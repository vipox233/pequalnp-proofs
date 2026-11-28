import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27657_aux

open PEqualNP.CircuitLowerBounds

def Form (n : ℕ) (g : Gate) : Prop :=
  (∃ a, a < n ∧ g = ⟨.not,[a]⟩) ∨
    ∃ a b, a < b ∧ b < n ∧ (g = ⟨.and,[a,b]⟩ ∨ g = ⟨.or,[a,b]⟩)

def Admiss (n out : ℕ) : List Gate → Prop
  | [] => out < n
  | g :: gs => Form n g ∧ (n = out ∨ n ∈ gs.flatMap Gate.inputs) ∧ Admiss (n+1) out gs

def needed (n out : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.range n).filter (fun i => i = out ∨ i ∈ gs.flatMap Gate.inputs)

theorem mem_needed {i n out gs} : i ∈ needed n out gs ↔
    i < n ∧ (i = out ∨ i ∈ gs.flatMap Gate.inputs) := by simp [needed]

theorem form_inputs {n g} (f : Form n g) : g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < n := by
  rcases f with ⟨a,ha,rfl⟩ | ⟨a,b,hab,hb,rfl | rfl⟩ <;> simp_all <;> omega

theorem needed_cons {n out gs g} (f : Form n g) :
    needed n out (g :: gs) = (needed (n+1) out gs).erase n ∪ g.inputs.toFinset := by
  ext i
  have sound := (form_inputs f).2 i
  simp only [mem_needed, Finset.mem_union, Finset.mem_erase, List.mem_toFinset,
    List.flatMap_cons, List.mem_append]
  grind

theorem live_head {n out g gs} (h : Admiss n out (g :: gs)) : n ∈ needed (n+1) out gs :=
  mem_needed.mpr ⟨by omega, h.2.1⟩

theorem needed_card {n out gs} (h : Admiss n out gs) :
    (needed n out gs).card ≤ gs.length+1 := by
  induction gs generalizing n with
  | nil =>
    have sub : needed n out [] ⊆ {out} := by intro i hi; simpa using (mem_needed.mp hi).2
    simpa using Finset.card_le_card sub
  | cons g gs ih =>
    have bound := ih h.2.2
    have le := Finset.card_union_le ((needed (n+1) out gs).erase n) g.inputs.toFinset
    have remove := Finset.card_erase_add_one (live_head h)
    have inputs := g.inputs.toFinset_card_le
    have len := (form_inputs h.1).1
    rw [needed_cons h.1]
    simp only [List.length_cons]
    omega

theorem admiss_of_index {n out : ℕ} {gs : List Gate}
    (ho : out+1=n+gs.length)
    (forms : ∀ j : Fin gs.length, Form (n+j.val) (gs.get j))
    (live : ∀ j : Fin gs.length, j.val+1 < gs.length →
      ∃ l : Fin gs.length, j.val < l.val ∧ n+j.val ∈ (gs.get l).inputs) :
    Admiss n out gs := by
  induction gs generalizing n with
  | nil => simp [Admiss]; simp at ho; omega
  | cons g gs ih =>
    have h0 : Form n g := by simpa using forms (0 : Fin (g::gs).length)
    have hs (j : Fin gs.length) : Form ((n+1)+j.val) (gs.get j) := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using forms j.succ
    refine ⟨h0, ?_, ih (by simp at ho; omega) hs ?_⟩
    · cases gs with
      | nil => left; simp at ho; omega
      | cons a t =>
        right
        obtain ⟨l,hl,hw⟩ := live 0 (by simp)
        obtain ⟨v,hv⟩ := l
        cases v with
        | zero => simp at hl
        | succ v =>
          have hv' : v < (a::t).length := by simpa using hv
          apply List.mem_flatMap.mpr
          refine ⟨(a::t).get ⟨v,hv'⟩, List.getElem_mem _, ?_⟩
          simpa using hw
    · intro j hj
      obtain ⟨l,hl,hw⟩ := live j.succ (by simp; omega)
      obtain ⟨v,hv⟩ := l
      cases v with
      | zero => simp at hl
      | succ v =>
        have hv' : v < gs.length := by simpa using hv
        exact ⟨⟨v,hv'⟩, by simpa using hl, by simpa [Nat.add_assoc,Nat.add_comm 1] using hw⟩

def evalGate (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map (fun a => xs.getD a false))]

def run (gs : List Gate) (xs : List Bool) (out : ℕ) := (gs.foldl evalGate xs).getD out false

theorem run_congr {n out gs} {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (h : Admiss n out gs) (agree : ∀ a ∈ needed n out gs, x.getD a false = y.getD a false) :
    run gs x out = run gs y out := by
  induction gs generalizing n x y with
  | nil => exact agree out (mem_needed.mpr ⟨h,Or.inl rfl⟩)
  | cons g gs ih =>
    have fg := (form_inputs h.1).2
    have same : g.inputs.map (fun a => x.getD a false) = g.inputs.map (fun a => y.getD a false) := by
      apply List.map_congr_left
      intro a ha
      exact agree a (mem_needed.mpr ⟨fg a ha, Or.inr (by simp [ha])⟩)
    apply ih (n := n+1) (x := evalGate x g) (y := evalGate y g)
      (by simp [evalGate,hx]) (by simp [evalGate,hy]) h.2.2
    intro a ha
    obtain ⟨ha',ho⟩ := mem_needed.mp ha
    by_cases e : a=n
    · subst a
      simp only [evalGate, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : x.length ≤ n),
        List.getElem?_append_right (by omega : y.length ≤ n), hx, hy, Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some]
      exact congrArg g.op.eval same
    · have al : a<n := by omega
      have old := agree a (mem_needed.mpr ⟨al, by simp only [List.flatMap_cons,List.mem_append]; tauto⟩)
      simpa only [evalGate, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega : a<x.length),List.getElem?_append_left (by omega : a<y.length)]
        using old

abbrev Sig (w : ℕ) := BitVec w × BitVec w

def bit {w : ℕ} (side : Bool) (i : Fin w) (v : Sig w) : Bool :=
  (if side then v.1 else v.2).getLsbD i.val

def project {w : ℕ} (side : Bool) (i : Fin w) (ws : List (Sig w)) := ws.map (bit side i)

def evalSig {w : ℕ} (ws : List (Sig w)) (g : Gate) : Sig w :=
  let x := ws.getD (g.inputs.getD 0 0) (0,0)
  let y := ws.getD (g.inputs.getD 1 0) (0,0)
  match g.op with
  | .not => (~~~x.1, ~~~x.2)
  | .and => (x.1 &&& y.1, x.2 &&& y.2)
  | _ => (x.1 ||| y.1, x.2 ||| y.2)

theorem read_project {w : ℕ} (side : Bool) (i : Fin w) (ws : List (Sig w)) (a : ℕ) :
    (project side i ws).getD a false = bit side i (ws.getD a (0,0)) := by
  simp only [project, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[a]? with
  | none => cases side <;> simp [bit]
  | some v => rfl

theorem project_step {w n : ℕ} (side : Bool) (i : Fin w) (ws : List (Sig w)) {g : Gate}
    (hf : Form n g) :
    project side i (ws ++ [evalSig ws g]) = evalGate (project side i ws) g := by
  rcases hf with ⟨a,_,rfl⟩ | ⟨a,b,_,_,rfl | rfl⟩ <;> cases side <;>
    simp [project,evalGate,evalSig,GateOp.eval,List.getD_eq_getElem?_getD,bit, i.isLt] <;>
    cases ws[a]? <;> (try cases ws[b]?) <;> simp [bit]

def differs {w : ℕ} (ws : List (Sig w)) (out : ℕ) (gs : List Gate) : Prop :=
  ∀ i : Fin w, run gs (project true i ws) out ≠ run gs (project false i ws) out

def cover {w : ℕ} (ws : List (Sig w)) : List ℕ → BitVec w
  | [] => 0
  | a :: as =>
    let v := ws.getD a (0,0)
    (v.1 ^^^ v.2) ||| cover ws as

theorem cover_spec {w : ℕ} (ws : List (Sig w)) (A : List ℕ) (i : Fin w) :
    (cover ws A).getLsbD i.val = true ↔
      ∃ a ∈ A, bit true i (ws.getD a (0,0)) ≠ bit false i (ws.getD a (0,0)) := by
  induction A with
  | nil => simp [cover]
  | cons a A ih =>
    simp only [cover, BitVec.getLsbD_or, Bool.or_eq_true, BitVec.getLsbD_xor, ih, List.mem_cons,
      exists_eq_or_imp, bit, ite_true, Bool.false_eq_true, ite_false]
    grind

theorem cover_full {w n out A gs} {ws : List (Sig w)} (len : ws.length=n)
    (ad : Admiss n out gs) (hA : ∀ i, i ∈ A ↔ i ∈ needed n out gs)
    (d : differs ws out gs) : cover ws A = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_allOnes, decide_eq_true hj]
  apply (cover_spec ws A ⟨j,hj⟩).mpr
  by_contra! ha
  apply d ⟨j,hj⟩
  apply run_congr (by simp [project,len]) (by simp [project,len]) ad
  intro a hu
  simpa only [read_project] using ha a ((hA a).mpr hu)

def menu (A : List ℕ) : List Gate := A.flatMap (fun a =>
  (⟨.not,[a]⟩ : Gate) :: A.flatMap (fun b =>
    if a < b then [⟨.and,[a,b]⟩,⟨.or,[a,b]⟩] else []))

def nextActive (n : ℕ) (A forget : List ℕ) := n :: A.filter (fun a => a ∉ forget)

def feasible {w : ℕ} (r : ℕ) (ws : List (Sig w)) (A : List ℕ) : Bool :=
  decide (A.length ≤ r+1) && (cover ws A == BitVec.allOnes w)

def explore {w : ℕ} : ℕ → ℕ → List (Sig w) → List ℕ → Bool
  | 0, r, ws, A => feasible r ws A
  | d+1, r, ws, A =>
      feasible r ws A && (decide (A.length ≤ 1) || (menu A).any (fun g =>
        g.inputs.sublists.any (fun forget =>
          explore d (r-1) (ws ++ [evalSig ws g]) (nextActive ws.length A forget))))


theorem menu_complete {A : List ℕ} {n : ℕ} {g : Gate} (f : Form n g) (h : ∀ i ∈ g.inputs, i ∈ A) :
    g ∈ menu A := by
  rcases f with ⟨a,_,rfl⟩ | ⟨a,b,hab,_,rfl | rfl⟩
  · exact List.mem_flatMap.mpr ⟨a,h a (by simp),by simp⟩
  all_goals
    apply List.mem_flatMap.mpr
    refine ⟨a,h a (by simp),List.mem_cons_of_mem _ ?_⟩
    exact List.mem_flatMap.mpr ⟨b,h b (by simp),by simp [hab]⟩

theorem explore_complete {w n out : ℕ} {ws : List (Sig w)} {gs : List Gate} {A : List ℕ}
    (d r : ℕ) (len : ws.length=n) (hr : gs.length ≤ r)
    (ad : Admiss n out gs) (nd : A.Nodup)
    (hA : ∀ i, i ∈ A ↔ i ∈ needed n out gs) (dis : differs ws out gs) :
    explore d r ws A = true := by
  induction d generalizing n r ws A gs with
  | zero =>
    have eq : A.toFinset = needed n out gs := Finset.ext (by simpa using hA)
    have sz := needed_card ad
    rw [← eq, List.toFinset_card_of_nodup nd] at sz
    simp [explore, feasible, show A.length ≤ r+1 by omega, cover_full len ad hA dis]
  | succ d ih =>
    have eq : A.toFinset = needed n out gs := Finset.ext (by simpa using hA)
    have sz := needed_card ad
    rw [← eq, List.toFinset_card_of_nodup nd] at sz
    have ok : feasible r ws A = true := by
      simp [feasible, show A.length ≤ r+1 by omega, cover_full len ad hA dis]
    rw [explore, ok, Bool.true_and, Bool.or_eq_true]
    cases gs with
    | nil => exact Or.inl (decide_eq_true (by simpa using sz))
    | cons g gs =>
      right
      let forget := g.inputs.filter (fun i => i ∉ needed (n+1) out gs)
      let A' := nextActive n A forget
      have small (i) (hi : i ∈ A) : i < n := (mem_needed.mp ((hA i).mp hi)).1
      have hread (i) (hi : i ∈ g.inputs) : i ∈ A :=
        (hA i).mpr (mem_needed.mpr ⟨(form_inputs ad.1).2 i hi, Or.inr (by simp [hi])⟩)
      have next (i) : i ∈ A' ↔ i ∈ needed (n+1) out gs := by
        simp only [A',nextActive,List.mem_cons,List.mem_filter,decide_eq_true_eq,forget,hA,
          needed_cons ad.1,Finset.mem_union,Finset.mem_erase,List.mem_toFinset]
        have inew := live_head ad
        by_cases e : i = n
        · subst i; simp [inew]
        · tauto
      have distinct : A'.Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,nd.filter _⟩
        intro h
        have bad := small _ (List.mem_filter.mp h).1
        omega
      apply List.any_eq_true.mpr
      refine ⟨g,menu_complete ad.1 hread,List.any_eq_true.mpr ⟨forget,?_,?_⟩⟩
      · exact List.mem_sublists.mpr List.filter_sublist
      · rw [len]
        apply ih (n := n+1) (gs := gs) (ws := ws ++ [evalSig ws g]) (r-1) (by simp [len]) (by simp at hr; omega) ad.2.2 distinct next
        intro i
        rw [project_step _ _ _ ad.1, project_step _ _ _ ad.1]
        exact dis i


def inputs : List (Sig 43) := [
  (1398011333023,4421668307349),
  (7398089033999,251263453194),
  (332852101104,298492088160),
  (2964526790375,2964123054823),
  (1839580780153,1839479461433),
  (5383749626131,5239868221715),
  (5192469172601,5191374393689),
  (349983469190,349436095622),
  (3397327249548,3302837969036)]

def gateA : Gate := ⟨.or,[0,1]⟩
def gateB : Gate := ⟨.not,[3]⟩

def initial : List (Sig 43) := inputs ++ [(8796092500383,4672923896223),(5831566231832,5831969967384)]

theorem extend_inputs : (inputs ++ [evalSig inputs gateA]) ++ [evalSig (inputs ++ [evalSig inputs gateA]) gateB] = initial := by decide

def row (s : Bool) (i : Fin 43) (j : Fin 9) := bit s i (inputs.getD j.val (0,0))

def matching (x : Fin 9 → Bool) := (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

theorem rows_good : ∀ i : Fin 43, matching (row true i) = true ∧ matching (row false i) = false := by decide

theorem proj_inputs (s : Bool) (i : Fin 43) : project s i inputs = List.ofFn (row s i) := by
  apply List.ext_getElem (by simp [project,inputs])
  intro j hj h2
  rw [List.getElem_ofFn]
  have v := read_project s i inputs j
  rw [List.getD_eq_getElem _ _ hj] at v
  exact v

def starts (d : ℕ) := (List.range 11).sublists.any (fun A => decide (9 ∈ A ∧ 10 ∈ A) && explore d 10 initial A)


set_option maxHeartbeats 10000000 in
set_option maxRecDepth 16384 in
theorem rejection : starts 3 = false := by decide

theorem reject_suffix (cert : starts 3 = false) (out : ℕ) (gs : List Gate)
    (allGates : Admiss 9 out (gateA :: gateB :: gs)) (bound : gs.length ≤ 10)
    (evals : ∀ x, run (gateA :: gateB :: gs) (List.ofFn x) out = matching x) : False := by
  have ad := allGates.2.2
  have tail := ad.2.2
  let A := (List.range 11).filter (fun i => i ∈ needed 11 out gs)
  have ha (i : ℕ) : i ∈ A ↔ i ∈ needed 11 out gs := by
    simp only [A, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => (mem_needed.mp h).1)
  have lastIn : 10 ∈ A := (ha 10).mpr (live_head ad)
  have firstIn : 9 ∈ A := (ha 9).mpr (mem_needed.mpr ⟨by decide, by
    simpa [List.flatMap_cons,gateB] using allGates.2.1⟩)
  have hGateA : Form 9 gateA := allGates.1
  have hGateB : Form 10 gateB := ad.1
  have hr (s : Bool) (i : Fin 43) : run gs (project s i initial) out = matching (row s i) := by
    rw [← extend_inputs,project_step _ _ _ hGateB,project_step _ _ _ hGateA,proj_inputs]
    exact evals (row s i)
  have dis : differs initial out gs := by
    intro i
    rw [hr,hr,(rows_good i).1,(rows_good i).2]
    decide
  have yes := explore_complete 3 10 (ws := initial) (by decide : initial.length = 11) bound tail
    (List.nodup_range.filter _) ha dis
  have hit : starts 3 = true := by
    apply List.any_eq_true.mpr
    exact ⟨A, List.mem_sublists.mpr List.filter_sublist, by simpa only [decide_eq_true (And.intro firstIn lastIn),Bool.true_and] using yes⟩
  simp [cert] at hit


end PEqualNP.Outside.L_meta_27657_aux

open PEqualNP.Outside.L_meta_27657_aux in
theorem PEqualNP.Outside.L_meta_27657 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩)) := by
  rintro ⟨C, _, bound, evals, hout, structureGates, _, used, first, second⟩
  have forms (j : Fin C.gates.length) : Form (9+j.val) (C.gates.get j) := by
    rcases structureGates j with ⟨hn,a,ha,ins⟩ | ⟨op,a,b,hab,hb,ins⟩
    · exact Or.inl ⟨a,ha,by cases h : C.gates.get j with | mk tag args => simp_all⟩
    · refine Or.inr ⟨a,b,hab,hb,?_⟩
      rcases op with hand | hor
      · left; cases h : C.gates.get j with | mk tag args => simp_all
      · right; cases h : C.gates.get j with | mk tag args => simp_all
  have ad := admiss_of_index hout forms used
  obtain ⟨gs,hh⟩ : ∃ gs, C.gates = gateA :: gateB :: gs := by
    cases h : C.gates with
    | nil => simp [h] at first
    | cons g t =>
      cases h' : t with
      | nil => simp [h,h'] at second
      | cons q gs =>
        have e1 : g=gateA := by simpa [h,gateA] using first
        have e2 : q=gateB := by simpa [h,h',gateB] using second
        exact ⟨gs,by simp [e1,e2]⟩
  rw [hh] at ad
  apply reject_suffix rejection C.output gs ad
  · change C.gates.length ≤ 12 at bound
    rw [hh] at bound
    simp at bound
    omega
  · intro x
    have h := evals x
    change run C.gates (List.ofFn x) C.output = matching x at h
    simpa only [hh] using h
