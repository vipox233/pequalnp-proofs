import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29784_aux

open PEqualNP.CircuitLowerBounds

def gateValue (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue g w]

lemma prefix_wires (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w++t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t,ht⟩ := ih (step w g)
    refine ⟨gateValue g w :: t,?_⟩
    simpa [step,List.append_assoc] using ht

lemma masked_gate {r : ℕ} {g : Gate} (key : 0 ∈ g.inputs → g.op = GateOp.or ∧ r+1 ∈ g.inputs)
    (rest : List Bool) (on : rest.getD r false = true) :
    gateValue g (false::rest) = gateValue g (true::rest) := by
  by_cases h : 0 ∈ g.inputs
  · obtain ⟨hor,hr⟩ := key h
    have sat (a : Bool) : gateValue g (a::rest)=true := by
      unfold gateValue
      rw [hor]
      simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
      exact ⟨true,⟨r+1,hr,on⟩,rfl⟩
    rw [sat,sat]
  · apply congrArg (GateOp.eval g.op)
    apply List.map_congr_left
    intro i hi
    cases i with
    | zero => exact (h hi).elim
    | succ j => rfl

lemma masked_run (gs : List Gate) {r : ℕ} (rest : List Bool) (hr : r<rest.length)
    (on : rest.getD r false = true)
    (key : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = GateOp.or ∧ r+1 ∈ g.inputs) (extra : List Bool) :
    ∃ t, gs.foldl step (false::(rest++extra)) = false::t ∧
      gs.foldl step (true::(rest++extra)) = true::t := by
  induction gs generalizing extra with
  | nil => exact ⟨rest++extra,rfl,rfl⟩
  | cons g gs ih =>
    have hv := masked_gate (key g (by simp)) (rest++extra)
      ((List.getD_append rest extra false r hr).trans on)
    let v := gateValue g (false::(rest++extra))
    obtain ⟨t,hf,ht⟩ := ih (fun e he => key e (List.mem_cons_of_mem _ he)) (extra++[v])
    refine ⟨t,?_,?_⟩
    · simpa only [List.foldl_cons,step,List.cons_append,List.append_assoc,v] using hf
    · simpa only [List.foldl_cons,step,List.cons_append,List.append_assoc,←hv,v] using ht

lemma output_nonzero {C : Circuit} (correct : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
    ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) : C.output ≠ 0 := by
  intro hout
  let onlyZero (i : Fin 7) := decide (i.val=0)
  have bad := correct onlyZero
  change C.eval (List.ofFn onlyZero) = false at bad
  obtain ⟨t,ht⟩ := prefix_wires C.gates (List.ofFn onlyZero)
  change (C.gates.foldl step (List.ofFn onlyZero)).getD C.output false=false at bad
  rw [ht,hout] at bad
  contradiction

lemma blocked {C : Circuit} {r : ℕ} (rest : List Bool) (hr : r<rest.length) (on : rest.getD r false=true)
    (key : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op=GateOp.or ∧ r+1 ∈ g.inputs) (hout : C.output≠0) :
    C.eval (false::rest)=C.eval (true::rest) := by
  obtain ⟨t,hf,ht⟩ := masked_run C.gates rest hr on key []
  simp only [List.append_nil] at hf ht
  change (C.gates.foldl step (false::rest)).getD C.output false =
    (C.gates.foldl step (true::rest)).getD C.output false
  rw [hf,ht]
  cases e : C.output with
  | zero => exact (hout e).elim
  | succ j => rfl

end PEqualNP.Outside.L_meta_29784_aux

open PEqualNP.Outside.L_meta_29784_aux in
theorem PEqualNP.Outside.L_meta_29784 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 0 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true)) := by
  rintro ⟨C,i,k,_,_,_,correct,_,uniqueRead,hor,_,_,_,hbuddy,_⟩
  have key (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g ∈ C.gates) (h : 0 ∈ g.inputs) :
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 1 + 1 ∈ g.inputs := by
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
    have use := uniqueRead j (by simpa only [hj] using h)
    rw [← hj,use]
    exact ⟨hor,hbuddy⟩
  let rest : List Bool := [false,true,false,false,false,true]
  let input (t : Bool) (j : Fin 7) := if j.val=0 then t else decide (j.val=2 ∨ j.val=6)
  have hx : (List.ofFn (input false)) = false::rest := by decide
  have hy : (List.ofFn (input true)) = true::rest := by decide
  have h0 := correct (input false)
  have h1 := correct (input true)
  change C.eval (List.ofFn (input false))=false at h0
  change C.eval (List.ofFn (input true))=true at h1
  have eq := blocked (r:=1) rest (by decide) (by decide) key (output_nonzero correct)
  rw [←hx,←hy,h0,h1] at eq
  contradiction
