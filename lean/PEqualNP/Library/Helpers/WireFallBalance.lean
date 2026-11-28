import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket
import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import Mathlib

namespace PEqualNP.WireFallBalance

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover Classical
open MetaComplexity.CoverCircuit (run run_append run_length run_singleton getD_run getD_snoc_length)

def drop (a b : Bool) := if a=true ∧ b=false then 1 else 0

def falls (l : Nat) (s : Nat → Bool) := (Finset.range l).sum (fun t => drop (s t) (s (t+1)))

private theorem invert_balance (l : Nat) (s : Nat → Bool) :
    falls l (fun t => !(s t)) + (s 0).toNat = falls l s + (s l).toNat := by
  induction l with
  | zero => simp [falls]
  | succ l ih =>
    simp only [falls,Finset.sum_range_succ] at ih ⊢
    cases h : s l <;> cases z : s (l+1) <;> simp [h,z,drop] at ih ⊢ <;> omega

private theorem invert_bound (l : Nat) (s : Nat → Bool) :
    falls l (fun t => !(s t)) ≤ drop (!(s 0)) (!(s l)) + falls l s := by
  have eq := invert_balance l s
  cases h : s 0 <;> cases z : s l <;> simp [h,z,drop] at eq ⊢ <;> omega

private theorem binary_bound (l : Nat) (a b : Nat → Bool) (op : Bool → Bool → Bool)
    (one : ∀ a b c d, drop (op a b) (op c d) ≤ drop a c+drop b d) :
    falls l (fun t => op (a t) (b t)) ≤ falls l a+falls l b := by
  simp only [falls,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => one ..)

private theorem disj (a b c d : Bool) : drop (a||b) (c||d) ≤ drop a c+drop b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem conj (a b c d : Bool) : drop (a&&b) (c&&d) ≤ drop a c+drop b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

noncomputable def effective (g : Gate) := if g.op=.not then g.inputs.take 1 else g.inputs

private theorem local_bound (g : Gate) (ops : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (size : g.inputs.length ≤ 2) (s : Nat → Nat → Bool) (l : Nat) :
    let value := fun t => g.op.eval (g.inputs.map (fun i => s i t))
    falls l value ≤ (if g.op=.not then drop (value 0) (value l) else 0) +
      ((effective g).map (fun i => falls l (s i))).sum := by
  obtain ⟨op,inputs⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl | rfl | rfl
  · match inputs with
    | [] => simp [effective,GateOp.eval,falls,drop]
    | [i] => simp [effective,GateOp.eval]
    | [i,j] => simpa [effective,GateOp.eval] using binary_bound l (s i) (s j) Bool.and conj
    | _::_::_::_ => simp at size
  · match inputs with
    | [] => simp [effective,GateOp.eval,falls,drop]
    | [i] => simp [effective,GateOp.eval]
    | [i,j] => simpa [effective,GateOp.eval] using binary_bound l (s i) (s j) Bool.or disj
    | _::_::_::_ => simp at size
  · cases inputs with
    | nil => simp [effective,GateOp.eval,falls,drop]
    | cons i rest => simpa [effective,GateOp.eval] using invert_bound l (s i)

theorem wire_gate (C : Circuit) (n : Nat) (back : ReadsBack n C) (xs : List Bool) (len : xs.length=n)
    (a : Nat) (ha : a < C.size) :
    (C.wires xs).getD (n+a) false =
      (gateAt C a).op.eval ((gateAt C a).inputs.map (fun i => (C.wires xs).getD i false)) := by
  let front := C.gates.take a
  let rest := C.gates.drop (a+1)
  let g := gateAt C a
  have geta : g=C.gates[a] := by simp [g,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]
  have split : C.gates=(front++[g])++rest := by
    rw [geta,←List.take_succ_eq_append_getElem ha,List.take_append_drop]
  have whole : C.wires xs=run rest (run [g] (run front xs)) := by
    change run C.gates xs=_
    conv_lhs => rw [split,run_append,run_append]
  have fw : (run front xs).length=n+a := by
    simp [run_length,front,len,List.length_take,Nat.min_eq_left (show a ≤ C.gates.length by exact ha.le)]
  have sw : (run [g] (run front xs)).length=n+a+1 := by rw [run_length,fw]; simp
  have old (i) (hi : i∈g.inputs) : (C.wires xs).getD i false=(run front xs).getD i false := by
    have good := back a ha i hi
    rw [whole,getD_run _ _ _ (sw ▸ (by omega)),getD_run _ _ _ (fw ▸ good)]
  change _=g.op.eval _
  rw [whole,getD_run _ _ _ (sw ▸ (by omega)),run_singleton,←fw,getD_snoc_length]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (old i hi).symm.trans (by rw [whole,run_singleton])

theorem distribute (l : List Nat) (N : Nat) (F : Nat → Nat) (h : ∀ i∈l, i < N) :
    (l.map F).sum=(Finset.range N).sum (fun i => l.count i * F i) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have mem := Finset.mem_range.mpr (h v (by simp))
    rw [List.map_cons,List.sum_cons,ih (fun i hi => h i (by simp [hi]))]
    simp [List.count_cons,Nat.add_mul,Finset.sum_add_distrib,ite_mul,mem,Nat.add_comm]

def wire (C : Circuit) {n : Nat} (x : Nat → Fin n → Bool) (i t : Nat) :=
  (C.wires (List.ofFn (x t))).getD i false

noncomputable def charges (C : Circuit) {n} (x : Nat → Fin n → Bool) (l : Nat) :=
  (Finset.range C.size).sum (fun a => if (gateAt C a).op=.not then
    drop (wire C x (n+a) 0) (wire C x (n+a) l) else 0)

noncomputable def uses (C : Circuit) (obs : List Nat) (i : Nat) :=
  obs.count i + (Finset.range C.size).sum (fun a => (effective (gateAt C a)).count i)

theorem gate_falls (n l : Nat) (C : Circuit) (fan : FanInTwo C) (back : ReadsBack n C)
    (x : Nat → Fin n → Bool) (a : Nat) (ha : a < C.size) :
    falls l (wire C x (n+a)) ≤
      (if (gateAt C a).op=.not then drop (wire C x (n+a) 0) (wire C x (n+a) l) else 0) +
      ((effective (gateAt C a)).map (fun i => falls l (wire C x i))).sum := by
  have hg : gateAt C a=C.gates[a] := by simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]
  have ok := fan (gateAt C a) (hg ▸ List.getElem_mem ..)
  have eq : wire C x (n+a) = fun t => (gateAt C a).op.eval ((gateAt C a).inputs.map (fun i => wire C x i t)) :=
    funext (fun t => wire_gate C n back _ (by simp) a ha)
  simpa only [eq] using local_bound (gateAt C a) ok.1 ok.2 (wire C x) l

theorem earlier (n : Nat) (C : Circuit) (back : ReadsBack n C) {a i : Nat} (ha : a < C.size)
    (hi : i∈effective (gateAt C a)) : i < n+a := by
  apply back a ha
  unfold effective at hi
  split at hi
  · exact List.mem_of_mem_take hi
  · exact hi

theorem balance (n l : Nat) (C : Circuit) (fan : FanInTwo C) (back : ReadsBack n C)
    (x : Nat → Fin n → Bool) (obs : List Nat) (valid : ∀ i∈obs, i < n+C.size) :
    let F := fun i => falls l (wire C x i)
    (obs.map F).sum ≤ (Finset.range n).sum F + charges C x l +
      (Finset.range (n+C.size)).sum (fun i => (uses C obs i-1)*F i) := by
  classical
  let F := fun i => falls l (wire C x i)
  let N := n+C.size
  let reads := fun a => effective (gateAt C a)
  have legal (a) (ha : a < C.size) (i) (hi : i∈reads a) : i < N := by
    have := earlier n C back ha hi
    dsimp [N]; omega
  let loss := fun a => if (gateAt C a).op=.not then drop (wire C x (n+a) 0) (wire C x (n+a) l) else 0
  have gate (a) (ha : a < C.size) : F (n+a) ≤ loss a + ((reads a).map F).sum := by
    exact gate_falls n l C fan back x a ha
  have bound := Finset.sum_le_sum (s:=Finset.range C.size) (fun a ha => gate a (Finset.mem_range.mp ha))
  rw [Finset.sum_add_distrib] at bound
  have cost : (Finset.range C.size).sum loss=charges C x l := rfl
  rw [cost] at bound
  have count : (Finset.range N).sum (fun i => uses C obs i*F i) =
      (obs.map F).sum + (Finset.range C.size).sum (fun a => ((reads a).map F).sum) := by
    simp only [uses,Nat.add_mul,Finset.sum_add_distrib,Finset.sum_mul]
    rw [←distribute obs N F valid,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    exact (distribute (reads a) N F (legal a (Finset.mem_range.mp ha))).symm
  have extra : (Finset.range N).sum (fun i => uses C obs i*F i) ≤
      (Finset.range N).sum F + (Finset.range N).sum (fun i => (uses C obs i-1)*F i) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases z : uses C obs i=0
    · simp [z]
    · rw [←Nat.succ_pred_eq_of_pos (show 0 < uses C obs i by omega)] at ⊢
      simp [Nat.succ_mul,Nat.add_mul,Nat.add_comm,Nat.pred_eq_sub_one,F]
  rw [count] at extra
  rw [show (Finset.range N).sum F=(Finset.range n).sum F+(Finset.range C.size).sum (fun a => F (n+a))
    from Finset.sum_range_add ..] at extra
  change (obs.map F).sum ≤ (Finset.range n).sum F + charges C x l +
    (Finset.range N).sum (fun i => (uses C obs i-1)*F i)
  omega

end PEqualNP.WireFallBalance
