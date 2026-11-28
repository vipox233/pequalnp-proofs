import Mathlib.Tactic
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket
namespace PEqualNP.Outside.L_meta_50536_aux
abbrev W := BitVec 6
def initial : List W := [62,60,56,48,32,0,63]
def absent (a : W) (B : List W) : Nat := if a ∈ B then 0 else 1
def need (B : List W) := absent 36 B + absent 38 B + absent 40 B
def choices (B : List W) := (B.flatMap fun a =>
  (~~~a) :: B.flatMap (fun b => [a &&& b,a ||| b])).eraseDups
def fresh (B : List W) := (choices B).filter (fun a => a ∉ B)
def available (v : W) (B : List W) : Bool := B.any fun a =>
  (~~~a == v) || B.any fun b => ((a &&& b) == v) || ((a ||| b) == v)
def targets : List W := [36,38,40]
def next (B : List W) (k : Nat) : List W :=
  if need B=k+1 then targets.filter (fun v => (v ∉ B) && available v B) else fresh B
def go : Nat → List W → Bool
  | 0,B => decide (need B=0)
  | k+1,B => decide (need B≤k+1) &&
      ((decide (need B≤k) && go k B) || (next B k).any (fun v => go k (v::B)))

theorem avail {a B} (h : a∈choices B) : available a B=true := by
  simp only [choices,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at h
  obtain ⟨v,hv,left|right⟩ := h
  · exact List.any_eq_true.mpr ⟨v,hv,Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr left.symm))⟩
  · obtain ⟨b,hb,op⟩ := right
    apply List.any_eq_true.mpr
    refine ⟨v,hv,Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨b,hb,?_⟩))⟩
    rcases op with l|r
    · simp [l]
    · simp [r]
theorem drop (v : W) (B : List W) : need B ≤ need (v::B)+1 := by
  have d1 : (36 : W) ≠ 38 := by decide
  have d2 : (36 : W) ≠ 40 := by decide
  have d3 : (38 : W) ≠ 40 := by decide
  unfold need absent
  simp only [List.mem_cons]
  by_cases h : (36 : W)=v <;> by_cases j : (38 : W)=v <;> by_cases k : (40 : W)=v <;>
    simp_all <;> split_ifs <;> omega

theorem bound {k B} (h : go k B=true) : need B≤k := by
  cases k with
  | zero => simpa [go] using h
  | succ k => exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem done_ok {B k} (h : need B=0) : go k B=true := by
  induction k with
  | zero => simp [go,h]
  | succ k ih => simp [go,h,ih]

theorem skip {B k} (h : go k B=true) : go (k+1) B=true := by
  simp [go,h,bound h,Nat.le_succ_of_le (bound h)]

theorem step {B k v} (hv : v ∈ choices B) (new : v ∉ B) (h : go k (v::B)=true) : go (k+1) B=true := by
  have ok := (drop v B).trans (Nat.add_le_add_right (bound h) 1)
  have nxt : v∈next B k := by
    unfold next
    split_ifs with same
    · apply List.mem_filter.mpr
      constructor
      · by_contra outside
        have h2 : (36 : W) ≠ v := fun e => outside (e ▸ (by decide : (36:W) ∈ targets))
        have h35 : (38 : W) ≠ v := fun e => outside (e ▸ (by decide : (38:W) ∈ targets))
        have h42 : (40 : W) ≠ v := fun e => outside (e ▸ (by decide : (40:W) ∈ targets))
        have eq : need (v::B)=need B := by simp only [need,absent,List.mem_cons,h2,h35,h42,false_or]
        have le := bound h
        omega
      · simp [new,avail hv]
    · exact List.mem_filter.mpr ⟨hv,by simpa using new⟩
  have : (next B k).any (fun x => go k (x::B))=true := List.any_eq_true.mpr ⟨v,nxt,h⟩
  simp [go,ok,this]

theorem candidates {B : List W} {a b : W} (ha : a∈B) (hb : b∈B) :
    (~~~a) ∈ choices B ∧ (a &&& b) ∈ choices B ∧ (a ||| b) ∈ choices B := by
  simp only [choices,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.mem_singleton]
  exact ⟨⟨a,ha,Or.inl rfl⟩,⟨a,ha,Or.inr ⟨b,hb,Or.inl rfl⟩⟩,⟨a,ha,Or.inr ⟨b,hb,Or.inr (Or.inl rfl)⟩⟩⟩
end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def bit (t : Fin 6) (v : W) := v.getLsbD t.val
def row (t : Fin 6) := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
def value (g : Gate) (w : List W) : W :=
  let a := w.getD (g.inputs.headD w.length) 0
  let b := w.getD (g.inputs.tail.headD w.length) 0
  match g.op,g.inputs with
  | .not,_ => ~~~a
  | .and,[] => 63
  | .or,[] => 0
  | _,[_] => a
  | .and,_ => a &&& b
  | _,_ => a ||| b
def run (gs : List Gate) (w : List W) := gs.foldl (fun ws g => ws++[value g ws]) w
def legal (g : Gate) := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2

theorem rd_mem {w B : List W} (z : (0 : W)∈B) (le : ∀ a∈w,a∈B) (i : Nat) : w.getD i 0 ∈ B := by
  induction w generalizing i with
  | nil => simpa using z
  | cons a l ih =>
    cases i with
    | zero => exact le a (by simp)
    | succ i => exact ih (fun x hx => le x (by simp [hx])) i

theorem options {w B : List W} (z : (0 : W)∈B) (u : (63 : W)∈B) (le : ∀ a∈w,a∈B)
    (g : Gate) (ok : legal g) : value g w∈B ∨ value g w∈choices B := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨h,len⟩ := ok
  change op=.and ∨ op=.or ∨ op=.not at h
  cases ins with
  | nil =>
    rcases h with rfl|rfl|rfl
    · exact Or.inl u
    · exact Or.inl z
    · exact Or.inr (candidates (rd_mem z le w.length) z).1
  | cons i tail =>
    have a := rd_mem z le i
    cases tail with
    | nil =>
      rcases h with rfl|rfl|rfl
      · exact Or.inl a
      · exact Or.inl a
      · exact Or.inr (candidates a z).1
    | cons j tail =>
      have pair := candidates a (rd_mem z le j)
      rcases h with rfl|rfl|rfl
      · exact Or.inr pair.2.1
      · exact Or.inr pair.2.2
      · exact Or.inr pair.1

theorem rd_map (t : Fin 6) (w : List W) (i : Nat) :
    (w.map (bit t)).getD i false = bit t (w.getD i 0) := by
  induction w generalizing i with
  | nil => simp [bit]
  | cons a l ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem value_bit (t : Fin 6) (w : List W) (g : Gate) (ok : legal g) :
    bit t (value g w) = g.op.eval (g.inputs.map fun i => (w.map (bit t)).getD i false) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨h,len⟩ := ok
  change op=.and ∨ op=.or ∨ op=.not at h
  change ins.length≤2 at len
  simp only [rd_map]
  have endw : w.getD w.length (0 : W) = 0 := by simp [List.getD_eq_getElem?_getD]
  have ones : bit t 63=true := by revert t; decide
  cases ins with
  | nil =>
    rcases h with rfl|rfl|rfl <;> simp [value,GateOp.eval,ones,endw,bit,BitVec.getLsbD_not,t.isLt] at * <;> assumption
  | cons a l =>
    cases l with
    | nil => rcases h with rfl|rfl|rfl <;> simp [value,GateOp.eval,rd_map,bit,BitVec.getLsbD_not,t.isLt]
    | cons b l =>
      obtain rfl : l=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
      rcases h with rfl|rfl|rfl <;> simp [value,GateOp.eval,rd_map,bit,BitVec.getLsbD_not,t.isLt]

theorem sim (gs : List Gate) (w : List W) (t : Fin 6) (ok : ∀ g∈gs,legal g) :
    (run gs w).map (bit t) = (Circuit.mk gs 0).wires (w.map (bit t)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[value g w])).map _ = _
    rw [ih _ (fun a ha => ok a (by simp [ha]))]
    simp [Circuit.wires,value_bit t w g (ok g (by simp))]

theorem complete (gs : List Gate) (w B : List W) (ok : ∀ g∈gs,legal g)
    (z : (0 : W)∈B) (u : (63 : W)∈B) (le : ∀ a∈w,a∈B)
    (got : ∀ a∈([36,38,40] : List W), a ∈ run gs w) : go gs.length B=true := by
  induction gs generalizing w B with
  | nil =>
    apply done_ok
    have a := le 36 (got 36 (by decide))
    have b := le 38 (got 38 (by decide))
    have c := le 40 (got 40 (by decide))
    simp only [need,absent,if_pos a,if_pos b,if_pos c]
  | cons g gs ih =>
    let v := value g w
    have ok' : ∀ a∈gs,legal a := fun a ha => ok a (by simp [ha])
    have hgot : ∀ a∈([36,38,40] : List W),a ∈ run gs (w++[v]) := got
    by_cases h : v∈B
    · apply skip
      apply ih (w++[v]) B ok' z u _ hgot
      intro a ha
      rcases List.mem_append.mp ha with old|last
      · exact le a old
      · exact List.mem_singleton.mp last ▸ h
    · apply step (v:=v) ((options z u le g (ok g (by simp))).resolve_left h) h
      apply ih (w++[v]) (v::B) ok' (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ u) _ hgot
      intro a ha
      rcases List.mem_append.mp ha with old|last
      · exact List.mem_cons_of_mem _ (le a old)
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp last))
end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Asked : Prop := ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (36 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val

theorem inputs : ∀ t, initial.map (bit t) = row t := by decide +kernel

theorem target_wire (gs : List Gate) (ok : ∀ g∈gs,legal g) (p : Nat) (v : W)
    (out : ∀ t, ((Circuit.mk gs 0).wires (row t)).getD p false = bit t v) :
    (run gs initial).getD p 0=v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let t : Fin 6 := ⟨i,hi⟩
  change bit t ((run gs initial).getD p 0)=bit t v
  rw [← rd_map,sim gs initial t ok,inputs]
  exact out t

theorem padding {n m : Nat} {B : List W} (hle : n≤m) (h : go n B=true) : go m B=true := by
  induction hle with
  | refl => exact h
  | step _ ih => exact skip ih

theorem forced_any (gs : List Gate) (p q r : Nat) (ok : ∀ g∈gs,legal g) (size : gs.length≤6)
    (values : ∀ t, let w := (Circuit.mk gs 0).wires (row t)
      w.getD p false = bit t 36 ∧ w.getD q false = bit t 38 ∧ w.getD r false = bit t 40) :
    go 6 initial=true := by
  let wires := run gs initial
  have eq2 := target_wire gs ok p 36 (fun t => (values t).1)
  have eq35 := target_wire gs ok q 38 (fun t => (values t).2.1)
  have eq42 := target_wire gs ok r 40 (fun t => (values t).2.2)
  have mem (j : Nat) (v : W) (nv : v≠0) (eq : wires.getD j 0=v) : v∈wires := by
    by_cases hj : j<wires.length
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] at eq
      exact eq ▸ List.getElem_mem hj
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : wires.length≤j)] at eq
      exact (nv eq.symm).elim
  apply padding size (complete gs initial initial ok (by decide) (by decide) (fun _ h => h) ?_)
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  · exact mem _ _ (by decide) eq2
  · exact mem _ _ (by decide) eq35
  · exact mem _ _ (by decide) eq42

theorem forced (h : Asked) : go 6 initial=true := by
  obtain ⟨⟨gs,o⟩,p,q,r,fan,_,_,size,values⟩ := h
  apply forced_any gs p.val q.val r.val _ size values
  intro g hg
  obtain ⟨ops,arity⟩ := fan g hg
  exact ⟨ops,arity⟩

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c4_root : go 4 [62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_1 : go 4 [1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_3 : go 4 [3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_7 : go 4 [7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_15 : go 4 [15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_31 : go 4 [31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c5_root : go 5 [62,60,56,48,32,0,63] = false := by
  have eq : next ([62,60,56,48,32,0,63] : List W) 4 = [1,3,7,15,31] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c4_root,c4_1,c4_3,c4_7,c4_15,c4_31,Bool.false_or,Bool.and_false,Bool.false_and]

theorem c4_61_1 : go 4 [61,1,62,60,56,48,32,0,63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c4_57_1 : go 4 [57,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_49_1 : go 4 [49,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_33_1 : go 4 [33,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_3_1 : go 4 [3,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_7_1 : go 4 [7,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_15_1 : go 4 [15,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_31_1 : go 4 [31,1,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c5_1 : go 5 [1,62,60,56,48,32,0,63] = false := by
  have eq : next ([1,62,60,56,48,32,0,63] : List W) 4 = [61,57,49,33,3,7,15,31] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c4_1,c4_61_1,c4_57_1,c4_49_1,c4_33_1,c4_3_1,c4_7_1,c4_15_1,c4_31_1,Bool.false_or,Bool.and_false,Bool.false_and]

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c4_2_3 : go 4 [2,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_59_3 : go 4 [59,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_51_3 : go 4 [51,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_35_3 : go 4 [35,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_1_3 : go 4 [1,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_7_3 : go 4 [7,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_15_3 : go 4 [15,3,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_31_3 : go 4 [31,3,62,60,56,48,32,0,63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c5_3 : go 5 [3,62,60,56,48,32,0,63] = false := by
  have eq : next ([3,62,60,56,48,32,0,63] : List W) 4 = [2,59,51,35,1,7,15,31] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c4_3,c4_2_3,c4_59_3,c4_51_3,c4_35_3,c4_1_3,c4_7_3,c4_15_3,c4_31_3,Bool.false_or,Bool.and_false,Bool.false_and]

theorem c4_6_7 : go 4 [6,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_4_7 : go 4 [4,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_55_7 : go 4 [55,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_39_7 : go 4 [39,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_1_7 : go 4 [1,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_3_7 : go 4 [3,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_15_7 : go 4 [15,7,62,60,56,48,32,0,63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c4_31_7 : go 4 [31,7,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c5_7 : go 5 [7,62,60,56,48,32,0,63] = false := by
  have eq : next ([7,62,60,56,48,32,0,63] : List W) 4 = [6,4,55,39,1,3,15,31] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c4_7,c4_6_7,c4_4_7,c4_55_7,c4_39_7,c4_1_7,c4_3_7,c4_15_7,c4_31_7,Bool.false_or,Bool.and_false,Bool.false_and]

theorem c4_14_15 : go 4 [14,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_12_15 : go 4 [12,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_8_15 : go 4 [8,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_47_15 : go 4 [47,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_1_15 : go 4 [1,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_3_15 : go 4 [3,15,62,60,56,48,32,0,63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c4_7_15 : go 4 [7,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_31_15 : go 4 [31,15,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c5_15 : go 5 [15,62,60,56,48,32,0,63] = false := by
  have eq : next ([15,62,60,56,48,32,0,63] : List W) 4 = [14,12,8,47,1,3,7,31] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c4_15,c4_14_15,c4_12_15,c4_8_15,c4_47_15,c4_1_15,c4_3_15,c4_7_15,c4_31_15,Bool.false_or,Bool.and_false,Bool.false_and]

theorem c4_30_31 : go 4 [30,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_28_31 : go 4 [28,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_24_31 : go 4 [24,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_16_31 : go 4 [16,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_1_31 : go 4 [1,31,62,60,56,48,32,0,63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
theorem c4_3_31 : go 4 [3,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_7_31 : go 4 [7,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c4_15_31 : go 4 [15,31,62,60,56,48,32,0,63] = false := by decide +kernel

theorem c5_31 : go 5 [31,62,60,56,48,32,0,63] = false := by
  have eq : next ([31,62,60,56,48,32,0,63] : List W) 4 = [30,28,24,16,1,3,7,15] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c4_31,c4_30_31,c4_28_31,c4_24_31,c4_16_31,c4_1_31,c4_3_31,c4_7_31,c4_15_31,Bool.false_or,Bool.and_false,Bool.false_and]

theorem c6_root : go 6 [62,60,56,48,32,0,63] = false := by
  have eq : next ([62,60,56,48,32,0,63] : List W) 5 = [1,3,7,15,31] := by decide +kernel
  rw [go,eq]
  simp only [List.any_cons,List.any_nil,c5_root,c5_1,c5_3,c5_7,c5_15,c5_31,Bool.false_or,Bool.and_false,Bool.false_and]

end PEqualNP.Outside.L_meta_50536_aux
namespace PEqualNP.Outside.L_meta_50536_aux
open PEqualNP.CircuitLowerBounds
theorem refutation : ¬Asked := by
  intro h
  exact Bool.noConfusion ((forced h).symm.trans c6_root)

end PEqualNP.Outside.L_meta_50536_aux

theorem PEqualNP.Outside.L_meta_50536 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (36 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val) := by
  exact PEqualNP.Outside.L_meta_50536_aux.refutation
