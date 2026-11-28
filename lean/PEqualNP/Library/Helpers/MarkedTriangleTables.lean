import PEqualNP.Library.Helpers.MarkedTriangleDecision

namespace PEqualNP.MarkedTriangleTables
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MarkedTriangleDecision

abbrev Byte := BitVec 8
abbrev Entry := Byte × Bool
def seed : List Byte := [170,204,240,0,255]

/-- The bit tags a NOT gate. All other entries must arise from a binary AND or OR. -/
def legalStep (W : List Byte) (e : Entry) : Bool :=
  if e.2 then W.any (fun a => (~~~a) == e.1)
  else W.any (fun a => W.any (fun b => ((a &&& b) == e.1) || ((a ||| b) == e.1)))

def legal : List Byte → List Entry → Bool
  | _, [] => true
  | W, e::es => legalStep W e && legal (W ++ [e.1]) es

/-- A Boolean inversion budget, suitable for fixed-width certificate checkers. -/
def within (r : Nat) : List Entry → Bool
  | [] => true
  | e::es => match r with
    | 0 => !e.2 && within 0 es
    | k+1 => if e.2 then within k es else within (k+1) es

theorem within_iff (es : List Entry) (r : Nat) :
    within r es = true ↔ (es.filter Prod.snd).length ≤ r := by
  induction es generalizing r with
  | nil => simp [within]
  | cons e es ih =>
    cases r <;> cases h : e.2 <;> simp [within,h,ih,List.filter_cons]

def accepts (r : Nat) (es : List Entry) : Bool :=
  let W := seed ++ es.map Prod.fst
  within r es && legal seed es &&
    W.contains 232 && W.any (fun a => (a &&& 232) == 96) && W.any (fun a => (a &&& 232) == 40)

private def value : GateOp → List Byte → Byte
  | .and, [] => 255
  | .and, [a] => a
  | .and, a::b::_ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a::b::_ => a ||| b
  | .not, [] => 255
  | .not, a::_ => ~~~a
  | _, _ => 0

private def table (W : List Byte) (g : Gate) :=
  value g.op (g.inputs.map fun i => W.getD i 0)

private def isNeg (g : Gate) := match g.op with | .not => true | _ => false

private def compile : List Gate → List Byte → List Entry
  | [], _ => []
  | g::gs, W =>
    let a := table W g
    (a,isNeg g) :: compile gs (W ++ [a])

private theorem stats (gs : List Gate) (W : List Byte) :
    (compile gs W).length = gs.length ∧
    ((compile gs W).filter Prod.snd).length = (gs.filter isNeg).length := by
  induction gs generalizing W with
  | nil => simp [compile]
  | cons g gs ih =>
    obtain ⟨len,ct⟩ := ih (W ++ [table W g])
    cases hn : isNeg g <;> simp [compile,List.filter_cons,hn,len,ct]

private def Good (g : Gate) :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private theorem member {W : List Byte} (zero : 0∈W) (i : Nat) : W.getD i 0∈W := by
  rw [List.getD_eq_getElem?_getD]
  cases h : W[i]? with
  | none => exact zero
  | some a => exact List.mem_of_getElem? h

private theorem conj_ok {W : List Byte} {a b : Byte} (ha : a∈W) (hb : b∈W) :
    legalStep W (a &&& b,false) = true := by
  simp only [legalStep,Bool.false_eq_true,ite_false,List.any_eq_true,Bool.or_eq_true,beq_iff_eq]
  exact ⟨a,ha,b,hb,Or.inl rfl⟩

private theorem disj_ok {W : List Byte} {a b : Byte} (ha : a∈W) (hb : b∈W) :
    legalStep W (a ||| b,false) = true := by
  simp only [legalStep,Bool.false_eq_true,ite_false,List.any_eq_true,Bool.or_eq_true,beq_iff_eq]
  exact ⟨a,ha,b,hb,Or.inr rfl⟩

private theorem not_ok {W : List Byte} {a : Byte} (ha : a∈W) :
    legalStep W (~~~a,true) = true := by
  simp only [legalStep,ite_true,List.any_eq_true,beq_iff_eq]
  exact ⟨a,ha,rfl⟩

private theorem copy_ok {W : List Byte} {a : Byte} (ha : a∈W) :
    legalStep W (a,false) = true := by simpa using conj_ok ha ha

private theorem gate_ok {W : List Byte} (hz : 0∈W) (ht : 255∈W) (g : Gate) (hg : Good g) :
    legalStep W (table W g,isNeg g) = true := by
  obtain ⟨ops,arity⟩ := hg
  obtain ⟨op,ins⟩ := g
  change ins.length≤2 at arity
  change op=.and ∨ op=.or ∨ op=.not at ops
  rcases ops with rfl|rfl|rfl
  all_goals
    match ins,arity with
    | [], _ => first | exact copy_ok ht | exact copy_ok hz | exact not_ok hz
    | [i], _ => first | exact copy_ok (member hz i) | exact not_ok (member hz i)
    | [i,j], _ => first | exact conj_ok (member hz i) (member hz j)
                          | exact disj_ok (member hz i) (member hz j)
                          | exact not_ok (member hz i)

private theorem compile_legal {gs : List Gate} (ok : ∀g∈gs, Good g) (W : List Byte)
    (hz : 0∈W) (ht : 255∈W) : legal W (compile gs W) = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    exact Bool.and_eq_true_iff.mpr ⟨gate_ok hz ht g (ok g (by simp)),
      ih (fun u hu => ok u (by simp [hu])) _ (List.mem_append_left _ hz) (List.mem_append_left _ ht)⟩

private def atBit (i : Fin 8) (a : Byte) := a.getLsbD i.val

private theorem bit_table (i : Fin 8) (W : List Byte) (g : Gate) (hg : Good g) :
    atBit i (table W g) = g.op.eval (g.inputs.map fun j => (W.map (atBit i)).getD j false) := by
  have rd (j : Nat) : (W.map (atBit i)).getD j false = atBit i (W.getD j 0) := by
    simpa [atBit] using (List.getD_map (f := atBit i) (l := W) (n := j) (d := 0))
  have full : atBit i 255 = true := by fin_cases i <;> decide
  obtain ⟨ops,arity⟩ := hg
  obtain ⟨op,ins⟩ := g
  change ins.length≤2 at arity
  change op=.and ∨ op=.or ∨ op=.not at ops
  rcases ops with rfl|rfl|rfl
  all_goals
    match ins,arity with
    | [], _ => first | exact full | simp [atBit,table,value,GateOp.eval]
    | [j], _ => simp only [table,List.map_cons,List.map_nil,value,GateOp.eval,rd] <;>
        simp [atBit,BitVec.getLsbD_not,i.isLt]
    | [j,k], _ => simp only [table,List.map_cons,List.map_nil,value,GateOp.eval,rd] <;>
        simp [atBit,BitVec.getLsbD_not,i.isLt]

private theorem eval_compile (i : Fin 8) (gs : List Gate) (ok : ∀g∈gs, Good g) (W : List Byte) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) (W.map (atBit i)) =
      (W ++ (compile gs W).map Prod.fst).map (atBit i) := by
  induction gs generalizing W with
  | nil => simp [compile]
  | cons g gs ih =>
    have e := bit_table i W g (ok g (by simp))
    simp only [compile,List.foldl_cons,List.map_cons,←e]
    simpa [List.append_assoc] using ih (fun z hz => ok z (by simp [hz])) (W ++ [table W g])

private def word (i : Fin 8) (v : Fin 3) := i.val.testBit v.val

/-- Any affordable physical circuit yields at most s eight-bit gates passing the concrete certificate. -/
theorem extract {s r} (h : Fits s r) :
    ∃ es : List Entry, es.length ≤ s ∧ accepts r es = true := by
  obtain ⟨C,p,q,fan,_,_,size,inv,works⟩ := h
  let es := compile C.gates seed
  let W := seed ++ es.map Prod.fst
  have ok : ∀g∈C.gates, Good g := fan
  obtain ⟨len,cnt⟩ := stats C.gates seed
  refine ⟨es,len.trans_le size,?_⟩
  have zero : 0∈W := List.mem_append_left _ (by decide : (0:Byte)∈seed)
  have tab (i : Fin 8) : C.wires (List.ofFn (word i) ++ [false,true]) = W.map (atBit i) := by
    have init : List.ofFn (word i) ++ [false,true] = seed.map (atBit i) := by fin_cases i <;> decide
    rw [init]
    exact eval_compile i C.gates ok seed
  have rd (i : Fin 8) (j : Nat) :
      (C.wires (List.ofFn (word i) ++ [false,true])).getD j false = atBit i (W.getD j 0) := by
    rw [tab]
    simpa [atBit] using (List.getD_map (f := atBit i) (l := W) (n := j) (d := 0))
  have results (i : Fin 8) := works (word i)
  have target (i : Fin 8) : cover (word i) = atBit i 232 := by fin_cases i <;> decide
  have dec : W.getD C.output 0 = 232 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    let i : Fin 8 := ⟨j,hj⟩
    change atBit i _ = atBit i _
    rw [←rd]
    exact (results i).1.trans (target i)
  have first (i : Fin 8) : ((xor (word i 0) (word i 1)) && atBit i 232) = atBit i 96 := by fin_cases i <;> decide
  have second (i : Fin 8) : ((xor (word i 1) (word i 2)) && atBit i 232) = atBit i 40 := by fin_cases i <;> decide
  have parity (out : Nat) (v : Fin 3) (z : Byte)
      (expr : ∀ i : Fin 8, cover (word i)=true → atBit i (W.getD out 0) = xor (word i v) (word i 1))
      (mask : ∀ i : Fin 8, ((xor (word i v) (word i 1)) && atBit i 232) = atBit i z) :
      W.getD out 0 &&& 232 = z := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    let i : Fin 8 := ⟨j,hj⟩
    rw [BitVec.getLsbD_and]
    change (atBit i _ && atBit i 232) = atBit i z
    rw [←mask]
    cases b : atBit i 232
    · simp
    · exact congrArg (fun t => t && true) (expr i ((target i).trans b))
  have pm := parity p.val 0 96 (fun i ok => (rd i p.val).symm.trans (((results i).2 ok).1)) first
  have qm := parity q.val 2 40 (fun i ok => (rd i q.val).symm.trans
    ((((results i).2 ok).2).trans (Bool.xor_comm ..))) (fun i => by rw [Bool.xor_comm]; exact second i)
  have cost : (C.gates.filter isNeg).length = NotBracket.notCount C := by
    unfold NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases eq : g.op <;> simp [isNeg,eq]
  have fitsCount : (es.filter Prod.snd).length ≤ r := cnt.trans_le (cost.trans_le inv)
  have valid := compile_legal ok seed (by decide) (by decide)
  change (((within r es && legal seed es) && W.contains 232) &&
    W.any (fun a => (a &&& 232) == 96)) && W.any (fun a => (a &&& 232) == 40) = true
  have dmem : W.contains 232 = true := List.contains_iff_mem.mpr (dec ▸ member zero C.output)
  have pmem : W.any (fun a => (a &&& 232) == 96) = true :=
    List.any_eq_true.mpr ⟨_,member zero p.val,beq_iff_eq.mpr pm⟩
  have qmem : W.any (fun a => (a &&& 232) == 40) = true :=
    List.any_eq_true.mpr ⟨_,member zero q.val,beq_iff_eq.mpr qm⟩
  have cst := (within_iff es r).mpr fitsCount
  rw [cst,show legal seed es = true from valid,dmem,pmem,qmem]
  rfl

private theorem append_copy (W : List Byte) (es : List Entry) (hz : 0 ∈ W)
    (yes : legal W es = true) : legal W (es ++ [(0,false)]) = true := by
  induction es generalizing W with
  | nil => exact Bool.and_eq_true_iff.mpr ⟨copy_ok hz,rfl⟩
  | cons e es ih =>
    obtain ⟨step,tail⟩ := Bool.and_eq_true_iff.mp yes
    exact Bool.and_eq_true_iff.mpr ⟨step,ih _ (List.mem_append_left _ hz) tail⟩

private theorem pad_one (r : Nat) (es : List Entry) (yes : accepts r es = true) :
    accepts r (es ++ [(0,false)]) = true := by
  unfold accepts at yes ⊢
  simp only [Bool.and_eq_true,within_iff,List.contains_iff_mem,List.any_eq_true,beq_iff_eq] at yes ⊢
  obtain ⟨⟨⟨⟨ct,ok⟩,d⟩,p,hp,pm⟩,q,hq,qm⟩ := yes
  have keep (v : Byte) (hv : v ∈ seed ++ es.map Prod.fst) :
      v ∈ seed ++ (es ++ [(0,false)]).map Prod.fst := by
    simpa only [List.map_append,List.append_assoc] using
      (List.mem_append_left ([((0,false) : Entry)].map Prod.fst) hv)
  exact ⟨⟨⟨⟨by simpa using ct,append_copy _ es (by decide) ok⟩,keep _ d⟩,p,keep _ hp,pm⟩,
    q,keep _ hq,qm⟩

private theorem pad (r : Nat) (es : List Entry) (yes : accepts r es = true) (k : Nat) :
    ∃ out : List Entry, out.length = es.length+k ∧ accepts r out = true := by
  induction k with
  | zero => exact ⟨es,rfl,yes⟩
  | succ k ih =>
    obtain ⟨out,len,works⟩ := ih
    exact ⟨out ++ [(0,false)],by simp [len,Nat.add_assoc],pad_one _ _ works⟩

/-- A single fixed length suffices. The free data are eight bits and one NOT tag per gate. -/
theorem reject {s r : Nat} (no : ∀ w : Fin s → Entry, accepts r (List.ofFn w) = false) :
    ¬ Fits s r := by
  intro h
  obtain ⟨es,size,yes⟩ := extract h
  obtain ⟨out,len,passed⟩ := pad r es yes (s-es.length)
  have same : out.length=s := by omega
  subst s
  have denied := no out.get
  rw [List.ofFn_get,passed] at denied
  contradiction

theorem classify
    (six : ∀ w : Fin 6 → Entry, accepts 6 (List.ofFn w) = false)
    (one : ∀ w : Fin 7 → Entry, accepts 1 (List.ofFn w) = false) (s r : Nat) :
    Fits s r ↔ (7 ≤ s ∧ 2 ≤ r) ∨ (8 ≤ s ∧ 1 ≤ r) :=
  MarkedTriangleDecision.classify (reject six) (reject one) s r

end PEqualNP.MarkedTriangleTables
