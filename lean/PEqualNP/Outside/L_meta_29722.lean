import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29722_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
inductive Expr61 (n : Nat)
  | var (i : Fin n)
  | both (a b : Expr61 n)
  | either (a b : Expr61 n)
  | inv (a : Expr61 n)

def size61 {n} : Expr61 n → Nat
  | .var _ => 0
  | .both a b | .either a b => size61 a + size61 b + 1
  | .inv a => size61 a + 1

def neg61 {n} : Expr61 n → Nat
  | .var _ => 0
  | .both a b | .either a b => neg61 a + neg61 b
  | .inv a => neg61 a + 1

def eval61 {n} (y : Fin n → Bool) : Expr61 n → Bool
  | .var i => y i
  | .both a b => eval61 y a && eval61 y b
  | .either a b => eval61 y a || eval61 y b
  | .inv a => !(eval61 y a)

private instance opDec61 : DecidableEq GateOp := lineDegreeGateOpDecEq

def run61 (gs : List Gate) (p : List Bool) := (⟨gs,0⟩ : Circuit).wires p

theorem runAppend61 (a b : List Gate) (p : List Bool) :
    run61 (a++b) p=run61 b (run61 a p) := by simp [run61,Circuit.wires,List.foldl_append]

theorem runExt61 (gs : List Gate) (p : List Bool) : ∃ tail, run61 gs p = p ++ tail ∧ tail.length=gs.length := by
  induction gs generalizing p with
  | nil => exact ⟨[],by simp [run61,Circuit.wires],rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => p.getD i false))
    obtain ⟨t,eq,lt⟩ := ih (p++[v])
    exact ⟨v::t, by simpa [run61,Circuit.wires,v] using eq, by simp [lt]⟩

theorem runSize61 (gs : List Gate) (p : List Bool) : (run61 gs p).length=p.length+gs.length := by
  obtain ⟨_,e,h⟩ := runExt61 gs p
  simp [e,h]

theorem runKeep61 (gs : List Gate) (p : List Bool) (i : Nat) (hi : i<p.length) :
    (run61 gs p).getD i false=p.getD i false := by
  obtain ⟨t,eq,_⟩ := runExt61 gs p
  simp [eq,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

def tick61 (gs : List Gate) := (gs.filter fun g=>decide (g.op=.not)).length

def shape61 (g : Gate) : Prop := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ (g.inputs.length≤2) ∧ (g.op=.not → ∃ w, g.inputs=[w])

def safe61 (lo b : Nat) (gs : List Gate) : Prop := ∀ (j : Nat) (h : j<gs.length),
  shape61 gs[j] ∧ ∀ w∈gs[j].inputs, lo≤w ∧ w<b+j

theorem safeAppend61 {lo b} {a c : List Gate} (ha : safe61 lo b a)
    (hc : safe61 lo (b+a.length) c) : safe61 lo b (a++c) := by
  intro j hj
  by_cases h : j<a.length
  · simpa only [List.getElem_append_left h] using ha j h
  · rw [List.getElem_append_right (by omega)]
    obtain ⟨sh,rd⟩ := hc (j-a.length) (by simpa using (show j-a.length<c.length by simp at hj;omega))
    exact ⟨sh,fun w hw => (rd w hw).imp_right (by intros;omega)⟩

theorem safeOne61 {lo b : Nat} {g : Gate} (h : shape61 g)
    (rd : ∀ w∈g.inputs,lo≤w ∧ w<b) : safe61 lo b [g] := by
  intro j hj
  have eq : j=0 := by simp at hj;omega
  subst j
  simpa using And.intro h rd

def emitted61 {n} (e : Expr61 n) (b : Nat) (gs : List Gate) (out : Nat) : Prop :=
  gs.length=size61 e ∧ tick61 gs=neg61 e ∧ safe61 (0) b gs ∧ 0≤out ∧ out<b+gs.length ∧
  ∀ p : List Bool, p.length=b → (run61 gs p).getD out false =
    eval61 (fun i => p.getD (i.val) false) e

theorem terminal61 (gs : List Gate) (p : List Bool) (g : Gate) :
    (run61 (gs++[g]) p).getD (p.length+gs.length) false =
      g.op.eval (g.inputs.map (fun i=>(run61 gs p).getD i false)) := by
  rw [runAppend61,← runSize61]
  simp [run61,Circuit.wires,List.getD_eq_getElem?_getD]

theorem binary61 {n b} (ht : n≤b) (a c : Expr61 n) (l r : List Gate) (u v : Nat)
    (hl : emitted61 a b l u) (hr : emitted61 c (b+l.length) r v)
    (op : GateOp) (ok : op=.and ∨ op=.or) :
    emitted61 (if op=.and then .both a c else .either a c) b
      ((l++r)++[⟨op,[u,v]⟩]) (b+(l++r).length) := by
  obtain ⟨szl,nl,sl,lowu,hiu,vl⟩ := hl
  obtain ⟨szr,nr,sr,lowv,hiv,vr⟩ := hr
  have sf : safe61 (0) b ((l++r)++[⟨op,[u,v]⟩]) := by
    apply safeAppend61 (safeAppend61 sl sr)
    apply safeOne61
    · rcases ok with rfl|rfl <;> simp [shape61]
    · intro w hw
      simp at hw
      rcases hw with rfl|rfl <;> simp only [List.length_append] <;> omega
  have semantics (p : List Bool) (plen : p.length=b) :
      (run61 ((l++r)++[⟨op,[u,v]⟩]) p).getD (b+(l++r).length) false =
      op.eval [eval61 (fun i=>p.getD (i.val) false) a,eval61 (fun i=>p.getD (i.val) false) c] := by
    rw [←plen,terminal61,runAppend61]
    have ll := runSize61 l p
    have hr' := vr (run61 l p) (by omega)
    have inputs : (fun i : Fin n=>(run61 l p).getD (i.val) false) =
        (fun i : Fin n=>p.getD (i.val) false) := by
      funext i
      apply runKeep61
      have := i.isLt
      omega
    simp only [List.map_cons,List.map_nil,runKeep61 r (run61 l p) u (by omega),vl p plen,hr',inputs]
  rcases ok with rfl | rfl
  all_goals
    refine ⟨?_,?_,sf,by omega,by simp,?_⟩
    · simp [size61,szl,szr,Nat.add_assoc]
    · simp [tick61,List.filter_append] at nl nr ⊢
      simp [neg61,nl,nr]
    · intro p plen
      simpa [eval61,GateOp.eval] using semantics p plen

theorem emit61 {n} (e : Expr61 n) (b : Nat) (ht : n≤b) :
    ∃ gs out, emitted61 e b gs out := by
  induction e generalizing b with
  | var i =>
    refine ⟨[],i.val,rfl,rfl,?_,by omega,?_,?_⟩
    · intro j hj; simp at hj
    · have := i.isLt; simp; omega
    · intro p hp; rfl
  | both a c ha hc =>
    obtain ⟨l,u,hl⟩ := ha b ht
    obtain ⟨r,v,hr⟩ := hc (b+l.length) (by omega)
    exact ⟨_,_,binary61 ht a c l r u v hl hr .and (Or.inl rfl)⟩
  | either a c ha hc =>
    obtain ⟨l,u,hl⟩ := ha b ht
    obtain ⟨r,v,hr⟩ := hc (b+l.length) (by omega)
    exact ⟨_,_,binary61 ht a c l r u v hl hr .or (Or.inr rfl)⟩
  | inv a ih =>
    obtain ⟨l,u,sz,nc,safe,low,hi,val⟩ := ih b ht
    let g : Gate := ⟨.not,[u]⟩
    refine ⟨l++[g],b+l.length,by simp [size61,sz],?_,?_,by omega,by simp,?_⟩
    · simp [tick61] at nc ⊢
      simp [g,neg61,nc]
    · apply safeAppend61 safe
      apply safeOne61
      · simp [shape61,g]
      · simpa [g] using And.intro low hi
    · intro p hp
      rw [←hp,terminal61]
      change (!((run61 l p).getD u false)) = (!(eval61 _ a))
      rw [val p hp]

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold oneEach
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have h2 : ¬ i = n + v.val := by omega
    simp [h2, Fin.ext_iff]
  · by_cases h2 : i < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      simp [h3, Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      have h4 : ¬ i = n + v.val := by omega
      simp [h3, h4]




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def rowW {n : Nat} (m : Nat) (r : Fin n) : Fin (n+m+1) := ⟨r.val, by omega⟩
def colW (n : Nat) {m : Nat} (c : Fin m) : Fin (n+m+1) := ⟨n+c.val, by omega⟩
def swW (n m : Nat) : Fin (n+m+1) := ⟨n+m,by omega⟩

def signal {n m : Nat} (r : Fin n) (c : Fin m) (i : Fin n) (j : Fin m) (k : Fin (n+m+1)) : Bool :=
  if k.val=n+m then decide (i=r ∨ j=c) else decide (k.val=i.val ∨ k.val=n+j.val)

theorem rowSignal {n m} (r i u : Fin n) (c j : Fin m) : signal r c i j (rowW m u) = decide (i=u) := by
  have h := u.isLt
  simp [signal,rowW,show u.val≠n+m by omega,show u.val≠n+j.val by omega,Fin.ext_iff,eq_comm]
theorem colSignal {n m} (r i : Fin n) (c j v : Fin m) : signal r c i j (colW n v) = decide (j=v) := by
  have h := v.isLt
  simp [signal,colW,show m≠v.val by omega,show v.val≠m by omega,show n+v.val≠i.val by omega,Fin.ext_iff,eq_comm]
theorem swSignal {n m} (r i : Fin n) (c j : Fin m) : signal r c i j (swW n m) = decide (i=r ∨ j=c) := by
  simp [signal,swW]

theorem foldOr {α : Type} [DecidableEq α] {N : Nat} (S : Finset α)
    (base : Expr61 N) (g : α → Expr61 N) (k : Nat) (hs : ∀ i, size61 (g i)=k) (hn : ∀ i, neg61 (g i)=0) :
    ∃ e : Expr61 N, size61 e = size61 base + (k+1)*S.card ∧ neg61 e=neg61 base ∧
      ∀ y, eval61 y e=true ↔ eval61 y base=true ∨ ∃ i∈S, eval61 y (g i)=true := by
  induction S using Finset.induction_on with
  | empty => exact ⟨base,by simp,rfl,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨e,se,ne,ve⟩ := ih
    refine ⟨.either e (g a), ?_, by simp [neg61,ne,hn], ?_⟩
    · simp [size61,hs,se,ha,Nat.mul_add]; omega
    · intro y
      simp only [eval61,Bool.or_eq_true,ve,Finset.exists_mem_insert]
      simp only [or_assoc, or_left_comm, or_comm]

theorem makeCircuit {n m} {A : Fin n → Fin m → Bool} (r : Fin n) (c : Fin m)
    (e : Expr61 (n+m+1)) (en : neg61 e=1) (sz : 1+size61 e ≤ n+m-1)
    (sem : ∀ i j, eval61 (signal r c i j) e=A i j) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (n+m) C ∧ Represents A C ∧
      C.size=n+m-1 ∧ ∃! j : Fin C.gates.length, (C.gates.get j).op=GateOp.not := by
  classical
  obtain ⟨gs,out,gsSize,gsNeg,gsSafe,_,outLt,value⟩ := emit61 e (n+m+1) le_rfl
  let first : Gate := ⟨.or,[r.val,n+c.val]⟩
  let z : Gate := ⟨.or,[]⟩
  let k := n+m-1-(1+gs.length)
  let pads := List.replicate k z
  let pre := [first]++gs
  let all := pre++pads
  let C : Circuit := ⟨all,out⟩
  have firstSafe : safe61 0 (n+m) [first] := by
    apply safeOne61 (by simp [shape61,first])
    intro w hw
    simp [first] at hw
    rcases hw with rfl|rfl <;> constructor <;> omega
  have preSafe : safe61 0 (n+m) pre := safeAppend61 firstSafe (by simpa using gsSafe)
  have padsSafe : safe61 0 (n+m+pre.length) pads := by
    intro i hi
    have hgate : pads[i]=z := by simp [pads]
    simp [hgate,shape61,z]
  have good : safe61 0 (n+m) all := safeAppend61 preSafe padsSafe
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨j,hj,h⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨⟨op,ln,_⟩,_⟩ := good j hj
    subst g
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using op,ln⟩
  · intro j hj w hw
    change w ∈ (all.getD j _).inputs at hw
    rw [List.getD_eq_getElem _ _ hj] at hw
    exact ((good j hj).2 w hw).2
  · intro i j
    let p := oneEach i j
    have plen : p.length=n+m := oneEach_length i j
    have p1 : (run61 [first] p).length=n+m+1 := by simp [runSize61,plen]
    change (run61 (pre++pads) p).getD out false=A i j
    rw [runAppend61, runKeep61 _ _ _ (by simp [runSize61,pre,plen]; omega)]
    rw [show pre=[first]++gs from rfl,runAppend61,value _ p1,←sem i j]
    congr 1
    funext t
    by_cases h : t.val=n+m
    · rw [h,←plen]
      have hfirst := terminal61 [] p first
      simp only [List.nil_append,List.length_nil,Nat.add_zero] at hfirst
      rw [hfirst]
      simp only [first,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
      change (p.getD r.val false || p.getD (n+c.val) false)=_
      have rr := oneEach_getD i j r.val
      have cc := oneEach_getD i j (n+c.val)
      change ((oneEach i j).getD r.val false || (oneEach i j).getD (n+c.val) false) = _ 
      rw [rr,cc]
      simp [signal,h,show r.val≠n+j.val by omega,show n+c.val≠i.val by omega,Fin.ext_iff,eq_comm]
    · rw [runKeep61 _ _ _ (by have := t.isLt;omega)]
      change (oneEach i j).getD t.val false = _
      rw [oneEach_getD]; simp [signal,h]
  · change all.length=_
    simp [all,pre,pads,k]
    omega
  · have tick : tick61 all=1 := by
      change tick61 gs=neg61 e at gsNeg
      simp only [tick61] at gsNeg ⊢
      simp [all,pre,first,pads,z,List.filter_append,gsNeg,en]
    have eq := List.countP_ofFn (fun j : Fin all.length => all.get j) (fun g => decide (g.op=GateOp.not))
    rw [List.ofFn_get, List.countP_eq_length_filter] at eq
    have hc : (Finset.univ.filter (fun j : Fin all.length => (all.get j).op=GateOp.not)).card=1 := by
      simpa [tick61] using eq.symm.trans tick
    simpa [C] using Finset.card_eq_one_iff_existsUnique.mp hc




def rest {n} (x : Fin 4 ↪ Fin n) (i : Fin n) : Prop :=
  i≠x 0 ∧ i≠x 1 ∧ i≠x 2 ∧ i≠x 3
def link {n} (x : Fin 4 ↪ Fin n) (i : Fin n) : Prop := i≠x 0 ∧ i≠x 1 ∧ i≠x 2

theorem charge {n} {α : Type} [DecidableEq α] (x : Fin 4 ↪ Fin n) (extra : Finset (Fin n)) (edges : Finset α)
    (f : α → Fin n) (ext : ∀ i∈extra, rest x i) (ef : ∀ a∈edges, rest x (f a))
    (dis : ∀ a∈edges, f a ∉ extra) (inj : Set.InjOn f (edges : Set α)) :
    extra.card + edges.card + 4 ≤ n := by
  classical
  let four := Finset.univ.image x
  have fourCard : four.card=4 := by simp [four,Finset.card_image_of_injective _ x.injective]
  have notFour (i : Fin n) (h : rest x i) : i ∉ four := by
    intro hi
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hi
    fin_cases j <;> simp_all [rest]
  have d₁ : Disjoint extra (edges.image f) := by
    rw [Finset.disjoint_left]
    intro i hi hf
    rcases Finset.mem_image.mp hf with ⟨a,ha,rfl⟩
    exact dis a ha hi
  have d₂ : Disjoint (extra ∪ edges.image f) four := by
    rw [Finset.disjoint_left]
    intro i h hi
    rcases Finset.mem_union.mp h with h|h
    · exact notFour i (ext i h) hi
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact notFour _ (ef a ha) hi
  have h := Finset.card_le_univ ((extra ∪ edges.image f) ∪ four)
  rw [Finset.card_union_of_disjoint d₂,Finset.card_union_of_disjoint d₁,Finset.card_image_of_injOn inj,fourCard,Fintype.card_fin] at h
  exact h

set_option maxHeartbeats 1800000 in
theorem table {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (hr : ∀ j, A (x 0) j=decide (j=y 2) ∧ A (x 1) j=decide (j=y 3) ∧ A (x 2) j=decide (j≠y 1))
    (hc : ∀ i, A i (y 0)=decide (i=x 2) ∧ A i (y 1)=decide (i=x 3) ∧ A i (y 2)=decide (i≠x 1))
    (cross : A (x 3) (y 3)=false)
    (ur : ∀ i j l, link x i → link y j → link y l → A i j=true → A i l=true → j=l)
    (uc : ∀ j i k, link y j → link x i → link x k → A i j=true → A k j=true → i=k) :
    ∃ (rows : Finset (Fin n)) (cols : Finset (Fin m)) (edges : Finset (Fin n × Fin m)),
      rows.card + edges.card + 4 ≤ n ∧ cols.card + edges.card + 4 ≤ m ∧
      ∀ i j, A i j=true ↔
        ((i=x 2 ∨ j=y 2) ∧ ¬(i=x 1 ∨ j=y 1)) ∨
        ((i=x 3 ∨ j=y 3) ∧ ((i=x 1 ∨ j=y 1) ∨ i∈rows ∨ j∈cols)) ∨ (i,j)∈edges := by
  classical
  let rows := Finset.univ.filter fun i => rest x i ∧ A i (y 3)=true
  let cols := Finset.univ.filter fun j => rest y j ∧ A (x 3) j=true
  let edges := Finset.univ.filter fun p : Fin n × Fin m => rest x p.1 ∧ rest y p.2 ∧ A p.1 p.2=true
  have hmR i : i ∈ rows ↔ rest x i ∧ A i (y 3)=true := by simp [rows]
  have hmC j : j ∈ cols ↔ rest y j ∧ A (x 3) j=true := by simp [cols]
  have hmE p : p ∈ edges ↔ rest x p.1 ∧ rest y p.2 ∧ A p.1 p.2=true := by simp [edges]
  have rl {k : Nat} {z : Fin 4 ↪ Fin k} {a} (h : rest z a) : link z a :=
    ⟨h.1,h.2.1,h.2.2.1⟩
  have l3 {k : Nat} (z : Fin 4 ↪ Fin k) : link z (z 3) := by
    simp [link,z.injective.eq_iff]
  refine ⟨rows,cols,edges,charge x rows edges Prod.fst (fun i h => ((hmR i).mp h).1)
    (fun p h => ((hmE p).mp h).1) ?_ ?_,charge y cols edges Prod.snd (fun j h => ((hmC j).mp h).1)
    (fun p h => ((hmE p).mp h).2.1) ?_ ?_,?_⟩
  · intro p hp h
    obtain ⟨ra,cb,v⟩ := (hmE p).mp hp
    exact cb.2.2.2 (ur _ _ _ (rl ra) (rl cb) (l3 y) v ((hmR _).mp h).2)
  · intro p hp q hq hpq
    obtain ⟨ra,cb,v⟩ := (hmE p).mp hp
    obtain ⟨rd,ce,w⟩ := (hmE q).mp hq
    exact Prod.ext hpq (ur p.1 _ _ (rl ra) (rl cb) (rl ce) v (hpq ▸ w))
  · intro p hp h
    obtain ⟨ra,cb,v⟩ := (hmE p).mp hp
    exact ra.2.2.2 (uc _ _ _ (rl cb) (rl ra) (l3 x) v ((hmC _).mp h).2)
  · intro p hp q hq hpq
    obtain ⟨ra,cb,v⟩ := (hmE p).mp hp
    obtain ⟨rd,ce,w⟩ := (hmE q).mp hq
    exact Prod.ext (uc p.2 _ _ (rl cb) (rl ra) (rl rd) v (hpq ▸ w)) hpq
  · intro i j
    rw [hmR,hmC,hmE]
    simp only [Prod.fst,Prod.snd]
    have rr := hr j
    have cc := hc i
    have part {k : Nat} (z : Fin 4 ↪ Fin k) (t : Fin k) :
        t=z 0 ∨ t=z 1 ∨ t=z 2 ∨ t=z 3 ∨ rest z t := by
      unfold rest
      by_cases a : t=z 0 <;> by_cases b : t=z 1 <;> by_cases c : t=z 2 <;> by_cases d : t=z 3 <;> simp_all
    have r0 j := (hr j).1
    have r1 j := (hr j).2.1
    have r2 j := (hr j).2.2
    have c0 i := (hc i).1
    have c1 i := (hc i).2.1
    have c2 i := (hc i).2.2
    rcases part x i with rfl|rfl|rfl|rfl|oi <;>
      rcases part y j with rfl|rfl|rfl|rfl|oj
    all_goals try obtain ⟨oi0,oi1,oi2,oi3⟩ := oi
    all_goals try obtain ⟨oj0,oj1,oj2,oj3⟩ := oj
    all_goals simp [rest,x.injective.eq_iff,y.injective.eq_iff,r0,r1,r2,c0,c1,c2,cross, *]


end PEqualNP.Outside.L_meta_29722_aux

open PEqualNP.Outside.L_meta_29722_aux

theorem PEqualNP.Outside.L_meta_29722 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
  (
  let R := fun i : Fin n => i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2
  let T := fun j : Fin m => j ≠ y 0 ∧ j ≠ y 1 ∧ j ≠ y 2
  (∀ j, A (x 0) j = decide (j = y 2) ∧ A (x 1) j = decide (j = y 3) ∧
    A (x 2) j = decide (j ≠ y 1)) ∧
  (∀ i, A i (y 0) = decide (i = x 2) ∧ A i (y 1) = decide (i = x 3) ∧
    A i (y 2) = decide (i ≠ x 1)) ∧ A (x 3) (y 3) = false ∧
  (∀ i j l, R i → T j → T l → A i j = true → A i l = true → j = l) ∧
  (∀ j i k, T j → R i → R k → A i j = true → A k j = true → i = k) ∧
  (∀ i, R i → i ≠ x 3 → ∃ j, T j ∧ A i j = true) ∧
  (∀ j, T j → j ≠ y 3 → ∃ i, R i ∧ A i j = true)) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧ PEqualNP.Represents.Represents A C ∧
    C.size = n+m-1 ∧ ∃! j : Fin C.gates.length, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not := by
  classical
  intro n m A x y hh
  obtain ⟨hr,hc,hcross,ur,uc,_,_⟩ := hh
  obtain ⟨rows,cols,edges,nr,nc,tab⟩ := table A x y hr hc hcross ur uc
  let row := fun i : Fin n => Expr61.var (rowW m i)
  let col := fun j : Fin m => Expr61.var (colW n j)
  let W := Expr61.var (swW n m)
  let env := signal (x 1) (y 1)
  have rv (u : Fin n) (v : Fin m) (a : Fin n) : eval61 (env u v) (row a) = decide (u=a) :=
    rowSignal _ _ _ _ _
  have cv (u : Fin n) (v : Fin m) (a : Fin m) : eval61 (env u v) (col a) = decide (v=a) :=
    colSignal _ _ _ _ _
  have wv (u : Fin n) (v : Fin m) : eval61 (env u v) W = decide (u=x 1 ∨ v=y 1) :=
    swSignal _ _ _ _
  obtain ⟨er,sr,ngR,vr⟩ := foldOr rows W row 0 (fun _=>rfl) (fun _=>rfl)
  obtain ⟨ec,sc,ngC,vc⟩ := foldOr cols er col 0 (fun _=>rfl) (fun _=>rfl)
  let P := Expr61.either (row (x 2)) (col (y 2))
  let Q := Expr61.either (row (x 3)) (col (y 3))
  let core := Expr61.either (.both P (.inv W)) (.both Q ec)
  let term := fun t : Fin n × Fin m => Expr61.both (row t.1) (col t.2)
  obtain ⟨e,se,ne,ve⟩ := foldOr edges core term 1 (fun _=>rfl) (fun _=>rfl)
  apply makeCircuit (x 1) (y 1) e
  · simp [ne,core,P,Q,W,row,col,neg61,ngC,ngR]
  · simp only [se,core,P,Q,size61,show ∀ i, size61 (row i)=0 from fun _=>rfl,
       show ∀ j, size61 (col j)=0 from fun _=>rfl,show size61 W=0 from rfl,sc,sr] 
    change _ ≤ n+m-1
    simp only [W,size61] at *
    omega
  · intro i j
    apply Bool.eq_iff_iff.mpr
    change eval61 (env i j) e=true ↔ _
    rw [ve,tab i j]
    have vEc := vc (env i j)
    rw [vr] at vEc
    simp only [rv,cv,wv,decide_eq_true_eq] at vEc
    have vm : (∃ a∈rows, i=a) ↔ i∈rows := by simp
    have vn : (∃ b∈cols, j=b) ↔ j∈cols := by simp
    rw [vm,vn] at vEc
    have hit : (∃ p∈edges, eval61 (env i j) (term p)=true) ↔ (i,j)∈edges := by
      simp only [term,eval61,Bool.and_eq_true]
      constructor
      · rintro ⟨⟨a,b⟩,h,ht⟩
        change eval61 (env i j) (row a)=true ∧ eval61 (env i j) (col b)=true at ht
        rw [rv,cv,decide_eq_true_eq,decide_eq_true_eq] at ht
        obtain ⟨rfl,rfl⟩ := ht
        exact h
      · intro h
        refine ⟨(i,j),h,?_⟩
        change eval61 (env i j) (row i)=true ∧ eval61 (env i j) (col j)=true
        simp [rv,cv]
    rw [hit]
    change (((eval61 (env i j) (row (x 2)) || eval61 (env i j) (col (y 2))) && !(eval61 (env i j) W)) ||
      ((eval61 (env i j) (row (x 3)) || eval61 (env i j) (col (y 3))) && eval61 (env i j) ec))=true ∨ _ ↔ _
    simp only [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',rv,cv,wv,decide_eq_true_eq,decide_eq_false_iff_not,vEc]
    simp only [or_assoc]
