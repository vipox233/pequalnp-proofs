import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_27129_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
abbrev Sig (N:ℕ):=(Fin N→Bool)→Bool
def vK (N:ℕ) (k:ℕ) (S:Set (Sig N)):Prop:=
 ∃ gs:List Gate,gs.length=k∧ReadsBack N ⟨gs,0⟩∧FanInTwo ⟨gs,0⟩∧
   ∀ a∈S,∃ i:ℕ,i<N+k∧
     ∀ x:Fin N→Bool,((Circuit.mk gs 0).wires (List.ofFn x)).getD i false=a x
theorem jF (C:Circuit) (w:List Bool):
 (C.wires w).length=w.length+C.gates.length:=by
 rcases C with ⟨gs,out⟩
 change (gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
  w).length=w.length+gs.length
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
   rw [List.foldl_cons,ih]
   simp only [List.length_append,List.length_cons,List.length_nil]
   omega
theorem jE (N:ℕ):
 vK N 0 (Set.range (fun i:Fin N=>fun x:Fin N→Bool=>x i)):=by
 refine ⟨[],rfl,by simp [ReadsBack],by simp [FanInTwo],?_⟩
 intro a ha
 obtain ⟨i,rfl⟩:=Set.mem_range.mp ha
 refine ⟨i.val,by simp,fun x=>?_⟩
 change (List.ofFn x).getD i.val false=x i
 rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
theorem jy {N k:ℕ} {S:Set (Sig N)} {gs:List Gate}
 (hw:∀ a∈S,∃ i:ℕ,i<N+k∧
   ∀ x:Fin N→Bool,((Circuit.mk gs 0).wires (List.ofFn x)).getD i false=a x)
 (deps:List (Sig N)) (hdeps:∀ a∈deps,a∈S):
 ∃ is:List ℕ,is.length=deps.length∧(∀ i∈is,i<N+k)∧
   ∀ x:Fin N→Bool,
     is.map (fun i=>((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)=
      deps.map (fun a=>a x):=by
 induction deps with
 | nil=>exact ⟨[],rfl,by simp,by simp⟩
 | cons a deps ih=>
   obtain ⟨i,hi,hval⟩:=hw a (hdeps a List.mem_cons_self)
   obtain ⟨is,hlen,hbound,hvals⟩:=ih (fun b hb=>hdeps b (List.mem_cons_of_mem a hb))
   refine ⟨i::is,by simp [hlen],?_,fun x=>?_⟩
   · intro j hj
     rcases List.mem_cons.mp hj with rfl|hj
     · exact hi
     · exact hbound j hj
   · simp only [List.map_cons,hval x,hvals x]
theorem jP {N k:ℕ} {S:Set (Sig N)}
 (h:vK N k S) (op:GateOp) (deps:List (Sig N)) (out:Sig N)
 (hop:op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp))
 (hlen:deps.length≤2) (hdeps:∀ a∈deps,a∈S)
 (hval:∀ x,out x=op.eval (deps.map fun a=>a x)):
 vK N (k+1) (insert out S):=by
 obtain ⟨gs,hgs,hr,hf,hw⟩:=h
 obtain ⟨is,his,hbound,hvalues⟩:=jy hw deps hdeps
 let g:Gate:=⟨op,is⟩
 have hlength (x:Fin N→Bool):
  ((Circuit.mk gs 0).wires (List.ofFn x)).length=N+k:=by
  rw [jF]; simpa using congrArg (N+·) hgs
 have hsnoc (x:Fin N→Bool):
  (Circuit.mk (gs++[g]) 0).wires (List.ofFn x)=
    (Circuit.mk gs 0).wires (List.ofFn x)++[out x]:=by
  simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (Circuit.mk gs 0).wires (List.ofFn x)++
   [op.eval (is.map fun i=>((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)]=
     (Circuit.mk gs 0).wires (List.ofFn x)++[out x]
  rw [hvalues x,hval x]
 refine ⟨gs++[g],by simp [hgs],?_,?_,?_⟩
 · intro j hj i hi
   change j<(gs++[g]).length at hj
   change i∈((gs++[g]).getD j ⟨GateOp.or,[]⟩).inputs at hi
   by_cases hj':j<gs.length
   · rw [List.getD_append _ _ _ _ hj'] at hi
     exact hr j hj' i hi
   · have heq:j=gs.length:=by simp at hj; omega
     subst j
     rw [List.getD_append_right _ _ _ _ le_rfl] at hi
     have hi':i∈is:=by simpa [g] using hi
     simpa [hgs] using hbound i hi'
 · intro g' hg'
   rcases List.mem_append.mp hg' with hg'|hg'
   · exact hf g' hg'
   · rw [List.mem_singleton.mp hg']
     exact ⟨hop,by change is.length≤2; simpa only [his] using hlen⟩
 · intro a ha
   rcases Set.mem_insert_iff.mp ha with rfl|ha
   · refine ⟨N+k,by omega,fun x=>?_⟩
     rw [hsnoc x,List.getD_append_right _ _ _ _ (by simp [hlength x])]
     simp [hlength x]
   · obtain ⟨i,hi,hval'⟩:=hw a ha
     refine ⟨i,by omega,fun x=>?_⟩
     rw [hsnoc x,List.getD_append _ _ _ _ (by simpa [hlength x] using hi),hval' x]
theorem j5 {N k L:ℕ} {S:Set (Sig N)}
 (h:vK N k S) (bits:Fin L→Sig N) (hbits:∀ p,bits p∈S):
 ∃ (C:Circuit) (out:Fin L→Fin (N+C.size)),
   FanInTwo C∧ReadsBack N C∧C.size=k∧
   ∀ (p:Fin L) (x:Fin N→Bool),
     (C.wires (List.ofFn x)).getD (out p).val false=bits p x:=by
 obtain ⟨gs,hgs,hr,hf,hw⟩:=h
 have hcho:∀ p:Fin L,∃ i:Fin (N+gs.length),
  ∀ x:Fin N→Bool,((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false=bits p x:=by
  intro p
  obtain ⟨i,hi,hv⟩:=hw (bits p) (hbits p)
  exact ⟨⟨i,by omega⟩,hv⟩
 choose out hout using hcho
 refine ⟨⟨gs,0⟩,out,hf,hr,hgs,?_⟩
 intro p x
 exact hout p x
structure qa {N:ℕ} (A B:Set (Sig N)) (b:ℕ):Prop where
 run:∀ {k:ℕ} {S:Set (Sig N)},vK N k S→A⊆S→
  ∃ c≤b,vK N (k+c) (S ∪ B)
theorem zk {N:ℕ} {A B:Set (Sig N)} (h:B⊆A):qa A B 0:=
 ⟨fun hs ha=>⟨0,le_rfl,by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩
theorem qd {N:ℕ} {A A' B B':Set (Sig N)} {b b':ℕ}
 (H:qa A B b) (hA:A⊆A') (hB:B'⊆A' ∪ B) (hb:b≤b'):qa A' B' b':=
 ⟨fun hs ha=>by
   obtain ⟨c,hc,hsc⟩:=H.run hs (hA.trans ha)
   obtain ⟨gs,hgs,hr,hf,hw⟩:=hsc
   refine ⟨c,hc.trans hb,gs,hgs,hr,hf,fun a hmem=>?_⟩
   rcases hmem with h1|h2
   · exact hw a (Or.inl h1)
   · rcases hB h2 with h2a|h2b
     · exact hw a (Or.inl (ha h2a))
     · exact hw a (Or.inr h2b)⟩
theorem zd {N:ℕ} {A B C:Set (Sig N)} {b c:ℕ}
 (H1:qa A B b) (H2:qa (A ∪ B) C c):qa A (B ∪ C) (b+c):=
 ⟨fun hs ha=>by
   obtain ⟨c1,hc1,hs1⟩:=H1.run hs ha
   obtain ⟨c2,hc2,hs2⟩:=H2.run hs1
    (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
   refine ⟨c1+c2,Nat.add_le_add hc1 hc2,?_⟩
   simpa [Nat.add_assoc,Set.union_assoc] using hs2⟩
theorem qe {N:ℕ} {A B C:Set (Sig N)} {b c:ℕ}
 (H1:qa A B b) (H2:qa (A ∪ B) C c):qa A C (b+c):=
 qd (zd H1 H2) le_rfl (fun _ h=>Or.inr (Or.inr h)) le_rfl
theorem qP {N:ℕ} {A B:Set (Sig N)} {b:ℕ} (H:qa A B b):qa A (A ∪ B) b:=
 qd H le_rfl le_rfl le_rfl
theorem qo {N:ℕ} {A B C:Set (Sig N)} {b c:ℕ}
 (H1:qa A B b) (H2:qa B C c):qa A C (b+c):=
 qd (zd H1 (qd H2 Set.subset_union_right Set.subset_union_right le_rfl))
  le_rfl (fun _ h=>Or.inr (Or.inr h)) le_rfl
theorem uF {N:ℕ} {A:Set (Sig N)} (op:GateOp) (deps:List (Sig N)) (out:Sig N)
 (hop:op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp))
 (hlen:deps.length≤2) (hdeps:∀ a∈deps,a∈A)
 (hval:∀ x,out x=op.eval (deps.map fun a=>a x)):
 qa A {out} 1:=
 ⟨fun hs ha=>⟨1,le_rfl,by
   simpa [Set.union_singleton] using
    jP hs op deps out hop hlen (fun a hm=>ha (hdeps a hm)) hval⟩⟩
theorem k4 {N:ℕ} {A:Set (Sig N)} (b:Bool):qa A {fun _=>b} 1:=by
 cases b with
 | false=>exact uF .or [] (fun _=>false) (by simp) (by simp) (by simp) (fun _=>rfl)
 | true=>exact uF .and [] (fun _=>true) (by simp) (by simp) (by simp) (fun _=>rfl)
theorem zn {N:ℕ} {A:Set (Sig N)} {f:Sig N} (hf:f∈A):
 qa A {fun x=>!(f x)} 1:=
 uF .not [f] (fun x=>!(f x)) (by simp) (by simp) (by simpa using hf) (fun _=>rfl)
theorem qD {N:ℕ} {A:Set (Sig N)} {f g:Sig N} (hf:f∈A) (hg:g∈A):
 qa A {fun x=>f x&&g x} 1:=
 uF .and [f,g] (fun x=>f x&&g x) (by simp) (by simp)
  (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha; rcases ha with rfl|rfl <;> assumption)
  (fun _=>by simp [GateOp.eval])
theorem orB {N:ℕ} {A:Set (Sig N)} {f g:Sig N} (hf:f∈A) (hg:g∈A):
 qa A {fun x=>f x||g x} 1:=
 uF .or [f,g] (fun x=>f x||g x) (by simp) (by simp)
  (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha; rcases ha with rfl|rfl <;> assumption)
  (fun _=>by simp [GateOp.eval])
theorem zZ (a b:Bool):
 xor a b=((a||b)&&!(a&&b)):=by
 cases a <;> cases b <;> rfl
theorem yW {N:ℕ} {A:Set (Sig N)} {f g:Sig N} (hf:f∈A) (hg:g∈A):
 qa A {fun x=>xor (f x) (g x)} 4:=by
 let s1:Sig N:=fun x=>f x||g x
 let s2:Sig N:=fun x=>f x&&g x
 let s3:Sig N:=fun x=>!(s2 x)
 let s4:Sig N:=fun x=>s1 x&&s3 x
 have h1:qa A {s1} 1:=orB hf hg
 have h2:qa (A ∪ {s1}) {s2} 1:=qD (Or.inl hf) (Or.inl hg)
 have h3:qa (A ∪ ({s1} ∪ {s2})) {s3} 1:=zn (Or.inr (Or.inr rfl))
 have h4:qa (A ∪ (({s1} ∪ {s2}) ∪ {s3})) {s4} 1:=
  qD (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
 have heq:s4=fun x=>xor (f x) (g x):=by
  funext x
  simp only [s4,s3,s2,s1]
  exact (zZ (f x) (g x)).symm
 refine qd (zd (zd (zd h1 h2) h3) h4) le_rfl ?_ (by omega)
 intro h hm
 rw [Set.mem_singleton_iff.mp hm,← heq]
 exact Or.inr (Or.inr rfl)
theorem vo {N:ℕ} {A:Set (Sig N)} {c a b:Sig N}
 (hc:c∈A) (ha:a∈A) (hb:b∈A):
 qa A {fun x=>if c x then a x else b x} 4:=by
 let nc:Sig N:=fun x=>!(c x)
 let t1:Sig N:=fun x=>c x&&a x
 let t2:Sig N:=fun x=>nc x&&b x
 let out:Sig N:=fun x=>t1 x||t2 x
 have h1:qa A {nc} 1:=zn hc
 have h2:qa (A ∪ {nc}) {t1} 1:=qD (Or.inl hc) (Or.inl ha)
 have h3:qa (A ∪ ({nc} ∪ {t1})) {t2} 1:=
  qD (Or.inr (Or.inl rfl)) (Or.inl hb)
 have h4:qa (A ∪ (({nc} ∪ {t1}) ∪ {t2})) {out} 1:=
  orB (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
 have heq:out=fun x=>if c x then a x else b x:=by
  funext x
  simp only [out,t1,t2,nc]
  cases c x <;> cases a x <;> cases b x <;> rfl
 refine qd (zd (zd (zd h1 h2) h3) h4) le_rfl ?_ (by omega)
 intro h hm
 rw [Set.mem_singleton_iff.mp hm,← heq]
 exact Or.inr (Or.inr rfl)
theorem j8 {N:ℕ} {α:Type*} {A:Set (Sig N)} (F:α→Set (Sig N)) (c:ℕ)
 (xs:List α) (h:∀ a∈xs,qa A (F a) c):
 qa A (⋃ a∈xs,F a) (xs.length * c):=by
 induction xs with
 | nil=>
   simp only [List.length_nil,Nat.zero_mul]
   exact zk (by simp)
 | cons a xs ih=>
   have h1:=h a List.mem_cons_self
   have h2:qa (A ∪ F a) (⋃ b∈xs,F b) (xs.length * c):=
    qd (ih (fun b hb=>h b (List.mem_cons_of_mem a hb)))
     Set.subset_union_left Set.subset_union_right le_rfl
   have hseq:=zd h1 h2
   refine qd hseq le_rfl ?_ (by simp [Nat.succ_mul,Nat.add_comm])
   intro f hf
   simp only [Set.mem_iUnion,List.mem_cons] at hf
   rcases hf with ⟨b,rfl|hb,hfb⟩
   · exact Or.inr (Or.inl hfb)
   · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hb,hfb⟩⟩))
theorem v7 {N n:ℕ} {A:Set (Sig N)} (F:Fin n→Set (Sig N)) (c:ℕ)
 (h:∀ i:Fin n,qa A (F i) c):
 qa A (⋃ i:Fin n,F i) (n * c):=by
 have hl:=j8 F c (List.finRange n) (fun i _=>h i)
 refine qd hl le_rfl ?_ (by simp)
 intro f hf
 rcases Set.mem_iUnion.mp hf with ⟨i,hfi⟩
 exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨List.mem_finRange i,hfi⟩⟩)
theorem qf {N n:ℕ} {A:Set (Sig N)} (F:Fin n→Sig N) (c:ℕ)
 (h:∀ i:Fin n,qa A {F i} c):
 qa A (Set.range F) (n * c):=by
 refine qd (v7 (fun i=>{F i}) c h) le_rfl ?_ le_rfl
 intro f hf
 rcases Set.mem_range.mp hf with ⟨i,rfl⟩
 exact Or.inr (Set.mem_iUnion.mpr ⟨i,rfl⟩)
theorem qT {N n1 n2:ℕ} {A:Set (Sig N)} (F:Fin n1→Fin n2→Sig N) (c:ℕ)
 (h:∀ i j,qa A {F i j} c):
 qa A {f|∃ i j,F i j=f} (n1 * (n2 * c)):=by
 have h1:qa A (⋃ i:Fin n1,Set.range (F i)) (n1 * (n2 * c)):=
  v7 (fun i=>Set.range (F i)) (n2 * c) (fun i=>qf (F i) c (fun j=>h i j))
 refine qd h1 le_rfl ?_ le_rfl
 rintro f ⟨i,j,rfl⟩
 exact Or.inr (Set.mem_iUnion.mpr ⟨i,⟨j,rfl⟩⟩)
theorem qr {N:ℕ} {A B C:Set (Sig N)} {b c:ℕ}
 (H1:qa A B b) (H2:qa A C c):qa A (B ∪ C) (b+c):=
 zd H1 (qd H2 Set.subset_union_left Set.subset_union_right le_rfl)
theorem kK {N:ℕ} {A:Set (Sig N)} (xs:List (Sig N))
 (hxs:∀ f∈xs,f∈A) (htrue:(fun _=>true)∈A):
 qa A {fun x=>xs.all (fun f=>f x)} xs.length:=by
 induction xs with
 | nil=>
   exact zk (by simpa using htrue)
 | cons f xs ih=>
   have h1:=ih (fun g hg=>hxs g (List.mem_cons_of_mem f hg))
   have h2:qa (A ∪ {fun x=>xs.all (fun g=>g x)})
    {fun x=>(f::xs).all (fun g=>g x)} 1:=by
    have heq:(fun x=>(f::xs).all (fun g=>g x))=
     (fun x=>f x&&xs.all (fun g=>g x)):=by
     funext x; simp [List.all_cons]
    rw [heq]
    exact qD (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
   exact qd (zd h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)
theorem vt {N:ℕ} {A:Set (Sig N)} (xs:List (Sig N))
 (hxs:∀ f∈xs,f∈A) (hfalse:(fun _=>false)∈A):
 qa A {fun x=>xs.any (fun f=>f x)} xs.length:=by
 induction xs with
 | nil=>
   exact zk (by simpa using hfalse)
 | cons f xs ih=>
   have h1:=ih (fun g hg=>hxs g (List.mem_cons_of_mem f hg))
   have h2:qa (A ∪ {fun x=>xs.any (fun g=>g x)})
    {fun x=>(f::xs).any (fun g=>g x)} 1:=by
    have heq:(fun x=>(f::xs).any (fun g=>g x))=
     (fun x=>f x||xs.any (fun g=>g x)):=by
     funext x; simp [List.any_cons]
    rw [heq]
    exact orB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
   exact qd (zd h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)
def zv (bs:List Bool):Bool:=
 bs.foldr xor false
theorem kY {N:ℕ} {A:Set (Sig N)} (xs:List (Sig N))
 (hxs:∀ f∈xs,f∈A) (hfalse:(fun _=>false)∈A):
 qa A {fun x=>zv (xs.map fun f=>f x)} (4 * xs.length):=by
 induction xs with
 | nil=>
   exact zk (by simpa [zv] using hfalse)
 | cons f xs ih=>
   have h1:=ih (fun g hg=>hxs g (List.mem_cons_of_mem f hg))
   have h2:qa (A ∪ {fun x=>zv (xs.map fun g=>g x)})
    {fun x=>zv ((f::xs).map fun g=>g x)} 4:=by
    have heq:(fun x=>zv ((f::xs).map fun g=>g x))=
     (fun x=>xor (f x) (zv (xs.map fun g=>g x))):=by
     funext x; rfl
    rw [heq]
    exact yW (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
   exact qd (zd h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp; omega)
theorem jD {N:ℕ} {α:Type*} (Sigs:((Fin N→Bool)→α)→Set (Sig N))
 (step:ℕ→α→α) (c:ℕ) (Base:Set (Sig N))
 (hstep:∀ t (st:(Fin N→Bool)→α),
   qa (Base ∪ Sigs st) (Sigs (fun x=>step t (st x))) c):
 ∀ T (st0:(Fin N→Bool)→α),
   qa (Base ∪ Sigs st0)
    (Sigs (fun x=>(List.range T).foldl (fun s t=>step t s) (st0 x)))
    (T * c):=by
 intro T
 induction T with
 | zero=>
   intro st0
   simpa using zk (A:=Base ∪ Sigs st0) (B:=Sigs st0) Set.subset_union_right
 | succ T ih=>
   intro st0
   let stT:(Fin N→Bool)→α:=
    fun x=>(List.range T).foldl (fun s t=>step t s) (st0 x)
   have h1:qa (Base ∪ Sigs st0) (Sigs stT) (T * c):=ih st0
   have h2:qa ((Base ∪ Sigs st0) ∪ Sigs stT) (Sigs (fun x=>step T (stT x))) c:=
    qd (hstep T stT)
     (Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right)
     Set.subset_union_right le_rfl
   have heq:(fun x=>(List.range (T+1)).foldl (fun s t=>step t s) (st0 x))=
    (fun x=>step T (stT x)):=by
    funext x
    simp [List.range_succ,List.foldl_append,stT]
   rw [heq]
   exact qd (qe h1 h2) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])
def kd (a b c:Bool):Bool:=xor (xor a b) c
def yS (a b c:Bool):Bool:=(a&&b)||(xor a b&&c)
theorem jB {N:ℕ} {A:Set (Sig N)} {fa fb fc:Sig N}
 (ha:fa∈A) (hb:fb∈A) (hc:fc∈A):
 qa A ({fun x=>kd (fa x) (fb x) (fc x),fun x=>yS (fa x) (fb x) (fc x)}) 9:=by
 let abOr:Sig N:=fun x=>fa x||fb x
 let abAnd:Sig N:=fun x=>fa x&&fb x
 let abNand:Sig N:=fun x=>!(abAnd x)
 let t1:Sig N:=fun x=>abOr x&&abNand x
 let tcOr:Sig N:=fun x=>t1 x||fc x
 let tcAnd:Sig N:=fun x=>t1 x&&fc x
 let tcNand:Sig N:=fun x=>!(tcAnd x)
 let sOut:Sig N:=fun x=>tcOr x&&tcNand x
 let cOut:Sig N:=fun x=>abAnd x||tcAnd x
 have h1:qa A {abOr} 1:=orB ha hb
 have h2:qa (A ∪ {abOr}) {abAnd} 1:=qD (Or.inl ha) (Or.inl hb)
 have h3:qa (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1:=zn (Or.inr (Or.inr rfl))
 have h4:qa (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1:=
  qD (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
 have h5:qa (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1:=
  orB (Or.inr (Or.inr rfl)) (Or.inl hc)
 have h6:qa (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1:=
  qD (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
 have h7:qa (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1:=
  zn (Or.inr (Or.inr rfl))
 have h8:qa (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1:=
  qD (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
 have h9:qa (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1:=
  orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
      (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
 have hall:=zd (zd (zd (zd (zd (zd (zd (zd h1 h2) h3) h4) h5) h6) h7) h8) h9
 have hsEq:sOut=fun x=>kd (fa x) (fb x) (fc x):=by
  funext x
  simp only [sOut,tcOr,tcNand,tcAnd,t1,abOr,abNand,abAnd,kd]
  rw [zZ (fa x) (fb x),zZ _ (fc x)]
 have hcEq:cOut=fun x=>yS (fa x) (fb x) (fc x):=by
  funext x
  simp only [cOut,tcAnd,t1,abOr,abNand,abAnd,yS]
  rw [zZ (fa x) (fb x)]
 refine qd hall le_rfl ?_ (by omega)
 intro f hf
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
 rcases hf with rfl|rfl
 · rw [← hsEq]
   exact Or.inr (Or.inl (Or.inr rfl))
 · rw [← hcEq]
   exact Or.inr (Or.inr rfl)
def zg (a b:ℕ):ℕ→Bool
 | 0=>false
 | j+1=>yS (a.testBit j) (b.testBit j) (zg a b j)
theorem qB (x j:ℕ):
 x.testBit j=decide ((x / 2 ^ j) % 2=1):=by
 rw [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two]
 have hlt:(x / 2 ^ j) % 2<2:=Nat.mod_lt _ (by omega)
 have hcases:(x / 2 ^ j) % 2=0∨(x / 2 ^ j) % 2=1:=by omega
 rcases hcases with h|h <;> simp [h]
theorem yN (a j:ℕ):
 a % 2 ^ (j+1)=a % 2 ^ j+(if a.testBit j then 2 ^ j else 0):=by
 have hpos:0<2 ^ j:=Nat.two_pow_pos j
 have hdiv1:=Nat.div_add_mod a (2 ^ j)
 have hdiv2:=Nat.div_add_mod (a / 2 ^ j) 2
 have ha_eq:a=(a % 2 ^ j+2 ^ j * ((a / 2 ^ j) % 2))+2 ^ (j+1) * (a / 2 ^ j / 2):=by
  rw [Nat.pow_succ]
  have h1:2 ^ j * (a / 2 ^ j)=2 ^ j * (2 * (a / 2 ^ j / 2)+(a / 2 ^ j) % 2):=by
   rw [hdiv2]
  rw [Nat.mul_add] at h1
  have h2:2 ^ j * (2 * (a / 2 ^ j / 2))=2 ^ j * 2 * (a / 2 ^ j / 2):=by ring
  omega
 have hlt_rem:a % 2 ^ j+2 ^ j * ((a / 2 ^ j) % 2)<2 ^ (j+1):=by
  have h1:a % 2 ^ j<2 ^ j:=Nat.mod_lt _ hpos
  have h2:(a / 2 ^ j) % 2≤1:=by have:=Nat.mod_lt (a / 2 ^ j) (by omega:0<2); omega
  have h3:2 ^ j * ((a / 2 ^ j) % 2)≤2 ^ j:=by
   calc 2 ^ j * ((a / 2 ^ j) % 2)≤2 ^ j * 1:=Nat.mul_le_mul_left _ h2
    _=2 ^ j:=Nat.mul_one _
  rw [Nat.pow_succ]; omega
 have h1:a % 2 ^ (j+1)=a % 2 ^ j+2 ^ j * ((a / 2 ^ j) % 2):=by
  conv_lhs=>rw [ha_eq]
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlt_rem]
 rw [h1,qB a j]
 have hcases:(a / 2 ^ j) % 2=0∨(a / 2 ^ j) % 2=1:=by
  have:=Nat.mod_lt (a / 2 ^ j) (by omega:0<2); omega
 rcases hcases with h|h <;> simp [h]
theorem ys (a b:ℕ):
 ∀ j:ℕ,
   zg a b j=decide (2 ^ j≤a % 2 ^ j+b % 2 ^ j)∧
   (a+b).testBit j=kd (a.testBit j) (b.testBit j) (zg a b j):=by
 intro j
 have hcarry:∀ k:ℕ,zg a b k=decide (2 ^ k≤a % 2 ^ k+b % 2 ^ k):=by
  intro k
  induction k with
  | zero=>simp [zg,Nat.mod_one]
  | succ k ih=>
    unfold zg
    rw [ih,yN a k,yN b k]
    have ha_lt:a % 2 ^ k<2 ^ k:=Nat.mod_lt _ (Nat.two_pow_pos k)
    have hb_lt:b % 2 ^ k<2 ^ k:=Nat.mod_lt _ (Nat.two_pow_pos k)
    have hp:2 ^ (k+1)=2 ^ k+2 ^ k:=by rw [Nat.pow_succ]; omega
    cases h1:a.testBit k <;> cases h2:b.testBit k <;>
     by_cases h3:2 ^ k≤a % 2 ^ k+b % 2 ^ k <;>
     simp [yS,h3,hp] <;> omega
 refine ⟨hcarry j,?_⟩
 rw [hcarry j]
 have hdiv:(a+b) / 2 ^ j=
  a / 2 ^ j+b / 2 ^ j+(a % 2 ^ j+b % 2 ^ j) / 2 ^ j:=by
  have ha:=Nat.div_add_mod a (2 ^ j)
  have hb:=Nat.div_add_mod b (2 ^ j)
  have hpos:0<2 ^ j:=Nat.two_pow_pos j
  have hsum:a+b=(a % 2 ^ j+b % 2 ^ j)+(a / 2 ^ j+b / 2 ^ j) * 2 ^ j:=by
   have:2 ^ j * (a / 2 ^ j)=(a / 2 ^ j) * 2 ^ j:=Nat.mul_comm _ _
   have:2 ^ j * (b / 2 ^ j)=(b / 2 ^ j) * 2 ^ j:=Nat.mul_comm _ _
   rw [Nat.add_mul]; omega
  rw [hsum,Nat.add_mul_div_right _ _ hpos]
  omega
 have hcdiv:(a % 2 ^ j+b % 2 ^ j) / 2 ^ j=if 2 ^ j≤a % 2 ^ j+b % 2 ^ j then 1 else 0:=by
  have ha_lt:a % 2 ^ j<2 ^ j:=Nat.mod_lt _ (Nat.two_pow_pos j)
  have hb_lt:b % 2 ^ j<2 ^ j:=Nat.mod_lt _ (Nat.two_pow_pos j)
  by_cases hle:2 ^ j≤a % 2 ^ j+b % 2 ^ j
  · simp only [hle,↓reduceIte]
    have hsub:a % 2 ^ j+b % 2 ^ j=(a % 2 ^ j+b % 2 ^ j-2 ^ j)+1 * 2 ^ j:=by omega
    rw [hsub,Nat.add_mul_div_right _ _ (Nat.two_pow_pos j),Nat.div_eq_of_lt (by omega)]
  · simp only [hle,↓reduceIte]
    exact Nat.div_eq_of_lt (by omega)
 rw [qB (a+b) j,qB a j,
  qB b j,hdiv,hcdiv]
 have ha2:(a / 2 ^ j) % 2=0∨(a / 2 ^ j) % 2=1:=by
  have:=Nat.mod_lt (a / 2 ^ j) (by omega:0<2); omega
 have hb2:(b / 2 ^ j) % 2=0∨(b / 2 ^ j) % 2=1:=by
  have:=Nat.mod_lt (b / 2 ^ j) (by omega:0<2); omega
 have hmod:(a / 2 ^ j+b / 2 ^ j+if 2 ^ j≤a % 2 ^ j+b % 2 ^ j then 1 else 0) % 2=
  ((a / 2 ^ j) % 2+(b / 2 ^ j) % 2+if 2 ^ j≤a % 2 ^ j+b % 2 ^ j then 1 else 0) % 2:=by
  omega
 rw [hmod]
 by_cases hc:2 ^ j≤a % 2 ^ j+b % 2 ^ j <;>
 rcases ha2 with ha|ha <;>
 rcases hb2 with hb|hb <;>
 simp [kd,hc,ha,hb]
def qk {N:ℕ} (L:ℕ) (F:(Fin N→Bool)→ℕ):Fin L→Sig N:=
 fun j x=>(F x).testBit j.val
theorem j2 {N:ℕ} {A:Set (Sig N)} (F G:(Fin N→Bool)→ℕ)
 (hfalse:(fun _=>false)∈A):
 ∀ L:ℕ,
   (∀ j:Fin L,(fun x=>(F x).testBit j.val)∈A)→
   (∀ j:Fin L,(fun x=>(G x).testBit j.val)∈A)→
   qa A
    ((Set.range (qk L (fun x=>F x+G x))) ∪ {fun x=>zg (F x) (G x) L})
    (9 * L):=by
 intro L
 induction L with
 | zero=>
   intro _ _
   simp only [Nat.mul_zero]
   apply zk
   intro f hf
   rcases hf with ⟨j,_⟩|rfl
   · exact Fin.elim0 j
   · exact hfalse
 | succ L ih=>
   intro hF hG
   have hprev:=ih (fun j=>hF j.castSucc) (fun j=>hG j.castSucc)
   have hstep:qa
    (A ∪ (Set.range (qk L (fun x=>F x+G x)) ∪ {fun x=>zg (F x) (G x) L}))
    ({fun x=>kd ((F x).testBit L) ((G x).testBit L) (zg (F x) (G x) L),
      fun x=>yS ((F x).testBit L) ((G x).testBit L) (zg (F x) (G x) L)}) 9:=
    jB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
   have hseq:=zd hprev hstep
   refine qd hseq le_rfl ?_ (by omega)
   intro f hf
   rcases hf with ⟨j,rfl⟩|rfl
   · by_cases hj:j.val<L
     · have hjeq:qk (L+1) (fun x=>F x+G x) j=
        qk L (fun x=>F x+G x) ⟨j.val,hj⟩:=rfl
       rw [hjeq]
       exact Or.inr (Or.inl (Or.inl ⟨⟨j.val,hj⟩,rfl⟩))
     · have hjeq:j.val=L:=by omega
       have hfeq:qk (L+1) (fun x=>F x+G x) j=
        fun x=>kd ((F x).testBit L) ((G x).testBit L) (zg (F x) (G x) L):=by
        funext x
        unfold qk
        rw [hjeq]
        exact (ys (F x) (G x) L).2
       rw [hfeq]
       exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inr (Or.inr rfl))
theorem uV {N:ℕ} {A:Set (Sig N)} (L:ℕ) (F G:(Fin N→Bool)→ℕ)
 (hfalse:(fun _=>false)∈A)
 (hF:∀ j:Fin L,qk L F j∈A)
 (hG:∀ j:Fin L,qk L G j∈A):
 qa A (Set.range (qk L (fun x=>F x+G x))) (9 * L):=
 qd (j2 F G hfalse L hF hG) le_rfl
  (fun _ hf=>Or.inr (Or.inl hf)) le_rfl
def q6 {N:ℕ}:List ((Fin N→Bool)→ℕ)→(Fin N→Bool)→ℕ
 | []=>fun _=>0
 | f::fs=>fun x=>f x+q6 fs x
theorem uA {N:ℕ} {A:Set (Sig N)} (L:ℕ)
 (hfalse:(fun _=>false)∈A)
 (Fs:List ((Fin N→Bool)→ℕ))
 (hFs:∀ F∈Fs,∀ j:Fin L,qk L F j∈A):
 qa A (Set.range (qk L (q6 Fs))) (Fs.length * (9 * L)):=by
 induction Fs with
 | nil=>
   simp only [List.length_nil,Nat.zero_mul]
   apply zk
   rintro _ ⟨j,rfl⟩
   have:qk L (q6 ([]:List ((Fin N→Bool)→ℕ))) j=fun _=>false:=by
    funext x; simp [qk,q6]
   rw [this]; exact hfalse
 | cons F Fs ih=>
   have h1:=ih (fun G hG=>hFs G (List.mem_cons_of_mem F hG))
   have h2:qa (A ∪ Set.range (qk L (q6 Fs)))
    (Set.range (qk L (fun x=>F x+q6 Fs x))) (9 * L):=
    uV L F (q6 Fs) (Or.inl hfalse)
     (fun j=>Or.inl (hFs F List.mem_cons_self j))
     (fun j=>Or.inr ⟨j,rfl⟩)
   refine qd (qe h1 h2) le_rfl Set.subset_union_right ?_
   simp only [List.length_cons]
   ring_nf
   omega
theorem y7 {L b j:ℕ} (hb:b<2 ^ L) (hj:j<L):
 (2 ^ L-1-b).testBit j=!(b.testBit j):=by
 have h1:(2 ^ L-1-b)+b=2 ^ L-1:=by omega
 have hpow:∀ n k,(2 ^ n-1).testBit k=decide (k<n):=by
  intro n
  induction n with
  | zero=>intro k; simp
  | succ n ih=>
    intro k
    rw [qB]
    cases k with
    | zero=>
      simp only [Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,decide_true]
      have hpos:0<2 ^ n:=Nat.two_pow_pos n
      have hm:(2 ^ (n+1)-1) % 2=1:=by rw [Nat.pow_succ]; omega
      simp [hm]
    | succ k=>
      have hpos:0<2 ^ n:=Nat.two_pow_pos n
      have hdiv:(2 ^ (n+1)-1) / 2 ^ (k+1)=(2 ^ n-1) / 2 ^ k:=by
       rw [Nat.pow_succ,Nat.pow_succ,Nat.mul_comm (2 ^ k) 2,← Nat.div_div_eq_div_mul]
       congr 1
       omega
      rw [hdiv,← qB,ih k]
      simp
 have hcarry:∀ k≤L,zg (2 ^ L-1-b) b k=false:=by
  intro k hk
  induction k with
  | zero=>rfl
  | succ k ih=>
    have hkL:k<L:=by omega
    have hspec:=(ys (2 ^ L-1-b) b k).2
    rw [h1,hpow L k,decide_eq_true hkL,ih (by omega)] at hspec
    unfold zg
    rw [ih (by omega)]
    simp only [kd,Bool.xor_false] at hspec
    cases hA:(2 ^ L-1-b).testBit k <;> cases hB:b.testBit k <;>
     simp [hA,hB,yS] at hspec ⊢
 have hspec:=(ys (2 ^ L-1-b) b j).2
 rw [h1,hpow L j,decide_eq_true hj,hcarry j (by omega)] at hspec
 simp only [kd,Bool.xor_false] at hspec
 cases hA:(2 ^ L-1-b).testBit j <;> cases hB:b.testBit j <;>
  simp [hA,hB] at hspec ⊢
theorem vY {L d j:ℕ} (hj:j<L):
 (2 ^ L+d).testBit j=d.testBit j:=by
 rw [qB,qB]
 have hsplit:2 ^ L=2 ^ j * 2 ^ (L-j):=by
  rw [← Nat.pow_add,Nat.add_sub_cancel' (by omega)]
 have hdiv:(2 ^ L+d) / 2 ^ j=2 ^ (L-j)+d / 2 ^ j:=by
  rw [hsplit,Nat.mul_add_div (Nat.two_pow_pos j)]
 rw [hdiv]
 have heven:2 ^ (L-j) % 2=0:=by
  have hpos:1≤L-j:=by omega
  rw [show L-j=(L-j-1)+1 by omega,Nat.pow_succ]
  omega
 have hmod:(2 ^ (L-j)+d / 2 ^ j) % 2=(d / 2 ^ j) % 2:=by omega
 rw [hmod]
theorem j3 {N:ℕ} {A:Set (Sig N)} (L:ℕ) (F G:(Fin N→Bool)→ℕ)
 (hfalse:(fun _=>false)∈A) (htrue:(fun _=>true)∈A)
 (hF:∀ j:Fin L,qk L F j∈A)
 (hG:∀ j:Fin L,qk L G j∈A)
 (hvalid:∀ x,G x≤F x∧G x<2 ^ L):
 qa A (Set.range (qk L (fun x=>F x-G x))) (19 * L):=by
 let compG:(Fin N→Bool)→ℕ:=fun x=>2 ^ L-1-G x
 let oneF:(Fin N→Bool)→ℕ:=fun _=>1
 have hcomp:qa A (Set.range (qk L compG)) L:=by
  have h1:=qf (A:=A) (fun j:Fin L=>fun x=>!(qk L G j x)) 1
   (fun j=>zn (hG j))
  refine qd h1 le_rfl ?_ (by omega)
  rintro _ ⟨j,rfl⟩
  have heq:qk L compG j=fun x=>!(qk L G j x):=by
   funext x
   exact y7 (hvalid x).2 j.isLt
  rw [heq]
  exact Or.inr ⟨j,rfl⟩
 have hone:∀ j:Fin L,qk L oneF j∈A:=by
  intro j
  by_cases hj:j.val=0
  · have heq:qk L oneF j=fun _=>true:=by
     funext x; simp [qk,oneF,hj]
    rw [heq]; exact htrue
  · have heq:qk L oneF j=fun _=>false:=by
     funext x
     simp only [qk,oneF]
     exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega:1<2 ^ 1)
      (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [heq]; exact hfalse
 have hadd1:qa (A ∪ Set.range (qk L compG))
  (Set.range (qk L (fun x=>compG x+oneF x))) (9 * L):=
  uV L compG oneF (Or.inl hfalse) (fun j=>Or.inr ⟨j,rfl⟩) (fun j=>Or.inl (hone j))
 have hadd2:qa (A ∪ (Set.range (qk L compG) ∪
  Set.range (qk L (fun x=>compG x+oneF x))))
  (Set.range (qk L (fun x=>F x+(compG x+oneF x)))) (9 * L):=
  uV L F (fun x=>compG x+oneF x) (Or.inl hfalse)
   (fun j=>Or.inl (hF j)) (fun j=>Or.inr (Or.inr ⟨j,rfl⟩))
 have hseq:=qe (zd hcomp hadd1) hadd2
 refine qd hseq le_rfl ?_ (by omega)
 rintro _ ⟨j,rfl⟩
 have heq:qk L (fun x=>F x-G x) j=qk L (fun x=>F x+(compG x+oneF x)) j:=by
  funext x
  unfold qk compG oneF
  dsimp only
  have hle:=(hvalid x).1
  have hlt:=(hvalid x).2
  have hsum:F x+(2 ^ L-1-G x+1)=2 ^ L+(F x-G x):=by omega
  rw [hsum,vY j.isLt]
 rw [heq]
 exact Or.inr ⟨j,rfl⟩
def qi {n:ℕ} (cond:Fin n→Bool) (i:Fin n):Bool:=
 cond i&&!(List.finRange n |>.filter (fun j=>decide (j.val< i.val)) |>.any cond)
theorem qU {n:ℕ} (cond:Fin n→Bool) (i:Fin n):
 qi cond i=true↔cond i=true∧∀ j:Fin n,j.val< i.val→cond j=false:=by
 unfold qi
 simp only [Bool.and_eq_true,Bool.not_eq_true',List.any_eq_false,List.mem_filter,
  List.mem_finRange,true_and,decide_eq_true_eq]
 constructor
 · rintro ⟨h1,h2⟩
   exact ⟨h1,fun j hj=>by
    have:=h2 j hj
    cases h:cond j <;> simp_all⟩
 · rintro ⟨h1,h2⟩
   exact ⟨h1,fun j hj=>by simp [h2 j hj]⟩
theorem q2 {n:ℕ} (cond:Fin n→Bool) {i j:Fin n}
 (hi:qi cond i=true) (hj:qi cond j=true):i=j:=by
 have hi':=(qU cond i).mp hi
 have hj':=(qU cond j).mp hj
 by_contra hne
 rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt|hgt
 · have:=hj'.2 i hlt
   rw [hi'.1] at this
   exact Bool.noConfusion this
 · have:=hi'.2 j hgt
   rw [hj'.1] at this
   exact Bool.noConfusion this
theorem q0 {n:ℕ} (cond:Fin n→Bool):
 (∃ i:Fin n,qi cond i=true)↔(∃ i:Fin n,cond i=true):=by
 constructor
 · rintro ⟨i,hi⟩
   exact ⟨i,((qU cond i).mp hi).1⟩
 · rintro ⟨i0,hi0⟩
   classical
   have hex:∃ k:ℕ,∃ h:k<n,cond ⟨k,h⟩=true:=⟨i0.val,i0.isLt,hi0⟩
   let k:=Nat.find hex
   rcases Nat.find_spec hex with ⟨hk,hcond⟩
   refine ⟨⟨k,hk⟩,(qU cond ⟨k,hk⟩).mpr ⟨hcond,?_⟩⟩
   intro j hj
   by_contra hne
   have hjtrue:cond j=true:=by cases h:cond j <;> simp_all
   exact Nat.find_min hex hj ⟨j.isLt,hjtrue⟩
theorem yE {N n:ℕ} {A:Set (Sig N)} (cond:Fin n→Sig N)
 (hfalse:(fun _=>false)∈A)
 (hcond:∀ i:Fin n,cond i∈A):
 qa A (Set.range (fun i:Fin n=>fun x=>qi (fun j=>cond j x) i)) (n * (n+2)):=by
 refine qf (fun i:Fin n=>fun x=>qi (fun j=>cond j x) i) (n+2) ?_
 intro i
 let xs:List (Sig N):=(List.finRange n |>.filter (fun j=>decide (j.val< i.val))).map cond
 have hxs:∀ f∈xs,f∈A:=by
  intro f hf
  rcases List.mem_map.mp hf with ⟨j,_,rfl⟩
  exact hcond j
 have h1:qa A {fun x=>xs.any (fun f=>f x)} xs.length:=vt xs hxs hfalse
 have h2:qa (A ∪ {fun x=>xs.any (fun f=>f x)})
  {fun x=>!(xs.any (fun f=>f x))} 1:=zn (Or.inr rfl)
 have h3:qa ((A ∪ {fun x=>xs.any (fun f=>f x)}) ∪ {fun x=>!(xs.any (fun f=>f x))})
  {fun x=>cond i x&&!(xs.any (fun f=>f x))} 1:=
  qD (Or.inl (Or.inl (hcond i))) (Or.inr rfl)
 have hlen:xs.length≤n:=by
  calc
   xs.length=(List.finRange n |>.filter (fun j=>decide (j.val< i.val))).length:=
    List.length_map _
   _≤(List.finRange n).length:=List.length_filter_le _ _
   _=n:=List.length_finRange
 have heq:(fun x=>cond i x&&!(xs.any (fun f=>f x)))=
  (fun x=>qi (fun j=>cond j x) i):=by
  funext x
  simp [qi,xs,List.any_map]
 rw [← heq]
 exact qd (qo (qo (qP h1) (qP h2)) h3) le_rfl Set.subset_union_right (by omega)
def z2b (x:ZMod 2):Bool:=decide (x≠0)
def b2z (b:Bool):ZMod 2:=if b then 1 else 0
theorem qF (x:ZMod 2):x=0∨x=1:=by
 fin_cases x
 · exact Or.inl rfl
 · exact Or.inr rfl
theorem z0 (b:Bool):z2b (b2z b)=b:=by
 cases b <;> decide
theorem vr (x:ZMod 2):b2z (z2b x)=x:=by
 rcases qF x with rfl|rfl <;> rfl
theorem qm:z2b 0=false:=by decide
theorem zA:z2b 1=true:=by decide
theorem vW (x y:ZMod 2):z2b (x+y)=xor (z2b x) (z2b y):=by
 rcases qF x with rfl|rfl <;> rcases qF y with rfl|rfl <;> rfl
theorem yX (x y:ZMod 2):z2b (x * y)=(z2b x&&z2b y):=by
 rcases qF x with rfl|rfl <;> rcases qF y with rfl|rfl <;> rfl
theorem wg (a b:Bool):b2z (xor a b)=b2z a+b2z b:=by
 cases a <;> cases b <;> rfl
theorem we (a b:Bool):b2z (a&&b)=b2z a * b2z b:=by
 cases a <;> cases b <;> rfl
theorem qj (x:ZMod 2):x+x=0:=by
 rcases qF x with rfl|rfl <;> rfl
theorem jA (x:ZMod 2):x * x=x:=by
 rcases qF x with rfl|rfl <;> rfl
theorem j4 {α:Type*} (l:List α) (f:α→ZMod 2):
 z2b (l.map f).sum=zv (l.map (fun a=>z2b (f a))):=by
 induction l with
 | nil=>simp [zv,qm]
 | cons a l ih=>
   simp only [List.map_cons,List.sum_cons,vW,ih,zv,List.foldr_cons]
theorem y4 {n:ℕ} (f:Fin n→ZMod 2):
 z2b (∑ i:Fin n,f i)=zv ((List.finRange n).map (fun i=>z2b (f i))):=by
 rw [Fin.sum_univ_def,j4]
structure qc (m:ℕ) where
 B:Fin m→Fin m→ZMod 2
 l:Fin m→ZMod 2
 c:ZMod 2
def qc.Valid {m:ℕ} (Q:qc m):Prop:=
 (∀ i,Q.B i i=0)∧(∀ i j,Q.B i j=Q.B j i)
def qc.zero (m:ℕ):qc m:=⟨fun _ _=>0,fun _=>0,0⟩
def qc.add {m:ℕ} (P Q:qc m):qc m:=
 ⟨fun i j=>P.B i j+Q.B i j,fun i=>P.l i+Q.l i,P.c+Q.c⟩
def qc.eval {m:ℕ} (Q:qc m) (a:Fin m→ZMod 2):ZMod 2:=
 Q.c+∑ i:Fin m,Q.l i * a i +
  ∑ i:Fin m,∑ j:Fin m,if i.val<j.val then Q.B i j * a i * a j else 0
theorem qc.uW {m:ℕ} (a:Fin m→ZMod 2):
 (qc.zero m).eval a=0:=by
 simp [qc.eval,qc.zero]
theorem qc.uK (m:ℕ):(qc.zero m).Valid:=
 ⟨fun _=>rfl,fun _ _=>rfl⟩
theorem qc.wb {m:ℕ} {P Q:qc m} (hP:P.Valid) (hQ:Q.Valid):
 (P.add Q).Valid:=
 ⟨fun i=>by simp [qc.add,hP.1 i,hQ.1 i],
  fun i j=>by simp [qc.add,hP.2 i j,hQ.2 i j]⟩
theorem qc.jV {m:ℕ} (P Q:qc m) (a:Fin m→ZMod 2):
 (P.add Q).eval a=P.eval a+Q.eval a:=by
 unfold qc.eval qc.add
 have h1:(∑ i:Fin m,(P.l i+Q.l i) * a i)=
  (∑ i:Fin m,P.l i * a i)+(∑ i:Fin m,Q.l i * a i):=by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _=>add_mul _ _ _)
 have h2:(∑ i:Fin m,∑ j:Fin m,if i.val<j.val then (P.B i j+Q.B i j) * a i * a j else 0)=
  (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then P.B i j * a i * a j else 0) +
  (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then Q.B i j * a i * a j else 0):=by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _=>?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _=>?_)
  by_cases h:i.val<j.val <;> simp only [h,↓reduceIte,add_zero]
  ring
 rw [h1,h2]
 ring
def qc.addAffineProd {m:ℕ} (Q:qc m)
    (e0:ZMod 2) (e:Fin m→ZMod 2) (f0:ZMod 2) (f:Fin m→ZMod 2):qc m:=
 { B:=fun i j=>if i=j then 0 else Q.B i j+e i * f j+e j * f i
   l:=fun i=>Q.l i+e0 * f i+f0 * e i+e i * f i
   c:=Q.c+e0 * f0 }
theorem qc.yQ {m:ℕ} {Q:qc m} (hQ:Q.Valid)
 (e0:ZMod 2) (e:Fin m→ZMod 2) (f0:ZMod 2) (f:Fin m→ZMod 2):
 (Q.addAffineProd e0 e f0 f).Valid:=by
 refine ⟨fun i=>by simp [qc.addAffineProd],fun i j=>?_⟩
 by_cases hij:i=j
 · subst hij; simp [qc.addAffineProd]
 · have hji:j≠i:=Ne.symm hij
   simp only [qc.addAffineProd,hij,hji,↓reduceIte,hQ.2 i j]
   ring
theorem qc.v5 {m:ℕ} (Q:qc m)
 (e0:ZMod 2) (e:Fin m→ZMod 2) (f0:ZMod 2) (f:Fin m→ZMod 2)
 (a:Fin m→ZMod 2):
 (Q.addAffineProd e0 e f0 f).eval a=
   Q.eval a+(e0+∑ i:Fin m,e i * a i) * (f0+∑ i:Fin m,f i * a i):=by
 have hprod:(e0+∑ i:Fin m,e i * a i) * (f0+∑ j:Fin m,f j * a j)=
  e0 * f0 +
  (∑ i:Fin m,(e0 * f i+f0 * e i+e i * f i) * a i) +
  (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then (e i * f j+e j * f i) * a i * a j else 0):=by
  have hexp:(e0+∑ i:Fin m,e i * a i) * (f0+∑ j:Fin m,f j * a j)=
   e0 * f0+(∑ j:Fin m,e0 * (f j * a j))+(∑ i:Fin m,(e i * a i) * f0) +
   (∑ i:Fin m,∑ j:Fin m,(e i * a i) * (f j * a j)):=by
   rw [add_mul,mul_add,mul_add,Finset.mul_sum,Finset.sum_mul]
   have hdd:(∑ i:Fin m,e i * a i) * (∑ j:Fin m,f j * a j)=
    ∑ i:Fin m,∑ j:Fin m,(e i * a i) * (f j * a j):=by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _=>Finset.mul_sum _ _ _)
   rw [hdd]
   ring
  have hsplit:(∑ i:Fin m,∑ j:Fin m,(e i * a i) * (f j * a j))=
   (∑ i:Fin m,e i * f i * a i) +
   (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then e i * f j * a i * a j else 0) +
   (∑ i:Fin m,∑ j:Fin m,if j.val< i.val then e i * f j * a i * a j else 0):=by
   have hterm:∀ i j:Fin m,
    (e i * a i) * (f j * a j)=
    (if i=j then e i * f i * a i else 0) +
    (if i.val<j.val then e i * f j * a i * a j else 0) +
    (if j.val< i.val then e i * f j * a i * a j else 0):=by
    intro i j
    rcases lt_trichotomy i.val j.val with hlt|heq|hgt
    · have hne:i≠j:=fun h=>by rw [h] at hlt; exact lt_irrefl _ hlt
      have hngt:¬ j.val< i.val:=by omega
      simp only [hne,hlt,hngt,↓reduceIte,zero_add,add_zero]
      ring
    · have hij:i=j:=Fin.ext heq
      subst hij
      simp only [lt_irrefl,↓reduceIte,add_zero]
      have:a i * a i=a i:=jA (a i)
      calc
       e i * a i * (f i * a i)=e i * f i * (a i * a i):=by ring
       _=e i * f i * a i:=by rw [this]
    · have hne:i≠j:=fun h=>by rw [h] at hgt; exact lt_irrefl _ hgt
      have hnlt:¬ i.val<j.val:=by omega
      simp only [hne,hnlt,hgt,↓reduceIte,zero_add]
      ring
   simp_rw [hterm,Finset.sum_add_distrib]
   congr 2
   refine Finset.sum_congr rfl (fun i _=>?_)
   simp
  have hswap:(∑ i:Fin m,∑ j:Fin m,if j.val< i.val then e i * f j * a i * a j else 0)=
   ∑ i:Fin m,∑ j:Fin m,if i.val<j.val then e j * f i * a i * a j else 0:=by
   rw [Finset.sum_comm]
   refine Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>?_))
   by_cases h:i.val<j.val <;> simp only [h,↓reduceIte]
   ring
  rw [hexp,hsplit,hswap]
  have hlin:(∑ j:Fin m,e0 * (f j * a j))+(∑ i:Fin m,e i * a i * f0) +
   (∑ i:Fin m,e i * f i * a i)=
   ∑ i:Fin m,(e0 * f i+f0 * e i+e i * f i) * a i:=by
   rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
   refine Finset.sum_congr rfl (fun i _=>by ring)
  have hquad:
   (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then e i * f j * a i * a j else 0) +
   (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then e j * f i * a i * a j else 0)=
   ∑ i:Fin m,∑ j:Fin m,if i.val<j.val then (e i * f j+e j * f i) * a i * a j else 0:=by
   rw [← Finset.sum_add_distrib]
   refine Finset.sum_congr rfl (fun i _=>?_)
   rw [← Finset.sum_add_distrib]
   refine Finset.sum_congr rfl (fun j _=>?_)
   by_cases h:i.val<j.val <;> simp only [h,↓reduceIte,add_zero]
   ring
  calc
   e0 * f0+(∑ j,e0 * (f j * a j))+(∑ i,e i * a i * f0) +
       ((∑ i,e i * f i * a i) +
         (∑ i,∑ j,if i.val<j.val then e i * f j * a i * a j else 0) +
         (∑ i,∑ j,if i.val<j.val then e j * f i * a i * a j else 0))=
    e0 * f0+((∑ j,e0 * (f j * a j))+(∑ i,e i * a i * f0)+(∑ i,e i * f i * a i)) +
     ((∑ i,∑ j,if i.val<j.val then e i * f j * a i * a j else 0) +
       (∑ i,∑ j,if i.val<j.val then e j * f i * a i * a j else 0)):=by ring
   _=_:=by rw [hlin,hquad]
 rw [hprod]
 unfold qc.eval qc.addAffineProd
 have h1:(∑ i:Fin m,(Q.l i+e0 * f i+f0 * e i+e i * f i) * a i)=
  (∑ i:Fin m,Q.l i * a i)+(∑ i:Fin m,(e0 * f i+f0 * e i+e i * f i) * a i):=by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _=>by ring)
 have h2:(∑ i:Fin m,∑ j:Fin m,
       if i.val<j.val then (if i=j then 0 else Q.B i j+e i * f j+e j * f i) * a i * a j else 0)=
  (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then Q.B i j * a i * a j else 0) +
  (∑ i:Fin m,∑ j:Fin m,if i.val<j.val then (e i * f j+e j * f i) * a i * a j else 0):=by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _=>?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _=>?_)
  by_cases h:i.val<j.val
  · have hne:i≠j:=fun heq=>by rw [heq] at h; exact lt_irrefl _ h
    simp only [h,hne,↓reduceIte]
    ring
  · simp only [h,↓reduceIte,add_zero]
 rw [h1,h2]
 ring
theorem qc.jZ {m:ℕ} {Q:qc m} (hQ:Q.Valid) (r s:Fin m):
 let unit:=fun (j i:Fin m)=>(if i=j then 1 else 0:ZMod 2)
 Q.eval (unit r+unit s)+Q.eval (unit r)+Q.eval (unit s)+Q.eval 0=Q.B r s:=by
 intro unit
 by_cases hrs:r=s
 · subst hrs
   have h0:unit r+unit r=0:=by
    funext i; simp [unit,qj]
   rw [h0,hQ.1 r]
   have h1:Q.eval 0+Q.eval (unit r)+Q.eval (unit r)+Q.eval 0=
    (Q.eval 0+Q.eval 0)+(Q.eval (unit r)+Q.eval (unit r)):=by ring
   rw [h1,qj,qj,add_zero]
 · have heval0:Q.eval 0=Q.c:=by simp [qc.eval]
   have heval1:∀ u:Fin m,Q.eval (unit u)=Q.c+Q.l u:=by
    intro u
    unfold qc.eval
    have hl:∑ i:Fin m,Q.l i * unit u i=Q.l u:=by
     rw [Finset.sum_eq_single u]
     · simp [unit]
     · intro i _ hiu; simp [unit,hiu]
     · intro h; exact absurd (Finset.mem_univ _) h
    have hq:∑ i:Fin m,∑ j:Fin m,
     (if i.val<j.val then Q.B i j * unit u i * unit u j else 0)=0:=by
     refine Finset.sum_eq_zero (fun i _=>Finset.sum_eq_zero (fun j _=>?_))
     by_cases hlt:i.val<j.val
     · have hne:i≠j:=fun h=>by rw [h] at hlt; exact lt_irrefl _ hlt
       by_cases hi:i=u
       · subst hi; simp [unit,hlt,Ne.symm hne]
       · simp [unit,hlt,hi]
     · simp [hlt]
    rw [hl,hq,add_zero]
   have heval2:∀ u v:Fin m,u.val<v.val→
    Q.eval (unit u+unit v)=Q.c+Q.l u+Q.l v+Q.B u v:=by
    intro u v huv
    have huv_ne:u≠v:=fun h=>by rw [h] at huv; exact lt_irrefl _ huv
    unfold qc.eval
    have hl:∑ i:Fin m,Q.l i * (unit u+unit v) i=Q.l u+Q.l v:=by
     have hsp:∀ i:Fin m,Q.l i * (unit u+unit v) i=
      Q.l i * unit u i+Q.l i * unit v i:=fun i=>mul_add _ _ _
     simp_rw [hsp,Finset.sum_add_distrib]
     congr 1
     · rw [Finset.sum_eq_single u]
       · simp [unit]
       · intro i _ hiu; simp [unit,hiu]
       · intro h; exact absurd (Finset.mem_univ _) h
     · rw [Finset.sum_eq_single v]
       · simp [unit]
       · intro i _ hiv; simp [unit,hiv]
       · intro h; exact absurd (Finset.mem_univ _) h
    have hq:∑ i:Fin m,∑ j:Fin m,
     (if i.val<j.val then Q.B i j * (unit u+unit v) i * (unit u+unit v) j else 0)=
     Q.B u v:=by
     rw [Finset.sum_eq_single u]
     · rw [Finset.sum_eq_single v]
       · simp [unit,huv,huv_ne,Ne.symm huv_ne]
       · intro j _ hjv
         by_cases hlt:u.val<j.val
         · have hju:j≠u:=fun h=>by rw [h] at hlt; exact lt_irrefl _ hlt
           simp [unit,hlt,hjv,hju]
         · simp [hlt]
       · intro h; exact absurd (Finset.mem_univ _) h
     · intro i _ hiu
       refine Finset.sum_eq_zero (fun j _=>?_)
       by_cases hlt:i.val<j.val
       · by_cases hiv:i=v
         · subst hiv
           have hji:j≠i:=fun h=>by rw [h] at hlt; exact lt_irrefl _ hlt
           have hju:j≠u:=fun h=>by rw [h] at hlt; omega
           simp [unit,hlt,hji,hju]
         · simp [unit,hlt,hiu,hiv]
       · simp [hlt]
     · intro h; exact absurd (Finset.mem_univ _) h
    rw [hl,hq]
    ring
   rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hrs) with hlt|hgt
   · rw [heval2 r s hlt,heval1 r,heval1 s,heval0]
     have h1:(Q.c+Q.l r+Q.l s+Q.B r s)+(Q.c+Q.l r)+(Q.c+Q.l s)+Q.c=
      Q.B r s+(Q.c+Q.c)+(Q.c+Q.c)+(Q.l r+Q.l r)+(Q.l s+Q.l s):=by ring
     rw [h1,qj Q.c,qj (Q.l r),qj (Q.l s)]
     ring
   · rw [add_comm (unit r) (unit s),heval2 s r hgt,heval1 r,heval1 s,heval0,hQ.2 s r]
     have h1:(Q.c+Q.l s+Q.l r+Q.B r s)+(Q.c+Q.l r)+(Q.c+Q.l s)+Q.c=
      Q.B r s+(Q.c+Q.c)+(Q.c+Q.c)+(Q.l r+Q.l r)+(Q.l s+Q.l s):=by ring
     rw [h1,qj Q.c,qj (Q.l r),qj (Q.l s)]
     ring
def qc.delVar {m:ℕ} (Q:qc m) (i:Fin m):qc m:=
 { B:=fun u v=>if u=i∨v=i then 0 else Q.B u v
   l:=fun u=>if u=i then 0 else Q.l u
   c:=Q.c }
theorem qc.ko {m:ℕ} {Q:qc m} (hQ:Q.Valid) (i:Fin m):
 (Q.delVar i).Valid:=by
 refine ⟨fun u=>?_,fun u v=>?_⟩
 · by_cases h:u=i <;> simp [qc.delVar,h,hQ.1 u]
 · by_cases hu:u=i <;> by_cases hv:v=i <;> simp [qc.delVar,hu,hv,hQ.2 u v]
theorem qc.vw {m:ℕ} {Q:qc m} (hQ:Q.Valid) (i:Fin m)
 (a:Fin m→ZMod 2):
 Q.eval a=(Q.delVar i).eval a +
  a i * (Q.l i+∑ u:Fin m,(if u=i then 0 else Q.B i u) * a u):=by
 unfold qc.eval qc.delVar
 have hlin:(∑ u:Fin m,Q.l u * a u)=
  (∑ u:Fin m,(if u=i then 0 else Q.l u) * a u)+Q.l i * a i:=by
  have hsp:∀ u:Fin m,Q.l u * a u=
   (if u=i then 0 else Q.l u) * a u+(if u=i then Q.l i * a i else 0):=by
   intro u
   by_cases h:u=i <;> simp [h]
  rw [Finset.sum_congr rfl (fun u _=>hsp u),Finset.sum_add_distrib]
  congr 1
  simp
 have hquad:
  (∑ u:Fin m,∑ v:Fin m,if u.val<v.val then Q.B u v * a u * a v else 0)=
  (∑ u:Fin m,∑ v:Fin m,
    if u.val<v.val then (if u=i∨v=i then 0 else Q.B u v) * a u * a v else 0) +
  a i * (∑ u:Fin m,(if u=i then 0 else Q.B i u) * a u):=by
  have hsp:∀ u v:Fin m,
   (if u.val<v.val then Q.B u v * a u * a v else 0)=
   (if u.val<v.val then (if u=i∨v=i then 0 else Q.B u v) * a u * a v else 0) +
   ((if u=i∧u.val<v.val then Q.B i v * a i * a v else 0) +
    (if v=i∧u.val<v.val then Q.B u i * a u * a i else 0)):=by
   intro u v
   by_cases hlt:u.val<v.val
   · have hne:u≠v:=fun h=>by rw [h] at hlt; exact lt_irrefl _ hlt
     by_cases hu:u=i
     · subst hu
       have hvi:v≠u:=Ne.symm hne
       simp [hlt,hvi]
     · by_cases hv:v=i
       · subst hv; simp [hlt,hu]
       · simp [hlt,hu,hv]
   · simp [hlt]
  rw [Finset.sum_congr rfl (fun u _=>Finset.sum_congr rfl (fun v _=>hsp u v))]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  have hA:(∑ u:Fin m,∑ v:Fin m,if u=i∧u.val<v.val then Q.B i v * a i * a v else 0)=
   ∑ v:Fin m,if i.val<v.val then Q.B i v * a i * a v else 0:=by
   rw [Finset.sum_eq_single i]
   · simp
   · intro u _ hui; simp [hui]
   · intro h; exact absurd (Finset.mem_univ _) h
  have hB:(∑ u:Fin m,∑ v:Fin m,if v=i∧u.val<v.val then Q.B u i * a u * a i else 0)=
   ∑ u:Fin m,if u.val< i.val then Q.B i u * a i * a u else 0:=by
   refine Finset.sum_congr rfl (fun u _=>?_)
   rw [Finset.sum_eq_single i]
   · by_cases hlt:u.val< i.val
     · simp only [hlt,and_self,↓reduceIte,hQ.2 u i]; ring
     · simp [hlt]
   · intro v _ hvi; simp [hvi]
   · intro h; exact absurd (Finset.mem_univ _) h
  rw [hA,hB,← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _=>?_)
  rcases lt_trichotomy i.val u.val with hlt|heq|hgt
  · have hui:u≠i:=fun h=>by rw [h] at hlt; exact lt_irrefl _ hlt
    have hngt:¬ u.val< i.val:=by omega
    simp only [hlt,hngt,hui,↓reduceIte,add_zero]
    ring
  · have hui:u=i:=Fin.ext heq.symm
    subst hui
    simp
  · have hui:u≠i:=fun h=>by rw [h] at hgt; exact lt_irrefl _ hgt
    have hnlt:¬ i.val<u.val:=by omega
    simp only [hnlt,hgt,hui,↓reduceIte,zero_add]
    ring
 rw [hlin,hquad]
 ring
structure vM (R C P:ℕ) where
 used:Fin R→Bool
 M:Fin R→Fin C→ZMod 2
 Pay:Fin R→Fin P→ZMod 2
def qu {R C P:ℕ} (col:ℕ) (st:vM R C P):vM R C P:=
 if hcol:col<C then
  let c0:Fin C:=⟨col,hcol⟩
  let cond:Fin R→Bool:=fun r=>!(st.used r)&&z2b (st.M r c0)
  let isPiv:Fin R→Bool:=qi cond
  let pivM:Fin C→ZMod 2:=fun c=>
   b2z ((List.finRange R).any (fun r=>isPiv r&&z2b (st.M r c)))
  let pivP:Fin P→ZMod 2:=fun p=>
   b2z ((List.finRange R).any (fun r=>isPiv r&&z2b (st.Pay r p)))
  { used:=fun r=>st.used r||isPiv r
    M:=fun r c=>if !(isPiv r)&&z2b (st.M r c0) then st.M r c+pivM c else st.M r c
    Pay:=fun r p=>if !(isPiv r)&&z2b (st.M r c0) then st.Pay r p+pivP p else st.Pay r p }
 else st
def qA {R C P:ℕ} (M0:Fin R→Fin C→ZMod 2) (Pay0:Fin R→Fin P→ZMod 2):
    vM R C P:=
 (List.range C).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay0⟩
theorem kE {R C P:ℕ} (col:ℕ) (hcol:col<C) (st:vM R C P):
 let c0:Fin C:=⟨col,hcol⟩
 let cond:Fin R→Bool:=fun r=>!(st.used r)&&z2b (st.M r c0)
 let st':=qu col st
 (∀ r,st'.used r=true↔st.used r=true∨qi cond r=true)∧
 ((∀ r,cond r=false)→st'=st)∧
 (∀ p0,qi cond p0=true→
   st'.M p0=st.M p0∧st'.Pay p0=st.Pay p0∧
   ∀ r,r≠p0→
     st'.M r=st.M r+(st.M r c0) • st.M p0∧
     st'.Pay r=st.Pay r+(st.M r c0) • st.Pay p0):=by
 intro c0 cond st'
 have hst':st'=
  let isPiv:Fin R→Bool:=qi cond
  let pivM:Fin C→ZMod 2:=fun c=>
   b2z ((List.finRange R).any (fun r=>isPiv r&&z2b (st.M r c)))
  let pivP:Fin P→ZMod 2:=fun p=>
   b2z ((List.finRange R).any (fun r=>isPiv r&&z2b (st.Pay r p)))
  { used:=fun r=>st.used r||isPiv r
    M:=fun r c=>if !(isPiv r)&&z2b (st.M r c0) then st.M r c+pivM c else st.M r c
    Pay:=fun r p=>if !(isPiv r)&&z2b (st.M r c0) then st.Pay r p+pivP p else st.Pay r p }:=by
  simp only [st',qu,hcol,↓reduceDIte,c0,cond]
 refine ⟨?_,?_,?_⟩
 · intro r
   rw [hst']
   simp
 · intro hnone
   have hnoPiv:∀ r,qi cond r=false:=by
    intro r
    cases h:qi cond r
    · rfl
    · have:=((qU cond r).mp h).1
      rw [hnone r] at this
      exact Bool.noConfusion this
   rw [hst']
   cases st with
   | mk u M Pay=>
     have hany0:((List.finRange R).any (fun _=>false))=false:=by simp
     dsimp only
     congr 1
     · funext r; simp [hnoPiv r]
     · funext r c
       simp only [hnoPiv,Bool.false_and,hany0,b2z,Bool.false_eq_true,↓reduceIte,add_zero,ite_self]
     · funext r p
       simp only [hnoPiv,Bool.false_and,hany0,b2z,Bool.false_eq_true,↓reduceIte,add_zero,ite_self]
 · intro p0 hp0
   have huniq:∀ r,qi cond r=true↔r=p0:=fun r=>
    ⟨fun h=>q2 cond h hp0,fun h=>h▸hp0⟩
   have hpivM:∀ c,b2z ((List.finRange R).any (fun r=>qi cond r&&z2b (st.M r c)))=
    st.M p0 c:=by
    intro c
    have hany:((List.finRange R).any (fun r=>qi cond r&&z2b (st.M r c)))=
     z2b (st.M p0 c):=by
     cases h:z2b (st.M p0 c)
     · rw [List.any_eq_false]
       intro r _
       by_cases hr:r=p0
       · subst hr; simp [h]
       · have hf:qi cond r=false:=by
          cases h':qi cond r
          · rfl
          · exact absurd ((huniq r).mp h') hr
         simp [hf]
     · rw [List.any_eq_true]
       exact ⟨p0,List.mem_finRange p0,by simp [hp0,h]⟩
    rw [hany,vr]
   have hpivP:∀ p,b2z ((List.finRange R).any (fun r=>qi cond r&&z2b (st.Pay r p)))=
    st.Pay p0 p:=by
    intro p
    have hany:((List.finRange R).any (fun r=>qi cond r&&z2b (st.Pay r p)))=
     z2b (st.Pay p0 p):=by
     cases h:z2b (st.Pay p0 p)
     · rw [List.any_eq_false]
       intro r _
       by_cases hr:r=p0
       · subst hr; simp [h]
       · have hf:qi cond r=false:=by
          cases h':qi cond r
          · rfl
          · exact absurd ((huniq r).mp h') hr
         simp [hf]
     · rw [List.any_eq_true]
       exact ⟨p0,List.mem_finRange p0,by simp [hp0,h]⟩
    rw [hany,vr]
   rw [hst']
   refine ⟨?_,?_,?_⟩
   · funext c; simp [hp0]
   · funext p; simp [hp0]
   · intro r hr
     have hrf:qi cond r=false:=by
      cases h':qi cond r
      · rfl
      · exact absurd ((huniq r).mp h') hr
     refine ⟨?_,?_⟩
     · funext c
       simp only [hrf,Bool.not_false,Bool.true_and,hpivM,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
       rcases qF (st.M r c0) with h0|h1
       · simp [h0,qm]
       · simp [h1,zA]
     · funext p
       simp only [hrf,Bool.not_false,Bool.true_and,hpivP,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
       rcases qF (st.M r c0) with h0|h1
       · simp [h0,qm]
       · simp [h1,zA]
theorem qv {R C P:ℕ}
 (M0:Fin R→Fin C→ZMod 2) (Pay0:Fin R→Fin P→ZMod 2):
 let st:=qA M0 Pay0
 Submodule.span (ZMod 2) (Set.range st.M)=Submodule.span (ZMod 2) (Set.range M0)∧
 (∀ r,st.used r=true→∃ c:Fin C,st.M r c=1∧∀ j,j≠r→st.M j c=0)∧
 (∀ r,st.used r=false→∀ c:Fin C,st.M r c=0)∧
 (∀ (α:Type) [AddCommGroup α] [Module (ZMod 2) α] (f:(Fin C→ZMod 2)→(Fin P→ZMod 2)→α),
   (∀ m1 m2 p1 p2,f (m1+m2) (p1+p2)=f m1 p1+f m2 p2)→
   ((∀ r,f (st.M r) (st.Pay r)=0)↔(∀ r,f (M0 r) (Pay0 r)=0)))∧
 (∀ (PropRow:(Fin C→ZMod 2)→Prop),
   PropRow 0→(∀ u v,PropRow u→PropRow v→PropRow (u+v))→
   (∀ r,PropRow (M0 r))→(∀ r,PropRow (st.M r))):=by
 have hloop:∀ t≤C,
  let st:=(List.range t).foldl (fun s col=>qu col s) ⟨fun _=>false,M0,Pay0⟩
  Submodule.span (ZMod 2) (Set.range st.M)=Submodule.span (ZMod 2) (Set.range M0)∧
  (∀ r,st.used r=true→∃ c:Fin C,c.val<t∧st.M r c=1∧∀ j,j≠r→st.M j c=0)∧
  (∀ r,st.used r=false→∀ c:Fin C,c.val<t→st.M r c=0)∧
  (∀ (α:Type) [AddCommGroup α] [Module (ZMod 2) α] (f:(Fin C→ZMod 2)→(Fin P→ZMod 2)→α),
    (∀ m1 m2 p1 p2,f (m1+m2) (p1+p2)=f m1 p1+f m2 p2)→
    ((∀ r,f (st.M r) (st.Pay r)=0)↔(∀ r,f (M0 r) (Pay0 r)=0)))∧
  (∀ (PropRow:(Fin C→ZMod 2)→Prop),
    PropRow 0→(∀ u v,PropRow u→PropRow v→PropRow (u+v))→
    (∀ r,PropRow (M0 r))→(∀ r,PropRow (st.M r))):=by
  intro t
  induction t with
  | zero=>
    intro _
    refine ⟨rfl,?_,?_,?_,?_⟩
    · intro r h; exact Bool.noConfusion h
    · intro r _ c hc; omega
    · intro _ _ _ _ _; exact Iff.rfl
    · intro _ _ _ h; exact h
  | succ t ih=>
    intro ht
    rcases ih (by omega) with ⟨hspan,hpiv,hzero,hlin,hprop⟩
    let st:=(List.range t).foldl (fun s col=>qu col s) ⟨fun _=>false,M0,Pay0⟩
    have hst_next:(List.range (t+1)).foldl (fun s col=>qu col s)
     ⟨fun _=>false,M0,Pay0⟩=qu t st:=by
     simp [List.range_succ,List.foldl_append,st]
    rw [hst_next]
    have hcol:t<C:=by omega
    let c0:Fin C:=⟨t,hcol⟩
    let cond:Fin R→Bool:=fun r=>!(st.used r)&&z2b (st.M r c0)
    rcases kE t hcol st with ⟨hused,hnone,hsome⟩
    by_cases hex:∃ r:Fin R,cond r=true
    · rcases (q0 cond).mpr hex with ⟨p0,hp0⟩
      rcases hsome p0 hp0 with ⟨hMp0,hPp0,hother⟩
      have hp0_cond:=((qU cond p0).mp hp0).1
      have hp0_unused:st.used p0=false:=by
       simp only [cond,Bool.and_eq_true,Bool.not_eq_true'] at hp0_cond
       exact hp0_cond.1
      have hp0_one:st.M p0 c0=1:=by
       simp only [cond,Bool.and_eq_true] at hp0_cond
       have:=hp0_cond.2
       rcases qF (st.M p0 c0) with h|h
       · simp [h,qm] at this
       · exact h
      have hstep_span:Submodule.span (ZMod 2) (Set.range (qu t st).M)=
       Submodule.span (ZMod 2) (Set.range st.M):=by
       apply le_antisymm
       · rw [Submodule.span_le]
         rintro _ ⟨r,rfl⟩
         by_cases hr:r=p0
         · subst hr; rw [hMp0]; exact Submodule.subset_span ⟨r,rfl⟩
         · rw [(hother r hr).1]
           exact Submodule.add_mem _ (Submodule.subset_span ⟨r,rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p0,rfl⟩))
       · rw [Submodule.span_le]
         rintro _ ⟨r,rfl⟩
         by_cases hr:r=p0
         · subst hr; rw [← hMp0]; exact Submodule.subset_span ⟨r,rfl⟩
         · have heq:st.M r=(qu t st).M r+(st.M r c0) • (qu t st).M p0:=by
            rw [(hother r hr).1,hMp0,add_assoc]
            have h2:(st.M r c0) • st.M p0+(st.M r c0) • st.M p0=0:=by
             funext c; simp [qj]
            rw [h2,add_zero]
           rw [heq]
           exact Submodule.add_mem _ (Submodule.subset_span ⟨r,rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p0,rfl⟩))
      refine ⟨hstep_span.trans hspan,?_,?_,?_,?_⟩
      · intro r hr
        rcases (hused r).mp hr with hr_old|hr_new
        · rcases hpiv r hr_old with ⟨c,hct,hrc1,hoth⟩
          have hp0_ne:p0≠r:=fun h=>by rw [h,hr_old] at hp0_unused; exact Bool.noConfusion hp0_unused
          have hp0c0:st.M p0 c=0:=hoth p0 hp0_ne
          refine ⟨c,by omega,?_,?_⟩
          · have hrp0:r≠p0:=Ne.symm hp0_ne
            have:=congrFun (hother r hrp0).1 c
            rw [this,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp0c0,mul_zero,add_zero,hrc1]
          · intro j hj
            by_cases hjp0:j=p0
            · subst hjp0; rw [hMp0]; exact hp0c0
            · have:=congrFun (hother j hjp0).1 c
              rw [this,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp0c0,mul_zero,add_zero,hoth j hj]
        · have hrp0:r=p0:=q2 cond hr_new hp0
          subst hrp0
          refine ⟨c0,by simp [c0],by rw [hMp0]; exact hp0_one,?_⟩
          intro j hj
          have:=congrFun (hother j hj).1 c0
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp0_one,mul_one] at this
          rw [this,qj]
      · intro r hr c hc
        have hr_old:st.used r=false:=by
         cases hu:st.used r
         · rfl
         · have:=(hused r).mpr (Or.inl hu)
           rw [hr] at this; exact Bool.noConfusion this
        have hr_ne:r≠p0:=by
         intro h; subst h
         have:=(hused r).mpr (Or.inr hp0)
         rw [hr] at this; exact Bool.noConfusion this
        have hm:=congrFun (hother r hr_ne).1 c
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hm
        by_cases hct:c.val<t
        · rw [hm,hzero r hr_old c hct,hzero p0 hp0_unused c hct,mul_zero,add_zero]
        · have hce:c=c0:=Fin.ext (by dsimp [c0]; omega)
          subst hce
          rw [hm,hp0_one,mul_one,qj]
      · intro α _ _ f hf
        rw [← hlin α f hf]
        have hscale:∀ (s:ZMod 2) m1 m2 p1 p2,
         f (m1+s • m2) (p1+s • p2)=f m1 p1+s • f m2 p2:=by
         intro s m1 m2 p1 p2
         rcases qF s with rfl|rfl
         · simp
         · simpa using hf m1 m2 p1 p2
        constructor
        · intro hall r
          by_cases hr:r=p0
          · subst hr; rw [← hMp0,← hPp0]; exact hall r
          · have h1:=hall r
            have h2:=hall p0
            rw [(hother r hr).1,(hother r hr).2,hscale,← hMp0,← hPp0,h2,smul_zero,add_zero] at h1
            exact h1
        · intro hall r
          by_cases hr:r=p0
          · subst hr; rw [hMp0,hPp0]; exact hall r
          · rw [(hother r hr).1,(hother r hr).2,hscale,hall r,hall p0,smul_zero,add_zero]
      · intro PropRow hP0 hPadd hPM0 r
        have hPrev:=hprop PropRow hP0 hPadd hPM0
        by_cases hr:r=p0
        · subst hr; rw [hMp0]; exact hPrev r
        · rw [(hother r hr).1]
          rcases qF (st.M r c0) with h0|h1
          · rw [h0,zero_smul,add_zero]; exact hPrev r
          · rw [h1,one_smul]; exact hPadd _ _ (hPrev r) (hPrev p0)
    · push Not at hex
      have hallf:∀ r,cond r=false:=fun r=>by
       cases h:cond r
       · rfl
       · exact absurd h (hex r)
      rw [hnone hallf]
      refine ⟨hspan,?_,?_,hlin,hprop⟩
      · intro r hr
        rcases hpiv r hr with ⟨c,hct,h1,h2⟩
        exact ⟨c,by omega,h1,h2⟩
      · intro r hr c hc
        by_cases hct:c.val<t
        · exact hzero r hr c hct
        · have hce:c=c0:=Fin.ext (by dsimp [c0]; omega)
          subst hce
          have hcf:=hallf r
          simp only [cond,hr,Bool.not_false,Bool.true_and] at hcf
          rcases qF (st.M r c0) with h|h
          · exact h
          · simp [h,zA] at hcf
 rcases hloop C le_rfl with ⟨hspan,hpiv,hzero,hlin,hprop⟩
 refine ⟨hspan,?_,?_,hlin,hprop⟩
 · intro r hr
   rcases hpiv r hr with ⟨c,_,h1,h2⟩
   exact ⟨c,h1,h2⟩
 · intro r hr c
   exact hzero r hr c c.isLt
theorem zw {R C P:ℕ}
 (M0:Fin R→Fin C→ZMod 2) (Pay0:Fin R→Fin P→ZMod 2):
 let st:=qA M0 Pay0
 (Finset.univ.filter (fun r:Fin R=>st.used r=true)).card=
   Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M0)):=by
 classical
 intro st
 rcases qv M0 Pay0 with ⟨hspan,hpiv,hzero,_,_⟩
 let U:Finset (Fin R):=Finset.univ.filter (fun r:Fin R=>st.used r=true)
 let S:Submodule (ZMod 2) (Fin C→ZMod 2):=Submodule.span (ZMod 2) (Set.range M0)
 have hmemS:∀ r:U,st.M r.val∈S:=by
  intro r
  change st.M r.val∈Submodule.span (ZMod 2) (Set.range M0)
  rw [← hspan]
  exact Submodule.subset_span ⟨r.val,rfl⟩
 let v:U→S:=fun r=>⟨st.M r.val,hmemS r⟩
 have hli:LinearIndependent (ZMod 2) v:=by
  rw [Fintype.linearIndependent_iff]
  intro a ha r
  have hval:=congrArg Subtype.val ha
  simp only [Submodule.coe_sum,SetLike.val_smul,ZeroMemClass.coe_zero,v] at hval
  rcases hpiv r.val (Finset.mem_filter.mp r.2).2 with ⟨c,h1,hoth⟩
  have hc:=congrFun hval c
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hc
  rw [Finset.sum_eq_single r] at hc
  · change a r * (qA M0 Pay0).M r.val c=0 at hc
    rw [h1,mul_one] at hc
    exact hc
  · intro j _ hj
    have hne:j.val≠r.val:=fun h=>hj (Subtype.ext h)
    change a j * (qA M0 Pay0).M j.val c=0
    rw [hoth j.val hne,mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
 have htop:⊤≤Submodule.span (ZMod 2) (Set.range v):=by
  rintro ⟨y,hy⟩ _
  have hy':y∈Submodule.span (ZMod 2) (Set.range st.M):=by rwa [hspan]
  have hmap:Submodule.span (ZMod 2) (Set.range st.M)≤
   Submodule.map S.subtype (Submodule.span (ZMod 2) (Set.range v)):=by
   rw [Submodule.span_le]
   rintro _ ⟨r,rfl⟩
   by_cases hu:st.used r=true
   · have hrU:r∈U:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩
     exact ⟨v ⟨r,hrU⟩,Submodule.subset_span ⟨⟨r,hrU⟩,rfl⟩,rfl⟩
   · have huf:st.used r=false:=by cases h:st.used r <;> simp_all
     have hr0:st.M r=0:=funext (hzero r huf)
     rw [hr0]
     exact Submodule.zero_mem _
  rcases hmap hy' with ⟨w,hw,hwy⟩
  have:w=⟨y,hy⟩:=Subtype.ext hwy
  rwa [← this]
 let b:Module.Basis U (ZMod 2) S:=Module.Basis.mk hli htop
 have hcard:Fintype.card U=Module.finrank (ZMod 2) S:=(Module.finrank_eq_card_basis b).symm
 rw [← Fintype.card_coe]
 exact hcard
def qY {N R C P:ℕ} (st:(Fin N→Bool)→vM R C P):Set (Sig N):=
 Set.range (fun r:Fin R=>fun x=>(st x).used r) ∪
 {f|∃ r c,(fun x=>z2b ((st x).M r c))=f} ∪
 {f|∃ r p,(fun x=>z2b ((st x).Pay r p))=f}
theorem jC {N R C P:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (col:ℕ) (st:(Fin N→Bool)→vM R C P):
 qa (Base ∪ qY st) (qY (fun x=>qu col (st x)))
  (R * (R+4)+(C+P) * (2 * R)+R * (1+(C+P) * 10)):=by
 by_cases hcol:col<C
 · let c0:Fin C:=⟨col,hcol⟩
   let cond:Fin R→Sig N:=fun r x=>!((st x).used r)&&z2b ((st x).M r c0)
   let isPiv:Fin R→Sig N:=fun r x=>qi (fun j=>cond j x) r
   let pivM:Fin C→Sig N:=fun c x=>
    (List.finRange R).any (fun r=>isPiv r x&&z2b ((st x).M r c))
   let pivP:Fin P→Sig N:=fun p x=>
    (List.finRange R).any (fun r=>isPiv r x&&z2b ((st x).Pay r p))
   have hcondB:qa (Base ∪ qY st) (Set.range cond) (R * 2):=by
    refine qf cond 2 (fun r=>?_)
    have h1:qa (Base ∪ qY st) {fun x=>!((st x).used r)} 1:=
     zn (Or.inr (Or.inl (Or.inl ⟨r,rfl⟩)))
    have h2:qa ((Base ∪ qY st) ∪ {fun x=>!((st x).used r)}) {cond r} 1:=
     qD (Or.inr rfl) (Or.inl (Or.inr (Or.inl (Or.inr ⟨r,c0,rfl⟩))))
    exact qe h1 h2
   have hftB:qa ((Base ∪ qY st) ∪ Set.range cond) (Set.range isPiv) (R * (R+2)):=
    yE cond (Or.inl (Or.inl hfalse)) (fun r=>Or.inr ⟨r,rfl⟩)
   let A1:=(Base ∪ qY st) ∪ (Set.range cond ∪ Set.range isPiv)
   have h1:qa (Base ∪ qY st) (Set.range cond ∪ Set.range isPiv) (R * 2+R * (R+2)):=
    zd hcondB hftB
   have hpivMB:qa A1 (Set.range pivM) (C * (2 * R)):=by
    refine qf pivM (2 * R) (fun c=>?_)
    let term:Fin R→Sig N:=fun r x=>isPiv r x&&z2b ((st x).M r c)
    have ht:qa A1 (Set.range term) (R * 1):=
     qf term 1 (fun r=>
      qD (Or.inr (Or.inr ⟨r,rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inr ⟨r,c,rfl⟩)))))
    have hor:qa (A1 ∪ Set.range term) {pivM c} R:=by
     have h:=vt (A:=A1 ∪ Set.range term) ((List.finRange R).map term)
      (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr ⟨r,rfl⟩)
      (Or.inl (Or.inl (Or.inl hfalse)))
     have heq:(fun x=>((List.finRange R).map term).any (fun f=>f x))=pivM c:=by
      funext x; simp [pivM,term,List.any_map]; rfl
     rw [heq,List.length_map,List.length_finRange] at h
     exact h
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
   have hpivPB:qa A1 (Set.range pivP) (P * (2 * R)):=by
    refine qf pivP (2 * R) (fun p=>?_)
    let term:Fin R→Sig N:=fun r x=>isPiv r x&&z2b ((st x).Pay r p)
    have ht:qa A1 (Set.range term) (R * 1):=
     qf term 1 (fun r=>
      qD (Or.inr (Or.inr ⟨r,rfl⟩)) (Or.inl (Or.inr (Or.inr ⟨r,p,rfl⟩))))
    have hor:qa (A1 ∪ Set.range term) {pivP p} R:=by
     have h:=vt (A:=A1 ∪ Set.range term) ((List.finRange R).map term)
      (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr ⟨r,rfl⟩)
      (Or.inl (Or.inl (Or.inl hfalse)))
     have heq:(fun x=>((List.finRange R).map term).any (fun f=>f x))=pivP p:=by
      funext x; simp [pivP,term,List.any_map]; rfl
     rw [heq,List.length_map,List.length_finRange] at h
     exact h
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
   have h2:qa A1 (Set.range pivM ∪ Set.range pivP) (C * (2 * R)+P * (2 * R)):=
    qr hpivMB hpivPB
   let A2:=A1 ∪ (Set.range pivM ∪ Set.range pivP)
   have h3:qa A2 (qY (fun x=>qu col (st x))) (R * (1+(C+P) * 10)):=by
    have husedB:qa A2 (Set.range (fun r:Fin R=>fun x=>(qu col (st x)).used r)) (R * 1):=
     qf _ 1 (fun r=>by
      have heq:(fun x=>(qu col (st x)).used r)=fun x=>(st x).used r||isPiv r x:=by
       funext x; simp [qu,hcol,isPiv,cond,c0]
      rw [heq]
      exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨r,rfl⟩)))))
       (Or.inl (Or.inr (Or.inr ⟨r,rfl⟩))))
    have hMB:qa A2 {f|∃ r c,(fun x=>z2b ((qu col (st x)).M r c))=f} (R * (C * 10)):=
     qT _ 10 (fun r c=>by
      let np:Sig N:=fun x=>!(isPiv r x)
      let flag:Sig N:=fun x=>np x&&z2b ((st x).M r c0)
      let xored:Sig N:=fun x=>xor (z2b ((st x).M r c)) (pivM c x)
      let out:Sig N:=fun x=>if flag x then xored x else z2b ((st x).M r c)
      have hb1:qa A2 {np} 1:=zn (Or.inl (Or.inr (Or.inr ⟨r,rfl⟩)))
      have hb2:qa (A2 ∪ {np}) {flag} 1:=
       qD (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r,c0,rfl⟩))))))
      have hb3:qa ((A2 ∪ {np}) ∪ {flag}) {xored} 4:=
       yW (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r,c,rfl⟩)))))))
        (Or.inl (Or.inl (Or.inr (Or.inl ⟨c,rfl⟩))))
      have hb4:qa (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4:=
       vo (Or.inl (Or.inr rfl)) (Or.inr rfl)
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r,c,rfl⟩))))))))
      have heq:out=fun x=>z2b ((qu col (st x)).M r c):=by
       funext x
       simp only [out,flag,np,xored,qu,hcol,↓reduceDIte,isPiv,cond,c0,pivM]
       cases hf:(!(qi (fun j=>!((st x).used j)&&z2b ((st x).M j c0)) r)&&
        z2b ((st x).M r c0)) <;> simp [vW,z0]
      rw [← heq]
      exact qd (qo (qo (qo (qP hb1) (qP hb2)) (qP hb3)) hb4)
       le_rfl Set.subset_union_right (by omega))
    have hPB:qa A2 {f|∃ r p,(fun x=>z2b ((qu col (st x)).Pay r p))=f} (R * (P * 10)):=
     qT _ 10 (fun r p=>by
      let np:Sig N:=fun x=>!(isPiv r x)
      let flag:Sig N:=fun x=>np x&&z2b ((st x).M r c0)
      let xored:Sig N:=fun x=>xor (z2b ((st x).Pay r p)) (pivP p x)
      let out:Sig N:=fun x=>if flag x then xored x else z2b ((st x).Pay r p)
      have hb1:qa A2 {np} 1:=zn (Or.inl (Or.inr (Or.inr ⟨r,rfl⟩)))
      have hb2:qa (A2 ∪ {np}) {flag} 1:=
       qD (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r,c0,rfl⟩))))))
      have hb3:qa ((A2 ∪ {np}) ∪ {flag}) {xored} 4:=
       yW (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨r,p,rfl⟩))))))
        (Or.inl (Or.inl (Or.inr (Or.inr ⟨p,rfl⟩))))
      have hb4:qa (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4:=
       vo (Or.inl (Or.inr rfl)) (Or.inr rfl)
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨r,p,rfl⟩)))))))
      have heq:out=fun x=>z2b ((qu col (st x)).Pay r p):=by
       funext x
       simp only [out,flag,np,xored,qu,hcol,↓reduceDIte,isPiv,cond,c0,pivP]
       cases hf:(!(qi (fun j=>!((st x).used j)&&z2b ((st x).M j c0)) r)&&
        z2b ((st x).M r c0)) <;> simp [vW,z0]
      rw [← heq]
      exact qd (qo (qo (qo (qP hb1) (qP hb2)) (qP hb3)) hb4)
       le_rfl Set.subset_union_right (by omega))
    exact qd (qr (qr husedB hMB) hPB) le_rfl Set.subset_union_right
     (by ring_nf; omega)
   have hall:=qo (qo (qP h1) (qP h2)) h3
   exact qd hall le_rfl Set.subset_union_right (by ring_nf; omega)
 · have heq:(fun x=>qu col (st x))=st:=by
    funext x; simp [qu,hcol]
   rw [heq]
   exact qd (zk (A:=Base ∪ qY st) (B:=qY st) Set.subset_union_right)
    le_rfl Set.subset_union_right (Nat.zero_le _)
theorem vN {N R C P:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (M0:(Fin N→Bool)→Fin R→Fin C→ZMod 2)
 (Pay0:(Fin N→Bool)→Fin R→Fin P→ZMod 2)
 (hM0:∀ r c,(fun x=>z2b (M0 x r c))∈Base)
 (hPay0:∀ r p,(fun x=>z2b (Pay0 x r p))∈Base):
 qa Base (qY (fun x=>qA (M0 x) (Pay0 x)))
  (C * (R * (R+4)+(C+P) * (2 * R)+R * (1+(C+P) * 10))):=by
 let st0:(Fin N→Bool)→vM R C P:=fun x=>⟨fun _=>false,M0 x,Pay0 x⟩
 have hst0:qY st0⊆Base:=by
  rintro f ((⟨r,rfl⟩|⟨r,c,rfl⟩)|⟨r,p,rfl⟩)
  · exact hfalse
  · exact hM0 r c
  · exact hPay0 r p
 have hit:=jD (Sigs:=qY) (step:=qu)
  (c:=R * (R+4)+(C+P) * (2 * R)+R * (1+(C+P) * 10))
  (Base:=Base) (fun col st=>jC Base hfalse col st) C st0
 exact qd hit (Set.union_subset le_rfl hst0) Set.subset_union_right le_rfl
def qn {N m:ℕ} (Q:(Fin N→Bool)→qc m):Set (Sig N):=
 {f|∃ i j,(fun x=>z2b ((Q x).B i j))=f} ∪
 Set.range (fun i:Fin m=>fun x=>z2b ((Q x).l i)) ∪
 {fun x=>z2b (Q x).c}
theorem kz {N m:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (Q:(Fin N→Bool)→qc m)
 (e0 f0:(Fin N→Bool)→ZMod 2)
 (e f:(Fin N→Bool)→Fin m→ZMod 2)
 (hQ:qn Q⊆Base)
 (he0:(fun x=>z2b (e0 x))∈Base)
 (hf0:(fun x=>z2b (f0 x))∈Base)
 (he:∀ i,(fun x=>z2b (e x i))∈Base)
 (hf:∀ i,(fun x=>z2b (f x i))∈Base):
 qa Base (qn (fun x=>(Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)))
  (m * (m * 10)+m * 15+5):=by
 have hBB:qa Base
  {g|∃ i j,(fun x=>z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).B i j))=g}
  (m * (m * 10)):=by
  refine qT _ 10 (fun i j=>?_)
  by_cases hij:i=j
  · have heq:(fun x=>z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).B i j))=
     fun _=>false:=by
     funext x; simp [qc.addAffineProd,hij,qm]
    rw [heq]
    exact qd (zk (A:=Base) (B:={fun _=>false}) (by simpa using hfalse))
     le_rfl Set.subset_union_right (by omega)
  · let t1:Sig N:=fun x=>z2b (e x i)&&z2b (f x j)
    let t2:Sig N:=fun x=>z2b (e x j)&&z2b (f x i)
    let s1:Sig N:=fun x=>xor (z2b ((Q x).B i j)) (t1 x)
    let s2:Sig N:=fun x=>xor (s1 x) (t2 x)
    have h1:qa Base {t1} 1:=qD (he i) (hf j)
    have h2:qa (Base ∪ {t1}) {t2} 1:=qD (Or.inl (he j)) (Or.inl (hf i))
    have h3:qa ((Base ∪ {t1}) ∪ {t2}) {s1} 4:=
     yW (Or.inl (Or.inl (hQ (Or.inl (Or.inl ⟨i,j,rfl⟩))))) (Or.inl (Or.inr rfl))
    have h4:qa (((Base ∪ {t1}) ∪ {t2}) ∪ {s1}) {s2} 4:=
     yW (Or.inr rfl) (Or.inl (Or.inr rfl))
    have heq:s2=fun x=>z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).B i j):=by
     funext x
     simp only [s2,s1,t1,t2,qc.addAffineProd,hij,↓reduceIte,vW,yX]
    rw [← heq]
    exact qd (qo (qo (qo (qP h1) (qP h2)) (qP h3)) h4)
     le_rfl Set.subset_union_right (by omega)
 have hll:qa Base
  (Set.range (fun i:Fin m=>fun x=>z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).l i)))
  (m * 15):=by
  refine qf _ 15 (fun i=>?_)
  let t1:Sig N:=fun x=>z2b (e0 x)&&z2b (f x i)
  let t2:Sig N:=fun x=>z2b (f0 x)&&z2b (e x i)
  let t3:Sig N:=fun x=>z2b (e x i)&&z2b (f x i)
  let s1:Sig N:=fun x=>xor (z2b ((Q x).l i)) (t1 x)
  let s2:Sig N:=fun x=>xor (s1 x) (t2 x)
  let s3:Sig N:=fun x=>xor (s2 x) (t3 x)
  have h1:qa Base {t1} 1:=qD he0 (hf i)
  have h2:qa (Base ∪ {t1}) {t2} 1:=qD (Or.inl hf0) (Or.inl (he i))
  have h3:qa ((Base ∪ {t1}) ∪ {t2}) {t3} 1:=qD (Or.inl (Or.inl (he i))) (Or.inl (Or.inl (hf i)))
  have h4:qa (((Base ∪ {t1}) ∪ {t2}) ∪ {t3}) {s1} 4:=
   yW (Or.inl (Or.inl (Or.inl (hQ (Or.inl (Or.inr ⟨i,rfl⟩)))))) (Or.inl (Or.inl (Or.inr rfl)))
  have h5:qa ((((Base ∪ {t1}) ∪ {t2}) ∪ {t3}) ∪ {s1}) {s2} 4:=
   yW (Or.inr rfl) (Or.inl (Or.inl (Or.inr rfl)))
  have h6:qa (((((Base ∪ {t1}) ∪ {t2}) ∪ {t3}) ∪ {s1}) ∪ {s2}) {s3} 4:=
   yW (Or.inr rfl) (Or.inl (Or.inl (Or.inr rfl)))
  have heq:s3=fun x=>z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).l i):=by
   funext x
   simp only [s3,s2,s1,t1,t2,t3,qc.addAffineProd,vW,yX]
  rw [← heq]
  exact qd (qo (qo (qo (qo (qo (qP h1) (qP h2)) (qP h3)) (qP h4)) (qP h5)) h6)
   le_rfl Set.subset_union_right (by omega)
 have hcc:qa Base {fun x=>z2b ((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).c} 5:=by
  let t1:Sig N:=fun x=>z2b (e0 x)&&z2b (f0 x)
  let s1:Sig N:=fun x=>xor (z2b (Q x).c) (t1 x)
  have h1:qa Base {t1} 1:=qD he0 hf0
  have h2:qa (Base ∪ {t1}) {s1} 4:=yW (Or.inl (hQ (Or.inr rfl))) (Or.inr rfl)
  have heq:s1=fun x=>z2b ((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).c:=by
   funext x; simp [s1,t1,qc.addAffineProd,vW,yX]
  rw [← heq]
  exact qd (qe h1 h2) le_rfl Set.subset_union_right (by omega)
 exact qd (qr (qr hBB hll) hcc) le_rfl Set.subset_union_right (by omega)
def qw {L:ℕ} (p:Fin (L+1)→Bool):Fin (L+1)→Bool:=
 fun k=>if h0:k.val=0 then false else p ⟨k.val-1,by omega⟩
theorem zU {L e:ℕ} (_he:e<L):
 qw (fun k:Fin (L+1)=>decide (k.val=e))=
  fun k:Fin (L+1)=>decide (k.val=e+1):=by
 funext k
 unfold qw
 by_cases h0:k.val=0
 · simp [h0]
 · simp only [h0,↓reduceDIte]
   by_cases hk:k.val=e+1
   · simp [hk]
   · simp only [hk,decide_false,decide_eq_false_iff_not]; omega
structure zh (m h:ℕ) where
 cnt:Fin (h+1)→Bool
 qs:Fin h→qc m
def qE {t m h:ℕ} (used:Fin t→Bool) (rowQ:Fin t→qc m)
    (j:ℕ) (st:zh m h):zh m h:=
 if hj:j<t then
  let j0:Fin t:=⟨j,hj⟩
  let u:=used j0
  { cnt:=fun v=>if u then qw st.cnt v else st.cnt v
    qs:=fun s=>
     if u&&st.cnt s.castSucc then rowQ j0 else st.qs s }
 else st
def vD {t m h:ℕ} (used:Fin t→Bool) (rowQ:Fin t→qc m):
    zh m h:=
 (List.range t).foldl (fun st j=>qE used rowQ j st)
   ⟨fun v=>decide (v.val=0),fun _=>qc.zero m⟩
theorem kG {t m h:ℕ} (used:Fin t→Bool) (rowQ:Fin t→qc m)
 (hvalid:∀ j,(rowQ j).Valid):
 ∀ s:Fin h,((vD used rowQ).qs s).Valid:=by
 have hloop:∀ r,∀ s:Fin h,
  (((List.range r).foldl (fun st j=>qE used rowQ j st)
    ⟨fun v=>decide (v.val=0),fun _=>qc.zero m⟩).qs s).Valid:=by
  intro r
  induction r with
  | zero=>intro _; exact qc.uK m
  | succ r ih=>
    intro s
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    unfold qE
    by_cases hr:r<t
    · simp only [hr,↓reduceDIte]
      split_ifs
      · exact hvalid ⟨r,hr⟩
      · exact ih s
    · simp only [hr,↓reduceDIte]; exact ih s
 exact hloop t
theorem ja {t m h:ℕ} (used:Fin t→Bool) (rowQ:Fin t→qc m)
 (hvalid:∀ j,(rowQ j).Valid)
 (hcnt:(Finset.univ.filter (fun j:Fin t=>used j=true)).card≤h):
 let st:zh m h:=vD used rowQ
 (∀ s:Fin h,(st.qs s).Valid)∧
 ∀ a:Fin m→ZMod 2,
   (∀ j:Fin t,used j=true→(rowQ j).eval a=0)↔
   (∀ s:Fin h,(st.qs s).eval a=0):=by
 have hloop:∀ r≤t,
  let st:zh m h:=(List.range r).foldl (fun s j=>qE used rowQ j s)
   ⟨fun v=>decide (v.val=0),fun _=>qc.zero m⟩
  let kr:=(Finset.univ.filter (fun j:Fin t=>j.val<r∧used j=true)).card
  st.cnt=(fun v:Fin (h+1)=>decide (v.val=kr))∧
  (∀ s:Fin h,kr≤ s.val→st.qs s=qc.zero m)∧
  (∀ s:Fin h,(st.qs s).Valid)∧
  (∀ a:Fin m→ZMod 2,
    (∀ j:Fin t,j.val<r→used j=true→(rowQ j).eval a=0)↔
    (∀ s:Fin h,(st.qs s).eval a=0)):=by
  intro r
  induction r with
  | zero=>
    intro _
    refine ⟨by simp,fun _ _=>rfl,fun _=>qc.uK m,fun a=>?_⟩
    constructor
    · intro _ s; exact qc.uW a
    · intro _ j hj; omega
  | succ r ih=>
    intro hr
    rcases ih (by omega) with ⟨hcnt_eq,hzero_tail,hval_prev,hequiv_prev⟩
    set st:zh m h:=(List.range r).foldl (fun s j=>qE used rowQ j s)
     ⟨fun v=>decide (v.val=0),fun _=>qc.zero m⟩
    have hst_next:(List.range (r+1)).foldl (fun s j=>qE used rowQ j s)
     ⟨fun v=>decide (v.val=0),fun _=>qc.zero m⟩=qE used rowQ r st:=by
     simp [List.range_succ,List.foldl_append,st]
    rw [hst_next]
    have hrt:r<t:=by omega
    let j0:Fin t:=⟨r,hrt⟩
    set Sr:=Finset.univ.filter (fun j:Fin t=>j.val<r∧used j=true)
    set Sr1:=Finset.univ.filter (fun j:Fin t=>j.val<r+1∧used j=true)
    have hSr1_le:Sr1.card≤h:=by
     calc
      Sr1.card≤(Finset.univ.filter (fun j:Fin t=>used j=true)).card:=by
       refine Finset.card_le_card ?_
       intro j hj
       simp only [Sr1,Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
       exact hj.2
      _≤h:=hcnt
    by_cases hu:used j0=true
    · have hSr1_eq:Sr1=insert j0 Sr:=by
       ext j
       simp only [Sr1,Sr,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
       constructor
       · rintro ⟨hlt,hju⟩
         by_cases hje:j.val=r
         · left; exact Fin.ext hje
         · right; exact ⟨by omega,hju⟩
       · rintro (rfl|⟨hlt,hju⟩)
         · exact ⟨by simp [j0],hu⟩
         · exact ⟨by omega,hju⟩
      have hj0_not:j0∉Sr:=by simp [Sr,j0]
      have hk_succ:Sr1.card=Sr.card+1:=by
       rw [hSr1_eq,Finset.card_insert_of_notMem hj0_not]
      have hk_lt:Sr.card<h:=by omega
      have hstep_cnt:(qE used rowQ r st).cnt=
       fun v:Fin (h+1)=>decide (v.val=Sr1.card):=by
       funext v
       simp only [qE,hrt,↓reduceDIte,j0,hu,↓reduceIte,hk_succ]
       rw [hcnt_eq]
       exact congrFun (zU hk_lt) v
      have hstep_qs:∀ s:Fin h,(qE used rowQ r st).qs s=
       if s.val=Sr.card then rowQ j0 else st.qs s:=by
       intro s
       simp only [qE,hrt,↓reduceDIte,j0,hu,Bool.true_and]
       rw [hcnt_eq]
       by_cases hs:s.val=Sr.card <;> simp [hs]
      refine ⟨hstep_cnt,?_,?_,?_⟩
      · intro s hs
        rw [hstep_qs s]
        have hne:s.val≠Sr.card:=by omega
        simp only [hne,↓reduceIte]
        exact hzero_tail s (by omega)
      · intro s
        rw [hstep_qs s]
        by_cases hs:s.val=Sr.card
        · simp only [hs,↓reduceIte]; exact hvalid j0
        · simp only [hs,↓reduceIte]; exact hval_prev s
      · intro a
        constructor
        · intro hall s
          rw [hstep_qs s]
          by_cases hs:s.val=Sr.card
          · simp only [hs,↓reduceIte]
            exact hall j0 (by simp [j0]) hu
          · simp only [hs,↓reduceIte]
            exact (hequiv_prev a).mp (fun j hj hju=>hall j (by omega) hju) s
        · intro hall j hj hju
          by_cases hjr:j.val=r
          · have hje:j=j0:=Fin.ext hjr
            subst hje
            have hslot:=hall ⟨Sr.card,hk_lt⟩
            rw [hstep_qs ⟨Sr.card,hk_lt⟩] at hslot
            simpa using hslot
          · refine (hequiv_prev a).mpr ?_ j (by omega) hju
            intro s
            by_cases hs:s.val=Sr.card
            · rw [hzero_tail s (by omega)]
              exact qc.uW a
            · have hslot:=hall s
              rw [hstep_qs s] at hslot
              simpa [hs] using hslot
    · have huf:used j0=false:=by cases h':used j0 <;> simp_all
      have hSr1_eq:Sr1=Sr:=by
       ext j
       simp only [Sr1,Sr,Finset.mem_filter,Finset.mem_univ,true_and]
       constructor
       · rintro ⟨hlt,hju⟩
         refine ⟨?_,hju⟩
         by_contra hge
         have hje:j=j0:=Fin.ext (by dsimp [j0]; omega)
         rw [hje,huf] at hju
         exact Bool.noConfusion hju
       · rintro ⟨hlt,hju⟩
         exact ⟨by omega,hju⟩
      have hst_eq:qE used rowQ r st=st:=by
       unfold qE
       simp only [hrt,↓reduceDIte]
       have huf':used ⟨r,hrt⟩=false:=huf
       simp [huf']
      rw [hst_eq,hSr1_eq]
      refine ⟨hcnt_eq,hzero_tail,hval_prev,fun a=>?_⟩
      rw [← hequiv_prev a]
      constructor
      · intro hall j hj hju; exact hall j (by omega) hju
      · intro hall j hj hju
        by_cases hjr:j.val=r
        · have hje:j=j0:=Fin.ext hjr
          rw [hje,huf] at hju
          exact Bool.noConfusion hju
        · exact hall j (by omega) hju
 rcases hloop t le_rfl with ⟨_,_,hval,hequiv⟩
 refine ⟨hval,fun a=>?_⟩
 dsimp only [vD]
 rw [← hequiv a]
 constructor
 · intro h j _ hu; exact h j hu
 · intro h j hu; exact h j j.isLt hu
def zG {N m h:ℕ} (st:(Fin N→Bool)→zh m h):Set (Sig N):=
 Set.range (fun v:Fin (h+1)=>fun x=>(st x).cnt v) ∪
 ⋃ s:Fin h,qn (fun x=>(st x).qs s)
theorem jM {N t m h:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (used:(Fin N→Bool)→Fin t→Bool)
 (rowQ:(Fin N→Bool)→Fin t→qc m)
 (hused:∀ j,(fun x=>used x j)∈Base)
 (hrowQ:∀ j,qn (fun x=>rowQ x j)⊆Base)
 (j:ℕ) (st:(Fin N→Bool)→zh m h):
 qa (Base ∪ zG st) (zG (fun x=>qE (used x) (rowQ x) j (st x)))
  ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4))):=by
 by_cases hj:j<t
 · let j0:Fin t:=⟨j,hj⟩
   have hcntB:qa (Base ∪ zG st)
    (Set.range (fun v:Fin (h+1)=>fun x=>(qE (used x) (rowQ x) j (st x)).cnt v))
    ((h+1) * 4):=by
    refine qf _ 4 (fun v=>?_)
    have hsh:(fun x=>qw (st x).cnt v)∈Base ∪ zG st:=by
     unfold qw
     by_cases h0:v.val=0
     · simp only [h0,↓reduceDIte]; exact Or.inl hfalse
     · simp only [h0,↓reduceDIte]; exact Or.inr (Or.inl ⟨⟨v.val-1,by omega⟩,rfl⟩)
    have heq:(fun x=>(qE (used x) (rowQ x) j (st x)).cnt v)=
     fun x=>if used x j0 then qw (st x).cnt v else (st x).cnt v:=by
     funext x; simp [qE,hj,j0]
    rw [heq]
    exact vo (Or.inl (hused j0)) hsh (Or.inr (Or.inl ⟨v,rfl⟩))
   have hqsB:qa (Base ∪ zG st)
    (⋃ s:Fin h,qn (fun x=>(qE (used x) (rowQ x) j (st x)).qs s))
    (h * (1+(m * (m * 4)+m * 4+4))):=by
    refine v7 _ (1+(m * (m * 4)+m * 4+4)) (fun s=>?_)
    let flag:Sig N:=fun x=>used x j0&&(st x).cnt s.castSucc
    have hflag:qa (Base ∪ zG st) {flag} 1:=
     qD (Or.inl (hused j0)) (Or.inr (Or.inl ⟨s.castSucc,rfl⟩))
    let A1:=(Base ∪ zG st) ∪ {flag}
    have hqB:qa A1 (qn (fun x=>(qE (used x) (rowQ x) j (st x)).qs s))
     (m * (m * 4)+m * 4+4):=by
     have hB:qa A1
      {f|∃ a b,(fun x=>z2b (((qE (used x) (rowQ x) j (st x)).qs s).B a b))=f}
      (m * (m * 4)):=
      qT _ 4 (fun a b=>by
       have heq:(fun x=>z2b (((qE (used x) (rowQ x) j (st x)).qs s).B a b))=
        fun x=>if flag x then z2b ((rowQ x j0).B a b) else z2b (((st x).qs s).B a b):=by
        funext x
        simp only [qE,hj,↓reduceDIte,j0,flag]
        cases used x j0&&(st x).cnt s.castSucc <;> simp
       rw [heq]
       exact vo (Or.inr rfl) (Or.inl (Or.inl (hrowQ j0 (Or.inl (Or.inl ⟨a,b,rfl⟩)))))
        (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inl ⟨a,b,rfl⟩)⟩)))))
     have hL:qa A1
      (Set.range (fun a:Fin m=>fun x=>z2b (((qE (used x) (rowQ x) j (st x)).qs s).l a)))
      (m * 4):=
      qf _ 4 (fun a=>by
       have heq:(fun x=>z2b (((qE (used x) (rowQ x) j (st x)).qs s).l a))=
        fun x=>if flag x then z2b ((rowQ x j0).l a) else z2b (((st x).qs s).l a):=by
        funext x
        simp only [qE,hj,↓reduceDIte,j0,flag]
        cases used x j0&&(st x).cnt s.castSucc <;> simp
       rw [heq]
       exact vo (Or.inr rfl) (Or.inl (Or.inl (hrowQ j0 (Or.inl (Or.inr ⟨a,rfl⟩)))))
        (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inr ⟨a,rfl⟩)⟩)))))
     have hC:qa A1
      {fun x=>z2b ((qE (used x) (rowQ x) j (st x)).qs s).c} 4:=by
      have heq:(fun x=>z2b ((qE (used x) (rowQ x) j (st x)).qs s).c)=
       fun x=>if flag x then z2b (rowQ x j0).c else z2b ((st x).qs s).c:=by
       funext x
       simp only [qE,hj,↓reduceDIte,j0,flag]
       cases used x j0&&(st x).cnt s.castSucc <;> simp
      rw [heq]
      exact vo (Or.inr rfl) (Or.inl (Or.inl (hrowQ j0 (Or.inr rfl))))
       (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inr rfl⟩))))
     exact qd (qr (qr hB hL) hC) le_rfl Set.subset_union_right (by omega)
    exact qe hflag hqB
   exact qr hcntB hqsB
 · have heq:(fun x=>qE (used x) (rowQ x) j (st x))=st:=by
    funext x; simp [qE,hj]
   rw [heq]
   exact qd (zk (A:=Base ∪ zG st) (B:=zG st) Set.subset_union_right)
    le_rfl Set.subset_union_right (Nat.zero_le _)
theorem jN {N t m h:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base) (htrue:(fun _=>true)∈Base)
 (used:(Fin N→Bool)→Fin t→Bool)
 (rowQ:(Fin N→Bool)→Fin t→qc m)
 (hused:∀ j,(fun x=>used x j)∈Base)
 (hrowQ:∀ j,qn (fun x=>rowQ x j)⊆Base):
 qa Base (zG (h:=h) (fun x=>vD (used x) (rowQ x)))
  (t * ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4)))):=by
 let st0:(Fin N→Bool)→zh m h:=
  fun _=>⟨fun v=>decide (v.val=0),fun _=>qc.zero m⟩
 have hst0:zG st0⊆Base:=by
  rintro f (⟨v,rfl⟩|hq)
  · by_cases hv:v.val=0
    · simpa [st0,hv] using htrue
    · simpa [st0,hv] using hfalse
  · rcases Set.mem_iUnion.mp hq with ⟨s,((⟨a,b,rfl⟩|⟨a,rfl⟩)|rfl)⟩
    · simpa [st0,qc.zero,qm] using hfalse
    · simpa [st0,qc.zero,qm] using hfalse
    · simpa [st0,qc.zero,qm] using hfalse
 have hit':∀ r,qa Base (zG (fun x=>
  (List.range r).foldl (fun s j=>qE (used x) (rowQ x) j s) (st0 x)))
  (r * ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4)))):=by
  intro r
  induction r with
  | zero=>
    simpa using zk (A:=Base) (B:=zG st0) hst0
  | succ r ih=>
    let str:(Fin N→Bool)→zh m h:=
     fun x=>(List.range r).foldl (fun s j=>qE (used x) (rowQ x) j s) (st0 x)
    have hstep:=jM Base hfalse used rowQ hused hrowQ r str
    have heq:(fun x=>(List.range (r+1)).foldl (fun s j=>qE (used x) (rowQ x) j s) (st0 x))=
     fun x=>qE (used x) (rowQ x) r (str x):=by
     funext x; simp [List.range_succ,List.foldl_append,str]
    rw [heq]
    exact qd (qe ih hstep) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])
 exact hit' t
structure z3 (t m h:ℕ) where
 affUsed:Fin t→Bool
 A:Fin t→Fin m→ZMod 2
 b:Fin t→ZMod 2
 varElim:Fin m→Bool
 qs:Fin h→qc m
def ql {t m h:ℕ} (v:ℕ) (st:z3 t m h):z3 t m h:=
 if hv:v< m then
  let i0:Fin m:=⟨v,hv⟩
  let cond:Fin t→Bool:=fun r=>!(st.affUsed r)&&z2b (st.A r i0)
  let isPiv:Fin t→Bool:=qi cond
  let found:Bool:=(List.finRange t).any isPiv
  let pivA:Fin m→ZMod 2:=fun u=>
   b2z ((List.finRange t).any (fun r=>isPiv r&&z2b (st.A r u)))
  let pivb:ZMod 2:=
   b2z ((List.finRange t).any (fun r=>isPiv r&&z2b (st.b r)))
  let e:Fin m→ZMod 2:=fun u=>if u=i0 then 0 else pivA u
  { affUsed:=fun r=>st.affUsed r||isPiv r
    A:=fun r u=>if !(isPiv r)&&z2b (st.A r i0) then st.A r u+pivA u else st.A r u
    b:=fun r=>if !(isPiv r)&&z2b (st.A r i0) then st.b r+pivb else st.b r
    varElim:=fun u=>st.varElim u||(found&&decide (u=i0))
    qs:=fun s=>
     let Qs:=st.qs s
     let f:Fin m→ZMod 2:=fun u=>if u=i0 then 0 else Qs.B i0 u
     let Qsub:=(Qs.delVar i0).addAffineProd pivb e (Qs.l i0) f
     if found then Qsub else Qs }
 else st
def yt {t m h:ℕ} (A0:Fin t→Fin m→ZMod 2) (b0:Fin t→ZMod 2)
    (qs0:Fin h→qc m):z3 t m h:=
 (List.range m).foldl (fun st v=>ql v st)
   ⟨fun _=>false,A0,b0,fun _=>false,qs0⟩
def z3.sols {t m h:ℕ} (st:z3 t m h):Finset (Fin m→ZMod 2):=
 Finset.univ.filter (fun a=>
  (∀ u:Fin m,st.varElim u=true→a u=0)∧
  (∀ r:Fin t,st.affUsed r=false→st.b r+∑ u:Fin m,st.A r u * a u=0)∧
  (∀ s:Fin h,(st.qs s).eval a=0))
theorem kg {t m h:ℕ}
 (A0:Fin t→Fin m→ZMod 2) (b0:Fin t→ZMod 2) (qs0:Fin h→qc m)
 (hqs0:∀ s:Fin h,(qs0 s).Valid):
 let st:=yt A0 b0 qs0
 let consistent:Bool:=(List.finRange t).all (fun r=>st.affUsed r||!(z2b (st.b r)))
 (∀ s:Fin h,(st.qs s).Valid)∧
 (∀ s:Fin h,∀ u:Fin m,st.varElim u=true→
   (st.qs s).l u=0∧∀ w:Fin m,(st.qs s).B u w=0)∧
 (Finset.univ.filter (fun a:Fin m→ZMod 2=>
   (∀ r:Fin t,b0 r+∑ u:Fin m,A0 r u * a u=0)∧
   (∀ s:Fin h,(qs0 s).eval a=0))).card=
 if consistent then
  (Finset.univ.filter (fun a:Fin m→ZMod 2=>
    (∀ u:Fin m,st.varElim u=true→a u=0)∧
    (∀ s:Fin h,(st.qs s).eval a=0))).card
 else 0:=by
 have hloop:∀ v≤ m,
  let st:=(List.range v).foldl (fun s k=>ql k s)
   ⟨fun _=>false,A0,b0,fun _=>false,qs0⟩
  (∀ u:Fin m,st.varElim u=true→u.val<v)∧
  (∀ r:Fin t,st.affUsed r=false→∀ u:Fin m,u.val<v→st.A r u=0)∧
  (∀ s:Fin h,(st.qs s).Valid)∧
  (∀ s:Fin h,∀ u:Fin m,st.varElim u=true→
    (st.qs s).l u=0∧∀ w:Fin m,(st.qs s).B u w=0)∧
  st.sols.card=
   (Finset.univ.filter (fun a:Fin m→ZMod 2=>
     (∀ r:Fin t,b0 r+∑ u:Fin m,A0 r u * a u=0)∧
     (∀ s:Fin h,(qs0 s).eval a=0))).card:=by
  intro v
  induction v with
  | zero=>
    intro _
    refine ⟨fun u hu=>Bool.noConfusion hu,fun _ _ _ hu=>by omega,hqs0,
     fun _ _ hu=>Bool.noConfusion hu,?_⟩
    congr 1
    ext a
    simp [z3.sols]
  | succ v ih=>
    intro hv
    rcases ih (by omega) with ⟨hve_lt,hA_zero,hq_val,hq_supp,hcard⟩
    set st:=(List.range v).foldl (fun s k=>ql k s)
     ⟨fun _=>false,A0,b0,fun _=>false,qs0⟩
    have hst_next:(List.range (v+1)).foldl (fun s k=>ql k s)
     ⟨fun _=>false,A0,b0,fun _=>false,qs0⟩=ql v st:=by
     simp [List.range_succ,List.foldl_append,st]
    rw [hst_next]
    have hvm:v< m:=by omega
    let i0:Fin m:=⟨v,hvm⟩
    let cond:Fin t→Bool:=fun r=>!(st.affUsed r)&&z2b (st.A r i0)
    let isPiv:Fin t→Bool:=qi cond
    by_cases hex:∃ r:Fin t,cond r=true
    · rcases (q0 cond).mpr hex with ⟨p0,hp0⟩
      have huniq:∀ r,isPiv r=true↔r=p0:=fun r=>
       ⟨fun h=>q2 cond h hp0,fun h=>h▸hp0⟩
      have hfound:(List.finRange t).any isPiv=true:=
       List.any_eq_true.mpr ⟨p0,List.mem_finRange p0,hp0⟩
      have hp0_cond:=((qU cond p0).mp hp0).1
      have hp0_unused:st.affUsed p0=false:=by
       simp only [cond,Bool.and_eq_true,Bool.not_eq_true'] at hp0_cond
       exact hp0_cond.1
      have hp0_one:st.A p0 i0=1:=by
       simp only [cond,Bool.and_eq_true] at hp0_cond
       have:=hp0_cond.2
       rcases qF (st.A p0 i0) with h|h
       · simp [h,qm] at this
       · exact h
      have hpivA:∀ u,b2z ((List.finRange t).any (fun r=>isPiv r&&z2b (st.A r u)))=st.A p0 u:=by
       intro u
       have hany:(List.finRange t).any (fun r=>isPiv r&&z2b (st.A r u))=z2b (st.A p0 u):=by
        cases h:z2b (st.A p0 u)
        · rw [List.any_eq_false]
          intro r _
          by_cases hr:r=p0
          · subst hr; simp [h]
          · have hf:isPiv r=false:=by
             cases h':isPiv r
             · rfl
             · exact absurd ((huniq r).mp h') hr
            simp [hf]
        · exact List.any_eq_true.mpr ⟨p0,List.mem_finRange p0,by simp [isPiv,hp0,h]⟩
       rw [hany,vr]
      have hpivb:b2z ((List.finRange t).any (fun r=>isPiv r&&z2b (st.b r)))=st.b p0:=by
       have hany:(List.finRange t).any (fun r=>isPiv r&&z2b (st.b r))=z2b (st.b p0):=by
        cases h:z2b (st.b p0)
        · rw [List.any_eq_false]
          intro r _
          by_cases hr:r=p0
          · subst hr; simp [h]
          · have hf:isPiv r=false:=by
             cases h':isPiv r
             · rfl
             · exact absurd ((huniq r).mp h') hr
            simp [hf]
        · exact List.any_eq_true.mpr ⟨p0,List.mem_finRange p0,by simp [isPiv,hp0,h]⟩
       rw [hany,vr]
      let e:Fin m→ZMod 2:=fun u=>if u=i0 then 0 else st.A p0 u
      have hst':ql v st=
       { affUsed:=fun r=>st.affUsed r||isPiv r
         A:=fun r u=>if !(isPiv r)&&z2b (st.A r i0) then st.A r u+st.A p0 u else st.A r u
         b:=fun r=>if !(isPiv r)&&z2b (st.A r i0) then st.b r+st.b p0 else st.b r
         varElim:=fun u=>st.varElim u||decide (u=i0)
         qs:=fun s=>
          let Qs:=st.qs s
          (Qs.delVar i0).addAffineProd (st.b p0) e (Qs.l i0)
            (fun u=>if u=i0 then 0 else Qs.B i0 u) }:=by
       simp only [ql,hvm,↓reduceDIte,i0,cond,isPiv,hfound,hpivA,hpivb,Bool.true_and,
        ↓reduceIte,e]
      have he_zero_elim:∀ u:Fin m,st.varElim u=true→e u=0:=by
       intro u hu
       have hult:u.val<v:=hve_lt u hu
       have hne:u≠i0:=fun h=>by rw [h] at hult; exact lt_irrefl _ hult
       simp only [e,hne,↓reduceIte]
       exact hA_zero p0 hp0_unused u hult
      have hi0_not_elim:st.varElim i0=false:=by
       cases h:st.varElim i0
       · rfl
       · have:=hve_lt i0 h; simp [i0] at this
      have hrow_upd:∀ r,r≠p0→
       (∀ u,(ql v st).A r u=st.A r u+st.A r i0 * st.A p0 u)∧
       (ql v st).b r=st.b r+st.A r i0 * st.b p0:=by
       intro r hr
       have hrf:isPiv r=false:=by
        cases h':isPiv r
        · rfl
        · exact absurd ((huniq r).mp h') hr
       rw [hst']
       rcases qF (st.A r i0) with h0|h1
       · exact ⟨fun u=>by simp [hrf,h0,qm],by simp [hrf,h0,qm]⟩
       · exact ⟨fun u=>by simp [hrf,h1,zA],by simp [hrf,h1,zA]⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · intro u hu
        rw [hst'] at hu
        simp only [Bool.or_eq_true,decide_eq_true_eq] at hu
        rcases hu with hu|rfl
        · exact Nat.lt_succ_of_lt (hve_lt u hu)
        · simp [i0]
      · intro r hr u hu
        rw [hst'] at hr
        simp only [Bool.or_eq_false_iff] at hr
        have hr_ne:r≠p0:=fun h=>by
         rw [h] at hr
         exact Bool.noConfusion (hp0.symm.trans hr.2)
        rw [(hrow_upd r hr_ne).1 u]
        by_cases huv:u.val<v
        · rw [hA_zero r hr.1 u huv,hA_zero p0 hp0_unused u huv,mul_zero,add_zero]
        · have hui:u=i0:=Fin.ext (by dsimp [i0]; omega)
          subst hui
          rw [hp0_one,mul_one,qj]
      · intro s
        rw [hst']
        exact qc.yQ (qc.ko (hq_val s) i0) _ _ _ _
      · intro s u hu
        rw [hst'] at hu ⊢
        simp only [Bool.or_eq_true,decide_eq_true_eq] at hu
        rcases hu with hu_old|rfl
        · have hult:u.val<v:=hve_lt u hu_old
          have hui:u≠i0:=fun h=>by rw [h] at hult; exact lt_irrefl _ hult
          have heu:e u=0:=he_zero_elim u hu_old
          have hBu:(st.qs s).B i0 u=0:=by
           rw [(hq_val s).2 i0 u]
           exact (hq_supp s u hu_old).2 i0
          refine ⟨?_,fun w=>?_⟩
          · simp only [qc.addAffineProd,qc.delVar,hui,↓reduceIte,
             (hq_supp s u hu_old).1,heu,hBu,mul_zero,add_zero]
          · by_cases huw:u=w
            · simp [qc.addAffineProd,huw]
            · by_cases hwi:w=i0
              · simp [qc.addAffineProd,qc.delVar,hui,hwi,e]
              · simp only [qc.addAffineProd,qc.delVar,huw,hui,hwi,or_self,↓reduceIte,
                 (hq_supp s u hu_old).2 w,heu,hBu,zero_mul,mul_zero,add_zero]
        · refine ⟨?_,fun w=>?_⟩
          · simp [qc.addAffineProd,qc.delVar,e]
          · by_cases hiw:i0=w
            · simp [qc.addAffineProd,hiw]
            · simp [qc.addAffineProd,qc.delVar,hiw,e]
      · rw [← hcard]
        have hdep_eval:∀ (s:Fin h) (a:Fin m→ZMod 2),
         a i0=st.b p0+∑ u:Fin m,e u * a u→
         ((ql v st).qs s).eval (Function.update a i0 0)=(st.qs s).eval a:=by
         intro s a hai
         have hQeq:((ql v st).qs s).eval (Function.update a i0 0)=
          ((ql v st).qs s).eval a:=by
          rw [hst']
          let Q':=((st.qs s).delVar i0).addAffineProd (st.b p0) e ((st.qs s).l i0)
           (fun u=>if u=i0 then 0 else (st.qs s).B i0 u)
          have hQ'0:Q'.l i0=0∧∀ w,Q'.B i0 w=0∧Q'.B w i0=0:=by
           refine ⟨by simp [Q',qc.addAffineProd,qc.delVar,e],fun w=>⟨?_,?_⟩⟩
           · by_cases h:i0=w <;> simp [Q',qc.addAffineProd,qc.delVar,h,e]
           · by_cases h:w=i0 <;> simp [Q',qc.addAffineProd,qc.delVar,h,e]
          change Q'.eval (Function.update a i0 0)=Q'.eval a
          unfold qc.eval
          congr 1
          · congr 1
            refine Finset.sum_congr rfl (fun u _=>?_)
            by_cases hu:u=i0
            · subst hu; simp [hQ'0.1]
            · simp [Function.update,hu]
          · refine Finset.sum_congr rfl (fun u _=>Finset.sum_congr rfl (fun w _=>?_))
            by_cases hlt:u.val<w.val
            · by_cases hu:u=i0
              · subst hu; simp [hlt,(hQ'0.2 w).1]
              · by_cases hw:w=i0
                · subst hw; simp [hlt,(hQ'0.2 u).2]
                · simp [hlt,Function.update,hu,hw]
            · simp [hlt]
         rw [hQeq,hst']
         rw [qc.v5,qc.vw (hq_val s) i0 a,hai]
        have he_sum_upd:∀ a:Fin m→ZMod 2,
         ∑ u:Fin m,e u * Function.update a i0 0 u=∑ u:Fin m,e u * a u:=by
         intro a
         refine Finset.sum_congr rfl (fun u _=>?_)
         by_cases hu:u=i0
         · subst hu; simp [e]
         · simp [Function.update,hu]
        have hp0_eq:∀ a:Fin m→ZMod 2,
         st.b p0+∑ u:Fin m,st.A p0 u * a u=0↔
         a i0=st.b p0+∑ u:Fin m,e u * a u:=by
         intro a
         have hsp:∑ u:Fin m,st.A p0 u * a u=a i0+∑ u:Fin m,e u * a u:=by
          have hterm:∀ u:Fin m,st.A p0 u * a u=
           (if u=i0 then a i0 else 0)+e u * a u:=by
           intro u
           by_cases hu:u=i0
           · subst hu; simp [e,hp0_one]
           · simp [e,hu]
          simp_rw [hterm,Finset.sum_add_distrib]
          congr 1
          simp
         rw [hsp]
         constructor
         · intro h
           have h1:a i0+(st.b p0+∑ u,e u * a u)=0:=by
            calc a i0+(st.b p0+∑ u,e u * a u)=st.b p0+(a i0+∑ u,e u * a u):=by ring
             _=0:=h
           calc
            a i0=a i0+(st.b p0+∑ u,e u * a u)+(st.b p0+∑ u,e u * a u):=by
              rw [add_assoc,qj,add_zero]
            _=st.b p0+∑ u,e u * a u:=by rw [h1,zero_add]
         · intro h
           rw [h]
           have:st.b p0+(st.b p0+∑ u,e u * a u+∑ u,e u * a u)=
            (st.b p0+st.b p0)+((∑ u,e u * a u)+(∑ u,e u * a u)):=by ring
           rw [this,qj,qj,add_zero]
        refine Finset.card_bij (fun a' _=>Function.update a' i0 (st.b p0+∑ u,e u * a' u))
         ?_ ?_ ?_
        · intro a' ha'
          rcases (Finset.mem_filter.mp ha').2 with ⟨hsupp',haff',hqs'⟩
          have ha'i0:a' i0=0:=by
           apply hsupp' i0
           rw [hst']; simp
          let a:=Function.update a' i0 (st.b p0+∑ u,e u * a' u)
          have hupd:Function.update a i0 0=a':=by
           funext u
           by_cases hu:u=i0
           · subst hu; simp [ha'i0]
           · simp [a,Function.update,hu]
          have hai:a i0=st.b p0+∑ u,e u * a u:=by
           have h1:a i0=st.b p0+∑ u,e u * a' u:=by simp [a]
           rw [h1,← hupd,he_sum_upd]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_,?_⟩
          · intro u hu
            have hui:u≠i0:=fun h=>by rw [h,hi0_not_elim] at hu; exact Bool.noConfusion hu
            simp only [Function.update,hui,↓reduceDIte]
            apply hsupp' u
            rw [hst']; simp [hu]
          · intro r hr
            by_cases hrp:r=p0
            · subst hrp; exact (hp0_eq a).mpr hai
            · have hrf:isPiv r=false:=by
               cases h':isPiv r
               · rfl
               · exact absurd ((huniq r).mp h') hrp
              have hr':(ql v st).affUsed r=false:=by
               rw [hst']; simp [hr,hrf]
              have heq':=haff' r hr'
              have hA0_i0:(ql v st).A r i0=0:=by
               rw [(hrow_upd r hrp).1 i0,hp0_one,mul_one,qj]
              have hsum_same:∑ u:Fin m,(ql v st).A r u * a' u=
               ∑ u:Fin m,(ql v st).A r u * a u:=by
               refine Finset.sum_congr rfl (fun u _=>?_)
               by_cases hu:u=i0
               · subst hu; simp [hA0_i0]
               · simp [a,hu]
              rw [hsum_same] at heq'
              have hexp:(ql v st).b r+∑ u:Fin m,(ql v st).A r u * a u=
               (st.b r+∑ u:Fin m,st.A r u * a u) +
               st.A r i0 * (st.b p0+∑ u:Fin m,st.A p0 u * a u):=by
               rw [(hrow_upd r hrp).2]
               have hterm:∀ u,(ql v st).A r u * a u=
                st.A r u * a u+st.A r i0 * (st.A p0 u * a u):=by
                intro u; rw [(hrow_upd r hrp).1 u]; ring
               simp_rw [hterm,Finset.sum_add_distrib,← Finset.mul_sum]
               ring
              rw [hexp,(hp0_eq a).mpr hai,mul_zero,add_zero] at heq'
              exact heq'
          · intro s
            rw [← hdep_eval s a hai,hupd]
            exact hqs' s
        · intro a1 ha1 a2 ha2 heq
          have h1i:a1 i0=0:=by
           apply (Finset.mem_filter.mp ha1).2.1 i0
           rw [hst']; simp
          have h2i:a2 i0=0:=by
           apply (Finset.mem_filter.mp ha2).2.1 i0
           rw [hst']; simp
          funext u
          by_cases hu:u=i0
          · subst hu; rw [h1i,h2i]
          · have:=congrFun heq u
            simpa [Function.update,hu] using this
        · intro a ha
          rcases (Finset.mem_filter.mp ha).2 with ⟨hsupp,haff,hqs⟩
          have hai:a i0=st.b p0+∑ u,e u * a u:=(hp0_eq a).mp (haff p0 hp0_unused)
          let a':=Function.update a i0 0
          refine ⟨a',?_,?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_,?_⟩
            · intro u hu
              rw [hst'] at hu
              simp only [Bool.or_eq_true,decide_eq_true_eq] at hu
              rcases hu with hu|rfl
              · by_cases hui:u=i0
                · subst hui; simp [a']
                · simp [a',hui,hsupp u hu]
              · simp [a']
            · intro r hr
              rw [hst'] at hr
              simp only [Bool.or_eq_false_iff] at hr
              have hrp:r≠p0:=fun h=>by
               rw [h] at hr
               exact Bool.noConfusion (hp0.symm.trans hr.2)
              have hA0_i0:(ql v st).A r i0=0:=by
               rw [(hrow_upd r hrp).1 i0,hp0_one,mul_one,qj]
              have hsum_same:∑ u:Fin m,(ql v st).A r u * a' u=
               ∑ u:Fin m,(ql v st).A r u * a u:=by
               refine Finset.sum_congr rfl (fun u _=>?_)
               by_cases hu:u=i0
               · subst hu; simp [hA0_i0]
               · simp [a',hu]
              rw [hsum_same,(hrow_upd r hrp).2]
              have hterm:∀ u,(ql v st).A r u * a u=
               st.A r u * a u+st.A r i0 * (st.A p0 u * a u):=by
               intro u; rw [(hrow_upd r hrp).1 u]; ring
              simp_rw [hterm,Finset.sum_add_distrib,← Finset.mul_sum]
              calc
               st.b r+st.A r i0 * st.b p0 +
                ((∑ u,st.A r u * a u)+st.A r i0 * ∑ u,st.A p0 u * a u)=
                (st.b r+∑ u,st.A r u * a u) +
                  st.A r i0 * (st.b p0+∑ u,st.A p0 u * a u):=by ring
               _=0+st.A r i0 * 0:=by rw [haff r hr.1,haff p0 hp0_unused]
               _=0:=by ring
            · intro s
              rw [hdep_eval s a hai]
              exact hqs s
          · funext u
            by_cases hu:u=i0
            · subst hu
              simp only [Function.update_self]
              rw [he_sum_upd,← hai]
            · simp [a',Function.update,hu]
    · push Not at hex
      have hallf:∀ r,cond r=false:=fun r=>by
       cases h':cond r
       · rfl
       · exact absurd h' (hex r)
      have hnoPiv:∀ r,isPiv r=false:=fun r=>by
       cases h':isPiv r
       · rfl
       · have:=((qU cond r).mp h').1
         rw [hallf r] at this; exact Bool.noConfusion this
      have hst_eq:ql v st=st:=by
       have hgen:∀ (s:z3 t m h),
        (∀ r,qi (fun r=>!(s.affUsed r)&&z2b (s.A r i0)) r=false)→
        ql v s=s:=by
        rintro ⟨u,A,b,ve,qs⟩ hnp
        have hany0:((List.finRange t).any (fun _=>false))=false:=by simp
        have hnf:(List.finRange t).any (qi (fun r=>!(u r)&&z2b (A r i0)))=false:=by
         rw [List.any_eq_false]; intro r _; simp [hnp r]
        simp only [ql,hvm,↓reduceDIte]
        change ({ affUsed:=_,A:=_,b:=_,varElim:=_,qs:=_ }:z3 t m h)=_
        congr 1
        · funext r; simp [i0,hnp r]
        · funext r w
          simp only [i0,hnp,Bool.false_and,hany0,b2z,Bool.false_eq_true,↓reduceIte,add_zero,ite_self]
        · funext r
          simp only [i0,hnp,Bool.false_and,hany0,b2z,Bool.false_eq_true,↓reduceIte,add_zero,ite_self]
        · funext w; simp [i0,hnf]
        · funext s; simp [i0,hnf]
       exact hgen st hnoPiv
      rw [hst_eq]
      refine ⟨fun u hu=>Nat.lt_succ_of_lt (hve_lt u hu),?_,hq_val,hq_supp,hcard⟩
      intro r hr u hu
      by_cases huv:u.val<v
      · exact hA_zero r hr u huv
      · have hui:u=i0:=Fin.ext (by dsimp [i0]; omega)
        subst hui
        have hcf:=hallf r
        simp only [cond,hr,Bool.not_false,Bool.true_and] at hcf
        rcases qF (st.A r i0) with h'|h'
        · exact h'
        · simp [h',zA] at hcf
 rcases hloop m le_rfl with ⟨_,hA_zero,hq_val,hq_supp,hcard⟩
 intro st consistent
 have hA_zero':∀ r:Fin t,st.affUsed r=false→∀ u:Fin m,st.A r u=0:=
  fun r hr u=>hA_zero r hr u u.isLt
 refine ⟨hq_val,hq_supp,?_⟩
 rw [← hcard]
 have hcons_iff:consistent=true↔∀ r:Fin t,st.affUsed r=false→st.b r=0:=by
  simp only [consistent,List.all_eq_true,List.mem_finRange,true_implies,Bool.or_eq_true,
   Bool.not_eq_true']
  constructor
  · intro hall r hr
    rcases hall r with h1|h2
    · rw [hr] at h1; exact Bool.noConfusion h1
    · rcases qF (st.b r) with h'|h'
      · exact h'
      · simp [h',zA] at h2
  · intro hall r
    cases hu:st.affUsed r
    · right; rw [hall r hu,qm]
    · left; rfl
 by_cases hc:consistent=true
 · simp only [hc,↓reduceIte]
   have hbr0:=hcons_iff.mp hc
   congr 1
   ext a
   simp only [z3.sols,Finset.mem_filter,Finset.mem_univ,true_and]
   constructor
   · rintro ⟨h1,_,h3⟩; exact ⟨h1,h3⟩
   · rintro ⟨h1,h3⟩
     refine ⟨h1,fun r hr=>?_,h3⟩
     change st.b r+∑ u:Fin m,st.A r u * a u=0
     have hAr:∀ u:Fin m,st.A r u=0:=hA_zero' r hr
     rw [hbr0 r hr,Finset.sum_eq_zero (fun u _=>by rw [hAr u,zero_mul]),add_zero]
 · have hcf:consistent=false:=by cases h':consistent <;> simp_all
   simp only [hcf,Bool.false_eq_true,↓reduceIte]
   rw [Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
   intro a ha
   have haff:=(Finset.mem_filter.mp ha).2.2.1
   have hnot:¬ (∀ r:Fin t,st.affUsed r=false→st.b r=0):=fun hall=>
    hc (hcons_iff.mpr hall)
   push Not at hnot
   rcases hnot with ⟨r,hr,hbr⟩
   have h1:st.b r+∑ u:Fin m,st.A r u * a u=0:=haff r hr
   have hAr:∀ u:Fin m,st.A r u=0:=hA_zero' r hr
   rw [Finset.sum_eq_zero (fun u _=>by rw [hAr u,zero_mul]),add_zero] at h1
   exact hbr h1
def zT {N t m h:ℕ} (st:(Fin N→Bool)→z3 t m h):Set (Sig N):=
 Set.range (fun r:Fin t=>fun x=>(st x).affUsed r) ∪
 {f|∃ r u,(fun x=>z2b ((st x).A r u))=f} ∪
 Set.range (fun r:Fin t=>fun x=>z2b ((st x).b r)) ∪
 Set.range (fun u:Fin m=>fun x=>(st x).varElim u) ∪
 ⋃ s:Fin h,qn (fun x=>(st x).qs s)
theorem jU {N t m h:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (v:ℕ) (st:(Fin N→Bool)→z3 t m h):
 qa (Base ∪ zT st) (zT (fun x=>ql v (st x)))
  (t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
    h * (m * (m * 14)+m * 19+9)):=by
 by_cases hv:v< m
 · let i0:Fin m:=⟨v,hv⟩
   let cond:Fin t→Sig N:=fun r x=>!((st x).affUsed r)&&z2b ((st x).A r i0)
   let isPiv:Fin t→Sig N:=fun r x=>qi (fun j=>cond j x) r
   let found:Sig N:=fun x=>(List.finRange t).any (fun r=>isPiv r x)
   let pivA:Fin m→Sig N:=fun u x=>(List.finRange t).any (fun r=>isPiv r x&&z2b ((st x).A r u))
   let pivb:Sig N:=fun x=>(List.finRange t).any (fun r=>isPiv r x&&z2b ((st x).b r))
   have hcondB:qa (Base ∪ zT st) (Set.range cond) (t * 2):=by
    refine qf cond 2 (fun r=>?_)
    have h1:qa (Base ∪ zT st) {fun x=>!((st x).affUsed r)} 1:=
     zn (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r,rfl⟩)))))
    have h2:qa ((Base ∪ zT st) ∪ {fun x=>!((st x).affUsed r)}) {cond r} 1:=
     qD (Or.inr rfl) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r,i0,rfl⟩))))))
    exact qe h1 h2
   have hftB:qa ((Base ∪ zT st) ∪ Set.range cond) (Set.range isPiv) (t * (t+2)):=
    yE cond (Or.inl (Or.inl hfalse)) (fun r=>Or.inr ⟨r,rfl⟩)
   let A1:=(Base ∪ zT st) ∪ (Set.range cond ∪ Set.range isPiv)
   have h1:qa (Base ∪ zT st) (Set.range cond ∪ Set.range isPiv) (t * 2+t * (t+2)):=
    zd hcondB hftB
   have hfoundB:qa A1 {found} t:=by
    have h:=vt (A:=A1) ((List.finRange t).map isPiv)
     (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr (Or.inr ⟨r,rfl⟩))
     (Or.inl (Or.inl hfalse))
    have heq:(fun x=>((List.finRange t).map isPiv).any (fun f=>f x))=found:=by
     funext x; simp [found,List.any_map]; rfl
    rw [heq,List.length_map,List.length_finRange] at h
    exact h
   have hpivAB:qa A1 (Set.range pivA) (m * (2 * t)):=by
    refine qf pivA (2 * t) (fun u=>?_)
    let term:Fin t→Sig N:=fun r x=>isPiv r x&&z2b ((st x).A r u)
    have ht:qa A1 (Set.range term) (t * 1):=
     qf term 1 (fun r=>
      qD (Or.inr (Or.inr ⟨r,rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r,u,rfl⟩)))))))
    have hor:qa (A1 ∪ Set.range term) {pivA u} t:=by
     have h:=vt (A:=A1 ∪ Set.range term) ((List.finRange t).map term)
      (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr ⟨r,rfl⟩)
      (Or.inl (Or.inl (Or.inl hfalse)))
     have heq:(fun x=>((List.finRange t).map term).any (fun f=>f x))=pivA u:=by
      funext x; simp [pivA,term,List.any_map]; rfl
     rw [heq,List.length_map,List.length_finRange] at h
     exact h
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
   have hpivbB:qa A1 {pivb} (2 * t):=by
    let term:Fin t→Sig N:=fun r x=>isPiv r x&&z2b ((st x).b r)
    have ht:qa A1 (Set.range term) (t * 1):=
     qf term 1 (fun r=>
      qD (Or.inr (Or.inr ⟨r,rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨r,rfl⟩))))))
    have hor:qa (A1 ∪ Set.range term) {pivb} t:=by
     have h:=vt (A:=A1 ∪ Set.range term) ((List.finRange t).map term)
      (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr ⟨r,rfl⟩)
      (Or.inl (Or.inl (Or.inl hfalse)))
     have heq:(fun x=>((List.finRange t).map term).any (fun f=>f x))=pivb:=by
      funext x; simp [pivb,term,List.any_map]; rfl
     rw [heq,List.length_map,List.length_finRange] at h
     exact h
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
   have h2:qa A1 (({found} ∪ Set.range pivA) ∪ {pivb}) (t+m * (2 * t)+2 * t):=
    qr (qr hfoundB hpivAB) hpivbB
   let A2:=A1 ∪ (({found} ∪ Set.range pivA) ∪ {pivb})
   have hFA2:(fun _=>false)∈A2:=Or.inl (Or.inl (Or.inl hfalse))
   have husedB:qa A2 (Set.range (fun r:Fin t=>fun x=>(ql v (st x)).affUsed r)) (t * 1):=
    qf _ 1 (fun r=>by
     have heq:(fun x=>(ql v (st x)).affUsed r)=fun x=>(st x).affUsed r||isPiv r x:=by
      funext x; simp [ql,hv,i0,cond,isPiv]
     rw [heq]
     exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r,rfl⟩)))))))
      (Or.inl (Or.inr (Or.inr ⟨r,rfl⟩))))
   have hAB:qa A2 {f|∃ r u,(fun x=>z2b ((ql v (st x)).A r u))=f} (t * (m * 10)):=
    qT _ 10 (fun r u=>by
     let np:Sig N:=fun x=>!(isPiv r x)
     let flag:Sig N:=fun x=>np x&&z2b ((st x).A r i0)
     let xored:Sig N:=fun x=>xor (z2b ((st x).A r u)) (pivA u x)
     let out:Sig N:=fun x=>if flag x then xored x else z2b ((st x).A r u)
     have hb1:qa A2 {np} 1:=zn (Or.inl (Or.inr (Or.inr ⟨r,rfl⟩)))
     have hb2:qa (A2 ∪ {np}) {flag} 1:=
      qD (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r,i0,rfl⟩))))))))
     have hb3:qa ((A2 ∪ {np}) ∪ {flag}) {xored} 4:=
      yW (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r,u,rfl⟩)))))))))
       (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))))
     have hb4:qa (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4:=
      vo (Or.inl (Or.inr rfl)) (Or.inr rfl)
       (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r,u,rfl⟩))))))))))
     have heq:out=fun x=>z2b ((ql v (st x)).A r u):=by
      funext x
      simp only [out,flag,np,xored,ql,hv,↓reduceDIte,i0,cond,isPiv,pivA]
      cases hf:(!(qi (fun j=>!((st x).affUsed j)&&z2b ((st x).A j i0)) r)&&
       z2b ((st x).A r i0)) <;> simp [vW,z0]
     rw [← heq]
     exact qd (qo (qo (qo (qP hb1) (qP hb2)) (qP hb3)) hb4)
      le_rfl Set.subset_union_right (by omega))
   have hbB:qa A2 (Set.range (fun r:Fin t=>fun x=>z2b ((ql v (st x)).b r))) (t * 10):=
    qf _ 10 (fun r=>by
     let np:Sig N:=fun x=>!(isPiv r x)
     let flag:Sig N:=fun x=>np x&&z2b ((st x).A r i0)
     let xored:Sig N:=fun x=>xor (z2b ((st x).b r)) (pivb x)
     let out:Sig N:=fun x=>if flag x then xored x else z2b ((st x).b r)
     have hb1:qa A2 {np} 1:=zn (Or.inl (Or.inr (Or.inr ⟨r,rfl⟩)))
     have hb2:qa (A2 ∪ {np}) {flag} 1:=
      qD (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r,i0,rfl⟩))))))))
     have hb3:qa ((A2 ∪ {np}) ∪ {flag}) {xored} 4:=
      yW (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨r,rfl⟩))))))))
       (Or.inl (Or.inl (Or.inr (Or.inr rfl))))
     have hb4:qa (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4:=
      vo (Or.inl (Or.inr rfl)) (Or.inr rfl)
       (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨r,rfl⟩)))))))))
     have heq:out=fun x=>z2b ((ql v (st x)).b r):=by
      funext x
      simp only [out,flag,np,xored,ql,hv,↓reduceDIte,i0,cond,isPiv,pivb]
      cases hf:(!(qi (fun j=>!((st x).affUsed j)&&z2b ((st x).A j i0)) r)&&
       z2b ((st x).A r i0)) <;> simp [vW,z0]
     rw [← heq]
     exact qd (qo (qo (qo (qP hb1) (qP hb2)) (qP hb3)) hb4)
      le_rfl Set.subset_union_right (by omega))
   have hveB:qa A2 (Set.range (fun u:Fin m=>fun x=>(ql v (st x)).varElim u)) (m * 1):=
    qf _ 1 (fun u=>by
     by_cases hu:u=i0
     · have heq:(fun x=>(ql v (st x)).varElim u)=fun x=>(st x).varElim u||found x:=by
        funext x; simp [ql,hv,i0,hu,cond,isPiv,found]
       rw [heq]
       exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))))
        (Or.inr (Or.inl (Or.inl rfl)))
     · have heq:(fun x=>(ql v (st x)).varElim u)=fun x=>(st x).varElim u:=by
        funext x; simp [ql,hv,i0,hu]
       rw [heq]
       exact qd (zk (A:=A2) (B:={fun x=>(st x).varElim u})
        (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))))))
        le_rfl Set.subset_union_right (by omega))
   have hqsB:qa A2 (⋃ s:Fin h,qn (fun x=>(ql v (st x)).qs s))
    (h * (m * (m * 14)+m * 19+9)):=by
    refine v7 _ (m * (m * 14)+m * 19+9) (fun s=>?_)
    let Qdel:(Fin N→Bool)→qc m:=fun x=>((st x).qs s).delVar i0
    let eZ:(Fin N→Bool)→Fin m→ZMod 2:=fun x u=>if u=i0 then 0 else b2z (pivA u x)
    let fZ:(Fin N→Bool)→Fin m→ZMod 2:=fun x u=>if u=i0 then 0 else ((st x).qs s).B i0 u
    let Qsub:(Fin N→Bool)→qc m:=
     fun x=>(Qdel x).addAffineProd (b2z (pivb x)) (eZ x) (((st x).qs s).l i0) (fZ x)
    have hQdel_in:qn Qdel⊆A2:=by
     rintro g ((⟨a,b,rfl⟩|⟨a,rfl⟩)|rfl)
     · by_cases h1:a=i0∨b=i0
       · have:(fun x=>z2b ((Qdel x).B a b))=fun _=>false:=by
          funext x; simp [Qdel,qc.delVar,h1,qm]
         rw [this]; exact hFA2
       · have:(fun x=>z2b ((Qdel x).B a b))=fun x=>z2b (((st x).qs s).B a b):=by
          funext x; simp [Qdel,qc.delVar,h1]
         rw [this]; exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inl ⟨a,b,rfl⟩)⟩))))
     · dsimp only
       by_cases h1:a=i0
       · have:(fun x=>z2b ((Qdel x).l a))=fun _=>false:=by
          funext x; simp [Qdel,qc.delVar,h1,qm]
         rw [this]; exact hFA2
       · have:(fun x=>z2b ((Qdel x).l a))=fun x=>z2b (((st x).qs s).l a):=by
          funext x; simp [Qdel,qc.delVar,h1]
         rw [this]; exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inr ⟨a,rfl⟩)⟩))))
     · exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inr rfl⟩))))
    have hpivb_in:(fun x=>z2b (b2z (pivb x)))∈A2:=by
     have:(fun x=>z2b (b2z (pivb x)))=pivb:=funext (fun x=>z0 (pivb x))
     rw [this]; exact Or.inr (Or.inr rfl)
    have hsubB:qa A2 (qn Qsub) (m * (m * 10)+m * 15+5):=
     kz A2 hFA2 Qdel (fun x=>b2z (pivb x))
      (fun x=>((st x).qs s).l i0) eZ fZ hQdel_in
      hpivb_in
      (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inr ⟨i0,rfl⟩)⟩)))))
      (fun u=>by
        by_cases hu:u=i0
        · have:(fun x=>z2b (eZ x u))=fun _=>false:=by funext x; simp [eZ,hu,qm]
          rw [this]; exact hFA2
        · have:(fun x=>z2b (eZ x u))=pivA u:=by funext x; simp [eZ,hu,z0]
          rw [this]; exact Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))
      (fun u=>by
        by_cases hu:u=i0
        · have:(fun x=>z2b (fZ x u))=fun _=>false:=by funext x; simp [fZ,hu,qm]
          rw [this]; exact hFA2
        · have:(fun x=>z2b (fZ x u))=fun x=>z2b (((st x).qs s).B i0 u):=by
           funext x; simp [fZ,hu]
          rw [this]; exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inl ⟨i0,u,rfl⟩)⟩)))))
    have hmuxB:qa (A2 ∪ qn Qsub)
     (qn (fun x=>(ql v (st x)).qs s)) (m * (m * 4)+m * 4+4):=by
     have hB:qa (A2 ∪ qn Qsub)
      {f|∃ a b,(fun x=>z2b (((ql v (st x)).qs s).B a b))=f} (m * (m * 4)):=
      qT _ 4 (fun a b=>by
       have heq:(fun x=>z2b (((ql v (st x)).qs s).B a b))=
        fun x=>if found x then z2b ((Qsub x).B a b) else z2b (((st x).qs s).B a b):=by
        funext x
        simp only [ql,hv,↓reduceDIte,i0,cond,isPiv,found,Qsub,Qdel,eZ,fZ,pivA,pivb]
        cases (List.finRange t).any (qi (fun r=>!((st x).affUsed r)&&z2b ((st x).A r i0))) <;>
         simp
       rw [heq]
       exact vo (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inr (Or.inl (Or.inl ⟨a,b,rfl⟩)))
        (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inl ⟨a,b,rfl⟩)⟩)))))))
     have hL:qa (A2 ∪ qn Qsub)
      (Set.range (fun a:Fin m=>fun x=>z2b (((ql v (st x)).qs s).l a))) (m * 4):=
      qf _ 4 (fun a=>by
       have heq:(fun x=>z2b (((ql v (st x)).qs s).l a))=
        fun x=>if found x then z2b ((Qsub x).l a) else z2b (((st x).qs s).l a):=by
        funext x
        simp only [ql,hv,↓reduceDIte,i0,cond,isPiv,found,Qsub,Qdel,eZ,fZ,pivA,pivb]
        cases (List.finRange t).any (qi (fun r=>!((st x).affUsed r)&&z2b ((st x).A r i0))) <;>
         simp
       rw [heq]
       exact vo (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inr (Or.inl (Or.inr ⟨a,rfl⟩)))
        (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inl (Or.inr ⟨a,rfl⟩)⟩)))))))
     have hC:qa (A2 ∪ qn Qsub)
      {fun x=>z2b ((ql v (st x)).qs s).c} 4:=by
      have heq:(fun x=>z2b ((ql v (st x)).qs s).c)=
       fun x=>if found x then z2b (Qsub x).c else z2b ((st x).qs s).c:=by
       funext x
       simp only [ql,hv,↓reduceDIte,i0,cond,isPiv,found,Qsub,Qdel,eZ,fZ,pivA,pivb]
       cases (List.finRange t).any (qi (fun r=>!((st x).affUsed r)&&z2b ((st x).A r i0))) <;>
        simp
      rw [heq]
      exact vo (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inr (Or.inr rfl))
       (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s,Or.inr rfl⟩))))))
     exact qd (qr (qr hB hL) hC) le_rfl Set.subset_union_right (by omega)
    exact qd (qe hsubB hmuxB) le_rfl Set.subset_union_right (by ring_nf; omega)
   have h3:=qr (qr (qr (qr husedB hAB) hbB) hveB) hqsB
   exact qd (qo (qo (qP h1) (qP h2)) h3) le_rfl Set.subset_union_right (by ring_nf; omega)
 · have heq:(fun x=>ql v (st x))=st:=by
    funext x; simp [ql,hv]
   rw [heq]
   exact qd (zk (A:=Base ∪ zT st) (B:=zT st) Set.subset_union_right)
    le_rfl Set.subset_union_right (Nat.zero_le _)
theorem jT {N t m h:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (A0:(Fin N→Bool)→Fin t→Fin m→ZMod 2)
 (b0:(Fin N→Bool)→Fin t→ZMod 2)
 (qs0:(Fin N→Bool)→Fin h→qc m)
 (hA0:∀ r u,(fun x=>z2b (A0 x r u))∈Base)
 (hb0:∀ r,(fun x=>z2b (b0 x r))∈Base)
 (hqs0:∀ s,qn (fun x=>qs0 x s)⊆Base):
 qa Base (zT (fun x=>yt (A0 x) (b0 x) (qs0 x)))
  (m * (t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
    h * (m * (m * 14)+m * 19+9))):=by
 let st0:(Fin N→Bool)→z3 t m h:=
  fun x=>⟨fun _=>false,A0 x,b0 x,fun _=>false,qs0 x⟩
 have hst0:zT st0⊆Base:=by
  rintro f ((((⟨r,rfl⟩|⟨r,u,rfl⟩)|⟨r,rfl⟩)|⟨u,rfl⟩)|hq)
  · exact hfalse
  · exact hA0 r u
  · exact hb0 r
  · exact hfalse
  · rcases Set.mem_iUnion.mp hq with ⟨s,hs⟩
    exact hqs0 s hs
 have hit:=jD (Sigs:=zT) (step:=ql)
  (c:=t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
    h * (m * (m * 14)+m * 19+9))
  (Base:=Base) (fun v st=>jU Base hfalse v st) m st0
 exact qd hit (Set.union_subset le_rfl hst0) Set.subset_union_right le_rfl
def qz (x:ZMod 2):ℤ:=if x=0 then 1 else -1
theorem yZ (x y:ZMod 2):qz (x+y)=qz x * qz y:=by
 fin_cases x <;> fin_cases y <;> decide
theorem jo (A B:ZMod 2):
 ∑ x:ZMod 2,∑ y:ZMod 2,qz (x * y+x * A+y * B)=2 * qz (A * B):=by
 fin_cases A <;> fin_cases B <;> decide
theorem uG (l:ZMod 2):
 ∑ x:ZMod 2,qz (l * x)=if l=0 then 2 else 0:=by
 fin_cases l <;> decide
theorem kB:∀ (h:ℕ) (v:Fin h→ZMod 2),
 ∑ σ:Fin h→ZMod 2,qz (∑ s:Fin h,σ s * v s)=
   if (∀ s:Fin h,v s=0) then (2:ℤ) ^ h else 0:=by
 intro h
 induction h with
 | zero=>
   intro v
   simp [qz]
 | succ h ih=>
   intro v
   let e:(ZMod 2×(Fin h→ZMod 2)) ≃ (Fin (h+1)→ZMod 2):=Fin.consEquiv (fun _=>ZMod 2)
   rw [← Fintype.sum_equiv e (fun p=>qz (∑ s:Fin (h+1),e p s * v s))
    (fun σ=>qz (∑ s:Fin (h+1),σ s * v s)) (fun _=>rfl)]
   rw [Fintype.sum_prod_type]
   have hsplit:∀ (a:ZMod 2) (τ:Fin h→ZMod 2),
    qz (∑ s:Fin (h+1),e (a,τ) s * v s)=
     qz (v 0 * a) * qz (∑ s:Fin h,τ s * v s.succ):=by
    intro a τ
    rw [Fin.sum_univ_succ,← yZ]
    congr 1
    simp only [e,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]
    ring
   simp_rw [hsplit,← Finset.mul_sum,← Finset.sum_mul,uG,ih (fun s=>v s.succ)]
   by_cases hall:∀ s:Fin (h+1),v s=0
   · have h0:v 0=0:=hall 0
     have hsucc:∀ s:Fin h,v s.succ=0:=fun s=>hall s.succ
     rw [ite_eq_left_of_eq_true _ _ (eq_true hall),ite_eq_left_of_eq_true _ _ (eq_true h0),
      ite_eq_left_of_eq_true _ _ (eq_true hsucc),pow_succ]
     ring
   · simp only [hall,↓reduceIte]
     by_cases h0:v 0=0
     · have hns:¬ ∀ s:Fin h,v s.succ=0:=fun hs=>hall (Fin.cases h0 hs)
       simp [h0,hns]
     · simp [h0]
def zQ {L:ℕ} (p:Fin (L+1)→Bool):ℕ:=
 ∑ k:Fin (L+1),if p k then 2 ^ k.val else 0
theorem vk {L e:ℕ} (he:e≤L):
 zQ (fun k:Fin (L+1)=>decide (k.val=e))=2 ^ e:=by
 unfold zQ
 rw [Finset.sum_eq_single ⟨e,by omega⟩]
 · simp
 · intro k _ hk
   have hne:k.val≠e:=fun h=>hk (Fin.ext h)
   simp [hne]
 · intro h; exact absurd (Finset.mem_univ _) h
theorem vH {L e j:ℕ} (he:e≤L):
 (zQ (fun k:Fin (L+1)=>decide (k.val=e))).testBit j=
   if j<L+1 then decide (j=e) else false:=by
 rw [vk he,Nat.testBit_two_pow]
 by_cases hj:j<L+1
 · simp only [hj,↓reduceIte]
   by_cases hje:e=j <;> simp [hje,eq_comm]
 · simp only [hj,↓reduceIte]
   have hne:e≠j:=by omega
   simp [hne]
structure zL (m:ℕ) where
 active:Fin m→Bool
 Q:qc m
 zero:Bool
 pow2:Fin (m+1)→Bool
def qM {m:ℕ} (i:ℕ) (st:zL m):zL m:=
 if hi:i< m then
  let i0:Fin m:=⟨i,hi⟩
  let cond:Fin m→Bool:=fun j=>st.active j&&z2b (st.Q.B i0 j)
  let isPiv:Fin m→Bool:=qi cond
  let found:Bool:=(List.finRange m).any isPiv
  let actIso:Fin m→Bool:=fun u=>if u=i0 then false else st.active u
  let actPair:Fin m→Bool:=fun u=>if u=i0||isPiv u then false else st.active u
  let b0:ZMod 2:=b2z ((List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.l j)))
  let bv:Fin m→ZMod 2:=fun u=>
   if actPair u then b2z ((List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.B j u))) else 0
  let av:Fin m→ZMod 2:=fun u=>if actPair u then st.Q.B i0 u else 0
  let QdelPair:qc m:=
   { B:=fun u v=>if actPair u&&actPair v then st.Q.B u v else 0
     l:=fun u=>if actPair u then st.Q.l u else 0
     c:=st.Q.c }
  let Qpair:qc m:=QdelPair.addAffineProd (st.Q.l i0) av b0 bv
  let Qiso:qc m:=st.Q.delVar i0
  if st.active i0 then
   if found then
    { active:=actPair
      Q:=Qpair
      zero:=st.zero
      pow2:=qw st.pow2 }
   else
    { active:=actIso
      Q:=Qiso
      zero:=st.zero||z2b (st.Q.l i0)
      pow2:=if z2b (st.Q.l i0) then st.pow2 else qw st.pow2 }
  else st
 else st
def qK {m:ℕ} (free:Fin m→Bool) (Q0:qc m):zL m:=
 (List.range m).foldl (fun st i=>qM i st)
   ⟨free,Q0,false,fun k=>decide (k.val=0)⟩
def z4 {m:ℕ} (act:Fin m→Bool):Finset (Fin m→ZMod 2):=
 Finset.univ.filter (fun a=>∀ u:Fin m,act u=false→a u=0)
theorem jd {m:ℕ} (act:Fin m→Bool) (Q:qc m)
 (hsupp:∀ u,act u=false→Q.l u=0∧∀ w,Q.B u w=0∧Q.B w u=0)
 (a b:Fin m→ZMod 2) (hab:∀ u,act u=true→a u=b u):
 Q.eval a=Q.eval b:=by
 unfold qc.eval
 congr 1
 · congr 1
   refine Finset.sum_congr rfl (fun u _=>?_)
   cases hu:act u
   · simp [(hsupp u hu).1]
   · rw [hab u hu]
 · refine Finset.sum_congr rfl (fun u _=>Finset.sum_congr rfl (fun v _=>?_))
   by_cases hlt:u.val<v.val
   · simp only [hlt,↓reduceIte]
     cases hu:act u
     · simp [(hsupp u hu).2 v |>.1]
     · cases hv:act v
       · simp [(hsupp v hv).2 u |>.2]
       · rw [hab u hu,hab v hv]
   · simp [hlt]
theorem kU {m:ℕ} (act:Fin m→Bool) (Q:qc m)
 (hQval:Q.Valid)
 (hQsupp:∀ u:Fin m,act u=false→Q.l u=0∧∀ w:Fin m,Q.B u w=0)
 (i0 j0:Fin m) (hij_ne:i0≠j0) (hj0_B1:Q.B i0 j0=1)
 (a':Fin m→ZMod 2) (xi xj:ZMod 2):
 let act':Fin m→Bool:=fun u=>if u=i0∨u=j0 then false else act u
 let av:Fin m→ZMod 2:=fun u=>if act' u then Q.B i0 u else 0
 let bv:Fin m→ZMod 2:=fun u=>if act' u then Q.B j0 u else 0
 let Qdel:qc m:=
  { B:=fun u v=>if act' u&&act' v then Q.B u v else 0
    l:=fun u=>if act' u then Q.l u else 0
    c:=Q.c }
 Q.eval (Function.update (Function.update a' j0 xj) i0 xi)=
  Qdel.eval a'+(xi * xj+xi * (Q.l i0+∑ u:Fin m,av u * a' u) +
   xj * (Q.l j0+∑ u:Fin m,bv u * a' u)):=by
 intro act' av bv Qdel
 let w:=Function.update (Function.update a' j0 xj) i0 xi
 have h1:=qc.vw hQval i0 w
 have hdel1_val:(Q.delVar i0).Valid:=qc.ko hQval i0
 have h2:=qc.vw hdel1_val j0 w
 have hwi:w i0=xi:=by simp [w]
 have hwj:w j0=xj:=by simp [w,Function.update,Ne.symm hij_ne]
 have hdel2_eq:((Q.delVar i0).delVar j0).eval w=Qdel.eval a':=by
  unfold qc.eval qc.delVar Qdel
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun u _=>?_)
    by_cases hu1:u=i0
    · subst hu1; simp [act']
    · by_cases hu2:u=j0
      · subst hu2; simp [act']
      · cases ha:act u
        · simp [act',hu1,hu2,ha,(hQsupp u ha).1]
        · simp [act',hu1,hu2,ha,w]
  · refine Finset.sum_congr rfl (fun u _=>Finset.sum_congr rfl (fun v _=>?_))
    by_cases hlt:u.val<v.val
    · simp only [hlt,↓reduceIte]
      by_cases hu1:u=i0
      · subst hu1; simp [act']
      · by_cases hu2:u=j0
        · subst hu2; simp [act']
        · by_cases hv1:v=i0
          · subst hv1; simp [act']
          · by_cases hv2:v=j0
            · subst hv2; simp [act']
            · cases hau:act u
              · simp [act',hu1,hu2,hv1,hv2,hau,(hQsupp u hau).2 v]
              · cases hav:act v
                · have hBv:=(hQsupp v hav).2 u
                  rw [hQval.2 v u] at hBv
                  simp [act',hu1,hu2,hv1,hv2,hau,hav,hBv]
                · simp [act',hu1,hu2,hv1,hv2,hau,hav,w]
    · simp [hlt]
 have hsumA:(∑ u:Fin m,(if u=i0 then 0 else Q.B i0 u) * w u)=
  xj+∑ u:Fin m,av u * a' u:=by
  have hsp:∀ u:Fin m,
   (if u=i0 then 0 else Q.B i0 u) * w u=
   (if u=j0 then xj else 0)+av u * a' u:=by
   intro u
   by_cases hu1:u=i0
   · subst hu1; simp [act',av,hij_ne]
   · by_cases hu2:u=j0
     · subst hu2; simp [act',av,hwj,hj0_B1,Ne.symm hij_ne]
     · cases ha:act u
       · have h0:=(hQsupp u ha).2 i0
         rw [hQval.2 u i0] at h0
         simp [act',av,hu1,hu2,ha,h0]
       · simp [act',av,hu1,hu2,ha,w]
  rw [Finset.sum_congr rfl (fun u _=>hsp u),Finset.sum_add_distrib]
  congr 1
  simp
 have hsumB:(Q.delVar i0).l j0 +
  (∑ u:Fin m,(if u=j0 then 0 else (Q.delVar i0).B j0 u) * w u)=
  Q.l j0+∑ u:Fin m,bv u * a' u:=by
  simp only [qc.delVar,Ne.symm hij_ne,↓reduceIte]
  congr 1
  refine Finset.sum_congr rfl (fun u _=>?_)
  by_cases hu1:u=i0
  · subst hu1; simp [act',bv]
  · by_cases hu2:u=j0
    · subst hu2; simp [act',bv]
    · cases ha:act u
      · have h0:=(hQsupp u ha).2 j0
        rw [hQval.2 u j0] at h0
        simp [act',bv,hu1,hu2,ha,h0]
      · simp [act',bv,hu1,hu2,ha,w]
 rw [h1,h2,hdel2_eq,hwi,hwj,hsumA,hsumB]
 ring
theorem jq {m:ℕ} (r:ℕ) (hrm:r< m) (st:zL m)
 (hact_ge:∀ u:Fin m,st.active u=true→ r≤u.val)
 (hQval:st.Q.Valid)
 (hQsupp:∀ u:Fin m,st.active u=false→st.Q.l u=0∧∀ w:Fin m,st.Q.B u w=0)
 (e:ℕ)
 (he_bound:e+(Finset.univ.filter (fun u:Fin m=>st.active u=true)).card≤ m)
 (hpow_eq:st.pow2=fun k:Fin (m+1)=>decide (k.val=e)):
 let st':=qM r st
 (∀ u:Fin m,st'.active u=true→ r+1≤u.val)∧
 st'.Q.Valid∧
 (∀ u:Fin m,st'.active u=false→st'.Q.l u=0∧∀ w:Fin m,st'.Q.B u w=0)∧
 (∃ e':ℕ,e'+(Finset.univ.filter (fun u:Fin m=>st'.active u=true)).card≤ m∧
   st'.pow2=fun k:Fin (m+1)=>decide (k.val=e'))∧
 (if st'.zero then (0:ℤ) else
   (zQ st'.pow2:ℤ) * ∑ a∈z4 st'.active,qz (st'.Q.eval a))=
 (if st.zero then (0:ℤ) else
   (zQ st.pow2:ℤ) * ∑ a∈z4 st.active,qz (st.Q.eval a)):=by
 let i0:Fin m:=⟨r,hrm⟩
 by_cases hi0:st.active i0=true
 · have hi0_in:i0∈Finset.univ.filter (fun u:Fin m=>st.active u=true):=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi0⟩
   have hact_pos:1≤(Finset.univ.filter (fun u:Fin m=>st.active u=true)).card:=
    Finset.card_pos.mpr ⟨i0,hi0_in⟩
   have he_lt:e< m:=by omega
   let cond:Fin m→Bool:=fun j=>st.active j&&z2b (st.Q.B i0 j)
   let isPiv:Fin m→Bool:=qi cond
   by_cases hex:∃ j:Fin m,cond j=true
   · rcases (q0 cond).mpr hex with ⟨j0,hj0⟩
     have huniq:∀ j,isPiv j=true↔j=j0:=fun j=>
      ⟨fun h=>q2 cond h hj0,fun h=>h▸hj0⟩
     have hfound:(List.finRange m).any isPiv=true:=
      List.any_eq_true.mpr ⟨j0,List.mem_finRange j0,hj0⟩
     have hj0_cond:=((qU cond j0).mp hj0).1
     simp only [cond,Bool.and_eq_true] at hj0_cond
     have hj0_act:st.active j0=true:=hj0_cond.1
     have hj0_B1:st.Q.B i0 j0=1:=by
      have:=hj0_cond.2
      rcases qF (st.Q.B i0 j0) with h|h
      · simp [h,qm] at this
      · exact h
     have hij_ne:i0≠j0:=fun h=>by
      rw [h,hQval.1 j0] at hj0_B1
      exact zero_ne_one hj0_B1
     have hb0:b2z ((List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.l j)))=st.Q.l j0:=by
      have hany:(List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.l j))=z2b (st.Q.l j0):=by
       cases h:z2b (st.Q.l j0)
       · rw [List.any_eq_false]
         intro j _
         by_cases hj:j=j0
         · subst hj; simp [h]
         · have hf:isPiv j=false:=by
            cases h':isPiv j
            · rfl
            · exact absurd ((huniq j).mp h') hj
           simp [hf]
       · exact List.any_eq_true.mpr ⟨j0,List.mem_finRange j0,by simp [isPiv,hj0,h]⟩
      rw [hany,vr]
     have hbv_raw:∀ u,b2z ((List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.B j u)))=st.Q.B j0 u:=by
      intro u
      have hany:(List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.B j u))=z2b (st.Q.B j0 u):=by
       cases h:z2b (st.Q.B j0 u)
       · rw [List.any_eq_false]
         intro j _
         by_cases hj:j=j0
         · subst hj; simp [h]
         · have hf:isPiv j=false:=by
            cases h':isPiv j
            · rfl
            · exact absurd ((huniq j).mp h') hj
           simp [hf]
       · exact List.any_eq_true.mpr ⟨j0,List.mem_finRange j0,by simp [isPiv,hj0,h]⟩
      rw [hany,vr]
     let act':Fin m→Bool:=fun u=>if u=i0∨u=j0 then false else st.active u
     have hact'_eq:(fun u=>if u=i0||isPiv u then false else st.active u)=act':=by
      funext u
      by_cases hu1:u=i0
      · simp [act',hu1]
      · by_cases hu2:u=j0
        · subst hu2; simp [act',isPiv,hj0]
        · have hf:isPiv u=false:=by
           cases h':isPiv u
           · rfl
           · exact absurd ((huniq u).mp h') hu2
          simp [act',hu1,hu2,hf]
     let av:Fin m→ZMod 2:=fun u=>if act' u then st.Q.B i0 u else 0
     let bv:Fin m→ZMod 2:=fun u=>if act' u then st.Q.B j0 u else 0
     let Qdel:qc m:=
      { B:=fun u v=>if act' u&&act' v then st.Q.B u v else 0
        l:=fun u=>if act' u then st.Q.l u else 0
        c:=st.Q.c }
     let Q':qc m:=Qdel.addAffineProd (st.Q.l i0) av (st.Q.l j0) bv
     have hact'_pt:∀ u,(if u=i0||isPiv u then false else st.active u)=act' u:=
      fun u=>congrFun hact'_eq u
     have hst':qM r st=⟨act',Q',st.zero,qw st.pow2⟩:=by
      unfold qM
      simp only [hrm,↓reduceDIte]
      change (if st.active i0 then if (List.finRange m).any isPiv then
       ({ active:=fun u=>if u=i0||isPiv u then false else st.active u
          Q:=({ B:=fun u v=>if (if u=i0||isPiv u then false else st.active u)&&
                 (if v=i0||isPiv v then false else st.active v) then st.Q.B u v else 0
                l:=fun u=>if (if u=i0||isPiv u then false else st.active u) then st.Q.l u else 0
                c:=st.Q.c }:qc m).addAffineProd (st.Q.l i0)
              (fun u=>if (if u=i0||isPiv u then false else st.active u) then st.Q.B i0 u else 0)
              (b2z ((List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.l j))))
              (fun u=>if (if u=i0||isPiv u then false else st.active u) then
                b2z ((List.finRange m).any (fun j=>isPiv j&&z2b (st.Q.B j u))) else 0)
          zero:=st.zero
          pow2:=qw st.pow2 }:zL m)
       else _ else _)=_
      simp only [hi0,hfound,↓reduceIte,hact'_pt,hb0,hbv_raw]
      rfl
     dsimp only
     rw [hst']
     dsimp only
     have hQdel_val:Qdel.Valid:=by
      refine ⟨fun u=>by dsimp only [Qdel]; split_ifs; exact hQval.1 u; rfl,fun u v=>?_⟩
      dsimp only [Qdel]
      rw [Bool.and_comm,hQval.2 u v]
     have hact'_card:(Finset.univ.filter (fun u:Fin m=>act' u=true)).card+2=
      (Finset.univ.filter (fun u:Fin m=>st.active u=true)).card:=by
      have hset:Finset.univ.filter (fun u:Fin m=>st.active u=true)=
       insert i0 (insert j0 (Finset.univ.filter (fun u:Fin m=>act' u=true))):=by
       ext u
       simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,act']
       by_cases hu1:u=i0
       · subst hu1; simp [hi0]
       · by_cases hu2:u=j0
         · subst hu2; simp [hj0_act]
         · simp [hu1,hu2]
      have hi_not:i0∉insert j0 (Finset.univ.filter (fun u:Fin m=>act' u=true)):=by
       simp [hij_ne,act']
      have hj_not:j0∉Finset.univ.filter (fun u:Fin m=>act' u=true):=by
       simp [act']
      rw [hset,Finset.card_insert_of_notMem hi_not,Finset.card_insert_of_notMem hj_not]
     refine ⟨?_,qc.yQ hQdel_val _ _ _ _,?_,?_,?_⟩
     · intro u hu
       have hne:u≠i0:=fun h=>by subst h; simp [act'] at hu
       have hu_old:st.active u=true:=by
        simp only [act'] at hu
        by_cases h1:u=i0∨u=j0
        · simp [h1] at hu
        · simp [h1] at hu; exact hu
       have hge:=hact_ge u hu_old
       have hval_ne:u.val≠r:=fun h=>hne (Fin.ext h)
       omega
     · intro u hu
       refine ⟨?_,fun w=>?_⟩
       · simp [Q',qc.addAffineProd,Qdel,av,bv,hu]
       · by_cases huw:u=w
         · simp [Q',qc.addAffineProd,huw]
         · simp [Q',qc.addAffineProd,Qdel,av,bv,hu,huw]
     · refine ⟨e+1,by omega,?_⟩
       rw [hpow_eq]
       exact zU he_lt
     · by_cases hz:st.zero=true
       · simp [hz]
       · have hzf:st.zero=false:=by cases h':st.zero <;> simp_all
         simp only [hzf,Bool.false_eq_true,↓reduceIte]
         rw [hpow_eq,zU he_lt,vk (by omega:e+1≤ m),
          vk (by omega:e≤ m)]
         have hsplit_sum:
          ∑ a∈z4 st.active,qz (st.Q.eval a)=
          2 * ∑ a'∈z4 act',qz (Q'.eval a'):=by
          have hbij:
           ∑ a∈z4 st.active,qz (st.Q.eval a)=
           ∑ a'∈z4 act',∑ xi:ZMod 2,∑ xj:ZMod 2,
             qz (st.Q.eval (Function.update (Function.update a' j0 xj) i0 xi)):=by
           have hprod:=Finset.sum_product' (z4 act') (Finset.univ:Finset (ZMod 2×ZMod 2))
            (fun a' p=>qz (st.Q.eval (Function.update (Function.update a' j0 p.2) i0 p.1)))
           have hinner:∀ a'∈z4 act',
            ∑ xi:ZMod 2,∑ xj:ZMod 2,
              qz (st.Q.eval (Function.update (Function.update a' j0 xj) i0 xi))=
            ∑ p:ZMod 2×ZMod 2,
              qz (st.Q.eval (Function.update (Function.update a' j0 p.2) i0 p.1)):=
            fun a' _=>(Fintype.sum_prod_type
             (fun p:ZMod 2×ZMod 2=>qz (st.Q.eval (Function.update (Function.update a' j0 p.2) i0 p.1)))).symm
           rw [Finset.sum_congr rfl hinner,← hprod]
           symm
           refine Finset.sum_bij
            (fun p _=>Function.update (Function.update p.1 j0 p.2.2) i0 p.2.1)
            ?_ ?_ ?_ ?_
           · rintro ⟨a',xi,xj⟩ hp
             have ha':=(Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
             refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun u hu=>?_⟩
             have hu1:u≠i0:=fun h=>by rw [h,hi0] at hu; exact Bool.noConfusion hu
             have hu2:u≠j0:=fun h=>by rw [h,hj0_act] at hu; exact Bool.noConfusion hu
             simp only [Function.update,hu1,hu2,↓reduceDIte]
             apply ha' u
             simp [act',hu1,hu2,hu]
           · rintro ⟨a1,x1,y1⟩ hp1 ⟨a2,x2,y2⟩ hp2 heq
             have ha1:∀ u,act' u=false→a1 u=0:=(Finset.mem_filter.mp (Finset.mem_product.mp hp1).1).2
             have ha2:∀ u,act' u=false→a2 u=0:=(Finset.mem_filter.mp (Finset.mem_product.mp hp2).1).2
             have hx:x1=x2:=by
              have:=congrFun heq i0; simpa using this
             have hy:y1=y2:=by
              have:=congrFun heq j0; simpa [Ne.symm hij_ne] using this
             have ha:a1=a2:=by
              funext u
              by_cases hu1:u=i0
              · rw [hu1,ha1 i0 (by simp [act']),ha2 i0 (by simp [act'])]
              · by_cases hu2:u=j0
                · rw [hu2,ha1 j0 (by simp [act']),ha2 j0 (by simp [act'])]
                · have:=congrFun heq u; simpa [Function.update,hu1,hu2] using this
             rw [ha,hx,hy]
           · intro a ha
             have haS:=(Finset.mem_filter.mp ha).2
             let a':=Function.update (Function.update a j0 0) i0 0
             refine ⟨(a',(a i0,a j0)),?_,?_⟩
             · refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
               refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun u hu=>?_⟩
               by_cases hu1:u=i0
               · subst hu1; simp [a']
               · by_cases hu2:u=j0
                 · subst hu2; simp [a',Ne.symm hij_ne]
                 · have huf:st.active u=false:=by simpa [act',hu1,hu2] using hu
                   simp [a',Function.update,hu1,hu2,haS u huf]
             · funext u
               by_cases hu1:u=i0
               · subst hu1; simp
               · by_cases hu2:u=j0
                 · subst hu2; simp [Function.update,Ne.symm hij_ne]
                 · simp [a',Function.update,hu1,hu2]
           · intro _ _; rfl
          rw [hbij,Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a' _=>?_)
          let A_val:ZMod 2:=st.Q.l i0+∑ u:Fin m,av u * a' u
          let B_val:ZMod 2:=st.Q.l j0+∑ u:Fin m,bv u * a' u
          have heval_step:∀ xi xj:ZMod 2,
           st.Q.eval (Function.update (Function.update a' j0 xj) i0 xi)=
           Qdel.eval a'+(xi * xj+xi * A_val+xj * B_val):=
           fun xi xj=>kU st.active st.Q hQval hQsupp i0 j0 hij_ne hj0_B1 a' xi xj
          have hQ'_eval:Q'.eval a'=Qdel.eval a'+A_val * B_val:=
           qc.v5 Qdel (st.Q.l i0) av (st.Q.l j0) bv a'
          simp_rw [heval_step]
          simp_rw [yZ (Qdel.eval a'),← Finset.mul_sum]
          rw [jo,hQ'_eval,yZ]
          ring
         rw [hsplit_sum,pow_succ]
         push_cast
         ring
   · push Not at hex
     have hallf:∀ j,cond j=false:=fun j=>by
      cases h':cond j
      · rfl
      · exact absurd h' (hex j)
     have hnoPiv:∀ j,isPiv j=false:=fun j=>by
      cases h':isPiv j
      · rfl
      · have:=((qU cond j).mp h').1
        rw [hallf j] at this; exact Bool.noConfusion this
     have hfound:(List.finRange m).any isPiv=false:=by
      rw [List.any_eq_false]; intro j _; simp [hnoPiv j]
     let act':Fin m→Bool:=fun u=>if u=i0 then false else st.active u
     have hst':qM r st=
      ⟨act',st.Q.delVar i0,st.zero||z2b (st.Q.l i0),
        if z2b (st.Q.l i0) then st.pow2 else qw st.pow2⟩:=by
      unfold qM
      simp only [hrm,↓reduceDIte]
      change (if st.active i0 then if (List.finRange m).any isPiv then _ else
       ({ active:=act'
          Q:=st.Q.delVar i0
          zero:=st.zero||z2b (st.Q.l i0)
          pow2:=if z2b (st.Q.l i0) then st.pow2 else qw st.pow2 }:zL m) else _)=_
      simp only [hi0,hfound,Bool.false_eq_true,↓reduceIte]
     dsimp only
     rw [hst']
     dsimp only
     have hB_i0_zero:∀ u:Fin m,st.Q.B i0 u=0:=by
      intro u
      cases hu:st.active u
      · have h0:=(hQsupp u hu).2 i0
        rwa [hQval.2 u i0] at h0
      · have hcf:=hallf u
        simp only [cond,hu,Bool.true_and] at hcf
        rcases qF (st.Q.B i0 u) with h'|h'
        · exact h'
        · simp [h',zA] at hcf
     have hact'_card:(Finset.univ.filter (fun u:Fin m=>act' u=true)).card+1=
      (Finset.univ.filter (fun u:Fin m=>st.active u=true)).card:=by
      have hset:Finset.univ.filter (fun u:Fin m=>st.active u=true)=
       insert i0 (Finset.univ.filter (fun u:Fin m=>act' u=true)):=by
       ext u
       simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,act']
       by_cases hu:u=i0
       · subst hu; simp [hi0]
       · simp [hu]
      have hi_not:i0∉Finset.univ.filter (fun u:Fin m=>act' u=true):=by simp [act']
      rw [hset,Finset.card_insert_of_notMem hi_not]
     refine ⟨?_,qc.ko hQval i0,?_,?_,?_⟩
     · intro u hu
       have hne:u≠i0:=fun h=>by subst h; simp [act'] at hu
       have hu_old:st.active u=true:=by simpa [act',hne] using hu
       have hge:=hact_ge u hu_old
       have hval_ne:u.val≠r:=fun h=>hne (Fin.ext h)
       omega
     · intro u hu
       by_cases hui:u=i0
       · subst hui; simp [qc.delVar]
       · have huf:st.active u=false:=by simpa [act',hui] using hu
         refine ⟨by simp [qc.delVar,hui,(hQsupp u huf).1],fun w=>?_⟩
         by_cases hwi:w=i0
         · simp [qc.delVar,hwi]
         · simp [qc.delVar,hui,hwi,(hQsupp u huf).2 w]
     · by_cases hl:z2b (st.Q.l i0)=true
       · refine ⟨e,by omega,by simp [hl,hpow_eq]⟩
       · have hlf:z2b (st.Q.l i0)=false:=by cases h':z2b (st.Q.l i0) <;> simp_all
         refine ⟨e+1,by omega,?_⟩
         simp only [hlf,Bool.false_eq_true,↓reduceIte,hpow_eq]
         exact zU he_lt
     · have hsplit_iso:
        ∑ a∈z4 st.active,qz (st.Q.eval a)=
        (if st.Q.l i0=0 then 2 else 0) * ∑ a'∈z4 act',qz ((st.Q.delVar i0).eval a'):=by
        have hbij:
         ∑ a∈z4 st.active,qz (st.Q.eval a)=
         ∑ a'∈z4 act',∑ xi:ZMod 2,
           qz (st.Q.eval (Function.update a' i0 xi)):=by
         rw [← Finset.sum_product']
         symm
         refine Finset.sum_bij (fun p _=>Function.update p.1 i0 p.2) ?_ ?_ ?_ ?_
         · rintro ⟨a',xi⟩ hp
           have ha':=(Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
           refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun u hu=>?_⟩
           have hu1:u≠i0:=fun h=>by rw [h,hi0] at hu; exact Bool.noConfusion hu
           simp only [Function.update,hu1,↓reduceDIte]
           exact ha' u (by simp [act',hu1,hu])
         · rintro ⟨a1,x1⟩ hp1 ⟨a2,x2⟩ hp2 heq
           have ha1:∀ u,act' u=false→a1 u=0:=(Finset.mem_filter.mp (Finset.mem_product.mp hp1).1).2
           have ha2:∀ u,act' u=false→a2 u=0:=(Finset.mem_filter.mp (Finset.mem_product.mp hp2).1).2
           have hx:x1=x2:=by have:=congrFun heq i0; simpa using this
           have ha:a1=a2:=by
            funext u
            by_cases hu:u=i0
            · rw [hu,ha1 i0 (by simp [act']),ha2 i0 (by simp [act'])]
            · have:=congrFun heq u; simpa [Function.update,hu] using this
           rw [ha,hx]
         · intro a ha
           have haS:=(Finset.mem_filter.mp ha).2
           refine ⟨(Function.update a i0 0,a i0),?_,?_⟩
           · refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
             refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun u hu=>?_⟩
             by_cases hu1:u=i0
             · subst hu1; simp
             · have huf:st.active u=false:=by simpa [act',hu1] using hu
               simp [Function.update,hu1,haS u huf]
           · funext u
             by_cases hu1:u=i0
             · subst hu1; simp
             · simp [Function.update,hu1]
         · intro _ _; rfl
        rw [hbij,Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a' _=>?_)
        have heval:∀ xi:ZMod 2,
         st.Q.eval (Function.update a' i0 xi)=(st.Q.delVar i0).eval a'+st.Q.l i0 * xi:=by
         intro xi
         rw [qc.vw hQval i0 (Function.update a' i0 xi)]
         have hB0:∑ u:Fin m,(if u=i0 then 0 else st.Q.B i0 u) *
          Function.update a' i0 xi u=0:=by
          refine Finset.sum_eq_zero (fun u _=>by simp [hB_i0_zero u])
         have hdel:(st.Q.delVar i0).eval (Function.update a' i0 xi)=(st.Q.delVar i0).eval a':=by
          unfold qc.eval qc.delVar
          congr 1
          · congr 1
            refine Finset.sum_congr rfl (fun u _=>?_)
            by_cases hu:u=i0 <;> simp [Function.update,hu]
          · refine Finset.sum_congr rfl (fun u _=>Finset.sum_congr rfl (fun v _=>?_))
            by_cases hlt:u.val<v.val
            · by_cases hu:u=i0
              · subst hu; simp [hlt]
              · by_cases hv:v=i0
                · subst hv; simp [hlt]
                · simp [hlt,Function.update,hu,hv]
            · simp [hlt]
         rw [hdel,hB0,add_zero,Function.update_self,mul_comm]
        simp_rw [heval,yZ,← Finset.mul_sum,uG]
        ring
       by_cases hz:st.zero=true
       · simp [hz]
       · have hzf:st.zero=false:=by cases h':st.zero <;> simp_all
         rcases qF (st.Q.l i0) with hl|hl
         · simp only [hzf,hl,qm,Bool.or_false,Bool.false_eq_true,↓reduceIte,
            hsplit_iso,hpow_eq,zU he_lt,vk (by omega:e+1≤ m),
            vk (by omega:e≤ m),pow_succ]
           push_cast
           ring
         · simp only [hzf,hl,zA,Bool.or_true,Bool.false_eq_true,↓reduceIte,hsplit_iso,
            one_ne_zero,zero_mul,mul_zero]
 · have hi0f:st.active i0=false:=by cases h':st.active i0 <;> simp_all
   have hst':qM r st=st:=by simp [qM,hrm,i0,hi0f]
   dsimp only
   rw [hst']
   refine ⟨?_,hQval,hQsupp,⟨e,he_bound,hpow_eq⟩,rfl⟩
   intro u hu
   have hge:=hact_ge u hu
   have hne:u.val≠r:=fun h=>by
    have:u=i0:=Fin.ext h
    rw [this,hi0f] at hu; exact Bool.noConfusion hu
   omega
theorem vG {m:ℕ} (free:Fin m→Bool) (Q0:qc m)
 (hval0:Q0.Valid)
 (hsupp0:∀ u:Fin m,free u=false→Q0.l u=0∧∀ w:Fin m,Q0.B u w=0):
 let st:=qK free Q0
 (∃ e≤ m,st.pow2=fun k:Fin (m+1)=>decide (k.val=e))∧
 (if st.zero then (0:ℤ) else (zQ st.pow2:ℤ) * qz st.Q.c)=
   ∑ a∈z4 free,qz (Q0.eval a):=by
 have hloop:∀ r≤ m,
  let st:=(List.range r).foldl (fun s i=>qM i s)
   ⟨free,Q0,false,fun k=>decide (k.val=0)⟩
  (∀ u:Fin m,st.active u=true→ r≤u.val)∧
  st.Q.Valid∧
  (∀ u:Fin m,st.active u=false→st.Q.l u=0∧∀ w:Fin m,st.Q.B u w=0)∧
  (∃ e:ℕ,e+(Finset.univ.filter (fun u:Fin m=>st.active u=true)).card≤ m∧
    st.pow2=fun k:Fin (m+1)=>decide (k.val=e))∧
  (if st.zero then (0:ℤ) else
    (zQ st.pow2:ℤ) * ∑ a∈z4 st.active,qz (st.Q.eval a))=
  ∑ a∈z4 free,qz (Q0.eval a):=by
  intro r
  induction r with
  | zero=>
    intro _
    refine ⟨fun _ _=>Nat.zero_le _,hval0,hsupp0,
     ⟨0,by rw [zero_add]; exact (Finset.card_le_univ _).trans (by simp),rfl⟩,?_⟩
    change (if false then (0:ℤ) else (zQ (fun k:Fin (m+1)=>decide (k.val=0)):ℤ) *
     ∑ a∈z4 free,qz (Q0.eval a))=_
    simp only [Bool.false_eq_true,↓reduceIte,vk (L:=m) (Nat.zero_le m),pow_zero,
     Nat.cast_one,one_mul]
  | succ r ih=>
    intro hr
    rcases ih (by omega) with ⟨hact_ge,hQval,hQsupp,⟨e,he_bound,hpow_eq⟩,hsum_eq⟩
    set st:=(List.range r).foldl (fun s i=>qM i s)
     ⟨free,Q0,false,fun k=>decide (k.val=0)⟩
    have hst_next:(List.range (r+1)).foldl (fun s i=>qM i s)
     ⟨free,Q0,false,fun k=>decide (k.val=0)⟩=qM r st:=by
     simp [List.range_succ,List.foldl_append,st]
    dsimp only
    rw [hst_next]
    rcases jq r (by omega) st hact_ge hQval hQsupp e he_bound hpow_eq with
     ⟨h1,h2,h3,h4,h5⟩
    exact ⟨h1,h2,h3,h4,h5.trans hsum_eq⟩
 rcases hloop m le_rfl with ⟨hact_ge,_,_,⟨e,he_bound,hpow_eq⟩,hsum_eq⟩
 intro st
 have hsum_eq':(if st.zero then (0:ℤ) else
  (zQ st.pow2:ℤ) * ∑ a∈z4 st.active,qz (st.Q.eval a))=
  ∑ a∈z4 free,qz (Q0.eval a):=hsum_eq
 have hall_false:∀ u:Fin m,st.active u=false:=fun u=>by
  cases h':st.active u
  · rfl
  · have:=hact_ge u h'; omega
 have hsupp_sing:z4 st.active={0}:=by
  ext a
  simp only [z4,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · intro h; funext u; exact h u (hall_false u)
  · rintro rfl u _; rfl
 have heval0:st.Q.eval 0=st.Q.c:=by simp [qc.eval]
 refine ⟨⟨e,by omega,hpow_eq⟩,?_⟩
 rw [← hsum_eq',hsupp_sing,Finset.sum_singleton,heval0]
def vd {N m:ℕ} (st:(Fin N→Bool)→zL m):Set (Sig N):=
 Set.range (fun u:Fin m=>fun x=>(st x).active u) ∪
 qn (fun x=>(st x).Q) ∪
 {fun x=>(st x).zero} ∪
 Set.range (fun k:Fin (m+1)=>fun x=>(st x).pow2 k)
theorem jX {N m:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (i:ℕ) (st:(Fin N→Bool)→zL m):
 qa (Base ∪ vd st) (vd (fun x=>qM i (st x)))
  (m * (m+7)+(m+1) * (2 * m)+(m * (m * 26)+m * 60+40)):=by
 by_cases hi:i< m
 · let i0:Fin m:=⟨i,hi⟩
   let cond:Fin m→Sig N:=fun j x=>(st x).active j&&z2b ((st x).Q.B i0 j)
   let isPiv:Fin m→Sig N:=fun j x=>qi (fun u=>cond u x) j
   let found:Sig N:=fun x=>(List.finRange m).any (fun j=>isPiv j x)
   let actIso:Fin m→Sig N:=fun u x=>if u=i0 then false else (st x).active u
   let actPair:Fin m→Sig N:=fun u x=>if u=i0||isPiv u x then false else (st x).active u
   let b0:Sig N:=fun x=>(List.finRange m).any (fun j=>isPiv j x&&z2b ((st x).Q.l j))
   let bvRaw:Fin m→Sig N:=fun u x=>(List.finRange m).any (fun j=>isPiv j x&&z2b ((st x).Q.B j u))
   have hcondB:qa (Base ∪ vd st) (Set.range cond) (m * 1):=
    qf cond 1 (fun j=>
     qD (Or.inr (Or.inl (Or.inl (Or.inl ⟨j,rfl⟩))))
      (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨i0,j,rfl⟩)))))))
   have hftB:qa ((Base ∪ vd st) ∪ Set.range cond) (Set.range isPiv) (m * (m+2)):=
    yE cond (Or.inl (Or.inl hfalse)) (fun j=>Or.inr ⟨j,rfl⟩)
   let A1:=(Base ∪ vd st) ∪ (Set.range cond ∪ Set.range isPiv)
   have h1:qa (Base ∪ vd st) (Set.range cond ∪ Set.range isPiv) (m * 1+m * (m+2)):=
    zd hcondB hftB
   have hfoundB:qa A1 {found} m:=by
    have h:=vt (A:=A1) ((List.finRange m).map isPiv)
     (fun f hf=>by rcases List.mem_map.mp hf with ⟨j,_,rfl⟩; exact Or.inr (Or.inr ⟨j,rfl⟩))
     (Or.inl (Or.inl hfalse))
    have heq:(fun x=>((List.finRange m).map isPiv).any (fun f=>f x))=found:=by
     funext x; simp [found,List.any_map]; rfl
    rw [heq,List.length_map,List.length_finRange] at h
    exact h
   have hactPairB:qa A1 (Set.range actPair) (m * 2):=by
    refine qf actPair 2 (fun u=>?_)
    by_cases hu:u=i0
    · have heq:actPair u=fun _=>false:=by funext x; simp [actPair,hu]
      rw [heq]
      exact qd (zk (A:=A1) (B:={fun _=>false})
       (Set.singleton_subset_iff.mpr (Or.inl (Or.inl hfalse))))
       le_rfl Set.subset_union_right (by omega)
    · have heq:actPair u=fun x=>!(isPiv u x)&&(st x).active u:=by
       funext x; simp only [actPair,hu,decide_false,Bool.false_or]
       cases isPiv u x <;> rfl
      rw [heq]
      have hn:qa A1 {fun x=>!(isPiv u x)} 1:=zn (Or.inr (Or.inr ⟨u,rfl⟩))
      have ha:qa (A1 ∪ {fun x=>!(isPiv u x)}) {fun x=>!(isPiv u x)&&(st x).active u} 1:=
       qD (Or.inr rfl) (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨u,rfl⟩))))))
      exact qe hn ha
   have hb0B:qa A1 {b0} (2 * m):=by
    let term:Fin m→Sig N:=fun j x=>isPiv j x&&z2b ((st x).Q.l j)
    have ht:qa A1 (Set.range term) (m * 1):=
     qf term 1 (fun j=>
      qD (Or.inr (Or.inr ⟨j,rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨j,rfl⟩))))))))
    have hor:qa (A1 ∪ Set.range term) {b0} m:=by
     have h:=vt (A:=A1 ∪ Set.range term) ((List.finRange m).map term)
      (fun f hf=>by rcases List.mem_map.mp hf with ⟨j,_,rfl⟩; exact Or.inr ⟨j,rfl⟩)
      (Or.inl (Or.inl (Or.inl hfalse)))
     have heq:(fun x=>((List.finRange m).map term).any (fun f=>f x))=b0:=by
      funext x; simp [b0,term,List.any_map]; rfl
     rw [heq,List.length_map,List.length_finRange] at h
     exact h
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
   have hbvRawB:qa A1 (Set.range bvRaw) (m * (2 * m)):=by
    refine qf bvRaw (2 * m) (fun u=>?_)
    let term:Fin m→Sig N:=fun j x=>isPiv j x&&z2b ((st x).Q.B j u)
    have ht:qa A1 (Set.range term) (m * 1):=
     qf term 1 (fun j=>
      qD (Or.inr (Or.inr ⟨j,rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨j,u,rfl⟩))))))))
    have hor:qa (A1 ∪ Set.range term) {bvRaw u} m:=by
     have h:=vt (A:=A1 ∪ Set.range term) ((List.finRange m).map term)
      (fun f hf=>by rcases List.mem_map.mp hf with ⟨j,_,rfl⟩; exact Or.inr ⟨j,rfl⟩)
      (Or.inl (Or.inl (Or.inl hfalse)))
     have heq:(fun x=>((List.finRange m).map term).any (fun f=>f x))=bvRaw u:=by
      funext x; simp [bvRaw,term,List.any_map]; rfl
     rw [heq,List.length_map,List.length_finRange] at h
     exact h
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
   let B2:=(({found} ∪ Set.range actPair) ∪ {b0}) ∪ Set.range bvRaw
   have h2:qa A1 B2 (m+m * 2+2 * m+m * (2 * m)):=
    qr (qr (qr hfoundB hactPairB) hb0B) hbvRawB
   let A2:=A1 ∪ B2
   let avZ:(Fin N→Bool)→Fin m→ZMod 2:=fun x u=>if actPair u x then (st x).Q.B i0 u else 0
   let bvZ:(Fin N→Bool)→Fin m→ZMod 2:=fun x u=>if actPair u x then b2z (bvRaw u x) else 0
   let QdelPair:(Fin N→Bool)→qc m:=fun x=>
    { B:=fun u v=>if actPair u x&&actPair v x then (st x).Q.B u v else 0
      l:=fun u=>if actPair u x then (st x).Q.l u else 0
      c:=(st x).Q.c }
   let Qpair:(Fin N→Bool)→qc m:=
    fun x=>(QdelPair x).addAffineProd ((st x).Q.l i0) (avZ x) (b2z (b0 x)) (bvZ x)
   have hprepB:qa A2
    (Set.range (fun u:Fin m=>fun x=>z2b (avZ x u)) ∪
     Set.range (fun u:Fin m=>fun x=>z2b (bvZ x u)) ∪
     qn QdelPair)
    (m * 1+m * 1+(m * (m * 2)+m * 1)):=by
    have havB:qa A2 (Set.range (fun u:Fin m=>fun x=>z2b (avZ x u))) (m * 1):=
     qf _ 1 (fun u=>by
      have heq:(fun x=>z2b (avZ x u))=fun x=>actPair u x&&z2b ((st x).Q.B i0 u):=by
       funext x; cases h:actPair u x <;> simp [avZ,h,qm]
      rw [heq]
      exact qD (Or.inr (Or.inl (Or.inl (Or.inr ⟨u,rfl⟩))))
       (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨i0,u,rfl⟩)))))))))
    have hbvB:qa A2 (Set.range (fun u:Fin m=>fun x=>z2b (bvZ x u))) (m * 1):=
     qf _ 1 (fun u=>by
      have heq:(fun x=>z2b (bvZ x u))=fun x=>actPair u x&&bvRaw u x:=by
       funext x; cases h:actPair u x <;> simp [bvZ,h,qm,z0]
      rw [heq]
      exact qD (Or.inr (Or.inl (Or.inl (Or.inr ⟨u,rfl⟩)))) (Or.inr (Or.inr ⟨u,rfl⟩)))
    have hQdelB:qa A2 (qn QdelPair) (m * (m * 2)+m * 1):=by
     have hB:qa A2 {f|∃ u v,(fun x=>z2b ((QdelPair x).B u v))=f} (m * (m * 2)):=
      qT _ 2 (fun u v=>by
       let t1:Sig N:=fun x=>actPair u x&&actPair v x
       let out:Sig N:=fun x=>t1 x&&z2b ((st x).Q.B u v)
       have ht1:qa A2 {t1} 1:=
        qD (Or.inr (Or.inl (Or.inl (Or.inr ⟨u,rfl⟩)))) (Or.inr (Or.inl (Or.inl (Or.inr ⟨v,rfl⟩))))
       have hout:qa (A2 ∪ {t1}) {out} 1:=
        qD (Or.inr rfl)
         (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨u,v,rfl⟩)))))))))
       have heq:out=fun x=>z2b ((QdelPair x).B u v):=by
        funext x; simp only [out,t1,QdelPair]
        cases actPair u x&&actPair v x <;> simp [qm]
       rw [← heq]
       exact qe ht1 hout)
     have hL:qa A2 (Set.range (fun u:Fin m=>fun x=>z2b ((QdelPair x).l u))) (m * 1):=
      qf _ 1 (fun u=>by
       have heq:(fun x=>z2b ((QdelPair x).l u))=fun x=>actPair u x&&z2b ((st x).Q.l u):=by
        funext x; cases h:actPair u x <;> simp [QdelPair,h,qm]
       rw [heq]
       exact qD (Or.inr (Or.inl (Or.inl (Or.inr ⟨u,rfl⟩))))
        (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))))))))
     have hC:qa A2 {fun x=>z2b (QdelPair x).c} 0:=
      zk (Set.singleton_subset_iff.mpr
       (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))))
     exact qd (qr (qr hB hL) hC) le_rfl Set.subset_union_right (by omega)
    exact qr (qr havB hbvB) hQdelB
   let A3:=A2 ∪ (Set.range (fun u:Fin m=>fun x=>z2b (avZ x u)) ∪
    Set.range (fun u:Fin m=>fun x=>z2b (bvZ x u)) ∪ qn QdelPair)
   have hb0_in:(fun x=>z2b (b2z (b0 x)))∈A3:=by
    have:(fun x=>z2b (b2z (b0 x)))=b0:=funext (fun x=>z0 (b0 x))
    rw [this]; exact Or.inl (Or.inr (Or.inl (Or.inr rfl)))
   have hQpairB:qa A3 (qn Qpair) (m * (m * 10)+m * 15+5):=
    kz A3 (Or.inl (Or.inl (Or.inl (Or.inl hfalse)))) QdelPair
     (fun x=>(st x).Q.l i0) (fun x=>b2z (b0 x)) avZ bvZ
     (Set.subset_union_right.trans (by intro f hf; exact Or.inr hf))
     (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i0,rfl⟩)))))))))
     hb0_in
     (fun u=>Or.inr (Or.inl (Or.inl ⟨u,rfl⟩)))
     (fun u=>Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))
   let A4:=A3 ∪ qn Qpair
   have hactIso_in:∀ u,actIso u∈A4:=fun u=>by
    by_cases hu:u=i0
    · have:actIso u=fun _=>false:=by funext x; simp [actIso,hu]
      rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
    · have:actIso u=fun x=>(st x).active u:=by funext x; simp [actIso,hu]
      rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨u,rfl⟩)))))))
   have hQiso_in:qn (fun x=>(st x).Q.delVar i0)⊆A4:=by
    rintro g ((⟨u,v,rfl⟩|⟨u,rfl⟩)|rfl)
    · by_cases h1:u=i0∨v=i0
      · have:(fun x=>z2b (((st x).Q.delVar i0).B u v))=fun _=>false:=by
         funext x; simp [qc.delVar,h1,qm]
        rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
      · have:(fun x=>z2b (((st x).Q.delVar i0).B u v))=fun x=>z2b ((st x).Q.B u v):=by
         funext x; simp [qc.delVar,h1]
        rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨u,v,rfl⟩)))))))))
    · dsimp only
      by_cases h1:u=i0
      · have:(fun x=>z2b (((st x).Q.delVar i0).l u))=fun _=>false:=by
         funext x; simp [qc.delVar,h1,qm]
        rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
      · have:(fun x=>z2b (((st x).Q.delVar i0).l u))=fun x=>z2b ((st x).Q.l u):=by
         funext x; simp [qc.delVar,h1]
        rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))))
   have hsh_in:∀ k:Fin (m+1),(fun x=>qw (st x).pow2 k)∈A4:=fun k=>by
    unfold qw
    by_cases h0:k.val=0
    · simp only [h0,↓reduceDIte]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
    · simp only [h0,↓reduceDIte]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨⟨k.val-1,by omega⟩,rfl⟩)))))
   have hmux2:∀ (fa fb fc:Sig N),fa∈A4→fb∈A4→fc∈A4→
    qa A4 {fun x=>if (st x).active i0 then (if found x then fa x else fb x) else fc x} 8:=by
    intro fa fb fc hfa hfb hfc
    let inner:Sig N:=fun x=>if found x then fa x else fb x
    have h_in:qa A4 {inner} 4:=vo (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl rfl)))))) hfa hfb
    have h_out:qa (A4 ∪ {inner})
     {fun x=>if (st x).active i0 then inner x else fc x} 4:=
     vo (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨i0,rfl⟩)))))))))
      (Or.inr rfl) (Or.inl hfc)
    exact qe h_in h_out
   have hactOut:qa A4 (Set.range (fun u:Fin m=>fun x=>(qM i (st x)).active u)) (m * 8):=
    qf _ 8 (fun u=>by
     have heq:(fun x=>(qM i (st x)).active u)=
      fun x=>if (st x).active i0 then (if found x then actPair u x else actIso u x) else (st x).active u:=by
      funext x
      simp only [qM,hi,↓reduceDIte,i0,cond,isPiv,found,actPair,actIso]
      cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
     rw [heq]
     exact hmux2 (actPair u) (actIso u) (fun x=>(st x).active u)
      (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨u,rfl⟩))))))
      (hactIso_in u)
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨u,rfl⟩)))))))))
   have hQOut:qa A4 (qn (fun x=>(qM i (st x)).Q)) (m * (m * 8)+m * 8+8):=by
    have hB:qa A4 {f|∃ u v,(fun x=>z2b ((qM i (st x)).Q.B u v))=f} (m * (m * 8)):=
     qT _ 8 (fun u v=>by
      have heq:(fun x=>z2b ((qM i (st x)).Q.B u v))=
       fun x=>if (st x).active i0 then
        (if found x then z2b ((Qpair x).B u v) else z2b (((st x).Q.delVar i0).B u v))
       else z2b ((st x).Q.B u v):=by
       funext x
       simp only [qM,hi,↓reduceDIte,i0,cond,isPiv,found,Qpair,QdelPair,
        actPair,b0,bvZ,bvRaw,avZ]
       cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
      rw [heq]
      exact hmux2 _ _ _ (Or.inr (Or.inl (Or.inl ⟨u,v,rfl⟩)))
       (hQiso_in (Or.inl (Or.inl ⟨u,v,rfl⟩)))
       (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨u,v,rfl⟩)))))))))))
    have hL:qa A4 (Set.range (fun u:Fin m=>fun x=>z2b ((qM i (st x)).Q.l u))) (m * 8):=
     qf _ 8 (fun u=>by
      have heq:(fun x=>z2b ((qM i (st x)).Q.l u))=
       fun x=>if (st x).active i0 then
        (if found x then z2b ((Qpair x).l u) else z2b (((st x).Q.delVar i0).l u))
       else z2b ((st x).Q.l u):=by
       funext x
       simp only [qM,hi,↓reduceDIte,i0,cond,isPiv,found,Qpair,QdelPair,
        actPair,b0,bvZ,bvRaw,avZ]
       cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
      rw [heq]
      exact hmux2 _ _ _ (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))
       (hQiso_in (Or.inl (Or.inr ⟨u,rfl⟩)))
       (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u,rfl⟩)))))))))))
    have hC:qa A4 {fun x=>z2b (qM i (st x)).Q.c} 8:=by
     have heq:(fun x=>z2b (qM i (st x)).Q.c)=
      fun x=>if (st x).active i0 then
       (if found x then z2b (Qpair x).c else z2b ((st x).Q.delVar i0).c)
      else z2b (st x).Q.c:=by
      funext x
      simp only [qM,hi,↓reduceDIte,i0,cond,isPiv,found,Qpair,QdelPair,
       actPair,b0,bvZ,bvRaw,avZ]
      cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
     rw [heq]
     exact hmux2 _ _ _ (Or.inr (Or.inr rfl))
      (hQiso_in (Or.inr rfl))
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))))))
    exact qd (qr (qr hB hL) hC) le_rfl Set.subset_union_right (by omega)
   have hzeroOut:qa A4 {fun x=>(qM i (st x)).zero} 9:=by
    let zIso:Sig N:=fun x=>(st x).zero||z2b ((st x).Q.l i0)
    have hz1:qa A4 {zIso} 1:=
     orB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))))
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i0,rfl⟩))))))))))
    let inner:Sig N:=fun x=>if found x then (st x).zero else zIso x
    have hz2:qa (A4 ∪ {zIso}) {inner} 4:=
     vo (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl rfl)))))))
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))))) (Or.inr rfl)
    have hz3:qa ((A4 ∪ {zIso}) ∪ {inner})
     {fun x=>if (st x).active i0 then inner x else (st x).zero} 4:=
     vo (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨i0,rfl⟩))))))))))
      (Or.inr rfl)
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))))))
    have heq:(fun x=>if (st x).active i0 then inner x else (st x).zero)=
     fun x=>(qM i (st x)).zero:=by
     funext x
     simp only [inner,zIso,qM,hi,↓reduceDIte,i0,cond,isPiv,found]
     cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
    rw [← heq]
    exact qd (qo (qo (qP hz1) (qP hz2)) hz3) le_rfl Set.subset_union_right (by omega)
   have hpowOut:qa A4 (Set.range (fun k:Fin (m+1)=>fun x=>(qM i (st x)).pow2 k))
    ((m+1) * 12):=by
    refine qf _ 12 (fun k=>?_)
    let pIso:Sig N:=fun x=>if z2b ((st x).Q.l i0) then (st x).pow2 k else qw (st x).pow2 k
    have hp1:qa A4 {pIso} 4:=
     vo (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i0,rfl⟩))))))))))
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨k,rfl⟩)))))) (hsh_in k)
    let inner:Sig N:=fun x=>if found x then qw (st x).pow2 k else pIso x
    have hp2:qa (A4 ∪ {pIso}) {inner} 4:=
     vo (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl rfl)))))))
      (Or.inl (hsh_in k)) (Or.inr rfl)
    have hp3:qa ((A4 ∪ {pIso}) ∪ {inner})
     {fun x=>if (st x).active i0 then inner x else (st x).pow2 k} 4:=
     vo (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨i0,rfl⟩))))))))))
      (Or.inr rfl)
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨k,rfl⟩))))))))
    have heq:(fun x=>if (st x).active i0 then inner x else (st x).pow2 k)=
     fun x=>(qM i (st x)).pow2 k:=by
     funext x
     simp only [inner,pIso,qM,hi,↓reduceDIte,i0,cond,isPiv,found]
     cases (st x).active i0 <;> cases (List.finRange m).any _ <;> cases z2b ((st x).Q.l i0) <;> rfl
    rw [← heq]
    exact qd (qo (qo (qP hp1) (qP hp2)) hp3) le_rfl Set.subset_union_right (by omega)
   have hOut:=qr (qr (qr hactOut hQOut) hzeroOut) hpowOut
   have hall:=qo (qo (qo (qo (qP h1) (qP h2)) (qP hprepB)) (qP hQpairB)) hOut
   exact qd hall le_rfl Set.subset_union_right (by ring_nf; omega)
 · have heq:(fun x=>qM i (st x))=st:=by funext x; simp [qM,hi]
   rw [heq]
   exact qd (zk (A:=Base ∪ vd st) (B:=vd st) Set.subset_union_right)
    le_rfl Set.subset_union_right (Nat.zero_le _)
theorem u7 {N m:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base) (htrue:(fun _=>true)∈Base)
 (free:(Fin N→Bool)→Fin m→Bool)
 (Q0:(Fin N→Bool)→qc m)
 (hfree:∀ u,(fun x=>free x u)∈Base)
 (hQ0:qn Q0⊆Base):
 qa Base (vd (fun x=>qK (free x) (Q0 x)))
  (m * (m * (m+7)+(m+1) * (2 * m)+(m * (m * 26)+m * 60+40))):=by
 let st0:(Fin N→Bool)→zL m:=
  fun x=>⟨free x,Q0 x,false,fun k=>decide (k.val=0)⟩
 have hst0:vd st0⊆Base:=by
  rintro f (((⟨u,rfl⟩|hq)|rfl)|⟨k,rfl⟩)
  · exact hfree u
  · exact hQ0 hq
  · exact hfalse
  · by_cases hk:k.val=0
    · simpa [st0,hk] using htrue
    · simpa [st0,hk] using hfalse
 have hit:=jD (Sigs:=vd) (step:=qM)
  (c:=m * (m+7)+(m+1) * (2 * m)+(m * (m * 26)+m * 60+40))
  (Base:=Base) (fun i st=>jX Base hfalse i st) m st0
 exact qd hit (Set.union_subset le_rfl hst0) Set.subset_union_right le_rfl
def qG (h n:ℕ):Fin h→ZMod 2:=
 fun s=>b2z (n.testBit s.val)
theorem yM (h:ℕ):
 Function.Bijective (fun s:Fin (2 ^ h)=>qG h s.val):=by
 rw [Fintype.bijective_iff_injective_and_card]
 refine ⟨?_,?_⟩
 · intro a b hab
   apply Fin.ext
   apply Nat.eq_of_testBit_eq
   intro j
   by_cases hj:j<h
   · have h1:=congrFun hab ⟨j,hj⟩
     have h2:=congrArg z2b h1
     simpa [qG,z0] using h2
   · have ha:a.val<2 ^ j:=lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))
     have hb:b.val<2 ^ j:=lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
     rw [Nat.testBit_lt_two_pow ha,Nat.testBit_lt_two_pow hb]
 · simp [Fintype.card_fin,Fintype.card_pi,ZMod.card]
def qg {m h:ℕ} (qs:Fin h→qc m) (σ:Fin h→ZMod 2):qc m:=
 { B:=fun u v=>∑ s:Fin h,σ s * (qs s).B u v
   l:=fun u=>∑ s:Fin h,σ s * (qs s).l u
   c:=∑ s:Fin h,σ s * (qs s).c }
theorem vv {m h:ℕ} (qs:Fin h→qc m) (hval:∀ s,(qs s).Valid)
 (σ:Fin h→ZMod 2):(qg qs σ).Valid:=by
 refine ⟨fun u=>by simp [qg,fun s=>(hval s).1 u],fun u v=>?_⟩
 dsimp only [qg]
 exact Finset.sum_congr rfl (fun s _=>by rw [(hval s).2 u v])
theorem vF {m h:ℕ} (qs:Fin h→qc m) (free:Fin m→Bool)
 (hsupp:∀ s u,free u=false→(qs s).l u=0∧∀ w,(qs s).B u w=0)
 (σ:Fin h→ZMod 2):
 ∀ u,free u=false→(qg qs σ).l u=0∧∀ w,(qg qs σ).B u w=0:=by
 intro u hu
 refine ⟨by simp [qg,fun s=>(hsupp s u hu).1],
  fun w=>by simp [qg,fun s=>(hsupp s u hu).2 w]⟩
theorem ka {m h:ℕ} (qs:Fin h→qc m) (σ:Fin h→ZMod 2)
 (a:Fin m→ZMod 2):
 (qg qs σ).eval a=∑ s:Fin h,σ s * (qs s).eval a:=by
 unfold qg qc.eval
 have hlin:(∑ i:Fin m,(∑ s:Fin h,σ s * (qs s).l i) * a i)=
  ∑ s:Fin h,σ s * ∑ i:Fin m,(qs s).l i * a i:=by
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _=>Finset.sum_congr rfl (fun i _=>by ring))
 have hquad:(∑ i:Fin m,∑ j:Fin m,
       if i.val<j.val then (∑ s:Fin h,σ s * (qs s).B i j) * a i * a j else 0)=
  ∑ s:Fin h,σ s * ∑ i:Fin m,∑ j:Fin m,
    if i.val<j.val then (qs s).B i j * a i * a j else 0:=by
  have hinner:∀ i j:Fin m,
   (if i.val<j.val then (∑ s:Fin h,σ s * (qs s).B i j) * a i * a j else 0)=
   ∑ s:Fin h,if i.val<j.val then σ s * ((qs s).B i j * a i * a j) else 0:=by
   intro i j
   by_cases hlt:i.val<j.val
   · simp only [hlt,↓reduceIte,Finset.sum_mul]
     refine Finset.sum_congr rfl (fun s _=>by ring)
   · simp [hlt]
  simp_rw [hinner]
  trans (∑ i:Fin m,∑ s:Fin h,∑ j:Fin m,
   if i.val<j.val then σ s * ((qs s).B i j * a i * a j) else 0)
  · exact Finset.sum_congr rfl (fun i _=>Finset.sum_comm)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _=>?_)
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>?_))
    by_cases hlt:i.val<j.val <;> simp [hlt]
 rw [hlin,hquad,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl (fun s _=>by ring)
theorem u6 {N m h:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base)
 (qs:(Fin N→Bool)→Fin h→qc m)
 (hqs:∀ s:Fin h,qn (fun x=>qs x s)⊆Base)
 (σ:Fin h→ZMod 2):
 qa Base (qn (fun x=>qg (qs x) σ))
  (m * (m * (4 * h))+m * (4 * h)+4 * h):=by
 have hBB:qa Base {f|∃ u v,(fun x=>z2b ((qg (qs x) σ).B u v))=f}
  (m * (m * (4 * h))):=by
  refine qT _ (4 * h) (fun u v=>?_)
  let xs:List (Sig N):=(List.finRange h).map (fun s=>
   if z2b (σ s) then (fun x=>z2b ((qs x s).B u v)) else (fun _=>false))
  have hxs:∀ f∈xs,f∈Base:=by
   intro f hf
   rcases List.mem_map.mp hf with ⟨s,_,rfl⟩
   by_cases hs:z2b (σ s)=true
   · simp only [hs,↓reduceIte]; exact hqs s (Or.inl (Or.inl ⟨u,v,rfl⟩))
   · simp [hs,hfalse]
  have hxl:=kY xs hxs hfalse
  have heq:(fun x=>zv (xs.map fun f=>f x))=
   fun x=>z2b ((qg (qs x) σ).B u v):=by
   funext x
   simp only [qg,y4,xs,List.map_map]
   congr 1
   refine List.map_congr_left (fun s _=>?_)
   simp only [Function.comp_apply,yX]
   cases z2b (σ s) <;> simp
  rw [heq,List.length_map,List.length_finRange] at hxl
  exact hxl
 have hLL:qa Base (Set.range (fun u:Fin m=>fun x=>z2b ((qg (qs x) σ).l u)))
  (m * (4 * h)):=by
  refine qf _ (4 * h) (fun u=>?_)
  let xs:List (Sig N):=(List.finRange h).map (fun s=>
   if z2b (σ s) then (fun x=>z2b ((qs x s).l u)) else (fun _=>false))
  have hxs:∀ f∈xs,f∈Base:=by
   intro f hf
   rcases List.mem_map.mp hf with ⟨s,_,rfl⟩
   by_cases hs:z2b (σ s)=true
   · simp only [hs,↓reduceIte]; exact hqs s (Or.inl (Or.inr ⟨u,rfl⟩))
   · simp [hs,hfalse]
  have hxl:=kY xs hxs hfalse
  have heq:(fun x=>zv (xs.map fun f=>f x))=
   fun x=>z2b ((qg (qs x) σ).l u):=by
   funext x
   simp only [qg,y4,xs,List.map_map]
   congr 1
   refine List.map_congr_left (fun s _=>?_)
   simp only [Function.comp_apply,yX]
   cases z2b (σ s) <;> simp
  rw [heq,List.length_map,List.length_finRange] at hxl
  exact hxl
 have hCC:qa Base {fun x=>z2b (qg (qs x) σ).c} (4 * h):=by
  let xs:List (Sig N):=(List.finRange h).map (fun s=>
   if z2b (σ s) then (fun x=>z2b (qs x s).c) else (fun _=>false))
  have hxs:∀ f∈xs,f∈Base:=by
   intro f hf
   rcases List.mem_map.mp hf with ⟨s,_,rfl⟩
   by_cases hs:z2b (σ s)=true
   · simp only [hs,↓reduceIte]; exact hqs s (Or.inr rfl)
   · simp [hs,hfalse]
  have hxl:=kY xs hxs hfalse
  have heq:(fun x=>zv (xs.map fun f=>f x))=
   fun x=>z2b (qg (qs x) σ).c:=by
   funext x
   simp only [qg,y4,xs,List.map_map]
   congr 1
   refine List.map_congr_left (fun s _=>?_)
   simp only [Function.comp_apply,yX]
   cases z2b (σ s) <;> simp
  rw [heq,List.length_map,List.length_finRange] at hxl
  exact hxl
 exact qd (qr (qr hBB hLL) hCC) le_rfl Set.subset_union_right (by omega)
def q8 {m:ℕ} (st:zL m):ℕ:=
 if !(st.zero)&&!(z2b st.Q.c) then zQ st.pow2 else 0
def q7 {m:ℕ} (st:zL m):ℕ:=
 if !(st.zero)&&z2b st.Q.c then zQ st.pow2 else 0
theorem kC {m:ℕ} (st:zL m):
 (q8 st:ℤ)-(q7 st:ℤ)=
   if st.zero then 0 else (zQ st.pow2:ℤ) * qz st.Q.c:=by
 unfold q8 q7 qz
 cases hz:st.zero
 · rcases qF st.Q.c with hc|hc
   · simp [hc,qm]
   · simp [hc,zA]
 · simp
theorem jb {m:ℕ} (st:zL m) (e:ℕ) (he:e≤ m)
 (hp:st.pow2=fun k:Fin (m+1)=>decide (k.val=e)):
 q8 st≤2 ^ m∧q7 st≤2 ^ m:=by
 unfold q8 q7
 rw [hp,vk he]
 have hle:2 ^ e≤2 ^ m:=Nat.pow_le_pow_right (by omega) he
 constructor <;> split_ifs <;> first|exact hle|exact Nat.zero_le _
def zC {m:ℕ} (u:Fin m→Bool):Fin (m+1)→Bool:=
 (List.range m).foldl
   (fun p r=>if hr:r< m then (if u ⟨r,hr⟩ then qw p else p) else p)
   (fun k=>decide (k.val=0))
theorem vh {m:ℕ} (u:Fin m→Bool):
 zC u=fun k:Fin (m+1)=>
  decide (k.val=(Finset.univ.filter (fun j:Fin m=>u j=true)).card):=by
 have hloop:∀ r≤ m,
  (List.range r).foldl
    (fun p i=>if hi:i< m then (if u ⟨i,hi⟩ then qw p else p) else p)
    (fun k:Fin (m+1)=>decide (k.val=0))=
  fun k:Fin (m+1)=>
   decide (k.val=(Finset.univ.filter (fun j:Fin m=>j.val<r∧u j=true)).card):=by
  intro r
  induction r with
  | zero=>
    intro _; funext k; simp
  | succ r ih=>
    intro hr
    have hrm:r< m:=by omega
    let j0:Fin m:=⟨r,hrm⟩
    set Sr:=Finset.univ.filter (fun j:Fin m=>j.val<r∧u j=true)
    set Sr1:=Finset.univ.filter (fun j:Fin m=>j.val<r+1∧u j=true)
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih (by omega)]
    simp only [hrm,↓reduceDIte]
    by_cases hu:u j0=true
    · have hSr1_eq:Sr1=insert j0 Sr:=by
       ext j
       simp only [Sr1,Sr,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
       constructor
       · rintro ⟨hlt,hju⟩
         by_cases hje:j.val=r
         · left; exact Fin.ext hje
         · right; exact ⟨by omega,hju⟩
       · rintro (rfl|⟨hlt,hju⟩)
         · exact ⟨by simp [j0],hu⟩
         · exact ⟨by omega,hju⟩
      have hj0_not:j0∉Sr:=by simp [Sr,j0]
      have hlt_m:Sr.card< m:=by
       have hsub:Sr1.card≤ m:=by
        calc Sr1.card≤(Finset.univ:Finset (Fin m)).card:=Finset.card_le_univ _
         _=m:=Fintype.card_fin m
       rw [hSr1_eq,Finset.card_insert_of_notMem hj0_not] at hsub
       omega
      simp only [j0,hu,↓reduceIte]
      rw [zU hlt_m,hSr1_eq,Finset.card_insert_of_notMem hj0_not]
    · have huf:u j0=false:=by cases h':u j0 <;> simp_all
      have hSr1_eq:Sr1=Sr:=by
       ext j
       simp only [Sr1,Sr,Finset.mem_filter,Finset.mem_univ,true_and]
       constructor
       · rintro ⟨hlt,hju⟩
         refine ⟨?_,hju⟩
         by_contra hge
         have hje:j=j0:=Fin.ext (by dsimp [j0]; omega)
         rw [hje,huf] at hju; exact Bool.noConfusion hju
       · rintro ⟨hlt,hju⟩; exact ⟨by omega,hju⟩
      simp only [j0,huf,Bool.false_eq_true,↓reduceIte,hSr1_eq]
 rw [zC,hloop m le_rfl]
 funext k
 congr 1
 congr 1
 congr 1
 ext j
 simp
theorem v3 {N m:ℕ} (Base:Set (Sig N))
 (hfalse:(fun _=>false)∈Base) (htrue:(fun _=>true)∈Base)
 (u:(Fin N→Bool)→Fin m→Bool)
 (hu:∀ j:Fin m,(fun x=>u x j)∈Base):
 qa Base (Set.range (fun k:Fin (m+1)=>fun x=>zC (u x) k))
  (m * ((m+1) * 4)):=by
 let Sigs:((Fin N→Bool)→(Fin (m+1)→Bool))→Set (Sig N):=
  fun p=>Set.range (fun k:Fin (m+1)=>fun x=>p x k)
 let st0:(Fin N→Bool)→(Fin (m+1)→Bool):=fun _ k=>decide (k.val=0)
 have hst0:Sigs st0⊆Base:=by
  rintro _ ⟨k,rfl⟩
  dsimp only
  by_cases hk:k=0
  · have heq:(fun x:Fin N→Bool=>st0 x k)=(fun _=>true):=by
     funext _; simp [st0,hk]
    rw [heq]; exact htrue
  · have heq:(fun x:Fin N→Bool=>st0 x k)=(fun _=>false):=by
     funext _; simp [st0,hk]
    rw [heq]; exact hfalse
 have hloop:∀ r,qa Base (Sigs (fun x=>
  (List.range r).foldl
    (fun p i=>if hi:i< m then (if u x ⟨i,hi⟩ then qw p else p) else p)
    (st0 x))) (r * ((m+1) * 4)):=by
  intro r
  induction r with
  | zero=>simpa using zk (A:=Base) (B:=Sigs st0) hst0
  | succ r ih=>
    let pr:(Fin N→Bool)→(Fin (m+1)→Bool):=fun x=>
     (List.range r).foldl
       (fun p i=>if hi:i< m then (if u x ⟨i,hi⟩ then qw p else p) else p)
       (st0 x)
    have hstep:qa (Base ∪ Sigs pr)
     (Sigs (fun x=>if hr:r< m then (if u x ⟨r,hr⟩ then qw (pr x) else pr x) else pr x))
     ((m+1) * 4):=by
     by_cases hr:r< m
     · refine qf _ 4 (fun k=>?_)
       have hsh:(fun x=>qw (pr x) k)∈Base ∪ Sigs pr:=by
        unfold qw
        by_cases h0:k.val=0
        · simp only [h0,↓reduceDIte]; exact Or.inl hfalse
        · simp only [h0,↓reduceDIte]; exact Or.inr ⟨⟨k.val-1,by omega⟩,rfl⟩
       have heq:(fun x=>(if hr':r< m then (if u x ⟨r,hr'⟩ then qw (pr x) else pr x) else pr x) k)=
        fun x=>if u x ⟨r,hr⟩ then qw (pr x) k else pr x k:=by
        funext x; simp only [hr,↓reduceDIte]; cases u x ⟨r,hr⟩ <;> rfl
       rw [heq]
       exact vo (Or.inl (hu ⟨r,hr⟩)) hsh (Or.inr ⟨k,rfl⟩)
     · have heq:(fun x=>if hr':r< m then (if u x ⟨r,hr'⟩ then qw (pr x) else pr x) else pr x)=pr:=by
        funext x; simp [hr]
       rw [heq]
       exact qd (zk (A:=Base ∪ Sigs pr) (B:=Sigs pr) Set.subset_union_right)
        le_rfl Set.subset_union_right (Nat.zero_le _)
    have heq:(fun x=>(List.range (r+1)).foldl
     (fun p i=>if hi:i< m then (if u x ⟨i,hi⟩ then qw p else p) else p) (st0 x))=
     fun x=>if hr:r< m then (if u x ⟨r,hr⟩ then qw (pr x) else pr x) else pr x:=by
     funext x; simp [List.range_succ,List.foldl_append,pr]
    rw [heq]
    exact qd (qe ih hstep) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])
 exact hloop m
theorem vn {V:Type*} [AddCommGroup V] [Module (ZMod 2) V]
 [Fintype V] (S:Submodule (ZMod 2) V) [Fintype S]:
 Fintype.card S=2 ^ Module.finrank (ZMod 2) S:=by
 let b:=Module.finBasis (ZMod 2) S
 have heqv:S ≃ (Fin (Module.finrank (ZMod 2) S)→ZMod 2):=b.equivFun.toEquiv
 rw [Fintype.card_congr heqv]
 simp [Fintype.card_pi,ZMod.card]
theorem zl {R C:ℕ} (M:Matrix (Fin R) (Fin C) (ZMod 2)):
 M.rank=Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun r:Fin R=>M r))):=by
 rw [← Matrix.rank_transpose]
 change Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin)=_
 have hsubEq:LinearMap.range M.transpose.mulVecLin=
  Submodule.span (ZMod 2) (Set.range (fun r:Fin R=>M r)):=by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    have hv:M.transpose.mulVecLin v=∑ r:Fin R,v r • M r:=by
     funext c
     simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
     exact Finset.sum_congr rfl (fun r _=>mul_comm _ _)
    rw [hv]
    exact Submodule.sum_mem _ (fun r _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨r,rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨r,rfl⟩
    refine ⟨Pi.single r 1,?_⟩
    funext c
    simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
    rw [Finset.sum_eq_single r]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ _) h
 rw [hsubEq]
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux.P25940Affine
abbrev F:=ZMod 2
abbrev V (n:ℕ):=Fin n→F
def lin {m} (v x:V m):F:=∑ i,v i * x i
def unit {m} (i:Fin m):V m:=fun j=>if j=i then 1 else 0
theorem lin_unit {m} (v:V m) (i:Fin m):lin v (unit i)=v i:=by
 simp [lin,unit,mul_ite]
theorem lin_add {m} (v x y:V m):lin v (x+y)=lin v x+lin v y:=by
 simp [lin,mul_add,Finset.sum_add_distrib]
theorem lin_coeff_add {m} (v w x:V m):lin (v+w) x=lin v x+lin w x:=by
 simp [lin,add_mul,Finset.sum_add_distrib]
def Aff {m} (f:V m→F):=∃ (a:F) (v:V m),∀ x,f x=a+lin v x
theorem Aff.const {m} (c:F):Aff (fun _:V m=>c):=by
 exact ⟨c,0,by simp [lin]⟩
theorem Aff.add {m} {f g:V m→F} (hf:Aff f) (hg:Aff g):Aff (fun x=>f x+g x):=by
 obtain ⟨a,v,hv⟩:=hf
 obtain ⟨b,w,hw⟩:=hg
 exact ⟨a+b,v+w,fun x=>by simp only [hv,hw,lin_coeff_add]; ring⟩
theorem Aff.scale {m} {f:V m→F} (b:F) (hf:Aff f):Aff (fun x=>b * f x):=by
 obtain ⟨a,v,hv⟩:=hf
 refine ⟨b*a,fun i=>b*v i,fun x=>?_⟩
 simp only [hv,mul_add]; simp [lin,Finset.mul_sum,mul_assoc]
def diff {m} (f:V m→F) (x y:V m):=f 0-f x-f y+f (x+y)
theorem diff_eq {m} (f:V m→F) (x y:V m):
 diff f x y=f 0+f x+f y+f (x+y):=by
 simp [diff,sub_eq_add_neg,ZMod.neg_eq_self_mod_two]
theorem Aff.diff_zero {m} {f:V m→F} (hf:Aff f) (x y:V m):diff f x y=0:=by
 obtain ⟨a,v,h⟩:=hf
 have h0:lin v 0=0:=by simp [lin]
 simp only [diff,h,lin_add,h0]; ring
theorem two_values (x:F):x=0∨x=1:=by decide +revert
theorem sq_id (x:F):x*x=x:=by rcases two_values x with rfl|rfl <;> decide
theorem degenerate {m} (v w:V m)
 (h:∀ i j,i<j→v i*w j+v j*w i=0):v=0∨w=0∨v=w:=by
 by_cases hv:v=0
 · exact Or.inl hv
 obtain ⟨i,hi⟩:∃ i,v i≠0:=by
  by_contra! hn
  exact hv (funext hn)
 have hi':=(two_values (v i)).resolve_left hi
 have row (j:Fin m):w j=v j * w i:=by
  rcases lt_trichotomy i j with hij|rfl|hji
  · have hh:=h i j hij
    rw [hi',one_mul] at hh
    simpa [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_left hh)
  · simp [hi']
  · have hh:=h j i hji
    rw [add_comm,hi',one_mul] at hh
    simpa [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_left hh)
 rcases two_values (w i) with h0|h1
 · exact Or.inr (Or.inl (funext (fun j=>by simpa [h0] using row j)))
 · exact Or.inr (Or.inr (funext (fun j=>by simpa [h1] using (row j).symm)))
theorem step_aff {m} {f g q:V m→F} (hf:Aff f) (hg:Aff g) (hq:Aff q)
 (h:∀ i j:Fin m,i<j→diff (fun x=>f x+g x*q x) (unit i) (unit j)=0):
 Aff (fun x=>f x+g x*q x):=by
 obtain ⟨a,v,hv⟩:=hg
 obtain ⟨b,w,hw⟩:=hq
 have hh (i j:Fin m) (hij:i<j):v i*w j+v j*w i=0:=by
  obtain ⟨c,u,hu⟩:=hf
  have e:=h i j hij
  have lin0 (l:V m):lin l 0=0:=by simp [lin]
  simp only [diff,hu,hv,hw,lin0,lin_add,lin_unit] at e
  linear_combination e
 apply hf.add
 rcases degenerate v w hh with h0|h0|hsame
 · subst v
   simpa only [hv,lin,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] using
    (Aff.scale a ⟨b,w,hw⟩:Aff (fun x=>a * q x))
 · subst w
   have ht:∀ x,q x=b:=fun x=>by simp [hw,lin]
   simpa only [ht,mul_comm] using (Aff.scale b ⟨a,v,hv⟩:Aff (fun x=>b * g x))
 · subst w
   have he (x:V m):g x*q x=a*b+(a+b+1)*lin v x:=by
    rw [hv,hw]; linear_combination sq_id (lin v x)
   have hl:Aff (lin v):=⟨0,v,by simp⟩
   simpa only [he] using (Aff.const (a*b)).add (Aff.scale (a+b+1) hl)
def shift {m k} (gen:Fin m→V k) (x:V m):V k:=∑ i,x i • gen i
theorem shift_apply {m k} (gen:Fin m→V k) (j:Fin k) (x:V m):
 shift gen x j=lin (fun i=>gen i j) x:=by
 simp [shift,lin,Finset.sum_apply,smul_eq_mul,mul_comm]
theorem shift_add {m k} (gen:Fin m→V k) (x y:V m):
 shift gen (x+y)=shift gen x+shift gen y:=by
 funext j; simp [shift_apply,lin_add]
theorem shift_unit {m k} (gen:Fin m→V k) (i:Fin m):shift gen (unit i)=gen i:=by
 funext j; rw [shift_apply,lin_unit]
theorem aff_key {m k} (gen:Fin m→V k) (a:V k) (j:Fin k):
 Aff (fun x=>(a+shift gen x) j):=⟨a j,fun i=>gen i j,fun x=>by simp [shift_apply]⟩
section Recurrence
variable {m k:ℕ} (hk:0<k)
def ix (u:ℕ):Fin k:=⟨u % k,Nat.mod_lt _ hk⟩
def gap (b:Bool):=if b then 2 else 1
def start (b:Bool):=if b then 3 else 1
def feed (b:Bool) (t:Nat):=if b then 3*(t+1)+1 else 2*t
def rot (s:ℕ) (x:V k) (j:Fin k):=x (ix hk (j.val+k-s % k))
def mix (b:Bool) (z:V k) (i:Fin k):=
 z i+z (ix hk (i.val+gap b))+z (ix hk (i.val+k-gap b % k))
def update (b:Bool) (key:V k) (t:ℕ) (C z:V k) (j:Fin k):=
 mix hk b z j+(1+mix hk b z (ix hk (j.val+1)))*mix hk b z (ix hk (j.val+2)) +
  rot hk (feed b t) key j+C j
def state {r:ℕ} (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
    (b:Bool) (key:V k) (n:ℕ):V k:=
 ((List.finRange (r+1)).take n).foldl (fun z tick=>update hk b key tick.val (c b tick) z)
   (rot hk (start b) key+name b)
theorem state_step {r:ℕ} (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (b:Bool) (key:V k) (n:ℕ) (hn:n<r+1):
 state hk name c b key (n+1)=update hk b key n (c b ⟨n,hn⟩) (state hk name c b key n):=by
 unfold state
 rw [List.take_succ_eq_append_getElem (by simpa using hn:n<(List.finRange (r+1)).length)]
 simp
def closed (watch:Bool→ℕ→Fin k→Bool) (N:ℕ):=
 ∀ b n,n<N→∀ j:Fin k,watch b (n+1) j=true→∀ e:Fin 3,
   let i:=ix hk (j.val+e.val)
   watch b n i=true∧watch b n (ix hk (i.val+gap b))=true∧
    watch b n (ix hk (i.val+k-gap b % k))=true
theorem aff_prefix {r:ℕ} (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (gen:Fin m→V k) (a:V k) (b:Bool) (watch:Bool→ℕ→Fin k→Bool)
 (hc:closed hk watch (r+1))
 (checks:∀ n,0<n→n≤r→∀ j,watch b n j=true→∀ i l:Fin m,i<l→
   diff (fun x=>state hk name c b (a+shift gen x) n j) (unit i) (unit l)=0):
 ∀ n,n≤r→∀ j,watch b n j=true→Aff (fun x=>state hk name c b (a+shift gen x) n j):=by
 intro n
 induction n with
 | zero=>
   intro _ j _
   exact (aff_key gen a (ix hk (j.val+k-start b % k))).add (Aff.const (name b j))
 | succ n ih=>
   intro hn j hj
   let key (x:V m):=a+shift gen x
   let Y (i:Fin k) (x:V m):=mix hk b (state hk name c b (key x) n) i
   have hY (e:Fin 3):Aff (Y (ix hk (j.val+e.val))):=by
    obtain ⟨h₁,h₂,h₃⟩:=hc b n (by omega) j hj e
    exact ((ih (by omega) _ h₁).add (ih (by omega) _ h₂)).add (ih (by omega) _ h₃)
   have heq:ix hk (j.val+(0:Fin 3).val)=j:=by apply Fin.ext; simp [ix,Nat.mod_eq_of_lt j.isLt]
   have h₀:Aff (Y j):=heq▸hY 0
   let A:=fun x=>Y j x+rot hk (feed b n) (key x) j+c b ⟨n,by omega⟩ j
   let G:=fun x=>1+Y (ix hk (j.val+1)) x
   let Q:=Y (ix hk (j.val+2))
   have hA:Aff A:=(h₀.add (aff_key gen a _)).add (Aff.const _)
   have hG:Aff G:=(Aff.const 1).add (hY 1)
   have hQ:Aff Q:=hY 2
   have evalStep (x:V m):state hk name c b (a+shift gen x) (n+1) j=A x+G x*Q x:=by
    rw [state_step hk name c b _ n (by omega)]; unfold update A G Q Y key; ring
   have hs:=step_aff hA hG hQ (fun i l hil=>by
    simpa only [diff,evalStep] using checks (n+1) (by omega) hn j hj i l hil)
   simpa only [evalStep] using hs
end Recurrence
theorem aff_coset {m k} (gen:Fin m→V k) (a:V k) (f:V k→F)
 (hf:Aff (fun x=>f (a+shift gen x))) (u x y:V m):
 let b:=a+shift gen u
 f b+f (b+shift gen x)+f (b+shift gen y)+f (b+shift gen x+shift gen y)=0:=by
 obtain ⟨c,v,h⟩:=hf
 change f (a+shift gen u)+f (a+shift gen u+shift gen x) +
  f (a+shift gen u+shift gen y)+f (a+shift gen u+shift gen x+shift gen y)=0
 simp only [add_assoc,←shift_add,h,lin_add]
 generalize lin v u=U; generalize lin v x=X; generalize lin v y=Y
 clear *-c U X Y
 decide +revert
theorem shift_zero {m k} (gen:Fin m→V k):shift gen 0=0:=by simp [shift]
theorem prefix_pair_iff {m d k r:ℕ} (hk:0<k)
 (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (gen:Fin m→V k) (dir:Fin d→V k)
 (same:Set.range (shift dir)=Set.range (shift gen))
 {R:Type*} (rep:R→V k) (cover:∀ a,∃ s u,a=rep s+shift dir u)
 (watch:Bool→ℕ→Fin k→Bool) (hc:closed hk watch (r+1)):
 (∀ a b n,n≤r→∀ j,watch b n j=true→∀ x y,
   state hk name c b a n j+state hk name c b (a+shift gen x) n j +
    state hk name c b (a+shift gen y) n j+state hk name c b (a+shift gen x+shift gen y) n j=0)
 ↔(∀ s b n,0<n→n≤r→∀ j,watch b n j=true→∀ i l:Fin d,i<l→
  state hk name c b (rep s) n j+state hk name c b (rep s+dir i) n j +
   state hk name c b (rep s+dir l) n j+state hk name c b (rep s+dir i+dir l) n j=0):=by
 constructor
 · intro good s b n _ hn j hj i l _
   have memDir (u:Fin d):dir u∈Set.range (shift gen):=by
    rw [← same]; exact ⟨unit u,shift_unit dir u⟩
   obtain ⟨x,hx⟩:=memDir i
   obtain ⟨y,hy⟩:=memDir l
   simpa only [hx,hy] using good (rep s) b n hn j hj x y
 · intro checks a b n hn j hj x y
   obtain ⟨s,u,rfl⟩:=cover a
   have hf:=aff_prefix hk name c dir (rep s) b watch hc (by
    intro n hn' hn j hj i l hil
    rw [diff_eq]
    simpa only [shift_add,shift_unit,shift_zero,add_zero,add_assoc] using
     checks s b n hn' hn j hj i l hil) n hn j hj
   have memGen (z:V m):shift gen z∈Set.range (shift dir):=by
    rw [same]; exact ⟨z,rfl⟩
   obtain ⟨x',hx⟩:=memGen x
   obtain ⟨y',hy⟩:=memGen y
   simpa only [hx,hy] using
    aff_coset dir (rep s) (fun key=>state hk name c b key n j) hf u x' y'
end PEqualNP.Outside.L_meta_27129_aux.P25940Affine
namespace PEqualNP.Outside.L_meta_27129_aux.P25940Sample
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine PEqualNP.Outside.L_meta_27129_aux
def sample {m k:ℕ} (gen:Fin m→V k) (rep:V k) (f:V k→F) (target:F):qc m:=
 ⟨fun i j=>f rep+f (rep+gen i)+f (rep+gen j)+f (rep+gen i+gen j),
  fun i=>f rep+f (rep+gen i),f rep+target⟩
theorem sample_valid {m k} (gen:Fin m→V k) (rep:V k) (f:V k→F) (target:F):
 (sample gen rep f target).Valid:=by
 constructor
 · intro i
   have hd:rep+gen i+gen i=rep:=by funext j; simp [add_assoc,qj]
   simp only [sample,hd]; linear_combination qj (f rep)+qj (f (rep+gen i))
 · intro i j
   have hs:rep+gen i+gen j=rep+gen j+gen i:=add_right_comm ..
   simp only [sample,hs]; ring
def OneProduct {m} (q:V m→F):=∃ (A G H:V m→F),Aff A∧Aff G∧Aff H∧
 ∀ x,q x=A x+G x * H x
def Checks {k m r} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
    (gen:Fin m→V k) (rep:V k) (watch:Bool→ℕ→Fin k→Bool):=
 ∀ b n,0<n→n≤r→∀ j,watch b n j=true→∀ i l:Fin m,i<l→
   (sample gen rep (fun key=>state hk name c b key n j) 0).B i l=0
theorem terminal_oneProduct {k m r} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (gen:Fin m→V k) (rep:V k) (watch:Bool→ℕ→Fin k→Bool) (hc:closed hk watch (r+1))
 (hs:Checks hk name c gen rep watch) (b:Bool) (j:Fin k) (hj:watch b (r+1) j=true):
 OneProduct (fun x=>state hk name c b (rep+shift gen x) (r+1) j):=by
 have hh:=aff_prefix hk name c gen rep b watch hc (by
  intro n hn' hn j hj i l hil; rw [diff_eq]
  simpa only [sample,shift_add,shift_unit,shift_zero,add_zero,add_assoc] using hs b n hn' hn j hj i l hil) r le_rfl
 let key (x:V m):=rep+shift gen x
 let Y (s:Fin k) (x:V m):=mix hk b (state hk name c b (key x) r) s
 have hY (e:Fin 3):Aff (Y (ix hk (j.val+e.val))):=by
  obtain ⟨h₁,h₂,h₃⟩:=hc b r (by omega) j hj e
  exact ((hh _ h₁).add (hh _ h₂)).add (hh _ h₃)
 have heq:ix hk (j.val+(0:Fin 3).val)=j:=by apply Fin.ext; simp [ix,Nat.mod_eq_of_lt j.isLt]
 have h₀:Aff (Y j):=heq▸hY 0
 let A:=fun x=>Y j x+rot hk (feed b r) (key x) j+c b ⟨r,by omega⟩ j
 let G:=fun x=>1+Y (ix hk (j.val+1)) x
 let Q:=Y (ix hk (j.val+2))
 refine ⟨A,G,Q,(h₀.add (aff_key gen rep _)).add (Aff.const _),(Aff.const 1).add (hY 1),hY 2,fun x=>?_⟩
 change state hk name c b (key x) (r+1) j=A x+G x * Q x
 rw [state_step hk name c b _ r (by omega)]; unfold update A G Q Y key; ring
private theorem four {m} (f:V m→F) (x i j:V m):
 f x+f (x+i)+f (x+j)+f (x+i+j)=f x-f (x+i)-f (x+j)+f (x+i+j):=by
 simp [sub_eq_add_neg,ZMod.neg_eq_self_mod_two]
private theorem cross {m} {f:V m→F} {a b c:F} {v w z:V m}
 (h:∀ x,f x=a+lin v x+(b+lin w x)*(c+lin z x)) (x i j:V m):
 f x+f (x+i)+f (x+j)+f (x+i+j)=lin w i*lin z j+lin w j*lin z i:=by
 rw [four]; simp only [h,lin_add]; ring
private theorem sampled_B {m k} (gen:Fin m→V k) (rep:V k) (f:V k→F) (t:F)
 {a b c:F} {v w z:V m} (h:∀ x,f (rep+shift gen x)=a+lin v x+(b+lin w x)*(c+lin z x))
 (x:V m) (i j:Fin m):
 (sample gen (rep+shift gen x) f t).B i j=w i*z j+w j*z i:=by
 have h':=cross (f:=fun x=>f (rep+shift gen x)) h x (unit i) (unit j)
 simpa only [sample,shift_add,shift_unit,lin_unit,add_assoc] using h'
private theorem OneProduct.coeffs {m} {q:V m→F} (hf:OneProduct q):
 ∃ (a b c:F) (v w z:V m),∀ x,q x=a+lin v x+(b+lin w x)*(c+lin z x):=by
 obtain ⟨A,G,H,⟨a,v,ha⟩,⟨b,w,hb⟩,⟨c,z,hc⟩,h⟩:=hf
 exact ⟨a,b,c,v,w,z,fun x=>by rw [h,ha,hb,hc]⟩
theorem sample_eval {m k} (gen:Fin m→V k) (rep:V k) (f:V k→F) (t:F)
 (hp:OneProduct (fun x=>f (rep+shift gen x))) (x:V m):
 (sample gen rep f t).eval x=f (rep+shift gen x)+t:=by
 obtain ⟨a,b,c,v,w,z,h⟩:=hp.coeffs
 let P:qc m:=⟨fun _ _=>0,v,a+t⟩
 have h0 (v:V m):lin v 0=0:=by simp [lin]
 have hrep:f rep=a+b*c:=by simpa only [shift_zero,add_zero,h0] using h 0
 have he (i:Fin m):f (rep+gen i)=a+v i+(b+w i)*(c+z i):=by
  simpa only [shift_unit,lin_unit] using h (unit i)
 have heq:sample gen rep f t=P.addAffineProd b w c z:=by
  have extQ (M N:qc m) (e:M.B=N.B∧M.l=N.l∧M.c=N.c):M=N:=by
   cases M; cases N; obtain ⟨rfl,rfl,rfl⟩:=e; rfl
  apply extQ
  refine ⟨funext fun i=>funext fun j=>?_,funext fun i=>?_,?_⟩
  · have hb:=sampled_B gen rep f t h 0 i j
    simp only [shift_zero,add_zero] at hb
    rw [hb]; change _=if i=j then 0 else 0+w i*z j+w j*z i
    split_ifs with heq
    · subst j; exact qj _
    · simp
  · change f rep+f (rep+gen i)=v i+b*z i+c*w i+w i*z i
    rw [← ZMod.neg_eq_self_mod_two (f rep),hrep,he]; ring
  · change f rep+t=(a+t)+b*c; rw [hrep]; ring
 have hP:P.eval x=a+t+lin v x:=by simp [P,qc.eval,lin]
 rw [heq,qc.v5,hP,h]; unfold lin; ring
theorem sample_B_invariant {m k} (gen:Fin m→V k) (rep:V k) (f:V k→F) (t:F)
 (hp:OneProduct (fun x=>f (rep+shift gen x))) (x:V m):
 (sample gen (rep+shift gen x) f t).B=(sample gen rep f t).B:=by
 obtain ⟨a,b,c,v,w,z,h⟩:=hp.coeffs
 funext i j; have h0:=sampled_B gen rep f t h 0 i j
 simp only [shift_zero,add_zero] at h0
 exact (sampled_B gen rep f t h x i j).trans h0.symm
def matrix {m k t} (gen:Fin m→V k) (rep:V k) (f:Fin t→V k→F) (target:Fin t→F):
    Matrix (Fin t) (Fin m×Fin m) F:=Matrix.of fun i jl=>(sample gen rep (f i) (target i)).B jl.1 jl.2
theorem terminal_sample {m k r t} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (gen:Fin m→V k) (rep:V k) (watch:Bool→ℕ→Fin k→Bool) (hc:closed hk watch (r+1))
 (side:Fin t→Bool) (site:Fin t→Fin k) (hw:∀ i,watch (side i) (r+1) (site i)=true)
 (target:Fin t→F) (hs:Checks hk name c gen rep watch):
 let f:=fun (i:Fin t) (key:V k)=>state hk name c (side i) key (r+1) (site i)
 (∀ i x,(sample gen rep (f i) (target i)).eval x=f i (rep+shift gen x)+target i)∧
 (∀ x,matrix gen (rep+shift gen x) f target=matrix gen rep f target)∧
 (∀ x,(matrix gen (rep+shift gen x) f target).rank=(matrix gen rep f target).rank):=by
 let f:=fun (i:Fin t) (key:V k)=>state hk name c (side i) key (r+1) (site i)
 have hp (i:Fin t):OneProduct (fun x=>f i (rep+shift gen x)):=
  terminal_oneProduct hk name c gen rep watch hc hs (side i) (site i) (hw i)
 have hm (x:V m):matrix gen (rep+shift gen x) f target=matrix gen rep f target:=by
  ext i jl; exact congrFun (congrFun (sample_B_invariant gen rep (f i) (target i) (hp i) x) jl.1) jl.2
 exact ⟨fun i=>sample_eval gen rep (f i) (target i) (hp i),hm,fun x=>congrArg Matrix.rank (hm x)⟩
end PEqualNP.Outside.L_meta_27129_aux.P25940Sample
namespace PEqualNP.Outside.L_meta_27129_aux
noncomputable section
abbrev qZ (m k:ℕ):=Fin m→Fin k→ZMod 2
abbrev qx {m k} (g:qZ m k):=qA g (fun _=>Fin.elim0)
def vT {m k} (g:qZ m k) (r:Fin m) (j:Fin k):=
 (List.finRange m).all (fun s=>if s=r then z2b ((qx g).M s j) else !(z2b ((qx g).M s j)))
def vg {m k} (g:qZ m k) (r:Fin m):=qi (vT g r)
def qh {m k} (g:qZ m k) (j:Fin k):=!((List.finRange m).any (fun r=>vg g r j))
def zK {m k} (g:qZ m k):=Finset.univ.filter (fun j=>qh g j=true)
def yc {m k} (g:qZ m k) (j:Fin k):=((zK g).filter (·<j)).card
noncomputable def kh (n:ℕ):Fin (2^n) ≃ (Fin n→ZMod 2):=
 Fintype.equivOfCardEq (by simp [ZMod.card])
def z5 (n a b:ℕ):ZMod 2:=
 if ha:a<2^n then if hb:b<n then kh n ⟨a,ha⟩ ⟨b,hb⟩ else 0 else 0
def zN {k m} (p:ℕ) (g:qZ m k) (i:Fin (2^min k p)) (j:Fin k):ZMod 2:=
 if qh g j then z5 (zK g).card i.val (yc g j) else 0
def yq {k m} (p:ℕ) (g:qZ m k) (i:Fin (2^min k p)):=decide (i.val<2^(zK g).card)
def yp {k m} (p:ℕ) (g:qZ m k):=decide ((zK g).card≤p)
theorem ki {m k} (g:qZ m k) (r j):vT g r j=true↔
 (qx g).M r j=1∧∀ s,s≠r→(qx g).M s j=0:=by
 simp only [vT,List.all_eq_true,List.mem_finRange,forall_const]
 constructor
 · intro h
   refine ⟨(qF _).resolve_left ?_,fun s hs=>?_⟩
   · simpa [z2b] using h r
   · simpa [hs,z2b] using h s
 · rintro ⟨h1,h0⟩ s
   by_cases hs:s=r
   · simpa [hs,h1] using zA
   · simp [hs,h0 s hs,qm]
theorem vQ {m k} (g:qZ m k) (r:Fin m):
 (∃ j,vg g r j=true)↔(qx g).used r=true:=by
 change (∃ j,qi _ j=true)↔_
 rw [← show (∃ j,vT g r j=true)↔(qx g).used r=true from by
  rcases qv g (fun _=>Fin.elim0) with ⟨_,hp,hz,_,_⟩
  simp_rw [ki]
  constructor
  · rintro ⟨j,h1,_⟩
    cases h:(qx g).used r
    · exact False.elim (zero_ne_one ((hz r h j).symm.trans h1))
    · rfl
  · exact hp r]
 exact q0 _
abbrev vu {m k} (g:qZ m k):=Finset.univ.filter (fun r=>(qx g).used r=true)
noncomputable def qN {m k} (g:qZ m k) (r:vu g):Fin k:=
 ((vQ g r).2 (Finset.mem_filter.mp r.2).2).choose
theorem yD {m k} (g:qZ m k) (r:vu g):
 vg g r (qN g r)=true:=((vQ g r).2 (Finset.mem_filter.mp r.2).2).choose_spec
theorem yR {m k} (g:qZ m k) (r:vu g) {j:Fin k} (h:vg g r j=true):
 qN g r=j:=by
 exact q2 _ (yD g r) h
theorem zB {m k} (g:qZ m k) (r:vu g):
 (qx g).M r (qN g r)=1∧∀ s,s≠r.val→(qx g).M s (qN g r)=0:=
 (ki _ _ _).1 ((qU _ _).1 (yD g r)).1
theorem um {m k} (g:qZ m k):Function.Injective (qN g):=by
 intro r s h
 by_contra hn
 have h0:=(zB g s).2 r (fun e=>hn (Subtype.ext e))
 rw [← h,(zB g r).1] at h0
 exact one_ne_zero h0
theorem zD {m k} (g:qZ m k) (j:Fin k):
 qh g j=true↔¬ ∃ r:vu g,qN g r=j:=by
 have h:(∃ r,vg g r j=true)↔∃ r:vu g,qN g r=j:=by
  constructor
  · rintro ⟨r,hr⟩
    let u:vu g:=⟨r,by simp [(vQ g r).1 ⟨j,hr⟩]⟩
    exact ⟨u,yR g u hr⟩
  · rintro ⟨r,rfl⟩
    exact ⟨r,yD g r⟩
 rw [← h]
 change (!(List.finRange m).any _)=true↔_
 rw [Bool.not_eq_true',← Bool.not_eq_true]
 simp
theorem kL {m k} (g:qZ m k):(zK g).card=
 k-Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)):=by
 classical
 have h:zK g=(Finset.univ.image (qN g))ᶜ:=by
  ext j; simp [zK,zD]
 rw [h,Finset.card_compl,Finset.card_image_of_injective _ (um g)]
 simp [zw]
theorem jg {m k} (p) (g:qZ m k):yp p g=true↔
 k-Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g))≤p:=by
 simp [yp,kL]
def ur {m k} (g:qZ m k) (j:zK g):Fin (zK g).card:=
 ⟨yc g j,by
   apply Finset.card_lt_card
   apply Finset.ssubset_iff_subset_ne.mpr
   refine ⟨Finset.filter_subset _ _,fun h=>?_⟩
   have hj:j.val∈(zK g).filter (·<j.val):=by rw [h]; exact j.property
   simp at hj⟩
theorem ji {m k} (g:qZ m k):Function.Bijective (ur g):=by
 apply (Fintype.bijective_iff_injective_and_card _).2
 refine ⟨StrictMono.injective ?_,by simp⟩
 intro i j hij
 change ((zK g).filter (·< i.val)).card<((zK g).filter (·<j.val)).card
 apply Finset.card_lt_card
 apply Finset.ssubset_iff_subset_ne.mpr
 refine ⟨fun x hx=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,lt_trans (Finset.mem_filter.mp hx).2 hij⟩,fun h=>?_⟩
 have hi:i.val∈(zK g).filter (·<j.val):=Finset.mem_filter.mpr ⟨i.property,hij⟩
 rw [← h] at hi
 exact lt_irrefl _ (Finset.mem_filter.mp hi).2
theorem kA {m k} (p) (g:qZ m k) (hg:yp p g=true) (w:Fin k→ZMod 2):
 ∃! i:Fin (2^min k p),yq p g i=true∧
     w-zN p g i∈Submodule.span (ZMod 2) (Set.range g):=by
 classical
 let S:=Submodule.span (ZMod 2) (Set.range g)
 let n:=(zK g).card
 have hnk:n≤k:=by simpa [n] using (zK g).card_le_univ
 have hnp:n≤ min k p:=le_min hnk (of_decide_eq_true hg)
 let idx:Fin (2^n)→Fin (2^min k p):=Fin.castLE (Nat.pow_le_pow_right (by decide) hnp)
 let f:Fin (2^n)×S→(Fin k→ZMod 2):=fun z=>zN p g (idx z.1)+z.2.val
 have surj:Function.Surjective f:=by
  intro v
  let z:Fin k→ZMod 2:=∑ r:vu g,(v (qN g r)) • (qx g).M r
  have hz:z∈S:=by
   apply Submodule.sum_mem
   intro r _
   apply Submodule.smul_mem
   change _∈Submodule.span _ (Set.range g)
   rw [← (qv g (fun _=>Fin.elim0)).1]
   exact Submodule.subset_span ⟨r.val,rfl⟩
  have hp (r:vu g):z (qN g r)=v (qN g r):=by
   simp only [z,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
   rw [Fintype.sum_eq_single r]
   · rw [(zB g r).1,mul_one]
   · intro s hs
     rw [(zB g r).2 s (fun e=>hs (Subtype.ext e)),mul_zero]
  let e:=Equiv.ofBijective (ur g) (ji g)
  let word:Fin n→ZMod 2:=fun b=>(v-z) (e.symm b).val
  let a:=(kh n).symm word
  refine ⟨⟨a,⟨z,hz⟩⟩,?_⟩
  funext j
  change zN p g (idx a) j+z j=v j
  by_cases hj:qh g j=true
  · let u:zK g:=⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
    have huv:z5 n a.val (yc g j)=word (e u):=by
     have hb:yc g j<n:=(ur g u).isLt
     simp only [z5,dite_eq_left a.isLt,dite_eq_left hb]
     exact congrFun ((kh n).apply_symm_apply word) (e u)
    change (if qh g j then z5 n a.val (yc g j) else 0)+z j=v j
    rw [ite_eq_left hj,huv]
    simp [word,u]
  · obtain ⟨r,rfl⟩:=Classical.not_not.mp (fun h=>hj ((zD g j).2 h))
    simp [zN,hj,hp]
 have bij:Function.Bijective f:=by
  apply (Fintype.bijective_iff_surjective_and_card _).2
  refine ⟨surj,?_⟩
  have hr':Module.finrank (ZMod 2) S≤k:=by
   simpa only [Module.finrank_fin_fun] using S.finrank_le
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,ZMod.card,vn,← pow_add]
  congr 1
  change (zK g).card+Module.finrank (ZMod 2) S=k
  rw [kL]
  exact Nat.sub_add_cancel hr'
 obtain ⟨⟨a,s⟩,ha⟩:=surj w
 change zN p g (idx a)+s.val=w at ha
 refine ⟨idx a,⟨decide_eq_true a.isLt,?_⟩,?_⟩
 · rw [← ha,add_sub_cancel_left]; exact s.property
 · rintro i ⟨hi,hs⟩
   let b:Fin (2^n):=⟨i.val,of_decide_eq_true hi⟩
   have h:f (b,⟨w-zN p g i,hs⟩)=f (a,s):=by
    change zN p g i+(w-zN p g i)=zN p g (idx a)+s.val
    rw [ha]; abel
   exact congrArg idx (congrArg Prod.fst (bij.1 h))
def jh {N k m} (p:ℕ) (g:(Fin N→Bool)→qZ m k):Set (Sig N):=
 ({fun x=>yp p (g x)} ∪ Set.range (fun i=>fun x=>yq p (g x) i)) ∪
   {f|∃ i j,(fun x=>z2b (zN p (g x) i j))=f}
theorem vC {N n} {A:Set (Sig N)} (f:Fin n→Sig N)
 (hf:∀ i,f i∈A) (hz:(fun _=>false)∈A):
 qa A {fun x=>(List.finRange n).any (fun i=>f i x)} n:=by
 simpa [List.any_map,Function.comp_def] using vt ((List.finRange n).map f) (by simpa using hf) hz
theorem vB {N n} {A:Set (Sig N)} (f:Fin n→Sig N)
 (hf:∀ i,f i∈A) (hz:(fun _=>true)∈A):
 qa A {fun x=>(List.finRange n).all (fun i=>f i x)} n:=by
 simpa [List.all_map,Function.comp_def] using kK ((List.finRange n).map f) (by simpa using hf) hz
theorem yr {N n} {A:Set (Sig N)} (hz:(fun _=>false)∈A)
 (w:(Fin N→Bool)→Fin n) (f:Fin n→Sig N)
 (hw:∀ i,(fun x=>decide (i=w x))∈A) (hf:∀ i,f i∈A):
 qa A {fun x=>f (w x) x} (n*2):=by
 let terms:=fun (i:Fin n) (x:Fin N→Bool)=>decide (i=w x)&&f i x
 have h1:=qf terms 1 (fun i=>qD (hw i) (hf i))
 have h2:=vC (A:=A ∪ Set.range terms) terms (fun i=>Or.inr ⟨i,rfl⟩) (Or.inl hz)
 have heq:(fun x=>(List.finRange n).any (fun i=>terms i x))=fun x=>f (w x) x:=by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [terms]
 rw [heq] at h2
 exact qd (qe h1 h2) le_rfl Set.subset_union_right (by omega)
def zV {k m} (g:qZ m k) (a:Fin (k+1)):Fin (k+1):=
 ⟨((zK g).filter (fun j=>j.val<a.val)).card,by
   have hh:=((zK g).filter (fun j=>j.val<a.val)).card_le_univ
   simp only [Fintype.card_fin] at hh; omega⟩
theorem kt {k m} (g:qZ m k):
 (zV g (Fin.last k)).val=(zK g).card:=by
 simp [zV]
theorem jH {N k m} (A:Set (Sig N)) (hz:(fun _=>false)∈A)
 (ht:(fun _=>true)∈A) (g:(Fin N→Bool)→qZ m k)
 (hf:∀ j,(fun x=>qh (g x) j)∈A):
 qa A (⋃ a:Fin (k+1),Set.range (fun i:Fin (k+1)=>fun x=>decide (i=zV (g x) a)))
  ((k+1)*(k*((k+1)*4))):=by
 apply v7
 intro a
 let u:=fun (x:Fin N→Bool) (j:Fin k)=>if j.val<a.val then qh (g x) j else false
 have hu (j:Fin k):(fun x=>u x j)∈A:=by
  by_cases h:j.val<a.val <;> simp [u,h] <;> solve_by_elim
 have heq (i:Fin (k+1)) (x:Fin N→Bool):zC (u x) i=decide (i=zV (g x) a):=by
  rw [vh]
  have hset:Finset.univ.filter (fun j=>u x j=true)=(zK (g x)).filter (fun j=>j.val<a.val):=by
   ext j; by_cases h:j.val<a.val <;> simp [u,h,zK]
  simp [hset,zV,Fin.ext_iff]
 simpa only [heq] using v3 A hz ht u hu
theorem jG {N m k} (A:Set (Sig N)) (hz:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (g:(Fin N→Bool)→qZ m k)
 (hM:∀ r j,(fun x=>z2b ((qx (g x)).M r j))∈A):
 qa A (Set.range (fun j=>fun x=>qh (g x) j))
  (m*(k*1)+m*(k*m)+m*(k*(k+2))+k*(m+1)):=by
 let neg:=fun (r:Fin m) (j:Fin k) (x:Fin N→Bool)=>!(z2b ((qx (g x)).M r j))
 have H1:=qT neg 1 (fun r j=>zn (hM r j))
 let A1:=A ∪ {f|∃ r j,neg r j=f}
 let priv:=fun (r:Fin m) (j:Fin k) x=>vT (g x) r j
 have H2:qa A1 {f|∃ r j,priv r j=f} (m*(k*m)):=by
  refine qT priv m (fun r j=>?_)
  let term:=fun (s:Fin m) (x:Fin N→Bool)=>if s=r then z2b ((qx (g x)).M s j) else neg s j x
  apply vB term _ (Or.inl ht)
  intro s; by_cases hs:s=r
  · simpa only [term,ite_eq_left hs] using (show (fun x=>z2b ((qx (g x)).M s j))∈A1 from Or.inl (hM s j))
  · simpa only [term,ite_eq_right hs] using (show neg s j∈A1 from Or.inr ⟨s,j,rfl⟩)
 let A2:=A1 ∪ {f|∃ r j,priv r j=f}
 let pick:=fun (r:Fin m) (j:Fin k) x=>vg (g x) r j
 have H3:qa A2 (⋃ r,Set.range (pick r)) (m*(k*(k+2))):=
  v7 _ _ (fun r=>yE (priv r) (Or.inl (Or.inl hz)) (fun j=>Or.inr ⟨r,j,rfl⟩))
 let A3:=A2 ∪ ⋃ r,Set.range (pick r)
 have H4:qa A3 (Set.range (fun j=>fun x=>qh (g x) j)) (k*(m+1)):=by
  refine qf _ _ (fun j=>?_)
  have hh:=vC (A:=A3) (fun r=>pick r j)
   (fun r=>Or.inr (Set.mem_iUnion.mpr ⟨r,⟨j,rfl⟩⟩)) (Or.inl (Or.inl (Or.inl hz)))
  exact qe hh (zn (Or.inr rfl))
 exact qo (qo (qo (qP H1) (qP H2)) (qP H3)) H4
theorem uD {N k m} (A:Set (Sig N)) (hz:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (p:ℕ) (g:(Fin N→Bool)→qZ m k) (hg:∀ r j,(fun x=>z2b (g x r j))∈A):
 qa A (jh p g) (128*(k+m+4)^5*2^min k p):=by
 classical
 let U:=2^min k p
 have G:=vN A hz g (fun _ _=>Fin.elim0) hg (fun _ j=>Fin.elim0 j)
 have F:=jG (A ∪ qY (fun x=>qx (g x))) (Or.inl hz) (Or.inl ht) g
  (fun r j=>Or.inr (Or.inl (Or.inr ⟨r,j,rfl⟩)))
 have GF:=qe G F
 let A1:=A ∪ Set.range (fun j=>fun x=>qh (g x) j)
 have H:=jH A1 (Or.inl hz) (Or.inl ht) g (fun j=>Or.inr ⟨j,rfl⟩)
 let A2:=A1 ∪ (⋃ a:Fin (k+1),Set.range (fun i:Fin (k+1)=>fun x=>decide (i=zV (g x) a)))
 have h0:(fun _=>false)∈A2:=Or.inl (Or.inl hz)
 have h1:(fun _=>true)∈A2:=Or.inl (Or.inl ht)
 have hc (b:Bool):(fun _=>b)∈A2:=by cases b <;> assumption
 have ho (a i:Fin (k+1)):(fun x=>decide (i=zV (g x) a))∈A2:=
  Or.inr (Set.mem_iUnion.mpr ⟨a,⟨i,rfl⟩⟩)
 let total:=fun x=>zV (g x) (Fin.last k)
 have goodB:qa A2 {fun x=>yp p (g x)} ((k+1)*2):=by
  simpa only [total,kt,yp] using
   yr h0 total (fun a _=>decide (a.val≤p)) (ho _) (fun a=>hc _)
 have liveB:qa A2 (Set.range (fun i=>fun x=>yq p (g x) i)) (U*((k+1)*2)):=by
  refine qf _ _ (fun i=>?_)
  simpa only [total,kt,yq] using
   yr h0 total (fun a _=>decide (i.val<2^a.val)) (ho _) (fun a=>hc _)
 have repB:qa A2 {f|∃ i j,(fun x=>z2b (zN p (g x) i j))=f}
  (U*(k*((k+1)*((k+1)*2)+(k+1)*2+1))):=by
  refine qT _ _ (fun i j=>?_)
  let pos:=fun x=>zV (g x) j.castSucc
  let tab:=fun (a:Fin (k+1)) x=>z2b (z5 a.val i.val (pos x).val)
  have hb:=qf tab ((k+1)*2) (fun a=>yr h0 pos
   (fun b _=>z2b (z5 a.val i.val b.val)) (ho _) (fun _=>hc _))
  have hb':=yr (A:=A2 ∪ Set.range tab) (Or.inl h0) total tab
   (fun s=>Or.inl (ho _ s)) (fun s=>Or.inr ⟨s,rfl⟩)
  have hh:=qe hb hb'
  have hf:(fun x=>qh (g x) j)∈A2:=Or.inl (Or.inr ⟨j,rfl⟩)
  have hf':=qe hh (qD (Or.inl hf) (Or.inr rfl))
  have eq:(fun x=>qh (g x) j&&tab (total x) x)=fun x=>z2b (zN p (g x) i j):=by
   funext x
   cases e:qh (g x) j <;> simp [zN,tab,total,e,qm,pos,zV,yc]
  rwa [eq] at hf'
 have Hout:=qr (qr goodB liveB) repB
 have full:=qo (qo (qP GF) (qP H)) Hout
 apply qd full le_rfl Set.subset_union_right
 dsimp only [U]
 obtain ⟨v,hv⟩:=Nat.exists_eq_succ_of_ne_zero (show 2^min k p≠0 by positivity)
 rw [hv,Nat.succ_eq_add_one]
 ring_nf
 omega
end
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
def zm {m t:Nat} (Q:Fin t→qc m):Matrix (Fin t) (Fin m×Fin m) (ZMod 2):=
 fun j ab=>(Q j).B ab.1 ab.2
theorem uQ {N m t:Nat} (Base:Set (Sig N)) (h:Nat)
 (Q0:(Fin N→Bool)→Fin t→qc m)
 (hF:(fun _=>false)∈Base) (hT:(fun _=>true)∈Base)
 (hQ:∀ j,qn (fun x=>Q0 x j)⊆Base):
 qa Base {fun x=>decide ((zm (Q0 x)).rank≤h)}
  ((m*m)*(t*(t+4)+(m*m)*(2*t)+t*(1+(m*m)*10))+t*((t+1)*4)+(t+1)):=by
 classical
 let e:(Fin m×Fin m) ≃ Fin (m*m):=finProdFinEquiv
 let M (x:Fin N→Bool) (j:Fin t) (a:Fin (m*m)):=(Q0 x j).B (e.symm a).1 (e.symm a).2
 let pay (_:Fin t):=(Fin.elim0:Fin 0→ZMod 2)
 let G (x:Fin N→Bool):=qA (M x) pay
 have g:=vN Base hF M (fun _=>pay)
  (fun j a=>hQ j (Or.inl (Or.inl ⟨(e.symm a).1,(e.symm a).2,rfl⟩))) (fun _ p=>p.elim0)
 let B1:=Base ∪ qY G
 let cnt (i:Fin (t+1)):Sig N:=fun x=>zC (G x).used i
 have c:qa B1 (Set.range cnt) (t*((t+1)*4)):=v3 B1 (Or.inl hF) (Or.inl hT)
  (fun x=>(G x).used) (fun j=>Or.inr (Or.inl (Or.inl ⟨j,rfl⟩)))
 let ds:=((List.finRange (t+1)).filter (fun i=>decide (i.val≤h))).map cnt
 have o:=vt (A:=B1 ∪ Set.range cnt) ds (fun f hf=>by
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hf; exact Or.inr ⟨j,rfl⟩) (Or.inl (Or.inl hF))
 have ds_len:ds.length≤t+1:=by
  simp only [ds,List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange
 have sem:(fun x=>ds.any (fun f=>f x))=fun x=>decide ((zm (Q0 x)).rank≤h):=by
  funext x
  let A:=zm (Q0 x)
  have gr:(Finset.univ.filter (fun j=>(G x).used j=true)).card=A.rank:=by
   calc _=Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (M x))):=zw _ pay
        _=(Matrix.of (M x)).rank:=(zl _).symm
        _=A.rank:=Matrix.rank_reindex (Equiv.refl _) e A
  have cs (i:Fin (t+1)):cnt i x=decide (i.val=A.rank):=by
   change zC (G x).used i=_; rw [vh,gr]
  have eh:ds.any (fun f=>f x)=true↔A.rank≤h:=by
   simp only [ds,List.any_map,List.any_eq_true,List.mem_filter,List.mem_finRange,true_and,
    decide_eq_true_eq,Function.comp_apply,cs]
   constructor
   · rintro ⟨i,hi,he⟩; omega
   · intro hh
     have hr:A.rank≤t:=by simpa using A.rank_le_card_height
     exact ⟨⟨A.rank,by omega⟩,hh,rfl⟩
  change ds.any (fun f=>f x)=decide (A.rank≤h)
  by_cases hh:A.rank≤h
  · rw [decide_eq_true hh]; exact eh.mpr hh
  · rw [decide_eq_false hh]; cases hx:ds.any (fun f=>f x) with
    | false=>rfl
    | true=>exact (hh (eh.mp hx)).elim
 rw [sem] at o
 have b:=qe g (qe c o)
 exact qd b le_rfl Set.subset_union_right (by dsimp only [Nat.add_zero]; omega)
theorem yO {N m t:Nat} (k r:Nat) (Base:Set (Sig N)) (h:Nat)
 (Q0:(Fin N→Bool)→Fin t→qc m)
 (hF:(fun _=>false)∈Base) (hT:(fun _=>true)∈Base)
 (hQ:∀ j,qn (fun x=>Q0 x j)⊆Base):
 qa Base {fun x=>decide ((zm (Q0 x)).rank≤h)}
  (2^12*(k+m+r+t+4)^10):=by
 refine qd (uQ Base h Q0 hF hT hQ) le_rfl Set.subset_union_right ?_
 let d:=k+m+r+t
 have hm:m≤d:=by dsimp [d]; omega
 have ht:t≤d:=by dsimp [d]; omega
 change _≤2^12*(d+4)^10
 calc _≤(d*d)*(d*(d+4)+(d*d)*(2*d)+d*(1+(d*d)*10))+d*((d+1)*4)+(d+1):=by gcongr
      _≤_:=by ring_nf; omega
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
def yG {k m t:ℕ} (q:ℕ) (gen:Fin m→Fin k→ZMod 2) (Q0:Fin t→qc m):ℕ:=
 let h:=min q t
 let M0:Fin t→Fin (m * m)→ZMod 2:=fun j idx=>
  let ab:=finProdFinEquiv.symm idx
  (Q0 j).B ab.1 ab.2
 let Pay0:Fin t→Fin (m+1)→ZMod 2:=fun j p=>
  if hp:p.val< m then (Q0 j).l ⟨p.val,hp⟩ else (Q0 j).c
 let gs1:=qA M0 Pay0
 let Q1:Fin t→qc m:=fun j=>
  { B:=fun a b=>gs1.M j (finProdFinEquiv (a,b))
    l:=fun i=>gs1.Pay j i.castSucc
    c:=gs1.Pay j (Fin.last m) }
 let pk:zh m h:=vD gs1.used Q1
 let A0:Fin t→Fin m→ZMod 2:=fun j i=>if gs1.used j then 0 else (Q1 j).l i
 let b0:Fin t→ZMod 2:=fun j=>if gs1.used j then 0 else (Q1 j).c
 let aff:=yt A0 b0 pk.qs
 let consistent:Bool:=(List.finRange t).all (fun r=>aff.affUsed r||!(z2b (aff.b r)))
 let free:Fin m→Bool:=fun i=>!(aff.varElim i)
 let posList:List ℕ:=(List.finRange (2 ^ h)).map (fun σ=>
  q8 (qK free (qg aff.qs (qG h σ.val))))
 let negList:List ℕ:=(List.finRange (2 ^ h)).map (fun σ=>
  q7 (qK free (qg aff.qs (qG h σ.val))))
 let shifted:ℕ:=if consistent then posList.sum-negList.sum else 0
 let gsGen:=qA gen (fun _=>Fin.elim0)
 let rGen:=(Finset.univ.filter (fun j:Fin m=>gsGen.used j=true)).card
 shifted / 2 ^ (h+m-rGen)
def yF {k m t:ℕ} (q:ℕ) (gen:Fin m→Fin k→ZMod 2) (Q0:Fin t→qc m) (o:Fin (k+1)):Bool:=
    let h:=min q t
    let L:=m+h+1
    let gsGen:=qA gen (fun _=>Fin.elim0)
    let rGenOH:=zC gsGen.used
    let M0:Fin t→Fin (m * m)→ZMod 2:=fun j idx=>
     let ab:=finProdFinEquiv.symm idx
     (Q0 j).B ab.1 ab.2
    let Pay0:Fin t→Fin (m+1)→ZMod 2:=fun j p=>
     if hp:p.val< m then (Q0 j).l ⟨p.val,hp⟩ else (Q0 j).c
    let gs1:=qA M0 Pay0
    let Q1:Fin t→qc m:=fun j=>
     { B:=fun a b=>gs1.M j (finProdFinEquiv (a,b))
       l:=fun i=>gs1.Pay j i.castSucc
       c:=gs1.Pay j (Fin.last m) }
    let pk:zh m h:=vD gs1.used Q1
    let A0:Fin t→Fin m→ZMod 2:=fun j i=>if gs1.used j then 0 else (Q1 j).l i
    let b0:Fin t→ZMod 2:=fun j=>if gs1.used j then 0 else (Q1 j).c
    let aff:=yt A0 b0 pk.qs
    let consistent:Bool:=(List.finRange t).all (fun r=>aff.affUsed r||!(z2b (aff.b r)))
    let free:Fin m→Bool:=fun i=>!(aff.varElim i)
    let posSum:ℕ:=((List.finRange (2 ^ h)).map (fun σ=>
     q8 (qK free (qg aff.qs (qG h σ.val))))).sum
    let negSum:ℕ:=((List.finRange (2 ^ h)).map (fun σ=>
     q7 (qK free (qg aff.qs (qG h σ.val))))).sum
    let shifted:ℕ:=if consistent then posSum-negSum else 0
    (List.finRange (m+1)).any (fun r=>
      rGenOH r&&(if _hlt:h+m-r.val+o.val<L then
       shifted.testBit (h+m-r.val+o.val) else false))
set_option maxHeartbeats 4000000 in
theorem kO {k m t:ℕ} (q:ℕ) (gen:Fin m→Fin k→ZMod 2) (Q0:Fin t→qc m):
 let h:=min q t
 let L:=m+h+1
 let gsGen:=qA gen (fun _=>Fin.elim0)
 let rGenOH:=zC gsGen.used
 let M0:Fin t→Fin (m * m)→ZMod 2:=fun j idx=>
  let ab:=finProdFinEquiv.symm idx
  (Q0 j).B ab.1 ab.2
 let Pay0:Fin t→Fin (m+1)→ZMod 2:=fun j p=>
  if hp:p.val< m then (Q0 j).l ⟨p.val,hp⟩ else (Q0 j).c
 let gs1:=qA M0 Pay0
 let Q1:Fin t→qc m:=fun j=>
  { B:=fun a b=>gs1.M j (finProdFinEquiv (a,b))
    l:=fun i=>gs1.Pay j i.castSucc
    c:=gs1.Pay j (Fin.last m) }
 let pk:zh m h:=vD gs1.used Q1
 let A0:Fin t→Fin m→ZMod 2:=fun j i=>if gs1.used j then 0 else (Q1 j).l i
 let b0:Fin t→ZMod 2:=fun j=>if gs1.used j then 0 else (Q1 j).c
 let aff:=yt A0 b0 pk.qs
 let consistent:Bool:=(List.finRange t).all (fun r=>aff.affUsed r||!(z2b (aff.b r)))
 let free:Fin m→Bool:=fun i=>!(aff.varElim i)
 let posSum:ℕ:=((List.finRange (2 ^ h)).map (fun σ=>
  q8 (qK free (qg aff.qs (qG h σ.val))))).sum
 let negSum:ℕ:=((List.finRange (2 ^ h)).map (fun σ=>
  q7 (qK free (qg aff.qs (qG h σ.val))))).sum
 let shifted:ℕ:=if consistent then posSum-negSum else 0
 shifted<2 ^ L→
 ∀ o:Fin (k+1),
   (yG q gen Q0).testBit o.val=
   (List.finRange (m+1)).any (fun r=>
     rGenOH r&&(if _hlt:h+m-r.val+o.val<L then
      shifted.testBit (h+m-r.val+o.val) else false)):=by
 intro h L gsGen rGenOH M0 Pay0 gs1 Q1 pk A0 b0 aff consistent free
  posSum negSum shifted hsh_lt o
 let rGen:=(Finset.univ.filter (fun j:Fin m=>gsGen.used j=true)).card
 have hrGen_le:rGen≤ m:=by
  calc rGen≤(Finset.univ:Finset (Fin m)).card:=Finset.card_le_univ _
   _=m:=Fintype.card_fin m
 have hrOH:∀ r:Fin (m+1),rGenOH r=decide (r.val=rGen):=
  fun r=>congrFun (vh gsGen.used) r
 have hdiv:(yG q gen Q0).testBit o.val=shifted.testBit (h+m-rGen+o.val):=by
  change (shifted / 2 ^ (h+m-rGen)).testBit o.val=shifted.testBit (h+m-rGen+o.val)
  rw [qB,qB,Nat.div_div_eq_div_mul,← Nat.pow_add]
 rw [hdiv]
 let r0:Fin (m+1):=⟨rGen,by omega⟩
 have hany:(List.finRange (m+1)).any (fun r=>
  rGenOH r&&(if hlt:h+m-r.val+o.val<L then shifted.testBit (h+m-r.val+o.val) else false))=
  (if hlt:h+m-rGen+o.val<L then shifted.testBit (h+m-rGen+o.val) else false):=by
  cases hval:(if hlt:h+m-rGen+o.val<L then shifted.testBit (h+m-rGen+o.val) else false)
  · rw [List.any_eq_false]
    intro r _
    by_cases hre:r.val=rGen
    · simp [hrOH r,hre,hval]
    · simp [hrOH r,hre]
  · exact List.any_eq_true.mpr ⟨r0,List.mem_finRange r0,by simp [hrOH r0,r0,hval]⟩
 rw [hany]
 by_cases hlt:h+m-rGen+o.val<L
 · simp [hlt]
 · simp only [hlt,↓reduceDIte]
   have hlt2:shifted<2 ^ (h+m-rGen+o.val):=
    lt_of_lt_of_le hsh_lt (Nat.pow_le_pow_right (by omega) (by omega))
   exact Nat.testBit_lt_two_pow hlt2
set_option maxHeartbeats 4000000 in
theorem kP {k m t:ℕ} (q:ℕ) (base:Fin k→ZMod 2) (gen:Fin m→Fin k→ZMod 2) (Q0:Fin t→qc m)
 (P:(Fin k→ZMod 2)→Fin t→Prop) (hQ0_val:∀ j,(Q0 j).Valid)
 (hEval:∀ j (a:Fin m→ZMod 2),(Q0 j).eval a=0↔P (base+∑ i,a i • gen i) j)
 (hHrank:Matrix.rank (fun j ab=>(Q0 j).B ab.1 ab.2:Matrix (Fin t) (Fin m×Fin m) (ZMod 2))≤q):
 let W:=Fin k→ZMod 2
 let X:=Fin m→ZMod 2
 let key:=fun a:X=>base+∑ i,a i • gen i
 let count:=Nat.card {w:W // w∈Set.range key∧∀ j,P w j}
 yG q gen Q0=count∧
 (let h:=min q t
  let M0:Fin t→Fin (m * m)→ZMod 2:=fun j idx=>(Q0 j).B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
  let Pay0:Fin t→Fin (m+1)→ZMod 2:=fun j p=>if hp:p.val< m then (Q0 j).l ⟨p.val,hp⟩ else (Q0 j).c
  let gs1:=qA M0 Pay0
  let Q1:Fin t→qc m:=fun j=>
   { B:=fun a b=>gs1.M j (finProdFinEquiv (a,b))
     l:=fun i=>gs1.Pay j i.castSucc
     c:=gs1.Pay j (Fin.last m) }
  let pk:zh m h:=vD gs1.used Q1
  let A0:Fin t→Fin m→ZMod 2:=fun j i=>if gs1.used j then 0 else (Q1 j).l i
  let b0:Fin t→ZMod 2:=fun j=>if gs1.used j then 0 else (Q1 j).c
  let aff:=yt A0 b0 pk.qs
  let consistent:Bool:=(List.finRange t).all (fun r=>aff.affUsed r||!(z2b (aff.b r)))
  let free:Fin m→Bool:=fun i=>!(aff.varElim i)
  let posSum:=((List.finRange (2 ^ h)).map (fun σ=>
   q8 (qK free (qg aff.qs (qG h σ.val))))).sum
  let negSum:=((List.finRange (2 ^ h)).map (fun σ=>
   q7 (qK free (qg aff.qs (qG h σ.val))))).sum
  (if consistent then posSum-negSum else 0)<2 ^ (m+h+1)):=by
 classical
 intro W X key count
 let H:Matrix (Fin t) (Fin m×Fin m) (ZMod 2):=fun j ab=>(Q0 j).B ab.1 ab.2
 have hH_eq_B:∀ j a b,H j (a,b)=(Q0 j).B a b:=fun _ _ _=>rfl
 let h:=min q t
 let M0:Fin t→Fin (m * m)→ZMod 2:=fun j idx=>
  (Q0 j).B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
 let Pay0:Fin t→Fin (m+1)→ZMod 2:=fun j p=>
  if hp:p.val< m then (Q0 j).l ⟨p.val,hp⟩ else (Q0 j).c
 let gs1:=qA M0 Pay0
 have hM0_rank:(Finset.univ.filter (fun j:Fin t=>gs1.used j=true)).card≤h:=by
  have hcard_eq:=zw M0 Pay0
  have hfin_eq:Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M0))=H.rank:=by
   let eqv:(Fin m×Fin m→ZMod 2) ≃ₗ[ZMod 2] (Fin (m * m)→ZMod 2):=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finProdFinEquiv.symm
   have hspan_map:Submodule.span (ZMod 2) (Set.range M0)=
    Submodule.map eqv.toLinearMap (Submodule.span (ZMod 2) (Set.range (fun j:Fin t=>H j))):=by
    rw [Submodule.map_span]
    congr 1
    ext row
    constructor
    · rintro ⟨j,rfl⟩
      refine ⟨H j,⟨j,rfl⟩,?_⟩
      funext idx
      simp only [LinearEquiv.coe_coe,eqv,LinearEquiv.funCongrLeft_apply,M0]
      exact hH_eq_B j _ _
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      refine ⟨j,?_⟩
      funext idx
      simp only [LinearEquiv.coe_coe,eqv,LinearEquiv.funCongrLeft_apply,M0]
      exact (hH_eq_B j _ _).symm
   rw [hspan_map,LinearEquiv.finrank_map_eq,← Matrix.rank_transpose]
   change _=Module.finrank (ZMod 2) (LinearMap.range H.transpose.mulVecLin)
   have hsubEq:Submodule.span (ZMod 2) (Set.range (fun j:Fin t=>H j))=
    LinearMap.range H.transpose.mulVecLin:=by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j,rfl⟩
      refine ⟨Pi.single j 1,?_⟩
      funext ab
      simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro r _ hr; simp [Pi.single_eq_of_ne hr]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rintro _ ⟨w,rfl⟩
      have hw:H.transpose.mulVecLin w=∑ j:Fin t,w j • H j:=by
       funext ab
       simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
       exact Finset.sum_congr rfl (fun j _=>mul_comm _ _)
      rw [hw]
      exact Submodule.sum_mem _ (fun j _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩))
   rw [hsubEq]
  have hle_t:(Finset.univ.filter (fun j:Fin t=>gs1.used j=true)).card≤t:=by
   calc _≤(Finset.univ:Finset (Fin t)).card:=Finset.card_le_univ _
    _=t:=Fintype.card_fin t
  have hle_q:(Finset.univ.filter (fun j:Fin t=>gs1.used j=true)).card≤q:=by
   rw [hcard_eq,hfin_eq]; exact hHrank
  exact le_min hle_q hle_t
 let Q1:Fin t→qc m:=fun j=>
  { B:=fun a b=>gs1.M j (finProdFinEquiv (a,b))
    l:=fun i=>gs1.Pay j i.castSucc
    c:=gs1.Pay j (Fin.last m) }
 rcases qv M0 Pay0 with ⟨_,_,hgs1_zero,hgs1_lin,hgs1_prop⟩
 have hQ1_val:∀ j,(Q1 j).Valid:=by
  let PropRow:(Fin (m * m)→ZMod 2)→Prop:=fun row=>
   (∀ i:Fin m,row (finProdFinEquiv (i,i))=0)∧
   (∀ i j:Fin m,row (finProdFinEquiv (i,j))=row (finProdFinEquiv (j,i)))
  have hall:=hgs1_prop PropRow ⟨fun _=>rfl,fun _ _=>rfl⟩
   (fun u v hu hv=>⟨fun i=>by simp [hu.1 i,hv.1 i],fun i j=>by simp [hu.2 i j,hv.2 i j]⟩)
   (fun j=>⟨fun i=>by dsimp only [M0]; rw [Equiv.symm_apply_apply]; exact (hQ0_val j).1 i,
     fun i r=>by dsimp only [M0]; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]; exact (hQ0_val j).2 i r⟩)
  exact fun j=>hall j
 have hQ1_equiv:∀ a:X,(∀ j:Fin t,(Q1 j).eval a=0)↔(∀ j:Fin t,P (key a) j):=by
  intro a
  let mkQ:(Fin (m * m)→ZMod 2)→(Fin (m+1)→ZMod 2)→qc m:=fun row pay=>
   { B:=fun i j=>row (finProdFinEquiv (i,j))
     l:=fun i=>pay i.castSucc
     c:=pay (Fin.last m) }
  let evalMP:(Fin (m * m)→ZMod 2)→(Fin (m+1)→ZMod 2)→ZMod 2:=fun row pay=>
   (mkQ row pay).eval a
  have hadd:∀ m1 m2 p1 p2,evalMP (m1+m2) (p1+p2)=evalMP m1 p1+evalMP m2 p2:=
   fun m1 m2 p1 p2=>qc.jV (mkQ m1 p1) (mkQ m2 p2) a
  have heq0:∀ j,evalMP (M0 j) (Pay0 j)=(Q0 j).eval a:=by
   intro j
   change ({ B:=fun i r=>(Q0 j).B (finProdFinEquiv.symm (finProdFinEquiv (i,r))).1
              (finProdFinEquiv.symm (finProdFinEquiv (i,r))).2
             l:=fun i=>if hi:i.castSucc.val< m then (Q0 j).l ⟨i.castSucc.val,hi⟩ else (Q0 j).c
             c:=if hc:(Fin.last m).val< m then (Q0 j).l ⟨(Fin.last m).val,hc⟩ else (Q0 j).c }:qc m).eval a=_
   congr 1
   cases hq:Q0 j with
   | mk B l c=>
     congr 1
     · funext i r; simp
     · funext i; simp [i.isLt]
     · simp
  have hiff:=hgs1_lin (ZMod 2) evalMP hadd
  constructor
  · intro h1 j
    have h0:(Q0 j).eval a=0:=by rw [← heq0 j]; exact hiff.mp h1 j
    exact (hEval j a).mp h0
  · intro h1
    apply hiff.mpr
    intro j
    rw [heq0 j]; exact (hEval j a).mpr (h1 j)
 let pk:zh m h:=vD gs1.used Q1
 rcases ja gs1.used Q1 hQ1_val hM0_rank with ⟨hpk_val,hpk_equiv⟩
 let A0:Fin t→Fin m→ZMod 2:=fun j i=>if gs1.used j then 0 else (Q1 j).l i
 let b0:Fin t→ZMod 2:=fun j=>if gs1.used j then 0 else (Q1 j).c
 have hQ1_unused:∀ j a,gs1.used j=false→
  (Q1 j).eval a=b0 j+∑ i:Fin m,A0 j i * a i:=by
  intro j a hj
  have hB0:∀ r s:Fin m,(Q1 j).B r s=0:=fun r s=>hgs1_zero j hj (finProdFinEquiv (r,s))
  simp [qc.eval,hB0,A0,b0,hj]
 let aff:=yt A0 b0 pk.qs
 let consistent:Bool:=(List.finRange t).all (fun r=>aff.affUsed r||!(z2b (aff.b r)))
 let free:Fin m→Bool:=fun i=>!(aff.varElim i)
 rcases kg A0 b0 pk.qs hpk_val with ⟨haff_val,haff_supp,haff_card⟩
 let SolA:Finset X:=Finset.univ.filter (fun a:X=>∀ j:Fin t,P (key a) j)
 have hSolA_eq:SolA.card=
  if consistent then
   (Finset.univ.filter (fun a:X=>
     (∀ u:Fin m,aff.varElim u=true→a u=0)∧
     (∀ s:Fin h,(aff.qs s).eval a=0))).card
  else 0:=by
  rw [← haff_card]
  congr 1
  ext a
  simp only [SolA,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← hQ1_equiv a,← hpk_equiv a]
  constructor
  · intro hall
    refine ⟨fun j=>?_,fun j _=>hall j⟩
    cases hu:gs1.used j
    · rw [← hQ1_unused j a hu]; exact hall j
    · simp [A0,b0,hu]
  · rintro ⟨haff0,hused0⟩ j
    cases hu:gs1.used j
    · rw [hQ1_unused j a hu]; exact haff0 j
    · exact hused0 j hu
 let Nfree:ℕ:=(Finset.univ.filter (fun a:X=>
  (∀ u:Fin m,aff.varElim u=true→a u=0)∧
  (∀ s:Fin h,(aff.qs s).eval a=0))).card
 let posSum:ℕ:=((List.finRange (2 ^ h)).map (fun σ=>
  q8 (qK free (qg aff.qs (qG h σ.val))))).sum
 let negSum:ℕ:=((List.finRange (2 ^ h)).map (fun σ=>
  q7 (qK free (qg aff.qs (qG h σ.val))))).sum
 have hpos_neg_eq:(posSum:ℤ)-(negSum:ℤ)=(2 ^ h * Nfree:ℕ):=by
  have hsum_cast:∀ (F:Fin (2 ^ h)→ℕ),
   (((List.finRange (2 ^ h)).map F).sum:ℤ)=∑ σ:Fin (2 ^ h),(F σ:ℤ):=by
   intro F
   rw [← Fin.sum_univ_def,Nat.cast_sum]
  rw [hsum_cast,hsum_cast,← Finset.sum_sub_distrib]
  have hterm:∀ σ:Fin (2 ^ h),
   (q8 (qK free (qg aff.qs (qG h σ.val))):ℤ) -
   (q7 (qK free (qg aff.qs (qG h σ.val))):ℤ)=
   ∑ a∈z4 free,qz ((qg aff.qs (qG h σ.val)).eval a):=by
   intro σ
   rw [kC]
   have hsupp':∀ s u,free u=false→(aff.qs s).l u=0∧∀ w,(aff.qs s).B u w=0:=by
    intro s u hu
    have hve:aff.varElim u=true:=by simp only [free,Bool.not_eq_false'] at hu; exact hu
    exact haff_supp s u hve
   exact (vG free _ (vv aff.qs haff_val _)
    (vF aff.qs free hsupp' _)).2
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner:∀ a∈z4 free,
   ∑ σ:Fin (2 ^ h),qz ((qg aff.qs (qG h σ.val)).eval a)=
   if (∀ s:Fin h,(aff.qs s).eval a=0) then (2:ℤ) ^ h else 0:=by
   intro a _
   simp_rw [ka]
   let eqv:=Equiv.ofBijective _ (yM h)
   have heqv_sum:∑ σ:Fin (2 ^ h),qz (∑ s:Fin h,qG h σ.val s * (aff.qs s).eval a)=
    ∑ τ:Fin h→ZMod 2,qz (∑ s:Fin h,τ s * (aff.qs s).eval a):=
    Fintype.sum_equiv eqv _ _ (fun _=>rfl)
   rw [heqv_sum]
   exact kB h (fun s=>(aff.qs s).eval a)
  rw [Finset.sum_congr rfl hinner,Finset.sum_ite,Finset.sum_const_zero,add_zero,
   Finset.sum_const,nsmul_eq_mul]
  have hcard_eq:(Finset.filter (fun a=>∀ s:Fin h,(aff.qs s).eval a=0) (z4 free)).card=Nfree:=by
   congr 1
   ext a
   simp only [z4,Finset.mem_filter,Finset.mem_univ,true_and,free,Bool.not_eq_false']
  rw [hcard_eq]
  push_cast
  ring
 have hsub_nat:posSum-negSum=2 ^ h * Nfree:=by omega
 have hshifted_eq:(if consistent then posSum-negSum else 0)=2 ^ h * SolA.card:=by
  rw [hSolA_eq,hsub_nat]
  change (if consistent then 2 ^ h * Nfree else 0)=2 ^ h * (if consistent then Nfree else 0)
  cases consistent <;> simp
 let Llin:(Fin m→ZMod 2) →ₗ[ZMod 2] (Fin k→ZMod 2):=
  { toFun:=fun a=>∑ j:Fin m,a j • gen j
    map_add':=fun a b=>by
     funext p
     simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
      Finset.sum_add_distrib]
    map_smul':=fun c a=>by
     funext p
     simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
     exact Finset.sum_congr rfl (fun j _=>by ring) }
 have hrange_L:LinearMap.range Llin=Submodule.span (ZMod 2) (Set.range gen):=by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    change ∑ j:Fin m,a j • gen j∈Submodule.span (ZMod 2) (Set.range gen)
    exact Submodule.sum_mem _ (fun j _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j,rfl⟩
    refine ⟨(Pi.single j (1:ZMod 2):Fin m→ZMod 2),?_⟩
    change ∑ r:Fin m,((Pi.single j (1:ZMod 2):Fin m→ZMod 2) r) • gen r=gen j
    rw [Finset.sum_eq_single j]
    · simp
    · intro r _ hr; simp [Pi.single_eq_of_ne hr]
    · intro h'; exact absurd (Finset.mem_univ _) h'
 let gsGen:=qA gen (fun _=>Fin.elim0)
 let rGen:=(Finset.univ.filter (fun j:Fin m=>gsGen.used j=true)).card
 have hrGen_eq:rGen=Module.finrank (ZMod 2) (LinearMap.range Llin):=by
  rw [hrange_L]
  exact zw gen (fun _=>Fin.elim0)
 have hrk_null:=LinearMap.finrank_range_add_finrank_ker Llin
 rw [Module.finrank_fin_fun (ZMod 2)] at hrk_null
 have hker_dim:Module.finrank (ZMod 2) (LinearMap.ker Llin)=m-rGen:=by omega
 have hker_card:Fintype.card (LinearMap.ker Llin)=2 ^ (m-rGen):=by
  rw [vn,hker_dim]
 let SolW:Finset W:=Finset.univ.filter (fun w:W=>w∈Set.range key∧∀ j,P w j)
 have hcount_eq:count=SolW.card:=by
  simp only [count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl
 have hSolA_fiber:SolA.card=SolW.card * 2 ^ (m-rGen):=by
  have hmaps:∀ a∈SolA,key a∈SolW:=by
   intro a ha
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨a,rfl⟩,(Finset.mem_filter.mp ha).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib:∀ w∈SolW,(SolA.filter (fun a=>key a=w)).card=2 ^ (m-rGen):=by
   intro w hw
   rcases (Finset.mem_filter.mp hw).2 with ⟨⟨a0,ha0⟩,hprob⟩
   rw [← hker_card,← Finset.card_univ]
   refine Finset.card_bij (fun a ha=>(⟨a-a0,?_⟩:LinearMap.ker Llin)) ?_ ?_ ?_
   · have hka:key a=w:=(Finset.mem_filter.mp ha).2
     simp only [LinearMap.mem_ker,map_sub]
     have h1:Llin a=Llin a0:=by
      have:base+Llin a=base+Llin a0:=by change key a=key a0; rw [hka,ha0]
      exact add_left_cancel this
     exact sub_eq_zero.mpr h1
   · intro _ _; exact Finset.mem_univ _
   · intro a1 _ a2 _ heq
     have h1:a1-a0=a2-a0:=congrArg Subtype.val heq
     exact sub_left_inj.mp h1
   · rintro ⟨d,hd⟩ _
     refine ⟨a0+d,?_,?_⟩
     · have hkd:key (a0+d)=w:=by
        change base+Llin (a0+d)=w
        rw [map_add,LinearMap.mem_ker.mp hd,add_zero]
        exact ha0
       refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j=>?_⟩,hkd⟩
       rw [hkd]; exact hprob j
     · apply Subtype.ext; simp
  rw [Finset.sum_congr rfl hfib,Finset.sum_const,smul_eq_mul]
 have hSolW_le:SolW.card≤2 ^ rGen:=by
  have hsub:SolW⊆Finset.univ.image key:=by
   intro w hw
   rcases (Finset.mem_filter.mp hw).2.1 with ⟨a,rfl⟩
   exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have himg_card:(Finset.univ.image key).card=2 ^ rGen:=by
   have hbij:(Finset.univ.image key).card=Fintype.card (LinearMap.range Llin):=by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun w hw=>(⟨w-base,?_⟩:LinearMap.range Llin)) ?_ ?_ ?_
    · rcases Finset.mem_image.mp hw with ⟨a,_,rfl⟩
      exact ⟨a,by change Llin a=base+Llin a-base; ring⟩
    · intro _ _; exact Finset.mem_univ _
    · intro w1 _ w2 _ heq
      exact sub_left_inj.mp (congrArg Subtype.val heq)
    · rintro ⟨y,a,rfl⟩ _
      exact ⟨key a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,
       Subtype.ext (by change base+Llin a-base=Llin a; ring)⟩
   rw [hbij,vn,← hrGen_eq]
  calc SolW.card≤(Finset.univ.image key).card:=Finset.card_le_card hsub
   _=2 ^ rGen:=himg_card
 have hrGen_le_m:rGen≤ m:=by omega
 have hshifted_final:(if consistent then posSum-negSum else 0)=
  count * 2 ^ (h+m-rGen):=by
  rw [hshifted_eq,hSolA_fiber,hcount_eq]
  have hpow:2 ^ h * (SolW.card * 2 ^ (m-rGen))=SolW.card * (2 ^ h * 2 ^ (m-rGen)):=by ring
  rw [hpow,← Nat.pow_add,show h+(m-rGen)=h+m-rGen by omega]
 have hshifted_lt:(if consistent then posSum-negSum else 0)<2 ^ (m+h+1):=by
  rw [hshifted_final,hcount_eq]
  calc
   SolW.card * 2 ^ (h+m-rGen)≤2 ^ rGen * 2 ^ (h+m-rGen):=
    Nat.mul_le_mul_right _ hSolW_le
   _=2 ^ (rGen+(h+m-rGen)):=(Nat.pow_add 2 _ _).symm
   _=2 ^ (m+h):=by congr 1; omega
   _<2 ^ (m+h+1):=Nat.pow_lt_pow_right (by omega) (by omega)
 refine ⟨?_,hshifted_lt⟩
 have halgo_eq:yG q gen Q0=(if consistent then posSum-negSum else 0) / 2 ^ (h+m-rGen):=by
  rfl
 rw [halgo_eq,hshifted_final,Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
set_option maxHeartbeats 4000000 in
theorem k6 {k m t:ℕ} (q:ℕ) (base:Fin k→ZMod 2) (gen:Fin m→Fin k→ZMod 2) (Q0:Fin t→qc m)
 (P:(Fin k→ZMod 2)→Fin t→Prop) (hQ0_val:∀ j,(Q0 j).Valid)
 (hEval:∀ j (a:Fin m→ZMod 2),(Q0 j).eval a=0↔P (base+∑ i,a i • gen i) j)
 (hHrank:Matrix.rank (fun j ab=>(Q0 j).B ab.1 ab.2:Matrix (Fin t) (Fin m×Fin m) (ZMod 2))≤q) (o:Fin (k+1)):
 yF q gen Q0 o=(Nat.card {w:Fin k→ZMod 2 // w∈Set.range (fun a:Fin m→ZMod 2=>base+∑ i,a i • gen i)∧∀ j,P w j}).testBit o.val:=by
 obtain ⟨hCount,hBound⟩:=kP q base gen Q0 P hQ0_val hEval hHrank
 rw [← hCount]
 exact (kO q gen Q0 hBound o).symm
set_option maxHeartbeats 4000000 in
theorem jj {inputs k m t:ℕ} (q:ℕ) (Base:Set (Sig inputs))
 (gen:(Fin inputs→Bool)→Fin m→Fin k→ZMod 2) (Q0:(Fin inputs→Bool)→Fin t→qc m)
 (hF:(fun _=>false)∈Base) (hT:(fun _=>true)∈Base)
 (hGen:∀ i j,(fun x=>z2b (gen x i j))∈Base)
 (hQ:∀ j,qn (fun x=>Q0 x j)⊆Base) (hValid:∀ x j,(Q0 x j).Valid):
 qa Base (Set.range (fun o x=>yF q (gen x) (Q0 x) o))
  (2 ^ 20 * (k+m+t+2)^8 * 2 ^ (min q t)):=by
 let h:=min q t
 let L:=m+h+1
 let gsGen:=fun x=>qA (gen x) (fun _=>Fin.elim0)
 let rGenOH:=fun x=>zC (gsGen x).used
 let M0:=fun x j idx=>(Q0 x j).B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
 let Pay0:=fun x j (p:Fin (m+1))=>if hp:p.val< m then (Q0 x j).l ⟨p.val,hp⟩ else (Q0 x j).c
 let gs1:=fun x=>qA (M0 x) (Pay0 x)
 let Q1:=fun x j=>
  ({ B:=fun a b=>(gs1 x).M j (finProdFinEquiv (a,b))
     l:=fun i=>(gs1 x).Pay j i.castSucc
     c:=(gs1 x).Pay j (Fin.last m) }:qc m)
 let pk:(Fin inputs→Bool)→zh m h:=fun x=>vD (gs1 x).used (Q1 x)
 let A0:=fun x j i=>if (gs1 x).used j then 0 else (Q1 x j).l i
 let b0:=fun x j=>if (gs1 x).used j then 0 else (Q1 x j).c
 let aff:=fun x=>yt (A0 x) (b0 x) (pk x).qs
 let consistent:=fun x=>(List.finRange t).all (fun r=>(aff x).affUsed r||!(z2b ((aff x).b r)))
 let free:=fun x i=>!((aff x).varElim i)
 let posSum:=fun x=>((List.finRange (2 ^ h)).map (fun σ=>
  q8 (qK (free x) (qg (aff x).qs (qG h σ.val))))).sum
 let negSum:=fun x=>((List.finRange (2 ^ h)).map (fun σ=>
  q7 (qK (free x) (qg (aff x).qs (qG h σ.val))))).sum
 let shifted:=fun x=>if consistent x then posSum x-negSum x else 0
 let outSig:Fin (k+1)→Sig inputs:=fun o x=>
  (List.finRange (m+1)).any (fun r=>
    rGenOH x r&&(if _hlt:h+m-r.val+o.val<L then
     (shifted x).testBit (h+m-r.val+o.val) else false))
 let B0:=Base
 have hF0:(fun _=>false)∈B0:=hF
 have hT0:(fun _=>true)∈B0:=hT
 have hS0:qa B0 (⋃ j:Fin t,qn (fun x=>Q0 x j))
  (t * (160+m * 40+(m * (m * 10)+m * 15+5))):=
  qd (zk (Set.iUnion_subset hQ)) le_rfl Set.subset_union_right (Nat.zero_le _)
 let B1:=B0 ∪ ⋃ j:Fin t,qn (fun x=>Q0 x j)
 have hF1:(fun _=>false)∈B1:=Or.inl hF0
 have hT1:(fun _=>true)∈B1:=Or.inl hT0
 have hS1:qa B1 (qY gs1)
  ((m * m) * (t * (t+4)+(m * m+(m+1)) * (2 * t)+t * (1+(m * m+(m+1)) * 10))):=
  vN B1 hF1 M0 Pay0
   (fun j idx=>Or.inr (Set.mem_iUnion.mpr ⟨j,Or.inl (Or.inl ⟨(finProdFinEquiv.symm idx).1,
     (finProdFinEquiv.symm idx).2,rfl⟩)⟩))
   (fun j p=>by
     by_cases hp:p.val< m
     · have heq:(fun x=>z2b (Pay0 x j p))=fun x=>z2b ((Q0 x j).l ⟨p.val,hp⟩):=by
        funext x; simp [Pay0,hp]
       rw [heq]; exact Or.inr (Set.mem_iUnion.mpr ⟨j,Or.inl (Or.inr ⟨⟨p.val,hp⟩,rfl⟩)⟩)
     · have heq:(fun x=>z2b (Pay0 x j p))=fun x=>z2b (Q0 x j).c:=by
        funext x; simp [Pay0,hp]
       rw [heq]; exact Or.inr (Set.mem_iUnion.mpr ⟨j,Or.inr rfl⟩))
 let B2:=B1 ∪ qY gs1
 have hF2:(fun _=>false)∈B2:=Or.inl hF1
 have hT2:(fun _=>true)∈B2:=Or.inl hT1
 have hPack:qa B2 (zG pk)
  (t * ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4)))):=
  jN B2 hF2 hT2 (fun x=>(gs1 x).used) Q1
   (fun j=>Or.inr (Or.inl (Or.inl ⟨j,rfl⟩)))
   (fun j=>by
     rintro f ((⟨a,b,rfl⟩|⟨i,rfl⟩)|rfl)
     · exact Or.inr (Or.inl (Or.inr ⟨j,finProdFinEquiv (a,b),rfl⟩))
     · exact Or.inr (Or.inr ⟨j,i.castSucc,rfl⟩)
     · exact Or.inr (Or.inr ⟨j,Fin.last m,rfl⟩))
 have hA0B:qa B2 {f|∃ j i,(fun x=>z2b (A0 x j i))=f} (t * (m * 2)):=
  qT _ 2 (fun j i=>by
   have hn:qa B2 {fun x=>!((gs1 x).used j)} 1:=zn (Or.inr (Or.inl (Or.inl ⟨j,rfl⟩)))
   have ha:qa (B2 ∪ {fun x=>!((gs1 x).used j)}) {fun x=>z2b (A0 x j i)} 1:=by
    have heq:(fun x=>z2b (A0 x j i))=fun x=>!((gs1 x).used j)&&z2b ((gs1 x).Pay j i.castSucc):=by
     funext x; simp only [A0,Q1]; cases (gs1 x).used j <;> simp [qm]
    rw [heq]
    exact qD (Or.inr rfl) (Or.inl (Or.inr (Or.inr ⟨j,i.castSucc,rfl⟩)))
   exact qe hn ha)
 have hb0B:qa B2 (Set.range (fun j:Fin t=>fun x=>z2b (b0 x j))) (t * 2):=
  qf _ 2 (fun j=>by
   have hn:qa B2 {fun x=>!((gs1 x).used j)} 1:=zn (Or.inr (Or.inl (Or.inl ⟨j,rfl⟩)))
   have ha:qa (B2 ∪ {fun x=>!((gs1 x).used j)}) {fun x=>z2b (b0 x j)} 1:=by
    have heq:(fun x=>z2b (b0 x j))=fun x=>!((gs1 x).used j)&&z2b ((gs1 x).Pay j (Fin.last m)):=by
     funext x; simp only [b0,Q1]; cases (gs1 x).used j <;> simp [qm]
    rw [heq]
    exact qD (Or.inr rfl) (Or.inl (Or.inr (Or.inr ⟨j,Fin.last m,rfl⟩)))
   exact qe hn ha)
 have hS1b:=qr (qr hPack hA0B) hb0B
 let B3:=B2 ∪ ((zG pk ∪ {f|∃ j i,(fun x=>z2b (A0 x j i))=f}) ∪
  Set.range (fun j:Fin t=>fun x=>z2b (b0 x j)))
 have hF3:(fun _=>false)∈B3:=Or.inl hF2
 have hT3:(fun _=>true)∈B3:=Or.inl hT2
 have hS2:qa B3 (zT aff)
  (m * (t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
    h * (m * (m * 14)+m * 19+9))):=
  jT B3 hF3 A0 b0 (fun x=>(pk x).qs)
   (fun j i=>Or.inr (Or.inl (Or.inr ⟨j,i,rfl⟩)))
   (fun j=>Or.inr (Or.inr ⟨j,rfl⟩))
   (fun s=>Set.subset_iUnion (fun s=>qn (fun x=>(pk x).qs s)) s |>.trans
     (Set.subset_union_right.trans (Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_right))))
 let B4:=B3 ∪ zT aff
 have hF4:(fun _=>false)∈B4:=Or.inl hF3
 have hT4:(fun _=>true)∈B4:=Or.inl hT3
 have hConsB:qa B4 {consistent} (t * 2+t):=by
  let term:Fin t→Sig inputs:=fun r x=>(aff x).affUsed r||!(z2b ((aff x).b r))
  have htB:qa B4 (Set.range term) (t * 2):=
   qf term 2 (fun r=>by
    have hn:qa B4 {fun x=>!(z2b ((aff x).b r))} 1:=
     zn (Or.inr (Or.inl (Or.inl (Or.inr ⟨r,rfl⟩))))
    have ho:qa (B4 ∪ {fun x=>!(z2b ((aff x).b r))}) {term r} 1:=
     orB (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r,rfl⟩)))))) (Or.inr rfl)
    exact qe hn ho)
  have hallB:qa (B4 ∪ Set.range term) {consistent} t:=by
   have h:=kK (A:=B4 ∪ Set.range term) ((List.finRange t).map term)
    (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr ⟨r,rfl⟩)
    (Or.inl hT4)
   have heq:(fun x=>((List.finRange t).map term).all (fun f=>f x))=consistent:=by
    funext x; simp [consistent,term,List.all_map]; rfl
   rw [heq,List.length_map,List.length_finRange] at h
   exact h
  exact qe htB hallB
 have hFreeB:qa B4 (Set.range (fun i:Fin m=>fun x=>free x i)) (m * 1):=
  qf _ 1 (fun i=>zn (Or.inr (Or.inl (Or.inr ⟨i,rfl⟩))))
 have hS2b:=qr hConsB hFreeB
 let B5:=B4 ∪ ({consistent} ∪ Set.range (fun i:Fin m=>fun x=>free x i))
 have hF5:(fun _=>false)∈B5:=Or.inl hF4
 have hT5:(fun _=>true)∈B5:=Or.inl hT4
 let posF:Fin (2 ^ h)→(Fin inputs→Bool)→ℕ:=fun σ x=>
  q8 (qK (free x) (qg (aff x).qs (qG h σ.val)))
 let negF:Fin (2 ^ h)→(Fin inputs→Bool)→ℕ:=fun σ x=>
  q7 (qK (free x) (qg (aff x).qs (qG h σ.val)))
 let cSigma:ℕ:=(m * (m * (4 * h))+m * (4 * h)+4 * h) +
  m * (m * (m+7)+(m+1) * (2 * m)+(m * (m * 26)+m * 60+40))+(4+L * 2)
 have hOneSigma:∀ σ:Fin (2 ^ h),
  qa B5 (Set.range (qk L (posF σ)) ∪ Set.range (qk L (negF σ))) cSigma:=by
  intro σ
  have hcomb:qa B5 (qn (fun x=>qg (aff x).qs (qG h σ.val)))
   (m * (m * (4 * h))+m * (4 * h)+4 * h):=
   u6 B5 hF5 (fun x=>(aff x).qs)
    (fun s=>Set.subset_iUnion (fun s=>qn (fun x=>(aff x).qs s)) s |>.trans
      (Set.subset_union_right.trans (Set.subset_union_right.trans Set.subset_union_left)))
    (qG h σ.val)
  have hgs:qa (B5 ∪ qn (fun x=>qg (aff x).qs (qG h σ.val)))
   (vd (fun x=>qK (free x) (qg (aff x).qs (qG h σ.val))))
   (m * (m * (m+7)+(m+1) * (2 * m)+(m * (m * 26)+m * 60+40))):=
   u7 _ (Or.inl hF5) (Or.inl hT5) free
    (fun x=>qg (aff x).qs (qG h σ.val))
    (fun u=>Or.inl (Or.inr (Or.inr ⟨u,rfl⟩)))
    Set.subset_union_right
  let stσ:(Fin inputs→Bool)→zL m:=
   fun x=>qK (free x) (qg (aff x).qs (qG h σ.val))
  have hst_pow:∀ x,∃ e≤ m,(stσ x).pow2=fun k:Fin (m+1)=>decide (k.val=e):=by
   intro x
   have hQ1v:∀ j,(Q1 x j).Valid:=by
    let PropRow:(Fin (m * m)→ZMod 2)→Prop:=fun row=>
     (∀ i:Fin m,row (finProdFinEquiv (i,i))=0)∧
     (∀ i j:Fin m,row (finProdFinEquiv (i,j))=row (finProdFinEquiv (j,i)))
    exact (qv (M0 x) (Pay0 x)).2.2.2.2 PropRow ⟨fun _=>rfl,fun _ _=>rfl⟩
     (fun u v hu hv=>⟨fun i=>by simp [hu.1 i,hv.1 i],fun i j=>by simp [hu.2 i j,hv.2 i j]⟩)
     (fun j=>⟨fun i=>by dsimp only [M0]; rw [Equiv.symm_apply_apply]; exact (hValid x j).1 i,
       fun i r=>by dsimp only [M0]; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]; exact (hValid x j).2 i r⟩)
   have haff_sp:=kg (A0 x) (b0 x) (pk x).qs (kG (gs1 x).used (Q1 x) hQ1v)
   have hsupp':∀ s u,free x u=false→((aff x).qs s).l u=0∧∀ w,((aff x).qs s).B u w=0:=by
    intro s u hu
    have hve:(aff x).varElim u=true:=by simp only [free,Bool.not_eq_false'] at hu; exact hu
    exact haff_sp.2.1 s u hve
   exact (vG (free x) _ (vv (aff x).qs haff_sp.1 _)
    (vF (aff x).qs (free x) hsupp' _)).1
  let Aσ:=(B5 ∪ qn (fun x=>qg (aff x).qs (qG h σ.val))) ∪ vd stσ
  let nZero:Sig inputs:=fun x=>!((stσ x).zero)
  let nC:Sig inputs:=fun x=>!(z2b (stσ x).Q.c)
  let posEn:Sig inputs:=fun x=>nZero x&&nC x
  let negEn:Sig inputs:=fun x=>nZero x&&z2b (stσ x).Q.c
  have henB:qa Aσ ({posEn} ∪ {negEn}) 4:=by
   have h1:qa Aσ {nZero} 1:=zn (Or.inr (Or.inl (Or.inr rfl)))
   have h2:qa (Aσ ∪ {nZero}) {nC} 1:=
    zn (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))
   have h3:qa ((Aσ ∪ {nZero}) ∪ {nC}) {posEn} 1:=
    qD (Or.inl (Or.inr rfl)) (Or.inr rfl)
   have h4:qa (((Aσ ∪ {nZero}) ∪ {nC}) ∪ {posEn}) {negEn} 1:=
    qD (Or.inl (Or.inl (Or.inr rfl)))
     (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))))
   exact qd (qo (qo (qP h1) (qP h2)) (zd h3 h4)) le_rfl Set.subset_union_right (by omega)
  let Aσ2:=Aσ ∪ ({posEn} ∪ {negEn})
  have hposBits:qa Aσ2 (Set.range (qk L (posF σ))) (L * 1):=by
   refine qf _ 1 (fun j=>?_)
   by_cases hj:j.val< m+1
   · have heq:qk L (posF σ) j=fun x=>posEn x&&(stσ x).pow2 ⟨j.val,hj⟩:=by
      funext x
      rcases hst_pow x with ⟨e,he,hpow⟩
      change (q8 (stσ x)).testBit j.val=(posEn x&&(stσ x).pow2 ⟨j.val,hj⟩)
      simp only [q8,posEn,nZero,nC]
      cases hcond:!(stσ x).zero&&!(z2b (stσ x).Q.c)
      · simp
      · simp only [↓reduceIte,Bool.true_and,hpow,vH he,hj]
     rw [heq]
     exact qD (Or.inr (Or.inl rfl)) (Or.inl (Or.inr (Or.inr ⟨⟨j.val,hj⟩,rfl⟩)))
   · have heq:qk L (posF σ) j=fun _=>false:=by
      funext x
      rcases hst_pow x with ⟨e,he,hpow⟩
      change (q8 (stσ x)).testBit j.val=false
      simp only [q8]
      cases !(stσ x).zero&&!(z2b (stσ x).Q.c)
      · simp
      · simp only [↓reduceIte,hpow,vH he,hj]
     rw [heq]
     exact qd (zk (A:=Aσ2) (B:={fun _=>false})
      (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl hF5))))) le_rfl Set.subset_union_right (by omega)
  have hnegBits:qa Aσ2 (Set.range (qk L (negF σ))) (L * 1):=by
   refine qf _ 1 (fun j=>?_)
   by_cases hj:j.val< m+1
   · have heq:qk L (negF σ) j=fun x=>negEn x&&(stσ x).pow2 ⟨j.val,hj⟩:=by
      funext x
      rcases hst_pow x with ⟨e,he,hpow⟩
      change (q7 (stσ x)).testBit j.val=(negEn x&&(stσ x).pow2 ⟨j.val,hj⟩)
      simp only [q7,negEn,nZero]
      cases hcond:!(stσ x).zero&&z2b (stσ x).Q.c
      · simp
      · simp only [↓reduceIte,Bool.true_and,hpow,vH he,hj]
     rw [heq]
     exact qD (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨⟨j.val,hj⟩,rfl⟩)))
   · have heq:qk L (negF σ) j=fun _=>false:=by
      funext x
      rcases hst_pow x with ⟨e,he,hpow⟩
      change (q7 (stσ x)).testBit j.val=false
      simp only [q7]
      cases !(stσ x).zero&&z2b (stσ x).Q.c
      · simp
      · simp only [↓reduceIte,hpow,vH he,hj]
     rw [heq]
     exact qd (zk (A:=Aσ2) (B:={fun _=>false})
      (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl hF5))))) le_rfl Set.subset_union_right (by omega)
  exact qd (qo (qo (qo (qP hcomb) (qP hgs)) (qP henB)) (qr hposBits hnegBits))
   le_rfl Set.subset_union_right (by omega)
 have hAllSig:qa B5
  (⋃ σ:Fin (2 ^ h),Set.range (qk L (posF σ)) ∪ Set.range (qk L (negF σ)))
  (2 ^ h * cSigma):=
  v7 _ cSigma hOneSigma
 let B6:=B5 ∪ ⋃ σ:Fin (2 ^ h),Set.range (qk L (posF σ)) ∪ Set.range (qk L (negF σ))
 have hF6:(fun _=>false)∈B6:=Or.inl hF5
 have hT6:(fun _=>true)∈B6:=Or.inl hT5
 have hsumList_eq:∀ (Fs:Fin (2 ^ h)→(Fin inputs→Bool)→ℕ) (x:Fin inputs→Bool),
  q6 ((List.finRange (2 ^ h)).map Fs) x=
  ((List.finRange (2 ^ h)).map (fun σ=>Fs σ x)).sum:=by
  intro Fs x
  have hgen:∀ (l:List (Fin (2 ^ h))),
   q6 (l.map Fs) x=(l.map (fun σ=>Fs σ x)).sum:=by
   intro l
   induction l with
   | nil=>rfl
   | cons a l ih=>simp [q6,ih]
  exact hgen (List.finRange (2 ^ h))
 have hPosSumB:qa B6 (Set.range (qk L posSum)) (2 ^ h * (9 * L)):=by
  have h1:=uA (A:=B6) L hF6 ((List.finRange (2 ^ h)).map posF)
   (fun F hF j=>by
     rcases List.mem_map.mp hF with ⟨σ,_,rfl⟩
     exact Or.inr (Set.mem_iUnion.mpr ⟨σ,Or.inl ⟨j,rfl⟩⟩))
  have heq:q6 ((List.finRange (2 ^ h)).map posF)=posSum:=
   funext (hsumList_eq posF)
  rw [heq,List.length_map,List.length_finRange] at h1
  exact h1
 have hNegSumB:qa B6 (Set.range (qk L negSum)) (2 ^ h * (9 * L)):=by
  have h1:=uA (A:=B6) L hF6 ((List.finRange (2 ^ h)).map negF)
   (fun F hF j=>by
     rcases List.mem_map.mp hF with ⟨σ,_,rfl⟩
     exact Or.inr (Set.mem_iUnion.mpr ⟨σ,Or.inr ⟨j,rfl⟩⟩))
  have heq:q6 ((List.finRange (2 ^ h)).map negF)=negSum:=
   funext (hsumList_eq negF)
  rw [heq,List.length_map,List.length_finRange] at h1
  exact h1
 have hSumsB:=qr hPosSumB hNegSumB
 let B7:=B6 ∪ (Set.range (qk L posSum) ∪ Set.range (qk L negSum))
 have hF7:(fun _=>false)∈B7:=Or.inl hF6
 have hT7:(fun _=>true)∈B7:=Or.inl hT6
 have hvalidSub:∀ x,negSum x≤posSum x∧negSum x<2 ^ L:=by
  intro x
  have hQ1v:∀ j,(Q1 x j).Valid:=by
   let PropRow:(Fin (m * m)→ZMod 2)→Prop:=fun row=>
    (∀ i:Fin m,row (finProdFinEquiv (i,i))=0)∧
    (∀ i j:Fin m,row (finProdFinEquiv (i,j))=row (finProdFinEquiv (j,i)))
   exact (qv (M0 x) (Pay0 x)).2.2.2.2 PropRow ⟨fun _=>rfl,fun _ _=>rfl⟩
    (fun u v hu hv=>⟨fun i=>by simp [hu.1 i,hv.1 i],fun i j=>by simp [hu.2 i j,hv.2 i j]⟩)
    (fun j=>⟨fun i=>by dsimp only [M0]; rw [Equiv.symm_apply_apply]; exact (hValid x j).1 i,
      fun i r=>by dsimp only [M0]; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]; exact (hValid x j).2 i r⟩)
  have haff_sp:=kg (A0 x) (b0 x) (pk x).qs (kG (gs1 x).used (Q1 x) hQ1v)
  have hsupp':∀ s u,free x u=false→((aff x).qs s).l u=0∧∀ w,((aff x).qs s).B u w=0:=by
   intro s u hu
   have hve:(aff x).varElim u=true:=by simp only [free,Bool.not_eq_false'] at hu; exact hu
   exact haff_sp.2.1 s u hve
  have hdiff_ge:(0:ℤ)≤(posSum x:ℤ)-(negSum x:ℤ):=by
   have hsum_cast:∀ (F:Fin (2 ^ h)→ℕ),
    (((List.finRange (2 ^ h)).map F).sum:ℤ)=∑ σ:Fin (2 ^ h),(F σ:ℤ):=fun F=>by
    rw [← Fin.sum_univ_def,Nat.cast_sum]
   rw [show (posSum x:ℤ)=∑ σ:Fin (2 ^ h),(posF σ x:ℤ) from hsum_cast (fun σ=>posF σ x),
    show (negSum x:ℤ)=∑ σ:Fin (2 ^ h),(negF σ x:ℤ) from hsum_cast (fun σ=>negF σ x),
    ← Finset.sum_sub_distrib]
   have hterm:∀ σ:Fin (2 ^ h),
    (posF σ x:ℤ)-(negF σ x:ℤ)=
    ∑ a∈z4 (free x),qz ((qg (aff x).qs (qG h σ.val)).eval a):=fun σ=>by
    rw [kC]
    exact (vG (free x) _ (vv (aff x).qs haff_sp.1 _)
     (vF (aff x).qs (free x) hsupp' _)).2
   simp_rw [hterm]
   rw [Finset.sum_comm]
   refine Finset.sum_nonneg (fun a _=>?_)
   simp_rw [ka]
   let eqv:=Equiv.ofBijective _ (yM h)
   have heqv_sum:∑ σ:Fin (2 ^ h),qz (∑ s:Fin h,qG h σ.val s * ((aff x).qs s).eval a)=
    ∑ τ:Fin h→ZMod 2,qz (∑ s:Fin h,τ s * ((aff x).qs s).eval a):=
    Fintype.sum_equiv eqv _ _ (fun _=>rfl)
   rw [heqv_sum,kB]
   split_ifs
   · positivity
   · exact le_rfl
  have hneg_lt:negSum x<2 ^ L:=by
   have hsum_le:negSum x≤∑ _σ:Fin (2 ^ h),2 ^ m:=by
    rw [show negSum x=∑ σ:Fin (2 ^ h),negF σ x from (Fin.sum_univ_def _).symm]
    refine Finset.sum_le_sum (fun σ _=>?_)
    rcases (vG (free x) _ (vv (aff x).qs haff_sp.1 _)
     (vF (aff x).qs (free x) hsupp' _)).1 with ⟨e,he,hpow⟩
    exact (jb _ e he hpow).2
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum_le
   calc
    negSum x≤2 ^ h * 2 ^ m:=hsum_le
    _=2 ^ (m+h):=by rw [Nat.mul_comm,← Nat.pow_add]
    _<2 ^ L:=Nat.pow_lt_pow_right (by omega) (by simp [L])
  exact ⟨by omega,hneg_lt⟩
 have hSubB:qa B7 (Set.range (qk L (fun x=>posSum x-negSum x))) (19 * L):=
  j3 L posSum negSum hF7 hT7 (fun j=>Or.inr (Or.inl ⟨j,rfl⟩))
   (fun j=>Or.inr (Or.inr ⟨j,rfl⟩)) hvalidSub
 let B8:=B7 ∪ Set.range (qk L (fun x=>posSum x-negSum x))
 have hShiftB:qa B8 (Set.range (qk L shifted)) (L * 1):=
  qf _ 1 (fun j=>by
   have heq:qk L shifted j=fun x=>consistent x&&qk L (fun x=>posSum x-negSum x) j x:=by
    funext x; simp only [qk,shifted]; cases consistent x <;> simp
   rw [heq]
   exact qD (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))) (Or.inr ⟨j,rfl⟩))
 have hGenElimB:qa B0 (qY gsGen)
  (k * (m * (m+4)+(k+0) * (2 * m)+m * (1+(k+0) * 10))):=
  vN B0 hF0 gen (fun _ _=>Fin.elim0)
   hGen
   (fun _ p=>Fin.elim0 p)
 have hGenOHB:qa (B0 ∪ qY gsGen)
  (Set.range (fun r:Fin (m+1)=>fun x=>rGenOH x r)) (m * ((m+1) * 4)):=
  v3 _ (Or.inl hF0) (Or.inl hT0) (fun x=>(gsGen x).used)
   (fun j=>Or.inr (Or.inl (Or.inl ⟨j,rfl⟩)))
 have hStage4Prep:qa B0 (Set.range (fun r:Fin (m+1)=>fun x=>rGenOH x r))
  (k * (m * (m+4)+(k+0) * (2 * m)+m * (1+(k+0) * 10))+m * ((m+1) * 4)):=
  qe hGenElimB hGenOHB
 have hMainPipe:qa B0 (Set.range (qk L shifted))
  (t * (160+m * 40+(m * (m * 10)+m * 15+5)) +
   (m * m) * (t * (t+4)+(m * m+(m+1)) * (2 * t)+t * (1+(m * m+(m+1)) * 10)) +
   (t * ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4)))+t * (m * 2)+t * 2) +
   m * (t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
     h * (m * (m * 14)+m * 19+9)) +
   (t * 2+t+m * 1) +
   2 ^ h * cSigma +
   (2 ^ h * (9 * L)+2 ^ h * (9 * L)) +
   19 * L+L * 1):=
  qo (qo (qo (qo (qo (qo (qo (qo
   (qP hS0) (qP hS1)) (qP hS1b)) (qP hS2)) (qP hS2b)) (qP hAllSig)) (qP hSumsB)) (qP hSubB)) hShiftB
 let B9:=B0 ∪ (Set.range (qk L shifted) ∪ Set.range (fun r:Fin (m+1)=>fun x=>rGenOH x r))
 have hBoth:=qr hMainPipe hStage4Prep
 have hOutB:qa B9 (Set.range outSig) ((k+1) * ((m+1) * 2)):=by
  refine qf outSig ((m+1) * 2) (fun o=>?_)
  let term:Fin (m+1)→Sig inputs:=fun r x=>
   rGenOH x r&&(if hlt:h+m-r.val+o.val<L then
    (shifted x).testBit (h+m-r.val+o.val) else false)
  have htB:qa B9 (Set.range term) ((m+1) * 1):=
   qf term 1 (fun r=>by
    by_cases hlt:h+m-r.val+o.val<L
    · have heq:term r=fun x=>rGenOH x r&&qk L shifted ⟨h+m-r.val+o.val,hlt⟩ x:=by
       funext x; simp [term,qk,hlt]
      rw [heq]
      exact qD (Or.inr (Or.inr ⟨r,rfl⟩)) (Or.inr (Or.inl ⟨⟨h+m-r.val+o.val,hlt⟩,rfl⟩))
    · have heq:term r=fun _=>false:=by funext x; simp [term,hlt]
      rw [heq]
      exact qd (zk (A:=B9) (B:={fun _=>false}) (Set.singleton_subset_iff.mpr (Or.inl hF0)))
       le_rfl Set.subset_union_right (by omega))
  have horB:qa (B9 ∪ Set.range term) {outSig o} (m+1):=by
   have h1:=vt (A:=B9 ∪ Set.range term) ((List.finRange (m+1)).map term)
    (fun f hf=>by rcases List.mem_map.mp hf with ⟨r,_,rfl⟩; exact Or.inr ⟨r,rfl⟩)
    (Or.inl (Or.inl hF0))
   have heq:(fun x=>((List.finRange (m+1)).map term).any (fun f=>f x))=outSig o:=by
    funext x; simp [outSig,term,List.any_map]; rfl
   rw [heq,List.length_map,List.length_finRange] at h1
   exact h1
  exact qd (qe htB horB) le_rfl Set.subset_union_right (by omega)
 have hTotal:=qe hBoth hOutB
 refine qd hTotal le_rfl Set.subset_union_right ?_
 have h_le_t:h≤t:=Nat.min_le_right q t
 have h2h_pos:1≤2 ^ h:=Nat.one_le_two_pow
 let N:=k+m+t+2
 have hkN:k≤N:=by omega
 have hmN:m≤N:=by omega
 have htN:t≤N:=by omega
 have hhN:h≤N:=by omega
 have hm1N:m+1≤N:=by omega
 have hk1N:k+1≤N:=by omega
 have hh1N:h+1≤N:=by omega
 have hLN:L≤2 * N:=by simp only [L]; omega
 have hN2:2≤N:=by omega
 have hN_le_2:N≤N ^ 2:=by
  calc N=N * 1:=(Nat.mul_one N).symm
   _≤N * N:=Nat.mul_le_mul_left N (by omega)
   _=N ^ 2:=(pow_two N).symm
 have hN2_le_3:N ^ 2≤N ^ 3:=Nat.pow_le_pow_right (by omega) (by omega)
 have hN_le_3:N≤N ^ 3:=le_trans hN_le_2 hN2_le_3
 have h1_le_3:1≤N ^ 3:=le_trans (by omega) hN_le_3
 have hmul2:∀ a b,a≤N→b≤N→a * b≤N ^ 2:=fun a b ha hb=>by
  calc a * b≤N * N:=Nat.mul_le_mul ha hb
   _=N ^ 2:=(pow_two N).symm
 have hmul3:∀ a b c,a≤N→b≤N→c≤N→a * (b * c)≤N ^ 3:=fun a b c ha hb hc=>by
  calc a * (b * c)≤N * N ^ 2:=Nat.mul_le_mul ha (hmul2 b c hb hc)
   _=N ^ 3:=by ring
 have hm2:m * m≤N ^ 2:=hmul2 m m hmN hmN
 have ht2:t * t≤N ^ 2:=hmul2 t t htN htN
 have hk2:k * k≤N ^ 2:=hmul2 k k hkN hkN
 have hmt:m * t≤N ^ 2:=hmul2 m t hmN htN
 have hkm:k * m≤N ^ 2:=hmul2 k m hkN hmN
 have hm3:m * (m * m)≤N ^ 3:=hmul3 m m m hmN hmN hmN
 have hm2h:m * (m * h)≤N ^ 3:=hmul3 m m h hmN hmN hhN
 have hm2t:m * (m * t)≤N ^ 3:=hmul3 m m t hmN hmN htN
 have htm2:t * (m * m)≤N ^ 3:=hmul3 t m m htN hmN hmN
 have hhm2:h * (m * m)≤N ^ 3:=hmul3 h m m hhN hmN hmN
 have hkm2:k * (m * m)≤N ^ 3:=hmul3 k m m hkN hmN hmN
 have hk2m:k * (k * m)≤N ^ 3:=hmul3 k k m hkN hkN hmN
 have hcSigma_le:cSigma≤400 * N ^ 3:=by
  have h1:m * (m * (4 * h))=4 * (m * (m * h)):=by ring
  have h2:m * (4 * h)=4 * (m * h):=by ring
  have h3:m * (m * (m+7)+(m+1) * (2 * m)+(m * (m * 26)+m * 60+40))=
   29 * (m * (m * m))+69 * (m * m)+40 * m:=by ring
  have hmh:m * h≤N ^ 2:=hmul2 m h hmN hhN
  simp only [cSigma]
  rw [h1,h2,h3]
  omega
 have hp1:t * (160+m * 40+(m * (m * 10)+m * 15+5))≤300 * N ^ 3:=by
  have heq:t * (160+m * 40+(m * (m * 10)+m * 15+5))=
   165 * t+55 * (m * t)+10 * (t * (m * m)):=by ring
  rw [heq]; omega
 have hp2:(m * m) * (t * (t+4)+(m * m+(m+1)) * (2 * t)+t * (1+(m * m+(m+1)) * 10))≤100 * N ^ 5:=by
  have h1:t * (t+4)+(m * m+(m+1)) * (2 * t)+t * (1+(m * m+(m+1)) * 10)=
   t * t+17 * t+12 * (t * (m * m))+12 * (m * t):=by ring
  have h1le:t * (t+4)+(m * m+(m+1)) * (2 * t)+t * (1+(m * m+(m+1)) * 10)≤100 * N ^ 3:=by
   rw [h1]; omega
  calc (m * m) * _≤N ^ 2 * (100 * N ^ 3):=Nat.mul_le_mul hm2 h1le
   _=100 * N ^ 5:=by ring
 have hp3:t * ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4)))+t * (m * 2)+t * 2≤100 * N ^ 4:=by
  have hmh:m * h≤N ^ 2:=hmul2 m h hmN hhN
  have h1:(h+1) * 4+h * (1+(m * (m * 4)+m * 4+4))=
   9 * h+4+4 * (h * (m * m))+4 * (m * h):=by ring
  have h1le:(h+1) * 4+h * (1+(m * (m * 4)+m * 4+4))≤50 * N ^ 3:=by
   rw [h1]; omega
  have htm:t * (m * 2)=2 * (m * t):=by ring
  have hN3_le_4:N ^ 3≤N ^ 4:=Nat.pow_le_pow_right (by omega) (by omega)
  have hN2_le_4:N ^ 2≤N ^ 4:=le_trans hN2_le_3 hN3_le_4
  have hN_le_4:N≤N ^ 4:=le_trans hN_le_3 hN3_le_4
  have hm1:t * ((h+1) * 4+h * (1+(m * (m * 4)+m * 4+4)))≤50 * N ^ 4:=by
   calc t * _≤N * (50 * N ^ 3):=Nat.mul_le_mul htN h1le
    _=50 * N ^ 4:=by ring
  rw [htm]; omega
 have hp4:m * (t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
  h * (m * (m * 14)+m * 19+9))≤200 * N ^ 4:=by
  have hmh:m * h≤N ^ 2:=hmul2 m h hmN hhN
  have h1:t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
   h * (m * (m * 14)+m * 19+9)=
   t * t+18 * t+12 * (m * t)+m+14 * (h * (m * m))+19 * (m * h)+9 * h:=by ring
  have h1le:t * (t+5)+(m+1) * (2 * t)+t * (1+m * 10+10)+m +
   h * (m * (m * 14)+m * 19+9)≤200 * N ^ 3:=by
   rw [h1]; omega
  calc m * _≤N * (200 * N ^ 3):=Nat.mul_le_mul hmN h1le
   _=200 * N ^ 4:=by ring
 have hp5:2 ^ h * cSigma+(2 ^ h * (9 * L)+2 ^ h * (9 * L))≤500 * N ^ 3 * 2 ^ h:=by
  have h1:cSigma+9 * L+9 * L≤500 * N ^ 3:=by omega
  calc 2 ^ h * cSigma+(2 ^ h * (9 * L)+2 ^ h * (9 * L))=2 ^ h * (cSigma+9 * L+9 * L):=by ring
   _≤2 ^ h * (500 * N ^ 3):=Nat.mul_le_mul_left _ h1
   _=500 * N ^ 3 * 2 ^ h:=by ring
 have hp6:k * (m * (m+4)+(k+0) * (2 * m)+m * (1+(k+0) * 10))+m * ((m+1) * 4) +
  (k+1) * ((m+1) * 2)+(t * 2+t+m * 1)+19 * L+L * 1+2≤200 * N ^ 3:=by
  have heq:k * (m * (m+4)+(k+0) * (2 * m)+m * (1+(k+0) * 10))+m * ((m+1) * 4) +
   (k+1) * ((m+1) * 2)+(t * 2+t+m * 1)+19 * L+L * 1+2=
   k * (m * m)+7 * (k * m)+12 * (k * (k * m))+4 * (m * m)+7 * m+2 * k+3 * t+20 * L+4:=by ring
  rw [heq]; omega
 have hN3_le_8:N ^ 3≤N ^ 8:=Nat.pow_le_pow_right (by omega) (by omega)
 have hN4_le_8:N ^ 4≤N ^ 8:=Nat.pow_le_pow_right (by omega) (by omega)
 have hN5_le_8:N ^ 5≤N ^ 8:=Nat.pow_le_pow_right (by omega) (by omega)
 have hsum_poly:300 * N ^ 3+100 * N ^ 5+100 * N ^ 4+200 * N ^ 4+200 * N ^ 3≤1000 * N ^ 8:=by
  omega
 have hmul_2h:1000 * N ^ 8≤1000 * N ^ 8 * 2 ^ h:=Nat.le_mul_of_pos_right _ h2h_pos
 have h500_le:500 * N ^ 3 * 2 ^ h≤500 * N ^ 8 * 2 ^ h:=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hN3_le_8)
 have h1500_le:1500 * N ^ 8 * 2 ^ h≤2 ^ 20 * N ^ 8 * 2 ^ h:=by
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
  norm_num
 have hadd_1500:1000 * N ^ 8 * 2 ^ h+500 * N ^ 8 * 2 ^ h=1500 * N ^ 8 * 2 ^ h:=by ring
 change _≤2 ^ 20 * N ^ 8 * 2 ^ h
 omega
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine
namespace yo
abbrev In (N:ℕ):=Fin N→Bool
variable {N k m r t:ℕ}
abbrev Val:=In N→F
abbrev bit (f:Val (N:=N)):Sig N:=fun x=>z2b (f x)
abbrev yB (A:Set (Sig N)) (f:Val) (n:ℕ):=qa A {bit f} n
theorem get {A:Set (Sig N)} {f:Val} (hf:bit f∈A):yB A f 0:=zk (by simpa using hf)
theorem add {A:Set (Sig N)} {f g:Val} {a b:ℕ} (hf:yB A f a) (hg:yB A g b):
 yB A (fun x=>f x+g x) (a+b+4):=by
 have z:=qr hf hg
 apply qe z
 rw [show bit (fun x=>f x+g x)=(fun x=>xor (bit f x) (bit g x)) from funext fun x=>vW _ _]
 exact yW (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
theorem mul {A:Set (Sig N)} {f g:Val} {a b:ℕ} (hf:yB A f a) (hg:yB A g b):
 yB A (fun x=>f x * g x) (a+b+1):=by
 apply qe (qr hf hg)
 rw [show bit (fun x=>f x * g x)=(fun x=>bit f x&&bit g x) from funext fun x=>yX _ _]
 exact qD (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
theorem one (A:Set (Sig N)):yB A (fun _=>1) 1:=by
 unfold yB
 rw [show bit (N:=N) (fun _=>1)=(fun _=>true) from funext fun _=>zA]
 exact k4 true
abbrev qJ (N k:ℕ):=In N→Bool→V k
abbrev Cst (N k r:ℕ):=In N→Bool→Fin (r+1)→V k
abbrev Key (N k:ℕ):=In N→V k
abbrev Gen (N k m:ℕ):=In N→Fin m→V k
def uw (hk:0<k) (nm:qJ N k) (c:Cst N k r) (key:Key N k) (b:Bool) (n:ℕ) (j:Fin k):=
 bit fun x=>state hk (nm x) (c x) b (key x) n j
theorem wa (hk:0<k) (nm:qJ N k) (c:Cst N k r) (key:Key N k) (A:Set (Sig N))
 (hnm:∀ b j,(bit fun x=>nm x b j)∈A) (hc:∀ b n j,(bit fun x=>c x b n j)∈A)
 (hkey:∀ j,(bit fun x=>key x j)∈A) (b:Bool) (n:ℕ) (hn:n≤r+1):
 qa A (Set.range (uw hk nm c key b n)) ((n+1)*(k*50)):=by
 induction n with
 | zero=>
   simp only [zero_add,one_mul]
   refine qf _ 50 fun j=>?_
   have h:=add (get (hkey (ix hk (j.val+k-start b % k)))) (get (hnm b j))
   exact qd h le_rfl Set.subset_union_right (by decide)
 | succ n ih=>
   have prev:=ih (by omega)
   have step:qa (A ∪ Set.range (uw hk nm c key b n)) (Set.range (uw hk nm c key b (n+1))) (k*50):=by
    refine qf _ 50 fun j=>?_
    let D:=A ∪ Set.range (uw hk nm c key b n)
    let z (x:In N):=state hk (nm x) (c x) b (key x) n
    have hz (i:Fin k):yB D (fun x=>z x i) 0:=get (Or.inr ⟨i,rfl⟩)
    have hy (i:Fin k):yB D (fun x=>mix hk b (z x) i) 8:=
     add (add (hz i) (hz _)) (hz _)
    have hz':=add (add (add (hy j) (mul (add (one D) (hy (ix hk (j.val+1)))) (hy (ix hk (j.val+2)))))
     (get (A:=D) (Or.inl (hkey (ix hk (j.val+k-feed b n % k)))))) (get (A:=D) (Or.inl (hc b ⟨n,by omega⟩ j)))
    have eq:uw hk nm c key b (n+1) j=bit (fun x=>update hk b (key x) n (c x b ⟨n,by omega⟩) (z x) j):=by
     funext x; exact congrArg (fun v:V k=>z2b (v j)) (state_step hk (nm x) (c x) b (key x) n (by omega))
    rw [eq]; exact qd hz' le_rfl Set.subset_union_right (by decide)
   exact qd (qe prev step) le_rfl Set.subset_union_right (by simp only [Nat.add_mul,one_mul,le_refl])
abbrev yh (m:ℕ):=Unit ⊕ (Fin m ⊕ Fin m×Fin m)
def yH (rep:Key N k) (gen:Gen N k m) (s:yh m):Key N k:=
 match s with
 | .inl _=>rep
 | .inr (.inl i)=>fun x=>rep x+gen x i
 | .inr (.inr (i,j))=>fun x=>rep x+gen x i+gen x j
theorem jY {I:Type*} [Fintype I] (A:Set (Sig N)) (U:I→Set (Sig N)) (d:ℕ)
 (h:∀ i,qa A (U i) d):qa A (⋃ i,U i) (Fintype.card I*d):=by
 classical
 let e:=Fintype.equivFin I
 apply qd (v7 (fun j=>U (e.symm j)) d (fun j=>h _)) le_rfl _ le_rfl
 intro f hf
 obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hf
 exact Or.inr (Set.mem_iUnion.mpr ⟨e i,by simpa using hi⟩)
abbrev Ix (m r:ℕ):=yh m×Bool×Fin (r+2)
def k3 (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m):Set (Sig N):=
 ⋃ a:Ix m r,Set.range (uw hk nm c (yH rep gen a.1) a.2.1 a.2.2.val)
theorem uD (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
 (A:Set (Sig N)) (hnm:∀ b j,(bit fun x=>nm x b j)∈A)
 (hc:∀ b n j,(bit fun x=>c x b n j)∈A) (hr:∀ j,(bit fun x=>rep x j)∈A)
 (hg:∀ i j,(bit fun x=>gen x i j)∈A):
 qa A (k3 hk nm c rep gen) ((1+(m+m*m))*(2*(r+2))*(k*8+(r+2)*(k*50))):=by
 classical
 unfold k3
 have cardI:Fintype.card (Ix m r)=(1+(m+m*m))*(2*(r+2)):=by simp [Ix,yh]
 rw [← cardI]
 apply jY
 rintro ⟨s,b,n⟩
 let key:=yH rep gen s
 let K:=Set.range (fun j=>bit fun x=>key x j)
 have keys:qa A K (k*8):=by
  apply qf
  intro j
  rcases s with _|i
  · exact qd (get (hr j)) le_rfl Set.subset_union_right (by decide)
  · rcases i with i|⟨i,l⟩
    · exact qd (add (get (hr j)) (get (hg i j))) le_rfl Set.subset_union_right (by decide)
    · exact add (add (get (hr j)) (get (hg i j))) (get (hg l j))
 have hh:=wa hk nm c key (A ∪ K) (fun b j=>Or.inl (hnm b j))
  (fun b n j=>Or.inl (hc b n j)) (fun j=>Or.inr ⟨j,rfl⟩) b n (by omega)
 exact qd (qe keys hh) le_rfl Set.subset_union_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ n.isLt) _)
theorem ue (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
 (s:yh m) (b:Bool) (n:ℕ) (hn:n≤r+1) (j:Fin k):
 uw hk nm c (yH rep gen s) b n j∈k3 hk nm c rep gen:=
 Set.mem_iUnion.mpr ⟨(s,b,⟨n,by omega⟩),j,rfl⟩
abbrev qI (k:ℕ):=Bool→ℕ→Fin k→Bool
abbrev ky (k m r:ℕ):=Bool×Fin r×Fin k×Fin m×Fin m
def za (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
    (b:Bool) (n:ℕ) (j:Fin k) (s:yh m) (x:In N):F:=
 state hk (nm x) (c x) b (yH rep gen s x) n j
def delta (u:yh m→F) (i j:Fin m):=u (.inl ())+u (.inr (.inl i)) +
 u (.inr (.inl j))+u (.inr (.inr (i,j)))
def uC (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
    (w:qI k) (a:ky k m r) (x:In N):=
 let (b,n,j,i,l):=a
 if w b (n.val+1) j=true∧i<l then
  !(z2b (delta (fun s=>za hk nm c rep gen b (n.val+1) j s x) i l)) else true
noncomputable def vE (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
 (w:qI k) (x:In N):=(Finset.univ:Finset (ky k m r)).toList.all
   fun a=>uC hk nm c rep gen w a x
theorem uo (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
 (w:qI k) (x:In N):vE hk nm c rep gen w x=true↔
 ∀ b n,0<n→n≤r→∀ j,w b n j=true→∀ i l:Fin m,i<l→
   delta (fun s=>za hk nm c rep gen b n j s x) i l=0:=by
 simp only [vE,List.all_eq_true,Finset.mem_toList,Finset.mem_univ,forall_const]
 constructor
 · intro h b n hn hr j hw i l hil
   obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
   simpa [uC,hw,hil,z2b] using h (b,⟨n,by omega⟩,j,i,l)
 · rintro h ⟨b,n,j,i,l⟩
   by_cases h':w b (n.val+1) j=true∧i<l
   · simp [uC,h',h b (n.val+1) (by omega) (by omega) j h'.1 i l h'.2,qm]
   · simp [uC,h']
def kx (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
    (side:Fin t→Bool) (site:Fin t→Fin k) (target:In N→V t) (u:Fin t) (x:In N):qc m:=
 let f:=fun s=>za hk nm c rep gen (side u) (r+1) (site u) s x
 ⟨delta f,fun i=>f (.inl ())+f (.inr (.inl i)),f (.inl ())+target x u⟩
theorem uE {A:Set (Sig N)} (v:yh m→Val (N:=N))
 (h:∀ s,bit (v s)∈A) (i j:Fin m):yB A (fun x=>delta (fun s=>v s x) i j) 12:=
 add (add (add (get (h _)) (get (h _))) (get (h _))) (get (h _))
def zI (k m r t:ℕ):=(1+(m+m*m))*(2*(r+2))*(k*8+(r+2)*(k*50)) +
 (1+(2*(r*(k*(m*m)))*13+2*(r*(k*(m*m)))))+t*(m*(m*12)+m*4+4)
theorem jJ (hk:0<k) (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m)
 (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k) (target:In N→V t)
 (A:Set (Sig N)) (hnm:∀ b j,(bit fun x=>nm x b j)∈A)
 (hc:∀ b n j,(bit fun x=>c x b n j)∈A) (hr:∀ j,(bit fun x=>rep x j)∈A)
 (hg:∀ i j,(bit fun x=>gen x i j)∈A) (ht:∀ u,(bit fun x=>target x u)∈A):
 qa A ({vE hk nm c rep gen w} ∪ ⋃ u,qn (kx hk nm c rep gen side site target u)) (zI k m r t):=by
 classical
 let D:=A ∪ k3 hk nm c rep gen
 have mem (b n j s) (hn:n≤r+1):bit (za hk nm c rep gen b n j s)∈D:=
  Or.inr (ue hk nm c rep gen s b n hn j)
 have quads:qa D (⋃ u,qn (kx hk nm c rep gen side site target u)) (t*(m*(m*12)+m*4+4)):=by
  apply v7
  intro u
  let f:=za hk nm c rep gen (side u) (r+1) (site u)
  have hf (s):bit (f s)∈D:=mem _ _ _ _ le_rfl
  exact qr (qr (qT _ 12 (fun i j=>uE f hf i j))
   (qf _ 4 (fun i=>add (get (hf (.inl ()))) (get (hf (.inr (.inl i)))))))
   (add (get (hf (.inl ()))) (get (A:=D) (Or.inl (ht u))))
 let I:=ky k m r
 let d:=2*(r*(k*(m*m)))
 have cardI:Fintype.card I=d:=by simp [I,ky,d]
 let T:=uC hk nm c rep gen w
 let L:=(Finset.univ:Finset I).toList
 have tests:qa D (⋃ a,{T a}) (d*13):=by
  rw [← cardI]
  apply jY
  rintro ⟨b,n,j,i,l⟩
  by_cases h:w b (n.val+1) j=true∧i<l
  · have q:=uE (za hk nm c rep gen b (n.val+1) j) (fun s=>mem _ _ _ _ (by omega)) i l
    have hn:=qe q (zn (A:=D ∪ _) (Or.inr rfl))
    rw [show T (b,n,j,i,l)=(fun x=>!z2b (delta (fun s=>za hk nm c rep gen b (n.val+1) j s x) i l)) by
     funext x; simp [T,uC,h]]
    exact hn
  · rw [show T (b,n,j,i,l)=(fun _=>true) by funext x; simp [T,uC,h]]
    exact qd (k4 true) le_rfl Set.subset_union_right (by decide)
 have allT:qa D {vE hk nm c rep gen w} (1+(d*13+d)):=by
  let B:=D ∪ {fun _=>true}
  apply qe (k4 (A:=D) true)
  apply qe (qd tests (A':=B) Set.subset_union_left Set.subset_union_right le_rfl)
  let xs:=L.map T
  have hf:∀ f∈xs,f∈B ∪ ⋃ a,{T a}:=by
   intro f hf; obtain ⟨a,_,rfl⟩:=List.mem_map.mp hf; exact Or.inr (Set.mem_iUnion.mpr ⟨a,rfl⟩)
  have hh:=kK xs hf (Or.inl (Or.inr rfl))
  rw [show vE hk nm c rep gen w=(fun x=>xs.all (fun f=>f x)) by
   funext x; simp [xs,L,T,vE,Function.comp_def]]
  exact qd hh le_rfl Set.subset_union_right (by simp [xs,L,cardI,d,I,ky])
 exact qd (qe (uD hk nm c rep gen A hnm hc hr hg) (qr allT quads)) le_rfl
  Set.subset_union_right (by simp [zI,d,Nat.add_assoc])
theorem k5 (k m r t:ℕ):zI k m r t≤1024*(k+m+r+t+4)^5:=by
 let s:=k+m+r+t
 calc
  zI k m r t≤zI s s s s:=by unfold zI; gcongr <;> dsimp [s] <;> omega
  _≤1024*(s+4)^5:=by unfold zI; ring_nf; omega
end yo
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
abbrev jf (k m r t:ℕ):=(m+2+2*(r+1))*k+t
abbrev vq (k m r t:ℕ):=(Fin m×Fin k) ⊕ ((Bool×Fin k) ⊕ ((Bool×Fin (r+1)×Fin k) ⊕ Fin t))
def uR {k m r t} (i:Fin m) (j:Fin k):vq k m r t:=Sum.inl (i,j)
def kW {k m r t} (b:Bool) (j:Fin k):vq k m r t:=Sum.inr (Sum.inl (b,j))
def je {k m r t} (b:Bool) (i:Fin (r+1)) (j:Fin k):vq k m r t:=Sum.inr (Sum.inr (Sum.inl (b,i,j)))
def uT {k m r t} (i:Fin t):vq k m r t:=Sum.inr (Sum.inr (Sum.inr i))
def vj (k m r t:ℕ):List (vq k m r t):=
 (List.ofFn fun i=>List.ofFn (uR i)).flatten++List.ofFn (kW false)++List.ofFn (kW true)++
   (List.ofFn fun i=>List.ofFn (je false i)).flatten++(List.ofFn fun i=>List.ofFn (je true i)).flatten++List.ofFn uT
theorem yI (k m r t:ℕ):(vj k m r t).length=jf k m r t:=by
 simp [vj,List.length_flatten,jf,Function.comp_def,List.ofFn_const]; ring
theorem jm {k m r t} (s:vq k m r t):s∈vj k m r t:=by
 rcases s with ⟨i,j⟩|(⟨b,j⟩|(⟨b,i,j⟩|i))
 · simp [vj,uR,List.mem_flatten,List.mem_ofFn]
 · cases b <;> simp [vj,kW,List.mem_ofFn]
 · cases b <;> simp [vj,je,List.mem_flatten,List.mem_ofFn] <;> tauto
 · simp [vj,uT,List.mem_ofFn]
def jR {k m r t} (s:vq k m r t):Fin (jf k m r t):=
 ⟨(vj k m r t).idxOf s,yI k m r t▸List.idxOf_lt_length_of_mem (jm s)⟩
def jQ {k m r t} (x:Fin (jf k m r t)→Bool) (s:vq k m r t):ZMod 2:=b2z (x (jR s))
def y6 {k m r t} (v:vq k m r t→ZMod 2):Fin (jf k m r t)→Bool:=
 fun i=>z2b (v ((vj k m r t).get ⟨i.val,by rw [yI]; exact i.isLt⟩))
theorem j7 {k m r t} (v:vq k m r t→ZMod 2) (s:vq k m r t):jQ (y6 v) s=v s:=by
 simp [jQ,y6,jR,vr,List.get_eq_getElem,List.getElem_idxOf]
def uU {k m r t} (gen:Fin m→Fin k→ZMod 2) (name:Bool→Fin k→ZMod 2)
    (c:Bool→Fin (r+1)→Fin k→ZMod 2) (tar:Fin t→ZMod 2):vq k m r t→ZMod 2
 | .inl (i,j)=>gen i j
 | .inr (.inl (b,j))=>name b j
 | .inr (.inr (.inl (b,i,j)))=>c b i j
 | .inr (.inr (.inr i))=>tar i
theorem jW {k m r t} (gen:Fin m→Fin k→ZMod 2) (name:Bool→Fin k→ZMod 2)
 (c:Bool→Fin (r+1)→Fin k→ZMod 2) (tar:Fin t→ZMod 2):
 let pack:=fun w:Fin k→ZMod 2=>List.ofFn (fun j=>decide (w j≠0))
 List.ofFn (y6 (uU gen name c tar))=
  (List.ofFn (fun i=>pack (gen i))).flatten++pack (name false)++pack (name true)++
  (List.ofFn (fun i=>pack (c false i))).flatten++(List.ofFn (fun i=>pack (c true i))).flatten++
  List.ofFn (fun i=>decide (tar i≠0)):=by
 intro pack
 let v:=uU gen name c tar
 have eqmap:List.ofFn (y6 v)=(vj k m r t).map (fun s=>z2b (v s)):=by
  apply List.ext_getElem
  · simp [yI]
  · intro i hi hj; simp [y6]
 rw [eqmap]
 simp only [vj,List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,uR,kW,je,uT,v,uU,pack,z2b]
 rfl
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
theorem j1 {N k L b:ℕ} {A:Set (Sig N)} {flag:Sig N}
 {ans:Fin L→Sig N} (hs:vK N k A)
 (hb:qa A ({flag} ∪ Set.range ans) b):
 ∃ (C:Circuit) (f:Fin (N+C.size)) (out:Fin L→Fin (N+C.size)),
   FanInTwo C∧ReadsBack N C∧C.output=f.val∧C.size≤k+b∧
   (∀ x,(C.wires (List.ofFn x)).getD f.val false=flag x)∧
   ∀ j x,(C.wires (List.ofFn x)).getD (out j).val false=ans j x:=by
 obtain ⟨c,hc,gs,hlen,hr,hf,hw⟩:=hb.run hs le_rfl
 obtain ⟨i,hi,hflag⟩:=hw flag (Or.inr (Or.inl rfl))
 have hcho:∀ j,∃ p:Fin (N+gs.length),∀ x,
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD p.val false=ans j x:=by
  intro j
  obtain ⟨p,hp,h⟩:=hw (ans j) (Or.inr (Or.inr ⟨j,rfl⟩))
  exact ⟨⟨p,by omega⟩,h⟩
 choose out hout using hcho
 exact ⟨⟨gs,i⟩,⟨i,by change i<N+gs.length; omega⟩,out,hf,hr,rfl,
  by change gs.length≤k+b; omega,hflag,hout⟩
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
variable {N d k:ℕ}
def vf (good:Sig N) (live localOK:Fin d→Sig N):Sig N:=fun x=>
 good x&&(List.ofFn (fun i=>(fun y=>!(live i y)||localOK i y:Sig N))).all (fun a=>a x)
lemma kZ (good:Sig N) (live localOK:Fin d→Sig N) (x:Fin N→Bool):
 vf good live localOK x=true↔good x=true∧∀ i,live i x=true→localOK i x=true:=by
 simp only [vf,Bool.and_eq_true,List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
 apply and_congr_right'
 apply forall_congr'; intro i
 cases live i x <;> simp
private lemma u5 {A:Set (Sig N)} (good:Sig N) (live localOK:Fin d→Sig N)
 (ht:(fun _=>true)∈A) (hg:good∈A) (hl:∀ i,live i∈A) (ho:∀ i,localOK i∈A):
 qa A {vf good live localOK} (d*2+d+1):=by
 let chk (i:Fin d):Sig N:=fun x=>!(live i x)||localOK i x
 have hchk:qa A (Set.range chk) (d*2):=by
  apply qf
  intro i
  exact qe (zn (hl i)) (orB (Or.inr rfl) (Or.inl (ho i)))
 let combined:Sig N:=fun x=>(List.ofFn chk).all (fun a=>a x)
 have hall:qa (A ∪ Set.range chk) {combined} d:=by
  simpa only [List.length_ofFn] using kK (A:=A ∪ Set.range chk) (List.ofFn chk)
   (fun a h=>Or.inr (List.mem_ofFn.mp h)) (Or.inl ht)
 exact qe (qe hchk hall) (qD (Or.inl hg) (Or.inr rfl))
private lemma jr (F:Fin d→(Fin N→Bool)→ℕ) (x:Fin N→Bool):
 q6 (List.ofFn F) x=∑ i,F i x:=by
 induction d with
 | zero=>simp [q6]
 | succ d ih=>rw [List.ofFn_succ,Fin.sum_univ_succ]; exact congrArg (F 0 x+·) (ih (fun i=>F i.succ))
theorem js {A:Set (Sig N)} (good:Sig N) (live localOK:Fin d→Sig N)
 (u:Fin d→Fin (k+1)→Sig N) (f:(Fin N→Bool)→Fin d→ℕ)
 (hfalse:(fun _=>false)∈A) (htrue:(fun _=>true)∈A)
 (hg:good∈A) (hl:∀ i,live i∈A) (ho:∀ i,localOK i∈A)
 (hu:∀ i j,u i j∈A)
 (hc:∀ x,vf good live localOK x=true→∀ i,live i x=true→
   ∀ j:Fin (k+1),u i j x=(f x i).testBit j.val):
 qa A ({vf good live localOK} ∪ Set.range (qk (k+1) (fun x=>
  if vf good live localOK x then ∑ i,if live i x then f x i else 0 else 0)))
  (32*(d+1)*(k+2)):=by
 let flag:=vf good live localOK
 let S:=A ∪ {flag}
 have hflag:=u5 good live localOK htrue hg hl ho
 let en (i:Fin d):Sig N:=fun x=>flag x&&live i x
 have hEn:qa S (Set.range en) (d*1):=qf _ _ (fun i=>qD (Or.inr rfl) (Or.inl (hl i)))
 let M (i:Fin d) (x:Fin N→Bool):=if en i x then f x i else 0
 let bit (i:Fin d):=qk (k+1) (M i)
 let B:Set (Sig N):={a|∃ i j,bit i j=a}
 have hbits:qa (S ∪ Set.range en) B (d*((k+1)*1)):=by
  apply qT bit 1
  intro i j
  have hj:bit i j=fun x=>en i x&&u i j x:=by
   funext x
   change (if en i x then f x i else 0).testBit j.val=_
   cases he:en i x with
   | false=>simp
   | true=>
     have hh:flag x=true∧live i x=true:=by simpa [en] using he
     obtain ⟨hflag',hl'⟩:=hh
     simp [hc x hflag' i hl' j]
  rw [hj]; exact qD (Or.inr ⟨i,rfl⟩) (Or.inl (Or.inl (hu i j)))
 let Fs:=List.ofFn M
 have hsum:qa ((S ∪ Set.range en) ∪ B) (Set.range (qk (k+1) (q6 Fs))) (d*(9*(k+1))):=by
  simpa only [Fs,List.length_ofFn] using uA (A:=(S ∪ Set.range en) ∪ B) (k+1)
   (Or.inl (Or.inl (Or.inl hfalse))) Fs (by
     intro F hF j; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hF; exact Or.inr ⟨i,j,rfl⟩)
 have hv:q6 Fs=fun x=>if flag x then ∑ i,if live i x then f x i else 0 else 0:=by
  funext x; rw [show q6 Fs x=∑ i,M i x from jr M x]
  cases he:flag x <;> simp [M,en,he]
 have H:=zd hflag (qe hEn (qe hbits hsum))
 rw [hv] at H
 exact qd H le_rfl Set.subset_union_right (by nlinarith [Nat.zero_le (d*k)])
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine yo
theorem wc {N k m r t:Nat} (h:Nat) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (rep:Key N k) (gen:Gen N k m) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (target:In N→V t)
 (A:Set (Sig N)) (hF:(fun _=>false)∈A) (hT:(fun _=>true)∈A)
 (hnm:∀ b j,(bit fun x=>nm x b j)∈A) (hc:∀ b n j,(bit fun x=>c x b n j)∈A)
 (hr:∀ j,(bit fun x=>rep x j)∈A) (hg:∀ i j,(bit fun x=>gen x i j)∈A)
 (ht:∀ u,(bit fun x=>target x u)∈A):
 let Q:=fun x i=>kx hk nm c rep gen side site target i x
 qa A ({fun x=>vE hk nm c rep gen w x&&decide ((zm (Q x)).rank≤h)} ∪
  Set.range (fun j x=>yF h (gen x) (Q x) j))
  (2^30*(k+m+r+t+4)^12*2^(min t h)):=by
 classical
 intro Q
 let p:=vE hk nm c rep gen w
 let front:={p} ∪ ⋃ j,qn (fun x=>Q x j)
 let B:=A ∪ front
 have fr:qa A front (zI k m r t):=jJ hk nm c rep gen w side site target A hnm hc hr hg ht
 have qs (j:Fin t):qn (fun x=>Q x j)⊆B:=fun _ hf=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j,hf⟩))
 let rankFlag:Sig N:=fun x=>decide ((zm (Q x)).rank≤h)
 have rank:qa B {rankFlag} (2^12*(k+m+r+t+4)^10):=
  yO k r B h Q (Or.inl hF) (Or.inl hT) qs
 have both:qa (B ∪ {rankFlag}) {fun x=>p x&&rankFlag x} 1:=
  qD (Or.inl (Or.inr (Or.inl rfl))) (Or.inr rfl)
 have val (x:In N) (j:Fin t):(Q x j).Valid:=
  PEqualNP.Outside.L_meta_27129_aux.P25940Sample.sample_valid (gen x) (rep x) (fun key=>state hk (nm x) (c x) (side j) key (r+1) (site j)) (target x j)
 have counts:=jj h B gen Q (Or.inl hF) (Or.inl hT) (fun i j=>Or.inl (hg i j)) qs val
 have b:=qe fr (qr (qe rank both) counts)
 apply qd b le_rfl Set.subset_union_right
 let d:=k+m+r+t+4
 let e:=2^(min t h)
 have hd:1≤d:=by dsimp [d]; omega
 have he:1≤e:=Nat.one_le_two_pow
 have h5:d^5≤d^12:=Nat.pow_le_pow_right hd (by decide)
 have h10:d^10≤d^12:=Nat.pow_le_pow_right hd (by decide)
 have h8:(k+m+t+2)^8≤d^12:=(Nat.pow_le_pow_left (by dsimp [d]; omega) 8).trans (Nat.pow_le_pow_right hd (by decide))
 have hu:d^12≤d^12*e:=Nat.le_mul_of_pos_right _ he
 have hfr:zI k m r t≤1024*(d^12*e):=(k5 k m r t).trans (Nat.mul_le_mul_left _ (h5.trans hu))
 have hrank:=Nat.mul_le_mul_left (2^12) (h10.trans hu)
 have hct:2^20*(k+m+t+2)^8*e≤2^20*(d^12*e):=by rw [←Nat.mul_assoc]; gcongr
 have hunit:1≤d^12*e:=(Nat.one_le_pow _ _ hd).trans hu
 change zI k m r t+(2^12*d^10+1+2^20*(k+m+t+2)^8*2^(min h t))≤2^30*d^12*e
 rw [Nat.min_comm h t,show 2^(min t h)=e from rfl,Nat.mul_assoc (2^30)]
 omega
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux.P25940Sem
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine PEqualNP.Outside.L_meta_27129_aux.P25940Sample PEqualNP.Outside.L_meta_27129_aux
def key {m k} (rep:V k) (gen:Fin m→V k) (x:V m):V k:=rep+shift gen x
theorem mem_key_iff {m k} (rep:V k) (gen:Fin m→V k) (w:V k):
 w∈Set.range (key rep gen)↔w-rep∈Submodule.span F (Set.range gen):=by
 rw [Submodule.mem_span_range_iff_exists_fun F]
 constructor
 · rintro ⟨x,rfl⟩; exact ⟨x,by unfold key shift; abel⟩
 · rintro ⟨x,hx⟩; exact ⟨x,by change rep+(∑ i,x i • gen i)=w; rw [hx]; abel⟩
def probe {k r t} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
    (side:Fin t→Bool) (site:Fin t→Fin k) (j:Fin t) (w:V k):F:=
 state hk name c (side j) w (r+1) (site j)
def fullPrefix {m k r} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
    (gen:Fin m→V k) (watch:Bool→ℕ→Fin k→Bool):=
 ∀ a b n,n≤r→∀ j,watch b n j=true→∀ x y,
   state hk name c b a n j+state hk name c b (a+shift gen x) n j +
    state hk name c b (a+shift gen y) n j+state hk name c b (a+shift gen x+shift gen y) n j=0
theorem quadPolar_eq {m k t} (rep:V k) (gen:Fin m→V k) (f:Fin t→V k→F) (target:Fin t→F):
 zm (fun j=>sample gen rep (f j) (target j))=matrix gen rep f target:=rfl
theorem local_global {m k r t d} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (gen:Fin m→V k) (live:Fin d→Bool) (rep:Fin d→V k)
 (part:∀ w,∃! i,live i=true∧w-rep i∈Submodule.span F (Set.range gen))
 (watch:Bool→ℕ→Fin k→Bool) (hc:closed hk watch (r+1))
 (side:Fin t→Bool) (site:Fin t→Fin k) (hw:∀ j,watch (side j) (r+1) (site j)=true)
 (h:ℕ) (target:Fin t→F):
 let f:=probe hk name c side site
 (∀ i,live i=true→Checks hk name c gen (rep i) watch∧(matrix gen (rep i) f target).rank≤h)↔
 fullPrefix hk name c gen watch∧∀ a,(matrix gen a f target).rank≤h:=by
 let I:={i:Fin d // live i=true}
 have cover (a:V k):∃ s:I,∃ u,a=rep s.val+shift gen u:=by
  obtain ⟨s,⟨hl,hw⟩,_⟩:=part a
  obtain ⟨u,e⟩:=(mem_key_iff (rep s) gen a).mpr hw
  exact ⟨⟨s,hl⟩,u,e.symm⟩
 have hp:fullPrefix hk name c gen watch↔∀ s:I,Checks hk name c gen (rep s.val) watch:=
  prefix_pair_iff hk name c gen gen rfl (fun s:I=>rep s.val) cover watch hc
 constructor
 · intro conditions
   refine ⟨hp.mpr (fun s=>(conditions s.val s.property).1),fun a=>?_⟩
   obtain ⟨s,u,rfl⟩:=cover a
   obtain ⟨hs,hr⟩:=conditions s.val s.property
   have eqr:=(terminal_sample hk name c gen (rep s.val) watch hc side site hw target hs).2.2 u
   exact eqr.trans_le hr
 · rintro ⟨hg,hr⟩ i hi
   exact ⟨hp.mp hg ⟨i,hi⟩,hr (rep i)⟩
noncomputable def cosetCount {k m t} (rep:V k) (gen:Fin m→V k) (f:Fin t→V k→F) (target:Fin t→F):ℕ:=
 Nat.card {w:V k // w∈Set.range (key rep gen)∧∀ j,f j w=target j}
theorem cosetCount_eq_filter {k m t} (rep:V k) (gen:Fin m→V k) (f:Fin t→V k→F)
 (target:Fin t→F) [DecidablePred (fun w=>w-rep∈Submodule.span F (Set.range gen)∧∀ j,f j w=target j)]:
 cosetCount rep gen f target=(Finset.univ.filter
  (fun w=>w-rep∈Submodule.span F (Set.range gen)∧∀ j,f j w=target j)).card:=by
 classical
 unfold cosetCount; simp_rw [mem_key_iff]; rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
theorem local_bit {k m r t} (hk:0<k) (name:Bool→V k) (c:Bool→Fin (r+1)→V k)
 (gen:Fin m→V k) (rep:V k) (watch:Bool→ℕ→Fin k→Bool) (hc:closed hk watch (r+1))
 (side:Fin t→Bool) (site:Fin t→Fin k) (hw:∀ j,watch (side j) (r+1) (site j)=true)
 (h:ℕ) (target:Fin t→F) (hs:Checks hk name c gen rep watch)
 (hr:(matrix gen rep (probe hk name c side site) target).rank≤h) (o:Fin (k+1)):
 let f:=probe hk name c side site
 yF h gen (fun j=>sample gen rep (f j) (target j)) o=(cosetCount rep gen f target).testBit o.val:=by
 let f:=probe hk name c side site
 let Q:=fun j=>sample gen rep (f j) (target j)
 have ev:=(terminal_sample hk name c gen rep watch hc side site hw target hs).1
 have eq0 (a b:F):a+b=0↔a=b:=by decide +revert
 apply k6 h rep gen Q (fun w j=>f j w=target j) (fun j=>sample_valid ..) _ hr o
 intro j a
 change (sample gen rep (f j) (target j)).eval a=0↔f j (rep+shift gen a)=target j
 have he:(sample gen rep (f j) (target j)).eval a=f j (rep+shift gen a)+target j:=ev j a
 rw [he,eq0]
end PEqualNP.Outside.L_meta_27129_aux.P25940Sem
namespace PEqualNP.Outside.L_meta_27129_aux
noncomputable section
theorem jI {α:Type*} [Fintype α] {d:ℕ} (live:Fin d→Bool)
 (cell:Fin d→α→Prop) (P:α→Prop) [DecidablePred P]
 (cover:∀ w,∃! i,live i=true∧cell i w):
 (∑ i,if live i then Nat.card {w:α // cell i w∧P w} else 0)=(Finset.univ.filter P).card:=by
 classical
 let T (i:Fin d):Finset α:=Finset.univ.filter (fun w=>live i=true∧cell i w∧P w)
 have cards (i:Fin d):(if live i then Nat.card {w:α // cell i w∧P w} else 0)=(T i).card:=by
  cases hl:live i <;> simp [T,hl,Nat.card_eq_fintype_card,Fintype.card_subtype]
 have un:Finset.univ.biUnion T=Finset.univ.filter P:=by
  ext w
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,T]
  constructor
  · rintro ⟨_,_,_,hp⟩; exact hp
  · intro hp; obtain ⟨i,⟨hl,hc⟩,_⟩:=cover w; exact ⟨i,hl,hc,hp⟩
 have dis:((Finset.univ:Finset (Fin d)):Set (Fin d)).PairwiseDisjoint T:=by
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr (fun w hi hj=>?_)
  have ai:=(Finset.mem_filter.mp hi).2
  have aj:=(Finset.mem_filter.mp hj).2
  obtain ⟨s,_,hs⟩:=cover w
  exact hij ((hs i ⟨ai.1,ai.2.1⟩).trans (hs j ⟨aj.1,aj.2.1⟩).symm)
 calc
  _=∑ i,(T i).card:=Finset.sum_congr rfl (fun i _=>cards i)
  _=_:=(Finset.card_biUnion dis).symm.trans (congrArg Finset.card un)
end
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
noncomputable section
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine
open PEqualNP.Outside.L_meta_27129_aux.P25940Sample
open PEqualNP.Outside.L_meta_27129_aux.P25940Sem
open PEqualNP.Outside.L_meta_27129_aux.yo
lemma zX {U W:Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
 [AddCommGroup W] [Module F W] [Module.Finite F W]
 (f:U →ₗ[F] W) (hf:Function.Injective f) (S:Submodule F U):
 Module.finrank F (Submodule.map f S)=Module.finrank F S:=by
 let g:S →ₗ[F] W:=f.comp S.subtype
 have hgj:Function.Injective g:=hf.comp S.injective_subtype
 have hrg:LinearMap.range g=Submodule.map f S:=by
  ext w; simp [g,Submodule.mem_map]
 rw [← hrg,LinearMap.finrank_range_of_inj hgj]
def kD {k:ℕ} (v:V k):V k →ₗ[F] F where
 toFun u:=dotProduct v u
 map_add' x y:=dotProduct_add v x y
 map_smul' c x:=by simp [dotProduct_smul]
def y5 {k:ℕ}:V k →ₗ[F] (V k →ₗ[F] F) where
 toFun:=kD
 map_add' x y:=LinearMap.ext fun u=>add_dotProduct x y u
 map_smul' c x:=LinearMap.ext fun u=>by simp [kD,smul_dotProduct]
lemma kk {k:ℕ}:Function.Injective (y5 (k:=k)):=by
 intro x y h
 funext j
 have hj:=congrArg (fun f:V k →ₗ[F] F=>f (Pi.single j 1)) h
 simpa [y5,kD,dotProduct_single] using hj
lemma uj {k:ℕ}:Function.Surjective (y5 (k:=k)):=by
 have hinj:=kk (k:=k)
 apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
 simp
lemma y8 (a b c vx vy ux uy zx zy:F):
 (a+0+(b+0) * (c+0))+(a+vx+(b+ux) * (c+zx)) +
 (a+vy+(b+uy) * (c+zy))+(a+(vx+vy)+(b+(ux+uy)) * (c+(zx+zy)))=
 ux * zy+uy * zx:=by
 have h2:(2:F)=0:=by decide
 linear_combination (2 * a+vx+vy+2 * b * c+b * zx+b * zy+c * ux+c * uy+ux * zx+uy * zy) * h2
def zM {k:ℕ} (S:Submodule F (V k)):Submodule F (V k):=
 { carrier:={v:V k|∀ x∈S,dotProduct v x=0},zero_mem':=fun x _=>zero_dotProduct x,add_mem':=fun ha hb x hx=>by rw [add_dotProduct,ha x hx,hb x hx,add_zero],smul_mem':=fun c a ha x hx=>by rw [smul_dotProduct,ha x hx,smul_zero] }
lemma uZ {k:ℕ} {S:Submodule F (V k)} {v:V k}:
 v∈zM S↔∀ x∈S,dotProduct v x=0:=Iff.rfl
lemma uP {k:ℕ} {S T:Submodule F (V k)} (h:S≤T):zM T≤zM S:=
 fun _ hv x hx=>hv x (h hx)
lemma z6 {k:ℕ} (S:Submodule F (V k)):
 Module.finrank F (zM S)+Module.finrank F S=k:=by
 let res:(V k →ₗ[F] F) →ₗ[F] (S →ₗ[F] F):=
  { toFun:=fun f=>f.comp S.subtype
    map_add':=fun f g=>LinearMap.ext fun _=>rfl
    map_smul':=fun c f=>LinearMap.ext fun _=>rfl }
 have hres_surj:Function.Surjective res:=by
  intro g
  obtain ⟨T,hT⟩:=Submodule.exists_isCompl S
  let proj:V k →ₗ[F] S:=Submodule.projectionOnto S T hT
  refine ⟨g.comp proj,LinearMap.ext fun x=>?_⟩
  change g (proj x.val)=g x
  congr 1
  exact Submodule.projectionOnto_apply_left hT x
 let φ:V k →ₗ[F] (S →ₗ[F] F):=res.comp y5
 have hφ_surj:Function.Surjective φ:=hres_surj.comp uj
 have hker:LinearMap.ker φ=zM S:=by
  ext v
  simp only [LinearMap.mem_ker,uZ,φ,res,LinearMap.comp_apply]
  constructor
  · intro h x hx
    have hx':=congrArg (fun f:S →ₗ[F] F=>f ⟨x,hx⟩) h
    simpa [y5,kD] using hx'
  · intro h
    exact LinearMap.ext fun ⟨x,hx⟩=>h x hx
 have hrn:=LinearMap.finrank_range_add_finrank_ker φ
 rw [LinearMap.range_eq_top.mpr hφ_surj,finrank_top,hker] at hrn
 simp only [Module.finrank_fin_fun] at hrn
 have hdual:Module.finrank F (S →ₗ[F] F)=Module.finrank F S:=by
  rw [Module.finrank_linearMap,Module.finrank_self,mul_one]
 rw [hdual] at hrn
 omega
lemma jw {k:ℕ} (S:Submodule F (V k)):zM (zM S)=S:=by
 have hle:S≤zM (zM S):=fun s hs v hv=>by
  rw [dotProduct_comm]; exact hv s hs
 symm
 apply Submodule.eq_of_le_of_finrank_eq hle
 have h1:=z6 S
 have h2:=z6 (zM S)
 omega
lemma yw {P k:ℕ} (Q:Fin P→V k) (q:V k)
 (h:∀ u:V k,(∀ i,dotProduct (Q i) u=0)→dotProduct q u=0):
 q∈Submodule.span F (Set.range Q):=by
 rw [← jw (Submodule.span F (Set.range Q))]
 intro u hu
 apply h u
 intro i
 rw [dotProduct_comm]
 exact hu (Q i) (Submodule.subset_span ⟨i,rfl⟩)
lemma zj {k:ℕ} (A:Matrix (Fin k) (Fin k) F)
 (hsym:∀ i j,A i j=A j i) (x y:V k):
 dotProduct x (A.mulVec y)=dotProduct y (A.mulVec x):=by
 have hT:A.transpose=A:=Matrix.ext fun i j=>hsym j i
 calc dotProduct x (A.mulVec y)
  =dotProduct (A.vecMul x) y:=Matrix.dotProduct_mulVec x A y
  _=dotProduct (A.transpose.mulVec x) y:=by rw [Matrix.mulVec_transpose]
  _=dotProduct (A.mulVec x) y:=by rw [hT]
  _=dotProduct y (A.mulVec x):=dotProduct_comm _ _
lemma ks {k:ℕ} (A:Matrix (Fin k) (Fin k) F)
 (hdiag:∀ i,A i i=0) (hsym:∀ i j,A i j=A j i) (x:V k):
 dotProduct x (A.mulVec x)=0:=by
 simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
 let f:Fin k→Fin k→F:=fun i j=>x i * (A i j * x j)
 have hsymf:∀ i j,f i j=f j i:=fun i j=>by
  dsimp only [f]; rw [hsym i j]; ring
 have hdiagf:∀ i,f i i=0:=fun i=>by
  dsimp only [f]; rw [hdiag i,zero_mul,mul_zero]
 have hsplit:∀ (s:Finset (Fin k)),∑ i∈s,∑ j∈s,f i j=0:=by
  intro s
  induction s using Finset.induction_on with
  | empty=>simp
  | insert a s ha ih=>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    rw [Finset.sum_add_distrib,ih,add_zero,hdiagf a,zero_add]
    have hcongr:∑ x∈s,f x a=∑ x∈s,f a x:=Finset.sum_congr rfl (fun x _=>hsymf x a)
    rw [hcongr]
    exact qj _
 exact hsplit Finset.univ
lemma ui {k:ℕ} (A:Matrix (Fin k) (Fin k) F)
 (hdiag:∀ i,A i i=0) (hsym:∀ i j,A i j=A j i):
 ∀ n:ℕ,∀ (U:Submodule F (V k)),Module.finrank F U=n→
   ∃ a:ℕ,Module.finrank F (LinearMap.range (
     { toFun:=fun x:U=>({ toFun:=fun y:U=>dotProduct x.val (A.mulVec y.val)
                          map_add':=fun y1 y2=>by simp [Matrix.mulVec_add,dotProduct_add]
                          map_smul':=fun c y=>by simp [Matrix.mulVec_smul,dotProduct_smul] }:U →ₗ[F] F)
       map_add':=fun x1 x2=>LinearMap.ext fun y=>by simp [add_dotProduct]
       map_smul':=fun c x=>LinearMap.ext fun y=>by simp [smul_dotProduct] }:U →ₗ[F] (U →ₗ[F] F)))=2 * a:=by
 intro n
 induction n using Nat.strong_induction_on with
 | ind n ih=>
   intro U hUn
   let B:U →ₗ[F] (U →ₗ[F] F):=
    { toFun:=fun x:U=>
       { toFun:=fun y:U=>dotProduct x.val (A.mulVec y.val)
         map_add':=fun y1 y2=>by simp [Matrix.mulVec_add,dotProduct_add]
         map_smul':=fun c y=>by simp [Matrix.mulVec_smul,dotProduct_smul] }
      map_add':=fun x1 x2=>LinearMap.ext fun y=>by simp [add_dotProduct]
      map_smul':=fun c x=>LinearMap.ext fun y=>by simp [smul_dotProduct] }
   change ∃ a,Module.finrank F (LinearMap.range B)=2 * a
   by_cases hzero:∀ x y:U,B x y=0
   · refine ⟨0,?_⟩
     have hB0:B=0:=LinearMap.ext fun x=>LinearMap.ext fun y=>hzero x y
     rw [hB0,LinearMap.range_zero,finrank_bot]
   · push Not at hzero
     obtain ⟨x0,y0,hxy⟩:=hzero
     have hxy1:B x0 y0=1:=(qF _).resolve_left hxy
     have hyx1:B y0 x0=1:=by
      change dotProduct y0.val (A.mulVec x0.val)=1
      rw [zj A hsym]; exact hxy1
     have hxx0:B x0 x0=0:=ks A hdiag hsym x0.val
     have hyy0:B y0 y0=0:=ks A hdiag hsym y0.val
     let W:Submodule F (V k):=
      { carrier:={z:V k|z∈U∧dotProduct x0.val (A.mulVec z)=0∧dotProduct y0.val (A.mulVec z)=0},zero_mem':=⟨U.zero_mem,by simp,by simp⟩,add_mem':=fun ha hb=>⟨U.add_mem ha.1 hb.1,
         by rw [Matrix.mulVec_add,dotProduct_add,ha.2.1,hb.2.1,add_zero],
         by rw [Matrix.mulVec_add,dotProduct_add,ha.2.2,hb.2.2,add_zero]⟩,
        smul_mem':=fun c a ha=>⟨U.smul_mem c ha.1,
         by rw [Matrix.mulVec_smul,dotProduct_smul,ha.2.1,smul_zero],
         by rw [Matrix.mulVec_smul,dotProduct_smul,ha.2.2,smul_zero]⟩ }
     have hWU:W≤U:=fun _ hz=>hz.1
     let P:Submodule F (V k):=Submodule.span F ({x0.val,y0.val}:Set (V k))
     have hPU:P≤U:=by
      rw [Submodule.span_le]
      rintro z (rfl|rfl)
      · exact x0.property
      · exact y0.property
     have hPdim:Module.finrank F P=2:=by
      let f:Fin 2→V k:=![x0.val,y0.val]
      have hli:LinearIndependent F f:=by
       rw [Fintype.linearIndependent_iff]
       intro g hg
       have hg':g 0 • x0.val+g 1 • y0.val=0:=by
        simpa [Fin.sum_univ_two,f] using hg
       have h1:g 1=0:=by
        have:=congrArg (fun z=>dotProduct x0.val (A.mulVec z)) hg'
        simp only [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,
         smul_eq_mul,Matrix.mulVec_zero,dotProduct_zero] at this
        change g 0 * B x0 x0+g 1 * B x0 y0=0 at this
        rw [hxx0,hxy1,mul_zero,zero_add,mul_one] at this
        exact this
       have h0:g 0=0:=by
        have:=congrArg (fun z=>dotProduct y0.val (A.mulVec z)) hg'
        simp only [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,
         smul_eq_mul,Matrix.mulVec_zero,dotProduct_zero] at this
        change g 0 * B y0 x0+g 1 * B y0 y0=0 at this
        rw [hyx1,hyy0,mul_zero,add_zero,mul_one] at this
        exact this
       intro i; fin_cases i <;> assumption
      have hPeq:P=Submodule.span F (Set.range f):=by
       dsimp only [P]; congr 1; ext z; simp [f,or_comm]
      rw [hPeq,finrank_span_eq_card hli,Fintype.card_fin]
     have hdisj:P ⊓ W=⊥:=by
      rw [eq_bot_iff]
      intro z ⟨hzP,hzW⟩
      change z∈Submodule.span F ({x0.val,y0.val}:Set (V k)) at hzP
      rw [Submodule.mem_span_pair] at hzP
      obtain ⟨c1,c2,rfl⟩:=hzP
      have h1:c2=0:=by
       have:=hzW.2.1
       simp only [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,
        smul_eq_mul] at this
       change c1 * B x0 x0+c2 * B x0 y0=0 at this
       rw [hxx0,hxy1,mul_zero,zero_add,mul_one] at this
       exact this
      have h0:c1=0:=by
       have:=hzW.2.2
       simp only [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,
        smul_eq_mul] at this
       change c1 * B y0 x0+c2 * B y0 y0=0 at this
       rw [hyx1,hyy0,mul_zero,add_zero,mul_one] at this
       exact this
      simp [h0,h1]
     have hsup:P ⊔ W=U:=by
      apply le_antisymm (sup_le hPU hWU)
      intro z hz
      let c1:F:=dotProduct y0.val (A.mulVec z)
      let c2:F:=dotProduct x0.val (A.mulVec z)
      let w:V k:=z+c1 • x0.val+c2 • y0.val
      have hwW:w∈W:=by
       refine ⟨U.add_mem (U.add_mem hz (U.smul_mem c1 x0.property)) (U.smul_mem c2 y0.property),?_,?_⟩
       · simp only [w,Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,smul_eq_mul]
         change c2+c1 * B x0 x0+c2 * B x0 y0=0
         rw [hxx0,hxy1,mul_zero,add_zero,mul_one]; exact qj c2
       · simp only [w,Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,smul_eq_mul]
         change c1+c1 * B y0 x0+c2 * B y0 y0=0
         rw [hyx1,hyy0,mul_zero,add_zero,mul_one]; exact qj c1
      have hpP:c1 • x0.val+c2 • y0.val∈P:=
       P.add_mem (P.smul_mem c1 (Submodule.subset_span (Or.inl rfl)))
        (P.smul_mem c2 (Submodule.subset_span (Or.inr rfl)))
      have hzeq:(c1 • x0.val+c2 • y0.val)+w=z:=by
       funext j
       simp only [w,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
       have hr:c1 * x0.val j+c2 * y0.val j+(z j+c1 * x0.val j+c2 * y0.val j)=
        z j+(c1 * x0.val j+c1 * x0.val j)+(c2 * y0.val j+c2 * y0.val j):=by ring
       rw [hr,qj,qj,add_zero,add_zero]
      rw [← hzeq]
      exact Submodule.add_mem_sup hpP hwW
     have hdimW:Module.finrank F W+2=n:=by
      have hm:=Submodule.finrank_sup_add_finrank_inf_eq P W
      rw [hsup,hdisj,finrank_bot,add_zero,hPdim,hUn] at hm
      omega
     let BW:W →ₗ[F] (W →ₗ[F] F):=
      { toFun:=fun x:W=>
         { toFun:=fun y:W=>dotProduct x.val (A.mulVec y.val)
           map_add':=fun y1 y2=>by simp [Matrix.mulVec_add,dotProduct_add]
           map_smul':=fun c y=>by simp [Matrix.mulVec_smul,dotProduct_smul] }
        map_add':=fun x1 x2=>LinearMap.ext fun y=>by simp [add_dotProduct]
        map_smul':=fun c x=>LinearMap.ext fun y=>by simp [smul_dotProduct] }
     obtain ⟨a',ha'⟩:=ih (Module.finrank F W) (by omega) W rfl
     have hker_eq:Module.finrank F (LinearMap.ker B)=Module.finrank F (LinearMap.ker BW):=by
      let emb:W →ₗ[F] U:=Submodule.inclusion hWU
      have hemb_inj:Function.Injective emb:=Submodule.inclusion_injective hWU
      have himg:Submodule.map emb (LinearMap.ker BW)=LinearMap.ker B:=by
       ext ⟨z,hz⟩
       simp only [Submodule.mem_map,LinearMap.mem_ker,LinearMap.ext_iff,LinearMap.zero_apply]
       constructor
       · rintro ⟨⟨w,hwW⟩,hwK,heq⟩
         have hzw:w=z:=congrArg Subtype.val heq
         subst hzw
         intro ⟨u,hu⟩
         have hu':u∈P ⊔ W:=hsup.symm▸hu
         obtain ⟨p,hpP,q,hqW,rfl⟩:=Submodule.mem_sup.mp hu'
         rw [Submodule.mem_span_pair] at hpP
         obtain ⟨c1,c2,rfl⟩:=hpP
         change dotProduct w (A.mulVec (c1 • x0.val+c2 • y0.val+q))=0
         simp only [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,smul_eq_mul]
         rw [zj A hsym w x0.val,hwW.2.1,
             zj A hsym w y0.val,hwW.2.2]
         have hq0:dotProduct w (A.mulVec q)=0:=hwK ⟨q,hqW⟩
         rw [hq0]; ring
       · intro hzk
         have hzW:z∈W:=by
          refine ⟨hz,?_,?_⟩
          · rw [zj A hsym]; exact hzk x0
          · rw [zj A hsym]; exact hzk y0
         refine ⟨⟨z,hzW⟩,?_,rfl⟩
         intro ⟨q,hqW⟩
         exact hzk ⟨q,hWU hqW⟩
      rw [← himg,zX emb hemb_inj]
     have hrnB:=LinearMap.finrank_range_add_finrank_ker B
     have hrnBW:=LinearMap.finrank_range_add_finrank_ker BW
     refine ⟨a'+1,?_⟩
     change Module.finrank F (LinearMap.range BW)=2 * a' at ha'
     omega
lemma u4 {k:ℕ} (A:Matrix (Fin k) (Fin k) F)
 (hdiag:∀ i,A i i=0) (hsym:∀ i j,A i j=A j i):
 ∃ a:ℕ,A.rank=2 * a:=by
 obtain ⟨a,ha⟩:=ui A hdiag hsym k ⊤ (by simp)
 refine ⟨a,?_⟩
 rw [← ha]
 let B:(⊤:Submodule F (V k)) →ₗ[F] ((⊤:Submodule F (V k)) →ₗ[F] F):=
  { toFun:=fun x=>
     { toFun:=fun y=>dotProduct x.val (A.mulVec y.val)
       map_add':=fun y1 y2=>by simp [Matrix.mulVec_add,dotProduct_add]
       map_smul':=fun c y=>by simp [Matrix.mulVec_smul,dotProduct_smul] }
    map_add':=fun x1 x2=>LinearMap.ext fun y=>by simp [add_dotProduct]
    map_smul':=fun c x=>LinearMap.ext fun y=>by simp [smul_dotProduct] }
 change Module.finrank F (LinearMap.range A.mulVecLin)=Module.finrank F (LinearMap.range B)
 let Ψ:V k →ₗ[F] ((⊤:Submodule F (V k)) →ₗ[F] F):=
  { toFun:=fun v=>(y5 v).comp (⊤:Submodule F (V k)).subtype
    map_add':=fun u v=>LinearMap.ext fun y=>by simp [y5,kD,add_dotProduct]
    map_smul':=fun c u=>LinearMap.ext fun y=>by simp [y5,kD] }
 have hΨ_inj:Function.Injective Ψ:=by
  intro u v h
  apply kk
  exact LinearMap.ext fun y=>congrArg (fun f:(⊤:Submodule F (V k)) →ₗ[F] F=>f ⟨y,trivial⟩) h
 have hB:LinearMap.range B=Submodule.map Ψ (LinearMap.range A.mulVecLin):=by
  ext f
  simp only [LinearMap.mem_range,Submodule.mem_map]
  constructor
  · rintro ⟨⟨x,_⟩,rfl⟩
    refine ⟨A.mulVec x,⟨x,rfl⟩,LinearMap.ext fun ⟨y,_⟩=>?_⟩
    change dotProduct (A.mulVec x) y=dotProduct x (A.mulVec y)
    rw [dotProduct_comm,zj A hsym]
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨⟨x,trivial⟩,LinearMap.ext fun ⟨y,_⟩=>?_⟩
    change dotProduct x (A.mulVec y)=dotProduct (A.mulVec x) y
    rw [zj A hsym,dotProduct_comm]
 rw [hB,zX Ψ hΨ_inj]
lemma kJ {k:ℕ} (A:Matrix (Fin k) (Fin k) F)
 (hsym:∀ i j,A i j=A j i)
 (free:Fin k→Bool)
 (hzero:∀ i j,free i=false∨free j=false→A i j=0)
 {a:ℕ} (hrk:A.rank=2 * a)
 (D':Submodule F (V k))
 (hdisj:∀ u∈D',(∀ j,free j=true→u j=0)→u=0)
 (hiso:∀ x∈D',∀ y∈D',dotProduct x (A.mulVec y)=0)
 (S:Submodule F (V k)) (hS:S≤LinearMap.range A.mulVecLin)
 (hSdim:Module.finrank F S=a+1):
 a+Module.finrank F D'≤(Finset.univ.filter (fun j=>free j=true)).card∧
 ∃ q∈S,q≠0∧(∀ x∈D',dotProduct q x=0)∧(∀ j,free j=false→q j=0):=by
 let L:V k →ₗ[F] V k:=A.mulVecLin
 have hLrk:Module.finrank F (LinearMap.range L)=2 * a:=hrk
 have hLker:Module.finrank F (LinearMap.ker L)+2 * a=k:=by
  have:=LinearMap.finrank_range_add_finrank_ker L
  rw [hLrk,Module.finrank_fin_fun] at this
  omega
 have hrange_eq:LinearMap.range L=zM (LinearMap.ker L):=by
  have hle:LinearMap.range L≤zM (LinearMap.ker L):=by
   rintro _ ⟨x,rfl⟩ z hz
   change dotProduct (A.mulVec x) z=0
   rw [dotProduct_comm,zj A hsym]
   have hz0:A.mulVec z=0:=hz
   rw [hz0,dotProduct_zero]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have ho:=z6 (LinearMap.ker L)
  omega
 let Np:Submodule F (V k):=
  { carrier:={u:V k|∀ j,free j=true→u j=0},zero_mem':=fun _ _=>rfl,add_mem':=fun hx hy j hj=>by simp [hx j hj,hy j hj],smul_mem':=fun c x hx j hj=>by simp [hx j hj] }
 have hNp_ker:Np≤LinearMap.ker L:=by
  intro u hu
  change A.mulVec u=0
  funext i
  simp only [Matrix.mulVec,dotProduct,Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  cases hj:free j
  · rw [hzero i j (Or.inr hj),zero_mul]
  · rw [hu j hj,mul_zero]
 have hNp_dim:Module.finrank F Np+(Finset.univ.filter (fun j=>free j=true)).card=k:=by
  let Fset:=Finset.univ.filter (fun j:Fin k=>free j=true)
  let Pset:=Finset.univ.filter (fun j:Fin k=>free j=false)
  let e:Pset→V k:=fun j=>Pi.single j.val 1
  have hli:LinearIndependent F e:=by
   rw [Fintype.linearIndependent_iff]
   intro g hg j
   have:=congrFun hg j.val
   simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,e] at this
   rw [Finset.sum_eq_single j] at this
   · simpa using this
   · intro i _ hij
     have hne:i.val≠j.val:=fun h=>hij (Subtype.ext h)
     simp [Pi.single_eq_of_ne (Ne.symm hne)]
   · intro h; exact absurd (Finset.mem_univ _) h
  have hspan:Submodule.span F (Set.range e)=Np:=by
   apply le_antisymm
   · rw [Submodule.span_le]
     rintro _ ⟨⟨j,hj⟩,rfl⟩ i hi
     have hne:i≠j:=by
      rintro rfl
      have hfalse:=(Finset.mem_filter.mp hj).2
      rw [hi] at hfalse; exact Bool.noConfusion hfalse
     exact Pi.single_eq_of_ne hne 1
   · intro u hu
     have hu_eq:u=∑ j:Pset,u j.val • e j:=by
      funext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,e]
      cases hi:free i
      · have hiP:i∈Pset:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
        rw [Finset.sum_eq_single (⟨i,hiP⟩:Pset)]
        · simp
        · intro j _ hj
          have hne:i≠j.val:=fun h=>hj (Subtype.ext h.symm)
          simp [Pi.single_eq_of_ne hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [hu i hi]
        symm; apply Finset.sum_eq_zero; intro j _
        have hne:i≠j.val:=by
         rintro rfl
         have hfalse:=(Finset.mem_filter.mp j.2).2
         rw [hi] at hfalse; exact Bool.noConfusion hfalse
        simp [Pi.single_eq_of_ne hne]
     rw [hu_eq]
     exact Submodule.sum_mem _ (fun j _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩))
  rw [← hspan,finrank_span_eq_card hli,Fintype.card_coe]
  have hPeq:Pset=Fsetᶜ:=by ext j; simp [Pset,Fset]
  rw [hPeq,Finset.card_compl,Fintype.card_fin]
  have hle:Fset.card≤k:=by simpa using Fset.card_le_univ
  dsimp only [Fset] at hle ⊢
  omega
 let K:Submodule F (V k):=D' ⊔ LinearMap.ker L
 have hLK_le:Submodule.map L K≤zM K:=by
  rintro _ ⟨x,hxK,rfl⟩ y hyK
  obtain ⟨x1,hx1,z1,hz1,rfl⟩:=Submodule.mem_sup.mp hxK
  obtain ⟨y1,hy1,z2,hz2,rfl⟩:=Submodule.mem_sup.mp hyK
  have hz10:A.mulVec z1=0:=hz1
  have hz20:A.mulVec z2=0:=hz2
  change dotProduct (A.mulVec (x1+z1)) (y1+z2)=0
  rw [Matrix.mulVec_add,hz10,add_zero,dotProduct_add]
  have h1:dotProduct (A.mulVec x1) y1=0:=by
   rw [dotProduct_comm]; exact hiso y1 hy1 x1 hx1
  have h2:dotProduct (A.mulVec x1) z2=0:=by
   rw [dotProduct_comm,zj A hsym,hz20,dotProduct_zero]
  rw [h1,h2,add_zero]
 have hLK_dim:Module.finrank F (Submodule.map L K)+Module.finrank F (LinearMap.ker L)=
  Module.finrank F K:=by
  let LK:K →ₗ[F] V k:=L.comp K.subtype
  have hrange:LinearMap.range LK=Submodule.map L K:=by
   ext v; simp [LK,Submodule.mem_map]
  have hker_dim:Module.finrank F (LinearMap.ker LK)=Module.finrank F (LinearMap.ker L):=by
   have himg:Submodule.map K.subtype (LinearMap.ker LK)=LinearMap.ker L:=by
    ext v
    simp only [Submodule.mem_map,LinearMap.mem_ker,LK,LinearMap.comp_apply,
     Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨w,_⟩,hw,rfl⟩; exact hw
    · intro hv; exact ⟨⟨v,Submodule.mem_sup_right hv⟩,hv,rfl⟩
   rw [← himg,zX K.subtype K.injective_subtype]
  have hrn:=LinearMap.finrank_range_add_finrank_ker LK
  rw [hrange,hker_dim] at hrn
  exact hrn
 have hK_dim:Module.finrank F K≤k-a:=by
  have hle:=Submodule.finrank_mono hLK_le
  have ho:=z6 K
  omega
 have hbound:a+Module.finrank F D'≤(Finset.univ.filter (fun j=>free j=true)).card:=by
  have hDN:D' ⊓ Np=⊥:=by
   rw [eq_bot_iff]; intro u ⟨hu1,hu2⟩; exact hdisj u hu1 hu2
  have hDN_le:D' ⊔ Np≤K:=sup_le_sup_left hNp_ker D'
  have hm:=Submodule.finrank_sup_add_finrank_inf_eq D' Np
  rw [hDN,finrank_bot,add_zero] at hm
  have hmono:=Submodule.finrank_mono hDN_le
  omega
 refine ⟨hbound,?_⟩
 let oK:Submodule F (V k):=zM K
 have hoK_le:oK≤LinearMap.range L:=by
  rw [hrange_eq]; exact uP le_sup_right
 have hoK_dim:a≤Module.finrank F oK:=by
  have ho:Module.finrank F oK+Module.finrank F K=k:=z6 K
  omega
 have hsup_le:S ⊔ oK≤LinearMap.range L:=sup_le hS hoK_le
 have hsup_dim:Module.finrank F (S ⊔ oK:Submodule F (V k))≤2 * a:=
  (Submodule.finrank_mono hsup_le).trans_eq hLrk
 have hinf_pos:1≤Module.finrank F (S ⊓ oK:Submodule F (V k)):=by
  have hm:=Submodule.finrank_sup_add_finrank_inf_eq S oK
  omega
 have hne_bot:(S ⊓ oK:Submodule F (V k))≠⊥:=by
  intro hbot; rw [hbot,finrank_bot] at hinf_pos; omega
 obtain ⟨q,hqmem,hqne⟩:=Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
 refine ⟨q,hqmem.1,hqne,fun x hx=>hqmem.2 x (Submodule.mem_sup_left hx),?_⟩
 obtain ⟨v,hv⟩:=hS hqmem.1
 intro j hj
 rw [← hv]
 change (A.mulVec v) j=0
 simp only [Matrix.mulVec,dotProduct]
 apply Finset.sum_eq_zero
 intro i _
 rw [hzero j i (Or.inl hj),zero_mul]
lemma kV {k:ℕ} (v w:V k):
 (Matrix.of (fun i j=>v i * w j+v j * w i)).rank≤2:=by
 let M:Matrix (Fin k) (Fin k) F:=Matrix.of (fun i j=>v i * w j+v j * w i)
 change Module.finrank F (LinearMap.range M.mulVecLin)≤2
 let T:Submodule F (V k):=Submodule.span F ({v,w}:Set (V k))
 have hle:LinearMap.range M.mulVecLin≤T:=by
  rintro _ ⟨x,rfl⟩
  have hmx:M.mulVecLin x=(dotProduct w x) • v+(dotProduct v x) • w:=by
   funext i
   simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,M,Matrix.of_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
   congr 1 <;> (apply Finset.sum_congr rfl; intro j _; ring)
  rw [hmx]
  exact T.add_mem (T.smul_mem _ (Submodule.subset_span (Or.inl rfl)))
   (T.smul_mem _ (Submodule.subset_span (Or.inr rfl)))
 calc Module.finrank F (LinearMap.range M.mulVecLin)
  ≤Module.finrank F T:=Submodule.finrank_mono hle
  _≤2:=by
   have hT:T=Submodule.span F ((↑({v,w}:Finset (V k)):Set (V k))):=by
       dsimp only [T]; simp
   rw [hT]
   exact (finrank_span_le_card _).trans (by
       have hc:((↑({v,w}:Finset (V k)):Set (V k))).toFinset=({v,w}:Finset (V k)):=by
        ext z; simp
       rw [hc]; exact Finset.card_le_two)
lemma jx {k m:ℕ} (M:Fin m→Matrix (Fin k) (Fin k) F):
 (∑ s,M s).rank≤∑ s,(M s).rank:=by
 have hgen:∀ (S:Finset (Fin m)),(∑ s∈S,M s).rank≤∑ s∈S,(M s).rank:=by
  intro S
  induction S using Finset.induction_on with
  | empty=>
    simp only [Finset.sum_empty]
    apply le_of_eq
    change Module.finrank F (LinearMap.range (0:Matrix (Fin k) (Fin k) F).mulVecLin)=0
    have h0:(0:Matrix (Fin k) (Fin k) F).mulVecLin=0:=LinearMap.ext fun x=>Matrix.zero_mulVec x
    rw [h0,LinearMap.range_zero,finrank_bot]
  | insert a s ha ih=>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have hadd:(M a+∑ x∈s,M x).rank≤(M a).rank+(∑ x∈s,M x).rank:=by
     change Module.finrank F (LinearMap.range (M a+∑ x∈s,M x).mulVecLin)≤
      Module.finrank F (LinearMap.range (M a).mulVecLin) +
      Module.finrank F (LinearMap.range (∑ x∈s,M x).mulVecLin)
     have hle:LinearMap.range (M a+∑ x∈s,M x).mulVecLin≤
      LinearMap.range (M a).mulVecLin ⊔ LinearMap.range (∑ x∈s,M x).mulVecLin:=by
      rintro _ ⟨x,rfl⟩
      rw [Matrix.mulVecLin_apply,Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩
     have hm:=Submodule.finrank_mono hle
     have hs:=Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (M a).mulVecLin) (LinearMap.range (∑ x∈s,M x).mulVecLin)
     omega
    omega
 exact hgen Finset.univ
lemma kc {k:ℕ} (v w:V k) (D':Submodule F (V k))
 (h:∀ x∈D',∀ y∈D',dotProduct v x * dotProduct w y+dotProduct v y * dotProduct w x=0):
 (∀ x∈D',dotProduct v x=0)∨(∀ x∈D',dotProduct w x=0)∨
   (∀ x∈D',dotProduct (v+w) x=0):=by
 by_cases hv:∀ x∈D',dotProduct v x=0
 · exact Or.inl hv
 by_cases hw:∀ x∈D',dotProduct w x=0
 · exact Or.inr (Or.inl hw)
 right; right
 push Not at hv hw
 obtain ⟨x0,hx0,hv0⟩:=hv
 obtain ⟨y0,hy0,hw0⟩:=hw
 have hv1:dotProduct v x0=1:=(qF _).resolve_left hv0
 have hw1:dotProduct w y0=1:=(qF _).resolve_left hw0
 have hxy:=h x0 hx0 y0 hy0
 rw [hv1,hw1,one_mul] at hxy
 have hwx1:dotProduct w x0=1:=by
  rcases qF (dotProduct w x0) with h0|h1
  · rw [h0,mul_zero,add_zero] at hxy; exact absurd hxy one_ne_zero
  · exact h1
 intro z hz
 rw [add_dotProduct]
 have hzx:=h x0 hx0 z hz
 rw [hv1,hwx1,one_mul,mul_one,add_comm] at hzx
 exact hzx
def zu {N n:ℕ} (cond:Fin n→Sig N):ℕ→Sig N
 | 0=>fun _=>false
 | m+1=>if hm:m<n then fun x=>zu cond m x||cond ⟨m,hm⟩ x else zu cond m
lemma jn {N n:ℕ} (cond:Fin n→Sig N) (m:ℕ) (hm:m≤n) (x:Fin N→Bool):
 zu cond m x=((List.finRange n).filter (fun j=>decide (j.val< m))).any (fun j=>cond j x):=by
 induction m with
 | zero=>
   simp [zu]
 | succ m ih=>
   have hmn:m<n:=by omega
   simp only [zu,hmn,↓reduceDIte,ih (by omega)]
   apply Bool.eq_iff_iff.mpr
   simp only [Bool.or_eq_true,List.any_eq_true,List.mem_filter,List.mem_finRange,true_and,
    decide_eq_true_eq]
   constructor
   · rintro (⟨j,hj,hc⟩|hc)
     · exact ⟨j,by omega,hc⟩
     · exact ⟨⟨m,hmn⟩,show m< m+1 by omega,hc⟩
   · rintro ⟨j,hj,hc⟩
     by_cases hjm:j.val< m
     · exact Or.inl ⟨j,hjm,hc⟩
     · have hje:j=⟨m,hmn⟩:=Fin.ext (show j.val=m by omega)
       exact Or.inr (hje▸hc)
theorem yk {N n:ℕ} {A:Set (Sig N)} (cond:Fin n→Sig N)
 (hfalse:(fun _=>false)∈A)
 (hcond:∀ i:Fin n,cond i∈A):
 qa A (Set.range (fun i:Fin n=>fun x=>qi (fun j=>cond j x) i)) (3 * n):=by
 have hpref:∀ m≤n,qa A {f|∃ j:Fin n,j.val< m∧zu cond j.val=f} m:=by
  intro m
  induction m with
  | zero=>
    intro _
    exact zk (by rintro _ ⟨j,hj,_⟩; omega)
  | succ m ih=>
    intro hm
    have hprev:=ih (by omega)
    cases m with
    | zero=>
      have h0:{f|∃ j:Fin n,j.val<1∧zu cond j.val=f}⊆A:=by
       rintro f ⟨j,hj,rfl⟩
       have hj0:j.val=0:=by omega
       rw [hj0]; exact hfalse
      exact qd (zk h0) le_rfl Set.subset_union_right (by omega)
    | succ m'=>
      have hlt:m'<n:=by omega
      let prevSig:Sig N:=zu cond m'
      have hprev_mem:prevSig∈A ∪ {f|∃ j:Fin n,j.val< m'+1∧zu cond j.val=f}:=
       Or.inr ⟨⟨m',hlt⟩,show m'< m'+1 by omega,rfl⟩
      have hstep:qa (A ∪ {f|∃ j:Fin n,j.val< m'+1∧zu cond j.val=f})
       {zu cond (m'+1)} 1:=by
       have heq:zu cond (m'+1)=fun x=>prevSig x||cond ⟨m',hlt⟩ x:=by
        funext x; simp [zu,hlt,prevSig]
       rw [heq]
       exact orB hprev_mem (Or.inl (hcond ⟨m',hlt⟩))
      refine qd (zd hprev hstep) le_rfl ?_ (by omega)
      rintro f ⟨j,hj,rfl⟩
      by_cases hjm:j.val< m'+1
      · exact Or.inr (Or.inl ⟨j,hjm,rfl⟩)
      · have hje:j.val=m'+1:=by omega
        rw [hje]; exact Or.inr (Or.inr rfl)
 have hpAll:qa A (Set.range (fun i:Fin n=>zu cond i.val)) n:=by
  refine qd (hpref n le_rfl) le_rfl ?_ le_rfl
  rintro _ ⟨i,rfl⟩
  exact Or.inr ⟨i,i.isLt,rfl⟩
 let A1:=A ∪ Set.range (fun i:Fin n=>zu cond i.val)
 have hft:qa A1 (Set.range (fun i:Fin n=>fun x=>qi (fun j=>cond j x) i)) (n * 2):=by
  refine qf _ 2 (fun i=>?_)
  have hn:qa A1 {fun x=>!(zu cond i.val x)} 1:=zn (Or.inr ⟨i,rfl⟩)
  have ha:qa (A1 ∪ {fun x=>!(zu cond i.val x)})
   {fun x=>cond i x&&!(zu cond i.val x)} 1:=
   qD (Or.inl (Or.inl (hcond i))) (Or.inr rfl)
  have heq:(fun x=>cond i x&&!(zu cond i.val x))=
   (fun x=>qi (fun j=>cond j x) i):=by
   funext x
   simp only [qi,jn cond i.val (le_of_lt i.isLt) x]
  rw [heq] at ha
  exact qd (qe hn ha) le_rfl Set.subset_union_right (by omega)
 exact qd (qe hpAll hft) le_rfl Set.subset_union_right (by omega)
def vL {d k:ℕ} (sel:Fin d→Bool) (vecs:Fin d→V k) (j:Fin k):F:=
 b2z ((List.finRange d).any (fun i=>sel i&&z2b (vecs i j)))
lemma kl {d k:ℕ} (sel:Fin d→Bool) (vecs:Fin d→V k)
 (i0:Fin d) (h1:sel i0=true) (huniq:∀ i,sel i=true→i=i0):
 vL sel vecs=vecs i0:=by
 funext j
 unfold vL
 have hany:(List.finRange d).any (fun i=>sel i&&z2b (vecs i j))=z2b (vecs i0 j):=by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true]
  constructor
  · rintro ⟨i,hi,hv⟩
    rw [huniq i hi] at hv; exact hv
  · intro hv
    exact ⟨i0,h1,hv⟩
 rw [hany,vr]
theorem kT {N d k:ℕ} {A:Set (Sig N)}
 (hfalse:(fun _=>false)∈A)
 (sel:Fin d→Sig N) (vecs:Fin d→In N→V k)
 (hsel:∀ i,sel i∈A) (hvecs:∀ i j,(fun x=>z2b (vecs i x j))∈A):
 qa A (Set.range (fun j:Fin k=>fun x=>z2b (vL (fun i=>sel i x) (fun i=>vecs i x) j)))
  (k * (2 * d)):=by
 refine qf _ (2 * d) (fun j=>?_)
 let term:Fin d→Sig N:=fun i x=>sel i x&&z2b (vecs i x j)
 have h1:qa A (Set.range term) (d * 1):=
  qf term 1 (fun i=>qD (hsel i) (hvecs i j))
 have h2:qa (A ∪ Set.range term) {fun x=>(List.finRange d).any (fun i=>term i x)} d:=
  vC term (fun i=>Or.inr ⟨i,rfl⟩) (Or.inl hfalse)
 have heq:(fun x=>(List.finRange d).any (fun i=>term i x))=
  (fun x=>z2b (vL (fun i=>sel i x) (fun i=>vecs i x) j)):=by
  funext x; simp [vL,term,z0]
 rw [heq] at h2
 exact qd (qe h1 h2) le_rfl Set.subset_union_right (by omega)
def uY (m:ℕ) (idx:ℕ) (s:Fin m):F:=
 if idx.testBit s.val then 1 else 0
def zi:∀ {m:ℕ},(Fin m→F)→ℕ
 | 0,_=>0
 | m+1,v=>zi (fun i:Fin m=>v i.castSucc)+(if v (Fin.last m)=0 then 0 else 2 ^ m)
lemma y3:∀ {m:ℕ} (v:Fin m→F),zi v<2 ^ m
 | 0,_=>by simp [zi]
 | m+1,v=>by
   simp only [zi]
   have ih:=y3 (fun i:Fin m=>v i.castSucc)
   have hpow:2 ^ (m+1)=2 ^ m+2 ^ m:=by rw [Nat.pow_succ]; omega
   split_ifs <;> omega
lemma vm:∀ {m:ℕ} (v:Fin m→F) (s:Fin m),
 (zi v).testBit s.val=z2b (v s)
 | 0,_,s=>s.elim0
 | m+1,v,s=>by
   simp only [zi]
   have hlt:=y3 (fun i:Fin m=>v i.castSucc)
   by_cases hs:s.val< m
   · have hsc:s=(⟨s.val,hs⟩:Fin m).castSucc:=Fin.ext rfl
     have hih:=vm (fun i:Fin m=>v i.castSucc) ⟨s.val,hs⟩
     rw [hsc]
     split_ifs with hlast
     · rw [Nat.add_zero]; exact hih
     · simp only [Fin.val_castSucc]
       rw [Nat.add_comm,vY hs]; exact hih
   · have hse:s=Fin.last m:=Fin.ext (by simp [Fin.last]; omega)
     rw [hse]
     simp only [Fin.val_last]
     split_ifs with hlast
     · rw [Nat.add_zero,hlast,qm]
       exact Nat.testBit_eq_false_of_lt hlt
     · have hv1:v (Fin.last m)=1:=(qF _).resolve_left hlast
       rw [hv1,zA]
       have hadd:(zi (fun i:Fin m=>v i.castSucc)+2 ^ m) / 2 ^ m=1:=by
        rw [Nat.add_div_right _ (Nat.two_pow_pos m),Nat.div_eq_of_lt hlt]
       rw [qB,hadd]; decide
lemma yg {m:ℕ} {v:Fin m→F} (hv:v≠0):0<zi v:=by
 by_contra h0
 have heq:zi v=0:=by omega
 apply hv
 funext s
 have hb:=vm v s
 rw [heq,Nat.zero_testBit] at hb
 have hz:v s=0:=by
  rcases qF (v s) with h|h
  · exact h
  · rw [h,zA] at hb; exact Bool.noConfusion hb
 exact hz
lemma jL {m:ℕ} (v:Fin m→F):
 uY m (zi v)=v:=by
 funext s
 unfold uY
 rw [vm]
 rcases qF (v s) with h|h <;> simp [h,qm,zA]
lemma k2 {R C P1 P2:ℕ}
 (M0:Fin R→Fin C→ZMod 2) (Pay1:Fin R→Fin P1→ZMod 2) (Pay2:Fin R→Fin P2→ZMod 2):
 (qA M0 Pay1).used=(qA M0 Pay2).used∧
 (qA M0 Pay1).M=(qA M0 Pay2).M:=by
 have hloop:∀ t,
  ((List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay1⟩).used=
  ((List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay2⟩).used∧
  ((List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay1⟩).M=
  ((List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay2⟩).M:=by
  intro t
  induction t with
  | zero=>exact ⟨rfl,rfl⟩
  | succ t ih=>
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    set s1:=(List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay1⟩
    set s2:=(List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,Pay2⟩
    obtain ⟨hu,hM⟩:=ih
    by_cases ht:t<C
    · simp [qu,ht,hu,hM]
    · simp only [qu,ht,↓reduceDIte]
      exact ⟨hu,hM⟩
 exact hloop C
theorem kN {R C P:ℕ}
 (M0:Fin R→Fin C→ZMod 2) (Pay0:Fin R→Fin P→ZMod 2):
 let st:=qA M0 Pay0
 LinearIndependent F (fun u:{r:Fin R // st.used r=true}=>M0 u.val):=by
 classical
 intro st
 let idPay:Fin R→Fin R→F:=fun r s=>if r=s then 1 else 0
 have heq:=k2 M0 Pay0 idPay
 let stI:=qA M0 idPay
 have hloop:∀ t≤C,
  let s:=(List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,idPay⟩
  (∀ r,s.M r=∑ j:Fin R,s.Pay r j • M0 j)∧
  (∀ r j,s.used j=false→s.Pay r j=if r=j then 1 else 0):=by
  intro t
  induction t with
  | zero=>
    intro _
    refine ⟨fun r=>?_,fun r j _=>rfl⟩
    simp [idPay]
  | succ t ih=>
    intro ht
    obtain ⟨hM,hP⟩:=ih (by omega)
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    set s:=(List.range t).foldl (fun st col=>qu col st) ⟨fun _=>false,M0,idPay⟩
    have htc:t<C:=by omega
    rcases kE t htc s with ⟨hused,hnone,hsome⟩
    let cond:Fin R→Bool:=fun r=>!(s.used r)&&z2b (s.M r ⟨t,htc⟩)
    by_cases hex:∃ r,cond r=true
    · obtain ⟨p0,hp0⟩:=(q0 cond).mpr hex
      obtain ⟨hp0M,hp0P,hoth⟩:=hsome p0 hp0
      refine ⟨fun r=>?_,fun r j hj=>?_⟩
      · by_cases hr:r=p0
        · rw [hr,hp0M,hp0P]; exact hM p0
        · obtain ⟨hrM,hrP⟩:=hoth r hr
          rw [hrM,hrP,hM r,hM p0]
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,Finset.sum_add_distrib,
           Finset.smul_sum,mul_smul]
      · have hj_s:s.used j=false∧j≠p0:=by
         have hn:(qu t s).used j≠true:=by rw [hj]; decide
         have h1:=mt (hused j).mpr hn
         push Not at h1
         have hjs:s.used j=false:=by cases hx:s.used j <;> simp_all
         refine ⟨hjs,fun he=>?_⟩
         rw [he] at h1; exact h1.2 hp0
        by_cases hr:r=p0
        · rw [hr,hp0P]; exact hP p0 j hj_s.1
        · obtain ⟨_,hrP⟩:=hoth r hr
          rw [hrP,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hP r j hj_s.1,hP p0 j hj_s.1]
          simp [Ne.symm hj_s.2]
    · push Not at hex
      have hallf:∀ r,cond r=false:=fun r=>by cases h:cond r <;> simp_all
      rw [hnone hallf]
      exact ⟨hM,hP⟩
 obtain ⟨hMfull,hPfull⟩:=hloop C le_rfl
 change ∀ r,stI.M r=∑ j:Fin R,stI.Pay r j • M0 j at hMfull
 change ∀ r j,stI.used j=false→stI.Pay r j=if r=j then 1 else 0 at hPfull
 let U:={r:Fin R // st.used r=true}
 have hspan_le:Submodule.span F (Set.range stI.M)≤Submodule.span F (Set.range (fun u:U=>M0 u.val)):=by
  rw [Submodule.span_le]
  rintro _ ⟨r,rfl⟩
  by_cases hr:stI.used r=true
  · rw [hMfull r]
    apply Submodule.sum_mem
    intro j _
    by_cases hj:stI.used j=true
    · have hj':st.used j=true:=heq.1.symm▸hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j,hj'⟩,rfl⟩)
    · have hjf:stI.used j=false:=by cases h:stI.used j <;> simp_all
      have hne:r≠j:=fun h=>by subst h; rw [hr] at hjf; exact Bool.noConfusion hjf
      rw [hPfull r j hjf,ite_eq_right hne,zero_smul]
      exact Submodule.zero_mem _
  · have hrf:stI.used r=false:=by cases h:stI.used r <;> simp_all
    have h0:=(qv M0 idPay).2.2.1 r hrf
    have hr0:stI.M r=0:=funext h0
    rw [hr0]; exact Submodule.zero_mem _
 have hspEq:Submodule.span F (Set.range stI.M)=Submodule.span F (Set.range M0):=
  (qv M0 idPay).1
 rw [hspEq] at hspan_le
 have hcard:Fintype.card U=Module.finrank F (Submodule.span F (Set.range M0)):=by
  have hrk:=zw M0 Pay0
  have hUeq:Fintype.card U=(Finset.univ.filter (fun r:Fin R=>st.used r=true)).card:=by
   rw [Fintype.card_subtype]
  rw [hUeq]; exact hrk
 have hfin_ge:Fintype.card U≤Module.finrank F (Submodule.span F (Set.range (fun u:U=>M0 u.val))):=by
  rw [hcard]; exact Submodule.finrank_mono hspan_le
 have hfin_le:Module.finrank F (Submodule.span F (Set.range (fun u:U=>M0 u.val)))≤Fintype.card U:=
  finrank_span_le_card _ |>.trans (by
   calc (Set.range (fun u:U=>M0 u.val)).toFinset.card
    =(Finset.univ.image (fun u:U=>M0 u.val)).card:=by congr 1; ext x; simp
    _≤Fintype.card U:=Finset.card_image_le)
 have hfin_eq:Module.finrank F (Submodule.span F (Set.range (fun u:U=>M0 u.val)))=Fintype.card U:=
  le_antisymm hfin_le hfin_ge
 let φ:(U→F) →ₗ[F] Submodule.span F (Set.range (fun u:U=>M0 u.val)):=
  { toFun:=fun g=>⟨∑ u:U,g u • M0 u.val,
     Submodule.sum_mem _ (fun u _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨u,rfl⟩))⟩
    map_add':=fun g1 g2=>Subtype.ext (by simp [add_smul,Finset.sum_add_distrib])
    map_smul':=fun c g=>Subtype.ext (by simp [Finset.smul_sum,mul_smul]) }
 have hφ_surj:Function.Surjective φ:=by
  rintro ⟨y,hy⟩
  rw [Submodule.mem_span_range_iff_exists_fun F] at hy
  obtain ⟨g,rfl⟩:=hy
  exact ⟨g,rfl⟩
 have hφ_inj:Function.Injective φ:=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Module.finrank_fintype_fun_eq_card,hfin_eq])).mpr hφ_surj
 rw [Fintype.linearIndependent_iff]
 intro g hg
 have h0:φ g=0:=Subtype.ext hg
 have hgeq:g=0:=hφ_inj (h0.trans (map_zero φ).symm)
 intro u; exact congrFun hgeq u
def q1 {R:ℕ} (used:Fin R→Bool) (r:Fin R):ℕ:=
 (Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r)).card
def vl {R C L:ℕ} (used:Fin R→Bool) (M:Fin R→Fin C→F)
    (s:Fin L) (c:Fin C):F:=
 b2z ((List.finRange R).any (fun r=>used r&&decide (q1 used r=s.val)&&z2b (M r c)))
lemma kH {R:ℕ} (used:Fin R→Bool) {r1 r2:Fin R}
 (h1:used r1=true) (h2:used r2=true) (heq:q1 used r1=q1 used r2):
 r1=r2:=by
 by_contra hne
 rcases lt_or_gt_of_ne hne with hlt|hgt
 · have hss:Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r1) ⊂
    Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r2):=by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx=>?_,fun h=>?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
      exact ⟨hx.1,lt_trans hx.2 hlt⟩
    · have hm:r1∈Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r1):=by
       rw [h]; simp [h1,hlt]
      simp at hm
   have:=Finset.card_lt_card hss
   dsimp only [q1] at heq; omega
 · have hss:Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r2) ⊂
    Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r1):=by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx=>?_,fun h=>?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
      exact ⟨hx.1,lt_trans hx.2 hgt⟩
    · have hm:r2∈Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r2):=by
       rw [h]; simp [h2,hgt]
      simp at hm
   have:=Finset.card_lt_card hss
   dsimp only [q1] at heq; omega
lemma kp {R:ℕ} (used:Fin R→Bool) (s:ℕ)
 (hs:s<(Finset.univ.filter (fun r:Fin R=>used r=true)).card):
 ∃ r:Fin R,used r=true∧q1 used r=s:=by
 classical
 let U:=Finset.univ.filter (fun r:Fin R=>used r=true)
 let f:U→Fin U.card:=fun r=>⟨q1 used r.val,by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun x hx=>?_,fun h=>?_⟩
  · simp only [U,Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢; exact hx.1
  · have hm:r.val∈Finset.univ.filter (fun r':Fin R=>used r'=true∧r'<r.val):=by
     rw [h]; exact r.2
    simp at hm⟩
 have hinj:Function.Injective f:=fun r1 r2 h=>by
  apply Subtype.ext
  exact kH used (Finset.mem_filter.mp r1.2).2 (Finset.mem_filter.mp r2.2).2 (congrArg Fin.val h)
 have hbij:Function.Bijective f:=
  (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,by simp⟩
 obtain ⟨r,hr⟩:=hbij.2 ⟨s,hs⟩
 exact ⟨r.val,(Finset.mem_filter.mp r.2).2,congrArg Fin.val hr⟩
lemma k0 {R C L:ℕ} (used:Fin R→Bool) (M:Fin R→Fin C→F)
 (hcard:L≤(Finset.univ.filter (fun r:Fin R=>used r=true)).card):
 ∃ pick:Fin L→Fin R,Function.Injective pick∧
   (∀ s,used (pick s)=true)∧(∀ s,vl used M s=M (pick s)):=by
 have hex:∀ s:Fin L,∃ r:Fin R,used r=true∧q1 used r=s.val:=
  fun s=>kp used s.val (lt_of_lt_of_le s.isLt hcard)
 choose pick hused hbef using hex
 refine ⟨pick,?_,hused,fun s=>?_⟩
 · intro s1 s2 h
   apply Fin.ext
   rw [← hbef s1,← hbef s2,h]
 · funext c
   unfold vl
   have hany:(List.finRange R).any (fun r=>used r&&decide (q1 used r=s.val)&&z2b (M r c))=
    z2b (M (pick s) c):=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨r,⟨hr1,hr2⟩,hrc⟩
      have heq:r=pick s:=kH used hr1 (hused s) (hr2.trans (hbef s).symm)
      rwa [← heq]
    · intro hrc
      exact ⟨pick s,⟨hused s,hbef s⟩,hrc⟩
   rw [hany,vr]
theorem u3 {N R C L:ℕ} (Base:Set (Sig N))
 (hF:(fun _=>false)∈Base) (hT:(fun _=>true)∈Base)
 (used:In N→Fin R→Bool) (M:In N→Fin R→Fin C→F)
 (hused:∀ r,(fun x=>used x r)∈Base)
 (hM:∀ r c,(fun x=>z2b (M x r c))∈Base):
 qa Base {f|∃ (s:Fin L) (c:Fin C),(fun x=>z2b (vl (used x) (M x) s c))=f}
  (R * (R * ((R+1) * 4))+L * (C * (R * 3))):=by
 let bef:Fin R→Fin (R+1)→Sig N:=fun r a x=>
  zC (fun r':Fin R=>if r'<r then used x r' else false) a
 have hbef:qa Base (⋃ r:Fin R,Set.range (bef r)) (R * (R * ((R+1) * 4))):=by
  refine v7 _ _ (fun r=>?_)
  refine v3 Base hF hT (fun x r'=>if r'<r then used x r' else false) (fun r'=>?_)
  by_cases h:r'<r <;> simp [h]
  · exact hused r'
  · exact hF
 have hbef_eq:∀ r (a:Fin (R+1)) x,bef r a x=decide (a.val=q1 (used x) r):=by
  intro r a x
  simp only [bef,vh,q1]
  have hset:Finset.univ.filter (fun j:Fin R=>(if j<r then used x j else false)=true)=
   Finset.univ.filter (fun r':Fin R=>used x r'=true∧r'<r):=by
   ext r'; by_cases h:r'<r <;> simp [h]
  rw [hset]
  rfl
 let A1:=Base ∪ ⋃ r:Fin R,Set.range (bef r)
 have hpack:qa A1 {f|∃ (s:Fin L) (c:Fin C),(fun x=>z2b (vl (used x) (M x) s c))=f}
  (L * (C * (R * 3))):=by
  refine qT _ (R * 3) (fun s c=>?_)
  by_cases hs:s.val<R+1
  · let term:Fin R→Sig N:=fun r x=>
     (used x r&&decide (q1 (used x) r=s.val))&&z2b (M x r c)
    have ht:qa A1 (Set.range term) (R * 2):=by
     refine qf term 2 (fun r=>?_)
     have hEq:(fun x=>decide (q1 (used x) r=s.val))∈A1:=by
      have:(fun x=>decide (q1 (used x) r=s.val))=bef r ⟨s.val,hs⟩:=by
       funext x; rw [hbef_eq]; simp [eq_comm]
      rw [this]; exact Or.inr (Set.mem_iUnion.mpr ⟨r,⟨⟨s.val,hs⟩,rfl⟩⟩)
     have h1:qa A1 {fun x=>used x r&&decide (q1 (used x) r=s.val)} 1:=
      qD (Or.inl (hused r)) hEq
     have h2:qa (A1 ∪ {fun x=>used x r&&decide (q1 (used x) r=s.val)}) {term r} 1:=
      qD (Or.inr rfl) (Or.inl (Or.inl (hM r c)))
     exact qd (qe h1 h2) le_rfl Set.subset_union_right (by omega)
    have hor:qa (A1 ∪ Set.range term) {fun x=>(List.finRange R).any (fun r=>term r x)} R:=
     vC term (fun r=>Or.inr ⟨r,rfl⟩) (Or.inl (Or.inl hF))
    have heq:(fun x=>(List.finRange R).any (fun r=>term r x))=
     (fun x=>z2b (vl (used x) (M x) s c)):=by
     funext x; simp [vl,term,z0]
    rw [heq] at hor
    exact qd (qe ht hor) le_rfl Set.subset_union_right (by omega)
  · have hzero:(fun x=>z2b (vl (used x) (M x) s c))=(fun _=>false):=by
     funext x
     unfold vl
     rw [z0,List.any_eq_false]
     intro r _
     have hle:q1 (used x) r≤R:=by
      unfold q1
      simpa using (Finset.univ.filter (fun r':Fin R=>used x r'=true∧r'<r)).card_le_univ
     have hne:q1 (used x) r≠s.val:=by omega
     simp [hne]
    rw [hzero]
    exact qd (zk (Set.singleton_subset_iff.mpr (Or.inl hF))) le_rfl Set.subset_union_right (Nat.zero_le _)
 exact qd (qe hbef hpack) le_rfl Set.subset_union_right le_rfl
def qb {P k:ℕ} (Q:Fin P→V k) (c:Fin k) (j:Fin k):F:=
 if qh Q c then
  if j=c then 1
  else b2z ((List.finRange P).any (fun r=>vg Q r j&&z2b ((qx Q).M r c)))
 else 0
lemma zJ {P k:ℕ} (Q:Fin P→V k) {c:Fin k} (hc:qh Q c=false):
 qb Q c=0:=by
 funext j; simp [qb,hc]
lemma zz {P k:ℕ} (Q:Fin P→V k) {c j:Fin k}
 (hc:qh Q c=true) (hj:qh Q j=true):
 qb Q c j=if j=c then 1 else 0:=by
 simp only [qb,hc,↓reduceIte]
 split_ifs with heq
 · rfl
 · have hnone:∀ r:Fin P,vg Q r j=false:=by
    intro r
    have hspec:=(zD Q j).mp hj
    cases hp:vg Q r j
    · rfl
    · exfalso
      have hu:(qx Q).used r=true:=(vQ Q r).mp ⟨j,hp⟩
      let u:vu Q:=⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩
      exact hspec ⟨u,yR Q u hp⟩
   simp [hnone,b2z]
lemma k7 {P k:ℕ} (Q:Fin P→V k) {c:Fin k}
 (hc:qh Q c=true) (r:vu Q):
 qb Q c (qN Q r)=(qx Q).M r.val c:=by
 have hne:qN Q r≠c:=by
  rintro rfl
  exact (zD Q (qN Q r)).mp hc ⟨r,rfl⟩
 simp only [qb,hc,↓reduceIte,hne]
 have hany:(List.finRange P).any (fun s=>vg Q s (qN Q r)&&z2b ((qx Q).M s c))=
  z2b ((qx Q).M r.val c):=by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true]
  constructor
  · rintro ⟨s,hs1,hs2⟩
    have hsu:(qx Q).used s=true:=(vQ Q s).mp ⟨qN Q r,hs1⟩
    let u:vu Q:=⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsu⟩⟩
    have hcol:qN Q u=qN Q r:=yR Q u hs1
    have hsr:s=r.val:=congrArg Subtype.val (um Q hcol)
    rwa [← hsr]
  · intro hrc
    exact ⟨r.val,yD Q r,hrc⟩
 rw [hany,vr]
lemma kb {P k:ℕ} (Q:Fin P→V k) (c:Fin k) (s:Fin P):
 dotProduct ((qx Q).M s) (qb Q c)=0:=by
 cases hc:qh Q c
 · rw [zJ Q hc,dotProduct_zero]
 · by_cases hs:(qx Q).used s=true
   · let su:vu Q:=⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩
     have hsum:dotProduct ((qx Q).M s) (qb Q c)=
      (qx Q).M s c * qb Q c c+(qx Q).M s (qN Q su) * qb Q c (qN Q su):=by
      unfold dotProduct
      have hne:c≠qN Q su:=by
       rintro rfl
       exact (zD Q (qN Q su)).mp hc ⟨su,rfl⟩
      have hzero:∀ j:Fin k,j≠c→j≠qN Q su→(qx Q).M s j * qb Q c j=0:=by
       intro j hjc hjsu
       cases hjf:qh Q j
       · have hex:∃ r:vu Q,qN Q r=j:=by
          by_contra hn
          have:=(zD Q j).mpr hn
          rw [hjf] at this; exact Bool.noConfusion this
         obtain ⟨r,rfl⟩:=hex
         have hne_sr:s≠r.val:=fun h=>hjsu (by
          have:su=r:=Subtype.ext h
          rw [this])
         rw [(zB Q r).2 s hne_sr,zero_mul]
       · rw [zz Q hc hjf,ite_eq_right hjc,mul_zero]
      have hpair:∑ j∈({c,qN Q su}:Finset (Fin k)),(qx Q).M s j * qb Q c j=
       ∑ j:Fin k,(qx Q).M s j * qb Q c j:=by
       apply Finset.sum_subset (Finset.subset_univ _)
       intro j _ hj
       simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
       exact hzero j hj.1 hj.2
      rw [← hpair,Finset.sum_pair hne]
     rw [hsum,zz Q hc hc,ite_eq_left rfl,mul_one,
         (zB Q su).1,one_mul,k7 Q hc su]
     exact qj _
   · have hsf:(qx Q).used s=false:=by cases h:(qx Q).used s <;> simp_all
     have h0:(qx Q).M s=0:=funext ((qv Q (fun _=>Fin.elim0)).2.2.1 s hsf)
     rw [h0,zero_dotProduct]
lemma qy {P k:ℕ} (Q:Fin P→V k) (c:Fin k) (i:Fin P):
 dotProduct (Q i) (qb Q c)=0:=by
 have hmem:Q i∈Submodule.span F (Set.range (qx Q).M):=by
  rw [(qv Q (fun _=>Fin.elim0)).1]
  exact Submodule.subset_span ⟨i,rfl⟩
 have hor:qb Q c∈zM (Submodule.span F (Set.range (qx Q).M)):=by
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨s,rfl⟩
    rw [dotProduct_comm]; exact kb Q c s
  · exact dotProduct_zero _
  · intro x y _ _ hx hy; rw [dotProduct_add,hx,hy,add_zero]
  · intro a x _ hx; rw [dotProduct_smul,hx,smul_zero]
 rw [dotProduct_comm]
 exact hor (Q i) hmem
lemma qV {P k:ℕ} (Q:Fin P→V k) {u:V k}
 (hu:∀ i,dotProduct (Q i) u=0):
 shift (qb Q) u=u:=by
 have hu_st:∀ s:Fin P,dotProduct ((qx Q).M s) u=0:=by
  intro s
  have hmem:(qx Q).M s∈Submodule.span F (Set.range Q):=by
   rw [← (qv Q (fun _=>Fin.elim0)).1]
   exact Submodule.subset_span ⟨s,rfl⟩
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨i,rfl⟩; exact hu i
  · exact zero_dotProduct u
  · intro x y _ _ hx hy; rw [add_dotProduct,hx,hy,add_zero]
  · intro a x _ hx; rw [smul_dotProduct,hx,smul_zero]
 let v:=shift (qb Q) u
 have hv_st:∀ s:Fin P,dotProduct ((qx Q).M s) v=0:=by
  intro s
  dsimp only [v,shift]
  rw [dotProduct_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [dotProduct_smul,kb Q c s,smul_zero]
 have hw_free:∀ j:Fin k,qh Q j=true→(u+v) j=0:=by
  intro j hj
  have hvj:v j=u j:=by
   simp only [v,shift,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
   rw [Finset.sum_eq_single j]
   · rw [zz Q hj hj,ite_eq_left rfl,mul_one]
   · intro c _ hcj
     cases hc:qh Q c
     · rw [zJ Q hc,Pi.zero_apply,mul_zero]
     · rw [zz Q hc hj,ite_eq_right (Ne.symm hcj),mul_zero]
   · intro h; exact absurd (Finset.mem_univ _) h
  simp only [Pi.add_apply,hvj,qj]
 have hw_zero:u+v=0:=by
  funext j
  cases hj:qh Q j
  · have hex:∃ r:vu Q,qN Q r=j:=by
     by_contra hn
     have:=(zD Q j).mpr hn
     rw [hj] at this; exact Bool.noConfusion this
    obtain ⟨r,rfl⟩:=hex
    have hdot:dotProduct ((qx Q).M r.val) (u+v)=0:=by
     rw [dotProduct_add,hu_st r.val,hv_st r.val,add_zero]
    change (u+v) (qN Q r)=0
    rw [← hdot]
    unfold dotProduct
    symm
    rw [Finset.sum_eq_single (qN Q r)]
    · rw [(zB Q r).1,one_mul]
    · intro c _ hcr
      cases hc:qh Q c
      · have hex2:∃ r2:vu Q,qN Q r2=c:=by
         by_contra hn
         have:=(zD Q c).mpr hn
         rw [hc] at this; exact Bool.noConfusion this
        obtain ⟨r2,rfl⟩:=hex2
        have hne:r.val≠r2.val:=fun h=>hcr (by rw [Subtype.ext h])
        rw [(zB Q r2).2 r.val hne,zero_mul]
      · rw [hw_free c hc,mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact hw_free j hj
 funext j
 have h1:=congrFun hw_zero j
 simp only [Pi.add_apply,Pi.zero_apply] at h1
 calc v j=u j+(u j+v j):=by rw [← add_assoc,qj,zero_add]
  _=u j:=by rw [h1,add_zero]
lemma uc {P k:ℕ} (Q:Fin P→V k):
 Set.range (shift (qb Q))={u:V k|∀ i,dotProduct (Q i) u=0}:=by
 ext u
 constructor
 · rintro ⟨x,rfl⟩ i
   simp only [shift,dotProduct_sum]
   apply Finset.sum_eq_zero
   intro c _
   rw [dotProduct_smul,qy Q c i,smul_zero]
 · intro hu
   exact ⟨u,qV Q hu⟩
lemma kX {P k:ℕ} (Q:Fin P→V k):
 Submodule.span F (Set.range (qb Q))=zM (Submodule.span F (Set.range Q)):=by
 ext u
 rw [Submodule.mem_span_range_iff_exists_fun F]
 change (∃ x,shift (qb Q) x=u)↔u∈zM (Submodule.span F (Set.range Q))
 have hmem:u∈Set.range (shift (qb Q))↔u∈zM (Submodule.span F (Set.range Q)):=by
  rw [uc]
  simp only [Set.mem_ofPred_eq,uZ]
  constructor
  · intro hu v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i,rfl⟩; rw [dotProduct_comm]; exact hu i
    · exact dotProduct_zero _
    · intro x y _ _ hx hy; rw [dotProduct_add,hx,hy,add_zero]
    · intro a x _ hx; rw [dotProduct_smul,hx,smul_zero]
  · intro hu i
    rw [dotProduct_comm]
    exact hu (Q i) (Submodule.subset_span ⟨i,rfl⟩)
 exact hmem
lemma kF {P k:ℕ} (Q:Fin P→V k):
 Module.finrank F (Submodule.span F (Set.range (qb Q))) +
  Module.finrank F (Submodule.span F (Set.range Q))=k:=by
 rw [kX]
 exact z6 _
lemma zt {P k:ℕ} (Q:Fin P→V k) {q:V k}
 (hsupp:∀ j,qh Q j=false→q j=0) (hne:q≠0):
 q∉Submodule.span F (Set.range Q):=by
 intro hmem
 rw [← (qv Q (fun _=>Fin.elim0)).1,
     Submodule.mem_span_range_iff_exists_fun F] at hmem
 obtain ⟨c,hc⟩:=hmem
 apply hne
 rw [← hc]
 have hc0:∀ r:Fin P,c r • (qx Q).M r=0:=by
  intro r
  by_cases hr:(qx Q).used r=true
  · let ru:vu Q:=⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
    have hcol_nf:qh Q (qN Q ru)=false:=by
     cases hf:qh Q (qN Q ru)
     · rfl
     · exact ((zD Q (qN Q ru)).mp hf ⟨ru,rfl⟩).elim
    have hq0:q (qN Q ru)=0:=hsupp _ hcol_nf
    have hsum:=congrFun hc (qN Q ru)
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hq0] at hsum
    rw [Finset.sum_eq_single r] at hsum
    · rw [(zB Q ru).1,mul_one] at hsum
      rw [hsum,zero_smul]
    · intro s _ hsr
      rw [(zB Q ru).2 s hsr,mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hrf:(qx Q).used r=false:=by cases h:(qx Q).used r <;> simp_all
    have h0:(qx Q).M r=0:=funext ((qv Q (fun _=>Fin.elim0)).2.2.1 r hrf)
    rw [h0,smul_zero]
 exact Finset.sum_eq_zero (fun r _=>hc0 r)
def vR {P k:ℕ} (Q:Fin P→V k) (j:Fin k):Bool:=!(qh Q j)
def vI {P k:ℕ} (Q:Fin P→V k):Finset (Fin k):=
 Finset.univ.filter (fun j=>vR Q j=true)
def yv {P k:ℕ} (Q:Fin P→V k) (j:Fin k):ℕ:=
 ((vI Q).filter (·<j)).card
def qO {P k:ℕ} (d:ℕ) (Q:Fin P→V k) (i:Fin (2 ^ d)) (j:Fin k):F:=
 if vR Q j then z5 (vI Q).card i.val (yv Q j) else 0
def zc {P k:ℕ} (d:ℕ) (Q:Fin P→V k) (i:Fin (2 ^ d)):Bool:=
 decide (i.val<2 ^ (vI Q).card)
lemma uX {P k:ℕ} (Q:Fin P→V k):
 (vI Q).card=Module.finrank F (Submodule.span F (Set.range Q)):=by
 have hcompl:vI Q=(zK Q)ᶜ:=by ext j; simp [vI,vR,zK]
 rw [hcompl,Finset.card_compl,Fintype.card_fin,kL]
 have hle:Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q))≤k:=by
  simpa [Module.finrank_fin_fun] using (Submodule.span (ZMod 2) (Set.range Q)).finrank_le
 change k-(k-Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)))=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q))
 omega
def uN {P k:ℕ} (Q:Fin P→V k) (j:vI Q):Fin (vI Q).card:=
 ⟨yv Q j.val,by
   apply Finset.card_lt_card
   rw [Finset.ssubset_iff_subset_ne]
   refine ⟨Finset.filter_subset _ _,fun h=>?_⟩
   have hj:j.val∈(vI Q).filter (·<j.val):=by rw [h]; exact j.property
   simp at hj⟩
lemma ju {P k:ℕ} (Q:Fin P→V k):Function.Bijective (uN Q):=by
 apply (Fintype.bijective_iff_injective_and_card _).mpr
 refine ⟨StrictMono.injective ?_,by simp⟩
 intro i j hij
 change ((vI Q).filter (·< i.val)).card<((vI Q).filter (·<j.val)).card
 apply Finset.card_lt_card
 rw [Finset.ssubset_iff_subset_ne]
 refine ⟨fun x hx=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,lt_trans (Finset.mem_filter.mp hx).2 hij⟩,
  fun h=>?_⟩
 have hi:i.val∈(vI Q).filter (·<j.val):=Finset.mem_filter.mpr ⟨i.property,hij⟩
 rw [← h] at hi
 exact lt_irrefl _ (Finset.mem_filter.mp hi).2
theorem u8 {P k:ℕ} (d:ℕ) (Q:Fin P→V k)
 (hrk:Module.finrank F (Submodule.span F (Set.range Q))≤d) (w:V k):
 ∃! i:Fin (2 ^ d),zc d Q i=true∧
  w-qO d Q i∈Submodule.span F (Set.range (qb Q)):=by
 classical
 let S:=Submodule.span F (Set.range (qb Q))
 let n:=(vI Q).card
 have hnd:n≤d:=by dsimp only [n]; rw [uX]; exact hrk
 let idx:Fin (2 ^ n)→Fin (2 ^ d):=Fin.castLE (Nat.pow_le_pow_right (by decide) hnd)
 let f:Fin (2 ^ n)×S→V k:=fun z=>qO d Q (idx z.1)+z.2.val
 have surj:Function.Surjective f:=by
  intro v
  let z:V k:=shift (qb Q) v
  have hz:z∈S:=by
   dsimp only [z,shift]
   exact Submodule.sum_mem _ (fun c _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨c,rfl⟩))
  have hz_free (j:Fin k) (hj:qh Q j=true):z j=v j:=by
   simp only [z,shift,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
   rw [Finset.sum_eq_single j]
   · rw [zz Q hj hj,ite_eq_left rfl,mul_one]
   · intro c _ hcj
     cases hc:qh Q c
     · rw [zJ Q hc,Pi.zero_apply,mul_zero]
     · rw [zz Q hc hj,ite_eq_right (Ne.symm hcj),mul_zero]
   · intro h; exact absurd (Finset.mem_univ _) h
  let e:=Equiv.ofBijective (uN Q) (ju Q)
  let word:Fin n→F:=fun b=>(v-z) (e.symm b).val
  let a:=(kh n).symm word
  refine ⟨⟨a,⟨z,hz⟩⟩,?_⟩
  funext j
  change qO d Q (idx a) j+z j=v j
  by_cases hj:vR Q j=true
  · let u:vI Q:=⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
    have huv:z5 n a.val (yv Q j)=word (e u):=by
     have hb:yv Q j<n:=(uN Q u).isLt
     simp only [z5,dite_eq_left a.isLt,dite_eq_left hb]
     exact congrFun ((kh n).apply_symm_apply word) (e u)
    change (if vR Q j then z5 n a.val (yv Q j) else 0)+z j=v j
    rw [ite_eq_left hj,huv]
    simp [word,u]
  · have hfree:qh Q j=true:=by
     cases h:qh Q j <;> simp_all [vR]
    simp [qO,hj,hz_free j hfree]
 have bij:Function.Bijective f:=by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨surj,?_⟩
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,ZMod.card,vn,← pow_add]
  congr 1
  change (vI Q).card+Module.finrank F S=k
  rw [uX]
  have hfr:=kF Q
  dsimp only [S]
  omega
 obtain ⟨⟨a,s⟩,ha⟩:=surj w
 change qO d Q (idx a)+s.val=w at ha
 refine ⟨idx a,⟨decide_eq_true a.isLt,?_⟩,?_⟩
 · rw [← ha,add_sub_cancel_left]; exact s.property
 · rintro i ⟨hi,hs⟩
   let b:Fin (2 ^ n):=⟨i.val,of_decide_eq_true hi⟩
   have h:f (b,⟨w-qO d Q i,hs⟩)=f (a,s):=by
    change qO d Q i+(w-qO d Q i)=qO d Q (idx a)+s.val
    rw [ha]; abel
   exact congrArg idx (congrArg Prod.fst (bij.1 h))
def ke {N P k:ℕ} (d:ℕ) (Q:In N→Fin P→V k):Set (Sig N):=
 Set.range (fun j=>fun x=>qh (Q x) j) ∪
 {f|∃ c j,(fun x=>z2b (qb (Q x) c j))=f} ∪
 Set.range (fun i:Fin (2 ^ d)=>fun x=>zc d (Q x) i) ∪
 {f|∃ (i:Fin (2 ^ d)) (j:Fin k),(fun x=>z2b (qO d (Q x) i j))=f}
def va {P k:ℕ} (Q:Fin P→V k) (a:Fin (k+1)):Fin (k+1):=
 ⟨((vI Q).filter (fun j=>j.val<a.val)).card,by
   have hh:=((vI Q).filter (fun j=>j.val<a.val)).card_le_univ
   simp only [Fintype.card_fin] at hh; omega⟩
lemma uM {P k:ℕ} (Q:Fin P→V k):
 (va Q (Fin.last k)).val=(vI Q).card:=by
 simp [va]
theorem j6 {N P k:ℕ} (d:ℕ) (A:Set (Sig N))
 (hz:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (Q:In N→Fin P→V k) (hQ:∀ r j,(fun x=>z2b (Q x r j))∈A):
 qa A (ke d Q) (128 * (k+P+4) ^ 5 * 2 ^ d):=by
 classical
 let U:=2 ^ d
 have hG:=vN A hz Q (fun _ _=>Fin.elim0) hQ (fun _ j=>Fin.elim0 j)
 let AG:=A ∪ qY (fun x=>qx (Q x))
 have hM (r:Fin P) (j:Fin k):(fun x=>z2b ((qx (Q x)).M r j))∈AG:=
  Or.inr (Or.inl (Or.inr ⟨r,j,rfl⟩))
 let neg:Fin P→Fin k→Sig N:=fun r j x=>!(z2b ((qx (Q x)).M r j))
 have H1:=qT neg 1 (fun r j=>zn (hM r j))
 let A1:=AG ∪ {f|∃ r j,neg r j=f}
 let priv:Fin P→Fin k→Sig N:=fun r j x=>vT (Q x) r j
 have H2:qa A1 {f|∃ r j,priv r j=f} (P * (k * P)):=by
  refine qT priv P (fun r j=>?_)
  let term:Fin P→Sig N:=fun s x=>if s=r then z2b ((qx (Q x)).M s j) else neg s j x
  apply vB term _ (Or.inl (Or.inl ht))
  intro s; by_cases hs:s=r
  · have heq:term s=(fun x=>z2b ((qx (Q x)).M s j)):=by funext x; simp [term,hs]
    rw [heq]; exact Or.inl (hM s j)
  · have heq:term s=neg s j:=by funext x; simp [term,hs]
    rw [heq]; exact Or.inr ⟨s,j,rfl⟩
 let A2:=A1 ∪ {f|∃ r j,priv r j=f}
 let pick:Fin P→Fin k→Sig N:=fun r j x=>vg (Q x) r j
 have H3:qa A2 (⋃ r,Set.range (pick r)) (P * (k * (k+2))):=
  v7 _ _ (fun r=>yE (priv r) (Or.inl (Or.inl (Or.inl hz))) (fun j=>Or.inr ⟨r,j,rfl⟩))
 let A3:=A2 ∪ ⋃ r,Set.range (pick r)
 have H4:qa A3 (Set.range (fun j=>fun x=>qh (Q x) j)) (k * (P+1)):=by
  refine qf _ _ (fun j=>?_)
  have hh:=vC (A:=A3) (fun r=>pick r j)
   (fun r=>Or.inr (Set.mem_iUnion.mpr ⟨r,⟨j,rfl⟩⟩)) (Or.inl (Or.inl (Or.inl (Or.inl hz))))
  exact qe hh (zn (Or.inr rfl))
 let A4:=A3 ∪ Set.range (fun j=>fun x=>qh (Q x) j)
 have hFreeMem (j:Fin k):(fun x=>qh (Q x) j)∈A4:=Or.inr ⟨j,rfl⟩
 have hPickMem (r:Fin P) (j:Fin k):pick r j∈A4:=Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨r,⟨j,rfl⟩⟩))
 have hM4 (r:Fin P) (j:Fin k):(fun x=>z2b ((qx (Q x)).M r j))∈A4:=
  Or.inl (Or.inl (Or.inl (Or.inl (hM r j))))
 have hF4:(fun _=>false)∈A4:=Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hz))))
 have hT4:(fun _=>true)∈A4:=Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ht))))
 have hKerGen:qa A4 {f|∃ c j,(fun x=>z2b (qb (Q x) c j))=f} (k * (k * (P * 2+1))):=by
  refine qT _ (P * 2+1) (fun c j=>?_)
  by_cases hjc:j=c
  · subst hjc
    have heq:(fun x=>z2b (qb (Q x) j j))=(fun x=>qh (Q x) j):=by
     funext x; cases hf:qh (Q x) j <;> simp [qb,hf,zA,qm]
    rw [heq]
    exact qd (zk (Set.singleton_subset_iff.mpr (hFreeMem j))) le_rfl Set.subset_union_right (Nat.zero_le _)
  · let term:Fin P→Sig N:=fun r x=>pick r j x&&z2b ((qx (Q x)).M r c)
    have ht1:qa A4 (Set.range term) (P * 1):=
     qf term 1 (fun r=>qD (hPickMem r j) (hM4 r c))
    have ht2:qa (A4 ∪ Set.range term) {fun x=>(List.finRange P).any (fun r=>term r x)} P:=
     vC term (fun r=>Or.inr ⟨r,rfl⟩) (Or.inl hF4)
    have ht12:=qe ht1 ht2
    have ht3:qa (A4 ∪ {fun x=>(List.finRange P).any (fun r=>term r x)})
     {fun x=>qh (Q x) c&&(List.finRange P).any (fun r=>term r x)} 1:=
     qD (Or.inl (hFreeMem c)) (Or.inr rfl)
    have heq:(fun x=>qh (Q x) c&&(List.finRange P).any (fun r=>term r x))=
     (fun x=>z2b (qb (Q x) c j)):=by
     funext x
     cases hf:qh (Q x) c <;> simp [qb,hf,hjc,term,qm,z0,pick]
    rw [heq] at ht3
    exact qd (qe ht12 ht3) le_rfl Set.subset_union_right (by omega)
 have hPiv:qa A4 (Set.range (fun j=>fun x=>vR (Q x) j)) (k * 1):=
  qf _ 1 (fun j=>zn (hFreeMem j))
 let A5:=A4 ∪ Set.range (fun j=>fun x=>vR (Q x) j)
 have hHist:qa A5 (⋃ a:Fin (k+1),Set.range (fun i:Fin (k+1)=>fun x=>decide (i=va (Q x) a)))
  ((k+1) * (k * ((k+1) * 4))):=by
  refine v7 _ _ (fun a=>?_)
  let u:In N→Fin k→Bool:=fun x j=>if j.val<a.val then vR (Q x) j else false
  have hu (j:Fin k):(fun x=>u x j)∈A5:=by
   by_cases h:j.val<a.val <;> simp [u,h]
   · exact Or.inr ⟨j,rfl⟩
   · exact Or.inl hF4
  have heq (i:Fin (k+1)) (x:In N):zC (u x) i=decide (i=va (Q x) a):=by
   rw [vh]
   have hset:Finset.univ.filter (fun j=>u x j=true)=(vI (Q x)).filter (fun j=>j.val<a.val):=by
    ext j; by_cases h:j.val<a.val <;> simp [u,h,vI]
   simp [hset,va,Fin.ext_iff]
  simpa only [heq] using v3 A5 (Or.inl hF4) (Or.inl hT4) u hu
 let A6:=A5 ∪ ⋃ a:Fin (k+1),Set.range (fun i:Fin (k+1)=>fun x=>decide (i=va (Q x) a))
 have h0:(fun _=>false)∈A6:=Or.inl (Or.inl hF4)
 have h1:(fun _=>true)∈A6:=Or.inl (Or.inl hT4)
 have hc (b:Bool):(fun _=>b)∈A6:=by cases b <;> assumption
 have ho (a i:Fin (k+1)):(fun x=>decide (i=va (Q x) a))∈A6:=
  Or.inr (Set.mem_iUnion.mpr ⟨a,⟨i,rfl⟩⟩)
 let total:=fun x=>va (Q x) (Fin.last k)
 have hLive:qa A6 (Set.range (fun i:Fin U=>fun x=>zc d (Q x) i)) (U * ((k+1) * 2)):=by
  refine qf _ _ (fun i=>?_)
  simpa only [total,uM,zc] using
   yr h0 total (fun a _=>decide (i.val<2 ^ a.val)) (ho _) (fun a=>hc _)
 have hRep:qa A6 {f|∃ (i:Fin U) (j:Fin k),(fun x=>z2b (qO d (Q x) i j))=f}
  (U * (k * ((k+1) * ((k+1) * 2)+(k+1) * 2+1))):=by
  refine qT _ _ (fun i j=>?_)
  let pos:=fun x=>va (Q x) j.castSucc
  let tab:Fin (k+1)→Sig N:=fun a x=>z2b (z5 a.val i.val (pos x).val)
  have hb:=qf tab ((k+1) * 2) (fun a=>yr h0 pos
   (fun b _=>z2b (z5 a.val i.val b.val)) (ho _) (fun _=>hc _))
  have hb':=yr (A:=A6 ∪ Set.range tab) (Or.inl h0) total tab
   (fun s=>Or.inl (ho _ s)) (fun s=>Or.inr ⟨s,rfl⟩)
  have hh:=qe hb hb'
  have hp:(fun x=>vR (Q x) j)∈A6:=Or.inl (Or.inr ⟨j,rfl⟩)
  have hp':=qe hh (qD (Or.inl hp) (Or.inr rfl))
  have heq:(fun x=>vR (Q x) j&&tab (total x) x)=fun x=>z2b (qO d (Q x) i j):=by
   funext x
   cases e:vR (Q x) j <;> simp [qO,tab,total,e,qm,pos,va,yv]
  rwa [heq] at hp'
 have hAll4:qa A4 (ke d Q)
  (k * (k * (P * 2+1))+(k * 1+((k+1) * (k * ((k+1) * 4)) +
    (U * ((k+1) * 2)+U * (k * ((k+1) * ((k+1) * 2)+(k+1) * 2+1)))))):=by
  have hLR:=qe hPiv (qe hHist (qr hLive hRep))
  have hU:=qr hKerGen hLR
  refine qd hU le_rfl ?_ le_rfl
  intro f hf
  rcases hf with ((hf|hf)|hf)|hf
  · exact Or.inl (by obtain ⟨j,rfl⟩:=hf; exact hFreeMem j)
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr (Or.inl hf))
  · exact Or.inr (Or.inr (Or.inr hf))
 have hFull:=qo (qo (qo (qo (qP hG) (qP H1)) (qP H2)) (qP H3)) (qe H4 hAll4)
 apply qd hFull le_rfl Set.subset_union_right
 dsimp only [U]
 obtain ⟨v,hv⟩:=Nat.exists_eq_succ_of_ne_zero (show 2 ^ d≠0 by positivity)
 rw [hv,Nat.succ_eq_add_one]
 ring_nf
 omega
def ze {k r t P:ℕ} (hk:0<k) (watch:qI k) (side:Fin t→Bool) (site:Fin t→Fin k)
    (h:ℕ) (nm:Bool→V k) (c:Bool→Fin (r+1)→V k) (Q:Fin P→V k):Prop:=
 let D:={u:V k // ∀ i,dotProduct (Q i) u=0}
 let pr:=fun (key:V k) (i:Fin t)=>state hk nm c (side i) key (r+1) (site i)
 let pol:=fun (a:V k) (i:Fin t) (xy:D×D)=>
  pr a i+pr (a+xy.1.val) i+pr (a+xy.2.val) i+pr (a+xy.1.val+xy.2.val) i
 (∀ (a:V k) (b:Bool) (n:ℕ),n≤r→∀ j:Fin k,watch b n j=true→
   ∀ x y:D,state hk nm c b a n j+state hk nm c b (a+x.val) n j +
     state hk nm c b (a+y.val) n j+state hk nm c b (a+x.val+y.val) n j=0)∧
 (∀ a:V k,Module.finrank F (Submodule.span F (Set.range (pol a)))≤h)
lemma vJ {k r t P:ℕ} (hk:0<k) (watch:qI k)
 (hc:closed hk watch (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,watch (side i) (r+1) (site i)=true)
 (nm:Bool→V k) (c:Bool→Fin (r+1)→V k) (tar:V t)
 (Q:Fin P→V k) (hpref:fullPrefix hk nm c (qb Q) watch) (a:V k):
 let D:={u:V k // ∀ i,dotProduct (Q i) u=0}
 let pr:=fun (key:V k) (i:Fin t)=>state hk nm c (side i) key (r+1) (site i)
 let pol:=fun (i:Fin t) (xy:D×D)=>
  pr a i+pr (a+xy.1.val) i+pr (a+xy.2.val) i+pr (a+xy.1.val+xy.2.val) i
 Module.finrank F (Submodule.span F (Set.range pol))=
  (matrix (qb Q) a (probe hk nm c side site) tar).rank:=by
 classical
 intro D pr pol
 have hchk:Checks hk nm c (qb Q) a watch:=by
  intro b n _ hn j hj u v _
  have hp:=hpref a b n hn j hj (unit u) (unit v)
  simpa [sample,shift_unit] using hp
 have hbil:∀ i:Fin t,∃ (w1 w2:V k),∀ x y:D,
  pol i (x,y)=lin w1 x.val * lin w2 y.val+lin w1 y.val * lin w2 x.val:=by
  intro i
  have hop:=terminal_oneProduct hk nm c (qb Q) a watch hc hchk (side i) (site i) (hw i)
  obtain ⟨a0,b0,c0,v0,w1,w2,heq⟩:=hop.coeffs
  refine ⟨w1,w2,fun x y=>?_⟩
  have hx:shift (qb Q) x.val=x.val:=qV Q x.property
  have hy:shift (qb Q) y.val=y.val:=qV Q y.property
  have hxy:shift (qb Q) (x.val+y.val)=x.val+y.val:=by
   rw [shift_add,hx,hy]
  have h0:pr a i=a0+lin v0 0+(b0+lin w1 0) * (c0+lin w2 0):=by
   simpa [pr,shift_zero,add_zero] using heq 0
  have h1:pr (a+x.val) i=a0+lin v0 x.val+(b0+lin w1 x.val) * (c0+lin w2 x.val):=by
   simpa [pr,hx] using heq x.val
  have h2:pr (a+y.val) i=a0+lin v0 y.val+(b0+lin w1 y.val) * (c0+lin w2 y.val):=by
   simpa [pr,hy] using heq y.val
  have h3:pr (a+x.val+y.val) i=
   a0+lin v0 (x.val+y.val)+(b0+lin w1 (x.val+y.val)) * (c0+lin w2 (x.val+y.val)):=by
   have ha:a+(x.val+y.val)=a+x.val+y.val:=(add_assoc _ _ _).symm
   simpa [pr,hxy,ha] using heq (x.val+y.val)
  dsimp only [pol]
  rw [h0,h1,h2,h3]
  have hl0 (v:V k):lin v 0=0:=by simp [lin]
  simp only [hl0,lin_add]
  exact y8 a0 b0 c0 (lin v0 x.val) (lin v0 y.val) (lin w1 x.val) (lin w1 y.val) (lin w2 x.val) (lin w2 y.val)
 have hpol_bil:∀ f∈Submodule.span F (Set.range pol),
  (∀ x1 x2 y:D,f (⟨x1.val+x2.val,fun i=>by rw [dotProduct_add,x1.2 i,x2.2 i,add_zero]⟩,y)=
    f (x1,y)+f (x2,y))∧
  (∀ x y1 y2:D,f (x,⟨y1.val+y2.val,fun i=>by rw [dotProduct_add,y1.2 i,y2.2 i,add_zero]⟩)=
    f (x,y1)+f (x,y2)):=by
  intro f hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨i,rfl⟩
    obtain ⟨w1,w2,hi⟩:=hbil i
    constructor
    · intro x1 x2 y; rw [hi,hi,hi]; simp only [lin_add]; ring
    · intro x y1 y2; rw [hi,hi,hi]; simp only [lin_add]; ring
  · exact ⟨fun _ _ _=>by simp,fun _ _ _=>by simp⟩
  · intro g1 g2 _ _ ⟨h1l,h1r⟩ ⟨h2l,h2r⟩
    exact ⟨fun x1 x2 y=>by simp only [Pi.add_apply,h1l,h2l]; ring,
           fun x y1 y2=>by simp only [Pi.add_apply,h1r,h2r]; ring⟩
  · intro c0 g _ ⟨hl,hr⟩
    exact ⟨fun x1 x2 y=>by simp only [Pi.smul_apply,smul_eq_mul,hl]; ring,
           fun x y1 y2=>by simp only [Pi.smul_apply,smul_eq_mul,hr]; ring⟩
 let gD:Fin k→D:=fun u=>⟨qb Q u,qy Q u⟩
 let ev:(D×D→F) →ₗ[F] ((Fin k×Fin k)→F):=
  { toFun:=fun f uv=>f (gD uv.1,gD uv.2)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
 let S:=Submodule.span F (Set.range pol)
 have hev_inj:Function.Injective (ev.comp S.subtype):=by
  intro ⟨f1,hf1⟩ ⟨f2,hf2⟩ heq
  apply Subtype.ext
  have hdiff:f1-f2∈S:=S.sub_mem hf1 hf2
  obtain ⟨hbl,hbr⟩:=hpol_bil (f1-f2) hdiff
  have hzero_gen:∀ u v:Fin k,(f1-f2) (gD u,gD v)=0:=by
   intro u v
   have h:=congrFun heq (u,v)
   change f1 (gD u,gD v)=f2 (gD u,gD v) at h
   simp [h]
  have hzero_left:∀ (s:Finset (Fin k)) (x:V k) (v:Fin k),
   (f1-f2) (⟨∑ u∈s,x u • qb Q u,fun i=>by
     rw [dotProduct_sum]; exact Finset.sum_eq_zero fun u _=>by rw [dotProduct_smul,qy,smul_zero]⟩,gD v)=0:=by
   intro s x v
   induction s using Finset.induction_on with
   | empty=>
     have hz0:(⟨0,fun i=>dotProduct_zero _⟩:D)=
      ⟨(⟨0,fun i=>dotProduct_zero _⟩:D).val+(⟨0,fun i=>dotProduct_zero _⟩:D).val,
        fun i=>by simp⟩:=Subtype.ext (add_zero 0).symm
     have h0:=hbl ⟨0,fun i=>dotProduct_zero _⟩ ⟨0,fun i=>dotProduct_zero _⟩ (gD v)
     simp only [Finset.sum_empty]
     change (f1-f2) (⟨0,_⟩,gD v)=0
     have h0':(f1-f2) (⟨0,fun i=>dotProduct_zero _⟩,gD v)=
      (f1-f2) (⟨0,fun i=>dotProduct_zero _⟩,gD v)+(f1-f2) (⟨0,fun i=>dotProduct_zero _⟩,gD v):=by
      simpa [add_zero] using h0
     rw [qj] at h0'; exact h0'
   | insert a0 s ha0 ih=>
     have hsum:=hbl ⟨x a0 • qb Q a0,fun i=>by rw [dotProduct_smul,qy,smul_zero]⟩
      ⟨∑ u∈s,x u • qb Q u,fun i=>by
        rw [dotProduct_sum]; exact Finset.sum_eq_zero fun u _=>by rw [dotProduct_smul,qy,smul_zero]⟩
      (gD v)
     have hstep:(⟨∑ u∈insert a0 s,x u • qb Q u,fun i=>by
      rw [dotProduct_sum]; exact Finset.sum_eq_zero fun u _=>by rw [dotProduct_smul,qy,smul_zero]⟩:D)=
      ⟨x a0 • qb Q a0+∑ u∈s,x u • qb Q u,fun i=>by
        rw [dotProduct_add,dotProduct_smul,qy,smul_zero,zero_add,dotProduct_sum]
        exact Finset.sum_eq_zero fun u _=>by rw [dotProduct_smul,qy,smul_zero]⟩:=by
      apply Subtype.ext; exact Finset.sum_insert ha0
     rw [hstep,hsum,ih,add_zero]
     rcases qF (x a0) with hx0|hx1
     · have hz:(⟨x a0 • qb Q a0,fun i=>by rw [dotProduct_smul,qy,smul_zero]⟩:D)=
        ⟨0,fun i=>dotProduct_zero _⟩:=Subtype.ext (by simp [hx0])
       rw [hz]
       have h0:=hbl ⟨0,fun i=>dotProduct_zero _⟩ ⟨0,fun i=>dotProduct_zero _⟩ (gD v)
       have h0':(f1-f2) (⟨0,fun i=>dotProduct_zero _⟩,gD v)=
        (f1-f2) (⟨0,fun i=>dotProduct_zero _⟩,gD v)+(f1-f2) (⟨0,fun i=>dotProduct_zero _⟩,gD v):=by
        simpa [add_zero] using h0
       rw [qj] at h0'; exact h0'
     · have h1:(⟨x a0 • qb Q a0,fun i=>by rw [dotProduct_smul,qy,smul_zero]⟩:D)=gD a0:=
        Subtype.ext (by simp [hx1,gD])
       rw [h1]; exact hzero_gen a0 v
  have hzero_all:∀ x:D,∀ (s:Finset (Fin k)) (y:V k),
   (f1-f2) (x,⟨∑ v∈s,y v • qb Q v,fun i=>by
     rw [dotProduct_sum]; exact Finset.sum_eq_zero fun v _=>by rw [dotProduct_smul,qy,smul_zero]⟩)=0:=by
   intro x s y
   induction s using Finset.induction_on with
   | empty=>
     simp only [Finset.sum_empty]
     have h0:=hbr x ⟨0,fun i=>dotProduct_zero _⟩ ⟨0,fun i=>dotProduct_zero _⟩
     have h0':(f1-f2) (x,⟨0,fun i=>dotProduct_zero _⟩)=
      (f1-f2) (x,⟨0,fun i=>dotProduct_zero _⟩)+(f1-f2) (x,⟨0,fun i=>dotProduct_zero _⟩):=by
      simpa [add_zero] using h0
     rw [qj] at h0'; exact h0'
   | insert a0 s ha0 ih=>
     have hsum:=hbr x ⟨y a0 • qb Q a0,fun i=>by rw [dotProduct_smul,qy,smul_zero]⟩
      ⟨∑ v∈s,y v • qb Q v,fun i=>by
        rw [dotProduct_sum]; exact Finset.sum_eq_zero fun v _=>by rw [dotProduct_smul,qy,smul_zero]⟩
     have hstep:(⟨∑ v∈insert a0 s,y v • qb Q v,fun i=>by
      rw [dotProduct_sum]; exact Finset.sum_eq_zero fun v _=>by rw [dotProduct_smul,qy,smul_zero]⟩:D)=
      ⟨y a0 • qb Q a0+∑ v∈s,y v • qb Q v,fun i=>by
        rw [dotProduct_add,dotProduct_smul,qy,smul_zero,zero_add,dotProduct_sum]
        exact Finset.sum_eq_zero fun v _=>by rw [dotProduct_smul,qy,smul_zero]⟩:=by
      apply Subtype.ext; exact Finset.sum_insert ha0
     rw [hstep,hsum,ih,add_zero]
     rcases qF (y a0) with hy0|hy1
     · have hz:(⟨y a0 • qb Q a0,fun i=>by rw [dotProduct_smul,qy,smul_zero]⟩:D)=
        ⟨0,fun i=>dotProduct_zero _⟩:=Subtype.ext (by simp [hy0])
       rw [hz]
       have h0:=hbr x ⟨0,fun i=>dotProduct_zero _⟩ ⟨0,fun i=>dotProduct_zero _⟩
       have h0':(f1-f2) (x,⟨0,fun i=>dotProduct_zero _⟩)=
        (f1-f2) (x,⟨0,fun i=>dotProduct_zero _⟩)+(f1-f2) (x,⟨0,fun i=>dotProduct_zero _⟩):=by
        simpa [add_zero] using h0
       rw [qj] at h0'; exact h0'
     · have h1:(⟨y a0 • qb Q a0,fun i=>by rw [dotProduct_smul,qy,smul_zero]⟩:D)=gD a0:=
        Subtype.ext (by simp [hy1,gD])
       rw [h1]
       have hxe:x=⟨∑ u∈Finset.univ,x.val u • qb Q u,fun i=>by
        rw [dotProduct_sum]; exact Finset.sum_eq_zero fun u _=>by rw [dotProduct_smul,qy,smul_zero]⟩:=
        Subtype.ext (qV Q x.property).symm
       rw [hxe]
       exact hzero_left Finset.univ x.val a0
  funext ⟨x,y⟩
  have hye:y=⟨∑ v∈Finset.univ,y.val v • qb Q v,fun i=>by
   rw [dotProduct_sum]; exact Finset.sum_eq_zero fun v _=>by rw [dotProduct_smul,qy,smul_zero]⟩:=
   Subtype.ext (qV Q y.property).symm
  have h0:(f1-f2) (x,y)=0:=by rw [hye]; exact hzero_all x Finset.univ y.val
  exact sub_eq_zero.mp h0
 have hrg:LinearMap.range (ev.comp S.subtype)=
  Submodule.span F (Set.range (fun i:Fin t=>matrix (qb Q) a (probe hk nm c side site) tar i)):=by
  have h1:LinearMap.range (ev.comp S.subtype)=Submodule.map ev S:=by
   ext w; simp [Submodule.mem_map]
  rw [h1,Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and]
  apply exists_congr; intro i
  have hevi:ev (pol i)=matrix (qb Q) a (probe hk nm c side site) tar i:=by
   funext ⟨u,v⟩; rfl
  rw [hevi]
 rw [← LinearMap.finrank_range_of_inj hev_inj,hrg]
 let e:=finProdFinEquiv (m:=k) (n:=k)
 let M:Matrix (Fin t) (Fin (k * k)) F:=
  Matrix.reindex (Equiv.refl (Fin t)) e (matrix (qb Q) a (probe hk nm c side site) tar)
 have hM_rk:M.rank=(matrix (qb Q) a (probe hk nm c side site) tar).rank:=
  Matrix.rank_reindex (Equiv.refl _) e _
 rw [← hM_rk,zl M]
 let re:((Fin k×Fin k)→F) ≃ₗ[F] (Fin (k * k)→F):=LinearEquiv.funCongrLeft F F e.symm
 have hmap:Submodule.map re.toLinearMap
  (Submodule.span F (Set.range (fun i:Fin t=>matrix (qb Q) a (probe hk nm c side site) tar i)))=
  Submodule.span F (Set.range (fun i:Fin t=>M i)):=by
  rw [Submodule.map_span]
  congr 1; ext w
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i,by funext j; rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨_,⟨i,rfl⟩,by funext j; rfl⟩
 rw [← hmap,zX re.toLinearMap re.injective]
lemma ud {k r t P:ℕ} (hk:0<k) (watch:qI k)
 (hc:closed hk watch (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,watch (side i) (r+1) (site i)=true)
 (h:ℕ) (nm:Bool→V k) (c:Bool→Fin (r+1)→V k) (tar:V t) (Q:Fin P→V k):
 ze hk watch side site h nm c Q↔
  fullPrefix hk nm c (qb Q) watch∧
  ∀ a,(matrix (qb Q) a (probe hk nm c side site) tar).rank≤h:=by
 have hpref_iff:(∀ (a:V k) (b:Bool) (n:ℕ),n≤r→∀ j:Fin k,watch b n j=true→
  ∀ x y:{u:V k // ∀ i,dotProduct (Q i) u=0},
    state hk nm c b a n j+state hk nm c b (a+x.val) n j +
    state hk nm c b (a+y.val) n j+state hk nm c b (a+x.val+y.val) n j=0)↔
  fullPrefix hk nm c (qb Q) watch:=by
  have hshift_ker (x:V k) (i:Fin P):dotProduct (Q i) (shift (qb Q) x)=0:=by
   simp only [shift,dotProduct_sum]
   exact Finset.sum_eq_zero fun c _=>by rw [dotProduct_smul,qy,smul_zero]
  constructor
  · intro h1 a b n hn j hj x y
    exact h1 a b n hn j hj ⟨shift (qb Q) x,hshift_ker x⟩ ⟨shift (qb Q) y,hshift_ker y⟩
  · intro h1 a b n hn j hj x y
    have hx:=qV Q x.property
    have hy:=qV Q y.property
    simpa only [hx,hy] using h1 a b n hn j hj x.val y.val
 constructor
 · rintro ⟨h1,h2⟩
   have hp:=hpref_iff.mp h1
   refine ⟨hp,fun a=>?_⟩
   rw [← vJ hk watch hc side site hw nm c tar Q hp a]
   exact h2 a
 · rintro ⟨hp,h2⟩
   refine ⟨hpref_iff.mpr hp,fun a=>?_⟩
   rw [vJ hk watch hc side site hw nm c tar Q hp a]
   exact h2 a
end
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
noncomputable section
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine
open PEqualNP.Outside.L_meta_27129_aux.P25940Sample
open PEqualNP.Outside.L_meta_27129_aux.P25940Sem
open PEqualNP.Outside.L_meta_27129_aux.yo
def ya {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r)
    (b:Bool) (j u v:Fin k) (x:In N):Bool:=
 if w b (n.val+1) j=true∧u<v then
  !(z2b (delta (fun s=>za hk nm c rep gen b (n.val+1) j s x) u v))
 else true
def z7 {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r)
    (b:Bool) (j:Fin k) (x:In N):Bool:=
 (List.finRange k).all fun u=>(List.finRange k).all fun v=>
   ya hk nm c rep gen w n b j u v x
def zo {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r) (x:In N):Bool:=
 (List.finRange k).all (fun j=>z7 hk nm c rep gen w n false j x)&&
 (List.finRange k).all (fun j=>z7 hk nm c rep gen w n true j x)
def yY {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (rep:Key N k) (gen:Gen N k k) (w:qI k) (x:In N):Bool:=
 (List.finRange r).all fun n=>zo hk nm c rep gen w n x
lemma kM {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r)
 (b:Bool) (j:Fin k) (x:In N):
 z7 hk nm c rep gen w n b j x=true↔
  (w b (n.val+1) j=true→∀ u v:Fin k,u<v→
    delta (fun s=>za hk nm c rep gen b (n.val+1) j s x) u v=0):=by
 simp only [z7,List.all_eq_true,List.mem_finRange,true_implies]
 constructor
 · intro h hw u v huv
   have:=h u v
   simp only [ya,hw,huv,and_self,↓reduceIte,Bool.not_eq_true',z2b,
    decide_eq_false_iff_not,not_not] at this
   exact this
 · intro h u v
   unfold ya
   by_cases hc:w b (n.val+1) j=true∧u<v
   · simp [hc,h hc.1 u v hc.2,qm]
   · simp only [hc,↓reduceIte]
lemma vO {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r) (x:In N):
 zo hk nm c rep gen w n x=true↔
  ∀ (b:Bool) (j:Fin k),w b (n.val+1) j=true→∀ u v:Fin k,u<v→
    delta (fun s=>za hk nm c rep gen b (n.val+1) j s x) u v=0:=by
 simp only [zo,Bool.and_eq_true,List.all_eq_true,List.mem_finRange,true_implies,
  kM]
 constructor
 · rintro ⟨hf,ht⟩ b j hw u v huv
   cases b
   · exact hf j hw u v huv
   · exact ht j hw u v huv
 · intro h
   exact ⟨fun j=>h false j,fun j=>h true j⟩
lemma kv {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (rep:Key N k) (gen:Gen N k k) (w:qI k) (x:In N):
 yY hk nm c rep gen w x=true↔
  Checks hk (nm x) (c x) (gen x) (rep x) w:=by
 simp only [yY,List.all_eq_true,List.mem_finRange,true_implies,vO]
 constructor
 · intro h b n hn hr j hj u v huv
   obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
   exact h ⟨m,by omega⟩ b j hj u v huv
 · intro h n b j hj u v huv
   exact h b (n.val+1) (by omega) (by omega) j hj u v huv
theorem uL {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r) (b:Bool) (j:Fin k)
 (D:Set (Sig N)) (hT:(fun _=>true)∈D)
 (hbank:k3 hk nm c rep gen⊆D):
 qa D {z7 hk nm c rep gen w n b j} (k * (k * 13+k)+k):=by
 have mem (s:yh k):bit (za hk nm c rep gen b (n.val+1) j s)∈D:=
  hbank (ue hk nm c rep gen s b (n.val+1) (by omega) j)
 let row (u:Fin k):Sig N:=fun x=>(List.finRange k).all fun v=>ya hk nm c rep gen w n b j u v x
 have hrows:qa D (Set.range row) (k * (k * 13+k)):=by
  refine qf row (k * 13+k) (fun u=>?_)
  let t (v:Fin k):Sig N:=ya hk nm c rep gen w n b j u v
  have ht:qa D (Set.range t) (k * 13):=by
   refine qf t 13 (fun v=>?_)
   by_cases hc:w b (n.val+1) j=true∧u<v
   · have q:=uE (za hk nm c rep gen b (n.val+1) j) mem u v
     have hn:=qe q (zn (A:=D ∪ _) (Or.inr rfl))
     have heq:(fun x=>!(z2b (delta (fun s=>za hk nm c rep gen b (n.val+1) j s x) u v)))=t v:=by
      funext x; simp [t,ya,hc]
     rw [heq] at hn
     exact qd hn le_rfl Set.subset_union_right le_rfl
   · have heq:t v=(fun _=>true):=by funext x; simp [t,ya,hc]
     rw [heq]
     exact qd (zk (Set.singleton_subset_iff.mpr hT)) le_rfl Set.subset_union_right (Nat.zero_le _)
  have ha:qa (D ∪ Set.range t) {row u} k:=
   vB t (fun v=>Or.inr ⟨v,rfl⟩) (Or.inl hT)
  exact qe ht ha
 have hall:qa (D ∪ Set.range row) {z7 hk nm c rep gen w n b j} k:=
  vB row (fun u=>Or.inr ⟨u,rfl⟩) (Or.inl hT)
 exact qe hrows hall
theorem jc {N k r:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (rep:Key N k) (gen:Gen N k k) (w:qI k) (n:Fin r)
 (D:Set (Sig N)) (hT:(fun _=>true)∈D)
 (hbank:k3 hk nm c rep gen⊆D):
 qa D {zo hk nm c rep gen w n} (2 * (k * (k * (k * 13+k)+k)+k)+1):=by
 let cf (j:Fin k):=z7 hk nm c rep gen w n false j
 let ct (j:Fin k):=z7 hk nm c rep gen w n true j
 have h1:qa D (Set.range cf) (k * (k * (k * 13+k)+k)):=
  qf cf _ (fun j=>uL hk nm c rep gen w n false j D hT hbank)
 have h2:qa D (Set.range ct) (k * (k * (k * 13+k)+k)):=
  qf ct _ (fun j=>uL hk nm c rep gen w n true j D hT hbank)
 have ha1:qa (D ∪ Set.range cf) {fun x=>(List.finRange k).all fun j=>cf j x} k:=
  vB cf (fun j=>Or.inr ⟨j,rfl⟩) (Or.inl hT)
 have ha2:qa (D ∪ Set.range ct) {fun x=>(List.finRange k).all fun j=>ct j x} k:=
  vB ct (fun j=>Or.inr ⟨j,rfl⟩) (Or.inl hT)
 have hb:=qr (qe h1 ha1) (qe h2 ha2)
 have hand:qa (D ∪ ({fun x=>(List.finRange k).all fun j=>cf j x} ∪
  {fun x=>(List.finRange k).all fun j=>ct j x})) {zo hk nm c rep gen w n} 1:=
  qD (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
 exact qd (qe hb hand) le_rfl Set.subset_union_right (by omega)
def zf {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (n:Fin r) (x:In N):Bool:=
 zo hk nm c (fun y=>qO d (Q y) idx) (fun y=>qb (Q y)) w n x
def vs {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (x:In N):Bool:=
 yY hk nm c (fun y=>qO d (Q y) idx) (fun y=>qb (Q y)) w x
def zr {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (x:In N):Bool:=
 decide ((zm (fun u=>
  kx hk nm c (fun y=>qO d (Q y) idx) (fun y=>qb (Q y)) side site tar u x)).rank≤h)
def q4 {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (x:In N):Bool:=
 (List.finRange (2 ^ d)).all fun idx=>!(zc d (Q x) idx)||vs d hk nm c w Q idx x
def zq {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (x:In N):Bool:=
 (List.finRange (2 ^ d)).all fun idx=>!(zc d (Q x) idx)||zr d hk nm c side site tar h Q idx x
def z8 {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (x:In N):Bool:=
 q4 d hk nm c w Q x&&zq d hk nm c side site tar h Q x
lemma yJ {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (Q:In N→Fin P→V k) (x:In N):
 q4 d hk nm c w Q x=true↔
  ∀ idx:Fin (2 ^ d),zc d (Q x) idx=true→
    Checks hk (nm x) (c x) (qb (Q x)) (qO d (Q x) idx) w:=by
 simp only [q4,List.all_eq_true,List.mem_finRange,true_implies]
 apply forall_congr'; intro idx
 cases hl:zc d (Q x) idx
 · simp
 · simp [vs,kv]
lemma ku {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (x:In N):
 zq d hk nm c side site tar h Q x=true↔
  ∀ idx:Fin (2 ^ d),zc d (Q x) idx=true→
    (matrix (qb (Q x)) (qO d (Q x) idx) (probe hk (nm x) (c x) side site) (tar x)).rank≤h:=by
 simp only [zq,List.all_eq_true,List.mem_finRange,true_implies]
 apply forall_congr'; intro idx
 cases hl:zc d (Q x) idx
 · simp
 · simp only [Bool.not_true,Bool.false_or,zr,decide_eq_true_eq,true_implies]
   exact Iff.rfl
lemma kS {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (hc:closed hk w (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,w (side i) (r+1) (site i)=true) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (x:In N)
 (hrk:Module.finrank F (Submodule.span F (Set.range (Q x)))≤d):
 z8 d hk nm c w side site tar h Q x=true↔
  ze hk w side site h (nm x) (c x) (Q x):=by
 rw [ud hk w hc side site hw h (nm x) (c x) (tar x) (Q x)]
 have hlg:=local_global hk (nm x) (c x) (qb (Q x)) (zc d (Q x)) (qO d (Q x))
  (u8 d (Q x) hrk) w hc side site hw h (tar x)
 dsimp only at hlg
 rw [← hlg]
 simp only [z8,Bool.and_eq_true,yJ,ku]
 constructor
 · rintro ⟨h1,h2⟩ idx hi; exact ⟨h1 idx hi,h2 idx hi⟩
 · intro h12; exact ⟨fun idx hi=>(h12 idx hi).1,fun idx hi=>(h12 idx hi).2⟩
def ym {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k):Set (Sig N):=
 ke d Q ∪
 {f|∃ (idx:Fin (2 ^ d)) (n:Fin r),zf d hk nm c w Q idx n=f} ∪
 Set.range (vs d hk nm c w Q) ∪
 Set.range (zr d hk nm c side site tar h Q) ∪
 {q4 d hk nm c w Q,zq d hk nm c side site tar h Q,
  z8 d hk nm c w side site tar h Q}
private lemma kw (k r t s:ℕ) (hk:k≤ s) (hr:r≤ s) (ht:t≤ s)
 (hs1:1≤ s) (h2s:k+k+r+t+4≤2 * s):
 (1+(k+k * k)) * (2 * (r+2)) * (k * 8+(r+2) * (k * 50)) +
   (r * (2 * (k * (k * (k * 13+k)+k)+k)+1)+r +
     (t * (k * (k * 12)+k * 4+4)+2 ^ 12 * (k+k+r+t+4) ^ 10))≤
   2 ^ 24 * s ^ 10:=by
 have h1:(1+(k+k * k)) * (2 * (r+2)) * (k * 8+(r+2) * (k * 50))≤
  (1+(s+s * s)) * (2 * (s+2)) * (s * 8+(s+2) * (s * 50)):=by gcongr
 have h2:r * (2 * (k * (k * (k * 13+k)+k)+k)+1)+r≤
  s * (2 * (s * (s * (s * 13+s)+s)+s)+1)+s:=by gcongr
 have h3:t * (k * (k * 12)+k * 4+4)≤ s * (s * (s * 12)+s * 4+4):=by gcongr
 have h4:2 ^ 12 * (k+k+r+t+4) ^ 10≤2 ^ 22 * s ^ 10:=by
  calc 2 ^ 12 * (k+k+r+t+4) ^ 10≤2 ^ 12 * (2 * s) ^ 10:=by gcongr
   _=2 ^ 22 * s ^ 10:=by ring
 have hsp5:s ^ 5≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hsp4:s ^ 4≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hsp3:s ^ 3≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hsp2:s ^ 2≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hsp1:s≤ s ^ 10:=by simpa using Nat.pow_le_pow_right hs1 (by decide:1≤10)
 have hexp:(1+(s+s * s)) * (2 * (s+2)) * (s * 8+(s+2) * (s * 50)) +
  (s * (2 * (s * (s * (s * 13+s)+s)+s)+1)+s) +
  s * (s * (s * 12)+s * 4+4)=
  100 * s ^ 5+544 * s ^ 4+962 * s ^ 3+854 * s ^ 2+438 * s:=by ring
 omega
private lemma kR (k P s D:ℕ) (hs1:1≤ s) (hD1:1≤D)
 (hkP:k+P+4≤2 * s):
 128 * (k+P+4) ^ 5 * D+D * (2 ^ 24 * s ^ 10) +
  (D * 2+D+(D * 2+D)+1)≤2 ^ 25 * s ^ 10 * D:=by
 have hker:128 * (k+P+4) ^ 5≤2 ^ 12 * s ^ 10:=by
  have h1:(k+P+4) ^ 5≤(2 * s) ^ 5:=Nat.pow_le_pow_left hkP 5
  have h2:(2 * s) ^ 5=32 * s ^ 5:=by ring
  have h3:s ^ 5≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
  omega
 have hker_mul:128 * (k+P+4) ^ 5 * D≤2 ^ 12 * (s ^ 10 * D):=by
  rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right D hker
 have h1s:D≤ s ^ 10 * D:=Nat.le_mul_of_pos_left D (Nat.one_le_pow 10 s hs1)
 have hcos:D * (2 ^ 24 * s ^ 10)=2 ^ 24 * (s ^ 10 * D):=by ring
 have hgoal:2 ^ 25 * s ^ 10 * D=2 ^ 25 * (s ^ 10 * D):=by ring
 rw [hcos,hgoal]; omega
theorem uH {N k r t P:ℕ} (d:ℕ) (hPk:P≤k) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (A:Set (Sig N))
 (hF:(fun _=>false)∈A) (hT:(fun _=>true)∈A)
 (hnm:∀ b j,(bit fun x=>nm x b j)∈A) (hc:∀ b n j,(bit fun x=>c x b n j)∈A)
 (htar:∀ u,(bit fun x=>tar x u)∈A) (hQ:∀ i j,(fun x=>z2b (Q x i j))∈A):
 qa A (ym d hk nm c w side site tar h Q)
  (2 ^ 25 * (k+r+t+6) ^ 10 * 2 ^ d):=by
 classical
 let s:=k+r+t+6
 have hKer:=j6 d A hF hT Q hQ
 let A1:=A ∪ ke d Q
 have hF1:(fun _=>false)∈A1:=Or.inl hF
 have hT1:(fun _=>true)∈A1:=Or.inl hT
 have hgen1 (i j:Fin k):(bit fun x=>qb (Q x) i j)∈A1:=
  Or.inr (Or.inl (Or.inl (Or.inr ⟨i,j,rfl⟩)))
 have hrep1 (idx:Fin (2 ^ d)) (j:Fin k):(bit fun x=>qO d (Q x) idx j)∈A1:=
  Or.inr (Or.inr ⟨idx,j,rfl⟩)
 have hlive1 (idx:Fin (2 ^ d)):(fun x=>zc d (Q x) idx)∈A1:=
  Or.inr (Or.inl (Or.inr ⟨idx,rfl⟩))
 let perCoset (idx:Fin (2 ^ d)):Set (Sig N):=
  Set.range (zf d hk nm c w Q idx) ∪
  {vs d hk nm c w Q idx} ∪
  {zr d hk nm c side site tar h Q idx}
 have hCoset (idx:Fin (2 ^ d)):qa A1 (perCoset idx) (2 ^ 24 * s ^ 10):=by
  let rep:Key N k:=fun x=>qO d (Q x) idx
  let gen:Gen N k k:=fun x=>qb (Q x)
  have hBank:=yo.uD hk nm c rep gen A1
   (fun b j=>Or.inl (hnm b j)) (fun b n j=>Or.inl (hc b n j))
   (hrep1 idx) hgen1
  let D:=A1 ∪ k3 hk nm c rep gen
  have hRnds:qa D (Set.range (zf d hk nm c w Q idx))
   (r * (2 * (k * (k * (k * 13+k)+k)+k)+1)):=
   qf _ _ (fun n=>jc hk nm c rep gen w n D (Or.inl hT1) Set.subset_union_right)
  have hPref:qa (D ∪ Set.range (zf d hk nm c w Q idx))
   {vs d hk nm c w Q idx} r:=
   vB (zf d hk nm c w Q idx) (fun n=>Or.inr ⟨n,rfl⟩) (Or.inl (Or.inl hT1))
  have hQuads:qa D (⋃ u,qn (kx hk nm c rep gen side site tar u))
   (t * (k * (k * 12)+k * 4+4)):=by
   apply v7; intro u
   let f:=za hk nm c rep gen (side u) (r+1) (site u)
   have hf (smp):bit (f smp)∈D:=Or.inr (ue hk nm c rep gen smp (side u) (r+1) le_rfl (site u))
   exact qr (qr (qT _ 12 (fun i j=>uE f hf i j))
    (qf _ 4 (fun i=>add (get (hf (.inl ()))) (get (hf (.inr (.inl i)))))))
    (add (get (hf (.inl ()))) (get (A:=D) (Or.inl (Or.inl (htar u)))))
  let DQ:=D ∪ ⋃ u,qn (kx hk nm c rep gen side site tar u)
  have hTerm:qa DQ {zr d hk nm c side site tar h Q idx}
   (2 ^ 12 * (k+k+r+t+4) ^ 10):=
   yO k r DQ h (fun x u=>kx hk nm c rep gen side site tar u x)
    (Or.inl (Or.inl hF1)) (Or.inl (Or.inl hT1))
    (fun u _ hmem=>Or.inr (Set.mem_iUnion.mpr ⟨u,hmem⟩))
  have hComb:=qe hBank (qr (zd hRnds hPref) (qe hQuads hTerm))
  refine qd hComb le_rfl ?_ ?_
  · intro f hf
    rcases hf with (hf|hf)|hf
    · exact Or.inr (Or.inl (Or.inl hf))
    · exact Or.inr (Or.inl (Or.inr hf))
    · exact Or.inr (Or.inr hf)
  · exact kw k r t s (by dsimp [s]; omega) (by dsimp [s]; omega)
     (by dsimp [s]; omega) (by dsimp [s]; omega) (by dsimp [s]; omega)
 have hAllCosets:qa A1 (⋃ idx:Fin (2 ^ d),perCoset idx) (2 ^ d * (2 ^ 24 * s ^ 10)):=
  v7 perCoset _ hCoset
 let A2:=A ∪ (ke d Q ∪ ⋃ idx:Fin (2 ^ d),perCoset idx)
 have hPrefAll:qa A2 {q4 d hk nm c w Q} (2 ^ d * 2+2 ^ d):=by
  let chk (idx:Fin (2 ^ d)):Sig N:=fun x=>!(zc d (Q x) idx)||vs d hk nm c w Q idx x
  have hchk:qa A2 (Set.range chk) (2 ^ d * 2):=
   qf chk 2 (fun idx=>qe (zn (Or.inr (Or.inl (Or.inl (Or.inr ⟨idx,rfl⟩)))))
    (orB (Or.inr rfl) (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨idx,Or.inl (Or.inr rfl)⟩))))))
  exact qe hchk (vB chk (fun idx=>Or.inr ⟨idx,rfl⟩) (Or.inl (Or.inl hT)))
 have hTermAll:qa A2 {zq d hk nm c side site tar h Q} (2 ^ d * 2+2 ^ d):=by
  let chk (idx:Fin (2 ^ d)):Sig N:=fun x=>!(zc d (Q x) idx)||zr d hk nm c side site tar h Q idx x
  have hchk:qa A2 (Set.range chk) (2 ^ d * 2):=
   qf chk 2 (fun idx=>qe (zn (Or.inr (Or.inl (Or.inl (Or.inr ⟨idx,rfl⟩)))))
    (orB (Or.inr rfl) (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨idx,Or.inr rfl⟩))))))
  exact qe hchk (vB chk (fun idx=>Or.inr ⟨idx,rfl⟩) (Or.inl (Or.inl hT)))
 have hBoth:qa (A2 ∪ ({q4 d hk nm c w Q} ∪ {zq d hk nm c side site tar h Q}))
  {z8 d hk nm c w side site tar h Q} 1:=
  qD (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
 have hTop:=zd (zd hKer hAllCosets) (zd (qr hPrefAll hTermAll) hBoth)
 refine qd hTop le_rfl ?_ ?_
 · intro f hf
   rcases hf with (((hf|hf)|hf)|hf)|hf
   · exact Or.inr (Or.inl (Or.inl hf))
   · obtain ⟨idx,n,rfl⟩:=hf
     exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨idx,Or.inl (Or.inl ⟨n,rfl⟩)⟩)))
   · obtain ⟨idx,rfl⟩:=hf
     exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨idx,Or.inl (Or.inr rfl)⟩)))
   · obtain ⟨idx,rfl⟩:=hf
     exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨idx,Or.inr rfl⟩)))
   · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
     rcases hf with rfl|rfl|rfl
     · exact Or.inr (Or.inr (Or.inl (Or.inl rfl)))
     · exact Or.inr (Or.inr (Or.inl (Or.inr rfl)))
     · exact Or.inr (Or.inr (Or.inr rfl))
 · exact kR k P s (2 ^ d) (by dsimp [s]; omega) Nat.one_le_two_pow (by dsimp [s]; omega)
def qW {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (n:Fin r) (x:In N):Bool:=
 (List.finRange (2 ^ d)).all fun idx=>!(zc d (Q x) idx)||zf d hk nm c w Q idx n x
def qL {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (n:Fin r) (x:In N):Bool:=
 qi (fun n'=>!(qW d hk nm c w Q n' x)) n
def zE {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (x:In N):Bool:=
 zc d (Q x) idx&&(List.finRange r).any fun n=>
  qL d hk nm c w Q n x&&!(zf d hk nm c w Q idx n x)
def yd {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (x:In N):Bool:=
 qi (fun i=>zE d hk nm c w Q i x) idx
def qt {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (x:In N):V k:=
 vL (fun i=>yd d hk nm c w Q i x) (fun i=>qO d (Q x) i)
def vZ (k:ℕ) (bj:Fin (2 * k)):Bool:=decide (k≤bj.val)
def yi {k:ℕ} (hk:0<k) (bj:Fin (2 * k)):Fin k:=⟨bj.val % k,Nat.mod_lt _ hk⟩
def zH {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (bj:Fin (2 * k)) (x:In N):Bool:=
 (List.finRange r).any fun n=>
   qL d hk nm c w Q n x&&
   !(z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n (vZ k bj) (yi hk bj) x)
def zP {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (bj:Fin (2 * k)) (x:In N):Bool:=
 qi (fun bj'=>zH d hk nm c w Q bj' x) bj
def yA {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (off:ℕ) (nb:Fin r×Fin (2 * k)) (x:In N) (u:Fin k):F:=
 let b:=vZ k nb.2
 let j:=yi hk nb.2
 let rep:=qt d hk nm c w Q x
 let gen:=qb (Q x)
 mix hk b (state hk (nm x) (c x) b (rep+gen u) nb.1.val) (ix hk (j.val+off)) +
 mix hk b (state hk (nm x) (c x) b rep nb.1.val) (ix hk (j.val+off))
def zb {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (off:ℕ) (x:In N):V k:=
 let e:=finProdFinEquiv (m:=r) (n:=2 * k)
 vL (fun p=>qL d hk nm c w Q (e.symm p).1 x&&zP d hk nm c w Q (e.symm p).2 x)
  (fun p=>yA d hk nm c w Q off (e.symm p) x)
def qX {N k r P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (Q:In N→Fin P→V k) (choice:Fin 3) (x:In N) (u:Fin k):F:=
 if qh (Q x) u then
  if choice.val=0 then zb d hk nm c w Q 1 x u
  else if choice.val=1 then zb d hk nm c w Q 2 x u
  else zb d hk nm c w Q 1 x u+zb d hk nm c w Q 2 x u
 else 0
lemma km {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (hc:closed hk w (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (h:ℕ) (Q:In N→Fin P→V k) (x:In N)
 (hfail:q4 d hk nm c w Q x=false)
 (Qopt:Fin P→V k) (hworks:ze hk w side site h (nm x) (c x) Qopt)
 (hle:Submodule.span F (Set.range (Q x))≤Submodule.span F (Set.range Qopt)):
 ∃ choice:Fin 3,
   qX d hk nm c w Q choice x∈Submodule.span F (Set.range Qopt)∧
   qX d hk nm c w Q choice x∉Submodule.span F (Set.range (Q x)):=by
 have hexRound:∃ n:Fin r,!(qW d hk nm c w Q n x)=true:=by
  by_contra hall
  push Not at hall
  have ht:q4 d hk nm c w Q x=true:=by
   rw [yJ]
   intro idx hlive
   exact (kv hk nm c (fun y=>qO d (Q y) idx) (fun y=>qb (Q y)) w x).mp (by
    simp only [yY,List.all_eq_true,List.mem_finRange,true_implies]
    intro n
    have hn:qW d hk nm c w Q n x=true:=by
     cases h':qW d hk nm c w Q n x
     · exfalso; exact hall n (by simp [h'])
     · rfl
    simp only [qW,List.all_eq_true,List.mem_finRange,true_implies] at hn
    have hi:=hn idx
    simp only [hlive,Bool.not_true,Bool.false_or] at hi
    exact hi)
  rw [hfail] at ht; exact Bool.noConfusion ht
 obtain ⟨n0,hn0⟩:=(q0 (fun n'=>!(qW d hk nm c w Q n' x))).mpr hexRound
 have hn0_spec:=(qU (fun n'=>!(qW d hk nm c w Q n' x)) n0).mp hn0
 have hn0_fail:qW d hk nm c w Q n0 x=false:=by
  cases h':qW d hk nm c w Q n0 x <;> simp_all
 have hn0_prev:∀ n:Fin r,n.val<n0.val→qW d hk nm c w Q n x=true:=by
  intro n hlt
  have:=hn0_spec.2 n hlt
  cases h':qW d hk nm c w Q n x <;> simp_all
 have hexCoset:∃ idx:Fin (2 ^ d),zE d hk nm c w Q idx x=true:=by
  by_contra hall
  push Not at hall
  have ht:qW d hk nm c w Q n0 x=true:=by
   simp only [qW,List.all_eq_true,List.mem_finRange,true_implies]
   intro idx
   cases hlive:zc d (Q x) idx
   · simp
   · simp only [Bool.not_true,Bool.false_or]
     cases hr:zf d hk nm c w Q idx n0 x
     · exfalso
       apply hall idx
       simp only [zE,hlive,Bool.true_and,List.any_eq_true,List.mem_finRange,true_and]
       exact ⟨n0,by simp [qL,hn0,hr]⟩
     · rfl
  rw [hn0_fail] at ht; exact Bool.noConfusion ht
 obtain ⟨idx0,hidx0⟩:=(q0 (fun i=>zE d hk nm c w Q i x)).mpr hexCoset
 have hidx0_fail:=((qU (fun i=>zE d hk nm c w Q i x) idx0).mp hidx0).1
 simp only [zE,Bool.and_eq_true,List.any_eq_true,List.mem_finRange,true_and] at hidx0_fail
 obtain ⟨hlive0,n0',hn0'1,hn0'2⟩:=hidx0_fail
 have hn0'_eq:n0'=n0:=q2 (fun n'=>!(qW d hk nm c w Q n' x)) hn0'1 hn0
 subst n0'
 have hrep_eq:qt d hk nm c w Q x=qO d (Q x) idx0:=
  kl _ _ idx0 hidx0 (fun i hi=>q2 _ hi hidx0)
 have hidx0_roundF:zo hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 x=false:=by
  have hr0:zf d hk nm c w Q idx0 n0 x=false:=by
   cases h':zf d hk nm c w Q idx0 n0 x <;> simp_all
  change zo hk nm c (fun y=>qO d (Q y) idx0) (fun y=>qb (Q y)) w n0 x=false at hr0
  have hcongr:∀ (r1 r2:Key N k),r1 x=r2 x→
   zo hk nm c r1 (fun y=>qb (Q y)) w n0 x=
   zo hk nm c r2 (fun y=>qb (Q y)) w n0 x:=by
   intro r1 r2 h12
   apply Bool.eq_iff_iff.mpr
   simp only [vO]
   have hcr:∀ b j s,za hk nm c r1 (fun y=>qb (Q y)) b (n0.val+1) j s x=
    za hk nm c r2 (fun y=>qb (Q y)) b (n0.val+1) j s x:=by
    intro b j s; rcases s with _|(i|⟨i,l⟩) <;> simp [za,yH,h12]
   simp_rw [hcr]
  rw [hcongr (qt d hk nm c w Q) (fun y=>qO d (Q y) idx0) hrep_eq]; exact hr0
 have hexCell:∃ bj:Fin (2 * k),zH d hk nm c w Q bj x=true:=by
  by_contra hall
  push Not at hall
  have ht:zo hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 x=true:=by
   rw [vO]
   intro b j hw u v huv
   let bj:Fin (2 * k):=⟨(if b then k else 0)+j.val,by
    cases b <;> simp only [↓reduceIte,Bool.false_eq_true] <;> omega⟩
   have hside:vZ k bj=b:=by
    cases b
    · simp only [vZ,bj,Bool.false_eq_true,↓reduceIte,Nat.zero_add,decide_eq_false_iff_not]; omega
    · simp only [vZ,bj,↓reduceIte,decide_eq_true_eq]; omega
   have hsite:yi hk bj=j:=by
    apply Fin.ext; cases b <;> simp [yi,bj,Nat.mod_eq_of_lt j.isLt]
   have hc0:z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 b j x=true:=by
    cases h':z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 b j x
    · exfalso; apply hall bj
      simp only [zH,List.any_eq_true,List.mem_finRange,true_and,hside,hsite]
      exact ⟨n0,by simp [qL,hn0,h']⟩
    · rfl
   exact (kM hk nm c _ _ w n0 b j x).mp hc0 hw u v huv
  rw [hidx0_roundF] at ht; exact Bool.noConfusion ht
 obtain ⟨bj0,hbj0⟩:=(q0 (fun bj'=>zH d hk nm c w Q bj' x)).mpr hexCell
 have hbj0_fail:=((qU (fun bj'=>zH d hk nm c w Q bj' x) bj0).mp hbj0).1
 simp only [zH,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true] at hbj0_fail
 obtain ⟨n1,hn1,hcellF⟩:=hbj0_fail
 have hn1_eq:n1=n0:=q2 (fun n'=>!(qW d hk nm c w Q n' x)) hn1 hn0
 subst n1
 let b0:=vZ k bj0
 let j0:=yi hk bj0
 have hcellF':z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 b0 j0 x=false:=by
  cases h':z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 b0 j0 x <;> simp_all [b0,j0]
 have hviol:w b0 (n0.val+1) j0=true∧∃ u v:Fin k,u<v∧
  delta (fun s=>za hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) b0 (n0.val+1) j0 s x) u v≠0:=by
  have hnot:=mt (kM hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n0 b0 j0 x).mpr
   (by rw [hcellF']; decide)
  push Not at hnot
  exact hnot
 obtain ⟨hw0,u0,v0,huv0,hdelta0⟩:=hviol
 have haff_prev:∀ m≤n0.val,∀ j:Fin k,w b0 m j=true→
  Aff (fun a=>state hk (nm x) (c x) b0 (qt d hk nm c w Q x+shift (qb (Q x)) a) m j):=by
  intro m
  induction m with
  | zero=>
    intro _ j _
    exact (aff_key (qb (Q x)) (qt d hk nm c w Q x) (ix hk (j.val+k-start b0 % k))).add (Aff.const (nm x b0 j))
  | succ m' ih=>
    intro hm j hj
    have hm'_lt:m'<n0.val:=by omega
    have hrm:qW d hk nm c w Q ⟨m',by omega⟩ x=true:=hn0_prev ⟨m',by omega⟩ hm'_lt
    simp only [qW,List.all_eq_true,List.mem_finRange,true_implies] at hrm
    have hidx_ok:=hrm idx0
    simp only [hlive0,Bool.not_true,Bool.false_or] at hidx_ok
    have hchk_m':=(vO hk nm c (fun y=>qO d (Q y) idx0) (fun y=>qb (Q y)) w ⟨m',by omega⟩ x).mp hidx_ok b0 j hj
    let key (a:V k):=qt d hk nm c w Q x+shift (qb (Q x)) a
    let Y (i:Fin k) (a:V k):=mix hk b0 (state hk (nm x) (c x) b0 (key a) m') i
    have hY (e:Fin 3):Aff (Y (ix hk (j.val+e.val))):=by
     obtain ⟨h1,h2,h3⟩:=hc b0 m' (by omega) j hj e
     exact ((ih (by omega) _ h1).add (ih (by omega) _ h2)).add (ih (by omega) _ h3)
    have heq0:ix hk (j.val+(0:Fin 3).val)=j:=Fin.ext (by simp [ix,Nat.mod_eq_of_lt j.isLt])
    have h0:Aff (Y j):=heq0▸hY 0
    let Afn:=fun a=>Y j a+rot hk (feed b0 m') (key a) j+c x b0 ⟨m',by omega⟩ j
    let Gfn:=fun a=>1+Y (ix hk (j.val+1)) a
    let Qfn:=Y (ix hk (j.val+2))
    have hA:Aff Afn:=(h0.add (aff_key (qb (Q x)) (qt d hk nm c w Q x) _)).add (Aff.const _)
    have hG:Aff Gfn:=(Aff.const 1).add (hY 1)
    have hQ':Aff Qfn:=hY 2
    have evalStep (a:V k):state hk (nm x) (c x) b0 (key a) (m'+1) j=Afn a+Gfn a * Qfn a:=by
     rw [state_step hk (nm x) (c x) b0 _ m' (by omega)]; unfold update Afn Gfn Qfn Y key; ring
    have hstep:=step_aff hA hG hQ' (fun u v huv=>by
     rw [diff_eq,← evalStep 0,← evalStep (unit u),← evalStep (unit v),← evalStep (unit u+unit v)]
     have hd:=hchk_m' u v huv
     have hs0:state hk (nm x) (c x) b0 (key 0) (m'+1) j=
      za hk nm c (fun y=>qO d (Q y) idx0) (fun y=>qb (Q y)) b0 (m'+1) j (.inl ()) x:=by
      simp [key,shift_zero,za,yH,hrep_eq]
     have hs1:state hk (nm x) (c x) b0 (key (unit u)) (m'+1) j=
      za hk nm c (fun y=>qO d (Q y) idx0) (fun y=>qb (Q y)) b0 (m'+1) j (.inr (.inl u)) x:=by
      simp [key,shift_unit,za,yH,hrep_eq]
     have hs2:state hk (nm x) (c x) b0 (key (unit v)) (m'+1) j=
      za hk nm c (fun y=>qO d (Q y) idx0) (fun y=>qb (Q y)) b0 (m'+1) j (.inr (.inl v)) x:=by
      simp [key,shift_unit,za,yH,hrep_eq]
     have hs3:state hk (nm x) (c x) b0 (key (unit u+unit v)) (m'+1) j=
      za hk nm c (fun y=>qO d (Q y) idx0) (fun y=>qb (Q y)) b0 (m'+1) j (.inr (.inr (u,v))) x:=by
      simp [key,shift_add,shift_unit,za,yH,hrep_eq,add_assoc]
     rw [hs0,hs1,hs2,hs3]; exact hd)
    have hfun:(fun a=>state hk (nm x) (c x) b0 (qt d hk nm c w Q x+shift (qb (Q x)) a) (m'+1) j)=
     (fun a=>Afn a+Gfn a * Qfn a):=funext evalStep
    rw [hfun]; exact hstep
 let rep0:=qt d hk nm c w Q x
 let key (a:V k):=rep0+shift (qb (Q x)) a
 let Y (i:Fin k) (a:V k):=mix hk b0 (state hk (nm x) (c x) b0 (key a) n0.val) i
 have hY (e:Fin 3):Aff (Y (ix hk (j0.val+e.val))):=by
  obtain ⟨h1,h2,h3⟩:=hc b0 n0.val (by omega) j0 hw0 e
  exact ((haff_prev n0.val le_rfl _ h1).add (haff_prev n0.val le_rfl _ h2)).add (haff_prev n0.val le_rfl _ h3)
 have heq0:ix hk (j0.val+(0:Fin 3).val)=j0:=Fin.ext (by simp [ix,Nat.mod_eq_of_lt j0.isLt])
 have hA:Aff (fun a=>Y j0 a+rot hk (feed b0 n0.val) (key a) j0+c x b0 ⟨n0.val,by omega⟩ j0):=
  ((heq0▸hY 0).add (aff_key (qb (Q x)) rep0 _)).add (Aff.const _)
 obtain ⟨aA,vA,hvA⟩:=hA
 obtain ⟨a1,v1,hv1⟩:=hY 1
 obtain ⟨a2,v2,hv2⟩:=hY 2
 have hslope_eq (off:ℕ):zb d hk nm c w Q off x=yA d hk nm c w Q off (n0,bj0) x:=by
  let e:=finProdFinEquiv (m:=r) (n:=2 * k)
  have h1:qL d hk nm c w Q n0 x&&zP d hk nm c w Q bj0 x=true:=by
   simp [qL,zP,hn0,hbj0]
  have huniq:∀ p:Fin (r * (2 * k)),
   (qL d hk nm c w Q (e.symm p).1 x&&zP d hk nm c w Q (e.symm p).2 x=true)→
   p=e (n0,bj0):=by
   intro p hp
   simp only [Bool.and_eq_true] at hp
   have h1':(e.symm p).1=n0:=q2 _ hp.1 hn0
   have h2':(e.symm p).2=bj0:=q2 _ hp.2 hbj0
   have hpair:e.symm p=(n0,bj0):=Prod.ext h1' h2'
   simpa using congrArg e hpair
  simpa [zb,e] using kl
   (fun p=>qL d hk nm c w Q (e.symm p).1 x&&zP d hk nm c w Q (e.symm p).2 x)
   (fun p=>yA d hk nm c w Q off (e.symm p) x)
   (e (n0,bj0)) (by simpa [e] using h1) huniq
 have hv1_eq:v1=qX d hk nm c w Q 0 x:=by
  funext u
  have h0:Y (ix hk (j0.val+1)) 0=a1:=by
   have:=hv1 0; simp [lin] at this; exact this
  have hu:Y (ix hk (j0.val+1)) (unit u)=a1+v1 u:=by
   have:=hv1 (unit u); rw [lin_unit] at this; exact this
  have hsl:zb d hk nm c w Q 1 x u=v1 u:=by
   rw [hslope_eq 1]
   have hku:rep0+qb (Q x) u=key (unit u):=by simp [key,shift_unit]
   have hk0:rep0=key 0:=by simp [key,shift_zero]
   have hval:yA d hk nm c w Q 1 (n0,bj0) x u=
    Y (ix hk (j0.val+1)) (unit u)+Y (ix hk (j0.val+1)) 0:=by
    change mix hk b0 (state hk (nm x) (c x) b0 (rep0+qb (Q x) u) n0.val) (ix hk (j0.val+1)) +
     mix hk b0 (state hk (nm x) (c x) b0 rep0 n0.val) (ix hk (j0.val+1))=_
    rw [hku,hk0]
   rw [hval,hu,h0]; calc a1+v1 u+a1=v1 u+(a1+a1):=by ring
    _=v1 u:=by rw [qj,add_zero]
  cases hf:qh (Q x) u
  · simp only [qX,hf,Bool.false_eq_true,↓reduceIte]
    have hgen0:qb (Q x) u=0:=zJ (Q x) hf
    have hku:key (unit u)=key 0:=by simp [key,shift_unit,shift_zero,hgen0]
    have hyu:Y (ix hk (j0.val+1)) (unit u)=Y (ix hk (j0.val+1)) 0:=by simp [Y,hku]
    rw [hu,h0] at hyu
    have:a1+v1 u=a1+0:=by simpa using hyu
    exact add_left_cancel this
  · simp [qX,hf,hsl]
 have hv2_eq:v2=qX d hk nm c w Q 1 x:=by
  funext u
  have h0:Y (ix hk (j0.val+2)) 0=a2:=by
   have:=hv2 0; simp [lin] at this; exact this
  have hu:Y (ix hk (j0.val+2)) (unit u)=a2+v2 u:=by
   have:=hv2 (unit u); rw [lin_unit] at this; exact this
  have hsl:zb d hk nm c w Q 2 x u=v2 u:=by
   rw [hslope_eq 2]
   have hku:rep0+qb (Q x) u=key (unit u):=by simp [key,shift_unit]
   have hk0:rep0=key 0:=by simp [key,shift_zero]
   have hval:yA d hk nm c w Q 2 (n0,bj0) x u=
    Y (ix hk (j0.val+2)) (unit u)+Y (ix hk (j0.val+2)) 0:=by
    change mix hk b0 (state hk (nm x) (c x) b0 (rep0+qb (Q x) u) n0.val) (ix hk (j0.val+2)) +
     mix hk b0 (state hk (nm x) (c x) b0 rep0 n0.val) (ix hk (j0.val+2))=_
    rw [hku,hk0]
   rw [hval,hu,h0]; calc a2+v2 u+a2=v2 u+(a2+a2):=by ring
    _=v2 u:=by rw [qj,add_zero]
  cases hf:qh (Q x) u
  · simp only [qX,hf,Bool.false_eq_true,↓reduceIte]
    have hgen0:qb (Q x) u=0:=zJ (Q x) hf
    have hku:key (unit u)=key 0:=by simp [key,shift_unit,shift_zero,hgen0]
    have hyu:Y (ix hk (j0.val+2)) (unit u)=Y (ix hk (j0.val+2)) 0:=by simp [Y,hku]
    rw [hu,h0] at hyu
    have:a2+v2 u=a2+0:=by simpa using hyu
    exact add_left_cancel this
  · simp [qX,hf,hsl]
 have hv12_eq:v1+v2=qX d hk nm c w Q 2 x:=by
  funext u
  have h1:=congrFun hv1_eq u
  have h2:=congrFun hv2_eq u
  cases hf:qh (Q x) u
  · simp [qX,hf] at h1 h2 ⊢; rw [h1,h2,add_zero]
  · simp [qX,hf] at h1 h2 ⊢; rw [h1,h2]
 have hstep_val (a:V k):
  state hk (nm x) (c x) b0 (rep0+shift (qb (Q x)) a) (n0.val+1) j0=
  aA+lin vA a+(1+a1+lin v1 a) * (a2+lin v2 a):=by
  rw [state_step hk (nm x) (c x) b0 _ n0.val (by omega)]
  unfold update
  have hrearr:
   Y j0 a+(1+Y (ix hk (j0.val+1)) a) * Y (ix hk (j0.val+2)) a +
     rot hk (feed b0 n0.val) (key a) j0+c x b0 ⟨n0.val,by omega⟩ j0=
   (Y j0 a+rot hk (feed b0 n0.val) (key a) j0+c x b0 ⟨n0.val,by omega⟩ j0) +
     (1+Y (ix hk (j0.val+1)) a) * Y (ix hk (j0.val+2)) a:=by ring
  change Y j0 a+(1+Y (ix hk (j0.val+1)) a) * Y (ix hk (j0.val+2)) a +
   rot hk (feed b0 n0.val) (key a) j0+c x b0 ⟨n0.val,by omega⟩ j0=_
  have hvAa:=hvA a; dsimp only at hvAa
  have hv1a:Y (ix hk (j0.val+1)) a=a1+lin v1 a:=hv1 a
  have hv2a:Y (ix hk (j0.val+2)) a=a2+lin v2 a:=hv2 a
  rw [hrearr,hvAa,hv1a,hv2a]; ring
 have hcross (a b:V k):
  state hk (nm x) (c x) b0 rep0 (n0.val+1) j0 +
  state hk (nm x) (c x) b0 (rep0+shift (qb (Q x)) a) (n0.val+1) j0 +
  state hk (nm x) (c x) b0 (rep0+shift (qb (Q x)) b) (n0.val+1) j0 +
  state hk (nm x) (c x) b0 (rep0+shift (qb (Q x)) a+shift (qb (Q x)) b) (n0.val+1) j0=
  dotProduct v1 a * dotProduct v2 b+dotProduct v1 b * dotProduct v2 a:=by
  have h0:=hstep_val 0
  have ha:=hstep_val a
  have hb:=hstep_val b
  have hab:=hstep_val (a+b)
  simp only [shift_zero,add_zero] at h0
  have hadd:rep0+shift (qb (Q x)) (a+b)=rep0+shift (qb (Q x)) a+shift (qb (Q x)) b:=by
   rw [shift_add,add_assoc]
  rw [hadd] at hab
  rw [h0,ha,hb,hab]
  have hl0 (v:V k):lin v 0=0:=by simp [lin]
  have hldot (v u:V k):lin v u=dotProduct v u:=rfl
  simp only [hl0,hldot,dotProduct_add]
  exact y8 aA (1+a1) a2 (dotProduct vA a) (dotProduct vA b)
   (dotProduct v1 a) (dotProduct v1 b) (dotProduct v2 a) (dotProduct v2 b)
 have hv_ne:v1≠0∧v2≠0∧v1+v2≠0:=by
  have hd0:v1 u0 * v2 v0+v1 v0 * v2 u0≠0:=by
   have hc0:=hcross (unit u0) (unit v0)
   have hdot (v:V k) (i:Fin k):dotProduct v (unit i)=v i:=lin_unit v i
   simp only [shift_unit,hdot] at hc0
   rw [← hc0]
   exact hdelta0
  refine ⟨?_,?_,?_⟩
  · intro h0; rw [h0] at hd0; simp at hd0
  · intro h0; rw [h0] at hd0; simp at hd0
  · intro h0
    have heq:v1=v2:=by
     funext j; have hj:=congrFun h0 j; simp only [Pi.add_apply,Pi.zero_apply] at hj
     calc v1 j=v1 j+(v1 j+v2 j):=by rw [hj,add_zero]
      _=v2 j:=by rw [← add_assoc,qj,zero_add]
    rw [heq] at hd0
    exact hd0 (by rw [mul_comm (v2 v0),qj])
 let Dopt:Submodule F (V k):=zM (Submodule.span F (Set.range Qopt))
 have hDopt_le:∀ u∈Dopt,∀ i,dotProduct (Q x i) u=0:=by
  intro u hu i
  rw [dotProduct_comm]
  exact hu (Q x i) (hle (Submodule.subset_span ⟨i,rfl⟩))
 have hzero_Dopt:∀ a∈Dopt,∀ b∈Dopt,
  dotProduct v1 a * dotProduct v2 b+dotProduct v1 b * dotProduct v2 a=0:=by
  intro a ha b hb
  have hshift_a:shift (qb (Q x)) a=a:=qV (Q x) (hDopt_le a ha)
  have hshift_b:shift (qb (Q x)) b=b:=qV (Q x) (hDopt_le b hb)
  rw [← hcross a b,hshift_a,hshift_b]
  have ha':∀ i,dotProduct (Qopt i) a=0:=fun i=>by
   rw [dotProduct_comm]; exact ha (Qopt i) (Submodule.subset_span ⟨i,rfl⟩)
  have hb':∀ i,dotProduct (Qopt i) b=0:=fun i=>by
   rw [dotProduct_comm]; exact hb (Qopt i) (Submodule.subset_span ⟨i,rfl⟩)
  exact hworks.1 rep0 b0 (n0.val+1) (by omega) j0 hw0 ⟨a,ha'⟩ ⟨b,hb'⟩
 have hmem_Dopt_of:∀ v:V k,(∀ u∈Dopt,dotProduct v u=0)→v∈Submodule.span F (Set.range Qopt):=by
  intro v hv
  apply yw Qopt v
  intro u hu
  apply hv u
  intro w hw
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i,rfl⟩; rw [dotProduct_comm]; exact hu i
  · exact dotProduct_zero _
  · intro x1 y1 _ _ hx hy; rw [dotProduct_add,hx,hy,add_zero]
  · intro a0 x1 _ hx; rw [dotProduct_smul,hx,smul_zero]
 have hsupp (ch:Fin 3) (j:Fin k) (hf:qh (Q x) j=false):
  qX d hk nm c w Q ch x j=0:=by simp [qX,hf]
 rcases kc v1 v2 Dopt hzero_Dopt with h1|h2|h3
 · refine ⟨0,hmem_Dopt_of _ (hv1_eq▸h1),
    zt (Q x) (hsupp 0) (hv1_eq▸hv_ne.1)⟩
 · refine ⟨1,hmem_Dopt_of _ (hv2_eq▸h2),
    zt (Q x) (hsupp 1) (hv2_eq▸hv_ne.2.1)⟩
 · refine ⟨2,hmem_Dopt_of _ (hv12_eq▸h3),
    zt (Q x) (hsupp 2) (hv12_eq▸hv_ne.2.2)⟩
private lemma uI (k r s D:ℕ) (hk:k≤ s) (hr:r≤ s) (hs1:1≤ s) (hD1:1≤D):
 (r * (D * 2+D)+(r * 1+3 * r)+(D * (r * 2+r+1)+(3 * D+k * (2 * D)))) +
   ((1+(k+k * k)) * (2 * (r+2)) * (k * 8+(r+2) * (k * 50)) +
     ((2 * k * (r * (k * (k * 13+k)+k+2)+r)+3 * (2 * k)) +
       ((r * (2 * k) * 1+((r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k)))) +
         (r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k))))))+3 * (k * 5))))≤
   2 ^ 18 * s ^ 8 * D:=by
 have hA:r * (D * 2+D)+(r * 1+3 * r)+(D * (r * 2+r+1)+(3 * D+k * (2 * D)))≤
  (12 * s+4) * D:=by
  have h0:r * 1+3 * r≤4 * (s * D):=by
   calc r * 1+3 * r=4 * r:=by ring
    _≤4 * s:=by omega
    _≤4 * s * D:=Nat.le_mul_of_pos_right _ hD1
    _=4 * (s * D):=by ring
  have h1:r * (D * 2+D)≤3 * (s * D):=by
   calc r * (D * 2+D)=3 * (r * D):=by ring
    _≤3 * (s * D):=by gcongr
  have h2:D * (r * 2+r+1)≤3 * (s * D)+D:=by
   calc D * (r * 2+r+1)=3 * (r * D)+D:=by ring
    _≤3 * (s * D)+D:=by gcongr
  have h3:k * (2 * D)≤2 * (s * D):=by
   calc k * (2 * D)=2 * (k * D):=by ring
    _≤2 * (s * D):=by gcongr
  have hrhs:(12 * s+4) * D=12 * (s * D)+4 * D:=by ring
  rw [hrhs]; omega
 have hB:(1+(k+k * k)) * (2 * (r+2)) * (k * 8+(r+2) * (k * 50)) +
  ((2 * k * (r * (k * (k * 13+k)+k+2)+r)+3 * (2 * k)) +
    ((r * (2 * k) * 1+((r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k)))) +
      (r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k))))))+3 * (k * 5)))≤2 ^ 17 * s ^ 8:=by
  have h1:(1+(k+k * k)) * (2 * (r+2)) * (k * 8+(r+2) * (k * 50))≤
   (1+(s+s * s)) * (2 * (s+2)) * (s * 8+(s+2) * (s * 50)):=by gcongr
  have h2:2 * k * (r * (k * (k * 13+k)+k+2)+r)+3 * (2 * k)≤
   2 * s * (s * (s * (s * 13+s)+s+2)+s)+3 * (2 * s):=by gcongr
  have h3:r * (2 * k) * 1+((r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k)))) +
        (r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k)))))+3 * (k * 5)≤
   s * (2 * s) * 1+((s * (2 * s) * (s * 20)+s * (2 * (s * (2 * s)))) +
     (s * (2 * s) * (s * 20)+s * (2 * (s * (2 * s)))))+3 * (s * 5):=by gcongr
  have hsp5:s ^ 5≤ s ^ 8:=Nat.pow_le_pow_right hs1 (by decide)
  have hsp4:s ^ 4≤ s ^ 8:=Nat.pow_le_pow_right hs1 (by decide)
  have hsp3:s ^ 3≤ s ^ 8:=Nat.pow_le_pow_right hs1 (by decide)
  have hsp2:s ^ 2≤ s ^ 8:=Nat.pow_le_pow_right hs1 (by decide)
  have hsp1:s≤ s ^ 8:=by simpa using Nat.pow_le_pow_right hs1 (by decide:1≤8)
  have hexp1:(1+(s+s * s)) * (2 * (s+2)) * (s * 8+(s+2) * (s * 50))=
   100 * s ^ 5+516 * s ^ 4+948 * s ^ 3+848 * s ^ 2+432 * s:=by ring
  have hexp2:2 * s * (s * (s * (s * 13+s)+s+2)+s)+3 * (2 * s)=
   28 * s ^ 4+2 * s ^ 3+6 * s ^ 2+6 * s:=by ring
  have hexp3:s * (2 * s) * 1+((s * (2 * s) * (s * 20)+s * (2 * (s * (2 * s)))) +
        (s * (2 * s) * (s * 20)+s * (2 * (s * (2 * s)))))+3 * (s * 5)=
   88 * s ^ 3+2 * s ^ 2+15 * s:=by ring
  rw [hexp1] at h1; rw [hexp2] at h2; rw [hexp3] at h3
  omega
 have hA2:(12 * s+4) * D≤2 ^ 17 * s ^ 8 * D:=by
  apply Nat.mul_le_mul_right
  have hsp1:s≤ s ^ 8:=by simpa using Nat.pow_le_pow_right hs1 (by decide:1≤8)
  have hsp0:1≤ s ^ 8:=Nat.one_le_pow 8 s hs1
  omega
 have hB2:2 ^ 17 * s ^ 8≤2 ^ 17 * s ^ 8 * D:=Nat.le_mul_of_pos_right _ hD1
 have hsum:2 ^ 18 * s ^ 8 * D=2 ^ 17 * s ^ 8 * D+2 ^ 17 * s ^ 8 * D:=by ring
 rw [hsum]; omega
theorem jO {N k r t P:ℕ} (d:ℕ) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (A:Set (Sig N))
 (hF:(fun _=>false)∈A) (hT:(fun _=>true)∈A)
 (hnm:∀ b j,(bit fun x=>nm x b j)∈A) (hc:∀ b n j,(bit fun x=>c x b n j)∈A)
 (hChk:ym d hk nm c w side site tar h Q⊆A):
 qa A {f|∃ (ch:Fin 3) (u:Fin k),(fun x=>z2b (qX d hk nm c w Q ch x u))=f}
  (2 ^ 18 * (k+r+t+6) ^ 8 * 2 ^ d):=by
 classical
 let s:=k+r+t+6
 have hfreeA (j:Fin k):(fun x=>qh (Q x) j)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j,rfl⟩)))))))
 have hgenA (i j:Fin k):(bit fun x=>qb (Q x) i j)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i,j,rfl⟩)))))))
 have hliveA (idx:Fin (2 ^ d)):(fun x=>zc d (Q x) idx)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx,rfl⟩))))))
 have hrepA (idx:Fin (2 ^ d)) (j:Fin k):(bit fun x=>qO d (Q x) idx j)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx,j,rfl⟩)))))
 have hrndA (idx:Fin (2 ^ d)) (n:Fin r):zf d hk nm c w Q idx n∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx,n,rfl⟩))))
 have hRndAll:qa A (Set.range (qW d hk nm c w Q)) (r * (2 ^ d * 2+2 ^ d)):=by
  refine qf _ _ (fun n=>?_)
  let chk (idx:Fin (2 ^ d)):Sig N:=fun x=>!(zc d (Q x) idx)||zf d hk nm c w Q idx n x
  have h1:=qf chk 2 (fun idx=>qe (zn (hliveA idx)) (orB (Or.inr rfl) (Or.inl (hrndA idx n))))
  exact qe h1 (vB chk (fun idx=>Or.inr ⟨idx,rfl⟩) (Or.inl hT))
 let A1:=A ∪ Set.range (qW d hk nm c w Q)
 have hNegRnd:qa A1 (Set.range (fun n x=>!(qW d hk nm c w Q n x))) (r * 1):=
  qf _ 1 (fun n=>zn (Or.inr ⟨n,rfl⟩))
 have hFirstRnd:qa (A1 ∪ Set.range (fun n x=>!(qW d hk nm c w Q n x)))
  (Set.range (qL d hk nm c w Q)) (3 * r):=
  yk _ (Or.inl (Or.inl hF)) (fun n=>Or.inr ⟨n,rfl⟩)
 have hS1:qa A (Set.range (qL d hk nm c w Q)) (r * (2 ^ d * 2+2 ^ d)+(r * 1+3 * r)):=
  qe hRndAll (qe hNegRnd hFirstRnd)
 let A2:=A ∪ Set.range (qL d hk nm c w Q)
 have hCosFail:qa A2 (Set.range (zE d hk nm c w Q)) (2 ^ d * (r * 2+r+1)):=by
  refine qf _ _ (fun idx=>?_)
  let term (n:Fin r):Sig N:=fun x=>qL d hk nm c w Q n x&&!(zf d hk nm c w Q idx n x)
  have ht:qa A2 (Set.range term) (r * 2):=
   qf term 2 (fun n=>qe (zn (Or.inl (hrndA idx n)))
    (qD (Or.inl (Or.inr ⟨n,rfl⟩)) (Or.inr rfl)))
  have ha:qa (A2 ∪ Set.range term) {fun x=>(List.finRange r).any fun n=>term n x} r:=
   vC term (fun n=>Or.inr ⟨n,rfl⟩) (Or.inl (Or.inl hF))
  exact qe (qe ht ha) (qD (Or.inl (Or.inl (hliveA idx))) (Or.inr rfl))
 have hFirstCos:qa (A2 ∪ Set.range (zE d hk nm c w Q))
  (Set.range (yd d hk nm c w Q)) (3 * 2 ^ d):=
  yk _ (Or.inl (Or.inl hF)) (fun idx=>Or.inr ⟨idx,rfl⟩)
 have hRepFail:qa ((A2 ∪ Set.range (zE d hk nm c w Q)) ∪ Set.range (yd d hk nm c w Q))
  (Set.range (fun j x=>z2b (qt d hk nm c w Q x j))) (k * (2 * 2 ^ d)):=
  kT (Or.inl (Or.inl (Or.inl hF))) (yd d hk nm c w Q)
   (fun idx x=>qO d (Q x) idx) (fun idx=>Or.inr ⟨idx,rfl⟩)
   (fun idx j=>Or.inl (Or.inl (Or.inl (hrepA idx j))))
 have hS2:=zd hS1 (qe hCosFail (qe hFirstCos hRepFail))
 let A3:=A ∪ (Set.range (qL d hk nm c w Q) ∪
  Set.range (fun j x=>z2b (qt d hk nm c w Q x j)))
 have hF3:(fun _=>false)∈A3:=Or.inl hF
 have hT3:(fun _=>true)∈A3:=Or.inl hT
 have hFR3 (n:Fin r):qL d hk nm c w Q n∈A3:=Or.inr (Or.inl ⟨n,rfl⟩)
 have hRF3 (j:Fin k):(bit fun x=>qt d hk nm c w Q x j)∈A3:=Or.inr (Or.inr ⟨j,rfl⟩)
 have hBank:=yo.uD hk nm c (qt d hk nm c w Q) (fun x=>qb (Q x)) A3
  (fun b j=>Or.inl (hnm b j)) (fun b n j=>Or.inl (hc b n j)) hRF3 (fun i j=>Or.inl (hgenA i j))
 let D:=A3 ∪ k3 hk nm c (qt d hk nm c w Q) (fun x=>qb (Q x))
 have hCellFail:qa D (Set.range (zH d hk nm c w Q))
  (2 * k * (r * (k * (k * 13+k)+k+2)+r)):=by
  refine qf _ _ (fun bj=>?_)
  let term (n:Fin r):Sig N:=fun x=>
   qL d hk nm c w Q n x&&
   !(z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n (vZ k bj) (yi hk bj) x)
  have ht:qa D (Set.range term) (r * (k * (k * 13+k)+k+2)):=by
   refine qf term _ (fun n=>?_)
   have hc1:=uL hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n
    (vZ k bj) (yi hk bj) D (Or.inl hT3) Set.subset_union_right
   let negC:Sig N:=fun x=>!(z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n (vZ k bj) (yi hk bj) x)
   have hc2:qa (D ∪ {z7 hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) w n (vZ k bj) (yi hk bj)}) {negC} 1:=
    zn (Or.inr rfl)
   have hc12:=qe hc1 hc2
   have hc3:qa (D ∪ {negC}) {term n} 1:=qD (Or.inl (Or.inl (hFR3 n))) (Or.inr rfl)
   exact qd (qe hc12 hc3) le_rfl Set.subset_union_right (by omega)
  exact qe ht (vC term (fun n=>Or.inr ⟨n,rfl⟩) (Or.inl (Or.inl hF3)))
 have hFirstCell:qa (D ∪ Set.range (zH d hk nm c w Q))
  (Set.range (zP d hk nm c w Q)) (3 * (2 * k)):=
  yk _ (Or.inl (Or.inl hF3)) (fun bj=>Or.inr ⟨bj,rfl⟩)
 let D1:=D ∪ Set.range (zP d hk nm c w Q)
 let e:=finProdFinEquiv (m:=r) (n:=2 * k)
 let sel (p:Fin (r * (2 * k))):Sig N:=fun x=>
  qL d hk nm c w Q (e.symm p).1 x&&zP d hk nm c w Q (e.symm p).2 x
 have hSel:qa D1 (Set.range sel) (r * (2 * k) * 1):=
  qf sel 1 (fun p=>qD (Or.inl (Or.inl (hFR3 (e.symm p).1))) (Or.inr ⟨(e.symm p).2,rfl⟩))
 have hSlope (off:ℕ):qa (D1 ∪ Set.range sel)
  (Set.range (fun u x=>z2b (zb d hk nm c w Q off x u)))
  (r * (2 * k) * (k * 20)+k * (2 * (r * (2 * k)))):=by
  have hSl:qa (D1 ∪ Set.range sel)
   {f|∃ (p:Fin (r * (2 * k))) (u:Fin k),(fun x=>z2b (yA d hk nm c w Q off (e.symm p) x u))=f}
   (r * (2 * k) * (k * 20)):=by
   refine qT _ 20 (fun p u=>?_)
   let nb:=e.symm p
   let b:=vZ k nb.2
   let j:=yi hk nb.2
   let j':=ix hk (j.val+off)
   have mS (smp:yh k) (i:Fin k):
    yB (D1 ∪ Set.range sel) (fun x=>state hk (nm x) (c x) b (yH (qt d hk nm c w Q) (fun y=>qb (Q y)) smp x) nb.1.val i) 0:=
    get (Or.inl (Or.inl (Or.inr (ue hk nm c (qt d hk nm c w Q) (fun y=>qb (Q y)) smp b nb.1.val (by omega) i))))
   have hmix (smp:yh k):
    yB (D1 ∪ Set.range sel) (fun x=>mix hk b (state hk (nm x) (c x) b (yH (qt d hk nm c w Q) (fun y=>qb (Q y)) smp x) nb.1.val) j') 8:=
    add (add (mS smp j') (mS smp _)) (mS smp _)
   have htot:=add (hmix (.inr (.inl u))) (hmix (.inl ()))
   exact qd htot le_rfl Set.subset_union_right (by decide)
  have hMux:=kT (A:=(D1 ∪ Set.range sel) ∪ {f|∃ (p:Fin (r * (2 * k))) (u:Fin k),
   (fun x=>z2b (yA d hk nm c w Q off (e.symm p) x u))=f})
   (Or.inl (Or.inl (Or.inl (Or.inl hF3)))) sel (fun p x=>yA d hk nm c w Q off (e.symm p) x)
   (fun p=>Or.inl (Or.inr ⟨p,rfl⟩)) (fun p u=>Or.inr ⟨p,u,rfl⟩)
  exact qe hSl hMux
 have hBothSl:=qe hSel (qr (hSlope 1) (hSlope 2))
 let D2:=D1 ∪ (Set.range (fun u x=>z2b (zb d hk nm c w Q 1 x u)) ∪
               Set.range (fun u x=>z2b (zb d hk nm c w Q 2 x u)))
 have hCuts:qa D2 {f|∃ (ch:Fin 3) (u:Fin k),(fun x=>z2b (qX d hk nm c w Q ch x u))=f}
  (3 * (k * 5)):=by
  refine qT _ 5 (fun ch u=>?_)
  have hf:(fun x=>qh (Q x) u)∈D2:=Or.inl (Or.inl (Or.inl (Or.inl (hfreeA u))))
  have hs1:(fun x=>z2b (zb d hk nm c w Q 1 x u))∈D2:=Or.inr (Or.inl ⟨u,rfl⟩)
  have hs2:(fun x=>z2b (zb d hk nm c w Q 2 x u))∈D2:=Or.inr (Or.inr ⟨u,rfl⟩)
  fin_cases ch
  · have heq:(fun x=>qh (Q x) u&&z2b (zb d hk nm c w Q 1 x u))=
     (fun x=>z2b (qX d hk nm c w Q 0 x u)):=by
     funext x; cases hfr:qh (Q x) u <;> simp [qX,hfr,qm]
    exact qd (heq▸qD hf hs1) le_rfl Set.subset_union_right (by decide)
  · have heq:(fun x=>qh (Q x) u&&z2b (zb d hk nm c w Q 2 x u))=
     (fun x=>z2b (qX d hk nm c w Q 1 x u)):=by
     funext x; cases hfr:qh (Q x) u <;> simp [qX,hfr,qm]
    exact qd (heq▸qD hf hs2) le_rfl Set.subset_union_right (by decide)
  · let xsig:Sig N:=fun x=>xor (z2b (zb d hk nm c w Q 1 x u)) (z2b (zb d hk nm c w Q 2 x u))
    let osig:Sig N:=fun x=>qh (Q x) u&&xsig x
    have hxor:qa D2 {xsig} 4:=yW hs1 hs2
    have hand:qa (D2 ∪ {xsig}) {osig} 1:=qD (Or.inl hf) (Or.inr rfl)
    have heq:osig=(fun x=>z2b (qX d hk nm c w Q 2 x u)):=by
     funext x; cases hfr:qh (Q x) u <;> simp [osig,xsig,qX,hfr,qm,vW]
    rw [heq] at hand
    exact qe hxor hand
 have hS3:=qe hBank (qe (qe hCellFail hFirstCell) (qe hBothSl hCuts))
 refine qd (qe hS2 hS3) le_rfl Set.subset_union_right ?_
 exact uI k r s (2 ^ d) (by dsimp [s]; omega) (by dsimp [s]; omega)
  (by dsimp [s]; omega) Nat.one_le_two_pow
def qC (t P h:ℕ):ℕ:=
 if t≤h then 3 else max 3 (((2:ℕ) ^ (min t h+1)-1) * (2 ^ (min P (min t h+1)+1)-1))
lemma y9 (t P h:ℕ):3≤qC t P h:=by
 unfold qC; split_ifs
 · exact le_rfl
 · exact le_max_left 3 _
def zO {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (x:In N):Bool:=
 zc d (Q x) idx&&!(zr d hk nm c side site tar h Q idx x)
def ye {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (idx:Fin (2 ^ d)) (x:In N):Bool:=
 qi (fun i=>zO d hk nm c side site tar h Q i x) idx
def zW {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (x:In N):V k:=
 vL (fun i=>ye d hk nm c side site tar h Q i x) (fun i=>qO d (Q x) i)
def zR {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (x:In N) (i:Fin t) (a:Fin (k * k)):F:=
 let uv:=finProdFinEquiv.symm a
 (kx hk nm c (zW d hk nm c side site tar h Q) (fun y=>qb (Q y)) side site tar i x).B uv.1 uv.2
def yb {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (x:In N):Fin (min t h+1)→Fin (k * k)→F:=
 let M:=zR d hk nm c side site tar h Q x
 vl (qA M (fun _=>Fin.elim0)).used M
def q9 {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (m_idx:Fin (2 ^ (min t h+1)-1)) (x:In N) (u v:Fin k):F:=
 ∑ s:Fin (min t h+1),
   if (m_idx.val+1).testBit s.val then
    yb d hk nm c side site tar h Q x s (finProdFinEquiv (u,v))
   else 0
def yK {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (m_idx:Fin (2 ^ (min t h+1)-1)) (x:In N):
    Fin (min P (min t h+1)+1)→V k:=
 let Gc:=qA (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0)
 vl Gc.used Gc.M
def vb {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (m_idx:Fin (2 ^ (min t h+1)-1))
    (c_idx:Fin (2 ^ (min P (min t h+1)+1)-1)) (x:In N) (j:Fin k):F:=
 ∑ s:Fin (min P (min t h+1)+1),
   if (c_idx.val+1).testBit s.val then
    yK d hk nm c side site tar h Q m_idx x s j
   else 0
def zY {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (b:Fin (qC t P h)) (x:In N):V k:=
 let M1:=2 ^ (min t h+1)-1
 let M2:=2 ^ (min P (min t h+1)+1)-1
 if hb:b.val<M1 * M2 then
  have hM2:0<M2:=by
   have:2≤2 ^ (min P (min t h+1)+1):=by
    rw [Nat.pow_succ]; have:=Nat.one_le_two_pow (n:=min P (min t h+1)); omega
   omega
  have hm1:b.val / M2<M1:=Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)
  vb d hk nm c side site tar h Q ⟨b.val / M2,hm1⟩ ⟨b.val % M2,Nat.mod_lt _ hM2⟩ x
 else 0
def q5 {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (b:Fin (qC t P h)) (x:In N) (j:Fin k):F:=
 if t≤h then
  qX d hk nm c w Q ⟨b.val % 3,Nat.mod_lt _ (by decide)⟩ x j
 else if q4 d hk nm c w Q x then
  zY d hk nm c side site tar h Q b x j
 else
  qX d hk nm c w Q ⟨b.val % 3,Nat.mod_lt _ (by decide)⟩ x j
lemma k1 {k:ℕ} (w1 w2 u v:V k):
 lin w1 u * lin w2 v+lin w1 v * lin w2 u=
  dotProduct u ((Matrix.of fun a b=>w1 a * w2 b+w1 b * w2 a).mulVec v):=by
 simp only [dotProduct,Matrix.mulVec,Matrix.of_apply,lin,Finset.mul_sum,
  mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
 congr 1
 · rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
 · apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
lemma uB {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (hc:closed hk w (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,w (side i) (r+1) (site i)=true) (tar:In N→V t) (h:ℕ)
 (ht:¬ t≤h) (Q:In N→Fin P→V k) (x:In N)
 (_hrk:Module.finrank F (Submodule.span F (Set.range (Q x)))≤d)
 (hpref:q4 d hk nm c w Q x=true)
 (htfail:zq d hk nm c side site tar h Q x=false)
 (Qopt:Fin P→V k) (hworks:ze hk w side site h (nm x) (c x) Qopt)
 (hle:Submodule.span F (Set.range (Q x))≤Submodule.span F (Set.range Qopt)):
 ∃ b:Fin (qC t P h),
   zY d hk nm c side site tar h Q b x∈Submodule.span F (Set.range Qopt)∧
   zY d hk nm c side site tar h Q b x∉Submodule.span F (Set.range (Q x)):=by
 classical
 have hH:min t h=h:=Nat.min_eq_right (by omega)
 have hexCoset:∃ idx:Fin (2 ^ d),zO d hk nm c side site tar h Q idx x=true:=by
  by_contra hall
  push Not at hall
  have ht':zq d hk nm c side site tar h Q x=true:=by
   simp only [zq,List.all_eq_true,List.mem_finRange,true_implies]
   intro idx
   cases hlive:zc d (Q x) idx
   · simp
   · simp only [Bool.not_true,Bool.false_or]
     cases hr:zr d hk nm c side site tar h Q idx x
     · exfalso; apply hall idx; simp [zO,hlive,hr]
     · rfl
  rw [htfail] at ht'; exact Bool.noConfusion ht'
 obtain ⟨idx0,hidx0⟩:=(q0 (fun i=>zO d hk nm c side site tar h Q i x)).mpr hexCoset
 have hidx0_fail:=((qU (fun i=>zO d hk nm c side site tar h Q i x) idx0).mp hidx0).1
 simp only [zO,Bool.and_eq_true,Bool.not_eq_true'] at hidx0_fail
 obtain ⟨hlive0,hterm0F⟩:=hidx0_fail
 have hrep_eq:zW d hk nm c side site tar h Q x=qO d (Q x) idx0:=
  kl _ _ idx0 hidx0 (fun i hi=>q2 _ hi hidx0)
 let rep0:=zW d hk nm c side site tar h Q x
 have hchk0:Checks hk (nm x) (c x) (qb (Q x)) rep0 w:=by
  rw [show rep0=qO d (Q x) idx0 from hrep_eq]
  exact (yJ d hk nm c w Q x).mp hpref idx0 hlive0
 let M:=zR d hk nm c side site tar h Q x
 have hM_uv (i:Fin t) (u v:Fin k):
  M i (finProdFinEquiv (u,v))=
    (sample (qb (Q x)) rep0 (fun key=>state hk (nm x) (c x) (side i) key (r+1) (site i)) (tar x i)).B u v:=by
  simp only [M,zR,Equiv.symm_apply_apply]; rfl
 let Gt:=qA M (fun _=>Fin.elim0)
 have hM_eq_mat:Matrix.of M=Matrix.reindex (Equiv.refl (Fin t)) finProdFinEquiv
  (matrix (qb (Q x)) rep0 (probe hk (nm x) (c x) side site) (tar x)):=by
  ext i a; rfl
 have hM_rk_eq:(Finset.univ.filter (fun i:Fin t=>Gt.used i=true)).card=
  (matrix (qb (Q x)) rep0 (probe hk (nm x) (c x) side site) (tar x)).rank:=by
  calc (Finset.univ.filter (fun i:Fin t=>Gt.used i=true)).card
   =Module.finrank F (Submodule.span F (Set.range M)):=zw M (fun _=>Fin.elim0)
   _=(Matrix.of M).rank:=(zl (Matrix.of M)).symm
   _=(matrix (qb (Q x)) rep0 (probe hk (nm x) (c x) side site) (tar x)).rank:=by
        rw [hM_eq_mat]; exact Matrix.rank_reindex (Equiv.refl _) finProdFinEquiv _
 have hM_rk_gt:min t h+1≤(Finset.univ.filter (fun i:Fin t=>Gt.used i=true)).card:=by
  rw [hM_rk_eq]
  have hgt:¬ (matrix (qb (Q x)) (qO d (Q x) idx0) (probe hk (nm x) (c x) side site) (tar x)).rank≤h:=by
   intro hle'
   have hnt:zr d hk nm c side site tar h Q idx0 x=true:=decide_eq_true hle'
   rw [hterm0F] at hnt; exact Bool.noConfusion hnt
  have hgt':¬ (matrix (qb (Q x)) rep0 (probe hk (nm x) (c x) side site) (tar x)).rank≤h:=by
   change ¬ (matrix (qb (Q x)) (zW d hk nm c side site tar h Q x) _ _).rank≤h
   rwa [hrep_eq]
  omega
 obtain ⟨pick,hpick_inj,hpick_used,hpick_eq⟩:=k0 Gt.used M hM_rk_gt
 have hbas_eq (s:Fin (min t h+1)):yb d hk nm c side site tar h Q x s=M (pick s):=hpick_eq s
 have hB_li:LinearIndependent F (yb d hk nm c side site tar h Q x):=by
  have horig:=kN M (fun _=>Fin.elim0)
  let emb:Fin (min t h+1)→{i:Fin t // Gt.used i=true}:=fun s=>⟨pick s,hpick_used s⟩
  have hemb_inj:Function.Injective emb:=fun s1 s2 hs=>hpick_inj (congrArg Subtype.val hs)
  have hcomp:LinearIndependent F (fun s=>M (emb s).val):=horig.comp emb hemb_inj
  have heq:(fun s=>M (emb s).val)=yb d hk nm c side site tar h Q x:=by
   funext s; exact (hpick_eq s).symm
  rwa [heq] at hcomp
 let DoptSub:={u:V k // ∀ i,dotProduct (Qopt i) u=0}
 let Dopt:Submodule F (V k):=zM (Submodule.span F (Set.range Qopt))
 have hDopt_mem (u:V k):u∈Dopt↔∀ i,dotProduct (Qopt i) u=0:=by
  constructor
  · intro hu i; rw [dotProduct_comm]; exact hu (Qopt i) (Submodule.subset_span ⟨i,rfl⟩)
  · intro hu v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i,rfl⟩; rw [dotProduct_comm]; exact hu i
    · exact dotProduct_zero _
    · intro x1 y1 _ _ hx hy; rw [dotProduct_add,hx,hy,add_zero]
    · intro a0 x1 _ hx; rw [dotProduct_smul,hx,smul_zero]
 have hDopt_le_Q:∀ u∈Dopt,∀ i,dotProduct (Q x i) u=0:=by
  intro u hu i; rw [dotProduct_comm]; exact hu (Q x i) (hle (Submodule.subset_span ⟨i,rfl⟩))
 let pr:=fun (key:V k) (i:Fin t)=>state hk (nm x) (c x) (side i) key (r+1) (site i)
 let polOpt (i:Fin t) (xy:DoptSub×DoptSub):F:=
  pr rep0 i+pr (rep0+xy.1.val) i+pr (rep0+xy.2.val) i+pr (rep0+xy.1.val+xy.2.val) i
 have hpol_eq_mat (i:Fin t) (u v:DoptSub):
  polOpt i (u,v)=dotProduct u.val ((Matrix.of fun a b=>M i (finProdFinEquiv (a,b))).mulVec v.val):=by
  have hop:=terminal_oneProduct hk (nm x) (c x) (qb (Q x)) rep0 w hc hchk0 (side i) (site i) (hw i)
  obtain ⟨a0,b0,c0,v0,w1,w2,hq⟩:=hop.coeffs
  have huQ:shift (qb (Q x)) u.val=u.val:=
   qV (Q x) (hDopt_le_Q u.val ((hDopt_mem u.val).mpr u.property))
  have hvQ:shift (qb (Q x)) v.val=v.val:=
   qV (Q x) (hDopt_le_Q v.val ((hDopt_mem v.val).mpr v.property))
  have hMat (a b:Fin k):M i (finProdFinEquiv (a,b))=w1 a * w2 b+w1 b * w2 a:=by
   have hs:=sampled_B (qb (Q x)) rep0 (fun key=>pr key i) (tar x i) hq 0 a b
   simp only [shift_zero,add_zero] at hs
   rw [hM_uv]; exact hs
  have hpol:polOpt i (u,v)=lin w1 u.val * lin w2 v.val+lin w1 v.val * lin w2 u.val:=by
   have h0:pr rep0 i=a0+lin v0 0+(b0+lin w1 0) * (c0+lin w2 0):=by
    simpa [pr,shift_zero,add_zero] using hq 0
   have h1:pr (rep0+u.val) i=a0+lin v0 u.val+(b0+lin w1 u.val) * (c0+lin w2 u.val):=by
    simpa [pr,huQ] using hq u.val
   have h2:pr (rep0+v.val) i=a0+lin v0 v.val+(b0+lin w1 v.val) * (c0+lin w2 v.val):=by
    simpa [pr,hvQ] using hq v.val
   have h3:pr (rep0+u.val+v.val) i=
    a0+lin v0 (u.val+v.val)+(b0+lin w1 (u.val+v.val)) * (c0+lin w2 (u.val+v.val)):=by
    have hadd:rep0+shift (qb (Q x)) (u.val+v.val)=rep0+u.val+v.val:=by
     rw [shift_add,huQ,hvQ,add_assoc]
    simpa [pr,hadd] using hq (u.val+v.val)
   dsimp only [polOpt]; rw [h0,h1,h2,h3]
   have hl0 (z:V k):lin z 0=0:=by simp [lin]
   simp only [hl0,lin_add]
   exact y8 a0 b0 c0 (lin v0 u.val) (lin v0 v.val) (lin w1 u.val) (lin w1 v.val) (lin w2 u.val) (lin w2 v.val)
  rw [hpol]
  have hMeq:(Matrix.of fun a b=>M i (finProdFinEquiv (a,b)))=
   Matrix.of (fun a b=>w1 a * w2 b+w1 b * w2 a):=Matrix.ext hMat
  rw [hMeq]
  exact k1 w1 w2 u.val v.val
 let res:(Fin (min t h+1)→F) →ₗ[F] (DoptSub×DoptSub→F):=
  { toFun:=fun lam xy=>∑ s:Fin (min t h+1),lam s * polOpt (pick s) xy
    map_add':=fun l1 l2=>by funext xy; simp [add_mul,Finset.sum_add_distrib]
    map_smul':=fun c0 l=>by funext xy; simp [Finset.mul_sum,mul_assoc] }
 have hres_rg:LinearMap.range res≤Submodule.span F (Set.range polOpt):=by
  rintro _ ⟨lam,rfl⟩
  have heq:res lam=∑ s:Fin (min t h+1),lam s • polOpt (pick s):=by
   funext xy; simp [res,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [heq]
  exact Submodule.sum_mem _ (fun s _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨pick s,rfl⟩))
 have hres_ker_ne:LinearMap.ker res≠⊥:=by
  intro hbot
  have hrn:=LinearMap.finrank_range_add_finrank_ker res
  rw [hbot,finrank_bot,add_zero,Module.finrank_fin_fun] at hrn
  have hle_rg:=Submodule.finrank_mono hres_rg
  have hopt_rk:Module.finrank F (Submodule.span F (Set.range polOpt))≤h:=hworks.2 rep0
  omega
 obtain ⟨lam,hlam_ker,hlam_ne⟩:=Submodule.exists_mem_ne_zero_of_ne_bot hres_ker_ne
 have hlam_pos:0<zi lam:=yg hlam_ne
 have hlam_lt:zi lam-1<2 ^ (min t h+1)-1:=by
  have:=y3 lam; omega
 let m_idx:Fin (2 ^ (min t h+1)-1):=⟨zi lam-1,hlam_lt⟩
 have hm_idx_val:m_idx.val+1=zi lam:=by dsimp [m_idx]; omega
 let A:Matrix (Fin k) (Fin k) F:=Matrix.of (q9 d hk nm c side site tar h Q m_idx x)
 have hA_eq:A=∑ s:Fin (min t h+1),lam s • Matrix.of (fun u v=>M (pick s) (finProdFinEquiv (u,v))):=by
  ext u v
  simp only [A,q9,Matrix.of_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
   hm_idx_val,vm]
  apply Finset.sum_congr rfl
  intro s _
  rcases qF (lam s) with h0|h1
  · simp [h0,qm]
  · simp [h1,zA,hbas_eq]
 have hA_ne:A≠0:=by
  intro hA0
  have hlin0:∑ s:Fin (min t h+1),lam s • yb d hk nm c side site tar h Q x s=0:=by
   funext a
   have huv:=congrFun (congrFun hA0 (finProdFinEquiv.symm a).1) (finProdFinEquiv.symm a).2
   simp only [hA_eq,Matrix.sum_apply,Matrix.smul_apply,Matrix.of_apply,Matrix.zero_apply,
    smul_eq_mul,Prod.mk.eta,Equiv.apply_symm_apply] at huv
   simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,hbas_eq]
   exact huv
  have hzero:=(Fintype.linearIndependent_iff.mp hB_li) lam hlin0
  exact hlam_ne (funext hzero)
 have hA_diag:∀ u,A u u=0:=by
  intro u
  rw [hA_eq]; simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
  apply Finset.sum_eq_zero; intro s _
  have hv:=(sample_valid (qb (Q x)) rep0 (fun key=>pr key (pick s)) (tar x (pick s))).1 u
  rw [hM_uv,hv,mul_zero]
 have hA_sym:∀ u v,A u v=A v u:=by
  intro u v
  rw [hA_eq]; simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
  apply Finset.sum_congr rfl; intro s _
  congr 1
  rw [hM_uv,hM_uv]
  exact (sample_valid (qb (Q x)) rep0 (fun key=>pr key (pick s)) (tar x (pick s))).2 u v
 have hA_zero:∀ u v,qh (Q x) u=false∨qh (Q x) v=false→A u v=0:=by
  intro u v hnf
  rw [hA_eq]; simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
  apply Finset.sum_eq_zero; intro s _
  have hB0:(sample (qb (Q x)) rep0 (fun key=>pr key (pick s)) (tar x (pick s))).B u v=0:=by
   rcases hnf with hu|hv
   · have hg0:qb (Q x) u=0:=zJ (Q x) hu
     simp only [sample,hg0,add_zero]
     have:pr rep0 (pick s)+pr rep0 (pick s)+pr (rep0+qb (Q x) v) (pick s) +
      pr (rep0+qb (Q x) v) (pick s)=0:=by
      rw [qj,zero_add,qj]
     exact this
   · have hg0:qb (Q x) v=0:=zJ (Q x) hv
     simp only [sample,hg0,add_zero]
     calc pr rep0 (pick s)+pr (rep0+qb (Q x) u) (pick s)+pr rep0 (pick s) +
           pr (rep0+qb (Q x) u) (pick s)
      =(pr rep0 (pick s)+pr rep0 (pick s)) +
           (pr (rep0+qb (Q x) u) (pick s)+pr (rep0+qb (Q x) u) (pick s)):=by ring
      _=0:=by rw [qj,qj,add_zero]
  rw [hM_uv,hB0,mul_zero]
 obtain ⟨a,ha_rk⟩:=u4 A hA_diag hA_sym
 have ha_pos:1≤a:=by
  by_contra h0
  have ha0:a=0:=by omega
  rw [ha0,Nat.mul_zero] at ha_rk
  apply hA_ne
  ext u v
  have hbot:LinearMap.range A.mulVecLin=⊥:=Submodule.finrank_eq_zero.mp ha_rk
  have hv0:A.mulVec (Pi.single v 1)=0:=by
   have:A.mulVecLin (Pi.single v 1)∈(⊥:Submodule F (V k)):=hbot▸⟨Pi.single v 1,rfl⟩
   exact (Submodule.mem_bot F).mp this
  have:=congrFun hv0 u
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using this
 have ha_le_H1:a≤ min t h+1:=by
  have hsum_rk:A.rank≤∑ s:Fin (min t h+1),
   (lam s • Matrix.of (fun u v=>M (pick s) (finProdFinEquiv (u,v)))).rank:=by
   rw [hA_eq]; exact jx _
  have heach (s:Fin (min t h+1)):
   (lam s • Matrix.of (fun u v=>M (pick s) (finProdFinEquiv (u,v)))).rank≤2:=by
   rcases qF (lam s) with h0|h1
   · rw [h0,zero_smul]
     have:(0:Matrix (Fin k) (Fin k) F).rank=0:=by
      change Module.finrank F (LinearMap.range (0:Matrix (Fin k) (Fin k) F).mulVecLin)=0
      have:(0:Matrix (Fin k) (Fin k) F).mulVecLin=0:=LinearMap.ext fun v=>Matrix.zero_mulVec v
      rw [this,LinearMap.range_zero,finrank_bot]
     omega
   · rw [h1,one_smul]
     have hop:=terminal_oneProduct hk (nm x) (c x) (qb (Q x)) rep0 w hc hchk0 (side (pick s)) (site (pick s)) (hw (pick s))
     obtain ⟨a0,b0,c0,v0,w1,w2,hq⟩:=hop.coeffs
     have hMeq:Matrix.of (fun u v=>M (pick s) (finProdFinEquiv (u,v)))=
      Matrix.of (fun u v=>w1 u * w2 v+w1 v * w2 u):=by
      ext u v
      have hs:=sampled_B (qb (Q x)) rep0 (fun key=>pr key (pick s)) (tar x (pick s)) hq 0 u v
      simp only [shift_zero,add_zero] at hs
      simp only [Matrix.of_apply]; rw [hM_uv]; exact hs
     rw [hMeq]; exact kV w1 w2
  have htot:∑ s:Fin (min t h+1),
   (lam s • Matrix.of (fun u v=>M (pick s) (finProdFinEquiv (u,v)))).rank≤
   ∑ _s:Fin (min t h+1),2:=Finset.sum_le_sum (fun s _=>heach s)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at htot
  omega
 have hiso:∀ u∈Dopt,∀ v∈Dopt,dotProduct u (A.mulVec v)=0:=by
  intro u hu v hv
  let uS:DoptSub:=⟨u,(hDopt_mem u).mp hu⟩
  let vS:DoptSub:=⟨v,(hDopt_mem v).mp hv⟩
  have h0:=congrFun hlam_ker (uS,vS)
  change ∑ s:Fin (min t h+1),lam s * polOpt (pick s) (uS,vS)=0 at h0
  rw [hA_eq,Matrix.sum_mulVec,dotProduct_sum]
  rw [← h0]
  apply Finset.sum_congr rfl
  intro s _
  have hsm:(lam s • Matrix.of fun a b=>M (pick s) (finProdFinEquiv (a,b))).mulVec v=
   lam s • (Matrix.of fun a b=>M (pick s) (finProdFinEquiv (a,b))).mulVec v:=by
   funext i; simp [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  rw [hsm,dotProduct_smul,smul_eq_mul,← hpol_eq_mat (pick s) uS vS]
 have hdisj:∀ u∈Dopt,(∀ j,qh (Q x) j=true→u j=0)→u=0:=by
  intro u hu hzf
  have hsh:=qV (Q x) (hDopt_le_Q u hu)
  rw [← hsh]
  dsimp only [shift]
  apply Finset.sum_eq_zero; intro c _
  cases hc:qh (Q x) c
  · rw [zJ (Q x) hc,smul_zero]
  · rw [hzf c hc,zero_smul]
 let Gc:=qA (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0)
 have hGc_rk:(Finset.univ.filter (fun r:Fin k=>Gc.used r=true)).card=2 * a:=by
  calc (Finset.univ.filter (fun r:Fin k=>Gc.used r=true)).card
   =Module.finrank F (Submodule.span F (Set.range (q9 d hk nm c side site tar h Q m_idx x))):=
        zw _ _
   _=A.rank:=(zl A).symm
   _=2 * a:=ha_rk
 have ha1_le_rk:a+1≤(Finset.univ.filter (fun r:Fin k=>Gc.used r=true)).card:=by omega
 obtain ⟨rpick,hrpick_inj,hrpick_used,hrpick_eq⟩:=k0 Gc.used Gc.M ha1_le_rk
 let basA:Fin (a+1)→V k:=vl Gc.used Gc.M
 have hbasA_li:LinearIndependent F basA:=by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have hpiv:=(qv (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0)).2.1
   (rpick s) (hrpick_used s)
  obtain ⟨c0,hc1,hcoth⟩:=hpiv
  have hsum:=congrFun hg c0
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,basA,hrpick_eq] at hsum
  rw [Finset.sum_eq_single s] at hsum
  · rw [hc1,mul_one] at hsum; exact hsum
  · intro s' _ hs'
    rw [hcoth (rpick s') (fun h=>hs' (hrpick_inj h)),mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
 let S:Submodule F (V k):=Submodule.span F (Set.range basA)
 have hS_dim:Module.finrank F S=a+1:=by
  rw [finrank_span_eq_card hbasA_li,Fintype.card_fin]
 have hS_le:S≤LinearMap.range A.mulVecLin:=by
  have hT:A.transpose=A:=Matrix.ext fun u v=>hA_sym v u
  have hrg:LinearMap.range A.mulVecLin=
   Submodule.span F (Set.range (q9 d hk nm c side site tar h Q m_idx x)):=by
   rw [← hT]
   apply le_antisymm
   · rintro _ ⟨v,rfl⟩
     have hv:A.transpose.mulVecLin v=∑ r:Fin k,v r • A r:=by
      funext c0
      simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
       Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact Finset.sum_congr rfl (fun r _=>mul_comm _ _)
     rw [hv]
     exact Submodule.sum_mem _ (fun r _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨r,rfl⟩))
   · rw [Submodule.span_le]
     rintro _ ⟨r,rfl⟩
     refine ⟨Pi.single r 1,?_⟩
     funext c0
     simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
     rw [Finset.sum_eq_single r]
     · simp [A]
     · intro j _ hj; simp [Pi.single_eq_of_ne hj]
     · intro h; exact absurd (Finset.mem_univ _) h
  rw [hrg,← (qv (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0)).1]
  rw [Submodule.span_le]
  rintro _ ⟨s,rfl⟩
  rw [show basA s=Gc.M (rpick s) from hrpick_eq s]
  exact Submodule.subset_span ⟨rpick s,rfl⟩
 obtain ⟨ha_bound,q,hqS,hqne,hqopt,hqfree⟩:=
  kJ A hA_sym (qh (Q x)) hA_zero ha_rk Dopt hdisj hiso S hS_le hS_dim
 have ha_le_P:a≤P:=by
  have h1:=z6 (Submodule.span F (Set.range Qopt))
  have h2:Module.finrank F (Submodule.span F (Set.range Qopt))≤P:=
   (finrank_span_le_card _).trans (by
     calc (Set.range Qopt).toFinset.card=(Finset.univ.image Qopt).card:=by congr 1; ext z; simp
      _≤P:=(Finset.card_image_le).trans_eq (Fintype.card_fin P))
  have h3:(Finset.univ.filter (fun j:Fin k=>qh (Q x) j=true)).card≤k:=by
   simpa using (Finset.univ.filter (fun j:Fin k=>qh (Q x) j=true)).card_le_univ
  change a+Module.finrank F (zM (Submodule.span F (Set.range Qopt)))≤_ at ha_bound
  omega
 have ha_le_Amax:a≤ min P (min t h+1):=le_min ha_le_P ha_le_H1
 rw [Submodule.mem_span_range_iff_exists_fun F] at hqS
 obtain ⟨mu,hmu_eq⟩:=hqS
 let muPad:Fin (min P (min t h+1)+1)→F:=fun s=>
  if hs:s.val<a+1 then mu ⟨s.val,hs⟩ else 0
 have hmuPad_ne:muPad≠0:=by
  intro h0
  apply hqne
  rw [← hmu_eq]
  apply Finset.sum_eq_zero; intro s _
  have:=congrFun h0 ⟨s.val,by omega⟩
  simp only [muPad,s.isLt,↓reduceDIte,Pi.zero_apply] at this
  rw [this,zero_smul]
 have hmu_pos:0<zi muPad:=yg hmuPad_ne
 have hmu_lt:zi muPad-1<2 ^ (min P (min t h+1)+1)-1:=by
  have:=y3 muPad; omega
 let c_idx:Fin (2 ^ (min P (min t h+1)+1)-1):=⟨zi muPad-1,hmu_lt⟩
 have hc_idx_val:c_idx.val+1=zi muPad:=by dsimp [c_idx]; omega
 have hcut_eq:vb d hk nm c side site tar h Q m_idx c_idx x=q:=by
  funext j
  rw [← hmu_eq]
  simp only [vb,hc_idx_val,vm,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hsplit:∑ s:Fin (min P (min t h+1)+1),
   (if z2b (muPad s) then yK d hk nm c side site tar h Q m_idx x s j else 0)=
   ∑ s:Fin (a+1),mu s * basA s j:=by
   let emb:Fin (a+1)→Fin (min P (min t h+1)+1):=fun s=>⟨s.val,by omega⟩
   have hemb_inj:Function.Injective emb:=fun s1 s2 he=>
    Fin.ext (congrArg (fun z:Fin (min P (min t h+1)+1)=>z.val) he)
   have hsub:Finset.univ.image emb⊆(Finset.univ:Finset (Fin (min P (min t h+1)+1))):=
    Finset.subset_univ _
   rw [← Finset.sum_subset hsub]
   · rw [Finset.sum_image (fun s1 _ s2 _ h=>hemb_inj h)]
     apply Finset.sum_congr rfl; intro s _
     have hmu_s:muPad (emb s)=mu s:=by
      dsimp only [muPad,emb]; simp only [s.isLt,↓reduceDIte]
     have hbas_s:yK d hk nm c side site tar h Q m_idx x (emb s) j=basA s j:=rfl
     rw [hmu_s,hbas_s]
     rcases qF (mu s) with h0|h1
     · simp [h0,qm]
     · simp [h1,zA]
   · intro s _ hs
     have hge:¬ s.val<a+1:=by
      intro hlt; exact hs (Finset.mem_image.mpr ⟨⟨s.val,hlt⟩,Finset.mem_univ _,Fin.ext rfl⟩)
     dsimp only [muPad]; simp only [hge,↓reduceDIte,qm,Bool.false_eq_true,↓reduceIte]
  exact hsplit
 let M1:=2 ^ (min t h+1)-1
 let M2:=2 ^ (min P (min t h+1)+1)-1
 have hM2_pos:0<M2:=by
  have:2≤2 ^ (min P (min t h+1)+1):=by
   rw [Nat.pow_succ]; have:=Nat.one_le_two_pow (n:=min P (min t h+1)); omega
  omega
 have hb_lt_prod:m_idx.val * M2+c_idx.val<M1 * M2:=by
  calc m_idx.val * M2+c_idx.val< m_idx.val * M2+M2:=Nat.add_lt_add_left c_idx.isLt _
   _=(m_idx.val+1) * M2:=by rw [Nat.succ_mul]
   _≤M1 * M2:=Nat.mul_le_mul_right M2 m_idx.isLt
 have hb_lt:m_idx.val * M2+c_idx.val<qC t P h:=by
  unfold qC; simp only [ht,↓reduceIte]
  exact lt_of_lt_of_le hb_lt_prod (le_max_right 3 _)
 let b:Fin (qC t P h):=⟨m_idx.val * M2+c_idx.val,hb_lt⟩
 have htc:zY d hk nm c side site tar h Q b x=q:=by
  unfold zY
  dsimp only [b]
  split_ifs with hlt
  · have hdiv:(m_idx.val * M2+c_idx.val) / M2=m_idx.val:=by
     rw [Nat.mul_comm,Nat.mul_add_div hM2_pos,Nat.div_eq_of_lt c_idx.isLt,Nat.add_zero]
    have hmod:(m_idx.val * M2+c_idx.val) % M2=c_idx.val:=by
     rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt c_idx.isLt]
    have hm_lt:(m_idx.val * M2+c_idx.val) / M2<M1:=
     Nat.div_lt_of_lt_mul (calc m_idx.val * M2+c_idx.val<M1 * M2:=hb_lt_prod
      _=M2 * M1:=Nat.mul_comm M1 M2)
    have hc_lt:(m_idx.val * M2+c_idx.val) % M2<M2:=Nat.mod_lt _ hM2_pos
    have hm_eq:(⟨(m_idx.val * M2+c_idx.val) / M2,hm_lt⟩:Fin M1)=m_idx:=Fin.ext hdiv
    have hc_eq:(⟨(m_idx.val * M2+c_idx.val) % M2,hc_lt⟩:Fin M2)=c_idx:=Fin.ext hmod
    change vb d hk nm c side site tar h Q ⟨(m_idx.val * M2+c_idx.val) / M2,hm_lt⟩
     ⟨(m_idx.val * M2+c_idx.val) % M2,hc_lt⟩ x=q
    rw [hm_eq,hc_eq]
    exact hcut_eq
  · exact absurd hb_lt_prod hlt
 refine ⟨b,?_,?_⟩
 · rw [htc]
   apply yw Qopt q
   intro u hu; exact hqopt u ((hDopt_mem u).mpr hu)
 · rw [htc]
   exact zt (Q x) hqfree hqne
lemma uz {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (hc:closed hk w (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,w (side i) (r+1) (site i)=true) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (x:In N)
 (hrk:Module.finrank F (Submodule.span F (Set.range (Q x)))≤d)
 (hfail:z8 d hk nm c w side site tar h Q x=false)
 (Qopt:Fin P→V k) (hworks:ze hk w side site h (nm x) (c x) Qopt)
 (hle:Submodule.span F (Set.range (Q x))≤Submodule.span F (Set.range Qopt)):
 ∃ b:Fin (qC t P h),
   q5 d hk nm c w side site tar h Q b x∈Submodule.span F (Set.range Qopt)∧
   q5 d hk nm c w side site tar h Q b x∉Submodule.span F (Set.range (Q x)):=by
 have hbr3:3≤qC t P h:=y9 t P h
 by_cases ht:t≤h
 · have htermT:zq d hk nm c side site tar h Q x=true:=by
    rw [ku]; intro idx _
    exact (Matrix.rank_le_card_height _).trans (by simpa using ht)
   have hprefF:q4 d hk nm c w Q x=false:=by
    cases hp:q4 d hk nm c w Q x
    · rfl
    · simp [z8,hp,htermT] at hfail
   obtain ⟨ch,h1,h2⟩:=km d hk nm c w hc side site h Q x hprefF Qopt hworks hle
   refine ⟨⟨ch.val,lt_of_lt_of_le ch.isLt hbr3⟩,?_,?_⟩
   · have heq:q5 d hk nm c w side site tar h Q ⟨ch.val,lt_of_lt_of_le ch.isLt hbr3⟩ x=
      qX d hk nm c w Q ch x:=by
      funext j; simp [q5,ht,Nat.mod_eq_of_lt ch.isLt]
     rwa [heq]
   · have heq:q5 d hk nm c w side site tar h Q ⟨ch.val,lt_of_lt_of_le ch.isLt hbr3⟩ x=
      qX d hk nm c w Q ch x:=by
      funext j; simp [q5,ht,Nat.mod_eq_of_lt ch.isLt]
     rwa [heq]
 · cases hp:q4 d hk nm c w Q x
   · obtain ⟨ch,h1,h2⟩:=km d hk nm c w hc side site h Q x hp Qopt hworks hle
     refine ⟨⟨ch.val,lt_of_lt_of_le ch.isLt hbr3⟩,?_,?_⟩
     · have heq:q5 d hk nm c w side site tar h Q ⟨ch.val,lt_of_lt_of_le ch.isLt hbr3⟩ x=
        qX d hk nm c w Q ch x:=by
        funext j; simp [q5,ht,hp,Nat.mod_eq_of_lt ch.isLt]
       rwa [heq]
     · have heq:q5 d hk nm c w side site tar h Q ⟨ch.val,lt_of_lt_of_le ch.isLt hbr3⟩ x=
        qX d hk nm c w Q ch x:=by
        funext j; simp [q5,ht,hp,Nat.mod_eq_of_lt ch.isLt]
       rwa [heq]
   · have htermF:zq d hk nm c side site tar h Q x=false:=by
      cases hta:zq d hk nm c side site tar h Q x
      · rfl
      · simp [z8,hp,hta] at hfail
     obtain ⟨b,h1,h2⟩:=uB d hk nm c w hc side site hw tar h ht Q x hrk hp htermF Qopt hworks hle
     refine ⟨b,?_,?_⟩
     · have heq:q5 d hk nm c w side site tar h Q b x=zY d hk nm c side site tar h Q b x:=by
        funext j; simp [q5,ht,hp]
       rwa [heq]
     · have heq:q5 d hk nm c w side site tar h Q b x=zY d hk nm c side site tar h Q b x:=by
        funext j; simp [q5,ht,hp]
       rwa [heq]
theorem uq {N L:ℕ} {A:Set (Sig N)} (hF:(fun _=>false)∈A)
 (mask:ℕ) (f:Fin L→In N→F)
 (hf:∀ s:Fin L,(fun x=>z2b (f s x))∈A):
 qa A {fun x=>z2b (∑ s:Fin L,if mask.testBit s.val then f s x else 0)} (4 * L):=by
 let xs:List (Sig N):=((List.finRange L).filter (fun s=>mask.testBit s.val)).map (fun s x=>z2b (f s x))
 have hxs:∀ g∈xs,g∈A:=by
  intro g hg; obtain ⟨s,_,rfl⟩:=List.mem_map.mp hg; exact hf s
 have hx:=kY xs hxs hF
 have hlen:xs.length≤L:=by
  simp only [xs,List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange
 have heq:(fun x=>zv (xs.map fun g=>g x))=
  (fun x=>z2b (∑ s:Fin L,if mask.testBit s.val then f s x else 0)):=by
  funext x
  rw [y4]
  have hfold:∀ (l:List (Fin L)),
   zv ((l.filter (fun s=>mask.testBit s.val)).map (fun s=>z2b (f s x)))=
   zv (l.map (fun s=>z2b (if mask.testBit s.val then f s x else 0))):=by
   intro l
   induction l with
   | nil=>rfl
   | cons a l ih=>
     cases hm:mask.testBit a.val
     · simp only [List.filter_cons,hm,Bool.false_eq_true,↓reduceIte,List.map_cons,zv,
        List.foldr_cons,qm,Bool.false_xor]
       exact ih
     · simp only [List.filter_cons,hm,↓reduceIte,List.map_cons,zv,List.foldr_cons]
       exact congrArg (xor (z2b (f a x))) ih
  simpa [xs,List.map_map,Function.comp_def,zv] using hfold (List.finRange L)
 rw [heq] at hx
 exact qd hx le_rfl Set.subset_union_right (by omega)
private lemma uJ (k r t H Amax s D br M1 M2:ℕ)
 (hk:k≤ s) (ht:t≤ s) (hH:H+1≤ s) (hAm:Amax+1≤ s)
 (hs1:1≤ s) (hD1:1≤D) (hfc0:zI k k r t≤1024 * (2 * s) ^ 5)
 (hM1:M1≤br) (hM1M2:M1 * M2≤br):
 (D * 2+3 * D+k * (2 * D) +
   (zI k k r t +
     ((k * k) * (t * (t+4)+(k * k) * (2 * t)+t * (1+(k * k) * 10)) +
       (t * (t * ((t+1) * 4))+(H+1) * ((k * k) * (t * 3)))))) +
   M1 * (k * (k * (4 * (H+1))) +
    k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
    (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3))) +
    M2 * (k * (4 * (Amax+1))))≤
   2 ^ 18 * s ^ 10 * (D+br):=by
 have hp5:s ^ 5≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hp4:s ^ 4≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hp3:s ^ 3≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hp2:s ^ 2≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
 have hp1:s≤ s ^ 10:=by simpa using Nat.pow_le_pow_right hs1 (by decide:1≤10)
 have hS1:D * 2+3 * D+k * (2 * D)≤2 ^ 16 * (s ^ 10 * D):=by
  have h2:1≤ s ^ 10:=Nat.one_le_pow 10 s hs1
  have:D * 2+3 * D+k * (2 * D)=(2 * k+5) * D:=by ring
  rw [this,← Nat.mul_assoc]; apply Nat.mul_le_mul_right; omega
 have hS2:zI k k r t +
  ((k * k) * (t * (t+4)+(k * k) * (2 * t)+t * (1+(k * k) * 10)) +
    (t * (t * ((t+1) * 4))+(H+1) * ((k * k) * (t * 3))))≤2 ^ 16 * s ^ 10:=by
  have hfc2:1024 * (2 * s) ^ 5=32768 * s ^ 5:=by ring
  have hrest:(k * k) * (t * (t+4)+(k * k) * (2 * t)+t * (1+(k * k) * 10)) +
   (t * (t * ((t+1) * 4))+(H+1) * ((k * k) * (t * 3)))≤
   (s * s) * (s * (s+4)+(s * s) * (2 * s)+s * (1+(s * s) * 10)) +
   (s * (s * ((s+1) * 4))+s * ((s * s) * (s * 3))):=by gcongr
  have hexp:(s * s) * (s * (s+4)+(s * s) * (2 * s)+s * (1+(s * s) * 10)) +
   (s * (s * ((s+1) * 4))+s * ((s * s) * (s * 3)))=
   12 * s ^ 5+4 * s ^ 4+9 * s ^ 3+4 * s ^ 2:=by ring
  rw [hexp] at hrest; omega
 have hS3:M1 * (k * (k * (4 * (H+1))) +
  k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
  (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3))) +
  M2 * (k * (4 * (Amax+1))))≤2 ^ 17 * (s ^ 10 * br):=by
  have h1:k * (k * (4 * (H+1))) +
   k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
   (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3)))≤
   s * (s * (4 * s))+s * (s * (s+4)+s * (2 * s)+s * (1+s * 10)) +
   (s * (s * ((s+1) * 4))+s * (s * (s * 3))):=by gcongr
  have hexp:s * (s * (4 * s))+s * (s * (s+4)+s * (2 * s)+s * (1+s * 10)) +
   (s * (s * ((s+1) * 4))+s * (s * (s * 3)))=24 * s ^ 3+9 * s ^ 2:=by ring
  rw [hexp] at h1
  have h1':k * (k * (4 * (H+1))) +
   k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
   (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3)))≤2 ^ 16 * s ^ 10:=by omega
  have h2:k * (4 * (Amax+1))≤4 * s ^ 2:=by
   have:k * (4 * (Amax+1))≤ s * (4 * s):=by gcongr
   calc k * (4 * (Amax+1))≤ s * (4 * s):=this
    _=4 * s ^ 2:=by ring
  have h2':k * (4 * (Amax+1))≤2 ^ 16 * s ^ 10:=by omega
  have hdist:M1 * (k * (k * (4 * (H+1))) +
   k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
   (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3))) +
   M2 * (k * (4 * (Amax+1))))=
   M1 * (k * (k * (4 * (H+1))) +
   k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
   (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3)))) +
   (M1 * M2) * (k * (4 * (Amax+1))):=by ring
  rw [hdist]
  have ha:=Nat.mul_le_mul hM1 h1'
  have hb:=Nat.mul_le_mul hM1M2 h2'
  have heq:2 ^ 17 * (s ^ 10 * br)=br * (2 ^ 16 * s ^ 10)+br * (2 ^ 16 * s ^ 10):=by ring
  rw [heq]; omega
 have hS2_mul:2 ^ 16 * s ^ 10≤2 ^ 16 * (s ^ 10 * D):=by
  rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hD1
 have hfin:2 ^ 18 * s ^ 10 * (D+br)=2 ^ 18 * (s ^ 10 * D)+2 ^ 18 * (s ^ 10 * br):=by ring
 rw [hfin]; omega
theorem jS {N k r t P:ℕ} (d:ℕ) (hPk:P≤k) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
 (ht:¬ t≤h) (Q:In N→Fin P→V k) (A:Set (Sig N))
 (hF:(fun _=>false)∈A) (hT:(fun _=>true)∈A)
 (hnm:∀ b j,(bit fun x=>nm x b j)∈A) (hc:∀ b n j,(bit fun x=>c x b n j)∈A)
 (htar:∀ u,(bit fun x=>tar x u)∈A)
 (hChk:ym d hk nm c w side site tar h Q⊆A):
 qa A {f|∃ (b:Fin (qC t P h)) (j:Fin k),(fun x=>z2b (zY d hk nm c side site tar h Q b x j))=f}
  (2 ^ 18 * (k+r+t+6) ^ 10 * (2 ^ d+qC t P h)):=by
 classical
 let s:=k+r+t+6
 let H:=min t h
 let Amax:=min P (H+1)
 let M1:=2 ^ (H+1)-1
 let M2:=2 ^ (Amax+1)-1
 have hM1M2:M1 * M2≤qC t P h:=by
  unfold qC; rw [ite_eq_right ht]; exact le_max_right 3 _
 have hM1_le:M1≤qC t P h:=by
  have hM2_pos:1≤M2:=by
   have:2≤2 ^ (Amax+1):=by rw [Nat.pow_succ]; have:=Nat.one_le_two_pow (n:=Amax); omega
   omega
  exact (Nat.le_mul_of_pos_right M1 hM2_pos).trans hM1M2
 have hgenA (i j:Fin k):(bit fun x=>qb (Q x) i j)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i,j,rfl⟩)))))))
 have hliveA (idx:Fin (2 ^ d)):(fun x=>zc d (Q x) idx)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx,rfl⟩))))))
 have hrepA (idx:Fin (2 ^ d)) (j:Fin k):(bit fun x=>qO d (Q x) idx j)∈A:=
  hChk (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨idx,j,rfl⟩)))))
 have htermA (idx:Fin (2 ^ d)):zr d hk nm c side site tar h Q idx∈A:=
  hChk (Or.inl (Or.inr ⟨idx,rfl⟩))
 have hCF:qa A (Set.range (zO d hk nm c side site tar h Q)) (2 ^ d * 2):=
  qf _ 2 (fun idx=>qe (zn (htermA idx)) (qD (Or.inl (hliveA idx)) (Or.inr rfl)))
 have hFT:qa (A ∪ Set.range (zO d hk nm c side site tar h Q))
  (Set.range (ye d hk nm c side site tar h Q)) (3 * 2 ^ d):=
  yk _ (Or.inl hF) (fun idx=>Or.inr ⟨idx,rfl⟩)
 have hS1a:=qe hCF hFT
 have hRT:qa (A ∪ Set.range (ye d hk nm c side site tar h Q))
  (Set.range (fun j x=>z2b (zW d hk nm c side site tar h Q x j))) (k * (2 * 2 ^ d)):=
  kT (Or.inl hF) (ye d hk nm c side site tar h Q)
   (fun idx x=>qO d (Q x) idx) (fun idx=>Or.inr ⟨idx,rfl⟩)
   (fun idx j=>Or.inl (hrepA idx j))
 have hS1:=qe hS1a hRT
 let A1:=A ∪ Set.range (fun j x=>z2b (zW d hk nm c side site tar h Q x j))
 have hFr:=jJ hk nm c (zW d hk nm c side site tar h Q) (fun x=>qb (Q x)) w side site tar A1
  (fun b j=>Or.inl (hnm b j)) (fun b n j=>Or.inl (hc b n j))
  (fun j=>Or.inr ⟨j,rfl⟩) (fun i j=>Or.inl (hgenA i j)) (fun u=>Or.inl (htar u))
 let A2:=A1 ∪ ({vE hk nm c (zW d hk nm c side site tar h Q) (fun x=>qb (Q x)) w} ∪
  ⋃ u,qn (kx hk nm c (zW d hk nm c side site tar h Q) (fun x=>qb (Q x)) side site tar u))
 have hM_mem (i:Fin t) (a:Fin (k * k)):
  (fun x=>z2b (zR d hk nm c side site tar h Q x i a))∈A2:=
  Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl (Or.inl ⟨(finProdFinEquiv.symm a).1,(finProdFinEquiv.symm a).2,rfl⟩)⟩))
 have hGt:=vN A2 (Or.inl (Or.inl hF))
  (zR d hk nm c side site tar h Q) (fun _ _=>Fin.elim0) hM_mem (fun _ p=>p.elim0)
 simp only [Nat.add_zero] at hGt
 let A3:=A2 ∪ qY (fun x=>qA (zR d hk nm c side site tar h Q x) (fun _=>Fin.elim0))
 have hBas:=u3 (L:=H+1) A3 (Or.inl (Or.inl (Or.inl hF))) (Or.inl (Or.inl (Or.inl hT)))
  (fun x=>(qA (zR d hk nm c side site tar h Q x) (fun _=>Fin.elim0)).used)
  (zR d hk nm c side site tar h Q)
  (fun i=>Or.inr (Or.inl (Or.inl ⟨i,rfl⟩))) (fun i a=>Or.inl (hM_mem i a))
 have hS2:=qe hFr (qe hGt hBas)
 let A4:=A ∪ {f|∃ (u:Fin (H+1)) (a:Fin (k * k)),
  (fun x=>z2b (yb d hk nm c side site tar h Q x u a))=f}
 have hPerM (m_idx:Fin M1):
  qa A4 {f|∃ (c_idx:Fin M2) (j:Fin k),
   (fun x=>z2b (vb d hk nm c side site tar h Q m_idx c_idx x j))=f}
   (k * (k * (4 * (H+1))) +
     k * (k * (k+4)+k * (2 * k)+k * (1+k * 10)) +
     (k * (k * ((k+1) * 4))+(Amax+1) * (k * (k * 3))) +
     M2 * (k * (4 * (Amax+1)))):=by
  have hMat:qa A4 {f|∃ (u v:Fin k),(fun x=>z2b (q9 d hk nm c side site tar h Q m_idx x u v))=f}
   (k * (k * (4 * (H+1)))):=
   qT _ (4 * (H+1)) (fun u v=>uq (Or.inl hF) (m_idx.val+1)
    (fun s' x=>yb d hk nm c side site tar h Q x s' (finProdFinEquiv (u,v)))
    (fun s'=>Or.inr ⟨s',finProdFinEquiv (u,v),rfl⟩))
  let B1:=A4 ∪ {f|∃ (u v:Fin k),(fun x=>z2b (q9 d hk nm c side site tar h Q m_idx x u v))=f}
  have hGc:=vN B1 (Or.inl (Or.inl hF))
   (q9 d hk nm c side site tar h Q m_idx) (fun _ _=>Fin.elim0)
   (fun u v=>Or.inr ⟨u,v,rfl⟩) (fun _ p=>p.elim0)
  let B2:=B1 ∪ qY (fun x=>qA (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0))
  have hRB:=u3 (L:=Amax+1) B2 (Or.inl (Or.inl (Or.inl hF))) (Or.inl (Or.inl (Or.inl hT)))
   (fun x=>(qA (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0)).used)
   (fun x=>(qA (q9 d hk nm c side site tar h Q m_idx x) (fun _=>Fin.elim0)).M)
   (fun r'=>Or.inr (Or.inl (Or.inl ⟨r',rfl⟩)))
   (fun r' j=>Or.inr (Or.inl (Or.inr ⟨r',j,rfl⟩)))
  let B3:=B2 ∪ {f|∃ (s':Fin (Amax+1)) (j:Fin k),
   (fun x=>z2b (yK d hk nm c side site tar h Q m_idx x s' j))=f}
  have hPairs:qa B3 {f|∃ (c_idx:Fin M2) (j:Fin k),
   (fun x=>z2b (vb d hk nm c side site tar h Q m_idx c_idx x j))=f}
   (M2 * (k * (4 * (Amax+1)))):=
   qT _ (4 * (Amax+1)) (fun c_idx j=>uq (Or.inl (Or.inl (Or.inl (Or.inl hF))))
    (c_idx.val+1) (fun s' x=>yK d hk nm c side site tar h Q m_idx x s' j)
    (fun s'=>Or.inr ⟨s',j,rfl⟩))
  have hseq:=qe hMat (qe hGc (qe hRB hPairs))
  exact qd hseq le_rfl Set.subset_union_right (by dsimp only [Nat.add_zero]; omega)
 have hAllM:=v7 (fun m_idx:Fin M1=>{f|∃ (c_idx:Fin M2) (j:Fin k),
  (fun x=>z2b (vb d hk nm c side site tar h Q m_idx c_idx x j))=f}) _ hPerM
 have hTot:=qe (qe hS1 hS2) hAllM
 refine qd hTot le_rfl ?_ ?_
 · rintro _ ⟨b,j,rfl⟩
   by_cases hb:b.val<M1 * M2
   · have hM2:0<M2:=by
      have:2≤2 ^ (Amax+1):=by rw [Nat.pow_succ]; have:=Nat.one_le_two_pow (n:=Amax); omega
      omega
     have hm1:b.val / M2<M1:=Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)
     have heq:(fun x=>z2b (zY d hk nm c side site tar h Q b x j))=
      (fun x=>z2b (vb d hk nm c side site tar h Q ⟨b.val / M2,hm1⟩ ⟨b.val % M2,Nat.mod_lt _ hM2⟩ x j)):=by
      funext x; simp [zY,hb,M1,M2,H,Amax]
     rw [heq]
     exact Or.inr (Set.mem_iUnion.mpr ⟨⟨b.val / M2,hm1⟩,⟨b.val % M2,Nat.mod_lt _ hM2⟩,j,rfl⟩)
   · have heq:(fun x=>z2b (zY d hk nm c side site tar h Q b x j))=(fun _=>false):=by
      funext x; simp [zY,hb,M1,M2,H,Amax,qm]
     rw [heq]; exact Or.inl hF
 · exact uJ k r t H Amax s (2 ^ d) (qC t P h) M1 M2
    (by dsimp [s]; omega) (by dsimp [s]; omega) (by dsimp [H,s]; omega) (by dsimp [Amax,H,s]; omega)
    (by dsimp [s]; omega) Nat.one_le_two_pow
    ((k5 k k r t).trans (by gcongr; dsimp [s]; omega)) hM1_le hM1M2
private lemma k9 (s D br:ℕ) (hs1:1≤ s):
 2 ^ 25 * s ^ 10 * D+2 ^ 18 * s ^ 8 * D≤2 ^ 27 * s ^ 10 * (D+br):=by
 have h1:2 ^ 18 * s ^ 8 * D≤2 ^ 18 * (s ^ 10 * D):=by
  have hsp8:s ^ 8≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
  calc 2 ^ 18 * s ^ 8 * D=2 ^ 18 * (s ^ 8 * D):=by ring
   _≤2 ^ 18 * (s ^ 10 * D):=by gcongr
 have hchk:2 ^ 25 * s ^ 10 * D=2 ^ 25 * (s ^ 10 * D):=by ring
 have h2:2 ^ 27 * s ^ 10 * (D+br)=2 ^ 27 * (s ^ 10 * D)+2 ^ 27 * (s ^ 10 * br):=by ring
 rw [hchk,h2]; omega
private lemma ua (k s D br:ℕ) (hk:k≤ s) (hs1:1≤ s):
 2 ^ 25 * s ^ 10 * D+(2 ^ 18 * s ^ 8 * D+2 ^ 18 * s ^ 10 * (D+br)+br * (k * 4))≤
   2 ^ 27 * s ^ 10 * (D+br):=by
 have h1:2 ^ 18 * s ^ 8 * D≤2 ^ 18 * (s ^ 10 * D):=by
  have hsp8:s ^ 8≤ s ^ 10:=Nat.pow_le_pow_right hs1 (by decide)
  calc 2 ^ 18 * s ^ 8 * D=2 ^ 18 * (s ^ 8 * D):=by ring
   _≤2 ^ 18 * (s ^ 10 * D):=by gcongr
 have h2:br * (k * 4)≤4 * (s ^ 10 * br):=by
  have hsp1:s≤ s ^ 10:=by simpa using Nat.pow_le_pow_right hs1 (by decide:1≤10)
  calc br * (k * 4)=4 * (k * br):=by ring
   _≤4 * (s ^ 10 * br):=by gcongr; exact hk.trans hsp1
 have hchk:2 ^ 25 * s ^ 10 * D=2 ^ 25 * (s ^ 10 * D):=by ring
 have h3:2 ^ 18 * s ^ 10 * (D+br)=2 ^ 18 * (s ^ 10 * D)+2 ^ 18 * (s ^ 10 * br):=by ring
 have h4:2 ^ 27 * s ^ 10 * (D+br)=2 ^ 27 * (s ^ 10 * D)+2 ^ 27 * (s ^ 10 * br):=by ring
 rw [hchk,h3,h4]; omega
theorem jv {N k r t P:ℕ} (d:ℕ) (hPk:P≤k) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (A:Set (Sig N))
 (hF:(fun _=>false)∈A) (hT:(fun _=>true)∈A)
 (hnm:∀ b j,(bit fun x=>nm x b j)∈A) (hc:∀ b n j,(bit fun x=>c x b n j)∈A)
 (htar:∀ u,(bit fun x=>tar x u)∈A) (hQ:∀ i j,(fun x=>z2b (Q x i j))∈A):
 qa A ({z8 d hk nm c w side site tar h Q} ∪
  {f|∃ (b:Fin (qC t P h)) (j:Fin k),(fun x=>z2b (q5 d hk nm c w side site tar h Q b x j))=f})
  (2 ^ 27 * (k+r+t+6) ^ 10 * (2 ^ d+qC t P h)):=by
 set s:=k+r+t+6
 have hChk:=uH d hPk hk nm c w side site tar h Q A hF hT hnm hc htar hQ
 let A1:=A ∪ ym d hk nm c w side site tar h Q
 have hF1:(fun _=>false)∈A1:=Or.inl hF
 have hT1:(fun _=>true)∈A1:=Or.inl hT
 have hOK1:z8 d hk nm c w side site tar h Q∈A1:=Or.inr (Or.inr (Or.inr (Or.inr rfl)))
 have hPrefAll1:q4 d hk nm c w Q∈A1:=Or.inr (Or.inr (Or.inl rfl))
 have hPref:=jO d hk nm c w side site tar h Q A1 hF1 hT1
  (fun b j=>Or.inl (hnm b j)) (fun b n j=>Or.inl (hc b n j)) Set.subset_union_right
 by_cases ht:t≤h
 · refine qd (zd hChk hPref) le_rfl ?_ ?_
   · rintro f (rfl|⟨b,j,rfl⟩)
     · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
     · have heq:(fun x=>z2b (q5 d hk nm c w side site tar h Q b x j))=
        (fun x=>z2b (qX d hk nm c w Q ⟨b.val % 3,Nat.mod_lt _ (by decide)⟩ x j)):=by
        funext x; simp [q5,ht]
       rw [heq]; exact Or.inr (Or.inr ⟨⟨b.val % 3,Nat.mod_lt _ (by decide)⟩,j,rfl⟩)
   · exact k9 s (2 ^ d) (qC t P h) (by omega)
 · have hTerm:=jS d hPk hk nm c w side site tar h ht Q A1 hF1 hT1
    (fun b j=>Or.inl (hnm b j)) (fun b n j=>Or.inl (hc b n j)) (fun u=>Or.inl (htar u))
    Set.subset_union_right
   let A2:=A1 ∪ ({f|∃ (ch:Fin 3) (u:Fin k),(fun x=>z2b (qX d hk nm c w Q ch x u))=f} ∪
    {f|∃ (b:Fin (qC t P h)) (j:Fin k),(fun x=>z2b (zY d hk nm c side site tar h Q b x j))=f})
   have hMux:qa A2 {f|∃ (b:Fin (qC t P h)) (j:Fin k),
    (fun x=>z2b (q5 d hk nm c w side site tar h Q b x j))=f}
    (qC t P h * (k * 4)):=by
    refine qT _ 4 (fun b j=>?_)
    have hite:=vo (A:=A2) (Or.inl hPrefAll1)
     (Or.inr (Or.inr ⟨b,j,rfl⟩))
     (Or.inr (Or.inl ⟨⟨b.val % 3,Nat.mod_lt _ (by decide)⟩,j,rfl⟩))
    have heq:(fun x=>if q4 d hk nm c w Q x then
     z2b (zY d hk nm c side site tar h Q b x j)
     else z2b (qX d hk nm c w Q ⟨b.val % 3,Nat.mod_lt _ (by decide)⟩ x j))=
     (fun x=>z2b (q5 d hk nm c w side site tar h Q b x j)):=by
     funext x; cases hp:q4 d hk nm c w Q x <;> simp [q5,ht,hp]
    rwa [heq] at hite
   have hAll:=zd hChk (qe (qr hPref hTerm) hMux)
   refine qd hAll le_rfl ?_ ?_
   · rintro f (rfl|hf)
     · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
     · exact Or.inr (Or.inr hf)
   · exact ua k s (2 ^ d) (qC t P h) (by omega) (by omega)
end
end PEqualNP.Outside.L_meta_27129_aux
namespace PEqualNP.Outside.L_meta_27129_aux
noncomputable section
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.Outside.L_meta_27129_aux.P25940Affine
open PEqualNP.Outside.L_meta_27129_aux.P25940Sample
open PEqualNP.Outside.L_meta_27129_aux.P25940Sem
open PEqualNP.Outside.L_meta_27129_aux.yo
abbrev qS (P k:ℕ):=Bool×(Fin (P+1)→Bool)×(Fin P→V k)
def yU {P:ℕ} (a b:Fin (P+1)→Bool):Bool:=
 (List.finRange (P+1)).any fun i=>
   a i&&(List.finRange (P+1)).any fun j=>decide (i.val<j.val)&&b j
lemma u2 {P:ℕ} {d1 d2:ℕ} (h1:d1≤P) (h2:d2≤P):
 yU (fun i:Fin (P+1)=>decide (i.val=d1))
    (fun j:Fin (P+1)=>decide (j.val=d2))=decide (d1<d2):=by
 apply Bool.eq_iff_iff.mpr
 simp only [yU,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,decide_eq_true_eq]
 constructor
 · rintro ⟨i,rfl,j,hlt,rfl⟩; exact hlt
 · intro hlt
   exact ⟨⟨d1,by omega⟩,rfl,⟨d2,by omega⟩,hlt,rfl⟩
def q3 {P k:ℕ} (r1 r2:qS P k):qS P k:=
 let take2:=r2.1&&(!(r1.1)||yU r2.2.1 r1.2.1)
 (r1.1||r2.1,
  fun i=>if take2 then r2.2.1 i else r1.2.1 i,
  fun a j=>if take2 then r2.2.2 a j else r1.2.2 a j)
def vi (P k:ℕ):qS P k:=
 (false,fun i=>decide (i.val=P),fun _ _=>0)
def vV {P k B:ℕ} (f:Fin B→qS P k):qS P k:=
 (List.finRange B).foldl (fun acc b=>q3 acc (f b)) (vi P k)
def qH {N P k:ℕ} (r:In N→qS P k):Set (Sig N):=
 {fun x=>(r x).1} ∪
 Set.range (fun i:Fin (P+1)=>fun x=>(r x).2.1 i) ∪
 {f|∃ (a:Fin P) (j:Fin k),(fun x=>z2b ((r x).2.2 a j))=f}
theorem j9 {N P:ℕ} {A:Set (Sig N)} (hF:(fun _=>false)∈A)
 (a b:Fin (P+1)→Sig N) (ha:∀ i,a i∈A) (hb:∀ j,b j∈A):
 qa A {fun x=>yU (fun i=>a i x) (fun j=>b j x)}
  ((P+1) * ((P+1)+1)+(P+1)):=by
 let row (i:Fin (P+1)):Sig N:=fun x=>
  a i x&&(List.finRange (P+1)).any fun j=>decide (i.val<j.val)&&b j x
 have hrows:qa A (Set.range row) ((P+1) * ((P+1)+1)):=by
  refine qf row ((P+1)+1) (fun i=>?_)
  let inner (j:Fin (P+1)):Sig N:=fun x=>decide (i.val<j.val)&&b j x
  have hi_mem (j:Fin (P+1)):inner j∈A:=by
   by_cases hlt:i.val<j.val
   · have heq:inner j=b j:=by funext x; simp only [inner,decide_eq_true hlt,Bool.true_and]
     rw [heq]; exact hb j
   · have heq:inner j=(fun _=>false):=by funext x; simp only [inner,decide_eq_false hlt,Bool.false_and]
     rw [heq]; exact hF
  have hany:qa A {fun x=>(List.finRange (P+1)).any fun j=>inner j x} (P+1):=
   vC inner hi_mem hF
  have hand:qa (A ∪ {fun x=>(List.finRange (P+1)).any fun j=>inner j x}) {row i} 1:=
   qD (Or.inl (ha i)) (Or.inr rfl)
  exact qe hany hand
 have hall:qa (A ∪ Set.range row) {fun x=>(List.finRange (P+1)).any fun i=>row i x} (P+1):=
  vC row (fun i=>Or.inr ⟨i,rfl⟩) (Or.inl hF)
 exact qe hrows hall
theorem u1 {N P k:ℕ} (hPk:P≤k) {A:Set (Sig N)}
 (hF:(fun _=>false)∈A)
 (r1 r2:In N→qS P k)
 (h1:qH r1⊆A) (h2:qH r2⊆A):
 qa A (qH (fun x=>q3 (r1 x) (r2 x))) (16 * (k+6) ^ 2):=by
 have h1ok:(fun x=>(r1 x).1)∈A:=h1 (Or.inl (Or.inl rfl))
 have h2ok:(fun x=>(r2 x).1)∈A:=h2 (Or.inl (Or.inl rfl))
 have h1d (i:Fin (P+1)):(fun x=>(r1 x).2.1 i)∈A:=h1 (Or.inl (Or.inr ⟨i,rfl⟩))
 have h2d (i:Fin (P+1)):(fun x=>(r2 x).2.1 i)∈A:=h2 (Or.inl (Or.inr ⟨i,rfl⟩))
 have h1q (a:Fin P) (j:Fin k):(fun x=>z2b ((r1 x).2.2 a j))∈A:=h1 (Or.inr ⟨a,j,rfl⟩)
 have h2q (a:Fin P) (j:Fin k):(fun x=>z2b ((r2 x).2.2 a j))∈A:=h2 (Or.inr ⟨a,j,rfl⟩)
 let take2:Sig N:=fun x=>(r2 x).1&&(!((r1 x).1)||yU (r2 x).2.1 (r1 x).2.1)
 have hlt:=j9 hF (fun i x=>(r2 x).2.1 i) (fun j x=>(r1 x).2.1 j) h2d h1d
 have hnot:qa (A ∪ {fun x=>yU (r2 x).2.1 (r1 x).2.1}) {fun x=>!((r1 x).1)} 1:=
  zn (Or.inl h1ok)
 have hor:qa (A ∪ ({fun x=>yU (r2 x).2.1 (r1 x).2.1} ∪ {fun x=>!((r1 x).1)}))
  {fun x=>!((r1 x).1)||yU (r2 x).2.1 (r1 x).2.1} 1:=
  orB (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
 have ht2:qa (A ∪ (({fun x=>yU (r2 x).2.1 (r1 x).2.1} ∪ {fun x=>!((r1 x).1)}) ∪
  {fun x=>!((r1 x).1)||yU (r2 x).2.1 (r1 x).2.1})) {take2} 1:=
  qD (Or.inl h2ok) (Or.inr (Or.inr rfl))
 have hTake:=qe (zd (zd hlt hnot) hor) ht2
 let A1:=A ∪ {take2}
 have hOK:qa A1 {fun x=>(q3 (r1 x) (r2 x)).1} 1:=
  orB (Or.inl h1ok) (Or.inl h2ok)
 have hDep:qa A1 (Set.range (fun i:Fin (P+1)=>fun x=>(q3 (r1 x) (r2 x)).2.1 i)) ((P+1) * 4):=
  qf _ 4 (fun i=>vo (Or.inr rfl) (Or.inl (h2d i)) (Or.inl (h1d i)))
 have hQ:qa A1 {f|∃ (a:Fin P) (j:Fin k),(fun x=>z2b ((q3 (r1 x) (r2 x)).2.2 a j))=f}
  (P * (k * 4)):=by
  refine qT _ 4 (fun a j=>?_)
  have hi:=vo (A:=A1) (Or.inr rfl) (Or.inl (h2q a j)) (Or.inl (h1q a j))
  have heq:(fun x=>if take2 x then z2b ((r2 x).2.2 a j) else z2b ((r1 x).2.2 a j))=
   (fun x=>z2b ((q3 (r1 x) (r2 x)).2.2 a j)):=by
   funext x; cases ht:take2 x <;> simp [q3,take2,ht]
  rwa [heq] at hi
 refine qd (qe hTake (qr (qr hOK hDep) hQ)) le_rfl Set.subset_union_right ?_
 have h1':(P+1) * ((P+1)+1)+(P+1)≤(k+1) * ((k+1)+1)+(k+1):=by gcongr
 have h2':(P+1) * 4≤(k+1) * 4:=by gcongr
 have h3':P * (k * 4)≤k * (k * 4):=by gcongr
 have h4':((k+1) * ((k+1)+1)+(k+1)+1+1+1)+(1+(k+1) * 4+k * (k * 4))≤
  16 * (k+6) ^ 2:=by ring_nf; omega
 omega
theorem u9 {N P k B:ℕ} (hPk:P≤k)
 (f:Fin B→In N→qS P k):
 ∀ (l:List (Fin B)) (A:Set (Sig N)) (init:In N→qS P k),
   (fun _=>false)∈A→(∀ b,qH (f b)⊆A)→qH init⊆A→
   qa A (qH (fun x=>l.foldl (fun acc b=>q3 acc (f b x)) (init x)))
    (l.length * (16 * (k+6) ^ 2)):=by
 intro l
 induction l with
 | nil=>
   intro A init _ _ hinit
   simpa using zk hinit
 | cons b l ih=>
   intro A init hF hf hinit
   let nxt:In N→qS P k:=fun x=>q3 (init x) (f b x)
   have h1:qa A (qH nxt) (16 * (k+6) ^ 2):=
    u1 hPk hF init (f b) hinit (hf b)
   have h2:qa (A ∪ qH nxt)
    (qH (fun x=>l.foldl (fun acc b'=>q3 acc (f b' x)) (nxt x)))
    (l.length * (16 * (k+6) ^ 2)):=
    ih (A ∪ qH nxt) nxt (Or.inl hF)
     (fun b'=>(hf b').trans Set.subset_union_left) Set.subset_union_right
   simpa [List.foldl_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using qe h1 h2
theorem k8 {N P k B:ℕ} (hPk:P≤k) {A:Set (Sig N)}
 (hF:(fun _=>false)∈A) (hT:(fun _=>true)∈A)
 (f:Fin B→In N→qS P k)
 (hf:∀ b,qH (f b)⊆A):
 qa A (qH (fun x=>vV (fun b=>f b x))) (B * (16 * (k+6) ^ 2)):=by
 have hEmpty:qH (fun _:In N=>vi P k)⊆A:=by
  rintro g ((rfl|⟨i,rfl⟩)|⟨a,j,rfl⟩)
  · exact hF
  · dsimp only
    by_cases hi:i.val=P
    · have heq:(fun _:In N=>(vi P k).2.1 i)=(fun _=>true):=by funext _; simp [vi,hi]
      rw [heq]; exact hT
    · have heq:(fun _:In N=>(vi P k).2.1 i)=(fun _=>false):=by funext _; simp [vi,hi]
      rw [heq]; exact hF
  · dsimp only
    have heq:(fun _:In N=>z2b ((vi P k).2.2 a j))=(fun _=>false):=by
     funext _; simp [vi,qm]
    rw [heq]; exact hF
 simpa [vV,List.length_finRange] using
  u9 hPk f (List.finRange B) A (fun _=>vi P k) hF hf hEmpty
def zF {k r t P:ℕ} (hk:0<k) (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k)
    (h:ℕ) (nm:Bool→V k) (c:Bool→Fin (r+1)→V k) (dMin:ℕ) (res:qS P k):Prop:=
 ∃ d:ℕ,dMin≤d∧d≤P∧
   res.2.1=(fun i:Fin (P+1)=>decide (i.val=d))∧
   (res.1=true→ze hk w side site h nm c res.2.2∧
     Module.finrank F (Submodule.span F (Set.range res.2.2))≤d)
def yC {P k:ℕ} (res:qS P k) (d0:ℕ):Prop:=
 res.1=true∧∃ d:ℕ,d≤d0∧d≤P∧res.2.1=fun i:Fin (P+1)=>decide (i.val=d)
lemma yf {k r t P:ℕ} (hk:0<k) (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k)
 (h dMin:ℕ) (nm:Bool→V k) (c:Bool→Fin (r+1)→V k) {r1 r2:qS P k}
 (hv1:zF hk w side site h nm c dMin r1) (hv2:zF hk w side site h nm c dMin r2):
 zF hk w side site h nm c dMin (q3 r1 r2):=by
 obtain ⟨d1,hd1a,hd1b,heq1,hok1⟩:=hv1
 obtain ⟨d2,hd2a,hd2b,heq2,hok2⟩:=hv2
 let take2:=r2.1&&(!(r1.1)||yU r2.2.1 r1.2.1)
 cases ht:take2
 · refine ⟨d1,hd1a,hd1b,?_,?_⟩
   · funext i; change (if take2 then r2.2.1 i else r1.2.1 i)=decide (i.val=d1); rw [ht]; simp [heq1]
   · intro hok
     have hr1:r1.1=true:=by
      cases h1:r1.1
      · cases h2:r2.1
        · simp [q3,h1,h2] at hok
        · simp [take2,h1,h2] at ht
      · rfl
     have hq:(q3 r1 r2).2.2=r1.2.2:=by
      funext a j; change (if take2 then r2.2.2 a j else r1.2.2 a j)=r1.2.2 a j; rw [ht]; rfl
     rw [hq]; exact hok1 hr1
 · refine ⟨d2,hd2a,hd2b,?_,?_⟩
   · funext i; change (if take2 then r2.2.1 i else r1.2.1 i)=decide (i.val=d2); rw [ht]; simp [heq2]
   · intro _
     have hr2:r2.1=true:=by
      cases h2:r2.1 <;> simp [take2,h2] at ht; rfl
     have hq:(q3 r1 r2).2.2=r2.2.2:=by
      funext a j; change (if take2 then r2.2.2 a j else r1.2.2 a j)=r2.2.2 a j; rw [ht]; rfl
     rw [hq]; exact hok2 hr2
lemma yx {P k:ℕ} {r1 r2:qS P k} {d1 d2 d0:ℕ}
 (h1:d1≤P) (h2:d2≤P)
 (heq1:r1.2.1=fun i=>decide (i.val=d1)) (heq2:r2.2.1=fun i=>decide (i.val=d2))
 (hr1:r1.1=true) (hd1:d1≤d0):
 yC (q3 r1 r2) d0:=by
 let take2:=r2.1&&(!(r1.1)||yU r2.2.1 r1.2.1)
 refine ⟨by simp [q3,hr1],?_⟩
 cases ht:take2
 · refine ⟨d1,hd1,h1,by funext i; change (if take2 then r2.2.1 i else r1.2.1 i)=_; rw [ht]; simp [heq1]⟩
 · have hlt:d2<d1:=by
    simp only [take2,hr1,Bool.not_true,Bool.false_or,heq1,heq2,u2 h2 h1,
     Bool.and_eq_true,decide_eq_true_eq] at ht
    exact ht.2
   refine ⟨d2,by omega,h2,by funext i; change (if take2 then r2.2.1 i else r1.2.1 i)=_; rw [ht]; simp [heq2]⟩
lemma yj {P k:ℕ} {r1 r2:qS P k} {d1 d2 d0:ℕ}
 (h1:d1≤P) (h2:d2≤P)
 (heq1:r1.2.1=fun i=>decide (i.val=d1)) (heq2:r2.2.1=fun i=>decide (i.val=d2))
 (hr2:r2.1=true) (hd2:d2≤d0):
 yC (q3 r1 r2) d0:=by
 let take2:=r2.1&&(!(r1.1)||yU r2.2.1 r1.2.1)
 refine ⟨by simp [q3,hr2],?_⟩
 cases ht:take2
 · have hge:d1≤d2:=by
    simp only [take2,hr2,Bool.true_and,heq1,heq2,u2 h2 h1,
     Bool.or_eq_false_iff,Bool.not_eq_false',decide_eq_false_iff_not] at ht
    omega
   refine ⟨d1,by omega,h1,by funext i; change (if take2 then r2.2.1 i else r1.2.1 i)=_; rw [ht]; simp [heq1]⟩
 · refine ⟨d2,hd2,h2,by funext i; change (if take2 then r2.2.1 i else r1.2.1 i)=_; rw [ht]; simp [heq2]⟩
def qR {N k r t P:ℕ} (d:ℕ) (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
    (Q:In N→Fin P→V k) (b:Fin (qC t P h)) (x:In N) (i:Fin P):V k:=
 if i.val=d then q5 d hk nm c w side site tar h Q b x else Q x i
def qQ {N k r t P:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
    (w:qI k) (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ):
    ∀ (rem d:ℕ),d+rem=P→(In N→Fin P→V k)→(In N→qS P k)
 | 0,d,_,Q,x=>
   (z8 d hk nm c w side site tar h Q x,fun i=>decide (i.val=d),Q x)
 | rem+1,d,hd,Q,x=>
   let selfR:qS P k:=(z8 d hk nm c w side site tar h Q x,fun i=>decide (i.val=d),Q x)
   let childR:Fin (qC t P h)→qS P k:=fun b=>
    qQ hk nm c w side site tar h rem (d+1) (by omega)
     (qR d hk nm c w side site tar h Q b) x
   q3 selfR (vV childR)
lemma yV {N k r t P:ℕ} (d:ℕ) (hd:d<P) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ)
 (Q:In N→Fin P→V k) (b:Fin (qC t P h)) (x:In N)
 (hzero:∀ i:Fin P,d≤ i.val→Q x i=0):
 Submodule.span F (Set.range (qR d hk nm c w side site tar h Q b x))=
  Submodule.span F (Set.range (Q x)) ⊔
  Submodule.span F ({q5 d hk nm c w side site tar h Q b x}:Set (V k)):=by
 apply le_antisymm
 · rw [Submodule.span_le]
   rintro _ ⟨i,rfl⟩
   unfold qR
   by_cases hi:i.val=d
   · rw [ite_eq_left hi]
     exact Submodule.mem_sup_right (Submodule.subset_span rfl)
   · rw [ite_eq_right hi]
     exact Submodule.mem_sup_left (Submodule.subset_span ⟨i,rfl⟩)
 · apply sup_le
   · rw [Submodule.span_le]
     rintro _ ⟨i,rfl⟩
     by_cases hi:i.val=d
     · rw [hzero i (by omega)]; exact Submodule.zero_mem _
     · have hq:qR d hk nm c w side site tar h Q b x i=Q x i:=by simp [qR,hi]
       rw [← hq]; exact Submodule.subset_span ⟨i,rfl⟩
   · rw [Submodule.span_le]
     rintro _ rfl
     have hq:qR d hk nm c w side site tar h Q b x ⟨d,hd⟩=
      q5 d hk nm c w side site tar h Q b x:=by simp [qR]
     rw [← hq]; exact Submodule.subset_span ⟨⟨d,hd⟩,rfl⟩
lemma zS {k:ℕ} (S:Submodule F (V k)) (v:V k):
 Module.finrank F (S ⊔ Submodule.span F ({v}:Set (V k)):Submodule F (V k))≤
  Module.finrank F S+1:=by
 have hm:=Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span F ({v}:Set (V k)))
 have h1:Module.finrank F (Submodule.span F ({v}:Set (V k)))≤1:=by
  have hle:=finrank_span_le_card (R:=F) ({v}:Set (V k))
  have hc:({v}:Set (V k)).toFinset=({v}:Finset (V k)):=by ext z; simp
  rw [hc,Finset.card_singleton] at hle
  exact hle
 omega
lemma yL {k:ℕ} (S:Submodule F (V k)) {v:V k} (hv:v∉S):
 Module.finrank F (S ⊔ Submodule.span F ({v}:Set (V k)):Submodule F (V k))=
  Module.finrank F S+1:=by
 have hle:=zS S v
 have hlt:S<S ⊔ Submodule.span F ({v}:Set (V k)):=by
  rw [lt_iff_le_and_ne]
  refine ⟨le_sup_left,fun heq=>hv ?_⟩
  rw [heq]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
 have hfl:Module.finrank F S<Module.finrank F (S ⊔ Submodule.span F ({v}:Set (V k)):Submodule F (V k)):=
  Submodule.finrank_lt_finrank_of_lt hlt
 omega
lemma kn {N k r t P:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (hc:closed hk w (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,w (side i) (r+1) (site i)=true) (tar:In N→V t) (h:ℕ):
 ∀ (rem d:ℕ) (hd:d+rem=P) (Q:In N→Fin P→V k) (x:In N),
   Module.finrank F (Submodule.span F (Set.range (Q x)))≤d→
   (∀ i:Fin P,d≤ i.val→Q x i=0)→
   zF hk w side site h (nm x) (c x) d (qQ hk nm c w side site tar h rem d hd Q x):=by
 intro rem
 induction rem with
 | zero=>
   intro d hd Q x hrk _
   refine ⟨d,le_rfl,by omega,rfl,fun hok=>?_⟩
   exact ⟨(kS d hk nm c w hc side site hw tar h Q x hrk).mp hok,hrk⟩
 | succ rem ih=>
   intro d hd Q x hrk hzero
   have hself:zF hk w side site h (nm x) (c x) d
    (z8 d hk nm c w side site tar h Q x,fun i=>decide (i.val=d),Q x):=
    ⟨d,le_rfl,by omega,rfl,fun hok=>
      ⟨(kS d hk nm c w hc side site hw tar h Q x hrk).mp hok,hrk⟩⟩
   have hchild (b:Fin (qC t P h)):
    zF hk w side site h (nm x) (c x) d
     (qQ hk nm c w side site tar h rem (d+1) (by omega)
       (qR d hk nm c w side site tar h Q b) x):=by
    have hsp:=yV d (by omega) hk nm c w side site tar h Q b x hzero
    have hrk':Module.finrank F (Submodule.span F (Set.range (qR d hk nm c w side site tar h Q b x)))≤d+1:=by
     rw [hsp]; exact (zS _ _).trans (by omega)
    have hz':∀ i:Fin P,d+1≤ i.val→qR d hk nm c w side site tar h Q b x i=0:=by
     intro i hi
     have hne:i.val≠d:=by omega
     simp [qR,hne,hzero i (by omega)]
    obtain ⟨d',hd'1,hd'2,heq',hok'⟩:=ih (d+1) (by omega) (qR d hk nm c w side site tar h Q b) x hrk' hz'
    exact ⟨d',by omega,hd'2,heq',hok'⟩
   have hfold:∀ (l:List (Fin (qC t P h))) (acc:qS P k),
    zF hk w side site h (nm x) (c x) d acc→
    zF hk w side site h (nm x) (c x) d
     (l.foldl (fun a b=>q3 a (qQ hk nm c w side site tar h rem (d+1) (by omega)
       (qR d hk nm c w side site tar h Q b) x)) acc):=by
    intro l
    induction l with
    | nil=>intro acc hacc; exact hacc
    | cons b l ihl=>
      intro acc hacc
      exact ihl _ (yf hk w side site h d (nm x) (c x) hacc (hchild b))
   have hempty:zF hk w side site h (nm x) (c x) d (vi P k):=
    ⟨P,by omega,le_rfl,rfl,fun hfalse=>Bool.noConfusion hfalse⟩
   exact yf hk w side site h d (nm x) (c x) hself (hfold _ _ hempty)
lemma kI {k r t P:ℕ} (hk:0<k) (w:qI k) (_hc:closed hk w (r+1))
 (side:Fin t→Bool) (site:Fin t→Fin k) (_hw:∀ i,w (side i) (r+1) (site i)=true)
 (h:ℕ) (nm:Bool→V k) (c:Bool→Fin (r+1)→V k) (_tar:V t)
 {Q1 Q2:Fin P→V k} (hsp:Submodule.span F (Set.range Q1)=Submodule.span F (Set.range Q2))
 (hw2:ze hk w side site h nm c Q2):ze hk w side site h nm c Q1:=by
 have hker_eq:∀ u:V k,(∀ i,dotProduct (Q1 i) u=0)↔(∀ i,dotProduct (Q2 i) u=0):=by
  intro u
  have h1:(∀ i,dotProduct (Q1 i) u=0)↔u∈zM (Submodule.span F (Set.range Q1)):=by
   constructor
   · intro hu v hv
     refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
     · rintro _ ⟨i,rfl⟩; rw [dotProduct_comm]; exact hu i
     · exact dotProduct_zero _
     · intro x y _ _ hx hy; rw [dotProduct_add,hx,hy,add_zero]
     · intro a x _ hx; rw [dotProduct_smul,hx,smul_zero]
   · intro hu i; rw [dotProduct_comm]; exact hu (Q1 i) (Submodule.subset_span ⟨i,rfl⟩)
  have h2:(∀ i,dotProduct (Q2 i) u=0)↔u∈zM (Submodule.span F (Set.range Q2)):=by
   constructor
   · intro hu v hv
     refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
     · rintro _ ⟨i,rfl⟩; rw [dotProduct_comm]; exact hu i
     · exact dotProduct_zero _
     · intro x y _ _ hx hy; rw [dotProduct_add,hx,hy,add_zero]
     · intro a x _ hx; rw [dotProduct_smul,hx,smul_zero]
   · intro hu i; rw [dotProduct_comm]; exact hu (Q2 i) (Submodule.subset_span ⟨i,rfl⟩)
  rw [h1,h2,hsp]
 let eD:{u:V k // ∀ i,dotProduct (Q1 i) u=0} ≃ {u:V k // ∀ i,dotProduct (Q2 i) u=0}:=
  { toFun:=fun u=>⟨u.val,(hker_eq u.val).mp u.property⟩
    invFun:=fun u=>⟨u.val,(hker_eq u.val).mpr u.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
 refine ⟨fun a b n hn j hj x y=>hw2.1 a b n hn j hj (eD x) (eD y),fun a=>?_⟩
 let pr:=fun (key:V k) (i:Fin t)=>state hk nm c (side i) key (r+1) (site i)
 let pol1:=fun (i:Fin t) (xy:{u:V k // ∀ i,dotProduct (Q1 i) u=0}×{u:V k // ∀ i,dotProduct (Q1 i) u=0})=>
  pr a i+pr (a+xy.1.val) i+pr (a+xy.2.val) i+pr (a+xy.1.val+xy.2.val) i
 let pol2:=fun (i:Fin t) (xy:{u:V k // ∀ i,dotProduct (Q2 i) u=0}×{u:V k // ∀ i,dotProduct (Q2 i) u=0})=>
  pr a i+pr (a+xy.1.val) i+pr (a+xy.2.val) i+pr (a+xy.1.val+xy.2.val) i
 let eqv:({u:V k // ∀ i,dotProduct (Q1 i) u=0}×{u:V k // ∀ i,dotProduct (Q1 i) u=0}→F) ≃ₗ[F]
     ({u:V k // ∀ i,dotProduct (Q2 i) u=0}×{u:V k // ∀ i,dotProduct (Q2 i) u=0}→F):=
  LinearEquiv.funCongrLeft F F (Equiv.prodCongr eD.symm eD.symm)
 have hmap:Submodule.map eqv.toLinearMap (Submodule.span F (Set.range pol1))=
  Submodule.span F (Set.range pol2):=by
  rw [Submodule.map_span]
  congr 1; ext f
  simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and]
  apply exists_congr; intro i
  have hi:eqv.toLinearMap (pol1 i)=pol2 i:=by funext ⟨u,v⟩; rfl
  rw [hi]
 rw [← zX eqv.toLinearMap eqv.injective,hmap]
 exact hw2.2 a
lemma yP {N k r t P:ℕ} (hk:0<k) (nm:qJ N k) (c:Cst N k r)
 (w:qI k) (hc:closed hk w (r+1)) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hw:∀ i,w (side i) (r+1) (site i)=true) (tar:In N→V t) (h:ℕ):
 ∀ (rem d:ℕ) (hd:d+rem=P) (Q:In N→Fin P→V k) (x:In N) (Qopt:Fin P→V k),
   ze hk w side site h (nm x) (c x) Qopt→
   Submodule.span F (Set.range (Q x))≤Submodule.span F (Set.range Qopt)→
   Module.finrank F (Submodule.span F (Set.range (Q x)))=d→
   (∀ i:Fin P,d≤ i.val→Q x i=0)→
   yC (qQ hk nm c w side site tar h rem d hd Q x)
    (Module.finrank F (Submodule.span F (Set.range Qopt))):=by
 intro rem
 induction rem with
 | zero=>
   intro d hd Q x Qopt hworks hle hrk _
   have hopt_le:Module.finrank F (Submodule.span F (Set.range Qopt))≤P:=
    (finrank_span_le_card _).trans (by
      calc (Set.range Qopt).toFinset.card=(Finset.univ.image Qopt).card:=by congr 1; ext z; simp
       _≤P:=(Finset.card_image_le).trans_eq (Fintype.card_fin P))
   have hle_rk:Module.finrank F (Submodule.span F (Set.range (Q x)))≤
    Module.finrank F (Submodule.span F (Set.range Qopt)):=Submodule.finrank_mono hle
   have hsp_eq:Submodule.span F (Set.range (Q x))=Submodule.span F (Set.range Qopt):=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
   have hwQ:ze hk w side site h (nm x) (c x) (Q x):=
    kI hk w hc side site hw h (nm x) (c x) (tar x) hsp_eq hworks
   have hok:z8 d hk nm c w side site tar h Q x=true:=
    (kS d hk nm c w hc side site hw tar h Q x (le_of_eq hrk)).mpr hwQ
   exact ⟨hok,d,by omega,by omega,rfl⟩
 | succ rem ih=>
   intro d hd Q x Qopt hworks hle hrk hzero
   have hd_le_opt:d≤Module.finrank F (Submodule.span F (Set.range Qopt)):=
    hrk▸Submodule.finrank_mono hle
   have hvalid_child (b:Fin (qC t P h)):
    zF hk w side site h (nm x) (c x) (d+1)
     (qQ hk nm c w side site tar h rem (d+1) (by omega)
       (qR d hk nm c w side site tar h Q b) x):=by
    have hsp:=yV d (by omega) hk nm c w side site tar h Q b x hzero
    have hrk':Module.finrank F (Submodule.span F (Set.range (qR d hk nm c w side site tar h Q b x)))≤d+1:=by
     rw [hsp]; exact (zS _ _).trans (by omega)
    have hz':∀ i:Fin P,d+1≤ i.val→qR d hk nm c w side site tar h Q b x i=0:=by
     intro i hi; have hne:i.val≠d:=by omega
     simp only [qR,ite_eq_right hne]; exact hzero i (by omega)
    exact kn hk nm c w hc side site hw tar h rem (d+1) (by omega)
     (qR d hk nm c w side site tar h Q b) x hrk' hz'
   have hvalid_mfin:zF hk w side site h (nm x) (c x) d
    (vV fun b=>qQ hk nm c w side site tar h rem (d+1) (by omega)
      (qR d hk nm c w side site tar h Q b) x):=by
    have hfold:∀ (l:List (Fin (qC t P h))) (acc:qS P k),
     zF hk w side site h (nm x) (c x) d acc→
     zF hk w side site h (nm x) (c x) d
      (l.foldl (fun a b=>q3 a (qQ hk nm c w side site tar h rem (d+1) (by omega)
        (qR d hk nm c w side site tar h Q b) x)) acc):=by
     intro l; induction l with
     | nil=>intro acc hacc; exact hacc
     | cons b l ihl=>
       intro acc hacc
       obtain ⟨d',hd'1,hd'2,heq',hok'⟩:=hvalid_child b
       exact ihl _ (yf hk w side site h d (nm x) (c x) hacc ⟨d',by omega,hd'2,heq',hok'⟩)
    exact hfold _ _ ⟨P,by omega,le_rfl,rfl,fun hf=>Bool.noConfusion hf⟩
   obtain ⟨dChild,_,hdChildP,heqChild,_⟩:=hvalid_mfin
   cases hok:z8 d hk nm c w side site tar h Q x
   · obtain ⟨b0,hb0_in,hb0_out⟩:=
      uz d hk nm c w hc side site hw tar h Q x (le_of_eq hrk) hok Qopt hworks hle
     have hsp:=yV d (by omega) hk nm c w side site tar h Q b0 x hzero
     have hle':Submodule.span F (Set.range (qR d hk nm c w side site tar h Q b0 x))≤
      Submodule.span F (Set.range Qopt):=by
      rw [hsp]; exact sup_le hle (by rw [Submodule.span_le]; rintro _ rfl; exact hb0_in)
     have hrk':Module.finrank F (Submodule.span F (Set.range (qR d hk nm c w side site tar h Q b0 x)))=d+1:=by
      rw [hsp,yL _ hb0_out,hrk]
     have hz':∀ i:Fin P,d+1≤ i.val→qR d hk nm c w side site tar h Q b0 x i=0:=by
      intro i hi; have hne:i.val≠d:=by omega
      simp only [qR,ite_eq_right hne]; exact hzero i (by omega)
     have hch0:=ih (d+1) (by omega) (qR d hk nm c w side site tar h Q b0) x Qopt hworks hle' hrk' hz'
     have hfold_dl:∀ (l:List (Fin (qC t P h))) (acc:qS P k),
      zF hk w side site h (nm x) (c x) d acc→
      (yC acc (Module.finrank F (Submodule.span F (Set.range Qopt)))∨b0∈l)→
      yC (l.foldl (fun a b=>q3 a (qQ hk nm c w side site tar h rem (d+1) (by omega)
       (qR d hk nm c w side site tar h Q b) x)) acc)
       (Module.finrank F (Submodule.span F (Set.range Qopt))):=by
      intro l
      induction l with
      | nil=>
        intro acc _ hdisj; rcases hdisj with h1|h2
        · exact h1
        · exact absurd h2 List.not_mem_nil
      | cons b l ihl=>
        intro acc hacc hdisj
        have ⟨dA,_,hdAP,heqA,_⟩:=hacc
        obtain ⟨dB,hdB1,hdBP,heqB,hokB⟩:=hvalid_child b
        have hnxtV:zF hk w side site h (nm x) (c x) d
         (q3 acc (qQ hk nm c w side site tar h rem (d+1) (by omega)
           (qR d hk nm c w side site tar h Q b) x)):=
         yf hk w side site h d (nm x) (c x) hacc ⟨dB,by omega,hdBP,heqB,hokB⟩
        apply ihl _ hnxtV
        rcases hdisj with hacc_dl|hmem
        · left
          obtain ⟨hacc1,dA',hdA'opt,hdA'P,heqA'⟩:=hacc_dl
          exact yx hdA'P hdBP heqA' heqB hacc1 hdA'opt
        · rcases List.mem_cons.mp hmem with rfl|hl
          · left
            obtain ⟨hb1,dB',hdB'opt,hdB'P,heqB'⟩:=hch0
            exact yj hdAP hdB'P heqA heqB' hb1 hdB'opt
          · exact Or.inr hl
     have hmf_dl:=hfold_dl (List.finRange (qC t P h)) (vi P k)
      ⟨P,by omega,le_rfl,rfl,fun hf=>Bool.noConfusion hf⟩ (Or.inr (List.mem_finRange b0))
     obtain ⟨hmf1,dM,hdMopt,hdMP,heqM⟩:=hmf_dl
     exact yj (by omega) hdMP rfl heqM hmf1 hdMopt
   · exact yx (by omega) hdChildP rfl heqChild hok hd_le_opt
def z9 (k r t:ℕ):ℕ:=2 ^ 28 * (k+r+t+6) ^ 10
private lemma uk (S10 K D B R c16:ℕ)
 (hK:K=2 ^ 28 * S10) (hc16:c16≤16 * S10) (hD1:1≤D) (hB3:3≤B) (hR1:1≤R):
 2 ^ 27 * S10 * (D+B)+(B * (2 * K * (D * 2) * R-K * (D * 2))+(B * c16+c16))≤
   2 * K * D * (R * (2 * B))-K * D:=by
 have h16:(B+1) * c16≤2 ^ 27 * S10 * B:=by
  have hB1:B+1≤2 * B:=by omega
  calc (B+1) * c16≤(2 * B) * (16 * S10):=Nat.mul_le_mul hB1 hc16
   _=32 * S10 * B:=by ring
   _≤2 ^ 27 * S10 * B:=by gcongr; decide
 have hLoc:2 ^ 27 * S10 * (D+B)+(B * c16+c16)≤K * (D+B):=by
  have hdist1:B * c16+c16=(B+1) * c16:=by ring
  have hKeq:K * (D+B)=2 ^ 27 * S10 * (D+B)+2 ^ 27 * S10 * D+2 ^ 27 * S10 * B:=by
   rw [hK]; ring
  rw [hdist1,hKeq]; omega
 have hmul_sub:B * (2 * K * (D * 2) * R-K * (D * 2))=
  2 * K * D * (R * (2 * B))-K * (2 * B) * D:=by
  rw [Nat.mul_sub_left_distrib]; congr 1 <;> ring
 have hkey:2 * D+B≤2 * B * D:=by
  have h1:B≤B * D:=Nat.le_mul_of_pos_right B hD1
  have h2:2 * D≤B * D:=Nat.mul_le_mul_right D (by omega)
  have h3:2 * B * D=B * D+B * D:=by ring
  omega
 have hkeyK:K * (D+B)+K * D≤K * (2 * B) * D:=by
  calc K * (D+B)+K * D=K * (2 * D+B):=by ring
   _≤K * (2 * B * D):=Nat.mul_le_mul_left K hkey
   _=K * (2 * B) * D:=by ring
 have hbig:K * (2 * B) * D≤2 * K * D * (R * (2 * B)):=by
  have h1:K * (2 * B) * D=K * D * (2 * B):=by ring
  have h2:K * D * (2 * B)≤(2 * K * D) * (2 * B):=
   Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have h3:(2 * K * D) * (2 * B)≤(2 * K * D * R) * (2 * B):=
   Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hR1)
  have h4:(2 * K * D * R) * (2 * B)=2 * K * D * (R * (2 * B)):=by ring
  rw [h1]; exact h2.trans (h3.trans (le_of_eq h4))
 rw [hmul_sub]; omega
theorem jz {N k r t P:ℕ} (hPk:P≤k) (hk:0<k)
 (nm:qJ N k) (c:Cst N k r) (w:qI k)
 (side:Fin t→Bool) (site:Fin t→Fin k) (tar:In N→V t) (h:ℕ):
 ∀ (rem d:ℕ) (hd:d+rem=P) (Q:In N→Fin P→V k) (A:Set (Sig N)),
   (fun _=>false)∈A→(fun _=>true)∈A→
   (∀ b j,(bit fun x=>nm x b j)∈A)→
   (∀ b n j,(bit fun x=>c x b n j)∈A)→
   (∀ u,(bit fun x=>tar x u)∈A)→
   (∀ i j,(fun x=>z2b (Q x i j))∈A)→
   qa A (qH (qQ hk nm c w side site tar h rem d hd Q))
    (2 * z9 k r t * 2 ^ d * (2 * qC t P h) ^ rem-z9 k r t * 2 ^ d):=by
 intro rem
 induction rem with
 | zero=>
   intro d hd Q A hF hT hnm hc htar hQ
   have hChk:=uH d hPk hk nm c w side site tar h Q A hF hT hnm hc htar hQ
   refine qd hChk le_rfl ?_ ?_
   · rintro f ((rfl|⟨i,rfl⟩)|⟨a,j,rfl⟩)
     · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
     · dsimp only
       by_cases hi:i.val=d
       · have heq:(fun x:In N=>(qQ hk nm c w side site tar h 0 d hd Q x).2.1 i)=(fun _=>true):=by
          funext _; simp [qQ,hi]
         rw [heq]; exact Or.inl hT
       · have heq:(fun x:In N=>(qQ hk nm c w side site tar h 0 d hd Q x).2.1 i)=(fun _=>false):=by
          funext _; simp [qQ,hi]
         rw [heq]; exact Or.inl hF
     · exact Or.inl (hQ a j)
   · simp only [pow_zero,Nat.mul_one]
     have hsub:2 * z9 k r t * 2 ^ d-z9 k r t * 2 ^ d=z9 k r t * 2 ^ d:=by
      rw [Nat.mul_assoc,Nat.two_mul,Nat.add_sub_cancel]
     rw [hsub]
     unfold z9
     exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
 | succ rem ih=>
   intro d hd Q A hF hT hnm hc htar hQ
   let B:=qC t P h
   let K:=z9 k r t
   have hBr:=jv d hPk hk nm c w side site tar h Q A hF hT hnm hc htar hQ
   let A1:=A ∪ ({z8 d hk nm c w side site tar h Q} ∪
    {f|∃ (b:Fin B) (j:Fin k),(fun x=>z2b (q5 d hk nm c w side site tar h Q b x j))=f})
   have hF1:(fun _=>false)∈A1:=Or.inl hF
   have hT1:(fun _=>true)∈A1:=Or.inl hT
   have hChild (b:Fin B):
    qa A1 (qH (qQ hk nm c w side site tar h rem (d+1) (by omega)
     (qR d hk nm c w side site tar h Q b)))
     (2 * K * 2 ^ (d+1) * (2 * B) ^ rem-K * 2 ^ (d+1)):=by
    apply ih (d+1) (by omega) _ A1 hF1 hT1
     (fun b' j=>Or.inl (hnm b' j)) (fun b' n j=>Or.inl (hc b' n j)) (fun u=>Or.inl (htar u))
    intro i j
    by_cases hi:i.val=d
    · have heq:(fun x=>z2b (qR d hk nm c w side site tar h Q b x i j))=
       (fun x=>z2b (q5 d hk nm c w side site tar h Q b x j)):=by
       funext x; simp [qR,hi]
      rw [heq]; exact Or.inr (Or.inr ⟨b,j,rfl⟩)
    · have heq:(fun x=>z2b (qR d hk nm c w side site tar h Q b x i j))=
       (fun x=>z2b (Q x i j)):=by
       funext x; simp [qR,hi]
      rw [heq]; exact Or.inl (hQ i j)
   have hAllCh:qa A1 (⋃ b:Fin B,qH (qQ hk nm c w side site tar h rem (d+1) (by omega)
    (qR d hk nm c w side site tar h Q b)))
    (B * (2 * K * 2 ^ (d+1) * (2 * B) ^ rem-K * 2 ^ (d+1))):=
    v7 _ _ hChild
   let A2:=A1 ∪ ⋃ b:Fin B,qH (qQ hk nm c w side site tar h rem (d+1) (by omega)
    (qR d hk nm c w side site tar h Q b))
   have hMF:=k8 hPk (A:=A2) (Or.inl hF1) (Or.inl hT1)
    (fun b=>qQ hk nm c w side site tar h rem (d+1) (by omega)
      (qR d hk nm c w side site tar h Q b))
    (fun b _ hf=>Or.inr (Set.mem_iUnion.mpr ⟨b,hf⟩))
   let A3:=A2 ∪ qH (fun x=>vV fun b=>
    qQ hk nm c w side site tar h rem (d+1) (by omega)
     (qR d hk nm c w side site tar h Q b) x)
   let selfR:In N→qS P k:=fun x=>
    (z8 d hk nm c w side site tar h Q x,fun i=>decide (i.val=d),Q x)
   have hSelfMem:qH selfR⊆A3:=by
    rintro f ((rfl|⟨i,rfl⟩)|⟨a,j,rfl⟩)
    · exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
    · dsimp only
      by_cases hi:i.val=d
      · have heq:(fun x:In N=>(selfR x).2.1 i)=(fun _=>true):=by funext _; simp [selfR,hi]
        rw [heq]; exact Or.inl (Or.inl hT1)
      · have heq:(fun x:In N=>(selfR x).2.1 i)=(fun _=>false):=by funext _; simp [selfR,hi]
        rw [heq]; exact Or.inl (Or.inl hF1)
    · exact Or.inl (Or.inl (Or.inl (hQ a j)))
   have hFinal:=u1 hPk (A:=A3) (Or.inl (Or.inl hF1)) selfR
    (fun x=>vV fun b=>qQ hk nm c w side site tar h rem (d+1) (by omega)
      (qR d hk nm c w side site tar h Q b) x)
    hSelfMem Set.subset_union_right
   have hTot:=qe hBr (qe hAllCh (qe hMF hFinal))
   refine qd hTot le_rfl Set.subset_union_right ?_
   have hB3:3≤B:=y9 t P h
   have hs1:1≤k+r+t+6:=by omega
   have hk2:(k+6) ^ 2≤(k+r+t+6) ^ 10:=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right hs1 (by decide))
   rw [pow_succ 2 d,pow_succ (2 * B) rem]
   exact uk ((k+r+t+6) ^ 10) K (2 ^ d) B ((2 * B) ^ rem) (16 * (k+6) ^ 2)
    rfl (Nat.mul_le_mul_left 16 hk2) Nat.one_le_two_pow hB3 (Nat.one_le_pow rem (2 * B) (by omega))
abbrev InN (k r t:ℕ):=(2+2 * (r+1)) * k+t
abbrev vP (k r t:ℕ):=(Bool×Fin k) ⊕ ((Bool×Fin (r+1)×Fin k) ⊕ Fin t)
def vz {k r t} (b:Bool) (j:Fin k):vP k r t:=Sum.inl (b,j)
def yu {k r t} (b:Bool) (i:Fin (r+1)) (j:Fin k):vP k r t:=Sum.inr (Sum.inl (b,i,j))
def v8 {k r t} (i:Fin t):vP k r t:=Sum.inr (Sum.inr i)
def vU (k r t:ℕ):List (vP k r t):=
 List.ofFn (vz false)++List.ofFn (vz true)++
 (List.ofFn fun i=>List.ofFn (yu false i)).flatten++
 (List.ofFn fun i=>List.ofFn (yu true i)).flatten++
 List.ofFn v8
theorem yT (k r t:ℕ):(vU k r t).length=InN k r t:=by
 simp [vU,List.length_flatten,InN,Function.comp_def,List.ofFn_const]; ring
theorem jt {k r t} (s:vP k r t):s∈vU k r t:=by
 rcases s with ⟨b,j⟩|(⟨b,i,j⟩|i)
 · cases b <;> simp [vU,vz,List.mem_ofFn]
 · cases b <;> simp [vU,yu,List.mem_flatten,List.mem_ofFn] <;> tauto
 · simp [vU,v8,List.mem_ofFn]
def kQ {k r t} (s:vP k r t):Fin (InN k r t):=
 ⟨(vU k r t).idxOf s,yT k r t▸List.idxOf_lt_length_of_mem (jt s)⟩
def ug {k r t} (x:In (InN k r t)) (s:vP k r t):F:=b2z (x (kQ s))
def uh {k r t} (v:vP k r t→F):In (InN k r t):=
 fun i=>z2b (v ((vU k r t).get ⟨i.val,by rw [yT]; exact i.isLt⟩))
theorem kj {k r t} (v:vP k r t→F) (s:vP k r t):
 ug (uh v) s=v s:=by
 simp [ug,uh,kQ,vr,List.get_eq_getElem,List.getElem_idxOf]
def v9 {k r t} (name:Bool→V k) (c:Bool→Fin (r+1)→V k) (tar:V t):vP k r t→F
 | .inl (b,j)=>name b j
 | .inr (.inl (b,i,j))=>c b i j
 | .inr (.inr i)=>tar i
theorem jk {k r t} (name:Bool→V k) (c:Bool→Fin (r+1)→V k) (tar:V t):
 let pack:=fun w:V k=>List.ofFn (fun j=>decide (w j≠0))
 List.ofFn (uh (v9 name c tar))=
  pack (name false)++pack (name true)++
  (List.ofFn (fun i=>pack (c false i))).flatten++
  (List.ofFn (fun i=>pack (c true i))).flatten++
  List.ofFn (fun i=>decide (tar i≠0)):=by
 intro pack
 let v:=v9 name c tar
 have eqmap:List.ofFn (uh v)=(vU k r t).map (fun s=>z2b (v s)):=by
  apply List.ext_getElem
  · simp [yT]
  · intro i hi hj; simp [uh]
 rw [eqmap]
 simp only [vU,List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,
  vz,yu,v8,v,v9,pack,z2b]
 rfl
def vX {k r t} (x:In (InN k r t)) (b:Bool) (j:Fin k):F:=ug x (vz b j)
def inC {k r t} (x:In (InN k r t)) (b:Bool) (n:Fin (r+1)) (j:Fin k):F:=ug x (yu b n j)
def yl {k r t} (x:In (InN k r t)) (i:Fin t):F:=ug x (v8 i)
theorem uu {N k P L b:ℕ} {A:Set (Sig N)} {flag:Sig N}
 {mask:Fin P→Fin k→Sig N} {ans:Fin L→Sig N}
 (hs:vK N 0 A)
 (hb:qa A ({flag} ∪ {f|∃ a j,mask a j=f} ∪ Set.range ans) b):
 ∃ (C:Circuit) (f:Fin (N+C.size)) (mW:Fin P→Fin k→Fin (N+C.size))
   (out:Fin L→Fin (N+C.size)),
   FanInTwo C∧ReadsBack N C∧C.output=f.val∧C.size≤b∧
   (∀ x,(C.wires (List.ofFn x)).getD f.val false=flag x)∧
   (∀ a j x,(C.wires (List.ofFn x)).getD (mW a j).val false=mask a j x)∧
   (∀ i x,(C.wires (List.ofFn x)).getD (out i).val false=ans i x):=by
 obtain ⟨c,hc,gs,hlen,hr,hf,hw⟩:=hb.run hs le_rfl
 obtain ⟨fi,hfi,hflag⟩:=hw flag (Or.inr (Or.inl (Or.inl rfl)))
 have hmcho:∀ (a:Fin P) (j:Fin k),∃ p:Fin (N+gs.length),∀ x,
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD p.val false=mask a j x:=by
  intro a j
  obtain ⟨p,hp,h⟩:=hw (mask a j) (Or.inr (Or.inl (Or.inr ⟨a,j,rfl⟩)))
  exact ⟨⟨p,by omega⟩,h⟩
 choose mW hmW using hmcho
 have hacho:∀ i:Fin L,∃ p:Fin (N+gs.length),∀ x,
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD p.val false=ans i x:=by
  intro i
  obtain ⟨p,hp,h⟩:=hw (ans i) (Or.inr (Or.inr ⟨i,rfl⟩))
  exact ⟨⟨p,by omega⟩,h⟩
 choose out hout using hacho
 exact ⟨⟨gs,fi⟩,⟨fi,by change fi<N+gs.length; omega⟩,mW,out,hf,hr,rfl,
  by change gs.length≤b; omega,hflag,hmW,hout⟩
private lemma uO (k r t p h:ℕ):
 let P:=min k p
 let H:=min t h
 let br:=qC t P h
 2+((2 * z9 k r t * 2 ^ 0 * (2 * br) ^ P-z9 k r t * 2 ^ 0) +
  (128 * (k+P+4) ^ 5 * 2 ^ 0+(128 * (k+k+4) ^ 5 * 2 ^ P +
    (2 ^ P * (2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H) +
      (32 * (2 ^ P+1) * (k+2)+(k+1) * 1)))))≤
  2 ^ 60 * (k+r+t+6) ^ 22 * ((2 * br) ^ P+2 ^ (P+H)):=by
 intro P H br
 set s:=k+r+t+6
 have hPk:P≤k:=Nat.min_le_left k p
 have hs1:1≤ s:=by omega
 have hP1:1≤2 ^ P:=Nat.one_le_two_pow
 have hH1:1≤2 ^ H:=Nat.one_le_two_pow
 have hPH:2 ^ P * 2 ^ H=2 ^ (P+H):=(pow_add 2 P H).symm
 let X1:=s ^ 22 * (2 * br) ^ P
 let X2:=s ^ 22 * 2 ^ (P+H)
 have hM1:2 * z9 k r t * 2 ^ 0 * (2 * br) ^ P-z9 k r t * 2 ^ 0≤2 ^ 29 * X1:=by
  have h1:2 * z9 k r t * 2 ^ 0 * (2 * br) ^ P-z9 k r t * 2 ^ 0≤
   2 * z9 k r t * (2 * br) ^ P:=by
   rw [pow_zero,Nat.mul_one,Nat.mul_one]; exact Nat.sub_le _ _
  have h2:2 * z9 k r t≤2 ^ 29 * s ^ 22:=by
   have hp:s ^ 10≤ s ^ 22:=Nat.pow_le_pow_right hs1 (by omega)
   have h29:2 * 2 ^ 28=2 ^ 29:=by rw [← pow_succ']
   calc 2 * z9 k r t=(2 * 2 ^ 28) * s ^ 10:=by
         unfold z9; dsimp [s]; exact (Nat.mul_assoc 2 (2 ^ 28) ((k+r+t+6) ^ 10)).symm
    _=2 ^ 29 * s ^ 10:=by rw [h29]
    _≤2 ^ 29 * s ^ 22:=Nat.mul_le_mul_left _ hp
  have h3:=h1.trans (Nat.mul_le_mul_right _ h2)
  exact h3.trans (le_of_eq (Nat.mul_assoc (2 ^ 29) (s ^ 22) ((2 * br) ^ P)))
 have hM2:128 * (k+P+4) ^ 5 * 2 ^ 0≤2 ^ 15 * X2:=by
  rw [pow_zero,Nat.mul_one]
  have h1:k+P+4≤2 * s:=by omega
  have h2:(k+P+4) ^ 5≤2 ^ 5 * s ^ 5:=by
   rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left h1 5
  have h3:128 * 2 ^ 5=2 ^ 12:=by decide
  have h4:2 ^ 12≤2 ^ 15:=Nat.pow_le_pow_right (by omega) (by omega)
  have h5:s ^ 5≤ s ^ 22:=Nat.pow_le_pow_right hs1 (by omega)
  have h6:128 * (k+P+4) ^ 5≤2 ^ 15 * s ^ 22:=by
   calc 128 * (k+P+4) ^ 5≤128 * (2 ^ 5 * s ^ 5):=Nat.mul_le_mul_left 128 h2
    _=(128 * 2 ^ 5) * s ^ 5:=(Nat.mul_assoc _ _ _).symm
    _=2 ^ 12 * s ^ 5:=by rw [h3]
    _≤2 ^ 15 * s ^ 22:=Nat.mul_le_mul h4 h5
  have h7:2 ^ 15 * s ^ 22≤2 ^ 15 * s ^ 22 * 2 ^ (P+H):=
   Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  exact h6.trans (h7.trans (le_of_eq (Nat.mul_assoc (2 ^ 15) (s ^ 22) (2 ^ (P+H)))))
 have hM3:128 * (k+k+4) ^ 5 * 2 ^ P≤2 ^ 15 * X2:=by
  have h1:k+k+4≤2 * s:=by omega
  have h2:(k+k+4) ^ 5≤2 ^ 5 * s ^ 5:=by
   rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left h1 5
  have h3:128 * 2 ^ 5=2 ^ 12:=by decide
  have h4:2 ^ 12≤2 ^ 15:=Nat.pow_le_pow_right (by omega) (by omega)
  have h5:s ^ 5≤ s ^ 22:=Nat.pow_le_pow_right hs1 (by omega)
  have h6:128 * (k+k+4) ^ 5≤2 ^ 15 * s ^ 22:=by
   calc 128 * (k+k+4) ^ 5≤128 * (2 ^ 5 * s ^ 5):=Nat.mul_le_mul_left 128 h2
    _=(128 * 2 ^ 5) * s ^ 5:=(Nat.mul_assoc _ _ _).symm
    _=2 ^ 12 * s ^ 5:=by rw [h3]
    _≤2 ^ 15 * s ^ 22:=Nat.mul_le_mul h4 h5
  have h7:128 * (k+k+4) ^ 5 * 2 ^ P≤2 ^ 15 * s ^ 22 * 2 ^ P * 2 ^ H:=
   (Nat.mul_le_mul_right _ h6).trans (Nat.le_mul_of_pos_right _ hH1)
  have heq:2 ^ 15 * s ^ 22 * 2 ^ P * 2 ^ H=2 ^ 15 * X2:=by
   dsimp only [X2]; rw [Nat.mul_assoc (2 ^ 15 * s ^ 22),hPH,Nat.mul_assoc]
  exact h7.trans (le_of_eq heq)
 have hM4:2 ^ P * (2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H)≤2 ^ 45 * X2:=by
  have h1:k+k+r+t+4≤2 * s:=by omega
  have h2:(k+k+r+t+4) ^ 12≤2 ^ 12 * s ^ 12:=by
   rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left h1 12
  have h3:2 ^ 30 * 2 ^ 12=2 ^ 42:=(pow_add 2 30 12).symm
  have h4:2 ^ 42≤2 ^ 45:=Nat.pow_le_pow_right (by omega) (by omega)
  have h5:s ^ 12≤ s ^ 22:=Nat.pow_le_pow_right hs1 (by omega)
  have h6:2 ^ 30 * (k+k+r+t+4) ^ 12≤2 ^ 45 * s ^ 22:=by
   calc 2 ^ 30 * (k+k+r+t+4) ^ 12≤2 ^ 30 * (2 ^ 12 * s ^ 12):=Nat.mul_le_mul_left _ h2
    _=(2 ^ 30 * 2 ^ 12) * s ^ 12:=(Nat.mul_assoc _ _ _).symm
    _=2 ^ 42 * s ^ 12:=by rw [h3]
    _≤2 ^ 45 * s ^ 22:=Nat.mul_le_mul h4 h5
  have h7:2 ^ P * (2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H)=
   2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ (P+H):=by
   calc 2 ^ P * (2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H)
    =(2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H) * 2 ^ P:=Nat.mul_comm _ _
    _=(2 ^ 30 * (k+k+r+t+4) ^ 12) * (2 ^ H * 2 ^ P):=Nat.mul_assoc _ _ _
    _=(2 ^ 30 * (k+k+r+t+4) ^ 12) * (2 ^ P * 2 ^ H):=by rw [Nat.mul_comm (2 ^ H)]
    _=(2 ^ 30 * (k+k+r+t+4) ^ 12) * 2 ^ (P+H):=by rw [hPH]
  rw [h7]
  have h8:=Nat.mul_le_mul_right (2 ^ (P+H)) h6
  exact h8.trans (le_of_eq (Nat.mul_assoc (2 ^ 45) (s ^ 22) (2 ^ (P+H))))
 have hM5:2+(32 * (2 ^ P+1) * (k+2)+(k+1) * 1)≤2 ^ 15 * X2:=by
  have hk1:k+2≤ s:=by omega
  have hs22:s≤ s ^ 22:=by
   have:=Nat.pow_le_pow_right hs1 (by omega:1≤22); rwa [pow_one] at this
  have h1:2 ^ P+1≤2 * 2 ^ P:=by omega
  have h2:32 * (2 ^ P+1) * (k+2)≤64 * (s * 2 ^ P):=by
   have ha:32 * (2 ^ P+1) * (k+2)≤(32 * (2 * 2 ^ P)) * s:=
    Nat.mul_le_mul (Nat.mul_le_mul_left 32 h1) hk1
   have hb:32 * (2 * 2 ^ P) * s=64 * (s * 2 ^ P):=by
    calc 32 * (2 * 2 ^ P) * s=(32 * 2) * 2 ^ P * s:=by rw [← Nat.mul_assoc 32 2]
     _=64 * (2 ^ P * s):=Nat.mul_assoc 64 (2 ^ P) s
     _=64 * (s * 2 ^ P):=by rw [Nat.mul_comm (2 ^ P) s]
   exact ha.trans (le_of_eq hb)
  have h3:2+(k+1) * 1≤2 * (s * 2 ^ P):=by
   have ha:2+(k+1) * 1≤2 * s:=by omega
   have hb:2 * s≤2 * s * 2 ^ P:=Nat.le_mul_of_pos_right _ hP1
   exact ha.trans (hb.trans (le_of_eq (Nat.mul_assoc 2 s (2 ^ P))))
  have h4:2+(32 * (2 ^ P+1) * (k+2)+(k+1) * 1)≤66 * (s * 2 ^ P):=by omega
  have h5:66 * (s * 2 ^ P)≤2 ^ 15 * (s ^ 22 * 2 ^ P):=by
   have h66:66≤2 ^ 15:=by decide
   exact Nat.mul_le_mul h66 (Nat.mul_le_mul_right (2 ^ P) hs22)
  have h6:2 ^ 15 * (s ^ 22 * 2 ^ P)≤2 ^ 15 * X2:=by
   have htmp:=Nat.le_mul_of_pos_right (2 ^ 15 * (s ^ 22 * 2 ^ P)) hH1
   have heq:2 ^ 15 * (s ^ 22 * 2 ^ P) * 2 ^ H=2 ^ 15 * X2:=by
    dsimp only [X2]
    calc 2 ^ 15 * (s ^ 22 * 2 ^ P) * 2 ^ H
     =2 ^ 15 * ((s ^ 22 * 2 ^ P) * 2 ^ H):=Nat.mul_assoc _ _ _
     _=2 ^ 15 * (s ^ 22 * (2 ^ P * 2 ^ H)):=by rw [Nat.mul_assoc (s ^ 22)]
     _=2 ^ 15 * (s ^ 22 * 2 ^ (P+H)):=by rw [hPH]
   exact htmp.trans (le_of_eq heq)
  exact h4.trans (h5.trans h6)
 have hdist:2 ^ 60 * s ^ 22 * ((2 * br) ^ P+2 ^ (P+H))=2 ^ 60 * X1+2 ^ 60 * X2:=by
  rw [Nat.mul_add]; dsimp only [X1,X2]; rw [Nat.mul_assoc,Nat.mul_assoc]
 rw [hdist]
 have hpow1:2 ^ 29≤2 ^ 60:=Nat.pow_le_pow_right (by omega) (by omega)
 have hpow2:2 ^ 15≤2 ^ 45:=Nat.pow_le_pow_right (by omega) (by omega)
 have hpow3:4 * 2 ^ 45≤2 ^ 60:=by
  have:4 * 2 ^ 45=2 ^ 47:=by
   change 2 ^ 2 * 2 ^ 45=2 ^ 47; rw [← pow_add]
  rw [this]; exact Nat.pow_le_pow_right (by omega) (by omega)
 have hle1:2 ^ 29 * X1≤2 ^ 60 * X1:=Nat.mul_le_mul_right X1 hpow1
 have hle2:2 ^ 15 * X2+2 ^ 15 * X2+2 ^ 45 * X2+2 ^ 15 * X2≤2 ^ 60 * X2:=by
  have hcoef:2 ^ 15+2 ^ 15+2 ^ 45+2 ^ 15≤4 * 2 ^ 45:=by
   have ha:2 ^ 15+2 ^ 15≤2 ^ 45+2 ^ 45:=Nat.add_le_add hpow2 hpow2
   have hb:2 ^ 45+2 ^ 15≤2 ^ 45+2 ^ 45:=Nat.add_le_add_left hpow2 _
   have hc:(2 ^ 45+2 ^ 45)+(2 ^ 45+2 ^ 45)=4 * 2 ^ 45:=by
    rw [← Nat.two_mul,← Nat.two_mul,← Nat.mul_assoc]
   calc 2 ^ 15+2 ^ 15+2 ^ 45+2 ^ 15
    =(2 ^ 15+2 ^ 15)+(2 ^ 45+2 ^ 15):=by rw [Nat.add_assoc]
    _≤(2 ^ 45+2 ^ 45)+(2 ^ 45+2 ^ 45):=Nat.add_le_add ha hb
    _=4 * 2 ^ 45:=hc
  have hmul:=Nat.mul_le_mul_right X2 (hcoef.trans hpow3)
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul] at hmul
  exact hmul
 have hL1:2+((2 * z9 k r t * 2 ^ 0 * (2 * br) ^ P-z9 k r t * 2 ^ 0) +
  (128 * (k+P+4) ^ 5 * 2 ^ 0+(128 * (k+k+4) ^ 5 * 2 ^ P +
    (2 ^ P * (2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H) +
      (32 * (2 ^ P+1) * (k+2)+(k+1) * 1)))))≤
  2 ^ 29 * X1+(2 ^ 15 * X2+2 ^ 15 * X2+2 ^ 45 * X2+2 ^ 15 * X2):=by
  have hA:=Nat.add_le_add hM4 hM5
  have hB:=Nat.add_le_add hM3 hA
  have hC:=Nat.add_le_add hM2 hB
  have hD:=Nat.add_le_add hM1 hC
  omega
 exact hL1.trans (Nat.add_le_add hle1 hle2)
theorem jK (k r t p h:ℕ) (hk:0<k)
 (watch:qI k) (side:Fin t→Bool) (site:Fin t→Fin k)
 (hc:closed hk watch (r+1)) (hw:∀ i,watch (side i) (r+1) (site i)=true):
 let P:=min k p
 let H:=min t h
 let br:=qC t P h
 let N:=InN k r t
 ∃ (C:Circuit) (flag:Fin (N+C.size))
   (maskWire:Fin P→Fin k→Fin (N+C.size))
   (ans:Fin (k+1)→Fin (N+C.size)),
   FanInTwo C∧ReadsBack N C∧C.output=flag.val∧
   C.size≤2 ^ 60 * (k+r+t+6) ^ 22 * ((2 * br) ^ P+2 ^ (P+H))∧
   ∀ (name:Bool→V k) (c:Bool→Fin (r+1)→V k) (target:V t),
     let x:=uh (v9 name c target)
     let wire:=fun i:Fin (N+C.size)=>(C.wires (List.ofFn x)).getD i.val false
     let chosen:=fun a b=>(if wire (maskWire a b) then 1 else 0:F)
     let count:=((Finset.univ:Finset (V k)).filter
      (fun key=>∀ i,probe hk name c side site i key=target i)).card
     (wire flag=true↔∃ Q:Fin P→V k,ze hk watch side site h name c Q)∧
     (wire flag=true→ze hk watch side site h name c chosen∧
       ∀ Q:Fin P→V k,ze hk watch side site h name c Q→
         Module.finrank F (Submodule.span F (Set.range chosen))≤
         Module.finrank F (Submodule.span F (Set.range Q)))∧
     (∀ i:Fin (k+1),wire (ans i)=((if wire flag then count else 0).testBit i.val)):=by
 classical
 intro P H br N
 have hPk:P≤k:=Nat.min_le_left k p
 let A0:Set (Sig N):=Set.range fun i:Fin N=>fun x:In N=>x i
 let A1:Set (Sig N):=A0 ∪ ({fun _=>false} ∪ {fun _=>true})
 have hInit:qa A0 A1 2:=qP (qr (k4 false) (k4 true))
 have hF1:(fun _=>false)∈A1:=Or.inr (Or.inl rfl)
 have hT1:(fun _=>true)∈A1:=Or.inr (Or.inr rfl)
 have hInMem (s:vP k r t):(fun x:In N=>z2b (ug x s))∈A1:=
  Or.inl ⟨kQ s,funext fun x=>(z0 (x (kQ s))).symm⟩
 let Q0:In N→Fin P→V k:=fun _ _ _=>0
 have hQ0Mem (i:Fin P) (j:Fin k):(fun x:In N=>z2b (Q0 x i j))∈A1:=by
  have heq:(fun x:In N=>z2b (Q0 x i j))=(fun _=>false):=by funext _; simp [Q0,qm]
  rw [heq]; exact hF1
 let rootRes:In N→qS P k:=
  qQ hk vX inC watch side site yl h P 0 (Nat.zero_add P) Q0
 have hSearch:=jz hPk hk vX inC watch side site yl h P 0 (Nat.zero_add P) Q0 A1
  hF1 hT1 (fun b j=>hInMem (vz b j)) (fun b n j=>hInMem (yu b n j))
  (fun u=>hInMem (v8 u)) hQ0Mem
 let rootFlag:Sig N:=fun x=>(rootRes x).1
 let rootQ:In N→Fin P→V k:=fun x=>(rootRes x).2.2
 let A2:=A1 ∪ qH rootRes
 have hF2:(fun _=>false)∈A2:=Or.inl hF1
 have hT2:(fun _=>true)∈A2:=Or.inl hT1
 have hRootFlag2:rootFlag∈A2:=Or.inr (Or.inl (Or.inl rfl))
 have hRootQ2 (a:Fin P) (j:Fin k):(fun x=>z2b (rootQ x a j))∈A2:=Or.inr (Or.inr ⟨a,j,rfl⟩)
 have hKer0:=j6 0 A2 hF2 hT2 rootQ hRootQ2
 let A3:=A2 ∪ ke 0 rootQ
 let chosenGen:In N→Fin k→V k:=fun x=>qb (rootQ x)
 have hGen3 (i j:Fin k):(fun x=>z2b (chosenGen x i j))∈A3:=
  Or.inr (Or.inl (Or.inl (Or.inr ⟨i,j,rfl⟩)))
 have hF3:(fun _=>false)∈A3:=Or.inl hF2
 have hT3:(fun _=>true)∈A3:=Or.inl hT2
 have hBank:=uD A3 hF3 hT3 p chosenGen hGen3
 let A4:=A3 ∪ jh p chosenGen
 let cGood:Sig N:=fun x=>yp p (chosenGen x)
 let cLive (i:Fin (2 ^ P)):Sig N:=fun x=>yq p (chosenGen x) i
 let cRep (i:Fin (2 ^ P)) (x:In N):V k:=zN p (chosenGen x) i
 let cQ (i:Fin (2 ^ P)) (x:In N) (u:Fin t):qc k:=
  kx hk vX inC (cRep i) chosenGen side site yl u x
 let cOK (i:Fin (2 ^ P)):Sig N:=fun x=>
  vE hk vX inC (cRep i) chosenGen watch x&&decide ((zm (cQ i x)).rank≤h)
 let cU (i:Fin (2 ^ P)) (j:Fin (k+1)):Sig N:=fun x=>yF h (chosenGen x) (cQ i x) j
 let cLocF (x:In N) (i:Fin (2 ^ P)):ℕ:=
  cosetCount (cRep i x) (chosenGen x) (probe hk (vX x) (inC x) side site) (yl x)
 have hRows:qa A4 (⋃ i:Fin (2 ^ P),({cOK i} ∪ Set.range (cU i)))
  (2 ^ P * (2 ^ 30 * (k+k+r+t+4) ^ 12 * 2 ^ H)):=by
  apply v7; intro i
  exact wc h hk vX inC (cRep i) chosenGen watch side site yl A4
   (Or.inl hF3) (Or.inl hT3)
   (fun b j=>Or.inl (Or.inl (Or.inl (hInMem (vz b j)))))
   (fun b n j=>Or.inl (Or.inl (Or.inl (hInMem (yu b n j)))))
   (fun j=>Or.inr (Or.inr ⟨i,j,rfl⟩))
   (fun a j=>Or.inl (hGen3 a j))
   (fun u=>Or.inl (Or.inl (Or.inl (hInMem (v8 u)))))
 let A5:=A4 ∪ ⋃ i:Fin (2 ^ P),({cOK i} ∪ Set.range (cU i))
 have hBankCond:∀ x,vf cGood cLive cOK x=true→∀ i,cLive i x=true→
  ∀ j,cU i j x=(cLocF x i).testBit j.val:=by
  intro x hx i hi j
  have hcond:=((kZ cGood cLive cOK x).mp hx).2 i hi
  simp only [cOK,Bool.and_eq_true,decide_eq_true_eq] at hcond
  exact local_bit hk (vX x) (inC x) (chosenGen x) (cRep i x) watch hc side site hw h (yl x)
   ((uo hk vX inC (cRep i) chosenGen watch x).mp hcond.1) hcond.2 j
 have hFinBank:=js (A:=A5) cGood cLive cOK cU cLocF
  (Or.inl (Or.inl hF3)) (Or.inl (Or.inl hT3))
  (Or.inl (Or.inr (Or.inl (Or.inl rfl))))
  (fun i=>Or.inl (Or.inr (Or.inl (Or.inr ⟨i,rfl⟩))))
  (fun i=>Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl rfl⟩))
  (fun i j=>Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inr ⟨j,rfl⟩⟩))
  hBankCond
 let rawSum (x:In N):ℕ:=
  if vf cGood cLive cOK x then ∑ i:Fin (2 ^ P),if cLive i x then cLocF x i else 0 else 0
 let ansSig (j:Fin (k+1)):Sig N:=fun x=>rootFlag x&&(rawSum x).testBit j.val
 let A6:=A5 ∪ ({vf cGood cLive cOK} ∪ Set.range (qk (k+1) rawSum))
 have hMaskAns:qa A6 (Set.range ansSig) ((k+1) * 1):=
  qf ansSig 1 (fun j=>qD (Or.inl (Or.inl (Or.inl (Or.inl hRootFlag2))))
   (Or.inr (Or.inr ⟨j,rfl⟩)))
 have hFull:=qo hInit (zd hSearch (qe hKer0 (qe hBank (qe hRows (qe hFinBank hMaskAns)))))
 have hBuild:qa A0 ({rootFlag} ∪ {f|∃ a j,(fun x=>z2b (rootQ x a j))=f} ∪ Set.range ansSig)
  (2 ^ 60 * (k+r+t+6) ^ 22 * ((2 * br) ^ P+2 ^ (P+H))):=by
  refine qd hFull le_rfl ?_ (uO k r t p h)
  rintro f ((rfl|⟨a,j,rfl⟩)|⟨i,rfl⟩)
  · exact Or.inr (Or.inl (Or.inl (Or.inl rfl)))
  · exact Or.inr (Or.inl (Or.inr ⟨a,j,rfl⟩))
  · exact Or.inr (Or.inr ⟨i,rfl⟩)
 obtain ⟨C,flag,maskWire,ans,hFT,hRB,hOut,hSz,hFl,hMk,hAn⟩:=
  uu (jE N) hBuild
 refine ⟨C,flag,maskWire,ans,hFT,hRB,hOut,hSz,?_⟩
 intro name c target x wire chosen count
 have hnm_x:vX x=name:=by funext b j; exact kj (v9 name c target) (vz b j)
 have hc_x:inC x=c:=by funext b n j; exact kj (v9 name c target) (yu b n j)
 have htar_x:yl x=target:=by funext i; exact kj (v9 name c target) (v8 i)
 have hFlx:wire flag=rootFlag x:=hFl x
 have hChx:chosen=rootQ x:=by
  funext a b
  dsimp only [chosen,wire]
  simp only [hMk a b x]
  exact vr _
 have hSound:=kn hk vX inC watch hc side site hw yl h P 0 (Nat.zero_add P) Q0 x
  (by
    have hz:Submodule.span F (Set.range (Q0 x))=⊥:=by
     rw [Submodule.span_eq_bot]; rintro _ ⟨_,rfl⟩; rfl
    rw [hz,finrank_bot])
  (fun _ _=>rfl)
 obtain ⟨dBest,_,hdBestP,heqBest,hBestOK⟩:=hSound
 have hIff:wire flag=true↔∃ Q:Fin P→V k,ze hk watch side site h name c Q:=by
  rw [hFlx]
  constructor
  · intro hok
    refine ⟨rootQ x,?_⟩
    have hw1:=(hBestOK hok).1
    rwa [hnm_x,hc_x] at hw1
  · rintro ⟨Qopt,hworks⟩
    have hw':ze hk watch side site h (vX x) (inC x) Qopt:=by rwa [hnm_x,hc_x]
    have hCpl:=yP hk vX inC watch hc side site hw yl h P 0 (Nat.zero_add P) Q0 x Qopt hw'
     (by
       have hz:Submodule.span F (Set.range (Q0 x))=⊥:=by
        rw [Submodule.span_eq_bot]; rintro _ ⟨_,rfl⟩; rfl
       rw [hz]; exact bot_le)
     (by
       have hz:Submodule.span F (Set.range (Q0 x))=⊥:=by
        rw [Submodule.span_eq_bot]; rintro _ ⟨_,rfl⟩; rfl
       rw [hz,finrank_bot])
     (fun _ _=>rfl)
    exact hCpl.1
 have hOpt:wire flag=true→ze hk watch side site h name c chosen∧
  ∀ Q:Fin P→V k,ze hk watch side site h name c Q→
    Module.finrank F (Submodule.span F (Set.range chosen))≤
    Module.finrank F (Submodule.span F (Set.range Q)):=by
  intro hok
  rw [hFlx] at hok
  rw [hChx]
  obtain ⟨hw1,hrk1⟩:=hBestOK hok
  rw [hnm_x,hc_x] at hw1
  refine ⟨hw1,fun Qopt hworks=>?_⟩
  have hw':ze hk watch side site h (vX x) (inC x) Qopt:=by rwa [hnm_x,hc_x]
  have hCpl:=yP hk vX inC watch hc side site hw yl h P 0 (Nat.zero_add P) Q0 x Qopt hw'
   (by
     have hz:Submodule.span F (Set.range (Q0 x))=⊥:=by
      rw [Submodule.span_eq_bot]; rintro _ ⟨_,rfl⟩; rfl
     rw [hz]; exact bot_le)
   (by
     have hz:Submodule.span F (Set.range (Q0 x))=⊥:=by
      rw [Submodule.span_eq_bot]; rintro _ ⟨_,rfl⟩; rfl
     rw [hz,finrank_bot])
   (fun _ _=>rfl)
  obtain ⟨_,dC,hdC_opt,hdCP,heqC⟩:=hCpl
  have hdEq:dBest=dC:=by
   have h1:=congrFun (heqBest.symm.trans heqC) ⟨dBest,by omega⟩
   simp at h1
   exact h1
  change Module.finrank F (Submodule.span F (Set.range (rootQ x)))≤dBest at hrk1
  exact hrk1.trans (hdEq▸hdC_opt)
 refine ⟨hIff,hOpt,fun i=>?_⟩
 have hAni:wire (ans i)=ansSig i x:=hAn i x
 rw [hAni]
 dsimp only [ansSig]
 cases hfl:rootFlag x
 · simp [hFlx,hfl]
 · simp only [hFlx,hfl,Bool.true_and,↓reduceIte]
   have hw_chosen:ze hk watch side site h (vX x) (inC x) (rootQ x):=(hBestOK hfl).1
   have hw_iff:=(ud hk watch hc side site hw h (vX x) (inC x) (yl x) (rootQ x)).mp hw_chosen
   have hcGood:cGood x=true:=by
    dsimp only [cGood,chosenGen]
    rw [jg]
    have hfr:=kF (rootQ x)
    have hP_le:Module.finrank F (Submodule.span F (Set.range (rootQ x)))≤P:=
     (hBestOK hfl).2.trans hdBestP
    have:k-Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (qb (rootQ x))))=
     Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (rootQ x))):=by
     change k-Module.finrank F (Submodule.span F (Set.range (qb (rootQ x))))=
      Module.finrank F (Submodule.span F (Set.range (rootQ x)))
     omega
    rw [this]
    exact hP_le.trans (Nat.min_le_right k p)
   have hbf:vf cGood cLive cOK x=true:=by
    rw [kZ]
    refine ⟨hcGood,fun idx hlive=>?_⟩
    have hlg:=(local_global hk (vX x) (inC x) (chosenGen x) (yq p (chosenGen x))
     (zN p (chosenGen x)) (kA p (chosenGen x) hcGood)
     watch hc side site hw h (yl x)).mpr hw_iff idx hlive
    simp only [cOK,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨(uo hk vX inC (cRep idx) chosenGen watch x).mpr hlg.1,hlg.2⟩
   have hsum_eq:rawSum x=count:=by
    dsimp only [rawSum,cLive,cLocF,cRep,count]
    rw [ite_eq_left hbf,hnm_x,hc_x,htar_x]
    apply jI (yq p (chosenGen x))
     (fun idx a=>a∈Set.range (key (zN p (chosenGen x) idx) (chosenGen x)))
     (fun a=>∀ j,probe hk name c side site j a=target j)
    simp only [mem_key_iff]
    exact kA p (chosenGen x) hcGood
   rw [hsum_eq]
end
end PEqualNP.Outside.L_meta_27129_aux
open PEqualNP.Outside.L_meta_27129_aux in
theorem PEqualNP.Outside.L_meta_27129 : ∀ (k r t p h : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-s % k))
  let gap := fun (b : Bool) => if b then 2 else 1
  let start := fun (b : Bool) => if b then 3 else 1
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let closed := fun (N : Nat) (watch : Bool → Nat → Fin k → Bool) =>
    ∀ (b : Bool) (t : Nat), t < N → ∀ j : Fin k, watch b (t+1) j = true →
      ∀ e : Fin 3, let i := ix (j.val+e.val)
        watch b t i = true ∧ watch b t (ix (i.val+gap b)) = true ∧
        watch b t (ix (i.val+k-gap b % k)) = true
  ∀ (watch : Bool → Nat → Fin k → Bool) (side : Fin t → Bool) (site : Fin t → Fin k),
    closed (r+1) watch → (∀ i, watch (side i) (r+1) (site i) = true) →
    let P := min k p
    let H := min t h
    let branch := if t ≤ h then 3 else
      max 3 (((2 : Nat)^(H+1)-1)*(2^(min P (H+1)+1)-1))
    let inputs := (2+2*(r+1))*k+t
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+C.size))
      (maskWire : Fin P → Fin k → Fin (inputs+C.size))
      (ans : Fin (k+1) → Fin (inputs+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.output = flag.val ∧
      C.size ≤ 2^60*(k+r+t+6)^22*((2*branch)^P + 2^(P+H)) ∧
      ∀ (name : Bool → W) (c : Bool → Fin (r+1) → W) (target : Fin t → F),
        let state := fun (b : Bool) (key : W) (n : Nat) =>
          ((List.finRange (r+1)).take n).foldl (fun z tick =>
            let y := fun i : Fin k =>
              z i + z (ix (i.val+gap b)) + z (ix (i.val+k-gap b % k))
            fun j : Fin k => y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
              rot (feed b tick.val) key j + c b tick j) (rot (start b) key + name b)
        let probe := fun (key : W) (i : Fin t) => state (side i) key (r+1) (site i)
        let works := fun (Q : Fin P → W) =>
          let D := {u : W // ∀ i, dotProduct (Q i) u = 0}
          let polar := fun (a : W) (i : Fin t) (xy : D × D) =>
            probe a i + probe (a+xy.1.val) i + probe (a+xy.2.val) i +
              probe (a+xy.1.val+xy.2.val) i
          (∀ (a : W) (b : Bool) (n : Nat), n ≤ r → ∀ j : Fin k, watch b n j = true →
            ∀ x y : D, state b a n j + state b (a+x.val) n j + state b (a+y.val) n j +
              state b (a+x.val+y.val) n j = 0) ∧
          (∀ a : W, Module.finrank F (Submodule.span F (Set.range (polar a))) ≤ h)
        let price := fun Q : Fin P → W => Module.finrank F (Submodule.span F (Set.range Q))
        let pack := fun w : W => List.ofFn (fun j : Fin k => decide (w j ≠ 0))
        let bits := pack (name false) ++ pack (name true) ++
          (List.ofFn (fun i => pack (c false i))).flatten ++
          (List.ofFn (fun i => pack (c true i))).flatten ++
          List.ofFn (fun i : Fin t => decide (target i ≠ 0))
        let wire := fun i : Fin (inputs+C.size) => (C.wires bits).getD i.val false
        let chosen := fun a b => (if wire (maskWire a b) then 1 else 0 : F)
        let count := ((Finset.univ : Finset W).filter (fun key => ∀ i, probe key i = target i)).card
        (wire flag = true ↔ ∃ Q : Fin P → W, works Q) ∧
          (wire flag = true → works chosen ∧ ∀ Q : Fin P → W, works Q → price chosen ≤ price Q) ∧
          (∀ i : Fin (k+1), wire (ans i) = ((if wire flag then count else 0).testBit i.val)) := by
  intro k r t p h hk F W ix rot gap start feed closed watch side site hc hw P H branch inputs
  obtain ⟨C,flag,maskWire,ans,hFT,hRB,hOut,hSz,hSpec⟩:=
   jK k r t p h hk watch side site hc hw
  refine ⟨C,flag,maskWire,ans,hFT,hRB,hOut,hSz,?_⟩
  intro name c target
  have h:=hSpec name c target
  dsimp only at h ⊢
  rw [← jk name c target]
  exact h
