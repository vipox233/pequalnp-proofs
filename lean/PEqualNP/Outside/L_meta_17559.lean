import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17559

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma J1{α}[DecidableEq α]{s t u:Finset α}{x:α}(h:x∈(s\t)∩u):x∈s:=(Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
lemma J2{α}[DecidableEq α]{s t u:Finset α}{x:α}(h:x∈(s\t)∩u):x∉t:=(Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).2
lemma I1{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s∩t):x∈s:=(Finset.mem_inter.mp h).1
lemma I2{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s∩t):x∈t:=(Finset.mem_inter.mp h).2
lemma Im{α}[DecidableEq α]{s t:Finset α}{x:α}(a:x∈s)(b:x∈t):x∈s∩t:=Finset.mem_inter.mpr ⟨a,b⟩
lemma D1{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s\t):x∈s:=(Finset.mem_sdiff.mp h).1
lemma D2{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s\t):x∉t:=(Finset.mem_sdiff.mp h).2
lemma Dm{α}[DecidableEq α]{s t:Finset α}{x:α}(a:x∈s)(b:x∉t):x∈s\t:=Finset.mem_sdiff.mpr ⟨a,b⟩
lemma Imp{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s∧x∈t):x∈s∩t:=Finset.mem_inter.mpr h
lemma Ip{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s∩t):x∈s∧x∈t:=Finset.mem_inter.mp h
lemma Dp{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s\t):x∈s∧x∉t:=Finset.mem_sdiff.mp h
lemma Fk{α}{s:Finset α}{p:α→Prop}[DecidablePred p]{x:α}(a:x∈s)(b:p x):x∈s.filter p:=Finset.mem_filter.mpr ⟨a,b⟩
lemma Fm{α}{s:Finset α}{p:α→Prop}[DecidablePred p]{x:α}(h:x∈s∧p x):x∈s.filter p:=Finset.mem_filter.mpr h
lemma Fp{α}{s:Finset α}{p:α→Prop}[DecidablePred p]{x:α}(h:x∈s.filter p):x∈s∧p x:=Finset.mem_filter.mp h
lemma Sp{α}{a b:α}(h:a∈({b}:Finset α)):a=b:=Finset.mem_singleton.mp h
lemma Sm{α}{a b:α}(h:a=b):a∈({b}:Finset α):=Finset.mem_singleton.mpr h
lemma Ss{α}(a:α):a∈({a}:Finset α):=Finset.mem_singleton_self a
lemma N0{α}{x:α}(h:x∈(∅:Finset α)):False:=Finset.notMem_empty x h
lemma Ns{α}{a b:α}(h:a≠b):a∉({b}:Finset α):=Finset.notMem_singleton.mpr h
lemma Ul{α}[DecidableEq α]{s:Finset α}(t:Finset α){x:α}(h:x∈s):x∈s∪t:=Finset.mem_union_left t h
lemma Ur{α}[DecidableEq α](s:Finset α){t:Finset α}{x:α}(h:x∈t):x∈s∪t:=Finset.mem_union_right s h
lemma Up{α}[DecidableEq α]{s t:Finset α}{x:α}(h:x∈s∪t):x∈s∨x∈t:=Finset.mem_union.mp h
lemma Uv{α}[Fintype α](x:α):x∈(Finset.univ:Finset α):=Finset.mem_univ x
lemma Fs{α}(p:α→Prop)[DecidablePred p](s:Finset α):s.filter p⊆s:=Finset.filter_subset p s
lemma Cl{α}{s t:Finset α}(h:s⊆t):s.card<=t.card:=Finset.card_le_card h
lemma Ir{α}[DecidableEq α]{s t:Finset α}:s∩t⊆t:=Finset.inter_subset_right
lemma Il{α}[DecidableEq α]{s t:Finset α}:s∩t⊆s:=Finset.inter_subset_left
lemma Ds{α}[DecidableEq α]{s t:Finset α}:s\t⊆s:=Finset.sdiff_subset
lemma Sr{α}(s:Finset α):s⊆s:=Finset.Subset.refl s
lemma Cs{α}(a:α):({a}:Finset α).card=1:=Finset.card_singleton a
lemma Ee{α}{s:Finset α}:s=∅↔∀x,x∉s:=Finset.eq_empty_iff_forall_notMem
lemma Eo{α}(s:Finset α):s=∅∨s.Nonempty:=s.eq_empty_or_nonempty
lemma Kc{α}{a:α}{l:List α}:a∈a::l:=List.mem_cons_self ..
lemma Km{α}(a:α){b:α}{l:List α}(h:b∈l):b∈a::l:=List.mem_cons_of_mem a h
lemma K2{α}{a b:α}{l:List α}:b∈a::b::l:=List.mem_cons_of_mem _ (List.mem_cons_self ..)
lemma Kp{α}{a b:α}{l:List α}(h:a∈b::l):a=b∨a∈l:=List.mem_cons.mp h
lemma Ks{α}(a:α):a∈[a]:=List.mem_singleton_self a
lemma Kl{α}{a b:α}:a∈[b]↔a=b:=List.mem_singleton
lemma Kal{α}{a:α}{l₁:List α}(l₂:List α)(h:a∈l₁):a∈l₁++l₂:=List.mem_append_left l₂ h
lemma Kar{α}{a:α}(l₁:List α){l₂:List α}(h:a∈l₂):a∈l₁++l₂:=List.mem_append_right l₁ h
lemma Kap{α}{a:α}{l₁ l₂:List α}(h:a∈l₁++l₂):a∈l₁∨a∈l₂:=List.mem_append.mp h
lemma Eg{V:Type*}[Fintype V]{G:SimpleGraph V}[DecidableRel G.Adj]{e:Sym2 V}(h:e∈G.edgeFinset):e∈G.edgeSet:=SimpleGraph.mem_edgeFinset.mp h
lemma Sw{α}{a b:α}:s(a,b)=s(b,a):=Sym2.eq_swap
lemma Sy2{α}{a b c d:α}(h:s(a,b)=s(c,d)):(a=c∧b=d)∨(a=d∧b=c):=Sym2.eq_iff.mp h
lemma Ql{a b:Prop}(h:a):a∨b:=Or.inl h
lemma Qr{a b:Prop}(h:b):a∨b:=Or.inr h
lemma Bf{α}[DecidableEq α]{a b:α}(h:a≠b):(a==b)=false:=beq_false_of_ne h
lemma Za{α}{l:List α}{p:α→Bool}(h:l.all p=true):∀x∈l,p x=true:=List.all_eq_true.mp h
lemma Nem{α}{s:Finset α}(h:s≠∅):s.Nonempty:=Finset.nonempty_iff_ne_empty.mpr h
lemma Nep{α}{s:Finset α}(h:s.Nonempty):s≠∅:=Finset.nonempty_iff_ne_empty.mp h
lemma Ism{α}[DecidableEq α]{a:α}{s t:Finset α}(h:a∈t∧s⊆t):insert a s⊆t:=Finset.insert_subset_iff.mpr h
lemma Nsp{α}[DecidableEq α]{a b:α}{s:Finset α}(h:a∈insert b s):a=b∨a∈s:=Finset.mem_insert.mp h
lemma Mi{α β}[DecidableEq β]{f:α→β}{s:Finset α}{b:β}(h:∃a∈s,f a=b):b∈s.image f:=Finset.mem_image.mpr h
lemma Mbu{α β}[DecidableEq β]{s:Finset α}{t:α→Finset β}{b:β}(h:∃a∈s,b∈t a):b∈s.biUnion t:=Finset.mem_biUnion.mpr h
lemma Cp{α}[DecidableEq α]{a b:α}(h:a≠b):({a,b}:Finset α).card=2:=Finset.card_pair h
lemma Ci{α β}[DecidableEq β]{f:α→β}{s:Finset α}:(s.image f).card<=s.card:=Finset.card_image_le
lemma Cu{α}[DecidableEq α](s t:Finset α):(s∪t).card<=s.card+t.card:=Finset.card_union_le s t
lemma Cns{α}[DecidableEq α]{a:α}{s:Finset α}(h:a∉s):(insert a s).card=s.card+1:=Finset.card_insert_of_notMem h
lemma Nss{α}{s t:Finset α}(h:¬s⊆t):∃x∈s,x∉t:=Finset.not_subset.mp h
lemma Cpr{α}{s:Finset α}(h:s.Nonempty):0<s.card:=Finset.card_pos.mpr h
lemma Bup{α β}[DecidableEq β]{s:Finset α}{t:α→Finset β}{b:β}(h:b∈s.biUnion t):∃a∈s,b∈t a:=Finset.mem_biUnion.mp h
lemma Us2{α}[DecidableEq α]{s t u:Finset α}(h1:s⊆u)(h2:t⊆u):s∪t⊆u:=Finset.union_subset h1 h2
lemma Mip{α β}[DecidableEq β]{f:α→β}{s:Finset α}{b:β}(h:b∈s.image f):∃a∈s,f a=b:=Finset.mem_image.mp h
lemma Sls{ι α}[AddCommMonoid α][PartialOrder α][IsOrderedAddMonoid α]{s:Finset ι}{f g:ι→α}(h:∀i∈s,f i<=g i):∑i∈s,f i<=∑i∈s,g i:=Finset.sum_le_sum h
lemma Mtf{α}[DecidableEq α]{l:List α}{a:α}(h:a∈l):a∈l.toFinset:=List.mem_toFinset.mpr h
lemma Nlt{a b:ℕ}(h:a<b):a≠b:=Nat.ne_of_lt h
lemma Lmc{α β}{f:α→β}{a:α}{l:List α}:(a::l).map f=f a::l.map f:=List.map_cons
lemma Lsc{α}[AddMonoid α]{a:α}{l:List α}:(a::l).sum=a+l.sum:=List.sum_cons
lemma Lmn{α β}{f:α→β}:([] : List α).map f=[]:=List.map_nil
lemma Lsn{α}[AddMonoid α]:([] : List α).sum=0:=List.sum_nil
lemma LqA{α β}{f:α→β}{l₁ l₂:List α}:(l₁++l₂).map f=l₁.map f++l₂.map f:=List.map_append
lemma LqS{α}[AddMonoid α]{l₁ l₂:List α}:(l₁++l₂).sum=l₁.sum+l₂.sum:=List.sum_append
lemma Cud{α}[DecidableEq α]{s t:Finset α}(h:Disjoint s t):(s∪t).card=s.card+t.card:=Finset.card_union_of_disjoint h
lemma Nne{α}:¬(∅:Finset α).Nonempty:=Finset.not_nonempty_empty
lemma Bub{α β}[DecidableEq β]{s₁ s₂:Finset α}(t:α→Finset β)(h:s₁⊆s₂):s₁.biUnion t⊆s₂.biUnion t:=Finset.biUnion_subset_biUnion_of_subset_left t h
lemma Csd{α}[DecidableEq α]{s t:Finset α}(h:s⊆t):(t\s).card+s.card=t.card:=Finset.card_sdiff_add_card_eq_card h
lemma Cui{α}[DecidableEq α](s t:Finset α):(s∪t).card+(s∩t).card=s.card+t.card:=Finset.card_union_add_card_inter s t
lemma Ceo{α}[DecidableEq α]{a:α}{s:Finset α}(h:a∈s):(s.erase a).card+1=s.card:=Finset.card_erase_add_one h
lemma Sul{α}[DecidableEq α]{s t:Finset α}:s⊆s∪t:=Finset.subset_union_left
lemma Sur{α}[DecidableEq α]{s t:Finset α}:t⊆s∪t:=Finset.subset_union_right
lemma Sbu{α β}[DecidableEq β]{a:α}{t:α→Finset β}:({a}:Finset α).biUnion t=t a:=Finset.singleton_biUnion
lemma Cil{α}[DecidableEq α](a:α)(s:Finset α):(insert a s).card<=s.card+1:=Finset.card_insert_le a s
lemma Lgd{α}(l:List α)(i:ℕ)(d:α):l.getD i d=(l[i]?).getD d:=List.getD_eq_getElem?_getD
lemma Rr{α}{r:α→α→Prop}{a:α}:Relation.ReflTransGen r a a:=Relation.ReflTransGen.refl
lemma A2l{a b:ℕ}(h:a<=b)(c:ℕ):c+a<=c+b:=Nat.add_le_add_left h c
lemma Isi{α}[DecidableEq α]{s₁ s₂ t₁ t₂:Finset α}(h1:s₁⊆t₁)(h2:s₂⊆t₂):s₁∩s₂⊆t₁∩t₂:=Finset.inter_subset_inter h1 h2
lemma Cbu{α β}[DecidableEq β]{s:Finset α}{t:α→Finset β}:(s.biUnion t).card<=∑x∈s,(t x).card:=Finset.card_biUnion_le
lemma Nne2{α}{s:Finset α}(h:¬s.Nonempty):s=∅:=Finset.not_nonempty_iff_eq_empty.mp h
abbrev Pi:=@pairInput
abbrev Ck:=Circuit
def QQ (w:List Bool)(g:Gate):List Bool:=
 w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma Xw (C:Ck)(x:List Bool): C.wires x=C.gates.foldl QQ x:=rfl
lemma WP (gs:List Gate)(w:List Bool): (gs.foldl QQ w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
  rw[List.foldl_cons,ih];simp[QQ];omega
lemma ZB (gs:List Gate)(w:List Bool)(i:ℕ)(j:i < w.length): (gs.foldl QQ w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  simp only[List.foldl_cons];have h:i < (QQ w g).length:=by simp[QQ];omega
  rw[ih (QQ w g) h];simp[QQ,Lgd,List.getElem?_append_left j]
lemma Bg (w:List Bool)(i:ℕ)(g:w.length<=i):w.getD i false=false:=by simp[Lgd,List.getElem?_eq_none g]
lemma W6 (gs:List Gate)(w:List Bool)(j:ℕ)(t:j < gs.length): (gs.foldl QQ w).getD (w.length+j) false= (gs[j]).op.eval ((gs[j]).inputs.map fun i=>
    if i < w.length+j then (gs.foldl QQ w).getD i false else false):=by
 induction gs generalizing w j with
 | nil=>simp at t
 | cons g gs ih=>
  rw[List.foldl_cons]
  cases j with
  | zero=>
   have z:w.length < (QQ w g).length:=by simp[QQ]
   rw[Nat.add_zero,ZB gs (QQ w g) w.length z];simp only[List.getElem_cons_zero]
   have h2:(QQ w g).getD w.length false=
     g.op.eval (g.inputs.map fun i=>w.getD i false):=by
    simp[QQ,Lgd]
   rw[h2]
   congr 1
   apply List.map_congr_left
   intro i _
   by_cases q:i < w.length
   ·rw[ite_eq_left q,ZB gs (QQ w g) i (by simp[QQ];omega)]
    simp[QQ,Lgd,List.getElem?_append_left q]
   ·rw[ite_eq_right q];exact Bg w i (by omega)
  | succ j=>
   have hj':j < gs.length:=by simpa using t
   have h:=ih (QQ w g) j hj';have hl:(QQ w g).length=w.length+1:=by simp[QQ]
   rw[hl] at h;have e:w.length+(j+1)=w.length+1+j:=by omega
   simp only[List.getElem_cons_succ];rw[e];exact h
def val (C:Ck)(x:List Bool)(u:ℕ):Bool:=(C.wires x).getD u false
lemma YC {C:Ck}{j:ℕ}(g:j < C.gates.length):gateAt C j=C.gates[j]:=by simp[gateAt,Lgd,g]
lemma YH {C:Ck}{j:ℕ}(g:j < C.gates.length):gateAt C j∈C.gates:=by rw[YC g];exact List.getElem_mem g
lemma Vg {n:ℕ}{C:Ck}{x:List Bool}(hx:x.length=n){u:ℕ}(hu:u < n): val C x u=x.getD u false:=by unfold val;rw[Xw];exact ZB _ _ _ (by omega)
lemma WR {n:ℕ}{C:Ck}{x:List Bool}(hx:x.length=n){u:ℕ}(hu:n+C.gates.length<=u):val C x u=false:=by unfold val;apply Bg;rw[Xw,WP];omega
lemma XX {n:ℕ}{C:Ck}{x:List Bool}(h:x.length=n){j:ℕ}(g:j < C.gates.length): val C x (n+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map fun i=>
   if i < n+j then val C x i else false):=by
 subst h;rw[YC g];exact W6 C.gates x j g
lemma BH {n:ℕ}{C:Ck}{x:List Bool}(q:x.length=n){r:ℕ}(hr:r < C.gates.length)(j:(gateAt C r).op=GateOp.or): val C x (n+r)=true↔∃i∈(gateAt C r).inputs,i < n+r/\val C x i=true:=by
 rw[XX q hr,j];simp only[GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
 constructor
 ·rintro⟨i,hi,h⟩
  by_cases g:i < n+r
  ·rw[ite_eq_left g] at h;exact⟨i,hi,g,h⟩
  ·rw[ite_eq_right g] at h;cases h
 ·rintro⟨i,hi,g,h⟩
  exact⟨i,hi,by rw[ite_eq_left g];exact h⟩
lemma Pe {n:ℕ}{C:Ck}{x:List Bool}(t:x.length=n){r:ℕ}(hr:r < C.gates.length)(q:(gateAt C r).op=GateOp.and): val C x (n+r)=true↔∀i∈(gateAt C r).inputs,i < n+r/\val C x i=true:=by
 rw[XX t hr,q];simp only[GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
 constructor
 ·intro h i j
  have h':=h i j
  by_cases g:i < n+r
  ·rw[ite_eq_left g] at h';exact⟨g,h'⟩
  ·rw[ite_eq_right g] at h';cases h'
 ·intro h i j;rw[ite_eq_left (h i j).1];exact(h i j).2
lemma VN {n:ℕ}(C:Ck)(x:Fin n->Bool)(u:Fin n): val C (List.ofFn x) u.val=x u:=by
 rw[Vg (n:=n) (by simp) u.isLt]
 simp[Lgd]
lemma Xy (n:ℕ)(C:Ck)(j:ℕ)(x:Fin n->Bool): gateVal n C j x=val C (List.ofFn x) (n+j):=rfl
def Kx (n:ℕ)(C:Ck)(w w':ℕ):Prop:=
 ∃k,k < C.gates.length/\w=n+k/\(gateAt C k).op=GateOp.or /\
  w'∈(gateAt C k).inputs/\w' < n+k
lemma Vc {n:ℕ}{C:Ck}{x:List Bool}(z:x.length=n){w t:ℕ}(h:Relation.ReflTransGen (Kx n C) w t)(hv:val C x t=true): val C x w=true:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>exact hv
 | head hstep _ ih=>
  obtain⟨k,hk,rfl,q,g,j⟩:=hstep;exact(BH z hk q).mpr ⟨_,g,j,ih⟩
lemma WX {n:ℕ}{C:Ck}{x:List Bool}(hx:x.length=n): ∀w:ℕ,val C x w=true -> ∃g,Relation.ReflTransGen (Kx n C) w g/\val C x g=true /\ (g < n\/∃h,h < C.gates.length/\g=n+h/\(gateAt C h).op≠GateOp.or):=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro hv
  by_cases hw:w < n
  ·exact⟨w,Rr,hv,Ql hw⟩
  ·by_cases t:n+C.gates.length<=w
   ·rw[WR hx t] at hv;cases hv
   ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩
    have z:k < C.gates.length:=by omega
    by_cases j:(gateAt C k).op=GateOp.or
    ·obtain⟨i,a4,q,hi⟩:=(BH hx z j).mp hv
     have⟨g,hr,a5,a3⟩:=ih i q hi
     exact⟨g,Relation.ReflTransGen.head ⟨k,z,rfl,j,a4,q⟩ hr,a5,a3⟩
    ·exact⟨n+k,Rr,hv,Qr ⟨k,z,rfl,j⟩⟩
lemma Q8 {n:ℕ}(u v:Fin n):pairInput u v u=true:=by simp[pairInput]
lemma Qq {n:ℕ}(u v:Fin n):pairInput u v v=true:=by simp[pairInput]
lemma K4 {n:ℕ}(u v w:Fin n):Pi u v w=true↔w=u\/w=v:=by simp[pairInput]
lemma Qx {n:ℕ}(G:SimpleGraph (Fin n))[DecidableRel G.Adj](u v:Fin n): graphFun G ∅ (Pi u v)=true↔G.Adj u v:=by
 simp only[graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
  Bool.false_or,decide_eq_true_eq,K4]
 constructor
 ·rintro⟨a,b,hab,ha,hb⟩
  rcases ha with rfl|rfl<;>rcases hb with rfl|rfl
  ·exact(G.irrefl hab).elim
  ·exact hab
  ·exact hab.symm
  ·exact(G.irrefl hab).elim
 ·intro h;exact⟨u,v,h,Ql rfl,Qr rfl⟩
lemma V2 {n:ℕ}{C:Ck}(u v:Fin n)(p:ℕ)(hv:val C (List.ofFn (Pi u v)) p=true): (∃t:Fin n,(t=u\/t=v)/\Relation.ReflTransGen (Kx n C) p t.val)\/ (∃h,h < C.gates.length/\(gateAt C h).op≠GateOp.or /\ Relation.ReflTransGen (Kx n C) p (n+h) /\ val C (List.ofFn (Pi u v)) (n+h)=true):=by
 have⟨j,hr,q,z⟩:=WX (n:=n) (C:=C) (x:=List.ofFn (Pi u v))
  (by simp) p hv
 rcases z with g|⟨h,hh,rfl,a3⟩
 ·left
  refine⟨⟨j,g⟩,?_,hr⟩
  have h1:=VN C (Pi u v) ⟨j,g⟩;rw[show (⟨j,g⟩:Fin n).val=j from rfl,q] at h1
  exact(K4 u v _).mp h1.symm
 ·right
  exact⟨h,hh,a3,hr,q⟩
lemma YR {n:ℕ}{C:Ck}(x:Fin n->Bool)(p:ℕ)(t:Fin n)(hr:Relation.ReflTransGen (Kx n C) p t.val)(ht:x t=true): val C (List.ofFn x) p=true:=
 Vc (n:=n) (by simp) hr (by rw[VN];exact ht)
lemma Bw {n:ℕ}(G:SimpleGraph (Fin n)){C:Ck}(F:(Fin n->Bool)->Bool)(z:∀u v:Fin n,F (Pi u v)=true->G.Adj u v)(g:∀x:Fin n->Bool,val C (List.ofFn x) C.output=F x)(u v:Fin n)(q:F (Pi u v)=true): ∃a,a < C.gates.length/\(gateAt C a).op≠GateOp.or /\ Relation.ReflTransGen (Kx n C) C.output (n+a) /\ val C (List.ofFn (Pi u v)) (n+a)=true:=by
 rcases V2 (C:=C) u v C.output (by rw[g];exact q) with
  ⟨t,_,hr⟩|h
 ·exfalso
  have j:=YR (Pi t t) _ t hr (Q8 t t);rw[g] at j
  exact G.irrefl (z t t j)
 ·exact h
lemma Wd {n:ℕ}{C:Ck}(F:(Fin n->Bool)->Bool)(g:∀x:Fin n->Bool,val C (List.ofFn x) C.output=F x)(a:ℕ)(hr:Relation.ReflTransGen (Kx n C) C.output (n+a))(x:Fin n->Bool)(hv:val C (List.ofFn x) (n+a)=true):F x=true:=by rw[←g];exact Vc (n:=n) (by simp) hr hv
lemma BB (n:ℕ)(gs:List Gate)(cs:List (List ℕ)): (gs.foldl (coneStep n) cs).length=cs.length+gs.length:=by
 induction gs generalizing cs with
 | nil=>simp
 | cons g gs ih=>
  rw[List.foldl_cons,ih];simp[coneStep];omega
lemma Bx (n:ℕ)(gs:List Gate): ∀i j,i∈(gs.foldl (coneStep n) []).getD j []↔ j < gs.length/\∃w∈(gs.getD j ⟨GateOp.or,[]⟩).inputs,n<=w/\w < n+j /\ (i=w-n\/i∈(gs.foldl (coneStep n) []).getD (w-n) []):=by
 induction gs using List.reverseRecOn with
 | nil=>intro i j;simp
 | append_singleton gs g ih=>
  intro i j;rw[List.foldl_append,List.foldl_cons,List.foldl_nil]
  have t:(gs.foldl (coneStep n) []).length=gs.length:=by rw[BB];simp
  have q:∀k,k < gs.length ->
    (coneStep n (gs.foldl (coneStep n) []) g).getD k []=
     (gs.foldl (coneStep n) []).getD k []:=by
   intro k hk;simp only[coneStep,Lgd];rw[List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h|h|h
  ·have e1:(gs++[g]).getD j ⟨GateOp.or,[]⟩=gs.getD j ⟨GateOp.or,[]⟩:=by
    simp only[Lgd];rw[List.getElem?_append_left h]
   rw[q j h,ih i j,e1]
   constructor
   ·rintro⟨_,w,hw,h1,h2,h3⟩
    refine⟨by simp;omega,w,hw,h1,h2,?_⟩
    rw[q (w-n) (by omega)]
    exact h3
   ·rintro⟨_,w,hw,h1,h2,h3⟩
    refine⟨h,w,hw,h1,h2,?_⟩
    rw[q (w-n) (by omega)] at h3
    exact h3
  ·subst h
   have e1:(gs++[g]).getD gs.length ⟨GateOp.or,[]⟩=g:=by simp[Lgd]
   have z:(coneStep n (gs.foldl (coneStep n) []) g).getD gs.length []=
     (g.inputs.filter (fun w=>decide (n<=w/\w < n+gs.length))).flatMap
      (fun w=>(w-n)::(gs.foldl (coneStep n) []).getD (w-n) []):=by
    simp only[coneStep,Lgd];rw[List.getElem?_append_right (by omega)]
    simp[t]
   rw[z,e1];simp only[List.mem_flatMap,List.mem_filter,List.mem_cons,decide_eq_true_eq]
   constructor
   ·rintro⟨w,⟨hw,h1,h2⟩,h3⟩
    refine⟨by simp,w,hw,h1,h2,?_⟩
    rw[q (w-n) (by omega)]
    exact h3
   ·rintro⟨_,w,hw,h1,h2,h3⟩
    rw[q (w-n) (by omega)] at h3
    exact⟨w,⟨hw,h1,h2⟩,h3⟩
  ·have e0:(coneStep n (gs.foldl (coneStep n) []) g).getD j []=[]:=by
    simp only[coneStep,Lgd];rw[List.getElem?_eq_none (by simp;omega)]
    rfl
   rw[e0]
   constructor
   ·intro h0;simp at h0
   ·rintro⟨h0,_⟩
    simp at h0;omega
lemma KB (n:ℕ)(C:Ck)(i j:ℕ): InCone n C i j↔j < C.gates.length/\∃k,k < j/\n+k∈(gateAt C j).inputs /\ (i=k\/InCone n C i k):=by
 have h:=Bx n C.gates i j;unfold InCone cones gateAt;rw[h]
 constructor
 ·rintro⟨h0,w,hw,h1,h2,h3⟩
  refine⟨h0,w-n,by omega,?_,h3⟩
  have:n+(w-n)=w:=by omega
  rw[this];exact hw
 ·rintro⟨h0,k,hk,hw,h3⟩
  refine⟨h0,n+k,hw,by omega,by omega,?_⟩
  have:n+k-n=k:=by omega
  rw[this];exact h3
lemma Y4 {n:ℕ}{C:Ck}{i j:ℕ}(h:InCone n C i j):i < j:=by
 induction j using Nat.strong_induction_on with
 | _ j ih=>
  obtain⟨_,k,g,_,rfl|q⟩:=(KB n C i j).mp h
  ·exact g
  ·exact(ih k g q).trans g
lemma WV {n:ℕ}{C:Ck}{i j k:ℕ}(t:InCone n C i j)(q:InCone n C j k):InCone n C i k:=by
 induction k using Nat.strong_induction_on with
 | _ k ih=>
  obtain⟨hk,m,g,h,a4|z⟩:=(KB n C j k).mp q
  ·subst a4
   exact(KB n C i k).mpr ⟨hk,j,g,h,Qr t⟩
  ·exact(KB n C i k).mpr ⟨hk,m,g,h,Qr (ih m g z)⟩
lemma Zv {n:ℕ}{C:Ck}{w g:ℕ}(h:Relation.ReflTransGen (Kx n C) w g):g<=w:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>exact le_rfl
 | head hstep _ ih=>
  obtain⟨k,_,rfl,_,_,j⟩:=hstep;omega
lemma B7 {n:ℕ}{C:Ck}{w z:ℕ}(h:Relation.ReflTransGen (Kx n C) w z): ∀k g,w=n+k->z=n+g->g=k\/InCone n C g k:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>intro k g h1 t;left;omega
 | @head a c hstep hrest ih=>
  intro k g h1 t;obtain⟨k0,q,e,_,j,a6⟩:=hstep;have hk:k0=k:=by omega
  subst hk;have a7:=Zv hrest;obtain⟨k1,hk1⟩:∃k1,c=n+k1:=⟨c-n,by omega⟩;subst hk1;right;rw[KB];exact⟨q,k1,by omega,j,ih k1 g rfl t⟩
lemma WW {n:ℕ}{C:Ck}{a p h:ℕ}(ha:a < C.gates.length)(g:p∈(gateAt C a).inputs)(hp:p < n+a)(hr:Relation.ReflTransGen (Kx n C) p (n+h)):InCone n C h a:=by have j:=Zv hr;obtain⟨k1,rfl⟩:∃k1,p=n+k1:=⟨p-n,by omega⟩;rw[KB];exact⟨ha,k1,by omega,g,B7 hr k1 h rfl rfl⟩
lemma Bs (n:ℕ)(gs:List Gate)(cs:List (List ℕ)): (gs.foldl (orStep n) cs).length=cs.length+gs.length:=by
 induction gs generalizing cs with
 | nil=>simp
 | cons g gs ih=>
  rw[List.foldl_cons,ih];simp[orStep];omega
lemma B9 (n:ℕ)(gs:List Gate): ∀i j,i∈(gs.foldl (orStep n) []).getD j []↔ j < gs.length/\(i=j\/((gs.getD j ⟨GateOp.or,[]⟩).op=GateOp.or /\ ∃w∈(gs.getD j ⟨GateOp.or,[]⟩).inputs,n<=w/\w < n+j /\ i∈(gs.foldl (orStep n) []).getD (w-n) [])):=by
 induction gs using List.reverseRecOn with
 | nil=>intro i j;simp
 | append_singleton gs g ih=>
  intro i j;rw[List.foldl_append,List.foldl_cons,List.foldl_nil]
  have a5:(gs.foldl (orStep n) []).length=gs.length:=by rw[Bs];simp
  have z:∀k,k < gs.length ->
    (orStep n (gs.foldl (orStep n) []) g).getD k []=
     (gs.foldl (orStep n) []).getD k []:=by
   intro k hk;simp only[orStep,Lgd];rw[List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h|h|h
  ·have e1:(gs++[g]).getD j ⟨GateOp.or,[]⟩=gs.getD j ⟨GateOp.or,[]⟩:=by
    simp only[Lgd];rw[List.getElem?_append_left h]
   rw[z j h,ih i j,e1]
   constructor
   ·rintro⟨_,q⟩
    refine⟨by simp;omega,?_⟩
    rcases q with q|⟨t,w,hw,h1,h2,q⟩
    ·exact Ql q
    ·refine Qr ⟨t,w,hw,h1,h2,?_⟩
     rw[z (w-n) (by omega)]
     exact q
   ·rintro⟨_,q⟩
    refine⟨h,?_⟩
    rcases q with q|⟨t,w,hw,h1,h2,q⟩
    ·exact Ql q
    ·rw[z (w-n) (by omega)] at q
     exact Qr ⟨t,w,hw,h1,h2,q⟩
  ·subst h
   have e1:(gs++[g]).getD gs.length ⟨GateOp.or,[]⟩=g:=by simp[Lgd]
   rw[e1]
   by_cases t:g.op=GateOp.or
   ·have e2:(orStep n (gs.foldl (orStep n) []) g).getD gs.length []=
      gs.length::(g.inputs.filter (fun w=>decide (n<=w/\w < n+gs.length))).flatMap
       (fun w=>(gs.foldl (orStep n) []).getD (w-n) []):=by
     simp only[orStep,Lgd];rw[List.getElem?_append_right (by omega)]
     simp[a5,t]
    rw[e2];simp only[List.mem_cons,List.mem_flatMap,List.mem_filter,decide_eq_true_eq]
    constructor
    ·rintro (q|⟨w,⟨hw,h1,h2⟩,q⟩)
     ·exact⟨by simp,Ql q⟩
     ·refine⟨by simp,Qr ⟨t,w,hw,h1,h2,?_⟩⟩
      rw[z (w-n) (by omega)]
      exact q
    ·rintro⟨_,q|⟨_,w,hw,h1,h2,q⟩⟩
     ·exact Ql q
     ·rw[z (w-n) (by omega)] at q
      exact Qr ⟨w,⟨hw,h1,h2⟩,q⟩
   ·have e2:(orStep n (gs.foldl (orStep n) []) g).getD gs.length []=[gs.length]:=by
     simp only[orStep,Lgd];rw[List.getElem?_append_right (by omega)]
     simp[a5,t]
    rw[e2];simp only[Kl]
    constructor
    ·intro q
     exact⟨by simp,Ql q⟩
    ·rintro⟨_,q|⟨hop2,_⟩⟩
     ·exact q
     ·exact(t hop2).elim
  ·have e0:(orStep n (gs.foldl (orStep n) []) g).getD j []=[]:=by
    simp only[orStep,Lgd];rw[List.getElem?_eq_none (by simp;omega)]
    rfl
   rw[e0]
   constructor
   ·intro h0;simp at h0
   ·rintro⟨h0,_⟩
    simp at h0;omega
lemma QT (n:ℕ)(C:Ck)(k g:ℕ): OrReaches n C (n+k) g↔k < C.gates.length/\(g=k\/((gateAt C k).op=GateOp.or /\ ∃i∈(gateAt C k).inputs,i < n+k/\OrReaches n C i g)):=by
 have h:=B9 n C.gates g k;unfold OrReaches orSets gateAt;have e:n+k-n=k:=by omega
 rw[e,h]
 constructor
 ·rintro⟨_,hk,j⟩
  refine⟨hk,?_⟩
  rcases j with j|⟨q,w,hw,z,t,j⟩
  ·exact Ql j
  ·exact Qr ⟨q,w,hw,t,z,j⟩
 ·rintro⟨hk,j⟩
  refine⟨by omega,hk,?_⟩
  rcases j with j|⟨q,w,hw,t,z,j⟩
  ·exact Ql j
  ·exact Qr ⟨q,w,hw,z,t,j⟩
lemma Ke {n:ℕ}{C:Ck}{w t:ℕ}(h:Relation.ReflTransGen (Kx n C) w t): ∀g,t=n+g->g < C.gates.length->OrReaches n C w g:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>
  intro g j q;subst j
  exact(QT n C g g).mpr ⟨q,Ql rfl⟩
 | @head a c hstep hrest ih=>
  intro g j q;obtain⟨k,hk,rfl,a4,z,a3⟩:=hstep;exact(QT n C k g).mpr ⟨hk,Qr ⟨a4,c,z,a3,ih g j q⟩⟩
lemma Qz {n:ℕ}{C:Ck}(g:ℕ): ∀w,OrReaches n C w g -> Relation.ReflTransGen (Kx n C) w (n+g)/\g < C.gates.length:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro h;have a6:n<=w:=h.1;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;obtain⟨z,h3⟩:=(QT n C k g).mp h
  rcases h3 with rfl|⟨t,i,hi,j,hr⟩
  ·exact⟨Rr,z⟩
  ·have⟨q,hg⟩:=ih i j hr;exact⟨Relation.ReflTransGen.head ⟨k,z,rfl,t,hi,j⟩ q,hg⟩
lemma QH {n:ℕ}{C:Ck}{w g h:ℕ}(q:OrReaches n C w g)(j:OrReaches n C (n+g) h):OrReaches n C w h:=
 Ke ((Qz g w q).1.trans (Qz h (n+g) j).1)
  h rfl (Qz h (n+g) j).2
lemma Kh {n:ℕ}{C:Ck}{p:ℕ}(u:Fin n)(q:u∈orIn n C p):Relation.ReflTransGen (Kx n C) p u.val:=by
 simp only[orIn,Finset.mem_filter,Uv,true_and] at q
 rcases q with h|⟨k,t,hr,g,j⟩
 ·rw[h]
 ·exact(Qz k p hr).1.tail ⟨k,t,rfl,g,j,by omega⟩
lemma Kb {n:ℕ}{C:Ck}{p:ℕ}(u:Fin n)(hr:Relation.ReflTransGen (Kx n C) p u.val):u∈orIn n C p:=by
 simp only[orIn,Finset.mem_filter,Uv,true_and]
 rcases Relation.ReflTransGen.cases_tail hr with h|⟨c,j,g⟩
 ·exact Ql h
 ·obtain⟨k,z,rfl,t,q,_⟩:=g;exact Qr ⟨k,z,Ke j k rfl z,t,q⟩
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Ck}
lemma Vr {a:ℕ}(ha:a∈tops G C): a < C.gates.length/\(gateAt C a).op=GateOp.and/\BelowF G C a:=by simpa only[tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using ha
lemma Q6 {a:ℕ}(ha:a∈junk G C): a < C.gates.length/\(gateAt C a).op=GateOp.and /\ ∃x:Fin n->Bool,gateVal n C a x=true/\graphFun G ∅ x=false:=by
 rcases Fp ha with⟨_,g,h,j⟩
 exact⟨h,g,j⟩
lemma Vb (hAO:IsAO2 n C){a:ℕ}(ha:a < C.gates.length): ∃p q,(gateAt C a).inputs=[p,q]:=
 List.length_eq_two.mp (hAO.2.2 _ (YH ha))
lemma Zh (h:IsAO2 n C){a:ℕ}(ha:a < C.gates.length)(b:Fin 2): opnd C a b∈(gateAt C a).inputs:=by
 have⟨p,q,g⟩:=Vb h ha
 fin_cases b<;>simp[opnd,g]
lemma Ku (hAO:IsAO2 n C){a:ℕ}(ha:a < C.gates.length)(b:Fin 2): opnd C a b < n+a:=
 hAO.2.1 a ha _ (Zh hAO ha b)
lemma KM (h:IsAO2 n C){m z:ℕ}(hm:m < C.gates.length)(t:z∈(gateAt C m).inputs):∃b:Fin 2,z=opnd C m b:=by
 have⟨p,q,g⟩:=Vb h hm
 rcases Kp (g▸t) with rfl|j
 ·exact⟨0,by simp[opnd,g]⟩
 ·exact⟨1,by simp[opnd,g,Kl.mp j]⟩
lemma Yk (hAO:IsAO2 n C){a:ℕ}(ha:a < C.gates.length)(g:(gateAt C a).op=GateOp.and)(x:Fin n->Bool): gateVal n C a x=true↔ val C (List.ofFn x) (opnd C a 0)=true /\ val C (List.ofFn x) (opnd C a 1)=true:=by
 rw[Xy,Pe (n:=n) (by simp) ha g]
 constructor
 ·intro h
  exact⟨(h _ (Zh hAO ha 0)).2,(h _ (Zh hAO ha 1)).2⟩
 ·intro h i j
  refine⟨hAO.2.1 a ha i j,?_⟩
  obtain⟨b,rfl⟩:=KM hAO ha j
  fin_cases b
  ·exact h.1
  ·exact h.2
lemma QF (j:IsAO2 n C){a:ℕ}(ha:a < C.gates.length)(g:(gateAt C a).op=GateOp.and)(x:Fin n->Bool): gateVal n C a x=true↔∀b:Fin 2,val C (List.ofFn x) (opnd C a b)=true:=by
 rw[Yk j ha g]
 constructor
 ·intro h b;fin_cases b<;>[exact h.1;exact h.2]
 ·intro h;exact⟨h 0,h 1⟩
lemma Qn (b c:Fin 2):c=b\/c=1-b:=by
 fin_cases b<;>fin_cases c<;>decide
lemma X7 (g:IsAO2 n C){a h:ℕ}(ha:a < C.gates.length){b:Fin 2}(hr:OrReaches n C (opnd C a b) h):InCone n C h a:=
 WW ha (Zh g ha b) (Ku g ha b) (Qz h _ hr).1
lemma KK (g:IsAO2 n C){a h:ℕ}(ha:a < C.gates.length){b:Fin 2}(hr:OrReaches n C (opnd C a b) h):h < a:=by have j:=Zv (Qz h _ hr).1;have hb:=Ku g ha b;omega
lemma X1 (t:IsAO2 n C)(hT:TopForm G C){a h:ℕ}(ha:a < C.gates.length)(z:(gateAt C a).op=GateOp.and){b:Fin 2}(hr:OrReaches n C (opnd C a b) h)(hh:(gateAt C h).op=GateOp.and):h∈junk G C:=by
 have g:=(Qz h _ hr).2
 have q:¬BelowF G C h:=
  fun hb=>hT h g a ha hh hb z (X7 t ha hr)
 have j:∃x:Fin n->Bool,gateVal n C h x=true/\graphFun G ∅ x=false:=by
  by_contra Pt
  apply q
  intro x hx
  by_contra hf
  exact Pt ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
 exact Fm ⟨Finset.mem_range.mpr g,hh,g,j⟩
lemma Kz {w h:ℕ}{x:Fin n->Bool}(hr:OrReaches n C w h)(g:gateVal n C h x=true):val C (List.ofFn x) w=true:=
 Vc (n:=n) (by simp) (Qz h _ hr).1 g
lemma Xh {w z:ℕ}(hr:Relation.ReflTransGen (Kx n C) w z): orIn n C z⊆orIn n C w:=
 fun x g=>Kb x (hr.trans (Kh x g))
lemma QJ {w g:ℕ}(hr:OrReaches n C w g): orIn n C (n+g)⊆orIn n C w:=
 Xh (Qz g w hr).1
lemma Be {w:ℕ}(h:w < n):orIn n C w={⟨w,h⟩}:=by
 ext x
 constructor
 ·intro g
  rcases Relation.ReflTransGen.cases_head (Kh x g) with he|⟨_,j,_⟩
  ·exact Sm (Fin.ext he.symm)
  ·obtain⟨_,_,eq,_,_,_⟩:=j;omega
 ·intro g;obtain rfl:=Sp g;exact Kb _ Rr
lemma Bc {j:ℕ}(g:(gateAt C j).op=GateOp.and):orIn n C (n+j)=∅:=by
 apply Ee.mpr
 intro x q
 rcases Relation.ReflTransGen.cases_head (Kh x q) with he|⟨_,hs,_⟩
 ·have:=x.isLt;omega
 ·obtain⟨k,_,he,h,_,_⟩:=hs
  have:k=j:=by omega
  subst k;rw[g] at h;cases h
lemma V5 (g:IsAO2 n C){m:ℕ}(j:m < C.gates.length)(a3:(gateAt C m).op=GateOp.or): orIn n C (n+m)=orIn n C (opnd C m 0)∪orIn n C (opnd C m 1):=by
 ext x
 simp only[Finset.mem_union]
 constructor
 ·intro hx
  rcases Relation.ReflTransGen.cases_head (Kh x hx) with he|⟨z,t,q⟩
  ·have:=x.isLt;omega
  ·obtain⟨k,_,eq,_,a4,_⟩:=t
   have:k=m:=by omega
   subst k;obtain⟨b,rfl⟩:=KM g j a4
   fin_cases b
   ·exact Ql (Kb x q)
   ·exact Qr (Kb x q)
 ·rintro (h|h)
  ·exact Xh (Relation.ReflTransGen.single
    ⟨m,j,rfl,a3,Zh g j 0,Ku g j 0⟩) h
  ·exact Xh (Relation.ReflTransGen.single
    ⟨m,j,rfl,a3,Zh g j 1,Ku g j 1⟩) h
lemma Yb {a:ℕ}{b:Fin 2}{x:Fin n->Bool}{t:Fin n}(ht:t∈side (n:=n) C a b)(hx:x t=true):
  val C (List.ofFn x) (opnd C a b)=true:=
 YR x _ t (Kh t ht) hx
lemma KV (h:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length) (g:(gateAt C a).op=GateOp.and) {x:Fin n->Bool} {u v:Fin n} (j:u∈side (n:=n) C a 0) (hv:v∈side (n:=n) C a 1)
  (xu:x u=true) (xv:x v=true):gateVal n C a x=true:=
 (Yk h ha g x).mpr ⟨Yb j xu,Yb hv xv⟩
lemma VY (g:IsAO2 n C){a:ℕ}(ha:a∈tops G C){u v:Fin n}(h:u∈side (n:=n) C a 0)(hv:v∈side (n:=n) C a 1):
  G.Adj u v:=by
 have⟨hl,j,hb⟩:=Vr ha
 exact(Qx G u v).mp
  (hb _ (KV g hl j h hv (Q8 u v) (Qq u v)))
lemma YZ (g:IsAO2 n C){a:ℕ}(ha:a∈tops G C){d:Fin 2}{u v:Fin n}(h:u∈side (n:=n) C a d)(hv:v∈side (n:=n) C a (1-d)):
  G.Adj u v:=by
 fin_cases d
 ·exact VY g ha h hv
 ·exact(VY g ha hv h).symm
lemma W4 {a:ℕ}(ha:a∈tops G C){d:Fin 2}{u v:Fin n}(g:u∈side (n:=n) C a d)(hv:v∈side (n:=n) C a (1-d)):
  s(u,v)∈starEdges G C:=by
 unfold starEdges;refine Mbu ⟨a,ha,Mi ?_⟩
 fin_cases d
 ·exact⟨(u,v),Finset.mem_product.mpr ⟨g,hv⟩,rfl⟩
 ·exact⟨(v,u),Finset.mem_product.mpr ⟨hv,g⟩,Sw⟩
lemma QY (g:IsAO2 n C){a j:ℕ}(ha:a∈tops G C){b:Fin 2}(hr:OrReaches n C (opnd C a b) j): side (n:=n) C a (1-b)⊆wmax G C j:=by
 intro t ht;have⟨h,q,hab⟩:=Vr ha;simp only[wmax,Finset.mem_filter,Uv,true_and];intro x z hx;apply hab x;apply(QF g h q x).mpr;intro c
 rcases Qn b c with rfl|rfl
 ·exact Kz hr z
 ·exact YR x _ t (Kh t ht) hx
lemma B5 (hL:IsLeastAO G C){u v:Fin n}(j:G.Adj u v): ∃a∈tops G C,gateVal n C a (Pi u v)=true:=by
 have g (x:Fin n->Bool):val C (List.ofFn x) C.output=graphFun G ∅ x:=
  congrFun hL.2.1 x
 have⟨a,hl,q,hr,hv⟩:=Bw G (graphFun G ∅) (fun k l=>(Qx G k l).mp)
   g u v ((Qx G u v).mpr j)
 have h:=(hL.1.1 _ (YH hl)).resolve_right q
 have hb:BelowF G C a:=fun x t=>
  Wd (graphFun G ∅) g a hr x (Xy n C a x▸t)
 refine⟨a,?_,hv⟩
 simpa only[tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using
  And.intro hl (And.intro h hb)
lemma Ze (hAO:IsAO2 n C)(hT:TopForm G C){a:ℕ}(ha:a < C.gates.length)(q:(gateAt C a).op=GateOp.and){b:Fin 2}{u v:Fin n}(h:val C (List.ofFn (Pi u v)) (opnd C a b)=true): (∃t∈side (n:=n) C a b,t=u\/t=v)\/
   ∃j∈junk G C,OrReaches n C (opnd C a b) j /\
    gateVal n C j (Pi u v)=true:=by
 rcases V2 (C:=C) u v _ h with⟨t,ht,hr⟩|⟨j,g,hn,hr,hv⟩
 ·exact .inl ⟨t,Kb t hr,ht⟩
 ·have hr':=Ke hr j rfl g
  exact .inr ⟨j,X1 hAO hT ha q hr'
   ((hAO.1 _ (YH g)).resolve_right hn),hr',hv⟩
lemma Yz (hAO:IsAO2 n C){w:ℕ}{x:Fin n->Bool}(hv:val C (List.ofFn x) w=true): (∃t∈orIn n C w,x t=true)\/ (∃h,h < C.gates.length/\(gateAt C h).op=GateOp.and /\ OrReaches n C w h/\gateVal n C h x=true):=by
 have⟨w',hr,j,a4⟩:=WX (n:=n) (C:=C) (x:=List.ofFn x) (by simp) w hv
 rcases a4 with g|⟨h,z,rfl,a5⟩
 ·left
  refine⟨⟨w',g⟩,Kb ⟨w',g⟩ hr,?_⟩
  have h1:=VN C x ⟨w',g⟩
  simpa only[h1] using j
 ·right
  have q:=(hAO.1 _ (YH z)).resolve_right a5;exact⟨h,z,q,Ke hr h rfl z,j⟩
lemma BV {m:ℕ}(h:m < C.gates.length)(g:(gateAt C m).op=GateOp.or)(hn:(orIn n C (n+m)).Nonempty):m∈orN G C:=by
 have⟨t,ht⟩:=hn;simp only[orN,gatesWhere,Finset.mem_filter,Finset.mem_range];refine⟨h,g,?_⟩;intro hb
 have hv:gateVal n C m (Pi t t)=true:=
  YR (Pi t t) _ t (Kh t ht) (Q8 t t)
 exact G.irrefl ((Qx G t t).mp (hb _ hv))
lemma ZW {j m:ℕ}(q:j∈junk G C)(t:m < C.gates.length)(g:(gateAt C m).op=GateOp.or)(hr:OrReaches n C (n+m) j): m∈orN G C:=by simp only[orN,gatesWhere,Finset.mem_filter,Finset.mem_range];refine⟨t,g,?_⟩;intro hb;obtain⟨_,_,x,h,hfx⟩:=Q6 q;exact Bool.false_ne_true (hfx.symm.trans (hb x (Kz hr h)))
lemma YD (j:NoFourCycle G){X:Finset (Fin n)}{a b:Fin n}(q:1 < X.card)(ha:∀x∈X,G.Adj a x)(hb:∀x∈X,G.Adj b x): a=b:=by
 by_contra ne
 have g:X⊆Finset.univ.filter (fun w=>G.Adj a w/\G.Adj b w):=by intro x h;simp[ha x h,hb x h]
 exact(Nat.not_le_of_lt q) ((Cl g).trans (j a b ne))
lemma Wf {m:ℕ}(hm:m∈lam G C)(h:∀a∈tops G C,∀x∈side (n:=n) C a 0,∀y∈side C a 1,G.Adj x y):
  ∃t:Fin n,∀x∈orIn n C (n+m),G.Adj t x/\s(t,x)∉Ustar G C:=by
 obtain⟨_,_,_,a,ha,b,z,hr⟩:=Fp hm
 have g:orIn n C (n+m)⊆side (n:=n) C a b:=
  Xh (Qz m _ hr).1
 have⟨t,ht⟩:=Finset.card_eq_one.mp z;refine⟨t,fun x q=>?_⟩;have j:t∈side (n:=n) C a (1-b):=by simp[ht]
 have hstar':s(t,x)∈starEdges G C:=by
  unfold starEdges;refine Mbu ⟨a,ha,Mi ?_⟩
  fin_cases b
  ·exact⟨(x,t),Finset.mem_product.mpr ⟨g q,j⟩,Sw⟩
  ·exact⟨(t,x),Finset.mem_product.mpr ⟨j,g q⟩,rfl⟩
 refine⟨?_,fun he=>(D2 he) hstar'⟩
 fin_cases b
 ·exact(h a ha x (g q) t j).symm
 ·exact h a ha t j x (g q)
def KD (n g w z:ℕ):ℕ:=
 if z=n+g then w else if n+g < z then z-1 else z
lemma Y8 (hL:IsLeastAO G C){g w:ℕ}(hg:g < C.gates.length)(hw:w < n+g)(aw:∀x:Fin n->Bool,gateVal n C g x=val C (List.ofFn x) w): False:=by
 let f:=KD n g w;let gs0:=C.gates.take g++C.gates.drop (g+1);let C':Ck:=⟨gs0.map (fun gt=>⟨gt.op,gt.inputs.map f⟩),f C.output⟩;have af:gs0.length=C.gates.length-1:=by simp only[gs0,List.length_append,List.length_take,List.length_drop];omega
 have ay:C'.gates.length=C.gates.length-1:=by simp only[C',List.length_map];exact af
 have a6:∀aj∈gs0,aj∈C.gates:=fun aj h=>(Kap h).elim List.mem_of_mem_take List.mem_of_mem_drop
 have q (j:ℕ) (hj:j < g) (hj0:j < gs0.length):gs0[j]=C.gates[j]:=by simp only[gs0];rw[List.getElem_append_left (by simp;omega)];simp
 have t (j:ℕ) (hj:¬j < g) (hj0:j < gs0.length):gs0[j]=C.gates[j+1]'(by omega):=by simp only[gs0];rw[List.getElem_append_right (by simp;omega)];simp only[List.length_take,List.getElem_drop];congr 1;omega
 have a4 (j:ℕ) (hj:j < C'.gates.length):gateAt C' j=⟨(gs0[j]'(by omega)).op,(gs0[j]'(by omega)).inputs.map f⟩:=by rw[YC hj];simp only[C',List.getElem_map]
 have hAO':IsAO2 n C':=⟨fun gt ac=>by obtain⟨g0,aa,rfl⟩:=List.mem_map.mp ac;exact hL.1.1 g0 (a6 g0 aa),
  fun j hj z hz=>by
   rw[a4 j hj] at hz;obtain⟨z0,a5,rfl⟩:=List.mem_map.mp hz
   by_cases al:j < g
   ·rw[q j al (by omega)] at a5;have aq:=hL.1.2.1 j (by omega) z0 (by rw[YC (by omega)];exact a5)
    simp only[f,KD];split_ifs<;>omega
   ·rw[t j al (by omega)] at a5;have aq:=hL.1.2.1 (j+1) (by omega) z0 (by rw[YC (by omega)];exact a5)
    simp only[f,KD];split_ifs<;>omega,
  fun gt ac=>by obtain⟨g0,aa,rfl⟩:=List.mem_map.mp ac;simp[hL.1.2.2 g0 (a6 g0 aa)]⟩
 have a8:∀x:Fin n->Bool,∀z:ℕ,val C' (List.ofFn x) (f z)=val C (List.ofFn x) z:=fun x z=>by
  induction z using Nat.strong_induction_on with| _ z ih=>
  by_cases ak:z < n
  ·have a9:f z=z:=by simp only[f,KD];split_ifs<;>omega
   rw[a9,Vg (n:=n) (by simp) ak,Vg (n:=n) (by simp) ak]
  by_cases ar:z=n+g
  ·subst ar;have a9:f (n+g)=w:=by simp[f,KD]
   have ax:f w=w:=by simp only[f,KD];split_ifs<;>omega
   rw[a9,←ax,ih w hw];exact(aw x).symm
  by_cases ah:n+C.gates.length<=z
  ·have ab:n+C'.gates.length<=f z:=by simp only[f,KD];split_ifs<;>omega
   rw[WR (n:=n) (by simp) ab,WR (n:=n) (by simp) ah]
  obtain⟨k,rfl⟩:∃k,z=n+k:=⟨z-n,by omega⟩;have hk:k < C.gates.length:=by omega
  have a7 (k':ℕ) (hk':k' < C'.gates.length) (hfk:f (n+k)=n+k')
    (hge:gateAt C' k'=⟨(gateAt C k).op,(gateAt C k).inputs.map f⟩)
    (hfle:∀i,i < n+k->f i < n+k'):val C' (List.ofFn x) (f (n+k))=val C (List.ofFn x) (n+k):=by
   rw[hfk,XX (n:=n) (by simp) hk',XX (n:=n) (by simp) hk,hge];simp only[List.map_map];congr 1
   apply List.map_congr_left;intro i hi;have a3:=hL.1.2.1 k hk i hi
   simp only[Function.comp_apply,ite_eq_left (hfle i a3),ite_eq_left a3];exact ih i a3
  by_cases an:k < g
  ·exact a7 k (by omega) (by simp only[f,KD];split_ifs<;>omega)
    (by rw[a4 k (by omega),q k an (by omega),YC hk]) (fun i a3=>by simp only[f,KD];split_ifs<;>omega)
  ·have am:k-1+1=k:=by omega
   exact a7 (k-1) (by omega) (by simp only[f,KD];split_ifs<;>omega)
    (by rw[a4 (k-1) (by omega),t (k-1) (by omega) (by omega),YC hk];simp only[am])
    (fun i a3=>by simp only[f,KD];split_ifs<;>omega)
 have hfun':circuitFun n C'=graphFun G ∅:=funext fun x=>(a8 x C.output).trans (congrFun hL.2.1 x);have au:=hL.2.2 C' hAO' hfun';change C.gates.length<=C'.gates.length at au;omega
def rFull (G:SimpleGraph (Fin n))[DecidableRel G.Adj](C:Ck):Finset ℕ:=
 (orN G C\lam G C).filter fun m=>
  (orIn n C (opnd C m 0)).Nonempty/\(orIn n C (opnd C m 1)).Nonempty
def rZero (G:SimpleGraph (Fin n))[DecidableRel G.Adj](C:Ck):Finset ℕ:=
 (orN G C\lam G C).filter fun m=>
  orIn n C (opnd C m 0)=∅/\orIn n C (opnd C m 1)=∅
lemma B3:mixing G C⊆orN G C\lam G C:=by intro m z;have⟨j,h⟩:=Fp z;refine Dm j (?_);intro g;obtain⟨_,h0,q,_⟩:=Fp g;have t:orIn n C (opnd C m 0)≠∅:=Nep h0;have e1:orIn n C (opnd C m 1)≠∅:=Nep q;simp[t,e1] at h
lemma Vy:Disjoint (rFull G C) (mixing G C):=by rw[Finset.disjoint_left];intro m q j;obtain⟨_,ha,hb⟩:=Fp q;obtain⟨_,g⟩:=Fp j;have h:=Nep ha;have eb:=Nep hb;simp[h,eb] at g
lemma VE:Disjoint (rFull G C) (rZero G C):=by rw[Finset.disjoint_left];intro m j h;obtain⟨_,ha,_⟩:=Fp j;obtain⟨_,g,_⟩:=Fp h;exact Nep ha g
lemma Vw:Disjoint (mixing G C) (rZero G C):=by rw[Finset.disjoint_left];intro m q j;obtain⟨_,g⟩:=Fp q;obtain⟨_,h,eb⟩:=Fp j;simp[h,eb] at g
lemma VM: (rFull G C).card+(mixing G C).card+(rZero G C).card= (orN G C\lam G C).card:=by
 have g:rFull G C∪mixing G C∪rZero G C=orN G C\lam G C:=by
  ext m
  simp only[Finset.mem_union,rFull,rZero,mixing,Finset.mem_filter,Finset.mem_sdiff]
  constructor
  ·rintro ((⟨hm,_⟩|⟨hmN,hxor⟩)|⟨hm,_⟩)
   ·exact hm
   ·exact Dp (B3 (Fk hmN hxor))
   ·exact hm
  ·intro hm
   by_cases h0:orIn n C (opnd C m 0)=∅<;>by_cases h:orIn n C (opnd C m 1)=∅
   ·exact Qr ⟨hm,h0,h⟩
   ·exact Ql (Qr ⟨hm.1,by simp[h0,h]⟩)
   ·exact Ql (Qr ⟨hm.1,by simp[h0,h]⟩)
   ·exact Ql (Ql ⟨hm,Nem h0,
     Nem h⟩)
 rw[←g,Cud,Cud Vy];exact Finset.disjoint_union_left.mpr ⟨VE,Vw⟩
lemma KY (ag:IsAO2 n C){w j:ℕ}(hj:j∈junk G C)(hr:OrReaches n C w j)(Pt:(orIn n C w).Nonempty): ∃m∈mixing G C,OrReaches n C w m/\OrReaches n C (n+m) j:=by
 have⟨aa,_⟩:=Qz j w hr
 induction aa using Relation.ReflTransGen.head_induction_on with
 | refl=>
  rw[Bc (Q6 hj).2.1] at Pt
  exact(Nne Pt).elim
 | @head u z hstep hrest ih=>
  obtain⟨m,hm,rfl,q,a6,af⟩:=hstep
  have a4:OrReaches n C (n+m) j:=
   Ke (Relation.ReflTransGen.head ⟨m,hm,rfl,q,a6,af⟩ hrest)
    j rfl (Q6 hj).1
  by_cases ah:(orIn n C z).Nonempty
  ·have⟨m',ak,ae,aj⟩:=ih (Ke hrest j rfl (Q6 hj).1) ah
   exact⟨m',ak,
    Ke (Relation.ReflTransGen.head ⟨m,hm,rfl,q,a6,af⟩
     (Qz m' z ae).1) m' rfl (Qz m' z ae).2,
    aj⟩
  ·have t:orIn n C z=∅:=Nne2 ah
   obtain⟨b,rfl⟩:=KM ag hm a6
   have al:(orIn n C (opnd C m (1-b))).Nonempty:=by
    rw[V5 ag hm q] at Pt;have⟨x,hx⟩:=Pt
    match b with
    | ⟨0,_⟩=>
     have h:orIn n C (opnd C m 0)=∅:=t
     rcases Up hx with h0|h1
     ·rw[h] at h0;exact(N0 h0).elim
     ·exact⟨x,h1⟩
    | ⟨1,_⟩=>
     have g:orIn n C (opnd C m 1)=∅:=t
     rcases Up hx with h0|h1
     ·exact⟨x,h0⟩
     ·rw[g] at h1;exact(N0 h1).elim
   have a9:m∈mixing G C:=by
    refine Fk (ZW hj hm q a4) (?_)
    have a5:orIn n C (opnd C m (1-b))≠∅:=Nep al
    match b with
    | ⟨0,_⟩=>
     have h:orIn n C (opnd C m 0)=∅:=t;have a7:orIn n C (opnd C m 1)≠∅:=a5
     simp[h,a7]
    | ⟨1,_⟩=>
     have g:orIn n C (opnd C m 1)=∅:=t;have ad:orIn n C (opnd C m 0)≠∅:=a5;simp[g,ad]
   exact⟨m,a9,(QT n C m m).mpr ⟨hm,Ql rfl⟩,a4⟩
lemma Xf (z:IsAO2 n C){w a b:ℕ}(ha:a∈junk G C)(a7:b∈junk G C)(Pt:a≠b)(j:orIn n C w=∅)(hra:OrReaches n C w a)(hrb:OrReaches n C w b): ∃q∈rZero G C,OrReaches n C w q:=by
 have a8:n<=w:=hra.1;obtain⟨m,rfl⟩:∃m,w=n+m:=⟨w-n,by omega⟩;obtain⟨t,a3⟩:=(QT n C m a).mp hra;obtain⟨_,a4⟩:=(QT n C m b).mp hrb
 have g:(gateAt C m).op=GateOp.or:=by
  rcases a3 with rfl|⟨g,_⟩
  ·rcases a4 with hba|⟨g,_⟩
   ·exact(Pt hba.symm).elim
   ·exact g
  ·exact g
 have hsub:=V5 z t g;rw[j] at hsub
 have e0:orIn n C (opnd C m 0)=∅:=by have:=Finset.union_eq_empty.mp hsub.symm;exact this.1
 have e1:orIn n C (opnd C m 1)=∅:=by have:=Finset.union_eq_empty.mp hsub.symm;exact this.2
 have a5:m∈orN G C:=ZW ha t g hra
 have h:m∉lam G C:=by intro hl;obtain⟨_,h0,_,_⟩:=Fp hl;rw[e0] at h0;exact Nne h0
 exact⟨m,Fm ⟨Dm a5 h,e0,e1⟩,
  (QT n C m m).mpr ⟨t,Ql rfl⟩⟩
lemma KZ (h:IsAO2 n C){m:ℕ}(t:m∈mixing G C): (orIn n C (n+m)).Nonempty:=by
 have⟨j,g⟩:=Fp t
 have hm':m < C.gates.length/\(gateAt C m).op=GateOp.or/\¬BelowF G C m:=by simpa only[orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using j
 rw[V5 h hm'.1 hm'.2.1]
 by_cases h0:orIn n C (opnd C m 0)=∅
 ·have q:orIn n C (opnd C m 1)≠∅:=by intro e;simp[h0,e] at g
  exact(Nem q).mono Sur
 ·exact(Nem h0).mono Sul
lemma Yp (a3:IsAO2 n C) (h4:NoFourCycle G) {m:ℕ} (hm:m∈mixing G C) {c w1 q:Fin n} {t1 t2:ℕ} {d1 d2:Fin 2} (a8:t1∈tops G C) (ad:t2∈tops G C) (hr1:OrReaches n C (opnd C t1 d1) m) (aa:OrReaches n C (opnd C t2 d2) m) (a6:w1∈side (n:=n) C t1 (1-d1)) (hw2:q∈side (n:=n) C t2 (1-d2))
  (he1:s(c,w1)∈Ustar G C) (he2:s(c,q)∈Ustar G C):w1=q:=by
 by_contra Pt
 have⟨u,hu⟩:=KZ a3 hm;have a7:u∈side (n:=n) C t1 d1:=QJ hr1 hu;have ab:u∈side (n:=n) C t2 d2:=QJ aa hu;have h:G.Adj u w1:=YZ a3 a8 a7 a6;have j:G.Adj u q:=YZ a3 ad ab hw2;have g:G.Adj c w1:=Eg (D1 he1);have t:G.Adj c q:=Eg (D1 he2)
 have ac:u=c:=YD h4 (X:={w1,q}) (by rw[Cp Pt];omega)
  (fun x hx=>by rcases Nsp hx with rfl|z
                ·exact h
                ·rw[Sp z];exact j)
  (fun x hx=>by rcases Nsp hx with rfl|z
                ·exact g
                ·rw[Sp z];exact t)
 subst ac;exact(D2 he1) (W4 a8 a7 a6)
def WH (n:ℕ)(C:Ck)(X:Finset (Fin n))(p q:ℕ):Prop:=
 Kx n C p q/\1 < (orIn n C p∩X).card/\(orIn n C q∩X).Nonempty
def Yr (n:ℕ)(C:Ck)(X:Finset (Fin n)):=
 Relation.ReflTransGen (WH n C X)
lemma YP {X:Finset (Fin n)}{w z:ℕ}(h:Yr n C X w z):Relation.ReflTransGen (Kx n C) w z:=by
 induction h with
 | refl=>exact Rr
 | tail _ step ih=>exact ih.tail step.1
noncomputable def X3 (n:ℕ)(C:Ck)(X:Finset (Fin n))(w:ℕ):Finset ℕ:=by
 classical
 exact(Finset.range (w+1)).filter fun z=>
  Yr n C X w z/\(orIn n C z∩X).Nonempty
lemma Zp {X:Finset (Fin n)}{w z:ℕ}: z∈X3 n C X w↔Yr n C X w z/\(orIn n C z∩X).Nonempty:=by
 classical
 simp only[X3,Finset.mem_filter,Finset.mem_range];exact⟨And.right,fun h=>⟨Nat.lt_succ_of_le (Zv (YP h.1)),h⟩⟩
lemma VG {X:Finset (Fin n)}{w:ℕ}{x:Fin n}(q:x∈X)(path:Relation.ReflTransGen (Kx n C) w x.val): ∃z,Yr n C X w z/\(orIn n C z∩X).card<=1/\x∈orIn n C z:=by
 induction path using Relation.ReflTransGen.head_induction_on with
 | refl=>
  refine⟨x.val,Rr,?_,Kb x Rr⟩
  rw[Be x.isLt]
  exact(Cl Il).trans_eq (Cs _)
 | @head a b step path ih=>
  by_cases g:1 < (orIn n C a∩X).card
  ·have⟨z,hz,h,mem⟩:=ih
   have j:x∈orIn n C b:=Kb x path
   exact⟨z,hz.head ⟨step,g,⟨x,Im j q⟩⟩,h,mem⟩
  ·exact⟨a,Rr,by omega,Kb x (path.head step)⟩
lemma Yv (hAO:IsAO2 n C)(h4:NoFourCycle G){c:Fin n}{X:Finset (Fin n)}{W:Finset ℕ}(hW:∀w∈W,w < n+C.gates.length)(hX:X⊆W.biUnion (orIn n C))(be:∀x∈X,G.Adj c x)(af:Fin n)(aa:∀x∈X,x≠af->s(c,x)∈Ustar G C): ∃P⊆rFull G C,X.card<=P.card+W.card /\ ∀p∈P,(∃w∈W,OrReaches n C w p)/\1 < (orIn n C (n+p)∩X).card:=by
 classical
 let R0:=W.filter fun w=>(orIn n C w∩X).Nonempty;let cone:=R0.biUnion (X3 n C X);let ay (z:ℕ):=1 < (orIn n C z∩X).card;let internal:=cone.filter ay;let frontier:=cone\internal;let split:=internal.filter fun z=>(orIn n C (opnd C (z-n) 0)∩X).Nonempty/\(orIn n C (opnd C (z-n) 1)∩X).Nonempty;let pass:=internal\split;have ag:R0⊆cone:=fun w hw=>Mbu ⟨w,hw,Zp.mpr ⟨.refl,(Fp hw).2⟩⟩;have bj:R0.card<=W.card:=Cl (Fs _ _)
 have q (z:ℕ) (hz:z∈cone):∃w∈R0,Yr n C X w z/\(orIn n C z∩X).Nonempty:=by have⟨w,hw,bp⟩:=Bup hz;exact⟨w,hw,Zp.mp bp⟩
 have a8 (z:ℕ) (hz:z∈internal):n<=z:=by
  by_contra! a7;have h:1 < (orIn n C z∩X).card:=(Fp hz).2
  rw[Be a7] at h;have:=(Cl (Il:({⟨z,a7⟩}:Finset (Fin n))∩X⊆{⟨z,a7⟩})).trans_eq (Cs _);omega
 have a5 (z:ℕ) (hz:z∈cone):z < n+C.gates.length:=by obtain⟨w,hw,hr,_⟩:=q z hz;have:=Zv (YP hr);have:=hW w (Fp hw).1;omega
 let g (z:ℕ):Finset ℕ:=({opnd C (z-n) 0,opnd C (z-n) 1}:Finset ℕ).filter fun y=>(orIn n C y∩X).Nonempty
 have a9:cone\R0⊆internal.biUnion g:=fun y hy=>by
  have⟨cy,aq⟩:=Dp hy;have⟨w,hw,hr,bk⟩:=q y cy
  rcases Relation.ReflTransGen.cases_tail hr with rfl|⟨z,al,⟨i,hi,eq,_,au,_⟩,b4,_⟩
  ·exact(aq hw).elim
  ·have bf:z∈internal:=Fk (Mbu ⟨w,hw,Zp.mpr ⟨al,Finset.card_pos.mp (by omega)⟩⟩) b4
   have⟨b,hb⟩:=KM hAO hi au;refine Mbu ⟨z,bf,Fk (?_) bk⟩;rw[show z-n=i by omega,hb];fin_cases b<;>simp
 have ab:∀z∈pass,(g z).card<=1:=fun z hz=>by
  have⟨j,ar⟩:=Dp hz;have b9:¬((orIn n C (opnd C (z-n) 0)∩X).Nonempty/\(orIn n C (opnd C (z-n) 1)∩X).Nonempty):=fun h=>ar (Fk j h)
  by_cases h0:(orIn n C (opnd C (z-n) 0)∩X).Nonempty
  ·exact(Cl (show g z⊆{opnd C (z-n) 0} from fun y hy=>by
    have⟨hm,Pt⟩:=Fp hy;rcases Nsp hm with rfl|ak;exact Ss _;rw[Sp ak] at Pt;exact(b9 ⟨h0,Pt⟩).elim)).trans_eq (Cs _)
  ·exact(Cl (show g z⊆{opnd C (z-n) 1} from fun y hy=>by
    have⟨hm,Pt⟩:=Fp hy;rcases Nsp hm with rfl|ak;exact(h0 Pt).elim;exact ak)).trans_eq (Cs _)
 have ah:(internal.biUnion g).card<=pass.card+2*split.card:=by
  have a6:∀z∈split,(g z).card<=2:=fun z _=>(Finset.card_filter_le _ _).trans ((Cil _ _).trans_eq (by simp))
  have bm:split⊆internal:=Fs _ _;have bq:pass∪split=internal:=Finset.sdiff_union_of_subset bm
  have h1:(internal.biUnion g).card<=∑z∈pass,(g z).card+∑z∈split,(g z).card:=by
   calc (internal.biUnion g).card<=∑z∈internal,(g z).card:=Cbu
    _=∑z∈pass,(g z).card+∑z∈split,(g z).card:=by rw[←bq,Finset.sum_union Finset.sdiff_disjoint]
  have h2:=Nat.add_le_add (Sls ab) (Sls a6);simp only[Finset.sum_const,smul_eq_mul,mul_one] at h2;omega
 have aj:frontier.card<=split.card+W.card:=by have h0:=(Cl a9).trans ah;have h1:=Csd ag;have h2:=Csd (Fs ay cone);have h3:=Csd (Fs _ internal:split⊆internal);change (cone\R0).card+R0.card=cone.card at h1;change frontier.card+internal.card=cone.card at h2;change pass.card+split.card=internal.card at h3;omega
 let P:=split.image (fun z=>z-n)
 have bl:P.card=split.card:=Finset.card_image_of_injOn fun x hx y hy e=>by have:=a8 x (Fp hx).1;have:=a8 y (Fp hy).1;change x-n=y-n at e;omega
 have aw:P⊆rFull G C:=fun k hk=>by
  obtain⟨z,hz,rfl⟩:=Mip hk;have⟨j,h0X,h1X⟩:=Fp hz;have nz:=a8 z j;have eq:n+(z-n)=z:=by omega
  have ae:z-n < C.gates.length:=by have:=a5 z (Fp j).1;omega
  have ad:1 < (orIn n C (n+(z-n))∩X).card:=by rw[eq];exact(Fp j).2
  have bg:(gateAt C (z-n)).op=GateOp.or:=(hAO.1 _ (YH ae)).resolve_left fun bd=>by rw[Bc bd,Finset.empty_inter,Finset.card_empty] at ad;omega
  have⟨x1,ap,x2,az,b8⟩:=Finset.one_lt_card.mp ad
  refine Fm ⟨Dm (BV ae bg ⟨x1,(I1 ap)⟩) (fun b7=>by
   have⟨t,ht⟩:=Wf b7 (fun a ha u hu v hv=>VY hAO ha hu hv);obtain rfl:t=c:=YD h4 ad (fun y hy=>(ht y (I1 hy)).1) (fun y hy=>be y (I2 hy))
   by_cases h1g:x1=af
   ·exact(ht x2 (I1 az)).2 (aa x2 (I2 az) (fun e=>b8 (h1g.trans e.symm)))
   ·exact(ht x1 (I1 ap)).2 (aa x1 (I2 ap) h1g)),h0X.mono Il,h1X.mono Il⟩
 refine⟨P,aw,?_,fun p hp=>by
  obtain⟨z,hz,rfl⟩:=Mip hp;have j:=(Fp hz).1;have nz:=a8 z j;have eq:n+(z-n)=z:=by omega
  have ae:z-n < C.gates.length:=by have:=a5 z (Fp j).1;omega
  obtain⟨w,b6,hr,_⟩:=q z (Fp j).1
  exact⟨⟨w,(Fp b6).1,Ke (YP hr) (z-n) eq.symm ae⟩,eq.symm▸(Fp j).2⟩⟩
 let am (z:ℕ):=orIn n C z∩X
 have bb:X⊆frontier.biUnion am:=fun x hx=>by
  have⟨w,hw,ax⟩:=Bup (hX hx);have⟨z,al,an,b3⟩:=VG hx (Kh x ax)
  exact Mbu ⟨z,Dm (Mbu ⟨w,Fk hw ⟨x,Im ax hx⟩,
   Zp.mpr ⟨al,⟨x,Im b3 hx⟩⟩⟩) (fun bh=>(Nat.not_le_of_lt (Fp bh).2) an),Im b3 hx⟩
 have h1:=(Cl bb).trans (Cbu.trans (Sls (s:=frontier) fun z hz=>
  Nat.le_of_not_gt fun h=>(D2 hz) (Fk (D1 hz) h)))
 simp only[Finset.sum_const,smul_eq_mul,mul_one] at h1;omega
lemma Ky (j:IsAO2 n C)(t:NoFourCycle G){c:Fin n}{X:Finset (Fin n)}{W:Finset ℕ}(hW:∀w∈W,w < n+C.gates.length)(q:X⊆W.biUnion (orIn n C))(g:∀x∈X,s(c,x)∈Ustar G C): ∃P⊆rFull G C,X.card<=P.card+W.card /\ ∀p∈P,(∃w∈W,OrReaches n C w p)/\1 < (orIn n C (n+p)∩X).card:=
 Yv j t hW q
  (fun x h=>Eg (Dp (g x h)).1) c (fun x h _=>g x h)
lemma XV (q:IsAO2 n C)(h4:NoFourCycle G){c:Fin n}{X:Finset (Fin n)}{w:ℕ}(hw:w < n+C.gates.length)(hX:X⊆orIn n C w)(h:∀x∈X,s(c,x)∈Ustar G C): ∃P⊆rFull G C,X.card<=P.card+1 /\ ∀p∈P,OrReaches n C w p/\1 < (orIn n C (n+p)∩X).card:=by
 have⟨P,t,g,j⟩:=Ky q h4 (W:={w})
  (fun z hz=>by rw[Sp hz];exact hw)
  (by simpa using hX) h
 refine⟨P,t,by simpa using g,fun p hp=>?_⟩
 obtain⟨⟨w',hw',hr⟩,hbig⟩:=j p hp;rw[Sp hw'] at hr;exact⟨hr,hbig⟩
lemma KE {P1 P2:Finset ℕ}{W1 W2:Finset ℕ}{L1 L2:Finset (Fin n)}(h1:∀p∈P1,(∃w∈W1,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L1).card)(h2:∀p∈P2,(∃w∈W2,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L2).card)(j:(W1.biUnion (orIn n C)∩L2).card<=1\/(W2.biUnion (orIn n C)∩L1).card<=1): Disjoint P1 P2:=by
 rw[Finset.disjoint_left];intro p z a3;obtain⟨⟨w1,hw1,hr1⟩,hbig1⟩:=h1 p z;obtain⟨⟨w2,hw2,hr2⟩,hbig2⟩:=h2 p a3
 rcases j with hs|hs
 ·have g:orIn n C (n+p)∩L2⊆W1.biUnion (orIn n C)∩L2:=by
   intro x t;have⟨h,q⟩:=Ip t;exact Im (Mbu ⟨w1,hw1,QJ hr1 h⟩) q
  exact Nat.not_le_of_lt hbig2 ((Cl g).trans hs)
 ·have g:orIn n C (n+p)∩L1⊆W2.biUnion (orIn n C)∩L1:=by
   intro x t;have⟨h,q⟩:=Ip t;exact Im (Mbu ⟨w2,hw2,QJ hr2 h⟩) q
  exact Nat.not_le_of_lt hbig1 ((Cl g).trans hs)
lemma Kw (h4:NoFourCycle G){P1 P2:Finset ℕ}{W1 W2:Finset ℕ}{L1 L2:Finset (Fin n)}{c1 c2:Fin n}(Pt:c1≠c2)(z:∀p∈P1,(∃w∈W1,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L1).card)(t:∀p∈P2,(∃w∈W2,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L2).card)(h:∀w∈W1,∀x∈orIn n C w,G.Adj c1 x)(g:∀y∈L2,G.Adj c2 y):Disjoint P1 P2:=by
 refine KE z t (Ql ?_)
 have j:W1.biUnion (orIn n C)∩L2⊆Finset.univ.filter (fun x=>G.Adj c1 x/\G.Adj c2 x):=by intro x hx;have⟨hW,hL⟩:=Ip hx;have⟨w,hw,q⟩:=Bup hW;exact Fm ⟨Uv _,h w hw x q,g x hL⟩
 exact(Cl j).trans (h4 c1 c2 Pt)
lemma Xg (hT:TopForm G C){h g:ℕ}(t:h < C.gates.length)(j:(gateAt C h).op=GateOp.and)(hg:g < C.gates.length)(z:(gateAt C g).op=GateOp.and)(hc:InCone n C h g):h∈junk G C:=by
 have a3:¬BelowF G C h:=fun hb=>hT h t g hg j hb z hc
 have q:∃x:Fin n->Bool,gateVal n C h x=true/\graphFun G ∅ x=false:=by
  by_contra Pt
  apply a3
  intro x hx
  by_contra hf
  exact Pt ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
 exact Fm ⟨Finset.mem_range.mpr t,j,t,q⟩
lemma Kk {a b j:ℕ}(hs:junk G C={a,b})(g:j∈junk G C): j=a\/j=b:=by simpa only[hs,Finset.mem_insert,Finset.mem_singleton] using g
lemma Wh (hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b){h:ℕ}(hh:h < C.gates.length)(g:(gateAt C h).op=GateOp.and)(q:InCone n C h a):False:=by
 have ha:a∈junk G C:=by simp[hs]
 have z:=Xg hT hh g (Q6 ha).1 (Q6 ha).2.1 q;have t:=Y4 q;have j:=Y4 hab
 rcases Kk hs z with rfl|rfl<;>omega
lemma ZQ (j:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b)(d:Fin 2)(x:Fin n->Bool): val C (List.ofFn x) (opnd C a d)=true↔∃u∈side (n:=n) C a d,x u=true:=by
 have ha:a∈junk G C:=by simp[hs]
 constructor
 ·intro hv
  rcases Yz j hv with⟨u,t,g⟩|⟨h,z,q,hr,_⟩
  ·exact⟨u,t,g⟩
  ·exact(Wh hT hs hab z q (X7 j (Q6 ha).1 hr)).elim
 ·rintro⟨u,t,g⟩
  exact Yb t g
lemma Qv (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b)(x:Fin n->Bool): gateVal n C a x=true↔ (∃u∈side (n:=n) C a 0,x u=true)/\(∃v∈side (n:=n) C a 1,x v=true):=by
 have ha:a∈junk G C:=by simp[hs]
 rw[Yk g (Q6 ha).1 (Q6 ha).2.1,
  ZQ g hT hs hab 0,ZQ g hT hs hab 1]
lemma Yj (hL:IsLeastAO G C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b): ¬(side (n:=n) C a 0⊆side (n:=n) C a 1) /\
  ¬(side (n:=n) C a 1⊆side (n:=n) C a 0):=by
 have ha:a∈junk G C:=by simp[hs]
 constructor
 ·intro g
  apply Y8 hL (Q6 ha).1 (Ku hL.1 (Q6 ha).1 0)
  intro x;apply Bool.eq_iff_iff.mpr;rw[Qv hL.1 hT hs hab,ZQ hL.1 hT hs hab 0]
  exact⟨And.left,fun ⟨u,hu,hxu⟩=>⟨⟨u,hu,hxu⟩,⟨u,g hu,hxu⟩⟩⟩
 ·intro g
  apply Y8 hL (Q6 ha).1 (Ku hL.1 (Q6 ha).1 1)
  intro x;apply Bool.eq_iff_iff.mpr;rw[Qv hL.1 hT hs hab,ZQ hL.1 hT hs hab 1];exact⟨And.right,fun ⟨u,hu,hxu⟩=>⟨⟨u,g hu,hxu⟩,⟨u,hu,hxu⟩⟩⟩
lemma XN (hAO:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b): ∀k,k < b->(a=k\/InCone n C a k)->InCone n C k b->OrReaches n C (n+k) a:=by
 have hb:b∈junk G C:=by simp[hs]
 have ha:a∈junk G C:=by simp[hs]
 intro k
 induction k using Nat.strong_induction_on with
 | _ k ih=>
  intro t a5 h
  rcases a5 with rfl|q
  ·exact(QT n C a a).mpr ⟨(Q6 ha).1,Ql rfl⟩
  ·have g:k < C.gates.length:=lt_trans t (Q6 hb).1
   have a3:(gateAt C k).op=GateOp.or:=by
    rcases hAO.1 _ (YH g) with a4|a7
    ·have aa:=Xg hT g a4 (Q6 hb).1 (Q6 hb).2.1 h
     rcases Kk hs aa with rfl|rfl
     ·exact(Nat.lt_irrefl _ (Y4 q)).elim
     ·omega
    ·exact a7
   obtain⟨_,m,j,z,a9⟩:=(KB n C a k).mp q
   have a8:InCone n C m b:=
    WV ((KB n C m k).mpr ⟨g,m,j,z,Ql rfl⟩) h
   have a6:OrReaches n C (n+m) a:=ih m j (lt_trans j t) a9 a8;exact(QT n C k a).mpr ⟨g,Qr ⟨a3,n+m,z,by omega,a6⟩⟩
lemma B8 (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b): ∃d:Fin 2,OrReaches n C (opnd C b d) a:=by
 have hb:b∈junk G C:=by simp[hs]
 obtain⟨q,k,j,h,z⟩:=(KB n C a b).mp hab;have⟨d,hd⟩:=KM g q h;have t:InCone n C k b:=(KB n C k b).mpr ⟨q,k,j,h,Ql rfl⟩;refine⟨d,?_⟩;rw[←hd];exact XN g hT hs hab k j z t
lemma ZG (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){d:Fin 2}{h:ℕ}(j:(gateAt C h).op=GateOp.and)(hr:OrReaches n C (opnd C b d) h):h=a:=by
 have hb:b∈junk G C:=by simp[hs]
 have q:=X1 g hT (Q6 hb).1 (Q6 hb).2.1 hr j;have t:=KK g (Q6 hb).1 hr
 rcases Kk hs q with rfl|rfl
 ·rfl
 ·omega
lemma KQ (q:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){d:Fin 2}(a3:¬OrReaches n C (opnd C b d) a)(x:Fin n->Bool): val C (List.ofFn x) (opnd C b d)=true↔∃u∈side (n:=n) C b d,x u=true:=by
 constructor
 ·intro hv
  rcases Yz q hv with⟨u,z,g⟩|⟨h,_,t,hr,_⟩
  ·exact⟨u,z,g⟩
  ·have j:=ZG q hT hs t hr
   subst j
   exact(a3 hr).elim
 ·rintro⟨u,z,g⟩
  exact Yb z g
lemma QD (q:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){d:Fin 2}(z:OrReaches n C (opnd C b d) a)(x:Fin n->Bool): val C (List.ofFn x) (opnd C b d)=true↔ gateVal n C a x=true\/∃u∈side (n:=n) C b d,x u=true:=by
 constructor
 ·intro hv
  rcases Yz q hv with⟨u,hu,g⟩|⟨h,_,t,hr,a4⟩
  ·exact Qr ⟨u,hu,g⟩
  ·have j:=ZG q hT hs t hr
   subst j
   exact Ql a4
 ·rintro (ha|⟨u,hu,g⟩)
  ·exact Kz z ha
  ·exact Yb hu g
lemma ZA (hL:IsLeastAO G C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hr0:OrReaches n C (opnd C b 0) a)(hr1:OrReaches n C (opnd C b 1) a): ¬(side (n:=n) C b 0⊆side (n:=n) C b 1) /\
  ¬(side (n:=n) C b 1⊆side (n:=n) C b 0):=by
 have hb:b∈junk G C:=by simp[hs]
 constructor
 ·intro g
  apply Y8 hL (Q6 hb).1 (Ku hL.1 (Q6 hb).1 0)
  intro x;apply Bool.eq_iff_iff.mpr
  rw[Yk hL.1 (Q6 hb).1 (Q6 hb).2.1,
   QD hL.1 hT hs hr0,QD hL.1 hT hs hr1]
  constructor
  ·exact And.left
  ·intro h0
   refine⟨h0,?_⟩
   rcases h0 with ha|⟨u,j,h⟩
   ·exact Ql ha
   ·exact Qr ⟨u,g j,h⟩
 ·intro g
  apply Y8 hL (Q6 hb).1 (Ku hL.1 (Q6 hb).1 1)
  intro x;apply Bool.eq_iff_iff.mpr
  rw[Yk hL.1 (Q6 hb).1 (Q6 hb).2.1,
   QD hL.1 hT hs hr0,QD hL.1 hT hs hr1]
  constructor
  ·exact And.right
  ·intro q
   refine⟨?_,q⟩
   rcases q with ha|⟨u,j,h⟩
   ·exact Ql ha
   ·exact Qr ⟨u,g j,h⟩
def Joint (G:SimpleGraph (Fin n))[DecidableRel G.Adj](C:Ck)(j k:ℕ):Prop:=
 ∀x:Fin n->Bool,gateVal n C j x=true->gateVal n C k x=true ->
  graphFun G ∅ x=true
lemma Bn {j k:ℕ}(h:Joint G C j k):Joint G C k j:=fun x q g=>h x g q
lemma Zu (j:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a)(z:Joint G C a b): ¬OrReaches n C (opnd C b (1-db)) a /\ (side (n:=n) C b db).Nonempty /\
  side (n:=n) C b (1-db)⊆wmax G C a:=by
 have ha:a∈junk G C:=by simp[hs]
 have hb:b∈junk G C:=by simp[hs]
 have a4:¬OrReaches n C (opnd C b (1-db)) a:=by
  intro a3;obtain⟨_,_,x,g,hfx⟩:=Q6 ha
  have h:gateVal n C b x=true:=(QF j (Q6 hb).1 (Q6 hb).2.1 x).mpr
   fun i=>by
    rcases Qn db i with rfl|rfl
    ·exact Kz hrb g
    ·exact Kz a3 g
  exact Bool.false_ne_true (hfx.symm.trans (z x g h))
 have Pt:(side (n:=n) C b db).Nonempty:=by
  by_contra q
  have he:side (n:=n) C b db=∅:=Nne2 q;obtain⟨_,_,x,h,hfx⟩:=Q6 hb;have hv:=(QF j (Q6 hb).1 (Q6 hb).2.1 x).mp h db
  rcases(QD j hT hs hrb x).mp hv with g|⟨u,hu,_⟩
  ·exact Bool.false_ne_true (hfx.symm.trans (z x g h))
  ·rw[he] at hu;exact N0 hu
 have t:side (n:=n) C b (1-db)⊆wmax G C a:=by
  intro w hw;refine Fk (Uv _) (fun x g a5=>?_)
  have h:gateVal n C b x=true:=(QF j (Q6 hb).1 (Q6 hb).2.1 x).mpr
   fun i=>by
    rcases Qn db i with rfl|rfl
    ·exact Kz hrb g
    ·exact Yb hw a5
  exact z x g h
 exact⟨a4,Pt,t⟩
lemma ZD (hL:IsLeastAO G C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){u v:Fin n}(he:s(u,v)∈Ustar G C): ∃t∈tops G C,∃d:Fin 2,∃j∈junk G C, gateVal n C t (Pi u v)=true /\ OrReaches n C (opnd C t d) j /\ gateVal n C j (Pi u v)=true /\ ((∃w∈side (n:=n) C t (1-d),w=u\/w=v)\/
       (Joint G C a b/\gateVal n C a (Pi u v)=true /\
        gateVal n C b (Pi u v)=true /\
        ∃k∈junk G C,k≠j/\OrReaches n C (opnd C t (1-d)) k)):=by
  have af:G.Adj u v:=Eg (D1 he);have⟨t,ht,a4⟩:=B5 hL af;have⟨q,h,aj⟩:=Vr ht;have a7:=(QF hL.1 q h (Pi u v)).mp a4
  rcases Ze hL.1 hT q h (b:=0) (a7 0) with⟨x,hx,ab⟩|⟨j,hj,z,g⟩
  · rcases Ze hL.1 hT q h (b:=1) (a7 1) with⟨y,hy,a8⟩|⟨j,hj,z,g⟩
    · have ad:=G.ne_of_adj (VY hL.1 ht hx hy)
      have eq:s(u,v)=s(x,y):=by
        rcases ab with rfl|rfl<;>rcases a8 with rfl|rfl
        ·exact(ad rfl).elim
        ·rfl
        ·exact Sw
        ·exact(ad rfl).elim
      exact((D2 he) (eq▸W4 ht (d:=0) hx hy)).elim
    ·exact⟨t,ht,1,j,hj,a4,z,g,Ql ⟨x,hx,ab⟩⟩
  · rcases Ze hL.1 hT q h (b:=1) (a7 1) with⟨y,hy,a8⟩|⟨k,hk,aa,ac⟩
    ·exact⟨t,ht,0,j,hj,a4,z,g,Ql ⟨y,hy,a8⟩⟩
    · have a6:Joint G C j k:=fun x a3 ag=>
        aj x ((Yk hL.1 q h x).mpr ⟨Kz z a3,Kz aa ag⟩)
      have Pt:j≠k:=by
        rintro rfl
        obtain⟨_,_,x,a3,hfx⟩:=Q6 hj;exact Bool.false_ne_true (hfx.symm.trans (a6 x a3 a3))
      have habJ:Joint G C a b/\gateVal n C a (Pi u v)=true /\
          gateVal n C b (Pi u v)=true:=by
        rcases Kk hs hj with rfl|rfl<;>rcases Kk hs hk with rfl|rfl
        ·exact(Pt rfl).elim
        ·exact⟨a6,g,ac⟩
        ·exact⟨Bn a6,ac,g⟩
        ·exact(Pt rfl).elim
      exact⟨t,ht,0,j,hj,a4,z,g,Qr ⟨habJ.1,habJ.2.1,habJ.2.2,k,hk,Pt.symm,aa⟩⟩
lemma Y1 (j:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b){d:Fin 2}{w:Fin n}(g:w∈side (n:=n) C a d)(hwW:w∈wmax G C a):
  ∀v∈side (n:=n) C a (1-d),G.Adj w v:=by
 intro v hv;have h:=(Fp hwW).2;apply(Qx G w v).mp;apply h (Pi w v) _ (Q8 w v);rw[Qv j hT hs hab]
 fin_cases d
 ·exact⟨⟨w,g,Q8 w v⟩,⟨v,hv,Qq w v⟩⟩
 ·exact⟨⟨v,hv,Qq w v⟩,⟨w,g,Q8 w v⟩⟩
lemma QC (h:IsAO2 n C){b:ℕ}(hb:b∈junk G C){d:Fin 2}{w:Fin n}(g:w∈side (n:=n) C b d)(hwW:w∈wmax G C b):
  ∀v∈side (n:=n) C b (1-d),G.Adj w v:=by
 intro v hv;have j:=(Fp hwW).2;apply(Qx G w v).mp;apply j (Pi w v) _ (Q8 w v)
 fin_cases d
 ·exact KV h (Q6 hb).1 (Q6 hb).2.1 g hv
   (Q8 w v) (Qq w v)
 ·exact KV h (Q6 hb).1 (Q6 hb).2.1 hv g
   (Qq w v) (Q8 w v)
lemma VP (h:IsAO2 n C) (hT:TopForm G C) {a b:ℕ} (hs:junk G C={a,b}) (hab:InCone n C a b) {db:Fin 2} (hrb:OrReaches n C (opnd C b db) a) {da:Fin 2} {w:Fin n} (g:w∈side (n:=n) C a da) (hwB:w∈side (n:=n) C b (1-db))
  (hwW:w∈wmax G C b):∀v∈side (n:=n) C a (1-da),G.Adj w v:=by
 have hb:b∈junk G C:=by simp[hs]
 intro v hv;have j:=(Fp hwW).2;apply(Qx G w v).mp;apply j (Pi w v) _ (Q8 w v)
 have q:gateVal n C a (Pi w v)=true:=by
  rw[Qv h hT hs hab]
  fin_cases da
  ·exact⟨⟨w,g,Q8 w v⟩,⟨v,hv,Qq w v⟩⟩
  ·exact⟨⟨v,hv,Qq w v⟩,⟨w,g,Q8 w v⟩⟩
 exact(QF h (Q6 hb).1 (Q6 hb).2.1 (Pi w v)).mpr fun i=>by
  rcases Qn db i with rfl|rfl
  ·exact Kz hrb q
  ·exact Yb hwB (Q8 w v)
lemma VZ (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a){da:Fin 2}{w:Fin n}(h:w∈side (n:=n) C a da)(hwW:w∈wmax G C b):
  ∀v∈side (n:=n) C a (1-da),v∈side (n:=n) C b (1-db)->G.Adj w v:=by
 have hb:b∈junk G C:=by simp[hs]
 intro v j z;have t:=(Fp hwW).2;apply(Qx G w v).mp;apply t (Pi w v) _ (Q8 w v)
 have q:gateVal n C a (Pi w v)=true:=by
  rw[Qv g hT hs hab]
  fin_cases da
  ·exact⟨⟨w,h,Q8 w v⟩,⟨v,j,Qq w v⟩⟩
  ·exact⟨⟨v,j,Qq w v⟩,⟨w,h,Q8 w v⟩⟩
 exact(QF g (Q6 hb).1 (Q6 hb).2.1 (Pi w v)).mpr fun i=>by
  rcases Qn db i with rfl|rfl
  ·exact Kz hrb q
  ·exact Yb z (Qq w v)
lemma VX (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a){w:Fin n}(hw0:w∈side (n:=n) C a 0)(hw1:w∈side (n:=n) C a 1)(hwW:w∈wmax G C b):
  ∀v∈side (n:=n) C b (1-db),G.Adj w v:=by
 have hb:b∈junk G C:=by simp[hs]
 intro v hv;have h:=(Fp hwW).2;apply(Qx G w v).mp;apply h (Pi w v) _ (Q8 w v)
 have j:gateVal n C a (Pi w v)=true:=
  (Qv g hT hs hab _).mpr ⟨⟨w,hw0,Q8 w v⟩,⟨w,hw1,Q8 w v⟩⟩
 exact(QF g (Q6 hb).1 (Q6 hb).2.1 (Pi w v)).mpr fun i=>by
  rcases Qn db i with rfl|rfl
  ·exact Kz hrb j
  ·exact Yb hv (Qq w v)
lemma VV (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a){w:Fin n}(h:w∈side (n:=n) C b (1-db))(hwW:w∈wmax G C b):
  ∀v∈side (n:=n) C a 0,v∈side (n:=n) C a 1->G.Adj w v:=by
 have hb:b∈junk G C:=by simp[hs]
 intro v Pv Pu;have j:=(Fp hwW).2;apply(Qx G w v).mp;apply j (Pi w v) _ (Q8 w v)
 have q:gateVal n C a (Pi w v)=true:=
  (Qv g hT hs hab _).mpr ⟨⟨v,Pv,Qq w v⟩,⟨v,Pu,Qq w v⟩⟩
 exact(QF g (Q6 hb).1 (Q6 hb).2.1 (Pi w v)).mpr fun i=>by
  rcases Qn db i with rfl|rfl
  ·exact Kz hrb q
  ·exact Yb h (Q8 w v)
lemma Vh (h4:NoFourCycle G){S0 S1:Finset (Fin n)}{c0 c1:Fin n}(aa:c0∈S0)(a5:c1∈S1)(g:∀v∈S1,G.Adj c0 v)(t:∀u∈S0,G.Adj c1 u){u v:Fin n}(hu:u∈S0)(hv:v∈S1)(a4:G.Adj u v):u=c0\/v=c1:=by
 by_contra h
 have a7:u≠c0:=fun e=>h (Ql e);have a6:v≠c1:=fun e=>h (Qr e)
 have eq:=YD h4 (X:={c1,v}) (by rw[Cp (Ne.symm a6)];omega)
  (fun z hz=>by
   rcases Nsp hz with q|j
   ·rw[q];exact g c1 a5
   ·rw[Sp j];exact g v hv)
  (fun z hz=>by
   rcases Nsp hz with q|j
   ·rw[q];exact(t u hu).symm
   ·rw[Sp j];exact a4)
 exact a7 eq.symm
lemma Q1 (q:IsAO2 n C){g:ℕ}(j:g∈junk G C){v:Fin n}(Pv:v∈side (n:=n) C g 0)(Pu:v∈side (n:=n) C g 1):
  v∉wmax G C g/\∀w∈wmax G C g,G.Adj v w:=by
 constructor
 ·intro hw
  have h:=KV q (Q6 j).1 (Q6 j).2.1 Pv Pu
   (Q8 v v) (Q8 v v)
  exact G.irrefl ((Qx G v v).mp
   ((Fp hw).2 (Pi v v) h (Q8 v v)))
 ·intro w hw
  have h:=KV q (Q6 j).1 (Q6 j).2.1 Pv Pu
   (Q8 v w) (Q8 v w)
  exact(Qx G v w).mp
   ((Fp hw).2 (Pi v w) h (Qq v w))
lemma Wy (h:IsAO2 n C) (hT:TopForm G C) {a b:ℕ} (hs:junk G C={a,b}) (hab:InCone n C a b) {db:Fin 2} (hrb:OrReaches n C (opnd C b db) a) {v:Fin n} (Pv:v∈side (n:=n) C a 0) (Pu:v∈side (n:=n) C a 1)
  (hvB:v∈side (n:=n) C b (1-db)):
  v∉wmax G C b/\∀w∈wmax G C b,G.Adj v w:=by
 have hb:b∈junk G C:=by simp[hs]
 have g (w:Fin n):gateVal n C b (Pi v w)=true:=by
  have j:gateVal n C a (Pi v w)=true:=
   (Qv h hT hs hab _).mpr ⟨⟨v,Pv,Q8 v w⟩,⟨v,Pu,Q8 v w⟩⟩
  exact(QF h (Q6 hb).1 (Q6 hb).2.1 (Pi v w)).mpr fun i=>by
   rcases Qn db i with rfl|rfl
   ·exact Kz hrb j
   ·exact Yb hvB (Q8 v w)
 constructor
 ·intro hw
  exact G.irrefl ((Qx G v v).mp
   ((Fp hw).2 (Pi v v) (g v) (Q8 v v)))
 ·intro w hw
  exact(Qx G v w).mp
   ((Fp hw).2 (Pi v w) (g w) (Qq v w))
def Q4 (c:Fin n)(E:Finset (Sym2 (Fin n))):Finset (Fin n):=
 Finset.univ.filter fun x=>s(c,x)∈E
lemma Zk {c x:Fin n}{E:Finset (Sym2 (Fin n))}: x∈Q4 c E↔s(c,x)∈E:=by simp[Q4]
lemma Yq {P1 P2 R:Finset ℕ}(j:P1⊆R)(h:P2⊆R)(g:Disjoint P1 P2): P1.card+P2.card<=R.card:=by rw[←Cud g];exact Cl (Us2 j h)
lemma Qa (j:NoFourCycle G){A B:Finset (Fin n)}(hB:2<=B.card)(g:∀u∈A,∀v∈B,G.Adj u v):A.card<=1:=by
 by_contra! h
 have⟨a,ha,b,hb,Pt⟩:=Finset.one_lt_card.mp h;exact Pt (YD j (by omega) (g a ha) (g b hb))
lemma Xc (t:NoFourCycle G){A:Finset (Fin n)}{x y:Fin n}(Pt:x≠y)(j:∀u∈A,G.Adj x u)(q:∀u∈A,G.Adj y u):A.card<=1:=by
 have g:A⊆Finset.univ.filter (fun w=>G.Adj x w/\G.Adj y w):=fun u h=>
  Fm ⟨Uv _,j u h,q u h⟩
 exact(Cl g).trans (t x y Pt)
noncomputable def T0For (G:SimpleGraph (Fin n))[DecidableRel G.Adj](C:Ck)(j:ℕ): Finset ℕ:=by
 classical
 exact(centreless G C).filter fun t=>
  ∃d:Fin 2,side (n:=n) C t d=∅/\OrReaches n C (opnd C t d) j /\
   (side (n:=n) C t (1-d)).Nonempty
noncomputable def W0For (G:SimpleGraph (Fin n))[DecidableRel G.Adj](C:Ck)(j:ℕ): Finset ℕ:=
 (T0For G C j).image fun t=>
  if side (n:=n) C t 0=∅ then opnd C t 1 else opnd C t 0
lemma Qj (j:ℕ):(W0For G C j).card<=(T0For G C j).card:=Ci
lemma Qs (j:ℕ):(T0For G C j).card<=(centreless G C).card:=
 Cl (Fs _ _)
lemma Qg (h:IsAO2 n C)(j:ℕ):∀w∈W0For G C j,w < n+C.gates.length:=by
 intro w hw;obtain⟨t,ht,rfl⟩:=Mip hw;have g:=(Vr (Fp (Fp ht).1).1).1
 split_ifs
 ·have h1:=Ku h g 1;omega
 ·have h0:=Ku h g 0;omega
lemma Qc (a6:IsAO2 n C)(j:ℕ): ∀w∈W0For G C j,orIn n C w⊆wmax G C j:=by
 intro w hw;obtain⟨t,ht,rfl⟩:=Mip hw;have⟨a7,d,a8,a3,z⟩:=Fp ht;have q:=(Fp a7).1
 by_cases h0:side (n:=n) C t 0=∅
 ·rw[if_pos h0]
  rcases Qn 0 d with rfl|rfl
  ·have g:(1:Fin 2)-0=1:=rfl
   have h:=QY a6 q a3
   rw[g] at h;exact h
  ·have g:(1:Fin 2)-(1-0)=0:=rfl
   rw[g,h0] at z
   exact(Nne z).elim
 ·rw[if_neg h0]
  rcases Qn 0 d with rfl|rfl
  ·exact(h0 a8).elim
  ·have a5:(1:Fin 2)-0=1:=rfl;have a4:(1:Fin 2)-1=0:=rfl;rw[a5] at a3;have h:=QY a6 q a3;rw[a4] at h;exact h
lemma X8 {t j:ℕ} {d:Fin 2} {w:Fin n} (ht:t∈centreless G C) (g:side (n:=n) C t d=∅)
  (hrd:OrReaches n C (opnd C t d) j) (hw:w∈side (n:=n) C t (1-d)):
  w∈(W0For G C j).biUnion (orIn n C):=by
 have z:t∈T0For G C j:=Fm ⟨ht,d,g,hrd,⟨w,hw⟩⟩;refine Mbu ⟨_,Mi ⟨t,z,rfl⟩,?_⟩
 rcases Qn 0 d with rfl|rfl
 ·rw[if_pos g];exact hw
 ·have q:(1:Fin 2)-(1-0)=0:=rfl;rw[q] at hw;have h:side (n:=n) C t 0≠∅:=Nep ⟨w,hw⟩;rw[if_neg h];exact hw
lemma K8 (q:IsAO2 n C){j:ℕ}(hj:j∈junk G C){w:Fin n}{t:ℕ}{d:Fin 2}(ht:t∈tops G C)(h:OrReaches n C (opnd C t d) j)(hw:w∈side (n:=n) C t (1-d)):
  w∈(W0For G C j).biUnion (orIn n C)\/
   ∃t'∈tops G C,∃d':Fin 2,∃m∈(mixing G C).filter (fun m=>OrReaches n C (n+m) j),
    OrReaches n C (opnd C t' d') m/\w∈side (n:=n) C t' (1-d'):=by
 by_cases g:side (n:=n) C t d=∅
 ·left
  have a3:t∈centreless G C:=Fk ht (by
   rcases Qn 0 d with rfl|rfl
   ·exact Ql g
   ·exact Qr g)
  exact X8 a3 g h hw
 ·right
  have Pt:(orIn n C (opnd C t d)).Nonempty:=Nem g;have⟨m,hm,z,a4⟩:=KY q hj h Pt;exact⟨t,ht,d,m,Fk hm a4,z,hw⟩
lemma YK (a6:IsAO2 n C){a b:ℕ}(ha:a∈junk G C)(hb:b∈junk G C)(Pt:a≠b)(z:(T0For G C a∩T0For G C b).Nonempty): (rZero G C).Nonempty:=by
 classical
 have⟨t,ht⟩:=z;have⟨a8,a7⟩:=Ip ht;obtain⟨_,da,a3,a5,g⟩:=Fp a8;obtain⟨_,db,a4,hrb,h⟩:=Fp a7
 have a9:da=db:=by
  have j:(1:Fin 2)-(1-0)=0:=rfl
  rcases Qn 0 da with rfl|rfl<;>rcases Qn 0 db with rfl|rfl
  ·rfl
  ·rw[j,a3] at h;exact(Nne h).elim
  ·rw[j,a4] at g;exact(Nne g).elim
  ·rfl
 subst a9;obtain⟨q,hq,_⟩:=Xf a6 ha hb Pt a3 a5 hrb;exact⟨q,hq⟩
lemma Yd (h:IsAO2 n C){a b g:ℕ}(ha:a∈junk G C)(hb:b∈junk G C)(Pt:a≠b)(a7:g∈mixing G C)(a8:OrReaches n C (n+g) a)(hrb:OrReaches n C (n+g) b): (rZero G C).Nonempty\/∃t∈mixing G C,t≠g/\OrReaches n C (n+g) t:=by
 have hm':g < C.gates.length/\(gateAt C g).op=GateOp.or:=by have h1:=(Fp a7).1;simp only[orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at h1;exact⟨h1.1,h1.2.1⟩
 have a6:=(Fp a7).2
 obtain⟨d,hde,hdne⟩:∃d:Fin 2,orIn n C (opnd C g d)=∅/\(orIn n C (opnd C g (1-d))).Nonempty:=by
  by_cases h0:orIn n C (opnd C g 0)=∅
  ·exact⟨0,h0,Nem fun e=>by change orIn n C (opnd C g 1)=∅ at e;simp[h0,e] at a6⟩
  ·exact⟨1,by by_contra h1;simp[h0,h1] at a6,Nem h0⟩
 have z (j:ℕ) (hj:j∈junk G C) (hr:OrReaches n C (n+g) j):
   OrReaches n C (opnd C g d) j\/OrReaches n C (opnd C g (1-d)) j:=by
  obtain⟨_,heq|⟨_,i,hi,_,hri⟩⟩:=(QT n C g j).mp hr
  ·subst heq;have:=(Q6 hj).2.1;rw[hm'.2] at this;cases this
  ·obtain⟨k,rfl⟩:=KM h hm'.1 hi;rcases Qn d k with rfl|rfl<;>[exact Ql hri;exact Qr hri]
 have a4 {j:ℕ} (hj:j∈junk G C) (hr1:OrReaches n C (opnd C g (1-d)) j):
   ∃t∈mixing G C,t≠g/\OrReaches n C (n+g) t:=by
  obtain⟨t,a3,a5,_⟩:=KY h hj hr1 hdne
  exact⟨t,a3,Nlt (KK h hm'.1 a5),(QT n C g t).mpr
   ⟨hm'.1,Qr ⟨hm'.2,opnd C g (1-d),Zh h hm'.1 (1-d),Ku h hm'.1 (1-d),a5⟩⟩⟩
 rcases z a ha a8 with aa|ab
 ·rcases z b hb hrb with a9|ac
  ·obtain⟨q,hq,_⟩:=Xf h ha hb Pt hde aa a9;exact Ql ⟨q,hq⟩
  ·exact Qr (a4 hb ac)
 ·exact Qr (a4 ha ab)
lemma X5 (a6:IsAO2 n C) (h4:NoFourCycle G) {a b:ℕ} (ha:a∈junk G C) (hb:b∈junk G C) (Pt:a≠b) {c:Fin n} {L:Finset (Fin n)} {M:Finset ℕ} {fw:ℕ->Fin n} (hM:M⊆mixing G C) (ag:∀m∈M,OrReaches n C (n+m) a) (a3:∀w∈L,s(c,w)∈Ustar G C) (a7:∀m∈M,fw m∈L/\∃t∈tops G C,∃d:Fin 2,OrReaches n C (opnd C t d) m/\fw m∈side (n:=n) C t (1-d))
  (hfinj:∀m1∈M,∀m2∈M,m1≠m2->fw m1≠fw m2)
  {mb:ℕ} (hmb:mb∈mixing G C) (hmb_b:OrReaches n C (n+mb) b):
  M.card+1<=(mixing G C).card+(rZero G C).card:=by
 by_cases g:mb∈M
 ·rcases Yd a6 ha hb Pt hmb (ag mb g) hmb_b with ah|⟨m',q,hne_m,z⟩
  ·have:=Cpr ah;have:=Cl hM;omega
  ·have j:m'∉M:=fun a4=>by
    have⟨af,t0,ak,d0,ae,aa⟩:=a7 mb g;have⟨ad,t',aj,d',ab,a8⟩:=a7 m' a4;exact hfinj mb g m' a4 hne_m.symm (Yp a6 h4 q ak aj (QH ae z) ab aa a8 (a3 _ af) (a3 _ ad))
   have h:=Cl (Ism ⟨q,hM⟩);rw[Cns j] at h;omega
 ·have h:=Cl (Ism ⟨hmb,hM⟩);rw[Cns g] at h;omega
lemma KG (z:IsAO2 n C) (h4:NoFourCycle G) {a b:ℕ} (ha:a∈junk G C) (hb:b∈junk G C) (Pt:a≠b) {c:Fin n} {L:Finset (Fin n)} {M:Finset ℕ} {j:ℕ->Fin n} (hM:M⊆mixing G C) (a4:∀m∈M,OrReaches n C (n+m) a) (q:∀w∈L,s(c,w)∈Ustar G C) (a9:∀m∈M,j m∈L/\∃t∈tops G C,∃d:Fin 2, OrReaches n C (opnd C t d) m/\j m∈side (n:=n) C t (1-d))
  (hfinj:∀m1∈M,∀m2∈M,m1≠m2->j m1≠j m2)
  (hbWit:(T0For G C b).Nonempty\/∃mb∈mixing G C,OrReaches n C (n+mb) b):
  (W0For G C a).card+M.card+1 <=
   2*(centreless G C).card+(mixing G C).card+(rZero G C).card:=by
 rcases hbWit with a8|⟨mb,a6,h⟩
 ·by_cases g:(T0For G C a∩T0For G C b).Nonempty
  ·have ae:1<=(rZero G C).card:=
    Cpr (YK z ha hb Pt g)
   have hw:=(Qj (G:=G) (C:=C) a).trans (Qs a);have hm:=Cl hM
   omega
  ·have a5:Disjoint (T0For G C a) (T0For G C b):=
    Finset.disjoint_iff_inter_eq_empty.mpr (Nne2 g)
   have ac:(T0For G C a).card+(T0For G C b).card<=(centreless G C).card:=
    Yq (Fs _ _) (Fs _ _) a5
   have h1:1<=(T0For G C b).card:=Cpr a8;have hw:=Qj (G:=G) (C:=C) a;have hm:=Cl hM
   omega
 ·have h1:=X5 z h4 ha hb Pt hM a4 q a9 hfinj a6 h;have hw:=(Qj (G:=G) (C:=C) a).trans (Qs a);omega
def TopCov (G:SimpleGraph (Fin n))[DecidableRel G.Adj](C:Ck)(j:ℕ)(w:Fin n):Prop:=
 w∈(W0For G C j).biUnion (orIn n C)\/
  ∃t∈tops G C,∃d:Fin 2,∃m∈(mixing G C).filter (fun m=>OrReaches n C (n+m) j),
   OrReaches n C (opnd C t d) m/\w∈side (n:=n) C t (1-d)
lemma Q5 (g:IsAO2 n C){j:ℕ}{w:Fin n}(h:TopCov G C j w): w∈wmax G C j:=by
 rcases h with hw0|⟨t,ht,d,m,hm,a3,a4⟩
 ·have⟨z,hz,q⟩:=Bup hw0
  exact Qc g j z hz q
 ·exact QY g ht (QH a3 (Fp hm).2) a4
lemma Kt {j:ℕ}{w:Fin n}(h:TopCov G C j w): (T0For G C j).Nonempty\/∃m∈mixing G C,OrReaches n C (n+m) j:=by
 classical
 rcases h with hw0|⟨_,_,_,m,hm,_,_⟩
 ·obtain⟨z,hz,_⟩:=Bup hw0
  obtain⟨t,ht,_⟩:=Mip hz
  exact Ql ⟨t,ht⟩
 ·have⟨q,g⟩:=Fp hm;exact Qr ⟨m,q,g⟩
def QW {n:ℕ}(u v w:Fin n):Fin n->Bool:=
 fun x=>decide (x=u\/x=v\/x=w)
lemma tripleInput_1 {n:ℕ}(u v w:Fin n):QW u v w u=true:=by simp[QW]
lemma tripleInput_2 {n:ℕ}(u v w:Fin n):QW u v w v=true:=by simp[QW]
lemma XZ {n:ℕ}(u v w:Fin n):QW u v w w=true:=by simp[QW]
lemma VW (G:SimpleGraph (Fin n))[DecidableRel G.Adj](u v w:Fin n): graphFun G ∅ (QW u v w)=true↔G.Adj u v\/G.Adj u w\/G.Adj v w:=by
 simp only[graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
  Bool.false_or,decide_eq_true_eq,QW]
 constructor
 ·rintro⟨x,y,hxy,hx,hy⟩
  rcases hx with rfl|rfl|rfl<;>rcases hy with rfl|rfl|rfl
  ·exact(G.irrefl hxy).elim
  ·exact Ql hxy
  ·exact Qr (Ql hxy)
  ·exact Ql hxy.symm
  ·exact(G.irrefl hxy).elim
  ·exact Qr (Qr hxy)
  ·exact Qr (Ql hxy.symm)
  ·exact Qr (Qr hxy.symm)
  ·exact(G.irrefl hxy).elim
 ·rintro (h|h|h)
  ·exact⟨u,v,h,Ql rfl,Qr (Ql rfl)⟩
  ·exact⟨u,w,h,Ql rfl,Qr (Qr rfl)⟩
  ·exact⟨v,w,h,Qr (Ql rfl),Qr (Qr rfl)⟩
lemma Ka {j:ℕ}{u v w:Fin n}(hw:w∈wmax G C j)(g:gateVal n C j (QW u v w)=true): G.Adj u v\/G.Adj u w\/G.Adj v w:=
 (VW G u v w).mp ((Fp hw).2 (QW u v w) g (XZ u v w))
abbrev G11:SimpleGraph (Fin 11):=
 PEqualNP.EdgeOwnership.edgeGraph 11
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
abbrev Ga:=G11.Adj
abbrev N:=side (n:=11)
abbrev Mw:=wmax G11
abbrev O:=OrReaches 11
abbrev Tc:=TopCov G11
abbrev Tp:=tops G11
abbrev Gv:=gateVal 11
abbrev Jk:=junk G11
abbrev Ic:=InCone 11
abbrev Oi:=orIn 11
abbrev Us:=Ustar G11
abbrev Tf:=TopForm G11
abbrev Ao:=IsAO2 11
abbrev Ls:=IsLeastAO G11
abbrev Bd(C:Ck):Prop:=(Us C).card<=2*(centreless G11 C).card+2+(rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card
lemma Zl{n:ℕ}{c x:Fin n}{E:Finset (Sym2 (Fin n))}(h:x∈Q4 c E):s(c,x)∈E:=Zk.mp h
lemma Zm{n:ℕ}{c x:Fin n}{E:Finset (Sym2 (Fin n))}(h:s(c,x)∈E):x∈Q4 c E:=Zk.mpr h
lemma Q3:NoFourCycle G11:=by decide
def ZU:Fin 11->List (Fin 11)
 | ⟨0,_⟩=>[9,10]
 | ⟨1,_⟩=>[4,8]
 | ⟨2,_⟩=>[5,10]
 | ⟨3,_⟩=>[6,7]
 | ⟨4,_⟩=>[1,8,10]
 | ⟨5,_⟩=>[2,8,9]
 | ⟨6,_⟩=>[3,7,10]
 | ⟨7,_⟩=>[3,6,9]
 | ⟨8,_⟩=>[1,4,5,9]
 | ⟨9,_⟩=>[0,5,7,8]
 | ⟨10,_⟩=>[0,2,4,6]
abbrev gB (u v:Fin 11):Bool:=(ZU u).contains v
lemma YB (u v:Fin 11):gB u v=true↔Ga u v:=by revert u v;decide
lemma VA {u v:Fin 11}(h:Ga u v):v∈ZU u:=by simpa[gB] using (YB u v).mpr h
structure DP where
 p:Prop
 b:Bool
 ok:b=true->p
abbrev dF (f:Fin 11->DP):DP:=
 ⟨∀⦃v⦄,(f v).p,(List.finRange 11).all fun v=>(f v).b,fun h v=>(f v).ok (Za h v (List.mem_finRange v))⟩
abbrev dN (u:Fin 11)(f:Fin 11->DP):DP:=
 ⟨∀⦃v⦄,Ga u v->(f v).p,(ZU u).all fun v=>(f v).b,fun h v hv=>(f v).ok (Za h v (VA hv))⟩
abbrev dG (c:Prop)(b:Bool)(hc:c->b=true)(q:DP):DP:=
 ⟨c->q.p,!b ||q.b,fun h c'=>q.ok (by simp[hc c'] at h;exact h)⟩
abbrev Y (a b:Fin 11):DP->DP:=dG (a≠b) (a !=b) (by intro h;simp[h])
abbrev Bh (a b:Fin 11):DP->DP:=dG (a < b) (Nat.blt a.val b.val) (fun h=>Nat.blt_eq.mpr h)
abbrev dA (a b:Fin 11):DP->DP:=dG (Ga a b) (gB a b) (YB a b).mpr
abbrev Pq (a b:Fin 11):DP->DP:=dG (¬Ga a b) (!gB a b) (by intro h;cases hb:gB a b;rfl;exact absurd ((YB a b).mp hb) h)
abbrev Pp (a b c d:Fin 11):DP->DP:=dG (Ga a b\/Ga c d) (gB a b ||gB c d) (fun h=>h.elim (fun h=>by rw[(YB a b).mpr h];simp) (fun h=>by rw[(YB c d).mpr h];simp))
abbrev dT (a b c:Fin 11):DP->DP:=dG (Ga a b\/Ga a c\/Ga b c) (gB a b ||gB a c ||gB b c) (fun h=>h.elim (fun h=>by rw[(YB a b).mpr h];simp) (fun h=>h.elim (fun h=>by rw[(YB a c).mpr h];simp) (fun h=>by rw[(YB b c).mpr h];simp)))
abbrev VT (x y a b c:Fin 11):DP->DP:=dG (x=y\/Ga a b\/Ga a c\/Ga b c) ((x==y) ||gB a b ||gB a c ||gB b c) (fun h=>h.elim (fun h=>by simp[h]) (fun h=>h.elim (fun h=>by rw[(YB a b).mpr h];simp) (fun h=>h.elim (fun h=>by rw[(YB a c).mpr h];simp) (fun h=>by rw[(YB b c).mpr h];simp))))
abbrev dX:DP:=⟨False,false,Bool.noConfusion⟩
abbrev Yg (d:DP)(h:d.b=true):d.p:=d.ok h
def VU:=Yg (dF fun c1=>dN c1 fun v=>dN c1 fun x0=>dN c1 fun x1=>Y x0 v<|Y x1 v<|Y x1 x0<|dT v x1 x0<|dN x0 fun y=>Y y c1<|Y y v<|Y y x0<|Y y x1<|Pq v y<|dN x1 fun w1=>Y w1 c1<|Y w1 v<|Y w1 x0<|Y w1 x1<|Y w1 y<|Pp v w1 y w1<|dN v fun g=>Y g v<|Y g c1<|Y g x0<|Y g y<|Y g x1<|Y g w1<|dT x1 y g<|dT x0 w1 g<|dX) (by decide)
def Z5:=Yg (dF fun v=>dN v fun w0=>dN v fun x0=>dN v fun x1=>Y x0 w0<|Y x1 w0<|Y x1 x0<|dT w0 x0 x1<|dN w0 fun j=>Y j v<|Y j x0<|Y j x1<|dN x0 fun g=>Y g v<|Y g w0<|Y g x0<|Y g x1<|Y g j<|dT x1 j g<|dN x1 fun h=>Y h v<|Y h w0<|Y h x0<|Y h x1<|Y h j<|Y h g<|dT x0 j h<|dT w0 g h<|dX) (by decide)
def XB:=Yg (dF fun q=>dN q fun g=>dN q fun j=>Y j g<|dN q fun w0=>Y w0 g<|Y w0 j<|dT g j w0<|dN w0 fun h=>Y h q<|Y h g<|Y h j<|Y h w0<|dN g fun x0=>Y x0 q<|Y x0 h<|Y x0 g<|Y x0 j<|Y x0 w0<|dT h j x0<|dN j fun x1=>Y x1 q<|Y x1 h<|Y x1 g<|Y x1 j<|Y x1 w0<|Y x1 x0<|dT h g x1<|dT x0 x1 w0<|dX) (by decide)
def Xj:=Yg (dF fun x0=>dN x0 fun h=>dN x0 fun j=>Bh h j<|dF fun x1=>Y x1 x0<|Y x1 h<|Y x1 j<|dN x1 fun g=>Y g x0<|Y g h<|Y g j<|dN x1 fun q=>Bh g q<|Y q x0<|Y q h<|Y q j<|dF fun w0=>Y w0 h<|Y w0 j<|Y w0 g<|Y w0 q<|dT g h w0<|dT g j w0<|dT q h w0<|dT q j w0<|dN w0 fun v1=>Y v1 x0<|Y v1 x1<|Y v1 h<|Y v1 j<|Y v1 g<|Y v1 q<|dT v1 g x0<|dT v1 q x0<|dT v1 h x1<|dT v1 j x1<|dN w0 fun t=>Bh v1 t<|Y t x0<|Y t x1<|Y t h<|Y t j<|Y t g<|Y t q<|dT t g x0<|dT t q x0<|dT t h x1<|dT t j x1<|dX) (by decide)
lemma W9 (v:Fin 11):(Finset.univ.filter (G11.Adj v)).card<=4:=by revert v;decide
lemma KX {S:Finset (Fin 11)}(h:2<=S.card): ∃x∈S,∃y∈S,x < y:=by
 have z:1 < S.card:=by omega
 have⟨x,g,y,j,Pt⟩:=Finset.one_lt_card.mp z
 rcases lt_or_gt_of_ne Pt with q|t
 ·exact⟨x,g,y,j,q⟩
 ·exact⟨y,j,x,g,t⟩
lemma Qp {α:Type*}{s:Finset α}(h:s.card<=1){x y:α}(g:x∈s)(j:y∈s):x=y:=Finset.card_le_one.mp h x g y j
lemma Qk {s:Finset (Fin 11)}(h:s.card<=1): ∃c:Fin 11,∀x∈s,x=c:=by
 rcases Eo s with rfl|⟨c,j⟩
 ·exact⟨0,fun _ g=>(N0 g).elim⟩
 ·exact⟨c,fun x g=>Qp h g j⟩
lemma Kq {s A:Finset (Fin 11)}{v:Fin 11}(h:s.card<=1)(g:s⊆A)(q:A.Nonempty)(hv:v∉A): ∃c:Fin 11,c≠v/\∀x∈s,x=c:=by
 rcases Eo s with rfl|⟨c,t⟩
 ·have⟨d,z⟩:=q
  exact⟨d,fun e=>hv (e▸z),fun _ j=>(N0 j).elim⟩
 ·exact⟨c,fun e=>hv (e▸g t),fun x j=>Qp h j t⟩
lemma Qe (j:IsAO2 n C){g:ℕ}(h:g∈junk G C)(d:Fin 2): opnd C g d < n+C.gates.length:=by have h1:=Ku j (Q6 h).1 d;have h2:=(Q6 h).1;omega
lemma Yf (z:IsAO2 n C) {a:ℕ} {Ma Mb:Finset ℕ} {Lb:Finset (Fin n)} {g:ℕ->Fin n} (j:∀m∈Ma,OrReaches n C (n+m) a) (q:∀m∈Mb,g m∈Lb/\∃t∈tops G C,∃d:Fin 2, OrReaches n C (opnd C t d) m/\g m∈side (n:=n) C t (1-d))
  (hnotWa:∀w∈Lb,w∉wmax G C a):Disjoint Ma Mb:=by
 rw[Finset.disjoint_left];intro m a6 a5;have⟨h,t,ht,d,a3,a4⟩:=q m a5;exact hnotWa (g m) h (QY z ht (QH a3 (j m a6)) a4)
lemma Xv {P1 P2:Finset ℕ}{W1 W2:Finset ℕ}{L1 L2 S:Finset (Fin n)}(h1:∀p∈P1,(∃w∈W1,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L1).card)(h2:∀p∈P2,(∃w∈W2,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L2).card)(j:∀w∈W1,orIn n C w⊆S)(g:(S∩L2).card<=1):Disjoint P1 P2:=by
 refine KE h1 h2 (Ql ?_)
 have h:W1.biUnion (orIn n C)∩L2⊆S∩L2:=by intro x hx;have⟨z,q⟩:=Ip hx;have⟨w,hw,t⟩:=Bup z;exact Im (j w hw t) q
 exact(Cl h).trans g
lemma ZR {P1 P2:Finset ℕ}{w1:ℕ}{W2:Finset ℕ}{L1 L2:Finset (Fin n)}(q:∀p∈P1,(∃w∈({w1}:Finset ℕ),OrReaches n C w p)/\1 < (orIn n C (n+p)∩L1).card)(j:∀p∈P2,(∃w∈W2,OrReaches n C w p)/\1 < (orIn n C (n+p)∩L2).card)(g:(orIn n C w1∩L2).card<=1):Disjoint P1 P2:=
 Xv q j (fun z h=>by rw[Sp h]) g
lemma Qd (d:Fin 2):(1:Fin 2)-(1-d)=d:=by fin_cases d<;>rfl
lemma QE {g:ℕ}{da:Fin 2}{x:Fin n}(h:x∈side (n:=n) C g da):
  x∈side (n:=n) C g (1-(1-da)):=by rw[Qd];exact h
lemma K9 (h:IsAO2 n C) (hT:TopForm G C) {a b:ℕ} (hs:junk G C={a,b}) (hab:InCone n C a b) {db:Fin 2} (hrb:OrReaches n C (opnd C b db) a) (da:Fin 2) {w v:Fin n} (g:w∈side (n:=n) C a da) (hwW:w∈wmax G C b)
  (hvA:v∈side (n:=n) C a (1-da)) (hvB:v∈side (n:=n) C b (1-db)):G.Adj w v:=
 VZ h hT hs hab hrb (da:=da) g hwW v hvA hvB
lemma Yh (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a)(hno2:¬OrReaches n C (opnd C b (1-db)) a)(hB0e:side (n:=n) C b db=∅)(x:Fin n->Bool):
  gateVal n C b x=true↔
   gateVal n C a x=true/\∃u∈side (n:=n) C b (1-db),x u=true:=by
 have hb:b∈junk G C:=by simp[hs]
 rw[QF g (Q6 hb).1 (Q6 hb).2.1]
 constructor
 ·intro h
  have h0:=(QD g hT hs hrb x).mp (h db);have j:=(KQ g hT hs hno2 x).mp (h (1-db))
  rcases h0 with ha|⟨u,q,_⟩
  ·exact⟨ha,j⟩
  ·rw[hB0e] at q;exact(N0 q).elim
 ·rintro⟨ha,j⟩ i
  rcases Qn db i with rfl|rfl
  ·exact(QD g hT hs hrb x).mpr (Ql ha)
  ·exact(KQ g hT hs hno2 x).mpr j
lemma VF (g:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a)(hB0e:side (n:=n) C b db=∅):¬Joint G C a b:=by intro h;have hst:=Zu g hT hs hrb h;have Pt:=hst.2.1;rw[hB0e] at Pt;exact Nne Pt
lemma VJ (q:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a)(hno2:¬OrReaches n C (opnd C b (1-db)) a)(hB0e:side (n:=n) C b db=∅):wmax G C a⊆wmax G C b:=by intro w hw;refine Fk (Uv _) (fun x j g=>?_);have h:=((Yh q hT hs hrb hno2 hB0e x).mp j).1;exact(Fp hw).2 x h g
lemma YY (hL:IsLeastAO G C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b}){db:Fin 2}(hrb:OrReaches n C (opnd C b db) a)(hno2:¬OrReaches n C (opnd C b (1-db)) a)(hB0e:side (n:=n) C b db=∅){u v:Fin n}(he:s(u,v)∈Ustar G C):
  gateVal n C a (Pi u v)=true /\
   ((TopCov G C a u\/TopCov G C a v)\/
    ((u∈side (n:=n) C b (1-db)\/v∈side (n:=n) C b (1-db)) /\
     (TopCov G C b u\/TopCov G C b v))):=by
 obtain⟨t,ht,d,j,hj,_,a9,h,a7⟩:=ZD hL hT hs he
 rcases a7 with⟨w,a6,q⟩|⟨hJ,_⟩
 ·have g:TopCov G C j w:=K8 hL.1 hj ht a9 a6
  rcases Kk hs hj with a5|a8
  ·rw[a5] at h g
   refine⟨h,Ql ?_⟩
   rcases q with rfl|rfl<;>[exact Ql g;exact Qr g]
  ·rw[a8] at h g
   obtain⟨hav,⟨z,hzB,hzp⟩⟩:=
    (Yh hL.1 hT hs hrb hno2 hB0e (Pi u v)).mp h
   have a3:u∈side (n:=n) C b (1-db)\/v∈side (n:=n) C b (1-db):=by
    rcases(K4 u v z).mp hzp with rfl|rfl
    ·exact Ql hzB
    ·exact Qr hzB
   refine⟨hav,Qr ⟨a3,?_⟩⟩
   rcases q with rfl|rfl<;>[exact Ql g;exact Qr g]
 ·exact(VF hL.1 hT hs hrb hB0e hJ).elim
lemma Y7 (j:IsAO2 n C)(hT:TopForm G C){a b:ℕ}(hs:junk G C={a,b})(hab:InCone n C a b)(da:Fin 2)(u v:Fin n): gateVal n C a (Pi u v)=true↔ (u∈side (n:=n) C a da\/v∈side (n:=n) C a da) /\
   (u∈side (n:=n) C a (1-da)\/v∈side (n:=n) C a (1-da)):=by
 rw[Qv j hT hs hab];simp only[K4]
 have g (d:Fin 2):(∃x∈side (n:=n) C a d,x=u\/x=v)↔
   u∈side (n:=n) C a d\/v∈side (n:=n) C a d:=by
  constructor
  ·rintro⟨x,hx,rfl|rfl⟩<;>[exact Ql hx;exact Qr hx]
  ·rintro (h|h)<;>[exact⟨u,h,Ql rfl⟩;exact⟨v,h,Qr rfl⟩]
 rw[g 0,g 1]
 fin_cases da
 ·rfl
 ·exact and_comm
lemma X2 (g:IsAO2 n C) (hT:TopForm G C) {a b:ℕ} (hs:junk G C={a,b}) (hab:InCone n C a b) {db:Fin 2} (hrb:OrReaches n C (opnd C b db) a) (hno2:¬OrReaches n C (opnd C b (1-db)) a) (hB0e:side (n:=n) C b db=∅) (da:Fin 2) {u v w:Fin n}
  (hu:u∈side (n:=n) C a da) (hv:v∈side (n:=n) C a (1-da))
  (hw:w∈wmax G C a∪(side (n:=n) C b (1-db)∩wmax G C b)):
  G.Adj u v\/G.Adj u w\/G.Adj v w:=by
 have h:gateVal n C a (QW u v w)=true:=by
  rw[Qv g hT hs hab]
  fin_cases da
  ·exact⟨⟨u,hu,tripleInput_1 u v w⟩,⟨v,hv,tripleInput_2 u v w⟩⟩
  ·exact⟨⟨v,hv,tripleInput_2 u v w⟩,⟨u,hu,tripleInput_1 u v w⟩⟩
 rcases Up hw with q|t
 ·exact Ka q h
 ·have⟨a3,j⟩:=Ip t
  have z:gateVal n C b (QW u v w)=true:=
   (Yh g hT hs hrb hno2 hB0e _).mpr ⟨h,w,a3,XZ u v w⟩
  exact Ka j z
lemma Xr (g:IsAO2 n C) (hT:TopForm G C) {a b:ℕ} (hs:junk G C={a,b}) (hab:InCone n C a b) {db:Fin 2} (hrb:OrReaches n C (opnd C b db) a) (hno2:¬OrReaches n C (opnd C b (1-db)) a) (hB0e:side (n:=n) C b db=∅) {v y w:Fin n}
  (Pv:v∈side (n:=n) C a 0) (Pu:v∈side (n:=n) C a 1)
  (hyB:y∈side (n:=n) C b (1-db)) (hwW:w∈wmax G C b):
  G.Adj v y\/G.Adj v w\/G.Adj y w:=by
 have j:gateVal n C a (QW v y w)=true:=
  (Qv g hT hs hab _).mpr ⟨⟨v,Pv,tripleInput_1 v y w⟩,⟨v,Pu,tripleInput_1 v y w⟩⟩
 have h:gateVal n C b (QW v y w)=true:=
  (Yh g hT hs hrb hno2 hB0e _).mpr ⟨j,y,hyB,tripleInput_2 v y w⟩
 exact Ka hwW h
lemma Qy (g:IsAO2 n C){m j:ℕ}(q:m∈mixing G C)(h:j∈junk G C)(hr:OrReaches n C (n+m) j):j < m:=by
 have hm':m < C.gates.length/\(gateAt C m).op=GateOp.or:=by have h1:=(Fp q).1;simp only[orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at h1;exact⟨h1.1,h1.2.1⟩
 obtain⟨_,heq|⟨_,i,hi,_,hri⟩⟩:=(QT n C m j).mp hr
 ·subst heq;have:=(Q6 h).2.1;rw[hm'.2] at this;cases this
 ·obtain⟨d,rfl⟩:=KM g hm'.1 hi;exact KK g hm'.1 hri
lemma KH {E:Finset (Sym2 (Fin 11))}(h:E⊆Us C)(c:Fin 11): (Q4 c E).card<=4:=by
 have g:Q4 c E⊆Finset.univ.filter (G11.Adj c):=fun x j=>
  Fk (Uv _) (Eg (Dp (h (Zl j))).1)
 exact(Cl g).trans (W9 c)
structure StarSpec (C:Ck) where
 c:Fin 11
 L:Finset (Fin 11)
 W:Finset ℕ
 hW:∀w∈W,w < 11+C.gates.length
 hL:L⊆W.biUnion (Oi C)
 he:∀x∈L,s(c,x)∈Us C
 good:Prop
 hgood:good->∀w∈W,∀x∈Oi C w,Ga c x
abbrev St(C:Ck):=StarSpec C
def Q0 (C:Ck)(c:Fin 11)(L:Finset (Fin 11))(w:ℕ)(hw:w < 11+C.gates.length)(hL:L⊆Oi C w)(he:∀x∈L,s(c,x)∈Us C)(good:Prop)(hgood:good->∀x∈Oi C w,Ga c x):St C where
 c:=c;L:=L;W:={w}
 hW:=fun z hz=>by rw[Sp hz];exact hw
 hL:=by simpa using hL
 he:=he;good:=good
 hgood:=fun hg z hz x hx=>by rw[Sp hz] at hx;exact hgood hg x hx
def Q9 (hAO:Ao C){g:ℕ}(hg:g∈Jk C)(d:Fin 2)(c:Fin 11)(hcS:c∈N C g d)(hcW:c∈Mw C g)(E:Finset (Sym2 (Fin 11)))(hEU:E⊆Us C):St C:=
 Q0 C c (Q4 c E∩N C g (1-d)) (opnd C g (1-d))
  (Qe hAO hg (1-d)) Ir
  (fun _ hx=>hEU (Zl (I1 hx))) True
  (fun _ x hx=>QC hAO hg hcS hcW x hx)
lemma Qf {α β:Type}[DecidableEq β](f:α->Finset β): ∀(l:List α) (x:β),x∈l.foldr (fun a g=>f a∪g) ∅↔∃a∈l,x∈f a
 | [],_=>by simp
 | a::t,x=>by simp[Qf f t x]
lemma Zd {α β:Type}[DecidableEq β](f:α->Finset β): ∀(l:List α),(l.foldr (fun a g=>f a∪g) ∅).card<=(l.map (fun a=>(f a).card)).sum
 | []=>by simp
 | a::t=>by simp only[List.foldr_cons,Lmc,Lsc];exact(Cu _ _).trans (A2l (Zd f t) _)
lemma Kg (h:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b)(d:Fin 2){u v:Fin 11}(g:Gv C a (Pi u v)=true)(j:u∉N C a d): v∈N C a d:=
 ((Y7 h hT hs hab d u v).mp g).1.resolve_left j
lemma Qt (j:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){u v:Fin 11}(t:Gv C a (Pi u v)=true)(z:u∉N C a 0∩N C a 1)(hv:v∉N C a 0∩N C a 1): (u∈N C a 0/\v∈N C a 1)\/ (u∈N C a 1/\v∈N C a 0):=by
 obtain⟨h0,q⟩:=(Y7 j hT hs hab 0 u v).mp t;change u∈N C a 1\/v∈N C a 1 at q
 rcases h0 with h|Pv<;>rcases q with g|Pu
 ·exact(z (Im h g)).elim
 ·exact Ql ⟨h,Pu⟩
 ·exact Qr ⟨g,Pv⟩
 ·exact(hv (Im Pv Pu)).elim
lemma YA (aq:Ao C) (items:List (St C)) (X:Fin 11->Finset (Fin 11)) (ag:∀c,X c⊆((items.filter (fun (it:St C)=>it.c==c)).foldr (fun (it:St C) ad=>it.W∪ad) ∅).biUnion (Oi C))
  (h:∀c,∀x∈X c,Ga c x)
  (a7:∀c,∃gh:Fin 11,∀x∈X c,x≠gh->s(c,x)∈Us C)
  (ah:∀it1∈items,∀it2∈items,it1.c≠it2.c ->
   (∀i∈items,i.c=it1.c->i.good)\/
   (∀i∈items,i.c=it2.c->i.good)\/
   ((∀i∈items,i.c=it1.c->i=it1)/\(∀j∈items,j.c=it2.c->j=it2) /\
    ((it1.W.biUnion (Oi C)∩X it2.c).card<=1\/(it2.W.biUnion (Oi C)∩X it1.c).card<=1))):
  ∑c∈(items.map StarSpec.c).toFinset,(X c).card<=(rFull G11 C).card+(items.map (fun it=>it.W.card)).sum:=by
 classical
 let g:Finset (Fin 11):=(items.map StarSpec.c).toFinset;let z (c:Fin 11):=items.filter (fun it=>it.c==c);let Wc (c:Fin 11):Finset ℕ:=(z c).foldr (fun it ad=>it.W∪ad) ∅;have hmem_grp {c:Fin 11} {it}:it∈z c↔it∈items/\it.c=c:=by simp[z]
 have af (c:Fin 11):∀w∈Wc c,w < 11+C.gates.length:=fun w hw=>by obtain⟨it,Px,q⟩:=(Qf StarSpec.W (z c) w).mp hw;exact it.hW w q
 have ak:∀c:Fin 11,∃P⊆rFull G11 C,(X c).card<=P.card+(Wc c).card /\
   ∀p∈P,(∃w∈Wc c,O C w p)/\1 < (Oi C (11+p)∩X c).card:=fun c=>by
  have⟨gh,an⟩:=a7 c;exact Yv aq Q3 (af c) (ag c) (h c) gh an
 choose Pc hPc_sub hPc_card hPc_spec using ak
 have a4:Set.PairwiseDisjoint (g:Set (Fin 11)) Pc:=by
  intro c1 ay c2 ar Pt;obtain⟨it1,al,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ay);obtain⟨it2,am,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ar)
  have ac (c:Fin 11) (hg:∀i∈items,i.c=c->i.good):∀w∈Wc c,∀x∈Oi C w,Ga c x:=fun w hw x hx=>by obtain⟨it,Px,q⟩:=(Qf StarSpec.W (z c) w).mp hw;have⟨a6,a3⟩:=hmem_grp.mp Px;exact a3▸it.hgood (hg it a6 a3) w q x hx
  rcases ah it1 al it2 am Pt with ax|av|⟨aw,au,ap⟩
  ·exact Kw Q3 Pt (hPc_spec it1.c) (hPc_spec it2.c) (ac it1.c ax) (h it2.c)
  ·exact(Kw Q3 Pt.symm (hPc_spec it2.c) (hPc_spec it1.c) (ac it2.c av) (h it1.c)).symm
  ·have a8 {it0:St C} (hu:∀i∈items,i.c=it0.c->i=it0):Wc it0.c⊆it0.W:=fun w hw=>by
    obtain⟨it,Px,q⟩:=(Qf StarSpec.W (z it0.c) w).mp hw;have⟨a6,a3⟩:=hmem_grp.mp Px;rwa[hu it a6 a3] at q
   refine KE (hPc_spec it1.c) (hPc_spec it2.c) ?_
   rcases ap with hs|hs
   ·exact Ql ((Cl (Isi (Bub _ (a8 aw)) (Sr _))).trans hs)
   ·exact Qr ((Cl (Isi (Bub _ (a8 au)) (Sr _))).trans hs)
 have ae:∑c∈g,(Pc c).card<=(rFull G11 C).card:=by rw[←Finset.card_biUnion a4];exact Cl (Finset.biUnion_subset.mpr fun c _=>hPc_sub c)
 have a9:∑c∈g,(Wc c).card<=(items.map (fun it=>it.W.card)).sum:=by
  have h1:=Sls fun c (_:c∈g)=>Zd StarSpec.W (z c)
  have h2:∀(l:List (St C)),(∀it∈l,it.c∈g) ->
    ∑c∈g,((l.filter (fun it=>it.c==c)).map (fun it=>it.W.card)).sum=(l.map (fun it=>it.W.card)).sum:=by
   intro l;induction l with
   | nil=>intro _;simp
   | cons a t ih=>
    intro ab;have ha:=ab a (Kc);have ht:∀it∈t,it.c∈g:=fun it Px=>ab it (Km _ Px);simp only[List.filter_cons,Lmc,Lsc]
    have az:∀c∈g,
      ((if (a.c==c)=true then a::t.filter (fun it=>it.c==c) else t.filter (fun it=>it.c==c)).map (fun it=>it.W.card)).sum=
      (if c=a.c then a.W.card else 0)+((t.filter (fun it=>it.c==c)).map (fun it=>it.W.card)).sum:=by
     intro c _;by_cases aa:c=a.c;· subst aa;simp
     ·simp[Bf (Ne.symm aa),aa]
    rw[Finset.sum_congr rfl az,Finset.sum_add_distrib,ih ht];simp[ha]
  exact h1.trans_eq (h2 items fun it Px=>Mtf (List.mem_map.mpr ⟨it,Px,rfl⟩))
 have hsum:∑c∈g,(X c).card<=(∑c∈g,(Pc c).card)+(∑c∈g,(Wc c).card):=
  (Sls fun c _=>hPc_card c).trans_eq Finset.sum_add_distrib
 exact hsum.trans (Nat.add_le_add ae a9)
lemma Z3 (ad:Ao C){E:Finset (Sym2 (Fin 11))}(items:List (St C))(aa:∀e∈E,∃it∈items,∃x∈it.L,e=s(it.c,x))(a3:∀it1∈items,∀it2∈items,it1.c≠it2.c -> (∀i∈items,i.c=it1.c->i.good)\/ (∀i∈items,i.c=it2.c->i.good)\/ ((∀i∈items,i.c=it1.c->i=it1)/\(∀j∈items,j.c=it2.c->j=it2) /\ ((it1.W.biUnion (Oi C)∩it2.L).card<=1\/(it2.W.biUnion (Oi C)∩it1.L).card<=1))): E.card<=(rFull G11 C).card+(items.map (fun it=>it.W.card)).sum:=by
 classical
 let g (c:Fin 11):=items.filter (fun it=>it.c==c);let z (c:Fin 11):Finset (Fin 11):=(g c).foldr (fun it ag=>it.L∪ag) ∅;have hmg {c:Fin 11} {it}:it∈g c↔it∈items/\it.c=c:=by simp[g]
 have q (c:Fin 11):∀x∈z c,s(c,x)∈Us C:=fun x h=>by obtain⟨it,Px,t⟩:=(Qf StarSpec.L (g c) x).mp h;obtain⟨_,rfl⟩:=hmg.mp Px;exact it.he x t
 have a4:E⊆(items.map StarSpec.c).toFinset.biUnion (fun c=>(z c).image (fun x=>s(c,x))):=fun e he=>by
  obtain⟨it,Px,x,h,rfl⟩:=aa e he
  exact Mbu ⟨it.c,Mtf (List.mem_map.mpr ⟨it,Px,rfl⟩),
   Mi ⟨x,(Qf StarSpec.L (g it.c) x).mpr ⟨it,hmg.mpr ⟨Px,rfl⟩,h⟩,rfl⟩⟩
 have hE_le:E.card<=∑c∈(items.map StarSpec.c).toFinset,(z c).card:=
  (Cl a4).trans (Cbu.trans (Sls fun _ _=>Ci))
 refine hE_le.trans (YA ad items z (fun c x h=>by
   obtain⟨it,Px,t⟩:=(Qf StarSpec.L (g c) x).mp h;have⟨w,hw,ac⟩:=Bup (it.hL t)
   exact Mbu ⟨w,(Qf StarSpec.W (g c) w).mpr ⟨it,Px,hw⟩,ac⟩)
  (fun c x h=>Eg (Dp (q c x h)).1)
  (fun c=>⟨c,fun x h _=>q c x h⟩) fun it1 h1 it2 h2 Pt=>?_)
 rcases a3 it1 h1 it2 h2 Pt with af|ae|⟨a6,a5,ab⟩
 ·exact Ql af
 ·exact Qr (Ql ae)
 ·have a7 {it0:St C} (hu:∀i∈items,i.c=it0.c->i=it0):z it0.c⊆it0.L:=fun x h=>by
   obtain⟨it,Px,t⟩:=(Qf StarSpec.L (g it0.c) x).mp h;have⟨a9,a8⟩:=hmg.mp Px;rwa[hu it a9 a8] at t
  refine Qr (Qr ⟨a6,a5,?_⟩)
  rcases ab with hs|hs
  ·exact Ql ((Cl (Isi (Sr _) (a7 a5))).trans hs)
  ·exact Qr ((Cl (Isi (Sr _) (a7 a6))).trans hs)
lemma Qw (z:Ao C){E:Finset (Sym2 (Fin 11))}(g:Fin 11)(items:List (St C))(j:∀e∈E,∃it∈items,∃x∈it.L,e=s(it.c,x))(h:∀it∈items,it.c≠g->it.good): E.card<=(rFull G11 C).card+(items.map (fun it=>it.W.card)).sum:=
 Z3 z items j fun it1 _ a4 _ Pt=>by
  by_cases h1:it1.c≠g
  ·exact Ql fun i q t=>h i q (t▸h1)
  ·exact Qr (Ql fun i q t=>h i q (t▸fun e=>Pt (by rw[not_not.mp h1,e])))
lemma QU (ag:Ao C){c:Fin 11}{L:Finset (Fin 11)}{W_c M_cand:Finset ℕ}(ak:M_cand⊆mixing G11 C)(q:∀w∈L,s(c,w)∈Us C)(ad:∀w∈L,w∈W_c.biUnion (Oi C)\/ ∃t∈Tp C,∃d:Fin 2,∃m∈M_cand, O C (opnd C t d) m/\w∈N C t (1-d)): ∃L0 Lm:Finset (Fin 11),∃M⊆M_cand, L=L0∪Lm/\L0⊆L/\L0⊆W_c.biUnion (Oi C)/\Lm.card=M.card /\ (∃fw:ℕ->Fin 11, (∀m∈M,fw m∈L/\∃t∈Tp C,∃d:Fin 2, O C (opnd C t d) m/\fw m∈N C t (1-d)) /\ (∀m1∈M,∀m2∈M,m1≠m2->fw m1≠fw m2)):=by
 classical
 let L0:=L.filter fun w=>w∈W_c.biUnion (Oi C);let Lm:=L\L0
 have z:∀w∈Lm,∃m∈M_cand,∃t∈Tp C,∃d:Fin 2,
   O C (opnd C t d) m/\w∈N C t (1-d):=fun w hw=>by
  have⟨aa,a5⟩:=Dp hw
  rcases ad w aa with h|⟨t,ht,d,m,g,j,ah⟩
  ·exact(a5 (Fk aa h)).elim
  ·exact⟨m,g,t,ht,d,j,ah⟩
 choose f hfM ft hft fd hfr hfw using z
 let M:Finset ℕ:=Lm.attach.image fun w=>f w.1 w.2;have a8:M⊆M_cand:=fun m g=>by obtain⟨w,_,rfl⟩:=Mip g;exact hfM w.1 w.2
 have a4:Set.InjOn (fun w:{x // x∈Lm}=>f w.1 w.2) Lm.attach:=fun w1 _ w2 _ ab=>by
  have ac:O C (opnd C (ft w2.1 w2.2) (fd w2.1 w2.2)) (f w1.1 w1.2):=by have heq':f w1.1 w1.2=f w2.1 w2.2:=ab;rw[heq'];exact hfr w2.1 w2.2
  exact Subtype.ext (Yp ag Q3 (ak (hfM w1.1 w1.2))
   (hft w1.1 w1.2) (hft w2.1 w2.2) (hfr w1.1 w1.2) ac
   (hfw w1.1 w1.2) (hfw w2.1 w2.2) (q w1.1 (Dp w1.2).1)
   (q w2.1 (Dp w2.2).1))
 have hMcard:M.card=Lm.card:=by rw[Finset.card_image_of_injOn a4,Finset.card_attach]
 have a7:∀m,∃w:Fin 11,m∈M->∃hw:w∈Lm,f w hw=m:=fun m=>by
  by_cases g:m∈M
  ·obtain⟨⟨w,hw⟩,_,rfl⟩:=Mip g;exact⟨w,fun _=>⟨hw,rfl⟩⟩
  ·exact⟨c,fun h=>(g h).elim⟩
 choose fw hfw_spec using a7
 refine⟨L0,Lm,M,a8,(Finset.union_sdiff_of_subset (Fs _ _)).symm,
  Fs _ _,fun _ hw=>(Fp hw).2,hMcard.symm,fw,?_,?_⟩
 ·intro m g;have⟨hw,ae⟩:=hfw_spec m g
  have j:=hfr (fw m) hw;rw[ae] at j
  exact⟨(D1 hw),ft (fw m) hw,hft (fw m) hw,fd (fw m) hw,j,hfw (fw m) hw⟩
 ·intro m1 af m2 aj Pt ab;obtain⟨_,e1⟩:=hfw_spec m1 af;obtain⟨_,e2⟩:=hfw_spec m2 aj;exact Pt (by rw[←e1,←e2];congr 1)
lemma QN (a3:Ao C){b g:ℕ}(hb:b∈Jk C)(h:g∈mixing G11 C)(a6:g < b)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): 2<=2*(centreless G11 C).card+(mixing G11 C).card:=by
 have h1:1<=(mixing G11 C).card:=Cpr ⟨g,h⟩
 rcases hbWit with a5|⟨mt,j,t⟩
 ·have h2:1<=(T0For G11 C b).card:=Cpr a5
  have h3:=Qs (G:=G11) (C:=C) b;omega
 ·have a8:=Qy a3 j hb t
  have q:({g,mt}:Finset ℕ)⊆mixing G11 C:=by
   intro x z;rcases Nsp z with rfl|z
   ·exact h
   ·rw[Sp z];exact j
  have hc:=Cl q;rw[Cp (by omega:g≠mt)] at hc;omega
lemma KF (a6:Ao C){b mb:ℕ}{db:Fin 2}(hb:b∈Jk C)(aa:mb∈mixing G11 C)(a5:Oi C (11+mb)⊆N C b db){v g w:Fin 11}(j:v∉N C b db)(a4:g∈N C b (1-db))(a3:g∈Mw C b)(hv_cb1:Ga v g)(hv_w:Ga v w)(Pt:w≠g){t:ℕ}{d:Fin 2}(ht:t∈Tp C)(hr:O C (opnd C t d) mb)(hw:w∈N C t (1-d)):False:=by
 have⟨z0,a8⟩:=KZ a6 aa;have h:=a5 a8;have hz0_ne_v:z0≠v:=fun e=>j (e▸h);have z:=QC a6 hb a4 a3 z0 (QE h);have hz0_w:=YZ a6 ht (QJ hr a8) hw;have h2:2<=({v,z0}:Finset (Fin 11)).card:=by rw[Cp hz0_ne_v.symm]
 exact Pt (YD Q3 (X:={v,z0}) (a:=w) (b:=g) h2
  (fun x q=>by
   rcases Nsp q with rfl|q
   ·exact hv_w.symm
   ·rw[Sp q];exact hz0_w.symm)
  (fun x q=>by
   rcases Nsp q with rfl|q
   ·exact hv_cb1.symm
   ·rw[Sp q];exact z))
lemma Xa (a6:Ao C){a b mb:ℕ}(ha:a∈Jk C)(hb:b∈Jk C)(Pt:a≠b)(ac:mb∈mixing G11 C)(ay:mb < b){c:Fin 11}{L:Finset (Fin 11)}{M:Finset ℕ}{fw:ℕ->Fin 11}(hM:M⊆mixing G11 C)(aw:∀m∈M,O C (11+m) a)(a7:∀w∈L,s(c,w)∈Us C)(ah:∀m∈M,fw m∈L/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw m∈N C t (1-d))(al:∀m1∈M,∀m2∈M,m1≠m2->fw m1≠fw m2)(h:∀w∈L,∀t∈Tp C,∀d:Fin 2,O C (opnd C t d) mb->w∈N C t (1-d)->False)(hbWit:(T0For G11 C b).Nonempty\/∃mt∈mixing G11 C,O C (11+mt) b): (W0For G11 C a).card+M.card+2 <= 2*(centreless G11 C).card+(mixing G11 C).card+(rZero G11 C).card:=by
 have g:mb∉M:=fun ax=>by have⟨az,t,ht,d,b4,b3⟩:=ah mb ax;exact h _ az t ht d b4 b3
 have bb:M.card+1<=(mixing G11 C).card:=by have hc:=Cl (Ism ⟨ac,hM⟩);rw[Cns g] at hc;exact hc
 rcases hbWit with b6|⟨mt,ae,ab⟩
 ·by_cases a3:(T0For G11 C a∩T0For G11 C b).Nonempty
  ·have an:=Cpr (YK a6 ha hb Pt a3)
   have hw:=(Qj (G:=G11) (C:=C) a).trans (Qs a);omega
  ·have b9:(T0For G11 C a).card+(T0For G11 C b).card<=(centreless G11 C).card:=
    Yq (Fs _ _) (Fs _ _) (Finset.disjoint_iff_inter_eq_empty.mpr (Nne2 a3))
   have h1:=Cpr b6;have hw:=Qj (G:=G11) (C:=C) a;omega
 ·have hw:=(Qj (G:=G11) (C:=C) a).trans (Qs a)
  have b7:=Qy a6 ae hb ab
  by_cases q:mt∈M
  ·rcases Yd a6 ha hb Pt ae (aw mt q) ab with an|⟨m',a4,hne_m,j⟩
   ·have:=Cpr an;omega
   ·have⟨aj,t0,ap,d0,af,ad⟩:=ah mt q
    have a5:m'∉M:=fun ag=>by have⟨av,t',b5,d',ar,aq⟩:=ah m' ag;exact al mt q m' ag hne_m.symm (Yp a6 Q3 a4 ap b5 (QH af j) ar ad aq (a7 _ aj) (a7 _ av))
    have z:m'≠mb:=fun e=>h _ aj t0 ap d0 (e▸QH af j) ad;have hc:=Cl (Ism ⟨a4,Ism ⟨ac,hM⟩⟩)
    rw[Cns (by simp[z,a5]),Cns g] at hc;omega
  ·have hc:=Cl (Ism ⟨ae,Ism ⟨ac,hM⟩⟩);rw[Cns (by simp[q];omega),Cns g] at hc;omega
lemma Y0 (a8:Ao C){a b:ℕ}(ha:a∈Jk C)(hb:b∈Jk C)(Pt:a≠b){v vb:Fin 11}(bn:v≠vb)(bg:∀w∈Mw C a,Ga v w){La Lb:Finset (Fin 11)}{Ma Mb:Finset ℕ}{au ab:ℕ->Fin 11}(a5:Ma⊆mixing G11 C)(av:∀m∈Ma,O C (11+m) a)(a6:Mb⊆mixing G11 C)(aw:∀m∈Mb,O C (11+m) b)(b9:∀w∈La,s(v,w)∈Us C)(am:∀w∈Lb,s(vb,w)∈Us C)(ad:∀m∈Ma,au m∈La/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\au m∈N C t (1-d))(aj:∀m1∈Ma,∀m2∈Ma,m1≠m2->au m1≠au m2)(al:∀m∈Mb,ab m∈Lb/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\ab m∈N C t (1-d))(a4:∀m1∈Mb,∀m2∈Mb,m1≠m2->ab m1≠ab m2): Ma.card+Mb.card<=(mixing G11 C).card+(rZero G11 C).card /\ ∀z∈mixing G11 C,z < b -> (∀w∈La,∀t∈Tp C,∀d:Fin 2,O C (opnd C t d) z->w∈N C t (1-d)->False) -> Ma.card+Mb.card+1<=(mixing G11 C).card+(rZero G11 C).card:=by
 have ay:(Ma∩Mb).card<=1:=by
  by_contra! h;have⟨m1,bj,m2,bl,bh⟩:=Finset.one_lt_card.mp h
  have az (m:ℕ) (hm:m∈Ma∩Mb):ab m∈Finset.univ.filter (fun x=>G11.Adj v x/\G11.Adj vb x):=by
   have⟨ah,tb,ba,c9,af,aq⟩:=al m (I2 hm)
   exact Fm ⟨Uv _,bg _ (QY a8 ba (QH af (av m (I1 hm))) aq),
    Eg (Dp (am _ ah)).1⟩
  exact a4 m1 (I2 bj) m2 (I2 bl) bh (Qp (Q3 v vb bn) (az m1 bj) (az m2 bl))
 have j:Ma∪Mb⊆mixing G11 C:=Us2 a5 a6;have bp:=Cui Ma Mb
 have ar (extra:Option {z:ℕ // z∈mixing G11 C/\z < b /\
   ∀w∈La,∀t∈Tp C,∀d:Fin 2,O C (opnd C t d) z->w∈N C t (1-d)->False}):
   Ma.card+Mb.card+(if extra.isSome then 1 else 0)<=(mixing G11 C).card+(rZero G11 C).card:=by
  have a9 (e:{z:ℕ // z∈mixing G11 C/\z < b/\∀w∈La,∀t∈Tp C,∀d:Fin 2,O C (opnd C t d) z->w∈N C t (1-d)->False}):e.1∉Ma∪Mb:=fun hU=>by
   rcases Up hU with hA|hB
   ·have⟨bt,t,ht,d,bv,bu⟩:=ad e.1 hA;exact e.2.2.2 _ bt t ht d bv bu
   ·have:=Qy a8 (a6 hB) hb (aw e.1 hB);omega
  have c3:(Ma∪Mb).card+(if extra.isSome then 1 else 0)<=(mixing G11 C).card:=by
   cases extra with
   | none=>have:=Cl j;simp;omega
   | some e=>have hc:=Cl (Ism ⟨e.2.1,j⟩);rw[Cns (a9 e)] at hc;simp;omega
  rcases Eo (Ma∩Mb) with bz|⟨m0,b4⟩
  ·have:(Ma∩Mb).card=0:=by rw[bz,Finset.card_empty]
   omega
  ·have ca:(Ma∩Mb).card=1:=le_antisymm ay (Cpr ⟨m0,b4⟩)
   have a7:=(I1 b4);have ag:=(I2 b4)
   rcases Yd a8 ha hb Pt (a5 a7) (av m0 a7) (aw m0 ag) with bs|⟨m',q,hne_m,g⟩
   ·have:=Cpr bs;omega
   ·have⟨b8,ta,bk,da,bb,b5⟩:=ad m0 a7;have⟨ah,tb,ba,db,af,aq⟩:=al m0 ag
    have a3:m'∉Ma∪Mb:=fun hU=>by
     rcases Up hU with hA|hB
     ·have⟨ap,t',b7,d',an,ae⟩:=ad m' hA
      exact aj m0 a7 m' hA hne_m.symm (Yp a8 Q3 q bk b7 (QH bb g) an b5 ae (b9 _ b8) (b9 _ ap))
     ·have⟨ap,t',b7,d',an,ae⟩:=al m' hB;exact a4 m0 ag m' hB hne_m.symm (Yp a8 Q3 q ba b7 (QH af g) an aq ae (am _ ah) (am _ ap))
    cases extra with
    | none=>have hc:=Cl (Ism ⟨q,j⟩);rw[Cns a3] at hc;simp;omega
    | some e=>
     have bf:m'≠e.1:=fun eq=>e.2.2.2 _ b8 ta bk da (eq▸QH bb g) b5;have hc:=Cl (Ism ⟨q,Ism ⟨e.2.1,j⟩⟩);rw[Cns (by simp[bf,a3]),Cns (a9 e)] at hc;simp;omega
 exact⟨by simpa using ar none,fun z br bq bx=>by simpa using ar (some ⟨z,br,bq,bx⟩)⟩
lemma Kj (ad:Ao C){a b:ℕ}(ha:a∈Jk C)(hb:b∈Jk C)(Pt:a≠b){v vb:Fin 11}(a7:v≠vb)(a6:∀w∈Mw C a,Ga v w)(ae:∀w∈Mw C b,Ga vb w){La Lb:Finset (Fin 11)}{Ma Mb:Finset ℕ}{q j:ℕ->Fin 11}(a3:Ma⊆mixing G11 C)(a5:∀m∈Ma,O C (11+m) a)(z:Mb⊆mixing G11 C)(a4:∀m∈Mb,O C (11+m) b)(ab:∀w∈La,s(v,w)∈Us C)(ac:∀w∈Lb,s(vb,w)∈Us C)(a8:∀m∈Ma,q m∈La/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\q m∈N C t (1-d))(h:∀m1∈Ma,∀m2∈Ma,m1≠m2->q m1≠q m2)(a9:∀m∈Mb,j m∈Lb/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\j m∈N C t (1-d))(g:∀m1∈Mb,∀m2∈Mb,m1≠m2->j m1≠j m2): Ma.card+Mb.card<=(mixing G11 C).card+(rZero G11 C).card /\ ∀mb∈mixing G11 C,mb < b -> (∀w∈La,∀t∈Tp C,∀d:Fin 2,O C (opnd C t d) mb->w∈N C t (1-d)->False) -> Ma.card+Mb.card+1<=(mixing G11 C).card+(rZero G11 C).card:=
 Y0 ad ha hb Pt a7 a6 a3 a5 z a4 ab ac a8 h a9 g
def Z7:=Yg (dF fun v=>dN v fun c0=>dN v fun c1=>dN v fun g=>dA c0 c1<|Y g c0<|Y g c1<|dN c1 fun u=>Y u v<|Y u c0<|dN c0 fun y=>Y y v<|Y y c1<|dT u y g<|dX) (by decide)
def XD:=Yg (dF fun w0=>dN w0 fun MP=>dN w0 fun h=>Y h MP<|dN w0 fun t=>dN t fun q=>Y q w0<|Y q MP<|Y q h<|dN t fun j=>Y j w0<|Y j MP<|Y j h<|Y j q<|dT j q w0<|dN q fun x0=>Y x0 w0<|Y x0 t<|Y x0 MP<|Y x0 h<|Y x0 q<|Y x0 j<|dT MP j x0<|dT h j x0<|dN j fun g=>Y g w0<|Y g t<|Y g MP<|Y g h<|Y g q<|Y g j<|Y g x0<|dT x0 g w0<|dT MP q g<|dT h q g<|dX) (by decide)
def Xe:=Yg (dF fun c0=>dN c0 fun q=>dN c0 fun g=>Y g q<|dN q fun x0=>Y x0 c0<|Y x0 q<|Y x0 g<|dN g fun j=>Y j c0<|Y j q<|Y j g<|Y j x0<|dN q fun t=>dA t j<|Y t x0<|Y t g<|dN t fun h=>Y h q<|Y h j<|Y h x0<|Y h g<|dT x0 g h<|dT j q h<|dX) (by decide)
def Xz:=Yg (dF fun z=>dN z fun x0=>dN z fun g=>Y g x0<|dN z fun h=>Y h x0<|Y h g<|dT x0 g h<|dN x0 fun j=>Y j z<|Y j x0<|Y j g<|Y j h<|dN g fun q=>Y q z<|Y q x0<|Y q g<|Y q h<|Y q j<|dT q j h<|dN j fun c0=>dA c0 g<|Y c0 x0<|Y c0 j<|Y c0 g<|Y c0 q<|dN h fun t=>Y t z<|Y t j<|Y t q<|VT t x0 t q x0<|VT t g t j g<|dX) (by decide)
def ZT:=Yg (dF fun v=>dN v fun x0=>dN v fun g=>Y g x0<|dN v fun h=>Y h x0<|Y h g<|dT x0 g h<|dN v fun z=>Y z x0<|Y z g<|Y z h<|dT x0 g z<|dN x0 fun q=>Y q v<|Y q x0<|Y q g<|Y q h<|Y q z<|dN g fun j=>Y j v<|Y j x0<|Y j g<|Y j h<|Y j z<|Y j q<|dT j q h<|dT j q z<|dN h fun t=>Y t v<|Y t x0<|Y t g<|Y t h<|Y t q<|Y t j<|dT t q g<|dT t j x0<|dX) (by decide)
def XS:=Yg (dF fun v=>dN v fun c0=>dN v fun q=>Y q c0<|dN c0 fun h=>Y h v<|Y h q<|dN c0 fun g=>Y g v<|Y g q<|Y g h<|dT v h g<|dN h fun x0=>Y x0 v<|Y x0 c0<|Y x0 q<|Y x0 h<|Y x0 g<|dT x0 g q<|dN g fun j=>Y j v<|Y j c0<|Y j q<|Y j h<|Y j g<|Y j x0<|dT j h q<|dT v j x0<|dX) (by decide)
def Xn:=Yg (dF fun v=>dN v fun c0=>dN v fun q=>Y q c0<|dN c0 fun j=>Y j v<|Y j q<|dN c0 fun g=>Y g v<|Y g q<|Y g j<|dN j fun x0=>Y x0 v<|Y x0 c0<|Y x0 q<|Y x0 j<|Y x0 g<|dT x0 g q<|dN g fun h=>Y h v<|Y h c0<|Y h q<|Y h j<|Y h g<|Y h x0<|dT h j q<|dN j fun t=>dA t h<|Y t x0<|Y t g<|dX) (by decide)
def Xu:=Yg (dF fun v=>dN v fun q=>dN v fun j=>Y j q<|dN v fun h=>Y h q<|Y h j<|dT j q h<|dN q fun x0=>Y x0 v<|Y x0 q<|Y x0 j<|Y x0 h<|dN j fun g=>Y g v<|Y g q<|Y g j<|Y g h<|Y g x0<|dT x0 g h<|dN h fun t=>Y t v<|Y t q<|Y t j<|VT t x0 t j x0<|VT t g t q g<|dX) (by decide)
lemma KN (j:Ao C){g:ℕ}(hg:g∈Jk C){v c0 c1 w3:Fin 11}(ac:c0∈(N C g 0\N C g 1)∩Mw C g)(ab:c1∈(N C g 1\N C g 0)∩Mw C g)(am:w3∈Mw C g)(af:Ga v c0)(al:Ga v c1)(ae:Ga v w3)(ah:w3≠c0)(ag:w3≠c1): (N C g 0\N C g 1)\{v}⊆{c0}\/ (N C g 1\N C g 0)\{v}⊆{c1}:=by
 by_contra h
 have⟨u,hu,a5⟩:=Nss (fun e=>h (Ql e));have⟨y,hy,a4⟩:=Nss (fun e=>h (Qr e));rw[Finset.mem_singleton] at a5 a4;have⟨aj,a9⟩:=Dp hu;have⟨ak,aa⟩:=Dp hy;rw[Finset.mem_singleton] at a9 aa;have z:=(J1 ac);have t:=(I2 ac);have q:=(J1 ab);have a7:=(I2 ab);have ad:=(D1 aj);have a8:=(D1 ak)
 have an:=KV j (Q6 hg).1 (Q6 hg).2.1 ad a8
  (tripleInput_1 u y w3) (tripleInput_2 u y w3)
 exact Z7 af al ae (QC j hg z t c1 q)
  ah ag (QC j hg q a7 u ad) a9 a5
  (QC j hg z t y a8) aa a4 (Ka am an)
lemma KJ (a4:Ao C){g:ℕ}(hg:g∈Jk C)(aq:N C g 0∩N C g 1=∅){E:Finset (Sym2 (Fin 11))}(z:E⊆Us C)(hE:∀u v:Fin 11,s(u,v)∈E -> ((u∈N C g 0/\v∈N C g 1)\/ (u∈N C g 1/\v∈N C g 0)) /\ (u∈Mw C g\/v∈Mw C g)): (∃it:St C,it.W.card=1/\it.L.card<=4/\∀e∈E,∃x∈it.L,e=s(it.c,x))\/ (∃items:List (St C),(items.map (fun it=>it.W.card)).sum<=2 /\
   (∀it∈items,it.good)/\∀e∈E,∃it∈items,∃x∈it.L,e=s(it.c,x)):=by
 have ac (d:Fin 2) {u v:Fin 11} (he:s(u,v)∈E):
   (u∈N C g d/\v∈N C g (1-d))\/
   (u∈N C g (1-d)/\v∈N C g d):=by
  fin_cases d;exact(hE u v he).1;exact(hE u v he).1.symm
 have a5 (d:Fin 2) (h1:(N C g d).card<=1):
   ∃it:St C,it.W.card=1/\it.L.card<=4/\∀e∈E,∃x∈it.L,e=s(it.c,x):=by
  have⟨c,hc⟩:=Qk h1
  refine⟨Q0 C c (Q4 c E) (opnd C g (1-d)) (Qe a4 hg (1-d)) (fun x hx=>by
    have he:=Zl hx;have Pt:=G11.ne_of_adj (Eg (Dp (z he)).1)
    rcases ac d he with⟨_,ap⟩|⟨_,an⟩;exact ap;exact(Pt (hc x an).symm).elim)
   (fun _ hx=>z (Zl hx)) False False.elim,Cs _,KH z c,fun e he=>by
    induction e using Sym2.ind with| _ u v=>
    rcases ac d he with⟨a6,_⟩|⟨_,Pv⟩
    ·obtain rfl:=hc u a6;exact⟨v,Zm he,rfl⟩
    ·obtain rfl:=hc v Pv;exact⟨u,Zm (Sw▸he),Sw⟩⟩
 by_cases al:(N C g 0).card<=1;· exact Ql (a5 0 al)
 by_cases ak:(N C g 1).card<=1;· exact Ql (a5 1 ak)
 right;set Wg:=Mw C g
 have aj (d:Fin 2):(N C g d∩Wg).card<=1:=Qa Q3
  (by fin_cases d<;>simp at*<;>omega:2<=(N C g (1-d)).card)
  (fun u hu v hv=>QC a4 hg (I1 hu) (I2 hu) v hv)
 let j (d:Fin 2):List (St C):=
  if h:(N C g d∩Wg).Nonempty then
   [Q9 a4 hg d h.choose (Ip h.choose_spec).1 (Ip h.choose_spec).2 E z] else []
 have t (d:Fin 2) {p q:Fin 11} (he:s(p,q)∈E) (hp:p∈N C g d) (hpW:p∈Wg) (hq:q∈N C g (1-d)):
   ∃it∈j 0++j 1,∃x∈it.L,s(p,q)=s(it.c,x):=by
  have Pt:(N C g d∩Wg).Nonempty:=⟨p,Im hp hpW⟩;obtain rfl:p=Pt.choose:=Qp (aj d) (Im hp hpW) Pt.choose_spec;let it:=Q9 a4 hg d Pt.choose (Ip Pt.choose_spec).1 (Ip Pt.choose_spec).2 E z;refine⟨it,?_,q,Im (Zm he) hq,rfl⟩;have a7:it∈j d:=by dsimp only[j];rw[dif_pos Pt];exact Ks _
  fin_cases d
  ·exact Kal _ a7
  ·exact Kar _ a7
 refine⟨j 0++j 1,by simp only[LqA,LqS,j];split_ifs<;>simp[Q9,Q0],
  fun it Px=>by rcases Kap Px with h|h<;>(dsimp only[j] at h;split_ifs at h with Pt;simp only[Kl] at h;subst h;trivial;cases h),
  fun e he=>by
   induction e using Sym2.ind with| _ u v=>
   rcases(hE u v he).1 with⟨a6,Pu⟩|⟨ad,Pv⟩<;>rcases(hE u v he).2 with af|ae
   ·exact t 0 he a6 af Pu
   ·have⟨it,hi,x,hx,hq⟩:=t 1 (Sw▸he) Pu ae a6;exact⟨it,hi,x,hx,Sw.trans hq⟩
   ·exact t 1 he ad af Pv
   ·have⟨it,hi,x,hx,hq⟩:=t 0 (Sw▸he) Pv ae ad;exact⟨it,hi,x,hx,Sw.trans hq⟩⟩
lemma Kd (ah:Ao C){g:ℕ}(hg:g∈Jk C){v:Fin 11}(b4:N C g 0∩N C g 1⊆{v})(az:2<=(N C g 0).card)(b3:2<=(N C g 1).card)(ad:∀w∈Mw C g,Ga v w){E:Finset (Sym2 (Fin 11))}(b5:E⊆Us C)(hE:∀u w:Fin 11,s(u,w)∈E->u≠v->w≠v -> ((u∈N C g 0/\w∈N C g 1)\/ (u∈N C g 1/\w∈N C g 0)) /\ (u∈Mw C g\/w∈Mw C g)): (∃items:List (St C),(items.map (fun it=>it.W.card)).sum<=1 /\
   (∀it∈items,it.good/\it.c∈Mw C g) /\
   ∀u w:Fin 11,s(u,w)∈E->u≠v->w≠v->∃it∈items,∃x∈it.L,s(u,w)=s(it.c,x))\/
  (∃c0 c1:Fin 11,c0∈(N C g 0\N C g 1)∩Mw C g /\
   c1∈(N C g 1\N C g 0)∩Mw C g /\
   ∀w∈Mw C g,w=c0\/w=c1):=by
 set S0:=N C g 0;set S1:=N C g 1;set S0':=S0\S1;set S1':=S1\S0;set Wg:=Mw C g;have a7 (z:Fin 11) (hz:z≠v):¬(z∈S0/\z∈S1):=fun h=>hz (Sp (b4 (Imp h)))
 have an:(S0'∩Wg).card<=1:=Qa Q3 b3
  (fun u hu y hy=>QC ah hg (J1 hu) (I2 hu) y hy)
 have aq:(S1'∩Wg).card<=1:=Qa Q3 az
  (fun y hy u hu=>QC ah hg (J1 hy) (I2 hy) u hu)
 have ak (d:Fin 2) (c:Fin 11) (hcS:c∈N C g d) (hcW:c∈Wg)
   (hpick:∀u w:Fin 11,s(u,w)∈E->u≠v->w≠v ->
    (u=c/\w∈N C g (1-d))\/(w=c/\u∈N C g (1-d))):
   ∃items:List (St C),(items.map (fun it=>it.W.card)).sum<=1 /\
    (∀it∈items,it.good/\it.c∈Wg) /\
    ∀u w:Fin 11,s(u,w)∈E->u≠v->w≠v->∃it∈items,∃x∈it.L,s(u,w)=s(it.c,x):=by
  let it:=Q9 ah hg d c hcS hcW E b5
  refine⟨[it],by simp[it,Q9,Q0],
   fun _ h=>by simp only[Kl] at h;subst h;exact⟨trivial,hcW⟩,fun u w he q j=>?_⟩
  rcases hpick u w he q j with⟨rfl,hw⟩|⟨rfl,hu⟩
  ·exact⟨it,Kc,w,Im (Zm he) hw,rfl⟩
  ·exact⟨it,Kc,u,Im (Zm (Sw▸he)) hu,Sw⟩
 have a5 {z:Fin 11} (hz0:z∈S0) (hzv:z≠v) (hzW:z∈Wg):z∈S0'∩Wg:=
  Im (Dm hz0 (fun h=>a7 z hzv ⟨hz0,h⟩)) hzW
 have a6 {z:Fin 11} (hz1:z∈S1) (hzv:z≠v) (hzW:z∈Wg):z∈S1'∩Wg:=
  Im (Dm hz1 (fun h=>a7 z hzv ⟨h,hz1⟩)) hzW
 rcases Eo (S0'∩Wg) with al|⟨c0,a9⟩
 ·rcases Eo (S1'∩Wg) with ae|⟨c1,a8⟩
  ·left;refine⟨[],by simp,by simp,fun u w he q j=>?_⟩
   rcases(hE u w he q j).1 with⟨a4,t⟩|⟨a3,hw0⟩<;>rcases(hE u w he q j).2 with aa|ab
   ·exact(N0 (al▸a5 a4 q aa)).elim
   ·exact(N0 (ae▸a6 t j ab)).elim
   ·exact(N0 (ae▸a6 a3 q aa)).elim
   ·exact(N0 (al▸a5 hw0 j ab)).elim
  ·left;refine ak 1 c1 (J1 a8) (I2 a8) fun u w he q j=>?_
   rcases(hE u w he q j).1 with⟨a4,t⟩|⟨a3,hw0⟩<;>rcases(hE u w he q j).2 with aa|ab
   ·exact(N0 (al▸a5 a4 q aa)).elim
   ·exact Qr ⟨Qp aq (a6 t j ab) a8,a4⟩
   ·exact Ql ⟨Qp aq (a6 a3 q aa) a8,hw0⟩
   ·exact(N0 (al▸a5 hw0 j ab)).elim
 ·rcases Eo (S1'∩Wg) with ae|⟨c1,a8⟩
  ·left;refine ak 0 c0 (J1 a9) (I2 a9) fun u w he q j=>?_
   rcases(hE u w he q j).1 with⟨a4,t⟩|⟨a3,hw0⟩<;>rcases(hE u w he q j).2 with aa|ab
   ·exact Ql ⟨Qp an (a5 a4 q aa) a9,t⟩
   ·exact(N0 (ae▸a6 t j ab)).elim
   ·exact(N0 (ae▸a6 a3 q aa)).elim
   ·exact Qr ⟨Qp an (a5 hw0 j ab) a9,a3⟩
  ·by_cases aw:∃w3∈Wg,w3≠c0/\w3≠c1
   ·left;have⟨w3,ap,ay,ax⟩:=aw
    rcases KN ah hg a9 a8 ap (ad c0 (I2 a9)) (ad c1 (I2 a8)) (ad w3 ap) ay ax with ag|aj
    ·refine ak 0 c0 (J1 a9) (I2 a9) fun u w he q j=>?_
     rcases(hE u w he q j).1 with⟨a4,t⟩|⟨a3,hw0⟩
     ·exact Ql ⟨Sp (ag (Dm (Dm a4 (fun h=>a7 u q ⟨a4,h⟩)) (Ns q))),t⟩
     ·exact Qr ⟨Sp (ag (Dm (Dm hw0 (fun h=>a7 w j ⟨hw0,h⟩)) (Ns j))),a3⟩
    ·refine ak 1 c1 (J1 a8) (I2 a8) fun u w he q j=>?_
     rcases(hE u w he q j).1 with⟨a4,t⟩|⟨a3,hw0⟩
     ·exact Qr ⟨Sp (aj (Dm (Dm t (fun h=>a7 w j ⟨h,t⟩)) (Ns j))),a4⟩
     ·exact Ql ⟨Sp (aj (Dm (Dm a3 (fun h=>a7 u q ⟨h,a3⟩)) (Ns q))),hw0⟩
   ·right;exact⟨c0,c1,a9,a8,fun w hw=>by by_contra h;exact aw ⟨w,hw,fun e=>h (Ql e),fun e=>h (Qr e)⟩⟩
lemma Zt (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b)(q:∀u v:Fin 11,s(u,v)∈Us C -> Gv C a (Pi u v)=true/\(u∈Mw C a\/v∈Mw C a)): ((Us C).card<=2*(centreless G11 C).card+2+(rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card)\/ (∃v:Fin 11,N C a 0∩N C a 1={v} /\ 2<=(N C a 0).card/\2<=(N C a 1).card):=by
 have ha:a∈Jk C:=by simp[hs]
 set A0:=N C a 0;set A1:=N C a 1;set Ia:=A0∩A1;set Wa:=Mw C a
 rcases Eo Wa with ad|⟨g,j⟩
 ·left;have aj:Us C=∅:=by
   rw[Ee];intro e he;induction e using Sym2.ind with| _ u v=>
   rcases(q u v he).2 with h|h<;>rw[ad] at h<;>exact N0 h
  have an:(Us C).card=0:=by rw[aj,Finset.card_empty]
  omega
 by_cases hIa2:2<=Ia.card
 ·left
  have a5:Wa.card<=1:=Qa Q3 hIa2
   (fun w hw v hv=>(Q1 hL.1 ha (I1 hv) (I2 hv)).2 w hw |>.symm)
  have a6:g∉Ia:=fun h=>(Q1 hL.1 ha (I1 h) (I2 h)).1 j
  obtain⟨d,hnd⟩:∃d:Fin 2,g∉N C a d:=by
   by_cases h0:g∈A0
   ·exact⟨1,fun h1=>a6 (Im h0 h1)⟩
   ·exact⟨0,h0⟩
  let it:=Q0 C g (Q4 g (Us C)) (opnd C a d) (Qe hL.1 ha d)
   (fun x hx=>Kg hL.1 hT hs hab d (q g x (Zl hx)).1 hnd)
   (fun _ hx=>Zl hx) False False.elim
  have a4:=Qw hL.1 g [it] (fun e he=>by
   induction e using Sym2.ind with| _ u v=>
   rcases(q u v he).2 with hu|hv
   ·obtain rfl:=Qp a5 hu j;exact⟨it,Kc,v,Zm he,rfl⟩
   ·obtain rfl:=Qp a5 hv j;exact⟨it,Kc,u,Zm (Sw▸he),Sw⟩)
   (fun _ h Pt=>by simp only[Kl] at h;subst h;exact(Pt rfl).elim)
  simp only[Lmc,Lmn,Lsc,Lsn,it,Q0,Cs] at a4;omega
 by_cases hIa0:Ia=∅
 ·left
  rcases KJ hL.1 ha hIa0 (Sr _) (fun u v he=>
   ⟨Qt hL.1 hT hs hab (q u v he).1 (show u∉Ia by rw[hIa0];exact N0) (show v∉Ia by rw[hIa0];exact N0),(q u v he).2⟩) with⟨it,hW1,_,hcov⟩|⟨its,hsum,hgd,hcov⟩
  ·have a4:=Qw hL.1 it.c [it] (fun e he=>by obtain⟨x,hx,rfl⟩:=hcov e he;exact⟨it,Kc,x,hx,rfl⟩)
    (fun _ h Pt=>by simp only[Kl] at h;subst h;exact(Pt rfl).elim)
   simp only[Lmc,Lmn,Lsc,Lsn] at a4;omega
  ·have a4:=Qw hL.1 0 its hcov (fun it Px _=>hgd it Px);omega
 ·right
  have⟨v,t⟩:=Finset.card_eq_one.mp (by have:=Cpr (Nem hIa0);omega:Ia.card=1)
  have Pv:v∈A0:=(Ip (t▸Ss v)).1;have Pu:v∈A1:=(Ip (t▸Ss v)).2;have⟨ac,aa⟩:=Yj hL hT hs hab;have⟨ak,ab,a7⟩:=Nss ac;have⟨ah,ae,a8⟩:=Nss aa
  have h2 (d:Fin 2) (x:Fin 11) (hx:x∈N C a d) (hxv:x≠v) (hvd:v∈N C a d):2<=(N C a d).card:=by
   have hc:=Cl (show ({v,x}:Finset (Fin 11))⊆N C a d from fun z hz=>by
    rcases Nsp hz with rfl|hz;exact hvd;rw[Sp hz];exact hx)
   rw[Cp hxv.symm] at hc;exact hc
  exact⟨v,t,h2 0 ak ab (fun e=>a7 (e▸Pu)) Pv,h2 1 ah ae (fun e=>a8 (e▸Pv)) Pu⟩
lemma YU (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){v:Fin 11}(g:N C a 0∩N C a 1={v})(hA02:2<=(N C a 0).card)(hA12:2<=(N C a 1).card)(q:∀u w:Fin 11,s(u,w)∈Us C -> Gv C a (Pi u w)=true/\(u∈Mw C a\/w∈Mw C a))(Wv:Finset ℕ)(aj:∀z∈Wv,z < 11+C.gates.length)(az:Wv.card<=2*(centreless G11 C).card+1)(ac:∀w∈Q4 v (Us C),w∈Wv.biUnion (Oi C)\/ ∃t∈Tp C,∃d:Fin 2,∃m∈mixing G11 C,O C (opnd C t d) m/\w∈N C t (1-d)): Bd C:=by
 have ha:a∈Jk C:=by simp[hs]
 have Pv:v∈N C a 0:=(Ip (g▸Ss v)).1;have Pu:v∈N C a 1:=(Ip (g▸Ss v)).2;have a6:=(Q1 hL.1 ha Pv Pu).1;have ag:=(Q1 hL.1 ha Pv Pu).2
 rcases Kd hL.1 ha (show N C a 0∩N C a 1⊆{v} by rw[g]) hA02 hA12 ag (Sr _)
   (fun u w he a8 a7=>⟨Qt hL.1 hT hs hab (q u w he).1 (fun h=>a8 (Sp (g▸h))) (fun h=>a7 (Sp (g▸h))),(q u w he).2⟩) with⟨ita,hsumA,hgdA,hcovA⟩|⟨ca0,ca1,hca0,hca1,hWa2⟩
 ·set Lv:=Q4 v (Us C)
  obtain⟨L0,Lm,M,ak,a9,ad,al,b4,_⟩:=
   QU (L:=Lv) (W_c:=Wv) hL.1 (Sr _) (fun _ hw=>Zl hw) ac
  let aa:St C:=⟨v,L0,Wv,aj,al,fun _ hx=>Zl (ad hx),False,False.elim⟩;set Em:=Lm.image (fun w=>s(v,w));set E':=Us C\Em
  have b5:(Us C).card<=E'.card+M.card:=by
   have h1:=Cl (show Us C⊆E'∪Em from fun e he=>by by_cases hm:e∈Em;exact Ur _ hm;exact Ul _ (Dm he hm))
   have h2:=(Cu E' Em).trans (A2l Ci E'.card);omega
  have ah:=Qw (E:=E') hL.1 v (aa::ita)
   (fun e b7=>by
    have⟨af,ab⟩:=Dp b7;induction e using Sym2.ind with| _ u w=>
    by_cases a8:u=v
    ·subst u;have aq:w∈Lv:=Zm af;rw[a9] at aq
     rcases Up aq with h0|hm;exact⟨aa,Kc,w,h0,rfl⟩;exact(ab (Mi ⟨w,hm,rfl⟩)).elim
    by_cases a7:w=v
    ·subst w;have an:u∈Lv:=Zm (Sw▸af);rw[a9] at an
     rcases Up an with h0|hm;exact⟨aa,Kc,u,h0,Sw⟩;exact(ab (Mi ⟨u,hm,Sw⟩)).elim
    have⟨it,Px,x,hx,b6⟩:=hcovA u w af a8 a7;exact⟨it,Km _ Px,x,hx,b6⟩)
   (fun it Px Pt=>by rcases Kp Px with rfl|h;exact(Pt rfl).elim;exact(hgdA it h).1)
  have b8:=Cl ak;simp only[Lmc,Lsc,aa] at ah;omega
 ·let a3:=Q9 hL.1 ha 0 ca0 (J1 hca0) (I2 hca0) (Us C) (Sr _)
  let j:=Q9 hL.1 ha 1 ca1 (J1 hca1) (I2 hca1) (Us C) (Sr _)
  have ah:=Qw (E:=Us C) hL.1 0 [a3,j]
   (fun e he=>by
    induction e using Sym2.ind with| _ u w=>
    by_cases a8:u=v
    ·subst u;rcases hWa2 w ((q v w he).2.resolve_left a6) with rfl|rfl
     ·exact⟨a3,Kc,v,Im (Zm (Sw▸he)) Pu,Sw⟩
     ·exact⟨j,K2,v,Im (Zm (Sw▸he)) Pv,Sw⟩
    by_cases a7:w=v
    ·subst w;rcases hWa2 u ((q u v he).2.resolve_right a6) with rfl|rfl
     ·exact⟨a3,Kc,v,Im (Zm he) Pu,rfl⟩
     ·exact⟨j,K2,v,Im (Zm he) Pv,rfl⟩
    have a4:=(J2 hca0);have a5:=(J2 hca1)
    rcases Qt hL.1 hT hs hab (q u w he).1 (fun h=>a8 (Sp (g▸h))) (fun h=>a7 (Sp (g▸h))) with⟨av,ap⟩|⟨ar,hw0⟩<;>
     rcases(q u w he).2 with au|aw
    ·rcases hWa2 u au with rfl|rfl;exact⟨a3,Kc,w,Im (Zm he) ap,rfl⟩;exact(a5 av).elim
    ·rcases hWa2 w aw with rfl|rfl;exact(a4 ap).elim;exact⟨j,K2,u,Im (Zm (Sw▸he)) av,Sw⟩
    ·rcases hWa2 u au with rfl|rfl;exact(a4 ar).elim;exact⟨j,K2,w,Im (Zm he) hw0,rfl⟩
    ·rcases hWa2 w aw with rfl|rfl;exact⟨a3,Kc,u,Im (Zm (Sw▸he)) ar,Sw⟩;exact(a5 hw0).elim)
   (fun _ h _=>by rcases Kp h with rfl|h2;trivial;simp only[Kl] at h2;subst h2;trivial)
  simp only[Lmc,Lmn,Lsc,Lsn,a3,j,Q9,Q0,Cs] at ah;omega
lemma Zc (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b)(g:∀u v:Fin 11,s(u,v)∈Us C -> Gv C a (Pi u v)=true /\ ((u∈Mw C a/\(Tc C a u\/Tc C b u))\/ (v∈Mw C a/\(Tc C a v\/Tc C b v)))): Bd C:=by
 have a5:∀u w:Fin 11,s(u,w)∈Us C->Gv C a (Pi u w)=true/\(u∈Mw C a\/w∈Mw C a):=fun u w he=>
  ⟨(g u w he).1,by rcases(g u w he).2 with⟨h,_⟩|⟨h,_⟩<;>[exact Ql h;exact Qr h]⟩
 rcases Zt hL hT hs hab a5 with a6|⟨v,j,hA02,hA12⟩
 ·exact a6
 ·have ha:a∈Jk C:=by simp[hs]
  have q:=(Q1 hL.1 ha (Ip (j▸Ss v)).1 (Ip (j▸Ss v)).2).1
  refine YU hL hT hs hab j hA02 hA12 a5 (W0For G11 C a∪W0For G11 C b)
   (fun z hz=>by rcases Up hz with h|h<;>[exact Qg hL.1 a z h;exact Qg hL.1 b z h])
   (by have h1:=(Qj (G:=G11) (C:=C) a).trans (Qs a);have h2:=(Qj (G:=G11) (C:=C) b).trans (Qs b);have h3:=Cu (W0For G11 C a) (W0For G11 C b);omega)
   fun w hw=>?_
  rcases(g v w (Zl hw)).2 with⟨a9,_⟩|⟨_,a8⟩
  ·exact(q a9).elim
  ·rcases a8 with (h0|⟨t,ht,d,m,hm,a3,a4⟩)|(h0|⟨t,ht,d,m,hm,a3,a4⟩)
   ·exact Ql (Bub _ Sul h0)
   ·exact Qr ⟨t,ht,d,m,(Fp hm).1,a3,a4⟩
   ·exact Ql (Bub _ Sur h0)
   ·exact Qr ⟨t,ht,d,m,(Fp hm).1,a3,a4⟩
lemma Xk (g:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hr0:O C (opnd C b 0) a)(hr1:O C (opnd C b 1) a)(x:Fin 11->Bool): Gv C b x=true↔ Gv C a x=true\/((∃u∈N C b 0,x u=true)/\(∃v∈N C b 1,x v=true)):=by
 have hb:b∈Jk C:=by simp[hs]
 rw[Yk g (Q6 hb).1 (Q6 hb).2.1 x,
  QD g hT hs hr0 x,QD g hT hs hr1 x];tauto
lemma W3 (g:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hr0:O C (opnd C b 0) a)(hr1:O C (opnd C b 1) a): ¬Joint G11 C a b:=fun h=>(Zu g hT hs (db:=0) hr0 h).1 (by simpa using hr1)
lemma Z8 (j:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hr0:O C (opnd C b 0) a)(hr1:O C (opnd C b 1) a): Mw C b⊆Mw C a:=fun w hw=>
 Fk (Uv _) (fun x h g=>
  (Fp hw).2 x ((Xk j hT hs hr0 hr1 x).mpr (Ql h)) g)
lemma ZZ (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hr0:O C (opnd C b 0) a)(hr1:O C (opnd C b 1) a): ∃g h:ℕ,g∈mixing G11 C/\h∈mixing G11 C/\g < b/\h < b /\ O C (11+g) a/\O C (11+h) a /\ Oi C (11+g)⊆N C b 0/\Oi C (11+h)⊆N C b 1 /\ (N C b 0∩N C b 1=∅->g≠h):=by
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 have⟨a9,aa⟩:=ZA hL hT hs hr0 hr1;obtain⟨u0,ac,_⟩:=Nss a9;obtain⟨u1,ab,_⟩:=Nss aa;have⟨g,a3,q,a4⟩:=KY hL.1 ha hr0 ⟨u0,ac⟩;have⟨h,a8,j,a5⟩:=KY hL.1 ha hr1 ⟨u1,ab⟩
 refine⟨g,h,a3,a8,KK hL.1 (Q6 hb).1 q,KK hL.1 (Q6 hb).1 j,
  a4,a5,QJ q,QJ j,fun a7 ad=>?_⟩
 subst ad;have⟨z,hz⟩:=KZ hL.1 a3;have t:z∈N C b 0∩N C b 1:=Im (QJ q hz) (QJ j hz);rw[a7] at t;exact N0 t
lemma ZJ {S0 S1:Finset (Fin 11)}{u v:Fin 11}(h0:∃x∈S0,x=u\/x=v)(j:∃y∈S1,y=u\/y=v)(q:u∉S0∩S1)(hv:v∉S0∩S1): (u∈S0/\v∈S1)\/(u∈S1/\v∈S0):=by
 obtain⟨x,g,rfl|rfl⟩:=h0<;>obtain⟨y,h,rfl|rfl⟩:=j
 ·exact(q (Im g h)).elim
 ·exact Ql ⟨g,h⟩
 ·exact Qr ⟨h,g⟩
 ·exact(hv (Im g h)).elim
lemma Va {g:ℕ}{u v:Fin 11}{d:Fin 2}(h0:∃x∈N C g 0,x=u\/x=v)(t:∃y∈N C g 1,y=u\/y=v)(q:u∉N C g d):v∈N C g d:=by
 fin_cases d
 ·obtain⟨x,h,rfl|rfl⟩:=h0
  ·exact(q h).elim
  ·exact h
 ·obtain⟨y,j,rfl|rfl⟩:=t
  ·exact(q j).elim
  ·exact j
lemma Zg {n:ℕ}(u v:Fin n):Pi u v=Pi v u:=by funext z;simp[pairInput,Bool.or_comm]
lemma V3 (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hr0:O C (opnd C b 0) a)(hr1:O C (opnd C b 1) a){u v:Fin 11}(he:s(u,v)∈Us C): (Gv C a (Pi u v)=true /\ ((u∈Mw C a/\(Tc C a u\/Tc C b u))\/ (v∈Mw C a/\(Tc C a v\/Tc C b v))))\/ (Gv C a (Pi u v)=false /\ (∃x0∈N C b 0,x0=u\/x0=v) /\ (∃x1∈N C b 1,x1=u\/x1=v) /\ ((u∈Mw C b/\Tc C b u)\/ (v∈Mw C b/\Tc C b v))):=by
 have a3:=Z8 hL.1 hT hs hr0 hr1;obtain⟨t,ht,d,j,hj,_,ac,a5,ab⟩:=ZD hL hT hs he
 rcases ab with⟨w,aa,z⟩|⟨hJ,_⟩
 ·have g:=K8 hL.1 hj ht ac aa
  have q:=Q5 hL.1 g
  rcases Kk hs hj with ah|aj
  ·subst j;left;refine⟨a5,?_⟩
   rcases z with a7|a6
   ·subst w;exact Ql ⟨q,Ql g⟩
   ·subst w;exact Qr ⟨q,Ql g⟩
  ·subst j
   by_cases a4:Gv C a (Pi u v)=true
   ·left;refine⟨a4,?_⟩
    rcases z with a7|a6
    ·subst w;exact Ql ⟨a3 q,Qr g⟩
    ·subst w;exact Qr ⟨a3 q,Qr g⟩
   ·right
    rcases(Xk hL.1 hT hs hr0 hr1 (Pi u v)).mp a5 with h|⟨⟨x0,ad,a9⟩,⟨x1,af,a8⟩⟩
    ·exact(a4 h).elim
    ·refine⟨Bool.eq_false_iff.mpr a4,⟨x0,ad,(K4 u v x0).mp a9⟩,
      ⟨x1,af,(K4 u v x1).mp a8⟩,?_⟩
     rcases z with a7|a6
     ·subst w;exact Ql ⟨q,g⟩
     ·subst w;exact Qr ⟨q,g⟩
 ·exact(W3 hL.1 hT hs hr0 hr1 hJ).elim
lemma QR (g:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(x:Fin 11->Bool): Gv C b x=true↔ (Gv C a x=true\/∃u∈N C b db,x u=true) /\ (∃v∈N C b (1-db),x v=true):=by
 have hb:b∈Jk C:=by simp[hs]
 rw[QF g (Q6 hb).1 (Q6 hb).2.1 x]
 constructor
 ·intro h
  exact⟨(QD g hT hs hrb x).mp (h db),(KQ g hT hs hno2 x).mp (h (1-db))⟩
 ·rintro⟨h0,h1⟩ i
  rcases Qn db i with rfl|rfl
  ·exact(QD g hT hs hrb x).mpr h0
  ·exact(KQ g hT hs hno2 x).mpr h1
lemma K7 (j:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a): N C b (1-db)∩Mw C b⊆Mw C a:=fun w hw=>by
 have⟨q,t⟩:=Ip hw;refine Fk (Uv _) (fun x h g=>?_)
 exact(Fp t).2 x
  ((QR j hT hs hrb hno2 x).mpr ⟨Ql h,⟨w,q,g⟩⟩) g
lemma YV (g:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){v:Fin 11}(Pv:v∈N C a 0)(Pu:v∈N C a 1)(q:v∈Mw C b): ∀y∈N C b (1-db),Ga v y:=fun y t=>by
 have j:Gv C a (Pi v y)=true:=
  (Qv g hT hs hab _).mpr ⟨⟨v,Pv,Q8 v y⟩,⟨v,Pu,Q8 v y⟩⟩
 have h:Gv C b (Pi v y)=true:=
  (QR g hT hs hrb hno2 _).mpr ⟨Ql j,⟨y,t,Qq v y⟩⟩
 exact(Qx G11 v y).mp ((Fp q).2 _ h (Q8 v y))
lemma QK (j:Ao C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hB0ne:(N C b db).Nonempty): ∃h∈mixing G11 C,h < b/\O C (11+h) a /\ Oi C (11+h)⊆N C b db:=by
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 have⟨h,t,g,q⟩:=KY j ha hrb hB0ne;exact⟨h,t,KK j (Q6 hb).1 g,q,QJ g⟩
lemma Xp (z:Ao C){a b:ℕ}(hs:Jk C={a,b}){t:ℕ}{d:Fin 2}(ht:t∈Tp C)(a5:O C (opnd C t d) a)(hrb:O C (opnd C t (1-d)) b): (centreless G11 C\T0For G11 C a).Nonempty\/ (T0For G11 C b).Nonempty\/∃q∈mixing G11 C,O C (11+q) b:=by
 have hb:b∈Jk C:=by simp[hs]
 by_cases g:side (n:=11) C t (1-d)=∅
 ·by_cases h0:side (n:=11) C t d=∅
  ·left
   have h:t∈centreless G11 C:=Fk ht (by
    rcases Qn 0 d with rfl|rfl
    ·exact Ql h0
    ·exact Qr h0)
   refine⟨t,Dm h (fun a3=>?_)⟩
   obtain⟨_,da,_,_,Pt⟩:=Fp a3
   rcases Qn d da with rfl|rfl
   ·rw[g] at Pt;exact Nne Pt
   ·rw[Qd,h0] at Pt;exact Nne Pt
  ·right;left
   have h:t∈centreless G11 C:=Fk ht (by
    fin_cases d
    ·exact Qr g
    ·exact Ql g)
   exact⟨t,Fm ⟨h,1-d,g,hrb,by rw[Qd];exact Nem h0⟩⟩
 ·right;right
  obtain⟨q,a4,_,j⟩:=KY z hb hrb (Nem g);exact⟨q,a4,j⟩
lemma QM (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){u v:Fin 11}(he:s(u,v)∈Us C): (Gv C a (Pi u v)=true /\ ((Tc C a u\/Tc C a v)\/ ((u∈N C b (1-db)\/v∈N C b (1-db)) /\ (Tc C b u\/Tc C b v))\/ (Joint G11 C a b/\(u∈N C b (1-db)\/v∈N C b (1-db)) /\ ∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) a/\O C (opnd C t (1-d)) b)))\/ (Gv C a (Pi u v)=false /\ (∃x0∈N C b db,x0=u\/x0=v) /\ (∃x1∈N C b (1-db),x1=u\/x1=v) /\ ((u∈Mw C b/\Tc C b u)\/(v∈Mw C b/\Tc C b v))):=by
  obtain⟨t,ht,d,j,hj,_,a4,a6,af⟩:=ZD hL hT hs he
  rcases af with⟨w,ae,a3⟩|⟨hJ,q,ah,k,hk,a9,a5⟩
  · have g:=K8 hL.1 hj ht a4 ae
    have aa:=Q5 hL.1 g
    rcases Kk hs hj with hja|hjb
    · subst j;left;refine⟨a6,Ql ?_⟩
      rcases a3 with a8|a7
      ·subst w;exact Ql g
      ·subst w;exact Qr g
    · subst j
      obtain⟨h0,⟨z,hzB1,hzp⟩⟩:=(QR hL.1 hT hs hrb hno2 (Pi u v)).mp a6
      have h:u∈N C b (1-db)\/v∈N C b (1-db):=by
        rcases(K4 u v z).mp hzp with aj|ad
        ·subst z;exact Ql hzB1
        ·subst z;exact Qr hzB1
      by_cases q:Gv C a (Pi u v)=true
      · left;refine⟨q,Qr (Ql ⟨h,?_⟩)⟩
        rcases a3 with a8|a7
        ·subst w;exact Ql g
        ·subst w;exact Qr g
      · right
        have⟨x0,ag,ac⟩:=h0.resolve_left q
        refine⟨Bool.eq_false_iff.mpr q,⟨x0,ag,(K4 u v x0).mp ac⟩,
          ⟨z,hzB1,(K4 u v z).mp hzp⟩,?_⟩
        rcases a3 with a8|a7
        ·subst w;exact Ql ⟨aa,g⟩
        ·subst w;exact Qr ⟨aa,g⟩
  · obtain⟨_,⟨z,hzB1,hzp⟩⟩:=(QR hL.1 hT hs hrb hno2 (Pi u v)).mp ah
    have h:u∈N C b (1-db)\/v∈N C b (1-db):=by
      rcases(K4 u v z).mp hzp with aj|ad
      ·subst z;exact Ql hzB1
      ·subst z;exact Qr hzB1
    left;refine⟨q,Qr (Qr ⟨hJ,h,t,ht,?_⟩)⟩
    rcases Kk hs hj with hja|hjb<;>rcases Kk hs hk with hka|hkb
    ·exact(a9 (hka.trans hja.symm)).elim
    ·subst j;subst k;exact⟨d,a4,a5⟩
    ·subst j;subst k;exact⟨1-d,a5,by rw[Qd];exact a4⟩
    ·exact(a9 (hkb.trans hjb.symm)).elim
lemma KT (q:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hA02:2<=(N C a 0).card)(hA12:2<=(N C a 1).card){E0 E1:Finset (Sym2 (Fin 11))}(a7:E0⊆Us C)(a6:E1⊆Us C)(ab:∀u v:Fin 11,s(u,v)∈E0 -> (u∈(N C a 0\N C a 1)∩Mw C b /\ v∈(N C a 1\N C a 0)∩N C b (1-db))\/ (v∈(N C a 0\N C a 1)∩Mw C b /\ u∈(N C a 1\N C a 0)∩N C b (1-db)))(ae:∀u v:Fin 11,s(u,v)∈E1 -> (u∈(N C a 1\N C a 0)∩Mw C b /\ v∈(N C a 0\N C a 1)∩N C b (1-db))\/ (v∈(N C a 1\N C a 0)∩Mw C b /\ u∈(N C a 0\N C a 1)∩N C b (1-db))): ∃it0 it1:St C,it0.W.card=1/\it1.W.card=1 /\ it0.L⊆(N C a 0\N C a 1)∪(N C a 1\N C a 0) /\ it1.L⊆(N C a 0\N C a 1)∪(N C a 1\N C a 0) /\ (∀e∈E0,∃x∈it0.L,e=s(it0.c,x)) /\ (∀e∈E1,∃x∈it1.L,e=s(it1.c,x)) /\ ((it0.W.biUnion (Oi C)∩it1.L).card<=1\/(it1.W.biUnion (Oi C)∩it0.L).card<=1):=by
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 set A0:=N C a 0;set A1:=N C a 1;set A0':=A0\A1;set A1':=A1\A0;set B1:=N C b (1-db);set Wb:=Mw C b;set Wa:=Mw C a;have PW:=K7 q hT hs hrb hno2
 have ak:(A0'∩Wa).card<=1:=Qa Q3 hA12
  (fun u hu y hy=>Y1 q hT hs hab (J1 hu) (I2 hu) y hy)
 have aj:(A1'∩Wa).card<=1:=Qa Q3 hA02
  (fun y hy u hu=>Y1 q hT hs hab (J1 hy) (I2 hy) u hu)
 have hD (d:Fin 2):((N C a d\N C a (1-d))∩Wb).card<=1\/
   ((N C a (1-d)\N C a d)∩B1).card<=1:=by
  by_contra! h
  have hc:((N C a d\N C a (1-d))∩Wb).card<=1:=
   Qa Q3 (by omega:2<=((N C a (1-d)\N C a d)∩B1).card)
    (fun u hu y hy=>K9 q hT hs hab hrb d (J1 hu) (I2 hu) (J1 hy) (I2 hy))
  omega
 have j {E:Finset (Sym2 (Fin 11))} {P Q:Finset (Fin 11)} (hEU:E⊆Us C)
   (hPQ:∀u v:Fin 11,s(u,v)∈E->(u∈P/\v∈Q)\/(v∈P/\u∈Q))
   (hP1:P.card<=1) (w:ℕ) (hw:w < 11+C.gates.length) (hsub:Q⊆Oi C w):
   ∃it:St C,it.W={w}/\it.L⊆Q/\∀e∈E,∃x∈it.L,e=s(it.c,x):=by
  have⟨c,hc⟩:=Qk hP1
  refine⟨Q0 C c (Q4 c E∩Q) w hw (Ir.trans hsub)
   (fun _ g=>hEU (Zl (I1 g))) False False.elim,
   rfl,Ir,fun e he=>by
    induction e using Sym2.ind with| _ u v=>
    rcases hPQ u v he with⟨hu,hv⟩|⟨hv,hu⟩
    ·obtain rfl:=hc u hu;exact⟨v,Im (Zm he) hv,rfl⟩
    ·obtain rfl:=hc v hv;exact⟨u,Im (Zm (Sw▸he)) hu,Sw⟩⟩
 have ag:∀u v:Fin 11,s(u,v)∈E0->(u∈A1'∩B1/\v∈A0'∩Wb)\/(v∈A1'∩B1/\u∈A0'∩Wb):=fun u v h=>by rcases ab u v h with⟨a,b⟩|⟨a,b⟩;exact Qr ⟨b,a⟩;exact Ql ⟨b,a⟩
 have aa:∀u v:Fin 11,s(u,v)∈E1->(u∈A0'∩B1/\v∈A1'∩Wb)\/(v∈A0'∩B1/\u∈A1'∩Wb):=fun u v h=>by rcases ae u v h with⟨a,b⟩|⟨a,b⟩;exact Qr ⟨b,a⟩;exact Ql ⟨b,a⟩
 rcases hD 0 with h0|h0<;>rcases hD 1 with h1|h1
 ·have⟨it0,z,hL0,a5⟩:=j a7 ab h0 (opnd C a 1) (Qe q ha 1) (fun _ g=>(J1 g))
  have⟨it1,t,hL1,a3⟩:=j a6 ae h1 (opnd C a 0) (Qe q ha 0) (fun _ g=>(J1 g));refine⟨it0,it1,by rw[z,Cs],by rw[t,Cs],hL0.trans (Il.trans Sur),hL1.trans (Il.trans Sul),a5,a3,Qr ?_⟩;have a9:it1.W.biUnion (Oi C)∩it0.L=∅:=by rw[t,Sbu,Ee];intro x g;exact(Dp (Ip (hL0 (I2 g))).1).2 (I1 g)
  rw[a9,Finset.card_empty];omega
 ·have⟨it0,z,hL0,a5⟩:=j a7 ab h0 (opnd C b (1-db)) (Qe q hb (1-db)) Ir
  have⟨it1,t,hL1,a3⟩:=j a6 aa h1 (opnd C a 1) (Qe q ha 1) (fun _ g=>(J1 g));refine⟨it0,it1,by rw[z,Cs],by rw[t,Cs],hL0.trans (Il.trans Sur),hL1.trans (Il.trans Sur),a5,a3,Ql ?_⟩
  exact(Cl fun x g=>by rw[z,Sbu] at g;have⟨ad,ah⟩:=Ip g;have⟨ap,ac⟩:=Ip (hL1 ah);exact Im ap (PW (Im ad ac))).trans aj
 ·have⟨it0,z,hL0,a5⟩:=j a7 ag h0 (opnd C a 0) (Qe q ha 0) (fun _ g=>(J1 g))
  have⟨it1,t,hL1,a3⟩:=j a6 ae h1 (opnd C b (1-db)) (Qe q hb (1-db)) Ir;refine⟨it0,it1,by rw[z,Cs],by rw[t,Cs],hL0.trans (Il.trans Sul),hL1.trans (Il.trans Sul),a5,a3,Qr ?_⟩
  exact(Cl fun x g=>by rw[t,Sbu] at g;have⟨ad,ah⟩:=Ip g;have⟨an,ac⟩:=Ip (hL0 ah);exact Im an (PW (Im ad ac))).trans ak
 ·have⟨it0,z,hL0,a5⟩:=j a7 ag h0 (opnd C a 0) (Qe q ha 0) (fun _ g=>(J1 g))
  have⟨it1,t,hL1,a3⟩:=j a6 aa h1 (opnd C a 1) (Qe q ha 1) (fun _ g=>(J1 g));refine⟨it0,it1,by rw[z,Cs],by rw[t,Cs],hL0.trans (Il.trans Sul),hL1.trans (Il.trans Sur),a5,a3,Ql ?_⟩;have a9:it0.W.biUnion (Oi C)∩it1.L=∅:=by rw[z,Sbu,Ee];intro x g;exact(Dp (Ip (hL1 (I2 g))).1).2 (I1 g)
  rw[a9,Finset.card_empty];omega
lemma QS (ae:Ao C){E:Finset (Sym2 (Fin 11))}(goods bads:List (St C))(a8:∀g∈goods,g.good)(ac:∀e∈E,∃it∈goods++bads,∃x∈it.L,e=s(it.c,x))(q:∀g∈goods,∀b∈bads,g.c≠b.c)(h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)(a3:∀b1∈bads,∀b2∈bads,b1.c≠b2.c -> (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1): E.card<=(rFull G11 C).card+(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum:=by
 have ag:=Z3 (E:=E) ae (goods++bads) ac (fun a4 h1 a6 h2 Pt=>by
  rcases Kap h1 with ab|a9<;>rcases Kap h2 with af|a7
  ·exact Ql fun i hi hci=>by
    rcases Kap hi with t|z
    ·exact a8 i t
    ·exact(q a4 ab i z hci.symm).elim
  ·exact Ql fun i hi hci=>by
    rcases Kap hi with t|z
    ·exact a8 i t
    ·exact(q a4 ab i z hci.symm).elim
  ·exact Qr (Ql fun i hi hci=>by
    rcases Kap hi with t|z
    ·exact a8 i t
    ·exact(q a6 af i z hci.symm).elim)
  ·refine Qr (Qr ⟨fun i hi hci=>?_,fun j hj aa=>?_,a3 a4 a9 a6 a7 Pt⟩)
   ·rcases Kap hi with t|z
    ·exact(q i t a4 a9 hci).elim
    ·exact h i z a4 a9 hci
   ·rcases Kap hj with ah|ad
    ·exact(q j ah a6 a7 aa).elim
    ·exact h j ad a6 a7 aa)
 simp only[LqA,LqS] at ag;omega
lemma Yy (ab:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hA02:2<=(N C a 0).card)(hA12:2<=(N C a 1).card){E0 E1:Finset (Sym2 (Fin 11))}(ah:E0⊆Us C)(ae:E1⊆Us C)(aa:∀u v:Fin 11,s(u,v)∈E0->u∉Mw C a/\v∉Mw C a /\ ((u∈(N C a 0\N C a 1)∩Mw C b/\v∈(N C a 1\N C a 0)∩N C b (1-db))\/ (v∈(N C a 0\N C a 1)∩Mw C b/\u∈(N C a 1\N C a 0)∩N C b (1-db))))(ac:∀u v:Fin 11,s(u,v)∈E1->u∉Mw C a/\v∉Mw C a /\ ((u∈(N C a 1\N C a 0)∩Mw C b/\v∈(N C a 0\N C a 1)∩N C b (1-db))\/ (v∈(N C a 1\N C a 0)∩Mw C b/\u∈(N C a 0\N C a 1)∩N C b (1-db)))): ∃bads:List (St C),(bads.map (fun it=>it.W.card)).sum<=2 /\
   (∀it∈bads,∃x:Fin 11,s(it.c,x)∈E0∪E1) /\
   (∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2) /\
   (∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
    (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1) /\
   ∀e∈E0∪E1,∃it∈bads,∃x∈it.L,e=s(it.c,x):=by
 classical
 have PW:=K7 ab hT hs hrb hno2
 obtain⟨it0,it1,ar,ak,_,_,a9,a7,hdisj01⟩:=
  KT ab hT hs hab hrb hno2 hA02 hA12 ah ae
   (fun u v he=>(aa u v he).2.2) (fun u v he=>(ac u v he).2.2)
 let bads:List (St C):=(if E0.Nonempty then [it0] else [])++(if E1.Nonempty then [it1] else [])
 have q {z:St C} (hz:z∈bads):(E0.Nonempty/\z=it0)\/(E1.Nonempty/\z=it1):=by
  rcases Kap hz with h|h<;>split_ifs at h with Pt
  ·simp only[Kl] at h;exact Ql ⟨Pt,h⟩
  ·cases h
  ·simp only[Kl] at h;exact Qr ⟨Pt,h⟩
  ·cases h
 have t:E0.Nonempty->E1.Nonempty->it0.c≠it1.c:=fun ⟨e0,a3⟩ ⟨e1,a4⟩ a5=>by
  obtain⟨x0,_,ap⟩:=a9 _ a3;obtain⟨x1,_,au⟩:=a7 _ a4;have h0:=aa it0.c x0 (ap▸a3);have h1:=ac it1.c x1 (au▸a4);rw[←a5] at h1
  rcases h0.2.2 with⟨g,_⟩|⟨_,g⟩<;>rcases h1.2.2 with⟨j,_⟩|⟨_,j⟩
  ·exact(J2 g) (J1 j)
  ·exact h0.1 (PW (Im (I2 j) (I2 g)))
  ·exact h0.1 (PW (Im (I2 g) (I2 j)))
  ·exact(J2 g) (J1 j)
 refine⟨bads,by simp only[bads,LqA,LqS];split_ifs<;>simp[ar,ak],
  fun it Px=>by
   rcases q Px with⟨⟨e0,a3⟩,rfl⟩|⟨⟨e1,a4⟩,rfl⟩
   ·obtain⟨x,_,hq⟩:=a9 _ a3;exact⟨x,Ul _ (hq▸a3)⟩
   ·obtain⟨x,_,hq⟩:=a7 _ a4;exact⟨x,Ur _ (hq▸a4)⟩,
  fun b1 a8 b2 a6 hceq=>by
   rcases q a8 with⟨al,rfl⟩|⟨am,rfl⟩<;>rcases q a6 with⟨aq,rfl⟩|⟨an,rfl⟩
   ·rfl
   ·exact(t al an hceq).elim
   ·exact(t aq am hceq.symm).elim
   ·rfl,
  fun b1 a8 b2 a6 Pt=>by
   rcases q a8 with⟨_,rfl⟩|⟨_,rfl⟩<;>rcases q a6 with⟨_,rfl⟩|⟨_,rfl⟩
   ·exact(Pt rfl).elim
   ·exact hdisj01
   ·exact hdisj01.symm
   ·exact(Pt rfl).elim,
  fun e he=>by
   rcases Up he with h0|h1
   ·have ad:E0.Nonempty:=⟨_,h0⟩;have⟨x,hx,a5⟩:=a9 _ h0
    exact⟨it0,Kal _ (by simp[ad]),x,hx,a5⟩
   ·have aj:E1.Nonempty:=⟨_,h1⟩;have⟨x,hx,a5⟩:=a7 _ h1
    exact⟨it1,Kar _ (by simp[aj]),x,hx,a5⟩⟩
lemma ZH (am:Ao C){E:Finset (Sym2 (Fin 11))}{bonus:ℕ}{c:Fin 11}{L:Finset (Fin 11)}{W_c M_cand:Finset ℕ}(av:M_cand⊆mixing G11 C)(ad:∀z∈W_c,z < 11+C.gates.length)(an:∀z∈W_c,∀x∈Oi C z,Ga c x)(h:∀w∈L,s(c,w)∈Us C)(a6:∀w∈L,w∈W_c.biUnion (Oi C)\/ ∃t∈Tp C,∃d:Fin 2,∃m∈M_cand,O C (opnd C t d) m/\w∈N C t (1-d))(goods bads:List (St C))(ar:∀g∈goods,g.good)(af:∀g∈goods,∀b∈bads,g.c≠b.c)(aq:∀b∈bads,b.c≠c)(a4:∀e∈E,(∃w∈L,e=s(c,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x))(ae:∀(E':Finset (Sym2 (Fin 11))) (itc:St C),itc.good->itc.c=c->itc.W=W_c -> (∀e∈E',∃it∈(itc::goods)++bads,∃x∈it.L,e=s(it.c,x)) -> (∀g∈itc::goods,g.good)->(∀g∈itc::goods,∀b∈bads,g.c≠b.c) -> E'.card+bonus<=(rFull G11 C).card+((itc::goods).map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum):
  ∃M⊆M_cand,E.card+bonus<=(rFull G11 C).card+W_c.card+
    (goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum+M.card /\
   ∃fw:ℕ->Fin 11,(∀m∈M,fw m∈L/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw m∈N C t (1-d)) /\
    (∀m1∈M,∀m2∈M,m1≠m2->fw m1≠fw m2):=by
 classical
 have⟨L0,Lm,M,a9,ak,j,aa,ah,fw,ay,q⟩:=QU (L:=L) (W_c:=W_c) am av h a6;set Em:=Lm.image (fun w=>s(c,w));set E':=E\Em
 have al:E.card<=E'.card+M.card:=by
  have h1:=Cl (show E⊆E'∪Em from fun e he=>by by_cases hm:e∈Em;exact Ur _ hm;exact Ul _ (Dm he hm))
  have h2:=(Cu E' Em).trans (A2l Ci E'.card);omega
 let itc:St C:=⟨c,L0,W_c,ad,aa,fun _ hx=>h _ (j hx),True,fun _=>an⟩
 have aw:=ae E' itc trivial rfl rfl (fun e ax=>by
   have⟨ap,a8⟩:=Dp ax
   rcases a4 e ap with⟨w,ac,rfl⟩|⟨it,Px,x,hx,au⟩
   ·rw[ak] at ac;rcases Up ac with h0|hm;exact⟨itc,Kc,w,h0,rfl⟩;exact(a8 (Mi ⟨w,hm,rfl⟩)).elim
   ·exact⟨it,Km _ Px,x,hx,au⟩)
  (fun g hg=>by rcases Kp hg with rfl|a5;exact trivial;exact ar g a5)
  (fun g hg b hb=>by rcases Kp hg with rfl|a5;exact(aq b hb).symm;exact af g a5 b hb)
 simp only[Lmc,Lsc,itc] at aw;exact⟨M,a9,by omega,fw,ay,q⟩
lemma KU (a6:Ao C){E:Finset (Sym2 (Fin 11))}{c:Fin 11}{L:Finset (Fin 11)}{W_c M_cand:Finset ℕ}(ab:M_cand⊆mixing G11 C)(a9:∀z∈W_c,z < 11+C.gates.length)(af:∀z∈W_c,∀x∈Oi C z,Ga c x)(q:∀w∈L,s(c,w)∈Us C)(a3:∀w∈L,w∈W_c.biUnion (Oi C)\/ ∃t∈Tp C,∃d:Fin 2,∃m∈M_cand,O C (opnd C t d) m/\w∈N C t (1-d))(goods bads:List (St C))(ae:∀g∈goods,g.good)(aa:∀g∈goods,∀b∈bads,g.c≠b.c)(ad:∀b∈bads,b.c≠c)(h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)(j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c -> (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)(a4:∀e∈E,(∃w∈L,e=s(c,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)): ∃M⊆M_cand,E.card<=(rFull G11 C).card+W_c.card+ (goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum+M.card /\
   ∃fw:ℕ->Fin 11,(∀m∈M,fw m∈L/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw m∈N C t (1-d)) /\
    (∀m1∈M,∀m2∈M,m1≠m2->fw m1≠fw m2):=
 ZH (bonus:=0) a6 ab a9 af q a3 goods bads ae aa ad a4
  fun E' ac _ _ _ a8 a7 a5=>QS a6 (ac::goods) bads a7 a8 a5 h j
lemma YW (al:Ao C){E:Finset (Sym2 (Fin 11))}{bonus:ℕ}{c1 c2:Fin 11}{L1 L2:Finset (Fin 11)}{W1 W2 M1c M2c:Finset ℕ}(ay:M1c⊆mixing G11 C)(aw:M2c⊆mixing G11 C)(ag:∀z∈W1,z < 11+C.gates.length)(aa:∀z∈W2,z < 11+C.gates.length)(b6:∀z∈W1,∀x∈Oi C z,Ga c1 x)(am:∀z∈W2,∀x∈Oi C z,Ga c2 x)(a5:∀w∈L1,s(c1,w)∈Us C)(a6:∀w∈L2,s(c2,w)∈Us C)(aq:∀w∈L1,w∈W1.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈M1c,O C (opnd C t d) m/\w∈N C t (1-d))(ax:∀w∈L2,w∈W2.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈M2c,O C (opnd C t d) m/\w∈N C t (1-d))(goods bads:List (St C))(b9:∀g∈goods,g.good)(ar:∀g∈goods,∀b∈bads,g.c≠b.c)(ap:∀b∈bads,b.c≠c1)(an:∀b∈bads,b.c≠c2)(a4:∀e∈E,(∃w∈L1,e=s(c1,w))\/(∃w∈L2,e=s(c2,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x))(au:∀(E':Finset (Sym2 (Fin 11))) (it1 it2:St C),it1.good->it2.good->it1.c=c1->it2.c=c2->it1.W=W1->it2.W=W2 -> (∀e∈E',∃it∈(it1::it2::goods)++bads,∃x∈it.L,e=s(it.c,x)) -> (∀g∈it1::it2::goods,g.good)->(∀g∈it1::it2::goods,∀b∈bads,g.c≠b.c) -> E'.card+bonus<=(rFull G11 C).card+((it1::it2::goods).map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum):
  ∃M1⊆M1c,∃M2⊆M2c,E.card+bonus<=(rFull G11 C).card+W1.card+W2.card+
    (goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum+M1.card+M2.card /\
   (∃h:ℕ->Fin 11,(∀m∈M1,h m∈L1/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\h m∈N C t (1-d)) /\
    (∀m1∈M1,∀m2∈M1,m1≠m2->h m1≠h m2)) /\
   (∃j:ℕ->Fin 11,(∀m∈M2,j m∈L2/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\j m∈N C t (1-d)) /\
    (∀m1∈M2,∀m2∈M2,m1≠m2->j m1≠j m2)):=by
 classical
 have⟨L10,L1m,M1,b5,ah,a8,ac,be,h,az,af⟩:=QU (L:=L1) (W_c:=W1) al ay a5 aq;have⟨L20,L2m,M2,av,a9,ak,aj,bf,j,b3,ab⟩:=QU (L:=L2) (W_c:=W2) al aw a6 ax;set Em:=L1m.image (fun w=>s(c1,w))∪L2m.image (fun w=>s(c2,w));set E':=E\Em
 have b7:E.card<=E'.card+M1.card+M2.card:=by
  have h1:=Cl (show E⊆E'∪Em from fun e he=>by by_cases hm:e∈Em;exact Ur _ hm;exact Ul _ (Dm he hm))
  have h2:=Cu E' Em;have h3:Em.card<=(L1m.image (fun w=>s(c1,w))).card+(L2m.image (fun w=>s(c2,w))).card:=Cu _ _;have h4:(L1m.image (fun w=>s(c1,w))).card<=L1m.card:=Ci;have h5:(L2m.image (fun w=>s(c2,w))).card<=L2m.card:=Ci;omega
 let it1:St C:=⟨c1,L10,W1,ag,ac,fun _ hx=>a5 _ (a8 hx),True,fun _=>b6⟩;let it2:St C:=⟨c2,L20,W2,aa,aj,fun _ hx=>a6 _ (ak hx),True,fun _=>am⟩
 have bb:=au E' it1 it2 trivial trivial rfl rfl rfl rfl (fun e bd=>by
   have⟨b8,q⟩:=Dp bd
   rcases a4 e b8 with⟨w,hw,rfl⟩|⟨w,hw,rfl⟩|⟨it,Px,x,hx,ba⟩
   ·rw[ah] at hw;rcases Up hw with h0|hm;exact⟨it1,Kc,w,h0,rfl⟩;exact(q (Ul _ (Mi ⟨w,hm,rfl⟩))).elim
   ·rw[a9] at hw;rcases Up hw with h0|hm;exact⟨it2,K2,w,h0,rfl⟩;exact(q (Ur _ (Mi ⟨w,hm,rfl⟩))).elim
   ·exact⟨it,Km _ (Km _ Px),x,hx,ba⟩)
  (fun g hg=>by rcases Kp hg with rfl|h1;exact trivial;rcases Kp h1 with rfl|h2;exact trivial;exact b9 g h2)
  (fun g hg b hb=>by rcases Kp hg with rfl|h1;exact(ap b hb).symm;rcases Kp h1 with rfl|h2;exact(an b hb).symm;exact ar g h2 b hb)
 simp only[Lmc,Lsc,it1,it2] at bb;exact⟨M1,b5,M2,av,by omega,⟨h,az,af⟩,⟨j,b3,ab⟩⟩
lemma Y9 (a6:Ao C){E:Finset (Sym2 (Fin 11))}{c1 c2:Fin 11}{L1 L2:Finset (Fin 11)}{W1 W2 M1c M2c:Finset ℕ}(ah:M1c⊆mixing G11 C)(af:M2c⊆mixing G11 C)(a5:∀z∈W1,z < 11+C.gates.length)(a4:∀z∈W2,z < 11+C.gates.length)(ak:∀z∈W1,∀x∈Oi C z,Ga c1 x)(a7:∀z∈W2,∀x∈Oi C z,Ga c2 x)(ad:∀w∈L1,s(c1,w)∈Us C)(ae:∀w∈L2,s(c2,w)∈Us C)(ab:∀w∈L1,w∈W1.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈M1c,O C (opnd C t d) m/\w∈N C t (1-d))(ag:∀w∈L2,w∈W2.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈M2c,O C (opnd C t d) m/\w∈N C t (1-d))(goods bads:List (St C))(an:∀g∈goods,g.good)(ac:∀g∈goods,∀b∈bads,g.c≠b.c)(aa:∀b∈bads,b.c≠c1)(a9:∀b∈bads,b.c≠c2)(h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)(j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c -> (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)(q:∀e∈E,(∃w∈L1,e=s(c1,w))\/(∃w∈L2,e=s(c2,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)): ∃M1⊆M1c,∃M2⊆M2c,E.card<=(rFull G11 C).card+W1.card+W2.card+ (goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum+M1.card+M2.card /\
   (∃fw1:ℕ->Fin 11,(∀m∈M1,fw1 m∈L1/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw1 m∈N C t (1-d)) /\
    (∀m1∈M1,∀m2∈M1,m1≠m2->fw1 m1≠fw1 m2)) /\
   (∃fw2:ℕ->Fin 11,(∀m∈M2,fw2 m∈L2/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw2 m∈N C t (1-d)) /\
    (∀m1∈M2,∀m2∈M2,m1≠m2->fw2 m1≠fw2 m2)):=
 YW (bonus:=0) a6 ah af a5 a4 ak a7 ad ae ab ag goods bads an ac aa a9 q
  fun E' am al _ _ _ _ _ _ aj a8 a3=>QS a6 (am::al::goods) bads a8 aj a3 h j
def Xx:=Yg (dF fun v=>dN v fun t=>dN v fun g=>dA t g<|dN g fun j=>Y j v<|Y j t<|dN t fun h=>Y h v<|Y h g<|dN v fun q=>Y q t<|Y q g<|VT j h j q h<|dX) (by decide)
def XK:=Yg (dF fun v=>dN v fun h=>dN v fun g=>dA h g<|dN g fun q=>Y q v<|Y q h<|dN h fun j=>Y j v<|Y j g<|dN h fun x=>Y x v<|dN v fun y=>Y y h<|dA x y<|dX) (by decide)
def X9:=Yg (dF fun v=>dN v fun c0=>dN v fun h=>dA c0 h<|dN v fun j=>Y j c0<|Y j h<|dN h fun x0=>Y x0 v<|Y x0 c0<|Y x0 h<|Y x0 j<|dN j fun g=>dA c0 g<|Y g v<|Y g c0<|Y g h<|Y g j<|Y g x0<|dX) (by decide)
def Zz:=Yg (dF fun v=>dN v fun c0=>dN v fun j=>Y j c0<|dN j fun g=>dA c0 g<|Y g v<|Y g c0<|dN v fun h=>Y h j<|Y h g<|dN h fun q=>Y q v<|Y q j<|VT q g q j g<|dX) (by decide)
def Xb:=Yg (dF fun v=>dN v fun c0=>dN v fun h=>dA c0 h<|dN h fun x0=>Y x0 v<|Y x0 c0<|dN v fun g=>Y g c0<|Y g h<|Y g x0<|dN g fun j=>Y j v<|Y j h<|VT j x0 j h x0<|dN c0 fun w1=>Y w1 v<|Y w1 h<|Y w1 x0<|Y w1 g<|dT x0 w1 g<|dX) (by decide)
def Xt:=Yg (dF fun v=>dN v fun c0=>dN v fun g=>dA c0 g<|dN g fun x0=>Y x0 v<|Y x0 c0<|dN c0 fun h=>Y h v<|Y h g<|VT h x0 h g x0<|dN c0 fun w1=>Y w1 v<|Y w1 g<|Y w1 x0<|dT x0 w1 c0<|dN v fun q=>Y q g<|Y q c0<|Y q x0<|VT h x0 h q x0<|dX) (by decide)
lemma KS (ac:Ao C){a b:ℕ}(ha:a∈Jk C)(hb:b∈Jk C)(Pt:a≠b){v vb:Fin 11}(a7:v≠vb)(a6:∀w∈Mw C a,Ga v w){La Lb:Finset (Fin 11)}{Ma Mb:Finset ℕ}{q j:ℕ->Fin 11}(a3:Ma⊆mixing G11 C)(a5:∀m∈Ma,O C (11+m) a)(z:Mb⊆mixing G11 C)(a4:∀m∈Mb,O C (11+m) b)(aa:∀w∈La,s(v,w)∈Us C)(ab:∀w∈Lb,s(vb,w)∈Us C)(a8:∀m∈Ma,q m∈La/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\q m∈N C t (1-d))(h:∀m1∈Ma,∀m2∈Ma,m1≠m2->q m1≠q m2)(a9:∀m∈Mb,j m∈Lb/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\j m∈N C t (1-d))(g:∀m1∈Mb,∀m2∈Mb,m1≠m2->j m1≠j m2): Ma.card+Mb.card<=(mixing G11 C).card+(rZero G11 C).card:=
 (Y0 ac ha hb Pt a7 a6 a3 a5 z a4 aa ab a8 h a9 g).1
def ZM:=Yg (dF fun v=>dN v fun w0=>dN v fun g=>dA g w0<|dN v fun x0=>Y x0 w0<|Y x0 g<|dN g fun h=>dA x0 h<|Y h v<|Y h w0<|dX) (by decide)
def Xd:=Yg (dF fun v=>dN v fun c0=>dN v fun h=>Y h c0<|dN c0 fun q=>Y q v<|Y q h<|dN c0 fun g=>Y g v<|Y g h<|Y g q<|dN q fun x0=>Y x0 v<|Y x0 c0<|Y x0 h<|Y x0 q<|Y x0 g<|dT x0 g h<|dN g fun j=>Y j v<|Y j c0<|Y j h<|Y j q<|Y j g<|Y j x0<|dT j q h<|dN h fun t=>Y t v<|Y t q<|Y t j<|Y t x0<|Y t g<|dT t j x0<|dT t q g<|dX) (by decide)
lemma Kv (b5:Ao C){E:Finset (Sym2 (Fin 11))}(goods bads:List (St C))(b9:∀g∈goods,g.good)(b3:∀e∈E,∃it∈goods++bads,∃x∈it.L,e=s(it.c,x))(a7:∀g∈goods,∀b∈bads,g.c≠b.c)(a8:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)(aa:∀b1∈bads,∀b2∈bads,b1.c≠b2.c -> (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1){g1 g2:St C}(ac:g1∈goods)(ap:g2∈goods)(hne12:g1.c≠g2.c)(hadj12:Ga g1.c g2.c)(ae:g2.c∈g1.W.biUnion (Oi C))(af:g1.c∈g2.W.biUnion (Oi C)): E.card+1<=(rFull G11 C).card+(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum:=by
 classical
 let items:=goods++bads;let centers:=(items.map StarSpec.c).toFinset;let z (c:Fin 11):=items.filter (fun it=>it.c==c);let q (c:Fin 11):Finset (Fin 11):=(z c).foldr (fun it ab=>it.L∪ab) ∅;have hmg {c:Fin 11} {it}:it∈z c↔it∈items/\it.c=c:=by simp[z]
 have t {g:St C} (hg:g∈goods):g.c∈centers:=Mtf (List.mem_map.mpr ⟨g,Kal _ hg,rfl⟩)
 have a3 (c:Fin 11):q c⊆((z c).foldr (fun (it:St C) ab=>it.W∪ab) ∅).biUnion (Oi C):=fun x hx=>by obtain⟨it,Px,a6⟩:=(Qf StarSpec.L (z c) x).mp hx;have⟨w,hw,ah⟩:=Bup (it.hL a6);exact Mbu ⟨w,(Qf StarSpec.W (z c) w).mpr ⟨it,Px,hw⟩,ah⟩
 have j (c:Fin 11):∀x∈q c,s(c,x)∈Us C:=fun x hx=>by obtain⟨it,Px,a6⟩:=(Qf StarSpec.L (z c) x).mp hx;obtain⟨_,rfl⟩:=hmg.mp Px;exact it.he x a6
 have a4 {g:St C} (hg:g∈goods):∀i∈items,i.c=g.c->i.good:=fun i hi hc=>
  (Kap hi).elim (b9 i) fun ak=>(a7 g hg i ak hc.symm).elim
 have a5 {b:St C} (hb:b∈bads):∀i∈items,i.c=b.c->i=b:=fun i hi hc=>
  (Kap hi).elim (fun b4=>(a7 i b4 b hb hc).elim) fun ak=>a8 i ak b hb hc
 have am (gc:Fin 11) (hgc_sep:∀b∈bads,b.c≠gc) (X:Fin 11->Finset (Fin 11))
   (hX_sub:∀c,X c⊆((z c).foldr (fun (it:St C) ab=>it.W∪ab) ∅).biUnion (Oi C))
   (hX_adj:∀c,∀x∈X c,Ga c x) (hX_eq:∀c,c≠gc->X c=q c)
   (hX_ghost:∀c,∃g:Fin 11,∀x∈X c,x≠g->s(c,x)∈Us C):
   ∑c∈centers,(X c).card<=(rFull G11 C).card+(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum:=by
  have ba:=YA b5 items X hX_sub hX_adj hX_ghost fun b7 h1 b6 h2 Pt=>by
   rcases Kap h1 with av|al
   ·exact Ql (a4 av)
   ·rcases Kap h2 with aw|aj
    ·exact Qr (Ql (a4 aw))
    ·have ar {itb:St C} (hb:itb∈bads):X itb.c⊆itb.L:=fun x hx=>by
      rw[hX_eq itb.c (hgc_sep itb hb)] at hx;obtain⟨it,Px,a6⟩:=(Qf StarSpec.L (z itb.c) x).mp hx;have⟨az,hc⟩:=hmg.mp Px;rwa[a5 hb it az hc] at a6
     refine Qr (Qr ⟨a5 al,a5 aj,(aa b7 al b6 aj Pt).elim
      (fun hs=>Ql ((Cl (Isi (Sr _) (ar aj))).trans hs))
      (fun hs=>Qr ((Cl (Isi (Sr _) (ar al))).trans hs))⟩)
  have bb:(items.map (fun it=>it.W.card)).sum=(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum:=by simp[items]
  change ∑c∈centers,(X c).card<=(rFull G11 C).card+(items.map (fun it=>it.W.card)).sum at ba;omega
 have ad:E⊆centers.biUnion (fun c=>(q c).image (fun x=>s(c,x))):=fun e he=>by
  obtain⟨it,Px,x,hx,rfl⟩:=b3 e he
  exact Mbu ⟨it.c,Mtf (List.mem_map.mpr ⟨it,Px,rfl⟩),
   Mi ⟨x,(Qf StarSpec.L (z it.c) x).mpr ⟨it,hmg.mpr ⟨Px,rfl⟩,hx⟩,rfl⟩⟩
 have a9 {ga gb:St C} (hga:ga∈goods) (hadj:Ga ga.c gb.c) (hgb_in:gb.c∈ga.W.biUnion (Oi C)) (hnot:gb.c∉q ga.c):
   E.card+1<=(rFull G11 C).card+(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum:=by
  let X (c:Fin 11):Finset (Fin 11):=if c=ga.c then insert gb.c (q ga.c) else q c
  have hE_le:E.card+1<=∑c∈centers,(X c).card:=by
   have h1:E.card<=∑c∈centers,(q c).card:=(Cl ad).trans (Cbu.trans (Sls fun _ _=>Ci));have h2:=Finset.add_sum_erase centers (fun c=>(q c).card) (t hga);have h3:=Finset.add_sum_erase centers (fun c=>(X c).card) (t hga);have h4:∑c∈centers.erase ga.c,(X c).card=∑c∈centers.erase ga.c,(q c).card:=Finset.sum_congr rfl fun c hc=>by simp[X,(Finset.mem_erase.mp hc).1]
   have h5:(X ga.c).card=(q ga.c).card+1:=by simp[X,Cns hnot]
   omega
  exact hE_le.trans (am ga.c (fun b hb=>(a7 ga hga b hb).symm) X
   (fun c=>by
    dsimp only[X];split_ifs with h
    ·subst h;intro x hx;rcases Nsp hx with rfl|ag
     ·have⟨w,hw,ah⟩:=Bup hgb_in
      exact Mbu ⟨w,(Qf StarSpec.W (z ga.c) w).mpr ⟨ga,hmg.mpr ⟨Kal _ hga,rfl⟩,hw⟩,ah⟩
     ·exact a3 ga.c ag
    ·exact a3 c)
   (fun c x hx=>by
    dsimp only[X] at hx;split_ifs at hx with h
    ·subst h;rcases Nsp hx with rfl|ag;exact hadj;exact Eg (Dp (j ga.c x ag)).1
    ·exact Eg (Dp (j c x hx)).1)
   (fun c hc=>by simp[X,hc])
   (fun c=>by
    by_cases hc:c=ga.c
    ·subst hc;exact⟨gb.c,fun x hx Pt=>by simp only[X,↓reduceIte,Finset.mem_insert] at hx;exact j ga.c x (hx.resolve_left Pt)⟩
    ·exact⟨c,fun x hx _=>by simp only[X,ite_eq_right hc] at hx;exact j c x hx⟩))
 by_cases an:g2.c∈q g1.c
 ·by_cases aq:g1.c∈q g2.c
  ·let A:=(q g1.c).image (fun x=>s(g1.c,x));let B:=(centers.erase g1.c).biUnion (fun c=>(q c).image (fun x=>s(c,x)))
   have b8:centers.biUnion (fun c=>(q c).image (fun x=>s(c,x)))=A∪B:=by
    ext e;simp only[A,B,Finset.mem_biUnion,Finset.mem_union,Finset.mem_erase];constructor
    ·rintro⟨c,hc,he⟩;exact if hcg:c=g1.c then Ql (hcg▸he) else Qr ⟨c,⟨hcg,hc⟩,he⟩
    ·rintro (he|⟨c,⟨_,hc⟩,he⟩);exact⟨g1.c,t ac,he⟩;exact⟨c,hc,he⟩
   have h0:=Cl ad;rw[b8] at h0;have h1:=Cui A B;have h2:1<=(A∩B).card:=Cpr ⟨s(g1.c,g2.c),Im (Mi ⟨g2.c,an,rfl⟩) (Mbu ⟨g2.c,Finset.mem_erase.mpr ⟨hne12.symm,t ap⟩,Mi ⟨g1.c,aq,Sw⟩⟩)⟩;have hA:A.card<=(q g1.c).card:=Ci;have hB:B.card<=∑c∈centers.erase g1.c,(q c).card:=Cbu.trans (Sls fun _ _=>Ci);have bd:=Finset.add_sum_erase centers (fun c=>(q c).card) (t ac);have hE_le:E.card+1<=∑c∈centers,(q c).card:=by omega
   exact hE_le.trans (am g1.c (fun b hb=>(a7 g1 ac b hb).symm) q a3 (fun c x hx=>Eg (Dp (j c x hx)).1) (fun _ _=>rfl) (fun c=>⟨c,fun x hx _=>j c x hx⟩))
  ·exact a9 ap hadj12.symm af aq
 ·exact a9 ac hadj12 ae an
def Zx:=Yg (dF fun v=>dN v fun h=>dN h fun z=>Y z v<|dN z fun x0=>Y x0 v<|Y x0 h<|dN z fun g=>Y g v<|Y g h<|Y g x0<|dT x0 g h<|dN x0 fun q=>Y q v<|Y q z<|Y q h<|Y q g<|dN g fun j=>Y j v<|Y j z<|Y j h<|Y j x0<|Y j q<|dT j q h<|dN h fun t=>Y t z<|Y t q<|Y t j<|Y t x0<|Y t g<|dT t j x0<|dT t q g<|dX) (by decide)
def ZF:=Yg (dF fun v=>dN v fun w0=>dN w0 fun q=>Y q v<|dN v fun c0=>Y c0 q<|dN q fun x0=>Y x0 v<|Y x0 w0<|Y x0 c0<|dN q fun g=>dA c0 g<|Y g v<|Y g w0<|Y g c0<|Y g x0<|dT x0 g w0<|dN x0 fun h=>dA c0 h<|Y h v<|Y h q<|Y h w0<|Y h g<|dN g fun j=>Y j v<|Y j q<|Y j w0<|Y j c0<|Y j x0<|Y j h<|dT j h w0<|dX) (by decide)
lemma YM (aa:Ao C){E:Finset (Sym2 (Fin 11))}{c:Fin 11}{L:Finset (Fin 11)}{W_c M_cand:Finset ℕ}(am:M_cand⊆mixing G11 C)(ac:∀z∈W_c,z < 11+C.gates.length)(ag:∀z∈W_c,∀x∈Oi C z,Ga c x)(a4:∀w∈L,s(c,w)∈Us C)(a7:∀w∈L,w∈W_c.biUnion (Oi C)\/ ∃t∈Tp C,∃d:Fin 2,∃m∈M_cand,O C (opnd C t d) m/\w∈N C t (1-d))(goods bads:List (St C))(al:∀g∈goods,g.good)(ad:∀g∈goods,∀b∈bads,g.c≠b.c)(ak:∀b∈bads,b.c≠c)(h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)(j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c -> (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)(a5:∀e∈E,(∃w∈L,e=s(c,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)){g1 g2:St C}(ah:g1∈goods)(af:g2∈goods)(a9:g1.c≠g2.c)(a6:Ga g1.c g2.c)(q:g2.c∈g1.W.biUnion (Oi C))(a3:g1.c∈g2.W.biUnion (Oi C)): ∃M⊆M_cand,E.card+1<=(rFull G11 C).card+W_c.card+ (goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum+M.card /\
   ∃fw:ℕ->Fin 11,(∀m∈M,fw m∈L/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw m∈N C t (1-d)) /\
    (∀m1∈M,∀m2∈M,m1≠m2->fw m1≠fw m2):=
 ZH (bonus:=1) aa am ac ag a4 a7 goods bads al ad ak a5
  fun E' aj _ _ _ ae ab a8=>Kv aa (aj::goods) bads ab ae a8 h j
   (Km _ ah) (Km _ af) a9 a6 q a3
lemma Zw (aa:Ao C){E:Finset (Sym2 (Fin 11))}{c1 c2:Fin 11}{L1 L2:Finset (Fin 11)}{W1 W2 M1c M2c:Finset ℕ}(am:M1c⊆mixing G11 C)(ak:M2c⊆mixing G11 C)(a8:∀z∈W1,z < 11+C.gates.length)(a7:∀z∈W2,z < 11+C.gates.length)(ap:∀z∈W1,∀x∈Oi C z,Ga c1 x)(ab:∀z∈W2,∀x∈Oi C z,Ga c2 x)(ah:∀w∈L1,s(c1,w)∈Us C)(aj:∀w∈L2,s(c2,w)∈Us C)(af:∀w∈L1,w∈W1.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈M1c,O C (opnd C t d) m/\w∈N C t (1-d))(al:∀w∈L2,w∈W2.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈M2c,O C (opnd C t d) m/\w∈N C t (1-d))(goods bads:List (St C))(aw:∀g∈goods,g.good)(ag:∀g∈goods,∀b∈bads,g.c≠b.c)(ae:∀b∈bads,b.c≠c1)(ad:∀b∈bads,b.c≠c2)(h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)(j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c -> (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)(a4:∀e∈E,(∃w∈L1,e=s(c1,w))\/(∃w∈L2,e=s(c2,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)){g1 g2:St C}(av:g1∈goods)(ar:g2∈goods)(a9:g1.c≠g2.c)(a5:Ga g1.c g2.c)(q:g2.c∈g1.W.biUnion (Oi C))(a3:g1.c∈g2.W.biUnion (Oi C)): ∃M1⊆M1c,∃M2⊆M2c,E.card+1<=(rFull G11 C).card+W1.card+W2.card+ (goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum+M1.card+M2.card /\
   (∃fw1:ℕ->Fin 11,(∀m∈M1,fw1 m∈L1/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw1 m∈N C t (1-d)) /\
    (∀m1∈M1,∀m2∈M1,m1≠m2->fw1 m1≠fw1 m2)) /\
   (∃fw2:ℕ->Fin 11,(∀m∈M2,fw2 m∈L2/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) m/\fw2 m∈N C t (1-d)) /\
    (∀m1∈M2,∀m2∈M2,m1≠m2->fw2 m1≠fw2 m2)):=
 YW (bonus:=1) aa am ak a8 a7 ap ab ah aj af al goods bads aw ag ae ad a4
  fun E' au aq _ _ _ _ _ _ an ac a6=>Kv aa (au::aq::goods) bads ac an a6 h j
   (Km _ (Km _ av)) (Km _ (Km _ ar)) a9 a5 q a3
def ZS:=Yg (dF fun v=>dN v fun c0=>dN c0 fun h=>Y h v<|dN c0 fun g=>Y g v<|Y g h<|dN h fun x0=>Y x0 v<|Y x0 c0<|Y x0 g<|dN x0 fun q=>dA q g<|Y q v<|Y q h<|dN g fun j=>Y j v<|Y j c0<|Y j q<|Y j h<|Y j x0<|dN v fun w=>Y w h<|Y w g<|Y w x0<|Y w j<|dT x0 g w<|dT j h w<|dN w fun ub=>Y ub q<|Y ub h<|Y ub j<|Y ub x0<|Y ub g<|dT ub j x0<|dT ub h g<|dX) (by decide)
lemma Z9 (al:Ao C){E:Finset (Sym2 (Fin 11))}(goods:List (St C))(bad:St C)(gh:Fin 11)(af:∀g∈goods,g.good)(ah:∀g∈goods,g.c≠bad.c)(ak:∀e∈E,∃it∈bad::goods,∃x∈it.L,e=s(it.c,x))(a7:gh∉bad.L)(a8:Ga bad.c gh)(ad:gh∈bad.W.biUnion (Oi C)): E.card+1<=(rFull G11 C).card+(goods.map (fun it=>it.W.card)).sum+bad.W.card:=by
 classical
 let items:=bad::goods;let centers:=(items.map StarSpec.c).toFinset;let q (c:Fin 11):=items.filter (fun it=>it.c==c);let Lc (c:Fin 11):Finset (Fin 11):=(q c).foldr (fun it ab=>it.L∪ab) ∅;have hmg {c:Fin 11} {it}:it∈q c↔it∈items/\it.c=c:=by simp[q]
 have t:bad.c∈centers:=Mtf (List.mem_map.mpr ⟨bad,Kc,rfl⟩)
 have a5:gh∉Lc bad.c:=fun h=>a7 (by
  obtain⟨it,Px,z⟩:=(Qf StarSpec.L (q bad.c) gh).mp h;have⟨aj,hc⟩:=hmg.mp Px
  rcases Kp aj with rfl|hg;exact z;exact(ah it hg hc).elim)
 let X (c:Fin 11):Finset (Fin 11):=if c=bad.c then insert gh (Lc bad.c) else Lc c
 have a4 (c:Fin 11):Lc c⊆((q c).foldr (fun (it:St C) ab=>it.W∪ab) ∅).biUnion (Oi C):=fun x hx=>by obtain⟨it,Px,z⟩:=(Qf StarSpec.L (q c) x).mp hx;have⟨w,hw,aa⟩:=Bup (it.hL z);exact Mbu ⟨w,(Qf StarSpec.W (q c) w).mpr ⟨it,Px,hw⟩,aa⟩
 have j (c:Fin 11):∀x∈Lc c,s(c,x)∈Us C:=fun x hx=>by obtain⟨it,Px,z⟩:=(Qf StarSpec.L (q c) x).mp hx;obtain⟨_,rfl⟩:=hmg.mp Px;exact it.he x z
 have ae:E⊆centers.biUnion (fun c=>(Lc c).image (fun x=>s(c,x))):=fun e he=>by
  obtain⟨it,Px,x,hx,rfl⟩:=ak e he
  exact Mbu ⟨it.c,Mtf (List.mem_map.mpr ⟨it,Px,rfl⟩),
   Mi ⟨x,(Qf StarSpec.L (q it.c) x).mpr ⟨it,hmg.mpr ⟨Px,rfl⟩,hx⟩,rfl⟩⟩
 have an:E.card+1<=∑c∈centers,(X c).card:=by
  have h1:E.card<=∑c∈centers,(Lc c).card:=(Cl ae).trans (Cbu.trans (Sls fun _ _=>Ci));have h2:=Finset.add_sum_erase centers (fun c=>(Lc c).card) t;have h3:=Finset.add_sum_erase centers (fun c=>(X c).card) t;have h4:∑c∈centers.erase bad.c,(X c).card=∑c∈centers.erase bad.c,(Lc c).card:=Finset.sum_congr rfl fun c hc=>by simp[X,(Finset.mem_erase.mp hc).1]
  have h5:(X bad.c).card=(Lc bad.c).card+1:=by simp[X,Cns a5]
  omega
 have am:=YA al items X
  (fun c=>by
   dsimp only[X];split_ifs with h
   ·subst h;intro x hx;rcases Nsp hx with rfl|a9
    ·have⟨w,hw,aa⟩:=Bup ad
     exact Mbu ⟨w,(Qf StarSpec.W (q bad.c) w).mpr ⟨bad,hmg.mpr ⟨Kc,rfl⟩,hw⟩,aa⟩
    ·exact a4 bad.c a9
   ·exact a4 c)
  (fun c x hx=>by
   dsimp only[X] at hx;split_ifs at hx with h
   ·subst h;rcases Nsp hx with rfl|a9
    ·exact a8
    ·exact Eg (Dp (j bad.c x a9)).1
   ·exact Eg (Dp (j c x hx)).1)
  (fun c=>by
   by_cases hc:c=bad.c
   ·subst hc;exact⟨gh,fun x hx Pt=>by simp only[X,↓reduceIte,Finset.mem_insert] at hx;exact j bad.c x (hx.resolve_left Pt)⟩
   ·exact⟨c,fun x hx _=>by simp only[X,if_neg hc] at hx;exact j c x hx⟩)
  (fun it1 _ aq _ Pt=>by
   by_cases h1:it1.c=bad.c
   ·exact Qr (Ql fun i hi hc=>by rcases Kp hi with rfl|hg;exact(Pt (h1.trans hc)).elim;exact af i hg)
   ·exact Ql fun i hi hc=>by rcases Kp hi with rfl|hg;exact(h1 hc.symm).elim;exact af i hg)
 have ap:(items.map (fun it=>it.W.card)).sum=bad.W.card+(goods.map (fun it=>it.W.card)).sum:=by simp[items]
 change ∑c∈centers,(X c).card<=(rFull G11 C).card+(items.map (fun it=>it.W.card)).sum at am;omega
def ZP:=Yg (dF fun v=>dN v fun h=>dN v fun j=>dA h j<|dN j fun x0=>Y x0 v<|Y x0 h<|dN h fun t=>dA x0 t<|Y t v<|Y t j<|dN h fun g=>Y g v<|Y g j<|Y g x0<|Y g t<|dN j fun q=>dA g q<|Y q v<|Y q h<|Y q x0<|Y q t<|dN x0 fun z=>dA z g<|Y z v<|Y z t<|Y z q<|dX) (by decide)
def ZN:=Yg (dF fun z=>dN z fun w0=>dN z fun x0=>Y x0 w0<|dN z fun g=>Y g w0<|Y g x0<|dT x0 g w0<|dN w0 fun t=>Y t z<|Y t x0<|Y t g<|dN w0 fun q=>Y q z<|Y q x0<|Y q g<|Y q t<|dN x0 fun j=>Y j z<|Y j w0<|Y j x0<|Y j g<|Y j t<|Y j q<|dT t j g<|dT q j g<|dN g fun h=>Y h z<|Y h w0<|Y h x0<|Y h g<|Y h t<|Y h q<|Y h j<|dT h j w0<|dT t h x0<|dT q h x0<|dX) (by decide)
lemma QP (j:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(q:Joint G11 C a b):N C b (1-db)⊆Mw C a:=fun w hw=>by
 refine Fk (Uv _) (fun x g h=>?_)
 exact q x g ((QR j hT hs hrb hno2 x).mpr ⟨Ql g,⟨w,hw,h⟩⟩)
lemma YG (h:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){z:Fin 11}(q:z∈N C a 0)(t:z∈N C a 1)(j:z∈N C b (1-db)): z∉Mw C b/\∀w∈Mw C b,Ga z w:=by
 have g (x:Fin 11->Bool) (hxz:x z=true):Gv C b x=true:=
  (QR h hT hs hrb hno2 x).mpr
   ⟨Ql ((Qv h hT hs hab x).mpr ⟨⟨z,q,hxz⟩,⟨z,t,hxz⟩⟩),⟨z,j,hxz⟩⟩
 refine⟨fun a3=>?_,fun w hw=>?_⟩
 ·exact G11.irrefl ((Qx G11 z z).mp ((Fp a3).2 (Pi z z) (g _ (Q8 z z)) (Q8 z z)))
 ·exact(Qx G11 z w).mp ((Fp hw).2 _ (g _ (Q8 z w)) (Qq z w))
lemma Ym {b:ℕ}{db d:Fin 2}{u v:Fin 11}(h0:∃x0∈N C b db,x0=u\/x0=v)(q:∃x1∈N C b (1-db),x1=u\/x1=v)(j:u∉N C b d):v∈N C b d:=by
 rcases Qn db d with rfl|rfl
 ·obtain⟨x0,h,rfl|rfl⟩:=h0
  ·exact(j h).elim
  ·exact h
 ·obtain⟨x1,g,rfl|rfl⟩:=q
  ·exact(j g).elim
  ·exact g
lemma Yt {b:ℕ}{db:Fin 2}{u v:Fin 11}(h0:∃x0∈N C b db,x0=u\/x0=v)(g:∃x1∈N C b (1-db),x1=u\/x1=v)(h:u∉N C b 0∩N C b 1)(hv:v∉N C b 0∩N C b 1): (u∈N C b 0/\v∈N C b 1)\/ (u∈N C b 1/\v∈N C b 0):=by
 fin_cases db
 ·exact ZJ h0 g h hv
 ·exact ZJ g h0 h hv
lemma Wk (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(q:¬((T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b)): Bd C:=by
 classical
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 have g:∀w:Fin 11,¬Tc C b w:=fun w hw=>q (Kt hw)
 by_cases aa:Joint G11 C a b/\∃t∈Tp C,∃d:Fin 2,O C (opnd C t d) a/\O C (opnd C t (1-d)) b
 ·have⟨hJ,t0,ax,d0,af,aj⟩:=aa
  have a5:=QP hL.1 hT hs hrb hno2 hJ
  have am:(centreless G11 C\T0For G11 C a).Nonempty:=by
   rcases Xp hL.1 hs ax af aj with h|h|h
   ·exact h
   ·exact(q (Ql h)).elim
   ·exact(q (Qr h)).elim
  have al:(W0For G11 C a).card+1<=(centreless G11 C).card:=by have h1:=Qj (G:=G11) (C:=C) a;have h2:(centreless G11 C\T0For G11 C a).card+(T0For G11 C a).card=(centreless G11 C).card:=Csd (Fs _ _);have h3:=Cpr am;omega
  have j:∀u v:Fin 11,s(u,v)∈Us C ->
    Gv C a (Pi u v)=true/\(u∈Mw C a\/v∈Mw C a) /\
    (Tc C a u\/Tc C a v\/u∈N C b (1-db)\/v∈N C b (1-db)):=fun u v he=>by
   rcases QM hL hT hs hrb hno2 he with⟨a3,a9⟩|⟨_,_,_,⟨_,hc⟩|⟨_,hc⟩⟩
   ·rcases a9 with av|⟨_,ad|ad⟩|⟨_,ac|a4,_⟩
    ·refine⟨a3,?_,by tauto⟩;rcases av with h|h<;>[exact Ql (Q5 hL.1 h);exact Qr (Q5 hL.1 h)]
    ·exact(g _ ad).elim
    ·exact(g _ ad).elim
    ·exact⟨a3,Ql (a5 ac),Qr (Qr (Ql ac))⟩
    ·exact⟨a3,Qr (a5 a4),Qr (Qr (Qr a4))⟩
   ·exact(g _ hc).elim
   ·exact(g _ hc).elim
  rcases Zt hL hT hs hab (fun u v he=>⟨(j u v he).1,(j u v he).2.1⟩) with ae|⟨v,a7,hA02,hA12⟩
  ·exact ae
  ·have a6:=(Q1 hL.1 ha (Ip (a7▸Ss v)).1 (Ip (a7▸Ss v)).2).1
   refine YU hL hT hs hab a7 hA02 hA12 (fun u w he=>⟨(j u w he).1,(j u w he).2.1⟩)
    (insert (opnd C b (1-db)) (W0For G11 C a))
    (fun z hz=>by rcases Nsp hz with rfl|h;exact Qe hL.1 hb (1-db);exact Qg hL.1 a z h)
    (by have:=Cil (opnd C b (1-db)) (W0For G11 C a);omega) fun w hw=>?_
   rcases(j v w (Zl hw)).2.2 with ar|au|a4|ah
   ·exact(a6 (Q5 hL.1 ar)).elim
   ·rcases au with h0|⟨t,ht,d,m,hm,ap,aq⟩
    ·exact Ql (Bub _ (Finset.subset_insert _ _) h0)
    ·exact Qr ⟨t,ht,d,m,(Fp hm).1,ap,aq⟩
   ·exact(a6 (a5 a4)).elim
   ·exact Ql (Mbu ⟨opnd C b (1-db),Finset.mem_insert_self _ _,ah⟩)
 ·refine Zc hL hT hs hab fun u v he=>?_
  rcases QM hL hT hs hrb hno2 he with⟨a3,a9⟩|⟨_,_,_,⟨_,hc⟩|⟨_,hc⟩⟩
  ·rcases a9 with (hu|hv)|⟨_,ab|ab⟩|⟨hJ,_,t,ht,d,an,ag⟩
   ·exact⟨a3,Ql ⟨Q5 hL.1 hu,Ql hu⟩⟩
   ·exact⟨a3,Qr ⟨Q5 hL.1 hv,Ql hv⟩⟩
   ·exact(g _ ab).elim
   ·exact(g _ ab).elim
   ·exact(aa ⟨hJ,t,ht,d,an,ag⟩).elim
  ·exact(g _ hc).elim
  ·exact(g _ hc).elim
def YX:=Yg (dF fun y1=>dN y1 fun j=>dN y1 fun t=>Bh j t<|dF fun g=>Y g y1<|Y g j<|Y g t<|dN g fun q=>Y q y1<|Y q j<|Y q t<|dN g fun h=>Bh q h<|Y h y1<|Y h j<|Y h t<|dF fun w1=>Y w1 y1<|Y w1 j<|Y w1 t<|Y w1 g<|Y w1 q<|Y w1 h<|dT j g w1<|dT t g w1<|dT q y1 w1<|dT h y1 w1<|dF fun z=>Bh w1 z<|Y z y1<|Y z j<|Y z t<|Y z g<|Y z q<|Y z h<|dT j g z<|dT t g z<|dT q y1 z<|dT h y1 z<|dX) (by decide)
lemma Vv {u a1 a2 h g j:Fin 11}(h1:Ga u a1)(h2:Ga u a2)(h3:Ga u h)(h4:Ga u g)(h5:Ga u j)(a6:a1≠a2)(a7:a1≠h)(a8:a1≠g)(ac:a1≠j)(t:a2≠h)(ad:a2≠g)(ae:a2≠j)(ab:h≠g)(a9:h≠j)(z:g≠j):False:=by
 have af:(ZU u).length<=4:=(by decide:∀x:Fin 11,(ZU x).length<=4) u
 have q:({a1,a2,h,g,j}:Finset (Fin 11))⊆(ZU u).toFinset:=fun x hx=>by
  simp only[Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl<;>exact Mtf (VA (by assumption))
 have ah:({a1,a2,h,g,j}:Finset (Fin 11)).card=5:=by
  rw[Cns (by simp[a6,a7,a8,ac]),
    Cns (by simp[t,ad,ae]),
    Cns (by simp[ab,a9]),
    Cp z]
 have ag:=(Cl q).trans (List.toFinset_card_le _);omega
@[simp] lemma Pg (C:Ck) c L w hw hL he gd hgd:(Q0 C c L w hw hL he gd hgd).c=c:=rfl
@[simp] lemma V9 (C:Ck) c L w hw hL he gd hgd:(Q0 C c L w hw hL he gd hgd).L=L:=rfl
@[simp] lemma Kf (C:Ck) c L w hw hL he gd hgd:(Q0 C c L w hw hL he gd hgd).W={w}:=rfl
@[simp] lemma P3 (C:Ck) c L w hw hL he gd hgd:(Q0 C c L w hw hL he gd hgd).good=gd:=rfl
@[simp] lemma BR (h:Ao C){g:ℕ}(j:g∈Jk C) d c hcS hcW E hEU: (Q9 h j d c hcS hcW E hEU).c=c:=rfl
@[simp] lemma BK (h:Ao C){g:ℕ}(j:g∈Jk C) d c hcS hcW E hEU: (Q9 h j d c hcS hcW E hEU).L=Q4 c E∩N C g (1-d):=rfl
@[simp] lemma BM (h:Ao C){g:ℕ}(j:g∈Jk C) d c hcS hcW E hEU: (Q9 h j d c hcS hcW E hEU).W={opnd C g (1-d)}:=rfl
@[simp] lemma Bz (h:Ao C){g:ℕ}(j:g∈Jk C) d c hcS hcW E hEU: (Q9 h j d c hcS hcW E hEU).good=True:=rfl
lemma Qh {u v:Fin 11}(h:s(u,v)∈Us C):Ga u v:=
 Eg (D1 h)
lemma QV {u v a b:Fin 11}(h:u≠v)(hab:a≠b)(j:Ga u a)(h2:Ga v a)(t:Ga u b)(q:Ga v b):False:=by
 have hc:=Cl (show ({a,b}:Finset (Fin 11))⊆Finset.univ.filter (fun z=>G11.Adj u z/\G11.Adj v z) from fun z g=>by
  rcases Nsp g with rfl|g
  ·exact Fm ⟨Uv _,j,h2⟩
  ·rw[Sp g];exact Fm ⟨Uv _,t,q⟩)
 rw[Cp hab] at hc;have:=Q3 u v h;omega
lemma X6 {E:Finset (Sym2 (Fin 11))}{g:List (St C)}(h:∀u v,s(u,v)∈E->∃it∈g,(u=it.c/\v∈it.L)\/(v=it.c/\u∈it.L)): ∀e∈E,∃it∈g,∃x∈it.L,e=s(it.c,x):=fun e he=>by
 induction e using Sym2.ind with| _ u v=>
 obtain⟨it,Px,⟨rfl,hv⟩|⟨rfl,hu⟩⟩:=h u v he
 ·exact⟨it,Px,v,hv,rfl⟩
 ·exact⟨it,Px,u,hu,Sw⟩
lemma Z6 {E:Finset (Sym2 (Fin 11))}{it:St C}(h:∀u v,s(u,v)∈E->(u=it.c/\v∈it.L)\/(v=it.c/\u∈it.L)): ∀e∈E,∃x∈it.L,e=s(it.c,x):=fun e he=>by
 induction e using Sym2.ind with| _ u v=>
 rcases h u v he with⟨rfl,hv⟩|⟨rfl,g⟩
 ·exact⟨v,hv,rfl⟩
 ·exact⟨u,g,Sw⟩
def Yu (C:Ck)(a:ℕ):Finset (Sym2 (Fin 11)):=
 (Us C).filter fun e=>∃u v:Fin 11,e=s(u,v)/\Gv C a (Pi u v)=false
def Vt (C:Ck)(a:ℕ):Finset (Sym2 (Fin 11)):=Us C\Yu C a
def Yx (C:Ck)(a:ℕ):Finset (Sym2 (Fin 11)):=
 (Vt C a).filter fun e=>∃u v:Fin 11,e=s(u,v)/\(u∈Mw C a\/v∈Mw C a)
def Ya (C:Ck)(a:ℕ):Finset (Sym2 (Fin 11)):=Vt C a\Yx C a
lemma QA:Yu C a⊆Us C:=Fs _ _
lemma V7:Vt C a⊆Us C:=Ds
lemma K0:Yx C a⊆Us C:=(Fs _ _).trans Ds
lemma Qu:Ya C a⊆Us C:=Ds.trans Ds
lemma Kr (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){u v:Fin 11}(he:s(u,v)∈Yu C a): Gv C a (Pi u v)=false /\ (∃x0∈N C b db,x0=u\/x0=v) /\ (∃x1∈N C b (1-db),x1=u\/x1=v) /\ ((u∈Mw C b/\Tc C b u)\/(v∈Mw C b/\Tc C b v)):=by
 obtain⟨u',v',t,g⟩:=(Fp he).2
 have q:Gv C a (Pi u v)=false:=by
  rcases Sy2 t with⟨rfl,rfl⟩|⟨rfl,rfl⟩;exact g;rwa[Zg] at g
 rcases QM hL hT hs hrb hno2 (QA he) with⟨j,_⟩|h
 ·rw[q] at j;cases j
 ·exact h
lemma WN (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){u v:Fin 11}(he:s(u,v)∈Vt C a):Gv C a (Pi u v)=true:=by
 have⟨h,g⟩:=Dp he
 rcases QM hL hT hs hrb hno2 h with⟨j,_⟩|⟨q,_⟩
 ·exact j
 ·exact(g (Fm ⟨h,u,v,rfl,q⟩)).elim
lemma Kn (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){u v:Fin 11}(he:s(u,v)∈Yx C a): Gv C a (Pi u v)=true/\(u∈Mw C a\/v∈Mw C a):=by have⟨g,u',v',h,hW⟩:=Fp he;exact⟨WN hL hT hs hrb hno2 g,by rcases Sy2 h with⟨rfl,rfl⟩|⟨rfl,rfl⟩;exact hW;exact hW.symm⟩
lemma Zr (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b}){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){u v:Fin 11}(he:s(u,v)∈Ya C a): Gv C a (Pi u v)=true/\u∉Mw C a/\v∉Mw C a /\ ((u∈Mw C b/\Tc C b u/\v∈N C b (1-db))\/ (v∈Mw C b/\Tc C b v/\u∈N C b (1-db))):=by
 have PW:=K7 hL.1 hT hs hrb hno2;have⟨a3,t⟩:=Dp he;have⟨a7,a6⟩:=Dp a3;have j:u∉Mw C a:=fun h=>t (Fm ⟨a3,u,v,rfl,Ql h⟩);have g:v∉Mw C a:=fun h=>t (Fm ⟨a3,u,v,rfl,Qr h⟩)
 rcases QM hL hT hs hrb hno2 a7 with⟨a8,ab⟩|⟨ac,_⟩
 ·rcases ab with (hc|hc)|⟨q|z,a4|a5⟩|⟨hJ,q|z,_⟩
  ·exact(j (Q5 hL.1 hc)).elim
  ·exact(g (Q5 hL.1 hc)).elim
  ·exact(j (PW (Im q (Q5 hL.1 a4)))).elim
  ·exact⟨a8,j,g,Qr ⟨Q5 hL.1 a5,a5,q⟩⟩
  ·exact⟨a8,j,g,Ql ⟨Q5 hL.1 a4,a4,z⟩⟩
  ·exact(g (PW (Im z (Q5 hL.1 a5)))).elim
  ·exact(j (QP hL.1 hT hs hrb hno2 hJ q)).elim
  ·exact(g (QP hL.1 hT hs hrb hno2 hJ z)).elim
 ·exact(a6 (Fm ⟨a7,u,v,rfl,ac⟩)).elim
lemma WA (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){v a6 a7:Fin 11}(z:N C a 0∩N C a 1={v})(a5:a6∈(N C a 0\N C a 1)∩Mw C a)(a4:a7∈(N C a 1\N C a 0)∩Mw C a)(g:∀w∈Mw C a,w=a6\/w=a7): ∃ita0 ita1:St C,ita0.c=a6/\ita1.c=a7/\ita0.good/\ita1.good /\ ita0.W.card=1/\ita1.W.card=1 /\ ita0.W={opnd C a 1}/\ita1.W={opnd C a 0} /\ ∀e∈Yx C a,(∃x∈ita0.L,e=s(ita0.c,x))\/(∃x∈ita1.L,e=s(ita1.c,x)):=by
 have ha:a∈Jk C:=by simp[hs]
 have Pv:v∈N C a 0:=(Ip (z▸Ss v)).1;have Pu:v∈N C a 1:=(Ip (z▸Ss v)).2;have a3:=(Q1 hL.1 ha Pv Pu).1;have t:=(J2 a5);have q:=(J2 a4);let ita0:=Q9 hL.1 ha 0 a6 (J1 a5) (I2 a5) (Us C) (Sr _);let ita1:=Q9 hL.1 ha 1 a7 (J1 a4) (I2 a4) (Us C) (Sr _);refine⟨ita0,ita1,rfl,rfl,trivial,trivial,Cs _,Cs _,rfl,rfl,fun e he=>?_⟩;have j:=K0 he
 induction e using Sym2.ind with| _ u w=>
 have⟨af,hW⟩:=Kn hL hT hs hrb hno2 he
 by_cases ad:u=v
 ·subst u;rcases g w (hW.resolve_left a3) with rfl|rfl
  ·exact Ql ⟨v,Im (Zm (Sw▸j)) Pu,Sw⟩
  ·exact Qr ⟨v,Im (Zm (Sw▸j)) Pv,Sw⟩
 by_cases ae:w=v
 ·subst w;rcases g u (hW.resolve_right a3) with rfl|rfl
  ·exact Ql ⟨v,Im (Zm j) Pu,rfl⟩
  ·exact Qr ⟨v,Im (Zm j) Pv,rfl⟩
 rcases Qt hL.1 hT hs hab af (fun h=>ad (Sp (z▸h))) (fun h=>ae (Sp (z▸h))) with⟨a9,aa⟩|⟨ab,hw0⟩<;>
  rcases hW with ac|a8
 ·rcases g u ac with rfl|rfl
  ·exact Ql ⟨w,Im (Zm j) aa,rfl⟩
  ·exact(q a9).elim
 ·rcases g w a8 with rfl|rfl
  ·exact(t aa).elim
  ·exact Qr ⟨u,Im (Zm (Sw▸j)) a9,Sw⟩
 ·rcases g u ac with rfl|rfl
  ·exact(t ab).elim
  ·exact Qr ⟨w,Im (Zm j) hw0,rfl⟩
 ·rcases g w a8 with rfl|rfl
  ·exact Ql ⟨u,Im (Zm (Sw▸j)) ab,Sw⟩
  ·exact(q hw0).elim
lemma Vx (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a){v:Fin 11}(g:N C a 0∩N C a 1={v})(hA02:2<=(N C a 0).card)(hA12:2<=(N C a 1).card): (∃ita:List (St C),(ita.map (fun it=>it.W.card)).sum<=1/\(∀it∈ita,it.good/\it.c∈Mw C a) /\
      ∀u w:Fin 11,s(u,w)∈Yx C a->u≠v->w≠v->∃it∈ita,∃x∈it.L,s(u,w)=s(it.c,x))\/
    (∃ca0 ca1:Fin 11,
      ca0∈(N C a 0\N C a 1)∩Mw C a /\
      ca1∈(N C a 1\N C a 0)∩Mw C a /\
      ∀w∈Mw C a,w=ca0\/w=ca1):=by
  have ha:a∈Jk C:=by simp[hs]
  have Pv:v∈N C a 0:=(Ip (g▸Ss v)).1;have Pu:v∈N C a 1:=(Ip (g▸Ss v)).2
  exact Kd hL.1 ha (g▸Sr _) hA02 hA12
    (Q1 hL.1 ha Pv Pu).2 K0 fun u w he q j=>
      ⟨Qt hL.1 hT hs hab (Kn hL hT hs hrb hno2 he).1
        (fun h=>q (Sp (g▸h))) (fun h=>j (Sp (g▸h))),
       (Kn hL hT hs hrb hno2 he).2⟩
lemma Y5 (hL:Ls C) {a b:ℕ} (hs:Jk C={a,b}) {db:Fin 2} (hrb:O C (opnd C b db) a) (hB0ne:(N C b db).Nonempty) (hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b) (goods bads:List (St C)) (a5:(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum<=4)
  (a4:∀g∈goods,g.good)
  (t:∀e∈Us C,∃it∈goods++bads,∃x∈it.L,e=s(it.c,x))
  (z:∀g∈goods,∀b∈bads,g.c≠b.c)
  (h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)
  (j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
   (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1):
  Bd C:=by
 have hb:b∈Jk C:=by simp[hs]
 obtain⟨mb,a3,q,_,_⟩:=QK hL.1 hs hrb hB0ne;have HZ:=QN hL.1 hb a3 q hbWit;have a6:=QS hL.1 goods bads a4 t z h j;omega
lemma Wr (hL:Ls C) {a b:ℕ} (hs:Jk C={a,b}) {db:Fin 2} (hrb:O C (opnd C b db) a) (hB0ne:(N C b db).Nonempty) (hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b) (goods bads:List (St C)) (ab:(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum<=5)
  (a9:∀g∈goods,g.good)
  (a5:∀e∈Us C,∃it∈goods++bads,∃x∈it.L,e=s(it.c,x))
  (a6:∀g∈goods,∀b∈bads,g.c≠b.c)
  (h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)
  (j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
   (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)
  {g1 g2:St C} (aa:g1∈goods) (a8:g2∈goods) (a4:g1.c≠g2.c)
  (z:Ga g1.c g2.c) (q:g2.c∈g1.W.biUnion (Oi C)) (t:g1.c∈g2.W.biUnion (Oi C)):
  Bd C:=by
 have hb:b∈Jk C:=by simp[hs]
 obtain⟨mb,a7,a3,_,_⟩:=QK hL.1 hs hrb hB0ne;have HZ:=QN hL.1 hb a7 a3 hbWit;have ac:=Kv hL.1 goods bads a9 a5 a6 h j aa a8 a4 z q t;omega
lemma Yw (hL:Ls C) {a b:ℕ} (hs:Jk C={a,b}) (hab:Ic C a b) (hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b) {v:Fin 11} (Pv:v∈N C a 0) (Pu:v∈N C a 1) {Lv:Finset (Fin 11)} (t:∀w∈Lv,s(v,w)∈Us C) (a5:∀w∈Lv,Tc C a w) (goods bads:List (St C)) (ac:(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum<=3)
  (a9:∀g∈goods,g.good) (a7:∀g∈goods,∀b∈bads,g.c≠b.c) (a8:∀b∈bads,b.c≠v)
  (h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)
  (j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
   (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)
  (a4:∀e∈Us C,(∃w∈Lv,e=s(v,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)):
  Bd C:=by
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 have Pt:=Nlt (Y4 hab);have a3:=(Q1 hL.1 ha Pv Pu).2
 have⟨Ma,hMa,af,ag,a6,q⟩:=KU (E:=Us C) hL.1 (Fs _ _)
  (Qg hL.1 a) (fun z hz x hx=>a3 x (Qc hL.1 a z hz hx))
  t a5 goods bads a9 a7 a8 h j a4
 have ae:=KG hL.1 Q3 ha hb Pt (hMa.trans (Fs _ _))
  (fun m hm=>(Fp (hMa hm)).2) t a6 q hbWit
 omega
lemma KW (hL:Ls C) {a b:ℕ} (hs:Jk C={a,b}) {db:Fin 2} (hrb:O C (opnd C b db) a) (hB0ne:(N C b db).Nonempty) {vb:Fin 11} (aa:vb∈N C b 0) (ab:vb∈N C b 1) {Lb:Finset (Fin 11)} (a7:∀w∈Lb,s(vb,w)∈Us C) (a5:∀w∈Lb,Tc C b w) (goods bads:List (St C)) (ag:(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum<=3)
  (ad:∀g∈goods,g.good) (a9:∀g∈goods,∀b∈bads,g.c≠b.c) (ae:∀b∈bads,b.c≠vb)
  (j:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)
  (q:∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
   (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)
  (t:∀e∈Us C,(∃w∈Lb,e=s(vb,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)):
  Bd C:=by
 have hb:b∈Jk C:=by simp[hs]
 have a6:=(Q1 hL.1 hb aa ab).2;obtain⟨mb,a8,ac,_,_⟩:=QK hL.1 hs hrb hB0ne
 obtain⟨Mb,hMb,al,_,_,_⟩:=KU (E:=Us C) hL.1 (Fs _ _)
  (Qg hL.1 b) (fun z hz x hx=>a6 x (Qc hL.1 b z hz hx))
  a7 a5 goods bads ad a9 ae j q t
 have a4:mb∉Mb:=fun h=>by have:=Qy hL.1 a8 hb (Fp (hMb h)).2;omega
 have hW:=(Qj (G:=G11) (C:=C) b).trans (Qs b);have hM:=Cl (Ism ⟨a8,hMb.trans (Fs _ _)⟩);rw[Cns a4] at hM;omega
lemma XQ (hL:Ls C) {a b:ℕ} (hs:Jk C={a,b}) (hab:Ic C a b) {v vb:Fin 11} (ac:v≠vb) (Pv:v∈N C a 0) (Pu:v∈N C a 1) (ad:vb∈N C b 0) (af:vb∈N C b 1) {La Lb:Finset (Fin 11)} (a3:∀w∈La,s(v,w)∈Us C) (a8:∀w∈La,Tc C a w) (a4:∀w∈Lb,s(vb,w)∈Us C) (a7:∀w∈Lb,Tc C b w) (goods bads:List (St C)) (ak:(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum<=2)
  (ah:∀g∈goods,g.good) (ab:∀g∈goods,∀b∈bads,g.c≠b.c)
  (aj:∀b∈bads,b.c≠v) (ag:∀b∈bads,b.c≠vb)
  (h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)
  (j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
   (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)
  (a6:∀e∈Us C,(∃w∈La,e=s(v,w))\/(∃w∈Lb,e=s(vb,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)):
  Bd C:=by
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 have Pt:=Nlt (Y4 hab);have t:=(Q1 hL.1 ha Pv Pu).2;have q:=(Q1 hL.1 hb ad af).2
 obtain⟨Ma,hMa,Mb,hMb,hbd,⟨fwa,hfwa,hfwai⟩,⟨fwb,hfwb,hfwbi⟩⟩:=
  Y9 (E:=Us C) hL.1 (Fs _ _) (Fs _ _)
   (Qg hL.1 a) (Qg hL.1 b)
   (fun z hz x hx=>t x (Qc hL.1 a z hz hx))
   (fun z hz x hx=>q x (Qc hL.1 b z hz hx))
   a3 a4 a8 a7 goods bads ah ab aj ag h j a6
 have am:=(Qj (G:=G11) (C:=C) a).trans (Qs a);have al:=(Qj (G:=G11) (C:=C) b).trans (Qs b)
 have HZ:=(Kj hL.1 ha hb Pt ac t q
  (hMa.trans (Fs _ _)) (fun m hm=>(Fp (hMa hm)).2)
  (hMb.trans (Fs _ _)) (fun m hm=>(Fp (hMb hm)).2)
  a3 a4 hfwa hfwai hfwb hfwbi).1
 omega
lemma Wz (hL:Ls C) {a b:ℕ} (hs:Jk C={a,b}) (hab:Ic C a b) {db:Fin 2} (hrb:O C (opnd C b db) a) (hB0ne:(N C b db).Nonempty) {v vb:Fin 11} (aj:v≠vb) (Pv:v∈N C a 0) (Pu:v∈N C a 1) (ak:vb∈N C b 0) (am:vb∈N C b 1) {La Lb:Finset (Fin 11)} (a4:∀w∈La,s(v,w)∈Us C) (ad:∀w∈La,Tc C a w) (a5:∀w∈Lb,s(vb,w)∈Us C) (ac:∀w∈Lb,Tc C b w) (aa:∀mb∈mixing G11 C,Oi C (11+mb)⊆N C b db -> ∀w∈La,∀t∈Tp C,∀d:Fin 2,O C (opnd C t d) mb->w∈N C t (1-d)->False) (goods bads:List (St C)) (ar:(goods.map (fun it=>it.W.card)).sum+(bads.map (fun it=>it.W.card)).sum<=3)
  (ap:∀g∈goods,g.good) (ah:∀g∈goods,∀b∈bads,g.c≠b.c)
  (aq:∀b∈bads,b.c≠v) (an:∀b∈bads,b.c≠vb)
  (h:∀b1∈bads,∀b2∈bads,b1.c=b2.c->b1=b2)
  (j:∀b1∈bads,∀b2∈bads,b1.c≠b2.c ->
   (b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)
  (a8:∀e∈Us C,(∃w∈La,e=s(v,w))\/(∃w∈Lb,e=s(vb,w))\/∃it∈goods++bads,∃x∈it.L,e=s(it.c,x)):
  Bd C:=by
 have ha:a∈Jk C:=by simp[hs]
 have hb:b∈Jk C:=by simp[hs]
 have Pt:=Nlt (Y4 hab);have a3:=(Q1 hL.1 ha Pv Pu).2;have q:=(Q1 hL.1 hb ak am).2;obtain⟨mb,ae,a9,_,a7⟩:=QK hL.1 hs hrb hB0ne
 obtain⟨Ma,hMa,Mb,hMb,hbd,⟨fwa,hfwa,hfwai⟩,⟨fwb,hfwb,hfwbi⟩⟩:=
  Y9 (E:=Us C) hL.1 (Fs _ _) (Fs _ _)
   (Qg hL.1 a) (Qg hL.1 b)
   (fun z hz x hx=>a3 x (Qc hL.1 a z hz hx))
   (fun z hz x hx=>q x (Qc hL.1 b z hz hx))
   a4 a5 ad ac goods bads ap ah aq an h j a8
 have av:=(Qj (G:=G11) (C:=C) a).trans (Qs a);have au:=(Qj (G:=G11) (C:=C) b).trans (Qs b)
 have HZ:=(Kj hL.1 ha hb Pt aj a3 q
  (hMa.trans (Fs _ _)) (fun m hm=>(Fp (hMa hm)).2)
  (hMb.trans (Fs _ _)) (fun m hm=>(Fp (hMb hm)).2)
  a4 a5 hfwa hfwai hfwb hfwbi).2 mb ae a9 (aa mb ae a7)
 omega
lemma YJ (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){v:Fin 11}(h:N C a 0∩N C a 1={v}): 2<=(N C a 0).card/\2<=(N C a 1).card /\ ((N C a 0\N C a 1)∩Mw C a).card<=1 /\ ((N C a 1\N C a 0)∩Mw C a).card<=1:=by
 have Pv:v∈N C a 0:=(Ip (h▸Ss v)).1;have Pu:v∈N C a 1:=(Ip (h▸Ss v)).2;have⟨a5,a4⟩:=Yj hL hT hs hab;have⟨x0,a7,a3⟩:=Nss a5;have⟨x1,a6,z⟩:=Nss a4
 have hA02:2<=(N C a 0).card:=by
  have j:=Cl (show ({v,x0}:Finset (Fin 11))⊆N C a 0 from fun x g=>by
   rcases Nsp g with rfl|g;exact Pv;rw[Sp g];exact a7)
  rw[Cp (fun e=>a3 (by rwa[←e]))] at j;exact j
 have hA12:2<=(N C a 1).card:=by
  have j:=Cl (show ({v,x1}:Finset (Fin 11))⊆N C a 1 from fun x g=>by
   rcases Nsp g with rfl|g;exact Pu;rw[Sp g];exact a6)
  rw[Cp (fun e=>z (by rwa[←e]))] at j;exact j
 exact⟨hA02,hA12,
  Qa Q3 hA12 (fun u t y q=>Y1 hL.1 hT hs hab (J1 t) (I2 t) y q),
  Qa Q3 hA02 (fun y q u t=>Y1 hL.1 hT hs hab (J1 q) (I2 q) u t)⟩
lemma VK (q:Ao C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(d:Fin 2): (((N C a d\N C a (1-d))∩Mw C b)\Mw C a).card<=1\/ (((N C a (1-d)\N C a d)∩N C b (1-db))\Mw C a).card<=1:=by
 by_contra! h
 have hc:(((N C a d\N C a (1-d))∩Mw C b)\Mw C a).card<=1:=
  Qa Q3 (by omega:2<=(((N C a (1-d)\N C a d)∩N C b (1-db))\Mw C a).card)
   (fun u g y j=>K9 q hT hs hab hrb d
    (Dp (Ip (D1 g)).1).1 (Ip (D1 g)).2
    (Dp (Ip (D1 j)).1).1 (Ip (D1 j)).2)
 omega
structure T1a (C:Ck) where
 hL:Ls C
 hT:Tf C
 a:ℕ
 b:ℕ
 hs:Jk C={a,b}
 hab:Ic C a b
 db:Fin 2
 hrb:O C (opnd C b db) a
 hno2:¬O C (opnd C b (1-db)) a
 hB0e:N C b db=∅
namespace T1a
open Finset
abbrev Q2:=Fin 11
abbrev F2:=Fin 2
abbrev U (C:Ck):=Us C
abbrev sl (C:Ck)(c:Q2):=Q4 c (U C)
abbrev TC (C:Ck):=Tc C
abbrev Jh (C:Ck)(M:Finset ℕ)(w:Q2):=
 ∃t∈Tp C,∃d:F2,∃m∈M,O C (opnd C t d) m/\w∈N C t (1-d)
abbrev ME (C:Ck)(W M:Finset ℕ)(w:Q2):=w∈W.biUnion (Oi C)\/Jh C M w
abbrev Th (C:Ck)(L:Finset Q2)(M:Finset ℕ)(fw:ℕ->Q2):=
 ∀m∈M,fw m∈L/\∃t∈Tp C,∃d:F2,O C (opnd C t d) m/\fw m∈N C t (1-d)
abbrev PV (C:Ck):Prop:=
 (U C).card<=2*(centreless G11 C).card+2+
  (rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card
abbrev uq:=@Qp
abbrev H1:=@Qk
abbrev H4:=@QE
lemma i1 {S T:Finset Q2}{x}(h:x∈S∩T):x∈S:=(I1 h)
lemma i2 {S T:Finset Q2}{x}(h:x∈S∩T):x∈T:=(I2 h)
lemma s1 {S T:Finset Q2}{x}(h:x∈S\T):x∈S:=(D1 h)
lemma s2 {S T:Finset Q2}{x}(h:x∈S\T):x∉T:=(D2 h)
lemma Py {S T:Finset Q2}{x}(h:x∈S)(g:x∈T):x∈S∩T:=Im h g
lemma R4 {S T:Finset Q2}{x}(h:x∈S)(g:x∉T):x∈S\T:=Dm h g
lemma d1 {S T V:Finset Q2}{x}(h:x∈(S\T)∩V):x∈S:=s1 (i1 h)
lemma d2 {S T V:Finset Q2}{x}(h:x∈(S\T)∩V):x∉T:=s2 (i1 h)
lemma r1 {S T V:Finset Q2}{x}(h:x∈S∩(T\V)):x∈T:=s1 (i2 h)
lemma r2 {S T V:Finset Q2}{x}(h:x∈S∩(T\V)):x∉V:=s2 (i2 h)
lemma Hp {S T V:Finset Q2}{x}(h:x∈S∩(T\V)):x∈S∩T:=Py (i1 h) (r1 h)
lemma Hu {S T:Finset Q2}{x}(h:S∩T=∅)(j:x∈S)(g:x∈T):False:=notMem_empty x (h▸Py j g)
lemma Hh {S:Finset Q2}{x}(g:S=∅)(h:x∈S):False:=notMem_empty x (g▸h)
lemma MA {A:Finset Q2}{x y:Q2}(g:x≠y)(h:∀z∈A,Ga x z)(j:∀z∈A,Ga y z):A.card<=1:=
 Xc Q3 g h j
lemma Mx {A B:Finset Q2}(g:2<=B.card)(h:∀u∈A,∀v∈B,Ga u v):A.card<=1:=
 Qa Q3 g h
variable {C:Ck} (k:T1a C)
lemma Hr {c x:Q2}(h:x∈sl C c):s(c,x)∈U C:=Zl h
lemma Mn {c x:Q2}(h:s(c,x)∈U C):x∈sl C c:=Zm h
lemma PK {u v:Q2}(h:s(u,v)∈U C):s(v,u)∈U C:=Sw▸h
abbrev A (d:F2):=N C k.a d
abbrev A' (d:F2):=k.A d\k.A (1-d)
abbrev Ia:=k.A 0∩k.A 1
abbrev B1:=N C k.b (1-k.db)
abbrev Wa:=Mw C k.a
abbrev Wb:=Mw C k.b
abbrev W0:=k.Wa∪(k.B1∩k.Wb)
abbrev JE:=k.Wb\k.W0
abbrev Jy:=k.B1\k.Wb
abbrev AW (d:F2):=k.A' d∩k.JE
abbrev AB (d:F2):=k.A' d∩k.Jy
abbrev A0 (d:F2):=k.A' d∩k.W0
abbrev Mp (d:F2):=k.A' d∩k.Wb
open Classical in
noncomputable def lb (c:Q2)(S:Finset Q2):Finset Q2:=(sl C c).filter fun x=>x∈S/\TC C k.b x
lemma PB {c x:Q2}{S:Finset Q2}:x∈k.lb c S↔s(c,x)∈U C/\x∈S/\TC C k.b x:=by
 classical simp[lb,sl,Zk]
lemma ha:k.a∈Jk C:=by simp[k.hs]
lemma hb:k.b∈Jk C:=by simp[k.hs]
lemma TB:k.a≠k.b:=Nlt (Y4 k.hab)
lemma Mk:k.Wa⊆k.Wb:=VJ k.hL.1 k.hT k.hs k.hrb k.hno2 k.hB0e
lemma Hv:k.W0⊆k.Wb:=fun _ h=>(Up h).elim (fun h=>k.Mk h) fun h=>i2 h
lemma PA (d:F2){x:Q2}:x∈k.Ia↔x∈k.A d/\x∈k.A (1-d):=by fin_cases d<;>simp[Ia,A,and_comm]
lemma Mj (d:F2):(k.A' d).Nonempty:=by have⟨h0,h1⟩:=Yj k.hL k.hT k.hs k.hab;fin_cases d<;>exact sdiff_nonempty.mpr (by assumption)
lemma ga {u v:Q2}(he:s(u,v)∈U C):Gv C k.a (Pi u v)=true:=
 (YY k.hL k.hT k.hs k.hrb k.hno2 k.hB0e he).1
lemma ec {u v:Q2}(he:s(u,v)∈U C): (TC C k.a u\/TC C k.a v)\/((u∈k.B1\/v∈k.B1)/\(TC C k.b u\/TC C k.b v)):=
 (YY k.hL k.hT k.hs k.hrb k.hno2 k.hB0e he).2
lemma Hj {u v:Q2}(he:s(u,v)∈U C): (u∈k.W0\/(u∈k.JE/\TC C k.b u/\v∈k.Jy))\/(v∈k.W0\/(v∈k.JE/\TC C k.b v/\u∈k.Jy)):=by
 have j {x y:Q2} (hB:x∈k.B1\/y∈k.B1) (ht:TC C k.b x):
   (x∈k.W0\/(x∈k.JE/\TC C k.b x/\y∈k.Jy))\/y∈k.W0:=by
  have t:=Q5 k.hL.1 ht
  by_cases h:x∈k.W0;· exact .inl (.inl h)
  by_cases q:y∈k.Wb;· exact .inr (by grind)
  exact .inl (.inr ⟨by grind,ht,by grind⟩)
 rcases k.ec he with (g|hv)|⟨hB,g|hv⟩
 ·exact .inl (.inl (Ul _ (Q5 k.hL.1 g)))
 ·exact .inr (.inl (Ul _ (Q5 k.hL.1 hv)))
 ·exact(j hB g).elim .inl (.inr ∘ .inl)
 ·exact(j hB.symm hv).elim .inr (.inl ∘ .inl)
lemma Hb (d:F2){w:Q2}(g:w∈k.A d)(hw0:w∈k.W0):∀z∈k.A (1-d),Ga w z:=
 (Up hw0).elim (Y1 k.hL.1 k.hT k.hs k.hab g) fun h=>VP k.hL.1 k.hT k.hs k.hab k.hrb g (i1 h) (i2 h)
lemma PH {w:Q2}(hw0:w∈k.W0):∀z∈k.Ia,Ga w z:=fun z g=>
 (Up hw0).elim (fun h=>((Q1 k.hL.1 k.ha (i1 g) (i2 g)).2 w h).symm)
  fun h=>VV k.hL.1 k.hT k.hs k.hab k.hrb (i1 h) (i2 h) z (i1 g) (i2 g)
lemma HA (d:F2){w v:Q2}(g:w∈k.A d)(q:w∈k.Wb)(h:v∈k.A (1-d))(j:v∈k.B1):Ga w v:=
 K9 k.hL.1 k.hT k.hs k.hab k.hrb d g q h j
lemma Jz (d:F2){w v:Q2}(hw:w∈k.AW d)(hv:v∈k.AB (1-d)):Ga w v:=k.HA d (d1 hw) (r1 hw) (d1 hv) (r1 hv)
lemma HP {w:Q2}(g:w∈k.Ia)(h:w∈k.Wb):∀v∈k.B1,Ga w v:=
 VX k.hL.1 k.hT k.hs k.hab k.hrb (i1 g) (i2 g) h
lemma M9 {v:Q2}(g:v∈k.Ia)(h:v∈k.B1):v∉k.Wb/\∀w∈k.Wb,Ga v w:=
 Wy k.hL.1 k.hT k.hs k.hab k.hrb (i1 g) (i2 g) h
lemma HU (d:F2){u v w:Q2}(g:u∈k.A d)(hv:v∈k.A (1-d))(hw:w∈k.W0):Ga u v\/Ga u w\/Ga v w:=
 X2 k.hL.1 k.hT k.hs k.hab k.hrb k.hno2 k.hB0e d g hv hw
lemma Hw {v y w:Q2}(hv:v∈k.Ia)(g:y∈k.B1)(hw:w∈k.Wb):Ga v y\/Ga v w\/Ga y w:=
 Xr k.hL.1 k.hT k.hs k.hab k.hrb k.hno2 k.hB0e (i1 hv) (i2 hv) g hw
lemma nA (d:F2){u v:Q2}(he:s(u,v)∈U C)(g:u∉k.A d):v∈k.A d:=
 Kg k.hL.1 k.hT k.hs k.hab d (k.ga he) g
lemma RV (d:F2){u v:Q2}(he:s(u,v)∈U C)(hu:u∉k.Ia)(hv:v∉k.Ia): (u∈k.A' d/\v∈k.A' (1-d))\/(v∈k.A' d/\u∈k.A' (1-d)):=by
 have:=(Y7 k.hL.1 k.hT k.hs k.hab d u v).mp (k.ga he)
 have:=k.PA d (x:=u);have:=k.PA d (x:=v);grind
lemma Mr (d:F2):(k.Mp d).card<=1\/(k.AB (1-d)).card<=1:=by by_contra! h;have:=Mx (A:=k.Mp d) (by omega:2<=(k.AB (1-d)).card) fun u g y j=>k.HA d (d1 g) (i2 g) (d1 j) (r1 j);omega
lemma RK (d:F2)(g:2<=(k.A (1-d)).card):(k.A0 d).card<=1:=Mx g fun _ h z j=>k.Hb d (d1 h) (i2 h) z j
lemma Ha {d:F2}{c x:Q2}(h:(k.Mp d).card<=1)(g:c∈k.A0 d)(j:x∈k.AW d):False:=
 r2 j (uq h (Hp j) (Py (i1 g) (k.Hv (i2 g)))▸i2 g)
lemma T7 {d:F2}{c1 y:Q2}(g:c1∈k.A0 (1-d))(j:y∈k.AB (1-d)):(k.AW d).card<=1:=
 MA (A:=k.AW d) (x:=c1) (y:=y) (fun e=>r2 j (e▸k.Hv (i2 g)))
  (fun u h=>k.Hb (1-d) (d1 g) (i2 g) u (H4 (d1 h))) fun _ h=>(k.Jz d h j).symm
lemma RS {d:F2}{c1:Q2}(g:c1∈k.A0 (1-d)):∃x0:Q2,(k.AB (1-d)).Nonempty->∀u∈k.AW d,u=x0:=by
 by_cases Pt:(k.AB (1-d)).Nonempty
 ·have⟨y,q⟩:=Pt;have⟨x0,j⟩:=H1 (k.T7 g q);exact⟨x0,fun _=>j⟩
 ·exact⟨0,fun h=>(Pt h).elim⟩
def S0:St C:=⟨0,∅,∅,by simp,by simp,by simp,False,False.elim⟩
def HN (P:Prop)[Decidable P](f:P->St C):St C:=if h:P then f h else S0
lemma Re {P:Prop}[Decidable P]{f:P->St C}(g:∀h,(f h).W.card<=1):(HN P f).W.card<=1:=by unfold HN;split_ifs with h;exact g h;simp[S0]
def PF (d:F2)(c:Q2)(S:Finset Q2)(hS:S⊆k.A d):St C:=
 Q0 C c (sl C c∩S) (opnd C k.a d) (Qe k.hL.1 k.ha d) (Ir.trans hS) (fun _ hx=>Hr (i1 hx)) False False.elim
abbrev Hc (d:F2)(c:Q2):=k.PF d c (k.A d) Subset.rfl
abbrev JB (d:F2)(c:Q2):=k.PF d c (k.A' d) Ds
abbrev TJ (d:F2)(c:Q2):=k.PF d c (k.AW d) (Il.trans Ds)
abbrev MX (d:F2)(c:Q2):=k.PF d c (k.AB d) (Il.trans Ds)
def MU (c:Q2)(S:Finset Q2)(hS:S⊆k.B1)(gd:Prop)(hgd:gd->∀x∈k.B1,Ga c x):St C:=
 Q0 C c (sl C c∩S) (opnd C k.b (1-k.db)) (Qe k.hL.1 k.hb (1-k.db)) (Ir.trans hS) (fun _ hx=>Hr (i1 hx)) gd hgd
def PE (c:Q2)(L:Finset Q2)(u v:Q2):Prop:=(u=c/\v∈L)\/(v=c/\u∈L)
abbrev PJ (s:St C)(u v:Q2):Prop:=PE s.c s.L u v
lemma PE.sym {c L u v}:PE c L u v->PE c L v u:=Or.symm
lemma PS {d c u v S hS}(he:s(u,v)∈U C)(g:u=c)(hv:v∈S):PJ (k.PF d c S hS) u v:=.inl ⟨g,Py (Mn (g▸he)) hv⟩
lemma Je {c u v S hS gd hgd}(he:s(u,v)∈U C)(g:u=c)(hv:v∈S):PJ (k.MU c S hS gd hgd) u v:=.inl ⟨g,Py (Mn (g▸he)) hv⟩
lemma HF {c u v S}(he:s(u,v)∈U C)(g:u=c)(hv:v∈S)(ht:TC C k.b v):PE c (k.lb c S) u v:=.inl ⟨g,k.PB.mpr ⟨g▸he,hv,ht⟩⟩
lemma Tb {P:Prop}[Decidable P]{f:P->St C}{u v:Q2}(g:P)(h:PJ (f g) u v):PJ (HN P f) u v:=by simpa[HN,g] using h
lemma HV {c1 L1 c2 L2}(u v:Q2):(PE c1 L1 u v\/PE c2 L2 u v)->(PE c1 L1 v u\/PE c2 L2 v u):=fun h=>h.elim (.inl ∘ PE.sym) (.inr ∘ PE.sym)
lemma H9 {c1 L1 c2 L2 c3 L3}(u v:Q2):(PE c1 L1 u v\/PE c2 L2 u v\/PE c3 L3 u v)->(PE c1 L1 v u\/PE c2 L2 v u\/PE c3 L3 v u):=
 fun h=>h.elim (.inl ∘ PE.sym) (.inr ∘ HV u v)
lemma Jj {c1 L1 c2 L2 c3 L3 c4 L4}(u v:Q2): (PE c1 L1 u v\/PE c2 L2 u v\/PE c3 L3 u v\/PE c4 L4 u v)->(PE c1 L1 v u\/PE c2 L2 v u\/PE c3 L3 v u\/PE c4 L4 v u):=
 fun h=>h.elim (.inl ∘ PE.sym) (.inr ∘ H9 u v)
lemma Rt {P:Q2->Q2->Prop}(hs:∀u v,P u v->P v u){u v:Q2}(he:s(u,v)∈U C)(h:∀x y,s(x,y)∈U C->(x∈k.W0\/(x∈k.JE/\TC C k.b x/\y∈k.Jy))->P x y):P u v:=
 (k.Hj he).elim (h u v he) fun g=>hs v u (h v u (PK he) g)
lemma Hm (d:F2){P:Q2->Q2->Prop}(hs:∀u v,P u v->P v u){u v:Q2}(he:s(u,v)∈U C)(g:u∉k.Ia)(hv:v∉k.Ia)(h:∀x y,s(x,y)∈U C->x∈k.A' d->y∈k.A' (1-d)->P x y):P u v:=
 (k.RV d he g hv).elim (fun ⟨h1,h2⟩=>h u v he h1 h2) fun ⟨h1,h2⟩=>hs v u (h v u (PK he) h1 h2)
lemma Hz {S T:Finset Q2}(h:∀x∈S,x∉T):(S∩T).card<=1:=by have:S∩T=∅:=Ee.mpr fun x g=>h x (i1 g) (i2 g);rw[this,card_empty];omega
def Hx (a b:St C):Prop:=
 (a.c≠b.c/\(a.good\/b.good))\/(a.W.biUnion (Oi C)∩b.L).card<=1\/(b.W.biUnion (Oi C)∩a.L).card<=1
def H3 (c:Q2)(L:Finset Q2)(W:Finset ℕ)(gd:Prop)(b:St C):Prop:=
 (c≠b.c/\(gd\/b.good))\/(W.biUnion (Oi C)∩b.L).card<=1\/(b.W.biUnion (Oi C)∩L).card<=1
lemma PZ {a:St C}:Hx a S0:=.inr (.inl (by simp[S0]))
lemma HH {c L W gd}:H3 c L W gd (S0:St C):=.inr (.inl (by simp[S0]))
lemma RA {P:Prop}[Decidable P]{f:P->St C}{a:St C}(h:∀g,Hx a (f g)):Hx a (HN P f):=by unfold HN;split_ifs with g;exact h g;exact PZ
lemma MK {P:Prop}[Decidable P]{f:P->St C}{c L W gd}(h:∀g,H3 c L W gd (f g)):H3 c L W gd (HN P f):=by unfold HN;split_ifs with g;exact h g;exact HH
lemma HC {d1 d2 c1 c2 S1 S2 h1 h2}(h:∀x∈k.A d1,x∉S2):Hx (k.PF d1 c1 S1 h1) (k.PF d2 c2 S2 h2):=
 .inr (.inl (by simp only[PF,Kf,V9,Sbu];exact Hz fun x g hL=>h x g (i2 hL)))
lemma Hf {c L W gd d c1 S1 h1}(h:∀x∈k.A d,x∉L):H3 c L W gd (k.PF d c1 S1 h1):=
 .inr (.inr (by simp only[PF,Kf,Sbu];exact Hz h))
lemma JA {c L gd d c1 S1 h1}(hS:S1⊆k.Jy):H3 c L (W0For G11 C k.b) gd (k.PF d c1 S1 h1):=
 .inr (.inl (Hz fun x j hL=>by have⟨z,h,g⟩:=Bup j;exact s2 (hS (i2 hL)) (Qc k.hL.1 k.b z h g)))
lemma Hs {d c gd c1 S1 h1}:H3 c (k.lb c (k.AW (1-d))) (W0For G11 C k.b) gd (k.PF d c1 S1 h1):=
 k.Hf fun _ g hL=>d2 (k.PB.mp hL).2.1 (H4 g)
lemma JC {d c gd c1 S1 h1}:H3 c (k.lb c (k.AW d)) (W0For G11 C k.b) gd (k.PF (1-d) c1 S1 h1):=
 k.Hf fun _ g hL=>d2 (k.PB.mp hL).2.1 g
lemma HR (j:ℕ):(W0For G11 C j).card<=(centreless G11 C).card:=(Qj j).trans (Qs j)
lemma RU (h:Ao C)(j:ℕ):(W0For G11 C j).biUnion (Oi C)⊆Mw C j:=fun _ t=>by have⟨z,q,g⟩:=Bup t;exact Qc h j z q g
lemma R2 {w:Q2}(h:TC C k.a w\/TC C k.b w):ME C (W0For G11 C k.a∪W0For G11 C k.b) (mixing G11 C) w:=by
 rcases h with (h0|⟨t,ht,d,m,g,hr,hw⟩)|(h0|⟨t,ht,d,m,g,hr,hw⟩)
 ·exact .inl (Bub _ Sul h0)
 ·exact .inr ⟨t,ht,d,m,(Fp g).1,hr,hw⟩
 ·exact .inl (Bub _ Sur h0)
 ·exact .inr ⟨t,ht,d,m,(Fp g).1,hr,hw⟩
lemma Rz:∀z∈W0For G11 C k.a∪W0For G11 C k.b,z < 11+C.gates.length:=fun z g=>
 (Up g).elim (Qg k.hL.1 k.a z) (Qg k.hL.1 k.b z)
lemma R6:(W0For G11 C k.a∪W0For G11 C k.b).card<=2*(centreless G11 C).card:=by have h1:=Cu (W0For G11 C k.a) (W0For G11 C k.b);have h2:=HR (C:=C) k.a;have h3:=HR (C:=C) k.b;omega
noncomputable def Rf (P:Prop)[Decidable P]:Finset ℕ:=W0For G11 C k.a∪if P then {opnd C k.b (1-k.db)} else ∅
lemma MS {P:Prop}[Decidable P]:∀z∈k.Rf P,z < 11+C.gates.length:=fun z g=>by
 rcases Up g with h|h;exact Qg k.hL.1 k.a z h
 split_ifs at h;rw[Sp h];exact Qe k.hL.1 k.hb (1-k.db);exact(N0 h).elim
lemma Rh {P:Prop}[Decidable P]:(k.Rf P).card<=(W0For G11 C k.a).card+if P then 1 else 0:=by
 have h1:(k.Rf P).card<=(W0For G11 C k.a).card+(if P then ({opnd C k.b (1-k.db)}:Finset ℕ) else ∅).card:=Cu _ _;have h2:(if P then ({opnd C k.b (1-k.db)}:Finset ℕ) else ∅).card=if P then 1 else 0:=by split_ifs<;>simp
 omega
open Classical in
noncomputable def Rj (C:Ck)(c:Q2)(L:Finset Q2):Finset (Sym2 Q2):=U C\L.image fun x=>s(c,x)
lemma Rn {c:Q2}{L:Finset Q2}{u v:Q2}(h:s(u,v)∈Rj C c L):s(u,v)∈U C/\∀x∈L,s(u,v)≠s(c,x):=by
 classical have⟨j,g⟩:=Dp h;exact⟨j,fun x q e=>g (Mi ⟨x,q,e.symm⟩)⟩
lemma Rk {c:Q2}{L:Finset Q2}(j:L.card<=1):(U C).card<=(Rj C c L).card+1:=by
 classical
 set E1:=L.image fun x=>s(c,x);have g:U C⊆Rj C c L∪E1:=fun e he=>by by_cases h:e∈E1<;>[exact Ur _ h;exact Ul _ (Dm he h)]
 have:=(Cl g).trans ((Cu _ _).trans (A2l (Ci.trans j) _));omega
lemma MW (a6:Ao C){E:Finset (Sym2 Q2)}(s0 s1 s2 s3:St C)(a3:∀u v,s(u,v)∈E->PJ s0 u v\/PJ s1 u v\/PJ s2 u v\/PJ s3 u v)(ac:Hx s0 s1)(ab:Hx s0 s2)(ae:Hx s0 s3)(a9:Hx s1 s2)(ad:Hx s1 s3)(aa:Hx s2 s3): E.card<=(rFull G11 C).card+s0.W.card+s1.W.card+s2.W.card+s3.W.card:=by
 classical
 let f:Fin 4->St C:=![s0,s1,s2,s3]
 choose P hPs hPc hPsp using fun i:Fin 4=>Ky a6 Q3 (f i).hW (f i).hL (f i).he
 have q:Set.PairwiseDisjoint (univ:Finset (Fin 4)) P:=by
  have z (i j:Fin 4) (hij:i < j):Disjoint (P i) (P j):=by
   have hp:Hx (f i) (f j):=by fin_cases i<;>fin_cases j<;>simp_all [f]
   rcases hp with⟨Pt,hg|hg⟩|g|g
   ·exact Kw Q3 Pt (hPsp i) (hPsp j) ((f i).hgood hg) fun y hy=>Qh ((f j).he y hy)
   ·exact(Kw Q3 Pt.symm (hPsp j) (hPsp i) ((f j).hgood hg) fun y hy=>Qh ((f i).he y hy)).symm
   ·exact KE (hPsp i) (hPsp j) (.inl g)
   ·exact KE (hPsp i) (hPsp j) (.inr g)
  intro i _ j _ Pt;rcases lt_or_gt_of_ne Pt with h|h;exact z i j h;exact(z j i h).symm
 have t:E⊆univ.biUnion fun i:Fin 4=>(f i).L.image fun x=>s((f i).c,x):=fun e he=>by
  induction e using Sym2.ind with| _ u v=>
  have Px (i:Fin 4) (h:PJ (f i) u v):s(u,v)∈univ.biUnion fun j:Fin 4=>(f j).L.image fun x=>s((f j).c,x):=
   Mbu ⟨i,Uv _,Mi (h.elim (fun ⟨rfl,hv⟩=>⟨v,hv,rfl⟩) fun ⟨rfl,hu⟩=>⟨u,hu,Sw⟩)⟩
  rcases a3 u v he with h|h|h|h;exact Px 0 h;exact Px 1 h;exact Px 2 h;exact Px 3 h
 have hE:E.card<=∑i:Fin 4,(f i).L.card:=(Cl t).trans (Cbu.trans (Sls fun _ _=>Ci));have hP:∑i:Fin 4,(P i).card<=(rFull G11 C).card:=by rw[←card_biUnion q];exact Cl (biUnion_subset.mpr fun i _=>hPs i)
 have a7:∑i:Fin 4,(f i).L.card<=(∑i:Fin 4,(P i).card)+∑i:Fin 4,(f i).W.card:=by rw[←sum_add_distrib];exact Sls fun i _=>hPc i
 have hW:∑i:Fin 4,(f i).W.card=s0.W.card+s1.W.card+s2.W.card+s3.W.card:=by simp[Fin.sum_univ_four,f,add_assoc]
 omega
lemma MV (j:Ao C){E:Finset (Sym2 Q2)}(s0 s1:St C)(g:∀u v,s(u,v)∈E->PJ s0 u v\/PJ s1 u v)(h:Hx s0 s1): E.card<=(rFull G11 C).card+s0.W.card+s1.W.card:=by
 have:=MW j s0 s1 S0 S0 (fun u v he=>(g u v he).elim .inl (.inr ∘ .inl)) h PZ PZ PZ PZ PZ
 simp only[S0,card_empty] at this;omega
lemma MH (aa:Ao C){E:Finset (Sym2 Q2)}{c:Q2}{L:Finset Q2}{W Mc:Finset ℕ}(af:Mc⊆mixing G11 C)(a4:∀z∈W,z < 11+C.gates.length)(gd:Prop)(ae:gd->∀z∈W,∀x∈Oi C z,Ga c x)(t:∀w∈L,s(c,w)∈U C)(a9:∀w∈L,ME C W Mc w): ∃(it:St C) (M:Finset ℕ) (E':Finset (Sym2 Q2)), M⊆Mc/\it.c=c/\it.L⊆L/\it.W=W/\it.good=gd/\E.card<=E'.card+M.card/\E'⊆E /\ (∀u v,s(u,v)∈E'->PE c L u v->PJ it u v)/\(∀s,H3 c L W gd s->Hx it s) /\ ∃j:ℕ->Q2,Th C L M j/\∀m1∈M,∀m2∈M,m1≠m2->j m1≠j m2:=by
 classical
 have⟨L0,Lm,M,ac,a8,g,a5,ak,j,ah,a6⟩:=QU aa af t a9;set q:=Lm.image fun w=>s(c,w);set E':=E\q
 have ab:E.card<=E'.card+M.card:=by
  have h1:=Cl (show E⊆E'∪q from fun e he=>by by_cases h:e∈q<;>[exact Ur _ h;exact Ul _ (Dm he h)])
  have h2:=(Cu E' q).trans (A2l Ci E'.card);omega
 let it:St C:=⟨c,L0,W,a4,a5,fun _ hx=>t _ (g hx),gd,ae⟩
 refine⟨it,M,E',ac,rfl,g,rfl,rfl,ab,Ds,fun u v ag hh=>?_,
  fun s hp=>hp.elim .inl fun h=>h.elim (.inr ∘ .inl) fun h=>.inr (.inr ((Cl (inter_subset_inter_left g)).trans h)),j,ah,a6⟩
 have ad:=(D2 ag)
 have a3 {x y:Q2} (hx:x=c) (hy:y∈L) (hn:s(x,y)∉q):y∈L0:=by rw[a8] at hy;exact(Up hy).elim id fun hm=>(hn (Mi ⟨y,hm,by rw[hx]⟩)).elim
 rcases hh with⟨rfl,hv⟩|⟨rfl,hu⟩;exact .inl ⟨rfl,a3 rfl hv ad⟩;exact .inr ⟨rfl,a3 rfl hu (by rwa[Sw])⟩
lemma HB (q:Ao C){E:Finset (Sym2 Q2)}{c:Q2}{L:Finset Q2}{W Mc:Finset ℕ}(ag:Mc⊆mixing G11 C)(a4:∀z∈W,z < 11+C.gates.length)(gd:Prop)(ae:gd->∀z∈W,∀x∈Oi C z,Ga c x)(ac:∀w∈L,s(c,w)∈U C)(a9:∀w∈L,ME C W Mc w)(s1 s2:St C)(a7:∀u v,s(u,v)∈E->PE c L u v\/PJ s1 u v\/PJ s2 u v)(ab:H3 c L W gd s1)(af:H3 c L W gd s2)(aa:Hx s1 s2): ∃M⊆Mc,E.card<=(rFull G11 C).card+W.card+s1.W.card+s2.W.card+M.card /\ ∃j:ℕ->Q2,Th C L M j/\∀m1∈M,∀m2∈M,m1≠m2->j m1≠j m2:=by
 obtain⟨it,M,E',ad,_,_,hW,_,ak,a8,a5,g,j,ah,a6⟩:=MH q ag a4 gd ae ac a9
 have t:=MW q it s1 s2 S0 (fun u v a3=>(a7 u v (a8 a3)).elim (fun h=>.inl (a5 u v a3 h)) fun h=>h.elim (.inr ∘ .inl) (.inr ∘ .inr ∘ .inl))
  (g s1 ab) (g s2 af) PZ aa PZ PZ
 rw[hW] at t;simp only[S0,card_empty] at t;exact⟨M,ad,by omega,j,ah,a6⟩
lemma MC (a3:Ao C){c1 c2:Q2}{L1 L2:Finset Q2}{W1 W2 M1c M2c:Finset ℕ}(ap:M1c⊆mixing G11 C)(am:M2c⊆mixing G11 C)(aa:∀z∈W1,z < 11+C.gates.length)(a7:∀z∈W2,z < 11+C.gates.length)(q g2:Prop)(b5:q->∀z∈W1,∀x∈Oi C z,Ga c1 x)(b3:g2->∀z∈W2,∀x∈Oi C z,Ga c2 x)(ag:∀w∈L1,s(c1,w)∈U C)(ak:∀w∈L2,s(c2,w)∈U C)(ad:∀w∈L1,ME C W1 M1c w)(an:∀w∈L2,ME C W2 M2c w)(s1 s2:St C)(ar:∀u v,s(u,v)∈U C->PE c1 L1 u v\/PE c2 L2 u v\/PJ s1 u v\/PJ s2 u v)(hp12:(c1≠c2/\(q\/g2))\/(W1.biUnion (Oi C)∩L2).card<=1\/(W2.biUnion (Oi C)∩L1).card<=1)(av:H3 c1 L1 W1 q s1)(ah:H3 c1 L1 W1 q s2)(af:H3 c2 L2 W2 g2 s1)(aq:H3 c2 L2 W2 g2 s2)(ay:Hx s1 s2): ∃M1⊆M1c,∃M2⊆M2c,(U C).card<=(rFull G11 C).card+W1.card+W2.card+s1.W.card+s2.W.card+M1.card+M2.card /\ ∃a6:ℕ->Q2,Th C L2 M2 a6:=by
 obtain⟨a5,M2,E1,al,az,aj,ab,ae,b7,ac,a8,j,a6,au,_⟩:=MH a3 am a7 g2 b3 ak an;obtain⟨b4,M1,E2,aw,_,_,ax,_,b8,t,a9,g,_⟩:=MH a3 (E:=E1) ap aa q b5 ag ad
 have hp12':H3 c1 L1 W1 q a5:=by unfold H3;rw[az,ab,ae];exact hp12.elim .inl fun h=>h.elim (fun h=>.inr (.inl ((Cl (inter_subset_inter_left aj)).trans h))) (.inr ∘ .inr)
 have b6:=MW a3 b4 a5 s1 s2
  (fun u v he=>(ar u v (ac (t he))).elim (fun h=>.inl (a9 u v he h))
   fun h=>h.elim (fun h=>.inr (.inl (a8 u v (t he) h))) (.inr ∘ .inr))
  (g a5 hp12') (g s1 av) (g s2 ah) (j s1 af) (j s2 aq) ay
 rw[ax,ab] at b6;exact⟨M1,aw,M2,al,by omega,a6,au⟩
lemma M7 {E:Finset (Sym2 Q2)}{bonus:ℕ}(hE:(U C).card<=E.card+bonus){c:Q2}{L:Finset Q2}(gd:Prop)(a3:gd->∀z∈W0For G11 C k.b,∀x∈Oi C z,Ga c x)(h:∀w∈L,s(c,w)∈U C)(j:∀w∈L,TC C k.b w)(s1 s2:St C)(a5:s1.W.card+s2.W.card+bonus<=2)(g:∀u v,s(u,v)∈E->PE c L u v\/PJ s1 u v\/PJ s2 u v)(t:H3 c L (W0For G11 C k.b) gd s1)(a4:H3 c L (W0For G11 C k.b) gd s2)(q:Hx s1 s2):PV C:=by obtain⟨M,hM,a6,_⟩:=HB k.hL.1 (E:=E) (Fs _ _) (Qg k.hL.1 k.b) gd a3 h j s1 s2 g t a4 q;have h1:=HR (C:=C) k.b;have h2:=Cl (hM.trans (Fs _ _));omega
lemma HM {E:Finset (Sym2 Q2)}{bonus:ℕ}(hE:(U C).card<=E.card+bonus){c:Q2}{S:Finset Q2}(gd:Prop)(a3:gd->∀z∈W0For G11 C k.b,∀x∈Oi C z,Ga c x)(s1 s2:St C)(j:s1.W.card+s2.W.card+bonus<=2)(g:∀u v,s(u,v)∈E->PE c (k.lb c S) u v\/PJ s1 u v\/PJ s2 u v)(t:H3 c (k.lb c S) (W0For G11 C k.b) gd s1)(a4:H3 c (k.lb c S) (W0For G11 C k.b) gd s2)(q:Hx s1 s2):PV C:=
 k.M7 hE gd a3 (fun _ h=>(k.PB.mp h).1) (fun _ h=>(k.PB.mp h).2.2) s1 s2 j g t a4 q
lemma HJ (d:F2)(c0 c1:Q2)(q:∀u v,s(u,v)∈U C->PE c0 (k.A (1-d)) u v\/PE c1 (k.A' d) u v):PV C:=by
 let g:=k.Hc (1-d) c0;let j:=k.JB d c1
 have t:=MV k.hL.1 (E:=U C) g j (fun u v he=>
  (q u v he).elim (fun h=>.inl (h.elim (fun ⟨hu,hv⟩=>k.PS he hu hv) fun ⟨hv,hu⟩=>(k.PS (PK he) hv hu).sym))
   fun h=>.inr (h.elim (fun ⟨hu,hv⟩=>k.PS he hu hv) fun ⟨hv,hu⟩=>(k.PS (PK he) hv hu).sym))
  (k.HC fun _ z h=>s2 h z)
 simp only[g,j,PF,Kf,Cs] at t;omega
lemma MT (a9:∀d,2<=(k.A d).card): (∃c0∈k.A' 0,∃c1∈k.A' 1,(∀z∈k.A0 0,z=c0)/\(∀z∈k.A0 1,z=c1) /\ (∀u w,s(u,w)∈U C->u∈k.A' 0->w∈k.A' 1->u=c0\/w=c1))\/ (∃d:F2,k.A0 0=∅/\k.A0 1=∅/\(k.AB (1-d)).card<=1/\(k.AW (1-d)).card<=1)\/ (∃d:F2,k.A0 d=∅/\(k.A0 (1-d)).Nonempty):=by
 have a4 (d:F2) {S:Finset Q2} (hS:S⊆k.A' d) (hc:S.card<=1):∃c∈k.A' d,∀x∈S,x=c:=by
  rcases Eo S with rfl|⟨c,aa⟩
  ·have⟨c,af⟩:=k.Mj d;exact⟨c,af,fun _ h=>(N0 h).elim⟩
  ·exact⟨c,hS aa,fun x hx=>uq hc hx aa⟩
 rcases Eo (k.A0 0) with t|⟨c0,j⟩
 ·rcases Eo (k.A0 1) with q|⟨c1,g⟩
  ·have hW' (d:F2) (h:(k.Mp d).card<=1):(k.AW d).card<=1:=(Cl fun _ hx=>Hp hx).trans h
   rcases k.Mr 0 with a8|a5<;>rcases k.Mr 1 with a6|a7
   ·have⟨c0,j,h0⟩:=a4 0 Il (hW' 0 a8);have⟨c1,g,h1⟩:=a4 1 Il (hW' 1 a6)
    refine .inl ⟨c0,j,c1,g,fun _ h=>(Hh t h).elim,fun _ h=>(Hh q h).elim,fun u w he hu hw=>?_⟩
    rcases k.Hj he with (h|⟨hW,_,_⟩)|(h|⟨hW,_,_⟩)
    ·exact(Hu t hu h).elim
    ·exact .inl (h0 u (Py hu hW))
    ·exact(Hu q hw h).elim
    ·exact .inr (h1 w (Py hw hW))
   ·exact .inr (.inl ⟨1,t,q,a7,hW' 0 a8⟩)
   ·exact .inr (.inl ⟨0,t,q,a5,hW' 1 a6⟩)
   ·have⟨c0,j,h0⟩:=a4 0 Il a7;have⟨c1,g,h1⟩:=a4 1 Il a5
    refine .inl ⟨c0,j,c1,g,fun _ h=>(Hh t h).elim,fun _ h=>(Hh q h).elim,fun u w he hu hw=>?_⟩
    rcases k.Hj he with (h|⟨_,_,hB⟩)|(h|⟨_,_,hB⟩)
    ·exact(Hu t hu h).elim
    ·exact .inr (h1 w (Py hw hB))
    ·exact(Hu q hw h).elim
    ·exact .inl (h0 u (Py hu hB))
  ·exact .inr (.inr ⟨0,t,c1,g⟩)
 ·rcases Eo (k.A0 1) with q|⟨c1,g⟩
  ·exact .inr (.inr ⟨1,q,c0,j⟩)
  ·exact .inl ⟨c0,i1 j,c1,i1 g,fun z hz=>uq (k.RK 0 (a9 1)) hz j,fun z hz=>uq (k.RK 1 (a9 0)) hz g,
    fun u w he hu hw=>Vh Q3 (d1 j) (d1 g) (k.Hb 0 (d1 j) (i2 j)) (k.Hb 1 (d1 g) (i2 g)) (s1 hu) (s1 hw) (Qh he)⟩
lemma TX (ap:k.Ia=∅):PV C:=by
 classical
 have t (x:Q2):x∉k.Ia:=Hh ap
 have af (d:F2) (h1:(k.A d).card<=1):PV C:=by have⟨c,hc⟩:=H1 h1;exact k.HJ d c 0 fun u v he=>k.Hm d HV he (t u) (t v) fun x y _ g q=>.inl (.inl ⟨hc x (s1 g),s1 q⟩)
 by_cases an:(k.A 0).card<=1;· exact af 0 an
 by_cases am:(k.A 1).card<=1;· exact af 1 am
 have ag (d:F2):2<=(k.A d).card:=by fin_cases d<;>simp<;>omega
 rcases k.MT ag with⟨c0,_,c1,_,_,_,h2⟩|⟨d,aa,aw,aj,a8⟩|⟨d,aa,⟨c1,a6⟩⟩
 ·exact k.HJ 0 c0 c1 fun u v he=>k.Hm 0 HV he (t u) (t v)
   fun x y j g q=>(h2 x y j g q).elim (fun h=>.inl (.inl ⟨h,s1 q⟩)) fun h=>.inr (.inr ⟨h,g⟩)
 ·have⟨y1,ah⟩:=H1 aj;have⟨c1,a6⟩:=H1 a8
  have ak:k.A0 d=∅:=by fin_cases d<;>assumption
  have aq:k.A0 (1-d)=∅:=by fin_cases d<;>assumption
  let ac:=k.MX d c1
  exact k.HM (bonus:=0) (by omega) False False.elim ac S0 (by simp[ac,PF,S0])
   (fun u v he=>k.Hm d H9 he (t u) (t v) fun x y j g q=>by
    rcases k.Hj j with (h|⟨a4,ht,a3⟩)|(h|⟨a5,_,a9⟩)
    ·exact(Hu ak g h).elim
    ·exact .inl (k.HF (PK j) (ah y (Py q a3)) (Py g a4) ht).sym
    ·exact(Hu aq q h).elim
    ·exact .inr (.inl (k.PS (PK j) (a6 y (Py q a5)) (Py g a9)).sym))
   (k.JA Ir) HH PZ
 ·have a7:∀z∈k.A0 (1-d),z=c1:=fun z hz=>uq (k.RK (1-d) (by rw[Qd];exact ag d)) hz a6
  have⟨x0,ae⟩:=k.RS a6
  by_cases ax:2<=(k.AB d).card
  ·have a8:(k.Mp (1-d)).card<=1:=(k.Mr (1-d)).resolve_right (by rw[Qd];omega)
   exact k.HJ d x0 c1 fun u v he=>k.Hm d HV he (t u) (t v) fun x y j g q=>by
    rcases k.Hj j with (h|⟨a4,_,a3⟩)|(h|⟨a5,_,_⟩)
    ·exact(Hu aa g h).elim
    ·exact .inl (.inl ⟨ae ⟨y,Py q a3⟩ x (Py g a4),s1 q⟩)
    ·exact .inr (.inr ⟨a7 y (Py q h),g⟩)
    ·exact(k.Ha a8 a6 (Py q a5)).elim
  ·have⟨x1,al⟩:=H1 (s:=k.AB d) (by omega)
   let ad:=k.Hc d c1;let ab:=k.MX (1-d) x0
   exact k.HM (bonus:=0) (by omega) False False.elim ad ab (by simp[ad,ab,PF])
    (fun u v he=>k.Hm d H9 he (t u) (t v) fun x y j g q=>by
     rcases k.Hj j with (h|⟨a4,_,a3⟩)|(h|⟨a5,ht,a9⟩)
     ·exact(Hu aa g h).elim
     ·exact .inr (.inr (k.PS j (ae ⟨y,Py q a3⟩ x (Py g a4)) (Py q a3)))
     ·exact .inr (.inl (k.PS (PK j) (a7 y (Py q h)) (s1 g)).sym)
     ·exact .inl (k.HF j (al x (Py g a9)) (Py q a5) ht))
    k.Hs (k.JA Ir) (k.HC fun _ g hL=>d2 hL (H4 g))
lemma Rp {v:Q2} (ae:k.Ia={v}) {d:F2} (bd:k.A0 0=∅) (b9:k.A0 1=∅) (ar:(k.AB (1-d)).card<=1) (ap:(k.AW (1-d)).card<=1) {Lv:Finset Q2} {Wv:Finset ℕ} (b6:Wv.card<=(W0For G11 C k.a).card+1) (a6:∀z∈Wv,z < 11+C.gates.length) (j:Prop) (al:j->∀z∈Wv,∀x∈Oi C z,Ga v x) (g:∀w,s(v,w)∈U C->w∈Lv) (a7:∀w∈Lv,s(v,w)∈U C) (aa:∀w∈Lv,ME C Wv ((mixing G11 C).filter fun m=>O C (11+m) k.a) w)
  (a8:∀q:Q2,q≠v->(v≠q/\j)\/(Wv.biUnion (Oi C)∩k.lb q (k.AW d)).card<=1)
  (a9:∀c1:Q2,c1≠v->H3 v Lv Wv j (k.MX d c1)):PV C:=by
 have aq:v∈k.Ia:=ae▸Ss v;have ab {x} (hx:x≠v):x∉k.Ia:=fun h=>hx (Sp (ae▸h));have au:k.A0 d=∅:=by fin_cases d<;>assumption
 have b3:k.A0 (1-d)=∅:=by fin_cases d<;>assumption
 have ac:v∉k.A' (1-d):=fun h=>s2 h (H4 ((k.PA d).mp aq).1);have⟨q,am,an⟩:=Kq ar Il (k.Mj (1-d)) ac;have⟨c1,ak,az⟩:=Kq ap Il (k.Mj (1-d)) ac;let ad:=k.MX d c1
 obtain⟨Mv,hMv,M3,hM3,b4,ba,ag⟩:=MC k.hL.1 (L2:=k.lb q (k.AW d)) (Fs _ _) (Fs _ _)
  a6 (Qg k.hL.1 k.b) j False al False.elim
  a7 (fun _ h=>(k.PB.mp h).1) aa (fun _ h=>(k.PB.mp h).2.2) ad S0
  (fun u w he=>by
   by_cases a3:u=v;· exact .inl (.inl ⟨a3,g w (a3▸he)⟩)
   by_cases t:w=v;· exact .inl (.inr ⟨t,g u (t▸PK he)⟩)
   exact .inr (k.Hm d H9 he (ab a3) (ab t) fun x y a4 hx hy=>by
    rcases k.Hj a4 with (h|⟨av,ht,ay⟩)|(h|⟨ax,_,aw⟩)
    ·exact(Hu au hx h).elim
    ·exact .inl (k.HF (PK a4) (an y (Py hy ay)) (Py hx av) ht).sym
    ·exact(Hu b3 hy h).elim
    ·exact .inr (.inl (k.PS (PK a4) (az y (Py hy ax)) (Py hx aw)).sym)))
  ((a8 q am).elim (fun ⟨h1,h2⟩=>.inl ⟨h1,.inl h2⟩) (.inr ∘ .inl))
  (a9 c1 ak) HH (k.JA Ir) HH PZ
 have ah:=Yf k.hL.1 (fun m hm=>(Fp (hMv hm)).2) ag fun u hu af=>r2 (k.PB.mp hu).2.1 (Ul _ af);have b5:=Yq (hMv.trans (Fs _ _)) (hM3.trans (Fs _ _)) ah;have af:=HR (C:=C) k.a;have bb:=HR (C:=C) k.b;simp only[ad,PF,Kf,Cs,S0,card_empty] at b4;omega
lemma RP {v:Q2}(aa:k.Ia={v})(am:v∈k.B1):PV C:=by
 classical
 have a5:v∈k.Ia:=aa▸Ss v;have ad {x} (g:x≠v):x∉k.Ia:=fun h=>g (Sp (aa▸h));have⟨hA02,hA12,_,_⟩:=YJ k.hL k.hT k.hs k.hab aa;have ap (d:F2):2<=(k.A d).card:=by fin_cases d<;>assumption
 have⟨q,j⟩:=k.M9 a5 am
 have ac (d:F2):∃c:Q2,c≠v/\∀u∈k.A' d,∀y∈k.A' (1-d),(u∈k.W0\/(u∈k.JE/\y∈k.Jy))->u=c:=by
  have ae:v∉k.A' d:=fun h=>s2 h ((k.PA d).mp a5).2
  by_cases Pt:(k.AB (1-d)).Nonempty
  ·have⟨y0,a6⟩:=Pt
   have⟨c,a9,hc⟩:=Kq (MA (A:=k.Mp d) (x:=v) (y:=y0) (fun e=>d2 a6 (H4 (e▸((k.PA d).mp a5).1)))
    (fun u hu=>j u (i2 hu)) fun u hu=>(k.HA d (d1 hu) (i2 hu) (d1 a6) (r1 a6)).symm) Il (k.Mj d) ae
   exact⟨c,a9,fun u hu _ _ h=>hc u (Py hu (h.elim (fun h=>k.Hv h) fun h=>s1 h.1))⟩
  ·have⟨c,a9,hc⟩:=Kq (k.RK d (ap (1-d))) Il (k.Mj d) ae;exact⟨c,a9,fun u hu y t h=>h.elim (fun h0=>hc u (Py hu h0)) fun h2=>(Pt ⟨y,Py t h2.2⟩).elim⟩
 have⟨c0,hc0v,aj⟩:=ac 0;have⟨c1,hc1v,ag⟩:=ac 1;let ah:=k.JB 1 c0;let af:=k.JB 0 c1
 obtain⟨M,hM,an,_⟩:=HB k.hL.1 (E:=U C) (L:=sl C v) Subset.rfl k.Rz True
  (fun _ z hz x g=>j x ((Up hz).elim (fun h=>k.Mk (Qc k.hL.1 k.a z h g)) (Qc k.hL.1 k.b z · g)))
  (fun _ hw=>Hr hw) (fun w hw=>k.R2 (by
   rcases k.ec (Hr hw) with (h1|h2)|⟨_,h1|h2⟩
   ·exact(q (k.Mk (Q5 k.hL.1 h1))).elim
   ·exact .inl h2
   ·exact(q (Q5 k.hL.1 h1)).elim
   ·exact .inr h2)) ah af
  (fun u w he=>by
   by_cases a8:u=v;· exact .inl (.inl ⟨a8,Mn (a8▸he)⟩)
   by_cases a7:w=v;· exact .inl (.inr ⟨a7,Mn (a7▸PK he)⟩)
   exact .inr (k.Hm 0 HV he (ad a8) (ad a7) fun x y a3 g t=>by
    rcases k.Hj a3 with (h|⟨hW,_,hB⟩)|(h|⟨hW,_,hB⟩)
    ·exact .inl (k.PS a3 (aj x g y t (.inl h)) t)
    ·exact .inl (k.PS a3 (aj x g y t (.inr ⟨hW,hB⟩)) t)
    ·exact .inr (k.PS (PK a3) (ag y t x g (.inl h)) g).sym
    ·exact .inr (k.PS (PK a3) (ag y t x g (.inr ⟨hW,hB⟩)) g).sym))
  (.inl ⟨hc0v.symm,.inl trivial⟩) (.inl ⟨hc1v.symm,.inl trivial⟩) (k.HC fun _ g h=>s2 h g)
 have h1:=k.R6;have h2:=Cl hM;simp only[ah,af,PF,Kf,Cs] at an;omega
lemma RN {v:Q2}(a9:k.Ia={v})(a6:v∉k.B1)(ax:v∈k.Wb):PV C:=by
 classical
 have j:v∈k.Ia:=a9▸Ss v;have aq {x} (q:x≠v):x∉k.Ia:=fun h=>q (Sp (a9▸h));have⟨hA02,hA12,_,_⟩:=YJ k.hL k.hT k.hs k.hab a9;have ap (d:F2):2<=(k.A d).card:=by fin_cases d<;>assumption
 have⟨ac,ab⟩:=Q1 k.hL.1 k.ha (i1 j) (i2 j);have a4:=k.HP j ax;let Lvb:=(sl C v).filter fun w=>¬TC C k.a w
 have am:∀w∈Lvb,w∈k.B1/\((T0For G11 C k.b).Nonempty\/∃mb∈mixing G11 C,O C (11+mb) k.b):=fun w hw=>by
  rcases k.ec (Hr (Fp hw).1) with (h1|h2)|⟨hB,h1|h2⟩
  ·exact(ac (Q5 k.hL.1 h1)).elim
  ·exact((Fp hw).2 h2).elim
  ·exact⟨hB.resolve_left a6,Kt h1⟩
  ·exact⟨hB.resolve_left a6,Kt h2⟩
 have t:∀z∈k.Rf Lvb.Nonempty,∀x∈Oi C z,Ga v x:=fun z hz x q=>by
  rcases Up hz with h|h;exact ab x (Qc k.hL.1 k.a z h q)
  split_ifs at h;rw[Sp h] at q;exact a4 x q;exact(N0 h).elim
 have aa:∀w∈sl C v,ME C (k.Rf Lvb.Nonempty) ((mixing G11 C).filter fun m=>O C (11+m) k.a) w:=fun w hw=>by
  by_cases hA:TC C k.a w
  ·exact hA.elim (fun h0=>.inl (Bub _ Sul h0)) .inr
  ·have a3:w∈Lvb:=Fk hw hA;have Pt:Lvb.Nonempty:=⟨w,a3⟩;exact .inl (Mbu ⟨opnd C k.b (1-k.db),Ur _ (by simp[Pt]),(am w a3).1⟩)
 have au (d:F2) (c0 c1:Q2) (hc0v:c0≠v) (hc1v:c1≠v)
   (h2:∀u w,s(u,w)∈U C->u∈k.A' d->w∈k.A' (1-d)->u=c0\/w=c1):PV C:=by
  let av:=k.JB (1-d) c0;let ar:=k.JB d c1
  have⟨M,hM,b6,fw,b7,ay⟩:=HB k.hL.1 (E:=U C) (Fs _ _) k.MS True (fun _=>t)
   (fun _ hw=>Hr hw) aa av ar
   (fun u w he=>by
    by_cases af:u=v;· exact .inl (.inl ⟨af,Mn (af▸he)⟩)
    by_cases ae:w=v;· exact .inl (.inr ⟨ae,Mn (ae▸PK he)⟩)
    exact .inr (k.Hm d HV he (aq af) (aq ae)
     fun x y ah q hy=>(h2 x y ah q hy).elim (fun h=>.inl (k.PS ah h hy)) fun h=>.inr (k.PS (PK ah) h q).sym))
   (.inl ⟨hc0v.symm,.inl trivial⟩) (.inl ⟨hc1v.symm,.inl trivial⟩) (k.HC fun _ q h=>s2 h q)
  have be:=k.Rh (P:=Lvb.Nonempty)
  have bf:(W0For G11 C k.a).card+M.card+(if Lvb.Nonempty then 1 else 0) <=
    2*(centreless G11 C).card+(mixing G11 C).card+(rZero G11 C).card:=by
   split_ifs with Pt
   ·have⟨w0,hw0⟩:=Pt
    exact KG k.hL.1 Q3 k.ha k.hb k.TB (hM.trans (Fs _ _))
     (fun m hm=>(Fp (hM hm)).2) (fun _ hw=>Hr hw) b7 ay (am w0 hw0).2
   ·have h1:=HR (C:=C) k.a;have h2:=Cl (hM.trans (Fs _ _));omega
  simp only[av,ar,PF,Kf,Cs] at b6;omega
 rcases k.MT ap with⟨c0,b9,c1,g,_,_,h2⟩|⟨d,al,az,b4,ad⟩|⟨d,al,⟨c1,g⟩⟩
 ·exact au 0 c0 c1 (fun e=>s2 b9 (e▸i2 j)) (fun e=>s2 g (e▸i1 j)) h2
 ·exact k.Rp a9 al az b4 ad (by have:=k.Rh (P:=Lvb.Nonempty);split_ifs at this<;>omega) k.MS True (fun _=>t)
   (fun _=>Mn) (fun _=>Hr) aa (fun _ hy=>.inl ⟨hy.symm,trivial⟩) fun _ hc=>.inl ⟨hc.symm,.inl trivial⟩
 ·have ak:∀z∈k.A0 (1-d),z=c1:=fun z hz=>uq (k.RK (1-d) (by rw[Qd];exact ap d)) hz g
  have ag:v∉k.A' d:=fun h=>s2 h ((k.PA d).mp j).2
  obtain⟨x1,a7,aj⟩:∃x1:Q2,x1≠v/\∀u∈k.AB d,∀w∈k.AW (1-d),u=x1:=by
   by_cases h2:2<=(k.AB d).card
   ·have⟨d0,b5⟩:=k.Mj d;have ad:(k.Mp (1-d)).card<=1:=(k.Mr (1-d)).resolve_right (by rw[Qd];omega)
    exact⟨d0,fun e=>ag (e▸b5),fun _ _ w hw=>(k.Ha ad g hw).elim⟩
   ·have⟨x1,a7,aj⟩:=Kq (s:=k.AB d) (by omega) Il (k.Mj d) ag
    exact⟨x1,a7,fun u hu _ _=>aj u hu⟩
  refine au d x1 c1 a7 (fun e=>d2 g (H4 (e▸((k.PA d).mp j).1))) fun u w he hu hw=>?_
  rcases k.Hj he with (h|⟨b8,_,a3⟩)|(h|⟨ba,_,b3⟩)
  ·exact(Hu al hu h).elim
  ·exact(QV (u:=u) (v:=v) (fun e=>ag (e▸hu)) (fun e=>s2 a3 (by rw[←e];exact k.Hv (i2 g)))
    (k.Hb (1-d) (d1 g) (i2 g) u (H4 (s1 hu))).symm (k.Hb (1-d) (d1 g) (i2 g) v (H4 ((k.PA d).mp j).1)).symm
    (k.HA d (s1 hu) (s1 b8) (s1 hw) (s1 a3)) (a4 w (s1 a3))).elim
  ·exact .inr (ak w (Py hw h))
  ·exact .inl (aj u (Py hu b3) w (Py hw ba))
lemma R7 {v:Q2}(aq:k.Ia={v})(bd:v∉k.B1)(af:v∉k.Wb):PV C:=by
 classical
 have a9:v∈k.Ia:=aq▸Ss v;have al {x} (g:x≠v):x∉k.Ia:=fun h=>g (Sp (aq▸h));have⟨hA02,hA12,_,_⟩:=YJ k.hL k.hT k.hs k.hab aq;have bl (d:F2):2<=(k.A d).card:=by fin_cases d<;>assumption
 have a4:∀w∈sl C v,w∈k.W0/\((w∈k.Wa/\TC C k.a w)\/(w∈k.B1∩k.Wb/\TC C k.b w)):=fun w hw=>by
  rcases k.ec (Hr hw) with (h1|h2)|⟨hB,h1|h2⟩
  ·exact(af (k.Mk (Q5 k.hL.1 h1))).elim
  ·have hW:=Q5 k.hL.1 h2;exact⟨Ul _ hW,.inl ⟨hW,h2⟩⟩
  ·exact(af (Q5 k.hL.1 h1)).elim
  ·have PQ:=Py (hB.resolve_left bd) (Q5 k.hL.1 h2);exact⟨Ur _ PQ,.inr ⟨PQ,h2⟩⟩
 let Lv':=(sl C v).filter fun w=>w∉k.A 0/\w∉k.A 1;let Lvb':=Lv'.filter fun w=>¬TC C k.a w;have j (d:F2) {w:Q2} (hw:w∈Lv'):w∉k.A d:=by have h:=(Fp hw).2;fin_cases d;exact h.1;exact h.2
 have a5 (d:F2) {w:Q2} (hw:s(v,w)∈U C):w∈k.A0 d\/w∈k.A0 (1-d)\/w∈Lv':=by
  have Pt:w≠v:=(G11.ne_of_adj (Qh hw)).symm;have hw0:=(a4 w (Mn hw)).1
  by_cases h1:w∈k.A d;· exact .inl (Py (R4 h1 fun h2=>al Pt ((k.PA d).mpr ⟨h1,h2⟩)) hw0)
  by_cases h2:w∈k.A (1-d);· exact .inr (.inl (Py (R4 h2 fun h=>h1 (by rwa[Qd] at h)) hw0))
  exact .inr (.inr (Fm ⟨Mn hw,match d,h1,h2 with|0,a,b=>⟨a,b⟩|1,a,b=>⟨b,a⟩⟩))
 have aj (d:F2) (c0 c1:Q2) (hcov:∀u w,s(u,w)∈U C->PE c0 (k.A (1-d)) u w\/PE c1 (k.A d) u w\/PE v Lv' u w):PV C:=by
  let bb:=k.Hc (1-d) c0;let b4:=k.Hc d c1
  obtain⟨M,hM,ba,_⟩:=HB k.hL.1 (E:=U C) Subset.rfl k.Rz False False.elim
   (fun _ hw=>Hr (Fp hw).1) (fun w hw=>k.R2 ((a4 w (Fp hw).1).2.elim (.inl ·.2) (.inr ·.2))) bb b4
   (fun u w he=>(hcov u w he).elim (fun h=>.inr (.inl (h.elim (fun ⟨hu,hw⟩=>k.PS he hu hw) fun ⟨hw,hu⟩=>(k.PS (PK he) hw hu).sym)))
    fun h=>h.elim (fun h=>.inr (.inr (h.elim (fun ⟨hu,hw⟩=>k.PS he hu hw) fun ⟨hw,hu⟩=>(k.PS (PK he) hw hu).sym))) .inl)
   (k.Hf fun _ g hL=>j (1-d) hL g) (k.Hf fun _ g hL=>j d hL g)
   (.inr (.inl (by
    simp only[bb,b4,PF,Kf,V9,Sbu]
    exact(Cl (show k.A (1-d)∩(sl C c1∩k.A d)⊆{v} from fun _ g=>aq▸(k.PA d).mpr ⟨i2 (i2 g),i1 g⟩)).trans (by simp))))
  have h1:=k.R6;have h2:=Cl hM;simp only[bb,b4,PF,Kf,Cs] at ba;omega
 rcases k.MT bl with⟨c0,_,c1,_,bm,bq,h2⟩|⟨d,ay,bs,bu,bt⟩|⟨d,ay,⟨c1,ad⟩⟩
 ·refine aj 0 c0 c1 fun u w he=>?_
  have hd {x:Q2} (g:s(v,x)∈U C):PE c0 (k.A 1) v x\/PE c1 (k.A 0) v x\/PE v Lv' v x:=by
   rcases a5 0 g with h|h|h;exact .inl (.inr ⟨bm x h,i2 a9⟩);exact .inr (.inl (.inr ⟨bq x h,i1 a9⟩));exact .inr (.inr (.inl ⟨rfl,h⟩))
  by_cases am:u=v;· exact am▸hd (am▸he)
  by_cases ak:w=v;· exact H9 _ _ (ak▸hd (ak▸PK he))
  exact k.Hm 0 H9 he (al am) (al ak) fun x y t g q=>(h2 x y t g q).elim (fun h=>.inl (.inl ⟨h,s1 q⟩)) fun h=>.inr (.inl (.inr ⟨h,s1 g⟩))
 ·have bv:k.A0 d=∅:=by fin_cases d<;>assumption
  have c8:k.A0 (1-d)=∅:=by fin_cases d<;>assumption
  refine k.Rp aq ay bs bu bt (by have:=k.Rh (P:=Lvb'.Nonempty);split_ifs at this<;>omega) k.MS False False.elim
   (fun w hw=>by rcases a5 d hw with h|h|h;exact(Hh bv h).elim;exact(Hh c8 h).elim;exact h)
   (fun _ hw=>Hr (Fp hw).1)
   (fun w hw=>by
    by_cases hA:TC C k.a w
    ·exact hA.elim (fun h0=>.inl (Bub _ Sul h0)) .inr
    ·have bz:w∈Lvb':=Fk hw hA;have Pt:Lvb'.Nonempty:=⟨w,bz⟩
     rcases(a4 w (Fp hw).1).2 with⟨_,bx⟩|⟨PQ,_⟩
     ·exact(hA bx).elim
     ·exact .inl (Mbu ⟨opnd C k.b (1-k.db),Ur _ (by simp[Pt]),i1 PQ⟩))
   (fun y1 _=>.inr (Hz fun x g hL=>by
    have⟨z,hz,b9⟩:=Bup g;have hxW':=i2 (k.PB.mp hL).2.1
    rcases Up hz with h|h
    ·exact s2 hxW' (Ul _ (Qc k.hL.1 k.a z h b9))
    ·split_ifs at h;rw[Sp h] at b9;exact s2 hxW' (Ur _ (Py b9 (s1 hxW')));exact N0 h))
   fun _ _=>k.Hf fun _ g hL=>j d hL g
 ·have ap:∀z∈k.A0 (1-d),z=c1:=fun z hz=>uq (k.RK (1-d) (by rw[Qd];exact bl d)) hz ad
  have a3:∀u∈k.A d,Ga c1 u:=fun u hu=>k.Hb (1-d) (d1 ad) (i2 ad) u (H4 hu)
  have ae {u w:Q2} (he:s(u,w)∈U C) (P:Q2->Q2->Prop) (hs:∀x y,P x y->P y x)
    (hc:∀x,s(c1,x)∈U C->x∈k.A d->P c1 x) (hv:∀x,x∈Lv'->P v x)
    (h34:∀x y,s(x,y)∈U C->x∈k.A' d->y∈k.A' (1-d)->((x∈k.JE/\y∈k.Jy)\/(y∈k.JE/\TC C k.b y/\x∈k.Jy))->P x y):P u w:=by
   have b8 {x:Q2} (g:s(v,x)∈U C):x=c1\/x∈Lv':=by
    rcases a5 d g with h|h|h;exact(Hh ay h).elim;exact .inl (ap x h);exact .inr h
   by_cases am:u=v;· subst u;exact(b8 he).elim (fun e=>hs _ _ (e▸hc v (e▸PK he) ((k.PA d).mp a9).1)) (hv w)
   by_cases ak:w=v;· subst w;exact(b8 (PK he)).elim (fun e=>e▸hc v (e▸he) ((k.PA d).mp a9).1) fun h=>hs _ _ (hv u h)
   exact k.Hm d hs he (al am) (al ak) fun x y t g q=>by
    rcases k.Hj t with (h|⟨ab,_,ac⟩)|(h|⟨an,ht,aa⟩)
    ·exact(Hu ay g h).elim
    ·exact h34 x y t g q (.inl ⟨ab,ac⟩)
    ·have e:=ap y (Py q h);exact hs _ _ (e▸hc x (e▸PK t) (s1 g))
    ·exact h34 x y t g q (.inr ⟨an,ht,aa⟩)
  by_cases b6:∃x1∈k.AB d,∃w1∈k.AW (1-d),s(x1,w1)∈U C
  ·have⟨x1,ax,w1,az,c6⟩:=b6
   have bf:(k.AB d).card<=1:=by by_contra! h;exact k.Ha ((k.Mr (1-d)).resolve_right (by rw[Qd];omega)) ad az
   have au:∀u∈k.AB d,u=x1:=fun u hu=>uq bf hu ax
   by_cases b7:∃x0∈k.AW d,∃y∈k.AB (1-d),s(x0,y)∈U C
   ·have⟨x0,a8,y,q,bj⟩:=b7
    have hcy:c1≠y:=fun e=>r2 q (e▸k.Hv (i2 ad));have b5:∀u∈k.AW d,u=x0:=fun u hu=>uq (k.T7 ad q) hu a8
    by_cases aw:Lvb'=∅
    ·let bh:=k.Hc d c1;let bg:=k.MX (1-d) x0
     obtain⟨Mv,hMv,M4,hM4,ba,ce,br⟩:=MC k.hL.1 (L2:=k.lb x1 (k.AW (1-d))) (Fs _ _) (Fs _ _)
      (Qg k.hL.1 k.a) (Qg k.hL.1 k.b) False False False.elim False.elim
      (fun _ hw=>Hr (Fp hw).1) (fun _ hw=>(k.PB.mp hw).1)
      (fun w hw=>by by_contra h;exact notMem_empty w (aw▸Fk hw h)) (fun _ hw=>(k.PB.mp hw).2.2) bh bg
      (fun u w he=>ae he _ Jj (fun x g ar=>.inr (.inr (.inl (k.PS g rfl ar)))) (fun x g=>.inl (.inl ⟨rfl,g⟩))
       fun x y t g q h34=>h34.elim (fun ⟨ab,ac⟩=>.inr (.inr (.inr (k.PS t (b5 x (Py g ab)) (Py q ac)))))
        fun ⟨an,ht,aa⟩=>.inr (.inl (k.HF t (au x (Py g aa)) (Py q an) ht)))
      (.inr (.inl (Hz fun _ g hL=>r2 (k.PB.mp hL).2.1 (Ul _ (RU k.hL.1 k.a g)))))
      (k.Hf fun _ g hL=>j d hL g) (k.Hf fun _ g hL=>j (1-d) hL g)
      k.Hs (k.JA Ir) (k.HC fun _ g hL=>d2 hL (H4 g))
     have bp:=Yf k.hL.1 (fun m hm=>(Fp (hMv hm)).2) br fun _ hw bk=>r2 (k.PB.mp hw).2.1 (Ul _ bk);have cb:=Yq (hMv.trans (Fs _ _)) (hM4.trans (Fs _ _)) bp
     have bk:=HR (C:=C) k.a;have cf:=HR (C:=C) k.b;simp only[bh,bg,PF,Kf,Cs] at ba;omega
    ·exfalso
     have⟨w2,c5⟩:=Nem aw;have ah:w2∈Lv':=(Fp c5).1;have av:=(a4 w2 (Fp ah).1).1;have hIaV:=(k.PA d).mp a9;have be:x0≠v:=fun e=>d2 a8 (e▸hIaV.2);have b3:¬Ga v y:=fun c4=>QV be hcy (a3 x0 (d1 a8)).symm (a3 v hIaV.1).symm (Qh bj) c4;have ca:=j d ah;have c9:=j (1-d) ah
     refine VU (a3 v hIaV.1) (a3 x0 (d1 a8)) (a3 x1 (d1 ax))
      be ?_ ?_ (k.Hw a9 (r1 ax) (r1 a8)) (Qh bj) hcy.symm ?_ ?_ ?_ b3 (Qh c6) ?_ ?_ ?_ ?_ ?_
      ((k.Hw a9 (r1 q) (r1 az)).resolve_left b3) (Qh (Hr (Fp ah).1)) ?_ ?_ ?_ ?_ ?_ ?_
      (k.HU d (d1 ax) (d1 q) av) (k.HU d (d1 a8) (d1 az) av)<;>grind
   ·push Not at b7
    exact aj d x1 c1 fun u w he=>ae he _ H9 (fun _ _ ar=>.inr (.inl (.inl ⟨rfl,ar⟩))) (fun _ g=>.inr (.inr (.inl ⟨rfl,g⟩)))
     fun x y t g q h34=>h34.elim (fun ⟨ab,ac⟩=>(b7 x (Py g ab) y (Py q ac) t).elim) fun ⟨_,_,aa⟩=>.inl (.inl ⟨au x (Py g aa),s1 q⟩)
  ·push Not at b6;have⟨x0,a8⟩:=k.RS ad
   exact aj d x0 c1 fun u w he=>ae he _ H9 (fun _ _ ar=>.inr (.inl (.inl ⟨rfl,ar⟩))) (fun _ g=>.inr (.inr (.inl ⟨rfl,g⟩)))
    fun x y t g q h34=>h34.elim (fun ⟨ab,ac⟩=>.inl (.inl ⟨a8 ⟨y,Py q ac⟩ x (Py g ab),s1 q⟩))
     fun ⟨an,_,aa⟩=>(b6 x (Py g aa) y (Py q an) t).elim
lemma H6 (d:F2){u w:Q2}(he:s(u,w)∈U C){P:Q2->Q2->Prop}(hs:∀x y,P x y->P y x)(h0:∀x y,s(x,y)∈U C->x∈k.W0->P x y)(hI:∀x y,s(x,y)∈U C->x∈k.JE->TC C k.b x->y∈k.Jy->(y∈k.Ia\/x∈k.Ia)->P x y)(hp:∀x y,s(x,y)∈U C->x∈k.AW d->TC C k.b x->y∈k.AB (1-d)->P x y)(hq:∀x y,s(x,y)∈U C->x∈k.AW (1-d)->TC C k.b x->y∈k.AB d->P x y):P u w:=
 k.Rt hs he fun x y g h=>h.elim (h0 x y g) fun ⟨hxW,ht,hyB⟩=>by
  by_cases q:y∈k.Ia;· exact hI x y g hxW ht hyB (.inl q)
  by_cases j:x∈k.Ia;· exact hI x y g hxW ht hyB (.inr j)
  rcases k.RV d g j q with⟨t,z⟩|⟨t,z⟩
  ·exact hp x y g (Py t hxW) ht (Py z hyB)
  ·exact hq x y g (Py z hxW) ht (Py t hyB)
lemma T6 (a5:2<=(k.Ia∩k.B1).card):PV C:=by
 have⟨w,hw⟩:=H1 (Mx (A:=k.Wb) a5 fun w hw v hv=>((k.M9 (i1 hv) (i2 hv)).2 w hw).symm)
 have a4:∀u v,s(u,v)∈U C->u=w\/v=w:=fun u v he=>by
  rcases k.ec he with (h|h)|⟨_,h|h⟩
  ·exact .inl (hw u (k.Mk (Q5 k.hL.1 h)))
  ·exact .inr (hw v (k.Mk (Q5 k.hL.1 h)))
  ·exact .inl (hw u (Q5 k.hL.1 h))
  ·exact .inr (hw v (Q5 k.hL.1 h))
 have g (it:St C) (hc:it.c=w) (hW:it.W.card=1) (hL:it.L=sl C w):PV C:=by
  have a6:=MV k.hL.1 (E:=U C) it S0 (fun u v he=>.inl ((a4 u v he).elim
   (fun h=>.inl ⟨h.trans hc.symm,hL▸Mn (h▸he)⟩) fun h=>.inr ⟨h.trans hc.symm,hL▸Mn (h▸PK he)⟩)) PZ
  simp only[hW,S0,card_empty] at a6;omega
 by_cases h0:w∉k.A 0
 ·exact g (Q0 C w (sl C w) (opnd C k.a 0) (Qe k.hL.1 k.ha 0) (fun _ q=>k.nA 0 (Hr q) h0) (fun _=>Hr) False False.elim) rfl (Cs _) rfl
 by_cases h1:w∉k.A 1
 ·exact g (Q0 C w (sl C w) (opnd C k.a 1) (Qe k.hL.1 k.ha 1) (fun _ q=>k.nA 1 (Hr q) h1) (fun _=>Hr) False False.elim) rfl (Cs _) rfl
 push Not at h0 h1;have j:=(Q1 k.hL.1 k.ha h0 h1).1
 exact g (Q0 C w (sl C w) (opnd C k.b (1-k.db)) (Qe k.hL.1 k.hb (1-k.db)) (fun x q=>by
   have he:=Hr q;have Pt:x≠w:=(G11.ne_of_adj (Qh he)).symm
   rcases k.ec he with (t|z)|⟨hB,t|z⟩
   ·exact(j (Q5 k.hL.1 t)).elim
   ·exact(Pt (hw x (k.Mk (Q5 k.hL.1 z)))).elim
   ·exact hB.resolve_left fun a7=>(k.M9 (Py h0 h1) a7).1 (Q5 k.hL.1 t)
   ·exact(Pt (hw x (Q5 k.hL.1 z))).elim) (fun _=>Hr) False False.elim) rfl (Cs _) rfl
lemma T5 (hIa2:2<=k.Ia.card){v:Q2}(aq:k.Ia∩k.B1={v}):PV C:=by
 classical
 have ba:v∈k.Ia∩k.B1:=aq▸Ss v;have ac:=i1 ba;have⟨a7,q⟩:=k.M9 ac (i2 ba);have ae:k.W0.card<=1:=Mx hIa2 fun _ hw z hz=>k.PH hw z hz;have a3:∀w∈k.W0,w∉k.Ia:=fun w hw hI=>G11.irrefl (k.PH hw w hI)
 obtain⟨vp,ap,a9⟩:∃vp∈k.Ia,vp≠v:=by
  have⟨x,j,y,t,g⟩:=one_lt_card.mp (by omega:1 < k.Ia.card)
  by_cases h:x=v;exact⟨y,t,fun e=>g (h.trans e.symm)⟩;exact⟨x,j,h⟩
 have bn (s1 s2:St C) (hsum:s1.W.card+s2.W.card<=2) (h1v:s1.c≠v) (h2v:s2.c≠v)
   (hcov:∀u w,s(u,w)∈U C->PE v (k.lb v k.JE) u w\/PJ s1 u w\/PJ s2 u w) (h12:Hx s1 s2):PV C:=
  k.HM (bonus:=0) (by omega) True (fun _ z hz x j=>q x (Qc k.hL.1 k.b z hz j))
   s1 s2 (by omega) hcov (.inl ⟨h1v.symm,.inl trivial⟩) (.inl ⟨h2v.symm,.inl trivial⟩) h12
 by_cases b8:∃cs∈k.Ia∩k.JE,∃y1∈k.Jy.erase v,s(cs,y1)∈U C
 ·obtain⟨cs,ab,y1,aw,_⟩:=b8
  have hcsv:cs≠v:=fun e=>a7 (e▸r1 ab);have aa:=k.HP (i1 ab) (r1 ab)
  have bg:(k.Ia∩k.JE).card<=1:=MA (A:=k.Ia∩k.JE) (mem_erase.mp aw).1.symm
   (fun x j=>q x (r1 j)) fun x j=>(k.HP (i1 j) (r1 j) y1 (s1 (mem_erase.mp aw).2)).symm
  have bf (d:F2) {x y:Q2} (j:x∈k.AW d) (t:y∈k.AB (1-d)):False:=
   QV (u:=cs) (v:=x) (a:=v) (b:=y)
    (fun e=>d2 j (by rw[←e];exact((k.PA d).mp (i1 ab)).2))
    (fun e=>d2 t (by rw[Qd,←e];exact((k.PA d).mp ac).1))
    (q cs (r1 ab)).symm (q x (r1 j)).symm (aa y (r1 t)) (k.Jz d j t)
  let am:=k.MU cs k.Jy Ds True (fun _=>aa);let bd (h:k.W0.Nonempty):St C:=let d0:F2:=if h.choose∈k.A 0 then 1 else 0;k.Hc d0 h.choose
  exact k.HM (bonus:=0) (by omega) True (fun _ z hz x j=>q x (Qc k.hL.1 k.b z hz j))
   am (HN k.W0.Nonempty bd) (by have h1:=Re (P:=k.W0.Nonempty) (f:=bd) (fun _=>by simp[bd,PF]);simp only[am,MU,Q0,Cs];omega)
   (fun u w he=>k.H6 0 he H9
    (fun x y g a4=>by
     have Pt:k.W0.Nonempty:=⟨x,a4⟩;have e:=uq ae a4 Pt.choose_spec;have br:Pt.choose∉k.A (if Pt.choose∈k.A 0 then 1 else 0):=by split_ifs with h0;exact fun h1=>a3 _ Pt.choose_spec (Py h0 h1);exact h0
     exact .inr (.inr (Tb Pt (k.PS g e (k.nA _ g (e▸br))))))
    (fun x y g a5 ht a6 hor=>hor.elim
     (fun az=>.inl (k.HF (PK g) (Sp (aq▸Py az (s1 a6))) a5 ht).sym)
     fun b4=>.inr (.inl (k.Je g (uq bg (Py b4 a5) ab) a6)))
    (fun _ _ _ j _ t=>(bf 0 j t).elim) fun _ _ _ j _ t=>(bf 1 j t).elim)
   (.inl ⟨hcsv.symm,.inl trivial⟩)
   (MK fun Pt=>.inl ⟨fun e=>a3 _ Pt.choose_spec (by change v=Pt.choose at e;rw[←e];exact ac),.inl trivial⟩)
   (RA fun Pt=>.inl ⟨fun e=>a3 _ Pt.choose_spec (by change cs=Pt.choose at e;rw[←e];exact i1 ab),.inl trivial⟩)
 push Not at b8
 have b9 (d:F2) {y:Q2} (t:y∈k.AB (1-d)):(k.Mp d).card<=1:=
  MA (A:=k.Mp d) (x:=v) (y:=y) (fun e=>d2 t (by rw[Qd,←e];exact((k.PA d).mp ac).1))
   (fun x j=>q x (i2 j)) fun x j=>(k.HA d (d1 j) (i2 j) (d1 t) (r1 t)).symm
 have a8 (d:F2) (c0 c1:Q2) (hc0v:c0≠v) (hc1v:c1≠v)
   (hcov:∀u w,s(u,w)∈U C->PE v (k.lb v k.JE) u w\/PE c0 (k.A (1-d)) u w\/PE c1 (k.A' d) u w):PV C:=by
  let bk:=k.Hc (1-d) c0;let am:=k.JB d c1
  exact bn bk am (by simp[bk,am,PF]) hc0v hc1v (fun u w he=>(hcov u w he).elim .inl
   fun h=>h.elim (fun h=>.inr (.inl (h.elim (fun ⟨hu,hw⟩=>k.PS he hu hw) fun ⟨hw,hu⟩=>(k.PS (PK he) hw hu).sym)))
    fun h=>.inr (.inr (h.elim (fun ⟨hu,hw⟩=>k.PS he hu hw) fun ⟨hw,hu⟩=>(k.PS (PK he) hw hu).sym)))
   (k.HC fun _ j h=>s2 h j)
 have af {x y:Q2} (g:s(x,y)∈U C) (a5:x∈k.JE) (ht:TC C k.b x) (a6:y∈k.Jy) (hor:y∈k.Ia\/x∈k.Ia):
   PE v (k.lb v k.JE) x y:=by
  by_cases b6:y=v;· exact(k.HF (PK g) b6 a5 ht).sym
  rcases hor with az|b4
  ·exact(b6 (Sp (aq▸Py az (s1 a6)))).elim
  ·exact(b8 x (Py b4 a5) y (mem_erase.mpr ⟨b6,a6⟩) g).elim
 have av (d:F2) (hNo:∀x∈k.AW (1-d),∀y∈k.AB d,s(x,y)∉U C):PV C:=by
  by_cases ah:∃x0∈k.AW d,∃y2∈k.AB (1-d),s(x0,y2)∈U C
  ·obtain⟨x0,a4,y2,al,_⟩:=ah;have ak:=b9 d al
   have b7:∀w0∈k.W0,w0∉k.A d:=fun w0 hw0 bj=>k.Ha ak (Py (R4 bj fun h=>a3 w0 hw0 ((k.PA d).mpr ⟨bj,h⟩)) hw0) a4
   obtain⟨w0,hw0v,hw0_eq⟩:∃w0:Q2,w0≠v/\∀w∈k.W0,w=w0:=by
    rcases Eo k.W0 with h|⟨w0,hw0⟩
    ·exact⟨vp,a9,fun _ h'=>(Hh h h').elim⟩
    ·exact⟨w0,fun e=>a3 w0 hw0 (e▸ac),fun w hw=>uq ae hw hw0⟩
   exact a8 (1-d) w0 x0 hw0v (fun e=>a7 (e▸r1 a4)) fun u w he=>k.H6 d he H9
    (fun x y g aj=>.inr (.inl (.inl ⟨hw0_eq x aj,H4 (k.nA d g (b7 x aj))⟩)))
    (fun _ _ g a5 ht a6 hor=>.inl (af g a5 ht a6 hor))
    (fun x _ _ j _ t=>.inr (.inr (.inl ⟨uq ak (Hp j) (Hp a4),i1 t⟩))) fun x y g j _ t=>(hNo x j y t g).elim
  ·push Not at ah
   rcases Eo k.W0 with an|⟨w0,hw0⟩
   ·exact a8 d vp vp a9 a9 fun u w he=>k.H6 d he H9 (fun _ _ _ a4=>(Hh an a4).elim)
     (fun _ _ g a5 ht a6 hor=>.inl (af g a5 ht a6 hor)) (fun x y g j _ t=>(ah x j y t g).elim) fun x y g j _ t=>(hNo x j y t g).elim
   ·obtain⟨da,hda⟩:∃da:F2,w0∉k.A da:=by by_cases h0:w0∈k.A 0;exact⟨1,fun h1=>a3 w0 hw0 (Py h0 h1)⟩;exact⟨0,h0⟩
    exact a8 (1-da) w0 vp (fun e=>a3 w0 hw0 (e▸ac)) a9 fun u w he=>k.H6 d he H9
     (fun x y g a4=>by have e:=uq ae a4 hw0;exact .inr (.inl (.inl ⟨e,H4 (k.nA da g (e▸hda))⟩)))
     (fun _ _ g a5 ht a6 hor=>.inl (af g a5 ht a6 hor)) (fun x y g j _ t=>(ah x j y t g).elim) fun x y g j _ t=>(hNo x j y t g).elim
 by_cases b5:∃x0∈k.AW 0,∃y2∈k.AB 1,s(x0,y2)∈U C
 ·by_cases be:∃x1∈k.AW 1,∃y3∈k.AB 0,s(x1,y3)∈U C
  ·have⟨x0,a4,y2,al,bp⟩:=b5;have⟨x1,ad,y3,bb,bs⟩:=be
   have ak:=b9 0 al;have bh:=b9 1 bb
   rcases Eo k.W0 with an|⟨w0,hw0⟩
   ·exact a8 0 x0 x1 (fun e=>a7 (e▸r1 a4)) (fun e=>a7 (e▸r1 ad)) fun u w he=>k.H6 0 he H9
     (fun _ _ _ aj=>(Hh an aj).elim) (fun _ _ g a5 ht a6 hor=>.inl (af g a5 ht a6 hor))
     (fun x _ _ j _ t=>.inr (.inl (.inl ⟨uq ak (Hp j) (Hp a4),d1 t⟩)))
     fun x _ _ j _ t=>.inr (.inr (.inl ⟨uq bh (Hp j) (Hp ad),i1 t⟩))
   ·exfalso;have bm:=k.Hv hw0;have ax:=a3 w0 hw0
    have bu:w0∉k.A 0:=fun h0=>k.Ha ak (Py (R4 h0 fun h1=>ax (Py h0 h1)) hw0) a4;have bt:w0∉k.A 1:=fun h1=>k.Ha bh (Py (R4 h1 fun h0=>ax (Py h0 h1)) hw0) ad
    refine Z5 (q w0 bm) (q x0 (r1 a4)) (q x1 (r1 ad)) ?_ ?_ ?_
     (by rcases k.HU 0 (d1 a4) (d1 ad) hw0 with h|h|h;exact .inr (.inr h);exact .inl h.symm;exact .inr (.inl h.symm))
     (k.PH hw0 vp ap) a9 ?_ ?_ (Qh bp) ?_ ?_ ?_ ?_ ?_
     (by rcases k.Hw ap (r1 al) (r1 ad) with h|h|h;exact .inr (.inr h);exact .inl h.symm;exact .inr (.inl h.symm))
     (Qh bs) ?_ ?_ ?_ ?_ ?_ ?_
     (by rcases k.Hw ap (r1 bb) (r1 a4) with h|h|h;exact .inr (.inr h);exact .inl h.symm;exact .inr (.inl h.symm))
     (by rcases k.HU 0 (d1 bb) (d1 al) hw0 with h|h|h;exact .inr (.inr h.symm);exact .inr (.inl h.symm);exact .inl h.symm)<;>grind
  ·push Not at be;exact av 0 be
 ·push Not at b5;exact av 1 b5
lemma Rg (hIa2:2<=k.Ia.card)(ad:k.Ia∩k.B1=∅)(ap:(k.Ia∩k.Wb).card<=1){cs:Q2}(aw:cs∈k.Ia∩k.JE):PV C:=by
 classical
 have ay:k.W0.card<=1:=Mx hIa2 fun _ hw z hz=>k.PH hw z hz;have a5:∀w∈k.W0,w∉k.Ia:=fun w hw hI=>G11.irrefl (k.PH hw w hI);have t:=i1 aw;have au:∀x∈k.Ia∩k.JE,x=cs:=fun _ g=>uq ap (Hp g) (Hp aw);have q:=k.HP t (r1 aw);let af:=k.MU cs k.Jy Ds True (fun _=>q)
 have ah (d:F2) {x:Q2} (g:x∈k.AW d):(k.A' (1-d)∩k.B1).card<=1:=
  MA (A:=k.A' (1-d)∩k.B1) (x:=cs) (y:=x) (fun e=>d2 g (by rw[←e];exact((k.PA d).mp t).2))
   (fun y hy=>q y (i2 hy)) fun y hy=>k.HA d (d1 g) (r1 g) (d1 hy) (i2 hy)
 have b5 {x y:Q2} (j:s(x,y)∈U C) (ag:x∈k.JE) (aa:y∈k.Jy) (hor:y∈k.Ia\/x∈k.Ia):PJ af x y:=
  hor.elim (fun bb=>(Hu ad bb (s1 aa)).elim) fun bd=>k.Je j (au x (Py bd ag)) aa
 have ae (d:F2) (hNo:∀x∈k.AW (1-d),∀y∈k.AB d,s(x,y)∉U C):PV C:=by
  let a4:=∃x0∈k.AW d,∃y2∈k.AB (1-d),s(x0,y2)∈U C;let y2:Q2:=if h:a4 then h.choose_spec.2.choose else 0;let L2:Finset Q2:=if a4 then k.lb y2 (k.AW d) else ∅
  have aq (h:k.W0.Nonempty):∃d0:F2,h.choose∉k.A d0/\(k.A d0∩L2).card<=1:=by
   set w0:=h.choose;have hw0:=h.choose_spec
   by_cases hc:a4
   ·have a8:y2∈k.AB (1-d):=by simp only[y2,hc,↓reduceDIte];exact hc.choose_spec.2.choose_spec.1
    by_cases a9:w0∈k.A (1-d)
    ·exact⟨d,fun hd=>a5 w0 hw0 ((k.PA d).mpr ⟨hd,a9⟩),(Cl Ir).trans
      (MA (A:=L2) (x:=w0) (y:=y2) (fun e=>r2 a8 (e▸k.Hv hw0))
       (fun x g=>by simp only[L2,hc,↓reduceIte] at g;exact k.Hb (1-d) a9 hw0 x (H4 (d1 (k.PB.mp g).2.1)))
       fun x g=>by simp only[L2,hc,↓reduceIte] at g;exact Qh (k.PB.mp g).1)⟩
    ·exact⟨1-d,a9,Hz fun _ g hL=>by simp only[L2,hc,↓reduceIte] at hL;exact d2 (k.PB.mp hL).2.1 g⟩
   ·simp only[L2,hc,↓reduceIte,inter_empty,card_empty]
    by_cases h0:w0∈k.A 0;exact⟨1,fun h1=>a5 w0 hw0 (Py h0 h1),by omega⟩;exact⟨0,h0,by omega⟩
  let al (h:k.W0.Nonempty):St C:=k.Hc (aq h).choose h.choose
  exact k.M7 (bonus:=0) (by omega) (c:=y2) (L:=L2) False False.elim
   (fun _ g=>by by_cases hc:a4<;>simp only[L2,hc,↓reduceIte] at g;exact(k.PB.mp g).1;exact(N0 g).elim)
   (fun _ g=>by by_cases hc:a4<;>simp only[L2,hc,↓reduceIte] at g;exact(k.PB.mp g).2.2;exact(N0 g).elim)
   af (HN k.W0.Nonempty al) (by have h1:=Re (P:=k.W0.Nonempty) (f:=al) (fun _=>by simp[al,PF]);simp only[af,MU,Q0,Cs];omega)
   (fun u w he=>k.H6 d he H9
    (fun x y j ac=>by
     have Pt:k.W0.Nonempty:=⟨x,ac⟩;have e:=uq ay ac Pt.choose_spec
     exact .inr (.inr (Tb Pt (k.PS j e (k.nA _ j (e▸(aq Pt).choose_spec.1))))))
    (fun _ _ j ag _ aa hor=>.inr (.inl (b5 j ag aa hor)))
    (fun x y j g ht hy=>by
     have hc:a4:=⟨x,g,y,hy,j⟩;have hy2':y2∈k.AB (1-d):=by simp only[y2,hc,↓reduceDIte];exact hc.choose_spec.2.choose_spec.1
     exact .inl (by simp only[L2,hc,↓reduceIte];exact(k.HF (PK j) (uq (ah d hc.choose_spec.1) (Hp hy) (Hp hy2')) g ht).sym))
    fun x y j g _ hy=>(hNo x g y hy j).elim)
   (by by_cases hc:a4
       ·have hy2':y2∈k.AB (1-d):=by simp only[y2,hc,↓reduceDIte];exact hc.choose_spec.2.choose_spec.1
        exact .inl ⟨fun e=>Hu ad (by change y2=cs at e;rw[e];exact t) (r1 hy2'),.inr trivial⟩
       ·exact .inr (.inr (by simp[L2,hc])))
   (MK fun Pt=>.inr (.inr (by simpa[al,PF,side] using (aq Pt).choose_spec.2)))
   (RA fun Pt=>.inl ⟨fun e=>a5 _ Pt.choose_spec (by change cs=Pt.choose at e;rw[←e];exact t),.inl trivial⟩)
 by_cases av:∃x1∈k.AW 1,∃y3∈k.AB 0,s(x1,y3)∈U C
 ·by_cases ar:∃x0∈k.AW 0,∃y2∈k.AB 1,s(x0,y2)∈U C
  ·have⟨x0,ak,y2,a8,b3⟩:=ar;have⟨x1,am,y3,ab,b6⟩:=av
   rcases Eo k.W0 with b8|⟨w0,hw0⟩
   ·let b4:=k.TJ 0 y2
    exact k.HM (bonus:=0) (by omega) False False.elim af b4 (by simp[af,b4,PF,MU,Q0])
     (fun u w he=>k.H6 0 he H9 (fun _ _ _ ac=>(Hh b8 ac).elim) (fun _ _ j ag _ aa hor=>.inr (.inl (b5 j ag aa hor)))
      (fun _ _ j g _ hy=>.inr (.inr (k.PS (PK j) (uq (ah 0 ak) (Hp hy) (Hp a8)) g).sym))
      fun _ _ j g ht hy=>.inl (k.HF (PK j) (uq (ah 1 am) (Hp hy) (Hp ab)) g ht).sym)
     (.inl ⟨fun e=>Hu ad (by change y3=cs at e;rw[e];exact t) (r1 ab),.inr trivial⟩) k.Hs
     (.inl ⟨fun e=>Hu ad (by change cs=y2 at e;rw[←e];exact t) (r1 a8),.inl trivial⟩)
   ·exfalso;have b9:=k.Hv hw0;have bj:=a5 w0 hw0
    have an (d:F2) {x y:Q2} (hxA':x∈k.A' d) (hyB':y∈k.Jy) (j:Ga x y):w0∉k.A (1-d):=fun a9=>
     QV (u:=cs) (v:=x) (a:=w0) (b:=y)
      (fun e=>s2 hxA' (by rw[←e];exact((k.PA d).mp t).2)) (fun e=>s2 hyB' (by rw[←e];exact b9))
      (k.PH hw0 cs t).symm (k.Hb (1-d) a9 hw0 x (H4 (s1 hxA'))).symm (q y (s1 hyB')) j
    have bg:=an 0 (i1 ak) (i2 a8) (Qh b3);have bh:=an 1 (i1 am) (i2 ab) (Qh b6)
    obtain⟨vp,aj,az⟩:∃vp∈k.Ia,vp≠cs:=by
     have⟨u,hu,z,hz,be⟩:=one_lt_card.mp (by omega:1 < k.Ia.card)
     by_cases h:u=cs;exact⟨z,hz,fun e=>be (h.trans e.symm)⟩;exact⟨u,hu,h⟩
    refine XB (q y2 (r1 a8)) (q y3 (r1 ab)) ?_ (k.PH hw0 cs t).symm ?_ ?_
     (by rcases k.HU 0 (d1 ab) (d1 a8) hw0 with h|h|h;exact .inl h.symm;exact .inr (.inr h);exact .inr (.inl h))
     (k.PH hw0 vp aj) az ?_ ?_ ?_ (Qh b3).symm ?_ ?_ ?_ ?_ ?_ (k.Hw aj (r1 ab) (r1 ak))
     (Qh b6).symm ?_ ?_ ?_ ?_ ?_ ?_ (k.Hw aj (r1 a8) (r1 am)) (k.HU 0 (d1 ak) (d1 am) hw0)<;>grind
  ·push Not at ar;exact ae 1 ar
 ·push Not at av;exact ae 0 av
lemma Rd (hIa2:2<=k.Ia.card)(bt:k.Ia∩k.B1=∅)(b5:(k.Ia∩k.Wb).card<=1)(c4:∀cs∈k.Ia∩k.JE,∀y1∈k.Jy,s(cs,y1)∉U C):PV C:=by
 classical
 have a9:k.W0.card<=1:=Mx hIa2 fun _ hw z hz=>k.PH hw z hz;have aj:∀w∈k.W0,w∉k.Ia:=fun w hw hI=>G11.irrefl (k.PH hw w hI)
 have ab {x y:Q2} (g:s(x,y)∈U C) (a5:x∈k.JE) (t:y∈k.Jy) (hor:y∈k.Ia\/x∈k.Ia):False:=
  hor.elim (fun bv=>Hu bt bv (s1 t)) fun bx=>c4 x (Py bx a5) y t g
 have aq (d:F2) (hSm:(k.AB (1-d)).card<=1):PV C:=by
  have⟨y2,b6⟩:=H1 hSm;let L2:Finset Q2:=if y2∈k.AB (1-d) then k.lb y2 (k.AW d) else ∅;have b7:∀w∈L2,s(y2,w)∈U C:=fun _ j=>by by_cases h:y2∈k.AB (1-d)<;>simp only[L2,h,↓reduceIte] at j;exact(k.PB.mp j).1;exact(N0 j).elim
  have b9:∀w∈L2,TC C k.b w:=fun _ j=>by by_cases h:y2∈k.AB (1-d)<;>simp only[L2,h,↓reduceIte] at j;exact(k.PB.mp j).2.2;exact(N0 j).elim
  have au:∀w∈L2,w∈k.AW d:=fun _ j=>by by_cases h:y2∈k.AB (1-d)<;>simp only[L2,h,↓reduceIte] at j;exact(k.PB.mp j).2.1;exact(N0 j).elim
  rcases k.Mr (1-d) with ay|ae
  ·have⟨x1,bd⟩:=H1 ay
   by_cases b4:∃w0∈k.W0,w0∈k.A (1-d)
   ·have⟨w0,hw0,a3⟩:=b4
    have ag:w0∉k.A d:=fun h=>aj w0 hw0 ((k.PA d).mpr ⟨h,a3⟩)
    have bf:L2.card<=1:=by
     by_cases h:y2∈k.AB (1-d)
     ·simp only[L2,h,↓reduceIte]
      exact MA (A:=k.lb y2 (k.AW d)) (x:=w0) (y:=y2) (fun e=>r2 h (e▸k.Hv hw0))
       (fun z hz=>k.Hb (1-d) a3 hw0 z (H4 (d1 (k.PB.mp hz).2.1))) fun z hz=>Qh (k.PB.mp hz).1
     ·simp[L2,h]
    let a6:=k.Hc d w0
    have c5:=MV k.hL.1 (E:=Rj C y2 L2) a6 S0 (fun u w ba=>by
     have⟨he,bs⟩:=Rn ba
     exact k.H6 d he (P:=fun x y=>(∀z∈L2,s(x,y)≠s(y2,z))->PJ a6 x y\/PJ S0 x y)
      (fun _ _ h hn=>HV _ _ (h fun z hz e=>hn z hz (Sw.trans e)))
      (fun x y g a7 _=>by have e:=uq a9 a7 hw0;exact .inl (k.PS g e (k.nA d g (e▸ag))))
      (fun _ _ g a5 _ t hor _=>(ab g a5 t hor).elim)
      (fun x y g j ht q hn=>by
       have e:=b6 y q;have hy2':y2∈k.AB (1-d):=e▸q
       exact(hn x (by simp only[L2,hy2',↓reduceIte];exact k.PB.mpr ⟨e▸PK g,j,ht⟩) (by rw[e,Sw])).elim)
      (fun _ _ _ j _ _ _=>(k.Ha ay (Py (R4 a3 fun h=>ag (by rwa[Qd] at h)) hw0) j).elim) bs) PZ
    have h1:=Rk (C:=C) (c:=y2) bf;simp only[a6,PF,Kf,Cs,S0,card_empty] at c5;omega
   ·have⟨w0,ak⟩:=H1 a9;let a6:=k.Hc (1-d) w0;let av:=k.MX d x1
    exact k.M7 (bonus:=0) (by omega) False False.elim b7 b9 a6 av (by simp[a6,av,PF])
     (fun u w he=>k.H6 d he H9
      (fun x y g a7=>.inr (.inl (k.PS g (ak x a7) (k.nA (1-d) g fun h=>b4 ⟨x,a7,h⟩))))
      (fun _ _ g a5 _ t hor=>(ab g a5 t hor).elim)
      (fun x y g j ht q=>by have e:=b6 y q;have hy2':y2∈k.AB (1-d):=e▸q;exact .inl (by simp only[L2,hy2',↓reduceIte];exact(k.HF (PK g) e j ht).sym))
      fun x _ g j _ q=>.inr (.inr (k.PS g (bd x (Hp j)) q)))
     (k.Hf fun _ j hL=>d2 (au _ hL) j) (k.JA Ir) (k.HC fun _ j hL=>d2 hL j)
  ·rw[Qd] at ae
   have bb (d':F2) {w0:Q2} (hw0:w0∈k.W0) (a3:w0∈k.A d') (hs1:(k.AB (1-d')).card<=1) (hs2:(k.AB d').card<=1):PV C:=by
    have ag:w0∉k.A (1-d'):=fun h=>aj w0 hw0 ((k.PA d').mpr ⟨a3,h⟩);have⟨ya,c3⟩:=H1 hs1;have⟨yb,c7⟩:=H1 hs2;let Lb:Finset Q2:=if yb∈k.AB d' then (sl C yb).filter (·∈k.AW (1-d')) else ∅
    have bg:Lb.card<=1:=by
     by_cases h:yb∈k.AB d'
     ·simp only[Lb,h,↓reduceIte]
      exact MA (A:=(sl C yb).filter (·∈k.AW (1-d'))) (x:=w0) (y:=yb) (fun e=>r2 h (e▸k.Hv hw0))
       (fun z hz=>k.Hb d' a3 hw0 z (d1 (Fp hz).2)) fun z hz=>Qh (Hr (Fp hz).1)
     ·simp[Lb,h]
    let a6:=k.Hc (1-d') w0
    exact k.HM (E:=Rj C yb Lb) (Rk (C:=C) (c:=yb) bg) False False.elim
     a6 S0 (by simp[a6,PF,S0])
     (fun u w ba=>by
      have⟨he,br⟩:=Rn ba
      exact k.H6 d' he (P:=fun x y=>(∀z∈Lb,s(x,y)≠s(yb,z))->PE ya (k.lb ya (k.AW d')) x y\/PJ a6 x y\/PJ S0 x y)
       (fun _ _ h hn=>H9 _ _ (h fun z hz e=>hn z hz (Sw.trans e)))
       (fun x y g a7 _=>by have e:=uq a9 a7 hw0;exact .inr (.inl (k.PS g e (k.nA (1-d') g (e▸ag)))))
       (fun _ _ g a5 _ t hor _=>(ab g a5 t hor).elim)
       (fun _ y g j ht q _=>.inl (k.HF (PK g) (c3 y q) j ht).sym)
       (fun x y g j _ q hn=>by
        have e:=c7 y q;have hyb':yb∈k.AB d':=e▸q
        exact(hn x (by simp only[Lb,hyb',↓reduceIte];exact Fk (Mn (e▸PK g)) j) (by rw[e,Sw])).elim) br)
     k.JC HH PZ
   by_cases h0:∃w0∈k.W0,w0∈k.A d;· have⟨w0,hw0,a3⟩:=h0;exact bb d hw0 a3 hSm ae
   by_cases h1:∃w0∈k.W0,w0∈k.A (1-d);· have⟨w0,hw0,a3⟩:=h1;exact bb (1-d) hw0 a3 (by rw[Qd];exact ae) hSm
   have⟨y3,c6⟩:=H1 ae;have⟨w0,ak⟩:=H1 a9;let a6:=k.PF d w0 k.Ia fun _ j=>((k.PA d).mp j).1;let av:=k.TJ (1-d) y3
   exact k.M7 (bonus:=0) (by omega) False False.elim b7 b9 a6 av (by simp[a6,av,PF])
    (fun u w he=>k.H6 d he H9
     (fun x y g a7=>.inr (.inl (k.PS g (ak x a7) ((k.PA d).mpr ⟨k.nA d g fun h=>h0 ⟨x,a7,h⟩,k.nA (1-d) g fun h=>h1 ⟨x,a7,h⟩⟩))))
     (fun _ _ g a5 _ t hor=>(ab g a5 t hor).elim)
     (fun x y g j ht q=>by have e:=b6 y q;have hy2':y2∈k.AB (1-d):=e▸q;exact .inl (by simp only[L2,hy2',↓reduceIte];exact(k.HF (PK g) e j ht).sym))
     fun _ y g j _ q=>.inr (.inr (k.PS (PK g) (c6 y q) j).sym))
    (.inr (.inl ((Cl fun _ j=>Py (i2 (i2 j)) (RU k.hL.1 k.b (i1 j))).trans b5)))
    (k.Hf fun _ j hL=>d2 (au _ hL) j) (k.HC fun _ j hL=>d2 hL (H4 j))
 by_cases h1:(k.AB 1).card<=1;· exact aq 0 h1
 by_cases h0:(k.AB 0).card<=1;· exact aq 1 h0
 have be:2<=(k.AB 1).card:=by omega
 have bh:2<=(k.AB 0).card:=by omega
 have af:(k.Mp 0).card<=1:=(k.Mr 0).resolve_right (by change ¬(k.AB 1).card<=1;omega)
 have ad:(k.Mp 1).card<=1:=(k.Mr 1).resolve_right (by change ¬(k.AB 0).card<=1;omega)
 have⟨x0,a7⟩:=H1 af;have⟨x1,bd⟩:=H1 ad
 rcases Eo k.W0 with bp|⟨w0,hw0⟩
 ·exact k.HJ 0 x0 x1 fun u w he=>k.H6 0 he HV (fun _ _ _ a4=>(Hh bp a4).elim)
   (fun _ _ g a5 _ t hor=>(ab g a5 t hor).elim)
   (fun x _ _ j _ q=>.inl (.inl ⟨a7 x (Hp j),d1 q⟩)) fun x _ _ j _ q=>.inr (.inl ⟨bd x (Hp j),i1 q⟩)
 have b3 (d:F2) (hw0n:w0∉k.A (1-d)) (hE:k.AW d=∅) (hO:(k.Mp (1-d)).card<=1):PV C:=by
  have⟨xo,bu⟩:=H1 hO
  exact k.HJ d w0 xo fun u w he=>k.H6 d he HV
   (fun x y g a4=>by have e:=uq a9 a4 hw0;exact .inl (.inl ⟨e,k.nA (1-d) g (e▸hw0n)⟩))
   (fun _ _ g a5 _ t hor=>(ab g a5 t hor).elim)
   (fun _ _ _ j _ _=>(Hh hE j).elim) fun x _ _ j _ q=>.inr (.inl ⟨bu x (Hp j),i1 q⟩)
 have bl:=aj w0 hw0
 by_cases ap:w0∈k.A 0
 ·have az:w0∉k.A 1:=fun h1=>bl (Py ap h1);exact b3 0 az (Ee.mpr fun _ j=>k.Ha af (Py (R4 ap az) hw0) j) ad
 by_cases b8:w0∈k.A 1
 ·exact b3 1 ap (Ee.mpr fun _ j=>k.Ha ad (Py (R4 b8 ap) hw0) j) af
 by_cases bn:k.AW 0=∅;· exact b3 0 b8 bn ad
 by_cases bm:k.AW 1=∅;· exact b3 1 ap bm af
 exfalso
 have⟨ce,a4⟩:=Nem bn;have⟨ch,ac⟩:=Nem bm;have⟨cd,ah,cf,al,bj⟩:=KX be;have⟨cc,an,cg,am,bk⟩:=KX bh;have⟨v1,Pu,v2,aw,bq⟩:=KX hIa2
 refine Xj (k.Jz 0 a4 ah) (k.Jz 0 a4 al) bj ?_ ?_ ?_ (k.Jz 1 ac an) ?_ ?_ ?_ (k.Jz 1 ac am) bk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  (k.HU 0 (d1 an) (d1 ah) hw0) (k.HU 0 (d1 an) (d1 al) hw0) (k.HU 0 (d1 am) (d1 ah) hw0) (k.HU 0 (d1 am) (d1 al) hw0)
  (k.PH hw0 v1 Pu) ?_ ?_ ?_ ?_ ?_ ?_ (k.Hw Pu (r1 an) (r1 a4)) (k.Hw Pu (r1 am) (r1 a4)) (k.Hw Pu (r1 ah) (r1 ac)) (k.Hw Pu (r1 al) (r1 ac))
  (k.PH hw0 v2 aw) bq ?_ ?_ ?_ ?_ ?_ ?_ (k.Hw aw (r1 an) (r1 a4)) (k.Hw aw (r1 am) (r1 a4)) (k.Hw aw (r1 ah) (r1 ac)) (k.Hw aw (r1 al) (r1 ac))<;>grind
lemma RY (hIa2:2<=k.Ia.card)(a4:k.Ia∩k.B1=∅):PV C:=by
 classical
 have j:k.W0.card<=1:=Mx hIa2 fun _ hw z hz=>k.PH hw z hz;have a5:∀w∈k.W0,w∉k.Ia:=fun w hw hI=>G11.irrefl (k.PH hw w hI)
 by_cases ak:k.B1.card<=1
 ·rcases Eo k.Jy with aq|⟨y0,q⟩
  ·have⟨w0,ag⟩:=H1 j
   obtain⟨d,hd⟩:∃d:F2,∀w∈k.W0,w∉k.A d:=by
    rcases Eo k.W0 with h|⟨w,hw⟩;exact⟨0,fun _ h'=>(Hh h h').elim⟩
    by_cases h0:w∈k.A 0;exact⟨1,fun x g h1=>a5 w hw (Py h0 (uq j g hw▸h1))⟩
    exact⟨0,fun x g ar=>h0 (uq j g hw▸ar)⟩
   exact k.HJ (1-d) w0 0 fun u v he=>k.Rt HV he
    fun x y a7 h=>h.elim (fun a9=>.inl (.inl ⟨ag x a9,H4 (k.nA d a7 (hd x a9))⟩)) fun h=>(Hh aq h.2.2).elim
  ·have ae:∀y∈k.B1,y=y0:=fun y hy=>uq ak hy (s1 q)
   let Lr:=k.lb y0 k.JE
   have ah (h:k.W0.Nonempty):∃da:F2,h.choose∉k.A da/\(k.A da∩Lr).card<=1:=by
    set w0:=h.choose;have hw0:=h.choose_spec;have an:w0≠y0:=fun e=>s2 q (e▸k.Hv hw0);have ab:(k.Ia∩Lr).card<=1:=MA (A:=k.Ia∩Lr) an (fun x g=>k.PH hw0 x (i1 g)) fun _ g=>Qh (k.PB.mp (i2 g)).1;have t (d:F2) (hy:y0∉k.A d):Lr⊆k.A d:=fun _ g=>k.nA d (k.PB.mp g).1 hy
    have a3 (d:F2) (hw:w0∈k.A d):∃da:F2,w0∉k.A da/\(k.A da∩Lr).card<=1:=by
     refine⟨1-d,fun h'=>a5 w0 hw0 ((k.PA d).mpr ⟨hw,h'⟩),?_⟩
     by_cases hy:y0∈k.A (1-d)
     ·have ap:=t d fun h0=>Hu a4 ((k.PA d).mpr ⟨h0,hy⟩) (s1 q)
      exact(Cl fun _ g=>Py ((k.PA d).mpr ⟨ap (i2 g),i1 g⟩) (i2 g)).trans ab
     ·exact(Cl Ir).trans (MA (A:=Lr) an (fun x g=>k.Hb d hw hw0 x (t (1-d) hy g)) fun _ g=>Qh (k.PB.mp g).1)
    by_cases h0:w0∈k.A 0;· exact a3 0 h0
    by_cases h1:w0∈k.A 1;· exact a3 1 h1
    obtain⟨d,hd⟩:∃d:F2,y0∉k.A d:=by by_cases am:y0∈k.A 0;exact⟨1,fun h'=>Hu a4 (Py am h') (s1 q)⟩;exact⟨0,am⟩
    exact⟨1-d,by fin_cases d<;>assumption,(Cl fun _ g=>Py ((k.PA d).mpr ⟨t d hd (i2 g),i1 g⟩) (i2 g)).trans ab⟩
   let ac (h:k.W0.Nonempty):St C:=k.Hc (ah h).choose h.choose
   exact k.HM (bonus:=0) (by omega) False False.elim (HN k.W0.Nonempty ac) S0
    (by have h1:=Re (P:=k.W0.Nonempty) (f:=ac) (fun _=>by simp[ac,PF]);simp only[S0,card_empty];omega)
    (fun u v he=>k.Rt H9 he fun x y a7 h=>h.elim (fun a9=>by
      have Pt:k.W0.Nonempty:=⟨x,a9⟩;have e:=uq j a9 Pt.choose_spec
      exact .inr (.inl (Tb Pt (k.PS a7 e (k.nA _ a7 (e▸(ah Pt).choose_spec.1))))))
     fun ⟨hxW,ht,hyB⟩=>.inl (k.HF (PK a7) (ae y (s1 hyB)) hxW ht).sym)
    (MK fun Pt=>.inr (.inr (by simpa[ac,PF,side] using (ah Pt).choose_spec.2))) HH PZ
 have a6:(k.Ia∩k.Wb).card<=1:=Mx (by omega:2<=k.B1.card) fun _ g y hy=>k.HP (i1 g) (i2 g) y hy
 by_cases aj:∃cs∈k.Ia∩k.JE,∃y1∈k.Jy,s(cs,y1)∈U C
 ·obtain⟨cs,av,_⟩:=aj;exact k.Rg hIa2 a4 a6 av
 ·push Not at aj;exact k.Rd hIa2 a4 a6 aj
end T1a
lemma WZ (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0e:N C b db=∅): Bd C:=by
 let k:T1a C:=⟨hL,hT,a,b,hs,hab,db,hrb,hno2,hB0e⟩
 by_cases t:2<=k.Ia.card
 ·by_cases q:2<=(k.Ia∩k.B1).card;· exact k.T6 q
  by_cases h:k.Ia∩k.B1=∅;· exact k.RY t h
  have⟨v,hv⟩:=Finset.card_eq_one.mp (show (k.Ia∩k.B1).card=1 by have:=Cpr (Nem h);omega)
  exact k.T5 t hv
 ·by_cases h0:k.Ia=∅;· exact k.TX h0
  have⟨v,hv⟩:=Finset.card_eq_one.mp (show k.Ia.card=1 by have:=Cpr (Nem h0);omega)
  by_cases g:v∈k.B1;· exact k.RP hv g
  by_cases j:v∈k.Wb;· exact k.RN hv g j
  exact k.R7 hv g j
section CompactT2Ia0
open Finset
abbrev Q2:=Fin 11
abbrev F2:=Fin 2
abbrev SS (C:Ck):=St C
abbrev US (C:Ck):=Us C
abbrev Wm (C:Ck)(g:ℕ):=Mw C g
abbrev sd (C:Ck)(g:ℕ)(d:F2):=N C g d
abbrev oi (C:Ck)(w:ℕ):=Oi C w
abbrev WS {C:Ck}(l:List (St C)):=(l.map (fun it=>it.W.card)).sum
abbrev C1 (l:List (SS C))(e:Sym2 Q2):Prop:=∃i∈l,∃x∈i.L,e=s(i.c,x)
abbrev Vd (l:List (SS C))(E:Finset (Sym2 Q2)):Prop:=∀e∈E,C1 l e
abbrev Pz (C:Ck):Prop:=
 (US C).card<=2*(centreless G11 C).card+2+
  (rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card
section
variable {α:Type} [DecidableEq α] {x y:α} {A B:Finset α}
lemma i1 (h:x∈A∩B):x∈A:=(I1 h)
lemma i2 (h:x∈A∩B):x∈B:=(I2 h)
lemma mi (a:x∈A)(b:x∈B):x∈A∩B:=Im a b
lemma s1 (h:x∈A\B):x∈A:=(D1 h)
lemma s2 (h:x∈A\B):x∉B:=(D2 h)
lemma ms (a:x∈A)(b:x∉B):x∈A\B:=Dm a b
lemma u1 (h:x∈A):x∈A∪B:=Ul B h
lemma u2 (h:x∈B):x∈A∪B:=Ur A h
lemma mu (h:x∈A∪B):x∈A\/x∈B:=Up h
lemma nE:x∉(∅:Finset α):=notMem_empty x
lemma ZK (h:x∈({y}:Finset α)):x=y:=Sp h
lemma eE (h:∀z,z∉A):A=∅:=Ee.mpr h
lemma sR:A⊆A:=Subset.rfl
lemma iL:A∩B⊆A:=Il
lemma iR:A∩B⊆B:=Ir
lemma Z1 (h:A⊆B):A.card<=B.card:=Cl h
lemma e1 (h:A.card<=1)(g:x∈A)(j:y∈A):x=y:=Qp h g j
lemma BY (g:x∈B)(hs:A⊆B)(hn:x∉A):A.card+1<=B.card:=by have h:=Z1 (Ism ⟨g,hs⟩);rwa[Cns hn] at h
lemma P5 (hx:x∈A)(hy:y∈A)(hn:x≠y):2<=A.card:=by have h:=Z1 (show ({x,y}:Finset α)⊆A by grind);rwa[Cp hn] at h
lemma BU (h0:A≠∅)(h2:¬2<=A.card):∃z,A={z}:=
 card_eq_one.mp (by have:=Cpr (Nem h0);omega)
end
section
variable {α:Type} {p:α->Prop} {_:DecidablePred p} {x:α} {A:Finset α}
lemma f1 (h:x∈A.filter p):x∈A:=(Fp h).1
lemma f2 (h:x∈A.filter p):p x:=(Fp h).2
lemma mf (a:x∈A)(b:p x):x∈A.filter p:=Fk a b
lemma fS:A.filter p⊆A:=Fs p A
end
lemma ml {E:Finset (Sym2 Q2)}{c x:Q2}(h:s(c,x)∈E):x∈Q4 c E:=Zm h
lemma Pr {E:Finset (Sym2 Q2)}{c x:Q2}(h:x∈Q4 c E):s(c,x)∈E:=Zl h
lemma sw {u v:Q2}:s(u,v)=s(v,u):=Sw
lemma sM {x u v:Q2}:x∈s(u,v)↔x=u\/x=v:=Sym2.mem_iff
lemma sI {P:Sym2 Q2->Prop}(h:∀u v,P s(u,v))(e:Sym2 Q2):P e:=Sym2.ind h e
lemma sE {E:Finset (Sym2 Q2)}{Q:Prop}(h:∀u v,s(u,v)∈E->Q){e:Sym2 Q2}(he:e∈E):Q:=by
 induction e using Sym2.ind with| _ u v=>exact h u v he
lemma Wj {α:Type}[DecidableEq α](x y:α):({x,y}:Finset α).card<=2:=(Cil _ _).trans (by simp)
lemma aU {u v:Q2}(h:s(u,v)∈US C):Ga u v:=Qh h
lemma b1 {A B:Finset Q2}(g:2<=B.card)(h:∀x∈A,∀y∈B,Ga x y):A.card<=1:=
 Qa Q3 g h
lemma Bu {C:Ck}(g:ℕ):(W0For G11 C g).card<=(centreless G11 C).card:=
 (Qj (G:=G11) (C:=C) g).trans (Qs g)
lemma BJ (d:F2):d=0\/d=1:=by fin_cases d<;>simp
section
variable {C:Ck} {a:SS C} {l l1 l2:List (SS C)} {e:Sym2 Q2} {c:Q2}
lemma wA {m n k:ℕ}(h1:WS l1<=m)(h2:WS l2<=n)(h:m+n<=k:=by decide):WS (l1++l2)<=k:=by simp[WS] at*;omega
lemma wC {m n k:ℕ}(h1:a.W.card<=m)(h2:WS l<=n)(h:m+n<=k:=by decide):WS (a::l)<=k:=by simp[WS] at*;omega
lemma cL (h:C1 l1 e):C1 (l1++l2) e:=by obtain⟨i,g,x,j,rfl⟩:=h;exact⟨i,Kal _ g,x,j,rfl⟩
lemma cR (h:C1 l2 e):C1 (l1++l2) e:=by obtain⟨i,g,x,j,rfl⟩:=h;exact⟨i,Kar _ g,x,j,rfl⟩
lemma cH (h:∃x∈a.L,e=s(a.c,x)):C1 (a::l) e:=by obtain⟨x,g,rfl⟩:=h;exact⟨a,Kc,x,g,rfl⟩
lemma cT (h:C1 l e):C1 (a::l) e:=by obtain⟨i,g,x,j,rfl⟩:=h;exact⟨i,Km _ g,x,j,rfl⟩
lemma c1 (h:∃x∈a.L,e=s(a.c,x)):C1 [a] e:=cH h
lemma Pn (hs:∀x∈l1,x∈l2)(h:C1 l1 e):C1 l2 e:=by obtain⟨i,g,x,j,rfl⟩:=h;exact⟨i,hs i g,x,j,rfl⟩
lemma Pj (ha:a.good)(hl:∀i∈l,i.good):∀i∈a::l,i.good:=fun i g=>(Kp g).elim (·▸ha) (hl i)
lemma Xq (h:∀i∈l1,i.good)(g:∀i∈l2,i.good):∀i∈l1++l2,i.good:=fun i j=>(Kap j).elim (h i) (g i)
lemma Zn (ha:a.c=c)(hl:∀i∈l,i.good):∀i∈a::l,i.c≠c->i.good:=fun i g hn=>(Kp g).elim (fun h=>(hn (h▸ha)).elim) (hl i)
lemma BN (j:∀i∈l1,i.c≠c->i.good)(g:∀i∈l2,i.good):∀i∈l1++l2,i.c≠c->i.good:=fun i q hn=>(Kap q).elim (fun h=>j i h hn) (g i)
end
lemma Wp {E:Finset (Sym2 Q2)}{c:Q2}{L:Finset Q2}(h:∀e∈E,∃x∈L,e=s(c,x)):E.card<=L.card:=
 (Z1 fun e he=>by obtain⟨x,g,rfl⟩:=h e he;exact Mi ⟨x,g,rfl⟩).trans Ci
lemma WC {E:Finset (Sym2 Q2)}{c:Q2}(h:∀u v,s(u,v)∈E->u=c\/v=c): ∀e∈E,∃x∈Q4 c E,e=s(c,x):=sI fun u v he=>(h u v he).elim (fun h=>⟨v,h▸ml he,h▸rfl⟩) (fun h=>⟨u,h▸ml (sw▸he),h▸sw⟩)
lemma By {v:Q2}{E:Finset (Sym2 Q2)}{P:Sym2 Q2->Prop}(h:∀u w,s(u,w)∈E->u≠v->w≠v->P s(u,w)){e:Sym2 Q2}(he:e∈E): (∃w∈Q4 v E,e=s(v,w))\/P e:=by
 induction e using Sym2.ind with| _ u w=>
 by_cases g:u=v;· subst g;exact .inl ⟨w,ml he,rfl⟩
 by_cases hw:w=v;· subst hw;exact .inl ⟨u,ml (sw▸he),sw⟩
 exact .inr (h u w he g hw)
lemma WQ (j:Ao C)(HZ:2<=2*(centreless G11 C).card+(mixing G11 C).card)(h:Q2)(g:List (SS C))(hs:WS g<=4)(q:Vd g (US C))(hb:∀i∈g,i.c≠h->i.good):Pz C:=by have:=Qw (E:=US C) j h g q hb;dsimp only[Pz,WS,US] at*;omega
lemma Bk {E:Finset (Sym2 Q2)}(P Q:Finset Q2){w:ℕ}(q:E⊆US C)(hw:w < 11+C.gates.length)(hQ:Q⊆oi C w)(t:P.card<=1)(z:∀u v,s(u,v)∈E->(u∈P/\v∈Q)\/(v∈P/\u∈Q)): ∃j:SS C,j.W={w}/\j.L⊆Q/\j.L.card<=4/\(∀e∈E,∃x∈j.L,e=s(j.c,x))/\(E.Nonempty->j.c∈P):=by
 have⟨c,g⟩:=Qk t
 refine⟨Q0 C c (Q4 c E∩Q) w hw (iR.trans hQ) (fun _ hx=>q (Pr (i1 hx))) False False.elim,
  rfl,iR,(Z1 iL).trans (KH q c),
  Z6 fun u v he=>(z u v he).elim (fun ⟨hu,hv⟩=>.inl ⟨g u hu,mi (ml (g u hu▸he)) hv⟩)
   (fun ⟨hv,hu⟩=>.inr ⟨g v hv,mi (ml (g v hv▸sw▸he)) hu⟩),
  fun ⟨_,he⟩=>sE (fun u v he=>(z u v he).elim (fun ⟨h,_⟩=>g u h▸h) (fun ⟨h,_⟩=>g v h▸h)) he⟩
lemma XU {g:ℕ}{db:F2}{u v:Q2}(h0:∃x∈sd C g db,x=u\/x=v)(h:∃y∈sd C g (1-db),y=u\/y=v): ∀d:F2,u∈sd C g d\/v∈sd C g d:=by obtain⟨x,hx,rfl|rfl⟩:=h0<;>obtain⟨y,hy,rfl|rfl⟩:=h<;>intro d<;>fin_cases db<;>fin_cases d<;>simp_all
lemma X0 {g:ℕ}{u v:Q2}(h:∀d:F2,u∈sd C g d\/v∈sd C g d)(hu:u∉sd C g 0∩sd C g 1)(hv:v∉sd C g 0∩sd C g 1): (u∈sd C g 0/\v∈sd C g 1)\/(u∈sd C g 1/\v∈sd C g 0):=by have:=h 0;have:=h 1;grind
lemma Zs {g:ℕ}(db:F2){u v:Q2}(j:∀d:F2,u∈sd C g d\/v∈sd C g d)(h:u∉sd C g 0∩sd C g 1)(hv:v∉sd C g 0∩sd C g 1): (u∈sd C g db/\v∈sd C g (1-db))\/(u∈sd C g (1-db)/\v∈sd C g db):=by have:=X0 j h hv;grind
lemma XC {g:ℕ}{w:Q2}(h:w∉sd C g 0∩sd C g 1):∃d:F2,w∉sd C g d:=
 if h0:w∈sd C g 0 then ⟨1,by grind⟩ else ⟨0,h0⟩
abbrev gS (hAO:Ao C){g:ℕ}(hg:g∈Jk C)(d:F2)(c:Q2)(hS:c∈sd C g d)(hW:c∈Wm C g)(E:Finset (Sym2 Q2))(hE:E⊆US C):=
 Q9 hAO hg d c hS hW E hE
noncomputable def Zj (hAO:Ao C){g:ℕ}(hg:g∈Jk C)(d:F2)(E:Finset (Sym2 Q2))(hE:E⊆US C):List (SS C):=
 if h:(sd C g d∩Wm C g).Nonempty then [gS hAO hg d h.choose (i1 h.choose_spec) (i2 h.choose_spec) E hE] else []
section
variable {C:Ck} {hAO:Ao C} {g:ℕ} {hg:g∈Jk C} {d:F2} {E:Finset (Sym2 Q2)} {hE:E⊆US C}
lemma Vq:∀i∈Zj hAO hg d E hE,i.good:=by intro i g;unfold Zj at g;split_ifs at g<;>simp_all [Q9,Q0]
lemma VD:WS (Zj hAO hg d E hE)<=1:=by unfold Zj;split_ifs<;>simp[WS,Q9,Q0]
lemma XG:∀i∈Zj hAO hg d E hE,i.c∈sd C g d∩Wm C g:=by intro i j;unfold Zj at j;split_ifs at j with h;simp at j;subst j;exact h.choose_spec;cases j
lemma ZV (j:1<=WS (Zj hAO hg d E hE)):(sd C g d∩Wm C g).Nonempty:=by by_contra h;unfold Zj at j;simp[h,WS] at j
lemma XM (q:(sd C g d∩Wm C g).card<=1){u v:Q2}(he:s(u,v)∈E)(j:u∈sd C g d∩Wm C g)(hv:v∈sd C g (1-d)):∃i∈Zj hAO hg d E hE,u=i.c/\v∈i.L:=by have hn:(sd C g d∩Wm C g).Nonempty:=⟨u,j⟩;have h:=e1 q j hn.choose_spec;exact⟨gS hAO hg d hn.choose (i1 hn.choose_spec) (i2 hn.choose_spec) E hE,by simp[Zj,hn],h,mi (ml (h▸he)) hv⟩
end
lemma XA (z:Ao C){g:ℕ}(hg:g∈Jk C){c0 c1:Q2}(q:c0∈(sd C g 0\sd C g 1)∩Wm C g)(j:c1∈(sd C g 1\sd C g 0)∩Wm C g)(a8:∀w∈Wm C g,w=c0\/w=c1){E:Finset (Sym2 Q2)}(t:E⊆US C)(hE:∀u w:Q2,s(u,w)∈E->(u∈Wm C g\/w∈Wm C g)/\∀d:F2,u∈sd C g d\/w∈sd C g d): ∃l:List (SS C),WS l=2/\(∀i∈l,i.good)/\Vd l E:=by
 let a0:=gS z hg 0 c0 (s1 (i1 q)) (i2 q) E t;let a1:=gS z hg 1 c1 (s1 (i1 j)) (i2 j) E t;refine⟨[a0,a1],by simp[WS,a0,a1,Q9,Q0],by simp[a0,a1,Q9,Q0],X6 fun u w he=>?_⟩
 have h1 (x y:Q2) (hxy:s(x,y)∈E) (hx:x∈Wm C g):∃i∈([a0,a1]:List (SS C)),x=i.c/\y∈i.L:=
  (a8 x hx).elim (fun h=>⟨a0,by simp,h,mi (ml (h▸hxy)) (((hE x y hxy).2 1).resolve_left (h▸s2 (i1 q)))⟩)
   (fun h=>⟨a1,by simp,h,mi (ml (h▸hxy)) (((hE x y hxy).2 0).resolve_left (h▸s2 (i1 j)))⟩)
 exact(hE u w he).1.elim (fun hu=>by have⟨i,hi,hc,hL⟩:=h1 u w he hu;exact⟨i,hi,.inl ⟨hc,hL⟩⟩)
  (fun hw=>by have⟨i,hi,hc,hL⟩:=h1 w u (sw▸he) hw;exact⟨i,hi,.inr ⟨hc,hL⟩⟩)
lemma Vk (a3:Ao C){c:Q2}{L:Finset Q2}{W_c Mc:Finset ℕ}(af:Mc⊆mixing G11 C)(a6:∀z∈W_c,z < 11+C.gates.length)(ad:∀z∈W_c,∀x∈oi C z,Ga c x)(a4:∀w∈L,s(c,w)∈US C)(ac:∀w∈L,w∈W_c.biUnion (oi C)\/ ∃t∈Tp C,∃d:F2,∃m∈Mc,O C (opnd C t d) m/\w∈sd C t (1-d))(q:Q2)(g:List (SS C))(hb:∀i∈g,i.c≠q->i.good)(hc:∀e∈US C,(∃w∈L,e=s(c,w))\/C1 g e): ∃M⊆Mc,(US C).card<=(rFull G11 C).card+W_c.card+WS g+M.card /\ ∃j:ℕ->Q2, (∀m∈M,j m∈L/\∃t∈Tp C,∃d:F2,O C (opnd C t d) m/\j m∈sd C t (1-d)) /\ (∀m1∈M,∀m2∈M,m1≠m2->j m1≠j m2):=by
 classical
 have⟨L0,Lm,M,hM,ab,aa,a7,ak,j,ah,a8⟩:=QU (L:=L) (W_c:=W_c) a3 af a4 ac;set Em:=Lm.image (fun w=>s(c,w));set E':=US C\Em
 have aq:(US C).card<=E'.card+M.card:=by
  have:=Z1 (show US C⊆E'∪Em by grind)
  have:=(Cu E' Em).trans (A2l Ci E'.card);omega
 let ic:SS C:=⟨c,L0,W_c,a6,a7,fun _ hx=>a4 _ (aa hx),True,fun _=>ad⟩
 have ag:=Qw (E:=E') a3 q (ic::g)
  (fun e a5=>(hc e (s1 a5)).elim (fun ⟨w,hw,hq⟩=>(mu (ab▸hw)).elim (fun h0=>cH ⟨w,h0,hq⟩)
   fun hm=>(s2 a5 (Mi ⟨w,hm,hq.symm⟩)).elim) cT)
  (fun i hi hn=>(Kp hi).elim (fun h=>h▸trivial) fun h=>hb i h hn)
 simp only[Lmc,Lsc,ic] at ag;dsimp only[WS,US] at*;exact⟨M,hM,by omega,j,ah,a8⟩
lemma Ph {E:Finset (Sym2 Q2)}{it:SS C}(hW:it.W.card=1)(h:∀e∈E,∃x∈it.L,e=s(it.c,x)): ∃l:List (SS C),WS l<=1/\(∀b∈l,∃x,s(b.c,x)∈E)/\(∀x∈l,∀y∈l,x.c=y.c->x=y) /\ (∀x∈l,∀y∈l,x.c≠y.c->(x.W.biUnion (oi C)∩y.L).card<=1\/(y.W.biUnion (oi C)∩x.L).card<=1)/\Vd l E:=by
 classical
 refine⟨if E.Nonempty then [it] else [],by dsimp only[WS];split_ifs<;>simp[hW],?_,by grind,by grind,?_⟩
 ·intro b hb;split_ifs at hb with hn;simp at hb;subst hb;have⟨e,he⟩:=hn;obtain⟨x,_,g⟩:=h e he;exact⟨x,g▸he⟩;cases hb
 ·intro e he;have⟨x,j,g⟩:=h e he;exact⟨it,by simp[show E.Nonempty from⟨e,he⟩],x,j,g⟩
lemma Wx (hL:Ls C){a b mb:ℕ}(hs:Jk C={a,b})(ap:mb∈mixing G11 C)(ay:mb < b)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b){Ub:Finset (Sym2 Q2)}(t:Ub⊆US C)(q:∀u v:Q2,s(u,v)∈Ub->(∀d:F2,u∈sd C b d\/v∈sd C b d) /\ ((u∈Wm C b/\Tc C b u)\/(v∈Wm C b/\Tc C b v)))(hUa:(∃ia:SS C,ia.W.card=1/\ia.L.card<=4/\∀e∈US C\Ub,∃x∈ia.L,e=s(ia.c,x))\/ (∃ia:List (SS C),WS ia<=2/\(∀i∈ia,i.good)/\Vd ia (US C\Ub))):Pz C:=by
 classical dsimp only[Pz]
 have hb:b∈Jk C:=by simp[hs]
 have HZ:=QN hL.1 hb ap ay hbWit;set Ua:=US C\Ub;set Ib:=sd C b 0∩sd C b 1;set Wb:=Wm C b;have ar:=WQ hL.1 HZ
 have bb:∃(ba:Q2) (iA:List (SS C)),WS iA<=2/\(∀i∈iA,i.c≠ba->i.good)/\Vd iA Ua:=
  hUa.elim (fun ⟨ia,hW1,_,hc⟩=>⟨ia.c,[ia],by simp[WS,hW1],Zn rfl (by simp),fun e he=>c1 (hc e he)⟩)
   (fun ⟨ia,a7,hg,hc⟩=>⟨0,ia,a7,fun i hi _=>hg i hi,hc⟩)
 have aq (ib:List (SS C)) (hsB:WS ib<=2) (a6:∀i∈ib,i.good) (g:Vd ib Ub):Pz C:=by have⟨ba,iA,a7,b5,a3⟩:=bb;exact ar ba (iA++ib) (wA a7 hsB) (fun e he=>if hm:e∈Ub then cR (g e hm) else cL (a3 e (ms he hm))) (BN b5 a6)
 have a9 (w:Q2) (hwW:w∈Wb) (d0:F2) (hw0:w∈sd C b d0) (hnd0:w∉sd C b (1-d0))
   (hcw:∀e∈Ub,∃x,e=s(w,x)):Pz C:=
  aq [gS hL.1 hb d0 w hw0 hwW Ub t] (by simp[WS,Q9,Q0]) (by simp[Q9,Q0]) fun e he=>by obtain⟨y,rfl⟩:=hcw e he;exact c1 ⟨y,mi (ml he) (((q w y he).1 (1-d0)).resolve_left hnd0),rfl⟩
 have bd {M:Finset ℕ} (hM:M⊆(mixing G11 C).filter (fun m=>O C (11+m) b)):M.card+1<=(mixing G11 C).card:=
  BY ap (hM.trans fS) fun h=>by have:=Qy hL.1 ap hb (Fp (hM h)).2;omega
 by_cases a8:Ib=∅
 · rcases KJ hL.1 hb a8 t (fun u v he=>
    ⟨X0 (q u v he).1 (by simp[Ib,a8]) (by simp[Ib,a8]),(q u v he).2.imp (·.1) (·.1)⟩) with
    ⟨ib,hWb1,hLb4,g⟩|⟨ib,hsB,a6,g⟩
   · rcases hUa with⟨ia,b3,_,a3⟩|⟨ia,a7,b8,a3⟩
     · obtain⟨Pa,b9,bq,_⟩:=Ky hL.1 Q3 ia.hW ia.hL ia.he
       have:=Wp a3;have:=Wp g;have:=Z1 b9
       have bz:Ua.card+Ub.card=(US C).card:=Csd t
       by_cases cg:1<=(centreless G11 C).card
       ·have:=Cpr ⟨mb,ap⟩;omega
       · by_cases am:ib.c∈Wb
         · rcases Eo Ub with bt|⟨eb,bk⟩
           ·rw[bt,card_empty] at bz;omega
           · obtain⟨x,_,hq⟩:=g _ bk;have hn:ib.c∉Ib:=by simp[a8]
             rcases X0 (q _ _ (hq▸bk)).1 hn (by simp[Ib,a8]) with⟨h0,_⟩|⟨h1,_⟩
             ·exact a9 ib.c am 0 h0 (fun h1=>hn (mi h0 h1)) fun e he=>by obtain⟨y,_,h⟩:=g e he;exact⟨y,h⟩
             ·exact a9 ib.c am 1 h1 (fun h0=>hn (mi h0 h1)) fun e he=>by obtain⟨y,_,h⟩:=g e he;exact⟨y,h⟩
         · have bn:W0For G11 C b=∅:=card_eq_zero.mp (by have:=Bu (C:=C) b;omega)
           obtain⟨L0,Lm,Mb,az,HF,_,bs,bm,_⟩:=QU (L:=Q4 ib.c Ub) (W_c:=W0For G11 C b) hL.1 fS
            (fun _ hw=>t (Pr hw)) fun w hw=>(q ib.c w (Pr hw)).2.elim (fun ⟨h,_⟩=>(am h).elim) (·.2)
           have bl:L0=∅:=by simpa[bn] using bs
           have:=bd az
           have hUb':Ub.card<=Mb.card:=by
            have h1:=Wp fun e he=>by obtain⟨x,_,rfl⟩:=g e he;exact⟨x,ml he,rfl⟩
            rwa[HF,bl,empty_union,bm] at h1
           omega
     ·exact ar ib.c (ib::ia) (wC hWb1.le a7) (fun e he=>if hm:e∈Ub then cH (g e hm) else cT (a3 e (ms he hm))) (Zn rfl b8)
   ·exact aq ib hsB a6 g
 by_cases b4:2<=Ib.card
 · have hWb1:Wb.card<=1:=b1 b4 (fun w hw v hv=>(Q1 hL.1 hb (i1 hv) (i2 hv)).2 w hw |>.symm)
   rcases Eo Wb with av|⟨wb,ab⟩
   ·exact aq [] (by simp[WS]) (by simp) (sI fun u v he=>(q u v he).2.elim (fun ⟨h,_⟩=>(nE (av▸h)).elim) (fun ⟨h,_⟩=>(nE (av▸h)).elim))
   · have b6:∀w∈Wb,w=wb:=fun w hw=>e1 hWb1 hw ab
     have ak:wb∉Ib:=fun h=>(Q1 hL.1 hb (i1 h) (i2 h)).1 ab;have ac:=WC (E:=Ub) (c:=wb) fun u v he=>(q u v he).2.elim (fun ⟨h,_⟩=>.inl (b6 u h)) (fun ⟨h,_⟩=>.inr (b6 v h))
     let aa (d:F2) (aj:wb∉sd C b d):=Q0 C wb (Q4 wb Ub) (opnd C b d) (Qe hL.1 hb d)
      (fun x j=>((q wb x (Pr j)).1 d).resolve_left aj) (fun _ j=>t (Pr j)) False False.elim
     rcases hUa with⟨ia,b3,ca,a3⟩|⟨ia,a7,b8,a3⟩
     · by_cases hsm:wb=ia.c
       · have⟨d,aj⟩:=XC ak
         exact ar wb [ia,aa d aj] (by simp[WS,b3,aa,Q0])
          (fun e he=>if hm:e∈Ub then cT (c1 (ac e hm)) else cH (a3 e (ms he hm)))
          (fun i hi hn=>by simp[aa,Q0] at hi;rcases hi with rfl|rfl;exact(hn hsm.symm).elim;exact(hn rfl).elim)
       · by_cases al:∃d0:F2,wb∈sd C b d0
         · have⟨d0,hw0⟩:=al
           exact a9 wb ab d0 hw0 (fun h1=>ak (by fin_cases d0<;>exact mi (by assumption) (by assumption)))
            fun e he=>by obtain⟨x,_,h⟩:=ac e he;exact⟨x,h⟩
         · push Not at al
           have c9:(ia.L∩Ib).card<=1:=(Z1 fun x j=>mf (Uv _) ⟨aU (ia.he x (i1 j)),(Q1 hL.1 hb (i1 (i2 j)) (i2 (i2 j))).2 wb ab |>.symm⟩).trans (Q3 ia.c wb (Ne.symm hsm))
           have c8:(ia.L∩sd C b 0).card+(ia.L∩sd C b 1).card<=5:=by
            have:=Cui (ia.L∩sd C b 0) (ia.L∩sd C b 1)
            have:=Z1 (Us2 iL iL:(ia.L∩sd C b 0)∪(ia.L∩sd C b 1)⊆ia.L)
            have:=Z1 (show (ia.L∩sd C b 0)∩(ia.L∩sd C b 1)⊆ia.L∩Ib from fun x j=>mi (i1 (i1 j)) (mi (i2 (i1 j)) (i2 (i2 j))));omega
           obtain⟨d,hd2⟩:∃d:F2,(ia.L∩sd C b d).card<=2:=if h:(ia.L∩sd C b 0).card<=2 then ⟨0,h⟩ else ⟨1,by omega⟩
           obtain⟨La',hLas,cd,br⟩:∃La'⊆ia.L,ia.L.card<=La'.card+1/\(La'∩sd C b d).card<=1:=by
            rcases Eo (ia.L∩sd C b d) with hp|⟨y0,bh⟩
            ·exact⟨ia.L,sR,by omega,by simp[hp]⟩
            · refine⟨ia.L.erase y0,erase_subset _ _,by have:=Ceo (i1 bh);omega,?_⟩
              have:=Z1 (show ia.L.erase y0∩sd C b d⊆(ia.L∩sd C b d).erase y0 from fun x j=>mem_erase.mpr ⟨(mem_erase.mp (i1 j)).1,mi (mem_erase.mp (i1 j)).2 (i2 j)⟩)
              have:=Ceo bh;omega
           have⟨Pa,b9,bq,bu⟩:=Ky hL.1 Q3 ia.hW (hLas.trans ia.hL) (fun x j=>ia.he x (hLas j));have⟨Pb,c4,ce,be⟩:=XV hL.1 Q3 (Qe hL.1 hb d) (fun x j=>((q wb x (Pr j)).1 d).resolve_left (al d)) (fun _ j=>t (Pr j));have c6:Disjoint Pa Pb:=(ZR (w1:=opnd C b d) (W2:=ia.W) (fun p hp=>⟨⟨opnd C b d,Ss _,(be p hp).1⟩,(be p hp).2⟩) bu (by simpa[inter_comm,side] using br)).symm
           have:=Yq b9 c4 c6;have:=Wp a3;have:=Wp ac;have:Ua.card+Ub.card=(US C).card:=Csd t;omega
     · have⟨d,aj⟩:=XC ak
       exact ar wb (aa d aj::ia) (wC (Cs _).le a7) (fun e he=>if hm:e∈Ub then cH (ac e hm) else cT (a3 e (ms he hm))) (Zn rfl b8)
 · have⟨vb,ae⟩:=BU a8 b4
   have Pv:vb∈sd C b 0:=i1 (ae▸Ss vb);have Pu:vb∈sd C b 1:=i2 (ae▸Ss vb);have bp:=(Q1 hL.1 hb Pv Pu).1;have aw:=(Q1 hL.1 hb Pv Pu).2
   have bg:
     (∃ib:List (SS C),WS ib<=1/\(∀i∈ib,i.good)/\∀u w,s(u,w)∈Ub->u≠vb->w≠vb->C1 ib s(u,w))\/
     (∃c0 c1:Q2,c0∈(sd C b 0\sd C b 1)∩Wb/\c1∈(sd C b 1\sd C b 0)∩Wb/\∀w∈Wb,w=c0\/w=c1):=by
    by_cases hsm:∃d:F2,(sd C b d).card<=1
    · have⟨d,bj⟩:=hsm;have b7:vb∈sd C b d:=by fin_cases d<;>assumption
      exact .inl ⟨[],by simp[WS],by simp,fun u w he ag af=>(q u w he).1 d |>.elim (fun h=>(ag (e1 bj h b7)).elim) (fun h=>(af (e1 bj h b7)).elim)⟩
    · push Not at hsm
      exact(Kd hL.1 hb (ae▸sR) (hsm 0) (hsm 1) aw t
       (fun u w he ag af=>⟨X0 (q u w he).1 (fun h=>ag (ZK (ae▸h))) (fun h=>af (ZK (ae▸h))),(q u w he).2.imp (·.1) (·.1)⟩)).elim
       (fun ⟨ib,hsB,a6,g⟩=>.inl ⟨ib,hsB,fun i hi=>(a6 i hi).1,g⟩) .inr
   rcases bg with⟨ib,hsB,a6,g⟩|⟨c0,c1,c7,c3,c5⟩
   · have⟨ba,iA,a7,b5,a3⟩:=bb
     obtain⟨Mb,az,cf,_⟩:=Vk hL.1 fS (Qg hL.1 b)
      (fun z hz x j=>aw x (Qc hL.1 b z hz j)) (fun _ hw=>t (Pr hw))
      (fun w hw=>(q vb w (Pr hw)).2.elim (fun ⟨h,_⟩=>(bp h).elim) (·.2))
      ba (iA++ib) (BN b5 a6) (fun e he=>if hm:e∈Ub then By (fun u w hm ag af=>cR (g u w hm ag af)) hm else .inr (cL (a3 e (ms he hm))))
     have:=bd az;have:=Bu (C:=C) b;have:=wA a7 hsB (k:=3);omega
   · have⟨ib,hsB,a6,g⟩:=XA hL.1 hb c7 c3 c5 t fun u w he=>⟨(q u w he).2.imp (·.1) (·.1),(q u w he).1⟩
     exact aq ib hsB.le a6 g
structure T2 where
 C:Ck
 a:ℕ
 b:ℕ
 hL:Ls C
 hT:Tf C
 hs:Jk C={a,b}
 hab:Ic C a b
 hr0:O C (opnd C b 0) a
 hr1:O C (opnd C b 1) a
section
variable (t:T2)
lemma T2.ha:t.a∈Jk t.C:=by simp[t.hs]
lemma T2.hb:t.b∈Jk t.C:=by simp[t.hs]
def T2.ec {u v:Q2}(h:s(u,v)∈US t.C):=V3 t.hL t.hT t.hs t.hr0 t.hr1 h
lemma T2.PR {u v:Q2}(he:s(u,v)∈Yu t.C t.a): Gv t.C t.a (Pi u v)=false/\(∀d:F2,u∈sd t.C t.b d\/v∈sd t.C t.b d) /\ ((u∈Wm t.C t.b/\Tc t.C t.b u)\/(v∈Wm t.C t.b/\Tc t.C t.b v)):=by
 have⟨u',v',z,j⟩:=f2 he;have q:Gv t.C t.a (Pi u v)=false:=by rcases Sy2 z with⟨rfl,rfl⟩|⟨rfl,rfl⟩;exact j;rwa[Zg]
 rcases t.ec (QA he) with⟨g,_⟩|⟨h,h0,h1,hW⟩
 ·rw[q] at g;cases g
 ·exact⟨h,XU (db:=0) h0 h1,hW⟩
lemma T2.Ry {u v:Q2}(he:s(u,v)∈Vt t.C t.a): Gv t.C t.a (Pi u v)=true /\ ((u∈Wm t.C t.a/\(Tc t.C t.a u\/Tc t.C t.b u))\/ (v∈Wm t.C t.a/\(Tc t.C t.a v\/Tc t.C t.b v))):=
 (t.ec (s1 he)).elim id fun ⟨hgf,_⟩=>(s2 he (mf (s1 he) ⟨u,v,rfl,hgf⟩)).elim
lemma T2.MP {v:Q2}(a3:sd t.C t.a 0∩sd t.C t.a 1={v})(hbWit:(T0For G11 t.C t.b).Nonempty\/∃m∈mixing G11 t.C,O t.C (11+m) t.b)(bg:(Wm t.C t.b).Nonempty):Pz t.C:=by
 classical dsimp only[Pz]
 have a7:=Z8 t.hL.1 t.hT t.hs t.hr0 t.hr1;obtain⟨m0,m1,bl,cf,bh,_,bu,bt,bv,c8,_⟩:=ZZ t.hL t.hT t.hs t.hr0 t.hr1;have HZ:=QN t.hL.1 t.hb bl bh hbWit;set Ub:=Yu t.C t.a;set Ua:=Vt t.C t.a;set B0:=sd t.C t.b 0;set B1:=sd t.C t.b 1;set Ib:=B0∩B1;set Wb:=Wm t.C t.b;have Pv:v∈sd t.C t.a 0:=i1 (a3▸Ss v);have Pu:v∈sd t.C t.a 1:=i2 (a3▸Ss v);have ad:=(Q1 t.hL.1 t.ha Pv Pu).1;have ax:v∉Wb:=fun h=>ad (a7 h);have ab:=(Q1 t.hL.1 t.ha Pv Pu).2;have a6:∀w∈Wb,Ga v w:=fun w hw=>ab w (a7 hw);obtain⟨hA02,hA12,_,_⟩:=YJ t.hL t.hT t.hs t.hab a3
 have c6:=Kd t.hL.1 t.ha (a3▸sR) hA02 hA12 ab V7 fun u w he q j=>
  ⟨Qt t.hL.1 t.hT t.hs t.hab (t.Ry he).1 (fun h=>q (ZK (a3▸h))) (fun h=>j (ZK (a3▸h))),(t.Ry he).2.imp (·.1) (·.1)⟩
 have b3:
   (∃(bb:Q2) (ib:List (SS t.C)),WS ib<=1/\(∀i∈ib,i.c≠bb->i.good)/\∀u w,s(u,w)∈Ub->u≠v->w≠v->C1 ib s(u,w))\/
   (∃c0 c1:Q2,c0∈(B0\B1)∩Wb/\c1∈(B1\B0)∩Wb/\∀w∈Wb,w=c0\/w=c1):=by
  by_cases c7:Wb.card<=1
  · left;have⟨wb,ba⟩:=bg;have bd:∀w∈Wb,w=wb:=fun w hw=>e1 c7 hw ba
    have⟨db,c9⟩:=XC (fun h=>(Q1 t.hL.1 t.hb (i1 h) (i2 h)).1 ba)
    let it:=Q0 t.C wb (Q4 wb Ub) (opnd t.C t.b db) (Qe t.hL.1 t.hb db)
     (fun x hx=>((t.PR (Pr hx)).2.1 db).resolve_left c9) (fun _ hx=>QA (Pr hx)) False False.elim
    refine⟨wb,[it],by simp[WS,it,Q0],Zn rfl (by simp),fun u w he _ _=>?_⟩
    rcases(t.PR he).2.2 with⟨h,_⟩|⟨h,_⟩
    ·have:=bd u h;subst this;exact c1 ⟨w,ml he,rfl⟩
    ·have:=bd w h;subst this;exact c1 ⟨u,ml (sw▸he),sw⟩
  have a9:Ib⊆{v}:=fun vb bn=>by
   by_contra hn;rw[mem_singleton] at hn
   have:Wb.card<=1:=(Z1 fun x hx=>mf (Uv _) ⟨a6 x hx,(Q1 t.hL.1 t.hb (i1 bn) (i2 bn)).2 x hx⟩).trans (Q3 v vb (Ne.symm hn));omega
  by_cases ar:∃d:F2,(sd t.C t.b d).card<=1
  · left;have⟨d,ck⟩:=ar;have⟨cb,bs⟩:=Qk ck
    let it:=Q0 t.C cb (Q4 cb Ub∩sd t.C t.b (1-d)) (opnd t.C t.b (1-d)) (Qe t.hL.1 t.hb (1-d))
     iR (fun _ hx=>QA (Pr (i1 hx))) False False.elim
    refine⟨cb,[it],by simp[WS,it,Q0],Zn rfl (by simp),fun u w he q j=>?_⟩
    rcases Zs d (t.PR he).2.1 (fun h=>q (ZK (a9 h))) (fun h=>j (ZK (a9 h))) with⟨hu,ca⟩|⟨cc,hw⟩
    ·have:=bs u hu;subst this;exact c1 ⟨w,mi (ml he) ca,rfl⟩
    ·have:=bs w hw;subst this;exact c1 ⟨u,mi (ml (sw▸he)) cc,sw⟩
  push Not at ar
  exact(Kd t.hL.1 t.hb a9 (ar 0) (ar 1) a6 QA (fun u w he q j=>
   ⟨X0 (t.PR he).2.1 (fun h=>q (ZK (a9 h))) (fun h=>j (ZK (a9 h))),(t.PR he).2.2.imp (·.1) (·.1)⟩)).elim
   (fun ⟨ib,hsB,aj,ak⟩=>.inl ⟨0,ib,hsB,fun i hi _=>(aj i hi).1,ak⟩) .inr
 have cd:(W0For G11 t.C t.a∪W0For G11 t.C t.b).card<=2*(centreless G11 t.C).card:=by have:=Bu (C:=t.C) t.a;have:=Bu (C:=t.C) t.b;have:=Cu (W0For G11 t.C t.a) (W0For G11 t.C t.b);omega
 have ag:∀z∈W0For G11 t.C t.a∪W0For G11 t.C t.b,z < 11+t.C.gates.length:=fun z hz=>
  (mu hz).elim (Qg t.hL.1 t.a z) (Qg t.hL.1 t.b z)
 have ay:∀z∈W0For G11 t.C t.a∪W0For G11 t.C t.b,∀x∈oi t.C z,Ga v x:=fun z hz x hx=>
  (mu hz).elim (fun h=>ab x (Qc t.hL.1 t.a z h hx)) (fun h=>a6 x (Qc t.hL.1 t.b z h hx))
 have al:∀w,s(v,w)∈US t.C->w∈(W0For G11 t.C t.a∪W0For G11 t.C t.b).biUnion (oi t.C)\/
   ∃p∈Tp t.C,∃d:F2,∃m∈mixing G11 t.C,O t.C (opnd t.C p d) m/\w∈sd t.C p (1-d):=fun w he=>by
  have cg:Tc t.C t.a w\/Tc t.C t.b w:=
   (t.ec he).elim (fun ⟨_,h⟩=>h.elim (fun ⟨h,_⟩=>(ad h).elim) (·.2)) (fun ⟨_,_,_,h⟩=>h.elim (fun ⟨h,_⟩=>(ax h).elim) fun ⟨_,h⟩=>.inr h)
  rcases cg with (h0|⟨p,hp,d,m,g,hr,hw⟩)|(h0|⟨p,hp,d,m,g,hr,hw⟩)
  ·exact .inl (Bub _ Sul h0)
  ·exact .inr ⟨p,hp,d,m,f1 g,hr,hw⟩
  ·exact .inl (Bub _ Sur h0)
  ·exact .inr ⟨p,hp,d,m,f1 g,hr,hw⟩
 rcases c6 with⟨ia,hsA,ah,bq⟩|⟨cz,d0,c4,c5,bz⟩
 · rcases b3 with⟨bb,ib,hsB,b9,ak⟩|⟨au,aw,a5,a4,af⟩
   · obtain⟨M,hM,cr,_⟩:=Vk t.hL.1 sR ag ay (fun _ hw=>Pr hw) (fun w hw=>al w (Pr hw))
      bb (ia++ib) (fun i hi hn=>(Kap hi).elim (fun h=>(ah i h).1) fun h=>b9 i h hn)
      (fun e he=>By (fun u w he q j=>if g:s(u,w)∈Ub then cR (ak u w g q j) else cL (bq u w (ms he g) q j)) he)
     have:=Z1 hM;have:=wA hsA hsB (k:=2);omega
   · set Eb':=(US t.C).filter fun e=>e∈Ub\/∃w,e=s(v,w)/\((w=au/\v∈B1)\/(w=aw/\v∈B0))
     have⟨ib,hsB,aj,ae⟩:=XA (E:=Eb') t.hL.1 t.hb a5 a4 af fS fun u w he=>by
      have h1 {c:Q2} {d:F2} (hcW:c∈Wb) (hc0:c∈sd t.C t.b d) (Pu:v∈sd t.C t.b (1-d)) (hq:s(u,w)=s(v,c)):
        (u∈Wb\/w∈Wb)/\∀k:F2,u∈sd t.C t.b k\/w∈sd t.C t.b k:=by
       rcases Sy2 hq with⟨rfl,rfl⟩|⟨rfl,rfl⟩
       ·exact⟨.inr hcW,XU ⟨w,hc0,.inr rfl⟩ ⟨u,Pu,.inl rfl⟩⟩
       ·exact⟨.inl hcW,XU ⟨u,hc0,.inl rfl⟩ ⟨w,Pu,.inr rfl⟩⟩
      rcases f2 he with g|⟨_,hq,⟨rfl,cp⟩|⟨rfl,cl⟩⟩
      ·exact⟨(t.PR g).2.2.imp (·.1) (·.1),(t.PR g).2.1⟩
      ·exact h1 (d:=0) (i2 a5) (s1 (i1 a5)) cp hq
      ·exact h1 (d:=1) (i2 a4) (s1 (i1 a4)) cl hq
     set Lv':=(Q4 v (US t.C)).filter fun w=>¬((w=au/\v∈B1)\/(w=aw/\v∈B0));let gs:List (SS t.C):=ia++ib;have cj:WS gs<=3:=wA hsA hsB.le;have br:∀i∈gs,i.good:=Xq (fun i hi=>(ah i hi).1) aj
     have bp:∀e∈US t.C,(∃w∈Lv',e=s(v,w))\/C1 gs e:=fun e he=>
      if g:e∈Ub then .inr (cR (ae e (mf he (.inl g)))) else
       (By (fun u w h q j=>cL (bq u w h q j)) (ms he g)).elim (fun ⟨z,hz,hq⟩=>
        if hc:(z=au/\v∈B1)\/(z=aw/\v∈B0) then .inr (cR (ae e (mf he (.inr ⟨z,hq,hc⟩))))
        else .inl ⟨z,mf (ml (s1 (Pr hz))) hc,hq⟩) .inr
     by_cases ac:∀w∈Lv',Tc t.C t.a w
     · exact Yw t.hL t.hs t.hab hbWit Pv Pu (fun _ hw=>Pr (f1 hw)) ac
        gs [] (by simpa only[WS,Lmn,Lsn,add_zero] using cj) br (by simp) (by simp) (by simp) (by simp)
        (fun e he=>by simpa only[List.append_nil] using bp e he)
     · push Not at ac;have⟨w0,aq,av⟩:=ac
       have am:w0∈Wb:=(t.ec (Pr (f1 aq))).elim
        (fun ⟨_,h⟩=>h.elim (fun ⟨h,_⟩=>(ad h).elim) fun ⟨_,ht⟩=>Q5 t.hL.1 (ht.resolve_left av))
        (fun ⟨_,_,_,h⟩=>h.elim (fun ⟨h,_⟩=>(ax h).elim) (·.1))
       obtain⟨Mv,cs,cr,fw,cm,_⟩:=Vk t.hL.1 sR ag ay
        (fun _ hw=>Pr (f1 hw)) (fun w hw=>al w (Pr (f1 hw))) 0 gs (fun i hi _=>br i hi) bp
       have bm (d:F2) (m:ℕ) (g:m∈mixing G11 t.C) (hma:O t.C (11+m) t.a)
         (hms:oi t.C (11+m)⊆sd t.C t.b d) (hws:w0∈sd t.C t.b (1-d)) (hvnd:v∉sd t.C t.b d):=
        BY g cs fun cn=>by
         have⟨ch,t1,bk,d1,az,be⟩:=cm m cn
         exact KF t.hL.1 (db:=d) t.hb g hms hvnd hws am (a6 w0 am)
          (aU (Pr (f1 ch))) (fun e=>av (e▸K8 t.hL.1 t.ha bk (QH az hma) be)) bk az be
       have:Mv.card+1<=(mixing G11 t.C).card:=(af w0 am).elim
        (fun h=>bm 1 m1 cf bt c8 (h▸s1 (i1 a5)) fun h1=>f2 aq (.inl ⟨h,h1⟩))
        (fun h=>bm 0 m0 bl bu bv (h▸s1 (i1 a4)) fun h0=>f2 aq (.inr ⟨h,h0⟩))
       omega
 · have⟨ia,hsA,ah,an⟩:=XA (E:=(US t.C).filter fun e=>e∈Ua\/v∈e) t.hL.1 t.ha c4 c5 bz fS fun u w he=>
    (f2 he).elim (fun hA=>⟨(t.Ry hA).2.imp (·.1) (·.1),fun d=>((Y7 t.hL.1 t.hT t.hs t.hab d u w).mp (t.Ry hA).1).1⟩)
     (fun hv=>⟨(t.ec (f1 he)).elim (fun ⟨_,h⟩=>h.imp (·.1) (·.1)) (fun ⟨_,_,_,h⟩=>h.imp (fun ⟨h,_⟩=>a7 h) (fun ⟨h,_⟩=>a7 h)),
      fun d=>(sM.mp hv).elim (fun h=>.inl (h▸by fin_cases d<;>assumption)) (fun h=>.inr (h▸by fin_cases d<;>assumption))⟩)
   rcases b3 with⟨bb,ib,hsB,b9,ak⟩|⟨au,aw,a5,a4,af⟩
   · exact WQ t.hL.1 HZ bb (ia++ib) (wA hsA.le hsB)
      (sI fun u w he=>if hv:v∈s(u,w) then cL (an _ (mf he (.inr hv))) else if g:s(u,w)∈Ub then
       cR (ak u w g (fun h=>hv (sM.mpr (.inl h.symm))) (fun h=>hv (sM.mpr (.inr h.symm))))
       else cL (an _ (mf he (.inl (ms he g)))))
      (fun i hi hn=>(Kap hi).elim (ah i) fun h=>b9 i h hn)
   · have⟨ib,hsB,aj,ae⟩:=XA t.hL.1 t.hb a5 a4 af QA fun u w he=>⟨(t.PR he).2.2.imp (·.1) (·.1),(t.PR he).2.1⟩
     exact WQ t.hL.1 HZ 0 (ia++ib) (wA hsA.le hsB.le)
      (fun e he=>if g:e∈Ub then cR (ae e g) else cL (an e (mf he (.inl (ms he g))))) (fun i hi _=>Xq ah aj i hi)
end
lemma B6 (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b)(hr0:O C (opnd C b 0) a)(hr1:O C (opnd C b 1) a): Bd C:=by
 classical
 let t:T2:=⟨C,a,b,hL,hT,hs,hab,hr0,hr1⟩;obtain⟨m0,_,a7,_,a3,_,_,_,_,_,_⟩:=ZZ hL hT hs hr0 hr1
 rcases Eo (Yu C a) with aa|⟨eb,j⟩
 ·exact Zc hL hT hs hab fun u v ae=>t.Ry (ms ae (by rw[aa];exact nE))
 have hbWit:=sE (fun _ _ j=>(t.PR j).2.2.elim (fun ⟨_,h⟩=>Kt h) (fun ⟨_,h⟩=>Kt h)) j;have a4:(Wm C b).Nonempty:=sE (fun u v j=>(t.PR j).2.2.elim (fun ⟨h,_⟩=>⟨u,h⟩) (fun ⟨h,_⟩=>⟨v,h⟩)) j
 by_cases hIa2:2<=(sd C a 0∩sd C a 1).card
 · have q:=Z8 hL.1 hT hs hr0 hr1
   have a8:(Wm C a).card<=1:=b1 hIa2 (fun w hw v hv=>(Q1 hL.1 t.ha (i1 hv) (i2 hv)).2 w hw |>.symm);have⟨w0,a5⟩:=a4;have a6:=q a5;have g:∀w∈Wm C a,w=w0:=fun w hw=>e1 a8 hw a6;have⟨da,ac⟩:=XC (fun h=>(Q1 hL.1 t.ha (i1 h) (i2 h)).1 a6);have⟨db,a9⟩:=XC (fun h=>(Q1 hL.1 t.hb (i1 h) (i2 h)).1 a5)
   let it:SS C:=⟨w0,Q4 w0 (US C),{opnd C a da,opnd C b db},
    fun z hz=>(Nsp hz).elim (·▸Qe hL.1 t.ha da) fun h=>ZK h▸Qe hL.1 t.hb db,
    fun x hx=>(t.ec (Pr hx)).elim (fun ⟨hga,_⟩=>Mbu ⟨opnd C a da,mem_insert_self _ _,Kg hL.1 hT hs hab da hga ac⟩)
     fun ⟨_,h0,h1,_⟩=>Mbu ⟨opnd C b db,mem_insert_of_mem (Ss _),Va h0 h1 a9⟩,
    fun _ hx=>Pr hx,False,False.elim⟩
   exact WQ hL.1 (QN hL.1 t.hb a7 a3 hbWit) w0 [it] (wC (Wj _ _) (by simp[WS]:WS ([]:List (SS C))<=0))
    (fun e he=>c1 (WC (E:=US C) (c:=w0) (fun u v he=>(t.ec he).elim
     (fun ⟨_,h⟩=>h.elim (fun ⟨hu,_⟩=>.inl (g u hu)) (fun ⟨hv,_⟩=>.inr (g v hv)))
     (fun ⟨_,_,_,h⟩=>h.elim (fun ⟨hu,_⟩=>.inl (g u (q hu))) (fun ⟨hv,_⟩=>.inr (g v (q hv))))) e he))
    (Zn rfl (by simp))
 by_cases hIa0:sd C a 0∩sd C a 1=∅
 · exact Wx hL hs a7 a3 hbWit QA (fun u v he=>(t.PR he).2)
    (KJ hL.1 t.ha hIa0 V7 fun u v he=>
     ⟨Qt hL.1 hT hs hab (t.Ry he).1 (by simp[hIa0]) (by simp[hIa0]),(t.Ry he).2.imp (·.1) (·.1)⟩)
 ·have⟨v,ad⟩:=BU hIa0 hIa2;exact t.MP ad hbWit a4
noncomputable def WF (C:Ck)(a b:ℕ)(db d:F2):Finset (Sym2 Q2):=by
 classical exact(Ya C a).filter fun e=>∃u v:Q2,e=s(u,v)/\u∈sd C a d∩Wm C b/\v∈sd C a (1-d)∩sd C b (1-db)
lemma QZ {C:Ck}{a b:ℕ}{db d:F2}{e:Sym2 Q2}: e∈WF C a b db d↔e∈Ya C a/\∃u v:Q2,e=s(u,v)/\u∈sd C a d∩Wm C b/\v∈sd C a (1-d)∩sd C b (1-db):=by
 classical exact mem_filter
lemma KA {C:Ck}{a b:ℕ}{db d:F2}:WF C a b db d⊆Ya C a:=fun _ h=>(QZ.mp h).1
structure T1b where
 C:Ck
 a:ℕ
 b:ℕ
 db:F2
 hL:Ls C
 hT:Tf C
 hs:Jk C={a,b}
 hab:Ic C a b
 hrb:O C (opnd C b db) a
 hno2:¬O C (opnd C b (1-db)) a
 hB0ne:(sd C b db).Nonempty
 hIa0:sd C a 0∩sd C a 1=∅
 hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b
 hA02:2<=(sd C a 0).card
 hA12:2<=(sd C a 1).card
section
variable (t:T1b)
abbrev T1b.A (d:F2):=sd t.C t.a d
abbrev T1b.B (d:F2):=sd t.C t.b d
abbrev T1b.B0:=sd t.C t.b t.db
abbrev T1b.B1:=sd t.C t.b (1-t.db)
abbrev T1b.Ib:=sd t.C t.b 0∩sd t.C t.b 1
abbrev T1b.Wa:=Wm t.C t.a
abbrev T1b.Wb:=Wm t.C t.b
abbrev T1b.Ub:=Yu t.C t.a
abbrev T1b.Hd:=Yx t.C t.a
abbrev T1b.Ht:=Ya t.C t.a
abbrev T1b.U:=US t.C
abbrev T1b.SW (d:F2):=(t.A d∩t.Wb)\t.Wa
abbrev T1b.SB (d:F2):=(t.A d∩t.B1)\t.Wa
noncomputable abbrev T1b.Ed (d:F2):=WF t.C t.a t.b t.db d
lemma T1b.ha:t.a∈Jk t.C:=by simp[t.hs]
lemma T1b.hb:t.b∈Jk t.C:=by simp[t.hs]
lemma T1b.Mt:t.B1∩t.Wb⊆t.Wa:=K7 t.hL.1 t.hT t.hs t.hrb t.hno2
lemma T1b.bw {x:Q2}(h:x∈t.B1)(g:x∈t.Wb):x∈t.Wa:=t.Mt (mi h g)
lemma T1b.MB {d:F2}{x:Q2}(h:x∈t.A d):x∉t.A (1-d):=fun g=>by
 have h0:x∈t.A 0∩t.A 1:=by fin_cases d;exact mi h g;exact mi g h
 exact nE (t.hIa0▸h0)
lemma T1b.BI:t.B0∩t.B1=t.Ib:=by
 rcases BJ t.db with g|g<;>simp[T1b.B0,T1b.B1,T1b.Ib,g,inter_comm]
lemma T1b.MY (h:t.Ib=∅){x:Q2}:x∉t.B 0∩t.B 1:=by simp[show t.B 0∩t.B 1=∅ from h]
lemma T1b.TG (h:t.Ib=∅){x:Q2}(h0:x∈t.B0):x∉t.B1:=fun g=>nE (h▸t.BI▸mi h0 g)
lemma T1b.HZ:2<=2*(centreless G11 t.C).card+(mixing G11 t.C).card:=by obtain⟨mb,h,g,_,_⟩:=QK t.hL.1 t.hs t.hrb t.hB0ne;exact QN t.hL.1 t.hb h g t.hbWit
def T1b.F4:=WQ t.hL.1 t.HZ
def T1b.Es {u v:Q2}(h:s(u,v)∈t.Ht):=Zr t.hL t.hT t.hs t.hrb t.hno2 h
lemma T1b.PR {u v:Q2}(he:s(u,v)∈t.Ub): (∀d:F2,u∈t.B d\/v∈t.B d)/\((u∈t.Wb/\Tc t.C t.b u)\/(v∈t.Wb/\Tc t.C t.b v)):=
 ⟨XU (Kr t.hL t.hT t.hs t.hrb t.hno2 he).2.1 (Kr t.hL t.hT t.hs t.hrb t.hno2 he).2.2.1,(Kr t.hL t.hT t.hs t.hrb t.hno2 he).2.2.2⟩
lemma T1b.a2 {d:F2}{u y:Q2}(h:u∈t.A d)(g:u∈t.Wa)(j:y∈t.A (1-d)):Ga u y:=
 Y1 (d:=d) (w:=u) t.hL.1 t.hT t.hs t.hab h g y j
lemma T1b.b2 (d:F2){w v:Q2}(j:w∈t.A d)(h:w∈t.Wb)(q:v∈t.A (1-d))(g:v∈t.B1):Ga w v:=
 K9 t.hL.1 t.hT t.hs t.hab t.hrb d j h q g
lemma T1b.c2 {d:F2}{u y:Q2}(h:u∈t.B d)(g:u∈t.Wb)(j:y∈t.B (1-d)):Ga u y:=
 QC (d:=d) (w:=u) t.hL.1 t.hb h g y j
lemma T1b.Tx (d:F2):(t.A d∩t.Wa).card<=1:=
 b1 (by fin_cases d;exact t.hA12;exact t.hA02) (fun u g y h=>t.a2 (i1 g) (i2 g) h)
lemma T1b.Tj {u v:Q2}(h:Gv t.C t.a (Pi u v)=true): (u∈t.A 0/\v∈t.A 1)\/(u∈t.A 1/\v∈t.A 0):=
 Qt t.hL.1 t.hT t.hs t.hab h (by simp[t.hIa0]) (by simp[t.hIa0])
lemma T1b.tA {da:F2}{p q:Q2}(h:p∈t.A da)(g:q∈t.A (1-da)){w:Q2}(hw:w∈t.Wa): Ga p q\/Ga p w\/Ga q w:=
 Ka hw ((Qv t.hL.1 t.hT t.hs t.hab _).mpr (by
  fin_cases da;exact⟨⟨p,h,tripleInput_1 ..⟩,⟨q,g,tripleInput_2 ..⟩⟩;exact⟨⟨q,g,tripleInput_2 ..⟩,⟨p,h,tripleInput_1 ..⟩⟩))
lemma T1b.eP {u v:Q2}(he:s(u,v)∈t.Ht):s(u,v)∈t.Ed 0\/s(u,v)∈t.Ed 1:=by
 obtain⟨a5,_,_,a4⟩:=t.Es he
 rcases t.Tj a5 with⟨a3,Pu⟩|⟨j,Pv⟩<;>rcases a4 with⟨q,_,h⟩|⟨z,_,g⟩
 ·exact .inl (QZ.mpr ⟨he,u,v,rfl,mi a3 q,mi Pu h⟩)
 ·exact .inr (QZ.mpr ⟨he,v,u,sw,mi Pu z,mi a3 g⟩)
 ·exact .inr (QZ.mpr ⟨he,u,v,rfl,mi j q,mi Pv h⟩)
 ·exact .inl (QZ.mpr ⟨he,v,u,sw,mi Pv z,mi j g⟩)
lemma T1b.eS (d:F2){u v:Q2}(he:s(u,v)∈t.Ed d): u∉t.Wa/\v∉t.Wa/\((u∈(t.A d\t.A (1-d))∩t.Wb/\v∈(t.A (1-d)\t.A d)∩t.B1)\/ (v∈(t.A d\t.A (1-d))∩t.Wb/\u∈(t.A (1-d)\t.A d)∩t.B1)):=by
 have⟨j,u',v',z,h,g⟩:=QZ.mp he;have q (k:F2) (x:Q2) (hx:x∈t.A k):x∈t.A k\t.A (1-k):=ms hx (t.MB hx);have hA' (x:Q2) (hx:x∈t.A (1-d)):x∈t.A (1-d)\t.A d:=by simpa[Qd] using q (1-d) x hx
 rcases Sy2 z with⟨rfl,rfl⟩|⟨rfl,rfl⟩
 ·exact⟨(t.Es j).2.1,(t.Es j).2.2.1,.inl ⟨mi (q d _ (i1 h)) (i2 h),mi (hA' _ (i1 g)) (i2 g)⟩⟩
 ·exact⟨(t.Es j).2.1,(t.Es j).2.2.1,.inr ⟨mi (q d _ (i1 h)) (i2 h),mi (hA' _ (i1 g)) (i2 g)⟩⟩
def T1b.eL {E0 E1:Finset (Sym2 Q2)}(h0:E0⊆t.Ed 0)(h1:E1⊆t.Ed 1):=
 Yy (E0:=E0) (E1:=E1) t.hL.1 t.hT t.hs t.hab t.hrb t.hno2 t.hA02 t.hA12
  (h0.trans (KA.trans Qu)) (h1.trans (KA.trans Qu)) (fun _ _ h=>t.eS 0 (h0 h)) (fun _ _ h=>t.eS 1 (h1 h))
lemma T1b.eO {E0 E1:Finset (Sym2 Q2)}(h0:E0⊆t.Ed 0)(h1:E1⊆t.Ed 1)(g:E0=∅\/E1=∅):∃i:SS t.C,i.W.card=1/\∀e∈E0∪E1,∃x∈i.L,e=s(i.c,x):=by
 obtain⟨a0,a1,j,q,_,_,a3,z,_⟩:=KT (E0:=E0) (E1:=E1) t.hL.1 t.hT t.hs t.hab t.hrb t.hno2 t.hA02 t.hA12
  (h0.trans (KA.trans Qu)) (h1.trans (KA.trans Qu)) (fun _ _ h=>(t.eS 0 (h0 h)).2.2) (fun _ _ h=>(t.eS 1 (h1 h)).2.2)
 rcases g with rfl|rfl;exact⟨a1,q,by simpa using z⟩;exact⟨a0,j,by simpa using a3⟩
lemma T1b.RT {P:Sym2 Q2->Prop}{_:DecidablePred P}{e:Sym2 Q2}(h:e∈(t.Ed 0).filter P∪(t.Ed 1).filter P):e∈t.Ht:=(mu h).elim (fun h=>KA (f1 h)) (fun h=>KA (f1 h))
lemma T1b.TA {P:Sym2 Q2->Prop}{_:DecidablePred P}{e:Sym2 Q2}(h:e∈(t.Ed 0).filter P∪(t.Ed 1).filter P):P e:=(mu h).elim f2 f2
lemma T1b.TY {P:Sym2 Q2->Prop}{_:DecidablePred P}{u v:Q2}(j:s(u,v)∈t.Ht)(hn:s(u,v)∉(t.Ed 0).filter P∪(t.Ed 1).filter P):¬P s(u,v):=fun g=>
 (t.eP j).elim (fun h=>hn (u1 (mf h g))) (fun h=>hn (u2 (mf h g)))
lemma T1b.Te {x:Q2}(j:x∈t.Wa){e:Sym2 Q2}(h:e∈t.Ht):x∉e:=by
 induction e using Sym2.ind with| _ u v=>
 exact sM.not.mpr (not_or.mpr ⟨fun g=>(t.Es h).2.1 (g▸j),fun g=>(t.Es h).2.2.1 (g▸j)⟩)
lemma T1b.Jc {v:Q2}(g:v∉t.Wb):∀w∈Q4 v (t.U\t.Hd),Tc t.C t.b w:=fun w hw=>
 if hbm:s(v,w)∈t.Ub then (t.PR hbm).2.elim (fun ⟨h,_⟩=>(g h).elim) (·.2)
 else (t.Es (ms (ms (s1 (Pr hw)) hbm) (s2 (Pr hw)))).2.2.2.elim (fun ⟨h,_,_⟩=>(g h).elim) (·.2.1)
lemma T1b.MF {c0 c1:Q2}(g:c0∈t.A 0∩t.Wa)(h:c1∈t.A 1∩t.Wa):t.Ht=∅:=
 eE (sI fun u v he=>by
  obtain⟨a4,j,q,_⟩:=t.Es he
  have h4 (x y:Q2) (hx0:x∈t.A 0) (hy1:y∈t.A 1) (hxW:x∉t.Wa) (hyW:y∉t.Wa) (hxy:Ga x y):False:=
   QV (fun z=>hxW (by rw[←z];exact i2 g)) (fun z=>hyW (by rw[←z];exact i2 h)) (t.a2 (i1 g) (i2 g) (i1 h)) (t.a2 (i1 h) (i2 h) hx0).symm (t.a2 (i1 g) (i2 g) hy1) hxy
  exact(t.Tj a4).elim (fun ⟨h0,h1⟩=>h4 u v h0 h1 j q (aU (Qu he))) (fun ⟨h1,h0⟩=>h4 v u h0 h1 q j (aU (Qu he)).symm))
noncomputable def T1b.MN (d:F2):=Zj t.hL.1 t.ha d t.Hd K0
noncomputable def T1b.PN:=t.MN 0++t.MN 1
lemma T1b.Mh (d:F2):WS (t.MN d)<=1:=VD
lemma T1b.M0:∀i∈t.PN,i.good:=Xq Vq Vq
lemma T1b.RR:∀i∈t.PN,i.c∈t.Wa:=fun i g=>(Kap g).elim (fun h=>i2 (XG i h)) (fun h=>i2 (XG i h))
lemma T1b.J5:WS t.PN<=2:=wA (t.Mh 0) (t.Mh 1)
lemma T1b.T4 (g:¬((t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty)):WS t.PN<=1:=by
 by_contra h;have:=t.Mh 0;have:=t.Mh 1;rw[T1b.PN] at h;dsimp only[WS] at*;simp at h
 exact g ⟨ZV (show 1<=WS (t.MN 0) by dsimp only[WS];omega),ZV (show 1<=WS (t.MN 1) by dsimp only[WS];omega)⟩
lemma T1b.J4 (g:1<=WS t.PN):∃d:F2,(t.A d∩t.Wa).Nonempty:=by rw[T1b.PN] at g;dsimp only[WS] at g;simp at g;exact if h0:1<=WS (t.MN 0) then ⟨0,ZV h0⟩ else ⟨1,ZV (show 1<=WS (t.MN 1) by dsimp only[WS] at h0 ⊢;omega)⟩
lemma T1b.HK:Vd t.PN t.Hd:=by
 have q (d:F2) (u v:Q2) (he:s(u,v)∈t.Hd) (hu:u∈t.A d) (hv:v∈t.A (1-d)) (j:u∈t.Wa):∃i∈t.PN,u=i.c/\v∈i.L:=by
  obtain⟨i,g,h,hL⟩:=XM (t.Tx d) he (mi hu j) hv
  fin_cases d;exact⟨i,Kal _ g,h,hL⟩;exact⟨i,Kar _ g,h,hL⟩
 exact X6 fun u v he=>by
  rcases t.Tj (Kn t.hL t.hT t.hs t.hrb t.hno2 he).1 with⟨a3,Pu⟩|⟨z,Pv⟩<;>
   rcases(Kn t.hL t.hT t.hs t.hrb t.hno2 he).2 with j|a4
  ·have⟨i,g,h,hL⟩:=q 0 u v he a3 Pu j;exact⟨i,g,.inl ⟨h,hL⟩⟩
  ·have⟨i,g,h,hL⟩:=q 1 v u (sw▸he) Pu a3 a4;exact⟨i,g,.inr ⟨h,hL⟩⟩
  ·have⟨i,g,h,hL⟩:=q 1 u v he z Pv j;exact⟨i,g,.inl ⟨h,hL⟩⟩
  ·have⟨i,g,h,hL⟩:=q 0 v u (sw▸he) Pv z a4;exact⟨i,g,.inr ⟨h,hL⟩⟩
lemma T1b.Tv (h:List (SS t.C))(a6:WS h<=2)(z:∀i∈h,i.good)(E0' E1':Finset (Sym2 Q2))(a5:E0'⊆t.Ed 0)(a7:E1'⊆t.Ed 1)(j:∀g∈h,∀e∈E0'∪E1',g.c∉e)(a9:∀e∈t.U,e∉E0'∪E1'->C1 h e):Pz t.C:=by
 classical have⟨q,ae,a8,aa,a4,a3⟩:=t.eL a5 a7
 exact Y5 t.hL t.hs t.hrb t.hB0ne t.hbWit h q (by dsimp only[WS] at a6;omega) z
  (fun e he=>if hm:e∈E0'∪E1' then cR (a3 e hm) else cL (a9 e he hm))
  (fun g hg b hb eq=>by have⟨x,hx⟩:=a8 b hb;exact j g hg _ hx (sM.mpr (.inl eq))) aa a4
lemma T1b.Tt (da:F2)(h1:2<=(t.SW da).card)(h2:2<=(t.SB da).card)(a5:2<=(t.B1∩t.Wb).card)(hA:(t.Ed da).Nonempty)(hB:(t.Ed (1-da)).Nonempty):False:=by
 have⟨eA,ae⟩:=hA;obtain⟨ag,_,y1,rfl,_,g⟩:=QZ.mp ae;have⟨eB,ac⟩:=hB;obtain⟨ab,af,_,rfl,Pu,_⟩:=QZ.mp ac;have⟨xa,z,xb,a3,a6⟩:=KX h1;have⟨ua,a4,ub,q,a8⟩:=KX h2;have⟨al,a9,Mq,aa,a7⟩:=KX a5;have av:y1∉t.Wa:=(t.Es ag).2.2.1;have ar:af∉t.Wa:=(t.Es ab).2.1;have h:al∈t.Wa:=t.Mt a9;have j:Mq∈t.Wa:=t.Mt aa;have t1 {w} (hw:w∈t.Wa):=t.tA (i1 (s1 z)) (i1 Pu) hw;have t2 {w} (hw:w∈t.Wa):=t.tA (i1 (s1 a3)) (i1 Pu) hw;have t3 {w} (hw:w∈t.Wa):=t.tA (i1 (s1 a4)) (i1 g) hw;have t4 {w} (hw:w∈t.Wa):=t.tA (i1 (s1 q)) (i1 g) hw
 refine YX
  (t.b2 da (i1 (s1 z)) (i2 (s1 z)) (i1 g) (i2 g)).symm (t.b2 da (i1 (s1 a3)) (i2 (s1 a3)) (i1 g) (i2 g)).symm a6
  ?_ ?_ ?_ (t.b2 (1-da) (i1 Pu) (i2 Pu) (QE (i1 (s1 a4))) (i2 (s1 a4))) ?_ ?_ ?_
  (t.b2 (1-da) (i1 Pu) (i2 Pu) (QE (i1 (s1 q))) (i2 (s1 q))) a8 ?_ ?_ ?_
  ?_ ?_ ?_ ?_ ?_ ?_ (t1 h) (t2 h) (t3 h) (t4 h) a7 ?_ ?_ ?_ ?_ ?_ ?_ (t1 j) (t2 j) (t3 j) (t4 j)
  <;>grind (splits:=0) [t.MB,t.bw]
set_option maxHeartbeats 600000 in
lemma T1b.Jp (av:t.Ib=∅)(c9:¬((t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty)){cb:Q2}(aj:∀x∈t.B0,x=cb)(b3:cb∉t.Wb):Pz t.C:=by
 classical dsimp only[Pz]
 have c3:cb∈t.B0:=by have⟨z,hz⟩:=t.hB0ne;exact aj z hz▸hz
 have bu:cb∉t.B1:=t.TG av c3;have cd:=t.T4 c9
 let itcb:=Q0 t.C cb (Q4 cb t.Ub∩(t.B1∩t.Wb)) (opnd t.C t.b (1-t.db)) (Qe t.hL.1 t.hb (1-t.db))
  (iR.trans iL) (fun _ hx=>QA (Pr (i1 hx))) False False.elim
 have ax:∀e∈t.Ub,∃x∈itcb.L,e=s(itcb.c,x):=Z6 fun u v he=>by
  rcases Zs t.db (t.PR he).1 (t.MY av) (t.MY av) with⟨bj,Pu⟩|⟨cg,Pv⟩<;>rcases(t.PR he).2 with⟨au,_⟩|⟨ap,_⟩
  ·exact(b3 (aj u bj▸au)).elim
  ·exact .inl ⟨aj u bj,mi (ml (aj u bj▸he)) (mi Pu ap)⟩
  ·exact .inr ⟨aj v Pv,mi (ml (aj v Pv▸sw▸he)) (mi cg au)⟩
  ·exact(b3 (aj v Pv▸ap)).elim
 by_cases bv:(t.B1∩t.Wb).card<=1
 · have cp:t.Ub.card<=1:=(Wp ax).trans ((Z1 iR).trans bv)
   have⟨cc,cs,ca,cm,cn,bp⟩:=t.eL sR sR
   have ct:=QS (E:=t.U\t.Ub) t.hL.1 t.PN cc t.M0
    (sI fun u v he=>if hwm:s(u,v)∈t.Hd then cL (t.HK _ hwm) else cR (bp _ ((t.eP (ms he hwm)).elim u1 u2)))
    (fun g hg b hb eq=>by have⟨x,hx⟩:=ca b hb;exact(t.Es ((mu hx).elim (fun h=>KA h) (fun h=>KA h))).2.1 (eq▸t.RR g hg)) cm cn
   have:=t.HZ;have:(t.U\t.Ub).card+t.Ub.card=t.U.card:=Csd QA;dsimp only[WS,T1b.U,US] at*;omega
 have bb:2<=(t.B1∩t.Wb).card:=by omega
 have a6 (d:F2):(oi t.C (opnd t.C t.a d)∩itcb.L).card<=1:=(Z1 (inter_subset_inter_left fun _ hx=>t.Mt (i2 hx))).trans (t.Tx d)
 have ay (d:F2):(t.SW d).card<=1\/(t.SB (1-d)).card<=1:=by
  have c5 (k:F2):t.A k\t.A (1-k)=t.A k:=ext fun x=>by simp only[mem_sdiff,and_iff_left_iff_imp];exact t.MB
  simpa only[T1b.SW,T1b.SB,c5 d,show t.A (1-d)\t.A d=t.A (1-d) by simpa[Qd] using c5 (1-d)] using VK t.hL.1 t.hT t.hs t.hab t.hrb d
 have b9 (d:F2):∀u v,s(u,v)∈t.Ed d->(u∈t.SW d/\v∈t.SB (1-d))\/(v∈t.SW d/\u∈t.SB (1-d)):=fun u v he=>by
  have⟨hE,u',v',hq,ar,aq⟩:=QZ.mp he
  exact(Sy2 hq).elim (fun ⟨h1,h2⟩=>.inl ⟨ms (h1▸ar) (t.Es hE).2.1,ms (h2▸aq) (t.Es hE).2.2.1⟩)
   (fun ⟨h1,h2⟩=>.inr ⟨ms (h2▸ar) (t.Es hE).2.2.1,ms (h1▸aq) (t.Es hE).2.1⟩)
 have al (d:F2) (h1:(t.SW d).card<=1):=Bk (t.SW d) (t.SB (1-d)) (KA.trans Qu) (Qe t.hL.1 t.ha (1-d)) (fun _ hx=>i1 (s1 hx)) h1 (b9 d);have ak (d:F2) (h1:(t.SB (1-d)).card<=1):=Bk (t.SB (1-d)) (t.SW d) (KA.trans Qu) (Qe t.hL.1 t.ha d) (fun _ hx=>i1 (s1 hx)) h1 (fun u v he=>(b9 d u v he).symm.imp And.symm And.symm)
 have b6 (h0ne:(t.Ed 0).Nonempty) (h1ne:(t.Ed 1).Nonempty):(∀d:F2,(t.SW d).card<=1)\/(∀d:F2,(t.SB d).card<=1):=by
  by_contra! h;obtain⟨⟨d1,hd1⟩,⟨d2,hd2⟩⟩:=h
  have c8:=ay 0;have c4:=ay 1;simp only[show (1:F2)-0=1 from rfl,show (1:F2)-1=0 from rfl] at c8 c4
  rcases BJ d1 with rfl|rfl<;>rcases BJ d2 with rfl|rfl<;>
   rcases c8 with h0|h0<;>rcases c4 with h1|h1<;>first|exact t.Tt 0 hd1 hd2 bb h0ne h1ne|exact t.Tt 1 hd1 hd2 bb h1ne h0ne|omega
 have bf (da:F2) (gs:List (SS t.C)) (x0:SS t.C) (hx0c:x0.c=cb) (hsG:WS gs+x0.W.card<=2)
   (hgG:∀g∈gs,g.good) (hGW:∀g∈gs,g.c∈t.Wa) (hGcb:∀g∈gs,g.c≠cb)
   (hc0':∀e∈t.U,e∉t.Ht->C1 gs e\/∃x∈x0.L,e=s(x0.c,x))
   (j0 j1:SS t.C) (d0 d1:F2) (a8:j0.W={opnd t.C t.a d0}) (ab:j1.W={opnd t.C t.a d1})
   (a9:(t.Ed da).Nonempty->j0.c∈t.SW da∪t.SB (1-da)) (aa:(t.Ed (1-da)).Nonempty->j1.c∈t.SW (1-da)∪t.SB da)
   (ac:∀e∈t.Ed da,∃x∈j0.L,e=s(j0.c,x)) (ad:∀e∈t.Ed (1-da),∃x∈j1.L,e=s(j1.c,x))
   (hd01:(t.Ed da).Nonempty->(t.Ed (1-da)).Nonempty->(j0.W.biUnion (oi t.C)∩j1.L).card<=1\/(j1.W.biUnion (oi t.C)∩j0.L).card<=1)
   (hdX:(oi t.C (opnd t.C t.a d0)∩x0.L).card<=1/\(oi t.C (opnd t.C t.a d1)∩x0.L).card<=1):Pz t.C:=by
  let bcl:List (SS t.C):=(if (t.Ed da).Nonempty then [j0] else [])++(if (t.Ed (1-da)).Nonempty then [j1] else []);have af {z:SS t.C} (hz:z∈bcl):((t.Ed da).Nonempty/\z=j0)\/((t.Ed (1-da)).Nonempty/\z=j1):=by dsimp only[bcl] at hz;split_ifs at hz<;>simp_all
  have cl:WS bcl<=2:=by simp only[WS,bcl,LqA,LqS];split_ifs<;>simp[a8,ab]
  have ce:Vd bcl t.Ht:=sI fun u v he=>
   (show s(u,v)∈t.Ed da\/s(u,v)∈t.Ed (1-da) by fin_cases da;exact t.eP he;exact(t.eP he).symm).elim
    (fun h0=>by have⟨x,hx,hq⟩:=ac _ h0;exact⟨j0,Kal _ (by simp[show (t.Ed da).Nonempty from⟨_,h0⟩]),x,hx,hq⟩)
    (fun h1=>by have⟨x,hx,hq⟩:=ad _ h1;exact⟨j1,Kar _ (by simp[show (t.Ed (1-da)).Nonempty from⟨_,h1⟩]),x,hx,hq⟩)
  have h01 (h0e:(t.Ed da).Nonempty) (h1e:(t.Ed (1-da)).Nonempty):j0.c≠j1.c:=fun hq=>by
   rcases mu (a9 h0e) with h0|h0<;>rcases mu (hq▸aa h1e) with h1|h1
   ·exact t.MB (i1 (s1 h0)) (i1 (s1 h1))
   ·exact s2 h0 (t.bw (i2 (s1 h1)) (i2 (s1 h0)))
   ·exact s2 h0 (t.bw (i2 (s1 h0)) (i2 (s1 h1)))
   ·exact t.MB (i1 (s1 h1)) (i1 (s1 h0))
  have ba {x:Q2} {k1 k2:F2} (h:x∈t.SW k1∪t.SB k2):x∉t.Wa/\x≠cb:=
   (mu h).elim (fun h=>⟨s2 h,fun e=>b3 (e▸i2 (s1 h))⟩) (fun h=>⟨s2 h,fun e=>bu (e▸i2 (s1 h))⟩)
  have bn {z:SS t.C} (hz:z∈bcl):z.c≠cb:=(af hz).elim (fun ⟨h0,h⟩=>h▸(ba (a9 h0)).2) (fun ⟨h1,h⟩=>h▸(ba (aa h1)).2)
  have c6 {b:SS t.C} (hb:b∈bcl):(b.W.biUnion (oi t.C)∩x0.L).card<=1:=by
   rcases af hb with⟨_,rfl⟩|⟨_,rfl⟩;rw[a8,Sbu];exact hdX.1;rw[ab,Sbu];exact hdX.2
  exact Y5 t.hL t.hs t.hrb t.hB0ne t.hbWit gs (x0::bcl) (by dsimp only[WS] at hsG cl;simp;omega) hgG
   (fun e he=>if hE:e∈t.Ht then cR (cT (ce e hE)) else (hc0' e he hE).elim cL fun h=>cR (cH h))
   (fun g hg b ch=>(Kp ch).elim (fun h=>h▸hx0c▸hGcb g hg) fun cf=>
    (af cf).elim (fun ⟨h0,h⟩ e=>(ba (a9 h0)).1 (h▸e▸hGW g hg)) (fun ⟨h1,h⟩ e=>(ba (aa h1)).1 (h▸e▸hGW g hg)))
   (fun b1 bm b2 bg hq=>by
    rcases Kp bm with rfl|ag<;>rcases Kp bg with rfl|ae
    ·rfl
    ·exact(bn ae (hq.symm.trans hx0c)).elim
    ·exact(bn ag (hq.trans hx0c)).elim
    ·rcases af ag with⟨bq,rfl⟩|⟨be,rfl⟩<;>rcases af ae with⟨bt,rfl⟩|⟨bs,rfl⟩<;>first|rfl|exact(h01 bq bs hq).elim|exact(h01 bt be hq.symm).elim)
   (fun b1 bm b2 bg hn=>by
    rcases Kp bm with rfl|ag<;>rcases Kp bg with rfl|ae
    ·exact(hn rfl).elim
    ·exact .inr (c6 ae)
    ·exact .inl (c6 ag)
    ·rcases af ag with⟨bq,rfl⟩|⟨be,rfl⟩<;>rcases af ae with⟨bt,rfl⟩|⟨bs,rfl⟩<;>first|exact(hn rfl).elim|exact hd01 bq bs|exact(hd01 bt be).symm)
 by_cases an:∃d:F2,cb∈t.A d∩t.Wa
 · have⟨q,a5⟩:=an
   let itm:SS t.C:=⟨cb,(Q4 cb t.Hd∩t.A (1-q))∪itcb.L,{opnd t.C t.a (1-q),opnd t.C t.b (1-t.db)},
    fun z hz=>(Nsp hz).elim (·▸Qe t.hL.1 t.ha (1-q)) fun h=>ZK h▸Qe t.hL.1 t.hb (1-t.db),
    fun x hx=>(mu hx).elim (fun h=>Mbu ⟨opnd t.C t.a (1-q),mem_insert_self _ _,i2 h⟩)
     (fun h=>Mbu ⟨opnd t.C t.b (1-t.db),mem_insert_of_mem (Ss _),i1 (i2 h)⟩),
    fun x hx=>(mu hx).elim (fun h=>K0 (Pr (i1 h))) (itcb.he x),False,False.elim⟩
   have b8:(oi t.C (opnd t.C t.a q)∩itm.L).card<=1:=
    (Z1 fun x hx=>(mu (i2 hx)).elim (fun h=>(t.MB (i1 hx) (i2 h)).elim) (mi (i1 hx))).trans (a6 q)
   have bl {x:Q2} (hxA:x∈t.A (1-q)) (hxW:x∈t.Wa):False:=
    c9 (by fin_cases q;exact⟨⟨cb,a5⟩,⟨x,mi hxA hxW⟩⟩;exact⟨⟨x,mi hxA hxW⟩,⟨cb,a5⟩⟩)
   have hKill:((t.Ed q).Nonempty->(t.SB (1-q)).card<=1)/\((t.Ed (1-q)).Nonempty->(t.SW (1-q)).card<=1):=⟨
    fun ⟨_,h0⟩=>by obtain⟨hE,u',_,rfl,ar,_⟩:=QZ.mp h0;exact(Z1 fun y hy=>mf (Uv _)
     ⟨t.a2 (i1 a5) (i2 a5) (i1 (s1 hy)),t.b2 q (i1 ar) (i2 ar) (i1 (s1 hy)) (i2 (s1 hy))⟩).trans (Q3 cb u' fun e=>(t.Es hE).2.1 (e▸i2 a5)),
    fun ⟨_,h1⟩=>by obtain⟨hE,_,v',rfl,_,aq⟩:=QZ.mp h1;exact(Z1 fun y hy=>mf (Uv _)
     ⟨t.a2 (i1 a5) (i2 a5) (i1 (s1 hy)),(t.b2 (1-q) (i1 (s1 hy)) (i2 (s1 hy)) (i1 aq) (i2 aq)).symm⟩).trans (Q3 cb v' fun e=>(t.Es hE).2.2.1 (e▸i2 a5))⟩
   let b7:=Q0 t.C 0 ∅ (opnd t.C t.a q) (Qe t.hL.1 t.ha q) (by simp) (by simp) False False.elim
   obtain⟨jA,hWA,hLA,hcA,hAc⟩:∃j:SS t.C,j.W={opnd t.C t.a q}/\j.L⊆t.SW q/\(∀e∈t.Ed q,∃x∈j.L,e=s(j.c,x))/\((t.Ed q).Nonempty->j.c∈t.SW q∪t.SB (1-q)):=
    if hn:(t.Ed q).Nonempty then by obtain⟨j,hW,hL,_,hc,hP⟩:=ak q (hKill.1 hn);exact⟨j,hW,hL,hc,fun h=>u2 (hP h)⟩
    else by rw[not_nonempty_iff_eq_empty] at hn;exact⟨b7,rfl,by simp[b7,Q0],by simp[hn],by simp[hn]⟩
   obtain⟨jB,hWB,hLB,bp,hBc⟩:∃j:SS t.C,j.W={opnd t.C t.a q}/\j.L⊆t.SB q/\(∀e∈t.Ed (1-q),∃x∈j.L,e=s(j.c,x))/\((t.Ed (1-q)).Nonempty->j.c∈t.SW (1-q)∪t.SB q):=
    if hn:(t.Ed (1-q)).Nonempty then by obtain⟨j,hW,hL,_,hc,hP⟩:=al (1-q) (hKill.2 hn);rw[Qd] at hW hL;exact⟨j,hW,hL,hc,fun h=>u1 (hP h)⟩
    else by rw[not_nonempty_iff_eq_empty] at hn;exact⟨b7,rfl,by simp[b7,Q0],by simp[hn],by simp[hn]⟩
   exact bf q [] itm rfl (by simp[WS];exact Wj _ _) (by simp) (by simp) (by simp)
    (sI fun u v he bk=>.inr<|if hbm:s(u,v)∈t.Ub then by have⟨x,hx,hq⟩:=ax _ hbm;exact⟨x,u2 hx,hq⟩
     else by
      have hw:s(u,v)∈t.Hd:=by by_contra hw;exact bk (ms (ms he hbm) hw)
      have hS:=t.Tj (Kn t.hL t.hT t.hs t.hrb t.hno2 hw).1;have hS':(u∈t.A q/\v∈t.A (1-q))\/(u∈t.A (1-q)/\v∈t.A q):=by fin_cases q;exact hS;exact hS.symm
      rcases hS' with⟨hu,hv⟩|⟨hu,hv⟩<;>rcases(Kn t.hL t.hT t.hs t.hrb t.hno2 hw).2 with au|ap
      ·have hq:=e1 (t.Tx q) (mi hu au) a5;exact⟨v,u1 (mi (ml (by rw[←hq];exact hw)) hv),hq▸rfl⟩
      ·exact(bl hv ap).elim
      ·exact(bl hu au).elim
      ·have hq:=e1 (t.Tx q) (mi hv ap) a5;exact⟨u,u1 (mi (ml (by rw[←hq,sw];exact hw)) hu),hq▸sw⟩)
    jA jB q q hWA hWB hAc hBc hcA bp
    (fun h0 h1=>(b6 (by fin_cases q;exact h0;exact h1) (by fin_cases q;exact h1;exact h0)).elim
     (fun hW=>.inr ((Z1 (iR.trans hLA)).trans (hW q))) (fun hB=>.inl ((Z1 (iR.trans hLB)).trans (hB q)))) ⟨b8,b8⟩
 · push Not at an
   have hRun':=bf 0 t.PN itcb rfl (by dsimp only[WS] at cd ⊢;simp[itcb,Q0];omega) t.M0 t.RR
    (fun g hg c7=>(Kap hg).elim (fun h=>an _ (c7▸XG g h)) (fun h=>an _ (c7▸XG g h)))
    (fun e he bk=>if hbm:e∈t.Ub then .inr (ax e hbm) else .inl (t.HK e (by by_contra hw;exact bk (ms (ms he hbm) hw))))
   by_cases h01:(t.Ed 0).Nonempty/\(t.Ed 1).Nonempty
   · rcases b6 h01.1 h01.2 with hW|hB
     · obtain⟨j0,a8,_,_,ac,a9⟩:=al 0 (hW 0);obtain⟨j1,ab,br,_,ad,aa⟩:=al 1 (hW 1)
       exact hRun' j0 j1 1 0 a8 ab (fun h=>u1 (a9 h)) (fun h=>u1 (aa h)) ac ad
        (fun _ _=>.inl (by rw[a8,Sbu,show oi t.C (opnd t.C t.a (1-0))∩j1.L=∅ from eE fun x hx=>t.MB (i1 (s1 (br (i2 hx)))) (i1 hx)];simp)) ⟨a6 1,a6 0⟩
     · obtain⟨j0,a8,_,_,ac,a9⟩:=ak 0 (hB 1);obtain⟨j1,ab,br,_,ad,aa⟩:=ak 1 (hB 0)
       exact hRun' j0 j1 0 1 a8 ab (fun h=>u2 (a9 h)) (fun h=>u2 (aa h)) ac ad
        (fun _ _=>.inl (by rw[a8,Sbu,show oi t.C (opnd t.C t.a 0)∩j1.L=∅ from eE fun x hx=>t.MB (i1 hx) (i1 (s1 (br (i2 hx))))];simp)) ⟨a6 0,a6 1⟩
   · have bd (d:F2):∃j:SS t.C,∃dj:F2,j.W={opnd t.C t.a dj}/\(∀e∈t.Ed d,∃x∈j.L,e=s(j.c,x))/\((t.Ed d).Nonempty->j.c∈t.SW d∪t.SB (1-d)):=
      (ay d).elim (fun h=>by obtain⟨j,hW,_,_,hc,hP⟩:=al d h;exact⟨j,1-d,hW,hc,fun h=>u1 (hP h)⟩)
       (fun h=>by obtain⟨j,hW,_,_,hc,hP⟩:=ak d h;exact⟨j,d,hW,hc,fun h=>u2 (hP h)⟩)
     have⟨j0,d0,a8,ac,a9⟩:=bd 0;have⟨j1,d1,ab,ad,aa⟩:=bd 1;exact hRun' j0 j1 d0 d1 a8 ab a9 aa ac ad (fun h0 h1=>(h01 ⟨h0,h1⟩).elim) ⟨a6 d0,a6 d1⟩
lemma T1b.Tz (a8:t.Ib=∅)(bh:¬((t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty))(b8:2<=t.B0.card)(ab:(t.B0∩t.Wb).card<=1):Pz t.C:=by
 classical
 have aw:=t.T4 bh;have au:(t.B1∩t.Wb).card<=1:=b1 b8 (fun x hx y hy=>t.c2 (i1 hx) (i2 hx) (QE hy));let j:=Zj t.hL.1 t.hb t.db t.U sR;let q:=Zj t.hL.1 t.hb (1-t.db) t.Ub QA;have a6:∀g∈j++q,g.good:=Xq Vq Vq
 have a9:Vd (j++q) t.Ub:=by
  have h1 (u v:Q2) (he:s(u,v)∈t.Ub) (huW:u∈t.Wb):∃g∈j++q,u=g.c/\v∈g.L:=
   (Zs t.db (t.PR he).1 (t.MY a8) (t.MY a8)).elim
    (fun ⟨a7,Pu⟩=>by obtain⟨g,hg,hc,hL⟩:=XM ab (QA he) (mi a7 huW) Pu;exact⟨g,Kal _ hg,hc,hL⟩)
    (fun ⟨hu1,Pv⟩=>by obtain⟨g,hg,hc,hL⟩:=XM au he (mi hu1 huW) (QE Pv);exact⟨g,Kar _ hg,hc,hL⟩)
  exact X6 fun u v he=>(t.PR he).2.elim (fun ⟨h,_⟩=>by have⟨g,hg,hc,hL⟩:=h1 u v he h;exact⟨g,hg,.inl ⟨hc,hL⟩⟩)
   (fun ⟨h,_⟩=>by have⟨g,hg,hc,hL⟩:=h1 v u (sw▸he) h;exact⟨g,hg,.inr ⟨hc,hL⟩⟩)
 let E' (d:F2):=(t.Ed d).filter fun e=>∀z∈t.B0∩t.Wb,z∉e
 have aa:∀e∈t.U,e∉E' 0∪E' 1->C1 (t.PN++(j++q)) e:=sI fun u v he hn=>
  if hbm:s(u,v)∈t.Ub then cR (a9 _ hbm) else if hwm:s(u,v)∈t.Hd then cL (t.HK _ hwm) else by
   have hE:s(u,v)∈t.Ht:=ms (ms he hbm) hwm;have b3:∃z∈t.B0∩t.Wb,z∈s(u,v):=by have:=t.TY hE hn;push Not at this;exact this
   have an (x y:Q2) (hEx:s(x,y)∈t.Ht) (hx:x∈t.B0∩t.Wb):∃g∈j,x=g.c/\y∈g.L:=
    XM ab (Qu hEx) hx ((t.Es hEx).2.2.2.elim (·.2.2) fun ⟨_,_,h1⟩=>(t.TG a8 (i1 hx) h1).elim)
   have⟨z,hz,be⟩:=b3
   exact(sM.mp be).elim (fun h=>by have⟨g,hg,hc,hL⟩:=an z v (h▸hE) hz;exact cR (cL ⟨g,hg,v,hL,h▸hc▸rfl⟩))
    (fun h=>by have⟨g,hg,hc,hL⟩:=an z u (h▸sw▸hE) hz;exact cR (cL ⟨g,hg,u,hL,h▸hc▸sw⟩))
 have b5:∀g∈t.PN++(j++q),∀e∈E' 0∪E' 1,g.c∉e:=fun g hg e he=>
  (Kap hg).elim (fun hA=>t.Te (t.RR g hA) (t.RT he)) fun hB=>
   (Kap hB).elim (fun h0=>t.TA he _ (XG g h0)) (fun h1=>t.Te (t.Mt (XG g h1)) (t.RT he))
 by_cases aj:WS (t.PN++(j++q))<=2
 ·exact t.Tv (t.PN++(j++q)) aj (Xq t.M0 a6) (E' 0) (E' 1) fS fS b5 aa
 · have b7:WS j<=1:=VD;have b6:WS q<=1:=VD
   dsimp only[WS] at aw b7 b6 aj;simp only[LqA,LqS] at aj;have⟨av,a3⟩:=ZV (show 1<=WS j by dsimp only[WS];omega)
   have⟨bd,ak⟩:=ZV (show 1<=WS q by dsimp only[WS];omega)
   have⟨da,cA,ad⟩:=t.J4 (by dsimp only[WS];omega);have ac:bd∈t.Wa:=t.Mt ak
   have ax:E' 0=∅\/E' 1=∅:=by
    by_contra! Pt;have am:∀d:F2,(E' d).Nonempty|0=>Pt.1|1=>Pt.2
    have⟨eA,bb⟩:=am da;have⟨az,ar⟩:=Fp bb;obtain⟨ah,x0,y1,rfl,bf,af⟩:=QZ.mp az;have⟨eB,ba⟩:=am (1-da);have⟨ay,aq⟩:=Fp ba;obtain⟨ag,bn,u0,rfl,ap,a7⟩:=QZ.mp ay;rw[Qd] at a7
    have:=t.Es ah;have:=t.Es ag;have:=ar av a3;have:=aq av a3
    refine Xe (t.a2 (i1 ad) (i2 ad) (i1 af)) (t.a2 (i1 ad) (i2 ad) (i1 ap)) ?_
     (aU (Qu ah)).symm ?_ ?_ ?_ (aU (Qu ag)) ?_ ?_ ?_ ?_
     (t.c2 (i1 a3) (i2 a3) (i2 af)).symm (t.c2 (i1 a3) (i2 a3) (i2 a7)) ?_ ?_
     (t.c2 (i1 a3) (i2 a3) (i1 ak)) ?_ ?_ ?_ ?_
     (t.tA (i1 bf) (i1 ap) ac) (t.tA (i1 a7) (i1 af) ac)<;>grind (splits:=0) [t.MB,t.bw]
   have⟨ite,bg,bj⟩:=t.eO (E0:=E' 0) (E1:=E' 1) fS fS ax
   exact t.F4 ite.c (ite::(t.PN++(j++q))) (by dsimp only[WS];simp[bg];omega)
    (fun e he=>if hm:e∈E' 0∪E' 1 then cH (bj e hm) else cT (aa e he hm)) (Zn rfl (Xq t.M0 a6))
set_option maxHeartbeats 600000 in
lemma T1b.Jv {vb:Q2}(aa:t.Ib={vb})(c5:2<=t.B1.card):Pz t.C:=by
 classical
 have av:=t.J5;have hvb':t.B0∩t.B1={vb}:=t.BI.trans aa;have Pv:vb∈t.B 0:=i1 (aa▸Ss vb);have Pu:vb∈t.B 1:=i2 (aa▸Ss vb);have bl:vb∈t.B0:=i1 (hvb'▸Ss vb);have cf:vb∈t.B1:=i2 (hvb'▸Ss vb);have az {z:Q2} (h0:z∈t.B0) (h1:z∈t.B1):z=vb:=ZK (hvb'▸mi h0 h1);have cb:=(Q1 t.hL.1 t.hb Pv Pu).1;have a7:=(Q1 t.hL.1 t.hb Pv Pu).2
 have ay (gs j:List (SS t.C)) (hs:WS gs+WS j<=3) (hg:∀g∈gs,g.good)
   (hgb:∀g∈gs,∀b∈j,g.c≠b.c) (hbnv:∀b∈j,b.c≠vb)
   (aq:∀b1∈j,∀b2∈j,b1.c=b2.c->b1=b2)
   (ar:∀b1∈j,∀b2∈j,b1.c≠b2.c->(b1.W.biUnion (oi t.C)∩b2.L).card<=1\/(b2.W.biUnion (oi t.C)∩b1.L).card<=1)
   (hA:∀g∈t.PN,g∈gs) (hO:∀u w,s(u,w)∈t.U\t.Hd->u≠vb->w≠vb->C1 (gs++j) s(u,w)):Pz t.C:=
  KW t.hL t.hs t.hrb t.hB0ne Pv Pu (fun _ hw=>Ds (Pr hw)) (t.Jc cb) gs j hs hg hgb hbnv aq ar
   (fun e he=>if hwm:e∈t.Hd then .inr (cL (Pn hA (t.HK e hwm))) else By (hO · ·) (ms he hwm))
 by_cases am:((t.B0\t.B1)∩t.Wb).Nonempty
 · have⟨bh,au⟩:=am;have ax:=s1 (i1 au);have bt:=s2 (i1 au);have bd:=i2 au
   let ic0:=gS t.hL.1 t.hb t.db bh ax bd t.U sR
   have c6:∀u w,s(u,w)∈t.Ht->u≠vb->w≠vb->∃x∈ic0.L,s(u,w)=s(ic0.c,x):=fun u w he huv hwv=>by
    have h4 (x y:Q2) (hxW:x∈t.Wb) (an:y∈t.B1) (hyv:y≠vb) (hxy:Ga x y):x=bh:=by by_contra hn;exact QV (Ne.symm hyv) (Ne.symm hn) (a7 bh bd) (t.c2 ax bd an).symm (a7 x hxW) hxy.symm
    exact(t.Es he).2.2.2.elim (fun ⟨ad,_,af⟩=>by obtain rfl:=h4 u w ad af hwv (aU (Qu he));exact⟨w,mi (ml (Qu he)) af,rfl⟩)
     (fun ⟨ae,_,ag⟩=>by obtain rfl:=h4 w u ae ag huv (aU (Qu he)).symm;exact⟨u,mi (ml (sw▸Qu he)) ag,sw⟩)
   have cl:2<=t.B0.card:=P5 bl ax fun e=>bt (e▸cf);have bz (d:F2):2<=(t.B d).card:=by rcases BJ t.db with h|h<;>fin_cases d<;>simp[T1b.B0,T1b.B1,h] at cl c5 ⊢<;>omega
   rcases Kd t.hL.1 t.hb (aa▸sR) (bz 0) (bz 1) a7 QA
     (fun u w he huv hwv=>⟨X0 (t.PR he).1 (fun h=>huv (ZK (aa▸h))) (fun h=>hwv (ZK (aa▸h))),(t.PR he).2.imp (·.1) (·.1)⟩) with
     ⟨ib,hsB,ap,hcB⟩|⟨c0',c1',hc0',hc1',hW2⟩
   · let ex:List (SS t.C):=if (t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty then [] else [ic0]
     exact ay (ex++(t.PN++ib)) [] (by
       dsimp only[ex,WS] at av hsB ⊢;split_ifs with hBothA;· simp;omega
       have:=t.T4 hBothA;dsimp only[WS] at this;simp[ic0,Q9,Q0];omega)
      (Xq (fun g hg=>by dsimp only[ex] at hg;split_ifs at hg<;>simp_all [ic0,Q9,Q0]) (Xq t.M0 fun g hg=>(ap g hg).1))
      (by simp) (by simp) (by simp) (by simp) (fun _ h=>Kar _ (Kal _ h)) (fun u w h huv hwv=>by
       by_cases a5:s(u,w)∈t.Ub;· exact cL (cR (cR (hcB u w a5 huv hwv)))
       have hE:s(u,w)∈t.Ht:=ms (ms (s1 h) a5) (s2 h)
       by_cases hBothA:(t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty
       ·exact(nE (show s(u,w)∈∅ by rw[←t.MF hBothA.1.choose_spec hBothA.2.choose_spec];exact hE)).elim
       ·exact cL (cL (by dsimp only[ex];simp only[hBothA,↓reduceIte];exact c1 (c6 u w hE huv hwv))))
   · have⟨ib,hsB,ap,ch⟩:=XA (E:=t.U\t.Hd) t.hL.1 t.hb hc0' hc1' hW2 Ds fun u w he=>by
      by_cases a5:s(u,w)∈t.Ub;· exact⟨(t.PR a5).2.imp (·.1) (·.1),(t.PR a5).1⟩
      have hE:s(u,w)∈t.Ht:=ms (ms (s1 he) a5) (s2 he)
      have c3 (x:Q2) (hxW:x∈t.Wb) (hxN:x∉t.Wa):x∈t.B0:=by
       rcases hW2 x hxW with rfl|rfl<;>rcases BJ t.db with hd|hd<;>
        first|simpa[T1b.B0,hd] using s1 (i1 hc0')|simpa[T1b.B0,hd] using s1 (i1 hc1')|exact(hxN (t.bw (by simpa[T1b.B1,hd] using s1 (i1 hc0')) hxW)).elim|exact(hxN (t.bw (by simpa[T1b.B1,hd] using s1 (i1 hc1')) hxW)).elim
      exact(t.Es hE).2.2.2.elim (fun ⟨ad,_,af⟩=>⟨.inl ad,XU ⟨u,c3 u ad (t.Es hE).2.1,.inl rfl⟩ ⟨w,af,.inr rfl⟩⟩)
       (fun ⟨ae,_,ag⟩=>⟨.inr ae,XU ⟨w,c3 w ae (t.Es hE).2.2.1,.inr rfl⟩ ⟨u,ag,.inl rfl⟩⟩)
     exact t.F4 0 (t.PN++ib) (wA av hsB.le)
      (fun e he=>if hwm:e∈t.Hd then cL (t.HK e hwm) else cR (ch e (ms he hwm))) (fun g hg _=>Xq t.M0 ap g hg)
 · rw[not_nonempty_iff_eq_empty] at am
   have bp (z:Q2) (hzv:z≠vb) (a9:z∈t.B0) (hzW:z∈t.Wb):False:=nE (am▸mi (ms a9 fun h1=>hzv (az a9 h1)) hzW)
   obtain⟨ib,hsB,ap,hc1i,hcB⟩:∃ib:List (SS t.C),WS ib<=1/\(∀i∈ib,i.good) /\
     (∀i∈ib,i.c∈t.B1∩t.Wb/\∃z0∈t.B0,z0≠vb/\Ga i.c z0)/\∀u w,s(u,w)∈t.Ub->u≠vb->w≠vb->C1 ib s(u,w):=by
    have c4:∀u w,s(u,w)∈t.Ub->u≠vb->w≠vb->(u∈t.B1∩t.Wb/\w∈t.B0)\/(w∈t.B1∩t.Wb/\u∈t.B0):=fun u w he huv hwv=>by
     rcases Zs t.db (t.PR he).1 (fun h=>huv (ZK (aa▸h))) (fun h=>hwv (ZK (aa▸h))) with⟨ah,af⟩|⟨ag,hw0⟩<;>
      rcases(t.PR he).2 with⟨ad,_⟩|⟨ae,_⟩
     ·exact(bp u huv ah ad).elim
     ·exact .inr ⟨mi af ae,ah⟩
     ·exact .inl ⟨mi ag ad,hw0⟩
     ·exact(bp w hwv hw0 ae).elim
    by_cases aw:∀e∈t.Ub,vb∈e
    ·exact⟨[],by simp[WS],by simp,by simp,fun u w he huv hwv=>(sM.mp (aw _ he)).elim (fun h=>(huv h.symm).elim) (fun h=>(hwv h.symm).elim)⟩
    · push Not at aw;have⟨e0,bf,bb⟩:=aw
      obtain⟨aj,ac,z0,a9,hz0v,be⟩:∃aj∈t.B1∩t.Wb,∃z0∈t.B0,z0≠vb/\Ga aj z0:=by
       induction e0 using Sym2.ind with| _ u w=>
       have huv:u≠vb:=fun h=>bb (sM.mpr (.inl h.symm));have hwv:w≠vb:=fun h=>bb (sM.mpr (.inr h.symm));exact(c4 u w bf huv hwv).elim (fun ⟨h1,h0⟩=>⟨u,h1,w,h0,hwv,aU (QA bf)⟩) (fun ⟨h1,h0⟩=>⟨w,h1,u,h0,huv,(aU (QA bf)).symm⟩)
      have b5:(t.B1∩t.Wb).card<=1:=b1 (P5 bl a9 hz0v.symm) (fun x hx y hy=>t.c2 (i1 hx) (i2 hx) (QE hy));let it:=gS t.hL.1 t.hb (1-t.db) aj (i1 ac) (i2 ac) t.Ub QA;refine⟨[it],by simp[WS,it,Q9,Q0],by simp[it,Q9,Q0],fun _ h=>by simp at h;subst h;exact⟨ac,z0,a9,hz0v,be⟩,fun u w he huv hwv=>?_⟩
      rcases c4 u w he huv hwv with⟨h1,h0⟩|⟨h1,h0⟩
      ·have:=e1 b5 h1 ac;subst this;exact c1 ⟨w,mi (ml he) (QE h0),rfl⟩
      ·have:=e1 b5 h1 ac;subst this;exact c1 ⟨u,mi (ml (sw▸he)) (QE h0),sw⟩
   let a4 (d:F2):=(t.Ed d).filter (vb∉·)
   have cj:∀g∈t.PN++ib,g.c∈t.Wa:=fun g hg=>(Kap hg).elim (t.RR g) fun h=>t.Mt (hc1i g h).1
   have bg (j:List (SS t.C)) (hsum:WS (t.PN++ib)+WS j<=3)
     (b6:∀b∈j,∃x,s(b.c,x)∈a4 0∪a4 1) (aq:∀b1∈j,∀b2∈j,b1.c=b2.c->b1=b2)
     (ar:∀b1∈j,∀b2∈j,b1.c≠b2.c->(b1.W.biUnion (oi t.C)∩b2.L).card<=1\/(b2.W.biUnion (oi t.C)∩b1.L).card<=1)
     (hcovE:Vd j (a4 0∪a4 1)):Pz t.C:=
    ay (t.PN++ib) j hsum (Xq t.M0 ap)
     (fun g hg b hb eq=>by have⟨x,hx⟩:=b6 b hb;exact(t.Es (t.RT hx)).2.1 (eq▸cj g hg))
     (fun b hb hq=>by have⟨x,hx⟩:=b6 b hb;exact t.TA hx (sM.mpr (.inl hq.symm)))
     aq ar (fun _=>Kal _) (fun u w h huv hwv=>
      if a5:s(u,w)∈t.Ub then cL (cR (hcB u w a5 huv hwv)) else
       cR (hcovE _ ((t.eP (ms (ms (s1 h) a5) (s2 h))).elim (fun h'=>u1 (mf h' (sM.not.mpr (not_or.mpr ⟨huv.symm,hwv.symm⟩))))
        (fun h'=>u2 (mf h' (sM.not.mpr (not_or.mpr ⟨huv.symm,hwv.symm⟩)))))))
   by_cases hBothA:(t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty
   · have bv:=t.MF hBothA.1.choose_spec hBothA.2.choose_spec
     exact bg [] (by have:=wA av hsB (k:=3);simp[WS] at this ⊢;exact this) (by simp) (by simp) (by simp) (fun e he=>by have hE:=t.RT he;rw[bv] at hE;exact(nE hE).elim)
   · by_cases b3:WS (t.PN++ib)<=1
     ·have⟨j,d3,b6,aq,ar,cn⟩:=t.eL (E0:=a4 0) (E1:=a4 1) fS fS;exact bg j (by dsimp only[WS] at b3 ⊢;omega) b6 aq ar cn
     · have c9:=t.T4 hBothA;dsimp only[WS] at c9 hsB b3;simp only[LqA,LqS] at b3
       have⟨da,cA,b8⟩:=t.J4 (by dsimp only[WS];omega)
       obtain⟨ic1,cc⟩:∃x,x∈ib:=by cases h:ib with|nil=>simp[h] at b3;omega|cons x _=>exact⟨x,by simp⟩
       have⟨bk,z0,a9,hz0v,be⟩:=hc1i ic1 cc;set aj:=ic1.c;have b4:aj∈t.Wa:=t.Mt bk
       have cd:a4 0=∅\/a4 1=∅:=by
        by_contra! Pt;have bq:∀d:F2,(a4 d).Nonempty|0=>Pt.1|1=>Pt.2
        have⟨eA,cp⟩:=bq da;have⟨cg,cx⟩:=Fp cp;obtain⟨ba,x0,y1,rfl,bm,an⟩:=QZ.mp cg;have⟨eB,ct⟩:=bq (1-da);have⟨ck,cy⟩:=Fp ct;obtain⟨bn,bx,u0,rfl,ak,ah⟩:=QZ.mp ck;rw[Qd] at ah;have cw:z0∉t.B1:=fun h1=>hz0v (az a9 h1)
        have b7 (q w:Q2) (hq:q∈t.B1) (hw:w∈t.Wb):z0=w\/Ga z0 q\/Ga z0 w\/Ga q w:=
         if hzw:z0=w then .inl hzw else .inr (Ka hw ((QR t.hL.1 t.hT t.hs t.hrb t.hno2 _).mpr ⟨.inr ⟨z0,a9,tripleInput_1 ..⟩,⟨q,hq,tripleInput_2 ..⟩⟩))
        have:=t.Es ba;have:=t.Es bn
        refine Xz (a7 x0 (i2 bm)) (a7 bx (i2 ak)) ?_ (a7 aj (i2 bk)) ?_ ?_
         (t.tA (i1 bm) (i1 ak) b4) (aU (Qu ba)) ?_ ?_ ?_ ?_ (aU (Qu bn)) ?_ ?_ ?_ ?_ ?_
         (t.tA (i1 ah) (i1 an) b4) (t.a2 (i1 b8) (i2 b8) (i1 an)).symm (t.a2 (i1 b8) (i2 b8) (i1 ak))
         ?_ ?_ ?_ ?_ be hz0v ?_ ?_ (b7 u0 x0 (i2 ah) (i2 bm)) (b7 y1 bx (i2 an) (i2 ak))<;>grind (splits:=0) [t.MB,t.bw]
       have⟨d7,cs,cu⟩:=t.eO (E0:=a4 0) (E1:=a4 1) fS fS cd;have⟨b1,c7,ca,bs,br,c8⟩:=Ph cs cu;exact bg b1 (by dsimp only[WS] at c7 ⊢;simp;omega) ca bs br c8
end
lemma W8 (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty)(hIa0:N C a 0∩N C a 1=∅)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): Bd C:=by
 classical
 by_cases a8:∃d:F2,(sd C a d).card<=1
 · have⟨da,b8⟩:=a8;have ha:a∈Jk C:=by simp[hs]
   obtain⟨mb,bb,aj,_,_⟩:=QK hL.1 hs hrb hB0ne
   obtain⟨ia,hW,_,bd,hc,_⟩:=Bk (sd C a da) (sd C a (1-da)) V7 (Qe hL.1 ha (1-da)) sR b8 fun u v he=>by
    rcases Qt hL.1 hT hs hab (WN hL hT hs hrb hno2 he) (by simp[hIa0]) (by simp[hIa0]) with⟨h1,h2⟩|⟨h1,h2⟩<;>
     fin_cases da<;>[exact .inl ⟨h1,h2⟩;exact .inr ⟨h2,h1⟩;exact .inr ⟨h2,h1⟩;exact .inl ⟨h1,h2⟩]
   exact Wx hL hs bb aj hbWit QA (fun u v he=>
    ⟨XU (Kr hL hT hs hrb hno2 he).2.1 (Kr hL hT hs hrb hno2 he).2.2.1,(Kr hL hT hs hrb hno2 he).2.2.2⟩) (.inl ⟨ia,by simp[hW],bd,hc⟩)
 push Not at a8;let t:T1b:=⟨C,a,b,db,hL,hT,hs,hab,hrb,hno2,hB0ne,hIa0,hbWit,a8 0,a8 1⟩;have a9:=t.J5
 by_cases al:2<=t.Ib.card
 · have ac:t.Wb.card<=1:=b1 al (fun w hw v hv=>(Q1 hL.1 t.hb (i1 hv) (i2 hv)).2 w hw |>.symm)
   have⟨wb,j⟩:=Qk ac
   have am:=WC (E:=t.U\t.Hd) (c:=wb) fun u v he=>
    if hbm:s(u,v)∈t.Ub then (t.PR hbm).2.elim (fun ⟨h,_⟩=>.inl (j u h)) (fun ⟨h,_⟩=>.inr (j v h))
    else (t.Es (ms (ms (s1 he) hbm) (s2 he))).2.2.2.elim (fun ⟨h,_,_⟩=>.inl (j u h)) (fun ⟨h,_,_⟩=>.inr (j v h))
   obtain⟨ib,hcwb,hW1,hcB⟩:∃ib:SS C,ib.c=wb/\ib.W.card=1/\∀e∈t.U\t.Hd,∃x∈ib.L,e=s(ib.c,x):=by
    by_cases ad:wb∈t.Wa
    · have aa:t.Ht=∅:=eE (sI fun u v he=>(t.Es he).2.2.2.elim (fun ⟨h,_,_⟩=>(t.Es he).2.1 (j u h▸ad)) (fun ⟨h,_,_⟩=>(t.Es he).2.2.1 (j v h▸ad)))
      obtain⟨db',hnd⟩:∃d:F2,wb∈t.Wb->wb∉t.B d:=if h0:wb∈t.B 0 then ⟨1,fun hW h1=>(Q1 hL.1 t.hb h0 h1).1 hW⟩ else ⟨0,fun _=>h0⟩
      refine⟨Q0 C wb (Q4 wb t.Ub) (opnd C b db') (Qe hL.1 t.hb db') (fun x hx=>
        ((t.PR (Pr hx)).1 db').resolve_left (hnd ((t.PR (Pr hx)).2.elim (·.1) fun ⟨h,_⟩=>j x h▸h)))
       (fun _ hx=>QA (Pr hx)) False False.elim,rfl,Cs _,fun e he=>
        if hbm:e∈t.Ub then by obtain⟨x,_,rfl⟩:=am e he;exact⟨x,ml hbm,rfl⟩ else by have hE:e∈t.Ht:=ms (ms (s1 he) hbm) (s2 he);rw[aa] at hE;exact(nE hE).elim⟩
    · have ag:wb∈t.Wb->wb∉t.B1:=fun hW h1=>ad (t.bw h1 hW)
      refine⟨Q0 C wb (Q4 wb (t.U\t.Hd)) (opnd C b (1-db)) (Qe hL.1 t.hb (1-db)) (fun x hx=>
        if hbm:s(wb,x)∈t.Ub then ((t.PR hbm).1 (1-db)).resolve_left (ag ((t.PR hbm).2.elim (·.1) fun ⟨h,_⟩=>j x h▸h))
        else (t.Es (ms (ms (s1 (Pr hx)) hbm) (s2 (Pr hx)))).2.2.2.elim (·.2.2) fun ⟨hxW,_,h1⟩=>(ag (j x hxW▸hxW) h1).elim)
       (fun _ hx=>Ds (Pr hx)) False False.elim,rfl,Cs _,am⟩
   exact t.F4 wb (ib::t.PN) (wC hW1.le a9) (fun e he=>if hm:e∈t.Hd then cT (t.HK e hm) else cH (hcB e (ms he hm))) (Zn hcwb t.M0)
 by_cases b6:t.B1.card<=1
 · have⟨q,hq⟩:=Qk b6
   rcases Eo t.B1 with b7|⟨z1,aw⟩
   · have hB1e':N C b (1-db)=∅:=b7
     exact t.F4 0 t.PN (by omega) (sI fun u v he=>if hm:s(u,v)∈t.Hd then t.HK _ hm else False.elim (
      if hbm:s(u,v)∈t.Ub then by obtain⟨x1,bf,_⟩:=(Kr hL hT hs hrb hno2 hbm).2.2.1;exact nE (hB1e'▸bf)
      else (t.Es (ms (ms he hbm) hm)).2.2.2.elim (fun ⟨_,_,h1⟩=>nE (hB1e'▸h1)) (fun ⟨_,_,h1⟩=>nE (hB1e'▸h1)))) (fun i hi _=>t.M0 i hi)
   have ax:=WC (E:=t.U\t.Hd) (c:=q) fun u v he=>
    if hbm:s(u,v)∈t.Ub then (t.PR hbm).1 (1-db) |>.elim (fun h=>.inl (hq u h)) (fun h=>.inr (hq v h))
    else (t.Es (ms (ms (s1 he) hbm) (s2 he))).2.2.2.elim (fun ⟨_,_,h⟩=>.inr (hq v h)) (fun ⟨_,_,h⟩=>.inl (hq u h))
   have bm:q∈t.B1:=hq z1 aw▸aw
   by_cases b5:q∈t.B0
   · have hq01:q∈t.B 0/\q∈t.B 1:=by fin_cases db<;>exact⟨by assumption,by assumption⟩
     exact KW hL hs hrb hB0ne hq01.1 hq01.2 (fun _ hw=>Ds (Pr hw)) (t.Jc (Q1 hL.1 t.hb hq01.1 hq01.2).1)
      t.PN [] (by simpa only[WS,Lmn,Lsn,add_zero] using le_trans a9 (by decide)) t.M0 (by simp) (by simp) (by simp) (by simp)
      (fun e he=>if hm:e∈t.Hd then .inr (cL (t.HK e hm)) else .inl (ax e (ms he hm)))
   · have⟨da,az⟩:=XC (by simp[sd,hIa0]:q∉sd C a 0∩sd C a 1)
     let bh:SS C:=⟨q,Q4 q (t.U\t.Hd),{opnd C b db,opnd C a da},
      fun z hz=>(Nsp hz).elim (·▸Qe hL.1 t.hb db) fun h=>ZK h▸Qe hL.1 t.ha da,
      fun x hx=>if hbm:s(q,x)∈t.Ub then Mbu ⟨opnd C b db,mem_insert_self _ _,((t.PR hbm).1 db).resolve_left b5⟩
       else Mbu ⟨opnd C a da,mem_insert_of_mem (Ss _),Kg hL.1 hT hs hab da (t.Es (ms (ms (s1 (Pr hx)) hbm) (s2 (Pr hx)))).1 az⟩,
      fun _ hx=>Ds (Pr hx),False,False.elim⟩
     exact t.F4 q (bh::t.PN) (wC (Wj _ _) a9) (fun e he=>if hm:e∈t.Hd then cT (t.HK e hm) else cH (ax e (ms he hm))) (Zn rfl t.M0)
 have ah:2<=t.B1.card:=by omega
 have ar:(t.B0∩t.Wb).card<=1:=b1 ah (fun u hu y hy=>t.c2 (i1 hu) (i2 hu) hy)
 by_cases a3:t.Ib=∅
 · by_cases hBothA:(t.A 0∩t.Wa).Nonempty/\(t.A 1∩t.Wa).Nonempty
   · have aa:=t.MF hBothA.1.choose_spec hBothA.2.choose_spec
     obtain⟨ba,ibs,hsB,hbB,hcB⟩:∃(ba:Q2) (ibs:List (SS C)),WS ibs<=2/\(∀i∈ibs,i.c≠ba->i.good)/\Vd ibs t.Ub:=
      (KJ hL.1 t.hb a3 QA fun u v he=>⟨X0 (t.PR he).1 (t.MY a3) (t.MY a3),(t.PR he).2.imp (·.1) (·.1)⟩).elim
       (fun ⟨ib,ac,_,hcB⟩=>⟨ib.c,[ib],by simp[WS,ac],Zn rfl (by simp),fun e he=>c1 (hcB e he)⟩)
       (fun ⟨ib,hsB,hgB,hcB⟩=>⟨0,ib,hsB,fun i hi _=>hgB i hi,hcB⟩)
     exact t.F4 ba (ibs++t.PN) (wA hsB a9)
      (fun e he=>if hm:e∈t.Ub then cL (hcB e hm) else if hwm:e∈t.Hd then cR (t.HK e hwm) else by have hE:e∈t.Ht:=ms (ms he hm) hwm;rw[aa] at hE;exact(nE hE).elim)
      (BN hbB t.M0)
   by_cases hB01:t.B0.card<=1
   · have⟨cb,a7⟩:=Qk hB01
     by_cases ap:cb∈t.Wb
     · have ay:=t.T4 hBothA;have ae:cb∈t.B0:=by have⟨z,hz⟩:=hB0ne;exact a7 z hz▸hz
       have au:cb∉t.B1:=t.TG a3 ae;let b4:=gS hL.1 t.hb db cb ae ap t.U sR;let E' (d:F2):=(t.Ed d).filter (cb∉·)
       refine t.Tv (b4::t.PN) (wC (Cs _).le ay) (Pj trivial t.M0) (E' 0) (E' 1) fS fS
        (fun g hg e he=>(Kp hg).elim (fun h=>h▸t.TA he) fun be=>t.Te (t.RR g be) (t.RT he))
        (sI fun u v he hn=>if hwm:s(u,v)∈t.Hd then cT (t.HK _ hwm) else
         if hbm:s(u,v)∈t.Ub then (Zs db (t.PR hbm).1 (t.MY a3) (t.MY a3)).elim
          (fun ⟨hu0,Pu⟩=>cH ⟨v,mi (ml (a7 u hu0▸he)) Pu,a7 u hu0▸rfl⟩)
          (fun ⟨hu1,Pv⟩=>cH ⟨u,mi (ml (a7 v Pv▸sw▸he)) hu1,a7 v Pv▸sw⟩)
         else by
          have hE:s(u,v)∈t.Ht:=ms (ms he hbm) hwm;have av (x:Q2) (hEx:s(cb,x)∈t.Ht):x∈t.B1:=(t.Es hEx).2.2.2.elim (·.2.2) fun ⟨_,_,h⟩=>(au h).elim
          exact(sM.mp (not_not.mp (t.TY hE hn))).elim (fun h=>cH ⟨v,mi (ml (h▸he)) (av v (h▸hE)),h▸rfl⟩)
           (fun h=>cH ⟨u,mi (ml (h▸sw▸he)) (av u (h▸sw▸hE)),h▸sw⟩))
     ·exact t.Jp a3 hBothA a7 ap
   ·exact t.Tz a3 hBothA (by omega) ar
 ·have⟨vb,b9⟩:=BU a3 al;exact t.Jv b9 ah
end CompactT2Ia0
section Ia2Compact
open Finset
section Micro
variable {α:Type*} {s t:Finset α} {x y:α} {l m:List α}
lemma Xm (h:∀z,z∉s):s=∅:=Ee.mpr h
lemma BX (h:∀z,z∉s):s.card<=1:=by rw[Xm h,card_empty];omega
lemma YE (h:x∈(∅:Finset α)):False:=N0 h
lemma ZE (h:s⊆t):s.card<=t.card:=Cl h
lemma Ys (h:x∈[y]):x=y:=Kl.mp h
lemma Zq (h:x∈({y}:Finset α)):x=y:=Sp h
lemma WB:x∈({x}:Finset α):=Ss x
lemma BQ:∅⊆s:=empty_subset s
lemma We (h:x∉({y}:Finset α)):x≠y:=notMem_singleton.mp h
lemma Pd (h:x≠y):x∉({y}:Finset α):=Ns h
lemma Bt:({x}:Finset α).card=1:=Cs x
lemma XT {p:α->Prop}[DecidablePred p](h:x∈s.filter p):x∈s/\p x:=Fp h
lemma B2 {p:α->Prop}[DecidablePred p](a:x∈s)(b:p x):x∈s.filter p:=Fk a b
lemma WG {β}[DecidableEq β]{f:α->Finset β}(h:s⊆t):s.biUnion f⊆t.biUnion f:=Bub f h
lemma ZC (h:x∈y::l):x=y\/x∈l:=Kp h
lemma BS (h:x∈l++m):x∈l\/x∈m:=Kap h
lemma XP:x∈x::l:=Kc
lemma XR (h:x∈l):x∈y::l:=Km _ h
lemma Bj:x∈[x]:=Ks _
lemma V6 (h:x∈l):x∈l++m:=Kal _ h
lemma Xs (h:x∈m):x∈l++m:=Kar _ h
variable [DecidableEq α]
lemma Q7 (h:x∈s∩t):x∈s:=(I1 h)
lemma Qb (h:x∈s∩t):x∈t:=(I2 h)
lemma Qm (h:x∈s\t):x∈s:=(D1 h)
lemma YN (h:x∈s\t):x∉t:=(D2 h)
lemma QB (a:x∈s)(b:x∈t):x∈s∩t:=Im a b
lemma QG (a:x∈s)(b:x∉t):x∈s\t:=Dm a b
lemma Z4 (h:x∈s):x∈s∪t:=Ul _ h
lemma X4 (h:x∈t):x∈s∪t:=Ur _ h
lemma Yc (h:x∈s∪t):x∈s\/x∈t:=Up h
lemma Vp {n:ℕ}(h:t.card<=n):(s∩t).card<=n:=(ZE Ir).trans h
lemma Vs (h:x∈insert y s):x=y\/x∈s:=Nsp h
end Micro
lemma YT {E:Finset (Sym2 (Fin 11))}{c x:Fin 11}(h:s(c,x)∈E):x∈Q4 c E:=Zm h
lemma KC {E:Finset (Sym2 (Fin 11))}{c x:Fin 11}(h:x∈Q4 c E):s(c,x)∈E:=Zl h
lemma Y6 {u v:Fin 11}:s(u,v)=s(v,u):=Sw
lemma Bp {u v:Fin 11}(h:s(u,v)∈Us C):Ga u v:=Qh h
lemma Vj {W:Finset ℕ}{L:Finset (Fin 11)}(h:∀z∈W,Oi C z∩L=∅):(W.biUnion (Oi C)∩L).card<=1:=
 BX fun x j=>by have⟨z,q,g⟩:=Bup (Q7 j);exact YE (h z q▸QB g (Qb j))
lemma WT {E:Finset (Sym2 (Fin 11))}(c:Fin 11)(h:∀u v,s(u,v)∈E->u=c\/v=c):E.card<=(Q4 c E).card:=
 (ZE fun e he=>by
  induction e using Sym2.ind with| _ u v=>
  rcases h u v he with rfl|rfl;exact Mi ⟨v,YT he,rfl⟩;exact Mi ⟨u,YT (Y6▸he),Y6⟩).trans Ci
def K1 (l:List (St C)):ℕ:=(l.map fun it=>it.W.card).sum
def Wq (x y:St C):Prop:=
 (x.W.biUnion (Oi C)∩y.L).card<=1\/(y.W.biUnion (Oi C)∩x.L).card<=1
def Zf (l:List (St C)):Prop:=
 (∀x∈l,∀y∈l,x.c=y.c->x=y)/\(∀x∈l,∀y∈l,x.c≠y.c->Wq x y)
def Vn (E:Finset (Sym2 (Fin 11)))(l:List (St C)):Prop:=
 ∀e∈E,∃it∈l,∃x∈it.L,e=s(it.c,x)
lemma Z0 {E:Finset (Sym2 (Fin 11))}{l m:List (St C)}(h:Vn E l)(hs:∀x∈l,x∈m):Vn E m:=fun e he=>by have⟨g,j,x,t,q⟩:=h e he;exact⟨g,hs g j,x,t,q⟩
lemma Vz:Zf ([]:List (St C)):=⟨by simp,by simp⟩
lemma YF (x:St C):Zf [x]:=
 ⟨fun _ h _ g _=>(Ys h).trans (Ys g).symm,fun _ h _ g hn=>(hn (by rw[Ys h,Ys g])).elim⟩
lemma Z2 {x:St C}{l:List (St C)}(hl:Zf l)(Pt:∀y∈l,y.c≠x.c)(h:∀y∈l,Wq x y):Zf (x::l):=
 ⟨fun _ ha _ hb hq=>by
   rcases ZC ha with rfl|ha'<;>rcases ZC hb with rfl|g<;>
    first|rfl|exact(Pt _ g hq.symm).elim|exact(Pt _ ha' hq).elim|exact hl.1 _ ha' _ g hq,
  fun _ ha _ hb hn=>by
   rcases ZC ha with rfl|ha'<;>rcases ZC hb with rfl|g<;>
    first|exact(hn rfl).elim|exact h _ g|exact(h _ ha').symm|exact hl.2 _ ha' _ g hn⟩
structure j2Ctx (C:Ck) where
 hL:Ls C
 hT:Tf C
 a:ℕ
 b:ℕ
 hs:Jk C={a,b}
 hab:Ic C a b
 db:Fin 2
 hrb:O C (opnd C b db) a
 hno2:¬O C (opnd C b (1-db)) a
 hB0ne:(N C b db).Nonempty
 hIa2:2<=(N C a 0∩N C a 1).card
 hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b
 w0:Fin 11
 hw0:∀w∈Mw C a,w=w0
section CtxSec
variable {C:Ck} (k:j2Ctx C)
def j2Ctx.A (d:Fin 2):=N C k.a d
def j2Ctx.Ia:=k.A 0∩k.A 1
def j2Ctx.Ad (d:Fin 2):=k.A d\k.A (1-d)
def j2Ctx.Wa:=Mw C k.a
def j2Ctx.B0:=N C k.b k.db
def j2Ctx.B1:=N C k.b (1-k.db)
def j2Ctx.Ib:=N C k.b 0∩N C k.b 1
def j2Ctx.Wb:=Mw C k.b
def j2Ctx.IC:=k.Ia∩k.B1
def j2Ctx.X:=(k.B0∩k.Wb)∪(k.Ia∩k.Wb)
def j2Ctx.oa (d:Fin 2):=opnd C k.a d
def j2Ctx.T8:=opnd C k.b k.db
def j2Ctx.HS:=opnd C k.b (1-k.db)
def j2Ctx.Ua:=Yx C k.a
def j2Ctx.Ub:=Yu C k.a
def j2Ctx.Eb:=Ya C k.a
def j2Ctx.dA (d:Fin 2):=(k.Ad d∩k.Wb)\k.Wa
def j2Ctx.dB (d:Fin 2):=(k.Ad (1-d)∩k.B1)\k.Wa
abbrev j2Ctx.w1:Prop:=k.w0∈k.B1∩k.Wb
abbrev j2Ctx.wA:Prop:=k.w0∈k.A 0\/k.w0∈k.A 1
def j2Ctx.Ed (d:Fin 2)(S:Finset (Fin 11)):=
 k.Eb.filter fun e=>∃u w:Fin 11,e=s(u,w)/\u∉S/\w∉S/\u∈k.Ad d∩k.Wb/\w∈k.Ad (1-d)∩k.B1/\u∉k.X
def j2Ctx.Pz (_:j2Ctx C):Prop:=
 Bd C
abbrev j2Ctx.R8 (da:Fin 2)(bs:St C):Prop:=
 bs.L.card<=1\/bs.W={k.HS}\/
  (Oi C (k.oa da)∩bs.L=∅/\(k.w1->Oi C k.T8∩bs.L=∅)/\(k.X.Nonempty->Oi C k.HS∩bs.L=∅))
lemma j2Ctx.ha:k.a∈Jk C:=by simp[k.hs]
lemma j2Ctx.hb:k.b∈Jk C:=by simp[k.hs]
lemma j2Ctx.MZ (d:Fin 2):k.oa d < 11+C.gates.length:=Qe k.hL.1 k.ha d
lemma j2Ctx.Jq:k.T8 < 11+C.gates.length:=Qe k.hL.1 k.hb k.db
lemma j2Ctx.MM:k.HS < 11+C.gates.length:=Qe k.hL.1 k.hb (1-k.db)
lemma j2Ctx.PW:k.B1∩k.Wb⊆k.Wa:=K7 k.hL.1 k.hT k.hs k.hrb k.hno2
lemma j2Ctx.hA02:2<=(k.A 0).card:=k.hIa2.trans (ZE Il)
lemma j2Ctx.hA12:2<=(k.A 1).card:=k.hIa2.trans (ZE Ir)
lemma j2Ctx.Rq:1 < k.Ia.card:=by have:2<=k.Ia.card:=k.hIa2;omega
lemma j2Ctx.Tu:k.B0∩k.B1=k.Ib:=by unfold j2Ctx.B0 j2Ctx.B1 j2Ctx.Ib;cases h:k.db using Fin.cases with|zero=>rfl|succ i=>fin_cases i;exact inter_comm _ _
lemma j2Ctx.Rw (h:k.w0∈k.Wa):k.w0∉k.Ia:=fun g=>(Q1 k.hL.1 k.ha (Q7 g) (Qb g)).1 h
lemma j2Ctx.Md (h:k.w0∈k.Wa){z:Fin 11}(g:z∈k.Ia):Ga k.w0 z:=
 ((Q1 k.hL.1 k.ha (Q7 g) (Qb g)).2 k.w0 h).symm
lemma j2Ctx.He (d:Fin 2){u v:Fin 11}(g:Gv C k.a (Pi u v)=true)(h:u∉k.A d):v∈k.A d:=
 Kg k.hL.1 k.hT k.hs k.hab d g h
lemma j2Ctx.HX (d:Fin 2){w v:Fin 11}(g:w∈k.A d)(q:w∈k.Wb)(h:v∈k.A (1-d))(j:v∈k.B1):Ga w v:=
 K9 k.hL.1 k.hT k.hs k.hab k.hrb d g q h j
lemma j2Ctx.Tk:∃d:Fin 2,k.w0∈k.Wa->k.w0∉k.A d:=by
 by_cases h0:k.w0∈k.A 0;exact⟨1,fun hW g=>k.Rw hW (QB h0 g)⟩;exact⟨0,fun _=>h0⟩
lemma j2Ctx.Mg {u v:Fin 11}(he:s(u,v)∈k.Ub): Gv C k.a (Pi u v)=false/\(∃x0∈k.B0,x0=u\/x0=v) /\ (∃x1∈k.B1,x1=u\/x1=v)/\((u∈k.Wb/\Tc C k.b u)\/(v∈k.Wb/\Tc C k.b v)):=
 Kr k.hL k.hT k.hs k.hrb k.hno2 he
lemma j2Ctx.H2 {u v:Fin 11}(he:s(u,v)∈k.Ua): Gv C k.a (Pi u v)=true/\(u∈k.Wa\/v∈k.Wa):=
 Kn k.hL k.hT k.hs k.hrb k.hno2 he
lemma j2Ctx.PM {u v:Fin 11}(he:s(u,v)∈k.Eb): Gv C k.a (Pi u v)=true/\u∉k.Wa/\v∉k.Wa /\ ((u∈k.Wb/\Tc C k.b u/\v∈k.B1)\/(v∈k.Wb/\Tc C k.b v/\u∈k.B1)):=
 Zr k.hL k.hT k.hs k.hrb k.hno2 he
lemma j2Ctx.Rv (d:Fin 2):(k.dA d).card<=1\/(k.dB d).card<=1:=by simpa only[j2Ctx.dA,j2Ctx.dB,j2Ctx.Ad,j2Ctx.A,j2Ctx.Wb,j2Ctx.Wa,j2Ctx.B1,Qd] using VK k.hL.1 k.hT k.hs k.hab k.hrb d
lemma j2Ctx.RB {u w:Fin 11}(h:s(u,w)∈k.Ua): ∃x∈Q4 k.w0 k.Ua,s(u,w)=s(k.w0,x):=by
 rcases(k.H2 h).2 with g|hw
 ·obtain rfl:=k.hw0 u g;exact⟨w,YT h,rfl⟩
 ·obtain rfl:=k.hw0 w hw;exact⟨u,YT (Y6▸h),Y6⟩
lemma KR {p q:Fin 11}(h:p∈k.Ad 0)(g:q∈k.Ad 1):p≠q:=fun e=>YN h (e▸Qm g)
lemma K6 {p z:Fin 11}(j:p∈k.Ad 0\/p∈k.Ad 1)(g:z∈k.Ia):p≠z:=
 fun e=>by subst e;rcases j with h|h;exact YN h (Qb g);exact YN h (Q7 g)
lemma KP {x:Fin 11}(hW:k.w0∈k.Wa)(g:x∉k.Wa):x≠k.w0:=fun e=>g (e▸hW)
lemma YQ {x y:Fin 11}(h:x∉k.Wa)(g:x∈k.B1)(hW:y∈k.Wb):x≠y:=fun e=>h (k.PW (QB g (e▸hW)))
lemma VH {u v:Fin 11}(h:s(u,v)∈k.Eb):Ga u v:=Bp (Qu h)
lemma WD (h:(s:St C).W={w}):s.W.card=1:=by rw[h,Bt]
lemma ZY {p q:Fin 11}(hw0:k.w0∈k.Wa)(h:p∈k.Ad 0)(g:q∈k.Ad 1): Ga p q\/Ga p k.w0\/Ga q k.w0:=
 Ka hw0 ((Qv k.hL.1 k.hT k.hs k.hab _).mpr ⟨⟨p,Qm h,tripleInput_1 ..⟩,⟨q,Qm g,tripleInput_2 ..⟩⟩)
lemma Ye {z q w:Fin 11}(g:z∈k.Ia)(h:q∈k.B1)(hw:w∈k.Wb): Ga z q\/Ga z w\/Ga q w:=
 Ka hw ((QR k.hL.1 k.hT k.hs k.hrb k.hno2 _).mpr
  ⟨.inl ((Qv k.hL.1 k.hT k.hs k.hab _).mpr ⟨⟨z,Q7 g,tripleInput_1 ..⟩,⟨z,Qb g,tripleInput_1 ..⟩⟩),⟨q,h,tripleInput_2 ..⟩⟩)
lemma WY (c:Fin 11)(h:∀u v:Fin 11,s(u,v)∈Us C->u=c\/v=c):k.Pz:=by obtain⟨mb,j,g,_,_⟩:=QK k.hL.1 k.hs k.hrb k.hB0ne;have HZ:=QN k.hL.1 k.hb j g k.hbWit;have h4:=(WT c h).trans (KH (Sr _) c);dsimp only[j2Ctx.Pz];omega
lemma V8 (h:∀u v:Fin 11,s(u,v)∈Us C\k.Ua->u=k.w0\/v=k.w0):k.Pz:=
 WY k k.w0 fun u v he=>by
  by_cases g:s(u,v)∈k.Ua
  ·rcases(k.H2 g).2 with j|hv;exact .inl (k.hw0 u j);exact .inr (k.hw0 v hv)
  ·exact h u v (QG he g)
lemma Wt {v:Fin 11}(a5:v∉k.Wb): ∃L0 Lm:Finset (Fin 11),∃Mb:Finset ℕ, Q4 v (Us C\k.Ua)=L0∪Lm/\L0⊆Q4 v (Us C\k.Ua) /\ L0⊆(W0For G11 C k.b).biUnion (Oi C)/\Lm.card=Mb.card /\ (Us C).card<=(Us C\Lm.image (fun w=>s(v,w))).card+Mb.card /\
   (W0For G11 C k.b).card<=2*(centreless G11 C).card/\Mb.card+1<=(mixing G11 C).card /\
   ∀u w:Fin 11,s(u,w)∈Us C\Lm.image (fun x=>s(v,x))->s(u,w)∉k.Ua->u=v\/w=v->∃x∈L0,s(u,w)=s(v,x):=by
 obtain⟨mb,q,af,_,_⟩:=QK k.hL.1 k.hs k.hrb k.hB0ne
 obtain⟨L0,Lm,Mb,hMb,t,a8,a6,a9,_⟩:=
  QU (L:=Q4 v (Us C\k.Ua)) (W_c:=W0For G11 C k.b)
   (M_cand:=(mixing G11 C).filter fun m=>O C (11+m) k.b) k.hL.1 (Fs _ _)
   (fun _ hw=>Ds (KC hw)) (fun w hw=>by
    have⟨hU,aa⟩:=Dp (KC hw)
    by_cases hb:s(v,w)∈k.Ub
    ·exact((k.Mg hb).2.2.2.resolve_left fun h=>a5 h.1).2
    ·exact((k.PM (QG (QG hU hb) aa)).2.2.2.resolve_left fun h=>a5 h.1).2.1)
 have hU:(Us C).card<=(Us C\Lm.image (fun w=>s(v,w))).card+Mb.card:=by
  set z:=Lm.image (fun w=>s(v,w));have h1:=ZE (show Us C⊆(Us C\z)∪z from fun e he=>by by_cases q:e∈z;exact X4 q;exact Z4 (QG he q))
  have h2:=(Cu (Us C\z) z).trans (A2l Ci _);omega
 have hW:=(Qj (G:=G11) (C:=C) k.b).trans (Qs k.b);have ab:mb∉Mb:=fun h=>by have:=Qy k.hL.1 q k.hb (Fp (hMb h)).2;omega
 have hM:=ZE (Ism ⟨q,hMb.trans (Fs _ _)⟩);rw[Cns ab] at hM;refine⟨L0,Lm,Mb,t,a8,a6,a9,hU,by omega,hM,fun u w ad a4 hv=>?_⟩;have⟨a3,g⟩:=Dp ad
 rcases hv with rfl|rfl
 · have h:=YT (QG a3 a4);rw[t] at h
   rcases Yc h with h0|j;exact⟨w,h0,rfl⟩;exact(g (Mi ⟨w,j,rfl⟩)).elim
 · have h:=YT (QG (Y6▸a3) fun h=>a4 (Y6▸h));rw[t] at h
   rcases Yc h with h0|j;exact⟨u,h0,Y6⟩;exact(g (Mi ⟨u,j,Y6⟩)).elim
lemma BG {v:Fin 11}(af:v∉k.Wb)(PU:∀w∈k.Wb,Ga v w)(t j:List (St C))(a7:K1 t+K1 j<=3)(ag:∀g∈t,g.good)(a9:∀g∈t,∀b∈j,g.c≠b.c)(aj:∀b∈j,b.c≠v)(hok:Zf j)(a5:∀u w:Fin 11,s(u,w)∈Us C->(u≠v/\w≠v)\/s(u,w)∈k.Ua->∃it∈t++j,∃x∈it.L,s(u,w)=s(it.c,x)):k.Pz:=by
 obtain⟨L0,Lm,Mb,_,ac,aa,_,hU,hW,hM,ae⟩:=Wt k af
 let a3:St C:=⟨v,L0,W0For G11 C k.b,Qg k.hL.1 k.b,aa,
  fun _ h=>Ds (KC (ac h)),True,fun _ z hz x h=>PU x (Qc k.hL.1 k.b z hz h)⟩
 have ah:=QS (E:=Us C\Lm.image (fun w=>s(v,w))) k.hL.1 (a3::t) j
  (fun g hg=>by rcases ZC hg with rfl|a4;exact trivial;exact ag g a4)
  (fun e a6=>by
   induction e using Sym2.ind with| _ u w=>
   by_cases hm:s(u,w)∈k.Ua
   ·have⟨it,hi,x,h,q⟩:=a5 u w (Qm a6) (.inr hm);exact⟨it,XR hi,x,h,q⟩
   by_cases hv:u=v\/w=v
   ·have⟨x,h,q⟩:=ae u w a6 hm hv;exact⟨a3,XP,x,h,q⟩
   ·have⟨it,hi,x,h,q⟩:=a5 u w (Qm a6) (.inl (not_or.mp hv));exact⟨it,XR hi,x,h,q⟩)
  (fun g hg b hb=>by rcases ZC hg with rfl|a4;exact(aj b hb).symm;exact a9 g a4 b hb) hok.1 hok.2
 simp only[Lmc,Lsc,a3,K1] at ah a7;dsimp only[j2Ctx.Pz];omega
lemma Vu (j:2<=k.B1.card):k.X.card<=1/\∀c∈k.X,c∈k.Wb/\∀y∈k.B1,Ga c y:=by
 have t:∀c∈k.X,c∈k.Wb/\∀y∈k.B1,Ga c y:=fun c q=>by
  rcases Yc q with h0|g
  ·exact⟨Qb h0,fun y h=>QC k.hL.1 k.hb (Q7 h0) (Qb h0) y h⟩
  ·exact⟨Qb g,fun y h=>YV k.hL.1 k.hT k.hs k.hab k.hrb k.hno2 (Q7 (Q7 g)) (Qb (Q7 g)) (Qb g) y h⟩
 exact⟨Qa Q3 j (fun c q y h=>(t c q).2 y h),t⟩
noncomputable def j2Ctx.Mu (hB12:2<=k.B1.card)(h:k.X.Nonempty):St C:=
 Q0 C h.choose (Q4 h.choose (Us C)∩k.B1) k.HS k.MM
  Ir (fun _ hx=>KC (Q7 hx)) True (fun _ y hy=>((Vu k hB12).2 h.choose h.choose_spec).2 y hy)
noncomputable def j2Ctx.HD (hB12:2<=k.B1.card):List (St C):=
 by classical exact if h:k.X.Nonempty then [k.Mu hB12 h] else []
lemma XJ {j:2<=k.B1.card}{g:St C}(q:g∈k.HD j):∃h:k.X.Nonempty,g=k.Mu j h:=by
 classical unfold j2Ctx.HD at q;split_ifs at q with h;exact⟨h,Ys q⟩;cases q
lemma W5 (h:2<=k.B1.card):∀g∈k.HD h,g.good:=fun _ j=>by obtain⟨_,rfl⟩:=XJ k j;trivial
lemma BC (g:2<=k.B1.card):K1 (k.HD g)=if k.X.Nonempty then 1 else 0:=by
 classical unfold j2Ctx.HD K1;split_ifs<;>simp[j2Ctx.Mu,Q0]
lemma Pf (h:2<=k.B1.card){p q:Fin 11}(j:p∈k.X)(t:q∈k.B1)(he:s(p,q)∈Us C): ∃g∈k.HD h,∃y∈g.L,s(p,q)=s(g.c,y):=by
 classical have hn:k.X.Nonempty:=⟨p,j⟩;have e:=Qp (Vu k h).1 j hn.choose_spec
 exact⟨k.Mu h hn,by unfold j2Ctx.HD;simp[hn],q,QB (YT (e▸he)) t,by simp[j2Ctx.Mu,Q0,e]⟩
lemma Ve {d:Fin 2}{S:Finset (Fin 11)}:k.Ed d S⊆Us C:=(Fs _ _).trans Qu
lemma YS {d:Fin 2}{S:Finset (Fin 11)}{u w:Fin 11}(he:s(u,w)∈k.Ed d S): u∉k.Wa/\w∉k.Wa/\u∉S/\w∉S /\ ((u∈k.Ad d∩k.Wb/\w∈k.Ad (1-d)∩k.B1/\u∉k.X)\/(w∈k.Ad d∩k.Wb/\u∈k.Ad (1-d)∩k.B1/\w∉k.X)):=by
 obtain⟨z,_,_,q,j,h,t,hw,g⟩:=Fp he;have hs:=k.PM z
 rcases Sy2 q with⟨rfl,rfl⟩|⟨rfl,rfl⟩
 ·exact⟨hs.2.1,hs.2.2.1,j,h,.inl ⟨t,hw,g⟩⟩
 ·exact⟨hs.2.1,hs.2.2.1,h,j,.inr ⟨t,hw,g⟩⟩
lemma WJ {S:Finset (Fin 11)}(d:Fin 2):k.Ed d S∪k.Ed (1-d) S=k.Ed 0 S∪k.Ed 1 S:=by
 fin_cases d;rfl;exact union_comm _ _
lemma VS {d:Fin 2}{S:Finset (Fin 11)}(hC:(k.dA d).card<=1)(w:ℕ)(hw:w < 11+C.gates.length)(q:k.dB d⊆Oi C w): ∃j:St C,j.W={w}/\j.L⊆k.dB d/\((k.Ed d S).Nonempty->j.c∈k.dA d/\∃x,s(j.c,x)∈k.Ed d S) /\ ∀e∈k.Ed d S,∃x∈j.L,e=s(j.c,x):=by
 have⟨t,g⟩:=Qk hC
 refine⟨Q0 C t (Q4 t (k.Ed d S)∩k.dB d) w hw (Ir.trans q)
  (fun _ z=>Ve k (KC (Q7 z))) False False.elim,rfl,Ir,fun ⟨e,he⟩=>by
   induction e using Sym2.ind with| _ u v=>
   obtain⟨huW,hvW,_,_,⟨hu,_,_⟩|⟨hv,_,_⟩⟩:=YS k he
   ·have h:=g u (QG hu huW);exact⟨h▸QG hu huW,v,h▸he⟩
   ·have h:=g v (QG hv hvW);exact⟨h▸QG hv hvW,u,h▸Y6▸he⟩,
  Z6 fun u v he=>by
   obtain⟨huW,hvW,_,_,⟨hu,hv,_⟩|⟨hv,hu,_⟩⟩:=YS k he
   ·have h:=g u (QG hu huW);exact .inl ⟨h,QB (YT (h▸he)) (QG hv hvW)⟩
   ·have h:=g v (QG hv hvW);exact .inr ⟨h,QB (YT (h▸Y6▸he)) (QG hu huW)⟩⟩
lemma Bq {d:Fin 2}{S:Finset (Fin 11)}(z:(k.dB d).card<=1): ∃j:St C,j.W={k.oa d}/\j.L⊆k.dA d\k.X/\(∀x∈j.L,s(j.c,x)∈k.Ed d S) /\ ((k.Ed d S).Nonempty->j.c∈k.dB d/\∃x,s(j.c,x)∈k.Ed d S)/\∀e∈k.Ed d S,∃x∈j.L,e=s(j.c,x):=by
 have⟨t,g⟩:=Qk z
 refine⟨Q0 C t (Q4 t (k.Ed d S)∩(k.dA d\k.X)) (k.oa d) (k.MZ d)
  (fun _ q=>Qm (Q7 (Qm (Qm (Qb q))))) (fun _ q=>Ve k (KC (Q7 q))) False False.elim,
  rfl,Ir,fun _ q=>KC (Q7 q),fun ⟨e,he⟩=>by
   induction e using Sym2.ind with| _ u v=>
   obtain⟨huW,hvW,_,_,⟨_,hv,_⟩|⟨_,hu,_⟩⟩:=YS k he
   ·have h:=g v (QG hv hvW);exact⟨h▸QG hv hvW,u,h▸Y6▸he⟩
   ·have h:=g u (QG hu huW);exact⟨h▸QG hu huW,v,h▸he⟩,
  Z6 fun u v he=>by
   obtain⟨huW,hvW,_,_,⟨hu,hv,huX⟩|⟨hv,hu,hvX⟩⟩:=YS k he
   ·have h:=g v (QG hv hvW);exact .inr ⟨h,QB (YT (h▸Y6▸he)) (QG (QG hu huW) huX)⟩
   ·have h:=g u (QG hu huW);exact .inl ⟨h,QB (YT (h▸he)) (QG (QG hv hvW) hvX)⟩⟩
lemma BD (d:Fin 2){L:Finset (Fin 11)}(hL:L⊆k.dA d\k.X): Oi C (k.oa (1-d))∩L=∅/\Oi C k.T8∩L=∅/\Oi C k.HS∩L=∅:=
 ⟨Xm fun _ g=>YN (Q7 (Qm (Qm (hL (Qb g))))) (Q7 g),
  Xm fun _ g=>YN (hL (Qb g)) (Z4 (QB (Q7 g) (Qb (Qm (Qm (hL (Qb g))))))),
  Xm fun _ g=>YN (Qm (hL (Qb g))) (k.PW (QB (Q7 g) (Qb (Qm (Qm (hL (Qb g)))))))⟩
structure j2BcPack (k:j2Ctx C) (S:Finset (Fin 11)) where
 da:Fin 2
 bcl:List (St C)
 endp:∀bs∈bcl,∃x,s(bs.c,x)∈k.Ed 0 S∪k.Ed 1 S
 ok:Zf bcl
 cov:Vn (k.Ed 0 S∪k.Ed 1 S) bcl
 disj:∀bs∈bcl,k.R8 da bs
lemma VQ {S:Finset (Fin 11)}(d da:Fin 2)(j0 j1:St C)(a7:(k.Ed d S).Nonempty->∃x,s(j0.c,x)∈k.Ed d S)(a3:(k.Ed (1-d) S).Nonempty->∃x,s(j1.c,x)∈k.Ed (1-d) S)(Pt:(k.Ed d S).Nonempty->(k.Ed (1-d) S).Nonempty->j0.c≠j1.c)(aa:∀e∈k.Ed d S,∃x∈j0.L,e=s(j0.c,x))(a5:∀e∈k.Ed (1-d) S,∃x∈j1.L,e=s(j1.c,x))(hd01:Wq j0 j1)(ab:k.R8 da j0)(a6:k.R8 da j1): ∃p:j2BcPack k S,p.da=da/\K1 p.bcl<=j0.W.card+j1.W.card/\∀b∈p.bcl,b=j0\/b=j1:=by
 classical
 set E0:=k.Ed d S;set E1:=k.Ed (1-d) S;have hEq:E0∪E1=k.Ed 0 S∪k.Ed 1 S:=WJ k (S:=S) d;let bcl:=(if E0.Nonempty then [j0] else [])++(if E1.Nonempty then [j1] else [])
 have g {z:St C} (hz:z∈bcl):(E0.Nonempty/\z=j0)\/(E1.Nonempty/\z=j1):=by
  rcases BS hz with h|h<;>split_ifs at h with h'
  ·exact .inl ⟨h',Ys h⟩
  ·cases h
  ·exact .inr ⟨h',Ys h⟩
  ·cases h
 refine⟨⟨da,bcl,fun b hb=>?_,
   ⟨fun _ ha _ hb q=>by
     rcases g ha with⟨a4,rfl⟩|⟨a8,rfl⟩<;>rcases g hb with⟨ac,rfl⟩|⟨a9,rfl⟩
     ·rfl
     ·exact(Pt a4 a9 q).elim
     ·exact(Pt ac a8 q.symm).elim
     ·rfl,
    fun _ ha _ hb hn=>by
     rcases g ha with⟨_,rfl⟩|⟨_,rfl⟩<;>rcases g hb with⟨_,rfl⟩|⟨_,rfl⟩
     ·exact(hn rfl).elim
     ·exact hd01
     ·exact hd01.symm
     ·exact(hn rfl).elim⟩,
   fun e he=>by
    rcases Yc (hEq.symm▸he) with h0|t
    ·have h':E0.Nonempty:=⟨_,h0⟩;have⟨x,j,q⟩:=aa _ h0;exact⟨j0,V6 (by simp[h']),x,j,q⟩
    ·have h':E1.Nonempty:=⟨_,t⟩;have⟨x,j,q⟩:=a5 _ t;exact⟨j1,Xs (by simp[h']),x,j,q⟩,
   fun b hb=>by rcases g hb with⟨_,rfl⟩|⟨_,rfl⟩;exact ab;exact a6⟩,
  rfl,by simp only[bcl,K1,LqA,LqS];split_ifs<;>simp,
  fun b hb=>by rcases g hb with⟨_,rfl⟩|⟨_,rfl⟩;exact .inl rfl;exact .inr rfl⟩
 rcases g hb with⟨h0,rfl⟩|⟨t,rfl⟩
 ·have⟨x,j⟩:=a7 h0;exact⟨x,hEq▸Z4 j⟩
 ·have⟨x,j⟩:=a3 t;exact⟨x,hEq▸X4 j⟩
lemma ZX {S:Finset (Fin 11)}(d:Fin 2)(hO:k.Ed (1-d) S=∅): ∃p:j2BcPack k S,K1 p.bcl<=if (k.Ed d S).Nonempty then 1 else 0:=by
 classical
 have hEq:k.Ed 0 S∪k.Ed 1 S=k.Ed d S:=by rw[←WJ k d,hO,union_empty]
 rcases Eo (k.Ed d S) with h|Pt
 ·exact⟨⟨0,[],by simp,Vz,fun e he=>by rw[hEq,h] at he;exact(YE he).elim,by simp⟩,by simp[K1,h]⟩
 · rcases k.Rv d with hA|hB
   · obtain⟨j,hW,_,t,hc⟩:=VS k hA k.HS k.MM (fun _ g=>Qb (Qm g))
     exact⟨⟨0,[j],fun z hb=>by obtain rfl:=Ys hb;obtain⟨x,g⟩:=(t Pt).2;exact⟨x,hEq.symm▸g⟩,
      YF j,fun e he=>by have⟨x,g,q⟩:=hc e (hEq▸he);exact⟨j,Bj,x,g,q⟩,
      fun z hb=>by obtain rfl:=Ys hb;exact .inr (.inl hW)⟩,by simp[K1,Pt,hW]⟩
   · obtain⟨j,hW,a4,_,t,hc⟩:=Bq k hB;have hd:=BD k d a4
     exact⟨⟨1-d,[j],fun z hb=>by obtain rfl:=Ys hb;obtain⟨x,g⟩:=(t Pt).2;exact⟨x,hEq.symm▸g⟩,
      YF j,fun e he=>by have⟨x,g,q⟩:=hc e (hEq▸he);exact⟨j,Bj,x,g,q⟩,
      fun z hb=>by obtain rfl:=Ys hb;exact .inr (.inr ⟨hd.1,fun _=>hd.2.1,fun _=>hd.2.2⟩)⟩,by simp[K1,Pt,hW]⟩
lemma Zy (aa:2<=k.B1.card){S:Finset (Fin 11)}(b3:k.IC⊆S)(aq:k.Ib⊆S)(j:List (St C))(av:∀x∈Q4 k.w0 k.Ua,∃it∈j,∃y∈it.L,s(k.w0,x)=s(it.c,y))(az:∀g∈k.HD aa,∀x∈g.L,∃it∈j,∃y∈it.L,s(g.c,x)=s(it.c,y))(ab:k.w1->∀x∈Q4 k.w0 k.Ub∩k.B0,∃it∈j,∃y∈it.L,s(k.w0,x)=s(it.c,y))(ae:Vn (k.Ed 0 S∪k.Ed 1 S) j){u w:Fin 11}(he:s(u,w)∈Us C)(hor:(u∉S/\w∉S)\/s(u,w)∈k.Ua): ∃it∈j,∃x∈it.L,s(u,w)=s(it.c,x):=by
 have hC (p q:Fin 11) (hp:p∈k.X) (hq:q∈k.B1) (hpq:s(p,q)∈Us C):
   ∃it∈j,∃z∈it.L,s(p,q)=s(it.c,z):=by
  have⟨g,hg,y,hy,q1⟩:=Pf k aa hp hq hpq;have⟨it,t,z,hz,q2⟩:=az g hg y hy;exact⟨it,t,z,hz,q1.trans q2⟩
 by_cases ac:s(u,w)∈k.Ua
 ·have⟨x,hx,q⟩:=k.RB ac;have⟨it,t,y,hy,q'⟩:=av x hx;exact⟨it,t,y,hy,q.trans q'⟩
 have⟨ah,af⟩:=hor.resolve_right ac
 by_cases a8:s(u,w)∈k.Ub
 · have hsp:=k.Mg a8;have hs:=Yt hsp.2.1 hsp.2.2.1 (fun h=>ah (aq h)) (fun h=>af (aq h))
   have hs':(u∈k.B0/\w∈k.B1)\/(u∈k.B1/\w∈k.B0):=by unfold j2Ctx.B0 j2Ctx.B1;cases h:k.db using Fin.cases with|zero=>exact hs|succ i=>fin_cases i;exact hs.symm
   rcases hs' with⟨au,a3⟩|⟨a4,hw0⟩<;>rcases hsp.2.2.2 with⟨a5,_⟩|⟨a6,_⟩
   ·exact hC u w (Z4 (QB au a5)) a3 he
   · obtain rfl:=k.hw0 w (k.PW (QB a3 a6))
     have⟨it,t,y,hy,q⟩:=ab (QB a3 a6) u (QB (YT (Y6▸a8)) au);exact⟨it,t,y,hy,Y6.trans q⟩
   ·obtain rfl:=k.hw0 u (k.PW (QB a4 a5));exact ab (QB a4 a5) w (QB (YT a8) hw0)
   ·have⟨it,t,y,hy,q⟩:=hC w u (Z4 (QB hw0 a6)) a4 (Y6▸he);exact⟨it,t,y,hy,Y6.trans q⟩
 · have ag:s(u,w)∈k.Eb:=QG (QG he a8) ac;obtain⟨ar,_,_,ay⟩:=k.PM ag
   have al (p q:Fin 11) (he':s(p,q)∈k.Eb) (hga':Gv C k.a (Pi p q)=true)
     (hpS:p∉S) (hqS:q∉S) (hpW:p∈k.Wb) (hq1:q∈k.B1):
     ∃it∈j,∃x∈it.L,s(p,q)=s(it.c,x):=by
    by_cases a9:p∈k.X;exact hC p q a9 hq1 (Qu he')
    have ak:p∉k.Ia:=fun h=>a9 (X4 (QB h hpW));have aj:q∉k.Ia:=fun h=>hqS (b3 (QB h hq1))
    rcases Qt k.hL.1 k.hT k.hs k.hab hga' ak aj with⟨am,ad⟩|⟨an,ap⟩
    ·exact ae _ (Z4 (B2 he' ⟨p,q,rfl,hpS,hqS,QB (QG am fun h=>ak (QB am h)) hpW,QB (QG ad fun h=>aj (QB h ad)) hq1,a9⟩))
    ·exact ae _ (X4 (B2 he' ⟨p,q,rfl,hpS,hqS,QB (QG an fun h=>ak (QB h an)) hpW,QB (QG ap fun h=>aj (QB ap h)) hq1,a9⟩))
   rcases ay with⟨a5,_,a3⟩|⟨a6,_,a4⟩
   ·exact al u w ag ar ah af a5 a3
   ·have⟨it,t,x,hx,q⟩:=al w u (Y6▸ag) (Zg u w▸ar) af ah a6 a4;exact⟨it,t,x,hx,Y6.trans q⟩
set_option maxHeartbeats 600000 in
lemma WK (q:2<=k.B1.card){S:Finset (Fin 11)}(ba:S.card<=1)(a9:k.IC⊆S)(ab:k.Ib⊆S)(b7:∀s∈S,s∉k.Wb)(b9:k.w0∈k.Wa->¬k.wA->k.w0∉S){m:ℕ}(bx:3<=m)(ad:∀gs bs:List (St C),K1 gs+K1 bs<=m -> (∀g∈gs,g.good)->(∀g∈gs,∀b∈bs,g.c≠b.c)->(∀b∈bs,b.c∉S)->Zf bs -> (∀u w:Fin 11,s(u,w)∈Us C->(u∉S/\w∉S)\/s(u,w)∈k.Ua->∃it∈gs++bs,∃x∈it.L,s(u,w)=s(it.c,x))->k.Pz)(bl:k.w0∈k.Wa->∃p:j2BcPack k S,(if k.X.Nonempty then 1 else 0)+(if k.w1 then 2 else 1)+K1 p.bcl<=m):k.Pz:=by
 classical
 obtain⟨_,b6⟩:=Vu k q;have ac:=BC k q
 have ap:∀g∈k.HD q,g.c∉k.B1:=fun g hg t=>by
  obtain⟨h,rfl⟩:=XJ k hg;have ag:=h.choose_spec;have au:h.choose∉S:=fun hS=>b7 _ hS (b6 _ ag).1
  rcases Yc ag with h0|bb;exact au (ab (k.Tu▸QB (Q7 h0) t));exact au (a9 (QB (Q7 bb) t))
 have a6:∀g∈k.HD q,∀u w:Fin 11,s(u,w)∈k.Ed 0 S∪k.Ed 1 S->g.c≠u/\g.c≠w:=fun g hg u w he=>by
  have aa:=ap g hg;obtain⟨h,rfl⟩:=XJ k hg;have ag:=h.choose_spec
  rcases Yc he with h'|h'<;>rcases(YS k h').2.2.2.2 with⟨_,hw,bk⟩|⟨_,hu,bp⟩<;>
   first|exact⟨fun e=>bk (e▸ag),fun e=>aa (e▸Qb hw)⟩|exact⟨fun e=>aa (e▸Qb hu),fun e=>bp (e▸ag)⟩
 by_cases hW:k.w0∈k.Wa
 · have⟨p,am⟩:=bl hW
   have aw:∀b∈p.bcl,b.c∉S:=fun b hb=>by have⟨x,j⟩:=p.endp b hb;rcases Yc j with h|h<;>exact(YS k h).2.2.1
   have ae:∀b∈p.bcl,b.c≠k.w0:=fun b hb eq=>by have⟨x,j⟩:=p.endp b hb;rcases Yc j with h|h<;>exact(YS k h).1 (eq▸hW)
   by_cases an:k.wA
   · obtain⟨da',h1d,a8⟩:∃d:Fin 2,k.w0∈k.A (1-d)/\k.w0∉k.A d:=by
      rcases an with h0|t;exact⟨1,h0,fun t=>k.Rw hW (QB h0 t)⟩;exact⟨0,t,fun h0=>k.Rw hW (QB h0 t)⟩
     let ia:=Q9 k.hL.1 k.ha (1-da') k.w0 h1d hW k.Ua K0;let aj (h:k.w1):=Q9 k.hL.1 k.hb (1-k.db) k.w0 (Q7 h) (Qb h) k.Ub QA;let ib:List (St C):=if h:k.w1 then [aj h] else []
     have bn:K1 (ia::(k.HD q++ib))+K1 p.bcl<=m:=by
      simp only[K1,Lmc,Lsc,LqA,LqS] at ac am ⊢;have t:ia.W.card=1:=by simp[ia,Q9,Q0]
      have h2:(ib.map fun it=>it.W.card).sum=if k.w1 then 1 else 0:=by dsimp only[ib];split_ifs<;>simp[aj,Q9,Q0]
      split_ifs at am h2 ac<;>omega
     exact ad (ia::(k.HD q++ib)) p.bcl bn
      (fun g hg=>by rcases ZC hg with rfl|t;exact trivial;rcases BS t with h2|h2;exact W5 k q g h2;dsimp only[ib] at h2;split_ifs at h2;obtain rfl:=Ys h2;trivial;cases h2)
      (fun g hg b hb=>by
       rcases ZC hg with rfl|t;exact(ae b hb).symm
       rcases BS t with h2|h2;have⟨x,j⟩:=p.endp b hb;exact(a6 g h2 b.c x j).1
       dsimp only[ib] at h2;split_ifs at h2;obtain rfl:=Ys h2;exact(ae b hb).symm;cases h2)
      aw p.ok (fun _ _ he a7=>Zy k q a9 ab _
       (fun x j=>⟨ia,V6 XP,x,QB j (by rw[Qd];exact k.He da' (k.H2 (KC j)).1 a8),rfl⟩)
       (fun g hg x j=>⟨g,V6 (XR (V6 hg)),x,j,rfl⟩)
       (fun t x j=>⟨aj t,V6 (XR (Xs (by simp[ib,t]))),x,QB (Q7 j) (by rw[Qd];exact Qb j),rfl⟩)
       (Z0 p.cov fun _=>Xs) he a7)
   · have a8 (d:Fin 2):k.w0∉k.A d:=fun h=>by fin_cases d<;>[exact an (.inl h);exact an (.inr h)]
     let Ww:Finset ℕ:=if k.w1 then {k.oa p.da,k.T8} else {k.oa p.da};let Lb:Finset (Fin 11):=if k.w1 then Q4 k.w0 k.Ub∩k.B0 else ∅
     let itw:St C:=⟨k.w0,Q4 k.w0 k.Ua∪Lb,Ww,
      fun z hz=>by
       dsimp only[Ww] at hz;split_ifs at hz
       ·rcases Vs hz with rfl|h;exact k.MZ p.da;rw[Zq h];exact k.Jq
       ·rw[Zq hz];exact k.MZ p.da,
      fun x j=>by
       rcases Yc j with t|h2
       ·exact Mbu ⟨k.oa p.da,by dsimp only[Ww];split_ifs<;>simp,k.He p.da (k.H2 (KC t)).1 (a8 p.da)⟩
       ·dsimp only[Lb] at h2;split_ifs at h2 with t;exact Mbu ⟨k.T8,by simp[Ww,t],Qb h2⟩;exact(YE h2).elim,
      fun x j=>by
       rcases Yc j with t|h2;exact K0 (KC t)
       dsimp only[Lb] at h2;split_ifs at h2;exact QA (KC (Q7 h2));exact(YE h2).elim,False,False.elim⟩
     have bu:itw.W.card<=if k.w1 then 2 else 1:=by dsimp only[itw,Ww];split_ifs;exact Cil _ _;simp
     have b4:k.w0∉S:=b9 hW an
     by_cases ax:∃g∈k.HD q,g.c=k.w0
     · have⟨g,hg,hgc⟩:=ax;obtain⟨hX,rfl⟩:=XJ k hg
       have aa:¬k.w1:=fun t=>ap _ hg (hgc.symm▸Q7 t)
       let itm:St C:=⟨k.w0,itw.L∪(k.Mu q hX).L,{k.oa p.da,k.HS},
        fun z hz=>by rcases Vs hz with rfl|h;exact k.MZ p.da;rw[Zq h];exact k.MM,
        fun x j=>by
         rcases Yc j with t|h2
         ·exact WG (by dsimp only[itw,Ww];simp only[aa,↓reduceIte];exact insert_subset_insert _ BQ) (itw.hL t)
         ·exact WG (fun _ hz=>mem_insert_of_mem hz) ((k.Mu q hX).hL h2),
        fun x j=>by rcases Yc j with t|h2;exact itw.he x t;exact hgc▸(k.Mu q hX).he x h2,False,False.elim⟩
       have bv:itm.W.card<=2:=Cil _ _
       exact ad [] (itm::p.bcl)
        (by simp only[K1,Lmn,Lsn,Lmc,Lsc,hX,aa,↓reduceIte] at am ⊢;omega)
        (by simp) (by simp) (fun b hb=>by rcases ZC hb with rfl|af;exact b4;exact aw b af)
        (Z2 p.ok ae fun b hb=>by
         rcases p.disj b hb with ar|ah|⟨hA,_,bf⟩
         ·exact .inl (Vp ar)
         · have hs:b.L⊆univ.filter (fun y=>G11.Adj k.w0 y/\G11.Adj b.c y):=fun y hy=>by
            have bd:y∈k.B1:=by have:=b.hL hy;rwa[ah,Sbu] at this
            exact B2 (Uv _) ⟨hgc▸(b6 hX.choose hX.choose_spec).2 y bd,Bp (b.he y hy)⟩
           exact .inl (Vp ((ZE hs).trans (Q3 k.w0 b.c (ae b hb).symm)))
         ·exact .inl (Vj fun z hz=>by rcases Vs hz with rfl|aq;exact hA;rw[Zq aq];exact bf hX))
        (fun _ _ he a7=>Zy k q a9 ab _ (fun x j=>⟨itm,XP,x,Z4 (Z4 j),rfl⟩)
         (fun g' bj x j=>by obtain⟨_,rfl⟩:=XJ k bj;exact⟨itm,XP,x,X4 j,by rw[hgc]⟩)
         (fun t=>(aa t).elim) (Z0 p.cov fun _=>XR) he a7)
     · push Not at ax
       have b8:(Oi C k.HS∩itw.L).card<=1:=by
        refine(ZE (show Oi C k.HS∩itw.L⊆S from fun x j=>?_)).trans ba
        rcases Yc (Qb j) with t|h2
        ·have b5:=(k.H2 (KC t)).1;exact a9 (QB (QB (k.He 0 b5 (a8 0)) (k.He 1 b5 (a8 1))) (Q7 j))
        ·dsimp only[Lb] at h2;split_ifs at h2;exact ab (k.Tu▸QB (Qb h2) (Q7 j));exact(YE h2).elim
       exact ad (k.HD q) (itw::p.bcl) (by simp only[K1,Lmc,Lsc] at ac am ⊢;omega) (W5 k q)
        (fun g hg b hb=>by rcases ZC hb with rfl|af;exact ax g hg;have⟨x,j⟩:=p.endp b af;exact(a6 g hg b.c x j).1)
        (fun b hb=>by rcases ZC hb with rfl|af;exact b4;exact aw b af)
        (Z2 p.ok ae fun b hb=>by
         rcases p.disj b hb with ar|ah|⟨hA,bh,_⟩
         ·exact .inl (Vp ar)
         ·right;rw[ah,Sbu];exact b8
         · exact .inl (Vj fun z hz=>by
            dsimp only[itw,Ww] at hz;split_ifs at hz with t
            ·rcases Vs hz with rfl|aq;exact hA;rw[Zq aq];exact bh t
            ·rw[Zq hz];exact hA))
        (fun _ _ he a7=>Zy k q a9 ab _ (fun x j=>⟨itw,Xs XP,x,Z4 j,rfl⟩) (fun g hg x j=>⟨g,V6 hg,x,j,rfl⟩)
         (fun t x j=>⟨itw,Xs XP,x,X4 (by simp[Lb,t,j]),rfl⟩) (Z0 p.cov fun _ h=>Xs (XR h)) he a7)
 · have az (d:Fin 2) u w (h:s(u,w)∈k.Ed d S):
     u∉k.Wa/\w∉k.Wa/\((u∈k.Ad d∩k.Wb/\w∈k.Ad (1-d)∩k.B1)\/(w∈k.Ad d∩k.Wb/\u∈k.Ad (1-d)∩k.B1)):=
    let s:=YS k h;⟨s.1,s.2.1,by rcases s.2.2.2.2 with⟨hu,hw,_⟩|⟨hw,hu,_⟩;exact .inl ⟨hu,hw⟩;exact .inr ⟨hw,hu⟩⟩
   have⟨bs,bt,b3,a8,bm,bq⟩:=Yy k.hL.1 k.hT k.hs k.hab k.hrb k.hno2 k.hA02 k.hA12 (Ve k) (Ve k) (az 0) (az 1)
   exact ad (k.HD q) bs (by rw[ac];dsimp only[K1];split_ifs<;>omega) (W5 k q)
    (fun g hg b hb=>by have⟨x,j⟩:=b3 b hb;exact(a6 g hg b.c x j).1)
    (fun b hb=>by have⟨x,j⟩:=b3 b hb;rcases Yc j with h|h<;>exact(YS k h).2.2.1)
    ⟨a8,bm⟩ (fun _ _ he a7=>Zy k q a9 ab _
     (fun x j=>(hW (by rcases(k.H2 (KC j)).2 with h|h;exact h;exact k.hw0 x h▸h)).elim)
     (fun g hg x j=>⟨g,V6 hg,x,j,rfl⟩) (fun t=>(hW (k.PW t)).elim) (Z0 bq fun _=>Xs) he a7)
lemma BE {x0 x1:Fin 11}(hw:k.w0∈k.Wa){Y2 Y3:Finset (Fin 11)}(h2:2<=Y2.card)(h3:2<=Y3.card)(hx:x1≠x0)(a8:∀y∈Y2,Ga x0 y)(a9:∀y∈Y3,Ga x1 y)(j:∀y∈Y2,y≠x1/\y≠k.w0/\∀v∈k.Ia,v≠y)(g:∀y∈Y3,y≠x0/\y≠k.w0/\(∀y2∈Y2,y≠y2)/\∀v∈k.Ia,v≠y)(a4:∀v∈k.Ia,v≠x0/\v≠x1)(a7:∀y2∈Y2,∀y3∈Y3,Ga y3 y2\/Ga y3 k.w0\/Ga y2 k.w0)(a5:∀v∈k.Ia,∀y3∈Y3,Ga v y3\/Ga v x0\/Ga y3 x0)(a6:∀v∈k.Ia,∀y2∈Y2,Ga v y2\/Ga v x1\/Ga y2 x1):False:=by
 have hS {T:Finset (Fin 11)} (hT:2<=T.card):∃p∈T,∃q∈T,p < q:=by
  have⟨p,hp,q,hq,hn⟩:=one_lt_card.mp (by omega:1 < T.card)
  rcases lt_or_gt_of_ne hn with h|h;exact⟨p,hp,q,hq,h⟩;exact⟨q,hq,p,hp,h⟩
 have⟨a,ha,b,hb,hab⟩:=hS h2;have⟨c,hc,d,z,ab⟩:=hS h3;have⟨u,t,v,hv,aa⟩:=hS k.hIa2
 exact Xj (a8 a ha) (a8 b hb) hab hx (j a ha).1.symm (j b hb).1.symm
  (a9 c hc) (g c hc).1 ((g c hc).2.2.1 a ha) ((g c hc).2.2.1 b hb)
  (a9 d z) ab (g d z).1 ((g d z).2.2.1 a ha) ((g d z).2.2.1 b hb)
  (j a ha).2.1.symm (j b hb).2.1.symm (g c hc).2.1.symm (g d z).2.1.symm
  (a7 a ha c hc) (a7 b hb c hc) (a7 a ha d z) (a7 b hb d z)
  (k.Md hw t) (a4 u t).1 (a4 u t).2 ((j a ha).2.2 u t) ((j b hb).2.2 u t) ((g c hc).2.2.2 u t) ((g d z).2.2.2 u t)
  (a5 u t c hc) (a5 u t d z) (a6 u t a ha) (a6 u t b hb)
  (k.Md hw hv) aa (a4 v hv).1 (a4 v hv).2 ((j a ha).2.2 v hv) ((j b hb).2.2 v hv) ((g c hc).2.2.2 v hv) ((g d z).2.2.2 v hv)
  (a5 v hv c hc) (a5 v hv d z) (a6 v hv a ha) (a6 v hv b hb)
lemma Wn (ab:2<=k.B1.card)(ap:k.IC=∅){vb:Fin 11}(aj:k.Ib={vb}):k.Pz:=by
 classical
 have az:vb∈N C k.b 0:=Q7 (aj▸WB);have b3:vb∈N C k.b 1:=Qb (aj▸WB);have c3:vb∈k.B1:=by unfold j2Ctx.B1;cases h:k.db using Fin.cases with|zero=>exact b3|succ i=>fin_cases i;exact az
 have bg:vb∉k.Ia:=fun h=>by have:vb∈k.IC:=QB h c3;rw[ap] at this;exact YE this
 have ae:=(Q1 k.hL.1 k.hb az b3).1;have PU:=(Q1 k.hL.1 k.hb az b3).2;obtain⟨_,b8⟩:=Vu k ab
 have b6 (hX:k.X.Nonempty) (d:Fin 2):k.Ed d {vb}=∅:=Xm fun e he=>by
  have⟨b5,hc⟩:=hX;induction e using Sym2.ind with| _ u w=>
  have h4 (x y:Fin 11) (bh:x∈k.Wb) (a8:y∈k.B1) (hyv:y≠vb) (hxy:Ga x y) (hxX:x∉k.X):False:=
   hxX ((by by_contra hn;exact QV hyv.symm (Ne.symm hn) (PU b5 (b8 b5 hc).1) ((b8 b5 hc).2 y a8).symm (PU x bh) hxy.symm:x=b5)▸hc)
  have hs:=YS k he;have ha:=Bp (Ve k he)
  rcases hs.2.2.2.2 with⟨hu,hw,cw⟩|⟨hw,hu,dd⟩
  ·exact h4 u w (Qb hu) (Qb hw) (We hs.2.2.2.1) ha cw
  ·exact h4 w u (Qb hw) (Qb hu) (We hs.2.2.1) ha.symm dd
 let D (da:Fin 2) (bs:St C):Prop:=bs.L.card<=1\/bs.W={k.HS}\/(Oi C (k.oa da)∩bs.L=∅/\bs.L⊆k.B1)
 have av (hW:k.w0∈k.Wa):∃p:j2BcPack k {vb},(if k.X.Nonempty then 1 else 0)+(if k.w1 then 2 else 1)+K1 p.bcl<=3/\(¬k.w1->∀bs∈p.bcl,D p.da bs):=by
  by_cases hX:k.X.Nonempty
  · exact⟨⟨0,[],by simp,Vz,fun e he=>by rw[b6 hX 0,b6 hX 1,union_empty] at he;exact(YE he).elim,by simp⟩,
     by dsimp only[K1];simp[hX];split_ifs<;>omega,fun _=>by simp⟩
  have bj (d:Fin 2) (hC:(k.dB d).card<=1):
    ∃j:St C,j.W.card=1/\j.L.card<=1/\((k.Ed d {vb}).Nonempty->j.c∈k.dB d/\∃x,s(j.c,x)∈k.Ed d {vb})/\∀e∈k.Ed d {vb},∃x∈j.L,e=s(j.c,x):=by
   obtain⟨j,d4,bn,d0,d9,hc⟩:=Bq k hC
   have a5:j.L.card<=1:=by
    rcases Eo j.L with c6|⟨x,t⟩;rw[c6,card_empty];omega
    exact(ZE fun y hy=>B2 (Uv _) ⟨Bp (j.he y hy),PU y (Qb (Qm (Qm (bn hy))))⟩).trans
     (Q3 j.c vb (We (YS k (d0 x t)).2.2.1))
   exact⟨j,WD d4,a5,d9,hc⟩
  by_cases h1:k.w1
  · have cn:k.Ed 0 {vb}=∅\/k.Ed 1 {vb}=∅:=by
     by_contra! Pt;have⟨e0,cs⟩:=Pt.1;have⟨e1,d8⟩:=Pt.2
     obtain⟨bl,x0,y1,rfl,_,bm,aa,a8,_⟩:=XT cs;obtain⟨bk,d6,u0,rfl,_,bp,a6,af,_⟩:=XT d8;rw[mem_singleton] at bm bp;have⟨z1,ad,z2,ah,hz12⟩:=one_lt_card.mp k.Rq;have hs0:=k.PM bl;have hs1:=k.PM bk
     exact ZN (PU k.w0 (Qb h1)) (PU x0 (Qb aa)) (KP k hW hs0.2.1)
      (PU d6 (Qb a6)) (KP k hW hs1.2.1) (KR k (Q7 aa) (Q7 a6)).symm (ZY k hW (Q7 aa) (Q7 a6))
      (k.Md hW ad) (fun e=>bg (e▸ad)) (K6 k (.inl (Q7 aa)) ad).symm (K6 k (.inr (Q7 a6)) ad).symm
      (k.Md hW ah) (fun e=>bg (e▸ah)) (K6 k (.inl (Q7 aa)) ah).symm (K6 k (.inr (Q7 a6)) ah).symm hz12.symm
      (VH k bl) bm (KP k hW hs0.2.2.1) (KR k (Q7 aa) (Q7 a8)).symm
      (YQ k hs0.2.2.1 (Qb a8) (Qb a6)) (K6 k (.inr (Q7 a8)) ad) (K6 k (.inr (Q7 a8)) ah)
      (Ye k ad (Qb a8) (Qb a6)) (Ye k ah (Qb a8) (Qb a6))
      (VH k bk) bp (KP k hW hs1.2.2.1) (YQ k hs1.2.2.1 (Qb af) (Qb aa))
      (KR k (Q7 af) (Q7 a6)) (K6 k (.inl (Q7 af)) ad) (K6 k (.inl (Q7 af)) ah) (KR k (Q7 af) (Q7 a8))
      (ZY k hW (Q7 af) (Q7 a8)) (Ye k ad (Qb af) (Qb aa)) (Ye k ah (Qb af) (Qb aa))
    rcases cn with cy|b4
    ·have⟨p,hs⟩:=ZX k 1 cy;exact⟨p,by simp[hX,h1];split_ifs at hs<;>omega,fun h=>(h h1).elim⟩
    ·have⟨p,hs⟩:=ZX k 0 b4;exact⟨p,by simp[hX,h1];split_ifs at hs<;>omega,fun h=>(h h1).elim⟩
  · have cp {da:Fin 2} {j:St C} (h:D da j):k.R8 da j:=by
     rcases h with h'|h'|⟨hA,_⟩;exact .inl h';exact .inr (.inl h');exact .inr (.inr ⟨hA,fun x=>(h1 x).elim,fun x=>(hX x).elim⟩)
    have bz (d:Fin 2) (hA:(k.dA d).card<=1) (hB:(k.dB (1-d)).card<=1):
      ∃p:j2BcPack k {vb},(if k.X.Nonempty then 1 else 0)+(if k.w1 then 2 else 1)+K1 p.bcl<=3/\(¬k.w1->∀bs∈p.bcl,D p.da bs):=by
     obtain⟨j0,ag,_,a9,aq⟩:=VS k (S:={vb}) hA k.HS k.MM (fun _ t=>Qb (Qm t));have⟨j1,ak,a5,ac,au⟩:=bj (1-d) hB
     obtain⟨p,ar,hs,aw⟩:=VQ k d d j0 j1 (fun h=>(a9 h).2) (fun h=>(ac h).2)
      (fun am a7 eq=>YN (a9 am).1 (k.PW (QB (eq▸Qb (Qm (ac a7).1)) (Qb (Qm (a9 am).1)))))
      aq au (.inl (Vp a5)) (.inr (.inl ag)) (.inl a5)
     exact⟨p,by rw[WD ag,ak] at hs;simp[hX,h1];omega,fun _ b hb=>by rw[ar];rcases aw b hb with rfl|rfl;exact .inr (.inl ag);exact .inl a5⟩
    rcases k.Rv 0 with h0|h0<;>rcases k.Rv 1 with a7|a7
    · have⟨j0,ag,ax,a9,aq⟩:=VS k (S:={vb}) h0 (k.oa 1) (k.MZ 1) (fun _ t=>Qm (Q7 (Qm t)))
      have⟨j1,ak,a5,ac,au⟩:=VS k (S:={vb}) a7 k.HS k.MM (fun _ t=>Qb (Qm t));have bu:D 0 j0:=.inr (.inr ⟨Xm fun _ t=>YN (Q7 (Qm (ax (Qb t)))) (Q7 t),fun _ t=>Qb (Qm (ax t))⟩)
      obtain⟨p,ar,hs,aw⟩:=VQ k 0 0 j0 j1 (fun h=>(a9 h).2) (fun h=>(ac h).2)
       (fun am a7 eq=>KR k (Q7 (Qm (a9 am).1)) (eq▸Q7 (Qm (ac a7).1)) rfl) aq au
       (.inl (by rw[ag,Sbu];exact BX fun _ t=>YN (Q7 (Qm (a5 (Qb t)))) (Q7 t))) (cp bu) (.inr (.inl ak))
      exact⟨p,by rw[WD ag,WD ak] at hs;simp[hX,h1];omega,fun _ b hb=>by rw[ar];rcases aw b hb with rfl|rfl;exact bu;exact .inr (.inl ak)⟩
    ·exact bz 0 h0 a7
    ·exact bz 1 a7 h0
    · have⟨j0,ag,ax,a9,aq⟩:=bj 0 h0;have⟨j1,ak,a5,ac,au⟩:=bj 1 a7
      obtain⟨p,ar,hs,aw⟩:=VQ k 0 0 j0 j1 (fun h=>(a9 h).2) (fun h=>(ac h).2)
       (fun am a7 eq=>KR k (eq▸Q7 (Qm (ac a7).1)) (Q7 (Qm (a9 am).1)) rfl) aq au (.inl (Vp a5)) (.inl ax) (.inl a5)
      exact⟨p,by rw[ag,ak] at hs;simp[hX,h1];omega,fun _ b hb=>by rw[ar];rcases aw b hb with rfl|rfl;exact .inl ax;exact .inl a5⟩
 by_cases ay:k.w0∈k.Wa/\¬k.wA/\k.w0=vb
 · have⟨ca,bf,al⟩:=ay;have⟨p,c8,cu⟩:=av ca
   have b4:k.B1∩k.Wb=∅:=Xm fun x t=>ae (al▸k.hw0 x (k.PW t)▸Qb t);have bq:¬k.w1:=fun h=>ae (al▸Qb h);have br (d:Fin 2):vb∉k.A d:=fun h=>by rw[←al] at h;fin_cases d<;>[exact bf (.inl h);exact bf (.inr h)]
   have cz:∀bs∈p.bcl,bs.c≠vb:=fun b hb=>by have⟨x,t⟩:=p.endp b hb;rcases Yc t with h|h<;>exact We (YS k h).2.2.1
   obtain⟨L0,Lm,Mb,_,ba,ce,_,hU,hW,hM,ch⟩:=Wt k ae
   let itm:St C:=⟨vb,Q4 vb k.Ua∪L0,insert (k.oa p.da) (W0For G11 C k.b),
    fun z hz=>by rcases Vs hz with rfl|h;exact k.MZ p.da;exact Qg k.hL.1 k.b z h,
    fun x t=>by
     rcases Yc t with h1|h2
     ·exact Mbu ⟨k.oa p.da,mem_insert_self _ _,k.He p.da (k.H2 (KC h1)).1 (br p.da)⟩
     ·exact WG (subset_insert _ _) (ce h2),
    fun x t=>by rcases Yc t with h1|h2;exact K0 (KC h1);exact Ds (KC (ba h2)),False,False.elim⟩
   have cf:itm.L∩k.B1=∅:=Xm fun x t=>by
    rcases Yc (Q7 t) with h1|h2
    · have bx:=(k.H2 (KC h1)).1
      have:x∈k.IC:=QB (QB (k.He 0 bx (br 0)) (k.He 1 bx (br 1))) (Qb t);rw[ap] at this;exact YE this
    · have⟨cg,d5⟩:=Dp (KC (ba h2))
      have bh:x∈k.Wb:=by
       by_cases hb:s(vb,x)∈k.Ub;exact((k.Mg hb).2.2.2.resolve_left fun h=>ae h.1).1
       exact((k.PM (QG (QG cg hb) d5)).2.2.2.resolve_left fun h=>ae h.1).1
      exact YE (b4▸QB (Qb t) bh)
   have hok:=Z2 p.ok cz fun b hb=>by
    rcases cu bq b hb with a5|cd|⟨hA,bn⟩
    ·exact .inl (Vp a5)
    ·right;rw[cd,Sbu,inter_comm];change (itm.L∩k.B1).card<=1;rw[cf,card_empty];omega
    ·exact .inl (Vj fun z hz=>by rcases Vs hz with rfl|cr;exact hA;exact Xm fun _ t=>YE (b4▸QB (bn (Qb t)) (Qc k.hL.1 k.b z cr (Q7 t))))
   have dc:=QS (E:=Us C\Lm.image (fun w=>s(vb,w))) k.hL.1 (k.HD ab) (itm::p.bcl) (W5 k ab)
    (fun e bv=>by
     induction e using Sym2.ind with| _ u w=>
     by_cases hv:(u=vb\/w=vb)/\s(u,w)∉k.Ua
     ·have⟨x,t,q⟩:=ch u w bv hv.2 hv.1;exact⟨itm,Xs XP,x,X4 t,q⟩
     exact Zy k ab (by rw[ap];exact BQ) (by rw[aj]) _
      (fun x t=>⟨itm,Xs XP,x,Z4 (al▸t),by change s(k.w0,x)=s(vb,x);rw[al]⟩)
      (fun g hg x t=>⟨g,V6 hg,x,t,rfl⟩) (fun h1=>(bq h1).elim) (Z0 p.cov fun _ h=>Xs (XR h))
      (Qm bv) (by by_cases hm:s(u,w)∈k.Ua;exact .inr hm;have⟨h1,h2⟩:=not_or.mp fun h=>hv ⟨h,hm⟩;exact .inl ⟨Pd h1,Pd h2⟩))
    (fun g hg b hb=>by
     obtain⟨hX,rfl⟩:=XJ k hg
     rcases ZC hb with rfl|cm
     ·intro e;have h:=(b8 _ hX.choose_spec).1;change hX.choose=vb at e;exact ae (e▸h)
     ·have⟨x,t⟩:=p.endp b cm;rw[b6 hX 0,b6 hX 1,union_empty] at t;exact(YE t).elim)
    hok.1 hok.2
   have df:itm.W.card<=(W0For G11 C k.b).card+1:=Cil _ _;have cl:=BC k ab
   simp only[Lmc,Lsc,bq,↓reduceIte,K1] at dc c8 cl;dsimp only[j2Ctx.Pz];omega
 · exact WK k ab (S:={vb}) (by simp) (by rw[ap];exact BQ) (by rw[aj])
    (fun s b9=>by rw[Zq b9];exact ae) (fun h1 h2 b9=>ay ⟨h1,h2,Zq b9⟩) (m:=3) (le_refl 3)
    (fun gs bs hs d3 c5 cx hok cb=>BG k ae PU gs bs hs d3 c5 (fun b hb=>We (cx b hb)) hok (fun u w he cj=>cb u w he (by simpa using cj)))
    (fun hW=>by obtain⟨p,hs,_⟩:=av hW;exact⟨p,hs⟩)
lemma Ws (ac:2<=k.B1.card)(ay:k.IC=∅)(au:k.Ib=∅):k.Pz:=by
 classical
 obtain⟨_,b8⟩:=Vu k ac
 exact WK k ac (S:=∅) (by simp) (by rw[ay]) (by rw[au]) (by simp) (by simp) (m:=4) (by omega)
  (fun gs bs hs b6 an _ hok av=>
   Y5 k.hL k.hs k.hrb k.hB0ne k.hbWit gs bs hs b6
    (fun e he=>by induction e using Sym2.ind with| _ u w=>exact av u w he (.inl ⟨YE,YE⟩)) an hok.1 hok.2)
  (fun hW=>by
   have bb:k.X.Nonempty->k.w1->k.Ed 0 ∅=∅\/k.Ed 1 ∅=∅:=fun ⟨cb0,hc⟩ h1=>by
    by_contra! Pt;have⟨e0,aa⟩:=Pt.1;have⟨e1,ab⟩:=Pt.2
    obtain⟨a9,x0,y1,rfl,_,_,t,j,am⟩:=XT aa;obtain⟨a8,aj,u0,rfl,_,_,g,q,ax⟩:=XT ab;have⟨z1,a6,z2,a7,hz12⟩:=one_lt_card.mp k.Rq;have hs0:=k.PM a9;have hs1:=k.PM a8;have ah:=(b8 cb0 hc).2
    exact XD (k.Md hW a6) (k.Md hW a7) hz12.symm (ah k.w0 (Q7 h1)).symm
     (ah y1 (Qb j)) (KP k hW hs0.2.2.1) (K6 k (.inr (Q7 j)) a6) (K6 k (.inr (Q7 j)) a7)
     (ah u0 (Qb q)) (KP k hW hs1.2.2.1) (K6 k (.inl (Q7 q)) a6) (K6 k (.inl (Q7 q)) a7)
     (KR k (Q7 q) (Q7 j)) (ZY k hW (Q7 q) (Q7 j))
     (VH k a9).symm (KP k hW hs0.2.1) (fun e=>am (e▸hc))
     (K6 k (.inl (Q7 t)) a6) (K6 k (.inl (Q7 t)) a7) (KR k (Q7 t) (Q7 j))
     (YQ k hs1.2.2.1 (Qb q) (Qb t)).symm (Ye k a6 (Qb q) (Qb t)) (Ye k a7 (Qb q) (Qb t))
     (VH k a8).symm (KP k hW hs1.2.1) (fun e=>ax (e▸hc))
     (K6 k (.inr (Q7 g)) a6) (K6 k (.inr (Q7 g)) a7) (YQ k hs0.2.2.1 (Qb j) (Qb g)).symm
     (KR k (Q7 q) (Q7 g)).symm (KR k (Q7 t) (Q7 g)).symm (ZY k hW (Q7 t) (Q7 g))
     (Ye k a6 (Qb j) (Qb g)) (Ye k a7 (Qb j) (Qb g))
   rcases Eo (k.Ed 0 ∅) with ba|⟨e0,aa⟩
   ·have⟨p,hs⟩:=ZX k 1 ba;exact⟨p,by split_ifs at hs ⊢<;>omega⟩
   rcases Eo (k.Ed 1 ∅) with az|⟨e1,ab⟩
   ·have⟨p,hs⟩:=ZX k 0 az;exact⟨p,by split_ifs at hs ⊢<;>omega⟩
   have bl:(if k.X.Nonempty then 1 else 0)+(if k.w1 then 2 else 1)<=2:=by
    by_cases hX:k.X.Nonempty
    · have b4:¬k.w1:=fun h1=>by rcases bb hX h1 with h|h<;>[exact YE (h▸aa);exact YE (h▸ab)]
      simp[hX,b4]
    ·simp[hX];split_ifs<;>omega
   obtain⟨a9,x0,y1,rfl,_,_,t,j,_⟩:=XT aa;obtain⟨a8,aj,u0,rfl,_,_,g,q,_⟩:=XT ab;have hs0:=k.PM a9;have hs1:=k.PM a8
   have hP:(k.dA 0).card<=1\/(k.dA 1).card<=1:=by
    by_contra! h
    exact BE k (x0:=y1) (x1:=u0) (Y2:=k.dA 0) (Y3:=k.dA 1) hW (by omega) (by omega) (KR k (Q7 q) (Q7 j))
     (fun _ z=>(k.HX 0 (Qm (Q7 (Qm z))) (Qb (Qm z)) (Qm (Q7 j)) (Qb j)).symm)
     (fun _ hz=>(k.HX 1 (Qm (Q7 (Qm hz))) (Qb (Qm hz)) (Qm (Q7 q)) (Qb q)).symm)
     (fun _ z=>⟨(YQ k hs1.2.2.1 (Qb q) (Qb (Qm z))).symm,KP k hW (YN z),fun _ hv=>(K6 k (.inl (Q7 (Qm z))) hv).symm⟩)
     (fun _ hz=>⟨(YQ k hs0.2.2.1 (Qb j) (Qb (Qm hz))).symm,KP k hW (YN hz),fun _ z=>(KR k (Q7 (Qm z)) (Q7 (Qm hz))).symm,fun _ hv=>(K6 k (.inr (Q7 (Qm hz))) hv).symm⟩)
     (fun _ hv=>⟨(K6 k (.inr (Q7 j)) hv).symm,(K6 k (.inl (Q7 q)) hv).symm⟩)
     (fun _ z _ hz=>by rcases ZY k hW (Q7 (Qm z)) (Q7 (Qm hz)) with h|h|h;exact .inl h.symm;exact .inr (.inr h);exact .inr (.inl h))
     (fun _ hv _ hz=>by rcases Ye k hv (Qb j) (Qb (Qm hz)) with h|h|h;exact .inr (.inl h);exact .inl h;exact .inr (.inr h.symm))
     (fun _ hv _ z=>by rcases Ye k hv (Qb q) (Qb (Qm z)) with h|h|h;exact .inr (.inl h);exact .inl h;exact .inr (.inr h.symm))
   have hQ:(k.dB 0).card<=1\/(k.dB 1).card<=1:=by
    by_contra! h
    exact BE k (x0:=x0) (x1:=aj) (Y2:=k.dB 0) (Y3:=k.dB 1) hW (by omega) (by omega) (KR k (Q7 t) (Q7 g)).symm
     (fun _ hy=>k.HX 0 (Qm (Q7 t)) (Qb t) (Qm (Q7 (Qm hy))) (Qb (Qm hy)))
     (fun _ hu=>k.HX 1 (Qm (Q7 g)) (Qb g) (Qm (Q7 (Qm hu))) (Qb (Qm hu)))
     (fun _ hy=>⟨YQ k (YN hy) (Qb (Qm hy)) (Qb g),KP k hW (YN hy),fun _ hv=>(K6 k (.inr (Q7 (Qm hy))) hv).symm⟩)
     (fun _ hu=>⟨YQ k (YN hu) (Qb (Qm hu)) (Qb t),KP k hW (YN hu),fun _ hy=>KR k (Q7 (Qm hu)) (Q7 (Qm hy)),fun _ hv=>(K6 k (.inl (Q7 (Qm hu))) hv).symm⟩)
     (fun _ hv=>⟨(K6 k (.inl (Q7 t)) hv).symm,(K6 k (.inr (Q7 g)) hv).symm⟩)
     (fun _ hy _ hu=>ZY k hW (Q7 (Qm hu)) (Q7 (Qm hy)))
     (fun _ hv _ hu=>Ye k hv (Qb (Qm hu)) (Qb t)) (fun _ hv _ hy=>Ye k hv (Qb (Qm hy)) (Qb g))
   obtain⟨d,hdA,hdB⟩:∃d:Fin 2,(k.dA d).card<=1/\(k.dB (1-d)).card<=1:=by
    by_cases af:(k.dA 0).card<=1
    ·by_cases ag:(k.dB 1).card<=1;exact⟨0,af,ag⟩;exact⟨1,(k.Rv 1).resolve_right ag,hQ.resolve_right ag⟩
    ·exact⟨1,hP.resolve_left af,(k.Rv 0).resolve_left af⟩
   obtain⟨jA,ad,_,ae,b5⟩:=VS k (S:=∅) hdA k.HS k.MM (fun _ z=>Qb (Qm z));obtain⟨jB,b9,bd,_,ak,b3⟩:=Bq k (S:=∅) hdB;have hDj:=BD k (1-d) bd;rw[Qd] at hDj
   obtain⟨p,_,hs,_⟩:=VQ k d d jA jB (fun h=>(ae h).2) (fun h=>(ak h).2)
    (fun al b7 eq=>YN (ae al).1 (k.PW (QB (eq▸Qb (Qm (ak b7).1)) (Qb (Qm (ae al).1))))) b5 b3
    (.inl (by rw[ad,Sbu,hDj.2.2,card_empty];omega)) (.inr (.inl ad)) (.inr (.inr ⟨hDj.1,fun _=>hDj.2.1,fun _=>hDj.2.2⟩))
   exact⟨p,by rw[ad,b9,Bt,Bt] at hs;omega⟩)
lemma Bm (a7:2<=k.B1.card)(bp:2<=k.Wb.card){v:Fin 11}(a6:k.IC={v}):k.Pz:=by
 classical
 have a3:v∈k.Ia:=Q7 (a6▸WB);have bj:v∈k.B1:=Qb (a6▸WB);have MG:=(Q1 k.hL.1 k.ha (Q7 a3) (Qb a3)).1;have a9:=(Q1 k.hL.1 k.ha (Q7 a3) (Qb a3)).2;have⟨aa,t⟩:=YG k.hL.1 k.hT k.hs k.hab k.hrb k.hno2 (Q7 a3) (Qb a3) bj;obtain⟨_,bg⟩:=Vu k a7
 have an:k.Ib⊆{v}:=fun vb ah=>by
  by_contra Pt;rw[mem_singleton] at Pt
  have h1:k.Wb.card<=1:=(ZE fun x hx=>B2 (Uv _) ⟨t x hx,(Q1 k.hL.1 k.hb (Q7 ah) (Qb ah)).2 x hx⟩).trans (Q3 v vb (Ne.symm Pt));omega
 exact WK k a7 (S:={v}) (by simp) (by rw[a6]) an
  (fun s ad=>by rw[Zq ad];exact aa) (fun hw _ ad=>MG (Zq ad▸hw)) (m:=3) (le_refl 3)
  (fun gs bs hs be am bb az aq=>BG k aa t gs bs hs be am (fun b hb=>We (bb b hb)) az (fun u w he b6=>aq u w he (by simpa using b6)))
  (fun hW=>by
   obtain⟨vp,j,ap⟩:∃vp∈k.Ia,vp≠v:=by
    have⟨z1,b5,z2,bl,hn⟩:=one_lt_card.mp k.Rq
    by_cases h1:z1=v;exact⟨z2,bl,fun e=>hn (h1.trans e.symm)⟩;exact⟨z1,b5,h1⟩
   have ba:k.Ed 0 {v}=∅\/k.Ed 1 {v}=∅:=by
    by_contra! Pt;have⟨e0,aw⟩:=Pt.1;have⟨e1,b8⟩:=Pt.2
    obtain⟨ac,x0,y2,rfl,_,ae,g,a4,_⟩:=XT aw;obtain⟨ab,x1,y3,rfl,_,a8,z,a5,_⟩:=XT b8;rw[mem_singleton] at ae a8;have hs0:=k.PM ac;have hs1:=k.PM ab
    have ak (p q:Fin 11) (hp:p∈k.Ad 0) (hq:q∈k.Ad 1):Ga k.w0 p\/Ga k.w0 q\/Ga p q:=by
     rcases ZY k hW hp hq with h|h|h;exact .inr (.inr h);exact .inl h.symm;exact .inr (.inl h.symm)
    have al (q w:Fin 11) (hq:q∈k.B1) (hw:w∈k.Wb):Ga w vp\/Ga w q\/Ga vp q:=by
     rcases Ye k j hq hw with h|h|h;exact .inr (.inr h);exact .inl h.symm;exact .inr (.inl h.symm)
    exact Z5 (a9 k.w0 hW) (t x0 (Qb g)) (t x1 (Qb z))
     (KP k hW hs0.2.1) (KP k hW hs1.2.1) (KR k (Q7 g) (Q7 z)).symm (ak x0 x1 (Q7 g) (Q7 z))
     (k.Md hW j) ap (K6 k (.inl (Q7 g)) j).symm (K6 k (.inr (Q7 z)) j).symm
     (VH k ac) ae (KP k hW hs0.2.2.1) (KR k (Q7 g) (Q7 a4)).symm
     (YQ k hs0.2.2.1 (Qb a4) (Qb z)) (K6 k (.inr (Q7 a4)) j) (al y2 x1 (Qb a4) (Qb z))
     (VH k ab) a8 (KP k hW hs1.2.2.1) (YQ k hs1.2.2.1 (Qb a5) (Qb g))
     (KR k (Q7 a5) (Q7 z)) (K6 k (.inl (Q7 a5)) j) (KR k (Q7 a5) (Q7 a4)) (al y3 x0 (Qb a5) (Qb g))
     (by rcases ak y3 y2 (Q7 a5) (Q7 a4) with h|h|h;exact .inr (.inl h);exact .inl h;exact .inr (.inr h.symm))
   have b7:k.X.Nonempty->k.w1->k.Ed 0 {v}∪k.Ed 1 {v}=∅:=fun ⟨cb0,hc⟩ h1=>
    Xm fun e he=>by
     have⟨bk,aj⟩:=bg cb0 hc
     have hS (d:Fin 2) (hEd:e∈k.Ed d {v}):False:=by
      obtain⟨hE,x0,y1,rfl,_,af,g,au,b4⟩:=XT hEd;rw[mem_singleton] at af;have hs:=k.PM hE
      exact ZM (a9 k.w0 hW) (t cb0 bk) (aj k.w0 (Q7 h1)) (t x0 (Qb g))
       (KP k hW hs.2.1) (fun e=>b4 (e▸hc)) (aj y1 (Qb au)) (VH k hE) af (KP k hW hs.2.2.1)
     rcases Yc he with h0|bf;exact hS 0 h0;exact hS 1 bf
   have hU (d:Fin 2) (hO:k.Ed (1-d) {v}=∅):∃p:j2BcPack k {v},(if k.X.Nonempty then 1 else 0)+(if k.w1 then 2 else 1)+K1 p.bcl<=3:=by
    have⟨p,hs⟩:=ZX k d hO;refine⟨p,?_⟩
    by_cases hB:k.X.Nonempty/\k.w1
    · have he:k.Ed d {v}=∅:=by have:=b7 hB.1 hB.2;rwa[←WJ k d,hO,union_empty] at this
      simp only[he,Nne,↓reduceIte] at hs;simp[hB.1,hB.2];omega
    ·split_ifs at hs ⊢<;>first|exact(hB ⟨‹_›,‹_›⟩).elim|omega
   rcases ba with bh|ar;exact hU 1 bh;exact hU 0 ar)
lemma BT:k.Pz:=by
 classical
 by_cases b4:2<=k.IC.card
 · have b9:(k.Wa∪k.Wb).card<=1:=Qa Q3 b4 fun w hw z hz=>by
    rcases Yc hw with ha|hb
    ·exact((Q1 k.hL.1 k.ha (Q7 (Q7 hz)) (Qb (Q7 hz))).2 w ha).symm
    ·exact((YG k.hL.1 k.hT k.hs k.hab k.hrb k.hno2 (Q7 (Q7 hz)) (Qb (Q7 hz)) (Qb hz)).2 w hb).symm
   have⟨wc,ar⟩:=Qk b9
   exact WY k wc fun u v he=>by
    have h:u∈k.Wa∪k.Wb\/v∈k.Wa∪k.Wb:=by
     rcases QM k.hL k.hT k.hs k.hrb k.hno2 he with⟨_,(h|h)|⟨_,h|h⟩|⟨hJ,hu|hv,_⟩⟩|⟨_,_,_,⟨h,_⟩|⟨h,_⟩⟩
     ·exact .inl (Z4 (Q5 k.hL.1 h))
     ·exact .inr (Z4 (Q5 k.hL.1 h))
     ·exact .inl (X4 (Q5 k.hL.1 h))
     ·exact .inr (X4 (Q5 k.hL.1 h))
     ·exact .inl (Z4 (QP k.hL.1 k.hT k.hs k.hrb k.hno2 hJ hu))
     ·exact .inr (Z4 (QP k.hL.1 k.hT k.hs k.hrb k.hno2 hJ hv))
     ·exact .inl (X4 h)
     ·exact .inr (X4 h)
    rcases h with hu|hv;exact .inl (ar u hu);exact .inr (ar v hv)
 by_cases av:k.Wb.card<=1
 · have⟨t,a4⟩:=Qk av
   have hR:∀u v:Fin 11,s(u,v)∈Us C\k.Ua->u=t\/v=t:=fun u v he=>by
    have⟨hU,a3⟩:=Dp he
    by_cases hb:s(u,v)∈k.Ub
    ·rcases(k.Mg hb).2.2.2 with⟨h,_⟩|⟨h,_⟩;exact .inl (a4 u h);exact .inr (a4 v h)
    ·rcases(k.PM (QG (QG hU hb) a3)).2.2.2 with⟨h,_,_⟩|⟨h,_,_⟩;exact .inl (a4 u h);exact .inr (a4 v h)
   by_cases hW:k.w0∈k.Wa
   · by_cases hw:t=k.w0
     ·subst t;exact V8 k hR
     · have aq:t∈k.Wb->t∉k.B1:=fun a5 j=>hw (k.hw0 t (k.PW (QB j a5)))
       let itwb:=Q0 C t (Q4 t (Us C\k.Ua)) k.HS k.MM (fun x g=>by
        have⟨hU,a3⟩:=Dp (KC g)
        by_cases hb:s(t,x)∈k.Ub
        · have hs:=k.Mg hb;have a5:t∈k.Wb:=by rcases hs.2.2.2 with⟨h,_⟩|⟨h,_⟩;exact h;exact a4 x h▸h
          exact Ym hs.2.1 hs.2.2.1 (aq a5)
        ·rcases(k.PM (QG (QG hU hb) a3)).2.2.2 with⟨_,_,j⟩|⟨a5,_,j⟩;exact j;exact(aq (a4 x a5▸a5) j).elim)
        (fun _ g=>Ds (KC g)) False False.elim
       have⟨da,ab⟩:=k.Tk
       let itw:=Q0 C k.w0 (Q4 k.w0 k.Ua) (k.oa da) (k.MZ da)
        (fun x g=>k.He da (k.H2 (KC g)).1 (ab hW)) (fun _ g=>K0 (KC g)) k.wA (fun hA x g=>by
         have bd:k.w0∈k.A (1-da):=by rcases hA with h0|j<;>fin_cases da<;>first|assumption|exact(ab hW ‹_›).elim
         exact Y1 k.hL.1 k.hT k.hs k.hab bd hW x (QE g))
       have aj:Vn (Us C) [itw,itwb]:=fun e he=>by
        induction e using Sym2.ind with| _ u v=>
        by_cases hm:s(u,v)∈k.Ua
        ·have⟨x,g,q⟩:=k.RB hm;exact⟨itw,XP,x,g,q⟩
        · rcases hR u v (QG he hm) with rfl|rfl
          ·exact⟨itwb,XR Bj,v,YT (QG he hm),rfl⟩
          ·exact⟨itwb,XR Bj,u,YT (QG (Y6▸he) fun h=>hm (Y6▸h)),Y6⟩
       by_cases ad:k.wA
       · exact Y5 k.hL k.hs k.hrb k.hB0ne k.hbWit [itw] [itwb] (by simp[itw,itwb,Q0])
          (fun _ h=>by obtain rfl:=Ys h;exact ad) aj
          (fun _ j _ h2=>by obtain rfl:=Ys j;obtain rfl:=Ys h2;exact Ne.symm hw) (YF itwb).1 (YF itwb).2
       · have bj:(itwb.W.biUnion (Oi C)∩itw.L).card<=1:=by
          refine(ZE (show itwb.W.biUnion (Oi C)∩itw.L⊆k.IC from fun x g=>?_)).trans (by omega)
          simp only[itwb,Q0,Sbu] at g;have ap:=(k.H2 (KC (Qb g))).1;exact QB (QB (k.He 0 ap fun h=>ad (.inl h)) (k.He 1 ap fun h=>ad (.inr h))) (Q7 g)
         have hok:=Z2 (x:=itw) (YF itwb) (fun _ h=>by obtain rfl:=Ys h;exact hw) (fun _ h=>by obtain rfl:=Ys h;exact .inr bj)
         exact Y5 k.hL k.hs k.hrb k.hB0ne k.hbWit [] [itw,itwb] (by simp[itw,itwb,Q0]) (by simp) aj (by simp) hok.1 hok.2
   ·exact WY k t fun u v he=>hR u v (QG he fun hm=>by rcases(k.H2 hm).2 with h|h<;>[exact hW (k.hw0 u h▸h);exact hW (k.hw0 v h▸h)])
 by_cases b5:k.B1.card<=1
 · rcases Eo k.B1 with ak|⟨z1,ah⟩
   · exact V8 k fun u v he=>by
      have⟨hU,a3⟩:=Dp he
      by_cases hb:s(u,v)∈k.Ub
      ·obtain⟨z,hz,_⟩:=(k.Mg hb).2.2.1;exact(YE (ak▸hz)).elim
      ·rcases(k.PM (QG (QG hU hb) a3)).2.2.2 with⟨_,_,j⟩|⟨_,_,j⟩<;>exact(YE (ak▸j)).elim
   have⟨q,hq⟩:=Qk b5
   have al:∀u v:Fin 11,s(u,v)∈Us C\k.Ua->u=q\/v=q:=fun u v he=>by
    have⟨hU,a3⟩:=Dp he
    by_cases hb:s(u,v)∈k.Ub
    ·obtain⟨x1,am,rfl|rfl⟩:=(k.Mg hb).2.2.1;exact .inl (hq x1 am);exact .inr (hq x1 am)
    ·rcases(k.PM (QG (QG hU hb) a3)).2.2.2 with⟨_,_,j⟩|⟨_,_,j⟩;exact .inr (hq v j);exact .inl (hq u j)
   by_cases bb:q=k.w0
   ·subst q;exact V8 k al
   · set Lq:=Q4 q (Us C\k.Ua)
     have an:(Us C\k.Ua).card<=Lq.card:=WT q al;have⟨da,ab⟩:=k.Tk
     let itw:=Q0 C k.w0 (Q4 k.w0 k.Ua) (k.oa da) (k.MZ da)
      (fun x g=>by have hW:k.w0∈k.Wa:=by rcases(k.H2 (KC g)).2 with h|h;exact h;exact k.hw0 x h▸h
                   exact k.He da (k.H2 (KC g)).1 (ab hW)) (fun _ g=>K0 (KC g)) False False.elim
     obtain⟨Pw,ba,bt,_⟩:=Ky k.hL.1 Q3 itw.hW itw.hL itw.he
     have bs:k.Ua.card<=(rFull G11 C).card+1:=by
      have j:k.Ua.card<=itw.L.card:=WT k.w0 fun u v he=>by rcases(k.H2 he).2 with h|h;exact .inl (k.hw0 u h);exact .inr (k.hw0 v h)
      have h2:=ZE ba;have h3:itw.W.card=1:=by simp[itw,Q0]
      omega
     have br:(Us C\k.Ua).card+k.Ua.card=(Us C).card:=Csd K0;obtain⟨mb,hm,_,_,_⟩:=QK k.hL.1 k.hs k.hrb k.hB0ne
     by_cases bu:1<=(centreless G11 C).card
     · have bp:1<=(mixing G11 C).card:=Cpr ⟨mb,hm⟩
       have bq:Lq.card<=4:=KH Ds q;dsimp only[j2Ctx.Pz];omega
     · have bf:q∉k.Wb:=fun h=>bb (k.hw0 q (k.PW (QB (hq z1 ah▸ah) h)))
       obtain⟨L0,Lm,Mb,be,_,ac,b8,_,_,hM,_⟩:=Wt k bf;have aw:W0For G11 C k.b=∅:=card_eq_zero.mp (by have:=(Qj (G:=G11) (C:=C) k.b).trans (Qs k.b);omega)
       have au:L0=∅:=by rw[aw,biUnion_empty,subset_empty] at ac;exact ac
       dsimp only[Lq] at an;rw[be,au,empty_union,b8] at an;dsimp only[j2Ctx.Pz];omega
 have ax:2<=k.Wb.card:=by omega
 have a7:2<=k.B1.card:=by omega
 by_cases aa:k.IC=∅
 · have b7:k.Ib.card<=1:=by
    by_contra! h
    have j:k.Wb.card<=1:=Qa Q3 (by omega:2<=k.Ib.card)
     (fun w hw v hv=>(Q1 k.hL.1 k.hb (Q7 hv) (Qb hv)).2 w hw |>.symm)
    omega
   rcases Eo k.Ib with az|af
   ·exact Ws k a7 aa az
   · have⟨vb,ag⟩:=card_eq_one.mp (le_antisymm b7 (Cpr af))
     exact Wn k a7 aa ag
 · have ay:k.IC.card=1:=by have:=Cpr (Nem aa);omega
   have⟨v,b6⟩:=card_eq_one.mp ay;exact Bm k a7 ax b6
end CtxSec
end Ia2Compact
lemma VR (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty)(hIa2:2<=(N C a 0∩N C a 1).card)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): Bd C:=by
 have ha:a∈Jk C:=by simp[hs]
 have g:(Mw C a).card<=1:=Qa Q3 hIa2
  (fun w hw v hv=>(Q1 hL.1 ha (I1 hv) (I2 hv)).2 w hw |>.symm)
 have⟨w0,hw0⟩:=Qk g;exact BT ⟨hL,hT,a,b,hs,hab,db,hrb,hno2,hB0ne,hIa2,hbWit,w0,hw0⟩
section Ia1TopCompact
open Finset
abbrev F1:=Fin 11
abbrev A1:=Ga
abbrev U1 (C:Ck):=Us C
abbrev W1 (C:Ck):=Mw C
abbrev TC (C:Ck):=Tc C
abbrev S1 (C:Ck)(g:ℕ)(d:Fin 2):Finset F1:=N C g d
abbrev SL:=@Q4 11
abbrev OR (C:Ck):=O C
abbrev Mf (C:Ck)(j:ℕ):=(mixing G11 C).filter fun m=>OR C (11+m) j
abbrev Yn (i:St C)(e:Sym2 F1):Prop:=∃x∈i.L,e=s(i.c,x)
abbrev CL (l:List (St C))(e:Sym2 F1):Prop:=∃i∈l,Yn i e
abbrev CO (v:F1)(E:Finset (Sym2 F1))(l:List (St C)):Prop:=∀u w,s(u,w)∈E->u≠v->w≠v->CL l s(u,w)
abbrev BO (C:Ck)(v:F1)(gs bs:List (St C)):Prop:=
 (∀g∈gs,∀b∈bs,g.c≠b.c)/\(∀b∈bs,b.c≠v)/\(∀b1∈bs,∀b2∈bs,b1.c=b2.c->b1=b2) /\
 (∀b1∈bs,∀b2∈bs,b1.c≠b2.c->(b1.W.biUnion (Oi C)∩b2.L).card<=1\/(b2.W.biUnion (Oi C)∩b1.L).card<=1)
abbrev G0 (C:Ck):Prop:=
 (Us C).card<=2*(centreless G11 C).card+2+(rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card
abbrev TW (C:Ck)(b:ℕ)(W2:Finset ℕ)(w:F1):Prop:=
 w∈W2.biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈Mf C b,OR C (opnd C t d) m/\w∈S1 C t (1-d)
lemma S0 {P:Prop}(h:P:=by simp):P:=h
lemma Pk {v:F1}{g:List (St C)}:BO C v g []:=⟨S0,S0,S0,S0⟩
lemma Wu {a:St C}(h:a.W.card=1:=by exact Cs _):([a].map (·.W.card)).sum<=1:=by simp[h]
lemma Ba {a:St C}(h:a.good:=by trivial):∀g∈[a],g.good:=by simp[h]
abbrev qE:=@Finset.eq_empty_or_nonempty
abbrev N4:=Q3
lemma qB {A B:Finset F1}(g:2<=B.card)(h:∀a∈A,∀b∈B,A1 a b):A.card<=1:=Qa N4 g h
abbrev qR:=@Qk
abbrev XH:=@QA
abbrev qG:=@Qh
lemma rR {P Q:Prop}(h:P\/Q)(n:¬Q):P:=h.resolve_right n
lemma rL {P Q:Prop}(h:P\/Q)(n:¬P):Q:=h.resolve_left n
section H
variable {α:Type*} {x y:α} {A B:Finset α}
lemma qf {p:α->Prop}[DecidablePred p](h:x∈A)(g:p x):x∈A.filter p:=Fk h g
lemma VB {p:α->Prop}[DecidablePred p](h:x∈A.filter p):x∈A:=(Fp h).1
lemma qF {p:α->Prop}[DecidablePred p](h:x∈A.filter p):x∈A/\p x:=Fp h
lemma qe (h:A.card<=1)(g:x∈A)(j:y∈A):x=y:=Qp h g j
lemma qn (g:A=∅)(h:x∈A):False:=notMem_empty x (g▸h)
lemma P6 (h:∀x∈A,False):A=∅:=Ee.mpr h
lemma q0 (h:x∈({y}:Finset α)):x=y:=Sp h
lemma B4 {P:Prop}[Decidable P](h:x∈if P then ({y}:Finset α) else ∅):x=y/\P:=by split_ifs at h with k;exact⟨q0 h,k⟩;exact(N0 h).elim
variable [DecidableEq α]
lemma qi (h:x∈A)(g:x∈B):x∈A∩B:=Im h g
lemma q1 (h:x∈A∩B):x∈A:=(I1 h)
lemma q2 (h:x∈A∩B):x∈B:=(I2 h)
lemma qs (h:x∈A)(g:x∉B):x∈A\B:=Dm h g
lemma K3 (h:x∈A\B):x∈A:=(D1 h)
lemma P9 (h:x∈A\B):x∉B:=(D2 h)
lemma qD (h:x∈A\B):x∈A/\x∉B:=Dp h
lemma VC (h:x∈A):x∈A∪B:=Ul B h
lemma W7 (h:x∈B):x∈A∪B:=Ur A h
lemma qU (h:x∈A∪B):x∈A\/x∈B:=Up h
lemma P4 (A B:Finset α):A.card<=(A\B).card+B.card:=
 (Cl fun x h=>if hb:x∈B then W7 hb else VC (qs h hb)).trans (Cu _ _)
lemma BZ (h:x∈B)(g:x∉A)(j:A⊆B):A.card+1<=B.card:=by have:=Cl (Ism ⟨h,j⟩);rwa[Cns g] at this
end H
lemma WM {m j}(h:m∈Mf C j):OR C (11+m) j:=(qF h).2
lemma XF {j}:Mf C j⊆mixing G11 C:=Fs _ _
lemma qw {x y:F1}:s(x,y)=s(y,x):=Sw
lemma ql {c x:F1}{E:Finset (Sym2 F1)}(h:s(c,x)∈E):x∈SL c E:=Zm h
lemma Ps {c x:F1}{E:Finset (Sym2 F1)}(h:s(x,c)∈E):x∈SL c E:=Zm (qw▸h)
lemma qm {c x:F1}{E:Finset (Sym2 F1)}(h:x∈SL c E):s(c,x)∈E:=Zl h
lemma q3 {g d}{x:F1}(h:x∈S1 C g d):x∈S1 C g (1-(1-d)):=by rwa[Qd]
lemma qc {g}{w:F1}(hL:Ao C)(h:TC C g w):w∈W1 C g:=Q5 hL h
lemma qA {a}{u w:F1}(h:s(u,w)∈Ya C a):A1 u w:=qG (Qu h)
lemma BF {a}{u w:F1}(h:s(u,w)∈Yu C a):A1 u w:=qG (XH h)
lemma V0 (j:ℕ):(W0For G11 C j).card<=(centreless G11 C).card:=(Qj (G:=G11) (C:=C) j).trans (Qs j)
lemma BP (a b:ℕ):(W0For G11 C a∪W0For G11 C b).card<=2*(centreless G11 C).card:=by have:=V0 (C:=C) a;have:=V0 (C:=C) b;have:=Cu (W0For G11 C a) (W0For G11 C b);omega
lemma qM {a}{e:Sym2 F1}(he:e∈U1 C)(g:e∉Yu C a)(hW:e∉Yx C a):e∈Ya C a:=qs (qs he g) hW
lemma Bb {a}{e:Sym2 F1}(he:e∈U1 C)(hW:e∉Yx C a):e∈Yu C a∪Ya C a:=
 if h:e∈Yu C a then VC h else W7 (qM he h hW)
lemma XY {v:F1}{E:Finset (Sym2 F1)}{P:Sym2 F1->Prop}(hv:∀w,s(v,w)∈E->P s(v,w))(g:∀u w,s(u,w)∈E->u≠v->w≠v->P s(u,w)):∀e∈E,P e:=fun e h=>by
 induction e using Sym2.ind with| _ u w=>
 by_cases a:u=v;· subst u;exact hv w h
 by_cases b:w=v;· subst w;rw[qw];exact hv u (qw▸h)
 exact g u w h a b
lemma Bv {v b:F1}{E:Finset (Sym2 F1)}{P:Sym2 F1->Prop}(hv:∀w,s(v,w)∈E->P s(v,w))(hb:∀w,s(b,w)∈E->w≠v->P s(b,w))(g:∀u w,s(u,w)∈E->u≠v->w≠v->u≠b->w≠b->P s(u,w)):∀e∈E,P e:=
 XY hv fun u w h a c=>by
  by_cases d:u=b;· subst u;exact hb w h c
  by_cases f:w=b;· subst w;rw[qw];exact hb u (qw▸h) a
  exact g u w h a c d f
lemma BA {g j:List (St C)}{e}(h:CL g e)(hs:∀x∈g,x∈j):CL j e:=by have⟨i,q,r⟩:=h;exact⟨i,hs i q,r⟩
lemma V1 {a b:List (St C)}{e}(h:CL a e):CL (a++b) e:=BA h fun _=>Kal _
lemma P7 {a b:List (St C)}{e}(h:CL b e):CL (a++b) e:=BA h fun _=>Kar _
lemma K5 {x:St C}{a:List (St C)}{e}(h:CL a e):CL (x::a) e:=BA h fun _=>Km _
lemma QX {x:St C}{l:List (St C)}{e}(h:Yn x e):CL (x::l) e:=⟨x,Kc,h⟩
lemma Zb {a b:St C}{l:List (St C)}{e}(h:Yn a e\/Yn b e):CL (a::b::l) e:=h.elim QX (K5∘QX)
lemma kL {s:St C}{u w:F1}{E}{T:Finset F1}(h:s(u,w)∈E)(t:w∈T)(e:u=s.c:=by rfl)(hL:s.L=SL s.c E∩T:=by rfl):Yn s s(u,w):=⟨w,hL▸qi (ql (e▸h)) t,e▸rfl⟩
lemma kR {s:St C}{u w:F1}{E}{T:Finset F1}(h:s(u,w)∈E)(t:u∈T)(e:w=s.c:=by rfl)(hL:s.L=SL s.c E∩T:=by rfl):Yn s s(u,w):=⟨u,hL▸qi (Ps (e▸h)) t,e▸qw⟩
lemma kS {s:St C}{u w:F1}{E}{T:Finset F1}(h:s(u,w)∈E)(ho:(u=s.c/\w∈T)\/(w=s.c/\u∈T))(hL:s.L=SL s.c E∩T:=by rfl):Yn s s(u,w):=
 ho.elim (fun ⟨e,t⟩=>kL h t e hL) fun ⟨e,t⟩=>kR h t e hL
abbrev qW (c:F1)(L:Finset F1)(w:ℕ)(hw:w<11+C.gates.length)(hL:L⊆Oi C w)(he:∀x∈L,s(c,x)∈U1 C):St C:=
 Q0 C c L w hw hL he False False.elim
def E1 (C:Ck)(a b:ℕ)(db d:Fin 2)(v:F1):Finset (Sym2 F1):=
 (Ya C a).filter fun e=>∃u w:F1,e=s(u,w)/\u≠v/\w≠v /\
  u∈(S1 C a d\S1 C a (1-d))∩W1 C b/\w∈(S1 C a (1-d)\S1 C a d)∩S1 C b (1-db)
lemma Vm {a b db d v}:E1 C a b db d v⊆U1 C:=(Fs _ _).trans Qu
lemma WE {a b db d v e}(h:E1 C a b db (1-d) v=∅)(ho:e∈E1 C a b db 0 v\/e∈E1 C a b db 1 v):e∈E1 C a b db d v:=by fin_cases d<;>simp_all
lemma P8 {a b db v}(h:E1 C a b db 0 v=∅\/E1 C a b db 1 v=∅)(hn:(E1 C a b db 0 v∪E1 C a b db 1 v).Nonempty): ∃d,E1 C a b db (1-d) v=∅/\(E1 C a b db d v).Nonempty:=by have⟨e,he⟩:=hn;rcases h with h0|g;exact⟨1,h0,⟨e,rL (qU he) (qn h0)⟩⟩;exact⟨0,g,⟨e,rR (qU he) (qn g)⟩⟩
structure T1 (C:Ck) (a b:ℕ) (db:Fin 2) (v:F1):Prop where
 hl:Ls C
 ht:Tf C
 hs:Jk C={a,b}
 ha':Ic C a b
 hr:OR C (opnd C b db) a
 hn:¬OR C (opnd C b (1-db)) a
 h0:(S1 C b db).Nonempty
 hv:S1 C a 0∩S1 C a 1={v}
 hw:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,OR C (11+m) b
lemma Pm (hL:Ls C){v:F1}{Lv:Finset F1}{Wc Mc:Finset ℕ}(hM:Mc⊆mixing G11 C)(hW:∀z∈Wc,z<11+C.gates.length)(hN:∀z∈Wc,∀x∈Oi C z,A1 v x)(g:∀w∈Lv,s(v,w)∈U1 C)(a7:∀w∈Lv,w∈Wc.biUnion (Oi C)\/ ∃t∈Tp C,∃d:Fin 2,∃m∈Mc,OR C (opnd C t d) m/\w∈S1 C t (1-d))(c:F1)(l:List (St C))(hb:∀i∈l,i.c≠c->i.good)(hc:∀e∈U1 C,(∃w∈Lv,e=s(v,w))\/CL l e): ∃M⊆Mc,(Us C).card<=(rFull G11 C).card+Wc.card+(l.map (·.W.card)).sum+M.card /\ ∃f:ℕ->F1,(∀m∈M,f m∈Lv/\∃t∈Tp C,∃d:Fin 2,OR C (opnd C t d) m/\f m∈S1 C t (1-d)) /\ ∀m1∈M,∀m2∈M,m1≠m2->f m1≠f m2:=by
 have⟨L0,Lm,M,a6,q,a5,j,hLmc,f,hf,aa⟩:=QU (L:=Lv) (W_c:=Wc) hL.1 hM g a7;let iv:St C:=⟨v,L0,Wc,hW,j,fun _ h=>g _ (a5 h),True,fun _=>hN⟩;let Em:=Lm.image fun w=>s(v,w);have ah:(Us C).card<=(Us C\Em).card+M.card:=(P4 _ _).trans (A2l (Ci.trans hLmc.le) _)
 have a8:=Qw (E:=Us C\Em) hL.1 c (iv::l) (fun e h=>by
  obtain⟨eU,a4⟩:=qD h
  rcases hc e eU with⟨w,hw,rfl⟩|h';· rw[q] at hw;rcases qU hw with h0|hm;exact QX ⟨w,h0,rfl⟩;exact(a4 (Mi ⟨w,hm,rfl⟩)).elim
  exact K5 h') (by simp[iv];exact hb)
 simp only[Lmc,Lsc,iv] at a8;exact⟨M,a6,by omega,f,hf,aa⟩
lemma Br {a b}{w:F1}(h:TC C a w\/TC C b w): w∈(W0For G11 C a∪W0For G11 C b).biUnion (Oi C)\/∃t∈Tp C,∃d:Fin 2,∃m∈mixing G11 C,OR C (opnd C t d) m/\w∈S1 C t (1-d):=by
 rcases h with (h|⟨t,ht,d,m,g,hr,hw⟩)|(h|⟨t,ht,d,m,g,hr,hw⟩)<;>
  first|exact .inl (Bub _ Sul h)|exact .inl (Bub _ Sur h)|exact .inr ⟨t,ht,d,m,VB g,hr,hw⟩
section T1M
variable {a b:ℕ} {db:Fin 2} {v:F1} (K:T1 C a b db v)
include K
abbrev T1.L:=K.hl.1
abbrev T1.I (_:T1 C a b db v):=S1 C b db
abbrev T1.J (_:T1 C a b db v):=S1 C b (1-db)
abbrev T1.Z (_:T1 C a b db v):=S1 C b 0∩S1 C b 1
abbrev T1.R (_:T1 C a b db v):=W1 C a
abbrev T1.W (_:T1 C a b db v):=W1 C b
abbrev T1.S (_:T1 C a b db v)(d:Fin 2):=S1 C a d
abbrev T1.D (_:T1 C a b db v)(d:Fin 2):=S1 C a d\S1 C a (1-d)
abbrev T1.P (_:T1 C a b db v):=TC C a
abbrev T1.T (_:T1 C a b db v):=TC C b
abbrev T1.U (_:T1 C a b db v):=Yu C a
abbrev T1.Q (_:T1 C a b db v):=Yx C a
abbrev T1.X (_:T1 C a b db v):=Ya C a
abbrev T1.F (_:T1 C a b db v):=SL v (U1 C)
abbrev T1.E (_:T1 C a b db v)(d:Fin 2):=E1 C a b db d v
lemma T1.ha:a∈Jk C:=by simp[K.hs]
lemma T1.hb:b∈Jk C:=by simp[K.hs]
lemma T1.ne:a≠b:=Nlt (Y4 K.ha')
lemma T1.v0:v∈K.S 0:=q1 (K.hv▸Ss v)
lemma T1.v1:v∈K.S 1:=q2 (K.hv▸Ss v)
lemma T1.vd {d}:v∈K.S d:=by fin_cases d<;>[exact K.v0;exact K.v1]
lemma T1.nW:v∉K.R:=(Q1 K.L K.ha K.v0 K.v1).1
lemma T1.wN:∀w∈K.R,A1 v w:=(Q1 K.L K.ha K.v0 K.v1).2
lemma T1.bW:K.J∩K.W⊆K.R:=K7 K.L K.ht K.hs K.hr K.hn
lemma T1.s0:K.I∩K.J=K.Z:=by fin_cases db<;>[rfl;exact inter_comm _ _]
lemma T1.dS {d}:K.D (1-d)=K.S (1-d)\K.S d:=by dsimp[T1.D];rw[Qd]
lemma T1.nO {d}{x:F1}(h1:x∈S1 C b d)(hW:x∈K.W):x∉S1 C b (1-d):=fun h2=>
 (Q1 K.L K.hb (by fin_cases d<;>assumption) (by fin_cases d<;>assumption)).1 hW
lemma T1.w0 (j:ℕ){c:F1}(h:∀w∈W1 C j,A1 c w):∀z∈W0For G11 C j,∀x∈Oi C z,A1 c x:=fun z hz x hx=>h x (Qc K.L j z hz hx)
lemma T1.ni {z:F1}(h:z≠v):z∉K.S 0∩K.S 1:=fun m=>h (q0 (K.hv▸m))
lemma T1.sa {d}{z:F1}(h:z≠v)(g:z∈K.S d):z∈K.D d:=qs g fun m=>K.ni h (by fin_cases d<;>exact qi (by assumption) (by assumption))
lemma T1.ib {g:F1}(h:K.Z={g}):g∈S1 C b 0/\g∈S1 C b 1/\g∈K.I/\g∈K.J/\g∉K.W/\∀w∈K.W,A1 g w:=by have h0:g∈S1 C b 0:=q1 (h▸Ss g);have j:g∈S1 C b 1:=q2 (h▸Ss g);have hW:=Q1 K.L K.hb h0 j;exact⟨h0,j,by fin_cases db<;>assumption,by fin_cases db<;>assumption,hW.1,hW.2⟩
abbrev T1.mx:=QK K.L K.hs K.hr K.h0
abbrev T1.A2:=YJ K.hl K.ht K.hs K.ha' K.hv
abbrev T1.ec {u w:F1}(h:s(u,w)∈U1 C):=QM K.hl K.ht K.hs K.hr K.hn h
abbrev T1.ub {u w:F1}(h:s(u,w)∈K.U):=Kr K.hl K.ht K.hs K.hr K.hn h
abbrev T1.uW {u w:F1}(h:s(u,w)∈K.Q):=Kn K.hl K.ht K.hs K.hr K.hn h
abbrev T1.eb {u w:F1}(h:s(u,w)∈K.X):=Zr K.hl K.ht K.hs K.hr K.hn h
abbrev T1.gS {u w:F1}(h:Gv C a (Pi u w)=true)(hu:u≠v)(hw:w≠v):=Qt K.L K.ht K.hs K.ha' h (K.ni hu) (K.ni hw)
lemma T1.gV {w:F1}:Gv C a (Pi v w)=true:=(Qv K.L K.ht K.hs K.ha' _).mpr ⟨⟨v,K.v0,Q8 ..⟩,⟨v,K.v1,Q8 ..⟩⟩
abbrev T1.vE {Lv:Finset F1}:=Yw K.hl K.hs K.ha' K.hw K.v0 K.v1 (Lv:=Lv)
lemma T1.A: (∃l:List (St C),(l.map (·.W.card)).sum<=1/\(∀i∈l,i.good/\i.c∈K.R)/\CO v K.Q l)\/ (∃i0 i1:St C,i0.c∈K.R/\i1.c∈K.R/\i0.good/\i1.good/\i0.W.card=1/\i1.W.card=1/\∀e∈K.Q,Yn i0 e\/Yn i1 e):=by
 rcases Vx K.hl K.ht K.hs K.ha' K.hr K.hn K.hv K.A2.1 K.A2.2.1 with h|⟨c0,c1,h0,g,z⟩;exact .inl h
 obtain⟨i0,i1,e0,e1,j,q,w0,w1,_,_,t⟩:=WA K.hl K.ht K.hs K.ha' K.hr K.hn K.hv h0 g z;exact .inr ⟨i0,i1,e0▸q2 h0,e1▸q2 g,j,q,w0,w1,t⟩
lemma T1.p3 {u w:F1}{P:Prop}(he:s(u,w)∈U1 C)(h:s(u,w)∈K.U->P)(g:s(u,w)∈K.Q->P)(j:s(u,w)∈K.X->P):P:=
 if a:s(u,w)∈K.U then h a else if b:s(u,w)∈K.Q then g b else j (qM he a b)
lemma T1.p2 {u w:F1}{P:Prop}(he:s(u,w)∈U1 C\K.Q)(h:s(u,w)∈K.U->P)(g:s(u,w)∈K.X->P):P:=
 let ⟨e,hw⟩:=qD he;if b:s(u,w)∈K.U then h b else g (qM e b hw)
lemma T1.la {w:F1}{d}(hs:w∈K.S d)(hw:w∈K.R):∀y∈K.S (1-d),A1 w y:=Y1 K.L K.ht K.hs K.ha' hs hw
lemma T1.lb {w:F1}{d}(hs:w∈S1 C b d)(hw:w∈K.W):∀y∈S1 C b (1-d),A1 w y:=QC K.L K.hb hs hw
abbrev T1.M (d)(c:F1)(hS:c∈K.S d)(hW:c∈K.R):=Q9 K.L K.ha d c hS hW (U1 C) Subset.rfl
abbrev T1.B (d)(c:F1)(hS:c∈S1 C b d)(hW:c∈K.W)(E:Finset (Sym2 F1))(hE:E⊆U1 C):=Q9 K.L K.hb d c hS hW E hE
abbrev T1.V (h1:∀y∈K.J,A1 v y):=
 Q0 C v (K.F∩K.J) (opnd C b (1-db)) (Qe K.L K.hb (1-db)) Ir (fun _ h=>qm (q1 h)) True (fun _ y hy=>h1 y hy)
lemma T1.lv (g:v∉K.J):∀w∈K.F,K.P w\/w∈K.J:=fun w hw=>by
 rcases K.ec (qm hw) with⟨_,(h|h)|⟨h|h,_⟩|⟨_,h|h,_⟩⟩|⟨_,_,⟨x,hx,rfl|rfl⟩,_⟩<;>
  first|exact .inl ‹_›|exact .inr ‹_›|exact(K.nW (qc K.L ‹_›)).elim|exact(g ‹_›).elim
lemma T1.mU {w:F1}(he:s(v,w)∈U1 C)(hw:w∈K.R):s(v,w)∈K.Q:=
 qf (qs he fun h=>by have:=(K.ub h).1;rw[K.gV] at this;cases this) ⟨v,w,rfl,.inr hw⟩
lemma T1.uS {u w:F1}(he:s(u,w)∈K.U)(g:u∉K.Z)(hw:w∉K.Z):(u∈K.I/\w∈K.J)\/(u∈K.J/\w∈K.I):=by have h:=Yt (K.ub he).2.1 (K.ub he).2.2.1 g hw;fin_cases db<;>[exact h;exact h.symm]
lemma T1.uB {u w:F1}(h0:K.I∩K.W⊆{v})(he:s(u,w)∈K.U)(j:u≠v)(hw:w≠v)(g:u∉K.Z)(h:w∉K.Z): (u∈K.J∩K.W/\K.T u/\w∈K.I)\/(w∈K.J∩K.W/\K.T w/\u∈K.I):=by
 rcases K.uS he g h with⟨_,_⟩|⟨_,_⟩<;>rcases(K.ub he).2.2.2 with⟨_,_⟩|⟨_,_⟩
 ·exact(j (q0 (h0 (qi ‹_› ‹_›)))).elim
 ·exact .inr ⟨qi ‹_› ‹_›,‹_›,‹_›⟩
 ·exact .inl ⟨qi ‹_› ‹_›,‹_›,‹_›⟩
 ·exact(hw (q0 (h0 (qi ‹_› ‹_›)))).elim
lemma T1.uC {c:F1}(h0:K.I∩K.W⊆{v})(g:c∈K.J∩K.W)(h:(K.J∩K.W).card<=1){E}(z:E⊆U1 C)(t:K.U⊆E){u w:F1}(he:s(u,w)∈K.U)(hu:u≠v)(hw:w≠v)(j:u∉K.Z)(q:w∉K.Z): Yn (K.B (1-db) c (q1 g) (q2 g) E z) s(u,w):=
 kS (t he) ((K.uB h0 he hu hw j q).imp (fun ⟨a,_,b⟩=>⟨qe h a g,q3 b⟩) fun ⟨a,_,b⟩=>⟨qe h a g,q3 b⟩)
lemma T1.u2 (s:Fin 2){u w:F1}(he:s(u,w)∈K.U):∃x∈S1 C b s,x=u\/x=w:=by have:=K.ub he;fin_cases db<;>fin_cases s<;>first|exact this.2.1|exact this.2.2.1
lemma T1.u1 (s:Fin 2){q u w:F1}(h:∀y∈S1 C b s,y=q)(hn:q∉S1 C b (1-s))(he:s(u,w)∈K.U): (u=q/\w∈S1 C b (1-s))\/(w=q/\u∈S1 C b (1-s)):=by
 obtain⟨x,j,rfl|rfl⟩:=K.u2 s he<;>obtain rfl:=h x j<;>obtain⟨y,g,rfl|rfl⟩:=K.u2 (1-s) he<;>
  first|exact(hn g).elim|exact .inl ⟨rfl,g⟩|exact .inr ⟨rfl,g⟩
lemma T1.uO (h0:K.I∩K.W⊆{v})(j:K.Z⊆{v}): (∀u w,s(u,w)∈K.U->u=v\/w=v)\/∃c∈K.J∩K.W,K.T c/\∃z∈K.I,z≠v/\A1 c z:=by
 classical
 by_cases h:∀u w,s(u,w)∈K.U->u=v\/w=v;exact .inl h
 push Not at h;have⟨u,w,he,g,hw⟩:=h;have ha:=BF he
 exact .inr ((K.uB h0 he g hw (fun m=>g (q0 (j m))) (fun m=>hw (q0 (j m)))).elim
  (fun ⟨h1,hc,h2⟩=>⟨u,h1,hc,w,h2,hw,ha⟩) fun ⟨h1,hc,h2⟩=>⟨w,h1,hc,u,h2,g,ha.symm⟩)
lemma T1.lS {g:F1}(hn:g∉K.W):(∀w∈SL g (K.U∪K.X),s(g,w)∈U1 C)/\(∀w∈SL g (K.U∪K.X),K.T w):=
 ⟨fun _ h=>(qU (qm h)).elim (fun h=>XH h) (fun h=>Qu h),fun _ h=>by
  rcases qU (qm h) with h|h;have:=(K.ub h).2.2.2;grind;have:=(K.eb h).2.2.2;grind⟩
lemma T1.ed {d}{u w:F1}(he:s(u,w)∈K.E d): u∉K.R/\w∉K.R/\u≠v/\w≠v/\((u∈K.D d∩K.W/\w∈(K.S (1-d)\K.S d)∩K.J)\/(w∈K.D d∩K.W/\u∈(K.S (1-d)\K.S d)∩K.J)):=by obtain⟨g,u',w',e,_,_,_,_⟩:=qF he;have:=(K.eb g).2;rcases Sy2 e with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>grind
lemma T1.eP {u w:F1}(he:s(u,w)∈K.X)(g:u≠v)(hw:w≠v):s(u,w)∈K.E 0\/s(u,w)∈K.E 1:=by
 obtain⟨h,_,_,j⟩:=K.eb he
 have mk d (p q:F1) (e:s(u,w)=s(p,q)) hpv hqv (hp:p∈K.S d) (hq:q∈K.S (1-d)) hW hB:s(u,w)∈K.E d:=
  qf he ⟨p,q,e,hpv,hqv,qi (K.sa hpv hp) hW,qi (K.dS▸K.sa hqv hq) hB⟩
 rcases K.gS h g hw with⟨_,_⟩|⟨_,_⟩<;>rcases j with⟨_,_,_⟩|⟨_,_,_⟩<;>
  first|exact .inl (mk 0 u w rfl g hw ‹_› ‹_› ‹_› ‹_›)|exact .inr (mk 1 w u qw hw g ‹_› ‹_› ‹_› ‹_›)
        | exact .inr (mk 1 u w rfl g hw ‹_› ‹_› ‹_› ‹_›)|exact .inl (mk 0 w u qw hw g ‹_› ‹_› ‹_› ‹_›)
lemma T1.eU {u w:F1}(he:s(u,w)∈K.X)(g:u≠v)(hw:w≠v):s(u,w)∈K.E 0∪K.E 1:=(K.eP he g hw).elim VC W7
lemma T1.eS (d:Fin 2):∃i:St C,i.W.card=1/\((K.E d).Nonempty->i.c∉K.R/\i.c≠v)/\∀e∈K.E d,Yn i e:=by
 set t:=K.D d;set j:=K.S (1-d)\K.S d
 have hD:(t∩K.W).card<=1\/(j∩K.J).card<=1:=by
  by_contra! h;have:(t∩K.W).card<=1:=qB (by omega:2<=(j∩K.J).card) fun u hu y hy=>
   K9 K.L K.ht K.hs K.ha' K.hr d (K3 (q1 hu)) (q2 hu) (K3 (q1 hy)) (q2 hy);omega
 have z (i:St C) (w:i.W.card=1) (c:∀e∈K.E d,Yn i e):∃i:St C,i.W.card=1/\((K.E d).Nonempty->i.c∉K.R/\i.c≠v)/\∀e∈K.E d,Yn i e:=
  ⟨i,w,fun ⟨e,he⟩=>by obtain⟨x,_,q⟩:=c e he;have h:=K.ed (q▸he);exact⟨h.1,h.2.2.1⟩,c⟩
 rcases hD with hA|hB
 · have⟨c,g⟩:=qR hA
   exact z (qW c (SL c (K.E d)∩(j∩K.J)) (opnd C b (1-db)) (Qe K.L K.hb (1-db)) (Ir.trans Ir) fun _ h=>Vm (qm (q1 h)))
    (Cs _) fun e h=>by induction e using Sym2.ind with| _ u w=>exact kS h ((K.ed h).2.2.2.2.imp (fun ⟨a,b⟩=>⟨g u a,b⟩) fun ⟨b,a⟩=>⟨g w b,a⟩)
 · have⟨c,g⟩:=qR hB
   exact z (qW c (SL c (K.E d)∩(t∩K.W)) (opnd C a d) (Qe K.L K.ha d) (fun _ h=>K3 (q1 (q2 h))) fun _ h=>Vm (qm (q1 h)))
    (Cs _) fun e h=>by induction e using Sym2.ind with| _ u w=>exact kS h ((K.ed h).2.2.2.2.symm.imp (fun ⟨b,a⟩=>⟨g u a,b⟩) fun ⟨a,b⟩=>⟨g w b,a⟩)
abbrev T1.bc:=
 Yy K.L K.ht K.hs K.ha' K.hr K.hn K.A2.1 K.A2.2.1 (Vm (v:=v)) (Vm (v:=v))
  (fun _ _ h=>have h':=K.ed h;⟨h'.1,h'.2.1,h'.2.2.2.2⟩) (fun _ _ h=>have h':=K.ed h;⟨h'.1,h'.2.1,h'.2.2.2.2⟩)
lemma T1.a1 {d}{c0 u w:F1}(j:c0∈K.D d∩K.R)(g:(K.S (1-d)\K.S d)∩K.R=∅)(he:s(u,w)∈K.Q)(q:u≠v)(hw:w≠v): (u=c0/\w∈K.S (1-d))\/(w=c0/\u∈K.S (1-d)):=by
 have t:(K.D d∩K.R).card<=1:=by have:=K.A2;fin_cases d<;>[exact this.2.2.1;exact this.2.2.2]
 have hsd':(u∈K.S d/\w∈K.S (1-d))\/(u∈K.S (1-d)/\w∈K.S d):=by have h:=K.gS (K.uW he).1 q hw;fin_cases d<;>[exact h;exact h.symm]
 rcases hsd' with⟨_,_⟩|⟨_,_⟩<;>rcases(K.uW he).2 with _| _<;>
  first|exact .inl ⟨qe t (qi (K.sa q ‹_›) ‹_›) j,‹_›⟩|exact .inr ⟨qe t (qi (K.sa hw ‹_›) ‹_›) j,‹_›⟩
        | exact(qn g (qi (K.dS▸K.sa hw ‹_›) ‹_›)).elim|exact(qn g (qi (K.dS▸K.sa q ‹_›) ‹_›)).elim
lemma T1.a0 {u w:F1}(h0:K.D 0∩K.R=∅)(g:K.D 1∩K.R=∅)(he:s(u,w)∈K.Q):u=v\/w=v:=by
 by_contra! h
 rcases K.gS (K.uW he).1 h.1 h.2 with⟨_,_⟩|⟨_,_⟩<;>rcases(K.uW he).2 with _| _<;>
  first|exact qn h0 (qi (K.sa h.1 ‹_›) ‹_›)|exact qn g (qi (K.sa h.2 ‹_›) ‹_›)|exact qn g (qi (K.sa h.1 ‹_›) ‹_›)|exact qn h0 (qi (K.sa h.2 ‹_›) ‹_›)
lemma T1.tA {p q w:F1}(h:p∈K.S 0)(g:q∈K.S 1)(hw:w∈K.R):A1 p q\/A1 p w\/A1 q w:=
 Ka hw ((Qv K.L K.ht K.hs K.ha' _).mpr ⟨⟨p,h,tripleInput_1 ..⟩,⟨q,g,tripleInput_2 ..⟩⟩)
lemma T1.tB {z q w:F1}(h:z∈K.I)(g:q∈K.J)(hw:w∈K.W):A1 z q\/A1 z w\/A1 q w:=
 Ka hw ((QR K.L K.ht K.hs K.hr K.hn _).mpr ⟨.inr ⟨z,h,tripleInput_1 ..⟩,⟨q,g,tripleInput_2 ..⟩⟩)
lemma T1.b0 (h2:2<=K.J.card)(g:∀y∈K.J,A1 v y):K.I∩K.W⊆{v}:=fun x hx=>by
 by_contra hn;rw[mem_singleton] at hn
 have:=(Cl fun y hy=>qf (Uv _) ⟨g y hy,K.lb (q1 hx) (q2 hx) y hy⟩).trans (N4 v x (Ne.symm hn));omega
lemma T1.b1 {z:F1}(g:∀y∈K.J,A1 v y)(h:z∈K.I)(hzv:z≠v):(K.J∩K.W).card<=1:=
 (Cl fun y hy=>qf (Uv _) ⟨g y (q1 hy),(K.lb (q1 hy) (q2 hy) z (q3 h)).symm⟩).trans (N4 v z hzv.symm)
lemma T1.i1 (g:2<=K.W.card):K.Z.card<=1:=qB g fun _ hx y hy=>(Q1 K.L K.hb (q1 hx) (q2 hx)).2 y hy
lemma T1.w1 {g:F1}(j:∀w∈K.W,w=g):∃i:St C,i.c=g/\i.W.card=1/\∀u w,s(u,w)∈K.U->Yn i s(u,w):=by
 obtain⟨d,hn⟩:∃d,g∈K.W->g∉S1 C b d:=by by_cases h0:g∈S1 C b 0;exact⟨1-0,fun hW=>K.nO h0 hW⟩;exact⟨0,fun _=>h0⟩
 refine⟨qW g (SL g K.U) (opnd C b d) (Qe K.L K.hb d) (fun x hx=>by
  have he:=qm hx;exact Ym (K.ub he).2.1 (K.ub he).2.2.1 (hn (by rcases(K.ub he).2.2.2 with⟨h,_⟩|⟨h,_⟩;exact h;exact j x h▸h))) (fun _ h=>XH (qm h)),
  rfl,Cs _,fun u w he=>by
   rcases(K.ub he).2.2.2 with⟨h,_⟩|⟨h,_⟩
   ·obtain rfl:=j u h;exact⟨w,ql he,rfl⟩
   ·obtain rfl:=j w h;exact⟨u,Ps he,qw⟩⟩
lemma T1.f1 (c:F1)(l:List (St C))(hs:(l.map (·.W.card)).sum<=4)(hb:∀i∈l,i.c≠c->i.good)(h:∀e∈U1 C,CL l e):G0 C:=by obtain⟨m,j,g,_,_⟩:=K.mx;have:=QN K.L K.hb j g K.hw;have:=Qw (E:=Us C) K.L c l h hb;omega
lemma T1.wl:∀z∈W0For G11 C a∪W0For G11 C b,z<11+C.gates.length:=fun z h=>(qU h).elim (Qg K.L a z) (Qg K.L b z)
lemma T1.JD (g:∀w∈K.W,A1 v w):∀z∈W0For G11 C a∪W0For G11 C b,∀x∈Oi C z,A1 v x:=fun z h=>(qU h).elim (K.w0 a K.wN z) (K.w0 b g z)
lemma T1.fa (j:∀w∈K.W,A1 v w)(g:∀w∈K.F,K.P w\/K.T w)(c:F1)(l:List (St C))(hs:(l.map (·.W.card)).sum<=2)(hb:∀i∈l,i.c≠c->i.good)(t:CO v (U1 C) l):G0 C:=by
 obtain⟨M,q,z,_⟩:=Pm K.hl Subset.rfl K.wl (K.JD j) (fun _ h=>qm h) (fun w h=>Br (g w h)) c l hb
  (XY (fun w h=>.inl ⟨w,ql h,rfl⟩) fun u w h hu hw=>.inr (t u w h hu hw))
 have:=BP (C:=C) a b;have:=Cl q;omega
lemma T1.fm (z:∀w∈K.W,A1 v w)(gs bs:List (St C))(hs:(gs.map (·.W.card)).sum+(bs.map (·.W.card)).sum<=3)(hg:∀g∈gs,g.good)(ok:BO C v gs bs)(hc:CO v (U1 C) (gs++bs))(q:∀w∈K.F,¬K.T w->CL (gs++bs) s(v,w)):G0 C:=by
 classical
 obtain⟨m,j,lt,_,_⟩:=K.mx;set Lb:=K.F.filter fun w=>K.T w
 obtain⟨M,hM,a5,_⟩:=KU (E:=Us C) K.L XF (Qg K.L b) (K.w0 b z) (fun _ h=>qm (VB h)) (fun _ h=>(qF h).2) gs bs hg ok.1 ok.2.1 ok.2.2.1 ok.2.2.2
  (XY (fun w h=>if t:K.T w then .inl ⟨w,qf (ql h) t,rfl⟩ else .inr (q w (ql h) t)) fun u w h hu hw=>.inr (hc u w h hu hw))
 have hn:m∉M:=fun h=>by have:=Qy K.L j K.hb (WM (hM h));omega
 have:=V0 (C:=C) b;have:=BZ j hn (hM.trans XF);omega
lemma T1.fv (z:∀y∈K.J,A1 v y)(q:∀w∈K.F,K.P w\/w∈K.J)(c:F1)(l:List (St C))(hs:(l.map (·.W.card)).sum<=2)(hb:∀i∈l,i.c≠c->i.good)(hc:CO v (U1 C) l):G0 C:=by
 let g:=K.V z
 have⟨M,hM,j,f,hf,t⟩:=Pm K.hl XF (Qg K.L a) (K.w0 a K.wN) (Lv:=K.F\K.J)
  (fun _ h=>qm (K3 h)) (fun w h=>rR (q w (K3 h)) (P9 h)) c (g::l) (by simp[g,T1.V,Q0];exact hb)
  (XY (fun w h=>if b:w∈K.J then .inr (QX (kL h b)) else .inl ⟨w,qs (ql h) b,rfl⟩) fun u w h hu hw=>.inr (K5 (hc u w h hu hw)))
 have:=KG K.L N4 K.ha K.hb K.ne (hM.trans XF) (fun _ hm=>WM (hM hm)) (fun _ h=>qm (K3 h)) hf t K.hw
 simp[g,T1.V,Q0] at j;omega
lemma T1.fG (t:∀y∈K.J,A1 v y)(q:∀w∈K.F,K.P w\/w∈K.J)(gs bs:List (St C))(hs:(gs.map (·.W.card)).sum+(bs.map (·.W.card)).sum<=2)(z:∀g∈gs,g.good)(ok:BO C v gs bs)(hc:CO v (U1 C) (gs++bs)):G0 C:=by
 let j:=K.V t
 exact K.vE (Lv:=K.F\K.J) (fun _ h=>qm (K3 h)) (fun w h=>rR (q w (K3 h)) (P9 h)) (j::gs) bs
  (by simp[j,T1.V,Q0];omega) (by simp[j,T1.V,Q0];exact z) (by simp[j,T1.V,Q0];exact⟨fun b hb=>(ok.2.1 b hb).symm,ok.1⟩) ok.2.1 ok.2.2.1 ok.2.2.2
  (XY (fun w h=>if b:w∈K.J then .inr (QX (kL h b)) else .inl ⟨w,qs (ql h) b,rfl⟩) fun u w h hu hw=>.inr (K5 (hc u w h hu hw)))
lemma T1.fO (h1:∀y∈K.J,A1 v y)(a3:∀w∈K.F,K.P w\/w∈K.J)(gs bs:List (St C))(hs:(gs.map (·.W.card)).sum+(bs.map (·.W.card)).sum<=1)(hg:∀g∈gs,g.good)(ok:BO C v gs bs)(z:∀b∈bs,b.c∉K.R)(hc:CO v (U1 C\K.Q) (gs++bs)):G0 C:=by
 rcases K.A with⟨la,sA,gA,j⟩|⟨i0,i1,a5,a6,g0,g1,w0,w1,j⟩
 · exact K.fG h1 a3 (la++gs) bs (by simp;omega) (by grind) ⟨by grind,ok.2⟩ fun u w h hu hw=>
    if m:s(u,w)∈K.Q then V1 (V1 (j u w m hu hw)) else BA (hc u w (qs h m) hu hw) (by grind)
 · let q:=K.V h1
   exact Y5 K.hl K.hs K.hr K.h0 K.hw (i0::i1::q::gs) bs (by simp[q,T1.V,Q0,w0,w1];omega) (by simp[q,T1.V,Q0,g0,g1];exact hg)
    (XY (fun w h=>if m:s(v,w)∈K.Q then Zb (j _ m) else K5 (K5 (QX (kL h (rL (a3 w (ql h)) fun t=>m (K.mU h (qc K.L t)))))))
     fun u w h hu hw=>if m:s(u,w)∈K.Q then Zb (j _ m) else BA (hc u w (qs h m) hu hw) (by grind))
    (by simp[q,T1.V,Q0];exact⟨fun b hb e=>z b hb (e▸a5),fun b hb e=>z b hb (e▸a6),fun b hb=>(ok.2.1 b hb).symm,ok.1⟩) ok.2.2.1 ok.2.2.2
lemma T1.f0 (t:∀y∈K.J,A1 v y)(j:∀w∈K.F,K.P w\/w∈K.J)(gs:List (St C))(hs:(gs.map (·.W.card)).sum<=1)(q:∀g∈gs,g.good)(z:CO v (U1 C\K.Q) gs):G0 C:=
 K.fO t j gs [] (by simp;omega) q Pk S0 fun u w h hu hw=>by simpa using z u w h hu hw
lemma T1.fb {j:F1}(a5:v∉K.J)(h1:∀y∈K.J,A1 v y)(a3:∀w∈K.F,K.P w\/w∈K.J)(hI:K.Z={j})(hO:∀u w,s(u,w)∈U1 C->u≠v->w≠v->u≠j->w≠j->s(u,w)∈K.Q):G0 C:=by
 obtain⟨v0,v1,_,b1,nW,_⟩:=K.ib hI;have nv:j≠v:=fun e=>a5 (e▸b1);have⟨Le,Lc⟩:=K.lS nW;let z:=K.V h1
 rcases K.A with⟨la,sA,gA,q⟩|⟨i0,i1,_,_,g0,g1,w0,w1,q⟩
 · exact XQ K.hl K.hs K.ha' nv.symm K.v0 K.v1 v0 v1 (La:=K.F\K.J) (fun _ h=>qm (K3 h))
    (fun w h=>rR (a3 w (K3 h)) (P9 h)) Le Lc (z::la) [] (by simp[z,T1.V,Q0];omega) (by simp[z,T1.V,Q0];exact fun g h=>(gA g h).1) S0 S0 S0 S0 S0
    (Bv (fun w h=>if b:w∈K.J then .inr (.inr (QX (kL h b))) else .inl ⟨w,qs (ql h) b,rfl⟩)
     (fun w h hw=>if m:s(j,w)∈K.Q then .inr (.inr (V1 (K5 (q j w m nv hw)))) else .inr (.inl ⟨w,ql (Bb h m),rfl⟩))
     fun u w h hu hw hub hwb=>.inr (.inr (V1 (K5 (q u w (hO u w h hu hw hub hwb) hu hw)))))
 · exact KW K.hl K.hs K.hr K.h0 v0 v1 Le Lc [i0,i1,z] [] (by simp[z,T1.V,Q0,w0,w1]) (by simp[z,T1.V,Q0,g0,g1]) S0 S0 S0 S0
    (Bv (fun w h=>if m:s(v,w)∈K.Q then .inr (Zb (q _ m)) else .inr (K5 (K5 (QX (kL h (rL (a3 w (ql h)) fun t=>m (K.mU h (qc K.L t))))))))
     (fun w h _=>if m:s(j,w)∈K.Q then .inr (Zb (q _ m)) else .inl ⟨w,ql (Bb h m),rfl⟩)
     fun u w h hu hw hub hwb=>.inr (Zb (q _ (hO u w h hu hw hub hwb))))
set_option maxHeartbeats 500000 in
lemma T1.vc {j:F1}(ap:v∉K.J)(h1:∀y∈K.J,A1 v y)(ax:K.I∩K.W⊆{v})(a9:∀w∈K.F,K.P w\/w∈K.J)(hI:K.Z={j})(hE:∀u w,s(u,w)∈K.X->u=v\/w=v\/u=j\/w=j)(hV:s(v,j)∈U1 C->j∈K.R\/K.T v)(bj:∀c∈K.J∩K.W,∀z∈K.I,z≠v->z≠j->A1 c z->∀w2∈K.W,w2≠v->w2≠c->s(v,j)∈U1 C->¬K.P j->¬K.T v -> ∃W2⊆W0For G11 C b,(W0For G11 C a).card+W2.card+1<=2*(centreless G11 C).card/\∀w∈SL j (K.U∪K.X)\{c},TW C b W2 w):G0 C:=by
 classical
 obtain⟨mb,aq,b5,_,b8⟩:=K.mx;have⟨v0,v1,b0,b1,nW,hN⟩:=K.ib hI;have nv:j≠v:=fun e=>ap (e▸b1)
 by_cases ah:∀u w,s(u,w)∈K.U->u=v\/w=v\/u=j\/w=j
 ·exact K.fb ap h1 a9 hI fun u w h hu hw a4 a3=>by by_contra m;exact K.p2 (qs h m) (fun b=>by have:=ah u w b;grind) fun e=>by have:=hE u w e;grind
 push Not at ah;have⟨u0,w0,h0,ay,hw0,a4,a3⟩:=ah
 obtain⟨c1,z0,a5,ac,an,bf,b7⟩:∃c z,c∈K.J∩K.W/\z∈K.I/\z≠v/\z≠j/\A1 c z:=
  (K.uB ax h0 ay hw0 (fun m=>a4 (q0 (hI▸m))) (fun m=>a3 (q0 (hI▸m)))).elim
   (fun ⟨a,_,c⟩=>⟨u0,w0,a,c,hw0,a3,BF h0⟩) fun ⟨c,_,a⟩=>⟨w0,u0,c,a,ay,a4,(BF h0).symm⟩
 have cB:=q1 a5;have cW:=q2 a5;have cb:c1≠j:=fun e=>nW (e▸cW);let ic:=K.B (1-db) c1 cB cW (U1 C) Subset.rfl
 have au {u w:F1} (h:s(u,w)∈K.U) (hu:u≠v) (hw:w≠v) (a4:u≠j) (a3:w≠j):Yn ic s(u,w):=
  K.uC ax a5 (K.b1 h1 ac an) Subset.rfl XH h hu hw (fun m=>a4 (q0 (hI▸m))) (fun m=>a3 (q0 (hI▸m)))
 by_cases aj:K.W⊆{v,c1}
 · refine K.f0 h1 a9 [ic] Wu Ba fun u w h hu hw=>K.p2 h (fun bm=>?_) fun e=>by
    have e':=K.eb e;have:=K.bW a5;rcases e'.2.2.2 with⟨m,_,_⟩|⟨m,_,_⟩<;>(have:=aj m;grind)
   have mk (p q:F1) (pW:p∈K.W) (pv:p≠v) (h':s(p,q)∈K.U):p=c1/\q∈S1 C b (1-(1-db)):=by
    obtain rfl:p=c1:=by have:=aj pW;grind
    obtain⟨x,hx,rfl|rfl⟩:=(K.ub h').2.1;exact(cb (q0 (hI▸K.s0▸qi hx cB))).elim;exact⟨rfl,q3 hx⟩
   exact QX (kS (K3 h) ((K.ub bm).2.2.2.imp (fun ⟨m,_⟩=>mk u w m hu bm) fun ⟨m,_⟩=>mk w u m hw (qw▸bm)))
 have⟨w2,ad,bu⟩:=Nss aj
 have az:∀q∈K.J,q=j\/q=c1:=fun q hq=>by
  by_contra! hn;refine @Xx v j ?_ c1 ?_ ?_ z0 ?_ ?_ ?_ w2 ?_ ?_ ?_ q ?_ ?_ ?_ ?_<;>
   grind [K.tB ac hq ad,h1 j b1,h1 c1 cB,hN c1 cW,hN w2 ad,h1 q hq]
 have⟨Le,Lc⟩:=K.lS nW
 rcases K.A with⟨la,sA,gA,cA⟩|⟨i0,i1,_,_,g0,g1,bk,bd,cA⟩
 · set b6:=K.F.filter fun w=>w≠c1/\w≠j;set av:=SL j (K.U∪K.X)\{c1}
   let P:=s(v,j)∈U1 C/\¬K.P j/\¬K.T v
   obtain⟨W2,hW2s,hSk,HF,hW2e⟩:∃W2⊆W0For G11 C b,(W0For G11 C a).card+W2.card+(if P then 1 else 0)<=2*(centreless G11 C).card/\(∀w∈av,TW C b W2 w)/\(¬P->W2=W0For G11 C b):=by
    by_cases hp:P
    · have⟨W2,s2,c2,v2⟩:=bj c1 a5 z0 ac an bf b7 w2 ad (by grind) (by grind) hp.1 hp.2.1 hp.2.2
      exact⟨W2,s2,by simp[hp];exact c2,v2,fun h=>(h hp).elim⟩
    ·exact⟨W0For G11 C b,Subset.rfl,by have:=V0 (C:=C) a;have:=V0 (C:=C) b;simp[hp];omega,fun w h=>Lc w (K3 h),fun _=>rfl⟩
   let La:=b6∪(if s(v,j)∈U1 C/\K.P j then {j} else ∅);let Lb:=av∪(if s(v,j)∈U1 C/\K.T v then {v} else ∅);let Er:Finset (Sym2 F1):=(if P then {s(v,j)} else ∅)∪(if v∈K.I then ∅ else {s(v,c1)});have af:La⊆K.F:=Us2 (Fs _ _) fun _ h=>let ⟨e,k⟩:=B4 h;e▸ql k.1;have aw:Lb⊆SL j (U1 C):=Us2 (fun _ h=>ql (Le _ (K3 h))) fun _ h=>let ⟨e,k⟩:=B4 h;e▸Ps k.1;have b4:c1∉La:=fun h=>(qU h).elim (by grind) fun h=>cb (B4 h).1
   obtain⟨Ma,hMa,Mb,hMb,hbd,⟨fa,hfa,hfai⟩,⟨fb,hfb,hfbi⟩⟩:=
    Y9 (E:=Us C\Er) K.L XF XF (Qg K.L a) (fun z hz=>Qg K.L b z (hW2s hz)) (K.w0 a K.wN) (fun z hz=>K.w0 b hN z (hW2s hz))
     (fun _ h=>qm (af h)) (fun _ h=>qm (aw h))
     (fun w h=>(qU h).elim (fun h=>rR (a9 w (VB h)) fun k=>by have:=az w k;grind) fun h=>let ⟨e,k⟩:=B4 h;e▸k.2)
     (fun w h=>(qU h).elim (HF w) fun h=>let ⟨e,k⟩:=B4 h;e▸(hW2e fun p=>p.2.2 k.2)▸k.2)
     (ic::la) [] (by simp[ic,T1.B];exact fun g h=>(gA g h).1) S0 S0 S0 S0 S0
     (Bv (fun w h=>by
       obtain⟨eU,ar⟩:=qD h
       by_cases h1':w=c1;· subst w;by_cases vB:v∈K.I;exact .inr (.inr (QX (kR eU (q3 vB))));exact(ar (W7 (by simp[vB]))).elim
       by_cases h2':w=j
       · subst w;by_cases ta:K.P j;exact .inl ⟨j,W7 (by simp[eU,ta]),rfl⟩
         by_cases tb:K.T v;exact .inr (.inl ⟨v,W7 (by simp[eU,tb]),qw⟩);exact(ar (VC (by simp[P,eU,ta,tb]))).elim
       exact .inl ⟨w,VC (qf (ql eU) ⟨h1',h2'⟩),rfl⟩)
      (fun w h hw=>by
       obtain⟨eU,_⟩:=qD h
       by_cases m:s(j,w)∈K.Q;· exact .inr (.inr (V1 (K5 (cA j w m nv hw))))
       by_cases h1':w=c1;· subst w;exact .inr (.inr (QX (kR eU (q3 b0))))
       exact .inr (.inl ⟨w,VC (qs (ql (Bb eU m)) (by grind)),rfl⟩))
      fun u w h hu hw a4 a3=>K.p3 (K3 h) (fun b=>.inr (.inr (QX (au b hu hw a4 a3)))) (fun m=>.inr (.inr (V1 (K5 (cA u w m hu hw))))) fun e=>by have:=hE u w e;grind)
   have hM:=Kj K.L K.ha K.hb K.ne nv.symm K.wN hN
    (hMa.trans XF) (fun _ m=>WM (hMa m)) (hMb.trans XF) (fun _ m=>WM (hMb m)) (fun _ h=>qm (af h)) (fun _ h=>qm (aw h)) hfa hfai hfb hfbi
   have:=P4 (Us C) Er;simp[ic,T1.B] at hbd
   by_cases vB:v∈K.I
   · have:Er.card<=if P then 1 else 0:=by simp[Er,vB];split_ifs<;>simp
     have:=hM.1;omega
   · have:Er.card<=(if P then 1 else 0)+1:=(Cu _ _).trans (by split_ifs<;>simp)
     have:=hM.2 mb aq b5 fun w hw t ht d hr wt=>KF K.L K.hb aq b8 vB cB cW (h1 c1 cB) (qG (qm (af hw))) (fun e=>b4 (e▸hw)) ht hr wt;omega
 · let bh:=SL j (K.U∪K.X)∪(if s(v,j)∈U1 C/\K.T v then {v} else ∅)
   exact KW K.hl K.hs K.hr K.h0 v0 v1 (Lb:=bh)
    (fun _ h=>(qU h).elim (Le _) fun h=>let ⟨e,k⟩:=B4 h;e▸qw▸k.1)
    (fun _ h=>(qU h).elim (Lc _) fun h=>let ⟨e,k⟩:=B4 h;e▸k.2)
    [i0,i1,ic] [] (by simp[ic,T1.B,bk,bd]) (by simp[ic,T1.B,g0,g1]) S0 S0 S0 S0
    (Bv (fun w h=>if m:s(v,w)∈K.Q then .inr (Zb (cA _ m)) else by
      rcases az w (rL (a9 w (ql h)) fun t=>m (K.mU h (qc K.L t))) with rfl|rfl
      ·rcases hV h with wW|tb;exact(m (K.mU h wW)).elim;exact .inl ⟨v,W7 (by simp[h,tb]),qw⟩
      ·exact(m (K.mU h (K.bW a5))).elim)
     (fun w h _=>if m:s(j,w)∈K.Q then .inr (Zb (cA _ m)) else .inl ⟨w,VC (ql (Bb h m)),rfl⟩)
     fun u w h hu hw a4 a3=>K.p3 h (fun b=>.inr (K5 (K5 (QX (au b hu hw a4 a3))))) (fun m=>.inr (Zb (cA _ m))) fun e=>by have:=hE u w e;grind)
lemma T1.iO (q:∀w∈K.W,A1 v w)(j:∀w∈K.F,K.P w\/K.T w)(lb:List (St C))(sB:(lb.map (·.W.card)).sum<=1)(gB:∀i∈lb,i.good)(t:CO v (U1 C\K.Q) lb):G0 C:=by
 rcases K.A with⟨la,sA,gA,g⟩|⟨i0,i1,_,_,z,g1,w0,w1,g⟩
 · exact K.fa q j 0 (la++lb) (by simp;omega) (by grind) fun u w h hu hw=>
    if m:s(u,w)∈K.Q then V1 (g u w m hu hw) else P7 (t u w (qs h m) hu hw)
 · exact K.fm q (i0::i1::lb) [] (by simp[w0,w1];omega) (by simp[z,g1];exact gB) Pk
    (fun u w h hu hw=>if m:s(u,w)∈K.Q then Zb (g _ m) else V1 (K5 (K5 (t u w (qs h m) hu hw))))
    fun w hw nb=>Zb (g _ (K.mU (qm hw) (qc K.L (rR (j w hw) nb))))
set_option maxHeartbeats 500000 in
lemma T1.iB (hN:∀w∈K.W,A1 v w)(nW:v∉K.W)(a3:∀w∈K.F,K.P w\/K.T w)(hI:K.Z⊆{v})(b8:K.I∩K.W=∅):G0 C:=by
 classical
 have bb:K.I∩K.W⊆{v}:=b8▸empty_subset _
 obtain⟨lb,sB,gB,ci,cB⟩:
  ∃lb:List (St C),(lb.map (·.W.card)).sum<=1/\(∀i∈lb,i.good)/\(∀i∈lb,i.c∈K.J∩K.W/\K.T i.c/\∃z∈K.I,z≠v/\A1 i.c z)/\CO v K.U lb:=by
  rcases K.uO bb hI with bz|⟨c1,t,bu,z0,a6,ag,h1z⟩
  ·exact⟨[],S0,S0,S0,fun u w h j hw=>by have:=bz u w h;grind⟩
  · have b3:∀u∈K.J∩K.W,∀w∈K.I,w≠v->A1 u w->u=c1:=fun u j w hw hwv h=>by
     by_cases h2:2<=K.I.card
     ·exact qe (qB h2 fun x hx y hy=>K.lb (q1 hx) (q2 hx) y (q3 hy)) j t
     ·obtain rfl:w=z0:=qe (by omega) hw a6;by_contra hn;exact QV hwv.symm hn (hN u (q2 j)) h.symm (hN c1 (q2 t)) h1z.symm
    let it:=K.B (1-db) c1 (q1 t) (q2 t) K.U XH
    exact⟨[it],Wu,Ba,fun _ h=>by rw[Kl.mp h];exact⟨t,bu,z0,a6,ag,h1z⟩,fun u w h j hw=>
     QX (kS h ((K.uB bb h j hw (fun m=>j (q0 (hI m))) (fun m=>hw (q0 (hI m)))).imp
      (fun ⟨a,_,b⟩=>⟨b3 u a w b hw (BF h),q3 b⟩) fun ⟨a,_,b⟩=>⟨b3 w a u b j (BF h).symm,q3 b⟩))⟩
 have aj d (c:F1) (hc:c∈K.D d∩K.R):K.E d=∅:=P6 fun e h=>by obtain⟨eE,u,w,rfl,_,wv,j,hw⟩:=qF h;exact QV wv.symm (fun (eq:c=u)=>(K.eb eE).2.1 (eq▸q2 hc)) (K.wN c (q2 hc)) (K.la (K3 (q1 hc)) (q2 hc) w (K3 (q1 hw))).symm (hN u (q2 j)) (qA eE).symm
 have av da (c0:F1) (a4:c0∈K.D da∩K.R) (hOE:(K.S (1-da)\K.S da)∩K.R=∅):G0 C:=by
  have cD:=K3 (q1 a4);have cW:=q2 a4;have bp:K.E (1-(1-da))=∅:=by rw[Qd];exact aj da c0 a4
  have ab {u w:F1} (h:s(u,w)∈K.X) (j:u≠v) (hw:w≠v):s(u,w)∈K.E (1-da):=WE bp (K.eP h j hw);let ic:=K.M da c0 cD cW;have cc {u w:F1} (h:s(u,w)∈K.Q) (j:u≠v) (hw:w≠v):Yn ic s(u,w):=kS (K0 h) (K.a1 a4 hOE h j hw)
  rcases qE (K.E (1-da)) with bg|⟨eo,aw⟩
  · exact K.fa hN a3 0 (ic::lb) (by simp[ic,T1.M];omega) (by simp[ic,T1.M];exact fun i h _=>gB i h) fun u w h j hw=>
     K.p3 h (fun b=>K5 (cB u w b j hw)) (fun m=>QX (cc m j hw)) fun e=>(qn bg (ab e j hw)).elim
  have⟨io,wO,bd,cO⟩:=K.eS (1-da);have hop:=bd ⟨eo,aw⟩
  by_cases ak:lb=[]
  · exact K.fa hN a3 io.c [io,ic] (by simp[ic,T1.M,wO]) (by simp[ic,T1.M]) fun u w h j hw=>
     K.p3 h (fun b=>by obtain⟨_,Px,_⟩:=cB u w b j hw;rw[ak] at Px;cases Px) (fun m=>K5 (QX (cc m j hw))) fun e=>QX (cO _ (ab e j hw))
  obtain⟨eE,q,u0,rfl,_,c3,bf,bm⟩:=qF aw;have Pu:q∈(K.S (1-da)\K.S da)∩K.W:=by rwa[Qd] at bf
  have a7:u0∈K.D da∩K.J:=by rwa[Qd] at bm
  by_cases bl:∃w3∈K.R,w3≠c0
  · have⟨w3,ah,cd⟩:=bl
    have ba:∀y∈K.S (1-da)\K.S da,y≠v->y≠q->¬A1 c0 y:=fun y hy yv y1 cy=>by
     have ht:A1 u0 y\/A1 u0 w3\/A1 y w3:=by fin_cases da;exact K.tA (K3 (q1 a7)) (K3 hy) ah;exact(K.tA (K3 hy) (K3 (q1 a7)) ah).imp SimpleGraph.Adj.symm fun h=>h.symm
     refine @Z7 v c0 ?_ q ?_ w3 ?_ ?_ ?_ ?_ u0 ?_ ?_ ?_ y ?_ ?_ ?_ ?_<;>
      grind [(K.eb eE).2,K.wN c0 cW,hN q (q2 Pu),K.wN w3 ah,K.la cD cW q (K3 (q1 Pu)),qA eE]
    have b7:∀x∈(K.S (1-da)\K.S da)∩K.W,x=q:=fun x hx=>by by_contra hn;exact ba x (q1 hx) (fun e=>nW (e▸(q2 hx:x∈W1 C b))) hn (K.la cD cW x (K3 (q1 hx)))
    have hy (x:F1) (xv:x≠v) (xD:x∈K.S (1-da)) (cx:A1 c0 x):x=q:=by by_contra hn;exact ba x (K.dS▸K.sa xv xD) xv hn cx
    let an:=qW q (SL q (U1 C)∩K.S da) (opnd C a da) (Qe K.L K.ha da) Ir fun _ h=>qm (q1 h)
    exact K.fa hN a3 q (an::lb) (by simp[an,qW,Q0];omega) (by simp[an,qW,Q0];exact fun i h _=>gB i h) fun u w h j hw=>
     K.p3 h (fun b=>K5 (cB u w b j hw))
      (fun m=>QX (kS h ((K.a1 a4 hOE m j hw).symm.imp (fun ⟨e,k⟩=>⟨hy u j k (e▸(qG h).symm),e▸cD⟩) fun ⟨e,k⟩=>⟨hy w hw k (e▸qG h),e▸cD⟩)))
      fun e=>QX (kS h ((K.ed (ab e j hw)).2.2.2.2.imp (fun ⟨a,b⟩=>⟨b7 u (K.dS▸a),K3 (q1 (by rwa[Qd] at b))⟩) fun ⟨b,a⟩=>⟨b7 w (K.dS▸b),K3 (q1 (by rwa[Qd] at a))⟩))
  · have bj:∀w∈K.R,w=c0:=by grind
    exact K.fm hN (ic::lb) [io] (by simp[ic,T1.M,wO];omega) (by simp[ic,T1.M];exact gB)
     ⟨by simp[ic,T1.M];exact⟨fun e=>hop.1 (e▸cW),fun g h e=>hop.1 (e▸K.bW (ci g h).1)⟩,by simpa using hop.2,S0,S0⟩
     (fun u w h j hw=>K.p3 h (fun b=>V1 (K5 (cB u w b j hw))) (fun m=>QX (cc m j hw)) fun e=>P7 (QX (cO _ (ab e j hw))))
     fun w hw nb=>QX (kR (qm hw) K.vd (bj w (qc K.L (rR (a3 w hw) nb))))
 rcases qE (K.D 0∩K.R) with s0|⟨c0,a4⟩
 · rcases qE (K.D 1∩K.R) with s1|⟨c1,t⟩
   · have ay {u w:F1} (h:s(u,w)∈K.Q):=K.a0 s0 s1 h
     have⟨bs,cb,ak,b6,b9,bt⟩:=K.bc;have al:∀i∈bs,i.c∉K.R/\i.c≠v:=fun i hi=>by obtain⟨_,h⟩:=ak i hi;rcases qU h with h|h<;>(have h':=K.ed h;exact⟨h'.1,h'.2.2.1⟩)
     have ax:CO v (U1 C) (lb++bs):=fun u w h j hw=>K.p3 h (fun b=>V1 (cB u w b j hw)) (fun m=>by have:=ay m;grind) fun e=>P7 (bt _ (K.eU e j hw))
     have az d (hde:K.E (1-d)=∅):G0 C:=by
      obtain⟨id,wD,_,cD⟩:=K.eS d
      exact K.fa hN a3 id.c (id::lb) (by simp[wD];omega) (by simp;exact fun i h _=>gB i h) fun u w h j hw=>
       K.p3 h (fun b=>K5 (cB u w b j hw)) (fun m=>by have:=ay m;grind) fun e=>QX (cD _ (WE hde (K.eP e j hw)))
     rcases qE (K.E 0) with h0|⟨e0,bk⟩;· exact az 1 h0
     rcases qE (K.E 1) with h1|⟨e1,br⟩;· exact az 0 h1
     rcases lb with _|⟨ic,tl⟩
     · obtain⟨M,hM,bx,_⟩:=KU (E:=Us C) K.L Subset.rfl K.wl (K.JD hN) (fun _ h=>qm h) (fun w h=>Br (a3 w h)) [] bs S0 S0 (fun b hb=>(al b hb).2) b6 b9
        (XY (fun w h=>.inl ⟨w,ql h,rfl⟩) fun u w h j hw=>.inr (ax u w h j hw))
       have:=BP (C:=C) a b;have:=Cl hM;simp at bx;omega
     · have⟨cW,cc,z0,a6,ag,h1z⟩:=ci ic (Kc);have ca:=K.bW cW
       refine K.fm hN (ic::tl) bs (by omega) gB ⟨fun g hg b hb e=>(al b hb).1 (e▸K.bW (ci g hg).1),fun b hb=>(al b hb).2,b6,b9⟩ ax fun w4 hw4 nb=>?_
       exfalso;have au:=qc K.L (rR (a3 w4 hw4) nb)
       obtain⟨b4,x0,y1,rfl,_,ce,am,af⟩:=qF bk;obtain⟨b5,q,u0,rfl,_,c3,Pu,a7⟩:=qF br
       have:∀x∈K.J,x∈K.W->x∈K.R:=fun _ a b=>K.bW (qi a b)
       have:z0∉K.W:=fun h=>qn b8 (qi a6 h);have:z0∉K.J:=fun h=>ag (q0 (hI (K.s0▸qi a6 h)))
       refine @ZT v x0 ?_ q ?_ ?_ ic.c ?_ ?_ ?_ ?_ w4 ?_ ?_ ?_ ?_ ?_ y1 ?_ ?_ ?_ ?_ ?_ ?_ u0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ z0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_<;>
        grind [(K.eb b4).2,(K.eb b5).2,qA b4,qA b5,K.wN,
         K.tA (K3 (q1 am)) (K3 (q1 Pu)) ca,K.tA (K3 (q1 am)) (K3 (q1 Pu)) au,
         K.tA (K3 (q1 a7)) (K3 (q1 af)) ca,K.tA (K3 (q1 a7)) (K3 (q1 af)) au,
         K.tB a6 (q2 af) (q2 Pu),K.tB a6 (q2 a7) (q2 am)]
   ·exact av 1 c1 t s0
 · rcases qE (K.D 1∩K.R) with s1|⟨c1,t⟩;· exact av 0 c0 a4 s1
   have h0:=aj 0 c0 a4;have h1:=aj 1 c1 t;exact K.iO hN a3 lb sB gB fun u w h j hw=>K.p2 h (fun b=>cB u w b j hw) fun e=>(K.eP e j hw).elim (fun k=>(qn h0 k).elim) fun k=>(qn h1 k).elim
set_option maxHeartbeats 500000 in
lemma T1.iA {c0:F1}(af:v∈K.J)(hN:∀w∈K.W,A1 v w)(ab:∀w∈K.F,K.P w\/K.T w)(hI:K.Z⊆{v})(aj:(K.I∩K.W).card<=1)(ae:c0∈K.I∩K.W):G0 C:=by
 classical
 obtain⟨mb,au,_,b4,be⟩:=K.mx;have a8:=q1 ae;have a5:=q2 ae;have ag:=K.nO a8 a5;let j:=K.B db c0 a8 a5 (U1 C) Subset.rfl
 have ah:∀u w,s(u,w)∈K.X->u≠v->w≠v->Yn j s(u,w):=fun u w h hu hw=>by
  have h4 (x y:F1) (xW:x∈K.W) (y1:y∈K.J) (yv:y≠v) (xy:A1 x y):x=c0:=by by_contra hn;exact QV yv.symm (Ne.symm hn) (hN c0 a5) (K.lb a8 a5 y y1).symm (hN x xW) xy.symm
  exact kS (Qu h) ((K.eb h).2.2.2.imp (fun ⟨a,_,b⟩=>⟨h4 u w a b hw (qA h),b⟩) fun ⟨a,_,b⟩=>⟨h4 w u a b hu (qA h).symm,b⟩)
 have uS' {u w:F1} (h:s(u,w)∈K.U) (hu:u≠v) (hw:w≠v):=K.uS h (fun m=>hu (q0 (hI m))) (fun m=>hw (q0 (hI m)));let P1:=∃lb:List (St C),(lb.map (·.W.card)).sum<=1/\(∀i∈lb,i.good)/\CO v (U1 C\K.Q) lb
 have b8:P1\/∃c1∈(K.J\K.I)∩K.W,∀w∈K.W,w=c0\/w=c1:=by
  have am (h0:∀u w,s(u,w)∈K.U->u≠v->w≠v->(u=c0/\w∈K.J)\/(w=c0/\u∈K.J)):P1:=
   ⟨[j],Wu,Ba,fun u w h hu hw=>K.p2 h (fun bm=>QX (kS (K3 h) (h0 u w bm hu hw))) fun e=>QX (ah u w e hu hw)⟩
  by_cases aw:K.I.card<=1
  ·exact .inl (am fun u w bm hu hw=>(uS' bm hu hw).imp (fun ⟨x,y⟩=>⟨qe aw x a8,y⟩) fun ⟨x,y⟩=>⟨qe aw y a8,x⟩)
  rcases qE (K.J∩K.W) with b6|⟨c1,a4⟩
  · exact .inl (am fun u w bm hu hw=>by
     rcases uS' bm hu hw with⟨x,y⟩|⟨x,y⟩<;>rcases(K.ub bm).2.2.2 with⟨m,_⟩|⟨m,_⟩<;>
      first|exact .inl ⟨qe aj (qi x m) ae,y⟩|exact .inr ⟨qe aj (qi y m) ae,x⟩|exact(qn b6 (qi ‹_› m)).elim)
  have a3:=q1 a4;have t:=q2 a4;have a9:c1∉K.I:=by have:=K.nO a3 t;rwa[Qd] at this
  by_cases bb:∃w3∈K.W,w3≠c0/\w3≠c1
  · left;have⟨w3,ac,ay,av⟩:=bb
    have h0':c0∈(K.I\K.J)∩K.W:=qi (qs a8 ag) a5;have h1':c1∈(K.J\K.I)∩K.W:=qi (qs a3 a9) t
    have b3:(K.I\K.J)\{v}⊆{c0}\/(K.J\K.I)\{v}⊆{c1}:=by
     fin_cases db
     ·exact KN K.L K.hb h0' h1' ac (hN c0 a5) (hN c1 t) (hN w3 ac) ay av
     ·exact(KN K.L K.hb h1' h0' ac (hN c1 t) (hN c0 a5) (hN w3 ac) av ay).symm
    have a7:∀z:F1,z≠v->z∈K.I->z∉K.J:=fun z zv z0 z1=>zv (q0 (hI (K.s0▸qi z0 z1)))
    rcases b3 with s0|s1
    ·exact am fun u w bm hu hw=>(uS' bm hu hw).imp (fun ⟨x,y⟩=>⟨q0 (s0 (qs (qs x (a7 u hu x)) (by simp[hu]))),y⟩) fun ⟨x,y⟩=>⟨q0 (s0 (qs (qs y (a7 w hw y)) (by simp[hw]))),x⟩
    · let q:=K.B (1-db) c1 a3 t (U1 C) Subset.rfl
      exact⟨[q],Wu,Ba,fun u w h hu hw=>K.p2 h
       (fun bm=>QX (kS (K3 h) ((uS' bm hu hw).symm.imp (fun ⟨x,y⟩=>⟨q0 (s1 (qs (qs x fun h0=>a7 u hu h0 x) (by simp[hu]))),q3 y⟩) fun ⟨x,y⟩=>⟨q0 (s1 (qs (qs y fun h0=>a7 w hw h0 y) (by simp[hw]))),q3 x⟩)))
       fun e=>by rcases(K.eb e).2.2.2 with⟨_,_,m⟩|⟨_,_,m⟩;exact((K.eb e).2.2.1 (q0 (s1 (qs (qs m fun h0=>a7 w hw h0 m) (by simp[hw])))▸K.bW a4)).elim;exact((K.eb e).2.1 (q0 (s1 (qs (qs m fun h0=>a7 u hu h0 m) (by simp[hu])))▸K.bW a4)).elim⟩
  ·exact .inr ⟨c1,qi (qs a3 a9) t,by grind⟩
 rcases b8 with⟨lb,sB,gB,cB⟩|⟨c1,a4,an⟩;· exact K.iO hN ab lb sB gB cB
 have a3:=K3 (q1 a4);have a9:=P9 (q1 a4);have t:=q2 a4;let q:=K.B (1-db) c1 a3 t (U1 C) Subset.rfl
 have al:∀u w,s(u,w)∈K.U->u≠v->w≠v->Yn j s(u,w)\/Yn q s(u,w):=fun u w bm hu hw=>by
  have mk (x y:F1) (hx:x∈K.I) (hy:y∈K.J) (hW:x∈K.W\/y∈K.W) (he:s(x,y)∈U1 C):Yn j s(x,y)\/Yn q s(x,y):=by
   rcases hW with m|m<;>rcases an _ m with rfl|rfl;exact .inl (kL he hy);exact(a9 hx).elim;exact(ag hy).elim;exact .inr (kR he (q3 hx))
  have hW:u∈K.W\/w∈K.W:=(K.ub bm).2.2.2.imp And.left And.left
  rcases uS' bm hu hw with⟨x,y⟩|⟨x,y⟩;exact mk u w x y hW (XH bm);exact qw▸mk w u y x hW.symm (qw▸XH bm)
 rcases K.A with⟨la,sA,gA,cA⟩|⟨i0,i1,_,_,g0,g1,bn,bg,cA⟩
 · set Lv':=K.F.filter fun w=>¬(w=c0\/(w=c1/\v∈K.I))
   have ak:∀e∈U1 C,(∃w∈Lv',e=s(v,w))\/CL ((j::q::la)++[]) e:=
    XY (fun w h=>by
      by_cases k:w=c0\/(w=c1/\v∈K.I)
      ·rcases k with rfl|⟨rfl,vB⟩;exact .inr (QX (kR h af));exact .inr (K5 (QX (kR h (q3 vB))))
      ·exact .inl ⟨w,qf (ql h) k,rfl⟩) fun u w h hu hw=>
      K.p3 h (fun b=>.inr (Zb (al u w b hu hw))) (fun m=>.inr (V1 (K5 (K5 (cA u w m hu hw))))) fun e=>.inr (QX (ah u w e hu hw))
   have ar:∀g∈j::q::la,g.good:=by simp[j,q,T1.B];exact fun g h=>(gA g h).1
   by_cases aa:∀w∈Lv',K.P w
   ·exact K.vE (fun _ h=>qm (VB h)) aa (j::q::la) [] (by simp[j,q,T1.B];omega) ar S0 S0 S0 S0 ak
   · push Not at aa;have⟨ad,wL,wn⟩:=aa
     have bz:ad=c1:=rL (an ad (qc K.L (rL (ab ad (VB wL)) wn))) fun h=>(qF wL).2 (.inl h);subst ad;have b7:v∉K.I:=fun v0=>(qF wL).2 (.inr ⟨rfl,v0⟩);obtain⟨Mv,bh,bk,fw,bp,_⟩:=KU (E:=Us C) K.L Subset.rfl K.wl (K.JD hN) (fun _ h=>qm (VB h)) (fun w h=>Br (ab w (VB h))) (j::q::la) [] ar S0 S0 S0 S0 ak
     have mn:mb∉Mv:=fun h=>by obtain⟨bf,t0,ax,_,hr,wt⟩:=bp mb h;exact KF K.L (db:=db) K.hb au be b7 a3 t (hN c1 t) (qG (qm (VB bf))) (fun e=>wn (e▸K8 K.L K.ha ax (QH hr b4) wt)) ax hr wt
     have:=BZ au mn bh;have:=BP (C:=C) a b;simp[j,q,T1.B] at bk;omega
 · exact Y5 K.hl K.hs K.hr K.h0 K.hw [i0,i1,j,q] [] (by simp[j,q,T1.B,bn,bg]) (by simp[j,q,T1.B,g0,g1])
    (XY (fun w h=>if m:s(v,w)∈K.Q then Zb (cA _ m) else by
      rcases ab w (ql h) with ha|hb;· exact(m (K.mU h (qc K.L ha))).elim
      rcases an w (qc K.L hb) with rfl|rfl;exact K5 (K5 (QX (kR h af)));exact(m (K.mU h (K.bW (qi a3 t)))).elim)
     fun u w h hu hw=>K.p3 h (fun b=>K5 (K5 (Zb (al u w b hu hw)))) (fun m=>Zb (cA _ m)) fun e=>K5 (K5 (QX (ah u w e hu hw)))) S0 S0 S0
lemma T1.cq {q:F1}(ar:∀w∈K.F,K.P w\/w∈K.J)(z:∀y∈K.J,y=q)(hqv:q≠v)(aj:q∉K.W):G0 C:=by
 obtain⟨mb,a6,b3,_,_⟩:=K.mx;have⟨Le,Lc⟩:=K.lS aj;have⟨L0b,Lmb,Mb,hMbs,ak,af,a9,hLmc,fb,al,aa⟩:=QU (L:=SL q (K.U∪K.X)) (W_c:=W0For G11 C b) K.L XF Le Lc;let t:St C:=⟨q,L0b,W0For G11 C b,Qg K.L b,a9,fun _ h=>Le _ (af h),False,False.elim⟩
 have ah:∀u w,s(u,w)∈K.U∪K.X->u=q\/w=q:=fun u w h=>(qU h).elim
  (fun h=>by obtain⟨x,hx,rfl|rfl⟩:=(K.ub h).2.2.1;exact .inl (z _ hx);exact .inr (z _ hx))
  fun h=>by rcases(K.eb h).2.2.2 with⟨_,_,w1⟩|⟨_,_,u1⟩;exact .inr (z _ w1);exact .inl (z _ u1)
 have a7 {u w:F1} (hU:s(u,w)∈K.U∪K.X) (j:s(u,w)∉Lmb.image fun w=>s(q,w)):Yn t s(u,w):=by
  have mk (x:F1) (hx:x∈SL q (K.U∪K.X)) (hM':s(q,x)∉Lmb.image fun w=>s(q,w)):x∈L0b:=
   rR (qU (ak▸hx)) fun hm=>hM' (Mi ⟨x,hm,rfl⟩)
  rcases ah u w hU with rfl|rfl;exact⟨w,mk w (ql hU) j,rfl⟩;exact⟨u,mk u (Ps hU) (qw▸j),qw⟩
 rcases K.A with⟨la,sA,gA,cA⟩|⟨i0,i1,_,_,g0,g1,aq,am,cA⟩
 · set La:=K.F.erase q
   have⟨L0a,Lma,Ma,hMas,ag,ad,a4,au,fa,ap,ac⟩:=QU (L:=La) (W_c:=W0For G11 C a) K.L XF (fun _ h=>qm (erase_subset _ _ h))
     fun w h=>rR (ar w (mem_erase.mp h).2) fun k=>(mem_erase.mp h).1 (z w k)
   let iv:St C:=⟨v,L0a,W0For G11 C a,Qg K.L a,a4,fun _ h=>qm (erase_subset _ _ (ad h)),True,fun _=>K.w0 a K.wN⟩;let Em:=Lma.image (fun w=>s(v,w))∪Lmb.image (fun w=>s(q,w))∪{s(v,q)}
   have:Em.card<=Lma.card+Lmb.card+1:=(Cu _ _).trans (Nat.add_le_add_right ((Cu _ _).trans (Nat.add_le_add Ci Ci)) _)
   have:=P4 (Us C) Em
   have a3:=Qw (E:=Us C\Em) K.L q (iv::t::la)
    (XY (fun w h=>by
      obtain⟨eU,j⟩:=qD h;by_cases k:w=q;· subst w;exact(j (W7 (Ss _))).elim
      have wL:w∈La:=mem_erase.mpr ⟨k,ql eU⟩;rw[ag] at wL
      rcases qU wL with h0|hm;exact QX ⟨w,h0,rfl⟩;exact(j (VC (VC (Mi ⟨w,hm,rfl⟩)))).elim)
     fun u w h hu hw=>by
      obtain⟨eU,j⟩:=qD h
      exact if m:s(u,w)∈K.Q then K5 (K5 (cA u w m hu hw)) else K5 (QX (a7 (Bb eU m) fun k=>j (VC (W7 k)))))
    (by simp[iv,t];exact fun g h _=>(gA g h).1)
   have:=KS K.L K.ha K.hb K.ne hqv.symm K.wN (hMas.trans XF) (fun _ m=>WM (hMas m))
    (hMbs.trans XF) (fun _ m=>WM (hMbs m)) (fun _ h=>qm (erase_subset _ _ h)) Le ap ac al aa
   have:=V0 (C:=C) a;have:=V0 (C:=C) b;simp only[Lmc,Lsc,iv,t] at a3;omega
 · let Em:=Lmb.image fun w=>s(q,w)
   have:(Us C).card<=(Us C\Em).card+Mb.card:=(P4 _ _).trans (A2l (Ci.trans hLmc.le) _)
   have a3:=Qw (E:=Us C\Em) K.L q [i0,i1,t] (fun e h=>by
     obtain⟨eU,j⟩:=qD h;by_cases m:e∈K.Q;· exact Zb (cA e m)
     induction e using Sym2.ind with| _ u w=>exact K5 (K5 (QX (a7 (Bb eU m) j)))) (by simp[t,g0,g1])
   have mn:mb∉Mb:=fun h=>by have:=Qy K.L a6 K.hb (WM (hMbs h));omega
   have:=BZ a6 mn (hMbs.trans XF);have:=V0 (C:=C) b;simp only[Lmc,Lmn,Lsc,Lsn,t,aq,am] at a3;omega
set_option maxHeartbeats 500000 in
lemma T1.c0 (h1:∀y∈K.J,A1 v y)(bf:K.I∩K.W⊆{v})(aa:∀w∈K.F,K.P w\/w∈K.J)(a6:K.Z=∅):G0 C:=by
 classical
 have hbW':∀x∈K.J,x∈K.W->x∈K.R:=fun _ a b=>K.bW (qi a b)
 have ar d (c0:F1) (t:c0∈K.D d∩K.R):K.E d=∅\/K.E (1-d)=∅:=by
  by_contra! hn;have⟨e0,ay⟩:=hn.1;have⟨e1,b7⟩:=hn.2
  obtain⟨ah,x0,g,rfl,bh,_,a3,j⟩:=qF ay;obtain⟨aj,au,u0,rfl,c3,_,bj,bv⟩:=qF b7;have Pu:au∈(K.S (1-d)\K.S d)∩K.W:=by rwa[Qd] at bj
  have b3:u0∈K.D d∩K.J:=by rwa[Qd] at bv
  refine @X9 v c0 ?_ g ?_ ?_ u0 ?_ ?_ ?_ x0 ?_ ?_ ?_ ?_ ?_ au ?_ ?_ ?_ ?_ ?_ ?_ ?_<;>
   grind [(K.eb ah).2,(K.eb aj).2,(qA ah).symm,(qA aj).symm,K.wN c0 (q2 t),K.la (K3 (q1 t)) (q2 t)]
 have br (c1:F1) (a7:c1∈K.J∩K.W) (z0:F1) (z:z0∈K.I) (b4:z0≠v) (bg:A1 c1 z0):K.E 0=∅\/K.E 1=∅:=by
  by_contra! hn;have⟨e0,ay⟩:=hn.1;have⟨e1,b7⟩:=hn.2
  obtain⟨ah,x0,g,rfl,bh,_,a3,j⟩:=qF ay;obtain⟨aj,au,u0,rfl,c3,_,Pu,b3⟩:=qF b7;have cW:=K.bW a7;have:z0∉K.J:=fun h=>qn a6 (K.s0▸qi z h)
  refine @Xu v g ?_ u0 ?_ ?_ c1 ?_ ?_ ?_ ?_ x0 ?_ ?_ ?_ ?_ ?_ au ?_ ?_ ?_ ?_ ?_ ?_ ?_ z0 ?_ ?_ ?_ ?_ ?_ ?_<;>
   grind [(K.eb ah).2,(K.eb aj).2,(qA ah).symm,(qA aj).symm,K.wN c1 cW,
    K.tA (K3 (q1 b3)) (K3 (q1 j)) cW,K.tA (K3 (q1 a3)) (K3 (q1 Pu)) cW,K.tB z (q2 b3) (q2 a3),K.tB z (q2 j) (q2 Pu)]
 rcases K.uO bf (a6▸empty_subset _) with ch|⟨c1,a7,_,z0,z,b4,bg⟩
 · rcases qE (K.E 0∪K.E 1) with an|al
   ·exact K.f0 h1 aa [] S0 S0 fun u w h hu hw=>K.p2 h (fun b=>by grind) fun e=>(qn an (K.eU e hu hw)).elim
   by_cases hU':∀u w,s(u,w)∈K.Q->u=v\/w=v
   · have⟨bs,cc,bt,c6,c8,bn⟩:=K.bc
     exact K.fG h1 aa [] bs (by simp;omega) S0 ⟨S0,fun b hb=>by obtain⟨_,h⟩:=bt b hb;rcases qU h with h|h<;>exact(K.ed h).2.2.1,c6,c8⟩
      fun u w h hu hw=>K.p3 h (fun b=>by grind) (fun m=>by grind) fun e=>bn _ (K.eU e hu hw)
   · push Not at hU';have⟨ua,wa,ac,ab,ad⟩:=hU'
     have aw:K.E 0=∅\/K.E 1=∅:=by
      rcases K.gS (K.uW ac).1 ab ad with⟨_,_⟩|⟨_,_⟩<;>rcases(K.uW ac).2 with _| _<;>
       first|exact ar 0 ua (qi (K.sa ab ‹_›) ‹_›)|exact(ar 1 wa (qi (K.sa ad ‹_›) ‹_›)).symm
             | exact(ar 1 ua (qi (K.sa ab ‹_›) ‹_›)).symm|exact ar 0 wa (qi (K.sa ad ‹_›) ‹_›)
     have⟨d,ax,Pt⟩:=P8 aw al;have⟨ibc,b8,bm,az⟩:=K.eS d;have hib:=bm Pt
     exact K.fO h1 aa [] [ibc] (by simp[b8]) S0 ⟨S0,by simpa using hib.2,S0,S0⟩ (by simpa using hib.1) fun u w h hu hw=>
      K.p2 h (fun b=>by grind) fun e=>QX (az _ (WE ax (K.eP e hu hw)))
 · have ae:=K.bW a7;let ic:=K.B (1-db) c1 (q1 a7) (q2 a7) K.U XH
   have ap {u w:F1} (h:s(u,w)∈K.U) (hu:u≠v) (hw:w≠v):Yn ic s(u,w):=K.uC bf a7 (K.b1 h1 z b4) XH Subset.rfl h hu hw (fun m=>qn a6 m) (fun m=>qn a6 m);have aw:=br c1 a7 z0 z b4 bg
   rcases qE (K.E 0∪K.E 1) with an|al
   ·exact K.f0 h1 aa [ic] Wu Ba fun u w h hu hw=>K.p2 h (fun b=>QX (ap b hu hw)) fun e=>(qn an (K.eU e hu hw)).elim
   · obtain⟨d,ax,⟨e_d,he_d⟩⟩:=P8 aw al
     have b6 {u w:F1} (h:s(u,w)∈K.X) (hu:u≠v) (hw:w≠v):s(u,w)∈K.E d:=WE ax (K.eP h hu hw);obtain⟨eE,x0,g,rfl,bh,c5,a3,j⟩:=qF he_d;have cd:=(qA eE).symm;have ck:=(K.eb eE).2.1;have be:=(K.eb eE).2.2.1;have cf:=K.tB z (q2 j) (q2 a3);have cj:z0≠g:=fun e=>qn a6 (K.s0▸qi z (e▸q2 j))
     have am:(K.S (1-d)\K.S d)∩K.R=∅:=P6 fun c hc=>by
      refine @Zz v c ?_ g ?_ ?_ x0 ?_ ?_ ?_ ?_ c1 ?_ ?_ ?_ z0 ?_ ?_ ?_ ?_<;>
       grind [K.wN c (q2 hc),K.wN c1 ae,h1 g (q2 j),K.la (K3 (q1 hc)) (q2 hc) x0 (q3 (K3 (q1 a3)))]
     rcases qE (K.D d∩K.R) with cb|⟨c0,t⟩
     · obtain⟨ibc,b8,_,az⟩:=K.eS d
       exact K.fv h1 aa ibc.c [ic,ibc] (by simp[ic,T1.B,b8]) (by simp[ic,T1.B]) fun u w h hu hw=>
        K.p3 h (fun b=>QX (ap b hu hw)) (fun m=>by have:=(by fin_cases d<;>exact K.a0 (by assumption) (by assumption) m:u=v\/w=v);grind) fun e=>K5 (QX (az _ (b6 e hu hw)))
     · have a4:=q2 t;have af:=K3 (q1 t);have c0v:c0≠v:=fun e=>K.nW (e▸a4)
       have av:((K.S (1-d)\K.S d)∩K.J).card<=1:=(Cl fun y hy=>qf (Uv _) ⟨h1 y (q2 hy),K.la af a4 y (K3 (q1 hy))⟩).trans (N4 v c0 c0v.symm);let j0:=qW g (SL g (U1 C)∩K.S d) (opnd C a d) (Qe K.L K.ha d) Ir fun _ h=>qm (q1 h)
       have b5:∀e∈K.E d,Yn j0 e:=fun e h=>by
        induction e using Sym2.ind with| _ u w=>exact kS (Vm h) ((K.ed h).2.2.2.2.symm.imp (fun ⟨b,a⟩=>⟨qe av a j,K3 (q1 b)⟩) fun ⟨a,b⟩=>⟨qe av b j,K3 (q1 a)⟩)
       by_cases ak:∀u w,s(u,w)∈K.Q->u≠v->w≠v->u=g\/w=g
       · exact K.fv h1 aa g [ic,j0] (by simp[ic,j0,T1.B,qW,Q0]) (by simp[ic,j0,T1.B,qW,Q0]) fun u w h hu hw=>
          K.p3 h (fun b=>QX (ap b hu hw)) (fun m=>by
            rcases ak u w m hu hw with rfl|rfl<;>rcases K.a1 t am m hu hw with⟨k,_⟩|⟨k,_⟩<;>
             first|exact(be (k▸a4)).elim|exact K5 (QX (kL h (k▸af)))|exact K5 (QX (kR h (k▸af))))
           fun e=>K5 (QX (b5 _ (b6 e hu hw)))
       · push Not at ak;have⟨ua,wa,ac,ab,ad,c7,bu⟩:=ak
         obtain⟨w1,bd,cl,w1y,bk⟩:∃w1∈K.S (1-d),w1≠v/\w1≠g/\A1 c0 w1:=
          (K.a1 t am ac ab ad).elim (fun ⟨e,k⟩=>⟨wa,k,ad,bu,e▸qG (K0 ac)⟩)
           fun ⟨e,k⟩=>⟨ua,k,ab,c7,e▸(qG (K0 ac)).symm⟩
         have cg:A1 x0 w1\/A1 x0 c1\/A1 w1 c1:=by fin_cases d;exact K.tA (K3 (q1 a3)) bd ae;exact(K.tA bd (K3 (q1 a3)) ae).imp SimpleGraph.Adj.symm fun h=>h.symm
         have c4:=K.la af a4 g (K3 (q1 j));have bq:=h1 g (q2 j)
         have bz:c1=c0:=by
          by_contra hn
          have ce:w1≠c1:=fun e=>by subst e;exact QV c0v.symm w1y.symm bq c4 (K.wN w1 ae) bk
          refine @Xb v c0 ?_ g ?_ ?_ x0 ?_ ?_ ?_ c1 ?_ ?_ ?_ ?_ z0 ?_ ?_ ?_ ?_ w1 ?_ ?_ ?_ ?_ ?_ ?_<;>grind [K.wN c0 a4,K.wN c1 ae]
         subst bz
         have bp:∀q∈K.J,q=g\/q=c1:=fun q hq=>by
          by_contra! hn;refine @Xt v c1 ?_ g ?_ ?_ x0 ?_ ?_ ?_ z0 ?_ ?_ ?_ ?_ w1 ?_ ?_ ?_ ?_ ?_ q ?_ ?_ ?_ ?_ ?_<;>
           grind [K.tB z hq (q2 a3),K.wN c1 a4,h1 q hq]
         let aq:=K.M d c1 af a4;set La:=K.F.filter fun w=>w≠g/\w≠c1;have bx:c1≠g:=fun e=>be (e▸a4)
         exact K.vE (Lv:=La) (fun _ h=>qm (VB h)) (fun w h=>rR (aa w (VB h)) fun k=>by have:=bp w k;grind)
          [aq,ic] [j0] (by simp[aq,ic,j0,T1.M,T1.B,qW,Q0]) (by simp[aq,ic,T1.M,T1.B]) (by simp[aq,ic,j0,T1.M,T1.B,qW,Q0,bx]) (by simp[j0,qW,Q0,c5]) S0 S0
          (XY (fun w h=>by
            by_cases h1':w=g;· subst w;exact .inr (K5 (K5 (QX (kR h K.vd))))
            by_cases h2':w=c1;· subst w;exact .inr (QX (kR h K.vd))
            exact .inl ⟨w,qf (ql h) ⟨h1',h2'⟩,rfl⟩) fun u w h hu hw=>
            K.p3 h (fun b=>.inr (K5 (QX (ap b hu hw)))) (fun m=>.inr (QX (kS h (K.a1 t am m hu hw)))) fun e=>.inr (K5 (K5 (QX (b5 _ (b6 e hu hw))))))
end T1M
set_option maxHeartbeats 400000 in
lemma XW (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty){v:Fin 11}(a8:N C a 0∩N C a 1={v})(q:v∈N C b (1-db))(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): Bd C:=by
 classical
 let K:T1 C a b db v:=⟨hL,hT,hs,hab,hrb,hno2,hB0ne,a8,hbWit⟩;have⟨nW,hN⟩:=YG hL.1 hT hs hab hrb hno2 K.v0 K.v1 q;have nJ:¬Joint G11 C a b:=fun h=>K.nW (QP hL.1 hT hs hrb hno2 h q)
 have a5:∀w∈K.F,K.P w\/K.T w:=fun w h=>by
  rcases K.ec (qm h) with⟨_,(h1|h2)|⟨_,h1|h2⟩|⟨hJ,_⟩⟩|⟨_,_,_,⟨ax,_⟩|⟨_,h2⟩⟩<;>
   first|exact .inl ‹_›|exact .inr ‹_›|exact(K.nW (qc hL.1 ‹_›)).elim|exact(nW (qc hL.1 ‹_›)).elim|exact(nJ ‹_›).elim
 by_cases w1:K.W.card<=1
 · have⟨j,a3⟩:=qR w1
   have hR:∀e∈U1 C\K.Q,∃x∈SL j (U1 C\K.Q),e=s(j,x):=fun e he=>by
    induction e using Sym2.ind with| _ u w=>
    have:u∈K.W\/w∈K.W:=K.p2 he (fun h=>(K.ub h).2.2.2.imp And.left And.left) fun h=>(K.eb h).2.2.2.imp And.left And.left
    rcases this with t|hw
    ·obtain rfl:=a3 u t;exact⟨w,ql he,rfl⟩
    ·obtain rfl:=a3 w hw;exact⟨u,Ps he,qw⟩
   obtain⟨ib,cb,wb1,cB⟩:∃i:St C,i.c=j/\i.W.card=1/\∀e∈U1 C\K.Q,Yn i e:=by
    by_cases m:j∈K.R
    · have ad:K.X=∅:=P6 fun e h=>by induction e using Sym2.ind with| _ u w=>have:=(K.eb h).2;grind
      have⟨i,ci,wi,ae⟩:=K.w1 a3
      exact⟨i,ci,wi,fun e h=>by induction e using Sym2.ind with| _ u w=>exact K.p2 h (ae u w) fun e=>(qn ad e).elim⟩
    · have a7:j∈K.W->j∉K.J:=fun hW h1=>m (K.bW (qi h1 hW))
      exact⟨qW j (SL j (U1 C\K.Q)) (opnd C b (1-db)) (Qe hL.1 K.hb (1-db)) (fun x h=>
        K.p2 (qm h) (fun bm=>Ym (K.ub bm).2.1 (K.ub bm).2.2.1 (a7 (by rcases(K.ub bm).2.2.2 with⟨k,_⟩|⟨k,_⟩;exact k;exact a3 x k▸k)))
         fun e=>by rcases(K.eb e).2.2.2 with⟨_,_,x1⟩|⟨xW,_,b1⟩;exact x1;exact(a7 (a3 x xW▸xW) b1).elim)
       (fun _ h=>Ds (qm h)),rfl,Cs _,hR⟩
   rcases K.A with⟨la,sA,gA,cA⟩|⟨i0,i1,_,_,g0,g1,am,aj,cA⟩
   · exact K.fa hN a5 j (ib::la) (by simp[wb1];omega) (by simp[cb];exact fun g h _=>(gA g h).1) fun u w h t hw=>
      if m:s(u,w)∈K.Q then K5 (cA u w m t hw) else QX (cB _ (qs h m))
   · exact K.f1 j [ib,i0,i1] (by simp[wb1,am,aj]) (by simp[cb,g0,g1]) fun e h=>
      if m:e∈K.Q then K5 (Zb (cA e m)) else QX (cB e (qs h m))
 have hI:K.Z⊆{v}:=fun vb hvb=>by
  by_contra hn;rw[mem_singleton] at hn
  have:K.W.card<=1:=(Cl fun x h=>qf (Uv _) ⟨hN x h,(Q1 hL.1 K.hb (q1 hvb) (q2 hvb)).2 x h⟩).trans (N4 v vb (Ne.symm hn));omega
 by_cases ac:K.J.card<=1
 · have a4:∀z∈K.J,z=v:=fun z h=>qe ac h q
   exact K.iO hN a5 [] S0 S0 fun u w h t hw=>K.p2 h
    (fun b=>by obtain⟨x,hx,rfl|rfl⟩:=(K.ub b).2.2.1<;>[exact(t (a4 _ hx)).elim;exact(hw (a4 _ hx)).elim])
    fun e=>by rcases(K.eb e).2.2.2 with⟨_,_,w1⟩|⟨_,_,u1⟩;exact(hw (a4 w w1)).elim;exact(t (a4 u u1)).elim
 have ag:(K.I∩K.W).card<=1:=qB (by omega:2<=K.J.card) fun u t y hy=>K.lb (q1 t) (q2 t) y hy
 rcases qE (K.I∩K.W) with al|⟨c0,an⟩;exact K.iB hN nW a5 hI al;exact K.iA q hN a5 hI ag an
set_option maxHeartbeats 500000 in
lemma XE (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty){v:Fin 11}(az:N C a 0∩N C a 1={v})(hJ:Joint G11 C a b)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): Bd C:=by
 classical
 let K:T1 C a b db v:=⟨hL,hT,hs,hab,hrb,hno2,hB0ne,az,hbWit⟩;have a5:=QP hL.1 hT hs hrb hno2 hJ
 have ag:K.X=∅:=P6 fun e h=>by
  induction e using Sym2.ind with| _ u w=>obtain⟨_,uW,wW,⟨_,_,w1⟩|⟨_,_,u1⟩⟩:=K.eb h;exact wW (a5 w1);exact uW (a5 u1)
 have ab:v∉K.J:=fun h=>K.nW (a5 h);have a6:∀y∈K.J,A1 v y:=fun y h=>K.wN y (a5 h);have ak {e:Sym2 F1} (he:e∈U1 C) (hB:e∉K.U):e∈K.Q:=by by_contra hW;exact qn ag (qM he hB hW)
 have ac:=K.lv ab
 have a7 c (lb:List (St C)) (sB:(lb.map (·.W.card)).sum<=1) (hb:∀i∈lb,i.c≠c->i.good) (cB:CO v K.U lb):G0 C:=by
  rcases K.A with⟨la,sA,gA,cA⟩|⟨i0,i1,_,_,g0,g1,bv,bf,cA⟩
  · exact K.fv a6 ac c (la++lb) (by simp;omega) (fun i h hn=>(Kap h).elim (fun h=>(gA i h).1) fun h=>hb i h hn) fun u w h hu hw=>
     if bm:s(u,w)∈K.U then P7 (cB u w bm hu hw) else V1 (cA u w (ak h bm) hu hw)
  · exact K.f1 c (i0::i1::lb) (by simp[bv,bf];omega) (by simp[g0,g1];exact hb)
     (XY (fun w h=>if m:s(v,w)∈K.Q then Zb (cA _ m) else (m (K.mU h ((ac w (ql h)).elim (qc hL.1) fun k=>a5 k))).elim)
      fun u w h hu hw=>if m:s(u,w)∈K.Q then Zb (cA _ m) else K5 (K5 (cB u w (by by_contra nb;exact m (ak h nb)) hu hw)))
 rcases qE K.U with c6|⟨eb,bl⟩;· exact a7 0 [] S0 S0 fun _ _ h _ _=>(qn c6 h).elim
 have ay:K.J.Nonempty:=by induction eb using Sym2.ind with| _ _ _=>obtain⟨x,g,_⟩:=(K.ub bl).2.2.1;exact⟨x,g⟩
 have av (s:Fin 2) (h1:(S1 C b s).card<=1) (Pt:(S1 C b s).Nonempty):G0 C:=by
  have⟨q,hq⟩:=qR h1;have qs':q∈S1 C b s:=by have⟨z,hz⟩:=Pt;exact hq z hz▸hz
  have ax {u w:F1} (h:s(u,w)∈K.U):u=q\/w=q:=by obtain⟨x,g,rfl|rfl⟩:=K.u2 s h;exact .inl (hq x g);exact .inr (hq x g)
  by_cases qv:q=v;· subst qv;exact a7 0 [] S0 S0 fun u w h hu hw=>by have:=ax h;grind
  by_cases qo:q∈S1 C b (1-s)
  · have b9:K.Z={q}:=eq_singleton_iff_unique_mem.mpr ⟨by fin_cases s<;>exact qi (by assumption) (by assumption),fun x g=>hq x (by fin_cases s;exact q1 g;exact q2 g)⟩
    exact K.fb ab a6 ac b9 fun u w h _ _ uq wq=>ak h fun bm=>by have:=ax bm;grind
  · let iq:=qW q (SL q K.U∩S1 C b (1-s)) (opnd C b (1-s)) (Qe hL.1 K.hb (1-s)) Ir fun _ h=>XH (qm (q1 h));exact a7 q [iq] Wu (by simp[iq,qW,Q0]) fun u w h _ _=>QX (kS h (K.u1 s hq qo h))
 by_cases b7:K.J.card<=1;· exact av (1-db) b7 ay
 by_cases bd:K.I.card<=1;· exact av db bd hB0ne
 have af:=K.b0 (by omega) a6
 have bu:(K.J∩K.W).card<=1:=qB (by omega:2<=K.I.card) fun y hy x g=>K.lb (q1 hy) (q2 hy) x (q3 g)
 by_cases w1:K.W.card<=1
 · have⟨wb,bz⟩:=qR w1;have⟨iw,cw,ww,bx⟩:=K.w1 bz;exact a7 wb [iw] (by simp[ww]) (by simp[cw]) fun u w h _ _=>QX (bx u w h)
 have cn:=K.i1 (by omega)
 by_cases a3:K.Z=∅
 · rcases qE (K.J∩K.W) with b6|⟨c1,a4⟩
   ·exact a7 0 [] S0 S0 fun _ _ h hu hw=>by rcases K.uB af h hu hw (fun m=>qn a3 m) (fun m=>qn a3 m) with⟨m,_,_⟩|⟨m,_,_⟩<;>exact(qn b6 m).elim
   · let ic:=K.B (1-db) c1 (q1 a4) (q2 a4) K.U XH;exact a7 0 [ic] Wu (by simp[ic,T1.B]) fun u w h hu hw=>QX (K.uC af a4 bu XH Subset.rfl h hu hw (fun m=>qn a3 m) (fun m=>qn a3 m))
 have⟨vb,hI⟩:=card_eq_one.mp (by have:=Cpr (Nem a3);omega:K.Z.card=1)
 obtain⟨_,_,_,b1,nW,hN⟩:=K.ib hI;have nv:vb≠v:=fun e=>ab (e▸b1);refine K.vc ab a6 af ac hI (fun _ _ h=>(qn ag h).elim) (fun _=>.inl (a5 b1)) ?_;intro c1 a4 z0 cp cs cx ct w2 b8 cu cr br na nb;rw[ag,union_empty]
 obtain⟨t,ht,d,ra,rb⟩:∃t∈Tp C,∃d:Fin 2,OR C (opnd C t d) a/\OR C (opnd C t (1-d)) b:=by
  rcases K.ec br with⟨_,(h|h)|⟨_,h|h⟩|⟨_,_,t,ht,d,ra,rb⟩⟩|⟨gf,_⟩<;>
   first|exact⟨t,ht,d,ra,rb⟩|exact(K.nW (qc hL.1 ‹_›)).elim|exact(nW (qc hL.1 ‹_›)).elim|exact(na ‹_›).elim|exact(nb ‹_›).elim|(have:=K.gV (w:=vb);rw[this] at gf;cases gf)
 have cy:=a6 vb b1;have bb:=a6 c1 (q1 a4);have bk:=hN c1 (q2 a4);have c5:K.R∩K.W⊆{c1}:=fun x h=>Sm (qe (N4 v vb nv.symm) (qf (Uv _) ⟨K.wN x (q1 h),hN x (q2 h)⟩) (qf (Uv _) ⟨bb,bk⟩));let G:=∃W2⊆W0For G11 C b,(W0For G11 C a).card+W2.card+1<=2*(centreless G11 C).card/\∀w∈SL vb K.U\{c1},TW C b W2 w
 have aa j (hc:t∈centreless G11 C) (hn:t∉T0For G11 C j) (hj:j=a\/j=b):G:=by
  have:=BZ hc hn (Fs _ _);have:=V0 (C:=C) a;have:=V0 (C:=C) b;have:=Qj (G:=G11) (C:=C) j
  exact⟨W0For G11 C b,Subset.rfl,by rcases hj with rfl|rfl<;>omega,fun _ h=>(K.ub (qm (K3 h))).2.2.2.elim (fun ⟨m,_⟩=>(nW m).elim) And.right⟩
 by_cases h0:S1 C t 0=∅\/S1 C t 1=∅
 · have hc:t∈centreless G11 C:=qf ht h0
   by_cases hA:t∈T0For G11 C a;swap;exact aa a hc hA (.inl rfl)
   by_cases hB:t∈T0For G11 C b;swap;exact aa b hc hB (.inr rfl)
   obtain⟨a8,ba,b3,_⟩:=(qF hA).2;obtain⟨aw,bp,b5,al⟩:=(qF hB).2;have c4:a8=aw:=by by_contra hn;have⟨z,hz⟩:=al;exact qn ba (by fin_cases a8<;>fin_cases aw<;>first|exact(hn rfl).elim|exact hz)
   subst c4;have hw0:opnd C t (1-a8)∈W0For G11 C b:=Mi ⟨t,hB,match a8,bp,al with|0,h0,_=>by simp[h0]|1,_,h1=>by have:S1 C t 0≠∅:=Nep h1;simp[this]⟩
   refine⟨(W0For G11 C b).erase (opnd C t (1-a8)),erase_subset _ _,by have:=V0 (C:=C) a;have:=V0 (C:=C) b;have:=Ceo hw0;omega,fun w h=>?_⟩
   obtain⟨wL,nc⟩:=qD h;rw[mem_singleton] at nc
   rcases(K.ub (qm wL)).2.2.2 with⟨m,_⟩|⟨_,bt|hm⟩;exact(nW m).elim
   · have⟨z,hz,zw⟩:=Bup bt
     exact .inl (Mbu ⟨z,mem_erase.mpr ⟨fun e=>nc (q0 (c5 (qi (QY hL.1 ht b3 (by rwa[e] at zw)) (QY hL.1 ht b5 (by rwa[e] at zw))))),hz⟩,zw⟩)
   ·exact .inr hm
 · push Not at h0
   obtain⟨x,g⟩:(S1 C t d).Nonempty:=by fin_cases d;exact h0.1;exact h0.2
   obtain⟨y,hy⟩:(S1 C t (1-d)).Nonempty:=by fin_cases d;exact h0.2;exact h0.1
   have xW:=QY hL.1 ht rb (q3 g);have yW:=QY hL.1 ht ra hy
   by_cases xv:x=v;· subst x;exact(nb (K8 hL.1 K.hb ht rb (q3 g))).elim
   by_cases yv:y=vb;· subst y;exact(na (K8 hL.1 K.ha ht ra hy)).elim
   exfalso;refine @XK v vb ?_ c1 ?_ ?_ z0 ?_ ?_ ?_ w2 ?_ ?_ ?_ x ?_ ?_ y ?_ ?_ ?_<;>
    grind [hN w2 b8,hN x xW,K.wN y yW,YZ hL.1 ht g hy]
set_option maxHeartbeats 400000 in
lemma V4 (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty){v:Fin 11}(aa:N C a 0∩N C a 1={v})(t:v∉N C b (1-db))(a4:v∈Mw C b)(ac:¬Joint G11 C a b)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): Bd C:=by
 classical
 let K:T1 C a b db v:=⟨hL,hT,hs,hab,hrb,hno2,hB0ne,aa,hbWit⟩;have g:∀y∈K.J,A1 v y:=YV hL.1 hT hs hab hrb hno2 K.v0 K.v1 a4;have j:=K.lv t
 by_cases ad:K.J.card<=1
 · rcases qE K.J with a7|⟨q,z⟩
   · exact K.f0 g j [] S0 S0 fun u w h _ _=>
      K.p2 h (fun b=>by obtain⟨_,x,_⟩:=(K.ub b).2.2.1;exact(qn a7 x).elim) fun e=>by rcases(K.eb e).2.2.2 with⟨_,_,x⟩|⟨_,_,x⟩<;>exact(qn a7 x).elim
   · have hq:∀y∈K.J,y=q:=fun y h=>qe ad h z;have qv:q≠v:=fun e=>t (e▸z)
     by_cases qW:q∈K.W
     · have a8:=K.bW (qi z qW);have ag:=K.nO z qW;let iq:=K.B (1-db) q z qW K.U XH
       exact K.f0 g j [iq] Wu Ba fun u w h _ _=>K.p2 h (fun bm=>QX (kS bm (K.u1 (1-db) hq ag bm)))
        fun e=>by obtain⟨_,uW,wW,⟨_,_,w1⟩|⟨_,_,u1⟩⟩:=K.eb e;exact(wW (hq w w1▸a8)).elim;exact(uW (hq u u1▸a8)).elim
     ·exact K.cq j hq qv qW
 have a9:=K.b0 (by omega) g
 by_cases w1:K.W.card<=1
 · have Wv:∀w∈K.W,w=v:=fun w h=>qe w1 h a4;exact K.f0 g j [] S0 S0 fun u w h hu hw=>K.p2 h (fun b=>by have:=(K.ub b).2.2.2;grind) fun e=>by have:=(K.eb e).2.2.2;grind
 have ap:=K.i1 (by omega)
 by_cases a5:K.Z=∅;· exact K.c0 g a9 j a5
 have⟨vb,hI⟩:=card_eq_one.mp (by have:=Cpr (Nem a5);omega:K.Z.card=1)
 obtain⟨_,_,_,b1,nW,hN⟩:=K.ib hI
 have hE:∀u w,s(u,w)∈K.X->u=v\/w=v\/u=vb\/w=vb:=fun u w h=>by
  by_contra! k;have⟨hu,hw,hub,hwb⟩:=k
  rcases(K.eb h).2.2.2 with⟨uW,_,w1⟩|⟨wW,_,u1⟩
  ·exact QV hu.symm hwb.symm (g vb b1) (hN u uW).symm (g w w1) (qA h)
  ·exact QV hw.symm hub.symm (g vb b1) (hN w wW).symm (g u u1) (qA h).symm
 have hV:s(v,vb)∈U1 C->K.P vb\/K.T v:=fun h=>by
  rcases K.ec h with⟨_,(h1|h1)|⟨_,h2|h2⟩|⟨hJ,_⟩⟩|⟨_,_,_,⟨_,h2⟩|⟨h',_⟩⟩<;>
   first|exact .inl ‹_›|exact .inr ‹_›|exact(K.nW (qc hL.1 ‹_›)).elim|exact(nW (qc hL.1 ‹_›)).elim|exact(ac ‹_›).elim
 exact K.vc t g a9 j hI hE (fun h=>(hV h).imp (qc hL.1) id) fun _ _ _ _ _ _ _ _ _ _ _ h na nb=>((hV h).elim na nb).elim
end Ia1TopCompact
structure Z2B (C:Ck) where
 L:Ls C
 T:Tf C
 a:ℕ
 b:ℕ
 s:Jk C={a,b}
 c:Ic C a b
 db:Fin 2
 r:O C (opnd C b db) a
 n:¬O C (opnd C b (1-db)) a
 e:(N C b db).Nonempty
 v:Fin 11
 I:N C a 0∩N C a 1={v}
 B:v∉N C b (1-db)
 W:v∉Mw C b
 J:¬Joint G11 C a b
 w:(T0For G11 C b).Nonempty\/ ∃m∈mixing G11 C,O C (11+m) b
namespace Z2B
open Finset
abbrev F:=Fin 11
abbrev F2:=Fin 2
abbrev S2:=Sym2 F
abbrev SS:=StarSpec
abbrev TC (C:Ck):=Tc C
abbrev oi (C:Ck):=Oi C
abbrev Px {C}(it:SS C)(e:S2):=∃x∈it.L,e=s(it.c,x)
abbrev PC {C}(l:List (SS C))(e:S2):=∃it∈l,Px it e
abbrev PP (c:F)(L:Finset F)(e:S2):=∃x∈L,e=s(c,x)
abbrev PY (c:F)(L:Finset F):Finset S2:=L.image fun w=>s(c,w)
abbrev PD {C}(l:List (St C)):ℕ:=(l.map fun it=>it.W.card).sum
@[simp] lemma H0 {C}:PD ([]:List (St C))=0:=rfl
@[simp] lemma PG {C}(x:St C)(l:List (St C)):PD (x::l)=x.W.card+PD l:=rfl
@[simp] lemma PT {C}(l m:List (St C)):PD (l++m)=PD l+PD m:=by simp[PD]
lemma PX {C}(l:List (St C)):(l.map fun it=>it.W.card).sum=PD l:=rfl
@[simp] lemma J0 {C c L w hw hL hU g hg}:(Q0 C c L w hw hL hU g hg).W.card=1:=Cs w
abbrev Rb {C}(x y:SS C):=(x.W.biUnion (oi C)∩y.L).card <=1\/ (y.W.biUnion (oi C)∩x.L).card <=1
abbrev Hn {C}(l:List (SS C)):=(∀x∈l,∀y∈l,x.c=y.c -> x=y) /\(∀x∈l,∀y∈l,x.c≠y.c -> Rb x y)
abbrev H5 (C:Ck)(L:Finset F)(M:Finset ℕ):=
 ∃fw:ℕ -> F,(∀m∈M,fw m∈L /\∃t∈Tp C,∃d:F2,O C (opnd C t d) m /\fw m∈N C t (1-d)) /\
  ∀m1∈M,∀m2∈M,m1≠m2 -> fw m1≠fw m2
abbrev Ru (C:Ck)(c:F)(L:Finset F)(W Mc:Finset ℕ)(gd:Prop):=
 ∃it:SS C,∃Lm:Finset F,∃M⊆Mc,it.c=c /\it.W=W /\it.L⊆L /\it.good=gd /\Lm.card=M.card /\H5 C L M /\
  ∀{e:S2},PP c L e -> e∉PY c Lm -> Px it e
section Mic
variable {α:Type*} {s t:Finset α} {x y:α} {l m:List α}
lemma mC (h:x∈y::l):x=y\/ x∈l:=Kp h
lemma mA (h:x∈l++m):x∈l\/ x∈m:=Kap h
lemma mL (h:x∈[y]):x=y:=Kl.mp h
lemma c0:x∈x::l:=Kc
lemma c1 (h:x∈l):x∈y::l:=Km _ h
lemma aL (h:x∈l):x∈l++m:=Kal _ h
lemma aR (h:x∈m):x∈l++m:=Kar _ h
lemma Tn (h:l≠[]):∃z t,l=z::t:=List.exists_cons_of_ne_nil h
lemma nE {P:Prop}(h:x∈(∅:Finset α)):P:=(N0 h).elim
lemma mS (h:x∈({y}:Finset α)):x=y:=Sp h
lemma ms:x∈({x}:Finset α):=Ss x
lemma nS (h:x∉({y}:Finset α)):x≠y:=notMem_singleton.mp h
lemma R1 (h:x≠y):x∉({y}:Finset α):=Ns h
lemma sr:s⊆s:=Subset.rfl
lemma R3 (h:s⊆t):s.card <=t.card:=Cl h
lemma Ms (s:Finset α):s=∅\/ s.Nonempty:=s.eq_empty_or_nonempty
lemma fs {p:α -> Prop}[DecidablePred p]:s.filter p⊆s:=Fs _ _
lemma f1 {p:α -> Prop}[DecidablePred p](h:s⊆t.filter p):s⊆t:=h.trans fs
lemma f2 {p:α -> Prop}[DecidablePred p](h:s⊆t.filter p):∀z∈s,p z:=fun _ g=>(Fp (h g)).2
lemma RE {P0 P1:Prop}[Decidable P0][Decidable P1](h:2 <=(if P0 then 1 else 0)+(if P1 then 1 else 0)):P0 /\P1:=by split_ifs at h<;>first|exact⟨‹_›,‹_›⟩|omega
variable [DecidableEq α]
lemma i1 (h:x∈s∩t):x∈s:=(I1 h)
lemma i2 (h:x∈s∩t):x∈t:=(I2 h)
lemma d1 (h:x∈s\t):x∈s:=(D1 h)
lemma d2 (h:x∈s\t):x∉t:=(D2 h)
lemma ds:s\t⊆s:=Ds
lemma mI (a:x∈s)(b:x∈t):x∈s∩t:=Im a b
lemma mD (a:x∈s)(b:x∉t):x∈s\t:=Dm a b
lemma uL (h:x∈s):x∈s∪t:=Ul _ h
lemma uR (h:x∈t):x∈s∪t:=Ur _ h
lemma mU (h:x∈s∪t):x∈s\/ x∈t:=Up h
end Mic
lemma sL {E:Finset S2}{c x:F}(h:s(c,x)∈E):x∈Q4 c E:=Zm h
lemma sE {E:Finset S2}{c x:F}(h:x∈Q4 c E):s(c,x)∈E:=Zl h
lemma sw {u v:F}:s(u,v)=s(v,u):=Sw
abbrev uq:=@Qp
abbrev H1:=@Qk
abbrev eS:=@Qu
abbrev uS:=@QA
abbrev H4:=@Qd
abbrev mW:=@Q0
abbrev cS:=@Cs
abbrev MR:=@Sym2.eq_iff
abbrev gA:=@Qh
abbrev RM:=@notMem_empty
lemma HW {E:Finset S2}{P:S2 -> Prop}(h:∀u w,s(u,w)∈E -> P s(u,w)):∀e∈E,P e:=fun e he=>by
 induction e using Sym2.ind with| _ u w=>exact h u w he
lemma R9 {E:Finset S2}{Q:Prop}(h:∀u w,s(u,w)∈E -> Q)(g:E.Nonempty):Q:=by have⟨e,he⟩:=g;induction e using Sym2.ind with| _ u w=>exact h u w he
lemma TQ {E M:Finset S2}{P:S2 -> Prop}(h:∀u w,s(u,w)∈E -> s(u,w)∉M -> P s(u,w)):∀e∈E\M,P e:=
 HW fun u w he=>h u w (d1 he) (d2 he)
lemma RF {E:Finset S2}(h:∀u w,s(u,w)∈E -> False):E=∅:=Ee.mpr (HW h)
lemma Rs {C}{l m:List (SS C)}{e:S2}(h:PC l e)(hs:∀x∈l,x∈m):PC m e:=by have⟨g,j,r⟩:=h;exact⟨g,hs g j,r⟩
lemma hL {C}{l m:List (SS C)}{e:S2}(h:PC l e):PC (l++m) e:=Rs h fun _=>aL
lemma hR {C}{l m:List (SS C)}{e:S2}(h:PC m e):PC (l++m) e:=Rs h fun _=>aR
lemma HT {C}{x:SS C}{l:List (SS C)}{e:S2}(h:Px x e):PC (x::l) e:=⟨x,c0,h⟩
lemma Hy {C}{x:SS C}{l:List (SS C)}{e:S2}(h:PC l e):PC (x::l) e:=Rs h fun _=>c1
lemma Ty {C}{a b c:List (SS C)}{e:S2}(h:PC (b++c) e):PC ((a++b)++c) e:=Rs h fun _ j=>(mA j).elim (fun g=>aL (aR g)) aR
lemma Jt {C}{x:SS C}{l:List (SS C)}(hl:Hn l)(hn:∀y∈l,y.c≠x.c)(h:∀y∈l,Rb x y):Hn (x::l):=
 ⟨fun _ ha _ hb q=>by rcases mC ha with rfl|ha'<;>rcases mC hb with rfl|g<;>first|rfl|exact(hn _ g q.symm).elim|exact(hn _ ha' q).elim|exact hl.1 _ ha' _ g q,
  fun _ ha _ hb ne=>by rcases mC ha with rfl|ha'<;>rcases mC hb with rfl|g<;>first|exact(ne rfl).elim|exact h _ g|exact(h _ ha').symm|exact hl.2 _ ha' _ g ne⟩
lemma b0 {C}:Hn ([]:List (SS C)):=⟨by simp,by simp⟩
lemma Ju {C}(P:Prop)[Decidable P](j:SS C):Hn (if P then [j] else []):=by
 split_ifs
 . exact⟨fun _ ha _ hb _=>(mL ha).trans (mL hb).symm,fun _ ha _ hb ne=>(ne (by rw[mL ha,mL hb])).elim⟩
 . exact b0
lemma RH {C}{P0 P1:Prop}[Decidable P0][Decidable P1]{g j z:SS C}(q:z∈(if P0 then [g] else [])++(if P1 then [j] else [])):(P0 /\z=g)\/ (P1 /\z=j):=by
 rcases mA q with h|h<;>split_ifs at h with hn<;>[exact .inl ⟨hn,mL h⟩;cases h;exact .inr ⟨hn,mL h⟩;cases h]
lemma J8 {C}{P0 P1:Prop}[Decidable P0][Decidable P1]{j0 j1:SS C}(Pt:P0 -> P1 -> j0.c≠j1.c)(hd:Rb j0 j1):Hn ((if P0 then [j0] else [])++(if P1 then [j1] else [])):=
 ⟨fun _ ha _ hb q=>by rcases RH ha with⟨t,rfl⟩|⟨g,rfl⟩<;>rcases RH hb with⟨h,rfl⟩|⟨j,rfl⟩<;>first|rfl|exact(Pt t j q).elim|exact(Pt h g q.symm).elim,
  fun _ ha _ hb ne=>by rcases RH ha with⟨_,rfl⟩|⟨_,rfl⟩<;>rcases RH hb with⟨_,rfl⟩|⟨_,rfl⟩<;>first|exact(ne rfl).elim|exact hd|exact hd.symm⟩
lemma Jw {C}(P0 P1:Prop)[Decidable P0][Decidable P1]{j0 j1:SS C}(h0:j0.W.card=1)(g:j1.W.card=1): PD ((if P0 then [j0] else [])++(if P1 then [j1] else []))=(if P0 then 1 else 0)+(if P1 then 1 else 0):=by rw[PT];split_ifs<;>simp[h0,g]
lemma Tw {α}[DecidableEq α](E:Finset α)(e:α):E.card <=(E\{e}).card+1:=by have h1:=R3 (show E⊆(E\{e})∪{e} from fun x hx=>by grind);have g:=Cu (E\{e}) {e};rw[cS] at g;omega
lemma Tq (E:Finset S2)(c:F)(L:Finset F):E.card <=(E\PY c L).card+L.card:=by
 have h1:=R3 (show E⊆(E\PY c L)∪PY c L from fun x hx=>by grind)
 have h2:=(Cu (E\PY c L) (PY c L)).trans (A2l Ci _);omega
lemma TF (E:Finset S2)(c1 c2:F)(L1 L2:Finset F):E.card <=(E\(PY c1 L1∪PY c2 L2)).card+L1.card+L2.card:=by
 set M:=PY c1 L1∪PY c2 L2;have h1:=R3 (show E⊆(E\M)∪M from fun x hx=>by grind);have h2:=Cu (E\M) M
 have h3:M.card <=(PY c1 L1).card+(PY c2 L2).card:=Cu _ _;have h4:(PY c1 L1).card <=L1.card:=Ci;have h5:(PY c2 L2).card <=L2.card:=Ci;omega
lemma RQ {S:Finset F}(h:2 <=S.card):∃p∈S,∃q∈S,p < q:=by
 have⟨p,j,q,g,ne⟩:=one_lt_card.mp (by omega:1 < S.card)
 exact(lt_or_gt_of_ne ne).elim (fun h=>⟨p,j,q,g,h⟩) fun h=>⟨q,g,p,j,h⟩
lemma Ra {C}(a7:Ao C){c:F}{L:Finset F}{W Mc:Finset ℕ}(a5:Mc⊆mixing G11 C)(hW:∀z∈W,z < 11+C.gates.length)(j:∀w∈L,s(c,w)∈Us C)(a6:∀w∈L,w∈W.biUnion (oi C)\/ ∃t∈Tp C,∃d:F2,∃m∈Mc,O C (opnd C t d) m /\w∈N C t (1-d))(gd:Prop)(a8:gd -> ∀z∈W,∀x∈oi C z,Ga c x):Ru C c L W Mc gd:=by
 have⟨L0,Lm,M,hM,a4,g,q,a3,fw,h1,h2⟩:=QU (L:=L) (W_c:=W) a7 a5 j a6;refine⟨⟨c,L0,W,hW,q,fun _ h=>j _ (g h),gd,a8⟩,Lm,M,hM,rfl,rfl,g,rfl,a3,⟨fw,h1,h2⟩,?_⟩
 rintro _ ⟨x,h,rfl⟩ hnm;rw[a4] at h;rcases mU h with h0|hm;exact⟨x,h0,rfl⟩;exact(hnm (Mi ⟨x,hm,rfl⟩)).elim
lemma tW {C}(k:Z2B C){g:ℕ}{w:F}(h:TC C g w):w∈Mw C g:=Q5 k.L.1 h
section Ctx
variable {C:Ck} (k:Z2B C)
abbrev o:=k.L.1
abbrev A (d:F2):=N C k.a d
abbrev Ad (d:F2):=k.A d\k.A (1-d)
abbrev Wa:=Mw C k.a
abbrev Wb:=Mw C k.b
abbrev B0:=N C k.b k.db
abbrev B1:=N C k.b (1-k.db)
abbrev BW:=k.B1∩k.Wb
abbrev H8:=k.B0∩k.Wb
abbrev Ib:=N C k.b 0∩N C k.b 1
abbrev U (_:Z2B C):=Us C
abbrev Pz:=k.U.card <=2*(centreless G11 C).card+2+(rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card
abbrev Ua:=Yx C k.a
abbrev Ub:=Yu C k.a
abbrev Eb:=Ya C k.a
abbrev oa (d:F2):=opnd C k.a d
abbrev ob (d:F2):=opnd C k.b d
abbrev Lv:=Q4 k.v k.U
abbrev dA (d:F2):=(k.Ad d∩k.Wb)\k.Wa
abbrev dB (d:F2):=(k.Ad (1-d)∩k.B1)\k.Wa
abbrev Mz:=(mixing G11 C).filter fun m=>O C (11+m) k.a
abbrev Rc:=(mixing G11 C).filter fun m=>O C (11+m) k.b
open Classical in
noncomputable def Hk (P:F -> F -> Prop)(d:F2):Finset S2:=
 k.Eb.filter fun e=>∃u w:F,e=s(u,w) /\u∈k.Ad d∩k.Wb /\w∈k.Ad (1-d)∩k.B1 /\P u w
open Classical in
lemma HY {P:F -> F -> Prop}{d:F2}{e:S2}: e∈k.Hk P d↔e∈k.Eb /\∃u w:F,e=s(u,w) /\u∈k.Ad d∩k.Wb /\w∈k.Ad (1-d)∩k.B1 /\P u w:=by unfold Hk;exact mem_filter
open Classical in
lemma HG {P:F -> F -> Prop}{d:F2}:k.Hk P d⊆k.Eb:=by unfold Hk;exact fs
lemma ha:k.a∈Jk C:=by simp[k.s]
lemma hb:k.b∈Jk C:=by simp[k.s]
lemma Pt:k.a≠k.b:=Nlt (Y4 k.c)
lemma Pv:k.v∈k.A 0:=i1 (k.I▸ms)
lemma Pu:k.v∈k.A 1:=i2 (k.I▸ms)
lemma hv (d:F2):k.v∈k.A d:=by fin_cases d;exact k.Pv;exact k.Pu
lemma MG:k.v∉k.Wa:=(Q1 k.o k.ha k.Pv k.Pu).1
lemma PU:∀w∈k.Wa,Ga k.v w:=(Q1 k.o k.ha k.Pv k.Pu).2
lemma PQ:k.BW⊆k.Wa:=K7 k.o k.T k.s k.r k.n
lemma Ts:k.Ub∪k.Eb⊆k.U:=Us2 uS eS
lemma TR:(W0For G11 C k.a).card <=(centreless G11 C).card:=(Qj (G:=G11) (C:=C) k.a).trans (Qs k.a)
lemma RW:(W0For G11 C k.b).card <=(centreless G11 C).card:=(Qj (G:=G11) (C:=C) k.b).trans (Qs k.b)
lemma RX:∀z∈(W0For G11 C k.a),∀x∈oi C z,Ga k.v x:=fun z g x h=>k.PU x (Qc k.o k.a z g h)
lemma Tm {h:F}(g:h∈k.Ib):∀z∈(W0For G11 C k.b),∀x∈oi C z,Ga h x:=
 fun z j x q=>(Q1 k.o k.hb (i1 g) (i2 g)).2 x (Qc k.o k.b z j q)
lemma hB01:k.B0∩k.B1=k.Ib:=by unfold B0 B1 Ib;cases h:k.db using Fin.cases with|zero=>rfl|succ i=>fin_cases i;exact inter_comm _ _
lemma RG {u w:F}(he:s(u,w)∈k.Ub)(j:u∉k.Ib)(hw:w∉k.Ib):(u∈k.B0 /\w∈k.B1)\/ (u∈k.B1 /\w∈k.B0):=by
 obtain⟨_,h0,g,_⟩:=Kr k.L k.T k.s k.r k.n he;have hs:=Yt h0 g j hw
 cases h:k.db using Fin.cases with|zero=>simpa[B0,B1,h] using hs|succ i=>fin_cases i;simpa[B0,B1,h] using hs.symm
abbrev A2:=YJ k.L k.T k.s k.c k.I
abbrev M6 {u w:F}(h:s(u,w)∈k.Ub):=Kr k.L k.T k.s k.r k.n h
abbrev RJ {u w:F}(h:s(u,w)∈k.Ua):=Kn k.L k.T k.s k.r k.n h
abbrev Hq {u w:F}(h:s(u,w)∈k.Eb):=Zr k.L k.T k.s k.r k.n h
lemma TE (d:F2):(k.dA d).card <=1\/ (k.dB d).card <=1:=by simpa only[dA,dB,Ad,A,Wb,Wa,B1,H4] using VK k.o k.T k.s k.c k.r d
lemma Hg {d:F2}{c y:F}(g:c∈k.A d)(hW:c∈k.Wa)(h:y∈k.A (1-d)):Ga c y:=Y1 k.o k.T k.s k.c g hW y h
lemma HX (d:F2){x y:F}(h:x∈k.A d)(hW:x∈k.Wb)(j:y∈k.A (1-d))(g:y∈k.B1):Ga x y:=K9 k.o k.T k.s k.c k.r d h hW j g
lemma M8 {d:F2}{x y:F}(g:x∈N C k.b d)(hW:x∈k.Wb)(h:y∈N C k.b (1-d)):Ga x y:=QC k.o k.hb g hW y h
lemma T3 {d:F2}{p q:F}(h:p∈k.Ad d)(g:q∈k.Ad (1-d)):p≠q:=fun e=>d2 h (e▸d1 g)
lemma Ja {x w:F}(g:x∉k.Wa)(hw:w∈k.Wa):x≠w:=fun e=>g (e▸hw)
lemma Rx {x y:F}(h:x∉k.Wa)(g:x∈k.B1)(hW:y∈k.Wb):x≠y:=fun e=>h (k.PQ (mI g (e▸hW)))
lemma n0 {P:Prop}(h:k.H8=∅){x:F}(h0:x∈k.B0)(hW:x∈k.Wb):P:=by have g:x∈k.H8:=mI h0 hW;rw[h] at g;exact nE g
lemma n1 {P:Prop}(h:k.BW=∅){x:F}(j:x∈k.B1)(hW:x∈k.Wb):P:=by have g:x∈k.BW:=mI j hW;rw[h] at g;exact nE g
abbrev Hc (d:F2)(c:F)(h1:c∈k.A d)(h2:c∈k.Wa)(E:Finset S2)(hE:E⊆k.U):=Q9 k.o k.ha d c h1 h2 E hE
abbrev R5 (d:F2)(c:F)(h1:c∈N C k.b d)(h2:c∈k.Wb):=Q9 k.o k.hb d c h1 h2 k.U sr
lemma M5 {e:S2}(he:e∈k.U)(hb:e∉k.Ub)(hw:e∉k.Ua):e∈k.Eb:=mD (mD he hb) hw
lemma Me {e:S2}(he:e∈k.U)(hw:e∉k.Ua):e∈k.Ub∪k.Eb:=by by_cases hb:e∈k.Ub;exact uL hb;exact uR (k.M5 he hb hw)
lemma HE (d:F2){x:F}(j:x∈k.A d)(g:x≠k.v):x∈k.Ad d:=
 mD j fun h=>g (mS (k.I▸(by fin_cases d<;>exact mI (by assumption) (by assumption))))
lemma ps {u w:F}(g:Gv C k.a (Pi u w)=true)(j:u≠k.v)(hw:w≠k.v)(d:F2): (u∈k.A d /\w∈k.A (1-d))\/ (u∈k.A (1-d) /\w∈k.A d):=by
 have h0:=Qt k.o k.T k.s k.c g (fun h=>j (mS (k.I▸h))) (fun h=>hw (mS (k.I▸h)))
 fin_cases d<;>[exact h0;exact h0.symm]
lemma H7 (d:F2){p q w:F}(h:p∈k.Ad d)(g:q∈k.Ad (1-d))(hw:w∈k.Wa):Ga p q\/ Ga p w\/ Ga q w:=
 Ka hw ((Qv k.o k.T k.s k.c _).mpr (by
  fin_cases d;exact⟨⟨p,d1 h,tripleInput_1 ..⟩,⟨q,d1 g,tripleInput_2 ..⟩⟩;exact⟨⟨q,d1 g,tripleInput_2 ..⟩,⟨p,d1 h,tripleInput_1 ..⟩⟩))
lemma My {z q w:F}(h:z∈k.B0)(g:q∈k.B1)(hw:w∈k.Wb):Ga z q\/ Ga z w\/ Ga q w:=
 Ka hw ((QR k.o k.T k.s k.r k.n _).mpr ⟨.inr ⟨z,h,tripleInput_1 ..⟩,⟨q,g,tripleInput_2 ..⟩⟩)
lemma HQ:∀w∈k.Lv,TC C k.a w\/ w∈k.BW:=fun w hw=>by
 rcases QM k.L k.T k.s k.r k.n (sE hw) with
  ⟨_,(q|q)|⟨j|j,t|t⟩|⟨hJ,_⟩⟩|⟨_,_,⟨x1,g,rfl|rfl⟩,⟨h,_⟩|⟨z,_⟩⟩
 . exact(k.MG (k.tW q)).elim
 . exact .inl q
 . exact(k.B j).elim
 . exact(k.B j).elim
 . exact(k.W (k.tW t)).elim
 . exact .inr (mI j (k.tW t))
 . exact(k.J hJ).elim
 . exact(k.B g).elim
 . exact(k.B g).elim
 . exact(k.W h).elim
 . exact .inr (mI g z)
lemma RD {u w:F}(he:s(u,w)∈k.Eb):u≠k.v /\w≠k.v:=by have hs:=k.Hq he;exact⟨fun e=>hs.2.2.2.elim (fun a=>k.W (e▸a.1)) fun a=>k.B (e▸a.2.2),fun e=>hs.2.2.2.elim (fun a=>k.B (e▸a.2.2)) fun a=>k.W (e▸a.1)⟩
lemma Es {u w:F}(he:s(u,w)∈k.Eb): ∃p q:F,s(u,w)=s(p,q) /\p∈k.Wb /\q∈k.B1 /\p∉k.Wa /\q∉k.Wa /\p≠k.v /\q≠k.v /\ ((p∈k.Ad 0 /\q∈k.Ad 1)\/ (p∈k.Ad 1 /\q∈k.Ad 0)):=by
 have hs:=k.Hq he;have hn:=k.RD he
 rcases hs.2.2.2 with⟨h,_,g⟩|⟨h,_,g⟩
 . exact⟨u,w,rfl,h,g,hs.2.1,hs.2.2.1,hn.1,hn.2,(k.ps hs.1 hn.1 hn.2 0).elim (fun a=>.inl ⟨k.HE 0 a.1 hn.1,k.HE 1 a.2 hn.2⟩) fun a=>.inr ⟨k.HE 1 a.1 hn.1,k.HE 0 a.2 hn.2⟩⟩
 . exact⟨w,u,sw,h,g,hs.2.2.1,hs.2.1,hn.2,hn.1,(k.ps hs.1 hn.1 hn.2 0).elim (fun a=>.inr ⟨k.HE 1 a.2 hn.2,k.HE 0 a.1 hn.1⟩) fun a=>.inl ⟨k.HE 0 a.2 hn.2,k.HE 1 a.1 hn.1⟩⟩
lemma cv {P:S2 -> Prop}(h:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> P s(u,w)):∀e∈k.U,PP k.v k.Lv e\/ P e:=HW fun u w he=>by
 by_cases g:u=k.v;. subst u;exact .inl ⟨w,sL he,rfl⟩
 by_cases hw:w=k.v;. subst w;exact .inl ⟨u,sL (sw▸he),sw⟩
 exact .inr (h u w he g hw)
lemma TU {q:F}{P:S2 -> Prop}(h:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> P s(u,w)): ∀e∈k.U\{s(k.v,q)},PP k.v (k.Lv\{q}) e\/ P e:=TQ fun u w he Pt=>by
 rw[mem_singleton] at Pt
 by_cases j:u=k.v;. subst u;exact .inl ⟨w,mD (sL he) (R1 fun g=>Pt (by rw[g])),rfl⟩
 by_cases hw:w=k.v;. subst w;exact .inl ⟨u,mD (sL (sw▸he)) (R1 fun g=>Pt (by rw[g,sw])),sw⟩
 exact .inr (h u w he j hw)
lemma TV {M:Finset S2}{P:S2 -> Prop}(h:∀e∈k.U,PP k.v k.Lv e -> e∉M -> P e)(j:∀u w,s(u,w)∈k.U -> s(u,w)∉M -> u≠k.v -> w≠k.v -> P s(u,w)):∀e∈k.U\M,P e:=TQ fun u w he g=>by
 by_cases q:u=k.v;. subst u;exact h _ he ⟨w,sL he,rfl⟩ g
 by_cases hw:w=k.v;. subst w;exact h _ he ⟨u,sL (sw▸he),sw⟩ g
 exact j u w he g q hw
lemma J9 {q:F}{P:S2 -> Prop}(g:s(k.v,q)∈k.U -> P s(k.v,q))(h:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> P s(u,w)): ∀e∈k.U,PP k.v (k.Lv\{q}) e\/ P e:=HW fun u w he=>by
 by_cases j:u=k.v;. subst u;exact if hq':w=q then hq'.symm▸.inr (g (hq'▸he)) else .inl ⟨w,mD (sL he) (R1 hq'),rfl⟩
 by_cases hw:w=k.v;. subst w;exact if hq':u=q then by subst u;rw[sw];exact .inr (g (sw▸he)) else .inl ⟨u,mD (sL (sw▸he)) (R1 hq'),sw⟩
 exact .inr (h u w he j hw)
lemma Td {L:Finset F}(hL:L⊆k.Lv)(g:∀w∈L,TC C k.a w):Ru C k.v L (W0For G11 C k.a) k.Mz True:=
 Ra k.o fs (Qg k.o k.a) (fun _ hw=>sE (hL hw)) g True fun _=>k.RX
lemma TS {g:F}(j:g∈k.Ib){L:Finset F}(h:∀w∈L,s(g,w)∈k.U)(q:∀w∈L,TC C k.b w):Ru C g L (W0For G11 C k.b) k.Rc True:=
 Ra k.o fs (Qg k.o k.b) h q True fun _=>k.Tm j
lemma Mq {z a3:F}(h0:z∈k.Ad 0∩k.Wa)(t:a3∈k.Ad 1∩k.Wa)(hW:∀w∈k.Wa,w=z\/ w=a3): ∃gs:List (SS C),PD gs=2 /\(∀g∈gs,g.good /\g.c∈k.Wa) /\ ∀u w,s(u,w)∈k.U -> (u=k.v\/ w=k.v\/ s(u,w)∈k.Ua) -> PC gs s(u,w):=by
 have a4:∀w∈k.Lv,w∈k.Wa:=fun w hw=>(k.HQ w hw).elim k.tW fun h=>k.PQ h;let j:=k.Hc 0 z (d1 (i1 h0)) (i2 h0) k.U sr;let q:=k.Hc 1 a3 (d1 (i1 t)) (i2 t) k.U sr;refine⟨[j,q],by simp[j,q],fun g hg=>(mC hg).elim (fun e=>e▸⟨trivial,i2 h0⟩) fun h=>mL h▸⟨trivial,i2 t⟩,fun u w he hc=>?_⟩
 by_cases hu:u=k.v
 . subst u;rcases hW w (a4 w (sL he)) with rfl|rfl;exact⟨j,c0,k.v,mI (sL (sw▸he)) k.Pu,sw⟩;exact⟨q,c1 c0,k.v,mI (sL (sw▸he)) k.Pv,sw⟩
 by_cases hw:w=k.v
 . subst w;rcases hW u (a4 u (sL (sw▸he))) with rfl|rfl;exact⟨j,c0,k.v,mI (sL he) k.Pu,rfl⟩;exact⟨q,c1 c0,k.v,mI (sL he) k.Pv,rfl⟩
 have⟨ab,aa⟩:=k.RJ (show s(u,w)∈k.Ua by grind)
 rcases k.ps ab hu hw 0 with⟨a9,a7⟩|⟨a6,hw0⟩<;>rcases aa with a8|a5
 . rcases hW u a8 with rfl|rfl;exact⟨j,c0,w,mI (sL he) a7,rfl⟩;exact(d2 (i1 t) a9).elim
 . rcases hW w a5 with rfl|rfl;exact(d2 (i1 h0) a7).elim;exact⟨q,c1 c0,u,mI (sL (sw▸he)) a9,sw⟩
 . rcases hW u a8 with rfl|rfl;exact(d2 (i1 h0) a6).elim;exact⟨q,c1 c0,w,mI (sL he) hw0,rfl⟩
 . rcases hW w a5 with rfl|rfl;exact⟨j,c0,u,mI (sL (sw▸he)) a6,sw⟩;exact(d2 (i1 t) hw0).elim
lemma MQ {E:Finset S2}(t:E⊆k.U){g:List (SS C)}{P:S2 -> Prop}(j:∀u w,s(u,w)∈k.U -> (u=k.v\/ w=k.v\/ s(u,w)∈k.Ua) -> PC g s(u,w))(q:∀{e},PC g e -> P e)(z:∀u w,s(u,w)∈E -> u≠k.v -> w≠k.v -> s(u,w)∉k.Ua -> P s(u,w)):∀e∈E,P e:=
 HW fun u w he=>if h:u=k.v\/ w=k.v\/ s(u,w)∈k.Ua then q (j u w (t he) h) else by push Not at h;exact z u w he h.1 h.2.1 h.2.2
abbrev Tg:=∃l:List (SS C),PD l <=1 /\(∀g∈l,g.good /\g.c∈k.Wa /\g.W.card=1 /\∃d:F2,g.c∈k.Ad d∩k.Wa) /\
 ∀u w,s(u,w)∈k.Ua -> u≠k.v -> w≠k.v -> PC l s(u,w)
lemma PN:k.Tg\/ (∃ca0 ca1:F,ca0∈k.Ad 0∩k.Wa /\ca1∈k.Ad 1∩k.Wa /\∀w∈k.Wa,w=ca0\/ w=ca1):=by
 obtain⟨_,_,ag,af⟩:=k.A2
 have aa (d':F2) (hE:k.Ad (1-d')∩k.Wa=∅):k.Tg:=by
  have z {x:F} (hx:x∈k.A (1-d')) (hv:x≠k.v) (hW:x∈k.Wa):False:=nE (hE▸mI (k.HE (1-d') hx hv) hW)
  rcases Ms (k.Ad d'∩k.Wa) with h0|⟨cx,h⟩
  . refine⟨[],by simp,by simp,fun u w he t hw=>by
     have⟨a8,hW⟩:=k.RJ he
     rcases k.ps a8 t hw d' with⟨ha,hb⟩|⟨ha,hb⟩<;>rcases hW with j|j
     . exact nE (h0▸mI (k.HE d' ha t) j)
     . exact(z hb hw j).elim
     . exact(z ha t j).elim
     . exact nE (h0▸mI (k.HE d' hb hw) j)⟩
  . let q:=k.Hc d' cx (d1 (i1 h)) (i2 h) k.Ua K0
    have ab:(k.Ad d'∩k.Wa).card <=1:=by fin_cases d'<;>assumption
    refine⟨[q],by simp[q],fun g hg=>mL hg▸⟨trivial,i2 h,cS _,d',h⟩,fun u w he t hw=>by
     have⟨a8,hW⟩:=k.RJ he
     rcases k.ps a8 t hw d' with⟨ha,hb⟩|⟨ha,hb⟩<;>rcases hW with j|j
     . obtain rfl:=uq ab (mI (k.HE d' ha t) j) h;exact⟨q,c0,w,mI (sL he) hb,rfl⟩
     . exact(z hb hw j).elim
     . exact(z ha t j).elim
     . obtain rfl:=uq ab (mI (k.HE d' hb hw) j) h;exact⟨q,c0,u,mI (sL (sw▸he)) ha,sw⟩⟩
 rcases Ms (k.Ad 0∩k.Wa) with h0|⟨a7,a5⟩;. exact .inl (aa 1 h0)
 rcases Ms (k.Ad 1∩k.Wa) with j|⟨a6,a4⟩;. exact .inl (aa 0 j)
 by_cases ad:k.Wa⊆{a7,a6};. exact .inr ⟨a7,a6,a5,a4,fun w hw=>by grind⟩
 have⟨w3,ac,ah⟩:=Nss ad
 have a9 (d':F2) (cx:F) (h:cx∈k.Ad d'∩k.Wa) (hs:k.Ad d'\{k.v}⊆{cx}):k.Tg:=by
  let q:=k.Hc d' cx (d1 (i1 h)) (i2 h) k.Ua K0
  refine⟨[q],by simp[q],fun g hg=>mL hg▸⟨trivial,i2 h,cS _,d',h⟩,fun u w he t hw=>by
   rcases k.ps (k.RJ he).1 t hw d' with⟨ha,hb⟩|⟨ha,hb⟩
   . obtain rfl:u=cx:=mS (hs (mD (k.HE d' ha t) (R1 t)));exact⟨q,c0,w,mI (sL he) hb,rfl⟩
   . obtain rfl:w=cx:=mS (hs (mD (k.HE d' hb hw) (R1 hw)));exact⟨q,c0,u,mI (sL (sw▸he)) ha,sw⟩⟩
 exact(KN k.o k.ha a5 a4 ac (k.PU _ (i2 a5)) (k.PU _ (i2 a4)) (k.PU _ ac) (by grind) (by grind)).elim
  (fun h0=>.inl (a9 0 a7 a5 h0)) fun j=>.inl (a9 1 a6 a4 j)
lemma Tr {q:F}(Pv:k.v∉k.B0)(g:q∈k.BW): ∀mb∈mixing G11 C,oi C (11+mb)⊆k.B0 -> ∀w∈k.Lv\{q},∀t∈Tp C,∀d:F2, O C (opnd C t d) mb -> w∈N C t (1-d) -> False:=
 fun _ j hs _ hw _ ht _ hr h=>KF k.o k.hb j hs Pv (i1 g) (i2 g) (k.PU q (k.PQ g)) (gA (sE (d1 hw))) (nS (d2 hw)) ht hr h
lemma TK {Lv:Finset F}{Ma:Finset ℕ}(hL:Lv⊆k.Lv)(g:Ma⊆k.Mz)(h:H5 C Lv Ma): (W0For G11 C k.a).card+Ma.card+1 <=2*(centreless G11 C).card+(mixing G11 C).card+(rZero G11 C).card:=by have⟨fw,j,q⟩:=h;exact KG k.o Q3 k.ha k.hb k.Pt (f1 g) (f2 g) (fun _ hw=>sE (hL hw)) j q k.w
lemma TM {Lv:Finset F}{Ma:Finset ℕ}{q:F}(hL:Lv⊆k.Lv\{q})(Pv:k.v∉k.B0)(hq:q∈k.BW)(t:Ma⊆k.Mz)(z:H5 C Lv Ma): (W0For G11 C k.a).card+Ma.card+2 <=2*(centreless G11 C).card+(mixing G11 C).card+(rZero G11 C).card:=by obtain⟨mb,g,j,_,h⟩:=QK k.o k.s k.r k.e;have⟨fw,h1,h2⟩:=z;exact Xa k.o k.ha k.hb k.Pt g j (f1 t) (f2 t) (fun _ hw=>sE (d1 (hL hw))) h1 h2 (fun w hw=>k.Tr Pv hq mb g h w (hL hw)) k.w
lemma Jb {Mb:Finset ℕ}(g:Mb⊆k.Rc):Mb.card+1 <=(mixing G11 C).card:=by
 obtain⟨q,j,z,_,_⟩:=QK k.o k.s k.r k.e;have hn:q∉Mb:=fun h=>by have:=Qy k.o j k.hb (f2 g _ h);omega
 have t:=R3 (Ism ⟨j,f1 g⟩);rwa[Cns hn] at t
lemma Jf {q:F}{Lv Lb:Finset F}{Ma Mb:Finset ℕ}(g:q∈k.Ib)(hL:Lv⊆k.Lv)(a4:∀w∈Lb,s(q,w)∈k.U)(h:Ma⊆k.Mz)(j:Mb⊆k.Rc)(z:H5 C Lv Ma)(a3:H5 C Lb Mb): Ma.card+Mb.card <=(mixing G11 C).card+(rZero G11 C).card /\ ∀mb∈mixing G11 C,mb < k.b -> (∀w∈Lv,∀t∈Tp C,∀d:F2,O C (opnd C t d) mb -> w∈N C t (1-d) -> False) -> Ma.card+Mb.card+1 <=(mixing G11 C).card+(rZero G11 C).card:=by
 have⟨fa,a7,a5⟩:=z;have⟨fb,a8,a6⟩:=a3
 exact Kj k.o k.ha k.hb k.Pt (fun (e:k.v=q)=>k.B (e▸i2 (k.hB01.symm▸g)))
  k.PU (Q1 k.o k.hb (i1 g) (i2 g)).2 (f1 h) (f2 h) (f1 j) (f2 j) (fun _ hw=>sE (hL hw)) a4 a7 a5 a8 a6
lemma J6 {vb q:F}{Lv Lb:Finset F}{Ma Mb:Finset ℕ}(t:vb∈k.Ib)(hL:Lv⊆k.Lv\{q})(Pv:k.v∉k.B0)(hq:q∈k.BW)(a8:∀w∈Lb,s(vb,w)∈k.U)(j:Ma⊆k.Mz)(z:Mb⊆k.Rc)(a4:H5 C Lv Ma)(a5:H5 C Lb Mb): Ma.card+Mb.card+1 <=(mixing G11 C).card+(rZero G11 C).card:=by obtain⟨mb,g,a6,_,h⟩:=QK k.o k.s k.r k.e;exact(k.Jf t (hL.trans ds) a8 j z a4 a5).2 mb g a6 fun w hw=>k.Tr Pv hq mb g h w (hL hw)
lemma T9 (j h:List (SS C))(hS:PD j+PD h <=4)(hG:∀g∈j,g.good)(t:∀e∈k.U,PC (j++h) e)(q:∀g∈j,∀b∈h,g.c≠b.c)(hok:Hn h):k.Pz:=
 Y5 k.L k.s k.r k.e k.w j h hS hG t q hok.1 hok.2
lemma TP {E:Finset S2}{Lv:Finset F}(z:Lv⊆k.Lv)(t:∀w∈Lv,TC C k.a w)(j h:List (SS C))(hG:∀g∈j,g.good)(a3:∀g∈j,∀b∈h,g.c≠b.c)(a5:∀b∈h,b.c≠k.v)(hok:Hn h)(hC:∀e∈E,PP k.v Lv e\/ PC (j++h) e): ∃Ma⊆k.Mz,E.card <=(rFull G11 C).card+(W0For G11 C k.a).card+PD j+PD h+Ma.card /\H5 C Lv Ma:=by have⟨Ma,q,a4,fw,h1,h2⟩:=KU (E:=E) k.o fs (Qg k.o k.a) k.RX (fun _ hw=>sE (z hw)) t j h hG a3 a5 hok.1 hok.2 hC;exact⟨Ma,q,a4,fw,h1,h2⟩
lemma TH {q:F}(a3:q∈k.Ib){E:Finset S2}{Lv Lb:Finset F}(z:Lv⊆k.Lv)(t:∀w∈Lv,TC C k.a w)(a6:∀w∈Lb,s(q,w)∈k.U)(a5:∀w∈Lb,TC C k.b w)(j h:List (SS C))(hG:∀g∈j,g.good)(a4:∀g∈j,∀b∈h,g.c≠b.c)(a8:∀b∈h,b.c≠k.v)(a7:∀b∈h,b.c≠q)(hok:Hn h)(hC:∀e∈E,PP k.v Lv e\/ PP q Lb e\/ PC (j++h) e): ∃Ma⊆k.Mz,∃Mb⊆k.Rc,E.card <=(rFull G11 C).card+(W0For G11 C k.a).card+(W0For G11 C k.b).card+PD j+PD h+Ma.card+Mb.card /\ H5 C Lv Ma /\H5 C Lb Mb:=
 Y9 (E:=E) k.o fs fs (Qg k.o k.a) (Qg k.o k.b) k.RX (k.Tm a3) (fun _ hw=>sE (z hw)) a6 t a5 j h hG a4 a8 a7 hok.1 hok.2 hC
lemma RC (h1:k.BW.card <=1){P:S2 -> Prop}(t:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> P s(u,w)){G:Prop}(f1:∀Lv⊆k.Lv,(∀w∈Lv,TC C k.a w) -> (∀e∈k.U,PP k.v Lv e\/ (∃q∈k.BW,k.v∈k.B0 /\e=s(k.v,q) /\s(k.v,q)∈k.U)\/ P e) -> G)(f2:∀q∈k.BW,k.v∉k.B0 -> (∀w∈k.Lv\{q},TC C k.a w) -> (∀e∈k.U\{s(k.v,q)},PP k.v (k.Lv\{q}) e\/ (∃q'∈k.BW,k.v∈k.B0 /\e=s(k.v,q') /\s(k.v,q')∈k.U)\/ P e) -> G):G:=by
 rcases Ms k.BW with he|⟨q,z⟩
 . exact f1 k.Lv sr (fun w hw=>(k.HQ w hw).elim id fun h=>nE (he▸h)) (k.cv fun u w h g hw=>.inr (t u w h g hw))
 . have j:∀w∈k.Lv\{q},TC C k.a w:=fun w hw=>(k.HQ w (d1 hw)).elim id fun h=>(nS (d2 hw) (uq h1 h z)).elim
   by_cases Pv:k.v∈k.B0
   . exact f1 (k.Lv\{q}) ds j (k.J9 (fun a3=>.inl ⟨q,z,Pv,rfl,a3⟩) fun u w h g hw=>.inr (t u w h g hw))
   . exact f2 q z Pv j (k.TU fun u w h g hw=>.inr (t u w h g hw))
lemma Ta (h1:k.BW.card <=1){P:S2 -> Prop}(hP:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> P s(u,w))(h:∀(E:Finset S2) (Lv:Finset F),Lv⊆k.Lv -> (∀w∈Lv,TC C k.a w) -> (∀e∈E,PP k.v Lv e\/ (∃q∈k.BW,k.v∈k.B0 /\e=s(k.v,q) /\s(k.v,q)∈k.U)\/ P e) -> ∃Ma⊆k.Mz,E.card <=(rFull G11 C).card+(W0For G11 C k.a).card+3+Ma.card /\H5 C Lv Ma):k.Pz:=
 k.RC h1 hP (fun Lv hL z t=>by have⟨Ma,g,a3,j⟩:=h k.U Lv hL z t;have:=k.TK hL g j;omega)
  (fun q hq Pv z t=>by have:=Tw k.U s(k.v,q);have⟨Ma,g,a3,j⟩:=h (k.U\{s(k.v,q)}) (k.Lv\{q}) ds z t;have:=k.TM sr Pv hq g j;omega)
lemma T0 (h1:k.BW.card <=1){vb:F}(z:vb∈k.Ib){Lb:Finset F}(a4:∀w∈Lb,s(vb,w)∈k.U){P:S2 -> Prop}(hP:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> P s(u,w))(a3:∀(E:Finset S2) (Lv:Finset F),Lv⊆k.Lv -> (∀w∈Lv,TC C k.a w) -> (∀e∈E,PP k.v Lv e\/ (∃q∈k.BW,k.v∈k.B0 /\e=s(k.v,q) /\s(k.v,q)∈k.U)\/ P e) -> ∃Ma⊆k.Mz,∃Mb⊆k.Rc,E.card <=(rFull G11 C).card+(W0For G11 C k.a).card+(W0For G11 C k.b).card+2+Ma.card+Mb.card /\ H5 C Lv Ma /\H5 C Lb Mb):k.Pz:=by
 have:=k.TR;have:=k.RW
 exact k.RC h1 hP (fun Lv hL hC hE=>by have⟨Ma,g,Mb,h,a8,j,t⟩:=a3 k.U Lv hL hC hE;have:=(k.Jf z hL a4 g h j t).1;omega)
  (fun q hq Pv hC hE=>by have:=Tw k.U s(k.v,q);have⟨Ma,g,Mb,h,a8,j,t⟩:=a3 (k.U\{s(k.v,q)}) (k.Lv\{q}) ds hC hE;have:=k.J6 z sr Pv hq a4 g h j t;omega)
lemma Mm {P:F -> F -> Prop}{d:F2}{u w:F}(he:s(u,w)∈k.Hk P d): u∉k.Wa /\w∉k.Wa /\u≠k.v /\w≠k.v /\ ((u∈k.Ad d∩k.Wb /\w∈k.Ad (1-d)∩k.B1 /\P u w)\/ (w∈k.Ad d∩k.Wb /\u∈k.Ad (1-d)∩k.B1 /\P w u)):=by obtain⟨q,_,_,j,h,g,t⟩:=k.HY.mp he;have hs:=k.Hq q;have hn:=k.RD q;exact⟨hs.2.1,hs.2.2.1,hn.1,hn.2,(MR.mp j).elim (fun ⟨e1,e2⟩=>e1▸e2▸.inl ⟨h,g,t⟩) fun ⟨e1,e2⟩=>e1▸e2▸.inr ⟨h,g,t⟩⟩
lemma TT (P:F -> F -> Prop): ∃bs:List (SS C),PD bs=(if (k.Hk P 0).Nonempty then 1 else 0)+(if (k.Hk P 1).Nonempty then 1 else 0) /\ Hn bs /\(∀e∈k.Hk P 0∪k.Hk P 1,PC bs e) /\∀b∈bs,b.c∉k.Wa /\b.c≠k.v /\∃d:F2,∃x:F,s(b.c,x)∈k.Hk P d:=by
 classical
 obtain⟨hA02,hA12,_,_⟩:=k.A2
 obtain⟨j0,j1,a4,a5,_,_,a3,t,a6⟩:=KT k.o k.T k.s k.c k.r k.n hA02 hA12
  (k.HG.trans eS) (k.HG.trans eS)
  (fun _ _ h=>(k.Mm h).2.2.2.2.elim (fun a=>.inl ⟨a.1,a.2.1⟩) fun a=>.inr ⟨a.1,a.2.1⟩)
  (fun _ _ h=>(k.Mm h).2.2.2.2.elim (fun a=>.inl ⟨a.1,a.2.1⟩) fun a=>.inr ⟨a.1,a.2.1⟩)
 have a7:(k.Hk P 0).Nonempty -> (k.Hk P 1).Nonempty -> j0.c≠j1.c:=fun ⟨_,g⟩ ⟨_,j⟩ eq=>by obtain⟨_,_,q0⟩:=a3 _ g;obtain⟨_,_,q1⟩:=t _ j;have h0:=k.Mm (q0▸g);have z:=k.Mm (q1▸j);rw[←eq] at z;have a8:=k.PQ;simp only[mem_inter,mem_sdiff] at h0 z;grind
 refine⟨(if (k.Hk P 0).Nonempty then [j0] else [])++(if (k.Hk P 1).Nonempty then [j1] else []),
  Jw _ _ a4 a5,J8 a7 a6,fun e he=>(mU he).elim
   (fun h0=>have hn:(k.Hk P 0).Nonempty:=⟨_,h0⟩;⟨j0,aL (by simp[hn]),a3 _ h0⟩)
   (fun z=>have hn:(k.Hk P 1).Nonempty:=⟨_,z⟩;⟨j1,aR (by simp[hn]),t _ z⟩),
  fun b hb=>by
   rcases RH hb with⟨⟨_,g⟩,rfl⟩|⟨⟨_,j⟩,rfl⟩
   . obtain⟨x,_,q⟩:=a3 _ g;have hs:=k.Mm (q▸g);exact⟨hs.1,hs.2.2.1,0,x,q▸g⟩
   . obtain⟨x,_,q⟩:=t _ j;have hs:=k.Mm (q▸j);exact⟨hs.1,hs.2.2.1,1,x,q▸j⟩⟩
structure ItB where
 l:List (SS C)
 bon:ℕ
 hS:PD l <=1+bon
 hG:∀g∈l,g.good /\(g.c∈k.H8\/ g.c∈k.BW)
 hB01:bon=0\/ bon=1
 hBon:bon=1 -> ∃g1∈l,∃g2∈l,g1.c≠g2.c /\Ga g1.c g2.c /\g2.c∈g1.W.biUnion (oi C) /\g1.c∈g2.W.biUnion (oi C)
 c0:∀{p q:F},s(p,q)∈k.U -> p∈k.H8 -> q∈k.B1 -> PC l s(p,q)
 c1:∀{p q:F},s(p,q)∈k.U -> p∈k.BW -> q∈k.B0 -> PC l s(p,q)
noncomputable def J7 (h01:k.H8.card <=1)(h11:k.BW.card <=1)(hdisj:∀x∈k.H8,x∉k.B1):k.ItB:=by
 classical
 let l0:List (SS C):=if h:k.H8.Nonempty then [k.R5 k.db h.choose (i1 h.choose_spec) (i2 h.choose_spec)] else [];let l1:List (SS C):=if h:k.BW.Nonempty then [k.R5 (1-k.db) h.choose (i1 h.choose_spec) (i2 h.choose_spec)] else [];let bon:=if k.H8.Nonempty /\k.BW.Nonempty then 1 else 0;refine⟨l0++l1,bon,?_,?_,?_,?_,?_,?_⟩
 . dsimp only[l0,l1,bon];rw[PT];by_cases h0:k.H8.Nonempty<;>by_cases h1:k.BW.Nonempty<;>simp[h0,h1,Q9,Q0]
 . intro g hg;rcases mA hg with h|h<;>dsimp only[l0,l1] at h<;>split_ifs at h with hn
   . exact mL h▸⟨trivial,.inl hn.choose_spec⟩
   . cases h
   . exact mL h▸⟨trivial,.inr hn.choose_spec⟩
   . cases h
 . dsimp only[bon];split_ifs<;>simp
 . intro hb1
   have⟨h0,h1⟩:k.H8.Nonempty /\k.BW.Nonempty:=by dsimp only[bon] at hb1;split_ifs at hb1 with h;exact h
   have s0:=h0.choose_spec;have s1:=h1.choose_spec;let g1:=k.R5 k.db h0.choose (i1 s0) (i2 s0);let g2:=k.R5 (1-k.db) h1.choose (i1 s1) (i2 s1)
   exact⟨g1,aL (by simp[l0,h0,g1]),g2,aR (by simp[l1,h1,g2]),fun e=>hdisj _ s0 ((show h0.choose=h1.choose from e)▸i1 s1),
    k.M8 (i1 s0) (i2 s0) (i1 s1),Mbu ⟨k.ob (1-k.db),ms,i1 s1⟩,Mbu ⟨k.ob (1-(1-k.db)),ms,by rw[H4];exact i1 s0⟩⟩
 . intro p q he hp hq;have h0:k.H8.Nonempty:=⟨p,hp⟩;have s0:=h0.choose_spec;obtain rfl:p=h0.choose:=uq h01 hp s0
   exact⟨k.R5 k.db h0.choose (i1 s0) (i2 s0),aL (by simp[l0,h0]),q,mI (sL he) hq,rfl⟩
 . intro p q he hp hq;have h1:k.BW.Nonempty:=⟨p,hp⟩;have s1:=h1.choose_spec;obtain rfl:p=h1.choose:=uq h11 hp s1
   exact⟨k.R5 (1-k.db) h1.choose (i1 s1) (i2 s1),aR (by simp[l1,h1]),q,mI (sL he) (by rw[H4];exact hq),rfl⟩
lemma ItB.gd {k:Z2B C}(ib:k.ItB){j:List (SS C)}(h:∀g∈j,g.good):∀g∈j++ib.l,g.good:=
 fun g q=>(mA q).elim (h g) fun t=>(ib.hG g t).1
lemma ItB.sp {k:Z2B C}(ib:k.ItB){q t:List (SS C)}(hG:∀g∈q,g.c∈k.Wa)(j:∀b∈t,b.c∉k.Wa /\b.c∉k.H8): ∀g∈q++ib.l,∀b∈t,g.c≠b.c:=fun g hg b hb e=>
 (mA hg).elim (fun h=>(j b hb).1 (e▸hG g h)) fun h=>(ib.hG g h).2.elim (fun h0=>(j b hb).2 (e▸h0)) fun z=>(j b hb).1 (e▸k.PQ z)
lemma ItB.ub {k:Z2B C}(ib:k.ItB){u w:F}(he:s(u,w)∈k.U)(hs:(u∈k.B0 /\w∈k.B1)\/ (u∈k.B1 /\w∈k.B0))(hw:(u∈k.Wb /\TC C k.b u)\/ (w∈k.Wb /\TC C k.b w)):PC ib.l s(u,w):=by
 rcases hs with⟨a,b⟩|⟨a,b⟩<;>rcases hw with⟨c,_⟩|⟨c,_⟩
 . exact ib.c0 he (mI a c) b
 . exact by simpa[sw] using ib.c1 (sw▸he) (mI b c) a
 . exact ib.c1 he (mI a c) b
 . exact by simpa[sw] using ib.c0 (sw▸he) (mI b c) a
lemma TN (ib:k.ItB)(j h:List (SS C))(hS:PD j+PD h <=3)(hG:∀g∈j,g.good /\g.c∈k.Wa)(hB:∀b∈h,b.c∉k.Wa /\b.c∉k.H8)(hok:Hn h)(hC:∀e∈k.U,PC ((j++ib.l)++h) e):k.Pz:=by
 have q:=ib.gd fun g z=>(hG g z).1;have t:=ib.sp (fun g z=>(hG g z).2) hB;have:=ib.hS
 rcases ib.hB01 with h0|h1
 . exact k.T9 (j++ib.l) h (by simp;omega) q hC t hok
 . have⟨g1,a8,g2,a5,ne,a3,a6,a4⟩:=ib.hBon h1
   exact Wr k.L k.s k.r k.e k.w (j++ib.l) h (by rw[PX,PX,PT];omega) q hC t hok.1 hok.2 (aR a8) (aR a5) ne a3 a6 a4
lemma J3 (ib:k.ItB)(E:Finset S2)(Lv:Finset F)(q h:List (SS C))(a4:Lv⊆k.Lv)(a3:∀w∈Lv,TC C k.a w)(hG:∀g∈q,g.good /\g.c∈k.Wa)(z:∀b∈h,b.c∉k.Wa /\b.c≠k.v /\b.c∉k.H8)(hok:Hn h)(hC:∀e∈E,PP k.v Lv e\/ PC ((q++ib.l)++h) e): ∃Ma⊆k.Mz,E.card <=(rFull G11 C).card+(W0For G11 C k.a).card+PD q+1+PD h+Ma.card /\H5 C Lv Ma:=by
 have a6:=ib.gd fun g hg=>(hG g hg).1;have a5:=ib.sp (fun g hg=>(hG g hg).2) fun b hb=>⟨(z b hb).1,(z b hb).2.2⟩;have:=ib.hS
 rcases ib.hB01 with h0|h1
 . obtain⟨Ma,j,t,hF⟩:=k.TP a4 a3 (q++ib.l) h a6 a5 (fun b hb=>(z b hb).2.1) hok hC
   rw[PT] at t;exact⟨Ma,j,by omega,hF⟩
 . have⟨g1,ab,g2,aa,ne,a8,ae,a9⟩:=ib.hBon h1
   have⟨Ma,j,t,fw,ac,af⟩:=YM (E:=E) k.o fs (Qg k.o k.a) k.RX
    (fun _ hw=>sE (a4 hw)) a3 (q++ib.l) h a6 a5 (fun b hb=>(z b hb).2.1) hok.1 hok.2 hC (aR ab) (aR aa) ne a8 ae a9
   rw[PX,PX,PT] at t;exact⟨Ma,j,by omega,fw,ac,af⟩
lemma Jx (ib:k.ItB){vb:F}(a6:vb∈k.Ib)(E:Finset S2)(Lv Lb:Finset F)(h:List (SS C))(a8:Lv⊆k.Lv)(a5:∀w∈Lv,TC C k.a w)(a7:∀w∈Lb,s(vb,w)∈k.U)(a9:∀w∈Lb,TC C k.b w)(hG:∀g∈h,g.good)(hC:∀e∈E,PP k.v Lv e\/ PP vb Lb e\/ PC (h++ib.l) e): ∃Ma⊆k.Mz,∃Mb⊆k.Rc,E.card <=(rFull G11 C).card+(W0For G11 C k.a).card+(W0For G11 C k.b).card+PD h+1+Ma.card+Mb.card /\ H5 C Lv Ma /\H5 C Lb Mb:=by
 have aa:=ib.gd hG;have:=ib.hS;have hC':∀e∈E,PP k.v Lv e\/ PP vb Lb e\/ PC ((h++ib.l)++[]) e:=by simpa using hC
 rcases ib.hB01 with h0|h1
 . have⟨Ma,j,Mb,q,z,t,a3⟩:=k.TH a6 a8 a5 a7 a9 (h++ib.l) [] aa (by simp) (by simp) (by simp) b0 hC'
   simp only[PT,H0] at z;exact⟨Ma,j,Mb,q,by omega,t,a3⟩
 . have⟨g1,ae,g2,ad,ne,ab,af,ac⟩:=ib.hBon h1
   have⟨Ma,j,Mb,q,z,t,a3⟩:=Zw (E:=E) k.o fs fs (Qg k.o k.a) (Qg k.o k.b)
    k.RX (k.Tm a6) (fun _ hw=>sE (a8 hw)) a7 a5 a9 (h++ib.l) [] aa (by simp) (by simp) (by simp) (by simp) (by simp) hC' (aR ae) (aR ad) ne ab af ac
   rw[PX,PX,PT,H0] at z;exact⟨Ma,j,Mb,q,by omega,t,a3⟩
lemma Jr (ib:k.ItB){q:F}(j:q∈k.Ib){Lb:Finset F}(z:∀w∈Lb,s(q,w)∈k.U)(t:∀w∈Lb,TC C k.b w)(h:List (SS C))(hS:PD h <=2)(hG:∀g∈h,g.good)(hC:∀e∈k.U,PP q Lb e\/ PC (h++ib.l) e):k.Pz:=by
 have a3:=ib.gd hG;have:=ib.hS;have hC':∀e∈k.U,PP q Lb e\/ PC ((h++ib.l)++[]) e:=by simpa using hC
 rcases ib.hB01 with h0|h1
 . exact KW k.L k.s k.r k.e (i1 j) (i2 j) z t (h++ib.l) [] (by rw[PX,PX,PT,H0];omega) a3 (by simp) (by simp) (by simp) (by simp) hC'
 . have⟨g1,aa,g2,a8,ne,a4,a9,a5⟩:=ib.hBon h1
   obtain⟨Mb,a6,a7,_⟩:=YM (E:=k.U) k.o fs (Qg k.o k.b) (k.Tm j)
    z t (h++ib.l) [] a3 (by simp) (by simp) (by simp) (by simp) hC' (aR aa) (aR a8) ne a4 a9 a5
   have:=k.RW;have:=k.Jb a6;rw[PX,PX,PT,H0] at a7;omega
lemma Jd {q:F}(hq:q∈k.BW)(z:∀w∈k.BW,w=q)(a4:k.Eb=∅)(a6:∀u w,s(u,w)∈k.Ub -> Px (k.R5 (1-k.db) q (i1 hq) (i2 hq)) s(u,w)):k.Pz:=by
 let j:=k.R5 (1-k.db) q (i1 hq) (i2 hq);have h1:k.BW.card <=1:=card_le_one.mpr fun x hx y hy=>(z x hx).trans (z y hy).symm
 rcases k.PN with⟨l,hS,hG,hC⟩|⟨ax,aw,h0,af,hW⟩
 . exact k.Ta h1 (P:=PC (j::l)) (fun u w he hu hw=>by
    by_cases a5:s(u,w)∈k.Ub;. exact HT (a6 u w a5)
    have ab:s(u,w)∈k.Ua:=by by_contra t;exact nE (a4▸k.M5 he a5 t)
    exact Hy (hC u w ab hu hw))
    (fun E Lv ad a9 ac=>by
     obtain⟨Ma,a8,ah,hF⟩:=k.TP ad a9 (j::l) [] (fun g hg=>(mC hg).elim (fun e=>e▸trivial) fun h=>(hG g h).1) (by simp) (by simp) b0
      (fun e he=>by
       rcases ac e he with h|⟨q',ae,Pv,rfl,aa⟩|h;exact .inl h
       . obtain rfl:=z q' ae;exact .inr (hL (HT ⟨k.v,mI (sL (sw▸aa)) (by rw[H4];exact Pv),sw⟩))
       . exact .inr (hL h))
     simp only[PG,H0,j,Q9,Q0,Cs] at ah;exact⟨Ma,a8,by omega,hF⟩)
 . have⟨gs,gS,gG,gC⟩:=k.Mq h0 af hW
   exact k.T9 (j::gs) [] (by simp[gS,j]) (fun g hg=>(mC hg).elim (fun e=>e▸trivial) fun h=>(gG g h).1)
    (k.MQ sr gC (fun h=>hL (Hy h)) fun u w he _ _ t=>hL (HT (a6 u w (by by_contra ag;exact nE (a4▸k.M5 he ag t))))) (by simp) b0
abbrev RZ (Pw Pb:F -> Prop):=
 (∃x y:F,s(x,y)∈k.Eb /\x∈k.Ad 0∩k.Wb /\y∈k.Ad 1∩k.B1 /\Pw x /\Pb y) /\
 (∃x y:F,s(x,y)∈k.Eb /\x∈k.Ad 1∩k.Wb /\y∈k.Ad 0∩k.B1 /\Pw x /\Pb y)
lemma MD {P:F -> F -> Prop}{Pw Pb:F -> Prop}(h:∀u w,P u w -> Pw u /\Pb w)(h0:(k.Hk P 0).Nonempty)(q:(k.Hk P 1).Nonempty):k.RZ Pw Pb:=by obtain⟨_,g⟩:=h0;obtain⟨_,j⟩:=q;obtain⟨e0,x0,y1,rfl,t,z,p0⟩:=k.HY.mp g;obtain⟨e1,v1,u0,rfl,hv,hu,p1⟩:=k.HY.mp j;exact⟨⟨x0,y1,e0,t,z,h _ _ p0⟩,⟨v1,u0,e1,hv,hu,h _ _ p1⟩⟩
lemma MJ {Pw Pb:F -> Prop}(d:F2)(h:k.RZ Pw Pb): ∃x y z u:F,Ga x y /\Ga z u /\x∉k.Wa /\y∉k.Wa /\z∉k.Wa /\u∉k.Wa /\ x≠k.v /\y≠k.v /\z≠k.v /\u≠k.v /\x∈k.Ad d /\x∈k.Wb /\Pw x /\y∈k.Ad (1-d) /\y∈k.B1 /\Pb y /\ z∈k.Ad (1-d) /\z∈k.Wb /\Pw z /\u∈k.Ad d /\u∈k.B1 /\Pb u:=by
 obtain⟨⟨x0,y1,e0,hx,hy,px,py⟩,⟨v1,u0,e1,hv,hu,pv,pu⟩⟩:=h;have s0:=k.Hq e0;have s1:=k.Hq e1;have n0:=k.RD e0;have n1:=k.RD e1
 fin_cases d
 . exact⟨x0,y1,v1,u0,gA (eS e0),gA (eS e1),s0.2.1,s0.2.2.1,s1.2.1,s1.2.2.1,n0.1,n0.2,n1.1,n1.2,
    i1 hx,i2 hx,px,i1 hy,i2 hy,py,i1 hv,i2 hv,pv,i1 hu,i2 hu,pu⟩
 . exact⟨v1,u0,x0,y1,gA (eS e1),gA (eS e0),s1.2.1,s1.2.2.1,s0.2.1,s0.2.2.1,n1.1,n1.2,n0.1,n0.2,
    i1 hv,i2 hv,pv,i1 hu,i2 hu,pu,i1 hx,i2 hx,px,i1 hy,i2 hy,py⟩
lemma TD {c0 h:F}(d:F2)(hc:c0∈k.Ad d∩k.Wa)(hw:h∈k.Wa)(t:h≠c0)(g:k.v∈k.B0)(a5:k.RZ (fun _=>True) (fun _=>True)):False:=by
 obtain⟨x,y,z,u,xy,zu,_,_,_,_,_,_,_,_,xA,xW,_,yA,yB,_,q,zW,_,uA,uB,_⟩:=k.MJ d a5;have ad:=k.PQ;have j:=i2 hc;have cd:=d1 (i1 hc)
 refine XS (k.PU c0 j) (k.PU h hw) t (k.Hg cd j (d1 yA)) ?_ ?_ (k.Hg cd j (d1 q)) ?_ ?_ ?_
  (k.My g yB zW) xy.symm ?_ ?_ ?_ ?_ ?_ (k.H7 d xA q hw) zu ?_ ?_ ?_ ?_ ?_ ?_ (k.H7 d uA yA hw) (k.My g uB xW)<;>
  (simp only[mem_inter,mem_sdiff] at*;grind)
lemma TZ {c0 j a7:F}(d:F2)(hc:c0∈k.Ad d∩k.Wa)(hw:j∈k.Wa)(t:j≠c0)(g:a7∈k.H8)(a5:k.RZ (fun x=>x∉k.B0) (fun _=>True)):False:=by
 obtain⟨x,y,z,u,xy,zu,_,_,_,_,_,_,_,_,xA,xW,_,yA,yB,_,q,zW,_,uA,uB,_⟩:=k.MJ d a5;have ac:=k.PQ;have h:=i2 hc;have cd:=d1 (i1 hc)
 refine Xn (k.PU c0 h) (k.PU j hw) t (k.Hg cd h (d1 yA)) ?_ ?_ (k.Hg cd h (d1 q)) ?_ ?_ ?_
  xy.symm ?_ ?_ ?_ ?_ ?_ (k.H7 d xA q hw) zu ?_ ?_ ?_ ?_ ?_ ?_ (k.H7 d uA yA hw)
  (k.M8 (i1 g) (i2 g) yB).symm (k.M8 (i1 g) (i2 g) uB) ?_ ?_<;>(simp only[mem_inter,mem_sdiff] at*;grind)
lemma Rm {c0 g t:F}(an:∀x∈k.B0,x∉k.B1)(d:F2)(hc:c0∈k.Ad d∩k.Wa)(ab:g∈k.BW)(a9:g≠c0)(ad:k.H8=∅)(j:t∈k.B0)(a4:t≠k.v)(a6:Ga g t)(aa:k.RZ (fun _=>True) (fun _=>True)):False:=by
 obtain⟨x,y,z,u,xy,zu,_,_,_,_,_,_,_,_,xA,xW,_,yA,yB,_,zA,zW,_,uA,uB,_⟩:=k.MJ d aa;have am:=k.PQ;have q:=k.PQ ab;have cW:=i2 hc;have cd:=d1 (i1 hc);have al:t∉k.Wb:=fun h=>k.n0 ad j h
 refine Xd (k.PU c0 cW) (k.PU g q) a9 (k.Hg cd cW (d1 yA)) ?_ ?_ (k.Hg cd cW (d1 zA)) ?_ ?_ ?_
  xy.symm ?_ ?_ ?_ ?_ ?_ (k.H7 d xA zA q) zu ?_ ?_ ?_ ?_ ?_ ?_ (k.H7 d uA yA q)
  a6 a4 ?_ ?_ ?_ ?_ (k.My j uB xW) (k.My j yB zW)<;>(simp only[mem_inter,mem_sdiff] at*;grind)
set_option maxHeartbeats 800000 in
lemma Jn (h2:2 <=k.BW.card):k.Pz:=by
 classical
 have b7:∀x∈k.B0,x=k.v:=fun x t=>by
  by_contra ne
  have hc:k.BW.card <=1:=(R3 fun y hy=>Fm ⟨Uv _,k.PU y (k.PQ hy),(k.M8 (i1 hy) (i2 hy) (QE t)).symm⟩).trans (Q3 k.v x (Ne.symm ne));omega
 have Pv:k.v∈k.B0:=by have⟨z,hz⟩:=k.e;exact b7 z hz▸hz
 obtain⟨_,_,e7,e4⟩:=k.A2
 have bm:∀u w,s(u,w)∈k.Ub -> u=k.v\/ w=k.v:=fun u w he=>by obtain⟨_,⟨_,af,rfl|rfl⟩,_⟩:=k.M6 he;exact .inl (b7 _ af);exact .inr (b7 _ af)
 let P:F -> F -> Prop:=fun _ _=>True;set E:=k.Hk P
 have br:∀u w,s(u,w)∈k.Eb -> s(u,w)∈E 0\/ s(u,w)∈E 1:=fun u w he=>by
  obtain⟨p,q,a3,c7,bu,_,_,_,_,h01⟩:=k.Es he
  exact h01.elim (fun a=>.inl (k.HY.mpr ⟨he,p,q,a3,mI a.1 c7,mI a.2 bu,trivial⟩))
   fun a=>.inr (k.HY.mpr ⟨he,p,q,a3,mI a.1 c7,mI a.2 bu,trivial⟩)
 rcases k.PN with⟨l,sA,gA,cA⟩|⟨e6,e9,h0,h1,hW⟩
 swap
 . have⟨gs,gS,gG,gC⟩:=k.Mq h0 h1 hW;have⟨bs,bS,b5,bC,bW⟩:=k.TT P
   exact k.T9 gs bs (by split_ifs at bS<;>omega) (fun g hg=>(gG g hg).1) (k.MQ sr gC hL fun u w he hu hw df=>
    hR (bC _ ((br u w (k.M5 he (fun hb=>by rcases bm u w hb with h|h<;>grind) df)).elim uL uR))) (fun g hg b hb e=>(bW b hb).1 (e▸(gG g hg).2)) b5
 have b8 (gs bl:List (SS C)) (hS:PD gs+PD bl <=2) (hG:∀g∈gs,g.good /\g.c∈k.Wa)
   (hB:∀b∈bl,b.c∉k.Wa /\b.c≠k.v /\(b.W={k.oa 0}\/ b.W={k.oa 1})) (b5:Hn bl)
   (hC:∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> PC (gs++bl) s(u,w)):k.Pz:=by
  set Wv:Finset ℕ:=insert (k.ob (1-k.db)) (W0For G11 C k.a)
  obtain⟨itv,Lm,Ma,cr,bz,cw,dd,_,e5,hF,d5⟩:=
   Ra k.o (L:=k.Lv) (W:=Wv) fs (fun z hz=>(Nsp hz).elim (fun e=>e▸Qe k.o k.hb (1-k.db)) (Qg k.o k.a z))
    (fun _=>sE) (fun w hw=>(k.HQ w hw).elim (fun a=>a.elim (fun h0=>.inl (Bub _ (subset_insert _ _) h0)) .inr)
     fun dc=>.inl (Mbu ⟨k.ob (1-k.db),mem_insert_self _ _,i1 dc⟩)) False False.elim
  have:=k.TK sr cr hF;have:=Tq k.U k.v Lm
  have c6:itv.L⊆k.Wa:=fun w hw=>(k.HQ w (dd hw)).elim k.tW fun h=>k.PQ h
  have hok':=Jt b5 (fun b hb e=>(hB b hb).2.1 (e.trans bz)) fun b hb=>.inr (by
   have bx (d:F2) (hW:b.W={k.oa d}):(b.W.biUnion (oi C)∩itv.L).card <=1:=by rw[hW,Sbu];exact(R3 fun x t=>mI (k.HE d (i1 t) fun e=>k.MG (e▸c6 (i2 t))) (c6 (i2 t))).trans (by fin_cases d<;>assumption)
   exact(hB b hb).2.2.elim (bx 0) (bx 1))
  have dj:=QS (E:=k.U\PY k.v Lm) k.o gs (itv::bl) (fun g hg=>(hG g hg).1)
   (k.TV (fun _ _ hv d6=>hR (HT (d5 hv d6))) fun u w he _ hu hw=>Rs (hC u w he hu hw) fun _ h=>(mA h).elim aL fun h'=>aR (c1 h'))
   (fun g hg b hb e=>(mC hb).elim (fun h=>k.MG ((e.trans (h▸bz))▸(hG g hg).2)) fun cu=>(hB b cu).1 (e▸(hG g hg).2)) hok'.1 hok'.2
  have:Wv.card <=(W0For G11 C k.a).card+1:=Cil _ _
  rw[PX,PX,PG,cw] at dj;omega
 have bk (d:F2) (pA:Bool) (hc:(if pA then k.dA d else k.dB d).card <=1):
   ∃j:SS C,j.W={k.oa (if pA then 1-d else d)} /\j.L⊆(if pA then k.dB d else k.dA d) /\
    ((E d).Nonempty -> j.c≠k.v /\j.c∉k.Wa /\j.c∈k.Ad d∩k.Wb∪k.Ad (1-d)∩k.B1) /\∀e∈E d,Px j e:=by
  have hS:∀u w,s(u,w)∈E d -> ∃u' w':F,s(u,w)=s(u',w') /\u'∈k.dA d /\w'∈k.dB d:=fun u w he=>by obtain⟨hE,u',w',a3,a5,a6,_⟩:=k.HY.mp he;have hs:=k.Hq (a3▸hE);exact⟨u',w',a3,mD a5 hs.2.1,mD a6 hs.2.2.1⟩
  cases pA<;>simp only[Bool.false_eq_true,↓reduceIte] at hc ⊢
  . have⟨cy,bn⟩:=H1 hc
    refine⟨mW C cy (Q4 cy (E d)∩k.dA d) (k.oa d) (Qe k.o k.ha d) (fun _ t=>d1 (i1 (d1 (i2 t))))
     (fun _ t=>eS (k.HG (sE (i1 t)))) False False.elim,rfl,Ir,
     R9 fun u w he=>by obtain⟨_,w',a3,_,a6⟩:=hS u w he;obtain rfl:=bn w' a6;exact⟨(k.RD (k.HG (a3▸he))).2,d2 a6,uR (d1 a6)⟩,
     HW fun u w he=>by obtain⟨_,_,a3,a5,a6⟩:=hS u w he;rcases MR.mp a3 with⟨rfl,rfl⟩|⟨rfl,rfl⟩;obtain rfl:=bn w a6;exact⟨u,mI (sL (sw▸he)) a5,sw⟩;obtain rfl:=bn u a6;exact⟨w,mI (sL he) a5,rfl⟩⟩
  . have⟨cx,ba⟩:=H1 hc
    refine⟨mW C cx (Q4 cx (E d)∩k.dB d) (k.oa (1-d)) (Qe k.o k.ha (1-d)) (fun _ t=>d1 (i1 (d1 (i2 t))))
     (fun _ t=>eS (k.HG (sE (i1 t)))) False False.elim,rfl,Ir,
     R9 fun u w he=>by obtain⟨u',_,a3,a5,_⟩:=hS u w he;obtain rfl:=ba u' a5;exact⟨(k.RD (k.HG (a3▸he))).1,d2 a5,uL (d1 a5)⟩,
     HW fun u w he=>by obtain⟨_,_,a3,a5,a6⟩:=hS u w he;rcases MR.mp a3 with⟨rfl,rfl⟩|⟨rfl,rfl⟩;obtain rfl:=ba u a5;exact⟨w,mI (sL he) a6,rfl⟩;obtain rfl:=ba w a5;exact⟨u,mI (sL (sw▸he)) a6,sw⟩⟩
 have bq (gs:List (SS C)) (hS:PD gs <=1) (hG:∀g∈gs,g.good /\g.c∈k.Wa)
   (hUa:∀u w,s(u,w)∈k.Ua -> u≠k.v -> w≠k.v -> PC gs s(u,w)) (d:F2) (hO:E (1-d)=∅):k.Pz:=by
  have hR (pA:Bool) (hc:(if pA then k.dA d else k.dB d).card <=1):k.Pz:=by
   obtain⟨j,hW,_,c4,d9⟩:=bk d pA hc;have de:j.W={k.oa 0}\/ j.W={k.oa 1}:=by cases pA<;>fin_cases d<;>simp at hW<;>first|exact .inl hW|exact .inr hW
   exact b8 gs (if (E d).Nonempty then [j] else []) (by split_ifs<;>simp[hW]<;>omega) hG
    (fun b hb=>by split_ifs at hb with hn;rw[mL hb];exact⟨(c4 hn).2.1,(c4 hn).1,de⟩;cases hb) (Ju _ j)
    (fun u w he hu hw=>by
     by_cases al:s(u,w)∈k.Ub;. rcases bm u w al with h|h<;>grind
     by_cases ak:s(u,w)∈k.Ua;. exact hL (hUa u w ak hu hw)
     have c9:s(u,w)∈E d:=by rcases br u w (k.M5 he al ak) with h0|h1<;>fin_cases d;exact h0;exact nE (hO▸h0);exact nE (hO▸h1);exact h1
     have hn:(E d).Nonempty:=⟨_,c9⟩;exact⟨j,aR (by simp[hn]),d9 _ c9⟩)
  exact(k.TE d).elim (hR true) (hR false)
 by_cases ar:∀u w,s(u,w)∈k.Ua -> u=k.v\/ w=k.v
 . have b6 (d:F2) (h1:2 <=(k.dA d).card) (h2':2 <=(k.dB (1-d)).card)
     (hEw:∃y∈k.dB d,∀x∈k.dA d,Ga y x) (hEb:∃v1∈k.dA (1-d),∀u∈k.dB (1-d),Ga v1 u):False:=by
    have⟨xa,ae,xb,ag,ck⟩:=RQ h1;have⟨ua,a9,ub,aa,cl⟩:=RQ h2';have⟨ee,cf,Mq,cg,ce⟩:=RQ h2;have⟨y1,a8,c8⟩:=hEw;have⟨v1,Pu,c3⟩:=hEb;have a7:=k.PQ cf;have a4:=k.PQ cg;have bp:=i1 (d1 ae);have bg:=i1 (d1 ag);have vD:=i1 (d1 Pu);have yD:=i1 (d1 a8);have b4:ua∈k.Ad d:=by have:=i1 (d1 a9);rwa[H4] at this
    have bb:ub∈k.Ad d:=by have:=i1 (d1 aa);rwa[H4] at this
    have nw {x w:F} (t:x∉k.Wa) (hw:w∈k.Wa):=(k.Ja t hw).symm
    exact YX (c8 xa ae) (c8 xb ag) ck (k.Rx (d2 a8) (i2 (d1 a8)) (i2 (d1 Pu))).symm (k.T3 bp vD).symm (k.T3 bg vD).symm
     (c3 ua a9) (k.T3 b4 yD) (k.Rx (d2 a9) (i2 (d1 a9)) (i2 (d1 ae))) (k.Rx (d2 a9) (i2 (d1 a9)) (i2 (d1 ag)))
     (c3 ub aa) cl (k.T3 bb yD) (k.Rx (d2 aa) (i2 (d1 aa)) (i2 (d1 ae))) (k.Rx (d2 aa) (i2 (d1 aa)) (i2 (d1 ag)))
     (nw (d2 a8) a7) (nw (d2 ae) a7) (nw (d2 ag) a7) (nw (d2 Pu) a7) (nw (d2 a9) a7) (nw (d2 aa) a7)
     (k.H7 d bp vD a7) (k.H7 d bg vD a7) (k.H7 d b4 yD a7) (k.H7 d bb yD a7)
     ce (nw (d2 a8) a4) (nw (d2 ae) a4) (nw (d2 ag) a4) (nw (d2 Pu) a4) (nw (d2 a9) a4) (nw (d2 aa) a4)
     (k.H7 d bp vD a4) (k.H7 d bg vD a4) (k.H7 d b4 yD a4) (k.H7 d bb yD a4)
   have dk:((k.dA 0).card <=1 /\(k.dA 1).card <=1)\/ ((k.dB 0).card <=1 /\(k.dB 1).card <=1)\/ E 0=∅\/ E 1=∅:=by
    by_contra! h;obtain⟨h1,h2',⟨_,he0⟩,⟨_,he1⟩⟩:=h
    obtain⟨e0,x0,y1,rfl,af,a8,_⟩:=k.HY.mp he0;obtain⟨e1,v1,u0,rfl,Pu,bh,_⟩:=k.HY.mp he1
    rcases k.TE 0 with c5|cb<;>rcases k.TE 1 with e8|ef
    . have:=h1 c5;omega
    . exact b6 1 (by have:=h1 c5;omega) (show 2 <=(k.dB 0).card by by_contra h';have:=h2' (by omega);omega)
       ⟨u0,mD bh (k.Hq e1).2.2.1,fun z hz=>(k.HX 1 (d1 (i1 (d1 hz))) (i2 (d1 hz)) (d1 (i1 bh)) (i2 bh)).symm⟩
       ⟨x0,mD af (k.Hq e0).2.1,fun y hy=>k.HX 0 (d1 (i1 af)) (i2 af) (d1 (i1 (d1 hy))) (i2 (d1 hy))⟩
    . exact b6 0 (by by_contra h';have:=h1 (by omega);omega) (show 2 <=(k.dB 1).card by have:=h2' cb;omega)
       ⟨y1,mD a8 (k.Hq e0).2.2.1,fun x t=>(k.HX 0 (d1 (i1 (d1 t))) (i2 (d1 t)) (d1 (i1 a8)) (i2 a8)).symm⟩
       ⟨v1,mD Pu (k.Hq e1).2.1,fun u hu=>k.HX 1 (d1 (i1 Pu)) (i2 Pu) (d1 (i1 (d1 hu))) (i2 (d1 hu))⟩
    . have:=h2' cb;omega
   have aq (pA:Bool) (b9:(if pA then k.dA 0 else k.dB 0).card <=1) (hc1:(if pA then k.dA 1 else k.dB 1).card <=1):k.Pz:=by
    obtain⟨j0,ah,_,bd,cn⟩:=bk 0 pA b9;have⟨j1,ap,ca,be,cm⟩:=bk 1 pA hc1;let bl:=(if (E 0).Nonempty then [j0] else [])++(if (E 1).Nonempty then [j1] else [])
    have h01:(E 0).Nonempty -> (E 1).Nonempty -> j0.c≠j1.c:=fun bf b3 eq=>by have h0:=bd bf;have h1:=be b3;rw[←eq] at h1;have ea:=k.PQ;simp only[mem_union,mem_inter,mem_sdiff] at h0 h1;grind
    have hW0':j0.W={k.oa 0}\/ j0.W={k.oa 1}:=by cases pA<;>simp at ah<;>[exact .inl ah;exact .inr ah]
    have hW1':j1.W={k.oa 0}\/ j1.W={k.oa 1}:=by cases pA<;>simp at ap<;>[exact .inr ap;exact .inl ap]
    have cj:Rb j0 j1:=.inl (by
     cases pA<;>simp at ah ca<;>rw[ah,Sbu]<;>
      exact(card_eq_zero.mpr (Ee.mpr fun x t=>d2 (i1 (d1 (ca (i2 t)))) (i1 t)))▸Nat.zero_le 1)
    exact b8 [] bl (by simp only[H0,bl,PT];split_ifs<;>simp[ah,ap]) (by simp)
     (fun b hb=>(RH hb).elim (fun ⟨h0,e⟩=>e▸⟨(bd h0).2.1,(bd h0).1,hW0'⟩) fun ⟨h1,e⟩=>e▸⟨(be h1).2.1,(be h1).1,hW1'⟩)
     (J8 h01 cj) (fun u w he hu hw=>by
      by_cases al:s(u,w)∈k.Ub;. rcases bm u w al with h|h<;>grind
      by_cases ak:s(u,w)∈k.Ua;. rcases ar u w ak with h|h<;>grind
      rcases br u w (k.M5 he al ak) with h0|h1
      . have hn:(E 0).Nonempty:=⟨_,h0⟩;exact⟨j0,by simp[bl,hn],cn _ h0⟩
      . have hn:(E 1).Nonempty:=⟨_,h1⟩;exact⟨j1,by simp[bl,hn],cm _ h1⟩)
   have ho:=bq [] (by simp) (by simp) fun u w he hu hw=>by rcases ar u w he with h|h<;>grind
   rcases dk with⟨a,b⟩|⟨a,b⟩|bf|b3
   . exact aq true a b
   . exact aq false a b
   . exact ho 1 bf
   . exact ho 0 b3
 . push Not at ar;have⟨ua,wa,d8,cc,cp⟩:=ar
   obtain⟨g,_,rfl⟩:=Tn (show l≠[] from fun h=>by obtain⟨_,bv,_⟩:=cA ua wa d8 cc cp;rw[h] at bv;cases bv)
   obtain⟨_,_,_,d,b9⟩:=gA g c0
   obtain⟨w2,a4,cd⟩:∃w2∈k.BW,w2≠g.c:=by
    have⟨z1,d4,z2,dl,ne⟩:=one_lt_card.mp (by omega:1 < k.BW.card)
    exact if h1:z1=g.c then ⟨z2,dl,fun e=>ne (h1.trans e.symm)⟩ else ⟨z1,d4,h1⟩
   have h01e:E 0=∅\/ E 1=∅:=by by_contra! ne;exact k.TD d b9 (k.PQ a4) cd Pv (k.MD (fun _ _ _=>⟨trivial,trivial⟩) ne.1 ne.2)
   have ho:=bq (g::_) sA (fun x t=>⟨(gA x t).1,(gA x t).2.1⟩) cA;exact h01e.elim (ho 1) (ho 0)
set_option maxHeartbeats 1200000 in
lemma Jg (h1:k.BW.card <=1)(b4:k.Ib=∅):k.Pz:=by
 classical
 have aw:∀x∈k.B0,x∉k.B1:=fun x h0 h1=>nE (b4▸k.hB01▸mI h0 h1)
 have a9:∀u w,s(u,w)∈k.Ub -> ((u∈k.B0 /\w∈k.B1)\/ (u∈k.B1 /\w∈k.B0)) /\((u∈k.Wb /\TC C k.b u)\/ (w∈k.Wb /\TC C k.b w)):=
  fun u w he=>⟨k.RG he (by rw[b4];exact RM _) (by rw[b4];exact RM _),(k.M6 he).2.2.2⟩
 have hA:=k.PN
 by_cases cm:k.B1.card <=1
 . rcases Ms k.B1 with b6|⟨q,a8⟩
   . have bp:k.Ub=∅:=RF fun u w he=>(a9 u w he).1.elim (fun h=>nE (b6▸h.2)) fun h=>nE (b6▸h.1)
     have cf:k.Eb=∅:=RF fun u w he=>by
      rcases(k.Hq he).2.2.2 with⟨_,_,h⟩|⟨_,_,h⟩<;>[change w∈k.B1 at h;change u∈k.B1 at h]<;>exact nE (b6▸h)
     have c3:∀e∈k.U,e∈k.Ua:=fun e he=>by by_contra aa;exact nE (cf▸k.M5 he (by rw[bp];exact RM _) aa)
     rcases hA with⟨l,sA,gA,cA⟩|⟨cd,ck,h0,af,hW⟩
     . exact Yw k.L k.s k.c k.w k.Pv k.Pu (fun _=>sE) (fun w hw=>(k.HQ w hw).elim id fun h=>nE (b6▸i1 h))
        l [] (by rw[PX,PX,H0];omega) (fun g hg=>(gA g hg).1) (by simp) (by simp) (by simp) (by simp) (k.cv fun u w he hu hw=>hL (cA u w (c3 _ he) hu hw))
     . have⟨gs,gS,gG,gC⟩:=k.Mq h0 af hW
       exact k.T9 gs [] (by simp[gS]) (fun g hg=>(gG g hg).1) (HW fun u w he=>hL (gC u w he (.inr (.inr (c3 _ he))))) (by simp) b0
   . have a7:∀x∈k.B1,x=q:=fun x hx=>uq cm hx a8;have hqv:q≠k.v:=fun e=>k.B (e▸a8)
     by_cases aq:q∈k.Wb
     . exact k.Jd (mI a8 aq) (fun w hw=>a7 w (i1 hw))
        (RF fun u w he=>by have hs:=k.Hq he;exact hs.2.2.2.elim (fun a=>hs.2.2.1 (a7 w a.2.2▸k.PQ (mI a8 aq))) fun a=>hs.2.1 (a7 u a.2.2▸k.PQ (mI a8 aq)))
        (fun u w he=>by rcases(a9 u w he).1 with⟨ap,ah⟩|⟨aj,hw0⟩;obtain rfl:=a7 w ah;exact⟨u,mI (sL (sw▸uS he)) (by rw[H4];exact ap),sw⟩;obtain rfl:=a7 u aj;exact⟨w,mI (sL (uS he)) (by rw[H4];exact hw0),rfl⟩)
     . have c7:∀w∈Q4 q (k.Ub∪k.Eb),TC C k.b w:=fun w hw=>(mU (sE hw)).elim
        (fun h=>((a9 q w h).2.resolve_left fun a=>aq a.1).2) fun h=>((k.Hq h).2.2.2.resolve_left fun a=>aq a.1).2.1
       have bm:∀w∈k.Lv,TC C k.a w:=fun w hw=>(k.HQ w hw).elim id fun h=>(aq (a7 w (i1 h)▸i2 h)).elim
       obtain⟨itq,Lmq,Mb,hMb,hqc,hqW',_,_,hLmc,⟨fwb,hfb1,hfb2⟩,hqC⟩:=
        Ra k.o (L:=Q4 q (k.Ub∪k.Eb)) (W:=(W0For G11 C k.b)) fs (Qg k.o k.b) (fun _ hw=>k.Ts (sE hw)) c7 False False.elim
       have bn:∀u w,s(u,w)∈k.Ub∪k.Eb -> s(u,w)∉PY q Lmq -> Px itq s(u,w):=fun u w bk an=>by
        have hor:u=q\/ w=q:=(mU bk).elim (fun h=>(a9 u w h).1.elim (fun a=>.inr (a7 _ a.2)) fun a=>.inl (a7 _ a.1))
         fun h=>(k.Hq h).2.2.2.elim (fun a=>.inr (a7 _ a.2.2)) fun a=>.inl (a7 _ a.2.2)
        exact hor.elim (fun e=>e▸hqC ⟨w,sL (e▸bk),rfl⟩ (e▸an)) fun e=>e▸hqC ⟨u,sL (sw▸e▸bk),sw⟩ (e▸an)
       have:=k.RW
       rcases hA with⟨l,sA,gA,cA⟩|⟨cd,ck,h0,af,hW⟩
       . obtain⟨itv,Lmv,Ma,ae,_,hvW,_,hvgd,hLmvc,⟨fwa,hfa1,hfa2⟩,hvC⟩:=k.Td sr bm
         have:=TF k.U k.v q Lmv Lmq
         have ak:=Qw (E:=k.U\(PY k.v Lmv∪PY q Lmq)) k.o q (itq::itv::l)
          (k.TV (fun _ _ hv an=>Hy (HT (hvC hv fun h=>an (uL h)))) fun u w he an hu hw=>by
           by_cases j:s(u,w)∈k.Ua;. exact Hy (Hy (cA u w j hu hw))
           exact HT (bn u w (k.Me he j) fun h=>an (uR h)))
          (fun it Px ne=>(mC Px).elim (fun e=>(ne (e▸hqc)).elim) fun h1=>(mC h1).elim (fun e=>e▸hvgd.symm▸trivial) fun h2=>(gA it h2).1)
         have:=KS k.o k.ha k.hb k.Pt hqv.symm k.PU (f1 ae) (f2 ae) (f1 hMb) (f2 hMb) (fun _=>sE) (fun _ hw=>k.Ts (sE hw)) hfa1 hfa2 hfb1 hfb2
         have:=k.TR;rw[PX,PG,PG,hqW',hvW] at ak;omega
       . have⟨gs,gS,gG,gC⟩:=k.Mq h0 af hW;have:=Tq k.U q Lmq
         have ak:=Qw (E:=k.U\PY q Lmq) k.o q (itq::gs)
          (k.MQ ds gC Hy fun u w he _ _ aa=>HT (bn u w (k.Me (d1 he) aa) (d2 he)))
          (fun it Px ne=>(mC Px).elim (fun e=>(ne (e▸hqc)).elim) fun h1=>(gG it h1).1)
         have:Mb.card <=(mixing G11 C).card:=R3 (f1 hMb);rw[PX,PG,hqW',gS] at ak;omega
 have c5:2 <=k.B1.card:=by omega
 have h01:k.H8.card <=1:=Qa Q3 c5 fun x hx y hy=>k.M8 (i1 hx) (i2 hx) hy;let P:F -> F -> Prop:=fun u _=>u∉k.B0;set E:=k.Hk P;have⟨bs,bS,hok,bC,bW⟩:=k.TT P;have b2:PD bs <=2:=by rw[bS];split_ifs<;>omega
 have bC':∀b∈bs,b.c∉k.Wa /\b.c≠k.v /\b.c∉k.H8:=fun b hb=>by obtain⟨cj,cr,_,_,hx⟩:=bW b hb;exact⟨cj,cr,fun h=>(k.Mm hx).2.2.2.2.elim (fun a=>a.2.2 (i1 h)) fun a=>aw _ (i1 h) (i2 a.2.1)⟩
 have bd:∀u w,s(u,w)∈k.Eb -> (u∈k.H8 /\w∈k.B1)\/ (w∈k.H8 /\u∈k.B1)\/ s(u,w)∈E 0∪E 1:=fun u w he=>by
  obtain⟨p,q,ag,bb,a8,_,_,_,_,h01⟩:=k.Es he
  by_cases b8:p∈k.B0
  . exact(MR.mp ag).elim (fun ⟨e1,e2⟩=>e1▸e2▸.inl ⟨mI b8 bb,a8⟩) fun ⟨e1,e2⟩=>e1▸e2▸.inr (.inl ⟨mI b8 bb,a8⟩)
  . exact h01.elim (fun a=>.inr (.inr (uL (k.HY.mpr ⟨he,p,q,ag,mI a.1 bb,mI a.2 a8,b8⟩)))) fun a=>.inr (.inr (uR (k.HY.mpr ⟨he,p,q,ag,mI a.1 bb,mI a.2 a8,b8⟩)))
 let ib:=k.J7 h01 h1 fun x hx=>aw x (i1 hx)
 have ba:∀u w,s(u,w)∈k.U -> s(u,w)∉k.Ua -> PC (ib.l++bs) s(u,w):=fun u w he aa=>by
  by_cases am:s(u,w)∈k.Ub;. exact hL (ib.ub he (a9 u w am).1 (a9 u w am).2)
  rcases bd u w (k.M5 he am aa) with⟨hu,ah⟩|⟨hw,aj⟩|h01
  . exact hL (ib.c0 he hu ah)
  . exact hL (by simpa[sw] using ib.c0 (sw▸he) hw aj)
  . exact hR (bC _ h01)
 have hZ (z:k.H8=∅) (h:¬∀u w,s(u,w)∈k.Ub -> u=k.v\/ w=k.v):∃ab∈k.BW,∃z0∈k.B0,z0≠k.v /\Ga ab z0:=by
  push Not at h;have⟨u,w,bl,cg,cc⟩:=h;have hadj:=gA (uS bl)
  rcases(a9 u w bl).1 with⟨ap,ah⟩|⟨aj,hw0⟩<;>rcases(a9 u w bl).2 with⟨ax,_⟩|⟨ay,_⟩
  . exact k.n0 z ap ax
  . exact⟨w,mI ah ay,u,ap,cg,hadj.symm⟩
  . exact⟨u,mI aj ax,w,hw0,cc,hadj⟩
  . exact k.n0 z hw0 ay
 rcases hA with⟨l,sA,gA,cA⟩|⟨ca,ch,h0,af,hW⟩
 . by_cases bz:PD l+PD bs <=2
   . exact k.Ta h1 (P:=PC (l++ib.l++bs)) (fun u w he hu hw=>by by_cases j:s(u,w)∈k.Ua;exact hL (hL (cA u w j hu hw));exact Ty (ba u w he j))
      (fun E Lv cn bm cs=>by
       have⟨Ma,ae,ak,hF⟩:=k.J3 ib E Lv l bs cn bm (fun g hg=>⟨(gA g hg).1,(gA g hg).2.1⟩) bC' hok
        (fun e he=>by rcases cs e he with h|⟨q,hq,Pv,rfl,cb⟩|h;exact .inl h;exact .inr (hL (hR (by simpa[sw] using ib.c1 (sw▸cb) hq Pv)));exact .inr h)
       exact⟨Ma,ae,by omega,hF⟩)
   . have hne01:(E 0).Nonempty /\(E 1).Nonempty:=RE (by dsimp only[E];omega)
     obtain⟨g,t,rfl⟩:=Tn (show l≠[] from fun h=>by rw[h] at bz;simp at bz;omega)
     have ht:t=[]:=by
      have:=(gA g c0).2.2.1;simp only[PG] at sA
      cases t with|nil=>rfl|cons x _=>have:=(gA x (c1 c0)).2.2.1;simp only[PG] at sA;omega
     subst ht;obtain⟨_,_,_,d,a5⟩:=gA g c0;let g':=k.Hc d g.c (d1 (i1 a5)) (i2 a5) k.U sr
     by_cases b5:k.Wa⊆{g.c}
     . exact k.TN ib [g'] bs (by simp[g'];omega) (fun x hx=>mL hx▸⟨trivial,i2 a5⟩) (fun b hb=>⟨(bC' b hb).1,(bC' b hb).2.2⟩) hok
        (HW fun u w he=>by
         by_cases hu:u=k.v;. subst u;obtain rfl:=mS (b5 ((k.HQ w (sL he)).elim k.tW fun h=>k.PQ h));exact⟨g',aL (aL c0),k.v,mI (sL (sw▸he)) (k.hv (1-d)),sw⟩
         by_cases hw:w=k.v;. subst w;obtain rfl:=mS (b5 ((k.HQ u (sL (sw▸he))).elim k.tW fun h=>k.PQ h));exact⟨g',aL (aL c0),k.v,mI (sL he) (k.hv (1-d)),rfl⟩
         by_cases j:s(u,w)∈k.Ua
         . have⟨cp,hW⟩:=k.RJ j;rcases k.ps cp hu hw d with⟨ha,hb⟩|⟨ha,hb⟩<;>rcases hW with h1|h1<;>obtain rfl:=mS (b5 h1)
           . exact⟨g',aL (aL c0),w,mI (sL he) hb,rfl⟩
           . exact(d2 (i1 a5) hb).elim
           . exact(d2 (i1 a5) ha).elim
           . exact⟨g',aL (aL c0),u,mI (sL (sw▸he)) ha,sw⟩
         . exact Ty (ba u w he j))
     . have⟨w2,bx,bh⟩:=Nss b5
       by_cases Pv:k.v∈k.B0;. exact(k.TD d a5 bx (nS bh) Pv (k.MD (fun _ _ _=>⟨trivial,trivial⟩) hne01.1 hne01.2)).elim
       rcases Ms k.H8 with z|⟨cl,b3⟩
       swap;. exact(k.TZ d a5 bx (nS bh) b3 (k.MD (fun _ _ h=>⟨h,trivial⟩) hne01.1 hne01.2)).elim
       rcases Ms k.BW with bg|⟨ab,a4⟩
       . have bp:k.Ub=∅:=RF fun u w he=>by
          rcases(a9 u w he).1 with⟨ap,ah⟩|⟨aj,hw0⟩<;>rcases(a9 u w he).2 with⟨ax,_⟩|⟨ay,_⟩<;>
           first|exact k.n0 z ap ax|exact k.n1 bg ah ay|exact k.n1 bg aj ax|exact k.n0 z hw0 ay
         exact Yw k.L k.s k.c k.w k.Pv k.Pu (fun _=>sE) (fun w hw=>(k.HQ w hw).elim id fun h=>nE (bg▸h)) [g] bs
          (by rw[PX,PX];omega) (fun x hx=>(gA x hx).1) (fun x hx b hb e=>(bC' b hb).1 (e▸(gA x hx).2.1)) (fun b hb=>(bC' b hb).2.1) hok.1 hok.2
          (k.cv fun u w he hu hw=>by
           by_cases j:s(u,w)∈k.Ua;. exact hL (cA u w j hu hw)
           rcases bd u w (k.M5 he (by rw[bp];exact RM _) j) with⟨h0,_⟩|⟨h0,_⟩|h01;exact nE (z▸h0);exact nE (z▸h0);exact hR (bC _ h01))
       . have c4:∀w∈k.Lv\{ab},TC C k.a w:=fun w hw=>(k.HQ w (d1 hw)).elim id fun h=>(nS (d2 hw) (uq h1 h a4)).elim
         by_cases hgc1:g.c=ab
         . have⟨Ma,ae,ak,hF⟩:=k.J3 ib k.U (k.Lv\{ab}) [g'] bs ds c4 (fun x hx=>mL hx▸⟨trivial,i2 a5⟩) bC' hok
            (k.J9 (fun he=>⟨g',aL (aL c0),k.v,mI (sL (sw▸hgc1.symm▸he)) (k.hv (1-d)),show s(k.v,ab)=s(g.c,k.v) by rw[hgc1,sw]⟩)
             (fun u w he hu hw=>by
              by_cases j:s(u,w)∈k.Ua
              . obtain⟨_,c9,y,hy,ag⟩:=cA u w j hu hw;rw[mL c9] at ag hy
                have ce:y∈k.A (1-d):=(k.ps (k.RJ (ag▸j)).1 (k.Ja k.MG (i2 a5)).symm (by rcases MR.mp ag with⟨_,rfl⟩|⟨rfl,_⟩<;>assumption) d).elim (fun a=>a.2) fun a=>(d2 (i1 a5) a.1).elim
                exact⟨g',aL (aL c0),y,mI (sL (g.he y hy)) ce,ag⟩
              . exact Ty (ba u w he j)))
           have:=k.TM sr Pv a4 ae hF;simp only[PG,H0,g',Q9,Q0,Cs] at ak;omega
         . by_cases av:∀u w,s(u,w)∈k.Ub -> u=k.v\/ w=k.v
           . have:=Tw k.U s(k.v,ab)
             obtain⟨Ma,ae,ak,hF⟩:=k.TP ds c4 [g] bs (fun x hx=>(gA x hx).1)
              (fun x hx b hb e=>(bC' b hb).1 (e▸(gA x hx).2.1)) (fun b hb=>(bC' b hb).2.1) hok
              (k.TU fun u w he hu hw=>by
               by_cases am:s(u,w)∈k.Ub;. rcases av u w am with h|h<;>grind
               by_cases j:s(u,w)∈k.Ua;. exact hL (cA u w j hu hw)
               rcases bd u w (k.M5 he am j) with⟨h0,_⟩|⟨h0,_⟩|h01;exact nE (z▸h0);exact nE (z▸h0);exact hR (bC _ h01))
             have:=k.TM sr Pv a4 ae hF;omega
           . have⟨cu,bu,z0,b7,ar,b9⟩:=hZ z av;obtain rfl:=uq h1 bu a4
             exact(k.Rm aw d a5 a4 (Ne.symm hgc1) z b7 ar b9 (k.MD (fun _ _ _=>⟨trivial,trivial⟩) hne01.1 hne01.2)).elim
 . have⟨gs,gS,gG,gC⟩:=k.Mq h0 af hW;have hc01:ca≠ch:=k.T3 (i1 h0) (i1 af)
   by_cases cz:PD bs <=1
   . exact k.TN ib gs bs (by omega) gG (fun b hb=>⟨(bC' b hb).1,(bC' b hb).2.2⟩) hok (k.MQ sr gC (fun h=>hL (hL h)) fun u w he _ _ aa=>Ty (ba u w he aa))
   . have hne01:(E 0).Nonempty /\(E 1).Nonempty:=RE (by dsimp only[E];omega)
     rcases Ms k.H8 with z|⟨cl,b3⟩
     . by_cases av:∀u w,s(u,w)∈k.Ub -> u=k.v\/ w=k.v
       . exact k.T9 gs bs (by omega) (fun g hg=>(gG g hg).1) (k.MQ sr gC hL fun u w he hu hw aa=>by
          rcases bd u w (k.M5 he (fun hb=>by rcases av u w hb with h|h<;>grind) aa) with⟨h0,_⟩|⟨h0,_⟩|h01;exact nE (z▸h0);exact nE (z▸h0);exact hR (bC _ h01))
          (fun g hg b hb e=>(bC' b hb).1 (e▸(gG g hg).2)) hok
       . have⟨ab,a4,z0,b7,ar,b9⟩:=hZ z av;have h01':=k.MD (fun _ _ _=>⟨trivial,trivial⟩) hne01.1 hne01.2
         rcases hW ab (k.PQ a4) with rfl|rfl
         . exact(k.Rm aw 1 af a4 hc01 z b7 ar b9 h01').elim
         . exact(k.Rm aw 0 h0 a4 hc01.symm z b7 ar b9 h01').elim
     . exact(k.TZ 0 h0 (i2 af) hc01.symm b3 (k.MD (fun _ _ h=>⟨h,trivial⟩) hne01.1 hne01.2)).elim
set_option maxHeartbeats 1600000 in
lemma Js (h1:k.BW.card <=1){vb:F}(c8:k.Ib={vb}):k.Pz:=by
 classical
 have a8:vb∈k.Ib:=c8▸ms;have an:=i1 a8;have ap:=i2 a8;have fj:vb∈k.B0:=i1 (k.hB01.symm▸a8);have bj:vb∈k.B1:=i2 (k.hB01.symm▸a8);have hnv:vb≠k.v:=fun e=>k.B (e▸bj);have b9:=(Q1 k.o k.hb an ap).1;have a5:=(Q1 k.o k.hb an ap).2;have bu:∀x∈k.B0,x∈k.B1 -> x=vb:=fun x h0 h1=>mS (c8▸k.hB01▸mI h0 h1);set Lb:=Q4 vb (k.Ub∪k.Eb);have a7:∀w∈Lb,s(vb,w)∈k.U:=fun _ hw=>k.Ts (sE hw)
 have ah:∀w∈Lb,TC C k.b w:=fun w hw=>(mU (sE hw)).elim
  (fun h=>((k.M6 h).2.2.2.resolve_left fun a=>b9 a.1).2) fun h=>((k.Hq h).2.2.2.resolve_left fun a=>b9 a.1).2.1
 have dj:∀u w,s(u,w)∈k.Ub -> u≠vb -> w≠vb -> (u∈k.B0 /\w∈k.B1)\/ (u∈k.B1 /\w∈k.B0):=
  fun u w he hu hw=>k.RG he (fun h=>hu (mS (c8▸h))) (fun h=>hw (mS (c8▸h)))
 have hA:=k.PN
 by_cases fc:k.B1.card <=1
 . have ay:∀x∈k.B1,x=vb:=fun x hx=>uq fc hx bj
   have ak:∀w∈k.Lv,TC C k.a w:=fun w hw=>(k.HQ w hw).elim id fun h=>(b9 (ay w (i1 h)▸i2 h)).elim
   have d3:∀u w,s(u,w)∈k.Ub∪k.Eb -> PP vb Lb s(u,w):=fun u w he=>by
    have ep:u=vb\/ w=vb:=(mU he).elim (fun h=>by obtain⟨_,dr,rfl|rfl⟩:=(k.M6 h).2.2.1;exact .inl (ay _ dr);exact .inr (ay _ dr))
     fun h=>(k.Hq h).2.2.2.elim (fun a=>.inr (ay _ a.2.2)) fun a=>.inl (ay _ a.2.2)
    rcases ep with rfl|rfl;exact⟨w,sL he,rfl⟩;exact⟨u,sL (sw▸he),sw⟩
   rcases hA with⟨l,sA,gA,cA⟩|⟨dn,dt,h0,av,hW⟩
   . exact XQ k.L k.s k.c hnv.symm k.Pv k.Pu an ap (fun _=>sE) ak a7 ah l [] (by rw[PX,PX,H0];omega)
      (fun g hg=>(gA g hg).1) (by simp) (by simp) (by simp) (by simp) (by simp)
      (k.cv fun u w he hu hw=>by by_cases ab:s(u,w)∈k.Ua;exact .inr (hL (cA u w ab hu hw));exact .inl (d3 u w (k.Me he ab)))
   . have⟨gs,gS,gG,gC⟩:=k.Mq h0 av hW
     exact KW k.L k.s k.r k.e an ap a7 ah gs [] (by rw[PX,PX,H0,gS];omega) (fun g hg=>(gG g hg).1)
      (by simp) (by simp) (by simp) (by simp) (k.MQ sr gC (fun h=>.inr (hL h)) fun u w he _ _ ae=>.inl (d3 u w (k.Me he ae)))
 have e0:2 <=k.B1.card:=by omega
 have h01:k.H8.card <=1:=Qa Q3 e0 fun x hx y hy=>k.M8 (i1 hx) (i2 hx) hy;let P:F -> F -> Prop:=fun u w=>u∉k.B0 /\w≠vb;set E:=k.Hk P;let ib:=k.J7 h01 h1 fun x hx h1=>b9 (bu x (i1 hx) h1▸i2 hx)
 have dz:∀u w,s(u,w)∈k.Eb -> u=vb\/ w=vb\/ (u∈k.H8 /\w∈k.B1)\/ (w∈k.H8 /\u∈k.B1)\/ s(u,w)∈E 0∪E 1:=fun u w he=>by
  by_cases ar:u=vb;. exact .inl ar
  by_cases a9:w=vb;. exact .inr (.inl a9)
  obtain⟨p,q,ad,cb,c7,_,_,_,_,h01⟩:=k.Es he;have dq:q≠vb:=by rcases MR.mp ad with⟨_,rfl⟩|⟨rfl,_⟩<;>assumption
  by_cases ca:p∈k.B0
  . exact(MR.mp ad).elim (fun ⟨e1,e2⟩=>e1▸e2▸.inr (.inr (.inl ⟨mI ca cb,c7⟩))) fun ⟨e1,e2⟩=>e1▸e2▸.inr (.inr (.inr (.inl ⟨mI ca cb,c7⟩)))
  . exact h01.elim (fun a=>.inr (.inr (.inr (.inr (uL (k.HY.mpr ⟨he,p,q,ad,mI a.1 cb,mI a.2 c7,ca,dq⟩))))))
     fun a=>.inr (.inr (.inr (.inr (uR (k.HY.mpr ⟨he,p,q,ad,mI a.1 cb,mI a.2 c7,ca,dq⟩)))))
 have dd:∀u w,s(u,w)∈k.U -> s(u,w)∉k.Ua -> PP vb Lb s(u,w)\/ PC ib.l s(u,w)\/ s(u,w)∈E 0∪E 1:=fun u w he ae=>by
  have hU:=k.Me he ae
  by_cases hu:u=vb;. subst u;exact .inl ⟨w,sL hU,rfl⟩
  by_cases hw:w=vb;. subst w;exact .inl ⟨u,sL (sw▸hU),sw⟩
  by_cases au:s(u,w)∈k.Ub;. exact .inr (.inl (ib.ub he (dj u w au hu hw) (k.M6 au).2.2.2))
  rcases dz u w (k.M5 he au ae) with rfl|rfl|⟨h0,h1⟩|⟨h0,h1⟩|h01
  . exact(hu rfl).elim
  . exact(hw rfl).elim
  . exact .inr (.inl (ib.c0 he h0 h1))
  . exact .inr (.inl (by simpa[sw] using ib.c0 (sw▸he) h0 h1))
  . exact .inr (.inr h01)
 rcases Ms k.H8 with ac|⟨du,bd⟩
 . have cc:∀g∈ib.l,g.good /\g.c∈k.Wa:=fun g hg=>(ib.hG g hg).2.elim (fun h0=>nE (ac▸h0)) fun h1=>⟨(ib.hG g hg).1,k.PQ h1⟩
   have fw:PD ib.l <=1:=by
    have h0:ib.bon=0:=ib.hB01.elim id fun h=>by obtain⟨g1,ey,g2,ex,ne,_,_,_⟩:=ib.hBon h;exact(ne (uq h1 ((ib.hG g1 ey).2.resolve_left (by rw[ac];exact RM _)) ((ib.hG g2 ex).2.resolve_left (by rw[ac];exact RM _)))).elim
    have:=ib.hS;omega
   by_cases ho:E 0=∅\/ E 1=∅
   . let GP (S:Finset S2):=∃j:SS C,j.W.card=1 /\j.c∉k.Wa /\j.c≠k.v /\j.c≠vb /\vb∉j.L /\Ga j.c vb /\vb∈j.W.biUnion (oi C) /\∀e∈S,Px j e
     have f6:(E 0∪E 1=∅)\/ GP (E 0∪E 1):=by
      rcases Ms (E 0∪E 1) with bz|Pt;. exact .inl bz
      right
      have d4 (d:F2) (hEd:(E d).Nonempty):GP (E d):=by
       have c9:∀u w,s(u,w)∈E d -> ∃u' w':F,s(u,w)=s(u',w') /\u'∈k.dA d /\w'∈k.dB d /\w'≠vb:=fun u w he=>by obtain⟨hE,u',w',ad,az,b5,_,a9⟩:=k.HY.mp he;have hs:=k.Hq (ad▸hE);exact⟨u',w',ad,mD az hs.2.1,mD b5 hs.2.2.1,a9⟩
       have em:(k.dA d).card <=1:=R9 (fun u0 w0 he=>by
        obtain⟨_,w',_,_,b5,a9⟩:=c9 u0 w0 he
        exact(R3 fun z hz=>Fm ⟨Uv _,a5 z (i2 (d1 hz)),(k.HX d (d1 (i1 (d1 hz))) (i2 (d1 hz)) (d1 (i1 (d1 b5))) (i2 (d1 b5))).symm⟩).trans (Q3 vb w' (Ne.symm a9))) hEd
       have⟨cx,cz⟩:=H1 em;have am:cx∈k.dA d:=R9 (fun u0 w0 he=>by obtain⟨u',_,_,az,_⟩:=c9 u0 w0 he;exact cz u' az▸az) hEd
       refine⟨mW C cx (Q4 cx (E d)\{vb}) (k.ob (1-k.db)) (Qe k.o k.hb (1-k.db))
        (fun x hx=>by obtain⟨_,_,ad,_,b5,_⟩:=c9 cx x (sE (d1 hx));rcases MR.mp ad with⟨_,rfl⟩|⟨rfl,_⟩;exact i2 (d1 b5);exact(d2 am (k.PQ (mI (i2 (d1 b5)) (i2 (d1 am))))).elim)
        (fun _ hx=>eS (k.HG (sE (d1 hx)))) False False.elim,
        cS _,d2 am,fun e=>k.W (e▸i2 (d1 am)),fun e=>b9 (e▸i2 (d1 am)),by simp,(a5 cx (i2 (d1 am))).symm,
        Mbu ⟨k.ob (1-k.db),ms,bj⟩,HW fun u w he=>by
         obtain⟨_,_,ad,az,_,a9⟩:=c9 u w he;rcases MR.mp ad with⟨rfl,rfl⟩|⟨rfl,rfl⟩
         . obtain rfl:=cz u az;exact⟨w,mD (sL he) (R1 a9),rfl⟩
         . obtain rfl:=cz w az;exact⟨u,mD (sL (sw▸he)) (R1 a9),sw⟩⟩
      rcases ho with h0|h1;. rw[h0,empty_union] at Pt ⊢;exact d4 1 Pt
      . rw[h1,union_empty] at Pt ⊢;exact d4 0 Pt
     have dv (E':Finset S2) (gs:List (SS C)) (hG:∀g∈gs,g.good /\(g.c=k.v\/ g.c=vb\/ g.c∈k.Wa))
       (hC:∀e∈E',PC gs e\/ e∈E 0∪E 1):E'.card <=(rFull G11 C).card+PD gs:=by
      rcases f6 with bz|⟨j,fx,eg,e6,dm,el,eh,ee,et⟩
      . have al:=QS (E:=E') k.o gs [] (fun g hg=>(hG g hg).1) (fun e he=>(hC e he).elim hL fun h01=>nE (bz▸h01)) (by simp) (by simp) (by simp)
        rw[PX,PX,H0] at al;omega
      . have al:=Z9 (E:=E') k.o gs j vb (fun g hg=>(hG g hg).1)
         (fun g hg e=>by rcases(hG g hg).2 with h|h|h;exact e6 (e.symm.trans h);exact dm (e.symm.trans h);exact eg (e▸h))
         (fun e he=>(hC e he).elim Hy fun h01=>HT (et e h01)) el eh ee
        rw[PX] at al;omega
     rcases hA with⟨l,sA,gA,cA⟩|⟨dn,dt,h0,av,hW⟩
     . exact k.T0 h1 a8 a7 (P:=fun e=>PP vb Lb e\/ PC (ib.l++l) e\/ e∈E 0∪E 1)
        (fun u w he hu hw=>by
         by_cases ab:s(u,w)∈k.Ua;. exact .inr (.inl (hR (cA u w ab hu hw)))
         rcases dd u w he ab with h|h|h;exact .inl h;exact .inr (.inl (hL h));exact .inr (.inr h))
        (fun E' Lv de ak dh=>by
         obtain⟨f9,Lma,Ma,bk,f4,es,_,vg,fu,bl,f3⟩:=k.Td de ak;obtain⟨bt,Lmb,Mb,ax,d7,d6,_,bg,en,bp,cr⟩:=k.TS a8 a7 ah
         have:=TF E' k.v vb Lma Lmb
         have al:=dv (E'\(PY k.v Lma∪PY vb Lmb)) (f9::bt::(ib.l++l))
          (fun g hg=>(mC hg).elim (fun e=>⟨e▸vg.symm▸trivial,.inl (e▸f4)⟩) fun h1=>
           (mC h1).elim (fun e=>⟨e▸bg.symm▸trivial,.inr (.inl (e▸d7))⟩) fun h2=>
           (mA h2).elim (fun h3=>⟨(cc g h3).1,.inr (.inr (cc g h3).2)⟩) fun h3=>⟨(gA g h3).1,.inr (.inr (gA g h3).2.1)⟩)
          (fun e f5=>by
           have⟨he,dp⟩:=Dp f5
           rcases dh e he with eu|⟨q,hq,Pv,rfl,cn⟩|ct|h|h01
           . exact .inl (HT (f3 eu fun h=>dp (uL h)))
           . exact .inl (Hy (Hy (hL (by simpa[sw] using ib.c1 (sw▸cn) hq Pv))))
           . exact .inl (Hy (HT (cr ct fun h=>dp (uR h))))
           . exact .inl (Hy (Hy h))
           . exact .inr h01)
         simp only[PG,PT,es,d6] at al;exact⟨Ma,bk,Mb,ax,by omega,bl,bp⟩)
     . have⟨gs,gS,gG,gC⟩:=k.Mq h0 av hW
       obtain⟨bt,Lmb,Mb,ax,d7,d6,_,bg,en,_,cr⟩:=k.TS a8 a7 ah
       have:=Tq k.U vb Lmb;have:=k.Jb ax;have:=k.RW
       have al:=dv (k.U\PY vb Lmb) (bt::(ib.l++gs))
        (fun g hg=>(mC hg).elim (fun e=>⟨e▸bg.symm▸trivial,.inr (.inl (e▸d7))⟩) fun h1=>
         (mA h1).elim (fun h2=>⟨(cc g h2).1,.inr (.inr (cc g h2).2)⟩) fun h2=>⟨(gG g h2).1,.inr (.inr (gG g h2).2)⟩)
        (k.MQ ds gC (fun h=>.inl (Hy (hR h))) fun u w he _ _ ae=>by
         rcases dd u w (d1 he) ae with ct|h|h01;exact .inl (HT (cr ct (d2 he)));exact .inl (Hy (hL h));exact .inr h01)
       simp only[PG,PT,d6,gS] at al;omega
   . push Not at ho;have h01:=k.MD (fun _ _ h=>h) ho.1 ho.2
     have cu (w0:F) (hw0W:w0∈k.Wa) (hw0v:Ga w0 vb) (d:F2) (c0:F) (hc:c0∈k.Ad d∩k.Wa):False:=by
      obtain⟨x,y,z,u,xy,zu,_,_,_,_,_,_,_,_,xA,xW,_,yA,yB,_,zA,zW,_,uA,uB,_⟩:=k.MJ d h01;have d8:=k.PQ;have cW:=i2 hc;have cd:=d1 (i1 hc);have fl:=k.MG
      have e4:c0≠vb:=fun eq=>by subst eq;refine Vv (k.PU c0 cW).symm hw0v.symm (a5 x xW) (a5 z zW) (k.Hg cd cW (d1 yA)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_<;>(simp only[mem_inter,mem_sdiff] at*;grind)
      refine ZF (k.PU w0 hw0W) hw0v hnv (k.PU c0 cW) e4 (a5 x xW) ?_ ?_ ?_ (a5 z zW) (k.Hg cd cW (d1 zA)) ?_ ?_ ?_ ?_
       (k.H7 d xA zA hw0W) xy (k.Hg cd cW (d1 yA)) ?_ ?_ ?_ ?_ zu ?_ ?_ ?_ ?_ ?_ ?_ (k.H7 d uA yA hw0W)<;>(simp only[mem_inter,mem_sdiff] at*;grind)
     have⟨bs,bS,hok,bC,bW⟩:=k.TT P;have b2:PD bs <=2:=by rw[bS];split_ifs<;>omega
     have bC':∀b∈bs,b.c∉k.Wa /\b.c≠k.v /\b.c≠vb:=fun b hb=>by obtain⟨fg,ea,_,_,hx⟩:=bW b hb;exact⟨fg,ea,fun eq=>(k.Mm hx).2.2.2.2.elim (fun a=>b9 (eq▸i2 a.1)) fun a=>a.2.2.2 eq⟩
     have dw (l:List (SS C)) (hC:∀u w,s(u,w)∈k.Ua -> u≠k.v -> w≠k.v -> PC l s(u,w)) (b4:∀u w,s(u,w)∈k.Ub -> u=vb\/ w=vb):
       ∀u w,s(u,w)∈k.U -> u≠k.v -> w≠k.v -> PP vb Lb s(u,w)\/ PC (l++bs) s(u,w):=fun u w he hu hw=>by
      by_cases au:s(u,w)∈k.Ub;. rcases b4 u w au with rfl|rfl;exact .inl ⟨w,sL (uL au),rfl⟩;exact .inl ⟨u,sL (uL (sw▸au)),sw⟩
      by_cases ab:s(u,w)∈k.Ua;. exact .inr (hL (hC u w ab hu hw))
      have cy:=k.M5 he au ab
      rcases dz u w cy with rfl|rfl|⟨h0,_⟩|⟨h0,_⟩|h01;exact .inl ⟨w,sL (uR cy),rfl⟩;exact .inl ⟨u,sL (uR (sw▸cy)),sw⟩;exact nE (ac▸h0);exact nE (ac▸h0);exact .inr (hR (bC _ h01))
     rcases Ms k.BW with ck|⟨af,aa⟩
     . have b4:∀u w,s(u,w)∈k.Ub -> u=vb\/ w=vb:=fun u w he=>by
        by_contra! ne
        rcases dj u w he ne.1 ne.2 with⟨aj,cm⟩|⟨c6,hw0⟩<;>rcases(k.M6 he).2.2.2 with⟨bb,_⟩|⟨ag,_⟩<;>
         first|exact k.n0 ac aj bb|exact k.n1 ck cm ag|exact k.n1 ck c6 bb|exact k.n0 ac hw0 ag
       have ak:∀w∈k.Lv,TC C k.a w:=fun w hw=>(k.HQ w hw).elim id fun h=>nE (ck▸h)
       rcases hA with⟨l,sA,gA,cA⟩|⟨cl,ez,h0,av,_⟩
       . have dx:=k.cv (P:=fun e=>PP vb Lb e\/ PC (l++bs) e) (dw l cA b4)
         have gg:∀g∈l,g.good:=fun g hg=>(gA g hg).1;have sp:∀g∈l,∀b∈bs,g.c≠b.c:=fun g hg b hb e=>(bC' b hb).1 (e▸(gA g hg).2.1)
         by_cases bq:PD l=0
         . exact XQ k.L k.s k.c hnv.symm k.Pv k.Pu an ap (fun _=>sE) ak a7 ah l bs (by rw[PX,PX];omega) gg sp (fun b hb=>(bC' b hb).2.1) (fun b hb=>(bC' b hb).2.2) hok.1 hok.2 dx
         . by_cases df:∀dg∈mixing G11 C,oi C (11+dg)⊆k.B0 -> ∀w∈k.Lv,∀t∈Tp C,∀d:F2,O C (opnd C t d) dg -> w∈N C t (1-d) -> False
           . exact Wz k.L k.s k.c k.r k.e hnv.symm k.Pv k.Pu an ap (fun _=>sE) ak a7 ah df l bs (by rw[PX,PX];omega) gg sp (fun b hb=>(bC' b hb).2.1) (fun b hb=>(bC' b hb).2.2) hok.1 hok.2 dx
           . push Not at df;have⟨dg,e3,er,w,f8,t,ht,d',ff,hwt⟩:=df
             have ag:=k.tW (ak w f8);have⟨ub,dy⟩:=KZ k.o e3;have aj:=er dy;have huw:=YZ k.o ht (QJ ff dy) hwt.1;obtain⟨g,_,rfl⟩:=Tn (show l≠[] from fun h=>by rw[h] at bq;simp at bq);obtain⟨_,_,_,d,bn⟩:=gA g c0
             by_cases ar:ub=vb;. subst ar;exact(cu w ag huw.symm d g.c bn).elim
             have bb:ub∉k.Wb:=fun h=>k.n0 ac aj h;have c6:ub∉k.B1:=fun h=>ar (bu ub aj h);obtain⟨x,y,z,u,xy,zu,_,_,_,_,xv,yv,zv,uv,xA,xW,_,yA,yB,yvb,zA,zW,_,uA,uB,uvb⟩:=k.MJ d h01;have d8:=k.PQ;have cW:=i2 bn;have cd:=d1 (i1 bn);exfalso
             refine ZS (k.PU g.c cW) (k.Hg cd cW (d1 yA)) yv (k.Hg cd cW (d1 zA)) zv ?_ xy.symm xv ?_ ?_ (a5 x xW).symm (a5 z zW) hnv yvb.symm
              zu uv ?_ uvb ?_ ?_ (k.PU w ag) ?_ ?_ ?_ ?_ (k.H7 d xA zA ag) (k.H7 d uA yA ag) huw.symm ar ?_ ?_ ?_ ?_ (k.My aj uB xW) (k.My aj yB zW)<;>
              (simp only[mem_inter,mem_sdiff] at*;grind)
       . obtain⟨x,y,z,u,xy,zu,_,_,_,_,xv,yv,zv,uv,xA,xW,_,yA,yB,yvb,zA,zW,_,uA,uB,uvb⟩:=k.MJ 0 h01
         have d8:=k.PQ;have c5:=i2 h0;have d9:=d1 (i1 h0);have cj:=i2 av;have cw:=d1 (i1 av);exfalso
         refine ZP (k.PU cl c5) (k.PU ez cj) (k.Hg d9 c5 cw) (k.Hg cw cj (d1 xA)) xv ?_ (k.Hg d9 c5 (d1 yA)) xy yv ?_
          (k.Hg d9 c5 (d1 zA)) zv ?_ ?_ ?_ (k.Hg cw cj (d1 uA)) zu uv ?_ ?_ ?_ (a5 x xW).symm (a5 z zW) hnv yvb.symm uvb.symm<;>
          (simp only[mem_inter,mem_sdiff] at*;grind)
     . have ba:=k.PQ aa
       have Rm (z0:F) (hz0:z0∈k.B0) (hzv:z0≠vb) (h1z:Ga af z0):False:=by
        obtain⟨x,y,z,u,xy,zu,_,_,_,_,_,_,_,_,xA,xW,_,yA,yB,_,zA,zW,_,uA,uB,_⟩:=k.MJ 0 h01;have d8:=k.PQ;have fz:z0∉k.Wb:=fun h=>k.n0 ac hz0 h;have fy:z0∉k.B1:=fun h=>hzv (bu z0 hz0 h)
        refine Zx (k.PU af ba) (a5 af (i2 aa)).symm hnv (a5 x xW) ?_ ?_ (a5 z zW) ?_ ?_ ?_ (k.H7 0 xA zA ba)
         xy ?_ ?_ ?_ ?_ zu ?_ ?_ ?_ ?_ ?_ (k.H7 0 uA yA ba) h1z hzv ?_ ?_ ?_ ?_ (k.My hz0 uB xW) (k.My hz0 yB zW)<;>(simp only[mem_inter,mem_sdiff] at*;grind)
       by_cases Pv:k.v∈k.B0;. exact(Rm k.v Pv hnv.symm (k.PU af ba).symm).elim
       by_cases b4:∀u w,s(u,w)∈k.Ub -> u=vb\/ w=vb
       swap
       . push Not at b4;have⟨u,w,dc,ar,a9⟩:=b4;have hadj:=gA (uS dc)
         rcases dj u w dc ar a9 with⟨aj,cm⟩|⟨c6,hw0⟩<;>rcases(k.M6 dc).2.2.2 with⟨bb,_⟩|⟨ag,_⟩
         . exact k.n0 ac aj bb
         . obtain rfl:=uq h1 (mI cm ag) aa;exact(Rm u aj ar hadj.symm).elim
         . obtain rfl:=uq h1 (mI c6 bb) aa;exact(Rm w hw0 a9 hadj).elim
         . exact k.n0 ac hw0 ag
       rcases hA with⟨l,sA,gA,cA⟩|⟨cl,_,h0,_,_⟩
       . by_cases bq:PD l=0
         . have:=Tw k.U s(k.v,af)
           have fh:∀w∈k.Lv\{af},TC C k.a w:=fun w hw=>(k.HQ w (d1 hw)).elim id fun h=>(nS (d2 hw) (uq h1 h aa)).elim
           have⟨Ma,bk,Mb,ax,al,bl,bp⟩:=k.TH a8 ds fh a7 ah l bs (fun g hg=>(gA g hg).1)
            (fun g hg b hb e=>(bC' b hb).1 (e▸(gA g hg).2.1)) (fun b hb=>(bC' b hb).2.1) (fun b hb=>(bC' b hb).2.2) hok (k.TU (dw l cA b4))
           have:=k.TR;have:=k.RW;have:=k.J6 a8 sr Pv aa a7 bk ax bl bp;omega
         . obtain⟨g,_,rfl⟩:=Tn (show l≠[] from fun h=>by rw[h] at bq;simp at bq)
           obtain⟨_,_,_,d,bn⟩:=gA g c0;exact(cu af ba (a5 af (i2 aa)).symm d g.c bn).elim
       . exact(cu af ba (a5 af (i2 aa)).symm 0 cl h0).elim
 . have ev:E 0∪E 1=∅:=RF fun u w he=>by
    have hadj:=gA (Us2 (k.HG.trans eS) (k.HG.trans eS) he)
    have hK {x y:F} (hxW:x∈k.Wb) (hx0:x∉k.B0) (hy1:y∈k.B1) (hyv:y≠vb) (hxy:Ga x y):False:=
     QV (fun (eq:du=x)=>hx0 (eq▸i1 bd)) hyv.symm (a5 du (i2 bd)).symm (a5 x hxW).symm (k.M8 (i1 bd) (i2 bd) hy1) hxy
    rcases mU he with h|h<;>exact(k.Mm h).2.2.2.2.elim (fun a=>hK (i2 a.1) a.2.2.1 (i2 a.2.1) a.2.2.2 hadj) fun a=>hK (i2 a.1) a.2.2.1 (i2 a.2.1) a.2.2.2 hadj.symm
   have hT':∀u w,s(u,w)∈k.U -> s(u,w)∉k.Ua -> PP vb Lb s(u,w)\/ PC ib.l s(u,w):=fun u w he ae=>by
    rcases dd u w he ae with h|h|h;exact .inl h;exact .inr h;exact nE (ev▸h)
   rcases hA with⟨l,sA,gA,cA⟩|⟨dn,dt,h0,av,hW⟩
   . exact k.T0 h1 a8 a7 (P:=fun e=>PP vb Lb e\/ PC (l++ib.l) e)
      (fun u w he hu hw=>by by_cases ab:s(u,w)∈k.Ua;exact .inr (hL (cA u w ab hu hw));exact(hT' u w he ab).elim .inl fun h=>.inr (hR h))
      (fun E' Lv de ak dh=>by
       have⟨Ma,bk,Mb,ax,al,bl,bp⟩:=k.Jx ib a8 E' Lv Lb l de ak a7 ah (fun g hg=>(gA g hg).1)
        (fun e he=>by rcases dh e he with h|⟨q,hq,Pv,rfl,cn⟩|h|h;exact .inl h;exact .inr (.inr (hR (by simpa[sw] using ib.c1 (sw▸cn) hq Pv)));exact .inr (.inl h);exact .inr (.inr h))
       exact⟨Ma,bk,Mb,ax,by omega,bl,bp⟩)
   . have⟨gs,gS,gG,gC⟩:=k.Mq h0 av hW
     exact k.Jr ib a8 a7 ah gs (by omega) (fun g hg=>(gG g hg).1) (k.MQ sr gC (fun h=>.inr (hL h)) fun u w he _ _ ae=>(hT' u w he ae).elim .inl fun h=>.inr (hR h))
lemma Jm (k:Z2B C):k.Pz:=by
 classical
 by_cases h2:2 <=k.BW.card;. exact k.Jn h2
 have q:k.BW.card <=1:=by omega
 by_cases h0:k.Ib=∅;. exact k.Jg q h0
 by_cases ay:k.Ib.card=1;. have⟨vb,ak⟩:=card_eq_one.mp ay;exact k.Js q ak
 have aq:2 <=k.Ib.card:=by have:=Cpr (Nem h0);omega
 have af:k.Wb.card <=1:=Qa Q3 aq fun x hx y hy=>((Q1 k.o k.hb (i1 hy) (i2 hy)).2 x hx).symm;have⟨wb,g⟩:=H1 af
 by_cases j:wb∈k.BW
 . have a8:wb∉k.B0:=fun h=>(Q1 k.o k.hb (i1 (k.hB01▸mI h (i1 j))) (i2 (k.hB01▸mI h (i1 j)))).1 (i2 j)
   exact k.Jd j (fun w hw=>g w (i2 hw))
    (RF fun u w he=>by have hs:=k.Hq he;exact hs.2.2.2.elim (fun a=>hs.2.1 (g u a.1▸k.PQ j)) fun a=>hs.2.2.1 (g w a.1▸k.PQ j))
    (fun u w he=>by
     rcases(k.M6 he).2.2.2 with⟨h,_⟩|⟨h,_⟩
     . obtain rfl:=g u h;obtain⟨_,t,q|h2⟩:=(k.M6 he).2.1;exact(a8 (q▸t)).elim;exact⟨w,mI (sL (uS he)) (by rw[H4];exact h2▸t),rfl⟩
     . obtain rfl:=g w h;obtain⟨_,t,q|h2⟩:=(k.M6 he).2.1;exact⟨u,mI (sL (sw▸uS he)) (by rw[H4];exact q▸t),sw⟩;exact(a8 (h2▸t)).elim)
 . have aj:∀w∈k.Lv,TC C k.a w:=fun w hw=>(k.HQ w hw).elim id fun h=>(j (g w (i2 h)▸h)).elim
   let z:=mW C wb (Q4 wb (k.Ub∪k.Eb)) (k.ob (1-k.db)) (Qe k.o k.hb (1-k.db)) (fun x hx=>by
    rcases mU (sE hx) with a6|ab
    . have az:wb∈k.Wb:=(k.M6 a6).2.2.2.elim (fun a=>a.1) fun a=>g x a.1▸a.1
      obtain⟨_,a7,rfl|rfl⟩:=(k.M6 a6).2.2.1;exact(j (mI a7 az)).elim;exact a7
    . rcases(k.Hq ab).2.2.2 with⟨_,_,a7⟩|⟨ad,_,ag⟩;exact a7;exact(j (mI ag (g x ad▸ad))).elim)
    (fun _ hx=>k.Ts (sE hx)) False False.elim
   have aa:∀u w,s(u,w)∈k.Ub∪k.Eb -> Px z s(u,w):=fun u w he=>by
    rcases mU he with a6|ab
    . rcases(k.M6 a6).2.2.2 with⟨h,_⟩|⟨h,_⟩;obtain rfl:=g u h;exact⟨w,sL he,rfl⟩;obtain rfl:=g w h;exact⟨u,sL (sw▸he),sw⟩
    . rcases(k.Hq ab).2.2.2 with⟨h,_,_⟩|⟨h,_,_⟩;obtain rfl:=g u h;exact⟨w,sL he,rfl⟩;obtain rfl:=g w h;exact⟨u,sL (sw▸he),sw⟩
   rcases k.PN with⟨l,sA,gA,cA⟩|⟨ba,b9,h0,ax,hW⟩
   . obtain⟨ap,Lmv,Ma,ah,_,au,_,vg,bb,hF,av⟩:=k.Td sr aj;have:=Tq k.U k.v Lmv
     have a3:=Qw (E:=k.U\PY k.v Lmv) k.o wb (z::ap::l)
      (k.TV (fun _ _ hv aw=>Hy (HT (av hv aw))) fun u w he _ hu hw=>by
       by_cases ac:s(u,w)∈k.Ua;. exact Hy (Hy (cA u w ac hu hw))
       exact HT (aa u w (k.Me he ac)))
      (fun it Px ne=>(mC Px).elim (fun e=>(ne (e▸rfl)).elim) fun q=>(mC q).elim (fun e=>e▸vg.symm▸trivial) fun h2=>(gA it h2).1)
     have:=k.TK sr ah hF;rw[PX,PG,PG,au] at a3;simp only[z,J0] at a3;omega
   . have⟨gs,gS,gG,gC⟩:=k.Mq h0 ax hW
     obtain⟨mb,al,am,_,_⟩:=QK k.o k.s k.r k.e;have:=QN k.o k.hb al am k.w
     have a3:=Qw (E:=k.U) k.o wb (z::gs)
      (k.MQ sr gC Hy fun u w he _ _ an=>HT (aa u w (k.Me he an)))
      (fun it Px ne=>(mC Px).elim (fun e=>(ne (e▸rfl)).elim) fun q=>(gG it q).1)
     rw[PX,PG,gS] at a3;simp only[z,J0] at a3;omega
end Ctx
end Z2B
lemma Vf (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty){v:Fin 11}(j:N C a 0∩N C a 1={v})(g:v∉N C b (1-db))(h:v∉Mw C b)(q:¬Joint G11 C a b)(hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b): Bd C:=
 Z2B.Jm ⟨hL,hT,a,b,hs,hab,db,hrb,hno2,hB0ne,v,j,g,h,q,hbWit⟩
lemma WU (hL:Ls C)(hT:Tf C){a b:ℕ}(hs:Jk C={a,b})(hab:Ic C a b){db:Fin 2}(hrb:O C (opnd C b db) a)(hno2:¬O C (opnd C b (1-db)) a)(hB0ne:(N C b db).Nonempty): Bd C:=by
 by_cases hbWit:(T0For G11 C b).Nonempty\/∃m∈mixing G11 C,O C (11+m) b
 swap
 ·exact Wk hL hT hs hab hrb hno2 hbWit
 by_cases hIa2:2<=(N C a 0∩N C a 1).card
 ·exact VR hL hT hs hab hrb hno2 hB0ne hIa2 hbWit
 by_cases hIa0:N C a 0∩N C a 1=∅
 ·exact W8 hL hT hs hab hrb hno2 hB0ne hIa0 hbWit
 have Rq:(N C a 0∩N C a 1).card=1:=by have:=Cpr (Nem hIa0);omega
 have⟨v,g⟩:=Finset.card_eq_one.mp Rq
 by_cases h:v∈N C b (1-db)
 ·exact XW hL hT hs hab hrb hno2 hB0ne g h hbWit
 by_cases q:Joint G11 C a b
 ·exact XE hL hT hs hab hrb hno2 hB0ne g q hbWit
 by_cases j:v∈Mw C b
 ·exact V4 hL hT hs hab hrb hno2 hB0ne g h j q hbWit
 ·exact Vf hL hT hs hab hrb hno2 hB0ne g h j q hbWit
lemma main_core (hL:IsLeastAO G11 C)(hT:TopForm G11 C)(a3:∃q t:ℕ,q∈junk G11 C/\t∈junk G11 C/\q≠t /\ (InCone 11 C q t\/InCone 11 C t q))(j:(junk G11 C).card=2): (Ustar G11 C).card<=2*(centreless G11 C).card+(junk G11 C).card+ (orN G11 C\lam G11 C).card:=by
 have⟨q,t,a6,a8,Pt,z⟩:=a3
 have a4:junk G11 C={q,t}:=
  (Finset.eq_of_subset_of_card_le (fun x hx=>by
   rcases Nsp hx with rfl|hx
   ·exact a6
   ·rw[Sp hx];exact a8)
   (by rw[Cp Pt,j])).symm
 have h:∀{a b:ℕ},junk G11 C={a,b}->InCone 11 C a b ->
   (Ustar G11 C).card<=2*(centreless G11 C).card+(junk G11 C).card+
    (orN G11 C\lam G11 C).card:=by
  intro a b hs hab;rw[j,←VM]
  have aa:(Ustar G11 C).card<=2*(centreless G11 C).card+2+
    (rFull G11 C).card+(mixing G11 C).card+(rZero G11 C).card:=by
   have⟨db,hrb⟩:=B8 hL.1 hT hs hab
   by_cases g:OrReaches 11 C (opnd C b (1-db)) a
   ·have hr0:OrReaches 11 C (opnd C b 0) a:=by fin_cases db<;>assumption
    have hr1:OrReaches 11 C (opnd C b 1) a:=by fin_cases db<;>assumption
    exact B6 hL hT hs hab hr0 hr1
   ·rcases(side (n:=11) C b db).eq_empty_or_nonempty with hB0e|hB0ne
    ·exact WZ hL hT hs hab hrb g hB0e
    ·exact WU hL hT hs hab hrb g hB0ne
  omega
 rcases z with a7|a9
 ·exact h a4 a7
 ·exact h (by rw[a4,Finset.pair_comm]) a9

end PEqualNP.Outside.L_meta_17559

theorem PEqualNP.Outside.L_meta_17559 : (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  dsimp only
  intro C _ hL hT _ hpair _ _ _ hcard
  exact PEqualNP.Outside.L_meta_17559.main_core hL hT hpair hcard
