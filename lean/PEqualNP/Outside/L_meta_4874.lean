import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4874_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset Relation
abbrev F0:=Fin 14
abbrev S0:=Finset F0
abbrev A0:=Nat×Bool
abbrev P0:=Σ _:Nat,Nat
abbrev mS:=@Finset.mem_singleton
abbrev mI:=@Finset.mem_insert
abbrev mF:=@Finset.mem_filter
abbrev mU:=@Finset.mem_union
abbrev mN:=@Finset.mem_inter
abbrev mD:=@Finset.mem_sdiff
abbrev mE:=@Finset.mem_erase
abbrev mM:=@Finset.mem_image
abbrev mV:=@Finset.mem_univ
abbrev mP:=@Finset.mem_product
abbrev mR:=@Finset.mem_range
abbrev mG:=@Finset.mem_sigma
abbrev mB:=@Finset.mem_biUnion
abbrev mX:=@Finset.mem_singleton_self
abbrev mO:=@Finset.mem_of_mem_erase
abbrev mK:=@Finset.mem_insert_of_mem
abbrev mL:=@Finset.mem_insert_self
abbrev cL:=@Finset.card_le_card
abbrev eS:=@Finset.eq_of_subset_of_card_le
abbrev cI:=@Finset.card_insert_of_notMem
abbrev cE:=@Finset.card_erase_of_mem
abbrev cU:=@Finset.card_union_of_disjoint
abbrev cA:=@Finset.card_union_add_card_inter
abbrev cS:=@Finset.card_singleton
abbrev cP:=@Finset.card_pair
abbrev cO:=@Finset.card_pos
abbrev cZ:=@Finset.card_eq_zero
abbrev ac:=@Finset.card_eq_one
abbrev cQ:=@Finset.card_le_one
abbrev oC:=@Finset.one_lt_card
abbrev dL:=@Finset.disjoint_left
abbrev nE:=@Finset.notMem_empty
abbrev sJ:=@Finset.singleton_injective
abbrev fS:=@Finset.filter_subset
abbrev uS:=@Finset.union_subset
abbrev cF:=@Finset.card_filter_le
abbrev cJ:=@Finset.card_image_of_injOn
abbrev iS:=@Finset.insert_subset_iff
abbrev iL:=@Finset.inter_subset_left
abbrev iR:=@Finset.inter_subset_right
abbrev sS:=@Finset.singleton_subset_iff
abbrev sM:=@Finset.sum_le_sum
abbrev sD:=@Finset.sum_add_distrib
abbrev sC:=@Finset.sum_congr
abbrev cG:=@Finset.card_image_le
abbrev nN:=@Finset.not_nonempty_empty
abbrev nI:=@Finset.nonempty_iff_ne_empty
abbrev eI:=@Finset.empty_inter
abbrev qL:=@Finset.inter_eq_left
abbrev qR:=@Finset.inter_eq_right
abbrev fE:=@Finset.filter_eq_empty_iff
abbrev eF:=@Finset.eq_empty_iff_forall_notMem
abbrev eO:=@Finset.eq_empty_of_forall_notMem
abbrev ad:=@Finset.card_empty
abbrev sP:=@Finset.card_sdiff_add_card_eq_card
abbrev cD:=@Finset.card_inter_add_card_sdiff
abbrev aE:=@Finset.add_sum_erase
abbrev sU:=@Finset.ssubset_iff_subset_ne
abbrev bF:=@Bool.false_ne_true
abbrev bQ:=@Bool.false_eq_true
abbrev bA:=@Bool.and_eq_true
abbrev bO:=@Bool.or_eq_true
abbrev bT:=@Bool.not_eq_true
abbrev bN:=@Bool.not_eq_false
abbrev bE:=@Bool.eq_false_iff
abbrev bC:=@Bool.and_comm
abbrev bR:=@Bool.or_comm
abbrev bK:=@Bool.not_not
abbrev dT:=@decide_eq_true_eq
abbrev kA:=@congrArg
abbrev oL:=@Or.inl
abbrev oR:=@Or.inr
abbrev sI:=@Nat.strong_induction_on
abbrev nT:=@Nat.lt_trichotomy
abbrev nM:=@Nat.mul_comm
abbrev nZ:=@Nat.zero_le
abbrev nP:=@Nat.pos_of_ne_zero
abbrev pE:=@Prod.ext
abbrev nS:=@Ne.symm
abbrev lR:=@le_refl
abbrev lT:=@le_trans
abbrev iO:=@Set.InjOn
abbrev eP:=@Equiv.Perm
abbrev fI:=@Function.Injective
abbrev rI:=@Relation.ReflTransGen.head_induction_on
abbrev cH:=@Relation.ReflTransGen.cases_head
abbrev cT:=@Relation.ReflTransGen.cases_tail
abbrev rH:=@Relation.ReflTransGen.head
abbrev rT:=@Relation.ReflTransGen.tail
abbrev rF:=@Relation.ReflTransGen.refl
abbrev rG:=@Relation.ReflTransGen
abbrev gD:=@List.getD_eq_getElem?_getD
abbrev gE:=@List.getElem?_eq_getElem
abbrev lM:=@List.mem_map
abbrev lO:=@List.ofFn
abbrev lN:=@List.getElem?_eq_none
abbrev lD:=@List.getD_eq_default
abbrev cW:=@Classical.choose_spec
abbrev ae:=@true_and
abbrev af:=@Finset.card_image_of_injective
abbrev ag:=@Finset.card_filter_add_card_filter_not
abbrev iF:=@ite_false
abbrev iT:=@ite_true
abbrev dF:=@dite_false
abbrev ah:=@dite_true
abbrev nO:=@not_or
abbrev ai:=@not_not
abbrev aj:=@Finset.mem_image_of_mem
abbrev ak:=@Finset.sum_le_sum_of_subset
abbrev al:=@Finset.card_lt_card
abbrev am:=@Nat.add_sub_cancel_left
abbrev an:=@Nat.mul_le_mul_left
abbrev ao:=@Finset.card_union_le
abbrev ap:=@Finset.sum_union
abbrev aq:=@Finset.mem_union_left
abbrev ar:=@Finset.mem_union_right
abbrev au:=@Finset.card_sigma
abbrev av:=@Bool.and_true
abbrev aw:=@Bool.true_and
abbrev ax:=@List.getElem?_append_left
abbrev ay:=@Prod.mk.injEq
abbrev az:=@smul_eq_mul
abbrev aA:=@Nat.not_lt
abbrev aB:=@Nat.two_pow_pos
abbrev aC:=@decide_true
abbrev aD:=@decide_false
abbrev aF:=@Option.any_some
lemma o {P:Prop}(h:P:=by decide):P:=h
lemma Y {P:Prop}(h:P:=by omega):P:=h
lemma aa {P:Prop}(h:P:=by decide +kernel):P:=h
lemma ab {P:Prop}(h:P:=by simp):P:=h
def dm:Bool->Bool->Bool->Bool
 | true,a,b=>a && b
 | false,a,b=>a || b
@[simp] theorem gop_true (a b : Bool) : dm true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : dm false a b = (a || b) := rfl
abbrev aJ:=List (Bool×Nat×Nat)
def bf (D:aJ)(j:Nat):Bool:=(D.getD j (false,0,0)).1
def aZ (D:aJ)(j:Nat):Nat:=(D.getD j (false,0,0)).2.1
def aY (D:aJ)(j:Nat):Nat:=(D.getD j (false,0,0)).2.2
def ep (w:List Bool)(g:Bool×Nat×Nat):List Bool:=
 w++[dm g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
def wl (D:aJ)(w:List Bool):List Bool:=D.foldl ep w
def val (D:aJ){n:Nat}(x:Fin n->Bool)(w:Nat):Bool:=
 (wl D (lO x)).getD w false
def aV (n:Nat)(D:aJ):Prop:=
 ∀j,j<D.length->aZ D j<n+j/\aY D j<n+j/\aZ D j≠aY D j
def bL (D:aJ)(w:Nat):Finset Nat:=
 (range D.length).filter (λj=>aZ D j=w\/aY D j=w)
def aS (D:aJ)(w:Nat):Nat:=(bL D w).card
def fA (n:Nat)(D:aJ):Prop:=∀w,w+1<n+D.length->1≤aS D w
def a9 (n:Nat)(D:aJ):Prop:=aV n D/\fA n D/\D≠[]
def aO (n:Nat)(D:aJ):Nat:=n+D.length-1
def single {n:Nat}(v:Fin n):Fin n->Bool:=λi=>decide (i=v)
def O (n:Nat)(D:aJ)(w:Nat):Finset (Fin n):=
 univ.filter (λv=>val D (single v) w=true)
def cd (D:aJ)(K:Finset Nat):Nat:=∑ w∈K,(aS D w-1)
def bY (n:Nat)(D:aJ):Finset Nat:=range (n+D.length-1)
def bH (n:Nat)(D:aJ):Nat:=cd D (bY n D)
def br (n:Nat)(D:aJ):Nat:=
 cd D ((bY n D).filter (λw=>(O n D w).Nonempty))
def bu (n:Nat)(D:aJ):Nat:=
 cd D ((bY n D).filter (λw=>¬(O n D w).Nonempty))
def iQ (n:Nat)(D:aJ):Finset Nat:=
 (range (n+D.length)).filter (λw=>2≤aS D w)
def aW (n:Nat)(D:aJ):Finset (Fin n):=(iQ n D).biUnion (O n D)
def aN (n:Nat)(D:aJ):Finset (Fin n):=univ \ aW n D
def cq (n:Nat)(D:aJ):Finset (P0):=
 (bY n D).sigma (λw=>range (aS D w-1))
def dr (n:Nat)(D:aJ):Finset (P0):=
 (cq n D).filter (λu=>(O n D u.1).Nonempty)
def bc (D:aJ):Finset (A0):=range D.length×ˢ univ
def W (D:aJ)(e:A0):Nat:=if e.2=true then aY D e.1 else aZ D e.1
def bo (n:Nat)(D:aJ)(K:Finset Nat):Finset (A0):=
 (bc D).filter (λe=>W D e∈K/\n+e.1∉K)
def bi (n:Nat)(D:aJ)(K:Finset Nat):Finset Nat:=
 (range D.length).filter (λj=>n+j∈K/\aZ D j∈K/\aY D j∈K)
def eX (n:Nat)(K:Finset Nat):Finset Nat:=K.filter (λw=>w<n)
def ba (n:Nat)(D:aJ)(T:Finset (Fin n)):Finset Nat:=
 (range (n+D.length)).filter (λw=>(O n D w∩T).Nonempty)
def bJ (n:Nat)(D:aJ)(x y:Fin n):Finset Nat:=
 (range (n+D.length)).filter (λw=>x∈O n D w/\y∉O n D w)
def cn (n:Nat)(D:aJ)(b:Fin n->Nat):Prop:=
 ∀v∈aW n D,2≤aS D (b v)/\O n D (b v)={v}
def dD (n:Nat)(D:aJ)(b:Fin n->Nat):Finset (P0):=
 (aW n D).image (λv=>(⟨b v,0⟩:P0))
def aR (n:Nat)(D:aJ)(b:Fin n->Nat):Finset (P0):=
 dr n D \ dD n D b
lemma hV (D:aJ)(j:Nat)(h:j<D.length):bf D j=(D[j]).1:=by simp[bf,gD,gE h]
lemma fa (D:aJ)(j:Nat)(h:j<D.length):aZ D j=(D[j]).2.1:=by simp[aZ,gD,gE h]
lemma fg (D:aJ)(j:Nat)(h:j<D.length):aY D j=(D[j]).2.2:=by simp[aY,gD,gE h]
lemma iE (g:Bool×Nat×Nat)(D:aJ)(w:List Bool):wl (g :: D) w=wl D (ep w g):=rfl
lemma jy (D E:aJ)(w:List Bool):wl (D++E) w=wl E (wl D w):=by simp[wl,List.foldl_append]
lemma jf (w:List Bool)(g:Bool×Nat×Nat):(ep w g).length=w.length+1:=by simp[ep]
lemma ig (D:aJ):∀w:List Bool,(wl D w).length=w.length+D.length:=by
 induction D with
 | nil=>intro w;simp[wl]
 | cons g D ih=>intro w;rw[iE,ih,jf];simp;omega
lemma nU (w:List Bool)(g:Bool×Nat×Nat)(i:Nat)(h:i<w.length):(ep w g).getD i false=w.getD i false:=by simp[ep,gD,ax h]
lemma gR (D:aJ):∀(w:List Bool) (i:Nat),i<w.length->(wl D w).getD i false=w.getD i false:=by
 induction D with
 | nil=>intro w i _;rfl
 | cons g D ih=>
  intro w i h;rw[iE,ih _ _ (by rw[jf];omega),nU _ _ _ h]
lemma o5 (w:List Bool)(i:Nat)(h:w.length≤ i):w.getD i false=false:=by simp[gD,lN h]
lemma m7 (w:List Bool)(g:Bool×Nat×Nat):(ep w g).getD w.length false=dm g.1 (w.getD g.2.1 false) (w.getD g.2.2 false):=by simp[ep,gD]
lemma pX (D:aJ)(w:List Bool)(j:Nat)(l:j<D.length):(wl D w).getD (w.length+j) false=dm (bf D j) ((wl (D.take j) w).getD (aZ D j) false) ((wl (D.take j) w).getD (aY D j) false):=by
 have h:D=D.take j++D[j] :: D.drop (j+1):=ab;have k:(wl (D.take j) w).length=w.length+j:=(by rw[ig,List.length_take];omega);rw[hV D j l,fa D j l,fg D j l]
 conv_lhs=>rw[h,jy,iE]
 rw[gR _ _ _ (by rw[jf,k];omega),← k,m7]
lemma jw (D:aJ)(w:List Bool)(j i:Nat)(l:i<w.length+j)(m:j≤D.length):(wl (D.take j) w).getD i false=(wl D w).getD i false:=by
 have h:D=D.take j++D.drop j:=ab;have k:(wl (D.take j) w).length=w.length+j:=(by rw[ig,List.length_take];omega)
 conv_rhs=>rw[h,jy]
 rw[gR (D.drop j) (wl (D.take j) w) i (by rw[k];exact l)]
lemma ck (D:aJ){n:Nat}(x:Fin n->Bool)(i:Nat)(h:i<n):val D x i=x ⟨i,h⟩:=by unfold val;rw[gR _ _ _ (by simpa using h)];simp[gD,h]
lemma dS (D:aJ){n:Nat}(x:Fin n->Bool)(w:Nat)(h:n+D.length≤w):val D x w=false:=by unfold val;exact o5 _ _ (by rw[ig];simpa using h)
lemma pK (D:aJ){n:Nat}(x:Fin n->Bool)(k w:Nat)(l:w<n+k)(h:k≤D.length):val (D.take k) x w=val D x w:=by unfold val;exact jw D _ k w (by simpa using l) h
lemma cu {n:Nat}{D:aJ}(p:aV n D)(x:Fin n->Bool)(j:Nat)(k:j<D.length):val D x (n+j)=dm (bf D j) (val D x (aZ D j)) (val D x (aY D j)):=by obtain ⟨m,l,-⟩:=p j k;have h:=pX D (lO x) j k;simp only[List.length_ofFn] at h;unfold val;rw[h,jw D _ j _ (by simpa using m) k.le,jw D _ j _ (by simpa using l) k.le]
lemma gS {n:Nat}{D:aJ}(p:aV n D)(x:Fin n->Bool)(f:Nat->Bool)(k:∀i (h:i<n),f i=x ⟨i,h⟩)(r:∀j,j<D.length->f (n+j)=dm (bf D j) (f (aZ D j)) (f (aY D j))):∀w,w<n+D.length->val D x w=f w:=by
 intro w;induction w using sI with
 | _ w ih=>
  intro hw;by_cases m:w<n
  ·rw[ck D x w m,k w m]
  ·obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have l:j<D.length:=Y
   obtain ⟨ha,hb,-⟩:=p j l;rw[cu p x j l,r j l,ih _ ha Y,ih _ hb Y]
lemma lW (D E:aJ)(k:Nat)(h:k<D.length):(D++E).getD k (false,0,0)=D.getD k (false,0,0):=by simp[gD,ax h]
lemma it (D:aJ)(g:Bool×Nat×Nat):(D++[g]).getD D.length (false,0,0)=g:=by simp[gD]
lemma mj {n:Nat}{D:aJ}(r:aV n D)(t:Bool)(i j:Nat)(p:i<n+D.length)(hj:j<n+D.length)(l:i≠j):aV n (D++[(t,i,j)]):=by
 intro k hk;simp only[List.length_append,List.length_singleton] at hk;by_cases h:k<D.length
 ·simp only[aZ,aY,lW D _ k h];exact r k h
 ·have m:k=D.length:=Y;subst m;simp only[aZ,aY,it];exact ⟨p,hj,l⟩
lemma im {D:aJ}{w:Nat}(h:aS D w=0)(j:Nat)(k:j<D.length):aZ D j≠w/\aY D j≠w:=by unfold aS bL at h;rw[cZ,fE] at h;have:=h (mR.mpr k);tauto
def dW (c a:Nat):Nat:=if c<a then a-1 else a
def b9 (c w:Nat):Nat:=if w<c then w else w+1
def dI (n j:Nat)(D:aJ):aJ:=
 (D.eraseIdx j).map (λg=>(g.1,dW (n+j) g.2.1,dW (n+j) g.2.2))
lemma ii (n j:Nat)(D:aJ)(h:j<D.length):(dI n j D).length=D.length-1:=by simp[dI,List.length_eraseIdx,h]
lemma jj (n j:Nat)(D:aJ)(k:Nat)(h:b9 j k<D.length):bf (dI n j D) k=bf D (b9 j k)/\aZ (dI n j D) k=dW (n+j) (aZ D (b9 j k))/\aY (dI n j D) k=dW (n+j) (aY D (b9 j k)):=by
 have e:(dI n j D).getD k (false,0,0) =
   ((D.getD (b9 j k) (false,0,0)).1,dW (n+j) (D.getD (b9 j k) (false,0,0)).2.1,dW (n+j) (D.getD (b9 j k) (false,0,0)).2.2):=by
  simp only[dI,gD,List.getElem?_map,List.getElem?_eraseIdx];unfold b9 at h ⊢;split_ifs at h ⊢<;>simp[gE h]
 unfold bf aZ aY;rw[e];exact ⟨rfl,rfl,rfl⟩
lemma lz {n:Nat}{D:aJ}(hS:aV n D)(j:Nat)(hj:j<D.length)(l:aS D (n+j)=0):aV n (dI n j D):=by
 intro k hk;rw[ii n j D hj] at hk;have h:b9 j k<D.length:=by unfold b9;split_ifs<;>omega
 have p:(k<j/\b9 j k=k)\/(j≤k/\b9 j k=k+1):=(by unfold b9;split_ifs<;>omega);obtain ⟨ha,hb,a0⟩:=hS _ h;obtain ⟨ra,rb⟩:=im l _ h;obtain ⟨-,r,m⟩:=jj n j D k h;rw[r,m];generalize b9 j k=k' at *;generalize aZ D k'=a at *;generalize aY D k'=b at *;refine ⟨?_,?_,?_⟩<;>unfold dW<;>split_ifs<;>omega
lemma jK {n:Nat}{D:aJ}(r:aV n D)(j:Nat)(l:j<D.length)(m:aS D (n+j)=0)(x:Fin n->Bool)(w:Nat)(hw:w<n+(D.length-1)):val (dI n j D) x w=val D x (b9 (n+j) w):=by
 refine gS (lz r j l m) x (λu=>val D x (b9 (n+j) u))
  (λi hi=>?_) (λk hk=>?_) w (by rw[ii n j D l];exact hw)
 ·have e:b9 (n+j) i=i:=by unfold b9;split_ifs<;>omega
  show val D x (b9 (n+j) i)=x ⟨i,hi⟩;rw[e];exact ck D x i hi
 ·rw[ii n j D l] at hk;have h:b9 j k<D.length:=by unfold b9;split_ifs<;>omega
  obtain ⟨et,ea,eb⟩:=jj n j D k h;obtain ⟨ra,rb⟩:=im m _ h;have e1:b9 (n+j) (n+k)=n+b9 j k:=by unfold b9;split_ifs<;>omega
  have p:∀a,a≠n+j->b9 (n+j) (dW (n+j) a)=a:=(by intro a ha;unfold b9 dW;split_ifs<;>omega);show val D x (b9 (n+j) (n+k))=dm (bf (dI n j D) k)
   (val D x (b9 (n+j) (aZ (dI n j D) k)))
   (val D x (b9 (n+j) (aY (dI n j D) k)))
  rw[e1,et,ea,eb,p _ ra,p _ rb];exact cu r x _ h
section SurplusFlow
variable {n : Nat} {D : aJ}
lemma cz {w:Nat}:w∈bY n D<->w+1<n+D.length:=by unfold bY;rw[mR];omega
lemma bP (j:Nat):W D (j,false)=aZ D j:=by simp[W]
lemma bU (j:Nat):W D (j,true)=aY D j:=by simp[W]
lemma gY (l:aV n D)(w:Nat)(h:n+D.length≤w+1):aS D w=0:=by unfold aS bL;rw[cZ,fE];intro j m;have k:=mR.mp m;have:=l j k;omega
lemma ew (k:aV n D){w:Nat}(h:1≤aS D w):w+1<n+D.length:=by by_contra l;have:=gY k w Y;omega
lemma jd (P:A0->Prop)[DecidablePred P]:((bc D).filter P).card=∑ j∈range D.length,((if P (j,false) then 1 else 0)+(if P (j,true) then 1 else 0)):=by rw[card_filter,bc,sum_product];refine sC rfl (λj _=>?_);rw[Fintype.sum_bool,add_comm]
lemma mn:(bc D).card=2*D.length:=by simp[bc,card_product,nM]
lemma oj (k:aV n D)(e:A0)(h:e∈bc D):W D e+1<n+D.length:=by
 obtain ⟨j,c⟩:=e;have l:j<D.length:=by simpa[bc] using h
 have:=k j l;cases c
 ·rw[bP];omega
 ·rw[bU];omega
lemma gb (h:aV n D)(w:Nat):aS D w=((bc D).filter (λe=>W D e=w)).card:=by rw[jd,aS,bL,card_filter];refine sC rfl (λj hj=>?_);have:=(h j (mR.mp hj)).2.2;rw[bP,bU];split_ifs<;>omega
lemma k8 (l:aV n D)(K:Finset Nat):∑ w∈K,aS D w=((bc D).filter (λe=>W D e∈K)).card:=by
 rw[card_eq_sum_card_fiberwise (f:=W D) (s:=(bc D).filter (λe=>W D e∈K)) (t:=K) (λe k=>mem_coe.mpr (mF.mp (mem_coe.mp k)).2)];refine sC rfl (λw hw=>?_);rw[gb l,filter_filter];congr 1;ext e;simp only[mF];constructor
 ·rintro ⟨k,rfl⟩;exact ⟨k,hw,rfl⟩
 ·rintro ⟨k,-,h⟩;exact ⟨k,h⟩
lemma kb {K:Finset Nat}(h:∀w∈K,1≤aS D w):cd D K+K.card=∑ w∈K,aS D w:=by rw[cd,card_eq_sum_ones,← sD];exact sC rfl (λw hw=>Nat.sub_add_cancel (h w hw))
lemma jm (h:a9 n D):bH n D+n=D.length+1:=by obtain ⟨m,p,k⟩:=h;have l:0<D.length:=List.length_pos_iff.mpr k;have h1:cd D (bY n D)+(bY n D).card=∑ w∈bY n D,aS D w:=kb (λw hw=>p w (cz.mp hw));have h2:∑ w∈bY n D,aS D w=2*D.length:=(by rw[k8 m,filter_true_of_mem,mn];intro e r;exact cz.mpr (oj m e r));have h3:(bY n D).card=n+D.length-1:=card_range _;unfold bH;omega
lemma dn (n:Nat)(D:aJ):bH n D=br n D+bu n D:=by unfold bH br bu cd;exact (sum_filter_add_sum_filter_not _ _ _).symm
lemma oA (n:Nat)(D:aJ):br n D≤bH n D:=by rw[dn];omega
lemma md (h:a9 n D)(w:Nat)(hw:w<n+D.length):rG (λa b=>b<n+D.length/\n≤b/\(aZ D (b-n)=a\/aY D (b-n)=a)) w (aO n D):=by
 obtain ⟨r,hL,-⟩:=h;generalize hk:n+D.length-w=k;induction k using sI generalizing w with
 | _ k ih=>
  by_cases p:w+1=n+D.length
  ·have l:w=aO n D:=by unfold aO;omega
   rw[l]
  ·obtain ⟨j,m⟩:=cO.mp (hL w Y);simp only[bL,mF,mR] at m;have hs:=r j m.1;refine rH (b:=n+j) ⟨Y,Y,?_⟩
    (ih (n+D.length-(n+j)) Y (n+j) Y rfl)
   simpa using m.2
lemma bD {v:Fin n}{w:Nat}:v∈O n D w<->val D (single v) w=true:=by simp[O]
lemma el (k:aV n D)(x y:Fin n->Bool)(h:∀i,x i=true->y i=true)(w:Nat):val D x w=true->val D y w=true:=by
 induction w using sI with
 | _ w ih=>
  by_cases m:w<n
  ·rw[ck D x w m,ck D y w m];exact h _
  ·by_cases hw:w<n+D.length
   ·obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have l:j<D.length:=Y
    obtain ⟨r,p,-⟩:=k j l;rw[cu k x j l,cu k y j l];have h1:=ih _ r;have h2:=ih _ p;cases bf D j<;>
     simp only[gop_true,gop_false,bA,bO]<;>tauto
   ·rw[dS D x w Y];simp
lemma nf (k:aV n D)(w:Nat):val D (λ_:Fin n=>false) w=false:=by
 by_cases h:w<n+D.length
 ·exact gS k _ (λ_=>false) (λ_ _=>rfl)
   (λj _=>by cases bf D j<;>rfl) w h
 ·exact dS D _ w Y
lemma du (D:aJ)(i:Fin n):O n D i.val={i}:=by ext v;rw[bD,ck D (single v) i.val i.isLt];simp[single,eq_comm]
lemma kE (D:aJ)(w:Nat)(h:n+D.length≤w):O n D w=∅:=by ext v;simp[bD,dS D (single v) w h]
lemma fO (h:aV n D)(j:Nat)(k:j<D.length):O n D (n+j)=if bf D j=true then O n D (aZ D j)∩O n D (aY D j) else O n D (aZ D j)∪O n D (aY D j):=by ext v;rw[bD,cu h _ j k];cases bf D j<;>simp[bD]
lemma jS (h:a9 n D)(K:Finset Nat)(hK:K⊆bY n D)(l:∀j,j<D.length->n+j∈K->aZ D j∈K\/aY D j∈K):(bo n D K).card+(bi n D K).card=(eX n K).card+cd D K:=by
 obtain ⟨hS,hL,-⟩:=h;have k:∀w∈K,w+1<n+D.length:=λw p=>cz.mp (hK p);have h1:cd D K+K.card=((bc D).filter (λe=>W D e∈K)).card:=(by rw[← k8 hS,kb (λw p=>hL w (k w p))]);have h2:=ag
  (s:=(bc D).filter (λe=>W D e∈K)) (λe:A0=>n+e.1∈K)
 rw[filter_filter,filter_filter] at h2;have h3:((bc D).filter (λe=>W D e∈K/\n+e.1∈K)).card =
   ((range D.length).filter (λj=>n+j∈K)).card+(bi n D K).card:=by
  rw[jd,bi,card_filter,card_filter,← sD];refine sC rfl (λj r=>?_);have:=l j (mR.mp r);rw[bP,bU];by_cases a0:n+j∈K<;>by_cases ha:aZ D j∈K<;>by_cases hb:aY D j∈K<;>
   simp_all
 have h4:K.card=(eX n K).card+((range D.length).filter (λj=>n+j∈K)).card:=by
  rw[← ag (s:=K) (λw=>w<n),eX];congr 1;have m:K.filter (λw=>¬w<n) =
    ((range D.length).filter (λj=>n+j∈K)).image (λj=>n+j):=by
   ext w;simp only[mF,mM,mR];constructor
   ·rintro ⟨p,hn⟩;have:=k w p;exact ⟨w-n,⟨Y,by rwa[Nat.add_sub_cancel' Y]⟩,Y⟩
   ·rintro ⟨j,⟨-,r⟩,rfl⟩;exact ⟨r,Y⟩
  rw[m,af _ (add_right_injective n)]
 unfold bo;omega
lemma pJ (T:Finset (Fin n))(h:O n D (aO n D)∩T=∅):ba n D T⊆bY n D:=by
 intro w l;simp only[ba,mF,mR] at l;rw[cz];by_contra m;have k:w=aO n D:=by unfold aO;omega
 rw[k,h] at l;exact nN l.2
lemma me (D:aJ)(T:Finset (Fin n)):(eX n (ba n D T)).card=T.card:=by
 have k:eX n (ba n D T)=T.image (λv:Fin n=>v.val):=by
  ext w;simp only[eX,ba,mF,mR,mM];constructor
  ·rintro ⟨⟨-,v,h⟩,l⟩;have m:O n D w={⟨w,l⟩}:=du D ⟨w,l⟩;rw[m,mN,mS] at h;exact ⟨v,h.2,by rw[h.1]⟩
  ·rintro ⟨v,h,rfl⟩;refine ⟨⟨by have:=v.isLt;omega,v,?_⟩,v.isLt⟩;rw[du];simp[h]
 rw[k,af _ Fin.val_injective]
lemma d9 (h:a9 n D)(T:Finset (Fin n))(l:O n D (aO n D)∩T=∅):(bo n D (ba n D T)).card+(bi n D (ba n D T)).card=T.card+cd D (ba n D T):=by
 rw[← me D T];refine jS h _ (pJ T l) (λj hj hK=>?_);obtain ⟨p,r,-⟩:=h.1 j hj;simp only[ba,mF,mR] at hK ⊢;obtain ⟨v,k⟩:=hK.2;rw[mN,fO h.1 j hj] at k;split_ifs at k with ht
 ·rw[mN] at k;exact oL ⟨Y,v,mN.mpr ⟨k.1.1,k.2⟩⟩
 ·rw[mU] at k;rcases k.1 with m|m
  ·exact oL ⟨Y,v,mN.mpr ⟨m,k.2⟩⟩
  ·exact oR ⟨Y,v,mN.mpr ⟨m,k.2⟩⟩
lemma lQ (h:a9 n D)(x y:Fin n)(a5:x≠y)(a1:x∉O n D (aO n D)):(bo n D (bJ n D x y)).card+(bi n D (bJ n D x y)).card=1+cd D (bJ n D x y):=by
 have r:bJ n D x y⊆bY n D:=by
  intro w p;simp only[bJ,mF,mR] at p;rw[cz];by_contra l;have a4:w=aO n D:=by unfold aO;omega
  rw[a4] at p;exact a1 p.2.1
 have a0:eX n (bJ n D x y)={x.val}:=by
  ext w;simp only[eX,bJ,mF,mR,mS];constructor
  ·rintro ⟨⟨-,k,-⟩,p⟩;have hs:O n D w={⟨w,p⟩}:=du D ⟨w,p⟩;rw[hs,mS] at k;rw[k]
  ·rintro rfl;refine ⟨⟨by have:=x.isLt;omega,?_,?_⟩,x.isLt⟩
   ·rw[du];exact mX x
   ·rw[du,mS];exact λl=>a5 l.symm
 have a2:=jS h _ r (λj hj hK=>?_)
 ·rw[a0,cS] at a2;exact a2
 ·obtain ⟨ha,hb,-⟩:=h.1 j hj;simp only[bJ,mF,mR] at hK ⊢;obtain ⟨-,k,m⟩:=hK;rw[fO h.1 j hj] at k m;split_ifs at k m with ht
  ·rw[mN] at k m;by_cases a3:y∈O n D (aZ D j)
   ·exact oR ⟨Y,k.2,λl=>m ⟨a3,l⟩⟩
   ·exact oL ⟨Y,k.1,a3⟩
  ·rw[mU] at k m;rcases k with h1|h1
   ·exact oL ⟨Y,h1,λl=>m (oL l)⟩
   ·exact oR ⟨Y,h1,λl=>m (oR l)⟩
lemma dh {u:P0}:u∈cq n D<->u.1∈bY n D/\u.2+1<aS D u.1:=by rw[cq,mG,mR];constructor<;>rintro ⟨h,k⟩<;>exact ⟨h,Y⟩
lemma iZ (n:Nat)(D:aJ)(p:Nat->Prop)[DecidablePred p]:((cq n D).filter (λu=>p u.1)).card=cd D ((bY n D).filter p):=by
 have h:(cq n D).filter (λu=>p u.1) =
   ((bY n D).filter p).sigma (λw=>range (aS D w-1)):=by
  ext u;simp only[cq,mF,mG];tauto
 rw[h,au,cd];simp
lemma jR (n:Nat)(D:aJ):(cq n D).card=bH n D:=by rw[cq,au,bH,cd];simp
lemma kd (n:Nat)(D:aJ):(dr n D).card=br n D:=by unfold dr br;exact iZ n D (λw=>(O n D w).Nonempty)
lemma gq {v:Fin n}:v∈aW n D<->∃w,2≤aS D w/\v∈O n D w:=by
 simp only[aW,iQ,mB,mF,mR];constructor
 ·rintro ⟨w,⟨-,k⟩,h⟩;exact ⟨w,k,h⟩
 ·rintro ⟨w,k,h⟩;refine ⟨w,⟨?_,k⟩,h⟩;by_contra l;rw[kE D w Y] at h;exact nE v h
lemma eG {v:Fin n}:v∈aN n D<->∀w,v∈O n D w->aS D w≤1:=by
 rw[aN,mD,gq];constructor
 ·rintro ⟨-,h⟩ w k;by_contra m;exact h ⟨w,Y,k⟩
 ·intro h;refine ⟨mV v,?_⟩;rintro ⟨w,k,l⟩;have:=h w l;omega
lemma lv {v:Fin n}{T:Finset (Fin n)}:(({v}:Finset (Fin n))∩T).Nonempty<->v∈T:=by
 constructor
 ·rintro ⟨u,k⟩;rw[mN,mS] at k;exact k.1▸k.2
 ·intro h;exact ⟨v,mN.mpr ⟨mX v,h⟩⟩
lemma ka (b:Fin n->Nat)(p:cn n D b):iO (λv=>(⟨b v,0⟩:P0)) (aW n D:Set (Fin n)):=by intro v r l k he;have h:b v=b l:=kA Sigma.fst he;have m:=(p v r).2;rw[h,(p l k).2] at m;exact (sJ m).symm
lemma gL (k:aV n D)(b:Fin n->Nat)(r:cn n D b):dD n D b⊆dr n D:=by
 intro u h;obtain ⟨v,m,rfl⟩:=mM.mp h;obtain ⟨h2,l⟩:=r v m;have p:1≤aS D (b v):=Y
 rw[dr,mF,dh];refine ⟨⟨cz.mpr (ew k p),?_⟩,?_⟩
 ·show 0+1<aS D (b v);omega
 ·show (O n D (b v)).Nonempty;rw[l];exact singleton_nonempty v
lemma kH (b:Fin n->Nat)(hb:cn n D b):(dD n D b).card=(aW n D).card:=
 cJ (ka b hb)
lemma iD (k:aV n D)(b:Fin n->Nat)(h:cn n D b):(aW n D).card≤br n D:=by rw[← kH b h,← kd];exact cL (gL k b h)
lemma dd (k:aV n D)(b:Fin n->Nat)(h:cn n D b):(aR n D b).card+(aW n D).card=br n D:=by rw[← kH b h,← kd];exact sP (gL k b h)
lemma iU (hS:aV n D)(b:Fin n->Nat)(p:cn n D b)(T:Finset (Fin n)):cd D (ba n D T)=(T∩aW n D).card+((aR n D b).filter (λu=>(O n D u.1∩T).Nonempty)).card:=by
 have h1:cd D (ba n D T) =
   ((cq n D).filter (λu=>(O n D u.1∩T).Nonempty)).card:=by
  rw[iZ n D (λw=>(O n D w∩T).Nonempty)];symm;refine sum_subset (λw hw=>?_) (λw hw hnot=>?_)
  ·rw[mF] at hw;have:=cz.mp hw.1;exact mF.mpr ⟨mR.mpr Y,hw.2⟩
  ·rw[ba,mF] at hw;have r:w∉bY n D:=λhc=>hnot (mF.mpr ⟨hc,hw.2⟩);rw[cz] at r;simp[gY hS w Y]
 have h2:(cq n D).filter (λu=>(O n D u.1∩T).Nonempty) =
   (dD n D b).filter (λu=>(O n D u.1∩T).Nonempty)∪
    (aR n D b).filter (λu=>(O n D u.1∩T).Nonempty):=by
  ext u;have k:=gL hS b p;simp only[aR,dr,mU,mF,mD];constructor
  ·intro h;by_cases hr:u∈dD n D b
   ·exact oL ⟨hr,h.2⟩
   ·exact oR ⟨⟨⟨h.1,h.2.mono iL⟩,hr⟩,h.2⟩
  ·rintro (h|h)
   ·exact ⟨(mF.mp (k h.1)).1,h.2⟩
   ·exact ⟨h.1.1.1,h.2⟩
 have h3:Disjoint ((dD n D b).filter (λu=>(O n D u.1∩T).Nonempty))
   ((aR n D b).filter (λu=>(O n D u.1∩T).Nonempty)):=
  disjoint_filter_filter disjoint_sdiff
 have h4:(dD n D b).filter (λu=>(O n D u.1∩T).Nonempty) =
   (T∩aW n D).image (λv=>(⟨b v,0⟩:P0)):=by
  rw[dD,filter_image];congr 1;ext v;simp only[mF,mN];constructor
  ·rintro ⟨l,m⟩;rw[(p v l).2,lv] at m;exact ⟨m,l⟩
  ·rintro ⟨hT,l⟩;refine ⟨l,?_⟩;rw[(p v l).2,lv];exact hT
 rw[h1,h2,cU h3,h4,cJ ((ka b p).mono (coe_subset.mpr iR))]
lemma eN (h:aV n D)(b:Fin n->Nat)(k:cn n D b)(T:Finset (Fin n)):cd D (ba n D T)+(aW n D).card≤(T∩aW n D).card+br n D:=by
 have m:=iU h b k T;have l:=dd h b k;have p:=cF (aR n D b)
  (λu=>(O n D u.1∩T).Nonempty)
 omega
end SurplusFlow
def b3 {n:Nat}(σ:eP (Fin n))(w:Nat):Nat:=
 if h:w<n then (σ ⟨w,h⟩).val else w
def bz {n:Nat}(σ:eP (Fin n))(D:aJ):aJ:=
 D.map (λg=>(g.1,b3 σ g.2.1,b3 σ g.2.2))
lemma ir {n:Nat}(σ:eP (Fin n)){w:Nat}(h:w<n):b3 σ w=(σ ⟨w,h⟩).val:=by simp[b3,h]
lemma fv {n:Nat}(σ:eP (Fin n)){w:Nat}(h:n≤w):b3 σ w=w:=by simp[b3,aA.mpr h]
lemma eR {n:Nat}(σ:eP (Fin n)){m:Nat}(k:n≤m)(w:Nat):b3 σ w<m<->w<m:=by
 by_cases h:w<n
 ·rw[ir σ h];have:=(σ ⟨w,h⟩).isLt;constructor<;>intro<;>omega
 ·rw[fv σ (aA.mp h)]
lemma fs {n:Nat}(σ:eP (Fin n))(w:Nat):b3 σ⁻¹ (b3 σ w)=w:=by
 by_cases h:w<n
 ·rw[ir σ h,ir σ⁻¹ (σ ⟨w,h⟩).isLt];simp
 ·rw[fv σ (aA.mp h),fv σ⁻¹ (aA.mp h)]
lemma gM {n:Nat}(σ:eP (Fin n))(w:Nat):b3 σ (b3 σ⁻¹ w)=w:=by simpa using fs σ⁻¹ w
lemma iH {n:Nat}(σ:eP (Fin n)){a b:Nat}:b3 σ a=b3 σ b<->a=b:=by refine ⟨λh=>?_,kA _⟩;have:=kA (b3 σ⁻¹) h;rwa[fs,fs] at this
lemma di {n:Nat}(σ:eP (Fin n))(D:aJ):(bz σ D).length=D.length:=by simp[bz]
lemma j8 {n:Nat}(σ:eP (Fin n))(D:aJ)(j:Nat)(h:j<D.length):bf (bz σ D) j=bf D j:=by rw[hV _ j (by rw[di];exact h),hV D j h];simp[bz]
lemma f7 {n:Nat}(σ:eP (Fin n))(D:aJ)(j:Nat)(h:j<D.length):aZ (bz σ D) j=b3 σ (aZ D j):=by rw[fa _ j (by rw[di];exact h),fa D j h];simp[bz]
lemma f6 {n:Nat}(σ:eP (Fin n))(D:aJ)(j:Nat)(h:j<D.length):aY (bz σ D) j=b3 σ (aY D j):=by rw[fg _ j (by rw[di];exact h),fg D j h];simp[bz]
lemma jM {n:Nat}(σ:eP (Fin n)){D:aJ}(m:aV n D):aV n (bz σ D):=by intro j k;rw[di] at k;obtain ⟨p,r,l⟩:=m j k;rw[f7 σ D j k,f6 σ D j k];exact ⟨(eR σ (Nat.le_add_right n j) _).mpr p,(eR σ (Nat.le_add_right n j) _).mpr r,λh=>l ((iH σ).mp h)⟩
lemma km {n:Nat}(σ:eP (Fin n)){D:aJ}(m:aV n D)(x:Fin n->Bool)(w:Nat):val (bz σ D) x (b3 σ w)=val D (λi=>x (σ i)) w:=by
 by_cases p:w<n+D.length
 ·refine (gS (jM σ m) x (λw'=>val D (λi=>x (σ i)) (b3 σ⁻¹ w')) ?_ ?_ (b3 σ w) ?_).trans ?_
  ·intro i l;show val D (λi=>x (σ i)) (b3 σ⁻¹ i)=x ⟨i,l⟩;rw[ir σ⁻¹ l,ck D _ _ (σ⁻¹ ⟨i,l⟩).isLt];simp
  ·intro j k;rw[di] at k;show val D (λi=>x (σ i)) (b3 σ⁻¹ (n+j)) =
    dm (bf (bz σ D) j) (val D (λi=>x (σ i)) (b3 σ⁻¹ (aZ (bz σ D) j)))
     (val D (λi=>x (σ i)) (b3 σ⁻¹ (aY (bz σ D) j)))
   rw[fv σ⁻¹ (Nat.le_add_right n j),j8 σ D j k,f7 σ D j k,f6 σ D j k,fs,fs,cu m _ j k]
  ·rw[di];exact (eR σ (Nat.le_add_right _ _) w).mpr p
  ·show val D (λi=>x (σ i)) (b3 σ⁻¹ (b3 σ w))=_;rw[fs]
 ·have h:=aA.mp p;rw[fv σ (lT (Nat.le_add_right _ _) h),dS _ _ _ (by rw[di];exact h),dS _ _ _ h]
lemma io {n:Nat}(σ:eP (Fin n))(D:aJ)(w:Nat):aS (bz σ D) (b3 σ w)=aS D w:=by unfold aS bL;rw[di];congr 1;apply filter_congr;intro j k;have h:=mR.mp k;rw[f7 σ D j h,f6 σ D j h,iH,iH]
lemma nk {n:Nat}(σ:eP (Fin n)){D:aJ}(r:fA n D):fA n (bz σ D):=by
 rcases eq_or_ne D [] with rfl|l
 ·exact r
 ·intro m k;rw[di] at k;have p:=List.length_pos_iff.mpr l;rw[← gM σ m,io];apply r;by_cases h:m<n
  ·have:=(eR σ⁻¹ le_rfl m).mpr h;omega
  ·rw[fv σ⁻¹ (aA.mp h)];exact k
lemma os {n:Nat}(σ:eP (Fin n)){D:aJ}(h:a9 n D):a9 n (bz σ D):=
 ⟨jM σ h.1,nk σ h.2.1,by simpa[bz] using h.2.2⟩
lemma py {n:Nat}(σ:eP (Fin n)){D:aJ}(l:aV n D)(h:D≠[])(x:Fin n->Bool):val (bz σ D) x (aO n (bz σ D))=val D (λi=>x (σ i)) (aO n D):=by have k:=List.length_pos_iff.mpr h;have e:aO n (bz σ D)=b3 σ (aO n D):=(by rw[fv σ (by unfold aO;omega)];simp[aO,di]);rw[e,km σ l]
lemma mA {n:Nat}(σ:eP (Fin n))(v:Fin n):(λi=>single v (σ i))=single (σ⁻¹ v):=by
 funext i;simp only[single,decide_eq_decide];constructor
 ·intro h;rw[← h];simp
 ·intro h;rw[h];simp
lemma eH {n:Nat}(σ:eP (Fin n)){D:aJ}(k:aV n D)(w:Nat):O n (bz σ D) (b3 σ w)=(O n D w).image σ:=by
 ext v;simp only[O,mF,mV,ae,mM];rw[km σ k,mA];constructor
 ·intro h;exact ⟨σ⁻¹ v,h,ab⟩
 ·rintro ⟨a,l,rfl⟩;simpa using l
lemma oO {n:Nat}(σ:eP (Fin n)){m:Nat}(k:n≤m)(P:Nat->Prop)[DecidablePred P](g:Nat->Nat):∑ w∈(range m).filter (λw=>P (b3 σ w)),g (b3 σ w)=∑ w∈(range m).filter P,g w:=by
 refine sum_nbij' (b3 σ) (b3 σ⁻¹) ?_ ?_ ?_ ?_ ?_
 ·intro a h;simp only[mF,mR] at h ⊢;exact ⟨(eR σ k a).mpr h.1,h.2⟩
 ·intro a h;simp only[mF,mR] at h ⊢;exact ⟨(eR σ⁻¹ k a).mpr h.1,by rw[gM];exact h.2⟩
 ·intro a _;exact fs σ a
 ·intro a _;exact gM σ a
 ·intro a _;rfl
lemma gK {n:Nat}(σ:eP (Fin n))(D:aJ)(P Q:Nat->Prop)[DecidablePred P][DecidablePred Q](h:∀w,Q (b3 σ w)<->P w):cd (bz σ D) ((bY n (bz σ D)).filter Q)=cd D ((bY n D).filter P):=by
 rcases eq_or_ne D [] with rfl|k
 ·simp[cd,bz,aS,bL]
 ·have l:=List.length_pos_iff.mpr k;have m:n≤n+D.length-1:=Y
  unfold cd bY;rw[di];exact (oO σ m Q (λw=>aS (bz σ D) w-1)).symm.trans
   (sC (filter_congr λw _=>h w) λw _=>by rw[io])
lemma nu {n:Nat}(σ:eP (Fin n))(D:aJ):bH n (bz σ D)=bH n D:=by
 simpa[bH] using
  gK σ D (λ_=>True) (λ_=>True) (λ_=>Iff.rfl)
lemma n9 {n:Nat}(σ:eP (Fin n)){D:aJ}(hS:aV n D):br n (bz σ D)=br n D:=
 gK σ D _ _ (λw=>by rw[eH σ hS];simp)
lemma my {n:Nat}(σ:eP (Fin n)){D:aJ}(hS:aV n D):bu n (bz σ D)=bu n D:=
 gK σ D _ _ (λw=>by rw[eH σ hS];simp)
lemma lq {n:Nat}(σ:eP (Fin n)){D:aJ}(p:aV n D):aW n (bz σ D)=(aW n D).image σ:=by
 ext v;simp only[aW,mB,mM,iQ,mF,mR];constructor
 ·rintro ⟨m,⟨h,k⟩,r⟩;obtain ⟨w,rfl⟩:∃w,m=b3 σ w:=⟨b3 σ⁻¹ m,(gM σ m).symm⟩;rw[eH σ p,mM] at r;obtain ⟨a,l,rfl⟩:=r;rw[io] at k;rw[di,eR σ (Nat.le_add_right _ _)] at h;exact ⟨a,⟨w,⟨h,k⟩,l⟩,rfl⟩
 ·rintro ⟨a,⟨w,⟨hw,k⟩,l⟩,rfl⟩;refine ⟨b3 σ w,⟨?_,?_⟩,?_⟩
  ·rw[di];exact (eR σ (Nat.le_add_right _ _) w).mpr hw
  ·rw[io];exact k
  ·rw[eH σ p];exact aj _ l
lemma nJ {n:Nat}(σ:eP (Fin n)){D:aJ}(m:aV n D):aN n (bz σ D)=(aN n D).image σ:=by
 ext v;simp only[aN,lq σ m,mD,mV,ae,mM];constructor
 ·intro h;exact ⟨σ⁻¹ v,λhm=>h ⟨σ⁻¹ v,hm,ab⟩,ab⟩
 ·rintro ⟨a,p,rfl⟩ ⟨b,l,k⟩;exact p (σ.injective k▸l)
def je:List (Nat×Nat):=
 [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),
  (3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def eA (x:F0->Bool):Prop:=
 ∃u v:F0,(u.val,v.val)∈je/\x u=true/\x v=true
abbrev aH (u v:F0):Prop:=(u.val,v.val)∈je\/(v.val,u.val)∈je
def aQ (u v:F0):Bool:=
 (([1408,8832,12544,6272,11264,5632,2816,11,69,98,49,88,44,22]:List Nat).getD
  u.val 0).testBit v.val
lemma aK:∀u v:F0,aQ u v=true<->aH u v:=aa
lemma bh {u v:F0}:aH u v->aH v u:=Or.symm
lemma bW (u:F0):¬aH u u:=by revert u;decide +kernel
lemma f5 (x:F0->Bool):eA x<->∃u v:F0,aH u v/\x u=true/\x v=true:=by
 constructor
 ·rintro ⟨u,v,h,l,k⟩;exact ⟨u,v,oL h,l,k⟩
 ·rintro ⟨u,v,h|h,l,k⟩
  ·exact ⟨u,v,h,l,k⟩
  ·exact ⟨v,u,h,k,l⟩
lemma dH (v:F0):(univ.filter (λu=>aH v u)).card=3:=by rw[filter_congr (λu _=>(aK v u).symm)];revert v;decide +kernel
lemma nF (u v:F0)(h:u≠v):(univ.filter (λz=>aH u z/\aH v z)).card≤1:=by rw[filter_congr (λz _=>and_congr (aK u z).symm (aK v z).symm)];revert u v;decide +kernel
lemma pm:∀v w:F0,v≠w->∃z,aQ v z=true/\aQ w z=false:=aa
lemma gv (v w:F0)(h:v≠w):∃z,aH v z/\¬aH w z:=by obtain ⟨z,k,l⟩:=pm v w h;refine ⟨z,(aK v z).mp k,λh3=>?_⟩;rw[← aK,l] at h3;exact bF h3
def jl (S:S0):Prop:=∀u v:F0,aH u v->u∈S\/v∈S
def d5 (I:S0):Prop:=∀u∈I,∀v∈I,¬aH u v
lemma ou (I:S0):d5 I<->jl (univ \ I):=by
 constructor
 ·intro h u v k;by_contra l;simp only[mD,mV,ae,nO,ai] at l;exact h u l.1 v l.2 k
 ·intro h u p v r k;rcases h u v k with m|m<;>simp[p,r] at m
def fX:List (F0×F0):=
 [(0,7),(1,13),(2,8),(3,12),(4,11),(5,10),(6,9)]
def dM (v:F0):F0:=
 Fin.ofNat 14 (([7,13,8,12,11,10,9,0,2,6,5,4,3,1]:List Nat).getD v.val 0)
lemma pU:∀e∈fX,aH e.1 e.2:=aa
lemma k4:∀v:F0,aQ v (dM v)=true/\dM (dM v)=v:=aa
lemma nt:∀v:F0,(v,dM v)∈fX\/(dM v,v)∈fX:=aa
lemma oU:(∀e∈fX,aH e.1 e.2)/\∀v:F0,aH v (dM v)/\dM (dM v)=v/\((v,dM v)∈fX\/(dM v,v)∈fX):=
 ⟨pU,λv=>⟨(aK _ _).mp (k4 v).1,(k4 v).2,nt v⟩⟩
def dv (σ:eP (F0)):Prop:=∀u v:F0,aH (σ u) (σ v)<->aH u v
lemma jr {σ:eP (F0)}(h:∀u v:F0,aQ (σ u) (σ v)=aQ u v):dv σ:=λu v=>by
 rw[← aK,← aK u v,h]
lemma oS:dv 1:=λ_ _=>Iff.rfl
lemma oi {σ τ:eP (F0)}(hσ:dv σ)(hτ:dv τ):dv (σ*τ):=
 λu v=>(hσ (τ u) (τ v)).trans (hτ u v)
lemma m6 (σ:eP (F0))(hσ:dv σ)(x:F0->Bool):eA (λi=>x (σ i))<->eA x:=by
 rw[f5,f5];constructor
 ·rintro ⟨u,v,h,l,k⟩;exact ⟨σ u,σ v,(hσ u v).mpr h,l,k⟩
 ·rintro ⟨u,v,h,l,k⟩;refine ⟨σ.symm u,σ.symm v,?_,by simpa using l,by simpa using k⟩;rw[← hσ,Equiv.apply_symm_apply,Equiv.apply_symm_apply];exact h
lemma pC {σ:eP (F0)}(hσ:dv σ){I:S0}(k:d5 I):d5 (I.image σ):=by intro u l v m;obtain ⟨a,p,rfl⟩:=mM.mp l;obtain ⟨b,r,rfl⟩:=mM.mp m;rw[hσ a b];exact k a p b r
def iM (l:List Nat)(v:F0):F0:=Fin.ofNat 14 (l.getD v.val 0)
def dw:List (S0):=
 [{0,1,2,3,4,5,6},{0,1,2,3,4,5},{0,1,2,3,4},{0,1,2,5,11},{0,1,2,3},
  {0,1,2,5},{0,1,2,11},{0,1,11,12},{0,1,2},{0,1,3},{0,1,11},{0,1},
  {0,9},{0}]
def df (n:Fin 15):S0:=((∅:S0) :: dw).getD n.val ∅
lemma jh {R:S0}(h:R∈dw):∃n:Fin 15,n≠0/\df n=R:=by obtain ⟨i,k,rfl⟩:=List.mem_iff_getElem.mp h;have l:i<14:=k;refine ⟨⟨i+1,Y⟩,by simp[Fin.ext_iff],?_⟩;show ((∅:S0) :: dw).getD (i+1) ∅=dw[i];rw[List.getD_cons_succ];exact List.getD_eq_getElem _ _ k
abbrev ki (I:S0):Prop:=∀u∈I,∀v∈I,aQ u v=false
lemma o8 {I:S0}:ki I<->d5 I:=by refine forall₂_congr λu _=>forall₂_congr λv _=>?_;rw[← aK,bT]
lemma jg (R:S0)(h:R∈dw):(R.card=7/\R={0,1,2,3,4,5,6})\/(R.card=6/\R={0,1,2,3,4,5})\/(R.card=5/\(R={0,1,2,3,4}\/R={0,1,2,5,11}))\/(R.card=4/\(R={0,1,2,3}\/R={0,1,2,5}\/R={0,1,2,11}\/R={0,1,11,12}))\/(R.card=3/\(R={0,1,2}\/R={0,1,3}\/R={0,1,11}))\/(R.card=2/\(R={0,1}\/R={0,9}))\/(R.card=1/\R={0}):=by obtain ⟨n,k,rfl⟩:=jh h;revert n;decide +kernel
def pn:List (List Nat):=
 [[0,1,2,3,4,5,6,7,8,9,10,11,12,13],[1,0,4,3,5,6,2,7,13,8,9,12,11,10],
  [0,3,2,1,5,4,6,7,8,11,10,9,13,12],[0,1,5,3,6,2,4,7,10,13,8,11,12,9],
  [0,2,1,6,4,5,3,8,7,12,10,11,9,13],[0,2,4,6,1,3,5,8,10,12,7,9,11,13],
  [0,2,3,6,5,4,1,8,7,13,10,9,11,12],[1,3,5,0,2,4,6,7,9,11,13,8,10,12],
  [1,2,5,4,3,0,6,13,9,8,7,11,10,12],[1,6,0,5,2,4,3,9,7,11,13,12,10,8],
  [1,6,2,5,0,3,4,9,13,11,7,10,12,8],[11,13,8,10,12,7,9,4,6,1,3,5,0,2],
  [11,13,12,10,8,9,7,4,3,1,6,0,5,2],[11,7,13,12,9,8,10,3,4,0,6,5,2,1],
  [1,2,3,4,5,6,0,13,7,8,9,10,11,12],[2,0,1,6,3,5,4,8,13,10,12,11,9,7],
  [13,8,7,12,10,11,9,2,1,6,4,5,3,0],[8,13,7,12,9,11,10,2,0,4,6,5,3,1],
  [8,13,9,12,7,10,11,2,6,4,0,3,5,1],[8,7,13,10,9,11,12,0,2,3,6,5,4,1]]
def eV (k:Fin 20):F0->F0:=iM (pn.getD k.val [])
lemma mJ:∀k:Fin 20,∀a b:F0,eV k a=eV k b->a=b:=aa
lemma nL:∀k:Fin 20,∀u v:F0,aQ (eV k u) (eV k v)=aQ u v:=aa
lemma pp (k:Fin 20):∃τ:eP (F0),dv τ/\⇑τ=eV k:=by have l:fI (eV k):=λa b h=>mJ k a b h;exact ⟨Equiv.ofBijective (eV k) ⟨l,Finite.injective_iff_surjective.mp l⟩,jr λu v=>nL k u v,rfl⟩
def ot:List (List Nat):=
 [[0,1,9,7,10,8,14,19,17,13,18,12,11,16],[],[],[0,0,0,0,0,0,1],[],[0,0,0,0,0,2,1],
  [0,0,0,2,5,0,6],[],[],[0,0,0,0,15,0,4],[0,0,0,0,7,3,1],[0,0,0,0,0,3],
  [0,0,0,0,5,3,1,0,0,0,0,0,1],[0,0,9,2,10,0,0,0,0,0,0,12,11,13],
  [0,0,4,2,5,8,6,0,0,0,0,2,4,3]]
def kY (n:Fin 15)(w:F0):Fin 20:=
 Fin.ofNat 20 ((ot.getD n.val []).getD w.val 0)
lemma pL:∀n:Fin 15,∀w:F0,w∉df n->ki (insert w (df n))->(insert w (df n)).image (eV (kY n w))∈dw:=aa
lemma pl (R:S0)(k:R=∅\/R∈dw)(w:F0)(p:w∉R)(l:d5 (insert w R)):∃τ:eP (F0),dv τ/\(insert w R).image τ∈dw:=by
 obtain ⟨n,rfl⟩:∃n:Fin 15,df n=R:=by
  rcases k with rfl|k
  ·exact ⟨0,rfl⟩
  ·obtain ⟨n,-,h⟩:=jh k;exact ⟨n,h⟩
 obtain ⟨τ,hτ,m⟩:=pp (kY n w);exact ⟨τ,hτ,by rw[m];exact pL n w p (o8.mpr l)⟩
lemma np (I:S0):d5 I->I=∅\/∃σ:eP (F0),dv σ/\I.image σ∈dw:=by
 induction I using Finset.induction_on with
 | empty=>intro _;exact oL rfl
 | insert v J hv ih=>
  intro m
  have r:d5 J:=λu hu w hw=>
   m u (mK hu) w (mK hw)
  obtain ⟨σ,hσ,R,hR,k⟩:∃σ:eP (F0),dv σ/\∃R,(R=∅\/R∈dw)/\J.image σ=R:=by
   rcases ih r with h|⟨σ,hσ,l⟩
   ·exact ⟨1,oS,∅,oL rfl,by simp[h]⟩
   ·exact ⟨σ,hσ,_,oR l,rfl⟩
  have p:(insert v J).image σ=insert (σ v) R:=(by rw[image_insert,k]);have h2:σ v∉R:=by rw[← k];simpa using hv
  have h3:d5 (insert (σ v) R):=by rw[← p];exact pC hσ m
  obtain ⟨τ,hτ,l⟩:=pl R hR (σ v) h2 h3;refine oR ⟨τ*σ,oi hτ hσ,?_⟩;rw[Equiv.Perm.coe_mul,← image_image,p];exact l
lemma pi (I:S0)(l:d5 I)(k:I.Nonempty):∃σ:eP (F0),dv σ/\I.image σ∈dw:=by
 rcases np I l with h|h
 ·exact absurd h k.ne_empty
 ·exact h
lemma jD (v:F0):¬eA (λi=>decide (i=v)):=by rw[f5];rintro ⟨a,b,h,k,l⟩;simp only[dT] at k l;subst k;subst l;exact bW _ h
lemma ds (u v:F0):eA (λi=>decide (i=u) || decide (i=v))<->aH u v:=by
 rw[f5];constructor
 ·rintro ⟨a,b,k,l,m⟩;simp only[bO,dT] at l m;rcases l with rfl|rfl<;>rcases m with rfl|rfl
  ·exact absurd k (bW _)
  ·exact k
  ·exact bh k
  ·exact absurd k (bW _)
 ·intro h;exact ⟨u,v,h,ab,ab⟩
lemma jH {u v:F0}(h:aH u v):eA (λi=>decide (i=u) || decide (i=v)):=(ds u v).mpr h
lemma nX (i:F0):∃x y:F0->Bool,(∀k,k≠i->x k=y k)/\¬eA x/\eA y:=by refine ⟨λk=>decide (k=dM i),λk=>decide (k=i) || decide (k=dM i),?_,jD _,jH (oU.2 i).1⟩;intro k h;simp[h]
def be (D:aJ):Prop:=
 ∀x:F0->Bool,val D x (aO 14 D)=true<->eA x
lemma c4 {D:aJ}(hD:be D):O 14 D (aO 14 D)=∅:=
 eF.2
  (λv hv=>jD v ((hD _).1 (bD.1 hv)))
lemma lk (σ:eP (F0))(hσ:dv σ){D:aJ}(h:a9 14 D)(k:be D):a9 14 (bz σ D)/\be (bz σ D)/\(bz σ D).length=D.length/\bH 14 (bz σ D)=bH 14 D/\br 14 (bz σ D)=br 14 D/\bu 14 (bz σ D)=bu 14 D/\aW 14 (bz σ D)=(aW 14 D).image σ/\aN 14 (bz σ D)=(aN 14 D).image σ:=by refine ⟨os σ h,λx=>?_,di σ D,nu σ D,n9 σ h.1,my σ h.1,lq σ h.1,nJ σ h.1⟩;rw[py σ h.1 h.2.2 x,k];exact m6 σ hσ x
lemma db (n:Nat)(D:aJ):(aN n D).card+(aW n D).card=n:=by have h:=sP (subset_univ (aW n D));rw[card_univ,Fintype.card_fin] at h;exact h
lemma oF (D:aJ):jl (aW 14 D)<->d5 (aN 14 D):=by have h:univ \ aN 14 D=aW 14 D:=(by simp[aN]);rw[ou,h]
def cN {n:Nat}(G:Fin n->Fin n->Prop)(x:Fin n->Bool):Prop:=
 ∃u v:Fin n,G u v/\x u=true/\x v=true
def bG (n:Nat)(G:Fin n->Fin n->Prop)(D:aJ):Prop:=
 ∀x:Fin n->Bool,val D x (aO n D)=true<->cN G x
def bI {n:Nat}(G:Fin n->Fin n->Prop):Prop:=
 (∀u v,G u v->G v u)/\(∀u,¬G u u)/\(∀v w,v≠w->∃z,G v z/\¬G w z)/\
  (∀u v,∃a,G u a/\a≠v)
def bk (n:Nat)(D:aJ)(a b:Nat):Prop:=
 b<n+D.length/\n≤b/\(aZ D (b-n)=a\/aY D (b-n)=a)
def aL {n:Nat}(u z:Fin n):Fin n->Bool:=λi=>decide (i=u) || decide (i=z)
def bs {n:Nat}(v:Fin n)(x:Fin n->Bool):Fin n->Bool:=λi=>decide (i=v) || x i
def bt {n:Nat}(A:Finset (Fin n)):Fin n->Bool:=λi=>decide (i∈A)
lemma dt {α:Type}{r p:α->α->Prop}(h:∀a b,r a b->p a b){a b:α}(k:rG r a b):rG p a b:=by
 induction k with
 | refl=>exact rF
 | tail _ hbc ih=>exact rT ih (h _ _ hbc)
section SemCore
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma eM (v:Fin n)(x:Fin n->Bool):∀k,k≠v->x k=bs v x k:=by intro k h;simp[bs,h]
lemma d7 (v:Fin n)(x:Fin n->Bool):bs v x v=true:=by simp[bs]
lemma ia (v:Fin n)(x:Fin n->Bool):∀i,x i=true->bs v x i=true:=by intro i h;simp[bs,h]
lemma mv {x:Fin n->Bool}{u:Fin n}(k:x u=true):∀i,single u i=true->x i=true:=by intro i h;simp only[single,dT] at h;rw[h];exact k
lemma cf (hS:aV n D){u:Fin n}{w:Nat}(hu:u∈O n D w){x:Fin n->Bool}(hx:x u=true):val D x w=true:=
 el hS (single u) x (mv hx) w (bD.mp hu)
lemma d4 {v:Fin n}{w:Nat}(h:v∈O n D w):w<n+D.length:=by by_contra k;rw[kE D w Y] at h;exact nE v h
lemma dC (k:aV n D){j:Nat}(l:j<D.length)(h:bf D j=true):O n D (n+j)=O n D (aZ D j)∩O n D (aY D j):=by rw[fO k j l];simp[h]
lemma eL (k:aV n D){j:Nat}(l:j<D.length)(h:bf D j=false):O n D (n+j)=O n D (aZ D j)∪O n D (aY D j):=by rw[fO k j l];simp[h]
lemma de (k:aV n D){j:Nat}(l:j<D.length)(h:bf D j=true)(s:Bool):O n D (n+j)⊆O n D (W D (j,s)):=by
 rw[dC k l h];cases s
 ·rw[bP];exact iL
 ·rw[bU];exact iR
lemma bv (l:aV n D){j:Nat}(m:j<D.length)(s:Bool):W D (j,s)<n+j:=by
 obtain ⟨k,h,-⟩:=l j m;cases s
 ·rw[bP];exact k
 ·rw[bU];exact h
lemma mz (k:aV n D){j:Nat}(l:j<D.length)(s:Bool):W D (j,s)≠W D (j,!s):=by
 obtain ⟨-,-,h⟩:=k j l;cases s
 ·simpa[W] using h
 ·simpa[W] using h.symm
lemma b4 {j:Nat}(h:j<D.length)(s:Bool):bk n D (W D (j,s)) (n+j):=by
 refine ⟨Y,Y,?_⟩;rw[am];cases s
 ·exact oL (bP j).symm
 ·exact oR (bU j).symm
lemma dN {a b:Nat}:bk n D a b<->∃j s,j<D.length/\b=n+j/\W D (j,s)=a:=by
 constructor
 ·rintro ⟨k,l,h|h⟩
  ·exact ⟨b-n,false,Y,Y,by rw[bP];exact h⟩
  ·exact ⟨b-n,true,Y,Y,by rw[bU];exact h⟩
 ·rintro ⟨j,s,m,rfl,rfl⟩;refine ⟨Y,Y,?_⟩;rw[am];cases s
  ·exact oL (bP j).symm
  ·exact oR (bU j).symm
lemma fG (k:aV n D){a b:Nat}(h:bk n D a b):a<b:=by obtain ⟨l,p,m⟩:=h;have:=k (b-n) Y;omega
lemma fV {a c:Nat}(h:bk n D a c):c-n∈bL D a:=by unfold bL;rw[mF,mR];exact ⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
lemma eU {a c:Nat}(h:bk n D a c):1≤aS D a:=
 cO.mpr ⟨_,fV h⟩
lemma cY {a c k:Nat}(l:bk n D a c)(h:bk n D a k)(m:aS D a=1):c=k:=by have p:=fV l;have m2:=fV h;obtain ⟨r,hr⟩:=ac.mp (show (bL D a).card=1 from m);rw[hr,mS] at p m2;have:=l.2.1;have:=h.2.1;omega
lemma gt (hS:aV n D)(x y:Fin n->Bool)(v:Fin n)(a0:∀k,k≠v->x k=y k)(w:Nat)(h:val D x w≠val D y w):rG (λa b=>bk n D a b/\val D x b≠val D y b) v.val w:=by
 induction w using sI with
 | _ w ih=>
  by_cases m:w<n
  ·rw[ck D x w m,ck D y w m] at h;have a1:(⟨w,m⟩:Fin n)=v:=by
    by_contra hc;exact h (a0 _ hc)
   rw[← a1]
  ·by_cases l:w<n+D.length
   ·obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have r:j<D.length:=Y
    obtain ⟨ha,hb,-⟩:=hS j r;have hg:=h;rw[cu hS x j r,cu hS y j r] at hg;by_cases h1:val D x (aZ D j)=val D y (aZ D j)
    ·have p:val D x (aY D j)≠val D y (aY D j):=by
      intro p;apply hg;rw[h1,p]
     exact rT (ih _ hb p)
      ⟨⟨l,Y,oR (by rw[am])⟩,h⟩
    ·exact rT (ih _ ha h1)
      ⟨⟨l,Y,oL (by rw[am])⟩,h⟩
   ·exfalso;apply h;rw[dS D x w Y,dS D y w Y]
def fK (n:Nat)(D:aJ)(b v:Nat):Prop:=
 b=v\/¬rG (λa c=>bk n D a c/\c≠b) v (aO n D)
lemma k5 (hS:aV n D)(x y:Fin n->Bool)(v:Fin n)(m:∀k,k≠v->x k=y k)(b:Nat)(l:fK n D b v.val)(hb:val D x b=val D y b):val D x (aO n D)=val D y (aO n D):=by
 by_contra r;rcases l with rfl|l
 ·rw[ck D x _ v.isLt,ck D y _ v.isLt] at hb;have p:x=y:=by
   funext k;by_cases hk:k=v
   ·rw[hk];exact hb
   ·exact m k hk
  exact r (by rw[p])
 ·exact l (dt (λa c h=>⟨h.1,λhc=>h.2 (by rw[hc];exact hb)⟩) (gt hS x y v m _ r))
def aU (n:Nat)(D:aJ)(a b:Nat):Prop:=
 rG (λa c=>bk n D a c/\aS D a=1) a b
lemma c9 (hS:aV n D){v b:Nat}(h:aU n D v b):fK n D b v:=by
 induction h using rI with
 | refl=>exact oL rfl
 | @head a c hstep _ r=>
  by_cases p:b=a
  ·exact oL p
  ·right;intro hp;rcases cH hp with m|⟨c',hs,k⟩
   ·have h0:=gY hS a (by rw[m];unfold aO;omega);have h1:=hstep.2;omega
   ·have l:c=c':=cY hstep.1 hs.1 hstep.2;subst l;rcases r with rfl|r
    ·exact hs.2 rfl
    ·exact r k
lemma gQ (hS:aV n D)(v:Fin n):∀w,v∈O n D w->(∀u,u<w->v∈O n D u->aS D u≤1)->aU n D v.val w:=by
 intro w;induction w using sI with
 | _ w ih=>
  intro m k;by_cases hn:w<n
  ·have hs:O n D w={⟨w,hn⟩}:=du D ⟨w,hn⟩;rw[hs,mS] at m;rw[m];exact rF
  ·have a0:=d4 m;obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have hj:j<D.length:=Y
   have p:∀s:Bool,v∈O n D (W D (j,s))->aU n D v.val (n+j):=by
    intro s r;have h:bk n D (W D (j,s)) (n+j):=b4 hj s;have l:=bv hS hj s;have h1:=eU h;have h2:=k _ l r;exact rT (ih _ l r (λu hu=>k u Y))
     ⟨h,Y⟩
   rw[fO hS j hj] at m;split_ifs at m with ht
   ·exact p false (by rw[bP];exact (mN.mp m).1)
   ·rcases mU.mp m with h1|h1
    ·exact p false (by rw[bP];exact h1)
    ·exact p true (by rw[bU];exact h1)
lemma go (m:bI G)(v:Fin n):¬cN G (single v):=by rintro ⟨a,c,h,l,k⟩;simp only[single,dT] at l k;rw[l,k] at h;exact m.2.1 _ h
lemma oH {u v:Fin n}(huv:G u v):cN G (aL u v):=
 ⟨u,v,huv,by simp[aL],by simp[aL]⟩
lemma dV (hG:bI G)(hC:bG n G D):O n D (aO n D)=∅:=
 eF.2
  (λv hv=>go hG v ((hC _).1 (bD.1 hv)))
lemma dZ (hG:bI G)(hS:aV n D)(hC:bG n G D)(v:Fin n)(b:Nat)(m:fK n D b v.val):O n D b⊆{v}:=by
 intro u hu;rw[mS];by_contra a3;obtain ⟨a1,k,l,-⟩:=hG;obtain ⟨z,a4,r⟩:=l v u (nS a3);have a2:val D (aL u z) b=true:=cf hS hu (by simp[aL]);have a5:val D (bs v (aL u z)) b=true:=cf hS hu (by simp[bs,aL]);have a0:=k5 hS _ _ v (eM v (aL u z)) b m (by rw[a2,a5]);have h1:¬cN G (aL u z):=by
  rintro ⟨a,c,h,ha,p⟩;simp only[aL,bO,dT] at ha p;rcases ha with ha|ha<;>rcases p with p|p<;>rw[ha,p] at h
  ·exact k _ h
  ·exact r h
  ·exact r (a1 _ _ h)
  ·exact k _ h
 have h2:cN G (bs v (aL u z)):=⟨v,z,a4,d7 v _,by simp[bs,aL]⟩;have h3:=(hC _).mpr h2;rw[← a0] at h3;exact h1 ((hC _).mp h3)
lemma pS (hG:bI G)(l:aV n D)(p:bG n G D)(v:Fin n)(r:v∈aW n D):∃b,2≤aS D b/\O n D b={v}/\aU n D v.val b:=by
 classical
 have h:∃w,2≤aS D w/\v∈O n D w:=gq.mp r;obtain ⟨h1,m⟩:=Nat.find_spec h
 have k:aU n D v.val (Nat.find h):=gQ l v _ m (λu hu huv=>by
  have:=Nat.find_min h hu;by_contra hc
  exact this ⟨Y,huv⟩)
 exact ⟨Nat.find h,h1,Subset.antisymm (dZ hG l p v _ (c9 l k)) (sS.mpr m),k⟩
def kp (n:Nat)(D:aJ)(b:Fin n->Nat):Prop:=
 ∀v∈aW n D,2≤aS D (b v)/\O n D (b v)={v}/\aU n D v.val (b v)
lemma oD (r:bI G)(m:aV n D)(p:bG n G D):∃b:Fin n->Nat,kp n D b:=by
 classical
 have h:∀v:Fin n,∃b,v∈aW n D->2≤aS D b/\O n D b={v}/\aU n D v.val b:=by
  intro v;by_cases k:v∈aW n D
  ·obtain ⟨b,l⟩:=pS r m p v k;exact ⟨b,λ_=>l⟩
  ·exact ⟨0,λh=>absurd h k⟩
 choose b l using h
 exact ⟨b,λv k=>l v k⟩
lemma nx {b:Fin n->Nat}(hb:kp n D b):cn n D b:=
 λv hv=>⟨(hb v hv).1,(hb v hv).2.1⟩
lemma kO (h:bI G)(k:aV n D)(l:bG n G D):∃b:Fin n->Nat,cn n D b:=by obtain ⟨b,m⟩:=oD h k l;exact ⟨b,nx m⟩
lemma cl {v:Fin n}:v∈aN n D<->v∉aW n D:=by simp[aN]
lemma fJ (hS:aV n D){v:Fin n}(hv:v∈aN n D){w:Nat}(hw:v∈O n D w):aU n D v.val w:=
 gQ hS v w hw (λu _ hu=>eG.mp hv u hu)
lemma i8 (hG:bI G)(hS:aV n D)(hC:bG n G D){v:Fin n}(hv:v∈aN n D){w:Nat}(hw:v∈O n D w):O n D w={v}:=
 Subset.antisymm (dZ hG hS hC v w (c9 hS (fJ hS hv hw)))
  (sS.mpr hw)
lemma dp {v:Fin n}{w:Nat}:w∈ba n D {v}<->v∈O n D w:=by
 simp only[ba,mF,mR];constructor
 ·rintro ⟨-,u,k⟩;rw[mN,mS] at k;exact k.2▸k.1
 ·intro h;exact ⟨d4 h,v,mN.mpr ⟨h,mX v⟩⟩
lemma fT {v:Fin n}{e:A0}:e∈bo n D (ba n D {v})<->e.1<D.length/\v∈O n D (W D e)/\v∉O n D (n+e.1):=by simp only[bo,bc,mF,mP,mR,mV,and_true,dp]
lemma o0 {v:Fin n}(h:v∈aN n D):cd D (ba n D {v})=0:=by unfold cd;refine sum_eq_zero (λw hw=>?_);have:=eG.mp h w (dp.mp hw);omega
lemma jp (hG:bI G)(hS:aV n D)(hC:bG n G D){u v:Fin n}(a5:G u v):∃j,j<D.length/\bf D j=true/\val D (aL u v) (n+j)=true/\u∉O n D (n+j)/\v∉O n D (n+j)/\∃s:Bool,u∈O n D (W D (j,s))/\v∉O n D (W D (j,s))/\v∈O n D (W D (j,!s))/\u∉O n D (W D (j,!s)):=by
 classical
 have a0:∃w,val D (aL u v) w=true/\u∉O n D w/\v∉O n D w:=⟨aO n D,(hC _).2 (oH a5),by rw[dV hG hC];simp,by rw[dV hG hC];simp⟩;obtain ⟨k,m,l⟩:=Nat.find_spec a0;have p:∀a,a<Nat.find a0->val D (aL u v) a=true->u∈O n D a\/v∈O n D a:=(by intro a ha a6;by_contra hc;rw[nO] at hc;exact Nat.find_min a0 ha ⟨a6,hc.1,hc.2⟩);generalize Nat.find a0=w at k m l p;have a7:w<n+D.length:=(by by_contra hc;rw[dS D _ w Y] at k;exact bF k);have hn:n≤w:=by
  by_contra hc;have a1:w<n:=Y
  rw[ck D _ w a1] at k;have hs:O n D w={⟨w,a1⟩}:=du D ⟨w,a1⟩;rw[hs,mS] at m l;simp only[aL,bO,dT] at k;rcases k with h|h
  ·exact m h.symm
  ·exact l h.symm
 obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have hj:j<D.length:=Y
 obtain ⟨ha,hb,-⟩:=hS j hj;have a4:=k;rw[cu hS _ j hj] at k;rw[fO hS j hj] at m l;cases ht:bf D j
 ·exfalso;rw[ht] at k m l;simp only[gop_false,bO] at k;simp only[bQ,iF,mU,nO] at m l;rcases k with h|h
  ·rcases p _ ha h with h'|h'
   ·exact m.1 h'
   ·exact l.1 h'
  ·rcases p _ hb h with h'|h'
   ·exact m.2 h'
   ·exact l.2 h'
 ·rw[ht] at k m l;simp only[gop_true,bA] at k;simp only[iT,mN,not_and] at m l;have r:u∉O n D (n+j)/\v∉O n D (n+j):=by
   rw[dC hS hj ht];simp only[mN,not_and];exact ⟨m,l⟩
  refine ⟨j,hj,ht,a4,r.1,r.2,?_⟩;rcases p _ ha k.1 with hA|hA
  ·have hB:u∉O n D (aY D j):=m hA;have a3:v∈O n D (aY D j):=(p _ hb k.2).resolve_left hB;exact ⟨false,by simpa[W] using hA,by simpa[W] using λh=>l h a3,by simpa[W] using a3,by simpa[W] using hB⟩
  ·have hB:v∉O n D (aY D j):=l hA;have a2:u∈O n D (aY D j):=(p _ hb k.2).resolve_right hB;exact ⟨true,by simpa[W] using a2,by simpa[W] using hB,by simpa[W] using hA,by simpa[W] using λh=>m h a2⟩
lemma eJ (hG:bI G)(h:a9 n D)(hC:bG n G D){v:Fin n}(hv:v∈aN n D):∃e:A0,e.1<D.length/\bf D e.1=true/\O n D (W D e)={v}/\O n D (n+e.1)=∅/\(∀a,G v a->a∈O n D (W D (e.1,!e.2)))/\bo n D (ba n D {v})={e}/\bi n D (ba n D {v})=∅:=by
 have hS:=h.1;have a8:=d9 h {v} (by rw[dV hG hC];simp);rw[o0 hv,cS] at a8;have k:∀a,G v a->∃j s,j<D.length/\bf D j=true/\(j,s)∈bo n D (ba n D {v})/\a∈O n D (W D (j,!s)):=(by intro a p;obtain ⟨j,hj,ht,-,a7,-,s,h1,-,h3,-⟩:=jp hG hS hC p;exact ⟨j,s,hj,ht,fT.mpr ⟨hj,h1,a7⟩,h3⟩);obtain ⟨a0,a6,-⟩:=hG.2.2.2 v v;obtain ⟨j0,s0,a2,a5,r,-⟩:=k a0 a6;have m:(bo n D (ba n D {v})).card=1:=(by have:=cO.mpr ⟨_,r⟩;omega);have a3:bi n D (ba n D {v})=∅:=cZ.mp Y;obtain ⟨e,he⟩:=ac.mp m;rw[he,mS] at r;subst r;have l:O n D (W D (j0,s0))={v}:=i8 hG hS hC hv
   (fT.mp (by rw[he];exact mX _)).2.1
 have a4:v∉O n D (n+j0):=(fT.mp (by rw[he];exact mX _)).2.2;refine ⟨(j0,s0),a2,a5,l,?_,?_,he,a3⟩
 ·refine eO (λx hx=>?_);have a1:=de hS a2 a5 s0 hx;rw[l,mS] at a1;exact a4 (a1▸hx)
 ·intro a p;obtain ⟨j,s,-,-,hm,ha⟩:=k a p;rw[he,mS] at hm;rw[ay] at hm;obtain ⟨rfl,rfl⟩:=hm;exact ha
lemma ij (k:bI G)(h:a9 n D)(m:bG n G D){u v:Fin n}(p:G u v):u∈aW n D\/v∈aW n D:=by by_contra hc;rw[nO] at hc;obtain ⟨eu,-,-,-,-,a0,a1,-⟩:=eJ k h m (cl.mpr hc.1);obtain ⟨ev,-,-,a5,-,-,r,-⟩:=eJ k h m (cl.mpr hc.2);obtain ⟨j,hj,-,-,l,a4,s,h1,-,h3,-⟩:=jp k h.1 m p;have m1:(j,s)∈bo n D (ba n D {u}):=fT.mpr ⟨hj,h1,l⟩;have m2:(j,!s)∈bo n D (ba n D {v}):=fT.mpr ⟨hj,h3,a4⟩;rw[a1,mS] at m1;rw[r,mS] at m2;subst m1;subst m2;obtain ⟨a,a3,a2⟩:=k.2.2.2 u v;have h5:a∈O n D (W D (j,!s)):=a0 a a3;rw[a5,mS] at h5;exact a2 h5
lemma jv {A:Finset (Fin n)}(m:∀a∈A,∀b∈A,¬G a b):¬cN G (bt A):=by rintro ⟨a,c,h,l,k⟩;simp only[bt,dT] at l k;exact m a l c k h
lemma fq (hG:bI G)(r:aV n D)(hC:bG n G D)(A:Finset (Fin n))(hA:∀a∈A,∀b∈A,¬G a b)(x:Fin n)(a7:∃a∈A,G x a):∃j s,j<D.length/\bf D j=true/\x∈O n D (W D (j,s))/\x∉O n D (n+j)/\Disjoint (O n D (W D (j,s))) A:=by
 by_contra a3;have k:∀j s,j<D.length->bf D j=true->x∈O n D (W D (j,s))->x∉O n D (n+j)->val D (bt A) (W D (j,s))=true/\val D (bs x (bt A)) (W D (j,s))=true:=(by intro j s m ht l h2;have a2:¬Disjoint (O n D (W D (j,s))) A:=λhd=>a3 ⟨j,s,m,ht,l,h2,hd⟩;rw[not_disjoint_iff] at a2;obtain ⟨a,a0,a4⟩:=a2;exact ⟨cf r a0 (by simp[bt,a4]),cf r a0 (by simp[bs,bt,a4])⟩);have a8:∀w,x∉O n D w->val D (bt A) w=val D (bs x (bt A)) w:=by
  intro w;induction w using sI with
  | _ w ih=>
   intro p;by_cases hn:w<n
   ·rw[ck D _ w hn,ck D _ w hn];have hs:O n D w={⟨w,hn⟩}:=du D ⟨w,hn⟩;rw[hs,mS] at p;exact eM x _ _ (λhc=>p hc.symm)
   ·by_cases bm:w<n+D.length
    ·obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have m:j<D.length:=Y
     obtain ⟨ha,hb,-⟩:=r j m;rw[cu r _ j m,cu r _ j m];cases ht:bf D j
     ·rw[eL r m ht,mU,nO] at p;rw[ih _ ha p.1,ih _ hb p.2]
     ·have a6:=p;rw[dC r m ht,mN,not_and] at a6;by_cases h:x∈O n D (aZ D j)
      ·have l:=k j false m ht (by rw[bP];exact h) p;rw[bP] at l;rw[ih _ hb (a6 h),l.1,l.2]
      ·by_cases a1:x∈O n D (aY D j)
       ·have l:=k j true m ht (by rw[bU];exact a1) p;rw[bU] at l;rw[ih _ ha h,l.1,l.2]
       ·rw[ih _ ha h,ih _ hb a1]
    ·rw[dS D _ w Y,dS D _ w Y]
 have a5:=a8 (aO n D) (by rw[dV hG hC];exact nE x);obtain ⟨a,ha,h⟩:=a7;have h2:cN G (bs x (bt A)):=⟨x,a,h,d7 x _,by simp[bs,bt,ha]⟩;have h3:=(hC _).mpr h2;rw[← a5] at h3;exact jv hA ((hC _).mp h3)
lemma ga (hS:aV n D)(T M:Finset (Fin n))(hM:2≤M.card)(w:Nat)(hw:O n D w∩T=M):∃j,j<D.length/\n+j≤w/\O n D (n+j)∩T=M/\j∈bi n D (ba n D T)/\(∀u,u<n+j->O n D u∩T≠M)/\((bf D j=true/\M ⊂ O n D (aZ D j)∩T/\M ⊂ O n D (aY D j)∩T)\/(bf D j=false/\O n D (aZ D j)∩T ⊂ M/\O n D (aY D j)∩T ⊂ M/\(O n D (aZ D j)∩T)∪(O n D (aY D j)∩T)=M/\(O n D (aZ D j)∩T).Nonempty/\(O n D (aY D j)∩T).Nonempty)):=by
 classical
 have m:∃u,O n D u∩T=M:=⟨w,hw⟩;have a4:Nat.find m≤w:=Nat.find_min' m hw;have l:∀u,u<Nat.find m->O n D u∩T≠M:=λu hu=>Nat.find_min m hu;have h:=Nat.find_spec m;generalize Nat.find m=f at a4 l h;have r:M.Nonempty:=cO.mp Y;have p:∀{u:Nat},(O n D u∩T).Nonempty->u∈ba n D T:=(by intro u hu;obtain ⟨v,k⟩:=hu;exact mF.mpr ⟨mR.mpr (d4 (mN.mp k).1),v,k⟩);have a7:f<n+D.length:=(by obtain ⟨v,k⟩:=r;rw[← h] at k;exact d4 (mN.mp k).1);have a8:n≤f:=by
  by_contra hc;have a6:f<n:=Y
  have hs:O n D f={⟨f,a6⟩}:=du D ⟨f,a6⟩;have h1:M.card≤1:=(by rw[← h,hs];exact (cL iL).trans ab);omega
 obtain ⟨j,rfl⟩:∃j,f=n+j:=⟨f-n,Y⟩;have hj:j<D.length:=Y
 obtain ⟨ha,hb,-⟩:=hS j hj;have a1:=l _ ha;have a0:=l _ hb;refine ⟨j,hj,a4,h,?_,l,?_⟩
 ·have a5:(O n D (aZ D j)∩T).Nonempty/\(O n D (aY D j)∩T).Nonempty:=by
   cases ht:bf D j
   ·rw[eL hS hj ht,union_inter_distrib_right] at h;constructor
    ·rw[nI];intro he;rw[he,empty_union] at h;exact a0 h
    ·rw[nI];intro he;rw[he,union_empty] at h;exact a1 h
   ·rw[dC hS hj ht] at h;obtain ⟨v,k⟩:=r;rw[← h] at k;simp only[mN] at k;exact ⟨⟨v,mN.mpr ⟨k.1.1,k.2⟩⟩,⟨v,mN.mpr ⟨k.1.2,k.2⟩⟩⟩
  rw[bi,mF,mR];exact ⟨hj,p (by rw[h];exact r),p a5.1,p a5.2⟩
 ·cases ht:bf D j
  ·right;rw[eL hS hj ht,union_inter_distrib_right] at h;have a2:O n D (aZ D j)∩T⊆M:=by rw[← h];exact subset_union_left
   have a3:O n D (aY D j)∩T⊆M:=by rw[← h];exact subset_union_right
   refine ⟨rfl,sU.mpr ⟨a2,a1⟩,sU.mpr ⟨a3,a0⟩,h,?_,?_⟩
   ·rw[nI];intro he;rw[he,empty_union] at h;exact a0 h
   ·rw[nI];intro he;rw[he,union_empty] at h;exact a1 h
  ·left;rw[dC hS hj ht] at h;have a2:M⊆O n D (aZ D j)∩T:=by
    rw[← h];intro v k;simp only[mN] at k ⊢;exact ⟨k.1.1,k.2⟩
   have a3:M⊆O n D (aY D j)∩T:=(by rw[← h];intro v k;simp only[mN] at k ⊢;exact ⟨k.1.2,k.2⟩);exact ⟨rfl,sU.mpr ⟨a2,nS a1⟩,sU.mpr ⟨a3,nS a0⟩⟩
end SemCore
lemma ob:∀u v:F0,∃a,aQ u a=true/\a≠v:=aa
lemma bn:bI (λu v:F0=>aH u v):=
 ⟨λ_ _=>bh,bW,gv,λu v=>by
  obtain ⟨a,h1,h2⟩:=ob u v
  exact ⟨a,(aK u a).mp h1,h2⟩⟩
lemma bl {D:aJ}(hD:be D):bG 14 (λu v:F0=>aH u v) D:=
 λx=>(hD x).trans (f5 x)
lemma dY {D:aJ}(h:a9 14 D)(hD:be D):∃b:F0->Nat,cn 14 D b:=
 kO bn h.1 (bl hD)
lemma nc {D:aJ}(h:a9 14 D)(hD:be D):jl (aW 14 D):=
 λ_ _ huv=>ij bn h (bl hD) huv
def aG (n:Nat)(D:aJ)(x:Fin n):Finset (A0):=bo n D (ba n D {x})
def aI (e:A0):A0:=(e.1,!e.2)
section SemCodes
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma aP {x:Fin n}{e:A0}:e∈aG n D x<->e.1<D.length/\x∈O n D (W D e)/\x∉O n D (n+e.1):=fT
lemma aT (e:A0):aI (aI e)=e:=by simp[aI]
lemma k6 {e f:A0}(h:e.1=f.1):f=e\/f=aI e:=by obtain ⟨j,s⟩:=e;obtain ⟨k,t⟩:=f;simp only at h;subst h;cases s<;>cases t<;>simp[aI]
lemma dJ (m:aV n D){x:Fin n}{e:A0}(r:e∈aG n D x):bf D e.1=true:=by
 obtain ⟨p,k,l⟩:=aP.mp r;by_contra h;rw[bT] at h;apply l;rw[eL m p h,mU];obtain ⟨j,s⟩:=e;cases s
 ·left;simpa[W] using k
 ·right;simpa[W] using k
lemma ln (k:bI G)(h:a9 n D)(m:bG n G D)(x:Fin n):(aG n D x).card+(bi n D (ba n D {x})).card=1+cd D (ba n D {x}):=by have l:=d9 h {x} (by rw[dV k m];simp);rwa[cS] at l
lemma bp (hG:bI G)(hS:aV n D)(hC:bG n G D){x y:Fin n}(m:G x y):∃e,e∈aG n D x/\aI e∈aG n D y/\y∉O n D (W D e)/\x∉O n D (W D (aI e))/\val D (aL x y) (n+e.1)=true:=by obtain ⟨j,p,-,h,l,k,s,h1,r,h3,h4⟩:=jp hG hS hC m;exact ⟨(j,s),aP.mpr ⟨p,h1,l⟩,aP.mpr ⟨p,h3,k⟩,r,h4,h⟩
lemma jW (hG:bI G)(hS:aV n D)(hC:bG n G D){x a b y:Fin n}(a1:¬G a b)(a2:G x y)(a0:¬G y a)(r:¬G y b):∃e,e∈aG n D x/\a∉O n D (W D e)/\b∉O n D (W D e):=by
 have l:=hG.1;have k:=hG.2.1;have hA:∀u∈({a,b,y}:Finset (Fin n)),∀v∈({a,b,y}:Finset (Fin n)),¬G u v:=by
  intro u m v p;simp only[mI,mS] at m p;rcases m with m|m|m<;>rcases p with p|p|p<;>rw[m,p]
  ·exact k a
  ·exact a1
  ·exact λh=>a0 (l _ _ h)
  ·exact λh=>a1 (l _ _ h)
  ·exact k b
  ·exact λh=>r (l _ _ h)
  ·exact a0
  ·exact r
  ·exact k y
 obtain ⟨j,s,hj,-,h1,h2,hd⟩:=fq hG hS hC {a,b,y} hA x ⟨y,ab,a2⟩;exact ⟨(j,s),aP.mpr ⟨hj,h1,h2⟩,λh=>dL.mp hd h ab,λh=>dL.mp hd h ab⟩
lemma pv (l:bI G)(hS:aV n D)(r:bG n G D){x a:Fin n}(m:x≠a):∃e,e∈aG n D x/\a∉O n D (W D e):=by
 obtain ⟨z,p,k⟩:=l.2.2.1 x a m;obtain ⟨e,he,h1,-⟩:=jW l hS r (a:=a) (b:=a) (l.2.1 a) p
  (λh=>k (l.1 _ _ h)) (λh=>k (l.1 _ _ h))
 exact ⟨e,he,h1⟩
end SemCodes
lemma nY:∀x a b:F0,x≠a->x≠b->aQ a b=false->∃y,aQ x y=true/\aQ y a=false/\aQ y b=false:=aa
lemma kr:∀i x:F0,∃r s,r≠s/\aQ i r=true/\aQ i s=true/\r≠x/\s≠x:=aa
lemma jX:∀r s t i:F0,r≠s->aQ i r=true->aQ i s=true->aQ t r=true->aQ t s=true->t=i:=aa
lemma bw {u v:F0}:aQ u v=false<->¬aH u v:=by rw[← aK,bT]
lemma bB {D:aJ}(h:a9 14 D)(hD:be D){x a b:F0}(m:x≠a)(l:x≠b)(k:¬aH a b):∃e,e∈aG 14 D x/\a∉O 14 D (W D e)/\b∉O 14 D (W D e):=by
 obtain ⟨y,r,p,h3⟩:=nY x a b m l (bw.mpr k);exact jW bn h.1 (bl hD) k ((aK x y).mp r)
  (bw.mp p) (bw.mp h3)
lemma kL {D:aJ}(h:a9 14 D)(hD:be D){i x:F0}(hi:i∈aN 14 D)(c2:x≠i){e:A0}(he:aG 14 D i={e})(hY:aI e∈aG 14 D x)(hc:(aG 14 D x).card≤2):∃Z,Z≠aI e/\aG 14 D x={aI e,Z}/\(∀t,t≠x->Z∉aG 14 D t)/\∀i'∈aN 14 D,∀e',aG 14 D i'={e'}->Z.1≠e'.1:=by
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have p:∀i'∈aN 14 D,∀e',aG 14 D i'={e'}->O 14 D (W D e')={i'}/\O 14 D (14+e'.1)=∅/\∀q,aH i' q->q∈O 14 D (W D (aI e')):=(by intro i' a3 e' m;obtain ⟨e0,-,-,a6,a7,b0,c6,-⟩:=eJ hG h hC a3;have h1:({e'}:Finset (A0))={e0}:=m.symm.trans c6;have h2:e'=e0:=sJ h1;subst h2;exact ⟨a6,a7,b0⟩);obtain ⟨b8,-,bm⟩:=p i hi e he;obtain ⟨r,s,c3,a0,a2,ca,c7⟩:=kr i x;rw[aK] at a0 a2;obtain ⟨Z,hZ,c1⟩:=pv hG hS hC (x:=x) (a:=r) (nS ca);have a5:Z≠aI e:=(by rintro rfl;exact c1 (bm r a0));have hW:aG 14 D x={aI e,Z}:=by
  symm;refine eS (λf hf=>?_) ?_
  ·rw[mI,mS] at hf;rcases hf with rfl|rfl
   ·exact hY
   ·exact hZ
  ·rw[cP (nS a5)];exact hc
 have k:∀t,t≠x->Z∉aG 14 D t:=by
  intro t c0 a4;have b6:∀q,q≠x->q∈O 14 D (W D (aI e))->aH q t:=by
   intro q d1 hq;by_contra ct;obtain ⟨f,hf,h1,h2⟩:=bB h hD (x:=x) (a:=q) (b:=t)
    (nS d1) (nS c0) ct
   rw[hW,mI,mS] at hf;rcases hf with rfl|rfl
   ·exact h1 hq
   ·exact h2 (aP.mp a4).2.1
  have c8:=bh (b6 r ca (bm r a0));have d0:=bh (b6 s c7 (bm s a2));have c5:t=i:=jX r s t i c3 ((aK _ _).mpr a0)
   ((aK _ _).mpr a2) ((aK _ _).mpr c8) ((aK _ _).mpr d0)
  rw[c5,he,mS] at a4;have b5:=(aP.mp hZ).2.1;rw[a4,b8,mS] at b5;exact c2 b5
 refine ⟨Z,a5,hW,k,?_⟩;intro i' a3 e' m l;obtain ⟨-,a8,b1⟩:=p i' a3 e' m;have b2:x≠i':=by
  intro hc;have h1:(aG 14 D x).card=2:=by rw[hW,cP (nS a5)]
  rw[hc,m,cS] at h1;omega
 rcases k6 l.symm with h1|h1
 ·exact k i' (nS b2) (by rw[m,mS];exact h1)
 ·obtain ⟨r',s',ea,a1,d2,cb,-⟩:=kr i' x;rw[aK] at a1;refine k r' cb (aP.mpr ⟨(aP.mp hZ).1,?_,?_⟩)
  ·rw[h1];exact b1 r' a1
  ·rw[l,a8];exact nE _
lemma kj {α:Type}{R:α->α->Prop}(m:∀a a' b,R a b->R a' b->a=a'){u v c:α}(hu:rG R u c)(r:rG R v c):rG R u v\/rG R v u:=by
 induction hu with
 | refl=>exact oR r
 | tail hab hbc ih=>
  rcases cT r with h|⟨b',k,l⟩
  ·left;rw[← h];exact rT hab hbc
  ·have p:b'=_:=m _ _ _ l hbc;rw[p] at k;exact ih k
def dz (n:Nat)(D:aJ)(b:Fin n->Nat):Prop:=
 ∀v∈aW n D,2≤aS D (b v)/\O n D (b v)={v}/\aU n D v.val (b v)/\
  ∀w,2≤aS D w->v∈O n D w->b v≤w
def dG (n:Nat)(D:aJ)(X:Finset (Fin n))(a b:Nat):Prop:=
 bk n D a b/\aS D a=1/\∀x∈X,x∈O n D a/\x∈O n D b
section SemArms
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma bV (l:aV n D){R:Nat->Nat->Prop}(k:∀a b,R a b->bk n D a b){a b:Nat}(h:rG R a b):a≤b:=by
 induction h with
 | refl=>exact lR _
 | tail _ hbc ih=>exact lT ih (le_of_lt (fG l (k _ _ hbc)))
lemma dB (hG:bI G)(p:aV n D)(hC:bG n G D):∃b:Fin n->Nat,dz n D b:=by
 classical
 have h:∀v:Fin n,∃b,v∈aW n D->2≤aS D b/\O n D b={v}/\aU n D v.val b/\∀w,2≤aS D w->v∈O n D w->b≤w:=by
  intro v;by_cases m:v∈aW n D
  ·have k:∃w,2≤aS D w/\v∈O n D w:=gq.mp m;obtain ⟨h1,r⟩:=Nat.find_spec k
   have l:aU n D v.val (Nat.find k):=gQ p v _ r (λu hu huv=>by
    have:=Nat.find_min k hu;by_contra hc
    exact this ⟨Y,huv⟩)
   exact ⟨Nat.find k,λ_=>⟨h1,Subset.antisymm (dZ hG p hC v _ (c9 p l)) (sS.mpr r),l,λw hw1 hw2=>Nat.find_min' k ⟨hw1,hw2⟩⟩⟩
  ·exact ⟨0,λh=>absurd h m⟩
 choose b hb using h
 exact ⟨b,λv m=>hb v m⟩
lemma cX {b:Fin n->Nat}(hb:dz n D b):cn n D b:=
 λv hv=>⟨(hb v hv).1,(hb v hv).2.1⟩
lemma eT (hS:aV n D){x:Fin n}(hM:bi n D (ba n D {x})=∅){j:Nat}(m:j<D.length)(k:x∈O n D (n+j)):bf D j=false/\¬(x∈O n D (aZ D j)/\x∈O n D (aY D j)):=by have h:¬(x∈O n D (aZ D j)/\x∈O n D (aY D j)):=(by intro r;have p:j∈bi n D (ba n D {x}):=(by rw[bi,mF,mR];exact ⟨m,dp.mpr k,dp.mpr r.1,dp.mpr r.2⟩);rw[hM] at p;exact nE _ p);refine ⟨?_,h⟩;by_contra l;rw[bN] at l;rw[dC hS m l,mN] at k;exact h k
lemma ff (hG:bI G)(h:a9 n D)(m:bG n G D)(b:Fin n->Nat)(hb:cn n D b)(x:Fin n):(aG n D x).card+(bi n D (ba n D {x})).card=1+(({x}:Finset (Fin n))∩aW n D).card+((aR n D b).filter (λu=>x∈O n D u.1)).card:=by
 have h1:=ln hG h m x;have l:=iU h.1 b hb {x};have r:(aR n D b).filter (λu=>(O n D u.1∩{x}).Nonempty) =
   (aR n D b).filter (λu=>x∈O n D u.1):=by
  refine filter_congr (λu _=>?_);constructor
  ·rintro ⟨y,k⟩;rw[mN,mS] at k;exact k.2▸k.1
  ·intro p;exact ⟨x,mN.mpr ⟨p,mX x⟩⟩
 rw[r] at l;omega
lemma kC (hG:bI G)(h:a9 n D)(hC:bG n G D)(X:Finset (Fin n))(hX:X.Nonempty)(hM:∀x∈X,bi n D (ba n D {x})=∅):∀c,(∀x∈X,x∈O n D c)->(∀x∈X,∀w,c≤w->x∈O n D w->aS D w≤1)->∃e:A0,(∀x∈X,e∈aG n D x)/\rG (dG n D X) c (W D e):=by
 classical
 have hS:=h.1;obtain ⟨x0,m⟩:=hX;intro c;generalize hk:n+D.length-c=k;induction k using sI generalizing c with
 | _ k ih=>
  intro hc r;have bm:=d4 (hc x0 m);have a1:c≠aO n D:=(by intro he;have:=hc x0 m;rw[he,dV hG hC] at this;exact nE _ this);have a4:1≤aS D c:=h.2.1 c (by unfold aO at a1;omega);have hf:aS D c=1:=le_antisymm (r x0 m c (lR c) (hc x0 m)) a4;obtain ⟨j,a2⟩:=cO.mp a4;simp only[bL,mF,mR] at a2;obtain ⟨hj,a3⟩:=a2;obtain ⟨s,hs⟩:∃s:Bool,W D (j,s)=c:=by
   rcases a3 with h1|h1
   ·exact ⟨false,by rw[bP];exact h1⟩
   ·exact ⟨true,by rw[bU];exact h1⟩
  have b0:c<n+j:=hs▸bv hS hj s;by_cases p:∃x1∈X,x1∈O n D (n+j)
  ·obtain ⟨x1,a8,a5⟩:=p;have ht:=(eT hS (hM x1 a8) hj a5).1;have a0:∀x∈X,x∈O n D (n+j):=by
    intro x l;rw[eL hS hj ht,mU];rcases a3 with h1|h1
    ·left;rw[h1];exact hc x l
    ·right;rw[h1];exact hc x l
   obtain ⟨e,a6,a7⟩:=ih (n+D.length-(n+j)) Y (n+j) rfl a0
    (λx l w hw=>r x l w Y)
   refine ⟨e,a6,rH ⟨?_,hf,λx l=>⟨hc x l,a0 x l⟩⟩ a7⟩;rw[← hs];exact b4 hj s
  ·refine ⟨(j,s),λx l=>aP.mpr ⟨hj,?_,λhc2=>p ⟨x,l,hc2⟩⟩,?_⟩
   ·rw[hs];exact hc x l
   ·rw[hs]
lemma lK (hG:bI G)(h:a9 n D)(hC:bG n G D)(X:Finset (Fin n))(hX:X.Nonempty)(hM:∀x∈X,bi n D (ba n D {x})=∅)(r:Nat)(hr:∀x∈X,x∈O n D r)(hf:2≤aS D r)(c2:∀x∈X,∀w,r<w->x∈O n D w->aS D w≤1):∃P Q:A0,P.1≠Q.1/\∀x∈X,P∈aG n D x/\Q∈aG n D x:=by
 classical
 have hS:=h.1;obtain ⟨x0,k⟩:=hX;obtain ⟨j1,a3,j2,a2,b8⟩:=oC.mp (show 1<(bL D r).card from hf);have l:∀j∈bL D r,j<D.length/\r<n+j/\(aZ D j=r\/aY D j=r):=(by intro j hj;simp only[bL,mF,mR] at hj;have:=hS j hj.1;exact ⟨hj.1,Y,hj.2⟩);have a1:∀j∈bL D r,∃e:A0,(∀x∈X,e∈aG n D x)/\((e.1=j/\W D e=r)\/rG (dG n D X) (n+j) (W D e)):=by
  intro j hj;obtain ⟨a8,f3,ca⟩:=l j hj;obtain ⟨s,hs⟩:∃s:Bool,W D (j,s)=r:=by
   rcases ca with p|p
   ·exact ⟨false,by rw[bP];exact p⟩
   ·exact ⟨true,by rw[bU];exact p⟩
  by_cases a4:∃x1∈X,x1∈O n D (n+j)
  ·obtain ⟨x1,er,eb⟩:=a4;have ht:=(eT hS (hM x1 er) a8 eb).1;have c5:∀x∈X,x∈O n D (n+j):=by
    intro x hx;rw[eL hS a8 ht,mU];rcases ca with p|p
    ·left;rw[p];exact hr x hx
    ·right;rw[p];exact hr x hx
   obtain ⟨e,ec,e0⟩:=kC hG h hC X ⟨x0,k⟩ hM (n+j) c5
    (λx hx w hw=>c2 x hx w Y)
   exact ⟨e,ec,oR e0⟩
  ·exact ⟨(j,s),λx hx=>aP.mpr ⟨a8,by rw[hs];exact hr x hx,λhc2=>a4 ⟨x,hx,hc2⟩⟩,oL ⟨rfl,hs⟩⟩
 have m:∀a b,dG n D X a b->bk n D a b:=λ_ _ b1=>b1.1;have c3:∀a a' b,dG n D X a b->dG n D X a' b->a=a':=by
  intro a a' b p h2;by_contra a5;obtain ⟨g0,e5,ez⟩:=p.1;obtain ⟨-,-,d0⟩:=h2.1;have bm:b-n<D.length:=Y
  have b5:x0∈O n D (n+(b-n)):=(by rw[Nat.add_sub_cancel' e5];exact (p.2.2 x0 k).2);apply (eT hS (hM x0 k) bm b5).2;have ha:=(p.2.2 x0 k).1;have ea:=(h2.2.2 x0 k).1;rcases ez with e1|e1<;>rcases d0 with e2|e2
  ·exact absurd (e1.symm.trans e2) a5
  ·rw[e1,e2];exact ⟨ha,ea⟩
  ·rw[e1,e2];exact ⟨ea,ha⟩
  ·exact absurd (e1.symm.trans e2) a5
 have a0:∀ja∈bL D r,∀jb∈bL D r,ja≠jb->¬rG (dG n D X) (n+ja) (n+jb):=by
  intro ja eu jb bm b1 hp;obtain ⟨fc,fl,-⟩:=l ja eu;obtain ⟨ct,fz,d1⟩:=l jb bm;rcases cT hp with f1|⟨u,es,b2⟩
  ·exact b1 Y
  ·have f0:=bV hS m es;have a6:u=r:=by
    by_contra a6;obtain ⟨-,-,c7⟩:=b2.1;rw[am] at c7;apply (eT hS (hM x0 k) ct (b2.2.2 x0 k).2).2;have hu:=(b2.2.2 x0 k).1;have cb:=hr x0 k;rcases c7 with e1|e1<;>rcases d1 with e2|e2
    ·exact absurd (e1.symm.trans e2) a6
    ·rw[e1,e2];exact ⟨hu,cb⟩
    ·rw[e1,e2];exact ⟨cb,hu⟩
    ·exact absurd (e1.symm.trans e2) a6
   omega
 obtain ⟨P,a7,e3⟩:=a1 j1 a3;obtain ⟨Q,d2,c1⟩:=a1 j2 a2;refine ⟨P,Q,λhPQ=>?_,λx hx=>⟨a7 x hx,d2 x hx⟩⟩;have b0:Q=P:=by
  rcases k6 hPQ with p|p
  ·exact p
  ·exfalso;obtain ⟨e4,c6,ej⟩:=aP.mp (a7 x0 k);have b6:=(aP.mp (d2 x0 k)).2.1;rw[p] at b6;apply ej;rw[dC hS e4 (dJ hS (a7 x0 k)),mN];obtain ⟨j,s⟩:=P;cases s
   ·exact ⟨by simpa[W] using c6,by simpa[W,aI] using b6⟩
   ·exact ⟨by simpa[W,aI] using b6,by simpa[W] using c6⟩
 rw[b0] at c1;obtain ⟨-,fi,-⟩:=l j1 a3;obtain ⟨-,e7,-⟩:=l j2 a2;rcases e3 with ⟨et,gs⟩|c8<;>rcases c1 with ⟨ev,f2⟩|c0
 ·exact b8 (et.symm.trans ev)
 ·have:=bV hS m c0;omega
 ·have:=bV hS m c8;omega
 ·rcases kj c3 c8 c0 with p|p
  ·exact a0 j1 a3 j2 a2 b8 p
  ·exact a0 j2 a2 j1 a3 (nS b8) p
lemma fQ (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:cn n D b){m:P0}(k:aR n D b={m}){x:Fin n}(a0:3≤(aG n D x).card):(aG n D x).card=3/\bi n D (ba n D {x})=∅/\x∈aW n D/\x∈O n D m.1:=by
 have r:=ff hG h hC b hb x;have h2:(({x}:Finset (Fin n))∩aW n D).card≤1:=(cL iL).trans ab;have h3:=cF (aR n D b) (λu=>x∈O n D u.1);rw[k,cS] at h3;rw[k] at r;refine ⟨Y,cZ.mp Y,?_,?_⟩
 ·by_contra hx;have p:({x}:Finset (Fin n))∩aW n D=∅:=by
   rw[singleton_inter_of_notMem hx]
  rw[p,ad] at r;omega
 ·have p:0<(({m}:Finset (P0)).filter (λu=>x∈O n D u.1)).card:=by
   omega
  obtain ⟨u,l⟩:=cO.mp p;rw[mF,mS] at l;exact l.1▸l.2
lemma fw (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:dz n D b)(b2:br n D=(aW n D).card+1)(X:Finset (Fin n))(hX:X.Nonempty)(m:∀x∈X,3≤(aG n D x).card):∃P Q:A0,P.1≠Q.1/\∀x∈X,P∈aG n D x/\Q∈aG n D x:=by
 have hS:=h.1;have p:=cX hb;have r:(aR n D b).card=1:=(by have:=dd hS b p;omega);obtain ⟨u0,k⟩:=ac.mp r;have bm:u0∈aR n D b:=by rw[k];exact mX _
 have a1:u0∈cq n D:=(mF.mp (mD.mp bm).1).1;have a4:2≤aS D u0.1:=(by have:=(dh.mp a1).2;omega);refine lK hG h hC X hX (λx hx=>(fQ hG h hC b p k (m x hx)).2.1)
  u0.1 (λx hx=>(fQ hG h hC b p k (m x hx)).2.2.2) a4 ?_
 intro x hx w b5 a0;obtain ⟨-,-,b0,b1⟩:=fQ hG h hC b p k (m x hx);by_contra hc;have b6:2≤aS D w:=Y
 have a8:(⟨w,0⟩:P0)∈dr n D:=(by rw[dr,mF,dh];exact ⟨⟨cz.mpr (ew hS (w:=w) Y),by show 0+1<aS D w;omega⟩,⟨x,a0⟩⟩);by_cases a7:(⟨w,0⟩:P0)∈dD n D b
 ·obtain ⟨v,hv,a6⟩:=mM.mp a7;have a5:b v=w:=kA Sigma.fst a6;have a2:=(hb v hv).2.1;rw[a5] at a2;rw[a2,mS] at a0;have a3:=(hb x b0).2.2.2 u0.1 a4 b1;rw[a0,a5] at a3;omega
 ·have l:(⟨w,0⟩:P0)∈aR n D b:=mD.mpr ⟨a8,a7⟩;rw[k,mS] at l
  have:w=u0.1:=kA Sigma.fst l
  omega
end SemArms
section SemPaths
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma iX (a:Fin n):bt ({a}:Finset (Fin n))=single a:=by funext k;simp[bt,single]
lemma cc (h:aV n D)(x:Fin n->Bool){j:Nat}(k:j<D.length)(s:Bool):val D x (n+j)=dm (bf D j) (val D x (W D (j,s))) (val D x (W D (j,!s))):=by
 rw[cu h x j k];cases s
 ·simp[W]
 ·cases bf D j<;>simp[W,bC,bR]
lemma k9 (p:bI G){i:Fin n}{S:Finset (Fin n)}(h:cN G (bs i (bt S))):(∃a∈S,G i a)\/∃a∈S,∃b∈S,G a b:=by
 obtain ⟨u,v,k,l,m⟩:=h;simp only[bs,bt,bO,dT] at l m;rcases l with l|l<;>rcases m with m|m
 ·rw[l,m] at k;exact absurd k (p.2.1 i)
 ·rw[l] at k;exact oL ⟨v,m,k⟩
 ·rw[m] at k;exact oL ⟨u,l,p.1 _ _ k⟩
 ·exact oR ⟨u,l,v,m,k⟩
lemma ip (hS:aV n D){v b t:Nat}(h:aU n D v b)(a0:b≤t):b=v\/¬rG (λa c=>bk n D a c/\c≠b) v t:=by
 induction h using rI with
 | refl=>exact oL rfl
 | @head a c hstep hrest p=>
  by_cases m:b=a
  ·exact oL m
  ·right;intro hp;rcases cH hp with a1|⟨c',r,k⟩
   ·have h1:=fG hS hstep.1;have h2:=bV hS (λ_ _ hab=>hab.1) hrest;omega
   ·have l:c=c':=cY hstep.1 r.1 hstep.2;subst l;rcases p with rfl|p
    ·exact r.2 rfl
    ·exact p k
lemma gW (hS:aV n D)(x y:Fin n->Bool)(v:Fin n)(m:∀k,k≠v->x k=y k)(b t:Nat)(l:b=v.val\/¬rG (λa c=>bk n D a c/\c≠b) v.val t)(hb:val D x b=val D y b):val D x t=val D y t:=by
 by_contra r;rcases l with rfl|l
 ·rw[ck D x _ v.isLt,ck D y _ v.isLt] at hb;have p:x=y:=by
   funext k;by_cases hk:k=v
   ·rw[hk];exact hb
   ·exact m k hk
  exact r (by rw[p])
 ·exact l (dt (λa c h=>⟨h.1,λhc=>h.2 (by rw[hc];exact hb)⟩) (gt hS x y v m _ r))
lemma gj (r:aV n D){a c q:Nat}(hc:aU n D a c)(k:rG (bk n D) a q):rG (bk n D) c q\/(aU n D q c/\q≠c):=by
 revert k;induction hc using rI with
 | refl=>exact λk=>oL k
 | @head a a' hstep hrest ih=>
  intro k;rcases cH k with p|⟨l,hs,h⟩
  ·right;have h1:=fG r hstep.1;have h2:=bV r (λ_ _ hab=>hab.1) hrest;refine ⟨?_,Y⟩;rw[← p];exact rH hstep hrest
  ·have m:a'=l:=cY hstep.1 hs hstep.2;subst m;exact ih h
lemma kc (hS:aV n D)(v:Fin n){j:Nat}(hj:j<D.length)(s:Bool)(a1:aU n D v.val (W D (j,!s)))(hf:aS D (W D (j,!s))=1)(x y:Fin n->Bool)(a2:∀k,k≠v->x k=y k):val D x (W D (j,s))=val D y (W D (j,s)):=by
 by_contra a3;have hp:rG (bk n D) v.val (W D (j,s)):=dt (λ_ _ h=>h.1) (gt hS x y v a2 _ a3);have m:bk n D (W D (j,!s)) (n+j):=b4 hj (!s);have p:bk n D (W D (j,s)) (n+j):=b4 hj s;have a4:=bv hS hj s;have a5:=bv hS hj (!s);rcases gj hS a1 hp with h1|⟨h1,h2⟩
 ·rcases cH h1 with a0|⟨c',hs,l⟩
  ·exact mz hS hj s a0.symm
  ·have r:n+j=c':=cY m hs hf;subst r;have:=bV hS (λ_ _ h=>h) l;omega
 ·rcases cH h1 with a0|⟨q',hs,l⟩
  ·exact h2 a0
  ·have r:n+j=q':=cY p hs.1 hs.2;subst r;have:=bV hS (λ_ _ h=>h.1) l;omega
lemma gc (r:aV n D)(p:bG n G D)(x:Fin n->Bool)(v:Fin n)(b:Nat)(k:fK n D b v.val)(h0:¬cN G x)(h1:cN G (bs v x)):val D x b=false/\val D (bs v x) b=true:=by
 have l:val D x b≠val D (bs v x) b:=(by intro m;have h2:=k5 r x _ v (eM v x) b k m;exact h0 ((p x).mp (by rw[h2];exact (p _).mpr h1)));have h:=el r x (bs v x) (ia v x) b;cases hx:val D x b
 ·refine ⟨rfl,?_⟩;cases hy:val D (bs v x) b
  ·exact absurd (hx.trans hy.symm) l
  ·rfl
 ·exact absurd (hx.trans (h hx).symm) l
lemma ns (l:aV n D)(i:Fin n)(w:Nat)(b2:aU n D i.val w)(Bs N:Finset (Fin n))(hN:N⊆Bs)(h0:val D (bs i (bt (Bs \ N))) w=false)(h1:∀a∈N,val D (bs i (bt {a})) w=true)(hz:∀a∈N,val D (bt {a}) w=false):∃j s,j<D.length/\bf D j=true/\n+j≤w/\aU n D i.val (W D (j,!s))/\O n D (W D (j,s))∩Bs=N:=by
 have hJ:∀c,aU n D i.val c->(val D (bs i (bt (Bs \ N))) c=true\/∃j s,j<D.length/\bf D j=true/\n+j≤c/\aU n D i.val (W D (j,!s))/\aS D (W D (j,!s))=1/\val D (bt (Bs \ N)) (W D (j,s))=false):=by
  intro c hc;induction hc with
  | refl=>left;rw[ck D _ _ i.isLt];exact d7 i _
  | tail hab hbc ih=>
   obtain ⟨j,s,m,rfl,rfl⟩:=dN.mp hbc.1;have b5:=bv l m s;rcases ih with hy|⟨j',s',bm,a4,r,a7,b1,a5⟩
   ·cases ht:bf D j
    ·left;rw[cc l _ m s,ht,gop_false,hy];rfl
    ·by_cases hq:val D (bs i (bt (Bs \ N))) (W D (j,!s))=true
     ·left;rw[cc l _ m s,ht,gop_true,hy,hq];rfl
     ·right;refine ⟨j,!s,m,ht,lR _,by rw[bK];exact hab,by rw[bK];exact hbc.2,?_⟩;by_contra h;rw[bN] at h;exact hq (el l _ _ (ia i _) _ h)
   ·right;exact ⟨j',s',bm,a4,Y,a7,b1,a5⟩
 rcases hJ w b2 with hy|⟨j,s,m,ht,r,hc,hf,hv⟩
 ·rw[h0] at hy;exact absurd hy bF
 ·refine ⟨j,s,m,ht,r,hc,?_⟩;have a1:aU n D i.val (n+j):=rT hc ⟨b4 m (!s),hf⟩;ext a;rw[mN];constructor
  ·rintro ⟨b0,a8⟩;by_contra k;have:=cf l b0 (x:=bt (Bs \ N))
    (by simp[bt,a8,k])
   rw[hv] at this;exact bF this
  ·intro k;refine ⟨?_,hN k⟩;have a3:val D (bt {a}) (n+j)≠val D (bs i (bt {a})) (n+j):=by
    intro a6;have h2:=gW l _ _ i (eM i (bt {a})) (n+j) w
     (ip l a1 r) a6
    rw[hz a k,h1 a k] at h2;exact bF h2
   have a2:val D (bs i (bt {a})) (n+j)=true:=(by by_contra h;rw[bT] at h;apply a3;rw[h];by_contra a0;rw[bN] at a0;rw[el l _ _ (ia i _) _ a0] at h;exact Bool.noConfusion h);rw[cc l _ m s,ht,gop_true,bA] at a2;have p:=kc l i m s hc hf _ _ (eM i (bt {a}));rw[a2.1,iX] at p;exact bD.mpr p
lemma j5 (hS:aV n D)(i:Fin n)(w:Nat)(m:aU n D i.val w)(Bs:Finset (Fin n))(h0:∀S:Finset (Fin n),S⊆Bs->(∀a∈S,¬G i a)->val D (bs i (bt S)) w=false)(p:∀a∈Bs,G i a->val D (bs i (bt {a})) w=true/\val D (bt {a}) w=false):∃j s,j<D.length/\bf D j=true/\n+j≤w/\aU n D i.val (W D (j,!s))/\∀a∈Bs,(a∈O n D (W D (j,s))<->G i a):=by
 classical
 obtain ⟨j,s,hj,r,l,hc,h⟩:=ns hS i w m Bs (Bs.filter (λa=>G i a))
  (fS _ _)
  (h0 _ sdiff_subset (λa ha k=>by
   rw[mD,mF] at ha
   exact ha.2 ⟨ha.1,k⟩))
  (λa ha=>(p a (mF.mp ha).1 (mF.mp ha).2).1)
  (λa ha=>(p a (mF.mp ha).1 (mF.mp ha).2).2)
 refine ⟨j,s,hj,r,l,hc,λa ha=>?_⟩;constructor
 ·intro has
  have:a∈O n D (W D (j,s))∩Bs:=mN.mpr ⟨has,ha⟩
  rw[h,mF] at this;exact this.2
 ·intro k
  have:a∈Bs.filter (λa=>G i a):=mF.mpr ⟨ha,k⟩
  rw[← h] at this;exact (mN.mp this).1
lemma n0 (hG:bI G)(m:aV n D)(r:bG n G D){i:Fin n}(p:i∈aN n D){b:Nat}(k:aU n D i.val b)(hf:2≤aS D b):O n D b=∅:=by have h:=dZ hG m r i b (c9 m k);refine eO (λx hx=>?_);have l:=h hx;rw[mS] at l;have h2:=eG.mp p b (l▸hx);omega
lemma nb {a t:Nat}(m:rG (bk n D) a t):aU n D a t\/∃b,aU n D a b/\2≤aS D b:=by
 induction m using rI with
 | refl=>exact oL rF
 | @head a a' hstep _ ih=>
  by_cases k:aS D a=1
  ·rcases ih with h|⟨b,h,l⟩
   ·exact oL (rH ⟨hstep,k⟩ h)
   ·exact oR ⟨b,rH ⟨hstep,k⟩ h,l⟩
  ·have:=eU hstep;exact oR ⟨a,rF,Y⟩
lemma cr (hG:bI G)(h:a9 n D)(r:bG n G D){i:Fin n}(p:i∈aN n D):aU n D i.val (aO n D)\/∃b,aU n D i.val b/\2≤aS D b/\O n D b=∅:=by
 have l:i.val<n+D.length:=by have:=i.isLt;omega
 have hp:rG (bk n D) i.val (aO n D):=md h i.val l;rcases nb hp with k|⟨b,k,m⟩
 ·exact oL k
 ·exact oR ⟨b,k,m,n0 hG h.1 r p k m⟩
lemma ie (hS:aV n D){b:Nat}(hf:2≤aS D b)(he:O n D b=∅):b∈(bY n D).filter (λw=>¬(O n D w).Nonempty):=
 mF.mpr ⟨cz.mpr (ew hS (w:=b) (by omega)),
  by rw[he];exact nN⟩
lemma eB (m:aV n D)(k:bu n D=0){b:Nat}(l:2≤aS D b):(O n D b).Nonempty:=by
 by_contra h;rw[not_nonempty_iff_eq_empty] at h;have p:aS D b-1≤∑ w∈(bY n D).filter (λw=>¬(O n D w).Nonempty),(aS D w-1):=single_le_sum (f:=λw=>aS D w-1) (λ_ _=>nZ _)
  (ie m l h)
 unfold bu cd at k;omega
lemma ex (hS:aV n D)(m:bu n D≤1){b k:Nat}(hf:2≤aS D b)(he:O n D b=∅)(l:2≤aS D k)(p:O n D k=∅):b=k:=by
 by_contra r;have h:({b,k}:Finset Nat)⊆(bY n D).filter (λw=>¬(O n D w).Nonempty):=by
  intro c hc;rw[mI,mS] at hc;rcases hc with rfl|rfl
  ·exact ie hS hf he
  ·exact ie hS l p
 have h1:=ak (f:=λw=>aS D w-1) h;rw[sum_pair r] at h1;unfold bu cd at m;omega
lemma fW (hG:bI G)(hS:aV n D)(m:bG n G D)(Bs:Finset (Fin n))(r:∀a∈Bs,∀b∈Bs,¬G a b){i:Fin n}(p:aU n D i.val (aO n D)):∃j s,j<D.length/\bf D j=true/\aU n D i.val (W D (j,!s))/\∀a∈Bs,(a∈O n D (W D (j,s))<->G i a):=by
 obtain ⟨j,s,hj,ht,-,l,h⟩:=j5 (G:=G) hS i (aO n D) p Bs
  (λS hS1 hS2=>by
   by_contra l;rw[bN] at l;rcases k9 hG ((m _).mp l) with ⟨a,ha,k⟩|⟨a,ha,b,hb,a0⟩
   ·exact hS2 a ha k
   ·exact r a (hS1 ha) b (hS1 hb) a0)
  (λa _ k=>by
   constructor
   ·exact (m _).mpr ⟨i,a,k,d7 i _,by simp[bs,bt]⟩
   ·by_contra l;rw[bN,iX] at l
    exact go hG a ((m _).mp l))
 exact ⟨j,s,hj,ht,l,h⟩
lemma iv (hG:bI G)(hS:aV n D)(hC:bG n G D)(Bs:Finset (Fin n))(a8:∀a∈Bs,∀b∈Bs,¬G a b){i j:Fin n}{w:Nat}(r:aU n D i.val w)(a4:fK n D w j.val)(l:∃a∈Bs,G j a/\¬G i a):∃k s,k<D.length/\bf D k=true/\n+k≤w/\aU n D i.val (W D (k,!s))/\∀a∈Bs,(a∈O n D (W D (k,s))<->G i a):=by
 classical
 have a7:¬cN G (bs i (bt (Bs.filter (λa=>¬G i a)))):=by
  intro hc;rcases k9 hG hc with ⟨a,ha,p⟩|⟨a,ha,b,hb,bm⟩
  ·exact (mF.mp ha).2 p
  ·exact a8 a (mF.mp ha).1 b (mF.mp hb).1 bm
 obtain ⟨a0,a3,a2,a1⟩:=l;have a5:cN G (bs j (bs i (bt (Bs.filter (λa=>¬G i a))))):=⟨j,a0,a2,d7 j _,by simp[bs,bt,a3,a1]⟩;have a6:=(gc hS hC _ j w a4 a7 a5).1;refine j5 hS i w r Bs (λS hS1 hS2=>?_) (λa _ p=>?_)
 ·by_contra hc;rw[bN] at hc;have h:=el hS (bs i (bt S))
   (bs i (bt (Bs.filter (λa=>¬G i a)))) (λk m=>by
    simp only[bs,bt,bO,dT] at m ⊢;rcases m with m|m
    ·exact oL m
    ·exact oR (mF.mpr ⟨hS1 m,hS2 k m⟩)) w hc
  rw[a6] at h;exact bF h
 ·have h2:=gc hS hC (bt {a}) i w (c9 hS r)
   (by rw[iX];exact go hG a)
   ⟨i,a,p,d7 i _,by simp[bs,bt]⟩
  exact ⟨h2.2,h2.1⟩
end SemPaths
def bX (i:F0):S0:=
 univ.filter (λa=>decide (a.val<7)≠decide (i.val<7))
def aX (i:F0):S0:=univ.filter (λa=>aH i a)
lemma oZ:∀a b:F0,aQ a b=true->decide (a.val<7)≠decide (b.val<7):=aa
lemma eg (i:F0):∀a∈bX i,∀b∈bX i,¬aH a b:=by
 intro a k b l h;simp only[bX,mF,mV,ae] at k l;have m:=oZ a b ((aK a b).mpr h);cases h2:decide (a.val<7)<;>cases h3:decide (b.val<7)<;>
  cases h4:decide (i.val<7)<;>simp_all
section SemDiff
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma gB {x y:Fin n}{w:Nat}:w∈bJ n D x y<->x∈O n D w/\y∉O n D w:=by simp only[bJ,mF,mR];exact ⟨λh=>h.2,λh=>⟨d4 h.1,h⟩⟩
lemma gl {x y:Fin n}{e:A0}:e∈bo n D (bJ n D x y)<->e.1<D.length/\(x∈O n D (W D e)/\y∉O n D (W D e))/\¬(x∈O n D (n+e.1)/\y∉O n D (n+e.1)):=by simp only[bo,bc,mF,mP,mR,mV,and_true,gB]
lemma kl (hS:aV n D)(b:Fin n->Nat)(hb:cn n D b){x y:Fin n}(a0:x≠y)(r:x∈aW n D):cd D (bJ n D x y)=1+((aR n D b).filter (λu=>x∈O n D u.1/\y∉O n D u.1)).card:=by
 have h1:cd D (bJ n D x y) =
   ((cq n D).filter (λu=>x∈O n D u.1/\y∉O n D u.1)).card:=by
  rw[iZ n D (λw=>x∈O n D w/\y∉O n D w)];symm;refine sum_subset (λw hw=>?_) (λw hw hnot=>?_)
  ·rw[mF] at hw;exact gB.mpr hw.2
  ·have a1:w∉bY n D:=λp=>hnot (mF.mpr ⟨p,gB.mp hw⟩);rw[cz] at a1;simp[gY hS w Y]
 have h2:(cq n D).filter (λu=>x∈O n D u.1/\y∉O n D u.1) =
   {(⟨b x,0⟩:P0)}∪(aR n D b).filter
    (λu=>x∈O n D u.1/\y∉O n D u.1):=by
  ext u;have k:=gL hS b hb;simp only[aR,dr,mU,mF,mD,mS];constructor
  ·intro h;by_cases hr:u∈dD n D b
   ·left;obtain ⟨v,hv,rfl⟩:=mM.mp hr;have l:=h.2.1;rw[(hb v hv).2,mS] at l;rw[l]
   ·exact oR ⟨⟨⟨h.1,⟨x,h.2.1⟩⟩,hr⟩,h.2⟩
  ·rintro (rfl|h)
   ·have m:=hb x r;refine ⟨(mF.mp (k (mM.mpr ⟨x,r,rfl⟩))).1,?_,?_⟩
    ·rw[m.2];exact mX x
    ·rw[m.2,mS];exact λp=>a0 p.symm
   ·exact ⟨h.1.1.1,h.2⟩
 have h3:(⟨b x,0⟩:P0)∉(aR n D b).filter
   (λu=>x∈O n D u.1/\y∉O n D u.1):=by
  intro p;exact (mD.mp (mF.mp p).1).2 (mM.mpr ⟨x,r,rfl⟩)
 rw[h1,h2,singleton_union,cI h3];omega
lemma lG (hS:aV n D){x y:Fin n}(a6:x≠y){w:Nat}(hw:x∈O n D w/\y∈O n D w):∃j s,j<D.length/\bf D j=false/\x∈O n D (n+j)/\y∈O n D (n+j)/\x∈O n D (W D (j,s))/\y∉O n D (W D (j,s))/\y∈O n D (W D (j,!s))/\x∉O n D (W D (j,!s)):=by
 classical
 have p:∃u,x∈O n D u/\y∈O n D u:=⟨w,hw⟩;obtain ⟨m,r⟩:=Nat.find_spec p;have h:∀u,u<Nat.find p->¬(x∈O n D u/\y∈O n D u):=λu hu=>Nat.find_min p hu;generalize Nat.find p=f at m r h;have a7:=d4 m;have hn:n≤f:=(by by_contra hc;have hs:O n D f={⟨f,Y⟩}:=du D ⟨f,Y⟩;rw[hs,mS] at m r;exact a6 (m.trans r.symm));obtain ⟨j,rfl⟩:∃j,f=n+j:=⟨f-n,Y⟩;have hj:j<D.length:=Y
 obtain ⟨ha,hb,-⟩:=hS j hj;have a1:=h _ ha;have a3:=h _ hb;cases ht:bf D j
 ·have a4:=m;have a0:=r;rw[eL hS hj ht,mU] at a4 a0;refine ⟨j,?_⟩;rcases a4 with a5|a2
  ·have l:y∉O n D (aZ D j):=λhc=>a1 ⟨a5,hc⟩;have k:y∈O n D (aY D j):=a0.resolve_left l;exact ⟨false,hj,ht,m,r,by simpa[W] using a5,by simpa[W] using l,by simpa[W] using k,by simpa[W] using λhc=>a3 ⟨hc,k⟩⟩
  ·have k:y∉O n D (aY D j):=λhc=>a3 ⟨a2,hc⟩;have l:y∈O n D (aZ D j):=a0.resolve_right k;exact ⟨true,hj,ht,m,r,by simpa[W] using a2,by simpa[W] using k,by simpa[W] using l,by simpa[W] using λhc=>a1 ⟨hc,l⟩⟩
 ·exfalso;rw[dC hS hj ht,mN] at m r;exact a1 ⟨m.1,r.1⟩
lemma jq (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:cn n D b){x c z:Fin n}(l:x≠c)(hx:x∈aW n D)(a4:∀u∈aR n D b,x∈O n D u.1->c∈O n D u.1){w:Nat}(hw:x∈O n D w/\c∈O n D w)(a6:G x z)(a2:¬G c z):cd D (bJ n D x c)=1/\bi n D (bJ n D x c)=∅/\(bo n D (bJ n D x c)).card=2/\∃e∈bo n D (bJ n D x c),bf D e.1=false/\c∈O n D (n+e.1):=by
 have hS:=h.1;have k:cd D (bJ n D x c)=1:=(by rw[kl hS b hb l hx,fE.mpr (λu m hc=>hc.2 (a4 u m hc.1)),ad]);have a7:=lQ h x c l
  (by rw[dV hG hC];exact nE x)
 rw[k] at a7;obtain ⟨j1,s1,b5,b6,bm,r,a5,p,-,-⟩:=lG hS l hw;have a1:(j1,s1)∈bo n D (bJ n D x c):=gl.mpr ⟨b5,⟨a5,p⟩,λhc=>hc.2 r⟩;have hA:∀u∈({c,z}:Finset (Fin n)),∀v∈({c,z}:Finset (Fin n)),¬G u v:=by
  intro u m v hv;simp only[mI,mS] at m hv;rcases m with m|m<;>rcases hv with hv|hv<;>rw[m,hv]
  ·exact hG.2.1 c
  ·exact a2
  ·exact λhc=>a2 (hG.1 _ _ hc)
  ·exact hG.2.1 z
 obtain ⟨j2,s2,b2,-,b1,a3,b0⟩:=fq hG hS hC {c,z} hA x ⟨z,ab,a6⟩;have a8:(j2,s2)∈bo n D (bJ n D x c):=gl.mpr ⟨b2,⟨b1,λhc=>dL.mp b0 hc ab⟩,λhc=>a3 hc.1⟩;have b8:(j1,s1)≠(j2,s2):=(by intro a0;rw[ay] at a0;exact a3 (a0.1▸bm));have h2:2≤(bo n D (bJ n D x c)).card:=oC.mpr ⟨_,a1,_,a8,b8⟩;exact ⟨k,cZ.mp Y,Y,(j1,s1),a1,b6,r⟩
lemma iY (hG:bI G)(p:aV n D)(hC:bG n G D){i:Fin n}{j:Nat}(hj:j<D.length)(s:Bool)(ht:bf D j=true)(l:aU n D i.val (W D (j,!s)))(hf:aS D (W D (j,!s))=1)(a0:n+j≤aO n D){a:Fin n}(a4:G i a):a∈O n D (W D (j,s)):=by
 have r:aU n D i.val (n+j):=rT l ⟨b4 hj (!s),hf⟩;have a2:val D (single a) (aO n D)=false:=(by by_contra hc;rw[bN] at hc;exact go hG a ((hC _).mp hc));have a5:val D (bs i (single a)) (aO n D)=true:=(hC _).mpr ⟨i,a,a4,d7 i _,by simp[bs,single]⟩;have a1:val D (bs i (single a)) (n+j)=true:=by
  by_contra h;rw[bT] at h;have a3:val D (single a) (n+j)=false:=(by by_contra m;rw[bN] at m;rw[el p _ _ (ia i _) _ m] at h;exact Bool.noConfusion h);have h2:=gW p _ _ i (eM i (single a)) (n+j) (aO n D)
   (ip p r a0) (a3.trans h.symm)
  rw[a2,a5] at h2;exact bF h2
 rw[cc p _ hj s,ht,gop_true,bA] at a1;have k:=kc p i hj s l hf _ _ (eM i (single a));rw[a1.1] at k;exact bD.mpr k
end SemDiff
def bq (n:Nat)(D:aJ)(P M:Finset (Fin n)):Prop:=∃w,O n D w∩P=M
def dk (n:Nat)(D:aJ)(P:Finset (Fin n)):Finset Nat:=
 (bi n D (ba n D P)).filter (λj=>2≤(O n D (n+j)∩P).card)
def dE (n:Nat)(D:aJ)(P U:Finset (Fin n))(f:Fin n)(e:A0):Prop:=
 e.1<D.length/\bf D e.1=true/\f∈P/\f∈O n D (W D e)/\
  f∉O n D (n+e.1)/\O n D (W D e)∩P⊆U/\(O n D (W D e)∩P).card≤2
def cM (n:Nat)(D:aJ)(P:Finset (Fin n))(e:A0):(A0)⊕Nat:=
 if O n D (n+e.1)∩P=∅ then Sum.inl e else Sum.inr e.1
def kJ (n:Nat)(D:aJ)(P:Finset (Fin n))(c:(A0)⊕Nat):Prop:=
 Sum.elim (λe=>e∈bo n D (ba n D P)/\(O n D (W D e)∩P).card≤2)
  (λj=>j∈bi n D (ba n D P)/\(O n D (n+j)∩P).card=1) c
section SupMask
variable {n : Nat} {D : aJ}
lemma jF (P:Finset (Fin n))(w:Nat):bq n D P (O n D w∩P):=⟨w,rfl⟩
lemma jB {P M:Finset (Fin n)}(h:bq n D P M):M⊆P:=by obtain ⟨w,rfl⟩:=h;exact iR
lemma dO {P:Finset (Fin n)}{w:Nat}:w∈ba n D P<->(O n D w∩P).Nonempty:=by
 simp only[ba,mF,mR];constructor
 ·exact λh=>h.2
 ·intro h;obtain ⟨v,k⟩:=h;exact ⟨d4 (mN.mp k).1,v,k⟩
lemma jU (p:aV n D){P M:Finset (Fin n)}(m:2≤M.card)(h:bq n D P M):∃j∈dk n D P,O n D (n+j)∩P=M:=by obtain ⟨w,r⟩:=h;obtain ⟨j,-,-,l,k,-,-⟩:=ga p P M m w r;exact ⟨j,mF.mpr ⟨k,by rw[l];exact m⟩,l⟩
lemma fy (p:aV n D)(P:Finset (Fin n))(F:Finset (Finset (Fin n)))(l:∀M∈F,2≤M.card/\bq n D P M):F.card≤(dk n D P).card:=by have h:F⊆(dk n D P).image (λj=>O n D (n+j)∩P):=(by intro M m;obtain ⟨j,r,k⟩:=jU p (l M m).1 (l M m).2;exact mM.mpr ⟨j,r,k⟩);exact (cL h).trans cG
lemma oW (hS:aV n D){P T:Finset (Fin n)}(hP:P.card≤7)(hT:T.card=3)(h:bq n D P T):(∃A,bq n D P A/\A.card=2/\A⊆T)\/(∃A,bq n D P A/\A.card=4/\T⊆A)\/(∃A B,A≠B/\bq n D P A/\bq n D P B/\A.card=5/\B.card=5/\T⊆A/\T⊆B/\A∩B=T):=by
 obtain ⟨w,hw⟩:=h;obtain ⟨j,hj,-,a5,-,-,a1⟩:=ga hS P T Y w hw;have k:bq n D P (O n D (aZ D j)∩P):=jF P _;have m:bq n D P (O n D (aY D j)∩P):=jF P _;rcases a1 with ⟨ht,p,r⟩|⟨-,p,r,a0,-,-⟩
 ·have l:(O n D (aZ D j)∩P)∩(O n D (aY D j)∩P)=T:=by
   rw[← a5,dC hS hj ht];ext v;simp only[mN];tauto
  generalize O n D (aZ D j)∩P=A at k p l;generalize O n D (aY D j)∩P=B at m r l;have a3:=al p;have a2:=al r;have hu:(A∪B).card≤7:=(cL (uS (jB k) (jB m))).trans hP;have a7:=cA A B;rw[l] at a7;by_cases h4:A.card=4
  ·exact oR (oL ⟨A,k,h4,p.subset⟩)
  by_cases a6:B.card=4
  ·exact oR (oL ⟨B,m,a6,r.subset⟩)
  refine oR (oR ⟨A,B,?_,k,m,Y,Y,p.subset,r.subset,l⟩);intro a4;rw[a4,inter_self] at l;rw[l] at a2;omega
 ·generalize O n D (aZ D j)∩P=A at k p a0;generalize O n D (aY D j)∩P=B at m r a0;have a3:=al p;have a2:=al r;have hc:=ao A B;rw[a0] at hc;by_cases h2:A.card=2
  ·exact oL ⟨A,k,h2,p.subset⟩
  ·exact oL ⟨B,m,Y,r.subset⟩
lemma mg {T T' A:Finset (Fin n)}(p:A.card=2)(m:A⊆T)(l:A⊆T')(h:T≠T'->(T∩T').card≤1):T=T':=by by_contra k;have h3:=cL (subset_inter m l);have r:=h k;omega
lemma mW {T T' A:Finset (Fin n)}(r:T.card=3)(p:T'.card=3)(hA:A.card=4)(m:T⊆A)(l:T'⊆A)(h:T≠T'->(T∩T').card≤1):T=T':=by by_contra k;have h3:=cL (uS m l);have h4:=cA T T';have h5:=h k;omega
lemma pQ {T1 T2 T3 A:Finset (Fin n)}(h1:T1.card=3)(h2:T2.card=3)(h3:T3.card=3)(hA:A.card≤5)(p:T1⊆A)(m:T2⊆A)(l:T3⊆A)(k:(T1∩T2).card≤1)(r:(T1∩T3).card≤1)(h:(T2∩T3).card≤1):False:=by have hu:=cL (uS (uS p m) l);have e1:=cA T1 T2;have e2:=cA (T1∪T2) T3;have e3:((T1∪T2)∩T3).card≤(T1∩T3).card+(T2∩T3).card:=(by rw[union_inter_distrib_right];exact ao _ _);omega
lemma oe (hS:aV n D){P:Finset (Fin n)}(hP:P.card≤7)(L:Finset (Finset (Fin n)))(h3:∀T∈L,T.card=3/\bq n D P T)(k:∀T∈L,∀T'∈L,T≠T'->(T∩T').card≤1):∃Aux:Finset (Finset (Fin n)),L.card≤Aux.card/\∀A∈Aux,bq n D P A/\((A.card=2/\∃T∈L,A⊆T)\/A.card=4\/A.card=5):=by
 classical
 refine ⟨P.powerset.filter (λA=>bq n D P A/\((A.card=2/\∃T∈L,A⊆T)\/A.card=4\/A.card=5)),?_,λA hA=>(mF.mp hA).2⟩;generalize hAux:P.powerset.filter (λA=>bq n D P A/\((A.card=2/\∃T∈L,A⊆T)\/A.card=4\/A.card=5))=Aux;have l:∀A,bq n D P A->((A.card=2/\∃T∈L,A⊆T)\/A.card=4\/A.card=5)->A∈Aux:=(by intro A h1 h2;rw[← hAux];exact mF.mpr ⟨mem_powerset.mpr (jB h1),h1,h2⟩);have a0:∀A∈Aux,(A.card=2/\∃T∈L,A⊆T)\/A.card=4\/A.card=5:=(by intro A hA;rw[← hAux] at hA;exact (mF.mp hA).2.2);have a4:∀T∈L,2≤∑ A∈Aux,(if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0)):=by
  intro T r;rcases oW hS hP (h3 T r).1 (h3 T r).2 with
   ⟨A,ho,hc,hs⟩|⟨A,ho,hc,hs⟩|⟨A,B,b8,a6,b1,a1,a2,b6,b0,-⟩
  ·refine lT ?_ (single_le_sum (λ_ _=>nZ _) (l A ho (oL ⟨hc,T,r,hs⟩)));simp[hc,hs]
  ·refine lT ?_ (single_le_sum (λ_ _=>nZ _) (l A ho (oR (oL hc))));simp[hc,hs]
  ·have a5:({A,B}:Finset (Finset (Fin n)))⊆Aux:=by
    intro x hx;rw[mI,mS] at hx;rcases hx with rfl|rfl
    ·exact l _ a6 (oR (oR a1))
    ·exact l _ b1 (oR (oR a2))
   refine lT ?_ (ak a5);rw[sum_pair b8];simp[a1,a2,b6,b0]
 have a3:∀A∈Aux,∑ T∈L,(if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0))≤2:=by
  intro A hA;by_cases h5:A.card=5
  ·have p:∑ T∈L,(if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0))=(L.filter (λT=>T⊆A)).card:=by
    rw[card_filter];exact sC rfl (λT _=>by simp[h5])
   rw[p];by_contra cb;obtain ⟨T1,T2,T3,m1,m2,m3,b2,b5,bm⟩:=two_lt_card_iff.mp (show 2<(L.filter (λT=>T⊆A)).card by omega);rw[mF] at m1 m2 m3;exact pQ (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
    (k _ m1.1 _ m2.1 b2) (k _ m1.1 _ m3.1 b5) (k _ m2.1 _ m3.1 bm)
  ·have p:∑ T∈L,(if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0)) =
     2*(L.filter (λT=>A⊆T\/T⊆A)).card:=by
    rw[card_filter,mul_sum];exact sC rfl (λT _=>by simp[h5])
   rw[p];have ca:(L.filter (λT=>A⊆T\/T⊆A)).card≤1:=by
    rw[cQ];intro T r T' m;rw[mF] at r m;have c3:=(h3 T r.1).1;have a7:=(h3 T' m.1).1;rcases a0 A hA with ⟨h2,-⟩|h4|a8
    ·have e1:A⊆T:=r.2.resolve_right (λh=>by
      have:=cL h;omega)
     have e2:A⊆T':=m.2.resolve_right (λh=>by
      have:=cL h;omega)
     exact mg h2 e1 e2 (k T r.1 T' m.1)
    ·have e1:T⊆A:=r.2.resolve_left (λh=>by
      have:=cL h;omega)
     have e2:T'⊆A:=m.2.resolve_left (λh=>by
      have:=cL h;omega)
     exact mW c3 a7 h4 e1 e2 (k T r.1 T' m.1)
    ·exact absurd a8 h5
   omega
 have h1:=card_nsmul_le_sum L _ 2 a4;have h2:=sum_le_card_nsmul Aux _ 2 a3;rw[sum_comm] at h1;simp only[az] at h1 h2;omega
lemma pZ (hS:aV n D){P:Finset (Fin n)}(hP:P.card≤7)(L:Finset (Finset (Fin n)))(m:∀T∈L,T.card=3/\bq n D P T)(l:∀T∈L,∀T'∈L,T≠T'->(T∩T').card≤1)(X:Finset (Finset (Fin n)))(hX:∀M∈X,bq n D P M/\2≤M.card/\M∉L/\M.card≠4/\M.card≠5/\(M.card=2->∀T∈L,¬M⊆T)):2*L.card+X.card≤(dk n D P).card:=by
 classical
 obtain ⟨Aux,a1,k⟩:=oe hS hP L m l;have a4:Disjoint L Aux:=(by rw[dL];intro T hT a2;have:=(m T hT).1;rcases (k T a2).2 with ⟨h,-⟩|h|h<;>omega);have p:Disjoint (L∪Aux) X:=by
  rw[dL];intro M hM a7;obtain ⟨-,-,a5,a0,a3,a6⟩:=hX M a7;rcases mU.mp hM with h|h
  ·exact a5 h
  ·rcases (k M h).2 with ⟨h2,T,hT,hs⟩|h4|h5
   ·exact a6 h2 T hT hs
   ·exact a0 h4
   ·exact a3 h5
 have r:=fy hS P ((L∪Aux)∪X) (by
  intro M hM;rcases mU.mp hM with h|h
  ·rcases mU.mp h with h|h
   ·exact ⟨by have:=(m M h).1;omega,(m M h).2⟩
   ·refine ⟨?_,(k M h).1⟩;rcases (k M h).2 with ⟨h,-⟩|h|h<;>omega
  ·exact ⟨(hX M h).2.1,(hX M h).1⟩)
 rw[cU p,cU a4] at r;omega
lemma j3 {G:Fin n->Fin n->Prop}(hG:bI G)(hS:aV n D)(hC:bG n G D){P U X:Finset (Fin n)}(r:U⊆P)(hU:U.card≤2\/(U.card=3/\¬bq n D P U))(hX:∀a∈X,∀b∈X,¬G a b)(a0:P \ U⊆X){f:Fin n}(hf:f∈U)(m:∃a∈X,G f a):∃e,dE n D P U f e:=by
 obtain ⟨j,s,hj,ht,h1,h2,hd⟩:=fq hG hS hC X hX f m;have k:O n D (W D (j,s))∩P⊆U:=(by intro v hv;rw[mN] at hv;by_contra p;exact dL.mp hd hv.1 (a0 (mD.mpr ⟨hv.2,p⟩)));refine ⟨(j,s),hj,ht,r hf,h1,h2,k,?_⟩;rcases hU with hU|⟨a2,l⟩
 ·exact (cL k).trans hU
 ·have a1:O n D (W D (j,s))∩P≠U:=λh=>l ⟨_,h⟩;have:=al (sU.mpr ⟨k,a1⟩);omega
lemma gZ (p:aV n D){P U:Finset (Fin n)}{f:Fin n}{e:A0}(h:dE n D P U f e):O n D (n+e.1)∩P⊆(O n D (W D e)∩P).erase f:=by obtain ⟨r,l,-,-,m,-,-⟩:=h;intro v k;rw[mN] at k;rw[mE,mN];exact ⟨λhvf=>m (hvf▸k.1),de p r l e.2 k.1,k.2⟩
lemma l6 {P U:Finset (Fin n)}{f:Fin n}{e:A0}(h:dE n D P U f e)(p:∀M,M⊆U->M.card=2->f∈M->¬bq n D P M):O n D (W D e)∩P={f}:=by obtain ⟨-,-,m,h1,-,k,hc⟩:=h;have l:f∈O n D (W D e)∩P:=mN.mpr ⟨h1,m⟩;have r:(O n D (W D e)∩P).card≠2:=λh2=>p _ k h2 l (jF P _);exact (eS (sS.mpr l) (by rw[cS];omega)).symm
lemma iN {P:Finset (Fin n)}{e k:A0}(h:cM n D P e=Sum.inl k):e=k/\O n D (n+e.1)∩P=∅:=by unfold cM at h;split_ifs at h with h0;exact ⟨Sum.inl.inj h,h0⟩
lemma kk {P:Finset (Fin n)}{e:A0}{j:Nat}(h:cM n D P e=Sum.inr j):e.1=j/\(O n D (n+e.1)∩P).Nonempty:=by unfold cM at h;split_ifs at h with h0;exact ⟨Sum.inr.inj h,nI.mpr h0⟩
lemma oQ (hS:aV n D){P U:Finset (Fin n)}{f:Fin n}{e:A0}(h:dE n D P U f e):kJ n D P (cM n D P e):=by
 have l:=gZ hS h;obtain ⟨r,ht,a1,h1,-,-,hc⟩:=h;have m:f∈O n D (W D e)∩P:=mN.mpr ⟨h1,a1⟩;unfold cM;split_ifs with h0
 ·show e∈bo n D (ba n D P)/\(O n D (W D e)∩P).card≤2;refine ⟨?_,hc⟩;rw[bo,mF];refine ⟨mP.mpr ⟨mR.mpr r,mV _⟩,dO.mpr ⟨f,m⟩,?_⟩;rw[dO,h0];exact nN
 ·show e.1∈bi n D (ba n D P)/\(O n D (n+e.1)∩P).card=1;have p:(O n D (n+e.1)∩P).Nonempty:=nI.mpr h0;have a0:=cL l;rw[cE m] at a0;have a2:=cO.mpr p;refine ⟨?_,Y⟩;obtain ⟨v,k⟩:=p;rw[mN] at k;have hA:=de hS r ht false k.1;have hB:=de hS r ht true k.1;rw[bP] at hA;rw[bU] at hB;rw[bi,mF,mR];exact ⟨r,dO.mpr ⟨v,mN.mpr k⟩,dO.mpr ⟨v,mN.mpr ⟨hA,k.2⟩⟩,dO.mpr ⟨v,mN.mpr ⟨hB,k.2⟩⟩⟩
lemma pf (hS:aV n D){P U U':Finset (Fin n)}{f m:Fin n}{e:A0}(h:dE n D P U f e)(r:dE n D P U' m e)(a1:(O n D (n+e.1)∩P).Nonempty):f=m:=by
 by_contra a0;obtain ⟨q,hq⟩:=a1;have p:=gZ hS h hq;have h2:=gZ hS r hq;rw[mE] at p h2;have l:({q,f,m}:Finset (Fin n))⊆O n D (W D e)∩P:=by
  intro x k;simp only[mI,mS] at k;rcases k with k|k|k<;>rw[k]
  ·exact p.2
  ·exact mN.mpr ⟨h.2.2.2.1,h.2.2.1⟩
  ·exact mN.mpr ⟨r.2.2.2.1,r.2.2.1⟩
 have hc:=cL l;have h3:({q,f,m}:Finset (Fin n)).card=3:=(by rw[cI,cP a0];simp only[mI,mS,nO];exact ⟨p.1,h2.1⟩);have:=h.2.2.2.2.2.2;omega
lemma lJ (hS:aV n D){P U U':Finset (Fin n)}{f p:Fin n}{e m:A0}(h:dE n D P U f e)(h':dE n D P U' p m)(hs:O n D (W D e)∩P={f})(r:f≠p):cM n D P e≠cM n D P m:=by intro l;have h0:O n D (n+e.1)∩P=∅:=(by have k:=gZ hS h;rw[hs,erase_singleton] at k;exact subset_empty.mp k);have hc:cM n D P e=Sum.inl e:=(by simp[cM,h0]);rw[hc] at l;have he:=(iN l.symm).1;subst he;have hm:p∈O n D (W D m)∩P:=mN.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩;rw[hs,mS] at hm;exact r hm.symm
lemma oJ (hS:aV n D){P:Finset (Fin n)}(Lab:Finset (Fin n))(U:Fin n->Finset (Fin n))(h:Fin n->A0)(k:∀f∈Lab,dE n D P (U f) f (h f))(c:(A0)⊕Nat):(Lab.filter (λf=>cM n D P (h f)=c)).card≤2:=by
 rcases c with e0|j0
 ·by_cases a0:(Lab.filter (λf=>cM n D P (h f)=Sum.inl e0)).Nonempty
  ·obtain ⟨f0,r⟩:=a0;rw[mF] at r;have l:=(k f0 r.1).2.2.2.2.2.2;rw[(iN r.2).1] at l;refine lT (cL ?_) l;intro f m;rw[mF] at m;have hw:=k f m.1;rw[(iN m.2).1] at hw;exact mN.mpr ⟨hw.2.2.2.1,hw.2.2.1⟩
  ·rw[not_nonempty_iff_eq_empty] at a0;rw[a0];simp
 ·have a1:iO (λf=>(h f).2)
    (Lab.filter (λf=>cM n D P (h f)=Sum.inr j0):Set (Fin n)):=by
   intro f m f' p hs;rw[mem_coe,mF] at m p;obtain ⟨h1,a4⟩:=kk m.2;obtain ⟨a6,-⟩:=kk p.2;have a5:h f=h f':=pE (h1.trans a6.symm) hs;have a2:=k f' p.1;rw[← a5] at a2;exact pf hS (k f m.1) a2 a4
  have a3:=card_le_card_of_injOn (t:=(univ:Finset Bool))
   (λf=>(h f).2) (λ_ _=>mV _) a1
  simpa using a3
lemma po (hS:aV n D){P:Finset (Fin n)}(Lab:Finset (Fin n))(U:Fin n->Finset (Fin n))(wit:Fin n->A0)(hwit:∀f∈Lab,dE n D P (U f) f (wit f)):Lab.card≤2*(Lab.image (λf=>cM n D P (wit f))).card:=
 card_le_mul_card_image Lab 2 (λc _=>oJ hS Lab U wit hwit c)
lemma pM (hS:aV n D){P:Finset (Fin n)}(Lab S:Finset (Fin n))(U:Fin n->Finset (Fin n))(k:Fin n->A0)(l:∀f∈Lab,dE n D P (U f) f (k f))(r:S⊆Lab)(p:∀f∈S,O n D (W D (k f))∩P={f}):2*S.card+(Lab \ S).card≤2*(Lab.image (λf=>cM n D P (k f))).card:=by
 have h1:(S.image (λf=>cM n D P (k f))).card=S.card:=cJ (λf hf f' m a0=>by
   by_contra a3
   exact lJ hS (l f (r hf)) (l f' (r m)) (p f hf) a3 a0)
 have h2:=po hS (Lab \ S) U k (λf hf=>l f (mD.mp hf).1);have hd:Disjoint (S.image (λf=>cM n D P (k f)))
   ((Lab \ S).image (λf=>cM n D P (k f))):=by
  rw[dL];intro c a1 a2;obtain ⟨f,hf,rfl⟩:=mM.mp a1;obtain ⟨f',m,a0⟩:=mM.mp a2;rw[mD] at m;exact lJ hS (l f (r hf)) (l f' m.1) (p f hf)
   (λh=>m.2 (h▸hf)) a0.symm
 have h3:(S.image (λf=>cM n D P (k f))∪(Lab \ S).image (λf=>cM n D P (k f))).card≤
   (Lab.image (λf=>cM n D P (k f))).card:=
  cL (uS (image_subset_image r) (image_subset_image sdiff_subset))
 rw[cU hd,h1] at h3;omega
lemma pR (P:Finset (Fin n))(E:Finset (A0))(hE:∀e∈E,e∈bo n D (ba n D P)/\3≤(O n D (W D e)∩P).card)(C:Finset ((A0)⊕Nat))(p:∀c∈C,kJ n D P c):(dk n D P).card+E.card+C.card≤(bo n D (ba n D P)).card+(bi n D (ba n D P)).card:=by
 have r:∀e∈C.toLeft,e∈bo n D (ba n D P)/\(O n D (W D e)∩P).card≤2:=λe he=>p _ (mem_toLeft.mp he);have m:∀j∈C.toRight,j∈bi n D (ba n D P)/\(O n D (n+j)∩P).card=1:=λj hj=>p _ (mem_toRight.mp hj);have l:E.card+C.toLeft.card≤(bo n D (ba n D P)).card:=by
  rw[← cU]
  ·refine cL (λe he=>?_);rcases mU.mp he with h|h
   ·exact (hE e h).1
   ·exact (r e h).1
  ·rw[dL];intro e l k;have a:=(hE e l).2;have b:=(r e k).2;omega
 have k:(dk n D P).card+C.toRight.card≤(bi n D (ba n D P)).card:=by
  rw[← cU]
  ·refine cL (λj hj=>?_);rcases mU.mp hj with h|h
   ·exact (mF.mp h).1
   ·exact (m j h).1
  ·rw[dL];intro j l k;have a:=(mF.mp l).2;have b:=(m j k).2;omega
 have h3:=card_toLeft_add_card_toRight (u:=C);omega
lemma m0 (p:aV n D)(P:Finset (Fin n))(E:Finset (A0))(hE:∀e∈E,e∈bo n D (ba n D P)/\3≤(O n D (W D e)∩P).card)(Lab S:Finset (Fin n))(U:Fin n->Finset (Fin n))(h:Fin n->A0)(k:∀f∈Lab,dE n D P (U f) f (h f))(m:S⊆Lab)(l:∀f∈S,O n D (W D (h f))∩P={f}):2*((dk n D P).card+E.card)+2*S.card+(Lab \ S).card≤2*((bo n D (ba n D P)).card+(bi n D (ba n D P)).card):=by
 have h1:=pM p Lab S U h k m l
 have h2:=pR P E hE (Lab.image (λf=>cM n D P (h f))) (by
  intro c hc;obtain ⟨f,r,rfl⟩:=mM.mp hc
  exact oQ p (k f r))
 omega
lemma nQ {G:Fin n->Fin n->Prop}(hG:bI G)(h:a9 n D)(hC:bG n G D)(P I:Finset (Fin n))(hI:∀i∈I,i∈aN n D/\∃N:Finset (Fin n),N⊆P/\3≤N.card/\∀a∈N,G i a):∃E:Finset (A0),E.card=I.card/\∀e∈E,e∈bo n D (ba n D P)/\3≤(O n D (W D e)∩P).card:=by
 classical
 have a2:∀i:Fin n,∃e:A0,i∈I->e.1<D.length/\O n D (W D e)={i}/\O n D (n+e.1)=∅/\∀a,G i a->a∈O n D (W D (e.1,!e.2)):=by
  intro i;by_cases k:i∈I
  ·obtain ⟨e,p,-,h3,h4,h5,-,-⟩:=eJ hG h hC (hI i k).1;exact ⟨e,λ_=>⟨p,h3,h4,h5⟩⟩
  ·exact ⟨(0,false),λhc=>absurd hc k⟩
 choose g hg using a2
 refine ⟨I.image (λi=>((g i).1,!(g i).2)),?_,?_⟩
 ·refine cJ (λi k i' hi' heq=>?_);rw[ay,Bool.not_inj_iff] at heq;have he:g i=g i':=pE heq.1 heq.2;have p:=(hg i k).2.1;rw[he,(hg i' hi').2.1] at p;exact (sJ p).symm
 ·intro e he;obtain ⟨i,k,rfl⟩:=mM.mp he;obtain ⟨hj,-,m,r⟩:=hg i k;obtain ⟨N,a0,a3,a1⟩:=(hI i k).2;have l:N⊆O n D (W D ((g i).1,!(g i).2))∩P:=λa ha=>mN.mpr ⟨r a (a1 a ha),a0 ha⟩;have hc:=cL l;refine ⟨?_,Y⟩;rw[bo,mF];refine ⟨mP.mpr ⟨mR.mpr hj,mV _⟩,dO.mpr (cO.mp Y),?_⟩;rw[dO,m,eI];exact nN
end SupMask
lemma gP (u v:F0)(h:u≠v)(P:S0):((univ.filter (λz=>aH u z)∩P)∩(univ.filter (λz=>aH v z)∩P)).card≤1:=by refine lT (cL (λz hz=>?_)) (nF u v h);simp only[mN,mF,mV,ae] at hz;exact mF.mpr ⟨mV z,hz.1.1,hz.2.1⟩
def fP (u v:Fin 10):Bool:=
 (([112,400,672,832,3,5,9,6,10,12]:List Nat).getD u.val 0).testBit v.val
abbrev eZ (u v:Fin 10):Prop:=fP u v=true
lemma fR:bI eZ:=
 ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
section K4Generic
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma nd {T:Finset (Fin n)}{w:Nat}:w∈ba n D T<->(O n D w∩T).Nonempty:=by simp only[ba,mF,mR,and_iff_right_iff_imp];rintro ⟨v,h⟩;exact d4 (mN.mp h).1
lemma e6 {T:Finset (Fin n)}{e:A0}:e∈bo n D (ba n D T)<->e.1<D.length/\(O n D (W D e)∩T).Nonempty/\¬(O n D (n+e.1)∩T).Nonempty:=by simp only[bo,bc,mF,mP,mR,mV,and_true,nd]
def ch (n:Nat)(G:Fin n->Fin n->Prop)(D:aJ)(pos:Fin n->A0):Prop:=
 (∀i∈aN n D,(pos i).1<D.length/\O n D (n+(pos i).1)=∅/\
  (∀a,G i a->a∈O n D (W D (pos i)))/\
  O n D (W D ((pos i).1,!(pos i).2))={i})/\
 ∀i∈aN n D,∀i'∈aN n D,pos i=pos i'->i=i'
lemma cR (hG:bI G)(h:a9 n D)(p:bG n G D):∃pos:Fin n->A0,ch n G D pos:=by
 classical
 have m:∀i:Fin n,∃e:A0,i∈aN n D->(e.1<D.length/\O n D (n+e.1)=∅/\(∀a,G i a->a∈O n D (W D e))/\O n D (W D (e.1,!e.2))={i}):=by
  intro i;by_cases k:i∈aN n D
  ·obtain ⟨e,l,-,r,h4,h5,-,-⟩:=eJ hG h p k;exact ⟨(e.1,!e.2),λ_=>⟨l,h4,h5,by simpa using r⟩⟩
  ·exact ⟨(0,false),λhc=>absurd hc k⟩
 choose pos hpos using m
 refine ⟨pos,hpos,λi k i' hi' he=>?_⟩;have l:=(hpos i k).2.2.2;rw[he,(hpos i' hi').2.2.2] at l;exact (sJ l).symm
lemma mq {h:Fin n->A0}(k:ch n G D h){i a:Fin n}{T:Finset (Fin n)}(p:i∈aN n D)(l:G i a)(m:a∈T):h i∈bo n D (ba n D T):=by obtain ⟨h1,r,h3,-⟩:=k.1 i p;rw[e6];refine ⟨h1,⟨a,mN.mpr ⟨h3 a l,m⟩⟩,?_⟩;rw[r,eI];exact nN
lemma gh {k:Fin n->A0}(h:ch n G D k)(T J:Finset (Fin n))(l:∀i∈J,i∈aN n D/\∃a∈T,G i a):J.image k⊆bo n D (ba n D T)/\(J.image k).card=J.card:=by
 constructor
 ·intro e he;obtain ⟨i,m,rfl⟩:=mM.mp he;obtain ⟨r,a,p,a0⟩:=l i m;exact mq h r a0 p
 ·exact cJ
   (λi m i' hi' he=>h.2 i (l i m).1 i' (l i' hi').1 he)
lemma ol (l:bI G)(h:a9 n D)(k:bG n G D)(b:Fin n->Nat)(m:cn n D b)(T:Finset (Fin n)):(bo n D (ba n D T)).card+(bi n D (ba n D T)).card+(aW n D).card≤2*T.card+br n D:=by have r:=d9 h T (by rw[dV l k,eI]);have p:=eN h.1 b m T;have h3:=cL (iL:T∩aW n D⊆T);omega
lemma jI (l:aV n D)(T:Finset (Fin n))(w:Nat)(k:2≤(O n D w∩T).card):∃j∈bi n D (ba n D T),O n D (n+j)∩T=O n D w∩T:=by obtain ⟨j,-,-,h,m,-,-⟩:=ga l T _ k w rfl;exact ⟨j,m,h⟩
lemma ic (hS:aV n D){T:Finset (Fin n)}(hT:T.card=3){a b c:Fin n}(ha:a∈T)(hb:b∈T)(hc:c∈T)(a3:a≠b)(a5:a≠c)(a7:b≠c){h l:Nat}(b0:a∈O n D h)(b8:b∈O n D h)(bm:a∈O n D l)(ca:c∈O n D l):2≤(bi n D (ba n D T)).card:=by
 have r:a∈O n D h∩T:=mN.mpr ⟨b0,ha⟩;have a2:b∈O n D h∩T:=mN.mpr ⟨b8,hb⟩;have a6:a∈O n D l∩T:=mN.mpr ⟨bm,ha⟩;have a0:c∈O n D l∩T:=mN.mpr ⟨ca,hc⟩;have c1:2≤(O n D h∩T).card:=oC.mpr ⟨a,r,b,a2,a3⟩;have c2:2≤(O n D l∩T).card:=oC.mpr ⟨a,a6,c,a0,a5⟩;obtain ⟨j1,b6,e1⟩:=jI hS T h c1;by_cases a1:O n D h∩T=O n D l∩T
 ·have k:O n D h∩T=T:=by
   refine eS iR ?_;rw[hT];exact two_lt_card.mpr
    ⟨a,r,b,a2,c,by rw[a1];exact a0,a3,a5,a7⟩
  obtain ⟨j,-,-,h3,h4,-,p⟩:=ga hS T T Y h k;rcases p with ⟨-,hA,-⟩|⟨-,hA,hB,hU,-,-⟩
  ·exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA iR).ne
  ·have a8:3≤(O n D (aZ D j)∩T).card+(O n D (aY D j)∩T).card:=by
    have:=ao (O n D (aZ D j)∩T) (O n D (aY D j)∩T);rw[hU,hT] at this;exact this
   have a4:∀w,O n D w∩T ⊂ T->2≤(O n D w∩T).card->2≤(bi n D (ba n D T)).card:=(by intro w b1 m;obtain ⟨j',b2,e'⟩:=jI hS T w m;refine oC.mpr ⟨j,h4,j',b2,λhjj=>?_⟩;rw[hjj,e'] at h3;exact b1.ne h3);by_cases m:2≤(O n D (aZ D j)∩T).card
   ·exact a4 _ hA m
   ·exact a4 _ hB Y
 ·obtain ⟨j2,b5,e2⟩:=jI hS T l c2;exact oC.mpr ⟨j1,b6,j2,b5,λhjj=>a1 (by rw[← e1,← e2,hjj])⟩
end K4Generic
lemma pH:∀I:Finset (Fin 10),(∀u∈I,∀v∈I,fP u v=false)->5≤I.card->(∀q∈I,4≤q.val)/\((4∈I/\5∈I)\/(4∈I/\7∈I)\/(5∈I/\7∈I)):=aa
lemma od:∀i:Fin 10,4≤ i.val->∃a∈({0,1,2}:Finset (Fin 10)),eZ i a:=aa
lemma ma {D:aJ}(h:a9 10 D)(p:bG 10 eZ D):∀u∈aN 10 D,∀v∈aN 10 D,fP u v=false:=by
 intro u m v r;by_contra l;rw[bN] at l;rcases ij fR h p (u:=u) (v:=v) l with k|k
 ·exact cl.mp m k
 ·exact cl.mp r k
lemma kM {D:aJ}(h:a9 10 D)(hC:bG 10 eZ D):6≤br 10 D:=by
 by_contra a6;obtain ⟨b,hb⟩:=kO fR h.1 hC;have hp:=iD h.1 b hb;have a0:=db 10 D;obtain ⟨a1,k⟩:=pH _ (ma h hC) Y;obtain ⟨a2,l⟩:=cR fR h hC;have a4:=ol fR h hC b hb ({0,1,2}:Finset (Fin 10));obtain ⟨p,a5⟩:=gh l ({0,1,2}:Finset (Fin 10)) (aN 10 D)
  (λi hi=>⟨hi,od i (a1 i hi)⟩)
 have a7:=cL p;have hT:({0,1,2}:Finset (Fin 10)).card=3:=o
 have q:∀i∈aN 10 D,∀a,eZ i a->a∈O 10 D (W D (a2 i)):=λi hi=>(l.1 i hi).2.2.1;have a3:2≤(bi 10 D (ba 10 D ({0,1,2}:Finset (Fin 10)))).card:=by
  rcases k with ⟨i4,r⟩|⟨i4,m⟩|⟨r,m⟩
  ·exact ic h.1 hT (a:=0) (b:=1) (c:=2) o o
    o o o o (q 4 i4 0 o)
    (q 4 i4 1 o) (q 5 r 0 o) (q 5 r 2 o)
  ·exact ic h.1 hT (a:=1) (b:=0) (c:=2) o o
    o o o o (q 4 i4 1 o)
    (q 4 i4 0 o) (q 7 m 1 o) (q 7 m 2 o)
  ·exact ic h.1 hT (a:=2) (b:=0) (c:=1) o o
    o o o o (q 5 r 2 o)
    (q 5 r 0 o) (q 7 m 2 o) (q 7 m 1 o)
 omega
def cj {n m:Nat}(ρ:Fin n->Option Bool)(ι:Fin m->Fin n)(y:Fin m->Bool):Fin n->Bool:=
 λv=>(ρ v).getD (decide (∃i:Fin m,ι i=v/\y i=true))
def dA {n m:Nat}(ρ:Fin n->Option Bool)(ι:Fin m->Fin n):Prop:=
 fI ι/\∀v,ρ v=none<->∃i,ι i=v
lemma eK {n m:Nat}{ρ:Fin n->Option Bool}{ι:Fin m->Fin n}(k:dA ρ ι)(y:Fin m->Bool)(i:Fin m):cj ρ ι y (ι i)=y i:=by
 have h:ρ (ι i)=none:=(k.2 _).mpr ⟨i,rfl⟩;unfold cj;rw[h,Option.getD_none];by_cases l:y i=true
 ·rw[l,dT];exact ⟨i,rfl,l⟩
 ·rw[bT] at l;rw[l,decide_eq_false_iff_not];rintro ⟨i',r,p⟩;rw[k.1 r,l] at p;exact bF p
lemma eo {n m:Nat}{ρ:Fin n->Option Bool}(ι:Fin m->Fin n)(y:Fin m->Bool){v:Fin n}{b:Bool}(h:ρ v=some b):cj ρ ι y v=b:=by unfold cj;rw[h,Option.getD_some]
lemma lg {n m:Nat}{ρ:Fin n->Option Bool}{ι:Fin m->Fin n}(l:dA ρ ι){y p:Fin m->Bool}{i:Fin m}(h:∀k,k≠i->y k=p k):∀v,v≠ι i->cj ρ ι y v=cj ρ ι p v:=by
 intro v r;cases hr:ρ v with
 | some b=>rw[eo ι y hr,eo ι p hr]
 | none=>
  obtain ⟨k,rfl⟩:=(l.2 v).mp hr;rw[eK l,eK l];exact h k (λhc=>r (by rw[hc]))
lemma kz {n:Nat}{D:aJ}(h:aV n D){j:Nat}(k:j<D.length)(s:Bool)(x:Fin n->Bool):val D x (n+j)=dm (bf D j) (val D x (W D (j,s))) (val D x (W D (j,!s))):=by
 rw[cu h x j k];cases s
 ·simp[W]
 ·cases bf D j<;>simp[W,bC,bR]
lemma pt (f:Nat->Nat)(K:Finset Nat)(h:∀w∈K,1≤f w):∑ w∈K,(f w-1)+K.card=∑ w∈K,f w:=by rw[card_eq_sum_ones,← sD];exact sC rfl (λw hw=>Nat.sub_add_cancel (h w hw))
lemma jZ (E:aJ)(g:Bool×Nat×Nat):aZ (E++[g]) E.length=g.2.1/\aY (E++[g]) E.length=g.2.2/\bf (E++[g]) E.length=g.1/\∀i,i<E.length->aZ (E++[g]) i=aZ E i/\aY (E++[g]) i=aY E i:=by
 refine ⟨?_,?_,?_,λi hi=>?_⟩
 ·unfold aZ;rw[it]
 ·unfold aY;rw[it]
 ·unfold bf;rw[it]
 ·unfold aZ aY;rw[lW E [g] i hi];exact ⟨rfl,rfl⟩
lemma j7 {m:Nat}{E:aJ}{g:Bool×Nat×Nat}(p:aV m (E++[g]))(y:Fin m->Bool):(∀w,w<m+E.length->val (E++[g]) y w=val E y w)/\val (E++[g]) y (m+E.length)=dm g.1 (val E y g.2.1) (val E y g.2.2):=by
 have k:∀w,w<m+E.length->val (E++[g]) y w=val E y w:=(by intro w hw;have h:=pK (E++[g]) y E.length w hw ab;rw[← h];simp);refine ⟨k,?_⟩;have l:E.length<(E++[g]).length:=ab
 obtain ⟨ha,r,-⟩:=p E.length l;obtain ⟨e1,e2,e3,-⟩:=jZ E g;rw[cu p y E.length l,e3];rw[e1] at ha;rw[e2] at r;rw[e1,e2,k _ ha,k _ r]
noncomputable section CofRestrict
open Classical
variable {n m : Nat} (D : aJ) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n)
def dR (w:Nat):Prop:=
 ∀y y':Fin m->Bool,val D (cj ρ ι y) w=val D (cj ρ ι y') w
def bg (w:Nat):Prop:=
 ¬dR D ρ ι w/\
  rG (λa b=>bk n D a b/\¬dR D ρ ι b) w (aO n D)
def cy (w:Nat):Nat:=((bL D w).filter (λj=>bg D ρ ι (n+j))).card
def eC (w:Nat):Finset (Fin m):=
 univ.filter (λi=>val D (cj ρ ι (single i)) w=true)
def gu:Nat:=∑ w∈(bY n D).filter (λw=>bg D ρ ι w),(cy D ρ ι w-1)
def gw:Nat:=
 ∑ w∈(bY n D).filter (λw=>bg D ρ ι w/\(eC D ρ ι w).Nonempty),
  (cy D ρ ι w-1)
def d8 (t:Nat->Nat)(e:Nat):Finset Nat:=
 (range (n+D.length)).filter (λw=>bg D ρ ι w/\t w=e)
variable {D ρ ι}
lemma kQ {w:Nat}{i:Fin m}:i∈eC D ρ ι w<->val D (cj ρ ι (single i)) w=true:=by simp[eC]
lemma fL {w:Nat}(h:bg D ρ ι w):w<n+D.length:=by by_contra k;exact h.1 (λy y'=>by rw[dS D _ w Y,dS D _ w Y])
lemma jt {a c:Nat}(hs:bk n D a c)(ha:¬dR D ρ ι a)(hc:bg D ρ ι c):bg D ρ ι a:=
 ⟨ha,rH ⟨hs,hc.1⟩ hc.2⟩
lemma j6 {w:Nat}(h:bg D ρ ι w)(p:w≠aO n D):∃c,bk n D w c/\bg D ρ ι c:=by
 rcases cH h.2 with l|⟨c,r,k⟩
 ·exact absurd l p
 ·exact ⟨c,r.1,r.2,k⟩
lemma lr (w:Nat):cy D ρ ι w≤aS D w:=cF _ _
lemma na {w:Nat}(h:bg D ρ ι w)(k:w≠aO n D):1≤cy D ρ ι w:=by obtain ⟨c,l,p⟩:=j6 h k;refine cO.mpr ⟨c-n,mF.mpr ⟨fV l,?_⟩⟩;rw[Nat.add_sub_cancel' l.2.1];exact p
lemma ni (k:aV n D){c:Fin n}(h:ρ c=some true){w:Nat}(l:c∈O n D w):dR D ρ ι w:=by intro y p;rw[cf k l (eo ι y h),cf k l (eo ι p h)]
lemma lm (hS:aV n D){c:Fin n}(hc:ρ c=some true){w:Nat}(hw:c∈O n D w):¬bg D ρ ι w:=
 λh=>h.1 (ni hS hc hw)
lemma f8 (h:dA ρ ι){w:Nat}(k:w<n)(p:bg D ρ ι w):∃i:Fin m,(ι i).val=w:=by
 cases hr:ρ ⟨w,k⟩ with
 | some b=>
  exact absurd (λy y'=>by
   rw[ck D _ w k,ck D _ w k,eo ι y hr,eo ι y' hr]) p.1
 | none=>
  obtain ⟨i,l⟩:=(h.2 _).mp hr;exact ⟨i,by rw[l]⟩
lemma ov (hS:aV n D)(l:dA ρ ι)(i:Fin m)(p:∃y y':Fin m->Bool,(∀k,k≠i->y k=y' k)/\val D (cj ρ ι y) (aO n D)≠val D (cj ρ ι y') (aO n D)):bg D ρ ι (ι i).val:=by
 obtain ⟨y,y',a0,a1⟩:=p;have hp:=gt hS _ _ (ι i) (lg l a0) _ a1;refine ⟨λhc=>a1 ?_,dt (λa b h=>⟨h.1,λhc=>h.2 (hc y y')⟩) hp⟩;have h1:=hc y y';rw[ck D _ _ (ι i).isLt,ck D _ _ (ι i).isLt,Fin.eta,eK l,eK l] at h1;have r:y=y':=by
  funext k;by_cases hk:k=i
  ·rw[hk];exact h1
  ·exact a0 k hk
 rw[r]
lemma pW (k:aV n D){j:Nat}(l:j<D.length)(p:dR D ρ ι (aZ D j))(r:dR D ρ ι (aY D j)):dR D ρ ι (n+j):=by intro y h;rw[cu k _ j l,cu k _ j l,p y h,r y h]
lemma lh (r:aV n D){j:Nat}(k:j<D.length)(h:bg D ρ ι (n+j)):∃s,bg D ρ ι (W D (j,s)):=by
 by_cases l:dR D ρ ι (aZ D j)
 ·by_cases p:dR D ρ ι (aY D j)
  ·exact absurd (pW r k l p) h.1
  ·exact ⟨true,jt (b4 k true) (by rw[bU];exact p) h⟩
 ·exact ⟨false,jt (b4 k false) (by rw[bP];exact l) h⟩
lemma pk (r:aV n D){j:Nat}(hj:j<D.length)(s:Bool)(hc:dR D ρ ι (W D (j,!s)))(p:¬dR D ρ ι (n+j)):∀y,val D (cj ρ ι y) (n+j)=val D (cj ρ ι y) (W D (j,s)):=by
 intro y;have h:∀y',val D (cj ρ ι y') (n+j)=dm (bf D j)
   (val D (cj ρ ι y') (W D (j,s))) (val D (cj ρ ι y) (W D (j,!s))):=
  λy'=>by rw[kz r hj s,hc y' y]
 rw[h y];cases ht:bf D j<;>cases hv:val D (cj ρ ι y) (W D (j,!s))
 ·simp
 ·exfalso;apply p;intro l k;rw[h l,h k,ht,hv];simp
 ·exfalso;apply p;intro l k;rw[h l,h k,ht,hv];simp
 ·simp
def dK (D:aJ)(ρ:Fin n->Option Bool)(ι:Fin m->Fin n)(k:Nat)(E:aJ)(t q:Nat->Nat):Prop:=
 aV m E/\
 (∀w,w<n+k->bg D ρ ι w->
  t w<m+E.length/\∀y,val E y (t w)=val D (cj ρ ι y) w)/\
 (∀i,i<E.length->q i<k/\bg D ρ ι (n+q i)/\t (n+q i)=m+i/\
  aZ E i=t (aZ D (q i))/\aY E i=t (aY D (q i))/\
  bg D ρ ι (aZ D (q i))/\bg D ρ ι (aY D (q i)))/\
 (∀j,j<k->bg D ρ ι (n+j)->(∃i,i<E.length/\q i=j)\/
  ∀s,bg D ρ ι (W D (j,s))->t (W D (j,s))=t (n+j))/\
 (∀i:Fin m,t (ι i).val=i.val)
lemma oB (l:dA ρ ι):∃E t q,dK D ρ ι 0 E t q:=by
 have a1:∀w:Nat,∃r:Nat,∀i:Fin m,(ι i).val=w->r=i.val:=by
  intro w;by_cases h:∃i:Fin m,(ι i).val=w
  ·obtain ⟨i,k⟩:=h;exact ⟨i.val,λi' hi'=>by rw[l.1 (Fin.ext (k.trans hi'.symm))]⟩
  ·exact ⟨0,λi k=>absurd ⟨i,k⟩ h⟩
 choose t ht using a1
 refine ⟨[],t,λ_=>0,λj hj=>absurd hj ab,?_,λi k=>absurd k ab,λj hj=>absurd hj ab,λi=>ht _ i rfl⟩;intro w p hl;rw[Nat.add_zero] at p;obtain ⟨i,k⟩:=f8 l p hl;have e:=ht w i k;have a0:(⟨w,p⟩:Fin n)=ι i:=Fin.ext k.symm;refine ⟨by rw[e];simp,λy=>?_⟩;rw[e,ck [] y i.val i.isLt,ck D _ w p,a0,eK l]
lemma nr (hS:aV n D){k:Nat}(hk:k<D.length){E:aJ}{t q:Nat->Nat}(h:dK D ρ ι k E t q):∃E' t' q',dK D ρ ι (k+1) E' t' q':=by
 obtain ⟨h1,h2,h3,h4,h5⟩:=h;obtain ⟨hA,hB,-⟩:=hS k hk;by_cases hl:bg D ρ ι (n+k)
 swap
 ·refine ⟨E,t,q,h1,λw hw hlw=>?_,λi hi=>?_,λj hj hlj=>?_,h5⟩
  ·have a0:w≠n+k:=λhc=>hl (hc▸hlw);exact h2 w Y hlw
  ·obtain ⟨a,b⟩:=h3 i hi;exact ⟨Y,b⟩
  ·have a0:j≠k:=λhc=>hl (hc▸hlj);exact h4 j Y hlj
 have l:∀(v:Nat) (w:Nat),w<n+k->Function.update t (n+k) v w=t w:=λv w hw=>Function.update_of_ne Y _ _;by_cases hc:bg D ρ ι (aZ D k)/\bg D ρ ι (aY D k)/\t (aZ D k)≠t (aY D k)
 ·obtain ⟨la,lb,a0⟩:=hc;obtain ⟨ta,va⟩:=h2 _ hA la;obtain ⟨tb,vb⟩:=h2 _ hB lb;have b6:aV m (E++[(bf D k,t (aZ D k),t (aY D k))]):=mj h1 _ _ _ ta tb a0;obtain ⟨e1,e2,-,e4⟩:=jZ E (bf D k,t (aZ D k),t (aY D k));have bm:(E++[(bf D k,t (aZ D k),t (aY D k))]).length=E.length+1:=ab
  refine ⟨_,Function.update t (n+k) (m+E.length),Function.update q E.length k,b6,λw hw hlw=>?_,λi hi=>?_,λj hj hlj=>?_,λi=>?_⟩
  ·rw[bm];by_cases b2:w=n+k
   ·rw[b2,Function.update_self];refine ⟨Y,λy=>?_⟩;rw[(j7 b6 y).2,va y,vb y,cu hS _ k hk]
   ·obtain ⟨tw,vw⟩:=h2 w Y hlw;rw[l _ w Y];exact ⟨Y,λy=>by rw[(j7 b6 y).1 _ tw,vw y]⟩
  ·rw[bm] at hi;by_cases b1:i<E.length
   ·obtain ⟨a1,a2,a3,a4,a5,a6,a7⟩:=h3 i b1;obtain ⟨sa,sb,-⟩:=hS (q i) Y;rw[Function.update_of_ne (by omega:i≠E.length),l _ _ (by omega:n+q i<n+k),l _ _ (by omega:aZ D (q i)<n+k),l _ _ (by omega:aY D (q i)<n+k),(e4 i b1).1,(e4 i b1).2];exact ⟨Y,a2,a3,a4,a5,a6,a7⟩
   ·have c1:i=E.length:=Y;rw[c1,Function.update_self,Function.update_self,l _ _ hA,l _ _ hB,e1,e2];exact ⟨Y,hl,rfl,rfl,rfl,la,lb⟩
  ·by_cases b5:j=k
   ·exact oL ⟨E.length,Y,by rw[b5,Function.update_self]⟩
   ·rcases h4 j Y hlj with ⟨i,hi,cb⟩|hr
    ·exact oL ⟨i,Y,by rw[Function.update_of_ne (by omega:i≠E.length)];exact cb⟩
    ·refine oR (λs p=>?_);have ct:=bv hS (by omega:j<D.length) s;rw[l _ _ Y,l _ _ Y];exact hr s p
  ·rw[l _ _ (by have:=(ι i).isLt;omega)];exact h5 i
 ·have b8:bg D ρ ι (aZ D k)->bg D ρ ι (aY D k)->t (aZ D k)=t (aY D k):=λla lb=>by
   by_contra a0;exact hc ⟨la,lb,a0⟩
  obtain ⟨s0,a8⟩:=lh hS hk hl;have b0:∀s,bg D ρ ι (W D (k,s))->t (W D (k,s))=t (W D (k,s0)):=by
   intro s p;cases s<;>cases s0<;>simp only[bP,bU] at p a8 ⊢
   ·exact b8 p a8
   ·exact (b8 a8 p).symm
  obtain ⟨t0,v0⟩:=h2 _ (bv hS hk s0) a8;have ca:∀y,val D (cj ρ ι y) (n+k)=val D (cj ρ ι y) (W D (k,s0)):=by
   by_cases r:dR D ρ ι (W D (k,!s0))
   ·exact pk hS hk s0 r hl.1
   ·have lo:=jt (b4 hk (!s0)) r hl;obtain ⟨-,v1⟩:=h2 _ (bv hS hk (!s0)) lo;intro y;rw[kz hS hk s0,← v1 y,b0 _ lo,v0 y];cases bf D k<;>simp
  refine ⟨E,Function.update t (n+k) (t (W D (k,s0))),q,h1,λw hw hlw=>?_,λi hi=>?_,λj hj hlj=>?_,λi=>?_⟩
  ·by_cases b2:w=n+k
   ·rw[b2,Function.update_self];exact ⟨t0,λy=>by rw[v0 y,ca y]⟩
   ·rw[l _ w Y];exact h2 w Y hlw
  ·obtain ⟨a1,a2,a3,a4,a5,a6,a7⟩:=h3 i hi;obtain ⟨sa,sb,-⟩:=hS (q i) Y;rw[l _ _ (by omega:n+q i<n+k),l _ _ (by omega:aZ D (q i)<n+k),l _ _ (by omega:aY D (q i)<n+k)];exact ⟨Y,a2,a3,a4,a5,a6,a7⟩
  ·by_cases b5:j=k
   ·refine oR (λs p=>?_);rw[b5] at p ⊢;rw[l _ _ (bv hS hk s),Function.update_self];exact b0 s p
   ·rcases h4 j Y hlj with c0|hr
    ·exact oL c0
    ·refine oR (λs p=>?_);have ct:=bv hS (by omega:j<D.length) s;rw[l _ _ Y,l _ _ Y];exact hr s p
  ·rw[l _ _ (by have:=(ι i).isLt;omega)];exact h5 i
lemma pY (r:aV n D)(l:dA ρ ι):∃E t q,dK D ρ ι D.length E t q:=by
 have h:∀k,k≤D.length->∃E t q,dK D ρ ι k E t q:=by
  intro k;induction k with
  | zero=>exact λ_=>oB l
  | succ k ih=>
   intro hk;obtain ⟨E,t,q,p⟩:=ih Y;exact nr r Y p
 exact h _ le_rfl
lemma jG {a:A0}:a∈bc D<->a.1<D.length:=by simp[bc]
lemma mY {E:aJ}{t q:Nat->Nat}(hI:dK D ρ ι D.length E t q){j:Nat}(hj:j<D.length)(s:Bool)(ha:bg D ρ ι (W D (j,s)))(hc:bg D ρ ι (n+j)):t (W D (j,s))≤t (n+j):=by
 obtain ⟨h1,-,h3,h4,-⟩:=hI;rcases h4 j hj hc with ⟨i,l,h⟩|hr
 ·obtain ⟨-,-,k,p,r,-,-⟩:=h3 i l;obtain ⟨sa,sb,-⟩:=h1 i l;rw[h] at k p r;cases s
  ·rw[bP,← p,k];omega
  ·rw[bU,← r,k];omega
 ·exact (hr s ha).le
lemma o1 {E:aJ}{t q:Nat->Nat}(l:dK D ρ ι D.length E t q){w:Nat}(r:bg D ρ ι w):t w≤t (aO n D):=by
 obtain ⟨h,p⟩:=r;revert h;induction p using rI with
 | refl=>exact λ_=>le_rfl
 | @head a c hstep hrest ih=>
  intro h;have k:bg D ρ ι a:=⟨h,rH hstep hrest⟩;obtain ⟨j,s,hj,rfl,rfl⟩:=dN.mp hstep.1;exact (mY l hj s k ⟨hstep.2,hrest⟩).trans (ih hstep.2)
lemma m5 {E:aJ}{t q:Nat->Nat}(r:dK D ρ ι D.length E t q){w:Nat}(hl:bg D ρ ι w)(h:t w≠t (aO n D)):∃i,i<E.length/\(aZ E i=t w\/aY E i=t w):=by
 obtain ⟨k,hp⟩:=hl;revert k h;induction hp using rI with
 | refl=>exact λh _=>absurd rfl h
 | @head a c hstep hrest ih=>
  intro h k;have p:bg D ρ ι a:=⟨k,rH hstep hrest⟩;obtain ⟨j,s,hj,rfl,rfl⟩:=dN.mp hstep.1;rcases r.2.2.2.1 j hj ⟨hstep.2,hrest⟩ with ⟨i,hi,l⟩|hr
  ·obtain ⟨-,-,-,e2,e3,-,-⟩:=r.2.2.1 i hi;rw[l] at e2 e3;refine ⟨i,hi,?_⟩;cases s
   ·left;rw[bP];exact e2
   ·right;rw[bU];exact e3
  ·have e:=hr s p;rw[e] at h ⊢;exact ih h hstep.2
lemma lA {E:aJ}{t q:Nat->Nat}(p:dK D ρ ι D.length E t q)(k:∀i:Fin m,bg D ρ ι (ι i).val){e:Nat}(he:e<m+E.length):∃w,bg D ρ ι w/\t w=e:=by
 by_cases l:e<m
 ·exact ⟨_,k ⟨e,l⟩,p.2.2.2.2 ⟨e,l⟩⟩
 ·obtain ⟨-,h,r,-⟩:=p.2.2.1 (e-m) Y;exact ⟨_,h,by rw[r];omega⟩
lemma jY {E:aJ}{t q:Nat->Nat}(l:dK D ρ ι D.length E t q)(h:∀i:Fin m,bg D ρ ι (ι i).val)(hm:0<m)(k:bg D ρ ι (aO n D)):t (aO n D)=aO m E:=by obtain ⟨w,r,p⟩:=lA l h (e:=m+E.length-1) Y;have h1:=o1 l r;have h2:=(l.2.1 _ (fL k) k).1;show t (aO n D)=m+E.length-1;omega
lemma p4 {E:aJ}{t q:Nat->Nat}(l:dK D ρ ι D.length E t q)(h:∀i:Fin m,bg D ρ ι (ι i).val)(hm:0<m)(p:bg D ρ ι (aO n D)):fA m E:=by intro e he;obtain ⟨w,hw,r⟩:=lA l h (e:=e) Y;have a0:t (aO n D)=m+E.length-1:=jY l h hm p;obtain ⟨i,hi,k⟩:=m5 l hw Y;rw[r] at k;exact cO.mpr ⟨i,mF.mpr ⟨mR.mpr hi,k⟩⟩
lemma pV (p:aV n D)(w:Nat):cy D ρ ι w=((bc D).filter (λa=>W D a=w/\bg D ρ ι (n+a.1))).card:=by
 rw[jd,cy,bL,filter_filter,card_filter];refine sC rfl (λj hj=>?_);have h:=(p j (mR.mp hj)).2.2;rw[bP,bU];by_cases l:aZ D j=w<;>by_cases k:aY D j=w<;>
  by_cases r:bg D ρ ι (n+j)<;>simp[l,k,r]
 exact h (l.trans k.symm)
lemma jP {E:aJ}{t q:Nat->Nat}(hS:aV n D)(a3:dA ρ ι)(hI:dK D ρ ι D.length E t q)(e:Nat):aS E e+(d8 D ρ ι t e).card≤∑ w∈d8 D ρ ι t e,cy D ρ ι w+1:=by
 obtain ⟨-,-,h3,h4,h5⟩:=hI;obtain ⟨F,hF⟩:∃F,F=d8 D ρ ι t e:=⟨_,rfl⟩;obtain ⟨A,hA⟩:∃A,A=(bc D).filter (λa=>bg D ρ ι (n+a.1)/\bg D ρ ι (W D a)/\t (W D a)=e):=⟨_,rfl⟩;rw[← hF];have l:∀w,w∈F<->bg D ρ ι w/\t w=e:=(by intro w;rw[hF,d8,mF,mR];exact ⟨λh=>h.2,λh=>⟨fL h.1,h⟩⟩);have k:∀a,a∈A<->a.1<D.length/\bg D ρ ι (n+a.1)/\bg D ρ ι (W D a)/\t (W D a)=e:=(by intro a;rw[hA,mF,jG]);have c2:A.card=∑ w∈F,cy D ρ ι w:=by
  rw[card_eq_sum_card_fiberwise (f:=W D) (s:=A) (t:=F) (λa ha=>mem_coe.mpr ((l _).mpr ((k a).mp (mem_coe.mp ha)).2.2))];refine sC rfl (λw hw=>?_);rw[pV hS w];congr 1;ext a;rw[mF,mF,k,jG];constructor
  ·rintro ⟨⟨ha,hl,-,-⟩,rfl⟩;exact ⟨ha,rfl,hl⟩
  ·rintro ⟨ha,rfl,hl⟩;exact ⟨⟨ha,hl,(l _).mp hw⟩,rfl⟩
 have c1:=ag (s:=A)
  (λa:A0=>∃i,i<E.length/\q i=a.1)
 have d0:aS E e≤(A.filter (λa:A0=>∃i,i<E.length/\q i=a.1)).card:=by
  have b5:∀i,∃a:A0,a.1=q i/\(i∈bL E e->a∈A.filter (λa:A0=>∃i,i<E.length/\q i=a.1)):=by
   intro i;by_cases hi:i∈bL E e
   ·rw[bL,mF,mR] at hi;obtain ⟨r,ct⟩:=hi;obtain ⟨a1,a2,-,a4,a5,a6,a7⟩:=h3 i r;rw[a4,a5] at ct;rcases ct with h|h
    ·exact ⟨(q i,false),rfl,λ_=>mF.mpr ⟨(k _).mpr ⟨a1,a2,by rw[bP];exact a6,by rw[bP];exact h⟩,i,r,rfl⟩⟩
    ·exact ⟨(q i,true),rfl,λ_=>mF.mpr ⟨(k _).mpr ⟨a1,a2,by rw[bU];exact a7,by rw[bU];exact h⟩,i,r,rfl⟩⟩
   ·exact ⟨(q i,false),rfl,λh=>absurd h hi⟩
  choose φ hφ1 hφ2 using b5
  refine card_le_card_of_injOn φ (λi hi=>hφ2 i hi) (λi hi p a8 heq=>?_);have hq:q i=q p:=by rw[← hφ1 i,← hφ1 p,heq]
  have r:i∈bL E e:=hi;have b0:p∈bL E e:=a8;rw[bL,mF,mR] at r b0;have e1:=(h3 i r.1).2.2.1;have e2:=(h3 p b0.1).2.2.1;rw[hq] at e1;omega
 have c8:=ag (s:=F)
  (λw=>w<n\/∃i,i<E.length/\n+q i=w)
 have c3:(F.filter (λw=>w<n\/∃i,i<E.length/\n+q i=w)).card≤1:=by
  rw[cQ];intro a ha b hb;rw[mF,l] at ha hb;obtain ⟨⟨la,ta⟩,ca⟩:=ha;obtain ⟨⟨lb,tb⟩,cb⟩:=hb;rcases ca with b8|⟨i,hi,rfl⟩<;>rcases cb with b6|⟨p,a8,rfl⟩
  ·obtain ⟨i,rfl⟩:=f8 a3 b8 la;obtain ⟨p,rfl⟩:=f8 a3 b6 lb;have e1:=h5 i;have e2:=h5 p;have b1:i=p:=Fin.ext Y;rw[b1]
  ·obtain ⟨i,rfl⟩:=f8 a3 b8 la;have e1:=h5 i;have e2:=(h3 p a8).2.2.1;have:=i.isLt;omega
  ·obtain ⟨p,rfl⟩:=f8 a3 b6 lb;have e1:=h5 p;have e2:=(h3 i hi).2.2.1;have:=p.isLt;omega
  ·have e1:=(h3 i hi).2.2.1;have e2:=(h3 p a8).2.2.1;have b1:i=p:=Y
   rw[b1]
 have c7:(F.filter (λw=>¬(w<n\/∃i,i<E.length/\n+q i=w))).card≤
   (A.filter (λa:A0=>¬∃i,i<E.length/\q i=a.1)).card:=by
  have b5:∀w,∃a:A0,a.1=w-n/\(w∈F.filter (λw=>¬(w<n\/∃i,i<E.length/\n+q i=w))->a∈A.filter (λa:A0=>¬∃i,i<E.length/\q i=a.1)):=by
   intro w;by_cases hw:w∈F.filter (λw=>¬(w<n\/∃i,i<E.length/\n+q i=w))
   ·have bm:=hw;rw[mF,l,nO] at bm;obtain ⟨⟨lw,tw⟩,hwn,hnem⟩:=bm;have c6:=fL lw;have hj:w-n<D.length:=Y
    have c0:n+(w-n)=w:=Y;have a0:¬∃i,i<E.length/\q i=w-n:=λ⟨i,hi,hq⟩=>hnem ⟨i,hi,Y⟩;have b2:bg D ρ ι (n+(w-n)):=by rw[c0];exact lw
    have hr:=(h4 (w-n) hj b2).resolve_left a0;obtain ⟨s,ls⟩:=lh hS hj b2;exact ⟨(w-n,s),rfl,λ_=>mF.mpr ⟨(k _).mpr ⟨hj,b2,ls,by rw[hr s ls,c0];exact tw⟩,a0⟩⟩
   ·exact ⟨(w-n,false),rfl,λh=>absurd h hw⟩
  choose ψ hψ1 hψ2 using b5
  refine card_le_card_of_injOn ψ (λw hw=>hψ2 w hw) (λw hw w' bm heq=>?_);have hq:w-n=w'-n:=by rw[← hψ1 w,← hψ1 w',heq]
  have h1:w∈F.filter (λw=>¬(w<n\/∃i,i<E.length/\n+q i=w)):=hw;have c5:w'∈F.filter (λw=>¬(w<n\/∃i,i<E.length/\n+q i=w)):=bm;rw[mF,nO] at h1 c5;omega
 omega
lemma l5 {E:aJ}{t q:Nat->Nat}(hS:aV n D)(a1:dA ρ ι)(hI:dK D ρ ι D.length E t q)(l:t (aO n D)=aO m E)(T:Finset Nat)(hT:T⊆bY m E):cd E T≤∑ w∈(bY n D).filter (λw=>bg D ρ ι w/\t w∈T),(cy D ρ ι w-1):=by
 have a0:t (aO n D)=m+E.length-1:=l;have r:∀e∈T,aS E e-1≤∑ w∈d8 D ρ ι t e,(cy D ρ ι w-1):=(by intro e he;have hb:=jP hS a1 hI e;have k:∀w∈d8 D ρ ι t e,1≤cy D ρ ι w:=(by intro w h;rw[d8,mF] at h;refine na h.2.1 (λhc=>?_);have h1:=cz.mp (hT he);have h2:=h.2.2;rw[hc] at h2;omega);have:=pt _ _ k;omega);have p:=sum_fiberwise_of_maps_to
  (s:=(bY n D).filter (λw=>bg D ρ ι w/\t w∈T)) (t:=T) (g:=t)
  (λw h=>(mF.mp h).2.2) (λw=>cy D ρ ι w-1)
 rw[← p];unfold cd;refine (sM r).trans (le_of_eq ?_);refine sC rfl (λe he=>sC ?_ (λ_ _=>rfl));ext w;simp only[d8,mF,mR];constructor
 ·rintro ⟨h,lw,rfl⟩;refine ⟨⟨cz.mpr ?_,lw,he⟩,rfl⟩;have h1:=cz.mp (hT he);by_contra hc;have a2:w=aO n D:=by unfold aO;omega
  rw[a2] at h1;omega
 ·rintro ⟨⟨h,lw,-⟩,rfl⟩;exact ⟨by have:=cz.mp h;omega,lw,rfl⟩
lemma pz (hS:aV n D)(r:dA ρ ι)(hm:2≤m)(a0:∀i:Fin m,∃y y':Fin m->Bool,(∀k,k≠i->y k=y' k)/\val D (cj ρ ι y) (aO n D)≠val D (cj ρ ι y') (aO n D)):∃E:aJ,a9 m E/\(∀y,val E y (aO m E)=val D (cj ρ ι y) (aO n D))/\bH m E≤gu D ρ ι/\br m E≤gw D ρ ι/\∀i:Fin m,(∀w,rG (bk n D) (ι i).val w->aS D w≤1)->i∈aN m E:=by
 obtain ⟨E,t,q,hI⟩:=pY hS r;have a1:∀i:Fin m,bg D ρ ι (ι i).val:=λi=>ov hS r i (a0 i);have a3:bg D ρ ι (aO n D):=(by obtain ⟨y,y',-,p⟩:=a0 ⟨0,Y⟩;exact ⟨λhc=>p (hc y y'),rF⟩);have a2:=jY hI a1 Y a3;obtain ⟨-,l⟩:=hI.2.1 _ (fL a3) a3;rw[a2] at l;have p:E≠[]:=by
  rintro rfl;obtain ⟨y,y',a8,p⟩:=a0 ⟨0,Y⟩;apply p;have h1:aO m ([]:aJ)=m-1:=by simp[aO]
  rw[← l y,← l y',h1,ck [] y (m-1) Y,ck [] y' (m-1) Y];exact a8 _ (λhc=>by have:=kA Fin.val hc;simp at this;omega)
 refine ⟨E,⟨hI.1,p4 hI a1 Y a3,p⟩,l,?_,?_,?_⟩
 ·unfold bH gu;refine (l5 hS r hI a2 (bY m E) (Subset.refl _)).trans
   (ak (λw hw=>?_))
  rw[mF] at hw ⊢;exact ⟨hw.1,hw.2.1⟩
 ·unfold br gw;refine (l5 hS r hI a2 _ (fS _ _)).trans
   (ak (λw hw=>?_))
  rw[mF] at hw ⊢;obtain ⟨a6,lw,a5⟩:=hw;have hs:O m E (t w)=eC D ρ ι w:=(by ext i;rw[bD,kQ,(hI.2.1 w (fL lw) lw).2]);exact ⟨a6,lw,by rw[← hs];exact (mF.mp a5).2⟩
 ·intro i0 a4;rw[eG];intro e he;have hb:=jP hS r hI e;have bm:∑ w∈d8 D ρ ι t e,cy D ρ ι w≤(d8 D ρ ι t e).card:=by
   rw[card_eq_sum_ones];refine sM (λw hw=>?_);rw[d8,mF] at hw;obtain ⟨-,lw,a7⟩:=hw;refine (lr w).trans (a4 w ?_);have hv:=(hI.2.1 w (fL lw) lw).2;rw[← a7] at he;have p:val D (cj ρ ι (single i0)) w≠val D (cj ρ ι (λ_=>false)) w:=(by rw[← hv,← hv,bD.mp he,nf hI.1];simp);exact dt (λa b h=>h.1) (gt hS _ _ (ι i0) (lg r (λk hk=>by simp[single,hk])) w p)
  omega
def fb (D:aJ)(ρ:Fin n->Option Bool)(ι:Fin m->Fin n):Finset (P0):=
 (cq n D).filter (λu=>bg D ρ ι u.1/\u.2+1<cy D ρ ι u.1)
def fF (D:aJ)(ρ:Fin n->Option Bool)(ι:Fin m->Fin n):Finset (P0):=
 (cq n D).filter (λu=>(bg D ρ ι u.1/\(eC D ρ ι u.1).Nonempty)/\
  u.2+1<cy D ρ ι u.1)
lemma jk {u:P0}:u∈fb D ρ ι<->u∈cq n D/\bg D ρ ι u.1/\u.2+1<cy D ρ ι u.1:=mF
lemma gN {u:P0}:u∈fF D ρ ι<->u∈cq n D/\(bg D ρ ι u.1/\(eC D ρ ι u.1).Nonempty)/\u.2+1<cy D ρ ι u.1:=mF
lemma lE (P:Nat->Prop)[DecidablePred P]:((cq n D).filter (λu=>P u.1/\u.2+1<cy D ρ ι u.1)).card=∑ w∈(bY n D).filter P,(cy D ρ ι w-1):=by
 have p:(cq n D).filter (λu=>P u.1/\u.2+1<cy D ρ ι u.1) =
   ((bY n D).filter P).sigma (λw=>range (cy D ρ ι w-1)):=by
  ext u;have:=lr (D:=D) (ρ:=ρ) (ι:=ι) u.1;simp only[cq,mF,mG,mR];constructor
  ·rintro ⟨⟨h,-⟩,k,l⟩;exact ⟨⟨h,k⟩,Y⟩
  ·rintro ⟨⟨h,k⟩,l⟩;exact ⟨⟨h,Y⟩,k,Y⟩
 rw[p,au];simp
lemma nG:gu D ρ ι=(fb D ρ ι).card:=
 (lE (λw=>bg D ρ ι w)).symm
lemma mh:gw D ρ ι=(fF D ρ ι).card:=
 (lE (λw=>bg D ρ ι w/\(eC D ρ ι w).Nonempty)).symm
lemma iu (hS:aV n D){c:Fin n}(hc:ρ c=some true){u:P0}(hu:c∈O n D u.1):u∉fb D ρ ι:=
 λh=>lm hS hc hu (jk.mp h).2.1
lemma kN {u:P0}(h:cy D ρ ι u.1≤u.2+1):u∉fb D ρ ι:=λhk=>by
 have:=(jk.mp hk).2.2
 omega
lemma iq:fF D ρ ι⊆fb D ρ ι:=λ_ hu=>
 jk.mpr ⟨(gN.mp hu).1,(gN.mp hu).2.1.1,
  (gN.mp hu).2.2⟩
lemma lt {u:P0}(h:eC D ρ ι u.1=∅):u∉fF D ρ ι:=λhk=>by
 have:=(gN.mp hk).2.1.2
 rw[h] at this
 exact nN this
lemma oh (S:Finset (P0))(k:S⊆cq n D)(h:∀u∈S,u∉fb D ρ ι):gu D ρ ι+S.card≤bH n D:=by rw[nG,← jR,← cU (dL.mpr (λu h1 h2=>h u h2 h1))];exact cL (uS (fS _ _) k)
lemma ly (S:Finset (P0))(k:S⊆cq n D)(h:∀u∈S,u∉fF D ρ ι):gw D ρ ι+S.card≤bH n D:=by rw[mh,← jR,← cU (dL.mpr (λu h1 h2=>h u h2 h1))];exact cL (uS (fS _ _) k)
lemma mx (hS:aV n D)(K:Finset Nat)(x b:Nat)(r:∀w∈K,rG (λa c=>bk n D a c/\a∈K/\c∈K) x w)(hb:b∈K)(b1:∀w∈K,w≠b->aS D w≤1)(e:A0)(he:e∈bo n D K)(a0:¬bg D ρ ι (n+e.1)):∃j∈bL D b,¬bg D ρ ι (n+j):=by
 obtain ⟨b8,a6,b6⟩:=mF.mp he;have ca:e.1<D.length:=jG.mp b8;have p:bk n D (W D e) (n+e.1):=b4 ca e.2;have a3:∀a c,a∈K->a≠b->bk n D a c->¬bg D ρ ι c->¬bg D ρ ι a/\∀c',bk n D a c'->c'=c:=(by intro a c b2 a2 hs hc;have h1:aS D a=1:=(by have:=b1 a b2 a2;have:=eU hs;omega);have a1:∀c',bk n D a c'->c'=c:=λc' k=>cY k hs h1;refine ⟨λhla=>?_,a1⟩;have b0:a≠aO n D:=(by have:=ew hS (eU hs);unfold aO;omega);obtain ⟨c',k,a7⟩:=j6 hla b0;rw[a1 c' k] at a7;exact hc a7);have bm:∀a,rG (λa c=>bk n D a c/\a∈K/\c∈K) a
   (W D e)->(∃j∈bL D b,¬bg D ρ ι (n+j))\/
   (¬bg D ρ ι a/\¬rG (λa c=>bk n D a c/\a∈K/\c∈K) a b):=by
  intro a hp;induction hp using rI with
  | refl=>
   by_cases a5:W D e=b
   ·have hr:=fV p;rw[am,a5] at hr;exact oL ⟨e.1,hr,a0⟩
   ·obtain ⟨h1,h2⟩:=a3 _ _ a6 a5 p a0;refine oR ⟨h1,λhp=>?_⟩;rcases cH hp with a4|⟨c',k,-⟩
    ·exact a5 a4
    ·rw[h2 c' k.1] at k;exact b6 k.2.2
  | @head a c hstep hrest ih=>
   rcases ih with hl|⟨a8,b5⟩
   ·exact oL hl
   ·by_cases a2:a=b
    ·refine oL ⟨c-n,?_,?_⟩
     ·rw[← a2];exact fV hstep.1
     ·rw[Nat.add_sub_cancel' hstep.1.2.1];exact a8
    ·obtain ⟨h1,h2⟩:=a3 _ _ hstep.2.1 a2 hstep.1 a8;refine oR ⟨h1,λhp=>?_⟩;rcases cH hp with a4|⟨c',k,l⟩
     ·exact a2 a4
     ·rw[h2 c' k.1] at l;exact b5 l
 rcases bm x (r _ a6) with h|⟨-,h⟩
 ·exact h
 ·exact absurd (r b hb) h
lemma oT (hS:aV n D)(x c:Fin n):∀w,w∈bJ n D x c->rG (λa d=>bk n D a d/\a∈bJ n D x c/\d∈bJ n D x c) x.val w:=by
 intro w;induction w using sI with
 | _ w ih=>
  intro hw;have l:∀u,u∈bJ n D x c<->u<n+D.length/\x∈O n D u/\c∉O n D u:=(by intro u;simp only[bJ,mF,mR]);obtain ⟨a2,p,hc⟩:=(l w).mp hw;by_cases hn:w<n
  ·have hs:O n D w={⟨w,hn⟩}:=du D ⟨w,hn⟩;rw[hs,mS] at p;have a1:x.val=w:=by rw[p]
   rw[a1]
  ·obtain ⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,Y⟩;have hj:j<D.length:=Y
   have k:∀s:Bool,x∈O n D (W D (j,s))->c∉O n D (W D (j,s))->rG (λa d=>bk n D a d/\a∈bJ n D x c/\d∈bJ n D x c) x.val (n+j):=(by intro s h1 h2;have a0:=bv hS hj s;have hm:W D (j,s)∈bJ n D x c:=(l _).mpr ⟨Y,h1,h2⟩;exact rT (ih _ a0 hm) ⟨b4 hj s,hm,hw⟩);cases ht:bf D j
   ·rw[eL hS hj ht,mU] at p hc;rcases p with h1|h1
    ·exact k false (by rw[bP];exact h1)
      (by rw[bP];exact λh=>hc (oL h))
    ·exact k true (by rw[bU];exact h1)
      (by rw[bU];exact λh=>hc (oR h))
   ·rw[dC hS hj ht,mN] at p hc;by_cases r:c∈O n D (aZ D j)
    ·exact k true (by rw[bU];exact p.2)
      (by rw[bU];exact λh=>hc ⟨r,h⟩)
    ·exact k false (by rw[bP];exact p.1) (by rw[bP];exact r)
lemma jN (r:aV n D){x c:Fin n}(hc:ρ c=some true){b:Nat}(hb:b∈bJ n D x c)(a1:2≤aS D b)(k:cd D (bJ n D x c)=1){e:A0}(he:e∈bo n D (bJ n D x c))(l:c∈O n D (n+e.1)):cy D ρ ι b≤1:=by
 have h1:aS D b-1+∑ u∈(bJ n D x c).erase b,(aS D u-1) =
   ∑ u∈bJ n D x c,(aS D u-1):=
  aE _ (λu=>aS D u-1) hb
 unfold cd at k;have h:∀w∈bJ n D x c,w≠b->aS D w≤1:=by
  intro w hw a0;have h2:aS D w-1≤∑ u∈(bJ n D x c).erase b,(aS D u-1):=single_le_sum (f:=λu=>aS D u-1) (λ_ _=>nZ _)
    (mE.mpr ⟨a0,hw⟩)
  omega
 obtain ⟨j,hj,p⟩:=mx (ρ:=ρ) (ι:=ι) r _ x.val b (oT r x c) hb
  h e he (lm r hc l)
 have a2:((bL D b).filter (λj=>bg D ρ ι (n+j))).card <
   (bL D b).card:=al (filter_ssubset.mpr ⟨j,hj,p⟩)
 have h2:(bL D b).card=aS D b:=rfl;unfold cy;omega
lemma nD {G:Fin n->Fin n->Prop}(l:dA ρ ι)(a0:∀u v,G u v->G v u)(hT:∀c a,ρ c=some true->G c a->ρ a=some false)(y:Fin m->Bool):cN G (cj ρ ι y)<->cN (λu v:Fin m=>G (ι u) (ι v)) y:=by
 have k:∀u v,G u v->cj ρ ι y u=true->cj ρ ι y v=true->∃i,ι i=u/\y i=true:=by
  intro u v h p hv;cases hr:ρ u with
  | none=>
   obtain ⟨i,rfl⟩:=(l.2 u).mp hr;rw[eK l] at p;exact ⟨i,rfl,p⟩
  | some b=>
   rw[eo ι y hr] at p;subst p;rw[eo ι y (hT u v hr h)] at hv;exact absurd hv bF
 constructor
 ·rintro ⟨u,v,h,p,hv⟩;obtain ⟨i,rfl,hi⟩:=k u v h p hv;obtain ⟨i',rfl,r⟩:=k v _ (a0 _ _ h) hv p;exact ⟨i,i',h,hi,r⟩
 ·rintro ⟨i,i',h,hi,r⟩;exact ⟨ι i,ι i',h,by rw[eK l];exact hi,by rw[eK l];exact r⟩
lemma kP {G:Fin n->Fin n->Prop}(hS:aV n D)(r:dA ρ ι)(hC:bG n G D)(a0:∀u v,G u v->G v u)(hT:∀c a,ρ c=some true->G c a->ρ a=some false)(l:bI (λu v:Fin m=>G (ι u) (ι v)))(hm:0<m):∃E:aJ,a9 m E/\bG m (λu v:Fin m=>G (ι u) (ι v)) E/\bH m E≤gu D ρ ι/\br m E≤gw D ρ ι/\∀i:Fin m,(∀w,rG (bk n D) (ι i).val w->aS D w≤1)->i∈aN m E:=by have h:∀y,val D (cj ρ ι y) (aO n D)=true<->cN (λu v:Fin m=>G (ι u) (ι v)) y:=λy=>(hC _).trans (nD r a0 hT y);have a1:2≤m:=(by obtain ⟨a,-,a2⟩:=l.2.2.2 ⟨0,hm⟩ ⟨0,hm⟩;by_contra hc;exact a2 (Fin.ext (by have:=a.isLt;show a.val=0;omega)));have p:∀i:Fin m,∃y y':Fin m->Bool,(∀k,k≠i->y k=y' k)/\val D (cj ρ ι y) (aO n D)≠val D (cj ρ ι y') (aO n D):=(by intro i;obtain ⟨a,ha,-⟩:=l.2.2.2 i i;refine ⟨single a,bs i (single a),eM i _,λheq=>?_⟩;have h1:cN (λu v:Fin m=>G (ι u) (ι v)) (bs i (single a)):=⟨i,a,ha,d7 i _,by simp[bs,single]⟩;have h2:=(h _).mpr h1;rw[← heq] at h2;exact go l a ((h _).mp h2));obtain ⟨E,h1,h2,h3,h4,h5⟩:=pz hS r a1 p;exact ⟨E,h1,λy=>by rw[h2 y];exact h y,h3,h4,h5⟩
end CofRestrict
section L3Gen
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma kK (hS:aV n D){P:Finset (Fin n)}(hP:P.card≤7)(L:Finset (Finset (Fin n)))(h3:∀T∈L,T.card=3/\bq n D P T)(m:∀T∈L,∀T'∈L,T≠T'->(T∩T').card≤1)(E:Finset (A0))(hE:∀e∈E,e∈bo n D (ba n D P)/\3≤(O n D (W D e)∩P).card)(Lab:Finset (Fin n))(U:Fin n->Finset (Fin n))(hw:∀f∈Lab,∃e,dE n D P (U f) f e)(a0:∀f∈Lab,∀T∈L,(U f∩T).card≤1):2*L.card+E.card+Lab.card≤(bo n D (ba n D P)).card+(bi n D (ba n D P)).card:=by
 classical
 choose! wit hwit using hw
 let S:=Lab.filter (λf=>∀M,M⊆U f->M.card=2->f∈M->¬bq n D P M)
 have k:S⊆Lab:=fS _ _;have a1:∀f∈Lab \ S,∃M,M⊆U f/\M.card=2/\f∈M/\bq n D P M:=(by intro f h;rw[mD,mF] at h;by_contra hc;exact h.2 ⟨h.1,λM r h2 h4 h5=>hc ⟨M,r,h2,h4,h5⟩⟩)
 choose! pr hpr using a1
 have hX:=pZ hS hP L h3 m ((Lab \ S).image pr) (by
  intro M hM;obtain ⟨f,h,rfl⟩:=mM.1 hM;obtain ⟨r,h2,-,h4⟩:=hpr f h;refine ⟨h4,Y,λhL=>by have:=(h3 _ hL).1;omega,Y,Y,λ_ T hT hsub=>?_⟩;have:=cL (subset_inter r hsub);have:=a0 f (mD.1 h).1 T hT
  omega)
 have a2:=m0 hS P E hE Lab S U wit hwit k (λf h=>
  l6 (hwit f (k h)) (mF.1 h).2)
 have a3:(Lab \ S).card≤2*((Lab \ S).image pr).card:=by
  refine card_le_mul_card_image _ 2 (λM _=>?_);by_cases l:((Lab \ S).filter (λf=>pr f=M)).Nonempty
  ·obtain ⟨g,hg⟩:=l;rw[mF] at hg;have p:M.card=2:=hg.2▸(hpr g hg.1).2.1;rw[← p];refine cL (λf h=>?_);rw[mF] at h;exact h.2▸(hpr f h.1).2.2.1
  ·rw[not_nonempty_iff_eq_empty.1 l];simp
 have:=sP k;omega
lemma li (l:aV n D)(Z:Finset Nat)(k:∀b∈Z,2≤aS D b/\O n D b=∅):Z.card≤bu n D:=by
 have h:Z⊆(bY n D).filter (λw=>¬(O n D w).Nonempty):=λb hb=>ie l (k b hb).1 (k b hb).2
 calc Z.card=∑ _w∈Z,1:=ab
  _≤∑ w∈Z,(aS D w-1):=sM (λw hw=>by have:=(k w hw).1;omega)
  _≤bu n D:=ak h
lemma kB (hG:bI G)(hS:aV n D)(hC:bG n G D){a2:Fin n->A0}(l:ch n G D a2)(T J:Finset (Fin n))(A:Fin n->Finset (Fin n))(hJ:∀i∈J,i∈aN n D/\(∃a∈T,G i a)/\∀f∈T,∃a∈A f,G i a)(hA:∀f∈T,(∀a∈A f,∀b∈A f,¬G a b)/\T.erase f⊆A f/\∃a∈A f,G f a):J.card+T.card≤(bo n D (ba n D T)).card:=by
 classical
 obtain ⟨a1,m⟩:=gh l T J (λi hi=>⟨(hJ i hi).1,(hJ i hi).2.1⟩);have bm:∀f∈T,∃e:A0,e.1<D.length/\bf D e.1=true/\f∈O n D (W D e)/\f∉O n D (n+e.1)/\Disjoint (O n D (W D e)) (A f):=(by intro f k;obtain ⟨j,s,h1,h2,h4,h5,h6⟩:=fq hG hS hC (A f) (hA f k).1 f (hA f k).2.2;exact ⟨(j,s),h1,h2,h4,h5,h6⟩)
 choose! w hw using bm
 have a0:iO w T:=by
  intro f k g r a4;by_contra b1;exact dL.1 (hw f k).2.2.2.2 (a4▸(hw g r).2.2.1)
   ((hA f k).2.1 (mE.2 ⟨λh=>b1 h.symm,r⟩))
 have a3:Disjoint (J.image a2) (T.image w):=by
  rw[dL];intro e a5 a6;obtain ⟨i,hi,rfl⟩:=mM.1 a5;obtain ⟨f,k,a8⟩:=mM.1 a6;obtain ⟨a,ha,b0⟩:=(hJ i hi).2.2 f k;exact dL.1 (hw f k).2.2.2.2
   (a8▸(l.1 i (hJ i hi).1).2.2.1 a b0) ha
 have p:T.image w⊆bo n D (ba n D T):=by
  intro e he;obtain ⟨f,k,rfl⟩:=mM.1 he;obtain ⟨h1,h2,h4,h5,h6⟩:=hw f k;refine e6.2 ⟨h1,⟨f,mN.2 ⟨h4,k⟩⟩,?_⟩;rintro ⟨g,r⟩;rw[mN] at r;have a7:g∈O n D (W D (w f)):=de hS h1 h2 (w f).2 r.1;exact dL.1 h6 a7
   ((hA f k).2.1 (mE.2 ⟨λh=>h5 (h▸r.1),r.2⟩))
 have:=cL (uS a1 p);rw[cU a3,m,cJ a0] at this;exact this
lemma jL (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:cn n D b){a1:Fin n->A0}(p:ch n G D a1)(T J:Finset (Fin n))(A:Fin n->Finset (Fin n))(hJ:∀i∈J,i∈aN n D/\(∃a∈T,G i a)/\∀f∈T,∃a∈A f,G i a)(hA:∀f∈T,(∀a∈A f,∀b∈A f,¬G a b)/\T.erase f⊆A f/\∃a∈A f,G f a){x y z:Fin n}(r:T={x,y,z})(m:x≠y)(k:x≠z)(l:y≠z){w v:Nat}(hx:x∈O n D w)(hy:y∈O n D w)(a0:x∈O n D v)(hz:z∈O n D v):J.card+2+(aW n D).card≤3+br n D:=by
 have a2:T.card=3:=(by rw[r,cI (by simp[m,k]),cI (by simp[l]),cS]);have h1:=kB hG h.1 hC p T J A hJ hA;have h2:=ic h.1 a2 (a:=x) (b:=y) (c:=z) (by simp[r]) (by simp[r])
  (by simp[r]) m k l hx hy a0 hz
 have h4:=d9 h T (by rw[dV hG hC];simp);have h5:=eN h.1 b hb T;have h6:=cL (iL:T∩aW n D⊆T);omega
end L3Gen
lemma lB {i j:F0}(h:aX i=aX j):i=j:=by
 by_contra m;obtain ⟨z,k,l⟩:=gv i j m
 have:z∈aX j:=h▸(by simp[aX,k])
 simp[aX,l] at this
lemma ce {i a:F0}:a∈aX i<->aH i a:=by simp[aX]
lemma iK {D:aJ}(h:a9 14 D)(hD:be D)(P:S0)(hP:∀a∈P,∀b∈P,¬aH a b)(J:S0)(hJ:∀i∈J,i∈aN 14 D/\aX i⊆P/\¬bq 14 D P (aX i)):J.card≤bu 14 D:=by
 classical
 have hG:=bn;have hC:=bl hD;have m:∀i∈J,∀q,(∀a∈P,(a∈O 14 D q<->aH i a))->False:=(by intro i l q p;refine (hJ i l).2.2 ⟨q,?_⟩;ext a;rw[mN,ce];exact ⟨λh1=>(p a h1.2).1 h1.1,λh1=>⟨(p a ((hJ i l).2.1 (ce.2 h1))).2 h1,(hJ i l).2.1 (ce.2 h1)⟩⟩);have hb:∀i∈J,∃b,aU 14 D i.val b/\2≤aS D b/\O 14 D b=∅:=by
  intro i l;rcases cr hG h hC (hJ i l).1 with a2|hb
  ·obtain ⟨j,s,-,-,-,p⟩:=fW hG h.1 hC P hP a2;exact (m i l _ p).elim
  ·exact hb
 choose! β hβ using hb
 have a0:iO β J:=by
  intro i l j hj a1;by_contra a4;obtain ⟨a,r,a3⟩:=gv j i (nS a4);obtain ⟨k,s,-,-,-,-,p⟩:=iv hG h.1 hC P hP (hβ i l).1
   (c9 h.1 (a1▸(hβ j hj).1)) ⟨a,(hJ j hj).2.1 (ce.2 r),r,a3⟩
  exact m i l _ p
 rw[← cJ a0];refine li h.1 _ (λb hb=>?_);obtain ⟨i,l,rfl⟩:=mM.1 hb;exact (hβ i l).2
lemma kV {D:aJ}(h:a9 14 D)(hD:be D)(P:S0)(p:P⊆bX 0)(a8:P⊆aW 14 D)(Oc Ct I:S0)(a1:∀i∈Oc,aX i⊆P/\bq 14 D P (aX i))(a2:∀c∈Ct,c∉Oc/\((aX c∩P).card≤2\/(aX c⊆P/\¬bq 14 D P (aX c))))(hI:∀i∈I,i∈aN 14 D/\aX i⊆P):2*Oc.card+I.card+(Ct.biUnion (λc=>aX c∩P)).card+(aW 14 D).card≤2*P.card+br 14 D:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨b,m⟩:=dY h hD;have bm:∀a∈P,∀b∈P,¬aH a b:=λa k b m=>eg 0 a (p k) b (p m);have a7:P.card≤7:=(cL p).trans o
 obtain ⟨E,a6,hE⟩:=nQ hG h hC P I (λi l=>
  ⟨(hI i l).1,aX i,(hI i l).2,(dH i).ge,λa k=>ce.1 k⟩)
 have a0:∀f∈Ct.biUnion (λc=>aX c∩P),∃c∈Ct,f∈aX c∩P:=λf hf=>mB.1 hf
 choose! ct hct using a0
 have r:=kK h.1 a7 (Oc.image aX)
  (λT hT=>by
   obtain ⟨i,l,rfl⟩:=mM.1 hT
   exact ⟨dH i,(a1 i l).2⟩)
  (λT hT T' hT' hne=>by
   obtain ⟨i,l,rfl⟩:=mM.1 hT;obtain ⟨j,hj,rfl⟩:=mM.1 hT';have:=gP i j (λhij=>hne (hij▸rfl)) univ
   simpa[aX] using this)
  E hE (Ct.biUnion (λc=>aX c∩P)) (λf=>aX (ct f)∩P)
  (λf hf=>by
   obtain ⟨hc,a5⟩:=hct f hf;refine j3 hG h.1 hC (X:=insert (ct f) (P \ (aX (ct f)∩P)))
    iR ?_ ?_ (λa k=>mK k) a5
    ⟨ct f,mL _ _,bh (ce.1 (mN.1 a5).1)⟩
   ·rcases (a2 _ hc).2 with h2|⟨h2,h4⟩
    ·exact oL h2
    ·rw[qL.2 h2];exact oR ⟨dH _,h4⟩
   ·have a4:∀a∈P \ (aX (ct f)∩P),¬aH (ct f) a:=by
     intro a k a3;rw[mD,mN,ce] at k;exact k.2 ⟨a3,k.1⟩
    intro a k b m;rcases mI.1 k with rfl|k<;>rcases mI.1 m with rfl|m
    ·exact bW _
    ·exact a4 b m
    ·exact λhab=>a4 a k (bh hab)
    ·exact bm a (mD.1 k).1 b (mD.1 m).1)
  (λf hf T hT=>by
   obtain ⟨i,l,rfl⟩:=mM.1 hT;have:=gP (ct f) i (λhij=>(a2 _ (hct f hf).1).1 (hij▸l)) P
   rwa[show univ.filter (λz=>aH i z)∩P=aX i from qL.2 (a1 i l).1] at this)
 have h4:=d9 h P (by rw[c4 hD];simp);have h5:=eN h.1 b m P;rw[qL.2 a8] at h5;rw[af _ (λi j hij=>lB hij),a6] at r;omega
lemma kS {D:aJ}(h:a9 14 D)(hD:be D)(hB:br 14 D=(aW 14 D).card)(h0:(0:F0)∈aN 14 D):False:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨b,hb⟩:=dY h hD;have ca:aR 14 D b=∅:=(by have:=dd h.1 b hb;exact cZ.1 Y);have a4:∀x,(aG 14 D x).card≤2:=by
  intro x;have m:=ff hG h hC b hb x;have l:=cL
   (iL:({x}:S0)∩aW 14 D⊆{x})
  rw[ca] at m;simp only[filter_empty,ad,cS] at m l;omega
 obtain ⟨e,c2,-,d1,d0,b2,c8,-⟩:=eJ hG h hC h0;have a2:∀u:F0,aH 0 u->∃Z,(∀t,t≠u->Z∉aG 14 D t)/\∀w:F0,aH w u->w≠0->aI Z∈aG 14 D w:=by
  intro u hu;have hY:aI e∈aG 14 D u:=aP.2 ⟨c2,b2 u hu,by rw[show (aI e).1=e.1 from rfl,d0];simp⟩;obtain ⟨Z,-,ct,hZ,-⟩:=kL h hD h0
   (λhu0=>bW 0 (by rw[hu0] at hu;exact hu)) c8 hY (a4 u)
  refine ⟨Z,hZ,λw hw p=>?_⟩;obtain ⟨e',m,l,-,-,-⟩:=bp hG h.1 hC hw;rw[ct,mI,mS] at l;rcases l with l|l
  ·have h4:e'=e:=(by rw[← aT e',l,aT]);rw[h4] at m;have:=(aP.1 m).2.1;rw[d1,mS] at this;exact (p this).elim
  ·rw[← l,aT];exact m
 have a3:∀w w' u:F0,aH 0 u->aH w u->aH w' u->w≠0->w'≠0->w≠w'->aH w 9->u≠9->∃r,aI r∈aG 14 D 9/\w∈O 14 D (W D r)/\∀a,a≠w->¬aH a w'->a∉O 14 D (W D r):=by
  intro w w' u hu cb bm p b0 a7 eb d2;obtain ⟨Z,hZ,b8⟩:=a2 u hu;obtain ⟨r,a8,a0,-,-,-⟩:=bp hG h.1 hC eb;have ec:r≠aI Z:=(by intro c3;rw[c3,aT] at a0;exact hZ 9 (nS d2) a0);refine ⟨r,a0,(aP.1 a8).2.1,λa ha haw' hmem=>?_⟩;obtain ⟨e3,m,l,h4⟩:=bB h hD (x:=w) (a:=a) (b:=w')
   (nS ha) a7 haw'
  have k:({aI Z,r}:Finset (A0))⊆aG 14 D w:=by
   intro x hx;rcases mI.1 hx with rfl|hx
   ·exact b8 w cb p
   ·rw[mS.1 hx];exact a8
  have c0:=eS k
   (by rw[cP (nS ec)];exact a4 w)
  rw[← c0,mI,mS] at m;rcases m with rfl|rfl
  ·exact h4 (aP.1 (b8 w' bm b0)).2.1
  ·exact l hmem
 obtain ⟨r1,a1,b1,c1⟩:=a3 1 3 7 o o o o
  o o o o
 obtain ⟨r5,a5,b5,c5⟩:=a3 5 4 10 o o o o
  o o o o
 obtain ⟨r6,a6,b6,c6⟩:=a3 6 2 8 o o o o
  o o o o
 have c7:aI r1≠aI r5:=λhh=>
  c1 5 o o (by rw[← aT r1,hh,aT];exact b5)
 have ea:aI r1≠aI r6:=λhh=>
  c1 6 o o (by rw[← aT r1,hh,aT];exact b6)
 have ej:aI r5≠aI r6:=λhh=>
  c5 6 o o (by rw[← aT r5,hh,aT];exact b6)
 have k:({aI r1,aI r5,aI r6}:Finset (A0))⊆aG 14 D 9:=(by intro x hx;simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl<;>assumption);have:=cL k;rw[cI (by simp[c7,ea]),cP ej] at this;have:=a4 9;omega
lemma js {D:aJ}(h:a9 14 D)(k:be D)(p:br 14 D≤(aW 14 D).card)(m:(0:F0)∈aN 14 D):False:=by obtain ⟨b,l⟩:=dY h k;exact kS h k (le_antisymm p (iD h.1 b l)) m
lemma nH {D:aJ}(h:a9 14 D)(p:be D)(m:br 14 D≤13)(k:aN 14 D={0}):False:=by have l:=db 14 D;rw[k,cS] at l;exact js h p Y (by rw[k];simp)
def cs (k:Fin 7):F0:=⟨k.val,by omega⟩
lemma dX:fI cs:=o
lemma eE:∀k:Fin 7,aX (cs k)⊆bX 0:=aa
def b7:S0:={7,8,9,10,12,13}
def fN (f:F0):S0:=
 if f=7 then {3,8,9,10,13} else if f=8 then {6,7,10,12,13} else {4,7,8,9,12}
lemma lV:∀i∈({0,1,2,5}:S0),(∃a∈({7,8,10}:S0),aQ i a=true)/\∀f∈({7,8,10}:S0),∃a∈fN f,aQ i a=true:=aa
lemma iV:∀f∈({7,8,10}:S0),(∀a∈fN f,∀b∈fN f,aQ a b=false)/\({7,8,10}:S0).erase f⊆fN f/\∃a∈fN f,aQ f a=true:=aa
lemma fp:∀i∈({0,1,2,5}:S0),aX i⊆b7:=aa
lemma iG:∀c∈({3,4,6}:S0),c∉({0,1,2,5}:S0)/\(aX c∩b7).card≤2:=aa
lemma n6:∀a∈b7,a∉({0,1,2,5,11}:S0):=o
lemma kW:(({3,4,6}:S0).biUnion (λc=>aX c∩b7)).card=6:=aa
lemma oM {D:aJ}(h:a9 14 D)(hD:be D)(l:∀i∈({0,1,2,5}:S0),i∈aN 14 D):(aW 14 D).card+3≤br 14 D:=by
 have hG:=bn;have hC:=bl hD;obtain ⟨b,r⟩:=dY h hD;obtain ⟨a0,k⟩:=cR hG h hC;have p:=(k.1 0 (l 0 o)).2.2.1;have m:=jL hG h hC b r k {7,8,10} {0,1,2,5} fN
  (λi hi=>⟨l i hi,(lV i hi).1.imp (λa ha=>⟨ha.1,(aK _ _).1 ha.2⟩),λf hf=>((lV i hi).2 f hf).imp (λa ha=>⟨ha.1,(aK _ _).1 ha.2⟩)⟩)
  (λf hf=>⟨λa ha b r=>bw.1 ((iV f hf).1 a ha b r),(iV f hf).2.1,(iV f hf).2.2.imp (λa ha=>⟨ha.1,(aK _ _).1 ha.2⟩)⟩)
  rfl o o o
  (p 7 o) (p 8 o) (p 7 o) (p 10 o)
 rw[show ({0,1,2,5}:S0).card=4 from rfl] at m;omega
section L3bGen
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma ek (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:cn n D b){x c:Fin n}(k:x≠c)(hx:x∈aW n D)(l:∀u∈aR n D b,x∈O n D u.1->c∈O n D u.1){w:Nat}(hw:x∈O n D w/\c∈O n D w):∃e0,∀e∈aG n D x,e≠e0->c∈O n D (W D e):=by
 classical
 obtain ⟨z,r,a2⟩:=hG.2.2.1 x c k;obtain ⟨-,-,h2,e1,a0,a3,-⟩:=jq hG h hC b hb k hx l hw r a2;have m:((bo n D (bJ n D x c)).erase e1).card=1:=(by rw[cE a0,h2]);obtain ⟨e0,a1⟩:=ac.1 m;refine ⟨e0,λe he hne=>?_⟩;by_contra p;obtain ⟨h1,h4,h5⟩:=aP.1 he
 have hm:e∈(bo n D (bJ n D x c)).erase e1:=mE.2 ⟨λheq=>by
  have:=dJ h.1 he;rw[heq,a3] at this
  exact bF this,gl.2 ⟨h1,⟨h4,p⟩,λhc=>h5 hc.1⟩⟩
 rw[a1,mS] at hm;exact hne hm
lemma pq (hS:aV n D){c:Fin n}(hM:bi n D (ba n D {c})=∅){e:A0}(he:e.1<D.length)(ht:bf D e.1=true)(hc:c∈O n D (W D e)):e∈aG n D c:=
 aP.2 ⟨he,hc,λhc2=>by
  have:=(eT hS hM he hc2).1
  rw[ht] at this
  exact Bool.noConfusion this⟩
lemma kh (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:dz n D b){m:P0}(a8:m∈aR n D b)(X:Finset (Fin n))(hX:X.Nonempty)(k:∀x∈X,bi n D (ba n D {x})=∅/\x∈O n D m.1/\∀u∈aR n D b,x∈O n D u.1->u=m):∃P Q:A0,P.1≠Q.1/\∀x∈X,P∈aG n D x/\Q∈aG n D x:=by
 have hS:=h.1;have a0:m∈cq n D:=(mF.mp (mD.mp a8).1).1;have p:2≤aS D m.1:=(by have:=(dh.mp a0).2;omega);refine lK hG h hC X hX (λx hx=>(k x hx).1) m.1
  (λx hx=>(k x hx).2.1) p ?_
 intro x hx w b0 l;obtain ⟨-,a5,r⟩:=k x hx;have bm:x∈aW n D:=gq.2 ⟨m.1,p,a5⟩;by_contra hc;have a7:(⟨w,0⟩:P0)∈dr n D:=(by rw[dr,mF,dh];exact ⟨⟨cz.mpr (ew hS (w:=w) Y),by show 0+1<aS D w;omega⟩,⟨x,l⟩⟩);by_cases a6:(⟨w,0⟩:P0)∈dD n D b
 ·obtain ⟨v,hv,a4⟩:=mM.mp a6;have a3:b v=w:=kA Sigma.fst a4;have a1:=(hb v hv).2.1;rw[a3] at a1;rw[a1,mS] at l;have a2:=(hb x bm).2.2.2 m.1 p a5;rw[l,a3] at a2;omega
 ·have h1:=r _ (mD.mpr ⟨a7,a6⟩) l
  have:w=m.1:=kA Sigma.fst h1
  omega
lemma ph (p:bI G)(h:a9 n D)(m:bG n G D)(b:Fin n->Nat)(hb:cn n D b){l:Fin n->A0}(k:ch n G D l)(T J:Finset (Fin n))(A:Fin n->Finset (Fin n))(r:∀i∈J,i∈aN n D/\(∃a∈T,G i a)/\∀f∈T,∃a∈A f,G i a)(hA:∀f∈T,(∀a∈A f,∀b∈A f,¬G a b)/\T.erase f⊆A f/\∃a∈A f,G f a)(F:Finset (Finset (Fin n)))(hF:∀M∈F,2≤M.card/\bq n D T M):J.card+F.card+(aW n D).card≤T.card+br n D:=by have h1:=kB p h.1 m k T J A r hA;have h2:=fy h.1 T F hF;have h3:(dk n D T).card≤(bi n D (ba n D T)).card:=cL (fS _ _);have h4:=d9 h T (by rw[dV p m];simp);have h5:=eN h.1 b hb T;have h6:=cL (iL:T∩aW n D⊆T);omega
end L3bGen
section L3bTri
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : aJ}
lemma oy (hG:bI G)(h:a9 n D)(hC:bG n G D)(b:Fin n->Nat)(hb:cn n D b){a5:Fin n->A0}(b2:ch n G D a5)(T J:Finset (Fin n))(A:Fin n->Finset (Fin n))(hJ:∀i∈J,i∈aN n D/\(∃a∈T,G i a)/\∀f∈T,∃a∈A f,G i a)(hA:∀f∈T,(∀a∈A f,∀b∈A f,¬G a b)/\T.erase f⊆A f/\∃a∈A f,G f a)(F:Finset (Finset (Fin n)))(hF:∀M∈F,M.card=2/\bq n D T M)(ez:T.card=3)(fz:T.card+br n D≤J.card+F.card+(aW n D).card):(∀w,¬T⊆O n D w)/\(∀t∈T,bi n D (ba n D {t})=∅/\∃e1,∀e∈aG n D t,e=e1\/e∈J.image a5)/\∀u∈aR n D b,(O n D u.1∩T).Nonempty:=by
 classical
 have hS:=h.1;obtain ⟨b6,a0⟩:=gh b2 T J (λi hi=>⟨(hJ i hi).1,(hJ i hi).2.1⟩);have fi:∀f∈T,∃e:A0,e.1<D.length/\bf D e.1=true/\f∈O n D (W D e)/\f∉O n D (n+e.1)/\Disjoint (O n D (W D e)) (A f):=(by intro f m;obtain ⟨j,s,h1,h2,h4,h5,h6⟩:=fq hG hS hC (A f) (hA f m).1 f (hA f m).2.2;exact ⟨(j,s),h1,h2,h4,h5,h6⟩)
 choose! w hw using fi
 have ca:iO w T:=by
  intro f m g p ej;by_contra fl;exact dL.1 (hw f m).2.2.2.2 (ej▸(hw g p).2.2.1)
   ((hA f m).2.1 (mE.2 ⟨λh=>fl h.symm,p⟩))
 have b5:Disjoint (J.image a5) (T.image w):=by
  rw[dL];intro e r a2;obtain ⟨i,hi,rfl⟩:=mM.1 r;obtain ⟨f,m,a6⟩:=mM.1 a2;obtain ⟨a,ha,e5⟩:=(hJ i hi).2.2 f m;exact dL.1 (hw f m).2.2.2.2
   (a6▸(b2.1 i (hJ i hi).1).2.2.1 a e5) ha
 have a1:T.image w⊆bo n D (ba n D T):=by
  intro e he;obtain ⟨f,m,rfl⟩:=mM.1 he;obtain ⟨h1,h2,h4,h5,h6⟩:=hw f m;refine e6.2 ⟨h1,⟨f,mN.2 ⟨h4,m⟩⟩,?_⟩;rintro ⟨g,p⟩;rw[mN] at p;have e4:g∈O n D (W D (w f)):=de hS h1 h2 (w f).2 p.1;exact dL.1 h6 e4
   ((hA f m).2.1 (mE.2 ⟨λh=>h5 (h▸p.1),p.2⟩))
 have c3:∀M∈F,2≤M.card/\bq n D T M:=λM hM=>⟨by rw[(hF M hM).1],(hF M hM).2⟩;have h2:=fy hS T F c3;have h3:(dk n D T).card≤(bi n D (ba n D T)).card:=cL (fS _ _);have h4:=d9 h T (by rw[dV hG hC];simp);have h5:=eN hS b hb T;have h6:=cL (iL:T∩aW n D⊆T);have fc:=cL (uS b6 a1);rw[cU b5,a0,cJ ca] at fc
 have c0:J.image a5∪T.image w=bo n D (ba n D T):=eS (uS b6 a1) (by
   rw[cU b5,a0,cJ ca];omega)
 have cb:dk n D T=bi n D (ba n D T):=eS (fS _ _) Y;have l:∀w',¬T⊆O n D w':=by
  intro w' et;have d0:T∉F:=λhTF=>by have:=(hF T hTF).1;omega
  have:=fy hS T (insert T F) (λM hM=>by
   rcases mI.1 hM with rfl|hM
   ·exact ⟨Y,⟨w',qR.2 et⟩⟩
   ·exact c3 M hM)
  rw[cI d0] at this;omega
 have a7:∀u∈aR n D b,(O n D u.1∩T).Nonempty:=by
  have h7:=iU hS b hb T;have h8:=dd hS b hb;have er:(aR n D b).filter (λu=>(O n D u.1∩T).Nonempty) =
    aR n D b:=
   eS (fS _ _) Y
  intro u hu;rw[← er] at hu;exact (mF.1 hu).2
 have ct:iO (λj=>O n D (n+j)∩T) (dk n D T):=(by have c2:F⊆(dk n D T).image (λj=>O n D (n+j)∩T):=(by intro M hM;obtain ⟨j,hj,e0⟩:=jU hS (c3 M hM).1 (hF M hM).2;exact mM.2 ⟨j,hj,e0⟩);have:=cL c2;exact card_image_iff.1 (le_antisymm cG Y));have k:∀{t:Fin n} {v:Nat},t∈T->t∈O n D v->v∈ba n D T:=λht hv=>dO.2 ⟨_,mN.2 ⟨hv,ht⟩⟩;refine ⟨l,λt ht=>⟨?_,w t,λe he=>?_⟩,a7⟩
 ·rw[eF];intro j hj;rw[bi,mF,mR] at hj;obtain ⟨es,d1,c1,c5⟩:=hj;rw[dp] at d1 c1 c5;have a4:j∈dk n D T:=by
   rw[cb,bi,mF,mR];exact ⟨es,k ht d1,k ht c1,k ht c5⟩
  have bm:2≤(O n D (n+j)∩T).card:=(mF.1 a4).2;obtain ⟨j0,-,-,b8,b0,-,ea⟩:=ga hS T _ bm (n+j) rfl;have eu:j0=j:=ct (mF.2 ⟨b0,by rw[b8];exact bm⟩) a4 b8;subst eu;have d2:∀v,(O n D v∩T).card<3:=(by intro v;by_contra hc;exact l v (qR.1 (eS iR Y)));rcases ea with ⟨-,c7,-⟩|⟨-,c7,e3,hU,-,-⟩
  ·have:=al c7;have:=d2 (aZ D j0);omega
  ·have f1:=al c7;have f0:=al e3;have:=d2 (n+j0);have e7:({t}:Finset (Fin n))=O n D (aZ D j0)∩T:=eS
     (sS.2 (mN.2 ⟨c1,ht⟩))
     (by rw[cS];omega)
   have ev:({t}:Finset (Fin n))=O n D (aY D j0)∩T:=eS
     (sS.2 (mN.2 ⟨c5,ht⟩))
     (by rw[cS];omega)
   rw[← hU,← e7,← ev,union_self,cS] at bm;omega
 ·obtain ⟨r,a2,e2⟩:=aP.1 he;have b1:=dJ hS he;have a3:e∈bo n D (ba n D T):=by
   refine e6.2 ⟨r,⟨t,mN.2 ⟨a2,ht⟩⟩,?_⟩;rintro ⟨g,p⟩;rw[mN] at p;have c8:∀s,g∈O n D (W D (e.1,s)):=λs=>de hS r b1 s p.1;have a4:e.1∈dk n D T:=by
    rw[cb,bi,mF,mR];refine ⟨r,k p.2 p.1,k p.2 ?_,k p.2 ?_⟩
    ·have:=c8 false;rwa[bP] at this
    ·have:=c8 true;rwa[bU] at this
   have bm:2≤(O n D (n+e.1)∩T).card:=(mF.1 a4).2
   have c6:O n D (n+e.1)∩T⊆T.erase t:=λa ha=>
    mE.2 ⟨λa8=>e2 (a8▸(mN.1 ha).1),(mN.1 ha).2⟩
   have ec:=eS c6
    (by rw[cE ht,ez];omega)
   apply l (W D e);intro a ha;by_cases a8:a=t
   ·rw[a8];exact a2
   ·have:a∈O n D (n+e.1)∩T:=by
     rw[ec];exact mE.2 ⟨a8,ha⟩
    exact de hS r b1 e.2 (mN.1 this).1
  rw[← c0,mU] at a3;rcases a3 with h1|h1
  ·exact oR h1
  ·obtain ⟨f,m,a6⟩:=mM.1 h1;left;by_cases eb:f=t
   ·rw[← a6,eb]
   ·exfalso;exact dL.1 (hw f m).2.2.2.2 (a6▸a2)
     ((hA f m).2.1 (mE.2 ⟨λh=>eb h.symm,ht⟩))
end L3bTri
abbrev HG:F0->F0->Prop:=λu v=>aH u v
def ru (D:aJ)(b:F0->Nat)(x:F0):Finset (P0):=
 (aR 14 D b).filter (λu=>x∈O 14 D u.1)
lemma bb {D:aJ}{b:F0->Nat}{x:F0}{u:P0}:u∈ru D b x<->u∈aR 14 D b/\x∈O 14 D u.1:=mF
lemma mu {n:Nat}{D:aJ}{b:Fin n->Nat}{u:P0}(h:u∈aR n D b):2≤aS D u.1:=by have:=(dh.mp (mF.mp (mD.mp h).1).1).2;omega
lemma eQ {n:Nat}{D:aJ}{b:Fin n->Nat}{u:P0}(hu:u∈aR n D b){x:Fin n}(hx:x∈O n D u.1):x∈aW n D:=
 gq.2 ⟨u.1,mu hu,hx⟩
lemma ci {D:aJ}(h:a9 14 D)(l:be D)(b:F0->Nat)(m:cn 14 D b)(x:F0):(aG 14 D x).card+(bi 14 D (ba 14 D {x})).card≤2+(ru D b x).card:=by
 have p:=ff bn h (bl l) b m x;have k:=cL
  (iL:({x}:S0)∩aW 14 D⊆{x})
 rw[cS] at k;unfold ru;omega
lemma fx {D:aJ}(h:a9 14 D)(m:be D)(b:F0->Nat)(p:cn 14 D b){x:F0}(k:x∈aW 14 D):(aG 14 D x).card+(bi 14 D (ba 14 D {x})).card=2+(ru D b x).card:=by have l:=ff bn h (bl m) b p x;rw[qL.2 (sS.2 k),cS] at l;unfold ru;omega
lemma gf {n:Nat}{D:aJ}(k:aV n D){x:Fin n}{e:A0}(m:e∈aG n D x):aI e∉aG n D x:=by
 intro hb;obtain ⟨r,l,p⟩:=aP.mp m;have h:=(aP.mp hb).2.1;apply p;rw[dC k r (dJ k m),mN];obtain ⟨j,s⟩:=e;cases s
 ·exact ⟨by simpa[W] using l,by simpa[W,aI] using h⟩
 ·exact ⟨by simpa[W,aI] using h,by simpa[W] using l⟩
section Assigned
variable {D : aJ} {pos : Fin 14 → Nat × Bool}
lemma bd (h:ch 14 HG D pos){i a:F0}(l:i∈aN 14 D)(k:aH i a):pos i∈aG 14 D a:=by obtain ⟨r,m,p,-⟩:=h.1 i l;exact aP.2 ⟨r,p a k,by rw[m];exact nE a⟩
lemma bx (h:ch 14 HG D pos){i t:F0}(l:i∈aN 14 D)(k:aI (pos i)∈aG 14 D t):t=i:=by have:=(aP.1 k).2.1;rw[show W D (aI (pos i))=W D ((pos i).1,!(pos i).2) from rfl,(h.1 i l).2.2.2] at this;exact mS.1 this
lemma fj (h:a9 14 D)(hD:be D)(k:ch 14 HG D pos){i:F0}(l:i∈aN 14 D):aG 14 D i={aI (pos i)}:=by
 obtain ⟨e,-,-,h3,-,-,p,-⟩:=eJ bn h (bl hD) l;obtain ⟨h1,r,-,h5⟩:=k.1 i l
 have m:aI (pos i)∈aG 14 D i:=aP.2 ⟨h1,by
  rw[show W D (aI (pos i))=W D ((pos i).1,!(pos i).2) from rfl,h5];exact mX i,by
  rw[show (aI (pos i)).1=(pos i).1 from rfl,r];exact nE i⟩
 have h7:aG 14 D i={e}:=p;rw[h7] at m ⊢;rw[mS.1 m]
lemma ps (h:a9 14 D)(hD:be D)(k:ch 14 HG D pos){i x:F0}(m:i∈aN 14 D)(l:x≠i)(hY:pos i∈aG 14 D x)(hc:(aG 14 D x).card≤2):∃Z,Z≠pos i/\aG 14 D x={pos i,Z}/\∀t,t≠x->Z∉aG 14 D t:=by
 obtain ⟨Z,r,p,h3,-⟩:=kL h hD m l (fj h hD k m)
  (by rw[aT];exact hY) hc
 rw[aT] at r p;exact ⟨Z,r,p,h3⟩
end Assigned
def tA (T:S0)(f:F0):S0:=
 T.erase f∪univ.filter
  (λa=>aQ f a=true/\∀g∈T.erase f,aQ a g=false)
def dU (T J:S0):Bool:=
 decide (∀i∈J,(∃a∈T,aQ i a=true)/\
  ∀f∈T,∃a∈tA T f,aQ i a=true) &&
 decide (∀f∈T,(∀a∈tA T f,∀b∈tA T f,aQ a b=false)/\
  ∃a∈tA T f,aQ f a=true) &&
 decide (T.card=3/\J.card=3) &&
 decide (∀i∈J,T⊆bX 0/\T⊆bX i/\aX i⊆bX 0/\
  (aX i∩T).card=2) &&
 decide (∀i∈J,∀j∈J,aX j∩T⊆aX i∩T->j=i) &&
 decide (∀t∈T,(J.filter (λi=>aQ i t=true)).card≤2/\
  ∀i∈J,aQ i t=false->T.erase t⊆aX i)
lemma gr {T J:S0}(h:dU T J=true):(∀i∈J,(∃a∈T,aQ i a=true)/\∀f∈T,∃a∈tA T f,aQ i a=true)/\(∀f∈T,(∀a∈tA T f,∀b∈tA T f,aQ a b=false)/\∃a∈tA T f,aQ f a=true)/\(T.card=3/\J.card=3)/\(∀i∈J,T⊆bX 0/\T⊆bX i/\aX i⊆bX 0/\(aX i∩T).card=2)/\(∀i∈J,∀j∈J,aX j∩T⊆aX i∩T->j=i)/\∀t∈T,(J.filter (λi=>aQ i t=true)).card≤2/\∀i∈J,aQ i t=false->T.erase t⊆aX i:=by simpa only [dU,bA,dT,and_assoc] using h
lemma gp {D:aJ}{T J:S0}(h:dU T J=true)(m:∀i∈J,i∈aN 14 D):(∀i∈J,i∈aN 14 D/\(∃a∈T,HG i a)/\∀f∈T,∃a∈tA T f,HG i a)/\∀f∈T,(∀a∈tA T f,∀b∈tA T f,¬HG a b)/\T.erase f⊆tA T f/\∃a∈tA T f,HG f a:=by
 obtain ⟨k,l,-⟩:=gr h
 exact ⟨λi hi=>⟨m i hi,(k i hi).1.imp (λ_ ha=>⟨ha.1,(aK _ _).1 ha.2⟩),λf hf=>((k i hi).2 f hf).imp (λ_ ha=>⟨ha.1,(aK _ _).1 ha.2⟩)⟩,
 λf hf=>⟨λa ha b hb=>bw.1 ((l f hf).1 a ha b hb),subset_union_left,(l f hf).2.imp (λ_ ha=>⟨ha.1,(aK _ _).1 ha.2⟩)⟩⟩
lemma iA {D:aJ}(h:a9 14 D)(hD:be D)(hz:bu 14 D≤1){T J:S0}(a1:dU T J=true)(hJ:∀i∈J,i∈aN 14 D):(aW 14 D).card+3≤br 14 D:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨b,hb⟩:=dY h hD;obtain ⟨a5,p⟩:=cR hG h hC;obtain ⟨a3,a4⟩:=gp a1 hJ;obtain ⟨-,-,⟨a7,a6⟩,hside,hinj,-⟩:=gr a1;have hM:∀i∈J,∃M,bq 14 D T M/\aX i∩T⊆M/\(bq 14 D (bX 0) (aX i)->M=aX i∩T):=by
  intro i k;by_cases hx:bq 14 D (bX 0) (aX i)
  ·obtain ⟨w,hw⟩:=hx
   have:O 14 D w∩T=aX i∩T:=(by rw[← hw,inter_assoc,qR.2 (hside i k).1])
   exact ⟨_,⟨w,rfl⟩,this▸Subset.refl _,λ_=>this⟩
  ·exact ⟨O 14 D (W D (a5 i))∩T,⟨_,rfl⟩,λa ha=>by
    rw[mN,ce] at ha
    exact mN.2 ⟨(p.1 i (hJ i k)).2.2.1 a ha.1,ha.2⟩,
    λhc=>absurd hc hx⟩
 choose! M hM using hM
 have a2:=iK h hD (bX 0) (eg 0)
  (J.filter (λi=>¬bq 14 D (bX 0) (aX i))) (λi k=>by
   rw[mF] at k
   exact ⟨hJ i k.1,(hside i k.1).2.2.1,k.2⟩)
 have r:iO M J:=by
  intro i k j hj m;by_contra l;have a0:∀i∈J,∀j∈J,M i=M j->i≠j->¬bq 14 D (bX 0) (aX i):=by
   intro i k j hj m l hx
   exact l (hinj i k j hj (by
    rw[← (hM i k).2.2 hx,m];exact (hM j hj).2.1)).symm
  have h1:i∈J.filter (λi=>¬bq 14 D (bX 0) (aX i)):=mF.2 ⟨k,a0 i k j hj m l⟩;have h2:j∈J.filter (λi=>¬bq 14 D (bX 0) (aX i)):=mF.2 ⟨hj,a0 j hj i k m.symm (nS l)⟩;have:=oC.2 ⟨i,h1,j,h2,l⟩;omega
 have:=ph hG h hC b hb p T J (tA T) a3 a4 (J.image M) (λX hX=>by
  obtain ⟨i,k,rfl⟩:=mM.1 hX;have:=cL (hM i k).2.1;rw[(hside i k).2.2.2] at this
  exact ⟨this,(hM i k).1⟩)
 rw[cJ r] at this;omega
lemma gH {D:aJ}(h:a9 14 D)(hD:be D)(l:∀i∈({0,1,2}:S0),i∈aN 14 D):(aW 14 D).card+2≤br 14 D:=by
 have hG:=bn;have hC:=bl hD;obtain ⟨b,hb⟩:=dY h hD;obtain ⟨a0,k⟩:=cR hG h hC;have p:dU {7,8,13} {0,1,2}=true:=aa
 obtain ⟨m,r⟩:=gp p l;have h0:=(k.1 0 (l 0 o)).2.2.1;have h1:=(k.1 1 (l 1 o)).2.2.1;have:=jL hG h hC b hb k {7,8,13} {0,1,2} (tA {7,8,13}) m r rfl
  o o o (h0 7 o) (h0 8 o)
  (h1 7 o) (h1 13 o)
 rw[show ({0,1,2}:S0).card=3 from rfl] at this;omega
def co (c v:F0):Option Bool:=
 if v=c then some true else if aQ c v=true then some false else none
def cK (l:List Nat)(k:Fin 10):F0:=Fin.ofNat 14 (l.getD k.val 0)
abbrev gA (c:F0)(l:List Nat):Prop:=
 (∀a b:Fin 10,cK l a=cK l b->a=b)/\
 (∀v:F0,co c v=none<->∃i:Fin 10,cK l i=v)/\
 ∀u v:Fin 10,aQ (cK l u) (cK l v)=fP u v
def mT:List Nat:=[2,4,5,6,13,12,8,10,11,9]
lemma kR:gA 7 mT:=aa
lemma nh {D:aJ}(h:a9 14 D)(hD:be D)(b:F0->Nat)(hb:cn 14 D b){c:F0}{l:List Nat}(a5:gA c l)(hc:c∈aW 14 D)(X:S0)(hX:∀x∈X,x∈aW 14 D/\x≠c/\(∀u∈aR 14 D b,x∈O 14 D u.1->c∈O 14 D u.1)/\∃w,x∈O 14 D w/\c∈O 14 D w):∃E:aJ,a9 10 E/\bG 10 eZ E/\bH 10 E+((ru D b c).card+X.card+1)≤bH 14 D/\br 10 E+((ru D b c).card+X.card+1)≤bH 14 D/\∀i:Fin 10,(∀w,rG (bk 14 D) (cK l i).val w->aS D w≤1)->i∈aN 10 E:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨bm,a4,b5⟩:=a5;have b8:dA (co c) (cK l):=⟨λa b hab=>bm a b hab,a4⟩;have hρc:co c c=some true:=by simp[co]
 have hT:∀d a:F0,co c d=some true->HG d a->co c a=some false:=by
  intro d a h1 h2;have hd:d=c:=by
   by_contra a8;unfold co at h1;simp only[a8,iF] at h1
   split at h1<;>simp at h1
  subst hd;have a8:a≠d:=λhac=>bW d (hac▸h2);simp[co,a8,(aK d a).2 h2]
 have b0:(λu v:Fin 10=>HG (cK l u) (cK l v))=eZ:=by
  funext u v
  exact propext (by
   show aH _ _<->fP u v=true
   rw[← b5 u v];exact (aK _ _).symm)
 obtain ⟨E,hE,c5,c8,cb,a6⟩:=kP hS b8 hC
  (λ_ _ huv=>bh huv) hT (by rw[b0];exact fR) (by norm_num)
 have b1:∀x∈aW 14 D,(⟨b x,0⟩:P0)∈cq 14 D:=λx k=>
  dh.2 ⟨cz.2 (ew hS (w:=b x) (by
   have:=(hb x k).1;omega)),by
   show 0+1<aS D (b x);have:=(hb x k).1;omega⟩
 have a0:∀x∈insert c X,x∈aW 14 D:=λx k=>by
  rcases mI.1 k with rfl|k
  ·exact hc
  ·exact (hX x k).1
 have r:iO (λx=>(⟨b x,0⟩:P0))
   (insert c X:S0):=by
  intro x k y hy c3;have h1:b x=b y:=kA Sigma.fst c3;have h2:=(hb x (a0 x k)).2;rw[h1,(hb y (a0 y hy)).2] at h2;exact (sJ h2).symm
 have b2:Disjoint (ru D b c)
   ((insert c X).image (λx=>(⟨b x,0⟩:P0))):=by
  rw[dL];intro u c0 c1;obtain ⟨x,k,rfl⟩:=mM.1 c1;exact (mD.1 (bb.1 c0).1).2 (mM.2 ⟨x,a0 x k,rfl⟩)
 have a1:ru D b c∪(insert c X).image (λx=>(⟨b x,0⟩:P0))⊆
   cq 14 D:=by
  intro u m;rcases mU.1 m with m|m
  ·exact (mF.1 (mD.1 (bb.1 m).1).1).1
  ·obtain ⟨x,k,rfl⟩:=mM.1 m;exact b1 x (a0 x k)
 have p:∀u∈ru D b c∪(insert c X).image (λx=>(⟨b x,0⟩:P0)),u∉fb D (co c) (cK l):=by
  intro u m;rcases mU.1 m with m|m
  ·exact iu hS hρc (bb.1 m).2
  ·obtain ⟨x,k,rfl⟩:=mM.1 m;rcases mI.1 k with rfl|k
   ·exact iu hS hρc (by
     show x∈O 14 D (b x)
     rw[(hb x hc).2];exact mX x)
   ·obtain ⟨a7,a2,b6,w,hw⟩:=hX x k;obtain ⟨z,ca,ct⟩:=hG.2.2.1 x c a2;obtain ⟨c7,-,-,e,he,-,c2⟩:=jq hG h hC b hb a2 a7 b6 hw ca ct
    have c6:b x∈bJ 14 D x c:=gB.2 (by
     rw[(hb x a7).2]
     exact ⟨mX x,λhcx=>a2 (mS.1 hcx).symm⟩)
    exact kN (jN hS hρc c6 (hb x a7).1 c7 he c2)
 have a3:(ru D b c∪(insert c X).image (λx=>(⟨b x,0⟩:P0))).card =
   (ru D b c).card+X.card+1:=by
  rw[cU b2,cJ r,cI (λhcX=>(hX c hcX).2.1 rfl)];omega
 have h1:=oh _ a1 p;have h2:=ly _ a1 (λu m hk=>p u m (iq hk));rw[a3] at h1 h2;exact ⟨E,hE,b0▸c5,Y,Y,a6⟩
lemma jO {D:aJ}(h:a9 14 D)(hD:be D)(b:F0->Nat)(r:cn 14 D b){c:F0}{l:List Nat}(k:gA c l)(hc:c∈aW 14 D)(X:S0)(p:∀x∈X,x∈aW 14 D/\x≠c/\(∀u∈aR 14 D b,x∈O 14 D u.1->c∈O 14 D u.1)/\∃w,x∈O 14 D w/\c∈O 14 D w):(ru D b c).card+X.card+7≤bH 14 D:=by obtain ⟨E,hE,m,-,h2,-⟩:=nh h hD b r k hc X p;have:=kM hE m;omega
lemma eq {α:Type}[DecidableEq α]{s:Finset α}{a b c:α}(ha:a∈s)(hb:b∈s)(r:c∈s)(m:a≠b)(k:a≠c)(l:b≠c):3≤s.card:=by have h:({a,b,c}:Finset α)⊆s:=(by intro e p;simp only[mI,mS] at p;rcases p with rfl|rfl|rfl<;>assumption);have:=cL h;rwa[cI (by simp[m,k]),cP l] at this
lemma ft {α:Type}[DecidableEq α]{s:Finset α}{a b c:α}(ha:a∈s)(r:b∈s)(hc:c∈s)(m:a≠b)(k:a≠c)(l:b≠c)(hs:s.card≤3):∀e∈s,e=a\/e=b\/e=c:=by
 intro e p;by_contra h;rw[nO,nO] at h;have:=eq (s:=s.erase e) (mE.2 ⟨nS h.1,ha⟩)
  (mE.2 ⟨nS h.2.1,r⟩) (mE.2 ⟨nS h.2.2,hc⟩)
  m k l
 rw[cE p] at this;omega
lemma jC {α:Type}[DecidableEq α]{s:Finset α}{a b:α}(m:a∈s)(p:b∈s)(k:a≠b)(r:s.card≤2):∀e∈s,e=a\/e=b:=by intro e l;by_contra h;rw[nO] at h;have:=eq l m p h.1 h.2 k;omega
lemma nm:∀i k t:F0,aQ i k=true->t≠i->∃q,aQ i q=true/\q≠k/\q≠t/\aQ t q=false:=aa
lemma gG {D:aJ}(h:a9 14 D)(hD:be D){x a b:F0}(m:x≠a)(l:x≠b)(r:¬aH a b)(k:∀e∈aG 14 D x,e∈aG 14 D a\/e∈aG 14 D b):False:=by
 obtain ⟨e,he,h1,h2⟩:=bB h hD m l r;rcases k e he with p|p
 exacts [h1 (aP.1 p).2.1,h2 (aP.1 p).2.1]
lemma fh {D:aJ}(h:a9 14 D)(hD:be D){l:F0->A0}(k:ch 14 HG D l){x y:F0}(m:aH x y):∃e∈aG 14 D x,aI e∈aG 14 D y/\(∀i∈aN 14 D,e=l i->y=i)/\∀i∈aN 14 D,aI e=l i->x=i:=by obtain ⟨e,r,p,-⟩:=bp bn h.1 (bl hD) m;exact ⟨e,r,p,λi hi hei=>bx k hi (hei▸p),λi hi hei=>bx k hi (by rw[← hei,aT];exact r)⟩
def jT (D:aJ)(pos:F0->A0)(P Q:A0):Prop:=
 ch 14 HG D pos/\(∀x,(aG 14 D x).card≤3)/\P≠Q/\
  ∀x,3≤(aG 14 D x).card->P∈aG 14 D x/\Q∈aG 14 D x
lemma kZ {D:aJ}(h:a9 14 D)(hD:be D)(a1:br 14 D≤13)(h0:(0:F0)∈aN 14 D)(hp:(aW 14 D).card=12):∃pos P Q,jT D pos P Q:=by
 classical
 have hG:=bn;have r:=bl hD;obtain ⟨b,hb⟩:=dB hG h.1 r;have l:=cX hb;obtain ⟨pos,k⟩:=cR hG h r;have h1:=dd h.1 b l;have hB:br 14 D=13:=(by by_contra a2;exact js h hD Y h0);have m:∀x,(aG 14 D x).card≤3:=λx=>by
  have h3:=ci h hD b l x;have h4:(ru D b x).card≤(aR 14 D b).card:=cF _ _;omega
 by_cases hX:(univ.filter (λx:F0=>3≤(aG 14 D x).card)).Nonempty
 ·obtain ⟨P,Q,a0,p⟩:=fw hG h r b hb Y _ hX
   (λx hx=>(mF.1 hx).2)
  exact ⟨pos,P,Q,k,m,λhpq=>a0 (hpq▸rfl),λx hx=>p x (mF.2 ⟨mV x,hx⟩)⟩
 ·exact ⟨pos,(0,false),(1,false),k,m,o,λx hx=>(hX ⟨x,mF.2 ⟨mV x,hx⟩⟩).elim⟩
lemma mr {D:aJ}(h:a9 14 D)(hD:be D)(c0:br 14 D≤13)(hI:aN 14 D={0,1}):False:=by
 have c6:=db 14 D;rw[hI,show ({0,1}:S0).card=2 from rfl] at c6;have m:(0:F0)∈aN 14 D:=by rw[hI];decide
 have r:(1:F0)∈aN 14 D:=by rw[hI];decide
 have a2:∀x:F0,x∉({0,1}:S0)->x∉aN 14 D:=λx hx=>hI▸hx;have bm:∀i∈aN 14 D,aH i 7:=by rw[hI];decide
 obtain ⟨a1,P,Q,k,b2,c8,a6⟩:=kZ h hD c0 m Y;have y7:=λi hi=>bd k hi (bm i hi);have b1:a1 0≠a1 1:=λp=>absurd (k.2 0 m 1 r p) o;obtain ⟨H,hH,-,b6,-⟩:=fh h hD k (show aH 7 3 by decide);obtain ⟨c7,c2⟩:=a6 7 (eq (y7 0 m) (y7 1 r) hH b1 (λp=>absurd (b6 0 m p.symm) o) (λp=>absurd (b6 1 r p.symm) o));have hS:∀t,3≤(aG 14 D t).card->∀j∈aN 14 D,a1 j∈aG 14 D t:=by
  intro t ht j hj;by_contra hn;obtain ⟨hP,hQ⟩:=a6 t ht
  obtain ⟨q,c5,c3,-,ct⟩:=nm j 7 t ((aK _ _).2 (bm j hj)) (λhti=>by
   rw[hti,fj h hD k hj,cS] at ht
   omega)
  refine gG h hD (λe:(7:F0)=t=>hn (e▸y7 j hj)) c3.symm
   (bw.1 ct) (λe p=>?_)
  rcases ft (y7 j hj) c7 c2 (λe=>hn (e▸hP)) (λe=>hn (e▸hQ)) c8
   (b2 7) e p with rfl|rfl|rfl
  exacts [oR (bd k hj ((aK _ _).1 c5)),oL hP,oL hQ]
 have a3:∀l i z:F0,i∈aN 14 D->aH i l->aH l z->z∉aN 14 D->∃Z∈aG 14 D l,(∀e∈aG 14 D l,e=Z\/∃j∈aN 14 D,e=a1 j)/\∀y,aH l y->y∉aN 14 D->aI Z∈aG 14 D y:=by
  intro l i z hi c1 d0 hz;obtain ⟨Z,hZ,-,d1,-⟩:=fh h hD k d0;have a0:∀j∈aN 14 D,a1 j≠Z:=λj hj p=>hz (d1 j hj p.symm▸hj);have b0:∀e∈aG 14 D l,e=Z\/∃j∈aN 14 D,e=a1 j:=by
   intro e p;by_cases h3:3≤(aG 14 D l).card
   ·rcases ft (hS l h3 0 m) (hS l h3 1 r) hZ b1 (a0 0 m) (a0 1 r)
     (b2 l) e p with h1|h1|h1
    exacts [oR ⟨0,m,h1⟩,oR ⟨1,r,h1⟩,oL h1]
   ·rcases jC (bd k hi c1) hZ (a0 i hi) Y e p with h1|h1
    exacts [oR ⟨i,hi,h1⟩,oL h1]
  refine ⟨Z,hZ,b0,λy hly hy=>?_⟩;obtain ⟨e,p,hb,hf,-⟩:=fh h hD k hly;rcases b0 e p with rfl|⟨j,hj,rfl⟩
  exacts [hb,(hy (hf j hj rfl▸hj)).elim]
 have e2:=a2 2 o;obtain ⟨Z8,cb,a8,b8⟩:=a3 8 0 2 m o o e2;obtain ⟨Z13,a4,-,b5⟩:=a3 13 1 2 r o o e2;have m8:=b8 2 o e2;have ca:=b5 2 o e2;have a7:aI Z8≠aI Z13:=by
  intro p;have hZ:Z8=Z13:=by rw[← aT Z8,p,aT]
  refine gG h hD (by decide:(8:F0)≠7) (by decide:(8:F0)≠13)
   o (λe p=>?_)
  rcases a8 e p with rfl|⟨j,hj,rfl⟩
  exacts [oR (hZ▸a4),oL (y7 j hj)]
 have a5:∀(Z:A0) (l i:F0),Z∈aG 14 D l->i∈aN 14 D->l∉({0,1}:S0)->a1 i≠aI Z:=λZ l i hZ hii hl p=>
  a2 l hl (bx k hii (by rw[p,aT];exact hZ)▸hii)
 by_cases h3:3≤(aG 14 D 2).card
 ·rcases ft (hS 2 h3 0 m) (hS 2 h3 1 r) m8 b1 (a5 Z8 8 0 cb m o)
   (a5 Z8 8 1 cb r o) (b2 2) _ ca with h1|h1|h1
  exacts [a5 Z13 13 0 a4 m o h1.symm,a5 Z13 13 1 a4 r o h1.symm,a7 h1.symm]
 ·exact gG h hD (by decide:(2:F0)≠6) (by decide:(2:F0)≠4)
   o (λe p=>by
    rcases jC m8 ca a7 Y e p with rfl|rfl
    exacts [oL (b8 6 o (a2 6 o)),oR (b5 4 o (a2 4 o))])
lemma lL {D:aJ}(h:a9 14 D)(hD:be D){a5:F0->A0}(l:ch 14 HG D a5)(z k v iz ik:F0)(m:(∀a∈({iz,ik}:S0),a∈aN 14 D)/\∀a∈({z,k,v}:S0),a∉aN 14 D)(hg:aQ iz z=true/\aQ ik k=true/\aQ z k=true/\aQ z v=true/\v≠k)(a7:(aG 14 D z).card≤2)(a4:(aG 14 D k).card≤2):False:=by
 obtain ⟨g1,g2,g3,g4,g5⟩:=hg;rw[aK] at g1 g2 g3 g4;have r:=m.1 iz ab;have p:=m.1 ik ab;have hk:=m.2 k ab;obtain ⟨Dk,-,a3,a6⟩:=ps h hD l p (λe:k=ik=>hk (e▸p)) (bd l p g2) a4;obtain ⟨e,he,a0,hf,a2⟩:=fh h hD l g3;obtain ⟨e',a8,a1,bm,-⟩:=fh h hD l g4;rw[a3,mI,mS] at a0;have hb:aI e=Dk:=a0.resolve_left (λhh=>m.2 z ab (a2 ik p hh▸p));rcases jC (bd l r g1) he (λhh=>hk (hf iz r hh.symm▸r)) a7 e' a8
  with h1|h1
 ·exact m.2 v ab (bm iz r h1▸r)
 ·exact a6 v g5 (by rw[← hb,← h1];exact a1)
def fd (D:aJ)(pos:F0->A0)(P Q:A0)(y:F0):Prop:=
 ∃e,(e=P\/e=Q)/\(∀i∈aN 14 D,e≠pos i)/\
  (∀s,s≠y->aI e∉aG 14 D s)/\aI e∈aG 14 D y/\
  ∃i∈aN 14 D,pos i=P\/pos i=Q
lemma iB {D:aJ}(h:a9 14 D)(hD:be D){p:F0->A0}{P Q:A0}(hc:jT D p P Q)(x y t w ix iy xa xb:F0)(a2:(∀a∈({ix,iy}:S0),a∈aN 14 D)/\∀a∈({x,y,w}:S0),a∉aN 14 D)(hg:aQ ix x=true/\aQ iy y=true/\aQ x y=true/\aQ w y=true/\aQ ix t=true/\ix≠iy/\x≠w/\x≠t/\x≠xa/\x≠xb/\aQ w xa=false/\aQ w xb=false/\aQ t xa=false/\aQ t xb=false)(er:3≤(aG 14 D x).card)(c8:3≤(aG 14 D xa).card\/3≤(aG 14 D xb).card):fd D p P Q y:=by
 obtain ⟨k,b5,c0,r⟩:=hc;obtain ⟨g1,g2,g3,g4,g5,g0,g6,g7,g8,g9,ca,b6,b8,b2⟩:=hg;rw[aK] at g1 g2 g3 g4 g5;rw[bw] at ca b6 b8 b2;have a3:=a2.1 ix ab;have l:=a2.1 iy ab;have hx:=a2.2 x ab;have hy:=a2.2 y ab;obtain ⟨u,hu,d0,ea,d2⟩ :
   ∃u,3≤(aG 14 D u).card/\x≠u/\¬aH w u/\¬aH t u:=by
  rcases c8 with hs|hs
  exacts [⟨xa,hs,g8,ca,b8⟩,⟨xb,hs,g9,b6,b2⟩]
 obtain ⟨b0,c1⟩:=r x er;obtain ⟨e,he,a1,hf,cb⟩:=fh h hD k g3;obtain ⟨e',eb,a7,-,ec⟩:=fh h hD k g4;have bm:∀(c:A0) (s:F0),c∈aG 14 D x->c∈aG 14 D s->x≠s->¬aH s u->c=P\/c=Q:=by
  intro c s ej c7 c6 ct;by_contra a4;rw[nO] at a4;refine gG h hD c6 d0 ct (λa ha=>?_);rcases ft b0 c1 ej c0 (nS a4.1) (nS a4.2) (b5 x) a ha with
   rfl|rfl|rfl
  exacts [oR (r u hu).1,oR (r u hu).2,oL c7]
 have a8:=bm (p ix) t (bd k a3 g1) (bd k a3 g5) g7 d2;have hB:(∀c∈aG 14 D y,c=aI e\/∃i∈aN 14 D,c=p i)->e=P\/e=Q:=by
  intro hA;refine bm e w he ?_ g6 ea;rcases hA _ a7 with m|⟨i,hi,m⟩
  ·rw[← aT e,← m,aT];exact eb
  ·exact (a2.2 w ab (ec i hi m▸hi)).elim
 by_cases c5:(aG 14 D y).card≤2
 ·obtain ⟨Dy,-,a0,c2⟩:=ps h hD k l (λe:y=iy=>hy (e▸l)) (bd k l g2) c5;have c3:Dy∈aG 14 D y:=by rw[a0];simp
  have hb:aI e=Dy:=(by rw[a0,mI,mS] at a1;exact a1.resolve_left (λhh=>hx (cb iy l hh▸l)));refine ⟨e,hB (λc hc'=>?_),λi hi hei=>hy (hf i hi hei▸hi),λs hs=>hb▸c2 s hs,hb▸c3,ix,a3,a8⟩;rw[a0,mI,mS] at hc';rcases hc' with m|m
  exacts [oR ⟨iy,l,m⟩,oL (m.trans hb.symm)]
 ·exfalso;obtain ⟨b1,a6⟩:=r y Y;have a0:=ft b1 a6 a1 c0 (λhh=>gf h.1 he (hh▸b0))
   (λhh=>gf h.1 he (hh▸c1)) (b5 y)
  have d1:p iy=P\/p iy=Q:=by
   rcases a0 _ (bd k l g2) with m|m|m
   exacts [oL m,oR m,(hx (cb iy l m.symm▸l)).elim]
  have a4:p ix≠p iy:=λhh=>g0 (k.2 ix a3 iy l hh);have a5:∀X,X=P\/X=Q->∃i∈aN 14 D,X=p i:=by
   intro X hX;rcases hX with rfl|rfl<;>rcases a8 with m|m<;>rcases d1 with h2|h2<;>
    first
     | exact ⟨ix,a3,m.symm⟩
     | exact ⟨iy,l,h2.symm⟩
     | exact (a4 (m.trans h2.symm)).elim
  rcases hB (λc hc'=>(a0 c hc').elim (λm=>oR (a5 c (oL m))) (λm=>m.elim (λh2=>oR (a5 c (oR h2))) oL)) with rfl|rfl
  exacts [gf h.1 b1 a1,gf h.1 a6 a1]
lemma ms {D:aJ}{h:F0->A0}{P Q:A0}{y1 y2:F0}(a3:y1≠y2)(c1:fd D h P Q y1)(c2:fd D h P Q y2):False:=by
 obtain ⟨e1,l,r,a1,-,i,hi,a0⟩:=c1;obtain ⟨e2,m,a2,-,k,-⟩:=c2;have h1:=r i hi;have h2:=a2 i hi;have p:e2=e1:=by
  rcases l with rfl|rfl<;>rcases m with rfl|rfl<;>rcases a0 with h3|h3<;>
   first
    | rfl
    | exact absurd h3.symm h1
    | exact absurd h3.symm h2
 exact a1 y2 (nS a3) (p▸k)
lemma m9 {D:aJ}(h:a9 14 D)(p:be D)(a0:br 14 D≤13)(l:aN 14 D={0,9}):False:=by
 have a1:=db 14 D;rw[l,show ({0,9}:S0).card=2 from rfl] at a1;obtain ⟨k,P,Q,r⟩:=kZ h p a0 (by rw[l];decide) Y;have s1:3≤(aG 14 D 1).card\/3≤(aG 14 D 7).card:=(by by_contra hn;exact lL h p r.1 1 7 13 9 0 (by rw[l];decide) o Y Y);have s2:3≤(aG 14 D 6).card\/3≤(aG 14 D 8).card:=(by by_contra hn;exact lL h p r.1 6 8 11 9 0 (by rw[l];decide) o Y Y);have c1:fd D k P Q 7\/fd D k P Q 1:=by
  rcases s1 with m|m
  ·exact oL (iB h p r 1 7 5 3 9 0 6 8 (by rw[l];decide) o m s2)
  ·exact oR (iB h p r 7 1 10 13 0 9 6 8 (by rw[l];decide) o m s2)
 have c2:fd D k P Q 8\/fd D k P Q 6:=by
  rcases s2 with m|m
  ·exact oL (iB h p r 6 8 5 2 9 0 1 7 (by rw[l];decide) o m s1)
  ·exact oR (iB h p r 8 6 10 11 0 9 1 7 (by rw[l];decide) o m s1)
 rcases c1 with a|a<;>rcases c2 with b|b<;>exact ms o a b
abbrev d6:S0:={8,9,10,11,12,13}
lemma jn {I:S0}(h:I={0,1,3}):(∀i∈I,aQ i 7=true)/\(∀t,t∉I->aQ 7 t=false)/\(∀l∈d6,l∉I/\l≠7/\(∃i∈I,aQ i l=true)/\∃z,aQ l z=true/\z∉I)/\(∀t,t∉I->t≠7->∀i∈I,∃q,aQ i q=true/\q≠7/\aQ q t=false)/\I.card=3:=by subst h;refine ⟨?_,?_,?_,?_,?_⟩<;>decide +kernel
abbrev dP (D:aJ)(pos:F0->A0):Finset (A0):=
 (aN 14 D).image pos
def jz (D:aJ)(b:F0->Nat)(u:P0):Prop:=
 ∀x:F0,x≠7->(aG 14 D x).card≤3/\(3≤(aG 14 D x).card->
  bi 14 D (ba 14 D {x})=∅/\x∈O 14 D u.1/\
   ∀v∈aR 14 D b,x∈O 14 D v.1->v=u)
def gx (D:aJ)(l:F0):Prop:=
 ∃Q:A0,aI Q∈aG 14 D l/\(∀t,aI Q∈aG 14 D t->t=l)/\
  ∀z,aH l z->z∈aW 14 D->Q∈aG 14 D z
def fU (D:aJ)(pos:F0->A0)(l:F0):Prop:=
 ∃F G,F∈aG 14 D l/\G∈aG 14 D l/\F≠G/\F∉dP D pos/\
  G∉dP D pos
lemma j4 {D:aJ}{h:F0->A0}(k:ch 14 HG D h){y:F0}(p:y∈aW 14 D){e:A0}(r:aI e∈aG 14 D y):e∉dP D h:=by intro m;obtain ⟨i,l,rfl⟩:=mM.1 m;have:=bx k l r;subst this;exact cl.1 l p
lemma ku {D:aJ}(h:a9 14 D)(hD:be D)(hI:aN 14 D={0,1,3}){r:F0->A0}(k:ch 14 HG D r){l z0:F0}(bm:l≠7)(a6:aH l z0)(a4:z0∈aW 14 D)(a8:¬fU D r l):gx D l:=by
 have hg:=jn hI;have hG:=bn;have hC:=bl hD;obtain ⟨e,he,a7,-⟩:=bp hG h.1 hC a6;have m:∀f∈aG 14 D l,f=e\/f∈dP D r:=(by intro f hf;by_contra p;rw[nO] at p;exact a8 ⟨e,f,he,hf,λheq=>p.1 heq.symm,j4 k a4 a7,p.2⟩);refine ⟨aI e,by rw[aT];exact he,λt ht=>?_,λz hz hze=>?_⟩
 ·rw[aT] at ht;have ht:=(aP.1 ht).2.1;by_contra a2;by_cases a1:t∈aN 14 D
  ·have a3:=(aP.1 he).2.1;rw[i8 hG h.1 hC a1 ht,mS] at a3;exact a2 a3.symm
  ·obtain ⟨f,hf,h7,a5⟩:=bB h hD bm (nS a2)
    (bw.1 (hg.2.1 t a1))
   rcases m f hf with rfl|p
   ·exact a5 ht
   ·obtain ⟨i,hi,rfl⟩:=mM.1 p;exact h7 ((k.1 i hi).2.2.1 7 ((aK _ _).1 (hg.1 i hi)))
 ·obtain ⟨f,hf,a0,-⟩:=bp hG h.1 hC hz;rcases m f hf with rfl|p
  ·exact a0
  ·exact absurd p (j4 k hze a0)
lemma pg {D:aJ}(h:a9 14 D)(hD:be D)(hI:aN 14 D={0,1,3})(b:F0->Nat)(hb:cn 14 D b){m:F0->A0}(p:ch 14 HG D m){u2:P0}(hx:jz D b u2){l t i j:F0}(a6:l≠7)(cb:t≠7)(b0:l≠t)(c6:t∉aN 14 D)(ct:l∈aW 14 D)(hi:i∈aN 14 D)(hj:j∈aN 14 D)(c5:aH i l)(c1:aH j t)(c2:fU D m l)(d1:fU D m t):i=j:=by
 classical
 have hg:=jn hI;have b5:∀{x k:F0},x≠7->k∈aN 14 D->aH k x->fU D m x->3≤(aG 14 D x).card/\∃F G,F∉dP D m/\G∉dP D m/\aG 14 D x={m k,F,G}:=by
  intro x k c0 hk c7 ⟨F,G,hF,hG,bm,a2,a3⟩;have b8:m k∈dP D m:=aj m hk;have hn:m k∉({F,G}:Finset (A0)):=(by simp only[mI,mS,nO];exact ⟨λr=>a2 (r▸b8),λr=>a3 (r▸b8)⟩);have a4:({m k,F,G}:Finset (A0))⊆aG 14 D x:=by
   intro e r;simp only[mI,mS] at r;rcases r with rfl|rfl|rfl
   ·exact bd p hk c7
   ·exact hF
   ·exact hG
  have h1:=cL a4;rw[cI hn,cP bm] at h1
  exact ⟨h1,F,G,a2,a3,(eS a4 (by
   rw[cI hn,cP bm];exact (hx x c0).1)).symm⟩
 obtain ⟨c3,F,G,a2,a3,a1⟩:=b5 a6 hi c5 c2;obtain ⟨b6,F',G',b1,ca,c8⟩:=b5 cb hj c1 d1;obtain ⟨-,d0,b2⟩:=(hx l a6).2 c3;have a8:=((hx t cb).2 b6).2.1;obtain ⟨e0,a5⟩:=ek bn h (bl hD) b hb b0 ct
  (λu hu hlu'=>by rw[b2 u hu hlu'];exact a8) ⟨d0,a8⟩
 have a0:m i∈dP D m:=aj m hi;by_cases hp:m i=e0
 ·exfalso;have h1:=a5 F (by rw[a1];simp) (λr=>a2 (by rw[r,← hp];exact a0));have h2:=a5 G (by rw[a1];simp) (λr=>a3 (by rw[r,← hp];exact a0));obtain ⟨e,r,h7,a7⟩:=bB h hD a6 b0 (bw.1 (hg.2.1 t c6));rw[a1] at r;simp only[mI,mS] at r;rcases r with rfl|rfl|rfl
  ·exact h7 ((p.1 i hi).2.2.1 7 ((aK _ _).1 (hg.1 i hi)))
  ·exact a7 h1
  ·exact a7 h2
 ·have h2:m i∈aG 14 D t:=aP.2 ⟨(p.1 i hi).1,a5 (m i) (by rw[a1];simp) hp,by
    rw[(p.1 i hi).2.1];exact nE t⟩
  rw[c8] at h2;simp only[mI,mS] at h2;rcases h2 with h2|h2|h2
  ·exact p.2 i hi j hj h2
  ·exact absurd (h2▸a0) b1
  ·exact absurd (h2▸a0) ca
def cp (l:List (F0))(k:Fin 4):F0:=l.getD k.val 0
abbrev kv (zl ll:List (F0)):Prop:=
 (∀k:Fin 4,aQ (cp ll k) (cp zl k)=true/\
  aQ (cp ll k) (cp zl (k+1))=true/\cp zl k≠7/\
  cp zl k∉({0,1,3}:S0))/\
 ∀k m:Fin 4,k≠m->cp zl k≠cp zl m/\
  aQ (cp zl k) (cp zl m)=false/\cp ll k≠cp ll m
lemma o2 {D:aJ}(h:a9 14 D)(hD:be D)(hI:aN 14 D={0,1,3})(b:F0->Nat)(b0:dz 14 D b){u2:P0}(ca:u2∈aR 14 D b)(hx:jz D b u2)(p ll:List (F0))(b8:kv p ll)(b1:∀k:Fin 4,gx D (cp ll k)):False:=by
 classical
 obtain ⟨r,a0⟩:=b8
 choose Q hQ1 hQ2 hQ3 using b1
 have hf:∀k:Fin 4,k-1≠k/\k+1≠k/\k+1≠k-1/\k-1+1=k:=o;have a6:∀k,cp p k∈aW 14 D:=λk=>ai.1 (λhc=>(r k).2.2.2 (hI▸cl.2 hc));have a3:∀k,Q k∈aG 14 D (cp p k):=λk=>hQ3 k _ ((aK _ _).1 (r k).1) (a6 k);have a2:∀k,Q k∈aG 14 D (cp p (k+1)):=λk=>hQ3 k _ ((aK _ _).1 (r k).2.1) (a6 _);have hd:∀k m:Fin 4,k≠m->Q k≠Q m:=λk m hkm l=>(a0 k m hkm).2.2 (hQ2 m _ (by rw[← l];exact hQ1 k));have a4:∀k,cp p k≠cp p (k+1):=λk=>(a0 _ _ (nS (hf k).2.1)).1;have h3:∀k,3≤(aG 14 D (cp p k)).card:=by
  intro k;by_contra hc;have b6:Q (k-1)∈aG 14 D (cp p k):=(by have:=a2 (k-1);rwa[(hf k).2.2.2] at this);have b2:=eS
   (s:=({Q k,Q (k-1)}:Finset (A0))) (t:=aG 14 D (cp p k))
   (λe l=>by
    rcases mI.1 l with rfl|l
    ·exact a3 k
    ·rw[mS.1 l];exact b6)
   (by rw[cP (hd _ _ (nS (hf k).1))];omega)
  obtain ⟨e,l,ha,bm⟩:=bB h hD (a4 k)
   (a0 k (k-1) (nS (hf k).1)).1 (bw.1 (a0 _ _ (hf k).2.2.1).2.1)
  rw[← b2] at l;rcases mI.1 l with rfl|l
  ·exact ha (aP.1 (a2 k)).2.1
  ·rw[mS.1 l] at bm;exact bm (aP.1 (a3 (k-1))).2.1
 obtain ⟨P,R,b5,a7⟩:=kh bn h (bl hD) b b0 ca
  (univ.image (cp p)) ⟨_,aj _ (mV 0)⟩
  (λx hx'=>by
   obtain ⟨k,-,rfl⟩:=mM.1 hx'
   exact (hx _ (r k).2.2.1).2 (h3 k))
 have a8:∀k,P∈aG 14 D (cp p k)/\R∈aG 14 D (cp p k):=λk=>a7 _ (aj _ (mV k));have a1:∀k,Q k=P\/Q k=R:=by
  intro k;by_contra hc;rw[nO] at hc;have hn:P∉({R,Q k}:Finset (A0)):=(by simp only[mI,mS,nO];exact ⟨λl=>b5 (l▸rfl),nS hc.1⟩)
  have a5:∀m,Q k∈aG 14 D (cp p m)->({P,R,Q k}:Finset (A0))=aG 14 D (cp p m):=λm hm=>
   eS (λe l=>by
    simp only[mI,mS] at l;rcases l with rfl|rfl|rfl
    ·exact (a8 m).1
    ·exact (a8 m).2
    ·exact hm) (by
    rw[cI hn,cP (nS hc.2)]
    exact (hx _ (r m).2.2.1).1)
  obtain ⟨e,l,ha,-⟩:=bB h hD (a4 k) (a4 k) (bW _);rw[← a5 k (a3 k),a5 (k+1) (a2 k)] at l;exact ha (aP.1 l).2.1
 rcases a1 0 with a|a<;>rcases a1 1 with c|c<;>rcases a1 2 with d|d<;>
  first
  | exact hd 0 1 o (a.trans c.symm)
  | exact hd 0 2 o (a.trans d.symm)
  | exact hd 1 2 o (c.trans d.symm)
lemma fC {α:Type}[DecidableEq α]{S:Finset α}{a b c:α}(ha:a∈S)(hb:b∈S)(r:c∈S)(m:a≠b)(k:a≠c)(l:b≠c):3≤S.card/\(S.card≤3->∀e∈S,e=a\/e=b\/e=c):=by have h:({a,b,c}:Finset α)⊆S:=(by simp[iS,ha,hb,r]);have p:({a,b,c}:Finset α).card=3:=(by rw[cI (by simp[m,k]),cP l]);refine ⟨p▸cL h,λh2 e he=>?_⟩;rw[← eS h (p▸h2)] at he;simpa using he
lemma pI:∀j∈({0,1}:S0),∀t:F0,t≠j->∃q,aQ j q=true/\q≠7/\aQ t q=false:=aa
lemma jJ:∀t:F0,aH 0 t->aH 1 t->t=7:=aa
lemma pc:∀l:F0,aH 1 l->¬aH 7 l:=aa
lemma mQ (d k h:F0)(l:(d=4/\k=10/\h=13)\/(d=6/\k=8/\h=9)):(d∉({0,1,11}:S0)/\k∉({0,1,11}:S0)/\h∉({0,1,11}:S0))/\(aH 11 d/\aH d k/\aH d h/\aH 0 k/\aH 1 h)/\(k≠7/\h≠7/\d≠7/\k≠d/\h≠d)/\¬aH 0 d/\¬aH 1 d:=by
 rcases l with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩<;>
  exact ⟨o,⟨o,o,o,o,o⟩,o,o,o⟩
lemma eD:dU {7,8,13} {0,1,2}=true:=aa
lemma o3:∀i t x:F0,aQ i t=true->x≠t->x≠i->∃q,aQ i q=true/\q≠t/\q≠x/\aQ x q=false:=aa
lemma nq {D:aJ}{b:F0->Nat}{u:P0}{x y z:F0}(k:u∈aR 14 D b)(l:(O 14 D u.1∩{x,y,z}).Nonempty):u∈ru D b x\/u∈ru D b y\/u∈ru D b z:=by
 obtain ⟨a,h⟩:=l;rw[mN,mI,mI,mS] at h;rcases h.2 with rfl|rfl|rfl
 ·exact oL (bb.2 ⟨k,h.1⟩)
 ·exact oR (oL (bb.2 ⟨k,h.1⟩))
 ·exact oR (oR (bb.2 ⟨k,h.1⟩))
lemma kG {D:aJ}{k:F0->A0}(h:a9 14 D)(hD:be D){t i x:F0}{P F:A0}(hW:∀e∈aG 14 D t,e=k i\/e=P\/e=F)(m:∀a,aH i a->a∈O 14 D (W D (k i)))(p:aH i t)(l:x≠t)(a1:x≠i)(hP:x∈O 14 D (W D P))(hF:x∈O 14 D (W D F)):False:=by
 obtain ⟨q,a0,r,-,a2⟩:=o3 i t x ((aK _ _).2 p) l a1;obtain ⟨e,he,h1,h2⟩:=bB h hD (nS l) (nS r) (bw.1 a2);rcases hW e he with rfl|rfl|rfl
 ·exact h2 (m q ((aK _ _).1 a0))
 ·exact h1 hP
 ·exact h1 hF
lemma iP {D:aJ}{k:F0->A0}(h:a9 14 D)(hD:be D)(a2:ch 14 HG D k)(b:F0->Nat)(hb:cn 14 D b){t i j:F0}{F:A0}(hi:i∈aN 14 D)(hj:j∈aN 14 D)(hg:i≠j/\aH i t/\aH j t)(hW:aG 14 D t={k i,k j,F})(hF:F≠k i/\F≠k j)(a6:∀a,a∈O 14 D (W D (k i))<->aH i a)(a1:∀a,a∈O 14 D (W D (k j))<->aH j a)(hc:(ru D b t).card=1){u:P0}(hu:u∈aR 14 D b)(p:t∈O 14 D u.1){x:F0}(hx:x∈O 14 D u.1):x=t:=by
 by_contra m;have a5:=eQ hu hx;have b0:x≠i:=λe=>cl.1 hi (e▸a5);have b5:x≠j:=λe=>cl.1 hj (e▸a5);obtain ⟨v,hv⟩:=ac.1 hc;have b1:u=v:=by
  have:u∈ru D b t:=bb.2 ⟨hu,p⟩
  rwa[hv,mS] at this
 obtain ⟨e0,l⟩:=ek bn h (bl hD) b hb (nS m)
  (eQ hu p) (λu' hu' ht'=>by
   have:u'∈ru D b t:=bb.2 ⟨hu',ht'⟩
   rw[hv,mS] at this
   rw[this,← b1];exact hx) ⟨p,hx⟩
 have a8:∀e∈aG 14 D t,e=k i\/e=k j\/e=F:=λe he=>by
  rw[hW] at he;simpa using he
 have bm:k i∈aG 14 D t:=by rw[hW];simp
 have a0:k j∈aG 14 D t:=by rw[hW];simp
 have a4:F∈aG 14 D t:=by rw[hW];simp
 have a3:k i≠k j:=λe=>hg.1 (a2.2 i hi j hj e);by_cases h1:x∈O 14 D (W D (k i))
 ·by_cases h2:x∈O 14 D (W D (k j))
  ·exact m (jX i j x t hg.1 ((aK _ _).2 (bh hg.2.1)) ((aK _ _).2 (bh hg.2.2)) ((aK _ _).2 (bh ((a6 x).1 h1))) ((aK _ _).2 (bh ((a1 x).1 h2))))
  ·have b2:k j=e0:=by
    by_contra r;exact h2 (l _ a0 r)
   exact kG h hD (λe he=>or_left_comm.1 (a8 e he)) (λa ha=>(a1 a).2 ha)
    hg.2.2 m b5 h1 (l F a4 (λe=>hF.2 (e.trans b2.symm)))
 ·have a7:k i=e0:=by
   by_contra r;exact h1 (l _ bm r)
  exact kG h hD a8 (λa ha=>(a6 a).2 ha) hg.2.1 m b0
   (l _ a0 (λe=>a3 (a7.trans e.symm)))
   (l F a4 (λe=>hF.1 (e.trans a7.symm)))
lemma iI {D:aJ}{r:F0->A0}(h:a9 14 D)(hD:be D)(k:ch 14 HG D r){i s d:F0}(hi:i∈aN 14 D)(p:aH i s/\aH d s/\s≠i/\d≠i)(hc:(aG 14 D s).card≤2):∃Z,(∀t,t≠s->Z∉aG 14 D t)/\Z∈aG 14 D s/\aI Z∈aG 14 D d:=by
 obtain ⟨Z,-,hW,a0⟩:=ps h hD k hi p.2.2.1 (bd k hi p.1) hc;obtain ⟨e,l,m,-⟩:=bp bn h.1 (bl hD) p.2.1;rw[hW,mI,mS] at m;rcases m with h1|h1
 ·exact absurd (bx k hi (by rw[← h1,aT];exact l)) p.2.2.2
 ·exact ⟨Z,a0,by rw[hW];simp,by rw[← h1,aT];exact l⟩
section PeMixed
def fY:eP (F0):=
 ⟨iM [11,12,13,7,8,9,10,3,4,5,6,0,1,2],
  iM [11,12,13,7,8,9,10,3,4,5,6,0,1,2],
  by intro x;revert x;decide +kernel,by intro x;revert x;decide +kernel⟩
def bM:S0:={0,1,11,12}
def e8 (D:aJ)(x:F0):Nat:=
 cd D ((bY 14 D).filter (λw=>x∈O 14 D w))
def ef (D:aJ)(b:F0->Nat)(pos:F0->A0):Prop:=
 a9 14 D/\be D/\cn 14 D b/\ch 14 HG D pos/\aN 14 D=bM
lemma lX (σ:eP (F0)){D:aJ}(hS:aV 14 D)(x:F0):e8 (bz σ D) (σ x)=e8 D x:=
 gK σ D _ _ (λw=>by rw[eH σ hS];simp)
variable {D : aJ} {pos : Fin 14 → Nat × Bool} {b : Fin 14 → Nat}
lemma lU (l:ef D b pos){x:F0}(m:x∈aW 14 D):e8 D x=1+(ru D b x).card:=by
 obtain ⟨h,k,r,-⟩:=l;have h1:=ln bn h (bl k) x;have h2:=fx h k b r m;have p:(bY 14 D).filter (λw=>x∈O 14 D w)=ba 14 D {x}:=by
  ext w;rw[mF,dp,cz];refine ⟨λhh=>hh.2,λhh=>⟨?_,hh⟩⟩;have h4:=d4 hh;have h5:w≠aO 14 D:=λe=>by
   rw[e,c4 k] at hh;exact nE _ hh
  unfold aO at h5;omega
 unfold e8;rw[p];omega
lemma d3 (h:ef D b pos)(i:F0)(k:i∈bM):i∈aN 14 D:=by rw[h.2.2.2.2];exact k
lemma fD (l:ef D b pos)(x:F0)(k:x∉bM):x∈aW 14 D:=by by_contra h;exact k (l.2.2.2.2▸cl.2 h)
lemma fe (hpos:ch 14 HG D pos){i x:F0}{e:A0}(hi:i∈aN 14 D)(hx:x∈aW 14 D)(he:aI e∈aG 14 D x):e≠pos i:=λheq=>cl.1 hi (bx hpos hi (heq▸he)▸hx)
lemma fB (hpos:ch 14 HG D pos){i x:F0}{e:A0}(hi:i∈aN 14 D)(hx:x∈aW 14 D)(he:e∈aG 14 D x):aI e≠pos i:=fe hpos hi hx (by rw[aT];exact he)
lemma fH (hpos:ch 14 HG D pos){i t:F0}(hi:i∈aN 14 D)(ht:t∈O 14 D (W D (pos i))):pos i∈aG 14 D t:=
 aP.2 ⟨(hpos.1 i hi).1,ht,by rw[(hpos.1 i hi).2.1];exact nE t⟩
lemma kw (hK:ef D b pos){x:F0}(J:S0)(hJ:∀i∈J,i∈bM/\aQ i x=true):∀i∈J,i∈aN 14 D/\pos i∈aG 14 D x:=λi hi=>
 ⟨d3 hK _ (hJ i hi).1,
  bd hK.2.2.2.1 (d3 hK _ (hJ i hi).1) ((aK _ _).1 (hJ i hi).2)⟩
lemma fk (h:ch 14 HG D pos){x:F0}(J:S0)(p:∀i∈J,i∈aN 14 D/\pos i∈aG 14 D x)(Fs:Finset (A0))(hF:∀e∈Fs,e∈aG 14 D x/\∀i∈J,e≠pos i):J.card+Fs.card≤(aG 14 D x).card:=by
 classical
 have m:iO pos J:=λi k j hj hij=>h.2 i (p i k).1 j (p j hj).1 hij;have l:Disjoint (J.image pos) Fs:=(by rw[dL];intro e r a0;obtain ⟨i,k,rfl⟩:=mM.1 r;exact (hF _ a0).2 i k rfl)
 have:=cL (uS (λe he=>by
  obtain ⟨i,k,rfl⟩:=mM.1 he
  exact (p i k).2) (λe he=>(hF e he).1):J.image pos∪Fs⊆aG 14 D x)
 rwa[cU l,cJ m] at this
lemma gz (hK:ef D b pos){v t j q:F0}(hj:j∈aN 14 D)(hv:v∈aW 14 D)(a0:∀u∈aR 14 D b,v∈O 14 D u.1->t∈O 14 D u.1){w:Nat}(hw:v∈O 14 D w/\t∈O 14 D w)(hg:aQ j v=true/\aQ j q=true/\v≠t/\v≠q/\aQ t q=false):t∈O 14 D (W D (pos j)):=by obtain ⟨h,hD,hb,k,-⟩:=hK;obtain ⟨p,r,l,a3,a1⟩:=hg;rw[aK] at p r;obtain ⟨e0,m⟩:=ek bn h (bl hD) b hb l hv a0 hw;by_contra hn;have h0:pos j=e0:=(by by_contra a2;exact hn (m _ (bd k hj p) a2));obtain ⟨e,he,h1,h2⟩:=bB h hD l a3 (bw.1 a1);exact h1 (m e he (λhee=>h2 (by rw[hee,← h0];exact (k.1 j hj).2.2.1 q r)))
lemma lF (h:ef D b pos){v i j t:F0}{u:P0}(hu:u∈aR 14 D b)(p:v∈O 14 D u.1)(a8:∀u'∈aR 14 D b,v∈O 14 D u'.1->u'=u)(hg:i∈bM/\j∈bM/\v∉bM/\aQ i v=true/\aQ j v=true/\∀t:F0,t∉bM->v≠t->∃q0 q1:F0,(aQ i q0=true/\v≠q0/\aQ t q0=false)/\aQ j q1=true/\v≠q1/\aQ t q1=false)(m:v≠t)(r:t∈O 14 D u.1):∀k∈({i,j}:S0),pos k∈aG 14 D t:=by
 obtain ⟨hi,hj,hv,a7,a0,hq⟩:=hg;obtain ⟨q0,q1,⟨a1,a2,a3⟩,a4,a5,a6⟩:=hq t
  (λhm=>cl.1 (d3 h _ hm) (eQ hu r)) m
 have l:∀u'∈aR 14 D b,v∈O 14 D u'.1->t∈O 14 D u'.1:=λu' hu' hv'=>a8 u' hu' hv'▸r;intro k hk;rcases mI.1 hk with e|e
 ·rw[e];exact fH h.2.2.2.1 (d3 h _ hi) (gz h (d3 h _ hi) (fD h _ hv) l ⟨p,r⟩ ⟨a7,a1,m,a2,a3⟩)
 ·rw[mS.1 e];exact fH h.2.2.2.1 (d3 h _ hj) (gz h (d3 h _ hj) (fD h _ hv) l ⟨p,r⟩ ⟨a0,a4,m,a5,a6⟩)
lemma j9 (hK:ef D b pos){v c:F0}(hv:v∈aW 14 D)(l:v≠c){w:Nat}(hw:v∈O 14 D w/\c∈O 14 D w)(a4:(ru D b v).card≤(ru D b v∩ru D b c).card+1){p q P:A0}(hp:p∈aG 14 D v)(hq:q∈aG 14 D v)(hP:P∈aG 14 D v)(hd:p≠q/\p≠P/\q≠P)(r:c∉O 14 D (W D P)):c∈O 14 D (W D p)\/c∈O 14 D (W D q):=by
 classical
 obtain ⟨h,hD,hb,-⟩:=hK;by_contra k;rw[nO] at k;have s1:=kl h.1 b hb l hv;have s2:=lQ h v c l (by rw[c4 hD];exact nE v);obtain ⟨j,s,hj,ht,-,a2,a0,a3,-⟩:=lG h.1 l hw
 have m:∀e∈aG 14 D v,c∉O 14 D (W D e)->e∈(bo 14 D (bJ 14 D v c)).erase (j,s):=λe he hce=>
  mE.2 ⟨λheq=>by
   have:=dJ h.1 he;rw[heq,ht] at this
   exact bF this,gl.2 ⟨(aP.1 he).1,⟨(aP.1 he).2.1,hce⟩,λhh=>(aP.1 he).2.2 hh.1⟩⟩
 have a1:=two_lt_card.2 ⟨p,m _ hp k.1,q,m _ hq k.2,P,m _ hP r,hd⟩;rw[cE (gl.2 ⟨hj,⟨a0,a3⟩,λhh=>hh.2 a2⟩)] at a1
 have h5:((aR 14 D b).filter (λu=>v∈O 14 D u.1/\c∉O 14 D u.1)).card≤(ru D b v \ ru D b c).card:=cL (λu hu=>by
   rw[mF] at hu
   exact mD.2 ⟨bb.2 ⟨hu.1,hu.2.1⟩,λm=>hu.2.2 (bb.1 m).2⟩)
 have h6:=cD (ru D b v) (ru D b c);omega
lemma kf (m:ef D b pos){x y z i j:F0}(hg:i∈bM/\j∈bM/\x∉bM/\y∉bM/\z∉bM/\aQ i x=true/\aQ j y=true/\aQ x y=true/\aQ z x=true/\z≠y)(b6:(ru D b x).card=0)(b5:(ru D b y).card=0):False:=by
 obtain ⟨g1,g2,g3,g4,g5,a6,a8,a7,a5,b1⟩:=hg;rw[aK] at a6 a8 a7 a5;have hi:=d3 m _ g1;have hj:=d3 m _ g2;have hx:=fD m _ g3;have hy:=fD m _ g4;have hz:=fD m _ g5;obtain ⟨h,hD,hb,k,-⟩:=m;have hG:=bn;have hC:=bl hD;obtain ⟨Zx,-,a0,-⟩:=ps h hD k hi (λe=>cl.1 hi (e▸hx))
  (bd k hi a6) (by have:=ci h hD b hb x;omega)
 obtain ⟨Zy,-,b0,b2⟩:=ps h hD k hj (λe=>cl.1 hj (e▸hy))
  (bd k hj a8) (by have:=ci h hD b hb y;omega)
 obtain ⟨e,p,r,-⟩:=bp hG h.1 hC a7;obtain ⟨e',l,bm,-⟩:=bp hG h.1 hC a5;have a1:e=Zx:=mS.1
  ((mI.1 (a0▸p)).resolve_left (fe k hi hy r))
 have a2:aI e=Zy:=mS.1
  ((mI.1 (b0▸r)).resolve_left (fB k hj hx p))
 have a3:aI e'=Zx:=mS.1
  ((mI.1 (a0▸bm)).resolve_left (fB k hi hz l))
 have a4:e'=Zy:=(by rw[← a2,a1,← a3,aT]);exact b2 z b1 (a4▸l)
lemma lj {x:F0}{h:P0}(h1:(ru D b x).card=1)(k:h∈aR 14 D b)(l:x∈O 14 D h.1):∀u∈aR 14 D b,x∈O 14 D u.1->u=h:=by obtain ⟨a,ha⟩:=ac.1 h1;intro u r hx;have m:u∈ru D b x:=bb.2 ⟨r,hx⟩;have p:h∈ru D b x:=bb.2 ⟨k,l⟩;rw[ha,mS] at m p;rw[m,p]
lemma ke (hK:ef D b pos){x i:F0}{us uo:P0}(Js Jo:S0){F:A0}(hg:Js⊆bM/\Jo⊆bM/\Js.card=2/\Jo.card=2/\Disjoint Js Jo/\i∈Js/\aQ i x=true)(hs:x∈O 14 D us.1->∀k∈Js,pos k∈aG 14 D x)(ho:x∈O 14 D uo.1->∀k∈Jo,pos k∈aG 14 D x)(hρ:(ru D b x).card≤(if x∈O 14 D us.1 then 1 else 0)+if x∈O 14 D uo.1 then 1 else 0)(hF:F∈aG 14 D x/\∀k∈aN 14 D,F≠pos k):∀e∈aG 14 D x,e=F\/e∈Js.image pos:=by
 classical
 obtain ⟨g1,g2,g3,g4,g5,g6,g7⟩:=hg;have m:∀{k:F0},k∈bM->k∈aN 14 D:=d3 hK _;obtain ⟨h,hD,hb,p,-⟩:=hK;have a4:=ci h hD b hb x;have a3:=bd p (m (g1 g6)) ((aK _ _).1 g7);have a2:∀J:S0,(∀k∈J,k∈aN 14 D/\pos k∈aG 14 D x)->J.card+1≤(aG 14 D x).card:=λJ hJ=>by
  have:=fk p J hJ {F} (λe he=>by
   rw[mS.1 he];exact ⟨hF.1,λk l=>hF.2 k (hJ k l).1⟩)
  rwa[cS] at this
 by_cases ko:x∈O 14 D uo.1
 ·exfalso;by_cases ks:x∈O 14 D us.1
  ·have:=a2 (Js∪Jo) (λk l=>by
    rcases mU.1 l with l|l
    ·exact ⟨m (g1 l),hs ks k l⟩
    ·exact ⟨m (g2 l),ho ko k l⟩)
   rw[cU g5] at this;simp only[ko,ks,iT] at hρ;omega
  ·have:=a2 (insert i Jo) (λk l=>by
    rcases mI.1 l with l|l
    ·rw[l];exact ⟨m (g1 g6),a3⟩
    ·exact ⟨m (g2 l),ho ko k l⟩)
   rw[cI (dL.1 g5 g6)] at this;simp only[ko,ks,iT,iF] at hρ;omega
 ·intro e he;by_contra a0;rw[nO] at a0;have a1:∀J:S0,J⊆Js->(∀k∈J,pos k∈aG 14 D x)->J.card+2≤(aG 14 D x).card:=λJ hJs hJ=>by
   have:=fk p J (λk l=>⟨m (g1 (hJs l)),hJ k l⟩) {F,e}
    (λe' r=>by
     rcases mI.1 r with r|r
     ·rw[r];exact ⟨hF.1,λk l=>hF.2 k (m (g1 (hJs l)))⟩
     ·rw[mS.1 r]
      exact ⟨he,λk l hek=>a0.2 (mM.2 ⟨k,hJs l,hek.symm⟩)⟩)
   rwa[cP (nS a0.1)] at this
  by_cases ks:x∈O 14 D us.1
  ·have:=a1 Js (Subset.refl _) (hs ks);simp only[ko,ks,iT,iF] at hρ;omega
  ·have:=a1 {i} (sS.2 g6) (λk l=>by
    rw[mS.1 l];exact a3)
   rw[cS] at this;simp only[ko,ks,iF] at hρ;omega
end PeMixed
def dx:F0->F0:=λi=>([0,1,2,3,4,5,6,7,13,12,11,10,9,8]:List (F0)).getD i.val 0
def cm (i:Nat):Nat:=if h:i<14 then (dx ⟨i,h⟩).val else i
def da (w:List Bool)(g:Gate):List Bool:=w++[g.op.eval (g.inputs.map λi=>w.getD i false)]
lemma ee {i:Nat}(h:14≤ i):cm i=i:=by simp[cm,aA.mpr h]
lemma gX {i:Nat}(h:i<14):cm i<14:=by rw[cm,dif_pos h];exact (dx ⟨i,h⟩).isLt
lemma oI (l:List Gate):∀w w':List Bool,w.length=w'.length->14≤w.length->(∀i,w'.getD (cm i) false=w.getD i false)->∀i,((l.map λg=>(⟨g.op,g.inputs.map cm⟩:Gate)).foldl da w').getD (cm i) false=(l.foldl da w).getD i false:=by
 induction l with
 | nil=>intro w w' _ _ h i;exact h i
 | cons g l ih=>
  intro w w' p h9 h i;simp only[List.map_cons,List.foldl_cons];apply ih
  ·simp[da,p]
  ·simp[da];omega
  ·intro j;have hv:g.op.eval ((g.inputs.map cm).map λi=>w'.getD i false)=g.op.eval (g.inputs.map λi=>w.getD i false):=by
    rw[List.map_map];congr 1;apply List.map_congr_left;intro a _;exact h a
   simp only[da];rw[hv];rcases nT j w.length with k|k|k
   ·have m:cm j<w'.length:=by
     by_cases r:j<14
     ·have:=gX r;omega
     ·rw[ee Y];omega
    have e:=h j;simp only[gD] at e ⊢;rw[ax m,ax k];exact e
   ·subst k;rw[ee h9];simp[gD,p]
   ·rw[ee Y];rw[lD _ _ (by simp;omega),lD _ _ (by simp;omega)]
def gm (x:F0->Bool):Prop:=∃(a:Fin 7) (b:Fin 7),(a=b\/a=b+1\/a=b+3)/\x (Fin.castAdd 7 a)=true/\x (Fin.natAdd 7 b)=true
lemma o4:∀a b:Fin 7,(a=b\/a=b+1\/a=b+3)->((dx (Fin.castAdd 7 a)).val,(dx (Fin.natAdd 7 b)).val)∈([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]:List (Nat×Nat)):=aa
lemma pB:∀u v:F0,(u.val,v.val)∈([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]:List (Nat×Nat))->∃a b:Fin 7,(a=b\/a=b+1\/a=b+3)/\dx (Fin.castAdd 7 a)=u/\dx (Fin.natAdd 7 b)=v:=aa
abbrev aM (D:aJ):Nat:=D.length-1
def cg (D:aJ):Prop:=
 1≤D.length/\D.length≤27/\bf D (aM D)=true/\
  ∃p l:F0,aH p l/\
   p∉O 14 D (aZ D (aM D))/\p∉O 14 D (aY D (aM D))/\
   l∉O 14 D (aZ D (aM D))/\l∉O 14 D (aY D (aM D))
def fu (D:aJ):Prop:=
 D.length=27/\bf D 26=true/\
  ∃p l:F0,aH p l/\
   p∉O 14 D (aZ D 26)/\p∉O 14 D (aY D 26)/\
   l∉O 14 D (aZ D 26)/\l∉O 14 D (aY D 26)
lemma lu {D:aJ}(hT:cg D)(a2:D.length=27):fu D:=by
 obtain ⟨-,-,h,p,l,a1,r,m,a0,k⟩:=hT;have ho:aM D=26:=by unfold aM;omega
 rw[ho] at h r m a0 k;exact ⟨a2,h,p,l,a1,r,m,a0,k⟩
lemma kt (σ:eP (F0))(hσ:dv σ){D:aJ}(hS:aV 14 D)(hT:cg D):cg (bz σ D):=by
 obtain ⟨h1,a5,k,p,l,a3,a2,a1,a4,a0⟩:=hT;have r:aM (bz σ D)=aM D:=by unfold aM;rw[di]
 have m:aM D<D.length:=by unfold aM;omega
 refine ⟨by rw[di];exact h1,by rw[di];exact a5,by rw[r,j8 σ D _ m,k],σ p,σ l,(hσ p l).mpr a3,?_,?_,?_,?_⟩
 ·rw[r,f7 σ D _ m,eH σ hS];simpa using a2
 ·rw[r,f6 σ D _ m,eH σ hS];simpa using a1
 ·rw[r,f7 σ D _ m,eH σ hS];simpa using a4
 ·rw[r,f6 σ D _ m,eH σ hS];simpa using a0
lemma mb (op:GateOp)(l:op=GateOp.and\/op=GateOp.or)(k:List Nat)(U V:List Bool)(h:∀i,U.getD i false=true->V.getD i false=true):op.eval (k.map λi=>U.getD i false)=true->op.eval (k.map λi=>V.getD i false)=true:=by
 rcases l with rfl|rfl
 ·simp only[GateOp.eval,List.all_map,List.all_eq_true,Function.comp,id];exact λhall i hi=>h i (hall i hi)
 ·simp only[GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id];exact λ⟨i,hi,hv⟩=>⟨i,hi,h i hv⟩
lemma pT (x y:F0->Bool)(h:∀v:F0,x v=true->y v=true)(w:Nat):(lO x).getD w false=true->(lO y).getD w false=true:=by
 by_cases k:w<14
 ·simp only[gD,List.getElem?_ofFn,k,ah,Option.getD_some];exact h ⟨w,k⟩
 ·rw[lD _ _ (by simp;omega)];simp
lemma pw (m:List Gate)(l:∀g∈m,g.op=GateOp.and\/g.op=GateOp.or):∀U V:List Bool,U.length=V.length->(∀i,U.getD i false=true->V.getD i false=true)->∀i,(m.foldl da U).getD i false=true->(m.foldl da V).getD i false=true:=by
 induction m with
 | nil=>intro U V _ h i;exact h i
 | cons g m ih=>
  intro U V k h i;have hg:=l g ab;refine ih (λg' hg'=>l g' (by simp[hg'])) (da U g) (da V g) (by simp[da,k])
   (λt=>?_) i
  rcases nT t U.length with p|p|p
  ·simp only[da,gD,ax p,ax (by omega:t<V.length)];exact λhv=>by simpa[gD] using h t (by simpa[gD] using hv)
  ·subst p;have h1:(da U g).getD U.length false=g.op.eval (g.inputs.map λi=>U.getD i false):=by
    simp[da,gD]
   have h2:(da V g).getD U.length false=g.op.eval (g.inputs.map λi=>V.getD i false):=(by rw[k];simp[da,gD]);rw[h1,h2];exact mb g.op hg g.inputs U V h
  ·rw[lD _ _ (by simp[da];omega)];intro r;exact absurd r ab
lemma kx (C:Circuit)(hAO:PEqualNP.TopForm.IsAO2 14 C){x y:F0->Bool}(hxy:∀v:F0,x v=true->y v=true)(hx:C.eval (lO x)=true):C.eval (lO y)=true:=
 pw C.gates (λg hg=>hAO.1 g hg) (lO x) (lO y) (by simp)
  (pT x y hxy) C.output hx
lemma fano_eval_of_edges_max (C:Circuit)(p:PEqualNP.TopForm.IsAO2 14 C)(a3:∀a b:Fin 7,(a=b\/a=b+1\/a=b+3)->C.eval (lO λu:F0=>decide (u=Fin.castAdd 7 a\/u=Fin.natAdd 7 b))=true)(h:∀x:F0->Bool,Maximal (λy:F0->Bool=>¬gm y) x->C.eval (lO x)=false):∀x:F0->Bool,C.eval (lO x)=true<->gm x:=by
 intro x;constructor
 ·intro a0;by_contra a2;have r:Set.Finite {y:F0->Bool|¬gm y/\x≤y}:=Set.toFinite _;obtain ⟨m,k,l⟩:=r.exists_le_maximal (a:=x) ⟨a2,lR x⟩;have a1:Maximal (λy:F0->Bool=>¬gm y) m:=by
   refine ⟨l.1.1,λz hz hmz=>l.2 ⟨hz,lT k hmz⟩ hmz⟩
  have hf:=h m a1
  have ht:=kx C p (y:=m) (λv hv=>by
   have:=k v;rw[Bool.le_iff_imp] at this;exact this hv) a0
  rw[hf] at ht;exact bF ht
 ·rintro ⟨a,b,a4,ha,hb⟩;refine kx C p (λv hv=>?_) (a3 a b a4);simp only[dT] at hv;rcases hv with rfl|rfl
  exacts [ha,hb]
def iC:GateOp->Bool
 | GateOp.and=>true
 | _=>false
def ei (gs:List Gate):aJ:=
 gs.map λg=>
  (iC g.op,g.inputs.getD 0 0,g.inputs.getD 1 0)
lemma o9 (h:List Gate):(ei h).length=h.length:=by simp[ei]
lemma pd (p:List Gate)(k:∀g∈p,(g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length=2):∀w:List Bool,wl (ei p) w=p.foldl da w:=by
 induction p with
 | nil=>intro w;rfl
 | cons g p ih=>
  intro w;obtain ⟨r,l⟩:=k g ab;rcases List.length_eq_two.mp l with ⟨a,b,a0⟩
  have m:ep w (iC g.op,g.inputs.getD 0 0,g.inputs.getD 1 0) =
    da w g:=by
   simp only[ep,da,a0];rcases r with h|h<;>simp[h,GateOp.eval,dm,iC]
  simp only[ei,List.map_cons,iE,List.foldl_cons,m];exact ih (λg' hg'=>k g' (by simp[hg'])) _
lemma ao2_to_dag_4874 (C:Circuit)(k a b:Nat)(er:C.size≤27)(ez:PEqualNP.TopForm.IsAO2 14 C)(c7:∀g∈C.gates,g.inputs.Nodup)(f1:C.output=14+k)(hk:C.gates[k]?=some ⟨GateOp.and,[a,b]⟩)(hc:∀x:F0->Bool,C.eval (lO x)=true<->gm x)(hr:∀v∈[(0:F0),(7:F0)],PEqualNP.BlindGate.wireValue C 14 (λu=>decide (u=v)) a=false/\PEqualNP.BlindGate.wireValue C 14 (λu=>decide (u=v)) b=false):∃D:aJ,a9 14 D/\be D/\cg D:=by
 let C':Circuit:=⟨C.gates.map λg=>⟨g.op,g.inputs.map cm⟩,cm C.output⟩
 have a8:PEqualNP.TopForm.IsAO2 14 C':=by
  refine ⟨λg hg=>?_,λj hj w hw=>?_,λg hg=>?_⟩
  ·obtain ⟨g0,cb,rfl⟩:=lM.mp hg;exact ez.1 g0 cb
  ·have fz:j<C.gates.length:=(by simpa[C'] using hj);have ca:NestedCover.gateAt C' j =
     ⟨(NestedCover.gateAt C j).op,(NestedCover.gateAt C j).inputs.map cm⟩:=by
    simp[NestedCover.gateAt,C',gD,gE fz]
   rw[ca] at hw;obtain ⟨u,hu,rfl⟩:=lM.mp hw;have hF:=ez.2.1 j fz u hu;by_cases g7:u<14
   ·have:=gX g7;omega
   ·rw[ee Y];omega
  ·obtain ⟨g0,cb,rfl⟩:=lM.mp hg;simpa using ez.2.2 g0 cb
 have e7:∀g∈C'.gates,g.inputs.Nodup:=by
  intro g hg;obtain ⟨g0,cb,rfl⟩:=lM.mp hg;refine List.Nodup.map ?_ (c7 g0 cb);intro x y b0;by_cases hx:x<14<;>by_cases hy:y<14
  ·simp only[cm,hx,hy,ah] at b0;have fl:∀u v:F0,(dx u).val=(dx v).val->u=v:=aa
   exact kA Fin.val (fl ⟨x,hx⟩ ⟨y,hy⟩ b0)
  ·have h1:=gX hx;rw[ee (by omega:14≤y)] at b0;omega
  ·have h1:=gX hy;rw[ee (by omega:14≤x)] at b0;omega
  ·rwa[ee (by omega:14≤x),ee (by omega:14≤y)] at b0
 have g1:k<C.gates.length:=(by by_contra hG;rw[lN Y] at hk;exact absurd hk ab);have hE:C.gates.length≤27:=er
 let Dfull:aJ:=ei C'.gates
 have a6:Dfull.length=C.gates.length:=by simp[Dfull,o9,C']
 let D0:aJ:=Dfull.take (k+1)
 have a3:D0.length=k+1:=by simp[D0,a6];omega
 have c5:aV 14 Dfull:=by
  intro j hj;rw[a6] at hj;have c8:j<C'.gates.length:=by simp[C',hj]
  let g0:=C'.gates[j]
  have d1:g0∈C'.gates:=List.getElem_mem c8;obtain ⟨u,v,b5⟩:=List.length_eq_two.mp (a8.2.2 g0 d1);have f0:=e7 g0 d1;rw[b5,List.nodup_cons,List.mem_singleton] at f0;have ca:NestedCover.gateAt C' j=g0:=(by simp[NestedCover.gateAt,gD,gE c8,g0]);have hu:=a8.2.1 j c8 u (by rw[ca,b5];simp);have hv:=a8.2.1 j c8 v (by rw[ca,b5];simp);have hA:aZ Dfull j=u:=(by rw[fa Dfull j Y];simp only[Dfull,ei,List.getElem_map];show g0.inputs.getD 0 0=u;rw[b5];rfl);have hB:aY Dfull j=v:=(by rw[fg Dfull j Y];simp only[Dfull,ei,List.getElem_map];show g0.inputs.getD 1 0=v;rw[b5];rfl);rw[hA,hB];exact ⟨hu,hv,f0.1⟩
 have e0:aV 14 D0:=by
  intro j hj;rw[a3] at hj;have h1:aZ D0 j=aZ Dfull j:=by rw[fa D0 j Y,fa Dfull j Y];simp[D0]
  have h2:aY D0 j=aY Dfull j:=by rw[fg D0 j Y,fg Dfull j Y];simp[D0]
  rw[h1,h2];exact c5 j Y
 have a4:∀(y:F0->Bool) (w:Nat),val Dfull y (cm w)=PEqualNP.BlindGate.wireValue C 14 (λi=>y (dx i)) w:=by
  intro y w;show (wl Dfull (lO y)).getD (cm w) false=(C.wires (lO λi=>y (dx i))).getD w false;rw[pd C'.gates (λg hg=>⟨a8.1 g hg,a8.2.2 g hg⟩)];refine oI C.gates (lO λi=>y (dx i)) (lO y) ab ab ?_ w;intro i;by_cases hi:i<14
  ·simp only[cm,hi,ah];interval_cases i<;>rfl
  ·rw[ee Y,lD _ _ (by simp;omega),lD _ _ (by simp;omega)]
 have a5:∀(y:F0->Bool) (w:Nat),w≤14+k->val D0 y w=val Dfull y w:=by
  intro y w hw;have c2:Dfull=D0++Dfull.drop (k+1):=(List.take_append_drop (k+1) Dfull).symm;show (wl D0 (lO y)).getD w false=(wl Dfull (lO y)).getD w false
  conv_rhs=>rw[c2,jy]
  exact (gR (Dfull.drop (k+1)) (wl D0 (lO y)) w (by rw[ig,List.length_ofFn,a3];omega)).symm
 have c0:be D0:=by
  intro y;have ec:aO 14 D0=14+k:=by unfold aO;rw[a3];omega
  rw[ec,a5 y (14+k) (lR _)];have g2:cm (14+k)=14+k:=ee Y;have hv:=a4 y (14+k);rw[g2] at hv;have hn:PEqualNP.BlindGate.wireValue C 14 (λi=>y (dx i)) (14+k) =
    C.eval (lO λi=>y (dx i)):=by rw[← f1];rfl
  rw[hv,hn,hc];constructor
  ·rintro ⟨p,l,c1,hp,hl⟩;exact ⟨_,_,o4 p l c1,hp,hl⟩
  ·rintro ⟨u,v,b5,hu,g4⟩;obtain ⟨p,l,c1,rfl,rfl⟩:=pB u v b5;exact ⟨p,l,c1,hu,g4⟩
 have d0:C'.gates[k]?=some ⟨GateOp.and,[cm a,cm b]⟩:=(by simp[C',List.getElem?_map,hk]);have fi:k<C'.gates.length:=by simp[C',g1]
 have ct:C'.gates[k]=⟨GateOp.and,[cm a,cm b]⟩:=(by have:=gE fi;rw[this] at d0;exact Option.some.inj d0);have a0:aM D0=k:=by unfold aM;omega
 have e2:bf D0 (aM D0)=true:=(by rw[a0,hV D0 k Y];simp[D0,Dfull,ei,ct,iC]);have b2:aZ D0 (aM D0)=cm a:=(by rw[a0,fa D0 k Y];simp[D0,Dfull,ei,ct]);have b1:aY D0 (aM D0)=cm b:=(by rw[a0,fg D0 k Y];simp[D0,Dfull,ei,ct]);have ht:cm a<14+k:=by have:=(e0 k Y).1;rw[← a0] at this;rw[b2,a0] at this;exact this
 have hs:cm b<14+k:=by have:=(e0 k Y).2.1;rw[← a0] at this;rw[b1,a0] at this;exact this
 have c6:∀v:F0,v=0\/v=7->v∉O 14 D0 (cm a)/\v∉O 14 D0 (cm b):=(by intro v hv;have e5:(λi:F0=>single v (dx i))=(λu=>decide (u=v)):=(by funext u;rcases hv with rfl|rfl<;>revert u<;>decide +kernel);obtain ⟨f3,g8⟩:=hr v (by rcases hv with rfl|rfl<;>simp);have h1:=a4 (single v) a;have h2:=a4 (single v) b;rw[← a5 (single v) (cm a) Y,e5,f3] at h1;rw[← a5 (single v) (cm b) Y,e5,g8] at h2;exact ⟨λhm=>bF (h1.symm.trans (bD.mp hm)),λhm=>bF (h2.symm.trans (bD.mp hm))⟩);have hd:cg D0:=by
  refine ⟨Y,Y,e2,0,7,o,?_,?_,?_,?_⟩
  ·rw[b2];exact (c6 0 (oL rfl)).1
  ·rw[b1];exact (c6 0 (oL rfl)).2
  ·rw[b2];exact (c6 7 (oR rfl)).1
  ·rw[b1];exact (c6 7 (oR rfl)).2
 have d2:∀m:Nat,∀D:aJ,D.length=m->aV 14 D->be D->cg D->∃D':aJ,a9 14 D'/\be D'/\cg D':=by
  intro m;induction m using sI with
  | ind m ih=>
   intro D hm hS hD hT;by_cases hL:fA 14 D
   ·exact ⟨D,⟨hS,hL,by have:=hT.1;intro he;rw[he] at this;simp at this⟩,hD,hT⟩
   ·simp only[fA,not_forall,not_le] at hL;obtain ⟨w,hw,hC⟩:=hL;have hf:aS D w=0:=Y
    by_cases fc:w<14
    ·exfalso;obtain ⟨x,y,b0,hx,hy⟩:=nX ⟨w,fc⟩;have c3:val D y (aO 14 D)=val D x (aO 14 D):=by
      have e3:aO 14 D≠w:=by unfold aO;omega
      have gs:=gS hS y (λu=>if u=w then y ⟨w,fc⟩ else val D x u)
       (λi hi=>by
        by_cases e1:i=w
        ·subst e1;simp
        ·simp only[e1,iF];rw[ck D x i hi]
         exact b0 ⟨i,hi⟩ (λh=>e1 (kA Fin.val h)))
       (λj hj=>by
        obtain ⟨ha,hb⟩:=im hf j hj;have hq:14+j≠w:=Y
        simp only[hq,ha,hb,iF];exact cu hS x j hj)
       (aO 14 D) (by unfold aO;have:=hT.1;omega)
      simpa[e3] using gs
     exact hx ((hD x).mp (c3▸(hD y).mpr hy))
    ·obtain ⟨j,rfl⟩:∃j,w=14+j:=⟨w-14,Y⟩;have r:j<aM D:=by unfold aM;omega
     have hj:j<D.length:=by unfold aM at r;omega
     let D':=dI 14 j D
     have a2:D'.length=D.length-1:=ii 14 j D hj;have bm:aV 14 D':=lz hS j hj hf;have ev:be D':=λy=>by
      have ho:aO 14 D'=14+(D.length-1)-1:=by unfold aO;rw[a2]
      have hu:b9 (14+j) (14+(D.length-1)-1)=aO 14 D:=(by unfold b9 aO;unfold aM at r;split_ifs<;>omega);rw[ho,jK hS j hj hf y _ (by unfold aM at r;omega),hu];exact hD y
     have es:cg D':=by
      obtain ⟨h1,hz,e4,p,l,c1,g6,g3,g9,f2⟩:=hT;have b6:b9 j (aM D')=aM D:=(by unfold b9 aM;unfold aM at r;rw[a2];split_ifs<;>omega);obtain ⟨et,ea,eb⟩:=jj 14 j D (aM D') (by rw[b6];unfold aM;omega);rw[b6] at et ea eb;obtain ⟨ra,rb⟩:=im hf (aM D) (by unfold aM;omega);have b8:∀a,a≠14+j->b9 (14+j) (dW (14+j) a)=a:=λa ha=>by
       unfold b9 dW;split_ifs<;>omega
      have a7:aM D'<D'.length:=by unfold aM;rw[a2];unfold aM at r;omega
      have a1:∀u:F0,(u∈O 14 D' (aZ D' (aM D'))<->u∈O 14 D (aZ D (aM D)))/\(u∈O 14 D' (aY D' (aM D'))<->u∈O 14 D (aY D (aM D))):=λu=>by
       have eu:aZ D' (aM D')<14+(D.length-1):=by
        have hh:=(bm (aM D') a7).1;have g5:aM D'=D.length-2:=by unfold aM;omega
        omega
       have ej:aY D' (aM D')<14+(D.length-1):=by
        have hh:=(bm (aM D') a7).2.1;have g5:aM D'=D.length-2:=by unfold aM;omega
        omega
       constructor
       ·simp only[bD];dsimp only[D'];rw[jK hS j hj hf (single u) _ eu,ea,b8 _ ra]
       ·simp only[bD];dsimp only[D'];rw[jK hS j hj hf (single u) _ ej,eb,b8 _ rb]
      refine ⟨by rw[a2];unfold aM at r;omega,by rw[a2];omega,by rw[et,e4],p,l,c1,λhm=>g6 ((a1 p).1.1 hm),λhm=>g3 ((a1 p).2.1 hm),λhm=>g9 ((a1 l).1.1 hm),λhm=>f2 ((a1 l).2.1 hm)⟩
     exact ih D'.length (by unfold aM at r;omega) D' rfl bm ev es
 exact d2 D0.length D0 rfl e0 c0 hd
def ng:List (List Nat):=
 [[9,11,12,13,6,5,1,3,4,2],[8,10,11,12,0,6,2,4,5,3],
  [7,9,10,11,1,0,3,5,6,4],[8,9,10,13,6,0,2,5,1,4],
  [7,8,9,12,0,1,3,6,2,5],[7,8,11,13,0,3,1,6,2,4],
  [7,10,12,13,0,3,1,5,4,2],[2,4,5,6,13,12,8,10,11,9],
  [1,3,4,5,7,13,9,11,12,10],[0,2,3,4,8,7,10,12,13,11],
  [1,2,3,6,13,7,9,12,8,11],[0,1,2,5,7,8,10,13,9,12],
  [0,1,4,6,7,10,8,13,9,11],[0,3,5,6,7,10,8,12,11,9]]
def gg (c:F0):List Nat:=ng.getD c.val []
lemma jE:∀c:F0,gA c (gg c):=aa
lemma lI {D:aJ}(hS:aV 14 D)(hD:be D){c i:F0}{l:List Nat}(m:gA c l)(a7:aH c i){z:Nat}(a8:aU 14 D i.val z):eC D (co c) (cK l) z=∅:=by
 refine eO (λk hk=>?_);have a0:=kQ.mp hk;have a6:dA (co c) (cK l):=⟨m.1,m.2.1⟩
 let x:=cj (co c) (cK l) (single k)
 have p:∀u:F0,x u=true->u=c\/u=cK l k:=by
  intro u hu;by_cases a2:u=c
  ·exact oL a2
  ·by_cases a1:aQ c u=true
   ·have hr:co c u=some false:=(by simp[co,a2,a1]);rw[show x u=false from eo _ _ hr] at hu;exact absurd hu bF
   ·have hr:co c u=none:=(by simp[co,a2,a1]);obtain ⟨k',bm⟩:=m.2.1 u |>.mp hr;subst bm;rw[show x (cK l k')=single k k' from eK a6 _ k'] at hu;simp only[single,dT] at hu;exact oR (kA (cK l) hu)
 have a3:cK l k≠c/\¬aH c (cK l k):=by
  have hr:co c (cK l k)=none:=(m.2.1 _).mpr ⟨k,rfl⟩;unfold co at hr;split_ifs at hr with h1 h2
  ·exact ⟨h1,λh=>h2 ((aK _ _).mpr h)⟩
 have b0:¬cN HG x:=by
  rintro ⟨u,v,r,hu,hv⟩;rcases p u hu with rfl|rfl<;>rcases p v hv with rfl|rfl
  ·exact bW _ r
  ·exact a3.2 r
  ·exact a3.2 (bh r)
  ·exact bW _ r
 have a4:cN HG (bs i x):=by
  refine ⟨i,c,bh a7,d7 i x,?_⟩;have b1:co c c=some true:=by simp[co]
  have a5:x c=true:=eo _ _ b1;simp[bs,a5]
 have h0:=(gc hS (bl hD) x i z (c9 hS a8) b0 a4).1;rw[h0] at a0;exact bF a0
lemma dl {D:aJ}(h:a9 14 D)(hD:be D)(b:F0->Nat)(b8:dz 14 D b){c:F0}(hc:c∈aW 14 D)(X N:S0)(Z:Finset Nat)(hX:∀x∈X,x∈aW 14 D/\x≠c/\(∀u∈aR 14 D b,x∈O 14 D u.1->c∈O 14 D u.1)/\∃w,x∈O 14 D w/\c∈O 14 D w)(hN:∀n∈N,n∈aW 14 D/\aH c n/\n∉X)(hZ:∀z∈Z,2≤aS D z/\O 14 D z=∅/\∃i:F0,aH c i/\aU 14 D i.val z):(ru D b c).card+X.card+N.card+Z.card+7≤bH 14 D:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have r:=cX b8;have a7:=jE c;obtain ⟨ca,a5,c2⟩:=a7;have d0:dA (co c) (cK (gg c)):=⟨ca,a5⟩;have hρc:co c c=some true:=by simp[co]
 have hT:∀d a:F0,co c d=some true->HG d a->co c a=some false:=by
  intro d a h1 h2;have hd:d=c:=by
   by_contra p;unfold co at h1;simp only[p,iF] at h1
   split at h1<;>simp at h1
  subst hd;have p:a≠d:=λhac=>bW d (hac▸h2);simp[co,p,(aK d a).2 h2]
 have cb:(λu v:Fin 10=>HG (cK (gg c) u) (cK (gg c) v))=eZ:=(by funext u v;exact propext (by show aH _ _<->fP u v=true;rw[← c2 u v];exact (aK _ _).symm));obtain ⟨E,hE,es,-,ea,-⟩:=kP hS d0 hC
  (λ_ _ huv=>bh huv) hT (by rw[cb];exact fR) (by norm_num)
 have h6:=kM hE (cb▸es)
 let B:=insert c (X∪N)
 have m:∀x∈B,x∈aW 14 D:=by
  intro x k;rcases mI.mp k with rfl|k
  ·exact hc
  ·rcases mU.mp k with k|k
   ·exact (hX x k).1
   ·exact (hN x k).1
 have ct:∀x∈aW 14 D,(⟨b x,0⟩:P0)∈cq 14 D:=λx k=>
  dh.2 ⟨cz.2 (ew hS (w:=b x) (by have:=(r x k).1;omega)),by show 0+1<aS D (b x);have:=(r x k).1;omega⟩
 have b5:iO (λx=>(⟨b x,0⟩:P0)) B:=(by intro x k y hy b6;have h1:b x=b y:=kA Sigma.fst b6;have h2:=(r x (m x k)).2;rw[h1,(r y (m y hy)).2] at h2;exact (sJ h2).symm);have a4:iO (λz=>(⟨z,0⟩:P0)) Z:=λ_ _ _ _ b6=>kA Sigma.fst b6
 let S1:=ru D b c
 let S2:=B.image (λx=>(⟨b x,0⟩:P0))
 let S3:=Z.image (λz=>(⟨z,0⟩:P0))
 have c6:Disjoint S1 S2:=(by rw[dL];intro u b0 b1;obtain ⟨x,k,rfl⟩:=mM.mp b1;exact (mD.mp (bb.mp b0).1).2 (mM.mpr ⟨x,m x k,rfl⟩));have c7:Disjoint S1 S3:=(by rw[dL];intro u b0 a8;obtain ⟨z,hz,rfl⟩:=mM.mp a8;have p:=(mF.mp (mD.mp (bb.mp b0).1).1).2;rw[(hZ z hz).2.1] at p;exact nN p);have c0:Disjoint S2 S3:=(by rw[dL];intro u b1 a8;obtain ⟨x,k,rfl⟩:=mM.mp b1;obtain ⟨z,hz,c3⟩:=mM.mp a8;have h1:z=b x:=kA Sigma.fst c3;have h2:=(r x (m x k)).2;rw[← h1,(hZ z hz).2.1] at h2;exact singleton_ne_empty x h2.symm);have c8:S1∪S2∪S3⊆cq 14 D:=by
  intro u l;rcases mU.mp l with l|l
  ·rcases mU.mp l with l|l
   ·exact (mF.mp (mD.mp (bb.mp l).1).1).1
   ·obtain ⟨x,k,rfl⟩:=mM.mp l;exact ct x (m x k)
  ·obtain ⟨z,hz,rfl⟩:=mM.mp l;exact dh.2 ⟨cz.2 (ew hS (w:=z) (by have:=(hZ z hz).1;omega)),by show 0+1<aS D z;have:=(hZ z hz).1;omega⟩
 have b2:∀u∈S1∪S2∪S3,u∉fF D (co c) (cK (gg c)):=by
  intro u l;rcases mU.mp l with l|l
  ·rcases mU.mp l with l|l
   ·exact λhk=>iu hS hρc (bb.mp l).2 (iq hk)
   ·obtain ⟨x,k,rfl⟩:=mM.mp l;rcases mI.mp k with rfl|k
    ·exact λhk=>iu hS hρc (by
      show x∈O 14 D (b x);rw[(r x hc).2];exact mX x)
      (iq hk)
    ·rcases mU.mp k with k|k
     ·obtain ⟨bm,a2,c5,w,hw⟩:=hX x k;obtain ⟨z,d2,ec⟩:=hG.2.2.1 x c a2;obtain ⟨eu,-,-,e,he,-,ej⟩:=jq hG h hC b r a2 bm c5 hw d2 ec
      have et:b x∈bJ 14 D x c:=gB.2 (by
       rw[(r x bm).2]
       exact ⟨mX x,λhcx=>a2 (mS.1 hcx).symm⟩)
      exact λhk=>kN (jN hS hρc et (r x bm).1 eu he ej)
       (iq hk)
     ·exact lt (lI hS hD (jE c) (hN x k).2.1 (b8 x (hN x k).1).2.2.1)
  ·obtain ⟨z,hz,rfl⟩:=mM.mp l;obtain ⟨i,d1,er⟩:=(hZ z hz).2.2;exact lt (lI hS hD (jE c) d1 er)
 have a1:Disjoint X N:=disjoint_right.mpr (λn hn=>(hN n hn).2.2);have a6:c∉X∪N:=by
  intro eb;rcases mU.mp eb with hm|hm
  ·exact (hX c hm).2.1 rfl
  ·exact bW c (hN c hm).2.1
 have a0:B.card=1+X.card+N.card:=(by rw[cI a6,cU a1];omega);have a3:(S1∪S2∪S3).card=(ru D b c).card+(1+X.card+N.card)+Z.card:=(by rw[cU (disjoint_union_left.mpr ⟨c7,c0⟩),cU c6,cJ b5,cJ a4,a0]);have c1:=ly _ c8 b2;rw[a3] at c1;omega
lemma pu:∀M:Finset (Fin 7),(M.card=1->3≤((M.image cs).biUnion (λc=>aX c∩bX 0)).card)/\(M.card=2->5≤((M.image cs).biUnion (λc=>aX c∩bX 0)).card)/\(M.card=3->6≤((M.image cs).biUnion (λc=>aX c∩bX 0)).card)/\(M.card=4->6≤((M.image cs).biUnion (λc=>aX c∩bX 0)).card)/\(5≤M.card->7≤((M.image cs).biUnion (λc=>aX c∩bX 0)).card):=aa
lemma ld {D:aJ}(h:a9 14 D)(hD:be D)(P:S0)(hP:∀a∈P,∀b∈P,¬aH a b)(Q M:S0)(hM:M⊆Q)(b2:M.card=bu 14 D)(hQ:∀i∈Q,i∈aN 14 D/\aX i⊆P)(a5:∀i∈M,¬bq 14 D P (aX i)):∀j∈Q \ M,aU 14 D j.val (aO 14 D):=by
 classical
 have hG:=bn;have hC:=bl hD;have p:∀i∈M,∀q,(∀a∈P,(a∈O 14 D q<->aH i a))->False:=(by intro i l q r;refine a5 i l ⟨q,?_⟩;ext a;rw[mN,ce];exact ⟨λh1=>(r a h1.2).1 h1.1,λh1=>⟨(r a ((hQ i (hM l)).2 (ce.2 h1))).2 h1,(hQ i (hM l)).2 (ce.2 h1)⟩⟩);have hb:∀i∈M,∃b,aU 14 D i.val b/\2≤aS D b/\O 14 D b=∅:=by
  intro i l;rcases cr hG h hC (hQ i (hM l)).1 with a2|hb
  ·obtain ⟨j,s,-,-,-,r⟩:=fW hG h.1 hC P hP a2;exact (p i l _ r).elim
  ·exact hb
 choose! β hβ using hb
 have a4:iO β M:=by
  intro i l j hj a0;by_contra b1;obtain ⟨a,m,a3⟩:=gv j i (nS b1);obtain ⟨k,s,-,-,-,-,r⟩:=iv hG h.1 hC P hP (hβ i l).1
   (c9 h.1 (a0▸(hβ j hj).1)) ⟨a,(hQ j (hM hj)).2 (ce.2 m),m,a3⟩
  exact p i l _ r
 intro j hj;rw[mD] at hj;rcases cr hG h hC (hQ j hj.1).1 with a2|⟨z,b0,a7,a8⟩
 ·exact a2
 ·exfalso;by_cases a6:z∈M.image β
  ·obtain ⟨i,l,bm⟩:=mM.mp a6;have a0:j≠i:=λhe=>hj.2 (he▸l);obtain ⟨a,m,a3⟩:=gv j i a0;obtain ⟨k,s,-,-,-,-,r⟩:=iv hG h.1 hC P hP (hβ i l).1
    (c9 h.1 (bm.symm▸b0)) ⟨a,(hQ j hj.1).2 (ce.2 m),m,a3⟩
   exact p i l _ r
  ·have a1:=li h.1 (insert z (M.image β)) (λw hw=>by
    rcases mI.mp hw with rfl|hw
    ·exact ⟨a7,a8⟩
    ·obtain ⟨i,l,rfl⟩:=mM.mp hw
     exact (hβ i l).2)
   rw[cI a6,cJ a4] at a1;omega
lemma gU {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D){i:F0}(_hi:i∈aN 14 D)(a0:aU 14 D i.val (aO 14 D)):∃s:Bool,aU 14 D i.val (W D (aM D,!s))/\O 14 D (W D (aM D,!s))⊆{i}/\∀a:F0,aH i a->a∈O 14 D (W D (aM D,s)):=by
 have hS:=h.1;have a2:aM D<D.length:=by unfold aM;have:=hT.1;omega
 have l:aO 14 D=14+aM D:=by unfold aO aM;have:=hT.1;omega
 rw[l] at a0;rcases cT a0 with a4|⟨w,m,p⟩
 ·have:=i.isLt;omega
 ·obtain ⟨j,s',hj,a3,r⟩:=dN.mp p.1;have a1:j=aM D:=Y
  subst a1;have k:W D (aM D,!(!s'))=w:=by rw[bK];exact r
  refine ⟨!s',k▸m,?_,λa hia=>?_⟩
  ·rw[k];exact dZ bn hS (bl hD) i w (c9 hS m)
  ·exact iY bn hS (bl hD) a2 (!s') hT.2.2.1
    (k▸m) (k▸p.2) (by rw[l]) hia
lemma om:∀i j:F0,i≠j->∃a b:F0,aQ i a=true/\aQ j b=true/\aQ a b=false:=aa
lemma kD {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D){i j:F0}(a0:i≠j){l r:Bool}(hi:∀a,aH i a->a∈O 14 D (W D (aM D,l)))(hj:∀b,aH j b->b∈O 14 D (W D (aM D,r))):l=r:=by
 by_contra a6;obtain ⟨a,b,a5,a2,a4⟩:=om i j a0;have ha:=hi a ((aK _ _).mp a5);have hb:=hj b ((aK _ _).mp a2);have a3:aM D<D.length:=by unfold aM;have:=hT.1;omega
 have m:aO 14 D=14+aM D:=by unfold aO aM;have:=hT.1;omega
 have a1:r=!l:=by cases l<;>cases r<;>simp_all
 rw[a1] at hb;have p:val D (aL a b) (aO 14 D)=true:=(by rw[m,cc h.1 _ a3 l,hT.2.2.1,gop_true,bA];exact ⟨cf h.1 ha (by simp[aL]),cf h.1 hb (by simp[aL])⟩);have k:=(hD _).mp p;have hp:=(ds a b).mp k;exact bw.mp a4 hp
lemma dj {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D){i j:F0}(a0:i≠j)(hi:i∈aN 14 D)(hj:j∈aN 14 D)(a4:aU 14 D i.val (aO 14 D))(a5:aU 14 D j.val (aO 14 D)):∃s:Bool,O 14 D (W D (aM D,!s))=∅/\(∀a,aH i a->a∈O 14 D (W D (aM D,s)))/\(∀a,aH j a->a∈O 14 D (W D (aM D,s)))/\∀k∈aN 14 D,aU 14 D k.val (aO 14 D)->∀a,aH k a->a∈O 14 D (W D (aM D,s)):=by
 obtain ⟨si,-,m,l⟩:=gU h hD hT hi a4;obtain ⟨sj,-,p,a3⟩:=gU h hD hT hj a5;have a6:=kD h hD hT a0 l a3;subst a6;have a2:O 14 D (W D (aM D,!si))=∅:=(by refine eO (λx hx=>?_);have h1:=mS.mp (m hx);have h2:=mS.mp (p hx);exact a0 (h1.symm.trans h2));refine ⟨si,a2,l,a3,λk hk hck a hka=>?_⟩;obtain ⟨sk,-,-,r⟩:=gU h hD hT hk hck;by_cases a1:k=i
 ·subst a1;exact l a hka
 ·rw[kD h hD hT a1 r l] at r;exact r a hka
lemma cV {D:aJ}(m:be D)(k:cg D){s:Bool}{v:F0}(l:v∈O 14 D (W D (aM D,s))):(aM D,s)∈aG 14 D v:=by
 refine aP.mpr ⟨by unfold aM;have:=k.1;omega,l,?_⟩;have h:aO 14 D=14+aM D:=by unfold aO aM;have:=k.1;omega
 rw[← h,c4 m];exact nE v
lemma cw {D:aJ}{h:F0->A0}(k:ch 14 HG D h){s:Bool}(l:O 14 D (W D (aM D,!s))=∅){i:F0}(r:i∈aN 14 D):(aM D,s)≠h i:=by intro m;have p:=(k.1 i r).2.2.2;rw[← m] at p;rw[l] at p;exact singleton_ne_empty i p.symm
lemma lY {D:aJ}(h:a9 14 D)(hD:be D)(r:cg D)(P:S0)(a0:P⊆bX 0)(ca:P⊆aW 14 D)(Oc Ct I:S0)(a5:∀i∈Oc,aX i⊆P/\bq 14 D P (aX i))(a8:∀c∈Ct,c∉Oc/\((aX c∩P).card≤2\/(aX c⊆P/\¬bq 14 D P (aX c))))(hI:∀i∈I,i∈aN 14 D/\aX i⊆P){s:Bool}(bm:O 14 D (W D (aM D,!s))=∅)(a3:3≤(O 14 D (W D (aM D,s))∩P).card):2*Oc.card+I.card+1+(Ct.biUnion (λc=>aX c∩P)).card+(aW 14 D).card≤2*P.card+br 14 D:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨b,hb⟩:=dY h hD;obtain ⟨a7,m⟩:=cR hG h hC;have cb:∀a∈P,∀b∈P,¬aH a b:=λa k b hb=>eg 0 a (a0 k) b (a0 hb);have c0:P.card≤7:=(cL a0).trans o
 let E0:Finset (A0):=I.image a7
 have a2:E0.card=I.card:=cJ
  (λi l j hj hij=>m.2 i (hI i l).1 j (hI j hj).1 hij)
 have p:(aM D,s)∉E0:=(by intro hm;obtain ⟨i,l,b8⟩:=mM.mp hm;exact cw m bm (hI i l).1 b8.symm)
 let E:=insert (aM D,s) E0
 have b6:E.card=I.card+1:=(by rw[cI p,a2]);have hE:∀e∈E,e∈bo 14 D (ba 14 D P)/\3≤(O 14 D (W D e)∩P).card:=by
  intro e he;rcases mI.mp he with rfl|he
  ·refine ⟨?_,a3⟩;rw[bo,mF];have b2:aO 14 D=14+aM D:=by unfold aO aM;have:=r.1;omega
   refine ⟨mP.mpr ⟨mR.mpr (by unfold aM;have:=r.1;omega),mV _⟩,dO.mpr (cO.mp Y),?_⟩;rw[dO,← b2,c4 hD,eI];exact nN
  ·obtain ⟨i,l,rfl⟩:=mM.mp he;obtain ⟨h1,h2,h3,-⟩:=m.1 i (hI i l).1;have a6:aX i⊆O 14 D (W D (a7 i))∩P:=λa k=>mN.mpr ⟨h3 a (ce.mp k),(hI i l).2 k⟩;have hc:=cL a6;have c1:(aX i).card=3:=dH i;refine ⟨?_,Y⟩;rw[bo,mF];refine ⟨mP.mpr ⟨mR.mpr h1,mV _⟩,dO.mpr (cO.mp Y),?_⟩;rw[dO,h2,eI];exact nN
 have a4:∀f∈Ct.biUnion (λc=>aX c∩P),∃c∈Ct,f∈aX c∩P:=λf hf=>mB.1 hf
 choose! ct hct using a4
 have a1:=kK h.1 c0 (Oc.image aX)
  (λT r=>by
   obtain ⟨i,l,rfl⟩:=mM.1 r
   exact ⟨dH i,(a5 i l).2⟩)
  (λT r T' hT' hne=>by
   obtain ⟨i,l,rfl⟩:=mM.1 r;obtain ⟨j,hj,rfl⟩:=mM.1 hT';have:=gP i j (λhij=>hne (hij▸rfl)) univ
   simpa[aX] using this)
  E hE (Ct.biUnion (λc=>aX c∩P)) (λf=>aX (ct f)∩P)
  (λf hf=>by
   obtain ⟨hc,b5⟩:=hct f hf;refine j3 hG h.1 hC (X:=insert (ct f) (P \ (aX (ct f)∩P)))
    iR ?_ ?_ (λa k=>mK k) b5
    ⟨ct f,mL _ _,bh (ce.1 (mN.1 b5).1)⟩
   ·rcases (a8 _ hc).2 with h2|⟨h2,h4⟩
    ·exact oL h2
    ·rw[qL.2 h2];exact oR ⟨dH _,h4⟩
   ·have b1:∀a∈P \ (aX (ct f)∩P),¬aH (ct f) a:=by
     intro a k b0;rw[mD,mN,ce] at k;exact k.2 ⟨b0,k.1⟩
    intro a k b hb;rcases mI.1 k with rfl|k<;>rcases mI.1 hb with rfl|hb
    ·exact bW _
    ·exact b1 b hb
    ·exact λhab=>b1 a k (bh hab)
    ·exact cb a (mD.1 k).1 b (mD.1 hb).1)
  (λf hf T r=>by
   obtain ⟨i,l,rfl⟩:=mM.1 r;have:=gP (ct f) i (λhij=>(a8 _ (hct f hf).1).1 (hij▸l)) P
   rwa[show univ.filter (λz=>aH i z)∩P=aX i from qL.2 (a5 i l).1] at this)
 have h4:=d9 h P (by rw[c4 hD];simp);have h5:=eN h.1 b hb P;rw[qL.2 ca] at h5;rw[af _ (λi j hij=>lB hij),b6] at a1;omega
lemma oV {D:aJ}(h:a9 14 D)(hD:be D)(hB:br 14 D≤(aW 14 D).card+3)(b:F0->Nat)(hb:cn 14 D b){T J:S0}(a3:dU T J=true)(hJ:∀i∈J,i∈aN 14 D)(a1:∀i∈J,bq 14 D T (aX i∩T)):(∀t∈T,(aG 14 D t).card≤3/\bi 14 D (ba 14 D {t})=∅)/\∀u∈aR 14 D b,(O 14 D u.1∩T).Nonempty:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨l,p⟩:=cR hG h hC;obtain ⟨a5,a7⟩:=gp a3 hJ;obtain ⟨-,-,⟨a8,bm⟩,hside,hinj,hgeo⟩:=gr a3;have a0:iO (λi=>aX i∩T) J:=λi m j hj hij=>hinj j hj i m (by rw[show aX i∩T=aX j∩T from hij]);obtain ⟨k,hT,hU⟩:=oy hG h hC b hb p T J (tA T) a5 a7
  (J.image (λi=>aX i∩T)) (λX hX=>by
   obtain ⟨i,m,rfl⟩:=mM.1 hX
   exact ⟨(hside i m).2.2.2,a1 i m⟩) a8
  (by rw[cJ a0];omega)
 refine ⟨λt ht=>⟨?_,(hT t ht).1⟩,hU⟩;obtain ⟨e1,a6⟩:=(hT t ht).2;have a2:aG 14 D t⊆insert e1 ((J.filter (λi=>aQ i t=true)).image l):=by
  intro e he;rcases a6 e he with rfl|h1
  ·exact mL _ _
  ·obtain ⟨i,m,rfl⟩:=mM.1 h1;refine mK (mM.2 ⟨i,mF.2 ⟨m,?_⟩,rfl⟩);by_contra r;rw[bT] at r;refine k (W D (l i)) (λa ha=>?_);by_cases a4:a=t
   ·rw[a4];exact (aP.1 he).2.1
   ·exact (p.1 i (hJ i m)).2.2.1 a
     (ce.1 ((hgeo t ht).2 i m r (mE.2 ⟨a4,ha⟩)))
 have h1:=cL a2;have h2:=card_insert_le e1 ((J.filter (λi=>aQ i t=true)).image l);have h4:=cG (s:=J.filter (λi=>aQ i t=true)) (f:=l);have h5:=(hgeo t ht).1;omega
lemma fM {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(hB:br 14 D≤(aW 14 D).card+3){T J:S0}(ca:dU T J=true)(hJ:∀i∈J,i∈aN 14 D){i1 i2:F0}(p:i1∈J)(m:i2∈J)(a8:i1≠i2)(c3:aU 14 D i1.val (aO 14 D))(c1:aU 14 D i2.val (aO 14 D)):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,hb⟩:=dY h hD;obtain ⟨b5,a0⟩:=cR hG h hC;obtain ⟨a7,a6⟩:=gp ca hJ;obtain ⟨-,-,⟨c2,e7⟩,hside,hinj,hgeo⟩:=gr ca;obtain ⟨s,ct,eb,er,-⟩:=dj h hD hT a8 (hJ i1 p) (hJ i2 m) c3 c1;have a5:T⊆O 14 D (W D (aM D,s)):=by
  intro t ht;by_cases k:aH i1 t
  ·exact eb t k
  ·have ej:aQ i1 t=false:=bw.mpr k;have eu:=(hgeo t ht).2 i1 p ej;have h2:aH i2 t:=by
    by_contra h2;have ez:aQ i2 t=false:=bw.mpr h2;have a3:=(hgeo t ht).2 i2 m ez;have c5:aX i1∩T=T.erase t:=eS
     (λa ha=>mE.mpr ⟨λhat=>k (hat▸ce.mp (mN.mp ha).1),(mN.mp ha).2⟩)
     (by rw[cE ht,c2,(hside i1 p).2.2.2])
    have c7:aX i2∩T=T.erase t:=eS
     (λa ha=>mE.mpr ⟨λhat=>h2 (hat▸ce.mp (mN.mp ha).1),(mN.mp ha).2⟩)
     (by rw[cE ht,c2,(hside i2 m).2.2.2])
    exact a8 (hinj i1 p i2 m (by rw[c5,c7])).symm
   exact er t h2
 obtain ⟨cb,b0⟩:=gh a0 T J (λi hi=>⟨(a7 i hi).1,(a7 i hi).2.1⟩);have e1:∀f∈T,∃e:A0,e.1<D.length/\bf D e.1=true/\f∈O 14 D (W D e)/\f∉O 14 D (14+e.1)/\Disjoint (O 14 D (W D e)) (tA T f):=(by intro f hf;obtain ⟨j,s',k,h2,h4,h5,h6⟩:=fq hG hS hC (tA T f) (a6 f hf).1 f (a6 f hf).2.2;exact ⟨(j,s'),k,h2,h4,h5,h6⟩)
 choose! w hw using e1
 have bm:iO w T:=by
  intro f hf g hg ea;by_contra e2;exact dL.1 (hw f hf).2.2.2.2 (ea▸(hw g hg).2.2.1)
   ((a6 f hf).2.1 (mE.2 ⟨λh=>e2 h.symm,hg⟩))
 have b8:Disjoint (J.image b5) (T.image w):=by
  rw[dL];intro e ec es;obtain ⟨i,hi,rfl⟩:=mM.1 ec;obtain ⟨f,hf,ev⟩:=mM.1 es;obtain ⟨a,ha,e0⟩:=(a7 i hi).2.2 f hf;exact dL.1 (hw f hf).2.2.2.2
   (ev▸(a0.1 i (a7 i hi).1).2.2.1 a e0) ha
 have a3:T.image w⊆bo 14 D (ba 14 D T):=by
  intro e he;obtain ⟨f,hf,rfl⟩:=mM.1 he;obtain ⟨k,h2,h4,h5,h6⟩:=hw f hf;refine e6.2 ⟨k,⟨f,mN.2 ⟨h4,hf⟩⟩,?_⟩;rintro ⟨g,hg⟩;rw[mN] at hg;have et:g∈O 14 D (W D (w f)):=de hS k h2 (w f).2 hg.1;exact dL.1 h6 et
   ((a6 f hf).2.1 (mE.2 ⟨λh=>h5 (h▸hg.1),hg.2⟩))
 have a4:(aM D,s)∈bo 14 D (ba 14 D T):=by
  obtain ⟨t0,c0⟩:=cO.mp (by omega:0<T.card);have d0:aO 14 D=14+aM D:=by unfold aO aM;have:=hT.1;omega
  refine e6.2 ⟨by unfold aM;have:=hT.1;omega,⟨t0,mN.mpr ⟨a5 c0,c0⟩⟩,?_⟩;rw[← d0,c4 hD,eI];exact nN
 have a1:(aM D,s)∉J.image b5:=(by intro hm;obtain ⟨i,hi,b1⟩:=mM.mp hm;exact cw a0 ct (hJ i hi) b1.symm);have a2:(aM D,s)∉T.image w:=by
  intro hm;obtain ⟨f,hf,b1⟩:=mM.mp hm;obtain ⟨g,hg⟩:=cO.mp (show 0<(T.erase f).card by rw[cE hf];omega);exact dL.1 (hw f hf).2.2.2.2 (b1▸a5 (mO hg))
   ((a6 f hf).2.1 hg)
 have e5:7≤(bo 14 D (ba 14 D T)).card:=by
  have k:=cL
   (iS.mpr ⟨a4,uS cb a3⟩)
  rw[cI (by simp[a1,a2]),cU b8,b0,cJ bm] at k;omega
 have b2:bq 14 D T (aX i1∩T):=by
  obtain ⟨j,s',-,-,-,hq⟩:=fW hG hS hC T
   (λa ha b hb=>eg 0 a ((hside i1 p).1 ha) b ((hside i1 p).1 hb)) c3
  refine ⟨W D (j,s'),?_⟩;ext a;simp only[mN,ce];exact ⟨λk=>⟨(hq a k.2).mp k.1,k.2⟩,λk=>⟨(hq a k.2).mpr k.1,k.2⟩⟩
 have b6:bq 14 D T (aX i2∩T):=by
  obtain ⟨j,s',-,-,-,hq⟩:=fW hG hS hC T
   (λa ha b hb=>eg 0 a ((hside i2 m).1 ha) b ((hside i2 m).1 hb)) c1
  refine ⟨W D (j,s'),?_⟩;ext a;simp only[mN,ce];exact ⟨λk=>⟨(hq a k.2).mp k.1,k.2⟩,λk=>⟨(hq a k.2).mpr k.1,k.2⟩⟩
 obtain ⟨i3,l⟩:∃i3∈J,i3≠i1/\i3≠i2:=by
  have:(J \ {i1,i2}).Nonempty:=cO.mp (by
   have d2:({i1,i2}:S0)⊆J:=(by simp[iS,p,m]);have:=sP d2
   rw[cP a8] at this;omega)
  obtain ⟨i3,l⟩:=this;rw[mD,mI,mS,nO] at l;exact ⟨i3,l.1,l.2.1,l.2.2⟩
 let M1:=aX i1∩T
 let M2:=aX i2∩T
 let M3:=O 14 D (W D (b5 i3))∩T
 have r:aX i3∩T⊆M3:=λa ha=>by
  rw[mN,ce] at ha;exact mN.mpr ⟨(a0.1 i3 (hJ i3 l.1)).2.2.1 a ha.1,ha.2⟩
 have c6:M1≠M2:=λhe=>a8 (hinj i2 m i1 p (by show M1⊆M2;rw[he]));have d1:M1≠M3:=λhe=>l.2.1 (hinj i1 p i3 l.1 (by show aX i3∩T⊆M1;rw[he];exact r));have c8:M2≠M3:=λhe=>l.2.2 (hinj i2 m i3 l.1 (by show aX i3∩T⊆M2;rw[he];exact r));have e4:({M1,M2,M3}:Finset (S0)).card=3:=(by rw[cI (by simp[c6,d1]),cP c8]);have e3:3≤(bi 14 D (ba 14 D T)).card:=by
  have k:=fy hS T {M1,M2,M3} (λM hM=>by
   simp only[mI,mS] at hM;rcases hM with rfl|rfl|rfl
   ·exact ⟨by rw[(hside i1 p).2.2.2],b2⟩
   ·exact ⟨by rw[(hside i2 m).2.2.2],b6⟩
   ·exact ⟨by have:=cL r;rw[(hside i3 l.1).2.2.2] at this;exact this,⟨_,rfl⟩⟩)
  have h2:(dk 14 D T).card≤(bi 14 D (ba 14 D T)).card:=cL (fS _ _);omega
 have h4:=d9 h T (by rw[c4 hD];simp);have h5:=eN hS b hb T;have h6:=cL (iL:T∩aW 14 D⊆T);omega
lemma nw:∀i j a:F0,i≠j->a≠i->a≠j->aQ i a=false->∃b:F0,aQ j b=true/\aQ i b=false/\aQ a b=false:=aa
lemma i6 {D:aJ}(h:a9 14 D)(hD:be D){l:F0->A0}(a2:ch 14 HG D l){i v:F0}(hi:i∈aN 14 D)(b6:aH i v)(hv:∀p∈aG 14 D v,p.1≠(l i).1->¬O 14 D (W D (aI p))⊆{i})(b2:aU 14 D i.val (aO 14 D)\/∃j∈aN 14 D,j≠i/\∃z,aU 14 D i.val z/\aU 14 D j.val z):∀t:F0,t∈O 14 D (W D (l i))<->aH i t:=by
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have ec:=fj h hD a2 hi;obtain ⟨e0,g6,fl,c6,e5,g3,g0,-⟩:=eJ hG h hC hi;have c0:aI (l i)=e0:=sJ (ec.symm.trans g0);have a0:O 14 D (W D (aI (l i)))={i}:=c0▸c6;have r:(l i).1<D.length:=(a2.1 i hi).1;have a7:bf D (l i).1=true:=by
  have h1:(l i).1=e0.1:=by rw[← c0];rfl
  rw[h1];exact fl
 have a3:aU 14 D i.val (14+(l i).1):=(by have h1:=fJ hS hi (by rw[a0];exact mX i);have c3:aS D (W D (aI (l i)))=1:=(by have g7:=eG.mp hi (W D (aI (l i))) (by rw[a0];exact mX i);have g5:1≤aS D (W D (aI (l i))):=eU (b4 (n:=14) r (!(l i).2));omega);exact rT h1 ⟨b4 (n:=14) r (!(l i).2),c3⟩);have a1:∀(w:Nat) (t:F0),aU 14 D (14+(l i).1) w->val D (aL i t) (14+(l i).1)=true->val D (aL i t) w=false->False:=by
  intro w t c2 f2 c5;have g2:∃a c,aU 14 D (14+(l i).1) a/\bk 14 D a c/\aS D a=1/\val D (aL i t) a=true/\val D (aL i t) c=false:=by
   induction c2 with
   | refl=>rw[f2] at c5;exact absurd c5.symm bF
   | @tail a c hab hbc ih=>
    by_cases ha:val D (aL i t) a=true
    ·exact ⟨a,c,hab,hbc.1,hbc.2,ha,c5⟩
    ·exact ih (bE.mpr ha)
  obtain ⟨a,c,cb,c7,c3,f1,ea⟩:=g2;obtain ⟨j,s,hj,rfl,bm⟩:=dN.mp c7;have ca:bf D j=true:=(by by_contra ez;rw[bT] at ez;rw[cc hS _ hj s,ez,gop_false,bm,f1] at ea;exact absurd ea.symm bF);have es:j≠(l i).1:=(by have:=bV hS (λ_ _ h=>h.1) cb;have:=bv hS hj s;omega);have a8:aU 14 D i.val a:=a3.trans cb;have ct:O 14 D a⊆{i}:=dZ hG hS hC i a (c9 hS a8);have f0:v≠i:=λh=>bW i (h▸b6);have a5:W D (j,!(!s))=a:=by rw[bK];exact bm
  have et:v∈O 14 D (W D (j,!s)):=iY hG hS hC hj (!s) ca (a5▸a8) (a5▸c3)
    (by unfold aO;omega) b6
  have hp:(j,!s)∈aG 14 D v:=aP.mpr ⟨hj,et,λhc=>f0 (mS.mp (ct (bm▸de hS hj ca s hc)))⟩;exact hv (j,!s) hp es (by rw[show aI (j,!s)=(j,!(!s)) from rfl,a5];exact ct)
 have a4:∀a u w,aU 14 D a u->aU 14 D a w->aU 14 D u w\/aU 14 D w u:=by
  intro a u w hu hw;induction hu using rI generalizing w with
  | refl=>exact oL hw
  | @head a c hac _ ih=>
   rcases cH hw with rfl|⟨c',d2,c8⟩
   ·exact oR (rH hac ‹_›)
   ·have f3:c'=c:=cY d2.1 hac.1 hac.2;subst f3;exact ih w c8
 have m:∀w,aU 14 D i.val w->14+(l i).1≤w->aU 14 D (14+(l i).1) w:=by
  intro w c2 b1;rcases a4 i.val (14+(l i).1) w a3 c2 with h1|h2
  ·exact h1
  ·have g4:=bV hS (λ_ _ hh=>hh.1) h2;have e3:w=14+(l i).1:=Y
   rw[e3];exact rF
 intro t;refine ⟨λht=>?_,λht=>(a2.1 i hi).2.2.1 t ht⟩;by_contra b5;have fi:t≠i:=λhe=>by
  have e2:i∈O 14 D (W D (l i)):=he▸ht;have d0:=gf hS (by rw[ec];exact mX _);rw[aT] at d0;exact d0 (aP.mpr ⟨r,e2,by rw[(a2.1 i hi).2.1];exact nE _⟩)
 have b8:i∈O 14 D (W D ((l i).1,!(l i).2)):=(by show i∈O 14 D (W D (aI (l i)));rw[a0];exact mX i);have a6:val D (aL i t) (14+(l i).1)=true:=(by rw[cc hS _ r (l i).2,a7,gop_true,bA];exact ⟨cf hS ht (by simp[aL]),cf hS b8 (by simp[aL])⟩);rcases b2 with eu|⟨j,hj,e4,z,ev,g1⟩
 ·have b1:14+(l i).1≤aO 14 D:=by unfold aO;omega
  have h0:val D (aL i t) (aO 14 D)=false:=(by by_contra h1;rw[bN] at h1;exact b5 ((ds i t).mp ((hD _).mp h1)));exact a1 (aO 14 D) t (m _ eu b1) a6 h0
 ·have e7:t≠j:=λhe=>by
   subst he;have:=i8 hG hS hC hj ht;have h7:=(a2.1 i hi).2.2.1 v b6;rw[this,mS] at h7;exact cl.mp hj (h7▸(ij hG h hC b6).resolve_left (cl.mp hi))
  obtain ⟨b0,gs,ej,d1⟩:=nw i j t e4.symm fi e7 (bw.mpr b5);have fz:¬cN HG (bt {i,t,b0}):=by
   refine jv (λx hx y hy=>?_);simp only[mI,mS] at hx hy;rcases hx with rfl|rfl|rfl<;>rcases hy with rfl|rfl|rfl
   ·exact bW _
   ·exact b5
   ·exact bw.mp ej
   ·exact λhh=>b5 (bh hh)
   ·exact bW _
   ·exact bw.mp d1
   ·exact λhh=>bw.mp ej (bh hh)
   ·exact λhh=>bw.mp d1 (bh hh)
   ·exact bW _
  have e1:cN HG (bs j (bt {i,t,b0})):=⟨j,b0,(aK _ _).mp gs,d7 j _,by simp[bs,bt]⟩;have fc:=(gc hS hC _ j z (c9 hS g1) fz e1).1;have c1:val D (aL i t) z=false:=by
   by_contra h1;rw[bN] at h1
   have hm:=el hS (aL i t) (bt {i,t,b0}) (λu hu=>by
    simp only[aL,bO,dT] at hu;simp only[bt,dT,mI,mS]
    rcases hu with rfl|rfl<;>tauto) z h1
   rw[fc] at hm;exact bF hm
  have b1:14+(l i).1≤z:=by
   by_contra g8;have er:val D (single t) z=false:=by
    by_contra h1;rw[bN] at h1
    have:=el hS (single t) (aL i t) (λu hu=>by
     simp only[single,dT] at hu;simp[aL,hu]) z h1
    rw[c1] at this;exact bF this
   have eb:val D (single t) (14+(l i).1)=false:=by
    by_contra h1;rw[bN] at h1
    have:t∈O 14 D (14+(l i).1):=bD.mpr h1
    rw[(a2.1 i hi).2.1] at this;exact nE _ this
   have h2:=gW hS (single t) (aL i t) i (by intro k hk;simp[single,aL,hk])
    z (14+(l i).1) (ip hS ev Y) (by rw[er,c1])
   rw[eb,a6] at h2;exact bF h2
  exact a1 z t (m z ev b1) a6 c1
local instance instDecAdj4874 (a b:F0):Decidable (aH a b):=
 decidable_of_iff (aQ a b=true) (aK a b)
lemma ow:∀a∈({0,1,2,5}:S0),∀b∈({0,1,2,5}:S0),a≠b->(a∈({0,1,2}:S0)/\b∈({0,1,2}:S0))\/(a∈({0,1,5}:S0)/\b∈({0,1,5}:S0))\/(a∈({0,2,5}:S0)/\b∈({0,2,5}:S0))\/(a∈({1,2,5}:S0)/\b∈({1,2,5}:S0)):=aa
lemma nV:dU {7,9,10} {0,1,5}=true:=aa
lemma ny:dU {8,10,12} {0,2,5}=true:=aa
lemma mf:dU {9,12,13} {1,2,5}=true:=aa
lemma oG:∀i∈({0,1,2}:S0),∀j∈({0,1,2}:S0),j≠i->∃a∈({7,8,13}:S0),aH j a/\¬aH i a:=aa
lemma en:∀i∈({0,1,3}:S0),i∈({0,1,2,3}:S0)/\aH i 7:=aa
lemma pD:∀x∈d6,x∉({0,1,2,3}:S0)/\x≠7/\∃i∈({0,1,3}:S0),aH i x/\aH i 7:=aa
lemma mC:(8:F0)≠12/\(2:F0)≠0/\(2:F0)≠3/\(0:F0)≠3/\aH 2 8/\aH 0 8/\aH 8 6/\(6:F0)≠2/\(6:F0)≠0/\(6:F0)≠3/\aH 2 12/\aH 3 12/\aH 12 5/\(5:F0)≠2/\(5:F0)≠3/\(5:F0)≠0/\aH 0 7/\(7:F0)≠8/\¬aH 7 12:=aa
lemma oo:∀l∈b7,∃i∈({0,1,2,5}:S0),∃j∈({0,1,2,5}:S0),∃z:F0,i≠j/\aH i l/\aH j l/\aH l z/\z≠i/\z≠j:=aa
lemma lx:∀l∈b7,l∉({0,1,2,5}:S0)/\∃z:F0,aH l z/\z∉({0,1,2,5}:S0)/\z∉b7:=aa
lemma p5:∀a∈b7,∀b∈b7,∀c∈b7,a≠b->a≠c->b≠c->(∃i∈({0,1,2,5}:S0),aQ i a=true/\aQ i b=true)\/(∃i∈({0,1,2,5}:S0),aQ i a=true/\aQ i c=true)\/(∃i∈({0,1,2,5}:S0),aQ i b=true/\aQ i c=true):=aa
def gF (l1 l2 i j1 j2 z1 z2 q:F0):Bool:=
 decide (l1≠l2/\i≠j1/\i≠j2/\j1≠j2) &&
 aQ i l1 && aQ j1 l1 && aQ l1 z1 &&
 decide (z1≠i/\z1≠j1/\z1≠j2) &&
 aQ i l2 && aQ j2 l2 && aQ l2 z2 &&
 decide (z2≠i/\z2≠j2/\z2≠j1) &&
 aQ j1 q && decide (q≠l1) && !aQ q l2
lemma lp {l1 l2 i j1 j2 z1 z2 q:F0}(h:gF l1 l2 i j1 j2 z1 z2 q=true):l1≠l2/\i≠j1/\i≠j2/\j1≠j2/\aH i l1/\aH j1 l1/\aH l1 z1/\z1≠i/\z1≠j1/\z1≠j2/\aH i l2/\aH j2 l2/\aH l2 z2/\z2≠i/\z2≠j2/\z2≠j1/\aH j1 q/\q≠l1/\¬aH q l2:=by
 simp only[gF,bA,Bool.not_eq_true',dT,and_assoc] at h;rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,k,a0,a3,r,a2,p,a4,a1,l,m⟩
 exact ⟨h1,h2,h3,h4,(aK _ _).1 h5,(aK _ _).1 h6,(aK _ _).1 h7,h8,h9,k,(aK _ _).1 a0,(aK _ _).1 a3,(aK _ _).1 r,a2,p,a4,(aK _ _).1 a1,l,bw.1 m⟩
def lC (l1 l2:F0):F0×F0×F0×F0×F0×F0:=
 match l1.val,l2.val with
 | 7,8=>(0,1,2,3,6,9)
 | 7,9=>(1,0,5,3,6,8)
 | 7,10=>(0,1,5,3,4,9)
 | 7,13=>(1,0,2,3,4,8)
 | 8,7=>(0,2,1,6,3,12)
 | 8,10=>(0,2,5,6,4,12)
 | 8,12=>(2,0,5,6,3,10)
 | 8,13=>(2,0,1,6,4,10)
 | 9,7=>(1,5,0,6,3,10)
 | 9,10=>(5,1,0,6,4,13)
 | 9,12=>(5,1,2,6,3,13)
 | 9,13=>(1,5,2,6,4,10)
 | 10,7=>(0,5,1,4,3,9)
 | 10,8=>(0,5,2,4,6,9)
 | 10,9=>(5,0,1,4,6,8)
 | 10,12=>(5,0,2,4,3,8)
 | 12,8=>(2,5,0,3,6,9)
 | 12,9=>(5,2,1,3,6,8)
 | 12,10=>(5,2,0,3,4,8)
 | 12,13=>(2,5,1,3,4,9)
 | 13,7=>(1,2,0,4,3,8)
 | 13,8=>(2,1,0,4,6,9)
 | 13,9=>(1,2,5,4,6,8)
 | 13,12=>(2,1,5,4,3,9)
 | _,_=>(0,0,0,0,0,0)
lemma oN:∀l1∈b7,∀l2∈b7,l1≠l2->(∃i∈({0,1,2,5}:S0),aQ i l1=true/\aQ i l2=true)->let w:=lC l1 l2
 w.1∈({0,1,2,5}:S0)/\w.2.1∈({0,1,2,5}:S0)/\
 w.2.2.1∈({0,1,2,5}:S0)/\
 gF l1 l2 w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2=true:=aa
lemma kF:∀l∈({7,8,13}:S0),l∉({0,1,2,11}:S0)/\∃i∈({0,1,2}:S0),∃j∈({0,1,2}:S0),∃z:F0,i≠j/\aH i l/\aH j l/\aH l z/\z≠i/\z≠j:=aa
def il (l:F0):S0:=
 if l=7 then {8,10,9,13} else if l=8 then {7,10,12,13} else {7,9,8,12}
lemma no:∀l∈({7,8,13}:S0),(il l).card=4/\∃p1∈({0,1,2}:S0),∃p2∈({0,1,2}:S0),∃zn:F0,zn∉({0,1,2,11}:S0)/\aH l zn/\zn∉il l/\∀x∈il l,x∉({0,1,2,11}:S0)/\x≠l/\((aH p1 x/\aH p1 l)\/(aH p2 x/\aH p2 l)):=aa
lemma pj:∀l∈({7,8,13}:S0),∀i0∈({0,1,2}:S0),¬aH l i0->∃j1∈({0,1,2}:S0),∃j2∈({0,1,2}:S0),j1≠j2/\aH l j1/\aH l j2/\∃l'∈({7,8,13}:S0),aH l' i0/\aH l' j1/\∃z',aH l' z'/\z'≠i0/\z'≠j1:=aa
lemma o7:∀l1∈({7,8,13}:S0),∀l2∈({7,8,13}:S0),l1≠l2->let w:=lC l1 l2
 w.1∈({0,1,2}:S0)/\w.2.1∈({0,1,2}:S0)/\
 w.2.2.1∈({0,1,2}:S0)/\
 gF l1 l2 w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2=true:=aa
lemma e9:∀i∈({0,1}:S0),i∈({0,1,11}:S0)/\aH 7 i/\aH i 7/\i≠3:=aa
lemma lH:∀x∈({4,5}:S0),x∉({0,1,11}:S0)/\x≠7:=aa
lemma o6:∀a∈({0,1,11}:S0),∀c∈({0,1,11}:S0),a≠c->aH a 7\/aH c 7:=aa
lemma pF:∀i∈({0,1}:S0),∃j1∈({0,1,11}:S0),∃j2∈({0,1,11}:S0),j1≠j2/\j1≠i/\j2≠i:=aa
lemma kU:∀a∈bM,aH a 7\/aH a 3:=aa
lemma lZ:∀i∈bM,∃k1∈bM,∃k2∈bM,k1≠k2/\k1≠i/\k2≠i:=aa
lemma dy:∀i∈({0,1}:S0),i∈bM/\aH i 7/\aQ i 7=true/\(3:F0)≠i/\¬aH i 3/\(11:F0)≠i/\i≠11/\∃i2∈({0,1}:S0),i2≠i:=aa
lemma gn:∀j∈({11,12}:S0),j∈bM/\aH 3 j/\aQ j 3=true/\(7:F0)≠j:=aa
lemma gk:∀l∈({10,13}:S0),l∉bM/\l≠3/\l≠7/\(7:F0)∉({4,6,2,5,l}:S0):=aa
lemma nK:∀x∈({3,6,2,5}:S0),x∉bM/\x≠4/\x≠7/\(aH 11 x\/aH 12 x):=aa
lemma oa {D:aJ}(h:a9 14 D)(m:be D)(p:bH 14 D≤14)(a0:1≤bu 14 D)(k:aN 14 D={0,1,2}):False:=by
 have h1:=db 14 D;rw[k,show ({0,1,2}:S0).card=3 from rfl] at h1;have r:=dn 14 D;by_cases l:bu 14 D=1
 ·have:=iA h m Y (by decide +kernel:dU {7,8,13} {0,1,2}=true)
   (λi hi=>by rw[k];exact hi)
  omega
 ·have:=gH h m (λi hi=>by rw[k];exact hi);omega
lemma mZ {D:aJ}(h:a9 14 D)(hD:be D)(hq:bH 14 D≤14)(hr:1≤bu 14 D)(hI:aN 14 D={0,1,3}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨b,ea⟩:=dB hG h.1 hC;have hb:=cX ea;obtain ⟨p,c0⟩:=cR hG h hC;have m:ch 14 HG D p:=c0;obtain ⟨g1,-,g3,g4,g5⟩:=jn hI;have a0:∀x:F0,x∉aN 14 D->x∈aW 14 D:=λx hx=>ai.1 (mt cl.2 hx);have ca:(7:F0)∈aW 14 D:=a0 7 (by rw[hI];decide);have hY:∀i∈aN 14 D,p i∈aG 14 D 7:=λi hi=>bd m hi ((aK _ _).1 (g1 i hi));have a4:dP D p⊆aG 14 D 7:=λe r=>by
  obtain ⟨i,hi,rfl⟩:=mM.1 r;exact hY i hi
 have c5:(dP D p).card=3:=(cJ (λ_ hi _ hj=>m.2 _ hi _ hj)).trans g5;have fc:=cL a4;rw[c5] at fc;have hg:=fx h hD b hb ca;have hn:=dd h.1 b hb;have hp:=db 14 D;rw[g5] at hp;have ho:=dn 14 D;have g0:(ru D b 7).card≤(aR 14 D b).card:=cF _ _;by_cases h2:2≤(ru D b 7).card
 ·have d2:∀u∈aR 14 D b,(7:F0)∈O 14 D u.1:=by
   have e1:ru D b 7=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← e1] at hu;exact (bb.1 hu).2
  have:=jO h hD b hb kR ca d6 (λx hx=>by
   obtain ⟨fi,fz,⟨i,hi,f3⟩,-⟩:=g3 x hx
   exact ⟨a0 x fi,fz,λu hu _=>d2 u hu,W D (p i),(m.1 i hi).2.2.1 x ((aK _ _).1 f3),(m.1 i hi).2.2.1 7 ((aK _ _).1 (g1 i hi))⟩)
  rw[show d6.card=6 from rfl] at this;omega
 ·obtain ⟨u1,c7⟩:=ac.1 (show (ru D b 7).card=1 by omega);have d0:u1∈ru D b 7:=by rw[c7];exact mX _
  obtain ⟨a7,c1⟩:=bb.1 d0;have b8:dP D p=aG 14 D 7:=eS a4 (by rw[c5];omega);have a6:∀t,t∈O 14 D u1.1->t=7:=by
   intro t ht;by_contra a8
   obtain ⟨e0,et⟩:=ek hG h hC b hb (nS a8) ca (λu hu hu7=>by
    have hm:u∈ru D b 7:=bb.2 ⟨hu,hu7⟩;rw[c7,mS] at hm
    exact hm▸ht) ⟨c1,ht⟩
   have g7:∃i3∈aN 14 D,∀i∈aN 14 D,i≠i3->t∈O 14 D (W D (p i)):=by
    by_cases hc:∃i3∈aN 14 D,p i3=e0
    ·obtain ⟨i3,b0,r⟩:=hc
     exact ⟨i3,b0,λi hi bm=>et _ (hY i hi) (λhh=>
      bm (m.2 i hi i3 b0 (hh.trans r.symm)))⟩
    ·exact ⟨0,by rw[hI];decide,λi hi _=>et _ (hY i hi) (λhh=>hc ⟨i,hi,hh⟩)⟩
   obtain ⟨i3,b0,c2⟩:=g7;obtain ⟨q,g2,fl,f0⟩:=g4 t (λhc=>cl.1 hc (eQ a7 ht)) a8 i3 b0;obtain ⟨e,r,h1,ec⟩:=bB h hD (nS a8) (nS fl)
    (λhadj=>bw.1 f0 (bh hadj))
   rw[← b8] at r;obtain ⟨i,hi,rfl⟩:=mM.1 r;by_cases eu:i=i3
   ·subst eu;exact ec ((m.1 i hi).2.2.1 q ((aK _ _).1 g2))
   ·exact h1 (c2 i hi eu)
  by_cases e7:(aR 14 D b).card=1
  ·have b6:∀x:F0,x≠7->(aG 14 D x).card≤2:=by
    intro x hx;have h1:=ci h hD b hb x
    have r:ru D b x=∅:=eF.2 (λu hu=>by
     obtain ⟨ev,f1⟩:=bb.1 hu;have:=cQ.1 e7.le u ev u1 a7
     exact hx (a6 x (this▸f1)))
    rw[r,ad] at h1;omega
   have b1:∀l∈d6,gx D l:=λl hl=>by
    obtain ⟨-,a2,-,z,hz,cb⟩:=g3 l hl;refine ku h hD hI m a2 ((aK _ _).1 hz) (a0 z cb) (λhdb=>?_);obtain ⟨F,G,hF,f2,ez,e5,g9⟩:=hdb;obtain ⟨-,-,⟨i,hi,e3⟩,-⟩:=g3 l hl;have c8:p i∈dP D p:=aj p hi;have h3:=eq (bd m hi ((aK _ _).1 e3)) hF f2
     (λr=>e5 (r▸c8)) (λr=>g9 (r▸c8)) ez
    have:=b6 l a2;omega
   obtain ⟨Q9,hf,eb,b5⟩:=b1 9 o;obtain ⟨Q12,ct,-,a3⟩:=b1 12 o;have bm:Q9≠Q12:=λr=>absurd (eb 12 (r▸ct)) o
   have g8:({Q9,Q12}:Finset (A0))=aG 14 D 5:=eS (λe r=>by
     rcases mI.1 r with rfl|r
     ·exact b5 5 o (a0 5 (by rw[hI];decide))
     ·rw[mS.1 r];exact a3 5 o (a0 5 (by rw[hI];decide)))
     (by rw[cP bm];exact b6 5 o)
   obtain ⟨e,r,ha,c6⟩:=bB h hD (x:=5) (a:=6) (b:=2)
    o o o
   rw[← g8] at r;rcases mI.1 r with rfl|r
   ·exact ha (aP.1 (b5 6 o (a0 6 (by rw[hI];decide)))).2.1
   ·rw[mS.1 r] at c6;exact c6 (aP.1 (a3 2 o (a0 2 (by rw[hI];decide)))).2.1
  ·have d1:((aR 14 D b).erase u1).card=1:=by
    rw[cE a7];omega
   obtain ⟨u2,er⟩:=cO.1 (d1▸Nat.one_pos);have ej:=mO er
   have b2:∀x:F0,x≠7->∀u∈ru D b x,u=u2:=λx hx u hu=>
    cQ.1 d1.le u
     (mE.2 ⟨λr=>hx (a6 x (r▸(bb.1 hu).2)),(bb.1 hu).1⟩) u2 er
   have es:jz D b u2:=by
    intro x hx;have h1:=ci h hD b hb x;have ec:(ru D b x).card≤1:=cQ.2
     (λu hu v hv=>(b2 x hx u hu).trans (b2 x hx v hv).symm)
    refine ⟨Y,λh3=>?_⟩;obtain ⟨u,hu⟩:=cO.1 (show 0<(ru D b x).card by omega);exact ⟨cZ.1 Y,b2 x hx u hu▸(bb.1 hu).2,λv hv hxv=>b2 x hx v (bb.2 ⟨hv,hxv⟩)⟩
   have hO:∀l∈d6,¬fU D p l->gx D l:=λl hl hnd=>by
    obtain ⟨-,a2,-,z,hz,cb⟩:=g3 l hl;exact ku h hD hI m a2 ((aK _ _).1 hz) (a0 z cb) hnd
   have a1:∃i0∈aN 14 D,∀l∈d6,aQ i0 l=false->gx D l:=by
    by_cases hd:∃l0∈d6,fU D p l0
    ·obtain ⟨l0,g6,gs⟩:=hd;obtain ⟨e2,a2,⟨i0,a1,a5⟩,-⟩:=g3 l0 g6;refine ⟨i0,a1,λl hl hnl=>hO l hl (λhdl=>?_)⟩;obtain ⟨e4,a8,⟨j,hj,c3⟩,-⟩:=g3 l hl;have bm:l0≠l:=λr=>by rw[r,hnl] at a5;exact bF a5
     rw[pg h hD hI b hb m es a2 a8 bm e4 (a0 l0 e2) a1 hj ((aK _ _).1 a5) ((aK _ _).1 c3) gs hdl,c3] at hnl;exact Bool.noConfusion hnl
    ·exact ⟨0,by rw[hI];decide,λl hl _=>hO l hl (λhdl=>hd ⟨l,hl,hdl⟩)⟩
   obtain ⟨i0,a1,b1⟩:=a1
   have fin:∀zl ll:List (F0),kv zl ll->(∀k:Fin 4,cp ll k∈d6/\aQ i0 (cp ll k)=false)->False:=λzl ll hcg hk=>
     o2 h hD hI b ea ej es zl ll hcg (λk=>b1 _ (hk k).1 (hk k).2)
   rw[hI] at a1;simp only[mI,mS] at a1;rcases a1 with rfl|rfl|rfl
   ·exact fin [5,6,4,2] [9,11,13,12] aa aa
   ·exact fin [2,6,4,5] [8,11,10,12] aa aa
   ·exact fin [2,6,5,4] [8,9,10,13] aa aa
lemma jc {D:aJ}(h:a9 14 D)(hD:be D)(hB:br 14 D=(aW 14 D).card+1){l1 l2 a b c d e:F0}(hI:∀x∈({a,b,c,d,e}:S0),x∈aN 14 D)(hg:a≠b/\a≠c/\b≠c/\d≠e/\d≠a/\e≠a/\d≠b/\d≠c/\e≠b/\e≠c/\aH a l1/\aH b l1/\aH c l1/\aH a l2/\aH d l2/\aH e l2):False:=by
 classical
 have hG:=bn;have hC:=bl hD;obtain ⟨bm,b0⟩:=dB hG h.1 hC;have hb:=cX b0;obtain ⟨a8,l⟩:=cR hG h hC;have ct:=dd h.1 bm hb;have b1:∀x,(aG 14 D x).card≤3:=λx=>by
  have:=ci h hD bm hb x
  have:(ru D bm x).card≤(aR 14 D bm).card:=cF _ _
  omega
 obtain ⟨ha,p,m,hd,a0⟩ :
   a∈aN 14 D/\b∈aN 14 D/\c∈aN 14 D/\
   d∈aN 14 D/\e∈aN 14 D:=
  ⟨hI a ab,hI b ab,hI c ab,hI d ab,hI e ab⟩
 obtain ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,b2,a1,a2,a3,a4,a5,a6⟩:=hg;have k:∀u v:F0,u∈aN 14 D->v∈aN 14 D->u≠v->a8 u≠a8 v:=λu v hu hv huv hpe=>huv (l.2 u hu v hv hpe);have b5:3≤(aG 14 D l1).card:=eq (bd l ha a1) (bd l p a2) (bd l m a3)
   (k a b ha p g1) (k a c ha m g2) (k b c p m g3)
 have cb:3≤(aG 14 D l2).card:=eq (bd l ha a4) (bd l hd a5) (bd l a0 a6)
   (k a d ha hd g5.symm) (k a e ha a0 g6.symm) (k d e hd a0 g4)
 obtain ⟨P,Q,b8,a7⟩:=fw hG h hC bm b0 Y {l1,l2}
  ⟨l1,ab⟩ (λx hx=>by
   rcases mI.1 hx with rfl|hx
   ·exact b5
   ·rw[mS.1 hx];exact cb)
 have h1:=ft (bd l ha a1) (bd l p a2) (bd l m a3)
  (k a b ha p g1) (k a c ha m g2) (k b c p m g3) (b1 l1)
 have h2:=ft (bd l ha a4) (bd l hd a5) (bd l a0 a6)
  (k a d ha hd g5.symm) (k a e ha a0 g6.symm) (k d e hd a0 g4) (b1 l2)
 have b6:P=a8 a:=by
  rcases h1 P (a7 l1 ab).1 with rfl|rfl|rfl
  ·rfl
  ·rcases h2 _ (a7 l2 ab).1 with r|r|r
   ·exact absurd r (k b a p ha g1.symm)
   ·exact absurd r (k b d p hd g7.symm)
   ·exact absurd r (k b e p a0 g9.symm)
  ·rcases h2 _ (a7 l2 ab).1 with r|r|r
   ·exact absurd r (k c a m ha g2.symm)
   ·exact absurd r (k c d m hd g8.symm)
   ·exact absurd r (k c e m a0 b2.symm)
 have ca:Q=a8 a:=by
  rcases h1 Q (a7 l1 ab).2 with rfl|rfl|rfl
  ·rfl
  ·rcases h2 _ (a7 l2 ab).2 with r|r|r
   ·exact absurd r (k b a p ha g1.symm)
   ·exact absurd r (k b d p hd g7.symm)
   ·exact absurd r (k b e p a0 g9.symm)
  ·rcases h2 _ (a7 l2 ab).2 with r|r|r
   ·exact absurd r (k c a m ha g2.symm)
   ·exact absurd r (k c d m hd g8.symm)
   ·exact absurd r (k c e m a0 b2.symm)
 exact b8 (by rw[b6,ca])
lemma jo {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(eb:bH 14 D≤14)(et:1≤bu 14 D)(q:Nat)(hq:q=5\/q=6\/q=7)(hI:∀i:F0,i∈aN 14 D<->i.val<q):False:=by
 classical
 obtain ⟨b,hb⟩:=dY h hD;have b1:bX 0⊆aW 14 D:=by
  intro a ha;by_contra c7;have:=(hI a).1 (cl.2 c7);simp only[bX,mF,mV,ae] at ha;have h7:¬a.val<7:=by simpa using ha
  omega
 let Oc:=univ.filter (λk:Fin 7=>bq 14 D (bX 0) (aX (cs k)))
 let Mi:=univ.filter
  (λk:Fin 7=>¬bq 14 D (bX 0) (aX (cs k)))
 let Iq:=univ.filter (λk:Fin 7=>k.val<q)
 have a0:∀k∈Iq,cs k∈aN 14 D:=λk l=>(hI _).2 (mF.1 l).2;have b5:=kV h hD (bX 0) (Subset.refl _) b1 (Oc.image cs)
  (Mi.image cs) (Iq.image cs)
  (λi r=>by
   obtain ⟨k,l,rfl⟩:=mM.1 r
   exact ⟨eE k,(mF.1 l).2⟩)
  (λc hc=>by
   obtain ⟨k,l,rfl⟩:=mM.1 hc;refine ⟨λhc'=>?_,oR ⟨eE k,(mF.1 l).2⟩⟩;obtain ⟨k',p,a1⟩:=mM.1 hc';rw[dX a1] at p
   exact (mF.1 l).2 (mF.1 p).2)
  (λi r=>by
   obtain ⟨k,l,rfl⟩:=mM.1 r
   exact ⟨a0 k l,eE k⟩)
 have a6:=iK h hD (bX 0) (eg 0) ((Mi∩Iq).image cs)
  (λi r=>by
   obtain ⟨k,l,rfl⟩:=mM.1 r;rw[mN] at l
   exact ⟨a0 k l.2,eE k,(mF.1 l.1).2⟩)
 rw[af _ dX] at a6;rw[af _ dX,af _ dX] at b5;have ct:Oc.card+Mi.card=7:=by
  have:=ag (s:=(univ:Finset (Fin 7)))
   (λk:Fin 7=>bq 14 D (bX 0) (aX (cs k)))
  simpa using this
 have a3:Iq.card=q:=by rcases hq with rfl|rfl|rfl<;>rfl
 have d2:Mi.card≤(Mi∩Iq).card+(7-q):=(by have h1:=cD Mi Iq;have h2:(Mi \ Iq).card≤(univ \ Iq).card:=cL (sdiff_subset_sdiff (subset_univ _) (Subset.refl _));rw[card_univ_sdiff,a3,Fintype.card_fin] at h2;omega);have er:(bX 0).card=7:=o;have es:=db 14 D;have d1:(aN 14 D).card=q:=by
  have:aN 14 D=Iq.image cs:=by
   ext i;rw[hI,mM];constructor
   ·intro r
    have:i.val<7:=Y
    exact ⟨⟨i.val,this⟩,mF.2 ⟨mV _,r⟩,rfl⟩
   ·rintro ⟨k,l,rfl⟩;exact (mF.1 l).2
  rw[this,af _ dX,a3]
 have h2:=iD h.1 b hb;have h4:=dn 14 D;obtain ⟨u1,u2,u3,u4,u5⟩:=pu Mi;by_cases c5:br 14 D=(aW 14 D).card
 ·exact kS h hD c5 ((hI 0).2 Y)
 ·by_cases a7:br 14 D=(aW 14 D).card+1
  ·rcases hq with rfl|rfl|rfl
   ·exact jc h hD a7 (l1:=7) (l2:=13) (a:=1) (b:=0) (c:=3)
     (d:=2) (e:=4) (λx hx=>(hI x).2 (by revert x hx;decide))
     ⟨o,o,o,o,o,o,o,o,o,o,(aK 1 7).1 rfl,(aK 0 7).1 rfl,(aK 3 7).1 rfl,(aK 1 13).1 rfl,(aK 2 13).1 rfl,(aK 4 13).1 rfl⟩
   ·exact jc h hD a7 (l1:=7) (l2:=10) (a:=0) (b:=1) (c:=3)
     (d:=4) (e:=5) (λx hx=>(hI x).2 (by revert x hx;decide))
     ⟨o,o,o,o,o,o,o,o,o,o,(aK 0 7).1 rfl,(aK 1 7).1 rfl,(aK 3 7).1 rfl,(aK 0 10).1 rfl,(aK 4 10).1 rfl,(aK 5 10).1 rfl⟩
   ·exact jc h hD a7 (l1:=7) (l2:=10) (a:=0) (b:=1) (c:=3)
     (d:=4) (e:=5) (λx hx=>(hI x).2 (by revert x hx;decide))
     ⟨o,o,o,o,o,o,o,o,o,o,(aK 0 7).1 rfl,(aK 1 7).1 rfl,(aK 3 7).1 rfl,(aK 0 10).1 rfl,(aK 4 10).1 rfl,(aK 5 10).1 rfl⟩
  ·have m:(Mi∩Iq).card=bu 14 D->2≤(Iq \ Mi).card->False:=by
    intro c0 c8;have b6:=ld h hD (bX 0) (eg 0) (Iq.image cs)
     ((Mi∩Iq).image cs) (image_subset_image iR)
     (by rw[cJ dX.injOn,c0])
     (λi r=>by obtain ⟨k,l,rfl⟩:=mM.1 r;exact ⟨a0 k l,eE k⟩)
     (λi r=>by
      obtain ⟨k,l,rfl⟩:=mM.1 r
      exact (mF.1 (mN.1 l).1).2)
    obtain ⟨k1,ca,k2,b2,bm⟩:=oC.1 (by omega:1<(Iq \ Mi).card);have a2:∀k∈Iq \ Mi,cs k∈Iq.image cs \ (Mi∩Iq).image cs:=λk l=>by
     rw[mD] at l ⊢;refine ⟨aj _ l.1,λhm=>?_⟩;obtain ⟨k',p,a1⟩:=mM.1 hm;rw[dX a1] at p;exact l.2 (mN.1 p).1
    obtain ⟨s,cb,c1,ea,-⟩:=dj h hD hT (λhe=>bm (dX he))
     (a0 k1 (mD.1 ca).1) (a0 k2 (mD.1 b2).1)
     (b6 _ (a2 k1 ca)) (b6 _ (a2 k2 b2))
    have b0:3≤(O 14 D (W D (aM D,s))∩bX 0).card:=(by have b8:aX (cs k1)⊆O 14 D (W D (aM D,s))∩bX 0:=λa ha=>mN.2 ⟨c1 a (ce.1 ha),eE k1 ha⟩;have:=cL b8;have d0:(aX (cs k1)).card=3:=dH _;omega);have a5:=lY h hD hT (bX 0) (Subset.refl _) b1
     (Oc.image cs) (Mi.image cs) (Iq.image cs)
     (λi r=>by
      obtain ⟨k,l,rfl⟩:=mM.1 r
      exact ⟨eE k,(mF.1 l).2⟩)
     (λc hc=>by
      obtain ⟨k,l,rfl⟩:=mM.1 hc;refine ⟨λhc'=>?_,oR ⟨eE k,(mF.1 l).2⟩⟩;obtain ⟨k',p,a1⟩:=mM.1 hc';rw[dX a1] at p
      exact (mF.1 l).2 (mF.1 p).2)
     (λi r=>by
      obtain ⟨k,l,rfl⟩:=mM.1 r
      exact ⟨a0 k l,eE k⟩) cb b0
    rw[af _ dX,af _ dX] at a5;have a8:=cD Iq Mi;rw[inter_comm] at a8
    have:Mi.card=4\/Mi.card=5:=Y
    rcases this with a4|ej
    ·have:=u4 a4;omega
    ·have:=u5 Y;omega
   have a8:=cD Iq Mi;rw[inter_comm] at a8;by_cases ec:Mi.card=0
   ·omega
   ·by_cases c2:Mi.card=1
    ·have:=u1 c2;omega
    ·by_cases c3:Mi.card=2
     ·have:=u2 c3;omega
     ·by_cases c6:Mi.card=3
      ·have:=u3 c6;omega
      ·by_cases a4:Mi.card=4
       ·have:=u4 a4;rcases hq with rfl|rfl|rfl
        ·exact m Y Y
        ·omega
        ·omega
       ·have:=u5 Y;rcases hq with rfl|rfl|rfl
        ·exact m Y Y
        ·omega
        ·omega
lemma oE {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(c0:bH 14 D≤14)(c1:1≤bu 14 D)(hI:aN 14 D={0,1,2,5,11}):False:=by
 classical
 have b6:=db 14 D;rw[hI,show ({0,1,2,5,11}:S0).card=5 from rfl] at b6;have k:∀i∈({0,1,2,5}:S0),i∈aN 14 D:=by rw[hI];decide
 have b8:=oM h hD k;have a1:b7⊆bX 0:=o
 have a5:b7⊆aW 14 D:=(by intro a r;by_contra ca;have h1:=cl.2 ca;rw[hI] at h1;exact n6 a r h1)
 let Oc:=({0,1,2,5}:S0).filter (λi=>bq 14 D b7 (aX i))
 let Mc:=({0,1,2,5}:S0).filter (λi=>¬bq 14 D b7 (aX i))
 have a6:=kV h hD b7 a1 a5 Oc {3,4,6} {0,1,2,5}
  (λi hi=>⟨fp i (mF.1 hi).1,(mF.1 hi).2⟩)
  (λc hc=>⟨λhc'=>(iG c hc).1 (mF.1 hc').1,oL (iG c hc).2⟩)
  (λi hi=>⟨k i hi,fp i hi⟩)
 have b5:=iK h hD b7
  (λa r b hb=>eg 0 a (a1 r) b (a1 hb)) Mc
  (λi hi=>⟨k i (mF.1 hi).1,fp i (mF.1 hi).1,(mF.1 hi).2⟩)
 have bm:Oc.card+Mc.card=4:=ag (s:=({0,1,2,5}:S0))
   (λi=>bq 14 D b7 (aX i))
 rw[kW,show ({0,1,2,5}:S0).card=4 from rfl,show b7.card=6 from rfl] at a6;have h4:=dn 14 D;have l:=ld h hD b7 (λa r b hb=>eg 0 a (a1 r) b (a1 hb))
  {0,1,2,5} Mc (fS _ _) Y
  (λi hi=>⟨k i hi,fp i hi⟩) (λi hi=>(mF.1 hi).2)
 have a2:({0,1,2,5}:S0) \ Mc=Oc:=(by ext x;simp only[mD,mF,Mc,Oc];tauto);rw[a2] at l;by_cases cb:bu 14 D=1
 ·obtain ⟨i1,m,i2,p,a0⟩:=oC.1 (by omega:1<Oc.card);obtain ⟨s,a8,b0,-,-⟩:=dj h hD hT a0
   (k i1 (mF.1 m).1) (k i2 (mF.1 p).1)
   (l i1 m) (l i2 p)
  have a4:3≤(O 14 D (W D (aM D,s))∩b7).card:=(by have a7:aX i1⊆O 14 D (W D (aM D,s))∩b7:=λa r=>mN.2 ⟨b0 a (ce.1 r),fp i1 (mF.1 m).1 r⟩;have:=cL a7;have ct:(aX i1).card=3:=dH i1;omega);have a3:=lY h hD hT b7 a1 a5 Oc {3,4,6} {0,1,2,5}
   (λi hi=>⟨fp i (mF.1 hi).1,(mF.1 hi).2⟩)
   (λc hc=>⟨λhc'=>(iG c hc).1 (mF.1 hc').1,oL (iG c hc).2⟩)
   (λi hi=>⟨k i hi,fp i hi⟩) a8 a4
  rw[kW,show ({0,1,2,5}:S0).card=4 from rfl,show b7.card=6 from rfl] at a3;omega
 ·obtain ⟨i1,m,i2,p,a0⟩:=oC.1 (by omega:1<Oc.card);have b1:i1∈({0,1,2,5}:S0):=(mF.1 m).1;have b2:i2∈({0,1,2,5}:S0):=(mF.1 p).1;rcases ow i1 b1 i2 b2 a0 with ⟨r,hb⟩|⟨r,hb⟩|⟨r,hb⟩|⟨r,hb⟩
  ·exact fM h hD hT Y eD
    (λi hi=>k i ((by decide:∀x∈({0,1,2}:S0),x∈({0,1,2,5}:S0)) i hi))
    r hb a0 (l i1 m) (l i2 p)
  ·exact fM h hD hT Y nV
    (λi hi=>k i ((by decide:∀x∈({0,1,5}:S0),x∈({0,1,2,5}:S0)) i hi))
    r hb a0 (l i1 m) (l i2 p)
  ·exact fM h hD hT Y ny
    (λi hi=>k i ((by decide:∀x∈({0,2,5}:S0),x∈({0,1,2,5}:S0)) i hi))
    r hb a0 (l i1 m) (l i2 p)
  ·exact fM h hD hT Y mf
    (λi hi=>k i ((by decide:∀x∈({1,2,5}:S0),x∈({0,1,2,5}:S0)) i hi))
    r hb a0 (l i1 m) (l i2 p)
lemma ji {D:aJ}(h:a9 14 D)(hD:be D){b:F0->Nat}(eb:dz 14 D b){m:F0->A0}(p:ch 14 HG D m){u:P0}(hu:u∈aR 14 D b){l1 l2 i j1 j2 z1 z2 q:F0}(hi:i∈aN 14 D)(a2:j1∈aN 14 D)(b0:j2∈aN 14 D)(hg:l1≠l2/\i≠j1/\i≠j2/\j1≠j2/\aH i l1/\aH j1 l1/\aH l1 z1/\z1≠i/\z1≠j1/\z1≠j2/\aH i l2/\aH j2 l2/\aH l2 z2/\z2≠i/\z2≠j2/\z2≠j1/\aH j1 q/\q≠l1/\¬aH q l2)(er:∀v∈aR 14 D b,l1∈O 14 D v.1->v=u)(c3:∀v∈aR 14 D b,l2∈O 14 D v.1->v=u)(f0:l1∈O 14 D u.1)(g1:l2∈O 14 D u.1):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hb:=cX eb;obtain ⟨ea,a3,ej,ec,d0,b1,cb,c8,a8,bm,a4,a6,ca,e5,b6,b5,c7,d2,ev⟩:=hg;have e2:∀l j k z:F0,j∈aN 14 D->k∈aN 14 D->i≠j->aH i l->aH j l->aH l z->z≠i->z≠j->z≠k->(∀v∈aR 14 D b,l∈O 14 D v.1->v=u)->∃F,F∈aG 14 D l/\F≠m i/\F≠m j/\F≠m k/\aG 14 D l={m i,m j,F}/\bi 14 D (ba 14 D {l})=∅:=by
  intro l j k z hj hk e7 fz fi f3 f1 fc fl eu;obtain ⟨F,c5,b8,-⟩:=bp hG h.1 hC f3;have e3:F≠m i:=λr=>f1 (bx p hi (r▸b8));have e1:F≠m j:=λr=>fc (bx p hj (r▸b8));have gs:F≠m k:=λr=>fl (bx p hk (r▸b8));have et:m i≠m j:=λr=>e7 (p.2 i hi j hj r);have a5:({m i,m j,F}:Finset (A0))⊆aG 14 D l:=by
   intro e r;simp only[mI,mS] at r;rcases r with rfl|rfl|rfl
   ·exact bd p hi fz
   ·exact bd p hj fi
   ·exact c5
  have a7:({m i,m j,F}:Finset (A0)).card=3:=(by rw[cI (by simp[et,nS e3]),cP (nS e1)]);have h1:=ci h hD b hb l;have g9:(ru D b l).card≤1:=cQ.2
   (λa ha c hc=>(eu a (bb.1 ha).1 (bb.1 ha).2).trans (eu c (bb.1 hc).1 (bb.1 hc).2).symm)
  have g5:=cL a5;rw[a7] at g5;exact ⟨F,c5,e3,e1,gs,(eS a5 Y).symm,cZ.1 Y⟩
 obtain ⟨F1,hd,e4,g7,c0,c2,g0⟩:=e2 l1 j1 j2 z1 a2 b0 a3 d0 b1 cb c8 a8 bm er;obtain ⟨F2,ez,g6,g8,e0,f2,g2⟩:=e2 l2 j2 j1 z2 b0 a2 ej a4 a6 ca e5 b6 b5 c3
 obtain ⟨P,Q,g3,a1⟩:=kh hG h hC b eb hu {l1,l2} ⟨l1,ab⟩ (λx hx=>by
  rcases mI.1 hx with rfl|hx
  ·exact ⟨g0,f0,er⟩
  ·rw[mS.1 hx];exact ⟨g2,g1,c3⟩)
 have ct:P≠Q:=λr=>g3 (kA Prod.fst r);have a0:∀e,e∈aG 14 D l1->e∈aG 14 D l2->e=m i\/(e=F1/\F1=F2):=by
  intro e c1 b2;rw[c2,mI,mI,mS] at c1;rw[f2,mI,mI,mS] at b2;have d1:m j1≠m j2:=λr=>ec (p.2 j1 a2 j2 b0 r);have es:m j1≠m i:=λr=>a3 (p.2 j1 a2 i hi r).symm;rcases c1 with rfl|rfl|rfl
  ·exact oL rfl
  ·rcases b2 with hh|hh|hh
   ·exact absurd hh es
   ·exact absurd hh d1
   ·exact absurd hh.symm e0
  ·rcases b2 with hh|hh|hh
   ·exact absurd hh e4
   ·exact absurd hh c0
   ·exact oR ⟨rfl,hh⟩
 have g4:F1=F2:=by
  rcases a0 P (a1 l1 ab).1 (a1 l2 ab).1 with hP|⟨-,hF⟩
  ·rcases a0 Q (a1 l1 ab).2 (a1 l2 ab).2 with hQ|⟨-,hF⟩
   ·exact absurd (hP.trans hQ.symm) ct
   ·exact hF
  ·exact hF
 obtain ⟨e,r,ha,c6⟩:=bB h hD (x:=l1) (a:=q) (b:=l2) (nS d2) ea ev;rw[c2,mI,mI,mS] at r;rcases r with rfl|rfl|rfl
 ·exact c6 ((p.1 i hi).2.2.1 l2 a4)
 ·exact ha ((p.1 j1 a2).2.2.1 q c7)
 ·exact c6 (g4▸(aP.1 ez).2.1)
lemma iW {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(hw:bu 14 D=1)(hs:br 14 D=13)(hr:(aW 14 D).card=10)(l:({0,1,2}:S0)⊆aN 14 D):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,hb⟩:=dY h hD;obtain ⟨r,m⟩:=cR hG h hC;have i0:(0:F0)∈aN 14 D:=l o;have i1:(1:F0)∈aN 14 D:=l o;have i2:(2:F0)∈aN 14 D:=l o;have hB:br 14 D≤(aW 14 D).card+3:=Y
 have a4:∀a c:F0,a∈({0,1,2}:S0)->c∈({0,1,2}:S0)->a≠c->aU 14 D a.val (aO 14 D)->aU 14 D c.val (aO 14 D)->False:=λa c ha hc hac hca ej=>
   fM h hD hT hB eD (λi hi=>l hi) ha hc hac hca ej
 have a0:∀i∈({0,1,2}:S0),aU 14 D i.val (aO 14 D)\/∃z,aU 14 D i.val z/\2≤aS D z/\O 14 D z=∅:=λi hi=>cr hG h hC (l hi);have g5:∃z,2≤aS D z/\O 14 D z=∅/\∀i∈({0,1,2}:S0),aU 14 D i.val (aO 14 D)\/(aU 14 D i.val z/\∃j∈({0,1,2}:S0),j≠i/\aU 14 D j.val z):=by
  have a1:∀z1 z2,2≤aS D z1->O 14 D z1=∅->2≤aS D z2->O 14 D z2=∅->z1=z2:=λz1 z2 f1 e1 f2 e2=>ex hS Y f1 e1 f2 e2;rcases a0 0 o with c0|⟨z0,b0,bm,a8⟩<;>
   rcases a0 1 o with c1|⟨z1,b1,ca,b8⟩<;>
   rcases a0 2 o with c2|⟨z2,a6,d1,ea⟩
  ·exact (a4 0 1 o o o c0 c1).elim
  ·exact (a4 0 1 o o o c0 c1).elim
  ·exact (a4 0 2 o o o c0 c2).elim
  ·have hg:=a1 z1 z2 ca b8 d1 ea;subst hg;refine ⟨z1,ca,b8,λi hi=>?_⟩;simp only[mI,mS] at hi;rcases hi with rfl|rfl|rfl
   ·exact oL c0
   ·exact oR ⟨b1,2,o,o,a6⟩
   ·exact oR ⟨a6,1,o,o,b1⟩
  ·exact (a4 1 2 o o o c1 c2).elim
  ·have et:=a1 z0 z2 bm a8 d1 ea;subst et;refine ⟨z0,bm,a8,λi hi=>?_⟩;simp only[mI,mS] at hi;rcases hi with rfl|rfl|rfl
   ·exact oR ⟨b0,2,o,o,a6⟩
   ·exact oL c1
   ·exact oR ⟨a6,0,o,o,b0⟩
  ·have eb:=a1 z0 z1 bm a8 ca b8;subst eb;refine ⟨z0,bm,a8,λi hi=>?_⟩;simp only[mI,mS] at hi;rcases hi with rfl|rfl|rfl
   ·exact oR ⟨b0,1,o,o,b1⟩
   ·exact oR ⟨b1,0,o,o,b0⟩
   ·exact oL c2
  ·have eb:=a1 z0 z1 bm a8 ca b8;subst eb;have et:=a1 z0 z2 bm a8 d1 ea;subst et;refine ⟨z0,bm,a8,λi hi=>?_⟩;simp only[mI,mS] at hi;rcases hi with rfl|rfl|rfl
   ·exact oR ⟨b0,1,o,o,b1⟩
   ·exact oR ⟨b1,0,o,o,b0⟩
   ·exact oR ⟨a6,0,o,o,b0⟩
 obtain ⟨z,fz,ez,a7⟩:=g5;have b5:∀a∈({7,8,13}:S0),∀c∈({7,8,13}:S0),¬aH a c:=aa;have e4:∀i∈({0,1,2}:S0),bq 14 D {7,8,13} (aX i∩{7,8,13}):=by
  intro i hi;rcases a7 i hi with b6|⟨eu,j,hj,d0,hl⟩
  ·obtain ⟨k,s,-,-,-,hq⟩:=fW hG hS hC {7,8,13} b5 b6;refine ⟨W D (k,s),?_⟩;ext a;simp only[mN,ce];exact ⟨λhh=>⟨(hq a hh.2).mp hh.1,hh.2⟩,λhh=>⟨(hq a hh.2).mpr hh.1,hh.2⟩⟩
  ·have hn:∃a∈({7,8,13}:S0),aH j a/\¬aH i a:=oG i hi j hj d0;obtain ⟨k,s,-,-,-,-,hq⟩:=iv hG hS hC {7,8,13} b5 eu
    (c9 hS hl) hn
   refine ⟨W D (k,s),?_⟩;ext a;simp only[mN,ce];exact ⟨λhh=>⟨(hq a hh.2).mp hh.1,hh.2⟩,λhh=>⟨(hq a hh.2).mpr hh.1,hh.2⟩⟩
 obtain ⟨c5,d2⟩:=oV h hD hB b hb eD (λi hi=>l hi) e4;have a5:∀t i j u:F0,t∈({7,8,13}:S0)->i∈({0,1,2}:S0)->j∈({0,1,2}:S0)->i≠j->aH i t->aH j t->aH t u->u≠i->u≠j->∃F,aI F∈aG 14 D u/\aG 14 D t={r i,r j,F}/\(F≠r i/\F≠r j)/\(ru D b t).card=1:=by
  intro t i j u ht hi hj g0 cb g2 g6 ec g7;obtain ⟨hv,hM⟩:=c5 t ht;obtain ⟨F,g3,es,-⟩:=bp hG hS hC g6;have fi:F≠r i:=λhe=>ec (bx m (l hi) (he▸es));have fc:F≠r j:=λhe=>g7 (bx m (l hj) (he▸es));have e7:r i≠r j:=λhe=>g0 (m.2 i (l hi) j (l hj) he);have a2:({r i,r j,F}:Finset (A0))⊆aG 14 D t:=by
   intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
   ·exact bd m (l hi) cb
   ·exact bd m (l hj) g2
   ·exact g3
  have c6:({r i,r j,F}:Finset (A0)).card=3:=(by rw[cI (by simp[e7,nS fi]),cP (nS fc)]);have ev:=eS a2 Y;have g9:t∈aW 14 D:=(ij hG h hC cb).resolve_left (cl.1 (l hi));have ej:=fx h hD b hb g9;rw[hM,← ev,c6,ad] at ej;exact ⟨F,es,ev.symm,⟨fi,fc⟩,Y⟩
 obtain ⟨F7,ho,e0,n7,c7⟩:=a5 7 0 1 3 o o o
  o o o o o o
 obtain ⟨F13,e5,c3,hk,hm⟩:=a5 13 1 2 4 o o o
  o o o o o o
 obtain ⟨F8,g1,e3,n8,c8⟩:=a5 8 2 0 6 o o o
  o o o o o o
 have a3:∀t i j u:F0,∀F:A0,i∈({0,1,2}:S0)->j∈({0,1,2}:S0)->aH i t->j≠i->u≠i->aG 14 D t={r i,r j,F}->aI F∈aG 14 D u->∀a,a∈O 14 D (W D (r i))<->aH i a:=by
  intro t i j u F hi hj cb d0 ec hW hF;refine i6 h hD m (l hi) cb (λp hp hne a2=>?_) ?_
  ·rw[hW,mI,mI,mS] at hp;rcases hp with rfl|rfl|rfl
   ·exact hne rfl
   ·have:j∈O 14 D (W D (aI (r j))):=by
     rw[show W D (aI (r j))=W D ((r j).1,!(r j).2) from rfl,(m.1 j (l hj)).2.2.2];exact mX j
    exact d0 (mS.1 (a2 this))
   ·exact ec (mS.1 (a2 (aP.1 hF).2.1))
  ·rcases a7 i hi with b6|⟨eu,j',hd,fl,f3⟩
   ·exact oL b6
   ·exact oR ⟨j',l hd,fl,z,eu,f3⟩
 have f0:=a3 7 0 1 3 F7 o o o o o e0 ho;have f1:=a3 13 1 2 4 F13 o o o o o c3 e5;have f2:=a3 8 2 0 6 F8 o o o o o e3 g1;have ct:∀y:F0,y∉({7,8,13}:S0)->(aG 14 D y).card≤2:=by
  intro y hy;have he:ru D b y=∅:=by
   rw[eF];intro u hu;obtain ⟨b2,er⟩:=bb.1 hu;rcases nq b2 (d2 u b2) with h7|h8|g8
   ·exact hy (by
     rw[iP h hD m b hb i0 i1 o e0 n7 f0 f1 c7 b2 (bb.1 h7).2 er]
     decide)
   ·exact hy (by
     rw[iP h hD m b hb i2 i0 o e3 n8 f2 f0 c8 b2 (bb.1 h8).2 er]
     decide)
   ·exact hy (by
     rw[iP h hD m b hb i1 i2 o c3 hk f1 f2 hm b2 (bb.1 g8).2 er]
     decide)
  have:=ci h hD b hb y;rw[he,ad] at this;omega
 obtain ⟨Z1,p1,q1,r1⟩:=iI h hD m i0 (s:=10) (d:=5) o (ct 10 o);obtain ⟨Z2,p2,q2,r2⟩:=iI h hD m i1 (s:=9) (d:=5) o (ct 9 o);obtain ⟨Z3,-,q3,r3⟩:=iI h hD m i2 (s:=12) (d:=5) o (ct 12 o)
 have hf:aI Z1≠aI Z2:=λe=>
  p1 9 o (by rw[← aT Z1,e,aT];exact q2)
 have gs:aI Z1≠aI Z3:=λe=>
  p1 12 o (by rw[← aT Z1,e,aT];exact q3)
 have g4:aI Z2≠aI Z3:=λe=>
  p2 12 o (by rw[← aT Z2,e,aT];exact q3)
 have a2:({aI Z1,aI Z2,aI Z3}:Finset (A0))⊆aG 14 D 5:=(by intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl<;>assumption);have:=cL a2;rw[cI (by simp[hf,gs]),cP g4] at this;have:=ct 5 o;omega
lemma on {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(gs:bH 14 D≤14)(g0:1≤bu 14 D)(hI:aN 14 D={0,1,2,3}):False:=by
 classical
 have er:=db 14 D;rw[hI,show ({0,1,2,3}:S0).card=4 from rfl] at er;have a3:({0,1,2}:S0)⊆aN 14 D:=by rw[hI];decide
 have f0:=gH h hD (λi p=>a3 p);have f3:=dn 14 D;by_cases ca:bu 14 D=1
 ·have fc:=iA h hD Y eD (λi p=>a3 p);exact iW h hD hT ca Y Y a3
 ·have hG:=bn;have hC:=bl hD;obtain ⟨b,c1⟩:=dB hG h.1 hC;have hb:=cX c1;obtain ⟨a2,m⟩:=cR hG h hC;have fz:=dd h.1 b hb;have k:∀x∈({0,1,2,3}:S0),x∈aN 14 D:=by rw[hI];exact λ_ hx=>hx
  have a5:∀x:F0,x∉({0,1,2,3}:S0)->x∈aW 14 D:=λx hx=>ai.1 (λhc=>hx (hI▸cl.2 hc));have b0:=a5 7 o;have a1:∀i∈({0,1,3}:S0),a2 i∈aG 14 D 7:=λi p=>bd m (k i (en i p).1) (en i p).2;have f1:3≤(aG 14 D 7).card:=eq (a1 0 o) (a1 1 o) (a1 3 o)
    (λr=>absurd (m.2 0 (k 0 o) 1 (k 1 o) r) o)
    (λr=>absurd (m.2 0 (k 0 o) 3 (k 3 o) r) o)
    (λr=>absurd (m.2 1 (k 1 o) 3 (k 3 o) r) o)
  have fi:=fx h hD b hb b0;have e4:(ru D b 7).card≤(aR 14 D b).card:=cF _ _;by_cases fl:(ru D b 7).card=2
  ·have c0:∀u∈aR 14 D b,(7:F0)∈O 14 D u.1:=by
    have d1:ru D b 7=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← d1] at hu;exact (bb.1 hu).2
   have ez:=jO h hD b hb kR b0 d6 (λx hx=>by
    obtain ⟨eb,e3,i,p,e2,es⟩:=pD x hx
    exact ⟨a5 x eb,e3,λu hu _=>c0 u hu,W D (a2 i),(m.1 i (k i (en i p).1)).2.2.1 x e2,(m.1 i (k i (en i p).1)).2.2.1 7 es⟩)
   rw[show d6.card=6 from rfl] at ez;omega
  ·obtain ⟨u1,b8⟩:=ac.1 (show (ru D b 7).card=1 by omega);have cb:u1∈ru D b 7:=by rw[b8];exact mX _
   obtain ⟨a7,b5⟩:=bb.1 cb;have a8:({0,1,3}:S0).image a2=aG 14 D 7:=by
    refine eS (λe r=>?_) ?_
    ·obtain ⟨i,p,rfl⟩:=mM.1 r;exact a1 i p
    ·rw[cJ (λa ha c hc=>m.2 a (k a (en a ha).1) c (k c (en c hc).1)),show ({0,1,3}:S0).card=3 from rfl];omega
   have b1:∀t,t∈O 14 D u1.1->t=7:=by
    intro t ht;by_contra b2
    obtain ⟨e0,c6⟩:=ek hG h hC b hb (nS b2) b0 (λu hu hu7=>by
     have hm:u∈ru D b 7:=bb.2 ⟨hu,hu7⟩;rw[b8,mS] at hm
     exact hm▸ht) ⟨b5,ht⟩
    have e7:∃i3∈({0,1,3}:S0),∀i∈({0,1,3}:S0),i≠i3->t∈O 14 D (W D (a2 i)):=by
     by_cases hc:∃i3∈({0,1,3}:S0),a2 i3=e0
     ·obtain ⟨i3,a4,r⟩:=hc
      exact ⟨i3,a4,λi p hne=>c6 _ (a1 i p) (λhh=>
       hne (m.2 i (k i (en i p).1) i3 (k i3 (en i3 a4).1) (hh.trans r.symm)))⟩
     ·exact ⟨0,o,λi p _=>c6 _ (a1 i p) (λhh=>hc ⟨i,p,hh⟩)⟩
    obtain ⟨i3,a4,b6⟩:=e7
    have bm:t∉({0,1,3}:S0):=λhc=>
     cl.1 (k t (en t hc).1) (eQ a7 ht)
    obtain ⟨q,e5,eu,ev⟩:=(by decide +kernel:∀t:F0,t∉({0,1,3}:S0)->t≠7->∀i∈({0,1,3}:S0),∃q,aQ i q=true/\q≠7/\aQ q t=false) t bm b2 i3 a4;obtain ⟨e,r,h1,e1⟩:=bB h hD (nS b2) (nS eu)
     (λhadj=>bw.1 ev (bh hadj))
    rw[← a8] at r;obtain ⟨i,p,rfl⟩:=mM.1 r;by_cases c7:i=i3
    ·subst c7;exact e1 ((m.1 i (k i (en i p).1)).2.2.1 q ((aK _ _).1 e5))
    ·exact h1 (b6 i p c7)
   have ct:((aR 14 D b).erase u1).card=1:=(by rw[cE a7];omega);obtain ⟨u2,c3⟩:=cO.1 (ct▸Nat.one_pos);have c2:=mO c3;have a0:∀l:F0,l≠7->∀v∈aR 14 D b,l∈O 14 D v.1->v=u2:=λl hl v hv hlv=>cQ.1 ct.le v
     (mE.2 ⟨λr=>hl (b1 l (r▸hlv)),hv⟩) u2 c3
   have a6:∀l i j z:F0,l≠7->i∈({0,1,2,3}:S0)->j∈({0,1,2,3}:S0)->i≠j->aH i l->aH j l->aH l z->z≠i->z≠j->l∈O 14 D u2.1:=by
    intro l i j z hl p hj c8 ec d2 et ej d0;obtain ⟨F,ea,c5,-⟩:=bp hG h.1 hC et;have h3:=eq (bd m (k i p) ec) (bd m (k j hj) d2) ea
     (λr=>c8 (m.2 i (k i p) j (k j hj) r))
     (λr=>ej (bx m (k i p) (r.symm▸c5)))
     (λr=>d0 (bx m (k j hj) (r.symm▸c5)))
    have f2:=ci h hD b hb l;obtain ⟨v,hv⟩:=cO.1 (show 0<(ru D b l).card by omega);exact a0 l hl v (bb.1 hv).1 (bb.1 hv).2▸(bb.1 hv).2
   exact ji h hD c1 m c2 (l1:=8) (l2:=12) (i:=2) (j1:=0) (j2:=3)
    (z1:=6) (z2:=5) (q:=7) (k 2 o) (k 0 o) (k 3 o)
    mC (a0 8 o) (a0 12 o)
    (a6 8 2 0 6 o o o o ((aK 2 8).1 rfl) ((aK 0 8).1 rfl) ((aK 8 6).1 rfl) o o)
    (a6 12 2 3 5 o o o o ((aK 2 12).1 rfl) ((aK 3 12).1 rfl) ((aK 12 5).1 rfl) o o)
lemma mc {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(f3:bH 14 D≤14)(gs:1≤bu 14 D)(hI:aN 14 D={0,1,2,5}):False:=by
 classical
 have eu:=db 14 D;rw[hI,show ({0,1,2,5}:S0).card=4 from rfl] at eu;have a3:({0,1,2}:S0)⊆aN 14 D:=by rw[hI];decide
 have fz:=gH h hD (λi hi=>a3 hi);have f2:=dn 14 D;by_cases cb:bu 14 D=1
 ·have fc:=iA h hD Y eD (λi hi=>a3 hi);exact iW h hD hT cb Y Y a3
 ·have hG:=bn;have hC:=bl hD;obtain ⟨b,bm⟩:=dB hG h.1 hC;have hb:=cX bm;obtain ⟨f0,k⟩:=cR hG h hC;have fi:=dd h.1 b hb;have m:∀x∈({0,1,2,5}:S0),x∈aN 14 D:=by rw[hI];exact λ_ hx=>hx
  have a0:∀x:F0,x∉({0,1,2,5}:S0)->x∈aW 14 D:=λx hx=>ai.1 (λhc=>hx (hI▸cl.2 hc));have a2:∀l∈b7,1≤(ru D b l).card:=by
   intro l p;obtain ⟨i,hi,j,hj,z,d2,er,ec,e1,et,ea⟩:=oo l p;obtain ⟨F,ej,c5,-⟩:=bp hG h.1 hC e1;have h3:=eq (bd k (m i hi) er) (bd k (m j hj) ec) ej
    (λhe=>d2 (k.2 i (m i hi) j (m j hj) he))
    (λhe=>et (bx k (m i hi) (he.symm▸c5)))
    (λhe=>ea (bx k (m j hj) (he.symm▸c5)))
   have:=ci h hD b hb l;omega
  by_cases h2:∃l∈b7,(ru D b l).card=2
  ·obtain ⟨l,p,fl⟩:=h2;have a4:∀u∈aR 14 D b,l∈O 14 D u.1:=by
    have eb:ru D b l=aR 14 D b:=eS (fS _ _) Y;intro u r;rw[← eb] at r;exact (bb.1 r).2
   obtain ⟨b8,z,e0,ca,b5⟩:=lx l p;have e2:=dl h hD b bm (a0 l b8) (b7.erase l) {z} ∅
    (λx hx=>by
     obtain ⟨d0,c3⟩:=mE.1 hx;obtain ⟨u,r⟩:=cO.1 (show 0<(ru D b x).card by have:=a2 x c3;omega)
     exact ⟨a0 x (lx x c3).1,d0,λv hv _=>a4 v hv,u.1,(bb.1 r).2,a4 u (bb.1 r).1⟩)
    (λn hn=>by
     rw[mS.1 hn]
     exact ⟨a0 z ca,e0,λhm=>b5 (mO hm)⟩)
    (λ_ hz=>(nE _ hz).elim)
   rw[cE p,show b7.card=6 from rfl,cS,ad] at e2;omega
  ·have h1:∀l∈b7,(ru D b l).card=1:=λl p=>by
    have:=a2 l p
    have:(ru D b l).card≤(aR 14 D b).card:=cF _ _
    by_contra g0;exact h2 ⟨l,p,Y⟩
   obtain ⟨u1,b6,u2,c6,e3⟩:=oC.1 (show 1<(aR 14 D b).card by omega)
   have hR:aR 14 D b={u1,u2}:=(eS (λu r=>by
     rcases mI.1 r with rfl|r
     ·exact b6
     ·rw[mS.1 r];exact c6) (by rw[cP e3];omega)).symm
   let L1:=b7.filter (λl=>l∈O 14 D u1.1)
   let L2:=b7.filter (λl=>l∈O 14 D u2.1)
   have a8:b7⊆L1∪L2:=by
    intro l p;obtain ⟨u,r⟩:=cO.1 (show 0<(ru D b l).card by rw[h1 l p];omega);obtain ⟨a1,c1⟩:=bb.1 r;rw[hR,mI,mS] at a1;rcases a1 with rfl|rfl
    ·exact aq _ (mF.2 ⟨p,c1⟩)
    ·exact ar _ (mF.2 ⟨p,c1⟩)
   have h3:∃u∈aR 14 D b,3≤(b7.filter (λl=>l∈O 14 D u.1)).card:=by
    have hc:=cL a8;have r:=ao L1 L2;rw[show b7.card=6 from rfl] at hc;by_cases d1:3≤L1.card
    ·exact ⟨u1,b6,d1⟩
    ·exact ⟨u2,c6,show 3≤L2.card by omega⟩
   obtain ⟨u,a1,f1⟩:=h3
   let Lu:=b7.filter (λl=>l∈O 14 D u.1)
   obtain ⟨a,ha,b',a6,c',a5,c7,ct,c2⟩:=two_lt_card.1 (show 2<Lu.card by dsimp only[Lu];omega);have e4:=(mF.1 ha).1;have e5:=(mF.1 a6).1;have ez:=(mF.1 a5).1;have b0:∃l1∈Lu,∃l2∈Lu,l1≠l2/\∃i∈({0,1,2,5}:S0),aQ i l1=true/\aQ i l2=true:=by
    rcases p5 a e4 b' e5 c' ez c7 ct c2 with h'|h'|h'
    ·exact ⟨a,ha,b',a6,c7,h'⟩
    ·exact ⟨a,ha,c',a5,ct,h'⟩
    ·exact ⟨b',a6,c',a5,c2,h'⟩
   obtain ⟨l1,b2,l2,a7,c0,e7⟩:=b0;obtain ⟨hi,ev,es,b1⟩:=oN l1 (mF.1 b2).1 l2 (mF.1 a7).1 c0 e7
   have c8:∀l∈Lu,∀v∈aR 14 D b,l∈O 14 D v.1->v=u:=λl p v hv hlv=>
    cQ.1 (by rw[h1 l (mF.1 p).1]) v (bb.2 ⟨hv,hlv⟩)
     u (bb.2 ⟨a1,(mF.1 p).2⟩)
   exact ji h hD bm k a1 (m _ hi) (m _ ev) (m _ es) (lp b1)
    (c8 l1 b2) (c8 l2 a7) (mF.1 b2).2 (mF.1 a7).2
lemma nj {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(hB:bH 14 D≤14)(hE:1≤bu 14 D)(hI:aN 14 D={0,1,2,11}):False:=by
 classical
 have ha:=db 14 D;rw[hI,show ({0,1,2,11}:S0).card=4 from rfl] at ha;have k:({0,1,2}:S0)⊆aN 14 D:=by rw[hI];decide
 have hs:=gH h hD (λi hi=>k hi);have hA:=dn 14 D;by_cases eu:bu 14 D=1
 ·have hp:=iA h hD Y eD (λi hi=>k hi);exact iW h hD hT eu Y Y k
 ·have hG:=bn;have hC:=bl hD;obtain ⟨b,d0⟩:=dB hG h.1 hC;have hb:=cX d0;obtain ⟨a2,m⟩:=cR hG h hC;have hr:=dd h.1 b hb;have hy:∀x∈({0,1,2,11}:S0),x∈aN 14 D:=by rw[hI];exact λ_ hx=>hx
  have a6:∀x:F0,x∉({0,1,2,11}:S0)->x∈aW 14 D:=λx hx=>ai.1 (λhc=>hx (hI▸cl.2 hc));have c3:∀l∈({7,8,13}:S0),1≤(ru D b l).card:=by
   intro l hl;obtain ⟨-,i,hi,j,hj,z,g0,g8,g6,hf,g9,g1⟩:=kF l hl;obtain ⟨F,c5,a4,-⟩:=bp hG h.1 hC hf;have h3:=eq (bd m (k hi) g8) (bd m (k hj) g6) c5
    (λhe=>g0 (m.2 i (k hi) j (k hj) he))
    (λhe=>g9 (bx m (k hi) (he.symm▸a4)))
    (λhe=>g1 (bx m (k hj) (he.symm▸a4)))
   have:=ci h hD b hb l;omega
  by_cases h2:∃l∈({7,8,13}:S0),(ru D b l).card=2
  ·by_cases a3:∀i∈({0,1,2}:S0),aU 14 D i.val (aO 14 D)
   ·exact fM h hD hT Y eD (λi hi=>k hi)
     (i1:=0) (i2:=1) o o o
     (a3 0 o) (a3 1 o)
   ·obtain ⟨i0,r,fz⟩:∃i0∈({0,1,2}:S0),¬aU 14 D i0.val (aO 14 D):=by
     by_contra hc;push Not at hc;exact a3 hc
    obtain ⟨z0,bm,cb,c0⟩:∃z,aU 14 D i0.val z/\2≤aS D z/\O 14 D z=∅:=(cr hG h hC (k r)).resolve_left fz;have p:∀l∈({7,8,13}:S0),(ru D b l).card=2->∀i∈({0,1,2}:S0),aH l i->∀z,aU 14 D i.val z->2≤aS D z->O 14 D z=∅->False:=by
     intro l hl b6 i _ hh z e4 g7 g3;have e5:∀u∈aR 14 D b,l∈O 14 D u.1:=(by have g5:ru D b l=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← g5] at hu;exact (bb.1 hu).2);obtain ⟨e3,p1,fi,p2,fc,zn,a0⟩:=no l hl;have hg:=dl h hD b d0 (a6 l (kF l hl).1) (il l) {zn} {z}
      (λx hx=>by
       obtain ⟨f0,gs,hk⟩:=a0.2.2.2 x hx;refine ⟨a6 x f0,gs,λu hu _=>e5 u hu,?_⟩;rcases hk with ⟨h1,h2⟩|⟨h1,h2⟩
       ·exact ⟨W D (a2 p1),(m.1 p1 (k fi)).2.2.1 x h1,(m.1 p1 (k fi)).2.2.1 l h2⟩
       ·exact ⟨W D (a2 p2),(m.1 p2 (k fc)).2.2.1 x h1,(m.1 p2 (k fc)).2.2.1 l h2⟩)
      (λn hn=>by rw[mS.1 hn];exact ⟨a6 zn a0.1,a0.2.1,a0.2.2.1⟩)
      (λw hw=>by rw[mS.1 hw];exact ⟨g7,g3,i,hh,e4⟩)
     rw[e3,cS,cS] at hg;omega
    obtain ⟨l,hl,b6⟩:=h2;by_cases b5:aH l i0
    ·exact p l hl b6 i0 r b5 z0 bm cb c0
    ·obtain ⟨j1,a1,j2,a7,eb,ca,ev,l',hm,ct,b2,z',et,es,ej⟩:=pj l hl i0 r b5;rcases cr hG h hC (k a1) with c1|⟨z1,ho,f1,e1⟩
     ·rcases cr hG h hC (k a7) with c2|⟨z2,hd,f2,e2⟩
      ·obtain ⟨s,b0,g4,-,-⟩:=dj h hD hT eb (k a1) (k a7) c1 c2;obtain ⟨F,c5,a4,-⟩:=bp hG h.1 hC et;have b1:(aM D,s)∈aG 14 D l':=cV hD hT (g4 l' (bh b2));have a5:(aM D,s)≠F:=λhe=>by
        have:=(aP.1 a4).2.1;rw[← he] at this;rw[show W D (aI (aM D,s))=W D (aM D,!s) from rfl,b0] at this;exact nE _ this
       have d2:({a2 i0,a2 j1,F,(aM D,s)}:Finset (A0))⊆aG 14 D l':=by
        intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl|rfl
        ·exact bd m (k r) (bh ct)
        ·exact bd m (k a1) (bh b2)
        ·exact c5
        ·exact b1
       have d1:i0≠j1:=λhe=>b5 (he▸ca);have h4:=cL d2;have b8:a2 i0≠a2 j1:=λhe=>d1 (m.2 i0 (k r) j1 (k a1) he);have c7:a2 i0≠F:=λhe=>es (bx m (k r) (he.symm▸a4));have ea:a2 j1≠F:=λhe=>ej (bx m (k a1) (he.symm▸a4));rw[cI (by simp[b8,c7,(cw m b0 (k r)).symm]),cI (by simp[ea,(cw m b0 (k a1)).symm]),cP a5.symm] at h4;have hz:=ci h hD b hb l';have hq:(ru D b l').card≤(aR 14 D b).card:=cF _ _;exact p l' hm Y i0 r ct z0 bm cb c0
      ·exact p l hl b6 j2 a7 ev z2 hd f2 e2
     ·exact p l hl b6 j1 a1 ca z1 ho f1 e1
  ·have h1:∀l∈({7,8,13}:S0),(ru D b l).card=1:=λl hl=>by
    have:=c3 l hl
    have:(ru D b l).card≤(aR 14 D b).card:=cF _ _
    by_contra hF;exact h2 ⟨l,hl,Y⟩
   obtain ⟨u1,er,u2,fl,eb⟩:=oC.1 (show 1<(aR 14 D b).card by omega)
   have hR:aR 14 D b={u1,u2}:=(eS (λu hu=>by
     rcases mI.1 hu with rfl|hu
     ·exact er
     ·rw[mS.1 hu];exact fl) (by rw[cP eb];omega)).symm
   let L1:=({7,8,13}:S0).filter (λl=>l∈O 14 D u1.1)
   let L2:=({7,8,13}:S0).filter (λl=>l∈O 14 D u2.1)
   have c8:({7,8,13}:S0)⊆L1∪L2:=by
    intro l hl;obtain ⟨u,hu⟩:=cO.1 (show 0<(ru D b l).card by rw[h1 l hl];omega);obtain ⟨a8,e7⟩:=bb.1 hu;rw[hR,mI,mS] at a8;rcases a8 with rfl|rfl
    ·exact aq _ (mF.2 ⟨hl,e7⟩)
    ·exact ar _ (mF.2 ⟨hl,e7⟩)
   have ez:∃u∈aR 14 D b,2≤(({7,8,13}:S0).filter (λl=>l∈O 14 D u.1)).card:=by
    have hc:=cL c8;have hu:=ao L1 L2;rw[show ({7,8,13}:S0).card=3 from rfl] at hc;by_cases g2:2≤L1.card
    ·exact ⟨u1,er,g2⟩
    ·exact ⟨u2,fl,show 2≤L2.card by omega⟩
   obtain ⟨u,a8,ht⟩:=ez
   let Lu:=({7,8,13}:S0).filter (λl=>l∈O 14 D u.1)
   obtain ⟨l1,ec,l2,c6,e0⟩:=oC.1 (show 1<Lu.card by dsimp only[Lu];omega)
   have f3:∀l∈Lu,∀v∈aR 14 D b,l∈O 14 D v.1->v=u:=λl hl v hv hlv=>
    cQ.1 (by rw[h1 l (mF.1 hl).1]) v (bb.2 ⟨hv,hlv⟩)
     u (bb.2 ⟨a8,(mF.1 hl).2⟩)
   obtain ⟨hi,a1,a7,a0⟩:=o7 l1 (mF.1 ec).1 l2 (mF.1 c6).1 e0;exact ji h hD d0 m a8 (k hi) (k a1) (k a7) (lp a0)
    (f3 l1 ec) (f3 l2 c6) (mF.1 ec).2 (mF.1 c6).2
lemma oc {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(q7:bH 14 D≤14)(ra:1≤bu 14 D)(hI:aN 14 D={0,1,11}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,gs⟩:=dB hG hS hC;have hb:=cX gs;obtain ⟨r,k⟩:=cR hG h hC;have a8:∀i∈({0,1,11}:S0),i∈aN 14 D:=(by rw[hI];exact λ_ hi=>hi);have h0:=a8 0 o;have h1:=a8 1 o;have a3:=a8 11 o;have m:∀x:F0,x∉({0,1,11}:S0)->x∈aW 14 D:=(by intro x hx;by_contra hc;exact hx (hI▸cl.2 hc));have id:∀x∈aW 14 D,∀i∈aN 14 D,x≠i:=λx hx i hi hxi=>cl.1 hi (hxi▸hx);have edge:∀x y:F0,aH x y->x∈aW 14 D->y∈aW 14 D->∃e∈aG 14 D x,aI e∈aG 14 D y/\(∀i∈aN 14 D,e≠r i/\aI e≠r i)/\x∉O 14 D (W D (aI e)):=(by intro x y hQ hx hy;obtain ⟨e,he,k2,-,hs,-⟩:=bp hG hS hC hQ;exact ⟨e,he,k2,λi hi=>⟨λhc=>id y hy i hi (bx k hi (hc▸k2)),λhc=>id x hx i hi (bx k hi (by rw[← hc,aT];exact he))⟩,hs⟩);have k0:=(k.1 0 h0).2.2.1;have k1:=(k.1 1 h1).2.2.1;have e7:=m 7 o;have e3:=m 3 o;obtain ⟨H,et,er,ej,-⟩:=edge 7 3 o e7 e3;have n8:=bd k h0 (a:=7) o;have h6:=bd k h1 (a:=7) o;have hh:r 0≠r 1:=λhc=>absurd (k.2 0 h0 1 h1 hc) o;obtain ⟨q6,qS⟩:=fC n8 h6 et hh (ej 0 h0).1.symm (ej 1 h1).1.symm;have c7:=fx h hD b hb e7;have hr:=dd hS b hb;have hp:=db 14 D;rw[hI,show ({0,1,11}:S0).card=3 from rfl] at hp;have p3:=dn 14 D;have q9:(ru D b 7).card≤(aR 14 D b).card:=cF _ _;have lw:∀(u:P0) (x:F0),(∀v∈aR 14 D b,x∈O 14 D v.1->v=u)->(aG 14 D x).card+(bi 14 D (ba 14 D {x})).card≤3/\(x∉O 14 D u.1->(aG 14 D x).card≤2):=by
  intro u x hu;have q1:=ci h hD b hb x
  have q2:(ru D b x).card≤1:=cQ.2 (λa ha c hc=>
   (hu a (bb.1 ha).1 (bb.1 ha).2).trans (hu c (bb.1 hc).1 (bb.1 hc).2).symm)
  refine ⟨Y,λhn=>?_⟩
  have:(ru D b x).card=0:=cZ.2 (fE.2 (λv hv hxv=>hn (hu v hv hxv▸hxv)))
  omega
 have nB:(ru D b 7).card≠2:=by
  intro hk;have a5:∀u∈aR 14 D b,7∈O 14 D u.1:=(by have hE:ru D b 7=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← hE] at hu;exact (bb.1 hu).2);have b5:∀i∈({0,1}:S0),aU 14 D i.val (aO 14 D):=by
   intro i hi;by_contra qE;obtain ⟨z,m3,qz,qv⟩:=(cr hG h hC (a8 i (e9 i hi).1)).resolve_left qE;have hU:aH 7 i:=(e9 i hi).2.1;have hy:∃y:F0,(y=3\/y=12)/\∃w,y∈O 14 D w/\7∈O 14 D w:=by
    by_cases h3:∃u∈aR 14 D b,3∈O 14 D u.1
    ·obtain ⟨u,hu,b6⟩:=h3;exact ⟨3,oL rfl,u.1,b6,a5 u hu⟩
    ·have qo:(ru D b 3).card=0:=cZ.2
      (fE.2 (λu hu b6=>h3 ⟨u,hu,b6⟩))
     have:=ci h hD b hb 3;obtain ⟨Z,-,hZ,-⟩:=ps h hD k a3 o
      (bd k a3 (a:=3) o) Y
     obtain ⟨g,hg,ev,hN,-⟩:=edge 3 12 o e3 (m 12 o);rw[hZ,mI,mS] at hg er;rw[hg.resolve_left (hN 11 a3).1,← er.resolve_left (ej 11 a3).2,aT] at ev;exact ⟨12,oR rfl,_,(aP.1 ev).2.1,(aP.1 et).2.1⟩
   obtain ⟨y,m8,w,qw,qi⟩:=hy;have qB:({8,10,9,13,y}:S0).card=5:=(by rcases m8 with rfl|rfl<;>rfl);have c5:=dl h hD b gs e7 {8,10,9,13,y} ∅ {z}
    (λx hx=>by
     simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl
     iterate 2 exact ⟨m _ o,o,λu hu _=>a5 u hu,_,k0 _ o,k0 7 o⟩
     iterate 2 exact ⟨m _ o,o,λu hu _=>a5 u hu,_,k1 _ o,k1 7 o⟩
     rcases m8 with rfl|rfl<;>
      exact ⟨m _ o,o,λu hu _=>a5 u hu,w,qw,qi⟩)
    (λ_ hn=>(nE _ hn).elim)
    (λw' hw'=>by rw[mS.1 hw'];exact ⟨qz,qv,i,hU,m3⟩)
   rw[qB,ad,cS] at c5;omega
  obtain ⟨s,b0,cb,k7,-⟩:=dj h hD hT (by decide:(0:F0)≠1) h0 h1
   (b5 0 o) (b5 1 o)
  by_cases h3:∃u∈aR 14 D b,3∈O 14 D u.1
  ·obtain ⟨u3,pa,b6⟩:=h3;by_cases ja:∃x∈({4,5}:S0),∃u∈aR 14 D b,x∈O 14 D u.1
   ·obtain ⟨x0,es,ux,qO,l7⟩:=ja;have qc:({8,10,9,13,3,x0}:S0).card=6:=by
     have fc:=es;simp only[mI,mS] at fc;rcases fc with h4|h4<;>rw[h4]<;>rfl
    have c5:=dl h hD b gs e7 {8,10,9,13,3,x0} ∅ ∅
     (λx hx=>by
      simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl|qJ
      iterate 2 exact ⟨m _ o,o,λu hu _=>a5 u hu,_,k0 _ o,k0 7 o⟩
      iterate 2 exact ⟨m _ o,o,λu hu _=>a5 u hu,_,k1 _ o,k1 7 o⟩
      ·exact ⟨e3,o,λu hu _=>a5 u hu,u3.1,b6,a5 u3 pa⟩
      ·rw[qJ]
       exact ⟨m x0 (lH x0 es).1,(lH x0 es).2,λu hu _=>a5 u hu,ux.1,l7,a5 ux qO⟩)
     (λ_ hn=>(nE _ hn).elim)
     (λ_ hz=>(nE _ hz).elim)
    rw[qc,ad] at c5;omega
   ·have q5:(ru D b 4).card=0:=cZ.2
     (fE.2 (λu hu h4u=>ja ⟨4,o,u,hu,h4u⟩))
    have q3:=ci h hD b hb 4;obtain ⟨Z4,-,qs,lc⟩:=ps h hD k a3 o
     (bd k a3 (a:=4) o) Y
    obtain ⟨e1,b2,b1,a7,-⟩:=edge 4 10 o (m 4 o) (m 10 o);have hB:=b2;rw[qs,mI,mS] at hB;have ez:e1=Z4:=hB.resolve_left (a7 11 a3).1;rw[ez] at b1;obtain ⟨e5,p9,oz,qg,-⟩:=edge 10 5 o (m 10 o) (m 5 o);have hL:(aM D,s)∈aG 14 D 10:=cV hD hT (cb 10 o);have c6:(aM D,s)≠aI Z4:=λhe=>by
     have iz:(4:F0)∈O 14 D (W D Z4):=(aP.1 (ez▸b2)).2.1
     have:W D (aI (aM D,s))=W D Z4:=by rw[he,aT]
     rw[← this,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,b0] at iz;exact nE _ iz
    have c3:(aM D,s)≠e5:=λhe=>by
     have ll:(5:F0)∈O 14 D (W D (aI e5)):=(aP.1 oz).2.1;rw[← he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,b0] at ll;exact nE _ ll
    have ea:aI Z4≠e5:=λhe=>
     lc 5 o (by rw[← aT Z4,he];exact oz)
    have hd:({r 0,(aM D,s),aI Z4,e5}:Finset (A0))⊆aG 14 D 10:=by
     intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl|rfl
     ·exact bd k h0 o
     ·exact hL
     ·exact b1
     ·exact p9
    have k3:=cL hd
    rw[cI (by
       simp[(cw k b0 h0).symm,(ez▸(a7 0 h0).2).symm,(qg 0 h0).1.symm]),
      cI (by simp[c6,c3]),
      cP ea] at k3
    have p8:=ci h hD b hb 10;have p6:(ru D b 10).card≤(aR 14 D b).card:=cF _ _;have a6:∀u∈aR 14 D b,(10:F0)∈O 14 D u.1:=(by have hE:ru D b 10=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← hE] at hu;exact (bb.1 hu).2);have c5:=dl h hD b gs (m 10 o) {7,8,9,13,3} {4,5} ∅
     (λx hx=>by
      simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl
      ·exact ⟨e7,o,λu hu _=>a6 u hu,_,cb 7 o,cb 10 o⟩
      ·exact ⟨m 8 o,o,λu hu _=>a6 u hu,_,cb 8 o,cb 10 o⟩
      ·exact ⟨m 9 o,o,λu hu _=>a6 u hu,_,k7 9 o,cb 10 o⟩
      ·exact ⟨m 13 o,o,λu hu _=>a6 u hu,_,k7 13 o,cb 10 o⟩
      ·exact ⟨e3,o,λu hu _=>a6 u hu,u3.1,b6,a6 u3 pa⟩)
     (λn hn=>by
      simp only[mI,mS] at hn
      rcases hn with rfl|rfl<;>exact ⟨m _ o,o,o⟩)
     (λ_ hz=>(nE _ hz).elim)
    rw[show ({7,8,9,13,3}:S0).card=5 from rfl,show ({4,5}:S0).card=2 from rfl,ad] at c5;omega
  ·have qo:(ru D b 3).card=0:=cZ.2
    (fE.2 (λu hu b6=>h3 ⟨u,hu,b6⟩))
   have:=ci h hD b hb 3;obtain ⟨Z,-,hZ,-⟩:=ps h hD k a3 o
    (bd k a3 (a:=3) o) Y
   obtain ⟨g,hg,ev,hN,-⟩:=edge 3 12 o e3 (m 12 o);rw[hZ,mI,mS] at hg er;rw[hg.resolve_left (hN 11 a3).1,← er.resolve_left (ej 11 a3).2,aT] at ev;have c5:=dl h hD b gs e7 {8,10,9,13,12} {3} ∅
    (λx hx=>by
     simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl
     iterate 2 exact ⟨m _ o,o,λu hu _=>a5 u hu,_,k0 _ o,k0 7 o⟩
     iterate 2 exact ⟨m _ o,o,λu hu _=>a5 u hu,_,k1 _ o,k1 7 o⟩
     exact ⟨m 12 o,o,λu hu _=>a5 u hu,_,(aP.1 ev).2.1,(aP.1 et).2.1⟩)
    (λn hn=>by rw[mS.1 hn];exact ⟨e3,o,o⟩)
    (λ_ hz=>(nE _ hz).elim)
   rw[show ({8,10,9,13,12}:S0).card=5 from rfl,cS,ad] at c5;omega
 obtain ⟨u1,ls⟩:=cO.1 (show 0<(ru D b 7).card by omega);obtain ⟨f3,i5⟩:=bb.1 ls
 have h5:∀v∈aR 14 D b,7∈O 14 D v.1->v=u1:=λv hv h7v=>
  cQ.1 (show (ru D b 7).card≤1 by omega) v (bb.2 ⟨hv,h7v⟩) u1 ls
 have hm:=qS Y;have hq:=λe he=>or_left_comm.1 (hm e he);have ca:∀t,t∈O 14 D u1.1->t≠7->t∈O 14 D (W D (r 0))/\t∈O 14 D (W D (r 1)):=by
  intro t ht g0;have qp:=eQ f3 ht;obtain ⟨e0,bm⟩:=ek hG h hC b hb (nS g0) e7
   (λv hv h7v=>by rw[h5 v hv h7v];exact ht) ⟨i5,ht⟩
  have mk:∀i j:F0,j∈aN 14 D->j∈({0,1}:S0)->(∀e∈aG 14 D 7,e=r i\/e=r j\/e=H)->t∈O 14 D (W D (r i))->t∈O 14 D (W D H)->False:=by
   intro i j hj mt hW qj qn;obtain ⟨q,qU,qF,qK⟩:=pI j mt t (id t qp j hj);obtain ⟨e,he,n1,n2⟩:=bB h hD (x:=7) (nS g0)
    (nS qF) (bw.1 qK)
   rcases hW e he with rfl|rfl|rfl
   ·exact n1 qj
   ·exact n2 ((k.1 j hj).2.2.1 q ((aK _ _).1 qU))
   ·exact n1 qn
  by_cases c0:r 0=e0
  ·exact (mk 1 0 h0 o hq (bm _ h6 (λhc=>hh (c0.trans hc.symm))) (bm _ et (λhc=>(ej 0 h0).1 (hc.trans c0.symm)))).elim
  ·have a0:=bm _ n8 c0;by_cases c1:r 1=e0
   ·exact (mk 0 1 h1 o hm a0 (bm _ et (λhc=>(ej 1 h1).1 (hc.trans c1.symm)))).elim
   ·exact ⟨a0,bm _ h6 c1⟩
 have nR:(aR 14 D b).card≠1:=by
  intro hR;have L:=λx=>lw u1 x (λv hv _=>cQ.1 hR.le v hv u1 f3)
  have hF:∀i∈aN 14 D,∀t,t∈O 14 D (W D (r i))->r i∈aG 14 D t:=λi hi t ht=>aP.2 ⟨(k.1 i hi).1,ht,by
     rw[(k.1 i hi).2.1];exact nE t⟩
  have e4:=m 4 o;have a4:=bd k a3 (a:=4) o;have ix:=bd k h0 (a:=10) o;obtain ⟨e1,b2,b1,a7,-⟩:=edge 4 10 o e4 (m 10 o);obtain ⟨e2,ec,b8,eu,-⟩:=edge 4 13 o e4 (m 13 o);have n4:4∉O 14 D u1.1:=by
   intro h4;obtain ⟨q0,q1⟩:=ca 4 h4 o;rcases (fC (hF 0 h0 4 q0) (hF 1 h1 4 q1) b2 hh (a7 0 h0).1.symm (a7 1 h1).1.symm).2 (by have:=(L 4).1;omega) _ a4 with hc|hc|hc
   ·exact absurd (k.2 11 a3 0 h0 hc) o
   ·exact absurd (k.2 11 a3 1 h1 hc) o
   ·exact (a7 11 a3).1 hc.symm
  have c8:e1=e2:=(by by_contra hc;have:=(fC a4 b2 ec (a7 11 a3).1.symm (eu 11 a3).1.symm hc).1;have:=(L 4).2 n4;omega);rw[← c8] at b8;obtain ⟨e,he,n7,qX⟩:=bB h hD (x:=10) (a:=7) (b:=13)
   o o o
  have d1:aI e1≠e:=λhc=>qX (hc▸(aP.1 b8).2.1);have d2:r 0≠e:=λhc=>n7 (hc▸k0 7 o);by_cases p0:10∈O 14 D u1.1
  ·rcases (fC b1 ix (hF 1 h1 10 (ca 10 p0 o).2) (a7 0 h0).2 (a7 1 h1).2 hh).2 (by have:=(L 10).1;omega) e he with hc|hc|hc
   ·exact d1 hc.symm
   ·exact d2 hc.symm
   ·exact n7 (hc▸k1 7 o)
  ·have:=(fC b1 ix he (a7 0 h0).2 d1 d2).1;have:=(L 10).2 p0;omega
 have q8:bu 14 D=1:=Y;have hH:∀a c:F0,a∈({0,1,11}:S0)->c∈({0,1,11}:S0)->a≠c->aU 14 D a.val (aO 14 D)->aU 14 D c.val (aO 14 D)->False:=by
  intro a c ha hc i3 qH qM;obtain ⟨s,b0,qd,qt,-⟩:=dj h hD hT i3 (a8 a ha) (a8 c hc) qH qM;have qG:(7:F0)∈O 14 D (W D (aM D,s)):=by
   rcases o6 a ha c hc i3 with qT|qA
   ·exact qd 7 qT
   ·exact qt 7 qA
  have ik:(aM D,s)∈aG 14 D 7:=cV hD hT qG;rcases hm (aM D,s) ik with he|he|he
  ·exact cw k b0 h0 he
  ·exact cw k b0 h1 he
  ·have jb:(3:F0)∈O 14 D (W D (aI H)):=(aP.1 er).2.1;rw[← he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,b0] at jb;exact nE _ jb
 have eb:∀i∈({0,1}:S0),aU 14 D i.val (aO 14 D)\/∃j∈aN 14 D,j≠i/\∃z,aU 14 D i.val z/\aU 14 D j.val z:=by
  intro i hi;rcases cr hG h hC (a8 i (e9 i hi).1) with p2|⟨zi,i0,ko,l0⟩
  ·exact oL p2
  ·obtain ⟨j1,hK,j2,hJ,i7,iy,ks⟩:=pF i hi;rcases cr hG h hC (a8 j1 hK) with c1|⟨z1,qV,qQ,qa⟩
   ·rcases cr hG h hC (a8 j2 hJ) with c2|⟨z2,qD,qf,qP⟩
    ·exact (hH j1 j2 hK hJ i7 c1 c2).elim
    ·have hO:=ex hS Y ko l0 qf qP;exact oR ⟨j2,a8 j2 hJ,ks,zi,i0,hO▸qD⟩
   ·have hO:=ex hS Y ko l0 qQ qa;exact oR ⟨j1,a8 j1 hK,iy,zi,i0,hO▸qV⟩
 have fl:∀i j:F0,i∈({0,1}:S0)->j∈({0,1}:S0)->i≠j->(∀e∈aG 14 D 7,e=r i\/e=r j\/e=H)->∀t,t∈O 14 D (W D (r i))->aH i t:=by
  intro i j hi hj p7 hW t;have qy:=a8 i (e9 i hi).1;have qq:=a8 j (e9 j hj).1;have hU:aH i 7:=(e9 i hi).2.2.1;have ql:i≠3:=(e9 i hi).2.2.2;refine (i6 h hD k qy hU (λp hp h2 hsub=>?_) (eb i hi) t).1;rcases hW p hp with rfl|rfl|rfl
  ·exact h2 rfl
  ·exact p7 (singleton_subset_singleton.1 ((k.1 j qq).2.2.2.symm.subset.trans hsub)).symm
  ·exact ql (mS.1 (hsub (aP.1 er).2.1)).symm
 have f0:=fl 0 1 o o o hm;have f1:=fl 1 0 o o o hq;have hY:∀t,t∈O 14 D u1.1->t=7:=(by intro t ht;by_contra g0;obtain ⟨q0,q1⟩:=ca t ht g0;exact g0 (jJ t (f0 t q0) (f1 t q1)));have i4:((aR 14 D b).erase u1).card=1:=(by rw[cE f3];omega);obtain ⟨u2,pr⟩:=cO.1 (i4▸Nat.one_pos);have pb:=mO pr;have fz:∀x:F0,x≠7->∀u∈aR 14 D b,x∈O 14 D u.1->u=u2:=λx hx u hu hxu=>cQ.1 i4.le u
  (mE.2 ⟨λhc=>hx (hY x (hc▸hxu)),hu⟩) u2 pr
 have L:=λx hx=>lw u2 x (fz x hx);have ct:∀x y:F0,x≠7->x≠y->x∈O 14 D u2.1->y∈O 14 D u2.1->∃e0,∀e∈aG 14 D x,e≠e0->y∈O 14 D (W D e):=λx y hx hQ hxu hyu=>ek hG h hC b hb hQ (eQ pb hxu)
   (λu hu hxu'=>by rw[fz x hx u hu hxu'];exact hyu) ⟨hxu,hyu⟩
 have h7:∀i l:F0,i∈aN 14 D->aH i l->l≠7->l∉O 14 D u2.1->∀P∈aG 14 D l,P≠r i->∀t,t≠l->P∉aG 14 D t:=by
  intro i l hi d0 ho hn P hP qh;obtain ⟨Z,-,hZ,qC⟩:=ps h hD k hi
   (λhx=>bW i (by rw[hx] at d0;exact d0)) (bd k hi d0)
   ((L l ho).2 hn)
  rw[hZ,mI,mS] at hP;rw[hP.resolve_left qh];exact qC
 have Q:∀l1 l2:F0,aH 0 l1->aH 1 l2->l1≠7->l2≠7->∀P:A0,P∈aG 14 D l1->P∈aG 14 D l2->P≠r 0->P≠r 1->False:=by
  intro l1 l2 a1 a2 n1 n2 P ih j0 qY l4;have hl:l1≠l2:=λhc=>n1 (jJ l1 a1 (hc▸a2));obtain ⟨e0,bm⟩:=ct l1 l2 n1 hl
   (by by_contra hn;exact h7 0 l1 h0 a1 n1 hn P ih qY l2 (nS hl) j0)
   (by by_contra hn;exact h7 1 l2 h1 a2 n2 hn P j0 l4 l1 hl ih)
  have qx:r 0=e0:=(by by_contra hc;exact n2 (jJ l2 (f0 l2 (bm _ (bd k h0 a1) hc)) a2));obtain ⟨e,he,n7,nl⟩:=bB h hD (x:=l1) (a:=7) (b:=l2) n1 hl
   (pc l2 a2)
  by_cases hc:e=e0
  ·exact n7 (by rw[hc,← qx];exact k0 7 o)
  ·exact nl (bm e he hc)
 have f2:∀d la lb:F0,(d=4/\la=10/\lb=13)\/(d=6/\la=8/\lb=9)->∃e1 e2,(∀e∈aG 14 D d,e=r 11\/e=e1\/e=e2)/\e1∈aG 14 D d/\e2∈aG 14 D d/\e1≠r 11/\e2≠r 11/\e1≠e2/\aI e1∈aG 14 D la/\aI e2∈aG 14 D lb/\(∀t,t≠la->aI e1∉aG 14 D t)/\(∀t,t≠lb->aI e2∉aG 14 D t)/\d∈O 14 D u2.1/\bi 14 D (ba 14 D {d})=∅:=by
  intro d la lb hM;obtain ⟨⟨g1,g2,g3⟩,⟨g4,g5,g6,g7,g8⟩,⟨n1,n2,n3,n4,n5⟩,g9,g10⟩:=mQ d la lb hM;obtain ⟨e1,b2,b1,a7,qk⟩:=edge d la g5 (m d g1) (m la g2);obtain ⟨e2,ec,b8,eu,qm⟩:=edge d lb g6 (m d g1) (m lb g3)
  have c8:e1≠e2:=λhc=>
   Q la lb g7 g8 n1 n2 (aI e1) b1 (hc▸b8) (a7 0 h0).2 (a7 1 h1).2
  obtain ⟨q4,qW⟩:=fC (bd k a3 g4) b2 ec (a7 11 a3).1.symm
   (eu 11 a3).1.symm c8
  have q1:=(L d n3).1;have p1:d∈O 14 D u2.1:=(by by_contra hn;have:=(L d n3).2 hn;omega);have hw:∀(i l:F0) (e:A0),i∈aN 14 D->aH i l->l≠7->l≠d->aI e∈aG 14 D l->aI e≠r i->d∉O 14 D (W D (aI e))->(∀t,t∈O 14 D (W D (r i))->aH i t)->¬aH i d->∀t,t≠l->aI e∉aG 14 D t:=(by intro i l e hi d0 ho qb lo hf hs fi qe;refine h7 i l hi d0 ho (λhl=>?_) _ lo hf;obtain ⟨e0,bm⟩:=ct l d ho qb hl p1;have hx:aI e=e0:=(by by_contra hc;exact hs (bm _ lo hc));exact qe (fi d (bm _ (bd k hi d0) (λhc=>hf (hx.trans hc.symm)))));exact ⟨e1,e2,qW Y,b2,ec,(a7 11 a3).1,(eu 11 a3).1,c8,b1,b8,hw 0 la e1 h0 g7 n1 n4 b1 (a7 0 h0).2 qk f0 g9,hw 1 lb e2 h1 g8 n2 n5 b8 (eu 1 h1).2 qm f1 g10,p1,cZ.1 Y⟩
 obtain ⟨e1,e2,-,b2,ec,m1,m2,c8,b1,b8,-,-,qr,-⟩:=f2 4 10 13 (oL ⟨rfl,rfl,rfl⟩);obtain ⟨g1,g2,qZ,-,-,-,-,-,-,-,h2,qI,qN,qu⟩:=f2 6 8 9 (oR ⟨rfl,rfl,rfl⟩);obtain ⟨e0,bm⟩:=ct 4 6 o o qr qN;have fin:∀(e:A0) (l:F0),e∈aG 14 D 4->aI e∈aG 14 D l->l≠8->l≠9->e≠r 11->e≠e0->False:=by
  intro e l he hA h8 h9 hX l3;rcases qZ e (pq hS qu (aP.1 he).1 (dJ hS he) (bm e he l3))
   with rfl|rfl|rfl
  ·exact hX rfl
  ·exact h2 l h8 hA
  ·exact qI l h9 hA
 by_cases c:e1=e0
 ·exact fin e2 13 ec b8 o o m2 (λhc=>c8 (c.trans hc.symm))
 ·exact fin e1 10 b2 b1 o o m1 c
lemma kn {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(qD:bH 14 D≤14)(qH:1≤bu 14 D)(hI:aN 14 D=bM)(qE:e8 D 7≤e8 D 3):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,hB⟩:=dB hG hS hC;have hb:=cX hB;obtain ⟨a1,m⟩:=cR hG h hC;obtain ⟨H,ej,b2,qd,qc,-⟩:=bp hG hS hC (x:=3) (y:=7) o;have hK:ef D b a1:=⟨h,hD,hb,m,hI⟩;have r:=d3 hK;have a5:=fD hK;have i0:=r 0 o;have i1:=r 1 o;have l3:=a5 3 o;have l7:=a5 7 o;have hR:(aR 14 D b).card+bu 14 D≤4:=(by have h1:=dd hS b hb;have h2:=db 14 D;have h3:=dn 14 D;rw[hI,show bM.card=4 from rfl] at h2;omega);have b1:=kw hK (x:=7) {0,1} o;have b0:=kw hK (x:=3) {11,12} o;have d0:∀i∈aN 14 D,aI H≠a1 i:=λi hi=>fB m hi l3 ej;have e1:∀i∈aN 14 D,H≠a1 i:=λi hi=>fe m hi l7 b2
 have c7:=fk m _ b1 {aI H} (λe he=>by
  rw[mS.1 he];exact ⟨b2,λi hi=>d0 i (b1 i hi).1⟩)
 have c3:=fk m _ b0 {H} (λe he=>by
  rw[mS.1 he];exact ⟨ej,λi hi=>e1 i (b0 i hi).1⟩)
 have hO:({0,1}:S0).card=2/\({11,12}:S0).card=2/\({4,6,2,5}:S0).card=4:=⟨rfl,rfl,rfl⟩;rw[cS,hO.1] at c7;rw[cS,hO.2.1] at c3;have k7:=fx h hD b hb l7;have k3:=fx h hD b hb l3;have e7:=lU hK l7;have e3:=lU hK l3;have d2:=(aP.1 ej).2.1;have hX:∀x∈({4,6,2,5}:S0),x∈aW 14 D/\x≠3/\x≠7/\∃w,x∈O 14 D w/\(3:F0)∈O 14 D w:=(by intro x hx;obtain ⟨g1,g2,g3,i,hi,g4,g5⟩:=(by decide:∀x∈({4,6,2,5}:S0),x∉bM/\x≠3/\x≠7/\∃i∈bM,aQ i x=true/\aQ i 3=true) x hx;have fi:=(m.1 i (r i hi)).2.2.1;exact ⟨a5 x g1,g2,g3,_,fi x ((aK _ _).1 g4),fi 3 ((aK _ _).1 g5)⟩);have a4:∀{v t0:F0} (J:S0)
   (hJ:∀i∈J,i∈aN 14 D/\a1 i∈aG 14 D v)
   {P:A0} (_:P∈aG 14 D v/\∀i∈aN 14 D,P≠a1 i)
   (_:t0∈O 14 D (W D (aI P)))
   (_:(aG 14 D v).card≤J.card+1)
   (i:F0) (_:i∈J) (_:aQ i v=true/\t0≠i)
   (_:aU 14 D i.val (aO 14 D)\/∃j∈aN 14 D,j≠i/\∃z,aU 14 D i.val z/\aU 14 D j.val z),
   ∀t,t∈O 14 D (W D (a1 i))<->aH i t:=by
  intro v t0 J hJ P hP hW e5 i hi hg c0;refine i6 h hD m (hJ i hi).1 ((aK _ _).1 hg.1) (λp hp er hsub=>?_) c0;by_cases h1:∃j∈J,p=a1 j
  ·obtain ⟨j,hj,rfl⟩:=h1;have h2:j∈O 14 D (W D (aI (a1 j))):=by
    rw[show W D (aI (a1 j))=W D ((a1 j).1,!(a1 j).2) from rfl,(m.1 j (hJ j hj).1).2.2.2];exact mX j
   exact er (by rw[mS.1 (hsub h2)])
  ·by_cases h2:p=P
   ·exact hg.2 (mS.1 (hsub (h2▸hW)))
   ·have:=fk m J hJ {P,p} (λe he=>by
     rcases mI.1 he with he|he
     ·rw[he];exact ⟨hP.1,λj hj=>hP.2 j (hJ j hj).1⟩
     ·rw[mS.1 he]
      exact ⟨hp,λj hj hpj=>h1 ⟨j,hj,hpj⟩⟩)
    rw[cP (nS h2)] at this;omega
 have a0:∀{v t0:F0} (J:S0)
   (hJ:∀i∈J,i∈aN 14 D/\a1 i∈aG 14 D v)
   {P:A0} (_:P∈aG 14 D v/\∀i∈aN 14 D,P≠a1 i)
   (_:t0∈O 14 D (W D (aI P)))
   (_:(aG 14 D v).card≤J.card+1)
   {s:Bool},O 14 D (W D (aM D,!s))=∅->(aM D,s)∈aG 14 D v->False:=by
  intro v t0 J hJ P hP hW e5 s a2 m1;by_cases h1:∃j∈J,(aM D,s)=a1 j
  ·obtain ⟨j,hj,he⟩:=h1;exact cw m a2 (hJ j hj).1 he
  ·by_cases h2:(aM D,s)=P
   ·rw[← h2,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at hW;exact nE _ hW
   ·have:=fk m J hJ {P,(aM D,s)} (λe he=>by
     rcases mI.1 he with he|he
     ·rw[he];exact ⟨hP.1,λj hj=>hP.2 j (hJ j hj).1⟩
     ·rw[mS.1 he]
      exact ⟨m1,λj hj hpj=>h1 ⟨j,hj,hpj⟩⟩)
    rw[cP (nS h2)] at this;omega
 have hA:¬∀u∈aR 14 D b,(7:F0)∈O 14 D u.1->(3:F0)∈O 14 D u.1:=by
  intro hA;obtain ⟨u,hu⟩:=cO.1 (show 0<(ru D b 7).card by omega);rw[bb] at hu;have hw:(7:F0)∈O 14 D u.1/\(3:F0)∈O 14 D u.1:=⟨hu.2,hA u hu.1 hu.2⟩;have p0:=fH m i0 (gz hK i0 l7 hA hw (q:=8) o);have p1:=fH m i1 (gz hK i1 l7 hA hw (q:=9) o)
  have c5:=fk m bM (λi hi=>⟨r i hi,by
   simp only[bM,mI,mS] at hi;rcases hi with rfl|rfl|rfl|rfl
   exacts [p0,p1,(b0 11 o).2,(b0 12 o).2]⟩) {H}
   (λe he=>by rw[mS.1 he];exact ⟨ej,λi hi=>e1 i (r i hi)⟩)
  rw[show bM.card=4 from rfl,cS] at c5;have g9:ru D b 3=aR 14 D b:=eS (fS _ _) Y;have f1:=dl h hD b hB l3 {4,6,2,5} {7} ∅
   (λx hx=>⟨(hX x hx).1,(hX x hx).2.1,λu hu _=>(bb.1 (g9▸hu)).2,(hX x hx).2.2.2⟩)
   (λn hn=>by rw[mS.1 hn];exact ⟨l7,o,o⟩)
   (λ_ hz=>(nE _ hz).elim)
  rw[hO.2.2,cS,ad] at f1;omega
 obtain ⟨uk,e0,pr,ks⟩:∃u∈aR 14 D b,(7:F0)∈O 14 D u.1/\(3:F0)∉O 14 D u.1:=(by by_contra a6;exact hA (λu hu h7=>by by_contra h3;exact a6 ⟨u,hu,h7,h3⟩))
 have mt:ru D b 3⊆(aR 14 D b).erase uk:=λu hu=>
  mE.2 ⟨λe=>ks (e▸(bb.1 hu).2),(bb.1 hu).1⟩
 have k0:=cL mt;rw[cE e0] at k0;have ls:(ru D b 7).card=1:=by
  by_contra ls;have b6:bu 14 D=1:=Y
  have qG:=cA (ru D b 3) (ru D b 7);have qF:(ru D b 3∪ru D b 7).card≤(aR 14 D b).card:=cL (uS (fS _ _) (fS _ _));obtain ⟨uj,i3⟩:=cO.1 (show 0<(ru D b 3∩ru D b 7).card by omega);rw[mN,bb,bb] at i3;have hw:(3:F0)∈O 14 D uj.1/\(7:F0)∈O 14 D uj.1:=⟨i3.1.2,i3.2.2⟩;have lw:∀i∈bM,∀j∈bM,i≠j->a1 i≠a1 j:=λi hi j hj hij e=>hij (m.2 i (r i hi) j (r j hj) e);have a7:=j9 hK l3 o hw Y (b0 11 o).2
   (b0 12 o).2 ej ⟨lw 11 o 12 o o,(e1 11 (r 11 o)).symm,(e1 12 (r 12 o)).symm⟩ qd
  have a3:=j9 hK l7 o hw.symm (by rw[inter_comm];omega)
   (b1 0 o).2 (b1 1 o).2 b2 ⟨lw 0 o 1 o o,(d0 0 i0).symm,(d0 1 i1).symm⟩ qc
  obtain ⟨j,hj,p6⟩:∃j∈({11,12}:S0),(7:F0)∈O 14 D (W D (a1 j)):=by
   rcases a7 with n3|n5
   ·exact ⟨11,o,n3⟩
   ·exact ⟨12,o,n5⟩
  obtain ⟨i',ct,h0⟩:∃i'∈({0,1}:S0),(3:F0)∈O 14 D (W D (a1 i')):=by
   rcases a3 with qp|qs
   ·exact ⟨0,o,qp⟩
   ·exact ⟨1,o,qs⟩
  have id:∀k∈insert j ({0,1}:S0),k∈aN 14 D/\a1 k∈aG 14 D 7:=by
   intro k hk;rcases mI.1 hk with qf|hk
   ·rw[qf];exact ⟨(b0 j hj).1,fH m (b0 j hj).1 p6⟩
   ·exact b1 k hk
  have la:∀k∈insert i' ({11,12}:S0),k∈aN 14 D/\a1 k∈aG 14 D 3:=by
   intro k hk;rcases mI.1 hk with p8|hk
   ·rw[p8];exact ⟨(b1 i' ct).1,fH m (b1 i' ct).1 h0⟩
   ·exact b0 k hk
  have qB:(insert j ({0,1}:S0)).card=3:=(by have ll:=hj;rw[mI,mS] at ll;rcases ll with h1|h1<;>rw[h1]<;>rfl);have qA:(insert i' ({11,12}:S0)).card=3:=(by have h9:=ct;rw[mI,mS] at h9;rcases h9 with h1|h1<;>rw[h1]<;>rfl);have ev:∀a c:F0,a∈bM->c∈bM->a≠c->aU 14 D a.val (aO 14 D)->aU 14 D c.val (aO 14 D)->False:=by
   intro a c ha hc hr hy hE;obtain ⟨s,a2,ez,-,-⟩:=dj h hD hT hr (r a ha) (r c hc) hy hE;rcases kU a ha with i7|ix
   ·exact a0 (insert j {0,1}) id ⟨b2,d0⟩ (by rw[aT];exact d2)
     Y a2 (cV hD hT (ez 7 i7))
   ·exact a0 (insert i' {11,12}) la ⟨ej,e1⟩ (aP.1 b2).2.1
     Y a2 (cV hD hT (ez 3 ix))
  have c0:aU 14 D i'.val (aO 14 D)\/∃k∈aN 14 D,k≠i'/\∃z,aU 14 D i'.val z/\aU 14 D k.val z:=by
   rcases cr hG h hC (b1 i' ct).1 with bm|⟨zi,d1,ea,ec⟩
   ·exact oL bm
   ·obtain ⟨k1,fl,k2,e2,hF,hs,hM⟩:=lZ i' (dy i' ct).1;rcases cr hG h hC (r k1 fl) with c1|⟨z1,j0,i5,ik⟩
    ·rcases cr hG h hC (r k2 e2) with c2|⟨z2,hv,ho,hH⟩
     ·exact (ev k1 k2 fl e2 hF c1 c2).elim
     ·have a8:=ex hS Y ea ec ho hH;exact oR ⟨k2,r k2 e2,hM,zi,d1,a8▸hv⟩
    ·have a8:=ex hS Y ea ec i5 ik;exact oR ⟨k1,r k1 fl,hs,zi,d1,a8▸j0⟩
  have qa:=a4 (insert j {0,1}) id ⟨b2,d0⟩ (by rw[aT];exact d2)
   Y i' (mK ct) ⟨(dy i' ct).2.2.1,(dy i' ct).2.2.2.1⟩ c0
  exact (dy i' ct).2.2.2.2.1 ((qa 3).1 h0)
 have p7:=lj ls e0 pr;have iy:∀t:F0,7≠t->t∈O 14 D uk.1->∀k∈({0,1}:S0),a1 k∈aG 14 D t:=λt ht htu=>lF hK e0 pr p7 o ht htu;have hm:∀a c:F0,a∈({0,1}:S0)->c∈bM->a≠c->aU 14 D a.val (aO 14 D)->aU 14 D c.val (aO 14 D)->False:=by
  intro a c ha hc hr hy hE;obtain ⟨s,a2,ez,-,-⟩:=dj h hD hT hr (r a (dy a ha).1) (r c hc) hy hE;exact a0 {0,1} b1 ⟨b2,d0⟩ (by rw[aT];exact d2) Y a2
   (cV hD hT (ez 7 (dy a ha).2.1))
 have eu:bu 14 D=1->∀i∈({0,1}:S0),∀t,t∈O 14 D (W D (a1 i))<->aH i t:=by
  intro b6 i hi;refine a4 {0,1} b1 ⟨b2,d0⟩ (by rw[aT];exact d2) Y i hi
   ⟨(dy i hi).2.2.1,(dy i hi).2.2.2.1⟩ ?_
  rcases cr hG h hC (r i (dy i hi).1) with bm|⟨zi,d1,ea,ec⟩
  ·exact oL bm
  ·obtain ⟨i2,fi,n8⟩:=(dy i hi).2.2.2.2.2.2.2;rcases cr hG h hC (r i2 (dy i2 fi).1) with c2|⟨z2,hv,ho,hH⟩
   ·rcases cr hG h hC (r 11 o) with qe|⟨qC,lo,p2,p3⟩
    ·exact (hm i2 11 fi o (dy i2 fi).2.2.2.2.2.2.1 c2 qe).elim
    ·have a8:=ex hS Y ea ec p2 p3;exact oR ⟨11,r 11 o,(dy i hi).2.2.2.2.2.1,zi,d1,a8▸lo⟩
   ·have a8:=ex hS Y ea ec ho hH;exact oR ⟨i2,r i2 (dy i2 fi).1,n8,zi,d1,a8▸hv⟩
 have hQ:bu 14 D=1->∀t∈O 14 D uk.1,t=7:=(by intro b6 t ht;by_contra er;have a:=iy t (nS er) ht;exact er ((by decide:∀t:F0,aH 0 t->aH 1 t->t=7) t ((eu b6 0 o t).1 (aP.1 (a 0 o)).2.1) ((eu b6 1 o t).1 (aP.1 (a 1 o)).2.1)));have lc:(ru D b 3).card=1:=by
  by_contra lc;have b6:bu 14 D=1:=Y
  have a8:=eS mt (by rw[cE e0];omega);have b5:∀x:F0,x≠7->∀u∈aR 14 D b,x∈O 14 D u.1->(3:F0)∈O 14 D u.1:=λx hx u hu hxu=>by
   by_cases hL:u=uk
   ·exact absurd (hQ b6 x (hL▸hxu)) hx
   ·exact (bb.1 (a8▸mE.2 ⟨hL,hu⟩)).2
  by_cases c8:∃j∈({11,12}:S0),¬aU 14 D j.val (aO 14 D)
  ·obtain ⟨j,hj,qm⟩:=c8;obtain ⟨z,n4,qk,qj⟩:=(cr hG h hC (r j (gn j hj).1)).resolve_left qm;have f1:=dl h hD b hB l3 {4,6,2,5} {7} {z}
    (λx hx=>⟨(hX x hx).1,(hX x hx).2.1,b5 x (hX x hx).2.2.1,(hX x hx).2.2.2⟩)
    (λn hn=>by rw[mS.1 hn];exact ⟨l7,o,o⟩)
    (λw hw=>by rw[mS.1 hw];exact ⟨qk,qj,j,(gn j hj).2.1,n4⟩)
   rw[hO.2.2,cS,cS] at f1;omega
  ·push Not at c8;obtain ⟨s,a2,hq,pa,-⟩:=dj h hD hT (by decide:(11:F0)≠12)
    (r 11 o) (r 12 o) (c8 11 o) (c8 12 o)
   by_cases fz:∃l∈({10,13}:S0),∃u∈aR 14 D b,l∈O 14 D u.1
   ·obtain ⟨l,hl,ul,qn,lb⟩:=fz;have qt:({4,6,2,5,l}:S0).card=5:=by
     have m2:=hl;simp only[mI,mS] at m2;rcases m2 with h1|h1<;>rw[h1]<;>rfl
    have f1:=dl h hD b hB l3 {4,6,2,5,l} {7} ∅
     (λx hx=>by
      simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|qi
      ·exact ⟨(hX 4 o).1,(hX 4 o).2.1,b5 4 o,(hX 4 o).2.2.2⟩
      ·exact ⟨(hX 6 o).1,(hX 6 o).2.1,b5 6 o,(hX 6 o).2.2.2⟩
      ·exact ⟨(hX 2 o).1,(hX 2 o).2.1,b5 2 o,(hX 2 o).2.2.2⟩
      ·exact ⟨(hX 5 o).1,(hX 5 o).2.1,b5 5 o,(hX 5 o).2.2.2⟩
      ·rw[qi]
       exact ⟨a5 l (gk l hl).1,(gk l hl).2.1,b5 l (gk l hl).2.2.1,ul.1,lb,b5 l (gk l hl).2.2.1 ul qn lb⟩)
     (λn hn=>by rw[mS.1 hn];exact ⟨l7,o,(gk l hl).2.2.2⟩)
     (λ_ hz=>(nE _ hz).elim)
    rw[qt,cS,ad] at f1;omega
   ·have qv:(ru D b 10).card=0:=cZ.2
     (fE.2 (λu hu h10u=>fz ⟨10,o,u,hu,h10u⟩))
    have qz:(ru D b 13).card=0:=cZ.2
     (fE.2 (λu hu h13u=>fz ⟨13,o,u,hu,h13u⟩))
    have qx:=ci h hD b hb 10;have qw:=ci h hD b hb 13;obtain ⟨Z10,-,ko,jb⟩:=ps h hD m i0 o
     (bd m i0 (a:=10) o) Y
    obtain ⟨Z13,-,n7,ql⟩:=ps h hD m i1 o
     (bd m i1 (a:=13) o) Y
    obtain ⟨qu,es,et,-⟩:=bp hG hS hC (x:=10) (y:=4) o;obtain ⟨qb,ca,gs,-⟩:=bp hG hS hC (x:=13) (y:=4) o;have hh:=es;rw[ko,mI,mS] at hh;have fc:qu=Z10:=hh.resolve_left (fe m i0 (a5 4 o) et);rw[fc] at et;have hd:=ca;rw[n7,mI,mS] at hd;have cb:qb=Z13:=hd.resolve_left (fe m i1 (a5 4 o) gs);rw[cb] at gs;have nB:(aM D,s)∈aG 14 D 4:=cV hD hT (hq 4 o)
    have c6:aI Z10≠aI Z13:=λhe=>
     jb 13 o (by rw[← aT Z10,he,aT];exact cb▸ca)
    have f2:(aM D,s)≠aI Z10:=λhe=>by
     have hZ:(10:F0)∈O 14 D (W D Z10):=(aP.1 (fc▸es)).2.1
     have:W D (aI (aM D,s))=W D Z10:=by rw[he,aT]
     rw[← this,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at hZ;exact nE _ hZ
    have e4:(aM D,s)≠aI Z13:=λhe=>by
     have h8:(13:F0)∈O 14 D (W D Z13):=(aP.1 (cb▸ca)).2.1
     have:W D (aI (aM D,s))=W D Z13:=by rw[he,aT]
     rw[← this,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at h8;exact nE _ h8
    have iz:({a1 11,(aM D,s),aI Z10,aI Z13}:Finset (A0))⊆aG 14 D 4:=by
     intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl|rfl
     ·exact bd m (r 11 o) o
     ·exact nB
     ·exact et
     ·exact gs
    have qr:=cL iz
    rw[cI (by
       simp[(cw m a2 (r 11 o)).symm,(fB m (r 11 o) (a5 10 o) (fc▸es)).symm,(fB m (r 11 o) (a5 13 o) (cb▸ca)).symm]),
      cI (by simp[f2,e4]),
      cP c6] at qr
    have qy:=ci h hD b hb 4
    have qq:ru D b 4⊆(aR 14 D b).erase uk:=λu hu=>
     mE.2 ⟨λe=>absurd (hQ b6 4 (e▸(bb.1 hu).2)) o,(bb.1 hu).1⟩
    have nl:ru D b 4=(aR 14 D b).erase uk:=eS qq (by rw[cE e0];omega);have f1:=dl h hD b hB (a5 4 o) {3,6,2,5} {10,13} ∅
     (λx hx=>by
      have b8:=nK x hx;refine ⟨a5 x b8.1,b8.2.1,λu hu hxu=>?_,W D (aM D,s),?_,hq 4 o⟩
      ·by_cases hL:u=uk
       ·exact absurd (hQ b6 x (hL▸hxu)) b8.2.2.1
       ·exact (bb.1 (nl▸mE.2 ⟨hL,hu⟩)).2
      ·rcases b8.2.2.2 with pb|l4
       ·exact hq x pb
       ·exact pa x l4)
     (λn hn=>by
      simp only[mI,mS] at hn
      rcases hn with rfl|rfl<;>exact ⟨a5 _ o,o,o⟩)
     (λ_ hz=>(nE _ hz).elim)
    rw[show ({3,6,2,5}:S0).card=4 from rfl,show ({10,13}:S0).card=2 from rfl,ad] at f1;omega
 obtain ⟨uc,eb⟩:=cO.1 (show 0<(ru D b 3).card by omega);rw[bb] at eb;have qo:=lj lc eb.1 eb.2;have er:uc≠uk:=λe=>ks (e▸eb.2);have ja:∀t:F0,3≠t->t∈O 14 D uc.1->∀k∈({11,12}:S0),a1 k∈aG 14 D t:=λt ht htu=>lF hK eb.1 eb.2 qo o ht htu;have nR:(aR 14 D b).card=2:=by
  by_contra nR;have b6:bu 14 D=1:=Y
  have ev:∀a c:F0,a∈bM->c∈bM->a≠c->aU 14 D a.val (aO 14 D)->aU 14 D c.val (aO 14 D)->False:=by
   intro a c ha hc hr hy hE;obtain ⟨s,a2,ez,-,-⟩:=dj h hD hT hr (r a ha) (r c hc) hy hE;rcases kU a ha with i7|ix
   ·exact a0 {0,1} b1 ⟨b2,d0⟩ (by rw[aT];exact d2)
     Y a2 (cV hD hT (ez 7 i7))
   ·exact a0 {11,12} b0 ⟨ej,e1⟩ (aP.1 b2).2.1
     Y a2 (cV hD hT (ez 3 ix))
  have g0:∀i∈bM,aU 14 D i.val (aO 14 D)\/∃k∈aN 14 D,k≠i/\∃z,aU 14 D i.val z/\aU 14 D k.val z:=by
   intro i hi;rcases cr hG h hC (r i hi) with bm|⟨zi,d1,ea,ec⟩
   ·exact oL bm
   ·obtain ⟨k1,fl,k2,e2,hF,hs,hM⟩:=lZ i hi;rcases cr hG h hC (r k1 fl) with c1|⟨z1,j0,i5,ik⟩
    ·rcases cr hG h hC (r k2 e2) with c2|⟨z2,hv,ho,hH⟩
     ·exact (ev k1 k2 fl e2 hF c1 c2).elim
     ·have a8:=ex hS Y ea ec ho hH;exact oR ⟨k2,r k2 e2,hM,zi,d1,a8▸hv⟩
    ·have a8:=ex hS Y ea ec i5 ik;exact oR ⟨k1,r k1 fl,hs,zi,d1,a8▸j0⟩
  have f3:∀i∈({11,12}:S0),∀t,t∈O 14 D (W D (a1 i))<->aH i t:=λi hi=>a4 {11,12} b0 ⟨ej,e1⟩ (aP.1 b2).2.1 Y i hi
    ⟨(gn i hi).2.2.1,(gn i hi).2.2.2⟩ (g0 i (gn i hi).1)
  have qh:∀t∈O 14 D uc.1,t=3:=(by intro t ht;by_contra ih;have a:=ja t (nS ih) ht;exact ih ((by decide:∀t:F0,aH 11 t->aH 12 t->t=3) t ((f3 11 o t).1 (aP.1 (a 11 o)).2.1) ((f3 12 o t).1 (aP.1 (a 12 o)).2.1)));have e5:(((aR 14 D b).erase uc).erase uk).card≤1:=(by rw[cE (mE.2 ⟨nS er,e0⟩),cE eb.1];omega);have bm:∀x:F0,x≠3->x≠7->∀u∈aR 14 D b,x∈O 14 D u.1->u∈((aR 14 D b).erase uc).erase uk:=λx a3 a7 u hu hx=>mE.2 ⟨λe=>a7 (hQ b6 x (e▸hx)),mE.2 ⟨λe=>a3 (qh x (e▸hx)),hu⟩⟩;have hN:∀x1 x2 i a:F0,(i∈bM/\x1∉bM/\x1≠3/\x1≠7/\x2≠3/\x2≠7/\(aQ i x1=true/\aQ i a=true/\x1≠x2/\x1≠a/\aQ x2 a=false)/\¬aH i x2)->(∀t,t∈O 14 D (W D (a1 i))<->aH i t)->(ru D b x1).card≠0->(ru D b x2).card≠0->False:=(by intro x1 x2 i a hg hf n1 n2;obtain ⟨g1,g2,g3,g4,g5,g6,g7,g8⟩:=hg;obtain ⟨u1,hU⟩:=cO.1 (nP n1);obtain ⟨u2,hY⟩:=cO.1 (nP n2);rw[bb] at hU hY;have h2:=bm x2 g5 g6 u2 hY.1 hY.2;have g9:∀u∈aR 14 D b,x1∈O 14 D u.1->x2∈O 14 D u.1:=λu hu hx=>cQ.1 e5 u (bm x1 g3 g4 u hu hx) u2 h2▸hY.2;exact g8 ((hf x2).1 (gz hK (r i g1) (a5 x1 g2) g9 ⟨hU.2,g9 u1 hU.1 hU.2⟩ g7)));have l1:(ru D b 4).card≠0\/(ru D b 10).card≠0:=by
   by_contra a6;rw[nO,ai,ai] at a6;exact kf hK (x:=4) (y:=10) (z:=13) (i:=11) (j:=0) o
    a6.1 a6.2
  have l2:(ru D b 5).card≠0\/(ru D b 9).card≠0:=by
   by_contra a6;rw[nO,ai,ai] at a6;exact kf hK (x:=5) (y:=9) (z:=10) (i:=12) (j:=1) o
    a6.1 a6.2
  have m3:=f3 11 o;have f0:=eu b6 0 o;rcases l1 with n1|n1<;>rcases l2 with n2|n2
  ·exact hN 4 5 11 3 o m3 n1 n2
  ·exact hN 4 9 11 3 o m3 n1 n2
  ·exact hN 10 5 0 7 o f0 n1 n2
  ·exact hN 10 9 0 7 o f0 n1 n2
 have oz:({uc,uk}:Finset (P0))=aR 14 D b:=eS (λu hu=>by
   rcases mI.1 hu with hu|hu
   ·rw[hu];exact eb.1
   ·rw[mS.1 hu];exact e0) (by rw[cP er,nR])
 have hρ:∀x:F0,(ru D b x).card≤
   (if x∈O 14 D uc.1 then 1 else 0)+if x∈O 14 D uk.1 then 1 else 0:=
  λx=>by
   have:=card_filter (λu:P0=>x∈O 14 D u.1) {uc,uk};rw[sum_pair er,oz] at this;exact this.le
 obtain ⟨F,m8,l0,-⟩:=bp hG hS hC (x:=4) (y:=10) o;have P4:=ke hK (x:=4) (i:=11) {11,12} {0,1} o (ja 4 o)
  (iy 4 o) (hρ 4) ⟨m8,λk hk=>fe m hk (a5 10 o) l0⟩
 have P10:=ke hK (x:=10) (i:=0) {0,1} {11,12} o (iy 10 o)
  (ja 10 o) (by rw[Nat.add_comm];exact hρ 10)
  ⟨l0,λk hk=>fB m hk (a5 4 o) m8⟩
 obtain ⟨e,p9,i4,-⟩:=bp hG hS hC (x:=4) (y:=13) o;rcases P4 e p9 with h1|h1
 ·rw[h1] at i4;obtain ⟨e',qg,h4,h5⟩:=bB h hD (x:=10) (a:=7) (b:=13)
   o o o
  rcases P10 e' qg with h6|h6
  ·exact h5 (h6▸(aP.1 i4).2.1)
  ·obtain ⟨k,hk,rfl⟩:=mM.1 h6;exact h4 (aP.1 (b1 k hk).2).2.1
 ·obtain ⟨k,hk,rfl⟩:=mM.1 h1;exact fe m (b0 k hk).1 (a5 13 o) i4 rfl
lemma mH {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(k:bH 14 D≤14)(l:1≤bu 14 D)(r:aN 14 D={0,1,11,12}):False:=by
 by_cases m:e8 D 7≤e8 D 3
 ·exact kn h hD hT k l r m
 ·obtain ⟨h1,h2,-,h4,-,h6,-,h8⟩:=lk fY (jr aa) h hD;have p:=kt fY (jr aa) h.1 hT;have e1:=lX fY h.1 3;have e2:=lX fY h.1 7;rw[show fY 3=7 from by decide] at e1;rw[show fY 7=3 from by decide] at e2;exact kn h1 h2 p (h4▸k) (h6▸l) (by rw[h8,r];decide) Y
lemma mm {D:aJ}(h:a9 14 D)(p:be D)(hT:cg D)(l:bH 14 D≤14)(m:1≤bu 14 D)(a0:aN 14 D∈dw):False:=by
 have r:br 14 D≤13:=by have:=dn 14 D;omega
 rcases jg _ a0 with ⟨-,k⟩|⟨-,k⟩|⟨-,k|k⟩ |
  ⟨-,k|k|k|k⟩|⟨-,k|k|k⟩|⟨-,k|k⟩|⟨-,k⟩
 ·exact jo h p hT l m 7 (oR (oR rfl)) (λi=>by rw[k];revert i;decide)
 ·exact jo h p hT l m 6 (oR (oL rfl)) (λi=>by rw[k];revert i;decide)
 ·exact jo h p hT l m 5 (oL rfl) (λi=>by rw[k];revert i;decide)
 ·exact oE h p hT l m k
 ·exact on h p hT l m k
 ·exact mc h p hT l m k
 ·exact nj h p hT l m k
 ·exact mH h p hT l m k
 ·exact oa h p l m k
 ·exact mZ h p l m k
 ·exact oc h p hT l m k
 ·exact mr h p r k
 ·exact m9 h p r k
 ·exact nH h p r k
lemma oP:∀p q x:F0,¬aH p q->x≠p->x≠q->∃y:F0,aH x y/\¬aH p y/\¬aH q y:=aa
lemma jA {D:aJ}(hS:aV 14 D)(hD:be D){b:F0->Nat}(a0:dz 14 D b){p q x:F0}(h:¬aH p q)(a2:x≠p)(a3:x≠q)(hx:x∈aW 14 D):val D (aL p q) (b x)=false:=by
 have hG:=bn;have hC:=bl hD;obtain ⟨y,a1,k,m⟩:=oP p q x h a2 a3;have l:fK 14 D (b x) x:=c9 hS (a0 x hx).2.2.1;have a4:¬cN HG (bt {p,q,y}):=by
  refine jv (λa ha c hc=>?_);simp only[mI,mS] at ha hc;rcases ha with rfl|rfl|rfl<;>rcases hc with rfl|rfl|rfl
  ·exact bW _
  ·exact h
  ·exact k
  ·exact λhh=>h (bh hh)
  ·exact bW _
  ·exact m
  ·exact λhh=>k (bh hh)
  ·exact λhh=>m (bh hh)
  ·exact bW _
 have r:cN HG (bs x (bt {p,q,y})):=⟨x,y,a1,d7 x _,by simp[bs,bt]⟩;have h0:=(gc hS hC (bt {p,q,y}) x (b x) l a4 r).1;by_contra h1;rw[bN] at h1
 have hm:=el hS (aL p q) (bt {p,q,y}) (λu hu=>by
  simp only[aL,bO,dT] at hu;simp only[bt,dT,mI,mS]
  rcases hu with rfl|rfl<;>tauto) (b x) h1
 rw[h0] at hm;exact bF hm
lemma ib {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D){k:F0->A0}(b5:ch 14 HG D k){i v:F0}(hi:i∈aN 14 D)(ct:aH i v)(a2:aU 14 D i.val (aO 14 D)){s:Bool}(er:O 14 D (W D (aM D,!s))=∅)(et:v∈O 14 D (W D (aM D,s)))(hv:∀p∈aG 14 D v,p.1≠(k i).1->p.1≠aM D->¬O 14 D (W D (aI p))⊆{i}):∀t:F0,t∈O 14 D (W D (aM D,s))->t∈O 14 D (W D (k i))->aH i t:=by
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have e3:1≤D.length:=hT.1;have f2:=fj h hD b5 hi;obtain ⟨e0,g4,fc,d2,-,-,gs,-⟩:=eJ hG h hC hi;have c7:aI (k i)=e0:=sJ (f2.symm.trans gs);have l:O 14 D (W D (aI (k i)))={i}:=c7▸d2;have m:(k i).1<D.length:=(b5.1 i hi).1;have b1:bf D (k i).1=true:=by
  have h1:(k i).1=e0.1:=by rw[← c7];rfl
  rw[h1];exact fc
 have a3:(k i).1≠aM D:=by
  intro b2;have h1:(k i).2=s\/(k i).2=!s:=by cases (k i).2<;>cases s<;>decide
  rcases h1 with hs|hs
  ·exact cw b5 er hi (pE b2.symm hs.symm)
  ·have h2:W D (aI (k i))=W D (aM D,s):=by
    show W D ((k i).1,!(k i).2)=W D (aM D,s);rw[b2,hs,bK]
   rw[h2] at l;have a6:v=i:=mS.1 (l▸et);exact bW i (a6▸ct)
 have a0:aU 14 D i.val (14+(k i).1):=(by have h1:=fJ hS hi (by rw[l];exact mX i);have d0:aS D (W D (aI (k i)))=1:=(by have g5:=eG.mp hi (W D (aI (k i))) (by rw[l];exact mX i);have g3:1≤aS D (W D (aI (k i))):=eU (b4 (n:=14) m (!(k i).2));omega);exact rT h1 ⟨b4 (n:=14) m (!(k i).2),d0⟩);have cb:aU 14 D i.val (W D (aM D,!s)):=by
  have r:aO 14 D=14+aM D:=by unfold aO aM;omega
  rw[r] at a2;rcases cT a2 with b2|⟨a,ha,a7⟩
  ·omega
  ·obtain ⟨j,s',hj,g0,a5⟩:=dN.mp a7.1;have ec:j=aM D:=Y
   subst ec;have e7:s'≠s:=(by intro f1;subst f1;have eu:=c9 hS ha;have bm:=dZ hG hS hC i a eu;have a6:v=i:=mS.1 (bm (a5▸et));exact bW i (a6▸ct));have c2:s'=!s:=by cases s'<;>cases s<;>simp_all
   rw[c2] at a5;exact a5▸ha
 have a1:∀a u w,aU 14 D a u->aU 14 D a w->aU 14 D u w\/aU 14 D w u:=by
  intro a u w hu hw;induction hu using rI generalizing w with
  | refl=>exact oL hw
  | @head a c hac _ ih=>
   rcases cH hw with rfl|⟨c',eb,a8⟩
   ·exact oR (rH hac ‹_›)
   ·have f0:c'=c:=cY eb.1 hac.1 hac.2;subst f0;exact ih w a8
 have c1:aU 14 D (14+(k i).1) (W D (aM D,!s)):=by
  rcases a1 i.val (14+(k i).1) (W D (aM D,!s)) a0 cb with h1|h2
  ·exact h1
  ·rcases cH h2 with b2|⟨c,hc,a8⟩
   ·exact b2▸rF
   ·exfalso;have e4:c=14+aM D:=cY hc.1 (b4 (n:=14) (by unfold aM;omega:aM D<D.length) (!s)) hc.2;have e2:=bV hS (λ_ _ hh=>hh.1) (e4▸a8);unfold aM at e2 a3;omega
 intro t f3 c8;by_contra fi;have c3:i∈O 14 D (W D ((k i).1,!(k i).2)):=(by show i∈O 14 D (W D (aI (k i)));rw[l];exact mX i);have d1:val D (aL i t) (14+(k i).1)=true:=(by rw[cc hS _ m (k i).2,b1,gop_true,bA];exact ⟨cf hS c8 (by simp[aL]),cf hS c3 (by simp[aL])⟩);have b0:val D (aL i t) (aO 14 D)=false:=(by by_contra h1;rw[bN] at h1;exact fi ((ds i t).mp ((hD _).mp h1)));have es:val D (aL i t) (W D (aM D,!s))=false:=by
  have r:aO 14 D=14+aM D:=by unfold aO aM;omega
  rw[r,cc hS _ (by unfold aM;omega:aM D<D.length) s,hT.2.2.1,gop_true,cf hS f3 (by simp[aL]),aw] at b0;exact b0
 have b8:∀u w,aU 14 D u w->val D (aL i t) u=true->val D (aL i t) w=false->∃a c,aU 14 D u a/\bk 14 D a c/\aS D a=1/\aU 14 D c w/\val D (aL i t) a=true/\val D (aL i t) c=false:=by
  intro u w e5 hu hw;induction e5 with
  | refl=>rw[hu] at hw;exact absurd hw.symm bF
  | @tail a c hab hbc ih=>
   by_cases ha:val D (aL i t) a=true
   ·exact ⟨a,c,hab,hbc.1,hbc.2,rF,ha,hw⟩
   ·obtain ⟨a',c',h1,h2,h3,h4,h5,h6⟩:=ih (bE.mpr ha);exact ⟨a',c',h1,h2,h3,rT h4 hbc,h5,h6⟩
 obtain ⟨a,c,c6,a7,d0,ea,fz,ej⟩:=b8 _ _ c1 d1 es;obtain ⟨j,s',hj,rfl,ca⟩:=dN.mp a7;have c5:bf D j=true:=(by by_contra e1;rw[bT] at e1;rw[cc hS _ hj s',e1,gop_false,ca,fz] at ej;exact absurd ej.symm bF);have ev:j≠(k i).1:=(by have:=bV hS (λ_ _ hh=>hh.1) c6;have:=bv hS hj s';omega);have c0:j≠aM D:=(by have g1:=bV hS (λ_ _ hh=>hh.1) ea;have g2:=bv hS (by unfold aM;omega:aM D<D.length) (!s);omega);have b6:aU 14 D i.val a:=a0.trans c6;have bm:O 14 D a⊆{i}:=dZ hG hS hC i a (c9 hS b6);have fl:v≠i:=λhh=>bW i (hh▸ct);have a4:W D (j,!(!s'))=a:=by rw[bK];exact ca
 have ez:v∈O 14 D (W D (j,!s')):=iY hG hS hC hj (!s') c5 (a4▸b6) (a4▸d0)
   (by unfold aO;omega) ct
 have hp:(j,!s')∈aG 14 D v:=aP.mpr ⟨hj,ez,λhc=>fl (mS.mp (bm (ca▸de hS hj c5 s' hc)))⟩;exact hv (j,!s') hp ev c0 (by rw[show aI (j,!s')=(j,!(!s')) from rfl,a4];exact bm)
lemma kg {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(c1:bu 14 D=0)(hB:br 14 D≤(aW 14 D).card+4)(m:({0,1,2}:S0)⊆aN 14 D):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,hb⟩:=dY h hD;obtain ⟨ca,a3⟩:=cR hG h hC;have b2:∀i∈({0,1,2}:S0),aU 14 D i.val (aO 14 D):=λi hi=>by
  rcases cr hG h hC (m hi) with hc|⟨z,-,c6,c5⟩
  ·exact hc
  ·exact (nN (c5▸eB hS c1 c6)).elim
 obtain ⟨s,ct,b6,c2,-⟩:=dj h hD hT (by decide:(0:F0)≠1)
  (m o) (m o) (b2 0 o) (b2 1 o)
 have a0:({7,8,13}:S0)⊆O 14 D (W D (aM D,s)):=by
  intro x hx;simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl
  ·exact b6 7 ((aK 0 7).1 rfl)
  ·exact b6 8 ((aK 0 8).1 rfl)
  ·exact c2 13 ((aK 1 13).1 rfl)
 obtain ⟨a6,a5⟩:=gp eD (λi hi=>m hi);obtain ⟨-,-,⟨d0,c8⟩,hside,hinj,-⟩:=gr eD;obtain ⟨cb,bm⟩:=gh a3 {7,8,13} {0,1,2} (λi hi=>⟨(a6 i hi).1,(a6 i hi).2.1⟩);have hw:∀f∈({7,8,13}:S0),∃e:A0,e.1<D.length/\bf D e.1=true/\f∈O 14 D (W D e)/\f∉O 14 D (14+e.1)/\Disjoint (O 14 D (W D e)) (tA {7,8,13} f):=(by intro f r;obtain ⟨j,s',h1,h2,h4,h5,h6⟩:=fq hG hS hC (tA {7,8,13} f) (a5 f r).1 f (a5 f r).2.2;exact ⟨(j,s'),h1,h2,h4,h5,h6⟩)
 choose! wf hwf using hw
 have b0:({7,8,13}:S0).image wf⊆bo 14 D (ba 14 D {7,8,13}):=by
  intro e p;obtain ⟨f,r,rfl⟩:=mM.1 p;obtain ⟨h1,h2,h4,h5,h6⟩:=hwf f r;refine e6.2 ⟨h1,⟨f,mN.2 ⟨h4,r⟩⟩,?_⟩;rintro ⟨g,hg⟩;rw[mN] at hg;have c3:g∈O 14 D (W D (wf f)):=de hS h1 h2 (wf f).2 hg.1;exact dL.1 h6 c3
   ((a5 f r).2.1 (mE.2 ⟨λh=>h5 (h▸hg.1),hg.2⟩))
 have a8:iO wf ({7,8,13}:S0):=λf r g hg p=>by
  by_contra d1;exact dL.1 (hwf f r).2.2.2.2 (p▸(hwf g hg).2.2.1)
   ((a5 f r).2.1 (mE.2 ⟨nS d1,hg⟩))
 have b5:Disjoint (({0,1,2}:S0).image ca) (({7,8,13}:S0).image wf):=(by rw[dL];intro e h1 h2;obtain ⟨i,hi,rfl⟩:=mM.1 h1;obtain ⟨f,r,p⟩:=mM.1 h2;obtain ⟨a,ha,c7⟩:=(a6 i hi).2.2 f r;exact dL.1 (hwf f r).2.2.2.2 (p▸(a3.1 i (a6 i hi).1).2.2.1 a c7) ha);have a4:(aM D,s)∈bo 14 D (ba 14 D {7,8,13}):=by
  refine e6.2 ⟨by unfold aM;have:=hT.1;omega,⟨7,mN.2 ⟨a0 o,o⟩⟩,?_⟩;rintro ⟨c,hc⟩;rw[mN] at hc;have c0:14+aM D=aO 14 D:=by unfold aO aM;have:=hT.1;omega
  rw[c0,c4 hD] at hc;exact nE _ hc.1
 have a2:(aM D,s)∉({0,1,2}:S0).image ca:=λhm=>by
  obtain ⟨i,hi,b1⟩:=mM.1 hm;exact cw a3 ct (m hi) b1.symm
 have a1:(aM D,s)∉({7,8,13}:S0).image wf:=λhm=>by
  obtain ⟨f,r,b1⟩:=mM.1 hm
  obtain ⟨g,hg⟩:=cO.1 (show 0<(({7,8,13}:S0).erase f).card by
   rw[cE r];decide)
  exact dL.1 (hwf f r).2.2.2.2 (b1▸a0 (mO hg))
   ((a5 f r).2.1 hg)
 have ec:7≤(bo 14 D (ba 14 D {7,8,13})).card:=by
  have h1:=cL
   (iS.2 ⟨a4,uS cb b0⟩)
  rw[cI (notMem_union.2 ⟨a2,a1⟩),cU b5,bm,cJ a8,c8,d0] at h1;omega
 have l:∀i∈({0,1,2}:S0),bq 14 D {7,8,13} (aX i∩{7,8,13}):=by
  intro i hi;obtain ⟨j,s',-,-,-,hq⟩:=fW hG hS hC {7,8,13}
   (λa ha c hc=>eg 0 a ((hside i hi).1 ha) c ((hside i hi).1 hc)) (b2 i hi)
  refine ⟨W D (j,s'),?_⟩;ext a;simp only[mN,ce];exact ⟨λhh=>⟨(hq a hh.2).1 hh.1,hh.2⟩,λhh=>⟨(hq a hh.2).2 hh.1,hh.2⟩⟩
 have a7:bq 14 D {7,8,13} {7,8,13}:=⟨W D (aM D,s),qR.2 a0⟩
 let M0:=aX 0∩{7,8,13}
 let M1:=aX 1∩{7,8,13}
 let M2:=aX 2∩{7,8,13}
 have b8:M0.card=2/\M1.card=2/\M2.card=2:=⟨(hside 0 o).2.2.2,(hside 1 o).2.2.2,(hside 2 o).2.2.2⟩;have k:M0≠M1/\M0≠M2/\M1≠M2/\M0≠{7,8,13}/\M1≠{7,8,13}/\M2≠{7,8,13}:=(by refine ⟨λp=>absurd (hinj 1 o 0 o (by show M0⊆M1;rw[p])) o,λp=>absurd (hinj 2 o 0 o (by show M0⊆M2;rw[p])) o,λp=>absurd (hinj 2 o 1 o (by show M1⊆M2;rw[p])) o,λp=>by have:=kA card p;omega,λp=>by have:=kA card p;omega,λp=>by have:=kA card p;omega⟩);have eb:({M0,M1,M2,{7,8,13}}:Finset (S0)).card=4:=(by rw[cI (by simp[k.1,k.2.1,k.2.2.2.1]),cI (by simp[k.2.2.1,k.2.2.2.2.1]),cP k.2.2.2.2.2]);have d2:4≤(bi 14 D (ba 14 D {7,8,13})).card:=by
  have h1:=fy hS {7,8,13} {M0,M1,M2,{7,8,13}} (λM hM=>by
   simp only[mI,mS] at hM;rcases hM with rfl|rfl|rfl|rfl
   ·exact ⟨Y,l 0 o⟩
   ·exact ⟨Y,l 1 o⟩
   ·exact ⟨Y,l 2 o⟩
   ·exact ⟨o,a7⟩)
  have h2:(dk 14 D {7,8,13}).card≤(bi 14 D (ba 14 D {7,8,13})).card:=cL (fS _ _);omega
 have h4:=d9 h {7,8,13} (by rw[c4 hD];simp);have h5:=eN hS b hb {7,8,13};have h6:=cL (iL:({7,8,13}:S0)∩aW 14 D⊆{7,8,13});have ea:=dd hS b hb;omega
lemma nA {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(hr:bH 14 D≤14)(f0:bu 14 D=0)(hI:aN 14 D={0,1}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,eb⟩:=dB hG hS hC;have hb:=cX eb;obtain ⟨a0,k⟩:=cR hG h hC;have h0:(0:F0)∈aN 14 D:=by rw[hI];decide
 have h1:(1:F0)∈aN 14 D:=by rw[hI];decide
 have p:∀x:F0,x∉({0,1}:S0)->x∈aW 14 D:=λx hx=>
  ai.1 (λhc=>hx (hI▸cl.2 hc))
 have e0:∀i:F0,i∈aN 14 D->aU 14 D i.val (aO 14 D):=λi hi=>by
  rcases cr hG h hC hi with hc|⟨z,-,ha,g9⟩
  ·exact hc
  ·exact (nN (g9▸eB hS f0 ha)).elim
 obtain ⟨s,a2,a1,b8,-⟩:=dj h hD hT (by decide:(0:F0)≠1) h0 h1
  (e0 0 h0) (e0 1 h1)
 have hq:=dn 14 D;have e1:=db 14 D;rw[hI,show ({0,1}:S0).card=2 from rfl] at e1;have hp:=dd hS b hb;obtain ⟨H,g4,ej,-⟩:=bp hG hS hC (x:=7) (y:=3) ((aK 7 3).1 rfl);have c1:H≠a0 0:=λl=>absurd (bx k h0 (l▸ej)) o;have ca:H≠a0 1:=λl=>absurd (bx k h1 (l▸ej)) o;have b5:(aM D,s)≠H:=λl=>by
  have e4:(3:F0)∈O 14 D (W D (aI H)):=(aP.1 ej).2.1;rw[← l,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at e4;exact nE _ e4
 have d2:({a0 0,a0 1,H,(aM D,s)}:Finset (A0))⊆aG 14 D 7:=by
  intro e l;simp only[mI,mS] at l;rcases l with rfl|rfl|rfl|rfl
  ·exact bd k h0 ((aK 0 7).1 rfl)
  ·exact bd k h1 ((aK 1 7).1 rfl)
  ·exact g4
  ·exact cV hD hT (a1 7 ((aK 0 7).1 rfl))
 have f2:=cL d2;have fz:a0 0≠a0 1:=λl=>absurd (k.2 0 h0 1 h1 l) o;rw[cI (by simp[fz,c1.symm,(cw k a2 h0).symm]),cI (by simp[ca.symm,(cw k a2 h1).symm]),cP b5.symm] at f2;have ho:=ci h hD b hb 7;have hf:(ru D b 7).card≤(aR 14 D b).card:=cF _ _;have m:∀u∈aR 14 D b,(7:F0)∈O 14 D u.1:=(by have hE:ru D b 7=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← hE] at hu;exact (bb.1 hu).2);have hh:(ru D b 2).card=0:=by
  by_contra f3;obtain ⟨u2,hd⟩:=cO.1 (nP f3);obtain ⟨fl,g1⟩:=bb.1 hd;have ec:=dl h hD b eb (p 7 o) {8,9,10,13,2} {3} ∅
   (λx hx=>by
    simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl
    ·exact ⟨p 8 o,o,λu hu _=>m u hu,_,a1 8 ((aK 0 8).1 rfl),a1 7 ((aK 0 7).1 rfl)⟩
    ·exact ⟨p 9 o,o,λu hu _=>m u hu,_,b8 9 ((aK 1 9).1 rfl),a1 7 ((aK 0 7).1 rfl)⟩
    ·exact ⟨p 10 o,o,λu hu _=>m u hu,_,a1 10 ((aK 0 10).1 rfl),a1 7 ((aK 0 7).1 rfl)⟩
    ·exact ⟨p 13 o,o,λu hu _=>m u hu,_,b8 13 ((aK 1 13).1 rfl),a1 7 ((aK 0 7).1 rfl)⟩
    ·exact ⟨p 2 o,o,λu hu _=>m u hu,u2.1,g1,m u2 fl⟩)
   (λn hn=>by rw[mS.1 hn];exact ⟨p 3 o,(aK 7 3).1 rfl,o⟩)
   (λ_ hz=>(nE _ hz).elim)
  rw[show ({8,9,10,13,2}:S0).card=5 from rfl,cS,ad] at ec;omega
 have ez:∀v i w1 w2:F0,i∈aN 14 D->v∉({0,1}:S0)->aH i v->aH v w1->aH v w2->w1≠i->w2≠i->w1∉({0,1}:S0)->w2∉({0,1}:S0)->w1≠w2->v∈O 14 D (W D (aM D,s))->v∈({8,13}:S0)->∃Z,aG 14 D v={a0 i,(aM D,s),Z}/\aI Z∈aG 14 D w1/\aI Z∈aG 14 D w2:=by
  intro v i w1 w2 hi hv g3 a7 b0 fi es c5 c6 ev e3 a3;have fc:(ru D b v).card≤1:=by
   by_contra hs;have hl:(ru D b v).card≤(aR 14 D b).card:=cF _ _;have c8:∀u∈aR 14 D b,v∈O 14 D u.1:=(by have hE:ru D b v=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← hE] at hu;exact (bb.1 hu).2);have ec:=dl h hD b eb (p v hv) (({7,8,9,10,13}:S0).erase v) {w1,w2} ∅
    (λx hx=>by
     obtain ⟨g0,f1⟩:=mE.1 hx;have a8:x∉({0,1}:S0)/\(aH 0 x\/aH 1 x):=(by decide +kernel:∀x∈({7,8,9,10,13}:S0),x∉({0,1}:S0)/\(aH 0 x\/aH 1 x)) x f1;refine ⟨p x a8.1,g0,λu hu _=>c8 u hu,W D (aM D,s),?_,e3⟩;rcases a8.2 with g7|hg
     ·exact a1 x g7
     ·exact b8 x hg)
    (λn hn=>by
     have r:w1∉({7,8,9,10,13}:S0)/\w2∉({7,8,9,10,13}:S0):=(by have:=(by decide +kernel:∀v∈({8,13}:S0),∀w:F0,aH v w->w∉({0,1}:S0)->w∉({7,8,9,10,13}:S0));exact ⟨this v a3 w1 a7 c5,this v a3 w2 b0 c6⟩);rcases mI.1 hn with e5|hn
     ·rw[e5];exact ⟨p w1 c5,a7,λhm=>r.1 (mO hm)⟩
     ·rw[mS.1 hn]
      exact ⟨p w2 c6,b0,λhm=>r.2 (mO hm)⟩)
    (λ_ hz=>(nE _ hz).elim)
   have gs:v∈({7,8,9,10,13}:S0):=(by have a4:=a3;simp only[mI,mS] at a4;rcases a4 with h1|h1<;>rw[h1]<;>decide);rw[cE gs,show ({7,8,9,10,13}:S0).card=5 from rfl,cP ev,ad] at ec;omega
  obtain ⟨Z,g6,d0,-⟩:=bp hG hS hC a7;have c0:Z≠a0 i:=λl=>fi (bx k hi (l▸d0));have bm:Z≠(aM D,s):=λl=>by
   have a6:w1∈O 14 D (W D (aI Z)):=(aP.1 d0).2.1;rw[l,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at a6;exact nE _ a6
  have c7:({a0 i,(aM D,s),Z}:Finset (A0))⊆aG 14 D v:=by
   intro e l;simp only[mI,mS] at l;rcases l with rfl|rfl|rfl
   ·exact bd k hi g3
   ·exact cV hD hT e3
   ·exact g6
  have hj:=ci h hD b hb v
  have c3:aG 14 D v={a0 i,(aM D,s),Z}:=(eS c7 (by
    rw[cI (by simp[(cw k a2 hi).symm,c0.symm]),cP bm.symm];omega)).symm
  obtain ⟨Z2,c2,b6,-⟩:=bp hG hS hC b0;have b2:Z2≠a0 i:=λl=>es (bx k hi (l▸b6));have a5:Z2≠(aM D,s):=λl=>by
   have a6:w2∈O 14 D (W D (aI Z2)):=(aP.1 b6).2.1;rw[l,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at a6;exact nE _ a6
  rw[c3,mI,mI,mS] at c2;have er:Z2=Z:=(c2.resolve_left b2).resolve_left a5;exact ⟨Z,c3,d0,er▸b6⟩
 obtain ⟨Z8,g5,ea,d1⟩:=ez 8 0 2 6 h0 o ((aK 0 8).1 rfl)
  ((aK 8 2).1 rfl) ((aK 8 6).1 rfl) o o
  o o o (a1 8 ((aK 0 8).1 rfl)) o
 obtain ⟨Z13,e7,cb,ct⟩:=ez 13 1 2 4 h1 o ((aK 1 13).1 rfl)
  ((aK 13 2).1 rfl) ((aK 13 4).1 rfl) o o
  o o o (b8 13 ((aK 1 13).1 rfl)) o
 have eu:aI Z8≠aI Z13:=λl=>by
  have et:Z8=Z13:=(by rw[← aT Z8,l,aT]);have e2:(13:F0)∈O 14 D (W D Z8):=(by rw[et];exact (aP.1 (by rw[e7];simp)).2.1);obtain ⟨e,b1,h7,g8⟩:=bB h hD (x:=8) (a:=7) (b:=13)
   o o (bw.1 rfl)
  rw[g5,mI,mI,mS] at b1;rcases b1 with rfl|rfl|rfl
  ·exact h7 ((k.1 0 h0).2.2.1 7 ((aK 0 7).1 rfl))
  ·exact h7 (a1 7 ((aK 0 7).1 rfl))
  ·exact g8 e2
 have hk:=ci h hD b hb 2
 have g2:({aI Z8,aI Z13}:Finset (A0))=aG 14 D 2:=eS (λe l=>by
   rcases mI.1 l with rfl|l
   ·exact ea
   ·rw[mS.1 l];exact cb) (by rw[cP eu];omega)
 obtain ⟨e,b1,h6,h4⟩:=bB h hD (x:=2) (a:=6) (b:=4)
  o o (bw.1 rfl)
 rw[← g2,mI,mS] at b1;rcases b1 with rfl|rfl
 ·exact h6 (aP.1 d1).2.1
 ·exact h4 (aP.1 ct).2.1
lemma oY {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(f2:bH 14 D≤14)(e0:bu 14 D=0)(hI:aN 14 D={0,9}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,er⟩:=dB hG hS hC;have hb:=cX er;obtain ⟨a2,l⟩:=cR hG h hC;have h0:(0:F0)∈aN 14 D:=by rw[hI];decide
 have h9:(9:F0)∈aN 14 D:=by rw[hI];decide
 have a0:∀x:F0,x∉({0,9}:S0)->x∈aW 14 D:=λx hx=>
  ai.1 (λhc=>hx (hI▸cl.2 hc))
 have ec:∀i:F0,i∈aN 14 D->aU 14 D i.val (aO 14 D):=λi hi=>by
  rcases cr hG h hC hi with hc|⟨z,-,e7,e5⟩
  ·exact hc
  ·exact (nN (e5▸eB hS e0 e7)).elim
 obtain ⟨s,a1,ct,c8,-⟩:=dj h hD hT (by decide:(0:F0)≠9) h0 h9
  (ec 0 h0) (ec 9 h9)
 have f1:=dn 14 D;have ej:=db 14 D;rw[hI,show ({0,9}:S0).card=2 from rfl] at ej;have f0:=dd hS b hb;have eb:∀v i w1 w2:F0,i∈aN 14 D->v∉({0,9}:S0)->aH i v->aH v w1->aH v w2->w1≠i->w2≠i->w1∉({0,9}:S0)->w2∉({0,9}:S0)->w1≠w2->v∈O 14 D (W D (aM D,s))->v∈({8,6}:S0)->∃Z,aG 14 D v={a2 i,(aM D,s),Z}/\aI Z∈aG 14 D w1/\aI Z∈aG 14 D w2:=by
  intro v i w1 w2 hi hv e1 a5 b0 ev d1 c2 c3 ea bm b2;have et:(ru D b v).card≤1:=by
   by_contra f3;have fz:(ru D b v).card≤(aR 14 D b).card:=cF _ _;have m:∀u∈aR 14 D b,v∈O 14 D u.1:=(by have hE:ru D b v=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← hE] at hu;exact (bb.1 hu).2);have e3:=dl h hD b er (a0 v hv) {7,10,1,5} {w1,w2} ∅
    (λx hx=>by
     simp only[mI,mS] at hx;have b8:x≠v:=(by have a7:=b2;simp only[mI,mS] at a7;rcases a7 with h1|h1<;>rw[h1]<;>rcases hx with rfl|rfl|rfl|rfl<;>decide);rcases hx with rfl|rfl|rfl|rfl
     ·exact ⟨a0 7 o,b8,λu hu _=>m u hu,_,ct 7 ((aK 0 7).1 rfl),bm⟩
     ·exact ⟨a0 10 o,b8,λu hu _=>m u hu,_,ct 10 ((aK 0 10).1 rfl),bm⟩
     ·exact ⟨a0 1 o,b8,λu hu _=>m u hu,_,c8 1 ((aK 9 1).1 rfl),bm⟩
     ·exact ⟨a0 5 o,b8,λu hu _=>m u hu,_,c8 5 ((aK 9 5).1 rfl),bm⟩)
    (λn hn=>by
     have r:w1∉({7,10,1,5}:S0)/\w2∉({7,10,1,5}:S0):=(by have:=(by decide +kernel:∀v∈({8,6}:S0),∀w:F0,aH v w->w∉({0,9}:S0)->w∉({7,10,1,5}:S0));exact ⟨this v b2 w1 a5 c2,this v b2 w2 b0 c3⟩);rcases mI.1 hn with es|hn
     ·rw[es];exact ⟨a0 w1 c2,a5,r.1⟩
     ·rw[mS.1 hn];exact ⟨a0 w2 c3,b0,r.2⟩)
    (λ_ hz=>(nE _ hz).elim)
   rw[show ({7,10,1,5}:S0).card=4 from rfl,cP ea,ad] at e3;omega
  obtain ⟨Z,e2,c6,-⟩:=bp hG hS hC a5;have ca:Z≠a2 i:=λhe=>ev (bx l hi (he▸c6));have a8:Z≠(aM D,s):=λhe=>by
   have a4:w1∈O 14 D (W D (aI Z)):=(aP.1 c6).2.1;rw[he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a1] at a4;exact nE _ a4
  have c5:({a2 i,(aM D,s),Z}:Finset (A0))⊆aG 14 D v:=by
   intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
   ·exact bd l hi e1
   ·exact cV hD hT bm
   ·exact e2
  have fl:=ci h hD b hb v
  have c1:aG 14 D v={a2 i,(aM D,s),Z}:=(eS c5 (by
    rw[cI (by simp[(cw l a1 hi).symm,ca.symm]),cP a8.symm];omega)).symm
  obtain ⟨Z2,c0,b5,-⟩:=bp hG hS hC b0;have b1:Z2≠a2 i:=λhe=>d1 (bx l hi (he▸b5));have a3:Z2≠(aM D,s):=λhe=>by
   have a4:w2∈O 14 D (W D (aI Z2)):=(aP.1 b5).2.1;rw[he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a1] at a4;exact nE _ a4
  rw[c1,mI,mI,mS] at c0;have d0:Z2=Z:=(c0.resolve_left b1).resolve_left a3;exact ⟨Z,c1,c6,d0▸b5⟩
 obtain ⟨Z8,c7,-,a6⟩:=eb 8 0 2 6 h0 o ((aK 0 8).1 rfl)
  ((aK 8 2).1 rfl) ((aK 8 6).1 rfl) o o
  o o o (ct 8 ((aK 0 8).1 rfl)) o
 obtain ⟨Z6,fi,e4,b6⟩:=eb 6 9 8 11 h9 o ((aK 9 6).1 rfl)
  ((aK 6 8).1 rfl) ((aK 6 11).1 rfl) o o
  o o o (c8 6 ((aK 9 6).1 rfl)) o
 have p:aI Z8≠a2 9:=λhe=>
  absurd (bx l h9 (by rw[← he,aT];exact by rw[c7];simp)) o
 have k:aI Z8≠(aM D,s):=λhe=>by
  have ez:(8:F0)∈O 14 D (W D Z8):=(aP.1 (by rw[c7];simp)).2.1
  have:W D (aI (aM D,s))=W D Z8:=by rw[← he,aT]
  rw[← this,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a1] at ez;exact nE _ ez
 rw[fi,mI,mI,mS] at a6;have d2:aI Z8=Z6:=(a6.resolve_left p).resolve_left k;have cb:(11:F0)∈O 14 D (W D Z8):=(by have:=(aP.1 b6).2.1;rwa[← d2,aT] at this);obtain ⟨e,eu,h7,fc⟩:=bB h hD (x:=8) (a:=7) (b:=11)
  o o (bw.1 rfl)
 rw[c7,mI,mI,mS] at eu;rcases eu with rfl|rfl|rfl
 ·exact h7 ((l.1 0 h0).2.2.1 7 ((aK 0 7).1 rfl))
 ·exact h7 (ct 7 ((aK 0 7).1 rfl))
 ·exact fc cb
def cC:S0:={3,4,6,7,8,9,10,13}
lemma gy:∀v∈cC,v∉({0,1,11}:S0)/\(aH 0 v\/aH 1 v\/aH 11 v)/\∃i∈({0,1,11}:S0),aH i v/\∃w:F0,aH v w/\w≠i/\w∉({0,1,11}:S0):=aa
lemma mw:∀i∈({0,1,11}:S0),∀u∈cC,∀v∈cC,aH i u->¬aH i v->u≠v->∃a:F0,aH i a/\a≠u/\a≠v/\¬aH a v:=aa
lemma m4:∀u∈({4,6}:S0),∀v∈({8,9,10,13}:S0),aH u v->∃i∈({0,1}:S0),∃v2 w2:F0,aH i v/\aH u v2/\v2≠v/\v2≠11/\¬aH 7 v2/\aH v w2/\w2≠i/\w2≠u/\v2≠w2/\v≠7/\v2≠7:=aa
set_option maxHeartbeats 400000 in
lemma px {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(qP:bH 14 D≤14)(qj:bu 14 D=0)(hI:aN 14 D={0,1,11}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,ja⟩:=dB hG hS hC;have hb:=cX ja;obtain ⟨a0,k⟩:=cR hG h hC;have b8:∀i∈({0,1,11}:S0),i∈aN 14 D:=by rw[hI];exact λ_ hi=>hi
 have h0:=b8 0 o;have l:=b8 1 o;have ct:=b8 11 o
 have e7:∀x:F0,x∉({0,1,11}:S0)->x∈aW 14 D:=λx hx=>
  ai.1 (λhc=>hx (hI▸cl.2 hc))
 have ez:∀i:F0,i∈aN 14 D->aU 14 D i.val (aO 14 D):=λi hi=>by
  rcases cr hG h hC hi with hc|⟨z,-,qe,qv⟩
  ·exact hc
  ·exact (nN (qv▸eB hS qj qe)).elim
 obtain ⟨s,a2,qf,iz,-⟩:=dj h hD hT (by decide:(0:F0)≠1) h0 l
  (ez 0 h0) (ez 1 l)
 have ls:∀a:F0,aH 11 a->a∈O 14 D (W D (aM D,s)):=by
  obtain ⟨s',qs,p0,i7,-⟩:=dj h hD hT (by decide:(0:F0)≠11) h0 ct
   (ez 0 h0) (ez 11 ct)
  have qu:s'=s:=by
   by_contra ca;have qb:s'=!s:=by cases s'<;>cases s<;>simp_all
   have oz:=p0 7 ((aK 0 7).1 rfl);rw[qb,a2] at oz;exact nE _ oz
  subst qu;exact i7
 have a3:∀v∈cC,v∈O 14 D (W D (aM D,s)):=λv hv=>by
  rcases (gy v hv).2.1 with c6|fz|mt
  ·exact qf v c6
  ·exact iz v fz
  ·exact ls v mt
 have qW:=dn 14 D;have n8:=db 14 D;rw[hI,show ({0,1,11}:S0).card=3 from rfl] at n8;have qO:=dd hS b hb;have a6:∀v∈cC,1≤(ru D b v).card/\(ru D b v).card≤2:=by
  intro v hv;obtain ⟨lo,-,i,hi,h6,w,qx,qy,-⟩:=gy v hv;obtain ⟨F,qn,m3,-⟩:=bp hG hS hC qx;have hM:F≠a0 i:=λhe=>qy (bx k (b8 i hi) (he▸m3));have g8:F≠(aM D,s):=λhe=>by
   have lb:w∈O 14 D (W D (aI F)):=(aP.1 m3).2.1;rw[he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at lb;exact nE _ lb
  have hX:({a0 i,(aM D,s),F}:Finset (A0))⊆aG 14 D v:=by
   intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
   ·exact bd k (b8 i hi) h6
   ·exact cV hD hT (a3 v hv)
   ·exact qn
  have h3:=cL hX;rw[cI (by simp[(cw k a2 (b8 i hi)).symm,hM.symm]),cP g8.symm] at h3;have qV:=ci h hD b hb v;refine ⟨Y,?_⟩;by_contra qX;have qJ:(ru D b v).card≤(aR 14 D b).card:=cF _ _;have i0:∀u∈aR 14 D b,v∈O 14 D u.1:=(by have hE:ru D b v=aR 14 D b:=eS (fS _ _) Y;intro u hu;rw[← hE] at hu;exact (bb.1 hu).2);have jb:=dl h hD b ja (e7 v lo) (cC.erase v) ∅ ∅
   (λx hx=>by
    obtain ⟨qq,g0⟩:=mE.1 hx
    exact ⟨e7 x (gy x g0).1,qq,λu hu _=>i0 u hu,_,a3 x g0,a3 v hv⟩)
   (λ_ hn=>(nE _ hn).elim)
   (λ_ hz=>(nE _ hz).elim)
  rw[cE hv,show cC.card=8 from rfl,ad] at jb;omega
 obtain ⟨H,h7,hB,-⟩:=bp hG hS hC (x:=7) (y:=3) ((aK 7 3).1 rfl);have ec:H≠a0 0:=λhe=>absurd (bx k h0 (he▸hB)) o;have d0:H≠a0 1:=λhe=>absurd (bx k l (he▸hB)) o;have et:(aM D,s)≠H:=λhe=>by
  have m1:(3:F0)∈O 14 D (W D (aI H)):=(aP.1 hB).2.1;rw[← he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at m1;exact nE _ m1
 have d1:({a0 0,a0 1,H,(aM D,s)}:Finset (A0))⊆aG 14 D 7:=by
  intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl|rfl
  ·exact bd k h0 ((aK 0 7).1 rfl)
  ·exact bd k l ((aK 1 7).1 rfl)
  ·exact h7
  ·exact cV hD hT (a3 7 o)
 have hA:a0 0≠a0 1:=λhe=>absurd (k.2 0 h0 1 l he) o;have ql:=cL d1;rw[cI (by simp[hA,ec.symm,(cw k a2 h0).symm]),cI (by simp[d0.symm,(cw k a2 l).symm]),cP et.symm] at ql;have qG:=ci h hD b hb 7;have p3:=(a6 7 o).2;have qN:(ru D b 7).card=2:=Y
 have hO:aG 14 D 7={a0 0,a0 1,H,(aM D,s)}:=(eS d1 (by
   rw[cI (by simp[hA,ec.symm,(cw k a2 h0).symm]),cI (by simp[d0.symm,(cw k a2 l).symm]),cP et.symm];omega)).symm
 have a7:∀t∈cC,t∈O 14 D (W D (a0 0))->aH 0 t:=λt ht hts=>
  ib h hD hT k h0 ((aK 0 7).1 rfl) (ez 0 h0) a2 (a3 7 o)
   (λp hp hp1 hp26 a1=>by
    rw[hO,mI,mI,mI,mS] at hp;rcases hp with rfl|rfl|rfl|rfl
    ·exact hp1 rfl
    ·exact absurd (singleton_subset_singleton.1 ((k.1 1 l).2.2.2.symm.subset.trans a1)) o
    ·exact absurd (mS.1 (a1 (aP.1 hB).2.1)) o
    ·exact hp26 rfl) t (a3 t ht) hts
 have a8:∀t∈cC,t∈O 14 D (W D (a0 1))->aH 1 t:=λt ht hts=>
  ib h hD hT k l ((aK 1 7).1 rfl) (ez 1 l) a2 (a3 7 o)
   (λp hp hp1 hp26 a1=>by
    rw[hO,mI,mI,mI,mS] at hp;rcases hp with rfl|rfl|rfl|rfl
    ·exact absurd (singleton_subset_singleton.1 ((k.1 0 h0).2.2.2.symm.subset.trans a1)) o
    ·exact hp1 rfl
    ·exact absurd (mS.1 (a1 (aP.1 hB).2.1)) o
    ·exact hp26 rfl) t (a3 t ht) hts
 have a4:∀i∈({0,1,11}:S0),(∀t∈cC,t∈O 14 D (W D (a0 i))->aH i t)->∀u∈cC,∀v∈cC,aH i u->¬aH i v->u≠v->¬ru D b u⊆ru D b v:=by
  intro i hi qi u hu v hv pb hW g3 a1;obtain ⟨r0,hy⟩:=cO.1 (show 0<(ru D b u).card by have:=(a6 u hu).1;omega);obtain ⟨e0,ea⟩:=ek hG h hC b hb g3 (e7 u (gy u hu).1)
   (λr hr hur=>(bb.1 (a1 (bb.2 ⟨hr,hur⟩))).2)
   ⟨(bb.1 hy).2,(bb.1 (a1 hy)).2⟩
  have pa:a0 i=e0:=(by by_contra ca;exact hW (qi v hv (ea _ (bd k (b8 i hi) pb) ca)));obtain ⟨a,qg,qo,qQ,p2⟩:=mw i hi u hu v hv pb hW g3;obtain ⟨e,c7,qz,a5⟩:=bB h hD (nS qo) g3 p2;by_cases he:e=e0
  ·exact qz (by rw[he,← pa];exact (k.1 i (b8 i hi)).2.2.1 a qg)
  ·exact a5 (ea e c7 he)
 have h4:∀v∈cC,v≠7->¬ru D b 7⊆ru D b v:=by
  intro v hv c5 a1;obtain ⟨r0,hy⟩:=cO.1 (show 0<(ru D b 7).card by omega);obtain ⟨e0,ea⟩:=ek hG h hC b hb (nS c5) (e7 7 o)
   (λr hr h7r=>(bb.1 (a1 (bb.2 ⟨hr,h7r⟩))).2)
   ⟨(bb.1 hy).2,(bb.1 (a1 hy)).2⟩
  by_cases c6:aH 0 v
  ·have n4:¬aH 1 v:=by
    have a5:=hv;simp only[cC,mI,mS] at a5;rcases a5 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>revert c6 c5<;>decide
   have g9:a0 1=e0:=(by by_contra ca;exact n4 (a8 v hv (ea _ (bd k l ((aK 1 7).1 rfl)) ca)));have id:v∈O 14 D (W D H):=ea H h7 (λhc=>d0 (hc.trans g9.symm));obtain ⟨e,c7,h9,a5⟩:=bB h hD (x:=7) (a:=9) (b:=v)
    o (nS c5) (by
     have a5:=hv;simp only[cC,mI,mS] at a5
     rcases a5 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>revert c6 c5<;>decide)
   rw[hO,mI,mI,mI,mS] at c7;rcases c7 with rfl|rfl|rfl|rfl
   ·exact a5 ((k.1 0 h0).2.2.1 v c6)
   ·exact h9 ((k.1 1 l).2.2.1 9 ((aK 1 9).1 rfl))
   ·exact a5 id
   ·exact a5 (a3 v hv)
  ·by_cases fz:aH 1 v
   ·have hF:a0 0=e0:=by
     by_contra ca;exact c6 (a7 v hv (ea _ (bd k h0 ((aK 0 7).1 rfl)) ca))
    have id:v∈O 14 D (W D H):=ea H h7 (λhc=>ec (hc.trans hF.symm));obtain ⟨e,c7,h8,a5⟩:=bB h hD (x:=7) (a:=8) (b:=v)
     o (nS c5) (by
      have a5:=hv;simp only[cC,mI,mS] at a5
      rcases a5 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>revert fz c5<;>decide)
    rw[hO,mI,mI,mI,mS] at c7;rcases c7 with rfl|rfl|rfl|rfl
    ·exact h8 ((k.1 0 h0).2.2.1 8 ((aK 0 8).1 rfl))
    ·exact a5 ((k.1 1 l).2.2.1 v fz)
    ·exact a5 id
    ·exact a5 (a3 v hv)
   ·have hF:a0 0=e0:=by
     by_contra ca;exact c6 (a7 v hv (ea _ (bd k h0 ((aK 0 7).1 rfl)) ca))
    have g9:a0 1=e0:=(by by_contra ca;exact fz (a8 v hv (ea _ (bd k l ((aK 1 7).1 rfl)) ca)));exact hA (hF.trans g9.symm)
 have qS:(aR 14 D b).card=3:=by
  have qE:2≤(aR 14 D b).card:=by
   have:(ru D b 7).card≤(aR 14 D b).card:=cF _ _
   omega
  by_contra ca;have qU:(aR 14 D b).card=2:=Y
  have k3:ru D b 7=aR 14 D b:=eS (fS _ _) Y;have jb:=dl h hD b ja (e7 7 o) {8,9,10,13,4,6} {3} ∅
   (λx hx=>by
    have g0:x∈cC/\x≠7:=(by simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl|rfl<;>decide)
    exact ⟨e7 x (gy x g0.1).1,g0.2,λu hu _=>(bb.1 (k3▸hu)).2,_,a3 x g0.1,a3 7 o⟩)
   (λn hn=>by rw[mS.1 hn];exact ⟨e7 3 o,(aK 7 3).1 rfl,o⟩)
   (λ_ hz=>(nE _ hz).elim)
  rw[show ({8,9,10,13,4,6}:S0).card=6 from rfl,cS,ad] at jb;omega
 obtain ⟨u0,hk,u1,hj,hQ⟩:=oC.1 (show 1<(ru D b 7).card by omega)
 have n7:ru D b 7={u0,u1}:=(eS (λu hu=>by
   rcases mI.1 hu with rfl|hu
   ·exact hk
   ·rw[mS.1 hu];exact hj) (by rw[cP hQ];omega)).symm
 have hP:(aR 14 D b \ ru D b 7).card=1:=(by have:=sP (fS (λu:P0=>(7:F0)∈O 14 D u.1) (aR 14 D b));change (aR 14 D b \ ru D b 7).card+(ru D b 7).card=(aR 14 D b).card at this;omega);obtain ⟨u2,qw⟩:=ac.1 hP;have l0:u2∈aR 14 D b \ ru D b 7:=by rw[qw];simp
 obtain ⟨lw,eb⟩:=mD.1 l0;have c1:aR 14 D b={u0,u1,u2}:=by
  have a1:({u0,u1,u2}:Finset (P0))⊆aR 14 D b:=by
   intro u hu;simp only[mI,mS] at hu;rcases hu with rfl|rfl|rfl
   ·exact (bb.1 hk).1
   ·exact (bb.1 hj).1
   ·exact lw
  have k0:u0≠u2:=λhe=>eb (he▸hk);have ih:u1≠u2:=λhe=>eb (he▸hj)
  exact (eS a1 (by
   rw[cI (by simp[hQ,k0]),cP ih];omega)).symm
 have b2:∀v∈cC,v≠7->(ru D b v).card=2->ru D b v={u0,u2}\/ru D b v={u1,u2}:=by
  intro v hv c5 h2;have a1:ru D b v⊆{u0,u1,u2}:=by rw[← c1];exact fS _ _
  have hU:u2∈ru D b v:=by
   by_contra qp;have d1:ru D b v⊆ru D b 7:=λu hu=>by
    have:=a1 hu;simp only[mI,mS] at this;rcases this with rfl|rfl|rfl
    ·exact hk
    ·exact hj
    ·exact (qp hu).elim
   have qm:=eS d1 Y;exact h4 v hv c5 (qm▸Subset.refl _)
  have k0:u0≠u2:=λhe=>eb (he▸hk);have ih:u1≠u2:=λhe=>eb (he▸hj);by_cases c6:u0∈ru D b v
  ·left
   exact (eS (λu hu=>by
    rcases mI.1 hu with rfl|hu
    ·exact c6
    ·rw[mS.1 hu];exact hU) (by rw[cP k0];omega)).symm
  ·right;have fz:u1∈ru D b v:=by
    by_contra iz
    have:ru D b v⊆{u2}:=λu hu=>by
     have:=a1 hu;simp only[mI,mS] at this;rcases this with rfl|rfl|rfl
     ·exact (c6 hu).elim
     ·exact (iz hu).elim
     ·simp
    have:=cL this;rw[cS] at this;omega
   exact (eS (λu hu=>by
    rcases mI.1 hu with rfl|hu
    ·exact fz
    ·rw[mS.1 hu];exact hU) (by rw[cP ih];omega)).symm
 have e2:∀u∈({4,6}:S0),(ru D b u).card=1->False:=by
  intro u hu n1;have ho:u∈cC:=(by have b1:=hu;simp only[mI,mS] at b1;rcases b1 with l|l<;>rw[l]<;>decide);have c8:∀v∈({8,9,10,13}:S0),aH u v->(ru D b v).card=2:=by
   intro v hv g3;obtain ⟨i,hi,v2,w2,h6,m2,nl,k2,ko,qM,qA,qK,-,c5,qB⟩:=m4 u hu v hv g3;have n2:v∈cC:=(by have a5:=hv;simp only[mI,mS] at a5;rcases a5 with l|l|l|l<;>rw[l]<;>decide);have qI:=a6 v n2;by_contra qF;have qT:(ru D b v).card=1:=Y
   obtain ⟨Fu,er,c2,-⟩:=bp hG hS hC g3;have b5:Fu≠a0 11:=λhe=>by
    have:=bx k ct (he▸c2);have a5:=hv;simp only[mI,mS] at a5;rcases a5 with l|l|l|l<;>rw[l] at this<;>exact absurd this o
   have b6:Fu≠(aM D,s):=λhe=>by
    have es:=(aP.1 c2).2.1;rw[he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at es;exact nE _ es
   have e1:({a0 11,(aM D,s),Fu}:Finset (A0))⊆aG 14 D u:=by
    intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
    ·exact bd k ct (by
      have b1:=hu;simp only[mI,mS] at b1
      rcases b1 with l|l<;>rw[l]<;>exact (aK _ _).1 rfl)
    ·exact cV hD hT (a3 u ho)
    ·exact er
   have p1:=ci h hD b hb u
   have iy:aG 14 D u={a0 11,(aM D,s),Fu}:=(eS e1 (by
     rw[cI (by simp[(cw k a2 ct).symm,b5.symm]),cP b6.symm];omega)).symm
   obtain ⟨Fu2,hw,e4,-⟩:=bp hG hS hC m2;have fl:Fu2≠a0 11:=λhe=>k2 (bx k ct (he▸e4));have eu:Fu2≠(aM D,s):=λhe=>by
    have es:=(aP.1 e4).2.1;rw[he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at es;exact nE _ es
   rw[iy,mI,mI,mS] at hw;have hK:Fu2=Fu:=(hw.resolve_left fl).resolve_left eu;have hd:v2∈O 14 D (W D (aI Fu)):=(aP.1 (hK▸e4)).2.1;have hH:aI Fu≠a0 i:=λhe=>by
    have:=bx k (b8 i (by
     have c0:=hi;simp only[mI,mS] at c0
     rcases c0 with l|l<;>rw[l]<;>decide)) (by rw[← he,aT];exact er)
    have b1:=hu;simp only[mI,mS] at b1;have c0:=hi;simp only[mI,mS] at c0;rcases b1 with l|l<;>rcases c0 with h2|h2<;>rw[l,h2] at this<;>exact absurd this o
   have g2:aI Fu≠(aM D,s):=λhe=>by
    have m8:u∈O 14 D (W D Fu):=(aP.1 er).2.1
    have:W D (aI (aM D,s))=W D Fu:=by rw[← he,aT]
    rw[← this,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at m8;exact nE _ m8
   have hJ:i∈({0,1,11}:S0):=(by have c0:=hi;simp only[mI,mS] at c0;rcases c0 with l|l<;>rw[l]<;>decide);have ix:({a0 i,(aM D,s),aI Fu}:Finset (A0))⊆aG 14 D v:=by
    intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
    ·exact bd k (b8 i hJ) h6
    ·exact cV hD hT (a3 v n2)
    ·exact c2
   have qC:=ci h hD b hb v
   have qr:aG 14 D v={a0 i,(aM D,s),aI Fu}:=(eS ix (by
     rw[cI (by simp[(cw k a2 (b8 i hJ)).symm,hH.symm]),cP g2.symm];omega)).symm
   obtain ⟨e,c7,n5,n3⟩:=bB h hD c5 (nS nl) ko;rw[qr,mI,mI,mS] at c7;rcases c7 with rfl|rfl|rfl
   ·exact n5 ((k.1 i (b8 i hJ)).2.2.1 7 (by
     have c0:=hi;simp only[mI,mS] at c0
     rcases c0 with l|l<;>rw[l]<;>exact (aK _ _).1 rfl))
   ·exact n5 (a3 7 o)
   ·exact n3 hd
  obtain ⟨va,fi,vb,g5,e3,g7,g6,f2⟩ :
    ∃va∈({8,9,10,13}:S0),∃vb∈({8,9,10,13}:S0),
    aH u va/\aH u vb/\aH 0 va/\aH 1 vb:=by
   have b1:=hu;simp only[mI,mS] at b1;rcases b1 with l|l<;>rw[l]
   ·exact ⟨10,o,13,o,(aK 4 10).1 rfl,(aK 4 13).1 rfl,(aK 0 10).1 rfl,(aK 1 13).1 rfl⟩
   ·exact ⟨8,o,9,o,(aK 6 8).1 rfl,(aK 6 9).1 rfl,(aK 0 8).1 rfl,(aK 1 9).1 rfl⟩
  have hl:va∈cC:=(by have h':=fi;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l]<;>decide);have hf:vb∈cC:=(by have h':=g5;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l]<;>decide);have pr:va≠7:=(by have h':=fi;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l]<;>decide);have nR:vb≠7:=(by have h':=g5;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l]<;>decide);have ev:va≠vb:=λhe=>by
   have h':=fi;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l] at g6<;>rw[← he,l] at f2<;>revert g6 f2<;>decide
  have hY:¬aH 0 vb:=λhh=>by
   have h':=g5;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l] at hh f2<;>revert hh f2<;>decide
  have f0:ru D b va≠ru D b vb:=λhe=>
   a4 0 o a7 va hl vb hf g6 hY ev (he▸Subset.refl _)
  have qk:=b2 va hl pr (c8 va fi e3);have p9:=b2 vb hf nR (c8 vb g5 g7);have hL:∀x∈({u0,u1,u2}:Finset (P0)),x∈ru D b va\/x∈ru D b vb:=by
   intro x hx;simp only[mI,mS] at hx;rcases qk with ha|ha<;>rcases p9 with hg|hg
   ·exact (f0 (ha.trans hg.symm)).elim
   ·rw[ha,hg];rcases hx with rfl|rfl|rfl<;>simp
   ·rw[ha,hg];rcases hx with rfl|rfl|rfl<;>simp
   ·exact (f0 (ha.trans hg.symm)).elim
  obtain ⟨Fu,er,c2,-⟩:=bp hG hS hC e3;have b5:Fu≠a0 11:=λhe=>by
   have:=bx k ct (he▸c2);have h':=fi;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l] at this<;>exact absurd this o
  have b6:Fu≠(aM D,s):=λhe=>by
   have es:=(aP.1 c2).2.1;rw[he,show W D (aI (aM D,s))=W D (aM D,!s) from rfl,a2] at es;exact nE _ es
  have gs:aH 11 u:=(by have b1:=hu;simp only[mI,mS] at b1;rcases b1 with l|l<;>rw[l]<;>exact (aK _ _).1 rfl);have e1:({a0 11,(aM D,s),Fu}:Finset (A0))⊆aG 14 D u:=by
   intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
   ·exact bd k ct gs
   ·exact cV hD hT (a3 u ho)
   ·exact er
  have p1:=ci h hD b hb u
  have iy:aG 14 D u={a0 11,(aM D,s),Fu}:=(eS e1 (by
    rw[cI (by simp[(cw k a2 ct).symm,b5.symm]),cP b6.symm];omega)).symm
  have c3:∀t∈cC,t∈O 14 D (W D (a0 11))->aH 11 t:=λt ht hts=>
   ib h hD hT k ct gs (ez 11 ct) a2 (a3 u ho)
    (λp hp hp1 hp26 a1=>by
     rw[iy,mI,mI,mS] at hp;rcases hp with rfl|rfl|rfl
     ·exact hp1 rfl
     ·exact hp26 rfl
     ·have f1:va=11:=mS.1 (a1 (aP.1 c2).2.1);have h':=fi;simp only[mI,mS] at h'
      rcases h' with l|l|l|l<;>rw[l] at f1<;>exact absurd f1 o)
    t (a3 t ht) hts
  obtain ⟨hq,fc⟩:=ac.1 n1;have qa:hq∈ru D b u:=by rw[fc];simp
  have g4:hq∈({u0,u1,u2}:Finset (P0)):=c1▸(bb.1 qa).1;have la:=hL hq g4;have k1:¬aH 11 va:=(by have h':=fi;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l]<;>decide);have hZ:¬aH 11 vb:=(by have h':=g5;simp only[mI,mS] at h';rcases h' with l|l|l|l<;>rw[l]<;>decide);have l4:u≠va:=λhe=>bW u (he▸e3);have lc:u≠vb:=λhe=>bW u (he▸g7);rcases la with qh|p6
  ·exact a4 11 o c3 u ho va hl gs k1 l4 (by
    rw[fc,sS];exact qh)
  ·exact a4 11 o c3 u ho vb hf gs hZ lc (by
    rw[fc,sS];exact p6)
 have qd:(ru D b 4).card=2:=(by have:=a6 4 o;by_contra ca;exact e2 4 o Y);have i4:=b2 4 o o qd;have b0:¬ru D b 8⊆ru D b 4:=a4 0 o a7 8 o 4 o ((aK 0 8).1 rfl) (bw.1 rfl) o;have hN:¬ru D b 8⊆ru D b 9:=a4 0 o a7 8 o 9 o ((aK 0 8).1 rfl) (bw.1 rfl) o;have cb:¬ru D b 9⊆ru D b 4:=a4 1 o a8 9 o 4 o ((aK 1 9).1 rfl) (bw.1 rfl) o;have ej:¬ru D b 9⊆ru D b 8:=a4 1 o a8 9 o 8 o ((aK 1 9).1 rfl) (bw.1 rfl) o;have qD:=a6 8 o;have qH:=a6 9 o;by_cases qc:(ru D b 8).card=2
 ·have h5:=b2 8 o o qc;have i3:∀x∈({u0,u1,u2}:Finset (P0)),x∈ru D b 4\/x∈ru D b 8:=by
   intro x hx;simp only[mI,mS] at hx;rcases i4 with bm|bm<;>rcases h5 with d2|d2
   ·exact (b0 (by rw[bm,d2])).elim
   ·rw[bm,d2];rcases hx with rfl|rfl|rfl<;>simp
   ·rw[bm,d2];rcases hx with rfl|rfl|rfl<;>simp
   ·exact (b0 (by rw[bm,d2])).elim
  by_cases p8:(ru D b 9).card=2
  ·have l7:=b2 9 o o p8;rcases i4 with bm|bm
   ·have d2:ru D b 8={u1,u2}:=h5.resolve_left (λhh=>b0 (by rw[hh,bm]));rcases l7 with e5|e5
    ·exact cb (by rw[e5,bm])
    ·exact ej (by rw[e5,d2])
   ·have d2:ru D b 8={u0,u2}:=h5.resolve_right (λhh=>b0 (by rw[hh,bm]));rcases l7 with e5|e5
    ·exact ej (by rw[e5,d2])
    ·exact cb (by rw[e5,bm])
  ·obtain ⟨x9,i5⟩:=ac.1 (show (ru D b 9).card=1 by omega);have l3:x9∈ru D b 9:=by rw[i5];simp
   have nB:x9∈({u0,u1,u2}:Finset (P0)):=c1▸(bb.1 l3).1;rcases i3 x9 nB with qt|p7
   ·exact cb (by rw[i5,sS];exact qt)
   ·exact ej (by rw[i5,sS];exact p7)
 ·obtain ⟨x8,ik⟩:=ac.1 (show (ru D b 8).card=1 by omega);have ll:x8∈ru D b 8:=by rw[ik];simp
  have f3:x8∈({u0,u1,u2}:Finset (P0)):=c1▸(bb.1 ll).1;have m:x8∉ru D b 4:=λhm=>b0 (by rw[ik,sS];exact hm);have g1:x8∉ru D b 9:=λhm=>hN (by rw[ik,sS];exact hm);have hs:ru D b 9⊆ru D b 4:=by
   intro x hx;have g4:x∈({u0,u1,u2}:Finset (P0)):=c1▸(bb.1 hx).1;have hR:x≠x8:=λhe=>g1 (he▸hx);rcases i4 with bm|bm
   ·rw[bm] at m ⊢;simp only[mI,mS] at g4 f3 m ⊢
    push_neg at m
    rcases f3 with ks|k7|j0
    ·exact (m.1 ks).elim
    ·rcases g4 with rfl|rfl|rfl
     ·exact oL rfl
     ·exact (hR k7.symm).elim
     ·exact oR rfl
    ·exact (m.2 j0).elim
   ·rw[bm] at m ⊢;simp only[mI,mS] at g4 f3 m ⊢
    push_neg at m
    rcases f3 with ks|k7|j0
    ·rcases g4 with rfl|rfl|rfl
     ·exact (hR ks.symm).elim
     ·exact oL rfl
     ·exact oR rfl
    ·exact (m.1 k7).elim
    ·exact (m.2 j0).elim
  exact cb hs
def gd:List (F0):=[1,2,3,4,5,6,9,11,12,13]
def cv (p:F0):F0:=
 match p.val with|1=>3|3=>1|2=>6|6=>2|4=>5|5=>4|_=>0
def bS (p:F0):F0:=
 match p.val with|1=>7|3=>7|2=>8|6=>8|4=>10|5=>10|_=>0
def fm (m:Fin 1024):S0:=
 (univ:Finset (Fin 10)).filter (λi=>(m.val >>> i.val) % 2=1) |>.image
  (λi=>gd.getD i.val 0)
def iJ (m:Fin 1024):Bool:=
 let H:=fm m
 decide (∀l∈({9,11,12,13}:S0),
  l∈H\/2≤((univ.filter (λp=>aQ l p=true))∩H).card) &&
 decide (∀c∈H,(H.card-1)+((univ.filter (λn=>aQ c n=true)) \ H).card≤6) &&
 decide (∃a1∈({7,8,10}:S0),∃a2∈({7,8,10}:S0),
  ∀p∈H,p.val<7->bS p≠a1->bS p≠a2->
   ∀y∈H,y≠p->y=cv p\/aQ (cv p) y=true)
lemma ox:∀m:Fin 1024,iJ m=true->fm m={9,11,12,13}\/fm m={1,3,4,5}\/fm m={1,2,3,6}\/fm m={2,4,5,6}:=aa
def f9:List (F0):=[1,2,3,4,5,6]
def ju (m:Fin 64):S0:=
 (univ:Finset (Fin 6)).filter (λi=>(m.val >>> i.val) % 2=1) |>.image
  (λi=>f9.getD i.val 0)
lemma pN:∀m:Fin 64,∀l_bad∈({9,11,12,13}:S0),let SE:=ju m
 (∃l∈({9,11,12,13}:S0),l≠l_bad/\∃p1∈({1,2,3,4,5,6}:S0),∃p2∈({1,2,3,4,5,6}:S0),∃p3∈({1,2,3,4,5,6}:S0),p1≠p2/\p1≠p3/\p2≠p3/\aH l p1/\aH l p2/\aH l p3/\((p1∈SE/\2≤SE.card)\/(p1∉SE/\cv p1∉SE))/\((p2∈SE/\2≤SE.card)\/(p2∉SE/\cv p2∉SE)))\/
 SE=(univ:S0).filter (λp=>aQ l_bad p=true):=aa
lemma pA:∀k:Nat,∀m:Nat,(univ.filter (λj:Fin k=>j.val<m)).sum (λj=>2 ^ j.val)<2 ^ m:=by
 intro k m;induction m with
 | zero=>
  have:univ.filter (λj:Fin k=>j.val<0)=∅:=by ext j;simp
  rw[this];simp
 | succ m ih=>
  by_cases l:m<k
  ·have h:univ.filter (λj:Fin k=>j.val<m+1) =
     insert ⟨m,l⟩ (univ.filter (λj:Fin k=>j.val<m)):=by
    ext j;simp only[mF,mV,ae,mI,Fin.ext_iff];omega
   rw[h,sum_insert ab];have h1:2 ^ (m+1)=2 ^ m+2 ^ m:=by ring
   have r:(⟨m,l⟩:Fin k).val=m:=rfl;rw[r];omega
  ·have p:univ.filter (λj:Fin k=>j.val<m+1) =
     univ.filter (λj:Fin k=>j.val<m):=by
    ext j;simp only[mF,mV,ae];omega
   rw[p]
   have:2 ^ m<2 ^ (m+1):=by rw[Nat.pow_succ];have:=aB m;omega
   omega
lemma gI {k:Nat}(P:Fin k->Prop)[DecidablePred P](i:Fin k):(((univ:Finset (Fin k)).sum (λj=>if P j then 2 ^ j.val else 0)) >>> i.val) % 2=1<->P i:=by
 let f:Fin k->Nat:=λj=>if P j then 2 ^ j.val else 0
 have l:(univ:Finset (Fin k)) =
   insert i (univ.filter (λj:Fin k=>j.val< i.val)∪univ.filter (λj:Fin k=>i.val<j.val)):=by
  ext j;simp only[mV,mI,mU,mF,ae,true_iff];rcases nT j.val i.val with h|h|h
  ·exact oR (oL h)
  ·exact oL (Fin.ext h)
  ·exact oR (oR h)
 have p:(univ:Finset (Fin k)).sum f =
   (univ.filter (λj:Fin k=>j.val< i.val)).sum f+f i +
   (univ.filter (λj:Fin k=>i.val<j.val)).sum f:=by
  conv_lhs=>rw[l]
  rw[sum_insert ab,ap (by
   rw[dL];intro j a1 a0;simp at a1 a0;omega)]
  ring
 have m:(univ.filter (λj:Fin k=>j.val< i.val)).sum f<2 ^ i.val:=by
  have h:(univ.filter (λj:Fin k=>j.val< i.val)).sum f≤
    (univ.filter (λj:Fin k=>j.val< i.val)).sum (λj=>2 ^ j.val):=
   sM (λj _=>by show (if P j then 2 ^ j.val else 0)≤2 ^ j.val;split_ifs;exact lR _;exact nZ _)
  exact lt_of_le_of_lt h (pA k i.val)
 have r:2 ^ (i.val+1) ∣ (univ.filter (λj:Fin k=>i.val<j.val)).sum f:=by
  refine dvd_sum (λj hj=>?_);have a2:i.val<j.val:=(mF.1 hj).2;show 2 ^ (i.val+1) ∣ (if P j then 2 ^ j.val else 0);split_ifs
  ·exact Nat.pow_dvd_pow 2 Y
  ·exact dvd_zero _
 obtain ⟨q,hq⟩:=r;change ((univ:Finset (Fin k)).sum f >>> i.val) % 2=1<->P i;rw[Nat.shiftRight_eq_div_pow,p,hq,Nat.pow_succ];dsimp only[f];split_ifs with hmem
 ·refine ⟨λ_=>hmem,λ_=>?_⟩
  have:(univ.filter (λj:Fin k=>j.val< i.val)).sum f+2 ^ i.val+2 ^ i.val*2*q =
    (univ.filter (λj:Fin k=>j.val< i.val)).sum f+2 ^ i.val*(1+2*q):=by ring
  rw[this,Nat.add_mul_div_left _ _ (aB i.val),Nat.div_eq_of_lt m];omega
 ·refine ⟨λh=>?_,λhc=>(hmem hc).elim⟩
  have:(univ.filter (λj:Fin k=>j.val< i.val)).sum f+0+2 ^ i.val*2*q =
    (univ.filter (λj:Fin k=>j.val< i.val)).sum f+2 ^ i.val*(2*q):=by ring
  rw[this,Nat.add_mul_div_left _ _ (aB i.val),Nat.div_eq_of_lt m] at h;omega
lemma nv (S:S0)(r:S⊆{1,2,3,4,5,6}):∃m:Fin 64,ju m=S:=by
 classical
 let n:Nat:=(univ:Finset (Fin 6)).sum (λi=>if f9.getD i.val 0∈S then 2 ^ i.val else 0)
 have h:n<64:=by
  have h1:n≤(univ:Finset (Fin 6)).sum (λi=>2 ^ i.val):=sM (λi _=>by split_ifs;exact lR _;exact nZ _);have h2:(univ:Finset (Fin 6)).sum (λi:Fin 6=>2 ^ i.val)=63:=o
  omega
 refine ⟨⟨n,h⟩,?_⟩;ext x;simp only[ju,mM,mF,mV,ae];constructor
 ·rintro ⟨i,l,rfl⟩;exact (gI (λj:Fin 6=>f9.getD j.val 0∈S) i).1 l
 ·intro p;have k:=r p;obtain ⟨i,l⟩:∃i:Fin 6,f9.getD i.val 0=x:=by
   simp only[mI,mS] at k;rcases k with rfl|rfl|rfl|rfl|rfl|rfl
   ·exact ⟨0,rfl⟩
   ·exact ⟨1,rfl⟩
   ·exact ⟨2,rfl⟩
   ·exact ⟨3,rfl⟩
   ·exact ⟨4,rfl⟩
   ·exact ⟨5,rfl⟩
  exact ⟨i,(gI (λj:Fin 6=>f9.getD j.val 0∈S) i).2 (l.symm▸p),l⟩
lemma ok (S:S0)(r:S⊆{1,2,3,4,5,6,9,11,12,13}):∃m:Fin 1024,fm m=S:=by
 classical
 let n:Nat:=(univ:Finset (Fin 10)).sum (λi=>if gd.getD i.val 0∈S then 2 ^ i.val else 0)
 have k:n<1024:=by
  have h1:n≤(univ:Finset (Fin 10)).sum (λi=>2 ^ i.val):=sM (λi _=>by split_ifs;exact lR _;exact nZ _);have h2:(univ:Finset (Fin 10)).sum (λi:Fin 10=>2 ^ i.val)=1023:=o
  omega
 refine ⟨⟨n,k⟩,?_⟩;ext x;simp only[fm,mM,mF,mV,ae];constructor
 ·rintro ⟨i,l,rfl⟩;exact (gI (λj:Fin 10=>gd.getD j.val 0∈S) i).1 l
 ·intro p;have h:=r p;obtain ⟨i,l⟩:∃i:Fin 10,gd.getD i.val 0=x:=by
   simp only[mI,mS] at h;rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   ·exact ⟨0,rfl⟩
   ·exact ⟨1,rfl⟩
   ·exact ⟨2,rfl⟩
   ·exact ⟨3,rfl⟩
   ·exact ⟨4,rfl⟩
   ·exact ⟨5,rfl⟩
   ·exact ⟨6,rfl⟩
   ·exact ⟨7,rfl⟩
   ·exact ⟨8,rfl⟩
   ·exact ⟨9,rfl⟩
  exact ⟨i,(gI (λj:Fin 10=>gd.getD j.val 0∈S) i).2 (l.symm▸p),l⟩
lemma kT {D:aJ}(h:aV 14 D)(w:Nat)(m:w<14+D.length):val D (λ_:F0=>false) w=false:=by
 induction w using sI with
 | _ w ih=>
  by_cases l:w<14
  ·rw[ck D (λ_:F0=>false) w l]
  ·obtain ⟨j,rfl⟩:∃j,w=14+j:=⟨w-14,Y⟩;have k:j<D.length:=Y
   rw[cc h _ k false,Bool.not_false,ih _ (bv h k false) (by have:=bv h k false;omega),ih _ (bv h k true) (by have:=bv h k true;omega)];cases bf D j<;>rfl
lemma eh {D:aJ}(hS:aV 14 D){w:Nat}(hw:w<14+D.length){x y:F0}(_hxy:x≠y)(hx:x∉O 14 D w)(hy:y∉O 14 D w)(h:val D (aL x y) w=true):∃e:A0,e∈aG 14 D x/\aI e∈aG 14 D y/\rG (λa c=>bk 14 D a c/\val D (aL x y) a=true) (14+e.1) w:=by
 induction w using sI with
 | _ w ih=>
  by_cases a4:w<14
  ·rw[ck D (aL x y) w a4] at h;simp only[aL,bO,dT] at h;rcases h with a6|a5
   ·exact (hx (bD.2 (by rw[ck D (single x) w a4,a6];simp[single]))).elim
   ·exact (hy (bD.2 (by rw[ck D (single y) w a4,a5];simp[single]))).elim
  ·obtain ⟨j,rfl⟩:∃j,w=14+j:=⟨w-14,Y⟩;have m:j<D.length:=Y
   have a3:=bv hS m false;have a1:=bv hS m true;cases ht:bf D j
   ·rw[cc hS _ m false,ht,gop_false,bO] at h;rcases h with hA|hB
    ·have a2:x∉O 14 D (W D (j,false)):=λhm=>
      hx (bD.2 (by rw[cc hS _ m false,ht,gop_false,bD.1 hm];rfl))
     have a0:y∉O 14 D (W D (j,false)):=λhm=>
      hy (bD.2 (by rw[cc hS _ m false,ht,gop_false,bD.1 hm];rfl))
     obtain ⟨e,k,l,hr⟩:=ih (W D (j,false)) a3 Y a2 a0 hA;exact ⟨e,k,l,rT hr ⟨b4 (n:=14) m false,hA⟩⟩
    ·have p:x∉O 14 D (W D (j,true)):=λhm=>
      hx (bD.2 (by rw[cc hS _ m true,ht,gop_false,bD.1 hm];rfl))
     have r:y∉O 14 D (W D (j,true)):=λhm=>
      hy (bD.2 (by rw[cc hS _ m true,ht,gop_false,bD.1 hm];rfl))
     obtain ⟨e,k,l,hr⟩:=ih (W D (j,true)) a1 Y p r hB;exact ⟨e,k,l,rT hr ⟨b4 (n:=14) m true,hB⟩⟩
   ·rw[cc hS _ m false,ht,gop_true,bA] at h;obtain ⟨hA,hB⟩:=h;by_cases a2:x∈O 14 D (W D (j,false))
    ·by_cases r:y∈O 14 D (W D (j,true))
     ·exact ⟨(j,false),aP.2 ⟨m,a2,hx⟩,aP.2 ⟨m,r,hy⟩,rF⟩
     ·have p:x∉O 14 D (W D (j,true)):=λhm=>
       hx (bD.2 (by rw[cc hS _ m false,ht,gop_true,Bool.not_false,bD.1 a2,bD.1 hm];rfl))
      obtain ⟨e,k,l,hr⟩:=ih (W D (j,true)) a1 Y p r hB;exact ⟨e,k,l,rT hr ⟨b4 (n:=14) m true,hB⟩⟩
    ·by_cases a0:y∈O 14 D (W D (j,false))
     ·by_cases p:x∈O 14 D (W D (j,true))
      ·exact ⟨(j,true),aP.2 ⟨m,p,hx⟩,aP.2 ⟨m,by simpa[aI] using a0,hy⟩,rF⟩
      ·have r:y∉O 14 D (W D (j,true)):=λhm=>
        hy (bD.2 (by rw[cc hS _ m false,ht,gop_true,Bool.not_false,bD.1 a0,bD.1 hm];rfl))
       obtain ⟨e,k,l,hr⟩:=ih (W D (j,true)) a1 Y p r hB;exact ⟨e,k,l,rT hr ⟨b4 (n:=14) m true,hB⟩⟩
     ·obtain ⟨e,k,l,hr⟩:=ih (W D (j,false)) a3 Y a2 a0 hA;exact ⟨e,k,l,rT hr ⟨b4 (n:=14) m false,hA⟩⟩
lemma iw {D:aJ}(hS:aV 14 D){b:F0->Nat}(a1:dz 14 D b){x:F0}(hx:x∈aW 14 D){e:A0}(he:e∈aG 14 D x):b x<14+e.1:=by
 rcases e with ⟨h,p⟩
 by_contra b0;obtain ⟨hj,a7,a2⟩:=aP.1 he;have bm:W D (h,p)<14+h:=bv hS hj p
 have m:aU 14 D x.val (W D (h,p)):=gQ hS x (W D (h,p)) a7 (λu hu hxu=>by
   by_contra a8;have a4:=(a1 x hx).2.2.2 u Y hxu
   omega)
 have r:aS D (W D (h,p))=1:=(by have h1:1≤aS D (W D (h,p)):=eU (b4 (n:=14) hj p);have h2:aS D (W D (h,p))≤1:=(by by_contra a8;have a4:=(a1 x hx).2.2.2 (W D (h,p)) Y a7;omega);omega);have a0:aU 14 D x.val (14+h):=rT m ⟨b4 (n:=14) hj p,r⟩;have a3:=ip hS a0 (by omega:14+h≤b x);have a6:val D (single x) (14+h)=val D (λ_:F0=>false) (14+h):=(by have h1:val D (single x) (14+h)=false:=(by by_contra ht;rw[bN] at ht;exact a2 (bD.2 ht));rw[h1,kT hS (14+h) Y]);have a5:=gW hS (single x) (λ_:F0=>false) x (λk hk=>by simp[single,hk])
  (14+h) (b x) a3 a6
 have l:x∈O 14 D (b x):=by rw[(a1 x hx).2.1];simp
 rw[kT hS (b x) (d4 l),bD.1 l] at a5;exact bF a5.symm
lemma ky {D:aJ}(h:a9 14 D)(u:Nat)(hu:u<aO 14 D):aU 14 D u (aO 14 D)\/∃w,u≤w/\w<aO 14 D/\2≤aS D w/\aU 14 D u w:=by
 have hS:=h.1;generalize hk:aO 14 D-u=k;induction k using sI generalizing u with
 | _ k ih=>
  by_cases a5:2≤aS D u
  ·exact oR ⟨u,lR _,hu,a5,rF⟩
  ·have m:aS D u=1:=by
    have:=h.2.1 u (by unfold aO at hu;omega);omega
   obtain ⟨j,p⟩:=cO.1 (show 0<(bL D u).card by unfold aS at m;omega);simp only[bL,mF,mR] at p;obtain ⟨hj,a0⟩:=p;have l:bk 14 D u (14+j):=by
    rcases a0 with r|r
    ·rw[← r];exact b4 (n:=14) hj false
    ·rw[← r];exact b4 (n:=14) hj true
   have a8:u<14+j:=fG hS l;have a6:14+j≤aO 14 D:=by unfold aO;omega
   by_cases a1:14+j=aO 14 D
   ·exact oL (a1▸ReflTransGen.single ⟨l,m⟩)
   ·rcases ih (aO 14 D-(14+j)) Y (14+j) Y rfl with hc|⟨w,a7,a4,a2,a3⟩
    ·exact oL (rH ⟨l,m⟩ hc)
    ·exact oR ⟨w,Y,a4,a2,rH ⟨l,m⟩ a3⟩
lemma lf {D:aJ}(hS:aV 14 D)(x:F0->Bool){u w:Nat}(r:aU 14 D u w)(hu:val D x u=true)(k:val D x w=false):∃j:Nat,∃s:Bool,j<D.length/\bf D j=true/\aU 14 D u (W D (j,s))/\aS D (W D (j,s))=1/\aU 14 D (14+j) w/\val D x (W D (j,s))=true/\val D x (W D (j,!s))=false:=by
 induction r with
 | refl=>rw[hu] at k;exact absurd k.symm bF
 | @tail a c hab hbc ih=>
  by_cases p:val D x a=true
  ·obtain ⟨j,s,hj,rfl,h⟩:=dN.1 hbc.1;have ht:bf D j=true:=by
    by_contra m;rw[bT] at m;rw[cc hS x hj s,m,gop_false,h,p] at k;exact bF k.symm
   have l:val D x (W D (j,!s))=false:=(by rw[cc hS x hj s,ht,gop_true,h,p,aw] at k;exact k);exact ⟨j,s,hj,ht,h.symm▸hab,h.symm▸hbc.2,rF,h.symm▸p,l⟩
  ·obtain ⟨j,s,h1,h2,h3,h4,h5,h6,h7⟩:=ih (bE.2 p);exact ⟨j,s,h1,h2,h3,h4,rT h5 hbc,h6,h7⟩
lemma gV {D:aJ}(p:aV 14 D){x:F0->Bool}{a b c:Nat}(l:aU 14 D a b)(m:rG (λu v=>bk 14 D u v/\val D x u=true) a c)(a0:b≤c)(hc:val D x c=true):val D x b=true/\rG (λu v=>bk 14 D u v/\val D x u=true) b c:=by
 induction l using rI with
 | refl=>
  rcases cH m with rfl|⟨_,k,_⟩
  ·exact ⟨hc,rF⟩
  ·exact ⟨k.2,m⟩
 | @head u v huv hrest ih=>
  rcases cH m with a1|⟨v',k,h⟩
  ·have a2:=fG p huv.1;have r:=bV p (λ_ _ hh=>hh.1) hrest;omega
  ·have hv:v'=v:=cY k.1 huv.1 huv.2;subst hv;exact ih h
lemma f4 {D:aJ}(m:aV 14 D){u j:Nat}{s:Bool}(r:j<D.length)(a1:aU 14 D u (W D (j,s)))(a3:aS D (W D (j,s))=1):¬rG (bk 14 D) u (W D (j,!s)):=by
 intro hr;have a4:W D (j,s)≠W D (j,!s):=(by have:=(m j r).2.2;cases s<;>simp[W,this,nS this]);rcases gj m a1 hr with h1|⟨h2,p⟩
 ·rcases cH h1 with l|⟨c,hc,h⟩
  ·exact a4 l
  ·have k:c=14+j:=cY hc (b4 (n:=14) r s) a3;have a0:=bV m (λ_ _ hh=>hh) (k▸h);have a2:=bv m r (!s);omega
 ·rcases cH h2 with l|⟨c,hc,h⟩
  ·exact p l
  ·have k:c=14+j:=cY hc.1 (b4 (n:=14) r (!s)) hc.2;have a0:=bV m (λ_ _ hh=>hh.1) (k▸h);have a2:=bv m r s;omega
lemma l8 {D:aJ}(h:a9 14 D)(hD:be D)(hT:fu D){b:F0->Nat}(g9:dz 14 D b){a8:F0->A0}(bm:ch 14 HG D a8){p:P0}(c6:aR 14 D b={p})(hI:aN 14 D={0})(k7:(a8 0).1=26){m u2:F0}(eu:m∈({7,8,10}:S0))(b8:u2∈({7,8,10}:S0))(ec:m≠u2)(ll:(aG 14 D m).card=3)(lb:(aG 14 D u2).card=3){E:A0}(b5:E.1≠(a8 0).1)(er:E∈aG 14 D m)(f3:E∈aG 14 D u2):p.1≤W D E/\∀(P:Nat->Nat->Prop),(∀a c,P a c->bk 14 D a c)->∀w:Nat,rG P p.1 w->w<aO 14 D->m∉O 14 D w->rG P p.1 (14+E.1)/\rG P (14+E.1) w:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have hb:=cX g9;have h0:(0:F0)∈aN 14 D:=by rw[hI];simp
 have l:=fQ hG h hC b hb c6 (by omega:3≤(aG 14 D m).card);have a0:=fQ hG h hC b hb c6 (by omega:3≤(aG 14 D u2).card);have hE:p∈aR 14 D b:=by rw[c6];simp
 have f0:p∈cq 14 D:=(mF.1 (mD.1 hE).1).1;have fz:2≤aS D p.1:=by have:=(dh.1 f0).2;omega
 have hk:aS D p.1=2:=by
  by_contra e4;have l0:3≤aS D p.1:=Y
  have cb:p.1∈bY 14 D:=(dh.1 f0).1;have a5:∀k:Nat,(⟨p.1,k⟩:P0)∉dD 14 D b:=(by intro k e5;obtain ⟨y,hy,i7⟩:=mM.1 e5;have hF:b y=p.1:=kA Sigma.fst i7;have g2:m=y:=mS.1 (by rw[← (hb y hy).2,hF];exact l.2.2.2);have e0:u2=y:=mS.1 (by rw[← (hb y hy).2,hF];exact a0.2.2.2);exact ec (g2.trans e0.symm));have ik:(⟨p.1,0⟩:P0)∈aR 14 D b:=mD.2 ⟨mF.2 ⟨dh.2 ⟨cb,by show 0+1<aS D p.1;omega⟩,⟨m,l.2.2.2⟩⟩,a5 0⟩;have i3:(⟨p.1,1⟩:P0)∈aR 14 D b:=mD.2 ⟨mF.2 ⟨dh.2 ⟨cb,by show 1+1<aS D p.1;omega⟩,⟨m,l.2.2.2⟩⟩,a5 1⟩;have hg:(⟨p.1,0⟩:P0)=p:=mS.1 (c6▸ik);have hK:(⟨p.1,1⟩:P0)=p:=mS.1 (c6▸i3);have g7:(⟨p.1,0⟩:P0)=⟨p.1,1⟩:=hg.trans hK.symm;cases g7
 have f1:∀x∈({m,u2}:S0),∀w,p.1<w->x∈O 14 D w->aS D w≤1:=by
  intro x hx w m1 hX;have ca:x∈aW 14 D/\x∈O 14 D p.1:=by
   rcases mI.1 hx with rfl|hx
   ·exact ⟨l.2.2.1,l.2.2.2⟩
   ·rw[mS.1 hx];exact ⟨a0.2.2.1,a0.2.2.2⟩
  by_contra la;have l4:2≤aS D w:=Y
  have h9:(⟨w,0⟩:P0)∈dr 14 D:=(by rw[dr,mF,dh];exact ⟨⟨cz.2 (ew hS (w:=w) Y),by show 0+1<aS D w;omega⟩,⟨x,hX⟩⟩);by_cases e5:(⟨w,0⟩:P0)∈dD 14 D b
  ·obtain ⟨v,hv,hY⟩:=mM.1 e5;have h5:b v=w:=kA Sigma.fst hY;have i5:x=v:=mS.1 (by rw[← (g9 v hv).2.1,h5];exact hX);have ho:=(g9 x ca.1).2.2.2 p.1 fz ca.2;rw[i5,h5] at ho;omega
  ·have c8:(⟨w,0⟩:P0)∈aR 14 D b:=mD.2 ⟨h9,e5⟩;rw[c6,mS] at c8;have k3:w=p.1:=kA Sigma.fst c8;omega
 have b1:∀e,e∈aG 14 D m->e∈aG 14 D u2->e=a8 0\/e=E:=by
  intro e c2 et;by_contra g8;rw[nO] at g8
  have g7:a8 0∈aG 14 D m:=bd bm h0 (by
   have h':=eu;simp only[mI,mS] at h'
   rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl)
  have ks:a8 0∈aG 14 D u2:=bd bm h0 (by
   have h':=b8;simp only[mI,mS] at h'
   rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl)
  have g0:a8 0≠E:=λhh=>b5 (kA Prod.fst hh).symm
  have hi:aG 14 D m={a8 0,E,e}:=(eS (λa ha=>by
    simp only[mI,mS] at ha;rcases ha with rfl|rfl|rfl
    ·exact g7
    ·exact er
    ·exact c2)
    (by rw[cI (by simp[g0,nS g8.1]),cP (nS g8.2)];omega)).symm
  obtain ⟨u3,hq,hm,k2⟩:=(by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),a≠c->∃u3∈({7,8,10}:S0),u3≠a/\u3≠c) m eu u2 b8 ec;obtain ⟨a,hZ,-,fc⟩:=bB h hD (nS hm) ec
   ((by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),¬aH a c) u3 hq u2 b8)
  rw[hi,mI,mI,mS] at hZ;rcases hZ with rfl|rfl|rfl
  ·exact fc (aP.1 ks).2.1
  ·exact fc (aP.1 f3).2.1
  ·exact fc (aP.1 et).2.1
 have b2:∀j∈bL D p.1,∃e:A0,(e=a8 0\/e=E)/\((e.1=j/\W D e=p.1)\/rG (dG 14 D {m,u2}) (14+j) (W D e)):=by
  intro j fi;simp only[bL,mF,mR] at fi;obtain ⟨c7,ev⟩:=fi;have m2:p.1<14+j:=by have:=hS j c7;omega
  obtain ⟨s,hs⟩:∃s:Bool,W D (j,s)=p.1:=by
   rcases ev with r|r
   ·exact ⟨false,by rw[bP];exact r⟩
   ·exact ⟨true,by rw[bU];exact r⟩
  by_cases es:∃x1∈({m,u2}:S0),x1∈O 14 D (14+j)
  ·obtain ⟨x1,i4,hR⟩:=es;have hM:∀x∈({m,u2}:S0),bi 14 D (ba 14 D {x})=∅:=λx hx=>by
    rcases mI.1 hx with rfl|hx
    ·exact l.2.1
    ·rw[mS.1 hx];exact a0.2.1
   have ht:=(eT hS (hM x1 i4) c7 hR).1;have hA:∀x∈({m,u2}:S0),x∈O 14 D (14+j):=λx hx=>by
    rw[eL hS c7 ht,mU];have hN:x∈O 14 D p.1:=by
     rcases mI.1 hx with rfl|hx
     ·exact l.2.2.2
     ·rw[mS.1 hx];exact a0.2.2.2
    rcases ev with r|r
    ·left;rw[r];exact hN
    ·right;rw[r];exact hN
   obtain ⟨e,c2,et⟩:=kC hG h hC {m,u2} ⟨m,ab⟩ hM (14+j) hA
    (λx hx w hw=>f1 x hx w Y)
   exact ⟨e,b1 e (c2 m ab) (c2 u2 ab),oR et⟩
  ·have c2:(j,s)∈aG 14 D m:=aP.2 ⟨c7,hs▸l.2.2.2,λhc=>es ⟨m,ab,hc⟩⟩;have et:(j,s)∈aG 14 D u2:=aP.2 ⟨c7,hs▸a0.2.2.2,λhc=>es ⟨u2,ab,hc⟩⟩;exact ⟨(j,s),b1 (j,s) c2 et,oL ⟨rfl,hs⟩⟩
 have g3:p.1≤W D E:=by
  obtain ⟨j1,c5,j2,c3,e4⟩:=oC.1 (show 1<(bL D p.1).card by unfold aS at fz;omega);obtain ⟨e1,c0,h3⟩:=b2 j1 c5;obtain ⟨e2,ct,hd⟩:=b2 j2 c3;have g6:e1.1≠e2.1:=by
   intro d1;have ej:e1=e2:=by
    rcases c0 with rfl|rfl<;>rcases ct with rfl|rfl
    ·rfl
    ·exact (b5 d1.symm).elim
    ·exact (b5 d1).elim
    ·rfl
   subst ej;have hM:∀x∈({m,u2}:S0),bi 14 D (ba 14 D {x})=∅:=λx hx=>by
    rcases mI.1 hx with rfl|hx
    ·exact l.2.1
    ·rw[mS.1 hx];exact a0.2.1
   have a6:∀a c,dG 14 D {m,u2} a c->bk 14 D a c:=λ_ _ hh=>hh.1;have a7:∀j∈bL D p.1,j<D.length/\p.1<14+j/\(aZ D j=p.1\/aY D j=p.1):=λj hj=>by
    simp only[bL,mF,mR] at hj;have:=hS j hj.1;exact ⟨hj.1,Y,hj.2⟩
   rcases h3 with ⟨iz,l7⟩|hW<;>rcases hd with ⟨i0,lw⟩|h8
   ·exact e4 (iz.symm.trans i0)
   ·have:=bV hS a6 h8;have:=(a7 j2 c3).2.1;omega
   ·have:=bV hS a6 hW;have:=(a7 j1 c5).2.1;omega
   ·have hB:∀a a' c,dG 14 D {m,u2} a c->dG 14 D {m,u2} a' c->a=a':=λa a' c ha ha'=>by
     by_contra f2;obtain ⟨l3,k0,j0⟩:=ha.1;obtain ⟨-,-,hO⟩:=ha'.1;have g5:c-14<D.length:=Y
     have g4:m∈O 14 D (14+(c-14)):=by rw[Nat.add_sub_cancel' k0];exact (ha.2.2 m ab).2
     apply (eT hS (hM m ab) g5 g4).2;have r:=(ha.2.2 m ab).1;have h2:=(ha'.2.2 m ab).1;rcases j0 with e1|e1<;>rcases hO with e2|e2
     ·exact absurd (e1.symm.trans e2) f2
     ·rw[e1,e2];exact ⟨r,h2⟩
     ·rw[e1,e2];exact ⟨h2,r⟩
     ·exact absurd (e1.symm.trans e2) f2
    have c1:∀ja∈bL D p.1,∀jb∈bL D p.1,ja≠jb->¬rG (dG 14 D {m,u2}) (14+ja) (14+jb):=λja hja jb g5 hab hp=>by
     obtain ⟨lo,lc,-⟩:=a7 ja hja;obtain ⟨hf,ls,h7⟩:=a7 jb g5;rcases cT hp with ej|⟨u,he,d0⟩
     ·exact hab Y
     ·have eb:=bV hS a6 he;have g1:u=p.1:=by
       by_contra g1;obtain ⟨-,-,hJ⟩:=d0.1;rw[am] at hJ;apply (eT hS (hM m ab) hf (d0.2.2 m ab).2).2;have hu:=(d0.2.2 m ab).1;have hU:=l.2.2.2;rcases hJ with e1|e1<;>rcases h7 with e2|e2
       ·exact absurd (e1.symm.trans e2) g1
       ·rw[e1,e2];exact ⟨hu,hU⟩
       ·rw[e1,e2];exact ⟨hU,hu⟩
       ·exact absurd (e1.symm.trans e2) g1
      omega
    rcases kj hB hW h8 with r|r
    ·exact c1 j1 c5 j2 c3 e4 r
    ·exact c1 j2 c3 j1 c5 (nS e4) r
  rcases c0 with rfl|rfl
  ·have hz:e2=E:=ct.resolve_left (λhh=>g6 (by rw[hh]));rw[hz] at hd;rcases hd with ⟨-,hs⟩|hp
   ·omega
   ·have eb:=bV hS (λ_ _ hh=>hh.1) hp;have h4:=(mF.1 c3).1;have hH:=(mR.1 h4);have:=hS j2 hH;have ev:=(mF.1 c3).2;omega
  ·rcases h3 with ⟨-,hs⟩|hp
   ·omega
   ·have eb:=bV hS (λ_ _ hh=>hh.1) hp;have hr:=mR.1 (mF.1 c5).1;have:=hS j1 hr;have ev:=(mF.1 c5).2;omega
 refine ⟨g3,λP hP w hrw hwlt hu1nw=>?_⟩;rcases cH hrw with rfl|⟨c,e7,b6⟩
 ·exact (hu1nw l.2.2.2).elim
 ·obtain ⟨j,s,hj,rfl,gs⟩:=dN.1 (hP _ _ e7);have fi:j∈bL D p.1:=by
   rw[bL,mF,mR];refine ⟨hj,?_⟩;cases s
   ·left;simpa[W] using gs
   ·right;simpa[W] using gs
  obtain ⟨e,a2,k1⟩:=b2 j fi;rcases k1 with ⟨h6,-⟩|a4
  ·rcases a2 with rfl|rfl
   ·exfalso;have eb:=bV hS hP b6;unfold aO at hwlt;rw[hT.1] at hwlt;omega
   ·exact ⟨h6▸ReflTransGen.single e7,h6▸b6⟩
  ·have hl:aU 14 D (14+j) (W D e):=dt (λ_ _ hh=>⟨hh.1,hh.2.1⟩) a4;have a3:∀v,rG (dG 14 D {m,u2}) (14+j) v->m∈O 14 D v/\u2∈O 14 D v:=by
    intro v hv;induction hv with
    | refl=>
     rcases cH a4 with ej|⟨_,r,_⟩
     ·have hn:m∈O 14 D (W D e):=by
       rcases a2 with rfl|rfl
       ·exact (bm.1 0 h0).2.2.1 m (by
         have h':=eu;simp only[mI,mS] at h'
         rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl)
       ·exact (aP.1 er).2.1
      have hQ:u2∈O 14 D (W D e):=by
       rcases a2 with rfl|rfl
       ·exact (bm.1 0 h0).2.2.1 u2 (by
         have h':=b8;simp only[mI,mS] at h'
         rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl)
       ·exact (aP.1 f3).2.1
      exact ⟨ej.symm▸hn,ej.symm▸hQ⟩
     ·exact ⟨(r.2.2 m ab).1,(r.2.2 u2 ab).1⟩
    | tail _ hbc _=>exact ⟨(hbc.2.2 m ab).2,(hbc.2.2 u2 ab).2⟩
   have ez:∀a,rG (dG 14 D {m,u2}) a (W D e)->∀v',rG P a v'->m∉O 14 D v'->rG P a (W D e)/\rG P (W D e) v':=by
    intro a ha;induction ha using rI with
    | refl=>intro v' d2 _;exact ⟨rF,d2⟩
    | @head a c hac hrest_a ih=>
     intro v' d2 fl;rcases cH d2 with rfl|⟨c',b0,a1⟩
     ·exact (fl (hac.2.2 m ab).1).elim
     ·have ko:c'=c:=cY (hP _ _ b0) hac.1 hac.2.1;subst ko;obtain ⟨r,h2⟩:=ih v' a1 fl;exact ⟨rH b0 r,h2⟩
   obtain ⟨id,iy⟩:=ez (14+j) a4 w b6 hu1nw;rcases cH iy with rfl|⟨c',b0,a1⟩
   ·exact (hu1nw (a3 _ a4).1).elim
   ·have ea:e.1<D.length:=by
     rcases a2 with rfl|rfl
     ·exact (bm.1 0 h0).1
     ·exact (aP.1 er).1
    have e3:aS D (W D e)=1:=(by have mt:1≤aS D (W D e):=eU (b4 (n:=14) ea e.2);have fc:aS D (W D e)≤1:=(by have eb:=bV hS (λ_ _ hh=>hh.1) a4;have ix:p.1<14+j:=fG hS (hP _ _ e7);exact f1 m ab (W D e) Y (a3 _ a4).1);omega);have hL:c'=14+e.1:=cY (hP _ _ b0) (b4 (n:=14) ea e.2) e3;subst hL;rcases a2 with rfl|rfl
    ·exfalso;have eb:=bV hS hP a1;unfold aO at hwlt;rw[hT.1] at hwlt;omega
    ·exact ⟨rH e7 (rT id b0),a1⟩
lemma oK {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(hM:D.length=27){b:F0->Nat}(hw:dz 14 D b){l:F0->A0}(k:ch 14 HG D l)(eb:br 14 D=(aW 14 D).card+1)(h0:(0:F0)∈aN 14 D)(er:aU 14 D (0:F0).val (aO 14 D))(fi:∀x:F0,(aG 14 D x).card≤3)(hO:(l 0).1<26):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have m:aM D=26:=by unfold aM;omega
 obtain ⟨s,ct,-,a0⟩:=gU h hD hT h0 er;rw[m] at ct a0;have a7:O 14 D (W D (26,!s))=∅:=by
  have a4:=dZ hG hS hC 0 (W D (26,!s)) (c9 hS ct);by_contra hL;obtain ⟨x,hx⟩:=nI.2 hL;have hH:x=0:=mS.1 (a4 hx);subst hH;have e5:=fj h hD k h0
  have ej:(26,!s)∈aG 14 D 0:=aP.2 ⟨Y,hx,by
   have hg:14+26=aO 14 D:=by unfold aO;omega
   rw[hg,c4 hD];simp⟩
  rw[e5,mS] at ej
  have:26=(l 0).1:=kA Prod.fst ej
  omega
 have bm:∀u∈({7,8,10}:S0),∃F,aG 14 D u={l 0,(26,s),F}/\(∀t:F0,t≠u->F∉aG 14 D t)/\∀w:F0,aH u w->w≠0->aI F∈aG 14 D w:=by
  intro u hu;have c2:aH 0 u:=(by have c8:=hu;simp only[mI,mS] at c8;rcases c8 with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl);obtain ⟨w0,hb,fc⟩:∃w0:F0,aH u w0/\w0≠0:=by
   have c8:=hu;simp only[mI,mS] at c8;rcases c8 with h1|h1|h1<;>rw[h1]
   ·exact ⟨1,(aK 7 1).1 rfl,o⟩
   ·exact ⟨2,(aK 8 2).1 rfl,o⟩
   ·exact ⟨4,(aK 10 4).1 rfl,o⟩
  obtain ⟨F,f2,hd,-⟩:=bp hG hS hC hb;have ea:F≠l 0:=λhe=>fc (bx k h0 (he▸hd));have c7:F≠(26,s):=λhe=>by
   have b8:=(aP.1 hd).2.1;rw[he,show W D (aI (26,s))=W D (26,!s) from rfl,a7] at b8;exact nE _ b8
  have et:({l 0,(26,s),F}:Finset (A0))⊆aG 14 D u:=by
   intro e he;simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
   ·exact bd k h0 c2
   ·exact m▸cV hD hT (m.symm▸a0 u c2)
   ·exact f2
  have ev:aG 14 D u={l 0,(26,s),F}:=(eS et (by
    have f3:(26,s)≠l 0:=m▸cw k (m.symm▸a7) h0
    rw[cI (by simp[f3.symm,ea.symm]),cP c7.symm];exact fi u)).symm
  refine ⟨F,ev,λt htu hFt=>?_,λw eu e7=>?_⟩
  ·have hE:t∈O 14 D (W D F):=(aP.1 hFt).2.1;by_cases g6:t=0
   ·subst g6;have e5:=fj h hD k h0;rw[e5,mS] at hFt;have h3:u∈O 14 D (W D (aI (l 0))):=hFt▸(aP.1 f2).2.1;rw[show W D (aI (l 0))=W D ((l 0).1,!(l 0).2) from rfl,(k.1 0 h0).2.2.2,mS] at h3;exact bW 0 (h3▸c2)
   ·obtain ⟨a,ec,hl,hW,g5⟩:=(by decide +kernel:∀u∈({7,8,10}:S0),∀t:F0,t≠u->t≠0->∃a∈({7,8,10}:S0),a≠u/\a≠t/\¬aH a t) u hu t htu g6;have g2:aH 0 a:=by
     have d2:=ec;simp only[mI,mS] at d2;rcases d2 with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl
    obtain ⟨e,hc,d2,hj⟩:=bB h hD (nS hl) (nS htu) g5;rw[ev,mI,mI,mS] at hc;rcases hc with rfl|rfl|rfl
    ·exact d2 ((k.1 0 h0).2.2.1 a g2)
    ·exact d2 (a0 a g2)
    ·exact hj hE
  ·obtain ⟨e',f1,fl,-⟩:=bp hG hS hC eu;have g3:e'≠l 0:=λhe=>e7 (bx k h0 (he▸fl));have fz:e'≠(26,s):=λhe=>by
    have b8:=(aP.1 fl).2.1;rw[he,show W D (aI (26,s))=W D (26,!s) from rfl,a7] at b8;exact nE _ b8
   rw[ev,mI,mI,mS] at f1;have ez:e'=F:=(f1.resolve_left g3).resolve_left fz;exact ez▸fl
 obtain ⟨F7,e4,d1,g8⟩:=bm 7 o;obtain ⟨F8,hy,es,hP⟩:=bm 8 o;obtain ⟨F10,hN,hk,hz⟩:=bm 10 o;have a3:∀t:F0,t∈O 14 D (W D (26,s))->t∈O 14 D (W D (l 0))->aH 0 t:=by
  have h1:=ib h hD hT k h0 ((aK 0 7).1 rfl) er (m.symm▸a7)
   (m.symm▸a0 7 ((aK 0 7).1 rfl))
   (λp hp hp1 hp26 a4=>by
    rw[e4,mI,mI,mS] at hp;rcases hp with rfl|rfl|rfl
    ·exact hp1 rfl
    ·exact hp26 m.symm
    ·exact absurd (mS.1 (a4 (aP.1 (g8 1 ((aK 7 1).1 rfl) o)).2.1)) o)
  rw[m] at h1;exact h1
 have c3:l 0≠F7:=λhe=>d1 8 o (he▸bd k h0 ((aK 0 8).1 rfl));have b2:(26,s)≠F7:=λhe=>d1 8 o (he▸(m▸cV hD hT (m.symm▸a0 8 ((aK 0 8).1 rfl))));have c0:l 0≠F8:=λhe=>es 7 o (he▸bd k h0 ((aK 0 7).1 rfl));have b0:(26,s)≠F8:=λhe=>es 7 o (he▸(m▸cV hD hT (m.symm▸a0 7 ((aK 0 7).1 rfl))));have cb:(26,s)≠l 0:=m▸cw k (m.symm▸a7) h0;have ca:∀x:F0,x∉({0,7,8,10}:S0)->(aG 14 D x).card≤2:=by
  intro x hx;by_contra hX;have hR:3≤(aG 14 D x).card:=Y
  have hU:3≤(aG 14 D 7).card:=(by rw[e4,cI (by simp[cb.symm,c3]),cP b2]);have hQ:3≤(aG 14 D 8).card:=(by rw[hy,cI (by simp[cb.symm,c0]),cP b0]);obtain ⟨P,Q,hI,a2⟩:=fw hG h hC b hw eb {7,8,x} ⟨7,ab⟩
   (λv hv=>by
    simp only[mI,mS] at hv
    rcases hv with rfl|rfl|rfl<;>assumption)
  have a8:∀e,e∈aG 14 D 7->e∈aG 14 D 8->e=l 0\/e=(26,s):=by
   intro e g4 hq;rw[e4,mI,mI,mS] at g4;rcases g4 with rfl|rfl|rfl
   ·exact oL rfl
   ·exact oR rfl
   ·exact (d1 8 o hq).elim
  have g7:=(a2 x ab).1;have hi:=(a2 x ab).2;have d0:P≠Q:=λhe=>hI (kA Prod.fst he);rcases a8 P (a2 7 ab).1 (a2 8 ab).1 with rfl|rfl<;>
   rcases a8 Q (a2 7 ab).2 (a2 8 ab).2 with rfl|rfl
  ·exact d0 rfl
  ·exact hx ((by decide +kernel:∀t:F0,aH 0 t->t∈({0,7,8,10}:S0)) x (a3 x (aP.1 hi).2.1 (aP.1 g7).2.1))
  ·exact hx ((by decide +kernel:∀t:F0,aH 0 t->t∈({0,7,8,10}:S0)) x (a3 x (aP.1 g7).2.1 (aP.1 hi).2.1))
  ·exact d0 rfl
 have e2:∀w w' u:F0,u∈({7,8,10}:S0)->aH u w->aH u w'->w≠0->w'≠0->w≠w'->aH w 9->u≠9->w∉({0,7,8,10}:S0)->∃r,aI r∈aG 14 D 9/\w∈O 14 D (W D r)/\∀a,a≠w->¬aH a w'->a∉O 14 D (W D r):=by
  intro w w' u hu eu gs e7 g0 f0 hJ ho hF;obtain ⟨Z,-,hn,g1⟩:=bm u hu;obtain ⟨r,g9,e0,-⟩:=bp hG hS hC hJ;have hK:r≠aI Z:=λhrz=>by rw[hrz,aT] at e0;exact hn 9 (nS ho) e0
  refine ⟨r,e0,(aP.1 g9).2.1,λa ha haw' hmem=>?_⟩;obtain ⟨e3,hf,hA,hr⟩:=bB h hD (x:=w) (a:=a) (b:=w') (nS ha) f0 haw';have a4:({aI Z,r}:Finset (A0))⊆aG 14 D w:=by
   intro x hx;rcases mI.1 hx with rfl|hx
   ·exact g1 w eu e7
   ·rw[mS.1 hx];exact g9
  have ez:=eS a4 (by rw[cP (nS hK)];exact ca w hF);rw[← ez,mI,mS] at hf;rcases hf with rfl|rfl
  ·exact hr (aP.1 (g1 w' gs g0)).2.1
  ·exact hA hmem
 obtain ⟨r1,a1,b1,c1⟩:=e2 1 3 7 o ((aK 7 1).1 rfl) ((aK 7 3).1 rfl)
  o o o ((aK 1 9).1 rfl) o o
 obtain ⟨r5,a5,b5,c5⟩:=e2 5 4 10 o ((aK 10 5).1 rfl) ((aK 10 4).1 rfl)
  o o o ((aK 5 9).1 rfl) o o
 obtain ⟨r6,a6,b6,c6⟩:=e2 6 2 8 o ((aK 8 6).1 rfl) ((aK 8 2).1 rfl)
  o o o ((aK 6 9).1 rfl) o o
 have hB:aI r1≠aI r5:=λhh=>
  c1 5 o (bw.1 rfl) (by rw[← aT r1,hh,aT];exact b5)
 have hs:aI r1≠aI r6:=λhh=>
  c1 6 o (bw.1 rfl) (by rw[← aT r1,hh,aT];exact b6)
 have ht:aI r5≠aI r6:=λhh=>
  c5 6 o (bw.1 rfl) (by rw[← aT r5,hh,aT];exact b6)
 have e1:({aI r1,aI r5,aI r6}:Finset (A0))⊆aG 14 D 9:=(by intro x hx;simp only[mI,mS] at hx;rcases hx with rfl|rfl|rfl<;>assumption);have hm:=cL e1;rw[cI (by simp[hB,hs]),cP ht] at hm;have:=ca 9 o;omega
lemma oq:∀u3∈({7,8,10}:S0),∃u1 u2 p1 p1' p2 p2' p3:F0,u1∈({7,8,10}:S0)/\u2∈({7,8,10}:S0)/\u1≠u3/\u2≠u3/\u1≠u2/\aH u1 p1/\aH u1 p1'/\p1≠p1'/\p1≠0/\p1'≠0/\aH 9 p1/\aH u2 p2/\aH u2 p2'/\p2≠p2'/\p2≠0/\p2'≠0/\aH 9 p2/\aH 9 p3/\p1≠p2/\p1≠p3/\p2≠p3/\¬aH p2 p1'/\¬aH p3 p1'/\¬aH p3 p2'/\p1∉({0,7,8,10}:S0)/\p2∉({0,7,8,10}:S0)/\u1≠9/\u2≠9:=by
 intro u3 h;simp only[mI,mS] at h;rcases h with rfl|rfl|rfl
 ·exact ⟨8,10,6,2,5,4,1,o⟩
 ·exact ⟨7,10,1,3,5,4,6,o⟩
 ·exact ⟨7,8,1,3,6,2,5,o⟩
lemma nC {D:aJ}(h:a9 14 D)(hD:be D){b:F0->Nat}(ht:dz 14 D b){a5:F0->A0}(l:ch 14 HG D a5)(b5:br 14 D=(aW 14 D).card+1)(h0:(0:F0)∈aN 14 D)(es:∀x:F0,(aG 14 D x).card≤3)(a0:∀t:F0,a5 0∈aG 14 D t->t∈({7,8,10}:S0)){u3:F0}(g3:({7,8,10}:S0).filter (λu=>(aG 14 D u).card=3)={u3}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have a2:u3∈({7,8,10}:S0).filter (λu=>(aG 14 D u).card=3):=(by rw[g3];simp);have a3:u3∈({7,8,10}:S0):=(mF.1 a2).1;have hA:(aG 14 D u3).card=3:=(mF.1 a2).2;have a4:∀x:F0,x∉({0,7,8,10}:S0)->(aG 14 D x).card≤2:=by
  intro x hx;by_contra hH;obtain ⟨P,Q,hy,m⟩:=fw hG h hC b ht b5 {u3,x} ⟨u3,ab⟩
   (λv hv=>by
    rcases mI.1 hv with rfl|hv
    ·omega
    ·rw[mS.1 hv];omega)
  have e0:P≠Q:=λk=>hy (kA Prod.fst k)
  have f1:a5 0∈aG 14 D u3:=bd l h0 (by
   have h':=a3;simp only[mI,mS] at h'
   rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl)
  have b1:a5 0≠P:=λk=>
   hx ((by decide +kernel:∀t∈({7,8,10}:S0),t∈({0,7,8,10}:S0)) x (a0 x (k▸(m x ab).1)))
  have bm:a5 0≠Q:=λk=>
   hx ((by decide +kernel:∀t∈({7,8,10}:S0),t∈({0,7,8,10}:S0)) x (a0 x (k▸(m x ab).2)))
  have fi:aG 14 D u3={a5 0,P,Q}:=(eS (λe k=>by
    simp only[mI,mS] at k;rcases k with rfl|rfl|rfl
    ·exact f1
    ·exact (m u3 ab).1
    ·exact (m u3 ab).2)
    (by rw[cI (by simp[b1,bm]),cP e0];omega)).symm
  obtain ⟨a,b6,g5,hF,g8⟩:=(by decide +kernel:∀u∈({7,8,10}:S0),∀x:F0,x∉({0,7,8,10}:S0)->∃a∈({7,8,10}:S0),a≠u/\a≠x/\¬aH a x) u3 a3 x hx
  have g4:u3≠x:=λk=>hx (by
   rw[← k];have h':=a3;simp only[mI,mS] at h'
   rcases h' with r|r|r<;>rw[r]<;>decide)
  obtain ⟨e,a7,e7,hk⟩:=bB h hD (nS g5) g4 g8;rw[fi,mI,mI,mS] at a7;rcases a7 with rfl|rfl|rfl
  ·exact e7 ((l.1 0 h0).2.2.1 a (by
    have h':=b6;simp only[mI,mS] at h'
    rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl))
  ·exact hk (aP.1 (m x ab).1).2.1
  ·exact hk (aP.1 (m x ab).2).2.1
 obtain ⟨u1,u2,p1,hw,p2,ho,p3,hi,g2,ej,d2,-,c6,b8,eb,hf,c2,g9,ec,b2,c7,g0,c5,f2,hh,g7,f0,fz,ev,e4,e5,eu,c3,hb,hj⟩:=oq u3 a3;have f3:∀u p p':F0,u∈({7,8,10}:S0)->u≠u3->aH u p->aH u p'->p≠p'->p≠0->p'≠0->aH 9 p->u≠9->p∉({0,7,8,10}:S0)->∃Q,aI Q∈aG 14 D 9/\p∈O 14 D (W D Q)/\∀a,a≠p->¬aH a p'->a∉O 14 D (W D Q):=by
  intro u p p' c8 hc hn hg g1 hr fl hs hq fc;have ea:(aG 14 D u).card≤2:=by
   have hE:(aG 14 D u).card≠3:=λh3=>
    hc (mS.1 (g3▸mF.2 ⟨c8,h3⟩))
   have:=es u;omega
  obtain ⟨Z,-,hm,hp⟩:=ps h hD l h0 (by
   have h':=c8;simp only[mI,mS] at h'
   rcases h' with r|r|r<;>rw[r]<;>decide)
   (bd l h0 (by
    have h':=c8;simp only[mI,mS] at h'
    rcases h' with r|r|r<;>rw[r]<;>exact (aK _ _).1 rfl)) ea
  obtain ⟨e1,c0,ca,-⟩:=bp hG hS hC hn;obtain ⟨e2,cb,ct,-⟩:=bp hG hS hC hg;rw[hm,mI,mS] at c0 cb;have b0:aI Z∈aG 14 D p:=(c0.resolve_left (λk=>hr (bx l h0 (k▸ca))))▸ca;have a6:aI Z∈aG 14 D p':=(cb.resolve_left (λk=>fl (bx l h0 (k▸ct))))▸ct;obtain ⟨Q,hl,d0,-⟩:=bp hG hS hC (bh hs);have g6:Q≠aI Z:=λk=>by rw[k,aT] at d0;exact hp 9 (nS hq) d0
  have hz:aG 14 D p={aI Z,Q}:=(eS (λe k=>by
    rcases mI.1 k with rfl|k
    ·exact b0
    ·rw[mS.1 k];exact hl)
    (by rw[cP g6.symm];exact a4 p fc)).symm
  refine ⟨Q,d0,(aP.1 hl).2.1,λa ha hap' haQ=>?_⟩;obtain ⟨e,a7,e7,gs⟩:=bB h hD (nS ha) g1 hap';rw[hz,mI,mS] at a7;rcases a7 with rfl|rfl
  ·exact gs (aP.1 a6).2.1
  ·exact e7 haQ
 obtain ⟨Q1,d1,hB,a8⟩:=f3 u1 p1 hw hi ej c6 b8 eb hf c2 g9 hb eu;obtain ⟨Q2,er,hd,ez⟩:=f3 u2 p2 ho g2 d2 ec b2 c7 g0 c5 f2 hj c3
 have et:aI Q1≠aI Q2:=λk=>
  a8 p2 g7.symm ev (by rw[← aT Q1,k,aT];exact hd)
 have hu:aG 14 D 9={aI Q1,aI Q2}:=(eS (λe k=>by
   rcases mI.1 k with rfl|k
   ·exact d1
   ·rw[mS.1 k];exact er)
   (by rw[cP et];exact a4 9 o)).symm
 obtain ⟨e3,c1,a1,-⟩:=bp hG hS hC hh;rw[hu,mI,mS] at c1;rcases c1 with rfl|rfl
 ·exact a8 p3 f0.symm e4 (by rw[aT] at a1;exact (aP.1 a1).2.1)
 ·exact ez p3 fz.symm e5 (by rw[aT] at a1;exact (aP.1 a1).2.1)
def lS (p1 p1' p2 p2' q1 q2 l0:F0):Bool:=
 decide (p1∈({1,2,3,4,5,6}:S0)/\p1'∈({1,2,3,4,5,6}:S0)/\
  p2∈({1,2,3,4,5,6}:S0)/\p2'∈({1,2,3,4,5,6}:S0)/\
  q1∈({1,2,3,4,5,6}:S0)/\q2∈({1,2,3,4,5,6}:S0)/\
  l0∈({9,11,12,13}:S0)/\
  cv p1=p1'/\cv p2=p2'/\cv q1=q2/\bS p1≠bS p2/\
  aH l0 p1/\aH l0 p2/\aH l0 q1/\
  q1∉({p1,p1',p2,p2'}:S0)/\l0∉({p1,p1',p2,p2'}:S0)/\
  p1≠p2/\p1≠q1/\p2≠q1/\p1'≠p2/\¬aH p1' p2)
set_option maxHeartbeats 400000 in
lemma pP {D:aJ}(h:a9 14 D)(hD:be D){b:F0->Nat}(ks:dz 14 D b){qc:F0->A0}(e4:ch 14 HG D qc){u0:P0}(j0:aR 14 D b={u0})(qO:bH 14 D≤14)(hs:br 14 D=(aW 14 D).card+1)(h0:(0:F0)∈aN 14 D)(ja:∀x:F0,x≠0->x∈aW 14 D)(hZ:∀x:F0,(aG 14 D x).card≤3)(hX:∀u∈({7,8,10}:S0),(aG 14 D u).card≤2):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have hb:=cX ks;have hj:∀u∈({7,8,10}:S0),∃Z,aG 14 D u={qc 0,Z}/\(∀t,t≠u->Z∉aG 14 D t)/\∀w,aH u w->w≠0->aI Z∈aG 14 D w:=by
  intro u hu
  obtain ⟨Z,-,p8,jb⟩:=ps h hD e4 h0 (by
   have h':=hu;simp only[mI,mS] at h'
   rcases h' with h1|h1|h1<;>rw[h1]<;>decide)
   (bd e4 h0 (by
    have h':=hu;simp only[mI,mS] at h'
    rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl)) (hX u hu)
  refine ⟨Z,p8,jb,λw hwu hw0=>?_⟩;obtain ⟨e,lc,b2,-⟩:=bp hG hS hC hwu;rw[p8,mI,mS] at lc;exact (lc.resolve_left (λhh=>hw0 (bx e4 h0 (hh▸b2))))▸b2
 obtain ⟨Z7,qP,fz,qg⟩:=hj 7 o;obtain ⟨Z8,qz,hF,n5⟩:=hj 8 o;obtain ⟨Z10,hE,lb,hU⟩:=hj 10 o
 let H3:=({1,2,3,4,5,6,9,11,12,13}:S0).filter (λx=>(aG 14 D x).card=3)
 have a6:∀x∈({1,2,3,4,5,6,9,11,12,13}:S0),x∉H3->(aG 14 D x).card≤2:=λx hx hnx=>by
  have cb:(aG 14 D x).card≠3:=λh3=>hnx (mF.2 ⟨hx,h3⟩);have:=hZ x;omega
 have a4:∀p l:F0,p∈({1,2,3,4,5,6}:S0)->p∉H3->l∈({9,11,12,13}:S0)->aH l p->∃Q,aI Q∈aG 14 D l/\p∈O 14 D (W D Q)/\∀t∈({1,2,3,4,5,6}:S0),t≠p->t∉O 14 D (W D Q):=by
  intro p l hp ql hl qy;have nR:p∈({1,2,3,4,5,6,9,11,12,13}:S0):=(by have h':=hp;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>decide);have b0:bS p∈({7,8,10}:S0)/\cv p∈({1,2,3,4,5,6}:S0)/\cv p≠p/\aH (bS p) p/\aH (bS p) (cv p)/\p≠0/\cv p≠0/\bS p≠l:=(by have h':=hp;have p0:=hl;simp only[mI,mS] at h' p0;rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>rcases p0 with rfl|rfl|rfl|rfl<;>decide);obtain ⟨Z,-,jb,ll⟩:=hj (bS p) b0.1;obtain ⟨Q,p6,i5,-⟩:=bp hG hS hC (bh qy);have l3:Q≠aI Z:=λhe=>by rw[he,aT] at i5;exact jb l (nS b0.2.2.2.2.2.2.2) i5
  have ix:aG 14 D p={aI Z,Q}:=(eS (λe he=>by
    rcases mI.1 he with rfl|he
    ·exact ll p b0.2.2.2.1 b0.2.2.2.2.2.1
    ·rw[mS.1 he];exact p6)
    (by rw[cP l3.symm];exact a6 p nR ql)).symm
  refine ⟨Q,i5,(aP.1 p6).2.1,λt ht htp htQ=>?_⟩;have ik:=(by decide +kernel:∀a∈({1,2,3,4,5,6}:S0),∀c∈({1,2,3,4,5,6}:S0),¬aH a c) t ht (cv p) b0.2.1;obtain ⟨e,b6,qq,qb⟩:=bB h hD (nS htp) (nS b0.2.2.1) ik;rw[ix,mI,mS] at b6;rcases b6 with rfl|rfl
  ·exact qb (aP.1 (ll (cv p) b0.2.2.2.2.1 b0.2.2.2.2.2.2.1)).2.1
  ·exact qq htQ
 have ec:∀l∈({9,11,12,13}:S0),l∈H3\/2≤((univ.filter (λp=>aQ l p=true))∩H3).card:=by
  intro l hl;by_contra ca;rw[nO] at ca;have oz:l∈({1,2,3,4,5,6,9,11,12,13}:S0):=(by have h':=hl;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl<;>decide)
  let Nl:=univ.filter (λp:F0=>aQ l p=true)
  have qK:Nl.card=3:=(by have h':=hl;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl<;>decide);have qG:¬(2≤(Nl∩H3).card):=ca.2;have qM:2≤(Nl \ H3).card:=(by have:=cD Nl H3;omega);obtain ⟨p1,b5,p2,c5,ct⟩:=oC.1 (by omega:1<(Nl \ H3).card);have ev:=(mD.1 b5).1;have ko:=(mD.1 b5).2;have es:=(mD.1 c5).1;have iz:=(mD.1 c5).2;have c7:∀p∈Nl,p∈({1,2,3,4,5,6}:S0)/\aH l p:=λp hp=>by
   have ha:=(aK l p).1 (mF.1 hp).2;exact ⟨(by decide +kernel:∀l∈({9,11,12,13}:S0),∀p:F0,aH l p->p∈({1,2,3,4,5,6}:S0)) l hl p ha,ha⟩
  obtain ⟨p3,f3,m3,qa⟩:∃p3∈Nl,p3≠p1/\p3≠p2:=by
   have lw:({p1,p2}:S0)⊆Nl:=by simp[iS,ev,es]
   have:(Nl \ {p1,p2}).Nonempty:=cO.1 (by
    have:=sP lw;rw[cP ct] at this;omega)
   obtain ⟨p3,g6⟩:=this;rw[mD,mI,mS,nO] at g6;exact ⟨p3,g6.1,g6.2.1,g6.2.2⟩
  obtain ⟨Q1,n7,m2,a7⟩:=a4 p1 l (c7 p1 ev).1 ko hl (c7 p1 ev).2;obtain ⟨Q2,qi,m8,id⟩:=a4 p2 l (c7 p2 es).1 iz hl (c7 p2 es).2
  have k2:aI Q1≠aI Q2:=λhe=>
   a7 p2 (c7 p2 es).1 ct.symm (by rw[← aT Q1,he,aT];exact m8)
  have qv:aG 14 D l={aI Q1,aI Q2}:=(eS (λe he=>by
    rcases mI.1 he with rfl|he
    ·exact n7
    ·rw[mS.1 he];exact qi)
    (by rw[cP k2];exact a6 l oz ca.1)).symm
  obtain ⟨e3,hO,eb,-⟩:=bp hG hS hC (c7 p3 f3).2;rw[qv,mI,mS] at hO;rcases hO with rfl|rfl
  ·exact a7 p3 (c7 p3 f3).1 m3 (by rw[aT] at eb;exact (aP.1 eb).2.1)
  ·exact id p3 (c7 p3 f3).1 qa (by rw[aT] at eb;exact (aP.1 eb).2.1)
 have hd:H3.Nonempty:=by
  rcases ec 9 o with h9|qD
  ·exact ⟨9,h9⟩
  ·obtain ⟨p,hp⟩:=cO.1 (show 0<((univ.filter (λp=>aQ 9 p=true))∩H3).card by omega);exact ⟨p,(mN.1 hp).2⟩
 have c6:∀x∈H3,x∈O 14 D u0.1:=λx hx=>by
  have qN:=(mF.1 hx).2;have:=ci h hD b hb x;obtain ⟨r,hr⟩:=cO.1 (show 0<(ru D b x).card by omega);have pr:r=u0:=mS.1 (j0▸(bb.1 hr).1);exact pr▸(bb.1 hr).2
 have ho:∀c∈H3,(H3.card-1)+((univ.filter (λn:F0=>aQ c n=true)) \ H3).card≤6:=by
  intro c hc;have f0:=(mF.1 hc).1;have qt:c≠0:=(by have h':=f0;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>decide);have qB:=dl h hD b ks (ja c qt) (H3.erase c)
   ((univ.filter (λn:F0=>aQ c n=true)) \ H3) ∅
   (λx hx=>by
    obtain ⟨qr,qe⟩:=mE.1 hx;have k1:=(mF.1 qe).1;have qo:x≠0:=(by have h':=k1;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>decide)
    exact ⟨ja x qo,qr,λu hu _=>by
     have qd:u=u0:=mS.1 (j0▸hu)
     rw[qd];exact c6 c hc,
     u0.1,c6 x qe,c6 c hc⟩)
   (λn hn=>by
    obtain ⟨qs,qu⟩:=mD.1 hn;have qj:=(aK c n).1 (mF.1 qs).2;have qn:n≠0:=λh0n=>by
     subst h0n;have h':=f0;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>exact absurd qj o
    exact ⟨ja n qn,qj,λhm=>qu (mO hm)⟩)
   (λ_ hz=>(nE _ hz).elim)
  have m1:(ru D b c).card=1:=by
   have:=ci h hD b hb c;have:=(mF.1 hc).2
   have:(ru D b c).card≤(aR 14 D b).card:=cF _ _
   rw[j0,cS] at this;omega
  rw[cE hc,ad,m1] at qB;omega
 obtain ⟨P,Q,qp,k⟩:=fw hG h hC b ks hs H3 hd
  (λx hx=>by have:=(mF.1 hx).2;omega)
 have d2:P≠Q:=λhe=>qp (kA Prod.fst he);have a5:aI Z7≠aI Z8/\aI Z7≠aI Z10/\aI Z8≠aI Z10:=⟨λhe=>fz 8 o (by rw[← aT Z7,he,aT,qz];simp),λhe=>fz 10 o (by rw[← aT Z7,he,aT,hE];simp),λhe=>hF 10 o (by rw[← aT Z8,he,aT,hE];simp)⟩
 let Zof (a:F0):A0:=if a=7 then aI Z7 else if a=8 then aI Z8 else aI Z10
 have a0:∀p∈({1,2,3,4,5,6}:S0),Zof (bS p)∈aG 14 D p/\Zof (bS p)∈aG 14 D (cv p)/\∀l∈({9,11,12,13}:S0),∀e,aI e∈aG 14 D l->e≠Zof (bS p):=by
  have e0:∀u∈({7,8,10}:S0),(∀w,aH u w->w≠0->Zof u∈aG 14 D w)/\(∀l∈({9,11,12,13}:S0),∀e,aI e∈aG 14 D l->e≠Zof u):=by
   intro u hu;simp only[mI,mS] at hu;have e5:∀u'∈({7,8,10}:S0),∀l∈({9,11,12,13}:S0),l≠u':=aa
   rcases hu with rfl|rfl|rfl
   ·exact ⟨qg,λl hl e b2 b1=>fz l (e5 7 o l hl) (by rw[b1] at b2;exact aT Z7▸b2)⟩
   ·exact ⟨n5,λl hl e b2 b1=>hF l (e5 8 o l hl) (by rw[b1] at b2;exact aT Z8▸b2)⟩
   ·exact ⟨hU,λl hl e b2 b1=>lb l (e5 10 o l hl) (by rw[b1] at b2;exact aT Z10▸b2)⟩
  intro p hp;have hg:=(by decide +kernel:∀p∈({1,2,3,4,5,6}:S0),bS p∈({7,8,10}:S0)/\aH (bS p) p/\p≠0/\aH (bS p) (cv p)/\cv p≠0) p hp;exact ⟨(e0 _ hg.1).1 p hg.2.1 hg.2.2.1,(e0 _ hg.1).1 _ hg.2.2.2.1 hg.2.2.2.2,(e0 _ hg.1).2⟩
 have et:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),Zof a=Zof c->a=c:=by
  intro a ha c hc b1;simp only[mI,mS] at ha hc;rcases ha with rfl|rfl|rfl<;>rcases hc with rfl|rfl|rfl
  ·rfl
  ·exact absurd b1 a5.1
  ·exact absurd b1 a5.2.1
  ·exact absurd b1.symm a5.1
  ·rfl
  ·exact absurd b1 a5.2.2
  ·exact absurd b1.symm a5.2.1
  ·exact absurd b1.symm a5.2.2
  ·rfl
 have hk:∃a1∈({7,8,10}:S0),∃a2∈({7,8,10}:S0),∀p∈H3,p.val<7->bS p≠a1->bS p≠a2->∀y∈H3,y≠p->y=cv p\/aQ (cv p) y=true:=by
  let a1:F0:=if P=aI Z7 then 7 else if P=aI Z8 then 8 else 10
  let a2:F0:=if Q=aI Z7 then 7 else if Q=aI Z8 then 8 else 10
  have c1:∀X:A0,∀a∈({7,8,10}:S0),a≠(if X=aI Z7 then 7 else if X=aI Z8 then 8 else 10)->Zof a≠X:=by
   intro X a ha cb he;simp only[mI,mS] at ha;rcases ha with rfl|rfl|rfl
   ·have h1:X=aI Z7:=he.symm;rw[h1] at cb;simp only[↓reduceIte] at cb;exact cb rfl
   ·have h1:X=aI Z8:=he.symm;have h2:aI Z8≠aI Z7:=a5.1.symm;rw[h1] at cb;simp only[h2,↓reduceIte] at cb;exact cb rfl
   ·have h1:X=aI Z10:=he.symm;have h2:aI Z10≠aI Z7:=a5.2.1.symm;have h3:aI Z10≠aI Z8:=a5.2.2.symm;rw[h1] at cb;simp only[h2,h3,↓reduceIte] at cb;exact cb rfl
  refine ⟨a1,by dsimp only[a1];split_ifs<;>decide,a2,by dsimp only[a2];split_ifs<;>decide,λp hp hp7 hpa1 hpa2 y hy hyp=>?_⟩;have h8:p∈({1,2,3,4,5,6}:S0):=(by decide +kernel:∀x∈({1,2,3,4,5,6,9,11,12,13}:S0),x.val<7->x∈({1,2,3,4,5,6}:S0)) p (mF.1 hp).1 hp7;have a8:bS p∈({7,8,10}:S0):=(by decide +kernel:∀x∈({1,2,3,4,5,6}:S0),bS x∈({7,8,10}:S0)) p h8;have e1:Zof (bS p)≠P:=c1 P (bS p) a8 hpa1;have g1:Zof (bS p)≠Q:=c1 Q (bS p) a8 hpa2;have d0:=a0 p h8
  have ix:aG 14 D p={P,Q,Zof (bS p)}:=(eS (λe he=>by
    simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
    ·exact (k p hp).1
    ·exact (k p hp).2
    ·exact d0.1)
    (by rw[cI (by simp[d2,e1.symm]),cP g1.symm];have:=(mF.1 hp).2;omega)).symm
  by_contra ca;rw[nO] at ca;have f1:cv p≠p:=(by decide +kernel:∀x∈({1,2,3,4,5,6}:S0),cv x≠x) p h8;obtain ⟨e,b6,qf,qh⟩:=bB h hD (nS f1) (nS hyp)
   (bw.1 (bE.2 ca.2))
  rw[ix,mI,mI,mS] at b6;rcases b6 with rfl|rfl|rfl
  ·exact qh (aP.1 (k y hy).1).2.1
  ·exact qh (aP.1 (k y hy).2).2.1
  ·exact qf (aP.1 d0.2.1).2.1
 obtain ⟨m,hm⟩:=ok H3 (fS _ _);have g9:iJ m=true:=(by simp only[iJ,hm,bA,dT];exact ⟨⟨ec,ho⟩,hk⟩);have hK:=ox m g9;rw[hm] at hK;have a3:∀p1 hw p2 hR q1 q2 l0:F0,H3={p1,hw,p2,hR}->lS p1 hw p2 hR q1 q2 l0=true->False:=by
  intro p1 hw p2 hR q1 q2 l0 er g9;simp only[lS,dT] at g9;obtain ⟨b5,qF,c5,qI,qC,qQ,hf,hH,qJ,qE,h7,nB,n4,l4,k3,h5,ct,p7,n1,qw,hv⟩:=g9;have h4:q1∉H3:=er.symm▸k3;have hQ:l0∉H3:=er.symm▸h5;have c8:p1∈H3:=by rw[er];simp
  have hN:p2∈H3:=by rw[er];simp
  have c0:∀pa pb:F0,pa∈({1,2,3,4,5,6}:S0)->pb∈({1,2,3,4,5,6}:S0)->pa∈H3->pb∈H3->pa≠pb->Zof (bS pa)=P\/Zof (bS pa)=Q:=by
   intro pa pb hY qA e7 hA ls;by_contra ca;rw[nO] at ca
   have n8:aG 14 D pa={P,Q,Zof (bS pa)}:=(eS (λe he=>by
     simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
     ·exact (k pa e7).1
     ·exact (k pa e7).2
     ·exact (a0 pa hY).1)
     (by rw[cI (by simp[d2,nS ca.1]),cP (nS ca.2)];have:=(mF.1 e7).2;omega)).symm
   have hg:=(by decide +kernel:∀a∈({1,2,3,4,5,6}:S0),∀c∈({1,2,3,4,5,6}:S0),cv a≠a/\¬aH (cv a) c) pa hY pb qA;obtain ⟨e,b6,hW,g5⟩:=bB h hD (nS hg.1) ls hg.2;rw[n8,mI,mI,mS] at b6;rcases b6 with rfl|rfl|rfl
   ·exact g5 (aP.1 (k pb hA).1).2.1
   ·exact g5 (aP.1 (k pb hA).2).2.1
   ·exact hW (aP.1 (a0 pa hY).2.1).2.1
  have d1:=c0 p1 p2 b5 c5 c8 hN ct;have ea:=c0 p2 p1 c5 b5 hN c8 ct.symm;have a8:∀p∈({1,2,3,4,5,6}:S0),bS p∈({7,8,10}:S0):=aa
  have b8:Zof (bS p1)≠Zof (bS p2):=λhe=>
   h7 (et _ (a8 p1 b5) _ (a8 p2 c5) he)
  have hP:(P=Zof (bS p1)/\Q=Zof (bS p2))\/(P=Zof (bS p2)/\Q=Zof (bS p1)):=by
   rcases d1 with h1|h1<;>rcases ea with h2|h2
   ·exact (b8 (h1.trans h2.symm)).elim
   ·exact oL ⟨h1.symm,h2.symm⟩
   ·exact oR ⟨h2.symm,h1.symm⟩
   ·exact (b8 (h1.trans h2.symm)).elim
  obtain ⟨R1,hM,fc,-⟩:=bp hG hS hC (bh nB);have f2:R1≠Zof (bS p1):=(a0 p1 b5).2.2 l0 hf R1 fc;have g0:R1≠Zof (bS p2):=(a0 p2 c5).2.2 l0 hf R1 fc;have nl:aG 14 D p1={Zof (bS p1),Zof (bS p2),R1}:=by
   have g4:Zof (bS p2)∈aG 14 D p1:=by
    rcases hP with ⟨-,rfl⟩|⟨rfl,-⟩
    ·exact (k p1 c8).2
    ·exact (k p1 c8).1
   exact (eS (λe he=>by
    simp only[mI,mS] at he;rcases he with rfl|rfl|rfl
    ·exact (a0 p1 b5).1
    ·exact g4
    ·exact hM)
    (by rw[cI (by simp[b8,f2.symm]),cP g0.symm];have:=(mF.1 c8).2;omega)).symm
  obtain ⟨Qq,lo,qH,fi⟩:=a4 q1 l0 qC h4 hf l4
  have hq:aI Qq≠aI R1:=λhe=>
   fi p1 b5 p7 (by rw[← aT Qq,he,aT];exact (aP.1 hM).2.1)
  have hT:l0∈({1,2,3,4,5,6,9,11,12,13}:S0):=(by decide +kernel:∀l∈({9,11,12,13}:S0),l∈({1,2,3,4,5,6,9,11,12,13}:S0)) l0 hf
  have p9:aG 14 D l0={aI Qq,aI R1}:=(eS (λe he=>by
    rcases mI.1 he with rfl|he
    ·exact lo
    ·rw[mS.1 he];exact fc)
    (by rw[cP hq];exact a6 l0 hT hQ)).symm
  obtain ⟨e2,hI,ej,-⟩:=bp hG hS hC n4;rw[p9,mI,mS] at hI;rcases hI with rfl|rfl
  ·exact fi p2 c5 n1 (by rw[aT] at ej;exact (aP.1 ej).2.1)
  ·rw[aT] at ej;have g8:hw≠p1:=hH▸(by decide +kernel:∀x∈({1,2,3,4,5,6}:S0),cv x≠x) p1 b5;obtain ⟨e,b6,i0,g3⟩:=bB h hD (nS g8) ct hv;rw[nl,mI,mI,mS] at b6;rcases b6 with rfl|rfl|rfl
   ·exact i0 (aP.1 (hH▸(a0 p1 b5).2.1)).2.1
   ·exact g3 (aP.1 (a0 p2 c5).1).2.1
   ·exact g3 (aP.1 ej).2.1
 rcases hK with i4|i3|k7|iy
 ·have bm:∀p∈({1,2,3,4,5,6}:S0),p∉H3:=λp hp hm=>by
   rw[i4] at hm;exact (by decide +kernel:∀x∈({1,2,3,4,5,6}:S0),x∉({9,11,12,13}:S0)) p hp hm
  obtain ⟨Q1,i7,m2,a7⟩:=a4 1 9 o (bm 1 o) o ((aK 9 1).1 rfl);obtain ⟨Q5,ih,mt,c2⟩:=a4 5 9 o (bm 5 o) o ((aK 9 5).1 rfl);obtain ⟨Q6,h6,hB,qx⟩:=a4 6 9 o (bm 6 o) o ((aK 9 6).1 rfl);obtain ⟨Q3,hi,hJ,gs⟩:=a4 3 11 o (bm 3 o) o ((aK 11 3).1 rfl);obtain ⟨Q4,g7,ez,k0⟩:=a4 4 11 o (bm 4 o) o ((aK 11 4).1 rfl);obtain ⟨Q6',eu,c3,qk⟩:=a4 6 11 o (bm 6 o) o ((aK 11 6).1 rfl);have la:(9:F0)∈H3:=by rw[i4];decide
  have g2:(11:F0)∈H3:=by rw[i4];decide
  have hL:∀l∈H3,∀a b c:A0,a∈aG 14 D l->b∈aG 14 D l->c∈aG 14 D l->a≠b->a≠c->b≠c->aG 14 D l={a,b,c}:=λl hl a b c ha hb hc nab nac nbc=>
   (eS (λe he=>by simp only[mI,mS] at he;rcases he with rfl|rfl|rfl<;>assumption) (by rw[cI (by simp[nab,nac]),cP nbc];have:=(mF.1 hl).2;omega)).symm
  have qm:=hL 9 la _ _ _ i7 ih h6
   (λhe=>a7 5 o o (by rw[← aT Q1,he,aT];exact mt))
   (λhe=>a7 6 o o (by rw[← aT Q1,he,aT];exact hB))
   (λhe=>c2 6 o o (by rw[← aT Q5,he,aT];exact hB))
  have l7:=hL 11 g2 _ _ _ hi g7 eu
   (λhe=>gs 4 o o (by rw[← aT Q3,he,aT];exact ez))
   (λhe=>gs 6 o o (by rw[← aT Q3,he,aT];exact c3))
   (λhe=>k0 6 o o (by rw[← aT Q4,he,aT];exact c3))
  have n3:∀e,e∈aG 14 D 9->e∈aG 14 D 11->e=aI Q6:=by
   intro e n2 fl;rw[qm,mI,mI,mS] at n2;rw[l7,mI,mI,mS] at fl;rcases n2 with rfl|rfl|rfl
   ·rcases fl with h1|h1|h1
    ·exact (a7 3 o o (by rw[← aT Q1,h1,aT];exact hJ)).elim
    ·exact (a7 4 o o (by rw[← aT Q1,h1,aT];exact ez)).elim
    ·exact (a7 6 o o (by rw[← aT Q1,h1,aT];exact c3)).elim
   ·rcases fl with h1|h1|h1
    ·exact (c2 3 o o (by rw[← aT Q5,h1,aT];exact hJ)).elim
    ·exact (c2 4 o o (by rw[← aT Q5,h1,aT];exact ez)).elim
    ·exact (c2 6 o o (by rw[← aT Q5,h1,aT];exact c3)).elim
   ·rfl
  exact d2 ((n3 P (k 9 la).1 (k 11 g2).1).trans (n3 Q (k 9 la).2 (k 11 g2).2).symm)
 ·exact a3 1 3 5 4 6 2 9 (by rw[i3];decide) rfl
 ·exact a3 1 3 6 2 5 4 9 (by rw[k7];decide) rfl
 ·exact a3 5 4 6 2 1 3 9 (by rw[iy];decide) rfl
def kI (lb l1 l2 l3 p1 p2 p3 q1 q2 q3:F0):Bool:=
 decide (l1∈({9,11,12,13}:S0)/\l2∈({9,11,12,13}:S0)/\
  l3∈({9,11,12,13}:S0)/\l1≠lb/\l2≠lb/\l3≠lb/\
  p1∈({1,2,3,4,5,6}:S0)/\p2∈({1,2,3,4,5,6}:S0)/\
  p3∈({1,2,3,4,5,6}:S0)/\q1∈({1,2,3,4,5,6}:S0)/\
  q2∈({1,2,3,4,5,6}:S0)/\q3∈({1,2,3,4,5,6}:S0)/\
  q1∉({p1,p2,p3}:S0)/\q2∉({p1,p2,p3}:S0)/\q3∉({p1,p2,p3}:S0)/\
  aH 7 p1/\aH 7 q1/\aH 8 p2/\aH 8 q2/\aH 10 p3/\aH 10 q3/\
  aH l1 p1/\aH l1 q2/\aH l1 q3/\¬aH l1 q1/\
  aH l2 p2/\aH l2 q1/\aH l2 q3/\aH l3 p3/\aH l3 q1/\aH l3 q2/\
  p1≠p2/\p1≠p3/\p2≠p3/\
  p1≠q2/\p1≠q3/\p2≠q1/\p2≠q3/\p3≠q1/\p3≠q2/\¬aH 7 p3)
set_option maxHeartbeats 800000 in
lemma nn {D:aJ}(h:a9 14 D)(hD:be D)(hT:fu D){b:F0->Nat}(hd:dz 14 D b){a0:F0->A0}(a4:ch 14 HG D a0){u0:P0}(lc:aR 14 D b={u0})(t0:bu 14 D=0)(hI:aN 14 D={0})(pa:br 14 D=(aW 14 D).card+1)(h0:(0:F0)∈aN 14 D)(qq:∀x:F0,x≠0->x∈aW 14 D)(rf:∀x:F0,(aG 14 D x).card≤3)(eb:(a0 0).1=26)(fi:∀t:F0,t∈O 14 D (W D (a0 0))<->aH 0 t)(ih:∀t:F0,a0 0∈aG 14 D t->t∈({7,8,10}:S0))(qF:2≤(({7,8,10}:S0).filter (λu=>(aG 14 D u).card=3)).card):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have hb:=cX hd;have u7:u0∈aR 14 D b:=by rw[lc];simp
 let U3:=({7,8,10}:S0).filter (λu=>(aG 14 D u).card=3)
 have v8:2≤U3.card:=qF;obtain ⟨u1,t6,u2,t9,c8⟩:=oC.1 (show 1<U3.card by omega);have b2:=(mF.1 t6).1;have uM:=(mF.1 t6).2;have ca:=(mF.1 t9).1;have vc:=(mF.1 t9).2;obtain ⟨P,Q,te,a2⟩:=fw hG h hC b hd pa {u1,u2} ⟨u1,ab⟩
  (λv hv=>by rcases mI.1 hv with rfl|hv;omega;rw[mS.1 hv];omega)
 have qO:P≠Q:=λk=>te (kA Prod.fst k);have h9:a0 0=P\/a0 0=Q:=by
  by_contra l0;rw[nO] at l0
  have vP:a0 0∈aG 14 D u1:=bd a4 h0 (by
   have h':=b2;simp only[mI,mS] at h'
   rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl)
  have qV:aG 14 D u1={a0 0,P,Q}:=(eS (λe k=>by
    simp only[mI,mS] at k;rcases k with rfl|rfl|rfl
    ·exact vP
    ·exact (a2 u1 ab).1
    ·exact (a2 u1 ab).2)
    (by rw[cI (by simp[l0.1,l0.2]),cP qO];omega)).symm
  obtain ⟨u3,l7,rd,ud⟩:=(by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),a≠c->∃u3∈({7,8,10}:S0),u3≠a/\u3≠c) u1 b2 u2 ca c8;obtain ⟨e,b0,wb,vl⟩:=bB h hD (nS rd) c8
   ((by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),¬aH a c) u3 l7 u2 ca)
  rw[qV,mI,mI,mS] at b0;rcases b0 with rfl|rfl|rfl
  ·exact wb ((a4.1 0 h0).2.2.1 u3 (by
    have h':=l7;simp only[mI,mS] at h'
    rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl))
  ·exact vl (aP.1 (a2 u2 ab).1).2.1
  ·exact vl (aP.1 (a2 u2 ab).2).2.1
 obtain ⟨E,hE,b1,hi,d0⟩:∃E:A0,E.1≠(a0 0).1/\E∈aG 14 D u1/\E∈aG 14 D u2/\∀x:F0,3≤(aG 14 D x).card->a0 0∈aG 14 D x/\E∈aG 14 D x:=by
  have hA:∀x:F0,3≤(aG 14 D x).card->P∈aG 14 D x/\Q∈aG 14 D x:=by
   intro x hx;obtain ⟨P',Q',ut,c7⟩:=fw hG h hC b hd pa {u1,u2,x}
    ⟨u1,ab⟩ (λv hv=>by
     simp only[mI,mS] at hv
     rcases hv with rfl|rfl|rfl<;>omega)
   have h3:∀e,e∈aG 14 D u1->e∈aG 14 D u2->e=P\/e=Q:=by
    intro e e5 et;by_contra l0;rw[nO] at l0
    have qV:aG 14 D u1={P,Q,e}:=(eS (λa ha=>by
      simp only[mI,mS] at ha;rcases ha with rfl|rfl|rfl
      ·exact (a2 u1 ab).1
      ·exact (a2 u1 ab).2
      ·exact e5)
      (by rw[cI (by simp[qO,nS l0.1]),cP (nS l0.2)];omega)).symm
    obtain ⟨u3,l7,rd,ud⟩:=(by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),a≠c->∃u3∈({7,8,10}:S0),u3≠a/\u3≠c) u1 b2 u2 ca c8;obtain ⟨a,us,-,qn⟩:=bB h hD (nS rd) c8
     ((by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),¬aH a c) u3 l7 u2 ca)
    rw[qV,mI,mI,mS] at us;rcases us with rfl|rfl|rfl
    ·exact qn (aP.1 (a2 u2 ab).1).2.1
    ·exact qn (aP.1 (a2 u2 ab).2).2.1
    ·exact qn (aP.1 et).2.1
   have n7:P'≠Q':=λk=>ut (kA Prod.fst k);rcases h3 P' (c7 u1 ab).1 (c7 u2 ab).1 with rfl|rfl<;>
    rcases h3 Q' (c7 u1 ab).2 (c7 u2 ab).2 with rfl|rfl
   ·exact (n7 rfl).elim
   ·exact ⟨(c7 x ab).1,(c7 x ab).2⟩
   ·exact ⟨(c7 x ab).2,(c7 x ab).1⟩
   ·exact (n7 rfl).elim
  rcases h9 with rfl|rfl
  ·exact ⟨Q,te.symm,(a2 u1 ab).2,(a2 u2 ab).2,hA⟩
  ·exact ⟨P,te,(a2 u1 ab).1,(a2 u2 ab).1,λx hx=>(hA x hx).symm⟩
 have b6:∀x:F0,x∉({0,7,8,10}:S0)->(aG 14 D x).card≤2:=(by intro x hx;by_contra uv;exact hx ((by decide +kernel:∀t∈({7,8,10}:S0),t∈({0,7,8,10}:S0)) x (ih x (d0 x Y).1)));have hf:∀v:F0,v∈O 14 D u0.1->v∈({7,8,10}:S0):=by
  intro v hv;by_contra s4;have vS:v≠0:=λk=>cl.1 h0 (k▸eQ u7 hv);have qQ:=fQ hG h hC b hb lc (by omega:3≤(aG 14 D u1).card);have se:u1≠v:=λk=>s4 (k▸b2);obtain ⟨e0,tX⟩:=ek hG h hC b hb se qQ.2.2.1
   (λr hr _=>by have ix:r=u0:=mS.1 (lc▸hr);rw[ix];exact hv)
   ⟨qQ.2.2.2,hv⟩
  have t7:a0 0=e0:=by
   by_contra eu
   have sV:=tX (a0 0) (bd a4 h0 (by
    have h':=b2;simp only[mI,mS] at h'
    rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl)) eu
   exact s4 ((by decide +kernel:∀t:F0,aH 0 t->t∈({7,8,10}:S0)) v ((fi v).1 sV))
  obtain ⟨a,rA,uq,ww,uc⟩:=(by decide +kernel:∀u∈({7,8,10}:S0),∀v:F0,v∉({7,8,10}:S0)->v≠0->∃a∈({7,8,10}:S0),a≠u/\a≠v/\¬aH a v) u1 b2 v s4 vS;obtain ⟨e,b0,vE,v2⟩:=bB h hD (nS uq) se uc;by_cases k:e=e0
  ·exact vE (by rw[k,← t7];exact (a4.1 0 h0).2.2.1 a (by
    have h':=rA;simp only[mI,mS] at h'
    rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl))
  ·exact v2 (tX e b0 k)
 obtain ⟨tQ,ho⟩:=l8 h hD hT hd a4 lc hI eb b2 ca c8 uM vc hE b1 hi;have a8:E.1<D.length:=(aP.1 b1).1;have a3:aO 14 D=14+26:=by unfold aO;rw[hT.1]
 have lw:14+E.1<aO 14 D:=by rw[a3];have:=hT.1;omega
 let SE:=({1,2,3,4,5,6}:S0).filter (λp=>aI E∈aG 14 D p)
 have a7:∀g:Nat,g<D.length->bf D g=true->∀x:F0,x∉({0,7,8,10}:S0)->2≤(aG 14 D x).card->x∉O 14 D (14+g):=λg hg qp x hx hW2 hxin=>by
  have hm:g∈bi 14 D (ba 14 D {x}):=(by rw[bi,mF,mR];exact ⟨hg,dp.2 hxin,dp.2 (by simpa[W] using de hS hg qp false hxin),dp.2 (by simpa[W] using de hS hg qp true hxin)⟩);have sX:=ff hG h hC b hb x;have wr:(ru D b x).card=0:=(by rw[cZ,eF];intro r hr;have ix:r=u0:=mS.1 (lc▸(bb.1 hr).1);exact hx ((by decide +kernel:∀t∈({7,8,10}:S0),t∈({0,7,8,10}:S0)) x (hf x (ix▸(bb.1 hr).2))));have vx:1≤(bi 14 D (ba 14 D {x})).card:=cO.2 ⟨g,hm⟩;have wm:({x}∩aW 14 D).card≤1:=(cL iL).trans ab;change _+_=_+(ru D b x).card at sX;omega
 have ea:∀bm:Bool,∀x:F0,x∉({0,7,8,10}:S0)->x∉O 14 D (W D (26,!bm)):=λbm x hx hm=>by
  by_cases hs:(!bm)=(a0 0).2
  ·have rW:x∈O 14 D (W D (a0 0)):=by
    show x∈O 14 D (W D ((a0 0).1,(a0 0).2));rw[eb,← hs];exact hm
   exact hx ((by decide +kernel:∀t:F0,aH 0 t->t∈({0,7,8,10}:S0)) x ((fi x).1 rW))
  ·have sF:(!bm)=!(a0 0).2:=by cases h1:bm<;>cases h2:(a0 0).2<;>simp_all
   have rW:x∈O 14 D (W D ((a0 0).1,!(a0 0).2)):=by rw[eb,← sF];exact hm
   rw[(a4.1 0 h0).2.2.2,mS] at rW;exact hx (by rw[rW];decide)
 have fz:∀w:Nat,w<aO 14 D->2≤aS D w->∀z:F0,z∈O 14 D w->w≠b z->w=u0.1:=λw c2 e4 z hz ql=>by
   have qd:(⟨w,0⟩:P0)∈aR 14 D b:=(by refine mD.2 ⟨mF.2 ⟨dh.2 ⟨cz.2 (by show w+1<14+D.length;unfold aO at c2;omega),by show 0+1<aS D w;omega⟩,⟨z,hz⟩⟩,λhwr=>?_⟩;obtain ⟨y,hy,vZ⟩:=mM.1 hwr;have ug:b y=w:=kA Sigma.fst vZ;have vt:z=y:=mS.1 (by rw[← (hb y hy).2,ug];exact hz);exact ql (by rw[vt,ug]));exact kA Sigma.fst (mS.1 (lc▸qd))
 have hF:∀l1∈({9,11,12,13}:S0),∀p1∈SE,aH l1 p1->∀l2∈({9,11,12,13}:S0),∀p2∈SE,aH l2 p2->l1≠l2->(∃Q∈aG 14 D p1,aI Q∈aG 14 D l1/\Q≠aI E)\/(∃Q∈aG 14 D p2,aI Q∈aG 14 D l2/\Q≠aI E):=by
  intro l1 c0 p1 f2 hw l2 h7 p2 g8 n8 qN;by_contra er;rw[nO] at er
  have hH:∀Q∈aG 14 D p1,aI Q∈aG 14 D l1->Q=aI E:=λQ h1 h2=>
   by_contra λeu=>er.1 ⟨Q,h1,h2,eu⟩
  have p7:∀Q∈aG 14 D p2,aI Q∈aG 14 D l2->Q=aI E:=λQ h1 h2=>
   by_contra λeu=>er.2 ⟨Q,h1,h2,eu⟩
  rcases ky h (14+E.1) lw with c3|⟨w,tI,c2,e4,e7⟩
  ·rw[a3] at c3;rcases cT c3 with ez|⟨tZ,hK,ct⟩
   ·exact hE Y
   ·obtain ⟨sN,bm,-,tR,c5⟩:=dN.1 ct.1;have n2:sN=26:=Y
    subst n2
    let ec:=W D (26,!bm)
    have ll:¬rG (bk 14 D) (14+E.1) ec:=f4 hS (by rw[hT.1];omega) (c5.symm▸hK) (c5.symm▸ct.2);have ty:=(mF.1 f2).1;have d2:val D (aL p1 l1) ec=true:=(by have h1:val D (aL p1 l1) (aO 14 D)=true:=(hD _).2 ((ds p1 l1).2 (bh hw));rw[a3,cc hS _ (by rw[hT.1];omega:26<D.length) (!bm),hT.2.1,gop_true,bA] at h1;exact h1.1);have ta:p1∉({0,7,8,10}:S0):=(by have h':=ty;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>decide);have s8:l1∉({0,7,8,10}:S0):=(by have h':=c0;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl<;>decide);obtain ⟨Q,g0,g9,tY⟩:=eh hS (by have rs:=hT.1;have:=bv hS (by omega:26<D.length) (!bm);omega)
     (λk:p1=l1=>by subst k;exact bW _ hw) (ea bm p1 ta) (ea bm l1 s8) d2
    have tr:=hH Q g0 g9;have vk:rG (λa c=>bk 14 D a c/\val D (aL p1 l1) a=true) (14+E.1) ec:=by rw[tr] at tY;exact tY
    exact ll (dt (λ_ _ hh=>hh.1) vk)
  ·have rh:=eB hS t0 e4;obtain ⟨z,hz⟩:=rh;have rM:z≠0:=λh0z=>by subst h0z;have:=eG.1 h0 w hz;omega
   have rU:z∈aW 14 D:=qq z rM;have ql:w=b z:=(by by_contra eu;have sw:=fz w c2 e4 z hz eu;have vC:W D E<14+E.1:=bv hS a8 E.2;omega);subst ql;have qv:∀l∈({9,11,12,13}:S0),∀p∈SE,aH l p->(∀Q∈aG 14 D p,aI Q∈aG 14 D l->Q=aI E)->∃j:Nat,∃s:Bool,j<D.length/\bf D j=true/\aU 14 D (14+E.1) (W D (j,s))/\aS D (W D (j,s))=1/\aU 14 D (14+j) (b z)/\(j,!s)∈aG 14 D l/\O 14 D (W D (j,!s))={l}:=by
    intro l hl p hp g6 k0;have vd:=(mF.1 hp).1;have uB:=(mF.1 hp).2;have i0:l∉({0,7,8,10}:S0):=(by have h':=hl;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl<;>decide);have t4:E∈aG 14 D l:=(by obtain ⟨Q,g0,g9,-⟩:=bp hG hS hC (bh g6);have tr:=k0 Q g0 g9;rwa[tr,aT] at g9);obtain ⟨u',f0,sT⟩:∃u'∈({u1,u2}:S0),¬aH u' p:=by
     rcases (by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),a≠c->∀p∈({1,2,3,4,5,6}:S0),¬aH a p\/¬aH c p) u1 b2 u2 ca c8 p vd with h1|h2
     ·exact ⟨u1,ab,h1⟩
     ·exact ⟨u2,ab,h2⟩
    have sx:E∈aG 14 D u':=by
     rcases mI.1 f0 with rfl|h2
     ·exact b1
     ·rw[mS.1 h2];exact hi
    have up:u'≠0:=by
     rcases mI.1 f0 with rfl|h2
     ·have h':=b2;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide
     ·rw[mS.1 h2];have h':=ca;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide
    have tt:p≠0:=(by have h':=vd;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>decide);have uh:z≠u':=λk=>by have:=iw hS hd (qq u' up) sx;subst k;omega
    have vT:z≠p:=λk=>by
     have:=iw hS hd (qq p tt) uB;change b p<14+E.1 at this;subst k;omega
    have ry:val D (aL u' p) (14+E.1)=true:=(by rw[cc hS _ a8 E.2,dJ hS b1,gop_true,bA];exact ⟨cf hS (aP.1 sx).2.1 (by simp[aL]),cf hS (aP.1 uB).2.1 (by simp[aL])⟩);have g4:val D (aL u' p) (b z)=false:=jA hS hD hd sT uh vT rU;obtain ⟨j,s,hj,qS,hQ,hY,hX,wx,rP⟩:=lf hS (aL u' p) e7 ry g4;have cb:val D (aL p l) (aO 14 D)=true:=(hD _).2 ((ds p l).2 (bh g6));obtain ⟨Q0,qy,qw,q9⟩:=eh hS (by unfold aO;rw[hT.1];omega)
     (λk:p=l=>by subst k;exact bW _ g6) (by rw[c4 hD];simp) (by rw[c4 hD];simp) cb
    have qZ:=k0 Q0 qy qw;have ra:rG (λa c=>bk 14 D a c/\val D (aL p l) a=true) (14+E.1) (aO 14 D):=(by rw[qZ] at q9;exact q9);have qi:aU 14 D (14+E.1) (14+j):=rT hQ ⟨b4 (n:=14) hj s,hY⟩;have uU:val D (aL p l) (14+j)=true:=(gV hS qi ra (by unfold aO;omega) cb).1;rw[cc hS _ hj s,qS,gop_true,bA] at uU;have uE:p∉O 14 D (W D (j,!s)):=λhm=>by
     have:=cf hS hm (x:=aL u' p) (by simp[aL]);rw[rP] at this;exact bF this
    have hN:l∈O 14 D (W D (j,!s)):=by
     by_contra vF;obtain ⟨Q',rg,rm,qM⟩:=eh hS (by have:=bv hS hj (!s);omega)
      (λk:p=l=>by subst k;exact bW _ g6) uE vF uU.2
     have qK:=k0 Q' rg rm;have qI:rG (λa c=>bk 14 D a c/\val D (aL p l) a=true) (14+E.1) (W D (j,!s)):=(by rw[qK] at qM;exact qM);exact f4 hS hj hQ hY (dt (λ_ _ hh=>hh.1) qI)
    have ri:l∉O 14 D (14+j):=by
     intro tW;have h4:l∈O 14 D (W D (j,s)):=de hS hj qS s tW;have tl:j∈bi 14 D (ba 14 D {l}):=by
      rw[bi,mF,mR];refine ⟨hj,dp.2 tW,?_⟩;cases s
      ·exact ⟨dp.2 (by simpa[W] using h4),dp.2 (by simpa[W] using hN)⟩
      ·exact ⟨dp.2 (by simpa[W] using hN),dp.2 (by simpa[W] using h4)⟩
     have sX:=ff hG h hC b hb l;have vy:(ru D b l).card=0:=(by rw[cZ,eF];intro r hr;have ix:r=u0:=mS.1 (lc▸(bb.1 hr).1);have rx:=hf l (ix▸(bb.1 hr).2);exact i0 ((by decide +kernel:∀t∈({7,8,10}:S0),t∈({0,7,8,10}:S0)) l rx));have vx:1≤(bi 14 D (ba 14 D {l})).card:=cO.2 ⟨j,tl⟩;have wk:({l}∩aW 14 D).card≤1:=(cL iL).trans ab;have wA:(aG 14 D l).card≤1:=by change _+_=_+(ru D b l).card at sX;omega
     have r0:aG 14 D l={E}:=(eS (sS.2 t4) (by rw[cS];omega)).symm;have u5:l≠u1:=λk=>i0 (by rw[k];have h':=b2;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide);have t5:l≠u2:=λk=>i0 (by rw[k];have h':=ca;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide);obtain ⟨e,b0,uX,wo⟩:=bB h hD u5 t5
      ((by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),¬aH a c) u1 b2 u2 ca)
     rw[r0,mS] at b0;subst b0;exact uX (aP.1 b1).2.1
    have nl:(j,!s)∈aG 14 D l:=aP.2 ⟨hj,hN,ri⟩;have rV:(j,!s)≠E:=λk=>by
     have h1:14+E.1<14+j:=(by have:=bV hS (λ_ _ hh=>hh.1) hQ;have:=bv hS hj s;omega);have:=kA Prod.fst k;omega
    have qh:aG 14 D l={E,(j,!s)}:=(eS (λe k=>by
      rcases mI.1 k with rfl|k;exact t4;rw[mS.1 k];exact nl)
      (by rw[cP rV.symm];exact b6 l i0)).symm
    have qm:O 14 D (W D (j,!s))={l}:=by
     ext t;simp only[mS];refine ⟨λht=>?_,λk=>k▸hN⟩;by_contra v6;by_cases uT:t=0
     ·subst uT;have wi:=fj h hD a4 h0
      have uV:(j,!s)∈aG 14 D 0:=aP.2 ⟨hj,ht,λh0in=>by
       have vN:aU 14 D (0:F0).val (W D (a0 0))\/True:=oR trivial;have wh:(0:F0)∉O 14 D (aO 14 D):=by rw[c4 hD];simp
       have h1:=fJ hS h0 h0in
       have h2:=eG.1 h0 (b z);have vo:=bV hS (λ_ _ hh=>hh.1) hX;have vq:(0:F0)∉O 14 D (b z):=by rw[(hb z rU).2,mS];exact nS rM
       have:(14+j)<14+26:=(by have:=bV hS (λ_ _ hh=>hh.1) hX;rw[a3] at c2;omega)
       have qz:=de hS hj qS s h0in
       have qe:=de hS hj qS (!s) h0in
       have hk:W D (j,s)≠W D (j,!s):=(by have:=(hS j hj).2.2;cases s<;>simp[W,this,nS this]);have p6:=fJ hS h0 qz;have nB:=fJ hS h0 qe;rcases gj hS p6 (dt (λ_ _ hh=>hh.1) nB) with vw|⟨vV,-⟩
       ·rcases cH vw with ez|⟨c',r5,hB⟩
        ·exact hk ez
        ·have i4:c'=14+j:=cY r5 (b4 (n:=14) hj s) hY;have rK:=bV hS (λ_ _ hh=>hh) (i4▸hB);have:=bv hS hj (!s);omega
       ·rcases cH vV with ez|⟨c',r5,hB⟩
        ·exact hk ez.symm
        ·have i4:c'=14+j:=cY r5.1 (b4 (n:=14) hj (!s)) r5.2;have rK:=bV hS (λ_ _ hh=>hh.1) (i4▸hB)
         have:=bv hS hj s;omega⟩
      rw[wi,mS] at uV;have n2:j=26:=by have:=kA Prod.fst uV;simp only[aI] at this;omega
      have:=bV hS (λ_ _ hh=>hh.1) hX;rw[a3] at c2;omega
     ·obtain ⟨ti,qX,vG⟩:∃ti∈({u1,u2}:S0),¬aH t ti:=by
       rcases (by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({7,8,10}:S0),a≠c->∀t:F0,t≠0->¬aH t a\/¬aH t c) u1 b2 u2 ca c8 t uT with h1|h2
       ·exact ⟨u1,ab,h1⟩
       ·exact ⟨u2,ab,h2⟩
      have r4:l≠ti:=λk=>i0 (by
       rw[k];rcases mI.1 qX with rfl|h2
       ·have h':=b2;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide
       ·rw[mS.1 h2];have h':=ca;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide)
      obtain ⟨e,b0,q5,uL⟩:=bB h hD (nS v6) r4 vG;rw[qh,mI,mS] at b0;rcases b0 with rfl|rfl
      ·exact uL (by rcases mI.1 qX with rfl|h2;exact (aP.1 b1).2.1;rw[mS.1 h2];exact (aP.1 hi).2.1)
      ·exact q5 ht
    exact ⟨j,s,hj,qS,hQ,hY,hX,nl,qm⟩
   obtain ⟨j1,s1,s6,v0,p6,sc,vD,wq,m3⟩:=qv l1 c0 p1 f2 hw hH;obtain ⟨j2,s2,u4,v3,nB,vn,vX,ws,oz⟩:=qv l2 h7 p2 g8 n8 p7;have tU:j1≠j2:=λk=>by
    subst k;have uK:s1=s2:=by
     by_contra eu;have sF:(!s1)=s2:=by cases s1<;>cases s2<;>first|rfl|exact (eu rfl).elim
     exact f4 hS s6 p6 sc (sF.symm▸dt (λ_ _ hh=>hh.1) nB)
    subst uK;exact qN (sJ (m3.symm.trans oz))
   have fc:∀ja jb:Nat,∀sa:Bool,∀rr es f1:F0,rr≠es->rr∈({9,11,12,13}:S0)->es∈({9,11,12,13}:S0)->f1∈SE->aH es f1->(∀Q∈aG 14 D f1,aI Q∈aG 14 D es->Q=aI E)->ja<D.length->bf D ja=true->aU 14 D (14+E.1) (W D (ja,sa))->aS D (W D (ja,sa))=1->O 14 D (W D (ja,!sa))={rr}->ja<jb->jb<D.length->False:=by
    intro ja jb sa rr es f1 rZ uo q8 va qT qc rS wa sr sh nR vp wy;have cb:val D (aL f1 es) (aO 14 D)=true:=(hD _).2 ((ds f1 es).2 (bh qT));obtain ⟨Q0,qy,qw,q9⟩:=eh hS (by unfold aO;rw[hT.1];omega)
     (λk:f1=es=>by subst k;exact bW _ qT) (by rw[c4 hD];simp) (by rw[c4 hD];simp) cb
    have qZ:=qc Q0 qy qw;have ra:rG (λa c=>bk 14 D a c/\val D (aL f1 es) a=true) (14+E.1) (aO 14 D):=(by rw[qZ] at q9;exact q9);have k3:aU 14 D (14+E.1) (14+ja):=rT sr ⟨b4 (n:=14) rS sa,sh⟩;have sp:val D (aL f1 es) (14+ja)=true:=(gV hS k3 ra (by unfold aO;omega) cb).1;rw[cc hS _ rS sa,wa,gop_true,bA] at sp;have tb:f1∉O 14 D (W D (ja,!sa)):=(by rw[nR,mS];intro k;have h1:=(mF.1 va).1;have h2:=uo;simp only[mI,mS] at h1 h2;rcases h1 with rfl|rfl|rfl|rfl|rfl|rfl<;>rcases h2 with rfl|rfl|rfl|rfl<;>exact absurd k o);have th:es∉O 14 D (W D (ja,!sa)):=(by rw[nR,mS];exact nS rZ);obtain ⟨Q',rg,rm,qM⟩:=eh hS (by have:=bv hS rS (!sa);omega)
     (λk:f1=es=>by subst k;exact bW _ qT) tb th sp.2
    have qK:=qc Q' rg rm;have qI:rG (λa c=>bk 14 D a c/\val D (aL f1 es) a=true) (14+E.1) (W D (ja,!sa)):=by rw[qK] at qM;exact qM
    exact f4 hS rS sr sh (dt (λ_ _ hh=>hh.1) qI)
   rcases Nat.lt_or_gt_of_ne tU with v9|uv
   ·exact fc j1 j2 s1 l1 l2 p2 qN c0 h7 g8 n8 p7 s6 v0 p6 sc m3 v9 u4
   ·exact fc j2 j1 s2 l2 l1 p1 qN.symm h7 c0 f2 hw hH u4 v3 nB vn oz uv s6
 have i7:∃g2∈({9,11,12,13}:S0),∀l∈({9,11,12,13}:S0),l≠g2->∀p∈SE,aH l p->∃Q∈aG 14 D p,aI Q∈aG 14 D l/\Q≠aI E:=by
  by_cases uI:∃l∈({9,11,12,13}:S0),∃p∈SE,aH l p/\¬∃Q∈aG 14 D p,aI Q∈aG 14 D l/\Q≠aI E
  ·obtain ⟨lb,r3,pb,wj,ux,rj⟩:=uI;refine ⟨lb,r3,λl hl eu p hp g6=>?_⟩;rcases hF lb r3 pb wj ux l hl p hp g6 eu.symm with h1|h2
   ·exact (rj h1).elim
   ·exact h2
  ·refine ⟨9,o,λl hl _ p hp g6=>?_⟩;by_contra rj;exact uI ⟨l,hl,p,hp,g6,rj⟩
 obtain ⟨g2,n5,hR⟩:=i7;have c6:∀l∈({9,11,12,13}:S0),l≠g2->∀p∈({1,2,3,4,5,6}:S0),aH l p->((p∈SE/\2≤SE.card)\/(p∉SE/\cv p∉SE))->∃Q,Q∈aG 14 D p/\aI Q∈aG 14 D l/\p∈O 14 D (W D Q)/\∀t∈({1,2,3,4,5,6}:S0),t≠p->t∉O 14 D (W D Q):=by
  intro l hl pr p hp g6 v4;have mt:p∉({0,7,8,10}:S0):=(by have qo:=hp;simp only[mI,mS] at qo;rcases qo with rfl|rfl|rfl|rfl|rfl|rfl<;>decide);rcases v4 with ⟨iy,wu⟩|⟨tg,rB⟩
  ·obtain ⟨Q,g0,g9,qx⟩:=hR l hl pr p iy g6;obtain ⟨q,p8,vH⟩:∃q∈SE,q≠p:=by
    have:(SE.erase p).Nonempty:=cO.1 (by rw[cE iy];omega)
    obtain ⟨q,hq⟩:=this;exact ⟨q,mO hq,(mE.1 hq).1⟩
   have vv:=(mF.1 p8).1;have we:=(aP.1 (mF.1 p8).2).2.1
   have q4:aG 14 D p={aI E,Q}:=(eS (λe k=>by
     rcases mI.1 k with rfl|k;exact (mF.1 iy).2;rw[mS.1 k];exact g0)
     (by rw[cP qx.symm];exact b6 p mt)).symm
   refine ⟨Q,g0,g9,(aP.1 g0).2.1,λt ht htp htQ=>?_⟩;have ub:=(by decide +kernel:∀t∈({1,2,3,4,5,6}:S0),∀q∈({1,2,3,4,5,6}:S0),¬aH t q) t ht q vv;obtain ⟨e,b0,q5,vY⟩:=bB h hD (nS htp) (nS vH) ub;rw[q4,mI,mS] at b0;rcases b0 with rfl|rfl
   ·exact vY we
   ·exact q5 htQ
  ·let u:=bS p
   let p':=cv p
   have a1:u∈({7,8,10}:S0)/\p'∈({1,2,3,4,5,6}:S0)/\p'≠p/\aH u p/\aH u p'/\p≠0/\p'≠0/\u≠l:=(by have qo:=hp;have q0:=hl;simp only[mI,mS] at qo q0;rcases qo with rfl|rfl|rfl|rfl|rfl|rfl<;>rcases q0 with rfl|rfl|rfl|rfl<;>decide);have vA:∃Z,aI Z∈aG 14 D p/\aI Z∈aG 14 D p'/\Z∉aG 14 D l:=by
    by_cases vB:(aG 14 D u).card=3
    ·have rN:=(d0 u Y).2;obtain ⟨Z,tJ,j0,-⟩:=bp hG hS hC a1.2.2.2.1;have hZ:Z≠a0 0:=λk=>a1.2.2.2.2.2.1 (bx a4 h0 (k▸j0));have ej:Z≠E:=λk=>tg (mF.2 ⟨hp,k▸j0⟩)
     have r1:a0 0∈aG 14 D u:=bd a4 h0 (by
      have h':=a1.1;simp only[mI,mS] at h'
      rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl)
     have k2:a0 0≠E:=λk=>hE (kA Prod.fst k).symm
     have hP:aG 14 D u={a0 0,E,Z}:=(eS (λe k=>by
       simp only[mI,mS] at k;rcases k with rfl|rfl|rfl
       ·exact r1
       ·exact rN
       ·exact tJ)
       (by rw[cI (by simp[k2,hZ.symm]),cP ej.symm];omega)).symm
     obtain ⟨Z',sf,qG,-⟩:=bp hG hS hC a1.2.2.2.2.1;have rk:Z'≠a0 0:=λk=>a1.2.2.2.2.2.2.1 (bx a4 h0 (k▸qG));have qE:Z'≠E:=λk=>rB (mF.2 ⟨a1.2.1,k▸qG⟩);rw[hP,mI,mI,mS] at sf;have tS:Z'=Z:=(sf.resolve_left rk).resolve_left qE;refine ⟨Z,j0,tS▸qG,λhZl=>?_⟩;obtain ⟨u',f0,lo⟩:∃u'∈({u1,u2}:S0),u'≠u:=by
      by_cases h1:u1≠u
      ·exact ⟨u1,ab,h1⟩
      ·exact ⟨u2,ab,λk=>c8 (by push Not at h1;exact h1.trans k.symm)⟩
     have c1:u'∈({7,8,10}:S0):=(by rcases mI.1 f0 with rfl|h2;exact b2;rw[mS.1 h2];exact ca);have s3:=(by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({9,11,12,13}:S0),¬aH a c) u' c1 l hl;obtain ⟨e,b0,i3,ua⟩:=bB h hD (nS lo) a1.2.2.2.2.2.2.2 s3;rw[hP,mI,mI,mS] at b0;rcases b0 with rfl|rfl|rfl
     ·exact i3 ((a4.1 0 h0).2.2.1 u' (by
       have h':=c1;simp only[mI,mS] at h'
       rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl))
     ·exact i3 (aP.1 (by rcases mI.1 f0 with rfl|h2;exact b1;rw[mS.1 h2];exact hi)).2.1
     ·exact ua (aP.1 hZl).2.1
    ·have k1:(aG 14 D u).card≤2:=by have:=rf u;omega
     obtain ⟨Z,-,hP,ko⟩:=ps h hD a4 h0 (by
      have h':=a1.1;simp only[mI,mS] at h'
      rcases h' with h1|h1|h1<;>rw[h1]<;>decide)
      (bd a4 h0 (by
       have h':=a1.1;simp only[mI,mS] at h'
       rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl)) k1
     obtain ⟨e1,id,ik,-⟩:=bp hG hS hC a1.2.2.2.1;obtain ⟨e2,sb,sv,-⟩:=bp hG hS hC a1.2.2.2.2.1;rw[hP,mI,mS] at id sb;have uJ:e1=Z:=id.resolve_left (λk=>a1.2.2.2.2.2.1 (bx a4 h0 (k▸ik)));have tT:e2=Z:=sb.resolve_left (λk=>a1.2.2.2.2.2.2.1 (bx a4 h0 (k▸sv)));exact ⟨Z,uJ▸ik,tT▸sv,ko l (nS a1.2.2.2.2.2.2.2)⟩
   obtain ⟨Z,ko,um,p0⟩:=vA;obtain ⟨Q,g0,g9,-⟩:=bp hG hS hC (bh g6);have qx:Q≠aI Z:=λk=>by rw[k,aT] at g9;exact p0 g9
   have q4:aG 14 D p={aI Z,Q}:=(eS (λe k=>by
     rcases mI.1 k with rfl|k;exact ko;rw[mS.1 k];exact g0)
     (by rw[cP qx.symm];exact b6 p mt)).symm
   refine ⟨Q,g0,g9,(aP.1 g0).2.1,λt ht htp htQ=>?_⟩;have tf:=(by decide +kernel:∀t∈({1,2,3,4,5,6}:S0),∀q∈({1,2,3,4,5,6}:S0),¬aH t q) t ht p' a1.2.1;obtain ⟨e,b0,q5,vi⟩:=bB h hD (nS htp) (nS a1.2.2.1) tf;rw[q4,mI,mS] at b0;rcases b0 with rfl|rfl
   ·exact vi (aP.1 um).2.1
   ·exact q5 htQ
 obtain ⟨m,hm⟩:=nv SE (fS _ _);rcases pN m g2 n5 with
  ⟨l,hl,pr,p1,f2,p2,g8,p3,qk,gs,h6,rb,hw,n8,uQ,t1,uA⟩|g3
 ·rw[hm] at t1 uA;obtain ⟨Q1,-,m8,sd,ev⟩:=c6 l hl pr p1 f2 hw t1;obtain ⟨Q2,-,m2,si,hO⟩:=c6 l hl pr p2 g8 n8 uA
  have tC:aI Q1≠aI Q2:=λk=>
   ev p2 g8 gs.symm (by rw[← aT Q1,k,aT];exact si)
  have qD:l∉({0,7,8,10}:S0):=(by have q0:=hl;simp only[mI,mS] at q0;rcases q0 with rfl|rfl|rfl|rfl<;>decide)
  have qh:aG 14 D l={aI Q1,aI Q2}:=(eS (λe k=>by
    rcases mI.1 k with rfl|k;exact m8;rw[mS.1 k];exact m2)
    (by rw[cP tC];exact b6 l qD)).symm
  obtain ⟨e3,sl,n1,-⟩:=bp hG hS hC uQ;rw[qh,mI,mS] at sl;rcases sl with rfl|rfl
  ·exact ev p3 qk h6.symm (by rw[aT] at n1;exact (aP.1 n1).2.1)
  ·exact hO p3 qk rb.symm (by rw[aT] at n1;exact (aP.1 n1).2.1)
 ·rw[hm] at g3;have f3:∀l1 l2 l3 p1 p2 p3 q1 q2 q3:F0,SE={p1,p2,p3}->kI g2 l1 l2 l3 p1 p2 p3 q1 q2 q3=true->False:=by
   intro l1 l2 l3 p1 p2 p3 q1 q2 q3 a6 uD;simp only[kI,dT] at uD;obtain ⟨c0,h7,qg,vm,ve,uC,f2,g8,qk,qj,r7,g7,tp,s5,tn,uH,ur,uf,t2,sA,tu,tN,tO,d1,rR,tm,tc,tG,tq,qA,tH,gs,h6,rb,sG,qW,sE,tB,q7,td,tD⟩:=uD;have ue:q1∉SE:=a6.symm▸tp;have uF:q2∉SE:=a6.symm▸s5;have r9:q3∉SE:=a6.symm▸tn;have qP:2≤SE.card:=(by rw[a6,cI (by simp[gs,h6]),cP rb];omega);obtain ⟨Q1,tM,m8,sd,ev⟩:=c6 l1 c0 vm p1 f2 tN (oL ⟨by rw[a6];simp,qP⟩);obtain ⟨Q2,s0,m2,si,hO⟩:=c6 l2 h7 ve p2 g8 tm (oL ⟨by rw[a6];simp,qP⟩);obtain ⟨Q3,tE,su,tV,k7⟩:=c6 l3 qg uC p3 qk tq (oL ⟨by rw[a6];simp,qP⟩);have ro:∀u p p' q l:F0,u∈({7,8,10}:S0)->p∈({1,2,3,4,5,6}:S0)->p'∈({1,2,3,4,5,6}:S0)->q∈({1,2,3,4,5,6}:S0)->l∈({9,11,12,13}:S0)->p∈SE->p'∈SE->p'≠p->q∉SE->aH u p->aH u q->∀Q,Q∈aG 14 D p->aI Q∈aG 14 D l->p'∉O 14 D (W D Q)->∃Z,aG 14 D u={a0 0,E,Z}/\E∈aG 14 D u/\aI Z∈aG 14 D q/\∀t∈({9,11,12,13}:S0),Z∉aG 14 D t:=by
    intro u p p' q l hu hp qo hq hl iy ts wp p8 wd vK Q so rQ s7
    have r1:a0 0∈aG 14 D u:=bd a4 h0 (by
     have h':=hu;simp only[mI,mS] at h'
     rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl)
    have vR:aI E∈aG 14 D p:=(mF.1 iy).2;have uj:p'∈O 14 D (W D (aI E)):=(aP.1 (mF.1 ts).2).2.1;have mt:p∉({0,7,8,10}:S0):=(by have h':=hp;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>decide);have vB:(aG 14 D u).card=3:=by
     by_contra wt;have k1:(aG 14 D u).card≤2:=by have:=rf u;omega
     obtain ⟨Z,-,hP,ko⟩:=ps h hD a4 h0 (by
      have h':=hu;simp only[mI,mS] at h'
      rcases h' with h1|h1|h1<;>rw[h1]<;>decide) r1 k1
     obtain ⟨e1,id,ik,-⟩:=bp hG hS hC wd;rw[hP,mI,mS] at id;have tt:p≠0:=by have h':=hp;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>decide
     have r6:aI Z∈aG 14 D p:=(id.resolve_left (λk=>tt (bx a4 h0 (k▸ik))))▸ik;have ej:aI Z≠aI E:=λk=>by
      have h1:Z=E:=(by rw[← aT Z,k,aT]);have eu:u1≠u\/u2≠u:=by by_cases h1:u1=u;exact oR (λh2=>c8 (h1.trans h2.symm));exact oL h1
      rcases eu with uO|h8
      ·exact ko u1 uO (h1▸b1)
      ·exact ko u2 h8 (h1▸hi)
     have q4:aG 14 D p={aI E,aI Z}:=(eS (λe k=>by
       rcases mI.1 k with rfl|k;exact vR;rw[mS.1 k];exact r6)
       (by rw[cP ej.symm];exact b6 p mt)).symm
     rw[q4,mI,mS] at so;rcases so with rfl|rfl
     ·exact s7 uj
     ·rw[aT] at rQ;have vW:l≠u:=λk=>by
       have h1:=hu;have h2:=hl;simp only[mI,mS] at h1 h2;rcases h1 with rfl|rfl|rfl<;>rcases h2 with rfl|rfl|rfl|rfl<;>exact absurd k o
      exact ko l vW rQ
    have rN:=(d0 u Y).2;obtain ⟨Z,tJ,j0,-⟩:=bp hG hS hC vK;have v7:q≠0:=by have h':=hq;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl|rfl|rfl<;>decide
    have hZ:Z≠a0 0:=λk=>v7 (bx a4 h0 (k▸j0));have ej:Z≠E:=λk=>p8 (mF.2 ⟨hq,k▸j0⟩);have k2:a0 0≠E:=λk=>hE (kA Prod.fst k).symm
    have hP:aG 14 D u={a0 0,E,Z}:=(eS (λe k=>by
      simp only[mI,mS] at k;rcases k with rfl|rfl|rfl
      ·exact r1
      ·exact rN
      ·exact tJ)
      (by rw[cI (by simp[k2,hZ.symm]),cP ej.symm];omega)).symm
    refine ⟨Z,hP,rN,j0,λt ht hZt=>?_⟩;obtain ⟨u',f0,lo⟩:∃u'∈({u1,u2}:S0),u'≠u:=(by by_cases h1:u1≠u;exact ⟨u1,ab,h1⟩;exact ⟨u2,ab,λk=>c8 (by push Not at h1;exact h1.trans k.symm)⟩);have c1:u'∈({7,8,10}:S0):=(by rcases mI.1 f0 with rfl|h2;exact b2;rw[mS.1 h2];exact ca);have v1:u≠t:=λk=>by
     have h1:=hu;have h2:=ht;simp only[mI,mS] at h1 h2;rcases h1 with rfl|rfl|rfl<;>rcases h2 with rfl|rfl|rfl|rfl<;>exact absurd k o
    obtain ⟨e,b0,i3,vf⟩:=bB h hD (nS lo) v1
     ((by decide +kernel:∀a∈({7,8,10}:S0),∀c∈({9,11,12,13}:S0),¬aH a c) u' c1 t ht)
    rw[hP,mI,mI,mS] at b0;rcases b0 with rfl|rfl|rfl
    ·exact i3 ((a4.1 0 h0).2.2.1 u' (by
      have h':=c1;simp only[mI,mS] at h'
      rcases h' with h1|h1|h1<;>rw[h1]<;>exact (aK _ _).1 rfl))
    ·exact i3 (aP.1 (by rcases mI.1 f0 with rfl|h2;exact b1;rw[mS.1 h2];exact hi)).2.1
    ·exact vf (aP.1 hZt).2.1
   obtain ⟨Z7,wz,vU,sY,s9⟩:=ro 7 p1 p2 q1 l1 o f2 g8 qj c0
    (by rw[a6];simp) (by rw[a6];simp) gs.symm ue uH ur Q1 tM m8 (ev p2 g8 gs.symm)
   obtain ⟨Z8,wB,wv,sH,tK⟩:=ro 8 p2 p1 q2 l2 o g8 f2 r7 h7
    (by rw[a6];simp) (by rw[a6];simp) gs uF uf t2 Q2 s0 m2 (hO p1 f2 gs)
   obtain ⟨Z10,uY,wn,rO,hJ⟩:=ro 10 p3 p1 q3 l3 o qk f2 g7 qg
    (by rw[a6];simp) (by rw[a6];simp) h6 r9 sA tu Q3 tE su (k7 p1 f2 h6)
   have re:∀l p qa qb:F0,l∈({9,11,12,13}:S0)->qa∈({1,2,3,4,5,6}:S0)->qb∈({1,2,3,4,5,6}:S0)->qa≠p->qb≠p->aH l qa->aH l qb->∀Q,aI Q∈aG 14 D l->(∀t∈({1,2,3,4,5,6}:S0),t≠p->t∉O 14 D (W D Q))->∃S,aG 14 D l={aI Q,S}/\aI Q≠S/\aI S∈aG 14 D qa/\aI S∈aG 14 D qb:=by
    intro l p qa qb hl vI vO uR uW u6 vb Q rQ st;have qD:l∉({0,7,8,10}:S0):=(by have h':=hl;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl|rfl<;>decide);obtain ⟨S,vQ,tz,-⟩:=bp hG hS hC u6;have sn:S≠aI Q:=λk=>st qa vI uR (by rw[k,aT] at tz;exact (aP.1 tz).2.1)
    have qh:aG 14 D l={aI Q,S}:=(eS (λe k=>by
      rcases mI.1 k with rfl|k;exact rQ;rw[mS.1 k];exact vQ)
      (by rw[cP sn.symm];exact b6 l qD)).symm
    obtain ⟨S',sq,qJ,-⟩:=bp hG hS hC vb;rw[qh,mI,mS] at sq;have sR:S'=S:=sq.resolve_left (λk=>st qb vO uW (by rw[k,aT] at qJ;exact (aP.1 qJ).2.1));exact ⟨S,qh,sn.symm,tz,sR▸qJ⟩
   obtain ⟨S1,h5,rL,tv,sB⟩:=re l1 p1 q2 q3 c0 r7 g7 sG.symm qW.symm tO d1 Q1 m8 ev;obtain ⟨S2,sy,rY,hM,sW⟩:=re l2 p2 q1 q3 h7 qj g7 sE.symm tB.symm tc tG Q2 m2 hO;obtain ⟨S3,g1,m1,qU,rc⟩:=re l3 p3 q1 q2 qg qj r7 q7.symm td.symm qA tH Q3 su k7;have fl:∀q∈({1,2,3,4,5,6}:S0),q∉({0,7,8,10}:S0):=aa
   have sj:∀q la lb:F0,∀Z Sa Sb:A0,q∈({1,2,3,4,5,6}:S0)->la∈({9,11,12,13}:S0)->lb∈({9,11,12,13}:S0)->aI Z∈aG 14 D q->aI Sa∈aG 14 D q->aI Sb∈aG 14 D q->Sa∈aG 14 D la->Sb∈aG 14 D lb->(∀t∈({9,11,12,13}:S0),Z∉aG 14 D t)->Sa=Sb:=by
    intro q la lb Z Sa Sb hq wc r3 vs ul r8 tj sz p0;have vz:aI Z≠aI Sa:=λk=>p0 la wc (by rw[← aT Z,k,aT];exact tj);have vM:aI Z≠aI Sb:=λk=>p0 lb r3 (by rw[← aT Z,k,aT];exact sz)
    have vu:aG 14 D q={aI Z,aI Sa}:=(eS (λe k=>by
      rcases mI.1 k with rfl|k;exact vs;rw[mS.1 k];exact ul)
      (by rw[cP vz];exact b6 q (fl q hq))).symm
    rw[vu,mI,mS] at r8;have ez:=r8.resolve_left vM.symm;rw[← aT Sa,← ez,aT]
   have vh:S2=S3:=sj q1 l2 l3 Z7 S2 S3 qj h7 qg sY hM qU (by rw[sy];simp) (by rw[g1];simp) s9;have sm:S1=S3:=sj q2 l1 l3 Z8 S1 S3 r7 c0 qg sH tv rc (by rw[h5];simp) (by rw[g1];simp) tK;have uy:S2=S1:=vh.trans sm.symm;rw[uy] at sy rY hM sW;rw[← sm] at g1 m1 qU rc;have a5:S1∈aG 14 D l1:=by rw[h5];simp
   have tP:S1∈aG 14 D l3:=by rw[g1];simp
   have qH:aG 14 D q3={aI Z10,aI S1}:=by
    have hn:aI Z10≠aI S1:=λk=>hJ l1 c0 (by rw[← aT Z10,k,aT];exact a5)
    exact (eS (λe k=>by
     rcases mI.1 k with rfl|k;exact rO;rw[mS.1 k];exact sB)
     (by rw[cP hn];exact b6 q3 (fl q3 g7))).symm
   have b5:∀e∈aG 14 D l1,aI e∈aG 14 D q3->e=S1:=(by intro e e5 et;rw[h5,mI,mS] at e5;exact e5.resolve_left (λhh=>ev q3 g7 qW.symm (by rw[hh,aT] at et;exact (aP.1 et).2.1)));have iz:∀e∈aG 14 D l3,aI e∈aG 14 D q1->e=S1:=(by intro e e5 et;rw[g1,mI,mS] at e5;exact e5.resolve_left (λhh=>k7 q1 qj q7.symm (by rw[hh,aT] at et;exact (aP.1 et).2.1)));have tw:S1.1<D.length:=(aP.1 a5).1;have q6:S1.1≠26:=λrs=>by
    have ks:S1=a0 0\/S1=aI (a0 0):=by
     rcases Bool.eq_or_eq_not S1.2 (a0 0).2 with hs|hs
     ·left;exact pE (rs.trans eb.symm) hs
     ·right;exact pE (rs.trans eb.symm) hs
    rcases ks with k|k
    ·exact (by decide +kernel:∀x∈({9,11,12,13}:S0),x∉({7,8,10}:S0)) l1 c0 (ih l1 (k▸a5))
    ·have vg:l1=0:=mS.1 (by
      have:=(aP.1 (k▸a5)).2.1
      rwa[show W D (aI (a0 0))=W D ((a0 0).1,!(a0 0).2) from rfl,(a4.1 0 h0).2.2.2] at this)
     exact (by decide +kernel:∀x∈({9,11,12,13}:S0),x≠0) l1 c0 vg
   have ls:14+S1.1<aO 14 D:=by rw[a3];have:=hT.1;omega
   have b8:∀x∈({9,11,12,13}:S0),x∉({0,7,8,10}:S0):=aa;rcases ky h (14+S1.1) ls with c3|⟨w,tI,c2,e4,e7⟩
   ·rw[a3] at c3;rcases cT c3 with ez|⟨tZ,hK,ct⟩
    ·exact q6 Y
    ·obtain ⟨sN,bm,-,tR,c5⟩:=dN.1 ct.1;have n2:sN=26:=Y
     subst n2
     let ec:=W D (26,!bm)
     have ll:=f4 hS (by rw[hT.1];omega) (c5.symm▸hK) (c5.symm▸ct.2);have d2:val D (aL l1 q3) ec=true:=(by have h1:val D (aL l1 q3) (aO 14 D)=true:=(hD _).2 ((ds l1 q3).2 d1);rw[a3,cc hS _ (by rw[hT.1];omega:26<D.length) (!bm),hT.2.1,gop_true,bA] at h1;exact h1.1);obtain ⟨e,e5,et,sK⟩:=eh hS (by have rs:=hT.1;have:=bv hS (by omega:26<D.length) (!bm);omega)
      (λk:l1=q3=>by subst k;exact bW _ d1) (ea bm l1 (b8 l1 c0)) (ea bm q3 (fl q3 g7)) d2
     have tF:=b5 e e5 et;exact ll (dt (λ_ _ hh=>hh.1) (tF▸sK))
   ·obtain ⟨z,hz⟩:=eB hS t0 e4;have rM:z≠0:=λh0z=>by subst h0z;have:=eG.1 h0 w hz;omega
    have rU:z∈aW 14 D:=qq z rM;by_cases ql:w=b z
    ·subst ql;have uk:l1≠0:=λk=>b8 l1 c0 (by rw[k];decide);have uw:q1≠0:=λk=>fl q1 qj (by rw[k];decide);have vj:z≠l1:=λk=>by have:=iw hS hd (qq l1 uk) a5;subst k;omega
     have u8:z≠q1:=λk=>by have:=iw hS hd (qq q1 uw) hM;change b q1<14+S1.1 at this;subst k;omega
     have rX:val D (aL l1 q1) (14+S1.1)=true:=(by rw[cc hS _ tw S1.2,dJ hS a5,gop_true,bA];exact ⟨cf hS (aP.1 a5).2.1 (by simp[aL]),cf hS (aP.1 hM).2.1 (by simp[aL])⟩);have g4:val D (aL l1 q1) (b z)=false:=jA hS hD hd rR vj u8 rU;obtain ⟨g,sg,hg,qp,hU,n3,-,-,rP⟩:=lf hS (aL l1 q1) e7 rX g4;have qf:aU 14 D (14+S1.1) (14+g):=rT hU ⟨b4 (n:=14) hg sg,n3⟩;have n4:∀u v:F0,aH u v->(∀e∈aG 14 D u,aI e∈aG 14 D v->e=S1)->(u∉O 14 D (W D (g,!sg))->v∈O 14 D (W D (g,!sg)))/\(v∉O 14 D (W D (g,!sg))->u∈O 14 D (W D (g,!sg))):=by
      intro u v sL rn;have un:val D (aL u v) (aO 14 D)=true:=(hD _).2 ((ds u v).2 sL);obtain ⟨e,e5,et,sK⟩:=eh hS (by unfold aO;rw[hT.1];omega)
       (λk:u=v=>by subst k;exact bW _ sL) (by rw[c4 hD];simp) (by rw[c4 hD];simp) un
      have t3:=(gV hS qf (rn e e5 et▸sK) (by unfold aO;omega) un).1;rw[cc hS _ hg sg,qp,gop_true,bA] at t3;have er:u∉O 14 D (W D (g,!sg))->v∉O 14 D (W D (g,!sg))->False:=λhun hvn=>by
       obtain ⟨e',qY,qC,uZ⟩:=eh hS (by have:=bv hS hg (!sg);omega)
        (λk:u=v=>by subst k;exact bW _ sL) hun hvn t3.2
       exact f4 hS hg hU n3 (dt (λ_ _ hh=>hh.1) (rn e' qY qC▸uZ))
      exact ⟨λhun=>by_contra (er hun),λhvn=>by_contra (λhun=>er hun hvn)⟩
     have tk:l1∉O 14 D (W D (g,!sg)):=λhm=>by
      have:=cf hS hm (x:=aL l1 q1) (by simp[aL]);rw[rP] at this;exact bF this
     have sO:q1∉O 14 D (W D (g,!sg)):=λhm=>by
      have:=cf hS hm (x:=aL l1 q1) (by simp[aL]);rw[rP] at this;exact bF this
     have rp:q3∈O 14 D (W D (g,!sg)):=(n4 l1 q3 d1 b5).1 tk;have rJ:l3∈O 14 D (W D (g,!sg)):=(n4 l3 q1 qA iz).2 sO;have hL:2≤(aG 14 D q3).card:=(by have hn:aI Z10≠aI S1:=λk=>hJ l1 c0 (by rw[← aT Z10,k,aT];exact a5);rw[qH,cP hn]);have rz:2≤(aG 14 D l3).card:=(by rw[g1,cP m1]);have qu:(g,!sg)∈aG 14 D q3:=aP.2 ⟨hg,rp,a7 g hg qp q3 (fl q3 g7) hL⟩;have qs:(g,!sg)∈aG 14 D l3:=aP.2 ⟨hg,rJ,a7 g hg qp l3 (b8 l3 qg) rz⟩;have vJ:14+S1.1<14+g:=(by have:=bV hS (λ_ _ hh=>hh.1) hU;have:=bv hS hg sg;omega);rw[qH,mI,mS] at qu;have u9:(g,!sg)=aI Z10:=qu.resolve_right (λk=>by have:=kA Prod.fst k;simp[aI] at this;omega);rw[g1,mI,mS] at qs;have uu:(g,!sg)=aI Q3:=qs.resolve_right (λk=>by have:=kA Prod.fst k;omega);have wg:Z10=Q3:=by rw[← aT Z10,← u9,uu,aT]
     have i5:(10:F0)≠p3:=λk=>fl p3 qk (by rw[← k];decide);obtain ⟨e,b0,uP,uz⟩:=bB h hD (by decide:(10:F0)≠7) i5 tD;rw[uY,mI,mI,mS] at b0;rcases b0 with rfl|rfl|rfl
     ·exact uP ((a4.1 0 h0).2.2.1 7 ((aK 0 7).1 rfl))
     ·exact uP (aP.1 vU).2.1
     ·exact uz (wg▸tV)
    ·have sw:=fz w c2 e4 z hz ql;subst sw
     let B:=W D ((a0 0).1,!(a0 0).2)
     have rl:B<aO 14 D:=(by have:=bv hS (by rw[hT.1];omega:(a0 0).1<D.length) (!(a0 0).2);rw[a3,← eb];exact this);have hW:val D (aL l1 q3) B=true:=by
      have h1:val D (aL l1 q3) (aO 14 D)=true:=(hD _).2 ((ds l1 q3).2 d1);have sQ:bf D (a0 0).1=true:=by rw[eb];exact hT.2.1
      rw[a3,← eb,cc hS _ (by rw[hT.1];omega:(a0 0).1<D.length) (a0 0).2,sQ,gop_true,bA] at h1;exact h1.2
     have g5:O 14 D B={0}:=(a4.1 0 h0).2.2.2;have tL:l1∉O 14 D B:=by rw[g5,mS];exact λk=>b8 l1 c0 (by rw[k];decide)
     have tx:q3∉O 14 D B:=by rw[g5,mS];exact λk=>fl q3 g7 (by rw[k];decide)
     obtain ⟨e,e5,et,wf⟩:=eh hS (by unfold aO at rl;omega)
      (λk:l1=q3=>by subst k;exact bW _ d1) tL tx hW
     have tF:=b5 e e5 et;have ss:rG (λa c=>bk 14 D a c/\val D (aL l1 q3) a=true) (14+S1.1) B:=tF▸wf;have qr:u0.1≤B:=by
      rcases gj hS e7 (dt (λ_ _ hh=>hh.1) ss) with h1|⟨h2,h8⟩
      ·exact bV hS (λ_ _ hh=>hh) h1
      ·exfalso;rcases cH h2 with ez|⟨c,hc,l4⟩
       ·exact h8 ez
       ·have i4:c=14+(a0 0).1:=cY hc.1 (b4 (n:=14) (by rw[hT.1];omega:(a0 0).1<D.length) (!(a0 0).2)) hc.2;have rK:=bV hS (λ_ _ hh=>hh.1) (i4▸l4);rw[a3,← eb] at c2;omega
     have qt:=(gV hS e7 ss qr hW).2;have sZ:u1∉O 14 D B:=(by rw[g5,mS];have h':=b2;simp only[mI,mS] at h';rcases h' with rfl|rfl|rfl<;>decide);obtain ⟨-,r2⟩:=ho (λa c=>bk 14 D a c/\val D (aL l1 q3) a=true)
      (λ_ _ hh=>hh.1) B qt rl sZ
     have uN:val D (aL l1 q3) (14+E.1)=true:=by
      rcases cH r2 with ez|⟨_,h1,_⟩
      ·exact ez▸hW
      ·exact h1.2
     rw[cc hS _ a8 E.2,dJ hS b1,gop_true,bA] at uN;have hL:2≤(aG 14 D q3).card:=(by have hn:aI Z10≠aI S1:=λk=>hJ l1 c0 (by rw[← aT Z10,k,aT];exact a5);rw[qH,cP hn])
     have rD:q3∉O 14 D (W D (aI E)):=λhm=>
      r9 (mF.2 ⟨g7,aP.2 ⟨a8,hm,a7 E.1 a8 (dJ hS b1) q3 (fl q3 g7) hL⟩⟩)
     have rq:l1∉O 14 D (W D (aI E)):=λhm=>by
      have p9:aI E∈aG 14 D l1:=aP.2 ⟨a8,hm,a7 E.1 a8 (dJ hS b1) l1 (b8 l1 c0) (by rw[h5,cP rL])⟩;rw[h5,mI,mS] at p9;rcases p9 with k|k
      ·have uG:Q1=E:=(by rw[← aT Q1,← k,aT]);have rv:p1∈O 14 D (14+E.1):=by
        rw[dC hS a8 (dJ hS b1),mN];have h1:p1∈O 14 D (W D E):=uG▸sd;have h2:p1∈O 14 D (W D (aI E)):=(aP.1 (mF.1 (by rw[a6];simp:p1∈SE)).2).2.1;cases hE2:E.2
        ·exact ⟨by simpa[W,hE2] using h1,by simpa[W,aI,hE2] using h2⟩
        ·exact ⟨by simpa[W,aI,hE2] using h2,by simpa[W,hE2] using h1⟩
       exact (aP.1 (mF.1 (by rw[a6];simp:p1∈SE)).2).2.2 rv
      ·have vr:14+S1.1<14+E.1:=by have h1:W D E<14+E.1:=bv hS a8 E.2;omega
       have:=kA Prod.fst k;simp[aI] at this;omega
     have rC:W D (aI E)<14+E.1:=bv hS a8 (!E.2);have sk:W D E<14+E.1:=bv hS a8 E.2;obtain ⟨e',qY,qC,t8⟩:=eh hS Y
      (λk:l1=q3=>by subst k;exact bW _ d1) rq rD uN.2
     have ui:=b5 e' qY qC;have rt:rG (bk 14 D) (14+S1.1) (W D (aI E)):=dt (λ_ _ hh=>hh.1) (ui▸t8);rcases gj hS e7 rt with h1|⟨h2,h8⟩
     ·have qB:u1∉O 14 D (W D (aI E)):=λhm=>by
       have v5:u1∈O 14 D (14+E.1):=by
        rw[dC hS a8 (dJ hS b1),mN];have qn:=(aP.1 b1).2.1;cases hE2:E.2
        ·exact ⟨by simpa[W,hE2] using qn,by simpa[W,aI,hE2] using hm⟩
        ·exact ⟨by simpa[W,aI,hE2] using hm,by simpa[W,hE2] using qn⟩
       exact (aP.1 b1).2.2 v5
      have rE:W D (aI E)<aO 14 D:=Y;obtain ⟨-,vL⟩:=ho (bk 14 D) (λ_ _ hh=>hh) (W D (aI E)) h1 rE qB;have rK:=bV hS (λ_ _ hh=>hh) vL;omega
     ·rcases cH h2 with ez|⟨c,hc,l4⟩
      ·exact h8 ez
      ·have i4:c=14+E.1:=cY hc.1 (b4 (n:=14) a8 (!E.2)) hc.2;have rK:=bV hS (λ_ _ hh=>hh.1) (i4▸l4);omega
  have q8:=n5;simp only[mI,mS] at q8;rcases q8 with rfl|rfl|rfl|rfl
  ·exact f3 13 11 12 1 6 5 3 2 4 (by rw[g3];decide) rfl
  ·exact f3 12 9 13 3 6 4 1 2 5 (by rw[g3];decide) rfl
  ·exact f3 11 13 9 3 2 5 1 6 4 (by rw[g3];decide) rfl
  ·exact f3 9 12 11 1 2 4 3 6 5 (by rw[g3];decide) rfl
lemma kX {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(c2:bH 14 D≤14)(b2:bu 14 D=0)(hI:aN 14 D={0}):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;obtain ⟨b,a3⟩:=dB hG hS hC;have hb:=cX a3;obtain ⟨r,p⟩:=cR hG h hC;have h0:(0:F0)∈aN 14 D:=by rw[hI];simp
 have b8:∀x:F0,x≠0->x∈aW 14 D:=λx hx=>
  ai.1 (λhc=>hx (mS.1 (hI▸cl.2 hc)))
 have b5:aU 14 D (0:F0).val (aO 14 D):=by
  rcases cr hG h hC h0 with hc|⟨z,-,c5,c0⟩
  ·exact hc
  ·exact (nN (c0▸eB hS b2 c5)).elim
 have d1:=dn 14 D;have ct:=db 14 D;rw[hI,cS] at ct;have c7:=dd hS b hb;by_cases d0:(aR 14 D b).card=0
 ·exact js h hD Y h0
 have c6:(aR 14 D b).card=1:=Y;have l:br 14 D=(aW 14 D).card+1:=Y
 have a6:D.length=27:=by have:=jm h;omega
 have a8:fu D:=lu hT a6;obtain ⟨u0,ca⟩:=ac.1 c6;have m:∀x:F0,(aG 14 D x).card≤3:=λx=>by
  have:=ci h hD b hb x
  have:(ru D b x).card≤(aR 14 D b).card:=cF _ _
  omega
 have b6:(r 0).1≤26:=by have:=(p.1 0 h0).1;omega
 by_cases b1:(r 0).1<26
 ·exact oK h hD hT a6 a3 p l h0 b5 m b1
 ·have a1:(r 0).1=26:=Y;have k:∀t:F0,t∈O 14 D (W D (r 0))<->aH 0 t:=by
   intro t;refine ⟨λht=>?_,λht=>(p.1 0 h0).2.2.1 t ht⟩;have a7:(0:F0)∈O 14 D (W D ((r 0).1,!(r 0).2)):=(by rw[(p.1 0 h0).2.2.2];simp);have a2:val D (aL 0 t) (aO 14 D)=true:=by
    have cb:aO 14 D=14+(r 0).1:=by unfold aO;omega
    have b0:bf D (r 0).1=true:=by rw[a1];exact a8.2.1
    rw[cb,cc hS _ (by omega:(r 0).1<D.length) (r 0).2,b0,gop_true,bA];exact ⟨cf hS ht (by simp[aL]),cf hS a7 (by simp[aL])⟩
   exact (ds 0 t).1 ((hD _).1 a2)
  have a0:∀t:F0,r 0∈aG 14 D t->t∈({7,8,10}:S0):=λt ht=>
   (by decide +kernel:∀t:F0,aH 0 t->t∈({7,8,10}:S0)) t ((k t).1 (aP.1 ht).2.1)
  let U3:=({7,8,10}:S0).filter (λu=>(aG 14 D u).card=3)
  by_cases a4:2≤U3.card
  ·exact nn h hD a8 a3 p ca b2 hI l h0 b8 m a1 k a0 a4
  ·by_cases a5:U3.card=1
   ·obtain ⟨u3,c3⟩:=ac.1 a5;exact nC h hD a3 p l h0 m a0 c3
   ·have bm:∀u∈({7,8,10}:S0),(aG 14 D u).card≤2:=λu hu=>by
     have c8:(aG 14 D u).card≠3:=λh3=>by
      have c1:u∈U3:=mF.2 ⟨hu,h3⟩;have:=cO.2 ⟨u,c1⟩;omega
     have:=m u;omega
    exact pP h hD a3 p ca c2 l h0 b8 m bm
lemma eW:∀a b c d:F0,a≠c->b≠d->aH a b->aH b c->aH c d->¬aH d a:=aa
lemma gJ:∀a b c:F0,aH a b->aH b c->¬aH c a:=aa
def em (v:F0):List (F0):=
 (List.finRange 14).filter (λu=>aQ v u)
def lP (l p1 p2:F0):F0×F0×F0×F0×F0×F0×F0×F0:=
 let ls1:=(em p1).filter (λx=>x != l)
 let l1:=ls1.getD 0 0
 let l2:=ls1.getD 1 0
 let ls2:=(em p2).filter (λx=>x != l)
 let l3:=ls2.getD 0 0
 let l4:=ls2.getD 1 0
 let qs:=(em l1).filter (λx=>x != p1)
 let q1:=qs.getD 0 0
 let q2:=qs.getD 1 0
 let lc:=if aQ q2 l3 then l3 else l4
 let lo:=if aQ q2 l3 then l4 else l3
 let q3:=((em lc).filter (λx=>x != p2 && x != q2)).getD 0 0
 let r:=((em q2).filter (λx=>x != l1 && x != lc)).getD 0 0
 (l1,l2,lc,lo,q1,q2,q3,r)
lemma mi:∀l p1 p2:F0,p1≠p2->aQ l p1=true->aQ l p2=true->let w:=lP l p1 p2
  let l1:=w.1;let l2:=w.2.1;let lc:=w.2.2.1;let lo:=w.2.2.2.1
  let q1:=w.2.2.2.2.1;let q2:=w.2.2.2.2.2.1;let q3:=w.2.2.2.2.2.2.1;let r:=w.2.2.2.2.2.2.2
  l1≠l2/\aQ p1 l1=true/\aQ p1 l2=true/\aQ p2 l1=false/\aQ p2 l2=false/\
  lc≠lo/\aQ p2 lc=true/\aQ p2 lo=true/\aQ p1 lc=false/\aQ p1 lo=false/\
  q1≠q2/\aQ l1 q1=true/\aQ l1 q2=true/\q1≠p1/\q2≠p1/\aQ p2 q1=false/\aQ p2 q2=false/\
  q3≠q2/\aQ lc q3=true/\aQ lc q2=true/\q3≠p2/\q2≠p2/\aQ p1 q3=false/\aQ p1 q2=false/\
  aQ q2 r=true/\r≠l1/\r≠lc/\aQ l2 r=false/\aQ lo r=false/\l1≠lc/\aQ lo l1=false:=by
 decide +kernel
lemma oX (l k m:F0)(p:k≠m)(a1:aH l k)(a8:aH l m):∃l1 l2 lc lo q1 q2 q3 r:F0,l1≠l2/\aH k l1/\aH k l2/\¬aH m l1/\¬aH m l2/\lc≠lo/\aH m lc/\aH m lo/\¬aH k lc/\¬aH k lo/\q1≠q2/\aH l1 q1/\aH l1 q2/\q1≠k/\q2≠k/\¬aH m q1/\¬aH m q2/\q3≠q2/\aH lc q3/\aH lc q2/\q3≠m/\q2≠m/\¬aH k q3/\¬aH k q2/\aH q2 r/\r≠l1/\r≠lc/\¬aH l2 r/\¬aH lo r/\l1≠lc/\¬aH lo l1:=by
 have h:=mi l k m p ((aK l k).2 a1) ((aK l m).2 a8)
 set w:=lP l k m
 refine ⟨w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2.1,w.2.2.2.2.2.2.1,w.2.2.2.2.2.2.2,?_⟩;rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,a0,a4,a7,a3,a6,a2,bm,a5,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31⟩
 exact ⟨h1,(aK _ _).1 h2,(aK _ _).1 h3,bw.1 h4,bw.1 h5,h6,(aK _ _).1 h7,(aK _ _).1 h8,bw.1 h9,bw.1 a0,a4,(aK _ _).1 a7,(aK _ _).1 a3,a6,a2,bw.1 bm,bw.1 a5,h18,(aK _ _).1 h19,(aK _ _).1 h20,h21,h22,bw.1 h23,bw.1 h24,(aK _ _).1 h25,h26,h27,bw.1 h28,bw.1 h29,h30,bw.1 h31⟩
def jQ (s1 s2:F0):F0×F0×F0×F0:=
 if s1 != 0 && s2 != 0 && s1 != 7 && s2 != 7 && s1 != 1 && s2 != 1 && s1 != 9 && s2 != 9 then (0,7,1,9)
 else if s1 != 2 && s2 != 2 && s1 != 8 && s2 != 8 && s1 != 6 && s2 != 6 && s1 != 11 && s2 != 11 then (2,8,6,11)
 else (3,12,5,10)
lemma pG:∀s1 s2:F0,let w:=jQ s1 s2
  w.1≠s1/\w.1≠s2/\w.2.1≠s1/\w.2.1≠s2/\w.2.2.1≠s1/\w.2.2.1≠s2/\w.2.2.2≠s1/\w.2.2.2≠s2/\
  aQ w.1 w.2.1=true/\aQ w.2.1 w.2.2.1=true/\aQ w.2.2.1 w.2.2.2=true/\aQ w.1 w.2.2.2=false:=by
 decide +kernel
lemma nW (l k:F0):∃a b c d:F0,a≠l/\a≠k/\b≠l/\b≠k/\c≠l/\c≠k/\d≠l/\d≠k/\aH a b/\aH b c/\aH c d/\¬aH a d:=by
 have h:=pG l k
 set w:=jQ l k
 rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,m,p,r⟩
 exact ⟨w.1,w.2.1,w.2.2.1,w.2.2.2,h1,h2,h3,h4,h5,h6,h7,h8,(aK _ _).1 h9,(aK _ _).1 m,(aK _ _).1 p,bw.1 r⟩
lemma mo:∀u v:F0,u=v\/aQ u v=true\/(em u).any (λa=>aQ a v)=true\/(em u).any (λa=>(em a).any (λb=>aQ b v))=true:=aa
lemma pe:∀a b:F0,a≠b->(a.val<7<->b.val<7)->∃l:F0,aH l a/\aH l b:=aa
lemma gT:∀a b:F0,aH a b->¬(a.val<7<->b.val<7):=aa
lemma og:∀n:Fin 15,n≠0->(∃p l:F0,aH p l/\(∀i∈df n,¬aH i p)/\(∀i∈df n,¬aH i l))->df n={0,1,2,5}\/df n={0,1,2}\/df n={0,1,11}\/df n={0,1}\/df n={0,9}\/df n={0}:=aa
inductive MTree:Type
 | leaf (v:F0):MTree
 | and (l r:MTree):MTree
 | or (l r:MTree):MTree
def MTree.eval:MTree->(F0->Bool)->Bool
 | .leaf v,x=>x v
 | .and l r,x=>l.eval x && r.eval x
 | .or l r,x=>l.eval x || r.eval x
def MTree.count:MTree->F0->Nat
 | .leaf u,v=>if u=v then 1 else 0
 | .and l r,v=>l.count v+r.count v
 | .or l r,v=>l.count v+r.count v
def MTree.leaves:MTree->Nat
 | .leaf _=>1
 | .and l r=>l.leaves+r.leaves
 | .or l r=>l.leaves+r.leaves
lemma gO (T:MTree):T.leaves=∑ v:F0,T.count v:=by
 induction T with
 | leaf u=>
  simp[MTree.leaves,MTree.count]
 | and l r ihl ihr=>
  simp only[MTree.leaves,MTree.count,sD,ihl,ihr]
 | or l r ihl ihr=>
  simp only[MTree.leaves,MTree.count,sD,ihl,ihr]
lemma dc (T:MTree){x y:F0->Bool}(k:∀v,x v=true->y v=true):T.eval x=true->T.eval y=true:=by
 induction T with
 | leaf v=>exact k v
 | and l r ihl ihr=>
  simp only[MTree.eval,bA];exact λ⟨h1,h2⟩=>⟨ihl h1,ihr h2⟩
 | or l r ihl ihr=>
  simp only[MTree.eval,bO];exact λh=>h.imp ihl ihr
lemma jx (T:MTree):T.eval (λ_=>false)=false:=by
 induction T with
 | leaf _=>rfl
 | and l r ihl ihr=>simp[MTree.eval,ihl,ihr]
 | or l r ihl ihr=>simp[MTree.eval,ihl,ihr]
lemma gC (T:MTree){v:F0}(k:T.count v=0){x y:F0->Bool}(p:∀u,u≠v->x u=y u):T.eval x=T.eval y:=by
 induction T with
 | leaf u=>
  simp only[MTree.count] at k;have m:u≠v:=by intro h;subst h;simp at k
  exact p u m
 | and l r ihl ihr=>
  simp only[MTree.count] at k;simp only[MTree.eval,ihl Y,ihr Y]
 | or l r ihl ihr=>
  simp only[MTree.count] at k;simp only[MTree.eval,ihl Y,ihr Y]
lemma dg (T:MTree){u v:F0}(hu:T.count u=0):T.eval (aL u v)=T.eval (single v):=
 gC T hu (λw hw=>by simp[aL,single,hw])
lemma dQ (T:MTree){u v:F0}(hv:T.count v=0):T.eval (aL u v)=T.eval (single u):=
 gC T hv (λw hw=>by simp[aL,single,hw])
lemma ed (T:MTree){v:F0}(h:T.eval (single v)=true):1≤T.count v:=by
 by_contra m;have l:T.count v=0:=Y
 have k:=gC T l (x:=single v) (y:=λ_=>false)
  (λu hu=>by simp[single,hu])
 rw[jx] at k;rw[k] at h;exact bF h
lemma fr (T:MTree)(u v:F0):T.eval (aL u v)=T.eval (aL v u):=by congr 1;funext w;simp[aL,bR]
lemma i9 (A:MTree):∀u v:F0,A.count u=1->A.count v=1->A.eval (single u)=false->A.eval (single v)=false->A.eval (aL u v)=true->∃L R:MTree,(∀x,L.eval x=true->R.eval x=true->A.eval x=true)/\L.eval (single u)=true/\R.eval (single v)=true/\(∀w,A.count w=1->L.eval (single w)=true->∀x,A.eval (aL w x)=true->A.eval (single x)=true\/R.eval (single x)=true)/\(∀w,A.count w=1->R.eval (single w)=true->∀x,A.eval (aL x w)=true->A.eval (single x)=true\/L.eval (single x)=true):=by
 induction A with
 | leaf a=>
  intro u v hu _ m _ _;simp only[MTree.count] at hu;have eb:a=u:=by by_contra h;simp[h] at hu
  subst eb;simp[MTree.eval,single] at m
 | or A1 A2 ih1 ih2=>
  intro u v hu hv m a1 l;simp only[MTree.count] at hu hv;simp only[MTree.eval,Bool.or_eq_false_iff,bO] at m a1 l;have a0:∀(B C:MTree),(∀u v:F0,B.count u=1->B.count v=1->B.eval (single u)=false->B.eval (single v)=false->B.eval (aL u v)=true->∃L R:MTree,(∀x,L.eval x=true->R.eval x=true->B.eval x=true)/\L.eval (single u)=true/\R.eval (single v)=true/\(∀w,B.count w=1->L.eval (single w)=true->∀x,B.eval (aL w x)=true->B.eval (single x)=true\/R.eval (single x)=true)/\(∀w,B.count w=1->R.eval (single w)=true->∀x,B.eval (aL x w)=true->B.eval (single x)=true\/L.eval (single x)=true))->B.count u=1->C.count u=0->B.count v+C.count v=1->B.eval (single u)=false->C.eval (single u)=false->B.eval (single v)=false->C.eval (single v)=false->(B.eval (aL u v)=true\/C.eval (aL u v)=true)->∃L R:MTree,(∀x,L.eval x=true->R.eval x=true->(B.eval x || C.eval x)=true)/\L.eval (single u)=true/\R.eval (single v)=true/\(∀w,B.count w+C.count w=1->L.eval (single w)=true->∀x,(B.eval (aL w x) || C.eval (aL w x))=true->(B.eval (single x) || C.eval (single x))=true\/R.eval (single x)=true)/\(∀w,B.count w+C.count w=1->R.eval (single w)=true->∀x,(B.eval (aL x w) || C.eval (aL x w))=true->(B.eval (single x) || C.eval (single x))=true\/L.eval (single x)=true):=by
   intro B C es d2 d0 eu a3 et b2 c1 c0;have a6:B.eval (aL u v)=true:=by
    rcases c0 with h1|h2
    ·exact h1
    ·rw[dg C d0,c1] at h2;exact absurd h2 bF
   have ea:B.count v=1:=by
    by_contra ev;have c3:B.count v=0:=Y
    rw[dQ B c3,a3] at a6;exact bF a6
   obtain ⟨L,R,a7,a8,bm,b1,b0⟩:=es u v d2 ea a3 b2 a6;have b8:∀w,L.eval (single w)=true->1≤B.count w:=by
    intro w hw;by_contra hc;have a4:B.count w=0:=Y
    have h1:B.eval (aL w v)=true:=a7 (aL w v)
      (dc L (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) hw)
      (dc R (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) bm)
    rw[dg B a4,b2] at h1;exact bF h1
   have cb:∀w,R.eval (single w)=true->1≤B.count w:=by
    intro w hw;by_contra hc;have a4:B.count w=0:=Y
    have h1:B.eval (aL u w)=true:=a7 (aL u w)
      (dc L (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) a8)
      (dc R (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) hw)
    rw[dQ B a4,a3] at h1;exact bF h1
   refine ⟨L,R,λx hx1 hx2=>by simp[a7 x hx1 hx2],a8,bm,?_,?_⟩
   ·intro w d1 r x k;have ca:B.count w=1:=by have:=b8 w r;omega
    have ct:C.count w=0:=Y;rw[bO] at k ⊢;rcases k with h1|h2
    ·rcases b1 w ca r x h1 with hs|hr
     ·exact oL (oL hs)
     ·exact oR hr
    ·rw[dg C ct] at h2;exact oL (oR h2)
   ·intro w d1 p x k;have ca:B.count w=1:=by have:=cb w p;omega
    have ct:C.count w=0:=Y;rw[bO] at k ⊢;rcases k with h1|h2
    ·rcases b0 w ca p x h1 with hs|hl
     ·exact oL (oL hs)
     ·exact oR hl
    ·rw[dQ C ct] at h2;exact oL (oR h2)
  by_cases h1:A1.count u=1
  ·exact a0 A1 A2 ih1 h1 Y hv m.1 m.2 a1.1 a1.2 l
  ·have h2:A2.count u=1:=Y;obtain ⟨L,R,a7,a8,bm,ec,ej⟩:=a0 A2 A1 ih2 h2 Y Y m.2 m.1 a1.2 a1.1 l.symm;refine ⟨L,R,λx h1 h2=>by rw[MTree.eval,bR];exact a7 x h1 h2,a8,bm,λw hw r x k=>?_,λw hw p x k=>?_⟩
   ·simp only[MTree.count] at hw;simp only[MTree.eval] at k ⊢;rw[bR] at k ⊢;exact ec w Y r x k
   ·simp only[MTree.count] at hw;simp only[MTree.eval] at k ⊢;rw[bR] at k ⊢;exact ej w Y p x k
 | and A1 A2 _ _=>
  intro u v hu hv m a1 l;simp only[MTree.count] at hu hv;simp only[MTree.eval,bA] at l;by_cases h1:A1.count u=1
  ·have c7:A2.count u=0:=Y;have b6:A2.eval (single v)=true:=by
    rw[← dg A2 c7];exact l.2
   have c8:A2.count v=1:=by have:=ed A2 b6;omega
   have c5:A1.count v=0:=Y;have c2:A1.eval (single u)=true:=(by rw[← dQ A1 c5];exact l.1);refine ⟨A1,A2,λx hx1 hx2=>by simp[MTree.eval,hx1,hx2],c2,b6,?_,?_⟩
   ·intro w hw r x k;have a5:=ed A1 r;simp only[MTree.count] at hw;have a2:A2.count w=0:=Y
    simp only[MTree.eval,bA] at k;exact oR (by rw[← dg A2 a2];exact k.2)
   ·intro w hw p x k;have a2:=ed A2 p;simp only[MTree.count] at hw;have a5:A1.count w=0:=Y
    simp only[MTree.eval,bA] at k;exact oR (by rw[← dQ A1 a5];exact k.1)
  ·have c7:A2.count u=1:=Y;have er:A1.count u=0:=Y
   have b5:A1.eval (single v)=true:=(by rw[← dg A1 er];exact l.1);have c5:A1.count v=1:=by have:=ed A1 b5;omega
   have c8:A2.count v=0:=Y;have c6:A2.eval (single u)=true:=(by rw[← dQ A2 c8];exact l.2);refine ⟨A2,A1,λx hx1 hx2=>by simp[MTree.eval,hx1,hx2],c6,b5,?_,?_⟩
   ·intro w hw r x k;have a2:=ed A2 r;simp only[MTree.count] at hw;have a5:A1.count w=0:=Y
    simp only[MTree.eval,bA] at k;exact oR (by rw[← dg A1 a5];exact k.1)
   ·intro w hw p x k;have a5:=ed A1 p;simp only[MTree.count] at hw;have a2:A2.count w=0:=Y
    simp only[MTree.eval,bA] at k;exact oR (by rw[← dQ A2 a2];exact k.2)
lemma pO (A B:MTree)(hm:∀v:F0,A.count v+B.count v≤2)(ej:∀v:F0,(A.and B).eval (single v)=false)(e5:∀u v:F0,(A.and B).eval (aL u v)=true->aH u v):4*((univ:Finset (F0×F0)).filter (λp=>p.1.val<p.2.val/\(A.and B).eval (aL p.1 p.2)=true)).card≤3*(A.leaves+B.leaves):=by
 classical
 let T:=A.and B
 let m:F0->Nat:=λv=>A.count v+B.count v
 let SA:S0:=univ.filter (λv=>A.eval (single v)=true)
 let SB:S0:=univ.filter (λv=>B.eval (single v)=true)
 let NT:F0->S0:=λu=>univ.filter (λv=>T.eval (aL u v)=true)
 let r:F0->Nat:=λu=>(NT u).card
 have a3:∀v,v∈SA<->A.eval (single v)=true:=λv=>by simp[SA]
 have a4:∀v,v∈SB<->B.eval (single v)=true:=λv=>by simp[SB]
 have a0:∀u v,v∈NT u<->T.eval (aL u v)=true:=λu v=>by simp[NT]
 have k:∀u v,v∈NT u->u∈NT v:=λu v h=>by
  rw[a0] at h ⊢;rwa[fr T v u]
 have e2:∀u v,v∈NT u->aH u v:=λu v h=>e5 u v ((a0 u v).1 h);have fz:∀u,r u≤3:=λu=>by
  have ev:NT u⊆aX u:=λv hv=>ce.2 (e2 u v hv);exact (cL ev).trans (dH u).le
 have hb:Disjoint SA SB:=(by rw[dL];intro v qh qz;have h1:=ej v;simp only[MTree.eval,(a3 v).1 qh,(a4 v).1 qz,Bool.and_self] at h1;exact bF h1.symm);have b5:∀u∈SA,∀v∈SB,aH u v:=(by intro u hu v hv;refine e5 u v ?_;simp only[MTree.eval,bA];exact ⟨dc A (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) ((a3 u).1 hu),dc B (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) ((a4 v).1 hv)⟩);have ca:SA.card≤1\/SB.card≤1:=by
  by_contra h;push Not at h;obtain ⟨u1,hU,u2,p9,n8⟩:=oC.1 h.1;obtain ⟨v1,pr,v2,qb,p2⟩:=oC.1 h.2;exact eW u1 v1 u2 v2 n8 p2 (b5 u1 hU v1 pr)
   (bh (b5 u2 p9 v1 pr)) (b5 u2 p9 v2 qb) (bh (b5 u1 hU v2 qb))
 have b1:∀u v,v∈NT u->B.count u=0->v∈SB:=(by intro u v b6 ko;have ht:T.eval (aL u v)=true:=(a0 u v).1 b6;simp only[T,MTree.eval,bA] at ht;rw[dg B ko] at ht;exact (a4 v).2 ht.2);have a8:∀u v,v∈NT u->A.count u=0->v∈SA:=(by intro u v b6 j0;have ht:T.eval (aL u v)=true:=(a0 u v).1 b6;simp only[T,MTree.eval,bA] at ht;rw[dg A j0] at ht;exact (a3 v).2 ht.1);have a2:∀u v,v∈NT u->1≤m u:=by
  intro u v b6;by_contra hc;have j0:A.count u=0:=by dsimp[m] at hc;omega
  have ko:B.count u=0:=by dsimp[m] at hc;omega
  exact dL.1 hb (a8 u v b6 j0) (b1 u v b6 ko)
 have c0:∀u,m u=1->(A.count u=1/\B.count u=0)\/(A.count u=0/\B.count u=1):=(by intro u hu;dsimp[m] at hu;omega);have ez:∀u v,v∈NT u->m u=1->m v=1->2≤r u->2≤r v->False:=by
  intro u v b6 n1 la gs nB;rcases c0 u n1 with ⟨g6,g9⟩|⟨g6,g9⟩
  ·have hI:v∈SB:=b1 u v b6 g9;have m8:1≤B.count v:=ed B ((a4 v).1 hI);have p8:A.count v=0:=by dsimp[m] at la;omega
   have hd:NT u⊆SB:=λw hw=>b1 u w hw g9;have hj:NT v⊆SA:=λw hw=>a8 v w hw p8;have h1:=cL hd;have h2:=cL hj;dsimp[r] at gs nB;rcases ca with qq|qw<;>omega
  ·have hD:v∈SA:=a8 u v b6 g6;have p8:1≤A.count v:=ed A ((a3 v).1 hD);have m8:B.count v=0:=by dsimp[m] at la;omega
   have hj:NT u⊆SA:=λw hw=>a8 u w hw g6;have hd:NT v⊆SB:=λw hw=>b1 v w hw m8;have h1:=cL hj;have h2:=cL hd;dsimp[r] at gs nB;rcases ca with qq|qw<;>omega
 let hr:F0->Prop:=λx=>
  x∈SB/\∃u∈SA,A.count u=1/\B.count u=0/\2≤r u/\x∈NT u
 let hn:F0->Prop:=λx=>
  x∈SA/\∃u∈SB,A.count u=0/\B.count u=1/\2≤r u/\x∈NT u
 let a5:F0->Prop:=λx=>hr x\/hn x
 have b8:∀x,hr x->2≤SB.card/\SA.card≤1:=(by rintro x ⟨-,u,-,-,g9,gs,-⟩;have ev:NT u⊆SB:=λw hw=>b1 u w hw g9;have h2:2≤SB.card:=lT gs (cL ev);exact ⟨h2,ca.resolve_right Y⟩);have ct:∀x,hn x->2≤SA.card/\SB.card≤1:=(by rintro x ⟨-,u,-,g6,-,gs,-⟩;have ev:NT u⊆SA:=λw hw=>a8 u w hw g6;have h2:2≤SA.card:=lT gs (cL ev);exact ⟨h2,ca.resolve_left Y⟩);have c1:∀x y,y∈NT x->a5 x->a5 y->False:=by
  intro x y hN hx hy;rcases hx with n7|n4<;>rcases hy with pa|nl
  ·obtain ⟨d1,u,iy,-,-,-,-⟩:=n7;exact gJ u x y (b5 u iy x d1) (e2 x y hN) (bh (b5 u iy y pa.1))
  ·have:=b8 x n7;have:=ct y nl;omega
  ·have:=ct x n4;have:=b8 y pa;omega
  ·obtain ⟨d2,u,h7,-,-,-,-⟩:=n4;exact gJ u x y (bh (b5 x d2 u h7)) (e2 x y hN) (b5 y nl.1 u h7)
 have cb:∀(P Q:MTree),(∀v:F0,P.count v+Q.count v≤2)->(∀v:F0,(P.and Q).eval (single v)=false)->(∀u v:F0,(P.and Q).eval (aL u v)=true->aH u v)->∀v u:F0,Q.eval (single v)=true->P.count u=1->Q.count u=0->P.eval (single u)=false->(P.and Q).eval (aL u v)=true->2≤(univ.filter (λw=>(P.and Q).eval (aL u w)=true)).card->(univ.filter (λx=>(P.and Q).eval (aL v x)=true)).card≤2:=by
  intro P Q ho c5 l v u e1 lo qi ik b6 gs;have ql:1≤Q.count v:=ed Q e1;have qf:P.count v≤1:=by have:=ho v;omega
  have hH:P.eval (single v)=false:=(by have h1:=c5 v;simp only[MTree.eval,e1,av] at h1;exact h1);have hG:P.eval (aL u v)=true:=(by simp only[MTree.eval,bA] at b6;exact b6.1);have hW:P.count v=1:=by
   by_contra hc;have nR:P.count v=0:=Y
   rw[dQ P nR,ik] at hG;exact bF hG
  obtain ⟨L,R,jb,qk,ks,k3,iz⟩:=i9 P u v lo hW ik hH hG;obtain ⟨v',b2,f0⟩:∃v',(P.and Q).eval (aL u v')=true/\v'≠v:=by
   have hl:0<((univ.filter (λw=>(P.and Q).eval (aL u w)=true)).erase v).card:=by
    have:=card_erase_le (s:=univ.filter (λw=>(P.and Q).eval (aL u w)=true)) (a:=v);have hL:v∈univ.filter (λw=>(P.and Q).eval (aL u w)=true):=by simp[b6]
    rw[cE hL];omega
   obtain ⟨v',hh⟩:=cO.1 hl;rw[mE,mF] at hh;exact ⟨v',hh.2.2,hh.1⟩
  have eu:Q.eval (single v')=true:=(by simp only[MTree.eval,bA] at b2;rw[← dg Q qi];exact b2.2);have k0:P.eval (single v')=false:=(by have h1:=c5 v';simp only[MTree.eval,eu,av] at h1;exact h1);have oz:R.eval (single v')=true:=by
   simp only[MTree.eval,bA] at b2;rcases k3 u lo qk v' b2.1 with h1|h2
   ·rw[k0] at h1;exact absurd h1 bF
   ·exact h2
  let SP:S0:=univ.filter (λx=>P.eval (single x)=true)
  have p1:SP.card≤1:=by
   by_contra qc;obtain ⟨a,ha,c,hc,qj⟩:=oC.1 (by omega:1<SP.card);simp only[SP,mF,mV,ae] at ha hc
   have hs:∀p q,P.eval (single p)=true->Q.eval (single q)=true->aH p q:=λp q hp hq=>
    l p q (by
     simp only[MTree.eval,bA]
     exact ⟨dc P (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) hp,dc Q (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) hq⟩)
   exact eW a v c v' qj f0.symm (hs a v ha e1)
    (bh (hs c v hc e1)) (hs c v' hc eu) (bh (hs a v' ha eu))
  have ev:univ.filter (λx=>(P.and Q).eval (aL v x)=true)⊆insert u SP:=by
   intro x hx;simp only[mF,mV,ae] at hx;rw[fr (P.and Q) v x] at hx;by_cases k7:P.eval (single x)=true
   ·exact mK (by simp[SP,k7])
   ·rw[bT] at k7;have pb:P.eval (aL x v)=true:=by
     simp only[MTree.eval,bA] at hx;exact hx.1
    have i7:L.eval (single x)=true:=by
     rcases iz v hW ks x pb with h1|h2
     ·rw[k7] at h1;exact absurd h1 bF
     ·exact h2
    have n2:aH x v':=l x v' (by
     simp only[MTree.eval,bA]
     refine ⟨jb (aL x v') (dc L (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) i7) (dc R (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) oz),dc Q (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) eu⟩)
    have qm:x=u:=by
     by_contra hk;exact eW x v u v' hk f0.symm (l x v hx)
      (bh (l u v b6)) (l u v' b2) (bh n2)
    rw[qm];exact mL u SP
  exact (cL ev).trans ((card_insert_le u SP).trans Y)
 have a7:∀(P Q:MTree),(∀v:F0,P.count v+Q.count v≤2)->(∀v:F0,(P.and Q).eval (single v)=false)->(∀u v:F0,(P.and Q).eval (aL u v)=true->aH u v)->∀v u1 u2 y:F0,Q.eval (single v)=true->P.eval (single u1)=true->P.count u1=1->Q.count u1=0->2≤(univ.filter (λw=>(P.and Q).eval (aL u1 w)=true)).card->(P.and Q).eval (aL u1 v)=true->P.count u2+Q.count u2=2->(P.and Q).eval (aL u2 v)=true->y≠v->(P.and Q).eval (aL u2 y)=true->(univ.filter (λx=>(P.and Q).eval (aL y x)=true)).card=1:=by
  intro P Q ho c5 l v u1 u2 y e1 hz qA p7 d0 c6 fi c2 g5 b0;have ql:1≤Q.count v:=ed Q e1;have fl:∀w,Q.eval (single w)=true->P.eval (single w)=false:=λw hw=>by
   have h1:=c5 w;simp only[MTree.eval,hw,av] at h1;exact h1
  have lc:∀w,P.eval (single w)=true->Q.eval (single w)=false:=λw hw=>by
   have h1:=c5 w;simp only[MTree.eval,hw,aw] at h1;exact h1
  have a6:∀p q,P.eval (single p)=true->Q.eval (single q)=true->aH p q:=λp q hp hq=>
   l p q (by
    simp only[MTree.eval,bA]
    exact ⟨dc P (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) hp,dc Q (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) hq⟩)
  obtain ⟨v',b2,f0⟩:∃v',(P.and Q).eval (aL u1 v')=true/\v'≠v:=(by have hL:v∈univ.filter (λw=>(P.and Q).eval (aL u1 w)=true):=(by simp[c6]);have hl:0<((univ.filter (λw=>(P.and Q).eval (aL u1 w)=true)).erase v).card:=(by rw[cE hL];omega);obtain ⟨v',hh⟩:=cO.1 hl;rw[mE,mF] at hh;exact ⟨v',hh.2.2,hh.1⟩);have eu:Q.eval (single v')=true:=(by simp only[MTree.eval,bA] at b2;rw[← dg Q p7];exact b2.2);have e0:∀w,P.eval (single w)=true->w=u1:=by
   intro w hw;by_contra hk;exact eW w v u1 v' hk f0.symm (a6 w v hw e1)
    (bh (a6 u1 v hz e1)) (a6 u1 v' hz eu) (bh (a6 w v' hw eu))
  have f3:u2≠u1:=by intro h;subst h;omega
  have ll:1≤P.count u2:=by
   by_contra hc;have h0:P.count u2=0:=Y
   simp only[MTree.eval,bA] at c2;rw[dg P h0,fl v e1] at c2;exact bF c2.1
  have lb:1≤Q.count u2:=by
   by_contra hc;have h0:Q.count u2=0:=Y
   have hg:=b0;simp only[MTree.eval,bA] at hg;rw[dg Q h0] at hg;exact eW u1 v u2 y f3.symm g5.symm (l u1 v c6)
    (bh (l u2 v c2)) (l u2 y b0) (bh (a6 u1 y hz hg.2))
  have id:P.count u2=1:=Y;have g7:P.eval (single u2)=false:=(by by_contra hc;rw[bN] at hc;exact f3 (e0 u2 hc));have hH:P.eval (single v)=false:=fl v e1;have hi:P.eval (aL u2 v)=true:=(by simp only[MTree.eval,bA] at c2;exact c2.1);have hW:P.count v=1:=by
   have qr:P.count v≤1:=by have:=ho v;omega
   by_contra hc;have h0:P.count v=0:=Y
   rw[dQ P h0,g7] at hi;exact bF hi
  obtain ⟨L,R,jb,l7,ks,k3,iz⟩:=i9 P u2 v id hW g7 hH hi;have k1:y≠u1:=(by intro h;rw[h] at b0;exact gJ u1 v u2 (l u1 v c6) (bh (l u2 v c2)) (l u2 u1 b0));have qa:P.eval (single y)=false:=(by by_contra hc;rw[bN] at hc;exact k1 (e0 y hc));have qt:R.eval (single y)=true:=by
   simp only[MTree.eval,bA] at b0;rcases k3 u2 id l7 y b0.1 with h1|h2
   ·rw[qa] at h1;exact absurd h1 bF
   ·exact h2
  have p0:1≤Q.count y:=by
   by_contra hc;have h0:Q.count y=0:=Y
   have h2:=b0;rw[fr (P.and Q) u2 y] at h2;simp only[MTree.eval,bA] at h2;rw[dg Q h0] at h2;exact gJ u1 v u2 (l u1 v c6) (bh (l u2 v c2))
    (bh (a6 u1 u2 hz h2.2))
  have qu:P.count y=1:=by
   have qr:P.count y≤1:=by have:=ho y;omega
   have hl:1≤P.count y:=by
    by_contra hc;have h0:P.count y=0:=Y
    simp only[MTree.eval,bA] at b0;rw[dQ P h0,g7] at b0;exact bF b0.1
   omega
  have m3:univ.filter (λx=>(P.and Q).eval (aL y x)=true)={u2}:=by
   ext x;simp only[mF,mV,ae,mS];constructor
   ·intro hR;have hN:(P.and Q).eval (aL x y)=true:=by rwa[fr (P.and Q) y x] at hR
    have i4:x≠u1:=by
     intro h;rw[h] at hR;exact eW u1 v u2 y f3.symm g5.symm (l u1 v c6)
      (bh (l u2 v c2)) (l u2 y b0) (l y u1 hR)
    have lw:P.eval (single x)=false:=(by by_contra hc;rw[bN] at hc;exact i4 (e0 x hc));have i7:L.eval (single x)=true:=by
     simp only[MTree.eval,bA] at hN;rcases iz y qu qt x hN.1 with h1|h2
     ·rw[lw] at h1;exact absurd h1 bF
     ·exact h2
    have qs:aH x v:=l x v (by
     simp only[MTree.eval,bA]
     refine ⟨jb (aL x v) (dc L (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) i7) (dc R (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) ks),dc Q (λt ht=>by simp only[single,dT] at ht;simp[aL,ht]) e1⟩)
    by_contra hk;exact eW x v u2 y hk g5.symm qs (bh (l u2 v c2)) (l u2 y b0) (l y x hR)
   ·intro hx;rw[hx,fr (P.and Q) y u2];exact b0
  rw[m3,cS]
 have et:∀w,(B.and A).eval (single w)=false:=λw=>by
  have h1:=ej w;simp only[MTree.eval] at h1 ⊢;rwa[bC]
 have e3:∀p q,(B.and A).eval (aL p q)=true->aH p q:=λp q hpq=>
  e5 p q (by simp only[MTree.eval] at hpq ⊢;rwa[bC])
 have bm:∀p q,(B.and A).eval (aL p q)=T.eval (aL p q):=λp q=>by
  simp only[T,MTree.eval,bC]
 have c7:∀v,(univ.filter (λz=>(B.and A).eval (aL v z)=true)).card=r v:=λv=>by
  congr 1;ext z;simp[bm,NT,T]
 have fc:∀v u,A.eval (single v)=true->B.count u=1->A.count u=0->B.eval (single u)=false->v∈NT u->2≤r u->r v≤2:=λv u hv g9 g6 hBf b6 gs=>by
  have h2:=cb B A (λw=>by have:=hm w;omega) et e3 v u hv g9 g6 hBf
   (by rw[bm];exact (a0 u v).1 b6) (by rw[c7];exact gs)
  rwa[c7] at h2
 have hf:∀v u1 u2 y,A.eval (single v)=true->B.eval (single u1)=true->B.count u1=1->A.count u1=0->2≤r u1->v∈NT u1->m u2=2->v∈NT u2->y≠v->y∈NT u2->r y=1:=λv u1 u2 y hv hU eb ec d0 c6 fi c2 g5 b0=>by
   have h1:=a7 B A (λw=>by have:=hm w;omega) et e3 v u1 u2 y hv hU eb ec
    (by rw[c7];exact d0) (by rw[bm];exact (a0 u1 v).1 c6)
    (by dsimp[m] at fi;omega) (by rw[bm];exact (a0 u2 v).1 c2)
    g5 (by rw[bm];exact (a0 u2 y).1 b0)
   rwa[c7] at h1
 let a1:F0->F0->Nat:=λu v=>
  if r u=1/\r v=1 then 2
  else if r u=1 then 3
  else if r v=1 then 1
  else if m u=1/\m v=2 then 1
  else if m u=2/\m v=1 then 3
  else if a5 u/\¬a5 v then 1
  else if ¬a5 u/\a5 v then 3
  else 2
 have hA:∀u v,v∈NT u->4≤a1 u v+a1 v u:=by
  intro u v b6;have p3:=k u v b6;have n1:1≤m u/\m u≤2:=⟨a2 u v b6,hm u⟩;have la:1≤m v/\m v≤2:=⟨a2 v u p3,hm v⟩;dsimp only[a1];by_cases h1:r u=1<;>by_cases h2:r v=1
  ·simp[h1,h2]
  ·simp[h1,h2]
  ·simp[h1,h2]
  ·have qd:2≤r u:=by
    have:1≤r u:=cO.2 ⟨v,b6⟩;omega
   have m2:2≤r v:=(by have:1≤r v:=cO.2 ⟨u,p3⟩;omega);by_cases h9:m u=1<;>by_cases ih:m v=1
   ·exact (ez u v b6 h9 ih qd m2).elim
   ·have hK:m v=2:=Y;simp[h1,h2,h9,hK]
   ·have fi:m u=2:=Y;simp[h1,h2,fi,ih]
   ·have fi:m u=2:=Y;have hK:m v=2:=Y
    by_cases qo:a5 u<;>by_cases qg:a5 v<;>simp[h1,h2,fi,hK,qo,qg]
 have hO:∀x:F0,∑ y∈NT x,a1 x y≤3*m x:=by
  intro x;by_cases l3:r x=0
  ·have mt:NT x=∅:=cZ.1 l3;rw[mt];simp
  by_cases c8:r x=1
  ·obtain ⟨y,hy⟩:=ac.1 c8;have h4:y∈NT x:=by rw[hy];simp
   have qB:1≤m x:=a2 x y h4;rw[hy,sum_singleton];have qC:a1 x y≤3:=by dsimp only[a1];split_ifs<;>omega
   omega
  have h5:2≤r x:=Y;have hE:1≤m x:=(by obtain ⟨y,hy⟩:=cO.1 (show 0<(NT x).card by dsimp only[r] at h5;omega);exact a2 x y hy);by_cases hJ:m x=1
  ·have n5:∀y∈NT x,a1 x y≤1:=by
    intro y hy;have qD:1≤m y/\m y≤2:=⟨a2 y x (k x y hy),hm y⟩;dsimp only[a1];by_cases c3:r y=1
    ·simp[c8,c3]
    ·have ea:2≤r y:=by
      have:1≤r y:=cO.2 ⟨x,k x y hy⟩;omega
     have e4:m y=2:=(by by_contra hc;exact ez x y hy hJ Y h5 ea);simp[c8,c3,hJ,e4]
   calc ∑ y∈NT x,a1 x y≤∑ _y∈NT x,1:=sM n5
    _=r x:=by simp[r]
    _≤3*m x:=by have:=fz x;omega
  have g1:m x=2:=by have:=hm x;dsimp only[m] at hJ hE ⊢;omega
  by_cases p6:r x=2
  ·have m1:∀y∈NT x,a1 x y≤3:=λy _=>by dsimp only[a1];split_ifs<;>omega
   calc ∑ y∈NT x,a1 x y≤∑ _y∈NT x,3:=sM m1
    _=3*r x:=by simp[r,nM]
    _≤3*m x:=Y
  have h8:r x=3:=by have:=fz x;omega
  by_cases g3:a5 x
  ·have hT:∃u1∈NT x,∀y∈NT x,y≠u1->a1 x y≤1:=by
    have ls:=g3;rcases ls with ⟨d1,u1,f2,ec,eb,d0,g0⟩|⟨d2,u1,f1,ec,eb,d0,g0⟩
    ·refine ⟨u1,k u1 x g0,λy hy hyne=>?_⟩;have hF:¬a5 y:=λhhy=>c1 x y hy g3 hhy;dsimp only[a1];by_cases c3:r y=1
     ·simp[c8,c3]
     ·have ea:2≤r y:=by
       have:1≤r y:=cO.2 ⟨x,k x y hy⟩;omega
      have e4:m y=2:=by
       by_contra g8;have e7:m y=1:=(by have h1:=a2 y x (k x y hy);have h2:=hm y;dsimp only[m] at g8 h1 ⊢;omega);rcases c0 y e7 with ⟨er,es⟩|⟨er,es⟩
       ·have h3:A.eval (single y)=false:=by
         by_contra hc;rw[bN] at hc;have qe:=(b8 x ⟨d1,u1,f2,ec,eb,d0,g0⟩).2;have g2:y∈SA:=(a3 y).2 hc;have hM:y=u1:=cQ.1 qe y g2 u1 f2;exact hyne hM
        have h2:=cb A B hm ej e5 x y ((a4 x).1 d1) er es h3
         ((a0 y x).1 (k x y hy)) ea
        have qx:r x≤2:=h2;omega
       ·have d2:x∈SA:=a8 y x (k x y hy) er;exact dL.1 hb d2 d1
      simp[c8,c3,g1,e4,g3,hF]
    ·refine ⟨u1,k u1 x g0,λy hy hyne=>?_⟩;have hF:¬a5 y:=λhhy=>c1 x y hy g3 hhy;dsimp only[a1];by_cases c3:r y=1
     ·simp[c8,c3]
     ·have ea:2≤r y:=by
       have:1≤r y:=cO.2 ⟨x,k x y hy⟩;omega
      have e4:m y=2:=by
       by_contra g8;have e7:m y=1:=(by have h1:=a2 y x (k x y hy);have h2:=hm y;dsimp only[m] at g8 h1 ⊢;omega);rcases c0 y e7 with ⟨er,es⟩|⟨er,es⟩
       ·have d1:x∈SB:=b1 y x (k x y hy) es;exact dL.1 hb d2 d1
       ·have hX:B.eval (single y)=false:=by
         by_contra hc;rw[bN] at hc;have n3:=(ct x ⟨d2,u1,f1,ec,eb,d0,g0⟩).2;have g4:y∈SB:=(a4 y).2 hc;have hM:y=u1:=cQ.1 n3 y g4 u1 f1;exact hyne hM
        have h2:=fc x y ((a3 x).1 d2) es er hX (k x y hy) ea;omega
      simp[c8,c3,g1,e4,g3,hF]
   obtain ⟨u1,ix,hC⟩:=hT;have hQ:∑ y∈NT x,a1 x y=a1 x u1+∑ y∈(NT x).erase u1,a1 x y:=(aE (NT x) (a1 x) ix).symm;have qy:a1 x u1≤3:=by dsimp only[a1];split_ifs<;>omega
   have k2:∑ y∈(NT x).erase u1,a1 x y≤∑ _y∈(NT x).erase u1,1:=sM (λy hy=>hC y (mO hy) (ne_of_mem_erase hy));have i0:((NT x).erase u1).card=2:=by rw[cE ix];dsimp[r] at h8;omega
   simp only[sum_const,az,mul_one,i0] at k2;omega
  ·by_cases hP:∃v∈NT x,a5 v
   ·obtain ⟨v,hS,qp⟩:=hP;have hZ:∀y∈NT x,y≠v->r y=1:=by
     intro y l0 g5;rcases qp with ⟨hI,u1,f2,ec,eb,d0,c6⟩|⟨hD,u1,f1,ec,eb,d0,c6⟩
     ·exact a7 A B hm ej e5 v u1 x y
       ((a4 v).1 hI) ((a3 u1).1 f2) ec eb d0
       ((a0 u1 v).1 c6) g1 ((a0 x v).1 hS) g5 ((a0 x y).1 l0)
     ·exact hf v u1 x y ((a3 v).1 hD) ((a4 u1).1 f1) eb ec d0 c6 g1 hS g5 l0
    have hQ:∑ y∈NT x,a1 x y=a1 x v+∑ y∈(NT x).erase v,a1 x y:=(aE (NT x) (a1 x) hS).symm;have qy:a1 x v≤3:=by dsimp only[a1];split_ifs<;>omega
    have k2:∑ y∈(NT x).erase v,a1 x y≤∑ _y∈(NT x).erase v,1:=sM (λy hy=>by
      have qv:=hZ y (mO hy) (ne_of_mem_erase hy)
      dsimp only[a1];simp[c8,qv])
    have i0:((NT x).erase v).card=2:=by rw[cE hS];dsimp[r] at h8;omega
    simp only[sum_const,az,mul_one,i0] at k2;omega
   ·have l4:∀y∈NT x,a1 x y≤2:=by
     intro y hy;have hF:¬a5 y:=λhhy=>hP ⟨y,hy,hhy⟩;dsimp only[a1];by_cases c3:r y=1
     ·simp[c8,c3]
     ·have ea:2≤r y:=by
       have:1≤r y:=cO.2 ⟨x,k x y hy⟩;omega
      by_cases e7:m y=1
      ·exfalso;rcases c0 y e7 with ⟨er,es⟩|⟨er,es⟩
       ·have d1:x∈SB:=b1 y x (k x y hy) es;by_cases g2:A.eval (single y)=true
        ·exact g3 (oL ⟨d1,y,(a3 y).2 g2,er,es,ea,k x y hy⟩)
        ·rw[bT] at g2;have h2:=cb A B hm ej e5 x y ((a4 x).1 d1) er es g2
          ((a0 y x).1 (k x y hy)) ea
         have qx:r x≤2:=h2;omega
       ·have d2:x∈SA:=a8 y x (k x y hy) er;by_cases g4:B.eval (single y)=true
        ·exact g3 (oR ⟨d2,y,(a4 y).2 g4,er,es,ea,k x y hy⟩)
        ·rw[bT] at g4;have h2:=fc x y ((a3 x).1 d2) es er g4 (k x y hy) ea;omega
      ·have e4:m y=2:=by
        have h1:=a2 y x (k x y hy);have h2:=hm y;dsimp only[m] at e7 h1 ⊢;omega
       simp[c8,c3,g1,e4,g3,hF]
    calc ∑ y∈NT x,a1 x y≤∑ _y∈NT x,2:=sM l4
     _=2*r x:=by simp[r,nM]
     _≤3*m x:=Y
 let E_lt:=(univ:Finset (F0×F0)).filter
  (λp=>p.1.val<p.2.val/\T.eval (aL p.1 p.2)=true)
 let E_gt:=(univ:Finset (F0×F0)).filter
  (λp=>p.2.val<p.1.val/\T.eval (aL p.1 p.2)=true)
 let E_all:=(univ:Finset (F0×F0)).filter
  (λp=>T.eval (aL p.1 p.2)=true)
 have i3:E_all=E_lt∪E_gt:=by
  ext ⟨u,v⟩;simp only[E_all,E_lt,E_gt,mU,mF,mV,ae];constructor
  ·intro h;have hk:u≠v:=λhe=>by
    subst he;have h1:T.eval (aL u u)=T.eval (single u):=(by congr 1;funext w;simp[aL,single]);rw[h1,ej u] at h;exact bF h
   rcases nT u.val v.val with qn|hM|qc
   ·exact oL ⟨qn,h⟩
   ·exact (hk (Fin.ext hM)).elim
   ·exact oR ⟨qc,h⟩
  ·rintro (⟨-,h⟩|⟨-,h⟩)<;>exact h
 have hY:Disjoint E_lt E_gt:=(by rw[dL];intro ⟨u,v⟩ h1 h2;simp only[E_lt,E_gt,mF,mV,ae] at h1 h2;omega);have i5:∑ p∈E_gt,a1 p.1 p.2=∑ p∈E_lt,a1 p.2 p.1:=by
  refine sum_nbij (λp=>(p.2,p.1)) ?_ ?_ ?_ ?_
  ·intro ⟨u,v⟩ h;simp only[E_gt,E_lt,mF,mV,ae] at h ⊢;exact ⟨h.1,by rw[fr];exact h.2⟩
  ·intro ⟨u1,v1⟩ _ ⟨u2,v2⟩ _ h;simp only[ay] at h;exact pE h.2 h.1
  ·intro ⟨u,v⟩ h;refine ⟨(v,u),?_,rfl⟩;simp only[mem_coe,E_gt,E_lt,mF,mV,ae] at h ⊢;exact ⟨h.1,by rw[fr];exact h.2⟩
  ·intro _ _;rfl
 have hB:∑ p∈E_all,a1 p.1 p.2=∑ x:F0,∑ y∈NT x,a1 x y:=by
  rw[sum_sigma' univ NT (λx y=>a1 x y)];refine sum_nbij (λp=>(⟨p.1,p.2⟩:Σ _:F0,F0)) ?_ ?_ ?_ ?_
  ·intro ⟨u,v⟩ h;simp only[E_all,mF,mV,ae] at h;simp[mG,NT,h]
  ·intro ⟨u1,v1⟩ _ ⟨u2,v2⟩ _ h;simp only[Sigma.mk.inj_iff,heq_eq_eq] at h;exact pE h.1 h.2
  ·intro ⟨u,v⟩ h;simp only[mem_coe,mG,mV,ae,NT,mF] at h;exact ⟨(u,v),by simp[E_all,h],rfl⟩
  ·intro _ _;rfl
 have h6:4*E_lt.card≤∑ p∈E_all,a1 p.1 p.2:=by
  rw[i3,ap hY,i5,← sD]
  calc 4*E_lt.card=∑ _p∈E_lt,4:=by simp[nM]
   _≤∑ p∈E_lt,(a1 p.1 p.2+a1 p.2 p.1):=sM (λp hp=>hA p.1 p.2 ((a0 p.1 p.2).2 (mF.1 hp).2.2))
 have ja:∑ x:F0,∑ y∈NT x,a1 x y≤3*(A.leaves+B.leaves):=by
  calc ∑ x:F0,∑ y∈NT x,a1 x y
    ≤∑ x:F0,3*m x:=sM (λx _=>hO x)
   _=3*∑ x:F0,(A.count x+B.count x):=by rw[← mul_sum]
   _=3*(A.leaves+B.leaves):=(by rw[sD,← gO A,← gO B])
 rw[hB] at h6;exact h6.trans ja
lemma nz (T:MTree)(hm:∀v:F0,T.count v≤2)(k:∀v:F0,T.eval (single v)=false)(l:∀u v:F0,T.eval (aL u v)=true->aH u v):4*((univ:Finset (F0×F0)).filter (λp=>p.1.val<p.2.val/\T.eval (aL p.1 p.2)=true)).card≤3*T.leaves:=by
 induction T with
 | leaf v=>
  have r:=k v;simp[MTree.eval,single] at r
 | and A B _ _=>
  exact pO A B hm k l
 | or A B ihA ihB=>
  have a5:∀v,A.count v≤2:=λv=>by have:=hm v;simp only[MTree.count] at this;omega
  have a4:∀v,B.count v≤2:=λv=>by have:=hm v;simp only[MTree.count] at this;omega
  have a1:∀v,A.eval (single v)=false:=λv=>by
   have:=k v;simp only[MTree.eval,Bool.or_eq_false_iff] at this;exact this.1
  have a3:∀v,B.eval (single v)=false:=λv=>by
   have:=k v;simp only[MTree.eval,Bool.or_eq_false_iff] at this;exact this.2
  have a0:∀u v,A.eval (aL u v)=true->aH u v:=λu v h=>
   l u v (by simp[MTree.eval,h])
  have a2:∀u v,B.eval (aL u v)=true->aH u v:=λu v h=>
   l u v (by simp[MTree.eval,h])
  have m:(univ:Finset (F0×F0)).filter
    (λp=>p.1.val<p.2.val/\(A.or B).eval (aL p.1 p.2)=true)⊆
   (univ:Finset (F0×F0)).filter
    (λp=>p.1.val<p.2.val/\A.eval (aL p.1 p.2)=true)∪
   (univ:Finset (F0×F0)).filter
    (λp=>p.1.val<p.2.val/\B.eval (aL p.1 p.2)=true):=by
   intro p hp;simp only[mU,mF,mV,ae,MTree.eval,bO] at hp ⊢;rcases hp.2 with r|h2
   ·exact oL ⟨hp.1,r⟩
   ·exact oR ⟨hp.1,h2⟩
  have hc:=(cL m).trans (ao _ _);have r:=ihA a5 a1 a0;have h2:=ihB a4 a3 a2;simp only[MTree.leaves];omega
lemma kq {D:aJ}(h:a9 14 D)(hD:be D)(hT:fu D)(hh:∀x:F0,(aG 14 D x).card≤2)(s:Bool){l p1 p2:F0}(a3:p1≠p2)(d0:aH l p1)(b6:aH l p2)(h1:p1∈O 14 D (W D (26,s)))(h2:p2∈O 14 D (W D (26,s))):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have ho:26<D.length:=by rw[hT.1];omega
 have a5:aO 14 D=14+26:=by unfold aO;rw[hT.1]
 have m:∀v:F0,v∈O 14 D (W D (26,!s))->v=l:=by
  intro v hv
  have f3:aH p1 v:=(ds p1 v).1 ((hD _).1 (by
   rw[a5,cc hS _ ho s,hT.2.1,gop_true,bA]
   exact ⟨cf hS h1 ab,cf hS hv ab⟩))
  have fi:aH p2 v:=(ds p2 v).1 ((hD _).1 (by
   rw[a5,cc hS _ ho s,hT.2.1,gop_true,bA]
   exact ⟨cf hS h2 ab,cf hS hv ab⟩))
  by_contra hI;exact eW p1 v p2 l a3 hI f3 (bh fi) (bh b6) d0
 have k:∀(x y:F0) (e0:A0),e0∈aG 14 D x->y∈O 14 D (W D e0)->y≠x->∀(a b:F0),a≠b->aH x a->aH x b->a∉O 14 D (W D (aI e0))->b∉O 14 D (W D (aI e0))->∃e1:A0,e1∈aG 14 D x/\aI e1∈aG 14 D a/\aI e1∈aG 14 D b/\∀z:F0,z≠x->¬aH y z->z∉O 14 D (W D e1):=by
  intro x y e0 hF hz hA a b hL hH hx c3 d1;obtain ⟨ea,e4,e3,-⟩:=bp hG hS hC hH;obtain ⟨eb,hf,eu,-⟩:=bp hG hS hC hx;have c0:ea≠e0:=λhe=>c3 (he▸(aP.1 e3).2.1);have ct:eb≠e0:=λhe=>d1 (he▸(aP.1 eu).2.1);have hj:aG 14 D x={e0,ea}:=(eS (λw hw=>by rcases mI.1 hw with rfl|hw;exact hF;rw[mS.1 hw];exact e4) (by rw[cP c0.symm];exact hh x)).symm;have b8:eb=ea:=(by have hm:=hf;rw[hj,mI,mS] at hm;exact hm.resolve_left ct);refine ⟨ea,e4,e3,b8▸eu,λz hzx hnyz hzmem=>?_⟩;obtain ⟨ec,hd,hE,hB⟩:=bB h hD (x:=x) (a:=y) (b:=z) hA.symm hzx.symm hnyz;rw[hj,mI,mS] at hd;rcases hd with rfl|rfl
  ·exact hE hz
  ·exact hB hzmem
 obtain ⟨l1,l2,lc,lo,q1,q2,q3,r,ez,g7,g8,b5,c1,b1,g5,g9,cb,b2,hb,g2,g6,g4,g3,c8,c6,ha,f0,e5,gs,f2,ej,c7,hr,hq,hu,fz,e7,g0,c2⟩:=oX l p1 p2 a3 d0 b6
 have et:∀v,v∈O 14 D (W D (26,s))->(26,s)∈aG 14 D v:=λv hv=>
  aP.mpr ⟨by have:=hT.1;omega,hv,by
   have a5:aO 14 D=14+26:=by unfold aO;rw[hT.1]
   rw[← a5,c4 hD];exact nE v⟩
 have g1:(26,s)∈aG 14 D p1:=et p1 h1;have fl:(26,s)∈aG 14 D p2:=et p2 h2
 have d2:l1∉O 14 D (W D (aI (26,s))):=λhm=>
  b5 (m l1 hm▸bh b6)
 have es:l2∉O 14 D (W D (aI (26,s))):=λhm=>
  c1 (m l2 hm▸bh b6)
 have c5:lc∉O 14 D (W D (aI (26,s))):=λhm=>
  cb (m lc hm▸bh d0)
 have ca:lo∉O 14 D (W D (aI (26,s))):=λhm=>
  b2 (m lo hm▸bh d0)
 obtain ⟨e1,-,hn,hc,a0⟩:=k p1 p2 (26,s) g1 h2 a3.symm l1 l2 ez g7 g8 d2 es;obtain ⟨e2,-,hg,hi,p⟩:=k p2 p1 (26,s) fl h1 a3 lc lo b1 g5 g9 c5 ca;have a8:q1∉O 14 D (W D (aI (aI e1))):=(by rw[aT];exact a0 q1 g4 c8);have b0:q2∉O 14 D (W D (aI (aI e1))):=(by rw[aT];exact a0 q2 g3 c6);obtain ⟨f1,hl,hK,ht,bm⟩:=k l1 l2 (aI e1) hn (aP.1 hc).2.1 ez.symm q1 q2 hb g2 g6 a8 b0;have a7:q3∉O 14 D (W D (aI (aI e2))):=(by rw[aT];exact p q3 gs ej);have a6:q2∉O 14 D (W D (aI (aI e2))):=(by rw[aT];exact p q2 f2 c7);obtain ⟨fc,-,hJ,hk,a1⟩:=k lc lo (aI e2) hg (aP.1 hi).2.1 b1.symm q3 q2 ha f0 e5 a7 a6;have a2:aI f1≠aI fc:=by
  intro hy;have hs:f1=fc:=by rw[← aT f1,hy,aT]
  exact a1 l1 g0 c2 (hs▸(aP.1 hl).2.1)
 have hp:aG 14 D q2={aI f1,aI fc}:=(eS (λw hw=>by
    rcases mI.1 hw with rfl|hw
    ·exact ht
    ·rw[mS.1 hw];exact hk)
   (by rw[cP a2];exact hh q2)).symm
 obtain ⟨er,ev,a4,-⟩:=bp hG hS hC hr;rw[hp,mI,mS] at ev;rcases ev with rfl|rfl
 ·rw[aT] at a4;exact bm r hq fz (aP.1 a4).2.1
 ·rw[aT] at a4;exact a1 r hu e7 (aP.1 a4).2.1
lemma l9 {D:aJ}(h:a9 14 D)(hD:be D)(hT:fu D)(ca:∀x:F0,(aG 14 D x).card≤2):(∀s:Bool,∀x:F0,(aX x∩O 14 D (W D (26,s))).card≤1)/\∃s1 s2:F0,O 14 D (aZ D 26)∪O 14 D (aY D 26)⊆{s1,s2}:=by
 have ct:∀s:Bool,∀x:F0,(aX x∩O 14 D (W D (26,s))).card≤1:=(by intro s x;by_contra ea;obtain ⟨p1,a3,p2,a0,a5⟩:=oC.1 (by omega:1<(aX x∩O 14 D (W D (26,s))).card);rw[mN,ce] at a3 a0;exact kq h hD hT ca s a5 a3.1 a0.1 a3.2 a0.2);refine ⟨ct,?_⟩;have p:∀s:Bool,∀a b:F0,a≠b->a∈O 14 D (W D (26,s))->b∈O 14 D (W D (26,s))->¬(a.val<7<->b.val<7):=(by intro s a b r ha hb a4;obtain ⟨l,c3,c8⟩:=pe a b r a4;exact kq h hD hT ca s r c3 c8 ha hb);have m:∀s:Bool,(O 14 D (W D (26,s))).card≤2:=(by intro s;by_contra ea;obtain ⟨a,ha,b,hb,r⟩:=oC.1 (by omega:1<(O 14 D (W D (26,s))).card);have a7:0<((O 14 D (W D (26,s))) \ {a,b}).card:=(by have c1:({a,b}:S0)⊆O 14 D (W D (26,s)):=(by simp[iS,ha,hb]);have:=sP c1;rw[cP r] at this;omega);obtain ⟨c,hc⟩:=cO.1 a7;rw[mD,mI,mS,nO] at hc;have h1:=p s a b r ha hb;have h2:=p s a c (nS hc.2.1) ha hc.1;have h3:=p s b c (nS hc.2.2) hb hc.1;by_cases d0:a.val<7<;>by_cases d1:b.val<7<;>by_cases e0:c.val<7<;>simp_all);have k:∀a∈O 14 D (aZ D 26),∀b∈O 14 D (aY D 26),aH a b:=by
  intro a ha b hb;have c6:26<D.length:=by rw[hT.1];omega
  have cb:aO 14 D=14+26:=by unfold aO;rw[hT.1]
  exact (ds a b).1 ((hD _).1 (by
   rw[cb,cu h.1 _ 26 c6,hT.2.1,gop_true,bA]
   exact ⟨cf h.1 ha ab,cf h.1 hb ab⟩))
 have c0:(O 14 D (aZ D 26)∪O 14 D (aY D 26)).card≤2:=by
  have et:(O 14 D (aZ D 26)).card≤2:=(by simpa[bP] using m false);have ez:(O 14 D (aY D 26)).card≤2:=by simpa[bU] using m true
  by_cases eu:(O 14 D (aZ D 26)).card=2
  ·obtain ⟨a1,bm,a2,a8,b8⟩:=oC.1 (by omega:1<(O 14 D (aZ D 26)).card)
   have c5:O 14 D (aY D 26)=∅:=eO (λb hb=>by
    have h1:=gT a1 b (k a1 bm b hb);have h2:=gT a2 b (k a2 a8 b hb);have h3:=p false a1 a2 b8 (by simpa[bP] using bm) (by simpa[bP] using a8)
    by_cases ej:a1.val<7<;>by_cases es:a2.val<7<;>by_cases d1:b.val<7<;>simp_all)
   rw[c5,union_empty];omega
  ·by_cases ev:(O 14 D (aY D 26)).card=2
   ·obtain ⟨b1,b0,b2,b5,b6⟩:=oC.1 (by omega:1<(O 14 D (aY D 26)).card)
    have c2:O 14 D (aZ D 26)=∅:=eO (λa ha=>by
     have h1:=gT a b1 (k a ha b1 b0);have h2:=gT a b2 (k a ha b2 b5);have h3:=p true b1 b2 b6 (by simpa[bU] using b0) (by simpa[bU] using b5)
     by_cases d0:a.val<7<;>by_cases er:b1.val<7<;>by_cases ec:b2.val<7<;>simp_all)
    rw[c2,empty_union];omega
   ·exact (ao _ _).trans Y
 set U:=O 14 D (aZ D 26)∪O 14 D (aY D 26)
 by_cases d2:U.card=0
 ·refine ⟨0,0,?_⟩;rw[cZ.1 d2];exact empty_subset _
 ·by_cases c7:U.card=1
  ·obtain ⟨s1,eb⟩:=ac.1 c7;refine ⟨s1,s1,?_⟩;rw[eb];simp
  ·obtain ⟨s1,s2,-,a6⟩:=card_eq_two.1 (show U.card=2 by omega);exact ⟨s1,s2,by rw[a6]⟩
noncomputable def bZ (D:aJ)(w:Nat):A0:=
 open Classical in
 if h:∃e∈bc D,W D e=w then Classical.choose h else (0,false)
noncomputable def eY (D:aJ) (b:F0->Nat):Nat->A0->Bool⊕F0
 | 0,e=>Sum.inl e.2
 | k+1,e=>
  open Classical in
  if e.1=26 then Sum.inl e.2
  else if h:∃z:F0,14+e.1=b z then Sum.inr (Classical.choose h)
  else eY D b k (bZ D (14+e.1))
noncomputable def bj (D:aJ)(b:F0->Nat)(e:A0):Bool⊕F0:=
 eY D b 28 e
def gi (D:aJ)(b:F0->Nat)(e1 e2:A0):Prop:=
 e1.1<26/\(∀r:F0,14+e1.1≠b r)/\e2=bZ D (14+e1.1)
def dq (D:aJ)(b:F0->Nat)(e1 e2:A0):Prop:=
 rG (gi D b) e1 e2
def fZ (t:Bool)(l r:Option MTree):Option MTree:=
 if t=true then
  match l,r with|some tl,some tr=>some (.and tl tr)|_,_=>none
 else
  match l,r with
  | some tl,some tr=>some (.or tl tr)|some tl,none=>some tl
  | none,some tr=>some tr|none,none=>none
noncomputable def fo (D:aJ) (b:F0->Nat) (oz:Option (F0)):Nat->Nat->Option MTree
 | 0,_=>none
 | k+1,w=>
  open Classical in
  if oz.any (λz=>decide (w=z.val)) then none
  else if h:∃y:F0,some y≠oz/\w=b y then some (.leaf (Classical.choose h))
  else if 14≤w then
   fZ (bf D (w-14)) (fo D b oz k (aZ D (w-14))) (fo D b oz k (aY D (w-14)))
  else none
def cx:Option MTree->(F0->Bool)->Bool
 | none,_=>false
 | some t,x=>t.eval x
def cB:Option MTree->F0->Nat
 | none,_=>0
 | some t,v=>t.count v
def ey:Option MTree->Nat
 | none=>0
 | some t=>t.leaves
lemma jV {D:aJ}(h:a9 14 D)(hD:be D)(sn:cg D)(rM:bH 14 D≤14)(hI:aN 14 D=∅):False:=by
 classical
 have hG:=bn;have hC:=bl hD;have hS:=h.1;have hL:=h.2.1
 have b8:∀x:F0,x∈aW 14 D:=λx=>
  ai.1 (λhc=>by have:=cl.2 hc;rw[hI] at this;exact nE _ this)
 have qU:(aW 14 D).card=14:=(by have:=db 14 D;rw[hI,ad] at this;omega);obtain ⟨b,qb⟩:=dB hG hS hC;have hb:cn 14 D b:=cX qb;have q2:14≤br 14 D:=by have:=iD hS b hb;omega
 have sL:=dn 14 D;have rX:br 14 D=14:=Y
 have r5:bu 14 D=0:=Y;have qz:D.length=27:=by have:=jm h;omega
 have hT:fu D:=lu sn qz;have n4:aO 14 D=14+26:=by unfold aO;omega
 have fz:aR 14 D b=∅:=cZ.1 (by
  have:=dd hS b hb;omega)
 have a4:∀x:F0,O 14 D (b x)={x}:=λx=>(hb x (b8 x)).2;have jb:fI b:=λx y f3=>by
  have h1:=a4 x;rw[f3,a4 y] at h1;exact sJ h1.symm
 have a5:∀x:F0,b x<aO 14 D:=λx=>by
  have h2:=(hb x (b8 x)).1;have e7:=ew hS (show 1≤aS D (b x) by omega);omega
 have nB:∀x:F0,aS D (b x)=2:=by
  intro x;have sE:2≤aS D (b x):=(hb x (b8 x)).1;by_contra h5;have sz:3≤aS D (b x):=Y
  have hu:(⟨b x,1⟩:P0)∈aR 14 D b:=(by rw[aR,mD,dr,mF,dh,cz];refine ⟨⟨⟨by dsimp only;have:=a5 x;unfold aO at this;omega,by show 1+1<aS D (b x);omega⟩,by rw[a4 x];exact singleton_nonempty x⟩,?_⟩;intro hm;obtain ⟨y,-,hE⟩:=mM.1 hm;exact absurd (Sigma.mk.inj_iff.1 hE).2 ab);rw[fz] at hu;exact nE _ hu
 have mt:∀w<aO 14 D,(∀x:F0,w≠b x)->aS D w=1:=by
  intro w hw rp;have sy:1≤aS D w:=hL w (by unfold aO at hw;omega);by_contra h5;have ry:2≤aS D w:=Y
  have pb:(O 14 D w).Nonempty:=eB hS r5 ry;have hu:(⟨w,0⟩:P0)∈aR 14 D b:=(by rw[aR,mD,dr,mF,dh,cz];refine ⟨⟨⟨by dsimp only;unfold aO at hw;omega,by show 0+1<aS D w;omega⟩,pb⟩,?_⟩;intro hm;obtain ⟨y,-,hE⟩:=mM.1 hm;exact rp y (kA Sigma.fst hE).symm);rw[fz] at hu;exact nE _ hu
 have su:∀x:F0,(aG 14 D x).card≤2:=λx=>by
  have h1:=ff hG h hC b hb x;rw[fz] at h1;have h2:(({x}:S0)∩aW 14 D).card≤1:=(cL iL).trans ab;simp only[filter_empty,ad] at h1;omega
 obtain ⟨qX,s1,s2,qF⟩:=l9 h hD hT su;have b2:∀w<aO 14 D,(∀x:F0,w≠b x)->bZ D w∈bc D/\W D (bZ D w)=w/\∀e∈bc D,W D e=w->e=bZ D w:=by
  intro w hw b6;have rU:((bc D).filter (λe=>W D e=w)).card=1:=(by rw[← gb hS,mt w hw b6]);obtain ⟨e0,q7⟩:=ac.1 rU;have l4:∃e∈bc D,W D e=w:=by
   have hm:e0∈(bc D).filter (λe=>W D e=w):=by rw[q7];simp
   exact ⟨e0,(mF.1 hm).1,(mF.1 hm).2⟩
  have qr:bZ D w∈(bc D).filter (λe=>W D e=w):=(by rw[bZ,dite_eq_left l4,mF];exact cW l4);refine ⟨(mF.1 qr).1,(mF.1 qr).2,λe hea hes=>?_⟩;have h1:e∈({e0}:Finset (A0)):=q7▸mF.2 ⟨hea,hes⟩;have h2:bZ D w∈({e0}:Finset (A0)):=q7▸qr;rw[mS.1 h1,mS.1 h2]
 have a6:∀e∈bc D,e.1<27:=λe he=>by
  have:=(mP.1 he).1;rw[mR,qz] at this;exact this
 have g7:∀g<26,(∀x:F0,14+g≠b x)->g<(bZ D (14+g)).1:=by
  intro g hg b6;obtain ⟨ha,hs,-⟩:=b2 (14+g) Y b6;have e7:=bv hS (show (bZ D (14+g)).1<D.length by have:=a6 _ ha;omega)
   (bZ D (14+g)).2
  rw[hs] at e7;omega
 have f2:∀m:Nat,∀e∈bc D,27-e.1≤m->∀k:Nat,27-e.1≤k->eY D b k e=eY D b (27-e.1) e:=by
  intro m;induction m with
  | zero=>
   intro e he hR;have:=a6 e he;omega
  | succ m ih=>
   intro e he hm k hk;have rL:=a6 e he;obtain ⟨k',rfl⟩:∃k',k=k'+1:=⟨k-1,Y⟩;have sp:27-e.1=(26-e.1)+1:=Y
   conv_rhs=>rw[sp]
   unfold eY;by_cases hY:e.1=26
   ·simp[hY]
   ·simp only[hY,iF];by_cases nR:∃z:F0,14+e.1=b z
    ·simp[nR]
    ·simp only[nR,dF];have b6:∀z:F0,14+e.1≠b z:=λz hz=>nR ⟨z,hz⟩;have gs:=(b2 (14+e.1) Y b6).1;have hX:=g7 e.1 Y b6;have rc:=a6 _ gs;rw[ih _ gs Y k' Y,ih _ gs Y (26-e.1) Y]
 have e5:∀e∈bc D,bj D b e =
    if e.1=26 then Sum.inl e.2
    else if h:∃z:F0,14+e.1=b z then Sum.inr (Classical.choose h)
    else bj D b (bZ D (14+e.1)):=by
  intro e he;have rL:=a6 e he;unfold bj
  conv_lhs=>unfold eY
  by_cases hY:e.1=26
  ·simp[hY]
  ·simp only[hY,iF];by_cases nR:∃z:F0,14+e.1=b z
   ·simp[nR]
   ·simp only[nR,dF];have b6:∀z:F0,14+e.1≠b z:=λz hz=>nR ⟨z,hz⟩;have gs:=(b2 (14+e.1) Y b6).1;have rc:=a6 _ gs;rw[f2 27 _ gs Y 27 Y,f2 27 _ gs Y 28 Y]
 have a8:∀e1 e2,e1∈bc D->gi D b e1 e2->e2∈bc D/\e1.1<e2.1/\bj D b e1=bj D b e2:=by
  intro e1 e2 rf rh;rcases rh with ⟨hY,b6,rfl⟩
  have gs:=(b2 (14+e1.1) Y b6).1;have hX:=g7 e1.1 hY b6;refine ⟨gs,hX,?_⟩;rw[e5 e1 rf];have n1:e1.1≠26:=Y
  have rJ:¬∃z:F0,14+e1.1=b z:=λ⟨z,hz⟩=>b6 z hz;simp[n1,rJ]
 have d2:∀e1 e2,e1∈bc D->dq D b e1 e2->e2∈bc D/\e1.1≤e2.1/\bj D b e1=bj D b e2:=by
  intro e1 e2 rf hp;induction hp with
  | refl=>exact ⟨rf,lR _,rfl⟩
  | @tail a c _ hac ih=>
   obtain ⟨ha,hR,hd⟩:=ih;obtain ⟨hc,e7,k1⟩:=a8 a c ha hac;exact ⟨hc,Y,hd.trans k1⟩
 have ec:∀g<27,∀e∈bc D,dq D b e (g,false)->dq D b e (g,true)->False:=by
  intro g hg e he sv se;have m2:∀a c1 c2,a∈bc D->dq D b a c1->dq D b a c2->dq D b c1 c2\/dq D b c2 c1:=by
   intro a c1 c2 ha h1 h2;induction h1 using rI generalizing c2 with
   | refl=>exact oL h2
   | @head a d had _ ih=>
    rcases cH h2 with rfl|⟨d',qv,ez⟩
    ·exact oR (rH had ‹_›)
    ·have r2:d'=d:=(by rw[qv.2.2,had.2.2]);subst d';exact ih c2 (a8 a d ha had).1 ez
  rcases m2 e (g,false) (g,true) he sv se with h1|h2
  ·rcases cH h1 with hE|⟨d,hd,ez⟩
   ·exact bF (kA Prod.snd hE)
   ·have i4:(g,false)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;obtain ⟨qh,e7,-⟩:=a8 _ d i4 hd;have hR:=(d2 d (g,true) qh ez).2.1;omega
  ·rcases cH h2 with hE|⟨d,hd,ez⟩
   ·exact bF (kA Prod.snd hE).symm
   ·have i4:(g,true)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;obtain ⟨qh,e7,-⟩:=a8 _ d i4 hd;have hR:=(d2 d (g,false) qh ez).2.1;omega
 have er:∀e∈bc D,∀z:F0,14+e.1=b z->bj D b e=Sum.inr z:=by
  intro e he z hz;rw[e5 e he];have e7:=a5 z;have n1:e.1≠26:=Y
  have l4:∃r:F0,14+e.1=b r:=⟨z,hz⟩;simp only[n1,iF,l4,ah];congr 1;exact jb ((cW l4).symm.trans hz)
 have et:∀s:Bool,bj D b (26,s)=Sum.inl s:=(by intro s;have ko:(26,s)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;rw[e5 (26,s) ko];simp);have g0:∀e∈bc D,∀x z:F0,W D e=b x->bj D b e=Sum.inr z->b x<b z:=by
  intro e he x z g2 so;have qc:∀k:Nat,∀e'∈bc D,27-e'.1≤k->eY D b k e'=Sum.inr z->14+e'.1≤b z:=by
   intro k;induction k with
   | zero=>intro e' q5 hR;have:=a6 e' q5;omega
   | succ k ih=>
    intro e' q5 hR hd;have sj:=a6 e' q5;unfold eY at hd;by_cases hY:e'.1=26
    ·simp[hY] at hd
    ·simp only[hY,iF] at hd;by_cases qG:∃r:F0,14+e'.1=b r
     ·simp only[qG,ah,Sum.inr.injEq] at hd;rw[← hd];exact (cW qG).le
     ·simp only[qG,dF] at hd;have b6:∀r:F0,14+e'.1≠b r:=λr hr=>qG ⟨r,hr⟩;have gs:=(b2 (14+e'.1) Y b6).1;have hX:=g7 e'.1 Y b6;have h1:=ih _ gs Y hd;omega
  have h1:=qc 28 e he Y so;have h2:=bv hS (show e.1<D.length by have:=a6 e he;omega) e.2;rw[g2] at h2;omega
 have f1:∀x:F0,x.val≠b x->∀w,aU 14 D x.val w->w<b x->bj D b (bZ D w)=Sum.inr x:=by
  intro x _ w p6 e7;have qr:aU 14 D x.val (b x):=(qb x (b8 x)).2.2.1;have m2:∀a0 u v,aU 14 D a0 u->aU 14 D a0 v->aU 14 D u v\/aU 14 D v u:=by
   intro a0 u v hu hv;induction hu using rI generalizing v with
   | refl=>exact oL hv
   | @head a d had _ ih=>
    rcases cH hv with rfl|⟨d',qv,ez⟩
    ·exact oR (rH had ‹_›)
    ·have r2:d'=d:=cY qv.1 had.1 had.2;subst d';exact ih v ez
  have rl:∀k:Nat,∀u,aU 14 D x.val u->u<b x->b x-u≤k->bj D b (bZ D u)=Sum.inr x:=by
   intro k;induction k with
   | zero=>intro u _ hK hk;omega
   | succ k ih=>
    intro u q4 hK hk;have rV:∀y:F0,u≠b y:=λy hy=>by
     by_cases qs:y=x
     ·subst qs;omega
     ·have c5:=dZ hG hS hC x u (c9 hS q4);exact qs (mS.1 (c5 (by rw[hy,a4 y];simp)))
    have r6:aU 14 D u (b x):=by
     rcases m2 x.val u (b x) q4 qr with h1|h2
     ·exact h1
     ·have:=bV hS (λ_ _ hh=>hh.1) h2;omega
    rcases cH r6 with hE|⟨c,qC,ez⟩
    ·omega
    ·obtain ⟨j,s,hj,rfl,g2⟩:=dN.1 qC.1;have q1:(j,s)∈bc D:=mP.2 ⟨mR.2 hj,mV _⟩;have hF:bZ D u=(j,s):=((b2 u (by have:=a5 x;omega) rV).2.2 (j,s) q1 g2).symm;rw[hF];by_cases qn:14+j=b x
     ·exact er (j,s) q1 x qn
     ·have rS:14+j<b x:=by
       have:=bV hS (λ_ _ hh=>hh.1) ez;omega
      have rC:aU 14 D x.val (14+j):=q4.tail qC;have q9:∀y:F0,14+j≠b y:=λy hy=>by
       by_cases qs:y=x
       ·subst qs;exact qn hy
       ·have c5:=dZ hG hS hC x (14+j) (c9 hS rC);exact qs (mS.1 (c5 (by rw[hy,a4 y];simp)))
      have rP:u<14+j:=(by have:=bv hS hj s;rw[g2] at this;omega);have qy:gi D b (j,s) (bZ D (14+j)):=⟨by have:=a5 x;omega,q9,rfl⟩;rw[(a8 _ _ q1 qy).2.2];exact ih (14+j) rC rS Y
  exact rl (b x-w) w p6 e7 (lR _)
 have c3:∀g<27,∀s:Bool,∀d:Bool⊕F0,bj D b (g,s)=d->∀u,u=W D (g,s)->(∃y:F0,u=b y)\/((∀y:F0,u≠b y)/\bZ D u=(g,s)/\bj D b (bZ D u)=d):=by
  intro g hg s d hd u hu;by_cases l3:∃y:F0,u=b y
  ·exact oL l3
  ·refine oR ?_;have b6:∀y:F0,u≠b y:=λy hy=>l3 ⟨y,hy⟩;have qd:(g,s)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;have hK:u<aO 14 D:=by
    have:=bv hS (by omega:g<D.length) s;rw[← hu] at this;omega
   have gs:=((b2 u hK b6).2.2 (g,s) qd hu.symm).symm;exact ⟨b6,gs,by rw[gs,hd]⟩
 have es:∀(x y:F0) (a3:Bool),aH x y->(∀e∈bc D,W D e=b x->bj D b e≠Sum.inl a3)->y∉O 14 D (W D (26,a3))->∃z:F0,z≠x/\z≠y/\val D (aL x y) (b z)=true:=by
  intro x y a3 f3 h7 qS;by_contra k7;push Not at k7;have qE:∀z:F0,z≠x->val D (aL x y) (b z)=val D (single y) (b z):=by
   intro z ja;by_cases qg:z=y
   ·subst qg;have h1:val D (single z) (b z)=true:=bD.1 (by rw[a4 z];simp)
    have h2:val D (aL x z) (b z)=true:=el hS (single z) (aL x z) (λt ht=>by
      simp only[single,dT] at ht;simp[aL,ht]) (b z) h1
    rw[h1,h2]
   ·have h1:val D (single y) (b z)=false:=by
     by_contra hc;rw[bN] at hc;have:=bD.2 hc;rw[a4 z,mS] at this;exact qg this.symm
    have h2:val D (aL x y) (b z)=false:=bE.2 (k7 z ja qg);rw[h1,h2]
  let Px:S0:=univ.filter (λz=>
   ∃e∈bc D,W D e=b x/\bj D b e=Sum.inr z)
  let Good:Nat->Prop:=λw=>
   (∃z:F0,z≠x/\w=b z)\/
   (w<aO 14 D/\(∀r:F0,w≠b r)/\(bj D b (bZ D w)=Sum.inl a3\/∃r:F0,r≠x/\r∉Px/\bj D b (bZ D w)=Sum.inr r))
  have p8:∀w,w<14+D.length->Good w->val D (aL x y) w=val D (single y) w:=by
   intro w;induction w using sI with
   | ind w ih=>
    intro hw sb;rcases sb with ⟨z,ja,rfl⟩|⟨qt,b6,l0⟩
    ·exact qE z ja
    ·by_cases hM:w<14
     ·rw[ck D _ w hM,ck D _ w hM];have q0:(⟨w,hM⟩:F0)≠x:=by
       intro hE;have rO:w=x.val:=kA Fin.val hE;have qD:x.val≠b x:=λh=>b6 x (rO.trans h);have hd:=f1 x qD x.val rF
        (by have:=bV hS (λ_ _ hh=>hh.1) (qb x (b8 x)).2.2.1;omega)
       rw[← rO] at hd;rcases l0 with h1|⟨r,qm,-,h2⟩
       ·rw[hd] at h1;exact absurd h1 ab
       ·rw[hd] at h2;exact qm (Sum.inr.inj h2).symm
      simp[aL,single,q0]
     ·obtain ⟨g,rfl⟩:∃g,w=14+g:=⟨w-14,Y⟩;have qW:g<26:=Y
      have qZ:(g,false)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;have rg:(g,true)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;have ss:bj D b (g,false)=bj D b (bZ D (14+g)):=(a8 (g,false) (bZ D (14+g)) qZ ⟨qW,b6,rfl⟩).2.2;have r8:bj D b (g,true)=bj D b (bZ D (14+g)):=(a8 (g,true) (bZ D (14+g)) rg ⟨qW,b6,rfl⟩).2.2;have g6:∀s:Bool,Good (W D (g,s)):=by
       intro s;have qu:(g,s)∈bc D:=by cases s<;>assumption
       have nl:bj D b (g,s)=bj D b (bZ D (14+g)):=(by cases s<;>assumption);rcases c3 g Y s (bj D b (bZ D (14+g))) nl (W D (g,s)) rfl with
        ⟨z,hz⟩|⟨hN,-,lo⟩
       ·left;refine ⟨z,?_,hz⟩;intro ja;subst ja;rcases l0 with h1|⟨r,-,rq,h2⟩
        ·exact h7 (g,s) qu hz (nl.trans h1)
        ·exact rq (mF.2 ⟨mV r,(g,s),qu,hz,nl.trans h2⟩)
       ·right;have hK:W D (g,s)<aO 14 D:=by
         have:=bv hS (by omega:g<D.length) s;omega
        exact ⟨hK,hN,lo▸l0⟩
      have hA:=ih (aZ D g) (hS g Y).1 (by have:=(hS g Y).1;omega)
       (by simpa[bP] using g6 false)
      have hB:=ih (aY D g) (hS g Y).2.1 (by have:=(hS g Y).2.1;omega)
       (by simpa[bU] using g6 true)
      rw[cu hS _ g Y,cu hS _ g Y,hA,hB]
  have l7:Good (W D (26,a3)):=by
   rcases c3 26 Y a3 (Sum.inl a3) (et a3) (W D (26,a3)) rfl with
    ⟨z,hz⟩|⟨hN,-,lo⟩
   ·left;refine ⟨z,?_,hz⟩;intro ja;subst ja;have ko:(26,a3)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;exact h7 (26,a3) ko hz (et a3)
   ·right;have hK:W D (26,a3)<aO 14 D:=by
     have:=bv hS (by omega:26<D.length) a3;omega
    exact ⟨hK,hN,oL lo⟩
  have heq_top:=p8 (W D (26,a3))
   (by have:=bv hS (by omega:26<D.length) a3;omega) l7
  have g5:val D (aL x y) (aO 14 D)=true:=(hD _).2 (jH f3);rw[n4,cc hS _ (by omega:26<D.length) a3,hT.2.1,gop_true,bA] at g5;rw[heq_top] at g5;exact qS (bD.2 g5.1)
 have g1:∀oz:Option (F0),∀w,w<14+D.length->∀k,w<k->fo D b oz k w=fo D b oz (w+1) w:=by
  intro oz w;induction w using sI with
  | ind w ih=>
   intro i5 k hk;obtain ⟨k',rfl⟩:∃k',k=k'+1:=⟨k-1,Y⟩;unfold fo;by_cases e4:oz.any (λz=>decide (w=z.val))=true
   ·simp[e4]
   ·rw[bT] at e4;simp only[e4,bQ,iF];by_cases ea:∃y:F0,some y≠oz/\w=b y
    ·simp[ea]
    ·simp only[ea,dF];by_cases eu:14≤w
     ·simp only[eu,iT];have hg:w-14<D.length:=Y
      have c7:aZ D (w-14)<w:=by have:=(hS (w-14) hg).1;omega
      have d1:aY D (w-14)<w:=by have:=(hS (w-14) hg).2.1;omega
      rw[ih (aZ D (w-14)) c7 Y k' Y,ih (aY D (w-14)) d1 Y k' Y,ih (aZ D (w-14)) c7 Y w c7,ih (aY D (w-14)) d1 Y w d1]
     ·simp[eu]
 let f0:Option (F0)->Nat->Option MTree:=λoz w=>fo D b oz (w+1) w
 let bm:F0->Nat->Option MTree:=λz w=>f0 (some z) w
 have b5:∀oz w,w<14+D.length->f0 oz w =
    if oz.any (λz=>decide (w=z.val)) then none
    else if h:∃y:F0,some y≠oz/\w=b y then some (.leaf (Classical.choose h))
    else if 14≤w then fZ (bf D (w-14)) (f0 oz (aZ D (w-14))) (f0 oz (aY D (w-14)))
    else none:=by
  intro oz w i5;dsimp only[f0]
  conv_lhs=>unfold fo
  by_cases e4:oz.any (λz=>decide (w=z.val))=true
  ·simp[e4]
  ·rw[bT] at e4;simp only[e4,bQ,iF];by_cases ea:∃y:F0,some y≠oz/\w=b y
   ·simp[ea]
   ·simp only[ea,dF];by_cases eu:14≤w
    ·simp only[eu,iT];have hg:w-14<D.length:=Y
     have c7:aZ D (w-14)<w:=by have:=(hS (w-14) hg).1;omega
     have d1:aY D (w-14)<w:=by have:=(hS (w-14) hg).2.1;omega
     rw[g1 oz (aZ D (w-14)) Y w c7,g1 oz (aY D (w-14)) Y w d1]
    ·simp[eu]
 have ev:∀t l r x,cx (fZ t l r) x=dm t (cx l x) (cx r x):=(by intro t l r x;cases t<;>cases l<;>cases r<;>simp[fZ,cx,MTree.eval,dm]);have fi:∀t l r v,cB (fZ t l r) v≤cB l v+cB r v:=(by intro t l r v;cases t<;>cases l<;>cases r<;>simp[fZ,cB,MTree.count]);have ct:∀z:F0,∀x:F0->Bool,x z=false->∀w<14+D.length,cx (bm z w) x=true->val D x w=true:=by
  intro z x lb w;induction w using sI with
  | ind w ih=>
   intro i5 e3;dsimp only[bm] at e3;rw[b5 (some z) w i5] at e3;by_cases e4:w=z.val
   ·simp[e4,cx] at e3
   ·simp only[aF,e4,aD,bQ,iF] at e3;by_cases ea:∃y:F0,some y≠some z/\w=b y
    ·simp only[ea,ah,cx,MTree.eval] at e3;have fl:=cW ea;rw[fl.2];exact cf hS (by rw[a4];simp) e3
    ·simp only[ea,dF] at e3;by_cases eu:14≤w
     ·simp only[eu,iT,ev] at e3;have hg:w-14<D.length:=Y
      have c7:aZ D (w-14)<w:=by have:=(hS (w-14) hg).1;omega
      have d1:aY D (w-14)<w:=by have:=(hS (w-14) hg).2.1;omega
      have c6:w=14+(w-14):=Y;rw[c6,cu hS x (w-14) hg];cases htg:bf D (w-14)
      ·rw[htg,gop_false,bO] at e3;rw[gop_false,bO];exact e3.imp (ih _ c7 Y) (ih _ d1 Y)
      ·rw[htg,gop_true,bA] at e3;rw[gop_true,bA];exact ⟨ih _ c7 Y e3.1,ih _ d1 Y e3.2⟩
     ·simp[eu,cx] at e3
 have ej:∀z:F0,∀x:F0->Bool,x z=false->(∀y:F0,b y<b z->val D x (b y)=x y)->∀w≤b z,(w=b z\/((∀r:F0,w≠b r)/\bj D b (bZ D w)=Sum.inr z))->cx (bm z w) x=val D x w:=by
  intro z x lb n5 w;induction w using sI with
  | ind w ih=>
   intro sx pa;have i5:w<14+D.length:=by have:=a5 z;omega
   dsimp only[bm];rw[b5 (some z) w i5];by_cases e4:w=z.val
   ·simp only[aF,e4,aC,iT,cx];rw[ck D x z.val z.isLt,lb]
   ·simp only[aF,e4,aD,bQ,iF];by_cases ea:∃y:F0,some y≠some z/\w=b y
    ·simp only[ea,ah,cx,MTree.eval];have fl:=cW ea;have e7:b (Classical.choose ea)<b z:=by
      have h5:b (Classical.choose ea)≠b z:=λh=>fl.1 (kA some (jb h));omega
     conv_rhs=>rw[fl.2]
     rw[n5 _ e7]
    ·simp only[ea,dF];by_cases eu:14≤w
     ·simp only[eu,iT,ev];have hg:w-14<D.length:=Y
      have c7:aZ D (w-14)<w:=by have:=(hS (w-14) hg).1;omega
      have d1:aY D (w-14)<w:=by have:=(hS (w-14) hg).2.1;omega
      have c6:w=14+(w-14):=Y;have qi:∀s:Bool,bj D b (w-14,s)=Sum.inr z:=by
       intro s;have qd:(w-14,s)∈bc D:=mP.2 ⟨mR.2 hg,mV _⟩;rcases pa with ik|⟨b6,p3⟩
       ·exact er (w-14,s) qd z Y
       ·have iy:w-14<26:=by have:=a5 z;omega
        rw[(a8 (w-14,s) (bZ D w) qd ⟨iy,by simpa[← c6] using b6,by rw[← c6]⟩).2.2];exact p3
      have hP:∀s:Bool,cx (bm z (W D (w-14,s))) x=val D x (W D (w-14,s)):=by
       intro s;have re:W D (w-14,s)<w:=by have:=bv hS hg s;omega
       by_cases l3:∃y:F0,some y≠some z/\W D (w-14,s)=b y
       ·dsimp only[bm];rw[b5 (some z) (W D (w-14,s)) Y];have r3:W D (w-14,s)≠z.val:=by
         obtain ⟨y,ro,hy⟩:=l3;intro ri;have h1:=a4 y;rw[← hy,ri,du D z] at h1;exact ro (kA some (sJ h1).symm)
        simp only[aF,r3,aD,bQ,iF,l3,ah,cx,MTree.eval];have fl:=cW l3
        conv_rhs=>rw[fl.2]
        rw[n5 _ Y]
       ·rcases c3 (w-14) Y s (Sum.inr z) (qi s) (W D (w-14,s)) rfl with
         ⟨y,hy⟩|⟨hN,-,lo⟩
        ·have ro:y=z:=by by_contra h5;exact l3 ⟨y,λh=>h5 (Option.some.inj h),hy⟩
         subst ro;omega
        ·exact ih (W D (w-14,s)) re Y (oR ⟨hN,lo⟩)
      have hA:=(by simpa[bP] using hP false);have hB:=by simpa[bU] using hP true
      conv_rhs=>rw[c6,cu hS x (w-14) hg]
      rw[← hA,← hB]
     ·exfalso;have hM:w<14:=Y
      let u:F0:=⟨w,hM⟩
      have lc:u≠z:=λh=>e4 (kA Fin.val h);rcases pa with ik|⟨b6,p3⟩
      ·have h1:=a4 z;rw[← ik] at h1;change O 14 D u.val={z} at h1;rw[du D u] at h1;exact lc (sJ h1)
      ·have iz:u.val≠b u:=λh=>b6 u h;have hd:=f1 u iz u.val rF
        (by have:=bV hS (λ_ _ hh=>hh.1) (qb u (b8 u)).2.2.1;omega)
       change bj D b (bZ D w)=Sum.inr u at hd;rw[p3] at hd;exact lc (Sum.inr.inj hd).symm
 have c8:∀oz:Option (F0),∀y:F0,∀w<14+D.length,(∀z:F0,oz=some z->w<b z)->∀a∈bc D,W D a=w->cB (f0 oz w) y≤
    ((bc D).filter (λe=>W D e=b y/\dq D b e a)).card:=by
  intro oz y w;induction w using sI with
  | ind w ih=>
   intro i5 ik a ha m1;rw[b5 oz w i5];by_cases e4:oz.any (λz=>decide (w=z.val))=true
   ·simp[e4,cB]
   ·rw[bT] at e4;simp only[e4,bQ,iF];by_cases ea:∃r:F0,some r≠oz/\w=b r
    ·simp only[ea,ah,cB,MTree.count];by_cases rk:Classical.choose ea=y
     ·simp only[rk,iT];have fl:=cW ea;exact cO.2 ⟨a,mF.2 ⟨ha,by rw[m1,fl.2,rk],rF⟩⟩
     ·simp only[rk,iF];exact nZ _
    ·simp only[ea,dF];by_cases eu:14≤w
     ·simp only[eu,iT];have hg:w-14<D.length:=Y
      have c7:aZ D (w-14)<w:=by have:=(hS (w-14) hg).1;omega
      have d1:aY D (w-14)<w:=by have:=(hS (w-14) hg).2.1;omega
      have qO:(w-14,false)∈bc D:=mP.2 ⟨mR.2 hg,mV _⟩;have hX:(w-14,true)∈bc D:=mP.2 ⟨mR.2 hg,mV _⟩;have k2:=fi (bf D (w-14)) (f0 oz (aZ D (w-14))) (f0 oz (aY D (w-14))) y;have h1:=ih (aZ D (w-14)) c7 Y (λz hz=>by have:=ik z hz;omega) (w-14,false) qO (bP (w-14));have h2:=ih (aY D (w-14)) d1 Y (λz hz=>by have:=ik z hz;omega) (w-14,true) hX (bU (w-14));have b6:∀r:F0,w≠b r:=λr hr=>by
       by_cases qP:some r=oz
       ·have:=ik r qP.symm;omega
       ·exact ea ⟨r,qP,hr⟩
      have n2:w<aO 14 D:=(by have e7:=bv hS (show a.1<D.length by have:=a6 a ha;omega) a.2;rw[m1] at e7;have:=a6 a ha;omega);have hF:bZ D w=a:=((b2 w n2 b6).2.2 a ha m1).symm;have iy:w-14<26:=Y
      have c6:14+(w-14)=w:=Y;have sh:gi D b (w-14,false) a:=⟨iy,by simpa[c6] using b6,by rw[c6,hF]⟩;have rh:gi D b (w-14,true) a:=⟨iy,by simpa[c6] using b6,by rw[c6,hF]⟩
      let Sf:=(bc D).filter (λe=>W D e=b y/\dq D b e (w-14,false))
      let St:=(bc D).filter (λe=>W D e=b y/\dq D b e (w-14,true))
      let Sa:=(bc D).filter (λe=>W D e=b y/\dq D b e a)
      have ks:Disjoint Sf St:=by
       rw[dL];intro e hQ i3;exact ec (w-14) Y e (mF.1 hQ).1
        (mF.1 hQ).2.2 (mF.1 i3).2.2
      have c5:Sf∪St⊆Sa:=by
       intro e he;rcases mU.1 he with hQ|i3
       ·exact mF.2 ⟨(mF.1 hQ).1,(mF.1 hQ).2.1,(mF.1 hQ).2.2.tail sh⟩
       ·exact mF.2 ⟨(mF.1 i3).1,(mF.1 i3).2.1,(mF.1 i3).2.2.tail rh⟩
      have hW:=cL c5;rw[cU ks] at hW;dsimp only[Sf,St,Sa] at hW;omega
     ·simp[eu,cB]
 have a7:∀z y:F0,cB (bm z (b z)) y≤
    ((bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr z)).card:=by
  intro z y;have qt:b z<14+D.length:=by have:=a5 z;omega
  dsimp only[bm];rw[b5 (some z) (b z) qt];by_cases e4:b z=z.val
  ·simp[e4,cB]
  ·simp only[aF,e4,aD,bQ,iF];have b6:¬∃r:F0,some r≠some z/\b z=b r:=λ⟨r,qP,hr⟩=>qP (kA some (jb hr.symm));simp only[b6,dF];have rM:14≤b z:=by
    by_contra hc;have qe:b z<14:=Y
    have h1:=a4 z;have h2:=du D (⟨b z,qe⟩:F0);change O 14 D (b z)={⟨b z,qe⟩} at h2;rw[h2] at h1;exact e4 (kA Fin.val (sJ h1))
   simp only[rM,iT]
   let g:=b z-14
   have hg:g<D.length:=by have:=a5 z;omega
   have qO:(g,false)∈bc D:=mP.2 ⟨mR.2 hg,mV _⟩;have hX:(g,true)∈bc D:=mP.2 ⟨mR.2 hg,mV _⟩;have k2:=fi (bf D g) (f0 (some z) (aZ D g)) (f0 (some z) (aY D g)) y;have h1:=c8 (some z) y (aZ D g) (by have:=(hS g hg).1;omega)
    (λz' qk=>by cases Option.some.inj qk;have:=(hS g hg).1;omega) (g,false) qO (bP g)
   have h2:=c8 (some z) y (aY D g) (by have:=(hS g hg).2.1;omega)
    (λz' qk=>by cases Option.some.inj qk;have:=(hS g hg).2.1;omega) (g,true) hX (bU g)
   let Sf:=(bc D).filter (λe=>W D e=b y/\dq D b e (g,false))
   let St:=(bc D).filter (λe=>W D e=b y/\dq D b e (g,true))
   let Sz:=(bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr z)
   have ks:Disjoint Sf St:=by
    rw[dL];intro e hQ i3;exact ec g Y e (mF.1 hQ).1
     (mF.1 hQ).2.2 (mF.1 i3).2.2
   have c5:Sf∪St⊆Sz:=by
    intro e he;rcases mU.1 he with hQ|i3
    ·have hf:=mF.1 hQ;have hd:=(d2 e (g,false) hf.1 hf.2.2).2.2;rw[er (g,false) qO z Y] at hd;exact mF.2 ⟨hf.1,hf.2.1,hd⟩
    ·have ht:=mF.1 i3;have hd:=(d2 e (g,true) ht.1 ht.2.2).2.2;rw[er (g,true) hX z Y] at hd;exact mF.2 ⟨ht.1,ht.2.1,hd⟩
   have hW:=cL c5;rw[cU ks] at hW;dsimp only[Sf,St,Sz,g] at k2 h1 h2 hW;omega
 let b1:F0->Nat:=λx=>
  ((bc D).filter (λe=>W D e=b x/\∃z:F0,bj D b e=Sum.inr z)).card
 have h9:∀x:F0,b1 x≤2:=λx=>by
  have c5:(bc D).filter (λe=>W D e=b x/\∃z:F0,bj D b e=Sum.inr z)⊆
    (bc D).filter (λe=>W D e=b x):=λe he=>by
   simp only[mF] at he ⊢;exact ⟨he.1,he.2.1⟩
  have:=cL c5;rw[← gb hS,nB x] at this;exact this
 let cb:Bool->F0->Nat:=λs x=>
  ((bc D).filter (λe=>W D e=b x/\bj D b e=Sum.inl s)).card
 have g9:∀x:F0,cb false x+cb true x+b1 x=2:=by
  intro x
  let Sx:=(bc D).filter (λe=>W D e=b x)
  let Sa:=(bc D).filter (λe=>W D e=b x/\bj D b e=Sum.inl false)
  let Sb:=(bc D).filter (λe=>W D e=b x/\bj D b e=Sum.inl true)
  let Si:=(bc D).filter (λe=>W D e=b x/\∃z:F0,bj D b e=Sum.inr z)
  have rE:Sx.card=2:=(by rw[← gb hS,nB x]);have hO:Sx=Sa∪Sb∪Si:=by
   ext e;simp only[Sx,Sa,Sb,Si,mU,mF];constructor
   ·intro ⟨ha,hs⟩;cases hd:bj D b e with
    | inl s=>
     cases s
     ·exact oL (oL ⟨ha,hs,rfl⟩)
     ·exact oL (oR ⟨ha,hs,rfl⟩)
    | inr z=>exact oR ⟨ha,hs,z,rfl⟩
   ·rintro ((⟨ha,hs,-⟩|⟨ha,hs,-⟩)|⟨ha,hs,-⟩)<;>exact ⟨ha,hs⟩
  have qT:Disjoint Sa Sb:=(by rw[dL];intro e h1 h2;have a1:=(mF.1 h1).2.2;have a2:=(mF.1 h2).2.2;rw[a1] at a2;exact absurd a2 ab);have k1:Disjoint (Sa∪Sb) Si:=by
   rw[dL];intro e h1 h2;obtain ⟨z,hz⟩:=(mF.1 h2).2.2;rcases mU.1 h1 with rd|rd
   ·rw[(mF.1 rd).2.2] at hz;exact absurd hz ab
   ·rw[(mF.1 rd).2.2] at hz;exact absurd hz ab
  rw[hO,cU k1,cU qT] at rE;exact rE
 have g8:∀x y:F0,(∃z:F0,z≠x/\z≠y/\val D (aL x y) (b z)=true)->∃z0:F0,cx (bm z0 (b z0)) (aL x y)=true/\1≤cB (bm z0 (b z0)) x/\1≤cB (bm z0 (b z0)) y:=by
  intro x y ⟨z,ja,qg,lw⟩
  let S:=univ.filter (λr:F0=>r≠x/\r≠y/\val D (aL x y) (b r)=true)
  obtain ⟨z0,rN,qB⟩:=exists_min_image S b ⟨z,mF.2 ⟨mV _,ja,qg,lw⟩⟩;have k3:=mF.1 rN;have qj:∀r:F0,b r<b z0->val D (aL x y) (b r)=aL x y r:=by
   intro r e7;by_cases qm:r=x
   ·subst qm;simp only[aL,aC,Bool.true_or];exact cf hS (u:=r) (by rw[a4 r];simp) (by simp[aL])
   ·by_cases q8:r=y
    ·subst q8;simp only[aL,aC,Bool.or_true];exact cf hS (u:=r) (by rw[a4 r];simp) (by simp[aL])
    ·have qN:val D (aL x y) (b r)=false:=by
      by_contra h1;rw[bN] at h1;have:=qB r (mF.2 ⟨mV _,qm,q8,h1⟩);omega
     rw[qN];simp[aL,qm,q8]
  have e3:=ej z0 (aL x y) (by simp[aL,k3.2.1,k3.2.2.1]) qj (b z0) (lR _) (oL rfl);rw[k3.2.2.2] at e3;have qV:∀u v:F0,z0≠v->cx (bm z0 (b z0)) (aL u v)=true->1≤cB (bm z0 (b z0)) u:=by
   intro u v pr ix;cases htr:bm z0 (b z0) with
   | none=>rw[htr] at ix;simp[cx] at ix
   | some t=>
    rw[htr] at ix;dsimp[cx] at ix;dsimp[cB];by_contra hc;have p1:t.count u=0:=Y
    rw[dg t p1] at ix;have sc:=ct z0 (single v) (by simp[single,pr]) (b z0) (by have:=a5 z0;omega) (by rw[htr];exact ix);have:=bD.2 sc;rw[a4 z0,mS] at this;exact pr this.symm
  have qM:cx (bm z0 (b z0)) (aL y x)=true:=by
   have:aL y x=aL x y:=by funext r;simp[aL,bR]
   rwa[this]
  exact ⟨z0,e3,qV x y k3.2.2.1 e3,qV y x k3.2.1 qM⟩
 have fc:∀s:Bool,∀x:F0,cb s x≤1:=by
  intro s x;by_contra hX;have sw:cb s x=2:=by have:=g9 x;cases s<;>omega
  have qx:∀e∈bc D,W D e=b x->bj D b e≠Sum.inl (!s):=(by intro e he g2 hd;have id:1≤cb (!s) x:=cO.2 ⟨e,mF.2 ⟨he,g2,hd⟩⟩;have:=g9 x;cases s<;>simp at id<;>omega);have qI:∀e∈bc D,W D e=b x->∀z:F0,bj D b e≠Sum.inr z:=(by intro e he g2 z hd;have id:1≤b1 x:=cO.2 ⟨e,mF.2 ⟨he,g2,z,hd⟩⟩;have:=g9 x;cases s<;>omega);have ql:aX x⊆O 14 D (W D (26,!s)):=(by intro y hy;by_contra rb;obtain ⟨z0,-,p9,-⟩:=g8 x y (es x y (!s) (ce.1 hy) qx rb);have hR:=a7 z0 x;obtain ⟨e,he⟩:=cO.1 (by omega:0<((bc D).filter (λe=>W D e=b x/\bj D b e=Sum.inr z0)).card);rw[mF] at he;exact qI e he.1 he.2.1 z0 he.2.2);have h3:3≤(aX x∩O 14 D (W D (26,!s))).card:=(by rw[qL.2 ql];exact (dH x).ge);have:=qX (!s) x;omega
 let Vin:S0:=univ.filter (λx=>1≤b1 x)
 by_cases la:Vin.Nonempty
 ·let E_H:Finset (F0×F0):=(univ:Finset (F0×F0)).filter
   (λp=>p.1.val<p.2.val/\aH p.1 p.2/\∃z:F0,z≠p.1/\z≠p.2/\val D (aL p.1 p.2) (b z)=true)
  let E_w:F0->Finset (F0×F0):=λw=>
   (univ:Finset (F0×F0)).filter
    (λp=>p.1.val<p.2.val/\cx (bm w (b w)) (aL p.1 p.2)=true)
  have p0:E_H⊆univ.biUnion E_w:=(by intro ⟨u,v⟩ g3;simp only[E_H,mF,mV,ae] at g3;obtain ⟨z0,e3,-,-⟩:=g8 u v g3.2.2;exact mB.2 ⟨z0,mV _,mF.2 ⟨mV _,g3.1,e3⟩⟩);have m8:∀w:F0,4*(E_w w).card≤3*ey (bm w (b w)):=by
   intro w;cases htr:bm w (b w) with
   | none=>
    have rx:E_w w=∅:=eO (λp hp=>by
     simp only[E_w,htr,cx,mF,mV,ae] at hp
     exact bF hp.2)
    rw[rx];simp[ey]
   | some t=>
    have hq:E_w w=(univ:Finset (F0×F0)).filter
      (λp=>p.1.val<p.2.val/\t.eval (aL p.1 p.2)=true):=by
     ext p;simp[E_w,htr,cx]
    have p6:t.count w=0:=by
     have h1:=a7 w w;rw[htr] at h1;dsimp only[cB] at h1
     have h0:(bc D).filter (λe=>W D e=b w/\bj D b e=Sum.inr w)=∅:=eO (λe he=>by
       rw[mF] at he;have:=g0 e he.1 w w he.2.1 he.2.2;omega)
     rw[h0,ad] at h1;omega
    rw[hq];dsimp only[ey];refine nz t ?_ ?_ ?_
    ·intro y;have h1:=a7 w y;rw[htr] at h1;dsimp only[cB] at h1;have h2:((bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr w)).card≤2:=by
      have c5:(bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr w)⊆
        (bc D).filter (λe=>W D e=b y):=λe he=>by
       simp only[mF] at he ⊢;exact ⟨he.1,he.2.1⟩
      exact (cL c5).trans (by rw[← gb hS,nB y])
     omega
    ·intro v;by_cases hZ:v=w
     ·subst hZ;rw[gC t p6 (y:=λ_=>false) (λu hu=>by simp[single,hu]),jx]
     ·by_contra hc;rw[bN] at hc;have hv:=ct w (single v) (by simp[single,nS hZ]) (b w)
       (by have:=a5 w;omega) (by rw[htr];exact hc)
      have:=bD.2 hv;rw[a4 w,mS] at this;exact hZ this
    ·intro u v g3;have qH:u≠w:=by
      intro he;subst he;rw[dg t p6] at g3;by_cases hZ:v=u
      ·subst hZ;rw[gC t p6 (y:=λ_=>false) (λr hr=>by simp[single,hr]),jx] at g3;exact bF g3
      ·have hv:=ct u (single v) (by simp[single,nS hZ]) (b u)
        (by have:=a5 u;omega) (by rw[htr];exact g3)
       have:=bD.2 hv;rw[a4 u,mS] at this;exact hZ this
     have hZ:v≠w:=by
      intro he;subst he;rw[dQ t p6] at g3;have hv:=ct v (single u) (by simp[single,nS qH]) (b v)
       (by have:=a5 v;omega) (by rw[htr];exact g3)
      have:=bD.2 hv;rw[a4 v,mS] at this;exact qH this
     have ll:=ct w (aL u v) (by simp[aL,nS qH,nS hZ]) (b w)
      (by have:=a5 w;omega) (by rw[htr];exact g3)
     by_contra gs;have hf:=jA hS hD qb gs qH.symm hZ.symm (b8 w);rw[hf] at ll;exact bF ll
  have j0:∑ w:F0,ey (bm w (b w))≤∑ y:F0,b1 y:=by
   have h1:∀w:F0,ey (bm w (b w))=∑ y:F0,cB (bm w (b w)) y:=λw=>by
    cases bm w (b w) with
    | none=>simp[ey,cB]
    | some t=>exact gO t
   calc ∑ w:F0,ey (bm w (b w))
     = ∑ w:F0,∑ y:F0,cB (bm w (b w)) y:=sC rfl (λw _=>h1 w)
    _=∑ y:F0,∑ w:F0,cB (bm w (b w)) y:=sum_comm
    _≤∑ y:F0,∑ w:F0,((bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr w)).card:=sM (λy _=>sM (λw _=>a7 w y))
    _=∑ y:F0,b1 y:=sC rfl (λy _=>by
      dsimp only[b1]
      rw[← card_biUnion (λw1 _ w2 _ h5=>by
       show Disjoint _ _;rw[dL];intro e h1 h2;have a1:=(mF.1 h1).2.2;have a2:=(mF.1 h2).2.2
       rw[a1] at a2;exact h5 (Sum.inr.inj a2))]
      congr 1;ext e;simp only[mB,mV,ae,mF]
      exact ⟨λ⟨w,ha,hs,hd⟩=>⟨ha,hs,w,hd⟩,λ⟨ha,hs,w,hd⟩=>⟨w,ha,hs,hd⟩⟩)
  have rW:4*E_H.card≤3*∑ y:F0,b1 y:=by
   calc 4*E_H.card
     ≤4*(univ.biUnion E_w).card:=an 4 (cL p0)
    _≤4*∑ w:F0,(E_w w).card:=an 4 card_biUnion_le
    _=∑ w:F0,4*(E_w w).card:=by rw[mul_sum]
    _≤∑ w:F0,3*ey (bm w (b w)):=sM (λw _=>m8 w)
    _=3*∑ w:F0,ey (bm w (b w)):=by rw[← mul_sum]
    _≤3*∑ y:F0,b1 y:=an 3 j0
  let NH:F0->S0:=λx=>
   univ.filter (λy=>aH x y/\∃z:F0,z≠x/\z≠y/\val D (aL x y) (b z)=true)
  have hi:∀x:F0,(b1 x=1->2≤(NH x).card)/\(b1 x=2->3≤(NH x).card):=by
   intro x;constructor
   ·intro qC;obtain ⟨s,h0⟩:∃s:Bool,cb s x=0:=by
     by_cases h0:cb false x=0;exact ⟨false,h0⟩
     have:=g9 x;have:=fc false x;have:=fc true x;exact ⟨true,Y⟩
    have st:∀e∈bc D,W D e=b x->bj D b e≠Sum.inl s:=λe he hs hd=>by
     have id:0<cb s x:=cO.2 ⟨e,mF.2 ⟨he,hs,hd⟩⟩;omega
    have c5:aX x \ O 14 D (W D (26,s))⊆NH x:=λy hy=>by
     rw[mD,ce] at hy;exact mF.2 ⟨mV _,hy.1,es x y s hy.1 st hy.2⟩
    have h1:=cL c5;have h2:=card_sdiff_add_card_inter (aX x) (O 14 D (W D (26,s)));have h3:(aX x).card=3:=dH x;have h4:=qX s x;omega
   ·intro r1;have sB:cb false x=0:=by have:=g9 x;omega
    have sG:cb true x=0:=by have:=g9 x;omega
    have rA:∀e∈bc D,W D e=b x->bj D b e≠Sum.inl false:=λe he hs hd=>by
     have id:0<cb false x:=cO.2 ⟨e,mF.2 ⟨he,hs,hd⟩⟩;omega
    have rQ:∀e∈bc D,W D e=b x->bj D b e≠Sum.inl true:=λe he hs hd=>by
     have id:0<cb true x:=cO.2 ⟨e,mF.2 ⟨he,hs,hd⟩⟩;omega
    have c5:aX x⊆NH x:=λy hy=>by
     have f3:=ce.1 hy;by_cases rD:y∈O 14 D (W D (26,false))
     ·have ra:y∉O 14 D (W D (26,true)):=λra=>by
       have lw:val D (single y) (aO 14 D)=true:=(by rw[n4,cu hS _ 26 Y,hT.2.1,gop_true,bA];exact ⟨bD.1 (by simpa[bP] using rD),bD.1 (by simpa[bU] using ra)⟩);exact jD y ((hD _).1 lw)
      exact mF.2 ⟨mV _,f3,es x y true f3 rQ ra⟩
     ·exact mF.2 ⟨mV _,f3,es x y false f3 rA rD⟩
    have h3:(aX x).card=3:=dH x;have:=cL c5;omega
  have sA:∑ x:F0,(NH x).card=2*E_H.card:=by
   let E_all:=(univ:Finset (F0×F0)).filter
    (λp=>aH p.1 p.2/\∃z:F0,z≠p.1/\z≠p.2/\val D (aL p.1 p.2) (b z)=true)
   let E_gt:=(univ:Finset (F0×F0)).filter
    (λp=>p.2.val<p.1.val/\aH p.1 p.2/\∃z:F0,z≠p.1/\z≠p.2/\val D (aL p.1 p.2) (b z)=true)
   have hO:E_all=E_H∪E_gt:=by
    ext ⟨u,v⟩;simp only[E_all,E_H,E_gt,mU,mF,mV,ae];constructor
    ·intro ⟨hH,hz⟩;have h5:u≠v:=λh=>bW u (h▸hH);rcases nT u.val v.val with e7|hE|hX
     ·exact oL ⟨e7,hH,hz⟩
     ·exact (h5 (Fin.ext hE)).elim
     ·exact oR ⟨hX,hH,hz⟩
    ·rintro (⟨-,h1,h2⟩|⟨-,h1,h2⟩)<;>exact ⟨h1,h2⟩
   have ks:Disjoint E_H E_gt:=(by rw[dL];intro ⟨u,v⟩ h1 h2;simp only[E_H,E_gt,mF,mV,ae] at h1 h2;omega);have qK:E_gt.card=E_H.card:=by
    refine card_nbij (λp=>(p.2,p.1)) ?_ ?_ ?_
    ·intro ⟨u,v⟩ h;simp only[mem_coe,E_gt,E_H,mF,mV,ae] at h ⊢;obtain ⟨e7,hH,z,rm,pr,lw⟩:=h
     exact ⟨e7,bh hH,z,pr,rm,by
      have:aL v u=aL u v:=by funext w;simp[aL,bR]
      rwa[this]⟩
    ·intro ⟨u1,v1⟩ _ ⟨u2,v2⟩ _ h;simp only[ay] at h;exact pE h.2 h.1
    ·intro ⟨u,v⟩ h;refine ⟨(v,u),?_,rfl⟩;simp only[mem_coe,E_gt,E_H,mF,mV,ae] at h ⊢;obtain ⟨e7,hH,z,rm,pr,lw⟩:=h
     exact ⟨e7,bh hH,z,pr,rm,by
      have:aL v u=aL u v:=by funext w;simp[aL,bR]
      rwa[this]⟩
   have qp:∑ x:F0,(NH x).card=E_all.card:=by
    rw[← au];refine card_nbij (λs=>(s.1,s.2)) ?_ ?_ ?_
    ·intro ⟨u,v⟩ h;simp only[mem_coe,mG,mV,ae,NH,mF] at h;simp[E_all,h]
    ·intro ⟨u1,v1⟩ _ ⟨u2,v2⟩ _ h;simp only[ay] at h;cases h.1;cases h.2;rfl
    ·intro ⟨u,v⟩ h;simp only[mem_coe,E_all,mF,mV,ae] at h;exact ⟨⟨u,v⟩,by simp[NH,h],rfl⟩
   rw[qp,hO,cU ks,qK];omega
  let V1:=univ.filter (λx:F0=>b1 x=1)
  let V2:=univ.filter (λx:F0=>b1 x=2)
  have rn:V1.card=0:=by
   have rr:∑ x:F0,b1 x=V1.card+2*V2.card:=by
    have hO:(univ:S0) =
      univ.filter (λx=>b1 x=0)∪(V1∪V2):=by
     ext x;simp only[V1,V2,mV,mU,mF,ae,true_iff];have:=h9 x;omega
    have qT:Disjoint (univ.filter (λx=>b1 x=0)) (V1∪V2):=(by rw[dL];intro x h1 h2;simp only[V1,V2,mU,mF,mV,ae] at h1 h2;omega);have k1:Disjoint V1 V2:=(by rw[dL];intro x h1 h2;simp only[V1,V2,mF,mV,ae] at h1 h2;omega)
    conv_lhs=>rw[hO]
    rw[ap qT,ap k1];have s0:∑ x∈univ.filter (λx=>b1 x=0),b1 x=0:=sum_eq_zero (λx hx=>(mF.1 hx).2);have s1:∑ x∈V1,b1 x=V1.card:=by
     calc ∑ x∈V1,b1 x=∑ _x∈V1,1:=sC rfl (λx hx=>(mF.1 hx).2)
      _=V1.card:=ab
    have s2:∑ x∈V2,b1 x=2*V2.card:=by
     calc ∑ x∈V2,b1 x=∑ _x∈V2,2:=sC rfl (λx hx=>(mF.1 hx).2)
      _=2*V2.card:=by simp[nM]
    omega
   have rs:2*V1.card+3*V2.card≤∑ x:F0,(NH x).card:=by
    have k1:Disjoint V1 V2:=(by rw[dL];intro x h1 h2;simp only[V1,V2,mF,mV,ae] at h1 h2;omega)
    calc 2*V1.card+3*V2.card
      = (∑ _x∈V1,2)+(∑ _x∈V2,3):=by simp[nM]
     _≤(∑ x∈V1,(NH x).card)+(∑ x∈V2,(NH x).card):=Nat.add_le_add
        (sM (λx hx=>(hi x).1 (mF.1 hx).2))
        (sM (λx hx=>(hi x).2 (mF.1 hx).2))
     _=∑ x∈V1∪V2,(NH x).card:=(ap k1).symm
     _≤∑ x:F0,(NH x).card:=sum_le_univ_sum_of_nonneg (λ_=>nZ _)
   omega
  have k0:∀x∈Vin,b1 x=2:=(by intro x hx;have h1:=(mF.1 hx).2;have h2:=h9 x;by_contra h5;have sr:x∈V1:=mF.2 ⟨mV _,Y⟩;have:=cO.2 ⟨x,sr⟩;omega);have ca:∀x∈Vin,∀y:F0,aH x y->y∈Vin:=by
   intro x hx y f3;have h3:=(hi x).2 (k0 x hx);have qQ:NH x=aX x:=eS (λu hu=>ce.2 (mF.1 hu).2.1)
     (by have r7:(aX x).card=3:=dH x;omega)
   have rv:y∈NH x:=qQ▸ce.2 f3;obtain ⟨z0,-,-,p9⟩:=g8 x y (mF.1 rv).2.2;have hR:=a7 z0 y;have c5:(bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr z0)⊆
     (bc D).filter (λe=>W D e=b y/\∃r:F0,bj D b e=Sum.inr r):=λe he=>by
    simp only[mF] at he ⊢;exact ⟨he.1,he.2.1,z0,he.2.2⟩
   have:=cL c5;exact mF.2 ⟨mV y,by dsimp[b1];omega⟩
  obtain ⟨u0,p1⟩:=la;have g4:∀u v:F0,v∈em u->aH u v:=λu v hv=>by
   simp only[em,List.mem_filter,List.mem_finRange,ae] at hv;exact (aK u v).1 hv
  have p2:∀v:F0,v∈Vin:=λv=>by
   rcases mo u0 v with rfl|h1|h2|h3
   ·exact p1
   ·exact ca u0 p1 v ((aK u0 v).1 h1)
   ·obtain ⟨a,ha,sm⟩:=List.any_eq_true.1 h2;exact ca a (ca u0 p1 a (g4 u0 a ha)) v ((aK a v).1 sm)
   ·obtain ⟨a,ha,ez⟩:=List.any_eq_true.1 h3;obtain ⟨c,hc,q6⟩:=List.any_eq_true.1 ez;exact ca c (ca a (ca u0 p1 a (g4 u0 a ha)) c (g4 a c hc)) v
     ((aK c v).1 q6)
  obtain ⟨n7,-,qY⟩:=exists_max_image (univ:S0) b univ_nonempty;have rY:1≤b1 n7:=(mF.1 (p2 n7)).2;obtain ⟨e,he⟩:=cO.1 (by omega:0<b1 n7);rw[mF] at he;obtain ⟨z',qk⟩:=he.2.2;have e7:=g0 e he.1 n7 z' he.2.1 qk;have hR:=qY z' (mV z');omega
 ·have q3:∀x:F0,b1 x=0:=λx=>by
   by_contra h5;exact la ⟨x,mF.2 ⟨mV x,Y⟩⟩
  have qA:∀e∈bc D,∀x z:F0,W D e=b x->bj D b e≠Sum.inr z:=(by intro e he x z hs hd;have id:0<b1 x:=cO.2 ⟨e,mF.2 ⟨he,hs,z,hd⟩⟩;have:=q3 x;omega);have m3:∀z:F0,∀x:F0->Bool,val D x (b z)=x z:=by
   intro z x;by_cases lb:x z=true
   ·rw[lb];exact cf hS (u:=z) (by rw[a4 z];simp) lb
   ·rw[bT] at lb;rw[lb];have qf:∀k:Nat,∀r:F0,b r<k->x r=false->val D x (b r)=false:=by
     intro k;induction k with
     | zero=>intro r hr;omega
     | succ k ih=>
      intro r hr si;have n5:∀y:F0,b y<b r->val D x (b y)=x y:=by
       intro y hy;by_cases f3:x y=true
       ·rw[f3];exact cf hS (u:=y) (by rw[a4 y];simp) f3
       ·rw[bT] at f3;rw[f3];exact ih y Y f3
      have e3:=ej r x si n5 (b r) (lR _) (oL rfl);rw[← e3];cases htr:bm r (b r) with
      | none=>rfl
      | some t=>
       exfalso;have qo:1≤t.leaves:=by
        have hl:∀u:MTree,1≤u.leaves:=λu=>by induction u<;>simp[MTree.leaves]<;>omega
        exact hl t
       rw[gO t] at qo;have l4:∃y:F0,1≤t.count y:=(by by_contra k7;push Not at k7;have h0:∑ y:F0,t.count y=0:=sum_eq_zero (λy _=>by have:=k7 y;omega);omega);obtain ⟨y,hy⟩:=l4;have hR:=a7 r y;rw[htr] at hR;dsimp only[cB] at hR;obtain ⟨e,he⟩:=cO.1 (by omega:0<((bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inr r)).card);rw[mF] at he;exact qA e he.1 y r he.2.1 he.2.2
    exact qf (b z+1) z Y lb
  let ls:Nat->Option MTree:=λw=>f0 none w
  have i7:∀a3:Bool,∀x:F0->Bool,∀w<aO 14 D,((∃y:F0,w=b y)\/((∀r:F0,w≠b r)/\bj D b (bZ D w)=Sum.inl a3))->cx (ls w) x=val D x w:=by
   intro a3 x w;induction w using sI with
   | ind w ih=>
    intro qt pa;dsimp only[ls];rw[b5 none w Y];simp only[Option.any_none,bQ,iF];by_cases ea:∃y:F0,some y≠none/\w=b y
    ·simp only[ea,ah,cx,MTree.eval]
     conv_rhs=>rw[(cW ea).2]
     rw[m3]
    ·simp only[ea,dF];have b6:∀r:F0,w≠b r:=λr hr=>ea ⟨r,ab,hr⟩;have p3:bj D b (bZ D w)=Sum.inl a3:=by
      rcases pa with ⟨y,hy⟩|⟨-,h2⟩
      ·exact (b6 y hy).elim
      ·exact h2
     by_cases eu:14≤w
     ·simp only[eu,iT,ev];have hg:w-14<D.length:=Y
      have c7:aZ D (w-14)<w:=by have:=(hS (w-14) hg).1;omega
      have d1:aY D (w-14)<w:=by have:=(hS (w-14) hg).2.1;omega
      have c6:w=14+(w-14):=Y;have hJ:∀s:Bool,(∃y:F0,W D (w-14,s)=b y)\/((∀r:F0,W D (w-14,s)≠b r)/\bj D b (bZ D (W D (w-14,s)))=Sum.inl a3):=by
       intro s;have qd:(w-14,s)∈bc D:=mP.2 ⟨mR.2 hg,mV _⟩;have rR:bj D b (w-14,s)=Sum.inl a3:=(by rw[(a8 (w-14,s) (bZ D w) qd ⟨Y,by simpa[← c6] using b6,by rw[← c6]⟩).2.2];exact p3);rcases c3 (w-14) Y s (Sum.inl a3) rR (W D (w-14,s)) rfl with h1|⟨h1,-,h2⟩
       ·exact oL h1
       ·exact oR ⟨h1,h2⟩
      have hA:=ih (aZ D (w-14)) c7 Y (by simpa[bP] using hJ false);have hB:=ih (aY D (w-14)) d1 Y (by simpa[bU] using hJ true)
      conv_rhs=>rw[c6,cu hS x (w-14) hg]
      rw[← hA,← hB]
     ·exfalso;have hM:w<14:=Y
      let u:F0:=⟨w,hM⟩
      have iz:u.val≠b u:=λh=>b6 u h;have hd:=f1 u iz u.val rF
       (by have:=bV hS (λ_ _ hh=>hh.1) (qb u (b8 u)).2.2.1;omega)
      change bj D b (bZ D w)=Sum.inr u at hd;rw[p3] at hd;exact absurd hd ab
  have hn:∀y:F0,∀w<14+D.length,∀a∈bc D,W D a=w->cB (ls w) y≤((bc D).filter (λe=>W D e=b y/\dq D b e a)).card:=λy w i5 a ha g2=>c8 none y w i5 (λ_ h=>by cases h) a ha g2;obtain ⟨a0,b0,c0,d0,sH,sF,sK,sN,qC,r1,qT,k1,qJ,rz,rt,rK⟩:=nW s1 s2;have rj:∀s:Bool,∀v∈({a0,b0,c0,d0}:S0),v∉O 14 D (W D (26,s)):=by
   intro s v hv n3;have hU:v∈O 14 D (aZ D 26)∪O 14 D (aY D 26):=by
    cases s
    ·rw[bP] at n3;exact aq _ n3
    ·rw[bU] at n3;exact ar _ n3
   have rB:=qF hU;simp only[mI,mS] at hv rB;rcases hv with rfl|rfl|rfl|rfl<;>rcases rB with rfl|rfl<;>contradiction
  have h6:∀a3:Bool,val D (aL a0 d0) (W D (26,a3))=true:=by
   intro a3;have ko:(26,a3)∈bc D:=mP.2 ⟨mR.2 Y,mV _⟩;have qq:W D (26,a3)<aO 14 D:=(by have:=bv hS (by omega:26<D.length) a3;omega);have qw:(∃y:F0,W D (26,a3)=b y)\/((∀r:F0,W D (26,a3)≠b r)/\bj D b (bZ D (W D (26,a3)))=Sum.inl a3):=by
    rcases c3 26 Y a3 (Sum.inl a3) (et a3) (W D (26,a3)) rfl with h1|⟨h1,-,h2⟩
    ·exact oL h1
    ·exact oR ⟨h1,h2⟩
   have n8:∀x:F0->Bool,cx (ls (W D (26,a3))) x=val D x (W D (26,a3)):=λx=>i7 a3 x (W D (26,a3)) qq qw;have eb:∀u v:F0,aH u v->val D (aL u v) (W D (26,a3))=true:=(by intro u v g3;have ho:=(hD _).2 (jH g3);rw[n4,cc hS _ (by omega:26<D.length) a3,hT.2.1,gop_true,bA] at ho;exact ho.1);cases htr:ls (W D (26,a3)) with
   | none=>
    have h1:=n8 (aL a0 b0);rw[htr,eb a0 b0 qJ] at h1;exact absurd h1 bF
   | some t=>
    have hq:∀x,t.eval x=val D x (W D (26,a3)):=λx=>by
     have:=n8 x;rw[htr] at this;exact this
    have h8:∀y:F0,t.count y≤1:=λy=>by
     have h1:=hn y (W D (26,a3)) Y (26,a3) ko rfl;rw[htr] at h1;dsimp only[cB] at h1;have c5:(bc D).filter (λe=>W D e=b y/\dq D b e (26,a3))⊆
       (bc D).filter (λe=>W D e=b y/\bj D b e=Sum.inl a3):=by
      intro e he;have hf:=mF.1 he;have hd:=(d2 e (26,a3) hf.1 hf.2.2).2.2;rw[et a3] at hd;exact mF.2 ⟨hf.1,hf.2.1,hd⟩
     have h2:=cL c5;have h3:=fc a3 y;dsimp only[cb] at h3;omega
    have p7:∀v∈({a0,b0,c0,d0}:S0),t.eval (single v)=false:=(by intro v hv;rw[hq (single v)];by_contra hc;rw[bN] at hc;exact rj a3 v hv (bD.2 hc));have i0:∀u v:F0,u∈({a0,b0,c0,d0}:S0)->v∈({a0,b0,c0,d0}:S0)->aH u v->t.count u=1/\t.count v=1:=by
     intro u v hu hv g3;have h1:t.eval (aL u v)=true:=by rw[hq];exact eb u v g3
     have r9:t.count u=1:=by
      have:=h8 u;by_contra hc;have hz:t.count u=0:=Y
      rw[dg t hz,p7 v hv] at h1;exact bF h1
     have q6:t.count v=1:=by
      have:=h8 v;by_contra hc;have hz:t.count v=0:=Y
      rw[dQ t hz,p7 u hu] at h1;exact bF h1
     exact ⟨r9,q6⟩
    have sd:t.count a0=1:=(i0 a0 b0 ab ab qJ).1;have qn:t.count b0=1:=(i0 a0 b0 ab ab qJ).2;have sf:t.count c0=1:=(i0 b0 c0 ab ab rz).2;have sq:t.count d0=1:=(i0 c0 d0 ab ab rt).2;obtain ⟨L,R,r4,sa,sl,sg,r0⟩:=i9 t a0 b0 sd qn
     (p7 a0 ab) (p7 b0 ab) (by rw[hq];exact eb a0 b0 qJ)
    have rZ:L.eval (single c0)=true:=by
     rcases r0 b0 qn sl c0 (by rw[hq];exact eb c0 b0 (bh rz)) with h1|h2
     ·rw[p7 c0 ab] at h1;exact absurd h1 bF
     ·exact h2
    have sk:R.eval (single d0)=true:=by
     rcases sg c0 sf rZ d0 (by rw[hq];exact eb c0 d0 rt) with h1|h2
     ·rw[p7 d0 ab] at h1;exact absurd h1 bF
     ·exact h2
    rw[← hq];exact r4 (aL a0 d0)
     (dc L (λr hr=>by simp only[single,dT] at hr;simp[aL,hr]) sa)
     (dc R (λr hr=>by simp only[single,dT] at hr;simp[aL,hr]) sk)
  have qa:val D (aL a0 d0) (aO 14 D)=true:=(by rw[n4,cu hS _ 26 Y,hT.2.1,gop_true,bA];exact ⟨by simpa[bP] using h6 false,by simpa[bU] using h6 true⟩);exact rK ((ds a0 d0).1 ((hD _).1 qa))
lemma ml {D:aJ}(h:a9 14 D)(hD:be D)(hT:cg D)(a0:bH 14 D≤14)(r:bu 14 D=0)(m:aN 14 D=∅\/aN 14 D∈dw):False:=by
 rcases m with hI|m
 ·exact jV h hD hT a0 hI
 ·obtain ⟨n,hn,a4⟩:=jh m;have k:aN 14 D=df n:=a4.symm;by_cases a8:(aN 14 D).card=1
  ·have h0:df n={0}:=by
    rcases jg _ m with ⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨-,hI⟩
    all_goals first|omega|(rw[k] at hI;exact hI)
   exact kX h hD hT a0 r (k.trans h0)
  ·have a7:2≤(aN 14 D).card:=by
    rcases jg _ m with ⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩|⟨hc,_⟩
    all_goals omega
   obtain ⟨i1,a6,i2,a5,c0⟩:=oC.1 (by omega:1<(aN 14 D).card);have a1:∀i∈aN 14 D,aU 14 D i.val (aO 14 D):=λi hi=>by
    rcases cr bn h (bl hD) hi with hc|⟨z,-,b6,b5⟩
    ·exact hc
    ·exact (nN (b5▸eB h.1 r b6)).elim
   obtain ⟨s,-,-,-,a2⟩:=dj h hD hT c0 a6 a5 (a1 i1 a6) (a1 i2 a5);have ct:=hT;obtain ⟨-,-,-,p,l,ca,b2,bm,cb,b8⟩:=ct;have b0:∀i∈df n,¬aH i p:=λi hi hip=>by
    have hm:=a2 i (k▸hi) (a1 i (k▸hi)) p hip;cases s
    ·rw[bP] at hm;exact b2 hm
    ·rw[bU] at hm;exact bm hm
   have b1:∀i∈df n,¬aH i l:=λi hi hil=>by
    have hm:=a2 i (k▸hi) (a1 i (k▸hi)) l hil;cases s
    ·rw[bP] at hm;exact cb hm
    ·rw[bU] at hm;exact b8 hm
   have a3:br 14 D≤14:=(oA 14 D).trans a0;have c1:=db 14 D;rcases og n hn ⟨p,l,ca,b0,b1⟩ with hR|hR|hR|hR|hR|hR
   ·have hI:aN 14 D={0,1,2,5}:=k.trans hR;have c2:(aN 14 D).card=4:=by rw[hI];decide
    exact kg h hD hT r Y (by rw[hI];decide)
   ·have hI:aN 14 D={0,1,2}:=k.trans hR;have c3:(aN 14 D).card=3:=by rw[hI];decide
    exact kg h hD hT r Y (by rw[hI])
   ·exact px h hD hT a0 r (k.trans hR)
   ·exact nA h hD hT a0 r (k.trans hR)
   ·exact oY h hD hT a0 r (k.trans hR)
   ·exact kX h hD hT a0 r (k.trans hR)
lemma main_4874 {D0:aJ}(h0:a9 14 D0)(r:be D0)(p:cg D0):False:=by
 have l:bH 14 D0≤14:=(by have:=jm h0;have:=p.2.1;omega);have a0:=nc h0 r;have a3:d5 (aN 14 D0):=(oF D0).mp a0;by_cases m:aN 14 D0=∅
 ·exact jV h0 r p l m
 ·have a5:(aN 14 D0).Nonempty:=nI.2 m;obtain ⟨σ,hσ,a1⟩:=pi _ a3 a5;obtain ⟨h1,h2,-,h4,-,-,-,h8⟩:=lk σ hσ h0 r;have hT:=kt σ hσ h0.1 p;have a2:bH 14 (bz σ D0)≤14:=h4▸l;have k:aN 14 (bz σ D0)∈dw:=h8▸a1;by_cases a4:1≤bu 14 (bz σ D0)
  ·exact mm h1 h2 hT a2 a4 k
  ·exact ml h1 h2 hT a2 Y (oR k)
end PEqualNP.Outside.L_meta_4874_aux
theorem PEqualNP.Outside.L_meta_4874 : ¬ (have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (27 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) ∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) => ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 ∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7);                   PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false) := by
  rintro ⟨C, k, a, b, hsize, hAO, hnodup, hout, hk, hed, hmax, h07⟩
  have hc := PEqualNP.Outside.L_meta_4874_aux.fano_eval_of_edges_max C hAO hed hmax
  obtain ⟨D, hSL, hD, hT⟩ :=
    PEqualNP.Outside.L_meta_4874_aux.ao2_to_dag_4874 C k a b hsize hAO hnodup hout hk hc h07
  exact PEqualNP.Outside.L_meta_4874_aux.main_4874 hSL hD hT
