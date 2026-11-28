import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_33619
abbrev Ls:=List
abbrev LB:=List Bool
abbrev L2(n:Nat):=List (Fin (2*n))
abbrev Cw(n:Nat):=Fin n×L2 n
abbrev EP(n:Nat):=Fin n×Fin n
abbrev ES(n:Nat):=Finset (EP n)
abbrev Fv(n:Nat):=Finset (Fin n)
abbrev PZ:=Polynomial Int
abbrev Sf(n:Nat):=List ((Fv n×Fv n)×Bool)
abbrev CP(n:Nat):=EP n×EP n
abbrev Bo:=Bool
abbrev Op:=Option
abbrev Ft:=Finset
abbrev Pm:=Equiv.Perm
abbrev fE:=@Fin.ext
abbrev pE:=@Prod.ext
abbrev bD:=@Function.update_of_ne
abbrev aX:=@List.length_cons
abbrev aO:=@List.map_cons
abbrev eo:=@Function.iterate_succ_apply
abbrev bI:=@Finset.mem_singleton
abbrev aI:=@congrArg
abbrev cQ:=@List.getD_eq_getElem
abbrev bR:=@List.map_append
abbrev cG:=@decide_eq_true_eq
abbrev dF:=@List.map_congr_left
abbrev ep:=@Finset.mem_insert_self
abbrev fp:=@Equiv.swap_apply_of_ne_of_ne
abbrev dL:=@List.length_append
abbrev fq:=@Function.iterate_add_apply
abbrev aV:=@Finset.mem_insert
abbrev aL:=@Finset.mem_filter
abbrev dG:=@List.flatMap_congr
abbrev dM:=@List.append_assoc
abbrev aT:=@Finset.disjoint_left
abbrev dB:=@Finset.sum_congr
abbrev cR:=@List.append_nil
abbrev eK:=@Equiv.Perm.mul_apply
abbrev eW:=@Function.update_self
abbrev eX:=@Bool.false_eq_true
abbrev gk:=@Finset.mem_singleton_self
abbrev f9:=@Classical.choose_spec
abbrev eY:=@List.flatMap_cons
abbrev eZ:=@List.mem_singleton
abbrev ga:=@Finset.mem_union_left
abbrev fB:=@List.cons_append
abbrev ft:=@List.length_map
abbrev eu:=@List.sum_cons
abbrev jb:=@Function.iterate_succ_apply'
abbrev gJ:=@Finset.subset_biUnion_of_mem
abbrev bS:=@ne_of_lt
abbrev g0:=@List.reverse_reverse
abbrev gx:=@List.length_flatMap
abbrev bL:=@Fin.ext
abbrev kI:=@Nat.pow_le_pow_right
abbrev dN:=@Finset.mem_univ
abbrev gl:=@List.nil_append
abbrev cB:=@List.mem_cons
abbrev gK:=@List.mem_cons_self
abbrev g9:=@List.mem_cons_of_mem
abbrev eL:=@List.mem_append
abbrev e7:=@not_lt_of_gt
abbrev gy:=@Bool.and_eq_true
abbrev dO:=@List.mem_toFinset
abbrev fC:=@List.map_nil
abbrev jA:=@Finset.mem_of_mem_erase
abbrev ia:=@Option.some.injEq
abbrev gm:=@List.map_map
abbrev jB:=@Finset.mem_union_right
abbrev ib:=@List.cons_ne_nil
abbrev hJ:=@List.cons.injEq
abbrev cT:=@dif_pos
abbrev cX:=@Finset.mem_product
abbrev gL:=@Prod.mk.injEq
abbrev gM:=@List.mem_flatMap
abbrev ic:=@List.sum_append
abbrev aY:=@List.mem_range
abbrev jY:=@Polynomial.coeff_zero
abbrev cD:=@Finset.mem_union
abbrev jC:=@List.Perm.nodup_iff
abbrev iw:=@decide_eq_false
abbrev iQ:=@List.getElem_mem
abbrev eC:=@Prod.ext
abbrev cM:=@if_neg
abbrev jZ:=@List.nodup_finRange
abbrev j1:=@List.mem_map_of_mem
abbrev j2:=@List.length_reverse
abbrev gb:=@Nat.mod_lt
abbrev jD:=@List.ext_getElem
abbrev nH:=@Finset.eq_of_subset_of_card_le
abbrev jE:=@List.pairwise_cons
abbrev iR:=@lt_or_gt_of_ne
abbrev iS:=@List.prod_cons
abbrev lv:=@List.length_singleton
abbrev nI:=@List.toFinset_card_of_nodup
abbrev lx:=@List.length_range
abbrev dP:=@if_pos
abbrev jF:=@List.tail_cons
abbrev mE:=@List.getD_eq_default
abbrev mF:=@Nat.mod_eq_of_lt
abbrev j3:=@List.map_reverse
abbrev kJ:=@List.getElem_map
abbrev o6:=@Finset.card_image_of_injective
abbrev j4:=@Fin.append_right
abbrev ly:=@Polynomial.eval_add
abbrev lz:=@Nat.mul_le_mul_left
abbrev qC:=@Nat.bits_append_bit
abbrev kK:=@Finset.sum_insert
abbrev mG:=@List.filterMap_append
abbrev fR:=@true_and
abbrev jG:=@decide_eq_true
abbrev iT:=@decide_false
abbrev j5:=@List.nodup_cons
abbrev gd:=@List.mem_filter
abbrev o7:=@Finset.card_insert_of_notMem
abbrev j6:=@Fin.append_left
abbrev lA:=@List.nodup_flatMap
abbrev mH:=@List.getElem_range
abbrev lB:=@Finset.sum_nat_mod
abbrev gN:=@pow_succ
abbrev iy:=@decide_true
abbrev kL:=@List.pairwise_append
abbrev j7:=@Nat.mod_modEq
abbrev o8:=@List.take_of_length_le
abbrev fu:=@List.nodup_append
abbrev nJ:=@List.filter_eq_nil_iff
abbrev bT:=@Finset.mem_biUnion
abbrev kM:=@Bool.false_and
abbrev mI:=@List.replicate_succ
abbrev mJ:=@List.flatMap_append
abbrev kN:=@Bool.or_eq_true
abbrev o9:=@List.replicate_add
abbrev pa:=@List.length_take
abbrev lC:=@Finset.card_pair
abbrev iU:=@Fin.lt_def
abbrev nK:=@Nat.mul_le_mul_right
abbrev nL:=@Nat.mul_le_mul
abbrev nM:=@List.mem_append_left
abbrev mK:=@List.mem_finRange
abbrev g1:=@add_zero
abbrev pb:=@Nat.pow_le_pow_left
abbrev jH:=@lt_irrefl
abbrev bV:=@Finset.mem_image
abbrev hK:=@lt_trans
abbrev sw:=@List.singleton_append
abbrev sx:=@List.getElem_append_right
abbrev kO:=@Finset.filter_subset
abbrev mL:=@List.length_nil
abbrev pc:=@List.reverse_cons
abbrev cC:=@List.mem_map
abbrev nN:=@Finset.union_comm
abbrev pd:=@Equiv.Perm.sign_swap
abbrev pe:=@Polynomial.eval_mul
abbrev pg:=@List.filterMap_cons
abbrev qD:=@decide_eq_false_iff_not
abbrev nO:=@List.prod_append
abbrev nP:=@List.flatMap_map
abbrev mM:=@Finset.mul_sum
abbrev mN:=@List.map_id
abbrev ph:=@Option.isSome_some
abbrev pj:=@Option.isSome_none
abbrev pk:=@List.filter_filter
abbrev nQ:=@List.range_succ
abbrev nR:=@Finset.card_bij
abbrev nT:=@Bool.cond_false
abbrev sy:=@List.length_replicate
abbrev qE:=@List.length_filter_le
abbrev qF:=@List.append_inj_left'
abbrev lD:=@Finset.disjoint_right
abbrev pl:=@Polynomial.eval_X
abbrev pn:=@Polynomial.eval_C
abbrev qG:=@Finset.card_union_of_disjoint
abbrev nV:=@Finset.sum_bij
abbrev nW:=@Bool.cond_true
abbrev mO:=@List.sum_nil
abbrev po:=@List.filter_cons
abbrev pq:=@Fintype.card_fin
abbrev pv:=@Finset.card_univ
abbrev mP:=@Bool.or_comm
abbrev qH:=@Function.comp_apply
abbrev qI:=@Finset.prod_eq_zero
abbrev qJ:=@Finset.insert_erase
abbrev qK:=@Finset.induction_on
abbrev qL:=@Finset.erase_insert
abbrev kP:=@mul_comm
abbrev uI:=@List.getElem_append_left
abbrev nX:=@Bool.true_and
abbrev pw:=@Option.map_some
abbrev sA:=@List.foldr_cons
abbrev qM:=@List.append_of_mem
abbrev mQ:=@Prod.mk.inj
abbrev nY:=@Nat.sub_self
abbrev nZ:=@Nat.mod_self
abbrev sB:=@Finset.sum_add_distrib
abbrev qN:=@Finset.prod_congr
abbrev sC:=@Finset.card_singleton
abbrev mR:=@mul_assoc
abbrev qO:=@List.reverse_nil
abbrev qP:=@Finset.sum_const
abbrev qQ:=@Bool.toNat_false
abbrev j8:=@pow_add
abbrev px:=@List.tail_nil
abbrev py:=@Bool.and_comm
abbrev n0:=@smul_eq_mul
abbrev sD:=@Polynomial.coeff_add
abbrev sE:=@Function.update_idem
abbrev sF:=@Equiv.Perm.one_apply
abbrev qR:=@Nat.div_add_mod
abbrev uJ:=@List.reverse_append
abbrev sG:=@Finset.notMem_empty
abbrev sH:=@Finset.card_biUnion
abbrev j9:=@one_mul
abbrev uK:=@Finset.disjoint_empty_right
abbrev lE:=@zero_add
abbrev qS:=@lt_of_le_of_ne
abbrev uL:=@Nat.mod_two_eq_zero_or_one
abbrev sI:=@List.toFinset_cons
abbrev sJ:=@Finset.sum_eq_zero
abbrev uM:=@Finset.prod_pow_eq_pow_sum
abbrev uN:=@Finset.filter_eq_empty_iff
abbrev sK:=@Bool.false_ne_true
abbrev sL:=@not_true_eq_false
abbrev kQ:=@mul_one
abbrev kR:=@map_mul
abbrev sM:=@Nat.lt_succ_of_lt
abbrev sN:=@List.flatten_cons
abbrev sO:=@Finset.sum_filter
abbrev sP:=@Bool.not_eq_true'
abbrev qT:=@lt_trichotomy
abbrev uO:=@Polynomial.eval_monomial
abbrev uP:=@Finset.singleton_biUnion
abbrev uQ:=@Finset.orderEmbOfFin_mem
abbrev uR:=@Finset.card_erase_of_mem
abbrev sQ:=@Bool.not_true
abbrev pz:=@Finset.mem_powerset
abbrev mS:=@le_trans
abbrev sR:=@List.map_flatMap
abbrev sS:=@List.flatten_nil
abbrev uS:=@List.append_cancel_left
abbrev sT:=@Finset.sum_union
abbrev sU:=@Finset.sum_image
abbrev uT:=@Finset.not_disjoint_iff
abbrev fL:=@Finset.mem_erase
abbrev lF:=@dif_neg
abbrev qU:=@Nat.succ_mul
abbrev uU:=@List.filterMap_reverse
abbrev uV:=@List.drop_of_length_le
abbrev uW:=@List.append_inj_right'
abbrev uX:=@Finset.ne_of_mem_erase
abbrev uY:=@Equiv.symm_apply_apply
abbrev uZ:=@Equiv.apply_symm_apply
abbrev sV:=@Option.some.inj
abbrev sW:=@Nat.min_eq_left
abbrev sX:=@List.filter_map
abbrev u0:=@and_iff_right_iff_imp
abbrev u1:=@List.toFinset_card_le
abbrev u2:=@Finset.sum_range_succ
abbrev pC:=@lt_asymm
abbrev sY:=@le_antisymm
abbrev qV:=@Nat.add_mod
abbrev u3:=@List.ofFn_fin_append
abbrev sZ:=@List.drop_zero
abbrev s0:=@List.Perm.refl
abbrev u4:=@Function.update_comm
abbrev u5:=@Finset.add_sum_erase
abbrev s3:=@Bool.and_false
open List (mem_iff_getElem sum_replicate mem_reverse not_mem_nil nodup_range flatMap_nil take_append drop_append replicate prod_nil finRange ofFn)
open Function (Involutive Injective Bijective update)
open Nat (mod_mod)
open Equiv (swap)
open Finset (univ)
open Turing.TM2 (stepAux step)
open PEqualNP.Library (ComputableInPolyTime encodePair)
open Sum (inl inr)
namespace Lib
abbrev U(f:LB->LB):Prop:=ComputableInPolyTime (fun x:LB=>x) (fun x:LB=>x) f
end Lib
open Lib
section
namespace Lib.Machines
open Turing
lemma B3{σ:Type}(f:σ->Op σ)(n:Nat):(flip bind f)^[n] none=none:=by induction n with|zero=>{rfl}|succ n b=>{rw[eo];exact b}
lemma zm{σ j:Type}(f:σ->Op σ)(g:j->Op j)(i:σ->j)(h:∀ c o,f c=some o->g (i c)=some (i o)):∀(n:Nat) (a b:σ),(flip bind f)^[n] (some a)=some b->(flip bind g)^[n] (some (i a))=some (i b):=by
 intro n;induction n with
 | zero=>intro a b d;have:a=b:=sV d;rw[this];rfl
 | succ n q=>
   intro a b d;rw[eo] at d ⊢;cases hfa:f a with
   | none=>have e:flip bind f (some a)=none:=hfa;rw[e,B3] at d;exact absurd d (by simp)
   | some c=>have e:flip bind f (some a)=some c:=hfa;have r:flip bind g (some (i a))=some (i c):=h a c hfa;rw[e] at d;rw[r];exact q c b d
section pushes
variable {K:Type} [DecidableEq K] {Γ:K->Type} {Λ σ:Type}
def pushes:TM2.Stmt Γ Λ σ->Nat
 | .push _ _ q=>pushes q+1
 | .peek _ _ q=>pushes q
 | .pop _ _ q=>pushes q
 | .load _ q=>pushes q
 | .branch _ q₁ q₂=>max (pushes q₁) (pushes q₂)
 | .goto _=>0
 | .halt=>0
lemma Dk(q:TM2.Stmt Γ Λ σ)(v:σ)(j:∀ k,Ls (Γ k))(k:K):((stepAux q v j).stk k).length<=(j k).length+pushes q:=by induction q generalizing v j with|push o f q i=>{simp only[stepAux,pushes];refine (i _ _).trans ?_;by_cases h:k=o;{subst h;rw[eW,aX];omega};{rw[bD h];omega}}|peek o f q i=>{exact i _ _}|pop o f q i=>{simp only[stepAux,pushes];refine (i _ _).trans ?_;by_cases h:k=o;{subst h;rw[eW,List.length_tail];omega};{rw[bD h]}}|load a q i=>{exact i _ _}|branch f c b e d=>{simp only[stepAux,pushes];cases f v;{exact (d v j).trans (by have:=le_max_right (pushes c) (pushes b);omega)};{exact (e v j).trans (by have:=le_max_left (pushes c) (pushes b);omega)}}|goto f=>{simp[stepAux,pushes]}|halt=>{simp[stepAux,pushes]}
end pushes
noncomputable def maxPush(tm:FinTM2):Nat:=(@univ tm.Λ tm.ΛFin).sup fun l=>pushes (tm.m l)
lemma DB(tm:FinTM2)(c b:TM2.Cfg tm.Γ tm.Λ tm.σ)(h:step tm.m c=some b)(k:tm.K):(b.stk k).length<=(c.stk k).length+maxPush tm:=by
 obtain⟨l,v,d⟩:=c;cases l with
 | none=>simp[step] at h
 | some l=>simp only[step,ia] at h;subst h;refine (Dk _ _ _ _).trans ?_;have:pushes (tm.m l)<=maxPush tm:=Finset.le_sup (f:=fun l=>pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l);simpa using this
lemma Cd(tm:FinTM2)(k:tm.K):∀(n:Nat) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),(flip bind (step tm.m))^[n] (some a)=some b->(b.stk k).length<=(a.stk k).length+maxPush tm*n:=by
 intro n;induction n with
 | zero=>intro a b d;have:a=b:=sV d;rw[this];simp
 | succ n h=>
   intro a b d;rw[eo] at d;cases hfa:step tm.m a with
   | none=>have e:flip bind (step tm.m) (some a)=none:=hfa;rw[e,B3] at d;exact absurd d (by simp)
   | some c=>have e:flip bind (step tm.m) (some a)=some c:=hfa;rw[e] at d;have j:=h c b d;have i:=DB tm a c hfa k;rw[Nat.mul_succ];omega
lemma d4(tm:FinTM2)(s:Ls (tm.Γ tm.k₀)):initList tm s=(⟨some tm.main,tm.initialState,update (fun _=>[]) tm.k₀ s⟩:TM2.Cfg tm.Γ tm.Λ tm.σ):=by unfold initList;congr 1;funext k;by_cases h:k=tm.k₀;{subst h;simp};{simp[h]}
lemma d5(tm:FinTM2)(s:Ls (tm.Γ tm.k₁)):haltList tm s=(⟨none,tm.initialState,update (fun _=>[]) tm.k₁ s⟩:TM2.Cfg tm.Γ tm.Λ tm.σ):=by unfold haltList;congr 1;funext k;by_cases h:k=tm.k₁;{subst h;simp};{simp[h]}
lemma yS(p:Polynomial Nat){x y:Nat}(h:x<=y):p.eval x<=p.eval y:=by induction p using Polynomial.induction_on' with|add p q e b=>{rw[ly,ly];exact add_le_add e b}|monomial d c=>{rw[uO,uO];exact lz _ (pb h _)}
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def zn:LB->TM2.Stmt (fun _:Unit=>Bo) Unit Bo
 | []=>.halt
 | a::l=>.push () (fun _=>a) (zn l)
def d3(l:LB):Unit->TM2.Stmt (fun _:Unit=>Bo) Unit Bo:=fun _=>.pop () (fun _ o=>o.isSome) (.branch (fun s=>s) (.load (fun _=>false) (.goto fun _=>())) (zn l.reverse))
def xM(l:LB):FinTM2 where
 K:=Unit
 k₀:=()
 k₁:=()
 Γ _:=Bo
 Λ:=Unit
 main:=()
 σ:=Bo
 initialState:=false
 m:=d3 l
abbrev rY:Type:=TM2.Cfg (fun _:Unit=>Bo) Unit Bo
lemma yP(b T:LB):update (fun _:Unit=>b) () T=fun _=>T:=by funext k;simp
lemma Di(l:LB)(v:Bo)(b:LB):stepAux (zn l) v (fun _:Unit=>b)=(⟨none,v,fun _=>l.reverse++b⟩:rY):=by induction l generalizing b with|nil=>{rfl}|cons a l c=>{simp only[zn,stepAux];rw[yP,c];simp}
lemma Dp(l:LB)(x:Bo)(a:LB):step (d3 l) (⟨some (),false,fun _=>x::a⟩:rY)=some ⟨some (),false,fun _=>a⟩:=by simp only[step,d3,stepAux];rw[yP];simp
lemma Dv(l:LB):step (d3 l) (⟨some (),false,fun _=>[]⟩:rY)=some ⟨none,false,fun _=>l⟩:=by simp only[step,d3,stepAux];rw[yP];simp only[List.head?_nil,pj,nT,px];rw[Di];simp
lemma Dn(l:LB)(a:LB):(flip bind (step (d3 l)))^[a.length+1] (some (⟨some (),false,fun _=>a⟩:rY))=some ⟨none,false,fun _=>l⟩:=by induction a with|nil=>{exact Dv l}|cons x a b=>{rw[aX,eo];have e:flip bind (step (d3 l)) (some (⟨some (),false,fun _=>x::a⟩:rY))=some ⟨some (),false,fun _=>a⟩:=Dp l x a;rw[e,b]}
lemma Du(l:LB)(a:LB):(flip bind (step (d3 l)))^[a.length+1] (some (initList (xM l) a))=some (haltList (xM l) l):=by refine (aI (fun c=>(flip bind (step (d3 l)))^[a.length+1] (some c)) (d4 (xM l) a)).trans (Eq.trans ?_ (aI some (d5 (xM l) l)).symm);show (flip bind (step (d3 l)))^[a.length+1] (some (⟨some (),false,update (fun _=>[]) () a⟩:rY))=some (⟨none,false,update (fun _=>[]) () l⟩:rY);rw[yP,yP];exact Dn l a
lemma Aa(l:LB):Nonempty (Turing.TM2ComputableInPolyTime (fun x:LB=>x) (fun x:LB=>x) (fun _:LB=>l)):=⟨{
 tm:=xM l
 inputAlphabet:=Equiv.refl _
 outputAlphabet:=Equiv.refl _
 time:=Polynomial.X+1
 outputsFun:=fun a=>
  { steps:=a.length+1
    evals_in_steps:=by
     have b:∀ l:LB,List.map (Equiv.refl Bo).invFun l=l:=fun l=>by simp
     exact (aI (fun x=>(flip bind (step (d3 l)))^[a.length+1] (some (initList (xM l) x))) (b a)).trans ((Du l a).trans (aI (fun x=>some (haltList (xM l) x)) (b l).symm))
    steps_le_m:=by simp } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
section update
variable {ι:Type} [DecidableEq ι] {β:ι->Type}
lemma B6(j:∀ i,β i){a b c:ι}(e:a≠b)(d:a≠c)(x h:β a)(y:β b)(z:β c):update (update (update (update j a x) b y) c z) a h=update (update (update j a h) b y) c z:=by rw[u4 d.symm,u4 e.symm,sE]
lemma B5(h:∀ i,β i){a b c:ι}(d:b≠c)(x:β a)(y e:β b)(z:β c):update (update (update (update h a x) b y) c z) b e=update (update (update h a x) b e) c z:=by rw[u4 d.symm,sE]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Op (M1.K ⊕ M2.K)
abbrev CΓ:CK M1 M2->Type
 | none=>M2.Γ M2.k₀
 | some (inl k)=>M1.Γ k
 | some (inr k)=>M2.Γ k
abbrev CΛ:Type:=M1.Λ ⊕ M2.Λ ⊕ Bo
abbrev Cσ:Type:=M1.σ×M2.σ×Op (M2.Γ M2.k₀)
variable {M1 M2}
def wR:TM2.Stmt M1.Γ M1.Λ M1.σ->TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q=>.push (some (inl k)) (fun s=>f s.1) (wR q)
 | .peek k f q=>.peek (some (inl k)) (fun s o=>(f s.1 o,s.2)) (wR q)
 | .pop k f q=>.pop (some (inl k)) (fun s o=>(f s.1 o,s.2)) (wR q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (wR q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (wR q₁) (wR q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr (inr false))
def wS:TM2.Stmt M2.Γ M2.Λ M2.σ->TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q=>.push (some (inr k)) (fun s=>f s.2.1) (wS q)
 | .peek k f q=>.peek (some (inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (wS q)
 | .pop k f q=>.pop (some (inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (wS q)
 | .load a q=>.load (fun s=>(s.1,a s.2.1,s.2.2)) (wS q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.2.1) (wS q₁) (wS q₂)
 | .goto f=>.goto (fun s=>inr (inl (f s.2.1)))
 | .halt=>.halt
variable (M1 M2)
def tA(b:M1.Γ M1.k₁->M2.Γ M2.k₀):Op (M2.Γ M2.k₀)->TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none=>.goto (fun _=>inr (inl M2.main))
 | some d=>.pop (some (inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map b)) (.branch (fun s=>s.2.2.isSome) (.push none (fun s=>s.2.2.getD d) (.goto fun _=>inr (inr false))) (.goto fun _=>inr (inr true)))
def tB:Op (M2.Γ M2.k₀)->TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none=>.goto (fun _=>inr (inl M2.main))
 | some d=>.pop none (fun s o=>(s.1,s.2.1,o)) (.branch (fun s=>s.2.2.isSome) (.push (some (inr M2.k₀)) (fun s=>s.2.2.getD d) (.goto fun _=>inr (inr true))) (.goto fun _=>inr (inl M2.main)))
def ig(b:M1.Γ M1.k₁->M2.Γ M2.k₀)(d:Op (M2.Γ M2.k₀)):CΛ M1 M2->TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | inl l=>wR (M1.m l)
 | inr (inl l)=>wS (M2.m l)
 | inr (inr false)=>tA M1 M2 b d
 | inr (inr true)=>tB M1 M2 d
def comp(b:M1.Γ M1.k₁->M2.Γ M2.k₀)(d:Op (M2.Γ M2.k₀)):FinTM2:=
 haveI:=M1.kFin
 haveI:=M2.kFin
 haveI:=M1.ΛFin
 haveI:=M2.ΛFin
 haveI:=M1.σFin
 haveI:=M2.σFin
 haveI:=M2.Γk₀Fin
 { K:=CK M1 M2
   k₀:=some (inl M1.k₀)
   k₁:=some (inr M2.k₁)
   Γ:=CΓ M1 M2
   Λ:=CΛ M1 M2
   main:=inl M1.main
   σ:=Cσ M1 M2
   initialState:=(M1.initialState,M2.initialState,none)
   Γk₀Fin:=M1.Γk₀Fin
   m:=ig M1 M2 b d }
variable {M1 M2}
def xO(b:∀ k,Ls (M1.Γ k)):∀ k,Ls (CΓ M1 M2 k)
 | none=>[]
 | some (inl k)=>b k
 | some (inr _)=>[]
def xN(b:∀ k,Ls (M2.Γ k)):∀ k,Ls (CΓ M1 M2 k)
 | none=>[]
 | some (inl _)=>[]
 | some (inr k)=>b k
lemma zd(b:∀ k,Ls (M1.Γ k))(k:M1.K)(x:Ls (M1.Γ k)):(xO (update b k x):∀ k,Ls (CΓ M1 M2 k))=update (xO b) (some (inl k)) x:=by
 funext j;rcases j with _|j|j
 {rw[bD (by simp)];rfl};{by_cases h:j=k;{subst h;rw[eW];show update b j x j=x;rw[eW]};{rw[bD (by simpa using h)];show update b k x j=b j;rw[bD h]}};{rw[bD (by simp)];rfl}
lemma zc(b:∀ k,Ls (M2.Γ k))(k:M2.K)(x:Ls (M2.Γ k)):(xN (update b k x):∀ k,Ls (CΓ M1 M2 k))=update (xN b) (some (inr k)) x:=by
 funext j;rcases j with _|j|j
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{by_cases h:j=k;{subst h;rw[eW];show update b j x j=x;rw[eW]};{rw[bD (by simpa using h)];show update b k x j=b j;rw[bD h]}}
lemma Ca:(xO (fun _=>[]):∀ k,Ls (CΓ M1 M2 k))=fun _=>[]:=by funext j;rcases j with _|j|j <;> rfl
lemma B9:(xN (fun _=>[]):∀ k,Ls (CΓ M1 M2 k))=fun _=>[]:=by funext j;rcases j with _|j|j <;> rfl
def wb(w:M2.σ×Op (M2.Γ M2.k₀))(c:TM2.Cfg M1.Γ M1.Λ M1.σ):TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2):=⟨some (c.l.elim (inr (inr false)) inl),(c.var,w),xO c.stk⟩
def wc(u:M1.σ)(b:Op (M2.Γ M2.k₀))(c:TM2.Cfg M2.Γ M2.Λ M2.σ):TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2):=⟨c.l.map (fun l=>inr (inl l)),(u,c.var,b),xN c.stk⟩
lemma CV(w:M2.σ×Op (M2.Γ M2.k₀))(q:TM2.Stmt M1.Γ M1.Λ M1.σ)(v:M1.σ)(b:∀ k,Ls (M1.Γ k)):stepAux (wR q) ((v,w):Cσ M1 M2) (xO b)=wb w (stepAux q v b):=by
 induction q generalizing v b with
 | push k f q e=>
   have:=e v (update b k (f v::b k))
   rw[zd] at this;exact this
 | peek k f q e=>exact e _ _
 | pop k f q e=>
   have:=e (f v (b k).head?) (update b k (b k).tail)
   rw[zd] at this;exact this
 | load a q e=>exact e _ _
 | branch f i h d c=>simp only[wR,stepAux];cases f v;{exact c v b};{exact d v b}
 | goto f=>rfl
 | halt=>rfl
lemma CW(u:M1.σ)(b:Op (M2.Γ M2.k₀))(q:TM2.Stmt M2.Γ M2.Λ M2.σ)(v:M2.σ)(c:∀ k,Ls (M2.Γ k)):stepAux (wS q) ((u,v,b):Cσ M1 M2) (xN c)=wc u b (stepAux q v c):=by
 induction q generalizing v c with
 | push k f q h=>
   have:=h v (update c k (f v::c k))
   rw[zc] at this;exact this
 | peek k f q h=>exact h _ _
 | pop k f q h=>
   have:=h (f v (c k).head?) (update c k (c k).tail)
   rw[zc] at this;exact this
 | load a q h=>exact h _ _
 | branch f j i e d=>simp only[wS,stepAux];cases f v;{exact d v c};{exact e v c}
 | goto f=>rfl
 | halt=>rfl
variable (f0_:M1.Γ M1.k₁->M2.Γ M2.k₀) (d:Op (M2.Γ M2.k₀))
lemma AA(w:M2.σ×Op (M2.Γ M2.k₀))(c b:TM2.Cfg M1.Γ M1.Λ M1.σ)(h:step M1.m c=some b):step (ig M1 M2 f0_ d) (wb w c)=some (wb w b):=by
 obtain⟨l,v,e⟩:=c;cases l with
 | none=>simp[step] at h
 | some l=>simp only[step,ia] at h;subst h;exact aI some (CV w (M1.m l) v e)
lemma AD(u:M1.σ)(b:Op (M2.Γ M2.k₀))(c e:TM2.Cfg M2.Γ M2.Λ M2.σ)(h:step M2.m c=some e):step (ig M1 M2 f0_ d) (wc u b c)=some (wc u b e):=by
 obtain⟨l,v,i⟩:=c;cases l with
 | none=>simp[step] at h
 | some l=>simp only[step,ia] at h;subst h;exact aI some (CW u b (M2.m l) v i)
def st(l:Ls (M1.Γ M1.k₁))(t u:Ls (M2.Γ M2.k₀)):∀ k,Ls (CΓ M1 M2 k):=update (update (update (fun _=>[]) (some (inl M1.k₁)) l) none t) (some (inr M2.k₀)) u
lemma yh(l:Ls (M1.Γ M1.k₁))(t u:Ls (M2.Γ M2.k₀)):(st l t u:∀ k,Ls (CΓ M1 M2 k)) (some (inl M1.k₁))=l:=by unfold st;rw[bD (by simp),bD (by simp),eW]
lemma wP(l:Ls (M1.Γ M1.k₁))(t u:Ls (M2.Γ M2.k₀)):(st l t u:∀ k,Ls (CΓ M1 M2 k)) none=t:=by unfold st;rw[bD (by simp),eW]
lemma zQ(l:Ls (M1.Γ M1.k₁))(t u:Ls (M2.Γ M2.k₀)):(st l t u:∀ k,Ls (CΓ M1 M2 k)) (some (inr M2.k₀))=u:=by unfold st;rw[eW]
lemma Cc(l b:Ls (M1.Γ M1.k₁))(t u:Ls (M2.Γ M2.k₀)):update (st l t u:∀ k,Ls (CΓ M1 M2 k)) (some (inl M1.k₁)) b=st b t u:=B6 _ (by simp) (by simp) _ _ _ _
lemma Ae(l:Ls (M1.Γ M1.k₁))(t b u:Ls (M2.Γ M2.k₀)):update (st l t u:∀ k,Ls (CΓ M1 M2 k)) none b=st l b u:=B5 _ (by simp) _ _ _ _
lemma DF(l:Ls (M1.Γ M1.k₁))(t u b:Ls (M2.Γ M2.k₀)):update (st l t u:∀ k,Ls (CΓ M1 M2 k)) (some (inr M2.k₀)) b=st l t b:=sE _ _ _
lemma Ak(l:Ls (M1.Γ M1.k₁)):(st l [] []:∀ k,Ls (CΓ M1 M2 k))=update (fun _=>[]:∀ k,Ls (CΓ M1 M2 k)) (some (inl M1.k₁)) l:=by unfold st;rw[Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr];{rw[bD (by simp)]};{rw[bD (by simp),bD (by simp)]}
lemma wO(u:Ls (M2.Γ M2.k₀)):(st [] [] u:∀ k,Ls (CΓ M1 M2 k))=update (fun _=>[]:∀ k,Ls (CΓ M1 M2 k)) (some (inr M2.k₀)) u:=by unfold st;congr 1;rw[Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr];{rfl};{rw[bD (by simp)]}
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {M1 M2:FinTM2} (f0_:M1.Γ M1.k₁->M2.Γ M2.k₀)
abbrev nF(M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
lemma DE(e:M2.Γ M2.k₀)(d:M1.σ)(c:M2.σ)(b:Op (M2.Γ M2.k₀))(x:M1.Γ M1.k₁)(l:Ls (M1.Γ M1.k₁))(t u:Ls (M2.Γ M2.k₀)):step (ig M1 M2 f0_ (some e)) (⟨some (inr (inr false)),(d,c,b),st (x::l) t u⟩:nF M1 M2)=some ⟨some (inr (inr false)),(d,c,some (f0_ x)),st l (f0_ x::t) u⟩:=by simp only[step,ig,tA,stepAux];rw[yh];simp only[List.head?_cons,jF,pw,ph,nW,Option.getD_some];rw[Cc,wP,Ae]
lemma AN(e:M2.Γ M2.k₀)(d:M1.σ)(c:M2.σ)(b:Op (M2.Γ M2.k₀))(t u:Ls (M2.Γ M2.k₀)):step (ig M1 M2 f0_ (some e)) (⟨some (inr (inr false)),(d,c,b),st [] t u⟩:nF M1 M2)=some ⟨some (inr (inr true)),(d,c,none),st [] t u⟩:=by simp only[step,ig,tA,stepAux];rw[yh];simp only[List.head?_nil,px,Option.map_none,pj,nT];rw[Cc]
lemma DD(e:M2.Γ M2.k₀)(d:M1.σ)(c:M2.σ)(b:Op (M2.Γ M2.k₀))(x:M2.Γ M2.k₀)(t u:Ls (M2.Γ M2.k₀)):step (ig M1 M2 f0_ (some e)) (⟨some (inr (inr true)),(d,c,b),st [] (x::t) u⟩:nF M1 M2)=some ⟨some (inr (inr true)),(d,c,some x),st [] t (x::u)⟩:=by simp only[step,ig,tB,stepAux];rw[wP];simp only[List.head?_cons,jF,ph,nW,Option.getD_some];rw[Ae,zQ,DF]
lemma AM(e:M2.Γ M2.k₀)(d:M1.σ)(c:M2.σ)(b:Op (M2.Γ M2.k₀))(u:Ls (M2.Γ M2.k₀)):step (ig M1 M2 f0_ (some e)) (⟨some (inr (inr true)),(d,c,b),st [] [] u⟩:nF M1 M2)=some ⟨some (inr (inl M2.main)),(d,c,none),st [] [] u⟩:=by simp only[step,ig,tB,stepAux];rw[wP];simp only[List.head?_nil,px,pj,nT];rw[Ae]
lemma Av(h:M2.Γ M2.k₀)(d:M1.σ)(c:M2.σ)(u:Ls (M2.Γ M2.k₀)):∀(l:Ls (M1.Γ M1.k₁)) (t:Ls (M2.Γ M2.k₀)) (b:Op (M2.Γ M2.k₀)),(flip bind (step (ig M1 M2 f0_ (some h))))^[l.length+1] (some (⟨some (inr (inr false)),(d,c,b),st l t u⟩:nF M1 M2))=some ⟨some (inr (inr true)),(d,c,none),st [] ((l.map f0_).reverse++t) u⟩:=by
 intro l;induction l with
 | nil=>intro t b;exact AN f0_ h d c b t u
 | cons x l i=>intro t b;rw[aX,eo];have e:flip bind (step (ig M1 M2 f0_ (some h))) (some (⟨some (inr (inr false)),(d,c,b),st (x::l) t u⟩:nF M1 M2))=some ⟨some (inr (inr false)),(d,c,some (f0_ x)),st l (f0_ x::t) u⟩:=DE f0_ h d c b x l t u;rw[e,i];simp
lemma Aw(h:M2.Γ M2.k₀)(d:M1.σ)(c:M2.σ):∀(t u:Ls (M2.Γ M2.k₀)) (b:Op (M2.Γ M2.k₀)),(flip bind (step (ig M1 M2 f0_ (some h))))^[t.length+1] (some (⟨some (inr (inr true)),(d,c,b),st [] t u⟩:nF M1 M2))=some ⟨some (inr (inl M2.main)),(d,c,none),st [] [] (t.reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro u b;exact AM f0_ h d c b u
 | cons x t i=>intro u b;rw[aX,eo];have e:flip bind (step (ig M1 M2 f0_ (some h))) (some (⟨some (inr (inr true)),(d,c,b),st [] (x::t) u⟩:nF M1 M2))=some ⟨some (inr (inr true)),(d,c,some x),st [] t (x::u)⟩:=DD f0_ h d c b x t u;rw[e,i];simp
lemma A5(d:Op (M2.Γ M2.k₀))(hd:d=none->IsEmpty (M2.Γ M2.k₀))(c:M1.σ)(b:M2.σ)(o:Ls (M1.Γ M1.k₁)):∃ n,n<=2*o.length+2/\(flip bind (step (ig M1 M2 f0_ d)))^[n] (some (⟨some (inr (inr false)),(c,b,none),update (fun _=>[]:∀ k,Ls (CΓ M1 M2 k)) (some (inl M1.k₁)) o⟩:nF M1 M2))=some ⟨some (inr (inl M2.main)),(c,b,none),update (fun _=>[]:∀ k,Ls (CΓ M1 M2 k)) (some (inr M2.k₀)) (o.map f0_)⟩:=by
 cases d with
 | none=>
   have:=hd rfl
   have e:o=[]:=by cases o with|nil=>{rfl}|cons x _=>{exact (IsEmpty.false (f0_ x)).elim}
   subst e;refine⟨1,by omega,?_⟩;show some _=some _;simp only[ig,tA,stepAux,fC];rw[Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
 | some h=>refine⟨((o.map f0_).reverse++[]).length+1+(o.length+1),by simp;omega,?_⟩;rw[fq,<- Ak,Av,Aw,<- wO];simp
lemma AY(d:Op (M2.Γ M2.k₀))(i:Ls (M1.Γ M1.k₀)):wb (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 f0_ d) i:=by rw[d4];refine Eq.trans ?_ (d4 (comp M1 M2 f0_ d) i).symm;show (⟨_,_,xO _⟩:nF M1 M2)=_;rw[zd,Ca];rfl
lemma AZ(w:M2.σ×Op (M2.Γ M2.k₀))(o:Ls (M1.Γ M1.k₁)):wb w (haltList M1 o)=(⟨some (inr (inr false)),(M1.initialState,w),update (fun _=>[]:∀ k,Ls (CΓ M1 M2 k)) (some (inl M1.k₁)) o⟩:nF M1 M2):=by rw[d5];show (⟨_,_,xO _⟩:nF M1 M2)=_;rw[zd,Ca];rfl
lemma AW(u:M1.σ)(i:Ls (M2.Γ M2.k₀)):wc u none (initList M2 i)=(⟨some (inr (inl M2.main)),(u,M2.initialState,none),update (fun _=>[]:∀ k,Ls (CΓ M1 M2 k)) (some (inr M2.k₀)) i⟩:nF M1 M2):=by rw[d4];show (⟨_,_,xN _⟩:nF M1 M2)=_;rw[zc,B9];rfl
lemma AX(d:Op (M2.Γ M2.k₀))(o:Ls (M2.Γ M2.k₁)):wc M1.initialState none (haltList M2 o)=haltList (comp M1 M2 f0_ d) o:=by rw[d5];refine Eq.trans ?_ (d5 (comp M1 M2 f0_ d) o).symm;show (⟨_,_,xN _⟩:nF M1 M2)=_;rw[zc,B9];rfl
lemma yO(d:Op (M2.Γ M2.k₀))(hd:d=none->IsEmpty (M2.Γ M2.k₀))(i:Ls (M1.Γ M1.k₀))(c:Ls (M1.Γ M1.k₁))(q:Ls (M2.Γ M2.k₁))(b e:Nat)(r:(flip bind (step M1.m))^[b] (some (initList M1 i))=some (haltList M1 c))(w:(flip bind (step M2.m))^[e] (some (initList M2 (c.map f0_)))=some (haltList M2 q)):∃ n,n<=b+(2*c.length+2)+e/\c.length<=i.length+maxPush M1*b/\(flip bind (step (ig M1 M2 f0_ d)))^[n] (some (initList (comp M1 M2 f0_ d) i))=some (haltList (comp M1 M2 f0_ d) q):=by
 have o:=zm (step M1.m) (step (ig M1 M2 f0_ d)) (wb (M2.initialState,none)) (AA f0_ d _) b _ _ r;rw[AY f0_ d,AZ] at o;obtain⟨u,v,s⟩:=A5 f0_ d hd M1.initialState M2.initialState c;have j:=zm (step M2.m) (step (ig M1 M2 f0_ d)) (wc M1.initialState none) (AD f0_ d _ _) e _ _ w;rw[AW,AX f0_ d] at j;refine⟨e+(u+b),by omega,?_,?_⟩
 ·
  have:=Cd M1 M1.k₁ b _ _ r
  rw[d5,d4] at this;simp only[eW] at this;refine this.trans (Nat.add_le_add_right ?_ _);by_cases h:M1.k₁=M1.k₀;{rw[h,eW]};{rw[bD h];simp}
 {rw[fq,fq,o,s,j];rfl}
lemma Dw{M E K s r q:Type}(j:M->Ls s)(o:E->Ls r)(B:K->Ls q)(f:M->E)(g:E->K)(c:TM2ComputableInPolyTime j o f)(b:TM2ComputableInPolyTime o B g):Nonempty (TM2ComputableInPolyTime j B (fun a=>g (f a))):=by
 classical
 let e:c.tm.Γ c.tm.k₁->b.tm.Γ b.tm.k₀:=
  fun x=>b.inputAlphabet.invFun (c.outputAlphabet x)
 let d:Op (b.tm.Γ b.tm.k₀):=
  if h:Nonempty (b.tm.Γ b.tm.k₀) then some (Classical.choice h) else none
 have hd:d=none->IsEmpty (b.tm.Γ b.tm.k₀):=(by intro h;by_cases L:Nonempty (b.tm.Γ b.tm.k₀);{simp[d,L] at h};{exact not_nonempty_iff.mp L})
 let T:Polynomial Nat:=
  c.time+(Polynomial.C 2*(Polynomial.X+Polynomial.C (maxPush c.tm)*c.time)+Polynomial.C 2)+b.time.comp (Polynomial.X+Polynomial.C (maxPush c.tm)*c.time)
 have i:∀ a,∃ n,n<=T.eval (j a).length/\(flip bind (step (ig c.tm b.tm e d)))^[n] (some (initList (comp c.tm b.tm e d) (List.map c.inputAlphabet.invFun (j a))))=some (haltList (comp c.tm b.tm e d) (List.map b.outputAlphabet.invFun (B (g (f a))))):=by
  intro a;have z:=c.outputsFun a;have w:=b.outputsFun (f a);have S:(List.map c.outputAlphabet.invFun (o (f a))).map e=List.map b.inputAlphabet.invFun (o (f a)):=(by rw[gm];refine dF fun y _=>?_;show b.inputAlphabet.invFun (c.outputAlphabet (c.outputAlphabet.invFun y))=_;exact aI _ (c.outputAlphabet.right_inv y));have P:(flip bind (step b.tm.m))^[w.steps] (some (initList b.tm ((List.map c.outputAlphabet.invFun (o (f a))).map e)))=some (haltList b.tm (List.map b.outputAlphabet.invFun (B (g (f a))))):=(by rw[S];exact w.evals_in_steps);obtain⟨n,L,v,u⟩:=yO e d hd _ _ _ z.steps w.steps z.evals_in_steps P;refine⟨n,L.trans ?_,u⟩;have Q:=z.steps_le_m;have b2:=w.steps_le_m;simp only[ft] at v
  have a5:maxPush c.tm*z.steps<=
   maxPush c.tm*Polynomial.eval (j a).length c.time:=lz _ Q
  have b3:Polynomial.eval (o (f a)).length b.time<=
   Polynomial.eval ((j a).length+maxPush c.tm*Polynomial.eval (j a).length c.time)
    b.time:=yS _ (by omega)
  simp only[T,ly,pe,pn,pl,Polynomial.eval_comp,ft];omega
 exact⟨{
  tm:=comp c.tm b.tm e d
  inputAlphabet:=c.inputAlphabet
  outputAlphabet:=b.outputAlphabet
  time:=T
  outputsFun:=fun a=>
   ⟨⟨Classical.choose (i a),(f9 (i a)).2⟩,(f9 (i a)).1⟩ }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {G0 G1:Type}
abbrev FΓ (G0 G1:Type):Op Bo->Type
 | some false=>G0
 | none=>Op G0
 | some true=>G1
def iY(b:G0->Op G1)(d:Op G1):Bo->TM2.Stmt (FΓ G0 G1) Bo (Op G0)
 | false=>.pop (some false) (fun _ o=>o) (.branch (fun s=>s.isSome) (.push none (fun s=>s) (.goto fun _=>false)) (.goto fun _=>true))
 | true=>
   .pop none (fun _ o=>o.join) (.branch (fun s=>s.isSome) (.branch (fun s=>(s.bind b).isSome) (match d with
         | some c=>.push (some true) (fun s=>(s.bind b).getD c) (.goto fun _=>true)
         | none=>.goto fun _=>true)
         (.goto fun _=>true))
     .halt)
def fm[Fintype G0](b:G0->Op G1)(d:Op G1):FinTM2 where
 K:=Op Bo
 k₀:=some false
 k₁:=some true
 Γ:=FΓ G0 G1
 Λ:=Bo
 main:=false
 σ:=Op G0
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype G0)
 m:=iY b d
def iu(l:Ls G0)(t:Ls (Op G0))(u:Ls G1):∀ k,Ls (FΓ G0 G1 k):=update (update (update (fun _=>[]) (some false) l) none t) (some true) u
lemma Cl(l:Ls G0)(t:Ls (Op G0))(u:Ls G1):iu l t u (some false)=l:=by unfold iu;rw[bD (by simp),bD (by simp),eW]
lemma Al(l:Ls G0)(t:Ls (Op G0))(u:Ls G1):iu l t u none=t:=by unfold iu;rw[bD (by simp),eW]
lemma Bg(l:Ls G0)(t:Ls (Op G0))(u:Ls G1):iu l t u (some true)=u:=by unfold iu;rw[eW]
lemma B4(l b:Ls G0)(t:Ls (Op G0))(u:Ls G1):update (iu l t u) (some false) b=iu b t u:=B6 _ (by simp) (by simp) _ _ _ _
lemma Ac(l:Ls G0)(t b:Ls (Op G0))(u:Ls G1):update (iu l t u) none b=iu l b u:=B5 _ (by simp) _ _ _ _
lemma Dy(l:Ls G0)(t:Ls (Op G0))(u b:Ls G1):update (iu l t u) (some true) b=iu l t b:=sE _ _ _
lemma DL(l:Ls G0):(iu l [] []:∀ k,Ls (FΓ G0 G1 k))=update (fun _=>[]:∀ k,Ls (FΓ G0 G1 k)) (some false) l:=by unfold iu;rw[Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr];{rw[bD (by simp)]};{rw[bD (by simp),bD (by simp)]}
lemma Bh(u:Ls G1):(iu [] [] u:∀ k,Ls (FΓ G0 G1 k))=update (fun _=>[]:∀ k,Ls (FΓ G0 G1 k)) (some true) u:=by unfold iu;congr 1;rw[Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr];{rfl};{rw[bD (by simp)]}
abbrev rJ(G0 G1:Type):Type:=TM2.Cfg (FΓ G0 G1) Bo (Op G0)
variable (f0_:G0->Op G1) (d:Op G1)
lemma Bj(b:Op G0)(x:G0)(l:Ls G0)(t:Ls (Op G0))(u:Ls G1):step (iY f0_ d) (⟨some false,b,iu (x::l) t u⟩:rJ G0 G1)=some ⟨some false,some x,iu l (some x::t) u⟩:=by simp only[step,iY,stepAux];rw[Cl];simp only[List.head?_cons,jF,ph,nW];rw[B4,Al,Ac]
lemma BP(b:Op G0)(t:Ls (Op G0))(u:Ls G1):step (iY f0_ d) (⟨some false,b,iu [] t u⟩:rJ G0 G1)=some ⟨some true,none,iu [] t u⟩:=by simp only[step,iY,stepAux];rw[Cl];simp only[List.head?_nil,px,pj,nT];rw[B4]
lemma Bi(hd:d=none->∀ x,f0_ x=none)(b:Op G0)(x:G0)(t:Ls (Op G0))(u:Ls G1):step (iY f0_ d) (⟨some true,b,iu [] (some x::t) u⟩:rJ G0 G1)=some ⟨some true,some x,iu [] t ((f0_ x).toList++u)⟩:=by
 simp only[step,iY,stepAux];rw[Al];simp only[List.head?_cons,jF,Option.join_some,ph,nW,Option.bind_some];rw[Ac];cases hφ:f0_ x with
 | none=>simp
 | some y=>cases d with|none=>{rw[hd rfl x] at hφ;exact absurd hφ (by simp)}|some c=>{simp only[ph,nW,stepAux,Option.toList_some,sw];rw[Bg,Dy];simp[hφ]}
lemma BO(b:Op G0)(u:Ls G1):step (iY f0_ d) (⟨some true,b,iu [] [] u⟩:rJ G0 G1)=some ⟨none,none,iu [] [] u⟩:=by simp only[step,iY,stepAux];rw[Al];simp only[List.head?_nil,px,Option.join_none,pj,nT];rw[Ac]
lemma BN(u:Ls G1):∀(l:Ls G0) (t:Ls (Op G0)) (b:Op G0),(flip bind (step (iY f0_ d)))^[l.length+1] (some (⟨some false,b,iu l t u⟩:rJ G0 G1))=some ⟨some true,none,iu [] (l.reverse.map some++t) u⟩:=by
 intro l;induction l with
 | nil=>intro t b;exact BP f0_ d b t u
 | cons x l c=>intro t b;rw[aX,eo];have e:flip bind (step (iY f0_ d)) (some (⟨some false,b,iu (x::l) t u⟩:rJ G0 G1))=some ⟨some false,some x,iu l (some x::t) u⟩:=Bj f0_ d b x l t u;rw[e,c];simp
lemma BM(hd:d=none->∀ x,f0_ x=none):∀(t:Ls G0) (u:Ls G1) (b:Op G0),(flip bind (step (iY f0_ d)))^[t.length+1] (some (⟨some true,b,iu [] (t.map some) u⟩:rJ G0 G1))=some ⟨none,none,iu [] [] ((t.filterMap f0_).reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro u b;exact BO f0_ d b u
 | cons x t c=>intro u b;rw[aX,eo];have e:flip bind (step (iY f0_ d)) (some (⟨some true,b,iu [] ((x::t).map some) u⟩:rJ G0 G1))=some ⟨some true,some x,iu [] (t.map some) ((f0_ x).toList++u)⟩:=Bi f0_ d hd b x (t.map some) u;rw[e,c];cases hφ:f0_ x <;> simp[hφ]
lemma zx[Fintype G0](hd:d=none->∀ x,f0_ x=none)(l:Ls G0):(flip bind (step (iY f0_ d)))^[l.length+1+(l.length+1)] (some (initList (fm f0_ d) l))=some (haltList (fm f0_ d) (l.filterMap f0_)):=by
 refine (aI (fun c=>(flip bind (step (iY f0_ d)))^[l.length+1+(l.length+1)] (some c)) (d4 (fm f0_ d) l)).trans (Eq.trans ?_ (aI some (d5 (fm f0_ d) (l.filterMap f0_))).symm);show (flip bind (step (iY f0_ d)))^[l.length+1+(l.length+1)] (some (⟨some false,none,update (fun _=>[]) (some false) l⟩:rJ G0 G1))=some (⟨none,none,update (fun _=>[]) (some true) (l.filterMap f0_)⟩:rJ G0 G1);rw[fq,<- DL,BN,<- Bh]
 have:=BM f0_ d hd l.reverse [] none
 rw[j2] at this;simpa[uU] using this
lemma d7{s r e b:Type}[Fintype e](i:s->Ls e)(q:r->Ls b)(f:s->r)(c:e->Op b)(h:∀ a,q (f a)=(i a).filterMap c):Nonempty (TM2ComputableInPolyTime i q f):=by
 classical
 let d:Op b:=if h:Nonempty b then some (Classical.choice h) else none
 have hd:d=none->∀ x,c x=none:=by
  intro o x;by_cases u:Nonempty b;{simp[d,u] at o}
  ·
   cases hφ:c x with|none=>{rfl}|some y=>{exact absurd ⟨y⟩ u}
 exact⟨{
  tm:=fm c d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2*Polynomial.X+Polynomial.C 2
  outputsFun:=fun a=>
   { steps:=(i a).length+1+((i a).length+1)
     evals_in_steps:=by
      have v:∀(j:Type) (l:Ls j),List.map (Equiv.refl j).invFun l=l:=fun j l=>by simp
      have:=zx c d hd (i a)
      exact (aI (fun l=>(flip bind (step (iY c d)))^[(i a).length+1+((i a).length+1)] (some (initList (fm c d) l))) (v e (i a))).trans (this.trans (aI (fun l=>some (haltList (fm c d) l)) ((h a).symm.trans (v b (q (f a))).symm)))
     steps_le_m:=by
      simp only[ly,pe,pn,pl];omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive z8:Type
 | inp|t1|t2|t3|out
 deriving DecidableEq
instance:Fintype z8:=Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x=>by cases x <;> simp)
inductive xr:Type
 | a|b|c|e
 deriving DecidableEq
instance:Fintype xr:=Fintype.ofList [.a,.b,.c,.e] (fun x=>by cases x <;> simp)
variable {G0 G1:Type}
abbrev wq(G0 G1:Type):z8->Type
 | .inp=>G0
 | .t1=>Op G0
 | .t2=>Op G0
 | .t3=>Op G0
 | .out=>G1
def yv(c:G0->Op G1)(d:Op G1)(b:xr):TM2.Stmt (wq G0 G1) xr (Op G0):=.branch (fun s=>(s.bind c).isSome) (match d with
     | some e=>.push .out (fun s=>(s.bind c).getD e) (.goto fun _=>b)
     | none=>.goto fun _=>b)
 (.goto fun _=>b)
def eQ(i h:G0->Op G1)(d:Op G1):xr->TM2.Stmt (wq G0 G1) xr (Op G0)
 | .a=>.pop .inp (fun _ o=>o) (.branch (fun s=>s.isSome) (.push .t1 (fun s=>s) (.goto fun _=>.a)) (.goto fun _=>.b))
 | .b=>.pop .t1 (fun _ o=>o.join) (.branch (fun s=>s.isSome) (.push .t2 (fun s=>s) (yv h d .b)) (.goto fun _=>.c))
 | .c=>.pop .t2 (fun _ o=>o.join) (.branch (fun s=>s.isSome) (.push .t3 (fun s=>s) (.goto fun _=>.c)) (.goto fun _=>.e))
 | .e=>.pop .t3 (fun _ o=>o.join) (.branch (fun s=>s.isSome) (yv i d .e) .halt)
def tp[Fintype G0](c b:G0->Op G1)(d:Op G1):FinTM2 where
 K:=z8
 k₀:=.inp
 k₁:=.out
 Γ:=wq G0 G1
 Λ:=xr
 main:=.a
 σ:=Op G0
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype G0)
 m:=eQ c b d
def f8(l:Ls G0)(a b c:Ls (Op G0))(u:Ls G1):∀ k,Ls (wq G0 G1 k)
 | .inp=>l
 | .t1=>a
 | .t2=>b
 | .t3=>c
 | .out=>u
lemma B8(l d:Ls G0)(a b c:Ls (Op G0))(u:Ls G1):update (f8 l a b c u) .inp d=f8 d a b c u:=by funext k;cases k <;> simp[f8]
lemma zh(l:Ls G0)(a d b c:Ls (Op G0))(u:Ls G1):update (f8 l a b c u) .t1 d=f8 l d b c u:=by funext k;cases k <;> simp[f8]
lemma zg(l:Ls G0)(a b d c:Ls (Op G0))(u:Ls G1):update (f8 l a b c u) .t2 d=f8 l a d c u:=by funext k;cases k <;> simp[f8]
lemma zf(l:Ls G0)(a b c d:Ls (Op G0))(u:Ls G1):update (f8 l a b c u) .t3 d=f8 l a b d u:=by funext k;cases k <;> simp[f8]
lemma B7(l:Ls G0)(a b c:Ls (Op G0))(u d:Ls G1):update (f8 l a b c u) .out d=f8 l a b c d:=by funext k;cases k <;> simp[f8]
lemma AO(l:Ls G0):(f8 l [] [] [] []:∀ k,Ls (wq G0 G1 k))=update (fun _=>[]:∀ k,Ls (wq G0 G1 k)) .inp l:=by funext k;cases k <;> simp[f8]
lemma BA(u:Ls G1):(f8 [] [] [] [] u:∀ k,Ls (wq G0 G1 k))=update (fun _=>[]:∀ k,Ls (wq G0 G1 k)) .out u:=by funext k;cases k <;> simp[f8]
abbrev iL(G0 G1:Type):Type:=TM2.Cfg (wq G0 G1) xr (Op G0)
variable (f1_ f2_:G0->Op G1) (d:Op G1)
lemma Bc(s:Op G0)(x:G0)(l:Ls G0)(a b c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .a,s,f8 (x::l) a b c u⟩:iL G0 G1)=some ⟨some .a,some x,f8 l (some x::a) b c u⟩:=by simp[step,eQ,stepAux,f8,B8,zh]
lemma Bz(s:Op G0)(a b c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .a,s,f8 [] a b c u⟩:iL G0 G1)=some ⟨some .b,none,f8 [] a b c u⟩:=by simp[step,eQ,stepAux,f8,B8]
lemma Bb(hd:d=none->∀ x,f2_ x=none)(s:Op G0)(x:G0)(a b c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .b,s,f8 [] (some x::a) b c u⟩:iL G0 G1)=some ⟨some .b,some x,f8 [] a (some x::b) c ((f2_ x).toList++u)⟩:=by
 cases hφ:f2_ x with
 | none=>
   cases d <;>
    simp[step,eQ,yv,stepAux,f8,zh,zg,hφ]
 | some y=>cases d with|none=>{rw[hd rfl x] at hφ;exact absurd hφ (by simp)}|some e=>{simp[step,eQ,yv,stepAux,f8,zh,zg,B7,hφ]}
lemma By(s:Op G0)(b c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .b,s,f8 [] [] b c u⟩:iL G0 G1)=some ⟨some .c,none,f8 [] [] b c u⟩:=by simp[step,eQ,stepAux,f8,zh]
lemma Ba(s:Op G0)(x:G0)(b c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .c,s,f8 [] [] (some x::b) c u⟩:iL G0 G1)=some ⟨some .c,some x,f8 [] [] b (some x::c) u⟩:=by simp[step,eQ,stepAux,f8,zg,zf]
lemma Bx(s:Op G0)(c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .c,s,f8 [] [] [] c u⟩:iL G0 G1)=some ⟨some .e,none,f8 [] [] [] c u⟩:=by simp[step,eQ,stepAux,f8,zg]
lemma A9(hd:d=none->∀ x,f1_ x=none)(s:Op G0)(x:G0)(c:Ls (Op G0))(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .e,s,f8 [] [] [] (some x::c) u⟩:iL G0 G1)=some ⟨some .e,some x,f8 [] [] [] c ((f1_ x).toList++u)⟩:=by
 cases hφ:f1_ x with
 | none=>
   cases d <;>
    simp[step,eQ,yv,stepAux,f8,zf,hφ]
 | some y=>cases d with|none=>{rw[hd rfl x] at hφ;exact absurd hφ (by simp)}|some b=>{simp[step,eQ,yv,stepAux,f8,zf,B7,hφ]}
lemma Bw(s:Op G0)(u:Ls G1):step (eQ f1_ f2_ d) (⟨some .e,s,f8 [] [] [] [] u⟩:iL G0 G1)=some ⟨none,none,f8 [] [] [] [] u⟩:=by simp[step,eQ,stepAux,f8,zf]
lemma Bv(b c:Ls (Op G0))(u:Ls G1):∀(l:Ls G0) (a:Ls (Op G0)) (s:Op G0),(flip bind (step (eQ f1_ f2_ d)))^[l.length+1] (some (⟨some .a,s,f8 l a b c u⟩:iL G0 G1))=some ⟨some .b,none,f8 [] (l.reverse.map some++a) b c u⟩:=by
 intro l;induction l with
 | nil=>intro a s;exact Bz f1_ f2_ d s a b c u
 | cons x l h=>intro a s;rw[aX,eo];have e:flip bind (step (eQ f1_ f2_ d)) (some (⟨some .a,s,f8 (x::l) a b c u⟩:iL G0 G1))=some ⟨some .a,some x,f8 l (some x::a) b c u⟩:=Bc f1_ f2_ d s x l a b c u;rw[e,h];simp
lemma Bu(hd:d=none->∀ x,f2_ x=none)(c:Ls (Op G0)):∀(t:Ls G0) (b:Ls (Op G0)) (u:Ls G1) (s:Op G0),(flip bind (step (eQ f1_ f2_ d)))^[t.length+1] (some (⟨some .b,s,f8 [] (t.map some) b c u⟩:iL G0 G1))=some ⟨some .c,none,f8 [] [] (t.reverse.map some++b) c ((t.filterMap f2_).reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro b u s;exact By f1_ f2_ d s b c u
 | cons x t h=>intro b u s;rw[aX,eo];have e:flip bind (step (eQ f1_ f2_ d)) (some (⟨some .b,s,f8 [] ((x::t).map some) b c u⟩:iL G0 G1))=some ⟨some .b,some x,f8 [] (t.map some) (some x::b) c ((f2_ x).toList++u)⟩:=Bb f1_ f2_ d hd s x (t.map some) b c u;rw[e,h];cases hφ:f2_ x <;> simp[hφ]
lemma Bt(u:Ls G1):∀(t:Ls G0) (c:Ls (Op G0)) (s:Op G0),(flip bind (step (eQ f1_ f2_ d)))^[t.length+1] (some (⟨some .c,s,f8 [] [] (t.map some) c u⟩:iL G0 G1))=some ⟨some .e,none,f8 [] [] [] (t.reverse.map some++c) u⟩:=by
 intro t;induction t with
 | nil=>intro c s;exact Bx f1_ f2_ d s c u
 | cons x t b=>intro c s;rw[aX,eo];have e:flip bind (step (eQ f1_ f2_ d)) (some (⟨some .c,s,f8 [] [] ((x::t).map some) c u⟩:iL G0 G1))=some ⟨some .c,some x,f8 [] [] (t.map some) (some x::c) u⟩:=Ba f1_ f2_ d s x (t.map some) c u;rw[e,b];simp
lemma Bs(hd:d=none->∀ x,f1_ x=none):∀(t:Ls G0) (u:Ls G1) (s:Op G0),(flip bind (step (eQ f1_ f2_ d)))^[t.length+1] (some (⟨some .e,s,f8 [] [] [] (t.map some) u⟩:iL G0 G1))=some ⟨none,none,f8 [] [] [] [] ((t.filterMap f1_).reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro u s;exact Bw f1_ f2_ d s u
 | cons x t b=>intro u s;rw[aX,eo];have e:flip bind (step (eQ f1_ f2_ d)) (some (⟨some .e,s,f8 [] [] [] ((x::t).map some) u⟩:iL G0 G1))=some ⟨some .e,some x,f8 [] [] [] (t.map some) ((f1_ x).toList++u)⟩:=A9 f1_ f2_ d hd s x (t.map some) u;rw[e,b];cases hφ:f1_ x <;> simp[hφ]
lemma zR[Fintype G0](i:d=none->∀ x,f1_ x=none)(h:d=none->∀ x,f2_ x=none)(l:Ls G0):(flip bind (step (eQ f1_ f2_ d)))^[l.length+1+(l.length+1)+(l.length+1)+(l.length+1)] (some (initList (tp f1_ f2_ d) l))=some (haltList (tp f1_ f2_ d) (l.filterMap f1_++l.filterMap f2_)):=by
 refine (aI (fun c=>(flip bind (step (eQ f1_ f2_ d)))^[l.length+1+(l.length+1)+(l.length+1)+(l.length+1)] (some c)) (d4 (tp f1_ f2_ d) l)).trans (Eq.trans ?_ (aI some (d5 (tp f1_ f2_ d) (l.filterMap f1_++l.filterMap f2_))).symm);show (flip bind (step (eQ f1_ f2_ d)))^[l.length+1+(l.length+1)+(l.length+1)+(l.length+1)] (some (⟨some .a,none,update (fun _=>[]) .inp l⟩:iL G0 G1))=some (⟨none,none,update (fun _=>[]) .out (l.filterMap f1_++l.filterMap f2_)⟩:iL G0 G1);have r:(flip bind (step (eQ f1_ f2_ d)))^[l.length+1] (some (⟨some .a,none,f8 l [] [] [] []⟩:iL G0 G1))=some ⟨some .b,none,f8 [] (l.reverse.map some) [] [] []⟩:=(by simpa using Bv f1_ f2_ d [] [] [] l [] none)
 have q:(flip bind (step (eQ f1_ f2_ d)))^[l.length+1] (some (⟨some .b,none,f8 [] (l.reverse.map some) [] [] []⟩:iL G0 G1))=some ⟨some .c,none,f8 [] [] (l.map some) [] (l.filterMap f2_)⟩:=by
  have:=Bu f1_ f2_ d h [] l.reverse [] [] none
  rw[j2] at this;simpa[uU] using this
 have o:(flip bind (step (eQ f1_ f2_ d)))^[l.length+1] (some (⟨some .c,none,f8 [] [] (l.map some) [] (l.filterMap f2_)⟩:iL G0 G1))=some ⟨some .e,none,f8 [] [] [] (l.reverse.map some) (l.filterMap f2_)⟩:=(by simpa using Bt f1_ f2_ d (l.filterMap f2_) l [] none)
 have j:(flip bind (step (eQ f1_ f2_ d)))^[l.length+1] (some (⟨some .e,none,f8 [] [] [] (l.reverse.map some) (l.filterMap f2_)⟩:iL G0 G1))=some ⟨none,none,f8 [] [] [] [] (l.filterMap f1_++l.filterMap f2_)⟩:=by
  have:=Bs f1_ f2_ d i l.reverse (l.filterMap f2_) none
  rw[j2] at this;simpa[uU] using this
 rw[fq,fq,fq,<- AO,r,q,o,j,BA]
lemma zb{v u c b:Type}[Fintype c](j:v->Ls c)(s:u->Ls b)(f:v->u)(i e:c->Op b)(h:∀ a,s (f a)=(j a).filterMap i++(j a).filterMap e):Nonempty (Turing.TM2ComputableInPolyTime j s f):=by
 classical
 let d:Op b:=if h:Nonempty b then some (Classical.choice h) else none
 have hd:∀ o:c->Op b,d=none->∀ x,o x=none:=by
  intro o r x;by_cases w:Nonempty b;{simp[d,w] at r}
  ·
   cases hφ:o x with|none=>{rfl}|some y=>{exact absurd ⟨y⟩ w}
 exact⟨{
  tm:=tp i e d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 4*Polynomial.X+Polynomial.C 4
  outputsFun:=fun a=>
   { steps:=(j a).length+1+((j a).length+1)+((j a).length+1) +
      ((j a).length+1)
     evals_in_steps:=by
      have z:∀(q:Type) (l:Ls q),List.map (Equiv.refl q).invFun l=l:=fun q l=>by simp
      have:=zR i e d (hd i) (hd e) (j a)
      exact (aI (fun l=>(flip bind (step (eQ i e d)))^[(j a).length+1+((j a).length+1)+((j a).length+1)+((j a).length+1)] (some (initList (tp i e d) l))) (z c (j a))).trans (this.trans (aI (fun l=>some (haltList (tp i e d) l)) ((h a).symm.trans (z b (s (f a))).symm)))
     steps_le_m:=by
      simp only[ly,pe,pn,pl];omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive FX
 | I|W|T|O
 deriving DecidableEq
instance:Fintype FX:=Fintype.ofList [FX.I,FX.W,FX.T,FX.O] (fun x=>by cases x <;> simp)
inductive FL
 | l1|l2|l3|l4|l5
 deriving DecidableEq
instance:Fintype FL:=Fintype.ofList [FL.l1,FL.l2,FL.l3,FL.l4,FL.l5] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev rK:M.K ⊕ FX->Type
 | inl k=>M.Γ k
 | inr FX.I=>Bo ⊕ Bo
 | inr FX.W=>Bo
 | inr FX.T=>Bo
 | inr FX.O=>Bo ⊕ Bo
abbrev wX:Type:=M.Λ ⊕ FL
abbrev wY:Type:=M.σ×Op (Bo ⊕ Bo)
def bit:Op (Bo ⊕ Bo)->Bo
 | none=>false
 | some (inl b)=>b
 | some (inr b)=>b
def tR:Op (Bo ⊕ Bo)->Bo
 | some (inl _)=>true
 | _=>false
variable {M}
def wT:TM2.Stmt M.Γ M.Λ M.σ->TM2.Stmt (rK M) (wX M) (wY M)
 | .push k f q=>.push (inl k) (fun s=>f s.1) (wT q)
 | .peek k f q=>.peek (inl k) (fun s o=>(f s.1 o,s.2)) (wT q)
 | .pop k f q=>.pop (inl k) (fun s o=>(f s.1 o,s.2)) (wT q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (wT q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (wT q₁) (wT q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr FL.l3)
variable (M)
def d0(c:Bo->M.Γ M.k₀)(b:M.Γ M.k₁->Bo):wX M->TM2.Stmt (rK M) (wX M) (wY M)
 | inl l=>wT (M.m l)
 | inr FL.l1=>.pop (inr FX.I) (fun s o=>(s.1,o)) (.branch (fun s=>s.2.isSome) (.branch (fun s=>tR s.2) (.push (inr FX.T) (fun s=>bit s.2) (.goto fun _=>inr FL.l1)) (.push (inr FX.W) (fun s=>bit s.2) (.goto fun _=>inr FL.l1))) (.goto fun _=>inr FL.l2))
 | inr FL.l2=>.pop (inr FX.T) (fun s o=>(s.1,o.map inl)) (.branch (fun s=>s.2.isSome) (.push (inl M.k₀) (fun s=>c (bit s.2)) (.goto fun _=>inr FL.l2)) (.goto fun _=>inl M.main))
 | inr FL.l3=>.pop (inr FX.W) (fun s o=>(s.1,o.map inl)) (.branch (fun s=>s.2.isSome) (.push (inr FX.O) (fun s=>inr (bit s.2)) (.goto fun _=>inr FL.l3)) (.goto fun _=>inr FL.l4))
 | inr FL.l4=>.pop (inl M.k₁) (fun s o=>(s.1,o.map fun y=>inl (b y))) (.branch (fun s=>s.2.isSome) (.push (inr FX.T) (fun s=>bit s.2) (.goto fun _=>inr FL.l4)) (.goto fun _=>inr FL.l5))
 | inr FL.l5=>.pop (inr FX.T) (fun s o=>(s.1,o.map inl)) (.branch (fun s=>s.2.isSome) (.push (inr FX.O) (fun s=>inl (bit s.2)) (.goto fun _=>inr FL.l5)) .halt)
def lM(c:Bo->M.Γ M.k₀)(b:M.Γ M.k₁->Bo):FinTM2:=
 haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ FX
   k₀:=inr FX.I
   k₁:=inr FX.O
   Γ:=rK M
   Λ:=wX M
   main:=inr FL.l1
   σ:=wY M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype (Bo ⊕ Bo))
   m:=d0 M c b }
variable {M}
def dH(b:∀ k,Ls (M.Γ k))(i:Ls (Bo ⊕ Bo))(w t:LB)(o:Ls (Bo ⊕ Bo)):∀ k,Ls (rK M k)
 | inl k=>b k
 | inr FX.I=>i
 | inr FX.W=>w
 | inr FX.T=>t
 | inr FX.O=>o
section dH
variable (S:∀ k,Ls (M.Γ k)) (i:Ls (Bo ⊕ Bo)) (w t:LB) (o:Ls (Bo ⊕ Bo))
lemma yQ(k:M.K)(x:Ls (M.Γ k)):update (dH S i w t o) (inl k) x=dH (update S k x) i w t o:=by
 funext j;rcases j with j|j
 {by_cases h:j=k;{subst h;rw[eW];show x=update S j x j;rw[eW]};{rw[bD (by simpa using h)];show S j=update S k x j;rw[bD h]}};{rw[bD (by simp)];cases j <;> rfl}
lemma zj(b:Ls (Bo ⊕ Bo)):update (dH S i w t o) (inr FX.I) b=dH S b w t o:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[eW];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl}
lemma Ah(b:LB):update (dH S i w t o) (inr FX.W) b=dH S i b t o:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[eW];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl}
lemma yt(b:LB):update (dH S i w t o) (inr FX.T) b=dH S i w b o:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[eW];rfl};{rw[bD (by simp)];rfl}
lemma Aj(b:Ls (Bo ⊕ Bo)):update (dH S i w t o) (inr FX.O) b=dH S i w t b:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[eW];rfl}
end dH
abbrev gj(M:FinTM2):Type:=TM2.Cfg (rK M) (wX M) (wY M)
def vw(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(w t:LB)(o:Ls (Bo ⊕ Bo))(c:TM2.Cfg M.Γ M.Λ M.σ):gj M:=⟨some (c.l.elim (inr FL.l3) inl),(c.var,b),dH c.stk i w t o⟩
lemma CX(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(w t:LB)(o:Ls (Bo ⊕ Bo))(q:TM2.Stmt M.Γ M.Λ M.σ)(v:M.σ)(c:∀ k,Ls (M.Γ k)):stepAux (wT q) ((v,b):wY M) (dH c i w t o)=vw b i w t o (stepAux q v c):=by
 induction q generalizing v c with
 | push k f q h=>
   have:=h v (update c k (f v::c k))
   rw[<- yQ] at this;exact this
 | peek k f q h=>exact h _ _
 | pop k f q h=>
   have:=h (f v (c k).head?) (update c k (c k).tail)
   rw[<- yQ] at this;exact this
 | load a q h=>exact h _ _
 | branch f r j e d=>simp only[wT,stepAux];cases f v;{exact d v c};{exact e v c}
 | goto f=>rfl
 | halt=>rfl
lemma AF(e:Bo->M.Γ M.k₀)(d:M.Γ M.k₁->Bo)(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(w t:LB)(o:Ls (Bo ⊕ Bo))(c j:TM2.Cfg M.Γ M.Λ M.σ)(h:step M.m c=some j):step (d0 M e d) (vw b i w t o c)=some (vw b i w t o j):=by
 obtain⟨l,v,q⟩:=c;cases l with
 | none=>simp[step] at h
 | some l=>simp only[step,ia] at h;subst h;exact aI some (CX b i w t o (M.m l) v q)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
lemma d6{σ:Type}(f:σ->Op σ){a b:Nat}{x y z:σ}(d:(flip bind f)^[a] (some x)=some y)(c:(flip bind f)^[b] (some y)=some z):(flip bind f)^[b+a] (some x)=some z:=by rw[fq,d,c]
variable {M:FinTM2} (e₀:Bo->M.Γ M.k₀) (e₁:M.Γ M.k₁->Bo)
section dH
variable (S:∀ k,Ls (M.Γ k)) (i:Ls (Bo ⊕ Bo)) (w t:LB) (o:Ls (Bo ⊕ Bo))
@[simp] lemma C5(k:M.K):dH S i w t o (inl k)=S k:=rfl
@[simp] lemma C4:dH S i w t o (inr FX.I)=i:=rfl
@[simp] lemma C8:dH S i w t o (inr FX.W)=w:=rfl
@[simp] lemma C7:dH S i w t o (inr FX.T)=t:=rfl
@[simp] lemma C6:dH S i w t o (inr FX.O)=o:=rfl
end dH
variable (v:M.σ) (S:∀ k,Ls (M.Γ k)) (w:LB) (o:Ls (Bo ⊕ Bo))
lemma zo(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l1),(v,b),dH S (inl a::i) w t o⟩:gj M)=some ⟨some (inr FL.l1),(v,some (inl a)),dH S i w (a::t) o⟩:=by simp[step,d0,stepAux,zj,yt,tR,bit]
lemma zq(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l1),(v,b),dH S (inr a::i) w t o⟩:gj M)=some ⟨some (inr FL.l1),(v,some (inr a)),dH S i (a::w) t o⟩:=by simp[step,d0,stepAux,zj,Ah,tR,bit]
lemma zr(b:Op (Bo ⊕ Bo))(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l1),(v,b),dH S [] w t o⟩:gj M)=some ⟨some (inr FL.l2),(v,none),dH S [] w t o⟩:=by simp[step,d0,stepAux,zj]
lemma Aq:∀(i:Ls (Bo ⊕ Bo)) (w t:LB) (b:Op (Bo ⊕ Bo)),(flip bind (step (d0 M e₀ e₁)))^[i.length+1] (some (⟨some (inr FL.l1),(v,b),dH S i w t o⟩:gj M))=some ⟨some (inr FL.l2),(v,none),dH S [] ((i.filterMap Sum.getRight?).reverse++w) ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i;induction i with
 | nil=>intro w t b;exact zr e₀ e₁ v S w o b t
 | cons x i c=>
   intro w t b;rw[aX,eo];cases x with
   | inl a=>have e:flip bind (step (d0 M e₀ e₁)) (some (⟨some (inr FL.l1),(v,b),dH S (inl a::i) w t o⟩:gj M))=some ⟨some (inr FL.l1),(v,some (inl a)),dH S i w (a::t) o⟩:=zo e₀ e₁ v S w o b a i t;rw[e,c];simp[pg]
   | inr a=>have e:flip bind (step (d0 M e₀ e₁)) (some (⟨some (inr FL.l1),(v,b),dH S (inr a::i) w t o⟩:gj M))=some ⟨some (inr FL.l1),(v,some (inr a)),dH S i (a::w) t o⟩:=zq e₀ e₁ v S w o b a i t;rw[e,c];simp[pg]
lemma BT(b:Op (Bo ⊕ Bo))(a:Bo)(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l2),(v,b),dH S [] w (a::t) o⟩:gj M)=some ⟨some (inr FL.l2),(v,some (inl a)),dH (update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=by simp[step,d0,stepAux,yt,yQ,bit]
lemma zt(b:Op (Bo ⊕ Bo)):step (d0 M e₀ e₁) (⟨some (inr FL.l2),(v,b),dH S [] w [] o⟩:gj M)=some ⟨some (inl M.main),(v,none),dH S [] w [] o⟩:=by simp[step,d0,stepAux,yt]
lemma Ar:∀(t:LB) (c:∀ k,Ls (M.Γ k)) (b:Op (Bo ⊕ Bo)),(flip bind (step (d0 M e₀ e₁)))^[t.length+1] (some (⟨some (inr FL.l2),(v,b),dH c [] w t o⟩:gj M))=some ⟨some (inl M.main),(v,none),dH (update c M.k₀ (t.reverse.map e₀++c M.k₀)) [] w [] o⟩:=by
 intro t;induction t with
 | nil=>
   intro c b;have:update c M.k₀ (([]:LB).reverse.map e₀++c M.k₀)=c:=by simp
   rw[this];exact zt e₀ e₁ v c w o b
 | cons a t d=>intro c b;rw[aX,eo];have e:flip bind (step (d0 M e₀ e₁)) (some (⟨some (inr FL.l2),(v,b),dH c [] w (a::t) o⟩:gj M))=some ⟨some (inr FL.l2),(v,some (inl a)),dH (update c M.k₀ (e₀ a::c M.k₀)) [] w t o⟩:=BT e₀ e₁ v c w o b a t;rw[e,d];simp
lemma BS(b:Op (Bo ⊕ Bo))(a:Bo)(w:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l3),(v,b),dH S [] (a::w) [] o⟩:gj M)=some ⟨some (inr FL.l3),(v,some (inl a)),dH S [] w [] (inr a::o)⟩:=by simp[step,d0,stepAux,Ah,Aj,bit]
lemma zu(b:Op (Bo ⊕ Bo)):step (d0 M e₀ e₁) (⟨some (inr FL.l3),(v,b),dH S [] [] [] o⟩:gj M)=some ⟨some (inr FL.l4),(v,none),dH S [] [] [] o⟩:=by simp[step,d0,stepAux,Ah]
lemma As:∀(w:LB) (o:Ls (Bo ⊕ Bo)) (b:Op (Bo ⊕ Bo)),(flip bind (step (d0 M e₀ e₁)))^[w.length+1] (some (⟨some (inr FL.l3),(v,b),dH S [] w [] o⟩:gj M))=some ⟨some (inr FL.l4),(v,none),dH S [] [] [] (w.reverse.map inr++o)⟩:=by
 intro w;induction w with
 | nil=>intro o b;exact zu e₀ e₁ v S o b
 | cons a w c=>intro o b;rw[aX,eo];have e:flip bind (step (d0 M e₀ e₁)) (some (⟨some (inr FL.l3),(v,b),dH S [] (a::w) [] o⟩:gj M))=some ⟨some (inr FL.l3),(v,some (inl a)),dH S [] w [] (inr a::o)⟩:=BS e₀ e₁ v S o b a w;rw[e,c];simp
lemma BR(b:Op (Bo ⊕ Bo))(y:M.Γ M.k₁)(m:Ls (M.Γ M.k₁))(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l4),(v,b),dH (update S M.k₁ (y::m)) [] [] t o⟩:gj M)=some ⟨some (inr FL.l4),(v,some (inl (e₁ y))),dH (update S M.k₁ m) [] [] (e₁ y::t) o⟩:=by simp[step,d0,stepAux,yt,yQ,bit]
lemma zv(b:Op (Bo ⊕ Bo))(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l4),(v,b),dH (update S M.k₁ []) [] [] t o⟩:gj M)=some ⟨some (inr FL.l5),(v,none),dH (update S M.k₁ []) [] [] t o⟩:=by simp[step,d0,stepAux,yQ]
lemma At:∀(m:Ls (M.Γ M.k₁)) (t:LB) (b:Op (Bo ⊕ Bo)),(flip bind (step (d0 M e₀ e₁)))^[m.length+1] (some (⟨some (inr FL.l4),(v,b),dH (update S M.k₁ m) [] [] t o⟩:gj M))=some ⟨some (inr FL.l5),(v,none),dH (update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
 intro m;induction m with
 | nil=>intro t b;exact zv e₀ e₁ v S o b t
 | cons y m c=>intro t b;rw[aX,eo];have e:flip bind (step (d0 M e₀ e₁)) (some (⟨some (inr FL.l4),(v,b),dH (update S M.k₁ (y::m)) [] [] t o⟩:gj M))=some ⟨some (inr FL.l4),(v,some (inl (e₁ y))),dH (update S M.k₁ m) [] [] (e₁ y::t) o⟩:=BR e₀ e₁ v S o b y m t;rw[e,c];simp
lemma BQ(b:Op (Bo ⊕ Bo))(a:Bo)(t:LB):step (d0 M e₀ e₁) (⟨some (inr FL.l5),(v,b),dH S [] [] (a::t) o⟩:gj M)=some ⟨some (inr FL.l5),(v,some (inl a)),dH S [] [] t (inl a::o)⟩:=by simp[step,d0,stepAux,yt,Aj,bit]
lemma zw(b:Op (Bo ⊕ Bo)):step (d0 M e₀ e₁) (⟨some (inr FL.l5),(v,b),dH S [] [] [] o⟩:gj M)=some ⟨none,(v,none),dH S [] [] [] o⟩:=by simp[step,d0,stepAux,yt]
lemma Au:∀(t:LB) (o:Ls (Bo ⊕ Bo)) (b:Op (Bo ⊕ Bo)),(flip bind (step (d0 M e₀ e₁)))^[t.length+1] (some (⟨some (inr FL.l5),(v,b),dH S [] [] t o⟩:gj M))=some ⟨none,(v,none),dH S [] [] [] (t.reverse.map inl++o)⟩:=by
 intro t;induction t with
 | nil=>intro o b;exact zw e₀ e₁ v S o b
 | cons a t c=>intro o b;rw[aX,eo];have e:flip bind (step (d0 M e₀ e₁)) (some (⟨some (inr FL.l5),(v,b),dH S [] [] (a::t) o⟩:gj M))=some ⟨some (inr FL.l5),(v,some (inl a)),dH S [] [] t (inl a::o)⟩:=BQ e₀ e₁ v S o b a t;rw[e,c];simp
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bo->M.Γ M.k₀) (e₁:M.Γ M.k₁->Bo)
lemma Ck:(dH (fun _=>[]) [] [] [] []:∀ k,Ls (rK M k))=fun _=>[]:=by funext j;rcases j with j|(_|_|_|_) <;> rfl
lemma DK(i:Ls (Bo ⊕ Bo)):(dH (fun _=>[]) i [] [] []:∀ k,Ls (rK M k))=update (fun _=>[]:∀ k,Ls (rK M k)) (inr FX.I) i:=(zj (fun _=>[]) [] [] [] [] i).symm.trans (by rw[Ck])
lemma DJ(o:Ls (Bo ⊕ Bo)):(dH (fun _=>[]) [] [] [] o:∀ k,Ls (rK M k))=update (fun _=>[]:∀ k,Ls (rK M k)) (inr FX.O) o:=(Aj (fun _=>[]) [] [] [] [] o).symm.trans (by rw[Ck])
lemma AU(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(w t:LB)(o:Ls (Bo ⊕ Bo))(l:Ls (M.Γ M.k₀)):vw b i w t o (initList M l)=(⟨some (inl M.main),(M.initialState,b),dH (update (fun _=>[]) M.k₀ l) i w t o⟩:gj M):=by rw[d4];rfl
lemma AV(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(w t:LB)(o:Ls (Bo ⊕ Bo))(m:Ls (M.Γ M.k₁)):vw b i w t o (haltList M m)=(⟨some (inr FL.l3),(M.initialState,b),dH (update (fun _=>[]) M.k₁ m) i w t o⟩:gj M):=by rw[d5];rfl
lemma BK{c b:Type}(l:Ls c):l.filterMap (fun _=>(none:Op b))=[]:=by induction l with|nil=>{rfl}|cons a l d=>{simp}
lemma BZ(x w:LB):(encodePair (x,w)).filterMap Sum.getLeft?=x:=by have c:(Sum.getLeft? ∘ (inl:Bo->Bo ⊕ Bo):Bo->Op Bo)=some:=rfl;have b:(Sum.getLeft? ∘ (inr:Bo->Bo ⊕ Bo):Bo->Op Bo)=fun _=>none:=rfl;simp only[encodePair,mG,List.filterMap_map,c,b,List.filterMap_some,BK,cR]
lemma BX(x w:LB):(encodePair (x,w)).filterMap Sum.getRight?=w:=by have c:(Sum.getRight? ∘ (inl:Bo->Bo ⊕ Bo):Bo->Op Bo)=fun _=>none:=rfl;have b:(Sum.getRight? ∘ (inr:Bo->Bo ⊕ Bo):Bo->Op Bo)=some:=rfl;simp only[encodePair,mG,List.filterMap_map,c,b,List.filterMap_some,BK,gl]
lemma d9(x w:LB):(encodePair (x,w)).length=x.length+w.length:=by simp[encodePair]
lemma AR(x b:LB)(m:Ls (M.Γ M.k₁))(s:Nat)(h:(flip bind (step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)):∃ n,n<=s+2*x.length+2*b.length+2*m.length+5/\(flip bind (step (d0 M e₀ e₁)))^[n] (some (initList (lM M e₀ e₁) (encodePair (x,b))))=some (haltList (lM M e₀ e₁) (encodePair (m.map e₁,b))):=by
 have q:(flip bind (step (d0 M e₀ e₁)))^[(encodePair (x,b)).length+1] (some (initList (lM M e₀ e₁) (encodePair (x,b))))=some (⟨some (inr FL.l2),(M.initialState,none),dH (fun _=>[]) [] b.reverse x.reverse []⟩:gj M):=by
  have:=Aq e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,b)) [] [] none
  rw[BZ,BX,cR,cR,DK] at this;exact (aI (fun c=>(flip bind (step (d0 M e₀ e₁)))^[ (encodePair (x,b)).length+1] (some c)) (d4 (lM M e₀ e₁) (encodePair (x,b)))).trans this
 have o:(flip bind (step (d0 M e₀ e₁)))^[x.reverse.length+1] (some (⟨some (inr FL.l2),(M.initialState,none),dH (fun _=>[]) [] b.reverse x.reverse []⟩:gj M))=some (vw none [] b.reverse [] [] (initList M (x.map e₀))):=by
  have:=Ar e₀ e₁ M.initialState b.reverse [] x.reverse (fun _=>[]) none
  rw[AU];simpa using this
 have d:=zm (step M.m) (step (d0 M e₀ e₁)) (vw none [] b.reverse [] []) (AF e₀ e₁ none [] b.reverse [] []) s _ _ h;rw[AV] at d
 have j:(flip bind (step (d0 M e₀ e₁)))^[b.reverse.length+1] (some (⟨some (inr FL.l3),(M.initialState,none),dH (update (fun _=>[]) M.k₁ m) [] b.reverse [] []⟩:gj M))=some (⟨some (inr FL.l4),(M.initialState,none),dH (update (fun _=>[]) M.k₁ m) [] [] [] (b.map inr)⟩:gj M):=by
  have:=As e₀ e₁ M.initialState (update (fun _=>[]) M.k₁ m) b.reverse [] none
  simpa using this
 have i:(flip bind (step (d0 M e₀ e₁)))^[m.length+1] (some (⟨some (inr FL.l4),(M.initialState,none),dH (update (fun _=>[]) M.k₁ m) [] [] [] (b.map inr)⟩:gj M))=some (⟨some (inr FL.l5),(M.initialState,none),dH (fun _=>[]) [] [] (m.reverse.map e₁) (b.map inr)⟩:gj M):=by
  have:=At e₀ e₁ M.initialState (fun _=>[]) (b.map inr) m [] none
  simpa using this
 have e:(flip bind (step (d0 M e₀ e₁)))^[(m.reverse.map e₁).length+1] (some (⟨some (inr FL.l5),(M.initialState,none),dH (fun _=>[]) [] [] (m.reverse.map e₁) (b.map inr)⟩:gj M))=some (haltList (lM M e₀ e₁) (encodePair (m.map e₁,b))):=by
  have:=Au e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (b.map inr) none
  rw[DJ] at this;refine this.trans (Eq.trans ?_ (aI some (d5 (lM M e₀ e₁) (encodePair (m.map e₁,b)))).symm);simp[encodePair];rfl
 refine⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ (d6 _ q o) d) j) i) e⟩;simp only[d9,j2,ft];omega
lemma Dl(f:LB->LB)(c:TM2ComputableInPolyTime (fun x:LB=>x) (fun x:LB=>x) f):Nonempty (TM2ComputableInPolyTime encodePair encodePair (fun p:LB×LB=>(f p.1,p.2))):=by
 let b:Bo->c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun;let d:c.tm.Γ c.tm.k₁->Bo:=c.outputAlphabet
 let T:Polynomial Nat:=
  c.time+Polynomial.C 2*(Polynomial.X+Polynomial.C (maxPush c.tm)*c.time)+Polynomial.C 2*Polynomial.X+Polynomial.C 5
 have e:∀ p:LB×LB,∃ n,n<=T.eval (encodePair p).length/\(flip bind (step (d0 c.tm b d)))^[n] (some (initList (lM c.tm b d) (encodePair p)))=some (haltList (lM c.tm b d) (encodePair (f p.1,p.2))):=by
  rintro⟨x,w⟩;have z:∃ s,s<=Polynomial.eval x.length c.time/\(flip bind (step c.tm.m))^[s] (some (initList c.tm (x.map b)))=some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))):=⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩;obtain⟨s,E,h⟩:=z;obtain⟨n,L,i⟩:=AR b d x w _ s h
  have o:(List.map c.outputAlphabet.invFun (f x)).map d=f x:=by
   rw[gm];conv_rhs=>rw[<- mN (f x)]
   exact dF fun y _=>c.outputAlphabet.right_inv y
  rw[o] at i;refine⟨n,L.trans ?_,i⟩;have v:=h;rw[d5,d4] at v;have j:=Cd c.tm c.tm.k₁ s _ _ v;simp only[eW,ft] at j;have K:((update (fun _=>[]:∀ k,Ls (c.tm.Γ k)) c.tm.k₀ (x.map b)) c.tm.k₁).length<=x.length:=(by by_cases u:c.tm.k₁=c.tm.k₀;{rw[u,eW,ft]};{rw[bD u];simp});have B:Polynomial.eval x.length c.time<=Polynomial.eval (x.length+w.length) c.time:=yS _ (by omega)
  have r:maxPush c.tm*s<=
   maxPush c.tm*Polynomial.eval (x.length+w.length) c.time:=
   lz _ (E.trans B)
  simp only[T,ly,pe,pn,pl,d9,ft];omega
 exact⟨{
  tm:=lM c.tm b d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun p=>
   { steps:=Classical.choose (e p)
     evals_in_steps:=by
      have o:∀(q:Type) (l:Ls q),List.map (Equiv.refl q).invFun l=l:=fun q l=>by simp
      exact (aI (fun l=>(flip bind (step (d0 c.tm b d)))^[ Classical.choose (e p)] (some (initList (lM c.tm b d) l))) (o _ (encodePair p))).trans ((f9 (e p)).2.trans (aI (fun l=>some (haltList (lM c.tm b d) l)) (o _ (encodePair (f p.1,p.2))).symm))
     steps_le_m:=(f9 (e p)).1 } }⟩
end Lib.Machines
end
section
namespace Lib.Machines.qB
open Turing
inductive IX
 | I|C|T|O
 deriving DecidableEq
instance:Fintype IX:=Fintype.ofList [IX.I,IX.C,IX.T,IX.O] (fun x=>by cases x <;> simp)
inductive IL
 | l1|l2|l3|l4|l5|l6
 deriving DecidableEq
instance:Fintype IL:=Fintype.ofList [IL.l1,IL.l2,IL.l3,IL.l4,IL.l5,IL.l6] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev vO:M.K ⊕ IX->Type
 | inl k=>M.Γ k
 | inr IX.I=>Bo ⊕ Bo
 | inr IX.C=>Bo
 | inr IX.T=>Bo
 | inr IX.O=>Bo
abbrev yG:Type:=M.Λ ⊕ IL
abbrev yH:Type:=M.σ×Op (Bo ⊕ Bo)
variable {M}
def wV:TM2.Stmt M.Γ M.Λ M.σ->TM2.Stmt (vO M) (yG M) (yH M)
 | .push k f q=>.push (inl k) (fun s=>f s.1) (wV q)
 | .peek k f q=>.peek (inl k) (fun s o=>(f s.1 o,s.2)) (wV q)
 | .pop k f q=>.pop (inl k) (fun s o=>(f s.1 o,s.2)) (wV q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (wV q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (wV q₁) (wV q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr IL.l4)
variable (M)
def d1(c:Bo->M.Γ M.k₀)(d:M.Γ M.k₀->Bo)(b:M.Γ M.k₁->Bo):yG M->TM2.Stmt (vO M) (yG M) (yH M)
 | inl l=>wV (M.m l)
 | inr IL.l1=>.pop (inr IX.I) (fun s o=>(s.1,o)) (.branch (fun s=>s.2.isSome) (.branch (fun s=>tR s.2) (.push (inr IX.T) (fun s=>bit s.2) (.goto fun _=>inr IL.l1)) (.push (inr IX.C) (fun s=>bit s.2) (.goto fun _=>inr IL.l1))) (.goto fun _=>inr IL.l2))
 | inr IL.l2=>.pop (inr IX.T) (fun s o=>(s.1,o.map inl)) (.branch (fun s=>s.2.isSome) (.push (inl M.k₀) (fun s=>c (bit s.2)) (.goto fun _=>inr IL.l2)) (.goto fun _=>inr IL.l3))
 | inr IL.l3=>.pop (inr IX.C) (fun s o=>(s.1,o.map inl)) (.branch (fun s=>s.2.isSome) (.goto fun _=>inl M.main) (.goto fun _=>inr IL.l5))
 | inr IL.l4=>.pop (inl M.k₁) (fun s o=>(s.1,o.map fun y=>inl (b y))) (.branch (fun s=>s.2.isSome) (.push (inr IX.T) (fun s=>bit s.2) (.goto fun _=>inr IL.l4)) (.goto fun _=>inr IL.l2))
 | inr IL.l5=>.pop (inl M.k₀) (fun s o=>(s.1,o.map fun y=>inl (d y))) (.branch (fun s=>s.2.isSome) (.push (inr IX.T) (fun s=>bit s.2) (.goto fun _=>inr IL.l5)) (.goto fun _=>inr IL.l6))
 | inr IL.l6=>.pop (inr IX.T) (fun s o=>(s.1,o.map inl)) (.branch (fun s=>s.2.isSome) (.push (inr IX.O) (fun s=>bit s.2) (.goto fun _=>inr IL.l6)) .halt)
def nf(c:Bo->M.Γ M.k₀)(d:M.Γ M.k₀->Bo)(b:M.Γ M.k₁->Bo):FinTM2:=
 haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ IX
   k₀:=inr IX.I
   k₁:=inr IX.O
   Γ:=vO M
   Λ:=yG M
   main:=inr IL.l1
   σ:=yH M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype (Bo ⊕ Bo))
   m:=d1 M c d b }
variable {M}
def dC(c:∀ k,Ls (M.Γ k))(i:Ls (Bo ⊕ Bo))(b t o:LB):∀ k,Ls (vO M k)
 | inl k=>c k
 | inr IX.I=>i
 | inr IX.C=>b
 | inr IX.T=>t
 | inr IX.O=>o
section dC
variable (S:∀ k,Ls (M.Γ k)) (i:Ls (Bo ⊕ Bo)) (cn t o:LB)
@[simp] lemma Db(k:M.K):dC S i cn t o (inl k)=S k:=rfl
@[simp] lemma Da:dC S i cn t o (inr IX.I)=i:=rfl
@[simp] lemma C9:dC S i cn t o (inr IX.C)=cn:=rfl
@[simp] lemma Dd:dC S i cn t o (inr IX.T)=t:=rfl
@[simp] lemma Dc:dC S i cn t o (inr IX.O)=o:=rfl
lemma xL(k:M.K)(x:Ls (M.Γ k)):update (dC S i cn t o) (inl k) x=dC (update S k x) i cn t o:=by
 funext j;rcases j with j|j
 {by_cases h:j=k;{subst h;rw[eW];show x=update S j x j;rw[eW]};{rw[bD (by simpa using h)];show S j=update S k x j;rw[bD h]}};{rw[bD (by simp)];cases j <;> rfl}
lemma zi(b:Ls (Bo ⊕ Bo)):update (dC S i cn t o) (inr IX.I) b=dC S b cn t o:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[eW];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl}
lemma Af(b:LB):update (dC S i cn t o) (inr IX.C) b=dC S i b t o:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[eW];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl}
lemma xK(b:LB):update (dC S i cn t o) (inr IX.T) b=dC S i cn b o:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[eW];rfl};{rw[bD (by simp)];rfl}
lemma Cf(b:LB):update (dC S i cn t o) (inr IX.O) b=dC S i cn t b:=by
 funext j;rcases j with j|(_|_|_|_)
 {rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[bD (by simp)];rfl};{rw[eW];rfl}
end dC
abbrev iq(M:FinTM2):Type:=TM2.Cfg (vO M) (yG M) (yH M)
def vx(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(d t o:LB)(c:TM2.Cfg M.Γ M.Λ M.σ):iq M:=⟨some (c.l.elim (inr IL.l4) inl),(c.var,b),dC c.stk i d t o⟩
lemma CY(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(s t o:LB)(q:TM2.Stmt M.Γ M.Λ M.σ)(v:M.σ)(c:∀ k,Ls (M.Γ k)):stepAux (wV q) ((v,b):yH M) (dC c i s t o)=vx b i s t o (stepAux q v c):=by
 induction q generalizing v c with
 | push k f q h=>
   have:=h v (update c k (f v::c k))
   rw[<- xL] at this;exact this
 | peek k f q h=>exact h _ _
 | pop k f q h=>
   have:=h (f v (c k).head?) (update c k (c k).tail)
   rw[<- xL] at this;exact this
 | load a q h=>exact h _ _
 | branch f r j e d=>simp only[wV,stepAux];cases f v;{exact d v c};{exact e v c}
 | goto f=>rfl
 | halt=>rfl
lemma AG(e:Bo->M.Γ M.k₀)(j:M.Γ M.k₀->Bo)(d:M.Γ M.k₁->Bo)(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(q t o:LB)(c r:TM2.Cfg M.Γ M.Λ M.σ)(h:step M.m c=some r):step (d1 M e j d) (vx b i q t o c)=some (vx b i q t o r):=by
 obtain⟨l,v,s⟩:=c;cases l with
 | none=>simp[step] at h
 | some l=>simp only[step,ia] at h;subst h;exact aI some (CY b i q t o (M.m l) v s)
lemma AS(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(c t o:LB)(l:Ls (M.Γ M.k₀)):vx b i c t o (initList M l)=(⟨some (inl M.main),(M.initialState,b),dC (update (fun _=>[]) M.k₀ l) i c t o⟩:iq M):=by rw[d4];rfl
lemma AT(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(c t o:LB)(m:Ls (M.Γ M.k₁)):vx b i c t o (haltList M m)=(⟨some (inr IL.l4),(M.initialState,b),dC (update (fun _=>[]) M.k₁ m) i c t o⟩:iq M):=by rw[d5];rfl
lemma Cj:(dC (fun _=>[]) [] [] [] []:∀ k,Ls (vO M k))=fun _=>[]:=by funext j;rcases j with j|(_|_|_|_) <;> rfl
lemma DI(i:Ls (Bo ⊕ Bo)):(dC (fun _=>[]) i [] [] []:∀ k,Ls (vO M k))=update (fun _=>[]:∀ k,Ls (vO M k)) (inr IX.I) i:=(zi (fun _=>[]) [] [] [] [] i).symm.trans (by rw[Cj])
lemma DH(o:LB):(dC (fun _=>[]) [] [] [] o:∀ k,Ls (vO M k))=update (fun _=>[]:∀ k,Ls (vO M k)) (inr IX.O) o:=(Cf (fun _=>[]) [] [] [] [] o).symm.trans (by rw[Cj])
end Lib.Machines.qB
end
section
namespace Lib.Machines.qB
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bo->M.Γ M.k₀) (d₀:M.Γ M.k₀->Bo) (e₁:M.Γ M.k₁->Bo)
variable (v:M.σ) (S:∀ k,Ls (M.Γ k))
lemma zz(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l1),(v,b),dC S (inl a::i) c t o⟩:iq M)=some ⟨some (inr IL.l1),(v,some (inl a)),dC S i c (a::t) o⟩:=by simp[step,d1,stepAux,zi,xK,tR,bit]
lemma zA(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l1),(v,b),dC S (inr a::i) c t o⟩:iq M)=some ⟨some (inr IL.l1),(v,some (inr a)),dC S i (a::c) t o⟩:=by simp[step,d1,stepAux,zi,Af,tR,bit]
lemma zB(b:Op (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l1),(v,b),dC S [] c t o⟩:iq M)=some ⟨some (inr IL.l2),(v,none),dC S [] c t o⟩:=by simp[step,d1,stepAux,zi]
lemma zH(o:LB):∀(i:Ls (Bo ⊕ Bo)) (c t:LB) (b:Op (Bo ⊕ Bo)),((flip bind (step (d1 M e₀ d₀ e₁))))^[i.length+1] (some (⟨some (inr IL.l1),(v,b),dC S i c t o⟩:iq M))=some ⟨some (inr IL.l2),(v,none),dC S [] ((i.filterMap Sum.getRight?).reverse++c) ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i;induction i with
 | nil=>intro c t b;exact zB e₀ d₀ e₁ v S b c t o
 | cons x i d=>
   intro c t b;rw[aX,eo];cases x with
   | inl a=>have e:(flip bind (step (d1 M e₀ d₀ e₁))) (some (⟨some (inr IL.l1),(v,b),dC S (inl a::i) c t o⟩:iq M))=some ⟨some (inr IL.l1),(v,some (inl a)),dC S i c (a::t) o⟩:=zz e₀ d₀ e₁ v S b a i c t o;rw[e,d];simp[pg]
   | inr a=>have e:(flip bind (step (d1 M e₀ d₀ e₁))) (some (⟨some (inr IL.l1),(v,b),dC S (inr a::i) c t o⟩:iq M))=some ⟨some (inr IL.l1),(v,some (inr a)),dC S i (a::c) t o⟩:=zA e₀ d₀ e₁ v S b a i c t o;rw[e,d];simp[pg]
lemma BI(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l2),(v,b),dC S i c (a::t) o⟩:iq M)=some ⟨some (inr IL.l2),(v,some (inl a)),dC (update S M.k₀ (e₀ a::S M.k₀)) i c t o⟩:=by simp[step,d1,stepAux,xK,xL,bit]
lemma zC(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(c o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l2),(v,b),dC S i c [] o⟩:iq M)=some ⟨some (inr IL.l3),(v,none),dC S i c [] o⟩:=by simp[step,d1,stepAux,xK]
lemma yc(i:Ls (Bo ⊕ Bo))(d o:LB):∀(t:LB) (c:∀ k,Ls (M.Γ k)) (b:Op (Bo ⊕ Bo)),((flip bind (step (d1 M e₀ d₀ e₁))))^[t.length+1] (some (⟨some (inr IL.l2),(v,b),dC c i d t o⟩:iq M))=some ⟨some (inr IL.l3),(v,none),dC (update c M.k₀ (t.reverse.map e₀++c M.k₀)) i d [] o⟩:=by
 intro t;induction t with
 | nil=>
   intro c b;have:update c M.k₀ (([]:LB).reverse.map e₀++c M.k₀)=c:=by simp
   rw[this];exact zC e₀ d₀ e₁ v c b i d o
 | cons a t h=>intro c b;rw[aX,eo];have e:(flip bind (step (d1 M e₀ d₀ e₁))) (some (⟨some (inr IL.l2),(v,b),dC c i d (a::t) o⟩:iq M))=some ⟨some (inr IL.l2),(v,some (inl a)),dC (update c M.k₀ (e₀ a::c M.k₀)) i d t o⟩:=BI e₀ d₀ e₁ v c b a i d t o;rw[e,h];simp
lemma BH(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l3),(v,b),dC S i (a::c) t o⟩:iq M)=some ⟨some (inl M.main),(v,some (inl a)),dC S i c t o⟩:=by simp[step,d1,stepAux,Af]
lemma zD(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l3),(v,b),dC S i [] t o⟩:iq M)=some ⟨some (inr IL.l5),(v,none),dC S i [] t o⟩:=by simp[step,d1,stepAux,Af]
lemma BG(b:Op (Bo ⊕ Bo))(y:M.Γ M.k₁)(m:Ls (M.Γ M.k₁))(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l4),(v,b),dC (update S M.k₁ (y::m)) i c t o⟩:iq M)=some ⟨some (inr IL.l4),(v,some (inl (e₁ y))),dC (update S M.k₁ m) i c (e₁ y::t) o⟩:=by simp[step,d1,stepAux,xK,xL,bit]
lemma zE(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l4),(v,b),dC (update S M.k₁ []) i c t o⟩:iq M)=some ⟨some (inr IL.l2),(v,none),dC (update S M.k₁ []) i c t o⟩:=by simp[step,d1,stepAux,xL]
lemma zI(i:Ls (Bo ⊕ Bo))(c o:LB):∀(m:Ls (M.Γ M.k₁)) (t:LB) (b:Op (Bo ⊕ Bo)),((flip bind (step (d1 M e₀ d₀ e₁))))^[m.length+1] (some (⟨some (inr IL.l4),(v,b),dC (update S M.k₁ m) i c t o⟩:iq M))=some ⟨some (inr IL.l2),(v,none),dC (update S M.k₁ []) i c (m.reverse.map e₁++t) o⟩:=by
 intro m;induction m with
 | nil=>intro t b;exact zE e₀ d₀ e₁ v S b i c t o
 | cons y m d=>intro t b;rw[aX,eo];have e:(flip bind (step (d1 M e₀ d₀ e₁))) (some (⟨some (inr IL.l4),(v,b),dC (update S M.k₁ (y::m)) i c t o⟩:iq M))=some ⟨some (inr IL.l4),(v,some (inl (e₁ y))),dC (update S M.k₁ m) i c (e₁ y::t) o⟩:=BG e₀ d₀ e₁ v S b y m i c t o;rw[e,d];simp
lemma BF(b:Op (Bo ⊕ Bo))(y:M.Γ M.k₀)(m:Ls (M.Γ M.k₀))(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l5),(v,b),dC (update S M.k₀ (y::m)) i c t o⟩:iq M)=some ⟨some (inr IL.l5),(v,some (inl (d₀ y))),dC (update S M.k₀ m) i c (d₀ y::t) o⟩:=by simp[step,d1,stepAux,xK,xL,bit]
lemma zF(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l5),(v,b),dC (update S M.k₀ []) i c t o⟩:iq M)=some ⟨some (inr IL.l6),(v,none),dC (update S M.k₀ []) i c t o⟩:=by simp[step,d1,stepAux,xL]
lemma zJ(i:Ls (Bo ⊕ Bo))(c o:LB):∀(m:Ls (M.Γ M.k₀)) (t:LB) (b:Op (Bo ⊕ Bo)),((flip bind (step (d1 M e₀ d₀ e₁))))^[m.length+1] (some (⟨some (inr IL.l5),(v,b),dC (update S M.k₀ m) i c t o⟩:iq M))=some ⟨some (inr IL.l6),(v,none),dC (update S M.k₀ []) i c (m.reverse.map d₀++t) o⟩:=by
 intro m;induction m with
 | nil=>intro t b;exact zF e₀ d₀ e₁ v S b i c t o
 | cons y m d=>intro t b;rw[aX,eo];have e:(flip bind (step (d1 M e₀ d₀ e₁))) (some (⟨some (inr IL.l5),(v,b),dC (update S M.k₀ (y::m)) i c t o⟩:iq M))=some ⟨some (inr IL.l5),(v,some (inl (d₀ y))),dC (update S M.k₀ m) i c (d₀ y::t) o⟩:=BF e₀ d₀ e₁ v S b y m i c t o;rw[e,d];simp
lemma BE(b:Op (Bo ⊕ Bo))(a:Bo)(i:Ls (Bo ⊕ Bo))(c t o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l6),(v,b),dC S i c (a::t) o⟩:iq M)=some ⟨some (inr IL.l6),(v,some (inl a)),dC S i c t (a::o)⟩:=by simp[step,d1,stepAux,xK,Cf,bit]
lemma zG(b:Op (Bo ⊕ Bo))(i:Ls (Bo ⊕ Bo))(c o:LB):step (d1 M e₀ d₀ e₁) (⟨some (inr IL.l6),(v,b),dC S i c [] o⟩:iq M)=some ⟨none,(v,none),dC S i c [] o⟩:=by simp[step,d1,stepAux,xK]
lemma zK(i:Ls (Bo ⊕ Bo))(c:LB):∀(t o:LB) (b:Op (Bo ⊕ Bo)),((flip bind (step (d1 M e₀ d₀ e₁))))^[t.length+1] (some (⟨some (inr IL.l6),(v,b),dC S i c t o⟩:iq M))=some ⟨none,(v,none),dC S i c [] (t.reverse++o)⟩:=by
 intro t;induction t with
 | nil=>intro o b;exact zG e₀ d₀ e₁ v S b i c o
 | cons a t d=>intro o b;rw[aX,eo];have e:(flip bind (step (d1 M e₀ d₀ e₁))) (some (⟨some (inr IL.l6),(v,b),dC S i c (a::t) o⟩:iq M))=some ⟨some (inr IL.l6),(v,some (inl a)),dC S i c t (a::o)⟩:=BE e₀ d₀ e₁ v S b a i c t o;rw[e,d];simp
lemma B0(k:M.K):update (fun _=>[]:∀ k,Ls (M.Γ k)) k []=fun _=>[]:=Function.update_eq_self k (fun _=>[]:∀ k,Ls (M.Γ k))
end Lib.Machines.qB
end
section
namespace Lib.Machines.qB
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bo->M.Γ M.k₀) (d₀:M.Γ M.k₀->Bo) (e₁:M.Γ M.k₁->Bo)
lemma Ds(g:LB->LB)(p:Polynomial Nat)(hd:∀ a,d₀ (e₀ a)=a)(q:∀ z:LB,∃(s:Nat) (m:Ls (M.Γ M.k₁)),s<=p.eval z.length/\(flip bind (step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)/\m.map e₁=g z):∀(c z:LB) (L:Nat) (b:Op (Bo ⊕ Bo)),(∀ j≤c.length,(g^[j] z).length<=L)->∃ n,n<=c.length*(p.eval L+2*L+3)+2*L+3/\((flip bind (step (d1 M e₀ d₀ e₁))))^[n] (some (⟨some (inr IL.l3),(M.initialState,b),dC (update (fun _=>[]) M.k₀ (z.map e₀)) [] c [] []⟩:iq M))=some ⟨none,(M.initialState,none),dC (fun _=>[]) [] [] [] (g^[c.length] z)⟩:=by
 intro c;induction c with
 | nil=>
   intro z L b d
   have y:((z.map e₀).reverse.map d₀).reverse=z:=by
    rw[j3,g0,gm];conv_rhs=>rw[<- mN z]
    exact dF fun a _=>hd a
   have u:((flip bind (step (d1 M e₀ d₀ e₁))))^[1] (some (⟨some (inr IL.l3),(M.initialState,b),dC (update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:iq M))=some ⟨some (inr IL.l5),(M.initialState,none),dC (update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:=zD e₀ d₀ e₁ M.initialState _ b [] [] [];have i:=zJ e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none;rw[B0,cR] at i;have h:=zK e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] ((z.map e₀).reverse.map d₀) [] none;rw[cR,y] at h;refine⟨_,?_,d6 _ (d6 _ u i) h⟩;have o:z.length<=L:=d 0 (Nat.zero_le _);simp only[j2,ft,mL] at o ⊢;omega
 | cons a c x=>
   intro z L b d;obtain⟨s,m,K,E,r⟩:=q z;rw[aX] at d;have o:z.length<=L:=d 0 (Nat.zero_le _);have a3:(g z).length<=L:=d 1 (by omega);have a1:m.length=(g z).length:=(by rw[<- r,ft]);have u:((flip bind (step (d1 M e₀ d₀ e₁))))^[1] (some (⟨some (inr IL.l3),(M.initialState,b),dC (update (fun _=>[]) M.k₀ (z.map e₀)) [] (a::c) [] []⟩:iq M))=some (vx (some (inl a)) [] c [] [] (initList M (z.map e₀))):=(by rw[AS];exact BH e₀ d₀ e₁ M.initialState _ b a [] c [] [])
   have i:=zm (step M.m) (step (d1 M e₀ d₀ e₁)) (vx (some (inl a)) [] c [] []) (AG e₀ d₀ e₁ (some (inl a)) [] c [] [])
    s _ _ E
   rw[AT] at i;have h:=zI e₀ d₀ e₁ M.initialState (fun _=>[]) [] c [] m [] (some (inl a));rw[B0,cR,j3,r] at h;have v:=yc e₀ d₀ e₁ M.initialState [] c [] (g z).reverse (fun _=>[]) none;rw[cR,g0] at v;obtain⟨n,B,w⟩:=x (g z) L none (fun j Q=>by
    have:=d (j+1) (by omega)
    rwa [eo] at this)
   have e:g^[(a::c).length] z=g^[c.length] (g z):=eo g _ z;rw[e];refine⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ u i) h) v) w⟩;have P:p.eval z.length<=p.eval L:=yS p (by omega);rw[j2,aX,qU];generalize c.length*(p.eval L+2*L+3)=S at B ⊢;omega
lemma Ch(g:LB->LB)(p:Polynomial Nat)(hd:∀ a,d₀ (e₀ a)=a)(b:∀ z:LB,∃(s:Nat) (m:Ls (M.Γ M.k₁)),s<=p.eval z.length/\(flip bind (step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)/\m.map e₁=g z)(y u:LB)(L:Nat)(q:∀ j≤u.length,(g^[j] y).length<=L):∃ n,n<=u.length*(p.eval L+2*L+3)+2*L+2*y.length+u.length+5/\((flip bind (step (d1 M e₀ d₀ e₁))))^[n] (some (initList (nf M e₀ d₀ e₁) (encodePair (y,u))))=some (haltList (nf M e₀ d₀ e₁) (g^[u.length] y)):=by
 have i:((flip bind (step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some (initList (nf M e₀ d₀ e₁) (encodePair (y,u))))=some (⟨some (inr IL.l2),(M.initialState,none),dC (fun _=>[]) [] u.reverse y.reverse []⟩:iq M):=by
  have:=zH e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none
  rw[BZ,BX,cR,cR,DI] at this;exact (aI (fun c=>((flip bind (step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c)) (d4 (nf M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have h:=yc e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none;rw[cR,g0] at h;obtain⟨n,o,e⟩:=Ds e₀ d₀ e₁ g p hd b u.reverse y L none (by rw[j2];exact q);rw[j2] at o e;rw[DH] at e;have d:((flip bind (step (d1 M e₀ d₀ e₁))))^[n] (some (⟨some (inr IL.l3),(M.initialState,none),dC (update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:iq M))=some (haltList (nf M e₀ d₀ e₁) (g^[u.length] y)):=e.trans (aI some (d5 (nf M e₀ d₀ e₁) (g^[u.length] y))).symm;refine⟨_,?_,d6 _ (d6 _ i h) d⟩;rw[d9,j2];omega
lemma Dg(g:LB->LB)(m:LB->Nat)(d:∀ y:LB,m (g y)<=m y)(e:∀ y:LB,(g y).length<=y.length+m y)(y:LB):∀ j:Nat,m (g^[j] y)<=m y/\(g^[j] y).length<=y.length+j*m y:=by
 intro j;induction j with
 | zero=>simp
 | succ j b=>rw[jb,qU];have o:=d (g^[j] y);have i:=e (g^[j] y);obtain⟨h,c⟩:=b;generalize j*m y=q at c ⊢;exact⟨by omega,by omega⟩
lemma Dr(d c L b y u:Nat)(e:L<=b)(h:d<=c):d+2*L+2*y+u+5<=c+2*b+3*(y+u)+5:=by omega
lemma lP(g:LB->LB)(c:Turing.TM2ComputableInPolyTime (fun x:LB=>x) (fun x:LB=>x) g)(m:LB->Nat)(a:Nat)(v:∀ y:LB,m (g y)<=m y)(K:∀ y:LB,(g y).length<=y.length+m y)(M:∀ y:LB,m y<=a*y.length+a):Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>g^[p.2.length] p.1)):=by
 let b:Bo->c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun;let e:c.tm.Γ c.tm.k₀->Bo:=c.inputAlphabet;let d:c.tm.Γ c.tm.k₁->Bo:=c.outputAlphabet
 let W:Polynomial Nat:=
  Polynomial.X+Polynomial.X*(Polynomial.C a*Polynomial.X+Polynomial.C a)
 let T:Polynomial Nat:=
  Polynomial.X*(c.time.comp W+Polynomial.C 2*W+Polynomial.C 3)+Polynomial.C 2*W+Polynomial.C 3*Polynomial.X+Polynomial.C 5
 have hd:∀ a,e (b a)=a:=fun a=>c.inputAlphabet.right_inv a
 have i:∀ z:LB,∃(s:Nat) (m:Ls (c.tm.Γ c.tm.k₁)),s<=c.time.eval z.length/\(flip bind (step c.tm.m))^[s] (some (initList c.tm (z.map b)))=some (haltList c.tm m)/\m.map d=g z:=by
  intro z;refine⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),(c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩;rw[gm];conv_rhs=>rw[<- mN (g z)]
  exact dF fun y _=>c.outputAlphabet.right_inv y
 have h:∀ q:LB×LB,∃ n,n<=T.eval (encodePair q).length/\(flip bind (step (d1 c.tm b e d)))^[n] (some (initList (nf c.tm b e d) (encodePair q)))=some (haltList (nf c.tm b e d) (g^[q.2.length] q.1)):=(by rintro⟨y,u⟩;have P:∀ j≤u.length,(g^[j] y).length<=y.length+u.length*(a*y.length+a):=(by intro j E;have h1:=(Dg g m v K y j).2;have S:j*m y<=u.length*(a*y.length+a):=nL E (M y);omega);obtain⟨n,B,L⟩:=Ch b e d g c.time hd i y u (y.length+u.length*(a*y.length+a)) P;have r:y.length+u.length*(a*y.length+a)<=(y.length+u.length)+(y.length+u.length)*(a*(y.length+u.length)+a):=Nat.add_le_add (by omega) (nL (by omega) (Nat.add_le_add_right (lz _ (by omega)) _));have Q:=yS c.time r;have o:u.length*(Polynomial.eval (y.length+u.length*(a*y.length+a)) c.time+2*(y.length+u.length*(a*y.length+a))+3)<=(y.length+u.length)*(Polynomial.eval ((y.length+u.length)+(y.length+u.length)*(a*(y.length+u.length)+a)) c.time+2*((y.length+u.length)+(y.length+u.length)*(a*(y.length+u.length)+a))+3):=nL (by omega) (by omega);refine⟨n,B.trans ?_,L⟩;simp only[T,W,ly,pe,pn,pl,Polynomial.eval_comp,d9];exact Dr _ _ _ _ _ _ r o);exact⟨{
  tm:=nf c.tm b e d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun q=>
   { steps:=Classical.choose (h q)
     evals_in_steps:=by
      have v:∀(w:Type) (l:Ls w),List.map (Equiv.refl w).invFun l=l:=fun w l=>by simp
      exact (aI (fun l=>(flip bind (step (d1 c.tm b e d)))^[ Classical.choose (h q)] (some (initList (nf c.tm b e d) l))) (v _ (encodePair q))).trans ((f9 (h q)).2.trans (aI (fun l=>some (haltList (nf c.tm b e d) l)) (v _ (g^[q.2.length] q.1)).symm))
     steps_le_m:=(f9 (h q)).1 } }⟩
lemma oq(g:LB->LB)(c:TM2ComputableInPolyTime (fun x:LB=>x) (fun x:LB=>x) g)(k:Nat)(b:∀ y:LB,(g y).length<=y.length+k):ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>g^[p.2.length] p.1):=lP g c (fun _=>k) k (fun _=>le_rfl) b (fun _=>Nat.le_add_left k _)
end Lib.Machines.qB
end
section
namespace Lib.Machines
open PEqualNP.Library
private lemma d2{c i e:Type}(h:c->i)(b:i->Op e)(g:c->e)(d:∀ a,b (h a)=some (g a))(l:Ls c):(l.map h).filterMap b=l.map g:=by induction l with|nil=>{rfl}|cons a l j=>{simp[d,j]}
private lemma d8{e d i:Type}(h:e->d)(b:d->Op i)(c:∀ a,b (h a)=none)(l:Ls e):(l.map h).filterMap b=[]:=by induction l with|nil=>{rfl}|cons a l j=>{simp[c,j]}
lemma aH{q e o d c b:Type}{j:q->Ls d}{i:e->Ls c}{h:o->Ls b}{f:q->e}{g:e->o}(s:ComputableInPolyTime j i f)(r:ComputableInPolyTime i h g):ComputableInPolyTime j h (fun a=>g (f a)):=by obtain⟨v⟩:=s;obtain⟨u⟩:=r;exact Dw j i h f g v u
lemma Am:ComputableInPolyTime encodePair encodePair (fun p:LB×LB=>(p.2,p.1)):=by refine zb _ _ _ (fun s:Bo ⊕ Bo=>Sum.elim (fun _=>none) (fun b=>some (inl b)) s) (fun s:Bo ⊕ Bo=>Sum.elim (fun b=>some (inr b)) (fun _=>none) s) ?_;rintro⟨x,w⟩;simp only[encodePair,mG];rw[d8 inl _ (fun _=>rfl) x,d2 inr _ inl (fun _=>rfl) w,d2 inl _ inr (fun _=>rfl) x,d8 inr _ (fun _=>rfl) w];simp
lemma BW:ComputableInPolyTime (fun x:LB=>x) encodePair (fun x:LB=>(x,x)):=by
 refine zb _ _ _ (fun b:Bo=>some (inl b)) (fun b:Bo=>some (inr b)) ?_;intro x
 have d:=d2 (fun b:Bo=>b) (fun b:Bo=>some (inl (β:=Bo) b))
  inl (fun _=>rfl) x
 have c:=d2 (fun b:Bo=>b) (fun b:Bo=>some (inr (α:=Bo) b))
  inr (fun _=>rfl) x
 simp only[List.map_id'] at d c;simp only[encodePair,d,c]
lemma BV:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>p.1):=by refine d7 _ _ _ (fun s:Bo ⊕ Bo=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_;rintro⟨x,w⟩;simp only[encodePair,mG];rw[d2 inl _ (fun b=>b) (fun _=>rfl) x,d8 inr _ (fun _=>rfl) w];simp
lemma BU:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>p.2):=by refine d7 _ _ _ (fun s:Bo ⊕ Bo=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_;rintro⟨x,w⟩;simp only[encodePair,mG];rw[d8 inl _ (fun _=>rfl) x,d2 inr _ (fun b=>b) (fun _=>rfl) w];simp
lemma Cg:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>p.1++p.2):=by refine d7 _ _ _ (fun s:Bo ⊕ Bo=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_;rintro⟨x,w⟩;simp only[encodePair,mG];rw[d2 inl _ (fun b=>b) (fun _=>rfl) x,d2 inr _ (fun b=>b) (fun _=>rfl) w];simp
lemma zk{f:LB->LB}(b:U f):ComputableInPolyTime encodePair encodePair (fun p:LB×LB=>(f p.1,p.2)):=by obtain⟨c⟩:=b;exact Dl f c
lemma AJ{g:LB->LB}(b:U g):ComputableInPolyTime encodePair encodePair (fun p:LB×LB=>(p.1,g p.2)):=aH (aH Am (zk b)) Am
lemma kv{f g:LB->LB}(c:U f)(b:U g):ComputableInPolyTime (fun x:LB=>x) encodePair (fun x:LB=>(f x,g x)):=aH (aH BW (AJ b)) (zk c)
lemma aR:U (fun x:LB=>x):=by refine d7 _ _ _ (fun b:Bo=>some b) ?_;intro x;have h:=d2 (fun b:Bo=>b) (fun b:Bo=>some b) (fun b=>b) (fun _=>rfl) x;simp only[List.map_id'] at h;exact h.symm
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def cL{h e c:Type}(d:c->h->c×Op e)(b:c->Op e):c->Ls h->Ls e
 | q,[]=>(b q).toList
 | q,a::l=>(d q a).2.toList++cL d b (d q a).1 l
def iB{h e d:Type}(c:d->h->d×Op e×Op e)(b:d->Op e):d->Ls h->Ls e
 | q,[]=>(b q).toList
 | q,a::l=>(c q a).2.1.toList++(c q a).2.2.toList++iB c b (c q a).1 l
lemma Dh{h e c:Type}(d:c->h->c×Op e)(b:c->Op e)(q:c)(l:Ls h):cL d b q l=iB (fun q a=>((d q a).1,(d q a).2,none)) b q l:=by induction l generalizing q with|nil=>{rfl}|cons a l i=>{simp[cL,iB,i]}
inductive z9:Type
 | inp|tmp|out
 deriving DecidableEq
instance:Fintype z9:=Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {G0 G1 Q:Type}
abbrev uj(G0 G1 Q:Type):z9->Type
 | .inp=>G0
 | .tmp=>Q×Op G0
 | .out=>G1
abbrev rZ(G0 Q:Type):Type:=Q×Op G0×Bo
def yi(c:Q->G0->Q×Op G1×Op G1)(b:Q->Op G1):Q×Op G0->Op G1
 | (q,some a)=>(c q a).2.1
 | (q,none)=>b q
def yj(b:Q->G0->Q×Op G1×Op G1):Q×Op G0->Op G1
 | (q,some a)=>(b q a).2.2
 | (_,none)=>none
def ss(c:Q->G0->Q×Op G1×Op G1)(b:Q->Op G1)(e:Q×Op G0):Ls G1:=(yi c b e).toList++(yj c e).toList
def vr(b:Q->G0->Q×Op G1×Op G1):Q->Ls G0->Ls (Q×Op G0)
 | q,[]=>[(q,none)]
 | q,a::l=>(q,some a)::vr b (b q a).1 l
lemma Dj(b:Q->G0->Q×Op G1×Op G1)(q:Q)(l:Ls G0):(vr b q l).length=l.length+1:=by induction l generalizing q with|nil=>{rfl}|cons a l c=>{simp[vr,c]}
lemma DA(c:Q->G0->Q×Op G1×Op G1)(b:Q->Op G1)(q:Q)(l:Ls G0):(vr c q l).flatMap (ss c b)=iB c b q l:=by induction l generalizing q with|nil=>{simp[vr,ss,yi,yj,iB]}|cons a l d=>{simp[vr,ss,yi,yj,iB,d]}
def yT(o:rZ G0 Q->Op G1)(d:Op G1)(next:TM2.Stmt (uj G0 G1 Q) Bo (rZ G0 Q)):TM2.Stmt (uj G0 G1 Q) Bo (rZ G0 Q):=.branch (fun s=>(o s).isSome) (match d with
     | some b=>.push .out (fun s=>(o s).getD b) next
     | none=>next)
 next
def ip(c:Q->G0->Q×Op G1×Op G1)(h:Q->Op G1)(b:Q)(d:Op G1):Bo->TM2.Stmt (uj G0 G1 Q) Bo (rZ G0 Q)
 | false=>
   .pop .inp (fun s o=>(s.1,o,o.isSome)) (.branch (fun s=>s.2.2) (.push .tmp (fun s=>(s.1,s.2.1)) (.load (fun s=>(match s.2.1 with
          | some a=>(c s.1 a).1
          | none=>s.1,none,false))
          (.goto fun _=>false)))
     (.push .tmp (fun s=>(s.1,none)) (.load (fun _=>(b,none,false)) (.goto fun _=>true))))
 | true=>
   .pop .tmp (fun _ o=>match o with
     | some e=>(e.1,e.2,true)
     | none=>(b,none,false))
     (.branch (fun s=>s.2.2) (yT (fun s=>yj c (s.1,s.2.1)) d (yT (fun s=>yi c h (s.1,s.2.1)) d (.goto fun _=>true))) .halt)
def xU[Fintype G0][Fintype Q](e:Q->G0->Q×Op G1×Op G1)(c:Q->Op G1)(b:Q)(d:Op G1):FinTM2 where
 K:=z9
 k₀:=.inp
 k₁:=.out
 Γ:=uj G0 G1 Q
 Λ:=Bo
 main:=false
 σ:=rZ G0 Q
 initialState:=(b,none,false)
 Γk₀Fin:=inferInstanceAs (Fintype G0)
 m:=ip e c b d
def gH(l:Ls G0)(t:Ls (Q×Op G0))(u:Ls G1):∀ k,Ls (uj G0 G1 Q k)
 | .inp=>l
 | .tmp=>t
 | .out=>u
lemma B2(l b:Ls G0)(t:Ls (Q×Op G0))(u:Ls G1):update (gH l t u) .inp b=gH b t u:=by funext k;cases k <;> simp[gH]
lemma ze(l:Ls G0)(t b:Ls (Q×Op G0))(u:Ls G1):update (gH l t u) .tmp b=gH l b u:=by funext k;cases k <;> simp[gH]
lemma Dx(l:Ls G0)(t:Ls (Q×Op G0))(u b:Ls G1):update (gH l t u) .out b=gH l t b:=by funext k;cases k <;> simp[gH]
lemma DC(l:Ls G0):(gH l [] []:∀ k,Ls (uj G0 G1 Q k))=update (fun _=>[]:∀ k,Ls (uj G0 G1 Q k)) .inp l:=by funext k;cases k <;> simp[gH]
lemma A6(u:Ls G1):(gH [] [] u:∀ k,Ls (uj G0 G1 Q k))=update (fun _=>[]:∀ k,Ls (uj G0 G1 Q k)) .out u:=by funext k;cases k <;> simp[gH]
abbrev m7(G0 G1 Q:Type):Type:=TM2.Cfg (uj G0 G1 Q) Bo (rZ G0 Q)
lemma BY(o:rZ G0 Q->Op G1)(d:Op G1)(hd:∀ _:G1,d≠none)(next:TM2.Stmt (uj G0 G1 Q) Bo (rZ G0 Q))(s:rZ G0 Q)(l:Ls G0)(t:Ls (Q×Op G0))(u:Ls G1):stepAux (yT o d next) s (gH l t u)=stepAux next s (gH l t ((o s).toList++u)):=by
 cases ho:o s with
 | none=>cases d <;> simp[yT,stepAux,ho]
 | some y=>cases d with|none=>{exact absurd rfl (hd y)}|some b=>{simp[yT,stepAux,ho,gH,Dx]}
variable (δ:Q->G0->Q×Op G1×Op G1) (fin:Q->Op G1) (q₀:Q) (d:Op G1)
lemma A8(s:rZ G0 Q)(a:G0)(l:Ls G0)(t:Ls (Q×Op G0))(u:Ls G1):step (ip δ fin q₀ d) (⟨some false,s,gH (a::l) t u⟩:m7 G0 G1 Q)=some ⟨some false,((δ s.1 a).1,none,false),gH l ((s.1,some a)::t) u⟩:=by simp[step,ip,stepAux,gH,B2,ze]
lemma Br(s:rZ G0 Q)(t:Ls (Q×Op G0))(u:Ls G1):step (ip δ fin q₀ d) (⟨some false,s,gH [] t u⟩:m7 G0 G1 Q)=some ⟨some true,(q₀,none,false),gH [] ((s.1,none)::t) u⟩:=by simp[step,ip,stepAux,gH,B2,ze]
lemma A7(hd:∀ _:G1,d≠none)(s:rZ G0 Q)(e:Q×Op G0)(t:Ls (Q×Op G0))(u:Ls G1):step (ip δ fin q₀ d) (⟨some true,s,gH [] (e::t) u⟩:m7 G0 G1 Q)=some ⟨some true,(e.1,e.2,true),gH [] t (ss δ fin e++u)⟩:=by simp only[step,ip,stepAux];have b:(gH [] (e::t) u:∀ k,Ls (uj G0 G1 Q k)) .tmp=e::t:=rfl;rw[b];simp only[List.head?_cons,jF,nW];rw[ze,BY _ _ hd,BY _ _ hd];simp[stepAux,ss]
lemma Bq(s:rZ G0 Q)(u:Ls G1):step (ip δ fin q₀ d) (⟨some true,s,gH [] [] u⟩:m7 G0 G1 Q)=some ⟨none,(q₀,none,false),gH [] [] u⟩:=by simp[step,ip,stepAux,gH,ze]
lemma Bp(u:Ls G1):∀(l:Ls G0) (t:Ls (Q×Op G0)) (s:rZ G0 Q),(flip bind (step (ip δ fin q₀ d)))^[l.length+1] (some (⟨some false,s,gH l t u⟩:m7 G0 G1 Q))=some ⟨some true,(q₀,none,false),gH [] ((vr δ s.1 l).reverse++t) u⟩:=by
 intro l;induction l with
 | nil=>intro t s;exact Br δ fin q₀ d s t u
 | cons a l b=>intro t s;rw[aX,eo];have e:flip bind (step (ip δ fin q₀ d)) (some (⟨some false,s,gH (a::l) t u⟩:m7 G0 G1 Q))=some ⟨some false,((δ s.1 a).1,none,false),gH l ((s.1,some a)::t) u⟩:=A8 δ fin q₀ d s a l t u;rw[e,b];simp[vr]
lemma Bn(hd:∀ _:G1,d≠none):∀(t:Ls (Q×Op G0)) (u:Ls G1) (s:rZ G0 Q),(flip bind (step (ip δ fin q₀ d)))^[t.length+1] (some (⟨some true,s,gH [] t u⟩:m7 G0 G1 Q))=some ⟨none,(q₀,none,false),gH [] [] (t.reverse.flatMap (ss δ fin)++u)⟩:=by
 intro t;induction t with
 | nil=>intro u s;exact Bq δ fin q₀ d s u
 | cons e t b=>intro u s;rw[aX,eo];have c:flip bind (step (ip δ fin q₀ d)) (some (⟨some true,s,gH [] (e::t) u⟩:m7 G0 G1 Q))=some ⟨some true,(e.1,e.2,true),gH [] t (ss δ fin e++u)⟩:=A7 δ fin q₀ d hd s e t u;rw[c,b];simp[mJ]
lemma Bm[Fintype G0][Fintype Q](hd:∀ _:G1,d≠none)(l:Ls G0):(flip bind (step (ip δ fin q₀ d)))^[l.length+1+1+(l.length+1)] (some (initList (xU δ fin q₀ d) l))=some (haltList (xU δ fin q₀ d) (iB δ fin q₀ l)):=by
 refine (aI (fun c=>(flip bind (step (ip δ fin q₀ d)))^[l.length+1+1+(l.length+1)] (some c)) (d4 (xU δ fin q₀ d) l)).trans (Eq.trans ?_ (aI some (d5 (xU δ fin q₀ d) (iB δ fin q₀ l))).symm);show (flip bind (step (ip δ fin q₀ d)))^[l.length+1+1+(l.length+1)] (some (⟨some false,(q₀,none,false),update (fun _=>[]) .inp l⟩:m7 G0 G1 Q))=some (⟨none,(q₀,none,false),update (fun _=>[]) .out (iB δ fin q₀ l)⟩:m7 G0 G1 Q)
 have e:(flip bind (step (ip δ fin q₀ d)))^[l.length+1] (some (⟨some false,(q₀,none,false),gH l [] []⟩:m7 G0 G1 Q))=some ⟨some true,(q₀,none,false),gH [] (vr δ q₀ l).reverse []⟩:=by
  have:=Bp δ fin q₀ d [] l [] (q₀,none,false)
  rw[cR] at this;exact this
 have b:(flip bind (step (ip δ fin q₀ d)))^[l.length+1+1] (some (⟨some true,(q₀,none,false),gH [] (vr δ q₀ l).reverse []⟩:m7 G0 G1 Q))=some ⟨none,(q₀,none,false),gH [] [] (iB δ fin q₀ l)⟩:=by
  have:=Bn δ fin q₀ d hd (vr δ q₀ l).reverse [] (q₀,none,false)
  rw[j2,Dj,g0,DA,cR] at this;exact this
 rw[fq,<- DC,e,b,A6]
lemma rd{v u e b q:Type}[Fintype e][Fintype q](j:v->Ls e)(s:u->Ls b)(f:v->u)(o:q->e->q×Op b×Op b)(i:q->Op b)(c:q)(h:∀ a,s (f a)=iB o i c (j a)):Nonempty (Turing.TM2ComputableInPolyTime j s f):=by
 classical
 let d:Op b:=if h:Nonempty b then some (Classical.choice h) else none;have hd:∀ _:b,d≠none:=(by intro y;have x:Nonempty b:=⟨y⟩;simp[d,x]);exact⟨{
  tm:=xU o i c d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  outputsFun:=fun a=>
   { steps:=(j a).length+1+1+((j a).length+1)
     evals_in_steps:=by
      have w:∀(r:Type) (l:Ls r),List.map (Equiv.refl r).invFun l=l:=fun r l=>by simp
      have:=Bm o i c d hd (j a)
      exact (aI (fun l=>(flip bind (step (ip o i c d)))^[(j a).length+1+1+((j a).length+1)] (some (initList (xU o i c d) l))) (w e (j a))).trans (this.trans (aI (fun l=>some (haltList (xU o i c d) l)) ((h a).symm.trans (w b (s (f a))).symm)))
     steps_le_m:=by
      simp only[ly,pe,pn,pl];omega } }⟩
lemma eU{u s c b i:Type}[Fintype c][Fintype i](o:u->Ls c)(r:s->Ls b)(f:u->s)(j:i->c->i×Op b)(e:i->Op b)(d:i)(h:∀ a,r (f a)=cL j e d (o a)):Nonempty (Turing.TM2ComputableInPolyTime o r f):=rd o r f (fun q a=>((j q a).1,(j q a).2,none)) e d (fun a=>(h a).trans (Dh j e d (o a)))
end Lib.Machines
end
section
namespace Lib.Machines.AI
open Turing PEqualNP.Library Lib.Machines
def ig:Unit->TM2.Stmt (fun _:Bo=>Bo) Unit (Op Bo)
 | ()=>.pop false (fun _ o=>o) (.branch (fun s=>s.isSome) (.push true (fun s=>s.getD false) (.load (fun _=>none) (.goto fun _=>()))) .halt)
def tm:FinTM2 where
 K:=Bo
 k₀:=false
 k₁:=true
 Γ _:=Bo
 Λ:=Unit
 main:=()
 σ:=Op Bo
 initialState:=none
 m:=ig
abbrev v9:Type:=TM2.Cfg (fun _:Bo=>Bo) Unit (Op Bo)
def st(l u:LB):Bo->LB:=fun k=>cond k u l
lemma Ak(l:LB):st l []=update (fun _=>([]:LB)) false l:=by funext k;cases k <;> simp[st]
lemma wO(u:LB):st [] u=update (fun _=>([]:LB)) true u:=by funext k;cases k <;> simp[st]
lemma AL(x:Bo)(l u:LB):step ig (⟨some (),none,st (x::l) u⟩:v9)=some ⟨some (),none,st l (x::u)⟩:=by simp only[step,ig,stepAux];simp only[st,nT,List.head?_cons,jF,ph,nW,Option.getD_some,ia,TM2.Cfg.mk.injEq,fR];funext k;cases k <;> simp[st]
lemma Be(u:LB):step ig (⟨some (),none,st [] u⟩:v9)=some ⟨none,none,st [] u⟩:=by simp only[step,ig,stepAux];simp only[st,nT,List.head?_nil,px,pj,ia,TM2.Cfg.mk.injEq,fR];funext k;cases k <;> simp[st]
lemma loop:∀(l u:LB),(flip bind (step ig))^[l.length+1] (some (⟨some (),none,st l u⟩:v9))=some ⟨none,none,st [] (l.reverse++u)⟩:=by
 intro l;induction l with
 | nil=>intro u;exact Be u
 | cons x l b=>intro u;rw[aX,eo];have e:flip bind (step ig) (some (⟨some (),none,st (x::l) u⟩:v9))=some ⟨some (),none,st l (x::u)⟩:=AL x l u;rw[e,b];simp
lemma run(l:LB):(flip bind (step ig))^[l.length+1] (some (initList tm l))=some (haltList tm l.reverse):=by refine (aI (fun c=>(flip bind (step ig))^[l.length+1] (some c)) (d4 tm l)).trans (Eq.trans ?_ (aI some (d5 tm l.reverse)).symm);show (flip bind (step ig))^[l.length+1] (some (⟨some (),none,update (fun _=>[]) false l⟩:v9))=some (⟨none,none,update (fun _=>[]) true l.reverse⟩:v9);rw[<- Ak,loop,<- wO];simp
noncomputable def si:TM2ComputableInPolyTime (fun x:LB=>x) (fun x:LB=>x) (fun x:LB=>x.reverse) where
 tm:=tm
 inputAlphabet:=Equiv.refl _
 outputAlphabet:=Equiv.refl _
 time:=Polynomial.X+1
 outputsFun a:=
  { steps:=a.length+1
    evals_in_steps:=by
     have b:∀ l:LB,List.map (Equiv.refl Bo).invFun l=l:=fun l=>by simp
     exact (aI (fun l=>(flip bind (step ig))^[a.length+1] (some (initList tm l))) (b a)).trans ((run a).trans (aI (fun l=>some (haltList tm l)) (b a.reverse).symm))
    steps_le_m:=by simp }
end Lib.Machines.AI
end
section
namespace Lib.Universal
def un(n:Nat):LB:=replicate n true
def Z(a b:LB):LB:=un a.length++false::(a++b)
def aN(s:LB):LB×LB:=(((s.dropWhile id).tail).take (s.takeWhile id).length,((s.dropWhile id).tail).drop (s.takeWhile id).length)
lemma G(a b:LB):aN (Z a b)=(a,b):=by have d:(Z a b).takeWhile id=un a.length:=(by simp[Z,un]);have c:(Z a b).dropWhile id=false::(a++b):=(by simp[Z,un]);simp[aN,d,c,un]
end Lib.Universal
end
section
namespace Lib.Universal
def cF(b:Bo):LB:=if b then [true] else []
@[simp] lemma CZ:un 0=[]:=rfl
@[simp] lemma J(n:Nat):(un n).length=n:=sy
lemma rv(n:Nat):un (n+1)=true::un n:=rfl
def hd(s:LB):LB:=s.takeWhile id
def jy(s:LB):LB:=(s.dropWhile id).tail
def gT(f a b:LB):LB:=if f=[] then a else b
def dS(u v:LB):LB:=un (u.length*v.length)
def fJ(s:LB):LB:=s.map fun _=>false
lemma xQ(s:LB):(hd s).length<=s.length:=List.IsPrefix.length_le (List.takeWhile_prefix id)
lemma ni(s:LB):2*(aN s).1.length+(aN s).2.length<=s.length:=by have h:=aI List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s));simp only[dL] at h;simp only[aN,pa,List.length_drop,List.length_tail];omega
lemma rT(a b:LB):(Z a b).length=2*a.length+b.length+1:=by simp[Z];omega
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private lemma zl{j i c b:Type}{q:j->Ls c}{o:i->Ls b}{f d:j->i}(h:ComputableInPolyTime q o f)(e:∀ a,f a=d a):ComputableInPolyTime q o d:=by obtain rfl:f=d:=funext e;exact h
private lemma zW{h e C:Type}(c:h->Op C)(b:e->Op C)(x:Ls h)(w:Ls e):(x.map inl++w.map inr).filterMap (Sum.elim c b)=x.filterMap c++w.filterMap b:=by
 have j:∀ x:Ls h,(x.map inl).filterMap (Sum.elim c b)=x.filterMap c:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l d=>simp[pg,d]
 have i:∀ w:Ls e,(w.map inr).filterMap (Sum.elim c b)=w.filterMap b:=by
  intro w;induction w with
  | nil=>rfl
  | cons a l d=>simp[pg,d]
 rw[mG,j,i]
private lemma yN{b C:Type}(g:b->C)(l:Ls b):l.filterMap (fun a=>some (g a))=l.map g:=by induction l with|nil=>{rfl}|cons a l c=>{simp[c]}
private lemma BL{b C:Type}(l:Ls b):l.filterMap (fun _:b=>(none:Op C))=[]:=by induction l with|nil=>{rfl}|cons a l c=>{simp}
lemma A2:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>Z p.1 p.2):=by
 have e:ComputableInPolyTime encodePair encodePair (fun p:LB×LB=>(p.1,p.1++p.2)):=(by refine zb _ _ _ (Sum.elim (fun b:Bo=>some (inl b)) (fun _:Bo=>none)) (Sum.elim (fun b:Bo=>some (inr b)) (fun b:Bo=>some (inr b))) ?_;rintro⟨x,w⟩;simp only[encodePair];rw[zW,zW,yN,yN,yN,BL];simp)
 have d:U (fun a:LB=>a.map (fun _=>true)++[false]):=by
  refine eU _ _ _ (fun (_:Unit) (_:Bo)=>((),some true)) (fun _=>some false) () ?_;intro a;induction a with
  | nil=>rfl
  | cons b l c=>simp only[cL,aO,fB,Option.toList_some] at c ⊢;rw[<- c];rfl
 refine zl (aH (aH e (zk d)) Cg) ?_;rintro⟨x,w⟩;simp[Z,un]
lemma Ad:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>if p.1=[] then p.2 else []):=by
 obtain⟨c⟩:=Aa [];have d:=qB.oq (fun _:LB=>([]:LB)) c 0 (by simp);refine zl (aH Am d) ?_;rintro⟨x,w⟩;cases x with
 | nil=>simp
 | cons b l=>simp[jb]
lemma Dm:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>if p.1=[] then [] else p.2):=by
 have c:U (fun x:LB=>if x=[] then [true] else []):=aH (kv aR (Aa [true])) Ad;refine zl (aH (zk c) Ad) ?_;rintro⟨x,w⟩;cases x with
 | nil=>simp
 | cons b l=>simp
private def pL(u:LB):LB:=u.flatMap (fun b=>[true,b])
private def li(v:LB):LB:=v.flatMap (fun b=>[false,b])
private def zS:Bo->Bo->Bo×Op Bo
 | true,true=>(true,some true)
 | _,_=>(false,none)
private lemma Bl(l:LB):cL zS (fun _=>none) false l=[]/\cL zS (fun _=>none) true l=l.takeWhile id:=by induction l with|nil=>{exact⟨rfl,rfl⟩}|cons b l c=>{cases b <;> simp[cL,zS,c.1,c.2]}
private def yW:Bo->Bo->Bo×Op Bo×Op Bo
 | false,true=>(false,none,none)
 | false,false=>(true,none,none)
 | true,b=>(true,some false,some b)
private lemma Dz(l:LB):iB yW (fun _=>none) true l=li l:=by induction l with|nil=>{rfl}|cons b l c=>{simp[iB,yW,li,c]}
private lemma Dt(l:LB):iB yW (fun _=>none) false l=li (l.dropWhile id).tail:=by induction l with|nil=>{rfl}|cons b l c=>{cases b <;> simp[iB,yW,c,Dz]}
private def mkD:Bo×Bo->Bo->(Bo×Bo)×Op Bo
 | (d,false),t=>((d||!t,true),some (t||!d))
 | (d,true),b=>((d,false),some b)
private def mk(l:LB):LB:=cL mkD (fun _=>none) (false,false) l
private lemma DG(q:Bo×Bo)(l:LB):(cL mkD (fun _=>none) q l).length=l.length:=by induction l generalizing q with|nil=>{rfl}|cons b l e=>{obtain⟨d,c⟩:=q;cases c <;> simp[cL,mkD,e]}
private lemma Bf(v:LB):cL mkD (fun _=>none) (true,false) (li v)=li v:=by induction v with|nil=>{rfl}|cons b v c=>{simp[cL,mkD,li] at c ⊢;exact c}
private lemma Ce(u r:LB):cL mkD (fun _=>none) (false,false) (pL u++r)=pL u++cL mkD (fun _=>none) (false,false) r:=by induction u with|nil=>{rfl}|cons b u c=>{simp[cL,mkD,pL] at c ⊢;exact c}
private lemma zL(u:LB):mk (pL u++li [])=pL u++li []:=by unfold mk;rw[Ce];rfl
private lemma BD(u:LB)(b:Bo)(v:LB):mk (pL u++li (b::v))=pL (u++[b])++li v:=by unfold mk;rw[Ce];have h:cL mkD (fun _=>none) (false,false) (li (b::v))=true::b::li v:=(by have c:=Bf v;simp[cL,mkD,li] at c ⊢;exact c);rw[h];simp[pL]
private lemma BC(k:Nat):∀ u t:LB,mk^[k] (pL u++li t)=pL (u++t.take k)++li (t.drop k):=by
 induction k with
 | zero=>intro u t;simp
 | succ k c=>
   intro u t;rw[eo];cases t with
   | nil=>rw[zL,c];simp
   | cons b t=>rw[BD,c];simp
private def xP:Op Bo->Bo->Op Bo×Op (Bo ⊕ Bo)
 | none,t=>(some t,none)
 | some t,b=>(none,some (if t then inl b else inr b))
private lemma An(v:LB):cL xP (fun _=>none) none (li v)=v.map inr:=by induction v with|nil=>{rfl}|cons b v c=>{simp[cL,xP,li] at c ⊢;exact c}
private lemma Ao(u r:LB):cL xP (fun _=>none) none (pL u++r)=u.map inl++cL xP (fun _=>none) none r:=by induction u with|nil=>{rfl}|cons b u c=>{simp[cL,xP,pL] at c ⊢;exact c}
private def uF(l:Ls (Bo ⊕ Bo)):LB×LB:=(l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private lemma Dq(u v:LB):uF (u.map inl++v.map inr)=(u,v):=by
 have h:∀ x:LB,(x.map (inl (β:=Bo))).filterMap Sum.getLeft?=x:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l b=>exact aI (a::·) b
 have e:∀ x:LB,(x.map (inr (α:=Bo))).filterMap Sum.getLeft?=[]:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l b=>exact b
 have d:∀ x:LB,(x.map (inl (β:=Bo))).filterMap Sum.getRight?=[]:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l b=>exact b
 have c:∀ x:LB,(x.map (inr (α:=Bo))).filterMap Sum.getRight?=x:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l b=>exact aI (a::·) b
 simp only[uF,mG,h,e,d,c,cR,gl]
lemma B1:ComputableInPolyTime (fun x:LB=>x) encodePair aN:=by have c:U (fun s:LB=>s.takeWhile id):=eU _ _ _ zS (fun _=>none) true (fun s=>(Bl s).2.symm);have j:U (fun s:LB=>li (s.dropWhile id).tail):=rd _ _ _ yW (fun _=>none) false (fun s=>(Dt s).symm);have d:U mk:=eU _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl);obtain⟨q⟩:=d;have i:=qB.oq mk q 0 (fun y=>by simp[mk,DG]);have o:ComputableInPolyTime (fun x:LB=>x) (fun l:Ls (Bo ⊕ Bo)=>l) (fun l:LB=>cL xP (fun _=>none) none l):=eU _ _ _ xP (fun _=>none) none (fun _=>rfl);have b:ComputableInPolyTime (fun l:Ls (Bo ⊕ Bo)=>l) encodePair uF:=(by refine zb _ _ _ (fun s:Bo ⊕ Bo=>(Sum.getLeft? s).map inl) (fun s:Bo ⊕ Bo=>(Sum.getRight? s).map inr) ?_;intro l;simp only[uF,encodePair,List.map_filterMap]);refine zl (aH (aH (aH (kv j c) i) o) b) ?_;intro s;have h:=BC (s.takeWhile id).length [] (s.dropWhile id).tail;have e:pL []++li (s.dropWhile id).tail=li (s.dropWhile id).tail:=rfl;rw[e] at h;simp only[h,gl];rw[Ao,An,Dq];rfl
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private lemma w6{j i c b:Type}{q:j->Ls c}{o:i->Ls b}{f d:j->i}(h:ComputableInPolyTime q o f)(e:∀ a,f a=d a):ComputableInPolyTime q o d:=by obtain rfl:f=d:=funext e;exact h
private def zy:Bo->Bo->Bo×Op Bo
 | true,true=>(true,some true)
 | _,_=>(false,none)
private lemma BJ(l:LB):cL zy (fun _=>none) false l=[]/\cL zy (fun _=>none) true l=l.takeWhile id:=by induction l with|nil=>{exact⟨rfl,rfl⟩}|cons b l c=>{cases b <;> simp[cL,zy,c.1,c.2]}
lemma mB:U hd:=eU _ _ _ zy (fun _=>none) true (fun s=>(BJ s).2.symm)
private def yV:Bo->Bo->Bo×Op Bo
 | false,true=>(false,none)
 | false,false=>(true,none)
 | true,b=>(true,some b)
private lemma Bk(l:LB):cL yV (fun _=>none) true l=l:=by induction l with|nil=>{rfl}|cons b l c=>{simp[cL,yV,c]}
private lemma A0(l:LB):cL yV (fun _=>none) false l=(l.dropWhile id).tail:=by induction l with|nil=>{rfl}|cons b l c=>{cases b <;> simp[cL,yV,c,Bk]}
lemma k6:U jy:=eU _ _ _ yV (fun _=>none) false (fun s=>(A0 s).symm)
private def y3:Bo->Bo->Bo×Op Bo
 | false,_=>(true,none)
 | true,b=>(true,some b)
private lemma Bd(l:LB):cL y3 (fun _=>none) true l=l:=by induction l with|nil=>{rfl}|cons b l c=>{simp[cL,y3,c]}
private lemma AK(l:LB):cL y3 (fun _=>none) false l=l.tail:=by cases l with|nil=>{rfl}|cons b l=>{simp[cL,y3,Bd]}
lemma rz:U (fun s:LB=>s.tail):=eU _ _ _ y3 (fun _=>none) false (fun s=>(AK s).symm)
private lemma A4(l:LB):cL (fun (_:Unit) (_:Bo)=>((),some false)) (fun _=>none) () l=fJ l:=by induction l with|nil=>{rfl}|cons b l c=>{simp[cL,fJ] at c ⊢;exact c}
lemma g2:U fJ:=eU _ _ _ (fun (_:Unit) (_:Bo)=>((),some false)) (fun _=>none) () (fun s=>(A4 s).symm)
lemma aG(l:LB):U (fun _:LB=>l):=Aa l
lemma f2:U (fun s:LB=>(aN s).1):=w6 (aH B1 BV) (fun _=>rfl)
lemma dI:U (fun s:LB=>(aN s).2):=w6 (aH B1 BU) (fun _=>rfl)
lemma aC{u v:LB->LB}(c:U u)(b:U v):U (fun s=>u s++v s):=w6 (aH (kv c b) Cg) (fun _=>rfl)
lemma D{u v:LB->LB}(c:U u)(b:U v):U (fun s=>Z (u s) (v s)):=w6 (aH (kv c b) A2) (fun _=>rfl)
lemma cY{f a b:LB->LB}(c:U f)(e:U a)(d:U b):U (fun s=>gT (f s) (a s) (b s)):=by have j:=aH (kv c e) Ad;have i:=aH (kv c d) Dm;refine w6 (aC j i) ?_;intro s;by_cases h:f s=[] <;> simp[gT,h]
end Lib.Universal
end
namespace MachineBits
open PEqualNP.Library Lib Lib.Universal Lib.Machines
lemma ts{f g:LB->LB}(b:U f)(h:∀ x,f x=g x):U g:=by
 have:f=g:=funext h
 rwa [<- this]
lemma Cq:U (fun s:LB=>s.reverse):=⟨AI.si⟩
lemma z0{g e arg:LB->LB}(k:Nat)(i:U g)(h:∀ s,(g s).length<=s.length+k)(b:U e)(d:U arg):U (fun s=>g^[(e s).length] (arg s)):=by obtain⟨c⟩:=i;have j:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>g^[p.2.length] p.1):=qB.oq g c k h;exact ts (aH (kv d b) j) (fun _=>rfl)
lemma CJ{g e arg:LB->LB}(m:LB->Nat)(a:Nat)(j:U g)(i:∀ y,m (g y)<=m y)(h:∀ y,(g y).length<=y.length+m y)(o:∀ y,m y<=a*y.length+a)(b:U e)(d:U arg):U (fun s=>g^[(e s).length] (arg s)):=by obtain⟨c⟩:=j;have q:ComputableInPolyTime encodePair (fun x:LB=>x) (fun p:LB×LB=>g^[p.2.length] p.1):=qB.lP g c m a i h o;exact ts (aH (kv d b) q) (fun _=>rfl)
lemma q7(a b:LB):(Z a b).length=2*a.length+b.length+1:=by simp[Z,un];omega
lemma q0(y:LB):2*(aN y).1.length+(aN y).2.length<=y.length:=by
 dsimp only[aN];have b:y=y.takeWhile id++y.dropWhile id:=(List.takeWhile_append_dropWhile (p:=id) (l:=y)).symm
 have c:y.length=(y.takeWhile id).length+(y.dropWhile id).length:=by
  conv_lhs=>rw[b]
  exact dL
 set a:=(y.takeWhile id).length
 set t:=(y.dropWhile id).tail;have d:t.length<=(y.dropWhile id).length:=(by dsimp only[t];cases y.dropWhile id <;> simp);have e:(t.take a).length=min a t.length:=pa;have h:(t.drop a).length=t.length-a:=List.length_drop;omega
lemma zM{g e arg:LB->LB}(c:Nat)(j:U g)(i:∀ y,(aN (g y)).1=(aN y).1)(h:∀ y,(g y).length<=y.length+c*(aN y).1.length+c)(b:U e)(d:U arg):U (fun s=>g^[(e s).length] (arg s)):=by
 refine CJ (fun y=>c*(aN y).1.length+c) c j (fun y=>by rw[i y]) (fun y=>by have:=h y;omega) (fun y=>by
  have o:(aN y).1.length<=y.length:=(by have:=q0 y;omega);have q:=lz c o;omega)
  b d
def m0(s:LB):LB:=replicate s.length true
lemma yZ(s:LB):(m0 s).length=s.length:=sy
lemma yD:U m0:=eU _ _ _ (fun (_:Unit) (_:Bo)=>((),some true)) (fun _=>none) () (fun s=>by
 induction s with
 | nil=>rfl
 | cons b l c=>simp only[cL,m0,aX,mI];exact aI (true::·) c)
def xT(s:LB):LB:=Z (aN s).1 ((aN s).2++(aN s).1)
lemma Cs:U xT:=D f2 (aC dI f2)
lemma CT(a:LB):∀ k b,xT^[k] (Z (m0 a) b)=Z (m0 a) (b++un (k*a.length))
 | 0,b=>by simp[un]
 | k+1,b=>by
   rw[eo,xT,G,CT a k (b++m0 a)];congr 1;simp[m0,un,dM,<- o9,qU,Nat.add_comm]
lemma jW{u v:LB->LB}(d:U u)(c:U v):U (fun s=>dS (u s) (v s)):=by
 have h:U (fun s=>xT^[(u s).length] (Z (m0 (v s)) [])):=zM 1 Cs (fun y=>by rw[xT,G]) (fun y=>by
  rw[xT,q7,dL]
  have:=q0 y
  omega)
  d (D (aH c yD) (aG []))
 have e:=aH h dI;have b:(fun s=>(aN (xT^[(u s).length] (Z (m0 (v s)) []))).2)=(fun s=>dS (u s) (v s)):=(by funext s;rw[CT,G,gl];rfl)
 rwa [b] at e
def pU(s:LB):LB:=match s with
 | true::_=>[true]
 | _=>[]
lemma xR:U pU:=eU _ _ _ (fun (st:Bo) (b:Bo)=>if st then (false,if b then some true else none) else (false,none)) (fun _=>none) true (fun s=>by
 have c:∀ l,cL (fun (st:Bo) (b:Bo)=>if st then (false,if b then some true else none) else (false,none)) (fun _=>none) false l=[]:=by intro l;induction l with|nil=>rfl|cons b l d=>simp[cL,d]
 cases s with
 | nil=>rfl
 | cons b l=>cases b <;> simp[cL,pU,c])
def z1(s:LB):LB:=gT s [true] []
lemma Cp:U z1:=cY aR (aG [true]) (aG [])
def gY(b xs:LB):LB:=(aN (m0 b++false::xs)).1
def fO(b xs:LB):LB:=(aN (m0 b++false::xs)).2
lemma vZ(b xs:LB):gY b xs=xs.take b.length:=by have d:(m0 b++false::xs).takeWhile id=m0 b:=(by simp[m0]);have c:(m0 b++false::xs).dropWhile id=false::xs:=(by simp[m0]);simp[gY,aN,d,c,yZ]
lemma xS(b xs:LB):fO b xs=xs.drop b.length:=by have d:(m0 b++false::xs).takeWhile id=m0 b:=(by simp[m0]);have c:(m0 b++false::xs).dropWhile id=false::xs:=(by simp[m0]);simp[fO,aN,d,c,yZ]
lemma sf{u v:LB->LB}(c:U u)(b:U v):U (fun s=>gY (u s) (v s)):=ts (aH (aC (aH c yD) (aC (aG [false]) b)) f2) (fun _=>rfl)
lemma gW{u v:LB->LB}(c:U u)(b:U v):U (fun s=>fO (u s) (v s)):=ts (aH (aC (aH c yD) (aC (aG [false]) b)) dI) (fun _=>rfl)
def val:LB->Nat
 | []=>0
 | b::l=>b.toNat+2*val l
lemma yX(l:LB):val l<2^l.length:=by induction l with|nil=>{simp[val]}|cons b l c=>{simp only[val,aX,gN];cases b <;> simp <;> omega}
lemma DP(a b:LB):val (a++b)=val a+2^a.length*val b:=by induction a with|nil=>{simp[val]}|cons x l c=>{simp only[fB,val,aX,gN,c];ring}
lemma DN(k:Nat):val (replicate k false)=0:=by induction k with|zero=>{rfl}|succ k b=>{simp[mI,val,b]}
lemma Ax(l:LB):val (fJ l)=0:=by
 have h:fJ l=replicate l.length false:=by induction l with|nil=>{rfl}|cons _ r b=>{simp[fJ,mI]}
 rw[h,DN]
lemma zN(l:LB):(fJ l).length=l.length:=by induction l with|nil=>{rfl}|cons _ r b=>{simp[fJ]}
lemma yY(k:Nat)(l:LB):val (l.take k)=val l % 2^k:=by
 induction k generalizing l with
 | zero=>simp[val,Nat.mod_one]
 | succ k d=>
   cases l with
   | nil=>simp[val]
   | cons b r=>
     simp only[List.take_succ_cons,val,d,pow_succ'];have e:b.toNat<2:=(by cases b <;> decide)
     have c:(b.toNat+2*val r) % (2*2^k)=b.toNat+2*(val r % 2^k):=by
      have j:=qR (val r) (2^k);have i:val r % 2^k<2^k:=gb _ (by positivity)
      have h:b.toNat+2*val r=(2*2^k)*(val r / 2^k)+(b.toNat+2*(val r % 2^k)):=by linarith
      rw[h,Nat.mul_add_mod];exact mF (by omega)
     exact c.symm
lemma CB(n:Nat):val n.bits=n:=by
 induction n using Nat.binaryRec with
 | zero=>simp[val]
 | bit b m c=>
   by_cases h:b=false/\m=0
   · rcases h with ⟨rfl,rfl⟩;simp[val]
   {rw[qC m b (fun d=>by subst d;cases b <;> simp_all)];simp only[val,c,Nat.bit];cases b <;> simp <;> omega}
def rI:LB->LB
 | []=>[true]
 | false::l=>true::l
 | true::l=>false::rI l
lemma Cu(l:LB):val (rI l)=val l+1:=by induction l with|nil=>{simp[rI,val]}|cons b l c=>{cases b <;> simp[rI,val,c] <;> omega}
lemma Cv(l:LB):(rI l).length<=l.length+1:=by induction l with|nil=>{simp[rI]}|cons b l c=>{cases b <;> simp[rI] <;> omega}
lemma Cr(n:Nat):rI n.bits=(n+1).bits:=by
 induction n using Nat.binaryRec with
 | zero=>decide
 | bit b m j=>cases b with|false=>{by_cases i:m=0;{subst i;decide};{have e:(Nat.bit false m).bits=false::m.bits:=qC m false (fun h=>(i h).elim);have d:Nat.bit false m+1=Nat.bit true m:=(by simp[Nat.bit]);have c:(Nat.bit true m).bits=true::m.bits:=qC m true (fun _=>by simp);rw[e,d,c,rI]}}|true=>{have e:(Nat.bit true m).bits=true::m.bits:=qC m true (fun _=>by simp);have d:Nat.bit true m+1=Nat.bit false (m+1):=(by simp[Nat.bit];omega);have c:(Nat.bit false (m+1)).bits=false::(m+1).bits:=qC (m+1) false (fun h=>by omega);rw[e,d,c,rI,j]}
lemma z2:U rI:=by
 let i:Bo->Bo->Bo×Op Bo:=fun c b=>
  match c,b with
  | false,b=>(false,some b)
  | true,false=>(false,some true)
  | true,true=>(true,some false)
 let d:Bo->Op Bo:=fun c=>if c then some true else none;refine eU _ _ _ i d true fun s=>?_
 have e:∀ l,cL i d false l=l:=by intro l;induction l with|nil=>rfl|cons b r j=>simp[cL,i,d,j]
 have h:∀ l,cL i d true l=rI l:=by
  intro l;induction l with
  | nil=>rfl
  | cons b r j=>cases b <;> simp[cL,i,d,rI,e,j]
 exact (h s).symm
def zO(u:LB):LB:=rI^[u.length] []
lemma DQ(u:LB):zO u=u.length.bits:=by
 dsimp only[zO]
 have h:∀ k,rI^[k] []=k.bits:=by
  intro k;induction k with
  | zero=>rfl
  | succ k b=>rw[jb,b,Cr]
 exact h u.length
lemma DM:U zO:=z0 1 z2 Cv aR (aG [])
def dT(b x:LB):LB:=gY b (x++fJ b)
lemma qd(b x:LB):(dT b x).length=b.length:=by dsimp only[dT];rw[vZ,pa,dL,zN];omega
lemma vI(b x:LB):val (dT b x)=val x % 2^b.length:=by dsimp only[dT];rw[vZ,yY,DP,Ax,mul_zero,g1]
lemma qu{c b:LB->LB}(d:U c)(e:U b):U (fun s=>dT (c s) (b s)):=sf d (aC e (aH d g2))
def oT(b u:LB):LB:=dT b (zO u)
lemma CQ(b u:LB):(oT b u).length=b.length:=qd b _
lemma zX(b u:LB):val (oT b u)=u.length % 2^b.length:=by dsimp only[oT];rw[vI,DQ,CB]
lemma Ay{b c:LB->LB}(d:U b)(e:U c):U (fun s=>oT (b s) (c s)):=qu d (aH e DM)
def tu(x:LB):LB:=x.map (!·)
lemma CD(x:LB):val (tu x)+val x+1=2^x.length:=by induction x with|nil=>{simp[tu,val]}|cons b l c=>{simp only[tu,aO,val,aX,gN] at c ⊢;cases b <;> simp <;> omega}
lemma CF:U tu:=eU _ _ _ (fun (_:Unit) (b:Bo)=>((),some (!b))) (fun _=>none) () fun s=>by
 induction s with|nil=>{rfl}|cons b l c=>{simp only[cL,tu,aO];exact aI ((!b)::·) c}
def yd(b x:LB):LB:=gY b (rI (dT b x))
lemma CL(b x:LB):val (yd b x)=(val x+1) % 2^b.length:=by dsimp only[yd];rw[vZ,yY,Cu,vI,Nat.mod_add_mod]
lemma CN{c b:LB->LB}(d:U c)(e:U b):U (fun s=>yd (c s) (b s)):=sf d (aH (qu d e) z2)
def ti(b x:LB):LB:=yd b (tu (dT b x))
lemma Co(b x:LB):((val (ti b x):Int) ≡ -(val x:Int) [ZMOD (2:Int)^b.length]):=by
 dsimp only[ti];rw[CL];have c:=CD (dT b x);rw[qd] at c;have j:val (tu (dT b x))+1=2^b.length-val (dT b x):=(by omega);have h:((val (tu (dT b x))+1) % 2^b.length:Int) ≡ ((val (tu (dT b x))+1:Nat):Int) [ZMOD (2:Int)^b.length]:=(by exact_mod_cast (j7 (val (tu (dT b x))+1) (2^b.length)));have i:((val (tu (dT b x))+1:Nat):Int)+(val (dT b x):Int)=(2:Int)^b.length:=(by exact_mod_cast (by omega:val (tu (dT b x))+1+val (dT b x)=2^b.length));have e:((val (dT b x):Nat):Int) ≡ (val x:Int) [ZMOD (2:Int)^b.length]:=(by rw[vI];exact_mod_cast (j7 (val x) (2^b.length)))
 have d:((val (tu (dT b x))+1:Nat):Int) ≡ -(val (dT b x):Int) [ZMOD (2:Int)^b.length]:=by
  rw[Int.modEq_iff_dvd];have:-(val (dT b x):Int)-((val (tu (dT b x))+1:Nat):Int)=-((2:Int)^b.length):=by linarith
  rw[this];exact dvd_neg.2 (dvd_refl _)
 exact h.trans (d.trans e.neg)
lemma zZ{c b:LB->LB}(d:U c)(e:U b):U (fun s=>ti (c s) (b s)):=CN d (aH (qu d e) CF)
def rt(b x:LB):LB:=gY b (false::dT b x)
lemma z3(b x:LB):(rt b x).length=b.length:=by dsimp only[rt];rw[vZ,List.length_take,List.length_cons,qd];omega
lemma CH(b x:LB):val (rt b x)=(2*val x) % 2^b.length:=by dsimp only[rt];rw[vZ,yY,val,qQ,lE,vI,Nat.mul_mod_mod]
lemma CI{c b:LB->LB}(d:U c)(e:U b):U (fun s=>rt (c s) (b s)):=sf d (aC (aG [false]) (qu d e))
def yC(f:LB):LB:=gT f [false] [true]
lemma CR{b:LB->LB}(c:U b):U (fun s=>yC (b s)):=cY c (aG [false]) (aG [true])
def qk(a b:LB):LB:=gT a (gT b [] [true]) (gT b [true] [])
def ye(a b c:LB):LB:=gT a (gT b [] (gT c [] [true])) (gT b (gT c [] [true]) [true])
lemma yg{c b:LB->LB}(e:U c)(d:U b):U (fun s=>qk (c s) (b s)):=cY e (cY d (aG []) (aG [true])) (cY d (aG [true]) (aG []))
lemma CM{d c b:LB->LB}(i:U d)(h:U c)(e:U b):U (fun s=>ye (d s) (c s) (b s)):=cY i (cY h (aG []) (cY e (aG []) (aG [true]))) (cY h (cY e (aG []) (aG [true])) (aG [true]))
def vH(y:LB):LB:=
 let a:=(aN y).1;let i:=(aN y).2;let b:=(aN i).1;let h:=(aN i).2;let c:=(aN h).1;let e:=(aN h).2;let q:=pU a;let o:=pU b;let j:=pU c;let d:=yC (qk (qk q o) j);let r:=ye q o j
 Z a.tail (Z b.tail (Z r (d++e)))
lemma CA(y:LB):(vH y).length<=y.length+6:=by dsimp only[vH];have j:=q0 y;have i:=q0 (aN y).2;have h:=q0 (aN (aN y).2).2;rw[q7,q7,q7,dL];have e:(aN y).1.tail.length<=(aN y).1.length:=(by cases (aN y).1 <;> simp);have d:(aN (aN y).2).1.tail.length<=(aN (aN y).2).1.length:=(by cases (aN (aN y).2).1 <;> simp);have b:(yC (qk (qk (pU (aN y).1) (pU (aN (aN y).2).1)) (pU (aN (aN (aN y).2).2).1))).length=1:=(by unfold yC gT;split_ifs <;> rfl);have c:(ye (pU (aN y).1) (pU (aN (aN y).2).1) (pU (aN (aN (aN y).2).2).1)).length<=1:=(by unfold ye gT;split_ifs <;> simp);omega
lemma Cz:U vH:=by have q:U (fun y=>(aN y).1):=f2;have h:U (fun y=>(aN y).2):=dI;have o:U (fun y=>(aN (aN y).2).1):=ts (aH h f2) (fun _=>rfl);have e:U (fun y=>(aN (aN y).2).2):=ts (aH h dI) (fun _=>rfl);have s:U (fun y=>(aN (aN (aN y).2).2).1):=ts (aH e f2) (fun _=>rfl);have i:U (fun y=>(aN (aN (aN y).2).2).2):=ts (aH e dI) (fun _=>rfl);have d:=aH q xR;have c:=aH o xR;have b:=aH s xR;have r:=CR (yg (yg d c) b);have j:=CM d c b;exact ts (D (aH q rz) (D (aH o rz) (D j (aC r i)))) (fun _=>rfl)
def nj(c a b:LB):LB:=
 let d:=vH^[c.length] (Z (dT c a) (Z (dT c b) (Z [] [])))
 (aN (aN (aN d).2).2).2.reverse
lemma Cn(k:Nat):∀(a b:LB) (c:Bo) (e:LB),a.length=k->b.length=k->∃(d:LB) (u:Bo),vH^[k] (Z a (Z b (Z (if c then [true] else []) e)))=Z [] (Z [] (Z (if u then [true] else []) (d.reverse++e)))/\d.length=k/\val d+2^k*u.toNat=val a+val b+c.toNat:=by
 induction k with
 | zero=>intro a b c e s r;cases a;cases b;{exact⟨[],c,by simp,rfl,by simp[val]⟩};{simp at r};{simp at s}
 | succ k z=>
   intro a b c e s r;cases a with
   | nil=>simp at s
   | cons i w=>
     cases b with
     | nil=>simp at r
     | cons h v=>
       rw[eo];have j:vH (Z (i::w) (Z (h::v) (Z (if c then [true] else []) e)))=Z w (Z v (Z (if ((i&&h)||(c&&(i||h))) then [true] else []) (((xor (xor i h) c)::e)))):=(by dsimp only[vH];simp only[G,jF];cases i <;> cases h <;> cases c <;> rfl);rw[j];obtain⟨d,u,o,q,x⟩:=z w v ((i&&h)||(c&&(i||h))) ((xor (xor i h) c)::e) (by simpa using s) (by simpa using r);refine⟨(xor (xor i h) c)::d,u,?_,by simp[q],?_⟩;{rw[o];simp}
       ·
        simp only[val,pow_succ'];have y:(xor (xor i h) c).toNat+2*((i&&h)||(c&&(i||h))).toNat=i.toNat+h.toNat+c.toNat:=(by cases i <;> cases h <;> cases c <;> decide)
        linarith
lemma z5(c a b:LB):(nj c a b).length=c.length/\val (nj c a b)=(val a+val b) % 2^c.length:=by
 dsimp only[nj];obtain⟨d,q,e,h,j⟩:=Cn c.length (dT c a) (dT c b) false [] (qd c a) (qd c b);simp only[eX,↓reduceIte,cR,qQ,g1] at e j;rw[e];simp only[G,g0];refine⟨h,?_⟩;have o:val d<2^c.length:=(by rw[<- h];exact yX d)
 have i:val d=(val (dT c a)+val (dT c b)) % 2^c.length:=by
  have:val (dT c a)+val (dT c b)=2^c.length*q.toNat+val d:=by linarith
  rw[this,Nat.mul_add_mod,mF o]
 rw[i,vI,vI,Nat.mod_add_mod,Nat.add_mod_mod]
lemma y0(c a b:LB):(nj c a b).length=c.length:=(z5 c a b).1
lemma z6(c a b:LB):val (nj c a b)=(val a+val b) % 2^c.length:=(z5 c a b).2
lemma DR(c a b:LB):((val (nj c a b):Int) ≡ (val a:Int)+(val b:Int) [ZMOD (2:Int)^c.length]):=by rw[z6];exact_mod_cast (j7 (val a+val b) (2^c.length))
lemma Az{d h e:LB->LB}(c:U d)(j:U h)(i:U e):U (fun s=>nj (d s) (h s) (e s)):=by have b:=z0 6 Cz CA c (D (qu c j) (D (qu c i) (aG (Z [] []))));exact aH (aH (aH (aH b dI) dI) dI) Cq
def vG(y:LB):LB:=
 let i:=(aN y).1;let o:=(aN y).2;let b:=(aN o).1;let j:=(aN o).2;let h:=(aN j).1;let d:=(aN j).2;let c:=gT (pU b) (dT i d) (nj i d h);let e:=rt i h
 Z i (Z b.tail (Z e c))
lemma Cy:U vG:=by have h:=f2;have e:=dI;have j:=aH e f2;have d:=aH e dI;have o:=aH d f2;have b:=aH d dI;have c:=cY (aH j xR) (qu h b) (Az h b o);have i:=CI h o;exact D h (D (aH j rz) (D i c))
def rk(c a b:LB):LB:=
 let d:=vG^[c.length] (Z c (Z (dT c b) (Z (dT c a) (fJ c))))
 (aN (aN (aN d).2).2).2
lemma CO{d h e:LB->LB}(b:U d)(q:U h)(o:U e):U (fun s=>rk (d s) (h s) (e s)):=by
 have c:=zM 4 Cy (fun y=>by dsimp only[vG];rw[G]) (fun y=>by
  dsimp only[vG]
  set wU:=(aN y).1;set r1:=(aN y).2
  set bRem:=(aN r1).1;set r2:=(aN r1).2
  set aSh:=(aN r2).1;set acc:=(aN r2).2;have v:2*wU.length+r1.length<=y.length:=q0 y;have u:2*bRem.length+r2.length<=r1.length:=q0 r1;have r:2*aSh.length+acc.length<=r2.length:=q0 r2;rw[q7,q7,q7,z3];have j:bRem.tail.length<=bRem.length:=(by cases bRem <;> simp);have i:(gT (pU bRem) (dT wU acc) (nj wU acc aSh)).length=wU.length:=(by unfold gT;split_ifs;{exact qd _ _};{exact y0 _ _ _});omega)
  b (D b (D (qu b o) (D (qu b q) (aH b g2))))
 exact ts (aH (aH (aH c dI) dI) dI) (fun _=>rfl)
lemma Cm(d:LB)(k:Nat):∀(e b c:LB),e.length=k->b.length=d.length->c.length=d.length->∃ q h,vG^[k] (Z d (Z e (Z b c)))=Z d (Z [] (Z q h))/\h.length=d.length/\val h % 2^d.length=(val c+val b*val e) % 2^d.length:=by
 induction k with
 | zero=>intro e b c B _ r;cases e;{exact⟨b,c,rfl,r,by simp[val]⟩};{simp at B}
 | succ k E=>
   intro e b c B K r;cases e with
   | nil=>simp at B
   | cons o z=>
     rw[eo];have u:vG (Z d (Z (o::z) (Z b c)))=Z d (Z z (Z (rt d b) (if o then nj d c b else dT d c))):=(by dsimp only[vG];simp only[G,jF];cases o <;> rfl);rw[u];have i:(if o then nj d c b else dT d c).length=d.length:=(by cases o <;> simp[y0,qd]);obtain⟨q,h,y,x,s⟩:=E z (rt d b) (if o then nj d c b else dT d c) (by simpa using B) (z3 d b) i;refine⟨q,h,y,x,?_⟩;rw[s,CH]
     have w:val (if o then nj d c b else dT d c) ≡
      val c+val b*o.toNat [MOD 2^d.length]:=by
      cases o with|false=>{simp only[eX,↓reduceIte,qQ,mul_zero,g1,vI];exact j7 _ _}|true=>{simp only[↓reduceIte,Bool.toNat_true,kQ,z6];exact j7 _ _}
     have v:((2*val b) % 2^d.length)*val z ≡ (2*val b)*val z [MOD 2^d.length]:=(j7 _ _).mul_right _;have j:=w.add v;have L:val c+val b*o.toNat+2*val b*val z=val c+val b*(o.toNat+2*val z):=(by ring);rw[L] at j;simpa only[Nat.ModEq,val] using j
lemma z4(c a b:LB):(rk c a b).length=c.length/\val (rk c a b)=(val a*val b) % 2^c.length:=by dsimp only[rk];obtain⟨o,h,i,e,d⟩:=Cm c c.length (dT c b) (dT c a) (fJ c) (qd c b) (qd c a) (zN c);rw[i];simp only[G];refine⟨e,?_⟩;rw[Ax,lE,vI,vI] at d;have j:val h<2^c.length:=(by rw[<- e];exact yX h);rw[mF j] at d;rw[d,Nat.mod_mul_mod,Nat.mul_mod_mod]
lemma CS(c a b:LB):(rk c a b).length=c.length:=(z4 c a b).1
lemma zY(c a b:LB):val (rk c a b)=(val a*val b) % 2^c.length:=(z4 c a b).2
lemma DO(c a b:LB):((val (rk c a b):Int) ≡ (val a:Int)*(val b:Int) [ZMOD (2:Int)^c.length]):=by rw[zY];exact_mod_cast (j7 (val a*val b) (2^c.length))
def kk(s:LB):LB:=s.filter id
lemma uc:U kk:=eU _ _ _ (fun (_:Unit) (b:Bo)=>((),if b then some true else none)) (fun _=>none) () fun s=>by
 induction s with|nil=>{rfl}|cons b r c=>{cases b <;> simp[cL,kk] at c ⊢ <;> exact c}
def tn(u:LB):LB:=if u.length % 2=1 then [true] else []
lemma yf:U tn:=by
 let d:Bo->Bo->Bo×Op Bo:=fun st _=>(!st,none);let c:Bo->Op Bo:=fun st=>if st then some true else none;refine eU _ _ _ d c false fun s=>?_
 have b:∀(st:Bo) (l:LB),cL d c st l=if (xor st (decide (l.length % 2=1))) then [true] else []:=by
  intro st l;induction l generalizing st with
  | nil=>cases st <;> rfl
  | cons _ r e=>simp only[cL,d,aX,e];cases st <;> by_cases h:r.length % 2=1 <;> simp[h] <;> omega
 simpa[tn] using (b false s).symm
def wh(y:LB):LB:=
 let d:=(aN y).1;let e:=(aN y).2;let b:=(aN e).1;let c:=(aN e).2
 Z d (Z b (rk d c b))
lemma Cx:U wh:=by have d:=f2;have b:=dI;have e:=aH b f2;have c:=aH b dI;exact D d (D e (CO d c e))
def rV(c b e:LB):LB:=
 let d:=wh^[e.length] (Z c (Z (dT c b) (oT c [true])))
 (aN (aN d).2).2
lemma CE{d h e:LB->LB}(c:U d)(j:U h)(i:U e):U (fun s=>rV (d s) (h s) (e s)):=by
 have b:=zM 6 Cx (fun y=>by dsimp only[wh];rw[G]) (fun y=>by
  dsimp only[wh];have q:=q0 y;have o:=q0 (aN y).2;rw[q7,q7,CS];omega)
  i (D c (D (qu c j) (Ay c (aG [true]))))
 exact ts (aH (aH b dI) dI) (fun _=>rfl)
lemma Ct(c b j:LB):(rV c b j).length=c.length/\val (rV c b j)=(val b)^j.length % 2^c.length:=by
 dsimp only[rV]
 have i:∀ k,∃ d,wh^[k] (Z c (Z (dT c b) (oT c [true])))=Z c (Z (dT c b) d)/\d.length=c.length/\val d=(val b)^k % 2^c.length:=by
  intro k;induction k with
  | zero=>refine⟨oT c [true],rfl,CQ _ _,by simp[zX]⟩
  | succ k q=>obtain⟨d,o,h,e⟩:=q;rw[jb,o];dsimp only[wh];simp only[G];refine⟨rk c d (dT c b),rfl,CS _ _ _,?_⟩;rw[zY,e,vI,Nat.mod_mul_mod,Nat.mul_mod_mod,gN]
 obtain⟨d,o,h,e⟩:=i j.length;rw[o];simp only[G];exact⟨h,e⟩
end MachineBits
namespace wZ
open Turing PEqualNP.Library Lib.Machines Lib.Universal
private def fh{c:Type}{b:c->Type}{Λ σ:Type}:Turing.TM2.Stmt b Λ σ->Set (Σ k,b k)
 | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,b k))∪ fh q
 | .peek _ _ q=>fh q
 | .pop _ _ q=>fh q
 | .load _ q=>fh q
 | .branch _ q₁ q₂=>fh q₁∪ fh q₂
 | .goto _=>∅
 | .halt=>∅
private lemma qt{h:Type}{e:h->Type}{Λ σ:Type}[Finite σ](q:Turing.TM2.Stmt e Λ σ):(fh q).Finite:=by induction q with|push _ _ _ d=>{exact (Set.finite_range _).union d}|peek _ _ _ d=>{exact d}|pop _ _ _ d=>{exact d}|load _ _ d=>{exact d}|branch _ _ _ c b=>{exact c.union b}|goto _=>{exact Set.finite_empty}|halt=>{exact Set.finite_empty}
private def fk{d:Type}[DecidableEq d]{c:d->Type}{Λ σ:Type}(T:∀ k,Set (c k)):∀(q:Turing.TM2.Stmt c Λ σ),(∀ k s,(⟨k,s⟩:Σ j,c j)∈fh q->s∈T k)->Turing.TM2.Stmt (fun k=>{s:c k // s∈T k}) Λ σ
 | .push k g q,h=>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩) (fk T q (fun j s b=>h j s (Or.inr b)))
 | .peek k f q,h=>.peek k (fun v o=>f v (o.map Subtype.val)) (fk T q h)
 | .pop k f q,h=>.pop k (fun v o=>f v (o.map Subtype.val)) (fk T q h)
 | .load a q,h=>.load a (fk T q h)
 | .branch f q₁ q₂,h=>.branch f (fk T q₁ (fun j s b=>h j s (Or.inl b))) (fk T q₂ (fun j s b=>h j s (Or.inr b)))
 | .goto f,_=>.goto f
 | .halt,_=>.halt
private def h9{d:Type}{c:d->Type}{Λ σ:Type}(T:∀ k,Set (c k))(b:Turing.TM2.Cfg (fun k=>{s:c k // s∈T k}) Λ σ):Turing.TM2.Cfg c Λ σ:=⟨b.l,b.var,fun k=>(b.stk k).map Subtype.val⟩
private lemma q9{r:Type}{o:r->Type}{Λ σ:Type}(T:∀ k,Set (o k)):Injective (h9 (Λ:=Λ) (σ:=σ) T):=by rintro⟨e,c,j⟩ ⟨d,b,i⟩ h;simp only[h9,Turing.TM2.Cfg.mk.injEq] at h;obtain⟨rfl,rfl,q⟩:=h;congr 1;funext k;exact List.map_injective_iff.mpr Subtype.val_injective (congrFun q k)
private lemma nm{c:Type}[DecidableEq c]{b:c->Type}(T:∀ k,Set (b k))(d:∀ k,Ls {s:b k // s∈T k})(k:c)(l:Ls {s:b k // s∈T k}):(fun j=>(update d k l j).map Subtype.val)=update (fun j=>(d j).map Subtype.val) k (l.map Subtype.val):=by funext j;by_cases h:j=k;{subst h;simp};{simp[h]}
private lemma qv{u:Type}[DecidableEq u]{h:u->Type}{Λ σ:Type}(T:∀ k,Set (h k))(q:Turing.TM2.Stmt h Λ σ)(i:∀ k s,(⟨k,s⟩:Σ j,h j)∈fh q->s∈T k)(v:σ)(e:∀ k,Ls {s:h k // s∈T k}):h9 T (stepAux (fk T q i) v e)=stepAux q v (fun k=>(e k).map Subtype.val):=by induction q generalizing v e with|push k g q d=>{simp only[fk,stepAux];rw[d,nm];rfl}|peek k f q d=>{simp only[fk,stepAux];exact (d i _ _).trans (by rw[List.head?_map])}|pop k f q d=>{simp only[fk,stepAux];exact (d i _ _).trans (by rw[nm,List.head?_map,List.map_tail])}|load a q d=>{simp only[fk,stepAux];exact d i (a v) e}|branch f r o c b=>{simp only[fk,stepAux];cases f v;{exact b _ v e};{exact c _ v e}}|goto f=>{rfl}|halt=>{rfl}
private lemma o0(c:Turing.TM2ComputableAux Bo Bo):∃ E:Turing.TM2ComputableAux Bo Bo,(∀ j,Finite (E.tm.Γ j))/\∀(x y:LB) (s:Nat),Turing.TM2OutputsInTime c.tm (x.map c.inputAlphabet.invFun) (some (y.map c.outputAlphabet.invFun)) s->Nonempty (Turing.TM2OutputsInTime E.tm (x.map E.inputAlphabet.invFun) (some (y.map E.outputAlphabet.invFun)) s):=by
 classical
 let _:DecidableEq c.tm.K:=c.tm.kDecidableEq;let _:Fintype c.tm.K:=c.tm.kFin;let _:Fintype c.tm.Λ:=c.tm.ΛFin;let _:Fintype c.tm.σ:=c.tm.σFin;let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
 let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k=>
  {s|k=c.tm.k₀\/k=c.tm.k₁\/
    (⟨k,s⟩:Σ j,c.tm.Γ j)∈⋃ l:c.tm.Λ,fh (c.tm.m l)}
 let q:{s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀:=
  { toFun:=Subtype.val
    invFun:=fun s=>⟨s,Or.inl rfl⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
 let o:{s:c.tm.Γ c.tm.k₁ // s∈T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁:=
  { toFun:=Subtype.val
    invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
 let e:Fintype {s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀}:=Fintype.ofEquiv _ q.symm
 let b:Turing.FinTM2:=
  { K:=c.tm.K
    kDecidableEq:=c.tm.kDecidableEq
    kFin:=c.tm.kFin
    k₀:=c.tm.k₀
    k₁:=c.tm.k₁
    Γ:=fun k=>{s:c.tm.Γ k // s∈T k}
    Λ:=c.tm.Λ
    main:=c.tm.main
    ΛFin:=c.tm.ΛFin
    σ:=c.tm.σ
    initialState:=c.tm.initialState
    σFin:=c.tm.σFin
    Γk₀Fin:=e
    m:=fun l=>fk T (c.tm.m l) (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
 have a3:∀ j:b.K,Finite (b.Γ j):=by
  intro j;by_cases S:j=c.tm.k₀;{subst S;exact Finite.of_fintype _}
  ·
   by_cases Q:j=c.tm.k₁;{subst Q;have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bo c.outputAlphabet.symm;exact Finite.of_equiv _ o.symm}
   ·
    have a1:(⋃ l:c.tm.Λ,fh (c.tm.m l)).Finite:=Set.finite_iUnion fun l=>qt (c.tm.m l);have:Finite ↥(⋃ l:c.tm.Λ,fh (c.tm.m l)):=a1.to_subtype;refine Finite.of_injective (f:=fun x:b.Γ j=>(⟨⟨j,x.1⟩,by
     rcases x.2 with h|h|h
     {exact (S h).elim};{exact (Q h).elim}
     · exact h⟩:↥(⋃ l:c.tm.Λ,fh (c.tm.m l)))) ?_
    intro x y a6;have a7:=aI (fun z=>z.1) a6;exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp a7).2)
 have r:∀ d:b.Cfg,Option.map (h9 T) (b.step d)=c.tm.step (h9 T d):=by
  rintro⟨l,v,M⟩;cases l with
  | none=>rfl
  | some l=>change some (h9 T (stepAux (fk T (c.tm.m l) _) v M))=some (stepAux (c.tm.m l) v (fun k=>(M k).map Subtype.val));exact aI some (qv T (c.tm.m l) _ v M)
 have w:∀(steps:Nat) (d:b.Cfg),Option.map (h9 T) ((flip bind b.step)^[steps] (some d))=(flip bind c.tm.step)^[steps] (some (h9 T d)):=by
  intro steps;induction steps with
  | zero=>intro d;rfl
  | succ steps P=>
    intro d;rw[jb,jb];cases hcur:(flip bind b.step)^[steps] (some d) with
    | none=>have i:=P d;rw[hcur] at i;rw[<- i];rfl
    | some a4=>have i:=P d;rw[hcur] at i;rw[<- i];exact r a4
 refine⟨⟨b,q.trans c.inputAlphabet,o.trans c.outputAlphabet⟩,a3,?_⟩;intro x y s h;refine⟨{ steps:=h.steps,evals_in_steps:=?_,steps_le_m:=h.steps_le_m }⟩;have u:=h.evals_in_steps;have L:h9 T (Turing.initList b (x.map (q.trans c.inputAlphabet).invFun))=Turing.initList c.tm (x.map c.inputAlphabet.invFun):=(by simp only[h9,Turing.initList];congr 1;funext k;by_cases B:k=c.tm.k₀;{subst B;dsimp only[b];simp only[↓reduceDIte,eq_mpr_eq_cast,cast_eq,gm];rfl};{dsimp only[b];simp only[B,↓reduceDIte,fC]});have a0:h9 T (Turing.haltList b (y.map (o.trans c.outputAlphabet).invFun))=Turing.haltList c.tm (y.map c.outputAlphabet.invFun):=(by simp only[h9,Turing.haltList];congr 1;funext k;by_cases B:k=c.tm.k₁;{subst B;dsimp only[b];simp only[↓reduceDIte,eq_mpr_eq_cast,cast_eq,gm];rfl};{dsimp only[b];simp only[B,↓reduceDIte,fC]});apply Option.map_injective (q9 T);rw[w,L,u];exact (aI some a0).symm
private lemma vz(n:Nat)(x:LB):hd (un n++false::x)=un n:=by simp[hd,un]
private lemma vU(n:Nat)(x:LB):jy (un n++false::x)=x:=by have h:(un n++false::x).dropWhile id=false::x:=(by simp[un]);simp[jy,h]
private lemma oi(p:Polynomial Nat):∃ a d:Nat,∀ m:Nat,1<=m->p.eval m<=a* m^d:=by induction p using Polynomial.induction_on' with|add p q o j=>{obtain⟨a,d,h⟩:=o;obtain⟨b,e,u⟩:=j;refine⟨a+b,d+e,fun m i=>?_⟩;rw[ly,Nat.add_mul];have s:m^d<=m^(d+e):=kI i (by omega);have r:m^e<=m^(d+e):=kI i (by omega);exact add_le_add ((h m i).trans (lz _ s)) ((u m i).trans (lz _ r))}|monomial d c=>{exact⟨c,d,fun m _=>by rw[uO]⟩}
private lemma lL(p:Polynomial Nat):∃ b,1<=b/\∀ m,p.eval m<=b* (m+ 1)^b:=by
 obtain⟨a,d,h⟩:=oi p;refine⟨a+ d+ 1,by omega,fun m=>?_⟩
 calc p.eval m<=p.eval (m+1):=yS p (by omega)
  _<=a* (m+ 1)^d:=h (m+ 1) (by omega)
  _<=(a+d+1)*(m+1)^(a+d+1):=nL (by omega) (kI (by omega) (by omega))
private lemma q3(d b c j e i o n w L:Nat)(B:1<=d)(z:1<=b)(h:b<=c)(M:j<=d* c)(x:e<=d* c)(E:i<=d* c)(v:n+ 2<=b)(q:w+ 1<=b)(y:L<=b)(K:o<=(w+ 1)* (e+ 2* L+ 3)+ 2* L+ 2* (n+ 2)+ (w+ 1)+ 5):j+ (2* ((n+ 2)+ (w+ 1))+ 2)+ (o+ (2* L+ 2)+ i)<=(3* d+ 25)* (b* c):=by
 have e1:(w+ 1)* (e+ 2* L+ 3)<=b* (d* c+ 2* b+ 3):=nL q (by omega);have e2:b* (d* c+ 2* b+ 3)=d* (b* c)+ 2* (b* b)+ 3* b:=(by ring);have S:b* b<=b* c:=lz b h;have Q:b<=b* c:=Nat.le_mul_of_pos_right b (by omega);have s:c<=b* c:=Nat.le_mul_of_pos_left c (by omega);have P:d* c<=d* (b* c):=lz d s;have r:(3* d+ 25)* (b* c)=3* (d* (b* c))+ 25* (b* c):=(by ring);rw[r];generalize b* c=u at *
 generalize d* u=AQ at *
 generalize d* c=AP at *
 generalize b* b=BB at *
 omega
private def m6(x:LB):LB:=true::(hd x++hd x++hd x++hd x)
private lemma nB(x:LB):(m6 x).length=4*(hd x).length+1:=by simp only[m6,aX,dL];omega
private def mx(x:LB):LB:=un ((x.length+2)^(4*(hd x).length+1))++false::x
private def ju(x:LB):LB×LB:=(true::false::x,m6 x)
private def ki(y:LB):LB:=dS (hd y) (MachineBits.m0 (jy y)++[true,true])++false::jy y
private lemma wW:U m6:=aC (aG [true]) (aC (aC (aC mB mB) mB) mB)
private lemma uB:ComputableInPolyTime (fun x:LB=>x) encodePair ju:=kv (aC (aG [true,false]) aR) wW
private lemma vC:U ki:=aC (MachineBits.jW mB (aC (aH k6 MachineBits.yD) (aG [true,true]))) (aC (aG [false]) k6)
private lemma qj(x:LB)(j:Nat):ki^[j] (true::false::x)=un ((x.length+2)^j)++false::x:=by induction j with|zero=>{rfl}|succ j c=>{rw[jb,c];show dS (hd (un ((x.length+2)^j)++false::x)) (MachineBits.m0 (jy (un ((x.length+2)^j)++false::x))++[true,true])++false::jy (un ((x.length+2)^j)++false::x)=_;rw[vz,vU];have b:dS (un ((x.length+2)^j)) (MachineBits.m0 x++[true,true])=un ((x.length+2)^(j+1)):=(by simp only[dS,J,dL,MachineBits.yZ,aX,mL,gN]);rw[b]}
private lemma tD(c b n w:Nat):b*((n+2)^(4*w+2))^(c+1)<=(n+2)^((b+4*(c+1))*(w+1)):=by
 have e:b<=(n+2)^b:=Nat.lt_two_pow_self.le.trans (pb (by omega) b);have d:b+(4*w+2)*(c+1)<=(b+4*(c+1))*(w+1):=(by nlinarith)
 calc b*((n+2)^(4*w+2))^(c+1)<=(n+2)^b*(n+2)^((4*w+2)*(c+1)):=by
       rw[<- pow_mul];exact nK _ e
  _=(n+2)^(b+(4*w+2)*(c+1)):=(j8 _ _ _).symm
  _<=(n+2)^((b+4*(c+1))*(w+1)):=kI (by omega) d
lemma wK(Q:LB->LB)(hG:U Q):∃(b4:Turing.TM2ComputableAux Bo Bo) (c:Nat),(∀ i,Finite (b4.tm.Γ i))/\∀(k:Nat) (d:LB),let x:=(replicate k true++[false])++d
 Nonempty (Turing.TM2OutputsInTime b4.tm (x.map b4.inputAlphabet.invFun) (some ((Q (replicate ((x.length+2)^(4*k+1)) true++false::x)).map b4.outputAlphabet.invFun)) ((x.length+2)^(c*(k+1)))):=by
 classical
 obtain⟨E⟩:=uB;obtain⟨o⟩:=vC;obtain⟨v⟩:=hG;obtain⟨A1,bw,b8⟩:=lL E.time;obtain⟨Ag,bu,b6⟩:=lL o.time;obtain⟨A3,bv,b7⟩:=lL v.time;let a6:Bo->o.tm.Γ o.tm.k₀:=o.inputAlphabet.invFun;let ad:o.tm.Γ o.tm.k₀->Bo:=o.inputAlphabet;let a5:o.tm.Γ o.tm.k₁->Bo:=o.outputAlphabet;let a7:FinTM2:=qB.nf o.tm a6 ad a5;let aj:a7.Γ a7.k₁->v.tm.Γ v.tm.k₀:=fun b=>v.inputAlphabet.invFun b;let d2:Op (v.tm.Γ v.tm.k₀):=some (v.inputAlphabet.invFun true);let M2:FinTM2:=comp a7 v.tm aj d2;let ae:E.tm.Γ E.tm.k₁->M2.Γ M2.k₀:=fun s=>E.outputAlphabet s;let d1:Op (M2.Γ M2.k₀):=some (Sum.inl true:Bo ⊕ Bo);let M1:FinTM2:=comp E.tm M2 ae d1;let u:=A1+Ag+A3;let az:=3*u+25
 have am:∀ z:LB,∃(s:Nat) (m:Ls (o.tm.Γ o.tm.k₁)),s<=o.time.eval z.length/\(flip bind (step o.tm.m))^[s] (some (initList o.tm (z.map a6)))=some (haltList o.tm m)/\m.map a5=ki z:=by
  intro z;refine⟨(o.outputsFun z).steps,List.map o.outputAlphabet.invFun (ki z),(o.outputsFun z).steps_le_m,(o.outputsFun z).evals_in_steps,?_⟩;rw[gm];conv_rhs=>rw[<- mN (ki z)]
  exact dF fun y _=>o.outputAlphabet.right_inv y
 have ag:∀ x:LB,∃ s,s<=(x.length+2)^((az+4*(u+1))*((hd x).length+1))/\(flip bind (step M1.m))^[s] (some (initList M1 (x.map E.inputAlphabet.invFun)))=some (haltList M1 ((Q (mx x)).map v.outputAlphabet.invFun)):=by
  intro x;let n:=x.length;let w:=(hd x).length;let L:=(n+2)^(4*w+1)+1+n;have hw:w<=n:=xQ x;have q:(mx x).length=L:=(by simp only[mx,dL,J,aX,L,n,w];omega);have M:=E.outputsFun x;have hL:∀ j≤(m6 x).length,(ki^[j] (true::false::x)).length<=L:=(by intro j hj;rw[qj];have bb:j<=4*w+1:=(by rw[nB] at hj;exact hj);have:(n+2)^j<=(n+2)^(4*w+1):=kI (by omega) bb;simp only[dL,J,aX,L,n] at this ⊢;omega);obtain⟨S,ar,a4⟩:=qB.Ch a6 ad a5 ki o.time (fun a=>o.inputAlphabet.right_inv a) am (true::false::x) (m6 x) L hL;have ah:ki^[(m6 x).length] (true::false::x)=mx x:=(by rw[nB,qj];rfl);rw[ah] at a4;have P:=v.outputsFun (mx x);obtain⟨a9,bk,-,ax⟩:=yO aj d2 (fun h=>by simp[d2] at h) (encodePair (ju x)) (mx x) ((Q (mx x)).map v.outputAlphabet.invFun)
   S P.steps a4 P.evals_in_steps
  have al:((encodePair (ju x)).map E.outputAlphabet.invFun).map ae=encodePair (ju x):=by
   rw[gm];conv_rhs=>rw[<- mN (encodePair (ju x))]
   exact dF fun y _=>E.outputAlphabet.right_inv y
  rw[<- al] at ax;obtain⟨nt,bq,-,ht⟩:=yO ae d1 (fun h=>by simp[d1] at h) (x.map E.inputAlphabet.invFun) ((encodePair (ju x)).map E.outputAlphabet.invFun) ((Q (mx x)).map v.outputAlphabet.invFun) M.steps a9 M.evals_in_steps ax;refine⟨nt,?_,ht⟩;have ba:((encodePair (ju x)).map E.outputAlphabet.invFun).length=(n+2)+(4*w+1):=(by simp only[ft,ju,Lib.Machines.d9,aX,nB,n,w]);have ap:nt<=M.steps+(2*((n+2)+(4*w+1))+2)+a9:=(by omega);have b9:a9<=S+(2*L+2)+P.steps:=(by have e:List.length (α:=a7.Γ a7.k₁) (mx x)=L:=q;omega);let B:=(n+2)^(4*w+2);have bi:1<=B:=Nat.one_le_pow _ _ (by omega)
  have bf:n+2<=B:=by
   calc n+2=(n+2)^1:=(pow_one _).symm
    _<=(n+2)^(4*w+2):=kI (by omega) (by omega)
  have be:4*w+1<=B:=by
   calc 4*w+1<=4*n+1:=by omega
    _<=(n+2)^2:=by nlinarith
    _<=(n+2)^(4*w+2):=kI (by omega) (by omega)
  have av:L+1<=B:=by
   have h1:n+2<=(n+2)^(4*w+1):=by
    calc n+2=(n+2)^1:=(pow_one _).symm
     _<=(n+2)^(4*w+1):=kI (by omega) (by omega)
   have h2:2*(n+2)^(4*w+1)<=(n+2)*(n+2)^(4*w+1):=nK _ (by omega);have h3:(n+2)*(n+2)^(4*w+1)=B:=(by simp only[B,pow_succ']);simp only[L];omega
  let K:=B^u;have bh:B<=K:=Nat.le_self_pow (by omega) B;have a2:∀(Ai m:Nat),Ai<=u->m+1<=B->Ai*(m+1)^Ai<=u*K:=(by intro Ai m aw hm;exact nL aw ((pb hm Ai).trans (kI (by omega) aw)));have b1:M.steps<=u*K:=M.steps_le_m.trans ((b8 _).trans (a2 A1 n (by omega) (by omega)));have bg:o.time.eval L<=u*K:=(b6 L).trans (a2 Ag L (by omega) av);have bj:Polynomial.eval (mx x).length v.time<=u*K:=(by rw[q];exact (b7 L).trans (a2 A3 L (by omega) av));have b3:P.steps<=u*K:=P.steps_le_m.trans bj;have aq:S<=(4*w+1)*(o.time.eval L+2*L+3)+2*L+2*(n+2)+(4*w+1)+5:=(by have e:(m6 x).length=4*w+1:=nB x;have e':(true::false::x).length=n+2:=rfl;rw[e,e'] at ar;exact ar);have hA:1<=u:=(by omega)
  have bd:=q3 u B K M.steps (o.time.eval L) P.steps S n (4*w) L hA bi bh b1 bg b3
   bf be (by omega) aq
  have au:B*K=B^(u+1):=(by simp only[K];rw[gN,kP]);have a3:=tD u az n w
  calc nt<=M.steps+(2*((n+2)+(4*w+1))+2)+a9:=ap
   _<=M.steps+(2*((n+2)+(4*w+1))+2)+(S+(2*L+2)+P.steps):=by omega
   _<=az*(B*K):=bd
   _=az*((n+2)^(4*w+2))^(u+1):=by rw[au]
   _<=_:=a3
 let Mx:Turing.TM2ComputableAux Bo Bo:=⟨M1,E.inputAlphabet,v.outputAlphabet⟩;obtain⟨M',a3,aa⟩:=o0 Mx;refine⟨M',az+4*(u+1),a3,fun k d=>?_⟩;let x:=(replicate k true++[false])++d
 have bc:hd x=replicate k true:=by
  have:x=un k++false::d:=by simp[x,un]
  rw[this];exact vz k d
 have r:(hd x).length=k:=(by rw[bc,sy]);have ao:mx x=replicate ((x.length+2)^(4*k+1)) true++false::x:=(by simp only[mx,r,un])
 have an:=aa x (Q (mx x)) _ {
  steps:=Classical.choose (ag x)
  evals_in_steps:=(f9 (ag x)).2
  steps_le_m:=(f9 (ag x)).1
 }
 simpa only[ao,r] using an
end wZ
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal MachineBits
def left(s:LB):LB:=(aN s).1
def right(s:LB):LB:=(aN s).2
lemma aD{f:LB->LB}(h:U f):U (fun s=>left (f s)):=aH h f2
lemma Y{f:LB->LB}(h:U f):U (fun s=>right (f s)):=aH h dI
lemma wF{f:LB->LB}(h:U f):U (fun s=>(f s).tail):=aH h rz
lemma wG{f g:LB->LB}(h:U f)(b:U g):U (fun s=>(g s).take (f s).length):=ts (sf h b) (fun s=>vZ (f s) (g s))
lemma x5{f g:LB->LB}(h:U f)(b:U g):U (fun s=>(g s).drop (f s).length):=ts (gW h b) (fun s=>xS (f s) (g s))
def oo(c:LB->LB->LB->LB)(f:LB->LB)(y:LB):LB:=
 let d:=left y;let b:=(left (right y)).tail;let args:=left (right (right y));let e:=right (right (right y))
 Z d (Z b (Z args (c d (f (Z b (Z args e))) e)))
lemma xI{d:LB->LB->LB->LB}(i:∀ {u v w:LB->LB},U u->U v->U w->U (fun s=>d (u s) (v s) (w s))){f:LB->LB}(j:U f):U (oo d f):=by have e:=aD aR;have b:=wF (aD (Y aR));have c:=aD (Y (Y aR));have h:=Y (Y (Y aR));exact D e (D b (D c (i e (aH (D b (D c h)) j) h)))
lemma uv{b:LB->LB->LB->LB}(c:∀ d val e,(b d val e).length<=d.length+e.length)(f:LB->LB)(y:LB):(oo b f y).length<=y.length+3*(left y).length+3:=by have j:=ni y;have i:=ni (right y);have h:=ni (right (right y));have q:=c (left y) (f (Z (left (right y)).tail (Z (left (right (right y))) (right (right (right y)))))) (right (right (right y)));have o:(left (right y)).tail.length<=(left (right y)).length:=(by simp);change 2*(left y).length+(right y).length<=y.length at j;change 2*(left (right y)).length+(right (right y)).length<=(right y).length at i;change 2*(left (right (right y))).length+(right (right (right y))).length<=(right (right y)).length at h;simp only[oo,rT];omega
def km(c:LB->LB->LB->LB)(f:LB->LB)(d b args e:LB):LB:=
 right (right (right ((oo c f)^[b.length] (Z d (Z (un b.length) (Z args e))))))
lemma mA{c:LB->LB->LB->LB}(i:∀ {u v w:LB->LB},U u->U v->U w->U (fun s=>c (u s) (v s) (w s)))(r:∀ e val h,(c e val h).length<=e.length+h.length){f e d args h:LB->LB}(L:U f)(x:U e)(b:U d)(o:U args)(z:U h):U (fun s=>km c f (e s) (d s) (args s) (h s)):=by have j:=D x (D (aH b yD) (D o z));have q:=zM 3 (xI i L) (fun y=>by simp only[oo,G,left]) (uv r f) b j;exact Y (Y (Y q))
lemma vW(b:LB->LB->LB->LB)(f:LB->LB)(c args:LB)(n:Nat)(d:LB):(oo b f)^[n] (Z c (Z (un n) (Z args d)))=Z c (Z [] (Z args ((List.range n).foldr (fun i x=>b c (f (Z (un i) (Z args x))) x) d))):=by induction n generalizing d with|zero=>{simp}|succ n e=>{rw[eo,nQ,List.foldr_append];simp only[oo,left,right,G,rv,jF,sA,List.foldr_nil];exact e _}
lemma kn(c:LB->LB->LB->LB)(f:LB->LB)(d b args e:LB):km c f d b args e=(List.range b.length).foldr (fun i x=>c d (f (Z (un i) (Z args x))) x) e:=by simp only[km,vW,right,G]
def lG(b val c:LB):LB:=val.take b.length++c
def f5(cap val _:LB):LB:=val.take cap.length
lemma tF{u v w:LB->LB}(d:U u)(c:U v)(b:U w):U (fun s=>lG (u s) (v s) (w s)):=aC (wG d c) b
lemma oV{u v w:LB->LB}(c:U u)(b:U v)(_:U w):U (fun s=>f5 (u s) (v s) (w s)):=wG c b
lemma rC(b val c:LB):(lG b val c).length<=b.length+c.length:=by simp[lG]
lemma m2(b val c:LB):(f5 b val c).length<=b.length+c.length:=by simp[f5]
def bX(f:LB->LB)(c b args:LB):LB:=km lG (fun s=>f (Z (left s) (left (right s)))) c b args []
lemma bW{f d b args:LB->LB}(e:U f)(c:U d)(h:U b)(i:U args):U (fun s=>bX f (d s) (b s) (args s)):=mA tF rC (aH (D (aD aR) (aD (Y aR))) e) c h i (aG [])
lemma bA(f:LB->LB)(c b args:LB)(h:∀ i<b.length,(f (Z (un i) args)).length<=c.length):bX f c b args=(List.range b.length).flatMap (fun i=>f (Z (un i) args)):=by
 simp only[bX,kn,left,right,G,lG]
 have r (L:Ls Nat) (d:∀ i∈L,i<b.length):
  L.foldr (fun i x=>(f (Z (un i) args)).take c.length++x) []=L.flatMap (fun i=>f (Z (un i) args)):=by
  induction L with|nil=>{rfl}|cons i L e=>{simp[o8 (h i (d i (by simp))),e (fun j o=>d j (by simp[o]))]}
 exact r _ (fun i q=>aY.mp q)
def eN(c d b:LB):LB:=(b.drop (c.length*d.length)).take c.length
lemma ku{w i s:LB->LB}(b:U w)(d:U i)(c:U s):U (fun x=>eN (w x) (i x) (s x)):=ts (wG b (x5 (jW b d) c)) (fun x=>by simp[eN,dS])
lemma fo{d:Type*}(L:Ls d)(f:d->LB)(w:LB)(i:Nat)(h:i<L.length)(e:∀ a∈L,(f a).length=w.length):eN w (un i) (L.flatMap f)=f L[i]:=by
 induction L generalizing i with
 | nil=>simp at h
 | cons a L j=>
   have c:=e a (by simp);have q:∀ b∈L,(f b).length=w.length:=fun b o=>e b (by simp[o]);cases i with
   | zero=>simp only[eN,J,Nat.mul_zero,sZ,eY,List.getElem_cons_zero];rw[<- c,List.take_left]
   | succ i=>simp only[eN,J,eY,List.getElem_cons_succ];rw[Nat.mul_succ,Nat.add_comm,<- c,List.drop_length_add_append,c];simpa only[eN,J] using j i (by simp at h;omega) q
def rh(w v a:LB):LB:=nj w v a
lemma xJ{u v w:LB->LB}(d:U u)(c:U v)(b:U w):U (fun s=>rh (u s) (v s) (w s)):=Az d c b
lemma uw(w v a:LB):(rh w v a).length<=w.length+a.length:=by rw[rh,y0];omega
def iv(f:LB->LB)(w b args:LB):LB:=km rh (fun s=>f (Z (left s) (left (right s)))) w b args (fJ w)
lemma kb{f w c a:LB->LB}(d:U f)(b:U w)(e:U c)(h:U a):U (fun s=>iv f (w s) (c s) (a s)):=mA xJ uw (aH (D (aD aR) (aD (Y aR))) d) b e h (aH b g2)
lemma pV(f:LB->LB)(w b args:LB):(iv f w b args).length=w.length:=by
 simp only[iv,kn];cases List.range b.length with
 | nil=>exact zN w
 | cons i L=>exact y0 _ _ _
def rep(w b:LB)(z:Int):Prop:=(val b:Int) ≡ z [ZMOD (2:Int)^w.length]
lemma h6(w:LB):rep w (fJ w) 0:=by simp[rep,Ax]
lemma xe(w u:LB):rep w (oT w u) (u.length:Int):=by rw[rep,zX];exact_mod_cast (j7 u.length (2^w.length))
lemma xd{w a b:LB}{x y:Int}(d:rep w a x)(c:rep w b y):rep w (nj w a b) (x+y):=(DR w a b).trans (d.add c)
lemma y1{w a b:LB}{x y:Int}(d:rep w a x)(c:rep w b y):rep w (rk w a b) (x*y):=(DO w a b).trans (d.mul c)
lemma xf{w a:LB}{x:Int}(b:rep w a x):rep w (ti w a) (-x):=(Co w a).trans b.neg
lemma y2{w a:LB}{x:Int}(b:rep w a x)(e:LB):rep w (rV w a e) (x^e.length):=by have h:(val (rV w a e):Int) ≡ (val a:Int)^e.length [ZMOD (2:Int)^w.length]:=(by rw[(Ct w a e).2];exact_mod_cast (j7 ((val a)^e.length) (2^w.length)));exact h.trans (b.pow _)
lemma i7(f:LB->LB)(w b args:LB)(z:Nat->Int)(h:∀ i<b.length,rep w (f (Z (un i) args)) (z i)):rep w (iv f w b args) ((List.range b.length).map z).sum:=by
 simp only[iv,kn,left,right,G,rh];generalize c:List.range b.length=L;have d:∀ i∈L,i<b.length:=(by simp[<- c]);clear c;induction L with
 | nil=>exact h6 w
 | cons i L e=>simp only[sA,aO,eu];exact xd (h i (d i (by simp))) (e (fun j o=>d j (by simp[o])))
lemma vM{w b:LB}{z:Nat}(c:b.length=w.length)(h:rep w b (z:Int))(i:z<2^w.length):val b=z:=by have j:val b<2^w.length:=c▸yX b;have e:(val b:Int)<(2:Int)^w.length:=(by exact_mod_cast j);have d:(z:Int)<(2:Int)^w.length:=(by exact_mod_cast i);unfold rep Int.ModEq at h;rw[Int.emod_eq_of_lt (by positivity) e,Int.emod_eq_of_lt (by positivity) d] at h;exact_mod_cast h
def dQ(i x:LB):LB:=pU (x.drop i.length)
lemma dK{i x:LB->LB}(c:U i)(b:U x):U (fun s=>dQ (i s) (x s)):=aH (x5 c b) xR
lemma eG(i x:LB):dQ i x=cF (x.getD i.length false):=by
 unfold dQ;generalize i.length=j;induction j generalizing x with
 | zero=>cases x with|nil=>rfl|cons b l=>cases b <;> rfl
 | succ j c=>cases x with|nil=>rfl|cons b l=>exact c l
end Packed
open Finset (card_le_card union_empty mem_image)
namespace L853.R012.TightReadOnce
open PEqualNP.CircuitLowerBounds
def en(b:Ls Gate)(w:LB):LB:=b.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
lemma yE(C:Circuit)(x:LB):C.wires x=en C.gates x:=rfl
lemma lZ(c b:Ls Gate)(w:LB):en (c++b) w=en b (en c w):=by simp[en,List.foldl_append]
lemma pW(b:Ls Gate):∀ w:LB,∃ t:LB,en b w=w++t/\t.length=b.length:=by induction b with|nil=>{intro w;exact⟨[],by simp[en],rfl⟩}|cons g b c=>{intro w;obtain⟨t,d,e⟩:=c (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]);refine⟨g.op.eval (g.inputs.map fun i=>w.getD i false)::t,?_,by simp[e]⟩;have:en (g::b) w=en b (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl;rw[this,d];simp}
lemma jS(b:Ls Gate)(w:LB):(en b w).length=w.length+b.length:=by obtain⟨t,c,d⟩:=pW b w;rw[c];simp[d]
lemma nc(b:Ls Gate)(w:LB)(i:Nat)(h:i<w.length):(en b w).getD i false=w.getD i false:=by obtain⟨t,c,_⟩:=pW b w;rw[c,List.getD_append _ _ _ _ h]
def Ok(g:Gate):Prop:=g.inputs.length<=2
variable {n:Nat}
lemma f3{b:Type}(L:Ls b)(e d:b)(j:Nat)(h:j≠L.length):(L++[e]).getD j d=L.getD j d:=by by_cases c:j<L.length;{exact List.getD_append _ _ _ _ c};{rw[mE _ _ (by simp;omega),mE _ _ (by omega)]}
lemma fI{b:Type}(L:Ls b)(c d:b):(L++[c]).getD L.length d=c:=by simp
def jo(g:Gate):Ls Nat:=match g.op with
 | .not=>g.inputs.take 1
 | _=>g.inputs
lemma wj(g:Gate):(jo g).length<=g.inputs.length:=by cases h:g.op <;> simp[jo,h]
def f7(L:Ls (Fv n))(g:Gate):Fv n:=((jo g).map fun a=>L.getD a ∅).foldr (· ∪ ·) ∅
lemma tT(l:Ls Nat)(F:Nat->Fv n)(i:Fin n):i∈(l.map F).foldr (· ∪ ·) ∅↔∃ a∈l,i∈F a:=by induction l with|nil=>{simp}|cons b l c=>{simp[c]}
lemma mD(L:Ls (Fv n))(g:Gate)(i:Fin n):i∈f7 L g↔∃ a∈jo g,i∈L.getD a ∅:=tT _ _ _
def mv(b:Ls Gate)(L:Ls (Fv n)):Ls (Fv n):=b.foldl (fun L g=>L++[f7 L g]) L
def fb(n:Nat):Ls (Fv n):=ofFn fun i:Fin n=>{i}
def xo(x y:Fin n->Bo)(L:Ls (Fv n))(w b:LB):Prop:=L.length=w.length/\w.length=b.length/\∀ j:Nat,(∀ i∈L.getD j ∅,x i=y i)->w.getD j false=b.getD j false
lemma tf(g:Gate)(w b:LB)(h:∀ a∈jo g,w.getD a false=b.getD a false):g.op.eval (g.inputs.map fun a=>w.getD a false)=g.op.eval (g.inputs.map fun a=>b.getD a false):=by
 by_cases c:g.op=.not
 ·
  rw[c];cases hi:g.inputs with
  | nil=>simp[GateOp.eval]
  | cons a l=>have d:=h a (by simp[jo,c,hi]);change (!w.getD a false)=!b.getD a false;rw[d]
 {have e:g.inputs.map (fun a=>w.getD a false)=g.inputs.map (fun a=>b.getD a false):=(by apply dF;intro a d;exact h a (by cases ho:g.op <;> simp_all [jo]));rw[e]}
lemma pD(x y:Fin n->Bo)(d:Ls Gate):∀(L:Ls (Fv n)) (w b:LB),xo x y L w b->xo x y (mv d L) (en d w) (en d b):=by induction d with|nil=>{intro L w b h;exact h}|cons g d s=>{intro L w b h;obtain⟨r,q,o⟩:=h;apply s (L++[f7 L g]) (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) (b++[g.op.eval (g.inputs.map fun i=>b.getD i false)]);refine⟨by simp[r],by simp[q],?_⟩;intro j e;by_cases c:j=L.length;{subst c;rw[fI] at e;rw[r,fI,q,fI];apply tf;intro a v;exact o a (fun i u=>e i ((mD L g i).2 ⟨a,v,u⟩))};{rw[f3 _ _ _ _ c] at e;rw[f3 _ _ _ _ (by omega),f3 _ _ _ _ (by omega)];exact o j e}}
lemma rM(x y:Fin n->Bo):xo x y (fb n) (ofFn x) (ofFn y):=by refine⟨by simp[fb],by simp,?_⟩;intro j d;by_cases b:j<n;{have c:x ⟨j,b⟩=y ⟨j,b⟩:=d _ (by simp[fb,b]);simp[b,c]};{rw[mE _ _ (by simp;omega),mE _ _ (by simp;omega)]}
def xq(t:Nat)(L:Ls (Fv n)):Prop:=∀ W:Ft Nat,(W.biUnion fun j=>L.getD j ∅).card<=t+W.card
lemma oQ:xq 0 (fb n):=by intro W;refine mS Finset.card_biUnion_le ?_;rw[lE,Finset.card_eq_sum_ones];apply Finset.sum_le_sum;intro j _;by_cases b:j<n;{simp[fb,b]};{rw[mE _ _ (by simp[fb];omega)];simp}
lemma wa(t:Nat)(L:Ls (Fv n))(g:Gate)(x:g.inputs.length<=2)(h:xq t L):xq (t+1) (L++[f7 L g]):=by
 intro W;by_cases u:L.length∈W
 ·
  have d:(W.biUnion fun j=>(L++[f7 L g]).getD j ∅)
   ⊆((W.erase L.length ∪ (jo g).toFinset).biUnion fun j=>L.getD j ∅):=by
   intro i v;rw[bT] at v ⊢;obtain⟨j,o,b⟩:=v;by_cases c:j=L.length;{subst c;rw[fI] at b;obtain⟨a,z,q⟩:=(mD L g i).1 b;exact⟨a,jB _ (dO.2 z),q⟩};{rw[f3 _ _ _ _ c] at b;exact⟨j,ga _ (fL.2 ⟨c,o⟩),b⟩}
  have y:(W.erase L.length ∪ (jo g).toFinset).card<=(W.card-1)+2:=(by refine mS (Finset.card_union_le _ _) ?_;rw[uR u];exact Nat.add_le_add_left (mS (u1 _) (mS (wj g) x)) _);have s:1<=W.card:=Finset.card_pos.2 ⟨_,u⟩
  have:=h (W.erase L.length ∪ (jo g).toFinset)
  have:=card_le_card d
  omega
 ·
  have r:(W.biUnion fun j=>(L++[f7 L g]).getD j ∅)=(W.biUnion fun j=>L.getD j ∅):=(by apply Finset.biUnion_congr rfl;intro j w;exact f3 _ _ _ _ (fun e=>u (e▸w)));rw[r]
  have:=h W
  omega
lemma qY(b:Ls Gate):∀(t:Nat) (L:Ls (Fv n)),(∀ g∈b,Ok g)->xq t L->xq (t+b.length) (mv b L):=by
 induction b with
 | nil=>intro t L _ h;exact h
 | cons g b e=>
   intro t L c h
   have:=e (t+1) (L++[f7 L g]) (fun i d=>c i (g9 _ d)) (wa t L g (c g gK) h)
   rw[aX,show t+(b.length+1)=t+1+b.length by omega];exact this
lemma kW(C:Circuit)(n k w:Nat)(c:k<=C.gates.length)(b:w<n+k)(x:Fin n->Bo):(C.wires (ofFn x)).getD w false=(en (C.gates.take k) (ofFn x)).getD w false:=by
 change (en C.gates (ofFn x)).getD w false=_;conv_lhs=>rw[<- List.take_append_drop k C.gates]
 rw[lZ];apply nc;rw[jS];simpa[pa,sW c] using b
lemma v7(C:Circuit)(n k w:Nat)(d:k<=C.gates.length)(h:w<n+k)(b:∀ g∈C.gates,g.inputs.length<=2):∃ c:Fv n,c.card<=k+1/\∀ x y:Fin n->Bo,(∀ i∈c,x i=y i)->(C.wires (ofFn x)).getD w false=(C.wires (ofFn y)).getD w false:=by let c:=(mv (C.gates.take k) (fb n)).getD w ∅;refine⟨c,?_,?_⟩;{have o:=qY (C.gates.take k) 0 (fb n) (fun g j=>b g (List.mem_of_mem_take j)) oQ {w};simpa only[uP,sC,lE,pa,sW d] using o};{intro x y e;rw[kW C n k w d h x,kW C n k w d h y];exact (pD x y (C.gates.take k) _ _ _ (rM x y)).2.2 w e}
lemma qw(C:Circuit)(n k w:Nat)(u:k<=C.gates.length)(s:w<n+k)(d:∀ g∈C.gates,g.inputs.length<=2)(r:Fv n)(b:∀ i∈r,∃ x y:Fin n->Bo,(∀ j,j≠i->x j=y j)/\(C.wires (ofFn x)).getD w false≠(C.wires (ofFn y)).getD w false):r.card<=k+1:=by obtain⟨B,c,e⟩:=v7 C n k w u s d;apply mS (card_le_card (t:=B) ?_) c;intro i L;by_contra o;obtain⟨x,y,h,q⟩:=b i L;apply q (e x y ?_);intro j z;apply h j;intro v;subst j;exact o z
def RO(h:Fv n)(f:(Fin n->Bo)->Bo):Prop:=∀ c:Fv n->((Fin n->Bo)->Bo)->Prop,(∀ i:Fin n,c {i} (fun x=>x i))->(∀ e d a b,Disjoint e d->c e a->c d b->c (e ∪ d) (fun x=>a x&&b x)/\c (e ∪ d) (fun x=>a x||b x))->c h f
lemma kZ(i:Fin n):RO {i} (fun x=>x i):=fun _ hl _=>hl i
lemma qe{d c:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint d c)(o:RO d a)(j:RO c b):RO (d ∪ c) (fun x=>a x&&b x):=fun i h e=>(e d c a b hd (o i h e) (j i h e)).1
lemma rq{d c:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint d c)(o:RO d a)(j:RO c b):RO (d ∪ c) (fun x=>a x||b x):=fun i h e=>(e d c a b hd (o i h e) (j i h e)).2
def Df(L:Ls (Fv n))(F:Nat->(Fin n->Bo)->Bo)(W:Ft Nat):Prop:=(∀ w∈W,RO (L.getD w ∅) (F w))/\(∀ w∈W,∀ v∈W,w≠v->Disjoint (L.getD w ∅) (L.getD v ∅))
def tC(t:Nat)(L:Ls (Fv n))(F:Nat->(Fin n->Bo)->Bo):Prop:=∀ W:Ft Nat,(W.biUnion fun j=>L.getD j ∅).card=t+W.card->Df L F W
lemma v5:tC 0 (fb n) (fun j x=>(ofFn x).getD j false):=by intro W o;have b:∀ j∈W,j<n:=(by intro j c;by_contra y;have s:(fb n).getD j ∅=∅:=mE _ _ (by simp[fb];omega);have r:=o;rw[<- qJ c,Finset.biUnion_insert,s,Finset.empty_union] at r;rw[qJ c] at r;have z:=oQ (n:=n) (W.erase j);have q:=Finset.card_erase_add_one c;omega);constructor;{intro j c;have d:=b j c;have u:(fb n).getD j ∅={⟨j,d⟩}:=(by simp[fb,d]);have w:(fun x:Fin n->Bo=>(ofFn x).getD j false)=(fun x=>x ⟨j,d⟩):=(by funext x;simp[d]);rw[u];change RO {⟨j,d⟩} (fun x:Fin n->Bo=>(ofFn x).getD j false);rw[w];exact kZ _};{intro j c k v e;have i:=b j c;have h:=b k v;simpa[fb,i,h,Fin.ext_iff] using e}
lemma xm(L:Ls (Fv n))(g:Gate)(W:Ft Nat)(r:L.length∈W):(W.biUnion fun j=>(L++[f7 L g]).getD j ∅)=((W.erase L.length ∪ (jo g).toFinset).biUnion fun j=>L.getD j ∅):=by
 ext i;constructor;{intro d;rw[bT] at d ⊢;obtain⟨j,h,b⟩:=d;by_cases c:j=L.length;{subst c;rw[fI] at b;obtain⟨a,q,o⟩:=(mD L g i).1 b;exact⟨a,jB _ (dO.2 q),o⟩};{rw[f3 _ _ _ _ c] at b;exact⟨j,ga _ (fL.2 ⟨c,h⟩),b⟩}}
 ·
  intro d;obtain⟨j,e,d⟩:=bT.mp d;rcases cD.mp e with e|e
  {refine bT.mpr ⟨j,jA e,?_⟩;rw[f3 _ _ _ _ (uX e)];exact d};{refine bT.mpr ⟨L.length,r,?_⟩;rw[fI];exact (mD L g i).mpr ⟨j,dO.mp e,d⟩}
lemma tI(g:Gate)(r:g.op=.and\/g.op=.or\/g.op=.not)(i:g.inputs.length<=2)(d:(jo g).toFinset.card=2):∃ a b,g.inputs=[a,b]/\a≠b/\(g.op=.and\/g.op=.or):=by
 have o:g.op≠.not:=(by intro o;have u:=u1 (jo g);have s:(jo g).length<=1:=(by simp[jo,o]);omega);have e:g.op=.and\/g.op=.or:=by rcases r with h|h|h <;> simp_all
 have q:jo g=g.inputs:=by rcases e with h|h <;> simp[jo,h]
 rw[q] at d;rcases hi:g.inputs with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩
 {simp[hi] at d};{simp[hi] at d};{refine⟨a,b,rfl,?_,e⟩;intro j;simp[hi,j] at d};{simp[hi] at i}
def ox(L:Ls (Fv n))(F:Nat->(Fin n->Bo)->Bo)(g:Gate)(j:Nat)(x:Fin n->Bo):Bo:=if j=L.length then g.op.eval (g.inputs.map fun a=>F a x) else F j x
lemma xl(t:Nat)(L:Ls (Fv n))(F:Nat->(Fin n->Bo)->Bo)(g:Gate)(ho:g.op=.and\/g.op=.or\/g.op=.not)(a6:g.inputs.length<=2)(hc:xq t L)(ht:tC t L F):tC (t+1) (L++[f7 L g]) (ox L F g):=by
 intro W ae
 have hW:L.length∈W:=by
  by_contra hn;have hU:(W.biUnion fun j=>(L++[f7 L g]).getD j ∅)=(W.biUnion fun j=>L.getD j ∅):=(by apply Finset.biUnion_congr rfl;intro j hj;exact f3 _ _ _ _ (fun h=>hn (h▸hj)));rw[hU] at ae
  have:=hc W
  omega
 let o:=W.erase L.length;let B:=(jo g).toFinset;let E:=o ∪ B;have b0:o.card+1=W.card:=Finset.card_erase_add_one hW;have b1:B.card<=2:=mS (u1 _) (mS (wj g) a6);have az:E.card<=o.card+B.card:=Finset.card_union_le _ _;have hU:(W.biUnion fun j=>(L++[f7 L g]).getD j ∅)=(E.biUnion fun j=>L.getD j ∅):=xm L g W hW;rw[hU] at ae;have ay:=hc E;have al:B.card=2:=(by omega);have y:E.card=o.card+B.card:=(by omega);have u:(E.biUnion fun j=>L.getD j ∅).card=t+E.card:=(by omega);have ah:Disjoint o B:=Finset.card_union_eq_card_add_card.mp y;obtain⟨a,b,a7,aj,r⟩:=tI g ho a6 al;have d:jo g=[a,b]:=by rcases r with h|h <;> simp[jo,h,a7]
 have ag:a∈B:=(by simp[B,d]);have af:b∈B:=(by simp[B,d]);have P:a∈E:=jB _ ag;have Q:b∈E:=jB _ af;have K:=ht E u;have z:o⊆E:=Finset.subset_union_left;have aa:∀ w∈o,w≠a:=(by intro w i ar;subst w;exact aT.mp ah i ag);have a9:∀ w∈o,w≠b:=(by intro w i aq;subst w;exact aT.mp ah i af);have hS:f7 L g=L.getD a ∅ ∪ L.getD b ∅:=(by simp[f7,d])
 have a8:RO (f7 L g) (ox L F g L.length):=by
  rw[hS];have hd:=K.2 a P b Q aj;rcases r with r|r
  {have M:ox L F g L.length=(fun x=>F a x&&F b x):=(by funext x;simp[ox,a7,r,GateOp.eval]);rw[M];exact qe hd (K.1 a P) (K.1 b Q)};{have M:ox L F g L.length=(fun x=>F a x||F b x):=(by funext x;simp[ox,a7,r,GateOp.eval]);rw[M];exact rq hd (K.1 a P) (K.1 b Q)}
 have c:∀ w∈o,(L++[f7 L g]).getD w ∅=L.getD w ∅:=fun w i=>f3 _ _ _ _ (uX i);have e:∀ w∈o,Disjoint (f7 L g) (L.getD w ∅):=(by intro w i;rw[hS,Finset.disjoint_union_left];exact⟨K.2 a P w (z i) (aa w i).symm,K.2 b Q w (z i) (a9 w i).symm⟩);constructor;{intro w i;by_cases S:w=L.length;{subst w;rw[fI];exact a8};{have q:w∈o:=fL.mpr ⟨S,i⟩;rw[c w q];have M:ox L F g w=F w:=(by funext x;simp[ox,S]);rw[M];exact K.1 w (z q)}};{intro w i v hv ab;by_cases S:w=L.length;{subst w;have s:v∈o:=fL.mpr ⟨ab.symm,hv⟩;rw[fI,c v s];exact e v s};{have q:w∈o:=fL.mpr ⟨S,i⟩;rw[c w q];by_cases ai:v=L.length;{subst v;rw[fI];exact (e w q).symm};{have s:v∈o:=fL.mpr ⟨ai,hv⟩;rw[c v s];exact K.2 w (z q) v (z s) ab}}}
lemma tY(b:Ls Gate):∀(t:Nat) (L:Ls (Fv n)) (v:(Fin n->Bo)->LB),(∀ x,(v x).length=L.length)->(∀ g∈b,(g.op=.and\/g.op=.or\/g.op=.not)/\g.inputs.length<=2)->xq t L->tC t L (fun j x=>(v x).getD j false)->tC (t+b.length) (mv b L) (fun j x=>(en b (v x)).getD j false):=by induction b with|nil=>{intro t L v i _ s r;exact r}|cons g b y=>{intro t L v i w s r;let c:=fun x:Fin n->Bo=>v x++[g.op.eval (g.inputs.map fun a=>(v x).getD a false)];have o:∀ x,(c x).length=(L++[f7 L g]).length:=(by intro x;simp[c,i x]);have z:(fun j x=>(c x).getD j false)=ox L (fun j x=>(v x).getD j false) g:=(by funext j x;by_cases u:j=L.length;{subst j;simp only[ox,ite_true];dsimp only[c];rw[<- i x,fI]};{simp only[ox,u,ite_false];exact f3 _ _ _ _ (by rw[i x];exact u)});have d:=w g gK;have q:tC (t+1) (L++[f7 L g]) (fun j x=>(c x).getD j false):=(by rw[z];exact xl t L _ g d.1 d.2 s r);have e:=y (t+1) (L++[f7 L g]) c o (fun B h=>w B (g9 g h)) (wa t L g d.2 s) q;simpa only[aX,show t+(b.length+1)=t+1+b.length by omega,mv,en,List.foldl_cons,c] using e}
lemma uz(C:Circuit)(n k w:Nat)(B:k<=C.gates.length)(E:w<n+k)(u:∀ g∈C.gates,(g.op=.and\/g.op=.or\/g.op=.not)/\g.inputs.length<=2)(r:Fv n)(hE:r.card=k+1)(o:∀ i∈r,∃ x y:Fin n->Bo,(∀ j,j≠i->x j=y j)/\(C.wires (ofFn x)).getD w false≠(C.wires (ofFn y)).getD w false):RO r (fun x=>(C.wires (ofFn x)).getD w false):=by
 let c:=C.gates.take k;let L:=mv c (fb n);let q:=L.getD w ∅;have d:c.length=k:=(by simp[c,pa,sW B]);have b:∀ g∈c,(g.op=.and\/g.op=.or\/g.op=.not)/\g.inputs.length<=2:=fun g K=>u g (List.mem_of_mem_take K);have hc:=qY c 0 (fb n) (fun g K=>(b g K).2) oQ
 have ad:q.card<=k+1:=by
  have:=hc {w}
  simpa only[uP,sC,lE,d] using this
 have v:∀ x y:Fin n->Bo,(∀ i∈q,x i=y i)->(C.wires (ofFn x)).getD w false=(C.wires (ofFn y)).getD w false:=(by intro x y e;rw[kW C n k w B E x,kW C n k w B E y];exact (pD x y c _ _ _ (rM x y)).2.2 w e);have s:r⊆q:=(by intro i Q;by_contra a3;obtain⟨x,y,e,a4⟩:=o i Q;apply a4 (v x y ?_);intro j P;exact e j (fun h=>a3 (h▸P)));have M:r=q:=nH s (by omega);have hT:=tY c 0 (fb n) (fun x=>ofFn x) (fun x=>by simp[fb]) b oQ v5;have a6:(({w}:Ft Nat).biUnion fun j=>L.getD j ∅).card=(0+c.length)+({w}:Ft Nat).card:=(by have hS:q.card=k+1:=(by rw[<-M];exact hE);simpa only[uP,sC,lE,d] using hS);have z:=(hT {w} a6).1 w (gk w);change RO q _ at z;rw[<-M] at z;have S:(fun x:Fin n->Bo=>(en c (ofFn x)).getD w false)=(fun x=>(C.wires (ofFn x)).getD w false):=(by funext x;exact (kW C n k w B E x).symm);change RO r (fun x:Fin n->Bo=>(en c (ofFn x)).getD w false) at z;rw[S] at z;exact z
end L853.R012.TightReadOnce
namespace L853.R012.ReadOncePath
open L853.R012.TightReadOnce
variable {n:Nat} {S:Fv n} {f:(Fin n->Bo)->Bo}
lemma xi(h:RO e f)(x:Fin n->Bo)(c:∀ i∈e,x i=false):f x=false:=by apply h (fun e f=>∀ x,(∀ i∈e,x i=false)->f x=false) ?_ ?_ x c;{intro i x c;exact c i (gk _)};{intro r q a b hd o j;constructor <;> intro x c;{dsimp only;rw[o x (fun i d=>c i (ga _ d)),j x (fun i d=>c i (jB _ d))];rfl};{dsimp only;rw[o x (fun i d=>c i (ga _ d)),j x (fun i d=>c i (jB _ d))];rfl}}
lemma xh(h:RO e f)(x y:Fin n->Bo)(c:∀ i∈e,x i=y i):f x=f y:=by
 apply h (fun e f=>∀ x y,(∀ i∈e,x i=y i)->f x=f y) ?_ ?_ x y c;{intro i x y c;exact c i (gk _)}
 ·
  intro r q a b hd o j;constructor <;> intro x y c <;> dsimp only <;>
   rw[o x y (fun i d=>c i (ga _ d)),j x y (fun i d=>c i (jB _ d))]
lemma rp(h:RO S f)(x y:Fin n->Bo)(c:∀ i,x i=true->y i=true)(d:f x=true):f y=true:=by apply h (fun _ f=>∀ x y,(∀ i,x i=true->y i=true)->f x=true->f y=true) ?_ ?_ x y c d;{intro i x y c d;exact c i d};{intro q o a b hd j e;constructor;{intro x y c d;simp only[gy] at d ⊢;exact⟨j x y c d.1,e x y c d.2⟩};{intro x y c d;simp only[kN] at d ⊢;exact d.elim (fun h=>Or.inl (j x y c h)) (fun h=>Or.inr (e x y c h))}}
def dJ(i j:Fin n):Fin n->Bo:=fun k=>decide (k=i\/k=j)
def fA(i:Fin n):Fin n->Bo:=fun k=>decide (k=i)
lemma qb(i j:Fin n):dJ i j=dJ j i:=by funext k;simp[dJ,or_comm]
lemma se(h:RO S f)(i j:Fin n)(o:i∉S)(e:j∉S):f (dJ i j)=false:=by apply xi h;intro k d;simp only[dJ,qD,not_or];exact⟨fun c=>o (c▸d),fun b=>e (b▸d)⟩
lemma ld(h:RO S f)(i j:Fin n)(d:j∉S):f (dJ i j)=f (fA i):=by apply xh h;intro k c;have b:k≠j:=fun b=>d (b▸c);simp[dJ,fA,b]
lemma oU(h:RO S f)(i j:Fin n)(b:i∉S):f (dJ i j)=f (fA j):=by rw[qb];exact ld h j i b
end L853.R012.ReadOncePath
namespace L853.R017
open L853.R012.TightReadOnce L853.R012.ReadOncePath
variable {n:Nat}
def kp(f:(Fin n->Bo)->Bo):Prop:=∀ i,f (fA i)=false
def jv(b:Fv n)(f:(Fin n->Bo)->Bo):Prop:=∀ i∈b,∃ j∈b,f (dJ i j)=true
def uH(b:Fv n)(f:(Fin n->Bo)->Bo):Prop:=∀ x,f x=true↔∃ i∈b,∃ j∈b,f (dJ i j)=true/\x i=true/\x j=true
lemma tk{i j:Fin n}{x:Fin n->Bo}(d:x i=true)(c:x j=true):∀ t,dJ i j t=true->x t=true:=by
 intro t b;have:t=i\/t=j:=by simpa[dJ] using b
 rcases this with rfl|rfl <;> assumption
lemma rW{b:Fv n}{f:(Fin n->Bo)->Bo}(q:RO b f)(x:Fin n->Bo)(d:f x=true):∃ i∈b,x i=true:=by
 by_contra j;have c:∀ i∈b,x i=false:=(by intro i o;have h:x i≠true:=fun e=>j ⟨i,o,e⟩;exact Bool.eq_false_iff.mpr h);have h:=xi q x c;rw[d] at h
 contradiction
lemma mb{q o:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint q o)(L:RO q a)(z:RO o b)(y:jv (q ∪ o) (fun x=>a x&&b x)):(∀ i∈q,a (fA i)=true)/\(∀ j∈o,b (fA j)=true):=by
 constructor
 ·
  intro i s;obtain⟨j,B,r⟩:=y i (ga _ s);have h:i∉o:=aT.mp hd s
  have c:j∉q:=by
   intro e;have d:j∉o:=aT.mp hd e;have u:=se z i j h d;simp only[u,s3] at r
   contradiction
  have w:a (dJ i j)=true:=(by simpa only[gy] using r:a (dJ i j)=true/\b (dJ i j)=true).1
  rwa [ld L i j c] at w
 ·
  intro i s;obtain⟨j,B,r⟩:=y i (jB _ s);have h:i∉q:=lD.mp hd s
  have c:j∉o:=by
   intro d;have e:j∉q:=lD.mp hd d;have u:=se L i j h e;simp only[u,kM] at r
   contradiction
  have v:b (dJ i j)=true:=(by simpa only[gy] using r:a (dJ i j)=true/\b (dJ i j)=true).2
  rwa [ld z i j c] at v
lemma rl{e o:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint e o)(B:RO e a)(L:RO o b)(v:kp (fun x=>a x||b x))(z:jv (e ∪ o) (fun x=>a x||b x)):jv e a:=by
 intro i w;obtain⟨j,E,y⟩:=z i (ga _ w);have u:i∉o:=aT.mp hd w;have r:∀ t,a (fA t)=false:=fun t=>(Bool.or_eq_false_iff.mp (v t)).1;have q:∀ t,b (fA t)=false:=fun t=>(Bool.or_eq_false_iff.mp (v t)).2
 have d:a (dJ i j)=true:=by
  have s:a (dJ i j)=true\/b (dJ i j)=true:=(by simpa only[kN] using y);rcases s with h|h
  {exact h}
  ·
   rw[oU L i j u,q j] at h
   contradiction
 have c:j∈e:=by
  by_contra c;rw[ld B i j c,r i] at d
  contradiction
 exact⟨j,c,d⟩
lemma qr{r:Fv n}{f:(Fin n->Bo)->Bo}(M:RO r f)(q:kp f)(z:jv r f):uH r f:=by
 let K:=fun (r:Fv n) (f:(Fin n->Bo)->Bo)=>RO r f/\(kp f->jv r f->uH r f)
 have P:K r f:=M K (by
  intro i;refine⟨kZ i,?_⟩;intro q z;have h:=q i;simp[fA] at h) (by
  intro E B a b hd o e;constructor;{refine⟨qe hd o.1 e.1,?_⟩;intro q z x;constructor;{intro L;obtain⟨y,v⟩:=mb hd o.1 e.1 z;obtain⟨i,w,d⟩:=rW o.1 x (by simpa only[gy] using L:a x=true/\b x=true).1;obtain⟨j,u,c⟩:=rW e.1 x (by simpa only[gy] using L:a x=true/\b x=true).2;refine⟨i,ga _ w,j,jB _ u,?_,d,c⟩;have a4:j∉E:=lD.mp hd u;have a5:i∉B:=aT.mp hd w;dsimp only;rw[ld o.1 i j a4,oU e.1 i j a5,y i w,v j u];rfl};{rintro⟨i,y,j,v,s,d,c⟩;exact rp (qe hd o.1 e.1) _ _ (tk d c) s}}
  ·
   refine⟨rq hd o.1 e.1,?_⟩;intro q z x;have a2:kp a:=fun t=>(Bool.or_eq_false_iff.mp (q t)).1;have a1:kp b:=fun t=>(Bool.or_eq_false_iff.mp (q t)).2;have S:=rl hd o.1 e.1 q z;have a6:jv B b:=(by have a3:kp (fun x=>b x||a x):=(by simpa only[mP] using q);have Q:jv (B ∪ E) (fun x=>b x||a x):=(by simpa only[nN,mP] using z);exact rl hd.symm e.1 o.1 a3 Q);constructor
   ·
    intro L;have a0:a x=true\/b x=true:=(by simpa only[kN] using L);rcases a0 with h|h
    {obtain⟨i,y,j,v,s,d,c⟩:=(o.2 a2 S x).mp h;refine⟨i,ga _ y,j,ga _ v,?_,d,c⟩;simp only[s,Bool.true_or]};{obtain⟨i,y,j,v,s,d,c⟩:=(e.2 a1 a6 x).mp h;refine⟨i,jB _ y,j,jB _ v,?_,d,c⟩;simp only[s,Bool.or_true]}
   ·
    rintro⟨i,y,j,v,s,d,c⟩;exact rp (rq hd o.1 e.1) _ _ (tk d c) s)
 exact P.2 q z
open L853.R012.TightReadOnce L853.R012.ReadOncePath
variable {n:Nat}
lemma fv{d s:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint d s)(z:RO d a)(y:RO s b)(u:kp (fun x=>a x||b x)){i j:Fin n}(w:i∈d)(v:(a (dJ i j)||b (dJ i j))=true):j∈d/\a (dJ i j)=true:=by
 have r:i∉s:=aT.mp hd w;have o:∀ t,a (fA t)=false:=fun t=>(Bool.or_eq_false_iff.mp (u t)).1;have e:∀ t,b (fA t)=false:=fun t=>(Bool.or_eq_false_iff.mp (u t)).2
 have c:a (dJ i j)=true:=by
  rcases Bool.or_eq_true_iff.mp v with h|h
  {exact h}
  ·
   rw[oU y i j r,e j] at h
   contradiction
 refine⟨?_,c⟩;by_contra q;rw[ld z i j q,o i] at c
 contradiction
lemma m9{d c:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint d c)(v:RO d a)(u:RO c b)(w:jv (d ∪ c) (fun x=>a x&&b x)){i j:Fin n}(s:i∈d)(r:j∈c):(a (dJ i j)&&b (dJ i j))=true:=by obtain⟨h,e⟩:=mb hd v u w;have q:i∉c:=aT.mp hd s;have o:j∉d:=lD.mp hd r;rw[ld v i j o,oU u i j q,h i s,e j r];rfl
lemma ek{h c:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint h c)(r:RO c b){i j:Fin n}(q:i∈h)(o:(a (dJ i j)&&b (dJ i j))=true):j∈c:=by
 by_contra d;have e:i∉c:=aT.mp hd q;rw[se r i j e d,s3] at o
 contradiction
def gI(dY:Fin n->Fin n)(cJ:Fin n->Bo)(b:Fv n)(f:(Fin n->Bo)->Bo):Prop:=kp f/\(∀ i∈b,dY i∈b)/\(∀ i∈b,f (dJ i (dY i))=true)/\(∀ i j,cJ i≠cJ j->j≠dY i->f (dJ i j)=false)
lemma lR{dY:Fin n->Fin n}{cJ:Fin n->Bo}{c:Fv n}{f:(Fin n->Bo)->Bo}(h:gI dY cJ c f):jv c f:=fun i b=>⟨dY i,h.2.1 i b,h.2.2.1 i b⟩
lemma mm{dY:Fin n->Fin n}{cJ:Fin n->Bo}{e h:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint e h)(q:RO e a)(o:RO h b)(c:gI dY cJ (e ∪ h) (fun x=>a x||b x)):gI dY cJ e a:=by refine⟨?_,?_,?_,?_⟩;{intro i;exact (Bool.or_eq_false_iff.mp (c.1 i)).1};{intro i d;exact (fv hd q o c.1 d (c.2.2.1 i (ga _ d))).1};{intro i d;exact (fv hd q o c.1 d (c.2.2.1 i (ga _ d))).2};{intro i j s r;exact (Bool.or_eq_false_iff.mp (c.2.2.2 i j s r)).1}
lemma oS{dY:Fin n->Fin n}{cJ:Fin n->Bo}{d c:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint d c)(j:RO d a)(i:RO c b)(e:gI dY cJ (d ∪ c) (fun x=>a x||b x)):gI dY cJ c b:=by have h:gI dY cJ (c ∪ d) (fun x=>b x||a x):=(by simpa only[nN,mP] using e);exact mm hd.symm i j h
lemma kD{dY:Fin n->Fin n}{cJ:Fin n->Bo}(s:Involutive dY)(d:∀ i,cJ (dY i)≠cJ i){e o:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint e o)(K:RO e a)(L:RO o b)(u:gI dY cJ (e ∪ o) (fun x=>a x&&b x)):∀ i∈e,∀ j∈e,cJ i=cJ j->i=j:=by
 intro i E j y v;have r:dY j∈o:=ek hd L y (u.2.2.1 j (ga _ y));have B:(a (dJ i (dY j))&&b (dJ i (dY j)))=true:=m9 hd K L (lR u) E r;have w:cJ i≠cJ (dY j):=(by intro h;exact d j (h.symm.trans v))
 have c:dY j=dY i:=by
  by_contra q;have z:=u.2.2.2 i (dY j) w q;dsimp only at z;rw[z] at B
  contradiction
 exact (s.injective c).symm
def nG(cJ:Fin n->Bo)(b:Fv n)(f:(Fin n->Bo)->Bo):Prop:=∀ i∈b,∀ j∈b,∀ l∈b,cJ i=cJ j->cJ i=cJ l->f (dJ i j)=true->f (dJ i l)=true->j=l
lemma ng{dY:Fin n->Fin n}{cJ:Fin n->Bo}(S:Involutive dY)(y:∀ i,cJ (dY i)≠cJ i){z:Fv n}{f:(Fin n->Bo)->Bo}(hf:RO z f)(h:gI dY cJ z f):nG cJ z f:=by
 let Q:=fun (z:Fv n) (f:(Fin n->Bo)->Bo)=>
  RO z f/\(gI dY cJ z f->nG cJ z f)
 have hQ:Q z f:=hf Q (by
  intro i;refine⟨kZ i,?_⟩;intro h;have hs:=h.1 i;simp[fA] at hs) (by
  intro M P a b hd e d;constructor
  ·
   refine⟨qe hd e.1 d.1,?_⟩;intro h i c j hj l hl v u s q;have a4:=kD S y hd e.1 d.1 h;have w:gI dY cJ (P ∪ M) (fun x=>b x&&a x):=(by simpa only[nN,py] using h);have a3:=kD S y hd.symm d.1 e.1 w;rcases cD.mp c with c|c
   {have E:=ek hd d.1 c s;have L:=ek hd d.1 c q;exact a3 j E l L (v.symm.trans u)};{have r:(b (dJ i j)&&a (dJ i j))=true:=(by simpa only[py] using s);have o:(b (dJ i l)&&a (dJ i l))=true:=(by simpa only[py] using q);have B:=ek hd.symm e.1 c r;have K:=ek hd.symm e.1 c o;exact a4 j B l K (v.symm.trans u)}
  ·
   refine⟨rq hd e.1 d.1,?_⟩;intro h i c j hj l hl v u s q;rcases cD.mp c with c|c
   {obtain⟨B,a8⟩:=fv hd e.1 d.1 h.1 c s;obtain⟨K,a6⟩:=fv hd e.1 d.1 h.1 c q;exact e.2 (mm hd e.1 d.1 h) i c j B l K v u a8 a6}
   ·
    have w:gI dY cJ (P ∪ M) (fun x=>b x||a x):=(by simpa only[nN,mP] using h);have r:(b (dJ i j)||a (dJ i j))=true:=(by simpa only[mP] using s);have o:(b (dJ i l)||a (dJ i l))=true:=(by simpa only[mP] using q);obtain⟨E,a7⟩:=fv hd.symm d.1 e.1 w.1 c r;obtain⟨L,a5⟩:=fv hd.symm d.1 e.1 w.1 c o;exact d.2 (oS hd e.1 d.1 h) i c j E l L v u a7 a5)
 exact hQ.2 h
variable {n:Nat}
lemma ri{dY:Fin n->Fin n}{cJ:Fin n->Bo}{r:Fv n}{f:(Fin n->Bo)->Bo}(Q:RO r f)(d:gI dY cJ r f):∀ i∈r,∀ j∈r,f (dJ i j)=true->f (dJ (dY i) (dY j))=true:=by
 let K:=fun (r:Fv n) (f:(Fin n->Bo)->Bo)=>
  RO r f/\(gI dY cJ r f->∀ i∈r,∀ j∈r,f (dJ i j)=true->f (dJ (dY i) (dY j))=true)
 have S:K r f:=Q K (by
  intro i;refine⟨kZ i,?_⟩;intro d;have M:=d.1 i;simp[fA] at M) (by
  intro B E a b hd o e;constructor
  ·
   refine⟨qe hd o.1 e.1,?_⟩;intro d i c j P w;have q:gI dY cJ (E ∪ B) (fun x=>b x&&a x):=(by simpa only[nN,py] using d);rcases cD.mp c with c|c
   {have s:=ek hd e.1 c w;have L:=ek hd e.1 c (d.2.2.1 i (ga _ c));have z:=ek hd.symm o.1 s (q.2.2.1 j (ga _ s));have h:=m9 hd.symm e.1 o.1 (lR q) L z;simpa only[py] using h};{have v:(b (dJ i j)&&a (dJ i j))=true:=(by simpa only[py] using w);have u:=ek hd.symm o.1 c v;have a0:=ek hd.symm o.1 c (q.2.2.1 i (ga _ c));have y:=ek hd e.1 u (d.2.2.1 j (ga _ u));exact m9 hd o.1 e.1 (lR d) a0 y}
  ·
   refine⟨rq hd o.1 e.1,?_⟩;intro d i c j P w;rcases cD.mp c with c|c
   {obtain⟨u,a2⟩:=fv hd o.1 e.1 d.1 c w;have h:=o.2 (mm hd o.1 e.1 d) i c j u a2;dsimp only;rw[h,Bool.true_or]}
   ·
    have q:gI dY cJ (E ∪ B) (fun x=>b x||a x):=(by simpa only[nN,mP] using d);have v:(b (dJ i j)||a (dJ i j))=true:=(by simpa only[mP] using w);obtain⟨s,a1⟩:=fv hd.symm e.1 o.1 q.1 c v;have h:=e.2 (oS hd o.1 e.1 d) i c j s a1;dsimp only;rw[h,Bool.or_true])
 exact S.2 d
variable {α:Type*}
lemma ro(R:α->α->Prop)(z:∀ {a b},R a b->R b a)(B:∀ a,¬ R a a)(y:∀ a b c,R a b->R a c->b=c):∃ p:Pm α,Involutive p/\(∀ a b,R a b↔p a=b/\b≠a)/\(∀ q:Pm α,(∀ a b,R a b↔q a=b/\b≠a)->q=p):=by
 classical
 let p:α->α:=fun a=>if h:∃ b,R a b then Classical.choose h else a;have r:∀ a b,R a b->p a=b:=(by intro a b h;have j:∃ b,R a b:=⟨b,h⟩;dsimp only[p];rw[dite_eq_left j];exact y a _ b (f9 j) h);have x:∀ a,p a=a\/R a (p a):=(by intro a;by_cases j:∃ b,R a b;{right;dsimp only[p];rw[dite_eq_left j];exact f9 j};{left;simp[p,j]})
 have s:Involutive p:=by
  intro a;rcases x a with h|h
  {rw[h,h]};{exact r _ _ (z h)}
 let e:Pm α:=s.toPerm p;have v:∀ a,e a=p a:=fun _=>rfl
 have i:∀ a b,R a b↔e a=b/\b≠a:=by
  intro a b;constructor;{intro h;refine⟨r a b h,?_⟩;intro d;exact B a (d▸h)}
  ·
   rintro⟨d,L⟩;rcases x a with h|h
   {exact False.elim (L (d.symm.trans h))};{exact d▸h}
 refine⟨e,s,i,?_⟩;intro q w;apply Equiv.ext;intro a;by_cases h:p a=a;{by_cases o:q a=a;{exact o.trans h.symm};{have u:=(w a (q a)).2 ⟨rfl,o⟩;have j:=r a (q a) u;exact False.elim (o (j.symm.trans h))}};{have u:=(i a (e a)).2 ⟨rfl,h⟩;exact (w a (e a)).1 u |>.1}
lemma m1{R:α->α->Prop}{p:Pm α}(d:∀ a b,R a b↔p a=b/\b≠a)(σ:α->α)(e:Involutive σ)(q:∀ a b,R a b->R (σ a) (σ b)):∀ a,p (σ a)=σ (p a):=by intro a;by_cases o:p a=a;{by_cases c:p (σ a)=σ a;{rw[o,c]};{have h:=q (σ a) (p (σ a)) ((d _ _).2 ⟨rfl,c⟩);rw[e a] at h;obtain⟨i,j⟩:=(d _ _).1 h;exact False.elim (j (i.symm.trans o))}};{have h:=q a (p a) ((d _ _).2 ⟨rfl,o⟩);exact ((d _ _).1 h).1}
variable {n:Nat}
lemma qW:∀ a b c d:Bo,a≠c->b≠d->c=d->a=b:=by decide
lemma l9{dY:Fin n->Fin n}{cJ:Fin n->Bo}(Q:Involutive dY)(e:∀ i,cJ (dY i)≠cJ i){r:Fv n}{f:(Fin n->Bo)->Bo}(B:RO r f)(o:gI dY cJ r f):∃ p:Pm (Fin n),Involutive p/\(∀ i,cJ (p i)=cJ i)/\(∀ i,p (dY i)=dY (p i))/\(∀ i,i∉r->p i=i)/\(∀ x,f x=true↔∃ i∈r,(x i=true/\x (dY i)=true)\/(p i≠i/\x i=true/\x (p i)=true))/\(∀ i j,(i∈r/\j∈r/\cJ i=cJ j/\f (dJ i j)=true)↔p i=j/\j≠i):=by
 classical
 let R:Fin n->Fin n->Prop:=fun i j=>
  i∈r/\j∈r/\cJ i=cJ j/\f (dJ i j)=true
 have a0:∀ {i j},R i j->R j i:=(by intro i j h;refine⟨h.2.1,h.1,h.2.2.1.symm,?_⟩;rw[qb];exact h.2.2.2)
 have a4:∀ i,¬ R i i:=by
  intro i h;have u:dJ i i=fA i:=(by funext j;simp[dJ,fA]);have v:=h.2.2.2;rw[u,o.1 i] at v
  contradiction
 have b:∀ i j l,R i j->R i l->j=l:=by
  intro i j l K M;exact ng Q e B o i K.1 j K.2.1 l M.2.1
   K.2.2.1 M.2.2.1 K.2.2.2 M.2.2.2
 obtain⟨p,a8,u,ai⟩:=ro R a0 a4 b;have q:∀ i,cJ (p i)=cJ i:=(by intro i;by_cases E:p i=i;{rw[E]};{exact ((u i (p i)).2 ⟨rfl,E⟩).2.2.1.symm});have d:∀ i j,R i j->R (dY i) (dY j):=(by intro i j h;refine⟨o.2.1 i h.1,o.2.1 j h.2.1,?_,?_⟩;{exact qW _ _ _ _ (e i) (e j) h.2.2.1};{exact ri B o i h.1 j h.2.1 h.2.2.2});have y:=m1 u dY Q d;have a2:∀ i,i∉r->p i=i:=(by intro i w;by_contra E;exact w ((u i (p i)).2 ⟨rfl,E⟩).1);refine⟨p,a8,q,y,a2,?_,u⟩;intro x;constructor
 ·
  intro ad;obtain⟨i,w,j,hj,c,L,z⟩:=(qr B o.1 (lR o) x).1 ad;by_cases P:cJ i=cJ j;{have a1:R i j:=⟨w,hj,P,c⟩;obtain⟨s,ab⟩:=(u i j).1 a1;refine⟨i,w,Or.inr ⟨?_,L,?_⟩⟩;{simpa only[s] using ab};{simpa only[s] using z}}
  ·
   have aa:j=dY i:=by
    by_contra a9;have S:=o.2.2.2 i j P a9;rw[S] at c
    contradiction
   exact⟨i,w,Or.inl ⟨L,aa▸z⟩⟩
 {rintro⟨i,w,h|h⟩;{exact rp B _ _ (tk h.1 h.2) (o.2.2.1 i w)};{have hr:=(u i (p i)).2 ⟨rfl,h.1⟩;exact rp B _ _ (tk h.2.1 h.2.2) hr.2.2.2}}
end L853.R017
namespace L853.R017.RowColumn
open L853.R012.TightReadOnce L853.R012.ReadOncePath
variable {k:Nat}
abbrev row(i:Fin k):Fin (k+k):=Fin.castAdd k i
abbrev col(i:Fin k):Fin (k+k):=Fin.natAdd k i
def dY:Fin (k+k)->Fin (k+k):=Fin.append col row
def cJ:Fin (k+k)->Bo:=Fin.append (fun _=>false) (fun _=>true)
@[simp] lemma kx(i:Fin k):dY (row i)=col i:=j6 _ _ i
@[simp] lemma nE(i:Fin k):dY (col i)=row i:=j4 _ _ i
@[simp] lemma n6(i:Fin k):cJ (row i)=false:=j6 _ _ i
@[simp] lemma n5(i:Fin k):cJ (col i)=true:=j4 _ _ i
lemma tS:Involutive (dY (k:=k)):=by
 intro i;induction i using Fin.addCases with
 | left j=>exact (aI dY (kx j)).trans (nE j)
 | right j=>exact (aI dY (nE j)).trans (kx j)
lemma w0(i:Fin (k+k)):cJ (dY i)≠cJ i:=by induction i using Fin.addCases with|left j=>{change cJ (dY (row j))≠cJ (row j);rw[kx,n5,n6];decide}|right j=>{change cJ (dY (col j))≠cJ (col j);rw[nE,n6,n5];decide}
lemma jq:Injective (row (k:=k)):=Fin.castAdd_injective k k
lemma ka:Injective (col (k:=k)):=Fin.natAdd_injective k k
@[simp] lemma z7(i j:Fin k):row i=row j↔i=j:=jq.eq_iff
@[simp] lemma zV(i j:Fin k):col i=col j↔i=j:=ka.eq_iff
lemma yB(p:Pm (Fin (k+k)))(c:∀ i,cJ (p i)=cJ i)(i:Fin k):∃ j,p (row i)=row j:=by
 have b:=c (row i);generalize d:p (row i)=v at *
 induction v using Fin.addCases with
 | left j=>exact⟨j,rfl⟩
 | right j=>
   rw[n6] at b;change cJ (col j)=false at b;rw[n5] at b
   contradiction
def fc(p:Pm (Fin k))(x y:Fin k->Bo):Bo:=
 decide (∃ i:Fin k,(x i=true/\y i=true)\/(p i≠i/\((x i=true/\x (p i)=true)\/(y i=true/\y (p i)=true))))
lemma o3(f:(Fin (k+k)->Bo)->Bo)(M:RO univ f)(K:L853.R017.gI dY cJ univ f):∃ p:Pm (Fin k),Involutive p/\∀ x y,f (Fin.append x y)=fc p x y:=by
 classical
 obtain⟨p,w,u,o,Q,z,L⟩:=L853.R017.l9 tS w0 M K
 choose q hq using yB p u;have s:Involutive q:=(by intro i;apply jq;rw[<- hq (q i),<- hq i,w (row i)]);let e:Pm (Fin k):=s.toPerm q;have b:∀ i,p (row i)=row (e i):=hq;have c:∀ i,p (col i)=col (e i):=(by intro i;rw[<- kx i,o,b,kx]);have d:∀ i,p (row i)≠row i↔e i≠i:=(by intro i;rw[b];exact not_congr (jq.eq_iff));have j:∀ i,p (col i)≠col i↔e i≠i:=(by intro i;rw[c];exact not_congr (ka.eq_iff));refine⟨e,s,?_⟩;intro x y;apply Bool.eq_iff_iff.mpr;rw[z];simp only[fc,cG];constructor
 ·
  rintro⟨v,P,h⟩;induction v using Fin.addCases with
  | left i=>
    rcases h with h|⟨r,E,B⟩
    {refine⟨i,Or.inl ?_⟩;simpa only[kx,j6,j4] using h};{refine⟨i,Or.inr ⟨(d i).mp r,Or.inl ⟨?_,?_⟩⟩⟩;{simpa only[j6] using E};{simpa only[b,j6] using B}}
  | right i=>
    rcases h with h|⟨r,E,B⟩
    {refine⟨i,Or.inl ?_⟩;simpa only[nE,j6,j4] using h.symm};{refine⟨i,Or.inr ⟨(j i).mp r,Or.inr ⟨?_,?_⟩⟩⟩;{simpa only[j4] using E};{simpa only[c,j4] using B}}
 {rintro⟨i,h|⟨r,h|h⟩⟩;{refine⟨row i,dN _,Or.inl ?_⟩;simpa only[kx,j6,j4] using h};{refine⟨row i,dN _,Or.inr ⟨(d i).mpr r,?_,?_⟩⟩;{simpa only[j6] using h.1};{simpa only[b,j6] using h.2}};{refine⟨col i,dN _,Or.inr ⟨(j i).mpr r,?_,?_⟩⟩;{simpa only[j4] using h.1};{simpa only[c,j4] using h.2}}}
lemma lO(p:Pm (Fin k))(r:Involutive p)(i j:Fin k):fc p (dJ i j) (fun _=>false)=true↔p i=j/\j≠i:=by
 simp only[fc,cG,eX,and_false,or_false,false_or,dJ];constructor
 ·
  rintro⟨a,e,v,o⟩;have q:a=i\/a=j:=(by simpa using v);have d:p a=i\/p a=j:=(by simpa using o);rcases q with u|s
  ·
   subst a;rcases d with h|h
   {exact False.elim (e h)};{exact⟨h,fun b=>e (h.trans b)⟩}
  ·
   subst a;rcases d with h|h
   {have c:p i=j:=(by rw[<- h,r j]);exact⟨c,fun b=>e (h.trans b.symm)⟩};{exact False.elim (e h)}
 {rintro⟨c,b⟩;refine⟨i,?_,?_,?_⟩;{exact fun h=>b (c.symm.trans h)};{simp};{simp[c]}}
lemma p8(p q:Pm (Fin k))(o:Involutive p)(e:Involutive q)(r:∀ x y,fc p x y=fc q x y):p=q:=by have d:∀ i j,(p i=j/\j≠i)↔(q i=j/\j≠i):=(by intro i j;rw[<- lO p o i j,<- lO q e i j,r]);apply Equiv.ext;intro i;by_cases c:p i=i;{by_cases b:q i=i;{exact c.trans b.symm};{have h:=(d i (q i)).2 ⟨rfl,b⟩;exact False.elim (b (h.1.symm.trans c))}};{exact ((d i (p i)).1 ⟨rfl,c⟩).1.symm}
lemma ma(f:(Fin (k+k)->Bo)->Bo)(h:RO univ f)(e:L853.R017.gI dY cJ univ f):∃! p:Pm (Fin k),Involutive p/\∀ x y,f (Fin.append x y)=fc p x y:=by obtain⟨p,c,d⟩:=o3 f h e;refine⟨p,⟨c,d⟩,?_⟩;intro q b;apply p8 q p b.1 c;intro x y;exact (b.2 x y).symm.trans (d x y)
variable {k:Nat}
lemma rS(d:2<=k)(i:Fin k):∃ j:Fin k,j≠i:=by let z:Fin k:=⟨0,by omega⟩;let o:Fin k:=⟨1,by omega⟩;by_cases b:i=z;{refine⟨o,?_⟩;intro h;have c:=aI Fin.val (h.trans b);change 1=0 at c;omega};{exact⟨z,Ne.symm b⟩}
lemma oR(z:2<=k)(f:(Fin (k+k)->Bo)->Bo)(e:∀ x y,(∀ i,x i=true->y i=true)->f x=true->f y=true)(b:∀ i j:Fin k,f (dJ (row i) (col j))=decide (i=j)):L853.R017.gI dY cJ univ f:=by
 have B:L853.R017.kp f:=by
  intro v;apply Bool.eq_false_iff.mpr;intro d;induction v using Fin.addCases with
  | left i=>
    obtain⟨j,o⟩:=rS z i
    have q:=e (fA (row i)) (dJ (row i) (col j)) (by
     intro t r;have u:t=row i:=(by simpa[fA] using r);simp[dJ,u]) d
    rw[b,iw (Ne.symm o)] at q
    contradiction
  | right i=>
    obtain⟨j,o⟩:=rS z i
    have q:=e (fA (col i)) (dJ (row j) (col i)) (by
     intro t r;have u:t=col i:=(by simpa[fA] using r);simp[dJ,u]) d
    rw[b,iw o] at q
    contradiction
 refine⟨B,by simp,?_,?_⟩
 ·
  intro v E;induction v using Fin.addCases with
  | left i=>change f (dJ (row i) (dY (row i)))=true;rw[kx,b];simp
  | right i=>change f (dJ (col i) (dY (col i)))=true;rw[nE,qb,b];simp
 ·
  intro v w L c;induction v using Fin.addCases with
  | left i=>induction w using Fin.addCases with|left j=>{exact False.elim (L ((n6 i).trans (n6 j).symm))}|right j=>{change col j≠dY (row i) at c;rw[kx] at c;have s:i≠j:=fun h=>c (aI col h.symm);rw[b,iw s]}
  | right i=>induction w using Fin.addCases with|left j=>{change row j≠dY (col i) at c;rw[nE] at c;have o:j≠i:=fun h=>c (aI row h);rw[qb,b,iw o]}|right j=>{exact False.elim (L ((n5 i).trans (n5 j).symm))}
lemma nx(d:2<=k)(f:(Fin (k+k)->Bo)->Bo)(c:RO univ f)(b:∀ i j:Fin k,f (dJ (row i) (col j))=decide (i=j)):∃! p:Pm (Fin k),Involutive p/\∀ x y,f (Fin.append x y)=fc p x y:=by exact ma f c (oR d f (rp c) b)
end L853.R017.RowColumn
namespace L853.R017.qg
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open L853.R012.TightReadOnce L853.R012.ReadOncePath
open L853.R017.RowColumn
lemma uu(g:Gate)(c:g.op=GateOp.and\/g.op=GateOp.or)(w e:LB)(h:∀ i∈g.inputs,w.getD i false=true->e.getD i false=true)(d:g.op.eval (g.inputs.map fun i=>w.getD i false)=true):g.op.eval (g.inputs.map fun i=>e.getD i false)=true:=by
 rcases c with c|c <;> rw[c] at d ⊢ <;> simp[GateOp.eval] at d ⊢
 {intro i b;exact h i b (d i b)};{obtain⟨i,b,j⟩:=d;exact⟨i,b,h i b j⟩}
lemma uA(c:Ls Gate)(r:∀ g∈c,g.op=GateOp.and\/g.op=GateOp.or):∀ w b:LB,w.length=b.length->(∀ i,w.getD i false=true->b.getD i false=true)->∀ i,(en c w).getD i false=true->(en c b).getD i false=true:=by induction c with|nil=>{intro w b e h;exact h}|cons g c s=>{intro w b e h i u;apply s (fun v o=>r v (g9 _ o)) (w++[g.op.eval (g.inputs.map fun a=>w.getD a false)]) (b++[g.op.eval (g.inputs.map fun a=>b.getD a false)]) (by simp[e]) ?_ i u;intro j d;by_cases q:j=w.length;{rw[q,fI] at d;rw[q,e,fI];exact uu g (r g gK) w b (fun a _=>h a) d};{rw[f3 _ _ _ _ q] at d;rw[f3 _ _ _ _ (by omega)];exact h j d}}
lemma vQ{n:Nat}(C:Circuit)(e:Monotone2 C)(x y:Fin n->Bo)(h:∀ i,x i=true->y i=true)(q:C.eval (ofFn x)=true):C.eval (ofFn y)=true:=by
 apply uA C.gates (fun g o=>(e g o).1) (ofFn x) (ofFn y) (by simp) ?_ C.output q;intro j c;by_cases b:j<n;{have d:x ⟨j,b⟩=true:=(by simpa[b] using c);simpa[b] using h ⟨j,b⟩ d}
 ·
  rw[mE _ _ (by simp;omega)] at c
  contradiction
lemma oy{k:Nat}(i j:Fin k):ofFn (dJ (row i) (col j))=oneEach i j:=by
 have h:dJ (row i) (col j)=Fin.append (fA i) (fA j):=by
  funext v;induction v using Fin.addCases with
  | left t=>have c:row t≠col j:=(by intro h;have b:=aI (fun z:Fin (k+k)=>z.val) h;change t.val=k+j.val at b;omega);simp only[dJ,fA,j6];simp only[c,or_false];exact Bool.eq_iff_iff.mpr (by simpa only[cG] using jq.eq_iff)
  | right t=>have c:col t≠row i:=(by intro h;have b:=aI (fun z:Fin (k+k)=>z.val) h;change k+t.val=i.val at b;omega);simp only[dJ,fA,j4];simp only[c,false_or];exact Bool.eq_iff_iff.mpr (by simpa only[cG] using ka.eq_iff)
 rw[h,u3];rfl
lemma rG{k:Nat}(B:2<=k)(C:Circuit)(s:Monotone2 C)(e:C.size+1<=2*k)(q:Represents (fun i j:Fin k=>decide (i=j)) C):RO univ (fun x:Fin (k+k)->Bo=>C.eval (ofFn x)):=by
 let f:(Fin (k+k)->Bo)->Bo:=fun x=>C.eval (ofFn x);have d:∀ i j:Fin k,f (dJ (row i) (col j))=decide (i=j):=(by intro i j;exact (aI C.eval (oy i j)).trans (q i j));have r:=oR B f (vQ C s) d;have c:∀ i∈(univ:Ft (Fin (k+k))),∃ x y:Fin (k+k)->Bo,(∀ j,j≠i->x j=y j)/\(C.wires (ofFn x)).getD C.output false≠(C.wires (ofFn y)).getD C.output false:=(by intro i E;refine⟨dJ i (dY i),fA (dY i),?_,?_⟩;{intro j w;simp[dJ,fA,w]};{change f (dJ i (dY i))≠f (fA (dY i));rw[r.2.2.1 i E,r.1 (dY i)];decide})
 have b:C.output<(k+k)+C.gates.length:=by
  let z:Fin k:=⟨0,by omega⟩;have L:=d z z;have v:(C.wires (ofFn (dJ (row z) (col z)))).getD C.output false=true:=(by change f (dJ (row z) (col z))=true;simpa only[iy] using L);by_contra M;have P:(C.wires (ofFn (dJ (row z) (col z)))).length=(k+k)+C.gates.length:=(by rw[yE,jS];simp);rw[mE _ _ (by omega)] at v
  contradiction
 have K:=qw C (k+k) C.gates.length C.output le_rfl b (fun g u=>(s g u).2) univ c;have o:(univ:Ft (Fin (k+k))).card=C.gates.length+1:=(by simp only[pv,pq] at K ⊢;change C.gates.length+1<=2*k at e;omega);exact uz C (k+k) C.gates.length C.output le_rfl b (fun g u=>⟨by have h:=(s g u).1;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at h;tauto,(s g u).2⟩)
  univ o c
lemma lK{k:Nat}(d:2<=k)(C:Circuit)(e:Monotone2 C)(c:C.size+1<=2*k)(b:Represents (fun i j:Fin k=>decide (i=j)) C):∃! p:Pm (Fin k),Involutive p/\∀ x y,C.eval (ofFn x++ofFn y)=fc p x y:=by
 have h:=nx d (fun x:Fin (k+k)->Bo=>C.eval (ofFn x)) (rG d C e c b) (by
  intro i j;rw[oy];exact b i j)
 simpa only[u3] using h
end L853.R017.qg
namespace L853.R017
 lemma tj:∀(k:Nat),2<=k->∀ f:(Fin k->Bo)->(Fin k->Bo)->Bo,(∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C/\C.size+1<=2*k/\PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C/\∀ x y,f x y=C.eval (ofFn x++ofFn y))->∃! p:Pm (Fin k),Involutive p/\∀ x y,f x y=decide (∃ i:Fin k,(x i=true/\y i=true)\/(p i≠i/\((x i=true/\x (p i)=true)\/(y i=true/\y (p i)=true)))):=by intro k hk f h;obtain⟨C,hm,hs,hr,he⟩:=h;obtain⟨p,hp,hu⟩:=qg.lK hk C hm hs hr;refine⟨p,⟨hp.1,?_⟩,?_⟩;{intro x y;exact (he x y).trans (hp.2 x y)};{intro q hq;apply hu q;refine⟨hq.1,?_⟩;intro x y;exact (he x y).symm.trans (hq.2 x y)}
end L853.R017
namespace L853.zU.t5
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open L853.R012.TightReadOnce
variable {n:Nat}
def y6(g:Gate):Prop:=(g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length<=2
def nC(d:Fv n)(f:(Fin n->Bo)->Bo):Prop:=∀ m:Nat,n<=m->∃(c:Ls Gate) (b:Nat),(∀ g∈c,y6 g)/\c.length+1=d.card/\b< m+c.length/\∀ w:LB,w.length=m->(en c w).getD b false=f (fun i:Fin n=>w.getD i.val false)
lemma vd(i:Fin n):nC {i} (fun x=>x i):=by
 intro m c;refine⟨[],i.val,?_,by simp,?_,?_⟩;{simp}
 ·
  have:=i.isLt
  simp only[mL,Nat.add_zero];omega
 {intro w b;rfl}
lemma q4{B E:Fv n}{a b:(Fin n->Bo)->Bo}(hd:Disjoint B E)(Q:nC B a)(P:nC E b)(op:GateOp)(z:op=GateOp.and\/op=GateOp.or):nC (B ∪ E) (fun x=>op.eval [a x,b x]):=by
 intro m M;obtain⟨e,j,v,a6,ra,a0⟩:=Q m M;obtain⟨s,r,u,a5,rb,L⟩:=P (m+e.length) (by omega);let q:=m+e.length+s.length;refine⟨e++s++[⟨op,[j,r]⟩],q,?_,?_,?_,?_⟩
 ·
  intro g d;simp only[eL,eZ] at d;rcases d with (d|d)|d
  {exact v g d};{exact u g d};{subst g;exact⟨z,by simp⟩}
 {rw[Finset.card_union_of_disjoint hd];simp only[dL,lv];omega};{simp only[dL,lv];dsimp[q];omega};{intro w K;rw[lZ,lZ];let h:=en e w;let c:=en s h;have o:h.length=m+e.length:=(by dsimp[h];rw[jS,K]);have y:c.length=q:=(by dsimp[c];rw[jS,o]);have S:c.getD j false=a (fun i:Fin n=>w.getD i.val false):=(by dsimp[c];rw[nc s h j (by omega)];exact a0 w K);have a1:c.getD r false=b (fun i:Fin n=>w.getD i.val false):=(by dsimp[c];rw[L h o];congr 1;funext i;exact nc e w i.val (by have:=i.isLt;omega));change (en [⟨op,[j,r]⟩] c).getD q false=_;change (c++[op.eval [c.getD j false,c.getD r false]]).getD q false=_;rw[<- y,fI,S,a1]}
lemma wN{e:Fv n}{f:(Fin n->Bo)->Bo}(h:RO e f):nC e f:=by
 apply h nC vd;intro j i a b hd d c;constructor
 ·
  simpa only[GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
   using q4 hd d c GateOp.and (Or.inl rfl)
 ·
  simpa only[GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
   using q4 hd d c GateOp.or (Or.inr rfl)
lemma xg{q:Fv n}{f:(Fin n->Bo)->Bo}(h:RO q f):∃ C:Circuit,Monotone2 C/\C.size+1=q.card/\C.output<n+C.size/\∀ x:Fin n->Bo,C.eval (ofFn x)=f x:=by obtain⟨o,c,j,e,d,b⟩:=wN h n (le_refl n);refine⟨⟨o,c⟩,?_,e,d,?_⟩;{intro g u;obtain⟨r,s⟩:=j g u;exact⟨by simpa only[Set.mem_insert_iff,Set.mem_singleton_iff] using r,s⟩};{intro x;change (en o (ofFn x)).getD c false=f x;rw[b (ofFn x) (by simp)];congr 1;funext i;simp}
lemma sj{d:Fv n}{f:(Fin n->Bo)->Bo}(h:RO d f):∃ C:Circuit,Monotone2 C/\C.size+1=d.card/\∀ x:Fin n->Bo,C.eval (ofFn x)=f x:=by obtain⟨C,e,b,_,c⟩:=xg h;exact⟨C,e,b,c⟩
end L853.zU.t5
namespace L853.v8.rL
open L853.R012.TightReadOnce L853.R012.ReadOncePath L853.R017.RowColumn
variable {k:Nat}
lemma m4(i j:Fin k):row i≠col j:=by intro h;have e:=aI (fun z:Fin (k+k)=>z.val) h;change i.val=k+j.val at e;omega
lemma qZ(i j:Fin k):col i≠row j:=(m4 j i).symm
def nq(b:Ft (Fin k)):Ft (Fin (k+k)):=b.image row ∪ b.image col
def uC(p:Pm (Fin k))(i:Fin k)(x:Fin (k+k)->Bo):Prop:=(x (row i)=true/\x (col i)=true)\/(p i≠i/\((x (row i)=true/\x (row (p i))=true)\/(x (col i)=true/\x (col (p i))=true)))
noncomputable def jQ(p:Pm (Fin k))(b:Ft (Fin k))(x:Fin (k+k)->Bo):Bo:=by
 classical
 exact decide (∃ i∈b,uC p i x)
lemma xk(b T:Ft (Fin k)):nq (b ∪ T)=nq b ∪ nq T:=by
 classical
 ext i;simp only[nq,cD,mem_image]
 aesop
lemma vL{o T:Ft (Fin k)}(hd:Disjoint o T):Disjoint (nq o) (nq T):=by
 classical
 rw[aT] at hd ⊢;intro v h d;simp only[nq,cD,mem_image] at h d;rcases h with ⟨i,e,rfl⟩|⟨i,e,rfl⟩
 ·
  rcases d with ⟨j,c,b⟩|⟨j,c,b⟩
  {exact hd e ((jq b)▸c)};{exact qZ j i b}
 ·
  rcases d with ⟨j,c,b⟩|⟨j,c,b⟩
  {exact m4 j i b};{exact hd e ((ka b)▸c)}
lemma vV(p:Pm (Fin k))(b T:Ft (Fin k)):jQ p (b ∪ T)=fun x=>jQ p b x||jQ p T x:=by
 funext x;apply Bool.eq_iff_iff.mpr;simp only[jQ,cG,kN,cD]
 aesop
lemma we(p:Pm (Fin k))(i:Fin k)(c:p i=i):RO (nq {i}) (jQ p {i}):=by
 have b:=qe (by simpa using m4 i i) (kZ (row i)) (kZ (col i))
 convert b using 1;{simp[nq]};{funext x;simp[jQ,uC,c]}
lemma xb(p:Pm (Fin k))(r:Involutive p)(i j:Fin k)(e:i≠j)(b:p i=j):RO (nq {i,j}) (jQ p {i,j}):=by
 have d:p j=i:=(by rw[<- b,r i]);have u:=rq (by simpa using m4 i j) (kZ (row i)) (kZ (col j));have s:=rq (by simpa using qZ i j) (kZ (col i)) (kZ (row j))
 have hd:Disjoint (({row i} ∪ {col j}):Ft (Fin (k+k))) ({col i} ∪ {row j}):=by
  rw[aT];intro v o h;simp only[cD,bI] at o h;rcases o with rfl|rfl
  ·
   rcases h with c|c
   {exact m4 i i c};{exact e (jq c)}
  ·
   rcases h with c|c
   {exact e.symm (ka c)};{exact qZ j j c}
 have q:=qe hd u s
 convert q using 1;{ext v;simp only[nq,Finset.image_insert,Finset.image_singleton,cD,aV,bI];tauto};{funext x;apply Bool.eq_iff_iff.mpr;simp only[jQ,cG,aV,bI,exists_eq_or_imp,exists_eq_left,uC,b,d,gy,kN];tauto}
lemma wk(p:Pm (Fin k))(b T:Ft (Fin k))(hd:Disjoint b T)(d:RO (nq b) (jQ p b))(c:RO (nq T) (jQ p T)):RO (nq (b ∪ T)) (jQ p (b ∪ T)):=by rw[xk,vV];exact rq (vL hd) d c
lemma vY(p:Pm (Fin k))(E:Involutive p)(d:Ft (Fin k))(L:∀ i∈d,p i∈d)(q:d.Nonempty):RO (nq d) (jQ p d):=by
 classical
 revert L q;refine Finset.strongInductionOn d ?_;intro d M L q;obtain⟨i,v⟩:=q;by_cases e:p i=i;{let T:=d.erase i;have B:T ⊂ d:=Finset.erase_ssubset v;have c:∀ j∈T,p j∈T:=(by intro j K;have s:=fL.mp K;apply fL.mpr;constructor;{intro w;apply s.1;exact p.injective (w.trans e.symm)};{exact L j s.2});have o:d={i} ∪ T:=(by simp[T,v]);by_cases b:T=∅;{rw[o,b,union_empty];exact we p i e};{rw[o];apply wk p {i} T;{simp[T]};{exact we p i e};{exact M T B c (Finset.nonempty_iff_ne_empty.mpr b)}}};{let j:=p i;have u:i≠j:=Ne.symm e;have K:j∈d:=L i v;have r:p j=i:=E i;let T:=(d.erase i).erase j;have B:T ⊂ d:=lt_of_le_of_lt (Finset.erase_subset j (d.erase i)) (Finset.erase_ssubset v);have c:∀ a∈T,p a∈T:=(by intro a z;have h:=fL.mp z;have P:=fL.mp h.2;apply fL.mpr;constructor;{intro w;exact P.1 (p.injective w)};{apply fL.mpr;constructor;{intro w;exact h.1 (p.injective (w.trans r.symm))};{exact L a P.2}});have o:d={i,j} ∪ T:=(by ext a;simp only[T,cD,aV,bI,fL];constructor;{intro z;by_cases y:a=i;{exact Or.inl (Or.inl y)};{by_cases x:a=j;{exact Or.inl (Or.inr x)};{exact Or.inr ⟨x,y,z⟩}}};{rintro ((rfl|rfl)|⟨-,-,z⟩);{exact v};{exact K};{exact z}});by_cases b:T=∅;{rw[o,b,union_empty];exact xb p E i j u rfl};{rw[o];apply wk p {i,j} T;{simp[T,aT]};{exact xb p E i j u rfl};{exact M T B c (Finset.nonempty_iff_ne_empty.mpr b)}}}
lemma vA(d:0<k)(p:Pm (Fin k))(c:Involutive p):RO univ (fun x:Fin (k+k)->Bo=>fc p (fun i=>x (row i)) (fun i=>x (col i))):=by
 have h:=vY p c univ (by simp) ⟨⟨0,d⟩,dN _⟩
 have b:nq (univ:Ft (Fin k))=univ:=by
  ext v;simp only[dN,iff_true];induction v using Fin.addCases with
  | left i=>exact ga _ (mem_image.mpr ⟨i,dN _,rfl⟩)
  | right i=>exact jB _ (mem_image.mpr ⟨i,dN _,rfl⟩)
 rw[b] at h;have e:jQ p univ=(fun x:Fin (k+k)->Bo=>fc p (fun i=>x (row i)) (fun i=>x (col i))):=(by funext x;apply Bool.eq_iff_iff.mpr;simp[jQ,uC,fc]);rw[e] at h;exact h
end L853.v8.rL
namespace L853.v8.qz
open L853.R017.RowColumn L853.R012.TightReadOnce L853.R012.ReadOncePath
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
lemma rf{k:Nat}(p:Pm (Fin k))(i j:Fin k):fc p (fA i) (fA j)=decide (i=j):=by apply Bool.eq_iff_iff.mpr;simp only[fc,fA,cG];constructor;{rintro⟨a,⟨e,d⟩|⟨b,h|h⟩⟩;{exact e.symm.trans d};{exact False.elim (b (h.2.trans h.1.symm))};{exact False.elim (b (h.2.trans h.1.symm))}};{intro c;exact⟨i,Or.inl ⟨rfl,c⟩⟩}
lemma l7(b:∀ {n:Nat} {d:Fv n} {f:(Fin n->Bo)->Bo},RO d f->∃ C:Circuit,Monotone2 C/\C.size+1=d.card/\∀ x,C.eval (ofFn x)=f x){k:Nat}(q:0<k)(p:Pm (Fin k))(h:Involutive p):∃ C:Circuit,Monotone2 C/\C.size+1<=2*k/\Represents (fun i j:Fin k=>decide (i=j)) C/\∀ x y,C.eval (ofFn x++ofFn y)=fc p x y:=by
 obtain⟨C,o,e,r⟩:=b (rL.vA q p h)
 have c:∀ x y,C.eval (ofFn x++ofFn y)=fc p x y:=by
  intro x y;simpa only[u3,j6,j4]
   using r (Fin.append x y)
 refine⟨C,o,?_,?_,c⟩;{simp only[pv,pq] at e;omega};{intro i j;change C.eval (ofFn (fA i)++ofFn (fA j))=decide (i=j);rw[c,rf]}
end L853.v8.qz
namespace L853.v8
lemma vD:∀(k:Nat),2<=k->∀ f:(Fin k->Bo)->(Fin k->Bo)->Bo,(∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C/\C.size+1<=2*k/\PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C/\∀ x y,f x y=C.eval (ofFn x++ofFn y))↔∃! p:Pm (Fin k),Involutive p/\∀ x y,f x y=decide (∃ i:Fin k,(x i=true/\y i=true)\/(p i≠i/\((x i=true/\x (p i)=true)\/(y i=true/\y (p i)=true)))):=by intro k o f;constructor;{exact L853.R017.tj k o f};{rintro⟨p,⟨d,q⟩,s⟩;obtain⟨C,e,b,c,r⟩:=qz.l7 (fun h=>L853.zU.t5.sj h) (by omega:0<k) p d;refine⟨C,e,b,c,?_⟩;intro x y;exact (q x y).trans (r x y).symm}
end L853.v8
namespace MathCore
noncomputable section
open Finset Polynomial
def gX(k:Nat):Ls (Fin k×Fin k):=(finRange k).flatMap (fun i=>((finRange k).filter (fun j=>decide (i<j))).map (fun j=>(i,j)))
def aF{k:Nat}(e:Fin k×Fin k):Ft (Fin k):={e.1,e.2}
abbrev aQ{k:Nat}(M:Ft (Fin k×Fin k)):Prop:=(∀ e∈M,e.1<e.2)/\(∀ e∈M,∀ f∈M,e≠f->Disjoint (aF e) (aF f))
abbrev eS{k:Nat}(e1 e2:Fin k×Fin k):Prop:=e1.1<e2.1/\e2.1<e1.2/\e1.2<e2.2
abbrev g8{k:Nat}(e1 e2:Fin k×Fin k):Prop:=eS e1 e2\/eS e2 e1
def cr{k:Nat}(b:Ft (Fin k×Fin k)):Nat:=((b ×ˢ b).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>eS p.1 p.2)).card
def fK{k:Nat}(c b:Ft (Fin k×Fin k)):Nat:=((c ×ˢ b).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>g8 p.1 p.2)).card
lemma gR{k:Nat}(e:Fin k×Fin k):e∈gX k↔e.1<e.2:=by simp only[gX,gM,cC,gd,mK,cG,fR];constructor;{rintro⟨i,j,b,rfl⟩;exact b};{intro h;exact⟨e.1,e.2,h,rfl⟩}
lemma wM(k:Nat):(gX k).Nodup:=by
 unfold gX;rw[lA];refine⟨?_,?_⟩;{intro i _;exact ((jZ k).filter _).map (fun a b h=>by simpa using h)}
 ·
  exact (jZ k).pairwise_of_forall_ne (fun i _ j _ hij=>by
   intro x d c;simp only[cC,gd,mK,fR] at d c;rcases d with ⟨a,_,rfl⟩
   rcases c with ⟨b,_,h⟩
   exact hij (aI Prod.fst h).symm)
lemma tQ{k:Nat}{e:Fin k×Fin k}(h:e.1<e.2):(aF e).card=2:=lC (bS h)
lemma iC{k:Nat}{i N:Ft (Fin k×Fin k)}(h:aQ i)(b:N⊆i):aQ N:=⟨fun e d=>h.1 e (b d),fun e d f j c=>h.2 e (b d) f (b j) c⟩
lemma kX{k:Nat}{b:Ft (Fin k×Fin k)}(h:aQ b):(b.biUnion aF).card=2*b.card:=by rw[sH (fun e d f i c=>h.2 e d f i c)];have j:∀ e∈b,(aF e).card=2:=fun e d=>tQ (h.1 e d);rw[dB rfl j,qP,n0,kP]
lemma uq{k:Nat}{c b:Fin k×Fin k}(h:eS c b):¬eS b c:=by intro d;exact jH _ (hK h.1 d.1)
lemma yr{k:Nat}:cr (∅:Ft (Fin k×Fin k))=0:=by simp[cr]
lemma jx{k:Nat}{d c:Ft (Fin k×Fin k)}(i:Disjoint d c):cr (d ∪ c)=cr d+cr c+fK d c:=by
 unfold cr fK;have j:(d ∪ c) ×ˢ (d ∪ c)=(d ×ˢ d) ∪ (c ×ˢ c) ∪ (d ×ˢ c) ∪ (c ×ˢ d):=(by ext⟨x,y⟩;simp only[cX,cD];tauto);have w:Disjoint (d ×ˢ d) (c ×ˢ c):=(by rw[aT];intro p b e;exact aT.mp i (cX.mp b).1 (cX.mp e).1)
 have v:Disjoint ((d ×ˢ d) ∪ (c ×ˢ c)) (d ×ˢ c):=by
  rw[aT];intro p b e;rcases cD.mp b with b|b
  {exact aT.mp i (cX.mp b).2 (cX.mp e).2};{exact aT.mp i (cX.mp e).1 (cX.mp b).1}
 have u:Disjoint (((d ×ˢ d) ∪ (c ×ˢ c)) ∪ (d ×ˢ c)) (c ×ˢ d):=by
  rw[aT];intro p b e;rcases cD.mp b with b|b
  ·
   rcases cD.mp b with b|b
   {exact aT.mp i (cX.mp b).1 (cX.mp e).1};{exact aT.mp i (cX.mp e).2 (cX.mp b).2}
  {exact aT.mp i (cX.mp b).1 (cX.mp e).1}
 rw[j,filter_union,qG (u.mono (kO _ _) (kO _ _)),filter_union,qG (v.mono (kO _ _) (kO _ _)),filter_union,qG (w.mono (kO _ _) (kO _ _))];have s:((c ×ˢ d).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>eS p.1 p.2)).card=((d ×ˢ c).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>eS p.2 p.1)).card:=(by refine nR (fun p _=>(p.2,p.1)) ?_ ?_ ?_;{intro p r;simp only[aL,cX] at r ⊢;exact⟨⟨r.1.2,r.1.1⟩,r.2⟩};{intro p _ q _ h;exact eC (aI Prod.snd h) (aI Prod.fst h)};{intro q o;simp only[aL,cX] at o;exact⟨(q.2,q.1),by simp only[aL,cX];exact⟨⟨o.1.2,o.1.1⟩,o.2⟩,rfl⟩});have z:((d ×ˢ c).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>eS p.1 p.2)).card+((d ×ˢ c).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>eS p.2 p.1)).card=((d ×ˢ c).filter (fun p:(Fin k×Fin k)×(Fin k×Fin k)=>g8 p.1 p.2)).card:=(by rw[<- qG];{congr 1;ext p;simp only[g8,aL,cD];tauto};{rw[aT];intro p b e;simp only[aL] at b e;exact uq b.2 e.2});omega
lemma oe{k:Nat}(F:Ft (Fin k×Fin k))(e:Fin k×Fin k):fK F {e}=(F.filter (fun f=>g8 f e)).card:=by unfold fK;refine nR (fun p _=>p.1) ?_ ?_ ?_;{intro p b;simp only[aL,cX,bI] at b ⊢;exact⟨b.1.1,b.1.2▸b.2⟩};{intro p b q d h;simp only[aL,cX,bI] at b d;exact eC h (b.1.2.trans d.1.2.symm)};{intro f c;simp only[aL] at c;exact⟨(f,e),by simp[c.1,c.2],rfl⟩}
lemma kc{k:Nat}(j d:Ft (Fin k×Fin k)):fK j d=∑ e∈d,(j.filter (fun f=>g8 f e)).card:=by unfold fK;rw[card_eq_sum_card_fiberwise (f:=Prod.snd) (t:=d) (fun p b=>(cX.mp (aL.mp b).1).2)];refine dB rfl fun e o=>?_;refine nR (fun p _=>p.1) ?_ ?_ ?_;{intro p b;simp only[aL,cX] at b ⊢;exact⟨b.1.1.1,b.2▸b.1.2⟩};{intro p b q i h;simp only[aL] at b i;exact eC h (b.2.trans i.2.symm)};{intro f c;simp only[aL] at c;exact⟨(f,e),by simp[c.1,o,c.2],rfl⟩}
lemma p3{k:Nat}{f e:Fin k×Fin k}(q:f.1<f.2)(w:e.1<e.2)(hd:Disjoint (aF f) (aF e)):((aF f).filter (fun x=>e.1<x/\x<e.2)).card % 2=if g8 f e then 1 else 0:=by
 have o:f.1≠e.1:=fun h=>aT.mp hd (ep f.1 {f.2}) (h▸ep e.1 {e.2});have j:f.1≠e.2:=fun h=>aT.mp hd (ep f.1 {f.2}) (h▸aV.mpr (Or.inr (gk e.2)));have i:f.2≠e.1:=fun h=>aT.mp hd (aV.mpr (Or.inr (gk f.2))) (h▸ep e.1 {e.2});have d:f.2≠e.2:=fun h=>aT.mp hd (aV.mpr (Or.inr (gk f.2))) (h▸aV.mpr (Or.inr (gk e.2)));have c:f.1≠f.2:=bS q
 have b:((aF f).filter (fun x=>e.1<x/\x<e.2)).card=(if e.1<f.1/\f.1<e.2 then 1 else 0)+(if e.1<f.2/\f.2<e.2 then 1 else 0):=by
  unfold aF;rw[Finset.filter_insert,Finset.filter_singleton];split_ifs with L h2 h2
  {rw[o7 (by simp[c]),sC]};{simp};{simp};{simp}
 rw[b];have z:f.1.val≠e.1.val:=fun h=>o (bL h);have s:f.1.val≠e.2.val:=fun h=>j (bL h);have y:f.2.val≠e.1.val:=fun h=>i (bL h);have r:f.2.val≠e.2.val:=fun h=>d (bL h);have u:f.1.val<f.2.val:=q;have v:e.1.val<e.2.val:=w;simp only[g8,eS,iU];split_ifs <;> omega
lemma hZ{k:Nat}{F:Ft (Fin k×Fin k)}(o:aQ F){e:Fin k×Fin k}(r:e.1<e.2)(hd:Disjoint (F.biUnion aF) (aF e)):(F.filter (fun f=>g8 f e)).card % 2=((F.biUnion aF).filter (fun x=>e.1<x/\x<e.2)).card % 2:=by
 have i:∀ f∈F,Disjoint (aF f) (aF e):=fun f b=>
  hd.mono_left (subset_biUnion_of_mem aF b)
 have h:(F.biUnion aF).filter (fun x=>e.1<x/\x<e.2)=F.biUnion (fun f=>(aF f).filter (fun x=>e.1<x/\x<e.2)):=(by ext x;simp only[aL,bT];constructor;{rintro⟨⟨f,b,c⟩,d⟩;exact⟨f,b,c,d⟩};{rintro⟨f,b,c,d⟩;exact⟨⟨f,b,c⟩,d⟩});rw[h,sH (fun f b g q j=>(o.2 f b g q j).mono (kO _ _) (kO _ _))];rw[lB,card_filter,lB];congr 1;refine dB rfl fun f b=>?_;rw[p3 (o.1 f b) r (i f b)];split_ifs <;> rfl
lemma gC{R:Type*}[CommRing R]{a b:Nat}(h:a % 2=b % 2):(-1:R)^a=(-1:R)^b:=by
 have d:(-1:R)^a=(-1:R)^(a % 2):=by
  conv_lhs=>rw[<- qR a 2,j8,pow_mul]
  simp
 have c:(-1:R)^b=(-1:R)^(b % 2):=by
  conv_lhs=>rw[<- qR b 2,j8,pow_mul]
  simp
 rw[d,c,h]
open Classical in
def o5{k:Nat}(c:Ft (Fin k)):Ft (Ft (Fin k×Fin k)):=((gX k).toFinset.powerset).filter (fun b=>aQ b/\b.biUnion aF=c)
lemma g4{k:Nat}{c:Ft (Fin k)}{b:Ft (Fin k×Fin k)}:b∈o5 c↔aQ b/\b.biUnion aF=c:=by
 classical
 simp only[o5,aL,pz,u0];intro h e d;rw[dO,gR];exact h.1.1 e d
lemma oH{R:Type*}[CommRing R](r:Nat):∑ j∈Finset.range (2*r+1),(-1:R)^j=1:=by induction r with|zero=>{simp}|succ r c=>{rw[show 2*(r+1)+1=(2*r+1)+1+1 by omega,u2,u2,c];have b:(-1:R)^(2*r+1)=-1:=(by rw[gN,pow_mul];norm_num);have d:(-1:R)^(2*r+1+1)=1:=(by rw[gN,b];ring);rw[b,d];ring}
lemma vF{k:Nat}{R:Type*}[CommRing R]:∀(r:Nat) (E:Ft (Fin k)),E.card=2*r->∑ B∈o5 E,(-1:R)^cr B=1:=by
 intro r;induction r with
 | zero=>intro E hS;have bl:E=∅:=card_eq_zero.mp hS;subst bl;have bn:o5 (∅:Ft (Fin k))={∅}:=(by ext B;rw[g4,bI];constructor;{rintro⟨S,Q⟩;have hc:=kX S;rw[Q,Finset.card_empty] at hc;exact card_eq_zero.mp (by omega)};{rintro rfl;exact⟨⟨fun _ h=>by simp at h,fun _ h=>by simp at h⟩,by simp⟩});rw[bn,Finset.sum_singleton,yr,pow_zero]
 | succ r ih=>
   intro E hS
   classical
   have b5:E.Nonempty:=card_pos.mp (by omega);let a:=E.min' b5;have ay:a∈E:=Finset.min'_mem E b5;let s:=E.erase a;have d:s.card=2*r+1:=(by rw[uR ay,hS];omega)
   have a6:∀ b∈s,a<b:=fun b P=>
    qS (Finset.min'_le E b (jA P)) (Ne.symm (uX P))
   have c:∀ B∈o5 E,∃! b∈s,(a,b)∈B:=by
    intro B M;obtain⟨S,Q⟩:=g4.mp M;have bk:a∈B.biUnion aF:=Q.symm▸ay;obtain⟨e,L,bc⟩:=bT.mp bk;have b8:aF e⊆E:=Q▸subset_biUnion_of_mem aF L;have aa:e.1<e.2:=S.1 e L
    have az:e.1=a:=by
     simp only[aF,aV,bI] at bc;rcases bc with h1|h1
     {exact h1.symm};{exfalso;have bf:a<=e.1:=Finset.min'_le E e.1 (b8 (by simp[aF]));exact not_lt_of_ge bf (h1▸aa)}
    have q:e.2∈s:=fL.mpr ⟨(az▸bS aa).symm,b8 (by simp[aF])⟩;have bb:(a,e.2)∈B:=(by have:(a,e.2)=e:=eC az.symm rfl;rw[this];exact L);refine⟨e.2,⟨q,bb⟩,?_⟩;rintro b' ⟨_,ba⟩;by_contra y;have hd:=S.2 (a,b') ba e L (fun h=>y (aI Prod.snd h));exact aT.mp hd (ep a {b'}) (az▸ep e.1 {e.2})
   have a3:∑ B∈o5 E,(-1:R)^cr B=∑ b∈s,∑ z∈o5 (s.erase b),(-1:R)^cr (insert (a,b) z):=by
    rw[sum_sigma'];refine nV (fun B M=>⟨Classical.choose (c B M),B.erase (a,Classical.choose (c B M))⟩)
     ?_ ?_ ?_ ?_
    ·
     intro B M
     set b:=Classical.choose (c B M);have P:=(f9 (c B M)).1;obtain⟨S,Q⟩:=g4.mp M;refine mem_sigma.mpr ⟨P.1,g4.mpr ⟨iC S (erase_subset _ _),?_⟩⟩;ext x;simp only[bT,mem_erase,s];constructor;{rintro⟨e,⟨y,L⟩,a5⟩;have au:x∈E:=Q▸bT.mpr ⟨e,L,a5⟩;have o:=S.2 e L (a,b) P.2 y;have a9:x≠a:=fun h=>aT.mp o a5 (by simp[aF,h]);have u:x≠b:=fun h=>aT.mp o a5 (by simp[aF,h]);exact⟨u,a9,au⟩}
     ·
      rintro⟨u,a9,au⟩;obtain⟨e,L,a5⟩:=bT.mp (Q.symm▸au);refine⟨e,⟨?_,L⟩,a5⟩;rintro rfl;simp only[aF,aV,bI] at a5;rcases a5 with rfl|rfl <;> contradiction
    ·
     intro P1 ag P2 af b7;simp only[Sigma.mk.inj_iff] at b7;obtain⟨P,M⟩:=b7;have ah:P1.erase (a,Classical.choose (c P1 ag))=P2.erase (a,Classical.choose (c P2 af)):=eq_of_heq M;have h1:=(f9 (c P1 ag)).1.2;have h2:=(f9 (c P2 af)).1.2
     calc P1=insert (a,Classical.choose (c P1 ag)) (P1.erase (a,Classical.choose (c P1 ag))):=(qJ h1).symm
      _=insert (a,Classical.choose (c P1 ag)) (P2.erase (a,Classical.choose (c P2 af))):=by rw[ah]
      _=insert (a,Classical.choose (c P2 af)) (P2.erase (a,Classical.choose (c P2 af))):=by rw[P]
      _=P2:=qJ h2
    ·
     intro⟨b,z⟩ hbp;simp only[mem_sigma] at hbp;obtain⟨q,ah⟩:=hbp;obtain⟨am,ae⟩:=g4.mp ah
     have o:Disjoint (z.biUnion aF) (aF (a,b)):=by
      rw[ae,lD];intro x K;simp only[aF,aV,bI] at K;rcases K with rfl|rfl
      {simp[s]};{simp}
     have v:(a,b)∉z:=fun hm=>
      aT.mp o (bT.mpr ⟨(a,b),hm,ep a {b}⟩) (ep a {b})
     have S:aQ (insert (a,b) z):=by
      refine⟨?_,?_⟩
      ·
       intro e he;rcases aV.mp he with rfl|he
       {exact a6 b q};{exact am.1 e he}
      ·
       intro e he f hf y;rcases aV.mp he with rfl|he <;> rcases aV.mp hf with rfl|hf
       {exact (y rfl).elim};{exact (o.mono_left (gJ aF hf)).symm};{exact o.mono_left (gJ aF he)};{exact am.2 e he f hf y}
     have Q:(insert (a,b) z).biUnion aF=E:=(by rw[biUnion_insert,ae];ext x;simp only[aF,cD,aV,bI,mem_erase,s];constructor;{rintro ((rfl|rfl)|⟨_,_,K⟩);{exact ay};{exact mem_of_mem_erase q};{exact K}};{intro K;by_cases a9:x=a;{exact Or.inl (Or.inl a9)};{by_cases u:x=b;{exact Or.inl (Or.inr u)};{exact Or.inr ⟨u,a9,K⟩}}});have a7:insert (a,b) z∈o5 E:=g4.mpr ⟨S,Q⟩;refine⟨insert (a,b) z,a7,?_⟩;have ad:Classical.choose (c (insert (a,b) z) a7)=b:=(f9 (c (insert (a,b) z) a7)).2 b ⟨q,mem_insert_self _ _⟩ |>.symm;refine Sigma.ext ad ?_;rw[ad,qL v]
    {intro B M;have h1:=(f9 (c B M)).1.2;rw[qJ h1]}
   rw[a3]
   have aj:∀ b∈s,∑ z∈o5 (s.erase b),(-1:R)^cr (insert (a,b) z)=(-1:R)^(s.filter (fun x=>x<b)).card:=by
    intro b q
    have av:∀ z∈o5 (s.erase b),(-1:R)^cr (insert (a,b) z)=(-1:R)^(s.filter (fun x=>x<b)).card*(-1:R)^cr z:=by
     intro z ah;obtain⟨am,ae⟩:=g4.mp ah
     have o:Disjoint (z.biUnion aF) (aF (a,b)):=by rw[ae,lD];intro x K;simp only[aF,aV,bI] at K;rcases K with rfl|rfl <;> simp[s]
     have v:(a,b)∉z:=fun hm=>
      aT.mp o (bT.mpr ⟨(a,b),hm,ep a {b}⟩) (ep a {b})
     have ai:insert (a,b) z=z ∪ {(a,b)}:=(by ext x;simp[or_comm]);rw[ai,jx (Finset.disjoint_singleton_right.mpr v),show cr {(a,b)}=0 by simp[cr],g1,oe,j8,kP];congr 1;apply gC;rw[hZ am (a6 b q) o,ae];congr 2;ext x;simp only[aL,mem_erase];constructor;{rintro⟨⟨_,w⟩,_,u⟩;exact⟨w,u⟩};{rintro⟨w,u⟩;exact⟨⟨bS u,w⟩,a6 x w,u⟩}
    rw[dB rfl av,<- mM,ih (s.erase b) (by rw[uR q,d];omega),kQ]
   rw[dB rfl aj]
   have ax:∑ b∈s,(-1:R)^(s.filter (fun x=>x<b)).card=∑ j∈Finset.range (2*r+1),(-1:R)^j:=by
    let a4:=Finset.orderEmbOfFin s d;refine nV (fun b _=>(s.filter (fun x=>x<b)).card) ?_ ?_ ?_ ?_
    ·
     intro b P;rw[mem_range,<- d];exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨kO _ _,fun h=>by
      have:=h▸P
      exact jH b (aL.mp this).2⟩)
    ·
     intro b1 bj b2 bi ab;rcases qT b1 b2 with aa|rfl|b6
     ·
      exfalso
      have aw:s.filter (fun x=>x<b1) ⊂ s.filter (fun x=>x<b2):=Finset.ssubset_iff_subset_ne.mpr ⟨fun x K=>by
       simp only[aL] at K ⊢;exact⟨K.1,hK K.2 aa⟩,
       fun h=>by
        have:b1∈s.filter (fun x=>x<b1):=h▸aL.mpr ⟨bj,aa⟩;exact jH b1 (aL.mp this).2⟩
      exact bS (Finset.card_lt_card aw) ab
     {rfl}
     ·
      exfalso
      have aw:s.filter (fun x=>x<b2) ⊂ s.filter (fun x=>x<b1):=Finset.ssubset_iff_subset_ne.mpr ⟨fun x K=>by
       simp only[aL] at K ⊢;exact⟨K.1,hK K.2 b6⟩,
       fun h=>by
        have:b2∈s.filter (fun x=>x<b2):=h▸aL.mpr ⟨bi,b6⟩;exact jH b2 (aL.mp this).2⟩
      exact ne_of_gt (Finset.card_lt_card aw) ab
    ·
     intro j hj;rw[mem_range] at hj;let b:=a4 ⟨j,hj⟩;have q:b∈s:=uQ s d ⟨j,hj⟩;refine⟨b,q,?_⟩
     have b9:(s.filter (fun x=>x<b)).card=j:=by
      have:s.filter (fun x=>x<b)=(univ.filter (fun i:Fin (2*r+1)=>i.val<j)).image a4:=by ext x;simp only[aL,bV,dN,fR];constructor;{rintro⟨w,u⟩;have ar:x∈Set.range (s.orderEmbOfFin d):=(by rw[Finset.range_orderEmbOfFin];exact w);obtain⟨i,rfl⟩:=ar;exact⟨i,a4.lt_iff_lt.mp u,rfl⟩};{rintro⟨i,bh,rfl⟩;exact⟨uQ s d i,a4.lt_iff_lt.mpr bh⟩}
      rw[this,o6 _ a4.injective];have:(univ.filter (fun i:Fin (2*r+1)=>i.val<j)).card=(Finset.range j).card:=by refine nR (fun i _=>i.val) ?_ ?_ ?_;{intro i hi;simp only[aL,dN,fR] at hi;exact mem_range.mpr hi};{intro i1 _ i2 _ h;exact bL h};{intro t ht;rw[mem_range] at ht;exact⟨⟨t,by omega⟩,by simp[ht],rfl⟩}
      rw[this,card_range]
     exact b9
    {intro _ _;rfl}
   rw[ax,oH]
def PM(N:Nat):Ft (Ft (Fin (2*N)×Fin (2*N))):=o5 univ
def jn{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R):R:=∑ P∈PM N,(-1:R)^cr P * ∏ e∈P,b e.1 e.2
open Classical in
def cE(n:Nat):Ft (ES n):=((gX n).toFinset.powerset).filter aQ
lemma cP{n:Nat}{b:ES n}:b∈cE n↔aQ b:=by
 classical
 simp only[cE,aL,pz,u0];intro h e c;rw[dO,gR];exact h.1 e c
def gh{n:Nat}{R:Type*}[CommRing R](W:Fin n->Fin n->R):Fin (2*n)->Fin (2*n)->R:=fun a b=>
 if ha:a.val<n then if hb:b.val<n then if a<b then W ⟨a.val,ha⟩ ⟨b.val,hb⟩
  else if b<a then-W ⟨b.val,hb⟩ ⟨a.val,ha⟩
  else 0
  else if a.val+b.val+1=2*n then 1 else 0
 else if hb:b.val<n then if a.val+b.val+1=2*n then -1 else 0
  else if a<b then 1
   else if b<a then -1
   else 0
lemma uG{n:Nat}{R:Type*}[CommRing R](W:Fin n->Fin n->R)(a:Fin (2*n)):gh W a a=0:=by
 unfold gh;split_ifs with c h2 b
 all_goals first|rfl|omega|exact (jH a b).elim|exact (jH a ‹a<a›).elim
lemma xp{n:Nat}{R:Type*}[CommRing R](W:Fin n->Fin n->R)(a b:Fin (2*n)):gh W b a=-gh W a b:=by
 by_cases i:a.val<n <;> by_cases e:b.val<n <;> simp only[gh,i,e,↓reduceDIte]
 ·
  rcases qT a b with h|rfl|h
  {simp[h,e7 h]};{simp};{simp[h,e7 h]}
 {by_cases d:a.val+b.val+1=2*n;{have c:b.val+a.val+1=2*n:=(by omega);simp[d,c]};{have c:b.val+a.val+1≠2*n:=(by omega);simp[d,c]}};{by_cases d:a.val+b.val+1=2*n;{have c:b.val+a.val+1=2*n:=(by omega);simp[d,c]};{have c:b.val+a.val+1≠2*n:=(by omega);simp[d,c]}}
 ·
  rcases qT a b with h|rfl|h
  {simp[h,e7 h]};{simp};{simp[h,e7 h]}
def ey{n:Nat}(i:Fin n):Fin (2*n):=⟨i.val,by omega⟩
def fi{n:Nat}(i:Fin n):Fin (2*n):=⟨2*n-1-i.val,by omega⟩
lemma gA{n:Nat}:Injective (ey (n:=n)):=fun _ _ h=>
 bL (by simpa[ey] using aI Fin.val h)
lemma nD{n:Nat}:Injective (fi (n:=n)):=fun a b h=>by
 have c:=aI Fin.val h;simp only[fi] at c;exact bL (by omega)
lemma dW{n:Nat}(i j:Fin n):ey i<fi j:=by simp only[ey,fi,iU];omega
lemma lI{n:Nat}{i j:Fin n}:ey i<ey j↔i<j:=Iff.rfl
lemma te{n:Nat}{i j:Fin n}:fi i<fi j↔j< i:=by simp only[fi,iU];omega
def bP{n:Nat}(e:EP n):Fin (2*n)×Fin (2*n):=(ey e.1,ey e.2)
lemma jg{n:Nat}:Injective (bP (n:=n)):=fun _ _ h=>eC (gA (aI Prod.fst h)) (gA (aI Prod.snd h))
lemma xc{n:Nat}{R:Type*}[CommRing R](W:Fin n->Fin n->R):jn (gh W)=∑ s∈cE n,(-1:R)^cr s * ∏ e∈s,W e.1 e.2:=by
 classical
 unfold jn
 let b5 (S:Ft (Fin (2*n)×Fin (2*n))):Prop:=
  ∀ e∈S,(e.1.val<n/\e.2.val<n)\/(n<=e.1.val/\n<=e.2.val)\/(e.1.val<n/\e.1.val+e.2.val+1=2*n)
 have bz:∀ S∈PM n,¬b5 S->(-1:R)^cr S * ∏ e∈S,gh W e.1 e.2=0:=(by intro S hP bj;simp only[b5,not_forall,not_or] at bj;obtain⟨e,a1,E,B,h3⟩:=bj;have bk:e.1.val<e.2.val:=(g4.mp hP).1.1 e a1;have de:gh W e.1 e.2=0:=(by unfold gh;by_cases ha:e.1.val<n;{by_cases hb:e.2.val<n;{exact (E ⟨ha,hb⟩).elim};{have a4:e.1.val+e.2.val+1≠2*n:=fun ay=>h3 ⟨ha,ay⟩;simp[ha,hb,a4]}};{by_cases hb:e.2.val<n;{omega};{exact (B ⟨by omega,by omega⟩).elim}});rw[qI a1 de,mul_zero]);rw[<- sum_filter_of_ne (p:=b5) (fun S hP a4=>by_contra fun bj=>a4 (bz S hP bj))];let c (s:ES n):=s.image bP
 let o (s:ES n):=
  (univ \ s.biUnion aF).image (fun i:Fin n=>(ey i,fi i))
 let v (s:ES n):Ft (Fin (2*n)):=
  (s.biUnion aF).image fi
 have ck:∑ S∈(PM n).filter b5,(-1:R)^cr S * ∏ e∈S,gh W e.1 e.2=∑ s∈cE n,∑ K∈o5 (v s),(-1:R)^cr (c s ∪ o s ∪ K) * ∏ e∈(c s ∪ o s ∪ K),gh W e.1 e.2:=by
  rw[sum_sigma'];refine (nV (fun (p:Σ _:ES n,Ft (Fin (2*n)×Fin (2*n))) _=>c p.1 ∪ o p.1 ∪ p.2) ?_ ?_ ?_ ?_).symm
  ·
   rintro⟨s,K⟩ Q;simp only[mem_sigma,cP,g4] at Q;obtain⟨hM,bt,af⟩:=Q;simp only[aL,PM,g4]
   have ab:Disjoint ((c s).biUnion aF) ((o s).biUnion aF):=by
    rw[aT];intro x y w;simp only[bT,bV,c,o,bP,aF,aV,bI,mem_sdiff,dN,fR] at y w;rcases y with ⟨_,⟨e,bo,rfl⟩,rfl|rfl⟩ <;>
    rcases w with ⟨_,⟨i,a0,rfl⟩,a8|a8⟩
    {have h:e.1=i:=gA a8;exact a0 ⟨e,bo,Or.inl h.symm⟩};{exact bS (dW e.1 i) a8};{have h:e.2=i:=gA a8;exact a0 ⟨e,bo,Or.inr h.symm⟩};{exact bS (dW e.2 i) a8}
   have aa:Disjoint ((c s).biUnion aF) (K.biUnion aF):=by
    rw[af,aT];intro x y w;simp only[bT,bV,c,bP,aF,aV,bI,v] at y w;rcases y with ⟨_,⟨e,_,rfl⟩,rfl|rfl⟩ <;> rcases w with ⟨j,_,ba⟩
    {exact bS (dW e.1 j) ba.symm};{exact bS (dW e.2 j) ba.symm}
   have ad:Disjoint ((o s).biUnion aF) (K.biUnion aF):=by
    rw[af,aT];intro x y w;simp only[bT,bV,o,aF,aV,bI,mem_sdiff,dN,fR,v] at y w;rcases y with ⟨_,⟨i,a0,rfl⟩,rfl|rfl⟩ <;> rcases w with ⟨j,c5,ba⟩
    {exact bS (dW i j) ba.symm}
    {have:=nD ba.symm;subst this;exact a0 c5}
   have ah:aQ (c s):=by
    refine⟨?_,?_⟩;{intro e r;obtain⟨L,a5,rfl⟩:=bV.mp r;exact lI.mpr (hM.1 L a5)}
    ·
     intro e r f P a4;obtain⟨L,a5,rfl⟩:=bV.mp r;obtain⟨M,ar,rfl⟩:=bV.mp P;have a9:L≠M:=fun h=>a4 (aI bP h);rw[aT];intro x y w;simp only[bP,aF,aV,bI] at y w;rcases y with rfl|rfl <;> rcases w with h|h
     {exact aT.mp (hM.2 L a5 M ar a9) (ep L.1 {L.2}) ((gA h)▸ep M.1 {M.2})};{exact aT.mp (hM.2 L a5 M ar a9) (ep L.1 {L.2}) ((gA h)▸aV.mpr (Or.inr (gk M.2)))};{exact aT.mp (hM.2 L a5 M ar a9) (aV.mpr (Or.inr (gk L.2))) ((gA h)▸ep M.1 {M.2})};{exact aT.mp (hM.2 L a5 M ar a9) (aV.mpr (Or.inr (gk L.2))) ((gA h)▸aV.mpr (Or.inr (gk M.2)))}
   have ai:aQ (o s):=by
    refine⟨?_,?_⟩;{intro e r;obtain⟨i,_,rfl⟩:=bV.mp r;exact dW i i}
    ·
     intro e r f P a4;obtain⟨i,_,rfl⟩:=bV.mp r;obtain⟨j,_,rfl⟩:=bV.mp P;have bm:i≠j:=fun h=>a4 (by subst h;rfl);rw[aT];intro x y w;simp only[aF,aV,bI] at y w;rcases y with rfl|rfl <;> rcases w with h|h
     {exact bm (gA h)};{exact bS (dW i j) h};{exact bS (dW j i) h.symm};{exact bm (nD h)}
   have az:aQ (c s ∪ o s ∪ K):=by
    refine⟨?_,?_⟩
    ·
     intro e r;rcases cD.mp r with r|r
     ·
      rcases cD.mp r with r|r
      {exact ah.1 e r};{exact ai.1 e r}
     {exact bt.1 e r}
    ·
     intro e r f P a4;rcases cD.mp r with (r|r) <;> rcases cD.mp P with (P|P)
     ·
      rcases cD.mp r with r|r <;> rcases cD.mp P with P|P
      {exact ah.2 e r f P a4};{exact ab.mono (gJ aF r) (gJ aF P)};{exact (ab.mono (gJ aF P) (gJ aF r)).symm};{exact ai.2 e r f P a4}
     ·
      rcases cD.mp r with r|r
      {exact aa.mono (gJ aF r) (gJ aF P)};{exact ad.mono (gJ aF r) (gJ aF P)}
     ·
      rcases cD.mp P with P|P
      {exact (aa.mono (gJ aF P) (gJ aF r)).symm};{exact (ad.mono (gJ aF P) (gJ aF r)).symm}
     {exact bt.2 e r f P a4}
   have c7:(c s ∪ o s ∪ K).biUnion aF=univ:=by
    ext x;rw[union_biUnion,union_biUnion,af];simp only[dN,iff_true,cD];by_cases hx:x.val<n
    ·
     let i:Fin n:=⟨x.val,hx⟩;have a8:x=ey i:=bL rfl;by_cases a0:i∈s.biUnion aF
     ·
      left;left;obtain⟨e,bo,ax⟩:=bT.mp a0;refine bT.mpr ⟨bP e,mem_image_of_mem _ bo,?_⟩;simp only[aF,aV,bI,bP] at ax ⊢;rcases ax with h|h <;> simp[a8,h]
     {left;right;refine bT.mpr ⟨(ey i,fi i),mem_image_of_mem _ (mem_sdiff.mpr ⟨dN _,a0⟩),?_⟩;simp[aF,a8]}
    {let i:Fin n:=⟨2*n-1-x.val,by omega⟩;have a8:x=fi i:=bL (by simp[fi,i];omega);by_cases a0:i∈s.biUnion aF;{right;exact bV.mpr ⟨i,a0,a8.symm⟩};{left;right;refine bT.mpr ⟨(ey i,fi i),mem_image_of_mem _ (mem_sdiff.mpr ⟨dN _,a0⟩),?_⟩;simp[aF,a8]}}
   refine⟨⟨az,c7⟩,?_⟩;intro e r;rcases cD.mp r with r|r
   ·
    rcases cD.mp r with r|r
    {obtain⟨L,_,rfl⟩:=bV.mp r;exact Or.inl ⟨L.1.isLt,L.2.isLt⟩};{obtain⟨i,_,rfl⟩:=bV.mp r;exact Or.inr (Or.inr ⟨i.isLt,by simp[ey,fi];omega⟩)}
   {have ci:aF e⊆v s:=af▸gJ aF r;obtain⟨i,_,hi⟩:=bV.mp (ci (ep e.1 {e.2}));obtain⟨j,_,hj⟩:=bV.mp (ci (aV.mpr (Or.inr (gk e.2))));exact Or.inr (Or.inl ⟨by rw[<- hi];simp[fi];omega,by rw[<- hj];simp[fi];omega⟩)}
  ·
   rintro⟨M1,cc⟩ b6 ⟨M2,cb⟩ aw ay;simp only[mem_sigma,cP,g4] at b6 aw;have c8:M1=M2:=(by ext e;have E:bP e∈c M1 ∪ o M1 ∪ cc↔e∈M1:=(by simp only[cD,bV,c,o];constructor;{rintro ((⟨L,a5,h⟩|⟨i,_,h⟩)|h);{exact jg h▸a5};{exfalso;have:=aI (fun p=>p.2.val) h;simp[bP,ey,fi] at this;omega};{exfalso;have z:ey e.1∈v M1:=b6.2.2▸bT.mpr ⟨bP e,h,by simp[bP,aF]⟩;obtain⟨j,_,hj⟩:=bV.mp z;exact bS (dW e.1 j) hj.symm}};{intro r;exact Or.inl (Or.inl ⟨e,r,rfl⟩)});have B:bP e∈c M2 ∪ o M2 ∪ cb↔e∈M2:=(by simp only[cD,bV,c,o];constructor;{rintro ((⟨L,a5,h⟩|⟨i,_,h⟩)|h);{exact jg h▸a5};{exfalso;have:=aI (fun p=>p.2.val) h;simp[bP,ey,fi] at this;omega};{exfalso;have z:ey e.1∈v M2:=aw.2.2▸bT.mpr ⟨bP e,h,by simp[bP,aF]⟩;obtain⟨j,_,hj⟩:=bV.mp z;exact bS (dW e.1 j) hj.symm}};{intro r;exact Or.inl (Or.inl ⟨e,r,rfl⟩)});rw[<- E,ay,B]);subst c8;congr 1;ext e
   have ct:e∈cc↔e∈(c M1 ∪ o M1 ∪ cc)/\n<=e.1.val:=by
    constructor;{intro r;refine⟨cD.mpr (Or.inr r),?_⟩;have z:e.1∈v M1:=b6.2.2▸bT.mpr ⟨e,r,ep e.1 {e.2}⟩;obtain⟨j,_,hj⟩:=bV.mp z;rw[<- hj];simp[fi];omega}
    ·
     rintro⟨r,bb⟩;rcases cD.mp r with r|r
     ·
      rcases cD.mp r with r|r
      {obtain⟨L,_,rfl⟩:=bV.mp r;simp[bP,ey] at bb;omega};{obtain⟨i,_,rfl⟩:=bV.mp r;simp[ey] at bb;omega}
     {exact r}
   have cs:e∈cb↔e∈(c M1 ∪ o M1 ∪ cb)/\n<=e.1.val:=by
    constructor;{intro r;refine⟨cD.mpr (Or.inr r),?_⟩;have z:e.1∈v M1:=aw.2.2▸bT.mpr ⟨e,r,ep e.1 {e.2}⟩;obtain⟨j,_,hj⟩:=bV.mp z;rw[<- hj];simp[fi];omega}
    ·
     rintro⟨r,bb⟩;rcases cD.mp r with r|r
     ·
      rcases cD.mp r with r|r
      {obtain⟨L,_,rfl⟩:=bV.mp r;simp[bP,ey] at bb;omega};{obtain⟨i,_,rfl⟩:=bV.mp r;simp[ey] at bb;omega}
     {exact r}
   rw[ct,ay,<- cs]
  ·
   intro S hP;simp only[aL,PM,g4] at hP;obtain⟨⟨bg,cl⟩,b1⟩:=hP
   let s:ES n:=
    ((gX n).toFinset).filter (fun e=>bP e∈S)
   let K:Ft (Fin (2*n)×Fin (2*n)):=
    S.filter (fun e=>n<=e.1.val/\n<=e.2.val)
   have b9:aQ s:=by
    refine⟨fun e r=>(gR e).mp (dO.mp (aL.mp r).1),?_⟩;intro e r f P a4;have a1:=(aL.mp r).2;have cu:=(aL.mp P).2;have hd:=bg.2 (bP e) a1 (bP f) cu (fun h=>a4 (jg h));rw[aT];intro x y w
    have cf:ey x∈aF (bP e):=by simp only[aF,aV,bI,bP] at y ⊢;rcases y with rfl|rfl <;> simp
    have ce:ey x∈aF (bP f):=by simp only[aF,aV,bI,bP] at w ⊢;rcases w with rfl|rfl <;> simp
    exact aT.mp hd cf ce
   have b4:c s=S.filter (fun e=>e.1.val<n/\e.2.val<n):=(by ext e;simp only[c,s,bV,aL,dO,gR];constructor;{rintro⟨L,⟨_,B⟩,rfl⟩;exact⟨B,L.1.isLt,L.2.isLt⟩};{rintro⟨a1,E,B⟩;refine⟨(⟨e.1.val,E⟩,⟨e.2.val,B⟩),⟨bg.1 e a1,?_⟩,eC (bL rfl) (bL rfl)⟩;have ay:bP (⟨e.1.val,E⟩,⟨e.2.val,B⟩)=e:=eC (bL rfl) (bL rfl);rw[ay];exact a1})
   have au:o s=S.filter (fun e=>e.1.val<n/\e.1.val+e.2.val+1=2*n):=by
    ext e;simp only[o,bV,mem_sdiff,dN,fR,aL];constructor
    ·
     rintro⟨i,a0,rfl⟩;refine⟨?_,i.isLt,by simp[ey,fi];omega⟩;have z:ey i∈S.biUnion aF:=cl.symm▸dN _;obtain⟨L,be,am⟩:=bT.mp z;rcases b1 L be with ⟨E,B⟩|⟨E,B⟩|⟨E,B⟩
     ·
      exfalso;have cj:L∈c s:=(by rw[b4];exact aL.mpr ⟨be,E,B⟩);obtain⟨M,bc,rfl⟩:=bV.mp cj;apply a0;refine bT.mpr ⟨M,bc,?_⟩;simp only[aF,aV,bI,bP] at am ⊢;rcases am with h|h
      {exact Or.inl (gA h)};{exact Or.inr (gA h)}
     ·
      exfalso;simp only[aF,aV,bI] at am;rcases am with h|h <;> (have:=aI Fin.val h;simp[ey] at this;omega)
     ·
      have bp:L=(ey i,fi i):=by
       simp only[aF,aV,bI] at am;rcases am with h|h
       ·
        exact eC h.symm (bL (by
         have:=aI Fin.val h;simp[ey,fi] at this ⊢;omega))
       {exfalso;have:=aI Fin.val h;simp[ey] at this;omega}
      exact bp▸be
    ·
     rintro⟨a1,E,B⟩;let i:Fin n:=⟨e.1.val,E⟩;have bd:(ey i,fi i)=e:=eC (bL rfl) (bL (by simp[fi,i];omega));refine⟨i,?_,bd⟩;intro a0;obtain⟨M,bc,bv⟩:=bT.mp a0;have ch:bP M∈S:=(aL.mp bc).2
     have a4:bP M≠e:=fun h=>by
      have:=aI (fun p=>p.2.val) h
      simp[bP,ey] at this;omega
     have hd:=bg.2 (bP M) ch e a1 a4
     have dg:ey i∈aF (bP M):=by simp only[aF,aV,bI,bP] at bv ⊢;rcases bv with h|h <;> simp[h]
     have df:ey i∈aF e:=(by rw[<- bd];exact ep _ _);exact aT.mp hd dg df
   have c9:K.biUnion aF=v s:=by
    ext x;simp only[K,v,bT,aL,bV];constructor
    ·
     rintro⟨e,⟨a1,E,B⟩,c0⟩
     have dj:n<=x.val:=by simp only[aF,aV,bI] at c0;rcases c0 with rfl|rfl <;> omega
     let i:Fin n:=⟨2*n-1-x.val,by omega⟩;have a8:fi i=x:=bL (by simp[fi,i];omega);refine⟨i,?_,a8⟩;by_contra a0;have bs:(ey i,fi i)∈S:=(by have cq:i∈univ \ s.biUnion aF:=mem_sdiff.mpr ⟨dN i,bT.not.mpr a0⟩;have:(ey i,fi i)∈o s:=bV.mpr ⟨i,cq,rfl⟩;rw[au] at this;exact (aL.mp this).1)
     have a4:(ey i,fi i)≠e:=fun h=>by
      have:=aI (fun p=>p.1.val) h;simp[ey] at this;omega
     exact aT.mp (bg.2 (ey i,fi i) bs e a1 a4) (a8▸aV.mpr (Or.inr (gk (fi i)))) c0
    ·
     rintro⟨i,a0,rfl⟩;have z:fi i∈S.biUnion aF:=cl.symm▸dN _;obtain⟨e,a1,ax⟩:=bT.mp z;rcases b1 e a1 with ⟨E,B⟩|⟨E,B⟩|⟨E,B⟩
     ·
      exfalso;simp only[aF,aV,bI] at ax;rcases ax with h|h <;> (have:=aI Fin.val h;simp[fi] at this;omega)
     {exact⟨e,⟨a1,E,B⟩,ax⟩}
     ·
      exfalso;have cv:e∈o s:=(by rw[au];exact aL.mpr ⟨a1,E,B⟩);obtain⟨j,c5,rfl⟩:=bV.mp cv;simp only[aF,aV,bI] at ax;rcases ax with h|h
      {exact bS (dW j i) h.symm};{have bm:i=j:=nD h;exact (mem_sdiff.mp c5).2 (bm▸bT.mpr a0)}
   refine⟨⟨s,K⟩,mem_sigma.mpr ⟨cP.mpr b9,g4.mpr ⟨iC bg (kO _ _),c9⟩⟩,?_⟩;rw[b4,au];ext e;simp only[K,cD,aL];constructor;{rintro ((⟨h,_,_⟩|⟨h,_,_⟩)|⟨h,_,_⟩) <;> exact h}
   ·
    intro a1;rcases b1 e a1 with ⟨E,B⟩|⟨E,B⟩|⟨E,B⟩
    {exact Or.inl (Or.inl ⟨a1,E,B⟩)};{exact Or.inr ⟨a1,E,B⟩};{exact Or.inl (Or.inr ⟨a1,E,B⟩)}
  {intro _ _;rfl}
 rw[ck];refine dB rfl fun s hM=>?_;have b3:aQ s:=cP.mp hM
 have bl:∀ K∈o5 (v s),(-1:R)^cr (c s ∪ o s ∪ K) * ∏ e∈(c s ∪ o s ∪ K),gh W e.1 e.2=((-1:R)^cr s * ∏ e∈s,W e.1 e.2)*(-1:R)^cr K:=by
  intro K bt;obtain⟨bx,af⟩:=g4.mp bt
  have ae:Disjoint (c s) (o s):=by
   rw[aT];intro e E B;obtain⟨L,_,rfl⟩:=bV.mp E;obtain⟨i,_,h⟩:=bV.mp B
   have:=aI (fun p=>p.2.val) h;simp[bP,ey,fi] at this;omega
  have an:Disjoint (c s) K:=(by rw[aT];intro e E B;obtain⟨L,_,rfl⟩:=bV.mp E;have z:ey L.1∈v s:=af▸bT.mpr ⟨bP L,B,by simp[bP,aF]⟩;obtain⟨j,_,hj⟩:=bV.mp z;exact bS (dW L.1 j) hj.symm);have ao:Disjoint (o s) K:=(by rw[aT];intro e E B;obtain⟨i,_,rfl⟩:=bV.mp E;have z:ey i∈v s:=af▸bT.mpr ⟨(ey i,fi i),B,by simp[aF]⟩;obtain⟨j,_,hj⟩:=bV.mp z;exact bS (dW i j) hj.symm);have c4:∏ e∈(c s ∪ o s ∪ K),gh W e.1 e.2=∏ e∈s,W e.1 e.2:=(by rw[prod_union (disjoint_union_left.mpr ⟨an,ao⟩),prod_union ae];have dd:∏ e∈c s,gh W e.1 e.2=∏ e∈s,W e.1 e.2:=(by rw[Finset.prod_image (fun a _ b _ h=>jg h)];refine qN rfl fun e r=>?_;have bk:=b3.1 e r;have E:(ey e.1).val<n:=e.1.isLt;have B:(ey e.2).val<n:=e.2.isLt;have cg:ey e.1<ey e.2:=lI.mpr bk;dsimp only[bP];unfold gh;rw[cT E,cT B,dP cg];rfl);have dc:∏ e∈o s,gh W e.1 e.2=1:=(by refine Finset.prod_eq_one fun e r=>?_;obtain⟨i,_,rfl⟩:=bV.mp r;have hi:(ey i).val<n:=i.isLt;have hr:¬ (fi i).val<n:=(by simp[fi];omega);have ay:(ey i).val+(fi i).val+1=2*n:=(by simp[ey,fi];omega);simp[gh,hi,hr,ay]);have db:∏ e∈K,gh W e.1 e.2=1:=(by refine Finset.prod_eq_one fun e r=>?_;have bk:=bx.1 e r;have E:e.1∈v s:=af▸bT.mpr ⟨e,r,by simp[aF]⟩;have B:e.2∈v s:=af▸bT.mpr ⟨e,r,by simp[aF]⟩;obtain⟨i,_,hi⟩:=bV.mp E;obtain⟨j,_,hj⟩:=bV.mp B;have cp:¬ e.1.val<n:=(by rw[<- hi];simp[fi];omega);have co:¬ e.2.val<n:=(by rw[<- hj];simp[fi];omega);simp[gh,cp,co,bk]);rw[dd,dc,db,kQ,kQ]);have b7:cr (c s)=cr s:=(by unfold cr;symm;refine nR (fun (p:(EP n)×(EP n)) _=>(bP p.1,bP p.2)) ?_ ?_ ?_;{intro p Q;simp only[aL,cX,c,bV,eS] at Q ⊢;exact⟨⟨⟨p.1,Q.1.1,rfl⟩,⟨p.2,Q.1.2,rfl⟩⟩,Q.2⟩};{intro p _ q _ h;exact eC (jg (aI Prod.fst h)) (jg (aI Prod.snd h))};{rintro⟨q1,q2⟩ hq;simp only[aL,cX,c,bV] at hq;obtain⟨⟨⟨e1,cx,rfl⟩,⟨e2,cw,rfl⟩⟩,cy⟩:=hq;exact⟨(e1,e2),by simp only[aL,cX,eS];exact⟨⟨cx,cw⟩,cy⟩,rfl⟩});have b8:cr (o s)=0:=(by rw[cr,card_eq_zero,uN];intro p Q;simp only[cX,o,bV] at Q;obtain⟨⟨i,_,hi⟩,⟨j,_,hj⟩⟩:=Q;simp only[eS,<- hi,<- hj,ey,fi,iU];omega);have av:∀ di dh:Ft (Fin (2*n)×Fin (2*n)),fK di dh=fK dh di:=(by intro di dh;unfold fK;refine nR (fun (p:(Fin (2*n)×Fin (2*n))×(Fin (2*n)×Fin (2*n))) _=>(p.2,p.1)) ?_ ?_ ?_;{intro p Q;simp only[aL,cX,g8] at Q ⊢;exact⟨⟨Q.1.2,Q.1.1⟩,Q.2.symm⟩};{intro _ _ _ _ h;exact eC (aI Prod.snd h) (aI Prod.fst h)};{intro q hq;simp only[aL,cX,g8] at hq;exact⟨(q.2,q.1),by simp only[aL,cX,g8];exact⟨⟨hq.1.2,hq.1.1⟩,hq.2.symm⟩,rfl⟩})
  have ak:fK (c s) K=0:=(by rw[fK,card_eq_zero,uN];intro p Q;simp only[cX,c,bV] at Q;obtain⟨⟨L,_,a5⟩,aw⟩:=Q;have E:p.2.1∈v s:=af▸bT.mpr ⟨p.2,aw,by simp[aF]⟩;have B:p.2.2∈v s:=af▸bT.mpr ⟨p.2,aw,by simp[aF]⟩;obtain⟨i,_,hi⟩:=bV.mp E;obtain⟨j,_,hj⟩:=bV.mp B;simp only[g8,eS,<- a5,bP,ey,<- hi,<- hj,fi,iU];omega);have aj:fK (c s ∪ o s) K=fK (c s) K+fK (o s) K:=(by unfold fK;have Q:(c s ∪ o s) ×ˢ K=(c s ×ˢ K) ∪ (o s ×ˢ K):=(by ext⟨a,b⟩;simp only[cX,cD];tauto);rw[Q,filter_union,qG];rw[aT];intro p E B;exact aT.mp ae (cX.mp (aL.mp E).1).1 (cX.mp (aL.mp B).1).1)
  have b0:aQ (c s):=by
   refine⟨fun e r=>by obtain⟨L,a5,rfl⟩:=bV.mp r;exact lI.mpr (b3.1 L a5),?_⟩;intro e r f P a4;obtain⟨L,a5,rfl⟩:=bV.mp r;obtain⟨M,ar,rfl⟩:=bV.mp P;have a9:L≠M:=fun h=>a4 (aI bP h);rw[aT];intro x y w;simp only[bP,aF,aV,bI] at y w;rcases y with rfl|rfl <;> rcases w with h|h
   {exact aT.mp (b3.2 L a5 M ar a9) (ep L.1 {L.2}) ((gA h)▸ep M.1 {M.2})};{exact aT.mp (b3.2 L a5 M ar a9) (ep L.1 {L.2}) ((gA h)▸aV.mpr (Or.inr (gk M.2)))};{exact aT.mp (b3.2 L a5 M ar a9) (aV.mpr (Or.inr (gk L.2))) ((gA h)▸ep M.1 {M.2})};{exact aT.mp (b3.2 L a5 M ar a9) (aV.mpr (Or.inr (gk L.2))) ((gA h)▸aV.mpr (Or.inr (gk M.2)))}
  have cm:(c s).biUnion aF=(s.biUnion aF).image ey:=(by ext x;simp only[c,bT,bV,bP,aF,aV,bI];constructor;{rintro⟨_,⟨e,r,rfl⟩,rfl|rfl⟩;{exact⟨e.1,⟨e,r,Or.inl rfl⟩,rfl⟩};{exact⟨e.2,⟨e,r,Or.inr rfl⟩,rfl⟩}};{rintro⟨u,⟨e,r,rfl|rfl⟩,rfl⟩;{exact⟨(ey e.1,ey e.2),⟨e,r,rfl⟩,Or.inl rfl⟩};{exact⟨(ey e.1,ey e.2),⟨e,r,rfl⟩,Or.inr rfl⟩}})
  have bu:(fK (c s) (o s)+fK K (o s)) % 2=0:=by
   rw[kc,kc,<- sB,lB]
   have bi:∀ d∈o s,(((c s).filter (fun f=>g8 f d)).card+(K.filter (fun f=>g8 f d)).card) % 2=0:=by
    intro d hd;obtain⟨i,a0,rfl⟩:=bV.mp hd;have bw:i∉s.biUnion aF:=(mem_sdiff.mp a0).2
    have br:Disjoint ((c s).biUnion aF) (aF (ey i,fi i)):=by
     rw[cm,aT];intro x y w;obtain⟨u,c1,rfl⟩:=bV.mp y;simp only[aF,aV,bI] at w;rcases w with h|h
     {exact bw (gA h▸c1)};{exact bS (dW u i) h}
    have bq:Disjoint (K.biUnion aF) (aF (ey i,fi i)):=by
     rw[af];dsimp only[v];rw[aT];intro x y w;obtain⟨u,c1,rfl⟩:=bV.mp y;simp only[aF,aV,bI] at w;rcases w with h|h
     {exact bS (dW i u) h.symm};{exact bw (nD h▸c1)}
    have b6:=hZ b0 (dW i i) br;have aw:=hZ bx (dW i i) bq;have b2:(((c s).biUnion aF).filter (fun x=>ey i<x/\x<fi i)).card=((K.biUnion aF).filter (fun x=>ey i<x/\x<fi i)).card:=(by rw[cm,af];dsimp only[v];have hL:((s.biUnion aF).image ey).filter (fun x=>ey i<x/\x<fi i)=((s.biUnion aF).filter (fun u=>i<u)).image ey:=(by ext x;simp only[aL,bV];constructor;{rintro⟨⟨u,hu,rfl⟩,E,_⟩;exact⟨u,⟨hu,lI.mp E⟩,rfl⟩};{rintro⟨u,⟨hu,c6⟩,rfl⟩;exact⟨⟨u,hu,rfl⟩,lI.mpr c6,dW u i⟩});have hR:((s.biUnion aF).image fi).filter (fun x=>ey i<x/\x<fi i)=((s.biUnion aF).filter (fun u=>i<u)).image fi:=(by ext x;simp only[aL,bV];constructor;{rintro⟨⟨u,hu,rfl⟩,_,B⟩;exact⟨u,⟨hu,te.mp B⟩,rfl⟩};{rintro⟨u,⟨hu,c6⟩,rfl⟩;exact⟨⟨u,hu,rfl⟩,dW i u,te.mpr c6⟩});rw[hL,hR,o6 _ gA,o6 _ nD]);rw[b2] at b6;have dk:((c s).filter (fun f=>g8 f (ey i,fi i))).card % 2=(K.filter (fun f=>g8 f (ey i,fi i))).card % 2:=b6.trans aw.symm;omega
   rw[dB rfl bi];simp
  have bf:cr (c s ∪ o s ∪ K) % 2=(cr s+cr K) % 2:=(by rw[jx (disjoint_union_left.mpr ⟨an,ao⟩),jx ae,b7,b8,aj,ak,av (o s) K];omega);rw[c4,gC bf,j8];ring
 rw[dB rfl bl,<- mM,vF s.card (v s) (by rw[o6 _ nD,kX b3]),kQ]
def cH{n:Nat}(b:ES n):Ft (CP n):=(b ×ˢ b).filter (fun p:(EP n)×(EP n)=>eS p.1 p.2)
def bF{n:Nat}(C:Ft (CP n)):ES n:=C.biUnion (fun p=>{p.1,p.2})
open Classical in
def jj{n:Nat}{R:Type*}[CommRing R](W:Fin n->Fin n->R)(F:ES n):Fin n->Fin n->R:=fun u v=>
 let b:=F.biUnion aF
 if u∈b\/v∈b then 0
 else (-1:R)^(b.filter (fun x=>u<x/\x<v)).card*W u v
lemma oz{n:Nat}{R:Type*}[CommRing R](c:ES n):(1:R)=(-1:R)^cr c * ∑ C∈(cH c).powerset,(-2:R)^C.card:=by
 have d:∀ s:Ft (CP n),∑ C∈s.powerset,(-2:R)^C.card=(1+(-2:R))^s.card:=by
  intro s;induction s using qK with
  | empty=>simp
  | @insert a s ha ih=>
    rw[Finset.powerset_insert,sT,sU,o7 ha,gN];{have e:∑ C∈s.powerset,(-2:R)^(insert a C).card=(-2:R) * ∑ C∈s.powerset,(-2:R)^C.card:=(by rw[mM];refine dB rfl fun C x=>?_;have j:a∉C:=fun i=>ha (mem_powerset.mp x i);rw[o7 j,gN,kP]);rw[e,ih];ring}
    ·
     intro B w L v h;have q:a∉B:=fun i=>ha (mem_powerset.mp w i);have o:a∉L:=fun i=>ha (mem_powerset.mp v i)
     have:=aI (fun X=>X.erase a) h
     simpa[qL q,qL o] using this
    {rw[aT];intro X u r;obtain⟨z,_,rfl⟩:=mem_image.mp r;exact ha (mem_powerset.mp u (ep a z))}
 have y:(∑ C∈(cH c).powerset,(-2:R)^C.card)=(-1:R)^(cH c).card:=(by rw[d];norm_num);have b:(cH c).card=cr c:=rfl;rw[y,b,<- mul_pow];norm_num
lemma tV{n:Nat}{R:Type*}[CommRing R](W:Fin n->Fin n->R)(F:ES n)(K:aQ F):(-1:R)^cr F*(∏ e∈F,W e.1 e.2)*jn (gh (jj W F))=∑ E∈(cE n).filter (fun E=>F⊆E),(-1:R)^cr E * ∏ e∈E,W e.1 e.2:=by
 classical
 rw[xc];let z:=F.biUnion aF
 have L:∀ d∈cE n,¬Disjoint (d.biUnion aF) z->(-1:R)^cr d * ∏ e∈d,jj W F e.1 e.2=0:=by
  intro d _ hnd;rw[uT] at hnd;obtain⟨x,Q,y⟩:=hnd;obtain⟨e,c,w⟩:=bT.mp Q
  have h0:jj W F e.1 e.2=0:=by
   unfold jj;simp only[aF,aV,bI] at w;rcases w with rfl|rfl
   {simp[z,y]};{simp[z,y]}
  rw[qI c h0,mul_zero]
 rw[<- sum_filter_of_ne (p:=fun d=>Disjoint (d.biUnion aF) z) (fun d j q=>by_contra fun h=>q (L d j h))];rw[mM];refine nV (fun d _=>F ∪ d) ?_ ?_ ?_ ?_
 ·
  intro d j;simp only[aL,cP] at j ⊢;obtain⟨o,b⟩:=j;refine⟨⟨?_,?_⟩,subset_union_left⟩
  ·
   intro e s;rcases cD.mp s with s|s
   {exact K.1 e s};{exact o.1 e s}
  ·
   intro e s f B q;rcases cD.mp s with s|s <;> rcases cD.mp B with B|B
   {exact K.2 e s f B q};{exact (b.mono (gJ aF B) (gJ aF s)).symm};{exact b.mono (gJ aF s) (gJ aF B)};{exact o.2 e s f B q}
 {intro M1 a7 S a6 aa;simp only[aL,cP] at a7 a6;have af:Disjoint F M1:=(by rw[aT];intro e u r;exact aT.mp a7.2 (bT.mpr ⟨e,r,ep e.1 {e.2}⟩) (bT.mpr ⟨e,u,ep e.1 {e.2}⟩));have ae:Disjoint F S:=(by rw[aT];intro e u ab;exact aT.mp a6.2 (bT.mpr ⟨e,ab,ep e.1 {e.2}⟩) (bT.mpr ⟨e,u,ep e.1 {e.2}⟩));have P:(F ∪ M1) \ F=M1:=Finset.union_sdiff_cancel_left af;have M:(F ∪ S) \ F=S:=Finset.union_sdiff_cancel_left ae;rw[<- P,aa,M]};{intro E hM;simp only[aL,cP] at hM;obtain⟨a5,a8⟩:=hM;refine⟨E \ F,?_,Finset.union_sdiff_of_subset a8⟩;simp only[aL,cP];refine⟨iC a5 sdiff_subset,?_⟩;rw[aT];intro x Q y;obtain⟨e,r,w⟩:=bT.mp Q;obtain⟨f,a4,a9⟩:=bT.mp y;have q:e≠f:=fun h=>(mem_sdiff.mp r).2 (h▸a4);exact aT.mp (a5.2 e (mem_sdiff.mp r).1 f (a8 a4) q) w a9}
 ·
  intro d j;simp only[aL,cP] at j;obtain⟨o,b⟩:=j;have v:Disjoint F d:=(by rw[aT];intro e u r;exact aT.mp b (bT.mpr ⟨e,r,ep e.1 {e.2}⟩) (bT.mpr ⟨e,u,ep e.1 {e.2}⟩))
  have i:∏ e∈d,jj W F e.1 e.2=(-1:R)^fK F d * ∏ e∈d,W e.1 e.2:=by
   have a1:∀ e∈d,jj W F e.1 e.2=(-1:R)^(F.filter (fun f=>g8 f e)).card*W e.1 e.2:=by
    intro e c;have P:e.1∉z:=fun h=>aT.mp b (bT.mpr ⟨e,c,by simp[aF]⟩) h;have M:e.2∉z:=fun h=>aT.mp b (bT.mpr ⟨e,c,by simp[aF]⟩) h
    have ad:Disjoint z (aF e):=by rw[lD];intro x hx;simp only[aF,aV,bI] at hx;rcases hx with rfl|rfl <;> assumption
    unfold jj;simp only[z,P,M,or_self,↓reduceIte];congr 1;exact gC (hZ K (o.1 e c) ad).symm
   rw[qN rfl a1,prod_mul_distrib,uM,kc]
  rw[i,jx v,prod_union v,j8,j8];ring
lemma rF{n k:Nat}(c:ES n)(W:Fin n->Fin n->PZ)(j:∀ e:EP n,e.1<e.2->e∉c->W e.1 e.2=0)(d:Nat):(∑ b∈cE n,∏ e∈b,W e.1 e.2).coeff d ≡ (∑ C∈(cH c).powerset.filter (fun C=>C.card<k/\aQ (bF C)),(-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,W e.1 e.2)*jn (gh (jj W (bF C)))).coeff d [ZMOD (2:Int)^k]:=by
 classical
 have y:∑ b∈cE n,∏ e∈b,W e.1 e.2=∑ b∈(cE n).filter (fun b=>b⊆c),∏ e∈b,W e.1 e.2:=(by symm;refine sum_filter_of_ne fun b z r=>?_;by_contra q;rw[not_subset] at q;obtain⟨e,u,Q⟩:=q;exact r (qI u (j e ((cP.mp z).1 e u) Q)))
 have a8:∑ b∈(cE n).filter (fun b=>b⊆c),∏ e∈b,W e.1 e.2=∑ C∈(cH c).powerset.filter (fun C=>aQ (bF C)),(-2:PZ)^C.card * ∑ b∈(cE n).filter (fun b=>bF C⊆b),(-1:PZ)^cr b * ∏ e∈b,W e.1 e.2:=by
  have P:∑ b∈(cE n).filter (fun b=>b⊆c),∏ e∈b,W e.1 e.2=∑ b∈(cE n).filter (fun b=>b⊆c),∑ C∈(cH c).powerset.filter (fun C=>bF C⊆b),(-2:PZ)^C.card*((-1:PZ)^cr b * ∏ e∈b,W e.1 e.2):=by
   refine dB rfl fun b z=>?_;have ab:b⊆c:=(aL.mp z).2
   have a4:(cH c).powerset.filter (fun C=>bF C⊆b)=(cH b).powerset:=by
    ext C;simp only[aL,pz,cH,bF,Finset.biUnion_subset_iff_forall_subset];constructor;{rintro⟨ai,L⟩ p a7;have a6:=ai a7;simp only[aL,cX] at a6 ⊢;have h:=L p a7;exact⟨⟨h (by simp),h (by simp)⟩,a6.2⟩}
    ·
     intro L;refine⟨fun p K=>?_,fun p K=>?_⟩;{have h:=L K;simp only[aL,cX] at h ⊢;exact⟨⟨ab h.1.1,ab h.1.2⟩,h.2⟩}
     ·
      have h:=L K;simp only[aL,cX] at h;intro e S;simp only[aV,bI] at S;rcases S with rfl|rfl
      {exact h.1.1};{exact h.1.2}
   rw[a4,<- sum_mul];have ho:=oz (R:=PZ) b
   calc ∏ e∈b,W e.1 e.2=1 * ∏ e∈b,W e.1 e.2:=(j9 _).symm
    _=((-1:PZ)^cr b * ∑ C∈(cH b).powerset,(-2:PZ)^C.card) * ∏ e∈b,W e.1 e.2:=by rw[<- ho]
    _=(∑ C∈(cH b).powerset,(-2:PZ)^C.card)*((-1:PZ)^cr b * ∏ e∈b,W e.1 e.2):=by ring
  rw[P]
  have a1:∑ b∈(cE n).filter (fun b=>b⊆c),∑ C∈(cH c).powerset.filter (fun C=>bF C⊆b),(-2:PZ)^C.card*((-1:PZ)^cr b * ∏ e∈b,W e.1 e.2)=∑ C∈(cH c).powerset,∑ b∈((cE n).filter (fun b=>b⊆c)).filter (fun b=>bF C⊆b),(-2:PZ)^C.card*((-1:PZ)^cr b * ∏ e∈b,W e.1 e.2):=by simp_rw [sO];rw[sum_comm];refine dB rfl fun b _=>?_;split_ifs <;> simp
  rw[a1];have w:∑ C∈(cH c).powerset,∑ b∈((cE n).filter (fun b=>b⊆c)).filter (fun b=>bF C⊆b),(-2:PZ)^C.card*((-1:PZ)^cr b * ∏ e∈b,W e.1 e.2)=∑ C∈(cH c).powerset.filter (fun C=>aQ (bF C)),∑ b∈((cE n).filter (fun b=>b⊆c)).filter (fun b=>bF C⊆b),(-2:PZ)^C.card*((-1:PZ)^cr b * ∏ e∈b,W e.1 e.2):=(by symm;refine sum_filter_of_ne fun C _ r=>?_;by_contra af;apply r;refine sJ fun b z=>?_;simp only[aL,cP] at z;exact (af (iC z.1.1 z.2)).elim);rw[w];refine dB rfl fun C _=>?_;rw[<- mM];congr 1;have a2:((cE n).filter (fun b=>b⊆c)).filter (fun b=>bF C⊆b)=((cE n).filter (fun b=>bF C⊆b)).filter (fun b=>b⊆c):=(by ext b;simp only[aL];tauto);rw[a2];refine sum_filter_of_ne fun b z r=>?_;by_contra q;rw[not_subset] at q;obtain⟨e,u,Q⟩:=q;have ah:aQ b:=cP.mp (aL.mp z).1;exact r (by rw[qI u (j e (ah.1 e u) Q),mul_zero])
 rw[y,a8];have o:∑ C∈(cH c).powerset.filter (fun C=>aQ (bF C)),(-2:PZ)^C.card * ∑ b∈(cE n).filter (fun b=>bF C⊆b),(-1:PZ)^cr b * ∏ e∈b,W e.1 e.2=∑ C∈(cH c).powerset.filter (fun C=>aQ (bF C)),(-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,W e.1 e.2)*jn (gh (jj W (bF C))):=(by refine dB rfl fun C E=>?_;simp only[aL,pz] at E;rw[<- tV W (bF C) E.2];ring);rw[o];let B:=(cH c).powerset.filter (fun C=>aQ (bF C));have v:B=B.filter (fun C=>C.card<k) ∪ B.filter (fun C=>¬ C.card<k):=(by ext C;simp only[cD,aL];tauto);have aa:B.filter (fun C=>C.card<k)=(cH c).powerset.filter (fun C=>C.card<k/\aQ (bF C)):=(by ext C;simp only[B,aL];tauto);change (∑ C∈B,(-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,W e.1 e.2)*jn (gh (jj W (bF C)))).coeff d ≡ _ [ZMOD _];have x:Disjoint (B.filter (fun C=>C.card<k)) (B.filter (fun C=>¬ C.card<k)):=aT.mpr fun C P M=>(aL.mp M).2 (aL.mp P).2;rw[v,sT x,aa,sD]
 have a9:((2:Int)^k) ∣ (∑ C∈B.filter (fun C=>¬ C.card<k),(-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,W e.1 e.2)*jn (gh (jj W (bF C)))).coeff d:=by
  have i:∀(t:Ft (Ft (CP n))) (f:Ft (CP n)->PZ),(∑ C∈t,f C).coeff d=∑ C∈t,(f C).coeff d:=by
   intro t f;induction t using qK with
   | empty=>simp
   | insert a s ha ih=>rw[kK ha,kK ha,sD,ih]
  rw[i];refine Finset.dvd_sum fun C E=>?_;have ag:k<=C.card:=Nat.le_of_not_lt (aL.mp E).2;have M:(-2:PZ)^C.card=Polynomial.C ((-2:Int)^C.card):=(by rw[map_pow];simp);rw[mR,mR,M,coeff_C_mul];apply dvd_mul_of_dvd_left;have a5:(-2:Int)^C.card=(-1:Int)^C.card*(2:Int)^C.card:=(by rw[<- mul_pow];norm_num);rw[a5];exact dvd_mul_of_dvd_right (pow_dvd_pow (2:Int) ag) _
 simpa only[g1] using Int.ModEq.add_left _ (Int.modEq_zero_iff_dvd.mpr a9)
def invFun{n:Nat}(p:Pm (Fin n))(x y:Fin n->Bo):Bo:=
 decide (∃ i:Fin n,(x i=true/\y i=true)\/(p i≠i/\((x i=true/\x (p i)=true)\/(y i=true/\y (p i)=true))))
def cV{n:Nat}(p:Pm (Fin n)):ES n:=(gX n).toFinset.filter (fun e=>p e.1=e.2)
lemma cA{n:Nat}(p:Pm (Fin n))(e:EP n):e∈cV p↔e.1<e.2/\p e.1=e.2:=by simp only[cV,aL,dO,gR]
lemma io{n:Nat}(p:Pm (Fin n))(i:Involutive p):aQ (cV p):=by
 refine⟨fun e s=>(cA p e).mp s |>.1,?_⟩;intro e s f v q;obtain⟨r,b⟩:=(cA p e).mp s;obtain⟨d,c⟩:=(cA p f).mp v;rw[aT];intro x o j;simp only[aF,aV,bI] at o j;rcases o with rfl|rfl <;> rcases j with h|h
 {exact q (eC h (by rw[<- b,<- c,h]))}
 ·
  have:e.1=f.1:=by rw[<- i f.1,c,<- h,b];exact absurd (h▸d) (e7 (by
   have u:p e.2=e.1:=(by rw[<- b,i e.1]);have:e.2=f.1:=(by rw[<- b,h,<- c,i f.1]);omega))
  exact bS d (h.symm.trans this).symm
 ·
  have:f.2=e.1:=by rw[<- c,<- h,<- b,i e.1]
  exact e7 r (by rw[<- this];exact hK (h▸d) (by omega))
 {have w:e.1=f.1:=(by rw[<- i e.1,b,h,<- c,i f.1]);exact q (eC w h)}
open Classical in
def gw{n:Nat}(b:ES n)(i:Fin n):Fin n:=if h1:∃ j,(i,j)∈b then Classical.choose h1
 else if h2:∃ j,(j,i)∈b then Classical.choose h2
 else i
lemma fZ{n:Nat}{e:ES n}(o:aQ e){a b:Fin n}(c:(a,b)∈e):gw e a=b/\gw e b=a:=by
 classical
 have u:∃ j,(a,j)∈e:=⟨b,c⟩;have w:gw e a=b:=(by unfold gw;rw[cT u];have q:=f9 u;by_contra d;exact aT.mp (o.2 _ q _ c (fun h=>d (aI Prod.snd h))) (ep a _) (ep a _));have i:¬∃ j,(b,j)∈e:=(by rintro⟨j,r⟩;have d:(b,j)≠(a,b):=fun h=>bS (o.1 _ c) (aI Prod.fst h).symm;exact aT.mp (o.2 _ r _ c d) (ep b _) (aV.mpr (Or.inr (gk b))));have s:∃ j,(j,b)∈e:=⟨a,c⟩;have v:gw e b=a:=(by unfold gw;rw[lF i,cT s];have q:=f9 s;by_contra d;exact aT.mp (o.2 _ q _ c (fun h=>d (aI Prod.fst h))) (aV.mpr (Or.inr (gk b))) (aV.mpr (Or.inr (gk b))));exact⟨w,v⟩
lemma mf{n:Nat}{b:ES n}(o:aQ b):Involutive (gw b):=by
 classical
 intro i;by_cases r:∃ j,(i,j)∈b;{obtain⟨j,d⟩:=r;have h:=fZ o d;rw[h.1,h.2]};{by_cases q:∃ j,(j,i)∈b;{obtain⟨j,c⟩:=q;have h:=fZ o c;rw[h.2,h.1]};{have e:gw b i=i:=(by unfold gw;rw[lF r,lF q]);rw[e,e]}}
def tl{n:Nat}(b:ES n)(c:aQ b):Pm (Fin n):=(mf c).toPerm (gw b)
lemma oD{n:Nat}(c:ES n)(b:aQ c):Involutive (tl c b):=mf b
lemma os{n:Nat}(d:ES n)(e:aQ d):cV (tl d e)=d:=by
 classical
 ext⟨a,b⟩;rw[cA];constructor
 ·
  rintro⟨c,o⟩;change gw d a=b at o;by_cases s:∃ j,(a,j)∈d
  ·
   obtain⟨j,i⟩:=s
   have:=(fZ e i).1
   rw[<- o,this];exact i
  ·
   by_cases r:∃ j,(j,a)∈d
   ·
    obtain⟨j,h⟩:=r
    have:=(fZ e h).2
    have q:j=b:=this.symm.trans o
    have:=e.1 _ h
    exact absurd (q▸this) (e7 c)
   ·
    have:gw d a=a:=by unfold gw;rw[lF s,lF r]
    exact absurd (this.symm.trans o) (bS c)
 {intro c;exact⟨e.1 _ c,(fZ e c).1⟩}
lemma lg{n:Nat}(p:Pm (Fin n))(o:Involutive p):tl (cV p) (io p o)=p:=by
 classical
 apply Equiv.ext;intro i;change gw (cV p) i=p i;rcases qT i (p i) with q|h|v
 {have b:(i,p i)∈cV p:=(cA p _).mpr ⟨q,rfl⟩;exact (fZ (io p o) b).1}
 ·
  have e:¬∃ j,(i,j)∈cV p:=(by rintro⟨j,s⟩;obtain⟨u,c⟩:=(cA p _).mp s;exact bS u (h.trans c))
  have d:¬∃ j,(j,i)∈cV p:=by
   rintro⟨j,s⟩;obtain⟨r,c⟩:=(cA p _).mp s;have:j=p i:=by rw[<- o j,c]
   exact bS r (this.trans h.symm)
  unfold gw;rw[lF e,lF d];exact h
 {have b:(p i,i)∈cV p:=(cA p _).mpr ⟨v,o i⟩;exact (fZ (io p o) b).2}
lemma iO{n:Nat}(p:Pm (Fin n))(y:Involutive p)(R T:Fv n):invFun p (fun i=>decide (i∈R)) (fun j=>decide (j∈T))=true↔¬Disjoint R T\/∃ e∈cV p,aF e⊆R\/aF e⊆T:=by
 simp only[invFun,cG,uT];constructor
 ·
  rintro⟨i,⟨q,o⟩|⟨s,⟨q,w⟩|⟨o,v⟩⟩⟩;{exact Or.inl ⟨i,q,o⟩}
  ·
   right;rcases iR s with c|r
   ·
    refine⟨(p i,i),(cA p _).mpr ⟨c,y i⟩,Or.inl ?_⟩;intro x d;simp only[aF,aV,bI] at d;rcases d with rfl|rfl <;> assumption
   ·
    refine⟨(i,p i),(cA p _).mpr ⟨r,rfl⟩,Or.inl ?_⟩;intro x d;simp only[aF,aV,bI] at d;rcases d with rfl|rfl <;> assumption
  ·
   right;rcases iR s with c|r
   ·
    refine⟨(p i,i),(cA p _).mpr ⟨c,y i⟩,Or.inr ?_⟩;intro x d;simp only[aF,aV,bI] at d;rcases d with rfl|rfl <;> assumption
   ·
    refine⟨(i,p i),(cA p _).mpr ⟨r,rfl⟩,Or.inr ?_⟩;intro x d;simp only[aF,aV,bI] at d;rcases d with rfl|rfl <;> assumption
 {rintro (⟨i,q,o⟩|⟨e,u,b|b⟩);{exact⟨i,Or.inl ⟨q,o⟩⟩};{obtain⟨c,h⟩:=(cA p e).mp u;refine⟨e.1,Or.inr ⟨h.symm▸ne_of_gt c,Or.inl ⟨b (by simp[aF]),h▸b (by simp[aF])⟩⟩⟩};{obtain⟨c,h⟩:=(cA p e).mp u;refine⟨e.1,Or.inr ⟨h.symm▸ne_of_gt c,Or.inr ⟨b (by simp[aF]),h▸b (by simp[aF])⟩⟩⟩}}
lemma qh{n:Nat}(p:Pm (Fin n))(K:Involutive p):(((gX n).map (fun e=>invFun p (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id).length=(cV p).card:=by
 have Q:∀ e∈gX n,invFun p (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n)))=
  decide (e∈cV p):=by
  intro e B;apply Bool.eq_iff_iff.mpr;rw[iO p K,cG];simp only[uK,sL,false_or,Finset.subset_empty];constructor
  ·
   rintro⟨f,c,d|r⟩
   ·
    have S:(aF f).card=2:=lC (bS ((cA p f).mp c).1);have y:(aF e).card=2:=lC (bS ((gR e).mp B));have q:aF f=aF e:=nH d (by omega);have o:f.1∈aF e:=q▸(by simp[aF]);have h:f.2∈aF e:=q▸(by simp[aF]);have b:=((cA p f).mp c).1;have s:=(gR e).mp B;simp only[aF,aV,bI] at o h
    have L:f=e:=by
     rcases o with w|w <;> rcases h with v|v
     {exact absurd (w.trans v.symm) (bS b)};{exact eC w v};{exact absurd (w▸v▸b) (e7 s)};{exact absurd (w.trans v.symm) (bS b)}
    exact L▸c
   {exact absurd (by simp[aF]:f.1∈aF f) (r▸sG f.1)}
  {intro u;exact⟨e,u,Or.inl subset_rfl⟩}
 have P:((gX n).map (fun e=>invFun p (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id=((gX n).filter (fun e=>decide (e∈cV p))).map (fun _=>true):=by
  clear Q
  have z:∀ e∈gX n,invFun p (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n)))=
   decide (e∈cV p):=by
   intro e B;apply Bool.eq_iff_iff.mpr;rw[iO p K,cG];simp only[uK,sL,false_or,Finset.subset_empty];constructor
   ·
    rintro⟨f,c,d|r⟩
    ·
     have S:(aF f).card=2:=lC (bS ((cA p f).mp c).1);have y:(aF e).card=2:=lC (bS ((gR e).mp B));have q:aF f=aF e:=nH d (by omega);have o:f.1∈aF e:=q▸(by simp[aF]);have h:f.2∈aF e:=q▸(by simp[aF]);have b:=((cA p f).mp c).1;have s:=(gR e).mp B;simp only[aF,aV,bI] at o h
     have L:f=e:=by
      rcases o with w|w <;> rcases h with v|v
      {exact absurd (w.trans v.symm) (bS b)};{exact eC w v};{exact absurd (w▸v▸b) (e7 s)};{exact absurd (w.trans v.symm) (bS b)}
     exact L▸c
    {exact absurd (by simp[aF]:f.1∈aF f) (r▸sG f.1)}
   {intro u;exact⟨e,u,Or.inl subset_rfl⟩}
  rw[dF z,sX];induction gX n with
  | nil=>simp
  | cons a l E=>simp only[po,qH,id_eq];by_cases M:a∈cV p;{have hd:decide (a∈cV p)=true:=jG M;simp only[hd,↓reduceIte,aO,E]};{have hd:decide (a∈cV p)=false:=iw M;simp only[hd,eX,↓reduceIte,E]}
 rw[P,ft];have x:((gX n).filter (fun e=>decide (e∈cV p))).Nodup:=(wM n).filter _;rw[<- nI x];congr 1;ext e;simp only[dO,gd,cG,gR,u0];intro u;exact ((cA p e).mp u).1
abbrev fy{n:Nat}(S:ES n)(t:(Fv n×Fv n)×Bo):Prop:=Disjoint t.1.1 t.1.2/\∀ e∈S,aF e⊆t.1.1\/aF e⊆t.1.2
def qi{n:Nat}(b:ES n)(R T:Fv n):Bo:=
 decide (¬Disjoint R T\/∃ e∈b,aF e⊆R\/aF e⊆T)
def lT{n:Nat}(b:Sf n)(c:ES n):Nat:=(b.filter (fun t=>decide (qi c t.1.1 t.1.2=t.2))).length
def cO{n:Nat}(b:Sf n):Nat:=(b.filter (fun t=>if Disjoint t.1.1 t.1.2 then !t.2 else t.2)).length
def rU{n:Nat}(b:Sf n)(e:EP n):Nat:=(b.filter (fun t=>t.2&&decide (fy {e} t))).length
def th{n:Nat}(b:Sf n)(e:EP n):Nat:=(b.filter (fun t=>!t.2&&decide (fy {e} t))).length
def cZ{n:Nat}(b:Sf n)(e:EP n):Nat:=(2*b.length+1)+rU b e-th b e
lemma uy{n:Nat}(b:Sf n)(e:EP n):th b e<=b.length:=qE _ _
lemma oI{q:Type*}[DecidableEq q](c:Ft q):∑ b∈c.powerset.erase ∅,(-1:Int)^(b.card-1)=if c.Nonempty then 1 else 0:=by
 by_cases r:c.Nonempty
 ·
  rw[dP r]
  have h0:∑ b∈c.powerset,(-1:Int)^b.card=0:=by
   have e:∀ s:Ft q,∑ b∈s.powerset,(-1:Int)^b.card=(1+(-1:Int))^s.card:=by
    intro s;induction s using qK with
    | empty=>simp
    | @insert a s ha ih=>
      rw[Finset.powerset_insert,sT,sU,o7 ha,gN];{have j:∑ b∈s.powerset,(-1:Int)^(insert a b).card=(-1:Int) * ∑ b∈s.powerset,(-1:Int)^b.card:=(by rw[mM];refine dB rfl fun b B=>?_;have v:a∉b:=fun o=>ha (mem_powerset.mp B o);rw[o7 v,gN,kP]);rw[j,ih];ring}
      ·
       intro Q M P L h;have x:a∉Q:=fun o=>ha (mem_powerset.mp M o);have w:a∉P:=fun o=>ha (mem_powerset.mp L o)
       have:=aI (fun X=>X.erase a) h
       simpa[qL x,qL w] using this
      {rw[aT];intro X z y;obtain⟨E,_,rfl⟩:=mem_image.mp y;exact ha (mem_powerset.mp z (ep a E))}
   rw[e];have i:c.card≠0:=Nat.pos_iff_ne_zero.mp (card_pos.mpr r);simp[i]
  have d:∑ b∈c.powerset,(-1:Int)^b.card=(-1:Int)^(∅:Ft q).card+∑ b∈c.powerset.erase ∅,(-1:Int)^b.card:=(u5 c.powerset _ (Finset.empty_mem_powerset c)).symm
  have a3:∑ b∈c.powerset.erase ∅,(-1:Int)^b.card=-∑ b∈c.powerset.erase ∅,(-1:Int)^(b.card-1):=by
   rw[<- sum_neg_distrib];refine dB rfl fun b B=>?_;have u:b≠∅:=(fL.mp B).1;have S:1<=b.card:=card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr u);conv_lhs=>rw[show b.card=(b.card-1)+1 by omega,gN]
   ring
  simp only[Finset.card_empty,pow_zero] at d
  linarith
 {rw[cM r];have K:c=∅:=Finset.not_nonempty_iff_eq_empty.mp r;subst K;simp}
lemma tE{n:Nat}(i:ES n)(t:(Fv n×Fv n)×Bo):(if qi i t.1.1 t.1.2=t.2 then (1:Int) else 0)=(if (if Disjoint t.1.1 t.1.2 then !t.2 else t.2) then (1:Int) else 0)+∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*((if t.2&&decide (fy b t) then (1:Int) else 0)-(if !t.2&&decide (fy b t) then (1:Int) else 0)):=by
 classical
 by_cases c:Disjoint t.1.1 t.1.2
 ·
  let v:=i.filter (fun e=>aF e⊆t.1.1\/aF e⊆t.1.2);have s:(i.powerset.erase ∅).filter (fun b=>fy b t)=v.powerset.erase ∅:=(by ext b;simp only[aL,mem_erase,pz,fy,c,fR,v];constructor;{rintro⟨⟨r,z⟩,L⟩;exact⟨r,fun e w=>aL.mpr ⟨z w,L e w⟩⟩};{rintro⟨r,y⟩;exact⟨⟨r,fun e w=>(aL.mp (y w)).1⟩,fun e w=>(aL.mp (y w)).2⟩})
  have x:∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*(if fy b t then (1:Int) else 0)=if v.Nonempty then 1 else 0:=by
   have B:∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*(if fy b t then (1:Int) else 0)=∑ b∈(i.powerset.erase ∅).filter (fun b=>fy b t),(-1:Int)^(b.card-1):=by rw[sO];refine dB rfl fun b _=>by split_ifs <;> ring
   rw[B,s,oI]
  have d:qi i t.1.1 t.1.2=decide v.Nonempty:=(by apply Bool.eq_iff_iff.mpr;simp only[qi,cG,c,sL,false_or,v,Finset.Nonempty,aL]);cases hb:t.2
  ·
   have j:∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*((if false&&decide (fy b t) then (1:Int) else 0)-(if !false&&decide (fy b t) then (1:Int) else 0))=-∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*(if fy b t then (1:Int) else 0):=by
    rw[<- sum_neg_distrib];refine dB rfl fun b _=>by
     simp only[kM,Bool.not_false,nX,eX,↓reduceIte,cG];split_ifs <;> ring
   rw[j,x,d];simp only[c,↓reduceIte,Bool.not_false];by_cases u:v.Nonempty <;> simp[u]
  ·
   have j:∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*((if true&&decide (fy b t) then (1:Int) else 0)-(if !true&&decide (fy b t) then (1:Int) else 0))=∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*(if fy b t then (1:Int) else 0):=by
    refine dB rfl fun b _=>by
     simp only[nX,sQ,kM,eX,↓reduceIte,cG];split_ifs <;> ring
   rw[j,x,d];simp only[c,↓reduceIte,sQ];by_cases u:v.Nonempty <;> simp[u]
 ·
  have o:∀ b,¬fy b t:=fun b h=>c h.1;have d:qi i t.1.1 t.1.2=true:=(by simp[qi,c])
  have q:∑ b∈i.powerset.erase ∅,(-1:Int)^(b.card-1)*((if t.2&&decide (fy b t) then (1:Int) else 0)-(if !t.2&&decide (fy b t) then (1:Int) else 0))=0:=by refine sJ fun b _=>by simp[o b]
  rw[q,g1,d,cM c];cases t.2 <;> simp
lemma h5{b:Type*}(L:Ls b)(p:b->Bo):((L.filter p).length:Int)=(L.map (fun a=>if p a then (1:Int) else 0)).sum:=by induction L with|nil=>{simp}|cons a L c=>{simp only[po,aO,eu];cases p a <;> simp[c] <;> omega}
lemma o1{d c:Type*}(L:Ls d)(e:Ft c)(f:d->c->Int):(L.map (fun a=>∑ b∈e,f a b)).sum=∑ b∈e,(L.map (fun a=>f a b)).sum:=by induction L with|nil=>{simp}|cons a L h=>{simp only[aO,eu,h,sB]}
lemma sn{n:Nat}(M:ES n)(b:Sf n)(a0:∀ d⊆M,2<=d.card->(∀ e∈d,∀ f∈d,e≠f->Disjoint (aF e) (aF f))->(b.filter (fun t=>t.2&&decide (fy d t))).length=(b.filter (fun t=>!t.2&&decide (fy d t))).length)(o:ES n)(Q:aQ o)(a8:o⊆M):(lT b o:Int)=(cO b:Int)+∑ e∈o,((rU b e:Int)-(th b e:Int)):=by
 classical
 rw[lT,h5];have z:b.map (fun t=>if decide (qi o t.1.1 t.1.2=t.2) then (1:Int) else 0)=b.map (fun t=>(if (if Disjoint t.1.1 t.1.2 then !t.2 else t.2) then (1:Int) else 0)+∑ d∈o.powerset.erase ∅,(-1:Int)^(d.card-1)*((if t.2&&decide (fy d t) then (1:Int) else 0)-(if !t.2&&decide (fy d t) then (1:Int) else 0))):=(by refine dF fun t _=>?_;simpa only[cG] using tE o t);rw[z]
 have j:∀ {E:Type} (L:Ls E) (f g:E->Int),(L.map (fun a=>f a+g a)).sum=(L.map f).sum+(L.map g).sum:=by
  intro E L f g;induction L with
  | nil=>simp
  | cons a L v=>simp[v];ring
 have i:=j b (fun (t:(Fv n×Fv n)×Bo)=>if (if Disjoint t.1.1 t.1.2 then !t.2 else t.2) then (1:Int) else 0) (fun (t:(Fv n×Fv n)×Bo)=>∑ d∈o.powerset.erase ∅,(-1:Int)^(d.card-1)*((if t.2&&decide (fy d t) then (1:Int) else 0)-(if !t.2&&decide (fy d t) then (1:Int) else 0)));rw[i,o1];have u:(b.map (fun t=>if (if Disjoint t.1.1 t.1.2 then !t.2 else t.2)=true then (1:Int) else 0)).sum=(cO b:Int):=(by unfold cO;rw[h5]);rw[u];congr 1
 have r:∀ d∈o.powerset.erase ∅,(b.map (fun t=>(-1:Int)^(d.card-1)*((if t.2&&decide (fy d t) then (1:Int) else 0)-(if !t.2&&decide (fy d t) then (1:Int) else 0)))).sum=(-1:Int)^(d.card-1)*(((b.filter (fun t=>t.2&&decide (fy d t))).length:Int)-((b.filter (fun t=>!t.2&&decide (fy d t))).length:Int)):=by
  intro d _
  have y:∀(c:Int) (L:Sf n) (f:_->Int),(L.map (fun a=>c*f a)).sum=c*(L.map f).sum:=by
   intro c L f;induction L with
   | nil=>simp
   | cons a L v=>simp[v,mul_add]
  have w:∀(L:Sf n) (f g:_->Int),(L.map (fun a=>f a-g a)).sum=(L.map f).sum-(L.map g).sum:=by
   intro L f g;induction L with
   | nil=>simp
   | cons a L v=>simp[v];ring
  rw[y,w,<- h5,<- h5]
 rw[dB rfl r];have s:∑ d∈o.powerset.erase ∅,(-1:Int)^(d.card-1)*(((b.filter (fun t=>t.2&&decide (fy d t))).length:Int)-((b.filter (fun t=>!t.2&&decide (fy d t))).length:Int))=∑ d∈(o.powerset.erase ∅).filter (fun d=>d.card=1),(-1:Int)^(d.card-1)*(((b.filter (fun t=>t.2&&decide (fy d t))).length:Int)-((b.filter (fun t=>!t.2&&decide (fy d t))).length:Int)):=(by symm;refine sum_filter_of_ne fun d B a3=>?_;obtain⟨a7,a6⟩:=fL.mp B;have q:d⊆o:=mem_powerset.mp a6;have a9:1<=d.card:=card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr a7);by_contra aa;have S:2<=d.card:=(by omega);have a4:=a0 d (q.trans a8) S (fun e K f P x=>Q.2 e (q K) f (q P) x);exact a3 (by rw[a4];ring));rw[s];symm;refine nV (fun e _=>({e}:ES n)) ?_ ?_ ?_ ?_;{intro e K;simp[K]};{intro e1 _ e2 _ h;exact singleton_injective h};{intro d B;simp only[aL,mem_erase,pz] at B;obtain⟨e,rfl⟩:=card_eq_one.mp B.2;exact⟨e,singleton_subset_iff.mp B.1.2,rfl⟩};{intro e _;simp[rU,th]}
lemma vt{n:Nat}(u:ES n)(b:Sf n)(o:∀ S⊆u,2<=S.card->(∀ e∈S,∀ f∈S,e≠f->Disjoint (aF e) (aF f))->(b.filter (fun t=>t.2&&decide (fy S t))).length=(b.filter (fun t=>!t.2&&decide (fy S t))).length)(c:ES n)(v:aQ c)(s:c⊆u):cO b+∑ e∈c,cZ b e=c.card*(2*b.length+1)+lT b c:=by
 have q:=sn u b o c v s
 have i:((cO b+∑ e∈c,cZ b e:Nat):Int)=((c.card*(2*b.length+1)+lT b c:Nat):Int):=by
  push_cast;have j:∑ e∈c,(cZ b e:Int)=∑ e∈c,((2*b.length+1:Int)+(rU b e:Int)-(th b e:Int)):=(by refine dB rfl fun e _=>?_;have r:th b e<=(2*b.length+1)+rU b e:=(uy b e).trans (by omega);unfold cZ;rw[Nat.cast_sub r];push_cast;ring);rw[j,q];have h:∑ _e∈c,((2*(b.length:Int)+1))=(c.card:Int)*(2*(b.length:Int)+1):=(by rw[qP,nsmul_eq_mul])
  have d:∑ e∈c,((2*(b.length:Int)+1)+(rU b e:Int)-(th b e:Int))=(∑ _e∈c,(2*(b.length:Int)+1))+∑ e∈c,((rU b e:Int)-(th b e:Int)):=by rw[<- sB];refine dB rfl fun e _=>by ring
  rw[d,h];ring
 exact Nat.cast_injective i
def fw{n:Nat}(c:ES n)(b:Sf n)(u v:Fin n):PZ:=if (u,v)∈c then X^cZ b (u,v)
 else if (v,u)∈c then X^cZ b (v,u)
 else 0
lemma kS{n:Nat}{h:ES n}(d:∀ e∈h,e.1<e.2)(b:Sf n)(e:EP n)(i:e.1<e.2):fw h b e.1 e.2=if e∈h then X^cZ b e else 0:=by unfold fw;have c:(e.2,e.1)∉h:=fun j=>pC i (d _ j);simp[c]
lemma fx{b:Type*}(s:Ft b)(f:b->PZ)(d:Nat):(∑ a∈s,f a).coeff d=∑ a∈s,(f a).coeff d:=by
 classical
 induction s using qK with|empty=>{simp}|@insert a s ha ih=>{rw[kK ha,kK ha,sD,ih]}
lemma t9{n:Nat}{o h:Pm (Fin n)}(z:Involutive o)(w:Involutive h)(P:∀ x y,invFun o x y=invFun h x y):o=h:=by
 have hm:cV o=cV h:=by
  ext e;by_cases q:e.1<e.2
  ·
   have K:invFun o (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n)))=invFun h (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))):=P _ _
   have c:∀(p:Pm (Fin n)),Involutive p->(invFun p (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n)))=true↔e∈cV p):=fun p E=>by
    rw[iO p E];simp only[uK,sL,false_or,Finset.subset_empty];constructor
    ·
     rintro⟨f,r,v|S⟩
     ·
      have a8:(aF f).card=2:=lC (bS ((cA p f).mp r).1);have a7:(aF e).card=2:=lC (bS q);have d:aF f=aF e:=nH v (by omega);have B:f.1∈aF e:=d▸(by simp[aF]);have L:f.2∈aF e:=d▸(by simp[aF]);have b:=((cA p f).mp r).1;simp only[aF,aV,bI] at B L
      have Q:f=e:=by
       rcases B with u|u <;> rcases L with s|s
       {exact absurd (u.trans s.symm) (bS b)};{exact eC u s};{exact absurd (u▸s▸b) (e7 q)};{exact absurd (u.trans s.symm) (bS b)}
      exact Q▸r
     {exact absurd (by simp[aF]:f.1∈aF f) (S▸sG f.1)}
    {intro M;exact⟨e,M,Or.inl subset_rfl⟩}
   rw[<- c o z,<- c h w,K]
  {simp[cA,q]}
 have u:=lg o z;have s:=lg h w;rw[<- u,<- s];congr 1
lemma kF{n:Nat}(p:Pm (Fin n))(b:Involutive p)(R T:Fv n):invFun p (fun i=>decide (i∈R)) (fun j=>decide (j∈T))=qi (cV p) R T:=by apply Bool.eq_iff_iff.mpr;rw[iO p b];simp[qi]
lemma n8{n:Nat}(c:Ls (Fv n×Fv n))(d:Sf n)(o:∃ z∈c,¬Disjoint z.1 z.2)(s j:Nat):Nat.card {f:(Fin n->Bo)->(Fin n->Bo)->Bo //
 ((∃! p:Pm (Fin n),Involutive p/\∀ x y,f x y=invFun p x y)/\∀ z∈c,f (fun i=>decide (i∈z.1)) (fun j=>decide (j∈z.2))=false)/\
 (((gX n).map (fun e=>f (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id).length=s/\
 (d.filter (fun t=>decide (f (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2))).length=j}=0:=by
 classical
 have r:IsEmpty {f:(Fin n->Bo)->(Fin n->Bo)->Bo //
  ((∃! p:Pm (Fin n),Involutive p/\∀ x y,f x y=invFun p x y)/\∀ z∈c,f (fun i=>decide (i∈z.1)) (fun j=>decide (j∈z.2))=false)/\
  (((gX n).map (fun e=>f (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id).length=s/\
  (d.filter (fun t=>decide (f (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2))).length=j}:=by
  refine⟨fun ⟨f,⟨⟨p,⟨hp,hf⟩,_⟩,hhard⟩,_,_⟩=>?_⟩;obtain⟨z,u,q⟩:=o;have b:=hhard z u;rw[hf] at b;have h:invFun p (fun i=>decide (i∈z.1)) (fun j=>decide (j∈z.2))=true:=(iO p hp z.1 z.2).mpr (Or.inl q);rw[h] at b;exact Bool.noConfusion b
 rw[Nat.card_eq_fintype_card];exact Fintype.card_eq_zero
lemma q5{n:Nat}(w:Ls (Fv n×Fv n))(b:Sf n)(ae:∀ z∈w,Disjoint z.1 z.2)(am:∀ S⊆((gX n).toFinset.filter (fun e=>∀ z∈w,¬(aF e⊆z.1)/\¬(aF e⊆z.2))),2<=S.card->(∀ e∈S,∀ f∈S,e≠f->Disjoint (aF e) (aF f))->(b.filter (fun t=>t.2&&decide (fy S t))).length=(b.filter (fun t=>!t.2&&decide (fy S t))).length)(s j:Nat)(hj:j<=b.length):let E:=(gX n).toFinset.filter (fun e=>∀ z∈w,¬(aF e⊆z.1)/\¬(aF e⊆z.2))
 (Nat.card {f:(Fin n->Bo)->(Fin n->Bo)->Bo //
   ((∃! p:Pm (Fin n),Involutive p/\∀ x y,f x y=invFun p x y)/\∀ z∈w,f (fun i=>decide (i∈z.1)) (fun j=>decide (j∈z.2))=false)/\
   (((gX n).map (fun e=>f (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id).length=s/\
   (b.filter (fun t=>decide (f (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2))).length=j}:Int)=
 (X^cO b * ∑ c∈cE n,∏ e∈c,fw E b e.1 e.2).coeff (s*(2*b.length+1)+j):=by
 classical
 intro E
 let d:Ft (ES n):=
  (cE n).filter (fun c=>c⊆E/\c.card=s/\lT b c=j)
 have a7:∀ e∈E,e.1<e.2:=fun e Q=>by
  have:=(aL.mp Q).1
  exact (gR e).mp (dO.mp this)
 let ah:={f:(Fin n->Bo)->(Fin n->Bo)->Bo //
     ((∃! p:Pm (Fin n),Involutive p/\∀ x y,f x y=invFun p x y)/\∀ z∈w,f (fun i=>decide (i∈z.1)) (fun j=>decide (j∈z.2))=false)/\
     (((gX n).map (fun e=>f (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id).length=s/\
     (b.filter (fun t=>decide (f (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2))).length=j}
 let a3:ah->{c // c∈d}:=fun ⟨f,⟨hex,hhard⟩,hsize,hscore⟩=>
  let p:=Classical.choose hex;let B:Involutive p/\∀ x y,f x y=invFun p x y:=(f9 hex).1
  ⟨cV p,by
    simp only[d,aL,cP];refine⟨io p B.1,?_,?_,?_⟩;{intro e v;simp only[E,aL,dO,gR];refine⟨((cA p e).mp v).1,fun z M=>?_⟩;have u:=hhard z M;rw[B.2] at u;have a6:¬(¬Disjoint z.1 z.2\/∃ e'∈cV p,aF e'⊆z.1\/aF e'⊆z.2):=(by intro h;have:=(iO p B.1 z.1 z.2).mpr h;rw[this] at u;exact Bool.noConfusion u);exact⟨fun P=>a6 (Or.inr ⟨e,v,Or.inl P⟩),fun h2=>a6 (Or.inr ⟨e,v,Or.inr h2⟩)⟩};{have aq:=qh p B.1;have ak:(gX n).map (fun e=>f (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))=(gX n).map (fun e=>invFun p (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n)))):=dF fun e _=>B.2 _ _;rw[<- aq,<- ak,hsize]}
    ·
     unfold lT;have af:b.filter (fun t=>decide (qi (cV p) t.1.1 t.1.2=t.2))=b.filter (fun t=>decide (f (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2)):=(by refine List.filter_congr fun t _=>?_;rw[B.2,kF p B.1]);rw[af,hscore]⟩
 let a4:{c // c∈d}->ah:=fun ⟨c,K⟩=>
  let r:aQ c:=cP.mp (aL.mp K).1;let L:c⊆E:=(aL.mp K).2.1;let az:c.card=s:=(aL.mp K).2.2.1;let ay:lT b c=j:=(aL.mp K).2.2.2;let p:=tl c r;let B:Involutive p:=oD c r;let ad:cV p=c:=os c r
  ⟨invFun p,⟨⟨p,⟨B,fun _ _=>rfl⟩,fun q ⟨hq,hqf⟩=>t9 hq B (fun x y=>(hqf x y).symm)⟩,fun z M=>by
    rw[kF p B,ad];apply Bool.eq_false_iff.mpr;intro ht;simp only[qi,cG] at ht;rcases ht with au|⟨e,v,a2|a2⟩
    {exact au (ae z M)};{exact ((aL.mp (L v)).2 z M).1 a2}
    · exact ((aL.mp (L v)).2 z M).2 a2⟩,
    by rw[qh p B,ad,az],
    by
     have af:b.filter (fun t=>decide (invFun p (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2))=b.filter (fun t=>decide (qi c t.1.1 t.1.2=t.2)):=(by refine List.filter_congr fun t _=>?_;rw[kF p B,ad]);rw[af];exact ay⟩
 have al:Bijective a3:=by
  refine Function.bijective_iff_has_inverse.mpr ⟨a4,?_,?_⟩;{intro⟨f,hf⟩;apply Subtype.ext;funext x y;dsimp only[a4,a3];have o:=(f9 hf.1.1).1;rw[lg _ o.1];exact (o.2 x y).symm}
  ·
   intro⟨c,K⟩;apply Subtype.ext;dsimp only[a3,a4]
   set hex:=(a4 ⟨c,K⟩).2.1.1;have o:=(f9 hex).1;have r:aQ c:=cP.mp (aL.mp K).1;have ab:Classical.choose hex=tl c r:=t9 o.1 (oD c r) (fun x y=>(o.2 x y).symm);rw[ab,os c r]
 have ag:Nat.card ah=d.card:=(by rw[Nat.card_congr (Equiv.ofBijective a3 al),Nat.card_eq_fintype_card,Fintype.card_coe]);rw[show (Nat.card _:Int)=(d.card:Int) from aI Nat.cast ag];rw[mM,fx]
 have a9:∀ c∈cE n,(X^cO b * ∏ e∈c,fw E b e.1 e.2).coeff (s*(2*b.length+1)+j)=if c⊆E/\c.card=s/\lT b c=j then (1:Int) else 0:=by
  intro c K;have r:aQ c:=cP.mp K;by_cases L:c⊆E
  ·
   have aa:∏ e∈c,fw E b e.1 e.2=X^(∑ e∈c,cZ b e):=(by have P:∏ e∈c,fw E b e.1 e.2=∏ e∈c,(X:PZ)^cZ b e:=(by refine qN rfl fun e Q=>?_;rw[kS a7 b e (r.1 e Q),dP (L Q)]);rw[P,uM]);rw[aa,<- j8,vt E b am c r L,coeff_X_pow];have ao:lT b c<=b.length:=qE _ _
   have aj:s*(2*b.length+1)+j=c.card*(2*b.length+1)+lT b c↔c.card=s/\lT b c=j:=by
    constructor
    ·
     intro ak
     have P:c.card=s:=by
      by_contra ar;rcases iR ar with av|aw
      {have:(c.card+1)*(2*b.length+1)<=s*(2*b.length+1):=nK _ av;nlinarith};{have:(s+1)*(2*b.length+1)<=c.card*(2*b.length+1):=nK _ aw;nlinarith}
     subst P;exact⟨rfl,by omega⟩
    {rintro⟨rfl,rfl⟩;rfl}
   simp only[L,fR,aj]
  {obtain⟨e,v,ax⟩:=not_subset.mp L;have a8:fw E b e.1 e.2=0:=(by rw[kS a7 b e (r.1 e v),cM ax]);rw[qI v a8,mul_zero,jY,cM (fun h=>L h.1)]}
 rw[dB rfl a9];simp[d,sum_boole]
def aA{N:Nat}(v:Fin (2*N)):Fin (2*N):=⟨if v.val % 2=0 then v.val+1 else v.val-1,by split_ifs <;> omega⟩
def j0{N:Nat}{R:Type*}[CommRing R](v:Fin (2*N)):R:=if v.val % 2=0 then 1 else -1
def V{N:Nat}(h:Fin N):Fin (2*N):=⟨2*h.val,by omega⟩
def aZ{N:Nat}(h:Fin N):Fin (2*N):=⟨2*h.val+1,by omega⟩
def H{N:Nat}(v:Fin (2*N)):Nat:=v.val / 2
lemma bH{N:Nat}(v:Fin (2*N)):aA (aA v)=v:=by apply bL;simp only[aA];split_ifs <;> omega
lemma lj{N:Nat}(v:Fin (2*N)):aA v≠v:=by intro h;have b:=aI Fin.val h;simp only[aA] at b;split_ifs at b <;> omega
lemma eJ{N:Nat}(v:Fin (2*N)):H (aA v)=H v:=by simp only[H,aA];split_ifs <;> omega
lemma cI{N:Nat}{u v:Fin (2*N)}(h:H u=H v):u=v\/u=aA v:=by simp only[H] at h;by_cases b:u.val=v.val;{left;exact bL b};{right;apply bL;simp only[aA];split_ifs <;> omega}
lemma ua{N:Nat}{R:Type*}[CommRing R](v:Fin (2*N)):j0 (R:=R) (aA v)=-j0 v:=by simp only[j0,aA];split_ifs <;> first|omega|ring
lemma om{N:Nat}(h:Fin N):aA (V h)=aZ h:=by apply bL;simp[aA,V,aZ]
lemma wg{N:Nat}{R:Type*}[CommRing R](h:Fin N):j0 (R:=R) (V h)=1:=by simp[j0,V]
lemma bK{N:Nat}(h:Fin N):H (V h)=h.val:=by simp[H,V]
def fU{N:Nat}{R:Type*}[CommRing R](e:Fin (2*N)->Fin (2*N)->R)(d:Fin N->Fin (2*N)->R):Fin N->Fin (2*N)->R:=fun h w=>
 let c:R:=
  if 2*h.val+1<=w.val then
   let v:=aA w
   if 2*h.val+2<=v.val then ∑ u:Fin (2*N),if 2*h.val+1<=u.val then d h u*e u v*j0 v else 0
   else 0
  else 0
 let b:R:=
  if w.val=2*h.val+1 then ∑ hp:Fin N,if hp.val<h.val then ∑ u:Fin (2*N),if 2*hp.val+1<=u.val then d hp u*(- e u (V hp)) else 0
   else 0
  else 0
 c+b
def fT{N:Nat}{R:Type*}[CommRing R]:Fin N->Fin (2*N)->R:=fun h w=>if w.val=2*h.val+1 then 1 else 0
def uD{N:Nat}{R:Type*}[CommRing R](c:Fin (2*N)->Fin (2*N)->R):R:=
 let b:=(fU c)^[N-1] fT
 ∑ h:Fin N,∑ u:Fin (2*N),if 2*h.val+1<=u.val then b h u*(- c u (V h)) else 0
def el{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(u:Fin (2*N)):L2 N->Fin (2*N)->R
 | [],target=>b u target
 | v::c,target=>b u v*j0 v*el b (aA v) c target
def bQ{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(c:Cw N):R:=-el b (aZ c.1) c.2 (V c.1)
def bJ{N:Nat}{R:Type*}[CommRing R](c:Fin (2*N)->Fin (2*N)->R)(b:Ls (Cw N)):R:=(b.map (bQ c)).prod
def ff{N:Nat}{R:Type*}[CommRing R](c:Fin (2*N)->Fin (2*N)->R):L2 N->R
 | []=>1
 | v0::b=>-j0 v0*el c (aA v0) b v0
lemma kV{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(c:Cw N):bQ b c=ff b (V c.1::c.2):=by simp[bQ,ff,wg,om]
lemma iH{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(u:Fin (2*N))(xs:L2 N)(v:Fin (2*N))(ys:L2 N)(target:Fin (2*N)):el b u (xs++v::ys) target=el b u xs v*j0 v*el b (aA v) ys target:=by induction xs generalizing u with|nil=>{simp[el]}|cons a xs c=>{simp only[fB,el,c];ring}
lemma nr{N:Nat}{R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(c:∀ a b,d b a=-d a b)(mid:L2 N):∀ u target:Fin (2*N),el d u (mid.reverse.map aA) target=-el d target mid u:=by induction mid with|nil=>{intro u target;simp[el,c target u]}|cons a e h=>{intro u target;simp only[pc,bR,aO,fC];rw[iH,h u (aA a)];simp only[el,bH,ua,c target a];ring}
lemma p4{N:Nat}{R:Type*}[CommRing R](c:Fin (2*N)->Fin (2*N)->R){xs ys:L2 N}(i:xs≠[])(h:ys≠[]):ff c (xs++ys)=ff c (ys++xs):=by
 cases xs with
 | nil=>exact (i rfl).elim
 | cons a e=>cases ys with|nil=>{exact (h rfl).elim}|cons b d=>{simp only[fB,ff,iH];ring}
def gF{N:Nat}:L2 N->L2 N
 | []=>[]
 | v0::b=>aA v0::b.reverse.map aA
lemma sg{N:Nat}(L:L2 N):gF (gF L)=L:=by cases L with|nil=>{rfl}|cons d c=>{simp only[gF,bH,j3,gm,g0];congr 1;have b:(aA (N:=N)) ∘ aA=id:=funext bH;rw[b,mN]}
lemma td{N:Nat}{R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(c:∀ a b,d b a=-d a b)(L:L2 N):ff d (gF L)=ff d L:=by cases L with|nil=>{rfl}|cons h e=>{simp only[gF,ff,bH,ua,nr d c];ring}
def eE{N:Nat}(h:Fin N):L2 N->Fin (2*N)
 | []=>aZ h
 | [v]=>aA v
 | _::v::vs=>eE h (v::vs)
lemma lJ{N:Nat}(h:Fin N)(c:L2 N)(v:Fin (2*N)):eE h (c++[v])=aA v:=by
 induction c with
 | nil=>rfl
 | cons a c e=>cases c with|nil=>{rfl}|cons b d=>{exact e}
def dV{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(u:Fin (2*N)):L2 N->R
 | []=>1
 | v::c=>b u v*j0 v*dV b (aA v) c
lemma lU{N:Nat}{R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(h:Fin N)(c:L2 N)(v:Fin (2*N)):dV d (aZ h) (c++[v])=dV d (aZ h) c*d (eE h c) v*j0 v:=by
 suffices ∀(u:Fin (2*N)),dV d u (c++[v])=dV d u c*d (if c=[] then u else eE h c) v*j0 v by
  have j:=this (aZ h);cases c with
  | nil=>simpa[eE] using j
  | cons a e=>simpa using j
 clear * -
 induction c with
 | nil=>intro u;simp[dV]
 | cons a c o=>
   intro u;cases c with
   | nil=>simp[dV,eE];ring
   | cons b e=>have i:=o (aA a);simp only[fB,dV,ib,↓reduceIte,eE] at i ⊢;rw[i];ring
lemma iK{N:Nat}{R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(h:Fin N)(c:L2 N)(target:Fin (2*N)):el d (aZ h) c target=dV d (aZ h) c*d (eE h c) target:=by
 suffices ∀(u:Fin (2*N)),el d u c target=dV d u c*d (if c=[] then u else eE h c) target by
  have j:=this (aZ h);cases c with
  | nil=>simpa[eE] using j
  | cons a e=>simpa using j
 clear * -
 induction c with
 | nil=>intro u;simp[el,dV]
 | cons a c o=>
   intro u;cases c with
   | nil=>simp[el,dV,eE,mR]
   | cons b e=>have i:=o (aA a);simp only[el,dV,ib,↓reduceIte,eE] at i ⊢;rw[i];ring
abbrev fG(N:Nat):=Ls (Cw N)×Cw N
def cK{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(p:fG N):R:=bJ b p.1*dV b (aZ p.2.1) p.2.2
def aW(N:Nat):Nat->Ls (fG N)
 | 0=>(finRange N).map (fun h=>([],h,[]))
 | t+1=>
   (aW N t).flatMap fun p=>
     (((finRange (2*N)).filter (fun v=>decide (2*p.2.1.val+2<=v.val))).map (fun v=>(p.1,p.2.1,p.2.2++[v])))++
     (((finRange N).filter (fun h=>decide (p.2.1.val<h.val))).map (fun h=>(p.1++[(p.2.1,p.2.2)],h,[])))
def ko{N:Nat}(c:Cw N):Prop:=∀ v∈c.2,2*c.1.val+2<=v.val
def er{N:Nat}(L:Nat)(b:Ls (Cw N)):Prop:=(∀ c∈b,ko c)/\(b.map Prod.fst).Pairwise (·<·)/\(b.map (fun c=>c.2.length+1)).sum=L
def qA{N:Nat}(t:Nat)(p:fG N):Prop:=(∀ c∈p.1,ko c)/\ko (p.2.1,p.2.2)/\((p.1++[(p.2.1,p.2.2)]).map Prod.fst).Pairwise (·<·)/\(p.1.map (fun c=>c.2.length+1)).sum+p.2.2.length=t
lemma oZ{N:Nat}{h:Fin N}{i:L2 N}(o:ko (h,i)):2*h.val+1<=(eE h i).val:=by
 cases i with
 | nil=>simp[eE,aZ]
 | cons a c=>
   have d:∃ v∈a::c,eE h (a::c)=aA v:=by
    clear o;induction c generalizing a with
    | nil=>exact⟨a,by simp,rfl⟩
    | cons b s q=>obtain⟨v,j,e⟩:=q b;exact⟨v,g9 a j,e⟩
   obtain⟨v,j,e⟩:=d;rw[e];have r:2*h.val+2<=v.val:=o v j;simp only[aA];split_ifs <;> omega
lemma jU{N:Nat}(t:Nat)(p:fG N):p∈aW N t↔qA t p:=by
 induction t generalizing p with
 | zero=>
   rcases p with ⟨B,h,K⟩
   simp only[aW,cC,mK,fR,qA];constructor;{rintro⟨h',e⟩;simp only[gL] at e;obtain⟨rfl,rfl,rfl⟩:=e;exact⟨fun _ h=>by simp at h,fun _ h=>by simp at h,by simp,by simp⟩}
   ·
    rintro⟨_,_,_,d⟩;have a4:K=[]:=List.eq_nil_of_length_eq_zero (by omega)
    have r:B=[]:=by cases B with|nil=>{rfl}|cons c cs=>{simp at d}
    subst a4;subst r;exact⟨h,rfl⟩
 | succ t Q=>
   rcases p with ⟨B,h,K⟩
   simp only[aW,gM,eL,cC,gd,mK,fR,cG,Q];constructor
   ·
    rintro⟨⟨P,L,j⟩,⟨x,z,i,o⟩,(⟨v,S,e⟩|⟨h1,y,e⟩)⟩
    ·
     simp only[gL] at e;obtain⟨rfl,rfl,rfl⟩:=e;refine⟨x,?_,by simpa[bR] using i,by simp only[dL,aX,mL] at o ⊢;omega⟩;intro u w;rcases eL.mp w with w|w
     {exact z u w};{simp only[eZ] at w;exact w▸S}
    ·
     simp only[gL] at e;obtain⟨rfl,rfl,rfl⟩:=e;refine⟨?_,fun _ h=>by simp at h,?_,by simp only[bR,ic,aO,fC,eu,mO,mL,g1] at o ⊢;omega⟩
     ·
      intro c s;rcases eL.mp s with s|s
      {exact x c s};{simp only[eZ] at s;exact s▸z}
     ·
      rw[bR,kL] at i;rw[bR,bR,kL];refine⟨by rw[kL];exact i,by simp,?_⟩;intro a E b M;simp only[aO,fC,eZ] at M;subst M;simp only[eL,aO,fC,eZ] at E;rcases E with E|rfl
      {exact hK (i.2.2 a E L (by simp)) y};{exact y}
   ·
    rintro⟨r,s,q,d⟩;cases K using List.reverseRecOn with
    | nil=>
      cases B using List.reverseRecOn with
      | nil=>simp at d
      | append_singleton P c0=>
        rcases c0 with ⟨L,j⟩
        refine⟨(P,L,j),⟨?_,?_,?_,?_⟩,Or.inr ⟨h,?_,rfl⟩⟩;{exact fun c a5=>r c (nM _ a5)};{exact r (L,j) (by simp)};{rw[bR,kL] at q;exact q.1};{simp only[bR,ic,aO,fC,eu,mO,mL,g1] at d ⊢;omega};{rw[bR,kL] at q;exact q.2.2 L (by simp) h (by simp)}
    | append_singleton j v=>refine⟨(B,h,j),⟨r,?_,by simpa[bR] using q,?_⟩,Or.inl ⟨v,s v (by simp),rfl⟩⟩;{exact fun u w=>s u (nM _ w)};{simp only[dL,aX,mL] at d ⊢;omega}
lemma rH{N:Nat}(t:Nat):(aW N t).Nodup:=by
 induction t with
 | zero=>exact (jZ N).map (fun a b h=>by simpa using h)
 | succ t z=>
   unfold aW;rw[lA];refine⟨?_,?_⟩
   ·
    intro p _;rw[fu];refine⟨?_,?_,?_⟩
    ·
     exact ((jZ (2*N)).filter _).map (fun a b h=>by
      have:=(mQ (mQ h).2).2
      simpa using uW this rfl)
    {exact ((jZ N).filter _).map (fun a b h=>(mQ (mQ h).2).1)}
    ·
     intro x e y d j;simp only[cC] at e d;rcases e with ⟨v,_,rfl⟩
     rcases d with ⟨h,_,rfl⟩
     have i:=aI (fun (q:fG N)=>q.2.2.length) j;simp at i
   ·
    refine z.pairwise_of_forall_ne fun w _ p2 _ hne x e d=>?_;simp only[eL,cC] at e d;rcases e with ⟨K,_,rfl⟩|⟨P,_,rfl⟩ <;> rcases d with ⟨E,_,c⟩|⟨M,_,c⟩
    {simp only[gL] at c;obtain⟨u,s,r⟩:=c;have L:p2.2.2=w.2.2:=qF r rfl;exact hne (eC u.symm (eC s.symm L.symm))};{simp only[gL] at c;simp at c};{simp only[gL] at c;simp at c};{simp only[gL] at c;have B:=qF c.1 rfl;have o:=uW c.1 rfl;simp only[hJ,gL,and_true] at o;exact hne (eC B.symm (eC o.1.symm o.2.symm))}
lemma hO{b R:Type*}[CommRing R](L:Ls b)(f:b->R){n:Nat}(g:b->Fin n):(L.map f).sum=∑ i:Fin n,((L.filter (fun a=>decide (g a=i))).map f).sum:=by
 induction L with
 | nil=>simp
 | cons a L d=>
   simp only[aO,eu,po,d];conv_rhs=>rw[<- u5 _ _ (dN (g a))]
   have j:((if decide (g a=g a)=true then a::L.filter (fun x=>decide (g x=g a)) else L.filter (fun x=>decide (g x=g a))).map f).sum=f a+((L.filter (fun x=>decide (g x=g a))).map f).sum:=(by simp);rw[j];have h:∑ i∈univ.erase (g a),((if decide (g a=i) then a::L.filter (fun x=>decide (g x=i)) else L.filter (fun x=>decide (g x=i))).map f).sum=∑ i∈univ.erase (g a),((L.filter (fun x=>decide (g x=i))).map f).sum:=(by refine dB rfl fun i e=>?_;have c:g a≠i:=(fL.mp e).1.symm;simp[c]);rw[h];conv_lhs=>rw[<- u5 _ _ (dN (g a))]
   ring
lemma jh{b R:Type*}[CommRing R](L:Ls b)(f:b->R)(c:R):(L.map (fun a=>f a*c)).sum=(L.map f).sum*c:=by induction L with|nil=>{simp}|cons a L d=>{simp[d,add_mul]}
lemma uk{N:Nat}{R:Type*}[CommRing R](e:Fin (2*N)->Fin (2*N)->R)(t:Nat):∀(h:Fin N) (w:Fin (2*N)),((fU e)^[t] fT) h w=(((aW N t).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=w))).map (cK e)).sum:=by
 induction t with
 | zero=>
   intro h w;simp only[Function.iterate_zero,id_eq,fT,aW,sX,gm]
   have r:((finRange N).filter (fun c=>decide (c=h/\aZ c=w)))=if w.val=2*h.val+1 then [h] else []:=by
    have ai:(finRange N).filter (fun c=>decide (c=h))=[h]:=by
     have M:=(jZ N).filter (fun c=>decide (c=h));have d:∀ x,x∈(finRange N).filter (fun c=>decide (c=h))↔x=h:=(by intro x;simp);cases hL:(finRange N).filter (fun c=>decide (c=h)) with
     | nil=>exact absurd ((d h).mpr rfl) (by simp[hL])
     | cons x xs=>
       have hx:x=h:=(d x).mp (by simp[hL]);subst hx;cases xs with
       | nil=>rfl
       | cons y ys=>have hy:y=x:=(d y).mp (by simp[hL]);rw[hL,hy] at M;simp at M
    split_ifs with E
    {have z:aZ h=w:=bL E.symm;have:(fun c:Fin N=>decide (c=h/\aZ c=w))=(fun c=>decide (c=h)):=(by funext c;apply Bool.eq_iff_iff.mpr;simp only[cG];exact⟨fun B=>B.1,fun B=>⟨B,B▸z⟩⟩);rw[this,ai]};{rw[nJ];intro c _;simp only[cG,not_and];rintro rfl z;exact E (aI Fin.val z).symm}
   have ah:((finRange N).filter (fun c=>decide (c=h/\eE c []=w))).map (fun c=>cK e ([],c,[]))=((finRange N).filter (fun c=>decide (c=h/\aZ c=w))).map (fun _=>(1:R)):=(by refine dF fun c _=>?_;simp[cK,bJ,dV]);change _=(((finRange N).filter (fun c=>decide (c=h/\eE c []=w))).map (fun c=>cK e ([],c,[]))).sum;rw[ah,r];split_ifs <;> simp
 | succ t ih=>
   intro h w;rw[jb]
   have aj:(((aW N (t+1)).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=w))).map (cK e)).sum=(((aW N t).flatMap (fun p=>(((finRange (2*N)).filter (fun v=>decide (2*p.2.1.val+2<=v.val))).map (fun v=>(p.1,p.2.1,p.2.2++[v]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w)))).map (cK e)).sum+(((aW N t).flatMap (fun p=>(((finRange N).filter (fun c=>decide (p.2.1.val<c.val))).map (fun c=>(p.1++[(p.2.1,p.2.2)],c,[]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w)))).map (cK e)).sum:=by
    conv_lhs=>unfold aW
    rw[List.filter_flatMap]
    have a4:∀(L:Ls (fG N)) (f g:fG N->Ls (fG N)) (val:fG N->R),((L.flatMap (fun a=>f a++g a)).map val).sum=((L.flatMap f).map val).sum+((L.flatMap g).map val).sum:=by
     intro L f g val;induction L with
     | nil=>simp
     | cons a L S=>simp only[eY,bR,ic,S];ring
    have hf:∀ p:fG N,((((finRange (2*N)).filter (fun v:Fin (2*N)=>decide (2*p.2.1.val+2<=v.val))).map (fun v=>(p.1,p.2.1,p.2.2++[v])))++(((finRange N).filter (fun c:Fin N=>decide (p.2.1.val<c.val))).map (fun c=>(p.1++[(p.2.1,p.2.2)],c,[])))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w))=((((finRange (2*N)).filter (fun v:Fin (2*N)=>decide (2*p.2.1.val+2<=v.val))).map (fun v=>(p.1,p.2.1,p.2.2++[v]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w)))++((((finRange N).filter (fun c:Fin N=>decide (p.2.1.val<c.val))).map (fun c=>(p.1++[(p.2.1,p.2.2)],c,[]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w))):=fun p=>List.filter_append ..;rw[dG (fun p _=>hf p)];exact a4 (aW N t) _ _ (cK e)
   rw[aj];have a2:∀(dp:Fin N->Fin (2*N)->R),fU e dp h w=(if 2*h.val+1<=w.val then if 2*h.val+2<=(aA w).val then ∑ u:Fin (2*N),if 2*h.val+1<=u.val then dp h u*e u (aA w)*j0 (aA w) else 0 else 0 else 0)+(if w.val=2*h.val+1 then ∑ i:Fin N,if i.val<h.val then ∑ u:Fin (2*N),if 2*i.val+1<=u.val then dp i u*(- e u (V i)) else 0 else 0 else 0):=fun _=>rfl;rw[a2];refine congrArg₂ (·+·) ?_ ?_
   ·
    have ag:(((aW N t).flatMap (fun p=>(((finRange (2*N)).filter (fun v=>decide (2*p.2.1.val+2<=v.val))).map (fun v=>(p.1,p.2.1,p.2.2++[v]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w)))).map (cK e)).sum=if 2*h.val+2<=(aA w).val then (((aW N t).filter (fun p=>decide (p.2.1=h))).map (fun p=>cK e p*e (eE p.2.1 p.2.2) (aA w)*j0 (aA w))).sum
     else 0:=by
     have a3:∀ p:fG N,(((((finRange (2*N)).filter (fun v=>decide (2*p.2.1.val+2<=v.val))).map (fun v=>(p.1,p.2.1,p.2.2++[v]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w))).map (cK e)).sum=if p.2.1=h/\2*h.val+2<=(aA w).val then cK e p*e (eE p.2.1 p.2.2) (aA w)*j0 (aA w)
      else 0:=by
      intro p;rw[sX,gm]
      have r:((finRange (2*N)).filter (fun v=>decide (2*p.2.1.val+2<=v.val))).filter (fun v=>decide (p.2.1=h/\eE p.2.1 (p.2.2++[v])=w))=if p.2.1=h/\2*h.val+2<=(aA w).val then [aA w] else []:=by
       rw[pk];split_ifs with Q
       ·
        obtain⟨rfl,o⟩:=Q
        set Lfilt:=(finRange (2*N)).filter (fun v=>decide (p.2.1=p.2.1/\eE p.2.1 (p.2.2++[v])=w)&&decide (2*p.2.1.val+2<=v.val));have M:Lfilt.Nodup:=(jZ (2*N)).filter _;have d:∀ v:Fin (2*N),v∈Lfilt↔v=aA w:=(by intro v;simp only[Lfilt,gd,mK,fR,gy,cG,lJ];constructor;{rintro⟨ap,_⟩;rw[<- ap,bH]};{rintro rfl;exact⟨bH w,o⟩});cases hL:Lfilt with
        | nil=>exact absurd ((d (aA w)).mpr rfl) (by simp[hL])
        | cons a as=>
          have ha:a=aA w:=(d a).mp (by simp[hL]);subst ha;cases as with
          | nil=>rfl
          | cons b bs=>have hb:b=aA w:=(d b).mp (by simp[hL]);rw[hL,hb] at M;simp at M
       {rw[nJ];intro v _;simp only[gy,cG,lJ,not_and];rintro⟨rfl,rfl⟩ o;exact Q ⟨rfl,by rwa [bH]⟩}
      change (((((finRange (2*N)).filter (fun v=>decide (2*p.2.1.val+2<=v.val))).filter (fun v=>decide (p.2.1=h/\eE p.2.1 (p.2.2++[v])=w)))).map (fun v=>cK e (p.1,p.2.1,p.2.2++[v]))).sum=_;rw[r];split_ifs;{simp only[aO,fC,eu,mO,g1,cK,lU];ring};{simp}
     have af:∀(L:Ls (fG N)) (f:fG N->Ls (fG N)) (g:fG N->R),((L.flatMap f).map g).sum=(L.map (fun a=>((f a).map g).sum)).sum:=by
      intro L f g;induction L with
      | nil=>simp
      | cons a L S=>simp[eY,S]
     rw[af (aW N t) _ (cK e)]
     simp_rw [a3];split_ifs with o
     ·
      simp_rw [o,and_true];induction (aW N t) with
      | nil=>simp
      | cons p ps a7=>simp only[aO,eu,po,a7];by_cases i:p.2.1=h <;> simp[i]
     ·
      simp_rw [o,and_false];induction (aW N t) with
      | nil=>simp
      | cons p ps a7=>simp
    rw[ag];by_cases a6:2*h.val+2<=(aA w).val;{have ao:2*h.val+1<=w.val:=(by change 2*h.val+2<=if w.val % 2=0 then w.val+1 else w.val-1 at a6;split_ifs at a6 <;> omega);simp only[ao,a6,↓reduceIte];rw[hO _ _ (fun p=>eE p.2.1 p.2.2)];refine dB rfl fun u _=>?_;by_cases P:2*h.val+1<=u.val;{rw[dP P,ih h u];have aq:((aW N t).filter (fun p=>decide (p.2.1=h))).filter (fun p=>decide (eE p.2.1 p.2.2=u))=(aW N t).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=u)):=(by rw[pk];congr 1;funext p;apply Bool.eq_iff_iff.mpr;simp[and_comm]);rw[aq];have a5:(((aW N t).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=u))).map (fun p=>cK e p*e (eE p.2.1 p.2.2) (aA w)*j0 (aA w)))=(((aW N t).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=u))).map (fun p=>cK e p*(e u (aA w)*j0 (aA w)))):=(by refine dF fun p i=>?_;have aa:p.2.1=h/\eE p.2.1 p.2.2=u:=(by simpa using (gd.mp i).2);rw[aa.2,mR]);rw[a5,jh,mR]};{rw[cM P];have j:((aW N t).filter (fun p=>decide (p.2.1=h))).filter (fun p=>decide (eE p.2.1 p.2.2=u))=[]:=(by rw[nJ];intro p i;rw[gd] at i;simp only[cG] at i ⊢;intro z;have o:=oZ ((jU t p).mp i.1).2.1;rw[z,i.2] at o;exact P o);rw[j];simp}};{simp only[a6,↓reduceIte,ite_self]}
   ·
    have a9:(((aW N t).flatMap (fun p=>(((finRange N).filter (fun c=>decide (p.2.1.val<c.val))).map (fun c=>(p.1++[(p.2.1,p.2.2)],c,[]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w)))).map (cK e)).sum=if w.val=2*h.val+1 then (((aW N t).filter (fun p=>decide (p.2.1.val<h.val))).map (fun p=>cK e p*(- e (eE p.2.1 p.2.2) (V p.2.1)))).sum
     else 0:=by
     have a3:∀ p:fG N,(((((finRange N).filter (fun c=>decide (p.2.1.val<c.val))).map (fun c=>(p.1++[(p.2.1,p.2.2)],c,[]))).filter (fun q=>decide (q.2.1=h/\eE q.2.1 q.2.2=w))).map (cK e)).sum=if p.2.1.val<h.val/\w.val=2*h.val+1 then cK e p*(- e (eE p.2.1 p.2.2) (V p.2.1))
      else 0:=by
      intro p;rw[sX,gm]
      have r:((finRange N).filter (fun c=>decide (p.2.1.val<c.val))).filter (fun c=>decide (c=h/\eE c []=w))=if p.2.1.val<h.val/\w.val=2*h.val+1 then [h] else []:=by
       rw[pk];split_ifs with Q
       ·
        obtain⟨K,E⟩:=Q
        set Lfilt:=(finRange N).filter (fun c=>decide (c=h/\eE c []=w)&&decide (p.2.1.val<c.val));have M:Lfilt.Nodup:=(jZ N).filter _;have d:∀ c:Fin N,c∈Lfilt↔c=h:=(by intro c;simp only[Lfilt,gd,mK,fR,gy,cG];constructor;{rintro⟨⟨rfl,_⟩,_⟩;rfl};{rintro rfl;exact⟨⟨rfl,bL E.symm⟩,K⟩});cases hL:Lfilt with
        | nil=>exact absurd ((d h).mpr rfl) (by simp[hL])
        | cons a as=>
          have ha:a=h:=(d a).mp (by simp[hL]);subst ha;cases as with
          | nil=>rfl
          | cons b bs=>have hb:b=a:=(d b).mp (by simp[hL]);rw[hL,hb] at M;simp at M
       {rw[nJ];intro c _;simp only[gy,cG,not_and];rintro⟨rfl,z⟩ K;exact Q ⟨K,(aI Fin.val z).symm⟩}
      change (((((finRange N).filter (fun c=>decide (p.2.1.val<c.val))).filter (fun c=>decide (c=h/\eE c []=w)))).map (fun c=>cK e (p.1++[(p.2.1,p.2.2)],c,[]))).sum=_;rw[r];split_ifs;{simp only[aO,fC,eu,mO,g1,cK,bJ,bR,nO,aO,fC,iS,prod_nil,kQ,dV,bQ,iK];ring};{simp}
     have af:∀(L:Ls (fG N)) (f:fG N->Ls (fG N)) (g:fG N->R),((L.flatMap f).map g).sum=(L.map (fun a=>((f a).map g).sum)).sum:=by
      intro L f g;induction L with
      | nil=>simp
      | cons a L S=>simp[eY,S]
     rw[af]
     simp_rw [a3];split_ifs with E
     ·
      simp_rw [E,and_true];induction (aW N t) with
      | nil=>simp
      | cons p ps a7=>simp only[aO,eu,po,a7];by_cases i:p.2.1.val<h.val <;> simp[i]
     ·
      simp_rw [E,and_false];induction (aW N t) with
      | nil=>simp
      | cons p ps a7=>simp
    rw[a9];split_ifs with E
    {rw[hO _ _ (fun p=>p.2.1)];refine dB rfl fun i _=>?_;by_cases K:i.val<h.val;{rw[dP K];have al:((aW N t).filter (fun p=>decide (p.2.1.val<h.val))).filter (fun p=>decide (p.2.1=i))=(aW N t).filter (fun p=>decide (p.2.1=i)):=(by rw[pk];congr 1;funext p;apply Bool.eq_iff_iff.mpr;simp only[gy,cG];exact⟨fun B=>B.1,fun B=>⟨B,B▸K⟩⟩);rw[al,hO _ _ (fun p=>eE p.2.1 p.2.2)];refine dB rfl fun u _=>?_;by_cases P:2*i.val+1<=u.val;{rw[dP P,ih i u];have ak:((aW N t).filter (fun p=>decide (p.2.1=i))).filter (fun p=>decide (eE p.2.1 p.2.2=u))=(aW N t).filter (fun p=>decide (p.2.1=i/\eE p.2.1 p.2.2=u)):=(by rw[pk];congr 1;funext p;apply Bool.eq_iff_iff.mpr;simp[and_comm]);rw[ak];have a5:(((aW N t).filter (fun p=>decide (p.2.1=i/\eE p.2.1 p.2.2=u))).map (fun p=>cK e p*(- e (eE p.2.1 p.2.2) (V p.2.1))))=(((aW N t).filter (fun p=>decide (p.2.1=i/\eE p.2.1 p.2.2=u))).map (fun p=>cK e p*(- e u (V i)))):=(by refine dF fun p s=>?_;have aa:p.2.1=i/\eE p.2.1 p.2.2=u:=(by simpa using (gd.mp s).2);rw[aa.2,aa.1]);rw[a5,jh]};{rw[cM P];have j:((aW N t).filter (fun p=>decide (p.2.1=i))).filter (fun p=>decide (eE p.2.1 p.2.2=u))=[]:=(by rw[nJ];intro p s;rw[gd] at s;simp only[cG] at s ⊢;intro z;have o:=oZ ((jU t p).mp s.1).2.1;rw[z,s.2] at o;exact P o);rw[j];simp}};{rw[cM K];have j:((aW N t).filter (fun p=>decide (p.2.1.val<h.val))).filter (fun p=>decide (p.2.1=i))=[]:=(by rw[nJ];intro p s;rw[gd] at s;simp only[cG] at s ⊢;rintro rfl;exact K s.2);rw[j];simp}};{rfl}
def ik(N:Nat):Ls (Ls (Cw N)):=(aW N (N-1)).map (fun p=>p.1++[(p.2.1,p.2.2)])
lemma jw(N:Nat):(ik N).Nodup:=by unfold ik;refine (rH (N-1)).map fun e d h=>?_;have c:=qF h rfl;have b:=uW h rfl;simp only[hJ,gL,and_true] at b;exact eC c (eC b.1 b.2)
lemma pQ{N:Nat}(u:1<=N)(q:Ls (Cw N)):q∈ik N↔er N q:=by
 simp only[ik,cC,jU,qA,er];constructor
 ·
  rintro⟨⟨r,h,j⟩,⟨o,i,e,d⟩,rfl⟩;refine⟨?_,e,by
   simp only[bR,ic,aO,fC,eu,mO,g1] at d ⊢;omega⟩
  intro c b;rcases eL.mp b with b|b
  {exact o c b};{simp only[eZ] at b;exact b▸i}
 ·
  rintro⟨i,e,d⟩;cases q using List.reverseRecOn with
  | nil=>simp at d;omega
  | append_singleton r s=>
    rcases s with ⟨h,j⟩
    refine⟨(r,h,j),⟨?_,i (h,j) (by simp),e,?_⟩,rfl⟩;{exact fun c b=>i c (nM _ b)};{simp only[bR,ic,aO,fC,eu,mO,g1] at d ⊢;omega}
lemma n4{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R):uD b=∑ S∈(ik N).toFinset,bJ b S:=by unfold uD;rw[List.sum_toFinset _ (jw N)];unfold ik;rw[gm];have e:∀ p:fG N,bJ b (p.1++[(p.2.1,p.2.2)])=cK b p*(- b (eE p.2.1 p.2.2) (V p.2.1)):=(by intro p;simp only[bJ,bR,nO,aO,fC,iS,prod_nil,kQ,bQ,iK,cK];ring);change _=((aW N (N-1)).map (fun p=>bJ b (p.1++[(p.2.1,p.2.2)]))).sum;rw[dF (fun p _=>e p)];rw[hO _ _ (fun p=>p.2.1)];refine dB rfl fun h _=>?_;rw[hO _ _ (fun p=>eE p.2.1 p.2.2)];refine dB rfl fun u _=>?_;by_cases q:2*h.val+1<=u.val;{rw[dP q,uk b (N-1) h u];have r:((aW N (N-1)).filter (fun p=>decide (p.2.1=h))).filter (fun p=>decide (eE p.2.1 p.2.2=u))=(aW N (N-1)).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=u)):=(by rw[pk];congr 1;funext p;apply Bool.eq_iff_iff.mpr;simp[and_comm]);rw[r];have d:(((aW N (N-1)).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=u))).map (fun p=>cK b p*(- b (eE p.2.1 p.2.2) (V p.2.1))))=(((aW N (N-1)).filter (fun p=>decide (p.2.1=h/\eE p.2.1 p.2.2=u))).map (fun p=>cK b p*(- b u (V h)))):=(by refine dF fun p i=>?_;have j:p.2.1=h/\eE p.2.1 p.2.2=u:=(by simpa using (gd.mp i).2);rw[j.2,j.1]);rw[d,jh]};{rw[cM q];have c:((aW N (N-1)).filter (fun p=>decide (p.2.1=h))).filter (fun p=>decide (eE p.2.1 p.2.2=u))=[]:=(by rw[nJ];intro p i;rw[gd] at i;simp only[cG] at i ⊢;intro s;have o:=oZ ((jU (N-1) p).mp i.1).2.1;rw[s,i.2] at o;exact q o);rw[c];simp}
lemma oC{N:Nat}(v:Fin (2*N)):H v<N:=by simp only[H];omega
lemma pO{N:Nat}(L:L2 N):(L.map aA).map aA=L:=by rw[gm];have h:(aA (N:=N)) ∘ aA=id:=funext bH;rw[h,mN]
lemma ln{N:Nat}(L:L2 N):(L.map aA).map H=L.map H:=by rw[gm];refine dF fun v _=>eJ v
def aE{N:Nat}(c:Cw N):L2 N:=V c.1::c.2
def A{N:Nat}(c:Cw N):Ls Nat:=(aE c).map H
def bE{N:Nat}(u:Fin (2*N)):L2 N->Fin (2*N)->Prop
 | [],target=>u≠target
 | v::b,target=>u≠v/\bE (aA v) b target
def f4{N:Nat}(c:Cw N):Prop:=bE (aZ c.1) c.2 (V c.1)
def fY{N:Nat}(b:Ls (Cw N)):Prop:=∀ c∈b,f4 c
lemma oF{N:Nat}(L:L2 N):List.Perm ((gF L).map H) (L.map H):=by cases L with|nil=>{simp[gF]}|cons c b=>{simp only[gF,aO,eJ,j3,ln];exact List.Perm.cons (H c) (List.reverse_perm _)}
lemma dX{N:Nat}(u:Fin (2*N))(xs:L2 N)(v:Fin (2*N))(ys:L2 N)(target:Fin (2*N)):bE u (xs++v::ys) target↔bE u xs v/\bE (aA v) ys target:=by induction xs generalizing u with|nil=>{simp[bE]}|cons a xs b=>{simp[bE,b,and_assoc]}
lemma pR{N:Nat}(mid:L2 N):∀ u target:Fin (2*N),bE u (mid.reverse.map aA) target↔bE target mid u:=by induction mid with|nil=>{intro u target;simp[bE,ne_comm]}|cons a b c=>{intro u target;simp only[pc,bR,aO,fC,dX,bE,bH,c];tauto}
lemma jk{N:Nat}(h:Fin (2*N))(b:L2 N)(d:((h::b).map H).Nodup):bE (aA h) b h:=by
 have i:∀(u:Fin (2*N)) (xs:L2 N) (target:Fin (2*N)),(H u∉xs.map H)->(xs.map H).Nodup->(H target∉xs.map H)->(u≠target)->bE u xs target:=by
  intro u xs;induction xs generalizing u with
  | nil=>intro target _ _ _ hne;exact hne
  | cons a xs q=>intro target o c j _;simp only[aO,cB,not_or,j5] at o c j;refine⟨fun e=>o.1 (aI H e),q (aA a) target ?_ c.2 j.2 ?_⟩;{rw[eJ];exact c.1};{intro e;exact j.1 ((aI H e).symm.trans (eJ a))}
 simp only[aO,j5] at d;exact i (aA h) b h (by rw[eJ];exact d.1) d.2 d.1 (lj h)
lemma kB{N:Nat}{R:Type*}[CommRing R](e:Fin (2*N)->Fin (2*N)->R)(b:∀ u,e u u=0)(d:L2 N):∀ u target,¬bE u d target->el e u d target=0:=by induction d with|nil=>{intro u target h;simp only[bE,not_not] at h;subst h;exact b u}|cons v d i=>{intro u target h;simp only[bE,not_and] at h;by_cases c:u=v;{subst c;simp[el,b]};{simp only[el,i (aA v) target (h c),mul_zero]}}
lemma kG{N:Nat}{R:Type*}[CommRing R](i:Fin (2*N)->Fin (2*N)->R)(b:∀ u,i u u=0)(d:Ls (Cw N))(h:¬fY d):bJ i d=0:=by simp only[fY,not_forall] at h;obtain⟨c,j,e⟩:=h;have o:bQ i c=0:=(by simp[bQ,kB i b _ _ _ e]);exact List.prod_eq_zero (cC.mpr ⟨c,j,o⟩)
lemma o2{N:Nat}(mid:L2 N)(u:Fin (2*N))(q:bE u mid u):mid.reverse.map aA≠mid:=by
 intro y
 have v:∀(k:Nat) (L:L2 N) (w:Fin (2*N)),L.length=k->bE w L w->L.reverse.map aA=L->False:=by
  intro k;induction k using Nat.strong_induction_on with
  | ind k B=>
    intro L w s r x;cases L with
    | nil=>exact r rfl
    | cons a o=>cases o using List.reverseRecOn with|nil=>{simp only[pc,qO,gl,aO,fC,hJ,and_true] at x;exact lj a x}|append_singleton c b=>{simp only[pc,uJ,qO,gl,fB,aO,bR,fC,hJ] at x;obtain⟨z,i⟩:=x;have e:c.reverse.map aA=c:=qF i (by simp);have h:bE (aA a) (c++[b]) w:=r.2;rw[dX] at h;have j:b=aA a:=(by rw[<- z,bH]);have d:bE (aA a) c (aA a):=j▸h.1;exact B c.length (by simp at s;omega) c (aA a) rfl d e}
 exact v mid.length mid u rfl q y
def fQ{N:Nat}(p:Nat)(c:L2 N):L2 N->Op (L2 N×Fin (2*N)×L2 N)
 | []=>none
 | a::b=>
   if H a=p then some (c,a,b)
   else fQ p (c++[a]) b
lemma i6{N:Nat}(p:Nat)(L:L2 N):∀(b pre:L2 N) (a:Fin (2*N)) (suf:L2 N),(p∉b.map H)->(fQ p b L=some (pre,a,suf)↔b++L=pre++a::suf/\H a=p/\p∉pre.map H):=by induction L with|nil=>{intro b pre a suf d;simp only[fQ,reduceCtorEq,false_iff,cR];rintro⟨i,r,_⟩;apply d;rw[i];simp[r]}|cons x u B=>{intro b pre a suf d;unfold fQ;by_cases j:H x=p;{simp only[j,↓reduceIte,ia,gL];constructor;{rintro⟨rfl,rfl,rfl⟩;exact⟨rfl,j,d⟩};{rintro⟨i,r,v⟩;have w:pre.length<=b.length:=(by by_contra E;have h:b.length<pre.length:=Nat.lt_of_not_le E;have q:pre[b.length]'h=x:=(by have z:=aI (fun l=>l[b.length]?) i;simp only[List.getElem?_append_right (le_refl _),nY,List.getElem?_cons_zero,List.getElem?_append_left h,List.getElem?_eq_getElem h] at z;exact sV z.symm);exact v (cC.mpr ⟨x,q▸iQ h,j⟩));have y:b.length<=pre.length:=(by by_contra h;have e:pre.length<b.length:=Nat.lt_of_not_le h;have q:b[pre.length]'e=a:=(by have z:=aI (fun l=>l[pre.length]?) i;simp only[List.getElem?_append_left e,List.getElem?_eq_getElem e,List.getElem?_append_right (le_refl _),nY,List.getElem?_cons_zero] at z;exact sV z);exact d (cC.mpr ⟨a,q▸iQ e,r⟩));have o:b=pre:=List.append_inj_left i (by omega);have c:x::u=a::suf:=List.append_inj_right i (by omega);simp only[hJ] at c;exact⟨o,c.1,c.2⟩}};{simp only[j,↓reduceIte];have s:p∉(b++[x]).map H:=(by simp only[bR,aO,fC,eL,eZ,not_or];exact⟨d,Ne.symm j⟩);rw[B (b++[x]) pre a suf s];simp[dM]}}
lemma eO{N:Nat}(p:Nat){L:L2 N}(b:(L.map H).Nodup)(pre:L2 N)(a:Fin (2*N))(suf:L2 N):fQ p [] L=some (pre,a,suf)↔L=pre++a::suf/\H a=p:=by rw[i6 p L [] pre a suf (by simp),gl];constructor;{rintro⟨e,d,_⟩;exact⟨e,d⟩};{rintro⟨e,d⟩;refine⟨e,d,?_⟩;rw[e,bR,aO,fu] at b;intro c;exact b.2.2 p c p (by simp[d]) rfl}
lemma ie{N:Nat}(p:Nat){L:L2 N}(e:p∈L.map H):∃ pre a suf,fQ p [] L=some (pre,a,suf):=by
 have h:∀(b:L2 N) (i:L2 N),p∈i.map H->∃ pre a suf,fQ p b i=some (pre,a,suf):=by
  intro b i;induction i generalizing b with
  | nil=>simp
  | cons x d o=>intro j;unfold fQ;by_cases c:H x=p;{exact⟨b,x,d,by simp[c]⟩};{simp only[c,↓reduceIte];simp only[aO,cB] at j;exact o (b++[x]) (j.resolve_left (Ne.symm c))}
 exact h [] L e
def kl{N:Nat}(L:L2 N)(p:Nat):L2 N:=match fQ p [] L with
 | some (pre,a,suf)=>a::suf++pre
 | none=>L
lemma et{N:Nat}{L pre suf:L2 N}{a:Fin (2*N)}{p:Nat}(b:(L.map H).Nodup)(d:L=pre++a::suf)(c:H a=p):kl L p=a::suf++pre:=by unfold kl;rw[(eO p b pre a suf).mpr ⟨d,c⟩]
lemma m3{N:Nat}(L:L2 N)(p:Nat):List.Perm (kl L p) L:=by
 unfold kl;cases h:fQ p [] L with
 | none=>exact s0 _
 | some t=>
   rcases t with ⟨pre,a,suf⟩
   have b:=((i6 p L [] pre a suf (by simp)).mp h).1;rw[gl] at b;rw[b];exact List.perm_append_comm
lemma ms{N:Nat}{R:Type*}[CommRing R](b:Fin (2*N)->Fin (2*N)->R)(L:L2 N)(p:Nat):ff b (kl L p)=ff b L:=by
 unfold kl;cases h:fQ p [] L with
 | none=>rfl
 | some t=>
   rcases t with ⟨pre,a,suf⟩
   have c:=((i6 p L [] pre a suf (by simp)).mp h).1;rw[gl] at c;rw[c];cases pre with
   | nil=>simp
   | cons x xs=>exact p4 b (xs:=a::suf) (ys:=x::xs) (by simp) (by simp)
lemma sm{N:Nat}{xs ys:L2 N}{p:Nat}(c:((xs++ys).map H).Nodup)(d:p∈(xs++ys).map H):kl (ys++xs) p=kl (xs++ys) p:=by
 have b:((ys++xs).map H).Nodup:=(jC (List.perm_append_comm.map H)).mp c;rw[bR,eL] at d;rcases d with d|d
 {obtain⟨a,e,rfl⟩:=cC.mp d;obtain⟨pre,suf,rfl⟩:=qM e;have i:(pre++a::suf)++ys=pre++a::(suf++ys):=(by simp[dM]);have h:ys++(pre++a::suf)=(ys++pre)++a::suf:=(by simp[dM]);rw[et c i rfl,et b h rfl];simp[dM]};{obtain⟨a,e,rfl⟩:=cC.mp d;obtain⟨pre,suf,rfl⟩:=qM e;have i:xs++(pre++a::suf)=(xs++pre)++a::suf:=(by simp[dM]);have h:(pre++a::suf)++xs=pre++a::(suf++xs):=(by simp[dM]);rw[et c i rfl,et b h rfl];simp[dM]}
lemma v3{N:Nat}{L:L2 N}{p:Nat}(e:(L.map H).Nodup)(i:p∈L.map H):kl (gF L) p=gF (kl L p):=by
 have b:((gF L).map H).Nodup:=(jC (oF L)).mpr e;cases L with
 | nil=>simp at i
 | cons d c=>
   simp only[aO,cB] at i;rcases i with rfl|i
   {rw[et e (pre:=[]) (a:=d) (suf:=c) rfl rfl,et b (pre:=[]) (a:=aA d) (suf:=c.reverse.map aA) rfl (eJ d)];simp[gF]};{obtain⟨a,o,rfl⟩:=cC.mp i;obtain⟨pre,suf,rfl⟩:=qM o;have j:d::(pre++a::suf)=(d::pre)++a::suf:=rfl;rw[et e j rfl];have h:gF (d::(pre++a::suf))=(aA d::suf.reverse.map aA)++aA a::(pre.reverse.map aA):=(by simp[gF,uJ,bR,dM]);rw[et b h (eJ a)];simp[gF,uJ,bR,dM]}
def eA{N:Nat}(L:L2 N)(v:Fin (2*N)):L2 N:=match kl L (H v) with
 | []=>[]
 | a::b=>if a=v then a::b else gF (a::b)
lemma oA{N:Nat}{L:L2 N}{v:Fin (2*N)}(e:(L.map H).Nodup)(j:H v∈L.map H):∃ c,eA L v=v::c:=by
 obtain⟨pre,a,suf,i⟩:=ie (H v) j;have b:=(eO (H v) e pre a suf).mp i;have d:kl L (H v)=a::suf++pre:=et e b.1 b.2;unfold eA;rw[d];rcases cI b.2 with rfl|rfl
 {exact⟨suf++pre,by simp⟩};{by_cases h:aA v=v;{exact (lj v h).elim};{exact⟨(suf++pre).reverse.map aA,by simp[h,gF,bH]⟩}}
lemma kj{N:Nat}(L:L2 N)(v:Fin (2*N)):List.Perm ((eA L v).map H) (L.map H):=by
 unfold eA;cases h:kl L (H v) with
 | nil=>
   have:=m3 L (H v)
   rw[h] at this;exact this.map H
 | cons a b=>dsimp only;split_ifs;{rw[<- h];exact (m3 L (H v)).map H};{exact (oF (a::b)).trans (h▸(m3 L (H v)).map H)}
lemma nn{N:Nat}{R:Type*}[CommRing R](c:Fin (2*N)->Fin (2*N)->R)(d:∀ a b,c b a=-c a b)(L:L2 N)(v:Fin (2*N)):ff c (eA L v)=ff c L:=by
 unfold eA;cases h:kl L (H v) with
 | nil=>
   have:=ms c L (H v)
   rw[h] at this;exact this
 | cons a e=>dsimp only;split_ifs;{rw[<- h];exact ms c L (H v)};{rw[td c d,<- h];exact ms c L (H v)}
lemma qo{N:Nat}{xs ys:L2 N}{v:Fin (2*N)}(b:((xs++ys).map H).Nodup)(c:H v∈(xs++ys).map H):eA (ys++xs) v=eA (xs++ys) v:=by unfold eA;rw[sm b c]
lemma tU{N:Nat}{L:L2 N}{v:Fin (2*N)}(e:(L.map H).Nodup)(i:H v∈L.map H):eA (gF L) v=eA L v:=by
 obtain⟨pre,a,suf,h⟩:=ie (H v) i;have c:=(eO (H v) e pre a suf).mp h;have d:kl L (H v)=a::(suf++pre):=(by simpa[fB] using et e c.1 c.2);have b:kl (gF L) (H v)=gF (a::(suf++pre)):=(by rw[v3 e i,d]);rcases cI c.2 with rfl|rfl
 {simp only[eA,d,b];rw[show gF (a::(suf++pre))=aA a::(suf++pre).reverse.map aA from rfl];simp only[lj,↓reduceIte];exact sg (a::(suf++pre))}
 ·
  simp only[eA,d,b];rw[show gF (aA v::(suf++pre))=v::(suf++pre).reverse.map aA by
   simp only[gF,bH]]
  simp only[lj,↓reduceIte]
lemma oB{N:Nat}{L:L2 N}{u v:Fin (2*N)}(i:(L.map H).Nodup)(w:H u∈L.map H)(s:H v∈L.map H):eA (eA L u) v=eA L v:=by
 obtain⟨pre,a,suf,r⟩:=ie (H u) w;have b:=(eO (H u) i pre a suf).mp r;have d:kl L (H u)=a::(suf++pre):=(by simpa[fB] using et i b.1 b.2)
 have c:eA (a::(suf++pre)) v=eA L v:=by
  have o:((pre++a::suf).map H).Nodup:=b.1▸i;have q:H v∈(pre++a::suf).map H:=b.1▸s
  have:=qo (xs:=pre) (ys:=a::suf) o q
  simpa[<- b.1,fB] using this
 have e:((a::(suf++pre)).map H).Nodup:=(jC ((d▸m3 L (H u)).map H)).mpr i;have h:H v∈(a::(suf++pre)).map H:=((d▸m3 L (H u)).map H).mem_iff.mpr s;have j:eA L u=if a=u then a::(suf++pre) else gF (a::(suf++pre)):=(by unfold eA;rw[d]);rw[j];split_ifs;{exact c};{exact (tU e h).trans c}
lemma rm{N:Nat}{v:Fin (2*N)}{b:L2 N}(c:((v::b).map H).Nodup):eA (v::b) v=v::b:=by unfold eA;rw[et c (pre:=[]) (a:=v) (suf:=b) rfl rfl];simp
def iE{N:Nat}:L2 N->Nat
 | []=>0
 | [a]=>H a
 | a::b::c=>min (H a) (iE (b::c))
lemma lS{N:Nat}:∀ {L:L2 N},L≠[]->iE L∈L.map H
 | [],h=>(h rfl).elim
 | [a],_=>by simp[iE]
 | a::b::c,_=>by
   simp only[iE,aO,cB];rcases le_total (H a) (iE (b::c)) with d|d
   {left;exact min_eq_left d};{right;rw[min_eq_right d];simpa only[aO,cB] using lS (ib b c)}
lemma rj{N:Nat}:∀ {L:L2 N} {x:Fin (2*N)},x∈L->iE L<=H x
 | [],_,c=>by simp at c
 | [a],x,c=>by simp at c;subst c;exact le_refl _
 | a::b::e,x,c=>by
   simp only[iE];rcases cB.mp c with rfl|d
   {exact min_le_left _ _};{exact mS (min_le_right _ _) (rj d)}
lemma lq{N:Nat}{L:L2 N}(c:L≠[]):iE L<N:=by obtain⟨x,_,b⟩:=cC.mp (lS c);rw[<- b];exact oC x
def iA{N:Nat}(L:L2 N)(b:L≠[]):Cw N:=
 let h:Fin N:=⟨iE L,lq b⟩
 (h,(eA L (V h)).tail)
lemma i9{N:Nat}{L:L2 N}(b:L≠[])(c:(L.map H).Nodup):aE (iA L b)=eA L (V ⟨iE L,lq b⟩):=by unfold iA aE;dsimp only;have h:H (V ⟨iE L,lq b⟩)∈L.map H:=(by rw[bK];exact lS b);obtain⟨d,e⟩:=oA c h;rw[e];rfl
lemma s7{N:Nat}{L:L2 N}(d:L≠[])(e:(L.map H).Nodup):ko (iA L d):=by
 have s:=i9 d e;have b:=kj L (V ⟨iE L,lq d⟩);rw[<- s] at b;have c:((aE (iA L d)).map H).Nodup:=(jC b).mpr e;simp only[aE,aO,j5,bK] at c;intro v u;have h:H v∈L.map H:=b.mem_iff.mp (g9 _ (j1 u));obtain⟨x,j,i⟩:=cC.mp h;have q:(iA L d).1.val<=H v:=(by rw[<- i];exact rj j)
 have o:H v≠(iA L d).1.val:=fun r=>
  c.1 (r▸j1 u)
 simp only[H] at q o;omega
def eP{N:Nat}(b:Ls Nat)(d:L2 N):L2 N->Op (L2 N×Fin (2*N)×L2 N)
 | []=>none
 | v::c=>
   if H v∈d.map H\/H v∈b then some (d.reverse,v,c)
   else eP b (v::d) c
lemma iF{N:Nat}(b:Ls Nat)(c x:L2 N)(e:(c.map H).Nodup)(i:∀ p∈c.map H,p∉b):eP b c x=none↔((c.reverse++x).map H).Nodup/\∀ p∈x.map H,p∉b:=by
 induction x generalizing c with
 | nil=>simp only[eP,cR,fC,not_mem_nil,IsEmpty.forall_iff,implies_true,and_true,true_iff];rw[j3,List.nodup_reverse];exact e
 | cons v q B=>
   unfold eP;have j:H v∈c.map H↔H v∈c.reverse.map H:=(by rw[j3,mem_reverse]);by_cases d:H v∈c.map H\/H v∈b
   ·
    rw[dP d];simp only[reduceCtorEq,false_iff,not_and];intro w r;rcases d with z|s
    {rw[bR,aO,fu] at w;exact w.2.2 _ (j.mp z) _ gK rfl};{exact r (H v) gK s}
   ·
    rw[cM d]
    push_neg at d;have o:((v::c).map H).Nodup:=(by simp only[aO,j5];exact⟨d.1,e⟩)
    have h:∀ p∈(v::c).map H,p∉b:=by
     intro p L;simp only[aO,cB] at L;rcases L with rfl|y
     {exact d.2};{exact i p y}
    rw[B (v::c) o h];have u:(v::c).reverse++q=c.reverse++v::q:=(by simp);rw[u];simp only[aO,cB,forall_eq_or_imp,d.2,not_false_eq_true,fR]
lemma f1{N:Nat}(d:Ls Nat)(i M:L2 N)(u:(i.map H).Nodup)(q:∀ p∈i.map H,p∉d)(pre:L2 N)(v:Fin (2*N))(suf:L2 N):eP d i M=some (pre,v,suf)↔∃ c,pre=i.reverse++c/\M=c++v::suf/\((i.reverse++c).map H).Nodup/\(∀ p∈(i.reverse++c).map H,p∉d)/\(H v∈(i.reverse++c).map H\/H v∈d):=by
 induction M generalizing i with
 | nil=>simp only[eP,reduceCtorEq,false_iff];rintro⟨c,_,a4,_⟩;exact List.append_ne_nil_of_right_ne_nil c (ib v suf) a4.symm
 | cons a a8 Q=>
   unfold eP;have j:∀ x:Fin (2*N),H x∈i.map H↔H x∈i.reverse.map H:=fun x=>by rw[j3,mem_reverse]
   by_cases e:H a∈i.map H\/H a∈d
   ·
    rw[dP e];constructor;{intro h;simp only[ia,gL] at h;obtain⟨rfl,rfl,rfl⟩:=h;refine⟨[],by simp,rfl,?_,?_,?_⟩;{simpa[j3,List.nodup_reverse] using u};{intro p E;simp only[cR,j3,mem_reverse] at E;exact q p E};{simpa only[cR,j a] using e}}
    ·
     rintro⟨c,r,s,y,o,_⟩;cases c with
     | nil=>simp only[gl,hJ] at s;obtain⟨rfl,rfl⟩:=s;simp only[cR] at r;rw[r]
     | cons b K=>
       simp only[fB,hJ] at s;obtain⟨rfl,_⟩:=s;exfalso;rcases e with P|L
       {rw[bR,aO,fu] at y;exact y.2.2 _ ((j a).mp P) _ gK rfl};{exact o (H a) (by simp) L}
   ·
    rw[cM e]
    push_neg at e;have z:((a::i).map H).Nodup:=(by simp only[aO,j5];exact⟨e.1,u⟩)
    have w:∀ p∈(a::i).map H,p∉d:=by intro p E;simp only[aO,cB] at E;rcases E with rfl|S;exact e.2;exact q p S
    rw[Q (a::i) z w];constructor;{rintro⟨K,r,a0,y,o,B⟩;refine⟨a::K,by simpa using r,by simp[a0],by simpa using y,by simpa using o,by simpa using B⟩}
    ·
     rintro⟨c,r,s,y,o,B⟩;cases c with
     | nil=>
       simp only[gl,hJ] at s;obtain⟨rfl,_⟩:=s;simp only[cR] at B;rcases B with P|L
       {exact (e.1 ((j a).mpr P)).elim};{exact (e.2 L).elim}
     | cons b K=>simp only[fB,hJ] at s;obtain⟨rfl,rfl⟩:=s;refine⟨K,by simpa using r,rfl,by simpa using y,by simpa using o,by simpa using B⟩
def eH{N:Nat}(d:Cw N):Ls (Cw N)->Ls (Cw N)
 | []=>[d]
 | c::b=>if d.1<c.1 then d::c::b else c::eH d b
def bC{N:Nat}(p:Nat):Ls (Cw N)->Op ((Cw N)×Ls (Cw N))
 | []=>none
 | c::b=>
   if p∈A c then some (c,b)
   else (bC p b).map (fun r=>(r.1,c::r.2))
lemma es{N:Nat}(d:Cw N)(b:Ls (Cw N)):List.Perm (eH d b) (d::b):=by induction b with|nil=>{exact s0 _}|cons c b e=>{unfold eH;split_ifs;{exact s0 _};{exact (List.Perm.cons c e).trans (List.Perm.swap d c b)}}
lemma p7{N:Nat}(d:Cw N)(j:Ls (Cw N))(b:(j.map Prod.fst).Pairwise (·<·))(q:∀ c∈j,d.1≠c.1):((eH d j).map Prod.fst).Pairwise (·<·):=by
 induction j with
 | nil=>simp[eH]
 | cons c j s=>
   unfold eH;simp only[aO,jE] at b;split_ifs with h
   ·
    simp only[aO,jE];refine⟨?_,b.1,b.2⟩;intro x o;rcases cB.mp o with rfl|e
    {exact h};{exact hK h (b.1 x e)}
   ·
    have i:c.1<d.1:=qS (not_lt.mp h) (q c gK).symm;simp only[aO,jE];refine⟨?_,s b.2 (fun x o=>q x (g9 c o))⟩;intro x o;have r:x∈(d::j).map Prod.fst:=((es d j).map Prod.fst).mem_iff.mp o;rcases cB.mp r with rfl|e
    {exact i};{exact b.1 x e}
lemma gs{N:Nat}{p:Nat}{q:Ls (Cw N)}{d:Cw N}{b:Ls (Cw N)}(h:bC p q=some (d,b)):p∈A d/\List.Perm q (d::b)/\(∀ c∈b,c∈q)/\d∈q:=by
 induction q generalizing b with
 | nil=>simp[bC] at h
 | cons c j w=>
   unfold bC at h;split_ifs at h with y
   {simp only[ia,gL] at h;obtain⟨rfl,rfl⟩:=h;exact⟨y,s0 _,fun _ u=>g9 _ u,gK⟩}
   ·
    cases hrec:bC p j with
    | none=>simp[hrec] at h
    | some r=>
      rw[hrec] at h;simp only[pw,ia,gL] at h;obtain⟨rfl,rfl⟩:=h;obtain⟨v,e,o,i⟩:=w hrec;refine⟨v,(List.Perm.cons c e).trans (List.Perm.swap r.1 c r.2),?_,g9 c i⟩;intro x u;rcases cB.mp u with rfl|s
      {exact gK};{exact g9 c (o x s)}
lemma jR{N:Nat}{p:Nat}{q:Ls (Cw N)}(j:p∈q.flatMap A):∃ d o,bC p q=some (d,o):=by induction q with|nil=>{simp at j}|cons c h r=>{simp only[eY,eL] at j;unfold bC;by_cases e:p∈A c;{rw[dP e];exact⟨c,h,rfl⟩};{rw[cM e];obtain⟨d,b,i⟩:=r (j.resolve_left e);rw[i];exact⟨d,c::b,rfl⟩}}
lemma mZ{N:Nat}{p:Nat}{o:Ls (Cw N)}{d:Cw N}{e:Ls (Cw N)}(b:(o.map Prod.fst).Pairwise (·<·))(h:bC p o=some (d,e)):(e.map Prod.fst).Pairwise (·<·):=by
 induction o generalizing e with
 | nil=>simp[bC] at h
 | cons c i q=>
   unfold bC at h;simp only[aO,jE] at b;split_ifs at h with v
   {simp only[ia,gL] at h;obtain⟨rfl,rfl⟩:=h;exact b.2}
   ·
    cases hrec:bC p i with|none=>{simp[hrec] at h}|some r=>{rw[hrec] at h;simp only[pw,ia,gL] at h;obtain⟨rfl,rfl⟩:=h;obtain⟨_,_,j,_⟩:=gs hrec;simp only[aO,jE];refine⟨fun x u=>?_,q b.2 hrec⟩;obtain⟨y,s,rfl⟩:=cC.mp u;exact b.1 y.1 (j1 (j y s))}
lemma lr{N:Nat}{p:Nat}{d:Cw N}{h:Ls (Cw N)}(e:p∈A d)(b:p∉h.flatMap A):bC p (eH d h)=some (d,h):=by induction h with|nil=>{simp[eH,bC,e]}|cons c i j=>{simp only[eY,eL,not_or] at b;unfold eH;split_ifs;{simp[bC,e]};{simp only[bC,b.1,↓reduceIte,j b.2,pw]}}
lemma lu{N:Nat}{p:Nat}{q:Ls (Cw N)}{d:Cw N}{j:Ls (Cw N)}(b:(q.map Prod.fst).Pairwise (·<·))(h:bC p q=some (d,j)):eH d j=q:=by
 induction q generalizing j with
 | nil=>simp[bC] at h
 | cons c e w=>
   unfold bC at h;simp only[aO,jE] at b;split_ifs at h with x
   ·
    simp only[ia,gL] at h;obtain⟨rfl,rfl⟩:=h;cases e with
    | nil=>rfl
    | cons v s=>have u:c.1<v.1:=b.1 v.1 (by simp);simp[eH,u]
   ·
    cases hrec:bC p e with|none=>{simp[hrec] at h}|some r=>{rw[hrec] at h;simp only[pw,ia,gL] at h;obtain⟨rfl,rfl⟩:=h;obtain⟨_,_,_,i⟩:=gs hrec;have o:c.1<r.1.1:=b.1 r.1.1 (j1 i);simp only[eH,e7 o,↓reduceIte,w b.2 hrec]}
def jK{N:Nat}(b:Ls (Cw N)):Prop:=(∀ c∈b,ko c)/\(b.map Prod.fst).Pairwise (·<·)/\(b.flatMap A).Nodup
abbrev bO{N:Nat}(seq:Ls (Cw N)):Prop:=(seq.flatMap A).Nodup
def cN{N:Nat}:Ls (Cw N)->Ls (Cw N)->Ls (Cw N)
 | [],e=>e
 | c::b,e=>
   let h:=e.flatMap A
   match eP h [V c.1] c.2 with
   | none=>cN b (c::e)
   | some (pre,v,suf)=>
     if H v∈pre.map H then match fQ (H v) [] pre with
      | none=>b.reverse++c::e
      | some (i,u,mid)=>
        if v=u then
         let o:Cw N:=(c.1,i.tail++u::suf);let d:=iA (u::mid) (ib u mid)
         b.reverse++o::eH d e
        else
         let o:Cw N:=
          (c.1,i.tail++u::(mid.reverse.map aA)++v::suf)
         b.reverse++o::e
     else match bC (H v) e with
      | none=>b.reverse++c::e
      | some (d,j)=>
        let mid:=(eA (aE d) v).tail;let o:Cw N:=(c.1,pre.tail++v::mid++v::suf)
        b.reverse++o::j
def cW{N:Nat}(b:Ls (Cw N)):Ls (Cw N):=cN b.reverse []
lemma gZ{N:Nat}(c e b:Ls (Cw N))(v:((c.reverse++b).flatMap A).Nodup):cN (c++e) b=cN e (c.reverse++b):=by
 induction c generalizing b with
 | nil=>simp
 | cons d L z=>
   simp only[fB];have u:(L.reverse.flatMap A++(A d++b.flatMap A)).Nodup:=(by simpa[mJ,dM] using v);have j:(A d++b.flatMap A).Nodup:=(fu.mp u).2.1;have q:(A d).Nodup:=(fu.mp j).1
   have h:∀ p∈A d,p∉b.flatMap A:=fun p y x=>
    (fu.mp j).2.2 p y p x rfl
   have o:(([V d.1]).map H).Nodup:=(by simp);have i:∀ p∈([V d.1]).map H,p∉b.flatMap A:=(by intro p w;simp only[aO,fC,cB,not_mem_nil,or_false] at w;exact h p (by simp[A,aE,w]));have r:eP (b.flatMap A) [V d.1] d.2=none:=(by rw[iF _ _ _ o i];refine⟨by simpa[A,aE] using q,fun p w=>h p (by simp only[A,aE,aO];exact g9 _ w)⟩);dsimp only[cN];rw[r];have s:=z (d::b) (by simpa[dM] using v);simpa[dM] using s
lemma gQ{N:Nat}{c:Cw N}{b:Ls (Cw N)}(e:∀ d∈b,ko d)(q:∀ d∈b,c.1<d.1):c.1.val∉b.flatMap A:=by
 intro u;obtain⟨d,hd,h⟩:=gM.mp u;have o:c.1.val<d.1.val:=q d hd;simp only[A,aE,aO,cB] at h;rcases h with r|i
 {rw[bK] at r;omega};{obtain⟨x,s,j⟩:=cC.mp i;have v:=e d hd x s;simp only[H] at j;omega}
lemma md{d:Type*}{r:d->d->Prop}{xs ys:Ls d}{a:d}(h:(xs++a::ys).Pairwise r):(∀ x∈xs,r x a)/\(∀ y∈ys,r a y)/\(xs.Pairwise r)/\(ys.Pairwise r):=by rw[kL] at h;obtain⟨e,b,c⟩:=h;rw[jE] at b;exact⟨fun x i=>c x i a gK,b.1,e,b.2⟩
lemma me{e:Type*}{r:e->e->Prop}{xs ys b:Ls e}{a:e}(h:(xs++a::ys).Pairwise r)(c:b.Pairwise r)(j:∀ y∈b,r a y)(d:∀ x∈xs,∀ y∈b,r x y):(xs++a::b).Pairwise r:=by
 rw[kL] at h ⊢;refine⟨h.1,jE.mpr ⟨j,c⟩,fun x o y q=>?_⟩;rcases cB.mp q with rfl|i
 {exact h.2.2 x o y gK};{exact d x o y i}
lemma ja{N L:Nat}:∀(a6 i:Ls (Cw N)),er L (a6.reverse++i)->fY (a6.reverse++i)->jK i->let cn:=cN a6 i
 er L cn/\
 fY cn/\
 cW cn=a6.reverse++i/\
 (bO (a6.reverse++i)->cn=a6.reverse++i)/\
 (¬bO (a6.reverse++i)->cn≠a6.reverse++i):=by
 intro a6;induction a6 with
 | nil=>intro i cz aq a9;simp only[qO,gl] at cz aq ⊢;dsimp only[cN];refine⟨cz,aq,?_,fun _=>rfl,fun ef=>(ef a9.2.2).elim⟩;unfold cW;have ed:=gZ i.reverse [] [] (by simpa using a9.2.2);simpa only[cR,g0,cN] using ed
 | cons c b ih=>
   intro i cz aq a9;have cq:(c::b).reverse++i=b.reverse++c::i:=(by simp[dM]);rw[cq] at cz aq ⊢;obtain⟨b0,ct,c1⟩:=cz;have cs:(b.reverse.map Prod.fst++c.1::i.map Prod.fst).Pairwise (·<·):=(by simpa only[bR,aO] using ct);have b6:=md cs;have w:ko c:=b0 c (by simp);have ce:f4 c:=aq c (by simp);have ab:∀ d∈i,c.1<d.1:=fun d hd=>b6.2.1 d.1 (j1 hd)
   have br:∀ r∈b.reverse,r.1<c.1:=fun r hr=>
    b6.1 r.1 (j1 hr)
   have ay:(([V c.1]).map H).Nodup:=(by simp);have ao:∀ p∈([V c.1]).map H,p∉i.flatMap A:=(by intro p P;simp only[aO,fC,cB,not_mem_nil,or_false,bK] at P;subst P;exact gQ a9.1 ab);cases hsfh:eP (i.flatMap A) [V c.1] c.2 with
   | none=>
     have cv:=(iF _ _ _ ay ao).mp hsfh
     have dj:jK (c::i):=by
      refine⟨fun d hd=>?_,?_,?_⟩
      · rcases cB.mp hd with rfl|ej;exact w;exact a9.1 d ej
      {simp only[aO,jE];exact⟨b6.2.1,a9.2.1⟩}
      ·
       simp only[eY,fu];refine⟨by simpa[A,aE] using cv.1,a9.2.2,fun p be q bd cu=>?_⟩;subst cu;simp only[A,aE,aO,cB,bK] at be;rcases be with rfl|e0
       {exact gQ a9.1 ab bd};{exact cv.2 p e0 bd}
     have eh:=ih (c::i) ⟨b0,ct,c1⟩ aq dj;simpa only[cN,hsfh] using eh
   | some r=>
     rcases r with ⟨pre,v,suf⟩
     obtain⟨b8,s,af,bi,ae,c6⟩:=(f1 _ _ _ ay ao pre v suf).mp hsfh;simp only[pc,qO,gl,sw] at s bi ae c6;have ai:pre.tail=b8:=(by rw[s];rfl)
     have b9:¬bO (b.reverse++c::i):=by
      intro e4;have cc:(A c++i.flatMap A).Nodup:=(by have E:(b.reverse.flatMap A++(A c++i.flatMap A)).Nodup:=(by simpa only[bO,mJ,eY] using e4);exact (fu.mp E).2.1);have cd:aE c=pre++v::suf:=(by simp only[aE,s,af,fB]);rcases c6 with du|c5
      {have cw:((pre++v::suf).map H).Nodup:=(by rw[<- cd];exact (fu.mp cc).1);rw[bR,aO,fu] at cw;exact cw.2.2 _ (s▸du) _ gK rfl};{have di:H v∈A c:=(by simp[A,cd]);exact (fu.mp cc).2.2 _ di _ c5 rfl}
     by_cases b1:H v∈pre.map H
     ·
      obtain⟨ad,u,mid,dk⟩:=ie (H v) b1;have al:(pre.map H).Nodup:=s▸bi;have a1:=(eO (H v) al ad u mid).mp dk;have c7:v∈c.2:=(by rw[af];simp);have ec:c.1.val<H v:=(by have:=w v c7;simp only[H];omega);have ci:ad≠[]:=(by intro e2;rw[e2,gl] at a1;have bn:=s.symm.trans a1.1;simp only[hJ] at bn;have ee:H u=c.1.val:=(by rw[<- bn.1,bK]);omega);obtain⟨x0,a3,bc⟩:=List.exists_cons_of_ne_nil ci;have cb:x0=V c.1/\b8=a3++u::mid:=(by have bn:=s.symm.trans a1.1;rw[bc,fB,hJ] at bn;exact⟨bn.1.symm,bn.2⟩);have aa:ad=V c.1::a3:=(by rw[bc,cb.1]);have z:ad.tail=a3:=(by rw[aa];rfl);have o:c.2=a3++u::(mid++v::suf):=(by rw[af,cb.2,dM,fB]);have a2:bE (aZ c.1) a3 u/\bE (aA u) mid v/\bE (aA v) suf (V c.1):=(by have E:bE (aZ c.1) (a3++u::(mid++v::suf)) (V c.1):=o▸ce;rw[dX] at E;have Q:=E.2;rw[dX] at Q;exact⟨E.1,Q.1,Q.2⟩);by_cases db:v=u
      ·
       subst db;let B:Cw N:=(c.1,ad.tail++v::suf);let d:=iA (v::mid) (ib v mid);let j:=eH d i;have av:cN (c::b) i=b.reverse++B::j:=(by simp only[cN,hsfh,b1,↓reduceIte,dk,B,d,j]);rw[av];have bb:((v::mid).map H).Nodup:=(by have E:((ad++v::mid).map H).Nodup:=a1.1▸al;exact (fu.mp (by simpa[bR] using E)).2.1);have b5:∀ p∈ad.map H,p∉(v::mid).map H:=(by have E:((ad++v::mid).map H).Nodup:=a1.1▸al;intro p be bd;exact (fu.mp (by simpa[bR] using E)).2.2 p be p bd rfl);have b4:∀ p∈(v::mid).map H,p∉i.flatMap A:=(by intro p P;apply ae p;rw[<- s,a1.1,bR,eL];exact Or.inr P);have ca:ko d:=s7 (ib v mid) bb;have aj:List.Perm (A d) ((v::mid).map H):=(by unfold A;rw[i9 (ib v mid) bb];exact kj (v::mid) _);have b7:(A d).Nodup:=(jC aj).mpr bb
       have b3:∀ p∈A d,p∉i.flatMap A:=fun p P=>
        b4 p (aj.mem_iff.mp P)
       have an:c.1<d.1:=by
        have bv:d.1.val∈(v::mid).map H:=aj.mem_iff.mp (by simp[A,aE,bK]);obtain⟨x,S,co⟩:=cC.mp bv
        have dh:x∈c.2:=by
         rw[o];rcases cB.mp S with rfl|eb
         {simp};{simp[eb]}
        have e3:=w x dh;simp only[H] at co;exact iU.mpr (by omega)
       have c3:∀ e∈i,d.1≠e.1:=fun e K bn=>by
        have bv:d.1.val∈A d:=(by simp[A,aE,bK]);have dc:d.1.val∈i.flatMap A:=gM.mpr ⟨e,K,by rw[bn];simp[A,aE,bK]⟩;exact b3 _ bv dc
       have a0:jK j:=by
        refine⟨fun e K=>?_,p7 d i a9.2.1 c3,?_⟩
        ·
         have hm:=(es d i).mem_iff.mp K;rcases cB.mp hm with rfl|bw
         {exact ca};{exact a9.1 e bw}
        {have ei:List.Perm (j.flatMap A) ((d::i).flatMap A):=(es d i).flatMap_right A;rw[jC ei,eY,fu];exact⟨b7,a9.2.2,fun p be q bd cu=>b3 p be (cu▸bd)⟩}
       have ah:ko B:=by
        intro x S;apply w x;dsimp only[B] at S;rw[z] at S;rw[o];simp only[eL,cB] at S ⊢;rcases S with E|rfl|Q
        {exact Or.inl E};{exact Or.inr (Or.inl rfl)};{exact Or.inr (Or.inr (Or.inr (Or.inr Q)))}
       have ax:f4 B:=(by unfold f4;change bE (aZ c.1) (ad.tail++v::suf) (V c.1);rw[z,dX];exact⟨a2.1,a2.2.2⟩);have dd:f4 d:=(by unfold f4;rw[<- om];exact jk (V d.1) d.2 b7)
       have c4:er L (b.reverse++B::j):=by
        refine⟨fun e K=>?_,?_,?_⟩
        ·
         simp only[eL,cB] at K;rcases K with E|rfl|Q
         {exact b0 e (by simp[E])};{exact ah};{exact a0.1 e Q}
        ·
         have dy:((b.reverse++B::j).map Prod.fst).Pairwise (·<·):=by
          rw[bR,aO];refine me (by simpa[bR] using ct) a0.2.1 ?_ ?_
          ·
           intro y hy;obtain⟨e,K,rfl⟩:=cC.mp hy;rcases cB.mp ((es d i).mem_iff.mp K) with rfl|bw
           {exact an};{exact ab e bw}
          ·
           intro x S y hy;obtain⟨r,hr,rfl⟩:=cC.mp S;obtain⟨e,K,rfl⟩:=cC.mp hy;have dw:r.1<c.1:=br r hr;rcases cB.mp ((es d i).mem_iff.mp K) with rfl|bw
           {exact hK dw an};{exact hK dw (ab e bw)}
         exact dy
        {have bz:d.2.length+1=mid.length+1:=(by have da:(aE d).length=(v::mid).length:=(by have E:=aj.length_eq;simp only[A,ft] at E;exact E);simpa[aE] using da);have c8:(j.map (fun e=>e.2.length+1)).sum=(d.2.length+1)+(i.map (fun e=>e.2.length+1)).sum:=(by have a7:=(es d i).map (fun e=>e.2.length+1);rw[a7.sum_eq,aO,eu]);have e8:c.2.length+1=(B.2.length+1)+(mid.length+1):=(by simp only[B,z,o,dL,aX];omega);simp only[bR,ic,aO,eu] at c1 ⊢;rw[c8,bz];omega}
       have bl:fY (b.reverse++B::j):=by
        intro e K;simp only[eL,cB] at K;rcases K with E|rfl|Q
        {exact aq e (by simp[E])};{exact ax}
        ·
         rcases cB.mp ((es d i).mem_iff.mp Q) with rfl|bw
         {exact dd};{exact aq e (by simp[bw])}
       have c2:cW (b.reverse++B::j)=b.reverse++c::i:=by
        unfold cW;rw[show (b.reverse++B::j).reverse=j.reverse++B::b by
         simp[dM]]
        rw[gZ j.reverse (B::b) [] (by simpa using a0.2.2)];simp only[g0,cR]
        have az:∀ p∈([V B.1]).map H,p∉j.flatMap A:=by
         intro p P;simp only[aO,fC,cB,not_mem_nil,or_false,bK] at P;subst P;exact gQ a0.1 (fun e K=>by
          rcases cB.mp ((es d i).mem_iff.mp K) with rfl|bw
          {exact an}
          · exact ab e bw)
        have cj:(ad.map H).Nodup:=(by have E:(ad.map H++(v::mid).map H).Nodup:=(by rw[<- bR];exact a1.1▸al);exact (fu.mp E).1)
        have bu:∀ p∈ad.map H,p∉j.flatMap A:=by
         intro p P cl;have dg:=((es d i).flatMap_right A).mem_iff.mp cl;simp only[eY,eL] at dg;rcases dg with dn|dm
         {exact b5 p P (aj.mem_iff.mp dn)};{exact ae p (by rw[<- s,a1.1,bR,eL];exact Or.inl P) dm}
        have bs:H v∈j.flatMap A:=(by rw[((es d i).flatMap_right A).mem_iff];simp only[eY,eL];exact Or.inl (aj.mem_iff.mpr (by simp)));have bh:eP (j.flatMap A) [V B.1] B.2=some (ad,v,suf):=(by rw[f1 _ _ _ ay az];refine⟨a3,by simpa[B] using aa,by simp[B,z],by simpa[<- aa] using cj,by simpa[<- aa] using bu,Or.inr bs⟩)
        have bg:H v∉ad.map H:=fun hm=>
         b5 (H v) hm (by simp)
        have ba:bC (H v) j=some (d,i):=lr (aj.mem_iff.mpr (by simp)) (b4 (H v) (by simp));have e1:eA (aE d) v=v::mid:=(by rw[i9 (ib v mid) bb];have eg:H (V ⟨iE (v::mid),lq (ib v mid)⟩)∈(v::mid).map H:=(by rw[bK];exact lS (ib v mid));rw[oB bb eg (by simp)];exact rm bb);dsimp only[cN];rw[bh];dsimp only;rw[cM bg,ba];dsimp only;rw[e1];dsimp only[List.tail_cons];congr 1;rw[hJ];refine⟨eC rfl ?_,rfl⟩;simp only[z,o,dM,fB]
       have aw:b.reverse++B::j≠b.reverse++c::i:=(by intro h;have bm:=aI List.length h;have c9:j.length=i.length+1:=(by rw[(es d i).length_eq];simp);simp only[dL,aX,c9] at bm;omega);exact⟨c4,bl,c2,fun hc=>(b9 hc).elim,fun _=>aw⟩
      ·
       have dv:v=aA u:=(cI a1.2.symm).resolve_left db;let ap:=mid.reverse.map aA;let B:Cw N:=(c.1,ad.tail++u::ap++v::suf);have av:cN (c::b) i=b.reverse++B::i:=(by simp only[cN,hsfh,b1,↓reduceIte,dk,db,B,ap]);rw[av];have cm:ap≠mid:=(by have ck:bE (aA u) mid (aA u):=dv▸a2.2.1;exact o2 mid (aA u) ck)
       have ah:ko B:=by
        intro x S;simp only[B,z,eL,cB] at S;rcases S with ((E|rfl|Q)|rfl|h3)
        {exact w x (by rw[o];simp[E])};{exact w x (by rw[o];simp)};{obtain⟨y,hy,rfl⟩:=cC.mp Q;have ea:y∈mid:=mem_reverse.mp hy;have e9:2*c.1.val+2<=y.val:=w y (by rw[o];simp[ea]);have P:=eJ y;simp only[H] at P;change 2*c.1.val+2<=(aA y).val;omega};{exact w x (by rw[o];simp)};{exact w x (by rw[o];simp[h3])}
       have ax:f4 B:=(by unfold f4;change bE (aZ c.1) (ad.tail++u::ap++v::suf) (V c.1);rw[z,dM,fB,dX,dX];refine⟨a2.1,?_,a2.2.2⟩;rw[dv] at a2 ⊢;exact (pR mid (aA u) (aA u)).mpr a2.2.1)
       have c4:er L (b.reverse++B::i):=by
        refine⟨fun e K=>?_,?_,?_⟩
        ·
         simp only[eL,cB] at K;rcases K with E|rfl|Q
         {exact b0 e (by simp[E])};{exact ah};{exact b0 e (by simp[Q])}
        {simpa[B] using ct};{have cy:B.2.length=c.2.length:=(by simp only[B,z,o,ap,dL,aX,ft,j2];omega);simpa only[bR,ic,aO,eu,cy] using c1}
       have bl:fY (b.reverse++B::i):=by
        intro e K;simp only[eL,cB] at K;rcases K with E|rfl|Q
        {exact aq e (by simp[E])};{exact ax};{exact aq e (by simp[Q])}
       have c2:cW (b.reverse++B::i)=b.reverse++c::i:=by
        unfold cW;rw[show (b.reverse++B::i).reverse=i.reverse++B::b by
         simp[dM]]
        rw[gZ i.reverse (B::b) [] (by simpa using a9.2.2)];simp only[g0,cR];let M:=ad++u::ap;have au:List.Perm (M.map H) (pre.map H):=(by rw[a1.1];simp only[M,bR,aO,ap,ln,j3];exact List.Perm.append_left _ (List.Perm.cons _ (List.reverse_perm _)));have am:(M.map H).Nodup:=(jC au).mpr al
        have ar:∀ p∈M.map H,p∉i.flatMap A:=fun p P=>
         ae p (s▸au.mem_iff.mp P)
        have ag:H v∈M.map H:=au.mem_iff.mpr b1;have bh:eP (i.flatMap A) [V B.1] B.2=some (M,v,suf):=(by rw[f1 _ _ _ ay ao];refine⟨a3++u::ap,by simp[M,aa],by simp[B,z,dM],by simpa[M,aa,B] using am,by simpa[M,aa,B] using ar,Or.inl (by simpa[M,aa,B] using ag)⟩);have cp:fQ (H v) [] M=some (ad,u,ap):=(eO (H v) am ad u ap).mpr ⟨rfl,a1.2⟩;dsimp only[cN];rw[bh];dsimp only;rw[dP ag,cp];dsimp only;rw[cM db];congr 1;rw[hJ];refine⟨eC rfl ?_,rfl⟩;simp only[z,o,ap,j3,g0,pO,dM,fB]
       have aw:b.reverse++B::i≠b.reverse++c::i:=by
        intro h;have ds:B=c:=(by have E:=uS h;exact (List.cons.inj E).1)
        have Q:a3++u::(ap++v::suf)=a3++u::(mid++v::suf):=by
         have:=aI Prod.snd ds
         simpa[B,z,o,dM] using this
        have h3:=(List.cons.inj (uS Q)).2;exact cm (List.append_cancel_right h3)
       exact⟨c4,bl,c2,fun hc=>(b9 hc).elim,fun _=>aw⟩
     ·
      have c5:H v∈i.flatMap A:=c6.resolve_left (s▸b1);obtain⟨d,j,ba⟩:=jR c5;obtain⟨dz,a7,bf,bx⟩:=gs ba;have b7:(A d).Nodup:=(by have E:((d::j).flatMap A).Nodup:=(jC (a7.flatMap_right A)).mp a9.2.2;exact (fu.mp (by simpa[eY] using E)).1);have bo:∀ p∈A d,p∉j.flatMap A:=(by have E:((d::j).flatMap A).Nodup:=(jC (a7.flatMap_right A)).mp a9.2.2;intro p be bd;exact (fu.mp (by simpa[eY] using E)).2.2 p be p bd rfl);obtain⟨mid,bk⟩:=oA b7 dz;let B:Cw N:=(c.1,pre.tail++v::mid++v::suf);have av:cN (c::b) i=b.reverse++B::j:=(by simp only[cN,hsfh,b1,↓reduceIte,ba,bk,jF,B]);rw[av];have a8:List.Perm ((v::mid).map H) (A d):=(by rw[<- bk];exact kj (aE d) v);have c0:((v::mid).map H).Nodup:=(jC a8).mpr b7;have an:c.1<d.1:=ab d bx;have a0:jK j:=(by refine⟨fun e K=>a9.1 e (bf e K),mZ a9.2.1 ba,?_⟩;have E:((d::j).flatMap A).Nodup:=(jC (a7.flatMap_right A)).mp a9.2.2;exact (fu.mp (by simpa[eY] using E)).2.1)
      have ah:ko B:=by
       intro x S;simp only[B,ai,eL,cB] at S;rcases S with ((E|rfl|Q)|rfl|h3)
       {exact w x (by rw[af];simp[E])};{exact w x (by rw[af];simp)}
       ·
        have df:H x∈A d:=a8.mem_iff.mp (j1 (g9 v Q));simp only[A,aE,aO,cB,bK] at df;change 2*c.1.val+2<=x.val;rcases df with bn|hm
        {simp only[H] at bn;have:c.1.val<d.1.val:=an;omega};{obtain⟨y,hy,hyp⟩:=cC.mp hm;have e3:=a9.1 d bx y hy;have:c.1.val<d.1.val:=an;simp only[H] at hyp;omega}
       {exact w x (by rw[af];simp)};{exact w x (by rw[af];simp[h3])}
      have ax:f4 B:=(by unfold f4;change bE (aZ c.1) (pre.tail++v::mid++v::suf) (V c.1);have E:bE (aZ c.1) (b8++v::suf) (V c.1):=af▸ce;rw[dX] at E;rw[ai,dM,fB,dX,dX];exact⟨E.1,jk v mid c0,E.2⟩)
      have c4:er L (b.reverse++B::j):=by
       refine⟨fun e K=>?_,?_,?_⟩
       ·
        simp only[eL,cB] at K;rcases K with E|rfl|Q
        {exact b0 e (by simp[E])};{exact ah};{exact a0.1 e Q}
       {rw[bR,aO];refine me (by simpa[bR] using ct) a0.2.1 ?_ ?_;{intro y hy;obtain⟨e,K,rfl⟩:=cC.mp hy;exact ab e (bf e K)};{intro x S y hy;obtain⟨r,hr,rfl⟩:=cC.mp S;obtain⟨e,K,rfl⟩:=cC.mp hy;exact hK (br r hr) (ab e (bf e K))}};{have bz:d.2.length+1=mid.length+1:=(by have E:=a8.length_eq;simp only[A,aE,ft,aX] at E;omega);have cg:(i.map (fun e=>e.2.length+1)).sum=(d.2.length+1)+(j.map (fun e=>e.2.length+1)).sum:=(by rw[(a7.map (fun e=>e.2.length+1)).sum_eq,aO,eu]);have e5:B.2.length+1=(c.2.length+1)+(mid.length+1):=(by simp only[B,ai,af,dL,aX];omega);simp only[bR,ic,aO,eu] at c1 ⊢;rw[cg,bz] at c1;omega}
      have bl:fY (b.reverse++B::j):=by
       intro e K;simp only[eL,cB] at K;rcases K with E|rfl|Q
       {exact aq e (by simp[E])};{exact ax};{exact aq e (by simp[bf e Q])}
      have c2:cW (b.reverse++B::j)=b.reverse++c::i:=by
       unfold cW;rw[show (b.reverse++B::j).reverse=j.reverse++B::b by
        simp[dM]]
       rw[gZ j.reverse (B::b) [] (by simpa using a0.2.2)];simp only[g0,cR];have az:∀ p∈([V B.1]).map H,p∉j.flatMap A:=(by intro p P;exact fun cl=>ao p P ((a7.flatMap_right A).mem_iff.mpr (by simp[cl])));let M:=pre++v::mid
       have bt:∀ p∈pre.map H,p∉A d:=fun p P dn=>
        ae p (s▸P) ((a7.flatMap_right A).mem_iff.mpr (by simp[dn]))
       have am:(M.map H).Nodup:=(by simp only[M,bR,fu];refine⟨s▸bi,c0,fun p be q bd cu=>?_⟩;exact bt p be (a8.mem_iff.mp (cu▸bd)))
       have ar:∀ p∈M.map H,p∉j.flatMap A:=by
        intro p P cl;simp only[M,bR,eL] at P;rcases P with be|bd
        {exact ae p (s▸be) ((a7.flatMap_right A).mem_iff.mpr (by simp[cl]))};{exact bo p (a8.mem_iff.mp bd) cl}
       have ag:H v∈M.map H:=(by simp[M]);have bh:eP (j.flatMap A) [V B.1] B.2=some (M,v,suf):=(by rw[f1 _ _ _ ay az];refine⟨b8++v::mid,by simp[M,s],by simp[B,ai,dM],by simpa[M,s,B] using am,by simpa[M,s,B] using ar,Or.inl (by simpa[M,s,B] using ag)⟩);have cp:fQ (H v) [] M=some (pre,v,mid):=(eO (H v) am pre v mid).mpr ⟨rfl,rfl⟩
       have de:iA (v::mid) (ib v mid)=d:=by
        have cx:iE (v::mid)=d.1.val:=by
         apply sY;{have dr:d.1.val∈(v::mid).map H:=a8.mem_iff.mpr (by simp[A,aE,bK]);obtain⟨x,S,co⟩:=cC.mp dr;rw[<- co];exact rj S}
         ·
          obtain⟨x,S,co⟩:=cC.mp (lS (ib v mid));rw[<- co];have dt:H x∈A d:=a8.mem_iff.mp (j1 S);simp only[A,aE,aO,cB,bK] at dt;rcases dt with bn|hm
          {omega};{obtain⟨y,hy,hyp⟩:=cC.mp hm;have e3:=a9.1 d bx y hy;simp only[H] at hyp ⊢;omega}
        have dq:(⟨iE (v::mid),lq (ib v mid)⟩:Fin N)=d.1:=bL cx;unfold iA;dsimp only;rw[dq,<- bk,oB b7 dz (by simp[aE,bK])];have dl:eA (aE d) (V d.1)=aE d:=rm b7;rw[dl];cases d;rfl
       dsimp only[cN];rw[bh];dsimp only;rw[dP ag,cp];dsimp only;rw[dP rfl,de,lu a9.2.1 ba];congr 1;rw[hJ];refine⟨eC rfl ?_,rfl⟩;simp only[ai,af]
      have aw:b.reverse++B::j≠b.reverse++c::i:=(by intro h;have bm:=aI List.length h;have ch:i.length=j.length+1:=(by rw[a7.length_eq];simp);simp only[dL,aX,ch] at bm;omega);exact⟨c4,bl,c2,fun hc=>(b9 hc).elim,fun _=>aw⟩
lemma rg{N L:Nat}{R:Type*}[CommRing R](i:Fin (2*N)->Fin (2*N)->R)(ah:∀ a b,i b a=-i a b):∀(h e:Ls (Cw N)),er L (h.reverse++e)->fY (h.reverse++e)->jK e->¬bO (h.reverse++e)->bJ i (cN h e)=-bJ i (h.reverse++e):=by
 intro h;induction h with
 | nil=>intro e _ _ x M;exact (M x.2.2).elim
 | cons c a9 ih=>
   intro e bd b0 x M;have ar:(c::a9).reverse++e=a9.reverse++c::e:=(by simp[dM]);rw[ar] at bd b0 M ⊢;obtain⟨ak,b7,bc⟩:=bd;have a1:=md (by simpa[bR] using b7);have a2:ko c:=ak c (by simp);have a6:∀ d∈e,c.1<d.1:=fun d hd=>a1.2.1 d.1 (j1 hd);have af:(([V c.1]).map H).Nodup:=(by simp);have a3:∀ p∈([V c.1]).map H,p∉e.flatMap A:=(by intro p hp;simp only[aO,fC,cB,not_mem_nil,or_false,bK] at hp;subst hp;exact gQ x.1 a6);cases hsfh:eP (e.flatMap A) [V c.1] c.2 with
   | none=>
     have av:=(iF _ _ _ af a3).mp hsfh
     have b3:jK (c::e):=by
      refine⟨fun d hd=>?_,?_,?_⟩
      · rcases cB.mp hd with rfl|bj;exact a2;exact x.1 d bj
      {simp only[aO,jE];exact⟨a1.2.1,x.2.1⟩}
      ·
       simp only[eY,fu];refine⟨by simpa[A,aE] using av.1,x.2.2,fun p ba q b8 bg=>?_⟩;subst bg;simp only[A,aE,aO,cB,bK] at ba;rcases ba with rfl|b9
       {exact gQ x.1 a6 b8};{exact av.2 p b9 b8}
     simpa only[cN,hsfh] using ih (c::e) ⟨ak,b7,bc⟩ b0 b3 M
   | some r=>
     rcases r with ⟨pre,v,suf⟩
     obtain⟨aa,o,a7,ab,_,ap⟩:=(f1 _ _ _ af a3 pre v suf).mp hsfh;simp only[pc,qO,gl,sw] at o ab ap;have ai:pre.tail=aa:=(by rw[o];rfl);by_cases s:H v∈pre.map H
     ·
      obtain⟨K,u,mid,Q⟩:=ie (H v) s;have a5:(pre.map H).Nodup:=o▸ab;have j:=(eO (H v) a5 K u mid).mp Q;have bf:c.1.val<H v:=(by have:=a2 v (by rw[a7];simp);simp only[H];omega);have am:K≠[]:=(by intro bb;rw[bb,gl] at j;have E:=o.symm.trans j.1;simp only[hJ] at E;have bi:H u=c.1.val:=(by rw[<- E.1,bK]);omega);obtain⟨x0,w,z⟩:=List.exists_cons_of_ne_nil am;have ax:x0=V c.1/\aa=w++u::mid:=(by have E:=o.symm.trans j.1;rw[z,fB,hJ] at E;exact⟨E.1.symm,E.2⟩);have y:K.tail=w:=(by rw[z];rfl);have a0:c.2=w++u::(mid++v::suf):=(by rw[a7,ax.2,dM,fB]);by_cases S:v=u
      ·
       subst S;let B:Cw N:=(c.1,K.tail++v::suf);let d:=iA (v::mid) (ib v mid);have b6:((v::mid).map H).Nodup:=(by have P:((K++v::mid).map H).Nodup:=j.1▸a5;exact (fu.mp (by simpa[bR] using P)).2.1);have aj:bQ i d=ff i (v::mid):=(by rw[kV];change ff i (aE d)=ff i (v::mid);rw[i9 (ib v mid) b6];exact nn i ah (v::mid) _);have al:bQ i B*bQ i d=-bQ i c:=(by rw[aj];simp only[bQ,ff,B,y,a0,iH];ring);have au:bJ i (eH d e)=bQ i d*bJ i e:=(by unfold bJ;rw[((es d e).map (bQ i)).prod_eq,aO,iS]);simp only[cN,hsfh,s,↓reduceIte,Q];simp only[bJ,bR,nO,aO,iS];change _*(bQ i B*bJ i (eH d e))=-(_*(bQ i c*bJ i e));rw[au];have:bQ i B*(bQ i d*bJ i e)=(bQ i B*bQ i d)*bJ i e:=by ring
       rw[this,al];ring
      {have be:v=aA u:=(cI j.2.symm).resolve_left S;let az:=mid.reverse.map aA;let B:Cw N:=(c.1,K.tail++u::az++v::suf);have a8:bQ i B=-bQ i c:=(by simp only[bQ,B,y,a0,dM,fB,iH,az,be,nr i ah];ring);simp only[cN,hsfh,s,↓reduceIte,Q,S];simp only[bJ,bR,nO,aO,iS];change _*(bQ i B*_)=-(_*(bQ i c*_));rw[a8];ring}
     {have b2:H v∈e.flatMap A:=ap.resolve_left (o▸s);obtain⟨d,ag,aw⟩:=jR b2;obtain⟨bh,ad,_,_⟩:=gs aw;have b5:(A d).Nodup:=(by have P:((d::ag).flatMap A).Nodup:=(jC (ad.flatMap_right A)).mp x.2.2;exact (fu.mp (by simpa[eY] using P)).1);obtain⟨mid,ae⟩:=oA b5 bh;let B:Cw N:=(c.1,pre.tail++v::mid++v::suf);have aj:bQ i d=ff i (v::mid):=(by rw[kV];change ff i (aE d)=ff i (v::mid);rw[<- nn i ah (aE d) v,ae]);have a8:bQ i B=-(bQ i c*bQ i d):=(by rw[aj];simp only[bQ,ff,B,ai,a7,dM,fB,iH];ring);have aq:bJ i e=bQ i d*bJ i ag:=(by unfold bJ;rw[(ad.map (bQ i)).prod_eq,aO,iS]);simp only[cN,hsfh,s,↓reduceIte,aw,ae,jF];simp only[bJ,bR,nO,aO,iS];change _*(bQ i B*bJ i ag)=-(_*(bQ i c*bJ i e));rw[a8,aq];ring}
lemma qf{E R:Type*}[DecidableEq E][CommRing R](s:Ft E)(b:E->E)(w:E->R)(a0:∀ x∈s,b x∈s)(h:∀ x∈s,b (b x)=x)(Q:∀ x∈s,b x≠x)(L:∀ x∈s,w (b x)=-w x):∑ x∈s,w x=0:=by
 induction hk:s.card using Nat.strong_induction_on generalizing s with
 | ind k ih=>
   rcases s.eq_empty_or_nonempty with rfl|⟨x,B⟩
   {simp}
   ·
    let y:=b x;have K:y∈s:=a0 x B;have S:y≠x:=Q x B;let o:=(s.erase y).erase x;have d:x∉o:=Finset.notMem_erase x _;have c:y∉o:=fun hm=>Finset.notMem_erase y s (jA hm);have a4:y∈s:=K;have e:x∈s.erase y:=fL.mpr ⟨S.symm,B⟩;have a2:s=insert x (insert y o):=(by ext z;simp only[o,aV,fL];by_cases u:z=x;{subst u;simp[B]};{by_cases r:z=y;{subst r;simp[K]};{simp[u,r]}});have j:o.card<k:=(by rw[<- hk];have h1:(s.erase y).card<s.card:=Finset.card_erase_lt_of_mem K;have h2:o.card<(s.erase y).card:=Finset.card_erase_lt_of_mem e;omega);have q:∀ z∈o,b z∈o:=(by intro z v;have P:z∈s:=jA (jA v);have u:z≠x:=(fL.mp v).1;have r:z≠y:=(fL.mp (jA v)).1;refine fL.mpr ⟨fun M=>r (by rw[<- h z P,M]),fL.mpr ⟨fun M=>u (by rw[<- h z P,M,h x B]),a0 z P⟩⟩)
    have i:∑ z∈o,w z=0:=ih o.card j o q (fun z v=>h z (jA (jA v))) (fun z v=>Q z (jA (jA v))) (fun z v=>L z (jA (jA v)))
     rfl
    rw[a2,kK (by simp[S.symm,d]),kK c,i];have hw:w y=-w x:=L x B;rw[hw];ring
lemma lY{N:Nat}{R:Type*}[CommRing R](q:Fin (2*N)->Fin (2*N)->R)(x:∀ a b,q b a=-q a b)(z:∀ u,q u u=0)(c:Ls (Ls (Cw N)))(E:c.Nodup)(h:∀ e,e∈c↔er N e):(c.map (bJ q)).sum=((c.filter (fun e=>decide (bO e))).map (bJ q)).sum:=by
 classical
 have i:∀(L:Ls (Ls (Cw N))),L.Nodup->(L.map (bJ q)).sum=∑ e∈L.toFinset,bJ q e:=fun L B=>by
  induction L with|nil=>{simp}|cons a L K=>{simp only[j5] at B;simp only[aO,eu,sI,kK (dO.not.mpr B.1),K B.2]}
 rw[i c E,i _ (E.filter _)];have r:(c.filter (fun e=>decide (bO e))).toFinset=c.toFinset.filter (fun e=>bO e):=(by ext e;simp);rw[r];rw[<- Finset.sum_filter_add_sum_filter_not c.toFinset (fun e=>bO e) (bJ q)];suffices hzero:∑ e∈c.toFinset.filter (fun e=>¬bO e),bJ q e=0 by
  rw[hzero,g1]
 rw[<- Finset.sum_filter_add_sum_filter_not _ (fun e=>fY e) (bJ q)];have o:∑ e∈(c.toFinset.filter (fun e=>¬bO e)).filter (fun e=>¬fY e),bJ q e=0:=(by refine sJ fun e j=>?_;exact kG q z e (aL.mp j).2);rw[o,g1];let w:=(c.toFinset.filter (fun e=>¬bO e)).filter (fun e=>fY e);refine qf w cW (bJ q) ?_ ?_ ?_ ?_;{intro e j;simp only[w,aL,dO] at j ⊢;obtain⟨⟨M,P⟩,S⟩:=j;have d:=ja e.reverse [] (by simpa using (h e).mp M) (by simpa using S) ⟨by simp,by simp,by simp⟩;refine⟨⟨(h _).mpr d.1,?_⟩,d.2.1⟩;intro a0;have s:=ja (cW e).reverse [] (by simpa only[g0,cR,cW] using d.1) (by simpa only[g0,cR,cW] using d.2.1) ⟨by simp,by simp,by simp⟩;have Q:cW (cW e)=cW e:=(by simpa only[g0,cR,cW] using s.2.2.2.1 (by simpa only[g0,cR] using a0));have v:cW (cW e)=e:=(by simpa only[g0,cR,cW] using d.2.2.1);have y:cW e≠e:=(by simpa only[g0,cR,cW] using d.2.2.2.2 (by simpa only[g0,cR] using P));exact y (Q.symm.trans v)};{intro e j;simp only[w,aL,dO] at j;have d:=ja e.reverse [] (by simpa using (h e).mp j.1.1) (by simpa using j.2) ⟨by simp,by simp,by simp⟩;simpa[cW] using d.2.2.1};{intro e j;simp only[w,aL,dO] at j;have d:=ja e.reverse [] (by simpa using (h e).mp j.1.1) (by simpa using j.2) ⟨by simp,by simp,by simp⟩;simpa[cW] using d.2.2.2.2 (by simpa using j.1.2)};{intro e j;simp only[w,aL,dO] at j;simpa[cW] using rg q x e.reverse [] (by simpa using (h e).mp j.1.1) (by simpa using j.2) ⟨by simp,by simp,by simp⟩ (by simpa using j.1.2)}
lemma gP{N:Nat}(r:Fin N):V r≠aZ r:=by intro h;have:=aI Fin.val h;simp[V,aZ] at this
lemma h8{N:Nat}:Injective (V (N:=N)):=fun _ _ h=>
 bL (by have:=aI Fin.val h;simp[V] at this;omega)
lemma jm{N:Nat}:Injective (aZ (N:=N)):=fun _ _ h=>
 bL (by have:=aI Fin.val h;simp[aZ] at this;omega)
lemma bZ{N:Nat}(r s:Fin N):V r≠aZ s:=by intro h;have:=aI Fin.val h;simp[V,aZ] at this;omega
def gf{m:Nat}(b:Pm (Fin m)):Nat:=((univ ×ˢ univ).filter (fun p:Fin m×Fin m=>p.1<p.2/\b p.2<b p.1)).card
lemma vX(m:Nat):gf (1:Pm (Fin m))=0:=by rw[gf,card_eq_zero,uN];intro p _;simp only[sF,not_and];intro c b;exact jH _ (hK c b)
lemma kE{m:Nat}(d:Pm (Fin m)){a b:Fin m}(v:a<b):(gf (d*swap a b)+gf d) % 2=1:=by
 let K:=(univ ×ˢ univ).filter (fun p:Fin m×Fin m=>p.1<p.2);let I (σ:Pm (Fin m)) (p:Fin m×Fin m):Nat:=if σ p.2<σ p.1 then 1 else 0;have af:∀ σ:Pm (Fin m),gf σ=∑ p∈K,I σ p:=(by intro σ;unfold gf K I;rw[<- card_filter,filter_filter]);rw[af,af,<- sB];let σ:=d*swap a b;have q:∀ p∈K,p.1≠a->p.1≠b->p.2≠a->p.2≠b->(I σ p+I d p) % 2=0:=(by intro p _ x w ab aa;have ao:σ p.1=d p.1:=(by simp[σ,fp x w]);have an:σ p.2=d p.2:=(by simp[σ,fp ab aa]);simp only[I,ao,an];split_ifs <;> omega);have a7:(a,b)∈K:=aL.mpr ⟨cX.mpr ⟨dN _,dN _⟩,v⟩
 have a6:I σ (a,b)+I d (a,b)=1:=by
  have j:σ a=d b:=(by simp[σ]);have i:σ b=d a:=(by simp[σ]);have a1:d a≠d b:=fun h=>bS v (d.injective h);simp only[I,j,i];rcases iR a1 with h|h
  {simp[h,e7 h]};{simp[h,e7 h]}
 let M:=K.filter (fun p=>p.1≠a/\p.1≠b/\p.2≠a/\p.2≠b);let B:=K.filter (fun p=>(p.1=a\/p.1=b\/p.2=a\/p.2=b)/\p≠(a,b));have ai:K=insert (a,b) (M ∪ B):=(by ext p;simp only[aV,cD,M,B,aL];constructor;{intro E;by_cases ar:p=(a,b);{exact Or.inl ar};{right;by_cases r:p.1≠a/\p.1≠b/\p.2≠a/\p.2≠b;{exact Or.inl ⟨E,r⟩};{exact Or.inr ⟨E,by tauto,ar⟩}}};{rintro (rfl|⟨E,_⟩|⟨E,_⟩);{exact a7};{exact E};{exact E}})
 have a5:(a,b)∉M ∪ B:=by
  intro h;simp only[cD,M,B,aL] at h;rcases h with ⟨_,r,_⟩|⟨_,_,a1⟩
  {exact r rfl};{exact a1 rfl}
 have au:Disjoint M B:=(by rw[aT];intro p r S;simp only[M,B,aL] at r S;tauto);rw[ai,kK a5,sT au,a6]
 have al:(∑ p∈M,(I σ p+I d p)) % 2=0:=by
  rw[lB];have:∀ p∈M,(I σ p+I d p) % 2=0:=fun p E=>by
   have a3:=aL.mp E;exact q p a3.1 a3.2.1 a3.2.2.1 a3.2.2.2.1 a3.2.2.2.2
  rw[dB rfl this];simp
 let c (p:Fin m×Fin m):Fin m:=if p.1=a\/p.1=b then p.2 else p.1;let aw:=(univ:Ft (Fin m)).filter (fun z=>z≠a/\z≠b)
 have ak:(∑ p∈B,(I σ p+I d p)) % 2=0:=by
  have aq:∑ p∈B,(I σ p+I d p)=∑ z∈aw,∑ p∈B.filter (fun p=>c p=z),(I σ p+I d p):=by
   rw[<- sum_fiberwise_of_maps_to (g:=c)];intro p E;simp only[B,K,aw,aL,cX,dN,fR,c] at E ⊢;obtain⟨e,y,a1⟩:=E;split_ifs with r
   ·
    rcases r with x|w
    {refine⟨fun h=>bS e (x.trans h.symm),fun h=>a1 (eC x h)⟩};{refine⟨fun h=>e7 v (w▸h▸e),fun h=>bS e (w.trans h.symm)⟩}
   {push_neg at r;exact r}
  rw[aq,lB]
  have av:∀ z∈aw,(∑ p∈B.filter (fun p=>c p=z),(I σ p+I d p)) % 2=0:=by
   intro z hz;obtain⟨o,s⟩:=(aL.mp hz).2;let Q:Fin m×Fin m:=if z<a then (z,a) else (a,z);let P:Fin m×Fin m:=if z<b then (z,b) else (b,z)
   have u:Q≠P:=by
    intro h;simp only[Q,P] at h;split_ifs at h with r S S
    {exact bS v (aI Prod.snd h)};{exact s (aI Prod.fst h)};{exact o (aI Prod.fst h).symm};{exact bS v (aI Prod.fst h)}
   have ap:B.filter (fun p=>c p=z)={Q,P}:=by
    ext p;simp only[aL,B,K,cX,dN,fR,aV,bI];constructor
    ·
     rintro⟨⟨e,y,a1⟩,L⟩;simp only[c] at L;split_ifs at L with r
     ·
      subst L;rcases r with x|w
      {left;simp only[Q,e7 (x▸e),↓reduceIte];exact eC x rfl};{right;simp only[P,e7 (w▸e),↓reduceIte];exact eC w rfl}
     ·
      push_neg at r;subst L;rcases y with h|h|ab|aa
      {exact (r.1 h).elim};{exact (r.2 h).elim};{left;simp only[Q,ab▸e,↓reduceIte];exact eC rfl ab};{right;simp only[P,aa▸e,↓reduceIte];exact eC rfl aa}
    ·
     rintro (rfl|rfl)
     ·
      simp only[Q];split_ifs with e
      {exact⟨⟨e,Or.inr (Or.inr (Or.inl rfl)),fun h=>o (aI Prod.fst h)⟩,by simp[c,o,s]⟩};{have aj:a<z:=qS (not_lt.mp e) o.symm;exact⟨⟨aj,Or.inl rfl,fun h=>s (aI Prod.snd h)⟩,by simp[c]⟩}
     ·
      simp only[P];split_ifs with e
      {exact⟨⟨e,Or.inr (Or.inr (Or.inr rfl)),fun h=>o (aI Prod.fst h)⟩,by simp[c,o,s]⟩};{have aj:b<z:=qS (not_lt.mp e) s.symm;exact⟨⟨aj,Or.inr (Or.inl rfl),fun h=>bS v (aI Prod.fst h).symm⟩,by simp[c]⟩}
   rw[ap,Finset.sum_pair u];have j:σ a=d b:=(by simp[σ]);have i:σ b=d a:=(by simp[σ]);have a2:σ z=d z:=(by simp[σ,fp o s]);have a9:d z≠d a:=fun h=>o (d.injective h);have a8:d z≠d b:=fun h=>s (d.injective h);simp only[Q,P];split_ifs with r S S
   {simp only[I,j,i,a2];split_ifs <;> omega};{exfalso;exact S (hK r v)}
   ·
    simp only[I,j,i,a2];rcases iR a9 with hA|hA <;> rcases iR a8 with hB|hB <;>
     simp[hA,hB,e7]
   {simp only[I,j,i,a2];split_ifs <;> omega}
  rw[dB rfl av];simp
 change (1+((∑ p∈M,(I σ p+I d p))+(∑ p∈B,(I σ p+I d p)))) % 2=1;omega
lemma m5{m:Nat}(o:Pm (Fin m)):Equiv.Perm.sign o=(-1:Intˣ)^gf o:=by
 induction o using Equiv.Perm.swap_induction_on with
 | one=>rw[map_one,vX,pow_zero]
 | swap_mul σ a b e z=>
   have i:swap a b * σ=σ * swap (σ.symm a) (σ.symm b):=(by ext x;simp only[eK];by_cases w:x=σ.symm a;{subst w;simp};{by_cases u:x=σ.symm b;{subst u;simp};{have v:σ x≠a:=fun h=>w (by rw[<- h,uY]);have s:σ x≠b:=fun h=>u (by rw[<- h,uY]);simp[fp w u,fp v s]}});have d:σ.symm a≠σ.symm b:=fun h=>e (σ.symm.injective h)
   have y:(gf (swap a b * σ)+gf σ) % 2=1:=by
    rw[i];rcases iR d with q|r
    {exact kE σ q};{rw[Equiv.swap_comm];exact kE σ r}
   rw[kR,pd e,z];have j:(gf (swap a b * σ)) % 2=(gf σ+1) % 2:=(by omega)
   have c:∀ n:Nat,(-1:Intˣ)^n=(-1:Intˣ)^(n % 2):=fun n=>by
    conv_lhs=>rw[<- qR n 2,j8,pow_mul]
    simp
   rw[c (gf (swap a b * σ)),j,<- c,gN,kP]
def fj{N:Nat}{R:Type*}[CommRing R](c:Fin (2*N)->Fin (2*N)->R)(b:Pm (Fin (2*N))):R:=((Equiv.Perm.sign b:Int):R) * ∏ r:Fin N,c (b (V r)) (b (aZ r))
lemma nA{N:Nat}{R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(e:∀ a b,d b a=-d a b)(c:Pm (Fin (2*N)))(r:Fin N):fj d (c*swap (V r) (aZ r))=fj d c:=by unfold fj;rw[kR,pd (gP r)];have q:∏ j:Fin N,d ((c*swap (V r) (aZ r)) (V j)) ((c*swap (V r) (aZ r)) (aZ j))=-∏ j:Fin N,d (c (V j)) (c (aZ j)):=(by rw[<- Finset.mul_prod_erase univ _ (dN r),<- Finset.mul_prod_erase univ _ (dN r)];have i:d ((c*swap (V r) (aZ r)) (V r)) ((c*swap (V r) (aZ r)) (aZ r))=-d (c (V r)) (c (aZ r)):=(by simp only[eK,Equiv.swap_apply_left,Equiv.swap_apply_right];exact e _ _);have o:∏ j∈univ.erase r,d ((c*swap (V r) (aZ r)) (V j)) ((c*swap (V r) (aZ r)) (aZ j))=∏ j∈univ.erase r,d (c (V j)) (c (aZ j)):=(by refine qN rfl fun j u=>?_;have s:j≠r:=(fL.mp u).1;have y:V j≠V r:=fun h=>s (h8 h);have x:V j≠aZ r:=bZ j r;have w:aZ j≠V r:=(bZ r j).symm;have v:aZ j≠aZ r:=fun h=>s (jm h);simp[eK,fp y x,fp w v]);rw[i,o];ring);rw[q];push_cast;ring
def ny{N:Nat}(b:Pm (Fin N))(v:Fin (2*N)):Fin (2*N):=⟨2*(b ⟨v.val / 2,by omega⟩).val+v.val % 2,by
 have:=(b ⟨v.val / 2,by omega⟩).isLt;omega⟩
def gp{N:Nat}(b:Pm (Fin N)):Pm (Fin (2*N)) where
 toFun:=ny b
 invFun:=ny b.symm
 left_inv v:=by apply bL;simp only[ny];have e:(2*(b ⟨v.val / 2,by omega⟩).val+v.val % 2) / 2=(b ⟨v.val / 2,by omega⟩).val:=(by omega);have c:(2*(b ⟨v.val / 2,by omega⟩).val+v.val % 2) % 2=v.val % 2:=(by omega);have d:(⟨(2*(b ⟨v.val / 2,by omega⟩).val+v.val % 2) / 2,by omega⟩:Fin N)=b ⟨v.val / 2,by omega⟩:=bL e;rw[d,uY,c];dsimp only;omega
 right_inv v:=by apply bL;simp only[ny];have e:(2*(b.symm ⟨v.val / 2,by omega⟩).val+v.val % 2) / 2=(b.symm ⟨v.val / 2,by omega⟩).val:=(by omega);have c:(2*(b.symm ⟨v.val / 2,by omega⟩).val+v.val % 2) % 2=v.val % 2:=(by omega);have d:(⟨(2*(b.symm ⟨v.val / 2,by omega⟩).val+v.val % 2) / 2,by omega⟩:Fin N)=b.symm ⟨v.val / 2,by omega⟩:=bL e;rw[d,uZ,c];dsimp only;omega
lemma eI{N:Nat}(b:Pm (Fin N))(r:Fin N):gp b (V r)=V (b r):=by apply bL;change 2*(b ⟨(2*r.val) / 2,by omega⟩).val+(2*r.val) % 2=2*(b r).val;have c:(⟨(2*r.val) / 2,by omega⟩:Fin N)=r:=fE (by dsimp only;omega);rw[c];omega
lemma fW{N:Nat}(b:Pm (Fin N))(r:Fin N):gp b (aZ r)=aZ (b r):=by apply bL;change 2*(b ⟨(2*r.val+1) / 2,by omega⟩).val+(2*r.val+1) % 2=2*(b r).val+1;have c:(⟨(2*r.val+1) / 2,by omega⟩:Fin N)=r:=fE (by dsimp only;omega);rw[c];omega
lemma tg{N:Nat}(c b:Pm (Fin N)):gp (c*b)=gp c*gp b:=by apply Equiv.ext;intro v;by_cases e:v.val % 2=0;{let r:Fin N:=⟨v.val / 2,by omega⟩;have d:v=V r:=bL (by simp[V,r];omega);rw[d,eI,eK,eK,eI,eI]};{let r:Fin N:=⟨v.val / 2,by omega⟩;have d:v=aZ r:=bL (by simp[aZ,r];omega);rw[d,fW,eK,eK,fW,fW]}
lemma sa{N:Nat}(a b:Fin N):gp (swap a b)=swap (V a) (V b)*swap (aZ a) (aZ b):=by apply Equiv.ext;intro v;by_cases i:v.val % 2=0;{let r:Fin N:=⟨v.val / 2,by omega⟩;have e:v=V r:=bL (by simp[V,r];omega);rw[e,eI,eK,fp (bZ r a) (bZ r b)];by_cases d:r=a;{subst d;simp};{by_cases c:r=b;{subst c;simp};{simp[fp d c,fp (fun h=>d (h8 h)) (fun h=>c (h8 h))]}}};{let r:Fin N:=⟨v.val / 2,by omega⟩;have e:v=aZ r:=bL (by simp[aZ,r];omega);rw[e,fW,eK];by_cases d:r=a;{subst d;simp[fp (bZ r b).symm (bZ b b).symm]};{by_cases c:r=b;{subst c;simp[fp (bZ a a).symm (bZ r a).symm]};{simp[fp d c,fp (fun h=>d (jm h)) (fun h=>c (jm h)),fp (bZ a r).symm (bZ b r).symm]}}}
lemma oG{N:Nat}(d:Pm (Fin N)):Equiv.Perm.sign (gp d)=1:=by induction d using Equiv.Perm.swap_induction_on with|one=>{have i:gp (1:Pm (Fin N))=1:=(by apply Equiv.ext;intro v;apply bL;change 2*(v.val / 2)+v.val % 2=v.val;omega);rw[i,map_one]}|swap_mul σ a b c e=>{rw[tg,sa,kR,kR,pd (fun h=>c (h8 h)),pd (fun h=>c (jm h)),e];decide}
lemma mq{N:Nat}{R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(c:Pm (Fin (2*N)))(b:Pm (Fin N)):fj d (c*gp b)=fj d c:=by unfold fj;rw[kR,oG,kQ];congr 1;simp only[eK,eI,fW];exact Fintype.prod_equiv b _ _ (fun _=>rfl)
lemma pS{N:Nat}{R:Type*}[CommRing R](E:Fin (2*N)->Fin (2*N)->R)(b2:∀ a b,E b a=-E a b)(z:Ft (Fin (2*N)×Fin (2*N)))(av:aQ z/\z.biUnion aF=univ)(π:Pm (Fin (2*N)))(aq:∀ r:Fin N,(π (V r),π (aZ r))∈z\/(π (aZ r),π (V r))∈z):fj E π=(-1:R)^cr z * ∏ e∈z,E e.1 e.2:=by
 have a6:∀(bm:Ft (Fin N)) (σ:Pm (Fin (2*N))),(∀ r:Fin N,(σ (V r),σ (aZ r))∈z\/(σ (aZ r),σ (V r))∈z)->(∀ r∉bm,(σ (V r),σ (aZ r))∈z)->∃ ag:Pm (Fin (2*N)),fj E ag=fj E σ/\∀ r:Fin N,(ag (V r),ag (aZ r))∈z:=by
  intro bm;induction bm using qK with
  | empty=>intro σ _ h;exact⟨σ,rfl,fun r=>h r (sG r)⟩
  | @insert r bm hr ih=>
    intro σ hm ax;by_cases bb:(σ (V r),σ (aZ r))∈z;{refine ih σ hm fun j hj=>?_;by_cases K:j=r;{exact K▸bb};{exact ax j (fun b5=>hj (Finset.mem_of_mem_insert_of_ne b5 K))}}
    ·
     have aw:(σ (aZ r),σ (V r))∈z:=(hm r).resolve_left bb;let d:=σ * swap (V r) (aZ r);have bq:∀ j:Fin N,(d (V j),d (aZ j))∈z\/(d (aZ j),d (V j))∈z:=(by intro j;by_cases K:j=r;{subst K;left;simpa[d] using aw};{have B:V j≠V r:=fun h=>K (h8 h);have S:V j≠aZ r:=bZ j r;have h3:aZ j≠V r:=(bZ r j).symm;have h4:aZ j≠aZ r:=fun h=>K (jm h);simpa[d,eK,fp B S,fp h3 h4] using hm j})
     have b3:∀ j∉bm,(d (V j),d (aZ j))∈z:=by
      intro j hj;by_cases K:j=r;{subst K;simpa[d] using aw}
      ·
       have B:V j≠V r:=fun h=>K (h8 h);have S:V j≠aZ r:=bZ j r;have h3:aZ j≠V r:=(bZ r j).symm;have h4:aZ j≠aZ r:=fun h=>K (jm h);simpa[d,eK,fp B S,fp h3 h4]
        using ax j (fun b5=>hj (Finset.mem_of_mem_insert_of_ne b5 K))
     obtain⟨ag,bg,bj⟩:=ih d bq b3;exact⟨ag,bg.trans (nA E b2 σ r),bj⟩
 obtain⟨d,aj,a9⟩:=a6 univ π aq (fun _ h=>(h (dN _)).elim);let w:Ft (Fin (2*N)):=univ.image (fun r:Fin N=>d (V r));have ad:Injective (fun r:Fin N=>d (V r)):=fun a b h=>h8 (d.injective h);have a1:w.card=N:=(by rw[o6 _ ad,pv,pq]);let a8:=w.orderEmbOfFin a1
 have ak:∀ r:Fin N,∃ s:Fin N,d (V s)=a8 r:=fun r=>by
  have hm:a8 r∈w:=uQ w a1 r;obtain⟨s,_,hs⟩:=mem_image.mp hm;exact⟨s,hs⟩
 let a7:Fin N->Fin N:=fun r=>Classical.choose (ak r);have u:∀ r:Fin N,d (V (a7 r))=a8 r:=fun r=>f9 (ak r)
 have ah:Injective a7:=fun r1 r2 h=>
  a8.injective ((u r1).symm.trans (by rw[h];exact u r2))
 let τ:Pm (Fin N):=Equiv.ofBijective a7 (Finite.injective_iff_bijective.mp ah);let c:Pm (Fin (2*N)):=d*gp τ;have ai:fj E c=fj E π:=(mq E d τ).trans aj
 have a2:∀ r:Fin N,(c (V r),c (aZ r))∈z:=fun r=>by
  simpa[c,eK,eI,fW] using a9 (τ r)
 have L:∀ r:Fin N,c (V r)<c (aZ r):=fun r=>av.1.1 _ (a2 r)
 have a3:∀ r s:Fin N,r<s->c (V r)<c (V s):=fun r s Q=>by
  have hr:c (V r)=a8 r:=(by simpa[c,eK,eI,τ] using u r);have hs:c (V s)=a8 s:=(by simpa[c,eK,eI,τ] using u s);rw[hr,hs];exact a8.lt_iff_lt.mpr Q
 have an:z.card=N:=(by have S:(z.biUnion aF).card=2*z.card:=(by rw[sH (fun e he f hf bp=>av.1.2 e he f hf bp)];have bv:∀ e∈z,(aF e).card=2:=fun e he=>lC (bS (av.1.1 e he));rw[dB rfl bv,qP,n0,kP]);rw[av.2,pv,pq] at S;omega);let o (r:Fin N):Fin (2*N)×Fin (2*N):=(c (V r),c (aZ r));have i:Injective o:=fun r s h=>h8 (c.injective (aI Prod.fst h));have am:univ.image o=z:=(by refine nH ?_ ?_;{intro e he;obtain⟨r,_,rfl⟩:=mem_image.mp he;exact a2 r};{rw[o6 _ i,pv,pq,an]});have aa:∏ r:Fin N,E (c (V r)) (c (aZ r))=∏ e∈z,E e.1 e.2:=(by rw[<- am,Finset.prod_image (fun a _ b _ h=>i h)])
 have ar:gf c % 2=cr z % 2:=by
  have ab:gf c=∑ r:Fin N,∑ s∈univ.filter (fun s:Fin N=>r<s),((if c (V s)<c (V r) then 1 else 0)+(if c (aZ s)<c (V r) then 1 else 0)+(if c (V s)<c (aZ r) then 1 else 0)+(if c (aZ s)<c (aZ r) then 1 else 0)):=by
   let b0:=(univ ×ˢ univ).filter (fun p:Fin (2*N)×Fin (2*N)=>p.1<p.2/\c p.2<c p.1);let v (p:Fin (2*N)×Fin (2*N)):Fin N×Fin N:=(⟨p.1.val / 2,by omega⟩,⟨p.2.val / 2,by omega⟩);let T:=(univ ×ˢ univ).filter (fun q:Fin N×Fin N=>q.1<q.2);have b4:∀ p∈b0,v p∈T:=(by intro p hp;simp only[b0,aL,cX,dN,fR] at hp;simp only[T,v,aL,cX,dN,fR,iU];have c5:p.1.val / 2<=p.2.val / 2:=Nat.div_le_div_right hp.1.le;by_contra ay;have c7:p.1.val / 2=p.2.val / 2:=(by omega);let r:Fin N:=⟨p.1.val / 2,by omega⟩;have B:p.1=V r:=bL (by simp[V,r];omega);have S:p.2=aZ r:=bL (by simp[aZ,r];omega);rw[B,S] at hp;exact pC (L r) hp.2);have au:b0.card=∑ q∈T,(b0.filter (fun p=>v p=q)).card:=card_eq_sum_card_fiberwise b4
   have bf:∀ q∈T,(b0.filter (fun p=>v p=q)).card=(if c (V q.2)<c (V q.1) then 1 else 0)+(if c (aZ q.2)<c (V q.1) then 1 else 0)+(if c (V q.2)<c (aZ q.1) then 1 else 0)+(if c (aZ q.2)<c (aZ q.1) then 1 else 0):=by
    intro⟨r,s⟩ hq;have Q:r<s:=(aL.mp hq).2
    let S4:Ft (Fin (2*N)×Fin (2*N)):=
     {(V r,V s),(V r,aZ s),(aZ r,V s),(aZ r,aZ s)}
    have b9:b0.filter (fun p=>v p=(r,s))=S4.filter (fun p=>c p.2<c p.1):=by
     ext⟨x,y⟩;simp only[b0,S4,v,aL,cX,dN,fR,aV,bI,gL,Fin.ext_iff];constructor;{rintro⟨⟨_,a4⟩,P,M⟩;refine⟨?_,a4⟩;by_cases c4:x.val % 2=0 <;> by_cases hyp:y.val % 2=0;{left;exact⟨by simp[V];omega,by simp[V];omega⟩};{right;left;exact⟨by simp[V];omega,by simp[aZ];omega⟩};{right;right;left;exact⟨by simp[aZ];omega,by simp[V];omega⟩};{right;right;right;exact⟨by simp[aZ];omega,by simp[aZ];omega⟩}}
     ·
      rintro⟨(⟨P,M⟩|⟨P,M⟩|⟨P,M⟩|⟨P,M⟩),a4⟩ <;>
       simp only[V,aZ] at P M
      {exact⟨⟨by rw[iU,P,M];omega,a4⟩,by omega,by omega⟩};{exact⟨⟨by rw[iU,P,M];omega,a4⟩,by omega,by omega⟩};{exact⟨⟨by rw[iU,P,M];omega,a4⟩,by omega,by omega⟩};{exact⟨⟨by rw[iU,P,M];omega,a4⟩,by omega,by omega⟩}
    rw[b9];have bz:(V r,V s)≠(V r,aZ s):=fun h=>gP s (aI Prod.snd h);have bx:(V r,V s)≠(aZ r,V s):=fun h=>gP r (aI Prod.fst h);have bw:(V r,V s)≠(aZ r,aZ s):=fun h=>gP r (aI Prod.fst h);have bu:(V r,aZ s)≠(aZ r,V s):=fun h=>gP r (aI Prod.fst h);have bt:(V r,aZ s)≠(aZ r,aZ s):=fun h=>gP r (aI Prod.fst h);have bs:(aZ r,V s)≠(aZ r,aZ s):=fun h=>gP s (aI Prod.snd h);simp only[S4,Finset.filter_insert,Finset.filter_singleton];split_ifs <;> simp[bz,bx,bw,bu,bt,bs] <;> omega
   rw[show gf c=b0.card from rfl,au,dB rfl bf];simp only[T,sO,Finset.sum_product]
  have al:cr z=∑ r:Fin N,∑ s∈univ.filter (fun s:Fin N=>r<s),if eS (o r) (o s) then 1 else 0:=by
   unfold cr;rw[<- am,card_filter,Finset.sum_product,sU (fun a _ b _ h=>i h)];refine dB rfl fun r _=>?_;rw[sU (fun a _ b _ h=>i h),sO];refine dB rfl fun s _=>?_;by_cases Q:r<s;{simp[Q]}
   ·
    simp only[Q,↓reduceIte]
    have ay:¬eS (o r) (o s):=fun hc=>by
     have B:c (V r)<c (V s):=hc.1;rcases qT r s with h|rfl|h
     {exact Q h};{exact jH _ B};{exact pC B (a3 s r h)}
    simp[ay]
  rw[ab,al];conv_lhs=>rw[lB]
  conv_rhs=>rw[lB]
  congr 1;refine dB rfl fun r _=>?_;conv_lhs=>rw[lB]
  conv_rhs=>rw[lB]
  congr 1;refine dB rfl fun s hs=>?_;have Q:r<s:=(aL.mp hs).2;have B:c (V r)<c (V s):=a3 r s Q;have S:c (V r)<c (aZ r):=L r;have h3:c (V s)<c (aZ s):=L s;have h4:c (V r)<c (aZ s):=hK B h3;have bd:c (aZ r)≠c (V s):=fun h=>bZ s r (c.injective h.symm);have bc:c (aZ r)≠c (aZ s):=fun h=>bS Q (jm (c.injective h));simp only[o,eS,e7 B,e7 h4,↓reduceIte,B,fR];rcases iR bd with ha|ha <;> rcases iR bc with hb|hb
  {simp[ha,hb,e7]};{exact absurd (hK ha h3) (pC hb)};{simp[ha,hb,e7]};{simp[ha,hb,e7]}
 rw[<- ai,fj,aa,m5]
 have b6:((((-1:Intˣ)^gf c:Intˣ):Int):R)=(-1:R)^gf c:=by induction gf c with|zero=>{simp}|succ k ih=>{rw[gN,gN];push_cast;rfl}
 rw[b6,gC ar]
lemma mC{N:Nat}{b:Ft (Fin (2*N)×Fin (2*N))}:b∈PM N↔aQ b/\b.biUnion aF=univ:=g4
def iN{m:Nat}(a:Nat):Nat->Pm (Fin m)
 | 0=>1
 | d+1=>
   if h:a+d+1< m then iN a d*swap ⟨a+d,by omega⟩ ⟨a+d+1,h⟩
   else iN a d
lemma vJ{m:Nat}(a d:Nat)(h:a+d< m):Equiv.Perm.sign (iN (m:=m) a d)=(-1:Intˣ)^d:=by
 induction d with
 | zero=>simp[iN]
 | succ d e=>
   unfold iN;rw[cT (by omega),kR,e (by omega)]
   have b:(⟨a+d,by omega⟩:Fin m)≠⟨a+d+1,by omega⟩:=fun c=>by
    have:=congrArg Fin.val c;dsimp only at this;omega
   rw[pd b,gN]
lemma k4{m:Nat}(a d:Nat)(h:a+d< m)(x:Fin m):(iN (m:=m) a d x).val=if a<=x.val/\x.val<a+d then x.val+1
 else if x.val=a+d then a
 else x.val:=by
 induction d generalizing x with|zero=>{simp only[iN,sF,Nat.add_zero];split_ifs <;> omega}|succ d i=>{unfold iN;rw[cT (by omega),eK,i (by omega)];by_cases e:x=⟨a+d,by omega⟩;{subst e;simp only[Equiv.swap_apply_left];split_ifs <;> omega};{by_cases c:x=⟨a+d+1,by omega⟩;{subst c;simp only[Equiv.swap_apply_right];split_ifs <;> omega};{rw[fp e c];have o:x.val≠a+d:=fun b=>e (bL b);have j:x.val≠a+d+1:=fun b=>c (bL b);split_ifs <;> omega}}}
def ez{N:Nat}(b:Nat):Ls Nat->Pm (Fin (2*N))
 | []=>1
 | L::Ls=>iN (2*b) (2*L-1)*ez (b+L) Ls
lemma tW{N:Nat}(b:Nat)(Ls:Ls Nat)(c:∀ L∈Ls,1<=L)(d:b+Ls.sum<=N):Equiv.Perm.sign (ez (N:=N) b Ls)=(-1:Intˣ)^Ls.length:=by induction Ls generalizing b with|nil=>{simp[ez]}|cons L Ls i=>{have o:1<=L:=c L gK;simp only[eu] at d;simp only[ez,kR,aX];rw[vJ (2*b) (2*L-1) (by omega),i (b+L) (fun x j=>c x (g9 _ j)) (by omega)];have h:(-1:Intˣ)^(2*L-1)=-1:=(by have e:2*L-1=2*(L-1)+1:=(by omega);rw[e,gN,pow_mul];simp);rw[h,pow_succ']}
lemma ow{N:Nat}(b:Nat)(Ls:Ls Nat)(c:∀ L∈Ls,1<=L)(d:b+Ls.sum<=N)(x:Fin (2*N))(i:x.val<2*b):ez (N:=N) b Ls x=x:=by induction Ls generalizing b with|nil=>{rfl}|cons L Ls e=>{have j:1<=L:=c L gK;simp only[eu] at d;simp only[ez,eK];rw[e (b+L) (fun y h=>c y (g9 _ h)) (by omega) (by omega)];apply bL;rw[k4 (2*b) (2*L-1) (by omega)];split_ifs <;> omega}
lemma ov{N:Nat}(b:Nat)(Ls:Ls Nat)(c:∀ L∈Ls,1<=L)(d:b+Ls.sum<=N)(x:Fin (2*N))(i:2*(b+Ls.sum)<=x.val):ez (N:=N) b Ls x=x:=by induction Ls generalizing b with|nil=>{rfl}|cons L Ls e=>{have j:1<=L:=c L gK;simp only[eu] at d i;simp only[ez,eK];rw[e (b+L) (fun y h=>c y (g9 _ h)) (by omega) (by omega)];apply bL;rw[k4 (2*b) (2*L-1) (by omega)];split_ifs <;> omega}
lemma sb{N:Nat}(b:Nat)(c d:Ls Nat):ez (N:=N) b (c++d)=ez b c*ez (b+c.sum) d:=by induction c generalizing b with|nil=>{simp[ez]}|cons L c e=>{simp only[fB,ez,eu,mR,e];rw[Nat.add_assoc]}
def f6{N:Nat}(b:L2 N)(d:b.length=N):Ls (Fin N)->Pm (Fin (2*N))
 | []=>1
 | r::c=>(if (b[r.val]'(by omega)).val % 2=0 then 1 else swap (V r) (aZ r))*f6 b d c
lemma tv{N:Nat}(c:L2 N)(e:c.length=N)(b:Ls (Fin N)):Equiv.Perm.sign (f6 c e b)=(b.map (fun r=>if (c[r.val]'(by omega)).val % 2=0 then (1:Intˣ) else -1)).prod:=by induction b with|nil=>{simp[f6]}|cons r b d=>{simp only[f6,kR,d,aO,iS];split_ifs <;> simp[pd (gP r)]}
lemma oK{N:Nat}(d:L2 N)(e:d.length=N)(b:Ls (Fin N))(j:Fin N)(c:j∉b):f6 d e b (V j)=V j/\f6 d e b (aZ j)=aZ j:=by induction b with|nil=>{simp[f6]}|cons r b i=>{simp only[cB,not_or] at c;obtain⟨q,o⟩:=i c.2;simp only[f6,eK,q,o];split_ifs;{exact⟨rfl,rfl⟩};{exact⟨fp (fun h=>c.1 (h8 h)) (bZ j r),fp (bZ r j).symm (fun h=>c.1 (jm h))⟩}}
lemma p6{N:Nat}(b:L2 N)(s:b.length=N)(e:Ls (Fin N))(d:e.Nodup)(j:Fin N)(w:j∈e):f6 b s e (V j)=(if (b[j.val]'(by omega)).val % 2=0 then V j else aZ j)/\f6 b s e (aZ j)=(if (b[j.val]'(by omega)).val % 2=0 then aZ j else V j):=by
 induction e with
 | nil=>simp at w
 | cons r e x=>
   simp only[j5] at d;rcases cB.mp w with rfl|o
   {obtain⟨v,u⟩:=oK b s e j d.1;simp only[f6,eK,v,u];split_ifs <;> simp}
   ·
    have c:j≠r:=fun h=>d.1 (h▸o);obtain⟨v,u⟩:=x d.2 o;simp only[f6,eK,v,u];constructor
    ·
     by_cases q:(b[r.val]'(by omega)).val % 2=0 <;> by_cases i:(b[j.val]'(by omega)).val % 2=0 <;>
      simp only[q,i,↓reduceIte,sF]
     {exact fp (fun h=>c (h8 h)) (bZ j r)};{exact fp (bZ r j).symm (fun h=>c (jm h))}
    ·
     by_cases q:(b[r.val]'(by omega)).val % 2=0 <;> by_cases i:(b[j.val]'(by omega)).val % 2=0 <;>
      simp only[q,i,↓reduceIte,sF]
     {exact fp (bZ r j).symm (fun h=>c (jm h))};{exact fp (fun h=>c (h8 h)) (bZ j r)}
lemma eT{N:Nat}(b:Ls (Cw N)):(b.flatMap aE).length=(b.map (fun c=>c.2.length+1)).sum:=by induction b with|nil=>{simp}|cons c b d=>{simp[aE,d];omega}
lemma fF{N:Nat}(b:Ls (Cw N)):(b.flatMap aE).map H=b.flatMap A:=by induction b with|nil=>{simp}|cons c b d=>{simp[A,d]}
def jN{N:Nat}(o:Ls (Cw N))(s:er N o)(j:bO o):Pm (Fin (2*N)):=
 let d:=o.flatMap aE;have u:d.length=N:=(eT o).trans s.2.2;let b:Fin N->Fin N:=fun r=>⟨H (d[r.val]'(by omega)),oC _⟩;have c:Injective b:=(by intro w v h;have e:H (d[w.val]'(by omega))=H (d[v.val]'(by omega)):=aI Fin.val h;have q:(d.map H).Nodup:=(fF o).symm▸j;have i:(d.map H)[w.val]'(by simp[u])=(d.map H)[v.val]'(by simp[u]):=(by simp only[kJ];exact e);exact bL (q.getElem_inj_iff.mp i));let x:Pm (Fin N):=Equiv.ofBijective b (Finite.injective_iff_bijective.mp c)
 gp x*f6 d u (finRange N)
def fP{N:Nat}(d:Ls (Cw N))(e:er N d)(b:bO d):Pm (Fin (2*N)):=jN d e b*ez 0 (d.map (fun c=>c.2.length+1))
lemma np{N:Nat}(h:Ls (Cw N))(e:er N h)(c:bO h)(r:Fin N):let b:=h.flatMap aE
 have j:b.length=N:=(eT h).trans e.2.2
 jN h e c (V r)=b[r.val]'(by omega)/\
 jN h e c (aZ r)=aA (b[r.val]'(by omega)):=by
 intro b j;unfold jN;dsimp only;have i:=p6 b j (finRange N) (jZ N) r (mK r);constructor;{rw[eK,i.1];by_cases d:(b[r.val]'(by omega)).val % 2=0;{rw[dP d,eI];apply bL;change 2*H (b[r.val]'(by omega))=(b[r.val]'(by omega)).val;simp only[H];omega};{rw[cM d,fW];apply bL;change 2*H (b[r.val]'(by omega))+1=(b[r.val]'(by omega)).val;simp only[H];omega}};{rw[eK,i.2];by_cases d:(b[r.val]'(by omega)).val % 2=0;{rw[dP d,fW];apply bL;change 2*H (b[r.val]'(by omega))+1=(aA (b[r.val]'(by omega))).val;simp only[H,aA,d,↓reduceIte];omega};{rw[cM d,eI];apply bL;change 2*H (b[r.val]'(by omega))=(aA (b[r.val]'(by omega))).val;simp only[H,aA,d,↓reduceIte];omega}}
lemma tw{N:Nat}{R:Type*}[CommRing R](b:Ls (Cw N))(e:er N b)(h:bO b):((Equiv.Perm.sign (fP b e h):Int):R)=(-1:R)^b.length*((b.flatMap aE).map (j0 (R:=R))).prod:=by
 let v:=b.flatMap aE;have y:v.length=N:=(eT b).trans e.2.2;have s:∀ L∈b.map (fun c=>c.2.length+1),1<=L:=(by intro L z;obtain⟨c,_,rfl⟩:=cC.mp z;omega);have q:0+(b.map (fun c=>c.2.length+1)).sum<=N:=(by rw[lE,e.2.2]);have j:Equiv.Perm.sign (ez (N:=N) 0 (b.map (fun c=>c.2.length+1)))=(-1:Intˣ)^b.length:=(by rw[tW 0 _ s q,ft]);have w:Equiv.Perm.sign (jN b e h)=((finRange N).map (fun r:Fin N=>if (v[r.val]'(by omega)).val % 2=0 then (1:Intˣ) else -1)).prod:=(by unfold jN;dsimp only;rw[kR,oG,j9,tv])
 have d:∀(L:Ls Intˣ),(((L.prod:Intˣ):Int):R)=(L.map (fun u:Intˣ=>((u:Int):R))).prod:=by
  intro L;induction L with
  | nil=>simp
  | cons u L x=>simp[x]
 unfold fP;rw[kR,w,j];push_cast;rw[d,gm,kP];congr 1;have o:v=(finRange N).map (fun r:Fin N=>v[r.val]'(by omega)):=(by apply jD;{simp[y]};{intro i E B;simp});conv_rhs=>rw[show b.flatMap aE=v from rfl,o,gm]
 congr 1;refine dF fun r _=>?_;simp only[qH,j0];split_ifs <;> simp
lemma oE{N:Nat}{R:Type*}[CommRing R](f:Fin N->R):∏ r:Fin N,f r=((finRange N).map f).prod:=by
 have h:(univ:Ft (Fin N))=(finRange N).toFinset:=(by ext r;simp);rw[h]
 have b:∀(L:Ls (Fin N)),L.Nodup->∏ r∈L.toFinset,f r=(L.map f).prod:=by
  intro L c;induction L with
  | nil=>simp
  | cons a L d=>simp only[j5] at c;simp only[sI,prod_insert (dO.not.mpr c.1),aO,iS,d c.2]
 exact b (finRange N) (jZ N)
lemma oN{N:Nat}{R:Type*}[CommRing R](q:Fin (2*N)->Fin (2*N)->R)(e:Fin (2*N))(o:L2 N)(target:Fin (2*N)):el q (aA e) o target=(o.map (j0 (R:=R))).prod*((List.range (o.length+1)).map (fun i=>let L:=e::o
 let a:=L.getD i e;let b:=if i+1<o.length+1 then L.getD (i+1) e else target
 q (aA a) b)).prod:=by
 induction o generalizing e with|nil=>{simp[el]}|cons d c u=>{simp only[el,aO,iS,aX];rw[u d];have v:List.range (c.length+1+1)=0::(List.range (c.length+1)).map Nat.succ:=List.range_succ_eq_map;rw[v,aO,iS,gm];simp only[Nat.zero_add,Nat.lt_add_left_iff_pos,Nat.zero_lt_succ,↓reduceIte,List.getD_cons_zero,List.getD_cons_succ];have j:(List.range (c.length+1)).map ((fun i=>q (aA ((e::d::c).getD i e)) (if i+1<c.length+1+1 then (d::c).getD i e else target)) ∘ Nat.succ)=(List.range (c.length+1)).map (fun i=>q (aA ((d::c).getD i d)) (if i+1<c.length+1 then c.getD i d else target)):=(by refine dF fun i x=>?_;have w:i<c.length+1:=aY.mp x;simp only[qH,Nat.succ_eq_add_one,List.getD_cons_succ];have s:(d::c).getD i e=(d::c).getD i d:=(by rw[cQ _ _ (by simp;omega),cQ _ _ (by simp;omega)]);by_cases h:i+1<c.length+1;{have y:c.getD i e=c.getD i d:=(by rw[cQ _ _ (by omega),cQ _ _ (by omega)]);have r:i+1+1<c.length+1+1:=(by omega);simp only[h,r,↓reduceIte,s,y]};{have r:¬(i+1+1<c.length+1+1):=(by omega);simp only[h,r,↓reduceIte,s]});rw[j];ring}
lemma i5{N:Nat}(u:Ls (Cw N))(h:er N u)(o:bO u)(v:Ls (Cw N))(c:Cw N)(B:Ls (Cw N))(K:u=v++c::B)(i:Nat)(hi:i<c.2.length+1):let b:=(v.map (fun x=>x.2.length+1)).sum
 have a8:b+i<N:=(by have d:=h.2.2;rw[K] at d;simp only[bR,ic,aO,eu] at d;omega);let r:Fin N:=⟨b+i,a8⟩;let L:=aE c
 fP u h o (V r)=aA (L[i]'(by simp only[L,aE,aX];omega))/\
 fP u h o (aZ r)=L[(i+1) % (c.2.length+1)]'(by simp only[L,aE,aX];exact gb _ (by omega)):=by
 intro b a8 r L;let E:=u.flatMap aE;have hV:E.length=N:=(eT u).trans h.2.2;have af:u.map (fun x=>x.2.length+1)=v.map (fun x=>x.2.length+1)++(c.2.length+1)::B.map (fun x=>x.2.length+1):=(by rw[K,bR,aO]);have y:∀ x∈v.map (fun x=>x.2.length+1),1<=x:=(by intro x P;obtain⟨a,_,rfl⟩:=cC.mp P;omega);have w:∀ x∈B.map (fun x=>x.2.length+1),1<=x:=(by intro x P;obtain⟨a,_,rfl⟩:=cC.mp P;omega);have ag:b+(c.2.length+1)+(B.map (fun x=>x.2.length+1)).sum=N:=(by have d:=h.2.2;rw[K] at d;simp only[bR,ic,aO,eu] at d;omega);have S:ez (N:=N) 0 (u.map (fun x=>x.2.length+1))=ez 0 (v.map (fun x=>x.2.length+1))*(iN (2*b) (2*(c.2.length+1)-1)*ez (b+(c.2.length+1)) (B.map (fun x=>x.2.length+1))):=(by rw[af,sb,lE,ez])
 have q:∀ j (hj:j<c.2.length+1),E[b+j]'(by omega)=L[j]'(by simp only[L,aE,aX];omega):=by
  intro j hj;have a1:E=v.flatMap aE++L++B.flatMap aE:=(by simp[E,K,L,dM]);have e:(v.flatMap aE).length=b:=eT v;have h1:(v.flatMap aE++L++B.flatMap aE)[b+j]'(by rw[<- a1];omega)=(v.flatMap aE++L)[b+j]'(by simp[e,L,aE];omega):=uI (by simp[e,L,aE];omega);have h2:(v.flatMap aE++L)[b+j]'(by simp[e,L,aE];omega)=L[j]'(by simp only[L,aE,aX];omega):=(by rw[sx (by omega)];congr 1;omega)
  calc E[b+j]'(by omega)=(v.flatMap aE++L++B.flatMap aE)[b+j]'(by rw[<- a1];omega):=by
          congr 1
   _=L[j]'(by simp only[L,aE,aX];omega):=h1.trans h2
 have Q:(V r).val=2*(b+i):=rfl;have M:(aZ r).val=2*(b+i)+1:=rfl;have a0:(i+1) % (c.2.length+1)<c.2.length+1:=gb _ (by omega);have s:ez (N:=N) 0 (u.map (fun x=>x.2.length+1)) (V r)=aZ r:=(by rw[S,eK,eK,ow _ _ w (by omega) _ (by rw[Q];omega)];have a7:iN (m:=2*N) (2*b) (2*(c.2.length+1)-1) (V r)=aZ r:=(by apply bL;rw[k4 (2*b) (2*(c.2.length+1)-1) (by omega),Q,M];split_ifs <;> omega);rw[a7];exact ov 0 _ y (by omega) _ (by rw[M];omega))
 have z:ez (N:=N) 0 (u.map (fun x=>x.2.length+1)) (aZ r)=V ⟨b+(i+1) % (c.2.length+1),by omega⟩:=by
  rw[S,eK,eK,ow _ _ w (by omega) _ (by rw[M];omega)];have a6:iN (m:=2*N) (2*b) (2*(c.2.length+1)-1) (aZ r)=V ⟨b+(i+1) % (c.2.length+1),by omega⟩:=(by apply bL;rw[k4 (2*b) (2*(c.2.length+1)-1) (by omega),M];change _=2*(b+(i+1) % (c.2.length+1));by_cases a4:i+1<c.2.length+1;{rw[mF a4];split_ifs <;> omega};{have a5:i+1=c.2.length+1:=(by omega);rw[a5,nZ];split_ifs <;> omega});rw[a6];exact ov 0 _ y (by omega) _ (by
   change 2*(0+b)<=2*(b+(i+1) % (c.2.length+1));omega)
 constructor;{unfold fP;rw[eK,s,(np u h o r).2];exact aI aA (q i hi)};{unfold fP;rw[eK,z,(np u h o _).1];exact q ((i+1) % (c.2.length+1)) a0}
lemma oL{N:Nat}{R:Type*}[CommRing R](u:Fin (2*N)->Fin (2*N)->R)(v:Ls (Cw N))(q:er N v)(o:bO v):fj u (fP v q o)=bJ u v:=by
 unfold fj;rw[tw v q o,oE];let e (r:Fin N):R:=u (fP v q o (V r)) (fP v q o (aZ r))
 have j:∀(B E:Ls (Cw N)),v=B++E->
  let a6:=(B.map (fun x=>x.2.length+1)).sum;let ad:=(E.map (fun x=>x.2.length+1)).sum
  ((List.range ad).map (fun k=>if h:a6+k<N then e ⟨a6+k,h⟩ else 1)).prod=
  (E.map (fun c=>((List.range (c.2.length+1)).map (fun i=>let L:=aE c
    u (aA (L.getD i (V c.1))) (L.getD ((i+1) % (c.2.length+1)) (V c.1)))).prod)).prod:=by
  intro B E;induction E generalizing B with
  | nil=>intro _;simp
  | cons c d K=>intro P;dsimp only;simp only[aO,eu,iS];have s:List.range (c.2.length+1+(d.map (fun x=>x.2.length+1)).sum)=List.range (c.2.length+1)++(List.range (d.map (fun x=>x.2.length+1)).sum).map (fun k=>(c.2.length+1)+k):=(by rw[List.range_add]);rw[s,bR,nO,gm];congr 1;{congr 1;refine dF fun i M=>?_;have S:i<c.2.length+1:=aY.mp M;have z:(B.map (fun x=>x.2.length+1)).sum+i<N:=(by have a1:=q.2.2;rw[P] at a1;simp only[bR,ic,aO,eu] at a1;omega);rw[cT z];have a2:=i5 v q o B c d P i S;simp only[e,a2.1,a2.2];rw[cQ _ _ (by simp only[aE,aX];omega),cQ _ _ (by simp only[aE,aX];exact gb _ (by omega))]};{have ag:v=(B++[c])++d:=(by simpa[dM] using P);have a8:=K (B++[c]) ag;simp only[bR,ic,aO,fC,eu,mO,g1] at a8;rw[<- a8];congr 1;refine dF fun k _=>?_;simp only[qH,Nat.add_assoc]}
 have w:((finRange N).map e).prod=((List.range N).map (fun k=>if h:k<N then e ⟨k,h⟩ else 1)).prod:=(by congr 1;apply jD;{simp};{intro i Q h2;simp only[ft,List.length_finRange] at Q;simp[Q]});rw[w];have a7:=j [] v rfl;simp only[fC,mO,lE,q.2.2] at a7;rw[a7]
 have a4:∀(L:Ls (Cw N)),(-1:R)^L.length*((L.flatMap aE).map (j0 (R:=R))).prod*(L.map (fun c=>((List.range (c.2.length+1)).map (fun i=>let y:=aE c
      u (aA (y.getD i (V c.1))) (y.getD ((i+1) % (c.2.length+1)) (V c.1)))).prod)).prod=
  bJ u L:=by
  intro L;induction L with
  | nil=>simp[bJ]
  | cons c d K=>
    simp only[aX,pow_succ',eY,bR,nO,aO,iS,bJ] at K ⊢
    have a5:(-1:R)*((aE c).map (j0 (R:=R))).prod*((List.range (c.2.length+1)).map (fun i=>let y:=aE c
     u (aA (y.getD i (V c.1))) (y.getD ((i+1) % (c.2.length+1)) (V c.1)))).prod=
     bQ u c:=by
     unfold bQ;rw[<- om,oN u (V c.1) c.2 (V c.1)];simp only[aE,aO,iS,wg,j9]
     have a0:(List.range (c.2.length+1)).map (fun i=>let y:=V c.1::c.2
           u (aA (y.getD i (V c.1))) (y.getD ((i+1) % (c.2.length+1)) (V c.1)))=
      (List.range (c.2.length+1)).map (fun i=>let y:=V c.1::c.2
        let a:=y.getD i (V c.1);let b:=if i+1<c.2.length+1 then y.getD (i+1) (V c.1) else V c.1
        u (aA a) b):=by
      refine dF fun i M=>?_;have S:i<c.2.length+1:=aY.mp M;by_cases z:i+1<c.2.length+1;{simp[z,mF z]};{have af:i+1=c.2.length+1:=(by omega);simp[af]}
     rw[a0];ring
    calc (-1:R)*(-1)^d.length*(((aE c).map j0).prod*((d.flatMap aE).map j0).prod)*(((List.range (c.2.length+1)).map _).prod*(d.map _).prod)=((-1:R)*((aE c).map j0).prod*((List.range (c.2.length+1)).map _).prod)*((-1:R)^d.length*((d.flatMap aE).map j0).prod*(d.map _).prod):=by ring
     _=bQ u c*(d.map (bQ u)).prod:=by rw[a5,K]
 exact a4 v
def rB{N:Nat}(b:Pm (Fin (2*N))):Ft (Fin (2*N)×Fin (2*N)):=univ.image (fun r:Fin N=>if b (V r)<b (aZ r) then (b (V r),b (aZ r)) else (b (aZ r),b (V r)))
lemma gD{N:Nat}(b:Pm (Fin (2*N))):rB b∈PM N:=by
 rw[mC];refine⟨⟨?_,?_⟩,?_⟩
 ·
  intro e v;obtain⟨r,_,rfl⟩:=mem_image.mp v;have c:b (V r)≠b (aZ r):=fun h=>gP r (b.injective h);split_ifs with o
  {exact o};{exact qS (not_lt.mp o) c.symm}
 ·
  intro e v f w c;obtain⟨r,_,rfl⟩:=mem_image.mp v;obtain⟨s,_,rfl⟩:=mem_image.mp w;have j:r≠s:=fun h=>c (by subst h;rfl);rw[aT];intro x i d;have L:x=b (V r)\/x=b (aZ r):=(by split_ifs at i <;> (simp only[aF,aV,bI] at i;tauto));have z:x=b (V s)\/x=b (aZ s):=(by split_ifs at d <;> (simp only[aF,aV,bI] at d;tauto));rcases L with rfl|rfl <;> rcases z with h|h
  {exact j (h8 (b.injective h))};{exact bZ r s (b.injective h)};{exact bZ s r (b.injective h.symm)};{exact j (jm (b.injective h))}
 {ext x;simp only[bT,dN,iff_true];let y:=b.symm x;let r:Fin N:=⟨y.val / 2,by omega⟩;refine⟨if b (V r)<b (aZ r) then (b (V r),b (aZ r)) else (b (aZ r),b (V r)),mem_image.mpr ⟨r,dN r,rfl⟩,?_⟩;by_cases B:y.val % 2=0;{have q:y=V r:=bL (by simp[V,r];omega);have u:x=b (V r):=(by rw[<- q,uZ]);rw[u];split_ifs <;> simp[aF]};{have q:y=aZ r:=bL (by simp[aZ,r];omega);have u:x=b (aZ r):=(by rw[<- q,uZ]);rw[u];split_ifs <;> simp[aF]}}
lemma pT{N:Nat}(b:Pm (Fin (2*N)))(r:Fin N):(b (V r),b (aZ r))∈rB b\/(b (aZ r),b (V r))∈rB b:=by by_cases c:b (V r)<b (aZ r);{left;exact mem_image.mpr ⟨r,dN r,by simp[c]⟩};{right;exact mem_image.mpr ⟨r,dN r,by simp[c]⟩}
def g5{N:Nat}(d:Ls (Cw N))(c:er N d)(b:bO d):Ft (Fin (2*N)×Fin (2*N)):=rB (fP d c b)
lemma rr{N:Nat}{R:Type*}[CommRing R](j:Fin (2*N)->Fin (2*N)->R)(i:∀ a b,j b a=-j a b)(h:Ls (Cw N))(d:er N h)(c:bO h):bJ j h=(-1:R)^cr (g5 h d c) * ∏ e∈g5 h d c,j e.1 e.2:=by rw[<- oL j h d c];exact pS j i (g5 h d c) (mC.mp (gD _)) (fP h d c) (pT _)
open Classical in
def la{N:Nat}(c:Ft (Fin (2*N)×Fin (2*N)))(d:c∈PM N)(x:Fin (2*N)):Fin (2*N):=
 let b:x∈c.biUnion aF:=(mC.mp d).2.symm▸dN x;let e:=Classical.choose (bT.mp b)
 if x=e.1 then e.2 else e.1
lemma qa{N:Nat}{b:Ft (Fin (2*N)×Fin (2*N))}(c:b∈PM N)(x:Fin (2*N)):(x,la b c x)∈b\/(la b c x,x)∈b:=by
 classical
 unfold la;dsimp only;have h:=f9 (bT.mp ((mC.mp c).2.symm▸dN x))
 set e:=Classical.choose (bT.mp ((mC.mp c).2.symm▸dN x));have i:x=e.1\/x=e.2:=(by simpa only[aF,aV,bI] using h.2);by_cases d:x=e.1;{rw[dP d];left;simpa[d] using h.1};{rw[cM d];right;have j:x=e.2:=i.resolve_left d;simpa[j] using h.1}
lemma pP{N:Nat}{i:Ft (Fin (2*N)×Fin (2*N))}(o:i∈PM N){a b:Fin (2*N)}(u:(a,b)∈i\/(b,a)∈i):la i o a=b:=by
 have r:=(mC.mp o).1;have v:=qa o a;have e:∀ y,a∈aF (a,y):=fun y=>ep a {y};have d:∀ y,a∈aF (y,a):=fun y=>aV.mpr (Or.inr (gk a));rcases u with q|q <;> rcases v with s|s
 {by_cases c:(a,b)=(a,la i o a);{exact (mQ c).2.symm};{exact (aT.mp (r.2 _ q _ s c) (e b) (e _)).elim}}
 ·
  have j:(a,b)≠(la i o a,a):=fun h=>
   bS (r.1 _ q) (mQ h).2.symm
  exact (aT.mp (r.2 _ q _ s j) (e b) (d _)).elim
 ·
  have j:(b,a)≠(a,la i o a):=fun h=>
   bS (r.1 _ q) (mQ h).1
  exact (aT.mp (r.2 _ q _ s j) (d b) (e _)).elim
 {by_cases c:(b,a)=(la i o a,a);{exact (mQ c).1.symm};{exact (aT.mp (r.2 _ q _ s c) (d b) (d _)).elim}}
lemma jT{N:Nat}{c:Ft (Fin (2*N)×Fin (2*N))}(b:c∈PM N)(x:Fin (2*N)):la c b (la c b x)=x:=pP b (Or.symm (qa b x))
lemma yA{N:Nat}{d:Ft (Fin (2*N)×Fin (2*N))}(b:d∈PM N)(x:Fin (2*N)):la d b x≠x:=by
 have c:=(mC.mp b).1;rcases qa b x with h|h
 {exact (bS (c.1 _ h)).symm};{exact bS (c.1 _ h)}
def bG{N:Nat}(b:Ft (Fin (2*N)×Fin (2*N)))(c:b∈PM N)(x:Fin (2*N)):Fin (2*N):=la b c (aA x)
lemma kA{N:Nat}{b:Ft (Fin (2*N)×Fin (2*N))}(c:b∈PM N):Bijective (bG b c):=by refine Function.bijective_iff_has_inverse.mpr ⟨fun y=>aA (la b c y),?_,?_⟩;{intro x;simp[bG,jT,bH]};{intro y;simp[bG,jT,bH]}
lemma lX{N:Nat}{c:Ft (Fin (2*N)×Fin (2*N))}(b:c∈PM N):∀(k:Nat) (x:Fin (2*N)),(bG c b)^[k] x≠aA x
 | 0,x=>(lj x).symm
 | 1,x=>yA b (aA x)
 | k+2,x=>fun h=>by
   have e:bG c b ((bG c b)^[k] (bG c b x))=aA x:=(by rw[jb,eo] at h;exact h)
   have d:aA ((bG c b)^[k] (bG c b x))=bG c b x:=by
    have:=aI (la c b) e
    simpa only[bG,jT] using this
   exact lX b k (bG c b x) (by rw[<- bH ((bG c b)^[k] (bG c b x)),d])
lemma wQ{N:Nat}{d c:Ft (Fin (2*N)×Fin (2*N))}(h:d∈PM N)(e:c∈PM N)(b:d=c):bG d h=bG c e:=by subst b;rfl
lemma gV{N:Nat}{b:Ft (Fin (2*N)×Fin (2*N))}(c:b∈PM N)(k:Nat)(x:Fin (2*N)):(bG b c)^[k] (aA ((bG b c)^[k] x))=aA x:=by induction k generalizing x with|zero=>{rfl}|succ k d=>{rw[eo,jb];have e:bG b c (aA (bG b c ((bG b c)^[k] x)))=aA ((bG b c)^[k] x):=(by simp[bG,bH,jT]);rw[e];exact d x}
lemma tX{N:Nat}(q:Ls (Cw N))(h:er N q)(e:bO q)(v:Ls (Cw N))(c:Cw N)(y:Ls (Cw N))(w:q=v++c::y)(i:Nat)(z:i<c.2.length+1):let u:=gD (fP q h e)
 let L:=aE c
 bG (g5 q h e) u (L[i]'(by simp only[L,aE,aX];omega))=L[(i+1) % (c.2.length+1)]'(by simp only[L,aE,aX];exact gb _ (by omega)):=by
 intro u L;let b:=(v.map (fun x=>x.2.length+1)).sum;have s:b+i<N:=(by have j:=h.2.2;rw[w] at j;simp only[bR,ic,aO,eu] at j;omega);let r:Fin N:=⟨b+i,s⟩;have o:=i5 q h e v c y w i z;have d:=pT (fP q h e) r;rw[o.1,o.2] at d;exact pP u d
lemma mg{N:Nat}(e:Ls (Cw N))(d:er N e)(b:bO e)(j:Ls (Cw N))(c:Cw N)(i:Ls (Cw N))(q:e=j++c::i)(k:Nat):let h:=gD (fP e d b)
 let L:=aE c
 (bG (g5 e d b) h)^[k] (V c.1)=L[k % (c.2.length+1)]'(by simp only[L,aE,aX];exact gb _ (by omega)):=by
 intro h L;induction k with
 | zero=>simp[L,aE]
 | succ k o=>rw[jb,o,tX e d b j c i q (k % (c.2.length+1)) (gb _ (by omega))];congr 1;rw[Nat.mod_add_mod]
lemma oj{N:Nat}(f:Fin (2*N)->Fin (2*N))(i:Bijective f)(x:Fin (2*N)):∃ L:Nat,1<=L/\L<=2*N/\f^[L] x=x:=by
 have e:Fintype.card (Fin (2*N+1))>Fintype.card (Fin (2*N)):=(by simp);obtain⟨a,b,o,j⟩:=Fintype.exists_ne_map_eq_of_card_lt (fun k:Fin (2*N+1)=>f^[k.val] x) e;have d:a.val<b.val\/b.val<a.val:=Nat.lt_or_gt_of_ne (fun h=>o (bL h));have c:∀ k,Injective (f^[k]):=fun k=>i.1.iterate k;rcases d with q|q
 {refine⟨b.val-a.val,by omega,by omega,c a.val ?_⟩;rw[<- fq,show a.val+(b.val-a.val)=b.val by omega,j]};{refine⟨a.val-b.val,by omega,by omega,c b.val ?_⟩;rw[<- fq,show b.val+(a.val-b.val)=a.val by omega,j.symm]}
open Classical in
def dD{N:Nat}(c:Ft (Fin (2*N)×Fin (2*N)))(b:c∈PM N)(x:Fin (2*N)):Nat:=Nat.find (oj (bG c b) (kA b) x)
lemma eB{N:Nat}{c:Ft (Fin (2*N)×Fin (2*N))}(b:c∈PM N)(x:Fin (2*N)):let L:=dD c b x
 1<=L/\L<=2*N/\(bG c b)^[L] x=x/\
 ∀ k,1<=k->k<L->(bG c b)^[k] x≠x:=by
 classical
 have e:=Nat.find_spec (oj (bG c b) (kA b) x);refine⟨e.1,e.2.1,e.2.2,fun k i h j=>?_⟩;have d:=Nat.find_min (oj (bG c b) (kA b) x) h;have o:dD c b x<=2*N:=e.2.1;exact d ⟨i,by omega,j⟩
lemma gu{N:Nat}{c:Ft (Fin (2*N)×Fin (2*N))}(b:c∈PM N)(x:Fin (2*N))(k:Nat):(bG c b)^[k] x=(bG c b)^[k % dD c b x] x:=by
 let L:=dD c b x;have h:=eB b x
 have d:∀ q:Nat,(bG c b)^[L*q] x=x:=by
  intro q;induction q with
  | zero=>simp
  | succ q e=>rw[Nat.mul_succ,fq,h.2.2.1,e]
 conv_lhs=>rw[<- qR k L,Nat.add_comm,fq,d]
lemma rn{N:Nat}{E M:Ls (Cw N)}(y:er N E)(s:bO E)(a3:er N M)(a2:bO M)(b0:g5 E y s=g5 M a3 a2):E=M:=by
 let w:=g5 E y s;have r:w∈PM N:=gD _
 have u:∀(K:Ls (Cw N)) (Q:er N K) (o:bO K),g5 K Q o=w->∀(h:Fin N),(h∈K.map Prod.fst↔∀ k:Nat,h.val<=H ((bG w r)^[k] (V h)))/\(∀ c∈K,c.1=h->aE c=(List.range (dD w r (V h))).map (fun k=>(bG w r)^[k] (V h))):=by
  intro K Q o bj h;have q:bG (g5 K Q o) (gD _)=bG w r:=wQ (gD _) r bj
  have e:∀ c∈K,aE c=(List.range (dD w r (V c.1))).map (fun k=>(bG w r)^[k] (V c.1))/\∀ k:Nat,c.1.val<=H ((bG w r)^[k] (V c.1)):=by
   intro c P;obtain⟨b4,b3,hS⟩:=qM P;have d:∀ k,(bG w r)^[k] (V c.1)=(aE c).getD (k % (c.2.length+1)) (V c.1):=(by intro k;rw[<- q,mg K Q o b4 c b3 hS k,cQ _ _ (by simp only[aE,aX];exact gb _ (by omega))]);have ak:(A c).Nodup:=(by have z:(b4.flatMap A++(A c++b3.flatMap A)).Nodup:=(by simpa only[bO,hS,mJ,eY] using o);exact (fu.mp (fu.mp z).2.1).1);have ag:dD w r (V c.1)=c.2.length+1:=(by have au:=eB r (V c.1);apply sY;{by_contra ay;have z:=au.2.2.2 (c.2.length+1) (by omega) (by omega);apply z;rw[d,nZ];rfl};{by_contra aw;have z:=au.2.2.1;rw[d,mF (by omega),cQ _ _ (by simp only[aE,aX];omega)] at z;have B:H ((aE c)[dD w r (V c.1)]'(by simp[aE];omega))=H ((aE c)[0]'(by simp[aE])):=aI H z;have az:(A c)[dD w r (V c.1)]'(by simp[A,aE];omega)=(A c)[0]'(by simp[A,aE]):=(by simp only[A,kJ];exact B);have h0:dD w r (V c.1)=0:=ak.getElem_inj_iff.mp az;omega});refine⟨?_,fun k=>?_⟩;{apply jD;{simp[aE,ag]};{intro i z B;simp only[ft,lx,ag] at B;simp only[kJ,mH];rw[d i,mF B,cQ _ _ (by simp only[aE,aX];omega)]}}
   ·
    rw[d k,cQ _ _ (by simp only[aE,aX];exact gb _ (by omega))];have av:(aE c)[k % (c.2.length+1)]'(by simp only[aE,aX];exact gb _ (by omega))∈aE c:=iQ _;rcases cB.mp av with h0|ai
    {rw[h0,bK]}
    {have:=Q.1 c P _ ai;simp only[H];omega}
  refine⟨⟨?_,?_⟩,fun c P ba=>by subst ba;exact (e c P).1⟩;{intro hh;obtain⟨c,P,rfl⟩:=cC.mp hh;exact (e c P).2}
  ·
   intro ah;have ad:(K.flatMap A).length=N:=(by rw[<- fF,ft,eT,Q.2.2]);have a6:(K.flatMap A).toFinset=(List.range N).toFinset:=(by refine nH ?_ ?_;{intro x hx;rw[dO] at hx ⊢;rw[<- fF] at hx;obtain⟨v,_,rfl⟩:=cC.mp hx;exact aY.mpr (oC v)};{rw[nI o,ad,nI nodup_range,lx]});have ae:h.val∈K.flatMap A:=(by rw[<- dO,a6,dO,aY];exact h.isLt);obtain⟨c,P,b7⟩:=gM.mp ae;obtain⟨b4,b3,hS⟩:=qM P;obtain⟨v,hv,ar⟩:=cC.mp b7;obtain⟨i,hi,b6⟩:=mem_iff_getElem.mp hv
   have d:∀ k,(bG w r)^[k] (V c.1)=(aE c).getD (k % (c.2.length+1)) (V c.1):=fun k=>by
    rw[<- q,mg K Q o b4 c b3 hS k,cQ _ _ (by simp only[aE,aX];exact gb _ (by omega))]
   have a0:(bG w r)^[i] (V c.1)=v:=(by rw[d i,mF (by simpa[aE] using hi),cQ _ _ hi];exact b6);have af:c.1.val<=h.val:=(by rw[<- ar,<- a0];exact (e c P).2 i)
   have al:h.val<=c.1.val:=by
    rcases cI (ar.trans (bK h).symm) with rfl|b9
    ·
     have am:(bG w r)^[c.2.length+1-i] (V h)=V c.1:=(by rw[<- a0,<- fq,show c.2.length+1-i+i=c.2.length+1 by simp[aE] at hi;omega,d,nZ];rfl)
     have:=ah (c.2.length+1-i)
     rwa [am,bK] at this
    ·
     have z:aA ((bG w r)^[i] (V c.1))=V h:=(by rw[a0,b9,bH]);have B:(bG w r)^[i] (V h)=aA (V c.1):=(by rw[<- z];exact gV r i (V c.1))
     have:=ah i
     rwa [B,eJ,bK] at this
   have bb:c.1=h:=bL (sY af al);exact cC.mpr ⟨c,P,bb⟩
 have j:E.map Prod.fst=M.map Prod.fst:=by
  have ab:∀ h:Fin N,h∈E.map Prod.fst↔h∈M.map Prod.fst:=fun h=>by
   rw[(u E y s rfl h).1,(u M a3 a2 b0.symm h).1]
  have aa:∀(S L2:Ls (Fin N)),S.Pairwise (·<·)->L2.Pairwise (·<·)->(∀ x,x∈S↔x∈L2)->S=L2:=by
   intro S;induction S with
   | nil=>
     intro L2 _ _ hm;cases L2 with
     | nil=>rfl
     | cons b _=>exact absurd ((hm b).mpr gK) (by simp)
   | cons a S ih=>
     intro L2 z B hm;cases L2 with
     | nil=>exact absurd ((hm a).mp gK) (by simp)
     | cons b L2=>
       simp only[jE] at z B
       have bg:a=b:=by
        by_contra aj;rcases iR aj with aw|ay
        ·
         have bh:a∈b::L2:=(hm a).mp gK;rcases cB.mp bh with rfl|bi
         {exact aj rfl};{exact pC aw (B.1 a bi)}
        ·
         have be:b∈a::S:=(hm b).mpr gK;rcases cB.mp be with rfl|bf
         {exact aj rfl};{exact pC ay (z.1 b bf)}
       subst bg;congr 1;refine ih L2 z.2 B.2 fun x=>?_
       have:=hm x
       simp only[cB] at this;constructor;{intro aq;exact (this.mp (Or.inr aq)).resolve_left (fun h=>jH a (h▸z.1 x aq))};{intro ap;exact (this.mpr (Or.inr ap)).resolve_left (fun h=>jH a (h▸B.1 x ap))}
  exact aa _ _ y.2.1 a3.2.1 ab
 apply jD
 {have:=aI List.length j;simpa using this}
 ·
  intro i z B
  have ax:E[i].1=M[i].1:=by
   have:=aI (fun L=>L[i]?) j
   simp only[List.getElem?_map,List.getElem?_eq_getElem z,List.getElem?_eq_getElem B,pw,ia] at this;exact this
  have bd:=(u E y s rfl E[i].1).2 E[i] (iQ z) rfl;have bc:=(u M a3 a2 b0.symm E[i].1).2 M[i] (iQ B) ax.symm;have b1:aE E[i]=aE M[i]:=bd.trans bc.symm;simp only[aE,hJ] at b1;exact eC ax b1.2
lemma qs{N:Nat}(s:Ft (Fin (2*N)×Fin (2*N)))(o:s∈PM N):∃(P:Ls (Cw N)) (aw:er N P) (a8:bO P),g5 P aw a8=s:=by
 classical
 let w:=(finRange N).filter (fun h:Fin N=>
  decide (∀ k:Nat,h.val<=H ((bG s o)^[k] (V h))))
 let q (h:Fin N):Cw N:=
  (h,((List.range (dD s o (V h))).map (fun k=>(bG s o)^[k] (V h))).tail)
 let P:=w.map q;have u:∀ h:Fin N,aE (q h)=(List.range (dD s o (V h))).map (fun k=>(bG s o)^[k] (V h)):=(by intro h;have hL:=(eB o (V h)).1;obtain⟨m,hm⟩:∃ m,dD s o (V h)=m+1:=⟨dD s o (V h)-1,by omega⟩;dsimp only[q,aE];rw[hm,List.range_succ_eq_map];simp only[aO,jF,Function.iterate_zero_apply])
 have a4:∀ x:Fin (2*N),(((List.range (dD s o x)).map (fun k=>(bG s o)^[k] x)).map H).Nodup:=by
  intro x;rw[gm,List.nodup_iff_injective_getElem];intro⟨i,hi⟩ ⟨j,hj⟩ hget;apply bL;dsimp only;simp only[ft,lx] at hi hj;simp only[kJ,mH,qH] at hget;by_contra ab;have c8:=eB o x
  have bh:∀ a b,a<b->b<dD s o x->H ((bG s o)^[a] x)=H ((bG s o)^[b] x)->False:=by
   intro a b ct hb hp;have bd:=(kA o).1.iterate a;rcases cI hp.symm with a6|ae
   {have c4:(bG s o)^[a] ((bG s o)^[b-a] x)=(bG s o)^[a] x:=(by rw[<- fq,show a+(b-a)=b by omega];exact a6);exact c8.2.2.2 (b-a) (by omega) (by omega) (bd c4)};{have a2:(bG s o)^[b-a] ((bG s o)^[a] x)=aA ((bG s o)^[a] x):=(by rw[<- fq,show b-a+a=b by omega];exact ae);exact lX o (b-a) ((bG s o)^[a] x) a2}
  rcases iR ab with ad|cb
  {exact bh i j ad hj hget};{exact bh j i cb hi hget.symm}
 have ao:∀ B M:Fin N,B∈w->M∈w->B≠M->∀ p∈A (q B),p∉A (q M):=by
  intro B M bu bt ab p b9 b8;have c3:∀ k,B.val<=H ((bG s o)^[k] (V B)):=(by simpa[w] using bu);have c2:∀ k,M.val<=H ((bG s o)^[k] (V M)):=(by simpa[w] using bt);simp only[A,u,cC,aY] at b9 b8;obtain⟨x1,⟨k1,_,rfl⟩,rfl⟩:=b9;obtain⟨x2,⟨S,_,rfl⟩,bg⟩:=b8
  have br:B.val<=M.val:=by
   rcases cI bg with a6|ae
   ·
    have aj:(bG s o)^[S] (V M)=(bG s o)^[k1] (V B):=a6;let L2:=dD s o (V M);have cv:=eB o (V M);let d:=(L2-S % L2) % L2
    have ar:(bG s o)^[d+k1] (V B)=V M:=by
     rw[fq,<- aj,<- fq,gu o (V M)]
     have a1:(d+S) % L2=0:=by
      have bw:(L2-S % L2+S % L2) % L2=0:=by
       have:=gb S (by omega:0<L2)
       rw[show L2-S % L2+S % L2=L2 by omega,nZ]
      simpa[d,qV] using bw
     rw[a1];rfl
    have:=c3 (d+k1);rwa [ar,bK] at this
   ·
    have a2:(bG s o)^[k1] (V B)=aA ((bG s o)^[S] (V M)):=(by rw[ae,bH]);have h3:(bG s o)^[S+k1] (V B)=aA (V M):=(by rw[fq,a2];exact gV o S (V M))
    have:=c3 (S+k1);rwa [h3,eJ,bK] at this
  have bq:M.val<=B.val:=by
   rcases cI bg.symm with a6|ae
   ·
    let Q:=dD s o (V B);have cw:=eB o (V B);let d:=(Q-k1 % Q) % Q
    have ar:(bG s o)^[d+S] (V M)=V B:=by
     rw[fq,<- a6,<- fq,gu o (V B)]
     have a1:(d+k1) % Q=0:=by
      have bw:(Q-k1 % Q+k1 % Q) % Q=0:=by
       have:=gb k1 (by omega:0<Q)
       rw[show Q-k1 % Q+k1 % Q=Q by omega,nZ]
      simpa[d,qV] using bw
     rw[a1];rfl
    have:=c2 (d+S);rwa [ar,bK] at this
   ·
    have a2:(bG s o)^[S] (V M)=aA ((bG s o)^[k1] (V B)):=(by rw[ae,bH]);have h3:(bG s o)^[k1+S] (V M)=aA (V B):=(by rw[fq,a2];exact gV o k1 (V B))
    have:=c2 (k1+S);rwa [h3,eJ,bK] at this
  exact ab (bL (sY br bq))
 have ak:∀ p:Fin N,p.val∈P.flatMap A:=by
  intro p;let b5:=(List.range (dD s o (V p))).map (fun k=>(bG s o)^[k] (V p))
  have c0:b5≠[]:=by
   have:=(eB o (V p)).1
   simp[b5];omega
  let z:Ft Nat:=(b5.map H).toFinset;have au:z.Nonempty:=(by refine⟨p.val,dO.mpr (cC.mpr ⟨V p,?_,bK p⟩)⟩;exact cC.mpr ⟨0,aY.mpr (by have:=(eB o (V p)).1;omega),rfl⟩);let m:=z.min' au;have bb:m∈b5.map H:=dO.mp (Finset.min'_mem z au);obtain⟨v,b6,bj⟩:=cC.mp bb;obtain⟨K,co,rfl⟩:=cC.mp b6;let h:Fin N:=⟨m,bj▸oC _⟩;have b1:∀ k:Nat,h.val<=H ((bG s o)^[k] (V p)):=(by intro k;rw[gu o (V p) k];have bo:H ((bG s o)^[k % dD s o (V p)] (V p))∈z:=(by rw[dO];exact cC.mpr ⟨_,cC.mpr ⟨k % dD s o (V p),aY.mpr (gb _ (by have:=(eB o (V p)).1;omega)),rfl⟩,rfl⟩);exact Finset.min'_le z _ bo)
  have av:h∈w:=by
   simp only[w,gd,mK,fR,cG];intro k;rcases cI (bj.trans (bK h).symm) with a6|ae
   {rw[<- a6,<- fq];exact b1 (k+K)};{have a2:V h=aA ((bG s o)^[K] (V p)):=(by rw[ae,bH]);let E:=dD s o (V p);have ce:=eB o (V p);let d:=(E-k % E) % E;have cl:(bG s o)^[k] (aA ((bG s o)^[k+(K+d)] (V p)))=aA ((bG s o)^[K+d] (V p)):=(by rw[fq];exact gV o k _);let y:=(bG s o)^[K+d] (V p);have bi:(bG s o)^[k] y=(bG s o)^[K] (V p):=(by simp only[y,<- fq];rw[gu o (V p) (k+(K+d)),gu o (V p) K];congr 1;have a1:(k+d) % E=0:=(by have ad:=gb k (by omega:0<E);have:(k % E+(E-k % E)) % E=0:=(by rw[show k % E+(E-k % E)=E by omega,nZ]);simpa[d,qV] using this);rw[show k+(K+d)=K+(k+d) by omega,qV,a1,g1,mod_mod]);have ay:(bG s o)^[k] (V h)=aA y:=(by rw[a2,<- bi];exact gV o k y);rw[ay,eJ];exact b1 (K+d)}
  refine gM.mpr ⟨q h,j1 av,?_⟩;simp only[A,u,cC,aY];rcases cI (bj.trans (bK h).symm) with a6|ae
  {let E:=dD s o (V p);have ce:=eB o (V p);let d:=(E-K % E) % E;have aa:(bG s o)^[d] (V h)=V p:=(by rw[<- a6,<- fq,gu o (V p)];have a1:(d+K) % E=0:=(by have ad:=gb K (by omega:0<E);have:(E-K % E+K % E) % E=0:=(by rw[show E-K % E+K % E=E by omega,nZ]);simpa[d,qV] using this);rw[a1];rfl);refine⟨V p,⟨d % dD s o (V h),gb _ (by have:=(eB o (V h)).1;omega),?_⟩,bK p⟩;rw[<- gu o (V h) d,aa]};{have a2:V h=aA ((bG s o)^[K] (V p)):=(by rw[ae,bH]);have aa:(bG s o)^[K] (V h)=aA (V p):=(by rw[a2];exact gV o K (V p));refine⟨aA (V p),⟨K % dD s o (V h),gb _ (by have:=(eB o (V h)).1;omega),?_⟩,by rw[eJ,bK]⟩;rw[<- gu o (V h) K,aa]}
 have a8:bO P:=by
  unfold bO;simp only[P,nP];rw[lA];refine⟨fun h _=>by rw[A,u];exact a4 (V h),?_⟩;have bm:w.Nodup:=(jZ N).filter _;refine bm.pairwise_of_forall_ne fun B bu M bt ab p b9 b8=>
   ao B M bu bt ab p b9 b8
 have aw:er N P:=by
  refine⟨?_,?_,?_⟩
  ·
   intro c hc;obtain⟨h,hh,rfl⟩:=cC.mp hc;have c1:∀ k,h.val<=H ((bG s o)^[k] (V h)):=(by simpa[w] using hh);have b0:(A (q h)).Nodup:=(by rw[A,u];exact a4 (V h));simp only[A,aE,aO,j5,bK] at b0;intro v hv;have ax:v∈aE (q h):=g9 _ hv;rw[u] at ax;obtain⟨k,_,rfl⟩:=cC.mp ax;have cc:=c1 k
   have ab:H ((bG s o)^[k] (V h))≠h.val:=fun a6=>
    b0.1 (a6▸j1 hv)
   simp only[H] at cc ab;change 2*h.val+2<=((bG s o)^[k] (V h)).val;omega
  {have az:(finRange N).Pairwise (·<·):=(by rw[List.pairwise_iff_getElem];intro i j hi hj ca;simp only[List.getElem_finRange,iU];exact ca);have ba:P.map Prod.fst=w:=(by simp only[P,gm];have bv:Prod.fst ∘ q=id:=funext (fun _=>rfl);rw[bv,mN]);rw[ba];exact az.filter _};{have bc:(P.flatMap A).length=(P.map (fun c=>c.2.length+1)).sum:=(by rw[<- fF,ft,eT]);rw[<- bc];have bz:(P.flatMap A).toFinset=(List.range N).toFinset:=(by ext x;simp only[dO,aY];constructor;{intro hx;rw[<- fF] at hx;obtain⟨v,_,rfl⟩:=cC.mp hx;exact oC v};{intro hx;exact ak ⟨x,hx⟩});have b2:=aI Finset.card bz;rw[nI a8,nI nodup_range,lx] at b2;exact b2}
 refine⟨P,aw,a8,?_⟩;have b4:g5 P aw a8∈PM N:=gD _
 have a9:∀ c6∈PM N,c6.card=N:=fun c6 hQ=>by
  have hM:=mC.mp hQ;have M:(c6.biUnion aF).card=2*c6.card:=(by rw[sH (fun e he f hf ab=>hM.1.2 e he f hf ab)];have cg:∀ e∈c6,(aF e).card=2:=fun e he=>lC (bS (hM.1.1 e he));rw[dB rfl cg,qP,n0,kP]);rw[hM.2,pv,pq] at M;omega
 refine nH ?_ (by rw[a9 _ b4,a9 _ o]);intro e he;obtain⟨r,_,rfl⟩:=mem_image.mp he
 have aq:∀(L:Ls (Cw N)) (an:Nat),an<(L.map (fun c=>c.2.length+1)).sum->∃ Q c L2 i,L=Q++c::L2/\i<c.2.length+1/\an=(Q.map (fun x=>x.2.length+1)).sum+i:=by
  intro L;induction L with
  | nil=>intro an h;simp at h
  | cons c bx ih=>intro an h;simp only[aO,eu] at h;by_cases ad:an<c.2.length+1;{exact⟨[],c,bx,an,rfl,ad,by simp⟩};{obtain⟨Q,c',L2,i,bk,hi,ci⟩:=ih (an-(c.2.length+1)) (by omega);refine⟨c::Q,c',L2,i,by simp[bk],hi,?_⟩;simp only[aO,eu];omega}
 obtain⟨S1,c,S2,i,b3,hi,bl⟩:=aq P r.val (by rw[aw.2.2];exact r.isLt);have am:=i5 P aw a8 S1 c S2 b3 i hi;dsimp only at am;have b7:(⟨(S1.map (fun x=>x.2.length+1)).sum+i,by omega⟩:Fin N)=r:=bL bl.symm;rw[b7] at am;have bf:c∈P:=(by rw[b3];simp);obtain⟨h,_,rfl⟩:=cC.mp bf;have al:(q h).2.length+1=dD s o (V h):=(by have B:=aI List.length (u h);simpa[aE] using B)
 have be:(aE (q h))[i]'(by simp[aE];omega)=(bG s o)^[i] (V h):=by
  have B:(aE (q h))[i]'(by simp[aE];omega)=((List.range (dD s o (V h))).map (fun k=>(bG s o)^[k] (V h)))[i]'(by
   simp[<- al];omega):=by
   congr 1;exact u h
  rw[B];simp
 have ap:(aE (q h))[(i+1) % ((q h).2.length+1)]'(by
       simp only[aE,aX];exact gb _ (by omega))=
  (bG s o)^[i+1] (V h):=by
  have B:(aE (q h))[(i+1) % ((q h).2.length+1)]'(by
        simp only[aE,aX];exact gb _ (by omega))=
   ((List.range (dD s o (V h))).map (fun k=>(bG s o)^[k] (V h)))[(i+1) % dD s o (V h)]'(by
     simp only[ft,lx];exact gb _ (by have:=(eB o (V h)).1;omega)):=by
   congr 1;{exact u h};{rw[al]}
  rw[B];simp only[kJ,mH];exact (gu o (V h) (i+1)).symm
 rw[be,ap] at am;rw[am.1,am.2];have bp:(bG s o)^[i+1] (V h)=la s o (aA ((bG s o)^[i] (V h))):=(by rw[jb];rfl);rw[bp];have bn:=qa o (aA ((bG s o)^[i] (V h)));rcases bn with B|B
 {have ad:=(mC.mp o).1.1 _ B;rw[dP ad];exact B};{have ad:=(mC.mp o).1.1 _ B;rw[cM (e7 ad)];exact B}
lemma oM{N:Nat}{R:Type*}[CommRing R](o:Fin (2*N)->Fin (2*N)->R)(q:∀ a b,o b a=-o a b)(c:Ls (Ls (Cw N)))(v:c.Nodup)(d:∀ e,e∈c↔er N e):((c.filter (fun e=>decide (bO e))).map (bJ o)).sum=jn o:=by
 classical
 let h:=c.filter (fun e=>decide (bO e));have j:h.Nodup:=v.filter _
 have i:(h.map (bJ o)).sum=∑ e∈h.toFinset,bJ o e:=by
  have s:∀(L:Ls (Ls (Cw N))),L.Nodup->(L.map (bJ o)).sum=∑ e∈L.toFinset,bJ o e:=fun L B=>by
   induction L with|nil=>{simp}|cons a L E=>{simp only[j5] at B;simp only[aO,eu,sI,kK (dO.not.mpr B.1),E B.2]}
  exact s h j
 rw[i,jn];refine nV (fun e z=>let u:=gd.mp (dO.mp z)
  g5 e ((d e).mp u.1) (of_decide_eq_true u.2)) ?_ ?_ ?_ ?_
 {intro e z;exact gD _};{intro S1 P S Q w;exact rn _ _ _ _ w};{intro M K;obtain⟨e,x,r,y⟩:=qs M K;refine⟨e,dO.mpr (gd.mpr ⟨(d e).mpr x,jG r⟩),y⟩};{intro e z;exact rr o q e _ _}
lemma tJ{N:Nat}(h:1<=N){R:Type*}[CommRing R](d:Fin (2*N)->Fin (2*N)->R)(c:∀ a b,d b a=-d a b)(e:∀ u,d u u=0):uD d=jn d:=by rw[n4,List.sum_toFinset _ (jw N)];change ((ik N).map (bJ d)).sum=jn d;rw[lY d c e (ik N) (jw N) (pQ h)];exact oM d c (ik N) (jw N) (pQ h)
end
end MathCore
namespace xV
open Polynomial
open PEqualNP.Library Lib.Machines Lib.Universal MachineBits Packed
lemma gg{c b d:Type*}(L:Ls c)(f:c->Ls b)(g:b->Ls d):(L.flatMap f).flatMap g=L.flatMap (fun a=>(f a).flatMap g):=by induction L with|nil=>{rfl}|cons a L e=>{simp[eY,mJ,e]}
lemma iJ{b c:Type*}(L:Ls b)(f:b->Ls (Ls c)):(L.flatMap f).flatten=L.flatMap (fun a=>(f a).flatten):=by induction L with|nil=>{rfl}|cons a L d=>{simp[eY,List.flatten_append,d]}
lemma ll(a b:Nat):(List.range a).flatMap (fun _=>replicate b false)=replicate (a*b) false:=by induction a with|zero=>{simp}|succ a c=>{rw[nQ,mJ,eY,flatMap_nil,cR,c,<- o9,qU]}
def mc(a:LB):LB:=z1 a
def gz(a b:LB):LB:=gT a [] b
def wL(a b:LB):LB:=gT a b [true]
def iX(f:LB):LB:=yC f
def mT(b:LB):LB:=pU (kk b)
def rX(a b:LB):LB:=fO b a
def lQ(a b:LB):LB:=pU (fO a (m0 b))
def l8(a b:LB):LB:=mc (lQ b a)
def p5(a b:LB):LB:=gz (l8 a b) (l8 b a)
def vu(a:LB):LB:=un (a.length / 2)
def vy(a:LB):LB:=gT (tn a) (a++[true]) a.tail
def jI(b d c:LB):LB:=dS b d++c
def lV(w c b:LB):LB:=gT c (dT w b) (ti w b)
def fa(w c b:LB):LB:=kk (eN w c b)
lemma kt{a:LB->LB}(b:U a):U (fun s=>mc (a s)):=aH b Cp
lemma fN{a b:LB->LB}(d:U a)(c:U b):U (fun s=>gz (a s) (b s)):=cY d (aG []) c
lemma r6{a b:LB->LB}(d:U a)(c:U b):U (fun s=>wL (a s) (b s)):=cY d c (aG [true])
lemma i3{f:LB->LB}(b:U f):U (fun s=>iX (f s)):=CR b
lemma pX{b:LB->LB}(c:U b):U (fun s=>mT (b s)):=
 show U (fun s=>pU (kk (b s))) from aH (aH c uc) xR
lemma wE{a b:LB->LB}(d:U a)(c:U b):U (fun s=>rX (a s) (b s)):=gW c d
lemma na{a b:LB->LB}(d:U a)(c:U b):U (fun s=>lQ (a s) (b s)):=aH (gW d (aH c yD)) xR
lemma oY{a b:LB->LB}(d:U a)(c:U b):U (fun s=>l8 (a s) (b s)):=kt (na c d)
lemma oW{a b:LB->LB}(d:U a)(c:U b):U (fun s=>p5 (a s) (b s)):=fN (oY d c) (oY c d)
lemma yJ:U vu:=by
 let d:Bo->Bo->Bo×Op Bo:=fun st _=>(!st,if st then some true else none);refine eU _ _ _ d (fun _=>none) false fun s=>?_
 have b:∀(st:Bo) (l:LB),cL d (fun _=>none) st l=un ((l.length+st.toNat) / 2):=by
  intro st l;induction l generalizing st with
  | nil=>cases st <;> rfl
  | cons _ r e=>cases st with|false=>{simp only[cL,d,Bool.not_false,eX,↓reduceIte,e,Bool.toNat_true,qQ,aX,g1,Option.toList_none,gl]}|true=>{simp only[cL,d,sQ,↓reduceIte,e,qQ,Bool.toNat_true,aX,g1,Option.toList_some,fB,gl];have c:(r.length+1+1) / 2=r.length / 2+1:=(by omega);rw[c,rv]}
 simpa[vu] using (b false s).symm
lemma yK{a:LB->LB}(b:U a):U (fun s=>vy (a s)):=cY (aH b yf) (aC b (aG [true])) (wF b)
lemma k3{n i j:LB->LB}(b:U n)(d:U i)(c:U j):U (fun s=>jI (n s) (i s) (j s)):=aC (jW b d) c
lemma vo{w b v:LB->LB}(c:U w)(e:U b)(d:U v):U (fun s=>lV (w s) (b s) (v s)):=cY e (qu c d) (zZ c d)
lemma i4{w i s:LB->LB}(b:U w)(d:U i)(c:U s):U (fun x=>fa (w x) (i x) (s x)):=aH (ku b d c) uc
lemma hY(b:Bo):mc (cF b)=cF (!b):=by cases b <;> rfl
lemma dx(a b:Bo):gz (cF a) (cF b)=cF (a&&b):=by cases a <;> cases b <;> rfl
lemma jz(a b:Bo):wL (cF a) (cF b)=cF (a||b):=by cases a <;> cases b <;> rfl
lemma ue(a b:Bo):qk (cF a) (cF b)=cF (xor a b):=by cases a <;> cases b <;> rfl
lemma ew(b:Bo):iX (cF b)=[b]:=by cases b <;> rfl
lemma eM(f:LB):(iX f).length=1:=by unfold iX yC gT;split_ifs <;> rfl
lemma dE(b:Bo)(x y:LB):gT (cF b) x y=if b then y else x:=by cases b <;> rfl
lemma oO(c:LB):mT c=cF (decide (true∈c)):=by
 induction c with
 | nil=>rfl
 | cons b r d=>cases b with|true=>{simp[mT,kk,pU,cF]}|false=>{simpa[mT,kk] using d}
lemma vK(m n:Nat):rX (un m) (un n)=un (m-n):=by rw[rX,xS,J];simp[un]
lemma iZ(a b:LB):lQ a b=cF (decide (a.length<b.length)):=by rw[lQ,xS,m0,List.drop_replicate];by_cases h:a.length<b.length;{have c:b.length-a.length=(b.length-a.length-1)+1:=(by omega);rw[c,mI];simp[pU,cF,h]};{have d:b.length-a.length=0:=(by omega);rw[d];simp[pU,cF,h]}
lemma iI(a b:LB):l8 a b=cF (decide (a.length<=b.length)):=by rw[l8,iZ,hY];congr 1;apply Bool.eq_iff_iff.mpr;simp
lemma nw(a b:LB):p5 a b=cF (decide (a.length=b.length)):=by rw[p5,iI,iI,dx];congr 1;apply Bool.eq_iff_iff.mpr;simp[Nat.le_antisymm_iff]
lemma tq(v:Nat):tn (un v)=cF (decide (v % 2=1)):=by by_cases h:v % 2=1 <;> simp[tn,cF,h]
lemma yx(v:Nat):vy (un v)=un (if v % 2=0 then v+1 else v-1):=by
 rw[vy,tq,dE];by_cases h:v % 2=0;{simp[h,un,List.replicate_succ']}
 ·
  have c:v % 2=1:=(by omega);have b:v=(v-1)+1:=(by omega);simp only[c,iy,↓reduceIte];conv_lhs=>rw[b,rv]
  rfl
lemma kg(n i j:Nat):jI (un n) (un i) (un j)=un (i*n+j):=by simp only[jI,dS,J];simp only[un,o9,Nat.mul_comm]
lemma tx{w v:LB}{z:Int}(c:rep w v z)(b:Bo):rep w (lV w (cF b) v) (if b then -z else z):=by
 rw[lV,dE];cases b with
 | false=>simp only[eX,↓reduceIte];have d:rep w (dT w v) (val v:Int):=(by rw[rep,vI];exact_mod_cast (j7 (val v) (2^w.length)));exact d.trans c
 | true=>simp only[↓reduceIte];exact xf c
lemma w9(b d:Nat)(hd:d<=b):dT (un b) (un d)=un d++replicate (b-d) false:=by
 rw[dT,vZ,J]
 have c:fJ (un b)=replicate b false:=by
  have:∀ m,fJ (un m)=replicate m false:=fun m=>by
   induction m with|zero=>{rfl}|succ m e=>{simp[un,mI,fJ]}
  exact this b
 rw[c,take_append,J,o8 (by simp[un];exact hd),List.take_replicate,sW (by omega)]
lemma kz(b d:Nat)(hd:d<=b):kk (dT (un b) (un d))=un d:=by
 rw[w9 b d hd]
 have h:kk (un d)=un d:=by induction d with|zero=>{rfl}|succ d c=>{simp[un,mI,kk] at c ⊢}
 have e:∀ m,kk (replicate m false)=[]:=fun m=>by
  induction m with|zero=>{rfl}|succ m c=>{simp[mI,kk] at c ⊢}
 simp only[kk,List.filter_append];change kk (un d)++kk (replicate (b-d) false)=un d;rw[h,e,cR]
lemma pM(b:LB):∀(i:Nat) (e:i<b.length),b[i]=(val b).testBit i:=by
 induction b with
 | nil=>intro i e;simp at e
 | cons c r h=>
   intro i e;cases i with
   | zero=>simp only[List.getElem_cons_zero,val,Nat.testBit_zero];cases c <;> simp
   | succ i=>simp only[List.getElem_cons_succ,val,Nat.testBit_succ];have d:(c.toNat+2*val r) / 2=val r:=(by cases c <;> simp <;> omega);rw[d];exact h i (by simp at e;omega)
lemma ur(k z:Nat)(b:LB)(c:b.length=k)(o:rep (un k) b (z:Int)):b=(List.range k).map (fun h=>(z % 2^k).testBit h):=by have d:rep (un k) b ((z % 2^k:Nat):Int):=(by have e:((z % 2^k:Nat):Int) ≡ (z:Int) [ZMOD (2:Int)^(un k).length]:=(by rw[J];exact_mod_cast j7 z (2^k));exact o.trans e.symm);have j:val b=z % 2^k:=vM (by simpa using c) d (by rw[J];exact gb z (by positivity));apply jD;{simp[c]};{intro i e q;simp only[kJ,mH];rw[pM b i e,j]}
lemma jf(j:Nat)(b:LB):hd ((replicate j true++[false])++b)=un j/\jy ((replicate j true++[false])++b)=b:=by have h:(replicate j true++[false])++b=un j++false::b:=(by simp[un,dM]);rw[h];refine⟨by simp[hd,un],?_⟩;have c:(un j++false::b).dropWhile id=false::b:=(by simp[un]);rw[jy,c];rfl
def iP(s:LB):LB:=
 let b:=left s;let R:=left (right s);let T:=right (right s)
 iX (gz (dQ b R) (dQ b T))
lemma tb:U iP:=i3 (fN (dK (aD aR) (aD (Y aR))) (dK (aD aR) (Y (Y aR))))
def lk(b R T:LB):LB:=mT (bX iP [true] b (Z R T))
lemma oX{n R T:LB->LB}(b:U n)(d:U R)(c:U T):U (fun s=>lk (n s) (R s) (T s)):=pX (bW tb (aG [true]) b (D d c))
def aK{n:Nat}(b:Fv n):LB:=(finRange n).map (fun i=>decide (i∈b))
lemma jL{n:Nat}(b:Fv n):(aK b).length=n:=by simp[aK]
lemma gn{n:Nat}(c:Fv n)(i:Nat)(b:i<n):(aK c).getD i false=decide (⟨i,b⟩∈c):=by rw[cQ _ _ (by simp[aK,b])];simp[aK]
lemma ii{n:Nat}(R:Fv n)(c:LB):gY (un n) (aK R++c)=aK R/\fO (un n) (aK R++c)=c:=by have b:=jL R;rw[vZ,xS,J];constructor;{rw[take_append,b,nY,List.take_zero,cR,o8 b.le]};{rw[drop_append,b,nY,sZ,uV b.le,gl]}
lemma lN{n:Nat}(R T:Fv n):lk (un n) (aK R) (aK T)=cF (decide (¬Disjoint R T)):=by unfold lk;rw[bA iP [true] (un n) (Z (aK R) (aK T)) (fun i _=>by simp[iP,eM])];rw[oO,J];congr 1;apply Bool.eq_iff_iff.mpr;simp only[cG,gM,aY,uT];constructor;{rintro⟨i,d,c⟩;simp only[iP,left,right,G,eG,J,gn _ i d,dx,ew,eZ] at c;have b:(decide (⟨i,d⟩∈R)&&decide (⟨i,d⟩∈T))=true:=c.symm;simp only[gy,cG] at b;exact⟨⟨i,d⟩,b.1,b.2⟩};{rintro⟨i,h,e⟩;refine⟨i.val,i.isLt,?_⟩;simp only[iP,left,right,G,eG,J,gn _ i.val i.isLt,dx,ew,eZ];simp[h,e]}
def ks(s:LB):LB:=
 let d:=left s;let c:=left (right s);let b:=right (right s);let row:=eN (c++c) d b
 iX (lk c (gY c row) (fO c row))
lemma vh:U ks:=by have d:=aD aR;have c:=aD (Y aR);have e:=Y (Y aR);have b:=ku (aC c c) d e;exact i3 (oX c (sf c b) (gW c b))
def kT(c d b:LB):LB:=mT (bX ks [true] d (Z c b))
lemma um{n h c:LB->LB}(d:U n)(e:U h)(b:U c):U (fun s=>kT (n s) (h s) (c s)):=pX (bW vh (aG [true]) e (D d b))
lemma tG{n:Nat}(b:Ls (Fv n×Fv n)):kT (un n) (un b.length) (b.flatMap (fun z=>aK z.1++aK z.2))=cF (decide (∃ z∈b,¬Disjoint z.1 z.2)):=by
 unfold kT;rw[bA ks [true] (un b.length) _ (fun _ _=>by simp[ks,eM]),oO,J];congr 1;apply Bool.eq_iff_iff.mpr;simp only[cG,gM,aY]
 have d:∀ i (h:i<b.length),eN (un n++un n) (un i) (b.flatMap (fun z=>aK z.1++aK z.2))=aK b[i].1++aK b[i].2:=fun i h=>
  fo b (fun z=>aK z.1++aK z.2) (un n++un n) i h (fun z _=>by simp[jL,J])
 have c:∀(R T:Fv n),gY (un n) (aK R++aK T)=aK R/\fO (un n) (aK R++aK T)=aK T:=fun R T=>ii R (aK T);constructor;{rintro⟨i,h,e⟩;simp only[ks,left,right,G,d i h,(c _ _).1,(c _ _).2,lN,ew,eZ] at e;exact⟨b[i],iQ h,of_decide_eq_true e.symm⟩};{rintro⟨z,o,j⟩;obtain⟨i,h,rfl⟩:=mem_iff_getElem.mp o;refine⟨i,h,?_⟩;simp only[ks,left,right,G,d i h,(c _ _).1,(c _ _).2,lN,ew,eZ];exact (jG j).symm}
def gB(s:LB):LB:=
 let j:=left s;let e:=right s;let c:=left e;let d:=right e;let b:=left d;let i:=left (right d);let h:=right (right d);let row:=eN (c++c) j b;let R:=gY c row;let T:=fO c row
 iX (wL (gz (dQ i R) (dQ h R)) (gz (dQ i T) (dQ h T)))
lemma r5:U gB:=by have r:=aD aR;have d:=Y aR;have e:=aD d;have c:=Y d;have h:=aD c;have j:=aD (Y c);have i:=Y (Y c);have b:=ku (aC e e) r h;have q:=sf e b;have o:=gW e b;exact i3 (r6 (fN (dK j q) (dK i q)) (fN (dK j o) (dK i o)))
def fM(s:LB):LB:=
 let h:=left s;let e:=right s;let i:=left e;let d:=right e;let j:=left d;let o:=left (right d);let b:=right (right d);let c:=mT (bX gB [true] o (Z j (Z b (Z i h))))
 iX (gz (lQ i h) (mc c))
lemma vj:U fM:=by have h:=aD aR;have c:=Y aR;have i:=aD c;have b:=Y c;have j:=aD b;have o:=aD (Y b);have e:=Y (Y b);have d:=pX (bW r5 (aG [true]) o (D j (D e (D i h))));exact i3 (fN (na i h) (kt d))
def gr(s:LB):LB:=
 let d:=left s;let b:=right s;let c:=left b
 bX fM [true] c (Z d b)
lemma vk:U gr:=bW vj (aG [true]) (aD (Y aR)) (D (aD aR) (Y aR))
def jP(c d b:LB):LB:=bX gr c c (Z c (Z d b))
lemma yk{n h d:LB->LB}(b:U n)(e:U h)(c:U d):U (fun s=>jP (n s) (h s) (d s)):=bW vk b b (D b (D e c))
lemma t6(c e b:LB):(jP c e b).length=c.length*c.length:=by unfold jP;have d:∀ i<c.length,(gr (Z (un i) (Z c (Z e b)))).length=c.length:=(by intro i _;simp only[gr,left,right,G];rw[bA fM [true] c _ (fun _ _=>by simp[fM,eM])];have q:∀ j∈List.range c.length,(fM (Z (un j) (Z (un i) (Z c (Z e b))))).length=1:=fun _ _=>eM _;simp[gx,dF q]);rw[bA gr c c _ (fun i h=>(d i h).le)];have o:∀ i∈List.range c.length,(gr (Z (un i) (Z c (Z e b)))).length=c.length:=fun i h=>d i (aY.mp h);simp[gx,dF o]
lemma wt{n:Nat}(c:Ls (Fv n×Fv n))(i j:Fin n):(jP (un n) (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))).getD (i.val*n+j.val) false=decide (i<j/\∀ z∈c,¬(({i,j}:Fv n)⊆z.1)/\¬(({i,j}:Fv n)⊆z.2)):=by
 have u:∀ t (s:t<c.length),eN (un n++un n) (un t) (c.flatMap (fun z=>aK z.1++aK z.2))=aK c[t].1++aK c[t].2:=fun t s=>
  fo c (fun z=>aK z.1++aK z.2) (un n++un n) t s (fun z _=>by simp[jL,J])
 have d:∀(R T:Fv n),gY (un n) (aK R++aK T)=aK R/\fO (un n) (aK R++aK T)=aK T:=fun R T=>ii R (aK T)
 have h:∀(a b:Fin n),fM (Z (un b.val) (Z (un a.val) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))))))=[decide (a<b/\∀ z∈c,¬(({a,b}:Fv n)⊆z.1)/\¬(({a,b}:Fv n)⊆z.2))]:=by
  intro a b;simp only[fM,left,right,G];rw[bA gB [true] (un c.length) _ (fun _ _=>by simp[gB,eM]),oO,iZ,J,J,J]
  have a0:decide (true∈(List.range c.length).flatMap (fun t=>gB (Z (un t) (Z (un n) (Z (c.flatMap (fun z=>aK z.1++aK z.2)) (Z (un a.val) (un b.val)))))))=
   decide (∃ z∈c,({a,b}:Fv n)⊆z.1\/({a,b}:Fv n)⊆z.2):=by
   apply Bool.eq_iff_iff.mpr;simp only[cG,gM,aY];constructor
   ·
    rintro⟨t,s,w⟩;simp only[gB,left,right,G,u t s,(d _ _).1,(d _ _).2,eG,J,gn _ a.val a.isLt,gn _ b.val b.isLt,dx,jz,ew,eZ] at w;have B:((decide (a∈c[t].1)&&decide (b∈c[t].1))||(decide (a∈c[t].2)&&decide (b∈c[t].2)))=true:=w.symm;simp only[kN,gy,cG] at B;refine⟨c[t],iQ s,?_⟩;rcases B with ⟨ad,ab⟩|⟨aa,a9⟩
    · left;intro x L;simp only[aV,bI] at L;rcases L with rfl|rfl <;> assumption
    · right;intro x L;simp only[aV,bI] at L;rcases L with rfl|rfl <;> assumption
   {rintro⟨z,E,e|e⟩;{obtain⟨t,s,rfl⟩:=mem_iff_getElem.mp E;refine⟨t,s,?_⟩;simp only[gB,left,right,G,u t s,(d _ _).1,(d _ _).2,eG,J,gn _ a.val a.isLt,gn _ b.val b.isLt,dx,jz,ew,eZ];have M:a∈c[t].1:=e (by simp);have Q:b∈c[t].1:=e (by simp);simp[M,Q]};{obtain⟨t,s,rfl⟩:=mem_iff_getElem.mp E;refine⟨t,s,?_⟩;simp only[gB,left,right,G,u t s,(d _ _).1,(d _ _).2,eG,J,gn _ a.val a.isLt,gn _ b.val b.isLt,dx,jz,ew,eZ];have P:a∈c[t].2:=e (by simp);have S:b∈c[t].2:=e (by simp);simp[P,S]}}
  rw[a0,hY,dx,ew];congr 1;apply Bool.eq_iff_iff.mpr;simp only[gy,sP,cG,qD,not_exists,not_and,not_or,iU]
 have o:eN (un n) (un i.val) (jP (un n) (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2)))=gr (Z (un i.val) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))))):=by
  unfold jP
  have q:∀ a∈List.range n,(gr (Z (un a) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2)))))).length=(un n).length:=fun a _=>by
   simp only[gr,left,right,G];rw[bA fM [true] (un n) _ (fun _ _=>by simp[fM,eM]),J];have B:∀ b∈List.range n,(fM (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))))))).length=1:=fun _ _=>eM _;simp[gx,dF B]
  rw[bA gr (un n) (un n) _ (fun a K=>(q a (aY.mpr (by simpa using K))).le)];rw[J,fo (List.range n) _ (un n) i.val (by simp[i.isLt]) q];simp
 have r:eN [true] (un j.val) (gr (Z (un i.val) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))))))=fM (Z (un j.val) (Z (un i.val) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2)))))):=(by simp only[gr,left,right,G];rw[bA fM [true] (un n) _ (fun _ _=>by simp[fM,eM]),J];rw[fo (List.range n) (fun b=>fM (Z (un b) (Z (un i.val) (Z (un n) (Z (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))))))) [true] j.val (by simp[j.isLt]) (fun _ _=>eM _)];simp);have y:(jP (un n) (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2))).getD (i.val*n+j.val) false=((eN [true] (un j.val) (eN (un n) (un i.val) (jP (un n) (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2)))))).getD 0 false:=(by simp only[eN,J,lv,j9,Nat.mul_comm n i.val];have v:=t6 (un n) (un c.length) (c.flatMap (fun z=>aK z.1++aK z.2));rw[J] at v;have a7:i.val*n+j.val<n*n:=(by nlinarith [i.isLt,j.isLt]);rw[cQ _ _ (by omega),cQ _ _ (by simp[v];omega)];simp[List.getElem_take,List.getElem_drop]);rw[y,o,r,h i j];rfl
def iz(s:LB):LB:=
 let h:=left s;let c:=left (right s);let b:=right (right s);let d:=c++c;let row:=eN (d++[true]) h b;let R:=gY c row;let T:=gY c (fO c row);let e:=dQ d row
 iX (gT (lk c R T) (mc e) e)
lemma tK:U iz:=by have h:=aD aR;have d:=aD (Y aR);have i:=Y (Y aR);have e:=aC d d;have b:=ku (aC e (aG [true])) h i;have o:=sf d b;have j:=sf d (gW d b);have c:=dK e b;exact i3 (cY (oX d o j) (kt c) c)
def mV(c d b:LB):LB:=kk (bX iz [true] d (Z c b))
lemma vR{n m c:LB->LB}(d:U n)(e:U m)(b:U c):U (fun s=>mV (n s) (m s) (c s)):=aH (bW tK (aG [true]) e (D d b)) uc
lemma o4{n:Nat}(b:Sf n)(t:Nat)(h:t<b.length):let e:=b.flatMap (fun x=>aK x.1.1++aK x.1.2++[x.2])
 let row:=eN ((un n++un n)++[true]) (un t) e
 gY (un n) row=aK b[t].1.1/\
 gY (un n) (fO (un n) row)=aK b[t].1.2/\
 dQ (un n++un n) row=cF b[t].2:=by
 intro e row;have c:row=aK b[t].1.1++aK b[t].1.2++[b[t].2]:=fo b (fun x=>aK x.1.1++aK x.1.2++[x.2]) ((un n++un n)++[true]) t h (fun x _=>by simp[jL,J]);rw[c];refine⟨?_,?_,?_⟩;{rw[dM];exact (ii b[t].1.1 (aK b[t].1.2++[b[t].2])).1};{rw[dM,(ii b[t].1.1 (aK b[t].1.2++[b[t].2])).2];exact (ii b[t].1.2 [b[t].2]).1};{rw[eG];have d:(un n++un n).length=(aK b[t].1.1++aK b[t].1.2).length:=(by simp[jL,J]);rw[d,cQ _ _ (by simp)];simp[sx]}
lemma jV{c:Type*}(L:Ls c)(f:c->Bo):kk (L.flatMap (fun a=>[f a]))=un (L.filter f).length:=by induction L with|nil=>{rfl}|cons a L b=>{cases hf:f a <;> simp only[eY,sw,kk,po,hf,id_eq,eX,↓reduceIte,aX,rv] at b ⊢;{exact b};{exact aI (true::·) b}}
lemma u6{n:Nat}(b:Sf n):mV (un n) (un b.length) (b.flatMap (fun x=>aK x.1.1++aK x.1.2++[x.2]))=un (b.filter (fun t=>if Disjoint t.1.1 t.1.2 then !t.2 else t.2)).length:=by
 unfold mV;rw[bA iz [true] (un b.length) _ (fun _ _=>by simp[iz,eM]),J]
 have j:(List.range b.length).flatMap (fun t=>iz (Z (un t) (Z (un n) (b.flatMap (fun x=>aK x.1.1++aK x.1.2++[x.2])))))=b.flatMap (fun x=>[if Disjoint x.1.1 x.1.2 then !x.2 else x.2]):=by
  have r:(List.range b.length).flatMap (fun t=>iz (Z (un t) (Z (un n) (b.flatMap (fun x=>aK x.1.1++aK x.1.2++[x.2])))))=(List.range b.length).flatMap (fun t=>if h:t<b.length then [if Disjoint b[t].1.1 b[t].1.2 then !b[t].2 else b[t].2] else []):=(by refine dG fun t o=>?_;have c:t<b.length:=aY.mp o;rw[cT c];have d:=o4 b t c;dsimp only at d;simp only[iz,left,right,G,d.1,d.2.1,d.2.2,lN,hY,dE];by_cases hd:Disjoint b[t].1.1 b[t].1.2 <;> simp[hd,ew]);rw[r];have e:b=(List.range b.length).map (fun t=>b.getD t ((∅,∅),false)):=(by apply jD;{simp};{intro i q _;simp only[kJ,mH];exact (cQ _ _ q).symm});conv_rhs=>rw[e,nP]
  refine dG fun t o=>?_;have c:t<b.length:=aY.mp o;rw[cT c,cQ _ _ c]
 rw[j,jV]
def kh(d R T c b:LB):LB:=gz (mc (lk d R T)) (wL (gz (dQ c R) (dQ b R)) (gz (dQ c T) (dQ b T)))
lemma pF{n R T i j:LB->LB}(h:U n)(c:U R)(b:U T)(e:U i)(d:U j):U (fun s=>kh (n s) (R s) (T s) (i s) (j s)):=fN (kt (oX h c b)) (r6 (fN (dK e c) (dK d c)) (fN (dK e b) (dK d b)))
def mr(s:LB):LB:=
 let j:=left s;let i:=right s;let c:=left i;let e:=right i;let b:=left e;let q:=left (right e);let o:=right (right e);let d:=c++c;let row:=eN (d++[true]) j b;let R:=gY c row;let T:=gY c (fO c row);let h:=dQ d row
 iX (gz h (kh c R T q o))
def mn(s:LB):LB:=
 let j:=left s;let i:=right s;let c:=left i;let e:=right i;let b:=left e;let q:=left (right e);let o:=right (right e);let d:=c++c;let row:=eN (d++[true]) j b;let R:=gY c row;let T:=gY c (fO c row);let h:=dQ d row
 iX (gz (mc h) (kh c R T q o))
lemma w5:U mr:=by have o:=aD aR;have e:=Y aR;have d:=aD e;have c:=Y e;have j:=aD c;have r:=aD (Y c);have q:=Y (Y c);have h:=aC d d;have b:=ku (aC h (aG [true])) o j;have u:=sf d b;have s:=sf d (gW d b);have i:=dK h b;exact i3 (fN i (pF d u s r q))
lemma w4:U mn:=by have o:=aD aR;have e:=Y aR;have d:=aD e;have c:=Y e;have j:=aD c;have r:=aD (Y c);have q:=Y (Y c);have h:=aC d d;have b:=ku (aC h (aG [true])) o j;have u:=sf d b;have s:=sf d (gW d b);have i:=dK h b;exact i3 (fN (kt i) (pF d u s r q))
def eV(b:LB):LB:=b++b++b++[true]
def fe(s:LB):LB:=
 let o:=left s;let i:=right s;let q:=left i;let h:=right i;let j:=left h;let e:=left (right h);let b:=right (right h);let args:=Z j (Z b (Z q o));let c:=kk (bX mr [true] e args);let d:=kk (bX mn [true] e args);let r:=rX ((e++e++[true])++c) d
 dT (eV e) r
lemma tL:U fe:=by have r:=aD aR;have e:=Y aR;have s:=aD e;have c:=Y e;have q:=aD c;have d:=aD (Y c);have j:=Y (Y c);have b:=D q (D j (D s r));have h:=aH (bW w5 (aG [true]) d b) uc;have i:=aH (bW w4 (aG [true]) d b) uc;have u:=aC (aC d d) (aG [true]);have hd:=wE (aC u h) i;have o:=aC (aC (aC d d) d) (aG [true]);exact qu o hd
def jc(s:LB):LB:=
 let e:=left s;let b:=right s;let c:=left b;let d:=left (right b)
 bX fe (eV d) c (Z e b)
lemma tM:U jc:=by have h:=aD aR;have b:=Y aR;have e:=aD b;have c:=aD (Y b);have d:=aC (aC (aC c c) c) (aG [true]);exact bW tL d e (D h b)
def hN(c d b:LB):LB:=bX jc (dS c (eV d)) c (Z c (Z d b))
lemma tN{n m e:LB->LB}(d:U n)(b:U m)(c:U e):U (fun s=>hN (n s) (m s) (e s)):=by have h:=aC (aC (aC b b) b) (aG [true]);exact bW tM (jW d h) d (D d (D b c))
lemma qm{n:Nat}(c:Sf n)(i j:Fin n):let s:=c.flatMap (fun x=>aK x.1.1++aK x.1.2++[x.2])
 let M:=(c.filter (fun t=>t.2&&decide (Disjoint t.1.1 t.1.2/\
  (({i,j}:Fv n)⊆t.1.1\/({i,j}:Fv n)⊆t.1.2)))).length
 let aa:=(c.filter (fun t=>!t.2&&decide (Disjoint t.1.1 t.1.2/\
  (({i,j}:Fv n)⊆t.1.1\/({i,j}:Fv n)⊆t.1.2)))).length
 fa (eV (un c.length)) (jI (un n) (un i.val) (un j.val)) (hN (un n) (un c.length) s)=un ((2*c.length+1)+M-aa):=by
 intro s M aa;have a0:∀(R T:Fv n) (a b:Fin n),kh (un n) (aK R) (aK T) (un a.val) (un b.val)=cF (decide (Disjoint R T/\(({a,b}:Fv n)⊆R\/({a,b}:Fv n)⊆T))):=(by intro R T a b;simp only[kh,lN,hY,eG,J,gn _ a.val a.isLt,gn _ b.val b.isLt,dx,jz];congr 1;apply Bool.eq_iff_iff.mpr;simp only[gy,kN,sP,cG,qD,not_not];constructor;{rintro⟨hd,⟨Q,P⟩|⟨Q,P⟩⟩;{exact⟨hd,Or.inl (fun x E=>by simp only[aV,bI] at E;rcases E with rfl|rfl <;> assumption)⟩};{exact⟨hd,Or.inr (fun x E=>by simp only[aV,bI] at E;rcases E with rfl|rfl <;> assumption)⟩}};{rintro⟨hd,u|u⟩;{exact⟨hd,Or.inl ⟨u (by simp),u (by simp)⟩⟩};{exact⟨hd,Or.inr ⟨u (by simp),u (by simp)⟩⟩}})
 have z:∀(a b:Fin n),
  let p:=(c.filter (fun t=>t.2&&decide (Disjoint t.1.1 t.1.2/\
   (({a,b}:Fv n)⊆t.1.1\/({a,b}:Fv n)⊆t.1.2)))).length
  let q:=(c.filter (fun t=>!t.2&&decide (Disjoint t.1.1 t.1.2/\
   (({a,b}:Fv n)⊆t.1.1\/({a,b}:Fv n)⊆t.1.2)))).length
  fe (Z (un b.val) (Z (un a.val) (Z (un n) (Z (un c.length) s))))=dT (eV (un c.length)) (un ((2*c.length+1)+p-q)):=by
  intro a b p q;simp only[fe,left,right,G]
  have a4:kk (bX mr [true] (un c.length) (Z (un n) (Z s (Z (un a.val) (un b.val)))))=un p:=by
   rw[bA mr [true] (un c.length) _ (fun _ _=>by simp[mr,eM]),J]
   have S:(List.range c.length).flatMap (fun t=>mr (Z (un t) (Z (un n) (Z s (Z (un a.val) (un b.val))))))=c.flatMap (fun x=>[x.2&&decide (Disjoint x.1.1 x.1.2/\(({a,b}:Fv n)⊆x.1.1\/({a,b}:Fv n)⊆x.1.2))]):=by
    have v:c=(List.range c.length).map (fun t=>c.getD t ((∅,∅),false)):=(by apply jD;{simp};{intro t B _;simp only[kJ,mH];exact (cQ _ _ B).symm});conv_rhs=>rw[v,nP]
    refine dG fun t B=>?_;have K:t<c.length:=aY.mp B;rw[cQ _ _ K];have o:=o4 c t K;dsimp only at o;simp only[mr,left,right,G,s,o.1,o.2.1,o.2.2,a0,dx,ew]
   rw[S,jV]
  have a5:kk (bX mn [true] (un c.length) (Z (un n) (Z s (Z (un a.val) (un b.val)))))=un q:=by
   rw[bA mn [true] (un c.length) _ (fun _ _=>by simp[mn,eM]),J]
   have S:(List.range c.length).flatMap (fun t=>mn (Z (un t) (Z (un n) (Z s (Z (un a.val) (un b.val))))))=c.flatMap (fun x=>[!x.2&&decide (Disjoint x.1.1 x.1.2/\(({a,b}:Fv n)⊆x.1.1\/({a,b}:Fv n)⊆x.1.2))]):=by
    have v:c=(List.range c.length).map (fun t=>c.getD t ((∅,∅),false)):=(by apply jD;{simp};{intro t B _;simp only[kJ,mH];exact (cQ _ _ B).symm});conv_rhs=>rw[v,nP]
    refine dG fun t B=>?_;have K:t<c.length:=aY.mp B;rw[cQ _ _ K];have o:=o4 c t K;dsimp only at o;simp only[mn,left,right,G,s,o.1,o.2.1,o.2.2,a0,hY,dx,ew]
   rw[S,jV]
  rw[a4,a5];have hD:(un c.length++un c.length++[true])++un p=un ((2*c.length+1)+p):=(by change (un c.length++un c.length++un 1)++un p=un ((2*c.length+1)+p);simp only[un,<- o9];congr 1;omega);rw[hD,vK]
 have a9:eV (un c.length)=un (3*c.length+1):=(by change un c.length++un c.length++un c.length++un 1=un (3*c.length+1);simp only[un,<- o9];congr 1;omega)
 have a1:eN (eV (un c.length)) (jI (un n) (un i.val) (un j.val)) (hN (un n) (un c.length) s)=fe (Z (un j.val) (Z (un i.val) (Z (un n) (Z (un c.length) s)))):=by
  let w:=eV (un c.length);have e:∀ a b,(fe (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) s))))).length=w.length:=fun _ _=>by simp only[fe,left,right,G];exact qd _ _
  have a2:∀ a,(jc (Z (un a) (Z (un n) (Z (un c.length) s)))).length=(dS (un n) w).length:=fun a=>by
   simp only[jc,left,right,G];rw[bA fe w (un n) _ (fun b _=>(e a b).le),J,gx];have af:(List.range n).map (fun b=>(fe (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) s))))).length)=(List.range n).map (fun _=>w.length):=dF (fun b _=>e a b);rw[af];simp[dS,J]
  have L:hN (un n) (un c.length) s=(List.range n).flatMap (fun a=>(List.range n).flatMap (fun b=>fe (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) s)))))):=(by unfold hN;rw[bA jc (dS (un n) w) (un n) _ (fun a _=>(a2 a).le),J];refine dG fun a _=>?_;simp only[jc,left,right,G];rw[bA fe w (un n) _ (fun b _=>(e a b).le),J]);rw[L,kg];have a8:(List.range n).flatMap (fun a=>(List.range n).flatMap (fun b=>fe (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) s))))))=((List.range n).flatMap (fun a=>(List.range n).map (fun b=>(a,b)))).flatMap (fun p=>fe (Z (un p.2) (Z (un p.1) (Z (un n) (Z (un c.length) s))))):=(by rw[gg];refine dG fun a _=>?_;rw[nP]);rw[a8];have h:i.val*n+j.val<((List.range n).flatMap (fun a=>(List.range n).map (fun b=>(a,b)))).length:=(by simp only[gx,ft,lx,List.map_const',sum_replicate,n0];nlinarith [i.isLt,j.isLt]);rw[fo _ _ w (i.val*n+j.val) h (fun p _=>e p.1 p.2)]
  have ah:((List.range n).flatMap (fun a=>(List.range n).map (fun b=>(a,b))))[i.val*n+j.val]'h=(i.val,j.val):=by
   have ai:∀(r:Nat) (a b:Nat),a<r->b<n->((List.range r).flatMap (fun x=>(List.range n).map (fun y=>(x,y)))).getD (a*n+b) (0,0)=(a,b):=by
    intro r;induction r with
    | zero=>intro a _ Q;omega
    | succ r ih=>intro a b Q P;rw[nQ,mJ,eY,flatMap_nil,cR];have d:((List.range r).flatMap (fun x=>(List.range n).map (fun y=>(x,y)))).length=r*n:=(by simp[gx]);have a7:((List.range n).map (fun y=>(r,y))).length=n:=(by simp);by_cases al:a<r;{have ag:a*n+b<r*n:=(by nlinarith);rw[cQ _ _ (by rw[dL,d];omega),uI (by rw[d];exact ag),<- cQ _ (0,0) (by rw[d];exact ag)];exact ih a b al P};{have am:a=r:=(by omega);subst am;rw[cQ _ _ (by rw[dL,d,a7];omega),sx (by rw[d];omega)];simp[d]}
   rw[<- cQ _ (0,0) h];exact ai n i.val j.val i.isLt j.isLt
  rw[ah]
 unfold fa;rw[a1,z i j,a9];have aj:(2*c.length+1)+M-aa<=3*c.length+1:=(by have hp:M<=c.length:=qE _ _;omega);exact kz (3*c.length+1) _ aj
def lh(b h e d c:LB):LB:=dT b h++dT b e++dT b d++dT b c
lemma w3{n a b c d:LB->LB}(e:U n)(j:U a)(i:U b)(h:U c)(hd:U d):U (fun s=>lh (n s) (a s) (b s) (c s) (d s)):=aC (aC (aC (qu e j) (qu e i)) (qu e h)) (qu e hd)
lemma rR(b h e d c:LB):(lh b h e d c).length=4*b.length:=by simp only[lh,dL,qd];omega
def od(e b i d c h:LB):LB:=gz (gz (gz (lQ i c) (lQ c d)) (lQ d h)) (gz (dQ (jI e i d) b) (dQ (jI e c h) b))
lemma s8{n q a b c d:LB->LB}(i:U n)(o:U q)(j:U a)(h:U b)(e:U c)(hd:U d):U (fun s=>od (n s) (q s) (a s) (b s) (c s) (d s)):=fN (fN (fN (na j e) (na e h)) (na h hd)) (fN (dK (k3 i j h) o) (dK (k3 i e hd) o))
def oc(s:LB):LB:=
 let j:=left s;let h:=right s;let o:=left h;let e:=right h;let q:=left e;let d:=right e;let r:=left d;let c:=right d;let i:=left c;let b:=right c
 gT (od i b r q o j) [] (lh i r q o j)
def ob(s:LB):LB:=
 let h:=left s;let c:=right s;let i:=left c;let d:=right c;let j:=left d;let e:=right d;let b:=left e
 bX oc (b++b++b++b) b (Z h c)
def oa(s:LB):LB:=
 let e:=left s;let c:=right s;let h:=left c;let d:=right c;let b:=left d
 bX ob (dS b (b++b++b++b)) b (Z e c)
def pG(s:LB):LB:=
 let d:=left s;let c:=right s;let b:=left c
 bX oa (dS b (dS b (b++b++b++b))) b (Z d c)
def eD(b c:LB):LB:=bX pG (dS b (dS b (dS b (b++b++b++b)))) b (Z b c)
def p0(s:LB):LB:=
 let j:=left s;let h:=right s;let o:=left h;let e:=right h;let q:=left e;let d:=right e;let r:=left d;let c:=right d;let i:=left c;let b:=right c
 gT (od i b r q o j) [] [true]
def pZ(s:LB):LB:=
 let h:=left s;let b:=right s;let i:=left b;let c:=right b;let j:=left c;let d:=right c;let e:=left d
 bX p0 [true] e (Z h b)
def pY(s:LB):LB:=
 let e:=left s;let b:=right s;let h:=left b;let d:=right b;let c:=left d
 bX pZ c c (Z e b)
def ry(s:LB):LB:=
 let d:=left s;let c:=right s;let b:=left c
 bX pY (dS b b) b (Z d c)
def gO(c b:LB):LB:=bX ry (dS c (dS c c)) c (Z c b)
lemma xB:U oc:=by have hd:=aD aR;have e:=Y aR;have i:=aD e;have d:=Y e;have j:=aD d;have c:=Y d;have o:=aD c;have b:=Y c;have h:=aD b;have q:=Y b;exact cY (s8 h q o j i hd) (aG []) (w3 h o j i hd)
lemma xA:U ob:=by have e:=aD aR;have b:=Y aR;have c:=aD (Y (Y b));have d:=aC (aC (aC c c) c) c;exact bW xB d c (D e b)
lemma xy:U oa:=by have e:=aD aR;have c:=Y aR;have b:=aD (Y c);have d:=aC (aC (aC b b) b) b;exact bW xA (jW b d) b (D e c)
lemma xw:U pG:=by have e:=aD aR;have c:=Y aR;have b:=aD c;have d:=aC (aC (aC b b) b) b;exact bW xy (jW b (jW b d)) b (D e c)
lemma q6{n d:LB->LB}(b:U n)(e:U d):U (fun s=>eD (n s) (d s)):=by have c:=aC (aC (aC b b) b) b;exact bW xw (jW b (jW b (jW b c))) b (D b e)
lemma yp:U p0:=by have hd:=aD aR;have e:=Y aR;have i:=aD e;have d:=Y e;have j:=aD d;have c:=Y d;have o:=aD c;have b:=Y c;have h:=aD b;have q:=Y b;exact cY (s8 h q o j i hd) (aG []) (aG [true])
lemma yo:U pZ:=by have d:=aD aR;have b:=Y aR;have c:=aD (Y (Y b));exact bW yp (aG [true]) c (D d b)
lemma ym:U pY:=by have d:=aD aR;have b:=Y aR;have c:=aD (Y b);exact bW yo c c (D d b)
lemma yl:U ry:=by have d:=aD aR;have b:=Y aR;have c:=aD b;exact bW ym (jW c c) c (D d b)
lemma nk{n c:LB->LB}(b:U n)(d:U c):U (fun s=>gO (n s) (c s)):=bW yl (jW b (jW b b)) b (D b d)
def n9(s:LB):LB:=
 let e:=left s;let c:=right s;let h:=left c;let b:=left (right c);let d:=right (right c)
 iX (wL (dQ (jI h e d) b) (dQ (jI h d e) b))
lemma xu:U n9:=by have d:=aD aR;have b:=Y aR;have e:=aD b;have h:=aD (Y b);have c:=Y (Y b);exact i3 (r6 (dK (k3 e d c) h) (dK (k3 e c d) h))
def my(c b d:LB):LB:=mT (bX n9 [true] c (Z c (Z b d)))
lemma mh{n F v:LB->LB}(b:U n)(d:U F)(c:U v):U (fun s=>my (n s) (F s) (v s)):=pX (bW xu (aG [true]) b (D b (D d c)))
def jt(c b o j i h:LB):LB:=
 let e:=wL (dQ (jI c o j) b)
  (gz (mc (my c b o)) (mc (my c b j)))
 let d:=wL (dQ (jI c i h) b)
  (gz (mc (my c b i)) (mc (my c b h)))
 gz e d
lemma rN{n F a b c d:LB->LB}(e:U n)(h:U F)(o:U a)(j:U b)(i:U c)(hd:U d):U (fun s=>jt (n s) (F s) (a s) (b s) (c s) (d s)):=fN (r6 (dK (k3 e o j) h) (fN (kt (mh e h o)) (kt (mh e h j)))) (r6 (dK (k3 e i hd) h) (fN (kt (mh e h i)) (kt (mh e h hd))))
def iV(s:LB):LB:=
 let e:=left s;let u:=right s;let h:=left u;let r:=right u;let v:=left r;let q:=right r;let b:=left q;let o:=right q;let z:=left o;let j:=right o;let y:=left j;let i:=right j;let x:=left i;let w:=right i;let d:=gz (p5 h z) (p5 e y);let c:=gz (p5 h x) (p5 e w)
 iX (wL (dQ (jI v h e) b) (wL d c))
def kr(s:LB):LB:=
 let d:=left s;let b:=right s;let c:=left b
 bX iV [true] c (Z d b)
def ij(c b i h e d:LB):LB:=bX kr c c (Z c (Z b (Z i (Z h (Z e d)))))
lemma vg:U iV:=by have j:=aD aR;have i:=Y aR;have o:=aD i;have h:=Y i;have q:=aD h;have e:=Y h;have v:=aD e;have d:=Y e;have u:=aD d;have c:=Y d;have s:=aD c;have b:=Y c;have r:=aD b;have hd:=Y b;exact i3 (r6 (dK (k3 q o j) v) (r6 (fN (oW o u) (oW j s)) (fN (oW o r) (oW j hd))))
lemma vf:U kr:=bW vg (aG [true]) (aD (Y aR)) (D (aD aR) (Y aR))
lemma ve{n F a b c d:LB->LB}(e:U n)(o:U F)(j:U a)(i:U b)(h:U c)(hd:U d):U (fun s=>ij (n s) (F s) (a s) (b s) (c s) (d s)):=bW vf e e (D e (D o (D j (D i (D h hd)))))
def dZ(b c:LB):LB:=(b++[true])++dS c c
def h7(s:LB):LB:=
 let i:=left s;let u:=right s;let d:=left u;let r:=right u;let c:=left r;let q:=right r;let h:=left q;let o:=right q;let j:=left o;let e:=right o;let b:=eN (h++h++h++h) i e;let y:=fa h [] b;let x:=fa h [true] b;let w:=fa h [true,true] b;let v:=fa h [true,true,true] b;let z:=gz (l8 d i) (jt h c y x w v)
 gT z [] (dT (j++[true]) (i++[true])++ij h c y x w v)
def jr(s:LB):LB:=
 let q:=left s;let o:=right s;let c:=left o;let j:=right o;let h:=left j;let i:=right j;let e:=left i;let r:=right i;let d:=right r;let b:=eN (e++e++e++e) q d;let y:=fa e [] b;let x:=fa e [true] b;let w:=fa e [true,true] b;let v:=fa e [true,true,true] b;let u:=gz (l8 c q) (jt e h y x w v)
 gT u [] [true]
def gU(s:LB):LB:=
 let u:=left s;let o:=right s;let c:=left o;let j:=right o;let r:=left j;let q:=right j;let d:=left q;let h:=dZ d r;let i:=eN h u c;let b:=kk (gY (d++[true]) i);let e:=fO (d++[true]) i
 bX h7 h d (Z b (Z e j))
def iG(s:LB):LB:=
 let u:=left s;let o:=right s;let c:=left o;let j:=right o;let r:=left j;let q:=right j;let d:=left q;let i:=dZ d r;let h:=eN i u c;let b:=kk (gY (d++[true]) h);let e:=fO (d++[true]) h
 bX jr [true] d (Z b (Z e j))
def ru(s:LB):LB:=
 let args:=left (right s);let d:=right (right s);let o:=left args;let h:=left (right args);let j:=left d;let c:=right d;let i:=dZ h o;let e:=bX iG h j (Z c args);let b:=bX gU (dS h i) j (Z c args)
 Z e b
def s6(e h d b i:LB):LB:=
 let c:=dT (d++[true]) []++fJ (dS h h)
 km f5 ru e i (Z h (Z d b)) (Z [true] c)
lemma rD:U h7:=by have j:=aD aR;have i:=Y aR;have q:=aD i;have h:=Y i;have y:=aD h;have e:=Y h;have c:=aD e;have d:=Y e;have z:=aD d;have r:=Y d;have u:=aC (aC (aC c c) c) c;have b:=ku u j r;have x:=i4 c (aG []) b;have w:=i4 c (aG [true]) b;have v:=i4 c (aG [true,true]) b;have hd:=i4 c (aG [true,true,true]) b;have o:=fN (oY q j) (rN c y x w v hd);have s:=aC z (aG [true]);exact cY o (aG []) (aC (qu s (aC j (aG [true]))) (ve c y x w v hd))
lemma tO:U jr:=by have r:=aD aR;have h:=Y aR;have j:=aD h;have e:=Y h;have w:=aD e;have d:=Y e;have c:=aD d;have i:=Y d;have o:=Y i;have q:=aC (aC (aC c c) c) c;have b:=ku q r o;have v:=i4 c (aG []) b;have u:=i4 c (aG [true]) b;have s:=i4 c (aG [true,true]) b;have hd:=i4 c (aG [true,true,true]) b;exact cY (fN (oY j r) (rN c w v u s hd)) (aG []) (aG [true])
lemma rE:U gU:=by have r:=aD aR;have h:=Y aR;have i:=aD h;have c:=Y h;have o:=aD c;have q:=aD (Y c);have d:=aC q (aG [true]);have e:=aC d (jW o o);have b:=ku e r i;have j:=aH (sf d b) uc;have s:=gW d b;exact bW rD e q (D j (D s c))
lemma tP:U iG:=by have r:=aD aR;have e:=Y aR;have h:=aD e;have c:=Y e;have o:=aD c;have q:=aD (Y c);have d:=aC q (aG [true]);have i:=aC d (jW o o);have b:=ku i r h;have j:=aH (sf d b) uc;have s:=gW d b;exact bW tO (aG [true]) q (D j (D s c))
lemma yM:U ru:=by have b:=aD (Y aR);have e:=Y (Y aR);have j:=aD b;have i:=aD (Y b);have d:=aD e;have c:=Y e;have h:=aC (aC i (aG [true])) (jW j j);exact D (bW tP i d (D c b)) (bW rE (jW i h) d (D c b))
lemma xt{c n o j r:LB->LB}(d:U c)(e:U n)(i:U o)(h:U j)(q:U r):U (fun s=>s6 (c s) (n s) (o s) (j s) (r s)):=by have b:=D (aG [true]) (aC (qu (aC i (aG [true])) (aG [])) (aH (jW e e) g2));exact mA oV m2 yM d q (D e (D i h)) b
def iW(s:LB):LB:=
 let c:=left s;let h:=right s;let i:=left h;let e:=right h;let b:=left e;let d:=right e;let o:=left d;let j:=right d
 iX (gz (gz (lQ o c) (lQ c j)) (my i b c))
lemma vi:U iW:=by have e:=aD aR;have d:=Y aR;have h:=aD d;have c:=Y d;have o:=aD c;have b:=Y c;have j:=aD b;have i:=Y b;exact i3 (fN (fN (na j e) (na e i)) (mh h o e))
def ot(K q P v e c i o j d w:LB):LB:=
 let x:=lQ o q;let h:=lQ j q;let E:=gT (lQ o j) j o;let B:=gT (lQ o j) o j;let Q:=dQ (jI q E B) v
 let a2:=gz (mc (p5 o j))
  (gz Q (gz (mc (my q c E)) (mc (my q c B))))
 let u:=tn (kk (bX iW [true] q (Z q (Z c (Z E B)))));let z:=qk (lQ j o) u;let a0:=fa (eV P) (jI q E B) e;let b:=p5 (o++j++[true]) (q++q);let a1:=mc (p5 o j);let y:=lQ j o
 let S:=gT x
  (gT h a1 b)
  (gT h b a2)
 let L:=gT x
  (gT h y [true])
  (gT h [] z)
 let M:=gT x [] (gT h [] a0);let s:=gz S (l8 M w);let r:=qk L d
 gT s (fJ K) (lV K r (eN K (rX w M) i))
lemma ta{k n m ah ai F Q u v S a5:LB->LB}(M:U k)(e:U n)(K:U m)(hE:U ah)(hD:U ai)(P:U F)(a8:U Q)(q:U u)(o:U v)(ab:U S)(r:U a5):U (fun s=>ot (k s) (n s) (m s) (ah s) (ai s) (F s) (Q s) (u s) (v s) (S s) (a5 s)):=by have c:=na q e;have b:=na o e;have L:=na q o;have z:=na o q;have E:=cY L o q;have B:=cY L q o;have a1:=dK (k3 e E B) hE;have x:=fN (kt (oW q o)) (fN a1 (fN (kt (mh e P E)) (kt (mh e P B))));have a4:=aH (aH (bW vi (aG [true]) e (D e (D P (D E B)))) uc) yf;have h:=yg z a4;have ad:=aC (aC (aC K K) K) (aG [true]);have j:=i4 ad (k3 e E B) hD;have d:=oW (aC (aC q o) (aG [true])) (aC e e);have w:=kt (oW q o);have y:=cY c (cY b w d) (cY b d x);have i:=cY c (cY b z (aG [true])) (cY b (aG []) h);have a2:=cY c (aG []) (cY b (aG []) j);have a3:=fN y (oY a2 r);have a0:=yg i ab;exact cY a3 (aH M g2) (vo M a0 (ku M (wE r a2) a8))
def jM(e c b i h d:LB):LB:=eN (dS b e) (jI (c++c) h d) i
lemma t7{k n T d h u:LB->LB}(i:U k)(c:U n)(o:U T)(b:U d)(j:U h)(e:U u):U (fun s=>jM (k s) (n s) (T s) (d s) (h s) (u s)):=ku (jW o i) (k3 (aC c c) j e) b
def mj(s:LB):LB:=
 let b:=left s;let d:=right s;let i:=left d;let c:=right d;let h:=left c;let e:=right c
 gT (gz (p5 i (h++h++[true])) (p5 b [])) (fJ e) (oT e [true])
def pI(s:LB):LB:=
 let h:=left s;let d:=right s;let i:=left d;let c:=right d;let e:=left c;let b:=right c
 bX mj e b (Z h (Z i e))
def pH(s:LB):LB:=
 let i:=left s;let d:=right s;let h:=left d;let c:=right d;let e:=left c;let b:=right c
 bX pI (dS b h) (e++e) (Z i (Z h b))
def kd(d c b:LB):LB:=bX pH (dS (c++c) (dS b d)) c (Z d (Z c b))
lemma wy:U mj:=by have d:=aD aR;have c:=Y aR;have i:=aD c;have b:=Y c;have h:=aD b;have e:=Y b;exact cY (fN (oW i (aC (aC h h) (aG [true]))) (oW d (aG []))) (aH e g2) (Ay e (aG [true]))
lemma xE:U pI:=by have e:=aD aR;have c:=Y aR;have h:=aD c;have b:=Y c;have d:=aD b;have i:=Y b;exact bW wy d i (D e (D h d))
lemma xD:U pH:=by have i:=aD aR;have c:=Y aR;have e:=aD c;have b:=Y c;have d:=aD b;have h:=Y b;exact bW xE (jW h e) (aC d d) (D i (D e h))
lemma vS{k n T:LB->LB}(c:U k)(b:U n)(d:U T):U (fun s=>kd (k s) (n s) (T s)):=bW xD (jW (aC b b) (jW d c)) b (D c (D b d))
def n1(c:LB):LB:=left c
def oP(c:LB):LB:=left (right c)
def vb(c:LB):LB:=left (right (right c))
def qX(c:LB):LB:=left (right (right (right c)))
def u9(c:LB):LB:=left (right (right (right (right c))))
def u8(c:LB):LB:=left (right (right (right (right (right c)))))
def va(c:LB):LB:=right (right (right (right (right (right c)))))
def n7(s:LB):LB:=
 let e:=left s;let v:=right s;let b:=left v;let u:=right v;let y:=left u;let r:=right u;let j:=left r;let q:=right r;let c:=left q;let d:=right q;let i:=n1 b;let w:=oP b;let x:=vb b;let o:=qX b;let h:=l8 (j++j++[true]) e
 gT h (fJ i) (ot i w x (u9 b) (u8 b) (va b) (jM i w o y j e) e c (tn c) d)
def ir(s:LB):LB:=
 let e:=left s;let r:=right s;let b:=left r;let q:=right r;let w:=left q;let o:=right q;let c:=left o;let d:=right o;let i:=n1 b;let u:=oP b;let v:=vb b;let j:=qX b;let h:=l8 (c++c++[true]) e
 gT h (fJ i) (ot i u v (u9 b) (u8 b) (va b) (jM i u j w c e) e (c++c) [true] d)
def lW(s:LB):LB:=
 let c:=left s;let i:=right s;let b:=left i;let h:=right i;let r:=left h;let e:=right h;let q:=left e;let d:=right e;let o:=n1 b;let j:=oP b
 gT (lQ c q) (fJ o) (iv ir o (j++j) (Z b (Z r (Z c d))))
def ml(s:LB):LB:=
 let i:=left s;let x:=right s;let r:=left x;let w:=right x;let h:=left w;let v:=right w;let e:=left v;let y:=right v;let o:=n1 e;let u:=oP e;let q:=vy r;let d:=gz (l8 (h++h++[true]) r) (l8 (h++h++[true,true]) q)
 let j:=gT d (fJ o)
  (iv n7 o (u++u) (Z e (Z y (Z h (Z q i)))))
 let b:=p5 r (h++h++[true])
 let c:=gT b (fJ o)
  (iv lW o u (Z e (Z y (Z h i))))
 nj o j c
def pK(s:LB):LB:=
 let e:=left s;let d:=right s;let h:=left d;let c:=right d;let b:=left c
 bX ml (n1 b) (qX b) (Z e (Z h c))
def pJ(s:LB):LB:=
 let e:=left s;let c:=right s;let b:=left c;let d:=oP b
 bX pK (dS (qX b) (n1 b)) (d++d) (Z e c)
def ke(s:LB):LB:=
 let b:=left (right s);let d:=right (right s);let c:=oP b
 bX pJ (dS (c++c) (dS (qX b) (n1 b))) c (Z b d)
def g7(b:LB):LB:=
 let h:=n1 b;let c:=oP b;let d:=qX b;let e:=dS c (dS (c++c) (dS d h))
 km f5 ke e c.tail b (kd h c d)
def kY(s:LB):LB:=
 let j:=left s;let e:=right s;let b:=left e;let d:=right e;let o:=left d;let c:=right d;let i:=n1 b;let h:=oP b
 iv ir i (h++h) (Z b (Z o (Z j c)))
def qc(b d c:LB):LB:=iv kY (n1 b) (oP b) (Z b (Z d c))
lemma mz{c:LB->LB}(b:U c):U (fun s=>n1 (c s)):=aD b
lemma nv{c:LB->LB}(b:U c):U (fun s=>oP (c s)):=aD (Y b)
lemma xZ{c:LB->LB}(b:U c):U (fun s=>vb (c s)):=aD (Y (Y b))
lemma rx{c:LB->LB}(b:U c):U (fun s=>qX (c s)):=aD (Y (Y (Y b)))
lemma xX{c:LB->LB}(b:U c):U (fun s=>u9 (c s)):=aD (Y (Y (Y (Y b))))
lemma xW{c:LB->LB}(b:U c):U (fun s=>u8 (c s)):=aD (Y (Y (Y (Y (Y b)))))
lemma xY{c:LB->LB}(b:U c):U (fun s=>va (c s)):=Y (Y (Y (Y (Y (Y b)))))
lemma wu:U n7:=by have o:=aD aR;have h:=Y aR;have b:=aD h;have e:=Y h;have s:=aD e;have d:=Y e;have r:=aD d;have c:=Y d;have i:=aD c;have j:=Y c;have q:=mz b;have u:=nv b;have v:=xZ b;have w:=rx b;exact cY (oY (aC (aC r r) (aG [true])) o) (aH q g2) (ta q u v (xX b) (xW b) (xY b) (t7 q u w s r o) o i (aH i yf) j)
lemma rO:U ir:=by have j:=aD aR;have h:=Y aR;have b:=aD h;have e:=Y h;have q:=aD e;have d:=Y e;have c:=aD d;have i:=Y d;have o:=mz b;have r:=nv b;have s:=xZ b;have u:=rx b;exact cY (oY (aC (aC c c) (aG [true])) j) (aH o g2) (ta o r s (xX b) (xW b) (xY b) (t7 o r u q c j) j (aC c c) (aG [true]) i)
lemma vq:U lW:=by have h:=aD aR;have e:=Y aR;have b:=aD e;have d:=Y e;have j:=aD d;have c:=Y d;have r:=aD c;have i:=Y c;have q:=mz b;have o:=nv b;exact cY (na h r) (aH q g2) (kb rO q (aC o o) (D b (D j (D h i))))
lemma wz:U ml:=by have d:=aD aR;have o:=Y aR;have x:=aD o;have j:=Y o;have w:=aD j;have i:=Y j;have b:=aD i;have v:=Y i;have s:=mz b;have y:=nv b;have u:=yK x;have h:=aC w w;have r:=fN (oY (aC h (aG [true])) x) (oY (aC h (aG [true,true])) u);have e:=cY r (aH s g2) (kb wu s (aC y y) (D b (D v (D w (D u d)))));have q:=oW x (aC h (aG [true]));have c:=cY q (aH s g2) (kb vq s y (D b (D v (D w d))));exact Az s e c
lemma xG:U pK:=by have e:=aD aR;have d:=Y aR;have h:=aD d;have c:=Y d;have b:=aD c;exact bW wz (mz b) (rx b) (D e (D h c))
lemma xF:U pJ:=by have e:=aD aR;have c:=Y aR;have b:=aD c;have d:=nv b;exact bW xG (jW (rx b) (mz b)) (aC d d) (D e c)
lemma wA:U ke:=by have b:=aD (Y aR);have d:=Y (Y aR);have c:=nv b;exact bW xF (jW (aC c c) (jW (rx b) (mz b))) c (D b d)
lemma vl{c:LB->LB}(e:U c):U (fun s=>g7 (c s)):=by have h:=mz e;have b:=nv e;have i:=rx e;have d:=jW b (jW (aC b b) (jW i h));exact mA oV m2 wA d (wF b) e (vS h b i)
lemma uo:U kY:=by have o:=aD aR;have d:=Y aR;have b:=aD d;have c:=Y d;have h:=aD c;have e:=Y c;have j:=mz b;have i:=nv b;exact kb rO j (aC i i) (D b (D h (D o e)))
lemma wD{c i d:LB->LB}(h:U c)(e:U i)(b:U d):U (fun s=>qc (c s) (i s) (d s)):=kb uo (mz h) (nv h) (D h (D e b))
def k7(s:LB):LB:=
 let o:=left s;let i:=right s;let q:=left i;let h:=right i;let j:=left h;let e:=right h;let r:=left e;let d:=right e;let c:=left d;let b:=right d
 gT (dQ (jI j q o) b) [] (fa (eV r) (jI j q o) c)
def mi(s:LB):LB:=
 let e:=left s;let b:=right s;let c:=left b;let d:=left (right b)
 bX k7 (eV d) c (Z e b)
def yb(c e d b:LB):LB:=bX mi (dS c (eV e)) c (Z c (Z e (Z d b)))
def rA(c b:LB):LB:=tn (gO c b)
lemma wx:U k7:=by have o:=aD aR;have e:=Y aR;have q:=aD e;have d:=Y e;have j:=aD d;have c:=Y d;have h:=aD c;have b:=Y c;have s:=aD b;have r:=Y b;have i:=aC (aC (aC h h) h) (aG [true]);exact cY (dK (k3 j q o) r) (aG []) (i4 i (k3 j q o) s)
lemma ww:U mi:=by have h:=aD aR;have b:=Y aR;have e:=aD b;have c:=aD (Y b);have d:=aC (aC (aC c c) c) (aG [true]);exact bW wx d e (D h b)
lemma za{n m e F:LB->LB}(c:U n)(b:U m)(i:U e)(h:U F):U (fun s=>yb (n s) (m s) (e s) (F s)):=by have d:=aC (aC (aC b b) b) (aG [true]);exact bW ww (jW c d) c (D c (D b (D i h)))
lemma w1{n F:LB->LB}(b:U n)(c:U F):U (fun s=>rA (n s) (F s)):=aH (nk b c) yf
def uE(c:LB):LB:=left c
def rQ(c:LB):LB:=left (right c)
def w7(c:LB):LB:=left (right (right c))
def t8(c:LB):LB:=left (right (right (right c)))
def x8(c:LB):LB:=left (right (right (right (right c))))
def x7(c:LB):LB:=left (right (right (right (right (right c)))))
def x6(c:LB):LB:=left (right (right (right (right (right (right c))))))
def tc(c:LB):LB:=left (right (right (right (right (right (right (right c)))))))
def w8(c:LB):LB:=left (right (right (right (right (right (right (right (right c))))))))
def wI(c:LB):LB:=right (right (right (right (right (right (right (right (right c))))))))
lemma yq{c:LB->LB}(b:U c):U (fun s=>uE (c s)):=aD b
lemma s9{c:LB->LB}(b:U c):U (fun s=>rQ (c s)):=aD (Y b)
lemma x3{c:LB->LB}(b:U c):U (fun s=>w7 (c s)):=aD (Y (Y b))
lemma wv{c:LB->LB}(b:U c):U (fun s=>t8 (c s)):=aD (Y (Y (Y b)))
lemma y9{c:LB->LB}(b:U c):U (fun s=>x8 (c s)):=aD (Y (Y (Y (Y b))))
lemma y8{c:LB->LB}(b:U c):U (fun s=>x7 (c s)):=aD (Y (Y (Y (Y (Y b)))))
lemma y7{c:LB->LB}(b:U c):U (fun s=>x6 (c s)):=aD (Y (Y (Y (Y (Y (Y b))))))
lemma xC{c:LB->LB}(b:U c):U (fun s=>tc (c s)):=aD (Y (Y (Y (Y (Y (Y (Y b)))))))
lemma x4{c:LB->LB}(b:U c):U (fun s=>w8 (c s)):=aD (Y (Y (Y (Y (Y (Y (Y (Y b))))))))
lemma yI{c:LB->LB}(b:U c):U (fun s=>wI (c s)):=Y (Y (Y (Y (Y (Y (Y (Y (Y b))))))))
def og(s:LB):LB:=
 let x:=left s;let P:=right s;let c:=left P;let M:=right P;let e:=left M;let K:=right M;let h:=left K;let o:=right K;let E:=rQ c;let B:=w7 c;let Q:=t8 c;let S:=x8 c;let j:=x7 c;let L:=x6 c;let u:=tc c;let z:=w8 c;let v:=dZ z B;let w:=eN v x e;let b:=fO (z++[true]) w;let d:=u++yb B Q L b
 gT (l8 d o) (fJ E) (let y:=Z E (Z B (Z Q (Z S (Z j (Z L b)))))
  let r:=g7 y;let q:=qc y r (rX o d);let i:=lV E (rA B b) h
  rk E i q)
def oh(s:LB):LB:=
 let o:=left s;let q:=right s;let d:=left q;let i:=right q;let j:=rQ d;let b:=s6 (uE d) (w7 d) (w8 d) (wI d) o;let h:=left b;let c:=right b;let e:=rV j (ti j (oT j [true,true])) o
 iv og j h (Z d (Z c (Z e i)))
def mY(b c:LB):LB:=iv oh (rQ b) (rQ b) (Z b c)
def i0(s:LB):LB:=
 let i:=left s;let d:=right s;let h:=left d;let b:=right d;let e:=t8 b;let c:=e++e++[true]
 mY b (dS h c++i)
def ky(s:LB):LB:=
 let c:=left s;let b:=right s
 bX i0 (rQ b) (t8 b++[true]) (Z c b)
def solve(s:LB):LB:=
 let v:=hd s;let x:=jy s;let w:=hd x;let M:=jy x;let q:=hd M;let K:=jy M;let y:=hd K;let E:=jy K;let c:=dS y (q++q);let d:=gY c E;let B:=fO c E;let r:=hd B;let b:=jy B;let h:=vu q;let j:=fJ (dS (dS (h++[true]) (r++[true])) w);let P:=r++r++[true];let L:=dS h P++r++[true];let e:=jP q y d;let Q:=hN q r b;let u:=mV q r b;let S:=gO q e;let i:=eD q e;let z:=Z v (Z w (Z q (Z r (Z L (Z e (Z Q (Z u (Z S i))))))));let o:=bX ky (dS (r++[true]) w) (h++[true]) z
 gT (kT q y d) o j
lemma wB:U og:=by have y:=aD aR;have w:=Y aR;have b:=aD w;have v:=Y w;have q:=aD v;have u:=Y v;have j:=aD u;have h:=Y u;have L:=s9 b;have x:=x3 b;have E:=wv b;have M:=y9 b;have Q:=y8 b;have K:=y7 b;have o:=xC b;have P:=x4 b;have z:=aC P (aG [true]);have S:=aC z (jW x x);have s:=ku S y q;have B:=gW z s;have r:=aC o (za x E K B);have i:=D L (D x (D E (D M (D Q (D K B)))));have e:=vl i;have d:=wD i e (wE h r);have c:=vo L (w1 x B) j;exact cY (oY r h) (aH L g2) (CO L c d)
lemma wC:U oh:=by have j:=aD aR;have c:=Y aR;have b:=aD c;have e:=Y c;have i:=s9 b;have h:=xt (yq b) (x3 b) (x4 b) (yI b) j;have d:=CE i (zZ i (Ay i (aG [true,true]))) j;exact kb wB i (aD h) (D b (D (Y h) (D d e)))
lemma xH{c d:LB->LB}(b:U c)(hd:U d):U (fun s=>mY (c s) (d s)):=kb wC (s9 b) (s9 b) (D b hd)
lemma vm:U i0:=by have h:=aD aR;have c:=Y aR;have e:=aD c;have b:=Y c;have d:=wv b;have i:=aC (aC d d) (aG [true]);exact xH b (aC (jW e i) h)
lemma vn:U ky:=by have c:=aD aR;have b:=Y aR;exact bW vm (s9 b) (aC (wv b) (aG [true])) (D c b)
lemma yL:U solve:=by have w:=mB;have M:=k6;have B:=aH M mB;have v:=aH M k6;have e:=aH v mB;have u:=aH v k6;have E:=aH u mB;have s:=aH u k6;have c:=jW E (aC e e);have y:=sf c s;have r:=gW c s;have i:=aH r mB;have q:=aH r k6;have d:=aH e yJ;have b:=aC d (aG [true]);have x:=aC i (aG [true]);have h:=aH (jW (jW b x) B) g2;have S:=aC (aC i i) (aG [true]);have P:=aC (aC (jW d S) i) (aG [true]);have K:=yk e E y;have L:=tN e i q;have o:=vR e i q;have Q:=nk e K;have a2:=q6 e K;have z:=D w (D B (D e (D i (D P (D K (D L (D o (D Q a2))))))));have j:=bW vn (jW x B) b z;exact cY (um e E y) j h
open MathCore Finset
lemma s5(m:Nat):fJ (un m)=replicate m false:=by induction m with|zero=>{rfl}|succ m b=>{simp[un,mI,fJ]}
lemma g6(a b:Nat):un a++un b=un (a+b):=by simp only[un,o9]
lemma eR(a:Nat):un a++[true]=un (a+1):=by change un a++un 1=un (a+1);exact g6 a 1
lemma mw(a:Nat):un a++un a=un (2*a):=by rw[g6,two_mul]
lemma nh(a:Nat):un a++un a++[true]=un (2*a+1):=by rw[mw,eR]
lemma tZ(a:Nat):un a++un a++[true,true]=un (2*a+2):=by rw[mw];change un (2*a)++un 2=un (2*a+2);exact g6 (2*a) 2
lemma gS(a b:Nat):dS (un a) (un b)=un (a*b):=by simp only[dS,J]
lemma bY{b d:Type*}(L:Ls b)(f:b->Ls d)(c:Nat)(h:∀ x∈L,(f x).length<=c):(L.flatMap f).length<=L.length*c:=by induction L with|nil=>{simp}|cons a L e=>{simp only[eY,dL,aX,qU];have o:=h a (by simp);have j:=e (fun x i=>h x (by simp[i]));omega}
lemma gq{b:Type*}(L:Ls b):L.flatMap (fun _=>[true])=un L.length:=by induction L with|nil=>{rfl}|cons a L c=>{simp[eY,c,rv]}
lemma r8(n:Nat)(f:Nat->Nat->Bo):let c:=(List.range n).flatMap (fun a=>(List.range n).flatMap (fun b=>[f a b]))
 c.length=n*n/\∀ i j,i<n->j<n->c.getD (i*n+j) false=f i j:=by
 intro c
 have e:∀ a,((List.range n).flatMap (fun b=>[f a b])).length=n:=fun a=>by
  simp[gx]
 have d:c.length=n*n:=(by rw[show c=(List.range n).flatMap (fun a=>(List.range n).flatMap (fun b=>[f a b])) from rfl,gx];have s:(List.range n).map (fun a=>((List.range n).flatMap (fun b=>[f a b])).length)=(List.range n).map (fun _=>n):=dF (fun a _=>e a);rw[s];simp);refine⟨d,fun i j v u=>?_⟩;have r:i*n+j<n*n:=(by nlinarith);have h:c.getD (i*n+j) false=(eN [true] (un j) (eN (un n) (un i) c)).getD 0 false:=(by simp only[eN,J,lv,j9,Nat.mul_comm n i];rw[cQ _ _ (by rw[d];exact r),cQ _ _ (by simp[d];omega)];simp[List.getElem_take,List.getElem_drop]);have q:eN (un n) (un i) c=(List.range n).flatMap (fun b=>[f i b]):=(by unfold c;rw[fo (List.range n) (fun a=>(List.range n).flatMap (fun b=>[f a b])) (un n) i (by simp[v]) (fun a _=>by rw[J];exact e a)];simp);have o:eN [true] (un j) ((List.range n).flatMap (fun b=>[f i b]))=[f i j]:=(by rw[fo (List.range n) (fun b=>[f i b]) [true] j (by simp[u]) (fun _ _=>rfl)];simp);rw[h,q,o];rfl
def dA{n:Nat}(F:ES n)(b:LB):Prop:=b.length=n*n/\∀ i j:Fin n,b.getD (i.val*n+j.val) false=decide ((i,j)∈F)
lemma r0{n:Nat}(b:Ls (Fv n×Fv n)):let c:=(gX n).toFinset.filter (fun e=>∀ z∈b,¬(aF e⊆z.1)/\¬(aF e⊆z.2))
 dA c (jP (un n) (un b.length) (b.flatMap (fun z=>aK z.1++aK z.2))):=by
 intro c;refine⟨by rw[t6,J],fun i j=>?_⟩;rw[wt b i j];apply Bool.eq_iff_iff.mpr;simp[c,gR,aF]
lemma s4(n:Nat):dA (∅:ES n) (fJ (dS (un n) (un n))):=by rw[gS,s5];refine⟨by simp,fun i j=>?_⟩;have b:i.val*n+j.val<n*n:=(by nlinarith [i.isLt,j.isLt]);rw[cQ _ _ (by simp[b]),List.getElem_replicate];simp
lemma k5{n:Nat}{F:ES n}{b:LB}(h:dA F b)(v:Fin n):my (un n) b (un v.val)=cF (decide (v∈F.biUnion aF)):=by
 unfold my;rw[bA n9 [true] (un n) _ (fun _ _=>by simp[n9,eM]),oO,J];congr 1;apply Bool.eq_iff_iff.mpr;simp only[cG,gM,aY,bT];constructor
 ·
  rintro⟨u,d,c⟩;simp only[n9,left,right,G,kg,eG,J,h.2 ⟨u,d⟩ v,h.2 v ⟨u,d⟩,jz,ew,eZ] at c;have i:(decide ((⟨u,d⟩,v)∈F)||decide ((v,⟨u,d⟩)∈F))=true:=c.symm;simp only[kN,cG] at i;rcases i with i|i
  {exact⟨(⟨u,d⟩,v),i,by simp[aF]⟩};{exact⟨(v,⟨u,d⟩),i,by simp[aF]⟩}
 ·
  rintro⟨e,o,j⟩;simp only[aF,aV,bI] at j;rcases j with rfl|rfl
  {refine⟨e.2.val,e.2.isLt,?_⟩;simp only[n9,left,right,G,kg,eG,J,h.2 e.2 e.1,h.2 e.1 e.2,jz,ew,eZ];simp[o]};{refine⟨e.1.val,e.1.isLt,?_⟩;simp only[n9,left,right,G,kg,eG,J,h.2 e.1 e.2,h.2 e.2 e.1,jz,ew,eZ];simp[o]}
lemma u7{n:Nat}{F:ES n}{r:LB}(B:dA F r)(s:aQ F){a b c d:Fin n}(o:eS (a,b) (c,d)):jt (un n) r (un a.val) (un b.val) (un c.val) (un d.val)=cF (decide (aQ (F ∪ {(a,b),(c,d)}))):=by
 have a7:a<b:=hK o.1 o.2.1;have a4:c<d:=hK o.2.1 o.2.2
 have i:Disjoint (aF (a,b)) (aF (c,d)):=by
  rw[aT];intro x Q S;simp only[aF,aV,bI] at Q S;rcases Q with rfl|rfl <;> rcases S with h|h <;>
   first|exact bS o.1 h|exact bS (hK o.1 (hK o.2.1 o.2.2)) h
        | exact bS o.2.1 h.symm|exact bS o.2.2 h
 simp only[jt,kg,eG,J,B.2 a b,B.2 c d,k5 B a,k5 B b,k5 B c,k5 B d,hY,dx,jz];congr 1;apply Bool.eq_iff_iff.mpr;simp only[gy,kN,sP,cG,qD,bT,not_exists,not_and];constructor
 ·
  rintro⟨y,w⟩;refine⟨?_,?_⟩
  ·
   intro e j;simp only[cD,aV,bI] at j;rcases j with j|rfl|rfl
   {exact s.1 e j};{exact a7};{exact a4}
  ·
   intro e j f v q;simp only[cD,aV,bI] at j v;rcases j with j|rfl|rfl <;> rcases v with v|rfl|rfl
   {exact s.2 e j f v q}
   ·
    rcases y with L|⟨P,M⟩
    {exact s.2 e j (a,b) L q}
    ·
     rw[lD];intro x u;simp only[aF,aV,bI] at u;rcases u with rfl|rfl
     {exact P e j};{exact M e j}
   ·
    rcases w with z|⟨K,hd⟩
    {exact s.2 e j (c,d) z q}
    ·
     rw[lD];intro x u;simp only[aF,aV,bI] at u;rcases u with rfl|rfl
     {exact K e j};{exact hd e j}
   ·
    rcases y with L|⟨P,M⟩
    {exact s.2 (a,b) L f v q}
    ·
     rw[aT];intro x u;simp only[aF,aV,bI] at u;rcases u with rfl|rfl
     {exact P f v};{exact M f v}
   {exact (q rfl).elim};{exact i}
   ·
    rcases w with z|⟨K,hd⟩
    {exact s.2 (c,d) z f v q}
    ·
     rw[aT];intro x u;simp only[aF,aV,bI] at u;rcases u with rfl|rfl
     {exact K f v};{exact hd f v}
   {exact i.symm};{exact (q rfl).elim}
 {intro E;constructor;{by_cases L:(a,b)∈F;{exact Or.inl L};{right;constructor <;> intro e j;{exact aT.mp (E.2 (a,b) (by simp) e (ga _ j) (fun h=>L (h▸j))) (by simp[aF])};{exact aT.mp (E.2 (a,b) (by simp) e (ga _ j) (fun h=>L (h▸j))) (by simp[aF])}}};{by_cases z:(c,d)∈F;{exact Or.inl z};{right;constructor <;> intro e j;{exact aT.mp (E.2 (c,d) (by simp) e (ga _ j) (fun h=>z (h▸j))) (by simp[aF])};{exact aT.mp (E.2 (c,d) (by simp) e (ga _ j) (fun h=>z (h▸j))) (by simp[aF])}}}}
lemma m8{n:Nat}{F:ES n}{e:LB}(r:dA F e)(a b c d:Fin n):dA (F ∪ {(a,b),(c,d)}) (ij (un n) e (un a.val) (un b.val) (un c.val) (un d.val)):=by
 let args:=Z (un n) (Z e (Z (un a.val) (Z (un b.val) (Z (un c.val) (un d.val)))))
 have o:∀ i,(kr (Z (un i) args)).length=n:=fun i=>by
  simp only[kr,left,right,G,args];rw[bA iV [true] (un n) _ (fun _ _=>by simp[iV,eM]),J,gx];have s:∀ j∈List.range n,(iV (Z (un j) (Z (un i) args))).length=1:=fun _ _=>eM _;rw[dF s];simp
 let f:Nat->Nat->Bo:=fun i j=>
  e.getD (i*n+j) false||((decide (i=a.val)&&decide (j=b.val))||(decide (i=c.val)&&decide (j=d.val)))
 have q:ij (un n) e (un a.val) (un b.val) (un c.val) (un d.val)=(List.range n).flatMap (fun i=>(List.range n).flatMap (fun j=>[f i j])):=(by unfold ij;rw[bA kr (un n) (un n) _ (fun i _=>by rw[J];exact (o i).le),J];refine dG fun i _=>?_;simp only[kr,left,right,G];rw[bA iV [true] (un n) _ (fun _ _=>by simp[iV,eM]),J];refine dG fun j _=>?_;simp only[iV,left,right,G,kg,eG,nw,J,dx,jz,ew,f]);rw[q];have h:=r8 n f;refine⟨h.1,fun i j=>?_⟩;rw[h.2 i.val j.val i.isLt j.isLt];simp only[f,r.2 i j];apply Bool.eq_iff_iff.mpr;simp only[kN,gy,cG,cD,aV,bI,gL,Fin.ext_iff]
def bB{n:Nat}(e:ES n):Ls (CP n):=(List.range n).flatMap fun a=>(List.range n).flatMap fun b=>(List.range n).flatMap fun c=>(List.range n).flatMap fun d=>
         if ha:a<n then if hb:b<n then if hc:c<n then if hd:d<n then if a<c/\c<b/\b<d/\(⟨a,ha⟩,⟨b,hb⟩)∈e/\(⟨c,hc⟩,⟨d,hd⟩)∈e then [((⟨a,ha⟩,⟨b,hb⟩),(⟨c,hc⟩,⟨d,hd⟩))]
          else []
         else [] else [] else [] else []
lemma jJ{n:Nat}(q:ES n)(p:(EP n)×(EP n)):p∈bB q↔p∈cH q:=by
 simp only[bB,gM,aY,cH,aL,mem_product,eS,iU];constructor
 ·
  rintro⟨a,u,b,s,c,r,d,hd,h⟩;simp only[u,s,r,hd,↓reduceDIte] at h;split_ifs at h with e
  {simp only[eZ] at h;subst h;exact⟨⟨e.2.2.2.1,e.2.2.2.2⟩,e.1,e.2.1,e.2.2.1⟩};{simp at h}
 {rintro⟨⟨w,v⟩,o,j,i⟩;refine⟨p.1.1.val,p.1.1.isLt,p.1.2.val,p.1.2.isLt,p.2.1.val,p.2.1.isLt,p.2.2.val,p.2.2.isLt,?_⟩;simp only[p.1.1.isLt,p.1.2.isLt,p.2.1.isLt,p.2.2.isLt,↓reduceDIte,Fin.eta];rw[dP ⟨o,j,i,w,v⟩];simp}
lemma lH{n:Nat}(r:ES n):(bB r).Nodup:=by
 let h (a b c d:Nat):Ls (CP n):=
  if ha:a<n then if hb:b<n then if hc:c<n then if hd:d<n then if a<c/\c<b/\b<d/\(⟨a,ha⟩,⟨b,hb⟩)∈r/\(⟨c,hc⟩,⟨d,hd⟩)∈r then [((⟨a,ha⟩,⟨b,hb⟩),(⟨c,hc⟩,⟨d,hd⟩))]
   else []
  else [] else [] else [] else []
 have e:∀ {a b c d x},x∈h a b c d->x.1.1.val=a/\x.1.2.val=b/\x.2.1.val=c/\x.2.2.val=d:=by
  intro a b c d x q;simp only[h] at q;split_ifs at q;{simp only[eZ] at q;subst q;exact⟨rfl,rfl,rfl,rfl⟩}
  all_goals simp at q
 have o:∀ a b c d,(h a b c d).Nodup:=fun a b c d=>by
  simp only[h];split_ifs <;> simp
 change ((List.range n).flatMap fun a=>(List.range n).flatMap fun b=>(List.range n).flatMap fun c=>(List.range n).flatMap fun d=>h a b c d).Nodup;rw[lA];refine⟨fun a _=>?_,nodup_range.pairwise_of_forall_ne fun a _ a' _ hne x j i=>?_⟩
 ·
  rw[lA];refine⟨fun b _=>?_,nodup_range.pairwise_of_forall_ne fun b _ b' _ hne x j i=>?_⟩
  ·
   rw[lA];refine⟨fun c _=>?_,nodup_range.pairwise_of_forall_ne fun c _ c' _ hne x j i=>?_⟩;{rw[lA];refine⟨fun d _=>o a b c d,nodup_range.pairwise_of_forall_ne fun d _ d' _ hne x j i=>?_⟩;exact hne ((e j).2.2.2.symm.trans (e i).2.2.2)}
   ·
    simp only[gM,aY] at j i;rcases j with ⟨_,_,j⟩;rcases i with ⟨_,_,i⟩
    exact hne ((e j).2.2.1.symm.trans (e i).2.2.1)
  ·
   simp only[gM,aY] at j i;rcases j with ⟨_,_,_,_,j⟩;rcases i with ⟨_,_,_,_,i⟩
   exact hne ((e j).2.1.symm.trans (e i).2.1)
 ·
  simp only[gM,aY] at j i;rcases j with ⟨_,_,_,_,_,_,j⟩;rcases i with ⟨_,_,_,_,_,_,i⟩
  exact hne ((e j).1.symm.trans (e i).1)
lemma qn{n:Nat}(F:ES n):(bB F).length=cr F:=by have b:(bB F).toFinset=cH F:=(by ext p;rw[dO,jJ]);rw[<- nI (lH F),b];rfl
lemma r7{n:Nat}(h:ES n):(bB h).length<=n^4:=by
 let e (a b c d:Nat):Ls (CP n):=
  if ha:a<n then if hb:b<n then if hc:c<n then if hd:d<n then if a<c/\c<b/\b<d/\(⟨a,ha⟩,⟨b,hb⟩)∈h/\(⟨c,hc⟩,⟨d,hd⟩)∈h then [((⟨a,ha⟩,⟨b,hb⟩),(⟨c,hc⟩,⟨d,hd⟩))]
   else []
  else [] else [] else [] else []
 have r:∀ a b c d,(e a b c d).length<=1:=fun a b c d=>by
  simp only[e];split_ifs <;> simp
 have q:∀ a b c,((List.range n).flatMap fun d=>e a b c d).length<=n:=fun a b c=>by
  simpa using bY (List.range n) (e a b c) 1 (fun d _=>r a b c d)
 have o:∀ a b,((List.range n).flatMap fun c=>(List.range n).flatMap fun d=>e a b c d).length<=n*n:=fun a b=>by
  simpa using bY (List.range n) _ n (fun c _=>q a b c)
 have j:∀ a,((List.range n).flatMap fun b=>(List.range n).flatMap fun c=>(List.range n).flatMap fun d=>e a b c d).length<=n*(n*n):=fun a=>by
  simpa using bY (List.range n) _ (n*n) (fun b _=>o a b)
 change ((List.range n).flatMap fun a=>(List.range n).flatMap fun b=>(List.range n).flatMap fun c=>(List.range n).flatMap fun d=>e a b c d).length<=n^4;have i:=bY (List.range n) _ (n*(n*n)) (fun a _=>j a);simp only[lx] at i
 calc _<=n*(n*(n*n)):=i
  _=n^4:=by ring
lemma rP{n:Nat}{h:ES n}{e:LB}(q:dA h e){a b c d:Nat}(o:a<n)(j:b<n)(i:c<n)(hd:d<n):od (un n) e (un a) (un b) (un c) (un d)=cF (decide (a<c/\c<b/\b<d/\(⟨a,o⟩,⟨b,j⟩)∈h/\(⟨c,i⟩,⟨d,hd⟩)∈h)):=by simp only[od,iZ,kg,eG,J,q.2 ⟨a,o⟩ ⟨b,j⟩,q.2 ⟨c,i⟩ ⟨d,hd⟩,dx];congr 1;apply Bool.eq_iff_iff.mpr;simp[and_assoc]
lemma mW{n:Nat}{z:ES n}{e:LB}(K:dA z e):gO (un n) e=un (bB z).length:=by have h:∀ a b c d,(p0 (Z (un d) (Z (un c) (Z (un b) (Z (un a) (Z (un n) e)))))).length<=1:=(by intro a b c d;simp only[p0,left,right,G];unfold gT;split_ifs <;> simp);have j:∀ a b c,pZ (Z (un c) (Z (un b) (Z (un a) (Z (un n) e))))=(List.range n).flatMap (fun d=>p0 (Z (un d) (Z (un c) (Z (un b) (Z (un a) (Z (un n) e)))))):=(by intro a b c;simp only[pZ,left,right,G];rw[bA p0 [true] (un n) _ (fun d _=>h a b c d),J]);have i:∀ a b c,(pZ (Z (un c) (Z (un b) (Z (un a) (Z (un n) e))))).length<=n:=(by intro a b c;rw[j];simpa using bY (List.range n) _ 1 (fun d _=>h a b c d));have q:∀ a b,pY (Z (un b) (Z (un a) (Z (un n) e)))=(List.range n).flatMap (fun c=>pZ (Z (un c) (Z (un b) (Z (un a) (Z (un n) e))))):=(by intro a b;simp only[pY,left,right,G];rw[bA pZ (un n) (un n) _ (fun c _=>by rw[J];exact i a b c),J]);have o:∀ a b,(pY (Z (un b) (Z (un a) (Z (un n) e)))).length<=n*n:=(by intro a b;rw[q];simpa using bY (List.range n) _ n (fun c _=>i a b c));have r:∀ a,ry (Z (un a) (Z (un n) e))=(List.range n).flatMap (fun b=>pY (Z (un b) (Z (un a) (Z (un n) e)))):=(by intro a;simp only[ry,left,right,G];rw[bA pY (dS (un n) (un n)) (un n) _ (fun b _=>by rw[gS,J];exact o a b),J]);have y:∀ a,(ry (Z (un a) (Z (un n) e))).length<=n*(n*n):=(by intro a;rw[r];simpa using bY (List.range n) _ (n*n) (fun b _=>o a b));rw[<- gq (bB z)];unfold gO bB;rw[bA ry (dS (un n) (dS (un n) (un n))) (un n) _ (fun a _=>by rw[gS,gS,J];exact y a),J];simp only[gg];refine dG fun a E=>?_;rw[r a];refine dG fun b B=>?_;rw[q a b];refine dG fun c L=>?_;rw[j a b c];refine dG fun d hd=>?_;have x:=aY.mp E;have w:=aY.mp B;have v:=aY.mp L;have s:=aY.mp hd;simp only[p0,left,right,G,rP K x w v s,dE,x,w,v,s,↓reduceDIte];by_cases u:a<c/\c<b/\b<d/\(⟨a,x⟩,⟨b,w⟩)∈z/\(⟨c,v⟩,⟨d,s⟩)∈z <;> simp[u]
lemma wH{n:Nat}{F:ES n}{b:LB}(c:dA F b):rA (un n) b=cF (decide (cr F % 2=1)):=by rw[rA,mW c,qn,tq]
lemma ql{n:Nat}{L:ES n}{e:LB}(M:dA L e):eD (un n) e=(bB L).flatMap (fun p=>lh (un n) (un p.1.1.val) (un p.1.2.val) (un p.2.1.val) (un p.2.2.val)):=by have s:(un n++un n++un n++un n).length=4*n:=(by simp[J];omega);have h:∀ a b c d,(oc (Z (un d) (Z (un c) (Z (un b) (Z (un a) (Z (un n) e)))))).length<=4*n:=(by intro a b c d;simp only[oc,left,right,G];unfold gT;split_ifs;{simp};{rw[rR,J]});have j:∀ a b c,ob (Z (un c) (Z (un b) (Z (un a) (Z (un n) e))))=(List.range n).flatMap (fun d=>oc (Z (un d) (Z (un c) (Z (un b) (Z (un a) (Z (un n) e)))))):=(by intro a b c;simp only[ob,left,right,G];rw[bA oc _ (un n) _ (fun d _=>by rw[s];exact h a b c d),J]);have i:∀ a b c,(ob (Z (un c) (Z (un b) (Z (un a) (Z (un n) e))))).length<=n*(4*n):=(by intro a b c;rw[j];simpa using bY (List.range n) _ (4*n) (fun d _=>h a b c d));have q:∀ a b,oa (Z (un b) (Z (un a) (Z (un n) e)))=(List.range n).flatMap (fun c=>ob (Z (un c) (Z (un b) (Z (un a) (Z (un n) e))))):=(by intro a b;simp only[oa,left,right,G];rw[bA ob _ (un n) _ (fun c _=>by simp only[dS,J,s];exact i a b c),J]);have o:∀ a b,(oa (Z (un b) (Z (un a) (Z (un n) e)))).length<=n*(n*(4*n)):=(by intro a b;rw[q];simpa using bY (List.range n) _ (n*(4*n)) (fun c _=>i a b c));have r:∀ a,pG (Z (un a) (Z (un n) e))=(List.range n).flatMap (fun b=>oa (Z (un b) (Z (un a) (Z (un n) e)))):=(by intro a;simp only[pG,left,right,G];rw[bA oa _ (un n) _ (fun b _=>by simp only[dS,J,s];exact o a b),J]);have z:∀ a,(pG (Z (un a) (Z (un n) e))).length<=n*(n*(n*(4*n))):=(by intro a;rw[r];simpa using bY (List.range n) _ (n*(n*(4*n))) (fun b _=>o a b));unfold eD bB;rw[bA pG _ (un n) _ (fun a _=>by simp only[dS,J,s];exact z a),J];simp only[gg];refine dG fun a K=>?_;rw[r a];refine dG fun b E=>?_;rw[q a b];refine dG fun c B=>?_;rw[j a b c];refine dG fun d hd=>?_;have y:=aY.mp K;have x:=aY.mp E;have w:=aY.mp B;have u:=aY.mp hd;simp only[oc,left,right,G,rP M y x w u,dE,y,x,w,u,↓reduceDIte];by_cases v:a<c/\c<b/\b<d/\(⟨a,y⟩,⟨b,x⟩)∈L/\(⟨c,w⟩,⟨d,u⟩)∈L <;> simp[v]
lemma q8{n:Nat}{j:ES n}{c:LB}(s:dA j c){q:Nat}(r:q<(bB j).length):let p:=(bB j)[q]
 let b:=eN (un n++un n++un n++un n) (un q) (eD (un n) c)
 fa (un n) [] b=un p.1.1.val/\
 fa (un n) [true] b=un p.1.2.val/\
 fa (un n) [true,true] b=un p.2.1.val/\
 fa (un n) [true,true,true] b=un p.2.2.val:=by
 intro p b;have e:b=lh (un n) (un p.1.1.val) (un p.1.2.val) (un p.2.1.val) (un p.2.2.val):=(by simp only[b,ql s];exact fo (bB j) _ (un n++un n++un n++un n) q r (fun x _=>by rw[rR];simp[J];omega));have d:lh (un n) (un p.1.1.val) (un p.1.2.val) (un p.2.1.val) (un p.2.2.val)=([p.1.1.val,p.1.2.val,p.2.1.val,p.2.2.val]).flatMap (fun v=>dT (un n) (un v)):=(by simp[lh,dM]);have h:∀ i (o:i<4),eN (un n) (un i) b=dT (un n) (un ([p.1.1.val,p.1.2.val,p.2.1.val,p.2.2.val][i])):=(by intro i o;rw[e,d];exact fo [p.1.1.val,p.1.2.val,p.2.1.val,p.2.2.val] (fun v=>dT (un n) (un v)) (un n) i o (fun v _=>qd _ _));refine⟨?_,?_,?_,?_⟩;{unfold fa;change kk (eN (un n) (un 0) b)=_;rw[h 0 (by omega)];exact kz n _ p.1.1.isLt.le};{unfold fa;change kk (eN (un n) (un 1) b)=_;rw[h 1 (by omega)];exact kz n _ p.1.2.isLt.le};{unfold fa;change kk (eN (un n) (un 2) b)=_;rw[h 2 (by omega)];exact kz n _ p.2.1.isLt.le};{unfold fa;change kk (eN (un n) (un 3) b)=_;rw[h 3 (by omega)];exact kz n _ p.2.2.isLt.le}
def eF(c:Ls Nat):Nat:=match c.getLast? with
 | none=>0
 | some b=>b+1
def cU{n:Nat}(L:Ls (CP n))(c:Ls Nat):ES n:=c.foldl (fun b q=>if h:q<L.length then b ∪ {L[q].1,L[q].2} else b) ∅
lemma fD{n:Nat}(L:Ls (CP n))(b:Ls Nat){q:Nat}(c:q<L.length):cU L (b++[q])=cU L b ∪ {L[q].1,L[q].2}:=by simp[cU,c]
lemma gE(b:Ls Nat)(q:Nat):eF (b++[q])=q+1:=by simp[eF]
def aJ{n:Nat}(L:Ls (CP n)):Nat->Ls (Ls Nat)
 | 0=>[[]]
 | r+1=>
   (aJ L r).flatMap fun b=>
     (List.range L.length).flatMap fun q=>
       if hq:q<L.length then if eF b<=q/\aQ (cU L b ∪ {L[q].1,L[q].2}) then [b++[q]]
        else []
       else []
lemma tz{n:Nat}(L:Ls (CP n))(r:Nat):(aJ L r).length<=L.length^r:=by
 induction r with
 | zero=>simp[aJ]
 | succ r c=>
   simp only[aJ,gN]
   have d:∀ b∈aJ L r,((List.range L.length).flatMap fun q=>if hq:q<L.length then if eF b<=q/\aQ (cU L b ∪ {L[q].1,L[q].2}) then [b++[q]] else [] else []).length<=L.length:=fun b _=>by
    simpa using bY (List.range L.length) _ 1 (fun q _=>by split_ifs <;> simp)
   exact (bY (aJ L r) _ L.length d).trans (nK _ c)
lemma t4{n:Nat}(L:Ls (CP n))(r:Nat):(aJ L r).Nodup:=by
 induction r with
 | zero=>simp[aJ]
 | succ r v=>
   let step (c:Ls Nat) (q:Nat):Ls (Ls Nat):=
    if hq:q<L.length then if eF c<=q/\aQ (cU L c ∪ {L[q].1,L[q].2}) then [c++[q]] else []
    else []
   have b:∀ {c q x},x∈step c q->x=c++[q]:=by
    intro c q x j;simp only[step] at j;split_ifs at j;{exact eZ.mp j}
    all_goals simp at j
   have d:∀ c q,(step c q).Nodup:=fun c q=>by
    simp only[step];split_ifs <;> simp
   change ((aJ L r).flatMap fun c=>(List.range L.length).flatMap fun q=>step c q).Nodup;rw[lA];refine⟨fun c _=>?_,v.pairwise_of_forall_ne fun u _ s2 _ hne x i h=>?_⟩;{rw[lA];refine⟨fun q _=>d c q,nodup_range.pairwise_of_forall_ne fun s _ o _ hne x i h=>?_⟩;have e:c++[s]=c++[o]:=(b i).symm.trans (b h);exact hne (by simpa using uS e)}
   ·
    simp only[gM,aY] at i h;rcases i with ⟨s,_,i⟩;rcases h with ⟨o,_,h⟩
    have e:u++[s]=s2++[o]:=(b i).symm.trans (b h);exact hne (qF e rfl)
lemma gv{n:Nat}(L:Ls (CP n))(r:Nat)(d:Ls Nat):d∈aJ L r↔d.length=r/\d.Pairwise (·<·)/\(∀ q∈d,q<L.length)/\aQ (cU L d):=by
 induction r generalizing d with
 | zero=>simp only[aJ,eZ];constructor;{rintro rfl;exact⟨rfl,List.Pairwise.nil,by simp,⟨by simp[cU],by simp[cU]⟩⟩};{rintro⟨b,_,_,_⟩;exact List.eq_nil_of_length_eq_zero b}
 | succ r E=>
   simp only[aJ,gM,aY];constructor
   ·
    rintro⟨s,B,q,u,c⟩;rw[cT u] at c;split_ifs at c with h
    ·
     simp only[eZ] at c;subst c;obtain⟨b,i,j,_⟩:=(E s).mp B;refine⟨by simp[b],?_,?_,by rw[fD L s u];exact h.2⟩
     ·
      rw[kL];refine⟨i,by simp,fun x v y K=>?_⟩;simp only[eZ] at K;subst K;cases s using List.reverseRecOn with
      | nil=>simp at v
      | append_singleton w e=>
        rw[gE] at h;rcases eL.mp v with Q|S
        {have a8:=(kL.mp i).2.2 x Q e (by simp);omega};{simp only[eZ] at S;omega}
     ·
      intro x v;rcases eL.mp v with a0|a1
      {exact j x a0};{simp only[eZ] at a1;omega}
    {simp at c}
   ·
    rintro⟨b,i,j,M⟩;cases d using List.reverseRecOn with
    | nil=>simp at b
    | append_singleton s q=>
      have u:q<L.length:=j q (by simp);have o:=kL.mp i;have z:cU L s⊆cU L (s++[q]):=(by rw[fD L s u];exact subset_union_left);have B:s∈aJ L r:=(E s).mpr ⟨by simp at b;omega,o.1,fun x v=>j x (nM _ v),iC M z⟩
      have P:eF s<=q:=by
       cases s using List.reverseRecOn with
       | nil=>simp[eF]
       | append_singleton w e=>
         rw[gE]
         have:=o.2.2 e (by simp) q (by simp)
         omega
      refine⟨s,B,q,u,?_⟩;rw[cT u,dP ⟨P,by rw[<- fD L s u];exact M⟩];simp
lemma mo{n:Nat}{L:Ls (CP n)}{r:Nat}{b:Ls Nat}(h:b∈aJ L r):eF b<=L.length:=by
 obtain⟨_,_,c,_⟩:=(gv L r b).mp h;cases b using List.reverseRecOn with
 | nil=>simp[eF]
 | append_singleton s q=>rw[gE];exact c q (by simp)
def dR{n:Nat}(L:Ls (CP n))(c:Ls Nat):Ft (CP n):=c.foldl (fun b q=>if h:q<L.length then insert L[q] b else b) ∅
lemma il{n:Nat}(L:Ls (CP n))(b:Ls Nat){q:Nat}(c:q<L.length):dR L (b++[q])=insert L[q] (dR L b):=by simp[dR,c]
lemma hX{n:Nat}(L:Ls (CP n))(d:Ls Nat)(p:(EP n)×(EP n)):p∈dR L d↔∃ q∈d,∃ h:q<L.length,L[q]'h=p:=by
 induction d using List.reverseRecOn with
 | nil=>simp[dR]
 | append_singleton s q o=>
   by_cases j:q<L.length
   ·
    rw[il L s j,aV,o];constructor;{rintro (rfl|⟨x,i,b,rfl⟩);{exact⟨q,by simp,j,rfl⟩};{exact⟨x,nM _ i,b,rfl⟩}}
    ·
     rintro⟨x,i,b,rfl⟩;rcases eL.mp i with e|c
     {exact Or.inr ⟨x,e,b,rfl⟩};{simp only[eZ] at c;subst c;exact Or.inl rfl}
   ·
    have r:dR L (s++[q])=dR L s:=(by simp[dR,j]);rw[r,o];constructor;{rintro⟨x,i,b,rfl⟩;exact⟨x,nM _ i,b,rfl⟩}
    ·
     rintro⟨x,i,b,rfl⟩;rcases eL.mp i with e|c
     {exact⟨x,e,b,rfl⟩};{simp only[eZ] at c;subst c;exact (j b).elim}
lemma je{n:Nat}(L:Ls (CP n))(b:Ls Nat):cU L b=bF (dR L b):=by induction b using List.reverseRecOn with|nil=>{simp[cU,dR,bF]}|append_singleton s q d=>{by_cases c:q<L.length;{rw[fD L s c,il L s c,d];simp[bF,biUnion_insert,nN]};{have h:cU L (s++[q])=cU L s:=(by simp[cU,c]);have e:dR L (s++[q])=dR L s:=(by simp[dR,c]);rw[h,e,d]}}
lemma nb{n:Nat}{L:Ls (CP n)}(r:L.Nodup)(b:Ls Nat)(e:b.Nodup)(h:∀ q∈b,q<L.length):(dR L b).card=b.length:=by
 induction b using List.reverseRecOn with
 | nil=>simp[dR]
 | append_singleton s q v=>
   have z:q<L.length:=h q (by simp)
   have d:s.Nodup/\q∉s:=by
    have:=fu.mp e
    exact⟨this.1,fun o=>this.2.2 q o q (by simp) rfl⟩
   have c:L[q]∉dR L s:=(by rw[hX];rintro⟨x,i,w,u⟩;have j:x=q:=r.getElem_inj_iff.mp u;exact d.2 (j▸i));rw[il L s z,o7 c,v d.1 (fun x y=>h x (nM _ y))];simp
lemma iD:∀(l1 w:Ls Nat),l1.Pairwise (·<·)->w.Pairwise (·<·)->(∀ x,x∈l1↔x∈w)->l1=w
 | [],[],_,_,_=>rfl
 | [],b::_,_,_,h=>by exfalso;exact (not_mem_nil (a:=b)) ((h b).mpr (by simp))
 | a::_,[],_,_,h=>by exfalso;exact (not_mem_nil (a:=a)) ((h a).mp (by simp))
 | a::v,b::u,i,e,h=>by
   rw[jE] at i e
   have L:a=b:=by
    have B:a∈b::u:=(h a).mp (by simp);have z:b∈a::v:=(h b).mpr (by simp);rcases cB.mp B with rfl|s
    {rfl}
    ·
     rcases cB.mp z with rfl|r
     {rfl};{have K:=i.1 b r;have E:=e.1 a s;omega}
   subst L;congr 1;refine iD v u i.2 e.2 fun x=>?_;have o:x∈v->x≠a:=fun y q=>Nat.lt_irrefl a (q▸i.1 x y);have j:x∈u->x≠a:=fun y q=>Nat.lt_irrefl a (q▸e.1 x y);constructor
   ·
    intro d;rcases cB.mp ((h x).mp (g9 a d)) with rfl|c
    {exact (o d rfl).elim};{exact c}
   ·
    intro c;rcases cB.mp ((h x).mpr (g9 a c)) with rfl|d
    {exact (j c rfl).elim};{exact d}
lemma su{n:Nat}(B:ES n)(r:Nat)(f:Ft (CP n)->Int):((aJ (bB B) r).map (fun b=>f (dR (bB B) b))).sum=∑ C∈(cH B).powerset.filter (fun C=>C.card=r/\aQ (bF C)),f C:=by
 let L:=bB B;have d:L.Nodup:=lH B
 have e:∀(E:Ls (Ls Nat)),E.Nodup->(E.map (fun b=>f (dR L b))).sum=∑ b∈E.toFinset,f (dR L b):=by
  intro E S;induction E with
  | nil=>simp
  | cons a E ih=>simp only[j5] at S;simp only[aO,eu,sI,kK (dO.not.mpr S.1),ih S.2]
 rw[e (aJ L r) (t4 L r)];refine nV (fun b _=>dR L b) ?_ ?_ ?_ ?_;{intro b a5;obtain⟨j,u,w,hm⟩:=(gv L r b).mp (dO.mp a5);simp only[aL,mem_powerset];refine⟨?_,?_,by rw[<- je];exact hm⟩;{intro p hp;obtain⟨q,_,K,rfl⟩:=(hX L b p).mp hp;exact (jJ B _).mp (iQ K)};{rw[nb d b (u.imp (fun h=>bS h)) w,j]}};{intro P ai M ah ad;obtain⟨_,ab,z,_⟩:=(gv L r P).mp (dO.mp ai);obtain⟨_,aa,y,_⟩:=(gv L r M).mp (dO.mp ah);refine iD P M ab aa fun q=>?_;constructor;{intro a1;have i:L[q]'(z q a1)∈dR L M:=(by rw[<- ad,hX];exact⟨q,a1,z q a1,rfl⟩);obtain⟨Q,a7,a6,o⟩:=(hX L M _).mp i;have:Q=q:=d.getElem_inj_iff.mp o;exact this▸a7};{intro a0;have i:L[q]'(y q a0)∈dR L P:=(by rw[ad,hX];exact⟨q,a0,y q a0,rfl⟩);obtain⟨Q,a8,a6,o⟩:=(hX L P _).mp i;have:Q=q:=d.getElem_inj_iff.mp o;exact this▸a8}}
 ·
  intro C hC;simp only[aL,mem_powerset] at hC;obtain⟨a2,x,al⟩:=hC;let b:Ls Nat:=(List.range L.length).filter (fun q=>decide (∃ h:q<L.length,L[q]'h∈C));have u:b.Pairwise (·<·):=List.Pairwise.filter _ List.pairwise_lt_range;have w:∀ q∈b,q<L.length:=fun q K=>aY.mp (gd.mp K).1
  have c:dR L b=C:=by
   ext p;rw[hX];constructor
   ·
    rintro⟨q,K,s,rfl⟩;have hf:=of_decide_eq_true (gd.mp K).2;rcases hf with ⟨_,v⟩;exact v
   {intro v;have aj:p∈L:=(jJ B p).mpr (a2 v);obtain⟨q,s,rfl⟩:=mem_iff_getElem.mp aj;refine⟨q,gd.mpr ⟨aY.mpr s,jG ⟨s,v⟩⟩,s,rfl⟩}
  have j:b.length=r:=(by rw[<- nb d b (u.imp (fun h=>bS h)) w,c,x]);refine⟨b,dO.mpr ((gv L r b).mpr ⟨j,u,w,?_⟩),c⟩;rw[je,c];exact al
 {intro _ _;rfl}
def k9{n:Nat}(h:ES n)(r:Nat)(st:LB):Prop:=
 let L:=bB h;let e:=L.length
 ∃ c:Ls (LB),st=Z (un (aJ L r).length) c.flatten/\c.length=(aJ L r).length/\∀ i (hi:i<(aJ L r).length),
     let d:=(aJ L r)[i]
     ∃ b,dA (cU L d) b/\c.getD i []=dT (un (e+1)) (un (eF d))++b
lemma vB{n:Nat}{w:ES n}{r:Nat}{st:LB}(u:k9 w r st):let q:=(bB w).length
 st.length=(aJ (bB w) r).length*((q+1)+n*n+2)+1:=by
 intro q;obtain⟨b,rfl,d,h⟩:=u
 have c:∀ j (i:j<b.length),b[j].length=(q+1)+n*n:=fun j i=>by
  obtain⟨s,y,o⟩:=h j (d▸i);rw[cQ _ _ i] at o;rw[o,dL,qd,J,y.1]
 have e:b.flatten.length=b.length*((q+1)+n*n):=(by rw[List.length_flatten];have x:b.map List.length=replicate b.length ((q+1)+n*n):=(by apply jD;{simp};{intro j i _;have v:j<b.length:=(by simpa using i);simp[c j v]});rw[x,sum_replicate,n0]);rw[rT,J,e,d];ring
lemma ux{n:Nat}{S:ES n}{ag:LB}(hE:dA S ag){r:Nat}{st:LB}(b4:k9 S r st)(b2:Nat):let L:=bB S
 let h:=L.length;let args:=Z (un n) (Z (un h) (eD (un n) ag))
 k9 S (r+1) (ru (Z (un b2) (Z args st))):=by
 intro L h args;obtain⟨j,rfl,a5,aw⟩:=b4;have ad:dZ (un h) (un n)=un ((h+1)+n*n):=(by simp only[dZ,eR,gS,g6])
 have ah:∀ x∈j,x.length=(dZ (un h) (un n)).length:=fun x hx=>by
  obtain⟨i,s,rfl⟩:=mem_iff_getElem.mp hx;obtain⟨b,hF,b0⟩:=aw i (a5▸s);rw[cQ _ _ s] at b0;rw[b0,dL,qd,ad,J,J,hF.1]
 have ab:∀ i (s:i<(aJ L r).length),eN (dZ (un h) (un n)) (un i) j.flatten=j.getD i []:=fun i s=>by
  have y:i<j.length:=a5.symm▸s;have b7:j.flatten=j.flatMap id:=(by rw[List.flatMap_id]);rw[b7,cQ _ _ y];exact fo j id (dZ (un h) (un n)) i y ah
 have a3:∀ i (s:i<(aJ L r).length),
  let P:=(aJ L r)[i];let v:=eN (dZ (un h) (un n)) (un i) j.flatten;let c:=kk (gY (un h++[true]) v);let b:=fO (un h++[true]) v
  c=un (eF P)/\dA (cU L P) b:=fun i s=>by
  intro P v c b;obtain⟨Fb,b9,b6⟩:=aw i s;have ak:v=dT (un (h+1)) (un (eF P))++Fb:=(ab i s).trans b6;have ar:eF P<=h+1:=(mo (iQ s)).trans (Nat.le_succ _);have a2:(dT (un (h+1)) (un (eF P))).length=h+1:=(by rw[qd,J]);have b3:gY (un h++[true]) v=dT (un (h+1)) (un (eF P)):=(by rw[ak,eR,vZ,J,take_append,a2,nY,List.take_zero,cR,o8 a2.le]);have b8:fO (un h++[true]) v=Fb:=(by rw[ak,eR,xS,J,drop_append,a2,nY,sZ,uV a2.le,gl]);exact⟨by simp only[c,b3];exact kz (h+1) _ ar,by simp only[b,b8];exact b9⟩
 let d (i:Nat) (s:i<(aJ L r).length) (q:Nat) (w:q<h):Ls (LB):=
  let P:=(aJ L r)[i];let p:=L[q];let v:=eN (dZ (un h) (un n)) (un i) j.flatten;let b:=fO (un h++[true]) v
  if eF P<=q/\aQ (cU L P ∪ {p.1,p.2}) then [dT (un (h+1)) (un (q+1))++ij (un n) b (un p.1.1.val) (un p.1.2.val) (un p.2.1.val) (un p.2.2.val)]
  else []
 have u:∀ i (s:i<(aJ L r).length) (q:Nat) (w:q<h),
  let v:=eN (dZ (un h) (un n)) (un i) j.flatten;let c:=kk (gY (un h++[true]) v);let b:=fO (un h++[true]) v
  h7 (Z (un q) (Z c (Z b args)))=(d i s q w).flatten/\
  jr (Z (un q) (Z c (Z b args)))=un (d i s q w).length:=by
  intro i s q w v c b;have B:=a3 i s;dsimp only at B;have Q:=q8 hE w;dsimp only at Q;have aq:L[q]∈cH S:=(jJ S _).mp (iQ w);have ay:eS L[q].1 L[q].2:=(aL.mp aq).2;have ap:aQ (cU L (aJ L r)[i]):=((gv L r _).mp (iQ s)).2.2.2;have af:gz (l8 c (un q)) (jt (un n) b (un L[q].1.1.val) (un L[q].1.2.val) (un L[q].2.1.val) (un L[q].2.2.val))=cF (decide (eF (aJ L r)[i]<=q/\aQ (cU L (aJ L r)[i] ∪ {L[q].1,L[q].2}))):=(by simp only[c,b,v,B.1,iI,J,u7 B.2 ap ay,dx];congr 1);constructor;{simp only[h7,left,right,G,args,Q.1,Q.2.1,Q.2.2.1,Q.2.2.2];change gT (gz (l8 c (un q)) (jt (un n) b (un L[q].1.1.val) (un L[q].1.2.val) (un L[q].2.1.val) (un L[q].2.2.val))) [] (dT (un h++[true]) (un q++[true])++ij (un n) b (un L[q].1.1.val) (un L[q].1.2.val) (un L[q].2.1.val) (un L[q].2.2.val))=_;rw[af,dE,eR,eR];simp only[d];by_cases K:eF (aJ L r)[i]<=q/\aQ (cU L (aJ L r)[i] ∪ {L[q].1,L[q].2});{rw[dP (jG K),dP K];simp only[sN,sS,cR];rfl};{rw[cM (by rw[iw K];decide),cM K];rfl}};{simp only[jr,left,right,G,args,Q.1,Q.2.1,Q.2.2.1,Q.2.2.2];change gT (gz (l8 c (un q)) (jt (un n) b (un L[q].1.1.val) (un L[q].1.2.val) (un L[q].2.1.val) (un L[q].2.2.val))) [] [true]=_;rw[af,dE];simp only[d];by_cases K:eF (aJ L r)[i]<=q/\aQ (cU L (aJ L r)[i] ∪ {L[q].1,L[q].2});{rw[dP (jG K),dP K];rfl};{rw[cM (by rw[iw K];decide),cM K];rfl}}
 let e:Ls (LB):=
  (List.range (aJ L r).length).flatMap fun i=>
    if s:i<(aJ L r).length then (List.range h).flatMap fun q=>
       if w:q<h then d i s q w else []
    else []
 have a8:∀ i (s:i<(aJ L r).length),iG (Z (un i) (Z j.flatten args))=un ((List.range h).flatMap fun q=>if w:q<h then d i s q w else []).length:=by
  intro i s;simp only[iG,left,right,G,args]
  have ae:∀ q<h,(jr (Z (un q) (Z (kk (gY (un h++[true]) (eN (dZ (un h) (un n)) (un i) j.flatten))) (Z (fO (un h++[true]) (eN (dZ (un h) (un n)) (un i) j.flatten)) args)))).length<=1:=fun q w=>by
   rw[(u i s q w).2,J];simp only[d];split_ifs <;> simp
  rw[bA jr [true] (un h) _ (fun q w=>ae q (by simpa using w)),J];conv_rhs=>rw[<- gq,gg]
  refine dG fun q w=>?_;have M:=aY.mp w;rw[cT M,(u i s q M).2,gq]
 have a7:∀ i (s:i<(aJ L r).length),gU (Z (un i) (Z j.flatten args))=((List.range h).flatMap fun q=>if w:q<h then d i s q w else []).flatten:=by
  intro i s;simp only[gU,left,right,G,args]
  have ae:∀ q<h,(h7 (Z (un q) (Z (kk (gY (un h++[true]) (eN (dZ (un h) (un n)) (un i) j.flatten))) (Z (fO (un h++[true]) (eN (dZ (un h) (un n)) (un i) j.flatten)) args)))).length<=(dZ (un h) (un n)).length:=fun q w=>by
   rw[(u i s q w).1];simp only[d];split_ifs with K
   {simp only[sN,sS,cR,dL,qd,J];have B:=a3 i s;dsimp only at B;have ha:=m8 B.2 L[q].1.1 L[q].1.2 L[q].2.1 L[q].2.2;rw[ha.1,ad,J]};{simp}
  rw[bA h7 (dZ (un h) (un n)) (un h) _ (fun q w=>ae q (by simpa using w)),J];rw[iJ];refine dG fun q w=>?_;have M:=aY.mp w;rw[cT M,(u i s q M).1]
 have ao:aJ L (r+1)=(List.range (aJ L r).length).flatMap fun i=>
  if s:i<(aJ L r).length then (List.range h).flatMap fun q=>
     if w:q<h then if eF (aJ L r)[i]<=q/\aQ (cU L (aJ L r)[i] ∪ {L[q].1,L[q].2}) then [(aJ L r)[i]++[q]]
      else []
     else []
  else []:=by
  have b5:aJ L r=(List.range (aJ L r).length).map (fun i=>(aJ L r).getD i []):=(by apply jD;{simp};{intro i s _;simp only[kJ,mH];exact (cQ _ _ s).symm});conv_lhs=>unfold aJ;rw[b5,nP]
  refine dG fun i s=>?_;have y:=aY.mp s;rw[cT y,cQ _ _ y]
 let o:Ls (Ls Nat×LB):=
  (List.range (aJ L r).length).flatMap fun i=>
    if s:i<(aJ L r).length then (List.range h).flatMap fun q=>
       if w:q<h then if eF (aJ L r)[i]<=q/\aQ (cU L (aJ L r)[i] ∪ {L[q].1,L[q].2}) then
        let b:=fO (un h++[true]) (eN (dZ (un h) (un n)) (un i) j.flatten)
        [((aJ L r)[i]++[q],dT (un (h+1)) (un (q+1))++ij (un n) b (un L[q].1.1.val) (un L[q].1.2.val) (un L[q].2.1.val) (un L[q].2.2.val))]
        else []
       else []
    else []
 have al:o.map Prod.fst=aJ L (r+1):=(by rw[ao];simp only[o,sR];refine dG fun i s=>?_;have y:=aY.mp s;rw[cT y,cT y,sR];refine dG fun q w=>?_;have M:=aY.mp w;rw[cT M,cT M];split_ifs <;> simp);have az:o.map Prod.snd=e:=(by simp only[o,e,sR];refine dG fun i s=>?_;have y:=aY.mp s;rw[cT y,cT y,sR];refine dG fun q w=>?_;have M:=aY.mp w;rw[cT M,cT M];simp only[d];split_ifs <;> simp)
 have aa:∀ pr∈o,∃ b,dA (cU L pr.1) b/\pr.2=dT (un (h+1)) (un (eF pr.1))++b:=by
  intro pr E;simp only[o,gM,aY] at E;rcases E with ⟨i,s,E⟩
  rw[cT s] at E;simp only[gM,aY] at E;rcases E with ⟨q,w,E⟩
  rw[cT w] at E;split_ifs at E with K
  {simp only[eZ] at E;subst E;have B:=a3 i s;dsimp only at B;refine⟨ij (un n) (fO (un h++[true]) (eN (dZ (un h) (un n)) (un i) j.flatten)) (un L[q].1.1.val) (un L[q].1.2.val) (un L[q].2.1.val) (un L[q].2.2.val),?_,?_⟩;{rw[fD L _ w];exact m8 B.2 L[q].1.1 L[q].1.2 L[q].2.1 L[q].2.2};{rw[gE]}};{simp at E}
 have aj:bX iG (un h) (un (aJ L r).length) (Z j.flatten args)=un e.length:=by
  have ae:∀ i<(aJ L r).length,(iG (Z (un i) (Z j.flatten args))).length<=h:=fun i s=>by
   rw[a8 i s,J];simpa using bY (List.range h) _ 1 (fun q _=>by
    by_cases w:q<h;{rw[cT w];simp only[d];split_ifs <;> simp}
    · rw[lF w];simp)
  rw[bA iG (un h) (un (aJ L r).length) _ (fun i s=>by rw[J];exact ae i (by simpa using s)),J,<- gq e];simp only[e,gg];refine dG fun i s=>?_;have y:=aY.mp s;rw[cT y,a8 i y,gq]
 have ai:bX gU (dS (un h) (dZ (un h) (un n))) (un (aJ L r).length) (Z j.flatten args)=e.flatten:=by
  have ae:∀ i<(aJ L r).length,(gU (Z (un i) (Z j.flatten args))).length<=h*(dZ (un h) (un n)).length:=fun i s=>by
   rw[a7 i s,iJ]
   have h1:=bY (List.range h) (fun q=>(if w:q<h then d i s q w else []).flatten) (dZ (un h) (un n)).length (fun q _=>by
    by_cases w:q<h;{rw[cT w];simp only[d];split_ifs;{simp only[sN,sS,cR,dL,qd,J];have B:=a3 i s;dsimp only at B;rw[(m8 B.2 L[q].1.1 L[q].1.2 L[q].2.1 L[q].2.2).1,ad,J]};{simp}}
    · rw[lF w];simp)
   simpa using h1
  rw[bA gU _ (un (aJ L r).length) _ (fun i s=>by simp only[dS,J];exact ae i (by simpa using s)),J];simp only[e,iJ];refine dG fun i s=>?_;have y:=aY.mp s;rw[cT y,a7 i y,iJ]
 have z:e.length=(aJ L (r+1)).length:=(by rw[<- al,<- az,ft,ft]);refine⟨e,?_,z,fun i s=>?_⟩;{have av:(aN args).1=un n:=(by simp only[args,G]);have au:(aN (aN args).2).1=un h:=(by simp only[args,G]);simp only[ru,left,right,G,av,au];rw[show (aJ (bB S) r).length=(aJ L r).length from rfl,show (aJ (bB S) (r+1)).length=(aJ L (r+1)).length from rfl,aj,ai,z]}
 ·
  have am:i<o.length:=(by rw[<- al,ft] at s;exact s)
  have h1:(aJ L (r+1))[i]'s= o[i].1:=by
   have:(o.map Prod.fst)[i]'(by simp[am])=(aJ L (r+1))[i]'s:=by congr 1
   simpa using this.symm
  have h2:e.getD i []= o[i].2:=by
   rw[cQ _ _ (z.symm▸s)];have:(o.map Prod.snd)[i]'(by simp[am])=e[i]'(z.symm▸s):=by congr 1
   simpa using this.symm
  rw[h1,h2];exact aa o[i] (iQ am)
lemma vP{n:Nat}{s:ES n}{b:LB}(M:dA s b)(h:LB)(r:Nat)(Q:∀ j≤r,(aJ (bB s) j).length*(((bB s).length+1)+n*n+2)+1<=h.length):k9 s r (s6 h (un n) (un (bB s).length) (eD (un n) b) (un r)):=by
 let L:=bB s;let B:=L.length;let args:=Z (un n) (Z (un B) (eD (un n) b));let c:=Z [true] (dT (un B++[true]) []++fJ (dS (un n) (un n)));have w:k9 s 0 c:=(by refine⟨[dT (un (B+1)) (un 0)++fJ (dS (un n) (un n))],?_,rfl,fun i K=>?_⟩;{simp only[c,aJ,lv,eR,sN,sS,cR];rfl};{simp only[aJ,lv] at K;have P:i=0:=(by omega);subst P;exact⟨fJ (dS (un n) (un n)),s4 n,rfl⟩});unfold s6;rw[kn,J]
 have y:∀(d:Ls Nat),d.length<=r->k9 s d.length (d.foldr (fun i x=>f5 h (ru (Z (un i) (Z args x))) x) c):=by
  intro d;induction d with
  | nil=>intro _;exact w
  | cons z e E=>intro u;simp only[sA,aX];have v:k9 s e.length (e.foldr (fun i x=>f5 h (ru (Z (un i) (Z args x))) x) c):=E (by simp at u;omega);have o:=ux M v z;have q:(ru (Z (un z) (Z args (e.foldr (fun i x=>f5 h (ru (Z (un i) (Z args x))) x) c)))).length<=h.length:=(by rw[vB o];exact Q (e.length+1) (by simp at u;omega));rw[f5,o8 q];exact o
 simpa using y (List.range r) (by simp)
lemma vE(n k b:Nat)(o:n+2<=b+2)(s:1<=k)(c:ES n)(j:Nat)(u:j<k):(aJ (bB c) j).length*(((bB c).length+1)+n*n+2)+1<=(b+2)^(4*k+1):=by
 have q:(bB c).length<=n^4:=r7 c;have h:(bB c).length<=(n+2)^4:=q.trans (pb (by omega) 4);have e:(aJ (bB c) j).length<=(n+2)^(4*j):=(tz _ j).trans ((pb h j).trans (by rw[<- pow_mul]))
 have d:((bB c).length+1)+n*n+2<=(n+2)^4:=by
  have:n^4+n*n+3<=(n+2)^4:=by have r:(n+2)^4=n^4+8*n^3+24*n^2+32*n+16:=(by ring);nlinarith
  omega
 have i:(aJ (bB c) j).length*(((bB c).length+1)+n*n+2)<=(n+2)^(4*(j+1)):=by
  calc _<=(n+2)^(4*j)*(n+2)^4:=nL e d
   _=(n+2)^(4*j+4):=(j8 _ _ _).symm
   _=(n+2)^(4*(j+1)):=by ring_nf
 have r:(n+2)^(4*(j+1))<=(b+2)^(4*k):=(pb o _).trans (kI (by omega) (by omega));have w:(b+2)^(4*k)+1<=2*(b+2)^(4*k):=(by have:1<=(b+2)^(4*k):=Nat.one_le_pow _ _ (by omega);omega);have v:2*(b+2)^(4*k)<=(b+2)^(4*k+1):=(by rw[pow_succ'];exact nK _ (by omega));omega
lemma fX{N:Nat}(f:Fin N->Int):((List.range N).map (fun i=>if h:i<N then f ⟨i,h⟩ else 0)).sum=∑ i:Fin N,f i:=by induction N with|zero=>{simp}|succ N d=>{rw[nQ,bR,ic,List.map_singleton,List.sum_singleton,cT (Nat.lt_succ_self N),Fin.sum_univ_castSucc];congr 1;have b:(List.range N).map (fun i=>if h:i<N+1 then f ⟨i,h⟩ else 0)=(List.range N).map (fun i=>if h:i<N then f ⟨i,sM h⟩ else 0):=(by refine dF fun i e=>?_;have c:=aY.mp e;rw[cT (sM c),cT c]);rw[b];exact d (fun i=>f i.castSucc)}
lemma ji{N:Nat}(f:Fin N->Nat):((List.range N).map (fun i=>if h:i<N then f ⟨i,h⟩ else 0)).sum=∑ i:Fin N,f i:=by induction N with|zero=>{simp}|succ N d=>{rw[nQ,bR,ic,List.map_singleton,List.sum_singleton,cT (Nat.lt_succ_self N),Fin.sum_univ_castSucc];congr 1;have b:(List.range N).map (fun i=>if h:i<N+1 then f ⟨i,h⟩ else 0)=(List.range N).map (fun i=>if h:i<N then f ⟨i,sM h⟩ else 0):=(by refine dF fun i e=>?_;have c:=aY.mp e;rw[cT (sM c),cT c]);rw[b];exact d (fun i=>f i.castSucc)}
lemma pN{b:Type*}(L:Ls b)(g:b->Nat):L.flatMap (fun a=>un (g a))=un (L.map g).sum:=by induction L with|nil=>{rfl}|cons a L c=>{simp only[eY,aO,eu,c,g6]}
lemma jd(i:PZ)(c:Bo)(d b:Nat):(i*((if c then (-1:PZ) else 1)*X^d)).coeff b=if d<=b then (if c then -(i.coeff (b-d)) else i.coeff (b-d)) else 0:=by have e:(i*X^d).coeff b=if d<=b then i.coeff (b-d) else 0:=(by by_cases hd:d<=b;{rw[dP hd];obtain⟨r,s⟩:=Nat.exists_eq_add_of_le' hd;have h:b-d=r:=(by omega);rw[h,s,coeff_mul_X_pow]};{rw[cM hd,coeff_mul];refine sJ fun x q=>?_;have o:=Finset.mem_antidiagonal.mp q;have j:x.2≠d:=(by omega);simp[coeff_X_pow,j]});cases c with|false=>{simp only[eX,↓reduceIte,j9,e]}|true=>{simp only[↓reduceIte,neg_mul,j9,mul_neg,coeff_neg,e];split_ifs <;> simp}
lemma tH{n:Nat}{F:ES n}{c:LB}(s:dA F c)(a b:Fin n):kk (bX iW [true] (un n) (Z (un n) (Z c (Z (un a.val) (un b.val)))))=un ((F.biUnion aF).filter (fun w=>a<w/\w<b)).card:=by
 rw[bA iW [true] (un n) _ (fun _ _=>by simp[iW,eM]),J];let d:Nat->Bo:=fun w=>decide (a.val<w/\w<b.val)&&decide (∃ j:w<n,⟨w,j⟩∈F.biUnion aF);have r:(List.range n).flatMap (fun w=>iW (Z (un w) (Z (un n) (Z c (Z (un a.val) (un b.val))))))=(List.range n).flatMap (fun w=>[d w]):=(by refine dG fun w j=>?_;have e:=aY.mp j;simp only[iW,left,right,G,iZ,J,k5 s ⟨w,e⟩,dx,ew,d];congr 1;apply Bool.eq_iff_iff.mpr;simp[e]);rw[r,jV];congr 1;have q:((List.range n).filter d).Nodup:=nodup_range.filter _;rw[<- nI q];refine nR (fun w j=>⟨w,aY.mp (gd.mp (dO.mp j)).1⟩) ?_ ?_ ?_
 ·
  intro w j;have e:=gd.mp (dO.mp j);have i:=e.2;simp only[d,gy,cG] at i;rcases i with ⟨⟨v,u⟩,_,o⟩
  exact aL.mpr ⟨o,v,u⟩
 {intro x _ w2 _ h;exact aI Fin.val h};{intro w j;have e:=aL.mp j;refine⟨w.val,dO.mpr (gd.mpr ⟨aY.mpr w.isLt,?_⟩),Fin.eta w _⟩;simp only[d,gy,cG];exact⟨⟨e.2.1,e.2.2⟩,w.isLt,e.1⟩}
lemma vN{n:Nat}(z:ES n)(S:∀ e∈z,e.1<e.2)(j:Sf n)(F:ES n){u v:Fin (2*n)}(B:u.val<n)(L:v.val<n)(M:u≠v):let a:Fin n:=if u<v then ⟨u.val,B⟩ else ⟨v.val,L⟩
 let b:Fin n:=if u<v then ⟨v.val,L⟩ else ⟨u.val,B⟩
 gh (jj (fw z j) F) u v=if (a,b)∈z/\a∉F.biUnion aF/\b∉F.biUnion aF then (if xor (decide (v.val<u.val)) (decide (((F.biUnion aF).filter (fun w=>a<w/\w<b)).card % 2=1)) then (-1:PZ) else 1)*X^cZ j (a,b)
  else 0:=by
 intro a b
 have r:a<b:=by
  rcases iR M with h|h
  {simp only[a,b,dP h];exact h};{simp only[a,b,cM (e7 h)];exact h}
 have K:fw z j a b=if (a,b)∈z then X^cZ j (a,b) else 0:=kS S j (a,b) r
 have i:∀ m:Nat,(-1:PZ)^m=if m % 2=1 then -1 else 1:=fun m=>by
  rw[gC (mod_mod m 2).symm];rcases uL m with Q|P
  {simp[Q]};{simp[P]}
 rcases iR M with q|o
 {have y:a=⟨u.val,B⟩:=(by simp[a,q]);have x:b=⟨v.val,L⟩:=(by simp[b,q]);have s:¬(v.val<u.val):=(by have:u.val<v.val:=q;omega);simp only[gh,B,L,↓reduceDIte,q,↓reduceIte,<- y,<- x,jj,K,s,iT,Bool.false_xor];by_cases c:(a,b)∈z/\a∉F.biUnion aF/\b∉F.biUnion aF;{rw[dP c,cM (by tauto),dP c.1,i];by_cases E:((F.biUnion aF).filter (fun w=>a<w/\w<b)).card % 2=1 <;> simp[E]};{rw[cM c];by_cases d:a∈F.biUnion aF\/b∈F.biUnion aF;{rw[dP d]};{rw[cM d,cM (by tauto),mul_zero]}}};{have y:a=⟨v.val,L⟩:=(by simp[a,e7 o]);have x:b=⟨u.val,B⟩:=(by simp[b,e7 o]);have s:v.val<u.val:=o;simp only[gh,B,L,↓reduceDIte,e7 o,o,↓reduceIte,<- y,<- x,jj,K,s,iy,Bool.true_xor];by_cases c:(a,b)∈z/\a∉F.biUnion aF/\b∉F.biUnion aF;{rw[dP c,cM (by tauto),dP c.1,i];by_cases E:((F.biUnion aF).filter (fun w=>a<w/\w<b)).card % 2=1 <;> simp[E]};{rw[cM c];by_cases d:a∈F.biUnion aF\/b∈F.biUnion aF;{rw[dP d,neg_zero]};{rw[cM d,cM (by tauto),mul_zero,neg_zero]}}}
lemma ou{n:Nat}(K:ES n)(ao:∀ e∈K,e.1<e.2){a1:LB}(hE:dA K a1)(r:Sf n){ah:LB}(ap:∀ a b:Fin n,fa (eV (un r.length)) (jI (un n) (un a.val) (un b.val)) ah=un (cZ r (a,b))){F:ES n}{a0:LB}(S:dA F a0)(k T:Nat)(Q:PZ)(o:LB)(hP:∀ d<T,rep (un k) (eN (un k) (un d) o) (Q.coeff d))(u v:Fin (2*n))(c:Bo)(j:Nat)(az:j<T):rep (un k) (ot (un k) (un n) (un r.length) a1 ah a0 o (un u.val) (un v.val) (cF c) (un j)) ((Q*((if c then (-1:PZ) else 1)*gh (jj (fw K r) F) u v)).coeff j):=by
 have i:∀(b:Bo),rep (un k) (fJ (un k)) ((Q*((if b then (-1:PZ) else 1)*(0:PZ))).coeff j):=fun b=>by
  simp only[mul_zero,jY];exact h6 (un k)
 have q:∀(s:Bo) (d:Nat),rep (un k) (gT (l8 (un d) (un j)) (fJ (un k)) (lV (un k) (qk (cF s) (cF c)) (eN (un k) (rX (un j) (un d)) o))) ((Q*((if c then (-1:PZ) else 1)*((if s then (-1:PZ) else 1)*X^d))).coeff j):=fun s d=>by
  have ae:(if c then (-1:PZ) else 1)*((if s then (-1:PZ) else 1)*X^d)=(if xor s c then (-1:PZ) else 1)*X^d:=(by cases s <;> cases c <;> simp);rw[ae,jd,iI,J,J,dE,ue,vK];by_cases hd:d<=j;{simp only[hd,iy,↓reduceIte];exact tx (hP (j-d) (by omega)) (xor s c)};{simp only[hd,iT,eX,↓reduceIte];exact h6 (un k)}
 dsimp only[ot];by_cases E:u.val<n <;> by_cases B:v.val<n;{have M:lQ (un u.val) (un n)=cF true:=(by rw[iZ,J,J,jG E]);have P:lQ (un v.val) (un n)=cF true:=(by rw[iZ,J,J,jG B]);simp only[M,P,dE,↓reduceIte];by_cases L:u=v;{subst L;have a5:p5 (un u.val) (un u.val)=cF true:=(by rw[nw];simp);simp only[a5,hY,sQ,uG];exact i c};{have a8:u.val≠v.val:=fun h=>L (bL h);let a:Fin n:=if u<v then ⟨u.val,E⟩ else ⟨v.val,B⟩;let b:Fin n:=if u<v then ⟨v.val,B⟩ else ⟨u.val,E⟩;have aw:gT (lQ (un u.val) (un v.val)) (un v.val) (un u.val)=un a.val:=(by rw[iZ,J,J,dE];by_cases h:u<v <;> simp[a,h]);have av:gT (lQ (un u.val) (un v.val)) (un u.val) (un v.val)=un b.val:=(by rw[iZ,J,J,dE];by_cases h:u<v <;> simp[b,h]);have al:mc (p5 (un u.val) (un v.val))=cF true:=(by rw[nw,J,J,hY,iw a8];rfl);have am:dQ (jI (un n) (un a.val) (un b.val)) a1=cF (decide ((a,b)∈K)):=(by rw[kg,eG,J,hE.2 a b]);have ag:=k5 S a;have af:=k5 S b;have an:tn (kk (bX iW [true] (un n) (Z (un n) (Z a0 (Z (un a.val) (un b.val))))))=cF (decide (((F.biUnion aF).filter (fun w=>a<w/\w<b)).card % 2=1)):=(by rw[tH S a b,tq]);have aa:fa (eV (un r.length)) (jI (un n) (un a.val) (un b.val)) ah=un (cZ r (a,b)):=ap a b;rw[aw,av,al,am,ag,af,an,aa];simp only[hY,dx,nX];rw[vN K ao r F E B L];by_cases y:(a,b)∈K/\a∉F.biUnion aF/\b∉F.biUnion aF;{have ai:(decide ((a,b)∈K)&&(!decide (a∈F.biUnion aF)&&!decide (b∈F.biUnion aF)))=true:=(by simp[y.1,y.2.1,y.2.2]);rw[ai,dP y];have a9:lQ (un v.val) (un u.val)=cF (decide (v.val<u.val)):=(by rw[iZ,J,J]);rw[a9,ue];have z:gz (cF true) (l8 (un (cZ r (a,b))) (un j))=l8 (un (cZ r (a,b))) (un j):=(by rw[iI,dx,nX]);rw[z];exact q _ (cZ r (a,b))};{have aj:(decide ((a,b)∈K)&&(!decide (a∈F.biUnion aF)&&!decide (b∈F.biUnion aF)))=false:=(by apply Bool.eq_false_iff.mpr;intro h;simp only[gy,sP,cG,qD] at h;exact y h);rw[aj,cM y,iI,dx,kM,dE,cM sK];exact i c}}}
 {have M:lQ (un u.val) (un n)=cF true:=(by rw[iZ,J,J,jG E]);have P:lQ (un v.val) (un n)=cF false:=(by rw[iZ,J,J,iw B]);have a4:p5 (un u.val++un v.val++[true]) (un n++un n)=cF (decide (u.val+v.val+1=2*n)):=(by rw[nw,dL,dL,dL,J,J,J,lv];congr 1;apply Bool.eq_iff_iff.mpr;simp only[cG];omega);simp only[M,P,dE,↓reduceIte,eX,a4,gh,E,B,↓reduceDIte];by_cases x:u.val+v.val+1=2*n;{rw[dP x,jG x];have z:gz (cF true) (l8 (un 0) (un j))=l8 (un 0) (un j):=(by rw[iI,dx,nX]);change rep (un k) (gT (gz (cF true) (l8 (un 0) (un j))) (fJ (un k)) (lV (un k) (qk (cF false) (cF c)) (eN (un k) (rX (un j) (un 0)) o))) _;rw[z];simpa only[eX,↓reduceIte,j9,pow_zero,kQ] using q false 0};{rw[cM x,iw x];rw[iI,dx,kM,dE,cM sK];exact i c}};{have M:lQ (un u.val) (un n)=cF false:=(by rw[iZ,J,J,iw E]);have P:lQ (un v.val) (un n)=cF true:=(by rw[iZ,J,J,jG B]);have a4:p5 (un u.val++un v.val++[true]) (un n++un n)=cF (decide (u.val+v.val+1=2*n)):=(by rw[nw,dL,dL,dL,J,J,J,lv];congr 1;apply Bool.eq_iff_iff.mpr;simp only[cG];omega);simp only[M,P,dE,↓reduceIte,eX,a4,gh,E,B,↓reduceDIte];by_cases x:u.val+v.val+1=2*n;{rw[dP x,jG x];have z:gz (cF true) (l8 (un 0) (un j))=l8 (un 0) (un j):=(by rw[iI,dx,nX]);change rep (un k) (gT (gz (cF true) (l8 (un 0) (un j))) (fJ (un k)) (lV (un k) (qk (cF true) (cF c)) (eN (un k) (rX (un j) (un 0)) o))) _;rw[z];simpa only[↓reduceIte,pow_zero,kQ] using q true 0};{rw[cM x,iw x];rw[iI,dx,kM,dE,cM sK];exact i c}}
 ·
  have M:lQ (un u.val) (un n)=cF false:=(by rw[iZ,J,J,iw E]);have P:lQ (un v.val) (un n)=cF false:=(by rw[iZ,J,J,iw B]);simp only[M,P,dE,eX,↓reduceIte,gh,E,B,↓reduceDIte];by_cases ad:u=v;{subst ad;have a5:mc (p5 (un u.val) (un u.val))=cF false:=(by rw[nw,hY];simp);rw[a5,iI,dx,kM,dE,cM sK,cM (jH u),cM (jH u)];exact i c}
  ·
   have au:u.val≠v.val:=fun h=>ad (bL h);have ar:mc (p5 (un u.val) (un v.val))=cF true:=(by rw[nw,J,J,hY,iw au];rfl);have ak:lQ (un v.val) (un u.val)=cF (decide (v.val<u.val)):=(by rw[iZ,J,J])
   have hB:(if u<v then (1:PZ) else if v<u then -1 else 0)=(if decide (v.val<u.val) then (-1:PZ) else 1)*X^0:=by
    rcases iR ad with h|h
    {have h1:¬(v.val<u.val):=(by have:u.val<v.val:=h;omega);simp[h,h1]};{have h1:v.val<u.val:=h;simp[e7 h,h,h1]}
   rw[ar,ak,hB];have z:gz (cF true) (l8 (un 0) (un j))=l8 (un 0) (un j):=(by rw[iI,dx,nX]);change rep (un k) (gT (gz (cF true) (l8 (un 0) (un j))) (fJ (un k)) (lV (un k) (qk (cF (decide (v.val<u.val))) (cF c)) (eN (un k) (rX (un j) (un 0)) o))) _;rw[z];exact q (decide (v.val<u.val)) 0
lemma ud(k n T:Nat)(c:Nat->Nat->Nat->LB)(z:∀ h<n,∀ w<2*n,∀ d<T,(c h w d).length=k):let j:=(List.range n).flatMap (fun h=>(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d)))
 j.length=n*(2*n)*T*k/\
 ∀(h:Fin n) (w:Fin (2*n)) (d:Nat) (_:d<T),eN (un k) (un d) (jM (un k) (un n) (un T) j (un h.val) (un w.val))=c h.val w.val d:=by
 intro j
 have o:∀ h<n,∀ w<2*n,((List.range T).flatMap (fun d=>c h w d)).length=T*k:=fun h E w K=>by
  rw[gx];have B:(List.range T).map (fun d=>(c h w d).length)=(List.range T).map (fun _=>k):=dF fun d hd=>z h E w K d (aY.mp hd);rw[B];simp
 have u:∀ h<n,((List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d))).length=(2*n)*(T*k):=fun h E=>by
  rw[gx];have B:(List.range (2*n)).map (fun w=>((List.range T).flatMap (fun d=>c h w d)).length)=(List.range (2*n)).map (fun _=>T*k):=dF fun w K=>o h E w (aY.mp K);rw[B];simp
 have q:j.length=n*(2*n)*T*k:=(by rw[show j=(List.range n).flatMap (fun h=>(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d))) from rfl,gx];have B:(List.range n).map (fun h=>((List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d))).length)=(List.range n).map (fun _=>(2*n)*(T*k)):=dF fun h E=>u h (aY.mp E);rw[B];simp;ring);refine⟨q,fun h w d hd=>?_⟩;have v:j=((List.range n).flatMap (fun a=>(List.range (2*n)).map (fun b=>(a,b)))).flatMap (fun p=>(List.range T).flatMap (fun d=>c p.1 p.2 d)):=(by rw[show j=(List.range n).flatMap (fun h=>(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d))) from rfl,gg];refine dG fun a _=>?_;rw[nP]);have i:h.val*(2*n)+w.val<((List.range n).flatMap (fun a=>(List.range (2*n)).map (fun b=>(a,b)))).length:=(by simp only[gx,ft,lx,List.map_const',sum_replicate,n0];nlinarith [h.isLt,w.isLt])
 have a3:((List.range n).flatMap (fun a=>(List.range (2*n)).map (fun b=>(a,b))))[h.val*(2*n)+w.val]'i=(h.val,w.val):=by
  have a4:∀(r a b:Nat),a<r->b<2*n->((List.range r).flatMap (fun x=>(List.range (2*n)).map (fun y=>(x,y)))).getD (a*(2*n)+b) (0,0)=(a,b):=by
   intro r;induction r with
   | zero=>intro a _ P;omega
   | succ r ih=>intro a b P M;rw[nQ,mJ,eY,flatMap_nil,cR];have e:((List.range r).flatMap (fun x=>(List.range (2*n)).map (fun y=>(x,y)))).length=r*(2*n):=(by simp[gx]);have s:((List.range (2*n)).map (fun y=>(r,y))).length=2*n:=(by simp);by_cases a8:a<r;{have S:a*(2*n)+b<r*(2*n):=(by nlinarith);rw[cQ _ _ (by rw[dL,e];omega),uI (by rw[e];exact S),<- cQ _ (0,0) (by rw[e];exact S)];exact ih a b a8 M};{have a9:a=r:=(by omega);subst a9;rw[cQ _ _ (by rw[dL,e,s];omega),sx (by rw[e];omega)];simp[e]}
  rw[<- cQ _ (0,0) i];exact a4 n h.val w.val h.isLt w.isLt
 have L:jM (un k) (un n) (un T) j (un h.val) (un w.val)=(List.range T).flatMap (fun d=>c h.val w.val d):=by
  unfold jM;have ab:un n++un n=un (2*n):=(by rw[g6];congr 1;omega);rw[ab,kg,v];rw[fo _ _ (dS (un T) (un k)) (h.val*(2*n)+w.val) i (fun p Q=>by
   simp only[gM,cC,aY] at Q;rcases Q with ⟨a,P,b,M,rfl⟩
   rw[gS,J];exact o a P b M)]
  rw[a3]
 rw[L];rw[fo (List.range T) (fun d=>c h.val w.val d) (un k) d (by simp[hd]) (fun d' a6=>by rw[J];exact z h.val h.isLt w.val w.isLt d' (aY.mp a6))];simp
def k8{n:Nat}(k T:Nat)(c:Fin n->Fin (2*n)->PZ)(b:LB):Prop:=b.length=n*(2*n)*T*k/\∀(h:Fin n) (w:Fin (2*n)) (d:Nat),d<T->rep (un k) (eN (un k) (un d) (jM (un k) (un n) (un T) b (un h.val) (un w.val))) ((c h w).coeff d)
lemma vv(k n T:Nat):k8 k T (fT (N:=n) (R:=PZ)) (kd (un k) (un n) (un T)):=by
 let c (h w d:Nat):LB:=mj (Z (un d) (Z (un w) (Z (un h) (un k))))
 have b:∀ h<n,∀ w<2*n,∀ d<T,(c h w d).length=k:=fun h _ w _ d _=>by
  simp only[c,mj,left,right,G];unfold gT;split_ifs;{rw[zN,J]};{rw[CQ,J]}
 have v:un n++un n=un (2*n):=(by rw[g6];congr 1;omega)
 have y:kd (un k) (un n) (un T)=(List.range n).flatMap (fun h=>(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d))):=by
  have j:∀ h<n,∀ w<2*n,pI (Z (un w) (Z (un h) (Z (un k) (un T))))=(List.range T).flatMap (fun d=>c h w d):=fun h i w e=>by
   simp only[pI,left,right,G];rw[bA mj (un k) (un T) _ (fun d hd=>by rw[J];exact (b h i w e d (by simpa using hd)).le),J]
  have o:∀ h<n,∀ w<2*n,(pI (Z (un w) (Z (un h) (Z (un k) (un T))))).length=T*k:=fun h i w e=>by
   rw[j h i w e,gx];have x:(List.range T).map (fun d=>(c h w d).length)=(List.range T).map (fun _=>k):=dF fun d hd=>b h i w e d (aY.mp hd);rw[x];simp
  have q:∀ h<n,pH (Z (un h) (Z (un k) (Z (un n) (un T))))=(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>c h w d)):=fun h i=>by
   simp only[pH,left,right,G,v];rw[bA pI (dS (un T) (un k)) (un (2*n)) _ (fun w e=>by rw[gS,J];exact (o h i w (by simpa using e)).le),J];exact dG fun w e=>j h i w (aY.mp e)
  have r:∀ h<n,(pH (Z (un h) (Z (un k) (Z (un n) (un T))))).length=(2*n)*(T*k):=fun h i=>by
   rw[q h i,gx];have x:(List.range (2*n)).map (fun w=>((List.range T).flatMap (fun d=>c h w d)).length)=(List.range (2*n)).map (fun _=>T*k):=dF fun w e=>by rw[<- j h i w (aY.mp e)];exact o h i w (aY.mp e)
   rw[x];simp
  unfold kd;rw[v,bA pH (dS (un (2*n)) (dS (un T) (un k))) (un n) _ (fun h i=>by rw[gS,gS,J];exact (r h (by simpa using i)).le),J];exact dG fun h i=>q h (aY.mp i)
 rw[k8,y];have u:=ud k n T c b;refine⟨u.1,fun h w d hd=>?_⟩;rw[u.2 h w d hd];simp only[c,mj,left,right,G,g6,eR,nw,J,mL,dx,dE,fT];have z:h.val+h.val+1=2*h.val+1:=(by omega);rw[z];by_cases e:w.val=2*h.val+1 <;> by_cases s:d=0;{subst s;simp only[e,iy,Bool.and_self,↓reduceIte,Polynomial.coeff_one_zero];simpa using xe (un k) [true]};{simp only[e,s,iy,iT,s3,eX,↓reduceIte,coeff_one];exact h6 (un k)};{simp only[e,iT,kM,eX,↓reduceIte,jY];exact h6 (un k)};{simp only[e,iT,kM,eX,↓reduceIte,jY];exact h6 (un k)}
lemma vT{n:Nat}(ao:ES n)(aj:∀ e∈ao,e.1<e.2){L:LB}(hE:dA ao L)(v:Sf n){an:LB}(ak:∀ a b:Fin n,fa (eV (un v.length)) (jI (un n) (un a.val) (un b.val)) an=un (cZ v (a,b))){F:ES n}{z:LB}(hF:dA F z)(k T:Nat)(M:Fin n->Fin (2*n)->PZ)(c:LB)(au:k8 k T M c)(ap:Nat):let i:=Z (un k) (Z (un n) (Z (un v.length) (Z (un T) (Z L (Z an z)))))
 k8 k T (fU (gh (jj (fw ao v) F)) M) (ke (Z (un ap) (Z i c))):=by
 intro i;let P:=gh (jj (fw ao v) F);have o:n1 i=un k:=(by simp only[n1,i,left,G]);have s:oP i=un n:=(by simp only[oP,i,left,right,G]);have aa:vb i=un v.length:=(by simp only[vb,i,left,right,G]);have y:qX i=un T:=(by simp only[qX,i,left,right,G]);have ad:u9 i=L:=(by simp only[u9,i,left,right,G]);have ae:u8 i=an:=(by simp only[u8,i,left,right,G]);have ab:va i=z:=(by simp only[va,i,right,G]);have ah:un n++un n=un (2*n):=mw n;let r (h w d:Nat):LB:=ml (Z (un d) (Z (un w) (Z (un h) (Z i c))))
 have q:∀ h<n,∀ w<2*n,∀ d<T,(r h w d).length=k:=fun h _ w _ d _=>by
  simp only[r,ml,left,right,G,o];rw[y0,J]
 have b0:ke (Z (un ap) (Z i c))=(List.range n).flatMap (fun h=>(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>r h w d))):=by
  have a4:∀ h<n,∀ w<2*n,pK (Z (un w) (Z (un h) (Z i c)))=(List.range T).flatMap (fun d=>r h w d):=fun h E w K=>by
   simp only[pK,left,right,G,o,y];rw[bA ml (un k) (un T) _ (fun d hd=>by rw[J];exact (q h E w K d (by simpa using hd)).le),J]
  have a6:∀ h<n,∀ w<2*n,(pK (Z (un w) (Z (un h) (Z i c)))).length=T*k:=fun h E w K=>by
   rw[a4 h E w K,gx];have Q:(List.range T).map (fun d=>(r h w d).length)=(List.range T).map (fun _=>k):=dF fun d hd=>q h E w K d (aY.mp hd);rw[Q];simp
  have af:∀ h<n,pJ (Z (un h) (Z i c))=(List.range (2*n)).flatMap (fun w=>(List.range T).flatMap (fun d=>r h w d)):=fun h E=>by
   simp only[pJ,left,right,G,o,s,y,ah];rw[bA pK (dS (un T) (un k)) (un (2*n)) _ (fun w K=>by rw[gS,J];exact (a6 h E w (by simpa using K)).le),J];exact dG fun w K=>a4 h E w (aY.mp K)
  have ag:∀ h<n,(pJ (Z (un h) (Z i c))).length=(2*n)*(T*k):=fun h E=>by
   rw[af h E,gx];have Q:(List.range (2*n)).map (fun w=>((List.range T).flatMap (fun d=>r h w d)).length)=(List.range (2*n)).map (fun _=>T*k):=dF fun w K=>by rw[<- a4 h E w (aY.mp K)];exact a6 h E w (aY.mp K)
   rw[Q];simp
  simp only[ke,left,right,G,o,s,y,ah];rw[bA pJ (dS (un (2*n)) (dS (un T) (un k))) (un n) _ (fun h E=>by rw[gS,gS,J];exact (ag h (by simpa using E)).le),J];exact dG fun h E=>af h (aY.mp E)
 rw[k8,b0];have aw:=ud k n T r q;refine⟨aw.1,fun h w d hd=>?_⟩;rw[aw.2 h w d hd]
 have a0:∀(j:Fin n),rep (un k) (iv ir (un k) (un n++un n) (Z i (Z c (Z (un j.val) (un d))))) ((∑ u:Fin (2*n),if 2*j.val+1<=u.val then M j u*(- P u (V j)) else 0).coeff d):=fun j=>by
  rw[fx,ah];rw[<- fX (fun u:Fin (2*n)=>(if 2*j.val+1<=u.val then M j u*(- P u (V j)) else 0).coeff d)];have hU:∀ u<(un (2*n)).length,rep (un k) (ir (Z (un u) (Z i (Z c (Z (un j.val) (un d)))))) (if B:u<2*n then (if 2*j.val+1<=u then M j ⟨u,B⟩*(- P ⟨u,B⟩ (V j)) else 0).coeff d else 0):=(by intro u B;have x:u<2*n:=(by simpa only[J] using B);rw[cT x];simp only[ir,left,right,G,o,s,aa,y,ad,ae,ab,mw,eR,iI,J,dE];by_cases a9:2*j.val+1<=u;{simp only[a9,iy,↓reduceIte];have Q:=ou ao aj hE v ak hF k T (M j ⟨u,x⟩) (jM (un k) (un n) (un T) c (un j.val) (un u)) (au.2 j ⟨u,x⟩) ⟨u,x⟩ (V j) true d hd;simpa only[cF,V,↓reduceIte,neg_mul,j9] using Q};{simp only[a9,iT,eX,↓reduceIte,jY];exact h6 (un k)});simpa only[J] using i7 ir (un k) (un (2*n)) (Z i (Z c (Z (un j.val) (un d)))) (fun u=>if B:u<2*n then (if 2*j.val+1<=u then M j ⟨u,B⟩*(- P ⟨u,B⟩ (V j)) else 0).coeff d else 0) hU
 simp only[r,ml,left,right,G,o,s,fU,sD];refine xd ?_ ?_
 ·
  have ay:vy (un w.val)=un (aA w).val:=(by rw[yx];rfl);rw[ay,nh,tZ,iI,iI,J,J,J,J,dx,dE];by_cases am:2*h.val+1<=w.val
  ·
   by_cases av:2*h.val+2<=(aA w).val
   ·
    simp only[am,av,iy,Bool.and_self,↓reduceIte];rw[fx,ah];rw[<- fX (fun u:Fin (2*n)=>(if 2*h.val+1<=u.val then M h u*P u (aA w)*j0 (aA w) else 0).coeff d)]
    have hU:∀ u<(un (2*n)).length,rep (un k) (n7 (Z (un u) (Z i (Z c (Z (un h.val) (Z (un (aA w).val) (un d))))))) (if B:u<2*n then (if 2*h.val+1<=u then M h ⟨u,B⟩*P ⟨u,B⟩ (aA w)*j0 (aA w) else 0).coeff d else 0):=by
     intro u B;have x:u<2*n:=(by simpa only[J] using B);rw[cT x];simp only[n7,left,right,G,o,s,aa,y,ad,ae,ab,nh,iI,J,dE];by_cases a9:2*h.val+1<=u
     ·
      simp only[a9,iy,↓reduceIte,tq];have Q:=ou ao aj hE v ak hF k T (M h ⟨u,x⟩) (jM (un k) (un n) (un T) c (un h.val) (un u)) (au.2 h ⟨u,x⟩) ⟨u,x⟩ (aA w) (decide ((aA w).val % 2=1)) d hd
      have ax:(if decide ((aA w).val % 2=1) then (-1:PZ) else 1)*P ⟨u,x⟩ (aA w)=P ⟨u,x⟩ (aA w)*j0 (aA w):=by
       unfold j0;rcases uL (aA w).val with az|aq
       {simp[az]};{simp[aq]}
      rw[mR,<- ax];exact Q
     {simp only[a9,iT,eX,↓reduceIte,jY];exact h6 (un k)}
    simpa only[J] using i7 n7 (un k) (un (2*n)) (Z i (Z c (Z (un h.val) (Z (un (aA w).val) (un d))))) (fun u=>if B:u<2*n then (if 2*h.val+1<=u then M h ⟨u,B⟩*P ⟨u,B⟩ (aA w)*j0 (aA w) else 0).coeff d else 0) hU
   {simp only[am,av,iy,iT,s3,eX,↓reduceIte,jY];exact h6 (un k)}
  {simp only[am,iT,kM,eX,↓reduceIte,jY];exact h6 (un k)}
 {simp only[nh,nw,J,dE];by_cases K:w.val=2*h.val+1;{simp only[K,iy,↓reduceIte,fx];rw[<- fX (fun j:Fin n=>(if j.val<h.val then ∑ u:Fin (2*n),if 2*j.val+1<=u.val then M j u*(- P u (V j)) else 0 else 0).coeff d)];have b2:∀ j<(un n).length,rep (un k) (lW (Z (un j) (Z i (Z c (Z (un h.val) (un d)))))) (if S:j<n then (if j<h.val then ∑ u:Fin (2*n),if 2*j+1<=u.val then M ⟨j,S⟩ u*(- P u (V ⟨j,S⟩)) else 0 else 0).coeff d else 0):=(by intro j S;have ai:j<n:=(by simpa only[J] using S);rw[cT ai];simp only[lW,left,right,G,o,s,iZ,J,dE];by_cases ar:j<h.val;{simp only[ar,iy,↓reduceIte];exact a0 ⟨j,ai⟩};{simp only[ar,iT,eX,↓reduceIte,jY];exact h6 (un k)});simpa only[J] using i7 lW (un k) (un n) (Z i (Z c (Z (un h.val) (un d)))) (fun j=>if S:j<n then (if j<h.val then ∑ u:Fin (2*n),if 2*j+1<=u.val then M ⟨j,S⟩ u*(- P u (V ⟨j,S⟩)) else 0 else 0).coeff d else 0) b2};{simp only[K,iT,eX,↓reduceIte,jY];exact h6 (un k)}}
lemma n3{n:Nat}(hn:1<=n)(K:ES n)(a6:∀ e∈K,e.1<e.2){v:LB}(hE:dA K v)(j:Sf n){S:LB}(a7:∀ a b:Fin n,fa (eV (un j.length)) (jI (un n) (un a.val) (un b.val)) S=un (cZ j (a,b))){F:ES n}{s:LB}(hF:dA F s)(k T:Nat)(d:Nat)(aj:d<T):let c:=Z (un k) (Z (un n) (Z (un j.length) (Z (un T) (Z v (Z S s)))))
 rep (un k) (qc c (g7 c) (un d)) ((jn (gh (jj (fw K j) F))).coeff d):=by
 intro c;let w:=gh (jj (fw K j) F);have r:n1 c=un k:=(by simp only[n1,c,left,G]);have q:oP c=un n:=(by simp only[oP,c,left,right,G]);have ab:vb c=un j.length:=(by simp only[vb,c,left,right,G]);have a1:qX c=un T:=(by simp only[qX,c,left,right,G]);have ae:u9 c=v:=(by simp only[u9,c,left,right,G]);have af:u8 c=S:=(by simp only[u8,c,left,right,G]);have ad:va c=s:=(by simp only[va,c,right,G]);have ak:un n++un n=un (2*n):=mw n;let M:=dS (un n) (dS (un n++un n) (dS (un T) (un k)));have L:M.length=n*(2*n)*T*k:=(by simp only[M,ak,gS,J];ring)
 have ai:k8 k T ((fU w)^[n-1] fT) (g7 c):=by
  unfold g7;simp only[r,q,a1];rw[kn];have y:(un n).tail.length=n-1:=(by simp[un]);rw[y]
  have aa:∀(z:Ls Nat),k8 k T ((fU w)^[z.length] fT) (z.foldr (fun i x=>f5 M (ke (Z (un i) (Z c x))) x) (kd (un k) (un n) (un T))):=by
   intro z;induction z with
   | nil=>exact vv k n T
   | cons i a5 ih=>
     simp only[sA,aX,jb]
     let st:=a5.foldr (fun i x=>f5 M (ke (Z (un i) (Z c x))) x)
      (kd (un k) (un n) (un T))
     have a0:=vT K a6 hE j a7 hF k T ((fU w)^[a5.length] fT) st ih i;have P:(ke (Z (un i) (Z c st))).length<=M.length:=(by rw[a0.1,L]);rw[f5,o8 P];exact a0
  simpa only[lx] using aa (List.range (n-1))
 rw[<- tJ hn w (xp _) (uG _),uD,fx];unfold qc;simp only[r,q];rw[<- fX (fun h:Fin n=>(∑ u:Fin (2*n),if 2*h.val+1<=u.val then ((fU w)^[n-1] fT) h u*(- w u (V h)) else 0).coeff d)];have hH:∀ h<(un n).length,rep (un k) (kY (Z (un h) (Z c (Z (g7 c) (un d))))) (if E:h<n then (∑ u:Fin (2*n),if 2*h+1<=u.val then ((fU w)^[n-1] fT) ⟨h,E⟩ u*(- w u (V ⟨h,E⟩)) else 0).coeff d else 0):=(by intro h E;have o:h<n:=(by simpa only[J] using E);rw[cT o];simp only[kY,left,right,G,r,q,ak,fx];rw[<- fX (fun u:Fin (2*n)=>(if 2*h+1<=u.val then ((fU w)^[n-1] fT) ⟨h,o⟩ u*(- w u (V ⟨h,o⟩)) else 0).coeff d)];have hU:∀ u<(un (2*n)).length,rep (un k) (ir (Z (un u) (Z c (Z (g7 c) (Z (un h) (un d)))))) (if B:u<2*n then (if 2*h+1<=u then ((fU w)^[n-1] fT) ⟨h,o⟩ ⟨u,B⟩*(- w ⟨u,B⟩ (V ⟨h,o⟩)) else 0).coeff d else 0):=(by intro u B;have Q:u<2*n:=(by simpa only[J] using B);rw[cT Q];simp only[ir,left,right,G,r,q,ab,a1,ae,af,ad,mw,eR,iI,J,dE];by_cases P:2*h+1<=u;{simp only[P,iy,↓reduceIte];have hm:=ou K a6 hE j a7 hF k T (((fU w)^[n-1] fT) ⟨h,o⟩ ⟨u,Q⟩) (jM (un k) (un n) (un T) (g7 c) (un h) (un u)) (ai.2 ⟨h,o⟩ ⟨u,Q⟩) ⟨u,Q⟩ (V ⟨h,o⟩) true d aj;simpa only[cF,V,↓reduceIte,neg_mul,j9] using hm};{simp only[P,iT,eX,↓reduceIte,jY];exact h6 (un k)});simpa only[J] using i7 ir (un k) (un (2*n)) (Z c (Z (g7 c) (Z (un h) (un d)))) (fun u=>if B:u<2*n then (if 2*h+1<=u then ((fU w)^[n-1] fT) ⟨h,o⟩ ⟨u,B⟩*(- w ⟨u,B⟩ (V ⟨h,o⟩)) else 0).coeff d else 0) hU);simpa only[J] using i7 kY (un k) (un n) (Z c (Z (g7 c) (un d))) (fun h=>if E:h<n then (∑ u:Fin (2*n),if 2*h+1<=u.val then ((fU w)^[n-1] fT) ⟨h,E⟩ u*(- w u (V ⟨h,E⟩)) else 0).coeff d else 0) hH
lemma yU{n:Nat}(c:Sf n){j:LB}(u:∀ a b:Fin n,fa (eV (un c.length)) (jI (un n) (un a.val) (un b.val)) j=un (cZ c (a,b))){F:ES n}{d:LB}(z:dA F d):yb (un n) (un c.length) j d=un (∑ e∈F,cZ c e):=by
 have x:(eV (un c.length)).length=3*c.length+1:=(by simp[eV,J];omega)
 have w:∀ a<n,∀ b<n,(k7 (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) (Z j d)))))).length<=(eV (un c.length)).length:=fun a h b r=>by
  simp only[k7,left,right,G];rw[u ⟨a,h⟩ ⟨b,r⟩,kg,eG,J,z.2 ⟨a,h⟩ ⟨b,r⟩,dE];split_ifs;{rw[J,x];unfold cZ;have L:rU c (⟨a,h⟩,⟨b,r⟩)<=c.length:=qE _ _;omega};{simp}
 have q:∀(a:Nat) (h:a<n),mi (Z (un a) (Z (un n) (Z (un c.length) (Z j d))))=un (∑ b:Fin n,if (⟨a,h⟩,b)∈F then cZ c (⟨a,h⟩,b) else 0):=fun a h=>by
  simp only[mi,left,right,G];rw[bA k7 (eV (un c.length)) (un n) _ (fun b r=>w a h b (by simpa using r)),J];have v:(List.range n).flatMap (fun b=>k7 (Z (un b) (Z (un a) (Z (un n) (Z (un c.length) (Z j d))))))=(List.range n).flatMap (fun b=>un (if r:b<n then if (⟨a,h⟩,⟨b,r⟩)∈F then cZ c (⟨a,h⟩,⟨b,r⟩) else 0 else 0)):=(by refine dG fun b r=>?_;have s:=aY.mp r;simp only[k7,left,right,G,s,↓reduceDIte];rw[u ⟨a,h⟩ ⟨b,s⟩,kg,eG,J,z.2 ⟨a,h⟩ ⟨b,s⟩,dE];by_cases y:(⟨a,h⟩,⟨b,s⟩)∈F;{simp[y]};{simp[y,un]});rw[v,pN,ji (fun b:Fin n=>if (⟨a,h⟩,b)∈F then cZ c (⟨a,h⟩,b) else 0)]
 unfold yb;rw[bA mi (dS (un n) (eV (un c.length))) (un n) _ (fun a h=>by
  have i:a<n:=(by simpa using h);rw[q a i,J,dS,J,x];have o:∑ b:Fin n,(if (⟨a,i⟩,b)∈F then cZ c (⟨a,i⟩,b) else 0)<=∑ _b:Fin n,(3*c.length+1):=(by refine sum_le_sum fun b _=>?_;split_ifs;{unfold cZ;have L:rU c (⟨a,i⟩,b)<=c.length:=qE _ _;omega};{omega});simpa[qP,n0] using o),J]
 have v:(List.range n).flatMap (fun a=>mi (Z (un a) (Z (un n) (Z (un c.length) (Z j d)))))=(List.range n).flatMap (fun a=>un (if h:a<n then ∑ b:Fin n,if (⟨a,h⟩,b)∈F then cZ c (⟨a,h⟩,b) else 0 else 0)):=(by refine dG fun a h=>?_;have i:=aY.mp h;rw[cT i,q a i]);rw[v,pN,ji (fun a:Fin n=>∑ b:Fin n,if (a,b)∈F then cZ c (a,b) else 0)];congr 1;rw[<- sum_product',univ_product_univ,sum_ite_mem,univ_inter]
lemma p9{d c:Type*}[Zero c](xs:Ls d)(f:d->c):xs.map f=(List.range xs.length).map (fun i=>if b:i<xs.length then f xs[i] else 0):=by apply jD;{simp};{intro i b _;simp only[ft] at b;simp[b]}
noncomputable def g3{n:Nat}(d:ES n)(b:Sf n)(c:Nat)(C:Ft (CP n)):Int:=(X^cO b*((-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,fw d b e.1 e.2)*jn (gh (jj (fw d b) (bF C))))).coeff c
lemma wJ{n k:Nat}(hn:1<=n)(o:ES n)(a8:∀ e∈o,e.1<e.2){w:LB}(hE:dA o w)(c:Sf n){bd:LB}(b3:∀ a b:Fin n,fa (eV (un c.length)) (jI (un n) (un a.val) (un b.val)) bd=un (cZ c (a,b)))(aw:LB)(bh:∀ r<k,∀ j≤r,(aJ (bB o) j).length*(((bB o).length+1)+n*n+2)+1<=aw.length)(T d:Nat)(bn:d<T)(v:LB)(u:v=Z aw (Z (un k) (Z (un n) (Z (un c.length) (Z (un T) (Z w (Z bd (Z (un (cO c)) (Z (gO (un n) w) (eD (un n) w)))))))))):rep (un k) (mY v (un d)) ((X^cO c * ∑ M∈cE n,∏ e∈M,fw o c e.1 e.2).coeff d):=by
 have ap:uE v=aw:=(by rw[u];simp only[uE,left,G]);have a5:rQ v=un k:=(by rw[u];simp only[rQ,left,right,G]);have ar:w7 v=un n:=(by rw[u];simp only[w7,left,right,G]);have b8:t8 v=un c.length:=(by rw[u];simp only[t8,left,right,G]);have b7:x8 v=un T:=(by rw[u];simp only[x8,left,right,G]);have b9:x7 v=w:=(by rw[u];simp only[x7,left,right,G]);have ba:x6 v=bd:=(by rw[u];simp only[x6,left,right,G]);have af:tc v=un (cO c):=(by rw[u];simp only[tc,left,right,G]);have aq:w8 v=un (bB o).length:=(by rw[u];simp only[w8,left,right,G,mW hE]);have az:wI v=eD (un n) w:=(by rw[u];simp only[wI,right,G]);clear u;let L:=bB o;let E:=L.length
 have a0:rep (un k) (mY v (un d)) ((List.range k).map (fun r=>∑ C∈(cH o).powerset.filter (fun C=>C.card=r/\aQ (bF C)),g3 o c d C)).sum:=by
  unfold mY;simp only[a5]
  have hR:∀ r<(un k).length,rep (un k) (oh (Z (un r) (Z v (un d)))) (∑ C∈(cH o).powerset.filter (fun C=>C.card=r/\aQ (bF C)),g3 o c d C):=by
   intro r hr;have b5:r<k:=(by simpa only[J] using hr);simp only[oh,left,right,G,ap,a5,ar,aq,az];have c1:=vP hE aw r (bh r b5);obtain⟨s,b0,z,a3⟩:=c1;rw[b0];simp only[G];have b4:dZ (un E) (un n)=un ((E+1)+n*n):=(by simp only[dZ,eR,gS,g6])
   have ad:∀ x∈s,x.length=(dZ (un E) (un n)).length:=fun x hx=>by
    obtain⟨i,Q,rfl⟩:=mem_iff_getElem.mp hx;obtain⟨Fb,P,bl⟩:=a3 i (z▸Q);rw[cQ _ _ Q] at bl;rw[bl,dL,qd,b4,J,J,P.1]
   have bf:rep (un k) (rV (un k) (ti (un k) (oT (un k) [true,true])) (un r)) ((-2:Int)^r):=(by have h2:rep (un k) (oT (un k) [true,true]) (2:Int):=xe (un k) [true,true];simpa only[J] using y2 (xf h2) (un r));rw[<- su o r (g3 o c d)];rw[p9 (aJ L r) (fun B=>g3 o c d (dR L B))]
   have au:∀ y<(un (aJ L r).length).length,rep (un k) (og (Z (un y) (Z v (Z s.flatten (Z (rV (un k) (ti (un k) (oT (un k) [true,true])) (un r)) (un d)))))) (if Q:y<(aJ L r).length then g3 o c d (dR L (aJ L r)[y]) else 0):=by
    intro y bi;have a2:y<(aJ L r).length:=(by simpa only[J] using bi);rw[cT a2];let B:=(aJ L r)[y];let C:=dR L B;let F:=bF C;have aa:B∈aJ L r:=iQ a2;obtain⟨ab,ak,al,bp⟩:=(gv L r B).mp aa;have av:C.card=r:=(by rw[nb (lH o) B (ak.imp (fun h=>bS h)) al,ab]);have bb:cU L B=F:=je L B
    have a7:F⊆o:=by
     intro e S;obtain⟨p,bx,bm⟩:=bT.mp S;obtain⟨q,_,bv,rfl⟩:=(hX L B p).mp bx;have bw:=(jJ o _).mp (iQ bv);have b2:=mem_product.mp (aL.mp bw).1;simp only[aV,bI] at bm;rcases bm with rfl|rfl
     {exact b2.1};{exact b2.2}
    obtain⟨Fb,P,am⟩:=a3 y a2;rw[bb] at P;have aj:eN (dZ (un E) (un n)) (un y) s.flatten=s.getD y []:=(by have bj:y<s.length:=z.symm▸a2;have c0:s.flatten=s.flatMap id:=(by rw[List.flatMap_id]);rw[c0,cQ _ _ bj];exact fo s id (dZ (un E) (un n)) y bj ad);have ag:fO (un (bB o).length++[true]) (eN (dZ (un (bB o).length) (un n)) (un y) s.flatten)=Fb:=(by change fO (un E++[true]) (eN (dZ (un E) (un n)) (un y) s.flatten)=Fb;rw[aj,am,eR,xS,J];have bg:(dT (un (E+1)) (un (eF B))).length=E+1:=(by rw[qd,J]);rw[drop_append,bg,nY,sZ,uV bg.le,gl]);simp only[og,left,right,G,a5,ar,b8,b7,b9,ba,af,aq,ag,yU c b3 P,g6,iI,J,dE];have an:∏ e∈F,fw o c e.1 e.2=X^(∑ e∈F,cZ c e):=(by have K:∏ e∈F,fw o c e.1 e.2=∏ e∈F,(X:PZ)^cZ c e:=(by refine qN rfl fun e S=>?_;rw[kS a8 c e (a8 e (a7 S)),dP (a7 S)]);rw[K,uM])
    have a9:g3 o c d C=if cO c+∑ e∈F,cZ c e<=d then ((if decide (cr F % 2=1) then -((-2:Int)^r) else (-2:Int)^r)*(jn (gh (jj (fw o c) F))).coeff (d-(cO c+∑ e∈F,cZ c e)))
     else 0:=by
     unfold g3;change (X^cO c*((-2:PZ)^C.card*(-1:PZ)^cr F*(∏ e∈F,fw o c e.1 e.2)*jn (gh (jj (fw o c) F)))).coeff d=_;rw[av,an]
     have ae:(-1:PZ)^cr F=if decide (cr F % 2=1) then -1 else 1:=by
      rw[gC (mod_mod (cr F) 2).symm];rcases uL (cr F) with h0|K
      {simp[h0]};{simp[K]}
     have ai:((-2:PZ)^r*(-1:PZ)^cr F)=Polynomial.C (if decide (cr F % 2=1) then -((-2:Int)^r) else (-2:Int)^r):=(by rw[ae];have c4:(-2:PZ)^r=Polynomial.C ((-2:Int)^r):=(by rw[map_pow];simp);rw[c4];split_ifs <;> simp);have ax:X^cO c*((-2:PZ)^r*(-1:PZ)^cr F*X^(∑ e∈F,cZ c e)*jn (gh (jj (fw o c) F)))=Polynomial.C (if decide (cr F % 2=1) then -((-2:Int)^r) else (-2:Int)^r)*(jn (gh (jj (fw o c) F))*X^(cO c+∑ e∈F,cZ c e)):=(by rw[<- ai,j8];ring);rw[ax,coeff_C_mul];have bo:=jd (jn (gh (jj (fw o c) F))) false (cO c+∑ e∈F,cZ c e) d;simp only[eX,↓reduceIte,j9] at bo;rw[bo];split_ifs <;> simp
    rw[a9];by_cases be:cO c+∑ e∈F,cZ c e<=d;{simp only[be,iy,↓reduceIte,vK,wH P];exact y1 (tx bf (decide (cr F % 2=1))) (n3 hn o a8 hE c b3 P k T (d-(cO c+∑ e∈F,cZ c e)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) bn))};{simp only[be,iT,eX,↓reduceIte];exact h6 (un k)}
   simpa only[J] using i7 og (un k) (un (aJ L r).length) (Z v (Z s.flatten (Z (rV (un k) (ti (un k) (oT (un k) [true,true])) (un r)) (un d)))) (fun y=>if Q:y<(aJ L r).length then g3 o c d (dR L (aJ L r)[y]) else 0) au
  simpa only[J] using i7 oh (un k) (un k) (Z v (un d)) (fun r=>∑ C∈(cH o).powerset.filter (fun C=>C.card=r/\aQ (bF C)),g3 o c d C) hR
 have ay:((List.range k).map (fun r=>∑ C∈(cH o).powerset.filter (fun C=>C.card=r/\aQ (bF C)),g3 o c d C)).sum=(X^cO c * ∑ C∈(cH o).powerset.filter (fun C:Ft (CP n)=>C.card<k/\aQ (bF C)),(-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,fw o c e.1 e.2)*jn (gh (jj (fw o c) (bF C)))).coeff d:=by
  rw[mM,fx];change _=∑ C∈(cH o).powerset.filter (fun C=>C.card<k/\aQ (bF C)),g3 o c d C;have bk:∑ C∈(cH o).powerset.filter (fun C=>C.card<k/\aQ (bF C)),g3 o c d C=∑ r∈Finset.range k,∑ C∈((cH o).powerset.filter (fun C=>C.card<k/\aQ (bF C))).filter (fun C=>C.card=r),g3 o c d C:=(by rw[<- sum_fiberwise_of_maps_to (g:=Finset.card)];intro C hC;exact mem_range.mpr (aL.mp hC).2.1);rw[bk]
  have a4:∀ m (g:Nat->Int),((List.range m).map g).sum=∑ r∈Finset.range m,g r:=fun m g=>by
   induction m with|zero=>{simp}|succ m ih=>{rw[nQ,bR,ic,List.map_singleton,List.sum_singleton,u2,ih]}
  rw[a4];refine dB rfl fun r hr=>?_;have b5:=mem_range.mp hr;refine dB ?_ fun _ _=>rfl;ext C;simp only[aL];constructor;{rintro⟨K,rfl,h3⟩;exact⟨⟨K,b5,h3⟩,rfl⟩};{rintro⟨⟨K,_,h3⟩,rfl⟩;exact⟨K,rfl,h3⟩}
 rw[ay] at a0
 have ao:(X^cO c * ∑ M∈cE n,∏ e∈M,fw o c e.1 e.2).coeff d ≡ (X^cO c * ∑ C∈(cH o).powerset.filter (fun C:Ft (CP n)=>C.card<k/\aQ (bF C)),(-2:PZ)^C.card*(-1:PZ)^cr (bF C)*(∏ e∈bF C,fw o c e.1 e.2)*jn (gh (jj (fw o c) (bF C)))).coeff d [ZMOD (2:Int)^(un k).length]:=by
  rw[J]
  have a6:∀ bt:PZ,(X^cO c*bt).coeff d=if cO c<=d then bt.coeff (d-cO c) else 0:=fun bt=>by
   rw[kP];simpa using jd bt false (cO c) d
  rw[a6,a6];by_cases hb:cO c<=d;{rw[dP hb,dP hb];exact rF o (fw o c) (fun e bz b6=>by rw[kS a8 c e bz,cM b6]) (d-cO c)};{rw[cM hb,cM hb]}
 exact a0.trans ao.symm
lemma xj(n:Nat)(hn:2<=n)(q:Ls (Fv n×Fv n))(u:Sf n)(b7:∀ S⊆((gX n).toFinset.filter (fun e=>∀ z∈q,¬(aF e⊆z.1)/\¬(aF e⊆z.2))),2<=S.card->(∀ e∈S,∀ f∈S,e≠f->Disjoint (aF e) (aF f))->(u.filter (fun t=>t.2&&decide (fy S t))).length=(u.filter (fun t=>!t.2&&decide (fy S t))).length)(k:Nat)(hk:1<=k):let o:=fun j:Nat=>replicate j true++[false]
 let K:=fun (w z:Nat)=>(List.range w).map (fun h=>z.testBit h);let m:=u.length;let Fn:=(Fin n->Bo)->(Fin n->Bo)->Bo
 let ad:=fun (f:Fn) (R T:Fv n)=>
  f (fun i=>decide (i∈R)) (fun j=>decide (j∈T))
 let valid:=fun f:Fn=>(∃ C:PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.Monotone2 C/\C.size+1<=2*n/\
  PEqualNP.Represents.Represents (fun i j:Fin n=>decide (i=j)) C/\
  ∀ x y,f x y=C.eval (ofFn x++ofFn y))/\
  ∀ z∈q,ad f z.1 z.2=false
 let ao:=fun f:Fn=>(gX n).map (fun e=>ad f (aF e) ∅);let size:=fun f:Fn=>((ao f).filter id).length;let a4:=fun f:Fn=>(u.filter (fun t=>decide (ad f t.1.1 t.1.2=t.2))).length;let P:=fun bl:Fv n=>(finRange n).map (fun i=>decide (i∈bl))
 let v:=o n++o q.length++q.flatMap (fun z=>P z.1++P z.2)++
  o m++u.flatMap (fun t=>P t.1.1++P t.1.2++[t.2])
 let x:=o k++v;let L:=fun s j:Nat=>Nat.card {f:Fn // valid f/\size f=s/\a4 f=j}
 let output:=(List.range (n / 2+1)).flatMap (fun s=>
  (List.range (m+1)).flatMap (fun j=>K k (L s j % 2^k)))
 solve (replicate ((x.length+2)^(4*k+1)) true++false::x)=output:=by
 intro o K m Fn ad valid ao size a4 P v x L output;let E:=un ((x.length+2)^(4*k+1));let d:=q.flatMap (fun z=>aK z.1++aK z.2);let c:=u.flatMap (fun t=>aK t.1.1++aK t.1.2++[t.2]);have ab:P=aK:=rfl
 have b5:hd (E++false::x)=E/\jy (E++false::x)=x:=by
  have:=jf ((x.length+2)^(4*k+1)) x
  simpa[E,un,dM] using this
 have b3:hd x=un k/\jy x=v:=jf k v;have b1:hd v=un n/\jy v=o q.length++(d++(o m++c)):=(by have B:=jf n (o q.length++(d++(o m++c)));simpa[v,o,ab,d,c,dM] using B);have b4:hd (o q.length++(d++(o m++c)))=un q.length/\jy (o q.length++(d++(o m++c)))=d++(o m++c):=jf q.length (d++(o m++c))
 have ag:d.length=(dS (un q.length) (un n++un n)).length:=by
  simp only[d,gx,dS,J,dL];have hm:q.map (fun z=>(aK z.1).length+(aK z.2).length)=q.map (fun _=>n+n):=dF fun z _=>by simp[jL]
  rw[hm];simp
 have a7:gY (dS (un q.length) (un n++un n)) (d++(o m++c))=d/\fO (dS (un q.length) (un n++un n)) (d++(o m++c))=o m++c:=(by rw[vZ,xS,<- ag,List.take_left,List.drop_left];exact⟨rfl,rfl⟩);have b2:hd (o m++c)=un m/\jy (o m++c)=c:=jf m c
 have a0:∀ s j,L s j=Nat.card {f:Fn //
  ((∃! p:Pm (Fin n),Involutive p/\∀ a b,f a b=invFun p a b)/\∀ z∈q,f (fun i=>decide (i∈z.1)) (fun j=>decide (j∈z.2))=false)/\
  (((gX n).map (fun e=>f (fun i=>decide (i∈aF e)) (fun j=>decide (j∈(∅:Fv n))))).filter id).length=s/\
  (u.filter (fun t=>decide (f (fun i=>decide (i∈t.1.1)) (fun j=>decide (j∈t.1.2))=t.2))).length=j}:=by
  intro s j;apply Nat.card_congr;refine Equiv.subtypeEquivRight fun f=>?_;have ar:=L853.v8.vD n hn f;simp only[valid,ad,size,ao,a4,invFun];exact⟨fun ⟨⟨B,Q⟩,h3,h4⟩=>⟨⟨ar.mp B,Q⟩,h3,h4⟩,fun ⟨⟨B,Q⟩,h3,h4⟩=>⟨⟨ar.mpr B,Q⟩,h3,h4⟩⟩
 have b6:kT (un n) (un q.length) d=cF (decide (∃ z∈q,¬Disjoint z.1 z.2)):=tG q;change solve (E++false::x)=output;unfold solve;simp only[b5.1,b5.2,b3.1,b3.2,b1.1,b1.2,b4.1,b4.2,a7.1,a7.2,b2.1,b2.2,b6,dE];have aw:vu (un n)=un (n / 2):=(by simp[vu,J]);rw[aw];by_cases a8:∃ z∈q,¬Disjoint z.1 z.2
 ·
  simp only[a8,iy,↓reduceIte]
  have a5:∀ s j,L s j=0:=fun s j=>by
   rw[a0 s j];exact n8 q u a8 s j
  have af:output=replicate ((n / 2+1)*(m+1)*k) false:=by
   simp only[output];have bc:K k (0 % 2^k)=replicate k false:=(by apply jD;{simp[K]};{intro i hi _;simp[K]})
   have B:∀ s∈List.range (n / 2+1),(List.range (m+1)).flatMap (fun j=>K k (L s j % 2^k))=replicate ((m+1)*k) false:=fun s _=>by
    have Q:(List.range (m+1)).flatMap (fun j=>K k (L s j % 2^k))=(List.range (m+1)).flatMap (fun _=>replicate k false):=dG fun j _=>by rw[a5 s j,bc]
    rw[Q,ll]
   rw[dG B,ll,mR]
  rw[af,eR,eR,gS,gS,s5]
 ·
  simp only[a8,iT,eX,↓reduceIte];have ax:∀ z∈q,Disjoint z.1 z.2:=(by intro z hz;by_contra ba;exact a8 ⟨z,hz,ba⟩);let M:=(gX n).toFinset.filter (fun e=>∀ z∈q,¬(aF e⊆z.1)/\¬(aF e⊆z.2));have b8:∀ e∈M,e.1<e.2:=fun e he=>(gR e).mp (dO.mp (aL.mp he).1);have az:dA M (jP (un n) (un q.length) d):=r0 q
  have am:∀ a b:Fin n,fa (eV (un m)) (jI (un n) (un a.val) (un b.val)) (hN (un n) (un m) c)=un (cZ u (a,b)):=fun a b=>by
   simpa[cZ,rU,th,fy,aF,m,c] using qm u a b
  have aa:mV (un n) (un m) c=un (cO u):=(by simpa[cO,m,c] using u6 u);have an:un m++un m++[true]=un (2*m+1):=(by rw[g6,eR];congr 1;omega);have ay:dS (un (n / 2)) (un m++un m++[true])++un m++[true]=un ((n / 2)*(2*m+1)+m+1):=(by rw[an,gS,g6,eR]);have ae:∀ r<k,∀ j≤r,(aJ (bB M) j).length*(((bB M).length+1)+n*n+2)+1<=E.length:=(by intro r hr j hj;rw[J];have av:n+2<=x.length+2:=(by simp only[x,v,o,dL,sy,lv];omega);exact vE n k x.length av hk M j (by omega));let T:=(n / 2)*(2*m+1)+m+1;rw[ay,aa];generalize aj:Z E (Z (un k) (Z (un n) (Z (un m) (Z (un T) (Z (jP (un n) (un q.length) d) (Z (hN (un n) (un m) c) (Z (un (cO u)) (Z (gO (un n) (jP (un n) (un q.length) d)) (eD (un n) (jP (un n) (un q.length) d))))))))))=ctx;have a6:rQ ctx=un k:=(by rw[<- aj];simp only[rQ,left,right,G]);have ai:t8 ctx=un m:=(by rw[<- aj];simp only[t8,left,right,G])
  have a9:∀ s j,(i0 (Z (un j) (Z (un s) ctx))).length=k:=fun s j=>by
   simp only[i0,left,right,G,mY,a6];rw[pV,J]
  have al:∀ s,ky (Z (un s) ctx)=(List.range (m+1)).flatMap (fun j=>i0 (Z (un j) (Z (un s) ctx))):=fun s=>by
   simp only[ky,left,right,G,a6,ai,eR];rw[bA i0 (un k) (un (m+1)) _ (fun j _=>by rw[J];exact (a9 s j).le),J]
  have ap:∀ s,(ky (Z (un s) ctx)).length=(m+1)*k:=fun s=>by
   rw[al s,gx];have hm:(List.range (m+1)).map (fun j=>(i0 (Z (un j) (Z (un s) ctx))).length)=(List.range (m+1)).map (fun _=>k):=dF fun j _=>a9 s j;rw[hm];simp
  rw[eR,eR,gS];rw[bA ky (un ((m+1)*k)) (un (n / 2+1)) _ (fun s _=>by rw[J];exact (ap s).le),J];refine dG fun s hs=>?_;have bf:s<n / 2+1:=aY.mp hs;rw[al s];refine dG fun j hj=>?_;have bj:j< m+1:=aY.mp hj;simp only[i0,left,right,G,ai];rw[an,gS,g6];have ah:s*(2*m+1)+j<T:=(by have B:s*(2*m+1)<=(n / 2)*(2*m+1):=nK _ (by omega);omega);have aq:=wJ (by omega) M b8 az u am E ae T (s*(2*m+1)+j) ah ctx aj.symm;have ak:=q5 q u ax b7 s j (by omega);dsimp only at ak;rw[<- a0 s j] at ak;rw[<- ak] at aq;exact ur k (L s j) (mY ctx (un (s*(2*m+1)+j))) (by rw[mY,a6,pV,J]) aq
end xV
end PEqualNP.Outside.L_meta_33619
theorem PEqualNP.Outside.L_meta_33619 :
    let header := fun j : Nat => List.replicate j true ++ [false]
    let bits := fun (w z : Nat) => (List.range w).map (fun h => z.testBit h)
    let pairs := fun k : Nat => (List.finRange k).flatMap (fun i =>
        ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : Nat), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : Nat), 2 ≤ n →
      ∀ (hard : List (Finset (Fin n) × Finset (Fin n)))
        (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool)),
      let m := soft.length
      let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
      let E := (pairs n).toFinset.filter (fun e =>
        ∀ z ∈ hard, ¬(ends e ⊆ z.1) ∧ ¬(ends e ⊆ z.2))
      let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
        Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ S, ends e ⊆ t.1.1 ∨ ends e ⊆ t.1.2
      (∀ S ⊆ E, 2 ≤ S.card →
        (∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f)) →
        (soft.filter (fun t => t.2 && decide (lists S t))).length =
          (soft.filter (fun t => !t.2 && decide (lists S t))).length) →
      let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
      let obs := fun (f : Fn) (R T : Finset (Fin n)) =>
        f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ T))
      let valid := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
        PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
        ∀ z ∈ hard, obs f z.1 z.2 = false
      let code := fun f : Fn => (pairs n).map (fun e => obs f (ends e) ∅)
      let size := fun f : Fn => ((code f).filter id).length
      let score := fun f : Fn => (soft.filter (fun t => decide (obs f t.1.1 t.1.2 = t.2))).length
      let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
      let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
        header m ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
      ∀ k : Nat, 1 ≤ k →
        let x := header k ++ input
        let count := fun s j : Nat => Nat.card {f : Fn // valid f ∧ size f = s ∧ score f = j}
        let output := (List.range (n/2+1)).flatMap (fun s =>
          (List.range (m+1)).flatMap (fun j => bits k (count s j % 2^k)))
        Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
          (some (output.map M.outputAlphabet.invFun)) ((x.length+2)^(c*(k+1))))
    := by
 obtain ⟨M,c,hfin,hrun⟩:=PEqualNP.Outside.L_meta_33619.wZ.wK
  PEqualNP.Outside.L_meta_33619.xV.solve PEqualNP.Outside.L_meta_33619.xV.yL
 refine ⟨M,c,hfin,fun n hn hard soft hbal k hk=>?_⟩
 let header:=fun j:Nat=>List.replicate j true++[false]
 let bank:=fun B:Finset (Fin n)=>(List.finRange n).map (fun i=>decide (i∈B))
 let payload:=header n++header hard.length++hard.flatMap (fun z=>bank z.1++bank z.2)++
  header soft.length++soft.flatMap (fun t=>bank t.1.1++bank t.1.2++[t.2])
 have hspec:=PEqualNP.Outside.L_meta_33619.xV.xj n hn hard soft hbal k hk
 have hr:=hrun k payload
 dsimp only at hspec hr ⊢
 rw [hspec] at hr
 exact hr
