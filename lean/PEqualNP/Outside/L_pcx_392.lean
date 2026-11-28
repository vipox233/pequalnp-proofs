import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
namespace PEqualNP.Outside.L_pcx_392_aux
open Finset (Icc add_sum_erase card_bij card_empty card_eq_sum_card_fiberwise card_filter card_filter_add_card_filter_not card_filter_le card_image_of_injective card_le_card card_lt_card card_product card_union_of_disjoint filter_image filter_subset induction_on mem_biUnion mem_erase mem_image_of_mem mem_insert_of_mem mem_insert_self mem_powersetCard mem_product mem_range mul_sum notMem_empty prod_biUnion prod_const prod_eq_one prod_image prod_insert prod_ite prod_pair prod_singleton prod_subset single_le_sum subset_univ sum_bij sum_const sum_empty sum_filter sum_insert sum_mul sum_singleton sum_sub_distrib sum_subset union_empty univ)
open Or (inl inr)
open Nat (add_mod cast_succ choose choose_symm div_add_mod div_eq_of_lt lt_two_pow_self mod_mod mod_self mul_div_cancel pow_le_pow_right succ_mul succ_ne_zero succ_pos testBit_mod_two_pow two_pow_pos zero_mod zero_testBit)
open Fin (castSucc elim0 last lastCases mk_one sum_univ_castSucc val_one val_two val_zero zero_eta)
open Polynomial (C X coeff_X coeff_X_zero coeff_eq_zero_of_natDegree_lt coeff_one_zero lcoeff natDegree_add_le natDegree_pow_le natDegree_sub_le)
open Function (Injective Surjective comp_def update update_of_ne)
open List (all_eq_true getD_cons_zero getD_eq_getElem getElem_mem getElem_ofFn get_eq_getElem get_mem map_ofFn mem_cons mem_cons_self mem_ofFn not_mem_nil ofFn pairwise_iff_get sum_ofFn)
open Equiv (Perm coe_fn_mk coe_fn_symm_mk)
open Relation (EqvGen ReflTransGen)
open Set (InjOn)
open Bool (true_xor)
open Fintype (card_bool card_subtype equivFin prod_equiv sum_bool sum_equiv sum_prod_type)
open Int (castRingHom cast_id)
open Classical (choose_spec decPred)
open Subtype (coe_eta)
open ZMod (val_lt val_natCast)
abbrev Y0:=Bool
abbrev V7:=Finset
abbrev V9:=Option
abbrev BV (n:ℕ):=Y0×Fin n
abbrev P0 (n:ℕ):=BV n->V9 Y0
abbrev Z2 (B:ℕ):=ZMod (2^B)
abbrev F0 (N:ℕ):=Fin N->Y0
abbrev R0 {α:Sort*}{β:Type*}(f:α->β):=Set.range f
abbrev W0 (α:Type*)[Fintype α]:=Fintype.card α
lemma L0 {p:Prop}[Decidable p]:(decide p=true)=p:=decide_eq_true_eq
lemma Y2 {b:Type*}[Fintype b](a:b):a∈(Finset.univ:Finset b):=Finset.mem_univ a
lemma Y3 {b:Type*}[Preorder b]{a:b}:a<=a:=le_rfl
lemma L3 {ι M:Type*}[AddCommMonoid M]{s t:Finset ι}{f g:ι->M}(b:s=t)(a:∀ x∈t,f x=g x):∑ x∈s,f x=∑ x∈t,g x:=Finset.sum_congr b a
lemma L4 {b:Type*}{s:Finset b}{p:b->Prop}[DecidablePred p]{a:b}:a∈s.filter p↔a∈s/\p a:=Finset.mem_filter
lemma L5 {a b:Bool}:(a=true↔b=true)->a=b:=Bool.eq_iff_iff.mpr
lemma L6 {n:ℕ}{i j:Fin n}(h:i.val=j.val):i=j:=Fin.ext h
lemma L7 {b:Sort*}{c:Prop}{h:Decidable c}(a:c){t:c->b}{e:¬c->b}:dite c t e=t a:=dif_pos a
lemma L8 {a b:ℕ}(h:a<b):a %b=a:=Nat.mod_eq_of_lt h
lemma L9 {ι M:Type*}[AddCommMonoid M]{s:Finset ι}{f:ι->M}(h:∀ x∈s,f x=0):∑ x∈s,f x=0:=Finset.sum_eq_zero h
lemma Q0 (a:Prop):(True/\a)=a:=true_and a
lemma Q1 {b:Type*}{a:b}{s:Set b}:a∈s->{a}⊆s:=Set.singleton_subset_iff.mpr
lemma Q2 {b:Sort*}{c:Prop}{h:Decidable c}(a:c){t e:b}:ite c t e=t:=if_pos a
lemma Q3 {b:Sort*}{c:Prop}{h:Decidable c}(a:¬c){t e:b}:ite c t e=e:=if_neg a
lemma Q4 {ι M:Type*}[AddCommMonoid M]{s:Finset ι}{f:ι->M}(a:ι)(c:∀ b∈s,b≠a->f b=0)(d:a∉s->f a=0):∑ x∈s,f x=f a:=Finset.sum_eq_single a c d
lemma Q6 {c:Sort*}{d:Sort*}{b a:c}(f:c->d)(h:b=a):f b=f a:=congrArg f h
lemma Q8 {b:Sort*}{c:Prop}{h:Decidable c}(a:¬c){t:c->b}{e:¬c->b}:dite c t e=e a:=dif_neg a
lemma Q9 (n:ℕ):Fintype.card (Fin n)=n:=Fintype.card_fin n
lemma M0 {d:Type*}[DecidableEq d](b:Finset d){c:Finset d}{a:d}(h:a∈c):a∈b∪c:=Finset.mem_union_right b h
lemma M1 (x:ℕ){y:ℕ}(h:0<y):x %y<y:=Nat.mod_lt x h
lemma M2 (a b:ℕ):(a+b) %b=a %b:=Nat.add_mod_right a b
lemma M3 {ι M:Type*}[CommMonoid M]{s:Finset ι}{f g:ι->M}:∏ x∈s,f x*g x=(∏ x∈s,f x)*∏ x∈s,g x:=Finset.prod_mul_distrib
lemma M4 {ι M:Type*}[CommMonoid M]{s t:Finset ι}{f g:ι->M}(b:s=t)(a:∀ x∈t,f x=g x):∏ x∈s,f x=∏ x∈t,g x:=Finset.prod_congr b a
lemma M5 {a b:Sort*}(e:a ≃ b)(x:a):e.symm (e x)=x:=e.symm_apply_apply x
lemma M6 {d:Type*}[DecidableEq d]{b:Finset d}(c:Finset d){a:d}(h:a∈b):a∈b∪c:=Finset.mem_union_left c h
lemma M7 {p:Prop}[Decidable p]:(decide p=false)↔¬p:=decide_eq_false_iff_not
lemma M8 {a:Type*}{s t:Set a}:s⊆s∪t:=Set.subset_union_left
lemma M9 {a:Type*}{s t:Set a}:t⊆s∪t:=Set.subset_union_right
lemma K2 {n:ℕ}(h:n≠0):0<n:=Nat.pos_of_ne_zero h
lemma K3 {b:Type*}[DecidableEq b]{l:List b}{a:b}:a∈l.toFinset↔a∈l:=List.mem_toFinset
lemma K4 {n:ℕ}{a b:Fin n}:a=b↔a.val=b.val:=Fin.ext_iff
lemma K6 {a:Type*}{s t:List a}:(s ++ t).length=s.length+t.length:=List.length_append
lemma K8 {a b:Bool}:((a && b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma J0 {e f:Type*}{a b:e}{c d:f}:((a,c)=(b,d))=(a=b/\c=d):=Prod.mk.injEq a c b d
lemma J3 (b a:Type*)[Fintype b][Fintype a]:Fintype.card (b×a)=Fintype.card b*Fintype.card a:=Fintype.card_prod b a
lemma J4 {c:Type*}[Preorder c][LocallyFiniteOrder c]{a b x:c}:x∈Finset.Icc a b↔a<=x/\x<=b:=Finset.mem_Icc
lemma J5:(false=true)=False:=Bool.false_eq_true
lemma J7 {b:Type*}[Fintype b][DecidableEq b]{s:Finset b}{a:b}:a∈sᶜ↔a∉s:=Finset.mem_compl
lemma J9 {c:Sort*}{p:c->Prop}{b a:Subtype p}:b=a↔b.val=a.val:=Subtype.ext_iff
lemma U0 (a:Bool):(a ^^ false)=a:=Bool.xor_false a
lemma U1 {n m:ℕ}(h:n<m+1):n<=m:=Nat.le_of_lt_succ h
lemma U2 (n:ℕ):n<n+1:=Nat.lt_succ_self n
lemma U3 {a:Type*}{s:Finset a}:s.card=0↔s=∅:=Finset.card_eq_zero
lemma U4 {M:Type*}[Monoid M](a:M)(n:ℕ):a^(n+1)=a^n*a:=pow_succ a n
lemma U5 {c:Type*}{a b:c}:a∈({b}:Finset c)↔a=b:=Finset.mem_singleton
lemma U6 {a b:Type*}[LE a][LE b](e:a ≃o b)(x:a):e.symm (e x)=x:=e.symm_apply_apply x
lemma U7 {a:Type*}{n:ℕ}{f:Fin n->a}:(List.ofFn f).length=n:=List.length_ofFn
lemma U8 (n:ℕ):Nat.choose n 0=1:=Nat.choose_zero_right n
lemma U9 (n:ℕ):Nat.choose n 1=n:=Nat.choose_one_right n
lemma W1 (n:ℕ):(Finset.range n).card=n:=Finset.card_range n
lemma W2 {a:Type*}[Fintype a]:(Finset.univ:Finset a).card=Fintype.card a:=Finset.card_univ
lemma W4 {n m:ℕ}(k:ℕ)(h:n<=m):n*k<=m*k:=Nat.mul_le_mul_right k h
lemma W5 (k:ℕ){n m:ℕ}(h:n<=m):k*n<=k*m:=Nat.mul_le_mul_left k h
lemma W6 {a:Type*}(s t u:Set a):(s∪t)∪u=s∪(t∪u):=Set.union_assoc s t u
lemma W7 {a b:ℕ}(h:a<b):b≠a:=Nat.ne_of_gt h
lemma W8 {a:Type*}{s:Finset a}{p:a->Prop}[DecidablePred p]:s.filter p=∅↔∀ x∈s,¬p x:=Finset.filter_eq_empty_iff
lemma W9 {b:Type*}[DecidableEq b]{a:b}{s:Finset b}(h:a∉s):(insert a s).card=s.card+1:=Finset.card_insert_of_notMem h
lemma V1 {a:Type*}[Fintype a][DecidableEq a](s:Finset a):s.card+sᶜ.card=Fintype.card a:=Finset.card_add_card_compl s
lemma V2 {n i:ℕ}(h:n<2^i):n.testBit i=false:=Nat.testBit_lt_two_pow h
lemma V3 {a b:ℕ}(h:a<=b):a+(b-a)=b:=Nat.add_sub_of_le h
lemma V4 {a b:Bool}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma V5 (n:ℕ):0<=n:=Nat.zero_le n
lemma V6 {ι M:Type*}[AddCommMonoid M][DecidableEq ι]{a b:ι}{f:ι->M}(h:a≠b):∑ x∈({a,b}:Finset ι),f x=f a+f b:=Finset.sum_pair h
lemma Z3 (a b c:ℕ):a*b*c=a*(b*c):=Nat.mul_assoc a b c
lemma Z4 {ι M:Type*}[AddCommMonoid M]{s:Finset ι}{f g:ι->M}:∑ x∈s,(f x+g x)=(∑ x∈s,f x)+∑ x∈s,g x:=Finset.sum_add_distrib
lemma Z6 (a b c:Bool):((a ^^ b) ^^ c)=(a ^^ (b ^^ c)):=Bool.xor_assoc a b c
lemma Z7 {b:Type*}{a:b}{as:List b}:(a :: as).length=as.length+1:=List.length_cons
lemma Z8 {a:Type*}:([]:List a).length=0:=List.length_nil
lemma Z9 {c:Sort*}{p:c->Prop}{b a:Subtype p}(h:b.val=a.val):b=a:=Subtype.ext h
lemma X3 {c:Type*}[DecidableEq c]{a b:c}{s:Finset c}:a∈insert b s↔a=b\/a∈s:=Finset.mem_insert
lemma X4 {d:Type*}[DecidableEq d]{b c:Finset d}{a:d}:a∈b∪c↔a∈b\/a∈c:=Finset.mem_union
lemma X5 {d c:Type*}[DecidableEq c]{f:d->c}{s:Finset d}{b:c}:b∈s.image f↔∃ a∈s,f a=b:=Finset.mem_image
lemma X6 {M:Type*}[Monoid M](a:M)(m n:ℕ):a^(m+n)=a^m*a^n:=pow_add a m n
lemma X7 {ι M:Type*}[AddCommMonoid M][DecidableEq ι]{a b:Finset ι}{f:ι->M}(h:Disjoint a b):∑ x∈a∪b,f x=(∑ x∈a,f x)+∑ x∈b,f x:=Finset.sum_union h
lemma X8 {b:Type*}{s t:Finset b}:Disjoint s t↔∀ ⦃a⦄,a∈s->a∉t:=Finset.disjoint_left
lemma X9 {ι₁ ι₂ M:Type*}[AddCommMonoid M]{s:Finset ι₁}{t:Finset ι₂}{f:ι₁->ι₂->M}:∑ x∈s,∑ y∈t,f x y=∑ y∈t,∑ x∈s,f x y:=Finset.sum_comm
namespace S399
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
structure a8 (D1 D2:ℕ) (R:Type*) where
 coeff:Fin D1->Fin D2->R
namespace a8
variable {D1 D2:ℕ} {R:Type*}
lemma ext {f g:a8 D1 D2 R}(h:∀ i j,f.coeff i j=g.coeff i j):f=g:=by
 cases f;cases g;congr;funext i j;exact h i j
section RingInst
variable [CommRing R]
def mc:a8 D1 D2 R:=⟨fun _ _=>0⟩
def ou:a8 D1 D2 R:=⟨fun i j=>if i.val=0/\j.val=0 then 1 else 0⟩
def mo (f g:a8 D1 D2 R):a8 D1 D2 R:=⟨fun i j=>f.coeff i j+g.coeff i j⟩
def rh (f:a8 D1 D2 R):a8 D1 D2 R:=⟨fun i j=>-f.coeff i j⟩
def ri (f g:a8 D1 D2 R):a8 D1 D2 R:=⟨fun i j=>f.coeff i j-g.coeff i j⟩
def aq (f g:a8 D1 D2 R):a8 D1 D2 R:=⟨fun i j=>∑ i1:Fin D1,∑ i2:Fin D1,∑ j1:Fin D2,∑ j2:Fin D2,if i1.val+i2.val=i.val/\j1.val+j2.val=j.val then f.coeff i1 j1*g.coeff i2 j2 else 0⟩
lemma pw (f g h:a8 D1 D2 R):aq (aq f g) h=aq f (aq g h):=by
 apply ext;intro i j;dsimp only[aq]
 have hL:(∑ m:Fin D1,∑ b:Fin D1,∑ e:Fin D2,∑ a:Fin D2,if m.val+b.val=i.val/\e.val+a.val=j.val then (∑ c:Fin D1,∑ i2:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,if c.val+i2.val=m.val/\d.val+j2.val=e.val then f.coeff c d*g.coeff i2 j2 else 0)*h.coeff b a
   else 0)=
  ∑ c:Fin D1,∑ i2:Fin D1,∑ b:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,∑ a:Fin D2,if c.val+i2.val+b.val=i.val/\d.val+j2.val+a.val=j.val then f.coeff c d*g.coeff i2 j2*h.coeff b a
    else 0:=by
  have o:∀(m b:Fin D1) (e a:Fin D2),(if m.val+b.val=i.val/\e.val+a.val=j.val then (∑ c:Fin D1,∑ i2:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,if c.val+i2.val=m.val/\d.val+j2.val=e.val then f.coeff c d*g.coeff i2 j2 else 0)*h.coeff b a
   else 0)=
   ∑ c:Fin D1,∑ i2:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,if(m.val+b.val=i.val/\e.val+a.val=j.val)/\(c.val+i2.val=m.val/\d.val+j2.val=e.val) then f.coeff c d*g.coeff i2 j2*h.coeff b a
    else 0:=by
   intro m b e a;by_cases r:m.val+b.val=i.val/\e.val+a.val=j.val
   . simp only[r,Q0,↓reduceIte,sum_mul];refine L3 rfl fun c _=>L3 rfl fun i2 _=>L3 rfl fun d _=>L3 rfl fun j2 _=>?_;split_ifs<;>ring
   . simp[r]
  simp_rw[o]
  trans (∑ c:Fin D1,∑ i2:Fin D1,∑ b:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,∑ a:Fin D2,∑ m:Fin D1,∑ e:Fin D2,if(m.val+b.val=i.val/\e.val+a.val=j.val)/\(c.val+i2.val=m.val/\d.val+j2.val=e.val) then f.coeff c d*g.coeff i2 j2*h.coeff b a else 0)
  . let z:(Fin D1×Fin D1×Fin D2×Fin D2×Fin D1×Fin D1×Fin D2×Fin D2) ≃
     (Fin D1×Fin D1×Fin D1×Fin D2×Fin D2×Fin D2×Fin D1×Fin D2):=
     {toFun:=fun⟨m,b,e,a,c,i2,d,j2⟩=>(c,i2,b,d,j2,a,m,e),invFun:=fun⟨c,i2,b,d,j2,a,m,e⟩=>(m,b,e,a,c,i2,d,j2),left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
    have s:=sum_equiv z
     (fun x=>if(x.1.val+x.2.1.val=i.val/\x.2.2.1.val+x.2.2.2.1.val=j.val)/\(x.2.2.2.2.1.val+x.2.2.2.2.2.1.val=x.1.val/\x.2.2.2.2.2.2.1.val+x.2.2.2.2.2.2.2.val=x.2.2.1.val) then f.coeff x.2.2.2.2.1 x.2.2.2.2.2.2.1*g.coeff x.2.2.2.2.2.1 x.2.2.2.2.2.2.2*h.coeff x.2.1 x.2.2.2.1
     else 0)
     (fun y=>if(y.2.2.2.2.2.2.1.val+y.2.2.1.val=i.val/\y.2.2.2.2.2.2.2.val+y.2.2.2.2.2.1.val=j.val)/\(y.1.val+y.2.1.val=y.2.2.2.2.2.2.1.val/\y.2.2.2.1.val+y.2.2.2.2.1.val=y.2.2.2.2.2.2.2.val) then f.coeff y.1 y.2.2.2.1*g.coeff y.2.1 y.2.2.2.2.1*h.coeff y.2.2.1 y.2.2.2.2.2.1
     else 0)
     (fun _=>rfl)
    simpa only[sum_prod_type] using s
  . refine L3 rfl fun c _=>L3 rfl fun i2 _=>L3 rfl fun b _=>L3 rfl fun d _=>L3 rfl fun j2 _=>L3 rfl fun a _=>?_;by_cases n:c.val+i2.val+b.val=i.val/\d.val+j2.val+a.val=j.val
    . have t:c.val+i2.val<D1:=(by have:=i.isLt;omega);have u:d.val+j2.val<D2:=(by have:=j.isLt;omega);rw[Q4 ⟨c.val+i2.val,t⟩]
      . rw[Q4 ⟨d.val+j2.val,u⟩]
        . simp[n]
        . intro e _ p;have:d.val+j2.val≠e.val:=fun h=>p (L6 h.symm);simp[this]
        . intro q;exact absurd (Y2 _) q
      . intro m _ p;refine L9 fun e _=>?_;have:c.val+i2.val≠m.val:=fun h=>p (L6 h.symm);simp[this]
      . intro q;exact absurd (Y2 _) q
    . rw[Q3 n];refine L9 fun m _=>L9 fun e _=>?_
      split_ifs with r
      . exfalso;apply n;omega
      . rfl
 have hR:(∑ c:Fin D1,∑ l:Fin D1,∑ d:Fin D2,∑ k:Fin D2,if c.val+l.val=i.val/\d.val+k.val=j.val then f.coeff c d*(∑ i2:Fin D1,∑ b:Fin D1,∑ j2:Fin D2,∑ a:Fin D2,if i2.val+b.val=l.val/\j2.val+a.val=k.val then g.coeff i2 j2*h.coeff b a else 0)
   else 0)=
  ∑ c:Fin D1,∑ i2:Fin D1,∑ b:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,∑ a:Fin D2,if c.val+i2.val+b.val=i.val/\d.val+j2.val+a.val=j.val then f.coeff c d*g.coeff i2 j2*h.coeff b a
    else 0:=by
  have o:∀(c l:Fin D1) (d k:Fin D2),(if c.val+l.val=i.val/\d.val+k.val=j.val then f.coeff c d*(∑ i2:Fin D1,∑ b:Fin D1,∑ j2:Fin D2,∑ a:Fin D2,if i2.val+b.val=l.val/\j2.val+a.val=k.val then g.coeff i2 j2*h.coeff b a else 0)
   else 0)=
   ∑ i2:Fin D1,∑ b:Fin D1,∑ j2:Fin D2,∑ a:Fin D2,if(c.val+l.val=i.val/\d.val+k.val=j.val)/\(i2.val+b.val=l.val/\j2.val+a.val=k.val) then f.coeff c d*g.coeff i2 j2*h.coeff b a
    else 0:=by
   intro c l d k;by_cases r:c.val+l.val=i.val/\d.val+k.val=j.val
   . simp only[r,Q0,↓reduceIte,mul_sum];refine L3 rfl fun i2 _=>L3 rfl fun b _=>L3 rfl fun j2 _=>L3 rfl fun a _=>?_;split_ifs<;>ring
   . simp[r]
  simp_rw[o]
  trans (∑ c:Fin D1,∑ i2:Fin D1,∑ b:Fin D1,∑ d:Fin D2,∑ j2:Fin D2,∑ a:Fin D2,∑ l:Fin D1,∑ k:Fin D2,if(c.val+l.val=i.val/\d.val+k.val=j.val)/\(i2.val+b.val=l.val/\j2.val+a.val=k.val) then f.coeff c d*g.coeff i2 j2*h.coeff b a else 0)
  . let e2:(Fin D1×Fin D1×Fin D2×Fin D2×Fin D1×Fin D1×Fin D2×Fin D2) ≃
     (Fin D1×Fin D1×Fin D1×Fin D2×Fin D2×Fin D2×Fin D1×Fin D2):=
     {toFun:=fun⟨c,l,d,k,i2,b,j2,a⟩=>(c,i2,b,d,j2,a,l,k),invFun:=fun⟨c,i2,b,d,j2,a,l,k⟩=>(c,l,d,k,i2,b,j2,a),left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
    have s:=sum_equiv e2
     (fun x=>if(x.1.val+x.2.1.val=i.val/\x.2.2.1.val+x.2.2.2.1.val=j.val)/\(x.2.2.2.2.1.val+x.2.2.2.2.2.1.val=x.2.1.val/\x.2.2.2.2.2.2.1.val+x.2.2.2.2.2.2.2.val=x.2.2.2.1.val) then f.coeff x.1 x.2.2.1*g.coeff x.2.2.2.2.1 x.2.2.2.2.2.2.1*h.coeff x.2.2.2.2.2.1 x.2.2.2.2.2.2.2
     else 0)
     (fun y=>if(y.1.val+y.2.2.2.2.2.2.1.val=i.val/\y.2.2.2.1.val+y.2.2.2.2.2.2.2.val=j.val)/\(y.2.1.val+y.2.2.1.val=y.2.2.2.2.2.2.1.val/\y.2.2.2.2.1.val+y.2.2.2.2.2.1.val=y.2.2.2.2.2.2.2.val) then f.coeff y.1 y.2.2.2.1*g.coeff y.2.1 y.2.2.2.2.1*h.coeff y.2.2.1 y.2.2.2.2.2.1
     else 0)
     (fun _=>rfl)
    simpa only[sum_prod_type] using s
  . refine L3 rfl fun c _=>L3 rfl fun i2 _=>L3 rfl fun b _=>L3 rfl fun d _=>L3 rfl fun j2 _=>L3 rfl fun a _=>?_;by_cases n:c.val+i2.val+b.val=i.val/\d.val+j2.val+a.val=j.val
    . have v:i2.val+b.val<D1:=(by have:=i.isLt;omega);have w:j2.val+a.val<D2:=(by have:=j.isLt;omega);rw[Q4 ⟨i2.val+b.val,v⟩]
      . rw[Q4 ⟨j2.val+a.val,w⟩]
        . simp[n,<-Nat.add_assoc]
        . intro k _ p;have:j2.val+a.val≠k.val:=fun h=>p (L6 h.symm);simp[this]
        . intro q;exact absurd (Y2 _) q
      . intro l _ p;refine L9 fun k _=>?_;have:i2.val+b.val≠l.val:=fun h=>p (L6 h.symm);simp[this]
      . intro q;exact absurd (Y2 _) q
    . rw[Q3 n];refine L9 fun l _=>L9 fun k _=>?_
      split_ifs with r
      . exfalso;apply n;omega
      . rfl
 exact hL.trans hR.symm
lemma ga (f g:a8 D1 D2 R):aq f g=aq g f:=by
 apply ext;intro i j;dsimp only[aq];rw[X9];refine L3 rfl fun i2 _=>L3 rfl fun i1 _=>?_;rw[X9];refine L3 rfl fun j2 _=>L3 rfl fun j1 _=>?_
 have b:(i1.val+i2.val=i.val/\j1.val+j2.val=j.val)↔(i2.val+i1.val=i.val/\j2.val+j1.val=j.val):=(by rw[Nat.add_comm i1.val,Nat.add_comm j1.val]);by_cases a:i1.val+i2.val=i.val/\j1.val+j2.val=j.val
 . rw[Q2 a,Q2 (b.mp a),mul_comm]
 . rw[Q3 a,Q3 (mt b.mpr a)]
lemma ov (f:a8 D1 D2 R):aq ou f=f:=by
 apply ext;intro i j;dsimp only[aq,ou];have d:0<D1:=Nat.lt_of_le_of_lt (V5 _) i.isLt;have c:0<D2:=Nat.lt_of_le_of_lt (V5 _) j.isLt;rw[Q4 ⟨0,d⟩]
 . rw[Q4 i]
   . rw[Q4 ⟨0,c⟩]
     . rw[Q4 j]
       . simp
       . intro j2 _ a;have:j2.val≠j.val:=fun h=>a (L6 h);simp[this]
       . intro b;exact absurd (Y2 _) b
     . intro j1 _ a;refine L9 fun j2 _=>?_;have:j1.val≠0:=fun h=>a (L6 h);simp[this]
     . intro b;exact absurd (Y2 _) b
   . intro i2 _ a;refine L9 fun j1 _=>L9 fun j2 _=>?_;have:i2.val≠i.val:=fun h=>a (L6 h);simp[this]
   . intro b;exact absurd (Y2 _) b
 . intro i1 _ a;refine L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_;have:i1.val≠0:=fun h=>a (L6 h);simp[this]
 . intro b;exact absurd (Y2 _) b
lemma kl (f g h:a8 D1 D2 R):aq f (mo g h)=mo (aq f g) (aq f h):=by apply ext;intro i j;dsimp only[aq,mo];simp_rw[<-Z4];refine L3 rfl fun i1 _=>L3 rfl fun i2 _=>L3 rfl fun j1 _=>L3 rfl fun j2 _=>?_;split_ifs<;>ring
instance instZero:Zero (a8 D1 D2 R):=⟨mc⟩
instance instOne:One (a8 D1 D2 R):=⟨ou⟩
instance instAdd:Add (a8 D1 D2 R):=⟨mo⟩
instance instNeg:Neg (a8 D1 D2 R):=⟨rh⟩
instance instSub:Sub (a8 D1 D2 R):=⟨ri⟩
instance instMul:Mul (a8 D1 D2 R):=⟨aq⟩
instance instCommRing:CommRing (a8 D1 D2 R):=
 {zero:=mc,one:=ou,add:=mo,neg:=rh,sub:=ri,mul:=aq,nsmul:=fun n f=>⟨fun i j=>n • f.coeff i j⟩,zsmul:=fun z f=>⟨fun i j=>z • f.coeff i j⟩,nsmul_zero:=fun f=>ext fun i j=>zero_nsmul _,nsmul_succ:=fun n f=>ext fun i j=>succ_nsmul _ _,zsmul_zero':=fun f=>ext fun i j=>zero_zsmul _,
  zsmul_succ':=fun n f=>ext fun i j=>by
   change (Int.ofNat (n+1)) • f.coeff i j=(Int.ofNat n) • f.coeff i j+f.coeff i j
   rw[Int.ofNat_eq_natCast,Int.ofNat_eq_natCast,Nat.cast_add,Nat.cast_one,add_zsmul,one_zsmul],
  zsmul_neg':=fun n f=>ext fun i j=>by
   change (Int.negSucc n) • f.coeff i j=-((Int.ofNat (n+1)) • f.coeff i j)
   rw[negSucc_zsmul,Int.ofNat_eq_natCast,natCast_zsmul],
  zero_add:=fun f=>ext fun i j=>zero_add _,add_assoc:=fun f g h=>ext fun i j=>add_assoc _ _ _,
  neg_add_cancel:=fun f=>ext fun i j=>neg_add_cancel _,add_zero:=fun f=>ext fun i j=>add_zero _,
  sub_eq_add_neg:=fun f g=>ext fun i j=>sub_eq_add_neg _ _,add_comm:=fun f g=>ext fun i j=>add_comm _ _,
  mul_assoc:=pw,
  one_mul:=ov,
  mul_one:=fun f=>(ga f ou).trans (ov f),
  zero_mul:=fun f=>ext fun i j=>by change (aq mc f).coeff i j=0;simp[aq,mc],
  mul_zero:=fun f=>ext fun i j=>by change (aq f mc).coeff i j=0;simp[aq,mc],
  left_distrib:=kl,
  right_distrib:=fun f g h=>by
   change aq (mo f g) h=mo (aq f h) (aq g h)
   rw[ga,kl,ga,ga h],
  mul_comm:=ga}
lemma gx (i:Fin D1)(j:Fin D2):(0:a8 D1 D2 R).coeff i j=0:=rfl
lemma coeff_one (i:Fin D1)(j:Fin D2):(1:a8 D1 D2 R).coeff i j=if i.val=0/\j.val=0 then 1 else 0:=rfl
lemma coeff_add (f g:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):(f+g).coeff i j=f.coeff i j+g.coeff i j:=rfl
lemma coeff_sub (f g:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):(f-g).coeff i j=f.coeff i j-g.coeff i j:=rfl
lemma qk (f:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):(-f).coeff i j=-f.coeff i j:=rfl
lemma coeff_mul (f g:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):(f*g).coeff i j=∑ i1:Fin D1,∑ i2:Fin D1,∑ j1:Fin D2,∑ j2:Fin D2,if i1.val+i2.val=i.val/\j1.val+j2.val=j.val then f.coeff i1 j1*g.coeff i2 j2 else 0:=rfl
lemma z8 {b:Type*}(s:V7 b)(f:b->a8 D1 D2 R)(i:Fin D1)(j:Fin D2):(∑ x∈s,f x).coeff i j=∑ x∈s,(f x).coeff i j:=by
 classical
 induction s using induction_on with
 | empty=>simp[gx]
 | @insert a s ha ih=>rw[sum_insert ha,sum_insert ha,coeff_add,ih]
def jo (c:R):a8 D1 D2 R:=⟨fun i j=>if i.val=0/\j.val=0 then c else 0⟩
lemma nd (c:R)(f:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):(jo c*f).coeff i j=c*f.coeff i j:=by
 rw[coeff_mul];have e:0<D1:=Nat.lt_of_le_of_lt (V5 _) i.isLt;have d:0<D2:=Nat.lt_of_le_of_lt (V5 _) j.isLt;rw[Q4 ⟨0,e⟩]
 . rw[Q4 i]
   . rw[Q4 ⟨0,d⟩]
     . rw[Q4 j]
       . simp[jo]
       . intro j2 _ a;have:j2.val≠j.val:=fun h=>a (L6 h);simp[this]
       . intro b;exact absurd (Y2 _) b
     . intro j1 _ a;refine L9 fun j2 _=>?_;have:j1.val≠0:=fun h=>a (L6 h);simp[jo,this]
     . intro b;exact absurd (Y2 _) b
   . intro i2 _ a;refine L9 fun j1 _=>L9 fun j2 _=>?_;have:i2.val≠i.val:=fun h=>a (L6 h);simp[this]
   . intro b;exact absurd (Y2 _) b
 . intro i1 _ a;refine L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_;have:i1.val≠0:=fun h=>a (L6 h);simp[jo,this]
 . intro b;exact absurd (Y2 _) b
lemma gm (m:ℕ)(i:Fin D1)(j:Fin D2):(m:a8 D1 D2 R).coeff i j=if i.val=0/\j.val=0 then (m:R) else 0:=by
 induction m with
 | zero=>simp[gx]
 | succ m ih=>rw[cast_succ,cast_succ,coeff_add,ih,coeff_one];split_ifs<;>simp
lemma om (m:ℤ)(i:Fin D1)(j:Fin D2):(m:a8 D1 D2 R).coeff i j=if i.val=0/\j.val=0 then (m:R) else 0:=by
 cases m with
 | ofNat k=>simpa using gm (D1:=D1) (D2:=D2) (R:=R) k i j
 | negSucc k=>simp only[Int.cast_negSucc,qk,gm];split_ifs<;>ring
lemma l0 (m:ℕ)(f:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):((m:a8 D1 D2 R)*f).coeff i j=(m:R)*f.coeff i j:=by have h:(m:a8 D1 D2 R)=jo (m:R):=ext fun a b=>gm m a b;rw[h,nd]
lemma s4 (m:ℤ)(f:a8 D1 D2 R)(i:Fin D1)(j:Fin D2):((m:a8 D1 D2 R)*f).coeff i j=(m:R)*f.coeff i j:=by have h:(m:a8 D1 D2 R)=jo (m:R):=ext fun a b=>om m a b;rw[h,nd]
def o5 (a b:ℕ):a8 D1 D2 R:=⟨fun i j=>if i.val=a/\j.val=b then 1 else 0⟩
lemma px:(o5 0 0:a8 D1 D2 R)=1:=rfl
lemma cl (a b:ℕ)(h:D1<=a\/D2<=b):(o5 a b:a8 D1 D2 R)=0:=by
 apply ext;intro i j;simp only[o5,gx]
 split_ifs with c
 . exfalso;rcases h with d|h2<;>[exact absurd i.isLt (by omega);exact absurd j.isLt (by omega)]
 . rfl
lemma oi (d e c f:ℕ):(o5 d e:a8 D1 D2 R)*o5 c f=o5 (d+c) (e+f):=by
 apply ext;intro i j;rw[coeff_mul];dsimp only[o5];by_cases g:i.val=d+c/\j.val=e+f
 . rw[Q2 g];have m:d<D1:=(by have:=i.isLt;omega);have n:c<D1:=(by have:=i.isLt;omega);have l:e<D2:=(by have:=j.isLt;omega);have k:f<D2:=(by have:=j.isLt;omega);rw[Q4 ⟨d,m⟩]
   . rw[Q4 ⟨c,n⟩]
     . rw[Q4 ⟨e,l⟩]
       . rw[Q4 ⟨f,k⟩]
         . simp[g]
         . intro j2 _ a;have:j2.val≠f:=fun h=>a (L6 h);simp[this]
         . intro b;exact absurd (Y2 _) b
       . intro j1 _ a;refine L9 fun j2 _=>?_;have:j1.val≠e:=fun h=>a (L6 h);simp[this]
       . intro b;exact absurd (Y2 _) b
     . intro i2 _ a;refine L9 fun j1 _=>L9 fun j2 _=>?_;have:i2.val≠c:=fun h=>a (L6 h);simp[this]
     . intro b;exact absurd (Y2 _) b
   . intro i1 _ a;refine L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_;have:i1.val≠d:=fun h=>a (L6 h);simp[this]
   . intro b;exact absurd (Y2 _) b
 . rw[Q3 g];refine L9 fun i1 _=>L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_
   split_ifs with q p o
   . exfalso;apply g;omega
   . simp
   . simp
   . simp
   . rfl
lemma cr (a b k:ℕ):(o5 a b:a8 D1 D2 R)^k=o5 (k*a) (k*b):=by
 induction k with
 | zero=>simp[px]
 | succ k ih=>rw[U4,ih,oi];congr 1<;>ring
def X1:a8 D1 D2 R:=o5 1 0
def X2:a8 D1 D2 R:=o5 0 1
lemma t5 (a b:ℕ):(X1:a8 D1 D2 R)^a*X2^b=o5 a b:=by simp[X1,X2,cr,oi]
def nf {S:Type*}[CommRing S](a:R →+* S):a8 D1 D2 R →+* a8 D1 D2 S where
 toFun f:=⟨fun i j=>a (f.coeff i j)⟩
 map_one':=ext fun i j=>by simp only[coeff_one];split_ifs<;>simp
 map_mul' f g:=ext fun i j=>by simp only[coeff_mul,map_sum];refine L3 rfl fun i1 _=>L3 rfl fun i2 _=>L3 rfl fun j1 _=>L3 rfl fun j2 _=>?_;split_ifs<;>simp
 map_zero':=ext fun i j=>by simp[gx]
 map_add' f g:=ext fun i j=>by simp[coeff_add]
lemma lc {S:Type*}[CommRing S](c:R →+* S)(a b:ℕ):nf (D1:=D1) (D2:=D2) c (o5 a b)=o5 a b:=by apply ext;intro i j;simp only[nf,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,o5];split_ifs<;>simp
lemma dp (f:a8 D1 D2 R)
 (b:∀ i j,i.val+j.val=0->f.coeff i j=0):
 ∀ k (i:Fin D1) (j:Fin D2),i.val+j.val<k->(f^k).coeff i j=0:=by
 intro k
 induction k with
 | zero=>intro i j h;omega
 | succ k ih=>
  intro i j c;rw[U4,coeff_mul];refine L9 fun i1 _=>L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_
  split_ifs with h
  . by_cases a:i2.val+j2.val=0
    . rw[b i2 j2 a,mul_zero]
    . rw[ih i1 j1 (by omega),zero_mul]
  . rfl
lemma gy (f:a8 D1 D2 R)
 (a:∀ i j,i.val+j.val=0->f.coeff i j=0):
 f^(D1+D2)=0:=by
 apply ext;intro i j;exact dp f a (D1+D2) i j (by have:=i.isLt;have:=j.isLt;omega)
def r5 (f:a8 D1 D2 R):a8 D1 D2 R:=∑ k∈Finset.range (D1+D2),f^k
lemma eo (f:a8 D1 D2 R)
 (a:∀ i j,i.val+j.val=0->f.coeff i j=0):
 (1-f)*r5 f=1:=by
 unfold r5;have h:=geom_sum_mul_neg f (D1+D2);rw[mul_comm,h,gy f a,sub_zero]
def c8 (f:a8 D1 D2 R)(c:ℤ):a8 D1 D2 R:=if 0<=c then (1-f)^c.toNat else (r5 f)^(-c).toNat
lemma iz (f:a8 D1 D2 R):c8 f 0=1:=by simp[c8]
lemma nv (f:a8 D1 D2 R):c8 f 1=1-f:=by simp[c8]
lemma ld (f:a8 D1 D2 R):c8 f (-1)=r5 f:=by simp[c8]
lemma fp (f:a8 D1 D2 R) (r:∀ i j,i.val+j.val=0->f.coeff i j=0)
 (a b:ℤ):
 c8 f (a+b)=c8 f a*c8 f b:=by
 have h:=eo f r
 have d:∀ m k:ℕ,(1-f)^m*(r5 f)^k=if k<=m then (1-f)^(m-k) else (r5 f)^(k-m):=by
  intro m k;by_cases o:k<=m
  . rw[Q2 o];have p:m=(m-k)+k:=by omega
    conv_lhs=>rw[p,X6,mul_assoc,<-mul_pow,h,one_pow,mul_one]
  . rw[Q3 o];have q:k=m+(k-m):=by omega
    conv_lhs=>rw[q,X6,<-mul_assoc,<-mul_pow,h,one_pow,one_mul]
 by_cases l:0<=a<;>by_cases n:0<=b
 . have c:0<=a+b:=(by omega);simp only[c8,l,n,c,↓reduceIte];rw[<-X6];congr 1;omega
 . simp only[c8,l,n,↓reduceIte,d];by_cases c:0<=a+b
   . have e:(-b).toNat<=a.toNat:=(by omega);simp only[c,e,↓reduceIte];congr 1;omega
   . have g:¬ ((-b).toNat<=a.toNat):=(by omega);simp only[c,g,↓reduceIte];congr 1;omega
 . simp only[c8,l,n,↓reduceIte];rw[mul_comm,d];by_cases c:0<=a+b
   . have e:(-a).toNat<=b.toNat:=(by omega);simp only[c,e,↓reduceIte];congr 1;omega
   . have g:¬ ((-a).toNat<=b.toNat):=(by omega);simp only[c,g,↓reduceIte];congr 1;omega
 . have c:¬ (0<=a+b):=(by omega);simp only[c8,l,n,c,↓reduceIte];rw[<-X6];congr 1;omega
lemma jp (f:a8 D1 D2 R)
 (a:∀ i j,i.val+j.val=0->f.coeff i j=0):
 1+f=c8 f (-1)*c8 (f^2) 1:=by
 rw[ld,nv];have b:(1-f)*(1+f)=1-f^2:=by ring
 calc 1+f=1*(1+f):=(one_mul _).symm
  _=(r5 f*(1-f))*(1+f):=by rw[mul_comm (r5 f),eo f a]
  _=r5 f*((1-f)*(1+f)):=by rw[mul_assoc]
  _=r5 f*(1-f^2):=by rw[b]
end RingInst
end a8
def hist {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (r b:Fin (n+1)):ℕ:=
 ((univ:V7 (BV n->Y0)).filter (fun x=>(∀ v,p v=none\/p v=some (x v))/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card=b.val)).card
def profile {n:ℕ}(H:Fin (n+1)->Fin (n+1)->ℕ)(h:ℕ)(s:Fin (2*n+1)):ℕ:=∑ r:Fin (n+1),∑ b:Fin (n+1),if r.val+b.val=s.val then choose r.val h*H r b else 0
def e3 {n:ℕ}(p:P0 n):ℕ:=(univ.filter (fun v:BV n=>p v=none)).card
section ArcFactor
def q0 {R:Type*}[CommRing R](b:Y0):R:=if b then -1 else 1
lemma km {R:Type*}[CommRing R](b:Y0):q0 (R:=R) b*q0 b=1:=by
 cases b<;>simp[q0]
lemma ii {R:Type*}[CommRing R](a b:Y0)(u:R):1+u*q0 a*q0 b=if a≠b then 1-u else 1+u:=by
 cases a<;>cases b<;>simp[q0]<;>ring
def g8 {n:ℕ}(a:Perm (Fin n)):BV n ≃ BV n where
 toFun e:=match e.1 with
  | false=>(true,e.2)
  | true=>(false,a e.2)
 invFun e:=match e.1 with
  | true=>(false,e.2)
  | false=>(true,a.symm e.2)
 left_inv e:=by rcases e with ⟨b,i⟩;cases b<;>simp
 right_inv e:=by rcases e with ⟨b,i⟩;cases b<;>simp
def p4 {n:ℕ}(a:Perm (Fin n)):BV n ≃ BV n where
 toFun e:=match e.1 with
  | false=>(false,e.2)
  | true=>(true,a e.2)
 invFun v:=match v.1 with
  | false=>(false,v.2)
  | true=>(true,a.symm v.2)
 left_inv e:=by rcases e with ⟨b,i⟩;cases b<;>simp
 right_inv v:=by rcases v with ⟨b,i⟩;cases b<;>simp
def ef {R:Type*}[CommRing R]{n:ℕ}(p:P0 n)(v:BV n):R:=match p v with
 | none=>1
 | some b=>q0 b
lemma mq {R:Type*}[CommRing R]{n:ℕ}(p:P0 n)(v:BV n):ef (R:=R) p v=1\/ef (R:=R) p v=-1:=by
 unfold ef
 cases p v with
 | none=>left;rfl
 | some b=>cases b<;>simp[q0]
def qE {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (e:BV n):V9 Y0:=
 p (p4 a e)
def p8 {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (e:BV n):R:=
 ef p (p4 a e)
def lf {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (u v:R) (e:BV n):R:=
 (if e.1 then v else u)*p8 a p e*p8 a p ((g8 a).symm e)
def ao {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (u v:R):R:=
 ∑ r:Fin (n+1),∑ b:Fin (n+1),(hist a p r b:R) *(1-u)^r.val*(1+u)^(n-r.val) *(1-v)^b.val*(1+v)^(n-b.val)
lemma jq {R:Type*}[CommRing R](u:R){n:ℕ}(P:Fin n->Prop)[DecidablePred P]:(∏ i:Fin n,if P i then 1-u else 1+u)=(1-u)^(univ.filter P).card *(1+u)^(n-(univ.filter P).card):=by rw[prod_ite,prod_const,prod_const];congr 2;have h:=card_filter_add_card_filter_not (s:=(univ:V7 (Fin n))) P;simp only[W2,Q9] at h;omega
lemma kr {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (x:BV n->Y0) (u v:R):
 (1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *
 (1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card) *
 ((1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *
 (1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card))=
 ∏ e:BV n,(1+(if e.1 then v else u)*q0 (x (p4 a e))*q0 (x (p4 a ((g8 a).symm e)))):=by
 rw[Fintype.prod_prod_type,Fintype.prod_bool];have b:∏ i:Fin n,(1+(if false then v else u) *q0 (x (p4 a (false,i)))*q0 (x (p4 a ((g8 a).symm (false,i)))))=(1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *(1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card):=(by rw[<-jq];refine M4 rfl fun i _=>?_;simp only[J5,↓reduceIte,p4,g8,coe_fn_mk,coe_fn_symm_mk,Equiv.apply_symm_apply];exact ii (x (false,i)) (x (true,i)) u);have c:∏ i:Fin n,(1+(if true then v else u) *q0 (x (p4 a (true,i)))*q0 (x (p4 a ((g8 a).symm (true,i)))))=(1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *(1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card):=(by rw[<-jq];refine M4 rfl fun i _=>?_;simp only[↓reduceIte,p4,g8,coe_fn_mk,coe_fn_symm_mk];rw[ii (x (true,a i)) (x (false,i)) v];have d:(x (true,a i)≠x (false,i))↔(x (false,i)≠x (true,a i)):=ne_comm;simp only[d]);rw[c,b,mul_comm]
lemma jr {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (u v:R):
 ao a p u v=∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),(1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *(1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card) *((1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *(1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card)):=by
 unfold ao hist
 have f:∀ r b:Fin (n+1),(((univ:V7 (BV n->Y0)).filter (fun x=>(∀ w,p w=none\/p w=some (x w))/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card=b.val)).card:R) *(1-u)^r.val*(1+u)^(n-r.val) *(1-v)^b.val*(1+v)^(n-b.val)=∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),if(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card=b.val then (1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *(1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card) *((1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *(1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card))
   else 0:=by
  intro r b;rw[<-sum_filter,Finset.filter_filter];have c:∀ x∈(univ.filter (fun x:BV n->Y0=>(∀ w,p w=none\/p w=some (x w))/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card=b.val)),(1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *(1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card) *((1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *(1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card))=(1-u)^r.val*(1+u)^(n-r.val) *((1-v)^b.val*(1+v)^(n-b.val)):=(by intro x g;have hx':=(L4.mp g).2;rw[hx'.2.1,hx'.2.2]);rw[L3 rfl c,sum_const,nsmul_eq_mul];ring
 simp_rw[f];rw[X9]
 have d:∀ r:Fin (n+1),(∑ b:Fin (n+1),∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),if(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card=b.val then (1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *(1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card) *((1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *(1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card))
   else 0)=
  ∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),∑ b:Fin (n+1),if(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card=b.val then (1-u)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card *(1+u)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card) *((1-v)^(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card *(1+v)^(n-(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card))
    else 0:=fun _=>X9
 rw[X9];simp_rw[d];rw[X9];refine L3 rfl fun x _=>?_;set l:=(univ.filter (fun i:Fin n=>x (false,i)≠x (true,i))).card;set j:=(univ.filter (fun i:Fin n=>x (false,i)≠x (true,a i))).card;have m:l<n+1:=Nat.lt_succ_of_le (by simpa using card_filter_le (univ:V7 (Fin n)) _);have o:j<n+1:=Nat.lt_succ_of_le (by simpa using card_filter_le (univ:V7 (Fin n)) _);rw[Q4 ⟨l,m⟩]
 . rw[Q4 ⟨j,o⟩]
   . simp
   . intro b _ e;have:j≠b.val:=fun h=>e (L6 h.symm);simp[this]
   . intro k;exact absurd (Y2 _) k
 . intro r _ e;refine L9 fun b _=>?_;have:l≠r.val:=fun h=>e (L6 h.symm);simp[this]
 . intro k;exact absurd (Y2 _) k
lemma cn {c:Type*} [Fintype c] [DecidableEq c]
 {R:Type*} [CommRing R] (f:c->R):
 (∏ a:c,(1+f a))=∑ S:c->Y0,∏ a:c,if S a then f a else 1:=by
 have h:(∏ a:c,(1+f a))=∏ a:c,∑ b:Y0,if b then f a else 1:=(by refine M4 rfl fun a _=>?_;rw[sum_bool];simp[add_comm]);rw[h,Fintype.prod_sum]
lemma md {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (S x:BV n->Y0):
 (∏ e:BV n,if S e then q0 (R:=R) (x (p4 a e)) *q0 (x (p4 a ((g8 a).symm e))) else 1)=
 ∏ e:BV n,if S e≠S (g8 a e) then q0 (R:=R) (x (p4 a e)) else 1:=by
 have c:(∏ e:BV n,if S e then q0 (R:=R) (x (p4 a e)) *q0 (x (p4 a ((g8 a).symm e))) else 1)=(∏ e:BV n,if S e then q0 (R:=R) (x (p4 a e)) else 1) *(∏ e:BV n,if S e then q0 (R:=R) (x (p4 a ((g8 a).symm e))) else 1):=by
  rw[<-M3];refine M4 rfl fun e _=>?_;cases S e<;>simp
 have b:(∏ e:BV n,if S e then q0 (R:=R) (x (p4 a ((g8 a).symm e))) else 1)=∏ e:BV n,if S (g8 a e) then q0 (R:=R) (x (p4 a e)) else 1:=prod_equiv (g8 a).symm _ _ fun e=>(by simp);rw[c,b,<-M3];refine M4 rfl fun e _=>?_;cases S e<;>cases S (g8 a e)<;>simp[km]
lemma me {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (S:BV n->Y0):
 (∏ e:BV n,if S e≠S (g8 a e) then p8 (R:=R) a p e else 1)=
 ∏ e:BV n,if S e then p8 (R:=R) a p e*p8 a p ((g8 a).symm e) else 1:=by
 have d:(∏ e:BV n,if S e≠S (g8 a e) then p8 (R:=R) a p e else 1)=(∏ e:BV n,if S e then p8 (R:=R) a p e else 1) *(∏ e:BV n,if S (g8 a e) then p8 (R:=R) a p e else 1):=by
  rw[<-M3];refine M4 rfl fun e _=>?_
  have b:p8 (R:=R) a p e*p8 a p e=1:=by rcases mq (R:=R) p (p4 a e) with h|h<;>simp[p8,h]
  cases S e<;>cases S (g8 a e)<;>simp[b]
 have c:(∏ e:BV n,if S (g8 a e) then p8 (R:=R) a p e else 1)=∏ e:BV n,if S e then p8 (R:=R) a p ((g8 a).symm e) else 1:=prod_equiv (g8 a) _ _ fun e=>(by simp);rw[d,c,<-M3];refine M4 rfl fun e _=>?_;cases S e<;>simp
lemma gz {n:ℕ}(p:P0 n):univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w))=Fintype.piFinset (fun w:BV n=>match p w with|none=>univ|some b=>{b}):=by
 ext x;simp only[L4,Y2,Q0,Fintype.mem_piFinset];constructor
 . intro c w
   cases a:p w with
   | none=>exact Y2 _
   | some b=>
    rcases c w with h|h
    . rw[a] at h;cases h
    . rw[a] at h;have d:b=x w:=Option.some.inj h;simp[d]
 . intro c w;have a:=c w
   cases hp:p w with
   | none=>left;rfl
   | some b=>rw[hp] at a;right;simp only[U5] at a;rw[a]
lemma jz {R:Type*} [CommRing R] {n:ℕ} (d:Perm (Fin n))
 (p:P0 n) (S:BV n->Y0):
 (∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),∏ e:BV n,if S e≠S (g8 d e) then q0 (R:=R) (x (p4 d e)) else 1)=
 if ∀ e:BV n,qE d p e=none->S (g8 d e)=S e then (2:R)^e3 p *(∏ e:BV n,if S e≠S (g8 d e) then p8 (R:=R) d p e else 1)
 else 0:=by
 rw[gz];have j:∀ x:BV n->Y0,(∏ e:BV n,if S e≠S (g8 d e) then q0 (R:=R) (x (p4 d e)) else 1)=∏ w:BV n,if S ((p4 d).symm w)≠S (g8 d ((p4 d).symm w)) then q0 (x w) else 1:=fun x=>prod_equiv (p4 d) _ _ fun e=>(by simp);simp_rw[j]
 rw[(Finset.prod_univ_sum (fun w:BV n=>match p w with|none=>univ|some b=>{b}) (fun w b=>if S ((p4 d).symm w)≠S (g8 d ((p4 d).symm w)) then q0 (R:=R) b else 1)).symm]
 have k:(∏ w:BV n,∑ b∈(match p w with|none=>univ|some c=>{c}),if S ((p4 d).symm w)≠S (g8 d ((p4 d).symm w)) then q0 (R:=R) b else 1)=∏ e:BV n,∑ b∈(match qE d p e with|none=>univ|some c=>{c}),if S e≠S (g8 d e) then q0 (R:=R) b else 1:=prod_equiv (p4 d).symm _ _ fun w=>by simp[qE]
 rw[k];by_cases h:∀ e:BV n,qE d p e=none->S (g8 d e)=S e
 . rw[Q2 h]
   have i:∀ e:BV n,(∑ b∈(match qE d p e with|none=>univ|some c=>{c}),if S e≠S (g8 d e) then q0 (R:=R) b else 1)=(if qE d p e=none then (2:R) else 1) *(if S e≠S (g8 d e) then p8 (R:=R) d p e else 1):=by
    intro e
    cases l:qE d p e with
    | none=>
     have q:S (g8 d e)=S e:=h e l;have g:¬ (S e≠S (g8 d e)):=(by simp[q]);simp only[g,↓reduceIte,sum_const,W2,card_bool,nsmul_eq_mul,mul_one,Nat.cast_ofNat]
    | some c=>
     simp only[sum_singleton,reduceCtorEq,↓reduceIte,one_mul,p8,ef]
     change (if S e≠S (g8 d e) then q0 (R:=R) c else 1)=if S e≠S (g8 d e) then (match qE d p e with|none=>1|some b=>q0 (R:=R) b) else 1
     rw[l]
   simp_rw[i];rw[M3];congr 1;rw[prod_ite,prod_const,Finset.prod_const_one,mul_one];congr 1;unfold e3;rw[<-card_subtype,<-card_subtype];exact Fintype.card_of_bijective (f:=fun x:{e:BV n // qE d p e=none}=>(⟨p4 d x.1,x.2⟩:{w:BV n // p w=none}))
    ⟨fun a b s=>Z9 ((p4 d).injective (Q6 Subtype.val s)),fun y=>⟨⟨(p4 d).symm y.1,by simp[qE,y.2]⟩,Z9 (by simp)⟩⟩
 . rw[Q3 h];have o:∃ e0:BV n,qE d p e0=none/\S (g8 d e0)≠S e0:=(by by_contra hall;apply h;intro e l;by_contra g;exact hall ⟨e,l,g⟩);obtain⟨e0,r,m⟩:=o;refine Finset.prod_eq_zero (Y2 e0) ?_;rw[r];have hne':S e0≠S (g8 d e0):=Ne.symm m;rw[sum_bool,Q2 hne',Q2 hne'];simp[q0]
lemma kt {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (u v:R):
 ao a p u v=(2:R)^e3 p *∑ S∈univ.filter (fun S:BV n->Y0=>∀ e:BV n,qE a p e=none->S (g8 a e)=S e),∏ e:BV n,if S e then lf a p u v e else 1:=by
 rw[jr];simp_rw[kr,cn];rw[X9]
 have c:∀ S:BV n->Y0,(∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),∏ e:BV n,if S e then (if e.1 then v else u)*q0 (R:=R) (x (p4 a e)) *q0 (x (p4 a ((g8 a).symm e)))
    else 1)=
  (∏ e:BV n,if S e then (if e.1 then v else u) else 1) *
  (∑ x∈univ.filter (fun x:BV n->Y0=>∀ w,p w=none\/p w=some (x w)),∏ e:BV n,if S e≠S (g8 a e) then q0 (R:=R) (x (p4 a e)) else 1):=by
  intro S;rw[mul_sum];refine L3 rfl fun x _=>?_;rw[<-md,<-M3];refine M4 rfl fun e _=>?_;cases S e<;>simp[mul_assoc]
 simp_rw[c,jz];rw[mul_sum,sum_filter];refine L3 rfl fun S _=>?_;by_cases b:∀ e:BV n,qE a p e=none->S (g8 a e)=S e
 . rw[Q2 b,Q2 b];rw[me,<-mul_assoc,mul_comm _ ((2:R)^e3 p),mul_assoc];congr 1;rw[<-M3];refine M4 rfl fun e _=>?_;cases S e<;>simp[lf,mul_assoc]
 . rw[Q3 b,Q3 b,mul_zero]
lemma lg {c f:Type*} [Fintype c] [Fintype f] [DecidableEq c] [DecidableEq f]
 {R:Type*} [CommRing R]
 (a:c->f) (d:Surjective a) (W:c->R)
 (P:(c->Y0)->Prop) [DecidablePred P]
 (k:∀ S:c->Y0,P S↔∀ x y,a x=a y->S x=S y):
 (∑ S∈univ.filter P,∏ x:c,if S x then W x else 1)=
 ∏ b:f,(1+∏ x∈univ.filter (fun x=>a x=b),W x):=by
 rw[cn];symm;refine sum_bij (fun T _=>fun x=>T (a x)) ?_ ?_ ?_ ?_
 . intro T _;simp only[L4,Y2,Q0,k];intro x y j;rw[j]
 . intro T1 _ T2 _ h
   funext b
   obtain⟨x,rfl⟩:=d b;exact congrFun h x
 . intro S i;simp only[L4,Y2,Q0,k] at i;refine⟨fun b=>S (d b).choose,Y2 _,?_⟩
   funext x
   exact i _ _ (d (a x)).choose_spec
 . intro T _;have g:(∏ x:c,if T (a x) then W x else 1)=∏ b:f,∏ x∈univ.filter (fun x:c=>a x=b),if T (a x) then W x else 1:=(Finset.prod_fiberwise_of_maps_to (fun _ _=>Y2 _) _).symm;rw[g];refine M4 rfl fun b _=>?_;cases hTb:T b
   . simp only[J5,↓reduceIte];refine (prod_eq_one fun x e=>?_).symm;rw[L4] at e;simp[e.2,hTb]
   . simp only[↓reduceIte];refine (M4 rfl fun x e=>?_).symm;rw[L4] at e;simp[e.2,hTb]
def o9 {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (b c:BV n):Prop:=
 qE a p b=none/\c=g8 a b
lemma ka {n:ℕ} {b:Perm (Fin n)} {p:P0 n}
 {x a c:BV n} (e:o9 b p x a) (d:o9 b p x c):a=c:=
 e.2.trans d.2.symm
lemma ku {n:ℕ} {a:Perm (Fin n)} {p:P0 n}
 {b c y:BV n} (e:o9 a p b y) (d:o9 a p c y):b=c:=
 (g8 a).injective (e.2.symm.trans d.2)
lemma mr {n:ℕ} {d:Perm (Fin n)} {p:P0 n}
 {a x y:BV n}
 (g:ReflTransGen (o9 d p) a x)
 (e:ReflTransGen (o9 d p) a y):
 ReflTransGen (o9 d p) x y\/ReflTransGen (o9 d p) y x:=by
 induction g using ReflTransGen.head_induction_on generalizing y with
 | refl=>left;exact e
 | @head a' b hab hbx ih=>
  rcases ReflTransGen.cases_head e with rfl|⟨c,hac,hcy⟩
  . right;exact ReflTransGen.head hab hbx
  . have f:b=c:=ka hab hac;subst f;exact ih hcy
lemma ng {n:ℕ} {d:Perm (Fin n)} {p:P0 n}
 {a x y:BV n}
 (g:ReflTransGen (o9 d p) x a)
 (e:ReflTransGen (o9 d p) y a):
 ReflTransGen (o9 d p) x y\/ReflTransGen (o9 d p) y x:=by
 induction g generalizing y with
 | refl=>right;exact e
 | @tail b a' hxb hba ih=>
  rcases ReflTransGen.cases_tail e with rfl|⟨c,hyc,hca⟩
  . left;exact ReflTransGen.tail hxb hba
  . have f:b=c:=ku hba hca;subst f;exact ih hyc
lemma eh {n:ℕ} {f:Perm (Fin n)} {p:P0 n}
 {x y:BV n} (h:EqvGen (o9 f p) x y):
 ReflTransGen (o9 f p) x y\/ReflTransGen (o9 f p) y x:=by
 induction h with
 | rel a b hab=>left;exact ReflTransGen.single hab
 | refl a=>left;exact ReflTransGen.refl
 | symm a b _ ih=>exact ih.symm
 | trans a b c _ _ ih1 ih2=>
  rcases ih1 with e|e<;>rcases ih2 with d|d
  . left;exact e.trans d
  . exact ng e d
  . exact mr e d
  . right;exact d.trans e
lemma pm {n:ℕ} {c:Perm (Fin n)} {p:P0 n}
 {x y:BV n} (a:EqvGen (o9 c p) x y)
 (e:qE c p x≠none) (d:qE c p y≠none):x=y:=by
 rcases eh a with h|h
 . rcases ReflTransGen.cases_head h with rfl|⟨b,hxb,_⟩
   . rfl
   . exact absurd hxb.1 e
 . rcases ReflTransGen.cases_head h with rfl|⟨b,hyb,_⟩
   . rfl
   . exact absurd hyb.1 d
lemma kv {n:ℕ} (d:Perm (Fin n)) (p:P0 n)
 (S:BV n->Y0):
 (∀ e:BV n,qE d p e=none->S (g8 d e)=S e)↔
 (∀ x y:BV n,EqvGen (o9 d p) x y->S x=S y):=by
 constructor
 . intro h x y f
   induction f with
   | rel a b hab=>rw[hab.2];exact (h a hab.1).symm
   | refl a=>rfl
   | symm a b _ ih=>exact ih.symm
   | trans a b c _ _ ih1 ih2=>exact ih1.trans ih2
 . intro h e g;exact (h e (g8 d e) (EqvGen.rel e (g8 d e) ⟨g,rfl⟩)).symm
noncomputable def n8 {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (e:BV n):V7 (BV n):=
 @Finset.filter _ (fun b=>EqvGen (o9 a p) e b) (decPred _) univ
noncomputable def f6 {n:ℕ}(a:Perm (Fin n))(p:P0 n):V7 (V7 (BV n)):=univ.image (n8 a p)
def n5 {n:ℕ}(c:V7 (BV n)):ℕ:=(c.filter (fun e=>e.1=false)).card
def s3 {n:ℕ}(c:V7 (BV n)):ℕ:=(c.filter (fun e=>e.1=true)).card
def p9 {n:ℕ}(c:V7 (BV n)):ℕ:=n5 c+s3 c
lemma bj {n:ℕ}(c:V7 (BV n)):p9 c=c.card:=by
 unfold p9 n5 s3;have h:=card_filter_add_card_filter_not (s:=c) (fun e:BV n=>e.1=false)
 have a:c.filter (fun e=>¬ e.1=false)=c.filter (fun e=>e.1=true):=by
  ext e;cases e.1<;>simp
 rw[a] at h;exact h
def m4 {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (c:V7 (BV n)):ℤ:=
 ∏ e∈c,(p8 (R:=ℤ) a p e*p8 (R:=ℤ) a p ((g8 a).symm e))
lemma ml {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (c:V7 (BV n)):
 m4 a p c=1\/m4 a p c=-1:=by
 unfold m4
 induction c using induction_on with
 | empty=>left;simp
 | @insert e s he ih=>
  rw[prod_insert he]
  have b:p8 (R:=ℤ) a p e*p8 (R:=ℤ) a p ((g8 a).symm e)=1\/p8 (R:=ℤ) a p e*p8 (R:=ℤ) a p ((g8 a).symm e)=-1:=by rcases mq (R:=ℤ) p (p4 a e) with d|d<;>rcases mq (R:=ℤ) p (p4 a ((g8 a).symm e)) with f|f<;>simp[p8,d,f]
  rcases b with b|b<;>rcases ih with ih|ih<;>simp[b,ih]
lemma js {n:ℕ} (b:Perm (Fin n)) (p:P0 n)
 (l:BV n):
 let c:=n8 b p l
 0<p9 c/\n5 c<=s3 c+1/\s3 c<=n5 c+1:=by
 classical
 intro c;have g:l∈c:=(by simp[c,n8,EqvGen.refl]);have k:0<p9 c:=by rw[bj];exact Finset.card_pos.mpr ⟨l,g⟩
 have f:(c.filter (fun e=>qE b p e≠none)).card<=1:=by rw[Finset.card_le_one];intro x h y i;simp only[L4,c,n8,Y2,Q0] at h i;exact pm (EqvGen.trans _ _ _ (EqvGen.symm _ _ h.1) i.1) h.2 i.2
 have d:∀ col:Y0,(c.filter (fun e=>e.1=col)).card<=(c.filter (fun e=>e.1=!col)).card+1:=by
  intro col;set s:=c.filter (fun e=>e.1=col);have q:=card_filter_add_card_filter_not (s:=s) (fun e=>qE b p e=none);have m:(s.filter (fun e=>¬ qE b p e=none)).card<=1:=by refine le_trans (card_le_card ?_) f;intro e a;simp only[L4,s] at a ⊢;exact⟨a.1.1,a.2⟩
  have o:(s.filter (fun e=>qE b p e=none)).card<=(c.filter (fun e=>e.1=!col)).card:=by
   have j:((s.filter (fun e=>qE b p e=none)).image (g8 b)).card=(s.filter (fun e=>qE b p e=none)).card:=card_image_of_injective _ (g8 b).injective;rw[<-j];refine card_le_card ?_;intro e' he';rw[X5] at he';obtain⟨e,a,rfl⟩:=he';simp only[L4,s,c,n8,Y2,Q0] at a ⊢;refine⟨EqvGen.trans _ _ _ a.1.1 (EqvGen.rel e (g8 b e) ⟨a.2,rfl⟩),?_⟩
   rcases e with ⟨eb,ei⟩
   cases eb<;>simp[g8] at a ⊢<;>simp[a.1.2]
  omega
 refine⟨k,?_,?_⟩
 . simpa[n5,s3] using d false
 . simpa[n5,s3] using d true
lemma fi {n:ℕ}(d:Perm (Fin n))(p:P0 n):∑ c∈f6 d p,c.card=2*n:=by
 classical
 have g:=card_eq_sum_card_fiberwise (f:=n8 d p) (s:=univ)
  (t:=f6 d p) (fun e _=>mem_image_of_mem _ (Y2 e))
 have i:(univ:V7 (BV n)).card=2*n:=(by simp);rw[i] at g;rw[g];refine L3 rfl fun c k=>?_;obtain⟨e0,_,rfl⟩:=X5.mp k;congr 1;ext e;simp only[L4,Y2,Q0];constructor
 . intro a;have hrel':EqvGen (o9 d p) e0 e:=(L4.mp a).2;ext z;simp only[n8,L4,Y2,Q0];exact⟨fun h=>EqvGen.trans _ _ _ hrel' h,fun h=>EqvGen.trans _ _ _ (EqvGen.symm _ _ hrel') h⟩
 . intro j;have b:e∈n8 d p e:=(by simp[n8,EqvGen.refl]);rw[j] at b;exact b
lemma gb {n:ℕ}(a:Perm (Fin n))(p:P0 n):(f6 a p).card<=2*n:=by have e:=fi a p;have b:∑ _c∈f6 a p,1<=∑ c∈f6 a p,c.card:=(by refine Finset.sum_le_sum fun c f=>?_;obtain⟨e0,_,rfl⟩:=X5.mp f;have d:=(js a p e0).1;rw[bj] at d;exact d);simp only[sum_const,smul_eq_mul,mul_one] at b;omega
lemma w9 {n:ℕ} (b:Perm (Fin n)) (p:P0 n)
 (c:V7 (BV n)) (e:c∈f6 b p):
 1<=p9 c/\p9 c<=2*n/\n5 c<=s3 c+1/\s3 c<=n5 c+1:=by
 obtain⟨e0,_,rfl⟩:=X5.mp e;obtain⟨a,g,f⟩:=js b p e0
 have d:(n8 b p e0).card<=2*n:=by
  calc (n8 b p e0).card<=(univ:V7 (BV n)).card:=Finset.card_le_univ _
   _=2*n:=by simp
 rw[bj] at a ⊢;exact⟨a,d,g,f⟩
lemma kn {R:Type*} [CommRing R] {n:ℕ} (a:Perm (Fin n))
 (p:P0 n) (e:BV n):
 ((p8 (R:=ℤ) a p e:ℤ):R)=p8 (R:=R) a p e:=by
 unfold p8 ef
 cases p (p4 a e) with
 | none=>simp
 | some b=>cases b<;>simp[q0]
lemma cs {R:Type*} [CommRing R] {n:ℕ}
 (b:Perm (Fin n)) (p:P0 n) (u v:R):
 ao b p u v=(2:R)^e3 p *∏ c∈f6 b p,(1+(m4 b p c:R)*u^n5 c*v^s3 c):=by
 classical
 rw[kt];congr 1;let a:BV n->{c:V7 (BV n) // c∈f6 b p}:=fun e=>⟨n8 b p e,mem_image_of_mem _ (Y2 e)⟩;have g:Surjective a:=by rintro⟨c,i⟩;obtain⟨e,_,rfl⟩:=X5.mp i;exact⟨e,rfl⟩
 have d:∀ x y,a x=a y↔EqvGen (o9 b p) x y:=by
  intro x y;constructor
  . intro h;have k:y∈n8 b p y:=(by simp[n8,EqvGen.refl]);have h':n8 b p x=n8 b p y:=Q6 Subtype.val h;rw[<-h'] at k;exact (L4.mp k).2
  . intro h;apply Z9;ext z;simp only[a,n8,L4,Y2,Q0];exact⟨fun l=>EqvGen.trans _ _ _ (EqvGen.symm _ _ h) l,fun m=>EqvGen.trans _ _ _ h m⟩
 have j:∀ c:{c:V7 (BV n) // c∈f6 b p},univ.filter (fun x=>a x=c)=c.1:=by rintro⟨c,i⟩;obtain⟨e0,_,rfl⟩:=X5.mp i;ext x;simp only[L4,Y2,Q0];change a x=a e0↔x∈n8 b p e0;rw[d];simp only[n8,L4,Y2,Q0];exact⟨fun h=>EqvGen.symm _ _ h,fun h=>EqvGen.symm _ _ h⟩
 rw[lg a g (lf b p u v) _ (fun S=>by
  simp only[d];exact kv b p S)]
 rw[<-Finset.prod_attach (f6 b p)];change (∏ c:{c // c∈f6 b p},_)=∏ c:{c // c∈f6 b p},_;refine M4 rfl fun c _=>?_;rw[j c];congr 1;have f:(∏ e∈c.1,lf b p u v e)=(∏ e∈c.1,if e.1 then v else u) *(∏ e∈c.1,(p8 (R:=R) b p e*p8 b p ((g8 b).symm e))):=by rw[<-M3];refine M4 rfl fun e _=>?_;simp[lf,mul_assoc]
 have o:(∏ e∈c.1,if e.1 then v else u)=u^n5 c.1*v^s3 c.1:=by
  have r:c.1.filter (fun e=>¬ e.1=true)=c.1.filter (fun e=>e.1=false):=by
   ext e;cases e.1<;>simp
  rw[prod_ite,prod_const,prod_const,mul_comm,r];rfl
 have q:(∏ e∈c.1,(p8 (R:=R) b p e*p8 b p ((g8 b).symm e)))=(m4 b p c.1:R):=(by unfold m4;rw[Int.cast_prod];refine M4 rfl fun e _=>?_;rw[Int.cast_mul,kn,kn]);rw[f,o,q];ring
lemma gc {n:ℕ}(a:Perm (Fin n))(p:P0 n):∑ r:Fin (n+1),∑ b:Fin (n+1),hist a p r b=2^e3 p:=by
 have h:=cs (R:=ℤ) a p 0 0;have g:ao (R:=ℤ) a p 0 0=((∑ r:Fin (n+1),∑ b:Fin (n+1),hist a p r b:ℕ):ℤ):=by unfold ao;simp[Nat.cast_sum]
 have j:(∏ c∈f6 a p,(1+(m4 a p c:ℤ)*(0:ℤ)^n5 c*(0:ℤ)^s3 c))=1:=by
  refine prod_eq_one fun c f=>?_;have d:=(w9 a p c f).1;unfold p9 at d;by_cases i:n5 c=0
  . have e:s3 c≠0:=(by omega);simp[zero_pow e]
  . simp[zero_pow i]
 simp only[cast_id] at h;rw[g,j,mul_one] at h
 exact_mod_cast h
lemma gn {n:ℕ}(a:Perm (Fin n))(p:P0 n):∑ s:Fin (2*n+1),profile (hist a p) 0 s=2^e3 p:=by
 rw[<-gc a p];unfold profile;simp only[U8,one_mul];rw[X9];refine L3 rfl fun r _=>?_;rw[X9];refine L3 rfl fun b _=>?_;have d:r.val+b.val<2*n+1:=(by have:=r.isLt;have:=b.isLt;omega);rw[Q4 ⟨r.val+b.val,d⟩]
 . simp
 . intro s _ c;have:r.val+b.val≠s.val:=fun h=>c (L6 h.symm);simp[this]
 . intro e;exact absurd (Y2 _) e
end ArcFactor
noncomputable section KrawAndAlgebra
def ca (deg s:ℕ):Polynomial ℤ:=(1-X)^s*(1+X)^(deg-s)
def c6 (deg s d:ℕ):ℤ:=(ca deg s).coeff d
lemma ep {deg s:ℕ}(b:s<=deg):(ca deg s).natDegree<=deg:=by
 unfold ca
 have c:((1-X:Polynomial ℤ)^s).natDegree<=s:=by
  calc ((1-X:Polynomial ℤ)^s).natDegree
   ≤ s*(1-X:Polynomial ℤ).natDegree:=natDegree_pow_le
   _<=s*1:=W5 _ (by
    calc (1-X:Polynomial ℤ).natDegree
     ≤ max (1:Polynomial ℤ).natDegree X.natDegree:=natDegree_sub_le _ _
     _<=1:=by simp)
   _=s:=Nat.mul_one _
 have a:((1+X:Polynomial ℤ)^(deg-s)).natDegree<=deg-s:=by
  calc ((1+X:Polynomial ℤ)^(deg-s)).natDegree
   ≤ (deg-s)*(1+X:Polynomial ℤ).natDegree:=natDegree_pow_le
   _<=(deg-s)*1:=W5 _ (by
    calc (1+X:Polynomial ℤ).natDegree
     ≤ max (1:Polynomial ℤ).natDegree X.natDegree:=natDegree_add_le _ _
     _<=1:=by simp)
   _=deg-s:=Nat.mul_one _
 calc ((1-X:Polynomial ℤ)^s*(1+X)^(deg-s)).natDegree
  ≤ ((1-X:Polynomial ℤ)^s).natDegree +((1+X:Polynomial ℤ)^(deg-s)).natDegree:=Polynomial.natDegree_mul_le
  _<=s+(deg-s):=Nat.add_le_add c a
  _=deg:=V3 b
lemma go {R:Type*}[CommRing R]{deg s:ℕ}(e:s<=deg)(x:R):∑ d:Fin (deg+1),(c6 deg s d.val:R)*x^d.val=(1-x)^s*(1+x)^(deg-s):=by have b:(ca deg s).natDegree<deg+1:=Nat.lt_succ_of_le (ep e);have a:=Polynomial.eval₂_eq_sum_range' (f:=castRingHom R) (x:=x) b;rw[<-Fin.sum_univ_eq_sum_range] at a;have c:Polynomial.eval₂ (castRingHom R) x (ca deg s)=(1-x)^s*(1+x)^(deg-s):=(by simp[ca,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_sub,Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_X]);rw[c] at a;simpa[c6] using a.symm
def df (d:ℕ)(p A B:Polynomial ℤ):Polynomial ℤ:=∑ i:Fin (d+1),C (p.coeff i.val)*A^i.val*B^(d-i.val)
lemma oj {a b:ℕ} {p q:Polynomial ℤ} (hp:p.natDegree<=a) (hq:q.natDegree<=b)
 (A B:Polynomial ℤ):
 df (a+b) (p*q) A B=df a p A B*df b q A B:=by
 unfold df;rw[sum_mul];simp_rw[mul_sum]
 have z:∀ k:Fin (a+b+1),C ((p*q).coeff k.val)*A^k.val*B^(a+b-k.val)=∑ i:Fin (a+1),∑ j:Fin (b+1),if i.val+j.val=k.val then C (p.coeff i.val)*A^i.val*B^(a-i.val) *(C (q.coeff j.val)*A^j.val*B^(b-j.val))
   else 0:=by
  intro k;rw[Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y=>p.coeff x*q.coeff y)]
  have e:(∑ x∈Finset.range (k.val+1),p.coeff x*q.coeff (k.val-x))=∑ i:Fin (a+1),∑ j:Fin (b+1),if i.val+j.val=k.val then p.coeff i.val*q.coeff j.val else 0:=by
   have c:∀ i:Fin (a+1),(∑ j:Fin (b+1),if i.val+j.val=k.val then p.coeff i.val*q.coeff j.val else 0)=if i.val<=k.val then p.coeff i.val*q.coeff (k.val-i.val) else 0:=by
    intro i;by_cases d:i.val<=k.val
    . rw[Q2 d];by_cases t:k.val-i.val<b+1
      . rw[Q4 ⟨k.val-i.val,t⟩]
        . simp[V3 d]
        . intro j _ f;have:i.val+j.val≠k.val:=fun h=>f (L6 (by dsimp only;omega));simp[this]
        . intro o;exact absurd (Y2 _) o
      . have u:q.coeff (k.val-i.val)=0:=coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq (by omega));rw[u,mul_zero];refine L9 fun j _=>?_;have:i.val+j.val≠k.val:=(by have:=j.isLt;omega);simp[this]
    . rw[Q3 d];refine L9 fun j _=>?_;have:i.val+j.val≠k.val:=(by omega);simp[this]
   simp_rw[c];have m:(∑ i:Fin (a+1),if i.val<=k.val then p.coeff i.val*q.coeff (k.val-i.val) else 0)=∑ x∈Finset.range (a+1),if x<=k.val then p.coeff x*q.coeff (k.val-x) else 0:=Fin.sum_univ_eq_sum_range (fun x=>if x<=k.val then p.coeff x*q.coeff (k.val-x) else 0) (a+1);rw[m,<-sum_filter];have r:(Finset.range (a+1)).filter (·<=k.val)=Finset.range (min (a+1) (k.val+1)):=(by ext x;simp only[L4,mem_range];omega);rw[r];symm;refine sum_subset (Finset.range_mono (Nat.min_le_right _ _)) fun x hx n=>?_;simp only[mem_range] at hx n;have v:p.natDegree<x:=lt_of_le_of_lt hp (by omega);rw[coeff_eq_zero_of_natDegree_lt v,zero_mul]
  rw[e,map_sum,sum_mul,sum_mul];refine L3 rfl fun i _=>?_;rw[map_sum,sum_mul,sum_mul];refine L3 rfl fun j _=>?_
  split_ifs with w
  . have g:i.val+j.val=k.val:=w;have l:a+b-(i.val+j.val)=(a-i.val)+(b-j.val):=(by have:=i.isLt;have:=j.isLt;omega);rw[map_mul,<-g,l,X6,X6];ring
  . simp
 simp_rw[z];rw[X9];refine L3 rfl fun i _=>?_;rw[X9];refine L3 rfl fun j _=>?_;have s:i.val+j.val<a+b+1:=(by have:=i.isLt;have:=j.isLt;omega);rw[Q4 ⟨i.val+j.val,s⟩]
 . simp
 . intro k _ f;have:i.val+j.val≠k.val:=fun h=>f (L6 h.symm);simp[this]
 . intro o;exact absurd (Y2 _) o
lemma nh (A B:Polynomial ℤ):df 1 (1-X) A B=B-A:=by unfold df;rw[Fin.sum_univ_two];simp only[val_zero,val_one,Nat.sub_zero,Nat.sub_self,pow_zero,pow_one,mul_one,one_mul,Polynomial.coeff_sub,coeff_one_zero,coeff_X_zero,Polynomial.coeff_one,coeff_X];simp;ring
lemma ni (A B:Polynomial ℤ):df 1 (1+X) A B=B+A:=by unfold df;rw[Fin.sum_univ_two];simp only[val_zero,val_one,Nat.sub_zero,Nat.sub_self,pow_zero,pow_one,mul_one,Polynomial.coeff_add,coeff_one_zero,coeff_X_zero,Polynomial.coeff_one,coeff_X];simp
lemma ok {p:Polynomial ℤ}(b:p.natDegree<=1)(k:ℕ)(A B:Polynomial ℤ):df k (p^k) A B=(df 1 p A B)^k:=by
 induction k with
 | zero=>simp[df]
 | succ k ih=>
  have a:(p^k).natDegree<=k:=by
   calc (p^k).natDegree<=k*p.natDegree:=natDegree_pow_le
    _<=k*1:=W5 _ b
    _=k:=Nat.mul_one _
  rw[U4,U4,oj a b,ih]
lemma nw {n s:ℕ}(f:s<=n)(A B:Polynomial ℤ):df n (ca n s) A B=(B-A)^s*(B+A)^(n-s):=by
 have b:(1-X:Polynomial ℤ).natDegree<=1:=by
  calc (1-X:Polynomial ℤ).natDegree
   ≤ max (1:Polynomial ℤ).natDegree X.natDegree:=natDegree_sub_le _ _
   _<=1:=by simp
 have d:(1+X:Polynomial ℤ).natDegree<=1:=by
  calc (1+X:Polynomial ℤ).natDegree
   ≤ max (1:Polynomial ℤ).natDegree X.natDegree:=natDegree_add_le _ _
   _<=1:=by simp
 have a:((1-X:Polynomial ℤ)^s).natDegree<=s:=by
  calc ((1-X:Polynomial ℤ)^s).natDegree<=s*_:=natDegree_pow_le
   _<=s*1:=W5 _ b
   _=s:=Nat.mul_one _
 have c:((1+X:Polynomial ℤ)^(n-s)).natDegree<=n-s:=by
  calc ((1+X:Polynomial ℤ)^(n-s)).natDegree<=(n-s)*_:=natDegree_pow_le
   _<=(n-s)*1:=W5 _ d
   _=n-s:=Nat.mul_one _
 have e:s+(n-s)=n:=V3 f;rw[<-e];unfold ca;rw[Nat.add_sub_cancel_left];rw[oj a c,ok b,ok d,nh,ni]
lemma nj (n:ℕ)(r l:Fin (n+1)):∑ i:Fin (n+1),c6 n i.val r.val*c6 n l.val i.val=if r=l then (2:ℤ)^n else 0:=by
 have b:=nw (U1 l.isLt) (1-X) (1+X);have g:(1+X:Polynomial ℤ)-(1-X)=C 2*X:=(by simp;ring);have j:(1+X:Polynomial ℤ)+(1-X)=C 2:=(by simp;ring);rw[g,j] at b
 have f:(C (2:ℤ)*X)^l.val*(C (2:ℤ))^(n-l.val)=C ((2:ℤ)^n)*X^l.val:=by
  rw[mul_pow,<-map_pow,<-map_pow];have e:C ((2:ℤ)^l.val)*C ((2:ℤ)^(n-l.val))=C ((2:ℤ)^n):=by rw[<-map_mul,<-X6,V3 (U1 l.isLt)]
  calc C ((2:ℤ)^l.val)*X^l.val*C ((2:ℤ)^(n-l.val))
   =(C ((2:ℤ)^l.val)*C ((2:ℤ)^(n-l.val)))*X^l.val:=by ring
   _=C ((2:ℤ)^n)*X^l.val:=by rw[e]
 rw[f] at b;have a:=Q6 (fun p:Polynomial ℤ=>lcoeff ℤ r.val p) b;simp only[df,map_sum,Polynomial.lcoeff_apply,mul_assoc,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow] at a
 have d:(∑ i:Fin (n+1),c6 n i.val r.val*c6 n l.val i.val)=∑ i:Fin (n+1),(ca n l.val).coeff i.val *(((1-X:Polynomial ℤ)^i.val)*(1+X)^(n-i.val)).coeff r.val:=by
  refine L3 rfl fun i _=>by rw[mul_comm];rfl
 rw[d,a];by_cases c:r=l
 . subst c;simp
 . have k:r.val≠l.val:=fun h=>c (L6 h);simp[c,k]
lemma ms {R:Type*} [CommRing R] {n:ℕ}
 (a:Perm (Fin n)) (p:P0 n) (i j:Fin (n+1)):
 (ao a p (a8.X1:a8 (n+1) (n+1) R) a8.X2).coeff i j=∑ r:Fin (n+1),∑ b:Fin (n+1),(hist a p r b:R)*(c6 n r.val i.val:R)*(c6 n b.val j.val:R):=by
 unfold ao;rw[a8.z8];refine L3 rfl fun r _=>?_;rw[a8.z8];refine L3 rfl fun b _=>?_;have g:=go (R:=a8 (n+1) (n+1) R) (U1 r.isLt) a8.X1;have k:=go (R:=a8 (n+1) (n+1) R) (U1 b.isLt) a8.X2;have f:(hist a p r b:a8 (n+1) (n+1) R) *(1-a8.X1)^r.val*(1+a8.X1)^(n-r.val) *(1-a8.X2)^b.val*(1+a8.X2)^(n-b.val)=(hist a p r b:a8 (n+1) (n+1) R) *(((1-a8.X1)^r.val*(1+a8.X1)^(n-r.val)) *((1-a8.X2)^b.val*(1+a8.X2)^(n-b.val))):=(by ring);rw[f,<-g,<-k];have d:((hist a p r b:a8 (n+1) (n+1) R) *((∑ d1:Fin (n+1),(c6 n r.val d1.val:a8 (n+1) (n+1) R)*a8.X1^d1.val) *(∑ d2:Fin (n+1),(c6 n b.val d2.val:a8 (n+1) (n+1) R)*a8.X2^d2.val)))=∑ d1:Fin (n+1),∑ d2:Fin (n+1),(hist a p r b:a8 (n+1) (n+1) R) *(c6 n r.val d1.val:a8 (n+1) (n+1) R) *(c6 n b.val d2.val:a8 (n+1) (n+1) R)*a8.o5 d1.val d2.val:=(by rw[sum_mul];simp_rw[mul_sum];refine L3 rfl fun d1 _=>L3 rfl fun d2 _=>?_;rw[<-a8.t5];ring);rw[d,a8.z8];rw[Q4 i]
 . rw[a8.z8,Q4 j]
   . rw[mul_assoc,mul_assoc,a8.l0,a8.s4,a8.s4];simp[a8.o5,mul_assoc]
   . intro d2 _ c;rw[mul_assoc,mul_assoc,a8.l0,a8.s4,a8.s4];have:j.val≠d2.val:=fun h=>c (L6 h.symm);simp[a8.o5,this]
   . intro e;exact absurd (Y2 _) e
 . intro d1 _ c;rw[a8.z8];refine L9 fun d2 _=>?_;rw[mul_assoc,mul_assoc,a8.l0,a8.s4,a8.s4];have:i.val≠d1.val:=fun h=>c (L6 h.symm);simp[a8.o5,this]
 . intro e;exact absurd (Y2 _) e
noncomputable def u9 {R:Type*} [CommRing R] {n:ℕ}
 (a:Perm (Fin n)) (p:P0 n):a8 (n+1) (n+1) R:=
 ∏ c∈f6 a p,(1+(m4 a p c:a8 (n+1) (n+1) R)*a8.X1^n5 c*a8.X2^s3 c)
lemma lh {n:ℕ} (c:Perm (Fin n)) (p:P0 n)
 (d f:Fin (n+1)):
 ∑ i:Fin (n+1),∑ j:Fin (n+1),c6 n i.val d.val*c6 n j.val f.val *(u9 (R:=ℤ) c p).coeff i j=(2:ℤ)^(2*n-e3 p)*(hist c p d f:ℤ):=by
 have o:e3 p<=2*n:=by
  unfold e3
  calc (univ.filter (fun v:BV n=>p v=none)).card
   ≤ (univ:V7 (BV n)).card:=card_filter_le _ _
   _=2*n:=by simp
 have t:((2:ℤ)^e3 p)≠0:=(by positivity);apply mul_left_cancel₀ t
 have w:(2:ℤ)^e3 p *(∑ i:Fin (n+1),∑ j:Fin (n+1),c6 n i.val d.val*c6 n j.val f.val*(u9 (R:=ℤ) c p).coeff i j)=∑ i:Fin (n+1),∑ j:Fin (n+1),c6 n i.val d.val*c6 n j.val f.val *((ao c p (a8.X1:a8 (n+1) (n+1) ℤ) a8.X2).coeff i j):=by
  rw[mul_sum];refine L3 rfl fun i _=>?_;rw[mul_sum];refine L3 rfl fun j _=>?_;have q:=cs (R:=a8 (n+1) (n+1) ℤ) c p a8.X1 a8.X2;have m:((2:a8 (n+1) (n+1) ℤ)^e3 p)=(((2^e3 p:ℕ):a8 (n+1) (n+1) ℤ)):=by simp
  have l:(ao c p (a8.X1:a8 (n+1) (n+1) ℤ) a8.X2).coeff i j=(2:ℤ)^e3 p*(u9 (R:=ℤ) c p).coeff i j:=(by rw[q];change ((2:a8 (n+1) (n+1) ℤ)^e3 p*u9 (R:=ℤ) c p).coeff i j=_;rw[m,a8.l0];simp);rw[l];ring
 rw[w];simp_rw[ms,cast_id]
 have k:(∑ i:Fin (n+1),∑ j:Fin (n+1),c6 n i.val d.val*c6 n j.val f.val *(∑ r:Fin (n+1),∑ b:Fin (n+1),(hist c p r b:ℤ)*c6 n r.val i.val*c6 n b.val j.val))=∑ r:Fin (n+1),∑ b:Fin (n+1),(hist c p r b:ℤ) *(∑ i:Fin (n+1),c6 n i.val d.val*c6 n r.val i.val) *(∑ j:Fin (n+1),c6 n j.val f.val*c6 n b.val j.val):=by
  have h1:∀ i j:Fin (n+1),c6 n i.val d.val*c6 n j.val f.val *(∑ r:Fin (n+1),∑ b:Fin (n+1),(hist c p r b:ℤ)*c6 n r.val i.val*c6 n b.val j.val)=∑ r:Fin (n+1),∑ b:Fin (n+1),(hist c p r b:ℤ)*(c6 n i.val d.val*c6 n r.val i.val) *(c6 n j.val f.val*c6 n b.val j.val):=by
   intro i j;rw[mul_sum];refine L3 rfl fun r _=>?_;rw[mul_sum];refine L3 rfl fun b _=>by ring
  simp_rw[h1];have h2:∀ r b:Fin (n+1),(hist c p r b:ℤ) *(∑ i:Fin (n+1),c6 n i.val d.val*c6 n r.val i.val) *(∑ j:Fin (n+1),c6 n j.val f.val*c6 n b.val j.val)=∑ i:Fin (n+1),∑ j:Fin (n+1),(hist c p r b:ℤ)*(c6 n i.val d.val*c6 n r.val i.val) *(c6 n j.val f.val*c6 n b.val j.val):=(by intro r b;rw[mul_sum (a:=(hist c p r b:ℤ)),sum_mul];refine L3 rfl fun i _=>?_;rw[mul_sum]);simp_rw[h2]
  let e:(Fin (n+1)×Fin (n+1)×Fin (n+1)×Fin (n+1)) ≃
   (Fin (n+1)×Fin (n+1)×Fin (n+1)×Fin (n+1)):=
   {toFun:=fun⟨i,j,r,b⟩=>(r,b,i,j),invFun:=fun⟨r,b,i,j⟩=>(i,j,r,b),left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
  have z:=sum_equiv e
   (fun x=>(hist c p x.2.2.1 x.2.2.2:ℤ) *(c6 n x.1.val d.val*c6 n x.2.2.1.val x.1.val) *(c6 n x.2.1.val f.val*c6 n x.2.2.2.val x.2.1.val))
   (fun y=>(hist c p y.1 y.2.1:ℤ) *(c6 n y.2.2.1.val d.val*c6 n y.1.val y.2.2.1.val) *(c6 n y.2.2.2.val f.val*c6 n y.2.1.val y.2.2.2.val))
   (fun _=>rfl)
  simpa only[sum_prod_type] using z
 rw[k];simp_rw[nj];rw[Q4 d]
 . rw[Q4 f]
   . simp only[↓reduceIte];have u:(2:ℤ)^e3 p*(2:ℤ)^(2*n-e3 p)=(2:ℤ)^n*(2:ℤ)^n:=by rw[<-X6,<-X6,V3 o,two_mul]
     calc (hist c p d f:ℤ)*(2:ℤ)^n*(2:ℤ)^n
      =((2:ℤ)^n*(2:ℤ)^n)*(hist c p d f:ℤ):=by ring
      _=((2:ℤ)^e3 p*(2:ℤ)^(2*n-e3 p))*(hist c p d f:ℤ):=by rw[u]
      _=(2:ℤ)^e3 p*((2:ℤ)^(2*n-e3 p)*(hist c p d f:ℤ)):=by ring
   . intro b _ g;have hne':f≠b:=fun h=>g h.symm;simp[hne']
   . intro s;exact absurd (Y2 _) s
 . intro r _ g;refine L9 fun b _=>?_;have hne':d≠r:=fun h=>g h.symm;simp[hne']
 . intro s;exact absurd (Y2 _) s
lemma ct {n:ℕ} (a:Perm (Fin n)) (p:P0 n)
 (r b:Fin (n+1)):
 hist a p r b<=2^e3 p:=by
 rw[<-gc a p]
 calc hist a p r b<=∑ d:Fin (n+1),hist a p r d:=single_le_sum (f:=fun d=>hist a p r d) (fun _ _=>V5 _) (Y2 b)
  _<=∑ c:Fin (n+1),∑ d:Fin (n+1),hist a p c d:=single_le_sum (f:=fun c=>∑ d:Fin (n+1),hist a p c d) (fun _ _=>V5 _) (Y2 r)
lemma cu {B f M:ℕ}(p:f<=M)(x:ℤ):((((((2:ℤ)^f*x:ℤ):ZMod (2^(B+M))).val/2^f:ℕ):Z2 B))=(x:Z2 B):=by
 have n:0<2^(B+M):=(by positivity);haveI:NeZero (2^(B+M)):=⟨W7 n⟩;set q:ℕ:=((((2:ℤ)^f*x:ℤ):ZMod (2^(B+M)))).val;have i:((q:ℤ):ZMod (2^(B+M)))=((2:ℤ)^f*x:ℤ):=(by simp[q]);have d:((2^(B+M):ℕ):ℤ) ∣ (q:ℤ)-(2:ℤ)^f*x:=by rw[<-ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,i,sub_self]
 have b:(2:ℤ)^f ∣ ((2^(B+M):ℕ):ℤ):=by
  push_cast
  exact pow_dvd_pow (2:ℤ) (by omega)
 have e:(2:ℤ)^f ∣ (q:ℤ):=by obtain⟨k,o⟩:=dvd_trans b d;exact⟨x+k,by linarith⟩
 have a:2^f ∣ q:=by exact_mod_cast e
 have j:(q:ℤ)=(2:ℤ)^f*((q/2^f:ℕ):ℤ):=by
  have:=Nat.mul_div_cancel' a
  exact_mod_cast this.symm
 have c:((2^(B+M):ℕ):ℤ)=(2:ℤ)^f*(2:ℤ)^(B+(M-f)):=by
  push_cast
  rw[<-X6];congr 1;omega
 rw[j,c] at d;have g:(2:ℤ)^f*((q/2^f:ℕ):ℤ)-(2:ℤ)^f*x=(2:ℤ)^f*(((q/2^f:ℕ):ℤ)-x):=(by ring);rw[g] at d;have m:(2:ℤ)^(B+(M-f)) ∣ ((q/2^f:ℕ):ℤ)-x:=(mul_dvd_mul_iff_left (by positivity:(2:ℤ)^f≠0)).mp d
 have l:((2^B:ℕ):ℤ) ∣ ((q/2^f:ℕ):ℤ)-x:=by
  refine dvd_trans ?_ m
  push_cast
  exact pow_dvd_pow (2:ℤ) (by omega)
 have h:((((q/2^f:ℕ):ℤ)-x:ℤ):Z2 B)=0:=(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr l;rw[Int.cast_sub,sub_eq_zero] at h
 exact_mod_cast h
def w0 {n:ℕ}(a:Fin 3->Fin (2*n+1)->ℕ):a8 3 (2*n+1) ℤ:=⟨fun h d=>match h.val with
  | 0=>∑ s:Fin (2*n+1),(a 0 s:ℤ)*c6 (2*n) s.val d.val
  | 1=>
   if hd:1<=d.val then (∑ s:Fin (2*n+1),if s.val<2*n then ((n:ℤ)*(a 0 s:ℤ)-(a 1 s:ℤ))*c6 (2*n-1) s.val (d.val-1) else 0) -
    (∑ s:Fin (2*n+1),if 1<=s.val then (a 1 s:ℤ)*c6 (2*n-1) (s.val-1) (d.val-1) else 0)
   else 0
  | _=>
   if hd:2<=d.val then (∑ s:Fin (2*n+1),if s.val+2<=2*n then ((choose n 2:ℤ)*(a 0 s:ℤ)-((n-1:ℕ):ℤ)*(a 1 s:ℤ)+(a 2 s:ℤ)) *c6 (2*n-2) s.val (d.val-2) else 0) +(∑ s:Fin (2*n+1),if 1<=s.val/\s.val+1<=2*n then (-((n-1:ℕ):ℤ)*(a 1 s:ℤ)+2*(a 2 s:ℤ)) *c6 (2*n-2) (s.val-1) (d.val-2) else 0) +(∑ s:Fin (2*n+1),if 2<=s.val then (a 2 s:ℤ)*c6 (2*n-2) (s.val-2) (d.val-2) else 0)
   else 0⟩
lemma fj {D2:ℕ}{R:Type*}[CommRing R]:(a8.X1:a8 3 D2 R)^3=0:=by
 rw[show (a8.X1:a8 3 D2 R)^3=a8.o5 3 0 by
  simp[a8.X1,a8.cr]]
 exact a8.cl 3 0 (inl (le_refl 3))
lemma ow {A:Type*}[CommRing A]{x:A}(l:x^3=0)(a b:A)(k:ℕ):(a+x*b)^k=a^k+(k:A)*a^(k-1)*b*x+(choose k 2:A)*a^(k-2)*b^2*x^2:=by
 induction k with
 | zero=>simp
 | succ k ih=>
  rw[U4,ih]
  cases k with
  | zero=>
   have c:choose 1 2=0:=(by decide);rw[c];simp;ring
  | succ m=>
   have h:(m+1)-1=m:=(by omega);have g:(m+1+1)-1=m+1:=(by omega);have i:(m+1+1)-2=m:=(by omega);have j:choose (m+2) 2=choose (m+1) 2+(m+1):=by rw[Nat.choose_succ_succ,U9,Nat.add_comm]
   cases m with
   | zero=>
    have c:choose 1 2=0:=(by decide);have f:choose 2 2=1:=(by decide);rw[c,f];simp;ring
   | succ m'=>
    have e:m'+1+1-2=m':=(by omega);rw[h,g,i,j,e];have d:(a^(m'+1+1)+((m'+1+1:ℕ):A)*a^(m'+1)*b*x +(choose (m'+1+1) 2:A)*a^m'*b^2*x^2)*(a+x*b)=a^(m'+1+1+1)+((m'+1+1+1:ℕ):A)*a^(m'+1+1)*b*x +((choose (m'+1+1) 2+(m'+1+1):ℕ):A)*a^(m'+1)*b^2*x^2 +(choose (m'+1+1) 2:A)*a^m'*b^3*x^3:=(by push_cast;ring);rw[l,mul_zero,add_zero] at d;exact d
lemma dq {D2:ℕ}{R:Type*}[CommRing R](a b:a8 3 D2 R)(k:ℕ):(a+a8.X1*b)^k=a^k+(k:a8 3 D2 R)*a^(k-1)*b*a8.X1 +(choose k 2:a8 3 D2 R)*a^(k-2)*b^2*a8.X1^2:=ow fj a b k
lemma kw {D2:ℕ}{R:Type*}[CommRing R](r:ℕ):(1+(a8.X1:a8 3 D2 R))^r=1+(r:a8 3 D2 R)*a8.X1+(choose r 2:a8 3 D2 R)*a8.X1^2:=by have h:=dq (1:a8 3 D2 R) 1 r;simpa using h
lemma bk {D2:ℕ}{R:Type*}[CommRing R](l r:ℕ)(h:Fin 3)(d:Fin D2):((a8.X2:a8 3 D2 R)^l*(1+a8.X1)^r).coeff h d=if d.val=l then (choose r h.val:R) else 0:=by
 rw[kw];have a:(a8.X2:a8 3 D2 R)^l*1=a8.o5 0 l:=(by rw[mul_one,<-a8.t5 0 l,pow_zero,one_mul]);have c:(a8.X2:a8 3 D2 R)^l*((r:a8 3 D2 R)*a8.X1)=(r:a8 3 D2 R)*a8.o5 1 l:=(by rw[<-a8.t5 1 l,pow_one];ring);have b:(a8.X2:a8 3 D2 R)^l*((choose r 2:a8 3 D2 R)*a8.X1^2)=(choose r 2:a8 3 D2 R)*a8.o5 2 l:=(by rw[<-a8.t5 2 l];ring);rw[mul_add,mul_add,a,c,b,a8.coeff_add,a8.coeff_add,a8.l0,a8.l0]
 fin_cases h<;>simp[a8.o5,U8,U9]
lemma nx (n r:ℕ)(h:r<=n):((choose (n-r) 2:ℕ):ℤ)=(choose n 2:ℤ)-((n-1:ℕ):ℤ)*(r:ℤ)+(choose r 2:ℤ):=by
 have a:∀ m:ℕ,2*((choose m 2:ℕ):ℤ)=(m:ℤ)*((m:ℤ)-1):=by
  intro m;have:=Nat.choose_two_right m;have b:2*choose m 2=m*(m-1):=by rw[this];exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
  cases m with
  | zero=>simp
  | succ m=>
   have:(2*choose (m+1) 2:ℕ)=(m+1)*m:=b;have c:((2*choose (m+1) 2:ℕ):ℤ)=(((m+1)*m:ℕ):ℤ):=by exact_mod_cast this
   push_cast at c ⊢
   linarith
 have b:=a (n-r);have e:=a n;have i:=a r;have d:((n-r:ℕ):ℤ)=(n:ℤ)-(r:ℤ):=Nat.cast_sub h;rw[d] at b
 cases n with
 | zero=>
  have g:r=0:=(by omega);subst g;simp
 | succ j=>
  have f:((j+1-1:ℕ):ℤ)=(j:ℤ):=(by simp);rw[f]
  push_cast at b e
  linarith
lemma mf (n r:ℕ)(f:r<=n):((r:ℤ)*((n-r:ℕ):ℤ))=((n-1:ℕ):ℤ)*(r:ℤ)-2*(choose r 2:ℤ):=by
 have g:2*((choose r 2:ℕ):ℤ)=(r:ℤ)*((r:ℤ)-1):=by
  have:=Nat.choose_two_right r;have e:2*choose r 2=r*(r-1):=by rw[this];exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  cases r with
  | zero=>simp
  | succ r=>
   have a:((2*choose (r+1) 2:ℕ):ℤ)=(((r+1)*r:ℕ):ℤ):=by exact_mod_cast e
   push_cast at a ⊢
   linarith
 have b:((n-r:ℕ):ℤ)=(n:ℤ)-(r:ℤ):=Nat.cast_sub f;rw[b]
 cases n with
 | zero=>
  have d:r=0:=(by omega);subst d;simp
 | succ h=>
  have c:((h+1-1:ℕ):ℤ)=(h:ℤ):=(by simp);rw[c]
  push_cast
  linarith
lemma s8 {D2:ℕ} {R:Type*} [CommRing R] {deg s:ℕ} (b:s<=deg)
 (i:deg<D2) (h:Fin 3) (d:Fin D2):
 (((1-(a8.X2:a8 3 D2 R))^s*(1+a8.X2)^(deg-s))).coeff h d=if h.val=0 then (c6 deg s d.val:R) else 0:=by
 rw[<-go b (a8.X2:a8 3 D2 R),a8.z8];by_cases f:d.val<deg+1
 . rw[Q4 ⟨d.val,f⟩]
   . rw[a8.s4,show (a8.X2:a8 3 D2 R)^d.val=a8.o5 0 d.val by
      simp[a8.X2,a8.cr]]
     simp[a8.o5]
   . intro k _ e
     rw[a8.s4,show (a8.X2:a8 3 D2 R)^k.val=a8.o5 0 k.val by
      simp[a8.X2,a8.cr]]
     have:d.val≠k.val:=fun j=>e (L6 j.symm);simp[a8.o5,this]
   . intro g;exact absurd (Y2 _) g
 . have c:c6 deg s d.val=0:=coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (ep b) (by omega));have a:(if h.val=0 then (c6 deg s d.val:R) else 0)=0:=(by simp[c]);rw[a];refine L9 fun k _=>?_
   rw[a8.s4,show (a8.X2:a8 3 D2 R)^k.val=a8.o5 0 k.val by
    simp[a8.X2,a8.cr]]
   have:d.val≠k.val:=(by have:=k.isLt;omega);simp[a8.o5,this]
lemma eu {D1 D2:ℕ} {R:Type*} [CommRing R] (f:a8 D1 D2 R) (a b:ℕ)
 (i:Fin D1) (j:Fin D2):
 (f*a8.o5 a b).coeff i j=if d:a<=i.val then if g:b<=j.val then f.coeff ⟨i.val-a,by omega⟩ ⟨j.val-b,by omega⟩ else 0
  else 0:=by
 rw[a8.coeff_mul];by_cases d:a<=i.val
 . by_cases g:b<=j.val
   . simp only[d,g,↓reduceDIte];have ha':a<D1:=(by have:=i.isLt;omega);have hb':b<D2:=(by have:=j.isLt;omega);rw[Q4 ⟨i.val-a,by omega⟩]
     . rw[Q4 ⟨a,ha'⟩]
       . rw[Q4 ⟨j.val-b,by omega⟩]
         . rw[Q4 ⟨b,hb'⟩]
           . simp[a8.o5,Nat.sub_add_cancel d,Nat.sub_add_cancel g]
           . intro j2 _ c;have:j2.val≠b:=fun h=>c (L6 h);simp[a8.o5,this]
           . intro e;exact absurd (Y2 _) e
         . intro j1 _ c;refine L9 fun j2 _=>?_
           split_ifs with k
           . simp only[a8.o5]
             split_ifs with l
             . exfalso;apply c;exact L6 (by dsimp only;omega)
             . simp
           . rfl
         . intro e;exact absurd (Y2 _) e
       . intro i2 _ c;refine L9 fun j1 _=>L9 fun j2 _=>?_;have:i2.val≠a:=fun h=>c (L6 h);simp[a8.o5,this]
       . intro e;exact absurd (Y2 _) e
     . intro i1 _ c;refine L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_
       split_ifs with k
       . simp only[a8.o5]
         split_ifs with l
         . exfalso;apply c;exact L6 (by dsimp only;omega)
         . simp
       . rfl
     . intro e;exact absurd (Y2 _) e
   . simp only[d,g,↓reduceDIte];refine L9 fun i1 _=>L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_
     split_ifs with k
     . simp only[a8.o5]
       split_ifs with l
       . exfalso;apply g;omega
       . simp
     . rfl
 . simp only[d,↓reduceDIte];refine L9 fun i1 _=>L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_
   split_ifs with k
   . simp only[a8.o5]
     split_ifs with l
     . exfalso;apply d;omega
     . simp
   . rfl
lemma kb {n:ℕ}(r b:Fin (n+1))(h:Fin 3)(d:Fin (2*n+1)):let U:a8 3 (2*n+1) ℤ:=a8.X2*(1+a8.X1)
 let V:a8 3 (2*n+1) ℤ:=a8.X2
 ((1-U)^r.val*(1+U)^(n-r.val)*(1-V)^b.val*(1+V)^(n-b.val)).coeff h d=
 let s:=r.val+b.val
 match h.val with
 | 0=>c6 (2*n) s d.val
 | 1=>
  if 1<=d.val then (if s<2*n then ((n:ℤ)-(r.val:ℤ))*c6 (2*n-1) s (d.val-1) else 0) -
   (if 1<=s then (r.val:ℤ)*c6 (2*n-1) (s-1) (d.val-1) else 0)
  else 0
 | _=>
  if 2<=d.val then (if s+2<=2*n then ((choose n 2:ℤ)-((n-1:ℕ):ℤ)*(r.val:ℤ)+(choose r.val 2:ℤ)) *c6 (2*n-2) s (d.val-2) else 0) +(if 1<=s/\s+1<=2*n then (-((n-1:ℕ):ℤ)*(r.val:ℤ)+2*(choose r.val 2:ℤ)) *c6 (2*n-2) (s-1) (d.val-2) else 0) +(if 2<=s then (choose r.val 2:ℤ)*c6 (2*n-2) (s-2) (d.val-2) else 0)
  else 0:=by
 intro U V;set A:a8 3 (2*n+1) ℤ:=1-a8.X2;set B:a8 3 (2*n+1) ℤ:=1+a8.X2;have a0:1-U=A+a8.X1*(-a8.X2):=(by dsimp only[U,A];ring);have h7:1+U=B+a8.X1*a8.X2:=(by dsimp only[U,B];ring);have v1:(a8.X1:a8 3 (2*n+1) ℤ)^3=0:=fj;have x:=dq A (-a8.X2) r.val;have u:=dq B a8.X2 (n-r.val)
 have w:(1-U)^r.val*(1+U)^(n-r.val)*(1-V)^b.val*(1+V)^(n-b.val)=(A^(r.val+b.val)*B^(2*n-(r.val+b.val))) +(((n-r.val:ℕ):a8 3 (2*n+1) ℤ)*(A^(r.val+b.val)*B^(2*n-1-(r.val+b.val))) -
   (r.val:a8 3 (2*n+1) ℤ)*(A^(r.val+b.val-1)*B^(2*n-(r.val+b.val)))) *a8.o5 1 1 +
  (((choose (n-r.val) 2:ℕ):a8 3 (2*n+1) ℤ)*(A^(r.val+b.val)*B^(2*n-2-(r.val+b.val)))-((r.val:a8 3 (2*n+1) ℤ)*((n-r.val:ℕ):a8 3 (2*n+1) ℤ)) *(A^(r.val+b.val-1)*B^(2*n-1-(r.val+b.val))) +((choose r.val 2:ℕ):a8 3 (2*n+1) ℤ)*(A^(r.val+b.val-2)*B^(2*n-(r.val+b.val)))) *a8.o5 2 2:=by
  rw[a0,h7,x,u];have y2:1-V=A:=rfl;have a1:1+V=B:=rfl;rw[y2,a1];have e:r.val<=n:=U1 r.isLt;have h3:b.val<=n:=U1 b.isLt;have h4:(a8.X1:a8 3 (2*n+1) ℤ)*a8.X2=a8.o5 1 1:=(by rw[<-a8.t5 1 1,pow_one,pow_one]);have z:(a8.X1:a8 3 (2*n+1) ℤ)^2*a8.X2^2=a8.o5 2 2:=(by rw[<-a8.t5 2 2]);have v2:A^r.val*A^b.val=A^(r.val+b.val):=(X6 A r.val b.val).symm;have a2:B^(n-r.val)*B^(n-b.val)=B^(2*n-(r.val+b.val)):=by rw[<-X6];congr 1;omega
  have v0:((n-r.val:ℕ):a8 3 (2*n+1) ℤ)*(B^(n-r.val-1)*B^(n-b.val))=((n-r.val:ℕ):a8 3 (2*n+1) ℤ)*B^(2*n-1-(r.val+b.val)):=by
   by_cases g:n-r.val=0
   . simp[g]
   . rw[<-X6];congr 2;omega
  have y1:(r.val:a8 3 (2*n+1) ℤ)*(A^(r.val-1)*A^b.val)=(r.val:a8 3 (2*n+1) ℤ)*A^(r.val+b.val-1):=by
   by_cases i:r.val=0
   . simp[i]
   . rw[<-X6];congr 2;omega
  have x0:((choose (n-r.val) 2:ℕ):a8 3 (2*n+1) ℤ)*(B^(n-r.val-2)*B^(n-b.val))=((choose (n-r.val) 2:ℕ):a8 3 (2*n+1) ℤ)*B^(2*n-2-(r.val+b.val)):=by
   by_cases g:n-r.val<2
   . rw[Nat.choose_eq_zero_of_lt g];simp
   . rw[<-X6];congr 2;omega
  have h6:((choose r.val 2:ℕ):a8 3 (2*n+1) ℤ)*(A^(r.val-2)*A^b.val)=((choose r.val 2:ℕ):a8 3 (2*n+1) ℤ)*A^(r.val+b.val-2):=by
   by_cases x1:r.val<2
   . rw[Nat.choose_eq_zero_of_lt x1];simp
   . rw[<-X6];congr 2;omega
  have v:((r.val:a8 3 (2*n+1) ℤ)*((n-r.val:ℕ):a8 3 (2*n+1) ℤ)) *((A^(r.val-1)*A^b.val)*(B^(n-r.val-1)*B^(n-b.val)))=((r.val:a8 3 (2*n+1) ℤ)*((n-r.val:ℕ):a8 3 (2*n+1) ℤ)) *(A^(r.val+b.val-1)*B^(2*n-1-(r.val+b.val))):=by
   by_cases i:r.val=0
   . simp[i]
   . by_cases g:n-r.val=0
     . simp[g]
     . rw[<-X6,<-X6];congr 2<;>[congr 1;congr 1]<;>omega
  have j:(A^r.val+(r.val:a8 3 (2*n+1) ℤ)*A^(r.val-1)*(-a8.X2)*a8.X1 +(choose r.val 2:a8 3 (2*n+1) ℤ)*A^(r.val-2)*(-a8.X2)^2*a8.X1^2) *(B^(n-r.val)+((n-r.val:ℕ):a8 3 (2*n+1) ℤ)*B^(n-r.val-1)*a8.X2*a8.X1 +(choose (n-r.val) 2:a8 3 (2*n+1) ℤ)*B^(n-r.val-2)*a8.X2^2*a8.X1^2) *A^b.val*B^(n-b.val)=(A^r.val*A^b.val)*(B^(n-r.val)*B^(n-b.val)) +(((n-r.val:ℕ):a8 3 (2*n+1) ℤ)*(B^(n-r.val-1)*B^(n-b.val))*(A^r.val*A^b.val) -
    (r.val:a8 3 (2*n+1) ℤ)*(A^(r.val-1)*A^b.val)*(B^(n-r.val)*B^(n-b.val))) *(a8.X1*a8.X2) +
   (((choose (n-r.val) 2:ℕ):a8 3 (2*n+1) ℤ)*(B^(n-r.val-2)*B^(n-b.val))*(A^r.val*A^b.val)-((r.val:a8 3 (2*n+1) ℤ)*((n-r.val:ℕ):a8 3 (2*n+1) ℤ)) *((A^(r.val-1)*A^b.val)*(B^(n-r.val-1)*B^(n-b.val))) +((choose r.val 2:ℕ):a8 3 (2*n+1) ℤ)*(A^(r.val-2)*A^b.val)*(B^(n-r.val)*B^(n-b.val))) *(a8.X1^2*a8.X2^2) +
   (a8.X1^3)*((r.val:a8 3 (2*n+1) ℤ)*(choose (n-r.val) 2:a8 3 (2*n+1) ℤ) *A^(r.val-1)*A^b.val*B^(n-r.val-2)*B^(n-b.val)*(-a8.X2)*a8.X2^2 +(choose r.val 2:a8 3 (2*n+1) ℤ)*((n-r.val:ℕ):a8 3 (2*n+1) ℤ) *A^(r.val-2)*A^b.val*B^(n-r.val-1)*B^(n-b.val)*a8.X2^3 +(choose r.val 2:a8 3 (2*n+1) ℤ)*(choose (n-r.val) 2:a8 3 (2*n+1) ℤ) *A^(r.val-2)*A^b.val*B^(n-r.val-2)*B^(n-b.val)*a8.X2^4*a8.X1):=by
   ring
  rw[j,v1,zero_mul,add_zero,h4,z,v2,a2,v0,y1,x0,h6,v];ring
 rw[w];have e:r.val<=n:=U1 r.isLt;have h3:b.val<=n:=U1 b.isLt;have k:=s8 (D2:=2*n+1) (R:=ℤ) (deg:=2*n) (s:=r.val+b.val) (by omega) (by omega)
 fin_cases h
 . simp only[zero_eta,val_zero,a8.coeff_add,eu,show ¬ (1<=(0:ℕ)) by omega,show ¬ (2<=(0:ℕ)) by omega,↓reduceDIte,add_zero];simpa[A,B] using k ⟨0,by omega⟩ d
 . simp only[mk_one,val_one,a8.coeff_add,eu,show (1<=(1:ℕ)) by omega,show ¬ (2<=(1:ℕ)) by omega,↓reduceDIte,add_zero];have y:(A^(r.val+b.val)*B^(2*n-(r.val+b.val))).coeff 1 d=0:=by dsimp only[A,B];rw[show (1:Fin 3)=⟨1,by omega⟩ from rfl,k ⟨1,by omega⟩ d];simp
   rw[y,zero_add];by_cases f:1<=d.val
   . rw[L7 f,Q2 f];rw[a8.coeff_sub,a8.l0,a8.l0];congr 1
     . by_cases a:r.val+b.val<2*n
       . rw[Q2 a,s8 (by omega) (by omega)];simp[Nat.cast_sub e]
       . have x2:r.val=n:=(by omega);rw[Q3 a,x2];simp
     . by_cases a:1<=r.val+b.val
       . have c:2*n-(r.val+b.val)=(2*n-1)-(r.val+b.val-1):=(by omega);rw[Q2 a,c,s8 (by omega) (by omega)];simp
       . have i:r.val=0:=(by omega);rw[Q3 a,i];simp
   . rw[Q8 f,Q3 f]
 . simp only[val_two,a8.coeff_add,eu,show (1<=(2:ℕ)) by omega,show (2<=(2:ℕ)) by omega,↓reduceDIte];have h5:(A^(r.val+b.val)*B^(2*n-(r.val+b.val))).coeff ⟨2,by omega⟩ d=0:=by dsimp only[A,B];rw[k ⟨2,by omega⟩ d];simp
   rw[h5,zero_add]
   have t:(if hb:1<=d.val then (((n-r.val:ℕ):a8 3 (2*n+1) ℤ)*(A^(r.val+b.val)*B^(2*n-1-(r.val+b.val))) -
      (r.val:a8 3 (2*n+1) ℤ)*(A^(r.val+b.val-1)*B^(2*n-(r.val+b.val)))).coeff
       ⟨2-1,by omega⟩ ⟨d.val-1,by omega⟩
    else 0)=0:=by
    split_ifs with a5
    . rw[a8.coeff_sub,a8.l0,a8.l0]
      have h1:((n-r.val:ℕ):ℤ)*(A^(r.val+b.val)*B^(2*n-1-(r.val+b.val))).coeff ⟨1,by omega⟩ ⟨d.val-1,by omega⟩=0:=by
       by_cases a:r.val+b.val<=2*n-1
       . rw[s8 a (by omega)];simp
       . have:n-r.val=0:=(by omega);simp[this]
      have h2:(r.val:ℤ)*(A^(r.val+b.val-1)*B^(2*n-(r.val+b.val))).coeff ⟨1,by omega⟩ ⟨d.val-1,by omega⟩=0:=by
       by_cases a:1<=r.val+b.val
       . have:2*n-(r.val+b.val)=(2*n-1)-(r.val+b.val-1):=(by omega);rw[this,s8 (by omega) (by omega)];simp
       . have:r.val=0:=(by omega);simp[this]
      rw[show (⟨2-1,_⟩:Fin 3)=⟨1,by omega⟩ from rfl,h1,h2,sub_self]
    . rfl
   rw[t,zero_add];by_cases f:2<=d.val
   . rw[L7 f,Q2 f];rw[a8.coeff_sub,a8.l0,mul_assoc,a8.l0,a8.l0,a8.l0]
     have m:((choose (n-r.val) 2:ℕ):ℤ) *(A^(r.val+b.val)*B^(2*n-2-(r.val+b.val))).coeff ⟨2-2,by omega⟩ ⟨d.val-2,by omega⟩=if r.val+b.val+2<=2*n then ((choose n 2:ℤ)-((n-1:ℕ):ℤ)*(r.val:ℤ)+(choose r.val 2:ℤ)) *c6 (2*n-2) (r.val+b.val) (d.val-2)
      else 0:=by
      by_cases a:r.val+b.val+2<=2*n
      . rw[Q2 a,s8 (by omega) (by omega)];simp[nx n r.val e]
      . have l:n-r.val<2:=(by omega);rw[Q3 a,Nat.choose_eq_zero_of_lt l];simp
     have o:-((r.val:ℤ)*(((n-r.val:ℕ):ℤ) *(A^(r.val+b.val-1)*B^(2*n-1-(r.val+b.val))).coeff ⟨2-2,by omega⟩ ⟨d.val-2,by omega⟩))=if 1<=r.val+b.val/\r.val+b.val+1<=2*n then (-((n-1:ℕ):ℤ)*(r.val:ℤ)+2*(choose r.val 2:ℤ)) *c6 (2*n-2) (r.val+b.val-1) (d.val-2)
      else 0:=by
      by_cases a:1<=r.val+b.val/\r.val+b.val+1<=2*n
      . rw[Q2 a];have c:2*n-1-(r.val+b.val)=(2*n-2)-(r.val+b.val-1):=(by omega);rw[c,s8 (by omega) (by omega)];simp only[Nat.sub_self,↓reduceIte,cast_id];have h8:=mf n r.val e
        calc -((r.val:ℤ)*(((n-r.val:ℕ):ℤ)*c6 (2*n-2) (r.val+b.val-1) (d.val-2)))
         =-(((r.val:ℤ)*((n-r.val:ℕ):ℤ))*c6 (2*n-2) (r.val+b.val-1) (d.val-2)):=by ring
         _=-((((n-1:ℕ):ℤ)*(r.val:ℤ)-2*(choose r.val 2:ℤ)) *c6 (2*n-2) (r.val+b.val-1) (d.val-2)):=by rw[h8]
         _=(-((n-1:ℕ):ℤ)*(r.val:ℤ)+2*(choose r.val 2:ℤ)) *c6 (2*n-2) (r.val+b.val-1) (d.val-2):=by ring
      . rw[Q3 a];have q:r.val=0\/n-r.val=0:=by omega
        rcases q with h0|h0<;>simp[h0]
     have p:((choose r.val 2:ℕ):ℤ) *(A^(r.val+b.val-2)*B^(2*n-(r.val+b.val))).coeff ⟨2-2,by omega⟩ ⟨d.val-2,by omega⟩=if 2<=r.val+b.val then (choose r.val 2:ℤ)*c6 (2*n-2) (r.val+b.val-2) (d.val-2) else 0:=by
      by_cases a:2<=r.val+b.val
      . rw[Q2 a];have c:2*n-(r.val+b.val)=(2*n-2)-(r.val+b.val-2):=(by omega);rw[c,s8 (by omega) (by omega)];simp
      . have l:r.val<2:=(by omega);rw[Q3 a,Nat.choose_eq_zero_of_lt l];simp
     rw[sub_eq_add_neg,m,o,p]
   . rw[Q8 f,Q3 f]
lemma x4 {n:ℕ}(H:Fin (n+1)->Fin (n+1)->ℕ)(f:Fin (2*n+1)->ℤ)(h:ℕ):(∑ s:Fin (2*n+1),(profile H h s:ℤ)*f s)=∑ r:Fin (n+1),∑ b:Fin (n+1),(H r b:ℤ)*(choose r.val h:ℤ)*f ⟨r.val+b.val,by have:=r.isLt;have:=b.isLt;omega⟩:=by
 unfold profile;simp_rw[Nat.cast_sum,sum_mul];rw[X9];refine L3 rfl fun r _=>?_;rw[X9];refine L3 rfl fun b _=>?_;have c:r.val+b.val<2*n+1:=(by have:=r.isLt;have:=b.isLt;omega);rw[Q4 ⟨r.val+b.val,c⟩]
 . simp[mul_comm,mul_left_comm,mul_assoc]
 . intro s _ a;have:r.val+b.val≠s.val:=fun e=>a (L6 e.symm);simp[this]
 . intro d;exact absurd (Y2 _) d
lemma fq {n:ℕ}(a:Perm (Fin n))(p:P0 n):ao a p (a8.X2*(1+a8.X1):a8 3 (2*n+1) ℤ) a8.X2=w0 (fun h s=>profile (hist a p) h.val s):=by
 apply a8.ext;intro h d;unfold ao;rw[a8.z8];simp_rw[a8.z8,mul_assoc,a8.l0];have e:∀ r b:Fin (n+1),((1-(a8.X2*(1+a8.X1):a8 3 (2*n+1) ℤ))^r.val *((1+a8.X2*(1+a8.X1))^(n-r.val) *((1-a8.X2)^b.val*(1+a8.X2)^(n-b.val)))).coeff h d=((1-(a8.X2*(1+a8.X1):a8 3 (2*n+1) ℤ))^r.val *(1+a8.X2*(1+a8.X1))^(n-r.val) *(1-a8.X2)^b.val*(1+a8.X2)^(n-b.val)).coeff h d:=(by intro r b;congr 1;ring);simp_rw[e,kb]
 fin_cases h
 . simp only[w0,zero_eta,val_zero];rw[x4 (hist a p) (fun s=>c6 (2*n) s.val d.val) 0];refine L3 rfl fun r _=>L3 rfl fun b _=>?_;simp[U8]
 . simp only[w0,mk_one,val_zero,val_one];by_cases c:1<=d.val
   . simp only[c,↓reduceDIte,↓reduceIte]
     have f:(∑ s:Fin (2*n+1),if s.val<2*n then ((n:ℤ)*(profile (hist a p) 0 s:ℤ)-(profile (hist a p) 1 s:ℤ)) *c6 (2*n-1) s.val (d.val-1)
      else 0)=
      (n:ℤ)*(∑ s:Fin (2*n+1),(profile (hist a p) 0 s:ℤ) *(if s.val<2*n then c6 (2*n-1) s.val (d.val-1) else 0)) -
      (∑ s:Fin (2*n+1),(profile (hist a p) 1 s:ℤ) *(if s.val<2*n then c6 (2*n-1) s.val (d.val-1) else 0)):=by
      rw[mul_sum,<-sum_sub_distrib];refine L3 rfl fun s _=>by split_ifs<;>ring
     have g:(∑ s:Fin (2*n+1),if 1<=s.val then (profile (hist a p) 1 s:ℤ)*c6 (2*n-1) (s.val-1) (d.val-1)
      else 0)=
      ∑ s:Fin (2*n+1),(profile (hist a p) 1 s:ℤ) *(if 1<=s.val then c6 (2*n-1) (s.val-1) (d.val-1) else 0):=by
      refine L3 rfl fun s _=>by split_ifs<;>ring
     rw[f,g,x4,x4,x4];simp_rw[mul_sum,<-sum_sub_distrib];refine L3 rfl fun r _=>L3 rfl fun b _=>?_;simp only[U8,U9,Nat.cast_one,mul_one];split_ifs<;>ring
   . simp[c]
 . simp only[w0,val_zero,val_one,val_two];by_cases c:2<=d.val
   . simp only[c,↓reduceDIte,↓reduceIte]
     have k:(∑ s:Fin (2*n+1),if s.val+2<=2*n then ((choose n 2:ℤ)*(profile (hist a p) 0 s:ℤ) -
        ((n-1:ℕ):ℤ)*(profile (hist a p) 1 s:ℤ)+(profile (hist a p) 2 s:ℤ)) *c6 (2*n-2) s.val (d.val-2)
      else 0)=
      (choose n 2:ℤ)*(∑ s:Fin (2*n+1),(profile (hist a p) 0 s:ℤ) *(if s.val+2<=2*n then c6 (2*n-2) s.val (d.val-2) else 0)) -
      ((n-1:ℕ):ℤ)*(∑ s:Fin (2*n+1),(profile (hist a p) 1 s:ℤ) *(if s.val+2<=2*n then c6 (2*n-2) s.val (d.val-2) else 0)) +
      (∑ s:Fin (2*n+1),(profile (hist a p) 2 s:ℤ) *(if s.val+2<=2*n then c6 (2*n-2) s.val (d.val-2) else 0)):=by
      rw[mul_sum,mul_sum,<-sum_sub_distrib,<-Z4];refine L3 rfl fun s _=>by split_ifs<;>ring
     have j:(∑ s:Fin (2*n+1),if 1<=s.val/\s.val+1<=2*n then (-((n-1:ℕ):ℤ)*(profile (hist a p) 1 s:ℤ)+2*(profile (hist a p) 2 s:ℤ)) *c6 (2*n-2) (s.val-1) (d.val-2)
      else 0)=
      -((n-1:ℕ):ℤ)*(∑ s:Fin (2*n+1),(profile (hist a p) 1 s:ℤ) *(if 1<=s.val/\s.val+1<=2*n then c6 (2*n-2) (s.val-1) (d.val-2) else 0)) +
      2*(∑ s:Fin (2*n+1),(profile (hist a p) 2 s:ℤ) *(if 1<=s.val/\s.val+1<=2*n then c6 (2*n-2) (s.val-1) (d.val-2) else 0)):=by
      rw[mul_sum,mul_sum,<-Z4];refine L3 rfl fun s _=>by split_ifs<;>ring
     have i:(∑ s:Fin (2*n+1),if 2<=s.val then (profile (hist a p) 2 s:ℤ)*c6 (2*n-2) (s.val-2) (d.val-2)
      else 0)=
      ∑ s:Fin (2*n+1),(profile (hist a p) 2 s:ℤ) *(if 2<=s.val then c6 (2*n-2) (s.val-2) (d.val-2) else 0):=by
      refine L3 rfl fun s _=>by split_ifs<;>ring
     rw[k,j,i,x4,x4,x4,x4,x4,x4];simp_rw[mul_sum,<-sum_sub_distrib,<-Z4];refine L3 rfl fun r _=>L3 rfl fun b _=>?_;simp only[U8,U9,Nat.cast_one,mul_one];split_ifs<;>ring
   . simp[c]
def j6 {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):ℕ:=((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=1)).card
def m8 {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):ℕ:=((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=-1)).card
def je {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):ℕ:=((f6 a p).filter (fun c=>p9 c=l/\n5 c=r)).card
lemma dz {n:ℕ}(e:Perm (Fin n))(p:P0 n)(l r:ℕ):j6 e p l r+m8 e p l r=je e p l r:=by
 unfold j6 m8 je;rw[<-card_union_of_disjoint]
 . congr 1;ext c;simp only[X4,L4];constructor
   . rintro (⟨b,a,d,_⟩|⟨b,a,d,_⟩)<;>exact⟨b,a,d⟩
   . rintro⟨b,a,d⟩
     rcases ml e p c with f|f
     . exact inl ⟨b,a,d,f⟩
     . exact inr ⟨b,a,d,f⟩
 . rw[X8];intro c g h;have i:=(L4.mp g).2.2.2;have j:=(L4.mp h).2.2.2;omega
lemma jt {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):je a p l r<=2*n:=le_trans (card_filter_le _ _) (gb a p)
def e9 {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):ℤ:=(m8 a p l r:ℤ)-(j6 a p l r:ℤ) +if l %2=0/\r %2=0 then (j6 a p (l/2) (r/2):ℤ) else 0
lemma dg {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):-(2*n:ℤ)<=e9 a p l r/\e9 a p l r<=2*n:=by
 unfold e9;have j:j6 a p l r+m8 a p l r<=2*n:=(by rw[dz];exact jt a p l r);have f:j6 a p (l/2) (r/2)<=2*n:=by have:=dz a p (l/2) (r/2);have:=jt a p (l/2) (r/2);omega
 have k:m8 a p l r+(if l %2=0/\r %2=0 then j6 a p (l/2) (r/2) else 0)<=2*n:=by
  split_ifs with m
  . by_cases i:l=0
    . subst i;have g:m8 a p 0 r=0:=(by unfold m8;rw[U3,W8];intro c e h;have:=(w9 a p c e).1;omega);rw[g];omega
    . have b:Disjoint
       ((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=-1))
       ((f6 a p).filter (fun c=>p9 c=l/2/\n5 c=r/2/\m4 a p c=1)):=by
       rw[X8];intro c h1' h2';have q:=(L4.mp h1').2.1;have s:=(L4.mp h2').2.1;omega
      have o:=card_union_of_disjoint b
      have d:((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=-1))∪((f6 a p).filter (fun c=>p9 c=l/2/\n5 c=r/2/\m4 a p c=1))⊆
       f6 a p:=Finset.union_subset (filter_subset _ _) (filter_subset _ _)
      have e:=le_trans (card_le_card d) (gb a p);unfold m8 j6;omega
  . omega
 split_ifs at k ⊢<;>omega
def n7 (l:ℕ):List ℕ:=if l %2=1 then [l/2,l/2+1] else [l/2]
def c4 (l:ℕ):List ℕ:=if l %2=1 then [l/2,l/2+1]
 else if l %4=0 then [l/2]
 else [l/2-1,l/2,l/2+1]
lemma ej {l r b:ℕ}(e:l=r+b)(d:r<=b+1)(c:b<=r+1):r∈n7 l:=by
 unfold n7
 split_ifs with a<;>simp<;>omega
lemma y6 {l r:ℕ}(a:r∈n7 l):r∈c4 l:=by unfold n7 at a;unfold c4;split_ifs at a ⊢<;>simp_all
lemma jf {l r:ℕ}(e:1<=l)(a:r∈n7 l):2*r∈c4 (2*l):=by
 unfold n7 at a;unfold c4;have c:¬ (2*l %2=1):=(by omega);simp only[c,↓reduceIte]
 split_ifs at a with d
 . have b:¬ (2*l %4=0):=(by omega);simp only[b,↓reduceIte,mem_cons,not_mem_nil,or_false] at a ⊢
   rcases a with rfl|rfl<;>omega
 . have b:2*l %4=0:=(by omega);simp only[b,↓reduceIte,List.mem_singleton] at a ⊢;omega
lemma s9 {n:ℕ} (d:Perm (Fin n))
 (p:P0 n) {l r:ℕ} (a:r∉n7 l):
 j6 d p l r=0:=by
 unfold j6;rw[U3,W8];intro c f h;have e:=w9 d p c f;have b:l=r+s3 c:=(by unfold p9 at h;omega);exact a (ej b (by rw[<-h.2.1];exact e.2.2.1) (by rw[<-h.2.1];exact e.2.2.2))
lemma ai {n:ℕ} (d:Perm (Fin n))
 (p:P0 n) {l r:ℕ} (a:r∉n7 l):
 m8 d p l r=0:=by
 unfold m8;rw[U3,W8];intro c f h;have e:=w9 d p c f;have b:l=r+s3 c:=(by unfold p9 at h;omega);exact a (ej b (by rw[<-h.2.1];exact e.2.2.1) (by rw[<-h.2.1];exact e.2.2.2))
lemma oo {R:Type*} [CommRing R] {n:ℕ}
 (a:Perm (Fin n)) (p:P0 n) (u v:R):
 (∏ c∈f6 a p,(1+(m4 a p c:R)*u^n5 c*v^s3 c))=
 ∏ l∈Icc 1 (2*n),∏ r∈(n7 l).toFinset,(1+u^r*v^(l-r))^j6 a p l r *(1-u^r*v^(l-r))^m8 a p l r:=by
 let m:V7 (BV n)->ℕ×ℕ:=fun c=>(p9 c,n5 c);let S:V7 (ℕ×ℕ):=(Icc 1 (2*n)).biUnion fun l=>(n7 l).toFinset.image fun r=>(l,r);have o:∀ c∈f6 a p,m c∈S:=(by intro c b;have s:=w9 a p c b;rw[mem_biUnion];refine⟨p9 c,J4.mpr ⟨s.1,s.2.1⟩,?_⟩;rw[X5];exact⟨n5 c,K3.mpr (ej rfl s.2.2.1 s.2.2.2),rfl⟩);rw[<-Finset.prod_fiberwise_of_maps_to o]
 have j:∀ f:ℕ×ℕ->R,(∏ x∈S,f x)=∏ l∈Icc 1 (2*n),∏ r∈(n7 l).toFinset,f (l,r):=by
  intro f;rw[prod_biUnion]
  . refine M4 rfl fun l _=>?_;exact prod_image fun r1 _ r2 _ h=>(Prod.mk.inj h).2
  . intro l1 _ l2 _ h3;change Disjoint _ _;rw[X8];intro x z h0;obtain⟨r1,_,rfl⟩:=X5.mp z;obtain⟨r2,_,k⟩:=X5.mp h0;exact h3 (Prod.mk.inj k).1.symm
 rw[j];refine M4 rfl fun l _=>M4 rfl fun r _=>?_;set t:=(f6 a p).filter (fun c=>m c=(l,r))
 have e:t=((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=1))∪((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=-1)):=by
  ext c;simp only[t,m,J0,X4,L4];constructor
  . rintro⟨b,d,g⟩
    rcases ml a p c with i|i
    . exact inl ⟨b,d,g,i⟩
    . exact inr ⟨b,d,g,i⟩
  . rintro (⟨b,d,g,_⟩|⟨b,d,g,_⟩)<;>exact⟨b,d,g⟩
 have q:Disjoint
  ((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=1))
  ((f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=-1)):=by
  rw[X8];intro c w k;have s1:=(L4.mp w).2.2.2;have s2:=(L4.mp k).2.2.2;omega
 rw[e,Finset.prod_union q];congr 1
 . have w:∀ c∈(f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=1),(1+(m4 a p c:R)*u^n5 c*v^s3 c)=1+u^r*v^(l-r):=by intro c b;obtain⟨_,d,g,i⟩:=L4.mp b;have y:s3 c=l-r:=(by unfold p9 at d;omega);rw[g,y,i];simp
   rw[M4 rfl w,prod_const];rfl
 . have k:∀ c∈(f6 a p).filter (fun c=>p9 c=l/\n5 c=r/\m4 a p c=-1),(1+(m4 a p c:R)*u^n5 c*v^s3 c)=1-u^r*v^(l-r):=by intro c b;obtain⟨_,d,g,i⟩:=L4.mp b;have y:s3 c=l-r:=(by unfold p9 at d;omega);rw[g,y,i];simp[sub_eq_add_neg]
   rw[M4 rfl k,prod_const];rfl
lemma gd {D1 D2:ℕ} {R:Type*} [CommRing R] {n:ℕ}
 (a:Perm (Fin n)) (p:P0 n)
 (u v:a8 D1 D2 R)
 (g:∀ l r,1≤l->r∈n7 l->∀ i j,i.val+j.val=0->(u^r*v^(l-r)).coeff i j=0)
 (h6:∀ l r,1≤l->l≤2*n->r∈n7 l->2*n<2*l->(u^r*v^(l-r))^2=0):
 (∏ c∈f6 a p,(1+(m4 a p c:a8 D1 D2 R)*u^n5 c*v^s3 c))=
 ∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r)) (e9 a p l r):=by
 rw[oo]
 have m:∀ l r,1≤l->r∈c4 l->∀ i j,i.val+j.val=0->(u^r*v^(l-r)).coeff i j=0:=by
  intro l r e d i j a6;by_cases hp:r∈n7 l
  . exact g l r e hp i j a6
  . have w:l %2=0/\r %2=0:=(by unfold n7 at hp;unfold c4 at d;split_ifs at hp d<;>simp_all<;>omega);have s:r/2∈n7 (l/2):=(by unfold n7 at hp ⊢;unfold c4 at d;split_ifs at hp d ⊢<;>simp_all<;>omega);have h5:u^r*v^(l-r)=(u^(r/2)*v^(l/2-r/2))^2:=by have a5:u^r*v^(l-r)=u^(2*(r/2))*v^(2*(l/2-r/2)):=(by congr 1<;>congr 1<;>omega);rw[a5,mul_pow,<-pow_mul,<-pow_mul,mul_comm 2,mul_comm 2]
    rw[h5];exact a8.dp _ (g (l/2) (r/2) (by omega) s) 2 i j (by omega)
 have q:(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r)) (e9 a p l r))=(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r)) (m8 a p l r:ℤ)) *(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r)) (-(j6 a p l r:ℤ))) *(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r))
    (if l %2=0/\r %2=0 then (j6 a p (l/2) (r/2):ℤ) else 0)):=by
  rw[<-M3,<-M3];refine M4 rfl fun l e=>?_;rw[<-M3,<-M3];refine M4 rfl fun r d=>?_;have hz:=m l r (J4.mp e).1 (K3.mp d);unfold e9;rw[sub_eq_add_neg,a8.fp _ hz,a8.fp _ hz]
 rw[q]
 have hA:(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r)) (m8 a p l r:ℤ))=∏ l∈Icc 1 (2*n),∏ r∈(n7 l).toFinset,(1-u^r*v^(l-r))^m8 a p l r:=by
  refine M4 rfl fun l _=>?_;rw[<-prod_subset (s₁:=(n7 l).toFinset)]
  . refine M4 rfl fun r _=>?_;simp[a8.c8]
  . intro r d;exact K3.mpr (y6 (K3.mp d))
  . intro r _ b;rw[ai a p (fun h=>b (K3.mpr h))];simp[a8.c8]
 have hB:(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r)) (-(j6 a p l r:ℤ)))=∏ l∈Icc 1 (2*n),∏ r∈(n7 l).toFinset,(a8.c8 (u^r*v^(l-r)) (-1))^j6 a p l r:=by
  refine M4 rfl fun l e=>?_;rw[<-prod_subset (s₁:=(n7 l).toFinset)]
  . refine M4 rfl fun r _=>?_;by_cases h0:j6 a p l r=0
    . simp[h0,a8.c8]
    . have x0:¬ (0<=-(j6 a p l r:ℤ)):=(by omega);simp[a8.c8,x0,h0]
  . intro r d;exact K3.mpr (y6 (K3.mp d))
  . intro r _ b;rw[s9 a p (fun h=>b (K3.mpr h))];simp[a8.c8]
 have hC:(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (u^r*v^(l-r))
    (if l %2=0/\r %2=0 then (j6 a p (l/2) (r/2):ℤ) else 0))=
  ∏ l∈Icc 1 (2*n),∏ r∈(n7 l).toFinset,(a8.c8 ((u^r*v^(l-r))^2) 1)^j6 a p l r:=by
  let S1:V7 (ℕ×ℕ):=(Icc 1 (2*n)).biUnion fun l=>(c4 l).toFinset.image fun r=>(l,r);let S2:V7 (ℕ×ℕ):=(Icc 1 (2*n)).biUnion fun l=>(n7 l).toFinset.image fun r=>(l,r)
  have a3:∀ f:ℕ×ℕ->a8 D1 D2 R,(∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,f (l,r))=∏ x∈S1,f x:=by
   intro f;rw[prod_biUnion]
   . refine M4 rfl fun l _=>(prod_image fun r1 _ r2 _ h=>(Prod.mk.inj h).2).symm
   . intro l1 _ l2 _ h8;change Disjoint _ _;rw[X8];intro x h7 o;obtain⟨r1,_,rfl⟩:=X5.mp h7;obtain⟨r2,_,h2⟩:=X5.mp o;exact h8 (Prod.mk.inj h2).1.symm
  have y1:∀ f:ℕ×ℕ->a8 D1 D2 R,(∏ l∈Icc 1 (2*n),∏ r∈(n7 l).toFinset,f (l,r))=∏ x∈S2,f x:=by
   intro f;rw[prod_biUnion]
   . refine M4 rfl fun l _=>(prod_image fun r1 _ r2 _ h=>(Prod.mk.inj h).2).symm
   . intro l1 _ l2 _ h8;change Disjoint _ _;rw[X8];intro x h7 o;obtain⟨r1,_,rfl⟩:=X5.mp h7;obtain⟨r2,_,h2⟩:=X5.mp o;exact h8 (Prod.mk.inj h2).1.symm
  rw[a3 (fun x=>a8.c8 (u^x.2*v^(x.1-x.2)) (if x.1 %2=0/\x.2 %2=0 then (j6 a p (x.1/2) (x.2/2):ℤ) else 0)),y1 (fun x=>(a8.c8 ((u^x.2*v^(x.1-x.2))^2) 1)^j6 a p x.1 x.2)];let S2small:=S2.filter (fun x=>2*x.1<=2*n);have t:(∏ x∈S2,(a8.c8 ((u^x.2*v^(x.1-x.2))^2) 1)^j6 a p x.1 x.2)=∏ x∈S2small,(a8.c8 ((u^x.2*v^(x.1-x.2))^2) 1)^j6 a p x.1 x.2:=by symm;refine prod_subset (filter_subset _ _) fun x k b=>?_;simp only[S2small,L4] at b;have a4:2*n<2*x.1:=(by have v2:¬ (2*x.1<=2*n):=fun h=>b ⟨k,h⟩;omega);obtain⟨l,e,hx'⟩:=mem_biUnion.mp k;obtain⟨r,d,rfl⟩:=X5.mp hx';have hl':=J4.mp e;rw[h6 l r hl'.1 hl'.2 (K3.mp d) a4];simp[a8.c8]
  rw[t];let S1img:=S2small.image (fun x=>(2*x.1,2*x.2));have h4:S1img⊆S1:=by intro y hy;obtain⟨⟨l,r⟩,k,rfl⟩:=X5.mp hy;obtain⟨o,v2⟩:=L4.mp k;obtain⟨l',hl',hx'⟩:=mem_biUnion.mp o;obtain⟨r',hr',z⟩:=X5.mp hx';obtain⟨rfl,rfl⟩:=Prod.mk.inj z;have a1:=J4.mp hl';rw[mem_biUnion];refine⟨2*l',J4.mpr ⟨by omega,v2⟩,?_⟩;rw[X5];exact⟨2*r',K3.mpr (jf a1.1 (K3.mp hr')),rfl⟩
  rw[<-prod_subset h4]
  . rw[prod_image]
    . refine M4 rfl fun x k=>?_;have h1:(2*x.1) %2=0/\(2*x.2) %2=0:=⟨by omega,by omega⟩;simp only[h1,and_self,↓reduceIte,Nat.mul_div_right _ (by omega:0<2)];have h5:u^(2*x.2)*v^(2*x.1-2*x.2)=(u^x.2*v^(x.1-x.2))^2:=by have hs:2*x.1-2*x.2=2*(x.1-x.2):=(by omega);rw[hs,mul_pow,<-pow_mul,<-pow_mul,mul_comm 2,mul_comm 2]
      rw[h5];simp[a8.c8]
    . intro x1 _ x2 _ z;obtain⟨h1,h2⟩:=Prod.mk.inj z;exact Prod.ext (by omega) (by omega)
  . intro y hy b;by_cases w:y.1 %2=0/\y.2 %2=0
    . by_cases s:y.2/2∈n7 (y.1/2)
      . exfalso;apply b;obtain⟨l,e,hy'⟩:=mem_biUnion.mp hy;obtain⟨r,d,rfl⟩:=X5.mp hy';have hl':=J4.mp e;rw[X5];refine⟨(l/2,r/2),L4.mpr ⟨?_,by omega⟩,Prod.ext (by omega) (by omega)⟩;rw[mem_biUnion];refine⟨l/2,J4.mpr ⟨by omega,by omega⟩,?_⟩;rw[X5];exact⟨r/2,K3.mpr s,rfl⟩
      . rw[Q2 w,s9 a p s];simp[a8.c8]
    . rw[Q3 w,a8.iz]
 rw[hA,hB,hC];rw[<-M3,<-M3];refine M4 rfl fun l e=>?_;rw[<-M3,<-M3];refine M4 rfl fun r d=>?_;have hz:=g l r (J4.mp e).1 (K3.mp d);have a0:=a8.jp (u^r*v^(l-r)) hz;rw[a0,mul_pow];ring
lemma gf {D2:ℕ} {R:Type*} [CommRing R] {l:ℕ} (hl:1<=l) (u:l<D2)
 {f g:a8 3 D2 R}
 (h5:∀ h:Fin 3,f.coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0)
 (h4:∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->f.coeff h d=0)
 (o:∀ h:Fin 3,g.coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0)
 (x2:∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->g.coeff h d=0):
 (∀ h:Fin 3,(f*g).coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0) ∧
 (∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->(f*g).coeff h d=0) ∧
 (∀ h:Fin 3,(f*g).coeff h ⟨l,u⟩=f.coeff h ⟨l,u⟩+g.coeff h ⟨l,u⟩):=by
 have c:0<D2:=by omega
 have j:∀(h:Fin 3) (d:Fin D2),d.val≤l->(f*g).coeff h d=(if d.val=0 then (if h.val=0 then 1 else 0)
    else if d.val<l then 0
    else f.coeff h d+g.coeff h d):=by
  intro h d y1;rw[a8.coeff_mul]
  have p:∀ a j2:Fin D2,(∑ i1:Fin 3,∑ i2:Fin 3,if i1.val+i2.val=h.val/\a.val+j2.val=d.val then f.coeff i1 a*g.coeff i2 j2 else 0)=if a.val+j2.val=d.val then if a.val=0 then g.coeff h j2
    else if j2.val=0 then f.coeff h a
    else 0
   else 0:=by
   intro a j2;by_cases hj:a.val+j2.val=d.val
   . simp only[hj,and_true,↓reduceIte];by_cases k:a.val=0
     . rw[Q2 k];have z:a=⟨0,c⟩:=L6 k;rw[z];rw[Q4 ⟨0,by omega⟩]
       . rw[Q4 h]
         . simp[h5]
         . intro i2 _ b;have:i2.val≠h.val:=fun h'=>b (L6 h');simp[this]
         . intro i;exact absurd (Y2 _) i
       . intro i1 _ b;refine L9 fun i2 _=>?_;have v1:i1.val≠0:=fun h'=>b (L6 h');simp[h5,v1]
       . intro i;exact absurd (Y2 _) i
     . rw[Q3 k];by_cases n:j2.val=0
       . rw[Q2 n];have r:j2=⟨0,c⟩:=L6 n;rw[r];rw[Q4 h]
         . rw[Q4 ⟨0,by omega⟩]
           . simp[o]
           . intro i2 _ b;have q:i2.val≠0:=fun h'=>b (L6 h');simp[o,q]
           . intro i;exact absurd (Y2 _) i
         . intro i1 _ b;refine L9 fun i2 _=>?_
           split_ifs with hi
           . have q:i2.val≠0:=fun h'=>b (L6 (by omega));simp[o,q]
           . rfl
         . intro i;exact absurd (Y2 _) i
       . rw[Q3 n];refine L9 fun i1 _=>L9 fun i2 _=>?_;split_ifs
         . rw[h4 i1 a (by omega) (by omega),zero_mul]
         . rfl
   . simp[hj]
  have h3:(∑ i1:Fin 3,∑ i2:Fin 3,∑ a:Fin D2,∑ j2:Fin D2,if i1.val+i2.val=h.val/\a.val+j2.val=d.val then f.coeff i1 a*g.coeff i2 j2 else 0)=∑ a:Fin D2,∑ j2:Fin D2,∑ i1:Fin 3,∑ i2:Fin 3,if i1.val+i2.val=h.val/\a.val+j2.val=d.val then f.coeff i1 a*g.coeff i2 j2 else 0:=by
   let e:(Fin 3×Fin 3×Fin D2×Fin D2) ≃ (Fin D2×Fin D2×Fin 3×Fin 3):=
    {toFun:=fun⟨i1,i2,a,j2⟩=>(a,j2,i1,i2),invFun:=fun⟨a,j2,i1,i2⟩=>(i1,i2,a,j2),left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
   have x0:=sum_equiv e
    (fun x=>if x.1.val+x.2.1.val=h.val/\x.2.2.1.val+x.2.2.2.val=d.val then f.coeff x.1 x.2.2.1*g.coeff x.2.1 x.2.2.2 else 0)
    (fun y=>if y.2.2.1.val+y.2.2.2.val=h.val/\y.1.val+y.2.1.val=d.val then f.coeff y.2.2.1 y.1*g.coeff y.2.2.2 y.2.1 else 0)
    (fun _=>rfl)
   simpa only[sum_prod_type] using x0
  rw[h3];simp_rw[p];by_cases m:d.val=0
  . rw[Q2 m];rw[Q4 ⟨0,c⟩]
    . rw[Q4 ⟨0,c⟩]
      . simp[m,o]
      . intro j2 _ b;have:j2.val≠0:=fun h'=>b (L6 h');simp[m,this]
      . intro i;exact absurd (Y2 _) i
    . intro a _ b;refine L9 fun j2 _=>?_;have:a.val+j2.val≠d.val:=(by have:a.val≠0:=fun h'=>b (L6 h');omega);simp[this]
    . intro i;exact absurd (Y2 _) i
  . rw[Q3 m]
    have v:(∑ a:Fin D2,∑ j2:Fin D2,if a.val+j2.val=d.val then if a.val=0 then g.coeff h j2 else if j2.val=0 then f.coeff h a else 0
     else 0)=g.coeff h d+f.coeff h d:=by
     have t:(⟨0,c⟩:Fin D2)≠d:=fun h'=>m (Q6 Fin.val h').symm;rw[<-add_sum_erase _ _ (Y2 ⟨0,c⟩)];have s:d∈(univ:V7 (Fin D2)).erase ⟨0,c⟩:=mem_erase.mpr ⟨t.symm,Y2 d⟩;rw[<-add_sum_erase _ _ s]
     have w:(∑ a∈((univ:V7 (Fin D2)).erase ⟨0,c⟩).erase d,∑ j2:Fin D2,if a.val+j2.val=d.val then if a.val=0 then g.coeff h j2 else if j2.val=0 then f.coeff h a else 0
       else 0)=0:=by
      refine L9 fun a k=>L9 fun j2 _=>?_;rw[mem_erase,mem_erase] at k;have h1:a.val≠d.val:=fun h'=>k.1 (L6 h');have h2:a.val≠0:=fun h'=>k.2.1 (L6 h');by_cases hs:a.val+j2.val=d.val
      . by_cases n:j2.val=0
        . exfalso;apply h1;omega
        . simp[hs,h2,n]
      . simp[hs]
     rw[w,add_zero];congr 1
     . rw[Q4 d]
       . simp
       . intro j2 _ b;have:j2.val≠d.val:=fun h'=>b (L6 h');simp[this]
       . intro i;exact absurd (Y2 _) i
     . rw[Q4 ⟨0,c⟩]
       . simp[m]
       . intro j2 _ b;have h9:d.val+j2.val≠d.val:=(by have:j2.val≠0:=fun h'=>b (L6 h');omega);rw[Q3 h9]
       . intro i;exact absurd (Y2 _) i
    rw[v,add_comm]
    split_ifs with h6
    . rw[h4 h d (by omega) h6,x2 h d (by omega) h6,add_zero]
    . rfl
 refine⟨fun h=>?_,fun h d h1 h2=>?_,fun h=>?_⟩
 . have:=j h ⟨0,c⟩ (V5 l);simpa using this
 . have:=j h d (by omega);have b:d.val≠0:=(by omega);simpa[b,h2] using this
 . have:=j h ⟨l,u⟩ (le_refl l);have b:l≠0:=(by omega);have h7:¬ (l<l):=lt_irrefl l;simpa[b,h7] using this
lemma gr {D2:ℕ} {R:Type*} [CommRing R] {l:ℕ} (g:1<=l) (b:l<D2)
 {f:a8 3 D2 R}
 (e:∀ h:Fin 3,f.coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0)
 (c:∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->f.coeff h d=0)
 (k:ℕ):
 (∀ h:Fin 3,(f^k).coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0) ∧
 (∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->(f^k).coeff h d=0) ∧
 (∀ h:Fin 3,(f^k).coeff h ⟨l,b⟩=(k:R)*f.coeff h ⟨l,b⟩):=by
 induction k with
 | zero=>refine⟨fun h=>by simp[a8.coeff_one],fun h d a _=>by simp[a8.coeff_one,W7 a],fun h=>by simp[a8.coeff_one,show l≠0 by omega]⟩
 | succ k ih=>rw[U4];obtain⟨a,j,i⟩:=gf g b ih.1 ih.2.1 e c;refine⟨a,j,fun h=>?_⟩;rw[i h,ih.2.2 h,cast_succ,add_mul,one_mul]
lemma x5 {i:Type*} {D2:ℕ} {R:Type*} [CommRing R] {l:ℕ}
 (j:1<=l) (g:l<D2) (s:V7 i) (F:i->a8 3 D2 R)
 (c:∀ a∈s,∀ h:Fin 3,(F a).coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0)
 (b:∀ a∈s,∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->(F a).coeff h d=0):
 (∀ h:Fin 3,(∏ a∈s,F a).coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0) ∧
 (∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->(∏ a∈s,F a).coeff h d=0) ∧
 (∀ h:Fin 3,(∏ a∈s,F a).coeff h ⟨l,g⟩=∑ a∈s,(F a).coeff h ⟨l,g⟩):=by
 classical
 induction s using induction_on with
 | empty=>refine⟨fun h=>by simp[a8.coeff_one],fun h d f _=>by simp[a8.coeff_one,W7 f],fun h=>by simp[a8.coeff_one,show l≠0 by omega]⟩
 | @insert a s ha ih=>
  rw[prod_insert ha]
  have ih':=ih (fun x e=>c x (mem_insert_of_mem e))
   (fun x e=>b x (mem_insert_of_mem e))
  obtain⟨f,m,k⟩:=gf j g (c a (mem_insert_self a s))
   (b a (mem_insert_self a s)) ih'.1 ih'.2.1
  refine⟨f,m,fun h=>?_⟩;rw[k h,ih'.2.2 h,sum_insert ha]
lemma m6 {D2:ℕ} {R:Type*} [CommRing R] {l l' r:ℕ}
 (v:1<=l) (z:l<=l') (o:l<D2) (c:ℤ):
 let f:a8 3 D2 R:=a8.X2^l'*(1+a8.X1)^r;let g:=a8.c8 f c
 (∀ h:Fin 3,g.coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0) ∧
 (∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->g.coeff h d=0) ∧
 (∀ h:Fin 3,g.coeff h ⟨l,o⟩=if l'=l then -(c:R)*(choose r h.val:R) else 0):=by
 intro f g;have a:∀(h:Fin 3) (d:Fin D2),f.coeff h d=if d.val=l' then (choose r h.val:R) else 0:=bk l' r
 have b:∀ k:ℕ,1≤k->∀(h:Fin 3) (d:Fin D2),d.val<k*l'->(f^k).coeff h d=0:=by
  intro k
  induction k with
  | zero=>intro j;omega
  | succ k ih=>
   intro _ h d y
   cases k with
   | zero=>rw[pow_one,a];have:d.val≠l':=(by omega);simp[this]
   | succ k'=>
    rw[U4,a8.coeff_mul];refine L9 fun i1 _=>L9 fun i2 _=>L9 fun j1 _=>L9 fun j2 _=>?_
    split_ifs with s
    . by_cases w:j2.val=l'
      . rw[ih (by omega) i1 j1 (by nlinarith),zero_mul]
      . rw[a i2 j2,Q3 w,mul_zero]
    . rfl
 have e:(∀ h:Fin 3,(1-f).coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0)/\(∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->(1-f).coeff h d=0)/\(∀ h:Fin 3,(1-f).coeff h ⟨l,o⟩=if l'=l then -(choose r h.val:R) else 0):=by
  refine⟨fun h=>?_,fun h d q u=>?_,fun h=>?_⟩
  . rw[a8.coeff_sub,a8.coeff_one,a];have:(0:ℕ)≠l':=(by omega);simp[this]
  . rw[a8.coeff_sub,a8.coeff_one,a];have h1':d.val≠0:=(by omega);have h2':d.val≠l':=(by omega);simp[h1',h2']
  . rw[a8.coeff_sub,a8.coeff_one,a];have j:l≠0:=(by omega);by_cases m:l'=l
    . subst m;simp[j]
    . have i:l≠l':=fun h'=>m h'.symm;simp[j,m,i]
 have n:(∀ h:Fin 3,(a8.r5 f).coeff h ⟨0,by omega⟩=if h.val=0 then 1 else 0)/\(∀(h:Fin 3) (d:Fin D2),0<d.val->d.val<l->(a8.r5 f).coeff h d=0)/\(∀ h:Fin 3,(a8.r5 f).coeff h ⟨l,o⟩=if l'=l then (choose r h.val:R) else 0):=by
  unfold a8.r5;refine⟨fun h=>?_,fun h d q u=>?_,fun h=>?_⟩
  . rw[a8.z8,Q4 0]
    . simp[a8.coeff_one]
    . intro k _ i;exact b k (by omega) h ⟨0,by omega⟩ (Nat.mul_pos (by omega) (by omega))
    . intro j;exfalso;apply j;exact mem_range.mpr (by omega)
  . rw[a8.z8];refine L9 fun k _=>?_
    cases k with
    | zero=>simp[a8.coeff_one,W7 q]
    | succ k'=>exact b (k'+1) (by omega) h d (by nlinarith)
  . rw[a8.z8];have t:1∈Finset.range (3+D2):=mem_range.mpr (by omega);rw[Q4 1]
    . rw[pow_one,a];by_cases m:l'=l
      . subst m;simp
      . have i:l≠l':=fun h'=>m h'.symm;simp[m,i]
    . intro k _ i
      cases k with
      | zero=>simp[a8.coeff_one,show l≠0 by omega]
      | succ k'=>
       have x:2<=k'+1:=(by omega);exact b (k'+1) (by omega) h ⟨l,o⟩ (by nlinarith)
    . intro j;exact absurd t j
 dsimp only[g,a8.c8];by_cases s:0<=c
 . rw[Q2 s];obtain⟨a1,a2,a3⟩:=gr v o e.1 e.2.1 c.toNat;refine⟨a1,a2,fun h=>?_⟩;rw[a3 h,e.2.2 h];have p:(c.toNat:R)=(c:R):=(by rw[<-Int.cast_natCast,Int.toNat_of_nonneg s]);rw[p];split_ifs<;>ring
 . rw[Q3 s];obtain⟨a1,a2,a3⟩:=gr v o n.1 n.2.1 (-c).toNat;refine⟨a1,a2,fun h=>?_⟩;rw[a3 h,n.2.2 h];have p:((-c).toNat:R)=-(c:R):=by rw[<-Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_neg]
   rw[p];split_ifs<;>ring
lemma nk {R:Type*}[CommRing R](m c d:R):let a:=c+d
 let b:=(m:R)*c+(m+1)*d
 b-m*a=d/\a-(b-m*a)=c:=by
 intro a b;constructor<;>ring
lemma mg {R:Type*}[CommRing R](m:ℕ)(q:1<=m)(a d b:R):let f:=a+d+b
 let l:=((m-1:ℕ):R)*a+(m:R)*d+((m+1:ℕ):R)*b;let n:=(choose (m-1) 2:R)*a+(choose m 2:R)*d+(choose (m+1) 2:R)*b;let c:=l-(m:R)*f;let cm1':=n-(choose m 2:R)*f-(m:R)*c;let cp1':=cm1'+c;let c0':=f-cm1'-cp1'
 cm1'=a/\c0'=d/\cp1'=b:=by
 intro f l n c cm1' cp1' c0'
 have p:((m-1:ℕ):R)=(m:R)-1:=by
  cases m with
  | zero=>omega
  | succ r=>simp
 have i:(choose (m-1) 2:R)=(choose m 2:R)-((m:R)-1):=by
  cases m with
  | zero=>omega
  | succ r=>
   have h:choose (r+1) 2=choose r 2+r:=(by rw[Nat.choose_succ_succ,U9,Nat.add_comm]);have h':(choose (r+1) 2:R)=(choose r 2:R)+(r:R):=(by rw[h,Nat.cast_add]);simp only[Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one];rw[h'];ring
 have j:(choose (m+1) 2:R)=(choose m 2:R)+(m:R):=by have h:choose (m+1) 2=choose m 2+m:=(by rw[Nat.choose_succ_succ,U9,Nat.add_comm]);rw[h,Nat.cast_add]
 have g:c=b-a:=(by dsimp only[c,l,f];rw[p];push_cast;ring);have e:cm1'=a:=(by dsimp only[cm1',n,f];rw[g,i,j];ring);have k:cp1'=b:=(by dsimp only[cp1'];rw[e,g];ring);have o:c0'=d:=(by dsimp only[c0',f];rw[e,k];ring);exact⟨e,o,k⟩
lemma li {B:ℕ}(q:2<=B)(c:ℤ)(p:-(2^(B-1):ℤ)<c/\c<2^(B-1)):let z:Z2 B:=(c:Z2 B)
 z.val.testBit (B-1)=decide (c<0) ∧
 (if c<0 then (-z).val else z.val)=c.natAbs ∧
 c.natAbs<2^(B-1):=by
 have i:0<2^B:=(by positivity);haveI:NeZero (2^B):=⟨W7 i⟩
 have m:2^B=2^(B-1)+2^(B-1):=by
  have:B=(B-1)+1:=by omega
  conv_lhs=>rw[this,U4,mul_two]
 intro z;have g:(c.natAbs:ℤ)<(2^(B-1):ℤ):=(by omega);have e:c.natAbs<2^(B-1):=(by exact_mod_cast g);by_cases d:c<0
 . have b:z.val=2^B-c.natAbs:=by
    have a:c=-((c.natAbs:ℕ):ℤ):=by omega
    have j:((2^B-c.natAbs:ℕ):Z2 B)=z:=by
     have l:c.natAbs<=2^B:=(by omega);rw[Nat.cast_sub l]
     conv_rhs=>dsimp only[z];rw[a,Int.cast_neg,Int.cast_natCast]
     simp
    rw[<-j,val_natCast,L8 (by omega)]
   have f:z.val.testBit (B-1)=true:=by
    rw[Nat.testBit_eq_decide_div_mod_eq];have k:z.val/2^(B-1)=1:=by rw[b];have o:2^(B-1)<=2^B-c.natAbs:=(by omega);have n:2^B-c.natAbs<2*2^(B-1):=(by omega);exact Nat.div_eq_of_lt_le (by simpa using o) n
    simp[k]
   have h:(-z).val=c.natAbs:=by have a:-c=(c.natAbs:ℤ):=(by omega);have:-z=((c.natAbs:ℕ):Z2 B):=(by conv_lhs=>dsimp only[z];rw[<-Int.cast_neg,a,Int.cast_natCast]);rw[this,val_natCast,L8 (by omega)]
   exact⟨by simp[f,d],by simp[d,h],e⟩
 . have b:z.val=c.natAbs:=by have a:c=(c.natAbs:ℤ):=(by omega);have:z=((c.natAbs:ℕ):Z2 B):=(by conv_lhs=>dsimp only[z];rw[a,Int.cast_natCast]);rw[this,val_natCast,L8 (by omega)]
   have f:z.val.testBit (B-1)=false:=(by rw[b,Nat.testBit_eq_false_of_lt e]);exact⟨by simp[f,d],by simp[d,b],e⟩
end KrawAndAlgebra
lemma kc {D1 D2:ℕ} {R:Type*} [CommRing R] (C A:a8 D1 D2 R)
 (i:Fin D1) (j:Fin D2):
 (C*A).coeff i j=∑ i1:Fin D1,∑ j1:Fin D2,if h:i1.val<=i.val/\j1.val<=j.val then C.coeff i1 j1*A.coeff ⟨i.val-i1.val,by omega⟩ ⟨j.val-j1.val,by omega⟩
   else 0:=by
 rw[a8.coeff_mul];refine L3 rfl fun i1 _=>?_;have b:(∑ i2:Fin D1,∑ j1:Fin D2,∑ j2:Fin D2,if i1.val+i2.val=i.val/\j1.val+j2.val=j.val then C.coeff i1 j1*A.coeff i2 j2 else 0)=∑ j1:Fin D2,∑ i2:Fin D1,∑ j2:Fin D2,if i1.val+i2.val=i.val/\j1.val+j2.val=j.val then C.coeff i1 j1*A.coeff i2 j2 else 0:=X9;rw[b];refine L3 rfl fun j1 _=>?_;by_cases h:i1.val<=i.val/\j1.val<=j.val
 . rw[L7 h];have e:i.val-i1.val<D1:=(by have:=i.isLt;omega);have d:j.val-j1.val<D2:=(by have:=j.isLt;omega);rw[Q4 ⟨i.val-i1.val,e⟩]
   . rw[Q4 ⟨j.val-j1.val,d⟩]
     . simp[V3 h.1,V3 h.2]
     . intro j2 _ a;have:j1.val+j2.val≠j.val:=(by have:j2.val≠j.val-j1.val:=fun f=>a (L6 f);omega);simp[this]
     . intro c;exact absurd (Y2 _) c
   . intro i2 _ a;refine L9 fun j2 _=>?_;have:i1.val+i2.val≠i.val:=(by have:i2.val≠i.val-i1.val:=fun f=>a (L6 f);omega);simp[this]
   . intro c;exact absurd (Y2 _) c
 . rw[Q8 h];refine L9 fun i2 _=>L9 fun j2 _=>?_;have:¬ (i1.val+i2.val=i.val/\j1.val+j2.val=j.val):=(by omega);simp[this]
noncomputable section MainAssembly
lemma x6 {n:ℕ}(p:P0 n):e3 p<=2*n:=by
 unfold e3
 calc (univ.filter (fun v:BV n=>p v=none)).card
  ≤ (univ:V7 (BV n)).card:=card_filter_le _ _
  _=2*n:=by simp
def fr (n:ℕ)(h:Fin 3)(d:Fin (2*n+1))(k:Fin 3)(s:Fin (2*n+1)):ℤ:=match h.val,k.val with
 | 0,0=>c6 (2*n) s.val d.val
 | 1,0=>if 1<=d.val/\s.val<2*n then (n:ℤ)*c6 (2*n-1) s.val (d.val-1) else 0
 | 1,1=>
  if 1<=d.val then -(if s.val<2*n then c6 (2*n-1) s.val (d.val-1) else 0) -
   (if 1<=s.val then c6 (2*n-1) (s.val-1) (d.val-1) else 0)
  else 0
 | 2,0=>if 2<=d.val/\s.val+2<=2*n then (choose n 2:ℤ)*c6 (2*n-2) s.val (d.val-2) else 0
 | 2,1=>
  if 2<=d.val then -((n-1:ℕ):ℤ)*(if s.val+2<=2*n then c6 (2*n-2) s.val (d.val-2) else 0) -
   ((n-1:ℕ):ℤ)*(if 1<=s.val/\s.val+1<=2*n then c6 (2*n-2) (s.val-1) (d.val-2) else 0)
  else 0
 | 2,2=>
  if 2<=d.val then (if s.val+2<=2*n then c6 (2*n-2) s.val (d.val-2) else 0) +2*(if 1<=s.val/\s.val+1<=2*n then c6 (2*n-2) (s.val-1) (d.val-2) else 0) +(if 2<=s.val then c6 (2*n-2) (s.val-2) (d.val-2) else 0)
  else 0
 | _,_=>0
lemma fh {n:ℕ} (a:Fin 3->Fin (2*n+1)->ℕ)
 (h:Fin 3) (d:Fin (2*n+1)):
 (w0 a).coeff h d=(∑ s:Fin (2*n+1),fr n h d 0 s*(a 0 s:ℤ)) +(∑ s:Fin (2*n+1),fr n h d 1 s*(a 1 s:ℤ)) +(∑ s:Fin (2*n+1),fr n h d 2 s*(a 2 s:ℤ)):=by
 fin_cases h
 . simp only[w0,fr,zero_eta,val_zero,val_one,val_two,zero_mul,Finset.sum_const_zero,add_zero];refine L3 rfl fun s _=>by ring
 . simp only[w0,fr,mk_one,val_zero,val_one,val_two,zero_mul,Finset.sum_const_zero,add_zero];by_cases b:1<=d.val
   . simp only[b,Q0,↓reduceDIte,↓reduceIte];rw[<-sum_sub_distrib,<-Z4];refine L3 rfl fun s _=>by split_ifs<;>ring
   . simp[b]
 . simp only[w0,fr,val_zero,val_one,val_two];by_cases b:2<=d.val
   . simp only[b,Q0,↓reduceDIte,↓reduceIte];rw[<-Z4,<-Z4,<-Z4,<-Z4];refine L3 rfl fun s _=>by split_ifs<;>ring
   . simp[b]
def z9 {R:Type*} [CommRing R] {n:ℕ}
 (a:Perm (Fin n)) (p:P0 n):a8 3 (2*n+1) R:=
 ∏ c∈f6 a p,(1+(m4 a p c:a8 3 (2*n+1) R) *(a8.X2*(1+a8.X1))^n5 c*a8.X2^s3 c)
lemma mu {n B:ℕ}(a:Perm (Fin n))(p:P0 n):a8.nf (castRingHom (Z2 B)) (z9 (R:=ℤ) a p)=z9 (R:=Z2 B) a p:=by unfold z9;rw[map_prod];refine M4 rfl fun c _=>?_;simp only[map_add,map_one,map_mul,map_pow,map_intCast,a8.X1,a8.X2,a8.lc]
lemma mv {n B:ℕ}(a:Perm (Fin n))(p:P0 n):a8.nf (castRingHom (Z2 B)) (u9 (R:=ℤ) a p)=u9 (R:=Z2 B) a p:=by unfold u9;rw[map_prod];refine M4 rfl fun c _=>?_;simp only[map_add,map_one,map_mul,map_pow,map_intCast,a8.X1,a8.X2,a8.lc]
lemma ro {B B0 f M:ℕ}(a:B0=B+M)(b:f<=M)(x:ℤ):(((((2:ℤ)^f*x:ℤ):ZMod (2^B0)).val/2^f:ℕ):Z2 B)=(x:Z2 B):=by subst a;exact cu b x
def v9 (n B l r:ℕ):a8 3 (2*n+1) (Z2 B):=a8.X2^l*(1+a8.X1)^r
def y4 (n B l r:ℕ):a8 (n+1) (n+1) (Z2 B):=a8.X1^r*a8.X2^(l-r)
lemma co {l r:ℕ}(b:1<=l)(a:r∈n7 l):r<=l:=by unfold n7 at a;split_ifs at a<;>simp at a<;>omega
lemma lj {l r:ℕ}(b:1<=l)(a:r∈c4 l):r<=l:=by unfold c4 at a;split_ifs at a<;>simp at a<;>omega
lemma jg {n B l r:ℕ}(a:r<=l):(a8.X2*(1+a8.X1):a8 3 (2*n+1) (Z2 B))^r*a8.X2^(l-r)=v9 n B l r:=by unfold v9;rw[mul_pow,mul_comm ((a8.X2:a8 3 (2*n+1) (Z2 B))^r),mul_assoc,<-X6,V3 a,mul_comm ((1+a8.X1)^r)]
lemma ju {n B l r:ℕ}(b:1<=l):∀ i j,i.val+j.val=0->(v9 n B l r).coeff i j=0:=by intro i j a;unfold v9;rw[bk];have:j.val≠l:=(by omega);simp[this]
lemma ny {n B l r:ℕ}(c:1<=l)(b:r<=l):∀ i j,i.val+j.val=0->(y4 n B l r).coeff i j=0:=by intro i j a;unfold y4;rw[a8.t5];simp only[a8.o5];have:¬ (i.val=r/\j.val=l-r):=(by omega);simp[this]
lemma kd {n B:ℕ}(c:Perm (Fin n))(p:P0 n):z9 (R:=Z2 B) c p=∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (v9 n B l r) (e9 c p l r):=by
 unfold z9;rw[gd]
 . refine M4 rfl fun l a=>M4 rfl fun r b=>?_;rw[jg (lj (J4.mp a).1 (K3.mp b))]
 . intro l r a b;rw[jg (co a b)];exact ju a
 . intro l r a _ b d;rw[jg (co a b)];unfold v9
   rw[mul_pow,<-pow_mul,show (a8.X2:a8 3 (2*n+1) (Z2 B))^(l*2)=a8.o5 0 (l*2) by
    simp[a8.X2,a8.cr],a8.cl 0 (l*2) (inr (by omega)),zero_mul]
lemma ev {n B:ℕ}(c:Perm (Fin n))(p:P0 n):u9 (R:=Z2 B) c p=∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (y4 n B l r) (e9 c p l r):=by
 unfold u9;rw[gd]
 . rfl
 . intro l r a b;exact ny a (co a b)
 . intro l r a _ b f;have e:=co a b;change (y4 n B l r)^2=0;unfold y4;rw[a8.t5,a8.cr];refine a8.cl _ _ ?_;by_cases d:n+1<=2*r
   . exact inl d
   . exact inr (by omega)
def y7 (n B:ℕ)(a:Perm (Fin n))(p:P0 n)(k:ℕ):a8 3 (2*n+1) (Z2 B):=∏ l∈Icc (k+1) (2*n),∏ r∈(c4 l).toFinset,a8.c8 (v9 n B l r) (e9 a p l r)
def ar (n B:ℕ)(a:Perm (Fin n))(p:P0 n)(k:ℕ):a8 (n+1) (n+1) (Z2 B):=∏ l∈Icc 1 k,∏ r∈(c4 l).toFinset,a8.c8 (y4 n B l r) (e9 a p l r)
lemma lk {n B:ℕ} (c:Perm (Fin n)) (p:P0 n)
 (d:Fin (2*n)) (h:Fin 3):
 let l:=d.val+1
 (y7 n B c p d.val).coeff h ⟨l,by omega⟩=∑ r∈(c4 l).toFinset,-(e9 c p l r:Z2 B)*(choose r h.val:Z2 B):=by
 intro l;unfold y7
 have e:=x5 (D2:=2*n+1) (R:=Z2 B) (l:=l) (by omega) (by omega)
  (Icc l (2*n))
  (fun j=>∏ r∈(c4 j).toFinset,a8.c8 (v9 n B j r) (e9 c p j r))
  (fun j k=>(x5 (by omega) (by omega) (c4 j).toFinset (fun r=>a8.c8 (v9 n B j r) (e9 c p j r)) (fun r _=>(m6 (by omega) (J4.mp k).1 (by omega) _).1) (fun r _=>(m6 (by omega) (J4.mp k).1 (by omega) _).2.1)).1)
  (fun j k=>(x5 (by omega) (by omega) (c4 j).toFinset (fun r=>a8.c8 (v9 n B j r) (e9 c p j r)) (fun r _=>(m6 (by omega) (J4.mp k).1 (by omega) _).1) (fun r _=>(m6 (by omega) (J4.mp k).1 (by omega) _).2.1)).2.1)
 rw[e.2.2 h];have f:l∈Icc l (2*n):=J4.mpr ⟨le_refl l,d.isLt⟩;rw[Q4 l]
 . have a:=x5 (D2:=2*n+1) (R:=Z2 B) (l:=l) (by omega) (by omega)
    (c4 l).toFinset (fun r=>a8.c8 (v9 n B l r) (e9 c p l r))
    (fun r _=>(m6 (by omega) (le_refl l) (by omega) _).1)
    (fun r _=>(m6 (by omega) (le_refl l) (by omega) _).2.1)
   rw[a.2.2 h];refine L3 rfl fun r _=>?_;simpa[v9] using (m6 (D2:=2*n+1) (R:=Z2 B) (r:=r) (by omega) (le_refl l) (by omega) (e9 c p l r)).2.2 h
 . intro j k g
   have a:=x5 (D2:=2*n+1) (R:=Z2 B) (l:=l) (by omega) (by omega)
    (c4 j).toFinset (fun r=>a8.c8 (v9 n B j r) (e9 c p j r))
    (fun r _=>(m6 (by omega) (J4.mp k).1 (by omega) _).1)
    (fun r _=>(m6 (by omega) (J4.mp k).1 (by omega) _).2.1)
   rw[a.2.2 h];refine L9 fun r _=>?_;simpa[v9,g] using (m6 (D2:=2*n+1) (R:=Z2 B) (r:=r) (by omega) (J4.mp k).1 (by omega) (e9 c p j r)).2.2 h
 . intro i;exact absurd f i
lemma dr {n B:ℕ} (c:Perm (Fin n)) (p:P0 n)
 (a:Fin (2*n)):
 let l:=a.val+1
 (∏ r∈(c4 l).toFinset,a8.c8 (v9 n B l r) (-e9 c p l r)) *y7 n B c p a.val=y7 n B c p (a.val+1):=by
 intro l;unfold y7;have b:Icc l (2*n)=insert l (Icc (l+1) (2*n)):=(by ext x;simp only[J4,X3];omega);have e:l∉Icc (l+1) (2*n):=(by simp);rw[b,prod_insert e,<-mul_assoc,<-M3];have d:(∏ r∈(c4 l).toFinset,a8.c8 (v9 n B l r) (-e9 c p l r) *a8.c8 (v9 n B l r) (e9 c p l r))=1:=by refine prod_eq_one fun r _=>?_;rw[<-a8.fp _ (ju (by omega)),neg_add_cancel,a8.iz]
 rw[d,one_mul]
lemma du {n B:ℕ} (c:Perm (Fin n)) (p:P0 n)
 (a:Fin (2*n)):
 let l:=a.val+1
 (∏ r∈(c4 l).toFinset,a8.c8 (y4 n B l r) (e9 c p l r)) *ar n B c p a.val=ar n B c p (a.val+1):=by
 intro l;unfold ar;have b:Icc 1 l=insert l (Icc 1 a.val):=(by ext x;simp only[J4,X3];omega);have d:l∉Icc 1 a.val:=(by simp[l]);rw[b,prod_insert d]
lemma p3 {n:ℕ} (e:1<=n) (a:Perm (Fin n))
 (p:P0 n) (l r:ℕ):
 (e9 a p l r).natAbs<2^(n+2):=by
 obtain⟨g,f⟩:=dg a p l r;have d:(e9 a p l r).natAbs<=2*n:=(by omega);have c:n<2^n:=lt_two_pow_self;have b:2^(n+2)=4*2^n:=(by rw[X6];ring);omega
lemma q8 {n B:ℕ} (f:B=2*n+10) (c:Perm (Fin n))
 (p:P0 n) (l r:ℕ):
 -(2^(B-1):ℤ)<e9 c p l r/\e9 c p l r<2^(B-1):=by
 obtain⟨h,g⟩:=dg c p l r;have e:2*n<2^(2*n):=lt_two_pow_self;have d:2^(2*n)<=2^(2*n+9):=pow_le_pow_right (by omega) (by omega);have a:((2*n:ℕ):ℤ)<((2^(2*n+9):ℕ):ℤ):=(by exact_mod_cast (lt_of_lt_of_le e d));have b:B-1=2*n+9:=(by omega);rw[b]
 push_cast at a
 omega
end MainAssembly
end S399
namespace S393
namespace Compiler
namespace GateBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
def Legal (op:GateOp)(a:ℕ):Prop:=((op=.and\/op=.or)/\a=2)\/(op=.not/\a=1)
variable {α:Type*}
def Scheduled (n:ℕ)(F:α->(Fin n->Y0)->Y0)(k:ℕ)(S:Set α):Prop:=∃ gs:List Gate,gs.length=k/\ReadsBack n ⟨gs,0⟩/\(∀ g∈gs,Legal g.op g.inputs.length)/\∀ a∈S,∃ i:ℕ,i<n+k/\∀ x:Fin n->Y0,((Circuit.mk gs 0).wires (ofFn x)).getD i false=F a x
theorem py (C:Circuit)(w:List Y0):(C.wires w).length=w.length+C.gates.length:=by
 rcases C with ⟨gs,out⟩
 change (gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) w).length=w.length+gs.length
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>rw[List.foldl_cons,ih];simp only[K6,Z7,Z8];omega
theorem j4 {n:ℕ} {F:α->(Fin n->Y0)->Y0}
 (b:Fin n->α) (h:∀ i x,F (b i) x=x i):
 Scheduled n F 0 (R0 b):=by
 refine⟨[],rfl,?_,?_,?_⟩
 . simp[ReadsBack]
 . simp
 . intro a c;obtain⟨i,rfl⟩:=Set.mem_range.mp c;refine⟨i.val,by simpa using i.isLt,fun x=>?_⟩;change (ofFn x).getD i.val false=F (b i) x;rw[getD_eq_getElem _ _ (by simpa using i.isLt),getElem_ofFn,h i x]
theorem mw {n k:ℕ} {F:α->(Fin n->Y0)->Y0} {S T:Set α}
 (h:Scheduled n F k S) (b:T⊆S):Scheduled n F k T:=by
 obtain⟨gs,g,e,d,f⟩:=h;exact⟨gs,g,e,d,fun a c=>f a (b c)⟩
theorem pn {n k:ℕ} {F:α->(Fin n->Y0)->Y0} {S:Set α}
 {m:List Gate}
 (q:∀ a∈S,∃ i:ℕ,i<n+k/\∀ x:Fin n->Y0,((Circuit.mk m 0).wires (ofFn x)).getD i false=F a x)
 (c:List α) (d:∀ a∈c,a∈S):
 ∃ is:List ℕ,is.length=c.length/\(∀ i∈is,i<n+k)/\∀ x:Fin n->Y0,is.map (fun i=>((Circuit.mk m 0).wires (ofFn x)).getD i false)=c.map (fun a=>F a x):=by
 induction c with
 | nil=>exact⟨[],rfl,by simp,by simp⟩
 | cons a c ih=>
  obtain⟨i,o,l⟩:=q a (d a mem_cons_self);obtain⟨is,g,e,f⟩:=ih (fun b p=>d b (List.mem_cons_of_mem a p));refine⟨i :: is,by simp[g],?_,fun x=>?_⟩
  . intro j h
    rcases mem_cons.mp h with rfl|h
    . exact o
    . exact e j h
  . simp only[List.map_cons,l x,f x]
theorem rm {n k:ℕ} {F:α->(Fin n->Y0)->Y0} {S:Set α}
 (h:Scheduled n F k S) (op:GateOp) (c:List α) (out:α)
 (t:Legal op c.length) (p:∀ a∈c,a∈S)
 (d:∀ x,F out x=op.eval (c.map fun a=>F a x)):
 Scheduled n F (k+1) (insert out S):=by
 obtain⟨gs,l,w,v,s⟩:=h;obtain⟨is,u,o,f⟩:=pn s c p;let g:Gate:=⟨op,is⟩;have hlength (x:Fin n->Y0):((Circuit.mk gs 0).wires (ofFn x)).length=n+k:=(by rw[py];simpa using Q6 (n + ·) l);have hsnoc (x:Fin n->Y0):(Circuit.mk (gs ++ [g]) 0).wires (ofFn x)=(Circuit.mk gs 0).wires (ofFn x) ++ [F out x]:=(by simp only[Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil];change (Circuit.mk gs 0).wires (ofFn x) ++[op.eval (is.map fun i=>((Circuit.mk gs 0).wires (ofFn x)).getD i false)]=(Circuit.mk gs 0).wires (ofFn x) ++ [F out x];rw[f x,d x]);refine⟨gs ++ [g],by simp[l],?_,?_,?_⟩
 . intro j m i b;change j<(gs ++ [g]).length at m;change i∈((gs ++ [g]).getD j ⟨GateOp.or,[]⟩).inputs at b;by_cases hj':j<gs.length
   . rw[List.getD_append _ _ _ _ hj'] at b;exact w j hj' i b
   . have r:j=gs.length:=(by simp only[K6,List.length_singleton] at m;omega);subst j;rw[List.getD_append_right _ _ _ _ Y3] at b;have hi':i∈is:=(by simpa[g] using b);simpa[l] using o i hi'
 . intro g' hg';change g'∈gs ++ [g] at hg'
   rcases List.mem_append.mp hg' with hg'|hg'
   . exact v g' hg'
   . have r:g'=g:=List.mem_singleton.mp hg';subst g';change Legal op is.length;simpa only[u] using t
 . intro a q
   rcases Set.mem_insert_iff.mp q with rfl|q
   . refine⟨n+k,by omega,fun x=>?_⟩;rw[hsnoc x,List.getD_append_right _ _ _ _ (by simp[hlength x])];simp[hlength x]
   . obtain⟨i,b,hval'⟩:=s a q;refine⟨i,by omega,fun x=>?_⟩;rw[hsnoc x,List.getD_append _ _ _ _ (by simpa[hlength x] using b),hval' x]
end GateBridge
namespace Build
open PEqualNP.CircuitLowerBounds
variable {n:Nat}
abbrev d4 (n:Nat):=(Fin n->Y0)->Y0
def Build (A B:Set (d4 n))(b:Nat):Prop:=True/\(∀ {m S},GateBridge.Scheduled n id m S->A⊆S->∃ c≤b,GateBridge.Scheduled n id (m+c) (S∪B))
theorem Build.run {A B:Set (d4 n)} {b m S} (H:Build A B b)
 (HS:GateBridge.Scheduled n id m S) (a:A⊆S):
 ∃ c≤b,GateBridge.Scheduled n id (m+c) (S∪B):=H.2 HS a
theorem s6 {A B:Set (d4 n)}(h:B⊆A):Build A B 0:=by refine⟨trivial,?_⟩;intro m S HS a;refine⟨0,Nat.le_refl _,?_⟩;simpa[Set.union_eq_left.mpr (h.trans a)] using HS
theorem d9 {A B C D:Set (d4 n)} {b d:Nat}
 (H:Build A B b) (f:A⊆C) (a:D⊆B) (h:b<=d):Build C D d:=by
 refine⟨trivial,?_⟩;intro m S HS g;obtain⟨c,e,HS'⟩:=H.run HS (f.trans g);exact⟨c,e.trans h,GateBridge.mw HS' (Set.union_subset_union Y3 a)⟩
theorem q4 {A B C:Set (d4 n)} {b c:Nat}
 (H:Build A B b) (J:Build (A∪B) C c):Build A (B∪C) (b+c):=by
 refine⟨trivial,?_⟩;intro m S HS a;obtain⟨d,f,K⟩:=H.run HS a;obtain⟨e,g,K'⟩:=J.run K (Set.union_subset_union a Y3);exact⟨d+e,Nat.add_le_add f g,by simpa[Nat.add_assoc,W6] using K'⟩
theorem one {A:Set (d4 n)} (op:GateOp) (a:List (d4 n))
 (c:GateBridge.Legal op a.length)
 (i:∀ g∈a,g∈A) (f:d4 n)
 (e:∀ x,f x=op.eval (a.map fun g=>g x)):Build A {f} 1:=by
 refine⟨trivial,?_⟩;intro m S HS d;refine⟨1,Y3,?_⟩;have h:=GateBridge.rm HS op a f c (fun g b=>d (i g b)) e;rw[Set.insert_eq] at h;exact GateBridge.mw h (by intro g b;exact b.elim inr inl)
def an (f g:d4 n):d4 n:=fun x=>f x && g x
def or (f g:d4 n):d4 n:=fun x=>f x||g x
def nt (f:d4 n):d4 n:=fun x=>!f x
def xo (f g:d4 n):d4 n:=fun x=>xor (f x) (g x)
theorem t7 {A:Set (d4 n)}{f g:d4 n}(b:f∈A)(a:g∈A):Build A {an f g} 1:=one .and [f,g] (by simp[GateBridge.Legal]) (by simpa using And.intro b a) _ (by simp[GateOp.eval,an])
theorem gg {A:Set (d4 n)}{f g:d4 n}(b:f∈A)(a:g∈A):Build A {or f g} 1:=one .or [f,g] (by simp[GateBridge.Legal]) (by simpa using And.intro b a) _ (by simp[GateOp.eval,or])
theorem ae {A:Set (d4 n)}{f:d4 n}(a:f∈A):Build A {nt f} 1:=one .not [f] (by simp[GateBridge.Legal]) (by simpa using a) _ (by simp[GateOp.eval,nt])
theorem qr {A:Set (d4 n)}{f g:d4 n}(h:f∈A)(e:g∈A):Build A {xo f g} 4:=by
 have i:xo f g=an (or f g) (nt (an f g)):=by
  funext x
  change xor (f x) (g x)=((f x||g x) && !(f x && g x));cases f x<;>cases g x<;>rfl
 rw[i];have b:=t7 h e;have c:=gg (A:=A∪{an f g}) (inl h) (inl e);have a:=ae (A:=A∪({an f g}∪{or f g})) (f:=an f g) (by simp)
 have d:=t7 (A:=A∪(({an f g}∪{or f g})∪{nt (an f g)}))
  (f:=or f g) (g:=nt (an f g)) (by simp) (by simp)
 exact d9 (q4 (q4 (q4 b c) a) d) Y3 (by simp) Y3
theorem po {d:Type*} [DecidableEq d] {A:Set (d4 n)}
 (F:d->d4 n) (a cost:d->Nat) (s:V7 d)
 (H:∀ i∈s,Build (A∪{f|∃ j∈s,a j<a i/\f=F j}) {F i} (cost i)):
 Build A {f|∃ i∈s,f=F i} (∑ i∈s,cost i):=by
 classical
 induction s using Finset.strongInduction with
 | H s IH=>
  by_cases m:s.Nonempty
  . obtain⟨i,g,e⟩:=Finset.exists_max_image s a m;have Hsub:s.erase i ⊂ s:=Finset.erase_ssubset g
    have hstep (j:d) (b:j∈s.erase i) (l:d) (k:l∈s)
     (c:a l<a j):l∈s.erase i:=by
     refine mem_erase.mpr ⟨?_,k⟩;intro p;subst l;exact (Nat.not_lt_of_ge (e j (Finset.mem_of_mem_erase b))) c
    have Hs:=IH (s.erase i) Hsub fun j b=>d9 (H j (Finset.mem_of_mem_erase b))
      (by
       rintro f (h|⟨l,k,c,rfl⟩)
       . exact inl h
       . exact inr ⟨l,hstep j b l k c,c,rfl⟩) Y3 Y3
    have Hi:=d9 (H i g) (C:=A∪{f|∃ j∈s.erase i,f=F j})
     (by
      rintro f (h|⟨j,b,c,rfl⟩)
      . exact inl h
      . exact inr ⟨j,mem_erase.mpr ⟨by aesop,b⟩,rfl⟩) Y3 Y3
    refine d9 (q4 Hs Hi) Y3 ?_ ?_
    . rintro f ⟨j,b,rfl⟩;by_cases o:j=i
      . exact inr (by simp[o])
      . exact inl ⟨j,mem_erase.mpr ⟨o,b⟩,rfl⟩
    . rw[Finset.sum_erase_add _ _ g]
  . have:s=∅:=Finset.not_nonempty_iff_eq_empty.mp m;subst s;exact d9 (s6 (A:=A) (B:=∅) (by simp)) Y3 (by simp) (by simp)
theorem rn {A:Set (d4 n)} (a:List (d4 n))
 (c:∀ f∈a,f∈A) (b:(fun _=>false)∈A):
 Build A {fun x=>a.any (fun f=>f x)} a.length:=by
 induction a with
 | nil=>exact s6 (Q1 b)
 | cons f a IH=>
  have H:=IH (fun g d=>c g (List.mem_cons_of_mem f d))
  have K:=gg (A:=A∪{fun x=>a.any (fun g=>g x)})
   (inl (c f mem_cons_self)) (inr rfl)
  exact d9 (q4 H K) Y3 (Q1 (inr rfl)) (by simp)
theorem ke {a:Type*} [Fintype a] {A:Set (d4 n)}
 (F:a->d4 n) (c:Nat) (H:∀ i,Build A {F i} c):
 Build A (R0 F) (W0 a*c):=by
 classical
 have K:=po F (fun _=>0) (fun _=>c) univ
  (fun i _=>d9 (H i) M8 Y3 Y3)
 refine d9 (by simpa only[sum_const,W2,Nat.nsmul_eq_mul] using K) Y3 ?_ Y3;rintro _ ⟨i,rfl⟩;exact⟨i,Y2 _,rfl⟩
theorem au {k:Nat} {A:Set (d4 n)} (F:Fin k->d4 n) (c:Nat)
 (H:∀ i,Build A {F i} c):Build A (R0 F) (k*c):=by
 simpa only[Q9] using ke F c H
def inputs (n:Nat):Set (d4 n):=R0 (fun i:Fin n=>fun v=>v i)
def jh (n:Nat):Set (d4 n):=inputs n∪{fun _=>false,fun _=>true}
theorem i7 {A B C:Set (d4 n)} {b c:Nat}
 (h:Build A B b) (j:Build (A∪B) C c):Build A C (b+c):=
 d9 (q4 h j) Y3 M9 Y3
theorem q6 {A B C:Set (d4 n)} {b c:Nat}
 (h:Build A B b) (j:Build A C c):Build A (B∪C) (b+c):=
 q4 h (d9 j M8 Y3 Y3)
theorem ew {A:Set (d4 n)} (F:Nat->Set (d4 n)) {b c t:Nat}
 (e:Build A (F 0) b)
 (a:∀ j,j<t->Build (A∪F j) (F (j+1)) c):
 Build A (F t) (b+t*c):=by
 induction t with
 | zero=>simpa only[Nat.zero_mul,Nat.add_zero] using e
 | succ t ih=>
  have d:=ih (fun j f=>a j (Nat.lt_succ_of_lt f));refine d9 (q4 d (a t (U2 t))) Y3 M9 ?_;rw[succ_mul,Nat.add_assoc]
def mx (s f g:d4 n):d4 n:=fun x=>if s x then g x else f x
theorem rj {A:Set (d4 n)}{s f g:d4 n}(e:s∈A)(i:f∈A)(h:g∈A):Build A {mx s f g} 4:=by
 have j:mx s f g=or (an (nt s) f) (an s g):=by
  funext x
  change (if s x then g x else f x)=((!(s x) && f x)||(s x && g x));cases s x<;>cases f x<;>cases g x<;>rfl
 rw[j];have b:=ae e;have c:=t7 (A:=A∪{nt s}) (f:=nt s) (by simp) (inl i)
 have a:=t7 (A:=A∪({nt s}∪{an (nt s) f}))
  (inl e) (inl h)
 have d:=gg (A:=A∪(({nt s}∪{an (nt s) f})∪{an s g}))
  (f:=an (nt s) f) (g:=an s g) (by simp) (by simp)
 exact d9 (q4 (q4 (q4 b c) a) d) Y3 (by simp) Y3
theorem ox {A:Set (d4 n)} (a:List (d4 n))
 (c:∀ f∈a,f∈A) (b:(fun _=>true)∈A):
 Build A {fun x=>a.all (fun f=>f x)} a.length:=by
 induction a with
 | nil=>exact s6 (Q1 b)
 | cons f a ih=>
  have H:=ih (fun g d=>c g (List.mem_cons_of_mem f d))
  have K:=t7 (A:=A∪{fun x=>a.all (fun g=>g x)})
   (inl (c f mem_cons_self)) (inr rfl)
  exact d9 (q4 H K) Y3 M9 (by simp)
abbrev pz (n w:Nat):=Fin w->d4 n
def i9 {w:Nat}(A:Set (d4 n))(v:pz n w):Prop:=∀ i,v i∈A
theorem qa {w:Nat} {A:Set (d4 n)} (v:Fin w->Y0)
 (a:(fun _=>false)∈A) (b:(fun _=>true)∈A):
 Build A (R0 (fun(i:Fin w) (_:Fin n->Y0)=>v i)) 0:=by
 apply s6;rintro _ ⟨i,rfl⟩;cases hi:v i
 . simpa only[hi] using a
 . simpa only[hi] using b
theorem oy {w:Nat}{A:Set (d4 n)}{v:pz n w}(a:i9 A v):Build A (R0 (fun i=>nt (v i))) w:=by simpa only[Nat.mul_one] using au (fun i=>nt (v i)) 1 (fun i=>ae (a i))
theorem qs {w:Nat} {A:Set (d4 n)} {v u:pz n w}
 (a:i9 A v) (b:i9 A u):
 Build A (R0 (fun i=>an (v i) (u i))) w:=by
 simpa only[Nat.mul_one] using au (fun i=>an (v i) (u i)) 1 (fun i=>t7 (a i) (b i))
theorem kf {w:Nat} {A:Set (d4 n)} {s:d4 n} {v u:pz n w}
 (c:s∈A) (a:i9 A v) (b:i9 A u):
 Build A (R0 (fun i=>mx s (v i) (u i))) (w*4):=
 au _ 4 (fun i=>rj c (a i) (b i))
theorem aa {A B C D:Set (d4 n)} {b d:Nat}
 (H:Build A B b) (g:A⊆C) (i:D⊆C∪B) (h:b<=d):Build C D d:=by
 refine⟨trivial,?_⟩;intro m S HS e;obtain⟨c,a,HS'⟩:=H.run HS (g.trans e);refine⟨c,a.trans h,GateBridge.mw HS' ?_⟩;intro f j
 rcases j with k|hd
 . exact inl k
 . rcases i hd with a|hb
   . exact inl (e a)
   . exact inr hb
theorem bl (a b:Y0):xor a b=((a||b) && !(a && b)):=by
 cases a<;>cases b<;>rfl
def kg (a b c:Y0):Y0:=xor (xor a b) c
def ie (a b c:Y0):Y0:=(a && b)||(xor a b && c)
theorem qb {N:ℕ} {A:Set (d4 N)} {j k l:d4 N}
 (s:j∈A) (t:k∈A) (r:l∈A):
 Build A ({fun x=>kg (j x) (k x) (l x),fun x=>ie (j x) (k x) (l x)}) 9:=by
 let c:d4 N:=fun x=>j x||k x;let b:d4 N:=fun x=>j x && k x;let a:d4 N:=fun x=>!(b x);let h:d4 N:=fun x=>c x && a x;let g:d4 N:=fun x=>h x||l x;let d:d4 N:=fun x=>h x && l x;let e:d4 N:=fun x=>!(d x);let i:d4 N:=fun x=>g x && e x;let m:d4 N:=fun x=>b x||d x;have v:Build A {c} 1:=gg s t;have h2:Build (A∪{c}) {b} 1:=t7 (inl s) (inl t);have h3:Build (A∪({c}∪{b})) {a} 1:=ae (inr (inr rfl));have w:Build (A∪(({c}∪{b})∪{a})) {h} 1:=t7 (inr (inl (inl rfl))) (inr (inr rfl));have z:Build (A∪((({c}∪{b})∪{a})∪{h})) {g} 1:=gg (inr (inr rfl)) (inl r);have h6:Build (A∪(((({c}∪{b})∪{a})∪{h})∪{g})) {d} 1:=t7 (inr (inl (inr rfl))) (inl r);have y:Build (A∪((((({c}∪{b})∪{a})∪{h})∪{g})∪{d})) {e} 1:=ae (inr (inr rfl));have h8:Build (A∪(((((({c}∪{b})∪{a})∪{h})∪{g})∪{d})∪{e})) {i} 1:=t7 (inr (inl (inl (inr rfl)))) (inr (inr rfl))
 have u:Build (A∪((((((({c}∪{b})∪{a})∪{h})∪{g})∪{d})∪{e})∪{i})) {m} 1:=gg (inr (inl (inl (inl (inl (inl (inl (inr rfl))))))))
   (inr (inl (inl (inr rfl))))
 have p:=q4 (q4 (q4 (q4 (q4 (q4 (q4 (q4 v h2) h3) w) z) h6) y) h8) u
 have o:i=fun x=>kg (j x) (k x) (l x):=by
  funext x
  simp only[i,g,e,d,h,c,a,b,kg];rw[bl (j x) (k x),bl _ (l x)]
 have n:m=fun x=>ie (j x) (k x) (l x):=by
  funext x
  simp only[m,d,h,c,a,b,ie];rw[bl (j x) (k x)]
 refine aa p Y3 ?_ (by omega);intro f q;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at q
 rcases q with rfl|rfl
 . rw[<-o];exact inr (inl (inr rfl))
 . rw[<-n];exact inr (inr rfl)
def v7 (a b:ℕ):ℕ->Y0
 | 0=>false
 | j+1=>ie (a.testBit j) (b.testBit j) (v7 a b j)
theorem y3 (x j:ℕ):x.testBit j=decide ((x/2^j) %2=1):=by
 rw[Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two];have b:(x/2^j) %2<2:=M1 _ (by omega);have a:(x/2^j) %2=0\/(x/2^j) %2=1:=by omega
 rcases a with h|h<;>simp[h]
theorem cm (a j:ℕ):a %2^(j+1)=a %2^j+(if a.testBit j then 2^j else 0):=by
 have g:0<2^j:=two_pow_pos j;have k:=div_add_mod a (2^j);have d:=div_add_mod (a/2^j) 2;have e:a=(a %2^j+2^j*((a/2^j) %2))+2^(j+1)*(a/2^j/2):=by rw[Nat.pow_succ];have f:2^j*(a/2^j)=2^j*(2*(a/2^j/2)+(a/2^j) %2):=(by rw[d]);rw[Nat.mul_add] at f;have i:2^j*(2*(a/2^j/2))=2^j*2*(a/2^j/2):=(by ring);omega
 have b:a %2^j+2^j*((a/2^j) %2)<2^(j+1):=by
  have f:a %2^j<2^j:=M1 _ g;have i:(a/2^j) %2<=1:=by have:=M1 (a/2^j) (by omega:0<2);omega
  have l:2^j*((a/2^j) %2)<=2^j:=by
   calc 2^j*((a/2^j) %2)<=2^j*1:=W5 _ i
    _=2^j:=Nat.mul_one _
  rw[Nat.pow_succ];omega
 have f:a %2^(j+1)=a %2^j+2^j*((a/2^j) %2):=by
  conv_lhs=>rw[e]
  rw[Nat.add_mul_mod_self_left,L8 b]
 rw[f,y3 a j];have c:(a/2^j) %2=0\/(a/2^j) %2=1:=by have:=M1 (a/2^j) (by omega:0<2);omega
 rcases c with h|h<;>simp[h]
theorem ij (a b:ℕ):∀ j:ℕ,v7 a b j=decide (2^j<=a %2^j+b %2^j)/\(a+b).testBit j=kg (a.testBit j) (b.testBit j) (v7 a b j):=by
 intro j
 have c:∀ k:ℕ,v7 a b k=decide (2^k≤a %2^k+b %2^k):=by
  intro k
  induction k with
  | zero=>simp[v7,Nat.mod_one]
  | succ k ih=>
   unfold v7;rw[ih,cm a k,cm b k];have e:a %2^k<2^k:=M1 _ (two_pow_pos k);have f:b %2^k<2^k:=M1 _ (two_pow_pos k);have u:2^(k+1)=2^k+2^k:=(by rw[Nat.pow_succ];omega);cases h1:a.testBit k<;>cases h2:b.testBit k<;>by_cases t:2^k<=a %2^k+b %2^k<;>simp[ie,t,u]<;>omega
 refine⟨c j,?_⟩;rw[c j];have i:(a+b)/2^j=a/2^j+b/2^j+(a %2^j+b %2^j)/2^j:=by have l:=div_add_mod a (2^j);have m:=div_add_mod b (2^j);have p:0<2^j:=two_pow_pos j;have n:a+b=(a %2^j+b %2^j)+(a/2^j+b/2^j)*2^j:=(by have:2^j*(a/2^j)=(a/2^j)*2^j:=Nat.mul_comm _ _;have:2^j*(b/2^j)=(b/2^j)*2^j:=Nat.mul_comm _ _;rw[Nat.add_mul];omega);rw[n,Nat.add_mul_div_right _ _ p];omega
 have d:(a %2^j+b %2^j)/2^j=if 2^j<=a %2^j+b %2^j then 1 else 0:=by
  have e:a %2^j<2^j:=M1 _ (two_pow_pos j);have f:b %2^j<2^j:=M1 _ (two_pow_pos j);by_cases g:2^j<=a %2^j+b %2^j
  . simp only[g,↓reduceIte];have h:a %2^j+b %2^j=(a %2^j+b %2^j-2^j)+1*2^j:=(by omega);rw[h,Nat.add_mul_div_right _ _ (two_pow_pos j),div_eq_of_lt (by omega)]
  . simp only[g,↓reduceIte];exact div_eq_of_lt (by omega)
 rw[y3 (a+b) j,y3 a j,y3 b j,i,d];have r:(a/2^j) %2=0\/(a/2^j) %2=1:=by have:=M1 (a/2^j) (by omega:0<2);omega
 have q:(b/2^j) %2=0\/(b/2^j) %2=1:=by have:=M1 (b/2^j) (by omega:0<2);omega
 have o:(a/2^j+b/2^j+if 2^j<=a %2^j+b %2^j then 1 else 0) %2=((a/2^j) %2+(b/2^j) %2+if 2^j<=a %2^j+b %2^j then 1 else 0) %2:=(by omega);rw[o]
 by_cases s:2^j<=a %2^j+b %2^j <;>
 rcases r with l|l <;>
 rcases q with m|m <;>
 simp[kg,s,l,m]
def a9 {N:ℕ}(L:ℕ)(F:(Fin N->Y0)->ℕ):Fin L->d4 N:=fun j x=>(F x).testBit j.val
theorem pv {N:ℕ} {A:Set (d4 N)} (F G:(Fin N->Y0)->ℕ)
 (b:(fun _=>false)∈A):
 ∀ L:ℕ,(∀ j:Fin L,(fun x=>(F x).testBit j.val)∈A)->(∀ j:Fin L,(fun x=>(G x).testBit j.val)∈A)->Build A
   ((R0 (a9 L (fun x=>F x+G x)))∪{fun x=>v7 (F x) (G x) L})
   (9*L):=by
 intro L
 induction L with
 | zero=>
  intro _ _;simp only[Nat.mul_zero];apply s6;intro f g
  rcases g with ⟨j,_⟩|rfl
  . exact elim0 j
  . exact b
 | succ L ih=>
  intro l i;have c:=ih (fun j=>l j.castSucc) (fun j=>i j.castSucc)
  have d:Build
   (A∪(R0 (a9 L (fun x=>F x+G x))∪{fun x=>v7 (F x) (G x) L}))
   ({fun x=>kg ((F x).testBit L) ((G x).testBit L) (v7 (F x) (G x) L),fun x=>ie ((F x).testBit L) ((G x).testBit L) (v7 (F x) (G x) L)}) 9:=
   qb (inl (l (last L))) (inl (i (last L))) (inr (inr rfl))
  have h:=q4 c d;refine aa h Y3 ?_ (by omega);intro f g
  rcases g with ⟨j,rfl⟩|rfl
  . by_cases k:j.val<L
    . have a:a9 (L+1) (fun x=>F x+G x) j=a9 L (fun x=>F x+G x) ⟨j.val,k⟩:=rfl;rw[a];exact inr (inl (inl ⟨⟨j.val,k⟩,rfl⟩))
    . have a:j.val=L:=by omega
      have e:a9 (L+1) (fun x=>F x+G x) j=fun x=>kg ((F x).testBit L) ((G x).testBit L) (v7 (F x) (G x) L):=by
       funext x
       unfold a9;rw[a];exact (ij (F x) (G x) L).2
      rw[e];exact inr (inr (inl rfl))
  . exact inr (inr (inr rfl))
theorem jv {N:ℕ} {A:Set (d4 N)} (L:ℕ) (F G:(Fin N->Y0)->ℕ)
 (a:(fun _=>false)∈A)
 (b:∀ j:Fin L,a9 L F j∈A)
 (c:∀ j:Fin L,a9 L G j∈A):
 Build A (R0 (a9 L (fun x=>F x+G x))) (9*L):=
 aa (pv F G a L b c) Y3
  (fun _ hf=>inr (inl hf)) Y3
def m0 {a:Type*}(s:V7 a)(B:a->Set (d4 n)):Set (d4 n):=
 {f|∃ i∈s,f∈B i}
lemma p7 {b:Type*} [Fintype b] {A:Set (d4 n)} (B:b->Set (d4 n)) (c:Nat)
 (h:∀ i,Build A (B i) c):Build A (m0 univ B) (W0 b*c):=by
 classical
 suffices ∀ s,Build A (m0 s B) (s.card*c) by simpa[W2] using this univ
 intro s
 induction s using induction_on with
 | empty=>simpa[m0] using (s6 (A:=A) (B:=∅) (by simp))
 | @insert i s hi ih=>
  have d:=q6 ih (h i);refine d9 d Y3 ?_ (by rw[W9 hi,succ_mul]);rintro v ⟨j,a,e⟩
  rcases X3.mp a with rfl|a
  . exact inr e
  . exact inl ⟨j,a,e⟩
lemma q3 {a:Type*} [Fintype a] {B:a->Set (d4 n)} {i:a} {f:d4 n}
 (h:f∈B i):f∈m0 univ B:=⟨i,Y2 i,h⟩
end Build
end Compiler
namespace Compiler
namespace Build
theorem my {A:Set (d4 N)} (c:ℕ) (b:(fun _=>false)∈A)
 (a:(fun _=>true)∈A):Build A (R0 (a9 m (fun _=>c))) 0:=
 qa (fun j=>c.testBit j.val) b a
theorem ig {A:Set (d4 N)} {p:d4 N} {F:(Fin N->Y0)->ℕ}
 (a:p∈A) (b:i9 A (a9 m F)):
 Build A (R0 (a9 m (fun x=>if p x then F x else 0))) m:=by
 apply d9 (qs (v:=fun _=>p) (u:=a9 m F) (fun _=>a) b) Y3 ?_ Y3;rintro _ ⟨j,rfl⟩;refine⟨j,?_⟩
 funext x
 cases hp':p x<;>simp[a9,an,hp']
private theorem ji (a:ℕ):(2*a+1).testBit 0=true:=by rw[show 2*a+1=2^1*a+1 by rfl];rw[Nat.testBit_two_pow_mul_add a (b:=1) (i:=1) (by decide)];rfl
private theorem jj (a j:ℕ):(2*a+1).testBit (j+1)=a.testBit j:=by rw[show 2*a+1=2^1*a+1 by rfl];rw[Nat.testBit_two_pow_mul_add a (b:=1) (i:=1) (by decide)];simp
private theorem oa (a j:ℕ):(2*a).testBit (j+1)=a.testBit j:=by rw[show 2*a=2^1*a+0 by rfl];rw[Nat.testBit_two_pow_mul_add a (b:=0) (i:=1) (by decide)];simp
theorem rc {N w:ℕ} {A:Set (d4 N)} (F T:(Fin N->Y0)->ℕ)
 (b:(fun _=>false)∈A) (d:(fun _=>true)∈A)
 (r:i9 A (a9 w F)) (q:i9 A (a9 w T))
 (g:∀ x,F x<2^w) (e:∀ x,T x<2^w):
 Build A (R0 (a9 w (fun x=>F x+(2^w-(T x+1))+1))∪
  {fun x=>decide (F x<T x)}) (10*w+10):=by
 let C:(Fin N->Y0)->ℕ:=fun x=>2^w-(T x+1);have hC (x):T x+C x+1=2^w:=(by have:=e x;dsimp[C];omega);have hCb (x):C x<2^w:=by have:=hC x;omega
 have hcbit (j:Fin w):a9 w C j=nt (a9 w T j):=by
  funext x
  simpa[a9,C,nt,j.isLt] using Nat.testBit_two_pow_sub_succ (e x) j.val
 have Hc:Build A (R0 (a9 w C)) w:=(by rw[show a9 w C=_ from funext hcbit];exact oy q);let B:=A∪R0 (a9 w C);let U:(Fin N->Y0)->ℕ:=fun x=>2*F x+1;let V:(Fin N->Y0)->ℕ:=fun x=>2*C x+1
 have liftBits {G:(Fin N->Y0)->ℕ} (o:i9 B (a9 w G)):i9 B (a9 (w+1) (fun x=>2*G x+1)):=by
  intro j;by_cases p:j.val=0
  . have a:a9 (w+1) (fun x=>2*G x+1) j=fun _=>true:=by
     funext x
     change (2*G x+1).testBit j.val=true;rw[p,ji]
    rw[a];exact inl d
  . let i:Fin w:=⟨j.val-1,by omega⟩;have l:j.val=i.val+1:=by dsimp[i];omega
    have a:a9 (w+1) (fun x=>2*G x+1) j=a9 w G i:=by
     funext x
     change (2*G x+1).testBit j.val=(G x).testBit i.val;rw[l,jj]
    rw[a];exact o i
 have Hsum:=pv U V (A:=B) (inl b) (w+1)
  (liftBits (fun j=>inl (r j))) (liftBits (fun j=>inr ⟨j,rfl⟩))
 let Carry:d4 N:=fun x=>v7 (U x) (V x) (w+1)
 have c:nt Carry=fun x=>decide (F x<T x):=by
  funext x
  have k:U x<2^(w+1):=(by have:=g x;rw[Nat.pow_succ];dsimp[U];omega);have m:V x<2^(w+1):=(by have:=hCb x;rw[Nat.pow_succ];dsimp[V];omega);have a:2^(w+1)<=U x+V x↔T x<=F x:=(by rw[Nat.pow_succ];have:=hC x;dsimp[U,V];omega);simp only[nt,Carry,(ij (U x) (V x) (w+1)).1,L8 k,L8 m,a];by_cases h:T x<=F x
  . simp[h,Nat.not_lt_of_ge h]
  . simp[h,Nat.lt_of_not_ge h]
 have Hnot:=ae
  (A:=A∪(R0 (a9 w C)∪(R0 (a9 (w+1) (fun x=>U x+V x))∪{Carry})))
  (f:=Carry) (inr (inr (inr rfl)))
 refine d9 (q4 (q4 Hc Hsum) Hnot) Y3 ?_ (by omega);intro f n
 rcases n with ⟨j,rfl⟩|rfl
 . let i:Fin (w+1):=⟨j.val+1,by omega⟩
   have a:a9 w (fun x=>F x+C x+1) j=a9 (w+1) (fun x=>U x+V x) i:=by
    funext x
    change (F x+C x+1).testBit j.val=(U x+V x).testBit (j.val+1);rw[show U x+V x=2*(F x+C x+1) by dsimp[U,V];omega,oa]
   change a9 w (fun x=>F x+C x+1) j∈_;rw[a];exact inl (inr (inl ⟨i,rfl⟩))
 . rw[<-c];exact inr rfl
theorem pq {N w:ℕ} {A:Set (d4 N)} (F T:(Fin N->Y0)->ℕ)
 (a:(fun _=>false)∈A) (b:(fun _=>true)∈A)
 (e:i9 A (a9 w F)) (k:i9 A (a9 w T))
 (d:∀ x,F x<2^w) (c:∀ x,T x<2^w):
 Build A (R0 (a9 w (fun x=>if T x<=F x then F x-T x else F x))∪
  {fun x=>decide (F x<T x)}) (14*w+10):=by
 let D:=a9 w (fun x=>F x+(2^w-(T x+1))+1);let L:d4 N:=fun x=>decide (F x<T x);have H:=rc F T a b e k d c
 have Hmux:=kf (A:=A∪(R0 D∪{L})) (s:=L) (v:=D) (u:=a9 w F)
  (inr (inr rfl)) (fun j=>inr (inl ⟨j,rfl⟩)) (fun j=>inl (e j))
 refine d9 (q4 H Hmux) Y3 ?_ (by omega);intro f g
 rcases g with ⟨j,rfl⟩|rfl
 . refine inr ⟨j,?_⟩
   funext x
   by_cases h:T x<=F x
   . have l:=c x;have i:F x+(2^w-(T x+1))+1=2^w+(F x-T x):=(by omega);simp[mx,D,L,a9,h,Nat.not_lt_of_ge h,i,Nat.testBit_two_pow_add_gt j.isLt]
   . simp[mx,D,L,a9,h,Nat.lt_of_not_ge h]
 . exact inl (inr rfl)
theorem dh {N w:ℕ} {A:Set (d4 N)} {a:Type*}
 (s:V7 a) (F:a->(Fin N->Y0)->ℕ)
 (b:(fun _=>false)∈A) (d:(fun _=>true)∈A)
 (c:∀ i∈s,i9 A (a9 w (F i))):
 Build A (R0 (a9 w (fun x=>∑ i∈s,F i x))) (s.card*(9*w)):=by
 classical
 induction s using induction_on with
 | empty=>simpa using (my (m:=w) 0 b d)
 | @insert i s hi ih=>
  have H:=ih (fun j e=>c j (mem_insert_of_mem e))
  have H':=jv (A:=A∪R0 (a9 w (fun x=>∑ j∈s,F j x)))
   w (F i) (fun x=>∑ j∈s,F j x) (inl b)
   (fun j=>inl (c i (mem_insert_self _ _) j))
   (fun j=>inr ⟨j,rfl⟩)
  simpa only[sum_insert hi,W9 hi,Nat.add_mul,Nat.one_mul]
   using i7 H H'
theorem gh {N w:ℕ} {A:Set (d4 N)} {a:Type*} [Fintype a]
 (b:a->d4 N) (F:a->(Fin N->Y0)->ℕ)
 (e:(fun _=>false)∈A) (c:(fun _=>true)∈A)
 (d:∀ i,b i∈A) (f:∀ i,i9 A (a9 w (F i))):
 Build A (R0 (a9 w (fun x=>∑ i,if b i x then F i x else 0)))
  (W0 a*(10*w)):=by
 classical
 let G (i:a) (x:Fin N->Y0):=if b i x then F i x else 0
 have H:=p7 (fun i=>R0 (a9 w (G i))) w
  (fun i=>ig (d i) (f i))
 have H':=dh (A:=A∪m0 univ (fun i=>R0 (a9 w (G i))))
  univ G (inl e) (inl c)
  (fun i _ j=>inr (q3 (B:=fun i=>R0 (a9 w (G i))) (i:=i) ⟨j,rfl⟩))
 simpa only[W2,<-Nat.mul_add,show w+9*w=10*w by omega]
  using i7 H H'
end Build
end Compiler
namespace Front
open Compiler.Build Compiler.GateBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
private theorem oz {N:ℕ}(d:0<N):Build (inputs N) ({fun _=>false,fun _=>true}:Set (d4 N)) 3:=by
 let p:d4 N:=fun x=>x ⟨0,d⟩;have e:p∈inputs N:=⟨⟨0,d⟩,rfl⟩;have c:=ae e;have b:=t7 (A:=inputs N∪{nt p}) (f:=p) (g:=nt p) (inl e) (inr rfl)
 have j:an p (nt p)=fun _=>false:=by
  funext x
  cases h:p x<;>simp[an,nt,h]
 rw[j] at b;have a:=ae (A:=inputs N∪({nt p}∪{fun _=>false})) (f:=fun _=>false) (inr (inr rfl));have i:nt (fun _:Fin N->Y0=>false)=fun _=>true:=rfl;rw[i] at a;refine d9 (q4 (q4 c b) a) Y3 ?_ Y3;rintro f (rfl|rfl)
 . exact inl (inr rfl)
 . exact inr rfl
theorem realize {N b:ℕ}{O:Set (d4 N)}(j:0<N)(H:Build (jh N) O b):∃(g:Circuit) (c:O->Fin (N+g.size)),ReadsBack N g/\g.size≤3+b/\(∀ a∈g.gates,Legal a.op a.inputs.length)/\∀(f:O) (x:Fin N->Y0),(g.wires (ofFn x)).getD (c f).val false=f.val x:=by
 classical
 have H':Build (inputs N) O (3+b):=i7 (oz j) H;have h:Scheduled N id 0 (inputs N):=j4 (F:=id) (fun(i:Fin N) x=>x i) (fun _ _=>rfl);obtain⟨k,l,d⟩:=H'.run h Y3;rw[Nat.zero_add] at d;obtain⟨gs,e,back,legal,m⟩:=d;have hh (f:O):=m f.val (inr f.property)
 choose i hi h using hh
 refine⟨⟨gs,0⟩,fun f=>⟨i f,?_⟩,back,?_,legal,?_⟩
 . simpa only[Circuit.size,e] using hi f
 . simpa only[Circuit.size,e] using l
 . intro f x;exact h f x
end Front
section BitHelpers
open scoped BigOperators
theorem fk (B v:ℕ):(∑ j:Fin B,(v.testBit j.val).toNat*2^j.val)=v %2^B:=by
 apply Nat.eq_of_testBit_eq;intro k
 have d:∀ B':ℕ,∀ w:Fin B'->Y0,(∑ j:Fin B',(w j).toNat*2^j.val).testBit k=if h:k<B' then w ⟨k,h⟩ else false:=by
  intro B' w
  induction B' generalizing k with
  | zero=>simp
  | succ B' ih=>
   rw[Fin.sum_univ_succ];simp only[val_zero,pow_zero,mul_one,Fin.val_succ,U4]
   have b:(∑ i:Fin B',(w i.succ).toNat*(2^i.val*2))=2*∑ i:Fin B',(w i.succ).toNat*2^i.val:=by
    rw[mul_sum];refine L3 rfl fun i _=>by ring
   rw[b]
   cases k with
   | zero=>
    simp only[Nat.zero_lt_succ,↓reduceDIte];change ((w 0).toNat+2*∑ i:Fin B',(w i.succ).toNat*2^i.val).testBit 0=w 0;cases h0:w 0<;>simp[Nat.testBit_zero]
   | succ k=>
    have c:((w 0).toNat+2*∑ i:Fin B',(w i.succ).toNat*2^i.val).testBit (k+1)=(∑ i:Fin B',(w i.succ).toNat*2^i.val).testBit k:=by
     rw[Nat.testBit_succ];congr 1;cases w 0<;>simp<;>omega
    rw[c,ih k (fun i=>w i.succ)];by_cases a:k<B'
    . simp[a,show k+1<B'+1 by omega]
    . simp[a,show ¬ (k+1<B'+1) by omega]
 rw[d B (fun j=>v.testBit j.val),testBit_mod_two_pow];by_cases a:k<B<;>simp[a]
theorem dv {B v:ℕ}(a:v<2^B):(∑ j:Fin B,(v.testBit j.val).toNat*2^j.val)=v:=(fk B v).trans (L8 a)
private def pa {w:ℕ}(z:Fin (2^w))(j:Fin w):Y0:=z.val.testBit j.val
private theorem ik {w:ℕ}:Function.Bijective (pa (w:=w)):=by
 refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_,by simp⟩;intro a b e;apply L6;apply Nat.eq_of_testBit_eq;intro j;by_cases d:j<w
 . exact congrFun e ⟨j,d⟩
 . have c:2^w<=2^j:=pow_le_pow_right (by decide) (by omega);rw[V2 (a.isLt.trans_le c),V2 (b.isLt.trans_le c)]
noncomputable def fs {w:ℕ}(f:Fin w->Y0):ℕ:=((Equiv.ofBijective pa ik).symm f).val
theorem jk {w:ℕ}(f:Fin w->Y0):fs f<2^w:=Fin.isLt _
theorem il {w:ℕ}(f:Fin w->Y0)(j:Fin w):(fs f).testBit j.val=f j:=congrFun ((Equiv.ofBijective pa ik).apply_symm_apply f) j
theorem ex {w:ℕ}(f:Fin w->Y0):fs f=∑ j:Fin w,(f j).toNat*2^j.val:=by rw[<-dv (jk f)];simp only[il]
end BitHelpers
end S393
namespace BuildExt
open S393.Compiler.Build
open scoped BigOperators
variable {N:ℕ}
lemma ol {w:ℕ} {A:Set (d4 N)} (c:ℕ) (F:(Fin N->Y0)->ℕ)
 (g:(fun _=>false)∈A) (n:(fun _=>true)∈A)
 (o:i9 A (a9 w F)):
 Build A (R0 (a9 w (fun x=>c*F x))) (w*(9*w)):=by
 let term (k:Fin w) (x:Fin N->Y0):ℕ:=if c.testBit k.val then 2^k.val*F x else 0
 have d:∀ k∈(univ:V7 (Fin w)),i9 A (a9 w (term k)):=by
  intro k _ j;by_cases b:c.testBit k.val=true
  . by_cases f:k.val<=j.val
    . have a:a9 w (term k) j=a9 w F ⟨j.val-k.val,by omega⟩:=(by funext x;dsimp only[a9,term];rw[Q2 b,Nat.testBit_two_pow_mul];simp[f]);rw[a];exact o _
    . have a:a9 w (term k) j=fun _=>false:=(by funext x;dsimp only[a9,term];rw[Q2 b,Nat.testBit_two_pow_mul];simp[f]);rw[a];exact g
  . have a:a9 w (term k) j=fun _=>false:=(by funext x;dsimp only[a9,term];rw[Q3 b];simp);rw[a];exact g
 have H:=dh (A:=A) (w:=w) univ term g n d
 have h:a9 w (fun x=>∑ k:Fin w,term k x)=a9 w (fun x=>c*F x):=by
  funext j x;dsimp only[a9]
  have l:(∑ k:Fin w,term k x)=(c %2^w)*F x:=by
   have e:(∑ k:Fin w,term k x)=(∑ k:Fin w,(c.testBit k.val).toNat*2^k.val)*F x:=by
    rw[sum_mul];refine L3 rfl fun k _=>?_;dsimp only[term];cases hc:c.testBit k.val<;>simp
   rw[e,S393.fk]
  rw[l];have i:((c %2^w)*F x) %2^w=(c*F x) %2^w:=(by rw[Nat.mul_mod,mod_mod,<-Nat.mul_mod]);have e:=testBit_mod_two_pow ((c %2^w)*F x) w j.val;have m:=testBit_mod_two_pow (c*F x) w j.val;rw[show decide (j.val<w)=true from decide_eq_true j.isLt,Bool.true_and] at e m;rw[<-e,<-m,i]
 rw[h] at H;simpa only[W2,Q9] using H
lemma rk {A:Set (d4 N)}{f g:d4 N}(c:f∈A)(b:g∈A):Build A {fun x=>f x == g x} 5:=by
 have a:(fun x=>f x == g x)=nt (xo f g):=by
  funext x;dsimp only[nt,xo];cases f x<;>cases g x<;>rfl
 rw[a];exact i7 (qr c b) (ae (inr rfl))
lemma ll {w:ℕ} {A:Set (d4 N)} (v:ℕ) (a:Fin w->d4 N)
 (d:(fun _=>true)∈A) (b:∀ j:Fin w,a j∈A):
 Build A {fun x=>decide (∀ j:Fin w,a j x=v.testBit j.val)} (2*w):=by
 let lit (j:Fin w):d4 N:=if v.testBit j.val then a j else nt (a j)
 have H1:Build A (R0 lit) w:=by
  simpa only[Nat.mul_one] using au lit 1 (fun j=>by
   dsimp only[lit];split_ifs
   . exact d9 (s6 (Q1 (b j))) Y3 Y3 (by decide)
   . exact ae (b j))
 let L:List (d4 N):=ofFn lit
 have H2:Build (A∪R0 lit) {fun x=>L.all (fun f=>f x)} w:=by
  simpa only[L,U7] using
   ox (A:=A∪R0 lit) L
    (fun f c=>by rw[mem_ofFn] at c;obtain⟨j,rfl⟩:=c;exact inr ⟨j,rfl⟩) (inl d)
 have e:(fun x=>L.all (fun f=>f x))=fun x=>decide (∀ j:Fin w,a j x=v.testBit j.val):=by
  funext x;apply L5
  simp only[L,all_eq_true,mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,L0];refine forall_congr' fun j=>?_;cases hv:v.testBit j.val<;>simp[lit,nt,hv]
 rw[e] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
lemma rd {w:ℕ} {A:Set (d4 N)} (u v:Fin w->d4 N)
 (b:(fun _=>true)∈A) (c:∀ j,u j∈A) (d:∀ j,v j∈A):
 Build A {fun x=>decide (∀ j:Fin w,u j x=v j x)} (6*w):=by
 let eqs (j:Fin w):d4 N:=fun x=>u j x == v j x;have H1:Build A (R0 eqs) (w*5):=au eqs 5 (fun j=>rk (c j) (d j));let L:List (d4 N):=ofFn eqs
 have H2:Build (A∪R0 eqs) {fun x=>L.all (fun f=>f x)} w:=by
  simpa only[L,U7] using
   ox (A:=A∪R0 eqs) L
    (fun f a=>by rw[mem_ofFn] at a;obtain⟨j,rfl⟩:=a;exact inr ⟨j,rfl⟩) (inl b)
 have e:(fun x=>L.all (fun f=>f x))=fun x=>decide (∀ j:Fin w,u j x=v j x):=by
  funext x;apply L5
  simp only[L,all_eq_true,mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,eqs,beq_iff_eq,L0]
 rw[e] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
lemma w3 {k:ℕ} {A:Set (d4 N)} (f:Fin k->d4 N)
 (a:(fun _=>false)∈A) (d:∀ i:Fin k,f i∈A):
 Build A {fun x=>decide (∃ i:Fin k,f i x=true)} k:=by
 have H:=rn (A:=A) (ofFn f)
  (fun g b=>by rw[mem_ofFn] at b;obtain⟨i,rfl⟩:=b;exact d i) a
 have c:(fun x=>(ofFn f).any (fun g=>g x))=fun x=>decide (∃ i:Fin k,f i x=true):=by
  funext x;apply L5
  simp only[List.any_eq_true,mem_ofFn,exists_exists_eq_and,L0]
 rw[c,U7] at H;exact H
lemma er {k:ℕ} {A:Set (d4 N)} (f:Fin k->d4 N)
 (a:(fun _=>true)∈A) (d:∀ i:Fin k,f i∈A):
 Build A {fun x=>decide (∀ i:Fin k,f i x=true)} k:=by
 have H:=ox (A:=A) (ofFn f)
  (fun g b=>by rw[mem_ofFn] at b;obtain⟨i,rfl⟩:=b;exact d i) a
 have c:(fun x=>(ofFn f).all (fun g=>g x))=fun x=>decide (∀ i:Fin k,f i x=true):=by
  funext x;apply L5
  simp only[all_eq_true,mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,L0]
 rw[c,U7] at H;exact H
lemma bi {w:ℕ} {A:Set (d4 N)} {a:Type*} [Fintype a]
 (c:a->d4 N) (b:a->ℕ) (F:a->(Fin N->Y0)->ℕ)
 (e:(fun _=>false)∈A) (d:(fun _=>true)∈A)
 (f:∀ i,c i∈A) (g:∀ i,i9 A (a9 w (F i))):
 Build A (R0 (a9 w (fun x=>∑ i:a,if c i x then b i*F i x else 0)))
  (W0 a*(w*(9*w)+10*w)):=by
 let G (i:a) (x:Fin N->Y0):ℕ:=b i*F i x
 have H1:=p7 (fun i=>R0 (a9 w (G i))) (w*(9*w))
  (fun i=>ol (b i) (F i) e d (g i))
 have H2:=gh (A:=A∪m0 univ (fun i=>R0 (a9 w (G i))))
  (w:=w) c G (inl e) (inl d) (fun i=>inl (f i))
  (fun i j=>inr (q3 (i:=i) ⟨j,rfl⟩))
 exact d9 (i7 H1 H2) Y3 Y3 (by rw[Nat.mul_add])
lemma z3 {B:ℕ} (F G:(Fin N->Y0)->ℕ)
 (h:∀ x,F x %2^B=G x %2^B):a9 B F=a9 B G:=by
 funext j x;dsimp only[a9]
 have b:=testBit_mod_two_pow (F x) B j.val;have a:=testBit_mod_two_pow (G x) B j.val;rw[show decide (j.val<B)=true from decide_eq_true j.isLt,Bool.true_and] at b a;rw[<-b,<-a,h x]
lemma pb {B:ℕ} {A:Set (d4 N)} (F G:(Fin N->Y0)->Z2 B)
 (c:(fun _=>false)∈A)
 (b:i9 A (a9 B (fun x=>(F x).val)))
 (d:i9 A (a9 B (fun x=>(G x).val))):
 Build A (R0 (a9 B (fun x=>(F x+G x).val))) (9*B):=by
 have:NeZero (2^B):=⟨W7 (by positivity)⟩;have a:a9 B (fun x=>(F x+G x).val)=a9 B (fun x=>(F x).val+(G x).val):=z3 _ _ (fun x=>by rw[ZMod.val_add,mod_mod]);rw[a];exact jv B _ _ c b d
lemma im {B:ℕ} {A:Set (d4 N)} (F:(Fin N->Y0)->Z2 B)
 (c:(fun _=>false)∈A) (e:(fun _=>true)∈A)
 (g:i9 A (a9 B (fun x=>(F x).val))):
 Build A (R0 (a9 B (fun x=>(-F x).val))) (10*B):=by
 have:NeZero (2^B):=⟨W7 (by positivity)⟩;let C (x:Fin N->Y0):ℕ:=2^B-((F x).val+1)
 have a:a9 B C=fun j=>nt (a9 B (fun x=>(F x).val) j):=by
  funext j x
  simpa[a9,C,nt,j.isLt] using Nat.testBit_two_pow_sub_succ (F x).val_lt j.val
 have H1:Build A (R0 (a9 B C)) B:=by rw[a];exact oy g
 have H2:=jv (A:=A∪R0 (a9 B C)) B C (fun _=>1) (inl c)
  (fun j=>inr ⟨j,rfl⟩) (fun j=>by
   change (fun _=>(1:ℕ).testBit j.val)∈_;cases (1:ℕ).testBit j.val
   . exact inl c
   . exact inl e)
 have f:a9 B (fun x=>C x+1)=a9 B (fun x=>(-F x).val):=z3 _ _ (fun x=>by
   have d:=(F x).val_lt;have h:C x+1=2^B-(F x).val:=(by dsimp[C];omega);have b:((2^B-(F x).val:ℕ):Z2 B)=-F x:=by rw[Nat.cast_sub (le_of_lt d),ZMod.natCast_self,ZMod.natCast_zmod_val,zero_sub]
   rw[h,<-b,val_natCast,mod_mod])
 rw[f] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
lemma ek {B:ℕ} {A:Set (d4 N)} (F G:(Fin N->Y0)->Z2 B)
 (a:(fun _=>false)∈A) (b:(fun _=>true)∈A)
 (c:i9 A (a9 B (fun x=>(F x).val)))
 (d:i9 A (a9 B (fun x=>(G x).val))):
 Build A (R0 (a9 B (fun x=>(F x-G x).val))) (19*B):=by
 have H1:=im G a b d
 have H2:=pb (A:=A∪R0 (a9 B (fun x=>(-G x).val))) F (fun x=>-G x)
  (inl a) (fun j=>inl (c j)) (fun j=>inr ⟨j,rfl⟩)
 have e:(fun x=>(F x+-G x).val)=fun x=>(F x-G x).val:=(by funext x;rw[sub_eq_add_neg]);rw[e] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
lemma cf {B:ℕ} {A:Set (d4 N)} (c:Z2 B) (F:(Fin N->Y0)->Z2 B)
 (e:(fun _=>false)∈A) (b:(fun _=>true)∈A)
 (d:i9 A (a9 B (fun x=>(F x).val))):
 Build A (R0 (a9 B (fun x=>(c*F x).val))) (B*(9*B)):=by
 have:NeZero (2^B):=⟨W7 (by positivity)⟩;have a:a9 B (fun x=>(c*F x).val)=a9 B (fun x=>c.val*(F x).val):=z3 _ _ (fun x=>by rw[ZMod.val_mul,mod_mod]);rw[a];exact ol c.val _ e b d
lemma cv {B:ℕ} {A:Set (d4 N)} {b:Type*} [Fintype b]
 (a:b->Z2 B) (F:b->(Fin N->Y0)->Z2 B)
 (e:(fun _=>false)∈A) (d:(fun _=>true)∈A)
 (f:∀ i,i9 A (a9 B (fun x=>(F i x).val))):
 Build A (R0 (a9 B (fun x=>(∑ i:b,a i*F i x).val)))
  (W0 b*(B*(9*B)+9*B)):=by
 have:NeZero (2^B):=⟨W7 (by positivity)⟩;let G (i:b) (x:Fin N->Y0):ℕ:=(a i*F i x).val
 have H1:=p7 (fun i=>R0 (a9 B (G i))) (B*(9*B))
  (fun i=>cf (a i) (F i) e d (f i))
 have H2:=dh (A:=A∪m0 univ (fun i=>R0 (a9 B (G i))))
  (w:=B) univ G (inl e) (inl d)
  (fun i _ j=>inr (q3 (i:=i) ⟨j,rfl⟩))
 have g:a9 B (fun x=>∑ i:b,G i x)=a9 B (fun x=>(∑ i:b,a i*F i x).val):=z3 _ _ (fun x=>by
   have c:((∑ i:b,G i x:ℕ):Z2 B)=∑ i:b,a i*F i x:=by rw[Nat.cast_sum];refine L3 rfl fun i _=>ZMod.natCast_zmod_val _
   rw[<-c,val_natCast,mod_mod])
 rw[g] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by simp[Nat.mul_add])
def x9 (B2 M:ℕ)(b:Fin M->Y0)(a:ℕ):ℕ:=∑ k:Fin M,if b k then (a/2^k.val) %2^B2 else 0
lemma gu {B2 M:ℕ} {d:Fin M->Y0} {b:Fin M}
 (c:∀ k:Fin M,d k=decide (k=b)) (a:ℕ):
 x9 B2 M d a=(a/2^b.val) %2^B2:=by
 unfold x9;rw[Q4 b]
 . simp[c b]
 . intro k _ e;simp[c k,e]
 . intro h;exact absurd (Y2 _) h
lemma ln {B1 B2 M:ℕ} {A:Set (d4 N)}
 (a:Fin M->d4 N) (F:(Fin N->Y0)->ℕ)
 (f:(fun _=>false)∈A) (h:(fun _=>true)∈A)
 (d:∀ k,a k∈A) (i:i9 A (a9 B1 F)) (b:∀ x,F x<2^B1):
 Build A (R0 (a9 B2 (fun x=>x9 B2 M (fun k=>a k x) (F x))))
  (M*(10*B2)):=by
 have e:∀ k:Fin M,i9 A (a9 B2 (fun x=>(F x/2^k.val) %2^B2)):=by
  intro k j;by_cases g:j.val+k.val<B1
  . have c:a9 B2 (fun x=>(F x/2^k.val) %2^B2) j=a9 B1 F ⟨j.val+k.val,g⟩:=by
     funext x;dsimp only[a9]
     rw[testBit_mod_two_pow,show decide (j.val<B2)=true from decide_eq_true j.isLt,Bool.true_and,Nat.testBit_div_two_pow,Nat.add_comm]
    rw[c];exact i _
  . have c:a9 B2 (fun x=>(F x/2^k.val) %2^B2) j=fun _=>false:=by
     funext x;dsimp only[a9]
     rw[testBit_mod_two_pow,show decide (j.val<B2)=true from decide_eq_true j.isLt,Bool.true_and,Nat.testBit_div_two_pow,Nat.add_comm];exact V2 ((b x).trans_le (pow_le_pow_right (by omega) (by omega)))
    rw[c];exact f
 simpa only[Q9,x9] using
  gh (w:=B2) a (fun k x=>(F x/2^k.val) %2^B2) f h d e
def g9 {D1 D2 B:ℕ}(P:(Fin N->Y0)->S399.a8 D1 D2 (Z2 B)):Set (d4 N):=m0 (univ:V7 (Fin D1×Fin D2))
  (fun p=>R0 (a9 B (fun x=>((P x).coeff p.1 p.2).val)))
lemma v8 {D1 D2 B:ℕ} {P:(Fin N->Y0)->S399.a8 D1 D2 (Z2 B)}
 (i:Fin D1) (j:Fin D2) (b:Fin B):
 a9 B (fun x=>((P x).coeff i j).val) b∈g9 P:=
 q3 (i:=(i,j)) ⟨b,rfl⟩
lemma nl {D1 D2 B:ℕ} {A:Set (d4 N)}
 (C:S399.a8 D1 D2 (Z2 B))
 (P:(Fin N->Y0)->S399.a8 D1 D2 (Z2 B))
 (c:(fun _=>false)∈A) (d:(fun _=>true)∈A) (e:g9 P⊆A):
 Build A (g9 (fun x=>C*P x))
  ((D1*D2)*((D1*D2)*(B*(9*B)+9*B))):=by
 have g:Build A (g9 (fun x=>C*P x))
  (W0 (Fin D1×Fin D2)*(W0 (Fin D1×Fin D2)*(B*(9*B)+9*B))):=by
  apply p7;rintro⟨i,j⟩;let coeffs (p:Fin D1×Fin D2):Z2 B:=if p.1.val<=i.val/\p.2.val<=j.val then C.coeff p.1 p.2 else 0
  let F (p:Fin D1×Fin D2) (x:Fin N->Y0):Z2 B:=if h:p.1.val<=i.val/\p.2.val<=j.val then (P x).coeff ⟨i.val-p.1.val,by omega⟩ ⟨j.val-p.2.val,by omega⟩
   else 0
  have f:∀ p,i9 A (a9 B (fun x=>(F p x).val)):=fun p b=>by
   dsimp only[F];split_ifs with h
   . exact e (v8 _ _ b)
   . have a:a9 B (fun _:Fin N->Y0=>(0:Z2 B).val) b=fun _=>false:=(by funext x;simp[a9]);rw[a];exact c
  have H:=cv coeffs F c d f
  have a:(fun x=>((C*P x).coeff i j).val)=fun x=>(∑ p:Fin D1×Fin D2,coeffs p*F p x).val:=by
   funext x;congr 1
   rw[S399.kc,sum_prod_type];refine L3 rfl fun i1 _=>L3 rfl fun j1 _=>?_;dsimp only[coeffs,F];split_ifs<;>simp
  rw[a];exact H
 simpa only[J3,Q9] using g
lemma bb {D1 D2 B K:ℕ} {A:Set (d4 N)}
 (a:S399.a8 D1 D2 (Z2 B))
 (c:(Fin N->Y0)->ℕ) (P:(Fin N->Y0)->S399.a8 D1 D2 (Z2 B))
 (q:(fun _=>false)∈A) (o:(fun _=>true)∈A)
 (f:i9 A (a9 K c)) (w:g9 P⊆A):
 Build A (g9 (fun x=>a^(c x %2^K)*P x))
  (K*((D1*D2)*((D1*D2)*(B*(9*B)+9*B))+(D1*D2)*(B*4))):=by
 let stage (k:ℕ) (x:Fin N->Y0):S399.a8 D1 D2 (Z2 B):=a^(c x %2^k)*P x;let O (k:ℕ):=g9 (stage k);have p:Build A (O 0) 0:=by have r:stage 0=P:=(by funext x;dsimp only[stage];rw[pow_zero,Nat.mod_one,pow_zero,one_mul]);rw[show O 0=g9 P by simp[O,r]];exact s6 w
 have H:=ew (t:=K) O p (fun k m=>by
  let Bset:=A∪O k;let mulP (x:Fin N->Y0):=a^(2^k)*stage k x
  have H1:=nl (A:=Bset) (a^(2^k)) (stage k)
   (inl q) (inl o) M9
  let Cset:=Bset∪g9 mulP;let e:d4 N:=a9 K c ⟨k,m⟩
  have H2:Build Cset (O (k+1)) ((D1*D2)*(B*4)):=by
   have g:Build Cset (O (k+1)) (W0 (Fin D1×Fin D2)*(B*4)):=by
    apply p7;rintro⟨i,j⟩
    have n:=kf (A:=Cset) (s:=e)
     (v:=a9 B (fun x=>((stage k x).coeff i j).val))
     (u:=a9 B (fun x=>((mulP x).coeff i j).val))
     (inl (inl (f ⟨k,m⟩)))
     (fun b=>inl (inr (v8 i j b)))
     (fun b=>inr (v8 i j b))
    have l:(fun b=>mx e (a9 B (fun x=>((stage k x).coeff i j).val) b)
     (a9 B (fun x=>((mulP x).coeff i j).val) b))=
     a9 B (fun x=>((stage (k+1) x).coeff i j).val):=by
     funext b x;dsimp only[mx,e,a9,stage,mulP]
     rw[cm (c x) k];by_cases d:(c x).testBit k=true
     . simp only[d,↓reduceIte,X6,mul_assoc,mul_comm (a^(c x %2^k))]
     . have h:(c x).testBit k=false:=Bool.eq_false_iff.mpr d;simp only[h,J5,↓reduceIte,add_zero]
    rw[l] at n;exact n
   simpa only[J3,Q9] using g
  exact i7 H1 H2)
 simpa only[Nat.zero_add,O,stage] using H
end BuildExt
namespace StageA
open S399 BuildExt
open S393.Compiler.Build
open scoped BigOperators
def N0 (n:ℕ):ℕ:=2+(n+1)*(n+1)*(2*n+1)+8*n
def Bw (n:ℕ):ℕ:=2*n+10
def o8 (n:ℕ):ℕ:=4*n+10
def c5 (n:ℕ):Perm (Fin n) where
 toFun i:=⟨(i.val+1) %n,M1 _ (K2 (by intro h;subst h;exact elim0 i))⟩
 invFun i:=⟨(i.val+n-1) %n,M1 _ (K2 (by intro h;subst h;exact elim0 i))⟩
 left_inv i:=by
  apply L6;dsimp only;have b:=i.isLt;have c:0<n:=K2 (by intro h;subst h;exact elim0 i);by_cases h:i.val+1=n
  . rw[h,mod_self,zero_add,L8 (by omega)];omega
  . rw[L8 (a:=i.val+1) (by omega),show i.val+1+n-1=i.val+n by omega,M2,L8 b]
 right_inv i:=by
  apply L6;dsimp only;have b:=i.isLt;have c:0<n:=K2 (by intro h;subst h;exact elim0 i);by_cases h:i.val=0
  . rw[h,zero_add,L8 (a:=n-1) (by omega),show n-1+1=n by omega,mod_self]
  . rw[show i.val+n-1=(i.val-1)+n by omega,M2,L8 (a:=i.val-1) (by omega),show i.val-1+1=i.val by omega,L8 b]
lemma ob (t:ℕ)(i:Fin (t+1)):c5 (t+1) i=i+1:=by apply L6;change (i.val+1) %(t+1)=(i.val+(1 %(t+1))) %(t+1);simp[add_mod]
lemma cx {A B:ℕ}(i:Fin A){j:ℕ}(a:j<B):i.val*B+j<A*B:=by have h:=W4 B (Nat.succ_le_of_lt i.isLt);rw[succ_mul] at h;omega
def aj (n:ℕ)(r b:Fin (n+1))(k:Fin (2*n+1)):Fin (N0 n):=⟨2+(r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val)),by
  unfold N0;have h:=cx r (cx b k.isLt);linarith⟩
def u4 (n:ℕ)(x:F0 (N0 n))(r b:Fin (n+1)):ℕ:=∑ k:Fin (2*n+1),(x (aj n r b k)).toNat*2^k.val
lemma kh (n:ℕ)(x:F0 (N0 n))(r b:Fin (n+1)):u4 n x r b<2^(2*n+1):=by have a:u4 n x r b=S393.fs (fun k=>x (aj n r b k)):=(S393.ex _).symm;rw[a];exact S393.jk _
lemma jl (n:ℕ)(x:F0 (N0 n))(r b:Fin (n+1))(k:Fin (2*n+1)):(u4 n x r b).testBit k.val=x (aj n r b k):=by have a:u4 n x r b=S393.fs (fun k=>x (aj n r b k)):=(S393.ex _).symm;rw[a];exact S393.il _ k
def av (n:ℕ)(x:F0 (N0 n))(h:Fin 3)(s:Fin (2*n+1)):ZMod (2^o8 n):=(profile (u4 n x) h.val s:ZMod (2^o8 n))
def q9 (n:ℕ)(x:F0 (N0 n)):ZMod (2^o8 n):=∑ s:Fin (2*n+1),av n x 0 s
noncomputable def ko (n:ℕ)(x:F0 (N0 n)):a8 3 (2*n+1) (ZMod (2^o8 n)):=⟨fun h d=>((w0 (fun k s=>profile (u4 n x) k.val s)).coeff h d:ZMod (2^o8 n))⟩
noncomputable def di (n:ℕ)(x:F0 (N0 n)):a8 3 (2*n+1) (Z2 (Bw n)):=⟨fun h d=>(x9 (Bw n) (2*n+1) (fun k=>(q9 n x).val.testBit k.val) ((ko n x).coeff h d).val:Z2 (Bw n))⟩
noncomputable def o3 {D2Z D1U D2U:ℕ} (B K:ℕ)
 (e:a8 3 D2Z (Z2 B)) (b:a8 D1U D2U (Z2 B))
 (g:Z2 B) (h:a8 3 D2Z (Z2 B)×a8 D1U D2U (Z2 B)):
 a8 3 D2Z (Z2 B)×a8 D1U D2U (Z2 B):=
 let a:=g.val.testBit (B-1);let f:=if a then (-g).val else g.val;let c:=if a then 0 else f;let d:=if a then f else 0
 ((1-e)^(d %2^K)*(a8.r5 e^(c %2^K)*h.1),(a8.r5 b)^(d %2^K)*((1-b)^(c %2^K)*h.2))
lemma o7 {D2Z D1U D2U B K:ℕ} (r:2<=B)
 (e:a8 3 D2Z (Z2 B)) (b:a8 D1U D2U (Z2 B))
 (p:Z2 B) (c:ℤ) (o:p=(c:Z2 B))
 (m:-(2^(B-1):ℤ)<c) (n:c<2^(B-1)) (h:c.natAbs<2^K)
 (j:a8 3 D2Z (Z2 B)×a8 D1U D2U (Z2 B)):
 o3 B K e b p j=(a8.c8 e (-c)*j.1,a8.c8 b c*j.2):=by
 obtain⟨l,a,_⟩:=li r c ⟨m,n⟩;subst o;unfold o3 a8.c8;rw[l];by_cases d:c<0
 . simp only[d,decide_true,↓reduceIte] at a ⊢;rw[a,L8 h];have i:0<=-c:=(by omega);have g:¬ 0<=c:=(by omega);have f:(-c).toNat=c.natAbs:=(by omega);simp only[i,g,f,↓reduceIte,zero_mod,pow_zero,one_mul,mul_one,neg_neg]
 . simp only[d,decide_false,J5,↓reduceIte] at a ⊢;rw[a,L8 h];by_cases q:c=0
   . subst q;simp only[Int.natAbs_zero,zero_mod,le_refl,neg_zero,Int.toNat_zero,↓reduceIte,pow_zero,one_mul,mul_one]
   . have i:0<=c:=(by omega);have g:¬ 0<=-c:=(by omega);have f:c.toNat=c.natAbs:=(by omega);have k:(-(-c)).toNat=c.natAbs:=(by omega);simp only[i,g,f,k,↓reduceIte,zero_mod,pow_zero,one_mul,mul_one]
abbrev pc (n B:ℕ):=(a8 3 (2*n+1) (Z2 B)×a8 (n+1) (n+1) (Z2 B))×
  (ℕ->ℕ->Z2 B)
abbrev qc (n:ℕ):=pc n (Bw n)
noncomputable def l7 (n B:ℕ)(j:Fin (2*n))(a:pc n B):pc n B:=let K:=n+2
 let l:=j.val+1;let c:=-(a.1.1.coeff 0 ⟨l,by omega⟩);let k:=-(a.1.1.coeff 1 ⟨l,by omega⟩);let p:=-(a.1.1.coeff 2 ⟨l,by omega⟩)
 if l %2=1 then let m:=l/2
  let i:=k-(m:Z2 B)*c;let f:=c-i;let b:=o3 B K (v9 n B l m) (y4 n B l m) f a.1;let g:=o3 B K (v9 n B l (m+1)) (y4 n B l (m+1)) i b
  (g,fun q s=>if q=l then (if s=m then f else if s=m+1 then i else 0) else a.2 q s)
 else if l %4=0 then let b:=o3 B K (v9 n B l (l/2)) (y4 n B l (l/2)) c a.1
  (b,fun q s=>if q=l then (if s=l/2 then c else 0) else a.2 q s)
 else let m:=l/2
  let e:=k-(m:Z2 B)*c;let d:=(p-(choose m 2:Z2 B)*c)-(m:Z2 B)*e;let h:=d+e;let f:=(c-d)-h;let b:=o3 B K (v9 n B l (m-1)) (y4 n B l (m-1)) d a.1;let g:=o3 B K (v9 n B l m) (y4 n B l m) f b;let o:=o3 B K (v9 n B l (m+1)) (y4 n B l (m+1)) h g
  (o,fun q s=>if q=l then (if s=m-1 then d else if s=m then f else if s=m+1 then h else 0) else a.2 q s)
noncomputable def eg (n:ℕ)(a:Fin (2*n))(b:qc n):qc n:=l7 n (Bw n) a b
noncomputable def f7 (n:ℕ)(x:F0 (N0 n)):ℕ->qc n
 | 0=>((di n x,1),fun _ _=>0)
 | k+1=>if h:k<2*n then eg n ⟨k,h⟩ (f7 n x k) else f7 n x k
noncomputable def ia (n:ℕ)(x:F0 (N0 n)):a8 (n+1) (n+1) (Z2 (Bw n)):=(f7 n x (2*n)).1.2
noncomputable def cy (n:ℕ)(x:F0 (N0 n))(l r:ℕ):Z2 (Bw n):=(f7 n x (2*n)).2 l r
noncomputable def z6 (n:ℕ)(x:F0 (N0 n)):a8 (n+1) (n+1) (Z2 (Bw n)):=⟨fun a j=>∑ i:Fin (n+1),(c6 n i.val a.val:Z2 (Bw n))*(ia n x).coeff i j⟩
noncomputable def z4 (n:ℕ)(x:F0 (N0 n)):a8 (n+1) (n+1) (Z2 (Bw n)):=⟨fun a b=>∑ j:Fin (n+1),(c6 n j.val b.val:Z2 (Bw n))*(z6 n x).coeff a j⟩
noncomputable def ac (n:ℕ)(x:F0 (N0 n))(a b:Fin (n+1)):ℕ:=x9 (2*n+1) (2*n+1)
  (fun k=>(q9 n x).val.testBit (2*n-k.val))
  ((z4 n x).coeff a b).val %2^(2*n+1)
lemma lo {n B:ℕ} (hn:1<=n) (hB:B=2*n+10) (g:2<=B)
 (c:Fin (2*n)) (i:(a8 3 (2*n+1) (Z2 B)×a8 (n+1) (n+1) (Z2 B))×(ℕ->ℕ->Z2 B))
 (q:P0 n)
 (hR:i.1.1=y7 n B (c5 n) q c.val)
 (hP:i.1.2=ar n B (c5 n) q c.val)
 (hW:∀ l'∈Icc 1 c.val,∀ r'∈(c4 l').toFinset,i.2 l' r'=(e9 (c5 n) q l' r':Z2 B)):
 let h7:=l7 n B c i
 h7.1.1=y7 n B (c5 n) q (c.val+1) ∧
 h7.1.2=ar n B (c5 n) q (c.val+1) ∧
 ∀ l'∈Icc 1 (c.val+1),∀ r'∈(c4 l').toFinset,h7.2 l' r'=(e9 (c5 n) q l' r':Z2 B):=by
 dsimp only;unfold l7;dsimp only;let l:=c.val+1
 have e:∀ h:Fin 3,-(i.1.1.coeff h ⟨l,by omega⟩)=∑ r'∈(c4 l).toFinset,(choose r' h.val:Z2 B)*(e9 (c5 n) q l r':Z2 B):=by
  intro h;rw[hR,lk (c5 n) q c h,<-Finset.sum_neg_distrib];refine L3 rfl fun r' _=>by ring
 split_ifs with v h4
 . set m:=l/2;have b:(c4 l).toFinset={m,m+1}:=(by ext a;simp[c4,l,v,m]);have v1:m≠m+1:=(by omega);have d:=e 0;have k:=e 1;rw[b,V6 v1] at d k;simp only[val_zero,val_one,U8,U9,Nat.cast_one,one_mul,Nat.cast_add] at d k
   have o:=nk (m:Z2 B)
    (e9 (c5 n) q l m:Z2 B) (e9 (c5 n) q l (m+1):Z2 B)
   have h9:-(i.1.1.coeff 1 ⟨l,by omega⟩)-(m:Z2 B)*-(i.1.1.coeff 0 ⟨l,by omega⟩)=(e9 (c5 n) q l (m+1):Z2 B):=by rw[d,k];exact o.1
   have t:-(i.1.1.coeff 0 ⟨l,by omega⟩) -
    (-(i.1.1.coeff 1 ⟨l,by omega⟩)-(m:Z2 B)*-(i.1.1.coeff 0 ⟨l,by omega⟩))=
    (e9 (c5 n) q l m:Z2 B):=by rw[h9,d];ring
   obtain⟨z,x⟩:=q8 hB (c5 n) q l m;obtain⟨x1,a1⟩:=q8 hB (c5 n) q l (m+1);rw[o7 g _ _ _ _ t z x (p3 hn (c5 n) q l m),o7 g _ _ _ _ h9 x1 a1 (p3 hn (c5 n) q l (m+1)),hR,hP];dsimp only;refine⟨?_,?_,fun l' b0 r' b2=>?_⟩
   . rw[<-mul_assoc];have hp:a8.c8 (v9 n B l (m+1)) (-e9 (c5 n) q l (m+1)) *a8.c8 (v9 n B l m) (-e9 (c5 n) q l m)=∏ r'∈(c4 l).toFinset,a8.c8 (v9 n B l r') (-e9 (c5 n) q l r'):=(by rw[b,prod_pair v1];ring);rw[hp];exact dr (c5 n) q c
   . rw[<-mul_assoc];have hp:a8.c8 (y4 n B l (m+1)) (e9 (c5 n) q l (m+1)) *a8.c8 (y4 n B l m) (e9 (c5 n) q l m)=∏ r'∈(c4 l).toFinset,a8.c8 (y4 n B l r') (e9 (c5 n) q l r'):=(by rw[b,prod_pair v1];ring);rw[hp];exact du (c5 n) q c
   . by_cases j:l'=c.val+1
     . subst j;rw[b] at b2;simp only[X3,U5] at b2
       rcases b2 with rfl|rfl
       . rw[Q2 rfl,Q2 rfl,<-hR];exact t
       . rw[Q2 rfl,Q3 (by omega),Q2 rfl,<-hR];exact h9
     . simp only[j,↓reduceIte];exact hW l' (J4.mpr ⟨(J4.mp b0).1,by have:=(J4.mp b0).2;omega⟩) r' b2
 . have b:(c4 l).toFinset={l/2}:=(by ext a;simp[c4,l,v,h4]);have d:=e 0;rw[b,sum_singleton] at d;simp only[val_zero,U8,Nat.cast_one,one_mul] at d;obtain⟨z,x⟩:=q8 hB (c5 n) q l (l/2);rw[o7 g _ _ _ _ d z x (p3 hn (c5 n) q l (l/2)),hR,hP];dsimp only;refine⟨by rw[<-prod_singleton (f:=fun r'=>a8.c8 (v9 n B l r') (-e9 (c5 n) q l r')),<-b];exact dr (c5 n) q c,by rw[<-prod_singleton (f:=fun r'=>a8.c8 (y4 n B l r') (e9 (c5 n) q l r')),<-b];exact du (c5 n) q c,fun l' b0 r' b2=>?_⟩;by_cases j:l'=c.val+1
   . subst j;rw[b,U5] at b2;subst b2;rw[Q2 rfl,Q2 rfl,<-hR];exact d
   . simp only[j,↓reduceIte];exact hW l' (J4.mpr ⟨(J4.mp b0).1,by have:=(J4.mp b0).2;omega⟩) r' b2
 . set m:=l/2;have a4:1<=m:=(by omega);have b:(c4 l).toFinset={m-1,m,m+1}:=(by ext a;simp[c4,l,v,h4,m]);have y:m-1∉({m,m+1}:V7 ℕ):=(by simp;omega);have u:m≠m+1:=(by omega);have d:=e 0;have k:=e 1;have h3:=e 2;rw[b,sum_insert y,V6 u] at d k h3;simp only[val_zero,val_one,val_two,U8,U9,Nat.cast_one,one_mul] at d k h3
   have o:=mg (R:=Z2 B) m a4
    (e9 (c5 n) q l (m-1):Z2 B)
    (e9 (c5 n) q l m:Z2 B)
    (e9 (c5 n) q l (m+1):Z2 B)
   set v0:=-(i.1.1.coeff 0 ⟨l,by omega⟩);set a6:=-(i.1.1.coeff 1 ⟨l,by omega⟩);set a7:=-(i.1.1.coeff 2 ⟨l,by omega⟩);set p:=a6-(m:Z2 B)*v0;set s:=a7-(choose m 2:Z2 B)*v0-(m:Z2 B)*p;set h8:=s+p;have w:s=(e9 (c5 n) q l (m-1):Z2 B):=(by dsimp only[s,p];rw[d,k,h3];convert o.1 using 1<;>ring);have h0:h8=(e9 (c5 n) q l (m+1):Z2 B):=(by dsimp only[h8,s,p];rw[d,k,h3];convert o.2.2 using 1<;>ring);have t:v0-s-h8=(e9 (c5 n) q l m:Z2 B):=(by rw[w,h0,d];ring);obtain⟨x2,y1⟩:=q8 hB (c5 n) q l (m-1);obtain⟨x0,a3⟩:=q8 hB (c5 n) q l m;obtain⟨a2,y2⟩:=q8 hB (c5 n) q l (m+1);rw[o7 g _ _ _ _ w x2 y1 (p3 hn (c5 n) q l (m-1)),o7 g _ _ _ _ t x0 a3 (p3 hn (c5 n) q l m),o7 g _ _ _ _ h0 a2 y2 (p3 hn (c5 n) q l (m+1)),hR,hP];dsimp only;refine⟨?_,?_,fun l' b0 r' b2=>?_⟩
   . rw[<-mul_assoc,<-mul_assoc];have hp:a8.c8 (v9 n B l (m+1)) (-e9 (c5 n) q l (m+1)) *a8.c8 (v9 n B l m) (-e9 (c5 n) q l m) *a8.c8 (v9 n B l (m-1)) (-e9 (c5 n) q l (m-1))=∏ r'∈(c4 l).toFinset,a8.c8 (v9 n B l r') (-e9 (c5 n) q l r'):=(by rw[b,prod_insert y,prod_pair u];ring);rw[hp];exact dr (c5 n) q c
   . rw[<-mul_assoc,<-mul_assoc];have hp:a8.c8 (y4 n B l (m+1)) (e9 (c5 n) q l (m+1)) *a8.c8 (y4 n B l m) (e9 (c5 n) q l m) *a8.c8 (y4 n B l (m-1)) (e9 (c5 n) q l (m-1))=∏ r'∈(c4 l).toFinset,a8.c8 (y4 n B l r') (e9 (c5 n) q l r'):=(by rw[b,prod_insert y,prod_pair u];ring);rw[hp];exact du (c5 n) q c
   . by_cases j:l'=c.val+1
     . subst j;rw[b] at b2;simp only[X3,U5] at b2
       rcases b2 with rfl|rfl|rfl
       . rw[Q2 rfl,Q2 rfl];exact w
       . rw[Q2 rfl,Q3 (by omega),Q2 rfl];exact t
       . rw[Q2 rfl,Q3 (by omega),Q3 (by omega),Q2 rfl];exact h0
     . simp only[j,↓reduceIte];exact hW l' (J4.mpr ⟨(J4.mp b0).1,by have:=(J4.mp b0).2;omega⟩) r' b2
lemma lq {n B:ℕ} (h:2<=B)
 (f:Fin (2*n)) (o:(a8 3 (2*n+1) (Z2 B)×a8 (n+1) (n+1) (Z2 B))×(ℕ->ℕ->Z2 B))
 (c:ℕ->ℕ->ℤ)
 (g:∀ r∈(c4 (f.val+1)).toFinset,(l7 n B f o).2 (f.val+1) r=(c (f.val+1) r:Z2 B)/\-(2^(B-1):ℤ)<c (f.val+1) r/\c (f.val+1) r<2^(B-1)/\(c (f.val+1) r).natAbs<2^(n+2)):
 (l7 n B f o).1.2=(∏ r∈(c4 (f.val+1)).toFinset,a8.c8 (y4 n B (f.val+1) r) (c (f.val+1) r))*o.1.2:=by
 unfold l7 at g ⊢;dsimp only at g ⊢;let l:=f.val+1
 split_ifs at g ⊢ with j s
 . set m:=l/2;have d:(c4 l).toFinset={m,m+1}:=(by ext a;simp[c4,l,j,m]);have q:m≠m+1:=(by omega);have b:=g m (by rw[d];simp);have e:=g (m+1) (by rw[d];simp);dsimp only at b e;rw[Q2 rfl,Q2 rfl] at b;rw[Q2 rfl,Q3 (by omega),Q2 rfl] at e;rw[o7 h _ _ _ _ b.1 b.2.1 b.2.2.1 b.2.2.2,o7 h _ _ _ _ e.1 e.2.1 e.2.2.1 e.2.2.2];dsimp only;rw[<-mul_assoc,d,prod_pair q];ring
 . have d:(c4 l).toFinset={l/2}:=(by ext a;simp[c4,l,j,s]);have b:=g (l/2) (by rw[d];simp);dsimp only at b;rw[Q2 rfl,Q2 rfl] at b;rw[o7 h _ _ _ _ b.1 b.2.1 b.2.2.1 b.2.2.2];dsimp only;rw[d,prod_singleton]
 . set m:=l/2;have d:(c4 l).toFinset={m-1,m,m+1}:=(by ext a;simp[c4,l,j,s,m]);have p:m-1∉({m,m+1}:V7 ℕ):=(by simp;omega);have k:m≠m+1:=(by omega);have b:=g (m-1) (by rw[d];simp);have e:=g m (by rw[d];simp);have i:=g (m+1) (by rw[d];simp);dsimp only at b e i;rw[Q2 rfl,Q2 rfl] at b;rw[Q2 rfl,Q3 (by omega),Q2 rfl] at e;rw[Q2 rfl,Q3 (by omega),Q3 (by omega),Q2 rfl] at i;rw[o7 h _ _ _ _ b.1 b.2.1 b.2.2.1 b.2.2.2,o7 h _ _ _ _ e.1 e.2.1 e.2.2.1 e.2.2.2,o7 h _ _ _ _ i.1 i.2.1 i.2.2.1 i.2.2.2];dsimp only;rw[<-mul_assoc,<-mul_assoc,d,prod_insert p,prod_pair k];ring
lemma kx {n:ℕ}(hn:1<=n)(x:F0 (N0 n)):(∀ q:P0 n,di n x=z9 (R:=Z2 (Bw n)) (c5 n) q->ia n x=u9 (R:=Z2 (Bw n)) (c5 n) q/\∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,cy n x l r=(e9 (c5 n) q l r:Z2 (Bw n)))/\(∀ c:ℕ->ℕ->ℤ,(∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,cy n x l r=(c l r:Z2 (Bw n))/\-(2^(Bw n-1):ℤ)<c l r/\c l r<2^(Bw n-1)/\(c l r).natAbs<2^(n+2))->ia n x=∏ l∈Icc 1 (2*n),∏ r∈(c4 l).toFinset,a8.c8 (y4 n (Bw n) l r) (c l r)):=by
 have hB:Bw n=2*n+10:=rfl;have j:2<=Bw n:=by unfold Bw;omega
 have w:∀ k (hk:k≤2*n),let b:=f7 n x k
  (∀ l r,k<l->b.2 l r=0) ∧
  (∀ q:P0 n,di n x=z9 (R:=Z2 (Bw n)) (c5 n) q->b.1.1=y7 n (Bw n) (c5 n) q k/\b.1.2=ar n (Bw n) (c5 n) q k/\∀ l∈Icc 1 k,∀ r∈(c4 l).toFinset,b.2 l r=(e9 (c5 n) q l r:Z2 (Bw n))) ∧
  (∀ c:ℕ->ℕ->ℤ,(∀ l∈Icc 1 k,∀ r∈(c4 l).toFinset,b.2 l r=(c l r:Z2 (Bw n))/\-(2^(Bw n-1):ℤ)<c l r/\c l r<2^(Bw n-1)/\(c l r).natAbs<2^(n+2))->b.1.2=∏ l∈Icc 1 k,∏ r∈(c4 l).toFinset,a8.c8 (y4 n (Bw n) l r) (c l r)):=by
  intro k
  induction k with
  | zero=>intro _;refine⟨fun _ _ _=>rfl,fun q o=>⟨by rw[f7,o];unfold y7;exact kd (c5 n) q,by simp[f7,ar],fun l i=>by simp at i⟩,fun c _=>by simp[f7]⟩
  | succ k ih=>
   intro hk;have t:k<2*n:=(by omega);obtain⟨s,f,e⟩:=ih (by omega);set d:Fin (2*n):=⟨k,t⟩;set l:=k+1;set b:=f7 n x k;have g:f7 n x (k+1)=eg n d b:=(by rw[f7,L7 t]);rw[g];have h:∀ l' r',l'≠l->(eg n d b).2 l' r'=b.2 l' r':=fun l' r' h0=>(by unfold eg l7;dsimp only;split_ifs<;>simp[h0,d,l]);have m:Icc 1 l=insert l (Icc 1 k):=(by ext a;simp only[J4,X3];omega);have y:l∉Icc 1 k:=(by simp[l]);refine⟨fun l' r' h6=>by rw[h l' r' (by omega)];exact s l' r' (by omega),?_,?_⟩
   . intro q o;obtain⟨hR,v,u⟩:=f q o;exact lo hn hB j d b q hR v u
   . intro c z
     have p:b.1.2=∏ l'∈Icc 1 k,∏ r'∈(c4 l').toFinset,a8.c8 (y4 n (Bw n) l' r') (c l' r'):=e c (fun l' h6 r' h8=>by
       have hm:=z l' (J4.mpr ⟨(J4.mp h6).1,by have:=(J4.mp h6).2;omega⟩) r' h8
       rwa[h l' r' (by have:=(J4.mp h6).2;omega)] at hm)
     rw[m,prod_insert y,<-p];exact lq j d b c (z l (J4.mpr ⟨by omega,Y3⟩))
 obtain⟨_,f,e⟩:=w (2*n) Y3;refine⟨fun q o=>?_,e⟩;obtain⟨_,v,u⟩:=f q o;exact⟨by rw[ia,v];exact (ev (c5 n) q).symm,u⟩
lemma lr {n:ℕ} (x:F0 (N0 n)) (q:P0 n)
 (d:∀ k:Fin (2*n+1),(q9 n x).val.testBit k.val=decide (k=⟨e3 q,by have:=x6 q;omega⟩))
 (m:ia n x=u9 (R:=Z2 (Bw n)) (c5 n) q)
 (a b:Fin (n+1)):
 ac n x a b=hist (c5 n) q a b:=by
 have:NeZero (2^Bw n):=⟨W7 (by positivity)⟩;have g:=x6 q;have hoh':∀ k:Fin (2*n+1),(q9 n x).val.testBit (2*n-k.val)=decide (k=⟨2*n-e3 q,by omega⟩):=fun k=>by have f:=d ⟨2*n-k.val,by omega⟩;rw[f];apply L5;simp only[L0,K4];have:=k.isLt;omega
 have o:((z4 n x).coeff a b).val=2^(2*n-e3 q)*hist (c5 n) q a b:=by
  have p:(z4 n x).coeff a b=((2^(2*n-e3 q)*hist (c5 n) q a b:ℕ):Z2 (Bw n)):=by simp only[z4,z6,mul_sum];rw[X9];have c:=Q6 (Int.cast (R:=Z2 (Bw n))) (lh (c5 n) q a b);simp only[Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast] at c;have h:(∑ i:Fin (n+1),∑ j:Fin (n+1),(c6 n j.val b.val:Z2 (Bw n)) *((c6 n i.val a.val:Z2 (Bw n))*(ia n x).coeff i j))=∑ i:Fin (n+1),∑ j:Fin (n+1),(c6 n i.val a.val:Z2 (Bw n))*(c6 n j.val b.val:Z2 (Bw n)) *((u9 (R:=ℤ) (c5 n) q).coeff i j:Z2 (Bw n)):=(by refine L3 rfl fun i _=>L3 rfl fun j _=>?_;have f:=Q6 (fun P=>P.coeff i j) m;have l:(u9 (R:=Z2 (Bw n)) (c5 n) q).coeff i j=((u9 (R:=ℤ) (c5 n) q).coeff i j:Z2 (Bw n)):=(Q6 (fun P=>P.coeff i j) (mv (B:=Bw n) (c5 n) q)).symm;rw[f,l];ring);rw[h,c];push_cast;ring
  have e:2^(2*n-e3 q)*hist (c5 n) q a b<2^Bw n:=by have f:=W5 (2^(2*n-e3 q)) (ct (c5 n) q a b);rw[<-X6,Nat.sub_add_cancel g] at f;have l:2^(2*n)<2^Bw n:=Nat.pow_lt_pow_right (by omega) (by unfold Bw;omega);omega
  rw[p,val_natCast,L8 e]
 unfold ac;rw[gu hoh',o,Nat.mul_div_right _ (by positivity:0<2^(2*n-e3 q)),mod_mod];have e:hist (c5 n) q a b<2^(2*n+1):=lt_of_le_of_lt (ct (c5 n) q a b) (Nat.pow_lt_pow_right (by omega) (by omega));exact L8 e
def t0 (n:ℕ)(v:Fin (4*n+1)):ℤ:=(v.val:ℤ)-(2*n:ℤ)
noncomputable def v3 (n:ℕ)(l r:ℕ)(v:Fin (4*n+1)):d4 (N0 n):=fun x=>decide (cy n x l r=(t0 n v:Z2 (Bw n)))
noncomputable def s7 (n:ℕ)(x:F0 (N0 n))(l r:ℕ):ℤ:=if h:∃ v:Fin (4*n+1),v3 n l r v x=true then t0 n (Classical.choose h) else 2*n+1
lemma mh {n B:ℕ} (e:4*n+1<=2^B) {b a:Fin (4*n+1)}
 (h:(t0 n b:Z2 B)=(t0 n a:Z2 B)):b=a:=by
 have:NeZero (2^B):=⟨W7 (by positivity)⟩;have d:((b.val:ℕ):Z2 B)=((a.val:ℕ):Z2 B):=(by unfold t0 at h;push_cast at h;have:=Q6 (· + (2*n:Z2 B)) h;simpa using this);have c:=Q6 ZMod.val d;rw[val_natCast,val_natCast,L8 (by omega),L8 (by omega)] at c;exact L6 c
lemma az (n:ℕ)(x:F0 (N0 n))(l r:ℕ)(v:Fin (4*n+1)):decide (s7 n x l r=t0 n v)=v3 n l r v x:=by
 unfold s7;apply L5;simp only[L0]
 split_ifs with c
 . set f:=Classical.choose c;have a:=choose_spec c;change v3 n l r f x=true at a;constructor
   . intro e;have b:f=v:=by unfold t0 at e;exact L6 (by omega)
     exact b▸a
   . intro d;unfold v3 at a d;simp only[L0] at a d;have g:4*n+1<=2^Bw n:=(by have:2*n+9<2^(2*n+9):=lt_two_pow_self;have h:2^(2*n+10)=2^(2*n+9)*2:=U4 2 (2*n+9);unfold Bw;omega);have b:f=v:=mh (B:=Bw n) g (a.symm.trans d);exact Q6 (t0 n) b
 . constructor
   . intro e;unfold t0 at e;omega
   . intro d;exact absurd ⟨v,d⟩ c
def u5 (n:ℕ)(k:Fin (o8 n)):d4 (N0 n):=fun x=>(q9 n x).val.testBit k.val
def cg (n:ℕ):d4 (N0 n):=fun x=>decide (∃ f:Fin (2*n+1),∀ k:Fin (o8 n),u5 n k x=decide (k.val=f.val))
noncomputable def cz (n:ℕ):d4 (N0 n):=fun x=>decide (∀ l:Fin (2*n),∀ r∈(c4 (l.val+1)).toFinset,∃ v:Fin (4*n+1),v3 n (l.val+1) r v x=true)
noncomputable def ag (n:ℕ):d4 (N0 n):=fun x=>decide (∀ r0 b0:Fin (n+1),ac n x r0 b0=u4 n x r0 b0)
noncomputable def l8 (n:ℕ):d4 (N0 n):=fun x=>cg n x && cz n x && ag n x
noncomputable def x3 (n:ℕ)(x:F0 (N0 n)):ℕ:=if h:∃ f:Fin (2*n+1),∀ k:Fin (o8 n),u5 n k x=decide (k.val=f.val)
 then (Classical.choose h).val else 0
lemma ki (n:ℕ)(x:F0 (N0 n)):x3 n x<=2*n:=by
 unfold x3;split_ifs with h
 . exact U1 (Classical.choose h).isLt
 . omega
lemma kj {n:ℕ} (hn:1<=n) (x:F0 (N0 n))
 (q:P0 n):
 hist (c5 n) q=u4 n x↔l8 n x=true/\e3 q=x3 n x/\∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,e9 (c5 n) q l r=s7 n x l r:=by
 have:NeZero (2^o8 n):=⟨W7 (by positivity)⟩;have:NeZero (2^Bw n):=⟨W7 (by positivity)⟩;obtain⟨v1,h8⟩:=kx hn x;constructor
 . intro i;have u:(q9 n x).val=2^e3 q:=by unfold q9 av;rw[<-i,<-Nat.cast_sum];simp only[val_zero];rw[gn,val_natCast];exact L8 (Nat.pow_lt_pow_right (by omega) (by have:=x6 q;unfold o8;omega))
   have a:∀ k:Fin (o8 n),u5 n k x=decide (k.val=e3 q):=fun k=>(by unfold u5;simp only[u,Nat.testBit_two_pow,eq_comm]);have b:cg n x=true:=by unfold cg;simp only[L0];exact⟨⟨e3 q,by have:=x6 q;omega⟩,a⟩
   have z:x3 n x=e3 q:=by unfold x3;have h5:∃ f:Fin (2*n+1),∀ k:Fin (o8 n),u5 n k x=decide (k.val=f.val):=⟨⟨e3 q,by have:=x6 q;omega⟩,a⟩;rw[L7 h5];have g:=choose_spec h5 ⟨e3 q,by have:=x6 q;unfold o8;omega⟩;rw[a] at g;simp only[decide_true,true_eq_decide_iff] at g;exact g.symm
   have h7:di n x=z9 (R:=Z2 (Bw n)) (c5 n) q:=by
    apply a8.ext;intro h d;unfold di;dsimp only;have y:∀ k:Fin (2*n+1),(q9 n x).val.testBit k.val=decide (k=⟨e3 q,by have:=x6 q;omega⟩):=fun k=>(by rw[u,Nat.testBit_two_pow];apply L5;simp[K4,eq_comm]);rw[gu y,ZMod.natCast_mod];unfold ko;dsimp only;have h3:ao (R:=a8 3 (2*n+1) ℤ) (c5 n) q (a8.X2*(1+a8.X1)) a8.X2=(2:a8 3 (2*n+1) ℤ)^e3 q*z9 (R:=ℤ) (c5 n) q:=cs (c5 n) q _ _;rw[<-i,<-fq,h3];have x0:((2:a8 3 (2*n+1) ℤ)^e3 q)=(((2^e3 q:ℕ):a8 3 (2*n+1) ℤ)):=by simp
    have h0:((2:a8 3 (2*n+1) ℤ)^e3 q*z9 (R:=ℤ) (c5 n) q).coeff h d=(2:ℤ)^e3 q*(z9 (R:=ℤ) (c5 n) q).coeff h d:=(by rw[x0,a8.l0];simp);rw[h0,ro (show o8 n=Bw n+2*n by unfold o8 Bw;omega) (x6 q)];exact Q6 (fun P=>P.coeff h d) (mu (B:=Bw n) (c5 n) q)
   obtain⟨hP,hW⟩:=v1 q h7;have e:cz n x=true:=by unfold cz;simp only[L0];intro l r p;obtain⟨a0,v2⟩:=dg (c5 n) q (l.val+1) r;let v:Fin (4*n+1):=⟨(e9 (c5 n) q (l.val+1) r+2*n).toNat,by omega⟩;refine⟨v,?_⟩;unfold v3 t0;simp only[L0,v];rw[hW (l.val+1) (J4.mpr ⟨by omega,l.isLt⟩) r p];congr 1;omega
   have h9:∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,e9 (c5 n) q l r=s7 n x l r:=by
    intro l hl r p;obtain⟨a0,v2⟩:=dg (c5 n) q l r;let v:Fin (4*n+1):=⟨(e9 (c5 n) q l r+2*n).toNat,by omega⟩;have t:t0 n v=e9 (c5 n) q l r:=by unfold t0;dsimp[v];omega
    have o:v3 n l r v x=true:=(by unfold v3;rw[hW l hl r p,t];simp);have m:=az n x l r v;rw[o,decide_eq_true_iff] at m;rw[m,t]
   have c:ag n x=true:=by unfold ag;simp only[L0];intro r0 b0;have y:∀ k:Fin (2*n+1),(q9 n x).val.testBit k.val=decide (k=⟨e3 q,by have:=x6 q;omega⟩):=fun k=>(by rw[u,Nat.testBit_two_pow];apply L5;simp[K4,eq_comm]);rw[lr x q y hP r0 b0,i]
   refine⟨by simp[l8,b,e,c],z.symm,h9⟩
 . rintro⟨h6,h4,hc⟩;simp only[l8,K8] at h6;obtain⟨⟨b,e⟩,c⟩:=h6;unfold cg at b;simp only[L0] at b;unfold cz at e;simp only[L0] at e;unfold ag at c;simp only[L0] at c;have a:∀ k:Fin (2*n+1),(q9 n x).val.testBit k.val=decide (k=⟨e3 q,by have:=x6 q;omega⟩):=fun k=>by have s:∀ j:Fin (o8 n),u5 n j x=decide (j.val=x3 n x):=(by unfold x3;rw[L7 b];exact choose_spec b);have m:=s ⟨k.val,by unfold o8;omega⟩;unfold u5 at m;rw[m,<-h4];apply L5;simp[K4]
   have hP:ia n x=u9 (R:=Z2 (Bw n)) (c5 n) q:=by
    have m:=h8 (e9 (c5 n) q) (fun l hl r p=>by
     obtain⟨a3,a4⟩:=J4.mp hl;obtain⟨v,w⟩:=e ⟨l-1,by omega⟩ r (by simpa[show l-1+1=l by omega] using p);rw[show l-1+1=l by omega] at w;have o:=az n x l r v;rw[w,decide_eq_true_iff] at o;have a1:e9 (c5 n) q l r=t0 n v:=(hc l hl r p).trans o;unfold v3 at w;simp only[L0] at w;obtain⟨x2,y2⟩:=q8 (rfl:Bw n=2*n+10) (c5 n) q l r
     exact⟨by rw[w,<-a1],x2,y2,p3 hn (c5 n) q l r⟩)
    rw[m];exact (ev (c5 n) q).symm
   funext r0 b0
   rw[<-lr x q a hP r0 b0,c r0 b0]
noncomputable def da (n:ℕ):Set (d4 (N0 n)):=
 {l8 n}∪
 R0 (u5 n)∪
 {f|∃ l:Fin (2*n),∃ r∈(c4 (l.val+1)).toFinset,∃ v:Fin (4*n+1),f=v3 n (l.val+1) r v}
def io (D1 D2 B:ℕ):ℕ:=(D1*D2)*((D1*D2)*(B*(9*B)+9*B))
def bm (D1 D2 B K:ℕ):ℕ:=K*(io D1 D2 B+(D1*D2)*(B*4))
def bn (n B:ℕ):ℕ:=10*B+B*4+(2*B+1)+2*bm 3 (2*n+1) B (n+2) +2*bm (n+1) (n+1) B (n+2)
def mn (n:ℕ):ℕ:=bn n (Bw n)
def v4 (n B:ℕ):ℕ:=3*(10*B)+4*(B*(9*B))+7*(19*B)+9*B+3*bn n B
def bc (n:ℕ):ℕ:=v4 n (Bw n)
def ey (n:ℕ):ℕ:=let B:=Bw n
 let B0:=o8 n
 (3*(2*n+1))*(((n+1)*(n+1))*(B0*(9*B0)+9*B0)) +
 (2*n+1)*(9*B0) +
 (3*(2*n+1))*((3*(2*n+1))*(B0*(9*B0)+9*B0)) +
 (3*(2*n+1))*((2*n+1)*(10*B)) +
 (2*n)*bc n +
 2*(((n+1)*(n+1))*((n+1)*(B*(9*B)+9*B))) +
 ((n+1)*(n+1))*((2*n+1)*(10*(2*n+1))) +
 ((2*n+1)*(2*B0)+(2*n+1)) +
 (2*n*(3*((4*n+1)*(2*B)))) +
 (2*n*(3*(4*n+1))+2*n*3) +
 (((n+1)*(n+1))*(6*(2*n+1))+(n+1)*(n+1))+2
lemma cj {D2Z D1U D2U B K:ℕ} (hB:2<=B) {A:Set (d4 N)}
 (d:a8 3 D2Z (Z2 B)) (e:a8 D1U D2U (Z2 B))
 (b:(Fin N->Y0)->Z2 B)
 (R:(Fin N->Y0)->a8 3 D2Z (Z2 B))
 (Puv:(Fin N->Y0)->a8 D1U D2U (Z2 B))
 (g:(fun _=>false)∈A) (n:(fun _=>true)∈A)
 (f:i9 A (a9 B (fun x=>(b x).val)))
 (hR:g9 R⊆A) (hP:g9 Puv⊆A):
 let nxt (x:Fin N->Y0):=o3 B K d e (b x) (R x,Puv x)
 Build A (g9 (fun x=>(nxt x).1)∪g9 (fun x=>(nxt x).2))
  (10*B+B*4+(2*B+1)+2*bm 3 D2Z B K+2*bm D1U D2U B K):=by
 intro nxt;let a:d4 N:=a9 B (fun x=>(b x).val) ⟨B-1,by omega⟩;have h1:=im b g n f;let A1:=A∪R0 (a9 B (fun x=>(-b x).val));let absV (x:Fin N->Y0):ℕ:=if a x then (-b x).val else (b x).val
 have h2:Build A1 (R0 (a9 B absV)) (B*4):=by
  have z:=kf (A:=A1) (s:=a) (v:=a9 B (fun x=>(b x).val))
   (u:=a9 B (fun x=>(-b x).val))
   (inl (f _)) (fun j=>inl (f j)) (fun j=>inr ⟨j,rfl⟩)
  have i:(fun j=>mx a (a9 B (fun x=>(b x).val) j) (a9 B (fun x=>(-b x).val) j))=a9 B absV:=by funext j x;dsimp only[mx,a9,absV];by_cases h:a x<;>simp[h]
  rw[i] at z;exact z
 let A2:=A1∪R0 (a9 B absV);let posV (x:Fin N->Y0):ℕ:=if a x then 0 else absV x;let negV (x:Fin N->Y0):ℕ:=if a x then absV x else 0
 have t:Build A2 (R0 (a9 B posV)) (B+1):=by
  have hn:=ae (A:=A2) (inl (inl (f ⟨B-1,by omega⟩)))
  have w:=ig (A:=A2∪{nt a}) (m:=B) (p:=nt a) (F:=absV)
   (inr rfl) (fun j=>inl (inr ⟨j,rfl⟩))
  have i:(fun x=>if nt a x then absV x else 0)=posV:=by funext x;dsimp only[nt,posV];by_cases h:a x<;>simp[h]
  rw[i] at w;exact d9 (i7 hn w) Y3 Y3 (by omega)
 have y:Build A2 (R0 (a9 B negV)) B:=ig (A:=A2) (m:=B) (p:=a) (F:=absV) (inl (inl (f _))) (fun j=>inr ⟨j,rfl⟩);let A3:=A2∪(R0 (a9 B posV)∪R0 (a9 B negV));have c:∀ x,absV x<2^B:=fun x=>by dsimp[absV];split_ifs<;>exact val_lt _
 have l:i9 A3 (a9 K posV):=fun j=>by
  by_cases q:j.val<B
  . exact inr (inl ⟨⟨j.val,q⟩,rfl⟩)
  . have i:a9 K posV j=fun _=>false:=by
     funext x;dsimp only[a9,posV];split_ifs
     . simp
     . exact V2 ((c x).trans_le (pow_le_pow_right (by omega) (by omega)))
    rw[i];exact inl (inl (inl g))
 have k:i9 A3 (a9 K negV):=fun j=>by
  by_cases q:j.val<B
  . exact inr (inr ⟨⟨j.val,q⟩,rfl⟩)
  . have i:a9 K negV j=fun _=>false:=by
     funext x;dsimp only[a9,negV];split_ifs
     . exact V2 ((c x).trans_le (pow_le_pow_right (by omega) (by omega)))
     . simp
    rw[i];exact inl (inl (inl g))
 have h4:=bb (A:=A3) (a8.r5 d) posV R
  (inl (inl (inl g))) (inl (inl (inl n))) l (fun _ h=>inl (inl (inl (hR h))))
 have h5:=bb (A:=A3∪_) (1-d) negV (fun x=>a8.r5 d^(posV x %2^K)*R x)
  (inl (inl (inl (inl g)))) (inl (inl (inl (inl n))))
  (fun j=>inl (k j)) M9
 have h6:=bb (A:=A3) (1-e) posV Puv
  (inl (inl (inl g))) (inl (inl (inl n))) l (fun _ h=>inl (inl (inl (hP h))))
 have h7:=bb (A:=A3∪_) (a8.r5 e) negV (fun x=>(1-e)^(posV x %2^K)*Puv x)
  (inl (inl (inl (inl g)))) (inl (inl (inl (inl n))))
  (fun j=>inl (k j)) M9
 have r:=q6 (i7 h4 h5) (i7 h6 h7);have o:=q4 (q4 h1 h2) (d9 (q6 t y) (by simp only[A2,A1,W6];exact Y3) Y3 Y3);exact d9 (i7 o (d9 r (by simp only[A3,A2,A1,W6];exact Y3) Y3 Y3)) Y3 Y3 (by unfold bm io;omega)
lemma pd {n B:ℕ} (k:2<=B) (v0:Fin (2*n))
 {Bset:Set (d4 (N0 n))}
 (R:F0 (N0 n)->a8 3 (2*n+1) (Z2 B))
 (P:F0 (N0 n)->a8 (n+1) (n+1) (Z2 B))
 (W:F0 (N0 n)->ℕ->ℕ->Z2 B)
 (w:(fun _=>false)∈Bset) (v:(fun _=>true)∈Bset)
 (z:g9 R⊆Bset) (hP:g9 P⊆Bset):
 let l:=v0.val+1;let nxt (x:F0 (N0 n)):=l7 n B v0 ((R x,P x),W x)
 Build Bset
  (g9 (fun x=>(nxt x).1.1)∪g9 (fun x=>(nxt x).1.2)∪m0 (univ:V7 (Fin 3)) (fun a=>if a.val<(c4 l).length then R0 (a9 B (fun x=>((nxt x).2 l ((c4 l).getD a.val 0)).val)) else ∅))
  (v4 n B):=by
 intro l nxt;let d0 (x:F0 (N0 n)):=-((R x).coeff 0 ⟨l,by omega⟩);let d1 (x:F0 (N0 n)):=-((R x).coeff 1 ⟨l,by omega⟩);let d2 (x:F0 (N0 n)):=-((R x).coeff 2 ⟨l,by omega⟩);have Hd0:=im (A:=Bset) (fun x=>(R x).coeff 0 ⟨l,by omega⟩) w v (fun j=>z (v8 0 ⟨l,by omega⟩ j));have Hd1:=im (A:=Bset) (fun x=>(R x).coeff 1 ⟨l,by omega⟩) w v (fun j=>z (v8 1 ⟨l,by omega⟩ j));have Hd2:=im (A:=Bset) (fun x=>(R x).coeff 2 ⟨l,by omega⟩) w v (fun j=>z (v8 2 ⟨l,by omega⟩ j));have Hd:=q6 (q6 Hd0 Hd1) Hd2;let Cset:=Bset∪((R0 (a9 B (fun x=>(d0 x).val))∪R0 (a9 B (fun x=>(d1 x).val)))∪R0 (a9 B (fun x=>(d2 x).val)));have c:(fun _=>false)∈Cset:=inl w;have d:(fun _=>true)∈Cset:=inl v;have i:i9 Cset (a9 B (fun x=>(d0 x).val)):=fun j=>inr (inl (inl ⟨j,rfl⟩));have h3:i9 Cset (a9 B (fun x=>(d1 x).val)):=fun j=>inr (inl (inr ⟨j,rfl⟩));have v1:i9 Cset (a9 B (fun x=>(d2 x).val)):=fun j=>inr (inr ⟨j,rfl⟩);have h7:g9 R⊆Cset:=fun _ h=>inl (z h);have h6:g9 P⊆Cset:=fun _ h=>inl (hP h)
 have o:∀(cW:Fin 3->F0 (N0 n)->Z2 B) (Dset:Set (d4 (N0 n))) (s:ℕ),Build Cset Dset s->g9 (fun x=>(nxt x).1.1)⊆Cset∪Dset->g9 (fun x=>(nxt x).1.2)⊆Cset∪Dset->(∀ a:Fin 3,a.val<(c4 l).length->∀ x,(nxt x).2 l ((c4 l).getD a.val 0)=cW a x)->(∀ a:Fin 3,a.val<(c4 l).length->R0 (a9 B (fun x=>(cW a x).val))⊆Cset∪Dset)->3*(10*B)+s<=v4 n B->Build Bset
   (g9 (fun x=>(nxt x).1.1)∪g9 (fun x=>(nxt x).1.2)∪m0 (univ:V7 (Fin 3)) (fun a=>if a.val<(c4 l).length then R0 (a9 B (fun x=>((nxt x).2 l ((c4 l).getD a.val 0)).val)) else ∅))
   (v4 n B):=by
  intro cW Dset s Hbody hR' hP' h9 h5 x2;refine aa (q4 Hd Hbody) Y3 ?_ (by omega);rintro f ((x1|hf2)|⟨a,_,hf3⟩)
  . exact W6 _ _ _▸hR' x1
  . exact W6 _ _ _▸hP' hf2
  . dsimp only at hf3
    split_ifs at hf3 with g
    . have x0:(fun x=>((nxt x).2 l ((c4 l).getD a.val 0)).val)=fun x=>(cW a x).val:=funext fun x=>Q6 ZMod.val (h9 a g x);rw[x0] at hf3;exact W6 _ _ _▸h5 a g hf3
    . exact False.elim hf3
 by_cases e:l %2=1
 . set m:=l/2;let md0 (x:F0 (N0 n)):=(m:Z2 B)*d0 x;let c1 (x:F0 (N0 n)):=d1 x-md0 x;let c0 (x:F0 (N0 n)):=d0 x-c1 x;have Hm:=cf (A:=Cset) (m:Z2 B) d0 c d i;have Hmc1:=q4 Hm (ek d1 md0 (inl c) (inl d) (fun j=>inl (h3 j)) (fun j=>inr ⟨j,rfl⟩));have Hcc:=q4 Hmc1 (ek d0 c1 (inl c) (inl d) (fun j=>inl (i j)) (fun j=>inr (inr ⟨j,rfl⟩)));let st1 (x:F0 (N0 n)):=o3 B (n+2) (v9 n B l m) (y4 n B l m) (c0 x) (R x,P x)
   have Hb1:=q4 Hcc (cj (K:=n+2) k (v9 n B l m) (y4 n B l m) c0 R P
    (inl c) (inl d) (fun j=>inr (inr ⟨j,rfl⟩)) (fun _ h=>inl (h7 h)) (fun _ h=>inl (h6 h)))
   have Hbody:=q4 Hb1 (cj (K:=n+2) k (v9 n B l (m+1)) (y4 n B l (m+1)) c1 (fun x=>(st1 x).1) (fun x=>(st1 x).2)
    (inl c) (inl d) (fun j=>inr (inl (inl (inr ⟨j,rfl⟩))))
    (fun _ h=>inr (inr (inl h))) (fun _ h=>inr (inr (inr h))))
   refine o (fun a=>if a.val=0 then c0 else c1) _ _ Hbody ?_ ?_ ?_ ?_ (by unfold v4 bn;omega)
   . intro f b;have q:(fun x=>(nxt x).1.1)=fun x=>(o3 B (n+2) (v9 n B l (m+1)) (y4 n B l (m+1)) (c1 x) ((st1 x).1,(st1 x).2)).1:=funext fun x=>(by dsimp only[nxt];unfold l7;dsimp only;rw[Q2 e]);rw[q] at b;exact inr (inr (inl b))
   . intro f b;have q:(fun x=>(nxt x).1.2)=fun x=>(o3 B (n+2) (v9 n B l (m+1)) (y4 n B l (m+1)) (c1 x) ((st1 x).1,(st1 x).2)).2:=funext fun x=>(by dsimp only[nxt];unfold l7;dsimp only;rw[Q2 e]);rw[q] at b;exact inr (inr (inr b))
   . intro a g x;have p:c4 l=[m,m+1]:=(by simp[c4,e,m]);rw[p] at g ⊢;dsimp only[nxt];unfold l7;dsimp only;rw[Q2 e];have u:a.val=0\/a.val=1:=by simp at g;omega
     rcases u with r|y
     . simp only[r,↓reduceIte,getD_cons_zero];rw[Q2 rfl,Q2 rfl]
     . simp only[y,Nat.one_ne_zero,↓reduceIte,List.getD_cons_succ,getD_cons_zero];rw[Q2 rfl,Q3 (by omega),Q2 rfl]
   . intro a _ f b;by_cases r:a.val=0
     . simp only[r,↓reduceIte] at b;exact inr (inl (inl (inr b)))
     . simp only[r,↓reduceIte] at b;exact inr (inl (inl (inl (inr b))))
 . by_cases t:l %4=0
   . have Hds1:=cj (A:=Cset) (K:=n+2) k (v9 n B l (l/2)) (y4 n B l (l/2)) d0 R P
      c d i h7 h6
     refine o (fun _=>d0) _ _ Hds1 ?_ ?_ ?_ ?_ (by unfold v4 bn;omega)
     . intro f b;have q:(fun x=>(nxt x).1.1)=fun x=>(o3 B (n+2) (v9 n B l (l/2)) (y4 n B l (l/2)) (d0 x) (R x,P x)).1:=funext fun x=>(by dsimp only[nxt];unfold l7;dsimp only;rw[Q3 e,Q2 t]);rw[q] at b;exact inr (inl b)
     . intro f b;have q:(fun x=>(nxt x).1.2)=fun x=>(o3 B (n+2) (v9 n B l (l/2)) (y4 n B l (l/2)) (d0 x) (R x,P x)).2:=funext fun x=>(by dsimp only[nxt];unfold l7;dsimp only;rw[Q3 e,Q2 t]);rw[q] at b;exact inr (inr b)
     . intro a g x;have p:c4 l=[l/2]:=(by simp[c4,e,t]);rw[p] at g ⊢;dsimp only[nxt];unfold l7;dsimp only;rw[Q3 e,Q2 t];have:a.val=0:=(by simp at g;omega);simp only[this,getD_cons_zero];rw[Q2 rfl,Q2 rfl]
     . intro a _ f b;rcases b with ⟨j,rfl⟩;exact inl (i j)
   . set m:=l/2;let r4 (x:F0 (N0 n)):=(m:Z2 B)*d0 x;let diff (x:F0 (N0 n)):=d1 x-r4 x;let r6 (x:F0 (N0 n)):=(choose m 2:Z2 B)*d0 x;let r7 (x:F0 (N0 n)):=d2 x-r6 x;let r8 (x:F0 (N0 n)):=(m:Z2 B)*diff x;let cm1 (x:F0 (N0 n)):=r7 x-r8 x;let cp1 (x:F0 (N0 n)):=cm1 x+diff x;let r11 (x:F0 (N0 n)):=d0 x-cm1 x;let c0 (x:F0 (N0 n)):=r11 x-cp1 x;have H4:=cf (A:=Cset) (m:Z2 B) d0 c d i;have H5:=q4 H4 (ek d1 r4 (inl c) (inl d) (fun j=>inl (h3 j)) (fun j=>inr ⟨j,rfl⟩));have H6:=q4 H5 (cf (choose m 2:Z2 B) d0 (inl c) (inl d) (fun j=>inl (i j)));have H7:=q4 H6 (ek d2 r6 (inl c) (inl d) (fun j=>inl (v1 j)) (fun j=>inr (inr ⟨j,rfl⟩)));have H8:=q4 H7 (cf (m:Z2 B) diff (inl c) (inl d) (fun j=>inr (inl (inl (inr ⟨j,rfl⟩)))));have H9:=q4 H8 (ek r7 r8 (inl c) (inl d) (fun j=>inr (inl (inr ⟨j,rfl⟩))) (fun j=>inr (inr ⟨j,rfl⟩)));have H10:=q4 H9 (pb cm1 diff (inl c) (fun j=>inr (inr ⟨j,rfl⟩)) (fun j=>inr (inl (inl (inl (inl (inr ⟨j,rfl⟩)))))));have H11:=q4 H10 (ek d0 cm1 (inl c) (inl d) (fun j=>inl (i j)) (fun j=>inr (inl (inr ⟨j,rfl⟩))));have Hcc:=q4 H11 (ek r11 cp1 (inl c) (inl d) (fun j=>inr (inr ⟨j,rfl⟩)) (fun j=>inr (inl (inr ⟨j,rfl⟩))));let st1 (x:F0 (N0 n)):=o3 B (n+2) (v9 n B l (m-1)) (y4 n B l (m-1)) (cm1 x) (R x,P x);let st2 (x:F0 (N0 n)):=o3 B (n+2) (v9 n B l m) (y4 n B l m) (c0 x) (st1 x)
     have Hb1:=q4 Hcc (cj (K:=n+2) k (v9 n B l (m-1)) (y4 n B l (m-1)) cm1 R P
      (inl c) (inl d) (fun j=>inr (inl (inl (inl (inr ⟨j,rfl⟩)))))
      (fun _ h=>inl (h7 h)) (fun _ h=>inl (h6 h)))
     have Hb2:=q4 Hb1 (cj (K:=n+2) k (v9 n B l m) (y4 n B l m) c0 (fun x=>(st1 x).1) (fun x=>(st1 x).2)
      (inl c) (inl d) (fun j=>inr (inl (inr ⟨j,rfl⟩)))
      (fun _ h=>inr (inr (inl h))) (fun _ h=>inr (inr (inr h))))
     have Hbody:=q4 Hb2 (cj (K:=n+2) k (v9 n B l (m+1)) (y4 n B l (m+1)) cp1 (fun x=>(st2 x).1) (fun x=>(st2 x).2)
      (inl c) (inl d) (fun j=>inr (inl (inl (inl (inl (inr ⟨j,rfl⟩))))))
      (fun _ h=>inr (inr (inl h))) (fun _ h=>inr (inr (inr h))))
     refine o (fun a=>if a.val=0 then cm1 else if a.val=1 then c0 else cp1) _ _ Hbody ?_ ?_ ?_ ?_ (by unfold v4 bn;omega)
     . intro f b;have q:(fun x=>(nxt x).1.1)=fun x=>(o3 B (n+2) (v9 n B l (m+1)) (y4 n B l (m+1)) (cp1 x) ((st2 x).1,(st2 x).2)).1:=funext fun x=>(by dsimp only[nxt];unfold l7;dsimp only;rw[Q3 e,Q3 t]);rw[q] at b;exact inr (inr (inl b))
     . intro f b;have q:(fun x=>(nxt x).1.2)=fun x=>(o3 B (n+2) (v9 n B l (m+1)) (y4 n B l (m+1)) (cp1 x) ((st2 x).1,(st2 x).2)).2:=funext fun x=>(by dsimp only[nxt];unfold l7;dsimp only;rw[Q3 e,Q3 t]);rw[q] at b;exact inr (inr (inr b))
     . intro a g x;have p:c4 l=[m-1,m,m+1]:=(by simp[c4,e,t,m]);rw[p] at g ⊢;dsimp only[nxt];unfold l7;dsimp only;rw[Q3 e,Q3 t];have u:a.val=0\/a.val=1\/a.val=2:=by have:=a.isLt;omega
       rcases u with r|y|h2
       . simp only[r,↓reduceIte,getD_cons_zero];rw[Q2 rfl,Q2 rfl]
       . simp only[y,Nat.one_ne_zero,↓reduceIte,List.getD_cons_succ,getD_cons_zero];rw[Q2 rfl,Q3 (by omega),Q2 rfl]
       . simp only[h2,show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,↓reduceIte,List.getD_cons_succ,getD_cons_zero];rw[Q2 rfl,Q3 (by omega),Q3 (by omega),Q2 rfl]
     . intro a _ f b;by_cases r:a.val=0
       . simp only[r,↓reduceIte] at b;exact inr (inl (inl (inl (inl (inl (inl (inr b)))))))
       . by_cases y:a.val=1
         . simp only[r,y,↓reduceIte] at b;exact inr (inl (inl (inl (inr b))))
         . simp only[r,y,↓reduceIte] at b;exact inr (inl (inl (inl (inl (inl (inr b))))))
noncomputable def ft (n:ℕ)(k:ℕ):Set (d4 (N0 n)):=g9 (fun x=>(f7 n x k).1.1)∪g9 (fun x=>(f7 n x k).1.2)∪m0 (univ:V7 (Fin (2*n)×Fin 3))
  (fun p=>let l:=p.1.val+1
   let r:=(c4 l).getD p.2.val 0
   if p.2.val<(c4 l).length/\p.1.val<k then R0 (a9 (Bw n) (fun x=>((f7 n x k).2 l r).val))
   else ∅)
set_option maxHeartbeats 800000 in
lemma ps (n:ℕ):Build (jh (N0 n)) (da n) (ey n):=by
 let A0:=jh (N0 n);have h2:(fun _=>false)∈A0:=inr (inl rfl);have h6:(fun _=>true)∈A0:=inr (inr rfl)
 have a5:∀ r b:Fin (n+1),i9 A0 (a9 (o8 n) (fun x=>((u4 n x r b:ℕ):ZMod (2^o8 n)).val)):=by
  have:NeZero (2^o8 n):=⟨W7 (by positivity)⟩;intro r b j;have a2:∀ x,u4 n x r b<2^o8 n:=fun x=>(kh n x r b).trans_le (pow_le_pow_right (by omega) (by unfold o8;omega));by_cases hj:j.val<2*n+1
  . have a:a9 (o8 n) (fun x=>((u4 n x r b:ℕ):ZMod (2^o8 n)).val) j=fun x=>x (aj n r b ⟨j.val,hj⟩):=by
     funext x;dsimp only[a9]
     rw[val_natCast,L8 (a2 x),jl n x r b ⟨j.val,hj⟩]
    rw[a];exact inl ⟨_,rfl⟩
  . have a:a9 (o8 n) (fun x=>((u4 n x r b:ℕ):ZMod (2^o8 n)).val) j=fun _=>false:=by
     funext x;dsimp only[a9]
     rw[val_natCast,L8 (a2 x)];exact V2 ((kh n x r b).trans_le (pow_le_pow_right (by omega) (by omega)))
    rw[a];exact h2
 let h3:Set (d4 (N0 n)):=m0 (univ:V7 (Fin 3×Fin (2*n+1)))
   (fun p=>R0 (a9 (o8 n) (fun x=>(av n x p.1 p.2).val)))
 have Hprof:Build A0 h3 ((3*(2*n+1))*(((n+1)*(n+1))*(o8 n*(9*o8 n)+9*o8 n))):=by
  have H:=p7 (A:=A0) (fun p:Fin 3×Fin (2*n+1)=>R0 (a9 (o8 n) (fun x=>(av n x p.1 p.2).val)))
   (((n+1)*(n+1))*(o8 n*(9*o8 n)+9*o8 n)) (fun⟨h,s⟩=>by
    let coeffs (t:Fin (n+1)×Fin (n+1)):ZMod (2^o8 n):=if t.1.val+t.2.val=s.val then (choose t.1.val h.val:ZMod (2^o8 n)) else 0
    have H1:=cv coeffs (fun t x=>(u4 n x t.1 t.2:ZMod (2^o8 n)))
     h2 h6 (fun t=>a5 t.1 t.2)
    have a:(fun x=>(∑ t:Fin (n+1)×Fin (n+1),coeffs t*(u4 n x t.1 t.2:ZMod (2^o8 n))).val)=fun x=>(av n x h s).val:=by
     funext x;congr 1;unfold av profile;rw[sum_prod_type,Nat.cast_sum]
     refine L3 rfl fun r _=>?_;rw[Nat.cast_sum];refine L3 rfl fun b _=>?_;dsimp[coeffs];split_ifs<;>simp
    rw[a] at H1;simpa only[J3,Q9] using H1)
  simpa only[J3,Q9] using H
 let A1:=A0∪h3
 have Htp:Build A1 (R0 (a9 (o8 n) (fun x=>(q9 n x).val))) ((2*n+1)*(9*o8 n)):=by
  have:NeZero (2^o8 n):=⟨W7 (by positivity)⟩
  have H:=dh (A:=A1) (w:=o8 n) (univ:V7 (Fin (2*n+1)))
   (fun s x=>(av n x 0 s).val) (inl h2) (inl h6)
   (fun s _ j=>inr (q3 (i:=((0:Fin 3),s)) ⟨j,rfl⟩))
  have a:a9 (o8 n) (fun x=>∑ s:Fin (2*n+1),(av n x 0 s).val)=a9 (o8 n) (fun x=>(q9 n x).val):=z3 _ _ (fun x=>by
    have a0:((∑ s:Fin (2*n+1),(av n x 0 s).val:ℕ):ZMod (2^o8 n))=q9 n x:=by unfold q9;rw[Nat.cast_sum];refine L3 rfl fun s _=>ZMod.natCast_zmod_val _
    rw[<-a0,val_natCast,mod_mod])
  rw[a] at H;simpa only[W2,Q9] using H
 have HQ:Build A1 (g9 (ko n)) ((3*(2*n+1))*((3*(2*n+1))*(o8 n*(9*o8 n)+9*o8 n))):=by
  have H:=p7 (A:=A1) (fun p:Fin 3×Fin (2*n+1)=>R0 (a9 (o8 n) (fun x=>((ko n x).coeff p.1 p.2).val)))
   ((3*(2*n+1))*(o8 n*(9*o8 n)+9*o8 n)) (fun⟨h,d⟩=>by
    let coeffs (y:Fin 3×Fin (2*n+1)):ZMod (2^o8 n):=(fr n h d y.1 y.2:ZMod (2^o8 n))
    have H1:=cv (A:=A1) coeffs (fun y x=>av n x y.1 y.2)
     (inl h2) (inl h6) (fun y j=>inr ⟨y,Y2 _,j,rfl⟩)
    have a:(fun x=>(∑ y:Fin 3×Fin (2*n+1),coeffs y*av n x y.1 y.2).val)=fun x=>((ko n x).coeff h d).val:=by
     funext x;congr 1;unfold ko av;dsimp only
     rw[fh,sum_prod_type,Fin.sum_univ_three];simp only[Int.cast_add,Int.cast_sum,Int.cast_mul,Int.cast_natCast,coeffs]
    rw[a] at H1;simpa only[J3,Q9] using H1)
  unfold g9;simpa only[J3,Q9] using H
 let A2:=A1∪(R0 (a9 (o8 n) (fun x=>(q9 n x).val))∪g9 (ko n))
 have HFzt:Build A2 (g9 (di n)) ((3*(2*n+1))*((2*n+1)*(10*Bw n))):=by
  have:NeZero (2^Bw n):=⟨W7 (by positivity)⟩
  have H:=p7 (A:=A2) (fun p:Fin 3×Fin (2*n+1)=>R0 (a9 (Bw n) (fun x=>((di n x).coeff p.1 p.2).val)))
   ((2*n+1)*(10*Bw n)) (fun⟨h,d⟩=>by
    have H1:=ln (B1:=o8 n) (B2:=Bw n) (M:=2*n+1)
     (A:=A2) (fun k x=>(q9 n x).val.testBit k.val) (fun x=>((ko n x).coeff h d).val)
     (inl (inl h2)) (inl (inl h6))
     (fun k=>inr (inl ⟨⟨k.val,by unfold o8;omega⟩,rfl⟩))
     (fun j=>inr (inr (v8 h d j))) (fun x=>val_lt _)
    have a:a9 (Bw n) (fun x=>x9 (Bw n) (2*n+1)
     (fun k=>(q9 n x).val.testBit k.val) ((ko n x).coeff h d).val)=
     a9 (Bw n) (fun x=>((di n x).coeff h d).val):=
     z3 _ _ (fun x=>by unfold di;dsimp;rw[val_natCast,mod_mod])
    rw[a] at H1;exact H1)
  unfold g9;simpa only[J3,Q9] using H
 let A3:=A2∪g9 (di n);have h8:(fun _=>false)∈A3:=inl (inl (inl h2));have h9:(fun _=>true)∈A3:=inl (inl (inl h6))
 have Hext0:Build A3 (ft n 0) 0:=by
  apply s6;rintro f ((v1|hf2)|⟨⟨m,r3⟩,_,hf3⟩)
  . exact inr v1
  . rcases hf2 with ⟨⟨i,j⟩,_,b,rfl⟩
    dsimp only[f7];have a:a9 (Bw n) (fun _:F0 (N0 n)=>((1:a8 (n+1) (n+1) (Z2 (Bw n))).coeff i j).val) b=fun _=>((1:a8 (n+1) (n+1) (Z2 (Bw n))).coeff i j).val.testBit b.val:=rfl;rw[a];cases ((1:a8 (n+1) (n+1) (Z2 (Bw n))).coeff i j).val.testBit b.val
    . exact h8
    . exact h9
  . simp at hf3
 have Hext:Build A3 (ft n (2*n)) ((2*n)*bc n):=by
  suffices H:Build A3 (ft n (2*n)) (0+(2*n)*bc n) by simpa only[Nat.zero_add] using H
  refine ew (ft n) Hext0 fun k hk=>?_;let Bset:=A3∪ft n k
  have Hstep:=pd (B:=Bw n) (Bset:=Bset) (by unfold Bw;omega) ⟨k,hk⟩
   (fun x=>(f7 n x k).1.1) (fun x=>(f7 n x k).1.2) (fun x=>(f7 n x k).2)
   (inl h8) (inl h9) (fun _ h=>inr (inl (inl h))) (fun _ h=>inr (inl (inr h)))
  have o:∀ x,f7 n x (k+1)=l7 n (Bw n) ⟨k,hk⟩ (((f7 n x k).1.1,(f7 n x k).1.2),(f7 n x k).2):=fun x=>(by rw[f7,L7 hk];rfl);refine aa Hstep Y3 ?_ Y3;rintro f ((v1|hf2)|⟨⟨i',r3⟩,_,hf3⟩)
  . have a:(fun x=>(f7 n x (k+1)).1.1)=_:=funext fun x=>Q6 (fun s=>s.1.1) (o x);rw[a] at v1;exact inr (inl (inl v1))
  . have a:(fun x=>(f7 n x (k+1)).1.2)=_:=funext fun x=>Q6 (fun s=>s.1.2) (o x);rw[a] at hf2;exact inr (inl (inr hf2))
  . dsimp only at hf3
    split_ifs at hf3 with v2
    . by_cases a4:i'.val<k
      . have b3:i'.val+1≠k+1:=(by omega);have h0:(fun x=>((f7 n x (k+1)).2 (i'.val+1) ((c4 (i'.val+1)).getD r3.val 0)).val)=fun x=>((f7 n x k).2 (i'.val+1) ((c4 (i'.val+1)).getD r3.val 0)).val:=(by funext x;rw[o x];unfold l7;dsimp only;split_ifs<;>(dsimp only;rw[Q3 b3]));rw[h0] at hf3;exact inl (inr (inr ⟨(i',r3),Y2 _,by dsimp only;rw[Q2 ⟨v2.1,a4⟩];exact hf3⟩))
      . have a3:i'.val+1=k+1:=(by omega);rw[a3] at hf3;have h0:(fun x=>((f7 n x (k+1)).2 (k+1) ((c4 (k+1)).getD r3.val 0)).val)=_:=funext fun x=>Q6 (fun s=>(s.2 (k+1) ((c4 (k+1)).getD r3.val 0)).val) (o x);rw[h0] at hf3;exact inr (inr ⟨r3,Y2 _,by dsimp only;rw[Q2 (a3▸v2.1)];exact hf3⟩)
    . exact False.elim hf3
 let A4:=A3∪ft n (2*n);have h4:(fun _=>false)∈A4:=inl h8;have h5:(fun _=>true)∈A4:=inl h9
 have HTmp:Build A4 (g9 (z6 n)) (((n+1)*(n+1))*((n+1)*(Bw n*(9*Bw n)+9*Bw n))):=by
  have H:=p7 (A:=A4) (fun p:Fin (n+1)×Fin (n+1)=>R0 (a9 (Bw n) (fun x=>((z6 n x).coeff p.1 p.2).val)))
   ((n+1)*(Bw n*(9*Bw n)+9*Bw n)) (fun⟨c,j⟩=>by
    unfold z6;simpa only[Q9] using cv (A:=A4)
     (fun i:Fin (n+1)=>(c6 n i.val c.val:Z2 (Bw n)))
     (fun i x=>(ia n x).coeff i j) h4 h5 (fun i b=>inr (inl (inr (v8 i j b)))))
  unfold g9;simpa only[J3,Q9] using H
 have HM:Build (A4∪g9 (z6 n)) (g9 (z4 n))
  (((n+1)*(n+1))*((n+1)*(Bw n*(9*Bw n)+9*Bw n))):=by
  have H:=p7 (A:=A4∪g9 (z6 n)) (fun p:Fin (n+1)×Fin (n+1)=>R0 (a9 (Bw n) (fun x=>((z4 n x).coeff p.1 p.2).val)))
   ((n+1)*(Bw n*(9*Bw n)+9*Bw n)) (fun⟨c,e⟩=>by
    unfold z4;simpa only[Q9] using cv (A:=A4∪g9 (z6 n))
     (fun j:Fin (n+1)=>(c6 n j.val e.val:Z2 (Bw n)))
     (fun j x=>(z6 n x).coeff c j) (inl h4) (inl h5)
     (fun j b=>inr (v8 c j b)))
  unfold g9 at H ⊢;simpa only[J3,Q9] using H
 let u:Set (d4 (N0 n)):=m0 (univ:V7 (Fin (n+1)×Fin (n+1)))
   (fun p=>R0 (a9 (2*n+1) (fun x=>ac n x p.1 p.2)))
 have HRec:Build (A4∪g9 (z4 n)) u
  (((n+1)*(n+1))*((2*n+1)*(10*(2*n+1)))):=by
  have H:=p7 (A:=A4∪g9 (z4 n)) (fun p:Fin (n+1)×Fin (n+1)=>R0 (a9 (2*n+1) (fun x=>ac n x p.1 p.2)))
   ((2*n+1)*(10*(2*n+1))) (fun⟨c,e⟩=>by
    have H1:=ln (B1:=Bw n) (B2:=2*n+1) (M:=2*n+1)
     (A:=A4∪g9 (z4 n))
     (fun k x=>(q9 n x).val.testBit (2*n-k.val))
     (fun x=>((z4 n x).coeff c e).val)
     (inl h4) (inl h5)
     (fun k=>inl (inl (inl (inr (inl ⟨⟨2*n-k.val,by unfold o8;omega⟩,rfl⟩)))))
     (fun b=>inr (v8 c e b)) (fun x=>val_lt _)
    have a:a9 (2*n+1) (fun x=>x9 (2*n+1) (2*n+1)
     (fun k=>(q9 n x).val.testBit (2*n-k.val)) ((z4 n x).coeff c e).val)=
     a9 (2*n+1) (fun x=>ac n x c e):=
     z3 _ _ (fun x=>by unfold ac;rw[mod_mod])
    rw[a] at H1;exact H1)
  simpa only[J3,Q9] using H
 let A5:=A4∪u;have y1:(fun _=>false)∈A5:=inl h4;have q:(fun _=>true)∈A5:=inl h5
 have HokF:Build A5 {cg n} ((2*n+1)*(2*o8 n)+(2*n+1)):=by
  let eqF (f:Fin (2*n+1)):d4 (N0 n):=fun x=>decide (∀ k:Fin (o8 n),u5 n k x=(2^f.val).testBit k.val)
  have H1:Build A5 (R0 eqF) ((2*n+1)*(2*o8 n)):=au eqF (2*o8 n) (fun f=>ll (2^f.val) (u5 n) q
    (fun k=>inl (inl (inl (inr (inl ⟨k,rfl⟩))))))
  have H2:=w3 (A:=A5∪R0 eqF) eqF (inl y1) (fun f=>inr ⟨f,rfl⟩)
  have a:(fun x=>decide (∃ f:Fin (2*n+1),eqF f x=true))=cg n:=by
   funext x;apply L5;unfold cg eqF
   simp only[L0];exact exists_congr fun f=>forall_congr' fun k=>by simp only[Nat.testBit_two_pow,eq_comm]
  rw[a] at H2;exact i7 H1 H2
 let h7:Set (d4 (N0 n)):=
  {f|∃ l:Fin (2*n),∃ r∈(c4 (l.val+1)).toFinset,∃ v:Fin (4*n+1),f=v3 n (l.val+1) r v}
 have HcEq:Build A5 h7 (2*n*(3*((4*n+1)*(2*Bw n)))):=by
  have:NeZero (2^Bw n):=⟨W7 (by positivity)⟩
  let Bcell (p:Fin (2*n)×Fin 3×Fin (4*n+1)):Set (d4 (N0 n)):=let l:=p.1.val+1
   if p.2.1.val<(c4 l).length then {v3 n l ((c4 l).getD p.2.1.val 0) p.2.2} else ∅
  have H:=p7 (A:=A5) Bcell (2*Bw n) (fun⟨l,r3,v⟩=>by
   dsimp only[Bcell];split_ifs with z
   . let r:=(c4 (l.val+1)).getD r3.val 0
     have H1:=ll (A:=A5) (t0 n v:Z2 (Bw n)).val
      (a9 (Bw n) (fun x=>(cy n x (l.val+1) r).val)) q
      (fun b=>inl (inr (inr ⟨(l,r3),Y2 _,by dsimp only;rw[Q2 ⟨z,l.isLt⟩];exact⟨b,rfl⟩⟩)))
     have a:(fun x=>decide (∀ j:Fin (Bw n),a9 (Bw n) (fun x=>(cy n x (l.val+1) r).val) j x=(t0 n v:Z2 (Bw n)).val.testBit j.val))=v3 n (l.val+1) r v:=by
      funext x;apply L5;unfold v3 a9
      simp only[L0];constructor
      . intro h1;apply ZMod.val_injective;apply Nat.eq_of_testBit_eq;intro j;by_cases hj:j<Bw n
        . exact h1 ⟨j,hj⟩
        . rw[V2 ((val_lt _).trans_le (pow_le_pow_right (by omega) (by omega))),V2 ((val_lt _).trans_le (pow_le_pow_right (by omega) (by omega)))]
      . intro h0 j;rw[h0]
     rw[a] at H1;exact H1
   . exact d9 (s6 (by simp)) Y3 Y3 (by omega))
  refine d9 H Y3 ?_ (by simp[Z3]);rintro _ ⟨l,r,hr,v,rfl⟩;rw[K3] at hr;obtain⟨i,hi⟩:=List.mem_iff_get.mp hr;have x2:i.val<3:=by have:(c4 (l.val+1)).length<=3:=(by unfold c4;split_ifs<;>simp);omega
  have b2:(c4 (l.val+1)).getD i.val 0=r:=(by rw[getD_eq_getElem _ _ i.isLt];exact hi);refine⟨(l,⟨i.val,x2⟩,v),Y2 _,?_⟩;dsimp only[Bcell];rw[Q2 i.isLt,b2];rfl
 let A6:=A5∪h7
 have HokC:Build A6 {cz n} (2*n*(3*(4*n+1))+2*n*3):=by
  let hasV (p:Fin (2*n)×Fin 3):d4 (N0 n):=let l:=p.1.val+1
   if p.2.val<(c4 l).length then fun x=>decide (∃ v:Fin (4*n+1),v3 n l ((c4 l).getD p.2.val 0) v x=true)
   else fun _=>true
  have H1:Build A6 (R0 hasV) ((2*n*3)*(4*n+1)):=by
   simpa only[J3,Q9] using ke (A:=A6) hasV (4*n+1) (fun⟨l,r3⟩=>by
    dsimp only[hasV];split_ifs with z
    . exact w3 (A:=A6) (fun v=>v3 n (l.val+1) ((c4 (l.val+1)).getD r3.val 0) v)
       (inl y1) (fun v=>inr ⟨l,_,K3.mpr (by
        rw[getD_eq_getElem _ _ z];exact getElem_mem z),v,rfl⟩)
    . exact d9 (s6 (Q1 (inl q))) Y3 Y3 (by omega))
  have H2:=er (A:=A6∪R0 hasV) (fun m:Fin (2*n*3)=>hasV (finProdFinEquiv.symm m))
   (inl (inl q)) (fun m=>inr ⟨_,rfl⟩)
  have a:(fun x=>decide (∀ m:Fin (2*n*3),hasV (finProdFinEquiv.symm m) x=true))=cz n:=by
   funext x;apply L5;unfold cz;simp only[L0]
   constructor
   . intro h1 l r hr;rw[K3] at hr;obtain⟨i,hi⟩:=List.mem_iff_get.mp hr;have x2:i.val<3:=by have:(c4 (l.val+1)).length<=3:=(by unfold c4;split_ifs<;>simp);omega
     have h:=h1 (finProdFinEquiv (l,⟨i.val,x2⟩));rw[M5] at h;dsimp only[hasV] at h;rw[Q2 i.isLt] at h;rw[getD_eq_getElem _ _ i.isLt] at h;rw[get_eq_getElem] at hi;simpa only[hi,L0] using h
   . intro h1 m
     rcases hpair:finProdFinEquiv.symm m with ⟨l,r3⟩
     dsimp only[hasV];split_ifs with z
     . simp only[L0];exact h1 l _ (K3.mpr (by rw[getD_eq_getElem _ _ z];exact getElem_mem z))
     . rfl
  rw[a] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by ring_nf;omega)
 have HokR:Build A5 {ag n} (((n+1)*(n+1))*(6*(2*n+1))+(n+1)*(n+1)):=by
  let eqCell (p:Fin (n+1)×Fin (n+1)):d4 (N0 n):=fun x=>decide (∀ k:Fin (2*n+1),a9 (2*n+1) (fun x=>ac n x p.1 p.2) k x=x (aj n p.1 p.2 k));have H1:Build A5 (R0 eqCell) (((n+1)*(n+1))*(6*(2*n+1))):=by simpa only[J3,Q9] using ke (A:=A5) eqCell (6*(2*n+1)) (fun⟨c,e⟩=>rd (a9 (2*n+1) (fun x=>ac n x c e)) (fun k x=>x (aj n c e k)) q (fun k=>inr ⟨(c,e),Y2 _,k,rfl⟩) (fun k=>inl (inl (inl (inl (inl (inl ⟨_,rfl⟩)))))))
  have H2:=er (A:=A5∪R0 eqCell) (fun m:Fin ((n+1)*(n+1))=>eqCell (finProdFinEquiv.symm m))
   (inl q) (fun m=>inr ⟨_,rfl⟩)
  have a:(fun x=>decide (∀ m:Fin ((n+1)*(n+1)),eqCell (finProdFinEquiv.symm m) x=true))=ag n:=by
   funext x;apply L5;unfold ag;simp only[L0]
   have v0:∀ c e,eqCell (c,e) x=true↔ac n x c e=u4 n x c e:=fun c e=>by
    dsimp only[eqCell];simp only[L0];dsimp only[a9];constructor
    . intro h;apply Nat.eq_of_testBit_eq;intro k;by_cases hk:k<2*n+1
      . rw[jl n x c e ⟨k,hk⟩];exact h ⟨k,hk⟩
      . have a7:ac n x c e<2^(2*n+1):=M1 _ (by positivity);rw[V2 (a7.trans_le (pow_le_pow_right (by omega) (by omega))),V2 ((kh n x c e).trans_le (pow_le_pow_right (by omega) (by omega)))]
    . intro h0 k;rw[h0,jl]
   constructor
   . intro h c e;have:=h (finProdFinEquiv (c,e));rw[M5] at this;exact (v0 c e).mp this
   . intro h m;rcases hpair:finProdFinEquiv.symm m with ⟨c,e⟩;exact (v0 c e).mpr (h c e)
  rw[a] at H2;exact i7 H1 H2
 have Htail:=q4 (q4 (q6 (q6 HokF HcEq) HokR)
  (d9 HokC (fun _ hf=>hf.elim inl (fun hc=>inr (inl (inr hc)))) Y3 Y3))
  (i7 (t7 (f:=cg n) (g:=cz n) (inr (inl (inl (inl rfl)))) (inr (inr rfl))) (t7 (f:=an (cg n) (cz n)) (g:=ag n) (inr rfl) (inl (inr (inl (inr rfl))))))
 have a6:=q4 (q4 (q4 (q4 (q4 Hprof (q6 Htp HQ))
  (d9 HFzt (by simp only[A2,A1,W6];exact Y3) Y3 Y3))
  (d9 Hext (by simp only[A3,A2,A1,W6];exact Y3) Y3 Y3))
  (d9 (i7 (i7 HTmp HM) HRec) (by simp only[A4,A3,A2,A1,W6];exact Y3) Y3 Y3))
  (d9 Htail (by simp only[A5,A4,A3,A2,A1,W6];exact Y3) Y3 Y3)
 refine aa a6 Y3 ?_ (le_of_eq (by unfold ey;dsimp only;ring));rintro f ((rfl|⟨k,rfl⟩)|hc)
 . exact inr (inr (inr rfl))
 . exact inr (inl (inl (inl (inl (inr (inl ⟨k,rfl⟩))))))
 . exact inr (inr (inl (inl (inl (inr hc)))))
end StageA
namespace RingCode
open S399 StageA
open scoped BigOperators
def d8 (n:ℕ)(m:Fin (2*n)):BV n:=if m.val %2=0 then (true,⟨m.val/2,by omega⟩)
 else (false,⟨m.val/2,by omega⟩)
def e8 (n:ℕ):Fin (2*n) ≃ BV n where
 toFun:=d8 n
 invFun v:=⟨2*v.2.val+(if v.1 then 0 else 1),by have:=v.2.isLt;cases v.1<;>simp<;>omega⟩
 left_inv m:=by apply L6;dsimp only[d8];by_cases h:m.val %2=0<;>simp[h]<;>omega
 right_inv v:=by
  rcases v with ⟨b,i⟩
  cases b
  . unfold d8;have c:¬ (2*i.val+1) %2=0:=(by omega);simp only[J5,↓reduceIte,c,J0,Q0];apply L6;dsimp only;omega
  . unfold d8;have a:(2*i.val+0) %2=0:=(by omega);simp only[↓reduceIte,a,J0,Q0];apply L6;dsimp only;omega
def q7 (n:ℕ)(m:Fin (2*n)):BV n:=if m.val %2=0 then (false,⟨m.val/2,by omega⟩)
 else (true,⟨m.val/2,by omega⟩)
def dj (n:ℕ):Fin (2*n) ≃ BV n where
 toFun:=q7 n
 invFun e:=⟨2*e.2.val+(if e.1 then 1 else 0),by have:=e.2.isLt;cases e.1<;>simp<;>omega⟩
 left_inv m:=by apply L6;dsimp only[q7];by_cases h:m.val %2=0<;>simp[h]<;>omega
 right_inv e:=by
  rcases e with ⟨b,i⟩
  cases b
  . unfold q7;have a:(2*i.val+0) %2=0:=(by omega);simp only[J5,↓reduceIte,a,J0,Q0];apply L6;dsimp only;omega
  . unfold q7;have c:¬ (2*i.val+1) %2=0:=(by omega);simp only[↓reduceIte,c,J0,Q0];apply L6;dsimp only;omega
lemma ql (n:ℕ)(m:Fin (2*n)):(q7 n m).1=decide (m.val %2=1):=by
 unfold q7
 split_ifs with h
 . simp[show m.val %2≠1 by omega]
 . simp[show m.val %2=1 by omega]
lemma jm {n:ℕ}(f:1<=n)(m:Fin (2*n)):g8 (c5 n) (q7 n m)=q7 n ⟨(m.val+1) %(2*n),M1 _ (by omega)⟩:=by
 unfold q7 g8 c5;dsimp only[coe_fn_mk];by_cases e:m.val %2=0
 . simp only[e,↓reduceIte];have a:m.val+1<2*n:=(by omega);have c:¬ (m.val+1) %(2*n) %2=0:=(by rw[L8 a];omega);simp only[c,↓reduceIte,J0,Q0];apply L6;dsimp only;rw[L8 a];omega
 . simp only[e,↓reduceIte];by_cases b:m.val+1=2*n
   . have c:(m.val+1) %(2*n) %2=0:=(by rw[b,mod_self]);have d:m.val/2+1=n:=(by omega);simp only[c,↓reduceIte,J0,Q0];apply L6;dsimp only;rw[b,mod_self,d,mod_self]
   . have a:m.val+1<2*n:=(by omega);have d:m.val/2+1<n:=(by omega);have c:(m.val+1) %(2*n) %2=0:=(by rw[L8 a];omega);simp only[c,↓reduceIte,J0,Q0];apply L6;dsimp only;rw[L8 a,L8 d];omega
lemma fx {n:ℕ}(f:1<=n)(m:Fin (2*n)):p4 (c5 n) (q7 n m)=d8 n ⟨(m.val+1) %(2*n),M1 _ (by omega)⟩:=by
 unfold q7 d8 p4 c5;dsimp only[coe_fn_mk];by_cases e:m.val %2=0
 . simp only[e,↓reduceIte];have a:m.val+1<2*n:=(by omega);have c:¬ (m.val+1) %(2*n) %2=0:=(by rw[L8 a];omega);simp only[c,↓reduceIte,J0,Q0];apply L6;dsimp only;rw[L8 a];omega
 . simp only[e,↓reduceIte];by_cases b:m.val+1=2*n
   . have c:(m.val+1) %(2*n) %2=0:=(by rw[b,mod_self]);have d:m.val/2+1=n:=(by omega);simp only[c,↓reduceIte,J0,Q0];apply L6;dsimp only;rw[b,mod_self,d,mod_self]
   . have a:m.val+1<2*n:=(by omega);have d:m.val/2+1<n:=(by omega);have c:(m.val+1) %(2*n) %2=0:=(by rw[L8 a];omega);simp only[c,↓reduceIte,J0,Q0];apply L6;dsimp only;rw[L8 a,L8 d];omega
lemma cb {n:ℕ}(g:1<=n)(m:Fin (2*n)):p4 (c5 n) ((g8 (c5 n)).symm (q7 n m))=d8 n m:=by
 let a:Fin (2*n):=⟨(m.val+2*n-1) %(2*n),M1 _ (by omega)⟩
 have c:g8 (c5 n) (q7 n a)=q7 n m:=by
  rw[jm g a];congr 1;apply L6;dsimp only[a];by_cases e:m.val=0
  . rw[e];simp only[zero_add];have b:(2*n-1) %(2*n)=2*n-1:=L8 (by omega);rw[b,show 2*n-1+1=2*n by omega,mod_self]
  . have b:(m.val+2*n-1) %(2*n)=m.val-1:=by have f:m.val+2*n-1=(m.val-1)+2*n:=(by omega);rw[f,M2,L8 (by omega)]
    rw[b,show m.val-1+1=m.val by omega,L8 m.isLt]
 have d:(g8 (c5 n)).symm (q7 n m)=q7 n a:=(by rw[<-c,M5]);rw[d,fx g a];congr 1;apply L6;dsimp only[a];by_cases e:m.val=0
 . rw[e];simp only[zero_add];have b:(2*n-1) %(2*n)=2*n-1:=L8 (by omega);rw[b,show 2*n-1+1=2*n by omega,mod_self]
 . have b:(m.val+2*n-1) %(2*n)=m.val-1:=by have f:m.val+2*n-1=(m.val-1)+2*n:=(by omega);rw[f,M2,L8 (by omega)]
   rw[b,show m.val-1+1=m.val by omega,L8 m.isLt]
abbrev c7 (n:ℕ):=Fin 3×Fin n×Y0
def c3 {n:ℕ}(t:c7 n):ℕ:=if t.1.val=2 then 2*t.2.1.val+2 else 2*t.2.1.val+1
def t6 {n:ℕ}(t:c7 n):ℕ:=if t.1.val=1 then t.2.1.val else t.2.1.val+1
def c9 {n:ℕ}(t:c7 n):Y0:=t.2.2
lemma k7 {n:ℕ}(t:c7 n):1<=c3 t/\c3 t<=2*n:=by unfold c3;split_ifs<;>omega
lemma ky {n:ℕ}(t:c7 n):t6 t∈n7 (c3 t):=by
 unfold t6 c3 n7;have a:t.1.val=0\/t.1.val=1\/t.1.val=2:=by have:=t.1.isLt;omega
 rcases a with h|h|h
 . simp[h,show (2*t.2.1.val+1) %2=1 by omega,show (2*t.2.1.val+1)/2=t.2.1.val by omega]
 . simp[h,show (2*t.2.1.val+1) %2=1 by omega,show (2*t.2.1.val+1)/2=t.2.1.val by omega]
 . simp[h,show (2*t.2.1.val+2)/2=t.2.1.val+1 by omega]
lemma aw {n:ℕ} {a b:c7 n}
 (d:c3 a=c3 b) (e:t6 a=t6 b)
 (c:c9 a=c9 b):a=b:=by
 rcases a with ⟨c1,q1,s1⟩
 rcases b with ⟨c2,q2,s2⟩
 simp only[c9] at c;subst c
 fin_cases c1<;>fin_cases c2<;>simp[c3,t6] at d e<;>first|omega|exact Prod.ext rfl (Prod.ext (L6 (by omega)) rfl)
def m5 {n:ℕ}(t:c7 n):Fin (6*n+1):=⟨1+(t.1.val*(2*n)+t.2.1.val*2+t.2.2.toNat),by
  have h1:=t.1.isLt;have h2:=t.2.1.isLt;have a:t.2.2.toNat<=1:=by cases t.2.2<;>simp
  have:t.1.val*(2*n)<=2*(2*n):=W4 _ (by omega)
  omega⟩
lemma o0 {n:ℕ}(t:c7 n):0<(m5 t).val:=by unfold m5;dsimp only;omega
def l3 {n:ℕ}(d:Fin (6*n+1))(b:0<d.val):c7 n:=let c:=d.val-1
 have a:c<6*n:=(by omega);have f:0<n:=by omega
 (⟨c/(2*n),by
  rw[Nat.div_lt_iff_lt_mul (by omega)];omega⟩,
  ⟨(c %(2*n))/2,by
   have e:c %(2*n)<2*n:=M1 _ (by omega)
   omega⟩,
  decide ((c %(2*n)) %2=1))
lemma z2 {n:ℕ}(t:c7 n):l3 (m5 t) (o0 t)=t:=by
 rcases t with ⟨c,q,s⟩
 unfold l3 m5;dsimp only;have h:=c.isLt;have g:=q.isLt;have f:s.toNat<=1:=by cases s<;>simp
 have b:q.val*2+s.toNat<2*n:=(by omega);have a:1+(c.val*(2*n)+q.val*2+s.toNat)-1=(q.val*2+s.toNat)+(2*n)*c.val:=(by ring_nf;omega);have e:(1+(c.val*(2*n)+q.val*2+s.toNat)-1)/(2*n)=c.val:=by rw[a,Nat.add_mul_div_left _ _ (by omega),div_eq_of_lt b,zero_add]
 have d:(1+(c.val*(2*n)+q.val*2+s.toNat)-1) %(2*n)=q.val*2+s.toNat:=(by rw[a,Nat.add_mul_mod_self_left,L8 b]);refine Prod.ext (L6 e) (Prod.ext (L6 ?_) ?_)
 . dsimp only;rw[d];cases s<;>simp<;>omega
 . dsimp only;rw[d];cases s<;>simp<;>omega
lemma p6 {n:ℕ}(d:Fin (6*n+1))(a:0<d.val):m5 (l3 d a)=d:=by
 apply L6;unfold m5 l3;dsimp only;have i:d.val-1<6*n:=(by omega);have g:0<n:=(by omega);set c:=d.val-1;have k:=div_add_mod c (2*n);have j:=div_add_mod (c %(2*n)) 2
 have b:(decide ((c %(2*n)) %2=1)).toNat=(c %(2*n)) %2:=by
  have:(c %(2*n)) %2=0\/(c %(2*n)) %2=1:=by omega
  rcases this with h|h<;>simp[h]
 rw[b];have f:c/(2*n)*(2*n)=2*n*(c/(2*n)):=Nat.mul_comm _ _;have e:c %(2*n)/2*2=2*(c %(2*n)/2):=Nat.mul_comm _ _;omega
lemma bd {n:ℕ}{a b:Fin (6*n+1)}(e:0<a.val)(d:0<b.val)(c:a=b):l3 a e=l3 b d:=by cases c;rfl
lemma w4 (n:ℕ):Injective (@m5 n):=by intro a b h;simpa only[z2] using bd (o0 a) (o0 b) h
def o1 (n:ℕ):c7 n ≃ Fin (6*n) where
 toFun t:=⟨(m5 t).val-1,by have:=(m5 t).isLt;have:=o0 t;omega⟩
 invFun i:=l3 ⟨i.val+1,by have:=i.isLt;omega⟩ (succ_pos i.val)
 left_inv t:=by have a:(⟨(m5 t).val-1+1,by have:=(m5 t).isLt;have:=o0 t;omega⟩:Fin (6*n+1))=m5 t:=L6 (by dsimp only;have:=o0 t;omega);exact (bd _ (o0 t) a).trans (z2 t)
 right_inv i:=L6 (by
  dsimp only;have:=Q6 Fin.val (p6 (⟨i.val+1,by have:=i.isLt;omega⟩:Fin (6*n+1)) (succ_pos i.val))
  dsimp only at this;omega)
def l5 {n:ℕ}(a:Y0)(t:c7 n):Y0:=(t.1.val == 2)||(t.1.val == if a then 1 else 0)
def es {n:ℕ}(a:Y0)(t:c7 n):Y0:=if t.1.val=2 then a else !a
def ea (l:ℕ)(a:Y0):ℕ:=if l %2=0 then l/2 else if a then l/2 else l/2+1
lemma gv {n:ℕ}(a:Y0)(t:c7 n):l5 a t=true↔t6 t=ea (c3 t) a:=by
 unfold l5 t6 c3 ea;have b:t.1.val=0\/t.1.val=1\/t.1.val=2:=by have:=t.1.isLt;omega
 rcases b with h|h|h<;>cases a<;>simp[h]<;>omega
lemma db {n:ℕ}(a:Y0)(t:c7 n):es a t=xor a (decide (c3 t %2=1)):=by
 unfold es c3;have b:t.1.val=0\/t.1.val=1\/t.1.val=2:=by have:=t.1.isLt;omega
 rcases b with h|h|h<;>cases a<;>simp[h]
def bg (n l:ℕ)(b a:Y0)(c:1<=l)(d:l<=2*n):c7 n:=if h:l %2=0 then (⟨2,by decide⟩,⟨l/2-1,by omega⟩,a)
 else if b then (⟨1,by decide⟩,⟨l/2,by omega⟩,a)
 else (⟨0,by decide⟩,⟨l/2,by omega⟩,a)
lemma n1 {n l:ℕ}(a b:Y0)(c:1<=l)(d:l<=2*n):let t:=bg n l a b c d
 c3 t=l/\t6 t=ea l a/\c9 t=b/\l5 a t=true:=by
 unfold bg c3 t6 c9 l5 ea;split_ifs<;>simp_all<;>omega
lemma qm {n:ℕ}(a:Y0)(t:c7 n)(b:l5 a t=true):t=bg n (c3 t) a (c9 t) (k7 t).1 (k7 t).2:=by
 apply aw
 . exact (n1 a (c9 t) (k7 t).1 (k7 t).2).1.symm
 . rw[(gv a t).mp b];exact (n1 a (c9 t) (k7 t).1 (k7 t).2).2.1.symm
 . exact (n1 a (c9 t) (k7 t).1 (k7 t).2).2.2.1.symm
def f4 (n:ℕ)(p:P0 n):List (Fin (2*n)):=(List.finRange (2*n)).filter (fun m=>(p (d8 n m)).isSome)
lemma gp (n:ℕ)(p:P0 n):(f4 n p).Nodup:=(List.nodup_finRange (2*n)).filter _
lemma t8 (n:ℕ)(p:P0 n):(f4 n p).Pairwise (·<·):=by unfold f4;refine List.Pairwise.filter _ ?_;rw[List.pairwise_iff_getElem];intro i j c b a;simp only[List.getElem_finRange];exact a
lemma m9 (n:ℕ)(p:P0 n)(m:Fin (2*n)):m∈f4 n p↔(p (d8 n m)).isSome=true:=by simp[f4,List.mem_finRange]
lemma bo (n:ℕ)(p:P0 n):(f4 n p).length+e3 p=2*n:=by
 have a:(f4 n p).length=(univ.filter (fun m:Fin (2*n)=>(p (d8 n m)).isSome=true)).card:=by rw[<-List.toFinset_card_of_nodup (gp n p)];congr 1;ext m;simp[m9]
 have c:e3 p=(univ.filter (fun m:Fin (2*n)=>¬ ((p (d8 n m)).isSome=true))).card:=by
  unfold e3;refine card_bij (fun v _=>(e8 n).symm v) ?_ ?_ ?_
  . intro v d;simp only[L4,Y2,Q0] at d ⊢;have e:d8 n ((e8 n).symm v)=v:=(e8 n).apply_symm_apply v;rw[e,d];simp
  . intro v1 _ v2 _ h;exact (e8 n).symm.injective h
  . intro m f;simp only[L4,Y2,Q0] at f;refine⟨d8 n m,?_,(e8 n).symm_apply_apply m⟩;simp only[L4,Y2,Q0]
    cases hp:p (d8 n m) with
    | none=>rfl
    | some b=>simp[hp] at f
 rw[a,c,card_filter_add_card_filter_not];simp
lemma af (n:ℕ)(p:P0 n):(f4 n p).length<=2*n:=by have:=bo n p;omega
def m3 (n:ℕ):Fin (2*n+2)->Fin (6*n+1):=fun j=>if j.val=2*n+1 then ⟨2*n,by omega⟩ else ⟨0,by omega⟩
def e5 (n:ℕ)(p:P0 n):Fin (2*n+2)->Fin (6*n+1):=let L:=f4 n p
 if h0:L.length=0 then m3 n
 else let k:=L.length
  have s:0<k:=K2 h0;have u:k<=2*n:=af n p;let o:=L.get ⟨0,s⟩;let t:=(p (d8 n o)).getD false
  fun j=>if j.val=2*n+1 then ⟨o.val,by have:=o.isLt;omega⟩
   else if j.val=2*n then ⟨t.toNat,by cases t<;>simp;omega⟩
   else let b:=2*n-1-j.val
    if hidx:b<k then let a:Fin k:=⟨(b+k-1) %k,M1 _ s⟩
     let c:=L.get a;let d:=L.get ⟨b,hidx⟩;let i:=(p (d8 n c)).getD false;let l:=(p (d8 n d)).getD false;let e:=if c.val<d.val then d.val-c.val else 2*n-c.val+d.val;have q:1<=e:=by have:=c.isLt;have:=d.isLt;dsimp only[e];split_ifs<;>omega
     have r:e<=2*n:=by
      have:=c.isLt;have:=d.isLt;dsimp only[e]
      split_ifs with g
      . omega
      . by_cases h:b=0
        . have v:d.val<=c.val:=by
           have f:=t8 n p;rw[pairwise_iff_get] at f;by_cases m:k=1
           . have:a=⟨b,hidx⟩:=L6 (by dsimp[a];simp[m];omega);simp[c,d,this]
           . have hlt':(⟨b,hidx⟩:Fin k)<a:=by change b<(b+k-1) %k;rw[h,zero_add,L8 (by omega)];omega
             exact le_of_lt (f ⟨b,hidx⟩ a hlt')
          omega
        . exfalso;have f:=t8 n p;rw[pairwise_iff_get] at f;have hlt':a<⟨b,hidx⟩:=by change (b+k-1) %k<b;have m:b+k-1=(b-1)+k:=(by omega);rw[m,M2,L8 (by omega)];omega
          exact g (f a ⟨b,hidx⟩ hlt')
     m5 (bg n e (decide (c.val %2=1)) (decide (i=l)) q r)
    else ⟨0,by omega⟩
def g5 (n:ℕ)(w:Fin (2*n+2)->Fin (6*n+1))(e:Fin (2*n))(c:Y0):ℕ->Fin (2*n)×Y0×(P0 n)
 | 0=>(e,c,fun v=>if v=d8 n e then some c else none)
 | j+1=>
  let a:=g5 n w e c j
  if hj:j+1<2*n then let d:=w ⟨2*n-1-(j+1),by omega⟩
   if hd:0<d.val then let t:=l3 d hd
    let m':Fin (2*n):=⟨(a.1.val+c3 t) %(2*n),M1 _ (by omega)⟩;let b':Y0:=if c9 t then a.2.1 else !a.2.1
    (m',b',fun v=>if v=d8 n m' then some b' else a.2.2 v)
   else a
  else a
def s5 (n:ℕ)(w:Fin (2*n+2)->Fin (6*n+1)):P0 n:=let a:=(w ⟨2*n+1,by omega⟩).val
 if hs:a<2*n then let b:=decide ((w ⟨2*n,by omega⟩).val=1)
  (g5 n w ⟨a,hs⟩ b (2*n-1)).2.2
 else fun _=>none
lemma ez (n:ℕ) (w:Fin (2*n+2)->Fin (6*n+1)) (f:Fin (2*n)) (d:Y0)
 (j:ℕ) (b:∀ i,j < i->i<2*n->(w ⟨2*n-1-i,by omega⟩).val=0):
 ∀ m,j≤m->g5 n w f d m=g5 n w f d j:=by
 intro m g
 induction m with
 | zero=>
  have:j=0:=(by omega);subst this;rfl
 | succ m ih=>
  by_cases e:j=m+1
  . subst e;rfl
  . have c:j<=m:=(by omega);rw[g5];dsimp only;by_cases a:m+1<2*n
    . rw[L7 a,Q8 (by have:=b (m+1) (by omega) a;omega)];exact ih c
    . rw[Q8 a];exact ih c
lemma fl {n:ℕ}(hn:1<=n)(p:P0 n):s5 n (e5 n p)=p:=by
 unfold s5;set L:=f4 n p;by_cases h0:L.length=0
 . have a0:e5 n p=m3 n:=(by simp[e5,L,h0]);rw[a0];simp only[m3,↓reduceIte,lt_irrefl,↓reduceDIte]
   funext v
   have a1:(e8 n).symm v∉L:=(by intro hm;have:=List.length_pos_of_mem hm;omega);have v1:¬ (p (d8 n ((e8 n).symm v))).isSome=true:=(by rwa[<-m9]);rw[show d8 n ((e8 n).symm v)=v from (e8 n).apply_symm_apply v] at v1
   cases hp:p v with
   | none=>rfl
   | some b=>simp[hp] at v1
 . have e:0<L.length:=K2 h0;have a2:L.length<=2*n:=af n p;have v0:L.Pairwise (·<·):=t8 n p;rw[pairwise_iff_get] at v0;have h5:(e5 n p ⟨2*n+1,by omega⟩).val=(L.get ⟨0,e⟩).val:=by simp[e5,L,h0]
   have x2:decide ((e5 n p ⟨2*n,by omega⟩).val=1)=(p (d8 n (L.get ⟨0,e⟩))).getD false:=by
    simp only[e5,L,h0,↓reduceDIte,show ¬ (2*n=2*n+1) by omega,↓reduceIte];cases (p (d8 n (L.get ⟨0,e⟩))).getD false<;>decide
   have h2:(e5 n p ⟨2*n+1,by omega⟩).val<2*n:=(by rw[h5];exact (L.get ⟨0,e⟩).isLt);rw[L7 h2];have v2:(⟨(e5 n p ⟨2*n+1,by omega⟩).val,h2⟩:Fin (2*n))=L.get ⟨0,e⟩:=L6 h5;rw[v2,x2]
   have y1:∀ j (a:j<L.length),let st:=g5 n (e5 n p) (L.get ⟨0,e⟩) ((p (d8 n (L.get ⟨0,e⟩))).getD false) j
    st.1=L.get ⟨j,a⟩ ∧
    st.2.1=(p (d8 n (L.get ⟨j,a⟩))).getD false ∧
    ∀ v,st.2.2 v=if ∃ i:Fin L.length,i.val≤j/\d8 n (L.get i)=v then p v else none:=by
    intro j
    induction j with
    | zero=>
     intro a;refine⟨rfl,rfl,fun v=>?_⟩;dsimp only[g5];by_cases w:v=d8 n (L.get ⟨0,e⟩)
     . subst w;have m:L.get ⟨0,e⟩∈L:=get_mem _ _;have c:(p (d8 n (L.get ⟨0,e⟩))).isSome=true:=(m9 n p _).mp m;have u:∃ i:Fin L.length,i.val≤0/\d8 n (L.get i)=d8 n (L.get ⟨0,e⟩):=⟨⟨0,e⟩,Y3,rfl⟩;rw[Q2 rfl,Q2 u]
       cases hp:p (d8 n (L.get ⟨0,e⟩)) with
       | none=>rw[hp] at c;cases c
       | some b=>rfl
     . have z:¬ ∃ i:Fin L.length,i.val≤0/\d8 n (L.get i)=v:=by rintro⟨i,hi,q⟩;have:i=⟨0,e⟩:=L6 (by dsimp only;omega);subst this;exact w q.symm
       rw[Q3 w,Q3 z]
    | succ j ih=>
     intro a;obtain⟨hm,hb,y⟩:=ih (by omega);have y2:j+1<2*n:=(by omega);have r:2*n-1-(2*n-1-(j+1))=j+1:=by omega
     have x:((j+1)+L.length-1) %L.length=j:=by have:j+1+L.length-1=j+L.length:=(by omega);rw[this,M2,L8 (by omega)]
     have s:(L.get ⟨j,by omega⟩).val<(L.get ⟨j+1,a⟩).val:=v0 ⟨j,by omega⟩ ⟨j+1,a⟩ (by show j<j+1;omega)
     set d:=e5 n p ⟨2*n-1-(j+1),by omega⟩ with t
     have h1:d=m5 (bg n ((L.get ⟨j+1,a⟩).val-(L.get ⟨j,by omega⟩).val)
      (decide ((L.get ⟨j,by omega⟩).val %2=1))
      (decide ((p (d8 n (L.get ⟨j,by omega⟩))).getD false=(p (d8 n (L.get ⟨j+1,a⟩))).getD false))
      (by omega) (by omega)):=by
      rw[t];dsimp only[e5];rw[Q8 h0,Q3 (by dsimp only;omega),Q3 (by dsimp only;omega),L7 (by change 2*n-1-(2*n-1-(j+1))<L.length;omega)];have g:L.get ⟨(2*n-1-(2*n-1-(j+1))+L.length-1) %L.length,M1 _ e⟩=L.get ⟨j,by omega⟩:=(by congr 1;apply L6;dsimp only;rw[r,x]);have k:L.get ⟨2*n-1-(2*n-1-(j+1)),by omega⟩=L.get ⟨j+1,a⟩:=(by congr 1;apply L6;exact r);congr 1;apply aw
      . rw[(n1 _ _ _ _).1,(n1 _ _ _ _).1];dsimp only;rw[g,k,Q2 s]
      . rw[(n1 _ _ _ _).2.1,(n1 _ _ _ _).2.1];dsimp only;rw[g,k,Q2 s]
      . rw[(n1 _ _ _ _).2.2.1,(n1 _ _ _ _).2.2.1];dsimp only;rw[g,k]
     have f:0<d.val:=by rw[h1];exact o0 _
     have o:c3 (l3 d f)=(L.get ⟨j+1,a⟩).val-(L.get ⟨j,by omega⟩).val/\c9 (l3 d f)=decide ((p (d8 n (L.get ⟨j,by omega⟩))).getD false=(p (d8 n (L.get ⟨j+1,a⟩))).getD false):=by
      have x1:l3 d f=bg n ((L.get ⟨j+1,a⟩).val-(L.get ⟨j,by omega⟩).val)
       (decide ((L.get ⟨j,by omega⟩).val %2=1))
       (decide ((p (d8 n (L.get ⟨j,by omega⟩))).getD false=(p (d8 n (L.get ⟨j+1,a⟩))).getD false))
       (by omega) (by omega):=by
       exact (bd f (o0 _) h1).trans (z2 _)
      rw[x1]
      have h9:=n1 (n:=n) (l:=(L.get ⟨j+1,a⟩).val-(L.get ⟨j,by omega⟩).val)
       (decide ((L.get ⟨j,by omega⟩).val %2=1))
       (decide ((p (d8 n (L.get ⟨j,by omega⟩))).getD false=(p (d8 n (L.get ⟨j+1,a⟩))).getD false))
       (by omega) (by omega)
      exact⟨h9.1,h9.2.2.1⟩
     have hm':(⟨((g5 n (e5 n p) (L.get ⟨0,e⟩) ((p (d8 n (L.get ⟨0,e⟩))).getD false) j).1.val +c3 (l3 d f)) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=L.get ⟨j+1,a⟩:=by apply L6;dsimp only;rw[hm,o.1,V3 (le_of_lt s),L8 (L.get ⟨j+1,a⟩).isLt]
     have hb':(if c9 (l3 d f) then (g5 n (e5 n p) (L.get ⟨0,e⟩) ((p (d8 n (L.get ⟨0,e⟩))).getD false) j).2.1
      else !(g5 n (e5 n p) (L.get ⟨0,e⟩) ((p (d8 n (L.get ⟨0,e⟩))).getD false) j).2.1)=
      (p (d8 n (L.get ⟨j+1,a⟩))).getD false:=by
      rw[hb,o.2];cases (p (d8 n (L.get ⟨j,by omega⟩))).getD false<;>cases (p (d8 n (L.get ⟨j+1,a⟩))).getD false<;>rfl
     dsimp only[g5];rw[L7 y2,L7 (t▸f)];refine⟨hm',hb',fun v=>?_⟩;dsimp only;rw[hm',hb'];by_cases w:v=d8 n (L.get ⟨j+1,a⟩)
     . subst w;have m:L.get ⟨j+1,a⟩∈L:=get_mem _ _;have c:(p (d8 n (L.get ⟨j+1,a⟩))).isSome=true:=(m9 n p _).mp m;have u:∃ i:Fin L.length,i.val≤j+1/\d8 n (L.get i)=d8 n (L.get ⟨j+1,a⟩):=⟨⟨j+1,a⟩,Y3,rfl⟩;rw[Q2 rfl,Q2 u]
       cases hp:p (d8 n (L.get ⟨j+1,a⟩)) with
       | none=>rw[hp] at c;cases c
       | some b=>rfl
     . rw[Q3 w,y v];congr 1;apply propext;constructor
       . rintro⟨i,hi,q⟩;exact⟨i,by omega,q⟩
       . rintro⟨i,hi,q⟩;have a5:i.val≠j+1:=(by intro h;apply w;rw[<-q];congr 1;congr 1;exact L6 h);exact⟨i,by omega,q⟩
   have h7:∀ i,L.length-1 < i->i<2*n->(e5 n p ⟨2*n-1-i,by omega⟩).val=0:=by intro i a3 a4;dsimp only[e5];rw[Q8 h0,Q3 (by dsimp only;omega),Q3 (by dsimp only;omega),Q8 (by change ¬ 2*n-1-(2*n-1-i)<L.length;omega)]
   dsimp only;rw[ez n (e5 n p) _ _ (L.length-1) h7 (2*n-1) (by omega)];obtain⟨_,_,y⟩:=y1 (L.length-1) (by omega)
   funext v
   rw[y v];by_cases c:(p v).isSome=true
   . have m:(e8 n).symm v∈L:=(by rw[m9,show d8 n ((e8 n).symm v)=v from (e8 n).apply_symm_apply v];exact c);obtain⟨i,hi⟩:=List.mem_iff_get.mp m;have u:∃ i:Fin L.length,i.val≤L.length-1/\d8 n (L.get i)=v:=⟨i,by omega,by rw[hi];exact (e8 n).apply_symm_apply v⟩;rw[Q2 u]
   . have z:¬ ∃ i:Fin L.length,i.val≤L.length-1/\d8 n (L.get i)=v:=(by rintro⟨i,_,rfl⟩;exact c ((m9 n p _).mp (get_mem _ _)));rw[Q3 z]
     cases hp:p v with
     | none=>rfl
     | some b=>exact absurd (by simp[hp]) c
lemma ls {n:ℕ}(a:1<=n):Injective (e5 n):=Function.LeftInverse.injective (fl a)
def f8 (a b:ℕ->ℕ->ℕ)(l r:ℕ):ℤ:=(if r∈n7 l then (b l r:ℤ)-(a l r:ℤ) else 0) +(if l %2=0/\r %2=0/\r/2∈n7 (l/2) then (a (l/2) (r/2):ℤ) else 0)
lemma bp {n:ℕ}(a:Perm (Fin n))(p:P0 n)(l r:ℕ):e9 a p l r=f8 (j6 a p) (m8 a p) l r:=by
 unfold e9 f8;congr 1
 . by_cases h:r∈n7 l
   . rw[Q2 h]
   . rw[Q3 h,s9 a p h,ai a p h];rfl
 . by_cases b:l %2=0/\r %2=0
   . by_cases c:r/2∈n7 (l/2)
     . rw[Q2 b,Q2 ⟨b.1,b.2,c⟩]
     . rw[Q2 b,Q3 (fun h=>c h.2.2),s9 a p c];rfl
   . rw[Q3 b,Q3 (fun h=>b ⟨h.1,h.2.1⟩)]
lemma nn (n j4 len:ℕ)(h:len<=2*n):((Finset.range len).filter (fun d=>((j4+d) %(2*n)) %2=0)).card=ea len (decide (j4 %2=1)):=by
 have a:∀ d,((j4+d) %(2*n)) %2=(j4+d) %2:=fun d=>(by have:2 ∣ 2*n:=⟨n,rfl⟩;exact Nat.mod_mod_of_dvd (j4+d) this);simp_rw[a]
 induction len with
 | zero=>simp[ea]
 | succ len ih=>
  rw[Finset.range_add_one,Finset.filter_insert];have c:len∉(Finset.range len).filter (fun d=>(j4+d) %2=0):=(by simp);by_cases g:(j4+len) %2=0
  . rw[Q2 g,W9 c,ih (by omega)];unfold ea;have f:(len+1) %2=0↔¬ len %2=0:=(by omega);by_cases e:j4 %2=1<;>by_cases b:len %2=0<;>simp[e,b,f]<;>omega
  . rw[Q3 g,ih (by omega)];unfold ea;have f:(len+1) %2=0↔¬ len %2=0:=(by omega);by_cases e:j4 %2=1<;>by_cases b:len %2=0<;>simp[e,b,f]<;>omega
lemma kz {n:ℕ} (r:1<=n) (p:P0 n)
 (j:∀ v,p v=none):
 f6 (c5 n) p={univ} ∧
 n5 (univ:V7 (BV n))=n ∧
 s3 (univ:V7 (BV n))=n ∧
 m4 (c5 n) p univ=1:=by
 have l:∀ a b:Fin (2*n),EqvGen (o9 (c5 n) p) (q7 n a) (q7 n b):=by
  have o:∀ k:ℕ,∀ a:Fin (2*n),EqvGen (o9 (c5 n) p) (q7 n a)
    (q7 n ⟨(a.val+k) %(2*n),M1 _ (by omega)⟩):=by
   intro k
   induction k with
   | zero=>intro a;simpa[L8 a.isLt] using EqvGen.refl (q7 n a)
   | succ k ih=>intro a;have g:=ih a;set m:Fin (2*n):=⟨(a.val+k) %(2*n),M1 _ (by omega)⟩;have d:o9 (c5 n) p (q7 n m) (g8 (c5 n) (q7 n m)):=⟨by simp[qE,j],rfl⟩;rw[jm r m] at d;have hm':(⟨(m.val+1) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=⟨(a.val+(k+1)) %(2*n),M1 _ (by omega)⟩:=(by apply L6;dsimp only[m];rw[add_mod,mod_mod,<-add_mod,Nat.add_assoc]);rw[hm'] at d;exact EqvGen.trans _ _ _ g (EqvGen.rel _ _ d)
  intro a b;have h:=o ((2*n-a.val)+b.val) a;have f:(⟨(a.val+(2*n-a.val+b.val)) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=b:=by apply L6;dsimp only;have:a.val+(2*n-a.val+b.val)=b.val+2*n:=(by omega);rw[this,M2,L8 b.isLt]
  rwa[f] at h
 have q:∀ e,n8 (c5 n) p e=univ:=fun e=>(by ext e';simp only[n8,L4,Y2,Q0,iff_true];rw[<-show q7 n ((dj n).symm e)=e from (dj n).apply_symm_apply e,<-show q7 n ((dj n).symm e')=e' from (dj n).apply_symm_apply e'];exact l _ _);refine⟨?_,?_,?_,?_⟩
 . ext c;simp only[f6,X5,Y2,Q0,U5,q];exact⟨fun⟨_,h⟩=>h.symm,fun h=>⟨(false,⟨0,r⟩),h.symm⟩⟩
 . unfold n5;refine (card_bij (fun(e:BV n) _=>e.2) (fun _ _=>Y2 _) ?_ ?_).trans (by simp)
   . intro e1 g e2 d f;simp only[L4,Y2,Q0] at g d;exact Prod.ext (g.trans d.symm) f
   . intro i _;exact⟨(false,i),by simp,rfl⟩
 . unfold s3;refine (card_bij (fun(e:BV n) _=>e.2) (fun _ _=>Y2 _) ?_ ?_).trans (by simp)
   . intro e1 g e2 d f;simp only[L4,Y2,Q0] at g d;exact Prod.ext (g.trans d.symm) f
   . intro i _;exact⟨(true,i),by simp,rfl⟩
 . unfold m4;refine prod_eq_one fun e _=>?_;simp[p8,ef,j]
lemma ip {n:ℕ} (g:1<=n) (p:P0 n)
 (e:∀ v,p v=none) (l r:ℕ):
 j6 (c5 n) p l r=(if l=2*n/\r=n then 1 else 0) ∧
 m8 (c5 n) p l r=0:=by
 obtain⟨c,a,f,d⟩:=kz g p e;have b:p9 (univ:V7 (BV n))=2*n:=(by unfold p9;rw[a,f];omega);constructor
 . unfold j6;rw[c,Finset.filter_singleton];by_cases h:l=2*n/\r=n
   . rcases h with ⟨rfl,rfl⟩;simp[b,a,d]
   . have:¬ (p9 (univ:V7 (BV n))=l/\n5 univ=r/\m4 (c5 n) p univ=1):=(by rw[b,a];intro h';exact h ⟨h'.1.symm,h'.2.1.symm⟩);simp[h,this]
 . unfold m8;rw[c,Finset.filter_singleton];have:¬ (p9 (univ:V7 (BV n))=l/\n5 univ=r/\m4 (c5 n) p univ=-1):=(by rw[d];omega);simp[this]
def j7 (n j4 len:ℕ)(a:1<=n):V7 (BV n):=(Finset.range len).image (fun d=>q7 n ⟨(j4+d) %(2*n),M1 _ (by omega)⟩)
lemma be {n j4 len:ℕ}(j:1<=n)(u:1<=len)(p:len<=2*n):(j7 n j4 len j).card=len/\p9 (j7 n j4 len j)=len/\n5 (j7 n j4 len j)=ea len (decide (j4 %2=1)):=by
 have f:InjOn (fun d:ℕ=>q7 n ⟨(j4+d) %(2*n),M1 _ (by omega)⟩) (Finset.range len:Set ℕ):=by
  intro d1 o d2 l m;simp only[Finset.mem_coe,mem_range] at o l;have q:(⟨(j4+d1) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=⟨(j4+d2) %(2*n),M1 _ (by omega)⟩:=(dj n).injective m;have s:(j4+d1) %(2*n)=(j4+d2) %(2*n):=Q6 Fin.val q
  have k:∀ a b,a<2*n->b<2*n->(j4+a) %(2*n)=(j4+b) %(2*n)->a=b:=by
   intro a b w y h;have i:(j4 %(2*n)+a) %(2*n)=(j4 %(2*n)+b) %(2*n):=(by simpa[add_mod] using h);have v:=M1 j4 (show 0<2*n by omega);by_cases e:j4 %(2*n)+a<2*n<;>by_cases g:j4 %(2*n)+b<2*n
   . rw[L8 e,L8 g] at i;omega
   . rw[L8 e,show j4 %(2*n)+b=(j4 %(2*n)+b-2*n)+2*n by omega,M2,L8 (show j4 %(2*n)+b-2*n<2*n by omega)] at i;omega
   . rw[L8 g,show j4 %(2*n)+a=(j4 %(2*n)+a-2*n)+2*n by omega,M2,L8 (show j4 %(2*n)+a-2*n<2*n by omega)] at i;omega
   . rw[show j4 %(2*n)+a=(j4 %(2*n)+a-2*n)+2*n by omega,show j4 %(2*n)+b=(j4 %(2*n)+b-2*n)+2*n by omega,M2,M2,L8 (show j4 %(2*n)+a-2*n<2*n by omega),L8 (show j4 %(2*n)+b-2*n<2*n by omega)] at i;omega
  exact k d1 d2 (by omega) (by omega) s
 have c:(j7 n j4 len j).card=len:=(by unfold j7;rw[Finset.card_image_of_injOn f,W1]);refine⟨c,by rw[bj,c],?_⟩;unfold n5 j7;rw[filter_image,Finset.card_image_of_injOn (f.mono (by intro x t;exact (L4.mp t).1))];rw[<-nn n j4 len p];congr 1;ext d;simp only[L4,mem_range,ql];constructor<;>rintro⟨r,h⟩<;>refine⟨r,?_⟩
 . simp only[M7] at h;omega
 . simp only[M7];omega
lemma iq {n j4 len:ℕ} (s:1<=n)
 (p:P0 n) (x2:1<=len) (a1:len<=2*n)
 (m:(p (d8 n ⟨j4 %(2*n),M1 _ (by omega)⟩)).isSome=true)
 (u:(p (d8 n ⟨(j4+len) %(2*n),M1 _ (by omega)⟩)).isSome=true)
 (h4:∀ d,d+1<len->p (d8 n ⟨(j4+d+1) %(2*n),M1 _ (by omega)⟩)=none):
 n8 (c5 n) p (q7 n ⟨j4 %(2*n),M1 _ (by omega)⟩)=j7 n j4 len s ∧
 m4 (c5 n) p (j7 n j4 len s)=if(p (d8 n ⟨j4 %(2*n),M1 _ (by omega)⟩)).getD false=(p (d8 n ⟨(j4+len) %(2*n),M1 _ (by omega)⟩)).getD false
  then 1 else -1:=by
 let f:ℕ->BV n:=fun d=>q7 n ⟨(j4+d) %(2*n),M1 _ (by omega)⟩;have k:∀ d,g8 (c5 n) (f d)=f (d+1):=fun d=>(by dsimp only[f];rw[jm s];congr 1;apply L6;dsimp only;rw[add_mod,mod_mod,<-add_mod,Nat.add_assoc]);have g:∀ d,d+1<len->qE (c5 n) p (f d)=none:=fun d q=>by dsimp only[f,qE];rw[fx s];have o:(⟨((j4+d) %(2*n)+1) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=⟨(j4+d+1) %(2*n),M1 _ (by omega)⟩:=(by apply L6;dsimp only;rw[add_mod,mod_mod,<-add_mod]);rw[o];exact h4 d q
 have r:qE (c5 n) p (f (len-1))≠none:=by
  dsimp only[f,qE];rw[fx s];have o:(⟨((j4+(len-1)) %(2*n)+1) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=⟨(j4+len) %(2*n),M1 _ (by omega)⟩:=by apply L6;dsimp only;rw[add_mod,mod_mod,<-add_mod,show j4+(len-1)+1=j4+len by omega]
  rw[o];intro h;rw[h] at u;simp at u
 have i:qE (c5 n) p ((g8 (c5 n)).symm (f 0))≠none:=by dsimp only[f,qE];rw[cb s];simp only[add_zero];intro h;rw[h] at m;simp at m
 have v:∀ d<len,ReflTransGen (o9 (c5 n) p) (f 0) (f d):=by
  intro d
  induction d with
  | zero=>intro _;exact ReflTransGen.refl
  | succ d ih=>intro q;refine ReflTransGen.tail (ih (by omega)) ⟨g d q,(k d).symm⟩
 have h5:n8 (c5 n) p (f 0)=j7 n j4 len s:=by
  ext e;simp only[n8,L4,Y2,Q0,j7,X5,mem_range];constructor
  . intro h7;have x0:=eh h7
    rcases x0 with h8|hbwd
    . have w:∀ x,ReflTransGen (o9 (c5 n) p) (f 0) x->∃ d<len,f d=x:=by
       intro x hx
       induction hx with
       | refl=>exact⟨0,by omega,rfl⟩
       | tail _ hstep ih=>
        obtain⟨d,q,rfl⟩:=ih;by_cases z:d=len-1
        . subst z;exact absurd hstep.1 r
        . refine⟨d+1,by omega,?_⟩;rw[hstep.2,k d]
      exact w e h8
    . have h3:∀ x,ReflTransGen (o9 (c5 n) p) x (f 0)->x=f 0:=by
       intro x hx
       cases hx using ReflTransGen.head_induction_on with
       | refl=>rfl
       | head hstep hrest=>
        rcases ReflTransGen.cases_tail hrest with o|htail
        . subst o;have:x=(g8 (c5 n)).symm (f 0):=(by rw[hstep.2,M5]);rw[this] at hstep;exact absurd hstep.1 i
        . obtain⟨c,_,hc⟩:=htail;have:c=(g8 (c5 n)).symm (f 0):=(by rw[hc.2,M5]);rw[this] at hc;exact absurd hc.1 i
      exact⟨0,by omega,(h3 e hbwd).symm⟩
  . rintro⟨d,q,rfl⟩
    have t:∀ a b,ReflTransGen (o9 (c5 n) p) a b->EqvGen (o9 (c5 n) p) a b:=by
     intro a b y1;induction y1 with
     | refl=>exact EqvGen.refl _
     | tail _ hstep ih=>exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hstep)
    exact t _ _ (v d q)
 refine⟨by simpa[f] using h5,?_⟩;have v0:InjOn f (Finset.range len:Set ℕ):=by intro d1 a0 d2 x1 o;have l:=(be (j4:=j4) (len:=len) s x2 a1).1;unfold j7 at l;have hcard':((Finset.range len).image f).card=(Finset.range len).card:=(by simpa using l);exact Finset.injOn_of_card_image_eq hcard' a0 x1 o
 unfold m4 j7;change (∏ e∈(Finset.range len).image f,(p8 (R:=ℤ) (c5 n) p e*p8 (c5 n) p ((g8 (c5 n)).symm e)))=_;rw[prod_image v0,M3]
 have v2:(∏ d∈Finset.range len,p8 (R:=ℤ) (c5 n) p (f d))=ef (R:=ℤ) p (d8 n ⟨(j4+len) %(2*n),M1 _ (by omega)⟩):=by
  rw[Finset.prod_eq_single (len-1)]
  . unfold p8 f;rw[fx s];congr 2;apply L6;dsimp only;rw[add_mod,mod_mod,<-add_mod,show j4+(len-1)+1=j4+len by omega]
  . intro d q a2;rw[mem_range] at q;have j:=g d (by omega);unfold p8 ef;unfold qE at j;rw[j]
  . intro h0;exfalso;exact h0 (mem_range.mpr (by omega))
 have y2:(∏ d∈Finset.range len,p8 (R:=ℤ) (c5 n) p ((g8 (c5 n)).symm (f d)))=ef (R:=ℤ) p (d8 n ⟨j4 %(2*n),M1 _ (by omega)⟩):=by
  rw[Finset.prod_eq_single 0]
  . unfold p8 f;rw[cb s];simp
  . intro d q a2;rw[mem_range] at q
    have y:(g8 (c5 n)).symm (f d)=f (d-1):=by
     conv_lhs=>rw[show d=(d-1)+1 by omega]
     rw[<-k (d-1),M5]
    rw[y];have j:=g (d-1) (by omega);unfold p8 ef;unfold qE at j;rw[j]
  . intro h0;exfalso;exact h0 (mem_range.mpr (by omega))
 rw[v2,y2];unfold ef
 cases h1:p (d8 n ⟨j4 %(2*n),M1 _ (by omega)⟩) with
 | none=>simp[h1] at m
 | some b1=>
  cases h2:p (d8 n ⟨(j4+len) %(2*n),M1 _ (by omega)⟩) with
  | none=>simp[h2] at u
  | some b2=>cases b1<;>cases b2<;>decide
def d5 {n k:ℕ}(a:Y0)(t:Fin k->c7 n):ℕ->Y0
 | 0=>a
 | j+1=>if h:j<k then es (d5 a t j) (t ⟨j,h⟩) else d5 a t j
def o6 {n k:ℕ}(t:Fin k->c7 n)(l r:ℕ)(a:Y0):ℕ:=(univ.filter (fun j:Fin k=>c3 (t j)=l/\t6 (t j)=r/\c9 (t j)=a)).card
def w8 (n:ℕ)(a:ℕ)(c:ℕ->ℕ->ℤ)(w:Fin (2*n+2)->Fin (6*n+1)):Prop:=if hk0:a=0 then w=m3 n/\∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (fun d e=>if d=2*n/\e=n then 1 else 0) (fun _ _=>0) l r=c l r
 else a<=2*n/\(w ⟨2*n+1,by omega⟩).val<2*n/\(w ⟨2*n,by omega⟩).val<2/\(∀ j:Fin (2*n),j.val<a->0<(w ⟨2*n-1-j.val,by omega⟩).val)/\(∀ j:Fin (2*n),a≤j.val->(w ⟨2*n-1-j.val,by omega⟩).val=0)/\∃(t:Fin a->c7 n),(∀ j:Fin a,w ⟨2*n-1-j.val,by omega⟩=m5 (t j))/\(w ⟨2*n+1,by omega⟩).val<c3 (t ⟨0,by omega⟩)/\let b:=decide ((2*n+(w ⟨2*n+1,by omega⟩).val-c3 (t ⟨0,by omega⟩)) %2=1)
   (∀ j:Fin a,l5 (d5 b t j.val) (t j)=true) ∧
   d5 b t a=b ∧
   (∑ j:Fin a,c3 (t j))=2*n ∧
   (univ.filter (fun j:Fin a=>c9 (t j)=false)).card %2=0 ∧
   ∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (fun d e=>o6 t d e true)
     (fun d e=>o6 t d e false) l r=c l r
lemma oc {k:ℕ}(b:Fin k->Y0):(univ.filter (fun j:Fin k=>b ⟨(j.val+k-1) %k,by have:=j.isLt;exact M1 _ (by omega)⟩≠b j)).card %2=0:=by
 by_cases l:k=0
 . subst l;simp
 . have a:0<k:=K2 l
   have d:(∏ j:Fin k,q0 (R:=ℤ) (b ⟨(j.val+k-1) %k,M1 _ a⟩)*q0 (R:=ℤ) (b j))=1:=by
    rw[M3]
    let c:Fin k ≃ Fin k:={
     toFun:=fun j=>⟨(j.val+k-1) %k,M1 _ a⟩
     invFun:=fun j=>⟨(j.val+1) %k,M1 _ a⟩
     left_inv:=fun j=>by
      apply L6;dsimp only;by_cases g:j.val=0
      . rw[g];simp[L8 (show k-1<k by omega),show k-1+1=k by omega]
      . have h:(j.val+k-1) %k=j.val-1:=by rw[show j.val+k-1=(j.val-1)+k by omega,M2,L8 (by omega)]
        rw[h,show j.val-1+1=j.val by omega,L8 j.isLt]
     right_inv:=fun j=>by
      apply L6;dsimp only;by_cases g:j.val+1=k
      . rw[g,mod_self,zero_add,L8 (by omega)];omega
      . have h:(j.val+1) %k=j.val+1:=L8 (by omega);rw[h,show j.val+1+k-1=j.val+k by omega,M2,L8 j.isLt]
    }
    have i:(∏ j:Fin k,q0 (R:=ℤ) (b (c j)))=∏ j:Fin k,q0 (R:=ℤ) (b j):=prod_equiv c _ (fun j=>q0 (R:=ℤ) (b j)) (fun _=>rfl);rw[show (∏ j:Fin k,q0 (R:=ℤ) (b ⟨(j.val+k-1) %k,M1 _ a⟩))=∏ j:Fin k,q0 (R:=ℤ) (b (c j)) from rfl,i,<-M3];refine prod_eq_one fun j _=>km (b j)
   have f:(∏ j:Fin k,q0 (R:=ℤ) (b ⟨(j.val+k-1) %k,M1 _ a⟩)*q0 (R:=ℤ) (b j))=(-1:ℤ)^(univ.filter (fun j:Fin k=>b ⟨(j.val+k-1) %k,M1 _ a⟩≠b j)).card:=by
    have e:∀ j:Fin k,q0 (R:=ℤ) (b ⟨(j.val+k-1) %k,M1 _ a⟩)*q0 (R:=ℤ) (b j)=if b ⟨(j.val+k-1) %k,M1 _ a⟩≠b j then (-1:ℤ) else 1:=fun j=>by
     cases b ⟨(j.val+k-1) %k,M1 _ a⟩<;>cases b j<;>decide
    simp_rw[e];rw[prod_ite,prod_const,Finset.prod_const_one,mul_one]
   rw[f] at d
   rcases Nat.even_or_odd (univ.filter (fun j:Fin k=>b ⟨(j.val+k-1) %k,M1 _ a⟩≠b j)).card with ⟨m,n⟩|⟨m,n⟩
   . omega
   . rw[n,X6,pow_mul] at d;norm_num at d
lemma ir {n:ℕ}(w:1<=n)(p:P0 n):w8 n (2*n-e3 p) (e9 (c5 n) p) (e5 n p):=by
 set L:=f4 n p;have hlen:L.length+e3 p=2*n:=bo n p;have r4:L.length=2*n-e3 p:=(by omega);unfold w8;by_cases h0:2*n-e3 p=0
 . rw[L7 h0];have y1:L.length=0:=by omega
   have r7:∀ v,p v=none:=fun v=>by
    have p1:(e8 n).symm v∉L:=(by intro hm;have:=List.length_pos_of_mem hm;omega);have ha:¬ (p (d8 n ((e8 n).symm v))).isSome=true:=(by rwa[<-m9]);rw[show d8 n ((e8 n).symm v)=v from (e8 n).apply_symm_apply v] at ha
    cases hp:p v with
    | none=>rfl
    | some b=>simp[hp] at ha
   refine⟨by simp[e5,L,y1],fun l _ r _=>?_⟩;rw[bp];have h1:=ip w p r7;unfold f8;simp only[h1]
 . rw[Q8 h0];have y1:L.length≠0:=(by omega);have q:0<L.length:=K2 y1;have hkle:L.length<=2*n:=af n p;have h4:L.Pairwise (·<·):=t8 n p;rw[pairwise_iff_get] at h4
   set k:=2*n-e3 p with hz
   have ho:k=L.length:=r4.symm;let o:Fin k->Fin (2*n):=fun j=>L.get ⟨j.val,by omega⟩;let e:Fin k->Fin (2*n):=fun j=>L.get ⟨(j.val+L.length-1) %L.length,M1 _ q⟩
   let g:Fin k->ℕ:=fun j=>if(e j).val<(o j).val then (o j).val-(e j).val
    else 2*n-(e j).val+(o j).val
   have f:∀ j:Fin k,1≤g j/\g j≤2*n:=fun j=>by
    have:=(e j).isLt;have:=(o j).isLt;dsimp only[g,e,o] at *
    split_ifs with u
    . omega
    . by_cases d1:j.val=0
      . have hsle:(L.get ⟨j.val,by omega⟩).val<=(L.get ⟨(j.val+L.length-1) %L.length,M1 _ q⟩).val:=by
         by_cases h1:L.length=1
         . have:(⟨(j.val+L.length-1) %L.length,M1 _ q⟩:Fin L.length)=⟨j.val,by omega⟩:=L6 (by dsimp only;simp[h1];omega);rw[this]
         . have hlt':(⟨j.val,by omega⟩:Fin L.length)<⟨(j.val+L.length-1) %L.length,M1 _ q⟩:=by change j.val<(j.val+L.length-1) %L.length;rw[d1,zero_add,L8 (by omega)];omega
           exact le_of_lt (h4 _ _ hlt')
        omega
      . exfalso;have hlt':(⟨(j.val+L.length-1) %L.length,M1 _ q⟩:Fin L.length)<⟨j.val,by omega⟩:=by change (j.val+L.length-1) %L.length<j.val;rw[show j.val+L.length-1=(j.val-1)+L.length by omega,M2,L8 (by omega)];omega
        exact u (h4 _ _ hlt')
   let t:Fin k->c7 n:=fun j=>bg n (g j) (decide ((e j).val %2=1))
     (decide ((p (d8 n (e j))).getD false=(p (d8 n (o j))).getD false))
     (f j).1 (f j).2
   have b8:∀ j:Fin k,e5 n p ⟨2*n-1-j.val,by omega⟩=m5 (t j):=fun j=>by unfold e5;simp only[L,y1,↓reduceDIte,show ¬ (2*n-1-j.val=2*n+1) by omega,show ¬ (2*n-1-j.val=2*n) by omega,↓reduceIte,show 2*n-1-(2*n-1-j.val)=j.val by omega,show j.val<L.length by omega];rfl
   have x1:(e5 n p ⟨2*n+1,by omega⟩).val=(o ⟨0,by omega⟩).val:=by simp[e5,L,y1,o]
   have p2:(e5 n p ⟨2*n,by omega⟩).val<2:=by
    simp only[e5,L,y1,↓reduceDIte,show ¬ (2*n=2*n+1) by omega,↓reduceIte];cases (p (d8 n (L.get ⟨0,q⟩))).getD false<;>decide
   have z:∀ j:Fin k,c3 (t j)=g j:=fun j=>(n1 _ _ (f j).1 (f j).2).1;have b4:∀ j:Fin k,t6 (t j)=ea (g j) (decide ((e j).val %2=1)):=fun j=>(n1 _ _ (f j).1 (f j).2).2.1;have b3:∀ j:Fin k,c9 (t j)=decide ((p (d8 n (e j))).getD false=(p (d8 n (o j))).getD false):=fun j=>(n1 _ _ (f j).1 (f j).2).2.2.1
   have x2:g ⟨0,by omega⟩=2*n-(L.get ⟨L.length-1,by omega⟩).val+(o ⟨0,by omega⟩).val:=by
    dsimp only[g,e,o];have h5:(0+L.length-1) %L.length=L.length-1:=by rw[zero_add,L8 (by omega)]
    have a1:L.get ⟨(0+L.length-1) %L.length,M1 _ q⟩=L.get ⟨L.length-1,by omega⟩:=Q6 L.get (L6 h5);simp only[a1]
    have q1:¬ (L.get ⟨L.length-1,by omega⟩).val<(L.get ⟨0,by omega⟩).val:=by
     by_cases h1:L.length=1
     . have:(⟨L.length-1,by omega⟩:Fin L.length)=⟨0,by omega⟩:=L6 (by dsimp only;omega);rw[this];omega
     . exact not_lt_of_ge (le_of_lt (h4 ⟨0,by omega⟩ ⟨L.length-1,by omega⟩ (by show 0<L.length-1;omega)))
    rw[Q3 q1]
   have c1:∀ j:Fin k,0<j.val->g j=(o j).val-(L.get ⟨j.val-1,by omega⟩).val:=fun j hj=>by
    dsimp only[g,e,o];have h5:(j.val+L.length-1) %L.length=j.val-1:=by rw[show j.val+L.length-1=(j.val-1)+L.length by omega,M2,L8 (by omega)]
    have a1:L.get ⟨(j.val+L.length-1) %L.length,M1 _ q⟩=L.get ⟨j.val-1,by omega⟩:=Q6 L.get (L6 h5);simp only[a1];exact Q2 (h4 ⟨j.val-1,by omega⟩ ⟨j.val,by omega⟩ (by show j.val-1<j.val;omega))
   have b7:(e5 n p ⟨2*n+1,by omega⟩).val<c3 (t ⟨0,by omega⟩):=by rw[x1,z,x2];have:=(L.get ⟨L.length-1,by omega⟩).isLt;omega
   have a5:decide ((2*n+(e5 n p ⟨2*n+1,by omega⟩).val-c3 (t ⟨0,by omega⟩)) %2=1)=decide ((e ⟨0,by omega⟩).val %2=1):=by
    rw[x1,z,x2];have h5:(0+L.length-1) %L.length=L.length-1:=by rw[zero_add,L8 (by omega)]
    have a1:e ⟨0,by omega⟩=L.get ⟨L.length-1,by omega⟩:=Q6 L.get (L6 h5);rw[a1];have h1:=(L.get ⟨L.length-1,by omega⟩).isLt;have h2:=(o ⟨0,by omega⟩).isLt;have h9:2*n+(o ⟨0,by omega⟩).val-(2*n-(L.get ⟨L.length-1,by omega⟩).val+(o ⟨0,by omega⟩).val)=(L.get ⟨L.length-1,by omega⟩).val:=(by omega);rw[h9]
   have k0:∀ m (hm:m≤k),d5 (decide ((e ⟨0,by omega⟩).val %2=1)) t m=if u:m<k then decide ((e ⟨m,u⟩).val %2=1)
     else decide ((e ⟨0,by omega⟩).val %2=1):=by
    intro m
    induction m with
    | zero=>intro _;simp[d5,show 0<k by omega]
    | succ m ih=>
     intro hm;rw[d5,L7 (by omega),ih (by omega),L7 (by omega),db,z];by_cases u:m+1<k
     . rw[L7 u];have f1:e ⟨m+1,u⟩=o ⟨m,by omega⟩:=by dsimp only[e,o];congr 1;apply L6;dsimp only;rw[show m+1+L.length-1=m+L.length by omega,M2,L8 (by omega)]
       rw[f1];have hl:(o ⟨m,by omega⟩).val %2=((e ⟨m,by omega⟩).val+g ⟨m,by omega⟩) %2:=(by dsimp only[g];split_ifs<;>omega);have hp:(o ⟨m,by omega⟩).val %2=1↔((e ⟨m,by omega⟩).val %2=1↔¬ g ⟨m,by omega⟩ %2=1):=(by omega);by_cases h1:(e ⟨m,by omega⟩).val %2=1<;>by_cases h2:g ⟨m,by omega⟩ %2=1<;>simp[h1,h2,hp]
     . rw[Q8 u];have hq:m=L.length-1:=by omega
       have c2:o ⟨m,by omega⟩=e ⟨0,by omega⟩:=by dsimp only[o,e];congr 1;apply L6;dsimp only;rw[zero_add,L8 (by omega)];omega
       have hl:(e ⟨0,by omega⟩).val %2=((e ⟨m,by omega⟩).val+g ⟨m,by omega⟩) %2:=(by rw[<-c2];dsimp only[g];split_ifs<;>omega);have hp:(e ⟨0,by omega⟩).val %2=1↔((e ⟨m,by omega⟩).val %2=1↔¬ g ⟨m,by omega⟩ %2=1):=(by omega);by_cases h1:(e ⟨m,by omega⟩).val %2=1<;>by_cases h2:g ⟨m,by omega⟩ %2=1<;>simp[h1,h2,hp]
   have y2:(∑ j:Fin k,c3 (t j))=2*n:=by
    simp_rw[z]
    have s0:∀ m (hm:m<k),(∑ j∈univ.filter (fun j:Fin k=>j.val<=m),g j)=2*n-(L.get ⟨L.length-1,by omega⟩).val+(L.get ⟨m,by omega⟩).val:=by
     intro m
     induction m with
     | zero=>intro hm;have b0:univ.filter (fun j:Fin k=>j.val<=0)={⟨0,by omega⟩}:=(by ext j;simp only[L4,Y2,Q0,U5,K4];omega);rw[b0,sum_singleton,x2]
     | succ m ih=>intro hm;have b0:univ.filter (fun j:Fin k=>j.val<=m+1)=insert ⟨m+1,hm⟩ (univ.filter (fun j:Fin k=>j.val<=m)):=(by ext j;simp only[L4,Y2,Q0,X3,K4];omega);have p1:(⟨m+1,hm⟩:Fin k)∉univ.filter (fun j:Fin k=>j.val<=m):=(by simp);rw[b0,sum_insert p1,ih (by omega),c1 ⟨m+1,hm⟩ (succ_pos m)];have h9:(⟨(⟨m+1,hm⟩:Fin k).val-1,by omega⟩:Fin L.length)=⟨m,by omega⟩:=L6 (by dsimp only;omega);rw[h9];have u:=h4 ⟨m,by omega⟩ ⟨m+1,by omega⟩ (by show m<m+1;omega);have s2:=(L.get ⟨L.length-1,by omega⟩).isLt;dsimp only[o];omega
    have hh:(univ:V7 (Fin k))=univ.filter (fun j:Fin k=>j.val<=k-1):=(by ext j;simp only[L4,Y2,Q0,true_iff];have:=j.isLt;omega);rw[hh,s0 (k-1) (by omega)];have v1:(⟨k-1,by omega⟩:Fin L.length)=⟨L.length-1,by omega⟩:=L6 (by dsimp only;omega);rw[v1];have s2:=(L.get ⟨L.length-1,by omega⟩).isLt;omega
   have s:∀ j:Fin k,n8 (c5 n) p (q7 n (e j))=j7 n (e j).val (g j) w/\m4 (c5 n) p (j7 n (e j).val (g j) w)=if c9 (t j) then 1 else -1:=fun j=>by
    have a6:(⟨(e j).val %(2*n),M1 _ (by omega)⟩:Fin (2*n))=e j:=L6 (L8 (e j).isLt)
    have a7:(⟨((e j).val+g j) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=o j:=by
     apply L6;dsimp only;dsimp only[g]
     split_ifs with u
     . rw[V3 (le_of_lt u),L8 (o j).isLt]
     . have:(e j).val+(2*n-(e j).val+(o j).val)=(o j).val+2*n:=(by have:=(e j).isLt;omega);rw[this,M2,L8 (o j).isLt]
    have e0:(p (d8 n ⟨(e j).val %(2*n),M1 _ (by omega)⟩)).isSome=true:=(by rw[a6];exact (m9 n p _).mp (get_mem _ _));have e2:(p (d8 n ⟨((e j).val+g j) %(2*n),M1 _ (by omega)⟩)).isSome=true:=by rw[a7];exact (m9 n p _).mp (get_mem _ _)
    have b6:∀ d,d+1<g j->p (d8 n ⟨((e j).val+d+1) %(2*n),M1 _ (by omega)⟩)=none:=by
     intro d hd;set m:Fin (2*n):=⟨((e j).val+d+1) %(2*n),M1 _ (by omega)⟩;by_contra hne
     have t2:(p (d8 n m)).isSome=true:=by cases hp:p (d8 n m) with|none=>exact absurd hp hne|some _=>rfl
     have d2:m∈L:=(m9 n p m).mpr t2;obtain⟨i,hi⟩:=List.mem_iff_get.mp d2;have v2:m.val=((e j).val+d+1) %(2*n):=rfl;dsimp only[g] at hd
     split_ifs at hd with u
     . have t1:(e j).val+d+1<2*n:=(by have:=(o j).isLt;omega);rw[L8 t1] at v2;have w1:(e j).val<(L.get i).val:=(by rw[hi];omega);have hlt2:(L.get i).val<(o j).val:=by rw[hi];omega
       have hj_pos:0<j.val:=by
        by_contra d1;have:j.val=0:=by omega
        have h5:(j.val+L.length-1) %L.length=L.length-1:=by rw[this,zero_add,L8 (by omega)]
        have hge:(o j).val<=(e j).val:=by
         dsimp only[o,e];by_cases h1:L.length=1
         . have:(⟨(j.val+L.length-1) %L.length,M1 _ q⟩:Fin L.length)=⟨j.val,by omega⟩:=L6 (by dsimp only;simp[h1];omega);rw[this]
         . exact le_of_lt (h4 ⟨j.val,by omega⟩ ⟨(j.val+L.length-1) %L.length,M1 _ q⟩ (by show j.val<(j.val+L.length-1) %L.length;rw[h5];omega))
        omega
       have h3:(j.val+L.length-1) %L.length=j.val-1:=by rw[show j.val+L.length-1=(j.val-1)+L.length by omega,M2,L8 (by omega)]
       have hi1:j.val-1 < i.val:=by
        by_contra g0
        rcases eq_or_lt_of_le (Nat.le_of_not_lt g0) with v1|hlt'
        . have:L.get i=e j:=Q6 L.get (L6 (by dsimp only;rw[h3];omega));omega
        . have q2:(L.get i).val<(e j).val:=h4 i ⟨(j.val+L.length-1) %L.length,M1 _ q⟩ (by show i.val<(j.val+L.length-1) %L.length;rw[h3];omega);omega
       have hi2:i.val<j.val:=by
        by_contra g0
        rcases eq_or_lt_of_le (Nat.le_of_not_lt g0) with v1|hlt'
        . have:L.get i=o j:=Q6 L.get (L6 (by dsimp only;omega));omega
        . have q2:(o j).val<(L.get i).val:=h4 ⟨j.val,by omega⟩ i (by show j.val < i.val;omega);omega
       omega
     . have d1:j.val=0:=by
        by_contra hne0;have h3:(j.val+L.length-1) %L.length=j.val-1:=by rw[show j.val+L.length-1=(j.val-1)+L.length by omega,M2,L8 (by omega)]
        exact u (h4 ⟨(j.val+L.length-1) %L.length,M1 _ q⟩ ⟨j.val,by omega⟩ (by show (j.val+L.length-1) %L.length<j.val;rw[h3];omega))
       have b2:e j=L.get ⟨L.length-1,by omega⟩:=by dsimp only[e];congr 1;apply L6;dsimp only;rw[d1,zero_add,L8 (by omega)]
       have b1:o j=L.get ⟨0,q⟩:=(by dsimp only[o];congr 1;apply L6;exact d1);by_cases s1:(e j).val+d+1<2*n
       . rw[L8 s1] at v2;have w1:(L.get ⟨L.length-1,by omega⟩).val<(L.get i).val:=by rw[hi,<-b2];omega
         have g0:(L.get i).val<=(L.get ⟨L.length-1,by omega⟩).val:=by
          by_cases hil:i.val=L.length-1
          . have:i=⟨L.length-1,by omega⟩:=L6 hil;rw[this]
          . exact le_of_lt (h4 i ⟨L.length-1,by omega⟩ (by show i.val<L.length-1;omega))
         omega
       . have r1:((e j).val+d+1) %(2*n)=(e j).val+d+1-2*n:=by
          have:=(e j).isLt;have:=(o j).isLt
          conv_lhs=>rw[show (e j).val+d+1=((e j).val+d+1-2*n)+2*n by omega]
          rw[M2,L8 (by omega)]
         rw[r1] at v2;have hlt0:(L.get i).val<(L.get ⟨0,q⟩).val:=by rw[hi,<-b1];omega
         have hge0:(L.get ⟨0,q⟩).val<=(L.get i).val:=by
          by_cases hi0:i.val=0
          . have:i=⟨0,q⟩:=L6 hi0;rw[this]
          . exact le_of_lt (h4 ⟨0,q⟩ i (by show 0 < i.val;omega))
         omega
    have e1:=iq w p (f j).1 (f j).2 e0 e2 b6;rw[a6,a7] at e1;refine⟨e1.1,?_⟩;rw[e1.2,b3 j];by_cases hb:(p (d8 n (e j))).getD false=(p (d8 n (o j))).getD false<;>simp[hb]
   have x0:∀ c∈f6 (c5 n) p,∃! j:Fin k,c=j7 n (e j).val (g j) w:=by
    have k1:∀ j:Fin k,j7 n (e j).val (g j) w∈f6 (c5 n) p:=fun j=>by rw[<-(s j).1];exact mem_image_of_mem _ (Y2 _)
    have b9:Injective (fun j:Fin k=>j7 n (e j).val (g j) w):=by
     classical
     intro j1 j2 v1;dsimp only at v1;have h7:n8 (c5 n) p (q7 n (e j1))=n8 (c5 n) p (q7 n (e j2)):=(by rw[(s j1).1,(s j2).1,v1]);have r6:q7 n (e j2)∈n8 (c5 n) p (q7 n (e j1)):=(by rw[h7];unfold n8;rw[L4];exact⟨Y2 _,EqvGen.refl _⟩);have hg:=(L4.mp r6).2
     have a4:∀ x y,EqvGen (o9 (c5 n) p) x y->qE (c5 n) p ((g8 (c5 n)).symm x)≠none->qE (c5 n) p ((g8 (c5 n)).symm y)≠none->x=y:=by
      intro x y hxy hx hy;have f2:∀ a b,o9 (c5 n) p a b->qE (c5 n) p ((g8 (c5 n)).symm b)=none:=by intro a b w2;rw[w2.2,M5];exact w2.1
      rcases eh hxy with hf|hb
      . rcases ReflTransGen.cases_tail hf with h|h
        . exact h.symm
        . obtain⟨c,_,hc⟩:=h;exact absurd (f2 c y hc) hy
      . rcases ReflTransGen.cases_tail hb with h|h
        . exact h
        . obtain⟨c,_,hc⟩:=h;exact absurd (f2 c x hc) hx
     have hq1:qE (c5 n) p ((g8 (c5 n)).symm (q7 n (e j1)))≠none:=(by unfold qE;rw[cb w];have hs:=(m9 n p _).mp (get_mem L ⟨(j1.val+L.length-1) %L.length,M1 _ q⟩);intro h;rw[h] at hs;simp at hs);have hq2:qE (c5 n) p ((g8 (c5 n)).symm (q7 n (e j2)))≠none:=(by unfold qE;rw[cb w];have hs:=(m9 n p _).mp (get_mem L ⟨(j2.val+L.length-1) %L.length,M1 _ q⟩);intro h;rw[h] at hs;simp at hs);have r2:=a4 _ _ hg hq1 hq2;have r8:e j1=e j2:=(dj n).injective r2;have m2:(⟨(j1.val+L.length-1) %L.length,M1 _ q⟩:Fin L.length)=⟨(j2.val+L.length-1) %L.length,M1 _ q⟩:=(List.nodup_iff_injective_get.mp (gp n p)) r8;have hv:=Q6 Fin.val m2;dsimp only at hv;apply L6;have h1:(j1.val+L.length-1+1) %L.length=j1.val:=by rw[show j1.val+L.length-1+1=j1.val+L.length by omega,M2,L8 (by omega)]
     have h2:(j2.val+L.length-1+1) %L.length=j2.val:=by rw[show j2.val+L.length-1+1=j2.val+L.length by omega,M2,L8 (by omega)]
     rw[<-h1,<-h2,add_mod,hv,<-add_mod]
    have h9:univ.image (fun j:Fin k=>j7 n (e j).val (g j) w)⊆f6 (c5 n) p:=(by intro c hc;obtain⟨j,_,rfl⟩:=X5.mp hc;exact k1 j);have hr:∑ c∈univ.image (fun j:Fin k=>j7 n (e j).val (g j) w),c.card=∑ c∈f6 (c5 n) p,c.card:=by rw[fi,Finset.sum_image (fun a _ b _ h=>b9 h)];have:∀ j:Fin k,(j7 n (e j).val (g j) w).card=c3 (t j):=fun j=>(by rw[(be w (f j).1 (f j).2).1,z]);simp_rw[this];exact y2
    have h7:f6 (c5 n) p=univ.image (fun j:Fin k=>j7 n (e j).val (g j) w):=by
     by_contra hne;have r3:univ.image (fun j:Fin k=>j7 n (e j).val (g j) w) ⊂ f6 (c5 n) p:=Finset.ssubset_iff_subset_ne.mpr ⟨h9,fun h=>hne h.symm⟩;obtain⟨c0,b5,k2⟩:=Finset.exists_of_ssubset r3;have ht:0<c0.card:=by have:=(w9 (c5 n) p c0 b5).1;rwa[bj] at this
     have w1:∑ c∈univ.image (fun j:Fin k=>j7 n (e j).val (g j) w),c.card<∑ c∈f6 (c5 n) p,c.card:=by
      calc ∑ c∈univ.image (fun j:Fin k=>j7 n (e j).val (g j) w),c.card
       < c0.card+∑ c∈univ.image (fun j:Fin k=>j7 n (e j).val (g j) w),c.card:=by omega
       _=∑ c∈insert c0 (univ.image (fun j:Fin k=>j7 n (e j).val (g j) w)),c.card:=(sum_insert k2).symm
       _<=∑ c∈f6 (c5 n) p,c.card:=Finset.sum_le_sum_of_subset (Finset.insert_subset b5 h9)
     omega
    intro c hc;rw[h7,X5] at hc;obtain⟨j,_,rfl⟩:=hc;exact⟨j,rfl,fun j' hj'=>b9 hj'.symm⟩
   have he:∀ l r,j6 (c5 n) p l r=o6 t l r true/\m8 (c5 n) p l r=o6 t l r false:=by
    intro l r
    have a0:∀ g1:Y0,((f6 (c5 n) p).filter (fun c=>p9 c=l/\n5 c=r/\m4 (c5 n) p c=if g1 then 1 else -1)).card=o6 t l r g1:=fun g1=>by
     unfold o6;symm;refine card_bij (fun(j:Fin k) _=>j7 n (e j).val (g j) w) ?_ ?_ ?_
     . intro j hj;simp only[L4,Y2,Q0] at hj ⊢;have hp:=be (j4:=(e j).val) (len:=g j) w (f j).1 (f j).2;refine⟨by rw[<-(s j).1];exact mem_image_of_mem _ (Y2 _),by rw[hp.2.1,<-z j];exact hj.1,by rw[hp.2.2,<-b4 j];exact hj.2.1,by rw[(s j).2,hj.2.2]⟩
     . intro j1 _ j2 _ v1;have d2:j7 n (e j1).val (g j1) w∈f6 (c5 n) p:=(by rw[<-(s j1).1];exact mem_image_of_mem _ (Y2 _));obtain⟨j0,_,g2⟩:=x0 _ d2;exact (g2 j1 rfl).trans (g2 j2 v1).symm
     . intro c hc;simp only[L4] at hc;obtain⟨j,rfl,_⟩:=x0 c hc.1;have hp:=be (j4:=(e j).val) (len:=g j) w (f j).1 (f j).2;refine⟨j,?_,rfl⟩;simp only[L4,Y2,Q0];refine⟨by rw[z j,<-hp.2.1];exact hc.2.1,by rw[b4 j,<-hp.2.2];exact hc.2.2.1,?_⟩;have hs:=hc.2.2.2;rw[(s j).2] at hs;cases hts:c9 (t j)<;>cases g1<;>simp[hts] at hs ⊢
    exact⟨by simpa[j6] using a0 true,by simpa[m8] using a0 false⟩
   refine⟨by omega,by rw[x1];exact (o ⟨0,by omega⟩).isLt,p2,fun j hj=>by
     have:=b8 ⟨j.val,hj⟩
     rw[this];exact o0 _,
    fun j hj=>by
     dsimp only[e5]
     rw[Q8 y1,Q3 (by dsimp only;omega),Q3 (by dsimp only;omega),Q8 (by change ¬ 2*n-1-(2*n-1-j.val)<L.length;omega)],
    t,b8,b7,?_,?_,y2,?_,?_⟩
   . intro j;rw[a5,k0 j.val (le_of_lt j.isLt),L7 j.isLt];exact (n1 _ _ (f j).1 (f j).2).2.2.2
   . rw[a5,k0 k Y3,Q8 (lt_irrefl k)]
   . have p0:=oc (k:=k) (fun j=>(p (d8 n (o j))).getD false)
     convert p0 using 3
     ext j;simp only[L4,Y2,Q0,b3 j,M7];have:e j=o ⟨(j.val+k-1) %k,M1 _ (by omega)⟩:=(by dsimp only[e,o];congr 1;apply L6;simp[ho]);rw[this]
   . intro l _ r _;rw[bp];unfold f8;simp only[he]
lemma w5 {n c:ℕ} (hn:1<=n) (f2:ℕ->ℕ->ℤ)
 (w:Fin (2*n+2)->Fin (6*n+1)) (hv:w8 n c f2 w):
 let p:=s5 n w
 e5 n p=w ∧
 e3 p=2*n-c ∧
 ∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,e9 (c5 n) p l r=f2 l r:=by
 intro p;unfold w8 at hv;by_cases h0:c=0
 . rw[L7 h0] at hv;obtain⟨hw,hc⟩:=hv;have hp:p=fun _=>none:=(by dsimp only[p];rw[hw];unfold s5 m3;simp only[↓reduceIte,lt_irrefl,↓reduceDIte]);have m1:e3 p=2*n:=(by rw[hp];unfold e3;simp);have hcw:e5 n p=w:=by have hL:(f4 n p).length=0:=(by have:=bo n p;omega);rw[hw];unfold e5;simp[hL]
   refine⟨hcw,by omega,fun l hl r hr=>?_⟩;rw[bp];have y:=ip hn p (fun v=>by rw[hp]);unfold f8;simp only[y];exact hc l hl r hr
 . rw[Q8 h0] at hv;obtain⟨hkle,p1,hb0lt,hpos,r2,t,d1,hs0_l0,q2,hq,b3,hu,hc⟩:=hv;have g:0<c:=K2 h0;set s0:Fin (2*n):=⟨(w ⟨2*n+1,by omega⟩).val,p1⟩;set b0:Y0:=decide ((w ⟨2*n,by omega⟩).val=1);let d:ℕ->ℕ:=fun m=>s0.val+∑ j∈univ.filter (fun j:Fin c=>0<j.val/\j.val<=m),c3 (t j);let z:ℕ->Y0:=fun m=>xor b0 (decide ((univ.filter (fun j:Fin c=>0<j.val/\j.val<=m/\c9 (t j)=false)).card %2=1));have h5:∀ j (hj:j+1<c),d (j+1)=d j+c3 (t ⟨j+1,hj⟩):=by intro j hj;dsimp only[d];have h9:univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j+1)=insert ⟨j+1,hj⟩ (univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j)):=(by ext i;simp only[L4,Y2,Q0,X3,K4];omega);have g2:(⟨j+1,hj⟩:Fin c)∉univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j):=(by simp);rw[h9,sum_insert g2];omega
   have k:∀ m<c,d m<2*n:=by
    intro m hm;dsimp only[d]
    have hy:univ.filter (fun j:Fin c=>0<j.val/\j.val<=m)⊆
     univ.erase ⟨0,g⟩:=by
     intro j hj;simp only[L4,Y2,Q0] at hj;exact mem_erase.mpr ⟨fun h=>by have:=Q6 Fin.val h;dsimp at this;omega,Y2 _⟩
    have hsum_le:(∑ j∈univ.filter (fun j:Fin c=>0<j.val/\j.val<=m),c3 (t j))<=2*n-c3 (t ⟨0,g⟩):=(by have y:=Finset.sum_le_sum_of_subset (f:=fun j=>c3 (t j)) hy;have h2:=add_sum_erase univ (fun j=>c3 (t j)) (Y2 (⟨0,g⟩:Fin c));rw[b3] at h2;omega);dsimp only[s0];omega
   have q:∀ a b,a<b->b<c->d a<d b:=by
    intro a b hk hb
    induction b with
    | zero=>omega
    | succ b ih=>
     rw[h5 b hb];have hl1:=(k7 (t ⟨b+1,hb⟩)).1;by_cases he:a=b
     . subst he;omega
     . have:=ih (by omega) (by omega);omega
   have a5:∀ j (hj:j+1<c),z (j+1)=if c9 (t ⟨j+1,hj⟩) then z j else !z j:=by
    intro j hj;dsimp only[z]
    have h9:univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j+1/\c9 (t i)=false)=if c9 (t ⟨j+1,hj⟩)=false then insert ⟨j+1,hj⟩ (univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j/\c9 (t i)=false))
     else univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j/\c9 (t i)=false):=by
     ext i;split_ifs with hs<;>simp only[L4,Y2,Q0,X3,K4]
     . constructor
       . rintro⟨y,h2,h3⟩;by_cases hi:i.val=j+1
         . exact inl hi
         . exact inr ⟨y,by omega,h3⟩
       . rintro (hi|⟨y,h2,h3⟩)
         . have:i=⟨j+1,hj⟩:=L6 hi;subst this;exact⟨by omega,Y3,hs⟩
         . exact⟨y,by omega,h3⟩
     . constructor
       . rintro⟨y,h2,h3⟩;refine⟨y,?_,h3⟩;by_contra hgt;have:i=⟨j+1,hj⟩:=L6 (by dsimp only;omega);subst this;exact hs h3
       . rintro⟨y,h2,h3⟩;exact⟨y,by omega,h3⟩
    rw[h9];cases hs:c9 (t ⟨j+1,hj⟩)
    . simp only[↓reduceIte,J5];have g2:(⟨j+1,hj⟩:Fin c)∉univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j/\c9 (t i)=false):=(by simp);rw[W9 g2];have hd:((univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j/\c9 (t i)=false)).card+1) %2=1↔¬ (univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j/\c9 (t i)=false)).card %2=1:=(by omega);by_cases hz:(univ.filter (fun i:Fin c=>0 < i.val/\i.val<=j/\c9 (t i)=false)).card %2=1<;>cases b0<;>simp[hz,hd]
    . simp
   have x2:d 0=s0.val:=by dsimp only[d];rw[L9 (fun j hj=>by simp only[L4,Y2,Q0] at hj;omega)];omega
   have a7:z 0=b0:=by
    dsimp only[z];have he:univ.filter (fun j:Fin c=>0<j.val/\j.val<=0/\c9 (t j)=false)=∅:=(by ext j;simp only[L4,Y2,Q0,notMem_empty,iff_false];intro h;omega);rw[he];cases b0<;>simp
   have f1:∀ m (hm:m<c),let st:=g5 n w s0 b0 m
    st.1.val=d m/\st.2.1=z m ∧
    ∀ v,st.2.2 v=if h:∃ i:Fin c,i.val≤m/\d8 n ⟨d i.val,k i.val i.isLt⟩=v
     then some (z (Classical.choose h).val) else none:=by
    intro m
    induction m with
    | zero=>
     intro hm;refine⟨x2.symm,a7.symm,fun v=>?_⟩;dsimp only[g5];by_cases hv:v=d8 n s0
     . subst hv;have s:∃ i:Fin c,i.val≤0/\d8 n ⟨d i.val,k i.val i.isLt⟩=d8 n s0:=⟨⟨0,g⟩,Y3,by congr 1;exact L6 x2⟩;rw[Q2 rfl,L7 s];have e1:(Classical.choose s).val=0:=(by have:=(choose_spec s).1;omega);rw[e1,a7]
     . have hnex:¬ ∃ i:Fin c,i.val≤0/\d8 n ⟨d i.val,k i.val i.isLt⟩=v:=by rintro⟨i,hi,v2⟩;have hi0:i.val=0:=(by omega);apply hv;rw[<-v2];congr 1;apply L6;dsimp only;rw[hi0,x2]
       rw[Q3 hv,Q8 hnex]
    | succ m ih=>
     intro hm;obtain⟨hpm,hbm,hmap⟩:=ih (by omega);have hg:m+1<2*n:=(by omega);have r3:=d1 ⟨m+1,hm⟩;have y1:0<(w ⟨2*n-1-(m+1),by omega⟩).val:=(by rw[r3];exact o0 _);have r7:l3 (w ⟨2*n-1-(m+1),by omega⟩) y1=t ⟨m+1,hm⟩:=(bd y1 (o0 _) r3).trans (z2 _);dsimp only[g5];rw[L7 hg,L7 y1];have hm':((g5 n w s0 b0 m).1.val+c3 (l3 (w ⟨2*n-1-(m+1),by omega⟩) y1)) %(2*n)=d (m+1):=(by rw[hpm,r7,<-h5 m hm,L8 (k (m+1) hm)]);have hb':(if c9 (l3 (w ⟨2*n-1-(m+1),by omega⟩) y1) then (g5 n w s0 b0 m).2.1 else !(g5 n w s0 b0 m).2.1)=z (m+1):=(by rw[hbm,r7,a5 m hm]);refine⟨hm',hb',fun v=>?_⟩;dsimp only;have hfin':(⟨((g5 n w s0 b0 m).1.val+c3 (l3 (w ⟨2*n-1-(m+1),by omega⟩) y1)) %(2*n),M1 _ (by omega)⟩:Fin (2*n))=⟨d (m+1),k (m+1) hm⟩:=L6 hm';rw[hfin',hb'];by_cases hv:v=d8 n ⟨d (m+1),k (m+1) hm⟩
     . subst hv;have s:∃ i:Fin c,i.val≤m+1/\d8 n ⟨d i.val,k i.val i.isLt⟩=d8 n ⟨d (m+1),k (m+1) hm⟩:=⟨⟨m+1,hm⟩,Y3,rfl⟩;rw[Q2 rfl,L7 s];have e1:(Classical.choose s).val=m+1:=by have s1:=choose_spec s;have b1:=Q6 Fin.val ((e8 n).injective s1.2);dsimp only at b1;by_contra hne;have:=q (Classical.choose s).val (m+1) (by omega) hm;omega
       rw[e1]
     . rw[Q3 hv,hmap v];by_cases y2:∃ i:Fin c,i.val≤m/\d8 n ⟨d i.val,k i.val i.isLt⟩=v
       . have b8:∃ i:Fin c,i.val≤m+1/\d8 n ⟨d i.val,k i.val i.isLt⟩=v:=by obtain⟨i,hi,v2⟩:=y2;exact⟨i,by omega,v2⟩
         rw[L7 y2,L7 b8];congr 1;congr 1;have y:=(choose_spec y2).2;have h2:=(choose_spec b8).2;have b1:=Q6 Fin.val ((e8 n).injective (y.trans h2.symm));dsimp only at b1
         rcases lt_trichotomy (Classical.choose y2).val (Classical.choose b8).val with a4|v2|hgt
         . exact absurd b1 (ne_of_lt (q _ _ a4 (Classical.choose b8).isLt))
         . exact v2
         . exact absurd b1 (ne_of_gt (q _ _ hgt (Classical.choose y2).isLt))
       . have w2:¬ ∃ i:Fin c,i.val≤m+1/\d8 n ⟨d i.val,k i.val i.isLt⟩=v:=by
          rintro⟨i,hi,v2⟩;by_cases him:i.val=m+1
          . apply hv;rw[<-v2];congr 1;exact L6 (by dsimp only;rw[him])
          . exact y2 ⟨i,by omega,v2⟩
         rw[Q8 y2,Q8 w2]
   have m2:p=(g5 n w s0 b0 (c-1)).2.2:=by dsimp only[p,s5];rw[L7 p1];exact Q6 (fun x=>x.2.2) (ez n w s0 b0 (c-1) (fun i hi1 hi2=>r2 ⟨i,hi2⟩ (by dsimp only;omega)) (2*n-1) (by omega))
   obtain⟨_,_,b2⟩:=f1 (c-1) (by omega)
   have d0:f4 n p=ofFn (fun i:Fin c=>(⟨d i.val,k i.val i.isLt⟩:Fin (2*n))):=by
    have k1:∀ {l1 l2:List (Fin (2*n))},l1.Perm l2->l1.Pairwise (·<·)->l2.Pairwise (·<·)->l1=l2:=by
     intro l1
     induction l1 with
     | nil=>intro l2 hp _ _;exact hp.nil_eq
     | cons a as ih=>
      intro l2 hp y h2
      cases l2 with
      | nil=>exact (hp.symm.nil_eq).symm
      | cons b bs=>
       have w1:a∈b :: bs:=hp.subset mem_cons_self;have t1:b∈a :: as:=hp.symm.subset mem_cons_self
       have hk:a=b:=by
        rcases mem_cons.mp w1 with rfl|ha'
        . rfl
        . rcases mem_cons.mp t1 with rfl|hb'
          . rfl
          . exfalso;have hx:=(List.pairwise_cons.mp y).1 b hb';have ht:=(List.pairwise_cons.mp h2).1 a ha';exact lt_asymm hx ht
       subst hk;exact Q6 (List.cons a) (ih ((List.perm_cons a).mp hp) (List.pairwise_cons.mp y).2 (List.pairwise_cons.mp h2).2)
    refine k1 ?_ (t8 n p) ?_
    . refine (List.perm_ext_iff_of_nodup (gp n p) ?_).mpr ?_
      . rw[List.nodup_ofFn];intro i1 i2 v2;have hv:=Q6 Fin.val v2;dsimp only at hv;apply L6
        rcases lt_trichotomy i1.val i2.val with a4|h|hgt
        . exact absurd hv (ne_of_lt (q _ _ a4 i2.isLt))
        . exact h
        . exact absurd hv (ne_of_gt (q _ _ hgt i1.isLt))
      . intro m;rw[m9,m2,b2,mem_ofFn];constructor
        . intro hs;by_cases s:∃ i:Fin c,i.val≤c-1/\d8 n ⟨d i.val,k i.val i.isLt⟩=d8 n m
          . obtain⟨i,_,hi⟩:=s;exact⟨i,(e8 n).injective hi⟩
          . rw[Q8 s] at hs;simp at hs
        . rintro⟨i,rfl⟩;have s:∃ j:Fin c,j.val≤c-1/\d8 n ⟨d j.val,k j.val j.isLt⟩=d8 n ⟨d i.val,k i.val i.isLt⟩:=⟨i,by omega,rfl⟩;rw[L7 s];rfl
    . rw[List.pairwise_iff_getElem];intro i j hi hj hij;simp only[getElem_ofFn];exact q i j hij (by simpa using hj)
   have a0:∀ i:Fin c,p (d8 n ⟨d i.val,k i.val i.isLt⟩)=some (z i.val):=fun i=>by
    rw[m2,b2];have s:∃ j:Fin c,j.val≤c-1/\d8 n ⟨d j.val,k j.val j.isLt⟩=d8 n ⟨d i.val,k i.val i.isLt⟩:=⟨i,by omega,rfl⟩;rw[L7 s]
    have e1:(Classical.choose s).val=i.val:=by
     have hv:=Q6 Fin.val ((e8 n).injective (choose_spec s).2);dsimp only at hv
     rcases lt_trichotomy (Classical.choose s).val i.val with a4|h|hgt
     . exact absurd hv (ne_of_lt (q _ _ a4 i.isLt))
     . exact h
     . exact absurd hv (ne_of_gt (q _ _ hgt (Classical.choose s).isLt))
    rw[e1]
   have g0:e5 n p=w:=by
    funext j
    dsimp only[e5];have h8:(f4 n p).length=c:=(by rw[d0,U7]);have hL0:(f4 n p).length≠0:=(by omega);rw[Q8 hL0];have x0:∀ i:Fin (f4 n p).length,(f4 n p).get i=⟨d i.val,k i.val (by omega)⟩:=fun i=>(by simp[d0]);by_cases r4:j.val=2*n+1
    . rw[Q2 r4];apply L6;dsimp only;have k0:j=⟨2*n+1,by omega⟩:=L6 r4;rw[k0,x0 ⟨0,by omega⟩];exact x2
    . rw[Q3 r4];by_cases r8:j.val=2*n
      . rw[Q2 r8];apply L6;dsimp only;have k0:j=⟨2*n,by omega⟩:=L6 r8;rw[k0,x0 ⟨0,by omega⟩];have hh:=a0 ⟨0,g⟩;dsimp only at hh;rw[hh,a7];dsimp only[Option.getD,b0];have:(w ⟨2*n,by omega⟩).val=0\/(w ⟨2*n,by omega⟩).val=1:=by omega
        rcases this with h|h<;>simp[h]
      . rw[Q3 r8]
        set o:=2*n-1-j.val with hidx_def
        have p0:j=⟨2*n-1-o,by omega⟩:=L6 (by dsimp only;omega);by_cases r6:o<(f4 n p).length
        . rw[L7 r6]
          conv_rhs=>rw[p0,d1 ⟨o,by omega⟩]
          have b7:d (c-1)=s0.val+(2*n-c3 (t ⟨0,g⟩)):=by dsimp only[d];have h9:univ.filter (fun i:Fin c=>0 < i.val/\i.val<=c-1)=univ.erase ⟨0,g⟩:=(by ext i;simp only[L4,Y2,Q0,and_true,mem_erase,ne_eq,K4];have:=i.isLt;omega);rw[h9];have h2:=add_sum_erase univ (fun i=>c3 (t i)) (Y2 (⟨0,g⟩:Fin c));rw[b3] at h2;omega
          set e:=(o+(f4 n p).length-1) %(f4 n p).length;have e2:e<c:=by dsimp only[e];rw[h8];exact M1 _ g
          have d2:decide (d e %2=1)=d5 (decide ((2*n+s0.val-c3 (t ⟨0,g⟩)) %2=1)) t o:=by
           have e0:∀ m (hm:m<c),d5 (decide ((2*n+s0.val-c3 (t ⟨0,g⟩)) %2=1)) t (m+1)=decide (d m %2=1):=by
            intro m
            induction m with
            | zero=>intro hm;rw[d5,L7 g,d5,db,x2];have a4:=(k7 (t ⟨0,g⟩)).2;have hp:s0.val %2=1↔((2*n+s0.val-c3 (t ⟨0,g⟩)) %2=1↔¬ c3 (t ⟨0,g⟩) %2=1):=(by omega);by_cases y:(2*n+s0.val-c3 (t ⟨0,g⟩)) %2=1<;>by_cases h2:c3 (t ⟨0,g⟩) %2=1<;>simp[y,h2,hp]
            | succ m ih=>intro hm;rw[d5,L7 hm,ih (by omega),db,h5 m hm];have hp:(d m+c3 (t ⟨m+1,hm⟩)) %2=1↔(d m %2=1↔¬ c3 (t ⟨m+1,hm⟩) %2=1):=(by omega);by_cases y:d m %2=1<;>by_cases h2:c3 (t ⟨m+1,hm⟩) %2=1<;>simp[y,h2,hp]
           by_cases u:o=0
           . rw[u,d5];have x1:e=c-1:=by dsimp only[e];rw[u,h8,zero_add,L8 (by omega)]
             rw[x1,b7];have a4:=(k7 (t ⟨0,g⟩)).2;have v2:s0.val+(2*n-c3 (t ⟨0,g⟩))=2*n+s0.val-c3 (t ⟨0,g⟩):=(by omega);rw[v2]
           . have x1:e=o-1:=by dsimp only[e];rw[h8,show o+c-1=(o-1)+c by omega,M2,L8 (by omega)]
             rw[x1];conv_rhs=>rw[show o=(o-1)+1 by omega,e0 (o-1) (by omega)]
          have b6:(if d e<d o then d o-d e
           else 2*n-d e+d o)=c3 (t ⟨o,by omega⟩):=by
           by_cases u:o=0
           . have x1:e=c-1:=by dsimp only[e];rw[u,h8,zero_add,L8 (by omega)]
             have c0:(⟨o,by omega⟩:Fin c)=⟨0,g⟩:=L6 u;rw[x1,c0,u,b7,x2];have a4:=(k7 (t ⟨0,g⟩)).2;rw[Q3 (by omega)];omega
           . have x1:e=o-1:=by dsimp only[e];rw[h8,show o+c-1=(o-1)+c by omega,M2,L8 (by omega)]
             rw[x1,Q2 (q (o-1) o (by omega) (by omega))];have hs:=h5 (o-1) (by omega);have a2:(⟨o-1+1,by omega⟩:Fin c)=⟨o,by omega⟩:=L6 (by dsimp only;omega);rw[a2,show o-1+1=o by omega] at hs;omega
          have p2:decide ((p (d8 n ⟨d e,k e e2⟩)).getD false=(p (d8 n ⟨d o,k o (by omega)⟩)).getD false)=c9 (t ⟨o,by omega⟩):=by
           have y:=a0 ⟨e,e2⟩;have h2:=a0 ⟨o,by omega⟩;dsimp only at y h2;simp only[y,h2,Option.getD_some];by_cases u:o=0
           . have x1:e=c-1:=by dsimp only[e];rw[u,h8,zero_add,L8 (by omega)]
             have c0:(⟨o,by omega⟩:Fin c)=⟨0,g⟩:=L6 u;simp only[x1,c0,u,a7];dsimp only[z];have h9:univ.filter (fun i:Fin c=>0 < i.val/\i.val<=c-1/\c9 (t i)=false)=(univ.filter (fun i:Fin c=>c9 (t i)=false)).erase ⟨0,g⟩:=by ext i;simp only[L4,Y2,Q0,and_true,mem_erase,ne_eq,K4];have:=i.isLt;exact⟨fun⟨y,_,h3⟩=>⟨by omega,h3⟩,fun⟨y,h3⟩=>⟨by omega,by omega,h3⟩⟩
             have b5:((univ.filter (fun i:Fin c=>c9 (t i)=false)).erase ⟨0,g⟩).card %2=if c9 (t ⟨0,g⟩)=false then 1 else 0:=by
              by_cases c2:c9 (t ⟨0,g⟩)=false
              . have k2:(⟨0,g⟩:Fin c)∈univ.filter (fun i:Fin c=>c9 (t i)=false):=L4.mpr ⟨Y2 _,c2⟩;rw[Q2 c2,Finset.card_erase_of_mem k2];have hpos_c:0<(univ.filter (fun i:Fin c=>c9 (t i)=false)).card:=Finset.card_pos.mpr ⟨⟨0,g⟩,k2⟩;omega
              . rw[Q3 c2,Finset.erase_eq_of_notMem (by simp[c2])];exact hu
             simp only[h9,b5];cases c9 (t ⟨0,g⟩)<;>cases b0<;>decide
           . have x1:e=o-1:=by dsimp only[e];rw[h8,show o+c-1=(o-1)+c by omega,M2,L8 (by omega)]
             rw[x1];have hs:=a5 (o-1) (by omega);have a2:(⟨o-1+1,by omega⟩:Fin c)=⟨o,by omega⟩:=L6 (by dsimp only;omega);rw[a2,show o-1+1=o by omega] at hs;rw[hs];cases c9 (t ⟨o,by omega⟩)<;>cases z (o-1)<;>decide
          congr 1;apply aw
          . rw[(n1 _ _ _ _).1];simp only[x0];exact b6
          . rw[(n1 _ _ _ _).2.1,(gv _ _).mp (q2 ⟨o,by omega⟩)];simp only[x0];rw[b6,d2]
          . rw[(n1 _ _ _ _).2.2.1];simp only[x0];exact p2
        . rw[Q8 r6];apply L6;dsimp only;rw[p0];exact (r2 ⟨o,by omega⟩ (by dsimp only;omega)).symm
   have m1:e3 p=2*n-c:=(by have y:=bo n p;rw[d0,U7] at y;omega);refine⟨g0,m1,?_⟩;have c1:=ir hn p;rw[g0,show 2*n-e3 p=c by omega] at c1;unfold w8 at c1;rw[Q8 h0] at c1;obtain⟨_,_,_,_,_,t',hwt',_,_,_,_,_,hc'⟩:=c1
   have htt':t'=t:=by
    funext j
    exact w4 n ((hwt' j).symm.trans (d1 j))
   intro l hl r hr;rw[<-hc' l hl r hr,htt',hc l hl r hr]
lemma dc {n a:ℕ} (j:1<=n) (hf:a<=2*n)
 (b:ℕ->ℕ->ℤ) (w:Fin (2*n+2)->Fin (6*n+1)):
 w8 n (2*n-a) b w↔∃ p:P0 n,e5 n p=w/\e3 p=a/\∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,e9 (c5 n) p l r=b l r:=by
 constructor
 . intro c;obtain⟨o,d,g⟩:=w5 j b w c;exact⟨s5 n w,o,by omega,g⟩
 . rintro⟨p,rfl,d,g⟩;have c:=ir j p;rw[d] at c;unfold w8 at c ⊢;by_cases i:2*n-a=0
   . rw[L7 i] at c ⊢;exact⟨c.1,fun l e r f=>(c.2 l e r f).trans (g l e r f)⟩
   . rw[Q8 i] at c ⊢;obtain⟨s,y,z,u,x,t,h6,v,h8,q,k,h,m⟩:=c;exact⟨s,y,z,u,x,t,h6,v,h8,q,k,h,fun l e r f=>(m l e r f).trans (g l e r f)⟩
end RingCode
namespace SuffixDP
open S399 StageA RingCode BuildExt
open S393.Compiler.Build
open scoped BigOperators
section SeqMath
noncomputable def f9 {b:Type*}[DecidableEq b](T:V7 b)(S:ℕ)(f:b->ℕ):ℕ:=(univ.filter (fun g:Fin S->{a // a∈T}=>∀ a:{a // a∈T},(univ.filter (fun i:Fin S=>g i=a)).card=f a.1)).card
lemma it {b:Type*}[DecidableEq b](S:ℕ)(f:b->ℕ):f9 (∅:V7 b) S f=if S=0 then 1 else 0:=by
 unfold f9;cases S with
 | zero=>simp only[↓reduceIte];have h:univ.filter (fun g:Fin 0->{a // a∈(∅:V7 b)}=>∀ a:{a // a∈(∅:V7 b)},(univ.filter (fun i:Fin 0=>g i=a)).card=f a.1)={fun i=>elim0 i}:=(by ext g;simp only[L4,Y2,Q0,U5];exact⟨fun _=>funext fun i=>elim0 i,fun _ a=>absurd a.2 (notMem_empty _)⟩);rw[h,Finset.card_singleton]
 | succ S=>simp only[succ_ne_zero,↓reduceIte];rw[U3,W8];intro g _ _;exact notMem_empty _ (g ⟨0,Nat.zero_lt_succ S⟩).2
lemma ib {b:Type*} [DecidableEq b] (T:V7 b) (S:ℕ) (f:b->ℕ)
 (c:∑ a∈T,f a≠S):f9 T S f=0:=by
 unfold f9;rw[U3,W8];intro g _ d;apply c;have e:(∑ a∈T,f a)=∑ a:{a // a∈T},(univ.filter (fun i:Fin S=>g i=a)).card:=(by rw[<-Finset.sum_attach T f];exact L3 rfl fun a _=>(d a).symm);rw[e,<-card_eq_sum_card_fiberwise (f:=g) (s:=univ) (t:=univ) (fun _ _=>Y2 _)];simp
lemma n9 {e:Type*} [DecidableEq e] {S K:ℕ}
 (A:V7 (Fin S)) (b:A.card=K) (f:Fin S->e) (a:e)
 (c:∀ i:Fin S,f i=a->i∈A):
 (univ.filter (fun r:Fin K=>f (A.orderIsoOfFin b r).1=a)).card=(univ.filter (fun i:Fin S=>f i=a)).card:=by
 refine card_bij (fun r _=>(A.orderIsoOfFin b r).1) ?_ ?_ ?_
 . intro r g;simp only[L4,Y2,Q0] at g ⊢;exact g
 . intro r1 _ r2 _ h;exact (A.orderIsoOfFin b).injective (Z9 h)
 . intro i j;have d:f i=a:=(L4.mp j).2;refine⟨(A.orderIsoOfFin b).symm ⟨i,c i d⟩,?_,by simp⟩;simp only[L4,Y2,Q0,OrderIso.apply_symm_apply];exact d
lemma iu {α:Type*} [DecidableEq α] (T1 T2:V7 α) (l:Disjoint T1 T2)
 (S1 S2:ℕ) (f:α->ℕ) (h1:∑ a∈T1,f a=S1) (h2:∑ a∈T2,f a=S2):
 f9 (T1∪T2) (S1+S2) f=choose (S1+S2) S1*f9 T1 S1 f*f9 T2 S2 f:=by
 classical
 let LHS:=univ.filter (fun g:Fin (S1+S2)->{a // a∈T1∪T2}=>∀ a:{a // a∈T1∪T2},(univ.filter (fun i=>g i=a)).card=f a.1);let Aset:=(univ:V7 (Fin (S1+S2))).powersetCard S1;let G1:=univ.filter (fun g:Fin S1->{a // a∈T1}=>∀ a:{a // a∈T1},(univ.filter (fun i=>g i=a)).card=f a.1);let G2:=univ.filter (fun g:Fin S2->{a // a∈T2}=>∀ a:{a // a∈T2},(univ.filter (fun i=>g i=a)).card=f a.1);change LHS.card=choose (S1+S2) S1*G1.card*G2.card;rw[<-show Aset.card=choose (S1+S2) S1 by simp[Aset,Finset.card_powersetCard],mul_assoc,<-card_product,<-card_product];symm
 refine card_bij (fun⟨A,j,k⟩ q=>have e:A.card=S1:=by simp[Aset] at q;exact q.1
  have c:Aᶜ.card=S2:=by have:=V1 A;rw[Q9] at this;omega
  fun b:Fin (S1+S2)=>if d:b∈A then let a:=j ((A.orderIsoOfFin e).symm ⟨b,d⟩);⟨a.1,M6 T2 a.2⟩
   else let a:=k ((Aᶜ.orderIsoOfFin c).symm ⟨b,J7.mpr d⟩);⟨a.1,M0 T1 a.2⟩) ?_ ?_ ?_
 . rintro⟨A,j,k⟩ q;simp only[mem_product,Aset,mem_powersetCard,subset_univ,Q0,G1,G2,L4,Y2] at q;obtain⟨e,h4,z⟩:=q;have c:Aᶜ.card=S2:=(by have:=V1 A;rw[Q9] at this;omega);simp only[LHS,L4,Y2,Q0];intro a
   rcases X4.mp a.2 with h5|ha2
   . rw[<-h4 ⟨a.1,h5⟩]
     have u:=n9 A e (fun b=>(if d:b∈A then (j ((A.orderIsoOfFin e).symm ⟨b,d⟩)).1
       else (k ((Aᶜ.orderIsoOfFin c).symm ⟨b,J7.mpr d⟩)).1)) a.1
      (fun b n=>by
       by_contra h0;rw[Q8 h0] at n
       exact X8.mp l h5 (n▸(k _).2))
     have m:(univ.filter (fun x:Fin (S1+S2)=>(if d:x∈A then (⟨(j ((A.orderIsoOfFin e).symm ⟨x,d⟩)).1,M6 T2 (j _).2⟩:{y // y∈T1∪T2})
       else ⟨(k ((Aᶜ.orderIsoOfFin c).symm ⟨x,J7.mpr d⟩)).1,M0 T1 (k _).2⟩)=a)).card=
      (univ.filter (fun b:Fin (S1+S2)=>(if d:b∈A then (j ((A.orderIsoOfFin e).symm ⟨b,d⟩)).1 else (k ((Aᶜ.orderIsoOfFin c).symm ⟨b,J7.mpr d⟩)).1)=a.1)).card:=by
      congr 1;ext x;simp only[L4,Y2,Q0,J9];split_ifs<;>rfl
     rw[m,<-u];congr 1;ext i;simp only[L4,Y2,Q0,J9];rw[L7 (A.orderIsoOfFin e i).2];simp only[coe_eta,U6]
   . rw[<-z ⟨a.1,ha2⟩]
     have u:=n9 Aᶜ c (fun b=>(if d:b∈A then (j ((A.orderIsoOfFin e).symm ⟨b,d⟩)).1
       else (k ((Aᶜ.orderIsoOfFin c).symm ⟨b,J7.mpr d⟩)).1)) a.1
      (fun b n=>J7.mpr fun d=>by
       rw[L7 d] at n
       exact Finset.disjoint_right.mp l ha2 (n▸(j _).2))
     have m:(univ.filter (fun x:Fin (S1+S2)=>(if d:x∈A then (⟨(j ((A.orderIsoOfFin e).symm ⟨x,d⟩)).1,M6 T2 (j _).2⟩:{y // y∈T1∪T2})
       else ⟨(k ((Aᶜ.orderIsoOfFin c).symm ⟨x,J7.mpr d⟩)).1,M0 T1 (k _).2⟩)=a)).card=
      (univ.filter (fun b:Fin (S1+S2)=>(if d:b∈A then (j ((A.orderIsoOfFin e).symm ⟨b,d⟩)).1 else (k ((Aᶜ.orderIsoOfFin c).symm ⟨b,J7.mpr d⟩)).1)=a.1)).card:=by
      congr 1;ext x;simp only[L4,Y2,Q0,J9];split_ifs<;>rfl
     rw[m,<-u];congr 1;ext i;simp only[L4,Y2,Q0,J9];have h0:(Aᶜ.orderIsoOfFin c i).1∉A:=J7.mp (Aᶜ.orderIsoOfFin c i).2;rw[Q8 h0];simp only[coe_eta,U6]
 . rintro⟨A1,g11,g21⟩ p ⟨A2,g12,g22⟩ v1 h3;simp only[mem_product,Aset,mem_powersetCard,subset_univ,Q0,G1,G2,L4,Y2] at p v1
   have h8:A1=A2:=by
    ext b;have o:=Q6 (fun v=>(v b).1) h3;by_cases h1:b∈A1<;>by_cases h2:b∈A2<;>simp[h1,h2] at o ⊢
    . exact X8.mp l (g11 _).2 (o▸(g22 _).2)
    . exact Finset.disjoint_right.mp l (g21 _).2 (o▸(g12 _).2)
   subst h8;have c:A1ᶜ.card=S2:=by have:=V1 A1;rw[Q9] at this;have:=p.1;omega
   have h4:g11=g12:=funext fun r=>Z9 (by
    have o:=Q6 (fun v=>(v (A1.orderIsoOfFin p.1 r).1).1) h3;dsimp only at o;rw[L7 (A1.orderIsoOfFin p.1 r).2,L7 (A1.orderIsoOfFin p.1 r).2] at o
    simpa only[coe_eta,U6] using o)
   have z:g21=g22:=funext fun r=>Z9 (by
    have hn:(A1ᶜ.orderIsoOfFin c r).1∉A1:=J7.mp (A1ᶜ.orderIsoOfFin c r).2;have o:=Q6 (fun v=>(v (A1ᶜ.orderIsoOfFin c r).1).1) h3;dsimp only at o;rw[Q8 hn,Q8 hn] at o
    simpa only[coe_eta,U6] using o)
   simp[h4,z]
 . intro g hg;set A:=univ.filter (fun i:Fin (S1+S2)=>(g i).1∈T1)
   have e:A.card=S1:=by
    rw[card_eq_sum_card_fiberwise (f:=fun i=>(g i).1) (s:=A) (t:=T1) (fun i w=>(L4.mp w).2)]
    trans (∑ a∈T1,f a)
    . refine L3 rfl fun a ha=>?_;rw[<-(L4.mp hg).2 ⟨a,M6 T2 ha⟩];congr 1;ext i;simp only[A,L4,Y2,Q0,J9];exact⟨fun h=>h.2,fun h=>⟨h▸ha,h⟩⟩
    . exact h1
   have c:Aᶜ.card=S2:=(by have:=V1 A;rw[Q9] at this;omega);let j:Fin S1->{a // a∈T1}:=fun r=>⟨(g (A.orderIsoOfFin e r).1).1,(L4.mp (A.orderIsoOfFin e r).2).2⟩;have h7:∀ r:Fin S2,(g (Aᶜ.orderIsoOfFin c r).1).1∉T1:=fun r=>(by have q:=J7.mp (Aᶜ.orderIsoOfFin c r).2;simp only[A,L4,Y2,Q0] at q;exact q);let k:Fin S2->{a // a∈T2}:=fun r=>⟨(g (Aᶜ.orderIsoOfFin c r).1).1,(X4.mp (g _).2).resolve_left (h7 r)⟩;refine⟨(A,j,k),?_,?_⟩
   . simp only[mem_product,Aset,mem_powersetCard,subset_univ,Q0,G1,G2,L4,Y2];refine⟨e,fun a=>?_,fun a=>?_⟩
     . rw[<-(L4.mp hg).2 ⟨a.1,M6 T2 a.2⟩];have u:=n9 A e (fun i=>(g i).1) a.1 (fun i w=>L4.mpr ⟨Y2 _,w▸a.2⟩)
       trans (univ.filter (fun i:Fin (S1+S2)=>(g i).1=a.1)).card
       . rw[<-u];congr 1;ext r;simp only[j,L4,Y2,Q0,J9]
       . congr 1;ext i;simp only[L4,Y2,Q0,J9]
     . rw[<-(L4.mp hg).2 ⟨a.1,M0 T1 a.2⟩]
       have u:=n9 Aᶜ c (fun i=>(g i).1) a.1
        (fun i w=>J7.mpr (by simp[A,w,Finset.disjoint_right.mp l a.2]))
       trans (univ.filter (fun i:Fin (S1+S2)=>(g i).1=a.1)).card
       . rw[<-u];congr 1;ext r;simp only[k,L4,Y2,Q0,J9]
       . congr 1;ext i;simp only[L4,Y2,Q0,J9]
   . funext b;apply Z9;dsimp only
     by_cases d:b∈A<;>simp[d,j,k]
lemma fd {b:Type*}[DecidableEq b](a:b)(S:ℕ)(f:b->ℕ):f9 {a} S f=if f a=S then 1 else 0:=by
 unfold f9;by_cases h:f a=S
 . rw[Q2 h]
   have d:univ.filter (fun g:Fin S->{x // x∈({a}:V7 b)}=>∀ x:{x // x∈({a}:V7 b)},(univ.filter (fun i:Fin S=>g i=x)).card=f x.1)=
    {fun _=>⟨a,Finset.mem_singleton_self a⟩}:=by
    ext g;simp only[L4,Y2,Q0,U5];exact⟨fun _=>funext fun i=>Z9 (U5.mp (g i).2),fun c x=>by have e:x=⟨a,Finset.mem_singleton_self a⟩:=Z9 (U5.mp x.2);rw[c,e,h];simp⟩
   rw[d,Finset.card_singleton]
 . rw[Q3 h];exact ib {a} S f (by simpa using h)
lemma cp {d:Type*} [DecidableEq d] (T:V7 d) (a b:d)
 (i:a∉T) (j:b∉T) (g:a≠b) (S:ℕ) (f:d->ℕ) (c:∑ x∈T,f x=S):
 f9 (T∪{a,b}) (S+f a+f b) f=f9 T S f*(choose (S+f a) (f a)*choose (S+f a+f b) (f b)):=by
 have k:T∪{a,b}=(T∪{a})∪{b}:=(by ext x;simp[or_assoc]);have h:Disjoint (T∪{a}) {b}:=(by simp[j,g.symm]);have e:Disjoint T {a}:=(by simp[i]);rw[k,iu (T∪{a}) {b} h (S+f a) (f b) f (by rw[X7 e,sum_singleton,c]) (by simp),iu T {a} e S (f a) f c (by simp),fd,fd];simp only[↓reduceIte,mul_one];rw[<-choose_symm (by omega:S<=S+f a),show S+f a-S=f a by omega,<-choose_symm (by omega:S+f a<=S+f a+f b),show S+f a+f b-(S+f a)=f b by omega];ring
noncomputable def z5 {a:Type*}[DecidableEq a](R:ℕ)(S:V7 a)(f:a->ℕ):ℕ:=choose R (∑ x∈S,f x)*f9 S (∑ x∈S,f x) f
lemma kp {a:Type*}[DecidableEq a](R:ℕ)(f:a->ℕ):z5 R (∅:V7 a) f=1:=by simp[z5,it]
lemma bq {b:Type*} [DecidableEq b] (R:ℕ) (S:V7 b) (f:b->ℕ)
 (a:∑ x∈S,f x=R):z5 R S f=f9 S R f:=by simp[z5,a]
lemma fm {c:Type*} [DecidableEq c] (R:ℕ) (S:V7 c) (a b:c)
 (i:a∉S) (j:b∉S) (g:a≠b) (f:c->ℕ) (l:(∑ x∈S,f x)+f a+f b<=R):
 z5 R (S∪{a,b}) f=z5 R S f*(choose (R-∑ x∈S,f x) (f a)*choose (R-∑ x∈S,f x-f a) (f b)):=by
 set K:=∑ x∈S,f x;have h:∑ x∈S∪{a,b},f x=K+f a+f b:=by rw[X7 (by simp[i,j]),V6 g];omega
 unfold z5;rw[h,cp S a b i j g K f rfl];have d:=Nat.choose_mul (n:=R) (k:=K+f a) (s:=K) (by omega);rw[<-choose_symm (by omega:K<=K+f a),show K+f a-K=f a by omega] at d;have e:=Nat.choose_mul (n:=R) (k:=K+f a+f b) (s:=K+f a) (by omega);rw[<-choose_symm (by omega:K+f a<=K+f a+f b),show K+f a+f b-(K+f a)=f b by omega,show R-(K+f a)=R-K-f a by omega] at e;change choose R (K+f a+f b)*(f9 S K f*(choose (K+f a) (f a)*choose (K+f a+f b) (f b)))=choose R K*f9 S K f*(choose (R-K) (f a)*choose (R-K-f a) (f b))
 calc choose R (K+f a+f b)*(f9 S K f*(choose (K+f a) (f a)*choose (K+f a+f b) (f b)))
  =(choose R (K+f a+f b)*choose (K+f a+f b) (f b))*(choose (K+f a) (f a)*f9 S K f):=by ring
  _=(choose R (K+f a)*choose (R-K-f a) (f b))*(choose (K+f a) (f a)*f9 S K f):=by rw[e]
  _=(choose R (K+f a)*choose (K+f a) (f a))*(choose (R-K-f a) (f b)*f9 S K f):=by ring
  _=(choose R K*choose (R-K) (f a))*(choose (R-K-f a) (f b)*f9 S K f):=by rw[d]
  _=choose R K*f9 S K f*(choose (R-K) (f a)*choose (R-K-f a) (f b)):=by ring
end SeqMath
section WalkAndBridge
def e4 {n:ℕ}(q:Fin n)(s:Y0):c7 n:=(⟨0,by decide⟩,q,s)
def f5 {n:ℕ}(q:Fin n)(s:Y0):c7 n:=(⟨1,by decide⟩,q,s)
def f3 {n:ℕ}(q:Fin n)(s:Y0):c7 n:=(⟨2,by decide⟩,q,s)
def d3 (n:ℕ):V7 (c7 n):=univ.filter (fun t:c7 n=>t.1.val=0)
def g7 (n:ℕ):V7 (c7 n):=univ.filter (fun t:c7 n=>t.1.val=1)
def br (n:ℕ):V7 (c7 n):=univ.filter (fun t:c7 n=>t.1.val=2)
def n2 (c b:Y0)(a:ℕ):V9 ℕ:=match c,b with
 | false,false=>some a
 | false,true=>if 1<=a then some (a-1) else none
 | true,false=>some (a+1)
 | true,true=>some a
lemma gw (k:ℕ):(univ.filter (fun r:Fin k=>r.val %2=0)).card=(k+1)/2/\(univ.filter (fun r:Fin k=>r.val %2=1)).card=k/2:=by
 induction k with
 | zero=>simp
 | succ k ih=>
  have a:∀ b:ℕ,(univ.filter (fun r:Fin (k+1)=>r.val %2=b)).card=(univ.filter (fun r:Fin k=>r.val %2=b)).card+if k %2=b then 1 else 0:=fun b=>by
   have c:(univ:V7 (Fin (k+1)))=insert (last k) (univ.image castSucc):=(by ext x;simp only[Y2,X3,X5,Q0,true_iff];exact lastCases (inl rfl) (fun i=>inr ⟨i,rfl⟩) x);rw[c,Finset.filter_insert];have f:last k∉(univ.image castSucc).filter (fun r:Fin (k+1)=>r.val %2=b):=(by simp[K4]);have e:((univ.image castSucc).filter (fun r:Fin (k+1)=>r.val %2=b)).card=(univ.filter (fun r:Fin k=>r.val %2=b)).card:=(by rw[filter_image,card_image_of_injective _ (Fin.castSucc_injective k)];rfl);by_cases d:k %2=b
   . rw[Q2 (show (last k).val %2=b from d),Q2 d,W9 f,e]
   . rw[Q3 (show ¬ (last k).val %2=b from d),Q3 d,e,add_zero]
  rw[a 0,a 1,ih.1,ih.2];split_ifs<;>omega
lemma ch {n k:ℕ}(c:Y0)(a:Fin k->c7 n)(m:ℕ)(p:m<=k):d5 c a m=xor c (decide ((univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2)).card %2=1)):=by
 induction m with
 | zero=>simp[d5]
 | succ m ih=>
  rw[d5,L7 (by omega),ih (by omega)]
  have e:univ.filter (fun j:Fin k=>j.val<m+1/\(a j).1.val≠2)=if(a ⟨m,by omega⟩).1.val≠2 then insert ⟨m,by omega⟩ (univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2))
   else univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2):=by
   ext j;split_ifs with g<;>simp only[L4,Y2,Q0,X3,K4]
   . exact⟨fun⟨h1,b⟩=>if i:j.val=m then inl i else inr ⟨by omega,b⟩,fun h=>h.elim (fun i=>by have d:j=⟨m,by omega⟩:=L6 i;rw[d];exact⟨by omega,g⟩)
       (fun⟨h1,b⟩=>⟨by omega,b⟩)⟩
   . exact⟨fun⟨h1,b⟩=>⟨by by_contra hge;have d:j=⟨m,by omega⟩:=L6 (by dsimp only;omega);rw[d] at b;exact g b,b⟩,fun⟨h1,b⟩=>⟨by omega,b⟩⟩
  rw[e];unfold es;by_cases b:(a ⟨m,by omega⟩).1.val=2
  . simp[b]
  . simp only[b,ne_eq,not_false_eq_true,↓reduceIte];have l:(⟨m,by omega⟩:Fin k)∉univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2):=(by simp);rw[W9 l];have f:((univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2)).card+1) %2=1↔¬ (univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2)).card %2=1:=(by omega);by_cases o:(univ.filter (fun j:Fin k=>j.val<m/\(a j).1.val≠2)).card %2=1<;>cases c<;>simp[o,f]
lemma el {k K:ℕ}(O:V7 (Fin k))(a:O.card=K)(r:Fin K):(univ.filter (fun j:Fin k=>j.val<(O.orderIsoOfFin a r).1.val/\j∈O)).card=r.val:=by
 have e:univ.filter (fun j:Fin k=>j.val<(O.orderIsoOfFin a r).1.val/\j∈O)=(univ.filter (fun s:Fin K=>s.val<r.val)).image (fun s=>(O.orderIsoOfFin a s).1):=by
  ext j;simp only[L4,Y2,Q0,X5];constructor
  . rintro⟨d,b⟩;let s:=(O.orderIsoOfFin a).symm ⟨j,b⟩
    have f:s<r:=(O.orderIsoOfFin a).lt_iff_lt.mp (by
     change (O.orderIsoOfFin a s).1<(O.orderIsoOfFin a r).1;rw[show (O.orderIsoOfFin a s).1=j from Q6 Subtype.val ((O.orderIsoOfFin a).apply_symm_apply ⟨j,b⟩)]
     exact d)
    exact⟨s,f,by simp[s]⟩
  . rintro⟨s,c,rfl⟩;exact⟨(O.orderIsoOfFin a).strictMono c,(O.orderIsoOfFin a s).2⟩
 rw[e,card_image_of_injective _ (fun n l h=>(O.orderIsoOfFin a).injective (Z9 h))];refine (card_bij (fun(s:Fin K) _=>s.val) (fun s i=>by simp at i ⊢;exact i) (fun _ _ _ _ h=>L6 h) (fun m g=>⟨⟨m,by rw[mem_range] at g;omega⟩,by simp only[L4,Y2,Q0];exact mem_range.mp g,rfl⟩)).trans
  (W1 r.val)
lemma lu {n d:ℕ}(m w:Y0)(sf:c7 n->ℕ):let p:=∑ t∈d3 n,sf t
 let q:=∑ t∈g7 n,sf t;let h3:=∑ t∈br n,sf t
 (univ.filter (fun l:Fin d->c7 n=>(∀ j:Fin d,l5 (d5 m l j.val) (l j)=true)/\d5 m l d=w/\∀ t:c7 n,(univ.filter (fun i=>l i=t)).card=sf t)).card=
 if p+q+h3=d/\n2 m w p=some q then choose d h3*f9 (d3 n) p sf *f9 (g7 n) q sf*f9 (br n) h3 sf
 else 0:=by
 classical
 intro p q h3;let LHS:=univ.filter (fun l:Fin d->c7 n=>(∀ j:Fin d,l5 (d5 m l j.val) (l j)=true)/\d5 m l d=w/\∀ t:c7 n,(univ.filter (fun i=>l i=t)).card=sf t);change LHS.card=_;have h7:∀(l:Fin d->c7 n),(∀ t,(univ.filter (fun i=>l i=t)).card=sf t)->∀ c:ℕ,(∑ t∈univ.filter (fun t:c7 n=>t.1.val=c),sf t)=(univ.filter (fun i:Fin d=>(l i).1.val=c)).card:=fun l h8 c=>by rw[card_eq_sum_card_fiberwise (f:=l) (s:=univ.filter (fun i=>(l i).1.val=c)) (t:=univ.filter (fun t:c7 n=>t.1.val=c)) (fun i hi=>by simp at hi ⊢;exact hi)];refine L3 rfl fun t ht=>?_;rw[<-h8 t];congr 1;ext i;simp only[L4,Y2,Q0] at ht ⊢;exact⟨fun h=>⟨h▸ht,h⟩,fun h=>h.2⟩
 have x0:∀(k:ℕ),(univ.filter (fun r:Fin k=>xor m (decide (r.val %2=1))=false)).card=if m then k/2 else (k+1)/2:=fun k=>by
  cases m
  . have hf:univ.filter (fun r:Fin k=>decide (r.val %2=1)=false)=univ.filter (fun r:Fin k=>r.val %2=0):=(by ext r;simp only[L4,Y2,Q0,M7];omega);simp[hf,(gw k).1]
  . have hf:univ.filter (fun r:Fin k=>(!decide (r.val %2=1))=false)=univ.filter (fun r:Fin k=>r.val %2=1):=(by ext r;simp only[L4,Y2,Q0,Bool.not_eq_false',L0]);simp[hf,(gw k).2]
 have k2:∀ l∈LHS,p+q+h3=d/\n2 m w p=some q:=by
  intro l a3;obtain⟨e0,r3,h8⟩:=(L4.mp a3).2;have z:=h7 l h8 0;have h1:=h7 l h8 1;have h2:=h7 l h8 2;set E:=univ.filter (fun i:Fin d=>(l i).1.val=2);set O:=Eᶜ;have m1:O=univ.filter (fun i:Fin d=>(l i).1.val=0)∪univ.filter (fun i:Fin d=>(l i).1.val=1):=(by ext i;simp only[O,E,J7,X4,L4,Y2,Q0];have:=(l i).1.isLt;omega);have b0:O.card=p+q:=by rw[m1,card_union_of_disjoint (by rw[X8];intro i a b;simp at a b;omega)];exact congrArg₂ (· + ·) z.symm h1.symm
  have e1:p+q+h3=d:=by have:=V1 E;simp only[W2,Q9] at this;change E.card+O.card=d at this;change h3=E.card at h2;omega
  have a6:p=(univ.filter (fun r:Fin O.card=>xor m (decide (r.val %2=1))=false)).card:=by
   change p=(univ.filter (fun i:Fin d=>(l i).1.val=0)).card at z;rw[z,<-n9 O rfl (fun i=>(l i).1.val) 0 (fun i hi=>by simp[O,E,hi])];congr 1;ext r;simp only[L4,Y2,Q0];set e:=(O.orderIsoOfFin rfl r).1;have hw:=ch m l e.val (le_of_lt e.isLt);have x1:(univ.filter (fun j:Fin d=>j.val<e.val/\(l j).1.val≠2))=univ.filter (fun j:Fin d=>j.val<e.val/\j∈O):=(by ext j;simp[O,E]);rw[x1,el O rfl r] at hw;have v1:=e0 e;rw[hw] at v1;have b6:(l e).1.val≠2:=(by have a2:e∈O:=(O.orderIsoOfFin rfl r).2;simp only[O,E,J7,L4,Y2,Q0] at a2;exact a2);unfold l5 at v1;simp only[V4,beq_iff_eq,b6,false_or] at v1;rw[v1];cases xor m (decide (r.val %2=1))<;>simp
  have a7:=ch m l d Y3;have b7:(univ.filter (fun j:Fin d=>j.val<d/\(l j).1.val≠2))=O:=(by ext j;simp[O,E,j.isLt]);rw[b7,r3] at a7;rw[x0 O.card,b0] at a6;rw[b0] at a7;refine⟨e1,?_⟩;cases m<;>cases w<;>simp[n2] at a6 a7 ⊢<;>omega
 by_cases a0:p+q+h3=d/\n2 m w p=some q
 . rw[Q2 a0];obtain⟨e1,m2⟩:=a0;let Eset:=(univ:V7 (Fin d)).powersetCard h3;let G0:=univ.filter (fun g:Fin p->{a // a∈d3 n}=>∀ a:{a // a∈d3 n},(univ.filter (fun i=>g i=a)).card=sf a.1);let G1:=univ.filter (fun g:Fin q->{a // a∈g7 n}=>∀ a:{a // a∈g7 n},(univ.filter (fun i=>g i=a)).card=sf a.1);let Ge:=univ.filter (fun g:Fin h3->{a // a∈br n}=>∀ a:{a // a∈br n},(univ.filter (fun i=>g i=a)).card=sf a.1);change LHS.card=choose d h3*G0.card*G1.card*Ge.card;rw[<-show Eset.card=choose d h3 by simp[Eset,Finset.card_powersetCard],mul_assoc,mul_assoc,<-card_product,<-card_product,<-card_product]
   let mkP0 (E:V7 (Fin d)) (o:E.card=h3):V7 (Fin d):=have v:Eᶜ.card=p+q:=by have:=V1 E;rw[Q9] at this;omega
    (univ.filter (fun r:Fin (p+q)=>xor m (decide (r.val %2=1))=false)).image (fun r=>(Eᶜ.orderIsoOfFin v r).1)
   let mkP1 (E:V7 (Fin d)) (o:E.card=h3):V7 (Fin d):=have v:Eᶜ.card=p+q:=by have:=V1 E;rw[Q9] at this;omega
    (univ.filter (fun r:Fin (p+q)=>xor m (decide (r.val %2=1))=true)).image (fun r=>(Eᶜ.orderIsoOfFin v r).1)
   have v0:∀(E:V7 (Fin d)) (o:E.card=h3),(mkP0 E o).card=p/\(mkP1 E o).card=q/\Disjoint (mkP0 E o) (mkP1 E o)/\Disjoint (mkP0 E o) E/\Disjoint (mkP1 E o) E/\mkP0 E o∪mkP1 E o=Eᶜ:=by
    intro E o;have v:Eᶜ.card=p+q:=(by have:=V1 E;rw[Q9] at this;omega);have b4:Injective (fun r:Fin (p+q)=>(Eᶜ.orderIsoOfFin v r).1):=fun r1 r2 h=>(Eᶜ.orderIsoOfFin v).injective (Z9 h)
    have p1:(univ.filter (fun r:Fin (p+q)=>xor m (decide (r.val %2=1))=false)).card=p:=by
     rw[x0];cases m<;>cases w<;>simp[n2] at m2 ⊢<;>omega
    have t1:(univ.filter (fun r:Fin (p+q)=>xor m (decide (r.val %2=1))=true)).card=q:=by
     have c2:=card_filter_add_card_filter_not (s:=(univ:V7 (Fin (p+q))))
      (fun r=>xor m (decide (r.val %2=1))=false)
     have p2:(univ.filter (fun r:Fin (p+q)=>¬ xor m (decide (r.val %2=1))=false))=univ.filter (fun r:Fin (p+q)=>xor m (decide (r.val %2=1))=true):=(by ext r;simp[Bool.not_eq_false]);rw[p2,p1] at c2;simp only[W2,Q9] at c2;omega
    refine⟨by simp only[mkP0,card_image_of_injective _ b4,p1],by simp only[mkP1,card_image_of_injective _ b4,t1],?_,?_,?_,?_⟩
    . rw[X8];intro x h1 h2;simp only[mkP0,mkP1,X5,L4,Y2,Q0] at h1 h2;obtain⟨r1,t2,rfl⟩:=h1;obtain⟨r2,p0,he⟩:=h2;have q2:=b4 he;subst q2;rw[t2] at p0;exact Bool.false_ne_true p0
    . rw[X8];intro x hx d0;simp only[mkP0,X5] at hx;obtain⟨r,_,rfl⟩:=hx;exact J7.mp (Eᶜ.orderIsoOfFin v r).2 d0
    . rw[X8];intro x hx d0;simp only[mkP1,X5] at hx;obtain⟨r,_,rfl⟩:=hx;exact J7.mp (Eᶜ.orderIsoOfFin v r).2 d0
    . ext x;simp only[mkP0,mkP1,X4,X5,L4,Y2,Q0];constructor
      . rintro (⟨r,_,rfl⟩|⟨r,_,rfl⟩)<;>exact (Eᶜ.orderIsoOfFin v r).2
      . intro hx;let r:=(Eᶜ.orderIsoOfFin v).symm ⟨x,hx⟩;cases hb:xor m (decide (r.val %2=1))
        . exact inl ⟨r,hb,by simp[r]⟩
        . exact inr ⟨r,hb,by simp[r]⟩
   symm
   refine card_bij (fun⟨E,g0,g1,ge⟩ hm=>have o:E.card=h3:=by simp[Eset] at hm;exact hm.1
    let u:=v0 E o
    fun e:Fin d=>if hE:e∈E then (ge ((E.orderIsoOfFin o).symm ⟨e,hE⟩)).1
     else if z:e∈mkP0 E o then (g0 (((mkP0 E o).orderIsoOfFin u.1).symm ⟨e,z⟩)).1
     else (g1 (((mkP1 E o).orderIsoOfFin u.2.1).symm ⟨e,(X4.mp (u.2.2.2.2.2.symm▸J7.mpr hE)).resolve_left z⟩)).1) ?_ ?_ ?_
   . rintro⟨E,g0,g1,ge⟩ hm;simp only[mem_product,Eset,mem_powersetCard,subset_univ,Q0,G0,G1,Ge,L4,Y2] at hm;obtain⟨o,s2,r8,s0⟩:=hm;have u:=v0 E o;have v:Eᶜ.card=p+q:=by have:=V1 E;rw[Q9] at this;omega
     set l:Fin d->c7 n:=fun e=>if hE:e∈E then (ge ((E.orderIsoOfFin o).symm ⟨e,hE⟩)).1
      else if z:e∈mkP0 E o then (g0 (((mkP0 E o).orderIsoOfFin u.1).symm ⟨e,z⟩)).1
      else (g1 (((mkP1 E o).orderIsoOfFin u.2.1).symm ⟨e,(X4.mp (u.2.2.2.2.2.symm▸J7.mpr hE)).resolve_left z⟩)).1
     have h4:∀ e,(e∈E->(l e).1.val=2)/\(e∈mkP0 E o->(l e).1.val=0)/\(e∈mkP1 E o->(l e).1.val=1):=fun e=>⟨fun hE=>by dsimp[l];rw[L7 hE];exact (L4.mp (ge _).2).2,fun z=>by dsimp[l];rw[Q8 (X8.mp u.2.2.2.1 z),L7 z];exact (L4.mp (g0 _).2).2,fun h1=>by dsimp[l];rw[Q8 (X8.mp u.2.2.2.2.1 h1),Q8 (Finset.disjoint_right.mp u.2.2.1 h1)];exact (L4.mp (g1 _).2).2⟩
     have a4:∀ j:Fin d,(l j).1.val≠2↔j∈Eᶜ:=fun j=>by
      by_cases hE:j∈E
      . simp[hE,(h4 j).1 hE]
      . have hO:=X4.mp (u.2.2.2.2.2.symm▸J7.mpr hE)
        rcases hO with z|h1
        . simp[hE,(h4 j).2.1 z]
        . simp[hE,(h4 j).2.2 h1]
     simp only[LHS,L4,Y2,Q0];refine⟨fun e=>?_,?_,fun t=>?_⟩
     . by_cases hE:e∈E
       . unfold l5;rw[(h4 e).1 hE];simp
       . rw[ch m l e.val (le_of_lt e.isLt)];have x1:univ.filter (fun j:Fin d=>j.val<e.val/\(l j).1.val≠2)=univ.filter (fun j:Fin d=>j.val<e.val/\j∈Eᶜ):=(by ext j;simp[a4]);let r:=(Eᶜ.orderIsoOfFin v).symm ⟨e,J7.mpr hE⟩;have y2:(Eᶜ.orderIsoOfFin v r).1=e:=(by simp[r]);rw[x1,<-y2,el Eᶜ v r,y2];unfold l5;cases hx:xor m (decide (r.val %2=1))
         . rw[(h4 e).2.1 (X5.mpr ⟨r,L4.mpr ⟨Y2 _,hx⟩,y2⟩)];simp
         . rw[(h4 e).2.2 (X5.mpr ⟨r,L4.mpr ⟨Y2 _,hx⟩,y2⟩)];simp
     . rw[ch m l d Y3];have x1:univ.filter (fun j:Fin d=>j.val<d/\(l j).1.val≠2)=Eᶜ:=(by ext j;simp[a4,j.isLt]);rw[x1,v];cases m<;>cases w<;>simp[n2] at m2 ⊢<;>omega
     . have w2:t.1.val=0\/t.1.val=1\/t.1.val=2:=by have:=t.1.isLt;omega
       rcases w2 with r4|ht1|ht2
       . have d1:∀ e,l e=t->e∈mkP0 E o:=fun e y=>by
          by_contra b8;by_cases hE:e∈E
          . have:=(h4 e).1 hE;rw[y] at this;omega
          . have:=(h4 e).2.2 ((X4.mp (u.2.2.2.2.2.symm▸J7.mpr hE)).resolve_left b8);rw[y] at this;omega
         rw[<-s2 ⟨t,L4.mpr ⟨Y2 _,r4⟩⟩,<-n9 (mkP0 E o) u.1 l t d1];congr 1;ext r;simp only[L4,Y2,Q0,J9,l];have z:=((mkP0 E o).orderIsoOfFin u.1 r).2;rw[Q8 (X8.mp u.2.2.2.1 z),L7 z];simp only[coe_eta,U6]
       . have g2:∀ e,l e=t->e∈mkP1 E o:=fun e y=>by
          by_contra hn1;by_cases hE:e∈E
          . have:=(h4 e).1 hE;rw[y] at this;omega
          . have:=(h4 e).2.1 ((X4.mp (u.2.2.2.2.2.symm▸J7.mpr hE)).resolve_right hn1);rw[y] at this;omega
         rw[<-r8 ⟨t,L4.mpr ⟨Y2 _,ht1⟩⟩,<-n9 (mkP1 E o) u.2.1 l t g2];congr 1;ext r;simp only[L4,Y2,Q0,J9,l];have h1:=((mkP1 E o).orderIsoOfFin u.2.1 r).2;rw[Q8 (X8.mp u.2.2.2.2.1 h1),Q8 (Finset.disjoint_right.mp u.2.2.1 h1)];simp only[coe_eta,U6]
       . have d2:∀ e,l e=t->e∈E:=fun e y=>by
          by_contra v2
          rcases X4.mp (u.2.2.2.2.2.symm▸J7.mpr v2) with z|h1
          . have:=(h4 e).2.1 z;rw[y] at this;omega
          . have:=(h4 e).2.2 h1;rw[y] at this;omega
         rw[<-s0 ⟨t,L4.mpr ⟨Y2 _,ht2⟩⟩,<-n9 E o l t d2];congr 1;ext r;simp only[L4,Y2,Q0,J9,l];rw[L7 (E.orderIsoOfFin o r).2];simp only[coe_eta,U6]
   . rintro⟨E1,g01,g11,ge1⟩ x2 ⟨E2,g02,g12,ge2⟩ s1 b9;simp only[mem_product,Eset,mem_powersetCard,subset_univ,Q0,G0,G1,Ge,L4,Y2] at x2 s1
     have r0:E1=E2:=by
      ext e;have hv:=Q6 (fun fn=>(fn e).1.val) b9;by_cases h1:e∈E1<;>by_cases h2:e∈E2<;>simp[h1,h2] at hv ⊢
      . rw[(L4.mp (ge1 _).2).2] at hv;split_ifs at hv
        . rw[(L4.mp (g02 _).2).2] at hv;omega
        . rw[(L4.mp (g12 _).2).2] at hv;omega
      . rw[(L4.mp (ge2 _).2).2] at hv;split_ifs at hv
        . rw[(L4.mp (g01 _).2).2] at hv;omega
        . rw[(L4.mp (g11 _).2).2] at hv;omega
     subst r0;have u:=v0 E1 x2.1
     have f2:ge1=ge2:=funext fun r=>Z9 (by
      have hv:=congrFun b9 (E1.orderIsoOfFin x2.1 r).1;dsimp only at hv;rw[L7 (E1.orderIsoOfFin x2.1 r).2,L7 (E1.orderIsoOfFin x2.1 r).2] at hv
      simpa only[coe_eta,U6] using hv)
     have k0:g01=g02:=funext fun r=>Z9 (by
      have z:=((mkP0 E1 x2.1).orderIsoOfFin u.1 r).2;have v2:=X8.mp u.2.2.2.1 z;have hv:=congrFun b9 ((mkP0 E1 x2.1).orderIsoOfFin u.1 r).1;dsimp only at hv;rw[Q8 v2,L7 z,Q8 v2,L7 z] at hv
      simpa only[coe_eta,U6] using hv)
     have f1:g11=g12:=funext fun r=>Z9 (by
      have h1:=((mkP1 E1 x2.1).orderIsoOfFin u.2.1 r).2;have v2:=X8.mp u.2.2.2.2.1 h1;have b8:=Finset.disjoint_right.mp u.2.2.1 h1;have hv:=congrFun b9 ((mkP1 E1 x2.1).orderIsoOfFin u.2.1 r).1;dsimp only at hv;rw[Q8 v2,Q8 b8,Q8 v2,Q8 b8] at hv
      simpa only[coe_eta,U6] using hv)
     simp[f2,k0,f1]
   . intro l a3;obtain⟨e0,_,h8⟩:=(L4.mp a3).2;set E:=univ.filter (fun i:Fin d=>(l i).1.val=2);have o:E.card=h3:=(h7 l h8 2).symm;have u:=v0 E o;have v:Eᶜ.card=p+q:=by have:=V1 E;rw[Q9] at this;omega
     have a1:∀(b:Y0) (e:Fin d),e∈(if b then mkP1 E o else mkP0 E o)->(l e).1.val=if b then 1 else 0:=fun b e hm=>by
      have c0:∃ r:Fin (p+q),xor m (decide (r.val %2=1))=b/\(Eᶜ.orderIsoOfFin v r).1=e:=by
       cases b<;>simpa[mkP0,mkP1] using hm
      obtain⟨r,hr,rfl⟩:=c0;have hw:=ch m l (Eᶜ.orderIsoOfFin v r).1.val (le_of_lt (Eᶜ.orderIsoOfFin v r).1.isLt);have x1:univ.filter (fun j:Fin d=>j.val<(Eᶜ.orderIsoOfFin v r).1.val/\(l j).1.val≠2)=univ.filter (fun j:Fin d=>j.val<(Eᶜ.orderIsoOfFin v r).1.val/\j∈Eᶜ):=(by ext j;simp[E]);rw[x1,el Eᶜ v r,hr] at hw;have v1:=e0 (Eᶜ.orderIsoOfFin v r).1;rw[hw] at v1;have b6:(l (Eᶜ.orderIsoOfFin v r).1).1.val≠2:=(by have a2:=J7.mp (Eᶜ.orderIsoOfFin v r).2;simp only[E,L4,Y2,Q0] at a2;exact a2);unfold l5 at v1;simp only[V4,beq_iff_eq,b6,false_or] at v1;exact v1
     let g0:Fin p->{a // a∈d3 n}:=fun r=>⟨l ((mkP0 E o).orderIsoOfFin u.1 r).1,L4.mpr ⟨Y2 _,a1 false _ ((mkP0 E o).orderIsoOfFin u.1 r).2⟩⟩;let g1:Fin q->{a // a∈g7 n}:=fun r=>⟨l ((mkP1 E o).orderIsoOfFin u.2.1 r).1,L4.mpr ⟨Y2 _,a1 true _ ((mkP1 E o).orderIsoOfFin u.2.1 r).2⟩⟩;let ge:Fin h3->{a // a∈br n}:=fun r=>⟨l (E.orderIsoOfFin o r).1,L4.mpr ⟨Y2 _,(L4.mp (E.orderIsoOfFin o r).2).2⟩⟩
     refine⟨(E,g0,g1,ge),?_,funext fun e=>by dsimp only;split_ifs with hE z<;>simp[g0,g1,ge]⟩
     simp only[mem_product,Eset,mem_powersetCard,subset_univ,Q0,G0,G1,Ge,L4,Y2];refine⟨o,fun a=>?_,fun a=>?_,fun a=>?_⟩
     . rw[<-h8 a.1,<-n9 (mkP0 E o) u.1 l a.1 (fun e y=>by
        have r6:(l e).1.val=0:=y▸(L4.mp a.2).2;have v2:e∉E:=by simp[E,r6]
        rcases X4.mp (u.2.2.2.2.2.symm▸J7.mpr v2) with z|h1
        . exact z
        . exfalso;have:=a1 true e h1;simp only[↓reduceIte] at this;omega)]
       congr 1;ext r;simp only[g0,L4,Y2,Q0,J9]
     . rw[<-h8 a.1,<-n9 (mkP1 E o) u.2.1 l a.1 (fun e y=>by
        have w1:(l e).1.val=1:=y▸(L4.mp a.2).2;have v2:e∉E:=by simp[E,w1]
        rcases X4.mp (u.2.2.2.2.2.symm▸J7.mpr v2) with z|h1
        . exfalso;have:=a1 false e z;simp only[J5,↓reduceIte] at this;omega
        . exact h1)]
       congr 1;ext r;simp only[g1,L4,Y2,Q0,J9]
     . rw[<-h8 a.1,<-n9 E o l a.1 (fun e y=>by simp[E,y▸(L4.mp a.2).2])];congr 1;ext r;simp only[ge,L4,Y2,Q0,J9]
 . rw[Q3 a0,U3,W8];intro l _ a3;exact a0 (k2 l (L4.mpr ⟨Y2 _,a3⟩))
end WalkAndBridge
section PureDP
def d6 (a e:ℕ):ℕ:=(2*a+1)*2^(e+1)
lemma t9 (u e:ℕ):2<=d6 u e:=by
 unfold d6;have b:2<=2^(e+1):=by rw[U4];have:1<=2^e:=Nat.one_le_pow _ _ (by omega);omega
 have a:1<=2*u+1:=(by omega);nlinarith
lemma ah {u e:ℕ}(a:e≠0):4<=d6 u e:=by
 unfold d6;have c:4<=2^(e+1):=by rw[show e+1=(e-1)+2 by omega,X6];have:1<=2^(e-1):=Nat.one_le_pow _ _ (by omega);omega
 have b:1<=2*u+1:=(by omega);nlinarith
def l9 {n:ℕ}(u e:ℕ)(a:d6 u e<=2*n):Fin n:=⟨d6 u e/2-1,by have:=t9 u e;omega⟩
def k4 {n:ℕ}(u e:ℕ)(a:e≠0)(b:d6 u e<=2*n):Fin n:=⟨d6 u e/4-1,by have:=ah a (u:=u);omega⟩
lemma dw {n l:ℕ}(h1:2<=l)(v:l<=2*n)(q:l %2=0):∃! p:Fin n×Fin (2*n),d6 p.1.val p.2.val=l:=by
 have o:∀ m:ℕ,1≤m->m≤n->∃ u e:ℕ,u<n/\e<2*n/\(2*u+1)*2^e=m:=by
  intro m;induction m using Nat.strong_induction_on with
  | ind m ih=>
   intro x h0;by_cases s:m %2=1
   . exact⟨m/2,0,by omega,by omega,by simp;omega⟩
   . obtain⟨u,e,d,j,c⟩:=ih (m/2) (by omega) (by omega) (by omega);have w:e+1<2^(e+1):=lt_two_pow_self
     have z:2^(e+1)<=m:=by
      have:1<=2*u+1:=by omega
      calc 2^(e+1)<=(2*u+1)*2^(e+1):=by nlinarith
       _=2*((2*u+1)*2^e):=by rw[U4];ring
       _=m:=by rw[c];omega
     exact⟨u,e+1,d,by omega,by
      have:(2*u+1)*2^(e+1)=2*((2*u+1)*2^e):=by rw[U4];ring
      rw[this,c];omega⟩
 obtain⟨u,e,d,j,c⟩:=o (l/2) (by omega) (by omega);have a:(2*u+1)*2^(e+1)=l:=by have:(2*u+1)*2^(e+1)=2*((2*u+1)*2^e):=(by rw[U4];ring);rw[this,c];omega
 refine⟨(⟨u,d⟩,⟨e,j⟩),by dsimp only[d6];exact a,?_⟩;rintro⟨⟨u',hu'⟩,⟨e',he'⟩⟩ h;dsimp only[d6] at h;have b:(2*u'+1)*2^(e'+1)=(2*u+1)*2^(e+1):=h.trans a.symm
 have f:e'=e:=by
  by_contra hne;rcases lt_or_gt_of_ne hne with y|hgt
  . have i:(2*u'+1)*2^(e'+1)=(2*u+1)*2^(e-e')*2^(e'+1):=by rw[b,show e+1=(e'+1)+(e-e') by omega,X6];ring
    have k:=Nat.eq_of_mul_eq_mul_right (by positivity:0<2^(e'+1)) i;have g:2 ∣ 2^(e-e'):=by rw[show e-e'=(e-e'-1)+1 by omega,U4];exact⟨2^(e-e'-1),by ring⟩
    have t:2 ∣ 2*u'+1:=k▸dvd_mul_of_dvd_right g _;omega
  . have i:(2*u'+1)*2^(e'-e)*2^(e+1)=(2*u+1)*2^(e+1):=by rw[<-b,show e'+1=(e+1)+(e'-e) by omega,X6];ring
    have k:=Nat.eq_of_mul_eq_mul_right (by positivity:0<2^(e+1)) i;have g:2 ∣ 2^(e'-e):=by rw[show e'-e=(e'-e-1)+1 by omega,U4];exact⟨2^(e'-e-1),by ring⟩
    have t:2 ∣ 2*u+1:=k.symm▸dvd_mul_of_dvd_right g _;omega
 subst f;have r:=Nat.eq_of_mul_eq_mul_right (by positivity:0<2^(e'+1)) b;exact Prod.ext (L6 (by dsimp only;omega)) (L6 rfl)
def g6 (n:ℕ)(a:ℕ->ℕ->ℤ)(b:c7 n->ℕ)(q:Fin n)(d e:ℕ):Y0:=let l:=2*q.val+1;let r:=q.val+1
 let mp:=b (e4 q true)+d;let c:=b (e4 q false)+e;decide (mp<=2*n/\c<=2*n/\(2*l<=2*n->a (2*l) (2*r)=(mp:ℤ))/\a l r=(c:ℤ)-(mp:ℤ))
def j9 (n:ℕ)(a:ℕ->ℕ->ℤ)(b:c7 n->ℕ)(q:Fin n)(d e:ℕ):Y0:=let l:=2*q.val+1;let r:=q.val
 let mp:=b (f5 q true)+d;let c:=b (f5 q false)+e;decide (mp<=2*n/\c<=2*n/\(2*l<=2*n->a (2*l) (2*r)=(mp:ℤ))/\a l r=(c:ℤ)-(mp:ℤ))
def o2 (n:ℕ) (c:ℕ->ℕ->ℤ) (d:c7 n->ℕ) (a:Fin n) (e:Fin (2*n))
 (b g i:ℕ):Y0:=
 let l:=d6 a.val e.val;let r:=l/2
 if h:l<=2*n then let q:=l9 a.val e.val h
  let mp:=d (f3 q true)+g;let f:=d (f3 q false)+i;decide (mp<=n/\f<=2*n/\c l r=(f:ℤ)-(mp:ℤ)+(b:ℤ))
 else false
def y8 {n:ℕ}(a:c7 n->ℕ)(l r:ℕ):ℕ:=if h:1<=l/\l<=2*n/\r∈n7 l then if hodd:l %2=1 then if r=l/2+1 then a (e4 ⟨l/2,by omega⟩ true) else a (f5 ⟨l/2,by omega⟩ true)
  else a (f3 ⟨l/2-1,by omega⟩ true)
 else 0
def y9 {n:ℕ}(a:c7 n->ℕ)(l r:ℕ):ℕ:=if h:1<=l/\l<=2*n/\r∈n7 l then if hodd:l %2=1 then if r=l/2+1 then a (e4 ⟨l/2,by omega⟩ false) else a (f5 ⟨l/2,by omega⟩ false)
  else a (f3 ⟨l/2-1,by omega⟩ false)
 else 0
lemma u8 {n k:ℕ}(t:Fin k->c7 n)(l r:ℕ):let tot (a:c7 n):=(univ.filter (fun i:Fin k=>t i=a)).card
 o6 t l r true=y8 tot l r/\o6 t l r false=y9 tot l r:=by
 intro tot
 have f:∀ b:Y0,o6 t l r b=if h:1<=l/\l<=2*n/\r∈n7 l then if d:l %2=1 then if r=l/2+1 then tot (e4 ⟨l/2,by omega⟩ b) else tot (f5 ⟨l/2,by omega⟩ b)
   else tot (f3 ⟨l/2-1,by omega⟩ b)
  else 0:=fun b=>by
  unfold o6;by_cases h:1<=l/\l<=2*n/\r∈n7 l
  . rw[L7 h];obtain⟨x,z,g⟩:=h;unfold n7 at g;have c:∀ a:c7 n,c3 a=l->t6 a=r->c9 a=b->(univ.filter (fun j:Fin k=>c3 (t j)=l/\t6 (t j)=r/\c9 (t j)=b)).card=tot a:=fun a p o m=>by dsimp[tot];congr 1;ext j;simp only[L4,Y2,Q0];exact⟨fun⟨u,s,h3⟩=>aw (u.trans p.symm) (s.trans o.symm) (h3.trans m.symm),fun w=>by rw[w];exact⟨p,o,m⟩⟩
    by_cases d:l %2=1
    . simp only[d,↓reduceIte,↓reduceDIte,mem_cons,not_mem_nil,or_false] at g ⊢;by_cases e:r=l/2+1
      . rw[Q2 e];exact c (e4 ⟨l/2,by omega⟩ b) (by simp[e4,c3];omega) (by simp[e4,t6];omega) rfl
      . rw[Q3 e];have y:=g.resolve_right e;exact c (f5 ⟨l/2,by omega⟩ b) (by simp[f5,c3];omega) (by simp[f5,t6];omega) rfl
    . simp only[d,↓reduceIte,↓reduceDIte,List.mem_singleton] at g ⊢;exact c (f3 ⟨l/2-1,by omega⟩ b) (by simp[f3,c3];omega) (by simp[f3,t6];omega) rfl
  . rw[Q8 h,U3,W8];intro i _ ⟨u,s,_⟩;apply h;have q:=k7 (t i);have v:=ky (t i);rw[u] at q v;rw[s] at v;exact⟨q.1,q.2,v⟩
 exact⟨f true,f false⟩
lemma fe {n:ℕ} (hn:1<=n) (k:ℕ->ℕ->ℤ)
 (v sf:c7 n->ℕ)
 (hb:∀ t:c7 n,v t+sf t≤2*n/\(t.1.val=2->v t+sf t≤n)):
 let tot (t:c7 n):=v t+sf t
 (∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (y8 tot) (y9 tot) l r=k l r)↔
 (∀ q:Fin n,g6 n k v q (sf (e4 q true)) (sf (e4 q false))=true) ∧
 (∀ q:Fin n,j9 n k v q (sf (f5 q true)) (sf (f5 q false))=true) ∧
 (∀ a:Fin n,∀ e:Fin (2*n),∀ h6:d6 a.val e.val≤2*n,let q:=l9 a.val e.val h6
  let pp:=if d:e.val=0 then 0 else tot (f3 (k4 a.val e.val d h6) true)
  o2 n k v a e pp (sf (f3 q true)) (sf (f3 q false))=true):=by
 intro tot;have h3:∀ q:Fin n,q.val+1∈n7 (2*q.val+1):=fun q=>by simp[n7,show (2*q.val+1) %2=1 by omega,show (2*q.val+1)/2=q.val by omega]
 have z:∀ q:Fin n,q.val∈n7 (2*q.val+1):=fun q=>by simp[n7,show (2*q.val+1) %2=1 by omega,show (2*q.val+1)/2=q.val by omega]
 have x:∀ q:Fin n,q.val+1∈n7 (2*q.val+2):=fun q=>by simp[n7,show ¬ (2*q.val+2) %2=1 by omega,show (2*q.val+2)/2=q.val+1 by omega]
 have w:∀ q:Fin n,y8 tot (2*q.val+1) (q.val+1)=tot (e4 q true)/\y9 tot (2*q.val+1) (q.val+1)=tot (e4 q false):=fun q=>by have hf:(⟨(2*q.val+1)/2,by omega⟩:Fin n)=q:=L6 (by dsimp only;omega);exact⟨by unfold y8;rw[L7 ⟨by omega,by omega,h3 q⟩,L7 (by omega),Q2 (by omega),hf],by unfold y9;rw[L7 ⟨by omega,by omega,h3 q⟩,L7 (by omega),Q2 (by omega),hf]⟩
 have s:∀ q:Fin n,y8 tot (2*q.val+1) q.val=tot (f5 q true)/\y9 tot (2*q.val+1) q.val=tot (f5 q false):=fun q=>by have hf:(⟨(2*q.val+1)/2,by omega⟩:Fin n)=q:=L6 (by dsimp only;omega);exact⟨by unfold y8;rw[L7 ⟨by omega,by omega,z q⟩,L7 (by omega),Q3 (by omega),hf],by unfold y9;rw[L7 ⟨by omega,by omega,z q⟩,L7 (by omega),Q3 (by omega),hf]⟩
 have g:∀ q:Fin n,y8 tot (2*q.val+2) (q.val+1)=tot (f3 q true)/\y9 tot (2*q.val+2) (q.val+1)=tot (f3 q false):=fun q=>by have hf:(⟨(2*q.val+2)/2-1,by omega⟩:Fin n)=q:=L6 (by dsimp only;omega);exact⟨by unfold y8;rw[L7 ⟨by omega,by omega,x q⟩,Q8 (by omega),hf],by unfold y9;rw[L7 ⟨by omega,by omega,x q⟩,Q8 (by omega),hf]⟩
 constructor
 . intro h7;refine⟨fun q=>?_,fun q=>?_,fun a e h6=>?_⟩
   . unfold g6;simp only[L0];refine⟨(hb _).1,(hb _).1,fun o=>?_,?_⟩
     . have h:=h7 (2*(2*q.val+1)) (J4.mpr ⟨by omega,o⟩) (2*(q.val+1))
        (K3.mpr (by unfold c4;simp[show ¬ (2*(2*q.val+1)) %2=1 by omega,show ¬ (2*(2*q.val+1)) %4=0 by omega];right;omega))
       unfold f8 at h;rw[Q3 (by unfold n7;simp[show ¬ (2*(2*q.val+1)) %2=1 by omega];omega),zero_add,Q2 ⟨by omega,by omega,by simpa[show 2*(q.val+1)/2=q.val+1 by omega,show 2*(2*q.val+1)/2=2*q.val+1 by omega] using h3 q⟩,show 2*(2*q.val+1)/2=2*q.val+1 by omega,show 2*(q.val+1)/2=q.val+1 by omega,(w q).1] at h;exact h.symm
     . have h:=h7 (2*q.val+1) (J4.mpr ⟨by omega,by omega⟩) (q.val+1) (K3.mpr (y6 (h3 q)));unfold f8 at h;rw[Q2 (h3 q),Q3 (by omega),add_zero,(w q).1,(w q).2] at h;exact h.symm
   . unfold j9;simp only[L0];refine⟨(hb _).1,(hb _).1,fun o=>?_,?_⟩
     . have h:=h7 (2*(2*q.val+1)) (J4.mpr ⟨by omega,o⟩) (2*q.val)
        (K3.mpr (by unfold c4;simp[show ¬ (2*(2*q.val+1)) %2=1 by omega,show ¬ (2*(2*q.val+1)) %4=0 by omega]))
       unfold f8 at h;rw[Q3 (by unfold n7;simp[show ¬ (2*(2*q.val+1)) %2=1 by omega]),zero_add,Q2 ⟨by omega,by omega,by simpa[show 2*q.val/2=q.val by omega,show 2*(2*q.val+1)/2=2*q.val+1 by omega] using z q⟩,show 2*(2*q.val+1)/2=2*q.val+1 by omega,show 2*q.val/2=q.val by omega,(s q).1] at h;exact h.symm
     . have h:=h7 (2*q.val+1) (J4.mpr ⟨by omega,by omega⟩) q.val (K3.mpr (y6 (z q)));unfold f8 at h;rw[Q2 (z q),Q3 (by omega),add_zero,(s q).1,(s q).2] at h;exact h.symm
   . dsimp only[o2];rw[L7 h6];simp only[L0];set l:=d6 a.val e.val;set q:=l9 a.val e.val h6;have h2:=t9 a.val e.val;have x2:l %2=0:=by have v0:2 ∣ l:=⟨(2*a.val+1)*2^e.val,by unfold l d6;rw[U4];ring⟩;omega
     have c:l=2*q.val+2:=(by dsimp[q,l9];omega);have f:l/2=q.val+1:=(by dsimp[q,l9];omega);refine⟨(hb (f3 q true)).2 rfl,(hb (f3 q false)).1,?_⟩
     have h:=h7 l (J4.mpr ⟨by omega,h6⟩) (l/2)
      (K3.mpr (y6 (by rw[f,c];exact x q)))
     unfold f8 at h;rw[Q2 (by rw[f,c];exact x q),f,c,(g q).1,(g q).2,<-c,<-f] at h;by_cases d:e.val=0
     . have a5:(l/2) %2=1:=by have y1:l=(2*a.val+1)*2:=(by unfold l d6;rw[d];simp);rw[y1,mul_div_cancel _ (by decide:0<2)];omega
       rw[Q3 (by omega),add_zero] at h;simp only[d,↓reduceDIte,Nat.cast_zero,add_zero];exact h.symm
     . have b2:=ah d (u:=a.val)
       have a3:l %4=0:=by
        have h4:4 ∣ l:=⟨(2*a.val+1)*2^(e.val-1),by
         unfold l d6;rw[show e.val+1=(e.val-1)+2 by omega,X6,show (2:ℕ)^2=4 by decide];ring⟩
        omega
       set q':=k4 a.val e.val d h6;have i:l/2=2*q'.val+2:=(by dsimp[q',k4];omega);have y:l/2/2=q'.val+1:=(by dsimp[q',k4];omega);rw[Q2 ⟨x2,by omega,by rw[y,i];exact x q'⟩,y,i,(g q').1,<-i] at h;simp only[d,↓reduceDIte];exact h.symm
 . rintro⟨h0,h1,x2⟩ l hl r hr;obtain⟨b1,h2⟩:=J4.mp hl;rw[K3] at hr;by_cases h5:l %2=1
   . set q:Fin n:=⟨l/2,by omega⟩;have c:l=2*q.val+1:=(by dsimp[q];omega);have x0:l/2=q.val:=rfl;unfold c4 at hr;simp only[h5,↓reduceIte,mem_cons,not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     . have j:=h1 q;unfold j9 at j;simp only[L0] at j;unfold f8;rw[x0,Q2 (by rw[c];exact z q),Q3 (by omega),add_zero,c,(s q).1,(s q).2];exact j.2.2.2.symm
     . have j:=h0 q;unfold g6 at j;simp only[L0] at j;unfold f8;rw[x0,Q2 (by rw[c];exact h3 q),Q3 (by omega),add_zero,c,(w q).1,(w q).2];exact j.2.2.2.symm
   . obtain⟨⟨a,e⟩,b,_⟩:=dw (by omega) h2 (by omega);dsimp only at b;have m:=x2 a e (by rw[b];exact h2);dsimp only[o2] at m;rw[L7 (by rw[b];exact h2)] at m;simp only[L0] at m;by_cases h4:l %4=0
     . unfold c4 at hr;simp only[h5,h4,↓reduceIte,List.mem_singleton] at hr;subst hr;have d:e.val≠0:=fun hz=>(by unfold d6 at b;rw[hz] at b;simp at b;omega);set q:=l9 a.val e.val (by rw[b];exact h2);set q':=k4 a.val e.val d (by rw[b];exact h2);have c:l=2*q.val+2:=(by dsimp[q,l9];rw[b];omega);have f:l/2=q.val+1:=(by dsimp[q,l9];rw[b];omega);have i:l/2=2*q'.val+2:=(by dsimp[q',k4];rw[b];omega);have y:l/2/2=q'.val+1:=(by dsimp[q',k4];rw[b];omega);unfold f8;rw[Q2 (by rw[f,c];exact x q),Q2 ⟨by omega,by omega,by rw[y,i];exact x q'⟩,y,i,(g q').1,<-i,f,c,(g q).1,(g q).2,<-c,<-f];have p:=m.2.2;simp only[d,↓reduceDIte,b] at p;exact p.symm
     . unfold c4 at hr;simp only[h5,h4,↓reduceIte,mem_cons,not_mem_nil,or_false] at hr;have d:e.val=0:=by by_contra hne;unfold d6 at b;rw[show e.val+1=(e.val-1)+2 by omega,X6] at b;have a3:4 ∣ l:=⟨(2*a.val+1)*2^(e.val-1),by linarith [b,show (2:ℕ)^2=4 by decide]⟩;omega
       have a4:l=2*(2*a.val+1):=by unfold d6 at b;rw[d] at b;simp only[zero_add,pow_one] at b;omega
       rcases hr with rfl|rfl|rfl
       . have j:=h1 a;unfold j9 at j;simp only[L0] at j;have o:=j.2.2.1 (by omega);unfold f8;have h8:l/2=2*a.val+1:=(by omega);have v0:(l/2-1)/2=a.val:=(by omega);rw[Q3 (by unfold n7;simp[h5];omega),zero_add,Q2 ⟨by omega,by omega,by rw[v0,h8];exact z a⟩,v0,h8,(s a).1,<-h8];rw[show 2*(2*a.val+1)=l by omega,show 2*a.val=l/2-1 by omega] at o;exact o.symm
       . set q:=l9 a.val e.val (by rw[b];exact h2);have c:l=2*q.val+2:=(by dsimp[q,l9];rw[b];omega);have f:l/2=q.val+1:=(by dsimp[q,l9];rw[b];omega);unfold f8;rw[Q2 (by rw[f,c];exact x q),Q3 (by omega),add_zero,f,c,(g q).1,(g q).2,<-c,<-f];have p:=m.2.2;simp only[d,↓reduceDIte,Nat.cast_zero,add_zero] at p;have y2:d6 a.val 0=l:=(by rw[<-d];exact b);rw[y2] at p;exact p.symm
       . have j:=h0 a;unfold g6 at j;simp only[L0] at j;have o:=j.2.2.1 (by omega);unfold f8;have h8:l/2=2*a.val+1:=(by omega);have v0:(l/2+1)/2=a.val+1:=(by omega);rw[Q3 (by unfold n7;simp[h5]),zero_add,Q2 ⟨by omega,by omega,by rw[v0,h8];exact h3 a⟩,v0,h8,(w a).1,<-h8];rw[show 2*(2*a.val+1)=l by omega,show 2*(a.val+1)=l/2+1 by omega] at o;exact o.symm
def od (n:ℕ) (a:ℕ->ℕ->ℤ) (c:c7 n->ℕ) (q:Fin n)
 (T:Fin (2*n+1)->Fin (n+2)->Y0->ℕ):Fin (2*n+1)->Fin (n+2)->Y0->ℕ:=
 fun f g e=>∑ sp:Fin (n+2),∑ sm:Fin (n+2),let l:=2*q.val+1;let b:=sp.val+sm.val;let d:=l*b
   if h:g6 n a c q sp.val sm.val=true/\b<=g.val/\d<=f.val then choose (g.val-b+sp.val) sp.val*choose g.val sm.val *T ⟨f.val-d,by omega⟩ ⟨g.val-b,by omega⟩ (xor e (decide (sm.val %2=1)))
   else 0
def u0 (n:ℕ)(b:ℕ->ℕ->ℤ)(c:c7 n->ℕ)(a:Y0):ℕ->Fin (2*n+1)->Fin (n+2)->Y0->ℕ
 | 0=>fun e d f=>if e.val=0/\d.val=0/\f=a then 1 else 0
 | k+1=>
  if h:k<n then od n b c ⟨k,h⟩ (u0 n b c a k)
  else u0 n b c a k
def ak (n a:ℕ) (c b:Y0)
 (T1:Fin (2*n+1)->Fin (n+2)->Y0->ℕ):
 Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ:=
 fun f e d g=>∑ so0:Fin (n+2),if n2 c b so0.val=some e.val/\so0.val+e.val+d.val=a then choose a d.val*T1 f so0 g
   else 0
def oe (n:ℕ) (b:ℕ->ℕ->ℤ) (c:c7 n->ℕ) (q:Fin n)
 (T:Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ):
 Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ:=
 fun j i e g=>∑ sp:Fin (n+2),∑ sm:Fin (n+2),let l:=2*q.val+1;let d:=sp.val+sm.val;let f:=l*d
   if h:j9 n b c q sp.val sm.val=true/\i.val+d<=n+1/\f<=j.val then let a:=i.val+d
    choose a sp.val*choose (a-sp.val) sm.val *T ⟨j.val-f,by omega⟩ ⟨a,by omega⟩ e (xor g (decide (sm.val %2=1)))
   else 0
def z0 (n:ℕ) (a:ℕ->ℕ->ℤ) (b:c7 n->ℕ)
 (Tinit:Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ):
 ℕ->Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ
 | 0=>Tinit
 | k+1=>
  if h:k<n then oe n a b ⟨k,h⟩ (z0 n a b Tinit k)
  else z0 n a b Tinit k
def ff (n:ℕ) (c:ℕ->ℕ->ℤ) (d:c7 n->ℕ) (a:Fin n) (e:Fin (2*n))
 (T:Fin (2*n+1)->Fin (2*n+1)->Y0->Fin (n+1)->ℕ):
 Fin (2*n+1)->Fin (2*n+1)->Y0->Fin (n+1)->ℕ:=
 let l:=d6 a.val e.val
 if hle:l<=2*n then let q:=l9 a.val e.val hle
  fun k i j m=>∑ prev_p:Fin (n+1),∑ sp:Fin (n+1),∑ sm:Fin (n+1),let f:=sp.val+sm.val;let g:=l*f
    if h:d (f3 q true)+sp.val=m.val/\o2 n c d a e prev_p.val sp.val sm.val=true/\i.val+f<=2*n/\g<=k.val then let b:=i.val+f
     choose b sp.val*choose (b-sp.val) sm.val *T ⟨k.val-g,by omega⟩ ⟨b,by omega⟩ (xor j (decide (sm.val %2=1))) prev_p
    else 0
 else T
def x7 (n:ℕ) (a:ℕ->ℕ->ℤ) (c:c7 n->ℕ) (b:Fin n)
 (Tinit:Fin (2*n+1)->Fin (2*n+1)->Y0->Fin (n+1)->ℕ):
 ℕ->Fin (2*n+1)->Fin (2*n+1)->Y0->Fin (n+1)->ℕ
 | 0=>Tinit
 | e+1=>
  if h:e<2*n then ff n a c b ⟨e,h⟩ (x7 n a c b Tinit e)
  else x7 n a c b Tinit e
def lv (n:ℕ) (a:ℕ->ℕ->ℤ) (c:c7 n->ℕ) (b:Fin n)
 (T:Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ):
 Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ:=
 let Tlift:=fun d f g (e:Fin (n+1))=>if e.val=0 then T d f g else 0;let Tend:=x7 n a c b Tlift (2*n)
 fun d f g=>∑ e:Fin (n+1),Tend d f g e
def z1 (n:ℕ) (a:ℕ->ℕ->ℤ) (b:c7 n->ℕ)
 (Tinit:Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ):
 ℕ->Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ
 | 0=>Tinit
 | u+1=>
  if h:u<n then lv n a b ⟨u,h⟩ (z1 n a b Tinit u)
  else z1 n a b Tinit u
def ad (n b:ℕ) (a:ℕ->ℕ->ℤ) (c:c7 n->ℕ)
 (g f d:Y0) (e:Fin (2*n+1)):ℕ:=
 let T1:=u0 n a c d n;let Tmid:=ak n b g f T1;let T2:=z0 n a c Tmid n
 z1 n a c (fun h i j=>T2 h ⟨0,by omega⟩ i j) n e ⟨0,by omega⟩ false
def x8 (n k:ℕ):V7 (c7 n):=univ.filter (fun t:c7 n=>t.1.val=0/\t.2.1.val<k)
def w7 (n k:ℕ):V7 (c7 n):=univ.filter (fun t:c7 n=>t.1.val=1/\t.2.1.val<k)
def k3 (n u e:ℕ):V7 (c7 n):=univ.filter (fun t:c7 n=>t.1.val=2/\∃ u':Fin n,∃ e':Fin (2*n),d6 u'.val e'.val=c3 t/\(u'.val<u\/(u'.val=u/\e'.val<e)))
def u6 (n:ℕ)(S:V7 (c7 n)):V7 (c7 n->Fin (2*n+1)):=univ.filter (fun a=>∀ t,t∉S->a t=0)
def r9 {n:ℕ}(S:V7 (c7 n))(a:c7 n->Fin (2*n+1)):ℕ:=∑ t∈S,(a t).val*c3 t
def d7 {n:ℕ}(S:V7 (c7 n))(a:c7 n->Fin (2*n+1)):ℕ:=∑ t∈S,(a t).val
def l4 {n:ℕ}(S:V7 (c7 n))(a:c7 n->Fin (2*n+1)):Y0:=decide ((∑ t∈S.filter (fun t=>c9 t=false),(a t).val) %2=1)
lemma fu {n:ℕ}(S1 S2:V7 (c7 n))(d:Disjoint S1 S2)(c:c7 n->Fin (2*n+1)):l4 (S1∪S2) c=xor (l4 S1 c) (l4 S2 c):=by unfold l4;rw[Finset.filter_union,X7 (Finset.disjoint_filter_filter d)];set a:=∑ t∈S1.filter (fun t=>c9 t=false),(c t).val;set b:=∑ t∈S2.filter (fun t=>c9 t=false),(c t).val;have g:(a+b) %2=1↔¬ (a %2=1↔b %2=1):=(by omega);by_cases e:a %2=1<;>by_cases f:b %2=1<;>simp[e,f,g]
lemma bh {n:ℕ} (U:V7 (c7 n)) (a b:c7 n)
 (l:a∉U) (m:b∉U) (j:a≠b) (F:(c7 n->Fin (2*n+1))->ℕ):
 ∑ sf∈u6 n (U∪{a,b}),F sf=∑ sp:Fin (2*n+1),∑ sm:Fin (2*n+1),∑ sf0∈u6 n U,F (fun t=>if t=a then sp else if t=b then sm else sf0 t):=by
 symm;rw[<-Finset.sum_product',<-Finset.sum_product'];refine sum_bij (fun⟨⟨sp,sm⟩,sf0⟩ _=>fun t=>if t=a then sp else if t=b then sm else sf0 t) ?_ ?_ ?_ (fun _ _=>rfl)
 . rintro⟨⟨sp,sm⟩,sf0⟩ h;simp only[mem_product,Y2,Q0,u6,L4] at h ⊢;intro t c;have d:t≠a:=fun q=>c (M0 _ (by simp[q]));have e:t≠b:=fun q=>c (M0 _ (by simp[q]));simp[d,e,h t (fun q=>c (M6 _ q))]
 . rintro⟨⟨p1,m1⟩,f1⟩ d ⟨⟨p2,m2⟩,f2⟩ e f;simp only[mem_product,Y2,Q0,u6,L4] at d e;have p:p1=p2:=(by have:=congrFun f a;simpa using this);have k:m1=m2:=by have:=congrFun f b;simpa[j.symm] using this
   have o:f1=f2:=funext fun t=>by
    by_cases c:t∈U
    . have:=congrFun f t;simpa[show t≠a from fun h=>l (h▸c),show t≠b from fun h=>m (h▸c)] using this
    . rw[d t c,e t c]
   simp[p,k,o]
 . intro sf g;simp only[u6,L4,Y2,Q0] at g
   refine⟨((sf a,sf b),fun t=>if t∈U then sf t else 0),by
    simp only[mem_product,Y2,Q0,u6,L4]
    intro t c;simp[c],funext fun t=>?_⟩
   by_cases d:t=a;· subst d;simp
   . by_cases e:t=b;· subst e;simp[d]
     . by_cases i:t∈U;· simp[d,e,i]
       . simp[d,e,i,g t (by simp[d,e,i])]
lemma gq {n:ℕ} {a b:c7 n} (d:c9 a=true) (e:c9 b=false)
 (c:c7 n->Fin (2*n+1)):
 l4 {a,b} c=decide ((c b).val %2=1):=by
 unfold l4;have f:({a,b}:V7 (c7 n)).filter (fun t=>c9 t=false)={b}:=by ext t;simp only[L4,X3,U5];exact⟨fun⟨h,hs⟩=>h.elim (fun g=>by rw[g,d] at hs;simp at hs) id,fun h=>⟨inr h,h▸e⟩⟩
 rw[f,sum_singleton]
lemma ap {A B:ℕ}(c:A≤B)(f:Fin B->ℕ)(b:∀ j:Fin B,A≤j.val->f j=0):(∑ i:Fin A,f ⟨i.val,by omega⟩)=∑ j:Fin B,f j:=by
 symm;rw[<-sum_subset (s₁:=univ.filter (fun j:Fin B=>j.val<A)) (filter_subset _ _) (fun j _ a=>b j (by simp at a;omega))];symm;exact sum_bij (fun(i:Fin A) _=>(⟨i.val,by omega⟩:Fin B))
  (fun i _=>by simp[i.isLt]) (fun _ _ _ _ h=>L6 (Q6 (Fin.val (n:=B)) h))
  (fun j a=>⟨⟨j.val,by simp at a;exact a⟩,Y2 _,L6 rfl⟩) (fun _ _=>rfl)
lemma pe (n:ℕ) (i:ℕ->ℕ->ℤ) (p:c7 n->ℕ) (o:Y0)
 (k:ℕ) (hk:k<=n) (z:Fin (2*n+1)) (f:Fin (n+2)) (np:Y0):
 u0 n i p o k z f np=∑ d∈u6 n (x8 n k),if(∀ q:Fin n,q.val<k->g6 n i p q (d (e4 q true)).val (d (e4 q false)).val=true)/\r9 (x8 n k) d=z.val/\d7 (x8 n k) d=f.val/\xor o (l4 (x8 n k) d)=np
   then f9 (x8 n k) f.val (fun t=>(d t).val) else 0:=by
 induction k generalizing z f np with
 | zero=>
  have h7:x8 n 0=∅:=(by ext t;simp[x8]);have h9:u6 n (x8 n 0)={fun _=>0}:=by ext d;simp only[u6,h7,notMem_empty,not_false_eq_true,forall_const,L4,Y2,Q0,U5];exact⟨funext,fun h t=>by rw[h]⟩
  rw[u0,h9,sum_singleton,h7];simp only[r9,d7,l4,it,sum_empty,Finset.filter_empty,zero_mod,zero_ne_one,decide_false,U0,Nat.not_lt_zero,IsEmpty.forall_iff,implies_true,Q0];by_cases v:z.val=0/\f.val=0/\np=o
  . rw[Q2 v,Q2 ⟨v.1.symm,v.2.1.symm,v.2.2.symm⟩,Q2 v.2.1]
  . rw[Q3 v,Q3 (fun h2=>v ⟨h2.1.symm,h2.2.1.symm,h2.2.2.symm⟩)]
 | succ k ih=>
  have v2:k<n:=(by omega);rw[u0,L7 v2];set q:Fin n:=⟨k,v2⟩;set S:=x8 n k
  have hS':x8 n (k+1)=S∪{e4 q true,e4 q false}:=by
   ext ⟨c,r,s⟩;simp only[S,x8,e4,q,X4,L4,Y2,Q0,X3,U5,J0,K4];cases s<;>constructor
   . rintro⟨l,w⟩;exact if h:r.val<k then inl ⟨l,h⟩ else inr (inr ⟨l,by omega,rfl⟩)
   . rintro (⟨l,w⟩|⟨l,w,hf⟩|⟨l,w,_⟩)<;>first|exact⟨l,by omega⟩|simp at hf
   . rintro⟨l,w⟩;exact if h:r.val<k then inl ⟨l,h⟩ else inr (inl ⟨l,by omega,rfl⟩)
   . rintro (⟨l,w⟩|⟨l,w,_⟩|⟨l,w,hf⟩)<;>first|exact⟨l,by omega⟩|simp at hf
  have ha:e4 q true∉S:=(by simp[S,x8,e4,q]);have hb:e4 q false∉S:=(by simp[S,x8,e4,q]);have e:e4 q true≠e4 q false:=fun h=>(by have:=Q6 (fun x=>x.2.2) h;simp[e4] at this);have hd:Disjoint S {e4 q true,e4 q false}:=(by simp[ha,hb]);unfold od;simp_rw[ih (by omega)];rw[hS',bh S (e4 q true) (e4 q false) ha hb e];rw[<-ap (by omega:n+2<=2*n+1)]
  . refine L3 rfl fun sp _=>?_;rw[<-ap (by omega:n+2<=2*n+1)]
    . refine L3 rfl fun sm _=>?_;have a2:f.val<=n+1:=(by omega);by_cases u:g6 n i p q sp.val sm.val=true/\sp.val+sm.val<=f.val/\(2*q.val+1)*(sp.val+sm.val)<=z.val
      . rw[L7 u,mul_sum];refine L3 rfl fun sf0 _=>?_;set d:=fun t=>if t=e4 q true then (⟨sp.val,by omega⟩:Fin (2*n+1)) else if t=e4 q false then ⟨sm.val,by omega⟩ else sf0 t;have b:∀ t∈S,d t=sf0 t:=fun t y=>by simp[d,show t≠e4 q true from fun h=>ha (h▸y),show t≠e4 q false from fun h=>hb (h▸y)]
        have x2:r9 (S∪{e4 q true,e4 q false}) d=r9 S sf0+(2*q.val+1)*(sp.val+sm.val):=by unfold r9;rw[X7 hd,V6 e,L3 rfl (fun t y=>by rw[b t y])];have v:c3 (e4 q true)=2*q.val+1:=(by simp[e4,c3]);have h2:c3 (e4 q false)=2*q.val+1:=(by simp[e4,c3]);simp only[d,↓reduceIte,e.symm,v,h2];ring
        have x1:d7 (S∪{e4 q true,e4 q false}) d=d7 S sf0+(sp.val+sm.val):=by unfold d7;rw[X7 hd,V6 e,L3 rfl (fun t y=>by rw[b t y])];simp only[d,↓reduceIte,e.symm]
        have x0:l4 (S∪{e4 q true,e4 q false}) d=xor (l4 S sf0) (decide (sm.val %2=1)):=by rw[fu S _ hd,gq rfl rfl];simp only[d,e.symm,↓reduceIte];congr 1;unfold l4;congr 3;exact L3 rfl fun t y=>Q6 Fin.val (b t (L4.mp y).1)
        have h8:(∀ r:Fin n,r.val<k+1->g6 n i p r (d (e4 r true)).val (d (e4 r false)).val=true)↔∀ r:Fin n,r.val<k->g6 n i p r (sf0 (e4 r true)).val (sf0 (e4 r false)).val=true:=by
         constructor
         . intro h r w;rw[<-b _ (L4.mpr ⟨Y2 _,rfl,w⟩),<-b _ (L4.mpr ⟨Y2 _,rfl,w⟩)];exact h r (by omega)
         . intro h r w;by_cases h6:r.val<k
           . rw[b _ (L4.mpr ⟨Y2 _,rfl,h6⟩),b _ (L4.mpr ⟨Y2 _,rfl,h6⟩)];exact h r h6
           . have:r=q:=L6 (by dsimp[q];omega);subst this;simpa[d,e.symm] using u.1
        simp only[h8,x2,x1,x0];by_cases m:(∀ r:Fin n,r.val<k->g6 n i p r (sf0 (e4 r true)).val (sf0 (e4 r false)).val=true)/\r9 S sf0=z.val-(2*q.val+1)*(sp.val+sm.val)/\d7 S sf0=f.val-(sp.val+sm.val)/\xor o (l4 S sf0)=xor np (decide (sm.val %2=1))
        . have a1:(∀ r:Fin n,r.val<k->g6 n i p r (sf0 (e4 r true)).val (sf0 (e4 r false)).val=true)/\r9 S sf0+(2*q.val+1)*(sp.val+sm.val)=z.val/\d7 S sf0+(sp.val+sm.val)=f.val/\xor o (xor (l4 S sf0) (decide (sm.val %2=1)))=np:=⟨m.1,by omega,by omega,by rw[<-Z6,m.2.2.2,Z6,Bool.xor_self,U0]⟩;rw[Q2 m,Q2 a1];have y2:f.val=(f.val-(sp.val+sm.val))+(d (e4 q true)).val+(d (e4 q false)).val:=by simp[d,e.symm];omega
          conv_rhs=>rw[y2]
          rw[cp S (e4 q true) (e4 q false) ha hb e _ (fun t=>(d t).val) (by rw[L3 rfl (fun t y=>Q6 Fin.val (b t y))];exact m.2.2.1)]
          have y1:f9 S (f.val-(sp.val+sm.val)) (fun t=>(d t).val)=f9 S (f.val-(sp.val+sm.val)) (fun t=>(sf0 t).val):=by
           unfold f9;congr 1;ext g;simp only[L4,Y2,Q0];exact forall_congr' fun a=>by rw[b a.1 a.2]
          rw[y1];simp only[d,↓reduceIte,e.symm];rw[show f.val-(sp.val+sm.val)+sp.val+sm.val=f.val by omega];ring
        . rw[Q3 m,mul_zero,Q3];intro h;exact m ⟨h.1,by omega,by omega,by rw[<-h.2.2.2,Z6,Z6,Bool.xor_self,U0]⟩
      . rw[Q8 u,L9];intro sf0 _;rw[Q3];intro h;apply u;let d:=fun t=>if t=e4 q true then (⟨sp.val,by omega⟩:Fin (2*n+1)) else if t=e4 q false then ⟨sm.val,by omega⟩ else sf0 t;have v:g6 n i p q sp.val sm.val=true:=by simpa[d,e.symm] using h.1 q (by dsimp[q];omega)
        have h2:sp.val+sm.val<=f.val:=(by have:=h.2.2.1;unfold d7 at this;rw[X7 hd,V6 e] at this;simp only[d,↓reduceIte,e.symm] at this;omega);have h3:(2*q.val+1)*(sp.val+sm.val)<=z.val:=by have:=h.2.1;unfold r9 at this;rw[X7 hd,V6 e] at this;have a0:c3 (e4 q true)=2*q.val+1:=(by simp[e4,c3]);have a3:c3 (e4 q false)=2*q.val+1:=(by simp[e4,c3]);simp only[d,↓reduceIte,e.symm,a0,a3] at this;have a4:(2*q.val+1)*(sp.val+sm.val)=sp.val*(2*q.val+1)+sm.val*(2*q.val+1):=(by ring);omega
        exact⟨v,h2,h3⟩
    . intro j hj;rw[L9];intro sf0 _;rw[Q3];intro h;have l:=h.2.2.1;unfold d7 at l;rw[X7 hd,V6 e] at l;simp only[↓reduceIte,e.symm] at l;have:=f.isLt;omega
  . intro j hj;rw[L9];intro sm _;rw[L9];intro sf0 _;rw[Q3];intro h;have l:=h.2.2.1;unfold d7 at l;rw[X7 hd,V6 e] at l;simp only[↓reduceIte,e.symm] at l;have:=f.isLt;omega
end PureDP
end SuffixDP
namespace SuffixDP
open S399 StageA RingCode BuildExt
open S393.Compiler.Build
open scoped BigOperators Classical
section DPExactness2
lemma qd (n:ℕ):x8 n n=d3 n:=by ext t;simp[x8,d3,t.2.1.isLt]
lemma qe (n:ℕ):w7 n n=g7 n:=by ext t;simp[w7,g7,t.2.1.isLt]
lemma qf (n:ℕ):k3 n n 0=br n:=by ext t;simp only[k3,br,L4,Y2,Q0];refine⟨And.left,fun a=>⟨a,?_⟩⟩;have b:2<=c3 t:=(by unfold c3;rw[a];simp only[↓reduceIte];omega);have d:c3 t %2=0:=(by unfold c3;rw[a];simp only[↓reduceIte];omega);obtain⟨⟨u',e'⟩,c,_⟩:=dw b (k7 t).2 d;exact⟨u',e',c,inl u'.isLt⟩
lemma cc {b:Type*} [DecidableEq b] (S:V7 b) (K:ℕ) (f g:b->ℕ)
 (h:∀ x∈S,f x=g x):f9 S K f=f9 S K g:=by
 unfold f9;congr 1;ext fn;simp only[L4,Y2,Q0];exact forall_congr' fun a=>by rw[h a.1 a.2]
lemma kq {a:Type*} [DecidableEq a] (R:ℕ) (S:V7 a) (f g:a->ℕ)
 (h:∀ x∈S,f x=g x):z5 R S f=z5 R S g:=by
 unfold z5;rw[L3 rfl h,cc S _ f g h]
lemma oq (n a:ℕ) (b:ℕ->ℕ->ℤ) (e:c7 n->ℕ)
 (f d c:Y0)
 (k:Fin (2*n+1)) (i:Fin (n+2)) (g:Fin (2*n+1)) (l:Y0):
 ak n a f d (u0 n b e c n) k i g l=∑ sf∈u6 n (d3 n),if(∀ q:Fin n,g6 n b e q (sf (e4 q true)).val (sf (e4 q false)).val=true)/\r9 (d3 n) sf=k.val/\n2 f d (d7 (d3 n) sf)=some i.val/\d7 (d3 n) sf+i.val+g.val=a/\d7 (d3 n) sf<=n+1/\xor c (l4 (d3 n) sf)=l
   then choose a g.val*f9 (d3 n) (d7 (d3 n) sf) (fun t=>(sf t).val)
   else 0:=by
 unfold ak;simp_rw[pe n b e c n Y3,qd]
 have p:(∑ so0:Fin (n+2),if n2 f d so0.val=some i.val/\so0.val+i.val+g.val=a then choose a g.val*∑ sf∈u6 n (d3 n),if(∀ q:Fin n,q.val<n->g6 n b e q (sf (e4 q true)).val (sf (e4 q false)).val=true)/\r9 (d3 n) sf=k.val/\d7 (d3 n) sf=so0.val/\xor c (l4 (d3 n) sf)=l
    then f9 (d3 n) so0.val (fun t=>(sf t).val) else 0
  else 0)=
  ∑ sf∈u6 n (d3 n),∑ so0:Fin (n+2),if d7 (d3 n) sf=so0.val/\n2 f d so0.val=some i.val/\so0.val+i.val+g.val=a/\(∀ q:Fin n,g6 n b e q (sf (e4 q true)).val (sf (e4 q false)).val=true)/\r9 (d3 n) sf=k.val/\xor c (l4 (d3 n) sf)=l
   then choose a g.val*f9 (d3 n) so0.val (fun t=>(sf t).val) else 0:=by
  rw[X9];refine L3 rfl fun so0 _=>?_
  split_ifs with j
  . rw[mul_sum];refine L3 rfl fun sf _=>?_;have r:(∀ q:Fin n,q.val<n->g6 n b e q (sf (e4 q true)).val (sf (e4 q false)).val=true)↔∀ q:Fin n,g6 n b e q (sf (e4 q true)).val (sf (e4 q false)).val=true:=forall_congr' fun q=>(by simp[q.isLt]);simp only[r,j.1,j.2,Q0];split_ifs<;>simp_all
  . rw[L9];intro sf _;rw[Q3];intro h;exact j ⟨h.2.1,h.2.2.1⟩
 rw[p];refine L3 rfl fun sf _=>?_;by_cases m:d7 (d3 n) sf<=n+1
 . rw[Q4 ⟨d7 (d3 n) sf,by omega⟩]
   . simp only[m,Q0,and_true];split_ifs<;>simp_all
   . intro so0 _ o;simp[show d7 (d3 n) sf≠so0.val from fun h=>o (L6 h.symm)]
   . intro h;exact absurd (Y2 _) h
 . rw[L9,Q3 (by intro h;exact m h.2.2.2.2.1)];intro so0 _;rw[Q3];intro h;have:=so0.isLt;omega
lemma pf (n g:ℕ) (a:ℕ->ℕ->ℤ) (e:c7 n->ℕ)
 (v o m:Y0)
 (k:ℕ) (hk:k<=n) (la:Fin (2*n+1)) (i:Fin (n+2)) (z:Fin (2*n+1)) (np:Y0):
 z0 n a e (ak n g v o (u0 n a e m n)) k la i z np=∑ d∈u6 n (d3 n∪w7 n k),let h6:=d7 (d3 n) d
   let h5:=i.val+d7 (w7 n k) d
   if(∀ q:Fin n,g6 n a e q (d (e4 q true)).val (d (e4 q false)).val=true)/\(∀ q:Fin n,q.val<k->j9 n a e q (d (f5 q true)).val (d (f5 q false)).val=true)/\r9 (d3 n∪w7 n k) d=la.val/\n2 v o h6=some h5/\h6+h5+z.val=g/\h6<=n+1/\h5<=n+1/\xor m (l4 (d3 n∪w7 n k) d)=np
   then choose g z.val*f9 (d3 n) h6 (fun t=>(d t).val) *z5 h5 (w7 n k) (fun t=>(d t).val)
   else 0:=by
 induction k generalizing la i np with
 | zero=>
  have a2:w7 n 0=∅:=(by ext t;simp[w7]);rw[z0,a2,union_empty,oq];refine L3 rfl fun d _=>?_;simp only[d7,sum_empty,add_zero,kp,mul_one,show i.val<=n+1 by omega,Q0,Nat.not_lt_zero,IsEmpty.forall_iff,implies_true];rfl
 | succ k ih=>
  have y1:k<n:=(by omega);rw[z0,L7 y1];set q:Fin n:=⟨k,y1⟩;set S1:=w7 n k;set U:=d3 n∪S1
  have hS1':w7 n (k+1)=S1∪{f5 q true,f5 q false}:=by
   ext ⟨c,r,s⟩;simp only[S1,w7,f5,q,X4,L4,Y2,Q0,X3,U5,J0,K4];cases s<;>constructor
   . rintro⟨l,y⟩;exact if h:r.val<k then inl ⟨l,h⟩ else inr (inr ⟨l,by omega,rfl⟩)
   . rintro (⟨l,y⟩|⟨l,y,hf⟩|⟨l,y,_⟩)<;>first|exact⟨l,by omega⟩|simp at hf
   . rintro⟨l,y⟩;exact if h:r.val<k then inl ⟨l,h⟩ else inr (inl ⟨l,by omega,rfl⟩)
   . rintro (⟨l,y⟩|⟨l,y,_⟩|⟨l,y,hf⟩)<;>first|exact⟨l,by omega⟩|simp at hf
  have hU':d3 n∪w7 n (k+1)=U∪{f5 q true,f5 q false}:=(by rw[hS1',<-Finset.union_assoc]);have v1:f5 q true∉S1:=(by simp[S1,w7,f5,q]);have x0:f5 q false∉S1:=(by simp[S1,w7,f5,q]);have v2:f5 q true∉U:=fun h=>(X4.mp h).elim (by simp[d3,f5]) v1;have v0:f5 q false∉U:=fun h=>(X4.mp h).elim (by simp[d3,f5]) x0;have f:f5 q true≠f5 q false:=fun h=>(by have:=Q6 (fun x=>x.2.2) h;simp[f5] at this);have h7:Disjoint S1 {f5 q true,f5 q false}:=(by simp[v1,x0]);have x2:Disjoint U {f5 q true,f5 q false}:=(by simp[v2,v0]);unfold oe;simp_rw[ih (by omega)];rw[hU',bh U (f5 q true) (f5 q false) v2 v0 f];rw[<-ap (by omega:n+2<=2*n+1)]
  . refine L3 rfl fun sp _=>?_;rw[<-ap (by omega:n+2<=2*n+1)]
    . refine L3 rfl fun sm _=>?_;by_cases w:j9 n a e q sp.val sm.val=true/\i.val+(sp.val+sm.val)<=n+1/\(2*q.val+1)*(sp.val+sm.val)<=la.val
      . rw[L7 w,mul_sum];refine L3 rfl fun sf0 _=>?_;set d:=fun t=>if t=f5 q true then (⟨sp.val,by omega⟩:Fin (2*n+1)) else if t=f5 q false then ⟨sm.val,by omega⟩ else sf0 t;have b:∀ t∈U,d t=sf0 t:=fun t p=>(by simp[d,show t≠f5 q true from fun h=>v2 (h▸p),show t≠f5 q false from fun h=>v0 (h▸p)]);have a5:d7 (d3 n) d=d7 (d3 n) sf0:=L3 rfl fun t p=>Q6 Fin.val (b t (M6 _ p));have a4:d7 (w7 n (k+1)) d=d7 S1 sf0+(sp.val+sm.val):=(by unfold d7;rw[hS1',X7 h7,V6 f,L3 rfl (fun t p=>Q6 Fin.val (b t (M0 _ p)))];simp only[d,↓reduceIte,f.symm]);have a1:r9 (U∪{f5 q true,f5 q false}) d=r9 U sf0+(2*q.val+1)*(sp.val+sm.val):=by unfold r9;rw[X7 x2,V6 f,L3 rfl (fun t p=>by rw[b t p])];have h1:c3 (f5 q true)=2*q.val+1:=(by simp[f5,c3]);have h2:c3 (f5 q false)=2*q.val+1:=(by simp[f5,c3]);simp only[d,↓reduceIte,f.symm,h1,h2];ring
        have y2:l4 (U∪{f5 q true,f5 q false}) d=xor (l4 U sf0) (decide (sm.val %2=1)):=(by rw[fu U _ x2,gq rfl rfl];simp only[d,f.symm,↓reduceIte];congr 1;unfold l4;congr 3;exact L3 rfl fun t p=>Q6 Fin.val (b t (L4.mp p).1));have b0:(∀ r:Fin n,g6 n a e r (d (e4 r true)).val (d (e4 r false)).val=true)↔∀ r:Fin n,g6 n a e r (sf0 (e4 r true)).val (sf0 (e4 r false)).val=true:=forall_congr' fun r=>by rw[b _ (M6 _ (by simp[d3,e4])),b _ (M6 _ (by simp[d3,e4]))]
        have b1:(∀ r:Fin n,r.val<k+1->j9 n a e r (d (f5 r true)).val (d (f5 r false)).val=true)↔∀ r:Fin n,r.val<k->j9 n a e r (sf0 (f5 r true)).val (sf0 (f5 r false)).val=true:=by
         constructor
         . intro h r y;rw[<-b _ (M0 _ (L4.mpr ⟨Y2 _,rfl,y⟩)),<-b _ (M0 _ (L4.mpr ⟨Y2 _,rfl,y⟩))];exact h r (by omega)
         . intro h r y;by_cases h9:r.val<k
           . rw[b _ (M0 _ (L4.mpr ⟨Y2 _,rfl,h9⟩)),b _ (M0 _ (L4.mpr ⟨Y2 _,rfl,h9⟩))];exact h r h9
           . have:r=q:=L6 (by dsimp[q];omega);subst this;simpa[d,f.symm] using w.1
        simp only[a5,a4,a1,y2,b0,b1];have h8:i.val+(d7 S1 sf0+(sp.val+sm.val))=i.val+(sp.val+sm.val)+d7 S1 sf0:=(by omega);rw[h8];by_cases u:(∀ r:Fin n,g6 n a e r (sf0 (e4 r true)).val (sf0 (e4 r false)).val=true)/\(∀ r:Fin n,r.val<k->j9 n a e r (sf0 (f5 r true)).val (sf0 (f5 r false)).val=true)/\r9 U sf0=la.val-(2*q.val+1)*(sp.val+sm.val)/\n2 v o (d7 (d3 n) sf0)=some (i.val+(sp.val+sm.val)+d7 S1 sf0)/\d7 (d3 n) sf0+(i.val+(sp.val+sm.val)+d7 S1 sf0)+z.val=g/\d7 (d3 n) sf0<=n+1/\i.val+(sp.val+sm.val)+d7 S1 sf0<=n+1/\xor m (l4 U sf0)=xor np (decide (sm.val %2=1))
        . have a7:(∀ r:Fin n,g6 n a e r (sf0 (e4 r true)).val (sf0 (e4 r false)).val=true)/\(∀ r:Fin n,r.val<k->j9 n a e r (sf0 (f5 r true)).val (sf0 (f5 r false)).val=true)/\r9 U sf0+(2*q.val+1)*(sp.val+sm.val)=la.val/\n2 v o (d7 (d3 n) sf0)=some (i.val+(sp.val+sm.val)+d7 S1 sf0)/\d7 (d3 n) sf0+(i.val+(sp.val+sm.val)+d7 S1 sf0)+z.val=g/\d7 (d3 n) sf0<=n+1/\i.val+(sp.val+sm.val)+d7 S1 sf0<=n+1/\xor m (xor (l4 U sf0) (decide (sm.val %2=1)))=np:=⟨u.1,u.2.1,by omega,u.2.2.2.1,u.2.2.2.2.1,u.2.2.2.2.2.1,u.2.2.2.2.2.2.1,by rw[<-Z6,u.2.2.2.2.2.2.2,Z6,Bool.xor_self,U0]⟩;rw[Q2 u,Q2 a7,hS1',cc (d3 n) _ (fun t=>(d t).val) (fun t=>(sf0 t).val) (fun t p=>Q6 Fin.val (b t (M6 _ p)))];have h0:∑ x∈S1,(d x).val=d7 S1 sf0:=L3 rfl fun t p=>Q6 Fin.val (b t (M0 _ p));rw[fm _ S1 (f5 q true) (f5 q false) v1 x0 f (fun t=>(d t).val) (by rw[h0];simp[d,f.symm];omega),kq _ S1 (fun t=>(d t).val) (fun t=>(sf0 t).val) (fun t p=>Q6 Fin.val (b t (M0 _ p))),h0];simp only[d,↓reduceIte,f.symm,show i.val+(sp.val+sm.val)+d7 S1 sf0-d7 S1 sf0=i.val+(sp.val+sm.val) by omega];ring
        . rw[Q3 u,mul_zero,Q3];intro h;exact u ⟨h.1,h.2.1,by omega,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,by rw[<-h.2.2.2.2.2.2.2,Z6,Z6,Bool.xor_self,U0]⟩
      . rw[Q8 w,L9];intro sf0 _;rw[Q3];intro h;apply w;let d:=fun t=>if t=f5 q true then (⟨sp.val,by omega⟩:Fin (2*n+1)) else if t=f5 q false then ⟨sm.val,by omega⟩ else sf0 t;have h1:j9 n a e q sp.val sm.val=true:=by simpa[d,f.symm] using h.2.1 q (by dsimp[q];omega)
        have h2:i.val+(sp.val+sm.val)<=n+1:=(by have:=h.2.2.2.2.2.2.1;unfold d7 at this;rw[hS1',X7 h7,V6 f] at this;simp only[d,↓reduceIte,f.symm] at this;omega);have h3:(2*q.val+1)*(sp.val+sm.val)<=la.val:=by have:=h.2.2.1;unfold r9 at this;rw[X7 x2,V6 f] at this;have a6:c3 (f5 q true)=2*q.val+1:=(by simp[f5,c3]);have b2:c3 (f5 q false)=2*q.val+1:=(by simp[f5,c3]);simp only[d,↓reduceIte,f.symm,a6,b2] at this;have b3:(2*q.val+1)*(sp.val+sm.val)=sp.val*(2*q.val+1)+sm.val*(2*q.val+1):=(by ring);omega
        exact⟨h1,h2,h3⟩
    . intro j hj;rw[L9];intro sf0 _;rw[Q3];intro h;have l:=h.2.2.2.2.2.2.1;unfold d7 at l;rw[hS1',X7 h7,V6 f] at l;simp only[↓reduceIte,f.symm] at l;omega
  . intro j hj;rw[L9];intro sm _;rw[L9];intro sf0 _;rw[Q3];intro h;have l:=h.2.2.2.2.2.2.1;unfold d7 at l;rw[hS1',X7 h7,V6 f] at l;simp only[↓reduceIte,f.symm] at l;omega
def o4 (n:ℕ)(a:ℕ->ℕ->ℤ)(b:c7 n->ℕ)(u e:ℕ)(c:c7 n->Fin (2*n+1)):Prop:=∀ u':Fin n,∀ e':Fin (2*n),(u'.val<u\/(u'.val=u/\e'.val<e))->∀ hle:d6 u'.val e'.val≤2*n,let q:=l9 u'.val e'.val hle
   let d:=if he0:e'.val=0 then 0 else b (f3 (k4 u'.val e'.val he0 hle) true)+(c (f3 (k4 u'.val e'.val he0 hle) true)).val
   o2 n a b u' e' d (c (f3 q true)).val (c (f3 q false)).val=true
def k5 (n:ℕ)(b:c7 n->ℕ)(a:Fin n)(e:ℕ)(c:c7 n->Fin (2*n+1)):ℕ:=match e with
 | 0=>0
 | e'+1=>
  if h:d6 a.val e'<=2*n then b (f3 (l9 a.val e' h) true)+(c (f3 (l9 a.val e' h) true)).val
  else k5 n b a e' c
lemma pg (n v:ℕ) (i:ℕ->ℕ->ℤ) (g:c7 n->ℕ)
 (y2 h8 h9:Y0) (d:Fin n)
 (T0:Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ)
 (hT0:∀(la re:Fin (2*n+1)) (np:Y0),T0 la re np=∑ k∈u6 n (d3 n∪g7 n∪k3 n d.val 0),let b0:=d7 (d3 n) k;let a7:=d7 (g7 n) k
    let a6:=re.val+d7 (k3 n d.val 0) k
    if(∀ q:Fin n,g6 n i g q (k (e4 q true)).val (k (e4 q false)).val=true)/\(∀ q:Fin n,j9 n i g q (k (f5 q true)).val (k (f5 q false)).val=true)/\o4 n i g d.val 0 k/\r9 (d3 n∪g7 n∪k3 n d.val 0) k=la.val/\n2 y2 h8 b0=some a7/\b0+a7+a6=v/\b0<=n+1/\a7<=n+1/\a6<=2*n/\xor h9 (l4 (d3 n∪g7 n∪k3 n d.val 0) k)=np
    then choose v a6*f9 (d3 n) b0 (fun t=>(k t).val) *f9 (g7 n) a7 (fun t=>(k t).val)*z5 a6 (k3 n d.val 0) (fun t=>(k t).val)
    else 0)
 (e:ℕ) (he:e<=2*n) (la' re':Fin (2*n+1)) (np':Y0) (pp:Fin (n+1)):
 x7 n i g d (fun s1 d1 w2 p0=>if p0.val=0 then T0 s1 d1 w2 else 0) e la' re' np' pp=∑ k∈u6 n (d3 n∪g7 n∪k3 n d.val e),let b0:=d7 (d3 n) k;let a7:=d7 (g7 n) k;let a6:=re'.val+d7 (k3 n d.val e) k
   if(∀ q:Fin n,g6 n i g q (k (e4 q true)).val (k (e4 q false)).val=true)/\(∀ q:Fin n,j9 n i g q (k (f5 q true)).val (k (f5 q false)).val=true)/\o4 n i g d.val e k/\k5 n g d e k=pp.val/\r9 (d3 n∪g7 n∪k3 n d.val e) k=la'.val/\n2 y2 h8 b0=some a7/\b0+a7+a6=v/\b0<=n+1/\a7<=n+1/\a6<=2*n/\xor h9 (l4 (d3 n∪g7 n∪k3 n d.val e) k)=np'
   then choose v a6*f9 (d3 n) b0 (fun t=>(k t).val) *f9 (g7 n) a7 (fun t=>(k t).val)*z5 a6 (k3 n d.val e) (fun t=>(k t).val)
   else 0:=by
 classical
 induction e generalizing la' re' np' pp with
 | zero=>
  rw[x7];by_cases m1:pp.val=0
  . rw[Q2 m1,hT0];refine L3 rfl fun k _=>by simp[k5,m1]
  . rw[Q3 m1,L9];intro k _;rw[Q3];intro h;exact m1 h.2.2.2.1.symm
 | succ e ihe=>
  have h6:e<2*n:=(by omega);rw[x7,L7 h6];set l:=d6 d.val e;unfold ff;by_cases o:l<=2*n
  . rw[L7 o];set q:=l9 d.val e o;set Se:=k3 n d.val e;set U:=d3 n∪g7 n∪Se
    have c0:c3 (f3 q true)=l/\c3 (f3 q false)=l:=by
     have s0:l %2=0:=by have q1:2 ∣ l:=⟨(2*d.val+1)*2^e,by unfold l d6;rw[U4];ring⟩;omega
     have w1:=t9 d.val e;constructor<;>(simp[f3,c3,q,l9];omega)
    have hSe':k3 n d.val (e+1)=Se∪{f3 q true,f3 q false}:=by
     ext t;simp only[Se,k3,X4,L4,Y2,Q0,X3,U5];constructor
     . rintro⟨e2,u',e',a5,w⟩
       rcases w with m2|⟨hu',m2⟩
       . exact inl ⟨e2,u',e',a5,inl m2⟩
       . by_cases hv:e'.val<e
         . exact inl ⟨e2,u',e',a5,inr ⟨hu',hv⟩⟩
         . have f1:c3 t=l:=by rw[<-a5,hu',show e'.val=e by omega]
           have r0:t.2.1=q:=L6 (by unfold c3 at f1;rw[e2] at f1;simp only[↓reduceIte] at f1;dsimp[q,l9];omega);have p2:t.1=⟨2,by decide⟩:=L6 e2
           rcases t with ⟨c,r,s⟩;dsimp at p2 r0;subst p2;subst r0;cases s<;>simp[f3]
     . rintro (⟨e2,u',e',a5,w⟩|rfl|rfl)
       . exact⟨e2,u',e',a5,w.imp id (fun⟨a,b⟩=>⟨a,by omega⟩)⟩
       . exact⟨rfl,d,⟨e,h6⟩,c0.1.symm,inr ⟨rfl,by dsimp only;omega⟩⟩
       . exact⟨rfl,d,⟨e,h6⟩,c0.2.symm,inr ⟨rfl,by dsimp only;omega⟩⟩
    have hU':d3 n∪g7 n∪k3 n d.val (e+1)=U∪{f3 q true,f3 q false}:=by rw[hSe',<-Finset.union_assoc]
    have v2:f3 q true∉Se/\f3 q false∉Se:=by
     have t1:∀ s:Y0,f3 q s∉Se:=fun s r2=>by
      simp only[Se,k3,L4,Y2,Q0] at r2;obtain⟨_,u',e',a5,w⟩:=r2;rw[show c3 (f3 q s)=l by cases s;exact c0.2;exact c0.1] at a5;have s0:l %2=0:=by have q1:2 ∣ l:=⟨(2*d.val+1)*2^e,by unfold l d6;rw[U4];ring⟩;omega
      obtain⟨_,_,q2⟩:=dw (t9 d.val e) o s0;have h3:=(q2 (u',e') a5).trans (q2 (d,⟨e,h6⟩) rfl).symm;have hc:=Q6 (fun p=>p.1.val) h3;have hd:=Q6 (fun p=>p.2.val) h3;dsimp only at hc hd;omega
     exact⟨t1 true,t1 false⟩
    have ha:f3 q true∉U:=fun h=>(X4.mp h).elim (fun r7=>(X4.mp r7).elim (by simp[d3,f3]) (by simp[g7,f3])) v2.1;have r3:f3 q false∉U:=fun h=>(X4.mp h).elim (fun r7=>(X4.mp r7).elim (by simp[d3,f3]) (by simp[g7,f3])) v2.2;have x1:f3 q true≠f3 q false:=fun h=>(by have:=Q6 (fun x=>x.2.2) h;simp[f3] at this);have hi:Disjoint Se {f3 q true,f3 q false}:=(by simp[v2.1,v2.2]);have r6:Disjoint U {f3 q true,f3 q false}:=by simp[ha,r3]
    have k2:∀ f,k5 n g d e f=if y:e=0 then 0 else g (f3 (k4 d.val e y o) true)+(f (f3 (k4 d.val e y o) true)).val:=fun f=>by
     cases e with
     | zero=>simp[k5]
     | succ e'=>
      have x0:d6 d.val e'<=2*n:=by dsimp only[l] at o;unfold d6 at o ⊢;rw[U4,<-Z3] at o;omega
      have hr:l9 d.val e' x0=k4 d.val (e'+1) (succ_ne_zero _) o:=L6 (by
        dsimp only[l9,k4,d6];set a:=(2*d.val+1)*2^(e'+1);have h2:(2*d.val+1)*2^(e'+1+1)=a*2:=by rw[U4];ring
        rw[h2];omega)
      dsimp only[k5];rw[L7 x0,Q8 (succ_ne_zero _),hr]
    have g0:∀(y:e≠0),f3 (k4 d.val e y o) true∈Se:=fun y=>by
     simp only[Se,k3,L4,Y2,Q0];refine⟨rfl,d,⟨e-1,by omega⟩,?_,inr ⟨rfl,by dsimp only;omega⟩⟩;dsimp only[f3,c3,k4,d6];simp only[↓reduceIte];have r4:=ah y (u:=d.val);dsimp only[d6] at r4;have h4:(2*d.val+1)*2^(e+1)=(2*d.val+1)*2^(e-1+1)*2:=by rw[show e+1=(e-1+1)+1 by omega,U4];ring
     have q1:2 ∣ (2*d.val+1)*2^(e-1+1):=⟨(2*d.val+1)*2^(e-1),by
      rw[show e-1+1=(e-1)+1 by omega,U4];ring⟩
     rw[h4];omega
    simp_rw[ihe (by omega)];rw[hU',bh U (f3 q true) (f3 q false) ha r3 x1];rw[X9,<-ap (by omega:n+1<=2*n+1)]
    . refine L3 rfl fun sp _=>?_;rw[X9,<-ap (by omega:n+1<=2*n+1)]
      . refine L3 rfl fun sm _=>?_;let P0 (f:c7 n->Fin (2*n+1)) (s1 d1:ℕ) (w2:Y0):Prop:=(∀ r:Fin n,g6 n i g r (f (e4 r true)).val (f (e4 r false)).val=true)/\(∀ r:Fin n,j9 n i g r (f (f5 r true)).val (f (f5 r false)).val=true)/\o4 n i g d.val e f/\r9 U f=s1/\n2 y2 h8 (d7 (d3 n) f)=some (d7 (g7 n) f)/\d7 (d3 n) f+d7 (g7 n) f+(d1+d7 Se f)=v/\d7 (d3 n) f<=n+1/\d7 (g7 n) f<=n+1/\d1+d7 Se f<=2*n/\xor h9 (l4 U f)=w2;let V0 (f:c7 n->Fin (2*n+1)) (d1:ℕ):ℕ:=choose v (d1+d7 Se f)*f9 (d3 n) (d7 (d3 n) f) (fun t=>(f t).val) *f9 (g7 n) (d7 (g7 n) f) (fun t=>(f t).val)*z5 (d1+d7 Se f) Se (fun t=>(f t).val);let ds:=sp.val+sm.val;let mC:=choose (re'.val+ds) sp.val*choose (re'.val+ds-sp.val) sm.val
        have hh:∀ z:Fin (n+1),(if h:g (f3 q true)+sp.val=pp.val/\o2 n i g d ⟨e,h6⟩ z.val sp.val sm.val=true/\re'.val+ds<=2*n/\l*ds<=la'.val then mC*∑ f∈u6 n U,if(∀ r:Fin n,g6 n i g r (f (e4 r true)).val (f (e4 r false)).val=true)/\(∀ r:Fin n,j9 n i g r (f (f5 r true)).val (f (f5 r false)).val=true)/\o4 n i g d.val e f/\k5 n g d e f=z.val/\r9 U f=la'.val-l*ds/\n2 y2 h8 (d7 (d3 n) f)=some (d7 (g7 n) f)/\d7 (d3 n) f+d7 (g7 n) f+(re'.val+ds+d7 Se f)=v/\d7 (d3 n) f<=n+1/\d7 (g7 n) f<=n+1/\re'.val+ds+d7 Se f<=2*n/\xor h9 (l4 U f)=xor np' (decide (sm.val %2=1)) then V0 f (re'.val+ds) else 0
         else 0)=
         ∑ f∈u6 n U,if g (f3 q true)+sp.val=pp.val/\o2 n i g d ⟨e,h6⟩ z.val sp.val sm.val=true/\re'.val+ds<=2*n/\l*ds<=la'.val/\k5 n g d e f=z.val/\P0 f (la'.val-l*ds) (re'.val+ds) (xor np' (decide (sm.val %2=1)))
         then mC*V0 f (re'.val+ds) else 0:=fun z=>by
         by_cases hp:g (f3 q true)+sp.val=pp.val/\o2 n i g d ⟨e,h6⟩ z.val sp.val sm.val=true/\re'.val+ds<=2*n/\l*ds<=la'.val
         . rw[L7 hp,mul_sum];refine L3 rfl fun f _=>?_;dsimp only[P0];by_cases h1:(∀ r:Fin n,g6 n i g r (f (e4 r true)).val (f (e4 r false)).val=true)/\(∀ r:Fin n,j9 n i g r (f (f5 r true)).val (f (f5 r false)).val=true)/\o4 n i g d.val e f/\k5 n g d e f=z.val/\r9 U f=la'.val-l*ds/\n2 y2 h8 (d7 (d3 n) f)=some (d7 (g7 n) f)/\d7 (d3 n) f+d7 (g7 n) f+(re'.val+ds+d7 Se f)=v/\d7 (d3 n) f<=n+1/\d7 (g7 n) f<=n+1/\re'.val+ds+d7 Se f<=2*n/\xor h9 (l4 U f)=xor np' (decide (sm.val %2=1))
           . rw[Q2 h1,Q2 ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,h1.2.2.2.1,h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.2⟩]
           . rw[Q3 h1,mul_zero,Q3];intro h2;obtain⟨_,_,_,_,hl,b1,b2,b3,brest⟩:=h2;exact h1 ⟨b1,b2,b3,hl,brest⟩
         . rw[Q8 hp,L9];intro f _;rw[Q3];intro h;exact hp ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
        rw[L3 rfl fun z _=>hh z];rw[X9];refine L3 rfl fun f _=>?_;set k:=fun t=>if t=f3 q true then (⟨sp.val,by omega⟩:Fin (2*n+1)) else if t=f3 q false then ⟨sm.val,by omega⟩ else f t;have m:∀ t∈U,k t=f t:=fun t ht=>(by simp[k,show t≠f3 q true from fun h=>ha (h▸ht),show t≠f3 q false from fun h=>r3 (h▸ht)]);have hx:d7 (d3 n) k=d7 (d3 n) f:=L3 rfl fun t ht=>Q6 Fin.val (m t (M6 _ (M6 _ ht)));have hw:d7 (g7 n) k=d7 (g7 n) f:=L3 rfl fun t ht=>Q6 Fin.val (m t (M6 _ (M0 _ ht)));have heu:d7 (k3 n d.val (e+1)) k=d7 Se f+ds:=(by unfold d7;rw[hSe',X7 hi,V6 x1,L3 rfl (fun t ht=>Q6 Fin.val (m t (M0 _ ht)))];simp only[k,↓reduceIte,x1.symm,ds]);have d0:r9 (U∪{f3 q true,f3 q false}) k=r9 U f+l*ds:=by unfold r9;rw[X7 r6,V6 x1,L3 rfl (fun t ht=>by rw[m t ht])];simp only[k,↓reduceIte,x1.symm,c0.1,c0.2,ds];ring
        have hm:l4 (U∪{f3 q true,f3 q false}) k=xor (l4 U f) (decide (sm.val %2=1)):=(by rw[fu U _ r6,gq rfl rfl];simp only[k,x1.symm,↓reduceIte];congr 1;unfold l4;congr 3;exact L3 rfl fun t ht=>Q6 Fin.val (m t (L4.mp ht).1));have hf:k5 n g d (e+1) k=g (f3 q true)+sp.val:=by unfold k5;rw[L7 o];simp[k,q]
        have r1:o4 n i g d.val (e+1) k↔o4 n i g d.val e f/\o2 n i g d ⟨e,h6⟩ (k5 n g d e f) sp.val sm.val=true:=by
         have y1:∀(u':Fin n) (e':Fin (2*n)) (w:u'.val<d.val\/u'.val=d.val/\e'.val<e) (hle':d6 u'.val e'.val≤2*n) (s:Y0),f3 (l9 u'.val e'.val hle') s∈Se:=fun u' e' w hle' s=>by
          simp only[Se,k3,L4,Y2,Q0];refine⟨rfl,u',e',?_,w⟩;have hev':d6 u'.val e'.val %2=0:=by have q1:2 ∣ d6 u'.val e'.val:=⟨(2*u'.val+1)*2^e'.val,by unfold d6;rw[U4];ring⟩;omega
          have hl2':=t9 u'.val e'.val;simp[f3,c3,l9];omega
         have d2:∀(u':Fin n) (e':Fin (2*n)) (w:u'.val<d.val\/u'.val=d.val/\e'.val<e) (y:e'.val≠0) (hle':d6 u'.val e'.val≤2*n),f3 (k4 u'.val e'.val y hle') true∈Se:=fun u' e' w y hle'=>by
          simp only[Se,k3,L4,Y2,Q0];refine⟨rfl,u',⟨e'.val-1,by omega⟩,?_,w.imp id (fun⟨a,b⟩=>⟨a,by dsimp only;omega⟩)⟩;have hl4':=ah y (u:=u'.val);dsimp only[d6] at hl4';dsimp only[f3,c3,k4,d6];simp only[↓reduceIte];have h4:(2*u'.val+1)*2^(e'.val+1)=(2*u'.val+1)*2^(e'.val-1+1)*2:=by rw[show e'.val+1=(e'.val-1+1)+1 by omega,U4];ring
          have q1:2 ∣ (2*u'.val+1)*2^(e'.val-1+1):=⟨(2*u'.val+1)*2^(e'.val-1),by
           rw[show e'.val-1+1=(e'.val-1)+1 by omega,U4];ring⟩
          rw[h4];omega
         have e1:(let pp:=if y:e=0 then 0 else g (f3 (k4 d.val e y o) true)+(k (f3 (k4 d.val e y o) true)).val
          o2 n i g d ⟨e,h6⟩ pp (k (f3 q true)).val (k (f3 q false)).val=true)↔
          o2 n i g d ⟨e,h6⟩ (k5 n g d e f) sp.val sm.val=true:=by
          rw[k2 f];by_cases y:e=0
          . simp[y,k,x1.symm]
          . dsimp only;rw[Q8 y,Q8 y,m _ (M0 _ (g0 y))];simp[k,x1.symm]
         constructor
         . intro h;refine⟨fun u' e' w hle'=>?_,e1.mp (h d ⟨e,h6⟩ (inr ⟨rfl,by dsimp only;omega⟩) o)⟩;have h1:=h u' e' (w.imp id (fun⟨a,b⟩=>⟨a,by omega⟩)) hle';dsimp only at h1 ⊢;rw[m _ (M0 _ (y1 u' e' w hle' true)),m _ (M0 _ (y1 u' e' w hle' false))] at h1;by_cases y:e'.val=0
           . simp only[y,↓reduceDIte] at h1 ⊢;exact h1
           . simp only[y,↓reduceDIte,m _ (M0 _ (d2 u' e' w y hle'))] at h1 ⊢;exact h1
         . rintro⟨h0,hq⟩ u' e' w hle';by_cases c2:u'.val<d.val\/u'.val=d.val/\e'.val<e
           . have h1:=h0 u' e' c2 hle';dsimp only at h1 ⊢;rw[m _ (M0 _ (y1 u' e' c2 hle' true)),m _ (M0 _ (y1 u' e' c2 hle' false))];by_cases y:e'.val=0
             . simp only[y,↓reduceDIte] at h1 ⊢;exact h1
             . simp only[y,↓reduceDIte,m _ (M0 _ (d2 u' e' c2 y hle'))] at h1 ⊢;exact h1
           . have hu':u'=d:=L6 (by omega);have he':e'=⟨e,h6⟩:=L6 (by dsimp only;omega);subst hu';subst he';exact e1.mpr hq
        have g2:o4 n i g d.val e f->k5 n g d e f<=n:=fun hs=>by
         cases e with
         | zero=>simp[k5]
         | succ e'=>
          have x0:d6 d.val e'<=2*n:=(by unfold l d6 at o;unfold d6;rw[U4,<-Z3] at o;omega);have p1:=hs d ⟨e',by omega⟩ (inr ⟨rfl,by dsimp only;omega⟩) x0;dsimp only[o2] at p1;rw[L7 x0] at p1;simp only[L0] at p1;simpa only[k5,L7 x0] using p1.1
        have hz:(∀ r:Fin n,g6 n i g r (k (e4 r true)).val (k (e4 r false)).val=true)↔∀ r:Fin n,g6 n i g r (f (e4 r true)).val (f (e4 r false)).val=true:=forall_congr' fun r=>by rw[m _ (M6 _ (M6 _ (by simp[d3,e4]))),m _ (M6 _ (M6 _ (by simp[d3,e4])))]
        have hq1:(∀ r:Fin n,j9 n i g r (k (f5 r true)).val (k (f5 r false)).val=true)↔∀ r:Fin n,j9 n i g r (f (f5 r true)).val (f (f5 r false)).val=true:=forall_congr' fun r=>by rw[m _ (M6 _ (M0 _ (by simp[g7,f5]))),m _ (M6 _ (M0 _ (by simp[g7,f5])))]
        simp only[hx,hw,heu,d0,hm,hf,r1,hz,hq1];have r8:re'.val+(d7 Se f+ds)=re'.val+ds+d7 Se f:=(by omega);rw[r8];by_cases x2:g (f3 q true)+sp.val=pp.val/\o2 n i g d ⟨e,h6⟩ (k5 n g d e f) sp.val sm.val=true/\re'.val+ds<=2*n/\l*ds<=la'.val/\P0 f (la'.val-l*ds) (re'.val+ds) (xor np' (decide (sm.val %2=1)))
        . have hle_p:=g2 x2.2.2.2.2.2.2.1;have g1:(∀ r:Fin n,g6 n i g r (f (e4 r true)).val (f (e4 r false)).val=true)/\(∀ r:Fin n,j9 n i g r (f (f5 r true)).val (f (f5 r false)).val=true)/\(o4 n i g d.val e f/\o2 n i g d ⟨e,h6⟩ (k5 n g d e f) sp.val sm.val=true)/\g (f3 q true)+sp.val=pp.val/\r9 U f+l*ds=la'.val/\n2 y2 h8 (d7 (d3 n) f)=some (d7 (g7 n) f)/\d7 (d3 n) f+d7 (g7 n) f+(re'.val+ds+d7 Se f)=v/\d7 (d3 n) f<=n+1/\d7 (g7 n) f<=n+1/\re'.val+ds+d7 Se f<=2*n/\xor h9 (xor (l4 U f) (decide (sm.val %2=1)))=np':=by obtain⟨a1,a2,a3,a4,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10⟩:=x2;exact⟨b1,b2,⟨b3,a2⟩,a1,by omega,b5,b6,b7,b8,b9,by rw[<-Z6,b10,Z6,Bool.xor_self,U0]⟩
          rw[Q2 g1,Q4 ⟨k5 n g d e f,by omega⟩]
          . rw[Q2 ⟨x2.1,x2.2.1,x2.2.2.1,x2.2.2.2.1,rfl,x2.2.2.2.2⟩,hSe',cc (d3 n) _ (fun t=>(k t).val) (fun t=>(f t).val) (fun t ht=>Q6 Fin.val (m t (M6 _ (M6 _ ht)))),cc (g7 n) _ (fun t=>(k t).val) (fun t=>(f t).val) (fun t ht=>Q6 Fin.val (m t (M6 _ (M0 _ ht))))];have f2:∑ x∈Se,(k x).val=d7 Se f:=L3 rfl fun t ht=>Q6 Fin.val (m t (M0 _ ht));rw[fm _ Se (f3 q true) (f3 q false) v2.1 v2.2 x1 (fun t=>(k t).val) (by rw[f2];simp[k,x1.symm,ds];omega),kq _ Se (fun t=>(k t).val) (fun t=>(f t).val) (fun t ht=>Q6 Fin.val (m t (M0 _ ht))),f2];simp only[k,↓reduceIte,x1.symm,mC,V0,ds,show re'.val+(sp.val+sm.val)+d7 Se f-d7 Se f=re'.val+(sp.val+sm.val) by omega];ring
          . intro z _ hy;rw[Q3];intro h;exact hy (L6 h.2.2.2.2.1.symm)
          . intro h;exact absurd (Y2 _) h
        . rw[L9,Q3]
          . intro h;apply x2;refine⟨h.2.2.2.1,h.2.2.1.2,by omega,by omega,h.1,h.2.1,h.2.2.1.1,by omega,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,by rw[<-h.2.2.2.2.2.2.2.2.2.2,Z6,Z6,Bool.xor_self,U0]⟩
          . intro z _;rw[Q3];intro h;exact x2 ⟨h.1,h.2.2.2.2.1▸h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2⟩
      . intro j hj;rw[L9];intro f _;rw[Q3];intro h;have w1:=t9 d.val e;have d0:=h.2.2.2.2.1;unfold r9 at d0;rw[X7 r6,V6 x1] at d0;simp only[↓reduceIte,x1.symm,c0.1,c0.2] at d0;have hmul:(n+1)*2<=j.val*l:=Nat.mul_le_mul hj w1;have hla:=la'.isLt;omega
    . intro j hj;rw[L9];intro sm _;rw[L9];intro f _;rw[Q3];intro h;have t2:=h.2.2.2.1;dsimp only[k5] at t2;rw[L7 o] at t2;simp only[↓reduceIte,q] at t2;have:=pp.isLt;omega
  . rw[Q8 o,ihe (by omega)]
    have s2:k3 n d.val (e+1)=k3 n d.val e:=by
     ext t;simp only[k3,L4,Y2,Q0];refine and_congr_right fun _=>exists_congr fun u'=>exists_congr fun e'=>and_congr_right fun a5=>?_;constructor
     . rintro (h|⟨hu',he'⟩)
       . exact inl h
       . refine inr ⟨hu',?_⟩;by_contra hge;have:=(k7 t).2;rw[<-a5,hu',show e'.val=e by omega] at this;exact o this
     . exact fun h=>h.imp id (fun⟨a,b⟩=>⟨a,by omega⟩)
    have hb:∀ k,o4 n i g d.val (e+1) k↔o4 n i g d.val e k:=fun k=>forall_congr' fun u'=>forall_congr' fun e'=>⟨fun h w=>h (w.imp id (fun⟨a,b⟩=>⟨a,by omega⟩)),fun h w hle'=>w.elim (fun h1=>h (inl h1) hle') fun⟨hu',he'⟩=>if hlt':e'.val<e then h (inr ⟨hu',hlt'⟩) hle' else False.elim (o (by dsimp only[l];rwa[<-hu',<-show e'.val=e by omega]))⟩;have k0:∀ k,k5 n g d (e+1) k=k5 n g d e k:=fun k=>(by dsimp only[k5];rw[Q8 o]);rw[s2];refine L3 rfl fun k _=>by simp only[hb,k0]
lemma ph (n d:ℕ) (a:ℕ->ℕ->ℤ) (c:c7 n->ℕ)
 (k i g:Y0) (u:ℕ) (hu:u<=n)
 (s:Fin (2*n+1)) (l:Fin (2*n+1)) (v:Y0):
 let Teven0:=fun x1 v2 x0=>z0 n a c (ak n d k i (u0 n a c g n)) n x1 ⟨0,by omega⟩ v2 x0
 z1 n a c Teven0 u s l v=∑ b∈u6 n (d3 n∪g7 n∪k3 n u 0),let y:=d7 (d3 n) b;let x:=d7 (g7 n) b
   let w:=l.val+d7 (k3 n u 0) b
   if(∀ q:Fin n,g6 n a c q (b (e4 q true)).val (b (e4 q false)).val=true)/\(∀ q:Fin n,j9 n a c q (b (f5 q true)).val (b (f5 q false)).val=true)/\o4 n a c u 0 b/\r9 (d3 n∪g7 n∪k3 n u 0) b=s.val/\n2 k i y=some x/\y+x+w=d/\y<=n+1/\x<=n+1/\w<=2*n/\xor g (l4 (d3 n∪g7 n∪k3 n u 0) b)=v
   then choose d w*f9 (d3 n) y (fun t=>(b t).val) *f9 (g7 n) x (fun t=>(b t).val)*z5 w (k3 n u 0) (fun t=>(b t).val)
   else 0:=by
 classical
 intro Teven0;induction u generalizing s l v with
 | zero=>
  have h2:k3 n 0 0=∅:=(by ext t;simp[k3]);rw[z1];dsimp only[Teven0];rw[pf n d a c k i g n Y3,qe,h2,union_empty];refine L3 rfl fun b _=>?_;have h6:(∀ q:Fin n,q.val<n->j9 n a c q (b (f5 q true)).val (b (f5 q false)).val=true)↔∀ q:Fin n,j9 n a c q (b (f5 q true)).val (b (f5 q false)).val=true:=forall_congr' fun q=>(by simp[q.isLt]);have h3:o4 n a c 0 0 b:=(by intro u' e' h;omega);dsimp only;simp only[d7,sum_empty,add_zero,zero_add,kp,mul_one,show l.val<=2*n by omega,Q0,h6,h3,bq _ _ _ rfl]
 | succ u ih=>
  have h1:u<n:=(by omega);rw[z1,L7 h1];set j:Fin n:=⟨u,h1⟩;unfold lv;dsimp only;rw[L3 rfl fun pp _=>pg n d a c k i g j (z1 n a c Teven0 u) (ih (by omega)) (2*n) Y3 s l v pp];rw[X9]
  have p:k3 n u (2*n)=k3 n (u+1) 0:=by
   ext t;simp only[k3,L4,Y2,Q0];refine and_congr_right fun _=>exists_congr fun u'=>exists_congr fun e'=>and_congr_right fun _=>by have:=e'.isLt;omega
  have r:∀ b,o4 n a c u (2*n) b↔o4 n a c (u+1) 0 b:=fun b=>forall_congr' fun u'=>forall_congr' fun e'=>by have:=e'.isLt;simp only[show (u'.val<u\/u'.val=u/\e'.val<2*n)↔(u'.val<u+1\/u'.val=u+1/\e'.val<0) by omega]
  rw[p];refine L3 rfl fun b _=>?_;dsimp only[j];simp_rw[r]
  have o:∀ e,o4 n a c (u+1) 0 b->k5 n c j e b≤n:=fun e h5=>by
   induction e with
   | zero=>simp[k5]
   | succ e' ih=>
    dsimp only[k5];by_cases m:d6 u e'<=2*n
    . rw[L7 m];have h0:e'<2*n:=by have h9:=lt_two_pow_self (n:=e'+1);unfold d6 at m;have h8:2^(e'+1)<=(2*u+1)*2^(e'+1):=Nat.le_mul_of_pos_left _ (by omega);omega
      have z:=h5 j ⟨e',h0⟩ (inl (by dsimp[j];omega)) m;dsimp only[o2] at z;rw[L7 m] at z;simp only[L0] at z;exact z.1
    . rw[Q8 m];exact ih
  by_cases f:(∀ q:Fin n,g6 n a c q (b (e4 q true)).val (b (e4 q false)).val=true)/\(∀ q:Fin n,j9 n a c q (b (f5 q true)).val (b (f5 q false)).val=true)/\o4 n a c (u+1) 0 b/\r9 (d3 n∪g7 n∪k3 n (u+1) 0) b=s.val/\n2 k i (d7 (d3 n) b)=some (d7 (g7 n) b)/\d7 (d3 n) b+d7 (g7 n) b+(l.val+d7 (k3 n (u+1) 0) b)=d/\d7 (d3 n) b<=n+1/\d7 (g7 n) b<=n+1/\l.val+d7 (k3 n (u+1) 0) b<=2*n/\xor g (l4 (d3 n∪g7 n∪k3 n (u+1) 0) b)=v
  . have h4:=o (2*n) f.2.2.1;rw[Q2 f,Q4 ⟨k5 n c j (2*n) b,by omega⟩]
    . dsimp only;rw[Q2 ⟨f.1,f.2.1,f.2.2.1,rfl,f.2.2.2⟩]
    . intro pp _ h7;rw[Q3];intro h;exact h7 (L6 h.2.2.2.1.symm)
    . intro h;exact absurd (Y2 _) h
  . rw[Q3 f,L9];intro pp _;rw[Q3];intro h;exact f ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2⟩
lemma iy {n b:ℕ} (hn:1<=n) (c2:b<=2*n)
 (o:ℕ->ℕ->ℤ) (d:c7 n->ℕ)
 (m k x:Y0) (y:Fin (2*n+1))
 (v0:(∑ t:c7 n,d t*c3 t)+y.val=2*n):
 ad n b o d m k x y=(univ.filter (fun c:Fin b->c7 n=>(∀ j:Fin b,l5 (d5 m c j.val) (c j)=true)/\d5 m c b=k/\(∑ j:Fin b,c3 (c j))=y.val/\xor x (decide ((univ.filter (fun j=>c9 (c j)=false)).card %2=1))=false/\let tot (t:c7 n):=d t+(univ.filter (fun j=>c j=t)).card
   ∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (y8 tot) (y9 tot) l r=o l r)).card:=by
 classical
 unfold ad;rw[ph n b o d m k x n Y3,qf];have v2:d3 n∪g7 n∪br n=univ:=(by ext t;simp only[d3,g7,br,X4,L4,Y2,Q0,iff_true];have:=t.1.isLt;omega);have v1:u6 n (d3 n∪g7 n∪br n)=univ:=(by rw[v2];ext sf;simp[u6]);rw[v1]
 let S:=univ.filter (fun c:Fin b->c7 n=>(∀ j:Fin b,l5 (d5 m c j.val) (c j)=true)/\d5 m c b=k/\(∑ j:Fin b,c3 (c j))=y.val/\xor x (decide ((univ.filter (fun j=>c9 (c j)=false)).card %2=1))=false/\let tot (t:c7 n):=d t+(univ.filter (fun j=>c j=t)).card
  ∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (y8 tot) (y9 tot) l r=o l r)
 let cntOf (c:Fin b->c7 n):c7 n->Fin (2*n+1):=fun t=>⟨(univ.filter (fun j:Fin b=>c j=t)).card,by
   have:=card_filter_le (univ:V7 (Fin b)) (fun j=>c j=t);simp at this;omega⟩
 rw[card_eq_sum_card_fiberwise (f:=cntOf) (s:=S) (t:=univ) (fun _ _=>Y2 _)];refine L3 rfl fun sf _=>?_
 have h7:∀ c:Fin b->c7 n,cntOf c=sf->(∑ j:Fin b,c3 (c j))=r9 univ sf/\(univ.filter (fun j=>c9 (c j)=false)).card=∑ t∈univ.filter (fun t:c7 n=>c9 t=false),(sf t).val:=fun c v=>by
  have hc:∀ t:c7 n,(univ.filter (fun j:Fin b=>c j=t)).card=(sf t).val:=fun t=>Q6 (fun f=>(f t).val) v;constructor
  . rw[<-Finset.sum_fiberwise_of_maps_to (g:=c) (s:=univ) (t:=univ) (fun _ _=>Y2 _)];unfold r9;refine L3 rfl fun t _=>?_;rw[L3 rfl (fun j hj=>by rw[(L4.mp hj).2]),sum_const,smul_eq_mul,hc t]
  . rw[card_eq_sum_card_fiberwise (f:=c) (s:=univ.filter (fun j=>c9 (c j)=false)) (t:=univ.filter (fun t=>c9 t=false)) (fun j hj=>by simp at hj ⊢;exact hj)];refine L3 rfl fun t ht=>?_;rw[<-hc t];congr 1;ext j;simp only[L4,Y2,Q0] at ht ⊢;exact⟨fun h=>h.2,fun h=>⟨h▸ht,h⟩⟩
 have y2:S.filter (fun c=>cntOf c=sf)=if r9 univ sf=y.val/\xor x (l4 univ sf)=false/\(∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (y8 (fun t=>d t+(sf t).val)) (y9 (fun t=>d t+(sf t).val)) l r=o l r) then univ.filter (fun c:Fin b->c7 n=>(∀ j:Fin b,l5 (d5 m c j.val) (c j)=true)/\d5 m c b=k/\∀ t:c7 n,(univ.filter (fun i=>c i=t)).card=(sf t).val)
  else ∅:=by
  ext c;split_ifs with p
  . simp only[S,L4,Y2,Q0];refine⟨fun⟨⟨h1,h2,_,_,_⟩,v⟩=>⟨h1,h2,fun t=>Q6 (fun f=>(f t).val) v⟩,fun⟨h1,h2,v⟩=>?_⟩;have hcnt':cntOf c=sf:=funext fun t=>L6 (v t);obtain⟨hl,hp⟩:=h7 c hcnt';have h9:(fun t=>d t+(univ.filter (fun j=>c j=t)).card)=fun t=>d t+(sf t).val:=funext fun t=>(by rw[v t]);exact⟨⟨h1,h2,hl.trans p.1,by rw[hp];exact p.2.1,by rw[h9];exact p.2.2⟩,hcnt'⟩
  . simp only[S,L4,Y2,Q0,notMem_empty,iff_false];rintro⟨⟨_,_,h3,h4,h5⟩,v⟩;obtain⟨hl,hp⟩:=h7 c v;have h9:(fun t=>d t+(univ.filter (fun j=>c j=t)).card)=fun t=>d t+(sf t).val:=funext fun t=>(by rw[show (univ.filter (fun j=>c j=t)).card=(sf t).val from Q6 (fun f=>(f t).val) v]);rw[h9] at h5;rw[hp] at h4;exact p ⟨hl.symm.trans h3,h4,h5⟩
 rw[y2,v2];by_cases h6:r9 univ sf=y.val
 . have a1:∀ t:c7 n,d t+(sf t).val≤2*n/\(t.1.val=2->d t+(sf t).val≤n):=fun t=>by have x0:∑ a:c7 n,(d a+(sf a).val)*c3 a=2*n:=(by simp_rw[Nat.add_mul,Z4];change (∑ a:c7 n,d a*c3 a)+r9 univ sf=2*n;rw[h6,v0]);have y1:=single_le_sum (f:=fun a=>(d a+(sf a).val)*c3 a) (fun _ _=>V5 _) (Y2 t);rw[x0] at y1;have d2:=(k7 t).1;refine⟨by nlinarith,fun b0=>by have h2:2<=c3 t:=(by unfold c3;rw[b0];simp only[↓reduceIte];omega);nlinarith⟩
   have z:=fe hn o d (fun t=>(sf t).val) a1;dsimp only at z
   have a0:(∀ u_idx:Fin n,∀ e:Fin (2*n),∀ hle:d6 u_idx.val e.val≤2*n,let q:=l9 u_idx.val e.val hle
    let pp:=if he0:e.val=0 then 0 else d (f3 (k4 u_idx.val e.val he0 hle) true)+(sf (f3 (k4 u_idx.val e.val he0 hle) true)).val
    o2 n o d u_idx e pp (sf (f3 q true)).val (sf (f3 q false)).val=true)↔
    o4 n o d n 0 sf:=
    forall_congr' fun u'=>forall_congr' fun e'=>by simp[u'.isLt]
   rw[a0] at z
   have h8:∀ x2 x1 a3,n2 m k x2=some x1->x2+x1+a3=b->x2<=n+1/\x1<=n+1/\a3<=2*n:=fun x2 x1 a3 b3 h9=>by
    cases m<;>cases k<;>simp[n2] at b3<;>omega
   by_cases p:xor x (l4 univ sf)=false/\(∀ l∈Icc 1 (2*n),∀ r∈(c4 l).toFinset,f8 (y8 (fun t=>d t+(sf t).val)) (y9 (fun t=>d t+(sf t).val)) l r=o l r)
   . conv_rhs=>rw[Q2 ⟨h6,p.1,p.2⟩,lu m k (fun t=>(sf t).val)]
     obtain⟨h0,h1,b5⟩:=z.mp p.2;simp only[zero_add,bq _ _ _ rfl];by_cases w:d7 (d3 n) sf+d7 (g7 n) sf+d7 (br n) sf=b/\n2 m k (d7 (d3 n) sf)=some (d7 (g7 n) sf)
     . obtain⟨b9,b6,b8⟩:=h8 _ _ _ w.2 w.1;rw[Q2 ⟨h0,h1,b5,h6,w.2,w.1,b9,b6,b8,p.1⟩];dsimp only[d7] at w ⊢;rw[Q2 w,bq _ _ _ rfl]
     . rw[Q3 (by intro h;exact w ⟨h.2.2.2.2.2.1,h.2.2.2.2.1⟩)];dsimp only[d7] at w;rw[Q3 w]
   . rw[Q3 (by intro h;exact p ⟨h.2.2.2.2.2.2.2.2.2,z.mpr ⟨h.1,h.2.1,h.2.2.1⟩⟩),Q3 (by intro h;exact p ⟨h.2.1,h.2.2⟩),card_empty]
 . rw[Q3 (by intro h;exact h6 h.2.2.2.1),Q3 (by intro h;exact h6 h.1),card_empty]
end DPExactness2
section DPBuild
noncomputable def g3 (n:ℕ)(x:F0 (N0 n))(l r:ℕ):ℤ:=if l8 n x then s7 n x l r else (4*n+5:ℤ)
noncomputable def ec (n l r:ℕ)(z:ℤ):d4 (N0 n):=if h:-(2*n:ℤ)<=z/\z<=(2*n:ℤ) then an (l8 n) (v3 n l r ⟨(z+2*n).toNat,by omega⟩)
 else fun _=>false
lemma al (n l r:ℕ) (j:1<=l) (k:l<=2*n) (h:r∈(c4 l).toFinset)
 (z:ℤ) (m:z<(4*n+5:ℤ)) (x:F0 (N0 n)):
 decide (g3 n x l r=z)=ec n l r z x:=by
 unfold g3 ec;by_cases a:l8 n x=true
 . rw[Q2 a]
   split_ifs with g
   . have f:t0 n ⟨(z+2*n).toNat,by omega⟩=z:=(by unfold t0;dsimp only;omega);have i:decide (s7 n x l r=z)=decide (s7 n x l r=t0 n ⟨(z+2*n).toNat,by omega⟩):=(by rw[f]);rw[i,az];simp[an,a]
   . apply L5;simp only[L0,J5,iff_false];intro b;have d:∀ l':Fin (2*n),∀ r'∈(c4 (l'.val+1)).toFinset,∃ v:Fin (4*n+1),v3 n (l'.val+1) r' v x=true:=(by unfold l8 cz at a;simp only[K8,L0] at a;exact a.1.2);unfold s7 at b
     split_ifs at b with c
     . unfold t0 at b;have:=(Classical.choose c).isLt;omega
     . exact c (by simpa[show l-1+1=l by omega] using d ⟨l-1,by omega⟩ r (by simpa[show l-1+1=l by omega] using h))
 . have e:l8 n x=false:=Bool.eq_false_iff.mpr a;rw[Q3 a]
   split_ifs with g
   . simp only[an,e,Bool.false_and,M7];omega
   . simp only[M7];omega
def v5 (n:ℕ):Set (d4 (N0 n)):=
 {f|∃ l:Fin (2*n),∃ r∈(c4 (l.val+1)).toFinset,∃ v:Fin (4*n+1),f=an (l8 n) (v3 n (l.val+1) r v)}
lemma qg (n:ℕ){A:Set (d4 (N0 n))}(b:da n⊆A):Build A (v5 n) (2*n*3*(4*n+1)):=by
 let Bcell (p:Fin (2*n)×Fin 3×Fin (4*n+1)):Set (d4 (N0 n)):=let l:=p.1.val+1
  if p.2.1.val<(c4 l).length then {an (l8 n) (v3 n l ((c4 l).getD p.2.1.val 0) p.2.2)} else ∅
 have H:=p7 (A:=A) Bcell 1 (fun⟨l,r3,v⟩=>by
  dsimp only[Bcell];split_ifs with a
  . exact t7 (b (inl (inl rfl))) (b (inr ⟨l,_,K3.mpr (by rw[getD_eq_getElem _ _ a];exact getElem_mem a),v,rfl⟩))
  . exact d9 (s6 (by simp)) Y3 Y3 (by omega))
 refine d9 H Y3 ?_ (by simp[Z3]);rintro _ ⟨l,r,c,v,rfl⟩;rw[K3] at c;obtain⟨i,f⟩:=List.mem_iff_get.mp c;have d:i.val<3:=by have e:=i.isLt;have g:(c4 (l.val+1)).length<=3:=(by unfold c4;split_ifs<;>simp);omega
 refine⟨(l,⟨i.val,d⟩,v),Y2 _,?_⟩;dsimp only[Bcell];rw[Q2 i.isLt,getD_eq_getElem _ _ i.isLt,<-get_eq_getElem,f];rfl
lemma ic {n l r:ℕ} {A:Set (d4 (N0 n))} (a:v5 n⊆A) (b:(fun _=>false)∈A)
 (d:1<=l) (f:l<=2*n) (c:r∈(c4 l).toFinset) (z:ℤ):
 ec n l r z∈A:=by
 unfold ec;split_ifs with e
 . exact a ⟨⟨l-1,by omega⟩,r,by simpa[show l-1+1=l by omega] using c,⟨(z+2*n).toNat,by omega⟩,by simp[show l-1+1=l by omega]⟩
 . exact b
lemma ra {N:ℕ}{A:Set (d4 N)}{a b c:d4 N}(e:a∈A)(f:b∈A)(d:c∈A):Build A {fun x=>a x && b x && c x} 2:=i7 (t7 e f) (t7 (inr rfl) (inl d))
lemma qh {N:ℕ}{A:Set (d4 N)}{a b c d:d4 N}(f:a∈A)(g:b∈A)(e:c∈A)(h:d∈A):Build A {fun x=>a x && b x && c x && d x} 3:=i7 (ra f g e) (t7 (inr rfl) (inl h))
lemma nq (n:ℕ) (b:Y0) {A:Set (d4 (N0 n))}
 (z:v5 n⊆A) (y:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (a:F0 (N0 n)->c7 n->ℕ)
 (k:∀ x t,a x t≤2*n)
 (m:∀ t (u:Fin (2*n+1)),(fun x=>decide (a x t=u.val))∈A)
 (q:Fin n) (f i:Fin (n+2)):
 Build A {fun x=>if b then j9 n (g3 n x) (a x) q f.val i.val else g6 n (g3 n x) (a x) q f.val i.val}
  (4*((2*n+1)*(2*n+1))):=by
 set l:=2*q.val+1;have h0:1<=l:=(by dsimp[l];omega);have h6:l<=2*n:=(by dsimp[l];have:=q.isLt;omega);set r:=if b then q.val else q.val+1;set s:c7 n:=if b then f5 q true else e4 q true;set v:c7 n:=if b then f5 q false else e4 q false
 have j:r∈(c4 l).toFinset:=by
  rw[K3];unfold c4;cases b<;>simp[l,r,show (2*q.val+1) %2=1 by omega,show (2*q.val+1)/2=q.val by omega]
 have g:2*l<=2*n->2*r∈(c4 (2*l)).toFinset:=fun _=>by
  rw[K3];unfold c4;cases b<;>simp[l,r,show ¬ (2*(2*q.val+1)) %2=1 by omega,show ¬ (2*(2*q.val+1)) %4=0 by omega]<;>omega
 let term (p:Fin (2*n+1)×Fin (2*n+1)):d4 (N0 n):=let mp:=p.1.val+f.val;let mm:=p.2.val+i.val
  if h:mp<=2*n/\mm<=2*n then fun x=>decide (a x s=p.1.val) && decide (a x v=p.2.val) &&
    (if 2*l<=2*n then ec n (2*l) (2*r) (mp:ℤ) x else true) &&
    ec n l r ((mm:ℤ)-(mp:ℤ)) x
  else fun _=>false
 have H1:Build A (R0 (fun c:Fin ((2*n+1)*(2*n+1))=>term (finProdFinEquiv.symm c)))
  (((2*n+1)*(2*n+1))*3):=
  au (fun c=>term (finProdFinEquiv.symm c)) 3 (fun c=>by
   rcases finProdFinEquiv.symm c with ⟨up,um⟩;dsimp only[term]
   by_cases h:up.val+f.val<=2*n/\um.val+i.val<=2*n
   . rw[L7 h]
     have h3:(fun x=>if 2*l<=2*n then ec n (2*l) (2*r) ((up.val+f.val:ℕ):ℤ) x else true)∈A:=by
      by_cases d:2*l<=2*n
      . simp only[d,↓reduceIte];exact ic z y (by omega) d (g d) _
      . simp only[d,↓reduceIte];exact ht
     have h4:ec n l r (((um.val+i.val:ℕ):ℤ)-((up.val+f.val:ℕ):ℤ))∈A:=ic z y (by omega) (by omega) j _;exact qh (m s up) (m v um) h3 h4
   . rw[Q8 h];exact d9 (s6 (Q1 y)) Y3 Y3 (by omega))
 have H2:=w3 (A:=A∪R0 _) (fun c:Fin ((2*n+1)*(2*n+1))=>term (finProdFinEquiv.symm c))
  (inl y) (fun c=>inr ⟨c,rfl⟩)
 have he:(fun x=>decide (∃ c:Fin ((2*n+1)*(2*n+1)),term (finProdFinEquiv.symm c) x=true))=fun x=>if b then j9 n (g3 n x) (a x) q f.val i.val
   else g6 n (g3 n x) (a x) q f.val i.val:=by
  funext x;apply L5;simp only[L0]
  have o:(if b then j9 n (g3 n x) (a x) q f.val i.val
   else g6 n (g3 n x) (a x) q f.val i.val)=true↔
   a x s+f.val<=2*n/\a x v+i.val<=2*n ∧
   (2*l<=2*n->g3 n x (2*l) (2*r)=((a x s+f.val:ℕ):ℤ)) ∧
   g3 n x l r=((a x v+i.val:ℕ):ℤ)-((a x s+f.val:ℕ):ℤ):=by
   cases b<;>simp only[g6,j9,l,r,s,v,↓reduceIte,J5,L0]
  rw[o];constructor
  . rintro⟨c,e⟩
    rcases hpair:finProdFinEquiv.symm c with ⟨up,um⟩;rw[hpair] at e
    dsimp only[term] at e;by_cases h:up.val+f.val<=2*n/\um.val+i.val<=2*n
    . rw[L7 h] at e;simp only[K8,L0] at e;obtain⟨⟨⟨h9,v0⟩,d⟩,h5⟩:=e;rw[h9,v0];refine⟨h.1,h.2,fun w=>?_,?_⟩
      . rw[Q2 w,<-al n (2*l) (2*r) (by omega) w (g w) _ (by have:=h.1;omega) x,L0] at d;exact d
      . rw[<-al n l r h0 h6 j _ (by have:=h.1;have:=h.2;omega) x,L0] at h5;exact h5
    . rw[Q8 h] at e;simp at e
  . rintro⟨h1,w,h3,h4⟩;refine⟨finProdFinEquiv (⟨a x s,by have:=k x s;omega⟩,⟨a x v,by have:=k x v;omega⟩),?_⟩;rw[M5];dsimp only[term];rw[L7 ⟨h1,w⟩];simp only[K8,L0,Q0];refine⟨?_,?_⟩
    . split_ifs with d
      . rw[<-al n (2*l) (2*r) (by omega) d (g d) _ (by omega) x,L0];exact h3 d
      . rfl
    . rw[<-al n l r h0 h6 j _ (by omega) x,L0];exact h4
 rw[he] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
lemma pi (n:ℕ) {A:Set (d4 (N0 n))}
 (z:v5 n⊆A) (y:(fun _=>false)∈A)
 (a:F0 (N0 n)->c7 n->ℕ)
 (o:∀ x t,a x t≤2*n)
 (j:∀ t (u:Fin (2*n+1)),(fun x=>decide (a x t=u.val))∈A)
 (b:Fin n) (e:Fin (2*n)) (m:d6 b.val e.val<=2*n)
 (c i p h8:Fin (n+1)):
 let q:=l9 b.val e.val m
 Build A {fun x=>decide (a x (f3 q true)+i.val=h8.val/\o2 n (g3 n x) (a x) b e c.val i.val p.val=true)}
  (3*(2*n+1)):=by
 intro q;set l:=d6 b.val e.val;have h7:=t9 b.val e.val;have s:1<=l:=by dsimp only[l];omega
 have g:l/2∈(c4 l).toFinset:=by
  rw[K3];unfold c4;have h0:l %2=0:=by have h6:2 ∣ l:=⟨(2*b.val+1)*2^e.val,by unfold l d6;rw[U4];ring⟩;omega
  split_ifs<;>simp[h0]
 let term (f:Fin (2*n+1)):d4 (N0 n):=if h:i.val<=h8.val/\f.val+p.val<=2*n then fun x=>decide (a x (f3 q true)=h8.val-i.val) &&
    decide (a x (f3 q false)=f.val) &&
    ec n l (l/2) (((f.val+p.val:ℕ):ℤ)-(h8.val:ℤ)+(c.val:ℤ)) x
  else fun _=>false
 have H1:Build A (R0 term) ((2*n+1)*2):=au term 2 (fun f=>by
   dsimp only[term];by_cases h:i.val<=h8.val/\f.val+p.val<=2*n
   . rw[L7 h];exact ra (j (f3 q true) ⟨h8.val-i.val,by omega⟩) (j (f3 q false) f)
      (ic z y (by omega) m g _)
   . rw[Q8 h];exact d9 (s6 (Q1 y)) Y3 Y3 (by omega))
 have H2:=w3 (A:=A∪R0 term) term (inl y) (fun f=>inr ⟨f,rfl⟩)
 have he:(fun x=>decide (∃ f:Fin (2*n+1),term f x=true))=fun x=>decide (a x (f3 q true)+i.val=h8.val/\o2 n (g3 n x) (a x) b e c.val i.val p.val=true):=by
  funext x;apply L5;simp only[L0]
  dsimp only[o2];rw[L7 m];simp only[L0];have h2:=h8.isLt;have h1:=c.isLt;constructor
  . rintro⟨f,k⟩;dsimp only[term] at k;by_cases h:i.val<=h8.val/\f.val+p.val<=2*n
    . rw[L7 h] at k;simp only[K8,L0] at k;obtain⟨⟨h5,r⟩,v⟩:=k;have d:a x (f3 q true)+i.val=h8.val:=(by omega);rw[<-al n l (l/2) s m g _ (by have:=h.2;omega) x,L0] at v;dsimp only[q] at d r ⊢;have:=h.2;exact⟨d,by omega,by omega,by rw[d,r];exact v⟩
    . rw[Q8 h] at k;simp at k
  . rintro⟨d,_,w,hc⟩;refine⟨⟨a x (f3 q false),by have:=o x (f3 q false);omega⟩,?_⟩;dsimp only[term];rw[L7 ⟨by dsimp only[q] at d ⊢;omega,w⟩];simp only[K8,L0,and_true];refine⟨by dsimp only[q] at d ⊢;omega,?_⟩;rw[<-al n l (l/2) s m g _ (by dsimp only[q] at w ⊢;omega) x,L0];dsimp only[q] at d ⊢;rw[<-d];exact hc
 rw[he] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
def nr {n:ℕ}(T:F0 (N0 n)->Fin (2*n+1)->Fin (n+2)->Y0->ℕ):Set (d4 (N0 n)):=m0 (univ:V7 (Fin (2*n+1)×Fin (n+2)×Y0))
  (fun p=>R0 (a9 (4*n) (fun x=>T x p.1 p.2.1 p.2.2)))
def jw {n:ℕ}(T:F0 (N0 n)->Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ):Set (d4 (N0 n)):=m0 (univ:V7 (Fin (2*n+1)×Fin (n+2)×Fin (2*n+1)×Y0))
  (fun p=>R0 (a9 (4*n) (fun x=>T x p.1 p.2.1 p.2.2.1 p.2.2.2)))
def lw {n:ℕ}(T:F0 (N0 n)->Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ):Set (d4 (N0 n)):=m0 (univ:V7 (Fin (2*n+1)×Fin (2*n+1)×Y0))
  (fun p=>R0 (a9 (4*n) (fun x=>T x p.1 p.2.1 p.2.2)))
def qt {n:ℕ}(T:F0 (N0 n)->Fin (2*n+1)->Fin (2*n+1)->Y0->Fin (n+1)->ℕ):Set (d4 (N0 n)):=m0 (univ:V7 (Fin (2*n+1)×Fin (2*n+1)×Y0×Fin (n+1)))
  (fun p=>R0 (a9 (4*n) (fun x=>T x p.1 p.2.1 p.2.2.1 p.2.2.2)))
def ed (n:ℕ):ℕ:=(n+2)*(n+2)*(4*((2*n+1)*(2*n+1))) +(2*n+1)*(n+2)*2*((n+2)*(n+2)*((4*n)*(9*(4*n))+10*(4*n)))
def gi (n:ℕ):ℕ:=6+(2*n+1)*(n+2)*(2*n+1)*2*((n+2)*4+(n+2)*((4*n)*(9*(4*n))+10*(4*n)))
def ck (n:ℕ):ℕ:=(n+2)*(n+2)*(4*((2*n+1)*(2*n+1))) +(2*n+1)*(n+2)*(2*n+1)*2*((n+2)*(n+2)*((4*n)*(9*(4*n))+10*(4*n)))
def bt (n:ℕ):ℕ:=(n+1)*(n+1)*(n+1)*(n+1)*(3*(2*n+1)) +(2*n+1)*(2*n+1)*2*(n+1)*((n+1)*(n+1)*(n+1)*((4*n)*(9*(4*n))+10*(4*n)))
def bu (n:ℕ):ℕ:=2*n*bt n+(2*n+1)*(2*n+1)*2*((n+1)*(9*(4*n)))
def u1 (n:ℕ):ℕ:=(2*n+1)*(n+2)*2*(4*n+1)+n*ed n+gi n +n*ck n+n*bu n+(2*n+1)*(10*(4*n))
lemma qn (n:ℕ) {A:Set (d4 (N0 n))}
 (v:v5 n⊆A) (f:(fun _=>false)∈A) (g:(fun _=>true)∈A)
 (b:F0 (N0 n)->c7 n->ℕ)
 (d:∀ x t,b x t≤2*n)
 (e:∀ t (u:Fin (2*n+1)),(fun x=>decide (b x t=u.val))∈A)
 (a:d4 (N0 n)) (r:a∈A):
 Build A (nr (fun x=>u0 n (g3 n x) (b x) (a x) n))
  ((2*n+1)*(n+2)*2*(4*n+1)+n*ed n):=by
 let O (k:ℕ):=nr (fun x=>u0 n (g3 n x) (b x) (a x) k)
 have H0:Build A (O 0) ((2*n+1)*(n+2)*2*(4*n+1)):=by
  have H:=p7 (A:=A) (fun p:Fin (2*n+1)×Fin (n+2)×Y0=>R0 (a9 (4*n) (fun x=>u0 n (g3 n x) (b x) (a x) 0 p.1 p.2.1 p.2.2)))
   (4*n+1) (fun⟨la,so0,np⟩=>by
    dsimp only[u0];by_cases s:la.val=0/\so0.val=0
    . have Hp:Build A {fun x=>decide (np=a x)} 1:=by
       cases np
       . have c:(fun x=>decide (false=a x))=nt a:=by funext x;unfold nt;cases a x<;>rfl
         rw[c];exact ae r
       . have c:(fun x=>decide (true=a x))=a:=by funext x;cases a x<;>rfl
         rw[c];exact d9 (s6 (Q1 r)) Y3 Y3 (by omega)
      have Hg:=ig (A:=A∪{fun x=>decide (np=a x)}) (m:=4*n) (p:=fun x=>decide (np=a x))
       (F:=fun _=>1) (inr rfl) (fun j=>by
        change (fun _=>(1:ℕ).testBit j.val)∈_;cases (1:ℕ).testBit j.val;exact inl f;exact inl g)
      have c:(fun x=>if decide (np=a x) then 1 else 0)=fun x=>if la.val=0/\so0.val=0/\np=a x then 1 else 0:=(by funext x;simp[s]);rw[c] at Hg;exact d9 (i7 Hp Hg) Y3 Y3 (by omega)
    . have c:(fun x=>if la.val=0/\so0.val=0/\np=a x then 1 else 0)=fun _=>0:=by funext x;rw[Q3];intro h;exact s ⟨h.1,h.2.1⟩
      rw[c];exact d9 (my (m:=4*n) 0 f g) Y3 Y3 (by omega))
  exact d9 H Y3 Y3 (by simp[Z3])
 refine ew O H0 fun k l=>?_;set q:Fin n:=⟨k,l⟩;let B:=A∪O k;let okSig (p:Fin (n+2)×Fin (n+2)):d4 (N0 n):=fun x=>g6 n (g3 n x) (b x) q p.1.val p.2.val;have Hok:Build B (R0 okSig) ((n+2)*(n+2)*(4*((2*n+1)*(2*n+1)))):=(by have H:=ke (A:=B) okSig (4*((2*n+1)*(2*n+1))) (fun⟨sp,sm⟩=>nq n false (v.trans M8) (inl f) (inl g) b d (fun t u=>inl (e t u)) q sp sm);simpa only[J3,Q9] using H);let C:=B∪R0 okSig
 have Hcells:Build C (O (k+1)) ((2*n+1)*(n+2)*2*((n+2)*(n+2)*((4*n)*(9*(4*n))+10*(4*n)))):=by
  have H:=p7 (A:=C) (fun p:Fin (2*n+1)×Fin (n+2)×Y0=>R0 (a9 (4*n) (fun x=>u0 n (g3 n x) (b x) (a x) (k+1) p.1 p.2.1 p.2.2)))
   ((n+2)*(n+2)*((4*n)*(9*(4*n))+10*(4*n))) (fun⟨la',so0',np'⟩=>by
    let on (p:Fin (n+2)×Fin (n+2)):d4 (N0 n):=if p.1.val+p.2.val<=so0'.val/\(2*q.val+1)*(p.1.val+p.2.val)<=la'.val then okSig p else fun _=>false;let mult (p:Fin (n+2)×Fin (n+2)):ℕ:=choose (so0'.val-(p.1.val+p.2.val)+p.1.val) p.1.val*choose so0'.val p.2.val
    let F (p:Fin (n+2)×Fin (n+2)) (x:F0 (N0 n)):ℕ:=if h:p.1.val+p.2.val<=so0'.val/\(2*q.val+1)*(p.1.val+p.2.val)<=la'.val then u0 n (g3 n x) (b x) (a x) k ⟨la'.val-(2*q.val+1)*(p.1.val+p.2.val),by omega⟩
       ⟨so0'.val-(p.1.val+p.2.val),by omega⟩ (xor np' (decide (p.2.val %2=1)))
     else 0
    have HS:=bi (w:=4*n) (A:=C) on mult F (inl (inl f)) (inl (inl g))
     (fun p=>by dsimp only[on];split_ifs;exact inr ⟨p,rfl⟩;exact inl (inl f))
     (fun p j=>by dsimp only[F];split_ifs with h;exact inl (inr (q3 (i:=(_,_,_)) ⟨j,rfl⟩));have z:a9 (4*n) (fun _:F0 (N0 n)=>0) j=fun _=>false:=funext fun _=>zero_testBit j.val;rw[z];exact inl (inl f))
    have c:(fun x=>∑ p:Fin (n+2)×Fin (n+2),if on p x then mult p*F p x else 0)=fun x=>u0 n (g3 n x) (b x) (a x) (k+1) la' so0' np':=by
     funext x;rw[u0,L7 l];unfold od;rw[sum_prod_type]
     refine L3 rfl fun sp _=>L3 rfl fun sm _=>?_;dsimp only[on,mult,F,okSig,q];by_cases o:sp.val+sm.val<=so0'.val/\(2*k+1)*(sp.val+sm.val)<=la'.val
     . simp only[o,↓reduceIte,↓reduceDIte];by_cases y:g6 n (g3 n x) (b x) ⟨k,l⟩ sp.val sm.val=true<;>simp[o,y]
     . simp[o,show ¬ (g6 n (g3 n x) (b x) ⟨k,l⟩ sp.val sm.val=true/\sp.val+sm.val<=so0'.val/\(2*k+1)*(sp.val+sm.val)<=la'.val) from fun h=>o ⟨h.2.1,h.2.2⟩]
    rw[c] at HS;simpa only[J3,Q9] using HS)
  exact d9 H Y3 Y3 (by simp[Z3])
 exact d9 (i7 Hok Hcells) Y3 Y3 (by unfold ed;omega)
lemma qi (n c:ℕ) {A:Set (d4 (N0 n))}
 (hf:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (b a:d4 (N0 n)) (k:b∈A) (h:a∈A)
 (T1:F0 (N0 n)->Fin (2*n+1)->Fin (n+2)->Y0->ℕ)
 (z:nr T1⊆A):
 Build A (jw (fun x=>ak n c (b x) (a x) (T1 x))) (gi n):=by
 have Hn:=q6 (ae k) (ae h);let A1:=A∪({nt b}∪{nt a});let q:=an (nt b) (nt a);let r:=an (nt b) a;let s:=an b (nt a);let o:=an b a
 have Hm:=q6 (q6 (t7 (A:=A1) (inr (inl rfl)) (inr (inr rfl)))
  (t7 (A:=A1) (inr (inl rfl)) (inl h)))
  (q6 (t7 (A:=A1) (inl k) (inr (inr rfl))) (t7 (A:=A1) (inl k) (inl h)))
 let A2:=A1∪(({q}∪{r})∪({s}∪{o}))
 have u:∀ l m:Y0,(fun x=>decide (b x=l/\a x=m))∈A2:=fun l m=>by
  cases l<;>cases m
  . have:(fun x=>decide (b x=false/\a x=false))=q:=by funext x;dsimp only[q,an,nt];cases b x<;>cases a x<;>rfl
    rw[this];exact inr (inl (inl rfl))
  . have:(fun x=>decide (b x=false/\a x=true))=r:=by funext x;dsimp only[r,an,nt];cases b x<;>cases a x<;>rfl
    rw[this];exact inr (inl (inr rfl))
  . have:(fun x=>decide (b x=true/\a x=false))=s:=by funext x;dsimp only[s,an,nt];cases b x<;>cases a x<;>rfl
    rw[this];exact inr (inr (inl rfl))
  . have:(fun x=>decide (b x=true/\a x=true))=o:=by funext x;dsimp only[o,an,nt];cases b x<;>cases a x<;>rfl
    rw[this];exact inr (inr (inr rfl))
 have g:(fun _=>false)∈A2:=inl (inl hf);have v:(fun _=>true)∈A2:=inl (inl ht)
 have Hcells:=p7 (A:=A2) (fun p:Fin (2*n+1)×Fin (n+2)×Fin (2*n+1)×Y0=>R0 (a9 (4*n) (fun x=>ak n c (b x) (a x) (T1 x) p.1 p.2.1 p.2.2.1 p.2.2.2)))
  ((n+2)*4+(n+2)*((4*n)*(9*(4*n))+10*(4*n))) (fun⟨la,ro1,tse,np⟩=>by
   let on (d:Fin (n+2)):d4 (N0 n):=fun x=>decide (n2 (b x) (a x) d.val=some ro1.val/\d.val+ro1.val+tse.val=c)
   have Hon:Build A2 (R0 on) ((n+2)*4):=au on 4 (fun d=>by
     let tbl (f:Fin 4):d4 (N0 n):=let l:Y0:=decide (f.val/2=1);let m:Y0:=decide (f.val %2=1)
      if n2 l m d.val=some ro1.val/\d.val+ro1.val+tse.val=c
      then fun x=>decide (b x=l/\a x=m) else fun _=>false
     have Hany:=w3 (A:=A2) tbl g (fun f=>by dsimp only[tbl];split_ifs;exact u _ _;exact g)
     have y:(fun x=>decide (∃ f:Fin 4,tbl f x=true))=on d:=by
      funext x;apply L5;simp only[on,L0]
      constructor
      . rintro⟨f,e⟩;dsimp only[tbl] at e;by_cases t:n2 (decide (f.val/2=1)) (decide (f.val %2=1)) d.val=some ro1.val/\d.val+ro1.val+tse.val=c
        . rw[Q2 t] at e;simp only[L0] at e;rw[e.1,e.2];exact t
        . rw[Q3 t] at e;simp at e
      . intro t;refine⟨⟨(b x).toNat*2+(a x).toNat,by cases b x<;>cases a x<;>decide⟩,?_⟩;dsimp only[tbl];cases hcm':b x<;>cases hce':a x<;>simp_all
     rw[y] at Hany;exact Hany)
   have Hsum:=bi (w:=4*n) (A:=A2∪R0 on) on (fun _=>choose c tse.val)
    (fun d x=>T1 x la d np) (inl g) (inl v) (fun d=>inr ⟨d,rfl⟩)
    (fun d j=>inl (inl (inl (z (q3 (i:=(la,d,np)) ⟨j,rfl⟩)))))
   have y:(fun x=>∑ d:Fin (n+2),if on d x then choose c tse.val*T1 x la d np else 0)=fun x=>ak n c (b x) (a x) (T1 x) la ro1 tse np:=by
    funext x;unfold ak;refine L3 rfl fun d _=>by simp[on]
   rw[y] at Hsum;simpa only[Q9] using i7 Hon Hsum)
 exact d9 (i7 Hn (i7 Hm Hcells)) Y3 Y3 (le_of_eq (by unfold gi;simp only[J3,Q9,card_bool];ring))
lemma qo (n:ℕ) {A:Set (d4 (N0 n))}
 (m:v5 n⊆A) (f:(fun _=>false)∈A) (l:(fun _=>true)∈A)
 (a:F0 (N0 n)->c7 n->ℕ)
 (b:∀ x t,a x t≤2*n)
 (c:∀ t (u:Fin (2*n+1)),(fun x=>decide (a x t=u.val))∈A)
 (Tinit:F0 (N0 n)->Fin (2*n+1)->Fin (n+2)->Fin (2*n+1)->Y0->ℕ)
 (d:jw Tinit⊆A):
 Build A (jw (fun x=>z0 n (g3 n x) (a x) (Tinit x) n)) (n*ck n):=by
 let O (k:ℕ):=jw (fun x=>z0 n (g3 n x) (a x) (Tinit x) k)
 suffices H:Build A (O n) (0+n*ck n) by simpa only[Nat.zero_add] using H
 refine ew O (s6 d) fun k e=>?_;set q:Fin n:=⟨k,e⟩;let B:=A∪O k;let okSig (p:Fin (n+2)×Fin (n+2)):d4 (N0 n):=fun x=>j9 n (g3 n x) (a x) q p.1.val p.2.val;have Hok:Build B (R0 okSig) ((n+2)*(n+2)*(4*((2*n+1)*(2*n+1)))):=(by simpa only[J3,Q9] using ke (A:=B) okSig (4*((2*n+1)*(2*n+1))) (fun⟨sp,sm⟩=>nq n true (m.trans M8) (inl f) (inl l) a b (fun t u=>inl (c t u)) q sp sm));let C:=B∪R0 okSig
 have Hcells:=p7 (A:=C) (fun p:Fin (2*n+1)×Fin (n+2)×Fin (2*n+1)×Y0=>R0 (a9 (4*n) (fun x=>z0 n (g3 n x) (a x) (Tinit x) (k+1) p.1 p.2.1 p.2.2.1 p.2.2.2)))
  ((n+2)*(n+2)*((4*n)*(9*(4*n))+10*(4*n))) (fun⟨la',ro1',tse,np'⟩=>by
   let on (p:Fin (n+2)×Fin (n+2)):d4 (N0 n):=if ro1'.val+(p.1.val+p.2.val)<=n+1/\(2*q.val+1)*(p.1.val+p.2.val)<=la'.val then okSig p else fun _=>false;let mult (p:Fin (n+2)×Fin (n+2)):ℕ:=choose (ro1'.val+(p.1.val+p.2.val)) p.1.val*choose (ro1'.val+(p.1.val+p.2.val)-p.1.val) p.2.val
   let F (p:Fin (n+2)×Fin (n+2)) (x:F0 (N0 n)):ℕ:=if h:ro1'.val+(p.1.val+p.2.val)<=n+1/\(2*q.val+1)*(p.1.val+p.2.val)<=la'.val then z0 n (g3 n x) (a x) (Tinit x) k ⟨la'.val-(2*q.val+1)*(p.1.val+p.2.val),by omega⟩
      ⟨ro1'.val+(p.1.val+p.2.val),by omega⟩ tse (xor np' (decide (p.2.val %2=1)))
    else 0
   have HS:=bi (w:=4*n) (A:=C) on mult F (inl (inl f)) (inl (inl l))
    (fun p=>by dsimp only[on];split_ifs;exact inr ⟨p,rfl⟩;exact inl (inl f))
    (fun p j=>by dsimp only[F];split_ifs with h;exact inl (inr (q3 (i:=(_,_,_,_)) ⟨j,rfl⟩));have s:a9 (4*n) (fun _:F0 (N0 n)=>0) j=fun _=>false:=funext fun _=>zero_testBit j.val;rw[s];exact inl (inl f))
   have o:(fun x=>∑ p:Fin (n+2)×Fin (n+2),if on p x then mult p*F p x else 0)=fun x=>z0 n (g3 n x) (a x) (Tinit x) (k+1) la' ro1' tse np':=by
    funext x;rw[z0,L7 e];unfold oe;rw[sum_prod_type]
    refine L3 rfl fun sp _=>L3 rfl fun sm _=>?_;dsimp only[on,mult,F,okSig,q];by_cases g:ro1'.val+(sp.val+sm.val)<=n+1/\(2*k+1)*(sp.val+sm.val)<=la'.val
    . simp only[g,↓reduceIte,↓reduceDIte];by_cases r:j9 n (g3 n x) (a x) ⟨k,e⟩ sp.val sm.val=true<;>simp[g,r]
    . simp[g,show ¬ (j9 n (g3 n x) (a x) ⟨k,e⟩ sp.val sm.val=true/\ro1'.val+(sp.val+sm.val)<=n+1/\(2*k+1)*(sp.val+sm.val)<=la'.val) from fun h=>g ⟨h.2.1,h.2.2⟩]
   rw[o] at HS;simpa only[J3,Q9] using HS)
 exact d9 (i7 Hok Hcells) Y3 Y3 (le_of_eq (by unfold ck;simp only[J3,Q9,card_bool];ring))
lemma qp (n:ℕ) {A:Set (d4 (N0 n))}
 (h4:v5 n⊆A) (r:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (a:F0 (N0 n)->c7 n->ℕ)
 (o:∀ x t,a x t≤2*n)
 (s:∀ t (u:Fin (2*n+1)),(fun x=>decide (a x t=u.val))∈A)
 (Tinit:F0 (N0 n)->Fin (2*n+1)->Fin (2*n+1)->Y0->ℕ)
 (y:lw Tinit⊆A):
 Build A (lw (fun x=>z1 n (g3 n x) (a x) (Tinit x) n)) (n*bu n):=by
 let O (u:ℕ):=lw (fun x=>z1 n (g3 n x) (a x) (Tinit x) u)
 suffices H:Build A (O n) (0+n*bu n) by simpa only[Nat.zero_add] using H
 refine ew O (s6 y) fun u hu=>?_;set b:Fin n:=⟨u,hu⟩;let B:=A∪O u;let Tlift (x:F0 (N0 n)) (d c:Fin (2*n+1)) (f:Y0) (m:Fin (n+1)):ℕ:=if m.val=0 then z1 n (g3 n x) (a x) (Tinit x) u d c f else 0;let Och (e:ℕ):=qt (fun x=>x7 n (g3 n x) (a x) b (Tlift x) e)
 have Hch0:Build B (Och 0) 0:=by
  apply s6;rintro _ ⟨⟨d,c,f,m⟩,_,j,rfl⟩;dsimp only[x7,Tlift];split_ifs
  . exact inr (q3 (i:=(d,c,f)) ⟨j,rfl⟩)
  . have hz:a9 (4*n) (fun _:F0 (N0 n)=>0) j=fun _=>false:=funext fun _=>zero_testBit j.val;rw[hz];exact inl r
 have Hch:Build B (Och (2*n)) (2*n*bt n):=by
  suffices H:Build B (Och (2*n)) (0+2*n*bt n) by simpa only[Nat.zero_add] using H
  refine ew Och Hch0 fun e v=>?_;let C:=B∪Och e;set l:=d6 u e;by_cases g:l<=2*n
  . set q:=l9 u e g;let trSig (p:Fin (n+1)×Fin (n+1)×Fin (n+1)×Fin (n+1)):d4 (N0 n):=fun x=>decide (a x (f3 q true)+p.2.1.val=p.2.2.2.val/\o2 n (g3 n x) (a x) b ⟨e,v⟩ p.1.val p.2.1.val p.2.2.1.val=true)
    have Htr:Build C (R0 trSig) ((n+1)*(n+1)*(n+1)*(n+1)*(3*(2*n+1))):=by
     simpa only[J3,Q9,Z3] using
      ke (A:=C) trSig (3*(2*n+1)) (fun⟨prev_p,sp,sm,mp'⟩=>pi n (h4.trans (M8.trans M8)) (inl (inl r)) a o (fun t u'=>inl (inl (s t u'))) b ⟨e,v⟩ g prev_p sp sm mp')
    let D:=C∪R0 trSig
    have Hcells:=p7 (A:=D) (fun p:Fin (2*n+1)×Fin (2*n+1)×Y0×Fin (n+1)=>R0 (a9 (4*n) (fun x=>x7 n (g3 n x) (a x) b (Tlift x) (e+1) p.1 p.2.1 p.2.2.1 p.2.2.2)))
     ((n+1)*(n+1)*(n+1)*((4*n)*(9*(4*n))+10*(4*n))) (fun⟨la',re',np',mp'⟩=>by
      let on (p:Fin (n+1)×Fin (n+1)×Fin (n+1)):d4 (N0 n):=if re'.val+(p.2.1.val+p.2.2.val)<=2*n/\l*(p.2.1.val+p.2.2.val)<=la'.val
       then trSig (p.1,p.2.1,p.2.2,mp') else fun _=>false
      let mult (p:Fin (n+1)×Fin (n+1)×Fin (n+1)):ℕ:=choose (re'.val+(p.2.1.val+p.2.2.val)) p.2.1.val *choose (re'.val+(p.2.1.val+p.2.2.val)-p.2.1.val) p.2.2.val
      let F (p:Fin (n+1)×Fin (n+1)×Fin (n+1)) (x:F0 (N0 n)):ℕ:=if h:re'.val+(p.2.1.val+p.2.2.val)<=2*n/\l*(p.2.1.val+p.2.2.val)<=la'.val then x7 n (g3 n x) (a x) b (Tlift x) e
         ⟨la'.val-l*(p.2.1.val+p.2.2.val),by omega⟩ ⟨re'.val+(p.2.1.val+p.2.2.val),by omega⟩
         (xor np' (decide (p.2.2.val %2=1))) p.1
       else 0
      have HS:=bi (w:=4*n) (A:=D) on mult F (inl (inl (inl r))) (inl (inl (inl ht)))
       (fun p=>by dsimp only[on];split_ifs;exact inr ⟨(p.1,p.2.1,p.2.2,mp'),rfl⟩;exact inl (inl (inl r)))
       (fun p j=>by dsimp only[F];split_ifs with h;exact inl (inr (q3 (i:=(_,_,_,_)) ⟨j,rfl⟩));have hz:a9 (4*n) (fun _:F0 (N0 n)=>0) j=fun _=>false:=funext fun _=>zero_testBit j.val;rw[hz];exact inl (inl (inl r)))
      have k:(fun x=>∑ p:Fin (n+1)×Fin (n+1)×Fin (n+1),if on p x then mult p*F p x else 0)=fun x=>x7 n (g3 n x) (a x) b (Tlift x) (e+1) la' re' np' mp':=by
       funext x;rw[x7,L7 v];unfold ff;rw[L7 g]
       rw[sum_prod_type];refine L3 rfl fun prev_p _=>?_;rw[sum_prod_type];refine L3 rfl fun sp _=>L3 rfl fun sm _=>?_;dsimp only[on,mult,F,trSig,q,l,b];by_cases z:re'.val+(sp.val+sm.val)<=2*n/\d6 u e*(sp.val+sm.val)<=la'.val
       . simp only[z,↓reduceIte,↓reduceDIte];by_cases h2:a x (f3 (l9 u e g) true)+sp.val=mp'.val/\o2 n (g3 n x) (a x) ⟨u,hu⟩ ⟨e,v⟩ prev_p.val sp.val sm.val=true<;>simp[z,h2]
       . simp[z,show ¬ (a x (f3 (l9 u e g) true)+sp.val=mp'.val/\o2 n (g3 n x) (a x) ⟨u,hu⟩ ⟨e,v⟩ prev_p.val sp.val sm.val=true/\re'.val+(sp.val+sm.val)<=2*n/\d6 u e*(sp.val+sm.val)<=la'.val) from fun h=>z ⟨h.2.2.1,h.2.2.2⟩]
      rw[k] at HS;simpa only[J3,Q9,Z3] using HS)
    exact d9 (i7 Htr Hcells) Y3 Y3 (le_of_eq (by unfold bt;simp only[J3,Q9,card_bool];ring))
  . have k:Och (e+1)=Och e:=(by dsimp only[Och];congr 1;funext x;rw[x7,L7 v];unfold ff;rw[Q8 g]);rw[k];exact d9 (s6 M9) Y3 Y3 (by omega)
 have Hsum:=p7 (A:=B∪Och (2*n)) (fun p:Fin (2*n+1)×Fin (2*n+1)×Y0=>R0 (a9 (4*n) (fun x=>z1 n (g3 n x) (a x) (Tinit x) (u+1) p.1 p.2.1 p.2.2)))
  ((n+1)*(9*(4*n))) (fun⟨d,c,f⟩=>by
   have HS:=dh (A:=B∪Och (2*n)) (w:=4*n) (univ:V7 (Fin (n+1)))
    (fun m x=>x7 n (g3 n x) (a x) b (Tlift x) (2*n) d c f m)
    (inl (inl r)) (inl (inl ht)) (fun m _ j=>inr (q3 (i:=(d,c,f,m)) ⟨j,rfl⟩))
   have k:(fun x=>∑ m:Fin (n+1),x7 n (g3 n x) (a x) b (Tlift x) (2*n) d c f m)=fun x=>z1 n (g3 n x) (a x) (Tinit x) (u+1) d c f:=by funext x;rw[z1,L7 hu];rfl
   rw[k] at HS;simpa only[W2,Q9] using HS)
 exact d9 (i7 Hch Hsum) Y3 Y3 (le_of_eq (by unfold bu;simp only[J3,Q9,card_bool];ring))
lemma mz (n b:ℕ) {A:Set (d4 (N0 n))}
 (s:v5 n⊆A) (v:(fun _=>false)∈A) (y:(fun _=>true)∈A)
 (c:F0 (N0 n)->c7 n->ℕ)
 (g:∀ x t,c x t≤2*n)
 (l:∀ t (u:Fin (2*n+1)),(fun x=>decide (c x t=u.val))∈A)
 (k f e:d4 (N0 n)) (z:k∈A) (q:f∈A) (h0:e∈A)
 (a:F0 (N0 n)->Fin (2*n+1))
 (r:∀ d:Fin (2*n+1),(fun x=>decide (a x=d))∈A):
 Build A (R0 (a9 (4*n) (fun x=>ad n b (g3 n x) (c x) (k x) (f x) (e x) (a x))))
  (u1 n):=by
 have H1:=qn n s v y c g l e h0;let T1 (x:F0 (N0 n)):=u0 n (g3 n x) (c x) (e x) n;let A1:=A∪nr T1;have HM:=qi n b (A:=A1) (inl v) (inl y) k f (inl z) (inl q) T1 M9;let Tmid (x:F0 (N0 n)):=ak n b (k x) (f x) (T1 x);let A2:=A1∪jw Tmid
 have H2:=qo n (A:=A2) (s.trans (M8.trans M8)) (inl (inl v)) (inl (inl y))
  c g (fun t u=>inl (inl (l t u))) Tmid M9
 let T2 (x:F0 (N0 n)):=z0 n (g3 n x) (c x) (Tmid x) n;let A3:=A2∪jw T2;have m:lw (fun x d o p=>T2 x d ⟨0,by omega⟩ o p)⊆A3:=by rintro _ ⟨⟨d,o,p⟩,_,j,rfl⟩;exact inr (q3 (i:=(d,⟨0,by omega⟩,o,p)) ⟨j,rfl⟩)
 have H3:=qp n (A:=A3) (s.trans (M8.trans (M8.trans M8)))
  (inl (inl (inl v))) (inl (inl (inl y)))
  c g (fun t u=>inl (inl (inl (l t u))))
  (fun x d o p=>T2 x d ⟨0,by omega⟩ o p) m
 let T3 (x:F0 (N0 n)):=z1 n (g3 n x) (c x) (fun d o p=>T2 x d ⟨0,by omega⟩ o p) n;let A4:=A3∪lw T3
 have HS:=gh (w:=4*n) (A:=A4) (fun d x=>decide (a x=d)) (fun d x=>T3 x d ⟨0,by omega⟩ false)
  (inl (inl (inl (inl v)))) (inl (inl (inl (inl y))))
  (fun d=>inl (inl (inl (inl (r d)))))
  (fun d j=>inr (q3 (i:=(d,⟨0,by omega⟩,false)) ⟨j,rfl⟩))
 have he:(fun x=>∑ d:Fin (2*n+1),if decide (a x=d) then T3 x d ⟨0,by omega⟩ false else 0)=fun x=>ad n b (g3 n x) (c x) (k x) (f x) (e x) (a x):=by
  funext x;rw[Q4 (a x)]
  . simp[ad,T3,T2,Tmid,T1]
  . intro d _ h1;simp[Ne.symm h1]
  . intro h;exact absurd (Y2 _) h
 rw[he] at HS;exact d9 (i7 H1 (i7 HM (i7 H2 (i7 H3 HS)))) Y3 Y3 (le_of_eq (by unfold u1;simp only[Q9];ring))
end DPBuild
end SuffixDP
namespace BaseD
open S393.Compiler.Build BuildExt
open scoped BigOperators
abbrev n4 (m D:ℕ):=Fin m->Fin D
def k9 {m D:ℕ}(w:n4 m D):ℕ:=∑ j:Fin m,(w j).val*D^j.val
lemma fy {m D:ℕ}(c:0<D)(w:n4 m D):k9 w<D^m:=by
 induction m with
 | zero=>simp[k9]
 | succ m ih=>
  unfold k9 at ih ⊢;rw[sum_univ_castSucc];have b:=ih (fun j=>w j.castSucc);have a:(w (last m)).val+1<=D:=(w (last m)).isLt
  calc (∑ i:Fin m,(w i.castSucc).val*D^i.val)+(w (last m)).val*D^m
   < D^m+(w (last m)).val*D^m:=Nat.add_lt_add_right b _
   _=((w (last m)).val+1)*D^m:=by ring
   _<=D*D^m:=W4 _ a
   _=D^(m+1):=by rw[U4,mul_comm]
lemma lx {m D:ℕ}(g:0<D):Injective (@k9 m D):=by
 induction m with
 | zero=>intro a b _;funext j;exact elim0 j
 | succ m ih=>
  intro a b c;unfold k9 at c;rw[sum_univ_castSucc,sum_univ_castSucc] at c;simp only[Fin.val_castSucc,Fin.val_last] at c;have h:=fy g (fun j=>a j.castSucc);have k:=fy g (fun j=>b j.castSucc);unfold k9 at h k;have d:(a (last m)).val=(b (last m)).val:=by have e:0<D^m:=pow_pos g m;have n:((∑ i:Fin m,(a i.castSucc).val*D^i.val)+(a (last m)).val*D^m)/D^m=(a (last m)).val:=(by rw[Nat.add_mul_div_right _ _ e,div_eq_of_lt h,zero_add]);have l:((∑ i:Fin m,(b i.castSucc).val*D^i.val)+(b (last m)).val*D^m)/D^m=(b (last m)).val:=(by rw[Nat.add_mul_div_right _ _ e,div_eq_of_lt k,zero_add]);rw[<-n,<-l,c]
  have f:(fun j:Fin m=>a j.castSucc)=(fun j:Fin m=>b j.castSucc):=ih (by unfold k9;rw[d] at c;exact Nat.add_right_cancel c)
  funext j;refine lastCases (L6 d) (fun i=>congrFun f i) j
lemma jx {m D:ℕ}(l:0<D)(u v:n4 m D):k9 u<k9 v↔∃ k:Fin m,(∀ j:Fin m,k.val<j.val->u j=v j)/\(u k).val<(v k).val:=by
 induction m with
 | zero=>simp[k9]
 | succ m ih=>
  unfold k9;rw[sum_univ_castSucc,sum_univ_castSucc];simp only[Fin.val_castSucc,Fin.val_last];have n:=fy l (fun i=>u i.castSucc);have o:=fy l (fun i=>v i.castSucc);unfold k9 at n o;dsimp only at n o;have s:0<D^m:=pow_pos l m;constructor
  . intro b;by_cases f:(u (last m)).val=(v (last m)).val
    . have hlt':k9 (fun i:Fin m=>u i.castSucc)<k9 (fun i:Fin m=>v i.castSucc):=(by unfold k9;dsimp only;rw[f] at b;omega);obtain⟨k,a,d⟩:=(ih (fun i=>u i.castSucc) (fun i=>v i.castSucc)).mp hlt';refine⟨k.castSucc,fun j e=>?_,d⟩;refine lastCases (fun _=>L6 f) (fun i q=>a i q) j e
    . have c:(u (last m)).val<(v (last m)).val:=by
       by_contra hge;push_neg at hge;have g:(v (last m)).val+1<=(u (last m)).val:=by omega
       have p:(v (last m)).val*D^m+D^m<=(u (last m)).val*D^m:=(by have:=W4 (D^m) g;rw[Nat.add_mul,one_mul] at this;exact this);omega
      exact⟨last m,fun j e=>absurd e (by have:=j.isLt;simp;omega),c⟩
  . rintro⟨k,a,d⟩;refine lastCases ?_ ?_ k a d
    . intro _ c;have p:((u (last m)).val+1)*D^m<=(v (last m)).val*D^m:=W4 _ c;rw[Nat.add_mul,one_mul] at p;omega
    . intro i a h;have f:u (last m)=v (last m):=a (last m) (by simp[i.isLt]);have hlt':k9 (fun r:Fin m=>u r.castSucc)<k9 (fun r:Fin m=>v r.castSucc):=(ih _ _).mpr ⟨i,fun j e=>a j.castSucc e,h⟩;unfold k9 at hlt';dsimp only at hlt';rw[f];omega
def n0 {m D:ℕ}(S:V7 (n4 m D))(k:ℕ)(p:n4 m D):V7 (n4 m D):=S.filter (fun w=>∀ j:Fin m,k≤j.val->w j=p j)
def g4 {m D:ℕ}(S:V7 (n4 m D))(k:ℕ)(p:n4 m D):ℕ:=(n0 S k p).card
lemma ja {m D:ℕ}(S:V7 (n4 m D))(p:n4 m D):g4 S 0 p=if p∈S then 1 else 0:=by
 unfold g4 n0
 have c:S.filter (fun w=>∀ j:Fin m,0≤j.val->w j=p j)=if p∈S then {p} else ∅:=by
  ext w;split_ifs with a
  . simp only[L4,U5,V5,true_imp_iff];exact⟨fun⟨_,h⟩=>funext h,fun h=>⟨h▸a,fun j=>congrFun h j⟩⟩
  . simp only[L4,notMem_empty,iff_false,V5,true_imp_iff];rintro⟨b,h⟩;exact a (funext h▸b)
 rw[c];split_ifs<;>simp
lemma cq {m D:ℕ}(S:V7 (n4 m D))(p:n4 m D):g4 S m p=S.card:=by unfold g4 n0;have a:S.filter (fun w=>∀ j:Fin m,m≤j.val->w j=p j)=S:=(by ext w;simp only[L4,and_iff_left_iff_imp];intro _ j b;have:=j.isLt;omega);rw[a]
lemma iv {m D:ℕ}(S:V7 (n4 m D)){k:ℕ}(b:k<m)(p:n4 m D):g4 S (k+1) p=∑ d:Fin D,g4 S k (update p ⟨k,b⟩ d):=by
 unfold g4 n0;rw[card_eq_sum_card_fiberwise (f:=fun w:n4 m D=>w ⟨k,b⟩) (s:=S.filter (fun w=>∀ j:Fin m,k+1≤j.val->w j=p j)) (t:=univ) (fun _ _=>Y2 _)];refine L3 rfl fun d _=>?_;congr 1;ext w;simp only[L4];constructor
 . rintro⟨⟨g,a⟩,i⟩;refine⟨g,fun j e=>?_⟩;by_cases c:j=⟨k,b⟩
   . subst c;simpa using i
   . rw[update_of_ne c];exact a j (by have:j.val≠k:=fun h=>c (L6 h);omega)
 . rintro⟨g,a⟩;refine⟨⟨g,fun j e=>?_⟩,?_⟩
   . have l:j≠⟨k,b⟩:=fun h=>(by rw[h] at e;dsimp only at e;omega);simpa[update_of_ne l] using a j (by omega)
   . simpa using a ⟨k,b⟩ Y3
def j8 {m D:ℕ}(count:ℕ->n4 m D->ℕ)(p:n4 m D):ℕ->ℕ
 | 0=>0
 | k+1=>
  if h:k<m then (∑ d:Fin D,if d.val<(p ⟨k,h⟩).val then count k (update p ⟨k,h⟩ d) else 0) +j8 count p k
  else j8 count p k
lemma bv {m D:ℕ}(hD:0<D)(S:V7 (n4 m D))(p:n4 m D):j8 (g4 S) p m=(S.filter (fun w=>k9 w<k9 p)).card:=by
 have u:∀ k≤m,j8 (g4 S) p k=(S.filter (fun w=>∃ i:Fin m,i.val<k/\(∀ j:Fin m,i.val<j.val->w j=p j)/\(w i).val<(p i).val)).card:=by
  intro k hk;induction k with
  | zero=>simp[j8]
  | succ k ih=>
   rw[j8,L7 (by omega),ih (by omega)];set F1:=S.filter (fun w=>(∀ j:Fin m,k+1≤j.val->w j=p j)/\(w ⟨k,by omega⟩).val<(p ⟨k,by omega⟩).val);set F2:=S.filter (fun w=>∃ i:Fin m,i.val<k/\(∀ j:Fin m,i.val<j.val->w j=p j)/\(w i).val<(p i).val)
   have x:S.filter (fun w=>∃ i:Fin m,i.val<k+1/\(∀ j:Fin m,i.val<j.val->w j=p j)/\(w i).val<(p i).val)=F1∪F2:=by
    ext w;simp only[F1,F2,X4,L4];constructor
    . rintro⟨c,i,n,a,b⟩;by_cases hlt':i.val<k
      . exact inr ⟨c,i,hlt',a,b⟩
      . have hi:i=⟨k,by omega⟩:=L6 (by dsimp only;omega);rw[hi] at a b;exact inl ⟨c,fun j g=>a j (by dsimp only;omega),b⟩
    . rintro (⟨c,a,b⟩|⟨c,i,n,a,b⟩)
      . exact⟨c,⟨k,by omega⟩,by dsimp only;omega,fun j g=>a j (by dsimp only at g;omega),b⟩
      . exact⟨c,i,by omega,a,b⟩
   have r:Disjoint F1 F2:=by rw[X8];intro w z y;simp only[F1,F2,L4] at z y;obtain⟨_,i,n,a,b⟩:=y;have l:=a ⟨k,by omega⟩ n;rw[l] at z;omega
   rw[x,card_union_of_disjoint r];congr 1;rw[card_eq_sum_card_fiberwise (f:=fun w:n4 m D=>w ⟨k,by omega⟩) (s:=F1) (t:=univ) (fun _ _=>Y2 _)];refine L3 rfl fun d _=>?_;by_cases q:d.val<(p ⟨k,by omega⟩).val
   . rw[Q2 q];unfold g4 n0;congr 1;ext w;simp only[F1,L4];constructor
     . rintro⟨c,a⟩;have e:w ⟨k,by omega⟩=d:=by simpa using a ⟨k,by omega⟩ Y3
       refine⟨⟨c,fun j g=>?_,by rw[e];exact q⟩,e⟩;have v:j≠⟨k,by omega⟩:=fun h=>(by rw[h] at g;dsimp only at g;omega);simpa[update_of_ne v] using a j (by omega)
     . rintro⟨⟨c,a,_⟩,e⟩;refine⟨c,fun j g=>?_⟩;by_cases o:j=⟨k,by omega⟩
       . rw[o];simpa using e
       . rw[update_of_ne o];exact a j (by have:j.val≠k:=fun h=>o (L6 h);omega)
   . rw[Q3 q];symm;rw[U3,W8];intro w c l;simp only[F1,L4] at c;rw[l] at c;exact q c.2.2
 rw[u m Y3];congr 1;ext w;simp only[L4,jx hD];exact and_congr_right fun _=>exists_congr fun i=>by simp[i.isLt]
def u3 {D:ℕ}(b:0<D)(c:Fin D->ℕ)(t:ℕ)(a:Y0×Fin D×ℕ):Y0×Fin D×ℕ:=if h:t<D-1 then if a.1 then a
  else if a.2.2<c ⟨t,by omega⟩ then (true,⟨t,by omega⟩,a.2.2)
  else (false,⟨t+1,by omega⟩,a.2.2-c ⟨t,by omega⟩)
 else a
def e6 {D:ℕ}(a:0<D)(c:Fin D->ℕ)(r:ℕ):ℕ->Y0×Fin D×ℕ
 | 0=>(false,⟨0,a⟩,r)
 | t+1=>u3 a c t (e6 a c r t)
def y5 {D:ℕ}(b:0<D)(c:Fin D->ℕ)(r:ℕ):Fin D×ℕ:=let a:=e6 b c r (D-1);(a.2.1,a.2.2)
lemma gj {D:ℕ}(a:0<D)(c:Fin D->ℕ)(r t:ℕ):(e6 a c r t).2.2<=r:=by
 induction t with
 | zero=>exact Y3
 | succ t ih=>rw[e6];unfold u3;split_ifs<;>(try dsimp only)<;>omega
lemma lb {D:ℕ}(j:0<D)(c:Fin D->ℕ)(r:ℕ)(t:ℕ)(o:t<=D-1):let a:=e6 j c r t
 let pref (k:ℕ):=∑ d:Fin D,if d.val<k then c d else 0
 (a.1=true/\a.2.1.val<t/\pref a.2.1.val<=r/\r<pref a.2.1.val+c a.2.1/\a.2.2=r-pref a.2.1.val) ∨
 (a.1=false/\a.2.1.val=t/\pref t<=r/\a.2.2=r-pref t):=by
 dsimp only
 induction t with
 | zero=>right;refine⟨rfl,rfl,?_,?_⟩<;>simp[e6]
 | succ t ih=>
  have e:(∑ d:Fin D,if d.val<t+1 then c d else 0)=(∑ d:Fin D,if d.val<t then c d else 0)+c ⟨t,by omega⟩:=by
   have b:(∑ d:Fin D,if d.val<t+1 then c d else 0)=(∑ d:Fin D,if d.val<t then c d else 0)+∑ d:Fin D,if d.val=t then c d else 0:=by
    rw[<-Z4];refine L3 rfl fun d _=>by split_ifs<;>omega
   rw[b];congr 1;rw[Q4 (⟨t,by omega⟩:Fin D)]
   . simp
   . intro d _ l;simp[show d.val≠t from fun h=>l (L6 h)]
   . intro h;exact absurd (Y2 _) h
  rcases ih (by omega) with ⟨b,n,g,i,m⟩|⟨b,n,g,i⟩
  . left;rw[e6,u3,L7 (by omega),Q2 b];exact⟨b,by omega,g,i,m⟩
  . rw[e6,u3,L7 (by omega),Q3 (by simp[b])];by_cases f:(e6 j c r t).2.2<c ⟨t,by omega⟩
    . left;rw[Q2 f];dsimp only;exact⟨rfl,by omega,g,by omega,i⟩
    . right;rw[Q3 f];dsimp only;refine⟨rfl,rfl,by omega,by omega⟩
lemma na {D:ℕ}(e:0<D)(c:Fin D->ℕ)(r:ℕ)(m:r<∑ d:Fin D,c d):let (d₀,r'):=y5 e c r
 let P:=∑ d:Fin D,if d.val<d₀.val then c d else 0
 P<=r/\r<P+c d₀/\r'=r-P:=by
 have a:=lb e c r (D-1) Y3;dsimp only[y5] at a ⊢
 rcases a with ⟨_,_,b,f,j⟩|⟨_,h2,b,f⟩
 . exact⟨b,f,j⟩
 . have i:(e6 e c r (D-1)).2.1=⟨D-1,by omega⟩:=L6 h2
   have l:(∑ d:Fin D,if d.val<D-1 then c d else 0)+c ⟨D-1,by omega⟩=∑ d:Fin D,c d:=by
    have k:(∑ d:Fin D,c d)=(∑ d:Fin D,if d.val<D-1 then c d else 0)+∑ d:Fin D,if d.val=D-1 then c d else 0:=by
     rw[<-Z4];refine L3 rfl fun d _=>by have:=d.isLt;split_ifs<;>omega
    rw[k];congr 1;symm;rw[Q4 (⟨D-1,by omega⟩:Fin D)]
    . simp
    . intro d _ g;simp[show d.val≠D-1 from fun h=>g (L6 h)]
    . intro h;exact absurd (Y2 _) h
   rw[i];dsimp only;exact⟨b,by omega,f⟩
def i8 {m D:ℕ}(b:0<D)(count:ℕ->n4 m D->ℕ):ℕ->n4 m D->ℕ->n4 m D
 | 0,p,_=>p
 | k+1,p,r=>
  if h:k<m then let a:=y5 b (fun d=>count k (update p ⟨k,h⟩ d)) r
   i8 b count k (update p ⟨k,h⟩ a.1) a.2
  else p
lemma fo {m D:ℕ}(i:0<D)(S:V7 (n4 m D)):∀ k≤m,∀(p:n4 m D) (r:ℕ),r<g4 S k p->let w:=i8 i (g4 S) k p r
  w∈n0 S k p/\j8 (g4 S) w k=r:=by
 intro k;induction k with
 | zero=>intro _ p r l;rw[ja] at l;have hp:p∈S:=(by by_contra hn;rw[Q3 hn] at l;omega);have y:r=0:=(by rw[Q2 hp] at l;omega);simp[i8,n0,j8,hp,y]
 | succ k ih=>
  intro hk p r l;have a:k<m:=(by omega);rw[iv S a p] at l;have q:=na i (fun d=>g4 S k (update p ⟨k,a⟩ d)) r l;set b:=y5 i (fun d=>g4 S k (update p ⟨k,a⟩ d)) r;set p':=update p ⟨k,a⟩ b.1;have t:=ih (by omega) p' b.2 (by dsimp only[b,p'] at q ⊢;omega);have o:i8 i (g4 S) (k+1) p r=i8 i (g4 S) k p' b.2:=(by rw[i8,L7 a]);set w:=i8 i (g4 S) k p' b.2;rw[o];obtain⟨f,n⟩:=t;have x:w∈S:=(L4.mp f).1;have e:∀ j:Fin m,k≤j.val->w j=p' j:=(L4.mp f).2;have z:w ⟨k,a⟩=b.1:=by simpa[p'] using e ⟨k,a⟩ Y3
  have g:∀ d:Fin D,g4 S k (update w ⟨k,a⟩ d)=g4 S k (update p ⟨k,a⟩ d):=fun d=>by
   unfold g4 n0;congr 1;ext u;simp only[L4];refine and_congr_right fun _=>forall_congr' fun j=>imp_congr_right fun v=>?_;by_cases c:j=⟨k,a⟩
   . subst c;simp
   . have h2:k<j.val:=(by have:j.val≠k:=fun h=>c (L6 h);omega);rw[update_of_ne c,update_of_ne c,e j (by omega)];dsimp only[p'];rw[update_of_ne c]
  refine⟨L4.mpr ⟨x,fun j v=>?_⟩,?_⟩
  . have h0:j≠⟨k,a⟩:=fun h=>(by rw[h] at v;dsimp only at v;omega);rw[e j (by omega)];dsimp only[p'];rw[update_of_ne h0]
  . rw[j8,L7 a,n,z];have s:(∑ d:Fin D,if d.val<b.1.val then g4 S k (update w ⟨k,a⟩ d) else 0)=∑ d:Fin D,if d.val<b.1.val then g4 S k (update p ⟨k,a⟩ d) else 0:=L3 rfl fun d _=>(by split_ifs<;>simp[g]);rw[s];dsimp only[b] at q ⊢;omega
noncomputable def dk {m D:ℕ}(d:0<D)(S:V7 (n4 m D)):Fin S.card ≃ {w:n4 m D // w∈S}:=let toF (i:Fin S.card):{w:n4 m D // w∈S}:=have h:=fo d S m Y3 (fun _=>⟨0,d⟩) i.val (by rw[cq];exact i.isLt)
  ⟨i8 d (g4 S) m (fun _=>⟨0,d⟩) i.val,(L4.mp h.1).1⟩
 let invF (w:{w:n4 m D // w∈S}):Fin S.card:=⟨j8 (g4 S) w.1 m,by
   rw[bv d S w.1]
   exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun g=>by
    have p:w.1∈S.filter (fun u=>k9 u<k9 w.1):=g.symm▸w.2
    exact Nat.lt_irrefl _ (L4.mp p).2⟩)⟩
 have j:Function.LeftInverse invF toF:=fun i=>L6 (by
  dsimp only[invF,toF]
  exact (fo d S m Y3 (fun _=>⟨0,d⟩) i.val (by rw[cq];exact i.isLt)).2)
 have o:Function.RightInverse invF toF:=by
  have l:Injective invF:=by
   intro a b h;have c:=Q6 Fin.val h;dsimp only[invF] at c;rw[bv d,bv d] at c;apply Z9;apply lx d
   rcases lt_trichotomy (k9 a.1) (k9 b.1) with k|g|hgt
   . exfalso;have e:S.filter (fun u=>k9 u<k9 a.1) ⊂ S.filter (fun u=>k9 u<k9 b.1):=Finset.ssubset_iff_subset_ne.mpr ⟨fun u f=>L4.mpr ⟨(L4.mp f).1,lt_trans (L4.mp f).2 k⟩,fun n=>by have:a.1∈S.filter (fun u=>k9 u<k9 a.1):=n▸L4.mpr ⟨a.2,k⟩;exact Nat.lt_irrefl _ (L4.mp this).2⟩;exact ne_of_lt (card_lt_card e) c
   . exact g
   . exfalso;have e:S.filter (fun u=>k9 u<k9 b.1) ⊂ S.filter (fun u=>k9 u<k9 a.1):=Finset.ssubset_iff_subset_ne.mpr ⟨fun u f=>L4.mpr ⟨(L4.mp f).1,lt_trans (L4.mp f).2 hgt⟩,fun n=>by have:b.1∈S.filter (fun u=>k9 u<k9 b.1):=n▸L4.mpr ⟨b.2,hgt⟩;exact Nat.lt_irrefl _ (L4.mp this).2⟩;exact ne_of_gt (card_lt_card e) c
  intro w;exact l (j (invF w))
 ⟨toF,invF,j,o⟩
lemma ns {m D:ℕ}(a:0<D)(S:V7 (n4 m D))(i:Fin S.card):j8 (g4 S) (dk a S i).1 m=i.val:=Q6 Fin.val ((dk a S).symm_apply_apply i)
lemma og {m D:ℕ}(a:0<D)(S:V7 (n4 m D))(i:Fin S.card):(dk a S i).1=i8 a (g4 S) m (fun _=>⟨0,a⟩) i.val:=rfl
abbrev u7 (N m D:ℕ):=(Fin N->Y0)->n4 m D
abbrev iw (N m D:ℕ):=(Fin N->Y0)->ℕ->n4 m D->ℕ
def f0 {N m D:ℕ}(p:u7 N m D)(j:Fin m)(d:Fin D):d4 N:=fun x=>decide (p x j=d)
def p5 {N m D:ℕ}(p:u7 N m D):Set (d4 N):={f|∃ j d,f=f0 p j d}
def fg {N m D:ℕ}(p:u7 N m D)(j:Fin m)(d:Fin D):u7 N m D:=fun x=>update (p x) j d
lemma fv {N m D:ℕ} {A:Set (d4 N)} (p:u7 N m D) (j:Fin m) (d:Fin D)
 (g:p5 p⊆A) (f:(fun _=>false)∈A) (b:(fun _=>true)∈A):
 p5 (fg p j d)⊆A:=by
 rintro _ ⟨i,a,rfl⟩;by_cases c:i=j
 . subst i;have e:f0 (fg p j d) j a=fun _=>decide (d=a):=(by funext x;simp[f0,fg]);rw[e];by_cases h:d=a
   . simpa only[h,decide_true] using b
   . simpa only[h,decide_false] using f
 . have e:f0 (fg p j d) i a=f0 p i a:=(by funext x;simp[f0,fg,update_of_ne c]);rw[e];exact g ⟨_,_,rfl⟩
def fz {N m D:ℕ}(A₀:Set (d4 N))(w c:ℕ)(count:iw N m D):Prop:=∀(A:Set (d4 N)),A₀⊆A->∀(k:ℕ),k≤m->∀ p:u7 N m D,p5 p⊆A->Build A (R0 (a9 w (fun x=>count x k (p x)))) c
lemma oh {N m D w c:ℕ} {A:Set (d4 N)} {count:iw N m D}
 (Q:fz A w c count) (e:(fun _=>false)∈A) (g:(fun _=>true)∈A)
 (p:u7 N m D) (n:p5 p⊆A):
 Build A (R0 (a9 w (fun x=>j8 (count x) (p x) m)))
  (m*(D*c+D*D+D*(10*w)+9*w)):=by
 let O (k:ℕ):=R0 (a9 w (fun x=>j8 (count x) (p x) k));have o:Build A (O 0) 0:=my 0 e g
 suffices H:Build A (O m) (0+m*(D*c+D*D+D*(10*w)+9*w)) by simpa only[Nat.zero_add] using H
 refine ew O o fun k h=>?_;set j:Fin m:=⟨k,h⟩;let B:=A∪O k;let F (d:Fin D) (x:Fin N->Y0):=count x k (fg p j d x);have HQ:Build B (m0 univ (fun d:Fin D=>R0 (a9 w (F d)))) (D*c):=(by simpa only[Q9] using p7 (A:=B) (fun d:Fin D=>R0 (a9 w (F d))) c (fun d=>Q B M8 k h.le (fg p j d) (fv p j d (n.trans M8) (inl e) (inl g))));let ltSig (d:Fin D):d4 N:=fun x=>decide (d.val<(p x j).val)
 have Hlt:Build B (R0 ltSig) (D*D):=au ltSig D (fun d=>by
   let f (r:Fin D):d4 N:=if d.val<r.val then f0 p j r else fun _=>false;have Hany:=w3 (A:=B) f (inl e) (fun r=>by dsimp only[f];split_ifs;exact inl (n ⟨j,r,rfl⟩);exact inl e)
   have q:(fun x=>decide (∃ r:Fin D,f r x=true))=ltSig d:=by
    funext x;apply L5;simp only[ltSig,L0]
    constructor
    . rintro⟨r,hd'⟩;dsimp only[f] at hd';by_cases a:d.val<r.val
      . rw[Q2 a] at hd';simp only[f0,L0] at hd';rw[hd'];exact a
      . rw[Q3 a] at hd';simp at hd'
    . intro a;refine⟨p x j,?_⟩;dsimp only[f];rw[Q2 a];simp[f0]
   rw[q] at Hany;exact Hany)
 let C:=B∪(m0 univ (fun d:Fin D=>R0 (a9 w (F d)))∪R0 ltSig)
 have Hsum:=gh (w:=w) (A:=C) ltSig F (inl (inl e)) (inl (inl g))
  (fun d=>inr (inr ⟨d,rfl⟩)) (fun d i=>inr (inl (q3 (i:=d) ⟨i,rfl⟩)))
 let R (x:Fin N->Y0):=∑ d:Fin D,if ltSig d x then F d x else 0
 have Hadd:=jv (A:=C∪R0 (a9 w R)) w R (fun x=>j8 (count x) (p x) k)
  (inl (inl (inl e))) (fun i=>inr ⟨i,rfl⟩) (fun i=>inl (inl (inr ⟨i,rfl⟩)))
 have l:O (k+1)=R0 (a9 w (fun x=>R x+j8 (count x) (p x) k)):=by
  dsimp only[O,R,ltSig,F];congr 1;funext i x;dsimp only[a9];congr 1;rw[j8,L7 h];congr 1;refine L3 rfl fun d _=>by simp[fg,j]
 rw[l];exact d9 (i7 (q6 HQ Hlt) (i7 Hsum Hadd)) Y3 Y3 (by simp only[Q9];omega)
def os {N D:ℕ} (a:0<D) (w:ℕ) (c:Fin D->(Fin N->Y0)->ℕ)
 (r:(Fin N->Y0)->ℕ) (t:ℕ):Set (d4 N):=
 let st (x:Fin N->Y0):=e6 a (fun d=>c d x) (r x) t
 {fun x=>(st x).1}∪(R0 (fun d:Fin D=>fun x=>decide ((st x).2.1=d))∪R0 (a9 w (fun x=>(st x).2.2)))
lemma pj {N D w:ℕ} (b:0<D) {A:Set (d4 N)}
 (c:Fin D->(Fin N->Y0)->ℕ) (r:(Fin N->Y0)->ℕ)
 (g:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (hc:∀ d,i9 A (a9 w (c d))) (hr:i9 A (a9 w r))
 (h6:∀ d x,c d x<2^w) (h7:∀ x,r x<2^w):
 Build A (R0 (fun d:Fin D=>fun x=>decide ((y5 b (fun d=>c d x) (r x)).1=d))∪R0 (a9 w (fun x=>(y5 b (fun d=>c d x) (r x)).2)))
  ((D-1)*(18*w+15+3*D)):=by
 let O (t:ℕ):=os b w c r t
 have H0:Build A (O 0) 0:=by
  apply s6;rintro _ (rfl|⟨d,rfl⟩|⟨i,rfl⟩)
  . exact g
  . by_cases hd:(⟨0,b⟩:Fin D)=d
    . simpa only[e6,hd,decide_true] using ht
    . simpa only[e6,hd,decide_false] using g
  . exact hr i
 suffices H:Build A (O (D-1)) (0+(D-1)*(18*w+15+3*D)) by
  exact d9 H Y3 (fun _ h=>inr h) (by omega)
 refine ew O H0 fun t f=>?_;let B:=A∪O t;let st (x:Fin N->Y0):=e6 b (fun d=>c d x) (r x) t;let a:d4 N:=fun x=>(st x).1;let rem (x:Fin N->Y0):=(st x).2.2;let k:Fin D:=⟨t,by omega⟩;have m:a∈B:=inr (inl rfl);have y:i9 B (a9 w rem):=fun i=>inr (inr (inr ⟨i,rfl⟩));have o:∀ x,rem x<2^w:=fun x=>(gj b _ _ t).trans_lt (h7 x);have Hsub:=pq (A:=B) rem (c k) (inl g) (inl ht) y (fun i=>inl (hc k i)) o (h6 k);let remSub (x:Fin N->Y0):=if c k x<=rem x then rem x-c k x else rem x;let e:d4 N:=fun x=>decide (rem x<c k x);let C:=B∪(R0 (a9 w remSub)∪{e})
 have Hmux:=kf (A:=C) (s:=a) (v:=a9 w remSub) (u:=a9 w rem)
  (inl m) (fun i=>inr (inl ⟨i,rfl⟩)) (fun i=>inl (y i))
 have Hnf:=ae (A:=C) (inl m);have Hor:=gg (A:=C) (inl m) (inr (inr rfl));let C1:=C∪((R0 (fun i=>mx a (a9 w remSub i) (a9 w rem i))∪{nt a})∪{S393.Compiler.Build.or a e})
 have Hpk:=q6 (t7 (A:=C1) (inr (inl (inr rfl))) (inl (inr (inr rfl))))
  (i7 (ae (A:=C1) (inl (inr (inr rfl)))) (t7 (A:=C1∪{nt e}) (inl (inr (inl (inr rfl)))) (inr rfl)))
 let z:d4 N:=an (nt a) e;let n:d4 N:=an (nt a) (nt e);let C2:=C1∪({z}∪{n})
 have Hdig:=au (A:=C2) (fun d:Fin D=>fun x=>decide ((e6 b (fun d=>c d x) (r x) (t+1)).2.1=d)) 3 (fun d=>by
  have p:(fun x=>decide ((st x).2.1=d))∈C2:=inl (inl (inl (inr (inr (inl ⟨d,rfl⟩)))));have h1:a∈C2:=inl (inl (inl m));have h3:z∈C2:=inr (inl rfl);have h0:n∈C2:=inr (inr rfl);have j:=t7 h1 p;by_cases h2:d.val=t
  . have Hor2:=i7 j (gg (inr rfl) (inl h3))
    have l:S393.Compiler.Build.or (an a (fun x=>decide ((st x).2.1=d))) z=fun x=>decide ((e6 b (fun d=>c d x) (r x) (t+1)).2.1=d):=by
     funext x;rw[e6,u3,L7 f]
     cases hf':(e6 b (fun d=>c d x) (r x) t).1<;>by_cases hlt':(e6 b (fun d=>c d x) (r x) t).2.2<c ⟨t,by omega⟩ x<;>simp[S393.Compiler.Build.or,an,nt,z,a,e,rem,st,hf',hlt',k,K4,h2]<;>omega
    rw[l] at Hor2;exact d9 Hor2 Y3 Y3 (by omega)
  . by_cases q:d.val=t+1
    . have Hor2:=i7 j (gg (inr rfl) (inl h0))
      have l:S393.Compiler.Build.or (an a (fun x=>decide ((st x).2.1=d))) n=fun x=>decide ((e6 b (fun d=>c d x) (r x) (t+1)).2.1=d):=by
       funext x;rw[e6,u3,L7 f]
       cases hf':(e6 b (fun d=>c d x) (r x) t).1<;>by_cases hlt':(e6 b (fun d=>c d x) (r x) t).2.2<c ⟨t,by omega⟩ x<;>simp[S393.Compiler.Build.or,an,nt,n,a,e,rem,st,hf',hlt',k,K4,q]<;>omega
      rw[l] at Hor2;exact d9 Hor2 Y3 Y3 (by omega)
    . have l:an a (fun x=>decide ((st x).2.1=d))=fun x=>decide ((e6 b (fun d=>c d x) (r x) (t+1)).2.1=d):=by
       funext x;rw[e6,u3,L7 f]
       cases hf':(e6 b (fun d=>c d x) (r x) t).1<;>by_cases hlt':(e6 b (fun d=>c d x) (r x) t).2.2<c ⟨t,by omega⟩ x<;>simp[an,a,st,hf',hlt',k,K4,h2,q]<;>omega
      rw[l] at j;exact d9 j Y3 Y3 (by omega))
 have Hall:=q4 (q4 (q4 Hsub (q6 (q6 Hmux Hnf) Hor))
  (d9 Hpk (by simp only[C1,C,W6];exact Y3) Y3 Y3))
  (d9 Hdig (by simp only[C2,C1,C,W6];exact Y3) Y3 Y3)
 refine aa Hall Y3 ?_ (by omega);rintro _ (rfl|⟨d,rfl⟩|⟨i,rfl⟩)
 . have l:(fun x=>(e6 b (fun d=>c d x) (r x) (t+1)).1)=S393.Compiler.Build.or a e:=by
    funext x;rw[e6,u3,L7 f]
    cases hf':(e6 b (fun d=>c d x) (r x) t).1<;>by_cases hlt':(e6 b (fun d=>c d x) (r x) t).2.2<c ⟨t,by omega⟩ x<;>simp[S393.Compiler.Build.or,a,e,rem,st,hf',hlt',k]
   rw[l];exact inr (inl (inl (inr (inr rfl))))
 . exact inr (inr ⟨d,rfl⟩)
 . have l:a9 w (fun x=>(e6 b (fun d=>c d x) (r x) (t+1)).2.2) i=mx a (a9 w remSub i) (a9 w rem i):=by
    funext x;dsimp only[a9,mx,a,remSub,rem,st]
    rw[e6,u3,L7 f];by_cases hf':(e6 b (fun d=>c d x) (r x) t).1=true<;>by_cases hlt':(e6 b (fun d=>c d x) (r x) t).2.2<c ⟨t,by omega⟩ x<;>simp[st,k,Bool.not_eq_true,hf',hlt',Nat.not_le_of_gt,Nat.le_of_not_gt]
   rw[l];exact inr (inl (inl (inr (inl (inl ⟨i,rfl⟩)))))
abbrev jb (N m D:ℕ):=u7 N m D×((Fin N->Y0)->ℕ)
def bw {N m D:ℕ}(a:0<D)(count:iw N m D)(j:Fin m)(s:jb N m D):jb N m D:=let c (d:Fin D) (x:Fin N->Y0):=count x j.val (fg s.1 j d x)
 (fun x=>update (s.1 x) j (y5 a (fun d=>c d x) (s.2 x)).1,fun x=>(y5 a (fun d=>c d x) (s.2 x)).2)
def m7 {N m D:ℕ}(a:0<D)(count:iw N m D)(r:(Fin N->Y0)->ℕ):ℕ->jb N m D
 | 0=>(fun _ _=>⟨0,a⟩,r)
 | k+1=>
  if h:k<m then bw a count ⟨m-1-k,by omega⟩ (m7 a count r k)
  else m7 a count r k
lemma nu {N m D:ℕ}(a:0<D)(count:iw N m D)(r:(Fin N->Y0)->ℕ)(k:ℕ)(x:Fin N->Y0):(m7 a count r k).2 x<=r x:=by
 induction k with
 | zero=>exact Y3
 | succ k ih=>
  rw[m7];split_ifs
  . exact (gj a _ _ (D-1)).trans ih
  . exact ih
lemma mi {N m D:ℕ}(a:0<D)(count:iw N m D)(r:(Fin N->Y0)->ℕ)(x:Fin N->Y0):(m7 a count r m).1 x=i8 a (count x) m (fun _=>⟨0,a⟩) (r x):=by
 suffices H:∀ k≤m,let s:=m7 a count r k
  i8 a (count x) (m-k) (s.1 x) (s.2 x)=i8 a (count x) m (fun _=>⟨0,a⟩) (r x) by
  simpa only[Nat.sub_self,i8] using H m Y3
 intro k c;induction k with
 | zero=>simp[m7]
 | succ k ih=>
  have hk':k<m:=(by omega);rw[show m-k=(m-(k+1))+1 by omega] at ih;simp only[i8,show m-(k+1)<m by omega,L7] at ih;have b:m-(k+1)=m-1-k:=(by omega);simpa only[m7,L7 hk',bw,b,fg] using ih hk'.le
def rf {N m D:ℕ}(w:ℕ)(s:jb N m D):Set (d4 N):=p5 s.1∪R0 (a9 w s.2)
lemma nb {N m D w c:ℕ} (a:0<D) {A:Set (d4 N)} {count:iw N m D}
 (Q:fz A w c count) (o:(fun _=>false)∈A) (l:(fun _=>true)∈A)
 (f:∀ x k,k<m->∀ p,count x k p<2^w)
 (r:(Fin N->Y0)->ℕ) (v:i9 A (a9 w r)) (q:∀ x,r x<2^w):
 Build A (p5 (fun x=>i8 a (count x) m (fun _=>⟨0,a⟩) (r x)))
  (m*(D*c+(D-1)*(18*w+15+3*D))):=by
 let O (k:ℕ):=rf w (m7 a count r k)
 have H0:Build A (O 0) 0:=by
  apply s6;rintro _ (⟨j,d,rfl⟩|⟨i,rfl⟩)
  . by_cases h:(⟨0,a⟩:Fin D)=d
    . have e:f0 (m7 a count r 0).1 j d=fun _=>true:=(by funext x;simp[f0,m7,h]);exact e▸l
    . have e:f0 (m7 a count r 0).1 j d=fun _=>false:=(by funext x;simp[f0,m7,h]);exact e▸o
  . exact v i
 have H:=ew (t:=m) O H0 fun k n=>by
  set j:Fin m:=⟨m-1-k,by omega⟩;let s:=m7 a count r k;let B:=A∪O k;let cF (d:Fin D) (x:Fin N->Y0):=count x j.val (fg s.1 j d x);have HQ:Build B (m0 univ (fun d:Fin D=>R0 (a9 w (cF d)))) (D*c):=(by simpa only[Q9] using p7 (A:=B) (fun d:Fin D=>R0 (a9 w (cF d))) c (fun d=>Q B M8 j.val j.isLt.le (fg s.1 j d) (fv s.1 j d (fun _ h=>inr (inl h)) (inl o) (inl l))));let C:=B∪m0 univ (fun d:Fin D=>R0 (a9 w (cF d)))
  have Hch:=pj a (A:=C) cF s.2 (inl (inl o)) (inl (inl l))
   (fun d i=>inr (q3 (i:=d) ⟨i,rfl⟩)) (fun i=>inl (inr (inr ⟨i,rfl⟩)))
   (fun d x=>f x j.val j.isLt _) (fun x=>(nu a count r k x).trans_lt (q x))
  refine aa (q4 HQ Hch) Y3 ?_ Y3;rintro _ (⟨i,d,rfl⟩|⟨b,rfl⟩)
  . by_cases u:i=j
    . subst i;have g:f0 (m7 a count r (k+1)).1 j d=fun x=>decide ((y5 a (fun d=>cF d x) (s.2 x)).1=d):=(by funext x;simp[f0,m7,L7 n,bw,j,s,cF]);rw[g];exact inr (inr (inl ⟨d,rfl⟩))
    . have g:f0 (m7 a count r (k+1)).1 i d=f0 s.1 i d:=(by funext x;simp[f0,m7,L7 n,bw,update_of_ne u,j,s]);rw[g];exact inl (inr (inl ⟨i,d,rfl⟩))
  . have g:a9 w (m7 a count r (k+1)).2 b=a9 w (fun x=>(y5 a (fun d=>cF d x) (s.2 x)).2) b:=(by funext x;simp[a9,m7,L7 n,bw,j,s,cF]);rw[g];exact inr (inr (inr ⟨b,rfl⟩))
 have e:(fun x=>i8 a (count x) m (fun _=>⟨0,a⟩) (r x))=(m7 a count r m).1:=funext fun x=>(mi a count r x).symm;rw[e];exact d9 H Y3 M8 (by simp)
def n6 {N:ℕ}{S:Type*}(a:S)(step:ℕ->S->(Fin N->Y0)->S):ℕ->(Fin N->Y0)->S
 | 0,_=>a
 | j+1,x=>step j (n6 a step j x) x
def dd {N:ℕ}{S:Type*}[DecidableEq S](a:S)(step:ℕ->S->(Fin N->Y0)->S)(k:ℕ):Set (d4 N):=
 {f|∃ j:Fin (k+1),∃ s:S,f=fun x=>decide (n6 a step j.val x=s)}
lemma dm {N:ℕ} {S:Type*} [Fintype S] [DecidableEq S] {A:Set (d4 N)}
 (d:(fun _=>false)∈A) (f:(fun _=>true)∈A)
 (a:S) (step:ℕ->S->(Fin N->Y0)->S) (L cStep:ℕ)
 (c:∀ j<L,∀ s o:S,Build A {fun x=>decide (step j s x=o)} cStep):
 Build A (dd a step L)
  (L*(W0 S*(W0 S*(cStep+1)+W0 S))):=by
 let O (k:ℕ):=dd a step k
 have H0:Build A (O 0) 0:=by
  apply s6;rintro _ ⟨j,s,rfl⟩;rw[Fin.eq_zero j];by_cases e:a=s
  . simpa only[n6,e,decide_true] using f
  . simpa only[n6,e,decide_false] using d
 suffices Hs:Build A (O L) (0+L*(W0 S*(W0 S*(cStep+1)+W0 S))) by
  simpa only[Nat.zero_add] using Hs
 refine ew O H0 fun j g=>?_;let B:=A∪O j
 have Hnxt:Build B (m0 univ (fun o:S=>{fun x=>decide (n6 a step (j+1) x=o)}))
  (W0 S*(W0 S*(cStep+1)+W0 S)):=
  p7 (A:=B) (fun o:S=>{fun x=>decide (n6 a step (j+1) x=o)})
   (W0 S*(cStep+1)+W0 S) (fun o=>by
    let b:=equivFin S;let pr (i:Fin (W0 S)):d4 N:=an (fun x=>decide (n6 a step j x=b.symm i)) (fun x=>decide (step j (b.symm i) x=o))
    have Hpr:Build B (R0 pr) (W0 S*(cStep+1)):=au pr (cStep+1) (fun i=>i7 (d9 (c j g (b.symm i) o) M8 Y3 Y3)
       (t7 (inl (inr ⟨⟨j,U2 j⟩,b.symm i,rfl⟩)) (inr rfl)))
    have Hany:=w3 (A:=B∪R0 pr) pr (inl (inl d)) (fun i=>inr ⟨i,rfl⟩)
    have l:(fun x=>decide (∃ i:Fin (W0 S),pr i x=true))=fun x=>decide (n6 a step (j+1) x=o):=by
     funext x;apply L5;simp only[pr,an,K8,L0];rw[n6]
     exact⟨fun⟨i,h1,h2⟩=>by rw[h1];exact h2,fun h=>⟨b (n6 a step j x),by simp[b,h]⟩⟩
    rw[l] at Hany;exact i7 Hpr Hany)
 refine aa Hnxt Y3 ?_ Y3;rintro _ ⟨i,s,rfl⟩;have n:=i.isLt;by_cases m:i.val<=j
 . exact inl (inr ⟨⟨i.val,by omega⟩,s,rfl⟩)
 . rw[show i.val=j+1 by omega];exact inr (q3 (i:=s) rfl)
end BaseD
namespace Query392
open S399 StageA RingCode SuffixDP BaseD BuildExt
open S393.Compiler.Build
open scoped BigOperators Classical
noncomputable def k6 (n:ℕ)(x:F0 (N0 n)):V7 (n4 (2*n+2) (6*n+1)):=univ.filter (fun w=>l8 n x=true/\w8 n (2*n-x3 n x) (s7 n x) w)
lemma dx {n:ℕ}(d:1<=n)(x:F0 (N0 n)):(k6 n x).card<2^(4*n):=by
 have i:(k6 n x).card<=W0 ((BV n)->V9 Y0):=(by refine Finset.card_le_card_of_injOn (s5 n) (fun _ _=>Y2 _) ?_;intro w1 a w2 b c;have f:=(w5 d (s7 n x) w1 (L4.mp a).2.2).1;have e:=(w5 d (s7 n x) w2 (L4.mp b).2.2).1;rw[<-f,c,e]);have g:W0 ((BV n)->V9 Y0)=3^(2*n):=(by simp);have h:3^(2*n)<2^(4*n):=by rw[show 3^(2*n)=(3^2)^n by rw[<-pow_mul],show 2^(4*n)=(2^4)^n by rw[<-pow_mul]];exact Nat.pow_lt_pow_left (by decide) (by omega)
 omega
def ci (n l r:ℕ):ℤ:=f8 (fun a b=>if a=2*n/\b=n then 1 else 0) (fun _ _=>0) l r
lemma ix (n l r:ℕ):ci n l r<(4*n+5:ℤ):=by unfold ci f8;dsimp only;split_ifs<;>omega
noncomputable def v6 (n:ℕ):d4 (N0 n):=fun x=>decide (∀ l:Fin (2*n),∀ r∈(c4 (l.val+1)).toFinset,g3 n x (l.val+1) r=ci n (l.val+1) r)
lemma ot (n:ℕ) {A:Set (d4 (N0 n))} (g:v5 n⊆A)
 (m:(fun _=>false)∈A) (f:(fun _=>true)∈A):
 Build A {v6 n} (2*n*3):=by
 let cell (a:Fin (2*n*3)):d4 (N0 n):=let p:=finProdFinEquiv.symm a;let l:=p.1.val+1
  if p.2.val<(c4 l).length then ec n l ((c4 l).getD p.2.val 0) (ci n l ((c4 l).getD p.2.val 0))
  else fun _=>true
 have H:=er (A:=A) cell f (fun a=>by
  dsimp only[cell];split_ifs with b
  . exact ic g m (by omega) (by omega) (K3.mpr (by rw[getD_eq_getElem _ _ b];exact getElem_mem b)) _
  . exact f)
 have o:(fun x=>decide (∀ a:Fin (2*n*3),cell a x=true))=v6 n:=by
  funext x;apply L5;unfold v6;simp only[L0]
  constructor
  . intro c l r d;have hr':=d;rw[K3] at d;obtain⟨i,k⟩:=List.mem_iff_get.mp d;have j:i.val<3:=by have:(c4 (l.val+1)).length<=3:=(by unfold c4;split_ifs<;>simp);omega
    have h:=c (finProdFinEquiv (l,⟨i.val,j⟩));dsimp only[cell] at h;rw[M5,Q2 i.isLt,getD_eq_getElem _ _ i.isLt,<-get_eq_getElem,k] at h;rw[<-al n (l.val+1) r (by omega) (by omega) hr' _ (ix n _ _) x,L0] at h;exact h
  . intro c a;dsimp only[cell];rcases finProdFinEquiv.symm a with ⟨l,r3⟩
    split_ifs with b
    . have e:(c4 (l.val+1)).getD r3.val 0∈(c4 (l.val+1)).toFinset:=K3.mpr (by rw[getD_eq_getElem _ _ b];exact getElem_mem b);rw[<-al n (l.val+1) _ (by omega) (by omega) e _ (ix n _ _) x,L0];exact c l _ e
    . rfl
 rw[o] at H;exact H
def z7 (n:ℕ)(a:1<=n)(d:Fin (6*n+1)):c7 n:=if hd:0<d.val then l3 d hd else e4 ⟨0,a⟩ true
lemma dy {n:ℕ}(b:1<=n)(d:Fin (6*n+1))(a:0<d.val):z7 n b d=l3 d a:=L7 a
def w6 (n:ℕ)(a:1<=n)(w:n4 (2*n+2) (6*n+1)):Y0:=decide ((2*n+(w ⟨2*n+1,by omega⟩).val-c3 (z7 n a (w ⟨2*n-1,by omega⟩))) %2=1)
def k8 (n m:ℕ)(a:1<=n)(b:m<=2*n)(w:n4 (2*n+2) (6*n+1))(j:Fin m):c7 n:=z7 n a (w ⟨2*n-1-j.val,by omega⟩)
def ab (n m:ℕ)(b:1<=n)(a:m<=2*n)(w:n4 (2*n+2) (6*n+1)):ℕ:=∑ j:Fin m,c3 (k8 n m b a w j)
def cd (n m:ℕ)(b:1<=n)(a:m<=2*n)(w:n4 (2*n+2) (6*n+1))(t:c7 n):ℕ:=(univ.filter (fun j:Fin m=>k8 n m b a w j=t)).card
def en (n m:ℕ)(b:1<=n)(a:m<=2*n)(w:n4 (2*n+2) (6*n+1)):Y0:=decide ((univ.filter (fun j:Fin m=>c9 (k8 n m b a w j)=false)).card %2=1)
def ce (n a d:ℕ) (g:1<=n) (o:1<=a) (p:a<=2*n) (l:d<2*n)
 (w:n4 (2*n+2) (6*n+1)):Y0:=
 let b:=2*n-d;let m:=min b a;have k:m<=2*n:=(by omega);have i:0<m:=(by omega);let c:=(w ⟨2*n+1,by omega⟩).val;let h:=(w ⟨2*n,by omega⟩).val;let f:=k8 n m g k w;let e:=w6 n g w;decide (c<2*n/\h<2/\(∀ j:Fin m,0<(w ⟨2*n-1-j.val,by omega⟩).val)/\(∀ j:Fin b,a≤j.val->(w ⟨2*n-1-j.val,by omega⟩).val=0)/\c<c3 (f ⟨0,i⟩)/\(∀ j:Fin m,l5 (d5 e f j.val) (f j)=true)/\ab n m g k w<=2*n)
noncomputable def t3 (n a c:ℕ) (b:1<=n) (f:1<=a) (g:a<=2*n)
 (e:c<2*n) (x:F0 (N0 n)) (w:n4 (2*n+2) (6*n+1)):ℕ:=
 let m:=min (2*n-c) a;have d:m<=2*n:=by omega
 if ce n a c b f g e w then ad n (a-m) (g3 n x) (cd n m b d w)
   (d5 (w6 n b w) (k8 n m b d w) m)
   (w6 n b w) (en n m b d w) ⟨2*n-ab n m b d w,by omega⟩
 else 0
noncomputable def u2 (n:ℕ)(c:1<=n)(x:F0 (N0 n))(a:ℕ)(b:a<2*n)(w:n4 (2*n+2) (6*n+1)):ℕ:=(if l8 n x=true/\u5 n ⟨2*n,by unfold o8;omega⟩ x=true/\v6 n x=true/\(∀ j:Fin (2*n+2),a≤j.val->w j=m3 n j) then 1 else 0) +∑ k0:Fin (2*n),if l8 n x=true/\u5 n ⟨2*n-(k0.val+1),by unfold o8;omega⟩ x=true then t3 n (k0.val+1) a c (by omega) (by omega) b x w
  else 0
noncomputable def j5 (n:ℕ)(a:1<=n)(x:F0 (N0 n)):ℕ->n4 (2*n+2) (6*n+1)->ℕ
 | cut,w=>
  if h:cut<2*n then u2 n a x cut h w
  else if h2:cut<=(2*n+2) then ∑ d:Fin (6*n+1),j5 n a x (cut-1) (update w ⟨cut-1,by omega⟩ d)
  else 0
lemma ly {n:ℕ} (x:F0 (N0 n)) (b:l8 n x=true)
 (k:Fin (o8 n)):u5 n k x=decide (k.val=x3 n x):=by
 have a:cg n x=true:=(by unfold l8 at b;simp only[K8] at b;exact b.1.1);unfold cg at a;simp only[L0] at a;unfold x3;rw[L7 a];exact choose_spec a k
lemma ax {n f e:ℕ} (a:Y0) (c:Fin f->c7 n) (d:Fin e->c7 n)
 (m:ℕ) (h:m≤f) (g:m≤e) (b:∀ j:Fin m,c ⟨j.val,by omega⟩=d ⟨j.val,by omega⟩):
 d5 a c m=d5 a d m:=by
 induction m with
 | zero=>rfl
 | succ m ih=>rw[d5,L7 (by omega),d5,L7 (by omega),ih (by omega) (by omega) (fun j=>b ⟨j.val,by omega⟩),b ⟨m,by omega⟩]
lemma fw {n c a0:ℕ} (hn:1<=n) (r7:1<=c) (k2:c<=2*n)
 (g1:a0<2*n) (x:F0 (N0 n)) (r4:l8 n x=true)
 (hf:2*n-x3 n x=c) (w:n4 (2*n+2) (6*n+1)):
 t3 n c a0 hn r7 k2 g1 x w=g4 (k6 n x) a0 w:=by
 classical
 have p2:g3 n x=s7 n x:=funext fun l=>funext fun r=>(by simp[g3,r4]);have v0:∀ u:n4 (2*n+2) (6*n+1),u∈n0 (k6 n x) a0 w↔w8 n c (s7 n x) u/\∀ j:Fin (2*n+2),a0≤j.val->u j=w j:=fun u=>(by simp[n0,k6,r4,hf]);unfold t3;rw[p2];set h7:=2*n-a0;set m:=min h7 c;have hm:m<=2*n:=(by omega);have hmk:m<=c:=(by dsimp only[m];omega);have hm1:1<=m:=(by omega);by_cases x2:ce n c a0 hn r7 k2 g1 w=true
 . rw[Q2 x2];unfold ce at x2;simp only[L0] at x2;obtain⟨r2,r1,m1,p1,a4,f1,hplen⟩:=x2;set s0:Fin (2*n):=⟨(w ⟨2*n+1,by omega⟩).val,r2⟩;set b0:Fin 2:=⟨(w ⟨2*n,by omega⟩).val,r1⟩;set y:=k8 n m hn hm w;set o:=w6 n hn w;set y2:=ab n m hn hm w;set q:=cd n m hn hm w;set g0:=en n m hn hm w
   have b7:(∑ t:c7 n,q t*c3 t)+(2*n-y2)=2*n:=by
    have h1:(∑ t:c7 n,q t*c3 t)=y2:=by
     change (∑ t:c7 n,(univ.filter (fun j:Fin m=>y j=t)).card*c3 t)=∑ j:Fin m,c3 (y j);rw[<-Finset.sum_fiberwise_of_maps_to (g:=y) (s:=univ) (t:=univ) (fun _ _=>Y2 _)];refine L3 rfl fun t _=>by rw[L3 rfl (fun j hj=>by rw[(L4.mp hj).2]),sum_const,smul_eq_mul]
    omega
   rw[iy hn (by omega) (s7 n x) q (d5 o y m) o g0 ⟨2*n-y2,by omega⟩ b7]
   let mkU (d:Fin (c-m)->c7 n):n4 (2*n+2) (6*n+1):=fun j=>if j.val=2*n+1 then ⟨s0.val,by omega⟩
    else if j.val=2*n then ⟨b0.val,by omega⟩
    else let k:=2*n-1-j.val
     if h1:k<m then m5 (y ⟨k,h1⟩)
     else if h2:k<c then m5 (d ⟨k-m,by omega⟩)
     else ⟨0,by omega⟩
   let catT (d:Fin (c-m)->c7 n):Fin c->c7 n:=fun j=>if h:j.val<m then y ⟨j.val,h⟩ else d ⟨j.val-m,by omega⟩
   have x0:∀ d:Fin (c-m)->c7 n,(∀ j:Fin m,catT d ⟨j.val,by omega⟩=y j)/\(∀ j:Fin (c-m),catT d ⟨m+j.val,by omega⟩=d j)/\(∑ j:Fin c,c3 (catT d j))=y2+∑ j:Fin (c-m),c3 (d j)/\(∀ a:c7 n,(univ.filter (fun j:Fin c=>catT d j=a)).card=q a+(univ.filter (fun j:Fin (c-m)=>d j=a)).card)/\(univ.filter (fun j:Fin c=>c9 (catT d j)=false)).card=(univ.filter (fun j:Fin m=>c9 (y j)=false)).card +(univ.filter (fun j:Fin (c-m)=>c9 (d j)=false)).card:=fun d=>by
    have b1:∀(f:c7 n->ℕ),(∑ j:Fin c,f (catT d j))=(∑ j:Fin m,f (y j))+∑ j:Fin (c-m),f (d j):=fun f=>by
     let e:Fin m ⊕ Fin (c-m) ≃ Fin c:=finSumFinEquiv.trans (finCongr (by omega));rw[<-sum_equiv e (fun z=>f (catT d (e z))) (fun j=>f (catT d j)) (fun _=>rfl),Fintype.sum_sum_type];exact congrArg₂ (· + ·) (L3 rfl fun j _=>by simp[e,catT,j.isLt])
      (L3 rfl fun j _=>by simp[e,catT,show ¬ m+j.val<m by omega])
    refine⟨fun j=>by simp[catT,j.isLt],fun j=>by simp[catT,show ¬ m+j.val<m by omega],b1 c3,fun a=>?_,?_⟩
    . simpa only[card_filter,q,cd] using b1 (fun t=>if t=a then 1 else 0)
    . simpa only[card_filter] using b1 (fun t=>if c9 t=false then 1 else 0)
   unfold g4;refine card_bij (fun d _=>mkU d) ?_ ?_ ?_
   . intro d k0;rw[v0];simp only[L4,Y2,Q0] at k0;obtain⟨he,p0,t1,g2,hz⟩:=k0;obtain⟨r6,hc2,a1,h8,a2⟩:=x0 d
     have p:∀ j (hj:j≤c-m),d5 o (catT d) (m+j)=d5 (d5 o y m) d j:=fun j hj=>by
      induction j with
      | zero=>simp[d5];exact ax o (catT d) y m (by omega) Y3 (fun i=>r6 i)
      | succ j ih=>rw[show m+(j+1)=(m+j)+1 by omega,d5,L7 (by omega),d5,L7 (by omega),ih (by omega),hc2 ⟨j,by omega⟩]
     have v:decide ((2*n+(mkU d ⟨2*n+1,by omega⟩).val-c3 (catT d ⟨0,by omega⟩)) %2=1)=o:=by simp[mkU,catT,show 0<m by omega,o,w6,y,k8,s0]
     refine⟨?_,fun j hj=>?_⟩
     . unfold w8;rw[Q8 (by omega)];refine⟨k2,by simp[mkU,s0.isLt],by simp[mkU,b0.isLt],fun j hj=>by have:=j.isLt;dsimp only[mkU];simp only[show ¬ 2*n-1-j.val=2*n+1 by omega,show ¬ 2*n-1-j.val=2*n by omega,↓reduceIte,show 2*n-1-(2*n-1-j.val)=j.val by omega];split_ifs<;>exact o0 _,fun j hj=>by have:=j.isLt;dsimp only[mkU];simp only[show ¬ 2*n-1-j.val=2*n+1 by omega,show ¬ 2*n-1-j.val=2*n by omega,↓reduceIte,show 2*n-1-(2*n-1-j.val)=j.val by omega,show ¬ j.val<m by omega,show ¬ j.val<c by omega,↓reduceDIte],catT d,fun j=>by have:=j.isLt;dsimp only[mkU,catT];simp only[show ¬ 2*n-1-j.val=2*n+1 by omega,show ¬ 2*n-1-j.val=2*n by omega,↓reduceIte,show 2*n-1-(2*n-1-j.val)=j.val by omega,j.isLt,↓reduceDIte];split_ifs<;>rfl,by simpa[mkU,catT,show 0<m by omega,s0] using a4,?_,?_,by rw[a1,t1];omega,?_,?_⟩
       . intro j;rw[v];by_cases b4:j.val<m
         . rw[ax o (catT d) y j.val (by omega) (by omega) (fun i=>r6 ⟨i.val,by omega⟩),show catT d j=y ⟨j.val,b4⟩ by simp[catT,b4]];exact f1 ⟨j.val,b4⟩
         . rw[show j.val=m+(j.val-m) by omega,p (j.val-m) (by omega),show catT d j=d ⟨j.val-m,by omega⟩ by simp[catT,b4]];exact he ⟨j.val-m,by omega⟩
       . have q1:m+(c-m)=c:=(by omega);rw[v];rw[<-p (c-m) Y3] at p0;simpa only[q1] using p0
       . rw[a2];dsimp only[g0,en] at g2;set a:=(univ.filter (fun j:Fin m=>c9 (y j)=false)).card;set b:=(univ.filter (fun j:Fin (c-m)=>c9 (d j)=false)).card;by_cases ha:a %2=1<;>by_cases hb:b %2=1<;>simp only[ha,hb,decide_true,decide_false,Bool.xor_true,U0,Bool.false_xor,true_xor,Bool.not_true,Bool.not_false,Bool.true_eq_false] at g2<;>omega
       . intro l hl r hr;have h1:(fun l' r'=>o6 (catT d) l' r' true)=y8 (fun a=>q a+(univ.filter (fun j=>d j=a)).card):=funext fun l'=>funext fun r'=>(by rw[(u8 (catT d) l' r').1];congr 1;funext a;exact h8 a);have h2:(fun l' r'=>o6 (catT d) l' r' false)=y9 (fun a=>q a+(univ.filter (fun j=>d j=a)).card):=funext fun l'=>funext fun r'=>(by rw[(u8 (catT d) l' r').2];congr 1;funext a;exact h8 a);rw[h1,h2];exact hz l hl r hr
     . dsimp only[mkU];by_cases a7:j.val=2*n+1
       . rw[Q2 a7,show j=⟨2*n+1,by omega⟩ from L6 a7]
       . rw[Q3 a7];by_cases b2:j.val=2*n
         . rw[Q2 b2,show j=⟨2*n,by omega⟩ from L6 b2]
         . rw[Q3 b2];have b6:=j.isLt;set k:=2*n-1-j.val;have a3:j=⟨2*n-1-k,by omega⟩:=L6 (by dsimp only[k];omega);by_cases h1:k<m
           . have r8:=m1 ⟨k,h1⟩;dsimp only at r8;rw[L7 h1];refine Eq.trans ?_ (Q6 w a3.symm);dsimp only[y,k8];rw[dy hn _ r8,p6]
           . have d1:k<h7:=(by dsimp only[h7,k];omega);have d2:c<=k:=(by dsimp only[m] at h1;omega);rw[Q8 h1,Q8 (by omega),a3];exact L6 (p1 ⟨k,d1⟩ d2).symm
   . intro s1 _ s2 _ hx;funext j;have b6:=j.isLt;have hv:=congrFun hx ⟨2*n-1-(m+j.val),by omega⟩;dsimp only[mkU] at hv;have h1:¬ 2*n-1-(m+j.val)=2*n+1:=(by omega);have h2:¬ 2*n-1-(m+j.val)=2*n:=(by omega);have h3:2*n-1-(2*n-1-(m+j.val))=m+j.val:=(by omega);have h4:¬ m+j.val<m:=(by omega);have h5:m+j.val<c:=(by omega);have h6:m+j.val-m=j.val:=(by omega);simp only[h1,h2,↓reduceIte,h3,h4,h5,↓reduceDIte,h6] at hv;exact w4 n hv
   . intro u hu;rw[v0] at hu;obtain⟨b3,x1⟩:=hu;unfold w8 at b3;rw[Q8 (by omega)] at b3;obtain⟨_,_,_,_,hi,t,b8,_,v1,d0,h9,c1,e2⟩:=b3;let d:Fin (c-m)->c7 n:=fun j=>t ⟨m+j.val,by omega⟩;have a5:∀ j:Fin m,t ⟨j.val,by omega⟩=y j:=fun j=>by have b6:=j.isLt;dsimp only[m,h7] at b6;have hw:u ⟨2*n-1-j.val,by omega⟩=w ⟨2*n-1-j.val,by omega⟩:=x1 _ (by dsimp only;omega);exact w4 n (by rw[<-b8 ⟨j.val,by omega⟩,hw];simp[y,k8,dy hn _ (m1 j),p6])
     have b5:catT d=t:=funext fun j=>by dsimp only[catT,d];split_ifs with b4;exact (a5 ⟨j.val,b4⟩).symm;congr 1;exact L6 (by dsimp only;omega)
     obtain⟨_,_,a1,h8,a2⟩:=x0 d;rw[b5] at a1 h8 a2;have k1:u ⟨2*n+1,by omega⟩=⟨s0.val,by omega⟩:=by rw[x1 _ (by dsimp only;omega)]
     have hc:u ⟨2*n,by omega⟩=⟨b0.val,by omega⟩:=by rw[x1 _ (by dsimp only;omega)]
     have v:decide ((2*n+(u ⟨2*n+1,by omega⟩).val-c3 (t ⟨0,by omega⟩)) %2=1)=o:=by rw[k1,a5 ⟨0,by omega⟩];simp[o,w6,y,k8,s0]
     have p:∀ j (hj:j≤c-m),d5 o t (m+j)=d5 (d5 o y m) d j:=fun j hj=>by
      rw[<-b5];induction j with
      | zero=>simp[d5];exact ax o (catT d) y m (by omega) Y3 (fun i=>by simp[catT,i.isLt])
      | succ j ih=>rw[show m+(j+1)=(m+j)+1 by omega,d5,L7 (by omega),d5,L7 (by omega),ih (by omega)];simp[catT,show ¬ m+j<m by omega]
     refine⟨d,?_,?_⟩
     . simp only[L4,Y2,Q0];have c2:∑ j:Fin (c-m),c3 (d j)=2*n-y2:=(by have:y2+∑ j:Fin (c-m),c3 (d j)=2*n:=a1.symm.trans h9;omega);refine⟨fun j=>by have:=j.isLt;rw[<-p j.val (by omega),<-v];exact v1 ⟨m+j.val,by omega⟩,by rw[<-p (c-m) Y3,show m+(c-m)=c by omega,<-v];exact d0,c2,?_,?_⟩
       . dsimp only[g0,en];set a:=(univ.filter (fun j:Fin m=>c9 (y j)=false)).card;set b:=(univ.filter (fun j:Fin (c-m)=>c9 (d j)=false)).card;have hs:(a+b) %2=0:=(by rw[<-a2];exact c1);by_cases ha:a %2=1<;>by_cases hb:b %2=1<;>simp only[ha,hb,decide_true,decide_false,Bool.xor_true,U0,Bool.false_xor,true_xor,Bool.not_true,Bool.not_false]<;>omega
       . intro l hl r hr;have h1':y8 (fun a=>q a+(univ.filter (fun j=>d j=a)).card)=fun l' r'=>o6 t l' r' true:=funext fun l'=>funext fun r'=>(by rw[(u8 t l' r').1];congr 1;funext a;exact (h8 a).symm);have h2':y9 (fun a=>q a+(univ.filter (fun j=>d j=a)).card)=fun l' r'=>o6 t l' r' false:=funext fun l'=>funext fun r'=>(by rw[(u8 t l' r').2];congr 1;funext a;exact (h8 a).symm);rw[h1',h2'];exact e2 l hl r hr
     . funext j;dsimp only[mkU]
       by_cases a7:j.val=2*n+1
       . rw[Q2 a7,show j=⟨2*n+1,by omega⟩ from L6 a7,k1]
       . rw[Q3 a7];by_cases b2:j.val=2*n
         . rw[Q2 b2,show j=⟨2*n,by omega⟩ from L6 b2,hc]
         . rw[Q3 b2];set k:=2*n-1-j.val;have a3:j=⟨2*n-1-k,by omega⟩:=L6 (by dsimp only[k];omega)
           conv_rhs=>rw[a3]
           by_cases h1:k<m
           . rw[L7 h1,<-a5 ⟨k,h1⟩,b8 ⟨k,by omega⟩]
           . rw[Q8 h1];by_cases h2:k<c
             . rw[L7 h2];dsimp only[d];have ho:(⟨m+(k-m),by omega⟩:Fin c)=⟨k,h2⟩:=L6 (by dsimp only;omega);rw[ho,<-b8 ⟨k,h2⟩]
             . rw[Q8 h2];exact L6 (hi ⟨k,by omega⟩ (by dsimp only;omega)).symm
 . rw[Q3 x2];symm;unfold g4 n0;rw[U3,W8];intro u hu hy;have f2:u∈n0 (k6 n x) a0 w:=L4.mpr ⟨hu,hy⟩;rw[v0 u] at f2;obtain⟨b3,x1⟩:=f2;apply x2;unfold ce;simp only[L0];unfold w8 at b3;rw[Q8 (by omega)] at b3;obtain⟨_,hk,hq,q2,m2,t,b8,a4,v1,_,h9,_,_⟩:=b3;have c0:w ⟨2*n+1,by omega⟩=u ⟨2*n+1,by omega⟩:=(x1 _ (by dsimp only;omega)).symm;have w2:w ⟨2*n,by omega⟩=u ⟨2*n,by omega⟩:=(x1 _ (by dsimp only;omega)).symm;have b9:∀ j:Fin m,k8 n m hn hm w j=t ⟨j.val,by omega⟩:=fun j=>by have b6:=j.isLt;unfold k8;have r3:w ⟨2*n-1-j.val,by omega⟩=m5 (t ⟨j.val,by omega⟩):=(x1 _ (by dsimp only;omega)).symm.trans (b8 ⟨j.val,by omega⟩);rw[dy hn _ (by rw[r3];exact o0 _)];exact w4 n (by rw[p6,r3])
   refine⟨by rw[c0];exact hk,by rw[w2];exact hq,fun j=>by have:=j.isLt;rw[<-x1 _ (by dsimp only;omega)];exact q2 ⟨j.val,by omega⟩ (by dsimp only;omega),fun j hj=>by have:=j.isLt;rw[<-x1 _ (by dsimp only;omega)];exact m2 ⟨j.val,by omega⟩ hj,by rw[c0,b9 ⟨0,by omega⟩];exact a4,fun j=>?_,?_⟩
   . have ht:w6 n hn w=decide ((2*n+(u ⟨2*n+1,by omega⟩).val-c3 (t ⟨0,by omega⟩)) %2=1):=by unfold w6;rw[c0];have:=b9 ⟨0,by omega⟩;unfold k8 at this;simpa using Q6 (fun a=>decide ((2*n+(u ⟨2*n+1,by omega⟩).val-c3 a) %2=1)) this
     have:=j.isLt;rw[ht,ax _ (k8 n m hn hm w) t j.val (by omega) (by omega) (fun i=>b9 ⟨i.val,by omega⟩),b9 j];exact v1 ⟨j.val,by omega⟩
   . unfold ab;rw[L3 rfl (fun j _=>by rw[b9 j])]
     have hsb:(∑ j:Fin m,c3 (t ⟨j.val,by omega⟩))=∑ j∈univ.filter (fun j:Fin c=>j.val<m),c3 (t j):=sum_bij (fun j _=>⟨j.val,by omega⟩) (fun j _=>by simp[j.isLt]) (fun _ _ _ _ h=>L6 (Q6 (Fin.val (n:=c)) h))
       (fun j hj=>⟨⟨j.val,by simp at hj;exact hj⟩,Y2 _,L6 rfl⟩) (fun _ _=>rfl)
     calc (∑ j:Fin m,c3 (t ⟨j.val,by omega⟩))
      =∑ j∈univ.filter (fun j:Fin c=>j.val<m),c3 (t j):=hsb
      _<=∑ j:Fin c,c3 (t j):=Finset.sum_le_univ_sum_of_nonneg (fun _=>V5 _)
      _=2*n:=h9
lemma am {n:ℕ} (q:1<=n) (x:F0 (N0 n))
 (b:ℕ) (e:b<2*n) (w:n4 (2*n+2) (6*n+1)):
 u2 n q x b e w=g4 (k6 n x) b w:=by
 unfold u2;by_cases a:l8 n x=true
 . have d:=ly x a;have h6:=ki n x;by_cases c:x3 n x=2*n
   . have m:(∑ k0:Fin (2*n),if l8 n x=true/\u5 n ⟨2*n-(k0.val+1),by unfold o8;omega⟩ x=true then t3 n (k0.val+1) b q (by omega) (by omega) e x w else 0)=0:=L9 fun k0 _=>(by rw[Q3];intro h;rw[d,c] at h;simp at h;omega);rw[m,add_zero,d,c];have f:g3 n x=s7 n x:=funext fun l=>funext fun r=>by simp[g3,a]
     have g:n0 (k6 n x) b w=if v6 n x=true/\(∀ j:Fin (2*n+2),b≤j.val->w j=m3 n j) then {m3 n} else ∅:=by
      ext u;split_ifs with v
      . simp only[n0,k6,w8,a,c,Nat.sub_self,↓reduceDIte,L4,Y2,Q0,U5];refine⟨fun h=>h.1.1,?_⟩;rintro rfl;refine⟨⟨rfl,fun l k r y=>?_⟩,fun j t=>(v.2 j t).symm⟩;obtain⟨h7,h8⟩:=J4.mp k;have p:=v.1;unfold v6 at p;simp only[L0,f] at p;have hl':l-1+1=l:=(by omega);have s:=(p ⟨l-1,by omega⟩ r (by simpa only[hl'] using y)).symm;dsimp only at s;unfold ci at s;simpa only[hl'] using s
      . simp only[n0,k6,w8,a,c,Nat.sub_self,↓reduceDIte,L4,Y2,Q0,notMem_empty,iff_false];rintro⟨⟨rfl,h3⟩,z⟩;apply v;refine⟨?_,fun j t=>(z j t).symm⟩;unfold v6;simp only[L0,f];intro l r y;exact (h3 (l.val+1) (J4.mpr ⟨by omega,by have:=l.isLt;omega⟩) r y).symm
     unfold g4;rw[g];simp only[a,decide_true,Q0];split_ifs<;>simp
   . have h0:(if l8 n x=true/\u5 n ⟨2*n,by unfold o8;omega⟩ x=true/\v6 n x=true/\(∀ j:Fin (2*n+2),b≤j.val->w j=m3 n j) then 1 else 0)=0:=(by rw[Q3];intro h;rw[d] at h;simp[Ne.symm c] at h);rw[h0,zero_add,Q4 (⟨2*n-x3 n x-1,by omega⟩:Fin (2*n))]
     . rw[Q2 ⟨a,by rw[d];simp[show 2*n-(2*n-x3 n x-1+1)=x3 n x by omega]⟩];exact fw q (by omega) (by dsimp only;omega) e x a (by dsimp only;omega) w
     . intro k0 _ h4;rw[Q3];intro h;rw[d] at h;simp only[L0] at h;exact h4 (L6 (by dsimp only;omega))
     . intro h;exact absurd (Y2 _) h
 . have i:l8 n x=false:=Bool.eq_false_iff.mpr a;have o:k6 n x=∅:=(by ext u;simp[k6,i]);simp[i,g4,n0,o]
lemma ay {n:ℕ} (e:1<=n) (x:F0 (N0 n))
 (a:ℕ) (c:a<=(2*n+2)) (w:n4 (2*n+2) (6*n+1)):
 j5 n e x a w=g4 (k6 n x) a w:=by
 induction a generalizing w with
 | zero=>rw[j5,L7 (by omega)];exact am e x 0 (by omega) w
 | succ a ih=>
  by_cases b:a+1<2*n
  . rw[j5,L7 b];exact am e x (a+1) b w
  . rw[j5,Q8 b,L7 c,iv (k6 n x) (by omega) w];refine L3 rfl fun d _=>by simpa only[Nat.add_sub_cancel] using ih (by omega) (update w ⟨a,by omega⟩ d)
def ba (n:ℕ):ℕ:=(2*n)*(6*n)+(6*n)*((2*n)*((2*n+1)*((2*n+1)*2+(2*n+1)))) +((6*n+1)+6*n+5)+(2*n)*(2*(2*(6*n+1)+2)) +(2*n+1)*5 +(2*n)*(1+6*n+6*n)+(2*n)*((2*n+2)*((2*n+2)*(6*n+1)+(2*n+2))) +(2*n+1)+(2*n)*(2*(2*(6*n+1)+2)) +(2*n+1+2*(2*n)+2*n+(2*n)*(6*n)*2+2*n+1+10)
def l6 (n:ℕ):ℕ:=2*n*3+(2*n+2)+6+4*n+(2*n)*(ba n+u1 n+4*n+1+10*(4*n))+9*(4*n)
def y0 (n:ℕ):ℕ:=(6*n+1)*((6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n))
lemma jy (n w b5:ℕ) (a:1<=n) (g2:1<=w) (g1:w<=2*n) (b7:b5<2*n)
 {A:Set (d4 (N0 n))} (hl:v5 n⊆A) (hf:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (p:u7 (N0 n) (2*n+2) (6*n+1)) (hp:p5 p⊆A):
 Build A (R0 (a9 (4*n) (fun x=>t3 n w b5 a g2 g1 b7 x (p x))))
  (ba n+u1 n+4*n):=by
 unfold t3;set h8:=2*n-b5;set m:=min h8 w;have o:m<=2*n:=(by omega);have x0:0<m:=(by omega);let pt (j:Fin m) (t:c7 n):d4 (N0 n):=fun x=>decide (k8 n m a o (p x) j=t);let m2:Set (d4 (N0 n)):=m0 univ (fun q:Fin m×c7 n=>{pt q.1 q.2})
 have Hpt:Build A m2 (m*(6*n)):=by
  have H:=p7 (A:=A) (fun q:Fin m×c7 n=>{pt q.1 q.2}) 1 (fun⟨j,t⟩=>by
   let wAt (d:Fin (6*n+1)):d4 (N0 n):=f0 p ⟨2*n-1-j.val,by omega⟩ d;by_cases r1:t=e4 ⟨0,a⟩ true
   . subst r1
     have he:S393.Compiler.Build.or (wAt (m5 (e4 ⟨0,a⟩ true))) (wAt ⟨0,by omega⟩)=pt j (e4 ⟨0,a⟩ true):=by
      funext x;apply L5;simp only[S393.Compiler.Build.or,wAt,f0,pt,V4,L0]
      unfold k8 z7;split_ifs with hd
      . exact⟨fun h=>h.elim (fun h1=>w4 n (by rw[p6,h1])) (fun z=>by rw[z] at hd;simp at hd),fun h=>inl ((p6 _ hd).symm.trans (Q6 m5 h))⟩
      . exact⟨fun _=>rfl,fun _=>inr (L6 (by dsimp only;omega))⟩
     rw[<-he];exact gg (hp ⟨_,_,rfl⟩) (hp ⟨_,_,rfl⟩)
   . have he:wAt (m5 t)=pt j t:=by
      funext x;apply L5;simp only[wAt,f0,pt,L0]
      unfold k8 z7;split_ifs with hd
      . exact⟨fun h=>w4 n (by rw[p6,h]),fun h=>(p6 _ hd).symm.trans (Q6 m5 h)⟩
      . exact⟨fun h=>absurd (h▸o0 t) hd,fun h=>absurd h.symm r1⟩
     rw[<-he];exact d9 (s6 (Q1 (hp ⟨_,_,rfl⟩))) Y3 Y3 (by omega))
  exact d9 H Y3 Y3 (le_of_eq (by simp only[J3,Q9,c7,card_bool];ring))
 let A1:=A∪m2;have y1:(fun _=>false)∈A1:=inl hf;have k1:(fun _=>true)∈A1:=inl ht;have d1:∀ j t,pt j t∈A1:=fun j t=>inr (q3 (i:=(j,t)) rfl);let usedStep (t:c7 n) (j:ℕ) (c:Fin (2*n+1)) (x:F0 (N0 n)):Fin (2*n+1):=if r:j<m then if k8 n m a o (p x) ⟨j,r⟩=t then ⟨min (c.val+1) (2*n),by omega⟩ else c else c
 have f2:∀ t j (r:j≤m) x,(n6 (⟨0,by omega⟩:Fin (2*n+1)) (usedStep t) j x).val=(univ.filter (fun i:Fin m=>i.val<j/\k8 n m a o (p x) i=t)).card:=fun t j r x=>by
  induction j with
  | zero=>simp[n6]
  | succ j ih=>
   have y:j<m:=by omega
   have hle:(univ.filter (fun i:Fin m=>i.val<j/\k8 n m a o (p x) i=t)).card<2*n:=by
    have w1:univ.filter (fun i:Fin m=>i.val<j/\k8 n m a o (p x) i=t)⊆univ.filter (fun i:Fin m=>i.val<j):=fun i hi=>by simp at hi ⊢;exact hi.1
    have hx:(univ.filter (fun i:Fin m=>i.val<j)).card=(Finset.range j).card:=card_bij (fun(i:Fin m) _=>i.val) (fun i hi=>by simp at hi ⊢;exact hi)
      (fun _ _ _ _ h=>L6 h) (fun v hv=>⟨⟨v,by rw[mem_range] at hv;omega⟩,by simp[mem_range.mp hv],rfl⟩)
    have hc:(univ.filter (fun i:Fin m=>i.val<j)).card<=j:=(by rw[hx,W1]);have:=card_le_card w1;omega
   have x2:univ.filter (fun i:Fin m=>i.val<j+1/\k8 n m a o (p x) i=t)=if k8 n m a o (p x) ⟨j,y⟩=t then insert ⟨j,y⟩ (univ.filter (fun i:Fin m=>i.val<j/\k8 n m a o (p x) i=t))
    else univ.filter (fun i:Fin m=>i.val<j/\k8 n m a o (p x) i=t):=by
    ext i;split_ifs with k2<;>simp only[L4,Y2,Q0,X3,K4]
    . exact⟨fun⟨h1,z⟩=>if c0:i.val=j then inl c0 else inr ⟨by omega,z⟩,fun h=>h.elim (fun c0=>⟨by omega,by rw[show i=⟨j,y⟩ from L6 c0];exact k2⟩) (fun⟨h1,z⟩=>⟨by omega,z⟩)⟩
    . exact⟨fun⟨h1,z⟩=>⟨by by_contra hge;exact k2 (by rw[<-show i=⟨j,y⟩ from L6 (by dsimp only;omega)];exact z),z⟩,fun⟨h1,z⟩=>⟨by omega,z⟩⟩
   rw[n6];dsimp only[usedStep];rw[L7 y,x2];split_ifs with k2
   . rw[W9 (by simp)];dsimp only;rw[ih (by omega)];omega
   . exact ih (by omega)
 let c1:Set (d4 (N0 n)):=m0 univ (fun q:c7 n×Fin (2*n+1)=>{fun x=>decide (cd n m a o (p x) q.1=q.2.val)})
 have Hused:Build A1 c1 ((6*n)*(m*((2*n+1)*((2*n+1)*2+(2*n+1))))):=by
  have H:=p7 (A:=A1) (fun t:c7 n=>dd (⟨0,by omega⟩:Fin (2*n+1)) (usedStep t) m)
   (m*((2*n+1)*((2*n+1)*2+(2*n+1)))) (fun t=>by
    simpa only[Q9] using dm y1 k1 (⟨0,by omega⟩:Fin (2*n+1)) (usedStep t) m 1 (fun j r c c'=>by
     by_cases h1:(⟨min (c.val+1) (2*n),by omega⟩:Fin (2*n+1))=c'<;>by_cases z:c=c'
     . have he:(fun x=>decide (usedStep t j c x=c'))=fun _=>true:=(by funext x;apply L5;simp only[L0];dsimp only[usedStep];rw[L7 r];split_ifs<;>simp_all);rw[he];exact d9 (s6 (Q1 k1)) Y3 Y3 (by omega)
     . have he:(fun x=>decide (usedStep t j c x=c'))=pt ⟨j,r⟩ t:=(by funext x;apply L5;simp only[pt,L0];dsimp only[usedStep];rw[L7 r];split_ifs<;>simp_all);rw[he];exact d9 (s6 (Q1 (d1 ⟨j,r⟩ t))) Y3 Y3 (by omega)
     . have he:(fun x=>decide (usedStep t j c x=c'))=nt (pt ⟨j,r⟩ t):=(by funext x;apply L5;simp only[pt,nt,Bool.not_eq_true',M7,L0];dsimp only[usedStep];rw[L7 r];split_ifs<;>simp_all);rw[he];exact ae (d1 ⟨j,r⟩ t)
     . have he:(fun x=>decide (usedStep t j c x=c'))=fun _=>false:=by funext x;apply L5;simp only[J5,L0];dsimp only[usedStep];rw[L7 r];split_ifs<;>simp_all
       rw[he];exact d9 (s6 (Q1 y1)) Y3 Y3 (by omega)))
  refine d9 H Y3 ?_ (le_of_eq (by simp only[J3,Q9,c7,card_bool];ring));rintro _ ⟨⟨t,u⟩,_,rfl⟩;refine⟨t,Y2 _,⟨m,U2 m⟩,u,?_⟩
  funext x;apply L5;simp only[L0,K4,f2 t m Y3 x,cd]
  have q1:univ.filter (fun i:Fin m=>i.val<m/\k8 n m a o (p x) i=t)=univ.filter (fun i:Fin m=>k8 n m a o (p x) i=t):=(by ext i;simp[i.isLt]);rw[q1]
 let h9:d4 (N0 n):=fun x=>w6 n a (p x)
 have HcolE:Build A1 {h9} ((6*n+1)+6*n+5):=by
  let s0O:=w3 (A:=A1) (fun d:Fin (6*n+1)=>if d.val %2=1 then f0 p ⟨2*n+1,by omega⟩ d else fun _=>false)
   y1 (fun d=>by split_ifs;exact inl (hp ⟨_,_,rfl⟩);exact y1)
  let hy:=w3 (A:=A1) (fun e:Fin (6*n)=>if c3 ((o1 n).symm e) %2=1 then pt ⟨0,x0⟩ ((o1 n).symm e) else fun _=>false)
   y1 (fun e=>by split_ifs;exact d1 _ _;exact y1)
  have Hx:=i7 (q6 s0O hy) (qr (inr (inl rfl)) (inr (inr rfl)))
  have he:xo (fun x=>decide (∃ d:Fin (6*n+1),(if d.val %2=1 then f0 p ⟨2*n+1,by omega⟩ d else fun _=>false) x=true))
   (fun x=>decide (∃ e:Fin (6*n),(if c3 ((o1 n).symm e) %2=1 then pt ⟨0,x0⟩ ((o1 n).symm e) else fun _=>false) x=true))=h9:=by
   funext x
   have h1:decide (∃ d:Fin (6*n+1),(if d.val %2=1 then f0 p ⟨2*n+1,by omega⟩ d else fun _=>false) x=true)=decide ((p x ⟨2*n+1,by omega⟩).val %2=1):=by
    apply L5;simp only[L0];constructor
    . rintro⟨d,hd⟩;by_cases ho:d.val %2=1
      . rw[Q2 ho] at hd;simp only[f0,L0] at hd;rwa[hd]
      . rw[Q3 ho] at hd;simp at hd
    . intro ho;exact⟨p x ⟨2*n+1,by omega⟩,by rw[Q2 ho];simp[f0]⟩
   have z:decide (∃ e:Fin (6*n),(if c3 ((o1 n).symm e) %2=1 then pt ⟨0,x0⟩ ((o1 n).symm e) else fun _=>false) x=true)=decide (c3 (k8 n m a o (p x) ⟨0,x0⟩) %2=1):=by
    apply L5;simp only[L0];constructor
    . rintro⟨e,k⟩;by_cases ho:c3 ((o1 n).symm e) %2=1
      . rw[Q2 ho] at k;simp only[pt,L0] at k;rwa[k]
      . rw[Q3 ho] at k;simp at k
    . intro ho;exact⟨o1 n (k8 n m a o (p x) ⟨0,x0⟩),by rw[M5,Q2 ho];simp[pt]⟩
   dsimp only[xo,h9,w6];rw[h1,z];have y2:=(k7 (z7 n a (p x ⟨2*n-1,by omega⟩))).2;have t2:k8 n m a o (p x) ⟨0,x0⟩=z7 n a (p x ⟨2*n-1,by omega⟩):=(by simp[k8]);rw[t2];have hp:(2*n+(p x ⟨2*n+1,by omega⟩).val-c3 (z7 n a (p x ⟨2*n-1,by omega⟩))) %2=1↔¬ ((p x ⟨2*n+1,by omega⟩).val %2=1↔c3 (z7 n a (p x ⟨2*n-1,by omega⟩)) %2=1):=(by omega);by_cases ha:(p x ⟨2*n+1,by omega⟩).val %2=1<;>by_cases hb:c3 (z7 n a (p x ⟨2*n-1,by omega⟩)) %2=1<;>simp[ha,hb,hp]
  rw[he] at Hx;exact d9 Hx Y3 Y3 (by omega)
 let A2:=A1∪(c1∪{h9});have b1:(fun _=>false)∈A2:=inl y1;have d0:(fun _=>true)∈A2:=inl k1;have b6:∀ j t,pt j t∈A2:=fun j t=>inl (d1 j t)
 have v2:∀ {S:Type} [Fintype S] [DecidableEq S] (g:S->c7 n->S),∀ j (r:j<m) (s s':S),Build A2 {fun x=>decide (g s (k8 n m a o (p x) ⟨j,r⟩)=s')} (6*n):=fun g j r s s'=>by
  have H:=w3 (A:=A2) (fun e:Fin (6*n)=>if g s ((o1 n).symm e)=s' then pt ⟨j,r⟩ ((o1 n).symm e) else fun _=>false)
   b1 (fun e=>by split_ifs;exact b6 _ _;exact b1)
  have he:(fun x=>decide (∃ e:Fin (6*n),(if g s ((o1 n).symm e)=s' then pt ⟨j,r⟩ ((o1 n).symm e) else fun _=>false) x=true))=fun x=>decide (g s (k8 n m a o (p x) ⟨j,r⟩)=s'):=by
   funext x;apply L5;simp only[L0]
   constructor
   . rintro⟨e,k⟩;by_cases hg:g s ((o1 n).symm e)=s'
     . rw[Q2 hg] at k;simp only[pt,L0] at k;rwa[k]
     . rw[Q3 hg] at k;simp at k
   . intro hg;exact⟨o1 n (k8 n m a o (p x) ⟨j,r⟩),by rw[M5,Q2 hg];simp[pt]⟩
  rw[he] at H;exact H
 let walkStep (j:ℕ) (b:Y0) (x:F0 (N0 n)):Y0:=if r:j<m then es b (k8 n m a o (p x) ⟨j,r⟩) else b
 have HwalkFSA:=dm b1 d0 false walkStep m (6*n) (fun j r b b'=>by
  simpa only[walkStep,L7 r] using v2 es j r b b')
 have k0:∀ j (r:j≤m) x,d5 (w6 n a (p x)) (k8 n m a o (p x)) j=xor (w6 n a (p x)) (n6 false walkStep j x):=fun j r x=>by
  induction j with
  | zero=>simp[d5,n6]
  | succ j ih=>
   have y:j<m:=(by omega);rw[d5,L7 y,n6];dsimp only[walkStep];rw[L7 y,ih (by omega),db,db,Z6]
 let walkSig (j:ℕ):d4 (N0 n):=fun x=>d5 (w6 n a (p x)) (k8 n m a o (p x)) j;let c2:Set (d4 (N0 n)):=R0 (fun j:Fin (m+1)=>walkSig j.val)
 have Hwalk:Build A2 c2 (m*(2*(2*(6*n+1)+2))+(m+1)*5):=by
  have Hx:=au (A:=A2∪dd false walkStep m) (fun j:Fin (m+1)=>xo h9 (fun x=>decide (n6 false walkStep j.val x=true))) 4
   (fun j=>qr (A:=A2∪dd false walkStep m) (inl (inr (inr rfl))) (inr ⟨j,true,rfl⟩))
  have he:(fun j:Fin (m+1)=>xo h9 (fun x=>decide (n6 false walkStep j.val x=true)))=fun j=>walkSig j.val:=by
   funext j x;dsimp only[xo,h9,walkSig];rw[k0 j.val (by omega) x];cases n6 false walkStep j.val x<;>rfl
  rw[he] at Hx;exact d9 (i7 HwalkFSA Hx) Y3 Y3 (by simp only[card_bool];omega)
 let lenStep (j:ℕ) (l:Fin (2*n+2)) (x:F0 (N0 n)):Fin (2*n+2):=if r:j<m then ⟨min (l.val+c3 (k8 n m a o (p x) ⟨j,r⟩)) (2*n+1),by omega⟩ else l
 have HlenFSA:=dm b1 d0 (⟨0,by omega⟩:Fin (2*n+2)) lenStep m (6*n) (fun j r l l'=>by
  simpa only[lenStep,L7 r] using v2 (fun(l:Fin (2*n+2)) t=>(⟨min (l.val+c3 t) (2*n+1),by omega⟩:Fin (2*n+2))) j r l l')
 have b9:∀ j (r:j≤m) x,(n6 (⟨0,by omega⟩:Fin (2*n+2)) lenStep j x).val=min (∑ i∈univ.filter (fun i:Fin m=>i.val<j),c3 (k8 n m a o (p x) i)) (2*n+1):=fun j r x=>by
  induction j with
  | zero=>simp[n6]
  | succ j ih=>
   have y:j<m:=(by omega);have x2:univ.filter (fun i:Fin m=>i.val<j+1)=insert ⟨j,y⟩ (univ.filter (fun i:Fin m=>i.val<j)):=(by ext i;simp only[L4,Y2,Q0,X3,K4];omega);rw[n6];dsimp only[lenStep];rw[L7 y,x2,sum_insert (by simp)];dsimp only;rw[ih (by omega)];omega
 let npStep (j:ℕ) (b:Y0) (x:F0 (N0 n)):Y0:=if r:j<m then xor b (decide (c9 (k8 n m a o (p x) ⟨j,r⟩)=false)) else b
 have HnpFSA:=dm b1 d0 false npStep m (6*n) (fun j r b b'=>by
  simpa only[npStep,L7 r] using v2 (fun b t=>xor b (decide (c9 t=false))) j r b b')
 have p1:∀ j (r:j≤m) x,n6 false npStep j x=decide ((univ.filter (fun i:Fin m=>i.val<j/\c9 (k8 n m a o (p x) i)=false)).card %2=1):=fun j r x=>by
  induction j with
  | zero=>simp[n6]
  | succ j ih=>
   have y:j<m:=by omega
   have x2:univ.filter (fun i:Fin m=>i.val<j+1/\c9 (k8 n m a o (p x) i)=false)=if c9 (k8 n m a o (p x) ⟨j,y⟩)=false then insert ⟨j,y⟩ (univ.filter (fun i:Fin m=>i.val<j/\c9 (k8 n m a o (p x) i)=false))
    else univ.filter (fun i:Fin m=>i.val<j/\c9 (k8 n m a o (p x) i)=false):=by
    ext i;split_ifs with hf'<;>simp only[L4,Y2,Q0,X3,K4]
    . exact⟨fun⟨h1,z⟩=>if c0:i.val=j then inl c0 else inr ⟨by omega,z⟩,fun h=>h.elim (fun c0=>⟨by omega,by rw[show i=⟨j,y⟩ from L6 c0];exact hf'⟩) (fun⟨h1,z⟩=>⟨by omega,z⟩)⟩
    . exact⟨fun⟨h1,z⟩=>⟨by by_contra hge;exact hf' (by rw[<-show i=⟨j,y⟩ from L6 (by dsimp only;omega)];exact z),z⟩,fun⟨h1,z⟩=>⟨by omega,z⟩⟩
   rw[n6];dsimp only[npStep];rw[L7 y,ih (by omega),x2];split_ifs with hf'
   . rw[W9 (by simp)];set c:=(univ.filter (fun i:Fin m=>i.val<j/\c9 (k8 n m a o (p x) i)=false)).card;have hp:(c+1) %2=1↔¬ c %2=1:=(by omega);by_cases hc:c %2=1<;>simp[hc,hf',hp]
   . simp[hf']
 let A3:=A2∪(c2∪(dd (⟨0,by omega⟩:Fin (2*n+2)) lenStep m∪dd false npStep m));have r3:(fun _=>false)∈A3:=inl b1;have w2:(fun _=>true)∈A3:=inl d0;let lenEqM (l:Fin (2*n+2)):d4 (N0 n):=fun x=>decide (n6 (⟨0,by omega⟩:Fin (2*n+2)) lenStep m x=l);have x1:∀ l,lenEqM l∈A3:=fun l=>inr (inr (inl ⟨⟨m,U2 m⟩,l,rfl⟩));let remLenSig (rl:Fin (2*n+1)):d4 (N0 n):=fun x=>decide ((⟨2*n-ab n m a o (p x),by omega⟩:Fin (2*n+1))=rl)
 have HremLen:Build A3 (R0 remLenSig) (2*n+1):=by
  simpa only[Nat.mul_one] using au remLenSig 1 (fun rl=>by
   have p0:∀ x,(n6 (⟨0,by omega⟩:Fin (2*n+2)) lenStep m x).val=min (ab n m a o (p x)) (2*n+1):=fun x=>(by rw[b9 m Y3 x];unfold ab;congr 2;ext i;simp[i.isLt]);by_cases hr0:rl.val=0
   . have Ho:=gg (A:=A3) (x1 ⟨2*n,by omega⟩) (x1 ⟨2*n+1,by omega⟩)
     have he:S393.Compiler.Build.or (lenEqM ⟨2*n,by omega⟩) (lenEqM ⟨2*n+1,by omega⟩)=remLenSig rl:=by
      funext x;apply L5;simp only[S393.Compiler.Build.or,lenEqM,remLenSig,K4,p0 x,hr0,V4,L0]
      have:=rl.isLt;omega
     rw[he] at Ho;exact Ho
   . have he:lenEqM ⟨2*n-rl.val,by omega⟩=remLenSig rl:=by funext x;apply L5;simp only[lenEqM,remLenSig,K4,p0 x,L0];omega
     rw[<-he];exact d9 (s6 (Q1 (x1 _))) Y3 Y3 (by omega))
 let colOkSig (j:Fin m):d4 (N0 n):=fun x=>l5 (walkSig j.val x) (k8 n m a o (p x) j)
 have HcolOk:Build A3 (R0 colOkSig) (m*(1+6*n+6*n)):=au colOkSig (1+6*n+6*n) (fun j=>by
   have Hn:=ae (A:=A3) (inr (inl ⟨⟨j.val,by omega⟩,rfl⟩));let C:=A3∪{nt (walkSig j.val)}
   let term (e:Fin (6*n)):d4 (N0 n):=let t:=(o1 n).symm e
    if t.1.val=2 then pt j t else if t.1.val=0 then an (pt j t) (nt (walkSig j.val)) else an (pt j t) (walkSig j.val)
   have Ht:=au (A:=C) term 1 (fun e=>by
    dsimp only[term];split_ifs
    . exact d9 (s6 (Q1 (inl (inl (b6 j _))))) Y3 Y3 (by omega)
    . exact t7 (inl (inl (b6 j _))) (inr rfl)
    . exact t7 (inl (inl (b6 j _))) (inl (inr (inl ⟨⟨j.val,by omega⟩,rfl⟩))))
   have Hany:=w3 (A:=C∪R0 term) term (inl (inl r3)) (fun e=>inr ⟨e,rfl⟩)
   have he:(fun x=>decide (∃ e:Fin (6*n),term e x=true))=colOkSig j:=by
    funext x;apply L5;simp only[colOkSig,L0]
    constructor
    . rintro⟨e,k⟩;dsimp only[term] at k;set t:=(o1 n).symm e;have h3:t.1.val=0\/t.1.val=1\/t.1.val=2:=by have:=t.1.isLt;omega
      rcases h3 with h0|h1|z
      . simp only[h0,show ¬ (0:ℕ)=2 by decide,↓reduceIte,an,nt,pt,K8,Bool.not_eq_true',L0] at k;rw[k.1];unfold l5;simp[h0,k.2]
      . simp only[h1,show ¬ (1:ℕ)=2 by decide,show ¬ (1:ℕ)=0 by decide,↓reduceIte,an,pt,K8,L0] at k;rw[k.1];unfold l5;simp[h1,k.2]
      . simp only[z,↓reduceIte,pt,L0] at k;rw[k];unfold l5;simp[z]
    . intro r2;refine⟨o1 n (k8 n m a o (p x) j),?_⟩;dsimp only[term];rw[M5];have h3:(k8 n m a o (p x) j).1.val=0\/(k8 n m a o (p x) j).1.val=1\/(k8 n m a o (p x) j).1.val=2:=(by have:=(k8 n m a o (p x) j).1.isLt;omega);unfold l5 at r2
      rcases h3 with h0|h1|z
      . simp only[h0,show ¬ (0:ℕ)=2 by decide,↓reduceIte,an,nt,pt,decide_true,Bool.true_and,Bool.not_eq_true'];cases hw:walkSig j.val x<;>simp[h0,hw] at r2 ⊢
      . simp only[h1,show ¬ (1:ℕ)=2 by decide,show ¬ (1:ℕ)=0 by decide,↓reduceIte,an,pt,decide_true,Bool.true_and];cases hw:walkSig j.val x<;>simp[h1,hw] at r2 ⊢
      . simp[z,pt]
   rw[he] at Hany;exact d9 (i7 Hn (i7 Ht Hany)) Y3 Y3 (by omega))
 let A4:=A3∪(R0 remLenSig∪R0 colOkSig);have f1:(fun _=>false)∈A4:=inl r3;have b2:(fun _=>true)∈A4:=inl w2;have b0:p5 p⊆A4:=hp.trans (M8.trans (M8.trans (M8.trans M8)))
 have Hpok:Build A4 {fun x=>ce n w b5 a g2 g1 b7 (p x)} (2*n+1+2*m+h8+(2*n)*(6*n)*2+m+1+7):=by
  have Hs0:=w3 (A:=A4) (fun s0:Fin (2*n)=>f0 p ⟨2*n+1,by omega⟩ ⟨s0.val,by omega⟩) f1 (fun s0=>b0 ⟨_,_,rfl⟩);have Hb0:=gg (A:=A4) (b0 ⟨⟨2*n,by omega⟩,⟨0,by omega⟩,rfl⟩) (b0 ⟨⟨2*n,by omega⟩,⟨1,by omega⟩,rfl⟩)
  have Hpos:Build A4 {fun x=>decide (∀ j:Fin m,0<(p x ⟨2*n-1-j.val,by omega⟩).val)} (2*m):=by
   let nz (j:Fin m):d4 (N0 n):=nt (f0 p ⟨2*n-1-j.val,by omega⟩ ⟨0,by omega⟩);have H1:=au (A:=A4) nz 1 (fun j=>ae (b0 ⟨_,_,rfl⟩));have H2:=er (A:=A4∪R0 nz) nz (inl b2) (fun j=>inr ⟨j,rfl⟩)
   have he:(fun x=>decide (∀ j:Fin m,nz j x=true))=fun x=>decide (∀ j:Fin m,0<(p x ⟨2*n-1-j.val,by omega⟩).val):=by
    funext x;apply L5;simp only[nz,nt,f0,Bool.not_eq_true',M7,L0,K4]
    exact forall_congr' fun j=>by omega
   rw[he] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
  have Hpad:=er (A:=A4) (fun j:Fin h8=>if w<=j.val then f0 p ⟨2*n-1-j.val,by omega⟩ ⟨0,by omega⟩ else fun _=>true)
   b2 (fun j=>by split_ifs;exact b0 ⟨_,_,rfl⟩;exact b2)
  have Hs0T0:Build A4 {fun x=>decide ((p x ⟨2*n+1,by omega⟩).val<c3 (k8 n m a o (p x) ⟨0,x0⟩))} ((2*n)*(6*n)*2):=by
   let pr (e:Fin ((2*n)*(6*n))):d4 (N0 n):=let q:=finProdFinEquiv.symm e;let s0:=q.1;let t:=(o1 n).symm q.2
    if s0.val<c3 t then an (f0 p ⟨2*n+1,by omega⟩ ⟨s0.val,by omega⟩) (pt ⟨0,x0⟩ t) else fun _=>false
   have H1:=au (A:=A4) pr 1 (fun e=>by
    dsimp only[pr];split_ifs;exact t7 (b0 ⟨_,_,rfl⟩) (inl (inl (b6 _ _)));exact d9 (s6 (Q1 f1)) Y3 Y3 (by omega))
   have H2:=w3 (A:=A4∪R0 pr) pr (inl f1) (fun e=>inr ⟨e,rfl⟩)
   have he:(fun x=>decide (∃ e:Fin ((2*n)*(6*n)),pr e x=true))=fun x=>decide ((p x ⟨2*n+1,by omega⟩).val<c3 (k8 n m a o (p x) ⟨0,x0⟩)):=by
    funext x;apply L5;simp only[L0]
    constructor
    . rintro⟨e,k⟩;dsimp only[pr] at k;by_cases y2:(finProdFinEquiv.symm e).1.val<c3 ((o1 n).symm (finProdFinEquiv.symm e).2)
      . rw[Q2 y2] at k;simp only[an,f0,pt,K8,L0] at k;rw[k.1,k.2];exact y2
      . rw[Q3 y2] at k;simp at k
    . intro y2;have r4:(p x ⟨2*n+1,by omega⟩).val<2*n:=lt_of_lt_of_le y2 (k7 _).2;refine⟨finProdFinEquiv (⟨(p x ⟨2*n+1,by omega⟩).val,r4⟩,o1 n (k8 n m a o (p x) ⟨0,x0⟩)),?_⟩;dsimp only[pr];simp only[M5,Q2 y2,an,f0,pt,decide_true,Bool.and_self]
   rw[he] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
  have Hcok:=er (A:=A4) colOkSig b2 (fun j=>inr (inr ⟨j,rfl⟩));have HlenLe:=ae (A:=A4) (inl (x1 ⟨2*n+1,by omega⟩))
  let cList (i:Fin 7):d4 (N0 n):=match i.val with
   | 0=>fun x=>decide (∃ s0:Fin (2*n),f0 p ⟨2*n+1,by omega⟩ ⟨s0.val,by omega⟩ x=true)
   | 1=>S393.Compiler.Build.or (f0 p ⟨2*n,by omega⟩ ⟨0,by omega⟩) (f0 p ⟨2*n,by omega⟩ ⟨1,by omega⟩)
   | 2=>fun x=>decide (∀ j:Fin m,0<(p x ⟨2*n-1-j.val,by omega⟩).val)
   | 3=>fun x=>decide (∀ j:Fin h8,(if w≤j.val then f0 p ⟨2*n-1-j.val,by omega⟩ ⟨0,by omega⟩ else fun _=>true) x=true)
   | 4=>fun x=>decide ((p x ⟨2*n+1,by omega⟩).val<c3 (k8 n m a o (p x) ⟨0,x0⟩))
   | 5=>fun x=>decide (∀ j:Fin m,colOkSig j x=true)
   | _=>nt (lenEqM ⟨2*n+1,by omega⟩)
  have H7:=q6 (q6 (q6 Hs0 Hb0) (q6 Hpos Hpad)) (q6 (q6 Hs0T0 Hcok) HlenLe)
  have Hall:=i7 H7 (er cList (inl b2) (fun i=>by
   fin_cases i
   . exact inr (inl (inl (inl rfl)))
   . exact inr (inl (inl (inr rfl)))
   . exact inr (inl (inr (inl rfl)))
   . exact inr (inl (inr (inr rfl)))
   . exact inr (inr (inl (inl rfl)))
   . exact inr (inr (inl (inr rfl)))
   . exact inr (inr (inr rfl))))
  have he:(fun x=>decide (∀ i:Fin 7,cList i x=true))=fun x=>ce n w b5 a g2 g1 b7 (p x):=by
   funext x;apply L5;unfold ce;simp only[L0]
   let i0:Fin 7:=⟨0,by decide⟩;let i1:Fin 7:=⟨1,by decide⟩;let i2:Fin 7:=⟨2,by decide⟩;let i3:Fin 7:=⟨3,by decide⟩;let i4:Fin 7:=⟨4,by decide⟩;let i5:Fin 7:=⟨5,by decide⟩;let i6:Fin 7:=⟨6,by decide⟩;have he7:(∀ i:Fin 7,cList i x=true)↔cList i0 x=true/\cList i1 x=true/\cList i2 x=true/\cList i3 x=true/\cList i4 x=true/\cList i5 x=true/\cList i6 x=true:=⟨fun h=>⟨h i0,h i1,h i2,h i3,h i4,h i5,h i6⟩,fun⟨a0,a1,a2,a3,a4,a5,a6⟩ i=>by fin_cases i<;>assumption⟩;rw[he7];dsimp only[cList,i0,i1,i2,i3,i4,i5,i6];simp only[L0];have h1:(∃ s0:Fin (2*n),f0 p ⟨2*n+1,by omega⟩ ⟨s0.val,by omega⟩ x=true)↔(p x ⟨2*n+1,by omega⟩).val<2*n:=⟨fun⟨s0,hs⟩=>by simp only[f0,L0] at hs;rw[hs];exact s0.isLt,fun y2=>⟨⟨_,y2⟩,by simp[f0]⟩⟩;have z:S393.Compiler.Build.or (f0 p ⟨2*n,by omega⟩ ⟨0,by omega⟩) (f0 p ⟨2*n,by omega⟩ ⟨1,by omega⟩) x=true↔(p x ⟨2*n,by omega⟩).val<2:=by simp only[S393.Compiler.Build.or,f0,V4,L0,K4];omega
   have h4:(∀ j:Fin h8,(if w≤j.val then f0 p ⟨2*n-1-j.val,by omega⟩ ⟨0,by omega⟩ else fun _=>true) x=true)↔(∀ j:Fin h8,w≤j.val->(p x ⟨2*n-1-j.val,by omega⟩).val=0):=forall_congr' fun j=>by
     by_cases r:w<=j.val
     . rw[Q2 r];simp only[f0,L0,K4,r,true_implies]
     . rw[Q3 r];simp only[r,false_implies]
   have h7:nt (lenEqM ⟨2*n+1,by omega⟩) x=true↔ab n m a o (p x)<=2*n:=by have p0:(n6 (⟨0,by omega⟩:Fin (2*n+2)) lenStep m x).val=min (ab n m a o (p x)) (2*n+1):=(by rw[b9 m Y3 x];unfold ab;congr 2;ext i;simp[i.isLt]);simp only[nt,lenEqM,K4,p0,Bool.not_eq_true',M7];omega
   simp only[h1,z,h4,h7,colOkSig,walkSig];exact⟨fun⟨a1,a2,a3,a4,a5,a6,a7⟩=>⟨a1,a2,a3,a4,a5,a6,a7⟩,fun⟨a1,a2,a3,a4,a5,a6,a7⟩=>⟨a1,a2,a3,a4,a5,a6,a7⟩⟩
  rw[he] at Hall;exact d9 Hall Y3 Y3 (by omega)
 let A5:=A4∪{fun x=>ce n w b5 a g2 g1 b7 (p x)}
 have Hpref:Build A A5
  (m*(6*n)+((6*n)*(m*((2*n+1)*((2*n+1)*2+(2*n+1))))+((6*n+1)+6*n+5)) +
  ((m*(2*(2*(6*n+1)+2))+(m+1)*5) +(m*((2*n+2)*((2*n+2)*(6*n+1)+(2*n+2)))+m*(2*(2*(6*n+1)+2)))) +
  ((2*n+1)+m*(1+6*n+6*n)) +
  (2*n+1+2*m+h8+(2*n)*(6*n)*2+m+1+7)):=by
  have h1:=q4 Hpt (q6 Hused HcolE);have z:=q4 h1 (d9 (q6 Hwalk (q6 HlenFSA HnpFSA)) (by rintro f ((hA|hm2)|hc2);exact inl hA;exact inr (inl hm2);exact inr (inr hc2)) Y3 Y3);have h3:=q4 z (d9 (q6 HremLen HcolOk) (by rintro f (((hA|hm2)|hc2)|h3);exact inl hA;exact inr (inl (inl hm2));exact inr (inl (inr hc2));exact inr (inr h3)) Y3 Y3);have h4:=q4 h3 (d9 Hpok (by rintro f ((((hA|hm2)|hc2)|h3)|h4);exact inl hA;exact inr (inl (inl (inl hm2)));exact inr (inl (inl (inr hc2)));exact inr (inl (inr h3));exact inr (inr h4)) Y3 Y3);refine aa h4 Y3 ?_ (by simp only[Q9,card_bool];omega);rintro f (((((hA|hm2)|hc2)|h3)|h4)|h5)
  . exact inl hA
  . exact inr (inl (inl (inl (inl hm2))))
  . exact inr (inl (inl (inl (inr hc2))))
  . exact inr (inl (inl (inr h3)))
  . exact inr (inl (inr h4))
  . exact inr (inr h5)
 have r0:(fun x=>decide (n6 false npStep m x=true))=fun x=>en n m a o (p x):=by
  funext x;rw[p1 m Y3 x];unfold en
  have x2:univ.filter (fun i:Fin m=>i.val<m/\c9 (k8 n m a o (p x) i)=false)=univ.filter (fun i:Fin m=>c9 (k8 n m a o (p x) i)=false):=(by ext i;simp[i.isLt]);rw[x2];cases decide ((univ.filter (fun i:Fin m=>c9 (k8 n m a o (p x) i)=false)).card %2=1)<;>rfl
 have Hcore:=mz n (w-m) (A:=A5)
  (hl.trans (M8.trans (M8.trans (M8.trans (M8.trans M8)))))
  (inl f1) (inl b2) (fun x=>cd n m a o (p x))
  (fun x t=>by unfold cd;exact (card_filter_le _ _).trans (by simp;exact o))
  (fun t u=>inl (inl (inl (inr (inl ⟨(t,u),Y2 _,rfl⟩)))))
  (walkSig m) h9 (fun x=>en n m a o (p x))
  (inl (inl (inr (inl ⟨⟨m,U2 m⟩,rfl⟩))))
  (inl (inl (inl (inr (inr rfl)))))
  (r0▸inl (inl (inr (inr (inr ⟨⟨m,U2 m⟩,true,rfl⟩)))))
  (fun x=>⟨2*n-ab n m a o (p x),by omega⟩)
  (fun rl=>inl (inr (inl ⟨rl,rfl⟩)))
 have Hcg:=i7 Hcore (ig (m:=4*n) (p:=fun x=>ce n w b5 a g2 g1 b7 (p x))
  (inl (inr rfl)) (fun j=>inr ⟨j,rfl⟩))
 refine d9 (i7 Hpref (d9 Hcg (by rintro f hf;exact inr hf) Y3 Y3)) Y3 Y3 ?_;unfold ba;have h1:m*(6*n)<=(2*n)*(6*n):=W4 _ o;have z:(6*n)*(m*((2*n+1)*((2*n+1)*2+(2*n+1))))<=(6*n)*((2*n)*((2*n+1)*((2*n+1)*2+(2*n+1)))):=W5 _ (W4 _ o);have h3:m*(2*(2*(6*n+1)+2))<=(2*n)*(2*(2*(6*n+1)+2)):=W4 _ o;have h4:m*((2*n+2)*((2*n+2)*(6*n+1)+(2*n+2)))<=(2*n)*((2*n+2)*((2*n+2)*(6*n+1)+(2*n+2))):=W4 _ o;have h5:m*(1+6*n+6*n)<=(2*n)*(1+6*n+6*n):=W4 _ o;have h6:(m+1)*5<=(2*n+1)*5:=W4 _ (by omega);have h7:h8<=2*n:=(by omega);omega
lemma kk (n:ℕ) (i:1<=n) {A:Set (d4 (N0 n))}
 (e:da n⊆A) (k:v5 n⊆A) (g:(fun _=>false)∈A) (f:(fun _=>true)∈A)
 (b:ℕ) (d:b<2*n) (p:u7 (N0 n) (2*n+2) (6*n+1)) (r:p5 p⊆A):
 Build A (R0 (a9 (4*n) (fun x=>u2 n i x b d (p x)))) (l6 n):=by
 have HokAll:=ot n k g f
 have Hmatch:Build A {fun x=>decide (∀ j:Fin (2*n+2),b≤j.val->p x j=m3 n j)} (2*n+2):=by
  have H:=er (A:=A) (fun j:Fin (2*n+2)=>if b<=j.val then f0 p j (m3 n j) else fun _=>true)
   f (fun j=>by split_ifs;exact r ⟨_,_,rfl⟩;exact f)
  have q:(fun x=>decide (∀ j:Fin (2*n+2),(if b≤j.val then f0 p j (m3 n j) else fun _=>true) x=true))=fun x=>decide (∀ j:Fin (2*n+2),b≤j.val->p x j=m3 n j):=by
   funext x;apply L5;simp only[L0]
   exact forall_congr' fun j=>by by_cases s:b<=j.val<;>simp[s,f0]
  rw[q] at H;exact H
 let B0:=A∪({v6 n}∪{fun x=>decide (∀ j:Fin (2*n+2),b≤j.val->p x j=m3 n j)})
 let c:d4 (N0 n):=fun x=>l8 n x && u5 n ⟨2*n,by unfold o8;omega⟩ x &&
  v6 n x && decide (∀ j:Fin (2*n+2),b≤j.val->p x j=m3 n j)
 have Hg0:Build B0 {c} 3:=qh (inl (e (inl (inl rfl)))) (inl (e (inl (inr ⟨_,rfl⟩)))) (inr (inl rfl)) (inr (inr rfl))
 have Hterm0:=ig (A:=B0∪{c}) (m:=4*n) (p:=c) (F:=fun _=>1) (inr rfl)
  (fun j=>by change (fun _=>(1:ℕ).testBit j.val)∈_;cases (1:ℕ).testBit j.val;exact inl (inl g);exact inl (inl f))
 have H0:Build A (R0 (a9 (4*n) (fun x=>if c x then 1 else 0))) (2*n*3+(2*n+2)+3+4*n):=d9 (i7 (q6 HokAll Hmatch) (i7 Hg0 Hterm0)) Y3 Y3 (by omega);let onK (a:Fin (2*n)):d4 (N0 n):=an (l8 n) (u5 n ⟨2*n-(a.val+1),by unfold o8;omega⟩);have HonK:Build A (R0 onK) (2*n):=(by simpa only[Nat.mul_one] using au onK 1 (fun a=>t7 (e (inl (inl rfl))) (e (inl (inr ⟨_,rfl⟩)))));let FK (a:Fin (2*n)) (x:F0 (N0 n)):ℕ:=t3 n (a.val+1) b i (by omega) (by omega) d x (p x)
 have HFK:Build A (m0 univ (fun a:Fin (2*n)=>R0 (a9 (4*n) (FK a)))) ((2*n)*(ba n+u1 n+4*n)):=by
  simpa only[Q9] using p7 (A:=A) (fun a:Fin (2*n)=>R0 (a9 (4*n) (FK a))) _
   (fun a=>jy n (a.val+1) b i (by omega) (by omega) d k g f p r)
 have HsumK:=gh (w:=4*n) (A:=A∪(R0 onK∪m0 univ (fun a:Fin (2*n)=>R0 (a9 (4*n) (FK a)))))
  onK FK (inl g) (inl f) (fun a=>inr (inl ⟨a,rfl⟩)) (fun a j=>inr (inr ⟨a,Y2 _,⟨j,rfl⟩⟩))
 have Hadd:=jv (A:=A∪(R0 (a9 (4*n) (fun x=>if c x then 1 else 0))∪R0 (a9 (4*n) (fun x=>∑ a:Fin (2*n),if onK a x then FK a x else 0))))
  (4*n) (fun x=>if c x then 1 else 0) (fun x=>∑ a:Fin (2*n),if onK a x then FK a x else 0)
  (inl g) (fun j=>inr (inl ⟨j,rfl⟩)) (fun j=>inr (inr ⟨j,rfl⟩))
 have q:(fun x=>(if c x then 1 else 0)+∑ a:Fin (2*n),if onK a x then FK a x else 0)=fun x=>u2 n i x b d (p x):=by
  funext x;unfold u2;congr 1
  . by_cases o:l8 n x=true/\u5 n ⟨2*n,by unfold o8;omega⟩ x=true/\v6 n x=true/\(∀ j:Fin (2*n+2),b≤j.val->p x j=m3 n j)
    . simp[c,o]
    . have l:c x=false:=(by apply Bool.eq_false_iff.mpr;intro h;apply o;simp only[c,K8,L0] at h;exact⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩);simp[l,o]
  . refine L3 rfl fun a _=>by simp[onK,an,FK]
 rw[q] at Hadd;exact d9 (i7 (q6 H0 (i7 (q6 HonK HFK) HsumK)) Hadd) Y3 Y3 (by unfold l6;simp;ring_nf;omega)
lemma nc (n:ℕ)(e:1<=n):fz (da n∪v5 n∪{fun _=>false,fun _=>true}) (4*n) (y0 n) (j5 n e):=by
 intro A o cut h6 p a;have z:da n⊆A:=(M8.trans M8).trans o;have v:v5 n⊆A:=(M9.trans M8).trans o;have r:(fun _=>false)∈A:=o (inr (inl rfl));have t:(fun _=>true)∈A:=o (inr (inr rfl))
 have g:∀ c (B:ℕ) (hc:2*n≤c) (k:c≤(2*n+2)),(∀ p':u7 (N0 n) (2*n+2) (6*n+1),p5 p'⊆A->Build A (R0 (a9 (4*n) (fun x=>j5 n e x (c-1) (p' x)))) B)->∀ p':u7 (N0 n) (2*n+2) (6*n+1),p5 p'⊆A->Build A (R0 (a9 (4*n) (fun x=>j5 n e x c (p' x)))) ((6*n+1)*B+(6*n+1)*(9*(4*n))):=by
  intro c B hc k m p' h8;let j:Fin (2*n+2):=⟨c-1,by omega⟩;let F (d:Fin (6*n+1)) (x:F0 (N0 n)):=j5 n e x (c-1) (fg p' j d x)
  have HF:Build A (m0 univ (fun d:Fin (6*n+1)=>R0 (a9 (4*n) (F d)))) ((6*n+1)*B):=by
   simpa only[Q9] using p7 (A:=A) (fun d:Fin (6*n+1)=>R0 (a9 (4*n) (F d))) B
    (fun d=>m (fg p' j d) (fv p' j d h8 r t))
  have HS:=dh (A:=A∪m0 univ (fun d:Fin (6*n+1)=>R0 (a9 (4*n) (F d)))) (w:=4*n)
   univ F (inl r) (inl t) (fun d _ i=>inr (q3 (i:=d) ⟨i,rfl⟩))
  have u:(fun x=>∑ d:Fin (6*n+1),F d x)=fun x=>j5 n e x c (p' x):=by funext x;rw[j5,Q8 (by omega),L7 k];rfl
  rw[u] at HS;simpa only[W2,Q9] using i7 HF HS
 have b:∀ c (f:c<2*n) (p':u7 (N0 n) (2*n+2) (6*n+1)),p5 p'⊆A->Build A (R0 (a9 (4*n) (fun x=>j5 n e x c (p' x)))) (l6 n):=fun c f p' h8=>by have u:(fun x=>j5 n e x c (p' x))=fun x=>u2 n e x c f (p' x):=(by funext x;rw[j5,L7 f]);rw[u];exact kk n e z v r t c f p' h8
 have h0:1<=(6*n+1):=(by omega);have q:∀ p',p5 p'⊆A->Build A (R0 (a9 (4*n) (fun x=>j5 n e x (2*n) (p' x)))) ((6*n+1)*l6 n+(6*n+1)*(9*(4*n))):=g (2*n) (l6 n) Y3 (by omega) (fun p' h8=>b (2*n-1) (by omega) p' h8)
 have h:∀ p',p5 p'⊆A->Build A (R0 (a9 (4*n) (fun x=>j5 n e x (2*n+1) (p' x))))
  ((6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n))):=
  g (2*n+1) _ (by omega) (by omega) (fun p' h8=>by simpa only[Nat.add_sub_cancel] using q p' h8)
 have s:∀ p',p5 p'⊆A->Build A (R0 (a9 (4*n) (fun x=>j5 n e x (2*n+2) (p' x)))) (y0 n):=g (2*n+2) _ (by omega) (by omega) (fun p' h8=>by rw[show 2*n+2-1=2*n+1 by omega];exact h p' h8);by_cases f:cut<2*n
 . refine d9 (b cut f p a) Y3 Y3 ?_;unfold y0;have y:l6 n<=(6*n+1)*l6 n:=Nat.le_mul_of_pos_left _ (by omega);have h2:(6*n+1)*l6 n<=(6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n))):=Nat.le_mul_of_pos_left _ (by omega)|> le_trans (by omega);have h3:(6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))<=(6*n+1)*((6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n))):=le_trans (Nat.le_mul_of_pos_left _ (by omega)) (W5 _ (by omega));omega
 . have l:cut=2*n\/cut=2*n+1\/cut=2*n+2:=by omega
   rcases l with rfl|rfl|rfl
   . refine d9 (q p a) Y3 Y3 ?_;unfold y0;have y:(6*n+1)*l6 n+(6*n+1)*(9*(4*n))<=(6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n))):=Nat.le_mul_of_pos_left _ (by omega);have h2:(6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))<=(6*n+1)*((6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n))):=le_trans (Nat.le_mul_of_pos_left _ (by omega)) (W5 _ (by omega));omega
   . refine d9 (h p a) Y3 Y3 ?_;unfold y0;have y:(6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n))<=(6*n+1)*((6*n+1)*((6*n+1)*l6 n+(6*n+1)*(9*(4*n)))+(6*n+1)*(9*(4*n))):=Nat.le_mul_of_pos_left _ (by omega);omega
   . exact s p a
end Query392
namespace Front392
open S399 StageA RingCode SuffixDP BaseD Query392 BuildExt
open S393.Compiler.Build S393.Front
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open scoped BigOperators
def et (n:ℕ):ℕ:=2+(n+1)*(n+1)*(2*n+1)
def pl (n:ℕ):ℕ:=et n+2*n
def qu (n:ℕ):ℕ:=et n+4*n
def dn (n:ℕ)(v:BV n):Fin (N0 n):=⟨et n+(if v.1 then n+v.2.val else v.2.val),by unfold N0 et;have:=v.2.isLt;split_ifs<;>omega⟩
def lz (n:ℕ)(v:BV n):Fin (N0 n):=⟨pl n+(if v.1 then n+v.2.val else v.2.val),by unfold N0 pl et;have:=v.2.isLt;split_ifs<;>omega⟩
def qv (n:ℕ)(k:Fin (4*n)):Fin (N0 n):=⟨qu n+k.val,by unfold N0 qu et;omega⟩
def e7 (n:ℕ)(x:F0 (N0 n))(v:BV n):V9 Y0:=if x (dn n v) then some (x (lz n v)) else none
noncomputable def bf (n:ℕ)(x:F0 (N0 n)):ℕ:=S393.fs (fun k:Fin (4*n)=>x (qv n k))
lemma jc {n:ℕ}(p:P0 n)(f:Fin (f4 n p).length)(m:Fin (2*n)):(f4 n p).get f=m↔(p (d8 n m)).isSome=true/\(univ.filter (fun i:Fin (2*n)=>i.val<m.val/\(p (d8 n i)).isSome=true)).card=f.val:=by
 have e:=m9 n p;have g:=t8 n p
 have c:∀ a b:Fin (f4 n p).length,((f4 n p).get a).val<((f4 n p).get b).val↔a.val<b.val:=fun a b=>by
  rw[pairwise_iff_get] at g
  exact⟨fun h=>by by_contra hge;rcases lt_or_eq_of_le (not_lt.mp hge) with l|h2;exact absurd (g b a l) (by omega);exact Nat.lt_irrefl _ (L6 h2▸h),fun h=>g a b h⟩
 have d:∀ r:Fin (f4 n p).length,(univ.filter (fun i:Fin (2*n)=>i.val<((f4 n p).get r).val/\(p (d8 n i)).isSome=true)).card=r.val:=fun r=>by
  have o:univ.filter (fun i:Fin (2*n)=>i.val<((f4 n p).get r).val/\(p (d8 n i)).isSome=true)=(univ.filter (fun a:Fin (f4 n p).length=>a.val<r.val)).image (fun a=>(f4 n p).get a):=by ext i;simp only[L4,Y2,Q0,X5];exact⟨fun⟨hlt,hs⟩=>by obtain⟨a,rfl⟩:=List.mem_iff_get.mp ((e i).mpr hs);exact⟨a,(c a r).mp hlt,rfl⟩,fun⟨a,hlt,k⟩=>k▸⟨(c a r).mpr hlt,(e _).mp (get_mem _ _)⟩⟩
  rw[o,card_image_of_injective _ (fun a b h=>by
   by_contra hne;rcases lt_or_gt_of_ne (fun j=>hne (L6 j)) with l|h2
   . exact Nat.lt_irrefl _ (h▸(c a b).mpr l)
   . exact Nat.lt_irrefl _ (h▸(c b a).mpr h2))]
  exact (card_bij (fun(a:Fin (f4 n p).length) _=>a.val) (fun a k=>by simp only[L4,Y2,Q0,mem_range] at k ⊢;exact k) (fun _ _ _ _ h=>L6 h) (fun v j=>⟨⟨v,by rw[mem_range] at j;have:=r.isLt;omega⟩,by simp only[L4,Y2,Q0];exact mem_range.mp j,rfl⟩)).trans (W1 r.val)
 exact⟨fun h=>h▸⟨(e _).mp (get_mem _ _),d f⟩,fun⟨hs,hc⟩=>by
  obtain⟨r,rfl⟩:=List.mem_iff_get.mp ((e m).mpr hs)
  exact Q6 (f4 n p).get (L6 (by rw[<-d r,hc])).symm⟩
def de (n:ℕ):ℕ:=(2*n)*((2*n+1)*((2*n+1)*2+(2*n+1)))+(2*n)*(2*n)+2*n +(2*n+2)*((6*n+1)*((2*n)*(2*n)*(2*n)*4*5+4*n+4))
lemma qq (n:ℕ)(hn:1<=n):Build (jh (N0 n)) (p5 (fun x=>e5 n (e7 n x))) (de n):=by
 let A0:=jh (N0 n);have b8:(fun _=>false)∈A0:=inr (inl rfl);have e0:(fun _=>true)∈A0:=inr (inr rfl);let isP (m:Fin (2*n)):d4 (N0 n):=fun x=>x (dn n (d8 n m));let valP (m:Fin (2*n)):d4 (N0 n):=fun x=>x (lz n (d8 n m));have a3:∀ m,isP m∈A0:=fun m=>inl ⟨_,rfl⟩;have v1:∀ m,valP m∈A0:=fun m=>inl ⟨_,rfl⟩;let cntStep (j:ℕ) (c:Fin (2*n+1)) (x:F0 (N0 n)):Fin (2*n+1):=if hj:j<2*n then if isP ⟨j,hj⟩ x then ⟨min (c.val+1) (2*n),by omega⟩ else c else c
 have x1:∀ j (hj:j≤2*n) x,(n6 (⟨0,by omega⟩:Fin (2*n+1)) cntStep j x).val=(univ.filter (fun i:Fin (2*n)=>i.val<j/\isP i x=true)).card:=fun j hj x=>by
  induction j with
  | zero=>simp[n6]
  | succ j ih=>
   have h8:j<2*n:=by omega
   have v2:(univ.filter (fun i:Fin (2*n)=>i.val<j/\isP i x=true)).card<2*n:=by
    have g2:univ.filter (fun i:Fin (2*n)=>i.val<j/\isP i x=true)⊆univ.filter (fun i:Fin (2*n)=>i.val<j):=fun i o=>by simp at o ⊢;exact o.1
    have hc:(univ.filter (fun i:Fin (2*n)=>i.val<j)).card=j:=(card_bij (fun(i:Fin (2*n)) _=>i.val) (fun i o=>by simp at o ⊢;exact o)
      (fun _ _ _ _ h=>L6 h) (fun v hv=>⟨⟨v,by rw[mem_range] at hv;omega⟩,by simp[mem_range.mp hv],rfl⟩)).trans (W1 j)
    have:=card_le_card g2;omega
   have g1:univ.filter (fun i:Fin (2*n)=>i.val<j+1/\isP i x=true)=if isP ⟨j,h8⟩ x then insert ⟨j,h8⟩ (univ.filter (fun i:Fin (2*n)=>i.val<j/\isP i x=true))
    else univ.filter (fun i:Fin (2*n)=>i.val<j/\isP i x=true):=by
    ext i;split_ifs with hp<;>simp only[L4,Y2,Q0,X3,K4]
    . exact⟨fun⟨w,y⟩=>if c0:i.val=j then inl c0 else inr ⟨by omega,y⟩,fun h=>h.elim (fun c0=>⟨by omega,by rw[show i=⟨j,h8⟩ from L6 c0];exact hp⟩) (fun⟨w,y⟩=>⟨by omega,y⟩)⟩
    . exact⟨fun⟨w,y⟩=>⟨by by_contra hge;exact hp (by rw[<-show i=⟨j,h8⟩ from L6 (by dsimp only;omega)];exact y),y⟩,fun⟨w,y⟩=>⟨by omega,y⟩⟩
   rw[n6];dsimp only[cntStep];rw[L7 h8,g1];split_ifs with hp
   . rw[W9 (by simp)];dsimp only;rw[ih (by omega)];omega
   . exact ih (by omega)
 have Hcnt:Build A0 (dd (⟨0,by omega⟩:Fin (2*n+1)) cntStep (2*n)) ((2*n)*((2*n+1)*((2*n+1)*2+(2*n+1)))):=by
  simpa only[Q9] using dm b8 e0 (⟨0,by omega⟩:Fin (2*n+1)) cntStep (2*n) 1 (fun j hj c c'=>by
   by_cases w:(⟨min (c.val+1) (2*n),by omega⟩:Fin (2*n+1))=c'<;>by_cases y:c=c'
   . have p:(fun x=>decide (cntStep j c x=c'))=fun _=>true:=(by funext x;apply L5;simp only[L0];dsimp only[cntStep];rw[L7 hj];split_ifs<;>simp_all);rw[p];exact d9 (s6 (Q1 e0)) Y3 Y3 (by omega)
   . have p:(fun x=>decide (cntStep j c x=c'))=isP ⟨j,hj⟩:=(by funext x;apply L5;simp only[L0];dsimp only[cntStep];rw[L7 hj];split_ifs<;>simp_all);rw[p];exact d9 (s6 (Q1 (a3 ⟨j,hj⟩))) Y3 Y3 (by omega)
   . have p:(fun x=>decide (cntStep j c x=c'))=nt (isP ⟨j,hj⟩):=(by funext x;apply L5;simp only[nt,Bool.not_eq_true',L0];dsimp only[cntStep];rw[L7 hj];split_ifs<;>simp_all);rw[p];exact ae (a3 ⟨j,hj⟩)
   . have p:(fun x=>decide (cntStep j c x=c'))=fun _=>false:=by funext x;apply L5;simp only[J5,L0];dsimp only[cntStep];rw[L7 hj];split_ifs<;>simp_all
     rw[p];exact d9 (s6 (Q1 b8)) Y3 Y3 (by omega))
 let cntEq (j:ℕ) (c:Fin (2*n+1)):d4 (N0 n):=fun x=>decide (n6 (⟨0,by omega⟩:Fin (2*n+1)) cntStep j x=c);let A1:=A0∪dd (⟨0,by omega⟩:Fin (2*n+1)) cntStep (2*n);let posS (a m:Fin (2*n)):d4 (N0 n):=an (isP m) (cntEq m.val ⟨a.val,by omega⟩)
 have Hpos:Build A1 (m0 univ (fun q:Fin (2*n)×Fin (2*n)=>{posS q.1 q.2})) ((2*n)*(2*n)):=by
  simpa only[J3,Q9,Nat.mul_one] using
   p7 (A:=A1) (fun q:Fin (2*n)×Fin (2*n)=>{posS q.1 q.2}) 1 (fun⟨a,m⟩=>t7 (inl (a3 m)) (inr ⟨⟨m.val,by omega⟩,⟨a.val,by omega⟩,rfl⟩))
 have Hnv:Build A1 (R0 (fun m:Fin (2*n)=>nt (valP m))) (2*n):=(by simpa only[Nat.mul_one] using au (fun m:Fin (2*n)=>nt (valP m)) 1 (fun m=>ae (inl (v1 m))));let A2:=A1∪(m0 univ (fun q:Fin (2*n)×Fin (2*n)=>{posS q.1 q.2})∪R0 (fun m:Fin (2*n)=>nt (valP m)));have u:(fun _=>false)∈A2:=inl (inl b8)
 have b5:∀ x,(f4 n (e7 n x)).length=(univ.filter (fun i:Fin (2*n)=>isP i x=true)).card:=fun x=>by
  have w:=bo n (e7 n x)
  have y:e3 (e7 n x)=(univ.filter (fun i:Fin (2*n)=>isP i x=false)).card:=by
   unfold e3;refine card_bij (fun v _=>(e8 n).symm v) (fun v hv=>?_) (fun _ _ _ _ h=>(e8 n).symm.injective h) (fun i o=>⟨d8 n i,?_,M5 (e8 n) i⟩)
   . simp only[L4,Y2,Q0,e7,isP] at hv ⊢;rw[show d8 n ((e8 n).symm v)=v from (e8 n).apply_symm_apply v];cases hb:x (dn n v)<;>simp[hb] at hv ⊢
   . simp only[L4,Y2,Q0,isP] at o;simp[e7,o]
  have b9:=card_filter_add_card_filter_not (s:=(univ:V7 (Fin (2*n)))) (fun i=>isP i x=true);have g0:univ.filter (fun i:Fin (2*n)=>¬ isP i x=true)=univ.filter (fun i:Fin (2*n)=>isP i x=false):=(by ext i;simp[Bool.not_eq_true]);rw[g0,<-y] at b9;simp at b9;omega
 have t:∀(c:Fin (2*n+1)) x,cntEq (2*n) c x=decide ((f4 n (e7 n x)).length=c.val):=fun c x=>by apply L5;simp only[cntEq,K4,x1 (2*n) Y3 x,b5 x,L0];have b4:univ.filter (fun i:Fin (2*n)=>i.val<2*n/\isP i x=true)=univ.filter (fun i:Fin (2*n)=>isP i x=true):=(by ext i;simp[i.isLt]);rw[b4]
 have f:∀(a m:Fin (2*n)) x,posS a m x=true↔∃ h:a.val<(f4 n (e7 n x)).length,(f4 n (e7 n x)).get ⟨a.val,h⟩=m:=fun a m x=>by
  conv_lhs=>simp only[posS,an,cntEq,K4,x1 m.val (le_of_lt m.isLt) x,K8,L0]
  have a1:∀ i,(e7 n x (d8 n i)).isSome=isP i x:=fun i=>by unfold e7 isP;cases x (dn n (d8 n i))<;>rfl
  constructor
  . rintro⟨hm,hc⟩;obtain⟨r,hr⟩:=List.mem_iff_get.mp ((m9 n (e7 n x) m).mpr (by rw[a1];exact hm));have r1:r.val=a.val:=(by rw[<-((jc (e7 n x) r m).mp hr).2,<-hc];congr 1;ext i;simp[a1]);exact⟨by omega,by rw[<-hr];congr 1;exact L6 r1.symm⟩
  . rintro⟨z,k1⟩;have d0:=(jc (e7 n x) ⟨a.val,z⟩ m).mp k1;exact⟨by rw[<-a1];exact d0.1,by rw[<-d0.2];congr 1;ext i;simp[a1]⟩
 have l:∀ x (r:Fin (f4 n (e7 n x)).length),(e7 n x (d8 n ((f4 n (e7 n x)).get r))).getD false=valP ((f4 n (e7 n x)).get r) x:=fun x r=>by
  have hm:=(m9 n (e7 n x) _).mp (get_mem _ r);unfold e7 at hm ⊢;unfold valP;cases hb:x (dn n (d8 n ((f4 n (e7 n x)).get r)))<;>simp_all
 have Hdig:=p7 (A:=A2) (fun q:Fin (2*n+2)×Fin (6*n+1)=>{f0 (fun x=>e5 n (e7 n x)) q.1 q.2})
  ((2*n)*(2*n)*(2*n)*4*5+4*n+4) (fun⟨j,d⟩=>by
   by_cases a0:j.val=2*n+1
   . have d1:j=⟨2*n+1,by omega⟩:=L6 a0;rw[d1];by_cases a4:d.val=2*n
     . have p:cntEq (2*n) ⟨0,by omega⟩=f0 (fun x=>e5 n (e7 n x)) ⟨2*n+1,by omega⟩ d:=by
        funext x;apply L5;rw[t];simp only[f0,e5,L0,K4]
        by_cases e:(f4 n (e7 n x)).length=0
        . rw[L7 e];simp[m3,a4,e]
        . rw[Q8 e];have:=((f4 n (e7 n x)).get ⟨0,K2 e⟩).isLt;simp[e,a4];omega
       rw[<-p];exact d9 (s6 (Q1 (inl (inr ⟨⟨2*n,U2 _⟩,⟨0,by omega⟩,rfl⟩)))) Y3 Y3 (by omega)
     . by_cases c1:d.val<2*n
       . have p:posS ⟨0,by omega⟩ ⟨d.val,c1⟩=f0 (fun x=>e5 n (e7 n x)) ⟨2*n+1,by omega⟩ d:=by
          funext x;apply L5;rw[f];simp only[f0,e5,L0]
          by_cases e:(f4 n (e7 n x)).length=0
          . rw[L7 e];simp[e,m3,K4,Ne.symm a4]
          . rw[Q8 e];simp[K4,show 0<(f4 n (e7 n x)).length by omega]
         rw[<-p];exact d9 (s6 (Q1 (inr (inl ⟨(⟨0,by omega⟩,⟨d.val,c1⟩),Y2 _,rfl⟩)))) Y3 Y3 (by omega)
       . have p:(fun _:F0 (N0 n)=>false)=f0 (fun x=>e5 n (e7 n x)) ⟨2*n+1,by omega⟩ d:=by
          funext x;apply L5;simp only[J5,false_iff,f0,e5,L0,K4]
          by_cases e:(f4 n (e7 n x)).length=0
          . rw[L7 e];simp[m3];omega
          . rw[Q8 e];have:=((f4 n (e7 n x)).get ⟨0,K2 e⟩).isLt;simp;omega
         rw[<-p];exact d9 (s6 (Q1 u)) Y3 Y3 (by omega)
   . by_cases b0:j.val=2*n
     . have d1:j=⟨2*n,by omega⟩:=L6 b0;rw[d1];by_cases x0:d.val=0
       . let term (m:Fin (2*n)):d4 (N0 n):=an (posS ⟨0,by omega⟩ m) (nt (valP m));have H1:=au (A:=A2) term 1 (fun m=>t7 (inr (inl ⟨(⟨0,by omega⟩,m),Y2 _,rfl⟩)) (inr (inr ⟨m,rfl⟩)));have H2:=w3 (A:=A2∪R0 term) term (inl u) (fun m=>inr ⟨m,rfl⟩);have H3:=i7 H1 (i7 H2 (gg (inl (inl (inl (inr ⟨⟨2*n,U2 _⟩,⟨0,by omega⟩,rfl⟩)))) (inr rfl)))
         have p:S393.Compiler.Build.or (cntEq (2*n) ⟨0,by omega⟩) (fun x=>decide (∃ m:Fin (2*n),term m x=true))=f0 (fun x=>e5 n (e7 n x)) ⟨2*n,by omega⟩ d:=by
          funext x;apply L5;simp only[S393.Compiler.Build.or,t,V4,L0,f0,e5]
          by_cases e:(f4 n (e7 n x)).length=0
          . rw[L7 e];simp[e,m3,K4,x0]
          . rw[Q8 e];simp only[e,false_or,show ¬ 2*n=2*n+1 by omega,↓reduceIte,K4,x0,l];constructor
            . rintro⟨m,hm⟩;simp only[term,an,nt,f,K8,Bool.not_eq_true'] at hm;obtain⟨⟨_,rfl⟩,p1⟩:=hm;simpa[get_eq_getElem] using p1
            . intro e2;refine⟨(f4 n (e7 n x)).get ⟨0,K2 e⟩,?_⟩;simp only[term,an,nt,f,K8,Bool.not_eq_true'];exact⟨⟨K2 e,trivial⟩,by simp only[get_eq_getElem] at e2 ⊢;cases hb:valP _ x<;>simp[hb] at e2 ⊢⟩
         rw[p] at H3;exact d9 H3 Y3 Y3 (by omega)
       . by_cases f1:d.val=1
         . let term (m:Fin (2*n)):d4 (N0 n):=an (posS ⟨0,by omega⟩ m) (valP m);have H1:=au (A:=A2) term 1 (fun m=>t7 (inr (inl ⟨(⟨0,by omega⟩,m),Y2 _,rfl⟩)) (inl (inl (v1 m))));have H2:=w3 (A:=A2∪R0 term) term (inl u) (fun m=>inr ⟨m,rfl⟩)
           have p:(fun x=>decide (∃ m:Fin (2*n),term m x=true))=f0 (fun x=>e5 n (e7 n x)) ⟨2*n,by omega⟩ d:=by
            funext x;apply L5;simp only[L0,f0,e5]
            by_cases e:(f4 n (e7 n x)).length=0
            . rw[L7 e];simp only[m3,show ¬ 2*n=2*n+1 by omega,↓reduceIte,K4,f1,show ¬ (0:ℕ)=1 by decide,iff_false];rintro⟨m,hm⟩;simp only[term,an,f,K8] at hm;obtain⟨⟨r7,_⟩,_⟩:=hm;omega
            . rw[Q8 e];simp only[show ¬ 2*n=2*n+1 by omega,↓reduceIte,K4,f1,l];constructor
              . rintro⟨m,hm⟩;simp only[term,an,f,K8] at hm;obtain⟨⟨_,rfl⟩,q2⟩:=hm;simpa[get_eq_getElem] using q2
              . intro e1;refine⟨(f4 n (e7 n x)).get ⟨0,K2 e⟩,?_⟩;simp only[term,an,f,K8];exact⟨⟨K2 e,trivial⟩,by simp only[get_eq_getElem] at e1 ⊢;cases hb:valP _ x<;>simp[hb] at e1 ⊢⟩
           rw[p] at H2;exact d9 (i7 H1 H2) Y3 Y3 (by omega)
         . have p:(fun _:F0 (N0 n)=>false)=f0 (fun x=>e5 n (e7 n x)) ⟨2*n,by omega⟩ d:=by
            funext x;apply L5;simp only[J5,false_iff,f0,e5,L0,K4]
            by_cases e:(f4 n (e7 n x)).length=0
            . rw[L7 e];simp[m3];omega
            . rw[Q8 e];simp only[show ¬ 2*n=2*n+1 by omega,↓reduceIte];cases (e7 n x _).getD false<;>simp<;>omega
           rw[<-p];exact d9 (s6 (Q1 u)) Y3 Y3 (by omega)
     . set a:=2*n-1-j.val;have h8:j.val<2*n:=(by have:=j.isLt;omega);have y2:a<2*n:=(by omega);by_cases x0:d.val=0
       . have H:=w3 (A:=A2) (fun c:Fin (2*n+1)=>if c.val<=a then cntEq (2*n) c else fun _=>false)
          u (fun c=>by split_ifs;exact inl (inr ⟨⟨2*n,U2 _⟩,c,rfl⟩);exact u)
         have p:(fun x=>decide (∃ c:Fin (2*n+1),(if c.val≤a then cntEq (2*n) c else fun _=>false) x=true))=f0 (fun x=>e5 n (e7 n x)) j d:=by
          funext x;apply L5;simp only[L0,f0,e5]
          have p0:=af n (e7 n x)
          have a5:(∃ c:Fin (2*n+1),(if c.val≤a then cntEq (2*n) c else fun _=>false) x=true)↔(f4 n (e7 n x)).length≤a:=by
           constructor
           . rintro⟨c,hc⟩;by_cases v2:c.val<=a
             . rw[Q2 v2,t] at hc;simp only[L0] at hc;omega
             . rw[Q3 v2] at hc;simp at hc
           . intro v2;exact⟨⟨(f4 n (e7 n x)).length,by omega⟩,by rw[Q2 v2,t];simp⟩
          rw[a5];by_cases e:(f4 n (e7 n x)).length=0
          . rw[L7 e];simp[e,m3,a0,K4,x0]
          . rw[Q8 e];simp only[a0,b0,↓reduceIte,K4,x0];by_cases o:a<(f4 n (e7 n x)).length
            . rw[L7 o];exact iff_of_false (by omega) (fun h=>absurd h (ne_of_gt (o0 _)))
            . rw[Q8 o];have v2:(f4 n (e7 n x)).length<=a:=Nat.le_of_not_lt o;simp[v2]
         rw[p] at H;exact d9 H Y3 Y3 (by omega)
       . let comb (q:Fin (2*n)×Fin (2*n)×Fin (2*n)×Y0×Y0):d4 (N0 n):=let k:=q.1.val+1;let b:=q.2.1;let g:=q.2.2.1;let b1:=q.2.2.2.1;let b2:=q.2.2.2.2
          let h3:=if b.val<g.val then g.val-b.val else 2*n-b.val+g.val
          if w:a<k/\1<=h3/\h3<=2*n then if m5 (bg n h3 (decide (b.val %2=1)) (decide (b1=b2)) w.2.1 w.2.2)=d then let h7:Fin (2*n):=⟨(a+k-1) %k,by have:=M1 (a+k-1) (by omega:0<k);have:=q.1.isLt;omega⟩
            fun x=>cntEq (2*n) ⟨k,by have:=q.1.isLt;omega⟩ x && posS h7 b x && posS ⟨a,y2⟩ g x &&
             (if b1 then valP b x else nt (valP b) x) && (if b2 then valP g x else nt (valP g) x)
           else fun _=>false
          else fun _=>false
         let E:=Fin (2*n)×Fin (2*n)×Fin (2*n)×Y0×Y0
         have Hcomb:Build A2 (R0 (fun i:Fin (W0 E)=>comb ((equivFin E).symm i))) (W0 E*4):=au (fun i=>comb ((equivFin E).symm i)) 4 (fun i=>by
           rcases (equivFin E).symm i with ⟨k0,b,g,b1,b2⟩;dsimp only[comb]
           let k:=k0.val+1;let h3:=if b.val<g.val then g.val-b.val else 2*n-b.val+g.val;by_cases w:a<k/\1<=h3/\h3<=2*n
           . rw[L7 w];by_cases y:m5 (bg n h3 (decide (b.val %2=1)) (decide (b1=b2)) w.2.1 w.2.2)=d
             . rw[Q2 y];have h4:(fun x=>if b1 then valP b x else nt (valP b) x)∈A2:=by cases b1;exact inr (inr ⟨b,rfl⟩);exact inl (inl (v1 b))
               have h5:(fun x=>if b2 then valP g x else nt (valP g) x)∈A2:=by cases b2;exact inr (inr ⟨g,rfl⟩);exact inl (inl (v1 g))
               let h7:Fin (2*n):=⟨(a+k-1) %k,by have:=M1 (a+k-1) (by dsimp only[k];omega:0<k);have:=k0.isLt;omega⟩
               exact i7 (qh (inl (inr ⟨⟨2*n,U2 _⟩,⟨k,by have:=k0.isLt;dsimp only[k];omega⟩,rfl⟩))
                (inr (inl ⟨(h7,b),Y2 _,rfl⟩))
                (inr (inl ⟨(⟨a,y2⟩,g),Y2 _,rfl⟩)) h4) (t7 (inr rfl) (inl h5))
             . rw[Q3 y];exact d9 (s6 (Q1 u)) Y3 Y3 (by omega)
           . rw[Q8 w];exact d9 (s6 (Q1 u)) Y3 Y3 (by omega))
         have Hany:=w3 (A:=A2∪R0 _) (fun i:Fin (W0 E)=>comb ((equivFin E).symm i)) (inl u) (fun i=>inr ⟨i,rfl⟩)
         have p:(fun x=>decide (∃ i:Fin (W0 E),comb ((equivFin E).symm i) x=true))=f0 (fun x=>e5 n (e7 n x)) j d:=by
          funext x;apply L5;simp only[L0,f0,e5]
          constructor
          . rintro⟨i,o⟩;rcases hq:(equivFin E).symm i with ⟨k0,b,g,b1,b2⟩;rw[hq] at o
            dsimp only[comb] at o;let k:=k0.val+1;let h3:=if b.val<g.val then g.val-b.val else 2*n-b.val+g.val;by_cases w:a<k/\1<=h3/\h3<=2*n
            . rw[L7 w] at o;by_cases y:m5 (bg n h3 (decide (b.val %2=1)) (decide (b1=b2)) w.2.1 w.2.2)=d
              . rw[Q2 y] at o;simp only[K8,t,f,L0] at o;obtain⟨⟨⟨⟨d2,_,b7⟩,_,f2⟩,b3⟩,a7⟩:=o;rw[Q8 (by omega),Q3 a0,Q3 b0,L7 (by omega)];have hm1':(f4 n (e7 n x)).get ⟨(2*n-1-j.val+(f4 n (e7 n x)).length-1) %(f4 n (e7 n x)).length,M1 _ (by omega)⟩=b:=(Q6 (f4 n (e7 n x)).get (L6 (by dsimp only[a];rw[d2]))).trans b7;have hb1':valP b x=b1:=by cases b1<;>simp[nt] at b3 ⊢<;>exact b3
                have hb2':valP g x=b2:=by cases b2<;>simp[nt] at a7 ⊢<;>exact a7
                dsimp only[a] at f2;rw[l,l];simp only[hm1',f2,hb1',hb2'];exact y
              . rw[Q3 y] at o;simp at o
            . rw[Q8 w] at o;simp at o
          . intro h6;by_cases e:(f4 n (e7 n x)).length=0
            . rw[L7 e] at h6;exfalso;simp[m3,a0,K4] at h6;exact x0 h6.symm
            . rw[Q8 e] at h6;simp only[a0,b0,↓reduceIte] at h6;by_cases z:a<(f4 n (e7 n x)).length
              . rw[L7 z] at h6;set k:=(f4 n (e7 n x)).length;have r8:=af n (e7 n x);set b:=(f4 n (e7 n x)).get ⟨(a+k-1) %k,M1 _ (by omega)⟩;set g:=(f4 n (e7 n x)).get ⟨a,z⟩;refine⟨equivFin E (⟨k-1,by omega⟩,b,g,valP b x,valP g x),?_⟩;rw[M5];dsimp only[comb];rw[l,l] at h6
                have a2:1<=(if b.val<g.val then g.val-b.val else 2*n-b.val+g.val)/\(if b.val<g.val then g.val-b.val else 2*n-b.val+g.val)<=2*n:=by
                 have b6:=t8 n (e7 n x);rw[pairwise_iff_get] at b6;have r2:=b.isLt;have r3:=g.isLt;split_ifs with p2;· omega
                 . by_cases r0:a=0
                   . have:g.val<=b.val:=by
                      by_cases hk1':k=1;· rw[show b=g from Q6 (f4 n (e7 n x)).get (L6 (by dsimp only;simp[hk1'];omega))]
                      . exact le_of_lt (b6 ⟨a,z⟩ ⟨(a+k-1) %k,M1 _ (by omega)⟩ (by show a<(a+k-1) %k;rw[r0,zero_add,L8 (by omega)];omega))
                     omega
                   . exfalso;exact p2 (b6 ⟨(a+k-1) %k,M1 _ (by omega)⟩ ⟨a,z⟩ (by show (a+k-1) %k<a;rw[show a+k-1=(a-1)+k by omega,M2,L8 (by omega)];omega))
                rw[L7 ⟨by omega,a2.1,a2.2⟩,Q2 h6];simp only[K8,t,f,L0];refine⟨⟨⟨⟨by omega,by have:=M1 (a+(k-1+1)-1) (by omega:0<k-1+1);omega,by dsimp only[b];congr 1;exact L6 (by simp[show k-1+1=k by omega])⟩,z,rfl⟩,by cases hb:valP b x<;>simp[nt,hb]⟩,by cases hb:valP g x<;>simp[nt,hb]⟩
              . rw[Q8 z] at h6;exfalso;exact x0 (Q6 Fin.val h6).symm
         rw[p] at Hany;refine d9 (i7 Hcomb Hany) Y3 Y3 ?_;have:W0 E=(2*n)*(2*n)*(2*n)*4:=by simp[E,Z3]
         rw[this];omega)
 refine d9 (i7 Hcnt (i7 (q6 Hpos Hnv) Hdig)) Y3 ?_ ?_
 . rintro _ ⟨j,d,rfl⟩;exact⟨(j,d),Y2 _,rfl⟩
 . unfold de;simp only[J3,Q9,Z3];omega
def ma (n:ℕ)(q:F0 (N0 n)->(P0 n)):Set (d4 (N0 n)):=R0 (fun v:BV n=>fun x=>(q x v).isSome)∪R0 (fun v:BV n=>fun x=>(q x v).getD false)
def bz (n:ℕ):ℕ:=(2*n)*((2*n*2+1)*((2*n*2+1)*((6*n+1)+2*n+2)+(2*n*2+1))) +(2*n)*(1+(2*n)*2+(2*n)*10)
lemma pu (n:ℕ) (hn:1<=n) {A:Set (d4 (N0 n))}
 (y:(fun _=>false)∈A) (ht:(fun _=>true)∈A)
 (a:u7 (N0 n) (2*n+2) (6*n+1)) (k:p5 a⊆A):
 Build A (ma n (fun x=>s5 n (a x))) (bz n):=by
 let S:=V9 (Fin (2*n)×Y0)
 let stepPB (j:ℕ) (st:S) (x:F0 (N0 n)):S:=if j=0 then let h9:=(a x ⟨2*n+1,by omega⟩).val
   if c:h9<2*n then some (⟨h9,c⟩,decide ((a x ⟨2*n,by omega⟩).val=1)) else none
  else match st with
   | none=>none
   | some (m,b)=>
    if r:j<2*n then let d:=a x ⟨2*n-1-j,by omega⟩
     if e:0<d.val then let t:=l3 d e
      some (⟨(m.val+c3 t) %(2*n),M1 _ (by omega)⟩,if c9 t then b else !b)
     else some (m,b)
    else some (m,b)
 have i:∀ j (r:j<2*n) x,n6 (none:S) stepPB (j+1) x=if c:(a x ⟨2*n+1,by omega⟩).val<2*n then let st:=g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) j
    some (st.1,st.2.1)
   else none:=fun j r x=>by
  induction j with
  | zero=>simp[n6,stepPB,g5]
  | succ j ih=>
   rw[n6,ih (by omega)];dsimp only[stepPB];rw[Q3 (succ_ne_zero j)];by_cases c:(a x ⟨2*n+1,by omega⟩).val<2*n
   . rw[L7 c,L7 c];dsimp only;rw[L7 r,g5,L7 r];by_cases e:0<(a x ⟨2*n-1-(j+1),by omega⟩).val<;>simp[e]
   . simp[c]
 have Hpb:Build A (dd (none:S) stepPB (2*n))
  ((2*n)*((2*n*2+1)*((2*n*2+1)*((6*n+1)+2*n+2)+(2*n*2+1)))):=by
  have z:W0 S=2*n*2+1:=by simp[S,Z3]
  have H:=dm y ht (none:S) stepPB (2*n) ((6*n+1)+2*n+1) (fun j r s s'=>by
   by_cases u:j=0
   . subst u
     cases s' with
     | none=>
      have H1:=w3 (A:=A) (fun m:Fin (2*n)=>f0 a ⟨2*n+1,by omega⟩ ⟨m.val,by omega⟩) y (fun m=>k ⟨_,_,rfl⟩);have H2:=i7 H1 (ae (inr rfl))
      have g:nt (fun x=>decide (∃ m:Fin (2*n),f0 a ⟨2*n+1,by omega⟩ ⟨m.val,by omega⟩ x=true))=fun x=>decide (stepPB 0 s x=none):=by
       funext x;apply L5;simp only[nt,f0,stepPB,↓reduceIte,Bool.not_eq_true',M7,L0]
       split_ifs with c
       . simp only[reduceCtorEq,iff_false,not_not];exact⟨⟨_,c⟩,rfl⟩
       . simp only[iff_true];rintro⟨m,hm⟩;exact c (hm▸m.isLt)
      rw[g] at H2;exact d9 H2 Y3 Y3 (by omega)
     | some mb=>
      rcases mb with ⟨m,b⟩
      have H2:Build A {fun x=>decide (stepPB 0 s x=some (m,b))} 2:=by
       cases b
       . have H:=i7 (ae (A:=A) (k ⟨⟨2*n,by omega⟩,⟨1,by omega⟩,rfl⟩))
          (t7 (inl (k ⟨⟨2*n+1,by omega⟩,⟨m.val,by omega⟩,rfl⟩)) (inr rfl))
         have g:an (f0 a ⟨2*n+1,by omega⟩ ⟨m.val,by omega⟩) (nt (f0 a ⟨2*n,by omega⟩ ⟨1,by omega⟩))=fun x=>decide (stepPB 0 s x=some (m,false)):=by
          funext x;apply L5;simp only[an,nt,f0,stepPB,↓reduceIte,K8,Bool.not_eq_true',M7,L0]
          split_ifs with c
          . dsimp only[S];simp only[Option.some.injEq,J0,K4,M7]
          . simp only[reduceCtorEq,iff_false];rintro⟨hm,_⟩;exact c (by rw[hm];exact m.isLt)
         rw[g] at H;exact H
       . have H:=t7 (A:=A) (k ⟨⟨2*n+1,by omega⟩,⟨m.val,by omega⟩,rfl⟩)
          (k ⟨⟨2*n,by omega⟩,⟨1,by omega⟩,rfl⟩)
         have g:an (f0 a ⟨2*n+1,by omega⟩ ⟨m.val,by omega⟩) (f0 a ⟨2*n,by omega⟩ ⟨1,by omega⟩)=fun x=>decide (stepPB 0 s x=some (m,true)):=by
          funext x;apply L5;simp only[an,f0,stepPB,↓reduceIte,K8,L0]
          split_ifs with c
          . dsimp only[S];simp only[Option.some.injEq,J0,K4,L0]
          . simp only[reduceCtorEq,iff_false];rintro⟨hm,_⟩;exact c (by rw[hm];exact m.isLt)
         rw[g] at H;exact d9 H Y3 Y3 (by omega)
      exact d9 H2 Y3 Y3 (by omega)
   . cases s with
     | none=>
      by_cases h8:(none:S)=s'
      . have g:(fun x=>decide (stepPB j none x=s'))=fun _=>true:=(by funext x;apply L5;simp only[L0];dsimp only[stepPB];rw[Q3 u];simp[h8]);rw[g];exact d9 (s6 (Q1 ht)) Y3 Y3 (by omega)
      . have g:(fun x=>decide (stepPB j none x=s'))=fun _=>false:=(by funext x;apply L5;simp only[J5,L0];dsimp only[stepPB];rw[Q3 u];simp[h8]);rw[g];exact d9 (s6 (Q1 y)) Y3 Y3 (by omega)
     | some mb=>
      rcases mb with ⟨m,b⟩
      let trD (d:Fin (6*n+1)):S:=if e:0<d.val then let t:=l3 d e
        some (⟨(m.val+c3 t) %(2*n),M1 _ (by omega)⟩,if c9 t then b else !b)
       else some (m,b)
      have H:=w3 (A:=A) (fun d:Fin (6*n+1)=>if trD d=s' then f0 a ⟨2*n-1-j,by omega⟩ d else fun _=>false)
       y (fun d=>by split_ifs;exact k ⟨_,_,rfl⟩;exact y)
      have g:(fun x=>decide (∃ d:Fin (6*n+1),(if trD d=s' then f0 a ⟨2*n-1-j,by omega⟩ d else fun _=>false) x=true))=fun x=>decide (stepPB j (some (m,b)) x=s'):=by
       funext x;apply L5;simp only[L0];dsimp only[stepPB];rw[Q3 u,L7 r]
       constructor
       . rintro⟨d,e⟩;by_cases q:trD d=s'
         . rw[Q2 q] at e;simp only[f0,L0] at e;rw[e];exact q
         . rw[Q3 q] at e;simp at e
       . intro q;exact⟨a x ⟨2*n-1-j,by omega⟩,by rw[Q2 q];simp[f0]⟩
      rw[g] at H;exact d9 H Y3 Y3 (by omega))
  exact d9 H Y3 Y3 (by rw[z])
 let A1:=A∪dd (none:S) stepPB (2*n)
 let stPin (j:ℕ) (x:F0 (N0 n)) (v:BV n):V9 Y0:=if c:(a x ⟨2*n+1,by omega⟩).val<2*n then (g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) j).2.2 v
  else none
 let O (j:ℕ):Set (d4 (N0 n)):=ma n (stPin j)
 have H0:Build A1 (O 0) ((2*n)*2):=by
  have H1:=ke (A:=A1) (fun v:BV n=>fun x=>(stPin 0 x v).isSome) 1 (fun v=>by
   have g:S393.Compiler.Build.or (fun x=>decide (n6 (none:S) stepPB 1 x=some ((e8 n).symm v,false)))
    (fun x=>decide (n6 (none:S) stepPB 1 x=some ((e8 n).symm v,true)))=fun x=>(stPin 0 x v).isSome:=by
    funext x;apply L5;dsimp only[S393.Compiler.Build.or,stPin];have w:=i 0 (by omega) x;simp only[Nat.zero_add] at w;rw[w]
    by_cases c:(a x ⟨2*n+1,by omega⟩).val<2*n
    . rw[L7 c,L7 c,g5];simp only[V4,L0,Option.some.injEq,J0];have f:((e8 n).symm v=⟨(a x ⟨2*n+1,by omega⟩).val,c⟩)↔v=d8 n ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩:=⟨fun h=>by rw[<-h];exact ((e8 n).apply_symm_apply v).symm,fun h=>by rw[h];exact M5 (e8 n) _⟩;by_cases l:v=d8 n ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩
      . rw[Q2 l];by_cases hb:(a x ⟨2*n,by omega⟩).val=1<;>simp[f.mpr l,hb]
      . rw[Q3 l];simp[Ne.symm (mt f.mp l)]
    . rw[Q8 c,Q8 c];simp
   rw[<-g];exact gg (A:=A1) (inr ⟨⟨1,by omega⟩,some ((e8 n).symm v,false),rfl⟩) (inr ⟨⟨1,by omega⟩,some ((e8 n).symm v,true),rfl⟩))
  have H2:Build A1 (R0 (fun v:BV n=>fun x=>(stPin 0 x v).getD false)) 0:=by
   apply s6;rintro _ ⟨v,rfl⟩
   have g:(fun x=>decide (n6 (none:S) stepPB 1 x=some ((e8 n).symm v,true)))=fun x=>(stPin 0 x v).getD false:=by
    funext x;apply L5;have w:=i 0 (by omega) x;simp only[Nat.zero_add] at w;rw[w];dsimp only[stPin]
    by_cases c:(a x ⟨2*n+1,by omega⟩).val<2*n
    . rw[L7 c,L7 c,g5];simp only[L0,Option.some.injEq,J0];have f:((e8 n).symm v=⟨(a x ⟨2*n+1,by omega⟩).val,c⟩)↔v=d8 n ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩:=⟨fun h=>by rw[<-h];exact ((e8 n).apply_symm_apply v).symm,fun h=>by rw[h];exact M5 (e8 n) _⟩;by_cases l:v=d8 n ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩
      . rw[Q2 l];simp[f.mpr l,eq_comm]
      . rw[Q3 l];simp[Ne.symm (mt f.mp l)]
    . rw[Q8 c,Q8 c];simp
   dsimp only;rw[<-g];exact inr ⟨⟨1,by omega⟩,some ((e8 n).symm v,true),rfl⟩
  exact d9 (q6 H1 H2) Y3 Y3 (by simp;omega)
 have Hloop:Build A1 (O (2*n-1)) ((2*n)*2+(2*n-1)*(1+(2*n)*3+(2*n)*7)):=ew O H0 fun j r=>by
  have p:j+1<2*n:=(by omega);let B:=A1∪O j;let d0:d4 (N0 n):=f0 a ⟨2*n-1-(j+1),by omega⟩ ⟨0,by omega⟩;have Hnd0:Build B {nt d0} 1:=ae (inl (inl (k ⟨⟨2*n-1-(j+1),by omega⟩,⟨0,by omega⟩,rfl⟩)));let B1:=B∪{nt d0};let atV (v:BV n) (b:Y0):d4 (N0 n):=fun x=>decide (n6 (none:S) stepPB (j+2) x=some ((e8 n).symm v,b));let hitV (v:BV n):d4 (N0 n):=an (nt d0) (S393.Compiler.Build.or (atV v false) (atV v true))
  have o:∀ v x,hitV v x=true↔∃ c:(a x ⟨2*n+1,by omega⟩).val<2*n,0<(a x ⟨2*n-1-(j+1),by omega⟩).val/\v=d8 n (g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) (j+1)).1:=fun v x=>by
   simp only[hitV,an,nt,S393.Compiler.Build.or,d0,f0,atV,i (j+1) p x,K8,V4,Bool.not_eq_true',M7,K4];by_cases c:(a x ⟨2*n+1,by omega⟩).val<2*n
   . rw[L7 c];simp only[L0,Option.some.injEq,J0,c,exists_true_left];refine and_congr (by omega) ?_;have f:((g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) (j+1)).1=(e8 n).symm v)↔v=d8 n (g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) (j+1)).1:=⟨fun h=>by rw[h];exact ((e8 n).apply_symm_apply v).symm,fun h=>by rw[h];exact (M5 (e8 n) _).symm⟩;cases (g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) (j+1)).2.1<;>simp[f]
   . rw[Q8 c];simp[c]
  have Hsome:Build B1 (R0 (fun v:BV n=>fun x=>(stPin (j+1) x v).isSome)) ((2*n)*3):=by
   simpa only[J3,card_bool,Q9] using ke (A:=B1) (fun v:BV n=>fun x=>(stPin (j+1) x v).isSome) 3 (fun v=>by
    have H1:=i7 (gg (A:=B1) (inl (inl (inr ⟨⟨j+2,by omega⟩,some ((e8 n).symm v,false),rfl⟩))) (inl (inl (inr ⟨⟨j+2,by omega⟩,some ((e8 n).symm v,true),rfl⟩))))
     (i7 (t7 (inl (inr rfl)) (inr rfl)) (gg (inl (inl (inl (inr (inl ⟨v,rfl⟩))))) (inr rfl)))
    have g:S393.Compiler.Build.or (fun x=>(stPin j x v).isSome) (hitV v)=fun x=>(stPin (j+1) x v).isSome:=by
     funext x;apply L5;simp only[S393.Compiler.Build.or,V4,o];dsimp only[stPin]
     by_cases c:(a x ⟨2*n+1,by omega⟩).val<2*n
     . rw[L7 c,L7 c,g5,L7 p];by_cases e:0<(a x ⟨2*n-1-(j+1),by omega⟩).val
       . simp only[L7 e,c,e,Q0,exists_true_left];rw[g5,L7 p,L7 e];dsimp only;by_cases f:v=d8 n ⟨((g5 n (a x) ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) j).1.val +c3 (l3 (a x ⟨2*n-1-(j+1),by omega⟩) e)) %(2*n),M1 _ (by omega)⟩<;>simp[f]
       . simp[Q8 e,e]
     . simp[Q8 c,c]
    rw[g] at H1;exact H1)
  have Hval:Build B1 (R0 (fun v:BV n=>fun x=>(stPin (j+1) x v).getD false)) ((2*n)*7):=by
   simpa only[J3,card_bool,Q9] using ke (A:=B1) (fun v:BV n=>fun x=>(stPin (j+1) x v).getD false) 7 (fun v=>by
    have H1:=i7 (gg (A:=B1) (inl (inl (inr ⟨⟨j+2,by omega⟩,some ((e8 n).symm v,false),rfl⟩))) (inl (inl (inr ⟨⟨j+2,by omega⟩,some ((e8 n).symm v,true),rfl⟩))))
     (i7 (t7 (inl (inr rfl)) (inr rfl)) (rj (inr rfl) (inl (inl (inl (inr (inr ⟨v,rfl⟩))))) (inl (inl (inl (inl (inr ⟨⟨j+2,by omega⟩,some ((e8 n).symm v,true),rfl⟩)))))))
    have g:mx (hitV v) (fun x=>(stPin j x v).getD false) (atV v true)=fun x=>(stPin (j+1) x v).getD false:=by
     funext x;dsimp only[mx,stPin,atV];rw[i (j+1) p x]
     by_cases c:(a x ⟨2*n+1,by omega⟩).val<2*n
     . rw[L7 c,L7 c,L7 c];by_cases hh:hitV v x=true
       . rw[hh];simp only[↓reduceIte];obtain⟨_,e,f⟩:=(o v x).mp hh;have hv':(g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) (j+1)).1=(e8 n).symm v:=(by rw[f];exact (M5 (e8 n) _).symm);rw[g5,L7 p,L7 e] at f hv' ⊢;dsimp only at f hv' ⊢;simp only[hv',Option.some.injEq,J0,Q0,show d8 n ((e8 n).symm v)=v from (e8 n).apply_symm_apply v,↓reduceIte,Option.getD_some];cases (if c9 (l3 (a x ⟨2*n-1-(j+1),by omega⟩) e) then (g5 n (a x) ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) j).2.1 else !(g5 n (a x) ⟨(a x ⟨2*n+1,by omega⟩).val,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) j).2.1)<;>rfl
       . have h0:hitV v x=false:=Bool.eq_false_iff.mpr hh;rw[h0];simp only[J5,↓reduceIte];rw[g5,L7 p];by_cases e:0<(a x ⟨2*n-1-(j+1),by omega⟩).val
         . rw[L7 e];dsimp only;have v0:v≠d8 n (g5 n (a x) ⟨_,c⟩ (decide ((a x ⟨2*n,by omega⟩).val=1)) (j+1)).1:=fun f=>hh ((o v x).mpr ⟨c,e,f⟩);rw[g5,L7 p,L7 e] at v0;rw[Q3 v0]
         . rw[Q8 e]
     . have h0:hitV v x=false:=Bool.eq_false_iff.mpr fun h=>c ((o v x).mp h).1;simp[h0,Q8 c]
    rw[g] at H1;exact d9 H1 Y3 Y3 (by omega))
  exact d9 (i7 Hnd0 (q6 Hsome Hval)) Y3 Y3 (by omega)
 have h7:O (2*n-1)=ma n (fun x=>s5 n (a x)):=(by dsimp only[O,ma];congr 2<;>(funext v x;unfold stPin s5;split_ifs<;>rfl));rw[h7] at Hloop;refine d9 (i7 Hpb Hloop) Y3 Y3 ?_;unfold bz;have w:(2*n-1)*(1+(2*n)*3+(2*n)*7)<=(2*n-1)*(1+(2*n)*2+(2*n)*10):=W5 _ (by omega)
 have h2:(2*n)*2+(2*n-1)*(1+(2*n)*2+(2*n)*10)<=(2*n)*(1+(2*n)*2+(2*n)*10):=by
  set M:=1+(2*n)*2+(2*n)*10;have hM:(2*n)*M=(2*n-1)*M+M:=by rw[<-succ_mul,Nat.succ_eq_add_one,show 2*n-1+1=2*n by omega]
  omega
 omega
def n3 (f:ℕ->ℕ):Prop:=∃ C:ℕ,∀ n:ℕ,f n≤(n+2)^C
lemma qj (k:ℕ):n3 (fun _=>k):=⟨k,fun n=>le_trans (Nat.le_of_lt lt_two_pow_self) (Nat.pow_le_pow_left (by omega) k)⟩
lemma rg:n3 (fun n=>n):=⟨1,fun n=>by simp⟩
lemma qw {f g:ℕ->ℕ}(d:n3 f)(c:n3 g):n3 (fun n=>f n+g n):=by
 obtain⟨Cf,a⟩:=d;obtain⟨Cg,b⟩:=c;refine⟨max Cf Cg+1,fun n=>?_⟩;have h:=pow_le_pow_right (show 1<=n+2 by omega) (le_max_left Cf Cg);have e:=pow_le_pow_right (show 1<=n+2 by omega) (le_max_right Cf Cg);have i:2*(n+2)^max Cf Cg<=(n+2)^(max Cf Cg+1):=by rw[U4,mul_comm ((n+2)^_)];exact W4 ((n+2)^max Cf Cg) (by omega:2<=n+2)
 have h1':=a n;have h2':=b n;dsimp only;omega
lemma qx {f g:ℕ->ℕ}(d:n3 f)(c:n3 g):n3 (fun n=>f n*g n):=by obtain⟨Cf,b⟩:=d;obtain⟨Cg,a⟩:=c;exact⟨Cf+Cg,fun n=>by rw[X6];exact Nat.mul_le_mul (b n) (a n)⟩
lemma qy {f g:ℕ->ℕ}(b:n3 f):n3 (fun n=>f n-g n):=by obtain⟨C,a⟩:=b;exact⟨C,fun n=>le_trans (Nat.sub_le _ _) (a n)⟩
def gk (n:ℕ):ℕ:=ey n+2*n*3*(4*n+1)+de n +y0 n+y0 n +(2*n+2)*((6*n+1)*y0 n+(6*n+1)*(6*n+1)+(6*n+1)*(10*(4*n))+9*(4*n)) +(2*n+2)*((6*n+1)*y0 n+((6*n+1)-1)*(18*(4*n)+15+3*(6*n+1))) +bz n
lemma poly_costTotal:n3 (fun n=>3+gk n):=by
 let b:=@qw;let a:=@qx;let c:=qj;let r:=rg;have e:=a (c 2) r;have g:=a (c 4) r;have j:=a (c 6) r;have f:=b r (c 1);have h:=b r (c 2);have d:=b e (c 1);have o:=b e (c 2);have p:=b g (c 1);have i:n3 Bw:=b e (c 10);have m:n3 o8:=b g (c 10);have v:=o;have k:=b j (c 1);have q:=b (a i (a (c 9) i)) (a (c 9) i);have s:=b (a m (a (c 9) m)) (a (c 9) m);have l:=b (a g (a (c 9) g)) (a (c 10) g)
 have y:n3 mn:=by
  unfold mn bn bm io;exact b (b (b (b (a (c 10) i) (a i (c 4))) (b (a (c 2) i) (c 1))) (a (c 2) (a h (b (a (a (c 3) d) (a (a (c 3) d) q)) (a (a (c 3) d) (a i (c 4)))))))
   (a (c 2) (a h (b (a (a f f) (a (a f f) q)) (a (a f f) (a i (c 4))))))
 have z:n3 bc:=(by unfold bc v4;exact b (b (b (b (a (c 3) (a (c 10) i)) (a (c 4) (a i (a (c 9) i)))) (a (c 7) (a (c 19) i))) (a (c 9) i)) (a (c 3) y));have h6:n3 ey:=(by unfold ey;exact b (b (b (b (b (b (b (b (b (b (b (a (a (c 3) d) (a (a f f) s)) (a d (a (c 9) m))) (a (a (c 3) d) (a (a (c 3) d) s))) (a (a (c 3) d) (a d (a (c 10) i)))) (a e z)) (a (c 2) (a (a f f) (a f q)))) (a (a f f) (a d (a (c 10) d)))) (b (a d (a (c 2) m)) d)) (a e (a (c 3) (a p (a (c 2) i))))) (b (a e (a (c 3) p)) (a e (c 3)))) (b (a (a f f) (a (c 6) d)) (a f f))) (c 2));have x:n3 ed:=(by unfold ed;exact b (a (a h h) (a (c 4) (a d d))) (a (a (a d h) (c 2)) (a (a h h) l)));have h2:n3 gi:=(by unfold gi;exact b (c 6) (a (a (a (a d h) d) (c 2)) (b (a h (c 4)) (a h l))));have h3:n3 ck:=(by unfold ck;exact b (a (a h h) (a (c 4) (a d d))) (a (a (a (a d h) d) (c 2)) (a (a h h) l)));have t:n3 bt:=(by unfold bt;exact b (a (a (a (a f f) f) f) (a (c 3) d)) (a (a (a (a d d) (c 2)) f) (a (a (a f f) f) l)));have w:n3 bu:=(by unfold bu;exact b (a e t) (a (a (a d d) (c 2)) (a f (a (c 9) g))));have h4:n3 u1:=by unfold u1;exact b (b (b (b (b (a (a (a d h) (c 2)) p) (a r x)) h2) (a r h3)) (a r w)) (a d (a (c 10) g))
 have h8:n3 ba:=by
  unfold ba;exact b (b (b (b (b (b (b (b (b (a e j) (a j (a e (a d (b (a d (c 2)) d))))) (b (b k j) (c 5))) (a e (a (c 2) (b (a (c 2) (b j (c 1))) (c 2))))) (a d (c 5))) (a e (b (b (c 1) j) j))) (a e (a o (b (a o (b j (c 1))) o)))) d) (a e (a (c 2) (b (a (c 2) (b j (c 1))) (c 2)))))
   (b (b (b (b (b (b (b e (c 1)) (a (c 2) e)) e) (a (a e j) (c 2))) e) (c 1)) (c 10))
 have h5:n3 l6:=(by unfold l6;exact b (b (b (b (b (a e (c 3)) v) (c 6)) g) (a e (b (b (b (b h8 h4) g) (c 1)) (a (c 10) g)))) (a (c 9) g));have u:n3 y0:=by unfold y0;have ht:=a k (a (c 9) g);exact b (a k (b (a k (b (a k h5) ht)) ht)) ht
 have h9:n3 de:=by
  unfold de;exact b (b (b (a e (a d (b (a d (c 2)) d))) (a e e)) e)
   (a v (a k (b (b (a (a (a (a e e) e) (c 4)) (c 5)) g) (c 4))))
 have h7:n3 bz:=(by unfold bz;have hS:=b (a e (c 2)) (c 1);exact b (a e (a hS (b (a hS (b (b k e) (c 2))) hS))) (a e (b (b (c 1) (a e (c 2))) (a e (c 10)))));unfold gk;exact b (c 3) (b (b (b (b (b (b (b h6 (a (a e (c 3)) p)) h9) u) u) (a v (b (b (b (a k u) (a k k)) (a k (a (c 10) g))) (a (c 9) g)))) (a v (b (a k u) (a (qy k) (b (b (a (c 18) g) (c 15)) (a (c 3) k)))))) h7)
noncomputable def jn (n:ℕ)(c:1<=n):Set (d4 (N0 n)):=let a:u7 (N0 n) (2*n+2) (6*n+1):=fun x=>e5 n (e7 n x)
 let count:=j5 n c;let b:u7 (N0 n) (2*n+2) (6*n+1):=fun x=>i8 (by omega) (count x) (2*n+2) (fun _=>⟨0,by omega⟩) (bf n x)
 R0 (a9 (4*n) (fun x=>count x (2*n+2) (a x)))∪R0 (a9 (4*n) (fun x=>j8 (count x) (a x) (2*n+2)))∪
  {fun x=>(count x 0 (a x)).testBit 0}∪
  ma n (fun x=>s5 n (b x))
lemma qz (n:ℕ)(d:1<=n):Build (jh (N0 n)) (jn n d) (gk n):=by
 unfold jn;let i:u7 (N0 n) (2*n+2) (6*n+1):=fun x=>e5 n (e7 n x);let count:=j5 n d;let h:u7 (N0 n) (2*n+2) (6*n+1):=fun x=>i8 (by omega) (count x) (2*n+2) (fun _=>⟨0,by omega⟩) (bf n x);have o:0<(6*n+1):=(by omega);have l:(fun _=>false)∈jh (N0 n):=inr (inl rfl);have j:(fun _=>true)∈jh (N0 n):=inr (inr rfl);have Hsa:=ps n;let A1:=jh (N0 n)∪da n;have Hce:=qg n (A:=A1) M9;let A2:=A1∪v5 n;have Hcw:=d9 (qq n d) (M8.trans M8:jh (N0 n)⊆A2) Y3 Y3;let A3:=A2∪p5 i
 have g:da n∪v5 n∪{fun _=>false,fun _=>true}⊆A3:=by
  rintro f ((r|hc)|(rfl|rfl))
  . exact inl (inl (inr r))
  . exact inl (inr hc)
  . exact inl (inl (inl l))
  . exact inl (inl (inl j))
 have HQ:fz A3 (4*n) (y0 n) count:=fun A hA k m p hp=>nc n d A (g.trans hA) k m p hp;have c:(fun _=>false)∈A3:=inl (inl (inl l));have b:(fun _=>true)∈A3:=inl (inl (inl j));have Hnum:=HQ A3 Y3 (2*n+2) Y3 i M9;have Hval0:=HQ A3 Y3 0 (V5 _) i M9;have Hrank:=oh (A:=A3) HQ c b i M9;have a:∀ x k,k<(2*n+2)->∀ p,count x k p<2^(4*n):=fun x k m p=>(by dsimp only[count];rw[ay d x k m.le p];exact lt_of_le_of_lt (card_filter_le _ _) (dx d x));have e:i9 A3 (a9 (4*n) (bf n)):=fun k=>(by have q:a9 (4*n) (bf n) k=fun x=>x (qv n k):=funext fun x=>S393.il _ k;rw[q];exact inl (inl (inl (inl ⟨_,rfl⟩))));have Hsel:Build A3 (p5 h) ((2*n+2)*((6*n+1)*y0 n+((6*n+1)-1)*(18*(4*n)+15+3*(6*n+1)))):=nb o (A:=A3) HQ c b a (bf n) e (fun x=>S393.jk _);have Hdec:=pu n d (A:=A3∪p5 h) (inl c) (inl b) h M9
 have Hall:=q4 (q4 (q4 Hsa Hce) (d9 Hcw (by simp only[A2,A1,W6];exact Y3) Y3 Y3))
  (d9 (q6 (q6 (q6 Hnum Hval0) Hrank) (i7 Hsel Hdec)) (by simp only[A3,A2,A1,W6];exact Y3) Y3 Y3)
 refine aa Hall Y3 ?_ (by unfold gk;omega);rintro f (((⟨k,rfl⟩|⟨k,rfl⟩)|rfl)|hpin)
 . exact inr (inr (inl (inl (inl ⟨k,rfl⟩))))
 . exact inr (inr (inl (inr ⟨k,rfl⟩)))
 . exact inr (inr (inl (inl (inr ⟨⟨0,by omega⟩,rfl⟩))))
 . exact inr (inr (inr hpin))
lemma gl {n:ℕ}{a b:F0 (N0 n)}(g:u4 n a=u4 n b):k6 n a=k6 n b:=by
 have u:av n a=av n b:=funext fun h=>funext fun s=>(by unfold av;rw[g]);have c:q9 n a=q9 n b:=(by unfold q9;rw[u]);have o:ko n a=ko n b:=(by unfold ko;congr 1;funext h d;rw[g]);have j:di n a=di n b:=by unfold di;rw[c,o]
 have f:∀ k,f7 n a k=f7 n b k:=fun k=>by
  induction k with
  | zero=>simp[f7,j]
  | succ k ih=>rw[f7,f7];split_ifs<;>simp[ih]
 have m:cy n a=cy n b:=(by unfold cy;rw[f]);have i:ac n a=ac n b:=funext fun x=>funext fun y=>(by unfold ac z4 z6 ia;rw[c,f]);have e:∀ l r v,v3 n l r v a=v3 n l r v b:=fun l r v=>(by unfold v3;rw[m]);have t:l8 n a=l8 n b:=(by unfold l8 cg cz ag u5;simp_rw[c,e,i,g]);have q:x3 n a=x3 n b:=(by unfold x3 u5;rw[c]);have p:s7 n a=s7 n b:=funext fun l=>funext fun r=>(by unfold s7;simp_rw[e]);ext w;simp[k6,t,q,p]
lemma q5 {a:Type*}(L1 L2:List a)(i:ℕ)(d:a)(b:i<L1.length):(L1 ++ L2).getD i d=L1.getD i d:=by rw[getD_eq_getElem _ _ (by rw[K6];omega),List.getElem_append_left b,getD_eq_getElem _ _ b]
lemma t4 {b:Type*}(L1 L2:List b)(i:ℕ)(d:b)(c:L1.length<=i):(L1 ++ L2).getD i d=L2.getD (i-L1.length) d:=by
 by_cases a:i<(L1 ++ L2).length
 . rw[getD_eq_getElem _ _ a,List.getElem_append_right c,getD_eq_getElem _ _ (by rw[K6] at a;omega)]
 . rw[List.getD_eq_default _ _ (not_lt.mp a),List.getD_eq_default _ _ (by rw[K6] at a;omega)]
lemma ee {b:Type*} (m L:ℕ) (f:Fin m->List b)
 (a:∀ i,(f i).length=L) (i:Fin m) (j:ℕ) (c:j<L) (d:b):
 (ofFn f).flatten.getD (i.val*L+j) d=(f i).getD j d:=by
 induction m with
 | zero=>exact elim0 i
 | succ m ih=>
  rw[List.ofFn_succ,List.flatten_cons];refine Fin.cases ?_ ?_ i
  . simp only[val_zero,zero_mul,zero_add];exact q5 _ _ j d (by rw[a];exact c)
  . intro i';simp only[Fin.val_succ,succ_mul];rw[t4 _ _ _ d (by rw[a];omega),show i'.val*L+L+j-(f 0).length=i'.val*L+j by rw[a];omega];exact ih (fun k=>f k.succ) (fun k=>a k.succ) i'
lemma jd (n:ℕ) (H:Fin (n+1)->Fin (n+1)->Fin (2*n+1)->Y0)
 (p:P0 n) (j:BV n->Y0) (z:Fin (4*n)->Y0):
 let raw:=fun(x:BV n->Y0)=>ofFn (fun i:Fin n=>x (false,i)) ++ ofFn (fun i:Fin n=>x (true,i));let a:=(ofFn (fun r:Fin (n+1)=>(ofFn (fun b:Fin (n+1)=>ofFn (H r b))).flatten)).flatten;let e:=[false,true] ++ a ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (j v)) ++ ofFn z;let x:F0 (N0 n):=fun m=>e.getD m.val false
 ofFn x=e ∧
 u4 n x=(fun r b=>∑ k:Fin (2*n+1),(H r b k).toNat*2^k.val) ∧
 e7 n x=p ∧
 bf n x=∑ k:Fin (4*n),(z k).toNat*2^k.val:=by
 intro raw a e x;have g:∀ r:Fin (n+1),(ofFn (fun b:Fin (n+1)=>ofFn (H r b))).flatten.length=(n+1)*(2*n+1):=fun r=>(by rw[List.length_flatten,map_ofFn,sum_ofFn];simp only[comp_def,U7,sum_const,W2,Q9,smul_eq_mul]);have c:a.length=(n+1)*(n+1)*(2*n+1):=(by dsimp only[a];rw[List.length_flatten,map_ofFn,sum_ofFn];simp only[comp_def,g,sum_const,W2,Q9,smul_eq_mul,Z3]);have d:∀ f:BV n->Y0,(raw f).length=2*n:=fun f=>(by dsimp only[raw];simp only[K6,U7];omega);refine⟨?_,?_,?_,?_⟩
 . apply List.ext_getElem (by rw[U7];simp only[e,K6,Z7,Z8,U7,c,d,N0];omega);intro i _ o;rw[getElem_ofFn];exact getD_eq_getElem _ false o
 . funext r b;unfold u4;refine L3 rfl fun k _=>?_;congr 2
   dsimp only[x,e,aj];have l:r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val)<a.length:=(by rw[c];have q:=cx r (cx b k.isLt);linarith);rw[q5 _ _ _ false (by simp only[K6,Z7,Z8];omega),q5 _ _ _ false (by simp only[K6,Z7,Z8];omega),q5 _ _ _ false (by simp only[K6,Z7,Z8];omega),t4 [false,true] a _ false (by simp only[Z7,Z8];omega),show 2+(r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val))-[false,true].length=r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val) by simp only[Z7,Z8];omega];dsimp only[a];rw[ee (n+1) ((n+1)*(2*n+1)) (fun w:Fin (n+1)=>(ofFn (fun u:Fin (n+1)=>ofFn (H w u))).flatten) g r _ (cx b k.isLt) false,ee (n+1) (2*n+1) (fun u:Fin (n+1)=>ofFn (H r u)) (fun u=>U7) b k.val k.isLt false,getD_eq_getElem _ _ (by rw[U7];exact k.isLt),getElem_ofFn]
 . funext v;unfold e7;dsimp only[x,e,dn,lz,et,pl]
   have h:∀(f:BV n->Y0) (v:BV n),(raw f).getD (if v.1 then n+v.2.val else v.2.val) false=f v:=fun f ⟨b,i⟩=>by
    dsimp only[raw];cases b
    . simp only[J5,↓reduceIte];rw[q5 _ _ _ false (by rw[U7];exact i.isLt),getD_eq_getElem _ _ (by rw[U7];exact i.isLt),getElem_ofFn]
    . simp only[↓reduceIte];rw[t4 _ _ _ false (by rw[U7];omega)];simp only[U7,Nat.add_sub_cancel_left];rw[getD_eq_getElem _ _ (by rw[U7];exact i.isLt),getElem_ofFn]
   have t:(if v.1 then n+v.2.val else v.2.val)<2*n:=by have:=v.2.isLt;split_ifs<;>omega
   have q:([false,true] ++ a ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (j v)) ++ ofFn z).getD
    (2+(n+1)*(n+1)*(2*n+1)+if v.1 then n+v.2.val else v.2.val) false=(p v).isSome:=by
    rw[q5 _ _ _ false (by simp only[K6,Z7,Z8,c,d];omega),q5 _ _ _ false (by simp only[K6,Z7,Z8,c,d];omega),t4 _ _ _ false (by simp only[K6,Z7,Z8,c];omega)];simp only[K6,Z7,Z8,c,show 2+(n+1)*(n+1)*(2*n+1)+(if v.1 then n+v.2.val else v.2.val)-(2+(n+1)*(n+1)*(2*n+1))=if v.1 then n+v.2.val else v.2.val by omega,h]
   have s:([false,true] ++ a ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (j v)) ++ ofFn z).getD
    (2+(n+1)*(n+1)*(2*n+1)+2*n+if v.1 then n+v.2.val else v.2.val) false=(p v).getD (j v):=by
    rw[q5 _ _ _ false (by simp only[K6,Z7,Z8,c,d];omega),t4 _ _ _ false (by simp only[K6,Z7,Z8,c,d];omega)];simp only[K6,Z7,Z8,c,d,show 2+(n+1)*(n+1)*(2*n+1)+2*n+(if v.1 then n+v.2.val else v.2.val)-(2+(n+1)*(n+1)*(2*n+1)+2*n)=if v.1 then n+v.2.val else v.2.val by omega,h]
   simp only[q,s];cases p v<;>rfl
 . unfold bf;rw[S393.ex];refine L3 rfl fun k _=>?_;congr 2;dsimp only[x,e,qv,qu,et];rw[t4 _ _ _ false (by simp only[K6,Z7,Z8,c,d];omega)];simp only[K6,Z7,Z8,c,d,show 2+(n+1)*(n+1)*(2*n+1)+4*n+k.val-(2+(n+1)*(n+1)*(2*n+1)+2*n+2*n)=k.val by omega];rw[getD_eq_getElem _ _ (by rw[U7];exact k.isLt),getElem_ofFn]
lemma mj (n:ℕ)[NeZero n](i:Fin n):c5 n i=i+1:=by
 cases n with
 | zero=>exact absurd rfl (NeZero.ne 0)
 | succ t=>exact ob t i
lemma buildAll_realize_n (n:ℕ)[NeZero n](hn:1<=n):let I:=Fin n;let J:=Fin (n+1);let V:=Y0×I;let W:=Fin (2*n+1);let K:=Fin (4*n);let P:=V->V9 Y0
 let h3:=fun(p:P) (r b:J)=>((univ:V7 (V->Y0)).filter (fun x=>(∀ v,p v=none\/p v=some (x v))/\(univ.filter (fun i:I=>x (false,i)≠x (true,i))).card=r.val/\(univ.filter (fun i:I=>x (false,i)≠x (true,i+1))).card=b.val)).card;let raw:=fun(x:V->Y0)=>ofFn (fun i:I=>x (false,i)) ++ ofFn (fun i:I=>x (true,i));let val:=fun(z:K->Y0)=>∑ k:K,(z k).toNat*2^k.val;let inputs:=2+(n+1)*(n+1)*(2*n+1)+8*n
 ∃(g:Circuit) (b9 b8:K->Fin (inputs+g.size))
  (valid:Fin (inputs+g.size)) (h5:Y0->V->Fin (inputs+g.size)),
  ReadsBack inputs g/\g.size<=3+gk n ∧
  (∀ gate∈g.gates,((gate.op=.and\/gate.op=.or)/\gate.inputs.length=2)\/(gate.op=.not/\gate.inputs.length=1)) ∧
  ∀(H:J->J->W->Y0),let table:=fun(r b:J)=>∑ k:W,(H r b k).toNat*2^k.val
   let fiber:=(univ:V7 P).filter (fun p=>h3 p=table);let j:=(ofFn (fun r:J=>(ofFn (fun b:J=>ofFn (H r b))).flatten)).flatten
   ∃ e:Fin fiber.card ≃ {p:P // p∈fiber},∀(p:P) (a:V->Y0) (z:K->Y0),let y:=g.wires ([false,true] ++ j ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (a v)) ++ ofFn z)
    let q:P:=fun v=>if y.getD (h5 false v).val false then some (y.getD (h5 true v).val false) else none
    val (fun k=>y.getD (b9 k).val false)=fiber.card/\(y.getD valid.val false=true↔p∈fiber)/\∀ i:Fin fiber.card,(p=(e i).val->val (fun k=>y.getD (b8 k).val false)=i.val)/\(val z=i.val->q=(e i).val):=by
 classical
 intro I J V W K P h3 raw val inputs;have b7:0<N0 n:=(by unfold N0;omega);have hD:0<(6*n+1):=(by omega);obtain⟨g,whereAt,c1,a7,b4,a5⟩:=realize b7 (qz n hn);let cw:u7 (N0 n) (2*n+2) (6*n+1):=fun x=>e5 n (e7 n x);let count:=j5 n hn;let v1:u7 (N0 n) (2*n+2) (6*n+1):=fun x=>i8 hD (count x) (2*n+2) (fun _=>⟨0,hD⟩) (bf n x);let OAll:=jn n hn;let wNum (k:K):OAll:=⟨a9 (4*n) (fun x=>count x (2*n+2) (cw x)) k,inl (inl (inl ⟨k,rfl⟩))⟩;let wOrd (k:K):OAll:=⟨a9 (4*n) (fun x=>j8 (count x) (cw x) (2*n+2)) k,inl (inl (inr ⟨k,rfl⟩))⟩;let h6:OAll:=⟨fun x=>(count x 0 (cw x)).testBit 0,inl (inr rfl)⟩;let wPinS (v:V):OAll:=⟨fun x=>(s5 n (v1 x) v).isSome,inr (inl ⟨v,rfl⟩)⟩;let wPinV (v:V):OAll:=⟨fun x=>(s5 n (v1 x) v).getD false,inr (inr ⟨v,rfl⟩)⟩;refine⟨g,?_⟩;refine⟨fun k=>whereAt (wNum k),?_⟩;refine⟨fun k=>whereAt (wOrd k),?_⟩;refine⟨whereAt h6,?_⟩;refine⟨fun b v=>if b then whereAt (wPinV v) else whereAt (wPinS v),?_⟩;refine⟨c1,a7,fun gate hg=>b4 gate hg,?_⟩;intro H table fiber j;have v2:∀ q:P,hist (c5 n) q=h3 q:=fun q=>(by funext r b;unfold hist;dsimp only[h3,V,I];congr 1;ext x;simp[mj n]);let mkX (p:P) (a:V->Y0) (z:K->Y0):F0 (N0 n):=fun b6=>([false,true] ++ j ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (a v)) ++ ofFn z).getD b6.val false;have h9:∀ p a z,ofFn (mkX p a z)=[false,true] ++ j ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (a v)) ++ ofFn z:=fun p a z=>(jd n H p a z).1;have t:∀ p a z,u4 n (mkX p a z)=table:=fun p a z=>(jd n H p a z).2.1;have h4:∀ p a z,e7 n (mkX p a z)=p:=fun p a z=>(jd n H p a z).2.2.1;have a2:∀ p a z,bf n (mkX p a z)=val z:=fun p a z=>(jd n H p a z).2.2.2;let l:=mkX (fun _=>none) (fun _=>false) (fun _=>false);have v0:∀ p a z,k6 n (mkX p a z)=k6 n l:=fun p a z=>gl ((t p a z).trans (t (fun _=>none) (fun _=>false) (fun _=>false)).symm)
 have h0:∀ p:P,p∈fiber↔e5 n p∈k6 n l:=by
  intro p;simp only[fiber,k6,L4,Y2,Q0];rw[<-v2 p,<-t (fun _=>none) (fun _=>false) (fun _=>false),kj hn l p];constructor
  . rintro⟨a4,y1,y2⟩;exact⟨a4,(dc hn (ki n l) (s7 n l) (e5 n p)).mpr ⟨p,rfl,y1,y2⟩⟩
  . rintro⟨a4,c2⟩;obtain⟨q,c0,y1,y2⟩:=(dc hn (ki n l) (s7 n l) (e5 n p)).mp c2;have b5:q=p:=ls hn c0;rw[b5] at y1 y2;exact⟨a4,y1,y2⟩
 let c:{p:P // p∈fiber} ≃ {w:n4 (2*n+2) (6*n+1) // w∈k6 n l}:=
  {toFun:=fun p=>⟨e5 n p.1,(h0 p.1).mp p.2⟩,invFun:=fun w=>⟨s5 n w.1,(h0 (s5 n w.1)).mpr (by rw[(w5 hn (s7 n l) w.1 (L4.mp w.2).2.2).1];exact w.2)⟩,left_inv:=fun p=>Z9 (fl hn p.1),right_inv:=fun w=>Z9 (w5 hn (s7 n l) w.1 (L4.mp w.2).2.2).1}
 have o:fiber.card=(k6 n l).card:=(by simpa using Fintype.card_congr c);let e:Fin fiber.card ≃ {p:P // p∈fiber}:=(finCongr o).trans ((dk hD (k6 n l)).trans c.symm);refine⟨e,?_⟩;intro p a z;let b2:=[false,true] ++ j ++ raw (fun v=>(p v).isSome) ++ raw (fun v=>(p v).getD (a v)) ++ ofFn z;let y:=g.wires b2;let x:=mkX p a z;have u:∀(f:OAll),y.getD (whereAt f).val false=f.val x:=fun f=>(by dsimp only[y,b2];rw[<-h9 p a z];exact a5 f x);have s:∀ k≤(2*n+2),∀ w,count x k w=g4 (k6 n l) k w:=fun k hk w=>(by rw[<-v0 p a z];exact ay hn x k hk w);change val (fun k=>y.getD (whereAt (wNum k)).val false)=fiber.card/\(y.getD (whereAt h6).val false=true↔p∈fiber)/\∀ i:Fin fiber.card,(p=(e i).val->val (fun k=>y.getD (whereAt (wOrd k)).val false)=i.val)/\(val z=i.val->(fun v=>if y.getD (whereAt (wPinS v)).val false then some (y.getD (whereAt (wPinV v)).val false) else none)=(e i).val);refine⟨?_,?_,?_⟩
 . have h1:(fun k:K=>y.getD (whereAt (wNum k)).val false)=fun k:K=>(count x (2*n+2) (cw x)).testBit k.val:=funext fun k=>u (wNum k);rw[h1];dsimp only[val];rw[S393.dv (by rw[s (2*n+2) Y3,cq];exact dx hn l),s (2*n+2) Y3,cq,o]
 . rw[u h6];dsimp only[h6,cw];rw[h4,s 0 (V5 _),ja,h0 p];by_cases h:e5 n p∈k6 n l<;>simp[h]
 . intro i;refine⟨?_,?_⟩
   . intro b1;have h1:(fun k:K=>y.getD (whereAt (wOrd k)).val false)=fun k:K=>(j8 (count x) (cw x) (2*n+2)).testBit k.val:=funext fun k=>u (wOrd k)
     have x1:j8 (count x) (cw x) (2*n+2)=j8 (g4 (k6 n l)) (e5 n p) (2*n+2):=by
      have a3:cw x=e5 n p:=(by dsimp only[cw];rw[h4]);rw[a3]
      have x2:∀ m≤(2*n+2),j8 (count x) (e5 n p) m=j8 (g4 (k6 n l)) (e5 n p) m:=by
       intro m hm
       induction m with
       | zero=>rfl
       | succ m ih=>
        rw[j8,L7 (by omega),j8,L7 (by omega),ih (by omega)];congr 1;refine L3 rfl fun d _=>by split_ifs<;>simp[s m (by omega)]
      exact x2 (2*n+2) Y3
     have b0:e5 n p=(dk hD (k6 n l) (finCongr o i)).1:=(by rw[b1];dsimp only[e,Equiv.trans_apply,c,coe_fn_symm_mk];exact (w5 hn (s7 n l) _ (L4.mp (dk hD (k6 n l) (finCongr o i)).2).2.2).1);rw[h1];dsimp only[val];rw[x1,b0,ns];simp only[finCongr_apply,Fin.val_cast];exact S393.dv (lt_trans i.isLt (by rw[o];exact dx hn l))
   . intro a6;funext v;simp only[u (wPinS v),u (wPinV v)];dsimp only[wPinS,wPinV]
     have a1:v1 x=i8 hD (g4 (k6 n l)) (2*n+2) (fun _=>⟨0,hD⟩) i.val:=by
      dsimp only[v1];rw[a2,a6]
      have x2:∀ m≤(2*n+2),∀ w r,i8 hD (count x) m w r=i8 hD (g4 (k6 n l)) m w r:=by
       intro m hm
       induction m with
       | zero=>intro _ _;rfl
       | succ m ih=>intro w r;rw[i8,L7 (by omega),i8,L7 (by omega)];rw[show (fun d=>count x m (update w ⟨m,by omega⟩ d))=fun d=>g4 (k6 n l) m (update w ⟨m,by omega⟩ d) from funext fun d=>s m (by omega) _];exact ih (by omega) _ _
      exact x2 (2*n+2) Y3 _ _
     have a0:s5 n (v1 x)=(e i).val:=(by rw[a1];dsimp only[e,Equiv.trans_apply,c,coe_fn_symm_mk];rw[og];simp only[finCongr_apply,Fin.val_cast]);simp only[a0];cases (e i).val v<;>rfl
end Front392
end PEqualNP.Outside.L_pcx_392_aux

theorem PEqualNP.Outside.L_pcx_392 : (∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let W := Fin (2*n+1)
  let K := Fin (4*n)
  let P := V → Option Bool
  let hist := fun (p : P) (r b : J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i+1))).card = b.val)).card
  let raw := fun (x : V → Bool) => List.ofFn (fun i : I => x (false,i)) ++ List.ofFn (fun i : I => x (true,i))
  let val := fun (z : K → Bool) => ∑ k : K, (z k).toNat * 2^k.val
  let inputs := 2+(n+1)*(n+1)*(2*n+1)+8*n
  ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (num ord : K → Fin (inputs+g.size))
    (valid : Fin (inputs+g.size)) (pinWire : Bool → V → Fin (inputs+g.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ (n+2)^C ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (H : J → J → W → Bool),
      let table := fun (r b : J) => ∑ k : W, (H r b k).toNat * 2^k.val
      let fiber := (Finset.univ : Finset P).filter (fun p => hist p = table)
      let countBits := (List.ofFn (fun r : J => (List.ofFn (fun b : J => List.ofFn (H r b))).flatten)).flatten
      ∃ e : Fin fiber.card ≃ {p : P // p ∈ fiber},
        ∀ (p : P) (junk : V → Bool) (z : K → Bool),
        let ws := g.wires ([false,true] ++ countBits ++ raw (fun v => (p v).isSome) ++
          raw (fun v => (p v).getD (junk v)) ++ List.ofFn z)
        let q : P := fun v => if ws.getD (pinWire false v).val false then some (ws.getD (pinWire true v).val false) else none
        val (fun k => ws.getD (num k).val false) = fiber.card ∧
          (ws.getD valid.val false = true ↔ p ∈ fiber) ∧
          ∀ i : Fin fiber.card,
            (p = (e i).val → val (fun k => ws.getD (ord k).val false) = i.val) ∧
            (val z = i.val → q = (e i).val)) := by
  obtain ⟨C, hC⟩ := PEqualNP.Outside.L_pcx_392_aux.Front392.poly_costTotal
  refine ⟨C + 1, Nat.succ_pos C, fun t => ?_⟩
  obtain ⟨g, num, ord, valid, pinWire, hrb, hsize, hleg, hspec⟩ :=
    PEqualNP.Outside.L_pcx_392_aux.Front392.buildAll_realize_n (t + 1) (Nat.succ_pos t)
  refine ⟨g, num, ord, valid, pinWire, hrb, le_trans hsize (le_trans (hC (t + 1)) (Nat.pow_le_pow_right (by omega) (Nat.le_succ C))), hleg, hspec⟩
