import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52834
namespace Engine
open PEqualNP.CircuitLowerBounds
abbrev RowNv(nv:Nat):=Fin (2^nv)
def mask12:Nat:=Nat.sub (Nat.shiftLeft 1 4096) 1
def mask11:Nat:=Nat.sub (Nat.shiftLeft 1 2048) 1
def mask10:Nat:=Nat.sub (Nat.shiftLeft 1 1024) 1
def mask9:Nat:=Nat.sub (Nat.shiftLeft 1 512) 1
def mask8:Nat:=Nat.sub (Nat.shiftLeft 1 256) 1
def maskC(nv:Nat):Nat:=
 cond (Nat.beq nv 12) mask12
  (cond (Nat.beq nv 11) mask11
   (cond (Nat.beq nv 10) mask10
    (cond (Nat.beq nv 9) mask9
     (cond (Nat.beq nv 8) mask8
      (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 nv)) 1)))))
def mkLo12(u:Nat):Nat:=
 Nat.div mask12 (Nat.add (Nat.shiftLeft 1 (Nat.shiftLeft 1 u)) 1)
def lo12_0:Nat:=mkLo12 0
def lo12_1:Nat:=mkLo12 1
def lo12_2:Nat:=mkLo12 2
def lo12_3:Nat:=mkLo12 3
def lo12_4:Nat:=mkLo12 4
def lo12_5:Nat:=mkLo12 5
def lo12_6:Nat:=mkLo12 6
def lo12_7:Nat:=mkLo12 7
def lo12_8:Nat:=mkLo12 8
def lo12_9:Nat:=mkLo12 9
def lo12_10:Nat:=mkLo12 10
def lo12_11:Nat:=mkLo12 11
def hi12_0:Nat:=Nat.xor mask12 lo12_0
def hi12_1:Nat:=Nat.xor mask12 lo12_1
def hi12_2:Nat:=Nat.xor mask12 lo12_2
def hi12_3:Nat:=Nat.xor mask12 lo12_3
def hi12_4:Nat:=Nat.xor mask12 lo12_4
def hi12_5:Nat:=Nat.xor mask12 lo12_5
def hi12_6:Nat:=Nat.xor mask12 lo12_6
def hi12_7:Nat:=Nat.xor mask12 lo12_7
def hi12_8:Nat:=Nat.xor mask12 lo12_8
def hi12_9:Nat:=Nat.xor mask12 lo12_9
def hi12_10:Nat:=Nat.xor mask12 lo12_10
def hi12_11:Nat:=Nat.xor mask12 lo12_11
def loC12:Nat->Nat
 | 0=>lo12_0| 1=>lo12_1| 2=>lo12_2| 3=>lo12_3
 | 4=>lo12_4| 5=>lo12_5| 6=>lo12_6| 7=>lo12_7
 | 8=>lo12_8| 9=>lo12_9| 10=>lo12_10| 11=>lo12_11
 | _=>0
def hiC12:Nat->Nat
 | 0=>hi12_0| 1=>hi12_1| 2=>hi12_2| 3=>hi12_3
 | 4=>hi12_4| 5=>hi12_5| 6=>hi12_6| 7=>hi12_7
 | 8=>hi12_8| 9=>hi12_9| 10=>hi12_10| 11=>hi12_11
 | _=>0
def loC(nv u:Nat):Nat:=cond (Nat.beq nv 12) (loC12 u) (Nat.land (loC12 u) (maskC nv))
def hiC(nv u:Nat):Nat:=cond (Nat.beq nv 12) (hiC12 u) (Nat.land (hiC12 u) (maskC nv))
def ValidWord(nv w:Nat):Prop:=w<2^(2^nv)
def properNv(nv w:Nat):Prop:=ValidWord nv w/\w≠0/\w≠maskC nv
def flipOp(d:Nat):Nat:=cond (Nat.beq d 2) 3 (cond (Nat.beq d 3) 2 d)
theorem lt4_cases{d:Nat}(h:d<4):d=0\/d=1\/d=2\/d=3:=by omega
theorem flip_flip{d:Nat}(h:d<4):flipOp d<4/\flipOp (flipOp d)=d:=by
 rcases lt4_cases h with rfl|rfl|rfl|rfl<;>decide
@[local simp] private lemma testBit_land' (a b r:Nat):(Nat.land a b).testBit r=(a.testBit r&&b.testBit r):=
 Nat.testBit_and a b r
@[local simp] private lemma testBit_lor' (a b r:Nat):(Nat.lor a b).testBit r=(a.testBit r||b.testBit r):=
 Nat.testBit_or a b r
@[local simp] private lemma testBit_xor' (a b r:Nat):(Nat.xor a b).testBit r=(a.testBit r ^^ b.testBit r):=
 Nat.testBit_xor a b r
private lemma testBit_shiftLeft' (a n r:Nat) :
  (Nat.shiftLeft a n).testBit r=(decide (n<=r)&&a.testBit (r-n)):=by
 change (a<<<n).testBit r=_;rw[Nat.testBit_shiftLeft]
@[local simp] private lemma testBit_shiftRight' (a n r:Nat) :
  (Nat.shiftRight a n).testBit r=a.testBit (n+r):=by
 change (a>>>n).testBit r=_;exact Nat.testBit_shiftRight a
private lemma shiftLeft_one_eq (u:Nat):Nat.shiftLeft 1 u=2^u:=by
 change 1<<<u=2^u;rw[Nat.shiftLeft_eq,Nat.one_mul]
@[local simp] private lemma testBit_one (k:Nat):(1:Nat).testBit k=decide (k=0):=by
 simpa[eq_comm]using Nat.testBit_two_pow (n:=0) (m:=k)
private lemma beq_false_of_ne {a b:Nat} (h:a≠b):Nat.beq a b=false:=
 Bool.eq_false_iff.mpr λe=>h (Nat.eq_of_beq_eq_true e)
private lemma ble_false_of_gt {a b:Nat} (h:¬(a<=b)):Nat.ble a b=false:=
 Bool.eq_false_iff.mpr λe=>h (Nat.ble_eq.mp e)
noncomputable def forceN{β:Type}(n:Nat)(f:Nat->β):β:=
 @Nat.rec (λ_=>(Nat->β)->β) (λg=>g 0) (λk _ g=>g (Nat.succ k)) n f
@[local simp] theorem forceN_eq{β:Type}(n:Nat)(f:Nat->β):forceN n f=f n:=by
 cases n<;>rfl
def forceB{β:Type}(b:Bool)(f:Bool->β):β:=
 Bool.casesOn b (f false) (f true)
@[local simp] theorem forceB_eq{β:Type}(b:Bool)(f:Bool->β):forceB b f=f b:=by
 cases b<;>rfl
noncomputable def forceList{α β:Type}(f:α->Nat)(l:List α):(List Nat->β)->β:=
 List.rec (λk=>k []) (λa _ ih k=>forceN (f a) λx=>ih λxs=>k (x::xs)) l
theorem forceList_eq{α β:Type}(f:α->Nat)(l:List α)(k:List Nat->β):
  forceList f l k=k (l.map f):=by
 induction l generalizing k with
 | nil=>rfl
 | cons a l ih=>
  change forceN (f a) (λx=>forceList f l λxs=>k (x::xs))=_
  rw[forceN_eq,ih];rfl
def zN(op x y:Nat):Nat:=
 cond (Nat.beq op 0) (Nat.land x y)
  (cond (Nat.beq op 1) (Nat.lor x y)
   (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y))
    (Nat.xor y (Nat.land x y))))
def binBool(op:Nat)(a b:Bool):Bool:=
 if op=0 then a&&b else if op=1 then a||b else if op=2 then a && !b else !a&&b
theorem zN_spec(op x y r:Nat):
  (zN op x y).testBit r=binBool op (x.testBit r) (y.testBit r):=by
 unfold zN binBool
 by_cases h0:op=0;· subst h0;simp
 by_cases h1:op=1;· subst h1;simp
 by_cases h2:op=2
 ·subst h2;cases hx:x.testBit r<;>cases hy:y.testBit r<;>simp[hx,hy]
 ·simp only[beq_false_of_ne h0,beq_false_of_ne h1,beq_false_of_ne h2,h0,h1,h2,Bool.cond_false,ite_false,testBit_xor',testBit_land']
  cases x.testBit r<;>cases y.testBit r<;>rfl
theorem lt_two_pow_of_testBit{m k:Nat}(h:∀r,k<=r->m.testBit r=false):m<2^k:=by
 have heq:m=m % 2^k:=Nat.eq_of_testBit_eq λr=>by
  rw[Nat.testBit_mod_two_pow];by_cases hr:r<k;· simp[hr]
  ·simp[hr,h r (Nat.le_of_not_lt hr)]
 rw[heq];exact Nat.mod_lt m (Nat.two_pow_pos k)
theorem testBit_eq_false_of_lt_pow{m k r:Nat}(hm:m<2^k)(hr:k<=r):m.testBit r=false:=
 Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hr))
private lemma valid_land_l {nv a b:Nat} (ha:ValidWord nv a):ValidWord nv (Nat.land a b):=
 lt_two_pow_of_testBit λr hr=>by rw[testBit_land',testBit_eq_false_of_lt_pow ha hr];rfl
private lemma valid_land_r {nv a b:Nat} (hb:ValidWord nv b):ValidWord nv (Nat.land a b):=
 lt_two_pow_of_testBit λr hr=>by rw[testBit_land',testBit_eq_false_of_lt_pow hb hr,Bool.and_false]
private lemma valid_lor {nv a b:Nat} (ha:ValidWord nv a) (hb:ValidWord nv b):ValidWord nv (Nat.lor a b):=
 lt_two_pow_of_testBit λr hr=>by rw[testBit_lor',testBit_eq_false_of_lt_pow ha hr,testBit_eq_false_of_lt_pow hb hr];rfl
private lemma valid_xor {nv a b:Nat} (ha:ValidWord nv a) (hb:ValidWord nv b):ValidWord nv (Nat.xor a b):=
 lt_two_pow_of_testBit λr hr=>by rw[testBit_xor',testBit_eq_false_of_lt_pow ha hr,testBit_eq_false_of_lt_pow hb hr];rfl
private lemma exists_testBit_of_ne_zero {m:Nat} (h:m≠0):∃k,m.testBit k=true:=by
 by_contra ha;exact h (Nat.eq_of_testBit_eq λk=>by rw[Nat.zero_testBit];exact Bool.eq_false_iff.mpr λht=>ha ⟨k,ht⟩)
private lemma lt_of_testBit {k m r:Nat} (hm:m<2^k) (h:m.testBit r=true):r<k:=
 by_contra λg=>Bool.noConfusion ((testBit_eq_false_of_lt_pow hm (Nat.le_of_not_lt g)).symm.trans h)
theorem zN_lt{nv op x y:Nat}(hx:ValidWord nv x)(hy:ValidWord nv y):
  ValidWord nv (zN op x y):=
 lt_two_pow_of_testBit λr hr=>by
  rw[zN_spec,testBit_eq_false_of_lt_pow hx hr,testBit_eq_false_of_lt_pow hy hr];unfold binBool;split_ifs<;>rfl
theorem zN_flip{d:Nat}(hd:d<4)(x y:Nat):zN d x y=zN (flipOp d) y x:=
 Nat.eq_of_testBit_eq λr=>by
  rw[zN_spec,zN_spec];rcases lt4_cases hd with rfl|rfl|rfl|rfl<;>cases x.testBit r<;>cases y.testBit r<;>decide
theorem zN_and_mask(op x y d:Nat):
  zN op (Nat.land x d) (Nat.land y d)=Nat.land (zN op x y) d:=
 Nat.eq_of_testBit_eq λr=>by
  rw[zN_spec,testBit_land',testBit_land',testBit_land',zN_spec]
  unfold binBool;cases d.testBit r<;>cases x.testBit r<;>cases y.testBit r<;>split_ifs<;>rfl
theorem zN_mod_op(op x y:Nat):
  ∃e,e<4/\zN op x y=zN e x y:=by
 by_cases h0:op=0;· exact⟨0,by omega,h0▸rfl⟩
 by_cases h1:op=1;· exact⟨1,by omega,h1▸rfl⟩
 by_cases h2:op=2;· exact⟨2,by omega,h2▸rfl⟩
 exact⟨3,by omega,Nat.eq_of_testBit_eq λr=>by simp[zN_spec,binBool,h0,h1,h2]⟩
theorem maskC_eq(nv:Nat):maskC nv=2^(2^nv)-1:=by
 have hm n k (hk:2^n=k) (e:maskC n=Nat.sub (Nat.shiftLeft 1 k) 1):maskC n=2^(2^n)-1:=by rw[hk,e];exact congrArg (· - 1) (shiftLeft_one_eq k)
 by_cases h12:nv=12;· exact h12▸hm 12 4096 rfl rfl
 by_cases h11:nv=11;· exact h11▸hm 11 2048 rfl rfl
 by_cases h10:nv=10;· exact h10▸hm 10 1024 rfl rfl
 by_cases h9:nv=9;· exact h9▸hm 9 512 rfl rfl
 by_cases h8:nv=8;· exact h8▸hm 8 256 rfl rfl
 simp[maskC,beq_false_of_ne h12,beq_false_of_ne h11,beq_false_of_ne h10,beq_false_of_ne h9,beq_false_of_ne h8,Bool.cond_false]
 change Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 nv)) 1=Nat.sub (2^(2^nv)) 1;rw[shiftLeft_one_eq,shiftLeft_one_eq]
theorem mask12_eq:mask12=2^4096-1:=
 congrArg (λx=>x-1) (shiftLeft_one_eq 4096)
theorem testBit_maskC(nv r:Nat):(maskC nv).testBit r=decide (r<2^nv):=by
 rw[maskC_eq,Nat.testBit_two_pow_sub_one]
theorem maskC_lt(nv:Nat):ValidWord nv (maskC nv):=by
 unfold ValidWord;rw[maskC_eq];exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
theorem land_maskC_lt(nv x:Nat):ValidWord nv (Nat.land x (maskC nv)):=
 valid_land_r (maskC_lt nv)
def allRange(n:Nat)(p:Nat->Bool):Bool:=
 match n with
 | 0=>true
 | k+1=>p k&&allRange k p
theorem allRange_sound{n:Nat}{p:Nat->Bool}(h:allRange n p=true):
  ∀i < n,p i=true:=by
 induction n with
 | zero=>intro i hi;omega
 | succ k ih=>
  simp[allRange,Bool.and_eq_true]at h
  intro i hi;by_cases he:i=k;· exact he▸h.1
  ·exact ih h.2 i (by omega)
set_option maxRecDepth 16000 in
theorem loC12_bits_all(u:Fin 12):
  allRange 4096 (λr=>(loC12 u.1).testBit r == !(r.testBit u.1))=true:=by
 fin_cases u<;>decide +kernel
theorem loC12_bits(u:Fin 12)(r:Fin 4096):
  (loC12 u.1).testBit r.1 = !(r.1.testBit u.1):=
 beq_iff_eq.mp (allRange_sound (loC12_bits_all u) r.1 r.2)
theorem hiC12_eq_xor(u:Fin 12):hiC12 u.1=Nat.xor mask12 (loC12 u.1):=by
 fin_cases u<;>rfl
theorem hiC12_bits(u:Fin 12)(r:Fin 4096):
  (hiC12 u.1).testBit r.1=r.1.testBit u.1:=by
 rw[hiC12_eq_xor u,testBit_xor',mask12_eq,Nat.testBit_two_pow_sub_one,decide_eq_true r.2,loC12_bits u r]
 cases r.1.testBit u.1<;>rfl
theorem loC_lt(nv u:Nat):ValidWord nv (loC nv u):=by
 unfold loC
 by_cases h12:nv=12
 ·subst h12;simp[Nat.beq_refl,Bool.cond_true]
  match u with
  | 0| 1| 2| 3| 4| 5| 6| 7| 8| 9| 10| 11=>
   exact Nat.lt_of_le_of_lt (Nat.div_le_self mask12 _) (maskC_lt 12)
  | _+12=>exact Nat.two_pow_pos _
 ·rw[beq_false_of_ne h12,Bool.cond_false];exact land_maskC_lt nv _
theorem hiC_lt(nv u:Nat):ValidWord nv (hiC nv u):=by
 unfold hiC
 by_cases h12:nv=12
 ·subst h12;simp[Nat.beq_refl,Bool.cond_true]
  by_cases hu:u<12
  ·rw[hiC12_eq_xor ⟨u,hu⟩];exact valid_xor (maskC_lt 12) (by simpa[loC]using loC_lt 12 u)
  ·match u,hu with| _+12,_=>exact Nat.two_pow_pos _
 ·rw[beq_false_of_ne h12,Bool.cond_false];exact land_maskC_lt nv _
private lemma lhC_bits {nv u r:Nat} {f:Nat->Nat} {b:Bool} (hnv:nv<=12) (hu:u<nv)
  (hlt:ValidWord nv (cond (Nat.beq nv 12) (f u) (Nat.land (f u) (maskC nv))))
  (hb:∀(_:r<4096)(_:u<12),(f u).testBit r=b) :
  (cond (Nat.beq nv 12) (f u) (Nat.land (f u) (maskC nv))).testBit r=(decide (r<2^nv)&&b):=by
 by_cases hr:r<2^nv
 ·have hr12:r<4096:=Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hnv)
  by_cases e:nv=12
  ·subst e;simp[hr12,hb hr12 (by omega)]
  ·simp[beq_false_of_ne e,testBit_maskC,hr,hb hr12 (by omega)]
 ·rw[testBit_eq_false_of_lt_pow hlt (Nat.le_of_not_lt hr),decide_eq_false hr];rfl
theorem loC_bits{nv u:Nat}(hnv:nv<=12)(hu:u<nv)(r:Nat):
  (loC nv u).testBit r=(decide (r<2^nv) && !(r.testBit u)):=
 lhC_bits hnv hu (loC_lt nv u) λhr hu'=>loC12_bits ⟨u,hu'⟩ ⟨r,hr⟩
theorem hiC_bits{nv u:Nat}(hnv:nv<=12)(hu:u<nv)(r:Nat):
  (hiC nv u).testBit r=(decide (r<2^nv)&&r.testBit u):=
 lhC_bits hnv hu (hiC_lt nv u) λhr hu'=>hiC12_bits ⟨u,hu'⟩ ⟨r,hr⟩
theorem hiC_bits_row{nv u:Nat}(hnv:nv<=12)(hu:u<nv)(r:RowNv nv):
  (hiC nv u).testBit r.1=r.1.testBit u:=by
 rw[hiC_bits hnv hu r.1,decide_eq_true r.2,Bool.true_and]
theorem loC_bits_row{nv u:Nat}(hnv:nv<=12)(hu:u<nv)(r:RowNv nv):
  (loC nv u).testBit r.1 = !(r.1.testBit u):=by
 rw[loC_bits hnv hu r.1,decide_eq_true r.2,Bool.true_and]
noncomputable def anyEq(m:Nat)(l:List Nat):Bool:=
 List.rec false (λv _ ih=>or (Nat.beq m v) ih) l
theorem anyEq_iff(m:Nat)(l:List Nat):anyEq m l=true↔m∈l:=by
 induction l with
 | nil=>simp[anyEq]
 | cons v vs ih=>
  change (Nat.beq m v||anyEq m vs)=true↔m∈v::vs
  simp[Bool.or_eq_true,ih]
def nconst(d m:Nat):Bool:=or (Nat.beq m 0) (Nat.beq m d)
theorem nconst_iff(d m:Nat):nconst d m=true↔m=0\/m=d:=by
 simp[nconst,Bool.or_eq_true]
noncomputable def navail(d:Nat)(pm:List Nat)(m:Nat):Bool:=
 or (or (nconst d m) (anyEq m pm)) (anyEq (Nat.xor d m) pm)
theorem navail_iff(d:Nat)(pm:List Nat)(m:Nat):
  navail d pm m=true↔m=0\/m=d\/m∈pm\/Nat.xor d m∈pm:=by
 simp[navail,Bool.or_eq_true,nconst_iff,anyEq_iff,or_assoc]
def listGetN:List Nat->Nat->Nat
 | [],_=>0
 | x::_,0=>x
 | _::xs,i+1=>listGetN xs i
theorem listGetN_eq_getD(l:List Nat)(i:Nat):listGetN l i=l.getD i 0:=by
 induction l generalizing i with
 | nil=>rfl
 | cons x xs ih=>
  cases i with
  | zero=>rfl
  | succ j=>simp[listGetN,ih]
private lemma listGetN_getElem {l:List Nat} {i:Nat} (hi:i<l.length):listGetN l i=l[i]:=by
 rw[listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi];rfl
theorem listGetN_mem{l:List Nat}{i:Nat}(hi:i<l.length):listGetN l i∈l:=by
 rw[listGetN_getElem hi];exact List.getElem_mem hi
theorem listGetN_append_left{a b:List Nat}{i:Nat}(hi:i<a.length):
  listGetN (a++b) i=listGetN a i:=by
 rw[listGetN_eq_getD,listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
  List.getElem?_append_left hi]
private lemma listGetN_append_right {a b:List Nat} {i:Nat} (hi:a.length<=i) :
  listGetN (a++b) i=listGetN b (i-a.length):=by
 rw[listGetN_eq_getD,listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
  List.getElem?_append_right hi]
def flipURaw(nv u w:Nat):Nat:=
 let sh:=Nat.shiftLeft 1 u
 Nat.lor (Nat.shiftLeft (Nat.land w (loC nv u)) sh) (Nat.shiftRight (Nat.land w (hiC nv u)) sh)
theorem xor_two_pow_lt{nv u r:Nat}(hu:u<nv)(hr:r<2^nv):
  r^^^(1<<<u)<2^nv:=by
 rw[Nat.shiftLeft_eq,Nat.one_mul]
 exact lt_two_pow_of_testBit λk hk=>by
  rw[Nat.testBit_xor,testBit_eq_false_of_lt_pow hr hk,Nat.testBit_two_pow,decide_eq_false (by omega)];rfl
set_option maxRecDepth 16000 in
private lemma flip_arith_12 (u:Fin 12) :
  allRange 4096 (λr=>
   let p:=2^u.1
   if r.testBit u.1 then
    decide (p<=r)&&(r-p==r^^^p) && !((r-p).testBit u.1) && !((p+r).testBit u.1)
   else
    (r+p==r^^^p)&&(r+p).testBit u.1&&(decide (r<p)||(r-p).testBit u.1))=true:=by
 fin_cases u<;>decide +kernel
theorem drop_cons_iff{α:Type}{l rest:List α}{i:Nat}{x:α}(h:l.drop i=x::rest):
  ∃hi:i<l.length,x=l[i]'hi/\rest=l.drop (i+1):=by
 have hi:i<l.length:=by have:=congrArg List.length h;simp at this;omega
 rw[List.drop_eq_getElem_cons hi]at h;cases h;exact⟨hi,rfl,rfl⟩
theorem cond_t{a b:Bool}(h:cond a b false=true):a=true/\b=true:=by cases a<;>simp_all
theorem cond_o{a b:Bool}(h:cond a true b=true):a=true\/b=true:=by cases a<;>simp_all
theorem cond_to{a b c:Bool}(h:cond a b (cond c b false)=true):(a=true\/c=true)/\b=true:=by cases a<;>cases c<;>simp_all
theorem flipURaw_spec{nv u w:Nat}(hnv:nv<=12)(hu:u<nv):
  ValidWord nv (flipURaw nv u w) /\
  ∀r:RowNv nv,(flipURaw nv u w).testBit r.1=w.testBit (r.1^^^(1<<<u)):=by
 have ha x (hx:x<2^nv):=allRange_sound (flip_arith_12 ⟨u,by omega⟩) x (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hnv))
 have hbit r:(flipURaw nv u w).testBit r=(decide (r<2^nv)&&w.testBit (r^^^2^u)):=by
  simp only[flipURaw,shiftLeft_one_eq,testBit_lor',testBit_shiftLeft',testBit_shiftRight',testBit_land',loC_bits hnv hu,hiC_bits hnv hu]
  by_cases hr:r<2^nv
  ·have h:=ha r hr;dsimp only at h
   cases hru:r.testBit u<;>simp only[hru,ite_true,ite_false,Bool.false_eq_true,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,decide_eq_true_eq]at h
   ·have hlt:2^u+r<2^nv:=by rw[Nat.add_comm,h.1.1];simpa[Nat.shiftLeft_eq]using xor_two_pow_lt hu hr
    rw[show(decide (2^u<=r)&&(w.testBit (r-2^u)&&(decide (r-2^u<2^nv) && !(r-2^u).testBit u)))=false from
     h.2.elim (λe=>by simp[Nat.not_le.mpr e]) (λe=>by simp[e]),
     Bool.false_or,decide_eq_true hlt,Nat.add_comm (2^u) r,h.1.2,h.1.1,decide_eq_true hr];simp
   ·rw[h.2,decide_eq_true h.1.1.1,decide_eq_true (Nat.lt_of_le_of_lt (Nat.sub_le r _) hr),h.1.2,h.1.1.2,decide_eq_true hr];simp
  ·have hnot:=Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_not_lt hr) (Nat.le_add_left r (2^u)))
   by_cases hge:2^u<=r<;>by_cases hs:r-2^u<2^nv<;>simp[hr,hnot,hge,hs]
   intro _;cases hsf:(r-2^u).testBit u;swap;rfl
   have h:=ha (r-2^u) hs;simp[hsf]at h
   have:(r-2^u)+2^u<2^nv:=by rw[h.1.1];simpa[Nat.shiftLeft_eq]using xor_two_pow_lt hu hs
   omega
 exact⟨lt_two_pow_of_testBit λr hr=>by simp[hbit r,show ¬(r<2^nv) by omega],λr=>by simp[hbit r.1,r.2,Nat.shiftLeft_eq]⟩
def subcubeGo(nv zMask oMask:Nat):Nat->Nat->Nat
 | 0,acc=>acc
 | u+1,acc=>
  if zMask.testBit u then subcubeGo nv zMask oMask u (Nat.land acc (loC nv u))
  else if oMask.testBit u then subcubeGo nv zMask oMask u (Nat.land acc (hiC nv u))
  else subcubeGo nv zMask oMask u acc
def subcubeNv(nv zMask oMask:Nat):Nat:=subcubeGo nv zMask oMask nv (maskC nv)
private lemma testBit_eq_land_shift (m u:Nat) :
  not (Nat.beq (Nat.land m (Nat.shiftLeft 1 u)) 0)=m.testBit u:=by
 rw[shiftLeft_one_eq];cases hm:m.testBit u
 ·have h0:Nat.land m (2^u)=0:=Nat.eq_of_testBit_eq λk=>by rw[testBit_land',Nat.testBit_two_pow,Nat.zero_testBit];by_cases hk:u=k<;>simp_all
  rw[h0];rfl
 ·rw[beq_false_of_ne λh0=>by have:=congrArg (·.testBit u) h0;simp[hm]at this];rfl
theorem subcubeNv_lt(nv zMask oMask:Nat):ValidWord nv (subcubeNv nv zMask oMask):=by
 have hgo:∀v acc,ValidWord nv acc->ValidWord nv (subcubeGo nv zMask oMask v acc):=by
  intro v;induction v with| zero=>exact λ_ ha=>ha| succ u ih=>intro acc ha;simp[subcubeGo];split_ifs<;>exact ih _ (by first| exact valid_land_l ha| exact ha)
 exact hgo nv (maskC nv) (maskC_lt nv)
theorem testBit_subcubeNv{nv zMask oMask:Nat}(hnv:nv<=12)(r:RowNv nv):
  (subcubeNv nv zMask oMask).testBit r.1=true ↔
   ∀u < nv,(zMask.testBit u=true->r.1.testBit u=false) /\
     (zMask.testBit u=false->oMask.testBit u=true->r.1.testBit u=true):=by
 have hgo:∀v acc,v<=nv->((subcubeGo nv zMask oMask v acc).testBit r.1=true ↔
   acc.testBit r.1=true/\∀u < v,(zMask.testBit u=true->r.1.testBit u=false)/\(zMask.testBit u=false->oMask.testBit u=true->r.1.testBit u=true)):=by
  intro v;induction v with
  | zero=>intro acc _;simp[subcubeGo]
  | succ u ih=>
   intro acc huv;simp only[subcubeGo];split_ifs with hz ho
   ·rw[ih _ (by omega),testBit_land',Bool.and_eq_true,loC_bits_row hnv (by omega) r];grind
   ·rw[ih _ (by omega),testBit_land',Bool.and_eq_true,hiC_bits_row hnv (by omega) r];grind
   ·rw[ih _ (by omega)];grind
 rw[subcubeNv,hgo nv (maskC nv) (Nat.le_refl nv),testBit_maskC,decide_eq_true r.2];simp
noncomputable def decodeBankFwd{β:Type}:List (Nat×Nat×Nat)->List Nat->(List Nat->β)->β
 | [],bank,k=>k bank
 | (op,a,b)::rest,bank,k=>
  forceN (zN op (listGetN bank a) (listGetN bank b)) λz=>
   decodeBankFwd rest (bank++[z]) k
def decodeBank:List (Nat×Nat×Nat)->List Nat->List Nat
 | [],bank=>bank
 | (op,a,b)::rest,bank=>
  decodeBank rest (bank++[zN op (listGetN bank a) (listGetN bank b)])
theorem decodeBankFwd_spec{β:Type}(gates:List (Nat×Nat×Nat))(bank:List Nat)(k:List Nat->β):
  decodeBankFwd gates bank k=k (decodeBank gates bank):=by
 induction gates generalizing bank with| nil=>rfl| cons g rest ih=>rcases g with ⟨op,a,b⟩;simpa[decodeBankFwd,decodeBank]using ih _
theorem decodeBank_prefix(gates:List (Nat×Nat×Nat))(init:List Nat):
  ∃ext,decodeBank gates init=init++ext/\ext.length=gates.length:=by
 induction gates generalizing init with
 | nil=>exact⟨[],by simp[decodeBank]⟩
 | cons g rest ih=>
  rcases g with ⟨op,a,b⟩;obtain⟨ext,heq,hlen⟩:=ih (init++[zN op (listGetN init a) (listGetN init b)])
  exact⟨_::ext,by rw[decodeBank,heq,List.append_assoc];rfl,by simp[hlen]⟩
theorem decodeBank_valid {nv:Nat} (gates:List (Nat×Nat×Nat)) (init:List Nat)
  (hi:∀w∈init,ValidWord nv w) :
  ∀w∈decodeBank gates init,ValidWord nv w:=by
 induction gates generalizing init with
 | nil=>exact hi
 | cons g rest ih=>
  rcases g with ⟨op,a,b⟩;refine ih _ λw hw=>(List.mem_append.mp hw).elim (hi w) λh2=> ?_
  rw[List.mem_singleton.mp h2]
  have hv i:ValidWord nv (listGetN init i):=by
   by_cases h:i < init.length;exact hi _ (listGetN_mem h)
   rw[listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt h)];exact Nat.two_pow_pos _
  exact zN_lt (hv a) (hv b)
theorem decodeBank_gate_eq(gates:List (Nat×Nat×Nat))(init:List Nat):
  ∀(idx:Nat)(g:Nat×Nat×Nat),
   gates[idx]?=some g ->
   listGetN (decodeBank gates init) (init.length+idx) =
    zN g.1 (listGetN (decodeBank gates init) g.2.1) (listGetN (decodeBank gates init) g.2.2) \/
   init.length+idx<=g.2.1\/init.length+idx<=g.2.2:=by
 induction gates generalizing init with
 | nil=>intro _ _ h;simp at h
 | cons hd tl ih=>
  rcases hd with ⟨op,a,b⟩;intro idx g hg;let z:=zN op (listGetN init a) (listGetN init b)
  cases idx with
  | zero=>
   simp at hg;subst hg;obtain⟨ext,heq,_⟩:=decodeBank_prefix tl (init++[z]);simp[decodeBank,Nat.add_zero]
   by_cases ha:a < init.length;swap;exact Or.inr (Or.inl (by omega))
   by_cases hb:b < init.length;swap;exact Or.inr (Or.inr (by omega))
   left;rw[heq,List.append_assoc,listGetN_append_left ha,listGetN_append_left hb,listGetN_append_right (Nat.le_refl _),Nat.sub_self];rfl
  | succ j=>simpa[decodeBank,show init.length+(j+1)=(init++[z]).length+j by simp;omega]using ih (init++[z]) j g (by simpa using hg)
def selectLive{α:Type}(mask:Nat):List α->List α
 | []=>[]
 | w::ws=>cond (Nat.beq (Nat.land mask 1) 1) (w::selectLive (Nat.shiftRight mask 1) ws) (selectLive (Nat.shiftRight mask 1) ws)
noncomputable def splitLiveCPS {β:Type} (nv liveM:Nat) (bank:List Nat)
  (k:List (Nat×Nat)->List (Nat×Nat)->List Nat->β):β:=
 let rec go (bankIdx liveIdx:Nat) (l:List Nat)
   (c:List (Nat×Nat)->List (Nat×Nat)->List Nat->β):β:=
  match l with
  | []=>c [] [] []
  | w::rest=>
   forceN (Nat.add bankIdx 1) λb1=>
   cond (Nat.beq (Nat.land (Nat.shiftRight liveM bankIdx) 1) 1)
    (forceN (Nat.add liveIdx 1) λl1=>
     go b1 l1 rest λinps gts ws=>
      cond (Nat.ble b1 nv)
       (c ((liveIdx,bankIdx)::inps) gts (w::ws))
       (c inps ((liveIdx,w)::gts) (w::ws)))
    (go b1 liveIdx rest c)
 go 0 0 bank k
def splitLiveGo(nv liveM:Nat):Nat->Nat->List Nat ->
  (List (Nat×Nat)×List (Nat×Nat)×List Nat)
 | _,_,[]=>([],[],[])
 | bankIdx,liveIdx,w::rest=>
  if liveM.testBit bankIdx then
   let r:=splitLiveGo nv liveM (bankIdx+1) (liveIdx+1) rest
   if bankIdx+1<=nv then((liveIdx,bankIdx)::r.1,r.2.1,w::r.2.2)
   else(r.1,(liveIdx,w)::r.2.1,w::r.2.2)
  else splitLiveGo nv liveM (bankIdx+1) liveIdx rest
private lemma bit_land1_eq (m i:Nat) :
  Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1=m.testBit i:=by
 have h1:Nat.land (Nat.shiftRight m i) 1=(m / 2^i) % 2:=by change (m>>>i)&&&1=_;rw[Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod]
 rw[h1,Nat.testBit_eq_decide_div_mod_eq];rcases(show m / 2^i % 2=0\/m / 2^i % 2=1 by omega)with h|h<;>rw[h]<;>decide
theorem splitLiveCPS_spec {β:Type} (nv liveM:Nat) (bank:List Nat)
  (k:List (Nat×Nat)->List (Nat×Nat)->List Nat->β) :
  let r:=splitLiveGo nv liveM 0 0 bank
  splitLiveCPS nv liveM bank k=k r.1 r.2.1 r.2.2:=by
 have hgo:∀bi li l (c:List (Nat×Nat)->List (Nat×Nat)->List Nat->β),
   splitLiveCPS.go nv liveM bi li l c=let r:=splitLiveGo nv liveM bi li l;c r.1 r.2.1 r.2.2:=by
  intro bi li l;induction l generalizing bi li with
  | nil=>intro _;rfl
  | cons w rest ih=>
   intro c;simp only[splitLiveCPS.go,splitLiveGo,forceN_eq,bit_land1_eq]
   cases liveM.testBit bi;· simpa using ih (bi+1) li c
   ·simp only[Bool.cond_true,ite_true];rw[ih (bi+1) (li+1)]
    by_cases hle:bi+1<=nv<;>simp[hle,Nat.ble_eq,ble_false_of_gt]
 exact hgo 0 0 bank k
theorem splitLive_ws_eq_selectLive(nv liveM:Nat)(bank:List Nat):
  (splitLiveGo nv liveM 0 0 bank).2.2=selectLive liveM bank:=by
 have hgo:∀bi li l,(splitLiveGo nv liveM bi li l).2.2=selectLive (Nat.shiftRight liveM bi) l:=by
  intro bi li l;induction l generalizing bi li with
  | nil=>rfl
  | cons w rest ih=>
   have hsh:Nat.shiftRight (Nat.shiftRight liveM bi) 1=Nat.shiftRight liveM (bi+1):=
    Nat.eq_of_testBit_eq λr=>by simp[show bi+(1+r)=bi+1+r by omega]
   simp only[splitLiveGo,selectLive,bit_land1_eq,hsh]
   cases liveM.testBit bi;· simpa using ih (bi+1) li
   ·simp only[ite_true,Bool.cond_true];split_ifs<;>simp[ih (bi+1) (li+1)]
 simpa using hgo 0 0 bank
abbrev Wire(R:Type):=R->Bool
def inv{R:Type}(a:Wire R):Wire R:=λr=> !(a r)
def combine{R:Type}(isOr:Bool)(a b:Wire R):Wire R:=
 λr=>if isOr then a r||b r else a r&&b r
def comb{R:Type}(d:Nat)(a b:Wire R):Wire R:=
 λr=>binBool d (a r) (b r)
def Constant{R:Type}(a:Wire R):Prop:=∃b:Bool,a=λ_=>b
noncomputable def cost{R:Type}(a:Wire R):Nat:=by classical exact if Constant a then 1 else 0
noncomputable def mass{R:Type}(xs:List (Wire R)):Nat:=(xs.map cost).sum
def Available{R:Type}(pool:List (Wire R))(v:Wire R):Prop:=
 v∈pool\/Constant v\/inv v∈pool
def supply{R:Type}(pool xs:List (Wire R)):Prop:=∀a∈xs,Available pool a
def Reach{R:Type}(roots:List (Wire R)):Nat->List (Wire R)->Prop
 | 0,bank=>bank=roots
 | p+1,bank=>∃(prev:List (Wire R))(a b:Wire R)(op:Bool),Reach roots p prev /\
  Available prev a/\Available prev b/\bank=combine op a b::prev
theorem Reach.start{R:Type}{roots:List (Wire R)}:Reach roots 0 roots:=rfl
theorem Reach.two {R:Type} {roots:List (Wire R)} {p bank a b} (op:Bool) (h:Reach roots p bank)
  (ha:Available bank a) (hb:Available bank b):Reach roots (p+1) (combine op a b::bank):=
 ⟨bank,a,b,op,h,ha,hb,rfl⟩
def kept{α:Type}(save:Bool)(x:α)(xs:List α):List α:=if save then x::xs else xs
def Run{R:Type}(goal:Wire R):Nat->List (Wire R)->Prop
 | 0,ws=>ws.Perm [goal]
 | s+1,ws=>∃(a b:Wire R)(rest:List (Wire R))(d:Nat)(ka kb:Bool),
  d<4/\ws.Perm (a::b::rest)/\Run goal s (comb d a b::kept ka a (kept kb b rest))
theorem Run.stop{R:Type}{goal:Wire R}:Run goal 0 [goal]:=List.Perm.refl _
theorem Run.perm {R:Type} {goal:Wire R} {s:Nat} {xs zs:List (Wire R)} (p:xs.Perm zs)
  (h:Run goal s xs):Run goal s zs:=by
 cases s with
 | zero=>exact p.symm.trans h
 | succ s=>obtain⟨a,b,rest,d,ka,kb,hd,q,tail⟩:=h;exact⟨a,b,rest,d,ka,kb,hd,p.symm.trans q,tail⟩
theorem Run.two {R:Type} {goal:Wire R} {s:Nat} {a b:Wire R} {rest:List (Wire R)}
  (d:Nat) (hd:d<4) (ka kb:Bool) (tail:Run goal s (comb d a b::kept ka a (kept kb b rest))) :
  Run goal (s+1) (a::b::rest):=
 ⟨a,b,rest,d,ka,kb,hd,List.Perm.refl _,tail⟩
theorem Run.ind {R:Type} {goal:Wire R} {motive:∀s ws,Run goal s ws->Prop}
  (stop:motive 0 [goal] Run.stop)
  (perm:∀{s xs zs}(p:xs.Perm zs)(h:Run goal s xs),motive s xs h->motive s zs (Run.perm p h))
  (two:∀{s a b rest} (d) (hd:d<4) (ka kb) (tail:Run goal s (comb d a b::kept ka a (kept kb b rest))),
   motive s _ tail->motive (s+1) (a::b::rest) (Run.two d hd ka kb tail))
  {s ws} (h:Run goal s ws):motive s ws h:=by
 induction s generalizing ws with
 | zero=>exact perm h.symm Run.stop stop
 | succ s ih=>obtain⟨a,b,rest,d,ka,kb,hd,p,tail⟩:=h;exact perm p.symm _ (two d hd ka kb tail (ih tail))
theorem mass_cons{R:Type}(a:Wire R)(xs:List (Wire R)):mass (a::xs)=cost a+mass xs:=by simp[mass]
theorem mass_kept{R:Type}(a:Wire R)(xs:List (Wire R))(k:Bool):mass xs<=mass (kept k a xs):=by
 cases k<;>simp[kept,mass_cons]
theorem inv_constant{R:Type}{a:Wire R}(h:Constant a):Constant (inv a):=by
 obtain⟨v,rfl⟩:=h;exact⟨!v,rfl⟩
theorem inv_inv'{R:Type}(a:Wire R):inv (inv a)=a:=by funext r;simp[inv]
theorem avail_inv{R:Type}{bank:List (Wire R)}{a:Wire R}(h:Available bank a):Available bank (inv a):=by
 rcases h with hm|hc|hi
 ·exact Or.inr (Or.inr (by simpa[inv_inv']using hm))
 ·exact Or.inr (Or.inl (inv_constant hc))
 ·exact Or.inl hi
theorem both_constant{R:Type}{a b:Wire R}(op:Bool)(h:Constant a)(g:Constant b):
  Constant (combine op a b):=by
 obtain⟨v,rfl⟩:=h;obtain⟨w,rfl⟩:=g;exact⟨if op then v||w else v&&w,rfl⟩
theorem from_constant {R:Type} (op:Bool) {a b:Wire R} {bank:List (Wire R)}
  (ha:Available bank a) (hb:Available bank b) (hc:Constant a\/Constant b) :
  Available bank (combine op a b):=by
 have one u v (hv:Available bank v) (hu:Constant u):Available bank (combine op u v):=by
  obtain⟨c,rfl⟩:=hu;cases op<;>cases c
  ·exact Or.inr (Or.inl ⟨false,rfl⟩)
  ·rwa[show combine false (λ_=>true) v=v from funext λ_=>Bool.true_and _]
  ·rwa[show combine true (λ_=>false) v=v from funext λ_=>Bool.false_or _]
  ·exact Or.inr (Or.inl ⟨true,rfl⟩)
 exact hc.elim (one a b hb) λh=>by
  rw[show combine op a b=combine op b a from funext λ_=>by cases op<;>simp[combine,Bool.and_comm,Bool.or_comm]]
  exact one b a ha h
theorem available_cons{R:Type}{bank:List (Wire R)}{v:Wire R}(w:Wire R)(h:Available bank v):
  Available (w::bank) v:=
 h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
theorem extend_two {R:Type} (roots:List (Wire R)) {p bank a b} (op:Bool) (hp:Reach roots p bank)
  (ha:Available bank a) (hb:Available bank b) :
  ∃q next,q+cost a+cost b<=p+1+cost (combine op a b)/\Reach roots q next /\
   Available next (combine op a b)/\∀v,Available bank v->Available next v:=by
 by_cases hc:Constant a\/Constant b
 ·exact⟨p,bank,by by_cases ha':Constant a<;>by_cases hb':Constant b<;>by_cases m:Constant (combine op a b)<;>simp[cost,ha',hb',m];exact absurd (both_constant op ha' hb') m;exact absurd hc (by tauto),hp,from_constant op ha hb hc,λ_ h=>h⟩
 ·exact⟨p+1,combine op a b::bank,by simp[cost,show ¬Constant a from λh=>hc (Or.inl h),show ¬Constant b from λh=>hc (Or.inr h)],Reach.two op hp ha hb,Or.inl (by simp),λ_ h=>available_cons _ h⟩
theorem comb_prime {R:Type} {bank:List (Wire R)} {d:Nat} {a b:Wire R}
  (hd:d<4) (ha:Available bank a) (hb:Available bank b) :
  ∃op x y,Available bank x/\Available bank y/\comb d a b=combine op x y /\
   cost x=cost a/\cost y=cost b:=by
 have ci (w:Wire R):cost (inv w)=cost w:=by
  by_cases h:Constant w;· simp[cost,h,inv_constant h]
  ·simp[cost,h,show ¬Constant (inv w) from λg=>h (by simpa[inv_inv']using inv_constant g)]
 rcases lt4_cases hd with rfl|rfl|rfl|rfl
 ·exact⟨false,a,b,ha,hb,rfl,rfl,rfl⟩
 ·exact⟨true,a,b,ha,hb,rfl,rfl,rfl⟩
 ·exact⟨false,a,inv b,ha,avail_inv hb,rfl,rfl,ci b⟩
 ·exact⟨false,inv a,b,avail_inv ha,hb,rfl,ci a,rfl⟩
theorem extend_comb {R:Type} (roots:List (Wire R)) {p bank a b} (d:Nat) (hd:d<4)
  (hp:Reach roots p bank) (ha:Available bank a) (hb:Available bank b) :
  ∃q next,q+cost a+cost b<=p+1+cost (comb d a b)/\Reach roots q next /\
   Available next (comb d a b)/\∀v,Available bank v->Available next v:=by
 obtain⟨op,x,y,hx,hy,eq,cx,cy⟩:=comb_prime hd ha hb;rw[eq,<-cx,<-cy];exact extend_two roots op hp hx hy
theorem from_constant_comb {R:Type} {d:Nat} (hd:d<4) {a b:Wire R} {bank:List (Wire R)}
  (ha:Available bank a) (hb:Available bank b) (hc:Constant a\/Constant b) :
  Available bank (comb d a b):=by
 obtain⟨op,x,y,hx,hy,eq,cx,cy⟩:=comb_prime hd ha hb;rw[eq]
 have f {w u:Wire R} (e:cost w=cost u) (hu:Constant u):Constant w:=by_contra λhn=>by simp[cost,hu,hn]at e
 exact from_constant op hx hy (hc.imp (f cx) (f cy))
theorem contraction {R:Type} {goal:Wire R} (nc:¬Constant goal) {s ws} (run:Run goal s ws)
  {roots p bank} (hp:Reach roots p bank) (hs:supply bank ws) :
  ∃q out,q+mass ws<=p+s/\Reach roots q out/\Available out goal:=by
 induction run using Run.ind generalizing p bank with
 | stop=>exact⟨p,bank,by simp[mass,cost,nc],hp,hs _ (by simp)⟩
 | @perm s xs zs eq _ ih=>
  obtain⟨q,out,hq,hr,hg⟩:=ih hp λa ha=>hs a (eq.subset ha)
  exact⟨q,out,by simpa[mass,(eq.map cost).sum_eq]using hq,hr,hg⟩
 | @two s a b rest d hd ka kb tail ih=>
  have ha:=hs a (by simp);have hb:=hs b (by simp)
  obtain⟨q,mid,hq,hreach,hz,lift⟩:=extend_comb roots d hd hp ha hb
  obtain⟨r,out,hr,hfin,hg⟩:=ih hreach λv hv=>(List.mem_cons.mp hv).elim (·▸hz) λhv=>by
   have:v=a\/v=b\/v∈rest:=by cases ka<;>cases kb<;>simp[kept]at hv<;>tauto
   rcases this with rfl|rfl|hm;exact lift _ ha;exact lift _ hb;exact lift _ (hs _ (by simp[hm]))
  have:=mass_kept b rest kb;have:=mass_kept a (kept kb b rest) ka;rw[mass_cons]at hr;rw[mass_cons,mass_cons]
  exact⟨r,out,by omega,hfin,hg⟩
def restrictRows{R S:Type}(rows:S->R)(a:Wire R):Wire S:=λr=>a (rows r)
theorem restrict_kept{R S:Type}(rows:S->R)(k:Bool)(a:Wire R)(ws:List (Wire R)):
 (kept k a ws).map (restrictRows rows)=kept k (restrictRows rows a) (ws.map (restrictRows rows)):=by cases k<;>rfl
theorem restrict_comb{R S:Type}(rows:S->R)(d:Nat)(a b:Wire R):
 restrictRows rows (comb d a b)=comb d (restrictRows rows a) (restrictRows rows b):=rfl
theorem restrict_run{R S:Type}(rows:S->R){goal s ws}(h:Run goal s ws):
  Run (restrictRows rows goal) s (ws.map (restrictRows rows)):=by
 induction h using Run.ind with
 | stop=>exact Run.stop
 | perm p _ ih=>exact Run.perm (p.map _) ih
 | two d hd ka kb _ ih=>rw[List.map_cons,restrict_comb,restrict_kept,restrict_kept]at ih;exact Run.two d hd ka kb ih
theorem projected_bound {R S:Type} (rows:S->R) {goal s ws} (h:Run goal s ws)
  (nc:¬Constant (restrictRows rows goal)) {roots p bank}
  (hp:Reach roots p bank) (hs:supply bank (ws.map (restrictRows rows)))
  {L:Nat} (lo:∀q out,Reach roots q out->Available out (restrictRows rows goal)->L<=q) :
  L+mass (ws.map (restrictRows rows))<=p+s:=by
 obtain⟨q,out,hq,hr,hg⟩:=contraction nc (restrict_run rows h) hp hs;have:=lo q out hr hg;omega
def observeNv(nv w:Nat):Wire (RowNv nv):=λr=>w.testBit r.1
def LiveNv(nv goal:Nat):Nat->Finset Nat->Prop
 | 0,S=>S={goal}/\properNv nv goal
 | k+1,S=>∃(U:Finset Nat)(a b:Nat)(d:Nat),d<4/\S=insert a (insert b U) /\
  properNv nv a/\properNv nv b/\a≠b /\
  zN d a b∉insert a (insert b U)/\LiveNv nv goal k (insert (zN d a b) U)
theorem LiveNv.stop{nv goal:Nat}(hp:properNv nv goal):LiveNv nv goal 0 {goal}:=⟨rfl,hp⟩
theorem LiveNv.binary {nv goal k:Nat} {U:Finset Nat} {a b d:Nat} (hd:d<4)
  (ha:properNv nv a) (hb:properNv nv b) (hab:a≠b)
  (hfresh:zN d a b∉insert a (insert b U)) (tail:LiveNv nv goal k (insert (zN d a b) U)) :
  LiveNv nv goal (k+1) (insert a (insert b U)):=
 ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveNv.ind {nv goal:Nat} {motive:∀(k:Nat)(S:Finset Nat),LiveNv nv goal k S->Prop}
  (stop:∀(hp:properNv nv goal),motive 0 {goal} (LiveNv.stop hp))
  (binary:∀{k:Nat}{U:Finset Nat}{a b d:Nat}(hd:d<4)
   (ha:properNv nv a) (hb:properNv nv b) (hab:a≠b)
   (hfresh:zN d a b∉insert a (insert b U)) (tail:LiveNv nv goal k (insert (zN d a b) U)),
   motive k (insert (zN d a b) U) tail ->
   motive (k+1) (insert a (insert b U)) (LiveNv.binary hd ha hb hab hfresh tail))
  {k:Nat} {S:Finset Nat} (h:LiveNv nv goal k S):motive k S h:=by
 induction k generalizing S with
 | zero=>obtain⟨rfl,hp⟩:=h;exact stop hp
 | succ k ih=>obtain⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩:=h;exact binary hd ha hb hab hf tail (ih tail)
theorem liveNv_proper{nv goal k S}(h:LiveNv nv goal k S):∀a∈S,properNv nv a:=by
 induction h using LiveNv.ind with
 | stop hp=>simpa using hp
 | binary _ ha hb _ _ _ ih=>simp[Finset.forall_mem_insert];exact⟨ha,hb,λa hm=>ih a (Finset.mem_insert_of_mem hm)⟩
theorem liveNv_size{nv goal k S}(h:LiveNv nv goal k S):S.card<=k+1:=by
 induction h using LiveNv.ind with
 | stop _=>simp
 | @binary k U a b d _ _ _ _ hf _ ih=>
  rw[Finset.card_insert_of_notMem λhm=>hf (by simp[hm])]at ih
  have:=Finset.card_insert_le a (insert b U);have:=Finset.card_insert_le b U;omega
theorem liveNv_row_difference {nv goal k S} (h:LiveNv nv goal k S) {r s:RowNv nv}
  (diff:goal.testBit r.1≠goal.testBit s.1) :
  ∃a∈S,a.testBit r.1≠a.testBit s.1:=by
 induction h using LiveNv.ind with
 | stop _=>exact⟨goal,by simp,diff⟩
 | @binary k U a b d _ _ _ _ _ _ ih=>
  obtain⟨v,hv,hd⟩:=ih
  rcases Finset.mem_insert.mp hv with rfl|hu
  ·by_cases aeq:a.testBit r.1=a.testBit s.1
   ·exact⟨b,by simp,λbeq=>hd (by rw[zN_spec,zN_spec,aeq,beq])⟩
   ·exact⟨a,by simp,aeq⟩
  ·exact⟨v,by simp[hu],hd⟩
theorem list_runNv{nv goal k S}(h:LiveNv nv goal k S)(v:List Nat)(hv:v.Nodup)(he:v.toFinset=S):
  Run (observeNv nv goal) k (v.map (observeNv nv)):=by
 classical
 induction h using LiveNv.ind generalizing v with
 | stop _=>exact Run.perm ((List.perm_of_nodup_nodup_toFinset_eq hv (List.nodup_singleton _) (by simpa using he)).symm.map _) Run.stop
 | @binary k U a b d hd _ _ hab hfresh tail ih=>
  let rest:=(v.erase a).erase b;have hr:rest.Nodup:=(hv.erase a).erase b
  have hru x:x∈rest↔x∈U/\x≠a/\x≠b:=by
   have:=congrArg (x∈·) he;simp[rest,(hv.erase a).mem_erase_iff,hv.mem_erase_iff]at this ⊢;tauto
  let ka:=decide (a∈U);let kb:=decide (b∈U);let tailL:=kept ka a (kept kb b rest)
  have hmt x:x∈tailL↔x∈U:=by
   have:ka=true↔a∈U:=decide_eq_true_iff;have:kb=true↔b∈U:=decide_eq_true_iff
   by_cases hxa:x=a<;>by_cases hxb:x=b<;>cases hka:ka<;>cases hkb:kb<;>simp_all[tailL,kept]
  have prog:=ih (zN d a b::tailL)
   (List.nodup_cons.mpr ⟨λhm=>hfresh (by simp[(hmt _).mp hm]),by cases hka:ka<;>cases hkb:kb<;>simp[tailL,kept,hka,hkb,hr,hru,hab]⟩)
   (by ext x;simp[hmt])
  have hm sv x xs:(kept sv x xs).map (observeNv nv)=kept sv (observeNv nv x) (xs.map (observeNv nv)):=by cases sv<;>rfl
  rw[List.map_cons,show observeNv nv (zN d a b)=comb d (observeNv nv a) (observeNv nv b) from funext λr=>zN_spec d a b r.1,hm,hm]at prog
  have hperm:(a::b::rest).Perm v:=List.perm_of_nodup_nodup_toFinset_eq (by simp[hab,hru,hr]) hv
   (by ext x;simp[List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,he,hru];tauto)
  exact Run.perm (hperm.map _) (Run.two d hd ka kb prog)
def ImpossibleNv(nv goal cap:Nat)(S:Finset Nat):Prop:=
 ∀k,k<=cap->¬LiveNv nv goal k S
def evalGateNv(nv:Nat)(w:List Nat)(g:Gate):Nat:=
 let xs:=g.inputs.map (λi=>listGetN w i)
 match g.op with
 | .and=>xs.foldr (λa b=>Nat.land a b) (maskC nv)
 | .or=>xs.foldr (λa b=>Nat.lor a b) 0
 | .not=>Nat.xor (xs.headD 0) (maskC nv)
 | _=>0
def evalCircuitNv(nv:Nat)(gs:List Gate)(init:List Nat):List Nat:=
 gs.foldl (λl g=>l++[evalGateNv nv l g]) init
def freeVarsNv(nv fixedM:Nat):List Nat:=
 let rec go:Nat->List Nat->List Nat
  | 0,acc=>acc
  | u+1,acc=>
   if fixedM.testBit u then go u acc else go u (hiC nv u::acc)
 go nv []
def ColLowerBound(nv goal zM oM lb:Nat):Prop:=
 let d:=subcubeNv nv zM oM
 let raw:=freeVarsNv nv (Nat.lor zM oM)
 ∃(f:RowNv nv->RowNv nv)(roots:List (Wire (RowNv nv))),
  (∀r,d.testBit (f r).1=true) /\
  (∀a∈raw,Available roots (restrictRows f (observeNv nv a))) /\
  ¬Constant (restrictRows f (observeNv nv goal)) /\
  (∀q bank,Reach roots q bank->Available bank (restrictRows f (observeNv nv goal))->lb<=q)
def onlyDiffNv(nv:Nat)(S:Finset Nat)(goal v:Nat)(r s:RowNv nv):Prop:=
 v∈S/\goal.testBit r.1≠goal.testBit s.1 /\
 ∀w∈S,w.testBit r.1≠w.testBit s.1↔w=v
def signedOrderLawOnNv(nv:Nat)(A S:Finset Nat)(goal:Nat)(f:Nat->Nat):Prop:=
 (∀{v w:Nat}{r1 na nb r2 pa pb:RowNv nv},v∈A->w∈A->v≠w ->
  onlyDiffNv nv S goal v r1 na->onlyDiffNv nv S goal w r1 nb ->
  onlyDiffNv nv S goal v r2 pa->onlyDiffNv nv S goal w r2 pb ->
  (v.testBit r1.1≠v.testBit r2.1\/w.testBit r1.1≠w.testBit r2.1)->f v≠f w) /\
 (∀{v w t:Nat}{p1 n1 na1 pb1 p2 n2 na2 pb2:RowNv nv},v∈A->w∈A->t∈A->v≠w ->
  onlyDiffNv nv S goal v p1 na1->onlyDiffNv nv S goal w pb1 n1->onlyDiffNv nv S goal t p1 n1 ->
  onlyDiffNv nv S goal v p2 na2->onlyDiffNv nv S goal w pb2 n2->onlyDiffNv nv S goal t p2 n2 ->
  (v.testBit p1.1≠v.testBit p2.1\/w.testBit n1.1≠w.testBit n2.1) ->
  f v=f w->f t<=f v)
def sensA(d:Nat):Bool:=if d=0 then true else if d=1 then false else if d=2 then true else false
def sensB(d:Nat):Bool:=if d=0 then true else if d=1 then false else if d=2 then false else true
private lemma onlyDiffNv_drop_a {nv goal U a b d k} {r s:RowNv nv} (hd:d<4) (hab:a≠b)
  (haU:a∉U) (hfresh:zN d a b∉insert a (insert b U))
  (tail:LiveNv nv goal k (insert (zN d a b) U))
  (hod:onlyDiffNv nv (insert a (insert b U)) goal a r s) :
  onlyDiffNv nv (insert (zN d a b) U) goal (zN d a b) r s/\b.testBit r.1=sensB d:=by
 have hb:b.testBit r.1=b.testBit s.1:=by_contra λh=>hab ((hod.2.2 b (by simp)).mp h).symm
 have hU w (hw:w∈U):w.testBit r.1=w.testBit s.1:=by_contra λh=>haU ((hod.2.2 w (by simp[hw])).mp h▸hw)
 have hz:(zN d a b).testBit r.1≠(zN d a b).testBit s.1:=by
  obtain⟨w,hw,hne⟩:=liveNv_row_difference tail hod.2.1
  exact(Finset.mem_insert.mp hw).elim (·▸hne) λhu=>absurd (hU w hu) hne
 refine⟨⟨Finset.mem_insert_self _ _,hod.2.1,λw hw=>(Finset.mem_insert.mp hw).elim (λe=>by simp[e,hz])
  λhu=>by simp[hU w hu,show w≠zN d a b from λe=>hfresh (by simp[e▸hu])]⟩,?_⟩
 rw[zN_spec,zN_spec,<-hb]at hz;revert hz
 rcases lt4_cases hd with rfl|rfl|rfl|rfl<;>cases a.testBit r.1<;>cases a.testBit s.1<;>cases b.testBit r.1<;>simp[binBool,sensB]
private lemma onlyDiffNv_drop_b {nv goal U a b d k} {r s:RowNv nv} (hd:d<4) (hab:a≠b)
  (hbU:b∉U) (hfresh:zN d a b∉insert a (insert b U))
  (tail:LiveNv nv goal k (insert (zN d a b) U))
  (hod:onlyDiffNv nv (insert a (insert b U)) goal b r s) :
  onlyDiffNv nv (insert (zN d a b) U) goal (zN d a b) r s/\a.testBit r.1=sensA d:=by
 have hsf:sensA d=sensB (flipOp d):=by rcases lt4_cases hd with rfl|rfl|rfl|rfl<;>rfl
 rw[zN_flip hd a b]at hfresh tail ⊢;rw[Finset.insert_comm]at hfresh hod
 simpa[hsf]using onlyDiffNv_drop_a (flip_flip hd).1 hab.symm hbU hfresh tail hod
private lemma onlyDiffNv_symm {nv S goal v} {r s:RowNv nv} (h:onlyDiffNv nv S goal v r s) :
  onlyDiffNv nv S goal v s r:=
 ⟨h.1,h.2.1.symm,λw hw=>by rw[ne_comm];exact h.2.2 w hw⟩
private lemma pull_order_core_nv {nv goal U a b d k} (hd:d<4) (hab:a≠b)
  (hfresh:zN d a b∉insert a (insert b U))
  (tail:LiveNv nv goal k (insert (zN d a b) U))
  {f':Nat->Nat} (law':signedOrderLawOnNv nv (insert (zN d a b) U) (insert (zN d a b) U) goal f')
  {A:Finset Nat} (hA_sub:A⊆insert a (insert b U))
  (hA_a:a∈A->a∉U) (hA_b:b∈A->b∉U) :
  signedOrderLawOnNv nv A (insert a (insert b U)) goal
   (λv=>if v=a\/v=b then f' (zN d a b)else f' v):=by
 let S:=insert a (insert b U);let z:=zN d a b;let Q:=insert z U;let m v:=if v=a\/v=b then z else v
 let D X:=onlyDiffNv nv X goal;let j {X v r s}:=@onlyDiffNv_symm nv X goal v r s
 rw[show(λv=>if v=a\/v=b then f' z else f' v)=λv=>f' (m v) from funext λv=>by dsimp[m];split_ifs<;>rfl]
 have da {r s} h:=onlyDiffNv_drop_a hd hab (hA_a h) hfresh tail (r:=r) (s:=s)
 have db {r s} h:=onlyDiffNv_drop_b hd hab (hA_b h) hfresh tail (r:=r) (s:=s)
 have M v (h:v∈A):m v∈Q:=by have:=hA_sub h;dsimp[m];split_ifs<;>simp_all[Q]
 have F {v r s} (h:v∈A) (o:D S v r s):D Q (m v) r s:=by
  dsimp[m]
  by_cases e:v=a;· subst e;simp[true_or,ite_true];exact(da h o).1
  by_cases e':v=b;· subst e';simp[or_true,ite_true];exact(db h o).1
  simp[e,e',or_self,ite_false];have hv:v∈U:=by have:=o.1;simp_all[S]
  have q x (hx:x∈S) (hn:x≠v):=by_contra λg=>hn ((o.2.2 x hx).mp g)
  refine⟨Finset.mem_insert_of_mem hv,o.2.1,λw c=>(Finset.mem_insert.mp c).elim ?_ λu=>o.2.2 w (by simp[S,u])⟩
  rintro rfl;simp[z,zN_spec,q a (by simp[S]) (Ne.symm e),q b (by simp[S]) (Ne.symm e'),show zN d a b≠v from λez=>hfresh (ez▸o.1)]
 have V {v r s t u} (h:v∈A) (o1:D S v r s) (o2:D S v t u) (l:v.testBit r.1≠v.testBit t.1):(m v).testBit r.1≠(m v).testBit t.1:=by
  dsimp[m];by_cases e:v=a
  ·subst e;simp[true_or,ite_true,z];rw[zN_spec,zN_spec,(da h o1).2,(da h o2).2]
   revert l;rcases lt4_cases hd with rfl|rfl|rfl|rfl<;>cases v.testBit r.1<;>cases v.testBit t.1<;>simp[binBool,sensB]
  by_cases e':v=b
  ·subst e';simp[or_true,ite_true,z];rw[zN_spec,zN_spec,(db h o1).2,(db h o2).2]
   revert l;rcases lt4_cases hd with rfl|rfl|rfl|rfl<;>cases v.testBit r.1<;>cases v.testBit t.1<;>simp[binBool,sensA]
  simpa[e,e']using l
 have E {v w} (hv:v∈A) (hw:w∈A) (hn:v≠w) (e:m v=m w):(v=a/\w=b)\/(v=b/\w=a):=by
  have q x (h:x∈A):x≠z:=λez=>hfresh (by simpa[z,<-ez]using hA_sub h)
  have:=q v hv;have:=q w hw;dsimp[m]at e;split_ifs at e<;>grind
 have W {x y r s t u} (o:(x=a/\y=b)\/(x=b/\y=a)) (h:x∈A) (o1:D S x r s) (o2:D S x t u):y.testBit r.1=y.testBit t.1:=by
  rcases o with ⟨rfl,rfl⟩|⟨rfl,rfl⟩;exact(da h o1).2.trans (da h o2).2.symm;exact(db h o1).2.trans (db h o2).2.symm
 refine⟨λ{v w _ _ _ _ _ _} hv hw hn v1 w1 v2 w2 g=> ?_,λ{v w t _ _ _ _ _ _ _ _} hv hw ht hn v1 w1 t1 v2 w2 t2 g fe=> ?_⟩
 ·by_cases e:m v=m w
  ·have o:=E hv hw hn e;exact g.elim (absurd (W (by grind) hw w1 w2)) (absurd (W o hv v1 v2))
  ·exact law'.1 (M v hv) (M w hw) e (F hv v1) (F hw w1) (F hv v2) (F hw w2) (g.imp (V hv v1 v2) (V hw w1 w2))
 ·by_cases et:m t=m v;· exact Nat.le_of_eq (congrArg f' et)
  by_cases e:m v=m w
  ·have o:=E hv hw hn e
   have Y {x p n} (hx:x=a\/x=b) (hA:x∈A) (td:D S t p n):=
    by_contra λhh=>et (by have q:=(td.2.2 x (hA_sub hA)).mp hh;subst q;rcases o with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>simp[m,hx])
   exact g.elim (absurd ((Y (by grind) hv t1).trans ((W (by grind) hw (j w1) (j w2)).trans (Y (by grind) hv t2).symm)))
    (absurd ((Y (by grind) hw t1).symm.trans ((W o hv v1 v2).trans (Y (by grind) hw t2))))
  ·exact law'.2 (M v hv) (M w hw) (M t ht) e (F hv v1) (j (F hw (j w1))) (F ht t1)
    (F hv v2) (j (F hw (j w2))) (F ht t2) (g.imp (V hv v1 v2) (V hw (j w1) (j w2))) fe
private lemma lift_one_min_nv {nv A S goal a} {f:Nat->Nat} {C:Nat}
  (hbnd:∀v∈A.erase a,f v<C) (hlaw:signedOrderLawOnNv nv (A.erase a) S goal f) :
  ∃g:Nat->Nat,(∀v∈A,g v<C+1)/\signedOrderLawOnNv nv A S goal g:=by
 classical
 have e {x} (h:x∈A) (n:x≠a):=Finset.mem_erase.mpr ⟨n,h⟩
 refine⟨λv=>if v=a then 0 else f v+1,λv h=>by
  dsimp;split_ifs with q;omega;have:=hbnd v (e h q);omega,
  λ{v w _ _ _ _ _ _} hv hw n v1 w1 v2 w2 g=>by dsimp only;(split_ifs<;>try omega);have:=hlaw.1 (e hv ‹_›) (e hw ‹_›) n v1 w1 v2 w2 g;omega,
  λ{v w t _ _ _ _ _ _ _ _} hv hw ht n v1 w1 t1 v2 w2 t2 g fe=>by dsimp at fe ⊢;(split_ifs at fe ⊢<;>try omega);have:=hlaw.2 (e hv ‹_›) (e hw ‹_›) (e ht ‹_›) n v1 w1 t1 v2 w2 t2 g (by omega);omega⟩
theorem signed_order_live_nv{nv goal k S}(h:LiveNv nv goal k S):
  ∃f:Nat->Nat,(∀v∈S,f v<k+2-S.card)/\signedOrderLawOnNv nv S S goal f:=by
 classical
 induction h using LiveNv.ind with
 | stop _=>refine⟨λ_=>0,λ_ _=>by simp,?_,?_⟩<;>(intros;simp_all)
 | @binary k U a b d hd _ _ hab hfresh tail ih=>
  obtain⟨f',fb,fl⟩:=ih;have:=liveNv_size tail
  have hct:(insert (zN d a b) U).card=U.card+1:=Finset.card_insert_of_notMem λm=>hfresh (by simp[m])
  set S:=insert a (insert b U);let g v:=if v=a\/v=b then f' (zN d a b)else f' v
  have hb v (m:v∈S):g v<k+2-(insert (zN d a b) U).card:=by
   dsimp[g];split_ifs;exact fb _ (Finset.mem_insert_self _ _);exact fb v (Finset.mem_insert_of_mem (by simp_all[S]))
  let hp {A}:=@pull_order_core_nv _ _ _ _ _ _ _ hd hab hfresh tail _ fl A
  by_cases ha:a∈U<;>by_cases hb':b∈U
  ·have hS:S=U:=by dsimp[S];rw[Finset.insert_eq_of_mem hb',Finset.insert_eq_of_mem ha]
   obtain⟨g1,b1,l1⟩:=lift_one_min_nv (λv m=>hb v (by simp_all)) (hp ((Finset.erase_subset b _).trans (Finset.erase_subset a _)) (by simp) (by simp))
   obtain⟨g2,b2,l2⟩:=lift_one_min_nv b1 l1
   exact⟨g2,λv m=>by have:=b2 v m;rw[hS]at m ⊢;omega,l2⟩
  ·have:S.card=U.card+1:=by dsimp[S];rw[Finset.insert_comm,Finset.insert_eq_of_mem ha,Finset.card_insert_of_notMem hb']
   obtain⟨g1,b1,l1⟩:=lift_one_min_nv (λv m=>hb v (Finset.mem_of_mem_erase m)) (hp (Finset.erase_subset a _) (by simp) λ_=>hb')
   exact⟨g1,λv m=>by have:=b1 v m;omega,l1⟩
  ·have:S.card=U.card+1:=by dsimp[S];rw[Finset.insert_eq_of_mem hb',Finset.card_insert_of_notMem ha]
   obtain⟨g1,b1,l1⟩:=lift_one_min_nv (λv m=>hb v (Finset.mem_of_mem_erase m)) (hp (Finset.erase_subset b _) (λ_=>ha) (by simp))
   exact⟨g1,λv m=>by have:=b1 v m;omega,l1⟩
  ·have:S.card=U.card+2:=by dsimp[S];rw[Finset.card_insert_of_notMem (by simp[hab,ha]),Finset.card_insert_of_notMem hb']
   exact⟨g,λv m=>by have:=hb v m;omega,hp (Finset.Subset.refl _) (λ_=>ha) λ_=>hb'⟩
private lemma pull_step_nv {nv goal k a b d:Nat} {U A S:Finset Nat}
  (hd:d<4) (hab:a≠b) (hS:S=insert a (insert b U)) (hfresh:zN d a b∉S)
  (hchild:LiveNv nv goal k (insert (zN d a b) U))
  (hsub:A⊆S) (hA_a:a∈A->a∉U) (hA_b:b∈A->b∉U) :
  ∃f:Nat->Nat,(∀v∈A,f v<k+2-(insert (zN d a b) U).card) /\
   f a=f b/\signedOrderLawOnNv nv A S goal f:=by
 classical
 obtain⟨f',b',l'⟩:=signed_order_live_nv hchild
 have l:=pull_order_core_nv hd hab (hS▸hfresh) hchild l' (hS▸hsub) hA_a hA_b;rw[<-hS]at l
 refine⟨λv=>if v=a\/v=b then f' (zN d a b)else f' v,λv hv=> ?_,by simp,l⟩
 have:=hS▸hsub hv;dsimp;split_ifs;exact b' _ (Finset.mem_insert_self _ _);exact b' v (Finset.mem_insert_of_mem (by simp_all))
theorem order_step_00_nv {nv goal k S a b d} (hd:d<4) (ha:a∈S) (hb:b∈S) (hab:a≠b)
  (hfresh:zN d a b∉S)
  (hchild:LiveNv nv goal k (insert (zN d a b) ((S.erase a).erase b))) :
  ∃f:Nat->Nat,(∀v∈S,f v<k+3-S.card)/\f a=f b/\signedOrderLawOnNv nv S S goal f:=by
 classical
 let U:=(S.erase a).erase b
 have hS:S=insert a (insert b U):=by ext x;simp[U,Finset.mem_insert,Finset.mem_erase];grind
 have:S.card=U.card+2:=by rw[hS,Finset.card_insert_of_notMem (by simp[U,hab]),Finset.card_insert_of_notMem (by simp[U])]
 have:(insert (zN d a b) U).card=U.card+1:=Finset.card_insert_of_notMem λm=>hfresh (by rw[hS];simp[m])
 obtain⟨f,b',e,l⟩:=pull_step_nv hd hab hS hfresh hchild (Finset.Subset.refl _) (by simp[U]) (by simp[U])
 exact⟨f,λv hv=>by have:=b' v hv;omega,e,l⟩
theorem order_step_10_nv {nv goal k S a b d} (hd:d<4) (ha:a∈S) (hb:b∈S) (hab:a≠b)
  (hfresh:zN d a b∉S)
  (hchild:LiveNv nv goal k (insert (zN d a b) (S.erase b))) :
  ∃f:Nat->Nat,(∀v∈S.erase a,f v<k+2-S.card)/\signedOrderLawOnNv nv (S.erase a) S goal f:=by
 classical
 let U:=S.erase b
 have hS:S=insert a (insert b U):=by ext x;simp[U,Finset.mem_insert,Finset.mem_erase];grind
 have:S.card=U.card+1:=by rw[hS,Finset.insert_comm,Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨hab,ha⟩),Finset.card_insert_of_notMem (by simp)]
 have:(insert (zN d a b) U).card=U.card+1:=Finset.card_insert_of_notMem λm=>hfresh (by rw[hS];simp[m])
 obtain⟨f,b',_,l⟩:=pull_step_nv hd hab hS hfresh hchild (Finset.erase_subset a _) (by simp) (by simp[U])
 exact⟨f,λv hv=>by have:=b' v hv;omega,l⟩
theorem order_step_11_nv {nv goal k S a b d} (hd:d<4) (ha:a∈S) (hb:b∈S) (hab:a≠b)
  (hfresh:zN d a b∉S)
  (hchild:LiveNv nv goal k (insert (zN d a b) S)) :
  ∃f:Nat->Nat,(∀v∈(S.erase a).erase b,f v<k+1-S.card) /\
   signedOrderLawOnNv nv ((S.erase a).erase b) S goal f:=by
 classical
 have:(insert (zN d a b) S).card=S.card+1:=Finset.card_insert_of_notMem hfresh
 obtain⟨f,b',_,l⟩:=pull_step_nv hd hab (by rw[Finset.insert_eq_of_mem hb,Finset.insert_eq_of_mem ha]) hfresh hchild
  ((Finset.erase_subset b _).trans (Finset.erase_subset a _)) (by simp) (by simp)
 exact⟨f,λv hv=>by have:=b' v hv;omega,l⟩
noncomputable def twoPatRaw(m wx wy:Nat):Bool:=
 forceN (Nat.land m wx) λm1=>
 cond (and (not (Nat.beq m1 0)) (not (Nat.beq m1 m))) true
  (forceN (Nat.land m wy) λm2=>
   and (not (Nat.beq m2 0)) (not (Nat.beq m2 m)))
theorem twoPatRaw_sound{nv m wx wy:Nat}(hm:ValidWord nv m)(h:twoPatRaw m wx wy=true):
  ∃r1 r2:RowNv nv,m.testBit r1.1=true/\m.testBit r2.1=true /\
   (wx.testBit r1.1≠wx.testBit r2.1\/wy.testBit r1.1≠wy.testBit r2.1):=by
 have f (w:Nat) (hw:and (not (Nat.beq (Nat.land m w) 0)) (not (Nat.beq (Nat.land m w) m))=true) :
   ∃r s:RowNv nv,m.testBit r.1=true/\m.testBit s.1=true/\w.testBit r.1≠w.testBit s.1:=by
  simp only[Bool.and_eq_true,Bool.not_eq_true']at hw
  obtain⟨k,g⟩:=exists_testBit_of_ne_zero (m:=Nat.land m w) λe=>by rw[e]at hw;exact Bool.noConfusion hw.1
  obtain⟨l,q⟩:∃k,(Nat.land m w).testBit k≠m.testBit k:=by_contra λa=>by
   have:Nat.land m w=m:=Nat.eq_of_testBit_eq λk=>by_contra λn=>a ⟨k,n⟩
   rw[this,Nat.beq_refl]at hw;exact Bool.noConfusion hw.2
  simp at g q;exact⟨⟨k,lt_of_testBit hm g.1⟩,⟨l,lt_of_testBit hm q.1⟩,g.1,q.1,by simp[g.2,q.2]⟩
 unfold twoPatRaw at h;rw[forceN_eq]at h
 cases c:and (not (Nat.beq (Nat.land m wx) 0)) (not (Nat.beq (Nat.land m wx) m))
 ·rw[c,Bool.cond_false,forceN_eq]at h;obtain⟨r,s,a,b,d⟩:=f wy h;exact⟨r,s,a,b,Or.inr d⟩
 ·obtain⟨r,s,a,b,d⟩:=f wx c;exact⟨r,s,a,b,Or.inl d⟩
noncomputable def orGateDiffsRaw{β:Type}(nv u ef:Nat):List (Nat×Nat)->Nat->(Nat->β)->β
 | [],any2,c=>c any2
 | (_,w)::rest,any2,c=>
  forceN (flipURaw nv u w) λfl=>
  forceN (Nat.lor any2 (Nat.land (Nat.xor w fl) ef)) λna2=>
  orGateDiffsRaw nv u ef rest na2 c
noncomputable def gateDiffsRaw{β:Type}(nv u ef:Nat):List (Nat×Nat)->Nat->Nat->List (Nat×Nat) ->
  (Bool->Nat->List (Nat×Nat)->β)->β
 | [],any1,any2,ds,c=>c (Nat.beq any1 ef) any2 ds
 | (gIdx,w)::rest,any1,any2,ds,c=>
  forceN (flipURaw nv u w) λfl=>
  forceN (Nat.land (Nat.xor w fl) ef) λd=>
  forceN (Nat.lor any1 d) λna1=>
  forceN (Nat.lor any2 (Nat.land any1 d)) λna2=>
  gateDiffsRaw nv u ef rest na1 na2 ((gIdx,d)::ds) c
noncomputable def mkGateCRaw{β:Type}(uniq:Nat):List (Nat×Nat)->List (Nat×Nat)->List Nat ->
  (List (Nat×Nat)->List Nat->β)->β
 | [],accP,accV,c=>c accP accV
 | (gIdx,d)::rest,accP,accV,c=>
  forceN (Nat.land d uniq) λcu=>
  mkGateCRaw uniq rest ((gIdx,cu)::accP) (cu::accV) c
noncomputable def zipOrRaw{β:Type}:List Nat->List Nat->(List Nat->β)->β
 | [],_,c=>c []
 | _,[],c=>c []
 | a::as,b::bs,c=>
  forceN (Nat.lor a b) λv=>
  zipOrRaw as bs λr=>c (v::r)
noncomputable def appRaw{β:Type}:List Nat->List Nat->(List Nat->β)->β
 | [],ys,c=>c ys
 | x::xs,ys,c=>appRaw xs ys λr=>c (x::r)
noncomputable def buildCoordsRaw {β:Type} (nv liveM:Nat) (efFn:Nat->Nat) (gts:List (Nat×Nat))
  (k:Bool->List Nat->List (Nat×List (Nat×Nat))->β):β:=
 let rec loopU:Nat->List Nat->List Nat->List (Nat×List (Nat×Nat)) ->
   (Bool->List Nat->List Nat->List (Nat×List (Nat×Nat))->β)->β
  | 0,inpCrits,gateAcc,deadUs,cont=>cont true inpCrits gateAcc deadUs
  | u'+1,inpCrits,gateAcc,deadUs,cont=>
   let ef:=efFn u'
   cond (Nat.beq (Nat.land (Nat.shiftRight liveM u') 1) 1)
    (orGateDiffsRaw nv u' ef gts 0 λany2=>
     forceN (Nat.xor ef any2) λcu=>
     loopU u' (cu::inpCrits) gateAcc deadUs cont)
    (gateDiffsRaw nv u' ef gts 0 0 [] λok any2 ds=>
     cond ok
      (forceN (Nat.xor ef any2) λuniq=>
       mkGateCRaw uniq ds [] [] λcusP cusV=>
       zipOrRaw gateAcc cusV λgateAcc'=>
       loopU u' inpCrits gateAcc' ((u',cusP)::deadUs) cont)
      (cont false [] [] []))
 loopU nv [] (List.replicate gts.length 0) [] λok inpCrits gateCrits deadUs=>
  cond ok (appRaw inpCrits gateCrits λcaList=>k true caList deadUs) (k false [] [])
abbrev B2(α:Type):=α×α
abbrev B4(α:Type):=B2 α×B2 α
abbrev B8(α:Type):=B4 α×B4 α
abbrev B16(α:Type):=B8 α×B8 α
def b16Get{α:Type}(t:B16 α)(i:Nat):α:=
 let t8:=cond (Nat.beq (Nat.land i 8) 0) t.1 t.2
 let t4:=cond (Nat.beq (Nat.land i 4) 0) t8.1 t8.2
 let t2:=cond (Nat.beq (Nat.land i 2) 0) t4.1 t4.2
 cond (Nat.beq (Nat.land i 1) 0) t2.1 t2.2
noncomputable def mkB16C{α β:Type}(f:Nat->(α->β)->β)(k:B16 α->β):β:=
 f 0 λr0=>f 1 λr1=>f 2 λr2=>f 3 λr3=>
 f 4 λr4=>f 5 λr5=>f 6 λr6=>f 7 λr7=>
 f 8 λr8=>f 9 λr9=>f 10 λr10=>f 11 λr11=>
 f 12 λr12=>f 13 λr13=>f 14 λr14=>f 15 λr15=>
 k ((((r0,r1),(r2,r3)),((r4,r5),(r6,r7))),(((r8,r9),(r10,r11)),((r12,r13),(r14,r15))))
theorem mkB16C_spec {α β:Type} {f:Nat->(α->β)->β} {g:Nat->α}
  (hf:∀i < 16,∀k,f i k=k (g i)) (k:B16 α->β) :
  ∃t,mkB16C f k=k t/\∀i < 16,b16Get t i=g i:=by
 refine⟨((((g 0,g 1),(g 2,g 3)),((g 4,g 5),(g 6,g 7))),
    (((g 8,g 9),(g 10,g 11)),((g 12,g 13),(g 14,g 15)))),by
  simp[mkB16C,hf 0 (by decide),hf 1 (by decide),hf 2 (by decide),hf 3 (by decide),
   hf 4 (by decide),hf 5 (by decide),hf 6 (by decide),hf 7 (by decide),
   hf 8 (by decide),hf 9 (by decide),hf 10 (by decide),hf 11 (by decide),
   hf 12 (by decide),hf 13 (by decide),hf 14 (by decide),hf 15 (by decide)],λi hi=> ?_⟩
 rcases(show i=0\/i=1\/i=2\/i=3\/i=4\/i=5\/i=6\/i=7\/i=8\/i=9\/i=10\/i=11\/i=12\/i=13\/i=14\/i=15 by omega)with
  rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>rfl
noncomputable def allListRec{α:Type}(p:α->Bool)(l:List α):Bool:=
 @List.rec α (λ_=>Bool) true (λx _ ih=>cond (p x) ih false) l
theorem allListRec_iff{α:Type}(p:α->Bool)(l:List α):
  allListRec p l=true↔∀x∈l,p x=true:=by
 induction l with
 | nil=>simp[allListRec]
 | cons x xs ih=>
  change cond (p x) (allListRec p xs) false=true↔∀y∈x::xs,p y=true
  cases hx:p x<;>simp[ih,hx]
def unS(x:Nat):Nat:=Nat.shiftRight x 32
def isZeroS(x:Nat):Bool:=Nat.ble x 0xffffffff
def eqS(x y:Nat):Bool:=Nat.ble (Nat.xor x y) 0xffffffff
theorem unS_land(x y:Nat):unS (Nat.land x y)=Nat.land (unS x) (unS y):=
 Nat.eq_of_testBit_eq λr=>by simp[unS]
theorem unS_xor(x y:Nat):unS (Nat.xor x y)=Nat.xor (unS x) (unS y):=
 Nat.eq_of_testBit_eq λr=>by simp[unS]
theorem unS_eq_zero_iff(x:Nat):unS x=0↔x<2^32:=by
 change x>>>32=0↔x<2^32;rw[Nat.shiftRight_eq_div_pow];omega
theorem isZeroS_eq(x:Nat):isZeroS x=Nat.beq (unS x) 0:=by
 cases h:isZeroS x
 ·have hlt:¬(x<=0xffffffff):=λle=>Bool.noConfusion ((Nat.ble_eq.mpr le).symm.trans h)
  exact(beq_false_of_ne λz=>hlt (by have:=(unS_eq_zero_iff x).mp z;omega)).symm
 ·have le:x<=0xffffffff:=Nat.ble_eq.mp h
  rw[(unS_eq_zero_iff x).mpr (by omega),Nat.beq_refl]
theorem eqS_eq(x y:Nat):eqS x y=Nat.beq (unS x) (unS y):=by
 change isZeroS (Nat.xor x y)=_;rw[isZeroS_eq,unS_xor]
 by_cases h:unS x=unS y
 ·rw[h,show Nat.xor (unS y) (unS y)=0 from Nat.xor_self _,Nat.beq_refl,Nat.beq_refl]
 ·rw[beq_false_of_ne h,beq_false_of_ne λz=>h (Nat.eq_of_testBit_eq λr=>by
   have:=congrArg (·.testBit r) z;simp only[testBit_xor',Nat.zero_testBit]at this
   revert this;cases(unS x).testBit r<;>cases(unS y).testBit r<;>simp)]
theorem unS_xor_tag{x t:Nat}(ht:t<2^32):unS (Nat.xor x t)=unS x:=by
 rw[unS_xor,(unS_eq_zero_iff t).mpr ht];exact Nat.xor_zero _
theorem unS_lor_shl{w t:Nat}(ht:t<2^32):unS (Nat.lor (Nat.shiftLeft w 32) t)=w:=
 Nat.eq_of_testBit_eq λr=>by
  simp[unS,testBit_eq_false_of_lt_pow ht (by omega:32<=32+r)]
theorem land_ff32_lt(x:Nat):Nat.land x 0xffffffff<2^32:=
 lt_two_pow_of_testBit λr hr=>by
  rw[testBit_land',show(0xffffffff:Nat)=2^32-1 from rfl,Nat.testBit_two_pow_sub_one,decide_eq_false (by omega),Bool.and_false]
theorem xor_lt32{a b:Nat}(ha:a<2^32)(hb:b<2^32):Nat.xor a b<2^32:=
 lt_two_pow_of_testBit λr hr=>by
  rw[testBit_xor',testBit_eq_false_of_lt_pow ha hr,testBit_eq_false_of_lt_pow hb hr];rfl
def detVal(w:Nat):Nat:=
 Nat.lor (Nat.shiftLeft w 32) (Nat.lor (Nat.mod (Nat.shiftLeft w 32) 4294967291) 1)
noncomputable def detS{β:Type}(x:Nat)(k:Nat->β):β:=
 forceN (Nat.land x 0xffffffff) λlo=>
 forceN (Nat.mod x 4294967291) λxp=>
 forceN (Nat.lor (Nat.mod (Nat.sub (Nat.add xp 4294967291) (Nat.mod lo 4294967291)) 4294967291) 1) λh=>
 forceN (Nat.xor x (Nat.xor lo h)) k
noncomputable def mkDet{β:Type}(w:Nat)(k:Nat->β):β:=
 forceN (Nat.lor (Nat.shiftLeft w 32) 1) λx=>detS x k
private lemma detHash_lt (w:Nat):Nat.lor (Nat.mod (Nat.shiftLeft w 32) 4294967291) 1<2^32:=
 lt_two_pow_of_testBit λr hr=>by
  have hm:Nat.mod (Nat.shiftLeft w 32) 4294967291<2^32:=
   Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw[testBit_lor',testBit_eq_false_of_lt_pow hm hr,testBit_one,decide_eq_false (by omega)];rfl
theorem unS_detVal(w:Nat):unS (detVal w)=w:=unS_lor_shl (detHash_lt w)
theorem detVal_inj{a b:Nat}(h:detVal a=detVal b):a=b:=by
 have:=congrArg unS h;rwa[unS_detVal,unS_detVal]at this
theorem detS_eq{β:Type}(x:Nat)(k:Nat->β):detS x k=k (detVal (unS x)):=by
 unfold detS;simp only[forceN_eq];apply congrArg k
 set lo:=Nat.land x 0xffffffff;set hi:=Nat.shiftLeft (unS x) 32
 have hlo:lo=x % 2^32:=Nat.eq_of_testBit_eq λr=>by
  rw[show lo=Nat.land x (2^32-1) from rfl,testBit_land',Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow]
  cases decide (r<32)<;>simp
 have hx:x=hi+lo:=by
  rw[hlo,show hi=(x / 2^32)*2^32 by change (x>>>32)<<<32=_;rw[Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq],Nat.mul_comm]
  exact(Nat.div_add_mod x (2^32)).symm
 have hmod:Nat.mod (Nat.sub (Nat.add (Nat.mod x 4294967291) 4294967291) (Nat.mod lo 4294967291)) 4294967291=Nat.mod hi 4294967291:=by
  change (x % 4294967291+4294967291-lo % 4294967291) % 4294967291=hi % 4294967291
  rw[hx];omega
 rw[hmod];apply Nat.eq_of_testBit_eq;intro r
 by_cases hr:r<32
 ·simp only[detVal,testBit_xor',testBit_lor',hi,lo,testBit_land',show(0xffffffff:Nat)=2^32-1 from rfl,
   Nat.testBit_two_pow_sub_one,testBit_shiftLeft',hr,decide_true,Bool.and_true,show ¬(32<=r) by omega,decide_false,Bool.false_and,Bool.false_or]
  cases x.testBit r<;>cases(Nat.mod (Nat.shiftLeft (unS x) 32) 4294967291).testBit r<;>cases(1:Nat).testBit r<;>rfl
 ·have hh0:(Nat.lor (Nat.mod hi 4294967291) 1).testBit r=false:=testBit_eq_false_of_lt_pow (detHash_lt (unS x)) (by omega)
  change (Nat.xor x (Nat.xor lo (Nat.lor (Nat.mod hi 4294967291) 1))).testBit r=(Nat.lor hi (Nat.lor (Nat.mod hi 4294967291) 1)).testBit r
  rw[testBit_xor',testBit_xor',hh0,Bool.xor_false,testBit_lor',hh0,Bool.or_false]
  simp only[lo,hi,unS,testBit_land',show(0xffffffff:Nat)=2^32-1 from rfl,Nat.testBit_two_pow_sub_one,
   decide_eq_false hr,Bool.and_false,Bool.xor_false,testBit_shiftLeft',decide_eq_true (by omega:32<=r),
   Bool.true_and,testBit_shiftRight',show 32+(r-32)=r by omega]
theorem mkDet_eq{β:Type}(w:Nat)(k:Nat->β):mkDet w k=k (detVal w):=by
 unfold mkDet;rw[forceN_eq,detS_eq,unS_lor_shl (by decide)]
theorem anyEq_map_detVal(m:Nat)(pm:List Nat):anyEq (detVal m) (pm.map detVal)=anyEq m pm:=by
 induction pm with
 | nil=>rfl
 | cons v vs ih=>
  change or (Nat.beq (detVal m) (detVal v)) (anyEq (detVal m) (vs.map detVal))=or (Nat.beq m v) (anyEq m vs)
  rw[ih];by_cases h:m=v
  ·subst h;simp
  ·rw[beq_false_of_ne h,beq_false_of_ne (λe=>h (detVal_inj e))]
noncomputable def navailNonConstD(dD:Nat)(pmD:List Nat)(mD:Nat):Bool:=
 cond (anyEq mD pmD) true
  (forceN (Nat.xor (Nat.xor dD mD) 0x5bd1e995) λraw2=>
   detS raw2 λdmD=>anyEq dmD pmD)
theorem navailNonConstD_eq(d m:Nat)(pm:List Nat):
  navailNonConstD (detVal d) (pm.map detVal) (detVal m)=or (anyEq m pm) (anyEq (Nat.xor d m) pm):=by
 unfold navailNonConstD;rw[anyEq_map_detVal,forceN_eq,detS_eq,unS_xor_tag (by decide),unS_xor,
  unS_detVal,unS_detVal,anyEq_map_detVal]
 cases anyEq m pm<;>rfl
theorem nconstRawD_eq(d x:Nat):or (isZeroS x) (eqS (detVal d) x)=nconst d (unS x):=by
 rw[isZeroS_eq,eqS_eq,unS_detVal];unfold nconst;by_cases h:d=unS x
 ·rw[h,Nat.beq_refl]
 ·rw[beq_false_of_ne h,beq_false_of_ne (Ne.symm h)]
noncomputable def twoPatS(m wx wy tag:Nat):Bool:=
 forceN (Nat.xor (Nat.land m wx) tag) λm1=>
 cond (and (not (isZeroS m1)) (not (eqS m1 m))) true
  (forceN (Nat.xor (Nat.land m wy) (Nat.xor tag 1)) λm2=>
   and (not (isZeroS m2)) (not (eqS m2 m)))
theorem twoPatS_eq{m wx wy tag:Nat}(ht:tag<2^32):
  twoPatS m wx wy tag=twoPatRaw (unS m) (unS wx) (unS wy):=by
 unfold twoPatS twoPatRaw
 have ht1:Nat.xor tag 1<2^32:=xor_lt32 ht (by decide)
 simp only[forceN_eq,isZeroS_eq,eqS_eq,unS_xor_tag ht,unS_xor_tag ht1,unS_land]
noncomputable def flipUS(loSB hiSB:B16 Nat)(u w tag:Nat):Nat:=
 let sh:=Nat.shiftLeft 1 u
 Nat.xor (Nat.lor (Nat.shiftLeft (Nat.land w (b16Get loSB u)) sh)
  (Nat.shiftRight (Nat.land w (b16Get hiSB u)) sh)) tag
theorem flipUS_unS {loSB hiSB:B16 Nat} {nv u w tag:Nat}
  (hlo:b16Get loSB u=Nat.shiftLeft (loC nv u) 32)
  (hhi:b16Get hiSB u=Nat.shiftLeft (hiC nv u) 32)
  (ht:tag<2^32) :
  unS (flipUS loSB hiSB u w tag)=flipURaw nv u (unS w):=by
 unfold flipUS flipURaw;rw[hlo,hhi,unS_xor_tag ht]
 apply Nat.eq_of_testBit_eq;intro r;set sh:=Nat.shiftLeft 1 u
 simp[unS,testBit_shiftRight',testBit_lor',testBit_shiftLeft',testBit_land',
  show sh+(32+r)=32+(sh+r) by omega,decide_eq_true (by omega:32<=32+(sh+r)),
  Bool.true_and,show 32+(sh+r)-32=sh+r by omega]
 by_cases h:sh<=r
 ·simp[decide_eq_true h,decide_eq_true (by omega:sh<=32+r),show 32+r-sh=32+(r-sh) by omega,
   decide_eq_true (by omega:32<=32+(r-sh)),Bool.true_and,show 32+(r-sh)-32=r-sh by omega]
 ·simp[decide_eq_false h,decide_eq_false (by omega:¬(32<=32+r-sh)),Bool.false_and,Bool.and_false]
def findPair(key:Nat):List (Nat×Nat)->Nat
 | []=>0
 | (k,v)::rest=>cond (Nat.beq k key) v (findPair key rest)
def findDead(u:Nat):List (Nat×List (Nat×Nat))->List (Nat×Nat)
 | []=>[]
 | (k,v)::rest=>cond (Nat.beq k u) v (findDead u rest)
def findInpLive(u:Nat):List (Nat×Nat)->Nat
 | []=>99
 | (lIdx,uBit)::rest=>cond (Nat.beq uBit u) lIdx (findInpLive u rest)
noncomputable def verifyReqWits (nv liveM n:Nat) (inps:List (Nat×Nat)) (caList ws:List Nat)
  (deadUs:List (Nat×List (Nat×Nat))):List (Nat×Nat×Nat×Nat)->List (Nat×Nat×Nat)
 | []=>[]
 | (u,v,w,t)::rest=>
  cond (and (Nat.ble (Nat.add u 1) nv)
     (and (Nat.ble (Nat.add v 1) n)
     (and (Nat.ble (Nat.add w 1) n)
     (and (Nat.ble (Nat.add t 1) n) (not (Nat.beq v w))))))
   (let cut:=
     cond (Nat.beq (Nat.land (Nat.shiftRight liveM u) 1) 1)
       (cond (Nat.beq t (findInpLive u inps)) (listGetN caList t) 0)
       (findPair t (findDead u deadUs))
    forceN (Nat.land cut (listGetN caList v)) λm1=>
    cond (Nat.beq m1 0) (verifyReqWits nv liveM n inps caList ws deadUs rest)
     (forceN (flipURaw nv u (listGetN caList w)) λfcw=>
      forceN (Nat.land m1 fcw) λm=>
      cond (Nat.beq m 0) (verifyReqWits nv liveM n inps caList ws deadUs rest)
        (forceN (flipURaw nv u (listGetN ws w)) λfw=>
         cond (twoPatRaw m (listGetN ws v) fw)
          ((v,w,t)::verifyReqWits nv liveM n inps caList ws deadUs rest)
          (verifyReqWits nv liveM n inps caList ws deadUs rest))))
   (verifyReqWits nv liveM n inps caList ws deadUs rest)
def getCadj(cadj v:Nat):Nat:=Nat.land (Nat.shiftRight cadj (Nat.mul v 16)) 0xffff
def bitTest(m i:Nat):Bool:=not (Nat.beq (Nat.land (Nat.shiftRight m i) 1) 0)
theorem bitTest_eq(m i:Nat):bitTest m i=m.testBit i:=by
 unfold bitTest;rw[<-bit_land1_eq m i]
 have hlt:Nat.land (Nat.shiftRight m i) 1<2:=by change (m>>>i)&&&1<2;rw[Nat.and_one_is_mod];omega
 rcases(show Nat.land (Nat.shiftRight m i) 1=0\/Nat.land (Nat.shiftRight m i) 1=1 by omega)with h|h<;>rw[h]<;>rfl
theorem getCadj_testBit{cadj a b:Nat}(hb:b<16):
  (getCadj cadj a).testBit b=cadj.testBit (a*16+b):=by
 unfold getCadj;rw[testBit_land',testBit_shiftRight',show(0xffff:Nat)=2^16-1 from rfl,
  Nat.testBit_two_pow_sub_one,decide_eq_true hb,Bool.and_true];rfl
theorem bitTest_getCadj{cadj a b:Nat}(hb:b<16):
  bitTest (getCadj cadj a) b=cadj.testBit (a*16+b):=by
 rw[bitTest_eq,getCadj_testBit hb]
def EfSpec(nv goal:Nat)(efFn:Nat->Nat):Prop:=
 ∀u < nv,ValidWord nv (efFn u) /\
  ∀r:RowNv nv,(efFn u).testBit r.1=(goal.testBit r.1 !=goal.testBit (r.1^^^(1<<<u)))
theorem efSpec_of_eq {nv goal:Nat} {efFn:Nat->Nat} (hnv:nv<=12) (hg:ValidWord nv goal)
  (heq:∀u < nv,efFn u=Nat.xor goal (flipURaw nv u goal)):EfSpec nv goal efFn:=λu hu=>by
 rw[heq u hu];obtain⟨hfv,hfb⟩:=flipURaw_spec (w:=goal) hnv hu
 exact⟨valid_xor hg hfv,λr=>by rw[testBit_xor',hfb r]⟩
def IsCritIdxU(nv goal:Nat)(ws:List Nat)(u idx m:Nat):Prop:=
 idx<ws.length/\ValidWord nv m /\
 ∀r:RowNv nv,m.testBit r.1=true ->
  goal.testBit r.1≠goal.testBit (r.1^^^(1<<<u)) /\
  (listGetN ws idx).testBit r.1≠(listGetN ws idx).testBit (r.1^^^(1<<<u)) /\
  ∀j < ws.length,j≠idx ->
   (listGetN ws j).testBit r.1=(listGetN ws j).testBit (r.1^^^(1<<<u))
def IsCritIdxAll(nv goal:Nat)(ws:List Nat)(idx m:Nat):Prop:=
 idx<ws.length/\ValidWord nv m /\
 ∀r:RowNv nv,m.testBit r.1=true ->
  ∃u < nv,
   goal.testBit r.1≠goal.testBit (r.1^^^(1<<<u)) /\
   (listGetN ws idx).testBit r.1≠(listGetN ws idx).testBit (r.1^^^(1<<<u)) /\
   ∀j < ws.length,j≠idx ->
    (listGetN ws j).testBit r.1=(listGetN ws j).testBit (r.1^^^(1<<<u))
private lemma isCritIdxU_zero {nv goal ws u idx} (hi:idx<ws.length):IsCritIdxU nv goal ws u idx 0:=
 ⟨hi,Nat.two_pow_pos _,λ_ h=>by simp at h⟩
private lemma isCritIdxU_to_all {nv goal ws u idx m} (hu:u<nv) (h:IsCritIdxU nv goal ws u idx m) :
 IsCritIdxAll nv goal ws idx m:=⟨h.1,h.2.1,λr hr=>⟨u,hu,h.2.2 r hr⟩⟩
private lemma crit_row_to_onlyDiff {nv goal ws u idx} (hu:u<nv) (hi:idx<ws.length) {r:RowNv nv}
  (hg:goal.testBit r.1≠goal.testBit (r.1^^^(1<<<u)))
  (hs:(listGetN ws idx).testBit r.1≠(listGetN ws idx).testBit (r.1^^^(1<<<u)))
  (ho:∀j < ws.length,j≠idx->(listGetN ws j).testBit r.1=(listGetN ws j).testBit (r.1^^^(1<<<u))) :
  onlyDiffNv nv ws.toFinset goal (listGetN ws idx) r ⟨r.1^^^(1<<<u),xor_two_pow_lt hu r.2⟩ /\
  ∀j < ws.length,j≠idx->listGetN ws j≠listGetN ws idx:=by
 have n j (hj:j<ws.length) (h:j≠idx) (e:listGetN ws j=listGetN ws idx):=hs (e▸ho j hj h)
 refine⟨⟨List.mem_toFinset.mpr (listGetN_mem hi),hg,λw hw=> ?_⟩,n⟩
 obtain⟨j,hj,rfl⟩:=List.getElem_of_mem (List.mem_toFinset.mp hw);rw[<-listGetN_getElem hj]
 by_cases e:j=idx;· subst e;simp[hs]
 ·simp[ho j hj e];exact n j hj e
private lemma isCritIdxAll_to_onlyDiff {nv goal ws idx m}
  (h:IsCritIdxAll nv goal ws idx m) {r:RowNv nv} (hr:m.testBit r.1=true) :
  (∃s:RowNv nv,onlyDiffNv nv ws.toFinset goal (listGetN ws idx) r s) /\
  ∀j < ws.length,j≠idx->listGetN ws j≠listGetN ws idx:=
 let⟨_,hu,g,s,o⟩:=h.2.2 r hr;let⟨d,n⟩:=crit_row_to_onlyDiff hu h.1 g s o;⟨⟨_,d⟩,n⟩
private lemma splitLiveGo_append (nv liveM bi li:Nat) (a b:List Nat) :
  let r1:=splitLiveGo nv liveM bi li a
  let r2:=splitLiveGo nv liveM (bi+a.length) (li+r1.2.2.length) b
  splitLiveGo nv liveM bi li (a++b)=(r1.1++r2.1,r1.2.1++r2.2.1,r1.2.2++r2.2.2):=by
 induction a generalizing bi li with
 | nil=>simp[splitLiveGo]
 | cons x xs ih=>
  simp[List.cons_append,splitLiveGo,List.length_cons]
  cases t:liveM.testBit bi
  ·simpa[show bi+1+xs.length=bi+(xs.length+1) by omega]using ih (bi+1) li
  ·simp[ite_true];have h:=ih (bi+1) (li+1);rw[show bi+1+xs.length=bi+(xs.length+1) by omega]at h
   have hl k:li+1+k=li+(k+1):=by omega
   split_ifs<;>simp[List.length_cons,h,List.cons_append,hl]
theorem splitLiveGo_bank_spec{nv liveM:Nat}{gates:List (Nat×Nat×Nat)}:
  let bank:=decodeBank gates ((List.range nv).map (hiC nv))
  let r:=splitLiveGo nv liveM 0 0 bank
  r.2.2.length=r.1.length+r.2.1.length /\
  r.1.map Prod.snd=(List.range nv).filter (λu=>liveM.testBit u) /\
  (∀k < r.1.length,∃u < nv,r.1[k]?=some (k,u)/\liveM.testBit u=true /\
   listGetN r.2.2 k=hiC nv u) /\
  (∀j < r.2.1.length,r.2.1[j]?=some (r.1.length+j,listGetN r.2.2 (r.1.length+j))):=by
 have hi:∀m≤nv,let r:=splitLiveGo nv liveM 0 0 ((List.range m).map (hiC nv))
   r.2.1=[]/\r.1.length=r.2.2.length/\r.1.map Prod.snd=(List.range m).filter (λu=>liveM.testBit u) /\
   ∀k < r.1.length,∃u < m,r.1[k]?=some (k,u)/\liveM.testBit u=true/\listGetN r.2.2 k=hiC nv u:=by
  intro m;induction m with
  | zero=>exact λ_=>by simp[splitLiveGo]
  | succ m ih=>
   intro hm;obtain⟨g,l,f,q⟩:=ih (by omega);dsimp only at g l f q ⊢
   rw[List.range_succ,List.map_append,List.map_singleton,splitLiveGo_append]
   set r:=splitLiveGo nv liveM 0 0 ((List.range m).map (hiC nv))
   simp only[List.length_map,List.length_range,Nat.zero_add,List.filter_append,List.filter_cons,List.filter_nil,splitLiveGo]
   cases t:liveM.testBit m
   ·exact⟨by simp[g],by simp[l],by simp[f],λk hk=>let⟨u,a,b,c,d⟩:=q k (by simpa[t]using hk);⟨u,by omega,by simpa[t]using b,c,by simpa[t]using d⟩⟩
   ·simp only[ite_true,hm,g,List.append_nil,List.length_append,List.length_singleton,List.map_append,List.map_singleton,f]
    refine⟨trivial,by omega,trivial,λk hk=> ?_⟩
    by_cases c:k<r.1.length
    ·obtain⟨u,a,b,c',d⟩:=q k c;exact⟨u,by omega,by rwa[List.getElem?_append_left c],c',by rwa[listGetN_append_left (by omega)]⟩
    ·have e:k=r.1.length:=by omega
     subst e;exact⟨m,by omega,by rw[List.getElem?_append_right (Nat.le_refl _),Nat.sub_self];simp[l],t,by rw[listGetN_append_right (by omega),show _-_=0 by omega];rfl⟩
 have hg:∀b i,nv<=b->∀l,let r:=splitLiveGo nv liveM b i l
   r.1=[]/\r.2.1.length=r.2.2.length/\∀j < r.2.1.length,r.2.1[j]?=some (i+j,listGetN r.2.2 j):=by
  intro b i hb l;induction l generalizing b i with
  | nil=>simp[splitLiveGo]
  | cons x xs ih=>
   simp only[splitLiveGo];cases t:liveM.testBit b
   ·simpa[t]using ih (b+1) i (by omega)
   ·simp only[ite_true,show ¬(b+1<=nv) by omega,ite_false]
    obtain⟨a,l',q⟩:=ih (b+1) (i+1) (by omega)
    refine⟨a,by simp[l'],λj hj=> ?_⟩
    cases j with| zero=>simp[listGetN]| succ k=>simpa[listGetN,Nat.add_assoc,Nat.add_comm 1]using q k (by simpa using hj)
 obtain⟨e,he,_⟩:=decodeBank_prefix gates ((List.range nv).map (hiC nv))
 dsimp;rw[he,splitLiveGo_append];simp[List.length_map,List.length_range,Nat.zero_add]
 obtain⟨g1,l1,f1,q1⟩:=hi nv (Nat.le_refl nv);set r:=splitLiveGo nv liveM 0 0 ((List.range nv).map (hiC nv))
 obtain⟨i2,l2,q2⟩:=hg nv r.2.2.length (Nat.le_refl nv) e;rw[g1,i2];simp[List.append_nil,List.nil_append,List.length_append]
 refine⟨by
  omega,f1,λk hk=>let⟨u,a,b,c,d⟩:=q1 k hk;⟨u,a,b,c,by rwa[listGetN_append_left (by omega)]⟩,
  λj hj=>by rw[listGetN_append_right (by omega),show r.1.length+j-r.2.2.length=j by omega,l1];exact q2 j hj⟩
private lemma orGateDiffsRaw_spec {β:Type} {nv u ef:Nat} (hnv:nv<=12) (hu:u<nv)
  (hef:ValidWord nv ef) (gts:List (Nat×Nat)) (any2:Nat) (ha2:ValidWord nv any2) (c:Nat->β) :
  ∃res,orGateDiffsRaw nv u ef gts any2 c=c res/\ValidWord nv res /\
   ∀r:RowNv nv,res.testBit r.1 =
    (any2.testBit r.1||(ef.testBit r.1&&gts.any (λp=>p.2.testBit r.1 !=p.2.testBit (r.1^^^(1<<<u))))):=by
 induction gts generalizing any2 c with
 | nil=>exact⟨any2,rfl,ha2,λ_=>by simp⟩
 | cons p rest ih=>
  simp[orGateDiffsRaw,forceN_eq];obtain⟨_,hflb⟩:=flipURaw_spec (w:=p.2) hnv hu
  obtain⟨res,h1,h2,h3⟩:=ih _ (valid_lor ha2 (valid_land_r hef)) c
  exact⟨res,h1,h2,λr=>by rw[h3 r];simp[testBit_lor',testBit_land',testBit_xor',hflb r,List.any_cons];grind⟩
private lemma two_le_countP {α:Type} {l:List α} {P:α->Bool} {i j:Nat}
  (hi:i<l.length) (hj:j<l.length) (hne:i≠j) (h1:P l[i]=true) (h2:P l[j]=true) :
  2<=l.countP P:=by
 induction l generalizing i j with
 | nil=>simp at hi
 | cons x xs ih=>
  have pos {k} (hk:k<xs.length) (hp:P xs[k]=true):=List.countP_pos_iff.mpr ⟨_,List.getElem_mem hk,hp⟩
  cases i<;>cases j
  ·omega
  ·simp only[List.getElem_cons_zero,List.getElem_cons_succ]at h1 h2;have:=pos (by simpa using hj) h2;simp only[List.countP_cons,h1,ite_true];omega
  ·simp only[List.getElem_cons_zero,List.getElem_cons_succ]at h1 h2;have:=pos (by simpa using hi) h1;simp only[List.countP_cons,h2,ite_true];omega
  ·have:=ih (by simpa using hi) (by simpa using hj) (by omega) h1 h2;simp[List.countP_cons];omega
private lemma gateDiffsRaw_spec {β:Type} {nv u ef:Nat} (hnv:nv<=12) (hu:u<nv)
  (hef:ValidWord nv ef) (gts:List (Nat×Nat)) (any1 any2:Nat) (ds:List (Nat×Nat))
  (ha1:ValidWord nv any1) (c:Bool->Nat->List (Nat×Nat)->β) :
  let D (r:Nat) (p:Nat×Nat):=p.2.testBit r !=p.2.testBit (r^^^(1<<<u))
  ∃res1 res2 resDs,
   gateDiffsRaw nv u ef gts any1 any2 ds c=c (Nat.beq res1 ef) res2 resDs/\ValidWord nv res1 /\
   resDs=(gts.map (λp=>(p.1,Nat.land (Nat.xor p.2 (flipURaw nv u p.2)) ef))).reverse++ds /\
   (∀r:RowNv nv,res1.testBit r.1=(any1.testBit r.1||(ef.testBit r.1&&gts.any (D r.1)))) /\
   (∀r:RowNv nv,any2.testBit r.1=true\/(ef.testBit r.1=true/\2<=(if any1.testBit r.1 then 1 else 0)+gts.countP (D r.1))->res2.testBit r.1=true):=by
 dsimp;induction gts generalizing any1 any2 ds c with
 | nil=>exact⟨any1,any2,ds,rfl,ha1,by simp,λ_=>by simp,λ_ h=>h.elim id λ⟨_,h⟩=>by split_ifs at h<;>simp at h⟩
 | cons p rest ih=>
  simp only[gateDiffsRaw,forceN_eq];obtain⟨_,hflb⟩:=flipURaw_spec (w:=p.2) hnv hu
  let d:=Nat.land (Nat.xor p.2 (flipURaw nv u p.2)) ef
  obtain⟨r1,r2,rD,hc,hv,hd,h1,h2⟩:=ih (Nat.lor any1 d) (Nat.lor any2 (Nat.land any1 d)) ((p.1,d)::ds) (valid_lor ha1 (valid_land_r hef)) c
  refine⟨r1,r2,rD,hc,hv,by simp[hd,d,List.reverse_cons,List.append_assoc],
   λr=>by rw[h1 r];simp[d,testBit_lor',testBit_land',testBit_xor',hflb r,List.any_cons];grind,λr hr=>h2 r ?_⟩
  simp only[d,testBit_lor',testBit_land',testBit_xor',hflb r,List.countP_cons]at hr ⊢
  rcases hr with h2'|⟨hef1,hcnt⟩;· exact Or.inl (by simp[h2'])
  ·generalize rest.countP (λp=>p.2.testBit r.1 !=p.2.testBit (r.1^^^(1<<<u)))=rc at hcnt ⊢
   cases hb1:any1.testBit r.1<;>cases hbp:p.2.testBit r.1<;>cases hbq:p.2.testBit (r.1^^^(1<<<u))<;>simp[hb1,hef1,hbp,hbq]at hcnt ⊢<;>(right;omega)
@[local simp] private lemma mkGateCRaw_spec {β:Type} (uniq:Nat) (ds accP:List (Nat×Nat)) (accV:List Nat)
  (c:List (Nat×Nat)->List Nat->β) :
  mkGateCRaw uniq ds accP accV c=c ((ds.map (λp=>(p.1,Nat.land p.2 uniq))).reverse++accP) ((ds.map (λp=>Nat.land p.2 uniq)).reverse++accV):=by
 induction ds generalizing accP accV c with| nil=>simp[mkGateCRaw]| cons p rest ih=>simp[mkGateCRaw,ih,List.append_assoc]
@[local simp] private lemma zipOrRaw_spec {β:Type} (a b:List Nat) (c:List Nat->β) :
  zipOrRaw a b c=c (List.zipWith Nat.lor a b):=by
 induction a generalizing b c with| nil=>simp[zipOrRaw]| cons x xs ih=>cases b<;>simp[zipOrRaw,ih]
@[local simp] private lemma appRaw_spec {β:Type} (a b:List Nat) (c:List Nat->β) :
  appRaw a b c=c (a++b):=by
 induction a generalizing c with| nil=>simp[appRaw]| cons x xs ih=>simp[appRaw,ih]
private lemma findPair_mem {key:Nat} {l:List (Nat×Nat)}:findPair key l=0\/(key,findPair key l)∈l:=by
 induction l with| nil=>exact Or.inl rfl| cons p rest ih=>simp only[findPair];by_cases hk:p.1=key;subst hk;simp;simp only[beq_false_of_ne hk,Bool.cond_false];exact ih.imp id (List.mem_cons_of_mem _)
private lemma findDead_mem {u:Nat} {deadUs:List (Nat×List (Nat×Nat))}:findDead u deadUs=[]\/(u,findDead u deadUs)∈deadUs:=by
 induction deadUs with| nil=>exact Or.inl rfl| cons p rest ih=>simp only[findDead];by_cases hk:p.1=u;subst hk;simp;simp only[beq_false_of_ne hk,Bool.cond_false];exact ih.imp id (List.mem_cons_of_mem _)
private lemma findInpLive_mem {u idx:Nat} {inps:List (Nat×Nat)}
  (hnd:(inps.map Prod.snd).Nodup) (hm:(idx,u)∈inps):findInpLive u inps=idx:=by
 induction inps with
 | nil=>simp at hm
 | cons p rest ih=>
  simp only[List.map_cons,List.nodup_cons,List.mem_cons]at hnd hm;simp only[findInpLive]
  rcases hm with rfl|htl;· simp
  ·rw[beq_false_of_ne λe=>hnd.1 (List.mem_map.mpr ⟨_,htl,e.symm⟩),Bool.cond_false];exact ih hnd.2 htl
theorem buildCoordsRaw_sound {β:Type} {nv liveM goal:Nat} {efFn:Nat->Nat}
  {gates:List (Nat×Nat×Nat)} (hnv:nv<=12) (hef:EfSpec nv goal efFn)
  (k:Bool->List Nat->List (Nat×List (Nat×Nat))->β) :
  let bank:=decodeBank gates ((List.range nv).map (hiC nv))
  let r:=splitLiveGo nv liveM 0 0 bank
  let inps:=r.1;let gts:=r.2.1;let ws:=r.2.2
  ∃ok caList deadUs,
   buildCoordsRaw nv liveM efFn gts k=k ok caList deadUs /\
   (ok=false->∀cap,ImpossibleNv nv goal cap ws.toFinset) /\
   (ok=true ->
    caList.length=ws.length /\
    (∀idx < ws.length,IsCritIdxAll nv goal ws idx (listGetN caList idx)) /\
    (∀u < nv,liveM.testBit u=true ->
     let t:=findInpLive u inps
     t<ws.length/\IsCritIdxU nv goal ws u t (listGetN caList t)) /\
    (∀u cus,(u,cus)∈deadUs ->
     u<nv/\∀gIdx cu,(gIdx,cu)∈cus->IsCritIdxU nv goal ws u gIdx cu)):=by
 obtain⟨hl,hf,hi,hg⟩:=@splitLiveGo_bank_spec nv liveM gates
 dsimp only at hl hf hi hg ⊢
 set r:=splitLiveGo nv liveM 0 0 (decodeBank gates ((List.range nv).map (hiC nv)))
 set s:=r.1;set g:=r.2.1;set w:=r.2.2;let F m:=(List.range m).filter (λu=>liveM.testBit u)
 let D u x (p:Nat×Nat):=p.2.testBit x !=p.2.testBit (x^^^(1<<<u))
 let U:=IsCritIdxU nv goal w;let A:=IsCritIdxAll nv goal w
 let G (l:List Nat):=l.length=g.length/\∀j < g.length,A (s.length+j) (listGetN l j)
 let O (d:List (Nat×List (Nat×Nat))):=∀u q,(u,q)∈d->u<nv/\∀i c,(i,c)∈q->U u i c
 let I m (l:List Nat):=l.length=(F nv).length-(F m).length /\
  ∀t,(F m).length<=t->t<s.length->∃u < nv,s[t]?=some (t,u)/\U u t (listGetN l (t-(F m).length))
 have sl:s.length=(F nv).length:=by simpa[F]using congrArg List.length hf
 have fi {i u} m:=@findInpLive_mem u i _ (by rw[hf];exact List.Nodup.filter _ List.nodup_range) m
 have ge j (h:j<g.length):=Option.some.inj (by simpa[List.getElem?_eq_getElem h]using hg j h)
 have hh {a b} (p:a<nv) (q:b<nv) (x:RowNv nv) :
   ((hiC nv a).testBit x.1≠(hiC nv a).testBit (x.1^^^(1<<<b)))↔a=b:=by
  rw[hiC_bits_row hnv p x,hiC_bits_row hnv p ⟨_,xor_two_pow_lt q x.2⟩]
  simp[Nat.shiftLeft_eq,Nat.testBit_xor,Nat.testBit_two_pow];by_cases h:a=b<;>simp[h,Ne.symm]
 have dn {u j} (p:u<nv) (l:liveM.testBit u=false) (q:j<s.length) (x:RowNv nv) :
   (listGetN w j).testBit x.1=(listGetN w j).testBit (x.1^^^(1<<<u)):=by
  obtain⟨_,b,_,t,e⟩:=hi j q;rw[e];exact by_contra λd=>by have:=(hh b p x).mp d;subst this;simp[l]at t
 have ng {u x j} (o:g.any (D u x)=false) (q:j<w.length) (e:¬(j<s.length)):=
  by_contra λd=>Bool.noConfusion (o.symm.trans (List.any_eq_true.mpr
   ⟨_,List.mem_of_getElem? (by simpa[show s.length+(j-s.length)=j by omega]using hg (j-s.length) (by omega)),bne_iff_ne.mpr d⟩))
 have lp:∀m≤nv,∀i a d (c:Bool->List Nat->List Nat->List (Nat×List (Nat×Nat))->β),
   G a->O d->I m i ->
   ∃b x y z,buildCoordsRaw.loopU nv liveM efFn g m i a d c=c b x y z /\
    (b=false->∀n,ImpossibleNv nv goal n w.toFinset)/\(b=true->I 0 x/\G y/\O z):=λm=>by
  induction m with
  | zero=>exact λ_ _ _ _ _ a d i=>⟨true,_,_,_,rfl,λh=>Bool.noConfusion h,λ_=>⟨i,a,d⟩⟩
  | succ u ih=>
   intro hm i a d c ga od ic;have hu:u<nv:=(by omega);obtain⟨ev,eb⟩:=hef u hu
   simp only[buildCoordsRaw.loopU,bit_land1_eq];cases lv:liveM.testBit u
   ·simp only[Bool.cond_false]
    obtain⟨x1,x2,xD,gd,v1,ds,b1,b2⟩:=gateDiffsRaw_spec hnv hu ev g 0 0 [] (Nat.two_pow_pos _) _
    rw[gd];cases ok:Nat.beq x1 (efFn u)
    ·refine⟨false,[],[],[],rfl,λ_ _ _ _ ls=> ?_,λh=>by cases h⟩
     obtain⟨x,hx⟩:∃x,x1.testBit x≠(efFn u).testBit x:=by_contra λa=>by have:=Nat.eq_of_testBit_eq λr=>by_contra λh=>a ⟨r,h⟩;simp[this]at ok
     have lt:x<2^nv:=by_contra λh=>hx ((testBit_eq_false_of_lt_pow v1 (Nat.le_of_not_lt h)).trans (testBit_eq_false_of_lt_pow ev (Nat.le_of_not_lt h)).symm)
     let y:RowNv nv:=⟨x,lt⟩
     have g0:(efFn u).testBit x=true/\g.any (D u x)=false:=by have hb:x1.testBit x=((efFn u).testBit x&&g.any (D u x)):=(by simpa using b1 y);revert hx hb;cases(efFn u).testBit x<;>cases g.any (D u x)<;>simp
     obtain⟨v,hv,vd⟩:=liveNv_row_difference ls (r:=y) (s:=⟨_,xor_two_pow_lt hu lt⟩) (bne_iff_ne.mp (by rw[<-eb y,g0.1]))
     obtain⟨j,hj,rfl⟩:=List.getElem_of_mem (List.mem_toFinset.mp hv);rw[<-listGetN_getElem hj]at vd
     exact if e:j<s.length then vd (dn hu lv e y)else vd (ng g0.2 hj e)
    ·simp only[Bool.cond_true,forceN_eq,mkGateCRaw_spec,zipOrRaw_spec,List.append_nil]
     let q:=Nat.xor (efFn u) x2;let f x:=Nat.land (Nat.land (Nat.xor x (flipURaw nv u x)) (efFn u)) q
     have lu:(F (u+1)).length=(F u).length:=by simp[F,List.range_succ,lv]
     have rv {α} (h:Nat×Nat->α):(xD.map h).reverse=g.map (λp=>h (p.1,Nat.land (Nat.xor p.2 (flipURaw nv u p.2)) (efFn u))):=by simp[ds,List.map_map,Function.comp_def]
     have hc j (hj:j<g.length):U u (s.length+j) (f (g[j]'hj).2):=by
      have g2:=congrArg Prod.snd (ge j hj);dsimp at g2;obtain⟨_,fl⟩:=flipURaw_spec (w:=(g[j]'hj).2) hnv hu
      refine⟨by omega,valid_land_l (valid_land_r ev),λx hx=> ?_⟩
      simp only[f,testBit_land',testBit_xor',fl x,Bool.and_eq_true,q]at hx;rcases hx with ⟨⟨df,e1⟩,uq⟩
      have f2:x2.testBit x.1=false:=by revert uq;cases x2.testBit x.1<;>simp[e1]
      refine⟨bne_iff_ne.mp (eb x▸e1),g2▸bne_iff_ne.mp df,λj' hj' ne=> ?_⟩
      by_cases e:j'<s.length;· exact dn hu lv e x
      have gl:j'-s.length<g.length:=by omega
      have g2':=congrArg Prod.snd (ge _ gl);simp only[show s.length+(j'-s.length)=j' by omega]at g2'
      exact by_contra λd'=>Bool.noConfusion ((b2 x (Or.inr ⟨e1,by have c2:=@two_le_countP _ _ (D u x.1) _ _ hj gl (by omega) df (bne_iff_ne.mpr (g2'.symm▸d'));dsimp[D]at c2;simp[c2]⟩)).symm.trans f2)
     refine ih (by omega) i _ ((u,_)::d) c
      ⟨by rw[List.length_zipWith,rv,List.length_map,ga.1,Nat.min_self],λj hj=> ?_⟩ (λv z m=> ?_)
      ⟨by omega,λt h1 h2=>by simpa[lu]using ic.2 t (by omega) h2⟩
     ·rw[rv,listGetN_getElem (by simp[ga.1,hj]),List.getElem_zipWith,List.getElem_map,<-listGetN_getElem (by omega:j<a.length)]
      have ha:=ga.2 j hj;have hb:=isCritIdxU_to_all hu (hc j hj)
      exact⟨ha.1,valid_lor ha.2.1 hb.2.1,λx hx=>by rw[testBit_lor',Bool.or_eq_true]at hx;exact hx.elim (ha.2.2 x) (hb.2.2 x)⟩
     ·exact(List.mem_cons.mp m).elim (λe=>by
       rcases Prod.mk.inj e with ⟨rfl,rfl⟩;refine⟨hu,λj' c' m'=> ?_⟩
       rw[rv]at m';obtain⟨p,mp,ep⟩:=List.mem_map.mp m';obtain⟨j,hj,rfl⟩:=List.getElem_of_mem mp;rcases Prod.mk.inj ep with ⟨rfl,rfl⟩
       rw[congrArg Prod.fst (ge j hj)];exact hc j hj) (od v z)
   ·have sf:F nv=F u++u::((List.range (nv-(u+1))).map (u+1+·)).filter (λx=>liveM.testBit x):=by
     dsimp[F];rw[show nv=u+1+(nv-(u+1)) by omega,List.range_add,List.filter_append,List.range_succ,List.filter_append,List.filter_cons,List.filter_nil,lv];simp
    have:(F u).length<(F nv).length:=by have:=congrArg List.length sf;simp at this;omega
    simp only[Bool.cond_true];obtain⟨a2,o,v2,b2⟩:=orGateDiffsRaw_spec hnv hu ev g 0 (Nat.two_pow_pos _) _
    rw[o,forceN_eq];set p:=(F u).length
    have lu:(F (u+1)).length=p+1:=by simp[F,List.range_succ,lv,p]
    have⟨hp,wp⟩:s[p]?=some (p,u)/\listGetN w p=hiC nv u:=by
     obtain⟨v,_,h0,_,hw⟩:=hi p (by omega);have h1:(F nv)[p]?=some u:=by rw[sf];simp[p]
     dsimp only[F]at h1;rw[<-hf,List.getElem?_map,h0]at h1;simp at h1;subst h1;exact⟨h0,hw⟩
    have cu:U u p (Nat.xor (efFn u) a2):=⟨by
     omega,valid_xor ev v2,λx hx=>by
     rw[testBit_xor',b2 x,Nat.zero_testBit,Bool.false_or]at hx
     have g0:(efFn u).testBit x.1=true/\g.any (D u x.1)=false:=by revert hx;cases(efFn u).testBit x.1<;>cases g.any (D u x.1)<;>simp
     refine⟨bne_iff_ne.mp (eb x▸g0.1),wp.symm▸(hh hu hu x).mpr rfl,λj hj ne=> ?_⟩
     by_cases e:j<s.length;· obtain⟨_,b,h0,_,hw⟩:=hi j e;rw[hw];exact by_contra λd=>by have:=(hh b hu x).mp d;subst this;exact ne ((fi (List.mem_of_getElem? h0)).symm.trans (fi (List.mem_of_getElem? hp)))
     ·exact ng g0.2 hj e⟩
    refine ih (by omega) (_::i) a d c ga od ⟨by simp[ic.1];omega,λt h1 h2=> ?_⟩
    by_cases e:t=p;· subst e;exact⟨u,hu,hp,by simpa[p,listGetN]using cu⟩
    ·obtain⟨v,b,h0,z⟩:=ic.2 t (by omega) h2;exact⟨v,b,h0,by simpa[p,show t-p=(t-(F (u+1)).length)+1 by omega,listGetN]using z⟩
 obtain⟨b,x,y,z,cl,fl,tr⟩:=lp nv (Nat.le_refl nv) [] (List.replicate g.length 0) [] _
  ⟨List.length_replicate,λj hj=>by rw[listGetN_getElem (by simpa using hj),List.getElem_replicate];exact⟨by omega,Nat.two_pow_pos _,λ_ h=>by simp at h⟩⟩
  (λ_ _ m=>by simp at m) ⟨by simp,λ_ _ _=>by omega⟩
 unfold buildCoordsRaw;rw[cl];cases b
 ·exact⟨false,[],[],rfl,λ_=>fl rfl,λh=>by cases h⟩
 ·simp only[Bool.cond_true,appRaw_spec];obtain⟨⟨lx,cx⟩,⟨ly,cy⟩,cd⟩:=tr rfl
  have lx':x.length=s.length:=by simpa[F,sl]using lx
  refine⟨true,x++y,z,rfl,λh=>Bool.noConfusion h,λ_=>⟨by simp[lx',ly,hl],λi h=> ?_,λu hu lv=> ?_,cd⟩⟩
  ·by_cases e:i<s.length;· rw[listGetN_append_left (by omega)];obtain⟨u,b,_,c⟩:=cx i (Nat.zero_le _) e;exact isCritIdxU_to_all b (by simpa[F]using c)
   ·rw[listGetN_append_right (by omega),lx'];simpa[show s.length+(i-s.length)=i by omega]using cy (i-s.length) (by omega)
  ·obtain⟨⟨i,v⟩,m,e⟩:=List.mem_map.mp (show u∈s.map Prod.snd from hf.symm▸List.mem_filter.mpr ⟨List.mem_range.mpr hu,lv⟩)
   dsimp at e;subst e;obtain⟨j,hj,he⟩:=List.getElem_of_mem m
   obtain⟨v2,_,h1,c⟩:=cx j (Nat.zero_le _) hj;rw[List.getElem?_eq_getElem hj,he]at h1;cases h1
   rw[fi m,listGetN_append_left (by omega)];exact⟨by omega,by simpa[F]using c⟩
def GoodCadj(nv goal:Nat)(ws:List Nat)(cadj:Nat):Prop:=
 ∀a b,a<16->b<16->bitTest (getCadj cadj a) b=true ->
  a<ws.length/\b<ws.length/\a≠b /\
  ∀A f,signedOrderLawOnNv nv A ws.toFinset goal f ->
   listGetN ws a∈A->listGetN ws b∈A->f (listGetN ws a)≠f (listGetN ws b)
private noncomputable def zipICWSGo {β:Type} (caL:List Nat) (i tag:Nat) (wsL:List Nat)
  (k:List (Nat×Nat×Nat)->β):β:=
 @List.rec Nat (λ_=>Nat->Nat->List Nat->(List (Nat×Nat×Nat)->β)->β)
  (λ_ _ _ c=>c [])
  (λca _ ih i' tag' ws c=>
   match ws with
   | []=>c []
   | w::wR=>
    forceN (Nat.add i' 1) λi1=>
    forceN (Nat.land (Nat.add tag' 2654435761) 0xffffffff) λt1=>
    cond (Nat.beq ca 0) (ih i1 t1 wR c)
     (forceN (Nat.lor (Nat.shiftLeft ca 32) t1) λcas=>
      forceN (Nat.lor (Nat.shiftLeft w 32) (Nat.xor t1 0x5bd1e995)) λws'=>
      ih i1 t1 wR λrest=>c ((i',cas,ws')::rest)))
  caL i tag wsL k
noncomputable def zipICWS{β:Type}(caL wsL:List Nat)(tag0:Nat)(k:List (Nat×Nat×Nat)->β):β:=
 zipICWSGo caL 0 tag0 wsL k
noncomputable def loopBS(caS waS:Nat)(l:List (Nat×Nat×Nat))(iA:Nat)(tag0 cadj:Nat):Nat:=
 @List.rec (Nat×Nat×Nat) (λ_=>Nat->Nat->Nat)
  (λ_ c=>c)
  (λp _ ih tag c=>
   let j:=p.1
   forceN (Nat.land (Nat.add tag 1013904223) 0xffffffff) λt1=>
   forceN (Nat.xor (Nat.land caS p.2.1) t1) λm=>
   cond (isZeroS m) (ih t1 c)
    (cond (twoPatS m waS p.2.2 (Nat.xor t1 0x9e3779b9))
     (forceN (Nat.lor c (Nat.lor (Nat.shiftLeft 1 (Nat.add (Nat.mul iA 16) j))
       (Nat.shiftLeft 1 (Nat.add (Nat.mul j 16) iA)))) λc'=>
      ih t1 c')
     (ih t1 c)))
  l tag0 cadj
private noncomputable def buildCadjSGo (icw:List (Nat×Nat×Nat)) (tag0 cadj:Nat):Nat:=
 @List.rec (Nat×Nat×Nat) (λ_=>Nat->Nat->Nat)
  (λ_ c=>c)
  (λp rest ih tag c=>
   forceN (Nat.land (Nat.add tag 2246822519) 0xffffffff) λt1=>
   forceN (loopBS p.2.1 p.2.2 rest p.1 t1 c) λc'=>
   ih t1 c')
  icw tag0 cadj
noncomputable def buildCadjS(icw:List (Nat×Nat×Nat))(tag0:Nat):Nat:=
 buildCadjSGo icw tag0 0
def IcwOK(caList ws:List Nat)(icw:List (Nat×Nat×Nat)):Prop:=
 (∀p∈icw,p.1<ws.length/\unS p.2.1=listGetN caList p.1/\unS p.2.2=listGetN ws p.1) /\
 icw.Pairwise (·.1<·.1)
theorem zipICWS_spec {β:Type} {caList ws:List Nat} (hlen:caList.length=ws.length)
  (tag0:Nat) (k:List (Nat×Nat×Nat)->β) :
  ∃icw,zipICWS caList ws tag0 k=k icw/\IcwOK caList ws icw:=by
 have go:∀x i tg y (c:List (Nat×Nat×Nat)->β),x=caList.drop i->y=ws.drop i ->
   ∃l,zipICWSGo x i tg y c=c l/\(∀p∈l,i<=p.1)/\IcwOK caList ws l:=λx=>by
  induction x with
  | nil=>exact λ_ _ _ _ _ _=>⟨[],rfl,by simp,by simp,.nil⟩
  | cons _ _ ih=>
   intro i tg y c hx hy;cases y with
   | nil=>have:=congrArg List.length hx;have:=congrArg List.length hy;simp at *;omega
   | cons _ _=>
    obtain⟨h1,rfl,rfl⟩:=drop_cons_iff hx.symm;obtain⟨h2,rfl,rfl⟩:=drop_cons_iff hy.symm
    unfold zipICWSGo;dsimp only;rw[forceN_eq,forceN_eq]
    set t1:=Nat.land (Nat.add tg 2654435761) 0xffffffff;have ht1:=land_ff32_lt (Nat.add tg 2654435761)
    cases Nat.beq caList[i] 0
    ·rw[forceN_eq,forceN_eq]
     obtain⟨l,e,hge,hm,hp⟩:=ih (i+1) t1 _ _ rfl rfl
     refine⟨_::l,e,λq hq=>(List.mem_cons.mp hq).elim (·▸Nat.le_refl _) λh=>Nat.le_of_succ_le (hge q h),
      λq hq=>(List.mem_cons.mp hq).elim (λh=>h▸⟨h2,by rw[unS_lor_shl ht1,listGetN_getElem h1],by rw[unS_lor_shl (xor_lt32 ht1 (by decide)),listGetN_getElem h2]⟩) (hm q),
      List.pairwise_cons.mpr ⟨λb hb=>hge b hb,hp⟩⟩
    ·obtain⟨l,e,hge,ok⟩:=ih (i+1) t1 _ c rfl rfl
     exact⟨l,e,λq hq=>Nat.le_of_succ_le (hge q hq),ok⟩
 obtain⟨l,e,_,ok⟩:=go caList 0 tag0 ws k rfl rfl;exact⟨l,e,ok⟩
theorem buildCadjS_sound {nv goal:Nat} {caList ws:List Nat} {icw:List (Nat×Nat×Nat)} {tag0:Nat}
  (hws16:ws.length<=16)
  (hcrit:∀idx < ws.length,IsCritIdxAll nv goal ws idx (listGetN caList idx))
  (hicw:IcwOK caList ws icw) :
  GoodCadj nv goal ws (buildCadjS icw tag0):=by
 let c:=listGetN caList;let w:=listGetN ws;let G:=GoodCadj nv goal ws
 have hp i j (p:i<ws.length) (q:j<ws.length) (n:i≠j)
   (t:twoPatRaw (Nat.land (c i) (c j)) (w i) (w j)=true)
   A f (l:signedOrderLawOnNv nv A ws.toFinset goal f) (a:w i∈A) (b:w j∈A):f (w i)≠f (w j):=by
  obtain⟨r,s,m1,m2,d⟩:=twoPatRaw_sound (valid_land_l (hcrit i p).2.1) t;simp at m1 m2
  exact l.1 a b ((isCritIdxAll_to_onlyDiff (hcrit i p) m1.1).2 j q n.symm).symm
   (isCritIdxAll_to_onlyDiff (hcrit i p) m1.1).1.choose_spec (isCritIdxAll_to_onlyDiff (hcrit j q) m1.2).1.choose_spec
   (isCritIdxAll_to_onlyDiff (hcrit i p) m2.1).1.choose_spec (isCritIdxAll_to_onlyDiff (hcrit j q) m2.2).1.choose_spec d
 have lb i caS waS (hi:i<ws.length) (hca:unS caS=c i) (hwa:unS waS=w i) :
   ∀l tg z,(∀q∈l,i<q.1/\q.1<ws.length/\unS q.2.1=c q.1/\unS q.2.2=w q.1)->G z ->
   G (loopBS caS waS l i tg z):=λl=>by
  induction l with| nil=>exact λ_ _ _ g=>g| cons q _ ih=>
   intro tg z hl g;obtain⟨ilt,hq,hcq,hwq⟩:=hl q (by simp)
   have hl' r hr:=hl r (List.mem_cons_of_mem _ hr);unfold loopBS;dsimp;rw[forceN_eq,forceN_eq]
   set t1:=Nat.land (Nat.add tg 1013904223) 0xffffffff;have ht1:=land_ff32_lt (Nat.add tg 1013904223)
   cases isZeroS (Nat.xor (Nat.land caS q.2.1) t1);swap;exact ih t1 z hl' g
   cases tp:twoPatS (Nat.xor (Nat.land caS q.2.1) t1) waS q.2.2 (Nat.xor t1 0x9e3779b9);· exact ih t1 z hl' g
   rw[Bool.cond_true,forceN_eq];rw[twoPatS_eq (xor_lt32 ht1 (by decide)),unS_xor_tag ht1,unS_land,hca,hwa,hcq,hwq]at tp
   refine ih t1 _ hl' λa d ha hd e=> ?_
   rw[bitTest_getCadj hd]at e;simp[shiftLeft_one_eq]at e
   rcases e with e|e|e
   ·exact g a d ha hd (by rwa[bitTest_getCadj hd])
   ·rcases(show a=i/\d=q.1 by omega)with ⟨rfl,rfl⟩;exact⟨hi,hq,by omega,hp a q.1 hi hq (by omega) tp⟩
   ·rcases(show a=q.1/\d=i by omega)with ⟨rfl,rfl⟩;exact⟨hq,hi,by omega,λA f l u v=>(hp d q.1 hi hq (by omega) tp A f l v u).symm⟩
 have la:∀l tg z,IcwOK caList ws l->G z->G (buildCadjSGo l tg z):=λl=>by
  induction l with| nil=>exact λ_ _ _ g=>g| cons p rest ih=>
   intro tg z ⟨hm,hpw⟩ g;obtain⟨hi,hca,hwa⟩:=hm p (by simp);obtain⟨hlt,hpw'⟩:=List.pairwise_cons.mp hpw
   have hm' q hq:=hm q (List.mem_cons_of_mem _ hq);unfold buildCadjSGo;dsimp;rw[forceN_eq,forceN_eq]
   exact ih _ _ ⟨hm',hpw'⟩ (lb p.1 p.2.1 p.2.2 hi hca hwa rest _ z (λq hq=>⟨hlt q hq,hm' q hq⟩) g)
 exact la icw tag0 0 hicw λ_ _ _ hb e=>by simp[bitTest_getCadj hb]at e
def GoodReqs(nv goal:Nat)(ws:List Nat)(reqs:List (Nat×Nat×Nat)):Prop:=
 ∀r∈reqs,
  r.1<ws.length/\r.2.1<ws.length/\r.2.2<ws.length/\r.1≠r.2.1 /\
  ∀A f,signedOrderLawOnNv nv A ws.toFinset goal f ->
   listGetN ws r.1∈A->listGetN ws r.2.1∈A->listGetN ws r.2.2∈A ->
   f (listGetN ws r.1)=f (listGetN ws r.2.1)->f (listGetN ws r.2.2)<=f (listGetN ws r.1)
private lemma req_law_of_rows {nv goal u v w t cut cv cw:Nat} {ws:List Nat}
  (hu:u<nv) (hw:w<ws.length) (hvw:v≠w)
  (hcut:IsCritIdxU nv goal ws u t cut) (hcv:IsCritIdxAll nv goal ws v cv) (hcw:IsCritIdxAll nv goal ws w cw)
  {p1 p2:RowNv nv} (hc1:cut.testBit p1.1=true) (hc2:cut.testBit p2.1=true)
  (hv1:cv.testBit p1.1=true) (hv2:cv.testBit p2.1=true)
  (hw1:cw.testBit (p1.1^^^(1<<<u))=true) (hw2:cw.testBit (p2.1^^^(1<<<u))=true)
  (hdiff:(listGetN ws v).testBit p1.1≠(listGetN ws v).testBit p2.1 \/
    (listGetN ws w).testBit (p1.1^^^(1<<<u))≠(listGetN ws w).testBit (p2.1^^^(1<<<u))) :
  ∀A f,signedOrderLawOnNv nv A ws.toFinset goal f ->
   listGetN ws v∈A->listGetN ws w∈A->listGetN ws t∈A ->
   f (listGetN ws v)=f (listGetN ws w)->f (listGetN ws t)<=f (listGetN ws v):=λ_ _ l a b c e=>
 l.2 a b c ((isCritIdxAll_to_onlyDiff hcv hv1).2 w hw hvw.symm).symm
  (isCritIdxAll_to_onlyDiff hcv hv1).1.choose_spec
  (onlyDiffNv_symm (isCritIdxAll_to_onlyDiff hcw (r:=⟨_,xor_two_pow_lt hu p1.2⟩) hw1).1.choose_spec) (let⟨g,s,o⟩:=hcut.2.2 p1 hc1;(crit_row_to_onlyDiff hu hcut.1 g s o).1)
  (isCritIdxAll_to_onlyDiff hcv hv2).1.choose_spec
  (onlyDiffNv_symm (isCritIdxAll_to_onlyDiff hcw (r:=⟨_,xor_two_pow_lt hu p2.2⟩) hw2).1.choose_spec) (let⟨g,s,o⟩:=hcut.2.2 p2 hc2;(crit_row_to_onlyDiff hu hcut.1 g s o).1) hdiff e
theorem verifyReqWits_sound {nv liveM goal:Nat} {inps:List (Nat×Nat)} {caList ws:List Nat}
  {deadUs:List (Nat×List (Nat×Nat))} {wits:List (Nat×Nat×Nat×Nat)}
  (hnv:nv<=12)
  (hcritAll:∀idx < ws.length,IsCritIdxAll nv goal ws idx (listGetN caList idx))
  (hcritInp:∀u < nv,liveM.testBit u=true ->
   let t:=findInpLive u inps
   t<ws.length/\IsCritIdxU nv goal ws u t (listGetN caList t))
  (hcritDead:∀u cus,(u,cus)∈deadUs ->
   u<nv/\∀gIdx cu,(gIdx,cu)∈cus->IsCritIdxU nv goal ws u gIdx cu) :
  GoodReqs nv goal ws (verifyReqWits nv liveM ws.length inps caList ws deadUs wits):=by
 let c:=listGetN caList;let g:=listGetN ws
 induction wits with
 | nil=>intro _ h;simp[verifyReqWits]at h
 | cons q _ ih=>
  rcases q with ⟨u,v,w,t⟩;intro r hr;simp only[verifyReqWits,forceN_eq]at hr
  cases hg:and (Nat.ble (Nat.add u 1) nv) (and (Nat.ble (Nat.add v 1) ws.length) (and (Nat.ble (Nat.add w 1) ws.length) (and (Nat.ble (Nat.add t 1) ws.length) (not (Nat.beq v w)))))
  ·rw[hg,Bool.cond_false]at hr;exact ih r hr
  ·rw[hg,Bool.cond_true]at hr;simp only[Bool.and_eq_true,Bool.not_eq_true',Nat.ble_eq,Nat.add_eq]at hg
   obtain⟨hu,hv,hw,ht,n⟩:=hg;have hn:v≠w:=λe=>by simp[e]at n
   set d:=cond (Nat.beq (Nat.land (Nat.shiftRight liveM u) 1) 1) (cond (Nat.beq t (findInpLive u inps)) (c t) 0) (findPair t (findDead u deadUs))
   have hd:IsCritIdxU nv goal ws u t d:=by
    simp only[d,bit_land1_eq];cases lv:liveM.testBit u
    ·rcases @findDead_mem u deadUs with e|D;· rw[Bool.cond_false,e];exact isCritIdxU_zero (by omega)
     rcases @findPair_mem t (findDead u deadUs)with e|P;· rw[Bool.cond_false,e];exact isCritIdxU_zero (by omega)
     exact(hcritDead u _ D).2 t _ P
    ·cases e:Nat.beq t (findInpLive u inps);· exact isCritIdxU_zero (by omega)
     rw[Bool.cond_true,Bool.cond_true,Nat.eq_of_beq_eq_true e];exact(hcritInp u (by omega) lv).2
   cases m1:Nat.beq (Nat.land d (c v)) 0<;>rw[m1]at hr<;>try exact ih r hr
   cases m:Nat.beq (Nat.land (Nat.land d (c v)) (flipURaw nv u (c w))) 0<;>rw[m]at hr<;>try exact ih r hr
   cases tp:twoPatRaw (Nat.land (Nat.land d (c v)) (flipURaw nv u (c w))) (g v) (flipURaw nv u (g w))<;>rw[tp]at hr<;>try exact ih r hr
   refine(List.mem_cons.mp hr).elim (λe=> ?_) (ih r);subst e;dsimp only
   obtain⟨p,q,hp,hq,df⟩:=twoPatRaw_sound (valid_land_l (valid_land_l hd.2.1)) tp;simp at hp hq
   obtain⟨_,fc⟩:=flipURaw_spec (w:=c w) hnv (by omega:u<nv)
   obtain⟨_,fw⟩:=flipURaw_spec (w:=g w) hnv (by omega:u<nv)
   exact⟨by
    omega,by omega,by omega,hn,req_law_of_rows (by omega) (by omega) hn hd (hcritAll v (by omega)) (hcritAll w (by omega))
    hp.1.1 hq.1.1 hp.1.2 hq.1.2 (fc p▸hp.2) (fc q▸hq.2) (df.imp id λh2=>by rwa[fw p,fw q]at h2)⟩
noncomputable def scanLiveW (t v fm1 wv adjV:Nat) (l:List (Nat×Nat×Nat)) (tag0:Nat)
  (acc:List (Nat×Nat×Nat)):List (Nat×Nat×Nat):=
 @List.rec (Nat×Nat×Nat) (λ_=>Nat->List (Nat×Nat×Nat)->List (Nat×Nat×Nat)) (λ_ a=>a)
  (λp _ ih tag a=>
   let w:=p.1
   cond (or (Nat.beq w t) (bitTest adjV w)) (ih tag a)
    (forceN (Nat.land fm1 p.2.1) λr2=>
     cond (isZeroS r2) (ih tag a)
      (forceN (Nat.land (Nat.add tag 1013904223) 0xffffffff) λt1=>
       forceN (Nat.xor r2 t1) λm2=>
       cond (twoPatS m2 p.2.2 wv (Nat.xor t1 0x9e3779b9)) (ih t1 ((v,w,t)::a)) (ih t1 a))))
  l tag0 acc
noncomputable def scanLiveV (loSB hiSB:B16 Nat) (u t bitT cut cadj:Nat) (l:List (Nat×Nat×Nat))
  (restM0 tag0:Nat) (acc:List (Nat×Nat×Nat)):List (Nat×Nat×Nat):=
 @List.rec (Nat×Nat×Nat) (λ_=>Nat->Nat->List (Nat×Nat×Nat)->List (Nat×Nat×Nat)) (λ_ _ a=>a)
  (λp rest ih restM tag a=>
   let v:=p.1
   forceN (Nat.xor restM (Nat.shiftLeft 1 v)) λrestM'=>
   cond (or (Nat.beq v t) (Nat.beq restM' 0)) (ih restM' tag a)
    (forceN (getCadj cadj v) λadjV=>
     cond (Nat.beq (Nat.land restM' (Nat.xor 65535 (Nat.lor adjV bitT))) 0) (ih restM' tag a)
      (forceN (Nat.land cut p.2.1) λr1=>
       cond (isZeroS r1) (ih restM' tag a)
        (forceN (Nat.land (Nat.add tag 2246822519) 0xffffffff) λt1=>
         forceN (Nat.xor r1 t1) λm1=>
         forceN (flipUS loSB hiSB u m1 (Nat.xor t1 0x85ebca6b)) λfm1=>
         ih restM' t1 (scanLiveW t v fm1 p.2.2 adjV rest t1 a)))))
  l restM0 tag0 acc
noncomputable def findInIcw(key:Nat)(icw:List (Nat×Nat×Nat)):Nat:=
 @List.rec (Nat×Nat×Nat) (λ_=>Nat) 0 (λp _ ih=>cond (Nat.beq p.1 key) p.2.1 ih) icw
private noncomputable def buildLiveReqsLoop (loSB hiSB:B16 Nat) (nv cadj:Nat) (icw:List (Nat×Nat×Nat))
  (wsLen allM:Nat) (inps:List (Nat×Nat)) (tag0:Nat) (acc:List (Nat×Nat×Nat)):List (Nat×Nat×Nat):=
 @List.rec (Nat×Nat) (λ_=>Nat->List (Nat×Nat×Nat)->List (Nat×Nat×Nat)) (λ_ a=>a)
  (λp _ ih tag a=>
   let t:=p.1;let u:=p.2
   forceN (Nat.land (Nat.add tag 3266489917) 0xffffffff) λt1=>
   cond (and (Nat.ble (Nat.add u 1) nv) (Nat.ble (Nat.add t 1) wsLen))
    (forceN (findInIcw t icw) λcut=>
     cond (isZeroS cut) (ih t1 a)
      (forceN (Nat.shiftLeft 1 t) λbitT=>
       ih t1 (scanLiveV loSB hiSB u t bitT cut cadj icw allM t1 a)))
    (ih t1 a))
  inps tag0 acc
noncomputable def buildLiveReqsGo (loSB hiSB:B16 Nat) (nv cadj:Nat) (inps:List (Nat×Nat))
  (icw:List (Nat×Nat×Nat)) (wsLen tag0:Nat) (acc:List (Nat×Nat×Nat)):List (Nat×Nat×Nat):=
 forceN (Nat.sub (Nat.shiftLeft 1 wsLen) 1) λallM=>buildLiveReqsLoop loSB hiSB nv cadj icw wsLen allM inps tag0 acc
theorem splitLive_inps_crit {nv liveM goal:Nat} {gates:List (Nat×Nat×Nat)} {caList:List Nat}
  (hcritInp:∀u < nv,liveM.testBit u=true ->
   let inps:=(splitLiveGo nv liveM 0 0 (decodeBank gates ((List.range nv).map (hiC nv)))).1
   let ws:=(splitLiveGo nv liveM 0 0 (decodeBank gates ((List.range nv).map (hiC nv)))).2.2
   let t:=findInpLive u inps
   t<ws.length/\IsCritIdxU nv goal ws u t (listGetN caList t)) :
  let r:=splitLiveGo nv liveM 0 0 (decodeBank gates ((List.range nv).map (hiC nv)))
  ∀p∈r.1,p.2<nv->p.1<r.2.2.length->IsCritIdxU nv goal r.2.2 p.2 p.1 (listGetN caList p.1):=by
 dsimp;obtain⟨_,hf,hi,_⟩:=@splitLiveGo_bank_spec nv liveM gates
 intro p hp _ _;obtain⟨i,h,rfl⟩:=List.getElem_of_mem hp;obtain⟨u,hu,h0,lv,_⟩:=hi i h
 have he:(splitLiveGo nv liveM 0 0 (decodeBank gates ((List.range nv).map (hiC nv)))).1[i]=(i,u):=
  Option.some.inj (by simpa[List.getElem?_eq_getElem h]using h0)
 rw[he]
 simpa[findInpLive_mem (by rw[hf];exact List.Nodup.filter _ List.nodup_range) (List.mem_of_getElem? h0)]using (hcritInp u hu lv).2
theorem buildLiveReqsGo_sound {loSB hiSB:B16 Nat} {nv goal cadj tag0:Nat}
  {inps:List (Nat×Nat)} {caList ws:List Nat} {icw:List (Nat×Nat×Nat)}
  {acc:List (Nat×Nat×Nat)} (hnv:nv<=12)
  (hlo:∀u < nv,b16Get loSB u=Nat.shiftLeft (loC nv u) 32)
  (hhi:∀u < nv,b16Get hiSB u=Nat.shiftLeft (hiC nv u) 32)
  (hcritAll:∀idx < ws.length,IsCritIdxAll nv goal ws idx (listGetN caList idx))
  (hcritInps:∀p∈inps,p.2<nv->p.1<ws.length->IsCritIdxU nv goal ws p.2 p.1 (listGetN caList p.1))
  (hicw:IcwOK caList ws icw) (hacc:GoodReqs nv goal ws acc) :
  GoodReqs nv goal ws (buildLiveReqsGo loSB hiSB nv cadj inps icw ws.length tag0 acc):=by
 let c:=listGetN caList;let w:=listGetN ws;let G:=GoodReqs nv goal ws
 have hfi key:∀l,(∀p∈l,unS p.2.1=c p.1)->findInIcw key l=0\/unS (findInIcw key l)=c key:=λl=>by
  induction l with| nil=>exact λ_=>Or.inl rfl| cons p _ ih=>
   intro hl;unfold findInIcw;dsimp only;by_cases e:p.1=key
   ·subst e;rw[Nat.beq_refl];exact Or.inr (hl p (by simp))
   ·rw[beq_false_of_ne e];exact ih λq hq=>hl q (List.mem_cons_of_mem _ hq)
 have sW u t v fm1 wvS adjV (hu:u<nv) (hv:v<ws.length) (vt:v≠t) (ct:IsCritIdxU nv goal ws u t (c t))
   (hfm:unS fm1=flipURaw nv u (Nat.land (c t) (c v))) (hwv:unS wvS=w v) :
   ∀l tg a,(∀q∈l,v<q.1/\q.1<ws.length/\unS q.2.1=c q.1/\unS q.2.2=w q.1)->G a ->
   G (scanLiveW t v fm1 wvS adjV l tg a):=λl=>by
  induction l with| nil=>exact λ_ _ _ ha=>ha| cons q _ ih=>
   intro tg a hl ha;obtain⟨vlt,hqw,hcq,hwq⟩:=hl q (by simp)
   have hl' r hr:=hl r (List.mem_cons_of_mem _ hr);have sk z:=ih z a hl' ha
   unfold scanLiveW;dsimp only;cases or (Nat.beq q.1 t) (bitTest adjV q.1);swap;exact sk tg
   rw[forceN_eq];cases isZeroS (Nat.land fm1 q.2.1);swap;exact sk tg
   rw[forceN_eq,forceN_eq];set t1:=Nat.land (Nat.add tg 1013904223) 0xffffffff;have ht1:=land_ff32_lt (Nat.add tg 1013904223)
   cases tp:twoPatS (Nat.xor (Nat.land fm1 q.2.1) t1) q.2.2 wvS (Nat.xor t1 0x9e3779b9);· exact sk t1
   rw[twoPatS_eq (xor_lt32 ht1 (by decide)),unS_xor_tag ht1,unS_land,hfm,hcq,hwq,hwv]at tp
   refine ih t1 _ hl' λr hr=>(List.mem_cons.mp hr).elim (λe=> ?_) (ha r)
   subst e;obtain⟨n1,n2,h1,h2,df⟩:=twoPatRaw_sound (valid_land_r (hcritAll q.1 hqw).2.1) tp;simp at h1 h2
   obtain⟨_,fm⟩:=flipURaw_spec (w:=Nat.land (c t) (c v)) hnv hu
   let f (n:RowNv nv):RowNv nv:=⟨n.1^^^(1<<<u),xor_two_pow_lt hu n.2⟩
   have fp {n:RowNv nv} (h:(flipURaw nv u (Nat.land (c t) (c v))).testBit n.1=true) :
     (c t).testBit (f n).1=true/\(c v).testBit (f n).1=true/\(w v).testBit (f n).1=(w v).testBit n.1:=by
    have x:(Nat.land (c t) (c v)).testBit (f n).1=true:=fm n▸h;simp at x
    exact⟨x.1,x.2,by simpa[f,Nat.xor_assoc]using (ct.2.2 (f n) x.1).2.2 v hv vt⟩
   obtain⟨c1,v1,w1⟩:=fp h1.1;obtain⟨c2,v2,w2⟩:=fp h2.1
   exact⟨hv,hqw,ct.1,Nat.ne_of_lt vlt,req_law_of_rows hu hqw (Nat.ne_of_lt vlt) ct (hcritAll v hv) (hcritAll q.1 hqw) c1 c2 v1 v2
    (by simpa[f]using h1.2) (by simpa[f]using h2.2) (df.elim (λh=>Or.inr (by simpa[f]using h)) (λh=>Or.inl (by rwa[w1,w2])))⟩
 have sV u t bitT cutS (hu:u<nv) (ct:IsCritIdxU nv goal ws u t (c t)) (hcut:unS cutS=c t) :
   ∀l rM tg a,IcwOK caList ws l->G a->G (scanLiveV loSB hiSB u t bitT cutS cadj l rM tg a):=λl=>by
  induction l with| nil=>exact λ_ _ _ _ ha=>ha| cons p rest ih=>
   intro rM tg a ⟨hm,hpw⟩ ha;obtain⟨hv,hcp,hwp⟩:=hm p (by simp);obtain⟨hlt,hpw'⟩:=List.pairwise_cons.mp hpw
   have hm' q hq:=hm q (List.mem_cons_of_mem _ hq);have sk:=ih (Nat.xor rM (Nat.shiftLeft 1 p.1)) tg a ⟨hm',hpw'⟩ ha
   unfold scanLiveV;dsimp only;rw[forceN_eq]
   cases hsk:or (Nat.beq p.1 t) (Nat.beq (Nat.xor rM (Nat.shiftLeft 1 p.1)) 0);swap;exact sk
   have vt:p.1≠t:=λe=>by rw[e,Nat.beq_refl,Bool.true_or]at hsk;cases hsk
   rw[forceN_eq];cases Nat.beq (Nat.land (Nat.xor rM (Nat.shiftLeft 1 p.1)) (Nat.xor 65535 (Nat.lor (getCadj cadj p.1) bitT))) 0;swap;exact sk
   rw[forceN_eq];cases isZeroS (Nat.land cutS p.2.1);swap;exact sk
   rw[forceN_eq,forceN_eq,forceN_eq];set t1:=Nat.land (Nat.add tg 2246822519) 0xffffffff;have ht1:=land_ff32_lt (Nat.add tg 2246822519)
   exact ih _ t1 _ ⟨hm',hpw'⟩ (sW u t p.1 _ p.2.2 _ hu hv vt ct
    (by rw[flipUS_unS (hlo u hu) (hhi u hu) (xor_lt32 ht1 (by decide)),unS_xor_tag ht1,unS_land,hcut,hcp]) hwp
    rest t1 a (λq hq=>⟨hlt q hq,hm' q hq⟩) ha)
 unfold buildLiveReqsGo;rw[forceN_eq]
 have go:∀is tg a,(∀p∈is,p.2<nv->p.1<ws.length->IsCritIdxU nv goal ws p.2 p.1 (c p.1))->G a ->
   G (buildLiveReqsLoop loSB hiSB nv cadj icw ws.length (Nat.sub (Nat.shiftLeft 1 ws.length) 1) is tg a):=λis=>by
  induction is with| nil=>exact λ_ _ _ ha=>ha| cons p _ ih=>
   intro tg a hci ha;have hci' q hq:=hci q (List.mem_cons_of_mem _ hq)
   unfold buildLiveReqsLoop;dsimp only;rw[forceN_eq];set t1:=Nat.land (Nat.add tg 3266489917) 0xffffffff
   have sk:=ih t1 a hci' ha
   cases hg:and (Nat.ble (Nat.add p.2 1) nv) (Nat.ble (Nat.add p.1 1) ws.length);· exact sk
   rw[forceN_eq];simp only[Bool.and_eq_true,Nat.ble_eq,Nat.add_eq]at hg
   cases hz:isZeroS (findInIcw p.1 icw);swap;exact sk
   rw[forceN_eq]
   exact ih t1 _ hci' (sV p.2 p.1 _ _ (by omega) (hci p (by simp) (by omega) (by omega))
    ((hfi p.1 icw λq hq=>(hicw.1 q hq).2.1).elim (λh0=>by rw[h0]at hz;cases hz) id) icw _ t1 a hicw ha)
 exact go inps tag0 acc hcritInps hacc
def popcnt4(m:Nat):Nat:=
 Nat.add (Nat.add (Nat.land m 1) (Nat.land (Nat.shiftRight m 1) 1))
  (Nat.add (Nat.land (Nat.shiftRight m 2) 1) (Nat.land (Nat.shiftRight m 3) 1))
def popcnt8(m:Nat):Nat:=
 Nat.add (popcnt4 (Nat.land m 15)) (popcnt4 (Nat.shiftRight m 4))
def popcnt16(m:Nat):Nat:=
 Nat.add (popcnt8 (Nat.land m 255)) (popcnt8 (Nat.shiftRight m 8))
def lsb16(m:Nat):Nat:=
 let r0:=cond (Nat.beq (Nat.land m 255) 0) 8 0
 let m1:=Nat.shiftRight m r0
 let r1:=cond (Nat.beq (Nat.land m1 15) 0) 4 0
 let m2:=Nat.shiftRight m1 r1
 let r2:=cond (Nat.beq (Nat.land m2 3) 0) 2 0
 let m3:=Nat.shiftRight m2 r2
 let r3:=cond (Nat.beq (Nat.land m3 1) 0) 1 0
 Nat.add (Nat.add r0 r1) (Nat.add r2 r3)
def b2Mod{α:Type}(i:Nat)(f:α->α)(t:B2 α):B2 α:=
 cond (Nat.beq (Nat.land i 1) 0) (f t.1,t.2) (t.1,f t.2)
def b4Mod{α:Type}(i:Nat)(f:α->α)(t:B4 α):B4 α:=
 cond (Nat.beq (Nat.land i 2) 0) (b2Mod i f t.1,t.2) (t.1,b2Mod i f t.2)
def b8Mod{α:Type}(i:Nat)(f:α->α)(t:B8 α):B8 α:=
 cond (Nat.beq (Nat.land i 4) 0) (b4Mod i f t.1,t.2) (t.1,b4Mod i f t.2)
def b16Mod{α:Type}(i:Nat)(f:α->α)(t:B16 α):B16 α:=
 cond (Nat.beq (Nat.land i 8) 0) (b8Mod i f t.1,t.2) (t.1,b8Mod i f t.2)
abbrev ReqIdx:=B16 (List (Nat×Nat))×B16 (List (Nat×Nat))
def emptyB16L:B16 (List (Nat×Nat)):=
 (((([],[]),([],[])),(([],[]),([],[]))),((([],[]),([],[])),(([],[]),([],[]))))
def emptyReqIdx:ReqIdx:=(emptyB16L,emptyB16L)
noncomputable def addPairMask(otherBit tBit:Nat)(l:List (Nat×Nat)):List (Nat×Nat):=
 @List.rec (Nat×Nat) (λ_=>List (Nat×Nat)) [(otherBit,tBit)]
  (λp rest ih=>cond (Nat.beq p.1 otherBit) (forceN (Nat.lor p.2 tBit) λm=>(p.1,m)::rest) (p::ih)) l
noncomputable def forcePairList{β:Type}(l:List (Nat×Nat))(k:List (Nat×Nat)->β):β:=
 @List.rec (Nat×Nat) (λ_=>(List (Nat×Nat)->β)->β) (λc=>c [])
  (λp _ ih c=>forceN p.1 λa=>forceN p.2 λb=>ih λr=>c ((a,b)::r)) l k
noncomputable def forceB2P{β:Type}(t:B2 (List (Nat×Nat)))(k:B2 (List (Nat×Nat))->β):β:=
 Prod.casesOn t λa b=>forcePairList a λa'=>forcePairList b λb'=>k (a',b')
noncomputable def forceB4P{β:Type}(t:B4 (List (Nat×Nat)))(k:B4 (List (Nat×Nat))->β):β:=
 Prod.casesOn t λa b=>forceB2P a λa'=>forceB2P b λb'=>k (a',b')
noncomputable def forceB8P{β:Type}(t:B8 (List (Nat×Nat)))(k:B8 (List (Nat×Nat))->β):β:=
 Prod.casesOn t λa b=>forceB4P a λa'=>forceB4P b λb'=>k (a',b')
noncomputable def forceB16P{β:Type}(t:B16 (List (Nat×Nat)))(k:B16 (List (Nat×Nat))->β):β:=
 Prod.casesOn t λa b=>forceB8P a λa'=>forceB8P b λb'=>k (a',b')
private noncomputable def mkReqIdxGo (reqs:List (Nat×Nat×Nat)) (acc:ReqIdx):ReqIdx:=
 @List.rec (Nat×Nat×Nat) (λ_=>ReqIdx->ReqIdx) (λa=>a)
  (λr _ ih a=>
   let v:=r.1;let w:=r.2.1;let t:=r.2.2
   cond (and (Nat.ble (Nat.add v 1) 16) (and (Nat.ble (Nat.add w 1) 16) (Nat.ble (Nat.add t 1) 16)))
    (forceN (Nat.shiftLeft 1 v) λvB=>forceN (Nat.shiftLeft 1 w) λwB=>forceN (Nat.shiftLeft 1 t) λtB=>
     ih (b16Mod w (addPairMask vB tB) (b16Mod v (addPairMask wB tB) a.1),b16Mod t (λl=>(vB,wB)::l) a.2))
    (ih a))
  reqs acc
noncomputable def mkReqIdx(reqs:List (Nat×Nat×Nat)):ReqIdx:=mkReqIdxGo reqs emptyReqIdx
noncomputable def mkReqIdxC{β:Type}(reqs:List (Nat×Nat×Nat))(k:ReqIdx->β):β:=
 let ri:=mkReqIdx reqs
 forceB16P ri.1 λp=>forceB16P ri.2 λt=>k (p,t)
def colMask(m0 m1 m2 m3 c:Nat):Nat:=
 cond (Nat.beq c 0) m0 (cond (Nat.beq c 1) m1 (cond (Nat.beq c 2) m2 m3))
noncomputable def gatherT(aC:Nat)(pairs:List (Nat×Nat))(acc:Nat):Nat:=
 @List.rec (Nat×Nat) (λ_=>Nat->Nat) (λm=>m)
  (λp _ ih m=>cond (Nat.beq (Nat.land aC p.1) 0) (ih m) (forceN (Nat.lor m p.2) λm'=>ih m'))
  pairs acc
private noncomputable def gatherClrGo (aK:Nat) (ts:List (Nat×Nat)) (acc:Nat):Nat:=
 @List.rec (Nat×Nat) (λ_=>Nat->Nat) (λm=>m)
  (λp _ ih m=>
   let m1:=cond (Nat.beq (Nat.land aK p.1) 0) m (Nat.lor m p.2)
   let m2:=cond (Nat.beq (Nat.land aK p.2) 0) m1 (Nat.lor m1 p.1)
   forceN m2 λm'=>ih m')
  ts acc
noncomputable def gatherClr(aK:Nat)(ts:List (Nat×Nat))(acc:Nat):Nat:=
 cond (Nat.beq aK 0) acc (gatherClrGo aK ts acc)
noncomputable def pickVar4(cadj unass d0 d1 d2 d3 n:Nat):Nat:=
 forceN (Nat.land d0 unass) λu0=>
 forceN (Nat.land d1 unass) λu1=>
 forceN (Nat.land d2 unass) λu2=>
 forceN (Nat.land d3 unass) λu3=>
 let o01:=Nat.lor u0 u1;let o23:=Nat.lor u2 u3
 let a01:=Nat.land u0 u1;let a23:=Nat.land u2 u3
 forceN (Nat.lor (Nat.lor a01 a23) (Nat.land o01 o23)) λge2=>
 forceN (Nat.xor unass ge2) λunitM=>
 cond (not (Nat.beq unitM 0)) (lsb16 unitM)
  (forceN (Nat.lor (Nat.land a01 o23) (Nat.land o01 a23)) λge3=>
   forceN (Nat.xor ge2 ge3) λsz2M=>
   let cand:=cond (not (Nat.beq sz2M 0)) sz2M
    (let sz3M:=Nat.xor ge3 (Nat.land a01 a23)
     cond (not (Nat.beq sz3M 0)) sz3M unass)
   lsb16 cand)
noncomputable def tryColor4 (go:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Bool)
  (rem nbRem bitBV:Nat) (pairs ts:List (Nat×Nat))
  (d0 d1 d2 d3 a0 a1 a2 a3 c:Nat):Bool:=
 let aC:=colMask a0 a1 a2 a3 c
 let tU:=cond (or (Nat.beq c 3) (Nat.beq aC 0)) 0 (gatherT aC pairs 0)
 forceN tU λtU'=>
 let aGt:=cond (Nat.beq c 0) (Nat.lor a1 (Nat.lor a2 a3))
  (cond (Nat.beq c 1) (Nat.lor a2 a3) (cond (Nat.beq c 2) a3 0))
 cond (not (Nat.beq (Nat.land tU' aGt) 0)) false
  (let cl0:=cond (Nat.beq c 0) nbRem (gatherClr a0 ts 0)
   let cl1:=cond (Nat.beq c 1) nbRem (cond (Nat.beq c 0) tU' (gatherClr a1 ts 0))
   let cl2:=cond (Nat.beq c 2) nbRem (cond (Nat.ble c 1) tU' (gatherClr a2 ts 0))
   let cl3:=cond (Nat.beq c 3) nbRem tU'
   forceN (Nat.land d0 (Nat.xor 65535 cl0)) λd0'=>
   forceN (Nat.land d1 (Nat.xor 65535 cl1)) λd1'=>
   forceN (Nat.land d2 (Nat.xor 65535 cl2)) λd2'=>
   forceN (Nat.land d3 (Nat.xor 65535 cl3)) λd3'=>
   cond (Nat.beq (Nat.land (Nat.lor (Nat.lor d0' d1') (Nat.lor d2' d3')) rem) rem)
    (forceN (cond (Nat.beq c 0) (Nat.lor a0 bitBV) a0) λa0'=>
     forceN (cond (Nat.beq c 1) (Nat.lor a1 bitBV) a1) λa1'=>
     forceN (cond (Nat.beq c 2) (Nat.lor a2 bitBV) a2) λa2'=>
     forceN (cond (Nat.beq c 3) (Nat.lor a3 bitBV) a3) λa3'=>
     go rem d0' d1' d2' d3' a0' a1' a2' a3')
    false)
noncomputable def tryC4 (go:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Bool)
  (rem nbRem bitBV:Nat) (pairs ts:List (Nat×Nat))
  (d0 d1 d2 d3 a0 a1 a2 a3 l:Nat):Bool:=
 @Nat.rec (λ_=>Bool) false
  (λc ih=>
   cond (Nat.beq (Nat.land (colMask d0 d1 d2 d3 c) bitBV) 0) ih
    (cond (tryColor4 go rem nbRem bitBV pairs ts d0 d1 d2 d3 a0 a1 a2 a3 c) true ih))
  l
noncomputable def solveRec4(fuel n C cadj:Nat)(ri:ReqIdx):
  Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Bool:=
 @Nat.rec (λ_=>Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Bool)
  (λ_ _ _ _ _ _ _ _ _=>true)
  (λ_ ih unass d0 d1 d2 d3 a0 a1 a2 a3=>
   cond (Nat.beq unass 0) true
    (forceN (pickVar4 cadj unass d0 d1 d2 d3 n) λbv=>
     forceN (Nat.shiftLeft 1 bv) λbitBV=>
     forceN (Nat.xor unass bitBV) λrem=>
     forceN (Nat.land (getCadj cadj bv) rem) λnbRem=>
     tryC4 ih rem nbRem bitBV (b16Get ri.1 bv) (b16Get ri.2 bv) d0 d1 d2 d3 a0 a1 a2 a3 C))
  fuel
noncomputable def noEdgeP(cadj active m:Nat):Bool:=
 @Nat.rec (λ_=>Bool) true
  (λv ih=>cond (and (bitTest active v) (not (Nat.beq (Nat.land (getCadj cadj v) active) 0))) false ih) m
noncomputable def canSolvePI(n C cadj:Nat)(ri:ReqIdx)(active:Nat):Bool:=
 cond (or (Nat.ble 5 C) (Nat.ble 17 n)) true
  (cond (Nat.beq C 0) (Nat.beq active 0)
   (cond (Nat.beq C 1) (noEdgeP cadj active n)
    (forceN (cond (Nat.ble 3 C) active 0) λd2=>
     forceN (cond (Nat.ble 4 C) active 0) λd3=>
     solveRec4 (Nat.add n 1) n C cadj ri active active active d2 d3 0 0 0 0)))
noncomputable def canMergeLoop4 (n C cadj:Nat) (ri:ReqIdx)
  (rem nbRem bitIJ tU d0 d1 d2 d3 l:Nat):Bool:=
 @Nat.rec (λ_=>Bool) false
  (λc ih=>
   let cl0:=cond (Nat.beq c 0) nbRem 0
   let cl1:=cond (Nat.beq c 1) nbRem (cond (Nat.beq c 0) tU 0)
   let cl2:=cond (Nat.beq c 2) nbRem (cond (Nat.ble c 1) tU 0)
   let cl3:=cond (Nat.beq c 3) nbRem tU
   forceN (Nat.land d0 (Nat.xor 65535 cl0)) λd0'=>
   forceN (Nat.land d1 (Nat.xor 65535 cl1)) λd1'=>
   forceN (Nat.land d2 (Nat.xor 65535 cl2)) λd2'=>
   forceN (Nat.land d3 (Nat.xor 65535 cl3)) λd3'=>
   let hit:=cond (Nat.beq (Nat.land (Nat.lor (Nat.lor d0' d1') (Nat.lor d2' d3')) rem) rem)
    (solveRec4 (Nat.add n 1) n C cadj ri rem d0' d1' d2' d3'
     (cond (Nat.beq c 0) bitIJ 0) (cond (Nat.beq c 1) bitIJ 0)
     (cond (Nat.beq c 2) bitIJ 0) (cond (Nat.beq c 3) bitIJ 0))
    false
   cond hit true ih)
  l
noncomputable def canMergePI(n C cadj:Nat)(ri:ReqIdx)(active ii jj:Nat):Bool:=
 cond (or (Nat.ble 5 C) (Nat.ble 17 n)) true
  (cond (or (Nat.beq C 0) (bitTest (getCadj cadj ii) jj)) false
   (forceN (Nat.shiftLeft 1 ii) λbitI=>
    forceN (Nat.shiftLeft 1 jj) λbitJ=>
    forceN (Nat.lor bitI bitJ) λbitIJ=>
    forceN (Nat.xor active bitIJ) λrem=>
    forceN (Nat.land (Nat.lor (getCadj cadj ii) (getCadj cadj jj)) rem) λnbRem=>
    forceN (gatherT bitJ (b16Get ri.1 ii) 0) λtU=>
    forceN (cond (Nat.ble 2 C) rem 0) λd1=>
    forceN (cond (Nat.ble 3 C) rem 0) λd2=>
    forceN (cond (Nat.ble 4 C) rem 0) λd3=>
    canMergeLoop4 n C cadj ri rem nbRem bitIJ tU rem d1 d2 d3 C))
private lemma forcePairList_eq {β:Type} (l:List (Nat×Nat)) (k:List (Nat×Nat)->β) :
  forcePairList l k=k l:=by
 induction l generalizing k with
 | nil=>rfl
 | cons p _ ih=>rcases p with ⟨a,b⟩;unfold forcePairList;dsimp;rw[forceN_eq,forceN_eq];exact ih _
private lemma forceB16P_eq {β:Type} (t:B16 (List (Nat×Nat))) (k:B16 (List (Nat×Nat))->β) :
  forceB16P t k=k t:=by
 rcases t with ⟨⟨⟨⟨_,_⟩,⟨_,_⟩⟩,⟨⟨_,_⟩,⟨_,_⟩⟩⟩,⟨⟨⟨_,_⟩,⟨_,_⟩⟩,⟨⟨_,_⟩,⟨_,_⟩⟩⟩⟩
 simp[forceB16P,forceB8P,forceB4P,forceB2P,forcePairList_eq]
theorem mkReqIdxC_eq{β:Type}(reqs:List (Nat×Nat×Nat))(k:ReqIdx->β):
  mkReqIdxC reqs k=k (mkReqIdx reqs):=by
 unfold mkReqIdxC;rw[forceB16P_eq,forceB16P_eq]
private lemma beq_dec (p q:Nat):Nat.beq p q=decide (p=q):=by
 cases h:Nat.beq p q
 ·exact(decide_eq_false λe=>by rw[e,Nat.beq_refl]at h;cases h).symm
 ·exact(decide_eq_true (Nat.eq_of_beq_eq_true h)).symm
private lemma shl1_tb (y x:Nat):(Nat.shiftLeft 1 y).testBit x=decide (y=x):=by
 rw[shiftLeft_one_eq,Nat.testBit_two_pow]
private lemma colMask_upd (m0 m1 m2 m3 c v k:Nat) (hc:c<4) (hk:k<4) :
  colMask (cond (Nat.beq c 0) v m0) (cond (Nat.beq c 1) v m1) (cond (Nat.beq c 2) v m2) (cond (Nat.beq c 3) v m3) k =
  if k=c then v else colMask m0 m1 m2 m3 k:=by
 rcases lt4_cases hk with rfl|rfl|rfl|rfl<;>rcases lt4_cases hc with rfl|rfl|rfl|rfl<;>rfl
private lemma colMask_lor (a0 a1 a2 a3 c b k:Nat) (hc:c<4) (hk:k<4) :
  colMask (cond (Nat.beq c 0) (Nat.lor a0 b) a0) (cond (Nat.beq c 1) (Nat.lor a1 b) a1)
   (cond (Nat.beq c 2) (Nat.lor a2 b) a2) (cond (Nat.beq c 3) (Nat.lor a3 b) a3) k =
  if k=c then Nat.lor (colMask a0 a1 a2 a3 k) b else colMask a0 a1 a2 a3 k:=by
 rcases lt4_cases hk with rfl|rfl|rfl|rfl<;>rcases lt4_cases hc with rfl|rfl|rfl|rfl<;>rfl
private lemma b16Get_b16Mod {α:Type} (t:B16 α) {i j:Nat} (hi:i<16) (hj:j<16) (f:α->α) :
  b16Get (b16Mod i f t) j=if j=i then f (b16Get t j)else b16Get t j:=by
 have st {β:Type} k (g:β->α) (m:β->β) (p:β×β)
   (hm:Nat.beq (Nat.land i k) 0=Nat.beq (Nat.land j k) 0->∀x,g (m x)=if j=i then f (g x)else g x) :
   (let r:=cond (Nat.beq (Nat.land i k) 0) (m p.1,p.2) (p.1,m p.2);g (cond (Nat.beq (Nat.land j k) 0) r.1 r.2)) =
   if j=i then f (g (cond (Nat.beq (Nat.land j k) 0) p.1 p.2))else g (cond (Nat.beq (Nat.land j k) 0) p.1 p.2):=by
  cases ei:Nat.beq (Nat.land i k) 0<;>cases ej:Nat.beq (Nat.land j k) 0 <;>
   first| exact hm (ei.trans ej.symm) _| simp[show j≠i from λe=>by rw[<-e,ej]at ei;cases ei]
 let g2 (x:B2 α):=cond (Nat.beq (Nat.land j 1) 0) x.1 x.2
 let g4 (x:B4 α):=g2 (cond (Nat.beq (Nat.land j 2) 0) x.1 x.2)
 exact st 8 (λx:B8 α=>g4 (cond (Nat.beq (Nat.land j 4) 0) x.1 x.2)) (b8Mod i f) t λh8 x8=>
  st 4 g4 (b4Mod i f) x8 λh4 x4=>st 2 g2 (b2Mod i f) x4 λh2 x2=>st 1 id f x2 λh1 _=>by
   have bit x k:x.testBit k = !Nat.beq (Nat.land x (2^k)) 0:=by rw[<-testBit_eq_land_shift,shiftLeft_one_eq]
   have eq:j=i:=Nat.eq_of_testBit_eq λb=>by
    rcases(show b=0\/b=1\/b=2\/b=3\/4<=b by omega)with rfl|rfl|rfl|rfl|hge
    ·rw[bit,bit];exact congrArg (!·) h1.symm
    ·rw[bit,bit];exact congrArg (!·) h2.symm
    ·rw[bit,bit];exact congrArg (!·) h4.symm
    ·rw[bit,bit];exact congrArg (!·) h8.symm
    ·rw[testBit_eq_false_of_lt_pow hj hge,testBit_eq_false_of_lt_pow hi hge]
   simp[eq]
def ValidColP(n C cadj:Nat)(reqs:List (Nat×Nat×Nat))(active:Nat)(col:Nat->Nat):Prop:=
 active<2^n /\
 (∀v < n,active.testBit v=true->col v<C) /\
 (∀v w,v<n->w<n->active.testBit v=true->active.testBit w=true ->
  bitTest (getCadj cadj v) w=true->col v≠col w) /\
 (∀r∈reqs,r.1<n/\r.2.1<n/\r.2.2<n /\
  (active.testBit r.1=true->active.testBit r.2.1=true->active.testBit r.2.2=true ->
   col r.1=col r.2.1->col r.2.2<=col r.1))
def SubMask(a b:Nat):Prop:=∀i,a.testBit i=true->b.testBit i=true
private lemma sub_lt2 {a b n:Nat} (hb:b<2^n) (h:SubMask a b):a<2^n:=
 lt_two_pow_of_testBit λk hk=>Bool.eq_false_iff.mpr λht=>
  Bool.noConfusion ((testBit_eq_false_of_lt_pow hb hk).symm.trans (h k ht))
private lemma bit_of_land_ne0 {a b:Nat} (h:Nat.beq (Nat.land a (Nat.shiftLeft 1 b)) 0=false):a.testBit b=true:=by
 cases ha:a.testBit b;swap;rfl
 exfalso;have:Nat.land a (Nat.shiftLeft 1 b)=0:=Nat.eq_of_testBit_eq λr=>by
  rw[testBit_land',shl1_tb,Nat.zero_testBit];by_cases e:b=r;subst e;simp[ha];simp[e]
 rw[this,Nat.beq_refl]at h;cases h
def ReqIdxOK(n:Nat)(reqs:List (Nat×Nat×Nat))(ri:ReqIdx):Prop:=
 (∀v < n,∀p∈b16Get ri.1 v,∃w < n,p.1=Nat.shiftLeft 1 w /\
  ∀t,p.2.testBit t=true->(v,w,t)∈reqs\/(w,v,t)∈reqs) /\
 (∀t < n,∀p∈b16Get ri.2 t,∃v w,v<n/\w<n/\p.1=Nat.shiftLeft 1 v/\p.2=Nat.shiftLeft 1 w /\
  (v,w,t)∈reqs)
theorem mkReqIdx_ok {n:Nat} (hn:n<=16) (reqs:List (Nat×Nat×Nat))
  (hbnd:∀r∈reqs,r.1<n/\r.2.1<n/\r.2.2<n):ReqIdxOK n reqs (mkReqIdx reqs):=by
 let P v (l:List (Nat×Nat)):=∀p∈l,∃u < n,p.1=Nat.shiftLeft 1 u/\∀x,p.2.testBit x=true->(v,u,x)∈reqs\/(u,v,x)∈reqs
 have add_ok {v w t l} (hw:w<n) (hvw:(v,w,t)∈reqs\/(w,v,t)∈reqs) (hl:P v l) :
    P v (addPairMask (Nat.shiftLeft 1 w) (Nat.shiftLeft 1 t) l):=by
  induction l with
  | nil=>
       intro p hp;simp only[addPairMask,List.mem_singleton]at hp;subst hp
       exact⟨w,hw,rfl,λx hx=>by rw[shl1_tb,decide_eq_true_eq]at hx;exact hx▸hvw⟩
  | cons q _ ih=>
    intro p hp;unfold addPairMask at hp;dsimp only at hp
    cases heq:Nat.beq q.1 (Nat.shiftLeft 1 w)
    ·rw[heq,Bool.cond_false]at hp;exact(List.mem_cons.mp hp).elim (·▸hl q List.mem_cons_self) (ih (λy hy=>hl y (List.mem_cons_of_mem _ hy)) p)
    ·rw[heq,Bool.cond_true,forceN_eq]at hp
     refine(List.mem_cons.mp hp).elim (λe=>e ▸ ?_) (λh=>hl p (List.mem_cons_of_mem _ h))
     obtain⟨u,hu,hu1,hu2⟩:=hl q List.mem_cons_self
     have uw:u=w:=by have h:=hu1.symm.trans (Nat.eq_of_beq_eq_true heq);rw[shiftLeft_one_eq,shiftLeft_one_eq]at h;exact Nat.pow_right_injective (by decide:1<2) h
     subst uw;refine⟨u,hu,hu1,λx hx=> ?_⟩
     rw[testBit_lor',shl1_tb,Bool.or_eq_true,decide_eq_true_eq]at hx;exact hx.elim (hu2 x) (·▸hvw)
 have go:∀sub acc,(∀r∈sub,r∈reqs)->ReqIdxOK n reqs acc->ReqIdxOK n reqs (mkReqIdxGo sub acc):=λsub=>by
  induction sub with
  | nil=>exact λ_ _ h=>h
  | cons r _ ih=>
    intro acc hsub ⟨h1,h2⟩;rcases r with ⟨v,w,t⟩;unfold mkReqIdxGo;dsimp
    have hr:(v,w,t)∈reqs:=hsub _ List.mem_cons_self
    obtain⟨hv,hw,ht⟩:=hbnd _ hr;dsimp at hv hw ht
    rw[show and (Nat.ble (Nat.add v 1) 16) (and (Nat.ble (Nat.add w 1) 16) (Nat.ble (Nat.add t 1) 16))=true by simp[Nat.ble_eq];omega,
     Bool.cond_true,forceN_eq,forceN_eq,forceN_eq]
    refine ih _ (λq hq=>hsub q (List.mem_cons_of_mem _ hq)) ⟨λx hx p hp=> ?_,λx hx p hp=> ?_⟩
    ·have hmid y (hy:y<n):P y (b16Get (b16Mod v (addPairMask (Nat.shiftLeft 1 w) (Nat.shiftLeft 1 t)) acc.1) y):=by
      rw[b16Get_b16Mod _ (by omega) (by omega)];split_ifs with hyv;subst hyv;exact add_ok hw (Or.inl hr) (h1 y hy);exact h1 y hy
     rw[b16Get_b16Mod _ (by omega) (by omega)]at hp;split_ifs at hp with hxw
     subst hxw;exact add_ok hv (Or.inr hr) (hmid x hx) p hp;exact hmid x hx p hp
    ·rw[b16Get_b16Mod _ (by omega) (by omega)]at hp;split_ifs at hp with hxt
     ·subst hxt;exact(List.mem_cons.mp hp).elim (·▸⟨v,w,hv,hw,rfl,rfl,hr⟩) (h2 x hx p)
     ·exact h2 x hx p hp
 have hemp (x:Nat):b16Get emptyB16L x=[]:=by
  unfold b16Get emptyB16L
  cases Nat.beq (Nat.land x 8) 0<;>cases Nat.beq (Nat.land x 4) 0<;>cases Nat.beq (Nat.land x 2) 0<;>cases Nat.beq (Nat.land x 1) 0<;>rfl
 exact go reqs emptyReqIdx (λ_ h=>h)
  ⟨(λv _ _ h=>by change _∈b16Get emptyB16L v at h;rw[hemp]at h;cases h),
   (λt _ _ h=>by change _∈b16Get emptyB16L t at h;rw[hemp]at h;cases h)⟩
def DomOK4(n rem d0 d1 d2 d3:Nat)(col:Nat->Nat):Prop:=
 ∀x < n,rem.testBit x=true->(colMask d0 d1 d2 d3 (col x)).testBit x=true
def ValOK4(n active unass a0 a1 a2 a3:Nat)(col:Nat->Nat):Prop:=
 ∀c < 4,∀x,(colMask a0 a1 a2 a3 c).testBit x=true ↔
  x<n/\active.testBit x=true/\unass.testBit x=false/\col x=c
private lemma lsb_step {x k:Nat} (hx:x % 2^(2*k)≠0) :
  let r:=cond (Nat.beq (Nat.land x (2^k-1)) 0) k 0
  (Nat.shiftRight x r) % 2^k≠0/\∀b,(Nat.shiftRight x r).testBit b=x.testBit (r+b):=by
 have hm:Nat.land x (2^k-1)=x % 2^k:=Nat.and_two_pow_sub_one_eq_mod x k
 refine⟨?_,λb=>testBit_shiftRight' x _ b⟩
 cases h:Nat.beq (Nat.land x (2^k-1)) 0
 ·rw[Bool.cond_false];change x % 2^k≠0;intro h0;rw[hm,h0,Nat.beq_refl]at h;cases h
 ·have h0:x % 2^k=0:=hm▸Nat.eq_of_beq_eq_true h
  rw[Bool.cond_true,show Nat.shiftRight x k=x / 2^k from Nat.shiftRight_eq_div_pow x k]
  intro hd;apply hx;rw[show 2^(2*k)=2^k*2^k by rw[<-Nat.pow_add,Nat.two_mul]]
  have hq:=(Nat.div_add_mod x (2^k)).symm;have hr:=(Nat.div_add_mod (x / 2^k) (2^k)).symm
  rw[h0,Nat.add_zero]at hq;rw[hd,Nat.add_zero]at hr;rw[hq,hr,<-Nat.mul_assoc,Nat.mul_mod_right]
private lemma lsb16_spec {m:Nat} (hne:m≠0) (hlt:m<65536):m.testBit (lsb16 m)=true:=by
 obtain⟨h1,e1⟩:=lsb_step (x:=m) (k:=8) (by rw[show 2^(2*8)=65536 from rfl,Nat.mod_eq_of_lt hlt];exact hne)
 obtain⟨h2,e2⟩:=lsb_step (k:=4) h1;obtain⟨h3,e3⟩:=lsb_step (k:=2) h2;obtain⟨h4,e4⟩:=lsb_step (k:=1) h3
 simp only[Nat.reducePow,Nat.reduceSub]at e1 e2 e3 e4 h4
 unfold lsb16;simp only[Nat.add_eq]
 rw[show ∀a b c d:Nat,(a+b)+(c+d)=a+(b+(c+(d+0))) by intros;omega,<-e1,<-e2,<-e3,<-e4,Nat.testBit_zero]
 exact decide_eq_true (by omega)
private lemma pickVar4_spec {cadj unass d0 d1 d2 d3 n:Nat} (hn:n<=16) (hne:unass≠0) (hlt:unass<2^n) :
  let bv:=pickVar4 cadj unass d0 d1 d2 d3 n
  bv<n/\unass.testBit bv=true:=by
 have hun16:unass<65536:=Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hn)
 have hsub_bit {m} (hm:SubMask m unass) (hm0:m≠0):=hm _ (lsb16_spec hm0 (sub_lt2 (n:=16) hun16 hm))
 have hret:unass.testBit (pickVar4 cadj unass d0 d1 d2 d3 n)=true:=by
  unfold pickVar4;simp only[forceN_eq]
  set u0:=Nat.land d0 unass;set u1:=Nat.land d1 unass;set u2:=Nat.land d2 unass;set u3:=Nat.land d3 unass
  set o01:=Nat.lor u0 u1;set o23:=Nat.lor u2 u3;set a01:=Nat.land u0 u1;set a23:=Nat.land u2 u3
  set ge2:=Nat.lor (Nat.lor a01 a23) (Nat.land o01 o23)
  have hmk {m} (hf:∀i,unass.testBit i=false->m.testBit i=false):SubMask m unass:=λi h=>by
   cases a:unass.testBit i;rw[hf i a]at h;cases h;rfl
  have hge2:SubMask ge2 unass:=hmk λi a=>by simp[ge2,a01,a23,o01,o23,u0,u1,u2,u3,a]
  cases hu:not (Nat.beq (Nat.xor unass ge2) 0)
  ·rw[Bool.cond_false];set ge3:=Nat.lor (Nat.land a01 o23) (Nat.land o01 a23)
   cases h2:not (Nat.beq (Nat.xor ge2 ge3) 0)
   ·rw[Bool.cond_false];cases h3:not (Nat.beq (Nat.xor ge3 (Nat.land a01 a23)) 0)
    ·exact hsub_bit (λ_ h=>h) hne
    ·rw[Bool.cond_true];exact hsub_bit (hmk λi a=>by simp[ge3,a01,a23,o01,o23,u0,u1,u2,u3,a]) (λe=>by rw[e,Nat.beq_refl]at h3;cases h3)
   ·rw[Bool.cond_true];exact hsub_bit (hmk λi a=>by simp[ge2,ge3,a01,a23,o01,o23,u0,u1,u2,u3,a]) (λe=>by rw[e,Nat.beq_refl]at h2;cases h2)
  ·exact hsub_bit (hmk λi a=>by rw[testBit_xor',a];cases b:ge2.testBit i;rfl;rw[hge2 i b]at a;cases a)
    (λe=>by rw[e,Nat.beq_refl]at hu;cases hu)
 exact⟨lt_of_testBit hlt hret,hret⟩
private lemma testBit_xor_bit {m b x:Nat} (hb:m.testBit b=true) :
  (Nat.xor m (Nat.shiftLeft 1 b)).testBit x=(m.testBit x&&decide (x≠b)):=by
 simp only[testBit_xor',shl1_tb];by_cases h:x=b;subst h;simp[hb];simp[h,Ne.symm h]
private lemma guard_le {C n:Nat} (h:or (Nat.ble 5 C) (Nat.ble 17 n)=false):C<=4/\n<=16:=by
 simp[Bool.or_eq_false_iff]at h
 exact⟨by_contra λg=>Bool.noConfusion ((Nat.ble_eq.mpr (by omega:5<=C)).symm.trans h.1),
  by_contra λg=>Bool.noConfusion ((Nat.ble_eq.mpr (by omega:17<=n)).symm.trans h.2)⟩
private lemma gatherT_spec {n C cadj active bv c aC:Nat} {reqs:List (Nat×Nat×Nat)} {col:Nat->Nat}
  (hvc:ValidColP n C cadj reqs active col) (hba:active.testBit bv=true) (hbc:col bv=c)
  (haC:∀x,aC.testBit x=true->x<n/\active.testBit x=true/\col x=c)
  {pairs:List (Nat×Nat)}
  (hp:∀p∈pairs,∃w < n,p.1=Nat.shiftLeft 1 w/\∀t,p.2.testBit t=true->(bv,w,t)∈reqs\/(w,bv,t)∈reqs) :
  ∀acc,(∀t,acc.testBit t=true->active.testBit t=true->col t<=c) ->
   ∀t,(gatherT aC pairs acc).testBit t=true->active.testBit t=true->col t<=c:=by
 induction pairs with
 | nil=>exact λ_ h=>h
 | cons p _ ih=>
  intro acc hacc;unfold gatherT;dsimp only;have hr q hq:=hp q (List.mem_cons_of_mem _ hq)
  cases h0:Nat.beq (Nat.land aC p.1) 0;swap;exact ih hr acc hacc
  rw[Bool.cond_false,forceN_eq];refine ih hr _ λt ht hta=> ?_
  rw[testBit_lor',Bool.or_eq_true]at ht;rcases ht with ha|hp2;exact hacc t ha hta
  obtain⟨w,_,hp1,hpt⟩:=hp p List.mem_cons_self
  obtain⟨_,hwa,hwc⟩:=haC w (bit_of_land_ne0 (hp1▸h0))
  rcases hpt t hp2 with hm|hm<;>have h:=(hvc.2.2.2 _ hm).2.2.2<;>[have:=h hba hwa hta (hbc.trans hwc.symm);have:=h hwa hba hta (hwc.trans hbc.symm)]<;>(dsimp at this;omega)
private lemma gatherClr_spec {n C cadj active bv k aK:Nat} {reqs:List (Nat×Nat×Nat)} {col:Nat->Nat}
  (hvc:ValidColP n C cadj reqs active col) (hba:active.testBit bv=true) (hklt:k<col bv)
  (haK:∀x,aK.testBit x=true->x<n/\active.testBit x=true/\col x=k)
  {ts:List (Nat×Nat)}
  (hts:∀p∈ts,∃v w,v<n/\w<n/\p.1=Nat.shiftLeft 1 v/\p.2=Nat.shiftLeft 1 w/\(v,w,bv)∈reqs) :
  ∀acc u,active.testBit u=true->col u=k->acc.testBit u=false ->
   (gatherClr aK ts acc).testBit u=false:=by
 intro acc u hua huk hacc;unfold gatherClr;cases Nat.beq aK 0;swap;exact hacc
 have go:∀l,(∀p∈l,∃v w,v<n/\w<n/\p.1=Nat.shiftLeft 1 v/\p.2=Nat.shiftLeft 1 w/\(v,w,bv)∈reqs) ->
   ∀m,m.testBit u=false->(gatherClrGo aK l m).testBit u=false:=λl=>by
  induction l with
  | nil=>exact λ_ _ hm=>hm
  | cons p _ ih=>
   intro hl m hm;unfold gatherClrGo;dsimp;rw[forceN_eq]
   obtain⟨v,w,_,_,hp1,hp2,hmem⟩:=hl p List.mem_cons_self
   have st m0 (hm0:m0.testBit u=false) a b (hab:(a=v/\b=w)\/(a=w/\b=v)) :
     (cond (Nat.beq (Nat.land aK (Nat.shiftLeft 1 a)) 0) m0 (Nat.lor m0 (Nat.shiftLeft 1 b))).testBit u=false:=by
    cases h:Nat.beq (Nat.land aK (Nat.shiftLeft 1 a)) 0;swap;exact hm0
    rw[Bool.cond_false,testBit_lor',hm0,Bool.false_or]
    refine Bool.eq_false_iff.mpr λht=> ?_;rw[shl1_tb,decide_eq_true_eq]at ht;subst ht
    obtain⟨_,haa,hac⟩:=haK a (bit_of_land_ne0 h)
    rcases hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>have:=(hvc.2.2.2 _ hmem).2.2.2<;>[have:=this haa hua hba (hac.trans huk.symm);have:=this hua haa hba (huk.trans hac.symm)]<;>(dsimp at this;omega)
   exact ih (λq hq=>hl q (List.mem_cons_of_mem _ hq)) _ (hp1▸hp2▸st _ (st m hm v w (Or.inl ⟨rfl,rfl⟩)) w v (Or.inr ⟨rfl,rfl⟩))
 exact go ts hts acc hacc
private lemma wipeout_ok {n C rem d0 d1 d2 d3:Nat} {col:Nat->Nat}
  (hC:C<=4) (hlt:rem<2^n) (hcol:∀x < n,rem.testBit x=true->col x<C)
  (hdok:DomOK4 n rem d0 d1 d2 d3 col) :
  Nat.beq (Nat.land (Nat.lor (Nat.lor d0 d1) (Nat.lor d2 d3)) rem) rem=true:=by
 rw[Nat.beq_eq];apply Nat.eq_of_testBit_eq;intro x;rw[testBit_land'];cases hr:rem.testBit x;· simp
 have hx:=lt_of_testBit hlt hr;have hd:=hdok x hx hr
 rcases lt4_cases (Nat.lt_of_lt_of_le (hcol x hx hr) hC)with h|h|h|h<;>simp[colMask,h]at hd ⊢<;>simp[hd]
private lemma wipeout_go {n C rem d0 d1 d2 d3:Nat} {col:Nat->Nat} {b:Bool}
  (hC:C<=4) (hlt:rem<2^n) (hcol:∀x < n,rem.testBit x=true->col x<C)
  (hd:DomOK4 n rem d0 d1 d2 d3 col) (hb:DomOK4 n rem d0 d1 d2 d3 col->b=true) :
  cond (Nat.beq (Nat.land (Nat.lor (Nat.lor d0 d1) (Nat.lor d2 d3)) rem) rem) b false=true:=by
 rw[wipeout_ok hC hlt hcol hd];exact hb hd
private lemma land_clr_tb {d cl x:Nat} (hx:x<16) (hd:d.testBit x=true) (hcl:cl.testBit x=false) :
  (Nat.land d (Nat.xor 65535 cl)).testBit x=true:=by
 rw[testBit_land',testBit_xor',hd,hcl,show(65535:Nat)=2^16-1 from rfl,Nat.testBit_two_pow_sub_one,decide_eq_true hx];rfl
private lemma solveRec4_complete {n C cadj active:Nat} {reqs:List (Nat×Nat×Nat)} {ri:ReqIdx} {col:Nat->Nat}
  (hC:C<=4) (hn:n<=16) (hvc:ValidColP n C cadj reqs active col) (hri:ReqIdxOK n reqs ri) :
  ∀fuel unass d0 d1 d2 d3 a0 a1 a2 a3,SubMask unass active ->
   DomOK4 n unass d0 d1 d2 d3 col->ValOK4 n active unass a0 a1 a2 a3 col ->
   solveRec4 fuel n C cadj ri unass d0 d1 d2 d3 a0 a1 a2 a3=true:=by
 intro f;induction f with
 | zero=>intros;rfl
 | succ f ih=>
  intro u d0 d1 d2 d3 a0 a1 a2 a3 hs hd hv;unfold solveRec4;dsimp only
  by_cases u0:u=0;· subst u0;simp
  rw[beq_false_of_ne u0,Bool.cond_false,forceN_eq]
  obtain⟨bl,bu⟩:=@pickVar4_spec cadj _ d0 d1 d2 d3 _ hn u0 (sub_lt2 hvc.1 hs)
  set b:=pickVar4 cadj u d0 d1 d2 d3 n;set bitB:=Nat.shiftLeft 1 b
  set rem:=Nat.xor u bitB;set nbRem:=Nat.land (getCadj cadj b) rem;rw[forceN_eq,forceN_eq,forceN_eq]
  have rb x:=testBit_xor_bit (x:=x) bu
  have rs:SubMask rem active:=λx hx=>hs x (by rw[rb,Bool.and_eq_true]at hx;exact hx.1)
  have tr:∀l,col b<l->l<=C ->
    tryC4 (solveRec4 f n C cadj ri) rem nbRem bitB (b16Get ri.1 b) (b16Get ri.2 b) d0 d1 d2 d3 a0 a1 a2 a3 l=true:=λl=>by
   induction l with| zero=>intro h;omega| succ c ihc=>
    intro hlt hle;unfold tryC4;dsimp only;by_cases e:c=col b
    ·subst e;have hdb:=hd b bl bu
     rw[beq_false_of_ne λh0=>by have:=congrArg (·.testBit b) h0;simp[bitB,hdb]at this,Bool.cond_false]
     suffices tryColor4 (solveRec4 f n C cadj ri) rem nbRem bitB (b16Get ri.1 b) (b16Get ri.2 b) d0 d1 d2 d3 a0 a1 a2 a3 (col b)=true by rw[this];rfl
     unfold tryColor4;dsimp only;rw[forceN_eq];have hc4:col b<4:=by omega
     have haK k (hk:k<4) x (hx:(colMask a0 a1 a2 a3 k).testBit x=true):x<n/\active.testBit x=true/\col x=k:=
      let⟨h1,h2,_,h4⟩:=(hv k hk x).mp hx;⟨h1,h2,h4⟩
     set tU:=cond (or (Nat.beq (col b) 3) (Nat.beq (colMask a0 a1 a2 a3 (col b)) 0)) 0 (gatherT (colMask a0 a1 a2 a3 (col b)) (b16Get ri.1 b) 0)
     have htU:∀t,tU.testBit t=true->active.testBit t=true->col t<=col b:=by
      dsimp only[tU];cases or (Nat.beq (col b) 3) (Nat.beq (colMask a0 a1 a2 a3 (col b)) 0)
      ·exact gatherT_spec hvc (hs b bu) rfl (haK _ hc4) (hri.1 b bl) 0 (by simp)
      ·intro _ ht;simp at ht
     have hgt0:Nat.land tU (cond (Nat.beq (col b) 0) (Nat.lor a1 (Nat.lor a2 a3))
       (cond (Nat.beq (col b) 1) (Nat.lor a2 a3) (cond (Nat.beq (col b) 2) a3 0)))=0:=
      Nat.eq_of_testBit_eq λx=>by
       rw[testBit_land',Nat.zero_testBit];cases ht:tU.testBit x;· rfl
       have hfa k (hk:k<4) (hgt:col b<k):(colMask a0 a1 a2 a3 k).testBit x=false:=
        Bool.eq_false_iff.mpr λh=>by have:=haK k hk x h;have:=htU x ht this.2.1;omega
       rcases lt4_cases hc4 with hc|hc|hc|hc
       ·simp[hc,beq_dec,testBit_lor',Bool.or_eq_false_iff];exact⟨hfa 1 (by decide) (by omega),hfa 2 (by decide) (by omega),hfa 3 (by decide) (by omega)⟩
       ·simp[hc,beq_dec,testBit_lor',Bool.or_eq_false_iff];exact⟨hfa 2 (by decide) (by omega),hfa 3 (by decide) (by omega)⟩
       ·simp[hc,beq_dec];exact hfa 3 (by decide) (by omega)
       ·simp[hc,beq_dec]
     rw[hgt0,Nat.beq_refl,Bool.not_true,Bool.cond_false];simp only[forceN_eq]
     refine wipeout_go hC (sub_lt2 hvc.1 rs) (λx hx h=>hvc.2.1 x hx (rs x h)) (λx hx hrx=> ?_) λhd'=>
      ih rem _ _ _ _ _ _ _ _ rs hd' λk hk x=>by
       rw[colMask_lor a0 a1 a2 a3 (col b) bitB k hc4 hk];split_ifs with hkc
       ·subst hkc;rw[testBit_lor',Bool.or_eq_true,shl1_tb,decide_eq_true_eq,hv _ hk x,rb]
        by_cases hbx:x=b;subst hbx;simp[bl,hs b bu,bu];simp[hbx,Ne.symm hbx]
       ·rw[hv k hk x,rb];by_cases hbx:x=b;subst hbx;simp[bu,Ne.symm hkc];simp[hbx]
     have hax:=rs x hrx;have hdx:=hd x hx (by rw[rb,Bool.and_eq_true]at hrx;exact hrx.1)
     have hnbF (he:col x=col b):nbRem.testBit x=false:=by
      rw[testBit_land',hrx,Bool.and_true];exact Bool.eq_false_iff.mpr λh=>hvc.2.2.1 b x bl hx (hs b bu) hax (by rwa[bitTest_eq]) he.symm
     have htUF (hgt:col b<col x):tU.testBit x=false:=Bool.eq_false_iff.mpr λht=>by have:=htU x ht hax;omega
     have hgc k (hk:k<4) (h1:k<col b) (h2:col x=k):=gatherClr_spec hvc (hs b bu) h1 (haK k hk) (hri.2 b bl) 0 x hax h2 (Nat.zero_testBit x)
     rcases lt4_cases (Nat.lt_of_lt_of_le (hvc.2.1 x hx hax) hC)with hx'|hx'|hx'|hx' <;>
     rcases lt4_cases hc4 with hb'|hb'|hb'|hb' <;>
     simp only[colMask,hx',hb',Nat.beq,Nat.ble,Bool.cond_true,Bool.cond_false]at hdx ⊢ <;>
     exact land_clr_tb (by omega) hdx (by first| exact hnbF (by omega)| exact htUF (by omega)| exact hgc 0 (by decide) (by omega) (by omega)| exact hgc 1 (by decide) (by omega) (by omega)| exact hgc 2 (by decide) (by omega) (by omega))
    ·have h:=ihc (by omega) (by omega);unfold tryC4 at h;rw[h]
     cases Nat.beq (Nat.land (colMask d0 d1 d2 d3 c) bitB) 0<;>cases tryColor4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _<;>rfl
  exact tr C (hvc.2.1 b bl (hs b bu)) (Nat.le_refl C)
theorem canSolvePI_complete {n C cadj active:Nat} {reqs:List (Nat×Nat×Nat)} {ri:ReqIdx} {col:Nat->Nat}
  (hvc:ValidColP n C cadj reqs active col) (hri:ReqIdxOK n reqs ri) :
  canSolvePI n C cadj ri active=true:=by
 unfold canSolvePI;cases g:or (Nat.ble 5 C) (Nat.ble 17 n);swap;rfl
 rw[Bool.cond_false];obtain⟨h4,h16⟩:=guard_le g
 by_cases c0:C=0
 ·subst c0;simp[show active=0 from Nat.eq_of_testBit_eq λk=>by
   rw[Nat.zero_testBit];by_cases hk:k<n
   cases a:active.testBit k;rfl;have:=hvc.2.1 k hk a;omega
   exact testBit_eq_false_of_lt_pow hvc.1 (Nat.le_of_not_lt hk)]
 rw[beq_false_of_ne c0,Bool.cond_false];by_cases c1:C=1
 ·subst c1;simp[Nat.beq_refl,Bool.cond_true]
  have no:∀m≤n,noEdgeP cadj active m=true:=λm=>by
   induction m with| zero=>exact λ_=>rfl| succ v ih=>
    intro hm;unfold noEdgeP;dsimp
    cases b:and (bitTest active v) (not (Nat.beq (Nat.land (getCadj cadj v) active) 0));· exact ih (by omega)
    simp only[Bool.and_eq_true,Bool.not_eq_true',bitTest_eq]at b
    obtain⟨w,hw⟩:=exists_testBit_of_ne_zero (m:=Nat.land (getCadj cadj v) active) λe=>by rw[e]at b;cases b.2
    simp at hw;have wl:=lt_of_testBit hvc.1 hw.2
    have:=hvc.2.2.1 v w (by omega) wl b.1 hw.2 (by rw[bitTest_eq];exact hw.1)
    have:=hvc.2.1 v (by omega) b.1;have:=hvc.2.1 w wl hw.2;omega
  exact no n (Nat.le_refl n)
 rw[beq_false_of_ne c1,Bool.cond_false,forceN_eq,forceN_eq]
 refine solveRec4_complete h4 h16 hvc hri (Nat.add n 1) active _ _ _ _ 0 0 0 0 (λ_ h=>h) (λx hx hax=> ?_) (λc hc x=> ?_)
 ·have:=hvc.2.1 x hx hax
  rcases lt4_cases (by omega:col x<4)with h|h|h|h<;>simp[colMask,h,Nat.beq,hax]<;>(split_ifs<;>first| exact hax| omega)
 ·rcases lt4_cases hc with rfl|rfl|rfl|rfl<;>(simp[colMask,Nat.beq];intro _ h1 h2;rw[h1]at h2;cases h2)
theorem canMergePI_complete {n C cadj active ii jj:Nat} {reqs:List (Nat×Nat×Nat)} {ri:ReqIdx} {col:Nat->Nat}
  (hvc:ValidColP n C cadj reqs active col) (hri:ReqIdxOK n reqs ri)
  (hi_lt:ii<n) (hj_lt:jj<n) (hne:ii≠jj)
  (hi_a:active.testBit ii=true) (hj_a:active.testBit jj=true) (heq:col ii=col jj) :
  canMergePI n C cadj ri active ii jj=true:=by
 unfold canMergePI;cases g:or (Nat.ble 5 C) (Nat.ble 17 n);swap;rfl
 rw[Bool.cond_false];obtain⟨h4,h16⟩:=guard_le g;have ci:=hvc.2.1 ii hi_lt hi_a
 have ne:bitTest (getCadj cadj ii) jj=false:=Bool.eq_false_iff.mpr λh=>hvc.2.2.1 ii jj hi_lt hj_lt hi_a hj_a h heq
 rw[beq_false_of_ne (by omega:C≠0),ne,Bool.or_false,Bool.cond_false];simp only[forceN_eq]
 set bitI:=Nat.shiftLeft 1 ii;set bitJ:=Nat.shiftLeft 1 jj;set bitIJ:=Nat.lor bitI bitJ
 set rm:=Nat.xor active bitIJ;set nb:=Nat.lor (getCadj cadj ii) (getCadj cadj jj)
 set nbRem:=Nat.land nb rm;set tU:=gatherT bitJ (b16Get ri.1 ii) 0
 set d1:=cond (Nat.ble 2 C) rm 0;set d2:=cond (Nat.ble 3 C) rm 0;set d3:=cond (Nat.ble 4 C) rm 0
 have rb (x:Nat):rm.testBit x=(active.testBit x&&decide (x≠ii)&&decide (x≠jj)):=by
  simp only[rm,bitIJ,bitI,bitJ,testBit_xor',testBit_lor',shl1_tb]
  by_cases hxi:x=ii;subst hxi;simp[hi_a];by_cases hxj:x=jj;subst hxj;simp[hj_a,hne.symm];simp[hxi,hxj,Ne.symm hxi,Ne.symm hxj]
 have rs:SubMask rm active:=λx hx=>by rw[rb,Bool.and_eq_true,Bool.and_eq_true]at hx;exact hx.1.1
 have htU:∀t,tU.testBit t=true->active.testBit t=true->col t<=col ii:=
  gatherT_spec hvc hi_a rfl (λx hx=>by dsimp only[bitJ]at hx;rw[shl1_tb,decide_eq_true_eq]at hx;subst hx;exact⟨hj_lt,hj_a,heq.symm⟩) (hri.1 ii hi_lt) 0 (by simp)
 have lp:∀l,col ii<l->l<=C->canMergeLoop4 n C cadj ri rm nbRem bitIJ tU rm d1 d2 d3 l=true:=λl=>by
  induction l with| zero=>intro h;omega| succ c ih=>
   intro hlt hle;unfold canMergeLoop4;dsimp only;by_cases e:c=col ii
   ·subst e;simp only[forceN_eq];have hc4:col ii<4:=by omega
    refine(λ{a b:Bool} (h:a=true)=>by rw[h];rfl:∀{a b:Bool},a=true->cond a true b=true) ?_
    refine wipeout_go h4 (sub_lt2 hvc.1 rs) (λx hx h=>hvc.2.1 x hx (rs x h)) (λx hx hrx=> ?_) λhd'=>
     solveRec4_complete h4 h16 hvc hri (Nat.add n 1) rm _ _ _ _ _ _ _ _ rs hd' λk hk x=>by
      rw[colMask_upd 0 0 0 0 (col ii) bitIJ k hc4 hk,show colMask 0 0 0 0 k=0 by rcases lt4_cases hk with rfl|rfl|rfl|rfl<;>rfl]
      split_ifs with hkc
      ·subst hkc;simp only[bitIJ,bitI,bitJ,testBit_lor',shl1_tb,Bool.or_eq_true,decide_eq_true_eq,rb]
       by_cases hxi:x=ii;subst hxi;simp[hi_lt,hi_a]
       by_cases hxj:x=jj;subst hxj;simp[hj_lt,hj_a,heq]
       simp[hxi,hxj,Ne.symm hxi,Ne.symm hxj];intro _ ha hna _;rw[ha]at hna;cases hna
      ·simp only[Nat.zero_testBit,Bool.false_eq_true,false_iff];rintro⟨_,ha,hr,hcx⟩;rw[rb]at hr
       by_cases hxi:x=ii;subst hxi;exact hkc hcx.symm
       by_cases hxj:x=jj;subst hxj;exact hkc (heq.trans hcx).symm;simp[ha,hxi,hxj]at hr
    have hax:=rs x hrx;have hcx:=hvc.2.1 x hx hax
    have hnbF (heq':col x=col ii):nbRem.testBit x=false:=by
     rw[testBit_land',hrx,Bool.and_true,testBit_lor',Bool.or_eq_false_iff]
     exact⟨Bool.eq_false_iff.mpr λh=>hvc.2.2.1 ii x hi_lt hx hi_a hax (by rwa[bitTest_eq]) heq'.symm,
        Bool.eq_false_iff.mpr λh=>hvc.2.2.1 jj x hj_lt hx hj_a hax (by rwa[bitTest_eq]) (heq.symm.trans heq'.symm)⟩
    have htUF (hgt:col ii<col x):tU.testBit x=false:=Bool.eq_false_iff.mpr λht=>by have:=htU x ht hax;omega
    rcases lt4_cases (by omega:col x<4)with hx'|hx'|hx'|hx' <;>
    rcases lt4_cases hc4 with hb'|hb'|hb'|hb' <;>
    simp only[colMask,hx',hb',Nat.beq,Nat.ble,Bool.cond_true,Bool.cond_false] <;>
    exact land_clr_tb (by omega)
     (by first| exact hrx| (dsimp only[d1,d2,d3];rw[Nat.ble_eq.mpr (by omega)];exact hrx))
     (by first| exact Nat.zero_testBit x| exact hnbF (by omega)| exact htUF (by omega))
   ·have hih:=ih (by omega) (by omega);unfold canMergeLoop4 at hih;rw[forceN_eq,forceN_eq,forceN_eq,forceN_eq,hih]
    cases cond _ _ false<;>rfl
 exact lp C ci (Nat.le_refl C)
private lemma law_to_validColP {nv goal C cadj active:Nat} {ws:List Nat}
   {reqs:List (Nat×Nat×Nat)} {A:Finset Nat} {f:Nat->Nat}
   (hws16:ws.length<=16) (hcadj:GoodCadj nv goal ws cadj) (hreqs:GoodReqs nv goal ws reqs)
   (hact:active<2^ws.length) (hA:∀i < ws.length,active.testBit i=true->listGetN ws i∈A)
   (hbnd:∀v∈A,f v<C) (hlaw:signedOrderLawOnNv nv A ws.toFinset goal f) :
   ValidColP ws.length C cadj reqs active (λi=>f (listGetN ws i)):=
 ⟨hact,λv hv hva=>hbnd _ (hA v hv hva),
  λv w hv hw hva hwa hce=>(hcadj v w (by omega) (by omega) hce).2.2.2 A f hlaw (hA v hv hva) (hA w hw hwa),
  λr hr=>let⟨h1,h2,h3,_,hlawR⟩:=hreqs r hr
    ⟨h1,h2,h3,λha1 ha2 ha3 hfeq=>hlawR A f hlaw (hA _ h1 ha1) (hA _ h2 ha2) (hA _ h3 ha3) hfeq⟩⟩
private lemma allV_lt (n:Nat):Nat.sub (Nat.shiftLeft 1 n) 1<2^n:=by
 rw[shiftLeft_one_eq];change 2^n-1<2^n;exact Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos
private lemma allV_testBit (n i:Nat):(Nat.sub (Nat.shiftLeft 1 n) 1).testBit i=decide (i<n):=by
 rw[shiftLeft_one_eq];change (2^n-1).testBit i=decide (i<n);exact Nat.testBit_two_pow_sub_one n i
private lemma xor_allV_lt {n i:Nat} (hi:i<n) :
  Nat.xor (Nat.sub (Nat.shiftLeft 1 n) 1) (Nat.shiftLeft 1 i)<2^n:=
 lt_two_pow_of_testBit λr hr=>by
  rw[testBit_xor',allV_testBit,decide_eq_false (by omega),shiftLeft_one_eq,Nat.testBit_two_pow,decide_eq_false (by omega)];rfl
private lemma listGetN_inj_of_nodup {ws:List Nat} (hnd:ws.Nodup) {i j:Nat}
  (hi:i<ws.length) (hj:j<ws.length) (heq:listGetN ws i=listGetN ws j):i=j:=by
 rw[listGetN_getElem hi,listGetN_getElem hj]at heq;exact(List.Nodup.getElem_inj_iff hnd).mp heq
def childSet(ws:List Nat)(ii jj z:Nat)(ka kb:Bool):Finset Nat:=
 insert z
  (if ka then(if kb then ws.toFinset else ws.toFinset.erase (listGetN ws jj))
   else(if kb then ws.toFinset.erase (listGetN ws ii)
    else(ws.toFinset.erase (listGetN ws ii)).erase (listGetN ws jj)))
theorem canSolvePI_sound {nv goal cap cadj:Nat} {ws:List Nat} {reqs:List (Nat×Nat×Nat)} {ri:ReqIdx}
  (hnd:ws.Nodup) (hws16:ws.length<=16) (hcadj:GoodCadj nv goal ws cadj) (hreqs:GoodReqs nv goal ws reqs)
  (hri:ReqIdxOK ws.length reqs ri)
  (hfalse:canSolvePI ws.length (cap+2-ws.length) cadj ri (Nat.sub (Nat.shiftLeft 1 ws.length) 1)=false) :
  ImpossibleNv nv goal cap ws.toFinset:=λ_ _ h=>by
 obtain⟨f,b,l⟩:=signed_order_live_nv h;have:=List.toFinset_card_of_nodup hnd
 exact Bool.noConfusion ((canSolvePI_complete (law_to_validColP hws16 hcadj hreqs (allV_lt ws.length)
  (λi q _=>List.mem_toFinset.mpr (listGetN_mem q)) (λv m=>by have:=b v m;omega) l) hri).symm.trans hfalse)
theorem mkReqIdx_of_goodReqs {nv goal:Nat} {ws:List Nat} {reqs:List (Nat×Nat×Nat)}
  (hws16:ws.length<=16) (hreqs:GoodReqs nv goal ws reqs):ReqIdxOK ws.length reqs (mkReqIdx reqs):=
 mkReqIdx_ok hws16 reqs λr hr=>let⟨h1,h2,h3,_⟩:=hreqs r hr;⟨h1,h2,h3⟩
theorem pord_child_00_soundI {nv goal kChild cadj ii jj op:Nat} {ws:List Nat} {reqs:List (Nat×Nat×Nat)} {ri:ReqIdx}
  (hnd:ws.Nodup) (hws16:ws.length<=16) (hcadj:GoodCadj nv goal ws cadj) (hreqs:GoodReqs nv goal ws reqs)
  (hri:ReqIdxOK ws.length reqs ri)
  (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hop:op<4)
  (hfresh:zN op (listGetN ws ii) (listGetN ws jj)∉ws.toFinset)
  (hkill:bitTest (getCadj cadj ii) jj=true \/
   canMergePI ws.length (kChild+3-ws.length) cadj ri (Nat.sub (Nat.shiftLeft 1 ws.length) 1) ii jj=false) :
  ImpossibleNv nv goal kChild (childSet ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) false false):=λ_ _ h=>by
 have a:=List.mem_toFinset.mpr (listGetN_mem hi);have b:=List.mem_toFinset.mpr (listGetN_mem hj)
 obtain⟨f,fb,e,l⟩:=order_step_00_nv hop a b (λe=>hne (listGetN_inj_of_nodup hnd hi hj e)) hfresh (by simpa[childSet]using h)
 rcases hkill with hedge|hfalse
 ·exact(hcadj ii jj (by omega) (by omega) hedge).2.2.2 ws.toFinset f l a b e
 ·have:=List.toFinset_card_of_nodup hnd
  exact Bool.noConfusion ((canMergePI_complete (law_to_validColP hws16 hcadj hreqs (allV_lt ws.length)
   (λi q _=>List.mem_toFinset.mpr (listGetN_mem q)) (λv m=>by have:=fb v m;omega) l) hri hi hj hne
   (by rw[allV_testBit,decide_eq_true hi]) (by rw[allV_testBit,decide_eq_true hj]) e).symm.trans hfalse)
theorem pord_child_keep_soundI {nv goal kChild cadj ii jj op:Nat} {ws:List Nat} {reqs:List (Nat×Nat×Nat)} {ri:ReqIdx}
  {ka kb:Bool} (hnd:ws.Nodup) (hws16:ws.length<=16) (hcadj:GoodCadj nv goal ws cadj) (hreqs:GoodReqs nv goal ws reqs)
  (hri:ReqIdxOK ws.length reqs ri)
  (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hop:op<4) (hkeep:ka=true\/kb=true)
  (hfresh:zN op (listGetN ws ii) (listGetN ws jj)∉ws.toFinset)
  (hfalse:canSolvePI ws.length (kChild+(if ka&&kb then 1 else 2)-ws.length) cadj ri
   (cond ka (cond kb (Nat.xor (Nat.xor (Nat.sub (Nat.shiftLeft 1 ws.length) 1) (Nat.shiftLeft 1 ii)) (Nat.shiftLeft 1 jj))
    (Nat.xor (Nat.sub (Nat.shiftLeft 1 ws.length) 1) (Nat.shiftLeft 1 ii)))
    (Nat.xor (Nat.sub (Nat.shiftLeft 1 ws.length) 1) (Nat.shiftLeft 1 jj)))=false) :
  ImpossibleNv nv goal kChild (childSet ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) ka kb):=by
 have hk {A:Finset Nat} {C act:Nat} {f:Nat->Nat} (ha:act<2^ws.length)
   (hA:∀i < ws.length,act.testBit i=true->listGetN ws i∈A) (hb:∀v∈A,f v<C)
   (hl:signedOrderLawOnNv nv A ws.toFinset goal f) (hf:canSolvePI ws.length C cadj ri act=false):False:=
  Bool.noConfusion ((canSolvePI_complete (law_to_validColP hws16 hcadj hreqs ha hA hb hl) hri).symm.trans hf)
 have hin {a} (ha:a<ws.length):=List.mem_toFinset.mpr (listGetN_mem ha)
 have h10 {a b o} (ha:a<ws.length) (hb:b<ws.length) (hab:a≠b) (ho:o<4)
   (hf:zN o (listGetN ws a) (listGetN ws b)∉ws.toFinset)
   (hfl:canSolvePI ws.length (kChild+2-ws.length) cadj ri (Nat.xor (Nat.sub (Nat.shiftLeft 1 ws.length) 1) (Nat.shiftLeft 1 a))=false) :
   ImpossibleNv nv goal kChild (insert (zN o (listGetN ws a) (listGetN ws b)) (ws.toFinset.erase (listGetN ws b))):=λ_ _ h=>by
  obtain⟨f,fb,l⟩:=order_step_10_nv ho (hin ha) (hin hb) (λe=>hab (listGetN_inj_of_nodup hnd ha hb e)) hf h
  have:=List.toFinset_card_of_nodup hnd
  exact hk (xor_allV_lt ha) (λi q c=>by
   rw[testBit_xor',allV_testBit,decide_eq_true q,shl1_tb]at c
   exact Finset.mem_erase.mpr ⟨λe=>by have:=listGetN_inj_of_nodup hnd q ha e;subst this;simp at c,hin q⟩)
   (λv m=>by have:=fb v m;omega) l hfl
 cases ka<;>cases kb
 ·simp at hkeep
 ·simp[childSet,Bool.false_eq_true,ite_false,ite_true,Bool.false_and,Bool.cond_false]at hfalse ⊢
  rw[zN_flip hop]at hfresh ⊢;exact h10 hj hi hne.symm (flip_flip hop).1 hfresh hfalse
 ·simp only[childSet,Bool.false_eq_true,ite_false,ite_true,Bool.and_false,Bool.cond_true,Bool.cond_false]at hfalse ⊢
  exact h10 hi hj hne hop hfresh hfalse
 ·simp only[childSet,ite_true,Bool.and_self,Bool.cond_true]at hfalse ⊢;intro _ _ h
  obtain⟨f,fb,l⟩:=order_step_11_nv hop (hin hi) (hin hj) (λe=>hne (listGetN_inj_of_nodup hnd hi hj e)) hfresh h
  have:=List.toFinset_card_of_nodup hnd
  exact hk (lt_two_pow_of_testBit λr hr=>by rw[testBit_xor',testBit_eq_false_of_lt_pow (xor_allV_lt hi) hr,shl1_tb,decide_eq_false (by omega)];rfl)
   (λi q c=>by
    rw[testBit_xor',testBit_xor',allV_testBit,decide_eq_true q,shl1_tb,shl1_tb]at c
    exact Finset.mem_erase.mpr ⟨λe=>by
     have:=listGetN_inj_of_nodup hnd q hj e;subst this;simp at c;exact hne c,
     Finset.mem_erase.mpr ⟨λe=>by have:=listGetN_inj_of_nodup hnd q hi e;subst this;simp at c;exact hne c.symm,hin q⟩⟩)
   (λv m=>by have:=fb v m;omega) l hfalse
abbrev QS01:=Nat×Nat×Nat×Nat×Nat×Nat×List Nat
abbrev QS01D:=Nat×Nat×Nat×Nat×Nat×Nat×List Nat
abbrev QS11:=Nat×Bool×Nat×List Nat
abbrev QNoZFast:=Bool×Bool×Nat×Nat
abbrev ColPrepD:=Nat×Nat×List Nat
def emptyQNoZ:QNoZFast:=(false,false,65535,0)
def bloomIdx(x:Nat):Nat:=
 Nat.mod (Nat.sub (Nat.add (Nat.mod x 257) 257) (Nat.mod (Nat.land x 0xffffffff) 257)) 257
noncomputable def mkBloom(dD:Nat)(pmD:List Nat):Nat:=
 @List.rec Nat (λ_=>Nat) 0
  (λmD _ ih=>Nat.lor ih (Nat.lor (Nat.shiftLeft 1 (bloomIdx mD)) (Nat.shiftLeft 1 (bloomIdx (Nat.xor dD mD))))) pmD
noncomputable def addG1(cM notCM:Nat)(n acc:Nat):Nat:=
 @Nat.rec (λ_=>Nat->Nat) (λa=>a)
  (λi ih a=>cond (bitTest cM i) (forceN (Nat.lor a (Nat.shiftLeft notCM (Nat.mul i 16))) λa'=>ih a') (ih a))
  n acc
noncomputable def detList{β:Type}(l:List Nat)(k:List Nat->β):β:=
 @List.rec Nat (λ_=>(List Nat->β)->β) (λc=>c [])
  (λx _ ih c=>mkDet x λxd=>ih λr=>c (xd::r)) l k
theorem detList_eq{β:Type}(l:List Nat)(k:List Nat->β):detList l k=k (l.map detVal):=by
 induction l generalizing k with| nil=>rfl| cons x _ ih=>unfold detList;dsimp;rw[mkDet_eq];exact ih _
theorem selectLive_map(m:Nat)(f:Nat->Nat)(l:List Nat):
  selectLive m (l.map f)=(selectLive m l).map f:=by
 induction l generalizing m with
 | nil=>rfl
 | cons a _ ih=>simp only[selectLive,List.map_cons];cases Nat.beq (Nat.land m 1) 1<;>simp[ih]
noncomputable def subcubeD{β:Type}(loDB hiDB:B16 Nat)(nv zM oM:Nat)(k:Nat->β):β:=
 mkDet (maskC nv) λinit=>
 @Nat.rec (λ_=>Nat->β) (λa=>detS a k)
  (λu ih a=>
   cond (not (Nat.beq (Nat.land zM (Nat.shiftLeft 1 u)) 0))
    (forceN (Nat.land a (b16Get loDB u)) λa'=>ih a')
    (cond (not (Nat.beq (Nat.land oM (Nat.shiftLeft 1 u)) 0))
     (forceN (Nat.land a (b16Get hiDB u)) λa'=>ih a') (ih a)))
  nv init
noncomputable def mkPm0D{β:Type}(hiDB:B16 Nat)(nv dD fixM:Nat)(k:List Nat->β):β:=
 @Nat.rec (λ_=>List Nat->β) (λacc=>k acc)
  (λu ih acc=>
   cond (not (Nat.beq (Nat.land fixM (Nat.shiftLeft 1 u)) 0)) (ih acc)
    (forceN (Nat.land (b16Get hiDB u) dD) λraw=>detS raw λmD=>ih (mD::acc)))
  nv []
noncomputable def prepColsD {β:Type} (loDB hiDB:B16 Nat) (nv n:Nat) (cols:List (Nat×Nat×Nat))
  (k:List ColPrepD->β):β:=
 @Nat.rec (λ_=>List (Nat×Nat×Nat)->(List ColPrepD->β)->β) (λ_ c=>c [])
  (λ_ ih cs c=>
   match cs with
   | []=>c []
   | (zM,oM,lb)::rest=>
    forceN zM λzM'=>forceN oM λoM'=>forceN lb λlb'=>
    forceN (Nat.lor zM' oM') λfixM=>
    subcubeD loDB hiDB nv zM' oM' λdD=>
    mkPm0D hiDB nv dD fixM λpm0D=>
    ih rest λr=>c ((lb',dD,pm0D)::r))
  n cols k
noncomputable def scanMasksD0 {β:Type} (dD:Nat) (pmD wsD:List Nat) (idx c0 cM uM:Nat)
  (k:Nat->Nat->Nat->β):β:=
 @List.rec Nat (λ_=>Nat->Nat->Nat->Nat->β) (λ_ a b e=>k a b e)
  (λwD _ ih i c0' cM' uM'=>
   forceN (Nat.land wD dD) λraw=>
   cond (or (isZeroS raw) (eqS dD raw))
    (forceN (Nat.add c0' 1) λnc0=>forceN (Nat.lor cM' (Nat.shiftLeft 1 i)) λncM=>ih (Nat.add i 1) nc0 ncM uM')
    (detS raw λmD=>
     cond (navailNonConstD dD pmD mD) (ih (Nat.add i 1) c0' cM' uM')
      (forceN (Nat.lor uM' (Nat.shiftLeft 1 i)) λnuM=>ih (Nat.add i 1) c0' cM' nuM)))
  wsD idx c0 cM uM
noncomputable def buildPoolD {β:Type} (dD:Nat) (gates:List (Nat×Nat×Nat)) (paidMask:Nat)
  (bankD:List Nat) (gIdx:Nat) (pmD:List Nat) (paid:Nat) (k:List Nat->Nat->β):β:=
 @List.rec (Nat×Nat×Nat) (λ_=>Nat->Nat->List Nat->Nat->β) (λ_ _ pm pd=>k pm pd)
  (λg _ ih pM gi pm pd=>
   let a:=g.2.1;let b:=g.2.2
   cond (Nat.beq (Nat.land pM 1) 0) (ih (Nat.shiftRight pM 1) (Nat.add gi 1) pm pd)
    (cond (and (Nat.ble (Nat.add a 1) gi) (Nat.ble (Nat.add b 1) gi))
     (forceN (Nat.land (listGetN bankD gi) dD) λrawZ=>
      cond (or (isZeroS rawZ) (eqS dD rawZ)) (ih (Nat.shiftRight pM 1) (Nat.add gi 1) pm pd)
       (detS rawZ λmz=>
        cond (navailNonConstD dD pm mz) (ih (Nat.shiftRight pM 1) (Nat.add gi 1) pm pd)
         (forceN (Nat.land (listGetN bankD a) dD) λrawA=>
          cond (or (or (isZeroS rawA) (eqS dD rawA)) (detS rawA λma=>navailNonConstD dD pm ma))
           (forceN (Nat.land (listGetN bankD b) dD) λrawB=>
            cond (or (or (isZeroS rawB) (eqS dD rawB)) (detS rawB λmb=>navailNonConstD dD pm mb))
             (ih (Nat.shiftRight pM 1) (Nat.add gi 1) (mz::pm) (Nat.add pd 1))
             (ih (Nat.shiftRight pM 1) (Nat.add gi 1) pm pd))
           (ih (Nat.shiftRight pM 1) (Nat.add gi 1) pm pd))))
     (ih (Nat.shiftRight pM 1) (Nat.add gi 1) pm pd)))
  gates paidMask gIdx pmD paid
noncomputable def addQSS {β:Type} (allV dD lb lo c0 cM uM:Nat) (pmD:List Nat)
  (qps:List QS01D) (qnoZ:QNoZFast) (q11:List QS11) (k11:Nat)
  (k:List QS01D->QNoZFast->List QS11->Nat->β):β:=
 forceN (Nat.add lb c0) λhi=>
 cond (Nat.ble lo hi)
  (forceB (Nat.beq uM 0) λisAv=>
   forceB (Nat.ble (Nat.succ lo) hi) λhasSlack=>
   forceB (or isAv (Nat.ble (popcnt16 uM) 2)) λneedQps=>
   forceN (cond (and hasSlack needQps) (mkBloom dD pmD) 0) λbl=>
   let qps':=cond needQps ((dD,hi,lo,cM,uM,bl,pmD)::qps) qps
   cond isAv
    (let(kAll,k01,g2I,g1K):=qnoZ
     let q11':=(dD,not hasSlack,bl,pmD)::q11
     cond (Nat.ble (Nat.add lo 2) hi)
      (cond (Nat.ble (Nat.add lo 3) hi)
       (k qps' (true,true,g2I,g1K) q11' allV)
       (forceN (Nat.land g2I cM) λg2I'=>k qps' (kAll,true,g2I',g1K) q11' allV))
      (cond hasSlack
       (forceN (Nat.xor 65535 (Nat.land cM 65535)) λnotCM=>
        forceN (addG1 cM notCM 16 g1K) λg1K'=>
        forceN (Nat.lor k11 cM) λk11'=>
        k qps' (kAll,k01,g2I,g1K') q11' k11')
       (k qps' qnoZ q11' k11)))
    (k qps' qnoZ q11 k11))
  (k qps qnoZ q11 k11)
noncomputable def scanAutoTierD {β:Type} (nv kChild allV fullM autoCnt:Nat) (gates:List (Nat×Nat×Nat))
  (bankD wsD:List Nat) (prepped:List ColPrepD)
  (qps0:List QS01D) (qnoZ0:QNoZFast) (q110:List QS11) (k110:Nat)
  (k:List QS01D->QNoZFast->List QS11->Nat->β):β:=
 @Nat.rec (λ_=>List ColPrepD->List QS01D->QNoZFast->List QS11->Nat->β)
  (λ_ q qn q1 k1=>k q qn q1 k1)
  (λ_ ih cs q qn q1 k1=>
   match cs with
   | []=>k q qn q1 k1
   | (lb,dD,pm0D)::rest=>
    scanMasksD0 dD pm0D wsD 0 0 0 0 λc0 cM uM=>
    addQSS allV dD lb kChild c0 cM uM pm0D q qn q1 k1 λq' qn' q1' k1'=>
    cond (and (not (Nat.beq uM 0)) (Nat.ble (Nat.add kChild 1) (Nat.add lb c0)))
     (buildPoolD dD gates fullM bankD nv pm0D 0 λpmF pdF=>
      cond (Nat.beq pdF 0) (ih rest q' qn' q1' k1')
       (scanMasksD0 dD pmF wsD 0 0 0 0 λc0F cMF uMF=>
        forceN (Nat.add kChild pdF) λloF=>
        addQSS allV dD lb loF c0F cMF uMF pmF q' qn' q1' k1' λq'' qn'' q1'' k1''=>
        ih rest q'' qn'' q1'' k1''))
     (ih rest q' qn' q1' k1'))
  autoCnt prepped qps0 qnoZ0 q110 k110
noncomputable def buildExpHintsDGo {β:Type} (loDB hiDB:B16 Nat) (cols:Array (Nat×Nat×Nat))
  (nv kChild allV:Nat) (gates:List (Nat×Nat×Nat)) (bankD wsD:List Nat)
  (hsExp:List (Nat×Nat)) (q0:List QS01D) (qn0:QNoZFast) (q10:List QS11) (k10:Nat)
  (k:List QS01D->QNoZFast->List QS11->Nat->β):β:=
 @List.rec (Nat×Nat) (λ_=>List QS01D->QNoZFast->List QS11->Nat->β)
  (λq qn q1 k1=>k q qn q1 k1)
  (λh _ ih q qn q1 k1=>
   cond (Nat.ble (Nat.add h.1 1) cols.size)
    (match cols.getD h.1 (0,0,0)with
     | (zM,oM,lb)=>
      forceN zM λzM'=>forceN oM λoM'=>forceN lb λlb'=>
      forceN (Nat.lor zM' oM') λfixM=>
      subcubeD loDB hiDB nv zM' oM' λdD=>
      mkPm0D hiDB nv dD fixM λpm0D=>
      buildPoolD dD gates h.2 bankD nv pm0D 0 λpm paid=>
      scanMasksD0 dD pm wsD 0 0 0 0 λc0 cM uM=>
      forceN (Nat.add kChild paid) λlo=>
      addQSS allV dD lb' lo c0 cM uM pm q qn q1 k1 λq' qn' q1' k1'=>
      ih q' qn' q1' k1')
    (ih q qn q1 k1))
  hsExp q0 qn0 q10 k10
def checkNoZFast(ii jj bitIJ:Nat)(ka kb:Bool)(qn:QNoZFast):Bool:=
 let(kAll,k01,g2I,g1K):=qn
 cond kAll true
  (cond (or ka kb)
   (cond k01 true (cond ka (bitTest (getCadj g1K ii) jj) (bitTest (getCadj g1K jj) ii)))
   (and k01 (not (Nat.beq (Nat.land g2I bitIJ) bitIJ))))
noncomputable def checkWithZListD2(zD bitI bitJ keepM:Nat)(ka kb:Bool)(l:List QS01D):Bool:=
 @List.rec QS01D (λ_=>Bool) false
  (λq _ ih=>
   let dD:=q.1;let hiBase:=q.2.1;let lo:=q.2.2.1
   let cM:=q.2.2.2.1;let uM:=q.2.2.2.2.1;let bl:=q.2.2.2.2.2.1;let pmD:=q.2.2.2.2.2.2
   cond (Nat.beq (Nat.land uM keepM) 0)
    (let lossI:=cond ka 0 (cond (Nat.beq (Nat.land cM bitI) 0) 0 1)
     let lossJ:=cond kb 0 (cond (Nat.beq (Nat.land cM bitJ) 0) 0 1)
     let hi:=Nat.sub (Nat.sub hiBase lossI) lossJ
     cond (Nat.ble lo hi)
      (forceN (Nat.land zD dD) λraw=>
       cond (or (isZeroS raw) (eqS dD raw)) true
        (cond (Nat.ble (Nat.succ lo) hi)
         (cond (bitTest bl (bloomIdx raw))
          (detS raw λmzD=>cond (navailNonConstD dD pmD mzD) true ih) ih)
         ih))
      ih)
    ih)
  l
noncomputable def fastCost11ListD2(zD:Nat)(l:List QS11):Bool:=
 @List.rec QS11 (λ_=>Bool) false
  (λq _ ih=>
   let dD:=q.1;let isTight:=q.2.1;let bl:=q.2.2.1;let pmD:=q.2.2.2
   forceN (Nat.land zD dD) λraw=>
   cond (or (isZeroS raw) (eqS dD raw)) true
    (cond isTight ih
     (cond (bitTest bl (bloomIdx raw))
      (detS raw λmzD=>cond (navailNonConstD dD pmD mzD) true ih) ih)))
  l
def autoCount(autoTier:Nat):Nat:=
 cond (Nat.beq autoTier 0) 0 (cond (Nat.beq autoTier 1) 8 (cond (Nat.beq autoTier 2) 32 96))
def ColsSound(nv goal:Nat)(cols:Array (Nat×Nat×Nat)):Prop:=
 ∀(i:Nat)(hi:i<cols.size),ColLowerBound nv goal (cols[i]'hi).1 (cols[i]'hi).2.1 (cols[i]'hi).2.2
def ValidQS(nv goal kChild:Nat)(ws:List Nat)(q:QS01):Prop:=
 let(d,lb,lo,c0,cM,uM,pm):=q
 lb+c0<lo \/
 ∃(f:RowNv nv->RowNv nv)(roots:List (Wire (RowNv nv)))(p:Nat)
   (curBank:List (Wire (RowNv nv))),
  lo=kChild+p/\Reach roots p curBank/\¬Constant (restrictRows f (observeNv nv goal)) /\
  (∀q' out,Reach roots q' out->Available out (restrictRows f (observeNv nv goal))->lb<=q') /\
  (∀r,d.testBit (f r).1=true)/\(∀m∈pm,Available curBank (restrictRows f (observeNv nv m))) /\
  c0=(List.range ws.length).countP (λidx=>nconst d (Nat.land (listGetN ws idx) d)) /\
  (∀idx,cM.testBit idx=true↔idx<ws.length/\nconst d (Nat.land (listGetN ws idx) d)=true) /\
  (∀idx < ws.length,uM.testBit idx=false->navail d pm (Nat.land (listGetN ws idx) d)=true)
def ValidQSD(nv goal kChild:Nat)(ws:List Nat)(q:QS01D):Prop:=
 let(dD,hiBase,lo,cM,uM,_,pmD):=q
 ∃d lb c0 pm,dD=detVal d/\hiBase=lb+c0/\pmD=pm.map detVal /\
  ValidQS nv goal kChild ws (d,lb,lo,c0,cM,uM,pm)
def QNoZFastOK(nv goal kChild:Nat)(ws:List Nat)(qn:QNoZFast):Prop:=
 let(kAll,k01,g2I,g1K):=qn
 (kAll=true->∃d lb lo c0 cM pm,ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo+3<=lb+c0) /\
 (k01=true->∃d lb lo c0 cM pm,ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo+2<=lb+c0) /\
 (∀i < ws.length,g2I.testBit i=false ->
  ∃d lb lo c0 cM pm,ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo+2<=lb+c0/\cM.testBit i=false) /\
 (∀i < ws.length,∀j < ws.length,bitTest (getCadj g1K i) j=true ->
  ∃d lb lo c0 cM pm,ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo+1<=lb+c0/\cM.testBit i=true/\cM.testBit j=false)
def QSBufOK (nv goal kChild:Nat) (ws:List Nat)
  (qps:List QS01D) (qnoZ:QNoZFast) (q11:List QS11) (k11:Nat):Prop:=
 (∀q∈qps,ValidQSD nv goal kChild ws q)/\QNoZFastOK nv goal kChild ws qnoZ /\
 (∀q∈q11,∃d lb lo c0 cM pm,q.1=detVal d/\q.2.2.2=pm.map detVal /\
  ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo<=lb+c0/\(q.2.1=false->lo+1<=lb+c0)) /\
 (∀idx < ws.length,k11.testBit idx=true ->
  ∃d lb lo c0 cM pm,ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm) /\
   (lo+2<=lb+c0\/(lo+1<=lb+c0/\cM.testBit idx=true)))
def ColPrepOK(nv goal:Nat)(cp:ColPrepD):Prop:=
 let(lb,dD,pm0D):=cp
 ∃(zM oM:Nat)(pm0:List Nat),ColLowerBound nv goal zM oM lb/\dD=detVal (subcubeNv nv zM oM)/\pm0D=pm0.map detVal /\
  ∀m∈pm0,∃u < nv,(Nat.lor zM oM).testBit u=false/\m=Nat.land (hiC nv u) (subcubeNv nv zM oM)
private lemma restrict_land_eq {nv d w:Nat} {f:RowNv nv->RowNv nv}
  (hd:∀r,d.testBit (f r).1=true) :
  restrictRows f (observeNv nv (Nat.land w d))=restrictRows f (observeNv nv w):=by
 funext r;simp[restrictRows,observeNv,hd r]
private lemma nconst_sound {nv d m:Nat} {f:RowNv nv->RowNv nv}
  (hd:∀r,d.testBit (f r).1=true) (h:nconst d m=true) :
  Constant (restrictRows f (observeNv nv m)):=by
 rcases(nconst_iff d m).mp h with rfl|rfl
 ·exact⟨false,by funext r;simp[restrictRows,observeNv]⟩
 ·exact⟨true,by funext r;simp[restrictRows,observeNv,hd r]⟩
private lemma navail_sound {nv d m:Nat} {pm:List Nat} {f:RowNv nv->RowNv nv}
  {curBank:List (Wire (RowNv nv))} (hd:∀r,d.testBit (f r).1=true)
  (hpm:∀x∈pm,Available curBank (restrictRows f (observeNv nv x))) (h:navail d pm m=true) :
  Available curBank (restrictRows f (observeNv nv m)):=by
 cases c:nconst d m;swap;exact Or.inr (Or.inl (nconst_sound hd c))
 rcases(navail_iff d pm m).mp h with rfl|rfl|hm|hi
 ·simp[nconst]at c
 ·simp[nconst]at c
 ·exact hpm m hm
 ·rw[show restrictRows f (observeNv nv m)=inv (restrictRows f (observeNv nv (Nat.xor d m))) from
   funext λr=>by simp only[restrictRows,observeNv,inv,testBit_xor',hd r];cases m.testBit (f r).1<;>rfl]
  exact avail_inv (hpm _ hi)
private lemma subcubeD_eq {β:Type} {loDB hiDB:B16 Nat} {nv zM oM:Nat}
  (hlo:∀u < nv,unS (b16Get loDB u)=loC nv u) (hhi:∀u < nv,unS (b16Get hiDB u)=hiC nv u)
  (k:Nat->β):subcubeD loDB hiDB nv zM oM k=k (detVal (subcubeNv nv zM oM)):=by
 have go:∀v acc accR,v<=nv->unS acc=accR ->
   @Nat.rec (λ_=>Nat->β) (λa=>detS a k)
    (λu ih a=>cond (not (Nat.beq (Nat.land zM (Nat.shiftLeft 1 u)) 0))
     (forceN (Nat.land a (b16Get loDB u)) λa'=>ih a')
     (cond (not (Nat.beq (Nat.land oM (Nat.shiftLeft 1 u)) 0))
      (forceN (Nat.land a (b16Get hiDB u)) λa'=>ih a') (ih a))) v acc =
   k (detVal (subcubeGo nv zM oM v accR)):=λv=>by
  induction v with
  | zero=>intro _ _ _ hu;change detS _ k=_;rw[detS_eq,hu];rfl
  | succ u ih=>
   intro acc accR hv hu;dsimp only;rw[subcubeGo,testBit_eq_land_shift,testBit_eq_land_shift]
   cases hz:zM.testBit u<;>simp only[Bool.cond_true,Bool.cond_false,Bool.false_eq_true,ite_true,ite_false]
   ·cases ho:oM.testBit u<;>simp only[Bool.cond_true,Bool.cond_false,Bool.false_eq_true,ite_true,ite_false]
    ·exact ih acc accR (by omega) hu
    ·rw[forceN_eq];exact ih _ _ (by omega) (by rw[unS_land,hu,hhi u (by omega)])
   ·rw[forceN_eq];exact ih _ _ (by omega) (by rw[unS_land,hu,hlo u (by omega)])
 unfold subcubeD subcubeNv;rw[mkDet_eq];exact go nv _ _ (Nat.le_refl nv) (unS_detVal _)
private lemma mkPm0D_spec {β:Type} {hiDB:B16 Nat} {nv d fx:Nat}
  (hhi:∀u < nv,unS (b16Get hiDB u)=hiC nv u) :
  ∃pm0:List Nat,(∀k:List Nat->β,mkPm0D hiDB nv (detVal d) fx k=k (pm0.map detVal)) /\
   (∀m∈pm0,∃u < nv,fx.testBit u=false/\m=Nat.land (hiC nv u) d):=by
 have go:∀v (acc:List Nat),v<=nv ->
   (∀m∈acc,∃u < nv,fx.testBit u=false/\m=Nat.land (hiC nv u) d) ->
   ∃pm0:List Nat,(∀k:List Nat->β,@Nat.rec (λ_=>List Nat->β) (λa=>k a)
    (λu ih a=>cond (not (Nat.beq (Nat.land fx (Nat.shiftLeft 1 u)) 0)) (ih a)
     (forceN (Nat.land (b16Get hiDB u) (detVal d)) λraw=>detS raw λmD=>ih (mD::a)))
    v (acc.map detVal)=k (pm0.map detVal)) /\
    (∀m∈pm0,∃u < nv,fx.testBit u=false/\m=Nat.land (hiC nv u) d):=λv=>by
  induction v with
  | zero=>exact λacc _ h1=>⟨acc,λ_=>rfl,h1⟩
  | succ u ih=>
   intro acc hv h1;cases hf:fx.testBit u
   ·obtain⟨pm0,ep,h1'⟩:=ih (Nat.land (hiC nv u) d::acc) (by omega)
     λm hm=>(List.mem_cons.mp hm).elim (λe=>⟨u,by omega,hf,e⟩) (h1 m)
    exact⟨pm0,λk=>by dsimp only;rw[testBit_eq_land_shift,hf,Bool.cond_false,forceN_eq,detS_eq,unS_land,hhi u (by omega),unS_detVal];exact ep k,h1'⟩
   ·obtain⟨pm0,ep,h1'⟩:=ih acc (by omega) h1
    exact⟨pm0,λk=>by dsimp only;rw[testBit_eq_land_shift,hf,Bool.cond_true];exact ep k,h1'⟩
 exact go nv [] (Nat.le_refl nv) (by simp)
theorem prepColsD_sound {β:Type} {loDB hiDB:B16 Nat} {nv goal n:Nat}
  {cols:List (Nat×Nat×Nat)} (hlo:∀u < nv,unS (b16Get loDB u)=loC nv u)
  (hhi:∀u < nv,unS (b16Get hiDB u)=hiC nv u)
  (hcols:∀c∈cols,ColLowerBound nv goal c.1 c.2.1 c.2.2) (k:List ColPrepD->β) :
  ∃ps,prepColsD loDB hiDB nv n cols k=k ps/\∀p∈ps,ColPrepOK nv goal p:=by
 induction n generalizing cols k with
 | zero=>exact⟨[],rfl,by simp⟩
 | succ m ih=>
  cases cols with| nil=>exact⟨[],rfl,by simp⟩| cons c rest=>
  rcases c with ⟨zM,oM,lb⟩;unfold prepColsD;dsimp only
  rw[forceN_eq,forceN_eq,forceN_eq,forceN_eq,subcubeD_eq hlo hhi]
  obtain⟨pm0,ep,hp1⟩:=@mkPm0D_spec β _ _ (subcubeNv nv zM oM) (Nat.lor zM oM) hhi
  rw[ep];obtain⟨ps,er,hps⟩:=ih (λq hq=>hcols q (List.mem_cons_of_mem _ hq)) _
  exact⟨_::ps,er,λq hq=>(List.mem_cons.mp hq).elim
   (λe=>e▸⟨zM,oM,pm0,hcols (zM,oM,lb) (by simp),rfl,rfl,hp1⟩) (hps q)⟩
private lemma addG1_spec {cM notCM:Nat} (hlt:notCM<65536) {i j:Nat} (hj:j<16) :
  ∀m acc,bitTest (getCadj (addG1 cM notCM m acc) i) j=true ->
   bitTest (getCadj acc i) j=true\/(cM.testBit i=true/\notCM.testBit j=true):=λm=>by
 induction m with
 | zero=>exact λ_ h=>Or.inl h
 | succ u ih=>
  intro acc h;unfold addG1 at h;dsimp only at h
  cases hu:bitTest cM u
  ·rw[hu,Bool.cond_false]at h;exact ih acc h
  ·rw[hu,Bool.cond_true,forceN_eq]at h
   rcases ih _ h with h1|h2;swap;exact Or.inr h2
   rw[bitTest_eq,getCadj_testBit hj,testBit_lor',Bool.or_eq_true]at h1
   rcases h1 with ha|hs
   ·exact Or.inl (by rw[bitTest_eq,getCadj_testBit hj];exact ha)
   ·rw[testBit_shiftLeft',Bool.and_eq_true,decide_eq_true_eq,Nat.mul_eq]at hs
    have hiu:i=u:=by
     by_contra hne;rcases Nat.lt_or_gt_of_ne hne with hlt'|hgt'
     ·omega
     ·have:16<=i*16+j-u*16:=by omega
      rw[testBit_eq_false_of_lt_pow (k:=16) hlt this]at hs;exact Bool.noConfusion hs.2
    subst hiu;rw[bitTest_eq]at hu
    exact Or.inr ⟨hu,by simpa[show i*16+j-i*16=j by omega]using hs.2⟩
private lemma addQSS_sound {β:Type} {nv goal kChild allV d lb lo c0 cM uM:Nat} {ws pm:List Nat}
  {qps:List QS01D} {qnoZ:QNoZFast} {q11:List QS11} {k11:Nat} (hws16:ws.length<=16)
  (hvq:ValidQS nv goal kChild ws (d,lb,lo,c0,cM,uM,pm))
  (hbuf:QSBufOK nv goal kChild ws qps qnoZ q11 k11)
  (k:List QS01D->QNoZFast->List QS11->Nat->β) :
  ∃q' qn' q1' k1',addQSS allV (detVal d) lb lo c0 cM uM (pm.map detVal) qps qnoZ q11 k11 k=k q' qn' q1' k1' /\
   QSBufOK nv goal kChild ws q' qn' q1' k1':=by
 unfold addQSS;rw[forceN_eq];cases hle:Nat.ble lo (Nat.add lb c0);· exact⟨_,_,_,_,rfl,hbuf⟩
 rw[forceB_eq,forceB_eq,forceB_eq,forceN_eq];have hle':=Nat.ble_eq.mp hle
 set bl:=cond (and (Nat.ble (Nat.succ lo) (Nat.add lb c0)) (or (Nat.beq uM 0) (Nat.ble (popcnt16 uM) 2))) (mkBloom (detVal d) (pm.map detVal)) 0
 have hqps':∀y∈cond (or (Nat.beq uM 0) (Nat.ble (popcnt16 uM) 2)) ((detVal d,Nat.add lb c0,lo,cM,uM,bl,pm.map detVal)::qps) qps,
   ValidQSD nv goal kChild ws y:=by
  cases or (Nat.beq uM 0) (Nat.ble (popcnt16 uM) 2)<;>intro y hy;exact hbuf.1 y hy
  exact(List.mem_cons.mp hy).elim (·▸⟨d,lb,c0,pm,rfl,rfl,rfl,hvq⟩) (hbuf.1 y)
 cases hu:Nat.beq uM 0;· rw[hu]at hqps';exact⟨_,_,_,_,rfl,hqps',hbuf.2⟩
 rw[Bool.cond_true,Bool.cond_true];cases Nat.eq_of_beq_eq_true hu
 rcases qnoZ with ⟨kAll,k01,g2I,g1K⟩;obtain⟨_,⟨hkA,hk01,hg2,hg1⟩,hq11,hk11⟩:=hbuf;dsimp only
 have hq11' b (hb:b=false->lo+1<=lb+c0):∀q∈(detVal d,b,bl,pm.map detVal)::q11,
   ∃d lb lo c0 cM pm,q.1=detVal d/\q.2.2.2=pm.map detVal /\
   ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo<=lb+c0/\(q.2.1=false->lo+1<=lb+c0):=
  λq hq=>(List.mem_cons.mp hq).elim (·▸⟨d,lb,lo,c0,cM,pm,rfl,rfl,hvq,hle',hb⟩) (hq11 q)
 have hq11n:=hq11' (not (Nat.ble (Nat.succ lo) (Nat.add lb c0))) λh=>match hsl:Nat.ble (Nat.succ lo) (Nat.add lb c0)with| false=>(by rw[hsl]at h;cases h)| true=>Nat.ble_eq.mp hsl
 cases h2:Nat.ble (Nat.add lo 2) (Nat.add lb c0)
 ·rw[Bool.cond_false];cases h1:Nat.ble (Nat.succ lo) (Nat.add lb c0)
  ·rw[Bool.cond_false];exact⟨_,_,_,_,rfl,hqps',⟨hkA,hk01,hg2,hg1⟩,hq11' _ (by simp),hk11⟩
  ·rw[Bool.cond_true,forceN_eq,forceN_eq,forceN_eq];have h1':=Nat.ble_eq.mp h1
   have hncLt:Nat.xor 65535 (Nat.land cM 65535)<65536:=lt_two_pow_of_testBit (k:=16) λr hr=>by
    rw[testBit_xor',testBit_land',show(65535:Nat)=2^16-1 from rfl,Nat.testBit_two_pow_sub_one,decide_eq_false (by omega)];simp
   refine⟨_,_,_,_,rfl,hqps',⟨hkA,hk01,hg2,λi hi j hj hb=> ?_⟩,hq11' _ (λ_=>h1'),λidx hidx hb=> ?_⟩
   ·rcases addG1_spec hncLt (by omega) 16 g1K hb with h0|⟨hci,hnj⟩;exact hg1 i hi j hj h0
    rw[testBit_xor',testBit_land',show(65535:Nat)=2^16-1 from rfl,Nat.testBit_two_pow_sub_one,decide_eq_true (by omega:j<16)]at hnj
    exact⟨d,lb,lo,c0,cM,pm,hvq,h1',hci,by cases hc':cM.testBit j<;>simp[hc']at hnj ⊢⟩
   ·rw[testBit_lor',Bool.or_eq_true]at hb;exact hb.elim (hk11 idx hidx) λh=>⟨d,lb,lo,c0,cM,pm,hvq,Or.inr ⟨h1',h⟩⟩
 ·rw[Bool.cond_true];have h2':=Nat.ble_eq.mp h2
  cases h3:Nat.ble (Nat.add lo 3) (Nat.add lb c0)
  ·rw[Bool.cond_false,forceN_eq]
   refine⟨_,_,_,_,rfl,hqps',⟨hkA,λ_=>⟨d,lb,lo,c0,cM,pm,hvq,h2'⟩,λi hi hf=> ?_,hg1⟩,hq11n,λ_ _ _=>⟨d,lb,lo,c0,cM,pm,hvq,Or.inl h2'⟩⟩
   rw[testBit_land',Bool.and_eq_false_iff]at hf;exact hf.elim (hg2 i hi) λhcF=>⟨d,lb,lo,c0,cM,pm,hvq,h2',hcF⟩
  ·rw[Bool.cond_true]
   exact⟨_,_,_,_,rfl,hqps',⟨λ_=>⟨d,lb,lo,c0,cM,pm,hvq,Nat.ble_eq.mp h3⟩,
    λ_=>⟨d,lb,lo,c0,cM,pm,hvq,h2'⟩,hg2,hg1⟩,hq11n,λ_ _ _=>⟨d,lb,lo,c0,cM,pm,hvq,Or.inl h2'⟩⟩
private lemma pm0_avail {nv zM oM:Nat} {f:RowNv nv->RowNv nv} {rs:List (Wire (RowNv nv))} {pm0:List Nat}
  (df:∀r,(subcubeNv nv zM oM).testBit (f r).1=true)
  (rw0:∀a∈freeVarsNv nv (Nat.lor zM oM),Available rs (restrictRows f (observeNv nv a)))
  (hp1:∀m∈pm0,∃u < nv,(Nat.lor zM oM).testBit u=false/\m=Nat.land (hiC nv u) (subcubeNv nv zM oM)) :
  ∀m∈pm0,Available rs (restrictRows f (observeNv nv m)):=λm hm=>by
 obtain⟨u,hu,hfu,rfl⟩:=hp1 m hm;rw[restrict_land_eq df]
 have go:∀k a,(∀x∈a,x∈freeVarsNv.go nv (Nat.lor zM oM) k a)/\(u<k->hiC nv u∈freeVarsNv.go nv (Nat.lor zM oM) k a):=λk=>by
  induction k with| zero=>exact λ_=>⟨λ_ h=>h,λh=>by omega⟩| succ j ih=>
   intro a;simp only[freeVarsNv.go];split_ifs with hj
   ·exact⟨(ih a).1,λh=>(ih a).2 (by have:u≠j:=λe=>(by rw[e,hj]at hfu;exact Bool.noConfusion hfu);omega)⟩
   ·exact⟨λx hx=>(ih _).1 x (List.mem_cons_of_mem _ hx),λh=>by by_cases e:u=j;subst e;exact(ih _).1 _ List.mem_cons_self;exact(ih _).2 (by omega)⟩
 exact rw0 (hiC nv u) ((go nv []).2 hu)
private lemma scanMasksD0_spec {β:Type} (d:Nat) (ws pm:List Nat) (k:Nat->Nat->Nat->β) :
  ∃c0 cM uM,scanMasksD0 (detVal d) (pm.map detVal) (ws.map detVal) 0 0 0 0 k=k c0 cM uM /\
   c0=(List.range ws.length).countP (λidx=>nconst d (Nat.land (listGetN ws idx) d)) /\
   (∀idx,cM.testBit idx=true↔idx<ws.length/\nconst d (Nat.land (listGetN ws idx) d)=true) /\
   (∀idx < ws.length,uM.testBit idx=false->navail d pm (Nat.land (listGetN ws idx) d)=true):=by
 let P i:=nconst d (Nat.land (listGetN ws i) d)
 let O m c0 (cM uM:Nat):=c0=(List.range m).countP P/\(∀i,cM.testBit i=true↔i < m/\P i=true) /\
  (∀i < m,uM.testBit i=false->navail d pm (Nat.land (listGetN ws i) d)=true)
 have go:∀o s c0 (cM uM:Nat),s=ws.drop o->o<=ws.length->O o c0 cM uM ->
   ∃a b e,scanMasksD0 (detVal d) (pm.map detVal) (s.map detVal) o c0 cM uM k=k a b e/\O ws.length a b e:=λo s=>by
  induction s generalizing o with
  | nil=>
      intro c0 cM uM h _ ok;have:o=ws.length:=by have:=congrArg List.length h;simp at this;omega
      exact this▸⟨c0,cM,uM,rfl,ok⟩
  | cons _ _ ih=>
   intro c0 cM uM h _ ⟨h0,hM,hU⟩;obtain⟨ho,rfl,rfl⟩:=drop_cons_iff h.symm
   unfold scanMasksD0;rw[List.map_cons];dsimp only
   rw[forceN_eq,nconstRawD_eq,unS_land,unS_detVal,unS_detVal,<-listGetN_getElem ho]
   have hcnt (b:Bool) (hb:P o=b):(List.range (o+1)).countP P=c0+if b then 1 else 0:=by simp[List.range_succ,hb,h0]
   cases hc:nconst d (Nat.land (listGetN ws o) d)
   ·rw[Bool.cond_false,detS_eq,unS_land,unS_detVal,unS_detVal,navailNonConstD_eq]
    have hbit i:cM.testBit i=true↔i<o+1/\P i=true:=by
     rw[hM];exact⟨λ⟨a,b⟩=>⟨by omega,b⟩,λ⟨a,b⟩=>⟨if e:i=o then Bool.noConfusion ((e▸b).symm.trans hc)else by omega,b⟩⟩
    cases hna:or (anyEq (Nat.land (listGetN ws o) d) pm) (anyEq (Nat.xor d (Nat.land (listGetN ws o) d)) pm)
    ·rw[Bool.cond_false,forceN_eq];exact ih (o+1) c0 cM (Nat.lor uM (Nat.shiftLeft 1 o)) rfl (by omega) ⟨by simpa using (hcnt false hc).symm,hbit,λi hi hu=>by rw[testBit_lor',shl1_tb,Bool.or_eq_false_iff]at hu;if e:i=o then simp[e]at hu else exact hU i (by omega) hu.1⟩
    ·exact ih (o+1) c0 cM uM rfl (by omega) ⟨by simpa using (hcnt false hc).symm,hbit,λi hi hu=>if e:i=o then by subst e;rw[navail,hc,Bool.false_or];exact hna else hU i (by omega) hu⟩
   ·rw[Bool.cond_true,forceN_eq,forceN_eq];exact ih (o+1) (Nat.add c0 1) (Nat.lor cM (Nat.shiftLeft 1 o)) uM rfl (by omega) ⟨by simpa[Nat.add_eq]using (hcnt true hc).symm,(λi=>by rw[testBit_lor',shl1_tb,Bool.or_eq_true,hM];if e:i=o then(subst e;exact⟨λ_=>⟨Nat.lt_succ_self _,hc⟩,λ_=>Or.inr (decide_eq_true rfl)⟩)else simp[Ne.symm e,show(i<o+1)↔(i<o) by omega]),λi hi hu=>if e:i=o then by subst e;rw[navail,hc];rfl else hU i (by omega) hu⟩
 exact go 0 ws 0 0 0 rfl (Nat.zero_le _) ⟨by simp,by simp,λ_ h=>by omega⟩
private lemma buildPoolD_sound {β:Type} {nv d:Nat} {f:RowNv nv->RowNv nv}
  {rs:List (Wire (RowNv nv))} (gates:List (Nat×Nat×Nat)) (df:∀r,d.testBit (f r).1=true) :
  ∀sg pM gi (pm:List Nat) pd cb (cont:List Nat->Nat->β),
   Reach rs pd cb->(∀m∈pm,Available cb (restrictRows f (observeNv nv m))) ->
   (∀j g,sg[j]?=some g->gates[gi-nv+j]?=some g)->nv<=gi ->
   ∃pm':List Nat,∃pd' cb',
    buildPoolD (detVal d) sg pM ((decodeBank gates ((List.range nv).map (hiC nv))).map detVal) gi (pm.map detVal) pd cont=cont (pm'.map detVal) pd' /\
    Reach rs pd' cb'/\(∀m∈pm',Available cb' (restrictRows f (observeNv nv m))):=by
 set bk:=decodeBank gates ((List.range nv).map (hiC nv))
 have hgetD idx:unS (listGetN (bk.map detVal) idx)=listGetN bk idx:=by
  simp[listGetN_eq_getD,List.getElem?_map];cases bk[idx]?<;>simp[unS_detVal];rfl
 intro sg;induction sg with
 | nil=>exact λ_ _ pm pd cb _ rc kp _ _=>⟨pm,pd,cb,rfl,rc,kp⟩
 | cons g restG ihG=>
  rcases g with ⟨o,a,b⟩;intro pM gi pm pd cb cont rc kp hsg hnvg
  have hrg j g' (hj:restG[j]?=some g'):=by simpa[show gi-nv+(j+1)=gi+1-nv+j by omega]using hsg (j+1) g' (by simpa using hj)
  have sk:=ihG (Nat.shiftRight pM 1) (gi+1) pm pd cb cont rc kp hrg (by omega)
  unfold buildPoolD;dsimp only
  cases Nat.beq (Nat.land pM 1) 0;swap;exact sk
  cases wf:and (Nat.ble (Nat.add a 1) gi) (Nat.ble (Nat.add b 1) gi);· exact sk
  rw[forceN_eq,nconstRawD_eq,unS_land,hgetD,unS_detVal]
  cases nconst d (Nat.land (listGetN bk gi) d);swap;exact sk
  rw[detS_eq,unS_land,hgetD,unS_detVal,navailNonConstD_eq]
  cases or (anyEq (Nat.land (listGetN bk gi) d) pm) (anyEq (Nat.xor d (Nat.land (listGetN bk gi) d)) pm);swap;exact sk
  have hokEq idx:or (or (isZeroS (Nat.land (listGetN (bk.map detVal) idx) (detVal d))) (eqS (detVal d) (Nat.land (listGetN (bk.map detVal) idx) (detVal d))))
    (detS (Nat.land (listGetN (bk.map detVal) idx) (detVal d)) λm=>navailNonConstD (detVal d) (pm.map detVal) m)=navail d pm (Nat.land (listGetN bk idx) d):=by
   rw[nconstRawD_eq,detS_eq,unS_land,hgetD,unS_detVal,navailNonConstD_eq,navail,Bool.or_assoc]
  rw[forceN_eq,hokEq a];cases ha':navail d pm (Nat.land (listGetN bk a) d);· exact sk
  rw[forceN_eq,hokEq b];cases hb':navail d pm (Nat.land (listGetN bk b) d);· exact sk
  simp[Bool.and_eq_true,Nat.ble_eq,Nat.add_eq]at wf
  have ge:=decodeBank_gate_eq gates ((List.range nv).map (hiC nv)) (gi-nv) (o,a,b) (by simpa using hsg 0 (o,a,b) rfl)
  simp[List.length_map,List.length_range,show nv+(gi-nv)=gi by omega]at ge
  have bq:=ge.elim id λh=>by rcases h with h|h<;>omega
  obtain⟨e,e4,ze⟩:=zN_mod_op o (Nat.land (listGetN bk a) d) (Nat.land (listGetN bk b) d)
  obtain⟨opB,x,y,hx,hy,cb',_,_⟩:=comb_prime e4 (navail_sound df kp ha') (navail_sound df kp hb')
  have ob:restrictRows f (observeNv nv (Nat.land (listGetN bk gi) d))=combine opB x y:=by
   rw[<-cb',bq,<-zN_and_mask,ze];funext r';exact zN_spec e _ _ (f r').1
  exact ihG (Nat.shiftRight pM 1) (gi+1) (Nat.land (listGetN bk gi) d::pm) (pd+1) (combine opB x y::cb) cont
   (Reach.two opB rc hx hy) (λm hm=>(List.mem_cons.mp hm).elim (λeq=>eq▸ob▸Or.inl (by simp)) λt=>available_cons _ (kp m t)) hrg (by omega)
theorem scanAutoTierD_sound {β:Type} (nv goal kChild allV fullM autoCnt:Nat)
  (gates:List (Nat×Nat×Nat)) (ws:List Nat) {prepped:List ColPrepD}
  {qps0:List QS01D} {qnoZ0:QNoZFast} {q110:List QS11} {k110:Nat} (hws16:ws.length<=16)
  (hprep:∀p∈prepped,ColPrepOK nv goal p) (hbuf0:QSBufOK nv goal kChild ws qps0 qnoZ0 q110 k110)
  (k:List QS01D->QNoZFast->List QS11->Nat->β) :
  ∃qps qnoZ q11 k11,
   scanAutoTierD nv kChild allV fullM autoCnt gates ((decodeBank gates ((List.range nv).map (hiC nv))).map detVal)
    (ws.map detVal) prepped qps0 qnoZ0 q110 k110 k=k qps qnoZ q11 k11 /\
   QSBufOK nv goal kChild ws qps qnoZ q11 k11:=by
 induction autoCnt generalizing prepped qps0 qnoZ0 q110 k110 with
 | zero=>exact⟨_,_,_,_,rfl,hbuf0⟩
 | succ cnt ih=>
  cases prepped with| nil=>exact⟨_,_,_,_,rfl,hbuf0⟩| cons cp rest=>
  rcases cp with ⟨lb,dD,pm0D⟩;obtain⟨zM,oM,pm0,⟨f,rs,df,rw0,nc,hlb⟩,rfl,rfl,hp1⟩:=hprep (lb,dD,pm0D) (by simp)
  have hpm0A:=pm0_avail df rw0 hp1;have hrest p hp:=hprep p (List.mem_cons_of_mem _ hp)
  unfold scanAutoTierD;dsimp only
  obtain⟨c0,cM,uM,hsm,hc0,hcM,huM⟩:=scanMasksD0_spec (subcubeNv nv zM oM) ws pm0 _
  obtain⟨q',qn',q1',k1',ha0,hbuf1⟩:=@addQSS_sound _ _ _ _ _ _ _ kChild _ _ _ _ _ _ _ _ _ hws16 (Or.inr ⟨f,rs,0,rs,rfl,Reach.start,nc,hlb,df,hpm0A,hc0,hcM,huM⟩) hbuf0 _
  rw[hsm,ha0];cases and (not (Nat.beq uM 0)) (Nat.ble (Nat.add kChild 1) (Nat.add lb c0));· exact ih hrest hbuf1
  obtain⟨pmF,pdF,cbF,ep,rF,kF⟩:=buildPoolD_sound gates df gates fullM nv pm0 0 rs _ Reach.start hpm0A (λ_ _ h=>by simpa using h) (Nat.le_refl nv)
  rw[ep];cases Nat.beq pdF 0;swap;exact ih hrest hbuf1
  obtain⟨c0F,cMF,uMF,hsmF,hc0F,hcMF,huMF⟩:=scanMasksD0_spec (subcubeNv nv zM oM) ws pmF _
  obtain⟨q'',qn'',q1'',k1'',haF,hbuf2⟩:=@addQSS_sound _ _ _ _ _ _ _ (Nat.add kChild pdF) _ _ _ _ _ _ _ _ _ hws16 (Or.inr ⟨f,rs,pdF,cbF,rfl,rF,nc,hlb,df,kF,hc0F,hcMF,huMF⟩) hbuf1 _
  rw[hsmF,forceN_eq,haF];exact ih hrest hbuf2
theorem buildExpHintsD_sound {β:Type} {loDB hiDB:B16 Nat} (nv goal kChild allV:Nat)
  {cols:Array (Nat×Nat×Nat)} (gates:List (Nat×Nat×Nat)) (ws:List Nat) (hsExp:List (Nat×Nat))
  (hws16:ws.length<=16)
  (hlo:∀u < nv,unS (b16Get loDB u)=loC nv u) (hhi:∀u < nv,unS (b16Get hiDB u)=hiC nv u)
  (hcols:ColsSound nv goal cols) (k:List QS01D->QNoZFast->List QS11->Nat->β) :
  ∃qps qnoZ q11 k11,
   buildExpHintsDGo loDB hiDB cols nv kChild allV gates ((decodeBank gates ((List.range nv).map (hiC nv))).map detVal)
    (ws.map detVal) hsExp [] emptyQNoZ [] 0 k=k qps qnoZ q11 k11 /\
   QSBufOK nv goal kChild ws qps qnoZ q11 k11:=by
 set bkD:=(decodeBank gates ((List.range nv).map (hiC nv))).map detVal
 have hgo:∀hs q qn q1 k1,QSBufOK nv goal kChild ws q qn q1 k1 ->
   ∃q' qn' q1' k1',buildExpHintsDGo loDB hiDB cols nv kChild allV gates bkD (ws.map detVal) hs q qn q1 k1 k=k q' qn' q1' k1' /\
    QSBufOK nv goal kChild ws q' qn' q1' k1':=λhs=>by
  induction hs with| nil=>exact λ_ _ _ _ hb=>⟨_,_,_,_,rfl,hb⟩| cons h _ ih=>
   intro q qn q1 k1 hb;rcases h with ⟨ci,paidM⟩;unfold buildExpHintsDGo;dsimp only
   by_cases hci:ci+1<=cols.size;swap;· rw[ble_false_of_gt hci];exact ih q qn q1 k1 hb
   have hlt:ci<cols.size:=by omega
   rw[Nat.ble_eq.mpr hci];simp only[Bool.cond_true,hlt,dite_true]
   set zM:=(cols.getInternal ci hlt).1;set oM:=(cols.getInternal ci hlt).2.1;set lb:=(cols.getInternal ci hlt).2.2
   obtain⟨f,rs,df,rw0,nc,hlb⟩:=show ColLowerBound nv goal zM oM lb from hcols ci hlt
   obtain⟨pm0,ep0,hp1⟩:=@mkPm0D_spec β _ _ (subcubeNv nv zM oM) (Nat.lor zM oM) hhi
   obtain⟨pm,pd,cb,ep,rc,kp⟩:=buildPoolD_sound gates df gates paidM nv pm0 0 rs _ Reach.start (pm0_avail df rw0 hp1) (λ_ _ h=>by simpa using h) (Nat.le_refl nv)
   obtain⟨c0,cM,uM,hsm,hc0,hcM,huM⟩:=scanMasksD0_spec (subcubeNv nv zM oM) ws pm _
   obtain⟨q',qn',q1',k1',ha,hb'⟩:=@addQSS_sound _ _ _ _ _ _ _ (Nat.add kChild pd) _ _ _ _ _ _ _ _ _ hws16 (Or.inr ⟨f,rs,pd,cb,rfl,rc,nc,hlb,df,kp,hc0,hcM,huM⟩) hb _
   rw[forceN_eq,forceN_eq,forceN_eq,forceN_eq,subcubeD_eq hlo hhi,ep0]
   dsimp only[bkD];rw[ep,hsm,forceN_eq,ha];exact ih q' qn' q1' k1' hb'
 exact hgo hsExp [] emptyQNoZ [] 0 (by
  refine⟨by simp,⟨by simp[emptyQNoZ],by simp[emptyQNoZ,bitTest_eq],λi hi hf=> ?_,λi _ j hj h=> ?_⟩,by simp,by simp⟩
  ·rw[show(65535:Nat)=2^16-1 from rfl,Nat.testBit_two_pow_sub_one,decide_eq_true (by omega)]at hf;cases hf
  ·rw[bitTest_eq,getCadj_testBit (by omega),Nat.zero_testBit]at h;cases h)
def keepMaskOf(allV bitI bitJ:Nat)(ka kb:Bool):Nat:=
 cond ka (cond kb allV (Nat.xor allV bitJ))
  (cond kb (Nat.xor allV bitI) (Nat.xor allV (Nat.lor bitI bitJ)))
private def keptWsOf (ws:List Nat) (ii jj:Nat) (ka kb:Bool):List Nat:=
 ((List.range ws.length).filter (λidx=>decide ((idx≠ii\/ka=true)/\(idx≠jj\/kb=true)))).map (listGetN ws)
private def lossB (k b:Bool):Nat:=if k=false/\b=true then 1 else 0
private lemma countP_filter_drop2 {l:List Nat} (hnd:l.Nodup) (P:Nat->Bool)
  (ii jj:Nat) (hne:ii≠jj) (ka kb:Bool) :
  let K:Nat->Bool:=λi=>decide ((i≠ii\/ka=true)/\(i≠jj\/kb=true))
  (l.filter K).countP P+(if ka=false/\ii∈l/\P ii=true then 1 else 0) +
   (if kb=false/\jj∈l/\P jj=true then 1 else 0)=l.countP P:=by
 induction l with
 | nil=>simp
 | cons x _ ih=>
  simp only[List.nodup_cons]at hnd;have h:=ih hnd.2;simp only[List.filter_cons,List.countP_cons,List.mem_cons]
  by_cases a:x=ii;· subst a;cases ka<;>cases p:P x<;>simp[hnd.1,hne,Ne.symm hne,p]at h ⊢<;>omega
  by_cases b:x=jj;· subst b;cases kb<;>cases p:P x<;>simp[hnd.1,a,Ne.symm a,p]at h ⊢<;>omega
  ·simp only[show decide ((x≠ii\/ka=true)/\(x≠jj\/kb=true))=true by simp[a,b],ite_true,List.countP_cons,Ne.symm a,Ne.symm b,false_or];omega
private lemma countP_le_mass {nv d:Nat} (ws:List Nat) {f:RowNv nv->RowNv nv}
  (hd:∀r,d.testBit (f r).1=true) (l:List Nat) :
  l.countP (λi=>nconst d (Nat.land (listGetN ws i) d)) <=
   mass ((l.map (listGetN ws)).map (λw=>restrictRows f (observeNv nv w))):=by
 induction l with| nil=>simp[mass]| cons i _ ih=>
  simp only[List.countP_cons,List.map_cons,mass_cons]
  cases p:nconst d (Nat.land (listGetN ws i) d);· simp only[p,Bool.false_eq_true,↓reduceIte,Nat.add_zero];omega
  have:cost (restrictRows f (observeNv nv (listGetN ws i)))=1:=by simp[cost,restrict_land_eq hd▸nconst_sound hd p]
  simp only[p,↓reduceIte,this];omega
private lemma qs_contra {nv goal k z p lb m0:Nat} {base:List Nat}
  {f:RowNv nv->RowNv nv} {roots bank:List (Wire (RowNv nv))}
  (hrun:Run (observeNv nv goal) k ((z::base).map (observeNv nv)))
  (hnc:¬Constant (restrictRows f (observeNv nv goal))) (hreach:Reach roots p bank)
  (hlb:∀q' out,Reach roots q' out->Available out (restrictRows f (observeNv nv goal))->lb<=q')
  (hz:Available bank (restrictRows f (observeNv nv z)))
  (hb:∀w∈base,Available bank (restrictRows f (observeNv nv w)))
  (hm:m0<=mass (base.map (λw=>restrictRows f (observeNv nv w))))
  (hgt:p+k<lb+cost (restrictRows f (observeNv nv z))+m0):False:=by
 have h:=projected_bound f hrun hnc hreach (λv hv=>by
  rw[List.map_map,List.map_cons]at hv;exact(List.mem_cons.mp hv).elim (·▸hz) λh=>let⟨w,hw,e⟩:=List.mem_map.mp h;e▸hb w hw) hlb
 simp[List.map_map,List.map_cons,mass_cons,Function.comp_def]at h;omega
private lemma kept_nd_fin {ii jj z:Nat} {ws:List Nat} (ka kb:Bool)
  (hnd:ws.Nodup) (hi:ii<ws.length) (hj:jj<ws.length) (hfresh:z∉ws.toFinset) :
  let K:Nat->Bool:=λidx=>decide ((idx≠ii\/ka=true)/\(idx≠jj\/kb=true))
  (z::keptWsOf ws ii jj ka kb).Nodup/\(z::keptWsOf ws ii jj ka kb).toFinset=childSet ws ii jj z ka kb /\
  (∀w∈keptWsOf ws ii jj ka kb,∃idx < ws.length,K idx=true/\w=listGetN ws idx):=by
 dsimp;set K:Nat->Bool:=λi=>decide ((i≠ii\/ka=true)/\(i≠jj\/kb=true))
 have hm w (h:w∈keptWsOf ws ii jj ka kb):∃i < ws.length,K i=true/\w=listGetN ws i:=by
  obtain⟨i,hi',rfl⟩:=List.mem_map.mp h;obtain⟨r,k⟩:=List.mem_filter.mp hi';exact⟨i,List.mem_range.mp r,k,rfl⟩
 refine⟨List.nodup_cons.mpr ⟨λm=>let⟨_,h,_,e⟩:=hm z m;hfresh (e▸List.mem_toFinset.mpr (listGetN_mem h)),
  List.Nodup.map_on (λa ha b hb=>listGetN_inj_of_nodup hnd (List.mem_range.mp (List.mem_filter.mp ha).1) (List.mem_range.mp (List.mem_filter.mp hb).1)) (List.Nodup.filter K List.nodup_range)⟩,?_,hm⟩
 ext x;simp[List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,childSet];apply or_congr_right;constructor
 ·intro h;obtain⟨i,q,k,rfl⟩:=hm x h
  have:=List.mem_toFinset.mpr (listGetN_mem q);have:=of_decide_eq_true k
  have:=mt (listGetN_inj_of_nodup hnd q hi);have:=mt (listGetN_inj_of_nodup hnd q hj)
  cases ka<;>cases kb<;>simp_all
 ·intro h
  have m:x∈ws.toFinset:=by cases ka<;>cases kb<;>simp only[Bool.false_eq_true,ite_false,ite_true,Finset.mem_erase]at h<;>tauto
  obtain⟨i,q,rfl⟩:=List.getElem_of_mem (List.mem_toFinset.mp m);rw[<-listGetN_getElem q]at h ⊢
  refine List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨List.mem_range.mpr q,decide_eq_true ?_⟩,rfl⟩
  cases ka<;>cases kb<;>simp[Bool.false_eq_true,ite_false,ite_true,Finset.mem_erase]at h<;>grind
private lemma kept_mass {nv d ii jj:Nat} {ws:List Nat} (ka kb:Bool) {f:RowNv nv->RowNv nv}
  (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hd:∀r,d.testBit (f r).1=true) :
  let c0:=(List.range ws.length).countP (λi=>nconst d (Nat.land (listGetN ws i) d))
  let a:=lossB ka (nconst d (Nat.land (listGetN ws ii) d));let b:=lossB kb (nconst d (Nat.land (listGetN ws jj) d))
  a+b<=c0/\c0-a-b<=mass ((keptWsOf ws ii jj ka kb).map (λw=>restrictRows f (observeNv nv w))):=by
 have h:=countP_filter_drop2 (l:=List.range ws.length) List.nodup_range (λi=>nconst d (Nat.land (listGetN ws i) d)) ii jj hne ka kb
 simp only[List.mem_range,hi,hj,true_and]at h
 have:=countP_le_mass ws hd ((List.range ws.length).filter (λi=>decide ((i≠ii\/ka=true)/\(i≠jj\/kb=true))))
 dsimp only[keptWsOf,lossB];omega
private lemma qs_kill_z {nv goal kChild z d lb lo c0 cM uM m0:Nat} {ws base:List Nat} {pm:List Nat} {S:Finset Nat}
  (hvq:ValidQS nv goal kChild ws (d,lb,lo,c0,cM,uM,pm)) (hm0:m0<=c0)
  (hnd:(z::base).Nodup) (hfin:(z::base).toFinset=S)
  (hsub:∀w∈base,∃idx < ws.length,uM.testBit idx=false/\w=listGetN ws idx)
  (hm:∀f:RowNv nv->RowNv nv,(∀r,d.testBit (f r).1=true) ->
   m0<=mass (base.map (λw=>restrictRows f (observeNv nv w))))
  (hcond:(lo+1<=lb+m0/\navail d pm (Nat.land z d)=true)\/(lo<=lb+m0/\nconst d (Nat.land z d)=true)) :
  ImpossibleNv nv goal kChild S:=by
 rcases hvq with _|⟨f,_,_,_,_,rc,nc,lb',df,hp,_,_,hu⟩;· rcases hcond with ⟨_,_⟩|⟨_,_⟩<;>omega
 intro _ _ hc;have rn:=list_runNv hc (z::base) hnd hfin
 have hb w (h:w∈base):=let⟨i,q,u,e⟩:=hsub w h;e.symm▸restrict_land_eq df▸navail_sound df hp (hu i q u)
 have ms:=hm f df
 rcases hcond with ⟨_,a⟩|⟨_,c⟩
 ·exact qs_contra rn nc rc lb' (restrict_land_eq df▸navail_sound df hp a) hb ms (by omega)
 ·have q:=restrict_land_eq df▸nconst_sound df c;have:cost (restrictRows f (observeNv nv z))=1:=by simp[cost,q]
  exact qs_contra rn nc rc lb' (Or.inr (Or.inl q)) hb ms (by omega)
private lemma validQS_noZ_kill {nv goal kChild ii jj op:Nat} {ws:List Nat} (ka kb:Bool)
  {d lb lo c0 cM:Nat} {pm:List Nat}
  (hnd:ws.Nodup) (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hop:op<4)
  (hfresh:zN op (listGetN ws ii) (listGetN ws jj)∉ws.toFinset)
  (hvq:ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm))
  (hge1:lo+1<=lb+c0-lossB ka (cM.testBit ii)-lossB kb (cM.testBit jj))
  (hor:lo+2<=lb+c0-lossB ka (cM.testBit ii)-lossB kb (cM.testBit jj)\/cM.testBit ii=true\/cM.testBit jj=true) :
  ImpossibleNv nv goal kChild (childSet ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) ka kb):=by
 rcases hvq with _|⟨f,_,_,_,_,rc,nc,lb',df,hp,h0,hM,hu⟩;· omega
 intro _ _ hc;obtain⟨nk,fk,km⟩:=kept_nd_fin ka kb hnd hi hj hfresh
 have rn:=list_runNv hc _ nk fk;obtain⟨ls,ms⟩:=kept_mass ka kb hi hj hne df;rw[<-h0]at ls ms
 have hl {i} (b:Bool) (h:i<ws.length):lossB b (cM.testBit i)=lossB b (nconst d (Nat.land (listGetN ws i) d)):=by simp[lossB,hM i,h]
 rw[hl ka hi,hl kb hj]at hge1
 have al i (h:i<ws.length):=restrict_land_eq df▸navail_sound df hp (hu i h (Nat.zero_testBit i))
 have ob:restrictRows f (observeNv nv (zN op (listGetN ws ii) (listGetN ws jj))) =
   comb op (restrictRows f (observeNv nv (listGetN ws ii))) (restrictRows f (observeNv nv (listGetN ws jj))):=funext λr=>zN_spec op _ _ (f r).1
 rcases hor with g2|cj
 ·rw[hl ka hi,hl kb hj]at g2;obtain⟨o,x,y,hx,hy,cb,_,_⟩:=comb_prime hop (al ii hi) (al jj hj)
  exact qs_contra rn nc (Reach.two o rc hx hy) lb' (by rw[ob,cb];exact Or.inl (by simp))
   (λw hw=>let⟨i,q,_,e⟩:=km w hw;e▸available_cons _ (al i q)) ms (by omega)
 ·exact qs_contra rn nc rc lb' (ob.symm▸from_constant_comb hop (al ii hi) (al jj hj)
   (cj.imp (λh=>restrict_land_eq df▸nconst_sound df ((hM ii).mp h).2) (λh=>restrict_land_eq df▸nconst_sound df ((hM jj).mp h).2)))
   (λw hw=>let⟨i,q,_,e⟩:=km w hw;e▸al i q) ms (by omega)
@[local simp] private lemma loss_eq_bit (cM idx:Nat) (k:Bool) :
  (cond k 0 (cond (Nat.beq (Nat.land cM (Nat.shiftLeft 1 idx)) 0) 0 1))=lossB k (cM.testBit idx):=by
 rw[<-testBit_eq_land_shift cM idx];cases Nat.beq (Nat.land cM (Nat.shiftLeft 1 idx)) 0<;>cases k<;>rfl
theorem checkNoZFast_sound {nv goal kChild ii jj op:Nat} {ws:List Nat} {ka kb:Bool} {qnoZ:QNoZFast}
  (hnd:ws.Nodup) (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hop:op<4)
  (hfresh:zN op (listGetN ws ii) (listGetN ws jj)∉ws.toFinset)
  (hqnoZ:QNoZFastOK nv goal kChild ws qnoZ)
  (htrue:checkNoZFast ii jj (Nat.lor (Nat.shiftLeft 1 ii) (Nat.shiftLeft 1 jj)) ka kb qnoZ=true) :
  ImpossibleNv nv goal kChild (childSet ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) ka kb):=by
 rcases qnoZ with ⟨kAll,k01,g2I,g1K⟩;obtain⟨hkA,hk01,hg2,hg1⟩:=hqnoZ
 unfold checkNoZFast at htrue;dsimp only at htrue
 have hloss (k b:Bool):lossB k b<=1:=by cases k<;>cases b<;>decide
 have hk2 d lb lo c0 cM pm (hv:ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm))
   (h2:lo+2<=lb+c0) (h1:lossB ka (cM.testBit ii)+lossB kb (cM.testBit jj)<=1):=
  validQS_noZ_kill ka kb hnd hi hj hne hop hfresh hv (by omega)
   (by cases ci:cM.testBit ii<;>cases cj:cM.testBit jj<;>simp[lossB,ci,cj]at h1 ⊢<;>omega)
 cases hk:kAll
 ·rw[hk,Bool.cond_false]at htrue;cases hkb:or ka kb
  ·rw[hkb,Bool.cond_false,Bool.and_eq_true,Bool.not_eq_true']at htrue
   cases h1:g2I.testBit ii
   ·obtain⟨d,lb,lo,c0,cM,pm,hv,h2,hf⟩:=hg2 ii hi h1;exact hk2 d lb lo c0 cM pm hv h2 (by simp[lossB,hf];exact hloss kb _)
   cases h2:g2I.testBit jj
   ·obtain⟨d,lb,lo,c0,cM,pm,hv,h2,hf⟩:=hg2 jj hj h2;exact hk2 d lb lo c0 cM pm hv h2 (by simp[lossB,hf];exact hloss ka _)
   have e:Nat.land g2I (Nat.lor (Nat.shiftLeft 1 ii) (Nat.shiftLeft 1 jj))=Nat.lor (Nat.shiftLeft 1 ii) (Nat.shiftLeft 1 jj):=
    Nat.eq_of_testBit_eq λb=>by rw[testBit_land',testBit_lor',shl1_tb,shl1_tb];by_cases e1:ii=b;subst e1;simp[h1];by_cases e2:jj=b;subst e2;simp[h2];simp[e1,e2]
   rw[e,Nat.beq_refl]at htrue;cases htrue.2
  ·rw[hkb,Bool.cond_true]at htrue;cases h01:k01
   ·rw[h01,Bool.cond_false]at htrue;cases ka<;>cases kb
    ·simp at hkb
    ·obtain⟨_,_,_,_,_,_,hv,_,hcj,hci⟩:=hg1 jj hj ii hi htrue
     exact validQS_noZ_kill false true hnd hi hj hne hop hfresh hv (by simp[lossB,hci];omega) (Or.inr (Or.inr hcj))
    ·obtain⟨_,_,_,_,_,_,hv,_,hci,hcj⟩:=hg1 ii hi jj hj htrue
     exact validQS_noZ_kill true false hnd hi hj hne hop hfresh hv (by simp[lossB,hcj];omega) (Or.inr (Or.inl hci))
    ·obtain⟨_,_,_,_,_,_,hv,_,hci,_⟩:=hg1 ii hi jj hj htrue
     exact validQS_noZ_kill true true hnd hi hj hne hop hfresh hv (by simp[lossB];omega) (Or.inr (Or.inl hci))
   ·obtain⟨d,lb,lo,c0,cM,pm,hv,h2⟩:=hk01 h01
    exact hk2 d lb lo c0 cM pm hv h2 (by cases ka<;>cases kb<;>cases cM.testBit ii<;>cases cM.testBit jj<;>simp[lossB]at hkb ⊢)
 ·obtain⟨_,_,_,_,cM,_,hv,_⟩:=hkA hk
  apply validQS_noZ_kill ka kb hnd hi hj hne hop hfresh hv (by have:=hloss ka (cM.testBit ii);have:=hloss kb (cM.testBit jj);omega)
  cases ka<;>cases kb<;>cases cM.testBit ii<;>cases cM.testBit jj<;>simp[lossB]<;>omega
private lemma zMatchD_elim {d z bl:Nat} {pm:List Nat} {ok1 r:Bool}
  (h:forceN (Nat.land (detVal z) (detVal d)) (λraw=>cond (or (isZeroS raw) (eqS (detVal d) raw)) true
   (cond ok1 (cond (bitTest bl (bloomIdx raw))
    (detS raw λmzD=>cond (navailNonConstD (detVal d) (pm.map detVal) mzD) true r) r) r))=true) :
  nconst d (Nat.land z d)=true\/(ok1=true/\navail d pm (Nat.land z d)=true)\/r=true:=by
 rw[forceN_eq,nconstRawD_eq,unS_land,unS_detVal,unS_detVal]at h
 cases hc:nconst d (Nat.land z d);swap;exact Or.inl rfl
 rw[hc]at h;cases ok1;· exact Or.inr (Or.inr h)
 rw[Bool.cond_false,Bool.cond_true]at h
 cases hb:bitTest bl (bloomIdx (Nat.land (detVal z) (detVal d)))
 ·rw[hb]at h;exact Or.inr (Or.inr h)
 rw[hb,Bool.cond_true,detS_eq,unS_land,unS_detVal,unS_detVal,navailNonConstD_eq]at h
 cases hn:or (anyEq (Nat.land z d) pm) (anyEq (Nat.xor d (Nat.land z d)) pm);· rw[hn]at h;exact Or.inr (Or.inr h)
 exact Or.inr (Or.inl ⟨rfl,by rw[navail,hc,Bool.false_or];exact hn⟩)
theorem checkWithZListD2_sound {nv goal kChild ii jj z:Nat} {ws:List Nat} {ka kb:Bool} {qps:List QS01D}
  (hnd:ws.Nodup) (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hfresh:z∉ws.toFinset)
  (hqps:∀q∈qps,ValidQSD nv goal kChild ws q)
  (htrue:checkWithZListD2 (detVal z) (Nat.shiftLeft 1 ii) (Nat.shiftLeft 1 jj)
   (keepMaskOf (Nat.sub (Nat.shiftLeft 1 ws.length) 1) (Nat.shiftLeft 1 ii) (Nat.shiftLeft 1 jj) ka kb) ka kb qps=true) :
  ImpossibleNv nv goal kChild (childSet ws ii jj z ka kb):=by
 set km:=keepMaskOf (Nat.sub (Nat.shiftLeft 1 ws.length) 1) (Nat.shiftLeft 1 ii) (Nat.shiftLeft 1 jj) ka kb
 obtain⟨nk,fk,hkm⟩:=kept_nd_fin ka kb hnd hi hj hfresh
 induction qps with| nil=>exact Bool.noConfusion htrue| cons hd _ ih=>
  rcases hd with ⟨_,_,lo,cM,uM,bl,_⟩;have vt q h:=hqps q (List.mem_cons_of_mem _ h)
  obtain⟨d,lb,c0,pm,rfl,rfl,rfl,vh⟩:=hqps _ List.mem_cons_self
  unfold checkWithZListD2 at htrue;dsimp only at htrue
  cases u:Nat.beq (Nat.land uM km) 0;· rw[u]at htrue;exact ih vt htrue
  rw[u,Bool.cond_true,loss_eq_bit,loss_eq_bit]at htrue;have u0:=Nat.eq_of_beq_eq_true u
  set hv:=Nat.sub (Nat.sub (lb+c0) (lossB ka (cM.testBit ii))) (lossB kb (cM.testBit jj))
  cases h0:Nat.ble lo hv;· rw[h0]at htrue;exact ih vt htrue
  rw[h0,Bool.cond_true]at htrue
  rcases @zMatchD_elim _ _ bl _ _ _ htrue with hc|⟨h1,hn⟩|hr
  rotate_left 2;exact ih vt hr
  all_goals
   have hvEq:hv=lb+c0-lossB ka (cM.testBit ii)-lossB kb (cM.testBit jj):=rfl
   have hcond:(lo+1<=hv/\navail d pm (Nat.land z d)=true)\/(lo<=hv/\nconst d (Nat.land z d)=true):=
    by first| exact Or.inr ⟨Nat.ble_eq.mp h0,hc⟩| exact Or.inl ⟨Nat.ble_eq.mp h1,hn⟩
   rcases vh with _|v;· rcases hcond with ⟨_,_⟩|⟨_,_⟩<;>omega
   have⟨_,_,_,_,_,_,_,_,df,_,h0',hM,_⟩:=v
   obtain⟨hl,_⟩:=kept_mass ka kb hi hj hne df;rw[<-h0']at hl
   have:lossB ka (cM.testBit ii)=lossB ka (nconst d (Nat.land (listGetN ws ii) d)):=by simp[lossB,hM ii,hi]
   have:lossB kb (cM.testBit jj)=lossB kb (nconst d (Nat.land (listGetN ws jj) d)):=by simp[lossB,hM jj,hj]
   exact @qs_kill_z _ _ _ _ _ _ _ _ _ _ (c0-lossB ka (cM.testBit ii)-lossB kb (cM.testBit jj)) _ _ _ _ (Or.inr v) (by omega) nk fk (λw hw=>by
    obtain⟨i,q,k,rfl⟩:=hkm w hw;have e:=congrArg (·.testBit i) u0
    have kb':km.testBit i=true:=by have:=of_decide_eq_true k;dsimp[km,keepMaskOf];cases ka<;>cases kb<;>simp<;>grind
    rw[testBit_land',kb',Bool.and_true,Nat.zero_testBit]at e;exact⟨i,q,e,rfl⟩)
    (λf' d'=>by obtain⟨_,m'⟩:=kept_mass ka kb hi hj hne d';rw[<-h0']at m';omega)
    (hcond.imp (λ⟨x,y⟩=>⟨by omega,y⟩) λ⟨x,y⟩=>⟨by omega,y⟩)
theorem kill11_sound {nv goal kChild ii jj op k11:Nat} {ws:List Nat}
  (hnd:ws.Nodup) (hi:ii<ws.length) (hj:jj<ws.length) (hne:ii≠jj) (hop:op<4)
  (hfresh:zN op (listGetN ws ii) (listGetN ws jj)∉ws.toFinset)
  (hk11:∀idx < ws.length,k11.testBit idx=true ->
   ∃d lb lo c0 cM pm,
    ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm) /\
    (lo+2<=lb+c0\/(lo+1<=lb+c0/\cM.testBit idx=true)))
  (hhit:k11.testBit ii=true\/k11.testBit jj=true) :
  ImpossibleNv nv goal kChild (insert (zN op (listGetN ws ii) (listGetN ws jj)) ws.toFinset):=by
 have go i (q:i<ws.length) (b:k11.testBit i=true) (e:i=ii\/i=jj) :
   ImpossibleNv nv goal kChild (childSet ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) true true):=by
  obtain⟨_,_,_,_,_,_,v,h2| ⟨h1,c⟩⟩:=hk11 i q b
  ·exact validQS_noZ_kill true true hnd hi hj hne hop hfresh v (by simp[lossB];omega) (Or.inl (by simp[lossB];omega))
  ·exact validQS_noZ_kill true true hnd hi hj hne hop hfresh v (by simp[lossB];omega) (Or.inr (e.elim (λh=>Or.inl (h▸c)) (λh=>Or.inr (h▸c))))
 exact hhit.elim (λh=>go ii hi h (Or.inl rfl)) (λh=>go jj hj h (Or.inr rfl))
theorem fastCost11ListD2_sound {nv goal kChild z:Nat} {ws:List Nat} {qps11:List QS11}
  (hnd:ws.Nodup) (hfresh:z∉ws.toFinset)
  (hqps11:∀q∈qps11,∃d lb lo c0 cM pm,q.1=detVal d/\q.2.2.2=pm.map detVal /\
   ValidQS nv goal kChild ws (d,lb,lo,c0,cM,0,pm)/\lo<=lb+c0/\(q.2.1=false->lo+1<=lb+c0))
  (htrue:fastCost11ListD2 (detVal z) qps11=true) :
  ImpossibleNv nv goal kChild (insert z ws.toFinset):=by
 induction qps11 with| nil=>exact Bool.noConfusion htrue| cons hd tl ih=>
  rcases hd with ⟨_,t,bl,_⟩;obtain⟨d,lb,lo,c0,cM,pm,rfl,rfl,v,g0,g1⟩:=hqps11 _ List.mem_cons_self
  unfold fastCost11ListD2 at htrue;dsimp at htrue
  rcases @zMatchD_elim _ _ bl _ (!t) _ (by cases t<;>exact htrue)with hnc| ⟨ht,hna⟩| hr
  rotate_left 2;exact ih (λq m=>hqps11 q (List.mem_cons_of_mem _ m)) hr
  all_goals
   have hc:(lo+1<=lb+c0/\navail d pm (Nat.land z d)=true)\/(lo<=lb+c0/\nconst d (Nat.land z d)=true):=
    by first| exact Or.inr ⟨g0,hnc⟩| exact Or.inl ⟨g1 (by cases t;rfl;cases ht),hna⟩
   exact qs_kill_z v (Nat.le_refl c0) (List.nodup_cons.mpr ⟨λm=>hfresh (List.mem_toFinset.mpr m),hnd⟩) (by simp)
    (λw m=>let⟨i,q,e⟩:=List.getElem_of_mem m;⟨i,q,Nat.zero_testBit _,e▸(listGetN_getElem q).symm⟩)
    (λf df=>by
     rcases v with _|⟨_,_,_,_,_,_,_,_,_,_,h0,_,_⟩;· rcases hc with ⟨_,_⟩|⟨_,_⟩<;>omega
     have e:(List.range ws.length).map (listGetN ws)=ws:=List.ext_getElem (by simp) λi _ q=>by simp[listGetN_getElem q]
     rw[h0];(conv_rhs=>rw[<-e]);exact countP_le_mass ws df _) hc
open PEqualNP.CircuitLowerBounds
private lemma shl_one (u:Nat):Nat.shiftLeft 1 u=2^u:=by
 change 1<<<u=2^u;rw[Nat.shiftLeft_eq,Nat.one_mul]
private lemma shl_eq (a n:Nat):Nat.shiftLeft a n=a*2^n:=Nat.shiftLeft_eq a n
private lemma shr_eq (a n:Nat):Nat.shiftRight a n=a / 2^n:=Nat.shiftRight_eq_div_pow a n
private lemma tb_shl (a n k:Nat) :
  (Nat.shiftLeft a n).testBit k=(decide (n<=k)&&a.testBit (k-n)):=by
 change (a<<<n).testBit k=_;exact Nat.testBit_shiftLeft a
private lemma tb_shr (a n k:Nat):(Nat.shiftRight a n).testBit k=a.testBit (n+k):=
 Nat.testBit_shiftRight a
private lemma bit0_tb (m:Nat):Nat.beq (Nat.land m 1) 1=m.testBit 0:=by
 have h1:Nat.land m 1=m % 2:=Nat.and_one_is_mod m
 rw[h1,Nat.testBit_zero]
 rcases(show m % 2=0\/m % 2=1 by omega)with h|h<;>rw[h]<;>decide
private lemma beq_f {a b:Nat} (h:a≠b):Nat.beq a b=false:=
 Bool.eq_false_iff.mpr λe=>h (Nat.eq_of_beq_eq_true e)
private lemma add_pow_self (k:Nat):Nat.add (2^k) (2^k)=2^(k+1):=by
 change 2^k+2^k=_;rw[Nat.pow_succ];omega
private lemma add_eq_lor {a b:Nat} (h:a&&&b=0):a+b=a|||b:=by
 induction a using Nat.strong_induction_on generalizing b with
 | ind a ih=>
  rcases Nat.eq_zero_or_pos a with rfl|ha;· simp
  have h0:a % 2=0\/b % 2=0:=by
   have:=congrArg (·.testBit 0) h;simp[Nat.testBit_zero]at this;omega
  have hd:(a / 2)&&&(b / 2)=0:=Nat.eq_of_testBit_eq λr=>by
   have:=congrArg (·.testBit (r+1)) h;simpa[Nat.testBit_and,Nat.testBit_div_two]using this
  have hr:=ih (a / 2) (Nat.div_lt_self ha (by decide)) hd
  apply Nat.eq_of_testBit_eq;rintro (_| r)
  ·have hm:(a+b) % 2=a % 2+b % 2:=by omega
   simp[Nat.testBit_zero,hm]
   rcases h0 with h'|h'<;>rw[h']<;>[rcases(show b % 2=0\/b % 2=1 by omega)with hb|hb;rcases(show a % 2=0\/a % 2=1 by omega)with ha'|ha']<;>simp[*]
  ·rw[Nat.testBit_or,<-Nat.testBit_div_two,<-Nat.testBit_div_two,<-Nat.testBit_div_two,<-Nat.testBit_or,<-hr]
   congr 1;omega
private lemma add_pow2_xor {m j:Nat} (h:m.testBit j=false):m+2^j=m^^^2^j:=by
 rw[add_eq_lor (Nat.eq_of_testBit_eq λk=>by rw[Nat.testBit_and,Nat.testBit_two_pow,Nat.zero_testBit];by_cases e:j=k<;>simp_all)]
 exact Nat.eq_of_testBit_eq λk=>by rw[Nat.testBit_or,Nat.testBit_xor,Nat.testBit_two_pow];by_cases e:j=k<;>simp_all
private def bitsOf (f:Nat->Bool):Nat->Nat
 | 0=>0
 | n+1=>bitsOf f n|||if f n then 1<<<n else 0
private lemma bitsOf_tb (f:Nat->Bool) (n k:Nat):(bitsOf f n).testBit k=(decide (k<n)&&f k):=by
 induction n with
 | zero=>simp[bitsOf]
 | succ m ih=>
  rw[bitsOf,Nat.testBit_or,ih]
  by_cases hk:k=m
  ·subst hk;cases f k<;>simp[Nat.shiftLeft_eq]
  ·cases f m<;>simp[Nat.shiftLeft_eq,Ne.symm hk,show(k < m+1)↔(k < m) by omega]
private lemma bitsOf_lt (f:Nat->Bool) (n:Nat):bitsOf f n<2^n:=
 lt_two_pow_of_testBit λk hk=>by rw[bitsOf_tb,decide_eq_false (Nat.not_lt_of_ge hk),Bool.false_and]
noncomputable def nodupN(l:List Nat):Bool:=
 @List.rec Nat (λ_=>Bool) true (λx xs ih=>cond (anyEq x xs) false ih) l
theorem nodupN_sound{l:List Nat}(h:nodupN l=true):l.Nodup:=by
 induction l with
 | nil=>exact List.nodup_nil
 | cons x xs ih=>
  change cond (anyEq x xs) false (nodupN xs)=true at h
  cases ha:anyEq x xs
  ·rw[ha,Bool.cond_false]at h
   exact List.nodup_cons.mpr ⟨λhm=>by rw[(anyEq_iff x xs).mpr hm]at ha;exact Bool.noConfusion ha,ih h⟩
  ·rw[ha,Bool.cond_true]at h;cases h
abbrev Row:=Fin 4096
abbrev Sig:=BitVec 4096
def zero:Sig:=0
def one:Sig:= ~~~zero
def bit(r:Row)(a:Sig):Bool:=a.getLsbD r.1
def neg(a:Sig):Sig:= ~~~a
def nrm(a:Sig):Sig:=if bit 0 a then neg a else a
def applyOp:Nat->Sig->Sig->Sig
 | 0,a,b=>a&&&b
 | 1,a,b=>a|||b
 | 2,a,b=>a&&&neg b
 | _,a,b=>neg a&&&b
def observe(a:Sig):Wire Row:=λr=>bit r a
def proper(a:Sig):Prop:=a≠zero/\a≠one
def plainWord(a:Sig):Bool:= !bit 0 a
def forceSig{β:Type}(s:Sig)(f:Sig->β):β:=BitVec.casesOn s λv=>f ⟨v⟩
private lemma forceSig_eq {β:Type} (s:Sig) (f:Sig->β):forceSig s f=f s:=by cases s;rfl
private lemma bit_ext {a b:Sig} (h:∀r:Row,bit r a=bit r b):a=b:=
 BitVec.eq_of_getLsbD_eq λi hi=>h ⟨i,hi⟩
private lemma bit_zero (r:Row):bit r zero=false:=BitVec.getLsbD_zero
private lemma bit_one (r:Row):bit r one=true:=by
 change (~~~(0#4096)).getLsbD r.1=true;rw[BitVec.getLsbD_not,BitVec.getLsbD_zero];simp[r.2]
private lemma bit_neg (r:Row) (a:Sig):bit r (neg a) = !bit r a:=by
 change (~~~a).getLsbD r.1 = !a.getLsbD r.1;rw[BitVec.getLsbD_not];simp[r.2]
private lemma bit_and (r:Row) (a b:Sig):bit r (a&&&b)=(bit r a&&bit r b):=BitVec.getLsbD_and
private lemma bit_or (r:Row) (a b:Sig):bit r (a|||b)=(bit r a||bit r b):=BitVec.getLsbD_or
private lemma nrm_zero:nrm zero=zero:=by simp[nrm,bit_zero]
private lemma nrm_one:nrm one=zero:=by
 apply bit_ext;intro r;simp[nrm,bit_one,bit_neg,bit_zero]
private lemma nrm_neg (a:Sig):nrm (neg a)=nrm a:=by
 apply bit_ext;intro r;simp[nrm,bit_neg];cases bit 0 a<;>simp[bit_neg]
private lemma nrm_id {a:Sig} (h:bit 0 a=false):nrm a=a:=by simp[nrm,h]
private lemma nrm_eq {a:Sig}:nrm a=a\/nrm a=neg a:=by unfold nrm;split<;>simp
private lemma bit0_nrm (a:Sig):bit 0 (nrm a)=false:=by
 unfold nrm;split<;>[rw[bit_neg];skip]<;>simp_all
private lemma proper_neg {a:Sig} (h:proper a):proper (neg a):=by
 refine⟨λe=>h.2 ?_,λe=>h.1 ?_⟩<;>(apply bit_ext;intro r;have hr:=congrArg (bit r) e;simp[bit_neg,bit_zero,bit_one]at hr ⊢;exact hr)
private lemma proper_nrm {a:Sig} (h:proper a):proper (nrm a):=by
 rcases nrm_eq (a:=a)with e|e<;>[rw[e];rw[e]]
 ·exact h
 ·exact proper_neg h
private lemma bit_applyOp (r:Row) (d:Nat) (a b:Sig) :
  bit r (applyOp d a b)=comb d (observe a) (observe b) r:=by
 rcases d with _|_|_|d<;>simp[applyOp,comb,binBool,observe,bit_and,bit_or,bit_neg]
private lemma observe_proper {a:Sig} (h:proper a):¬Constant (observe a):=by
 rintro⟨b,hb⟩;cases b
 ·exact h.1 (bit_ext λr=>(congrFun hb r).trans (bit_zero r).symm)
 ·exact h.2 (bit_ext λr=>(congrFun hb r).trans (bit_one r).symm)
private lemma applyOp_nrm (op:Bool) (a b:Sig) :
  ∃d < 4,nrm (if op then a|||b else a&&&b)=applyOp d (nrm a) (nrm b):=by
 have case4:∀x y:Sig,bit 0 x=false->bit 0 y=false ->
   nrm (if op then x|||y else x&&&y)=applyOp (if op then 1 else 0) x y /\
   nrm (if op then x|||neg y else x&&&neg y)=applyOp (if op then 3 else 2) x y /\
   nrm (if op then neg x|||y else neg x&&&y)=applyOp (if op then 2 else 3) x y /\
   nrm (if op then neg x|||neg y else neg x&&&neg y)=applyOp (if op then 0 else 1) x y:=by
  intro x y hx hy
  refine⟨?_,?_,?_,?_⟩<;>(apply bit_ext;intro r;cases op<;>simp[ite_true,nrm,applyOp,bit_and,bit_or,bit_neg,hx,hy,Bool.not_false,Bool.and_false,Bool.or_false,Bool.and_true,Bool.or_true,ite_false,Bool.false_eq_true]<;>cases bit r x<;>cases bit r y<;>rfl)
 have c:=case4 (nrm a) (nrm b) (bit0_nrm a) (bit0_nrm b)
 have h1:∀w:Sig,w=nrm w\/w=neg (nrm w):=λw=>by
  unfold nrm;split
  ·right;apply bit_ext;intro r;simp[bit_neg]
  ·left;rfl
 rcases h1 a with ha|ha<;>rcases h1 b with hb|hb
 ·exact⟨if op then 1 else 0,by cases op<;>decide,by conv_lhs=>rw[ha,hb];exact c.1⟩
 ·exact⟨if op then 3 else 2,by cases op<;>decide,by conv_lhs=>rw[ha,hb];exact c.2.1⟩
 ·exact⟨if op then 2 else 3,by cases op<;>decide,by conv_lhs=>rw[ha,hb];exact c.2.2.1⟩
 ·exact⟨if op then 0 else 1,by cases op<;>decide,by conv_lhs=>rw[ha,hb];exact c.2.2.2⟩
def inputs:List Sig:=(List.range 12).map λu=>BitVec.ofNat 4096 (hiC12 u)
theorem input_coords(i:Fin 12)(r:Row):bit r (inputs.getD i.1 zero)=r.1.testBit i.1:=by
 have hi:i.1 < inputs.length:=by simp[inputs,i.2]
 rw[List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
 simp only[inputs,List.getElem_map,List.getElem_range,bit,BitVec.getLsbD_ofNat,r.2,decide_true,Bool.true_and]
 exact hiC12_bits i r
theorem inputs_inj{i j:Fin 12}(h:inputs.getD i.1 zero=inputs.getD j.1 zero):i=j:=by
 apply Fin.ext;by_contra hne
 have hlt:2^i.1<4096:=lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) i.2) (by decide)
 have hbit:=congrArg (bit ⟨2^i.1,hlt⟩) h
 rw[input_coords,input_coords,Nat.testBit_two_pow_self,Nat.testBit_two_pow]at hbit
 simp[hne]at hbit
def Live(T:Sig):Nat->Finset Sig->Prop
 | 0,S=>S={T}/\proper T
 | k+1,S=>∃U a b d,d<4/\S=insert a (insert b U)/\proper a/\proper b/\a≠b /\
  applyOp d a b∉insert a (insert b U)/\Live T k (insert (applyOp d a b) U)
def Impossible(T:Sig)(cap:Nat)(S:Finset Sig):Prop:=∀k,k<=cap->¬Live T k S
def Lower(raw:List Sig)(T:Sig)(L:Nat):Prop:=
 ∀p bank,Reach (raw.map observe) p bank->Available bank (observe T)->L<=p
def Essential(T:Sig)(raw:List Sig)(a:Sig):Prop:=
 ∃r s:Row,bit r T≠bit s T/\∀v∈raw,v≠a->bit r v=bit s v
private lemma live_ind {T:Sig} {motive:∀k S,Live T k S->Prop}
  (stop:∀hp:proper T,motive 0 {T} ⟨rfl,hp⟩)
  (step:∀{k U a b d}(hd:d<4)(ha:proper a)(hb:proper b)(hab:a≠b)
   (hf:applyOp d a b∉insert a (insert b U)) (tl:Live T k (insert (applyOp d a b) U)),
   motive k _ tl->motive (k+1) (insert a (insert b U)) ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tl⟩)
  {k S} (h:Live T k S):motive k S h:=by
 induction k generalizing S with
 | zero=>obtain⟨rfl,hp⟩:=h;exact stop hp
 | succ k ih=>obtain⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tl⟩:=h;exact step hd ha hb hab hf tl (ih tl)
private lemma live_size {T k S} (h:Live T k S):S.card<=k+1:=by
 induction h using live_ind with
 | stop _=>simp
 | @step k U a b d _ _ _ _ hf _ ih=>
  have hu:applyOp d a b∉U:=λhm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  rw[Finset.card_insert_of_notMem hu]at ih
  have:=Finset.card_insert_le (a:=a) (s:=insert b U)
  have:=Finset.card_insert_le (a:=b) (s:=U);omega
private lemma live_row_diff {T k S} (h:Live T k S) {r s:Row} (hd:bit r T≠bit s T) :
  ∃a∈S,bit r a≠bit s a:=by
 induction h using live_ind with
 | stop _=>exact⟨T,by simp,hd⟩
 | @step k U a b d _ _ _ _ _ _ ih=>
  obtain⟨v,hv,hdv⟩:=ih
  rcases Finset.mem_insert.mp hv with rfl|hu
  ·by_cases ha:bit r a=bit s a
   ·refine⟨b,by simp,λhb=>hdv ?_⟩
    rw[bit_applyOp,bit_applyOp];change comb d (observe a) (observe b) r=comb d (observe a) (observe b) s
    simp[comb,observe,ha,hb]
   ·exact⟨a,by simp,ha⟩
  ·exact⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hdv⟩
private lemma raw_required {T k S} (h:Live T k S) (raw:List Sig) (a:Sig)
  (sub:∀v∈S,v∈raw) (r s:Row) (hd:bit r T≠bit s T)
  (iso:∀v∈raw,v≠a->bit r v=bit s v):a∈S:=by
 obtain⟨v,hv,hdv⟩:=live_row_diff h hd
 by_contra ha;exact hdv (iso v (sub v hv) λe=>ha (e▸hv))
private lemma live_proper {T k S} (h:Live T k S):∀x∈S,proper x:=by
 induction h using live_ind with
 | stop hp=>simpa using hp
 | step _ ha hb _ _ _ ih=>simp[Finset.forall_mem_insert];exact⟨ha,hb,λx hx=>ih x (Finset.mem_insert_of_mem hx)⟩
private lemma live_step_of_bin {T k S} (h:Live T k S) {a b z:Sig} {d:Nat}
  (hd:d<4) (ha:proper a) (hb:proper b) (hz:z=applyOp d a b) :
  ∃m≤k+1,∃S',Live T m S'/\∀x∈S',x=a\/x=b\/(x∈S/\x≠z):=by
 by_cases hmem:z∈S
 ·by_cases hza:z=a
  ·exact⟨k,Nat.le_succ _,S,h,λx hx=>if e:x=a then Or.inl e else Or.inr (Or.inr ⟨hx,hza.symm▸e⟩)⟩
  ·by_cases hzb:z=b
   ·exact⟨k,Nat.le_succ _,S,h,λx hx=>if e:x=b then Or.inr (Or.inl e)else Or.inr (Or.inr ⟨hx,hzb.symm▸e⟩)⟩
   ·by_cases hab:a=b
    ·subst hab;exfalso;have hpz:=live_proper h z hmem
     rcases lt4_cases hd with rfl|rfl|rfl|rfl
     ·exact hza (hz.trans (bit_ext λr=>by simp[applyOp]))
     ·exact hza (hz.trans (bit_ext λr=>by simp[applyOp]))
     ·exact hpz.1 (hz.trans (bit_ext λr=>by simp[applyOp,bit_and,bit_neg,bit_zero]))
     ·exact hpz.1 (hz.trans (bit_ext λr=>by simp[applyOp,bit_and,bit_neg,bit_zero]))
    ·exact⟨k+1,Nat.le_refl _,insert a (insert b (S.erase z)),
      ⟨S.erase z,a,b,d,hd,rfl,ha,hb,hab,by rw[<-hz];simp[hza,hzb],hz▸(Finset.insert_erase hmem).symm▸h⟩,
      λx hx=>by simp[Finset.mem_insert,Finset.mem_erase]at hx;tauto⟩
 ·exact⟨k,Nat.le_succ _,S,h,λx hx=>Or.inr (Or.inr ⟨hx,λe=>hmem (e▸hx)⟩)⟩
def isNot(g:Gate):Bool:=match g.op with| .not=>true| _=>false
def runGate(w:List Sig)(g:Gate):Sig:=
 let xs:=g.inputs.map (λj=>w.getD j zero)
 match g.op with
 | .and=>xs.foldr (·&&&·) one
 | .or=>xs.foldr (·|||·) zero
 | .not=>neg (xs.headD zero)
 | _=>zero
def execute(gs:List Gate)(w:List Sig):List Sig:=gs.foldl (λw g=>w++[runGate w g]) w
private lemma b_read (i:Row) (w:List Sig) (j:Nat) :
  (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
 simp[List.getElem?_map];cases w[j]? with| none=>exact(bit_zero _).symm| some _=>rfl
private lemma run_bit (i:Row) (g:Gate) (w:List Sig)
  (hg:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)) :
  bit i (runGate w g)=g.op.eval (g.inputs.map λj=>(w.map (bit i)).getD j false):=by
 obtain⟨o,l⟩:=g;simp only[Set.mem_insert_iff,Set.mem_singleton_iff]at hg;simp only[b_read]
 rcases hg with rfl|rfl|rfl
 ·induction l with
  | nil=>exact bit_one _
  | cons a l ih=>simp only[runGate,List.map_cons,List.foldr_cons,GateOp.eval,bit,BitVec.getLsbD_and]at ih ⊢;exact congrArg (_&&·) ih
 ·induction l with
  | nil=>exact bit_zero _
  | cons a l ih=>simp only[runGate,List.map_cons,List.foldr_cons,GateOp.eval,bit,BitVec.getLsbD_or]at ih ⊢;exact congrArg (_||·) ih
 ·cases l with
  | nil=>change bit i (neg zero) = !false;rw[bit_neg,bit_zero]
  | cons _ _=>exact bit_neg _ _
private lemma execute_bits (gs:List Gate) (i:Row) (w:List Sig)
  (hg:∀g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)) :
  (execute gs w).map (bit i) =
   gs.foldl (λ(l:List Bool) g=>l++[g.op.eval (g.inputs.map λj=>l.getD j false)]) (w.map (bit i)):=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  change (execute gs (w++[runGate w g])).map _=_
  rw[ih _ (λa ha=>hg a (by simp[ha]))]
  simp[List.foldl_cons,List.map_append,run_bit i g w (hg g (by simp))]
private lemma pull_gate {target k S} (h:Live target k S) {w:List Sig} {z:Sig} {costG:Nat}
  (rep:(z=zero\/z=one\/z∈w) \/
   (costG=1/\∃d a b,d<4/\a∈w/\b∈w/\proper a/\proper b/\z=applyOp d a b))
  (sub:∀a∈S,a∈w++[z]) :
  ∃l T,l<=k+costG/\Live target l T/\∀a∈T,a∈w:=by
 have sub_w:∀x∈S,x≠z->x∈w:=λx hx hne=>by have:=sub x hx;simp[hne]at this;exact this
 by_cases hm:z∈S
 ·rcases rep with (rfl|rfl|hw)|⟨rfl,d,a,b,hd,ha,hb,pa,pb,hz⟩
  ·exact absurd rfl (live_proper h zero hm).1
  ·exact absurd rfl (live_proper h one hm).2
  ·exact⟨k,S,by omega,h,λx hx=>if e:x=z then e▸hw else sub_w x hx e⟩
  ·obtain⟨m,hmle,S',hlive',hsub'⟩:=live_step_of_bin h hd pa pb hz
   refine⟨m,S',hmle,hlive',λx hx=> ?_⟩
   rcases hsub' x hx with rfl|rfl|⟨hs,hne⟩<;>first| exact ha| exact hb| exact sub_w x hs hne
 ·exact⟨k,S,by omega,h,λx hx=>sub_w x hx λe=>hm (e▸hx)⟩
private lemma bin_rep {ws:List Sig} (opB:Bool) {x y:Sig}
  (hx:x=zero\/x=one\/nrm x∈ws) (hy:y=zero\/y=one\/nrm y∈ws) :
  let z:=nrm (if opB then x|||y else x&&&y)
  (z=zero\/z=one\/z∈ws)\/∃d a b,d<4/\a∈ws/\b∈ws/\proper a/\proper b/\z=applyOp d a b:=by
 have hconst (u v:Sig) (hu:u=zero\/u=one) (hv:v=zero\/v=one\/nrm v∈ws) :
   let z:=nrm (if opB then u|||v else u&&&v);z=zero\/z=one\/z∈ws:=by
  have e1:zero&&&v=zero:=bit_ext λr=>by simp[bit_and,bit_zero]
  have e2:one&&&v=v:=bit_ext λr=>by simp[bit_and,bit_one]
  have e3:zero|||v=v:=bit_ext λr=>by simp[bit_or,bit_zero]
  have e4:one|||v=one:=bit_ext λr=>by simp[bit_or,bit_one]
  rcases hu with rfl|rfl<;>cases opB<;>simp only[Bool.false_eq_true,ite_true,ite_false,e1,e2,e3,e4,nrm_zero,nrm_one]
  ·exact Or.inl trivial
  ·rcases hv with rfl|rfl|hm<;>[exact Or.inl nrm_zero;exact Or.inl nrm_one;exact Or.inr (Or.inr hm)]
  ·rcases hv with rfl|rfl|hm<;>[exact Or.inl nrm_zero;exact Or.inl nrm_one;exact Or.inr (Or.inr hm)]
  ·exact Or.inl trivial
 by_cases px:proper x;swap;exact Or.inl (hconst x y (by by_contra hc;exact px ⟨λh=>hc (Or.inl h),λh=>hc (Or.inr h)⟩) hy)
 by_cases py:proper y;swap
 ·have hcomm:(if opB then x|||y else x&&&y)=(if opB then y|||x else y&&&x):=by cases opB<;>exact bit_ext λr=>by simp[bit_and,bit_or,Bool.and_comm,Bool.or_comm]
  exact Or.inl (by change nrm _=_\/_\/_;rw[hcomm];exact hconst y x (by by_contra hc;exact py ⟨λh=>hc (Or.inl h),λh=>hc (Or.inr h)⟩) hx)
 rcases hx with rfl|rfl|hxm;exact absurd rfl px.1;exact absurd rfl px.2
 rcases hy with rfl|rfl|hym;exact absurd rfl py.1;exact absurd rfl py.2
 obtain⟨d,hd,heq⟩:=applyOp_nrm opB x y;exact Or.inr ⟨d,nrm x,nrm y,hd,hxm,hym,proper_nrm px,proper_nrm py,heq⟩
private lemma gate_rep (w:List Sig) (g:Gate)
  (h:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2) :
  let wn:=w.map nrm;let z:=nrm (runGate w g)
  (z=zero\/z=one\/z∈wn)\/(isNot g=false/\∃d a b,d<4/\a∈wn/\b∈wn/\proper a/\proper b/\z=applyOp d a b):=by
 obtain⟨o,l⟩:=g;obtain⟨ho,hlen⟩:=h;simp[Set.mem_insert_iff,Set.mem_singleton_iff]at ho
 have memN idx:w.getD idx zero=zero\/w.getD idx zero=one\/nrm (w.getD idx zero)∈w.map nrm:=by
  simp only[List.getD_eq_getElem?_getD];cases hq:w[idx]? with| none=>exact Or.inl rfl| some _=>exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? hq)))
 have oneArg idx:let z:=nrm (w.getD idx zero);z=zero\/z=one\/z∈w.map nrm:=by
  rcases memN idx with h0|h1|hm;exact Or.inl (by rw[h0];exact nrm_zero);exact Or.inl (by rw[h1];exact nrm_one);exact Or.inr (Or.inr hm)
 rcases ho with rfl|rfl|rfl
 ·match l,hlen with
  | [],_=>exact Or.inl (Or.inl nrm_one)
  | [i],_=>exact Or.inl (by change nrm (runGate w ⟨.and,[i]⟩)=_\/_\/_;rw[show runGate w ⟨.and,[i]⟩=w.getD i zero from bit_ext λr=>by simp[runGate,bit_and,bit_one]];exact oneArg i)
  | [i,j],_=>change (nrm (runGate w ⟨.and,[i,j]⟩)=_\/_\/_)\/_;rw[show runGate w ⟨.and,[i,j]⟩=w.getD i zero&&&w.getD j zero from bit_ext λr=>by simp[runGate,bit_and,bit_one]];exact(bin_rep false (memN i) (memN j)).imp id (⟨rfl,·⟩)
 ·match l,hlen with
  | [],_=>exact Or.inl (Or.inl nrm_zero)
  | [i],_=>exact Or.inl (by change nrm (runGate w ⟨.or,[i]⟩)=_\/_\/_;rw[show runGate w ⟨.or,[i]⟩=w.getD i zero from bit_ext λr=>by simp[runGate,bit_or,bit_zero]];exact oneArg i)
  | [i,j],_=>change (nrm (runGate w ⟨.or,[i,j]⟩)=_\/_\/_)\/_;rw[show runGate w ⟨.or,[i,j]⟩=w.getD i zero|||w.getD j zero from bit_ext λr=>by simp[runGate,bit_or,bit_zero]];exact(bin_rep true (memN i) (memN j)).imp id (⟨rfl,·⟩)
 ·cases l with| nil=>exact Or.inl (Or.inl (by simp[runGate,nrm_neg,nrm_zero]))| cons i _=>exact Or.inl (by change nrm (runGate w ⟨.not,i::_⟩)=_\/_\/_;simp only[runGate,List.map_cons,List.headD_cons,nrm_neg];exact oneArg i)
private lemma extract {target} (gs:List Gate) (w:List Sig)
  (legal:∀g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2)
  (hp:proper target) (hout:target∈(execute gs w).map nrm) :
  ∃k S,k<=gs.countP (λg=> !isNot g)/\Live target k S/\∀a∈S,a∈w.map nrm:=by
 induction gs generalizing w with
 | nil=>exact⟨0,{target},by simp,⟨rfl,hp⟩,by simpa[execute]using hout⟩
 | cons g gs ih=>
  obtain⟨k,S,hk,ht,hs⟩:=ih (w++[runGate w g]) (λa ha=>legal a (by simp[ha])) hout
  rw[List.map_append]at hs
  obtain⟨l,T,hl,hu,hT⟩:=@pull_gate _ _ _ ht _ _ (if isNot g then 0 else 1) ((gate_rep w g (legal g (by simp))).imp id λh=>⟨by simp[h.1],h.2⟩) hs
  exact⟨l,T,by rw[List.countP_cons];cases hn:isNot g<;>simp[hn]at hl ⊢<;>omega,hu,hT⟩
private lemma reach_live {raw:List Sig} {T:Sig} (hpT:proper T) (hT:plainWord T=true)
  (hR:raw.all plainWord=true) {p bank} (hr:Reach (raw.map observe) p bank) (ha:Available bank (observe T)) :
  ∃k S,k<=p/\Live T k S/\∀a∈S,a∈raw:=by
 have toSig (w:Wire Row):∃s:Sig,observe s=w:=
  ⟨BitVec.ofNat 4096 (bitsOf (λi=>if h:i<4096 then w ⟨i,h⟩ else false) 4096),
   funext λr=>by simp only[observe,bit,BitVec.getLsbD_ofNat,r.2,decide_true,Bool.true_and,bitsOf_tb,dite_true]⟩
 have hrep {ws:List Sig} {u:Sig} (hu:Available (ws.map observe) (observe u)):u=zero\/u=one\/nrm u∈ws.map nrm:=by
  rcases hu with hm|⟨c,hc⟩|hi
  ·obtain⟨v,hv,he⟩:=List.mem_map.mp hm;exact Or.inr (Or.inr ((bit_ext λr=>congrFun he r)▸List.mem_map_of_mem hv))
  ·cases c<;>[exact Or.inl (bit_ext λr=>(congrFun hc r).trans (bit_zero r).symm);exact Or.inr (Or.inl (bit_ext λr=>(congrFun hc r).trans (bit_one r).symm))]
  ·obtain⟨v,hv,he⟩:=List.mem_map.mp hi
   exact Or.inr (Or.inr (by rw[<-(bit_ext λr=>by rw[bit_neg];have h1:=congrFun he r;simp[observe,inv]at h1;rw[h1,Bool.not_not]:neg v=u),nrm_neg];exact List.mem_map_of_mem hv))
 have hbuild:∀{q bk},Reach (raw.map observe) q bk->∃ws:List Sig,bk=ws.map observe /\
   ∀k S,Live T k S->(∀a∈S,a∈ws.map nrm)->∃l U,l<=q+k/\Live T l U/\∀a∈U,a∈raw:=λ{q}=>by
  induction q with
  | zero=>intro bk h;exact⟨raw,h,λk S hl hs=>⟨k,S,by omega,hl,λa ha=>by
    obtain⟨r,hr,rfl⟩:=List.mem_map.mp (hs a ha);have hpr:=List.all_eq_true.mp hR r hr;simp[plainWord]at hpr;rwa[nrm_id hpr]⟩⟩
  | succ q ih=>
   intro bk ⟨_,a,b,op,hrp,ha',hb',hbk⟩;subst hbk;obtain⟨ws,rfl,hws⟩:=ih hrp
   obtain⟨sa,hsa⟩:=toSig a;obtain⟨sb,hsb⟩:=toSig b;let c:=if op then sa|||sb else sa&&&sb
   have hsc:observe c=combine op a b:=by rw[<-hsa,<-hsb];funext r;cases op<;>simp[c,observe,combine,bit_and,bit_or]
   refine⟨c::ws,by simp[hsc],λk S hl hs=> ?_⟩
   obtain⟨l1,U1,hl1,hlive1,hsub1⟩:=@pull_gate _ _ _ hl _ _ 1 ((bin_rep op (hrep (hsa.symm▸ha')) (hrep (hsb.symm▸hb'))).imp id (⟨rfl,·⟩))
    (show ∀x∈S,x∈ws.map nrm++[nrm c] from λx hx=>(List.mem_cons.mp (List.map_cons ..▸hs x hx)).elim (λe=>List.mem_append_right _ (by simp[e])) (List.mem_append_left _))
   obtain⟨l2,U2,hl2,hlive2,hsub2⟩:=hws l1 U1 hlive1 hsub1;exact⟨l2,U2,by omega,hlive2,hsub2⟩
 obtain⟨ws,rfl,hws⟩:=hbuild hr
 have hTmem:T∈ws.map nrm:=by rcases hrep ha with rfl|rfl|hm;exact absurd rfl hpT.1;exact absurd rfl hpT.2;simp[plainWord]at hT;rwa[nrm_id hT]at hm
 obtain⟨k,S,hk,hl,hs⟩:=hws 0 {T} ⟨rfl,hpT⟩ (λa ha=>(Finset.mem_singleton.mp ha)▸hTmem);exact⟨k,S,by omega,hl,hs⟩
private lemma list_run {T k S} (h:Live T k S) (v:List Sig) (hv:v.Nodup) (he:v.toFinset=S):Run (observe T) k (v.map observe):=by
 classical
 induction h using live_ind generalizing v with
 | stop _=>exact Run.perm ((List.perm_of_nodup_nodup_toFinset_eq hv (List.nodup_singleton T) (by simpa using he)).symm.map _) Run.stop
 | @step k U a b d hd _ _ hab hf tl ih=>
  let rest:=(v.erase a).erase b;have hr:rest.Nodup:=(hv.erase a).erase b
  have er:rest.toFinset=((insert a (insert b U)).erase a).erase b:=by ext x;simp[rest,(hv.erase a).mem_erase_iff,hv.mem_erase_iff,<-he]
  have hrestU x:x∈rest↔x∈U/\x≠a/\x≠b:=by rw[<-List.mem_toFinset,er];simp[Finset.mem_erase,Finset.mem_insert];tauto
  have ar:a∉rest:=λhm=>(hrestU a).mp hm |>.2.1 rfl;have br:b∉rest:=λhm=>(hrestU b).mp hm |>.2.2 rfl
  let ka:=decide (a∈U);let kb:=decide (b∈U);let tailL:=kept ka a (kept kb b rest)
  have hnd_t:tailL.Nodup:=by cases hka:ka<;>cases hkb:kb<;>simp[tailL,kept,hka,hkb,hr,ar,br,hab]
  have hmem_t x:x∈tailL↔x∈U:=by
   have haU:(a∈U)↔ka=true:=(decide_eq_true_iff ..).symm;have hbU:(b∈U)↔kb=true:=(decide_eq_true_iff ..).symm
   cases hka:ka<;>cases hkb:kb<;>(rw[hka]at haU;rw[hkb]at hbU;simp[tailL,kept];grind)
  have prog:=ih (applyOp d a b::tailL) (List.nodup_cons.mpr ⟨λhm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((hmem_t _).mp hm))),hnd_t⟩) (by ext x;simp[hmem_t])
  have hm (sv:Bool) x xs:(kept sv x xs).map observe=kept sv (observe x) (xs.map observe):=by cases sv<;>rfl
  rw[List.map_cons,show observe (applyOp d a b)=comb d (observe a) (observe b) from funext λr=>bit_applyOp r d a b,hm,hm]at prog
  exact Run.perm ((List.perm_of_nodup_nodup_toFinset_eq (show(a::b::rest).Nodup by simp[hab,ar,br,hr]) hv
   (by ext x;simp[List.toFinset_cons,Finset.mem_insert,he,er,Finset.mem_erase];by_cases hxa:x=a<;>by_cases hxb:x=b<;>simp[hxa,hxb])).map _) (Run.two d hd ka kb prog)
private lemma lower_impossible {raw T cap} (hpT:proper T) (hT:plainWord T=true) (hR:raw.all plainWord=true)
  (ess:∀a∈raw,Essential T raw a) (himp:Impossible T cap raw.toFinset):Lower raw T (cap+1):=λp bank hr ha=>by
 obtain⟨k,S,hk,hl,sub⟩:=reach_live hpT hT hR hr ha
 have hS:S=raw.toFinset:=by ext a;rw[List.mem_toFinset];exact⟨sub a,λhm=>let⟨r,s,hd,iso⟩:=ess a hm;raw_required hl raw a sub r s hd iso⟩
 by_contra hlt;exact himp k (by omega) (hS▸hl)
private lemma lower_slice {raw T base G L} (hpT:proper T) (hT:plainWord T=true) (hR:raw.all plainWord=true)
  (hpG:proper G) (r:Row->Row) (eq:restrictRows r (observe T)=observe G)
  (cov:∀a∈raw,Available (base.map observe) (restrictRows r (observe a)))
  (singles:Finset Sig) (ess:∀a∈singles,Essential T raw a) (const:∀a∈singles,Constant (restrictRows r (observe a)))
  (prior:Lower base G L):Lower raw T (L+singles.card):=by
 classical
 intro p bank hr ha;obtain⟨k,S,hk,hl,sub⟩:=reach_live hpT hT hR hr ha
 have hsub:singles⊆S:=λa ha=>let⟨r1,r2,hd,iso⟩:=ess a ha;raw_required hl raw a sub r1 r2 hd iso
 let front:=singles.toList++(S \ singles).toList
 have hnd:front.Nodup:=List.nodup_append.mpr ⟨Finset.nodup_toList _,Finset.nodup_toList _,λ_ ha _ hb e=>(Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (e▸Finset.mem_toList.mp ha)⟩
 have hfin:front.toFinset=S:=by ext a;simp only[front,List.toFinset_append,Finset.mem_union,List.mem_toFinset,Finset.mem_toList,Finset.mem_sdiff];exact⟨λh=>h.elim (λha=>hsub ha) And.left,λha=>if hs:a∈singles then Or.inl hs else Or.inr ⟨ha,hs⟩⟩
 have hpb:=projected_bound r (list_run hl front hnd hfin) (eq▸observe_proper hpG) Reach.start (λ_ hv=>by obtain⟨_,hm,rfl⟩:=List.mem_map.mp hv;obtain⟨a,hmem,rfl⟩:=List.mem_map.mp hm;exact cov a (sub a (by rwa[<-hfin,List.mem_toFinset]))) (λq out hro hgo=>prior q out hro (eq▸hgo))
 have hmass_c:∀xs:List (Wire Row),(∀v∈xs,Constant v)->mass xs=xs.length:=λxs=>by
  induction xs with| nil=>exact λ_=>rfl| cons x _ ih=>intro hc;rw[mass_cons,show cost x=1 by simp[cost,hc x (by simp)],ih λv hv=>hc v (by simp[hv])];simp;omega
 have h1:=hmass_c ((singles.toList.map observe).map (restrictRows r)) λ_ hv=>by obtain⟨_,hm,rfl⟩:=List.mem_map.mp hv;obtain⟨a,ha,rfl⟩:=List.mem_map.mp hm;exact const a (Finset.mem_toList.mp ha)
 simp[front,List.map_append,mass,List.sum_append,List.length_map,Finset.length_toList]at h1 hpb;omega
abbrev Move:=Sig×Sig×Row
def shifted(d r:Row):Row:=if h:r.1+d.1<4096 then ⟨r.1+d.1,h⟩ else ⟨r.1+d.1-4096,by omega⟩
def backwards(d:Row):Row:=Fin.ofNat 4096 (4096-d.1)
def rowMove(m:Move)(r:Row):Row:=if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux(m a b:Sig):Sig:=if m==zero then b else(m&&&a)|||(~~~m&&&b)
def wordMove(m:Move)(a:Sig):Sig:=mux m.1 (a.rotateRight m.2.2.1) (mux m.2.1 (a.rotateRight (backwards m.2.2).1) a)
def movedRow(ms:List Move)(r:Row):Row:=ms.foldl (λj m=>rowMove m j) r
def movedWord(ms:List Move)(a:Sig):Sig:=ms.foldr wordMove a
private lemma bit_moved (ms:List Move) (a:Sig) (r:Row):bit r (movedWord ms a)=bit (movedRow ms r) a:=by
 have hbm:∀(m:Move)(w:Sig)(j:Row),bit j (wordMove m w)=bit (rowMove m j) w:=λm w j=>by
  have hsh:∀(d x:Row)(s:Sig),bit x (s.rotateRight d.1)=bit (shifted d x) s:=λd x s=>by
   simp[bit,x.2,shifted,Nat.mod_eq_of_lt d.2]
   split_ifs<;>(apply congrArg (BitVec.getLsbD s);dsimp;omega)
  have hmx:∀(x:Row)(p u v:Sig),bit x (mux p u v)=if bit x p then bit x u else bit x v:=λx p u v=>by
   unfold mux;by_cases hp:(p==zero)=true
   ·rw[beq_iff_eq.mp hp];simp[bit_zero]
   ·rw[if_neg hp];rw[bit_or,bit_and,bit_and];change (bit x p&&bit x u||bit x (neg p)&&bit x v)=_
    rw[bit_neg];cases bit x p<;>simp
  simp[wordMove,rowMove,hmx,hsh];split_ifs<;>rfl
 induction ms generalizing r with
 | nil=>rfl
 | cons m ms ih=>exact(hbm m _ r).trans (ih _)
def freeWord(roots:List Sig)(w:Sig):Bool:=w==zero||w==one||roots.contains w
def checkMap(ms:List Move)(raw:List Sig)(T:Sig)(base:List Sig)(G:Sig):Bool:=
 (movedWord ms T==G)&&raw.all (λa=>freeWord base (movedWord ms a))
private lemma map_correct {ms raw T base G} (ok:checkMap ms raw T base G=true) :
  restrictRows (movedRow ms) (observe T)=observe G /\
  ∀a∈raw,Available (base.map observe) (restrictRows (movedRow ms) (observe a)):=by
 simp[checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true]at ok
 refine⟨funext λr=>(bit_moved ms T r).symm.trans (congrArg (bit r) ok.1),λa ha=> ?_⟩
 have hf:=ok.2 a ha
 simp[freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq]at hf
 have heq:restrictRows (movedRow ms) (observe a)=observe (movedWord ms a):=funext λr=>(bit_moved ms a r).symm
 rw[heq];rcases hf with (h|h)|hm
 ·exact Or.inr (Or.inl ⟨false,funext λr=>by rw[h];exact bit_zero r⟩)
 ·exact Or.inr (Or.inl ⟨true,funext λr=>by rw[h];exact bit_one r⟩)
 ·exact Or.inl (List.mem_map_of_mem hm)
private lemma lower_map {ms raw T base G L} (ok:checkMap ms raw T base G=true) (prior:Lower base G L):Lower raw T L:=by
 obtain⟨heq,cov⟩:=map_correct ok;intro p bank hr ha
 have lift:∀{q bk},Reach (raw.map observe) q bk->∃next,Reach (base.map observe) q next/\∀v,Available bk v->Available next (restrictRows (movedRow ms) v):=λ{q}=>by
  induction q with
  | zero=>intro bk h;exact⟨base.map observe,Reach.start,λv hv=>by
    rcases h▸hv with hm|⟨b,rfl⟩|hm
    ·obtain⟨a,ha,rfl⟩:=List.mem_map.mp hm;exact cov a ha
    ·exact Or.inr (Or.inl ⟨b,rfl⟩)
    ·obtain⟨a,ha,he⟩:=List.mem_map.mp hm;rw[show v=inv (observe a) by rw[<-inv_inv' v,<-he]];exact avail_inv (cov a ha)⟩
  | succ q ih=>
   intro bk ⟨_,a,b,op,hrp,ha',hb',hbk⟩;subst hbk;obtain⟨next,hn,htr⟩:=ih hrp
   refine⟨combine op (restrictRows (movedRow ms) a) (restrictRows (movedRow ms) b)::next,Reach.two op hn (htr _ ha') (htr _ hb'),λv hv=> ?_⟩
   rcases hv with hm|⟨c,rfl⟩|hm
   ·exact(List.mem_cons.mp hm).elim (λe=>e▸Or.inl (List.mem_cons.mpr (Or.inl (by funext r;cases op<;>rfl)))) λht=>available_cons _ (htr _ (Or.inl ht))
   ·exact Or.inr (Or.inl ⟨c,rfl⟩)
   ·exact(List.mem_cons.mp hm).elim (λhe=>by have hi:=congrArg inv he;rw[inv_inv']at hi;rw[hi];exact avail_inv (Or.inl (List.mem_cons.mpr (Or.inl (by funext r;cases op<;>rfl))))) λht=>available_cons _ (htr _ (Or.inr (Or.inr ht)))
 obtain⟨next,hn,htr⟩:=lift hr;exact prior p next hn (heq▸htr _ ha)
def witnessB(T:Sig)(roots:List Sig)(a:Sig)(rs:Row×Row):Bool:=
 (bit rs.1 T !=bit rs.2 T)&&roots.all (λv=>v==a||bit rs.1 v==bit rs.2 v)
def checkEssential(T:Sig)(raw:List Sig)(xs:List (Sig×Row×Row)):Bool:=
 plainWord T&&raw.all plainWord&&xs.all (λe=>witnessB T raw e.1 e.2)
def checkLift (ms:List Move) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
  (xs:List (Sig×Row×Row)):Bool:=
 checkMap ms raw T base G&&checkEssential T raw xs &&
  xs.all (λe=>movedWord ms e.1==zero||movedWord ms e.1==one)
private lemma essential_ok {T raw xs} (ok:checkEssential T raw xs=true) :
  (plainWord T=true/\raw.all plainWord=true)/\∀a∈(xs.map Prod.fst).toFinset,Essential T raw a:=by
 simp only[checkEssential,Bool.and_eq_true]at ok
 refine⟨ok.1,λa ha=> ?_⟩
 obtain⟨e,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
 have hw:=List.all_eq_true.mp ok.2 e hm
 simp[witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq]at hw
 exact⟨e.2.1,e.2.2,hw.1,λv hv hne=>(hw.2 v hv).resolve_left hne⟩
private lemma lower_count {raw T} (hpT:proper T) (xs:List (Sig×Row×Row))
  (ok:checkEssential T raw xs=true):Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
 obtain⟨⟨hT,hR⟩,hess⟩:=essential_ok ok
 intro p bank hr ha;obtain⟨k,S,hk,hl,sub⟩:=reach_live hpT hT hR hr ha
 have le:(xs.map Prod.fst).toFinset⊆S:=λa ha=>let⟨r,s,hd,iso⟩:=hess a ha;raw_required hl raw a sub r s hd iso
 have:=Finset.card_le_card le;have:=live_size hl;omega
private lemma lift_ok {ms T raw base G xs L} (ok:checkLift ms T raw base G xs=true)
  (hpT:proper T) (hpG:proper G) (prior:Lower base G L) :
  Lower raw T (L+(xs.map Prod.fst).toFinset.card):=by
 simp only[checkLift,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,beq_iff_eq]at ok
 obtain⟨eq,cov⟩:=map_correct ok.1.1;obtain⟨⟨hT,hR⟩,hess⟩:=essential_ok ok.1.2
 apply lower_slice hpT hT hR hpG (movedRow ms) eq cov _ hess _ prior
 intro a ha;obtain⟨e,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
 have h1:restrictRows (movedRow ms) (observe e.1)=observe (movedWord ms e.1):=funext λr=>(bit_moved ms e.1 r).symm
 rw[h1];rcases ok.2 e hm with h|h<;>rw[h]
 ·exact⟨false,funext bit_zero⟩
 ·exact⟨true,funext bit_one⟩
def g16Edges:List (Nat×Nat):=
 [(0,2),(1,3),(0,4),(2,4),(1,5),(3,5),(0,6),(1,6),(2,6),(3,6),(4,6),(0,7),(1,7),(2,7),(3,7),(4,7),(5,7),(6,7)]
def selected(m:Nat):List (Nat×Sig):=
 (List.range 12).filterMap λi=>if m.testBit i then some (i,inputs.getD i zero)else none
def vars(m:Nat):List Sig:=(selected m).map Prod.snd
def vertex(m j:Nat):Sig:=if m.testBit j then inputs.getD j zero else zero
def graphGoal(m:Nat):Sig:=
 let x:=vertex m
 (x 0&&&x 2)|||(x 1&&&x 3)|||(x 0&&&x 4)|||(x 2&&&x 4)|||(x 1&&&x 5)|||(x 3&&&x 5)|||(x 0&&&x 6)|||(x 1&&&x 6)|||(x 2&&&x 6)|||(x 3&&&x 6)|||(x 4&&&x 6)|||(x 0&&&x 7)|||(x 1&&&x 7)|||(x 2&&&x 7)|||(x 3&&&x 7)|||(x 4&&&x 7)|||(x 5&&&x 7)|||(x 6&&&x 7)
def subcube(z o:Nat):Sig:=if z&&&o !=0 then zero else BitVec.ofNat 4096 (subcubeNv 12 z o)
def fixRows(z o:Nat):List Move:=
 (List.range 12).filterMap λj=>
  let x:=inputs.getD j zero;let step:=Fin.ofNat 4096 (1<<<j)
  if z.testBit j then some (zero,x,step)else if o.testBit j then some (~~~x,zero,step)else none
def swapRows(v:Nat):Move:=
 let i:=v&&&15;let j:=v>>>4;let a:=inputs.getD i zero;let b:=inputs.getD j zero
 (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 4096 ((1<<<j)-(1<<<i)))
def supportPairs(mask:Nat):List (Sig×Row×Row):=(selected mask).map λ(i,a)=>(a,0,Fin.ofNat 4096 (1<<<i))
def graphPairs(m hints:Nat):List (Sig×Row×Row):=
 (selected m).map λ(i,a)=>let r:=1<<<((hints>>>(4*i))&&&15);(a,Fin.ofNat 4096 r,Fin.ofNat 4096 (r|||(1<<<i)))
def properB(T:Sig):Bool:=T !=zero&&T !=one
private lemma proper_of (T:Sig) (h:properB T=true):proper T:=by
 simpa only[properB,proper,Bool.and_eq_true,bne_iff_ne]using h
private lemma vars_nodup (m:Nat):(vars m).Nodup:=by
 have hsub:((selected m).map Prod.fst).Sublist (List.range 12):=by
  unfold selected
  have go (l:List Nat):((l.filterMap λi=>if m.testBit i then some (i,inputs.getD i zero)else none).map Prod.fst).Sublist l:=by
   induction l with
   | nil=>exact .slnil
   | cons a l ih=>
    simp[List.filterMap_cons]
    by_cases h:m.testBit a=true
    ·simp only[h,ite_true,List.map_cons];exact .cons_cons a ih
    ·simp[h];exact .cons a ih
  exact go (List.range 12)
 have hsel:∀{j a},(j,a)∈selected m->j<12/\a=inputs.getD j zero:=λh=>by
  obtain⟨v,hv,hh⟩:=List.mem_filterMap.mp h;split at hh<;>[cases hh;contradiction]
  exact⟨List.mem_range.mp hv,rfl⟩
 have heq:vars m=((selected m).map Prod.fst).map (λi=>inputs.getD i zero):=by
  simp only[vars,List.map_map];exact List.map_congr_left λ⟨j,a⟩ hm=>(hsel hm).2
 rw[heq,List.nodup_map_iff_inj_on (List.nodup_range.sublist hsub)]
 intro i hi j hj hij
 exact congrArg Fin.val (inputs_inj (i:=⟨i,List.mem_range.mp (hsub.subset hi)⟩) (j:=⟨j,List.mem_range.mp (hsub.subset hj)⟩) hij)
private lemma supportPairs_card (s:Nat):((supportPairs s).map Prod.fst).toFinset.card=(selected s).length:=by
 rw[show(supportPairs s).map Prod.fst=vars s by simp[supportPairs,vars,List.map_map,Function.comp_def],
  List.toFinset_card_of_nodup (vars_nodup s)];simp[vars]
private lemma graphPairs_card (m hints:Nat):((graphPairs m hints).map Prod.fst).toFinset.card=(selected m).length:=by
 rw[show(graphPairs m hints).map Prod.fst=vars m by simp[graphPairs,vars,List.map_map,Function.comp_def],
  List.toFinset_card_of_nodup (vars_nodup m)];simp[vars]
abbrev Face(m L:Nat):=Lower (vars m) (graphGoal m) L
def Known(entries:List (Nat×Nat)):Prop:=∀e∈entries,Lower (vars e.1) (graphGoal e.1) e.2
theorem baseKnown:Known []:=by simp[Known]
theorem known_cons {entries:List (Nat×Nat)} {m L:Nat}
  (h1:Lower (vars m) (graphGoal m) L) (h2:Known entries):Known ((m,L)::entries):=λe he=>
 (List.mem_cons.mp he).elim (λh=>h▸h1) (h2 e)
def boundsBefore(entries:List (Nat×Nat))(q:Nat):Nat:=
 entries.foldl (λbest e=>if e.1=q then max best e.2 else best) 0
theorem before_sound(entries:List (Nat×Nat))(sound:Known entries)(q:Nat):
  Lower (vars q) (graphGoal q) (boundsBefore entries q):=by
 have go (acc:Nat) (hacc:Lower (vars q) (graphGoal q) acc) (es:List (Nat×Nat)) (hs:Known es) :
   Lower (vars q) (graphGoal q) (es.foldl (λbest e=>if e.1=q then max best e.2 else best) acc):=by
  induction es generalizing acc with
  | nil=>exact hacc
  | cons e es ih=>
   apply ih _ _ λx hx=>hs x (by simp[hx]);dsimp;split
   next eq=>have he:=eq▸hs e (by simp);intro p bank hr ha;exact max_le (hacc p bank hr ha) (he p bank hr ha)
   next=>exact hacc
 exact go 0 (λ_ _ _ _=>Nat.zero_le _) entries sound
def colFree(m z o:Nat):Nat:=m^^^(m&&&(z|||o))
noncomputable def colCheckWith(m:Nat)(T:Sig)(z o q s L:Nat)(prior:Nat->Nat):Bool:=
 let ms:=fixRows z o;let free:=colFree m z o
 forceSig (movedWord ms T) λG=>
 let xs:=supportPairs s;let count:=(selected s).length
 properB G&&(vars m).all (λa=>freeWord (vars free) (movedWord ms a)) &&
  (movedWord ms (subcube z o)==one) &&
  (if q=0 then checkEssential G (vars free) xs&&decide (L<=count-1)
   else forceSig (graphGoal q) λGq=>
    properB Gq&&checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) Gq xs &&
    decide (L<=prior q+count))
private lemma colCheckWith_explicit {m z o q s L:Nat} {prior:Nat->Nat}
  (valid:∀q',Lower (vars q') (graphGoal q') (prior q'))
  (ok:colCheckWith m (graphGoal m) z o q s L prior=true) :
  let ms:=fixRows z o;let free:=colFree m z o
  (∀r:Row,bit (movedRow ms r) (subcube z o)=true) /\
  (∀a∈vars m,Available ((vars free).map observe) (restrictRows (movedRow ms) (observe a))) /\
  ¬Constant (restrictRows (movedRow ms) (observe (graphGoal m))) /\
  (∀p bank,Reach ((vars free).map observe) p bank ->
   Available bank (restrictRows (movedRow ms) (observe (graphGoal m)))->L<=p):=by
 simp[colCheckWith,forceSig_eq,Bool.and_eq_true,List.all_eq_true,beq_iff_eq]at ok
 set ms:=fixRows z o;set G:=movedWord ms (graphGoal m)
 have hobsG:restrictRows (movedRow ms) (observe (graphGoal m))=observe G:=funext λr=>(bit_moved ms _ r).symm
 refine⟨λr=>(bit_moved ms _ r).symm.trans (by rw[ok.1.2];exact bit_one r),λa ha=> ?_,
  hobsG▸observe_proper (proper_of _ ok.1.1.1),λp bank hr ha=> ?_⟩
 ·have hf:=ok.1.1.2 a ha
  simp[freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq]at hf
  rw[show restrictRows (movedRow ms) (observe a)=observe (movedWord ms a) from funext λr=>(bit_moved ms a r).symm]
  rcases hf with (h|h)|hm
  ·exact Or.inr (Or.inl ⟨false,funext λr=>by rw[h];exact bit_zero r⟩)
  ·exact Or.inr (Or.inl ⟨true,funext λr=>by rw[h];exact bit_one r⟩)
  ·exact Or.inl (List.mem_map_of_mem hm)
 ·rw[hobsG]at ha;have hh:=ok.2
  by_cases hq:q=0
  ·simp[hq]at hh
   rw[<-supportPairs_card s]at hh;exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
  ·simp[hq]at hh
   rw[<-supportPairs_card s]at hh
   exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)
noncomputable def carryOK(old rep:Nat)(swaps:List Nat):Bool:=
 forceSig (graphGoal old) λT=>forceSig (graphGoal rep) λG=>checkMap (swaps.map swapRows) (vars old) T (vars rep) G
noncomputable def dropLiftOK(old sub hints:Nat):Bool:=
 forceSig (graphGoal old) λT=>forceSig (graphGoal sub) λG=>
 properB T&&properB G&&checkLift (fixRows (old^^^sub) 0) T (vars old) (vars sub) G (graphPairs (old^^^sub) hints)
noncomputable def baseLowerOK(m hints L:Nat):Bool:=
 forceSig (graphGoal m) λT=>properB T&&checkEssential T (vars m) (graphPairs m hints)&&decide (L<=(selected m).length-1)
inductive StepEntry where
 | base (m hints L:Nat)
 | carry (old rep L:Nat) (swaps:List Nat)
 | drop (old sub hints Lsub L:Nat)
def stepOut:StepEntry->Nat×Nat
 | .base m _ L=>(m,L)
 | .carry old _ L _=>(old,L)
 | .drop old _ _ _ L=>(old,L)
noncomputable def stepCheck(entries:List (Nat×Nat)):StepEntry->Bool
 | .base m hints L=>baseLowerOK m hints L
 | .carry old rep L swaps=>decide (L<=boundsBefore entries rep)&&carryOK old rep swaps
 | .drop old sub hints Lsub L=>
  decide (Lsub<=boundsBefore entries sub)&&dropLiftOK old sub hints&&decide (L<=Lsub+(selected (old^^^sub)).length)
def applyStepsEntries(entries:List (Nat×Nat)):List StepEntry->List (Nat×Nat)
 | []=>entries
 | s::rest=>applyStepsEntries (stepOut s::entries) rest
noncomputable def checkSteps(entries:List (Nat×Nat)):List StepEntry->Bool
 | []=>true
 | s::rest=>stepCheck entries s&&checkSteps (stepOut s::entries) rest
theorem known_of_steps:∀(steps:List StepEntry)(entries:List (Nat×Nat)),
  Known entries->checkSteps entries steps=true->Known (applyStepsEntries entries steps)
 | [],entries,hk,_=>hk
 | s::rest,entries,hk,hchk=>by
  simp[checkSteps,Bool.and_eq_true]at hchk
  apply known_of_steps rest (stepOut s::entries) _ hchk.2
  refine known_cons ?_ hk
  cases s with
  | base m hints L=>
   have h:=hchk.1;simp[stepCheck,baseLowerOK,forceSig_eq,Bool.and_eq_true,decide_eq_true_eq]at h
   rw[<-graphPairs_card m hints]at h
   intro p bank hr ha;exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
  | carry old rep L swaps=>
   have h:=hchk.1;simp[stepCheck,carryOK,forceSig_eq,Bool.and_eq_true,decide_eq_true_eq]at h
   intro p bank hr ha;exact h.1.trans (lower_map h.2 (before_sound entries hk rep) p bank hr ha)
  | drop old sub hints Lsub L=>
   have h:=hchk.1;simp[stepCheck,dropLiftOK,forceSig_eq,Bool.and_eq_true,decide_eq_true_eq]at h
   rw[<-graphPairs_card (old^^^sub) hints]at h
   have hs:Lower (vars sub) (graphGoal sub) Lsub:=λp b hr ha=>h.1.1.trans (before_sound entries hk sub p b hr ha)
   intro p bank hr ha;exact h.2.trans (lift_ok h.1.2.2 (proper_of _ h.1.2.1.1) (proper_of _ h.1.2.1.2) hs p bank hr ha)
def unpackSwaps:Nat->Nat->List Nat->List Nat
 | 0,_,acc=>acc
 | k+1,p,acc=>unpackSwaps k (Nat.shiftRight p 8) (Nat.land p 255::acc)
def unpackStep(w:Nat):StepEntry:=
 let tag:=Nat.land w 3
 let oldM:=Nat.land (Nat.shiftRight w 2) 0xfff
 let refM:=Nat.land (Nat.shiftRight w 14) 0xfff
 let L:=Nat.land (Nat.shiftRight w 26) 31
 let Lsub:=Nat.land (Nat.shiftRight w 31) 31
 let len:=Nat.land (Nat.shiftRight w 36) 15
 let pay:=Nat.shiftRight w 40
 if Nat.beq tag 0 then .base oldM pay L
 else if Nat.beq tag 1 then .carry oldM refM L (unpackSwaps len pay [])
 else .drop oldM refM pay Lsub L
def packedStepsSlice(tab:Array Nat)(lo hi:Nat):List StepEntry:=
 (List.range (hi-lo)).map λi=>unpackStep (tab.getD (lo+i) 0)
def applyPackedSteps(entries:List (Nat×Nat))(tab:Array Nat)(lo hi:Nat):List (Nat×Nat):=
 applyStepsEntries entries (packedStepsSlice tab lo hi)
noncomputable def checkPackedSteps(entries:List (Nat×Nat))(tab:Array Nat)(lo hi:Nat):Bool:=
 checkSteps entries (packedStepsSlice tab lo hi)
theorem known_of_packedSteps (tab:Array Nat) (lo hi:Nat) (entries:List (Nat×Nat))
  (hk:Known entries) (hok:checkPackedSteps entries tab lo hi=true) :
  Known (applyPackedSteps entries tab lo hi):=
 known_of_steps (packedStepsSlice tab lo hi) entries hk hok
noncomputable def faceRootOK(m hints:Nat):Bool:=
 forceSig (graphGoal m) λT=>properB T&&plainWord T&&(vars m).all plainWord&&checkEssential T (vars m) (graphPairs m hints)
theorem lowerOfFaceRoot {m hints cap:Nat} (hroot:faceRootOK m hints=true)
  (himp:Impossible (graphGoal m) cap (vars m).toFinset):Lower (vars m) (graphGoal m) (cap+1):=by
 simp only[faceRootOK,forceSig_eq,Bool.and_eq_true]at hroot
 have hess:=(essential_ok hroot.2).2
 apply lower_impossible (proper_of _ hroot.1.1.1) hroot.1.1.2 hroot.1.2 (λa ha=> ?_) himp
 exact hess a (by rw[show(graphPairs m hints).map Prod.fst=vars m by simp[graphPairs,vars,List.map_map,Function.comp_def]];exact List.mem_toFinset.mpr ha)
def edgeFlat52834:List Nat:=
 [0,2,1,3,0,4,2,4,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7]
def target52834(x:Fin 8->Bool):Bool:=
 decide (∃i < edgeFlat52834.length / 2,
  (List.ofFn x).getD (edgeFlat52834.getD (2*i) 0) false=true /\
  (List.ofFn x).getD (edgeFlat52834.getD (2*i+1) 0) false=true)
def witness52834:List Gate:=
 [⟨.or,[0,4]⟩,⟨.or,[5,6]⟩,⟨.or,[6,7]⟩,⟨.or,[1,3]⟩,⟨.or,[11,7]⟩,⟨.or,[2,11]⟩,⟨.or,[13,8]⟩,⟨.and,[0,4]⟩,⟨.and,[1,3]⟩,⟨.and,[2,8]⟩,⟨.and,[14,10]⟩,⟨.and,[9,12]⟩,⟨.or,[15,16]⟩,⟨.or,[17,18]⟩,⟨.or,[19,20]⟩,⟨.or,[21,22]⟩]
private lemma avail_mono {R:Type} {p1 p2:List (Wire R)} (hsub:∀x∈p1,x∈p2) {v} (h:Available p1 v):Available p2 v:=by
 rcases h with hm|hc|hi
 ·exact Or.inl (hsub _ hm)
 ·exact Or.inr (Or.inl hc)
 ·exact Or.inr (Or.inr (hsub _ hi))
private lemma avail_inv' {R:Type} {p:List (Wire R)} {v} (h:Available p v):Available p (inv v):=by
 rcases h with hm|⟨b,hb⟩|hi
 ·exact Or.inr (Or.inr (by rw[show inv (inv v)=v from funext λr=>by simp[inv]];exact hm))
 ·exact Or.inr (Or.inl ⟨!b,funext λr=>by simp[inv,congrFun hb r]⟩)
 ·exact Or.inl hi
private lemma execute_reach (gs:List Gate) (raw:List Sig)
  (hleg:∀g∈gs,(g.op=GateOp.and\/g.op=GateOp.or\/g.op=GateOp.not)/\g.inputs.length<=2) :
  ∃q bank,q<=gs.countP (λg=> !isNot g)/\Reach (raw.map observe) q bank /\
   ∀a∈execute gs raw,Available bank (observe a):=by
 have go:∀(gs:List Gate)(w:List Sig)(p:Nat)(bank:List (Wire Row)),
   (∀g∈gs,(g.op=GateOp.and\/g.op=GateOp.or\/g.op=GateOp.not)/\g.inputs.length<=2) ->
   Reach (raw.map observe) p bank->(∀a∈w,Available bank (observe a)) ->
   ∃q bank',q<=p+gs.countP (λg=> !isNot g)/\Reach (raw.map observe) q bank' /\
    ∀a∈execute gs w,Available bank' (observe a):=λgs=>by
  induction gs with
  | nil=>exact λw p bank _ hr hw=>⟨p,bank,by simp,hr,hw⟩
  | cons g gs ih=>
   intro w p bank hlg hr hw
   have hgw:=hlg g (by simp)
   have getA:∀idx,Available bank (observe (w.getD idx zero)):=λidx=>by
    simp only[List.getD_eq_getElem?_getD]
    cases hq:w[idx]? with
    | none=>exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
    | some v=>exact hw v (List.mem_of_getElem? hq)
   have hstep:∃d bank1,d<=(if !isNot g then 1 else 0)/\Reach (raw.map observe) (p+d) bank1 /\
     (∀x∈bank,x∈bank1)/\Available bank1 (observe (runGate w g)):=by
    obtain⟨op,l⟩:=g;obtain⟨hop,hlen⟩:=hgw
    rcases hop with rfl|rfl|rfl
    ·match l,hlen with
     | [],_=>exact⟨0,bank,by simp[isNot],hr,λ_ h=>h,Or.inr (Or.inl ⟨true,funext λr=>by simp[observe,runGate,bit_one]⟩)⟩
     | [i],_=>exact⟨0,bank,by simp[isNot],hr,λ_ h=>h,by
       rw[show runGate w ⟨.and,[i]⟩=w.getD i zero from bit_ext λr=>by simp[runGate,bit_and,bit_one]]
       exact getA i⟩
     | [i,j],_=>
      refine⟨1,combine false (observe (w.getD i zero)) (observe (w.getD j zero))::bank,by simp[isNot],
       Reach.two false hr (getA i) (getA j),λ_ h=>List.mem_cons_of_mem _ h,Or.inl ?_⟩
      have he:observe (runGate w ⟨.and,[i,j]⟩)=combine false (observe (w.getD i zero)) (observe (w.getD j zero)):=
       funext λr=>by simp[observe,combine,runGate,bit_and,bit_one]
      rw[he];exact List.mem_cons_self
    ·match l,hlen with
     | [],_=>exact⟨0,bank,by simp[isNot],hr,λ_ h=>h,Or.inr (Or.inl ⟨false,funext λr=>by simp[observe,runGate,bit_zero]⟩)⟩
     | [i],_=>exact⟨0,bank,by simp[isNot],hr,λ_ h=>h,by
       rw[show runGate w ⟨.or,[i]⟩=w.getD i zero from bit_ext λr=>by simp[runGate,bit_or,bit_zero]]
       exact getA i⟩
     | [i,j],_=>
      refine⟨1,combine true (observe (w.getD i zero)) (observe (w.getD j zero))::bank,by simp[isNot],
       Reach.two true hr (getA i) (getA j),λ_ h=>List.mem_cons_of_mem _ h,Or.inl ?_⟩
      have he:observe (runGate w ⟨.or,[i,j]⟩)=combine true (observe (w.getD i zero)) (observe (w.getD j zero)):=
       funext λr=>by simp[observe,combine,runGate,bit_or,bit_zero]
      rw[he];exact List.mem_cons_self
    ·cases l with
     | nil=>exact⟨0,bank,by simp[isNot],hr,λ_ h=>h,Or.inr (Or.inl ⟨true,funext λr=>by simp[observe,runGate,bit_neg,bit_zero]⟩)⟩
     | cons i tail=>
      refine⟨0,bank,by simp[isNot],hr,λ_ h=>h,?_⟩
      have he:observe (runGate w ⟨.not,i::tail⟩)=inv (observe (w.getD i zero)):=
       funext λr=>by simp[observe,inv,runGate,bit_neg]
      rw[he];exact avail_inv' (getA i)
   obtain⟨d,bank1,hd,hr1,hsub,hnew⟩:=hstep
   obtain⟨q,bank',hq,hr',hw'⟩:=ih (w++[runGate w g]) (p+d) bank1
    (λx hx=>hlg x (by simp[hx])) hr1 (λa ha=>by
     simp only[List.mem_append,List.mem_singleton]at ha
     rcases ha with hw1|rfl
     ·exact avail_mono hsub (hw a hw1)
     ·exact hnew)
   refine⟨q,bank',?_,hr',hw'⟩
   simp only[List.countP_cons];split at hd<;>simp_all<;>omega
 obtain⟨q,bank,hq,hr,hw⟩:=go gs raw 0 (raw.map observe) hleg Reach.start (λa ha=>Or.inl (List.mem_map_of_mem ha))
 exact⟨q,bank,by omega,hr,hw⟩
private lemma vars255_eq :
  vars 255=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,
    inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]:=by
 change ((List.range 12).filterMap λi=>if(255:Nat).testBit i then some (i,inputs.getD i zero)else none).map Prod.snd=_
 rw[show List.range 12=[0,1,2,3,4,5,6,7,8,9,10,11] from rfl]
 simp[show(255:Nat).testBit 0=true by decide,show(255:Nat).testBit 1=true by decide,
   show(255:Nat).testBit 2=true by decide,show(255:Nat).testBit 3=true by decide,
   show(255:Nat).testBit 4=true by decide,show(255:Nat).testBit 5=true by decide,
   show(255:Nat).testBit 6=true by decide,show(255:Nat).testBit 7=true by decide,
   show(255:Nat).testBit 8=false by decide,show(255:Nat).testBit 9=false by decide,
   show(255:Nat).testBit 10=false by decide,show(255:Nat).testBit 11=false by decide]
private lemma vars255_map_bit (r:Row) :
  (vars 255).map (bit r)=List.ofFn (λi:Fin 8=>r.1.testBit i.1):=by
 rw[vars255_eq]
 exact List.ext_getElem (by simp) λi h1 h2=>by
  have hi:i<8:=by simp at h2;exact h2
  simp only[List.getElem_ofFn]
  have hk:∀k:Fin 8,([inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,
    inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero].map (bit r))[k.1]'(by simp)=r.1.testBit k.1:=by
   intro k;fin_cases k<;>exact input_coords ⟨_,by omega⟩ r
  exact hk ⟨i,hi⟩
private lemma bit_graphGoal_255_eq (r:Row) :
  bit r (graphGoal 255)=target52834 (λi:Fin 8=>r.1.testBit i.1):=by
 have h1:∀u v,u<8->v<8->bit r (vertex 255 u&&&vertex 255 v)=(r.1.testBit u&&r.1.testBit v):=by
  intro u v hu hv
  have htu:(255:Nat).testBit u=true:=by
   have:∀k:Fin 8,(255:Nat).testBit k.1=true:=by decide
   exact this ⟨u,hu⟩
  have htv:(255:Nat).testBit v=true:=by
   have:∀k:Fin 8,(255:Nat).testBit k.1=true:=by decide
   exact this ⟨v,hv⟩
  rw[bit_and];simp only[vertex,htu,htv,ite_true,input_coords ⟨u,by omega⟩ r,input_coords ⟨v,by omega⟩ r]
 have h_all:∀b0 b1 b2 b3 b4 b5 b6 b7:Bool,
   ((b0&&b2)||(b1&&b3)||(b0&&b4)||(b2&&b4)||(b1&&b5)||(b3&&b5)||(b0&&b6)||(b1&&b6)||(b2&&b6)||(b3&&b6)||(b4&&b6)||(b0&&b7)||(b1&&b7)||(b2&&b7)||(b3&&b7)||(b4&&b7)||(b5&&b7)||(b6&&b7)) =
   target52834 ![b0,b1,b2,b3,b4,b5,b6,b7]:=by decide +kernel
 have hvec:(λi:Fin 8=>r.1.testBit i.1) =
   ![r.1.testBit 0,r.1.testBit 1,r.1.testBit 2,r.1.testBit 3,
    r.1.testBit 4,r.1.testBit 5,r.1.testBit 6,r.1.testBit 7]:=by
  funext i;fin_cases i<;>rfl
 rw[hvec,<-h_all]
 simp[graphGoal,bit_or,h1 0 2 (by omega) (by omega),h1 1 3 (by omega) (by omega),h1 0 4 (by omega) (by omega),h1 2 4 (by omega) (by omega),h1 1 5 (by omega) (by omega),h1 3 5 (by omega) (by omega),h1 0 6 (by omega) (by omega),h1 1 6 (by omega) (by omega),h1 2 6 (by omega) (by omega),h1 3 6 (by omega) (by omega),h1 4 6 (by omega) (by omega),h1 0 7 (by omega) (by omega),h1 1 7 (by omega) (by omega),h1 2 7 (by omega) (by omega),h1 3 7 (by omega) (by omega),h1 4 7 (by omega) (by omega),h1 5 7 (by omega) (by omega),h1 6 7 (by omega) (by omega)]
private lemma witness52834_mono :
  ∀g∈witness52834,(g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length<=2:=by
 intro g hg
 simp only[witness52834,List.mem_cons,List.not_mem_nil,or_false]at hg
 rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>simp
private lemma witness52834_eval (x:Fin 8->Bool) :
  Circuit.eval ⟨witness52834,23⟩ (List.ofFn x)=target52834 x:=by
 have hall:∀b0 b1 b2 b3 b4 b5 b6 b7:Bool,
   Circuit.eval ⟨witness52834,23⟩ (List.ofFn ![b0,b1,b2,b3,b4,b5,b6,b7]) =
   target52834 ![b0,b1,b2,b3,b4,b5,b6,b7]:=by decide +kernel
 have hx:x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7]:=by funext i;fin_cases i<;>rfl
 rw[hx];exact hall (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
theorem oneNot_combine_52834(hlow:Face 255 15):
  ∀(gates:List Gate)(o:ℕ),
   (∀g∈gates,(g.op=GateOp.and\/g.op=GateOp.or\/g.op=GateOp.not)/\g.inputs.length<=2) ->
   (∀i j:Fin gates.length,(gates.get i).op=GateOp.not->(gates.get j).op=GateOp.not->i=j) ->
   (∀x:Fin 8->Bool,Circuit.eval ⟨gates,o⟩ (List.ofFn x)=target52834 x) ->
   ∃(gates':List Gate)(o':ℕ),
    (∀g∈gates',(g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length<=2) /\
    gates'.length<=gates.length /\
    ∀x:Fin 8->Bool,Circuit.eval ⟨gates',o'⟩ (List.ofFn x)=target52834 x:=by
 intro gates o hleg _hone hcomp
 by_cases hnot:∃g∈gates,g.op=GateOp.not
 ·have hfit:∀g∈gates,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp):=
   λg hg=>by rcases(hleg g hg).1 with h|h|h<;>simp[h]
  have hT_eq:(execute gates (vars 255)).getD o zero=graphGoal 255:=bit_ext λr=>by
   have h1:=execute_bits gates r (vars 255) hfit
   have hev:bit r ((execute gates (vars 255)).getD o zero)=Circuit.eval ⟨gates,o⟩ ((vars 255).map (bit r)):=by
    rw[<-b_read r (execute gates (vars 255)) o,h1];rfl
   rw[hev,vars255_map_bit r,hcomp,bit_graphGoal_255_eq r]
  obtain⟨q,bank,hq,hr,hmem⟩:=execute_reach gates (vars 255) hleg
  have hav:Available bank (observe (graphGoal 255)):=by
   rw[<-hT_eq];simp only[List.getD_eq_getElem?_getD]
   cases hm:(execute gates (vars 255))[o]? with
   | none=>exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
   | some v=>exact hmem v (List.mem_of_getElem? hm)
  have h14:15<=q:=hlow q bank hr hav
  have hcnt:gates.countP (λg=> !isNot g)+1<=gates.length:=by
   obtain⟨g,hg,ho⟩:=hnot
   have hpos:0<gates.countP isNot:=List.countP_pos_iff.mpr ⟨g,hg,by simp[isNot,ho]⟩
   have hsum:∀gs:List Gate,gs.countP isNot+gs.countP (λg=> !isNot g)=gs.length:=λgs=>by
    induction gs with| nil=>rfl| cons x _ ih=>simp only[List.countP_cons,List.length_cons];cases isNot x<;>simp<;>omega
   have:=hsum gates;omega
  exact⟨witness52834,23,witness52834_mono,by change 16<=gates.length;omega,witness52834_eval⟩
 ·exact⟨gates,o,λg hg=>⟨(hleg g hg).1.imp_right λh=>h.resolve_right λhn=>hnot ⟨g,hg,hn⟩,(hleg g hg).2⟩,le_rfl,hcomp⟩
def activeVars(mask:Nat):List Nat:=(List.range 12).filter (λi=>mask.testBit i)
private lemma activeVars_sub (mask:Nat):(activeVars mask).Sublist (List.range 12):=List.filter_sublist
private lemma activeVars_nd (mask:Nat):(activeVars mask).Nodup:=List.nodup_range.sublist (activeVars_sub mask)
private lemma activeVars_mem (mask i:Nat):i∈activeVars mask↔i<12/\mask.testBit i=true:=by
 simp[activeVars,List.mem_filter,List.mem_range]
private lemma activeVars_le (mask:Nat):(activeVars mask).length<=12:=by
 simpa using (activeVars_sub mask).length_le
def idxInList:List Nat->Nat->Nat->Option Nat
 | [],_,_=>none
 | a::l,x,idx=>if a==x then some idx else idxInList l x (idx+1)
private lemma idxInList_some {l:List Nat} {x idx k:Nat} (h:idxInList l x idx=some k) :
  ∃h1:idx<=k,∃h2:k < idx+l.length,l[k-idx]'(by omega)=x:=by
 induction l generalizing idx with
 | nil=>simp[idxInList]at h
 | cons a l ih=>
  simp[idxInList,beq_iff_eq]at h;split at h
  next ha=>cases h;exact⟨Nat.le_refl _,by simp,by simpa using ha⟩
  next=>
   obtain⟨h1,h2,h3⟩:=ih h
   refine⟨by omega,by simp;omega,?_⟩
   have hidx:k-idx=(k-(idx+1))+1:=by omega
   simpa[hidx]using h3
private lemma idxInList_get {l:List Nat} (nd:l.Nodup) {i:Nat} (hi:i<l.length) :
  idxInList l l[i] 0=some i:=by
 have go (l:List Nat) (nd:l.Nodup) (base i:Nat) (hi:i<l.length):idxInList l l[i] base=some (base+i):=by
  induction l generalizing base i with
  | nil=>simp at hi
  | cons a l ih=>
   obtain⟨hn,nd'⟩:=List.nodup_cons.mp nd
   cases i with
   | zero=>simp[idxInList]
   | succ i'=>
    have hne:a≠l[i']'(by simp at hi;exact hi):=λe=>hn (e▸List.getElem_mem _)
    simp[List.getElem_cons_succ,idxInList,beq_iff_eq,hne]
    simpa[show base+1+i'=base+(i'+1) by omega]using ih nd' (base+1) i' (by simp at hi;exact hi)
 simpa using go l nd 0 i hi
def faceEdgesNv(mask:Nat):List (Nat×Nat):=
 let av:=activeVars mask
 g16Edges.filterMap λ(u,v)=>
  match idxInList av u 0,idxInList av v 0 with
  | some iu,some iv=>some (iu,iv)
  | _,_=>none
def faceGoalNv(mask:Nat):Nat:=
 let nv:=(activeVars mask).length
 (faceEdgesNv mask).foldl (λacc e=>Nat.lor acc (Nat.land (hiC nv e.1) (hiC nv e.2))) 0
def efCNv(mask u:Nat):Nat:=
 let g:=faceGoalNv mask
 Nat.xor g (flipURaw (activeVars mask).length u g)
def varsNv(nv:Nat):List Nat:=(List.range nv).map (hiC nv)
private lemma faceEdgesNv_lt {mask:Nat} {e:Nat×Nat} (he:e∈faceEdgesNv mask) :
  e.1<(activeVars mask).length/\e.2<(activeVars mask).length:=by
 obtain⟨⟨u,v⟩,_,hf⟩:=List.mem_filterMap.mp he
 cases h1:idxInList (activeVars mask) u 0<;>cases h2:idxInList (activeVars mask) v 0<;>simp[h1,h2]at hf
 rcases hf with rfl;obtain⟨_,ha,_⟩:=idxInList_some h1;obtain⟨_,hb,_⟩:=idxInList_some h2;exact⟨by simpa using ha,by simpa using hb⟩
private lemma faceGoalNv_tb (mask r:Nat) :
  (faceGoalNv mask).testBit r=(faceEdgesNv mask).any (λe=>(hiC (activeVars mask).length e.1).testBit r&&(hiC (activeVars mask).length e.2).testBit r):=by
 unfold faceGoalNv
 have go (es:List (Nat×Nat)) (acc:Nat) :
   (es.foldl (λa e=>Nat.lor a (Nat.land (hiC (activeVars mask).length e.1) (hiC (activeVars mask).length e.2))) acc).testBit r =
   (acc.testBit r||es.any λe=>(hiC (activeVars mask).length e.1).testBit r&&(hiC (activeVars mask).length e.2).testBit r):=by
  induction es generalizing acc with
  | nil=>simp
  | cons e es ih=>rw[List.foldl_cons,ih,Nat.lor_eq,Nat.land_eq,Nat.testBit_or,Nat.testBit_and,List.any_cons,Bool.or_assoc]
 simpa using go (faceEdgesNv mask) 0
theorem faceGoalNv_lt(mask:Nat):ValidWord (activeVars mask).length (faceGoalNv mask):=by
 apply lt_two_pow_of_testBit;intro r hr
 rw[faceGoalNv_tb];apply Bool.eq_false_iff.mpr;intro ha
 obtain⟨e,hm,hb⟩:=List.any_eq_true.mp ha
 have hlt:=faceEdgesNv_lt hm
 rw[hiC_bits (activeVars_le mask) hlt.1]at hb
 simp[Nat.not_lt_of_ge hr]at hb
theorem efCNv_spec(mask:Nat):EfSpec (activeVars mask).length (faceGoalNv mask) (efCNv mask):=
 efSpec_of_eq (activeVars_le mask) (faceGoalNv_lt mask) (λ_ _=>rfl)
private def scatterBits (av:List Nat) (r:Nat):Nat:=
 let rec go:List Nat->Nat->Nat->Nat
  | [],_,acc=>acc
  | j::rest,k,acc=>go rest (k+1) (if r.testBit k then acc|||(1<<<j)else acc)
 go av 0 0
private lemma scatterBits_tb (av:List Nat) (r j:Nat) :
  (scatterBits av r).testBit j=true↔∃k,∃hk:k<av.length,av[k]=j/\r.testBit k=true:=by
 unfold scatterBits
 have go (l:List Nat) (k0 acc:Nat) :
   (scatterBits.go r l k0 acc).testBit j=true ↔
   acc.testBit j=true\/∃i,∃hi:i<l.length,l[i]=j/\r.testBit (k0+i)=true:=by
  induction l generalizing k0 acc with
  | nil=>simp[scatterBits.go]
  | cons a l ih=>
   simp only[scatterBits.go,ih]
   have hite:(if r.testBit k0=true then acc|||1<<<a else acc).testBit j=true ↔
     acc.testBit j=true\/(a=j/\r.testBit k0=true):=by
    cases h:r.testBit k0<;>simp[Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
   rw[hite];constructor
   ·rintro ((ha| ⟨rfl,hr⟩)| ⟨i,hi,he,hr⟩)
    ·exact Or.inl ha
    ·exact Or.inr ⟨0,by simp,rfl,by simpa using hr⟩
    ·exact Or.inr ⟨i+1,by simp[hi],by simpa using he,by simpa[show k0+(i+1)=k0+1+i by omega]using hr⟩
   ·rintro (ha| ⟨i,hi,he,hr⟩)
    ·exact Or.inl (Or.inl ha)
    ·cases i with
     | zero=>exact Or.inl (Or.inr ⟨by simpa using he,by simpa using hr⟩)
     | succ i'=>exact Or.inr ⟨i',by simp at hi;exact hi,by simpa using he,by simpa[show k0+1+i'=k0+(i'+1) by omega]using hr⟩
 simpa using go av 0 0
private lemma scatterBits_lt (mask r:Nat):scatterBits (activeVars mask) r<4096:=
 lt_two_pow_of_testBit (k:=12) λj hj=>Bool.eq_false_iff.mpr λht=>by
  obtain⟨k,hk,rfl,_⟩:=(scatterBits_tb _ r j).mp ht
  have:=((activeVars_mem mask _).mp (List.getElem_mem hk)).1;omega
private def liftRow (mask r:Nat):Row:=⟨scatterBits (activeVars mask) r,scatterBits_lt mask r⟩
private lemma liftRow_tb (mask r k:Nat) (hk:k<(activeVars mask).length) :
  (liftRow mask r).1.testBit (activeVars mask)[k]=r.testBit k:=by
 apply Bool.eq_iff_iff.mpr;rw[show(liftRow mask r).1=scatterBits (activeVars mask) r from rfl,scatterBits_tb]
 exact⟨λ⟨k',hk',he,hr⟩=>((List.Nodup.getElem_inj_iff (activeVars_nd mask)).mp he)▸hr,λhr=>⟨k,hk,rfl,hr⟩⟩
private def packBits (av:List Nat) (r:Nat):Nat:=bitsOf (λk=>r.testBit (av.getD k 0)) av.length
private lemma packBits_tb (av:List Nat) (r k:Nat) :
 (packBits av r).testBit k=(decide (k<av.length)&&r.testBit (av.getD k 0)):=bitsOf_tb _ _ k
private lemma packBits_lt (av:List Nat) (r:Nat):packBits av r<2^av.length:=bitsOf_lt _ _
private def projRow (mask:Nat) (r:Row):RowNv (activeVars mask).length:=
 ⟨packBits (activeVars mask) r.1,packBits_lt _ r.1⟩
private lemma projRow_tb (mask:Nat) (r:Row) {k:Nat} (hk:k<(activeVars mask).length) :
  (projRow mask r).1.testBit k=r.1.testBit (activeVars mask)[k]:=by
 change (packBits (activeVars mask) r.1).testBit k=_
 rw[packBits_tb];simp[hk]
private lemma proj_lift (mask:Nat) (r:RowNv (activeVars mask).length) :
  projRow mask (liftRow mask r.1)=r:=Fin.ext <| Nat.eq_of_testBit_eq λk=>by
 by_cases hk:k<(activeVars mask).length
 ·rw[projRow_tb mask _ hk,liftRow_tb mask r.1 k hk]
 ·change (packBits (activeVars mask) _).testBit k=_
  rw[packBits_tb,decide_eq_false hk,Bool.false_and,testBit_eq_false_of_lt_pow r.2 (Nat.le_of_not_lt hk)]
private lemma active_var_dep (mask:Nat) {i:Nat} (hi:i<12) (hmi:mask.testBit i=true) (r:Row) :
  bit (liftRow mask (projRow mask r).1) (inputs.getD i zero)=bit r (inputs.getD i zero):=by
 obtain⟨k,hk,hgk⟩:=List.getElem_of_mem ((activeVars_mem mask i).mpr ⟨hi,hmi⟩)
 rw[input_coords ⟨i,hi⟩,input_coords ⟨i,hi⟩];dsimp
 rw[<-hgk,liftRow_tb mask _ k hk,projRow_tb mask r hk]
private lemma bit_graphGoal_eq (mask:Nat) (r:Row) :
  bit r (graphGoal mask)=g16Edges.any (λe=>mask.testBit e.1&&mask.testBit e.2&&r.1.testBit e.1&&r.1.testBit e.2):=by
 have hv (j:Nat) (hj:j<12):bit r (vertex mask j)=(mask.testBit j&&r.1.testBit j):=by
  unfold vertex;cases hm:mask.testBit j<;>[simp[bit_zero];simpa using input_coords ⟨j,hj⟩ r]
 have h1:∀a b,a<12->b<12->bit r (vertex mask a&&&vertex mask b)=(mask.testBit a&&mask.testBit b&&r.1.testBit a&&r.1.testBit b):=by
  intro a b ha hb;rw[bit_and,hv a ha,hv b hb]
  cases mask.testBit a<;>cases mask.testBit b<;>cases r.1.testBit a<;>cases r.1.testBit b<;>rfl
 simp[graphGoal,g16Edges,List.any_cons,List.any_nil,Bool.or_false,bit_or,h1 0 2 (by omega) (by omega),h1 1 3 (by omega) (by omega),h1 0 4 (by omega) (by omega),h1 2 4 (by omega) (by omega),h1 1 5 (by omega) (by omega),h1 3 5 (by omega) (by omega),h1 0 6 (by omega) (by omega),h1 1 6 (by omega) (by omega),h1 2 6 (by omega) (by omega),h1 3 6 (by omega) (by omega),h1 4 6 (by omega) (by omega),h1 0 7 (by omega) (by omega),h1 1 7 (by omega) (by omega),h1 2 7 (by omega) (by omega),h1 3 7 (by omega) (by omega),h1 4 7 (by omega) (by omega),h1 5 7 (by omega) (by omega),h1 6 7 (by omega) (by omega),Bool.or_assoc]
private lemma g16Edges_lt {e:Nat×Nat} (he:e∈g16Edges):e.1<12/\e.2<12:=by
 simp[g16Edges,List.mem_cons,List.not_mem_nil,or_false]at he
 rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl<;>decide
private lemma goal_proj_eq (mask:Nat) (r:Row) :
  (faceGoalNv mask).testBit (projRow mask r).1=bit r (graphGoal mask):=by
 rw[faceGoalNv_tb,bit_graphGoal_eq];apply Bool.eq_iff_iff.mpr
 simp only[List.any_eq_true,Bool.and_eq_true]
 constructor
 ·rintro⟨⟨iu,iv⟩,hm,h1,h2⟩
  obtain⟨⟨u,v⟩,hge,hf⟩:=List.mem_filterMap.mp hm
  cases hi1:idxInList (activeVars mask) u 0 with
  | none=>simp[hi1]at hf
  | some iu'=>
   cases hi2:idxInList (activeVars mask) v 0 with
   | none=>simp[hi1,hi2]at hf
   | some iv'=>
    simp only[hi1,hi2,Option.some.injEq,Prod.mk.injEq]at hf;rcases hf with ⟨rfl,rfl⟩
    obtain⟨_,hu0,hgu⟩:=idxInList_some hi1;obtain⟨_,hv0,hgv⟩:=idxInList_some hi2
    have hu:iu'<(activeVars mask).length:=by simpa using hu0
    have hv:iv'<(activeVars mask).length:=by simpa using hv0
    have hgu':(activeVars mask)[iu']=u:=by simpa using hgu
    have hgv':(activeVars mask)[iv']=v:=by simpa using hgv
    rw[hiC_bits_row (activeVars_le mask) hu,projRow_tb mask r hu,hgu']at h1
    rw[hiC_bits_row (activeVars_le mask) hv,projRow_tb mask r hv,hgv']at h2
    exact⟨(u,v),hge,⟨⟨((activeVars_mem mask u).mp (hgu'▸List.getElem_mem hu)).2,
     ((activeVars_mem mask v).mp (hgv'▸List.getElem_mem hv)).2⟩,h1⟩,h2⟩
 ·rintro⟨⟨u,v⟩,hge,⟨⟨hmu,hmv⟩,hru⟩,hrv⟩
  have hlt:=g16Edges_lt hge
  obtain⟨iu,hiu,hgu⟩:=List.getElem_of_mem ((activeVars_mem mask u).mpr ⟨hlt.1,hmu⟩)
  obtain⟨iv,hiv,hgv⟩:=List.getElem_of_mem ((activeVars_mem mask v).mpr ⟨hlt.2,hmv⟩)
  refine⟨(iu,iv),List.mem_filterMap.mpr ⟨(u,v),hge,by dsimp;rw[<-hgu,<-hgv,idxInList_get (activeVars_nd mask) hiu,idxInList_get (activeVars_nd mask) hiv]⟩,?_,?_⟩
  ·rwa[hiC_bits_row (activeVars_le mask) hiu,projRow_tb mask r hiu,hgu]
  ·rwa[hiC_bits_row (activeVars_le mask) hiv,projRow_tb mask r hiv,hgv]
private def compressWord (mask:Nat) (w:Sig):Nat:=bitsOf (λr=>bit (liftRow mask r) w) (2^(activeVars mask).length)
private lemma compressWord_tb (mask:Nat) (w:Sig) (r:Nat) :
 (compressWord mask w).testBit r=(decide (r<2^(activeVars mask).length)&&bit (liftRow mask r) w):=bitsOf_tb _ _ r
private lemma compressWord_lt (mask:Nat) (w:Sig):ValidWord (activeVars mask).length (compressWord mask w):=bitsOf_lt _ _
private lemma compressWord_goal (mask:Nat):compressWord mask (graphGoal mask)=faceGoalNv mask:=
 Nat.eq_of_testBit_eq λr=>by
  rw[compressWord_tb];by_cases hr:r<2^(activeVars mask).length
  ·rw[decide_eq_true hr,Bool.true_and,<-goal_proj_eq,proj_lift mask ⟨r,hr⟩]
  ·rw[decide_eq_false hr,Bool.false_and,testBit_eq_false_of_lt_pow (faceGoalNv_lt mask) (Nat.le_of_not_lt hr)]
private lemma compressWord_var (mask:Nat) {k:Nat} (hk:k<(activeVars mask).length) :
  compressWord mask (inputs.getD (activeVars mask)[k] zero)=hiC (activeVars mask).length k:=
 Nat.eq_of_testBit_eq λr=>by
  rw[compressWord_tb,hiC_bits (activeVars_le mask) hk]
  by_cases hr:r<2^(activeVars mask).length
  ·simp only[hr,decide_true,Bool.true_and,input_coords ⟨_,((activeVars_mem mask _).mp (List.getElem_mem hk)).1⟩,liftRow_tb mask r k hk]
  ·simp[hr]
theorem embed_nv_impossible12 {mask cap:Nat}
  (himp:ImpossibleNv (activeVars mask).length (faceGoalNv mask) cap (varsNv (activeVars mask).length).toFinset) :
  Impossible (graphGoal mask) cap (vars mask).toFinset:=by
 let nv:=(activeVars mask).length;let cw:=compressWord mask
 let dep (x:Sig):=∀r:Row,bit r x=bit (liftRow mask (projRow mask r).1) x
 have hc {x} (hx:dep x) (r:Row):(cw x).testBit (projRow mask r).1=bit r x:=by
  rw[hx r];simp[cw,compressWord_tb,(projRow mask r).2]
 have hcw_eq {x y} (hx:dep x) (hy:dep y) (hxy:cw x=cw y):x=y:=bit_ext λr=>by rw[<-hc hx r,<-hc hy r,hxy]
 have hcw_prop {x} (hx:dep x) (hpx:proper x):properNv nv (cw x):=
  ⟨compressWord_lt mask x,
   λh0=>hpx.1 (bit_ext λr=>by rw[<-hc hx r,h0,bit_zero,Nat.zero_testBit]),
   λh1=>hpx.2 (bit_ext λr=>by rw[<-hc hx r,h1,bit_one,testBit_maskC,decide_eq_true (projRow mask r).2])⟩
 have hdep:∀{k S},(∀a∈S,dep a)->Live (graphGoal mask) k S->LiveNv nv (faceGoalNv mask) k (S.image cw):=by
  intro k S hS hl;induction hl using live_ind with
  | stop hp=>
    rw[Finset.image_singleton,show cw (graphGoal mask)=faceGoalNv mask from compressWord_goal mask]
    exact LiveNv.stop (compressWord_goal mask▸hcw_prop (λr=>by rw[<-goal_proj_eq,<-goal_proj_eq,proj_lift]) hp)
  | @step k U a b d hd ha hb hab hf tl ih=>
    have hcw_z:cw (applyOp d a b)=zN d (cw a) (cw b):=Nat.eq_of_testBit_eq λr=>by
     rw[zN_spec,compressWord_tb,compressWord_tb,compressWord_tb]
     by_cases hr:r<2^nv<;>simp[hr,nv,bit_applyOp]<;>rcases lt4_cases hd with rfl|rfl|rfl|rfl<;>rfl
    have hdep_z:dep (applyOp d a b):=λr=>by rw[bit_applyOp,bit_applyOp];simp[comb,observe,hS a (by simp) r,hS b (by simp) r]
    have htail:=ih λx hx=>(Finset.mem_insert.mp hx).elim (·▸hdep_z) λhu=>hS x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    rw[Finset.image_insert,Finset.image_insert];rw[Finset.image_insert,hcw_z]at htail
    refine LiveNv.binary hd (hcw_prop (hS a (by simp)) ha) (hcw_prop (hS b (by simp)) hb) (λe=>hab (hcw_eq (hS a (by simp)) (hS b (by simp)) e)) (λhm=> ?_) htail
    rw[<-hcw_z,<-Finset.image_insert,<-Finset.image_insert,Finset.mem_image]at hm
    obtain⟨y,hy,hye⟩:=hm;exact hf (hcw_eq hdep_z (hS y hy) hye.symm▸hy)
 have hmemV {a} (ha:a∈vars mask):∃i < 12,mask.testBit i=true/\a=inputs.getD i zero:=by
  obtain⟨⟨_,_⟩,hs,rfl⟩:=List.mem_map.mp ha;obtain⟨i,hi12,hfi⟩:=List.mem_filterMap.mp hs
  by_cases hmi:mask.testBit i=true;· simp[hmi]at hfi;exact⟨i,List.mem_range.mp hi12,hmi,hfi.2.symm⟩
  . simp[hmi]at hfi
 have himg:(vars mask).toFinset.image cw=(varsNv nv).toFinset:=by
  ext w;simp only[Finset.mem_image,List.mem_toFinset,varsNv,List.mem_map,List.mem_range]
  refine⟨λ⟨a,ha,e⟩=>let⟨i,hi12,hmi,ea⟩:=hmemV ha;let⟨k,hk,hgk⟩:=List.getElem_of_mem ((activeVars_mem mask i).mpr ⟨hi12,hmi⟩);⟨k,hk,by rw[<-e,ea,<-hgk];exact(compressWord_var mask hk).symm⟩,
    λ⟨k,hk,e⟩=>let hm:=(activeVars_mem mask _).mp (List.getElem_mem hk);⟨inputs.getD (activeVars mask)[k] zero,List.mem_map.mpr ⟨((activeVars mask)[k],inputs.getD (activeVars mask)[k] zero),List.mem_filterMap.mpr ⟨_,List.mem_range.mpr hm.1,by simp[hm.2]⟩,rfl⟩,e▸compressWord_var mask hk⟩⟩
 exact λk hk hl=>himp k hk (himg▸hdep (λa ha r=>let⟨i,hi,hm,e⟩:=hmemV (List.mem_toFinset.mp ha);e▸(active_var_dep mask hi hm r).symm) hl)
theorem embed_nv_to_12 {mask hints cap:Nat} (hroot:faceRootOK mask hints=true)
  (himp:ImpossibleNv (activeVars mask).length (faceGoalNv mask) cap (varsNv (activeVars mask).length).toFinset) :
  Face mask (cap+1):=
 lowerOfFaceRoot hroot (embed_nv_impossible12 himp)
def expandMask(mask m:Nat):Nat:=scatterBits (activeVars mask) m
private lemma expandMask_tb (mask m j:Nat) :
  (expandMask mask m).testBit j=true↔∃u,∃hu:u<(activeVars mask).length,(activeVars mask)[u]=j/\m.testBit u=true:=
 scatterBits_tb (activeVars mask) m j
def unpackColNv(w:Nat):Nat×Nat×Nat:=
 (Nat.land w 0xfff,Nat.land (Nat.shiftRight w 12) 0xfff,Nat.shiftRight w 48)
def unpackColsNv(ws:Array Nat):Array (Nat×Nat×Nat):=⟨ws.toList.map unpackColNv⟩
def mkLoArr(nv:Nat):Array Nat:=⟨(List.range nv).map (loC nv)⟩
def mkHiArr(nv:Nat):Array Nat:=⟨(List.range nv).map (hiC nv)⟩
def mkEfArr(mask:Nat):Array Nat:=
 let nv:=(activeVars mask).length
 match faceGoalNv mask with
 | 0=>⟨(List.range nv).map λ_=>0⟩
 | g'+1=>let g:=g'+1;⟨(List.range nv).map λu=>Nat.xor g (flipURaw nv u g)⟩
noncomputable def colCheckNvWith(mask:Nat)(T:Sig)(w:Nat)(prior:Nat->Nat):Bool:=
 let nv:=(activeVars mask).length
 let zM:=Nat.land w 0xfff;let oM:=Nat.land (Nat.shiftRight w 12) 0xfff
 let q:=Nat.land (Nat.shiftRight w 24) 0xfff;let s:=Nat.land (Nat.shiftRight w 36) 0xfff
 let lb:=Nat.shiftRight w 48
 and (Nat.beq (Nat.shiftRight zM nv) 0)
  (and (Nat.beq (Nat.shiftRight oM nv) 0)
   (colCheckWith mask T (expandMask mask zM) (expandMask mask oM) q s lb prior))
private lemma movedRow_fixRows_tb (z o:Nat) (r:Row) (i:Fin 12) :
  (movedRow (fixRows z o) r).1.testBit i.1 =
   if z.testBit i.1 then false else if o.testBit i.1 then true else r.1.testBit i.1:=by
 have hsh (j:Fin 12):(Fin.ofNat 4096 (1<<<j.1)).1=2^j.1:=by
  have:2^j.1<4096:=lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) j.2) (by decide)
  simp[Fin.ofNat,Nat.shiftLeft_eq,Nat.mod_eq_of_lt this]
 have hfix (b:Bool) (j:Fin 12) (x:Row) :
   (rowMove (if b then ~~~inputs.getD j.1 zero else zero,if b then zero else inputs.getD j.1 zero,Fin.ofNat 4096 (1<<<j.1)) x).1.testBit i.1 =
   if i=j then b else x.1.testBit i.1:=by
  have hflip {v} (e:v=x.1^^^2^j.1):v.testBit i.1=if i=j then !x.1.testBit j.1 else x.1.testBit i.1:=by
   rw[e,Nat.testBit_xor,Nat.testBit_two_pow];by_cases h:i=j;subst h;simp;simp[h,show j.1≠i.1 from λh'=>h (Fin.ext h'.symm)]
  have hneg:bit x (~~~inputs.getD j.1 zero) = !(x.1.testBit j.1):=(bit_neg x _).trans (congrArg (!·) (input_coords j x))
  cases b<;>cases hbj:x.1.testBit j.1<;>simp only[ite_false,ite_true,rowMove,bit_zero,input_coords j x,hneg,hbj,Bool.not_true,Bool.not_false,Bool.false_eq_true]
  ·split_ifs with e;subst e;exact hbj;rfl
  ·have hge:=Nat.ge_two_pow_of_testBit hbj;have hp:=Nat.two_pow_pos j.1
   have hbw:(backwards (Fin.ofNat 4096 (1<<<j.1))).1=4096-2^j.1:=by unfold backwards;rw[hsh j];simp[Fin.ofNat,Nat.mod_eq_of_lt (show 4096-2^j.1<4096 by omega)]
   have hval:(shifted (backwards (Fin.ofNat 4096 (1<<<j.1))) x).1=x.1-2^j.1:=by unfold shifted;split_ifs<;>dsimp only<;>omega
   have hsub_j:(x.1-2^j.1).testBit j.1=false:=by
    have:x.1 / 2^j.1=(x.1-2^j.1) / 2^j.1+1:=by conv_lhs=>rw[<-Nat.sub_add_cancel hge];exact Nat.add_div_right _ hp
    have:x.1 / 2^j.1 % 2=1:=by simpa[Nat.testBit_eq_decide_div_mod_eq]using hbj
    simpa[Nat.testBit_eq_decide_div_mod_eq]using (show(x.1-2^j.1) / 2^j.1 % 2=0 by omega)
   have hxr:x.1-2^j.1=x.1^^^2^j.1:=by
    have h1:(x.1-2^j.1)^^^2^j.1=x.1:=by rw[<-add_pow2_xor hsub_j,Nat.sub_add_cancel hge]
    conv_rhs=>rw[<-h1];rw[Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
   simpa[hbj]using hflip (hval.trans hxr)
  ·have hxr:=add_pow2_xor hbj;have:=hsh j
   have:x.1+2^j.1<4096:=by rw[hxr];exact Nat.xor_lt_two_pow x.2 (Nat.pow_lt_pow_right (by decide) j.2)
   simpa[hbj]using hflip ((show(shifted (Fin.ofNat 4096 (1<<<j.1)) x).1=x.1+2^j.1 by unfold shifted;split_ifs<;>dsimp<;>omega).trans hxr)
  ·split_ifs with e;subst e;exact hbj;rfl
 unfold movedRow fixRows
 have go:∀l:List Nat,(∀j∈l,j<12)->l.Nodup->∀x:Row,
   ((l.filterMap λj=>let y:=inputs.getD j zero;let st:=Fin.ofNat 4096 (1<<<j)
    if z.testBit j then some (zero,y,st)else if o.testBit j then some (~~~y,zero,st)else none).foldl (λj m=>rowMove m j) x).1.testBit i.1 =
   if i.1∈l then(if z.testBit i.1 then false else if o.testBit i.1 then true else x.1.testBit i.1)else x.1.testBit i.1:=λl=>by
  induction l with| nil=>intros;simp| cons a l ih=>
   intro hl hnd x;obtain⟨hn,hnd'⟩:=List.nodup_cons.mp hnd;have ha12:=hl a (by simp);have hl' j (hj:j∈l):=hl j (by simp[hj])
   simp only[List.filterMap_cons]
   have hst (b:Bool) (hb:b=if z.testBit a then false else if o.testBit a then true else x.1.testBit a) :
     (if i.1∈l then if z.testBit i.1 then false else if o.testBit i.1 then true else if i=⟨a,ha12⟩ then b else x.1.testBit i.1
      else if i=⟨a,ha12⟩ then b else x.1.testBit i.1) =
     if i.1∈a::l then if z.testBit i.1 then false else if o.testBit i.1 then true else x.1.testBit i.1 else x.1.testBit i.1:=by
    by_cases e:i.1=a;· have hf:i=⟨a,ha12⟩:=Fin.ext e;simp[hf,hn,hb]
    ·simp[e,show i≠⟨a,ha12⟩ from λh=>e (congrArg Fin.val h)]
   cases hz:z.testBit a
   ·cases ho:o.testBit a
    ·simp only[Bool.false_eq_true,ite_false,ih hl' hnd'];by_cases e:i.1=a<;>simp[e,hn,hz,ho]
    ·simp only[Bool.false_eq_true,ite_false,ite_true,List.foldl_cons,ih hl' hnd',show(rowMove (~~~inputs.getD a zero,zero,Fin.ofNat 4096 (1<<<a)) x).1.testBit i.1=_ from hfix true ⟨a,ha12⟩ x]
     exact hst true (by simp[hz,ho])
   ·simp only[ite_true,List.foldl_cons,ih hl' hnd',show(rowMove (zero,inputs.getD a zero,Fin.ofNat 4096 (1<<<a)) x).1.testBit i.1=_ from hfix false ⟨a,ha12⟩ x]
    exact hst false (by simp[hz])
 simpa[List.mem_range,i.2]using go (List.range 12) (λ_=>List.mem_range.mp) List.nodup_range r
theorem colValidNv_of_colCheckWith {mask w:Nat} {prior:Nat->Nat}
  (valid:∀q',Lower (vars q') (graphGoal q') (prior q')) (ok:colCheckNvWith mask (graphGoal mask) w prior=true) :
  ColLowerBound (activeVars mask).length (faceGoalNv mask) (Nat.land w 0xfff) (Nat.land (Nat.shiftRight w 12) 0xfff) (Nat.shiftRight w 48):=by
 let nv:=(activeVars mask).length;let zM:=Nat.land w 0xfff;let oM:=Nat.land (Nat.shiftRight w 12) 0xfff
 simp[colCheckNvWith,Bool.and_eq_true,Nat.beq_eq]at ok
 let z12:=expandMask mask zM;let o12:=expandMask mask oM;let f12:=movedRow (fixRows z12 o12);let free:=colFree mask z12 o12
 obtain⟨_,hcov12,hnc12,hlb12⟩:=colCheckWith_explicit valid ok.2.2
 let f:RowNv nv->RowNv nv:=λr=>projRow mask (f12 (liftRow mask r.1))
 let roots:List (Wire (RowNv nv)):=(vars free).map (λa r=>bit (liftRow mask r.1) a)
 have hgoal_eq (r:Row):(faceGoalNv mask).testBit (f (projRow mask r)).1=bit (f12 r) (graphGoal mask):=by
  rw[show f (projRow mask r)=projRow mask (f12 r) from Fin.ext <| Nat.eq_of_testBit_eq λk=>by
    by_cases hk:k<nv
    ·have h12:=((activeVars_mem mask _).mp (List.getElem_mem hk)).1
     rw[projRow_tb mask _ hk,projRow_tb mask _ hk,movedRow_fixRows_tb z12 o12 _ ⟨_,h12⟩,movedRow_fixRows_tb z12 o12 _ ⟨_,h12⟩,liftRow_tb mask _ k hk,projRow_tb mask r hk]
    ·change (packBits (activeVars mask) _).testBit k=(packBits (activeVars mask) _).testBit k;simp[packBits_tb,hk,nv]]
  exact goal_proj_eq mask (f12 r)
 have hlift_avail {R S:Type} (g:S->R) {pool:List (Wire R)} {v:Wire R} (hu:Available pool v):Available (pool.map (restrictRows g)) (restrictRows g v):=
  hu.elim (Or.inl ∘ List.mem_map_of_mem) λh=>h.elim (λ⟨c,e⟩=>Or.inr (Or.inl ⟨c,e▸rfl⟩)) (Or.inr ∘ Or.inr ∘ List.mem_map_of_mem)
 have hlift_reach {R S:Type} (g:S->R) {rts:List (Wire R)}:∀{q bk},Reach rts q bk->Reach (rts.map (restrictRows g)) q (bk.map (restrictRows g)):=λ{q}=>by
  induction q with| zero=>exact λh=>h▸rfl| succ q ih=>rintro bk ⟨_,_,_,op,hrp,ha,hb,rfl⟩;exact⟨_,_,_,op,ih hrp,hlift_avail g ha,hlift_avail g hb,rfl⟩
 have hfree_mem:∀{a},a∈freeVarsNv nv (Nat.lor zM oM)->∃u < nv,a=hiC nv u:=by
  have go:∀n acc,n<=nv->(∀x∈acc,∃u < nv,x=hiC nv u)->∀x∈freeVarsNv.go nv (Nat.lor zM oM) n acc,∃u < nv,x=hiC nv u:=λn=>by
    induction n with| zero=>exact λ_ _ h=>h| succ u ih=>
     intro acc hu h;simp[freeVarsNv.go];split_ifs<;>[exact ih acc (by omega) h;exact ih _ (by omega) λx hx=>(List.mem_cons.mp hx).elim (λe=>⟨u,by omega,e⟩) (h x)]
  exact go nv [] (Nat.le_refl _) (λ_ h=>by simp at h)
 have hex m u (hu:u<nv):(expandMask mask m).testBit (activeVars mask)[u]=m.testBit u:=Bool.eq_iff_iff.mpr
  ⟨λht=>let⟨u',_,he,hmu⟩:=(expandMask_tb mask m _).mp ht;(List.Nodup.getElem_inj_iff (activeVars_nd mask)).mp he▸hmu,
   λhm=>(expandMask_tb mask m _).mpr ⟨u,hu,rfl,hm⟩⟩
 refine⟨f,roots,λr=> ?_,λa ha=> ?_,λ⟨b,hb⟩=>hnc12 ⟨b,funext λr=>(hgoal_eq r).symm.trans (congrFun hb (projRow mask r))⟩,λq bank hr ha=> ?_⟩
 ·rw[testBit_subcubeNv (activeVars_le mask)];intro u hu
  rw[projRow_tb mask _ hu,movedRow_fixRows_tb z12 o12 _ ⟨_,((activeVars_mem mask _).mp (List.getElem_mem hu)).1⟩];dsimp[z12,o12];rw[hex zM u hu,hex oM u hu]
  exact⟨λhz=>by rw[show zM.testBit u=true from hz];rfl,λhzf ho=>by rw[show zM.testBit u=false from hzf,show oM.testBit u=true from ho];rfl⟩
 ·obtain⟨u,hu,rfl⟩:=hfree_mem ha;have hm:=(activeVars_mem mask _).mp (List.getElem_mem hu)
  have hav:=hlift_avail (λq:RowNv nv=>liftRow mask q.1) (hcov12 _ (List.mem_map.mpr ⟨((activeVars mask)[u],inputs.getD (activeVars mask)[u] zero),List.mem_filterMap.mpr ⟨_,List.mem_range.mpr hm.1,by simp[hm.2]⟩,rfl⟩))
  rw[List.map_map]at hav
  exact(funext λq=>by change bit (f12 (liftRow mask q.1)) (inputs.getD (activeVars mask)[u] zero)=(hiC nv u).testBit (f q).1;rw[input_coords ⟨_,hm.1⟩,hiC_bits_row (activeVars_le mask) hu,projRow_tb mask _ hu]:_=restrictRows f (observeNv nv (hiC nv u)))▸hav
 ·have hroots_eq:roots.map (restrictRows (projRow mask))=(vars free).map observe:=by
    rw[List.map_map];exact List.map_congr_left λa ha=>funext λr=>by
     obtain⟨⟨_,_⟩,hs,rfl⟩:=List.mem_map.mp ha;obtain⟨i,hi12,hfi⟩:=List.mem_filterMap.mp hs
     by_cases hfi':free.testBit i=true;swap;simp[hfi']at hfi
     simp[hfi']at hfi;rcases hfi with ⟨rfl,rfl⟩
     exact active_var_dep mask (List.mem_range.mp hi12) (by simp[free,colFree,Nat.testBit_xor,Nat.testBit_and]at hfi';cases hm:mask.testBit i<;>simp_all) r
  exact hlb12 q _ (hroots_eq▸hlift_reach (projRow mask) hr) ((show restrictRows (projRow mask) (restrictRows f (observeNv nv (faceGoalNv mask)))=restrictRows f12 (observe (graphGoal mask)) from funext hgoal_eq)▸hlift_avail (projRow mask) ha)
def mkSamplesX(ham1W:Nat)(xs:List (Nat×Nat×Nat×Nat)):Array (Nat×Nat):=
 (xs.map λ(pos,off,cnt,extraDiff)=>
  let m1:=Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 cnt) 1) off
  let m2:=Nat.shiftLeft extraDiff ham1W
  (pos,Nat.xor pos (Nat.xor m1 m2))).toArray
def evalEdgesMask(edges:List (Nat×Nat))(f:Nat->Nat):Nat:=
 edges.foldl (λacc e=>Nat.lor acc (Nat.land (f e.1) (f e.2))) 0
def samplesOK(mask W:Nat)(samps:Array (Nat×Nat)):Bool:=
 let nv:=(activeVars mask).length;let edges:=faceEdgesNv mask
 let allW:=Nat.sub (Nat.shiftLeft 1 W) 1
 and (Nat.beq samps.size nv)
  (and (allRange nv λi=>
     let p:=samps.getD i (0,0)
     and (Nat.beq (Nat.shiftRight p.1 W) 0) (Nat.beq (Nat.shiftRight p.2 W) 0))
   (and (Nat.beq (evalEdgesMask edges λi=>(samps.getD i (0,0)).1) allW)
    (Nat.beq (evalEdgesMask edges λi=>(samps.getD i (0,0)).2) 0)))
def sampleRowFrom(nv:Nat)(f:Nat->Nat)(t:Nat):Nat:=bitsOf (λi=>(f i).testBit t) nv
def sampleRowP(nv:Nat)(samps:Array (Nat×Nat))(t:Nat):Nat:=sampleRowFrom nv (λi=>(samps.getD i (0,0)).1) t
def sampleRowN(nv:Nat)(samps:Array (Nat×Nat))(t:Nat):Nat:=sampleRowFrom nv (λi=>(samps.getD i (0,0)).2) t
private lemma sampleRowFrom_tb (nv:Nat) (f:Nat->Nat) (t i:Nat) :
 (sampleRowFrom nv f t).testBit i=(decide (i<nv)&&(f i).testBit t):=bitsOf_tb _ _ i
private lemma sampleRowFrom_lt (nv:Nat) (f:Nat->Nat) (t:Nat):sampleRowFrom nv f t<2^nv:=bitsOf_lt _ _
private lemma evalEdgesMask_tb (es:List (Nat×Nat)) (f:Nat->Nat) (t:Nat) :
  (evalEdgesMask es f).testBit t=es.any (λe=>(f e.1).testBit t&&(f e.2).testBit t):=by
 unfold evalEdgesMask
 have go (l:List (Nat×Nat)) (acc:Nat) :
   (l.foldl (λa e=>Nat.lor a (Nat.land (f e.1) (f e.2))) acc).testBit t =
   (acc.testBit t||l.any λe=>(f e.1).testBit t&&(f e.2).testBit t):=by
  induction l generalizing acc with
  | nil=>simp
  | cons e l ih=>rw[List.foldl_cons,ih,Nat.lor_eq,Nat.land_eq,Nat.testBit_or,Nat.testBit_and,List.any_cons,Bool.or_assoc]
 simpa using go es 0
theorem samplesOK_sound{mask W:Nat}{samps:Array (Nat×Nat)}(hok:samplesOK mask W samps=true):
  samps.size=(activeVars mask).length /\
  (∀i < (activeVars mask).length,(samps.getD i (0,0)).1<2^W/\(samps.getD i (0,0)).2<2^W) /\
  ∀t < W,(faceGoalNv mask).testBit (sampleRowP (activeVars mask).length samps t)=true /\
      (faceGoalNv mask).testBit (sampleRowN (activeVars mask).length samps t)=false:=by
 simp only[samplesOK,Bool.and_eq_true,Nat.beq_eq]at hok
 obtain⟨hsz,hbnd,hp,hn⟩:=hok
 have hlt_shr:∀x,Nat.shiftRight x W=0->x<2^W:=λx h=>by
  rw[shr_eq]at h;by_contra hge;have:=Nat.div_pos (Nat.le_of_not_lt hge) (Nat.two_pow_pos W);omega
 refine⟨hsz,λi hi=> ?_,λt ht=> ?_⟩
 ·have hbi:=allRange_sound hbnd i hi;simp only[Bool.and_eq_true,Nat.beq_eq]at hbi
  exact⟨hlt_shr _ hbi.1,hlt_shr _ hbi.2⟩
 ·have hrow:∀f:Nat->Nat,(faceGoalNv mask).testBit (sampleRowFrom (activeVars mask).length f t)=(evalEdgesMask (faceEdgesNv mask) f).testBit t:=λf=>by
   rw[faceGoalNv_tb,evalEdgesMask_tb];apply Bool.eq_iff_iff.mpr;simp only[List.any_eq_true,Bool.and_eq_true]
   exact⟨λ⟨e,hm,h1,h2⟩=>⟨e,hm,by
     have hlt:=faceEdgesNv_lt hm
     rw[hiC_bits (activeVars_le mask) hlt.1,sampleRowFrom_tb]at h1
     rw[hiC_bits (activeVars_le mask) hlt.2,sampleRowFrom_tb]at h2
     simpa[hlt.1,hlt.2,sampleRowFrom_lt]using And.intro h1 h2⟩,
    λ⟨e,hm,h1,h2⟩=>⟨e,hm,by
     have hlt:=faceEdgesNv_lt hm
     rw[hiC_bits (activeVars_le mask) hlt.1,sampleRowFrom_tb,hiC_bits (activeVars_le mask) hlt.2,sampleRowFrom_tb]
     simp[hlt.1,hlt.2,sampleRowFrom_lt,h1,h2]⟩⟩
  unfold sampleRowP sampleRowN
  rw[hrow,hrow,hp,hn,Nat.sub_eq,shl_one,Nat.testBit_two_pow_sub_one,decide_eq_true ht,Nat.zero_testBit];exact⟨rfl,rfl⟩
def faithfulSamp(nv W:Nat)(samps:Array (Nat×Nat))(w:Nat)(p:Nat×Nat):Prop:=
 p.1<2^W/\p.2<2^W /\
 ∀t < W,p.1.testBit t=w.testBit (sampleRowP nv samps t)/\p.2.testBit t=w.testBit (sampleRowN nv samps t)
def colsOr:List (Nat×Nat)->Nat
 | []=>0
 | p::ps=>Nat.lor (Nat.xor p.1 p.2) (colsOr ps)
private lemma colsOr_tb (ps:List (Nat×Nat)) (t:Nat) :
  (colsOr ps).testBit t=true↔∃p∈ps,p.1.testBit t≠p.2.testBit t:=by
 induction ps with
 | nil=>simp[colsOr]
 | cons p ps ih=>simp[colsOr,Nat.lor_eq,Nat.xor_eq,Nat.testBit_or,Nat.testBit_xor,ih]
theorem sample_cover_required {mask W k:Nat} {samps:Array (Nat×Nat)} {ws:List Nat} {sws:List (Nat×Nat)}
  (hok:samplesOK mask W samps=true) (hlen:ws.length=sws.length)
  (hf:∀i < ws.length,faithfulSamp (activeVars mask).length W samps (listGetN ws i) (sws.getD i (0,0)))
  (hlive:LiveNv (activeVars mask).length (faceGoalNv mask) k ws.toFinset) :
  colsOr sws=Nat.sub (Nat.shiftLeft 1 W) 1:=by
 obtain⟨_,_,hrows⟩:=samplesOK_sound hok
 apply Nat.eq_of_testBit_eq;intro t;rw[Nat.sub_eq,shl_one,Nat.testBit_two_pow_sub_one]
 by_cases ht:t<W
 ·simp[ht,decide_true];apply(colsOr_tb sws t).mpr
  obtain⟨hp,hn⟩:=hrows t ht
  obtain⟨w,hw,hdiff⟩:=liveNv_row_difference hlive (r:=⟨sampleRowP _ samps t,sampleRowFrom_lt ..⟩)
   (s:=⟨sampleRowN _ samps t,sampleRowFrom_lt ..⟩) (by simp[hp,hn])
  obtain⟨i,hi,rfl⟩:=List.getElem_of_mem (List.mem_toFinset.mp hw)
  have hfi:=hf i hi;rw[listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
   List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (hlen▸hi),Option.getD_some,Option.getD_some]at hfi
  exact⟨sws[i]'(hlen▸hi),List.getElem_mem _,by rw[(hfi.2.2 t ht).1,(hfi.2.2 t ht).2];exact hdiff⟩
 ·simp[ht,decide_false];apply Bool.eq_false_iff.mpr;intro hc
  obtain⟨p,hp,hne⟩:=(colsOr_tb sws t).mp hc;obtain⟨i,hi,rfl⟩:=List.getElem_of_mem hp
  have hfi:=hf i (hlen.symm▸hi);rw[List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]at hfi
  exact hne ((testBit_eq_false_of_lt_pow hfi.1 (Nat.le_of_not_lt ht)).trans (testBit_eq_false_of_lt_pow hfi.2.1 (Nat.le_of_not_lt ht)).symm)
def swapIdx(v t:Nat):Nat:=
 cond (Nat.beq t (Nat.land v 15)) (Nat.shiftRight v 4)
  (cond (Nat.beq t (Nat.shiftRight v 4)) (Nat.land v 15) t)
def validSwapNv(nv v:Nat):Bool:=
 and (Nat.ble (Nat.add (Nat.land v 15) 1) (Nat.shiftRight v 4)) (Nat.ble (Nat.add (Nat.shiftRight v 4) 1) nv)
def idxOf(perm:List Nat)(t:Nat):Nat:=perm.foldl (λt v=>swapIdx v t) t
private lemma swapIdx_lt {nv v t:Nat} (hv:validSwapNv nv v=true) (ht:t<nv):swapIdx v t<nv:=by
 simp only[validSwapNv,Bool.and_eq_true,Nat.ble_eq,Nat.add_eq]at hv;unfold swapIdx
 cases Nat.beq t (Nat.land v 15)
 ·simp only[Bool.cond_false]
  cases Nat.beq t (Nat.shiftRight v 4)<;>simp only[Bool.cond_false,Bool.cond_true]<;>omega
 ·simp only[Bool.cond_true];omega
private lemma swapIdx_invol {nv v t:Nat} (hv:validSwapNv nv v=true):swapIdx v (swapIdx v t)=t:=by
 simp only[validSwapNv,Bool.and_eq_true,Nat.ble_eq,Nat.add_eq]at hv;unfold swapIdx
 by_cases h1:t=Nat.land v 15
 ·subst h1;rw[Nat.beq_refl,Bool.cond_true,beq_f (show Nat.shiftRight v 4≠Nat.land v 15 by omega),Bool.cond_false,Nat.beq_refl,Bool.cond_true]
 ·by_cases h2:t=Nat.shiftRight v 4
  ·subst h2;rw[beq_f h1,Bool.cond_false,Nat.beq_refl,Bool.cond_true,Nat.beq_refl,Bool.cond_true]
  ·rw[beq_f h1,Bool.cond_false,beq_f h2,Bool.cond_false,beq_f h1,Bool.cond_false,beq_f h2,Bool.cond_false]
private lemma idxOf_lt {nv:Nat} {perm:List Nat} (hp:perm.all (validSwapNv nv)=true) {t:Nat} (ht:t<nv) :
  idxOf perm t<nv:=by
 unfold idxOf;induction perm generalizing t with
 | nil=>exact ht
 | cons v rest ih=>simp only[List.all_cons,Bool.and_eq_true]at hp;exact ih hp.2 (swapIdx_lt hp.1 ht)
private lemma idxOf_rev_inv {nv:Nat} {perm:List Nat} (hp:perm.all (validSwapNv nv)=true) (t:Nat) :
  idxOf perm.reverse (idxOf perm t)=t:=by
 unfold idxOf;induction perm generalizing t with
 | nil=>rfl
 | cons v rest ih=>
  simp only[List.all_cons,Bool.and_eq_true]at hp
  simpa[List.reverse_cons,List.foldl_append,ih hp.2]using swapIdx_invol hp.1
private def hasUndirEdge (es:List (Nat×Nat)) (u v:Nat):Bool:=
 es.any λe=>(Nat.beq e.1 u&&Nat.beq e.2 v)||(Nat.beq e.1 v&&Nat.beq e.2 u)
def autoSwapNvOK(mask:Nat)(perm:List Nat):Bool:=
 let nv:=(activeVars mask).length;let es:=faceEdgesNv mask
 perm.all (validSwapNv nv)&&es.all λe=>hasUndirEdge es (idxOf perm e.1) (idxOf perm e.2)
private def permRow (nv:Nat) (perm:List Nat) (r:Nat):Nat:=
 sampleRowFrom nv (λk=>if r.testBit (idxOf perm k)then 1 else 0) 0
private lemma permRow_tb (nv:Nat) (perm:List Nat) (r i:Nat) :
  (permRow nv perm r).testBit i=(decide (i<nv)&&r.testBit (idxOf perm i)):=by
 unfold permRow;rw[sampleRowFrom_tb];cases r.testBit (idxOf perm i)<;>simp
private lemma permRow_lt (nv:Nat) (perm:List Nat) (r:Nat):permRow nv perm r<2^nv:=
 lt_two_pow_of_testBit λi hi=>by rw[permRow_tb,decide_eq_false (Nat.not_lt_of_ge hi),Bool.false_and]
private lemma permRow_inv {nv:Nat} {perm:List Nat} (hp:perm.all (validSwapNv nv)=true) {r:Nat} (hr:r<2^nv) :
  permRow nv perm.reverse (permRow nv perm r)=r:=by
 have hpR:perm.reverse.all (validSwapNv nv)=true:=by simpa[List.all_eq_true]using List.all_eq_true.mp hp
 apply Nat.eq_of_testBit_eq;intro i;rw[permRow_tb]
 by_cases hi:i<nv
 ·rw[decide_eq_true hi,Bool.true_and,permRow_tb,decide_eq_true (idxOf_lt hpR hi),Bool.true_and]
  have hinv:=idxOf_rev_inv hpR i;rw[List.reverse_reverse]at hinv;rw[hinv]
 ·rw[decide_eq_false hi,Bool.false_and,testBit_eq_false_of_lt_pow hr (Nat.le_of_not_lt hi)]
private lemma autoSwapNvOK_goal {mask:Nat} {perm:List Nat} (hok:autoSwapNvOK mask perm=true) {r:Nat} (hr:r<2^(activeVars mask).length) :
  (faceGoalNv mask).testBit (permRow (activeVars mask).length perm.reverse r)=(faceGoalNv mask).testBit r:=by
 let nv:=(activeVars mask).length;obtain⟨hp,hedges⟩:=Bool.and_eq_true _ _ |>.mp hok
 have hpR:perm.reverse.all (validSwapNv nv)=true:=by simpa[List.all_eq_true]using List.all_eq_true.mp hp
 have hbij a b (ha:a<nv) (hb:b<nv):hasUndirEdge (faceEdgesNv mask) (idxOf perm a) (idxOf perm b)=true↔hasUndirEdge (faceEdgesNv mask) a b=true:=by
  let S:Finset (Fin nv×Fin nv):=Finset.univ.filter λp=>hasUndirEdge (faceEdgesNv mask) p.1.1 p.2.1=true
  let f:Fin nv×Fin nv->Fin nv×Fin nv:=λp=>(⟨idxOf perm p.1.1,idxOf_lt hp p.1.2⟩,⟨idxOf perm p.2.1,idxOf_lt hp p.2.2⟩)
  have hf_inj:Function.Injective f:=λ_ _ he=>Prod.ext
   (Fin.ext <| by simpa[f,idxOf_rev_inv hp]using congrArg (λx=>idxOf perm.reverse x.1.1) he)
   (Fin.ext <| by simpa[f,idxOf_rev_inv hp]using congrArg (λx=>idxOf perm.reverse x.2.1) he)
  have hf_eq:S.image f=S:=Finset.eq_of_subset_of_card_le (λ_ hy=>by
   obtain⟨p,hpS,rfl⟩:=Finset.mem_image.mp hy;simp[S]at hpS ⊢
   obtain⟨e,he,hbe⟩:=List.any_eq_true.mp hpS;simp[Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq]at hbe
   have hsym u v:hasUndirEdge (faceEdgesNv mask) u v=hasUndirEdge (faceEdgesNv mask) v u:=by simp[hasUndirEdge,Bool.or_comm]
   rcases hbe with ⟨h1,h2⟩|⟨h1,h2⟩<;>[skip;rw[hsym]]<;>(dsimp[f];rw[<-h1,<-h2];exact List.all_eq_true.mp hedges e he))
   (by rw[Finset.card_image_of_injective S hf_inj])
  simpa[S,f]using (⟨λh=>let⟨_,hq,hfq⟩:=Finset.mem_image.mp (hf_eq.symm▸h);hf_inj hfq▸hq,
   λh=>hf_eq▸Finset.mem_image_of_mem f h⟩:f (⟨a,ha⟩,⟨b,hb⟩)∈S↔(⟨a,ha⟩,⟨b,hb⟩)∈S)
 have hgoal_iff x (hx:x<2^(activeVars mask).length):(faceGoalNv mask).testBit x=true↔∃a < nv,∃b < nv,hasUndirEdge (faceEdgesNv mask) a b=true/\x.testBit a=true/\x.testBit b=true:=by
  rw[faceGoalNv_tb];simp only[List.any_eq_true,Bool.and_eq_true]
  refine⟨λ⟨e,he,h1,h2⟩=>by
   have hlt:=faceEdgesNv_lt he;simp[hiC_bits (activeVars_le mask) hlt.1,hiC_bits (activeVars_le mask) hlt.2,hx]at h1 h2;exact⟨e.1,hlt.1,e.2,hlt.2,List.any_eq_true.mpr ⟨e,he,by simp⟩,h1,h2⟩,
   λ⟨_,_,_,_,hedge,h1,h2⟩=>by obtain⟨e,he,hbe⟩:=List.any_eq_true.mp hedge;simp only[Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq]at hbe;have hlt:=faceEdgesNv_lt he;refine⟨e,he,?_,?_⟩<;>rw[hiC_bits (activeVars_le mask) (by first| exact hlt.1| exact hlt.2),decide_eq_true hx,Bool.true_and]<;>rcases hbe with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>assumption⟩
 apply Bool.eq_iff_iff.mpr;rw[hgoal_iff _ (permRow_lt nv perm.reverse r),hgoal_iff _ hr]
 refine⟨λ⟨a,ha,b,hb,hedge,h1,h2⟩=> ?_,λ⟨a,ha,b,hb,hedge,h1,h2⟩=> ?_⟩
 ·simp[permRow_tb,ha,hb]at h1 h2
  refine⟨idxOf perm.reverse a,idxOf_lt hpR ha,idxOf perm.reverse b,idxOf_lt hpR hb,?_,h1,h2⟩
  rw[<-hbij _ _ (idxOf_lt hpR ha) (idxOf_lt hpR hb)]
  have ha':=idxOf_rev_inv hpR a;have hb':=idxOf_rev_inv hpR b;rw[List.reverse_reverse]at ha' hb';rwa[ha',hb']
 ·exact⟨idxOf perm a,idxOf_lt hp ha,idxOf perm b,idxOf_lt hp hb,(hbij a b ha hb).mpr hedge,
   by rw[permRow_tb,decide_eq_true (idxOf_lt hp ha),Bool.true_and,idxOf_rev_inv hp];exact h1,by rw[permRow_tb,decide_eq_true (idxOf_lt hp hb),Bool.true_and,idxOf_rev_inv hp];exact h2⟩
private def permWord (nv:Nat) (perm:List Nat) (w:Nat):Nat:=
 sampleRowFrom (2^nv) (λk=>if w.testBit (permRow nv perm k)then 1 else 0) 0
private lemma permWord_tb (nv:Nat) (perm:List Nat) (w r:Nat) :
  (permWord nv perm w).testBit r=(decide (r<2^nv)&&w.testBit (permRow nv perm r)):=by
 unfold permWord;rw[sampleRowFrom_tb];cases w.testBit (permRow nv perm r)<;>simp
private lemma permWord_lt (nv:Nat) (perm:List Nat) (w:Nat):ValidWord nv (permWord nv perm w):=
 lt_two_pow_of_testBit λr hr=>by rw[permWord_tb,decide_eq_false (Nat.not_lt_of_ge hr),Bool.false_and]
private lemma permWord_hiC {nv u:Nat} {perm:List Nat} (hnv:nv<=12) (hp:perm.all (validSwapNv nv)=true) (hu:u<nv) :
  permWord nv perm (hiC nv u)=hiC nv (idxOf perm u):=Nat.eq_of_testBit_eq λr=>by
 rw[permWord_tb,hiC_bits hnv (idxOf_lt hp hu)]
 by_cases hr:r<2^nv
 ·rw[decide_eq_true hr,Bool.true_and,hiC_bits hnv hu,decide_eq_true (permRow_lt nv perm r),Bool.true_and,permRow_tb,decide_eq_true hu,Bool.true_and]
 ·simp[hr]
private lemma permWord_zN (nv op x y:Nat) (perm:List Nat) :
  permWord nv perm (zN op x y)=zN op (permWord nv perm x) (permWord nv perm y):=Nat.eq_of_testBit_eq λr=>by
 rw[permWord_tb,zN_spec,zN_spec,permWord_tb,permWord_tb]
 by_cases hr:r<2^nv
 ·simp[hr]
 ·simp[hr,decide_false,Bool.false_and];rcases op with _|_|_|_<;>rfl
noncomputable def fastStateN {β:Type} (nv:Nat) (initW:List Nat) (hiB:B16 Nat)
  (gates:List (Nat×Nat×Nat)) (liveM:Nat) (perm:List Nat) (k:List Nat->β):β:=
 match perm with
 | []=>decodeBankFwd gates initW λbank=>k (selectLive liveM bank)
 | _::_=>
  forceList (λt=>b16Get hiB (idxOf perm t)) (List.range nv) λinitP=>
  decodeBankFwd gates initP λbank=>k (selectLive liveM bank)
noncomputable def subsetWordsN(xs ys:List Nat):Bool:=
 @List.rec Nat (λ_=>Bool) true (λx _ ih=>cond (anyEq x ys) ih false) xs
noncomputable def sameWordsN(xs ys:List Nat):Bool:=
 and (Nat.beq xs.length ys.length) (subsetWordsN xs ys)
private lemma sameWordsN_toFinset {xs ys:List Nat} (hnd:xs.Nodup) (hok:sameWordsN xs ys=true) :
  xs.toFinset=ys.toFinset:=by
 simp[sameWordsN,Bool.and_eq_true,Nat.beq_eq]at hok
 have hsub:∀l,subsetWordsN l ys=true->∀x∈l,x∈ys:=λl=>by
  induction l with
  | nil=>intro _ _ h;simp at h
  | cons a l ih=>
   intro hs x hx;change cond (anyEq a ys) (subsetWordsN l ys) false=true at hs
   cases ha:anyEq a ys
   ·rw[ha,Bool.cond_false]at hs;cases hs
   ·rw[ha,Bool.cond_true]at hs
    rcases List.mem_cons.mp hx with rfl|ht
    ·exact(anyEq_iff x ys).mp ha
    ·exact ih hs x ht
 have hsf:xs.toFinset⊆ys.toFinset:=λx hx=>List.mem_toFinset.mpr (hsub xs hok.2 x (List.mem_toFinset.mp hx))
 have hle:ys.toFinset.card<=xs.toFinset.card:=by
  rw[List.toFinset_card_of_nodup hnd,hok.1];exact List.toFinset_card_le ys
 exact Finset.eq_of_subset_of_card_le hsf hle
private lemma permWord_inv {nv:Nat} {perm:List Nat} (hp:perm.all (validSwapNv nv)=true) {w:Nat} (hw:ValidWord nv w) :
  permWord nv perm (permWord nv perm.reverse w)=w:=Nat.eq_of_testBit_eq λr=>by
 rw[permWord_tb];by_cases hr:r<2^nv
 ·rw[decide_eq_true hr,Bool.true_and,permWord_tb,decide_eq_true (permRow_lt nv perm r),Bool.true_and,permRow_inv hp hr]
 ·rw[decide_eq_false hr,Bool.false_and,testBit_eq_false_of_lt_pow hw (Nat.le_of_not_lt hr)]
theorem fastStateN_sound {mask kChild liveM:Nat} {hiB:B16 Nat} {gates:List (Nat×Nat×Nat)} {perm cws:List Nat}
  (hhi:∀u < (activeVars mask).length,b16Get hiB u=hiC (activeVars mask).length u)
  (haut:autoSwapNvOK mask perm=true) (hnd:cws.Nodup)
  (hsame:fastStateN (activeVars mask).length (varsNv (activeVars mask).length) hiB gates liveM perm (λrws=>sameWordsN cws rws)=true)
  (himp:ImpossibleNv (activeVars mask).length (faceGoalNv mask) kChild (selectLive liveM (decodeBank gates (varsNv (activeVars mask).length))).toFinset) :
  ImpossibleNv (activeVars mask).length (faceGoalNv mask) kChild cws.toFinset:=by
 let nv:=(activeVars mask).length;let goal:=faceGoalNv mask
 cases perm with
 | nil=>dsimp[fastStateN]at hsame;rw[decodeBankFwd_spec]at hsame;exact(sameWordsN_toFinset hnd hsame).symm▸himp
 | cons p0 ps=>
  let pm:=p0::ps;have hp:pm.all (validSwapNv nv)=true:=(Bool.and_eq_true _ _ |>.mp haut).1
  have hp0 p:permWord nv p 0=0:=Nat.eq_of_testBit_eq λr=>by simp[permWord_tb]
  have hinit:((List.range nv).map λt=>b16Get hiB (idxOf pm t))=(varsNv nv).map (permWord nv pm):=by
   simp only[varsNv,List.map_map];exact List.map_congr_left λt ht=>
     (hhi _ (idxOf_lt hp (List.mem_range.mp ht))).trans (permWord_hiC (activeVars_le mask) hp (List.mem_range.mp ht)).symm
  have hdec_map:∀gs init,decodeBank gs (init.map (permWord nv pm))=(decodeBank gs init).map (permWord nv pm):=λgs=>by
   induction gs with| nil=>exact λ_=>rfl| cons g _ ih=>
     intro init;rcases g with ⟨op,a,b⟩;simp[decodeBank]
     have hg i:listGetN (init.map (permWord nv pm)) i=permWord nv pm (listGetN init i):=by
      simp[listGetN_eq_getD,List.getElem?_map];cases init[i]?<;>[exact(hp0 pm).symm;rfl]
     rw[hg a,hg b,<-permWord_zN,<-List.map_singleton,<-List.map_append];exact ih _
  dsimp[fastStateN]at hsame
  rw[forceList_eq,decodeBankFwd_spec,show(activeVars mask).length=nv from rfl,hinit,hdec_map,selectLive_map]at hsame
  have hpR:pm.reverse.all (validSwapNv nv)=true:=by simpa[List.all_eq_true]using hp
  have hinvL w (hw:ValidWord nv w):permWord nv pm.reverse (permWord nv pm w)=w:=by simpa using permWord_inv hpR hw
  have hinj {x y} (hx:ValidWord nv x) (hy:ValidWord nv y) (he:permWord nv pm.reverse x=permWord nv pm.reverse y):x=y:=by
   have:=congrArg (permWord nv pm) he;rwa[permWord_inv hp hx,permWord_inv hp hy]at this
  have hprop w (h:properNv nv w):properNv nv (permWord nv pm.reverse w):=
   ⟨permWord_lt nv pm.reverse w,λe=>h.2.1 (hinj h.1 (Nat.two_pow_pos _) (e.trans (hp0 _).symm)),
    λe=>h.2.2 (hinj h.1 (maskC_lt nv) (e.trans (Nat.eq_of_testBit_eq λr=>by rw[permWord_tb,testBit_maskC];by_cases hr:r<2^nv<;>simp[hr,testBit_maskC,permRow_lt]).symm))⟩
  have hgl:permWord nv pm.reverse goal=goal:=Nat.eq_of_testBit_eq λr=>by
   rw[permWord_tb];by_cases hr:r<2^nv
   . rw[decide_eq_true hr,Bool.true_and];exact autoSwapNvOK_goal haut hr
   . rw[decide_eq_false hr,Bool.false_and,testBit_eq_false_of_lt_pow (faceGoalNv_lt mask) (Nat.le_of_not_lt hr)]
  have hlm:∀{k S},LiveNv nv goal k S->LiveNv nv goal k (S.image (permWord nv pm.reverse)):=by
   intro k S hl;induction hl using LiveNv.ind with
   | stop hpG=>rw[Finset.image_singleton,hgl];exact LiveNv.stop hpG
   | @binary k U a b d hd ha hb hab hf tl ih=>
     rw[Finset.image_insert,Finset.image_insert];rw[Finset.image_insert,permWord_zN]at ih
     refine LiveNv.binary hd (hprop a ha) (hprop b hb) (λe=>hab (hinj ha.1 hb.1 e)) (λhm=> ?_) ih
     rw[<-permWord_zN,<-Finset.image_insert,<-Finset.image_insert,Finset.mem_image]at hm
     obtain⟨y,hy,hye⟩:=hm;exact hf ((hinj (zN_lt ha.1 hb.1) (liveNv_proper (LiveNv.binary hd ha hb hab hf tl) y hy).1 hye.symm)▸hy)
  have hvs w (hw:w∈selectLive liveM (decodeBank gates (varsNv nv))):ValidWord nv w:=by
   have hs:∀m (l:List Nat),(selectLive m l).Sublist l:=λm l=>by
     induction l generalizing m with| nil=>exact .slnil| cons a _ ih=>simp only[selectLive];cases Nat.beq (Nat.land m 1) 1<;>[exact .cons a (ih _);exact .cons_cons a (ih _)]
   exact decodeBank_valid gates (varsNv nv) (λ_ hv=>let⟨u,_,e⟩:=List.mem_map.mp hv;e▸hiC_lt nv u) w ((hs liveM _).subset hw)
  have himg:cws.toFinset.image (permWord nv pm.reverse)=(selectLive liveM (decodeBank gates (varsNv nv))).toFinset:=by
   rw[sameWordsN_toFinset hnd hsame];ext x;simp only[Finset.mem_image,List.mem_toFinset,List.mem_map]
   exact⟨λ⟨_,⟨w,hw,rfl⟩,e⟩=>(hinvL w (hvs w hw)▸e)▸hw,λhx=>⟨_,⟨x,hx,rfl⟩,hinvL x (hvs x hx)⟩⟩
  exact λk hk hl=>himp k hk (himg▸hlm hl)
abbrev LevelTopo:=Nat×Nat×(Nat->Nat)
noncomputable def unpackTopoStep(pBits pMask:Nat):Nat->Nat->Nat->Nat×Nat
 | 0,p,s=>(p,Nat.land s 0xfff)
 | r+1,p,s=>
  forceN (Nat.shiftRight s 12) λs1=>
  let tag:=Nat.land s1 7
  forceN (Nat.shiftRight s1 3) λs2=>
  cond (Nat.beq tag 7)
   (forceN (Nat.land s2 pMask) λp'=>forceN (Nat.shiftRight s2 pBits) λs3=>unpackTopoStep pBits pMask r p' s3)
   (forceN (Nat.add p tag) λp'=>unpackTopoStep pBits pMask r p' s2)
noncomputable def unpackTopo(lv:LevelTopo)(idx:Nat):Nat×Nat:=
 let pBits:=lv.2.1
 forceN (Nat.sub (Nat.shiftLeft 1 pBits) 1) λpMask=>
 forceN (lv.2.2 (Nat.shiftRight idx 4)) λw=>
 unpackTopoStep pBits pMask (Nat.land idx 15) (Nat.land w pMask) (Nat.shiftRight w pBits)
def encMove(ii jj op md:Nat):Nat:=
 Nat.lor ii (Nat.lor (Nat.shiftLeft jj 4) (Nat.lor (Nat.shiftLeft op 8) (Nat.shiftLeft md 10)))
private lemma encMove_fields {ii jj op md:Nat} (hii:ii<16) (hjj:jj<16) (hop:op<4) (hmd:md<4) :
  let m:=encMove ii jj op md
  Nat.land m 15=ii/\Nat.land (Nat.shiftRight m 4) 15=jj /\
  Nat.land (Nat.shiftRight m 8) 3=op/\Nat.land (Nat.shiftRight m 10) 3=md:=by
 have hb:∀k x,x<2^k->∀t≥k,x.testBit t=false:=λk x hx t ht=>testBit_eq_false_of_lt_pow hx ht
 have h1:∀a b,Nat.land a (2^b-1)=a % 2^b:=λa b=>by
  apply Nat.eq_of_testBit_eq;intro t;rw[Nat.land_eq,Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow];exact Bool.and_comm ..
 dsimp;refine⟨?_,?_,?_,?_⟩<;>apply Nat.eq_of_testBit_eq<;>intro t <;>
  simp only[encMove,Nat.lor_eq,Nat.testBit_and,Nat.testBit_or,tb_shl,
   show(15:Nat)=2^4-1 from rfl,show(3:Nat)=2^2-1 from rfl,Nat.testBit_two_pow_sub_one]
 ·by_cases ht:t<4
  ·simp[ht,show ¬4<=t by omega,show ¬8<=t by omega,show ¬10<=t by omega]
  ·simp[ht,hb 4 ii hii t (by omega)]
 ·by_cases ht:t<4
  ·simp[ht,hb 4 ii hii (4+t) (by omega),show 4<=4+t by omega,show 4+t-4=t by omega,
    show ¬8<=4+t by omega,show ¬10<=4+t by omega]
  ·simp[ht,hb 4 jj hjj t (by omega)]
 ·by_cases ht:t<2
  ·simp[ht,hb 4 ii hii (8+t) (by omega),hb 4 jj hjj (8+t-4) (by omega),
    show 8<=8+t by omega,show 8+t-8=t by omega,show ¬10<=8+t by omega]
  ·simp[ht,hb 2 op hop t (by omega)]
 ·by_cases ht:t<2
  ·simp[ht,hb 4 ii hii (10+t) (by omega),hb 4 jj hjj (10+t-4) (by omega),
    hb 2 op hop (10+t-8) (by omega),show 10<=10+t by omega,show 10+t-10=t by omega]
  ·simp[ht,hb 2 md hmd t (by omega)]
def liveToBank:Nat->Nat->Nat->Nat
 | 0,_,_=>0
 | fuel+1,liveM,k=>
  cond (Nat.beq (Nat.land liveM 1) 1)
   (cond (Nat.beq k 0) 0 (Nat.add 1 (liveToBank fuel (Nat.shiftRight liveM 1) (Nat.sub k 1))))
   (Nat.add 1 (liveToBank fuel (Nat.shiftRight liveM 1) k))
def clrBit(m i:Nat):Nat:=Nat.land m (Nat.xor m (Nat.shiftLeft 1 i))
noncomputable def decodeNode(levels:Array LevelTopo)(nv:Nat):Nat->Nat->List (Nat×Nat×Nat)×Nat
 | 0,_=>([],Nat.sub (Nat.shiftLeft 1 nv) 1)
 | d+1,idx=>
  match unpackTopo (levels.getD (d+1) (0,0,λ_=>0)) idx with
  | (pIdx,m12)=>
   forceN pIdx λpIdx'=>forceN m12 λm12'=>
   let ii:=Nat.land m12' 15;let jj:=Nat.land (Nat.shiftRight m12' 4) 15
   let op:=Nat.land (Nat.shiftRight m12' 8) 3;let km:=Nat.land (Nat.shiftRight m12' 10) 3
   match decodeNode levels nv d pIdx' with
   | (gates,liveM)=>
    forceN liveM λliveM'=>
    let bankSz:=Nat.add nv d
    forceN (liveToBank bankSz liveM' ii) λa=>
    forceN (liveToBank bankSz liveM' jj) λb=>
    forceN (cond (Nat.beq (Nat.land km 2) 2) liveM' (clrBit liveM' a)) λm1=>
    forceN (cond (Nat.beq (Nat.land km 1) 1) m1 (clrBit m1 b)) λm2=>
    (gates++[(op,a,b)],Nat.lor m2 (Nat.shiftLeft 1 bankSz))
noncomputable def stateOf(levels:Array LevelTopo)(nv d idx:Nat):List Nat:=
 let(gates,liveM):=decodeNode levels nv d idx
 selectLive liveM (decodeBank gates (varsNv nv))
def dropAt{α:Type}:Nat->List α->List α
 | _,[]=>[]
 | 0,_::xs=>xs
 | k+1,x::xs=>x::dropAt k xs
def buildChildWs(cur:Nat):List Nat->Nat->Nat->Nat->Bool->Bool->List Nat
 | [],_,_,z,_,_=>[z]
 | w::rest,ii,jj,z,ka,kb=>
  let keep:=and (or ka (not (Nat.beq cur ii))) (or kb (not (Nat.beq cur jj)))
  cond keep (w::buildChildWs (Nat.add cur 1) rest ii jj z ka kb)
   (buildChildWs (Nat.add cur 1) rest ii jj z ka kb)
private lemma clrBit_tb (m i k:Nat):(clrBit m i).testBit k=(if i=k then false else m.testBit k):=by
 simp only[clrBit,Nat.land_eq,Nat.xor_eq,Nat.testBit_and,Nat.testBit_xor,shl_one,Nat.testBit_two_pow]
 by_cases e:i=k
 ·subst e;cases m.testBit i<;>simp
 ·cases m.testBit k<;>simp[e]
private lemma clrBit_lt {m n i:Nat} (hm:m<2^n):clrBit m i<2^n:=
 lt_two_pow_of_testBit λk hk=>by rw[clrBit_tb];split_ifs<;>[rfl;exact testBit_eq_false_of_lt_pow hm hk]
private lemma decodeNode_wf (levels:Array LevelTopo) (nv d idx:Nat) :
  let r:=decodeNode levels nv d idx
  r.1.length=d/\r.2<2^(nv+d):=by
 induction d generalizing idx with
 | zero=>
  simp only[decodeNode,List.length_nil,Nat.add_zero,Nat.sub_eq,shl_one]
  exact⟨trivial,Nat.sub_lt (Nat.two_pow_pos nv) (by decide)⟩
 | succ d ih=>
  simp only[decodeNode,forceN_eq]
  obtain⟨hl,hm⟩:=ih (unpackTopo (levels.getD (d+1) (0,0,λ_=>0)) idx).1
  set liveM:=(decodeNode levels nv d _).2
  have hlt2:∀(ka kb:Bool)(a b:Nat),(cond kb (cond ka liveM (clrBit liveM a)) (clrBit (cond ka liveM (clrBit liveM a)) b))<2^(nv+d):=λka kb a b=>by
   have hm1:cond ka liveM (clrBit liveM a)<2^(nv+d):=by cases ka<;>[exact clrBit_lt hm;exact hm]
   cases kb<;>[exact clrBit_lt hm1;exact hm1]
  refine⟨by rw[List.length_append,List.length_singleton,hl],lt_two_pow_of_testBit λk hk=> ?_⟩
  rw[Nat.lor_eq,Nat.testBit_or,shl_one,Nat.testBit_two_pow,Nat.add_eq,
   testBit_eq_false_of_lt_pow (hlt2 _ _ _ _) (by omega),decide_eq_false (by omega)];rfl
private lemma selectLive_app_one {α:Type} (bank:List α) (m:Nat) (x:α) (hm:m<2^bank.length) :
  selectLive (Nat.lor m (Nat.shiftLeft 1 bank.length)) (bank++[x])=selectLive m bank++[x]:=by
 induction bank generalizing m with
 | nil=>
  have:m=0:=by simp at hm;exact hm
  subst this;simp[selectLive]
 | cons a rest ih=>
  have hdiv:Nat.shiftRight m 1<2^rest.length:=by
   rw[shr_eq];simp[List.length_cons,Nat.pow_succ]at hm;omega
  have hb0:Nat.beq (Nat.land (Nat.lor m (Nat.shiftLeft 1 (rest.length+1))) 1) 1=Nat.beq (Nat.land m 1) 1:=by
   rw[bit0_tb,bit0_tb,Nat.lor_eq,Nat.testBit_or,shl_one,Nat.testBit_two_pow];simp
  have hshr:Nat.shiftRight (Nat.lor m (Nat.shiftLeft 1 (rest.length+1))) 1=Nat.lor (Nat.shiftRight m 1) (Nat.shiftLeft 1 rest.length):=
   Nat.eq_of_testBit_eq λk=>by
    rw[tb_shr,Nat.lor_eq,Nat.lor_eq,Nat.testBit_or,Nat.testBit_or,tb_shr,shl_one,shl_one,Nat.testBit_two_pow,Nat.testBit_two_pow]
    simp[show(rest.length+1=1+k)↔(rest.length=k) by omega]
  rw[List.cons_append,List.length_cons,selectLive,selectLive,hb0,hshr]
  cases Nat.beq (Nat.land m 1) 1
  ·simp[Bool.cond_false];exact ih _ hdiv
  ·simp only[Bool.cond_true,List.cons_append];exact congrArg (a::·) (ih _ hdiv)
private lemma liveToBank_spec {α:Type} [Inhabited α] (bank:List α) (m k:Nat) (hk:k<(selectLive m bank).length) :
  let a:=liveToBank bank.length m k
  a<bank.length/\m.testBit a=true/\bank.getD a default=(selectLive m bank).getD k default:=by
 induction bank generalizing m k with
 | nil=>simp[selectLive]at hk
 | cons x xs ih=>
  simp only[List.length_cons,selectLive,liveToBank]at hk ⊢
  cases hb:Nat.beq (Nat.land m 1) 1
  ·rw[hb,Bool.cond_false]at hk;simp only[Bool.cond_false]
   obtain⟨ha,htb,hget⟩:=ih (Nat.shiftRight m 1) k hk
   refine⟨by rw[Nat.add_eq];omega,?_,by simpa[Nat.add_eq,Nat.add_comm 1]using hget⟩
   rw[tb_shr]at htb;simpa[Nat.add_eq,Nat.add_comm 1]using htb
  ·rw[hb,Bool.cond_true]at hk;simp only[Bool.cond_true]
   cases k with
   | zero=>exact⟨Nat.zero_lt_succ _,by simpa[bit0_tb]using hb,rfl⟩
   | succ k'=>
    simp[List.length_cons]at hk
    obtain⟨ha,htb,hget⟩:=ih (Nat.shiftRight m 1) k' (by omega)
    have hnz:Nat.beq (k'+1) 0=false:=rfl
    simp only[hnz,Bool.cond_false,show Nat.sub (k'+1) 1=k' by rfl]
    refine⟨by rw[Nat.add_eq];omega,?_,by simpa[Nat.add_eq,Nat.add_comm 1]using hget⟩
    rw[tb_shr]at htb;simpa[Nat.add_eq,Nat.add_comm 1]using htb
private lemma shr_clrBit_succ (m i:Nat):Nat.shiftRight (clrBit m (Nat.add 1 i)) 1=clrBit (Nat.shiftRight m 1) i:=
 Nat.eq_of_testBit_eq λt=>by rw[tb_shr,clrBit_tb,clrBit_tb,tb_shr,Nat.add_eq];simp
private lemma bit0_clrBit_succ (m i:Nat):Nat.beq (Nat.land (clrBit m (Nat.add 1 i)) 1) 1=Nat.beq (Nat.land m 1) 1:=by
 rw[bit0_tb,bit0_tb,clrBit_tb,Nat.add_eq];simp
private lemma bit0_clrBit_zero (m:Nat):Nat.beq (Nat.land (clrBit m 0) 1) 1=false:=by rw[bit0_tb,clrBit_tb];simp
private lemma shr_clrBit_zero (m:Nat):Nat.shiftRight (clrBit m 0) 1=Nat.shiftRight m 1:=
 Nat.eq_of_testBit_eq λt=>by rw[tb_shr,clrBit_tb,tb_shr];simp[show(0:Nat)≠1+t by omega]
private lemma selectLive_clrBit {α:Type} (bank:List α) (m k:Nat) (hk:k<(selectLive m bank).length) :
  selectLive (clrBit m (liveToBank bank.length m k)) bank=dropAt k (selectLive m bank):=by
 induction bank generalizing m k with
 | nil=>simp[selectLive]at hk
 | cons x xs ih=>
  simp only[List.length_cons,selectLive,liveToBank]at hk ⊢
  cases hb:Nat.beq (Nat.land m 1) 1
  ·rw[hb,Bool.cond_false]at hk;simp only[Bool.cond_false,bit0_clrBit_succ,hb,shr_clrBit_succ];exact ih _ k hk
  ·rw[hb,Bool.cond_true]at hk;simp only[Bool.cond_true]
   cases k with
   | zero=>simp only[show Nat.beq 0 0=true from rfl,Bool.cond_true,dropAt,bit0_clrBit_zero,Bool.cond_false,shr_clrBit_zero]
   | succ k'=>
    simp only[List.length_cons]at hk
    simp only[show Nat.beq (k'+1) 0=false from rfl,Bool.cond_false,show Nat.sub (k'+1) 1=k' by rfl,
     bit0_clrBit_succ,hb,Bool.cond_true,shr_clrBit_succ,dropAt]
    exact congrArg (x::·) (ih _ k' (by omega))
private lemma liveToBank_clrBit_gt {α:Type} (bank:List α) (m i j:Nat) (hij:i<j) (hj:j<(selectLive m bank).length) :
  liveToBank bank.length (clrBit m (liveToBank bank.length m i)) (j-1)=liveToBank bank.length m j:=by
 induction bank generalizing m i j with
 | nil=>simp[selectLive]at hj
 | cons x xs ih=>
  simp only[List.length_cons,selectLive,liveToBank]at hj ⊢
  cases hb:Nat.beq (Nat.land m 1) 1
  ·rw[hb,Bool.cond_false]at hj;simp only[Bool.cond_false,bit0_clrBit_succ,hb,shr_clrBit_succ]
   exact congrArg (Nat.add 1) (ih _ i j hij hj)
  ·rw[hb,Bool.cond_true]at hj;simp only[Bool.cond_true]
   cases j with
   | zero=>omega
   | succ j'=>
    simp[List.length_cons]at hj
    cases i with
    | zero=>simp only[show Nat.beq 0 0=true from rfl,Bool.cond_true,show Nat.beq (j'+1) 0=false from rfl,Bool.cond_false,show Nat.sub (j'+1) 1=j' by rfl,bit0_clrBit_zero,shr_clrBit_zero];rfl
    | succ i'=>
     have hnz:∀n,Nat.beq (n+1) 0=false:=λ_=>rfl
     simp only[hnz,Bool.cond_false,show Nat.sub (i'+1) 1=i' by rfl,show Nat.sub (j'+1) 1=j' by rfl,
      bit0_clrBit_succ,hb,Bool.cond_true,shr_clrBit_succ]
     cases j' with
     | zero=>omega
     | succ j''=>
      simp only[show j''+1+1-1=j''+1 by rfl,hnz j'',Bool.cond_false,show Nat.sub (j''+1) 1=j'' by rfl]
      exact congrArg (Nat.add 1) (ih _ i' (j''+1) (by omega) (by omega))
private lemma dropAt_len {α:Type}:∀(l:List α)(k:Nat),k<l.length->(dropAt k l).length=l.length-1
 | [],_,h=>by simp at h
 | _::_,0,_=>by simp[dropAt]
 | _::xs,k+1,hk=>by simp[dropAt,List.length_cons]at hk ⊢;have:=dropAt_len xs k (by omega);omega
private lemma dropAt_getD:∀(l:List Nat)(a b:Nat),a<b->(dropAt a l).getD (b-1) 0=l.getD b 0
 | [],_,_,_=>by simp[dropAt]
 | _::_,0,0,h=>by omega
 | _::_,0,_+1,_=>by simp[dropAt]
 | _::xs,a+1,b,hab=>by rcases b with _|_|b''<;>[omega;omega;exact dropAt_getD xs a (b''+1) (by omega)]
private lemma buildChildWs_eq_dropAt (ws:List Nat) (ii jj z:Nat) (ka kb:Bool) (hij:ii<jj) :
  buildChildWs 0 ws ii jj z ka kb =
   (cond kb id (dropAt (cond ka jj (jj-1)))) ((cond ka id (dropAt ii)) ws)++[z]:=by
 have hpl:∀(zs:List Nat)(c c0 c1:Nat),c<c1->c0<c1->buildChildWs c1 zs c c0 z ka kb=zs++[z]:=λzs=>by
  induction zs with| nil=>intros;rfl| cons q _ ih=>intro c c0 c1 h1 h2;simp only[buildChildWs,beq_f (show c1≠c by omega),beq_f (show c1≠c0 by omega),Bool.not_false,Bool.or_true,Bool.and_self,Bool.cond_true,List.cons_append,Nat.add_eq];exact congrArg (q::·) (ih c c0 (c1+1) (by omega) (by omega))
 have h1:∀(ys:List Nat)(c c0 k:Nat),c<c0->buildChildWs c0 ys c (c0+k) z ka kb=(cond kb id (dropAt k)) ys++[z]:=λys=>by
  induction ys with
  | nil=>intros;cases kb<;>simp[buildChildWs,dropAt]
  | cons _ ys' ih=>
   intro c c0 k hc0;simp[buildChildWs,beq_f (show c0≠c by omega),Bool.not_false,Bool.true_and]
   cases k with
   | zero=>simp[hpl ys' c c0 (c0+1) (by omega) (by omega)];cases kb<;>simp[dropAt]
   | succ k'=>simp[beq_f (show c0≠c0+(k'+1) by omega)];rw[show c0+(k'+1)=(c0+1)+k' by omega,ih c (c0+1) k' (by omega)];cases kb<;>simp[dropAt]
 have go (l:List Nat) (c i j:Nat) (h:i<j) :
   buildChildWs c l (c+i) (c+j) z ka kb=(cond kb id (dropAt (cond ka j (j-1)))) ((cond ka id (dropAt i)) l)++[z]:=by
  induction l generalizing c i j with
  | nil=>cases ka<;>cases kb<;>simp[buildChildWs,dropAt]
  | cons _ xs ih=>
   simp[buildChildWs];rcases i with _|i'<;>rcases j with _|j'
   ·omega
   ·simp[beq_f (show c≠c+(j'+1) by omega)]
    rw[show c+(j'+1)=(c+1)+j' by omega,h1 xs c (c+1) j' (by omega)];cases ka<;>cases kb<;>simp[dropAt]
   ·omega
   ·simp[beq_f (show c≠c+(i'+1) by omega),beq_f (show c≠c+(j'+1) by omega)]
    rw[show c+(i'+1)=(c+1)+i' by omega,show c+(j'+1)=(c+1)+j' by omega,ih (c+1) i' j' (by omega)]
    rcases j' with _|j''<;>[omega;cases ka<;>cases kb<;>simp[dropAt]]
 simpa using go ws 0 ii jj hij
private lemma decodeNode_tree_edge (levels:Array LevelTopo) (nv d pIdx cIdx ii jj op km:Nat)
  (hii:ii<16) (hjj16:jj<16) (hop:op<4) (hkm:km<4)
  (hmatch:unpackTopo (levels.getD (d+1) (0,0,λ_=>0)) cIdx=(pIdx,encMove ii jj op km))
  (hij:ii<jj) (hjj:jj<(stateOf levels nv d pIdx).length) :
  let ws:=stateOf levels nv d pIdx
  stateOf levels nv (d+1) cIdx=buildChildWs 0 ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) (Nat.beq (Nat.land km 2) 2) (Nat.beq (Nat.land km 1) 1):=by
 obtain⟨hf1,hf2,hf3,hf4⟩:=encMove_fields hii hjj16 hop hkm
 unfold stateOf;simp only[decodeNode,forceN_eq,hmatch,hf1,hf2,hf3,hf4]
 generalize hpar:decodeNode levels nv d pIdx=par;obtain⟨hlenG,hltM⟩:=hpar▸decodeNode_wf levels nv d pIdx
 let bank:=decodeBank par.1 (varsNv nv)
 have hdec_len:∀gs init,(decodeBank gs init).length=init.length+gs.length:=λgs=>by
  induction gs with| nil=>exact λ_=>by simp[decodeBank]| cons _ _ ih=>intro _;simp[decodeBank,ih];omega
 have hlenB:bank.length=nv+d:=by simp[bank,hdec_len,varsNv,hlenG]
 have hws:stateOf levels nv d pIdx=selectLive par.2 bank:=by simp[stateOf,hpar,bank]
 rw[hws]at hjj;simp only[Nat.add_eq]
 have hget i (hi:i<(selectLive par.2 bank).length):listGetN bank (liveToBank (nv+d) par.2 i)=listGetN (selectLive par.2 bank) i:=by
  rw[listGetN_eq_getD,listGetN_eq_getD,<-hlenB];exact(liveToBank_spec bank par.2 i hi).2.2
 have hdec_app:∀gs g init,decodeBank (gs++[g]) init=decodeBank gs init++[zN g.1 (listGetN (decodeBank gs init) g.2.1) (listGetN (decodeBank gs init) g.2.2)]:=λgs g=>by
  induction gs with| nil=>exact λ_=>rfl| cons _ _ ih=>intro _;simp[decodeBank,ih]
 rw[hdec_app];change selectLive _ (bank++[zN op (listGetN bank _) (listGetN bank _)])=_
 rw[hget ii (lt_trans hij hjj),hget jj hjj,<-hlenB]
 let ka:=Nat.beq (Nat.land km 2) 2;let kb:=Nat.beq (Nat.land km 1) 1
 let m1:=cond ka par.2 (clrBit par.2 (liveToBank bank.length par.2 ii));let m2:=cond kb m1 (clrBit m1 (liveToBank bank.length par.2 jj))
 have hm1:m1<2^bank.length:=by rw[hlenB];dsimp[m1];cases ka<;>[exact clrBit_lt hltM;exact hltM]
 have hm2:m2<2^bank.length:=by dsimp[m2];cases kb<;>[exact clrBit_lt hm1;exact hm1]
 rw[selectLive_app_one bank m2 _ hm2,buildChildWs_eq_dropAt _ ii jj _ ka kb hij];congr 1
 have hsel1:selectLive m1 bank=(cond ka id (dropAt ii)) (selectLive par.2 bank):=by
  cases hka:ka<;>simp only[m1,hka,Bool.cond_false,Bool.cond_true,id];exact selectLive_clrBit bank par.2 ii (lt_trans hij hjj)
 have hb_eq:liveToBank bank.length par.2 jj=liveToBank bank.length m1 (cond ka jj (jj-1)):=by
  cases hka:ka<;>simp only[m1,hka,Bool.cond_false,Bool.cond_true];exact(liveToBank_clrBit_gt bank par.2 ii jj hij hjj).symm
 have hjj1:cond ka jj (jj-1)<(selectLive m1 bank).length:=by
  rw[hsel1];cases ka<;>[rw[Bool.cond_false,Bool.cond_false,dropAt_len _ ii (lt_trans hij hjj)];exact hjj];omega
 cases hkb:kb;· simp only[m2,hkb,Bool.cond_false,hb_eq];rw[selectLive_clrBit bank m1 _ hjj1,hsel1]
 ·simp only[m2,hkb,Bool.cond_true,id,hsel1];rfl
private lemma buildChildWs_nodup_toFinset {ws:List Nat} {ii jj z:Nat} {ka kb:Bool}
  (hnd:ws.Nodup) (hij:ii<jj) (hjj:jj<ws.length) (hz:z∉ws) :
  let cws:=buildChildWs 0 ws ii jj z ka kb;cws.Nodup/\cws.toFinset=childSet ws ii jj z ka kb:=by
 have hdrop:∀(l:List Nat) k,l.Nodup->k<l.length->(dropAt k l).Nodup/\(dropAt k l).toFinset=l.toFinset.erase (listGetN l k):=λl=>by
  induction l with| nil=>intro _ _ h;simp at h| cons x xs ih=>
   intro k hnd' hk;obtain⟨hx,hxs⟩:=List.nodup_cons.mp hnd'
   cases k with
   | zero=>exact⟨hxs,by ext y;simp only[dropAt,List.mem_toFinset,Finset.mem_erase,List.toFinset_cons,Finset.mem_insert,listGetN];exact⟨λhy=>⟨λe=>hx (e▸hy),Or.inr hy⟩,λ⟨h1,h2⟩=>h2.resolve_left h1⟩⟩
   | succ k'=>
     obtain⟨hdn,hdt⟩:=ih k' hxs (by simp at hk;exact hk)
     refine⟨List.nodup_cons.mpr ⟨λhm=>hx (List.mem_toFinset.mp (Finset.mem_of_mem_erase (hdt▸List.mem_toFinset.mpr hm))),hdn⟩,?_⟩
     ext y;simp[dropAt,List.toFinset_cons,Finset.mem_insert,hdt,Finset.mem_erase,listGetN]
     exact⟨λh=>h.elim (λe=>⟨λe'=>hx ((e▸e')▸listGetN_mem (by simp at hk;exact hk)),Or.inl e⟩) λ⟨h1,h2⟩=>⟨h1,Or.inr h2⟩,λ⟨h1,h2⟩=>h2.elim Or.inl λhy=>Or.inr ⟨h1,hy⟩⟩
 dsimp;rw[buildChildWs_eq_dropAt ws ii jj z ka kb hij];have hii:=lt_trans hij hjj
 have hstep:((cond kb id (dropAt (cond ka jj (jj-1)))) ((cond ka id (dropAt ii)) ws)).Nodup /\
   ((cond kb id (dropAt (cond ka jj (jj-1)))) ((cond ka id (dropAt ii)) ws)).toFinset =
   (if ka then if kb then ws.toFinset else ws.toFinset.erase (listGetN ws jj)
    else if kb then ws.toFinset.erase (listGetN ws ii)else(ws.toFinset.erase (listGetN ws ii)).erase (listGetN ws jj)):=by
  cases ka<;>cases kb
  ·obtain⟨hd1,ht1⟩:=hdrop ws ii hnd hii;obtain⟨hd2,ht2⟩:=hdrop (dropAt ii ws) (jj-1) hd1 (by rw[dropAt_len ws ii hii];omega)
   rw[ht1,show listGetN (dropAt ii ws) (jj-1)=listGetN ws jj by rw[listGetN_eq_getD,listGetN_eq_getD];exact dropAt_getD ws ii jj hij]at ht2;exact⟨hd2,ht2⟩
  ·exact hdrop ws ii hnd hii
  ·exact hdrop ws jj hnd hjj
  ·exact⟨hnd,rfl⟩
 refine⟨List.nodup_append.mpr ⟨hstep.1,List.nodup_singleton z,λa ha b hb=>by simp[List.mem_singleton]at hb;subst hb;have hm:=hstep.2▸List.mem_toFinset.mpr ha;exact λe=>hz (e▸by cases ka<;>cases kb<;>simp_all)⟩,?_⟩
 rw[List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_comm,Finset.insert_union,Finset.empty_union,hstep.2];cases ka<;>cases kb<;>simp[childSet]
noncomputable def scanTopoRange(nextTopo:LevelTopo)(start endIdx:Nat):Nat->Nat->List (Nat×Nat)->List (Nat×Nat)
 | _,0,acc=>acc
 | ci,len+1,acc=>
  cond (Nat.ble (Nat.add ci 1) nextTopo.1)
   (match unpackTopo nextTopo ci with
    | (p,m)=>
     forceN p λp'=>forceN m λm'=>
     let acc':=cond (and (Nat.ble start p') (Nat.ble (Nat.add p' 1) endIdx)) ((p',m')::acc) acc
     scanTopoRange nextTopo start endIdx (Nat.add ci 1) len acc')
   (scanTopoRange nextTopo start endIdx (Nat.add ci 1) len acc)
noncomputable def readTreeRangesGo(nextTopo:LevelTopo)(start endIdx cBits cMask:Nat):
  Nat->Nat->List (Nat×Nat)->List (Nat×Nat)×Nat
 | 0,s,acc=>(acc,s)
 | n+1,s,acc=>
  forceN (Nat.land s cMask) λlo=>
  forceN (Nat.shiftRight s cBits) λs1=>
  let l0:=Nat.land s1 63
  forceN (Nat.shiftRight s1 6) λs2=>
  cond (Nat.beq l0 63)
   (forceN (Nat.land s2 cMask) λlen=>forceN (Nat.shiftRight s2 cBits) λs3=>
    readTreeRangesGo nextTopo start endIdx cBits cMask n s3 (scanTopoRange nextTopo start endIdx lo len acc))
   (readTreeRangesGo nextTopo start endIdx cBits cMask n s2 (scanTopoRange nextTopo start endIdx lo l0 acc))
noncomputable def readBatchTreeRanges(nextTopo:LevelTopo)(start endIdx cBits s:Nat):List (Nat×Nat)×Nat:=
 let nrng:=Nat.land s 7
 forceN (Nat.sub (Nat.shiftLeft 1 cBits) 1) λcMask=>
 forceN (Nat.shiftRight s 3) λs0=>
 readTreeRangesGo nextTopo start endIdx cBits cMask nrng s0 []
private lemma readBatchTreeRanges_sound (nextTopo:LevelTopo) (start endIdx cBits s:Nat) :
  ∀pm∈(readBatchTreeRanges nextTopo start endIdx cBits s).1,
   ∃cIdx < nextTopo.1,unpackTopo nextTopo cIdx=pm:=by
 let P (pm:Nat×Nat):=∃c < nextTopo.1,unpackTopo nextTopo c=pm
 have hscan:∀ci len acc,(∀pm∈acc,P pm)->∀pm∈scanTopoRange nextTopo start endIdx ci len acc,P pm:=λci len=>by
  induction len generalizing ci with| zero=>exact λ_ h=>h| succ _ ih=>
   intro acc hacc pm hpm;simp only[scanTopoRange,forceN_eq]at hpm
   cases hlt:Nat.ble (Nat.add ci 1) nextTopo.1
   ·rw[hlt,Bool.cond_false]at hpm;exact ih _ acc hacc pm hpm
   ·rw[hlt,Bool.cond_true]at hpm
    refine ih _ _ (λpm' hpm'=> ?_) pm hpm
    cases hrng:and (Nat.ble start (unpackTopo nextTopo ci).1) (Nat.ble (Nat.add (unpackTopo nextTopo ci).1 1) endIdx)
    ·rw[hrng,Bool.cond_false]at hpm';exact hacc pm' hpm'
    ·rw[hrng,Bool.cond_true]at hpm'
     exact(List.mem_cons.mp hpm').elim (λe=>e▸⟨ci,Nat.ble_eq.mp hlt,Prod.mk.eta.symm⟩) (hacc pm')
 have hgo:∀n s0 acc,(∀pm∈acc,P pm)->∀pm∈(readTreeRangesGo nextTopo start endIdx cBits (Nat.sub (Nat.shiftLeft 1 cBits) 1) n s0 acc).1,P pm:=λn=>by
  induction n with| zero=>exact λ_ _ h=>h| succ _ ih=>
   intro s0 acc hacc pm hpm;simp only[readTreeRangesGo,forceN_eq]at hpm
   cases h63:Nat.beq (Nat.land (Nat.shiftRight s0 cBits) 63) 63 <;>
    [rw[h63,Bool.cond_false]at hpm;rw[h63,Bool.cond_true]at hpm]<;>exact ih _ _ (hscan _ _ acc hacc) pm hpm
 simpa only[readBatchTreeRanges,forceN_eq]using hgo _ _ [] (λ_ h=>by simp at h)
def filterLaneMoves(idx:Nat):List (Nat×Nat)->List Nat
 | []=>[]
 | (p,m)::rest=>cond (Nat.beq p idx) (m::filterLaneMoves idx rest) (filterLaneMoves idx rest)
private lemma filterLaneMoves_mem {idx m:Nat} {es:List (Nat×Nat)} (h:m∈filterLaneMoves idx es):(idx,m)∈es:=by
 induction es with
 | nil=>simp[filterLaneMoves]at h
 | cons p rest ih=>
  rcases p with ⟨p1,p2⟩;simp only[filterLaneMoves]at h
  cases he:Nat.beq p1 idx
  ·rw[he,Bool.cond_false]at h;exact List.mem_cons_of_mem _ (ih h)
  ·rw[he,Bool.cond_true]at h;rcases List.mem_cons.mp h with rfl|ht
   ·rw[Nat.eq_of_beq_eq_true he];exact List.mem_cons_self ..
   ·exact List.mem_cons_of_mem _ (ih ht)
noncomputable def readHintsGo(colBits d fullMask colMask:Nat):Nat->Nat->List (Nat×Nat)->List (Nat×Nat)×Nat
 | 0,s,acc=>(acc,s)
 | n+1,s,acc=>
  forceN (Nat.land s colMask) λci=>
  forceN (Nat.shiftRight s colBits) λs1=>
  let tag0:=Nat.land s1 1;let s2:=Nat.shiftRight s1 1
  cond (Nat.beq tag0 0)
   (forceN s2 λs2'=>readHintsGo colBits d fullMask colMask n s2' ((ci,fullMask)::acc))
   (let tag1:=Nat.land s2 1
    forceN (Nat.shiftRight s2 1) λs2'=>
    cond (Nat.beq tag1 0)
     (readHintsGo colBits d fullMask colMask n s2' ((ci,0)::acc))
     (forceN (Nat.land s2' fullMask) λpm=>forceN (Nat.shiftRight s2' d) λs3=>
      readHintsGo colBits d fullMask colMask n s3 ((ci,pm)::acc)))
noncomputable def readDeadReqsGo:Nat->Nat->List (Nat×Nat×Nat×Nat)->List (Nat×Nat×Nat×Nat)×Nat
 | 0,s,acc=>(acc,s)
 | n+1,s,acc=>
  forceN (Nat.land s 15) λu=>forceN (Nat.land (Nat.shiftRight s 4) 15) λv=>
  forceN (Nat.land (Nat.shiftRight s 8) 15) λw=>forceN (Nat.land (Nat.shiftRight s 12) 15) λt=>
  forceN (Nat.shiftRight s 16) λs'=>readDeadReqsGo n s' ((u,v,w,t)::acc)
noncomputable def readOptDeadReqs(s:Nat):List (Nat×Nat×Nat×Nat)×Nat:=
 let hasD:=Nat.beq (Nat.land s 1) 1
 forceN (Nat.shiftRight s 1) λs1=>
 cond hasD
  (let n0:=Nat.land s1 15;forceN (Nat.shiftRight s1 4) λs2=>
   cond (Nat.beq n0 15)
    (forceN (Nat.shiftRight s2 8) λs3=>readDeadReqsGo (Nat.land s2 255) s3 [])
    (readDeadReqsGo n0 s2 []))
  ([],s1)
noncomputable def readDedupGo(cBits aBits cMask aMask:Nat):Nat->Nat->List (Nat×Nat)->List (Nat×Nat)×Nat
 | 0,s,acc=>(acc,s)
 | n+1,s,acc=>
  forceN (Nat.land s cMask) λcIdx=>
  forceN (Nat.shiftRight s cBits) λs1=>
  let isId:=Nat.beq (Nat.land s1 1) 1
  forceN (Nat.shiftRight s1 1) λs2=>
  cond isId
   (readDedupGo cBits aBits cMask aMask n s2 ((cIdx,0)::acc))
   (forceN (Nat.land s2 aMask) λaIdx=>forceN (Nat.shiftRight s2 aBits) λs3=>
    readDedupGo cBits aBits cMask aMask n s3 ((cIdx,aIdx)::acc))
noncomputable def readOptDedupLinks(cBits aBits cMask aMask s:Nat):List (Nat×Nat)×Nat:=
 let hasL:=Nat.beq (Nat.land s 1) 1
 forceN (Nat.shiftRight s 1) λs1=>
 cond hasL
  (let n0:=Nat.land s1 15;forceN (Nat.shiftRight s1 4) λs2=>
   cond (Nat.beq n0 15)
    (forceN (Nat.shiftRight s2 8) λs3=>readDedupGo cBits aBits cMask aMask (Nat.land s2 255) s3 [])
    (readDedupGo cBits aBits cMask aMask n0 s2 []))
  ([],s1)
abbrev NodeRecV5:=
 Nat×List (Nat×Nat×Nat)×Nat×Bool×Bool×Nat×List (Nat×Nat)×List (Nat×Nat×Nat×Nat)×List (Nat×Nat)
noncomputable def readOneNonLeaf {β:Type} (levels:Array LevelTopo) (nv d idx colBits cBits aBits s:Nat)
  (k:NodeRecV5->Nat->β):β:=
 match decodeNode levels nv d idx with
 | (gates,liveM)=>
  forceN liveM λliveM'=>
  forceB (Nat.beq (Nat.land s 1) 1) λneedP=>
  forceN (Nat.land (Nat.shiftRight s 1) 3) λtier=>
  forceB (Nat.beq (Nat.land (Nat.shiftRight s 3) 1) 1) λhasH=>
  forceN (Nat.shiftRight s 4) λs1=>
  forceN (Nat.sub (Nat.shiftLeft 1 d) 1) λfullMask=>
  forceN (Nat.sub (Nat.shiftLeft 1 colBits) 1) λcolMask=>
  match cond hasH
   (let nh0:=Nat.land s1 31;forceN (Nat.shiftRight s1 5) λs1'=>
    cond (Nat.beq nh0 31)
      (forceN (Nat.shiftRight s1' 8) λs1''=>readHintsGo colBits d fullMask colMask (Nat.land s1' 255) s1'' [])
      (readHintsGo colBits d fullMask colMask nh0 s1' []))
   ([],s1)with
  | (hsExp,s2)=>
   forceN s2 λs2'=>
   match cond needP
     (forceB (Nat.beq (Nat.land s2' 1) 1) λnlv=>
      match readOptDeadReqs (Nat.shiftRight s2' 1)with| (dr,s2'')=>(nlv,dr,s2''))
     (false,[],s2')with
   | (needLive,dReqs,s3)=>
     forceN s3 λs3'=>
     forceN (Nat.sub (Nat.shiftLeft 1 cBits) 1) λcMask=>
     forceN (Nat.sub (Nat.shiftLeft 1 aBits) 1) λaMask=>
     match readOptDedupLinks cBits aBits cMask aMask s3' with
     | (dlinks,s4)=>forceN s4 λs4'=>k (idx,gates,liveM',needP,needLive,tier,hsExp,dReqs,dlinks) s4'
private lemma readOneNonLeaf_spec {β:Type} (levels:Array LevelTopo) (nv d idx colBits cBits aBits s:Nat)
  (k:NodeRecV5->Nat->β) :
  ∃nd s',readOneNonLeaf levels nv d idx colBits cBits aBits s k=k nd s' /\
   nd.1=idx/\(nd.2.1,nd.2.2.1)=decodeNode levels nv d idx:=by
 unfold readOneNonLeaf;simp only[forceN_eq,forceB_eq]
 exact⟨_,_,rfl,rfl,Prod.mk.eta.symm⟩
noncomputable def readNonLeafBatch(levels:Array LevelTopo)(nv d start colBits cBits aBits:Nat):
  Nat->Nat->List NodeRecV5
 | 0,_=>[]
 | cnt+1,s=>
  readOneNonLeaf levels nv d start colBits cBits aBits s λnd s'=>
  nd::readNonLeafBatch levels nv d (Nat.add start 1) colBits cBits aBits cnt s'
private lemma readNonLeafBatch_spec (levels:Array LevelTopo) (nv d start colBits cBits aBits cnt s:Nat) :
  let l:=readNonLeafBatch levels nv d start colBits cBits aBits cnt s
  ∃hlen:l.length=cnt,∀q (hq:q<cnt),
   let nd:=l[q]'(hlen▸hq)
   nd.1=start+q/\(nd.2.1,nd.2.2.1)=decodeNode levels nv d (start+q):=by
 induction cnt generalizing start s with
 | zero=>exact⟨rfl,λ_ h=>by omega⟩
 | succ cnt ih=>
  obtain⟨nd0,s',heq,h1,h2⟩:=readOneNonLeaf_spec levels nv d start colBits cBits aBits s
   (λnd s'=>nd::readNonLeafBatch levels nv d (Nat.add start 1) colBits cBits aBits cnt s')
  obtain⟨hl,hg⟩:=ih (start+1) s'
  refine⟨by simp[readNonLeafBatch,heq,hl],λq hq=> ?_⟩
  cases q with
  | zero=>simpa[readNonLeafBatch,heq]using ⟨h1,h2⟩
  | succ q'=>simpa[readNonLeafBatch,heq,Nat.add_eq,show start+1+q'=start+(q'+1) by omega]using hg q' (by omega)
abbrev LeafRecV5:=Nat×List (Nat×Nat×Nat)×Nat×Bool×List (Nat×Nat×Nat×Nat)
noncomputable def readLeafAllLive(levels:Array LevelTopo)(nv d start:Nat):Nat->List LeafRecV5
 | 0=>[]
 | cnt+1=>
  match decodeNode levels nv d start with
  | (gates,liveM)=>forceN liveM λliveM'=>(start,gates,liveM',true,[])::readLeafAllLive levels nv d (Nat.add start 1) cnt
noncomputable def readLeafGo(levels:Array LevelTopo)(nv d start:Nat):Nat->Nat->List LeafRecV5
 | 0,_=>[]
 | cnt+1,s=>
  match decodeNode levels nv d start with
  | (gates,liveM)=>
   forceN liveM λliveM'=>
   forceB (Nat.beq (Nat.land s 1) 1) λnlv=>
   match readOptDeadReqs (Nat.shiftRight s 1)with
   | (dr,s')=>forceN s' λs''=>(start,gates,liveM',nlv,dr)::readLeafGo levels nv d (Nat.add start 1) cnt s''
noncomputable def readLeafBatch(levels:Array LevelTopo)(nv d start cnt s:Nat):List LeafRecV5:=
 cond (Nat.beq (Nat.land s 1) 1) (readLeafAllLive levels nv d start cnt)
  (forceN (Nat.shiftRight s 1) λs0=>readLeafGo levels nv d start cnt s0)
private lemma readLeafBatch_spec (levels:Array LevelTopo) (nv d start cnt s:Nat) :
  let l:=readLeafBatch levels nv d start cnt s
  ∃hlen:l.length=cnt,∀q (hq:q<cnt),
   let nd:=l[q]'(hlen▸hq);(nd.2.1,nd.2.2.1)=decodeNode levels nv d (start+q):=by
 have go1 c st:let l:=readLeafAllLive levels nv d st c;∃h:l.length=c,∀q (hq:q<c),
   let nd:=l[q]'(h▸hq);(nd.2.1,nd.2.2.1)=decodeNode levels nv d (st+q):=by
  induction c generalizing st with
  | zero=>exact⟨rfl,λ_ h=>by omega⟩
  | succ c ih=>
   obtain⟨h,hi⟩:=ih (st+1)
   refine⟨by simp[readLeafAllLive,forceN_eq,Nat.add_eq,h],λq hq=> ?_⟩
   cases q with
   | zero=>simp[readLeafAllLive,forceN_eq]
   | succ q'=>simpa[readLeafAllLive,forceN_eq,Nat.add_eq,show st+1+q'=st+(q'+1) by omega]using hi q' (by omega)
 have go2 c st s0:let l:=readLeafGo levels nv d st c s0;∃h:l.length=c,∀q (hq:q<c),
   let nd:=l[q]'(h▸hq);(nd.2.1,nd.2.2.1)=decodeNode levels nv d (st+q):=by
  induction c generalizing st s0 with
  | zero=>exact⟨rfl,λ_ h=>by omega⟩
  | succ c ih=>
   obtain⟨h,hi⟩:=ih (st+1) (readOptDeadReqs (Nat.shiftRight s0 1)).2
   refine⟨by simpa[readLeafGo,forceN_eq,forceB_eq,Nat.add_eq]using h,λq hq=> ?_⟩
   cases q with
   | zero=>simp[readLeafGo,forceN_eq,forceB_eq]
   | succ q'=>simpa[readLeafGo,forceN_eq,forceB_eq,Nat.add_eq,show st+1+q'=st+(q'+1) by omega]using hi q' (by omega)
 unfold readLeafBatch;cases Nat.beq (Nat.land s 1) 1
 ·simp[forceN_eq];exact go2 cnt start _
 ·exact go1 cnt start
def lanePlace(W v upper:Nat):Nat:=Nat.lor (Nat.shiftLeft upper (Nat.add W 1)) v
noncomputable def combineLanes(W:Nat){α:Type}(f:α->Nat):List α->Nat
 | []=>0
 | x::xs=>lanePlace W (f x) (combineLanes W f xs)
def unitsW(W:Nat):Nat->Nat
 | 0=>0
 | n+1=>lanePlace W 1 (unitsW W n)
def fullMarksW(W r packed:Nat):Nat:=Nat.land (Nat.shiftRight (Nat.add packed r) W) r
def extractMaskFuel(stride:Nat):Nat->Nat->Nat->Nat->Nat
 | 0,_,_,acc=>acc
 | n+1,m,bit,acc=>
  let acc':=cond (Nat.beq (Nat.land m 1) 0) acc (Nat.lor acc bit)
  extractMaskFuel stride n (Nat.shiftRight m stride) (Nat.add bit bit) acc'
noncomputable def covOfColsF{β:Type}(allW:Nat):
  List Nat->Nat->Nat->Nat->(Nat×Nat×Nat->β)->β
 | [],c1,c2,c3,k=>k (c1,c2,c3)
 | z::zs,c1,c2,c3,k=>
  forceN (Nat.xor allW z) λnz=>
  forceN (Nat.lor z c1) λnc1=>
  forceN (Nat.lor (Nat.land z (Nat.xor allW c1)) (Nat.land c2 nz)) λnc2=>
  forceN (Nat.lor (Nat.land z c2) (Nat.land c3 nz)) λnc3=>
  covOfColsF allW zs nc1 nc2 nc3 k
def covOfColsVal(allW:Nat):List Nat->Nat->Nat->Nat->Nat×Nat×Nat
 | [],c1,c2,c3=>(c1,c2,c3)
 | z::zs,c1,c2,c3=>
  let nz:=Nat.xor allW z
  covOfColsVal allW zs (Nat.lor z c1)
   (Nat.lor (Nat.land z (Nat.xor allW c1)) (Nat.land c2 nz))
   (Nat.lor (Nat.land z c2) (Nat.land c3 nz))
def takeOnePacked(c1 c2 colA:Nat):Nat:=Nat.xor c1 (Nat.land (Nat.land c1 c2) colA)
def takeTwoPacked(c1 c2 c3 colA colB:Nat):Nat:=
 Nat.xor c1 (Nat.land c1 (Nat.lor (Nat.land c2 (Nat.lor colA colB)) (Nat.land (Nat.land c3 colA) colB)))
noncomputable def decodeSampleFwd{β:Type}:
  List (Nat×Nat×Nat)->List (Nat×Nat)->(List (Nat×Nat)->β)->β
 | [],bank,k=>k bank
 | (op,a,b)::rest,bank,k=>
  let pa:=bank.getD a (0,0);let pb:=bank.getD b (0,0)
  forceN (zN op pa.1 pb.1) λz1=>forceN (zN op pa.2 pb.2) λz2=>
  decodeSampleFwd rest (bank++[(z1,z2)]) k
def decodeSampleVal:List (Nat×Nat×Nat)->List (Nat×Nat)->List (Nat×Nat)
 | [],bank=>bank
 | (op,a,b)::rest,bank=>
  let pa:=bank.getD a (0,0);let pb:=bank.getD b (0,0)
  decodeSampleVal rest (bank++[(zN op pa.1 pb.1,zN op pa.2 pb.2)])
private lemma decodeSampleFwd_eq {β:Type} (gs:List (Nat×Nat×Nat)) (bank:List (Nat×Nat)) (k:List (Nat×Nat)->β) :
  decodeSampleFwd gs bank k=k (decodeSampleVal gs bank):=by
 induction gs generalizing bank with| nil=>rfl| cons g rest ih=>rcases g with ⟨op,a,b⟩;simp[decodeSampleFwd,decodeSampleVal,forceN_eq];exact ih _
private lemma covOfColsF_eq {β:Type} (allW:Nat) (zs:List Nat) (c1 c2 c3:Nat) (k:Nat×Nat×Nat->β) :
  covOfColsF allW zs c1 c2 c3 k=k (covOfColsVal allW zs c1 c2 c3):=by
 induction zs generalizing c1 c2 c3 with| nil=>rfl| cons z zs ih=>simp[covOfColsF,covOfColsVal,forceN_eq];exact ih _ _ _
private lemma combineLanes_tb {W:Nat} {α:Type} (f:α->Nat) (xs:List α)
  (hf:∀x∈xs,f x<2^W) (k:Nat) :
  (combineLanes W f xs).testBit k =
   if h:k / (W+1)<xs.length then
    if k % (W+1)<W then(f (xs[k / (W+1)])).testBit (k % (W+1))else false
   else false:=by
 induction xs generalizing k with
 | nil=>simp[combineLanes]
 | cons x xs ih=>
  have hfx:f x<2^W:=hf x (by simp)
  have hf':∀y∈xs,f y<2^W:=λy hy=>hf y (by simp[hy])
  simp only[combineLanes,lanePlace,Nat.lor_eq,Nat.testBit_or,tb_shl,Nat.add_eq]
  by_cases hlt:k<W+1
  ·have hdiv:k / (W+1)=0:=Nat.div_eq_of_lt hlt
   have hmod:k % (W+1)=k:=Nat.mod_eq_of_lt hlt
   simp only[show ¬W+1<=k by omega,decide_false,Bool.false_and,Bool.false_or,hdiv,hmod,List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
   by_cases hk:k<W
   ·simp[hk]
   ·simp[hk,testBit_eq_false_of_lt_pow hfx (Nat.le_of_not_lt hk)]
  ·have hge:W+1<=k:=Nat.le_of_not_lt hlt
   have h0:(f x).testBit k=false:=testBit_eq_false_of_lt_pow hfx (by omega)
   have hdiv:k / (W+1)=(k-(W+1)) / (W+1)+1:=by
    conv_lhs=>rw[<-Nat.sub_add_cancel hge];exact Nat.add_div_right _ (by omega)
   have hmod:k % (W+1)=(k-(W+1)) % (W+1):=by
    conv_lhs=>rw[<-Nat.sub_add_cancel hge];exact Nat.add_mod_right _ _
   simp only[hge,decide_true,Bool.true_and,h0,Bool.or_false,ih hf' (k-(W+1)),hdiv,hmod,List.length_cons]
   split_ifs with h1 h2 h3<;>first| rfl| omega
private lemma combineLanes_bin {W:Nat} {α:Type} {f g:α->Nat} {xs:List α}
  (hf:∀x∈xs,f x<2^W) (hg:∀x∈xs,g x<2^W)
  (op:Nat->Nat->Nat) (bop:Bool->Bool->Bool) (hb0:bop false false=false)
  (hop:∀a b k,(op a b).testBit k=bop (a.testBit k) (b.testBit k)) :
  op (combineLanes W f xs) (combineLanes W g xs)=combineLanes W (λx=>op (f x) (g x)) xs:=by
 have hfg:∀x∈xs,op (f x) (g x)<2^W:=λx hx=>
  lt_two_pow_of_testBit λk hk=>by rw[hop,testBit_eq_false_of_lt_pow (hf x hx) hk,testBit_eq_false_of_lt_pow (hg x hx) hk,hb0]
 apply Nat.eq_of_testBit_eq;intro k
 rw[hop,combineLanes_tb f xs hf k,combineLanes_tb g xs hg k,combineLanes_tb _ xs hfg k]
 split_ifs<;>simp[hop,hb0]
private lemma fullMarksW_lane_tb {W:Nat} (hW:0<W) {α:Type} (f:α->Nat) (xs:List α)
  (hf:∀x∈xs,f x<2^W) (q:Nat) (hq:q<xs.length) :
  (fullMarksW W (unitsW W xs.length) (combineLanes W f xs)).testBit (q*(W+1))=decide (f (xs[q]'hq)=2^W-1):=by
 have h1lt:1<2^W:=by have:=Nat.pow_le_pow_right (by decide:1<=2) hW;omega
 have hsum:∀l:List α,(∀x∈l,f x<2^W) ->
   Nat.add (combineLanes W f l) (unitsW W l.length) =
    combineLanes W (λx=>Nat.land (f x+1) (2^W-1)) l|||(combineLanes W (λx=>if f x=2^W-1 then 1 else 0) l<<<W):=λl=>by
  induction l with| nil=>exact λ_=>by simp[combineLanes,unitsW]| cons x xs ih=>
   intro hl;have hfx:=hl x (by simp);have hfx1:f x+1<2^(W+1):=by rw[Nat.pow_succ];omega
   have hlp p a (hp:p<2^(W+1)):lanePlace W p a=a*2^(W+1)+p:=by
    rw[lanePlace,Nat.lor_eq,<-add_eq_lor (Nat.eq_of_testBit_eq λk=>by rw[Nat.testBit_and,tb_shl,Nat.zero_testBit];by_cases hk:W+1<=k<;>simp[hk,testBit_eq_false_of_lt_pow hp]),shl_eq]
   simp only[List.length_cons,combineLanes,unitsW]
   rw[show Nat.add (lanePlace W (f x) (combineLanes W f xs)) (lanePlace W 1 (unitsW W xs.length))=lanePlace W (f x+1) (Nat.add (combineLanes W f xs) (unitsW W xs.length)) by
    change lanePlace W (f x) _+lanePlace W 1 _=lanePlace W (f x+1) (_+_);rw[hlp _ _ (by rw[Nat.pow_succ];omega),hlp _ _ (by rw[Nat.pow_succ];omega),hlp _ _ hfx1];ring,
    ih λy hy=>hl y (by simp[hy])]
   apply Nat.eq_of_testBit_eq;intro k;simp only[lanePlace,Nat.lor_eq,Nat.testBit_or,tb_shl,Nat.testBit_shiftLeft,Nat.add_eq]
   by_cases hlt:k<W+1
   ·simp only[show ¬W+1<=k by omega,decide_false,Bool.false_and,Bool.false_or]
    by_cases hkw:k<W;· simp[show ¬W<=k by omega,Nat.land_eq,hkw]
    rw[show k=W by omega];simp only[Nat.le_refl,decide_true,Bool.true_and,Nat.sub_self,Nat.land_eq,Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.lt_irrefl,decide_false,Bool.and_false,Bool.false_or]
    by_cases hfull:f x=2^W-1;· rw[hfull,Nat.sub_add_cancel (Nat.two_pow_pos W),Nat.testBit_two_pow_self];simp
    ·simp[hfull,testBit_eq_false_of_lt_pow (show f x+1<2^W by omega) (Nat.le_refl W)]
   ·have h0c:(if f x=2^W-1 then 1 else 0).testBit (k-W)=false:=by split_ifs<;>[exact Bool.eq_false_iff.mpr (by simp[Nat.testBit_one_eq_true_iff_self_eq_zero,show k-W≠0 by omega]);simp]
    simp[show W+1<=k by omega,show W<=k by omega,testBit_eq_false_of_lt_pow hfx1 (show W+1<=k by omega),h0c,
     show(W<=k-(W+1))↔(W+1<=k-W) by omega,show k-(W+1)-W=k-W-(W+1) by omega]
 have hu_eq:unitsW W xs.length=combineLanes W (λ_=>1) xs:=by clear hq hf;induction xs with| nil=>rfl| cons _ _ ih=>simp[unitsW,combineLanes,ih]
 unfold fullMarksW;rw[Nat.land_eq,Nat.testBit_and,tb_shr,hsum xs hf,Nat.testBit_or,Nat.testBit_shiftLeft,hu_eq,
  combineLanes_tb (λ_=>1) xs (λ_ _=>h1lt),combineLanes_tb _ xs (λ_ _=>lt_two_pow_of_testBit λt ht=>by rw[Nat.land_eq,Nat.testBit_and,Nat.testBit_two_pow_sub_one,decide_eq_false (by omega),Bool.and_false]),
  combineLanes_tb _ xs (λ_ _=>by split_ifs<;>[exact h1lt;exact Nat.two_pow_pos W]),
  show(W+q*(W+1)) / (W+1)=q by rw[Nat.add_comm,Nat.mul_comm q];exact(Nat.mul_add_div (by omega) q W).trans (by rw[Nat.div_eq_of_lt (by omega),Nat.add_zero]),
  show(W+q*(W+1)) % (W+1)=W by rw[Nat.add_comm,Nat.mul_comm q,Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega)],
  show W+q*(W+1)-W=q*(W+1) by omega,Nat.mul_div_cancel q (by omega),Nat.mul_mod_left q (W+1)]
 simp[hq,hW,show W<=W+q*(W+1) by omega];split_ifs with h<;>simp[h]
private lemma extractMaskFuel_tb (stride n m bit acc k:Nat) (hacc:∀j≥k,acc.testBit j=false)
  (q:Nat) (hq:q<n) :
  (extractMaskFuel stride n m (2^k) acc).testBit (k+q)=m.testBit (q*stride):=by
 have hpow t:Nat.add (2^t) (2^t)=2^(t+1):=by change 2^t+2^t=_;rw[Nat.pow_succ];omega
 induction n generalizing m acc k q with
 | zero=>omega
 | succ n ih=>
  simp only[extractMaskFuel,hpow]
  have hb0:Nat.beq (Nat.land m 1) 0 = !m.testBit 0:=by rw[show Nat.land m 1=m % 2 from Nat.and_one_is_mod m,Nat.testBit_zero];rcases(show m % 2=0\/m % 2=1 by omega)with h|h<;>[simp[h];(simp[h];rfl)]
  rw[hb0];cases q with
  | zero=>
   have hgo:∀r m' a' t,k<t->(extractMaskFuel stride r m' (2^t) a').testBit k=a'.testBit k:=λr=>by
    induction r with| zero=>intros;rfl| succ _ ihr=>intro m' a' t hkt;simp only[extractMaskFuel,hpow];rw[ihr _ _ (t+1) (by omega)];cases Nat.beq (Nat.land m' 1) 0<;>simp[Nat.lor_eq,Nat.testBit_or,show t≠k by omega]
   simp only[Nat.add_zero,Nat.zero_mul];rw[hgo n _ _ (k+1) (by omega)]
   cases m.testBit 0<;>simp[hacc k (Nat.le_refl _),Nat.lor_eq,Nat.testBit_or]
  | succ q'=>
   rw[show k+(q'+1)=(k+1)+q' by omega,ih _ _ (k+1) (λj hj=>by cases m.testBit 0<;>simp[hacc j (by omega),Nat.lor_eq,Nat.testBit_or,show k≠j by omega]) q' (by omega),tb_shr];congr 1;ring
private def countBitAt (t:Nat):List Nat->Nat
 | []=>0
 | z::zs=>(if z.testBit t then 1 else 0)+countBitAt t zs
private lemma covOfColsVal_spec {W:Nat} (zs:List Nat) (hz:∀z∈zs,z<2^W) :
  let r:=covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) zs 0 0 0
  r.1<2^W/\r.2.1<2^W/\r.2.2<2^W /\
  ∀t < W,r.1.testBit t=decide (1<=countBitAt t zs) /\
       r.2.1.testBit t=decide (countBitAt t zs=1) /\
       r.2.2.testBit t=decide (countBitAt t zs=2):=by
 set allW:=Nat.sub (Nat.shiftLeft 1 W) 1
 have hallW t:allW.testBit t=decide (t<W):=by dsimp only[allW];rw[Nat.sub_eq,shl_one,Nat.testBit_two_pow_sub_one]
 have hltA:allW<2^W:=by dsimp only[allW];rw[Nat.sub_eq,shl_one];exact Nat.sub_lt (Nat.two_pow_pos W) (by decide)
 have hgo:∀(l:List Nat) c1 c2 c3,(∀z∈l,z<2^W)->c1<2^W->c2<2^W->c3<2^W ->
   ∀(cnt:Nat->Nat),
    (∀t < W,c1.testBit t=decide (1<=cnt t)/\c2.testBit t=decide (cnt t=1)/\c3.testBit t=decide (cnt t=2)) ->
   let r:=covOfColsVal allW l c1 c2 c3
   r.1<2^W/\r.2.1<2^W/\r.2.2<2^W /\
   ∀t < W,r.1.testBit t=decide (1<=cnt t+countBitAt t l) /\
         r.2.1.testBit t=decide (cnt t+countBitAt t l=1) /\
         r.2.2.testBit t=decide (cnt t+countBitAt t l=2):=λl=>by
  induction l with
  | nil=>intro _ _ _ _ h1 h2 h3 _ hc;simp[covOfColsVal,countBitAt];exact⟨h1,h2,h3,hc⟩
  | cons z zs ih=>
   intro c1 c2 c3 hzl h1 h2 h3 cnt hc;have hzb:=hzl z (by simp);dsimp only[covOfColsVal]
   have hres:=ih (Nat.lor z c1) (Nat.lor (Nat.land z (Nat.xor allW c1)) (Nat.land c2 (Nat.xor allW z))) (Nat.lor (Nat.land z c2) (Nat.land c3 (Nat.xor allW z))) (λy hy=>hzl y (by simp[hy])) (Nat.or_lt_two_pow hzb h1)
    (Nat.or_lt_two_pow (Nat.and_lt_two_pow _ (Nat.xor_lt_two_pow hltA h1)) (Nat.and_lt_two_pow _ (Nat.xor_lt_two_pow hltA hzb)))
    (Nat.or_lt_two_pow (Nat.and_lt_two_pow _ h2) (Nat.and_lt_two_pow _ (Nat.xor_lt_two_pow hltA hzb)))
    (λt=>cnt t+if z.testBit t then 1 else 0) λt ht=>by
     obtain⟨a,b,c⟩:=hc t ht
     simp only[Nat.lor_eq,Nat.land_eq,Nat.xor_eq,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,hallW t,decide_eq_true ht,a,b,c]
     cases z.testBit t;· simp
     ·rcases(show cnt t=0\/cnt t=1\/cnt t>=2 by omega)with h|h|h <;>
        simp[h,show ∀k,k>=2->1<=k/\k≠0/\k≠1/\k+1≠2/\1<=k+1 by intro k hk;omega]
   exact⟨hres.1,hres.2.1,hres.2.2.1,λt ht=>by rw[countBitAt,<-Nat.add_assoc];exact hres.2.2.2 t ht⟩
 simpa using hgo zs 0 0 0 hz (Nat.two_pow_pos W) (Nat.two_pow_pos W) (Nat.two_pow_pos W) (λ_=>0) (λ_ _=>⟨by simp,by simp,by simp⟩)
private lemma countBitAt_dropAt (t k:Nat) (l:List Nat) (hk:k<l.length) :
  countBitAt t (dropAt k l)+(if(l.getD k 0).testBit t then 1 else 0)=countBitAt t l:=by
 induction l generalizing k with
 | nil=>simp at hk
 | cons _ xs ih=>cases k with| zero=>simp[dropAt,countBitAt];omega| succ k'=>simp only[dropAt,countBitAt,List.getD_cons_succ];have:=ih k' (by simp at hk;exact hk);omega
private lemma takeOne_tb {W:Nat} {zs:List Nat} (hz:∀z∈zs,z<2^W) {i:Nat} (hi:i<zs.length) (t:Nat) (ht:t<W) :
  (takeOnePacked (covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) zs 0 0 0).1
   (covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) zs 0 0 0).2.1 (zs.getD i 0)).testBit t =
   decide (1<=countBitAt t (dropAt i zs)):=by
 have hc:=(covOfColsVal_spec zs hz).2.2.2 t ht;have hd:=countBitAt_dropAt t i zs hi
 simp only[takeOnePacked,Nat.xor_eq,Nat.land_eq,Nat.testBit_xor,Nat.testBit_and,hc.1,hc.2.1]
 cases ha:(zs.getD i 0).testBit t<;>rw[ha]at hd<;>simp at hd
 ·rw[hd];simp
 ·rcases(show countBitAt t (dropAt i zs)=0\/1<=countBitAt t (dropAt i zs) by omega)with h0|h1
  ·rw[<-hd,h0];simp
  ·simp[h1,show 1<=countBitAt t zs by omega,show countBitAt t zs≠1 by omega]
private lemma takeTwo_tb {W:Nat} {zs:List Nat} (hz:∀z∈zs,z<2^W) {i j:Nat} (hij:i<j) (hj:j<zs.length) (t:Nat) (ht:t<W) :
  (takeTwoPacked (covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) zs 0 0 0).1
   (covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) zs 0 0 0).2.1
   (covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) zs 0 0 0).2.2 (zs.getD i 0) (zs.getD j 0)).testBit t =
   decide (1<=countBitAt t (dropAt (j-1) (dropAt i zs))):=by
 have hc:=(covOfColsVal_spec zs hz).2.2.2 t ht
 have hi:i<zs.length:=lt_trans hij hj
 have hd1:=countBitAt_dropAt t i zs hi
 have hd2:=countBitAt_dropAt t (j-1) (dropAt i zs) (by rw[dropAt_len zs i hi];omega)
 rw[dropAt_getD zs i j hij]at hd2
 have htot:countBitAt t (dropAt (j-1) (dropAt i zs))+(if(zs.getD i 0).testBit t then 1 else 0)+(if(zs.getD j 0).testBit t then 1 else 0)=countBitAt t zs:=by omega
 simp only[takeTwoPacked,Nat.xor_eq,Nat.land_eq,Nat.lor_eq,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_or,hc.1,hc.2.1,hc.2.2]
 set r:=countBitAt t (dropAt (j-1) (dropAt i zs))
 cases ha:(zs.getD i 0).testBit t<;>cases hb:(zs.getD j 0).testBit t<;>(rw[ha,hb]at htot;simp at htot)
 ·rw[htot];simp
 ·rcases(show r=0\/1<=r by omega)with h0|h1
  ·rw[<-htot,h0];simp
  ·simp[h1,show 1<=countBitAt t zs by omega,show countBitAt t zs≠1 by omega]
 ·rcases(show r=0\/1<=r by omega)with h0|h1
  ·rw[<-htot,h0];simp
  ·simp[h1,show 1<=countBitAt t zs by omega,show countBitAt t zs≠1 by omega]
 ·rcases(show r=0\/1<=r by omega)with h0|h1
  ·rw[<-htot,h0];simp
  ·simp[h1,show 1<=countBitAt t zs by omega,show countBitAt t zs≠1 by omega,show countBitAt t zs≠2 by omega]
noncomputable def forceSurvList{β:Type}:List (Nat×Nat)->(List (Nat×Nat)->β)->β
 | [],k=>k []
 | (mc,lm)::rest,k=>forceN mc λmc'=>forceN lm λlm'=>forceSurvList rest λr=>k ((mc',lm')::r)
private lemma forceSurvList_eq {β:Type} (l:List (Nat×Nat)) (k:List (Nat×Nat)->β):forceSurvList l k=k l:=by
 induction l generalizing k with| nil=>rfl| cons p _ ih=>rcases p with ⟨a,b⟩;simp[forceSurvList,forceN_eq];exact ih _
noncomputable def forceNatL{β:Type}:List Nat->(List Nat->β)->β
 | [],k=>k []
 | x::rest,k=>forceN x λx'=>forceNatL rest λr=>k (x'::r)
private lemma forceNatL_eq {β:Type} (l:List Nat) (k:List Nat->β):forceNatL l k=k l:=by
 induction l generalizing k with| nil=>rfl| cons _ _ ih=>simp[forceNatL,forceN_eq];exact ih _
noncomputable def forceReqs{β:Type}:List (Nat×Nat×Nat)->(List (Nat×Nat×Nat)->β)->β
 | [],k=>k []
 | (a,b,c)::rest,k=>forceN a λa'=>forceN b λb'=>forceN c λc'=>forceReqs rest λr=>k ((a',b',c')::r)
private lemma forceReqs_eq {β:Type} (l:List (Nat×Nat×Nat)) (k:List (Nat×Nat×Nat)->β):forceReqs l k=k l:=by
 induction l generalizing k with| nil=>rfl| cons p _ ih=>rcases p with ⟨a,b,c⟩;simp[forceReqs,forceN_eq];exact ih _
noncomputable def forceNodes{β:Type}:List NodeRecV5->(List NodeRecV5->β)->β
 | [],k=>k []
 | (i,g,lm,np,nl,tr,hs,dw,dl)::rest,k=>
  forceN i λi'=>forceReqs g λg'=>forceN lm λlm'=>forceB np λnp'=>forceB nl λnl'=>
  forceN tr λtr'=>forceSurvList hs λhs'=>forceSurvList dl λdl'=>
  forceNodes rest λr=>k ((i',g',lm',np',nl',tr',hs',dw,dl')::r)
private lemma forceNodes_eq {β:Type} (l:List NodeRecV5) (k:List NodeRecV5->β):forceNodes l k=k l:=by
 induction l generalizing k with
 | nil=>rfl
 | cons p _ ih=>
  rcases p with ⟨i,g,lm,np,nl,tr,hs,dw,dl⟩
  simp[forceNodes,forceN_eq,forceB_eq,forceReqs_eq,forceSurvList_eq];exact ih _
noncomputable def buildSwarBatch {β:Type} (nv W arity:Nat) (samples:Array (Nat×Nat))
  (nodes:List NodeRecV5) (k:Nat->Array (Nat×Nat)->Nat×Nat×Nat->β):β:=
 forceN (Nat.sub (Nat.shiftLeft 1 W) 1) λallW=>
 forceSurvList ((List.range nv).map λv=>samples.getD v (0,0)) λinitS=>
 let rec decAll:List NodeRecV5->(List (List (Nat×Nat)×(Nat×Nat×Nat))->β)->β
  | [],cont=>cont []
  | (_,gates,liveM,_,_,_,_,_,_)::rest,cont=>
   decodeSampleFwd gates initS λsbank=>
   forceSurvList (selectLive liveM sbank) λsws=>
   forceList (λp=>Nat.xor p.1 p.2) sws λcs=>
   covOfColsF allW cs 0 0 0 λcov=>
   decAll rest λxs=>cont ((sws,cov)::xs)
 decAll nodes λdecoded=>
 forceN (unitsW W decoded.length) λu=>
 forceN (combineLanes W (λd=>d.2.1) decoded) λpc1=>
 forceN (combineLanes W (λd=>d.2.2.1) decoded) λpc2=>
 forceN (combineLanes W (λd=>d.2.2.2) decoded) λpc3=>
 let rec packWires:Nat->List (Nat×Nat)->(Array (Nat×Nat)->β)->β
  | 0,acc,cont=>cont acc.toArray
  | i+1,acc,cont=>
   forceN (combineLanes W (λd=>(d.1.getD i (0,0)).1) decoded) λwp=>
   forceN (combineLanes W (λd=>(d.1.getD i (0,0)).2) decoded) λwn=>
   packWires i ((wp,wn)::acc) cont
 packWires arity [] λpw=>k u pw (pc1,pc2,pc3)
private noncomputable def swarLoopOp (W nLanes stride u ii a1 a2 jj b1 b2 r00 r01 r10:Nat) :
  Nat->List (Nat×Nat)->List (Nat×Nat)
 | 0,acc=>acc
 | op'+1,acc=>
  forceN (zN op' a1 b1) λz1=>forceN (zN op' a2 b2) λz2=>
  forceN (Nat.xor z1 z2) λcolZ=>
  forceN (fullMarksW W u (Nat.lor r00 colZ)) λm00=>
  forceN (fullMarksW W u (Nat.lor r01 colZ)) λm01=>
  forceN (fullMarksW W u (Nat.lor r10 colZ)) λm10=>
  let acc1:=cond (Nat.beq m00 0) acc ((encMove ii jj op' 0,extractMaskFuel stride nLanes m00 1 0)::acc)
  let acc2:=cond (Nat.beq m01 0) acc1 ((encMove ii jj op' 1,extractMaskFuel stride nLanes m01 1 0)::acc1)
  let acc3:=cond (Nat.beq m10 0) acc2 ((encMove ii jj op' 2,extractMaskFuel stride nLanes m10 1 0)::acc2)
  swarLoopOp W nLanes stride u ii a1 a2 jj b1 b2 r00 r01 r10 op' acc3
private noncomputable def swarLoopJ (W arity nLanes stride u:Nat) (pw:Array (Nat×Nat))
  (pc1 pc2 pc3 ii a1 a2 colA:Nat):Nat->List (Nat×Nat)->List (Nat×Nat)
 | 0,acc=>acc
 | j'+1,acc=>
  let jj:=Nat.sub (Nat.sub arity 1) j'
  let b:=pw.getD jj (0,0)
  forceN b.1 λb1=>forceN b.2 λb2=>forceN (Nat.xor b1 b2) λcolB=>
  forceN (takeTwoPacked pc1 pc2 pc3 colA colB) λr00=>
  forceN (takeOnePacked pc1 pc2 colA) λr01=>
  forceN (takeOnePacked pc1 pc2 colB) λr10=>
  swarLoopJ W arity nLanes stride u pw pc1 pc2 pc3 ii a1 a2 colA j'
   (swarLoopOp W nLanes stride u ii a1 a2 jj b1 b2 r00 r01 r10 4 acc)
private noncomputable def swarLoopI (W arity nLanes stride u:Nat) (pw:Array (Nat×Nat))
  (pc1 pc2 pc3:Nat):Nat->List (Nat×Nat)->List (Nat×Nat)
 | 0,acc=>acc
 | i'+1,acc=>
  let ii:=Nat.sub (Nat.sub arity 1) i'
  let a:=pw.getD ii (0,0)
  forceN a.1 λa1=>forceN a.2 λa2=>forceN (Nat.xor a1 a2) λcolA=>
  swarLoopI W arity nLanes stride u pw pc1 pc2 pc3 i'
   (swarLoopJ W arity nLanes stride u pw pc1 pc2 pc3 ii a1 a2 colA i' acc)
noncomputable def collectSwarSurv(nv W arity:Nat)(samples:Array (Nat×Nat))(nodes:List NodeRecV5):List (Nat×Nat):=
 buildSwarBatch nv W arity samples nodes λu pw pcov=>
 swarLoopI W arity nodes.length (Nat.add W 1) u pw pcov.1 pcov.2.1 pcov.2.2 arity []
private def decNodeSamp (nv W:Nat) (samples:Array (Nat×Nat)) (nd:NodeRecV5):List (Nat×Nat)×(Nat×Nat×Nat):=
 let initS:=(List.range nv).map λv=>samples.getD v (0,0)
 let sws:=selectLive nd.2.2.1 (decodeSampleVal nd.2.1 initS)
 (sws,covOfColsVal (Nat.sub (Nat.shiftLeft 1 W) 1) (sws.map λp=>Nat.xor p.1 p.2) 0 0 0)
private lemma zN_lt_pow {W op x y:Nat} (hx:x<2^W) (hy:y<2^W):zN op x y<2^W:=
 lt_two_pow_of_testBit λr hr=>by
  rw[zN_spec,testBit_eq_false_of_lt_pow hx hr,testBit_eq_false_of_lt_pow hy hr];rcases op with _|_|_|_<;>rfl
private abbrev FaithL (nv W:Nat) (s:Array (Nat×Nat)) (a:List Nat) (b:List (Nat×Nat)):=
 a.length=b.length/\∀k < a.length,faithfulSamp nv W s (listGetN a k) (b.getD k (0,0))
private lemma faithL_get {nv W:Nat} {s:Array (Nat×Nat)} {a:List Nat} {b:List (Nat×Nat)}
  (h:FaithL nv W s a b) (i:Nat):faithfulSamp nv W s (listGetN a i) (b.getD i (0,0)):=by
 by_cases hi:i<a.length
 ·exact h.2 i hi
 ·rw[listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt hi),
   List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
  exact⟨Nat.two_pow_pos W,Nat.two_pow_pos W,λ_ _=>⟨by simp,by simp⟩⟩
private lemma faithL_snoc {nv W:Nat} {s:Array (Nat×Nat)} {a:List Nat} {b:List (Nat×Nat)} {x:Nat} {y:Nat×Nat}
  (h:FaithL nv W s a b) (hxy:faithfulSamp nv W s x y):FaithL nv W s (a++[x]) (b++[y]):=by
 refine⟨by simp[h.1],λk hk=> ?_⟩
 simp[List.length_append]at hk
 by_cases hlt:k<a.length
 ·rw[listGetN_append_left hlt,List.getD_eq_getElem?_getD,List.getElem?_append_left (h.1▸hlt)];exact h.2 k hlt
 ·have:k=a.length:=by omega
  subst this;rw[listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
   List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),show a.length-b.length=0 by omega];exact hxy
private lemma faithL_dropAt {nv W:Nat} {s:Array (Nat×Nat)}:∀{a:List Nat}{b:List (Nat×Nat)}(i:Nat),
  FaithL nv W s a b->FaithL nv W s (dropAt i a) (dropAt i b)
 | [],[],i,h=>by cases i<;>exact h
 | [],_::_,_,h=>absurd h.1 (by simp)
 | _::_,[],_,h=>absurd h.1 (by simp)
 | _::_,_::_,0,h=>⟨by simpa[dropAt]using h.1,λk hk=>by simpa[dropAt,listGetN]using h.2 (k+1) (Nat.succ_lt_succ (by simpa[dropAt]using hk))⟩
 | _::xs,_::ys,i+1,h=>by
  have hs:=faithL_dropAt (a:=xs) (b:=ys) i ⟨by simpa using h.1,λk hk=>by simpa[listGetN]using h.2 (k+1) (Nat.succ_lt_succ hk)⟩
  exact⟨by
   simp[dropAt,hs.1],λk hk=>match k with
   | 0=>by simpa[dropAt,listGetN]using h.2 0 (by simp)
   | k'+1=>by simpa[dropAt,listGetN]using hs.2 k' (by simp[dropAt]at hk;exact hk)⟩
private lemma faithL_selectLive {nv W:Nat} {s:Array (Nat×Nat)}:∀(m:Nat){a:List Nat}{b:List (Nat×Nat)},
  FaithL nv W s a b->FaithL nv W s (selectLive m a) (selectLive m b)
 | _,[],[],_=>⟨rfl,λ_ hk=>by simp[selectLive]at hk⟩
 | _,[],_::_,h=>absurd h.1 (by simp)
 | _,_::_,[],h=>absurd h.1 (by simp)
 | m,_::xs,_::ys,h=>by
  have ht:=faithL_selectLive (Nat.shiftRight m 1) (a:=xs) (b:=ys) ⟨by simpa using h.1,λk hk=>by simpa[listGetN]using h.2 (k+1) (Nat.succ_lt_succ hk)⟩
  rw[selectLive,selectLive];cases Nat.beq (Nat.land m 1) 1
  ·simp only[Bool.cond_false];exact ht
  ·simp only[Bool.cond_true]
   exact⟨by
    rw[List.length_cons,List.length_cons,ht.1],λk hk=>match k with
    | 0=>by simpa[listGetN]using h.2 0 (by simp)
    | k'+1=>by simpa[listGetN]using ht.2 k' (by simp at hk;exact hk)⟩
private lemma faithfulSamp_zN {nv W:Nat} {s:Array (Nat×Nat)} {op w1 w2:Nat} {p1 p2:Nat×Nat}
  (h1:faithfulSamp nv W s w1 p1) (h2:faithfulSamp nv W s w2 p2) :
  faithfulSamp nv W s (zN op w1 w2) (zN op p1.1 p2.1,zN op p1.2 p2.2):=
 ⟨zN_lt_pow h1.1 h2.1,zN_lt_pow h1.2.1 h2.2.1,λt ht=>
  ⟨by rw[zN_spec,zN_spec,(h1.2.2 t ht).1,(h2.2.2 t ht).1],by rw[zN_spec,zN_spec,(h1.2.2 t ht).2,(h2.2.2 t ht).2]⟩⟩
private lemma faithL_decodeBank {nv W:Nat} {s:Array (Nat×Nat)}:∀gs {b:List Nat} {sb:List (Nat×Nat)},
  FaithL nv W s b sb->FaithL nv W s (decodeBank gs b) (decodeSampleVal gs sb)
 | [],_,_,h=>h
 | (op',a,b')::rest,b,sb,h=>
  faithL_decodeBank rest (faithL_snoc h (faithfulSamp_zN (faithL_get h a) (faithL_get h b')))
private lemma combineLanes_and {W:Nat} {α:Type} {f g:α->Nat} {xs:List α}
  (hf:∀x∈xs,f x<2^W) (hg:∀x∈xs,g x<2^W) :
  Nat.land (combineLanes W f xs) (combineLanes W g xs)=combineLanes W (λx=>Nat.land (f x) (g x)) xs:=
 combineLanes_bin hf hg _ _ rfl λ_ _ _=>Nat.testBit_and ..
private lemma combineLanes_or {W:Nat} {α:Type} {f g:α->Nat} {xs:List α}
  (hf:∀x∈xs,f x<2^W) (hg:∀x∈xs,g x<2^W) :
  Nat.lor (combineLanes W f xs) (combineLanes W g xs)=combineLanes W (λx=>Nat.lor (f x) (g x)) xs:=
 combineLanes_bin hf hg _ _ rfl λ_ _ _=>Nat.testBit_or ..
private lemma combineLanes_xor {W:Nat} {α:Type} {f g:α->Nat} {xs:List α}
  (hf:∀x∈xs,f x<2^W) (hg:∀x∈xs,g x<2^W) :
  Nat.xor (combineLanes W f xs) (combineLanes W g xs)=combineLanes W (λx=>Nat.xor (f x) (g x)) xs:=
 combineLanes_bin hf hg _ _ rfl λ_ _ _=>Nat.testBit_xor ..
private lemma andL_lt {W a b:Nat} (ha:a<2^W):Nat.land a b<2^W:=by
 rw[Nat.land_eq,Nat.and_comm];exact Nat.and_lt_two_pow b ha
private lemma orL_lt {W a b:Nat} (ha:a<2^W) (hb:b<2^W):Nat.lor a b<2^W:=Nat.or_lt_two_pow ha hb
private lemma xorL_lt {W a b:Nat} (ha:a<2^W) (hb:b<2^W):Nat.xor a b<2^W:=Nat.xor_lt_two_pow ha hb
theorem collectSwarSurv_sound {mask W:Nat} (arity:Nat) {samples:Array (Nat×Nat)} {nodes:List NodeRecV5}
  (hW:0<W) (hsok:samplesOK mask W samples=true)
  (har:∀nd∈nodes,(selectLive nd.2.2.1 (decodeBank nd.2.1 (varsNv (activeVars mask).length))).length=arity)
  {q ii jj op md k:Nat} (hq:q<nodes.length) (hij:ii<jj) (hjj:jj<arity) (hop:op<4) (hmd:md<3)
  (hlive:let nd:=nodes[q]'hq;let ws:=selectLive nd.2.2.1 (decodeBank nd.2.1 (varsNv (activeVars mask).length))
      LiveNv (activeVars mask).length (faceGoalNv mask) k
       (buildChildWs 0 ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) (Nat.beq md 2) (Nat.beq md 1)).toFinset) :
  ∃lm,(encMove ii jj op md,lm)∈collectSwarSurv (activeVars mask).length W arity samples nodes/\lm.testBit q=true:=by
 let nv:=(activeVars mask).length;obtain⟨_,hs_get,_⟩:=samplesOK_sound hsok
 let dec:=nodes.map (decNodeSamp nv W samples)
 let g1 i (d:List (Nat×Nat)×Nat×Nat×Nat):=(d.1.getD i (0,0)).1
 let g2 i (d:List (Nat×Nat)×Nat×Nat×Nat):=(d.1.getD i (0,0)).2
 have hbuild {α:Type} (k0:Nat->Array (Nat×Nat)->Nat×Nat×Nat->α):buildSwarBatch nv W arity samples nodes k0=k0 (unitsW W dec.length)
   ((List.range arity).map λi=>(combineLanes W (g1 i) dec,combineLanes W (g2 i) dec)).toArray
   (combineLanes W (·.2.1) dec,combineLanes W (·.2.2.1) dec,combineLanes W (·.2.2.2) dec):=by
  unfold buildSwarBatch;simp only[forceN_eq,forceSurvList_eq]
  have hd:∀ns (c:List (List (Nat×Nat)×Nat×Nat×Nat)->α),buildSwarBatch.decAll (Nat.sub (Nat.shiftLeft 1 W) 1) ((List.range nv).map λv=>samples.getD v (0,0)) ns c=c (ns.map (decNodeSamp nv W samples)):=λns=>by
   induction ns with| nil=>exact λ_=>rfl| cons _ _ ih=>intro _;simp only[buildSwarBatch.decAll,decodeSampleFwd_eq,forceSurvList_eq,forceList_eq,covOfColsF_eq];exact ih _
  have hp:∀n acc (c:Array (Nat×Nat)->α),buildSwarBatch.packWires W dec n acc c =
    c (((List.range n).map λi=>(combineLanes W (g1 i) dec,combineLanes W (g2 i) dec))++acc).toArray:=λn=>by
   induction n with| zero=>intros;simp[buildSwarBatch.packWires]| succ _ ih=>intros;simp only[buildSwarBatch.packWires,forceN_eq];rw[show(λx=>(List.getD x.1 _ (0,0)).1)=g1 _ from rfl,show(λx=>(List.getD x.1 _ (0,0)).2)=g2 _ from rfl,ih];simp[List.range_succ,List.append_assoc]
  rw[hd,hp];simp[dec]
 have hinitF:FaithL nv W samples (varsNv nv) ((List.range nv).map λv=>samples.getD v (0,0)):=
  ⟨by
   simp[varsNv],λk hk=>by
   have hkn:k<nv:=by simpa[varsNv]using hk
   simp only[listGetN_eq_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show k<((List.range nv).map _).length by simpa using hkn),varsNv,List.getElem_map,List.getElem_range,Option.getD_some]
   exact⟨(hs_get k hkn).1,(hs_get k hkn).2,λt _=>by unfold sampleRowP sampleRowN;rw[hiC_bits (activeVars_le mask) hkn,hiC_bits (activeVars_le mask) hkn,decide_eq_true (sampleRowFrom_lt ..),decide_eq_true (sampleRowFrom_lt ..),Bool.true_and,Bool.true_and,sampleRowFrom_tb,sampleRowFrom_tb,decide_eq_true hkn,Bool.true_and];exact⟨rfl,rfl⟩⟩⟩
 have hdecF (nd:NodeRecV5):=faithL_selectLive nd.2.2.1 (faithL_decodeBank nd.2.1 hinitF)
 have hwp_lt i d (hd:d∈dec):g1 i d<2^W/\g2 i d<2^W:=by obtain⟨nd,_,rfl⟩:=List.mem_map.mp hd;have h:=faithL_get (hdecF nd) i;exact⟨h.1,h.2.1⟩
 let xorP (p:Nat×Nat):=Nat.xor p.1 p.2
 have hcs_of nd c (hc:c∈(decNodeSamp nv W samples nd).1.map xorP):c<2^W:=by
  obtain⟨p,hp,rfl⟩:=List.mem_map.mp hc;obtain⟨i,hi,rfl⟩:=List.getElem_of_mem hp
  have h:=faithL_get (hdecF nd) i;simp[decNodeSamp]at hi ⊢;simp[List.getElem?_eq_getElem hi,Option.getD_some]at h;exact Nat.xor_lt_two_pow h.1 h.2.1
 have hcov_lt d (hd:d∈dec):d.2.1<2^W/\d.2.2.1<2^W/\d.2.2.2<2^W:=by
  obtain⟨nd,_,rfl⟩:=List.mem_map.mp hd;have hc:=covOfColsVal_spec _ (hcs_of nd);exact⟨hc.1,hc.2.1,hc.2.2.1⟩
 set nd:=nodes[q]'hq;have hselQ:=hdecF nd;set ws:=selectLive nd.2.2.1 (decodeBank nd.2.1 (varsNv nv))
 set sws:=(decNodeSamp nv W samples nd).1;have hsws_len:sws.length=arity:=hselQ.1.symm.trans (har nd (List.getElem_mem hq))
 set ka:=Nat.beq md 2;set kb:=Nat.beq md 1;set sa:=sws.getD ii (0,0);set sb:=sws.getD jj (0,0)
 set sz:=(zN op sa.1 sb.1,zN op sa.2 sb.2);let sws2:=(cond kb id (dropAt (cond ka jj (jj-1)))) ((cond ka id (dropAt ii)) sws)
 have hcF:FaithL nv W samples (buildChildWs 0 ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) ka kb) (sws2++[sz]):=by
  rw[buildChildWs_eq_dropAt ws ii jj _ ka kb hij]
  have h1:FaithL nv W samples ((cond ka id (dropAt ii)) ws) ((cond ka id (dropAt ii)) sws):=by cases ka<;>[exact faithL_dropAt ii hselQ;exact hselQ]
  exact faithL_snoc (by dsimp[sws2];cases kb<;>[exact faithL_dropAt _ h1;exact h1]) (faithfulSamp_zN (faithL_get hselQ ii) (faithL_get hselQ jj))
 have hcov_all:=sample_cover_required hsok hcF.1 hcF.2 hlive
 let cs:=sws.map xorP;have hcs_lt:=hcs_of nd
 have hcs_get idx (hi:idx<arity):cs.getD idx 0=xorP (sws.getD idx (0,0)):=by simp[cs,xorP,hsws_len▸hi]
 let cov_q:=(decNodeSamp nv W samples nd).2
 let r_q:=if md=0 then takeTwoPacked cov_q.1 cov_q.2.1 cov_q.2.2 (xorP sa) (xorP sb)
      else if md=1 then takeOnePacked cov_q.1 cov_q.2.1 (xorP sa)else takeOnePacked cov_q.1 cov_q.2.1 (xorP sb)
 have hrq_full:Nat.lor r_q (xorP sz)=2^W-1:=Nat.eq_of_testBit_eq λt=>by
  rw[Nat.lor_eq,Nat.testBit_or,Nat.testBit_two_pow_sub_one];by_cases ht:t<W
  ·simp[ht,decide_true]
   have hco:∀ps,(colsOr ps).testBit t=decide (1<=countBitAt t (ps.map xorP)):=λps=>by
    induction ps with| nil=>simp[colsOr,countBitAt]| cons p _ ih=>simp only[colsOr,List.map_cons,countBitAt,Nat.lor_eq,Nat.testBit_or,ih,xorP];cases(Nat.xor p.1 p.2).testBit t<;>simp
   have hmd':∀k (l:List (Nat×Nat)),(dropAt k l).map xorP=dropAt k (l.map xorP):=λk l=>by
    induction l generalizing k with| nil=>simp[dropAt]| cons _ _ ih=>cases k<;>simp[dropAt,ih]
   have hca:∀(l:List Nat) x,countBitAt t (l++[x])=countBitAt t l+if x.testBit t then 1 else 0:=λl x=>by
    induction l with| nil=>simp[countBitAt]| cons _ _ ih=>simp[countBitAt,ih];omega
   have hct:=congrArg (·.testBit t) hcov_all
   rw[Nat.sub_eq,shl_one,Nat.testBit_two_pow_sub_one,decide_eq_true ht,hco,List.map_append,List.map_singleton,hca]at hct
   have hcl:(sws.map xorP).length=arity:=by rw[List.length_map,hsws_len]
   have hrb:r_q.testBit t=decide (1<=countBitAt t (sws2.map xorP)):=by
    rcases(show md=0\/md=1\/md=2 by omega)with rfl|rfl|rfl
    ·change (takeTwoPacked ..).testBit t=decide (1<=countBitAt t ((dropAt (jj-1) (dropAt ii sws)).map xorP))
     rw[hmd',hmd',<-hcs_get ii (lt_trans hij hjj),<-hcs_get jj hjj];exact takeTwo_tb hcs_lt hij (hcl.symm▸hjj) t ht
    ·change (takeOnePacked ..).testBit t=decide (1<=countBitAt t ((dropAt ii sws).map xorP))
     rw[hmd',<-hcs_get ii (lt_trans hij hjj)];exact takeOne_tb hcs_lt (hcl.symm▸lt_trans hij hjj) t ht
    ·change (takeOnePacked ..).testBit t=decide (1<=countBitAt t ((dropAt jj sws).map xorP))
     rw[hmd',<-hcs_get jj hjj];exact takeOne_tb hcs_lt (hcl.symm▸hjj) t ht
   rw[hrb];cases hcz:(xorP sz).testBit t;rw[hcz]at hct;simpa using hct;simp
  ·simp only[ht,decide_false];have hmq:=List.mem_map_of_mem (f:=decNodeSamp nv W samples) (List.getElem_mem hq)
   have hcz0:=testBit_eq_false_of_lt_pow (xorL_lt (@zN_lt_pow _ op _ _ (hwp_lt ii _ hmq).1 (hwp_lt jj _ hmq).1) (@zN_lt_pow _ op _ _ (hwp_lt ii _ hmq).2 (hwp_lt jj _ hmq).2)) (Nat.le_of_not_lt ht)
   have hc10:=testBit_eq_false_of_lt_pow (by simpa[cov_q,decNodeSamp]using (hcov_lt _ hmq).1:cov_q.1<2^W) (Nat.le_of_not_lt ht)
   rw[show r_q.testBit t=false by dsimp[r_q];split_ifs<;>simp[takeTwoPacked,takeOnePacked,Nat.xor_eq,Nat.land_eq,Nat.testBit_xor,Nat.testBit_and,hc10],hcz0];rfl
 unfold collectSwarSurv;rw[hbuild];set u:=unitsW W dec.length
 set pc1:=combineLanes W (·.2.1) dec;set pc2:=combineLanes W (·.2.2.1) dec;set pc3:=combineLanes W (·.2.2.2) dec
 set pw:=((List.range arity).map λi=>(combineLanes W (g1 i) dec,combineLanes W (g2 i) dec)).toArray
 let a1:=combineLanes W (g1 ii) dec;let a2:=combineLanes W (g2 ii) dec
 let b1:=combineLanes W (g1 jj) dec;let b2:=combineLanes W (g2 jj) dec
 let r00:=takeTwoPacked pc1 pc2 pc3 (Nat.xor a1 a2) (Nat.xor b1 b2)
 let r01:=takeOnePacked pc1 pc2 (Nat.xor a1 a2);let r10:=takeOnePacked pc1 pc2 (Nat.xor b1 b2)
 let rSel:=if md=0 then r00 else if md=1 then r01 else r10
 let colZ:=Nat.xor (zN op a1 b1) (zN op a2 b2);let mT:=fullMarksW W u (Nat.lor rSel colZ)
 have hmT_bit:mT.testBit (q*(W+1))=true:=by
  have h1 d hd:=(hcov_lt d hd).1;have h2 d hd:=(hcov_lt d hd).2.1;have h3 d hd:=(hcov_lt d hd).2.2
  have ha1 d hd:=(hwp_lt ii d hd).1;have ha2 d hd:=(hwp_lt ii d hd).2;have hb1 d hd:=(hwp_lt jj d hd).1;have hb2 d hd:=(hwp_lt jj d hd).2
  have hca d hd:=xorL_lt (ha1 d hd) (ha2 d hd);have hcb d hd:=xorL_lt (hb1 d hd) (hb2 d hd)
  have hbz:binBool op false false=false:=by rcases op with _|_|_|_<;>rfl
  have hcolZ:colZ=combineLanes W (λd=>Nat.xor (zN op (g1 ii d) (g1 jj d)) (zN op (g2 ii d) (g2 jj d))) dec:=by
   dsimp[colZ];rw[combineLanes_bin ha1 hb1 _ _ hbz λ_ _ _=>zN_spec ..,combineLanes_bin ha2 hb2 _ _ hbz λ_ _ _=>zN_spec ..]
   exact combineLanes_xor (λd hd=>zN_lt_pow (ha1 d hd) (hb1 d hd)) (λd hd=>zN_lt_pow (ha2 d hd) (hb2 d hd))
  have hcz_lt d hd:=xorL_lt (@zN_lt_pow _ op _ _ (ha1 d hd) (hb1 d hd)) (@zN_lt_pow _ op _ _ (ha2 d hd) (hb2 d hd))
  have ht1 i:takeOnePacked pc1 pc2 (Nat.xor (combineLanes W (g1 i) dec) (combineLanes W (g2 i) dec)) =
    combineLanes W (λd=>takeOnePacked d.2.1 d.2.2.1 (Nat.xor (g1 i d) (g2 i d))) dec:=by
   rw[combineLanes_xor (λd hd=>(hwp_lt i d hd).1) (λd hd=>(hwp_lt i d hd).2)]
   unfold takeOnePacked;rw[combineLanes_and h1 h2,combineLanes_and (λd hd=>andL_lt (h1 d hd)) λd hd=>xorL_lt (hwp_lt i d hd).1 (hwp_lt i d hd).2,combineLanes_xor h1 λd hd=>andL_lt (andL_lt (h1 d hd))]
  have hr_comb:∃rf:_->Nat,(∀d∈dec,rf d<2^W)/\rSel=combineLanes W rf dec/\rf (dec[q]'(by simp[dec,hq]))=r_q:=by
   rcases(show md=0\/md=1\/md=2 by omega)with rfl|rfl|rfl
   ·refine⟨λd=>takeTwoPacked d.2.1 d.2.2.1 d.2.2.2 (Nat.xor (g1 ii d) (g2 ii d)) (Nat.xor (g1 jj d) (g2 jj d)),λd hd=>xorL_lt (h1 d hd) (andL_lt (h1 d hd)),?_,by simp[dec,r_q,cov_q,sa,sb,sws,nd,g1,g2,xorP]⟩
    simp only[rSel,r00,ite_true,pc1,pc2,pc3,a1,a2,b1,b2];rw[combineLanes_xor ha1 ha2,combineLanes_xor hb1 hb2];unfold takeTwoPacked
    rw[combineLanes_or hca hcb,combineLanes_and h2 (λd hd=>orL_lt (hca d hd) (hcb d hd)),combineLanes_and h3 hca,combineLanes_and (λd hd=>andL_lt (h3 d hd)) hcb,
     combineLanes_or (λd hd=>andL_lt (h2 d hd)) (λd hd=>andL_lt (andL_lt (h3 d hd))),
     combineLanes_and h1 (λd hd=>orL_lt (andL_lt (h2 d hd)) (andL_lt (andL_lt (h3 d hd)))),combineLanes_xor h1 λd hd=>andL_lt (h1 d hd)]
   ·exact⟨_,λd hd=>xorL_lt (h1 d hd) (andL_lt (andL_lt (h1 d hd))),by simp[rSel,r01,show(1:Nat)≠0 by decide,ite_false,ite_true,a1,a2];exact ht1 ii,by simp[dec,r_q,cov_q,sa,sws,nd,g1,g2,xorP,takeOnePacked]⟩
   ·exact⟨_,λd hd=>xorL_lt (h1 d hd) (andL_lt (andL_lt (h1 d hd))),by simp[rSel,r10,show(2:Nat)≠0 by decide,show(2:Nat)≠1 by decide,ite_false,b1,b2];exact ht1 jj,by simp[dec,r_q,cov_q,sb,sws,nd,g1,g2,xorP,takeOnePacked]⟩
  obtain⟨rf,hrf_lt,hr_eq,hrq_eq⟩:=hr_comb;simp only[mT,hr_eq,hcolZ,combineLanes_or hrf_lt hcz_lt]
  rw[show u=unitsW W dec.length from rfl,fullMarksW_lane_tb hW _ dec (λd hd=>orL_lt (hrf_lt d hd) (hcz_lt d hd)) q (by simp[dec,hq]),hrq_eq,show(dec[q]'(by simp[dec,hq]))=decNodeSamp nv W samples nd by simp[dec,nd]]
  exact decide_eq_true hrq_full
 have hmT_ne0:Nat.beq mT 0=false:=beq_f λh0=>by rw[h0,Nat.zero_testBit]at hmT_bit;cases hmT_bit
 let eOut:=(encMove ii jj op md,extractMaskFuel (Nat.add W 1) nodes.length mT 1 0)
 let LOp:=swarLoopOp W nodes.length (Nat.add W 1) u
 let LJ:=swarLoopJ W arity nodes.length (Nat.add W 1) u pw pc1 pc2 pc3
 let LI:=swarLoopI W arity nodes.length (Nat.add W 1) u pw pc1 pc2 pc3
 have hOpM {i0 a1' a2' j0 b1' b2' r00' r01' r10'}:∀n acc x,x∈acc->x∈LOp i0 a1' a2' j0 b1' b2' r00' r01' r10' n acc:=λn=>by
  induction n with| zero=>exact λ_ _ h=>h| succ _ ih=>intro _ _ hx;simp only[LOp,swarLoopOp,forceN_eq];exact ih _ _ (by cases Nat.beq (fullMarksW W u _) 0<;>cases Nat.beq (fullMarksW W u _) 0<;>cases Nat.beq (fullMarksW W u _) 0<;>simp[hx])
 have hJM {i0 a1' a2' cA}:∀n acc x,x∈acc->x∈LJ i0 a1' a2' cA n acc:=λn=>by
  induction n with| zero=>exact λ_ _ h=>h| succ _ ih=>intro _ _ hx;simp[LJ,swarLoopJ,forceN_eq];exact ih _ _ (hOpM 4 _ _ hx)
 have hIM:∀n acc x,x∈acc->x∈LI n acc:=λn=>by
  induction n with| zero=>exact λ_ _ h=>h| succ _ ih=>intro _ _ hx;simp[LI,swarLoopI,forceN_eq];exact ih _ _ (hJM _ _ _ hx)
 have hOpMem:∀n,op<n->∀acc,eOut∈LOp ii a1 a2 jj b1 b2 r00 r01 r10 n acc:=λn=>by
  induction n with| zero=>intro h;omega| succ op' ih=>
   intro h acc;simp only[LOp,swarLoopOp,forceN_eq];if e:op=op' then subst e;apply hOpM;rcases(show md=0\/md=1\/md=2 by omega)with rfl|rfl|rfl<;>(simp only[eOut,mT,rSel,show(1:Nat)≠0 by decide,show(2:Nat)≠0 by decide,show(2:Nat)≠1 by decide,ite_true,ite_false]at hmT_ne0 ⊢;dsimp[colZ]at hmT_ne0 ⊢;rw[hmT_ne0,Bool.cond_false])<;>(try cases Nat.beq (fullMarksW W u (Nat.lor r01 colZ)) 0)<;>(try cases Nat.beq (fullMarksW W u (Nat.lor r10 colZ)) 0)<;>simp else exact ih (by omega) _
 have hstepJ:∀n,arity-1-jj<n->∀acc,eOut∈LJ ii a1 a2 (Nat.xor a1 a2) n acc:=λn=>by
  induction n with| zero=>intro h;omega| succ j' ih=>
   intro h acc;simp only[LJ,swarLoopJ,forceN_eq];by_cases e:arity-1-jj=j';swap;exact ih (by omega) _
   rw[show Nat.sub (Nat.sub arity 1) j'=jj by simp[Nat.sub_eq];omega,show pw.getD jj (0,0)=(b1,b2) by simp[pw,Array.getD,hjj,b1,b2]]
   exact hJM j' _ _ (hOpMem 4 hop acc)
 have hstepI:∀n,arity-1-ii<n->∀acc,eOut∈LI n acc:=λn=>by
  induction n with| zero=>intro h;omega| succ i' ih=>
   intro h acc;simp only[LI,swarLoopI,forceN_eq];by_cases e:arity-1-ii=i';swap;exact ih (by omega) _
   rw[show Nat.sub (Nat.sub arity 1) i'=ii by simp[Nat.sub_eq];omega,show pw.getD ii (0,0)=(a1,a2) by simp[pw,Array.getD,lt_trans hij hjj,a1,a2]]
   exact hIM i' _ _ (hstepJ i' (by omega) acc)
 exact⟨_,hstepI arity (by omega) [],by simpa using (extractMaskFuel_tb (Nat.add W 1) nodes.length mT 0 0 0 (λ_ _=>Nat.zero_testBit _) q hq).trans hmT_bit⟩
structure FaceData where
 mask:Nat
 cap:Nat
 W:Nat
 samples:Array (Nat×Nat)
 cols:Array (Nat×Nat×Nat)
 autos:Array (List Nat)
 levels:Array LevelTopo
 loArr:Array Nat
 hiArr:Array Nat
 efArr:Array Nat
 aBits:Nat
noncomputable def graphValidV5(fd:FaceData)(colWords:Array Nat)(prior:List (Nat×Nat)):Bool:=
 let nv:=(activeVars fd.mask).length
 let priorFn:=boundsBefore prior
 and (Nat.ble 1 fd.W)
  (and (samplesOK fd.mask fd.W fd.samples)
   (and (Nat.ble 1 fd.autos.size)
    (and (fd.autos.getD 0 []==[])
     (and (allRange fd.autos.size λi=>autoSwapNvOK fd.mask (fd.autos.getD i []))
      (and (Nat.beq fd.loArr.size nv)
       (and (allRange nv λu=>Nat.beq (fd.loArr.getD u 0) (loC nv u))
        (and (Nat.beq fd.hiArr.size nv)
         (and (allRange nv λu=>Nat.beq (fd.hiArr.getD u 0) (hiC nv u))
          (and (Nat.beq fd.efArr.size nv)
           (and (allRange nv λu=>Nat.beq (fd.efArr.getD u 0) (efCNv fd.mask u))
            (and (Nat.beq fd.cols.size colWords.size)
             (and (Nat.beq (fd.levels.getD 0 (0,0,λ_=>0)).1 1)
              (forceSig (graphGoal fd.mask) λT=>
               allRange colWords.size λi=>
                let w:=colWords.getD i 0
                let c:=fd.cols.getD i (0,0,0)
                let u:=unpackColNv w
                and (colCheckNvWith fd.mask T w priorFn)
                 (and (Nat.beq c.1 u.1)
                  (and (Nat.beq c.2.1 u.2.1) (Nat.beq c.2.2 u.2.2))))))))))))))))
structure FaceValid (fd:FaceData):Prop where
 wPos:0<fd.W
 sampsOk:samplesOK fd.mask fd.W fd.samples=true
 autosOk:∀aIdx:Nat,autoSwapNvOK fd.mask (fd.autos.getD aIdx [])=true
 hiOk:∀u < (activeVars fd.mask).length,fd.hiArr.getD u 0=hiC (activeVars fd.mask).length u
 efOk:∀u < (activeVars fd.mask).length,fd.efArr.getD u 0=efCNv fd.mask u
 colsOk:ColsSound (activeVars fd.mask).length (faceGoalNv fd.mask) fd.cols
 rootCount:(fd.levels.getD 0 (0,0,λ_=>0)).1=1
theorem graphValidV5_sound {fd:FaceData} {colWords:Array Nat} {prior:List (Nat×Nat)}
  (hprior:Known prior) (hok:graphValidV5 fd colWords prior=true):FaceValid fd:=by
 unfold graphValidV5 at hok
 simp only[Bool.and_eq_true,Nat.ble_eq,Nat.beq_eq,beq_iff_eq,forceSig_eq]at hok
 obtain⟨hW,hsamp,haSz,ha0,haAll,_,_,_,hhiAll,_,hefAll,hcolSz,hrootC,hcolAll⟩:=hok
 refine⟨hW,hsamp,λaIdx=> ?_,λu hu=>Nat.beq_eq.mp (allRange_sound hhiAll u hu),
  λu hu=>Nat.beq_eq.mp (allRange_sound hefAll u hu),λci hci=> ?_,hrootC⟩
 ·by_cases hlt:aIdx<fd.autos.size
  ·exact allRange_sound haAll aIdx hlt
  ·rw[show fd.autos.getD aIdx []=[] by simp[Array.getD,hlt],<-ha0];exact allRange_sound haAll 0 (by omega)
 ·have hlt:ci<colWords.size:=by omega
  have hc:=allRange_sound hcolAll ci hlt
  simp only[Bool.and_eq_true,Nat.beq_eq]at hc
  obtain⟨hchk,h1,h2,h3⟩:=hc
  have hget:fd.cols.getD ci (0,0,0)=fd.cols[ci]'hci:=by simp[Array.getD,hci]
  rw[hget]at h1 h2 h3
  rw[h1,h2,h3];exact colValidNv_of_colCheckWith (before_sound prior hprior) hchk
noncomputable def xorAll(ws:List Nat):Nat:=
 @List.rec Nat (λ_=>Nat) 0 (λw _ ih=>Nat.xor w ih) ws
private noncomputable def precomputeDedupGo {β:Type} (levels:Array LevelTopo) (autos:Array (List Nat))
  (initW:List Nat) (hiB:B16 Nat) (nv d1 nextNum:Nat) (dlinks:List (Nat×Nat))
  (acc:List (Nat×List Nat)) (k:List (Nat×List Nat)->β):β:=
 @List.rec (Nat×Nat) (λ_=>List (Nat×List Nat)->β) (λa=>k a)
  (λp _ ih a=>
   cond (Nat.ble (Nat.add p.1 1) nextNum)
    (match decodeNode levels nv d1 p.1 with
     | (tg,tl)=>forceN tl λtl'=>
      fastStateN nv initW hiB tg tl' (autos.getD p.2 []) λrws=>
      forceN (Nat.mod (xorAll rws) 4294967291) λh=>ih ((h,rws)::a))
    (ih a))
  dlinks acc
noncomputable def precomputeDedup {β:Type} (levels:Array LevelTopo) (autos:Array (List Nat))
  (initW:List Nat) (hiB:B16 Nat) (nv d1 nextNum:Nat) (dlinks:List (Nat×Nat))
  (k:List (Nat×List Nat)->β):β:=
 precomputeDedupGo levels autos initW hiB nv d1 nextNum dlinks [] k
private noncomputable def checkDedupPreGo (cH ii jj z:Nat) (ka kb:Bool)
  (ws:List Nat) (preDedup:List (Nat×List Nat)):Bool:=
 @List.rec (Nat×List Nat) (λ_=>Bool) false
  (λp _ ih=>
   cond (Nat.beq cH p.1)
    (forceNatL (buildChildWs 0 ws ii jj z ka kb) λcws=>cond (sameWordsN cws p.2) true ih)
    ih)
  preDedup
noncomputable def checkDedupPre (wsXor ii jj wi wj z:Nat) (ka kb:Bool)
  (ws:List Nat) (preDedup:List (Nat×List Nat)):Bool:=
 match preDedup with
 | []=>false
 | _::_=>
  let cXor0:=Nat.xor wsXor z
  let cXor1:=cond ka cXor0 (Nat.xor cXor0 wi)
  let cXor:=cond kb cXor1 (Nat.xor cXor1 wj)
  forceN (Nat.mod cXor 4294967291) λcH=>checkDedupPreGo cH ii jj z ka kb ws preDedup
noncomputable def checkChild01Fast (ar Cpar maskN allV wsXor:Nat)
  (ws:List Nat) (qps:List QS01D) (qnoZ:QNoZFast)
  (needPord:Bool) (cadj:Nat) (ri:ReqIdx)
  (tMoves:List Nat) (preDedup:List (Nat×List Nat)) (mc:Nat):Bool:=
 cond (anyEq mc tMoves) true
  (let ii:=Nat.land mc 15
   let jj:=Nat.land (Nat.shiftRight mc 4) 15
   let op:=Nat.land (Nat.shiftRight mc 8) 3
   let md:=Nat.land (Nat.shiftRight mc 10) 3
   let ka:=Nat.beq md 2;let kb:=Nat.beq md 1
   cond (and (Nat.ble Cpar 1) (not (Nat.beq md 0))) true
    (cond (and needPord (and (Nat.beq md 0) (bitTest (getCadj cadj ii) jj))) true
     (forceN (Nat.shiftLeft 1 ii) λbitI=>
      forceN (Nat.shiftLeft 1 jj) λbitJ=>
      forceN (Nat.lor bitI bitJ) λbitIJ=>
      cond (checkNoZFast ii jj bitIJ ka kb qnoZ) true
       (let wi:=listGetN ws ii;let wj:=listGetN ws jj
        forceN (zN op wi wj) λz=>
        cond (or (Nat.beq z 0) (Nat.beq z maskN)) true
         (cond (anyEq z ws) true
          (forceN (keepMaskOf allV bitI bitJ ka kb) λkeepM=>
           mkDet z λzD=>
           cond (checkWithZListD2 zD bitI bitJ keepM ka kb qps) true
            (let pordLazy:=
              cond needPord
               (cond (Nat.beq md 0)
                (not (canMergePI ar Cpar cadj ri allV ii jj))
                (cond (Nat.ble 2 Cpar)
                 (not (canSolvePI ar (Nat.sub Cpar 1) cadj ri (Nat.xor allV (cond ka bitI bitJ))))
                 false))
               false
             cond pordLazy true
              (checkDedupPre wsXor ii jj wi wj z ka kb ws preDedup))))))))
private noncomputable def checkAll11LoopOpF (wsXor ii jj wi wj maskN:Nat)
  (ws:List Nat) (q11:List QS11) (tMoves:List Nat) (preDedup:List (Nat×List Nat)) (n:Nat):Bool:=
 @Nat.rec (λ_=>Bool) true
  (λop' ih=>
   let ok:=
    cond (anyEq (encMove ii jj op' 3) tMoves) true
     (forceN (zN op' wi wj) λz=>
      cond (or (Nat.beq z 0) (Nat.beq z maskN)) true
       (cond (anyEq z ws) true
        (mkDet z λzD=>
         cond (fastCost11ListD2 zD q11) true
          (checkDedupPre wsXor ii jj wi wj z true true ws preDedup))))
   cond ok ih false)
  n
private noncomputable def checkAll11LoopJF (fOp:Nat->Nat->Nat->Nat->Bool)
  (ar Cpar allV k11:Nat) (needPord:Bool) (cadj:Nat) (ri:ReqIdx)
  (i bitI wi j0 bitJ0:Nat) (lJ:List Nat):Bool:=
 @List.rec Nat (λ_=>Nat->Nat->Bool) (λ_ _=>true)
  (λwj _ ih j bitJ=>
   let skip:=or (not (Nat.beq (Nat.land k11 bitJ) 0))
    (and needPord (not (canSolvePI ar (Nat.sub Cpar 2) cadj ri (Nat.xor (Nat.xor allV bitI) bitJ))))
   cond skip (ih (Nat.add j 1) (Nat.add bitJ bitJ))
    (cond (fOp i j wi wj) (ih (Nat.add j 1) (Nat.add bitJ bitJ)) false))
  lJ j0 bitJ0
private noncomputable def checkAll11LoopIF (fOp:Nat->Nat->Nat->Nat->Bool)
  (ar Cpar allV k11:Nat) (needPord:Bool) (cadj:Nat) (ri:ReqIdx)
  (i0 bitI0:Nat) (lI:List Nat):Bool:=
 @List.rec Nat (λ_=>Nat->Nat->Bool) (λ_ _=>true)
  (λwi restI ih i bitI=>
   cond (not (Nat.beq (Nat.land k11 bitI) 0)) (ih (Nat.add i 1) (Nat.add bitI bitI))
    (cond (checkAll11LoopJF fOp ar Cpar allV k11 needPord cadj ri i bitI wi (Nat.add i 1) (Nat.add bitI bitI) restI)
     (ih (Nat.add i 1) (Nat.add bitI bitI)) false))
  lI i0 bitI0
noncomputable def checkAll11Fast (ar Cpar maskN allV wsXor:Nat)
  (ws:List Nat) (q11:List QS11) (k11:Nat) (needPord:Bool) (cadj:Nat) (ri:ReqIdx)
  (tMoves:List Nat) (preDedup:List (Nat×List Nat)):Bool:=
 cond (or (Nat.ble Cpar 2) (Nat.beq k11 allV)) true
  (checkAll11LoopIF (λi j wi wj=>checkAll11LoopOpF wsXor i j wi wj maskN ws q11 tMoves preDedup 4)
   ar Cpar allV k11 needPord cadj ri 0 1 ws)
noncomputable def checkSurvListFast(f:Nat->Bool)(laneBit:Nat)(surv:List (Nat×Nat)):Bool:=
 @List.rec (Nat×Nat) (λ_=>Bool) true
  (λp _ ih=>cond (Nat.beq (Nat.land p.2 laneBit) 0) ih (cond (f p.1) ih false))
  surv
noncomputable def verifyOneNodeBody (fd:FaceData) (nv d1 nextNum maskN kChild ar Cpar allV fullM:Nat)
  (initW:List Nat) (hiB loDB hiDB:B16 Nat) (prepped:List ColPrepD)
  (treeEdges:List (Nat×Nat)) (idx tier liveM:Nat) (gates:List (Nat×Nat×Nat))
  (hsExp dlinks:List (Nat×Nat)) (bank ws:List Nat)
  (needPord:Bool) (cadj:Nat) (ri:ReqIdx)
  (laneBit:Nat) (surv:List (Nat×Nat)):Bool:=
 forceNatL (filterLaneMoves idx treeEdges) λtMoves=>
 forceN (autoCount tier) λac=>
 detList bank λbankD=>
 forceNatL (selectLive liveM bankD) λwsD=>
 buildExpHintsDGo loDB hiDB fd.cols nv kChild allV gates bankD wsD hsExp [] emptyQNoZ [] 0 λq0 qn0 q10 k0=>
 scanAutoTierD nv kChild allV fullM ac gates bankD wsD prepped q0 qn0 q10 k0 λqps qnoZ q11 k11=>
 forceN (match dlinks with| []=>0| _::_=>xorAll ws) λwsXor=>
 precomputeDedup fd.levels fd.autos initW hiB nv d1 nextNum dlinks λpreDedup=>
 cond (checkAll11Fast ar Cpar maskN allV wsXor ws q11 k11 needPord cadj ri tMoves preDedup)
  (checkSurvListFast (checkChild01Fast ar Cpar maskN allV wsXor ws qps qnoZ needPord cadj ri tMoves preDedup) laneBit surv)
  false
noncomputable def verifyOneNodeFast (fd:FaceData) (nv d1 nextNum maskN kChild ar Cpar allV fullM:Nat)
  (initW:List Nat) (hiB efB loSB hiSB loDB hiDB:B16 Nat) (prepped:List ColPrepD)
  (treeEdges:List (Nat×Nat)) (nd:NodeRecV5) (laneBit:Nat) (surv:List (Nat×Nat)):Bool:=
 let(idx,gates,liveM,needP,needLive,tier,hsExp,deadWits,dlinks):=nd
 decodeBankFwd gates initW λbank=>
 splitLiveCPS nv liveM bank λinps gts ws=>
 cond (and (Nat.beq ws.length ar) (nodupN ws))
  (cond (or (Nat.beq ar 0) (Nat.beq Cpar 0)) true
   (let runBody np cadj ri:=
     verifyOneNodeBody fd nv d1 nextNum maskN kChild ar Cpar allV fullM initW hiB loDB hiDB prepped treeEdges
       idx tier liveM gates hsExp dlinks bank ws np cadj ri laneBit surv
    cond (and needP (and (Nat.ble Cpar 4) (Nat.ble ar 16)))
     (buildCoordsRaw nv liveM (λu=>b16Get efB u) gts λok caList deadUs=>
      cond (not ok) true
        (zipICWS caList ws 1 λicw=>
         forceN (buildCadjS icw 3) λcadj=>
         let dReqs:=verifyReqWits nv liveM ar inps caList ws deadUs deadWits
         forceReqs (cond needLive (buildLiveReqsGo loSB hiSB nv cadj inps icw ar 5 dReqs) dReqs) λreqs=>
         mkReqIdxC reqs λri=>runBody true cadj ri))
     (runBody false 0 emptyReqIdx)))
  false
noncomputable def verifyAllLanesPhase2F(f:NodeRecV5->Nat->Bool)(laneBit0:Nat)(nodes:List NodeRecV5):Bool:=
 @List.rec NodeRecV5 (λ_=>Nat->Bool) (λ_=>true)
  (λnd _ ih lb=>cond (f nd lb) (ih (Nat.add lb lb)) false)
  nodes laneBit0
noncomputable def verifyBatchV5Fast (fd:FaceData) (nv:Nat) (initW:List Nat)
  (hiB efB loSB hiSB loDB hiDB:B16 Nat) (prepped:List ColPrepD)
  (d ar start cnt colBits cBits auxStream:Nat):Bool:=
 cond (and (Nat.ble (Nat.add d 1) fd.cap) (and (Nat.ble 2 ar) (Nat.ble ar 16)))
  (let kRem:=Nat.sub fd.cap d;let kChild:=Nat.sub kRem 1
   let Cpar:=Nat.sub (Nat.add kRem 2) ar;let maskN:=maskC nv
   let allV:=Nat.sub (Nat.shiftLeft 1 ar) 1;let fullM:=Nat.sub (Nat.shiftLeft 1 d) 1;let d1:=Nat.add d 1
   let nextTopo:=fd.levels.getD d1 (0,0,λ_=>0)
   match readBatchTreeRanges nextTopo start (Nat.add start cnt) cBits auxStream with
   | (treeEdges,s1)=>
    forceSurvList treeEdges λtreeEdges'=>
    forceN s1 λs1'=>
    forceNodes (readNonLeafBatch fd.levels nv d start colBits cBits fd.aBits cnt s1') λnodes=>
    forceSurvList (collectSwarSurv nv fd.W ar fd.samples nodes) λsurv=>
    verifyAllLanesPhase2F
     (λnd lb=>verifyOneNodeFast fd nv d1 nextTopo.1 maskN kChild ar Cpar allV fullM initW hiB efB loSB hiSB loDB hiDB prepped treeEdges' nd lb surv)
     1 nodes)
  false
noncomputable def verifyOneLeafFast (nv ar Cleaf allV:Nat) (initW:List Nat)
  (efB loSB hiSB:B16 Nat) (nd:LeafRecV5):Bool:=
 let(_,gates,liveM,needLive,deadWits):=nd
 decodeBankFwd gates initW λbank=>
 splitLiveCPS nv liveM bank λinps gts ws=>
 cond (and (Nat.beq ws.length ar) (nodupN ws))
  (cond (or (Nat.beq ar 0) (Nat.beq Cleaf 0)) true
   (cond (and (Nat.ble Cleaf 4) (Nat.ble ar 16))
    (buildCoordsRaw nv liveM (λu=>b16Get efB u) gts λok caList deadUs=>
     cond (not ok) true
      (zipICWS caList ws 1 λicw=>
       forceN (buildCadjS icw 3) λcadj=>
       let dReqs:=verifyReqWits nv liveM ar inps caList ws deadUs deadWits
       forceReqs (cond needLive (buildLiveReqsGo loSB hiSB nv cadj inps icw ar 5 dReqs) dReqs) λreqs=>
       mkReqIdxC reqs λri=>not (canSolvePI ar Cleaf cadj ri allV)))
    false))
  false
noncomputable def verifyLeafBatchFast (fd:FaceData) (nv:Nat) (initW:List Nat)
  (efB loSB hiSB:B16 Nat) (d ar start cnt auxStream:Nat):Bool:=
 let kRem:=Nat.sub fd.cap d;let Cleaf:=Nat.sub (Nat.add kRem 2) ar
 let allV:=Nat.sub (Nat.shiftLeft 1 ar) 1
 allListRec (verifyOneLeafFast nv ar Cleaf allV initW efB loSB hiSB)
  (readLeafBatch fd.levels nv d start cnt auxStream)
def batchAr(hdr:Nat):Nat:=Nat.add (Nat.land hdr 15) 1
def batchStart(hdr:Nat):Nat:=Nat.land (Nat.shiftRight hdr 4) 8191
def batchCnt(hdr:Nat):Nat:=Nat.land (Nat.shiftRight hdr 17) 31
def batchIsLeaf(hdr:Nat):Bool:=Nat.beq (Nat.land (Nat.shiftRight hdr 22) 1) 1
def mbStart:List (Nat×Nat)->Nat
 | []=>0
 | (h,_)::_=>batchStart h
def mbSumCnt:List (Nat×Nat)->Nat
 | []=>0
 | (h,_)::rest=>Nat.add (batchCnt h) (mbSumCnt rest)
def mbEnd(xs:List (Nat×Nat)):Nat:=Nat.add (mbStart xs) (mbSumCnt xs)
noncomputable def verifyMultiBatchPGo(f:Nat->Nat->Bool):Nat->List (Nat×Nat)->Bool
 | _,[]=>true
 | expStart,(hdr,aux)::rest=>
  let st:=batchStart hdr;let cnt:=batchCnt hdr
  cond (Nat.beq st expStart) (cond (f hdr aux) (verifyMultiBatchPGo f (Nat.add st cnt) rest) false) false
noncomputable def forceFDLeaf{β:Type}(fd:FaceData)(k:FaceData->β):β:=
 forceN fd.mask λm=>forceN fd.cap λc=>
 forceNatL fd.efArr.toList λef=>
 k ⟨m,c,fd.W,fd.samples,fd.cols,fd.autos,fd.levels,fd.loArr,fd.hiArr,Array.mk ef,fd.aBits⟩
private lemma forceFDLeaf_eq {β:Type} (fd:FaceData) (k:FaceData->β):forceFDLeaf fd k=k fd:=by
 cases fd;simp[forceFDLeaf,forceN_eq,forceNatL_eq]
noncomputable def forceFDNonLeaf{β:Type}(fd:FaceData)(k:FaceData->β):β:=
 forceN fd.W λw=>forceSurvList fd.samples.toList λsm=>forceReqs fd.cols.toList λcl=>forceN fd.aBits λab=>
 k ⟨fd.mask,fd.cap,w,Array.mk sm,Array.mk cl,fd.autos,fd.levels,fd.loArr,fd.hiArr,fd.efArr,ab⟩
private lemma forceFDNonLeaf_eq {β:Type} (fd:FaceData) (k:FaceData->β):forceFDNonLeaf fd k=k fd:=by
 cases fd;simp[forceFDNonLeaf,forceN_eq,forceSurvList_eq,forceReqs_eq]
noncomputable def verifyMultiBatchP(fc:FaceData)(d colBits cBits:Nat)(xs:List (Nat×Nat)):Bool:=
 forceFDLeaf fc λfc0=>
 let nv:=(activeVars fc0.mask).length
 forceNatL (varsNv nv) λinitW=>
 mkB16C (λu k=>forceN (fc0.efArr.getD u 0) k) λefB=>
 mkB16C (λu k=>forceN (Nat.shiftLeft (loC nv u) 32) k) λloSB=>
 mkB16C (λu k=>forceN (Nat.shiftLeft (hiC nv u) 32) k) λhiSB=>
 cond (allListRec (λp=>batchIsLeaf p.1) xs)
  (verifyMultiBatchPGo (λhdr aux=>verifyLeafBatchFast fc0 nv initW efB loSB hiSB d (batchAr hdr) (batchStart hdr) (batchCnt hdr) aux) (mbStart xs) xs)
  (forceFDNonLeaf fc0 λfc'=>
   mkB16C (λu k=>forceN (hiC nv u) k) λhiB=>
   mkB16C (λu k=>mkDet (loC nv u) k) λloDB=>
   mkB16C (λu k=>mkDet (b16Get hiB u) k) λhiDB=>
   let maxC:=cond (Nat.ble 128 fc'.cols.size) 128 fc'.cols.size
   prepColsD loDB hiDB nv maxC fc'.cols.toList λprepped=>
   verifyMultiBatchPGo (λhdr aux=>cond (batchIsLeaf hdr)
    (verifyLeafBatchFast fc' nv initW efB loSB hiSB d (batchAr hdr) (batchStart hdr) (batchCnt hdr) aux)
    (verifyBatchV5Fast fc' nv initW hiB efB loSB hiSB loDB hiDB prepped d (batchAr hdr) (batchStart hdr) (batchCnt hdr) colBits cBits aux))
    (mbStart xs) xs)
def CutLevel(levels:Array LevelTopo)(nv goal kRem d lo hi:Nat):Prop:=
 ∀idx,lo<=idx->idx<hi->ImpossibleNv nv goal kRem (stateOf levels nv d idx).toFinset
def RangeImp(fc:FaceData)(d lo hi:Nat):Prop:=
 CutLevel fc.levels (activeVars fc.mask).length (faceGoalNv fc.mask) (fc.cap-d) d lo hi
def LevelImp(fc:FaceData)(d:Nat):Prop:=
 RangeImp fc d 0 (fc.levels.getD d (0,0,λ_=>0)).1
theorem joinCut{fc:FaceData}{d a b c:Nat}(h1:RangeImp fc d a b)(h2:RangeImp fc d b c):
 RangeImp fc d a c:=λidx hlo hhi=>if hlt:idx<b then h1 idx hlo hlt else h2 idx (Nat.le_of_not_lt hlt) hhi
theorem levelImp_empty(fc:FaceData)(d:Nat)(h0:(fc.levels.getD d (0,0,λ_=>0)).1=0):
 LevelImp fc d:=λ_ _ hhi=>by rw[h0]at hhi;omega
theorem levelImp_of_range {fc:FaceData} {d lo hi:Nat} (hr:RangeImp fc d lo hi)
  (heq:lo=0/\hi=(fc.levels.getD d (0,0,λ_=>0)).1):LevelImp fc d:=by
 rcases heq with ⟨rfl,rfl⟩;exact hr
private lemma fastStateN_cps {nv liveM:Nat} {initW:List Nat} {hiB:B16 Nat}
  {gates:List (Nat×Nat×Nat)} {perm:List Nat} :
  ∃rws,∀{β:Type}(k:List Nat->β),fastStateN nv initW hiB gates liveM perm k=k rws:=by
 cases perm with
 | nil=>exact⟨_,λk=>by dsimp[fastStateN];rw[decodeBankFwd_spec]⟩
 | cons _ _=>exact⟨_,λk=>by dsimp[fastStateN];rw[forceList_eq,decodeBankFwd_spec]⟩
private lemma precomputeDedup_sound {β:Type} {fd:FaceData} (hv:FaceValid fd) {hiB:B16 Nat} {d:Nat}
  (hhi:∀u < (activeVars fd.mask).length,b16Get hiB u=hiC (activeVars fd.mask).length u)
  (hcut:LevelImp fd (d+1)) (dlinks:List (Nat×Nat)) (k:List (Nat×List Nat)->β) :
  ∃pre,precomputeDedup fd.levels fd.autos (varsNv (activeVars fd.mask).length) hiB
   (activeVars fd.mask).length (d+1) (fd.levels.getD (d+1) (0,0,λ_=>0)).1 dlinks k=k pre /\
   ∀p∈pre,∀cws,cws.Nodup->sameWordsN cws p.2=true ->
    ImpossibleNv (activeVars fd.mask).length (faceGoalNv fd.mask) (fd.cap-d-1) cws.toFinset:=by
 let nv:=(activeVars fd.mask).length
 let OK (l:List (Nat×List Nat)):=∀p∈l,∀cws,cws.Nodup->sameWordsN cws p.2=true ->
  ImpossibleNv nv (faceGoalNv fd.mask) (fd.cap-d-1) cws.toFinset
 have go:∀ds acc,OK acc->∃pre,precomputeDedupGo fd.levels fd.autos (varsNv nv) hiB nv (d+1)
   (fd.levels.getD (d+1) (0,0,λ_=>0)).1 ds acc k=k pre/\OK pre:=λds=>by
  induction ds with
  | nil=>exact λacc h=>⟨acc,rfl,h⟩
  | cons p _ ih=>
   intro acc hacc;rcases p with ⟨cIdx,aIdx⟩;unfold precomputeDedupGo;dsimp
   cases hlt:Nat.ble (Nat.add cIdx 1) (fd.levels.getD (d+1) (0,0,λ_=>0)).1;· exact ih acc hacc
   rw[Bool.cond_true,forceN_eq]
   obtain⟨rws,hrws⟩:=@fastStateN_cps nv (decodeNode fd.levels nv (d+1) cIdx).2 (varsNv nv) hiB (decodeNode fd.levels nv (d+1) cIdx).1 (fd.autos.getD aIdx [])
   rw[hrws,forceN_eq]
   exact ih _ λq hq=>(List.mem_cons.mp hq).elim (·▸λcws hnd hs=>
    @fastStateN_sound _ _ (decodeNode fd.levels nv (d+1) cIdx).2 _ (decodeNode fd.levels nv (d+1) cIdx).1 _ _
     hhi (hv.autosOk aIdx) hnd (by rw[hrws];exact hs)
     (show ImpossibleNv nv (faceGoalNv fd.mask) (fd.cap-d-1) (stateOf fd.levels nv (d+1) cIdx).toFinset by
      simpa[Nat.sub_sub]using hcut cIdx (Nat.zero_le _) (Nat.ble_eq.mp hlt))) (hacc q)
 exact go dlinks [] (by simp[OK])
private lemma checkDedupPre_sound {nv goal kChild wsXor ii jj wi wj z:Nat} {ka kb:Bool}
  {ws:List Nat} {preDedup:List (Nat×List Nat)}
  (hpre:∀p∈preDedup,∀cws,cws.Nodup->sameWordsN cws p.2=true->ImpossibleNv nv goal kChild cws.toFinset)
  (hnd:(buildChildWs 0 ws ii jj z ka kb).Nodup)
  (hok:checkDedupPre wsXor ii jj wi wj z ka kb ws preDedup=true) :
  ImpossibleNv nv goal kChild (buildChildWs 0 ws ii jj z ka kb).toFinset:=by
 cases preDedup with| nil=>exact Bool.noConfusion hok| cons p0 rest0=>
  dsimp[checkDedupPre]at hok;rw[forceN_eq]at hok
  have go:∀cH l,(∀p∈l,∀cws,cws.Nodup->sameWordsN cws p.2=true->ImpossibleNv nv goal kChild cws.toFinset) ->
    checkDedupPreGo cH ii jj z ka kb ws l=true->ImpossibleNv nv goal kChild (buildChildWs 0 ws ii jj z ka kb).toFinset:=λcH l=>by
   induction l with| nil=>exact λ_ h=>Bool.noConfusion h| cons p _ ih=>
    intro hl h;unfold checkDedupPreGo at h;dsimp at h
    cases heq:Nat.beq cH p.1;· rw[heq]at h;exact ih (λq hq=>hl q (List.mem_cons_of_mem _ hq)) h
    rw[heq,Bool.cond_true,forceNatL_eq]at h
    exact(cond_o h).elim (hl p List.mem_cons_self _ hnd) (ih λq hq=>hl q (List.mem_cons_of_mem _ hq))
  exact go _ (p0::rest0) hpre hok
private lemma treeMove_sound {fd:FaceData} {d pIdx ii jj op km:Nat} {treeEdges:List (Nat×Nat)}
  (hcut:LevelImp fd (d+1))
  (htree:∀pm∈treeEdges,∃c < (fd.levels.getD (d+1) (0,0,λ_=>0)).1,unpackTopo (fd.levels.getD (d+1) (0,0,λ_=>0)) c=pm)
  (hii:ii<16) (hjj16:jj<16) (hop:op<4) (hkm:km<4) (hij:ii<jj)
  (hjj:jj<(stateOf fd.levels (activeVars fd.mask).length d pIdx).length)
  (hmem:anyEq (encMove ii jj op km) (filterLaneMoves pIdx treeEdges)=true) :
  let ws:=stateOf fd.levels (activeVars fd.mask).length d pIdx
  ImpossibleNv (activeVars fd.mask).length (faceGoalNv fd.mask) (fd.cap-d-1)
   (buildChildWs 0 ws ii jj (zN op (listGetN ws ii) (listGetN ws jj)) (Nat.beq (Nat.land km 2) 2) (Nat.beq (Nat.land km 1) 1)).toFinset:=by
 obtain⟨cIdx,hcLt,hcEq⟩:=htree _ (filterLaneMoves_mem ((anyEq_iff ..).mp hmem))
 dsimp only;rw[<-decodeNode_tree_edge fd.levels (activeVars fd.mask).length d pIdx cIdx ii jj op km hii hjj16 hop hkm hcEq hij hjj]
 simpa[Nat.sub_sub]using hcut cIdx (Nat.zero_le _) hcLt
private lemma liveNv_step_choice {nv goal k:Nat} {ws:List Nat} (hnd:ws.Nodup) (hlive:LiveNv nv goal (k+1) ws.toFinset) :
  ∃ii jj op ka kb,ii<jj/\jj<ws.length/\op<4 /\
   let z:=zN op (listGetN ws ii) (listGetN ws jj)
   z∉ws/\properNv nv z/\LiveNv nv goal k (buildChildWs 0 ws ii jj z ka kb).toFinset:=by
 obtain⟨U,a,b,d,hd,hS,_,_,hab,hf,tl⟩:=hlive
 obtain⟨ia,hia,rfl⟩:=List.getElem_of_mem (List.mem_toFinset.mp (hS▸Finset.mem_insert_self a _))
 obtain⟨ib,hib,rfl⟩:=List.getElem_of_mem (List.mem_toFinset.mp (hS▸Finset.mem_insert_of_mem (Finset.mem_insert_self b _)))
 have hgi i (hi:i<ws.length):listGetN ws i=ws[i]:=by simp[listGetN_eq_getD,hi]
 have hord:∃ii jj op,ii<jj/\jj<ws.length/\op<4/\zN op (listGetN ws ii) (listGetN ws jj)=zN d ws[ia] ws[ib] /\
   ws.toFinset=insert (listGetN ws ii) (insert (listGetN ws jj) U):=by
  rcases Nat.lt_or_gt_of_ne (λe:ia=ib=>hab (by subst e;rfl))with hlt| hgt
  ·exact⟨ia,ib,d,hlt,hib,hd,by rw[hgi ia hia,hgi ib hib],by rw[hgi ia hia,hgi ib hib];exact hS⟩
  ·exact⟨ib,ia,flipOp d,hgt,hia,(flip_flip hd).1,by rw[hgi ib hib,hgi ia hia,zN_flip (flip_flip hd).1,(flip_flip hd).2],by rw[hgi ib hib,hgi ia hia,Finset.insert_comm];exact hS⟩
 obtain⟨ii,jj,op,hij,hjj,hop,hzEq,hS'⟩:=hord
 let z:=zN op (listGetN ws ii) (listGetN ws jj);have hzNot:z∉ws:=λhm=>hf (hS▸hzEq▸List.mem_toFinset.mpr hm)
 let ka:=decide (listGetN ws ii∈U);let kb:=decide (listGetN ws jj∈U)
 have hcs:childSet ws ii jj z ka kb=insert (zN d ws[ia] ws[ib]) U:=by
  ext x;rw[<-hzEq];cases hka:ka<;>cases hkb:kb <;>
   simp[childSet,Bool.false_eq_true,Finset.mem_insert,Finset.mem_erase,hS'] <;>
   have h1:(listGetN ws ii∈U)↔ka=true:=(decide_eq_true_iff ..).symm <;>
   have h2:(listGetN ws jj∈U)↔kb=true:=(decide_eq_true_iff ..).symm<;>(rw[hka]at h1;rw[hkb]at h2;grind)
 exact⟨ii,jj,op,ka,kb,hij,hjj,hop,hzNot,liveNv_proper tl z (hzEq▸Finset.mem_insert_self _ _),(buildChildWs_nodup_toFinset hnd hij hjj hzNot).2.symm▸hcs.symm▸tl⟩
private lemma not_beq_land_pow (m t:Nat):not (Nat.beq (Nat.land m (2^t)) 0)=m.testBit t:=by
 cases hm:m.testBit t
 ·rw[show Nat.land m (2^t)=0 from Nat.eq_of_testBit_eq λr=>by rw[Nat.land_eq,Nat.testBit_and,Nat.testBit_two_pow,Nat.zero_testBit];by_cases e:t=r;subst e;simp[hm];simp[e]];rfl
 ·rw[beq_f λh0=>by have:=congrArg (·.testBit t) h0;rw[Nat.land_eq,Nat.testBit_and,Nat.testBit_two_pow_self,Nat.zero_testBit,hm]at this;cases this];rfl
private lemma pordSetup_elim {fd:FaceData} {efB loSB hiSB:B16 Nat} {liveM ar kRem:Nat}
  {gates:List (Nat×Nat×Nat)} {deadWits:List (Nat×Nat×Nat×Nat)} {needLive:Bool}
  (hefB:∀u < (activeVars fd.mask).length,b16Get efB u=efCNv fd.mask u)
  (hloS:∀u < (activeVars fd.mask).length,b16Get loSB u=Nat.shiftLeft (loC (activeVars fd.mask).length u) 32)
  (hhiS:∀u < (activeVars fd.mask).length,b16Get hiSB u=Nat.shiftLeft (hiC (activeVars fd.mask).length u) 32)
  (hws_len:(selectLive liveM (decodeBank gates (varsNv (activeVars fd.mask).length))).length=ar)
  (har16:ar<=16) (f:Nat->List (Nat×Nat×Nat)->Bool)
  (hgo:∀cadj reqs,GoodCadj (activeVars fd.mask).length (faceGoalNv fd.mask) (selectLive liveM (decodeBank gates (varsNv (activeVars fd.mask).length))) cadj ->
   GoodReqs (activeVars fd.mask).length (faceGoalNv fd.mask) (selectLive liveM (decodeBank gates (varsNv (activeVars fd.mask).length))) reqs->f cadj reqs=true ->
   ImpossibleNv (activeVars fd.mask).length (faceGoalNv fd.mask) kRem (selectLive liveM (decodeBank gates (varsNv (activeVars fd.mask).length))).toFinset)
  (hok:let nv:=(activeVars fd.mask).length;let sl:=splitLiveGo nv liveM 0 0 (decodeBank gates (varsNv nv));let ws:=selectLive liveM (decodeBank gates (varsNv nv))
   (buildCoordsRaw nv liveM (λu=>b16Get efB u) sl.2.1 λok caList deadUs=>
    cond (not ok) true (zipICWS caList ws 1 λicw=>forceN (buildCadjS icw 3) λcadj=>
     let dReqs:=verifyReqWits nv liveM ar sl.1 caList ws deadUs deadWits
     forceReqs (cond needLive (buildLiveReqsGo loSB hiSB nv cadj sl.1 icw ar 5 dReqs) dReqs) λreqs=>f cadj reqs))=true) :
  ImpossibleNv (activeVars fd.mask).length (faceGoalNv fd.mask) kRem (selectLive liveM (decodeBank gates (varsNv (activeVars fd.mask).length))).toFinset:=by
 dsimp at hok;set nv:=(activeVars fd.mask).length;set bk:=decodeBank gates (varsNv nv);set ws:=selectLive liveM bk
 have hsl:(splitLiveGo nv liveM 0 0 bk).2.2=ws:=splitLive_ws_eq_selectLive nv liveM bk
 obtain⟨okC,caList,deadUs,heq,hcr_f,hcr_t⟩:=@buildCoordsRaw_sound _ nv liveM (faceGoalNv fd.mask) _ gates (activeVars_le fd.mask) (λu hu=>hefB u hu▸efCNv_spec fd.mask u hu) _
 have heq':buildCoordsRaw nv liveM (λu=>b16Get efB u) (splitLiveGo nv liveM 0 0 bk).2.1 _=_:=heq
 rw[heq']at hok;cases okC;· exact hsl▸hcr_f rfl kRem
 obtain⟨hcalen,hcritAll,hcritInp,hcritDead⟩:=hcr_t rfl
 have hsl':(splitLiveGo nv liveM 0 0 (decodeBank gates (List.map (hiC nv) (List.range nv)))).2.2=ws:=hsl
 rw[hsl']at hcalen hcritAll hcritInp hcritDead
 obtain⟨icw,ez,hicw⟩:=zipICWS_spec hcalen 1 _;rw[Bool.not_true,Bool.cond_false,ez,forceN_eq,forceReqs_eq]at hok
 have hcadj:=@buildCadjS_sound _ _ _ _ _ 3 (show ws.length<=16 by omega) hcritAll hicw
 have hdReqs:GoodReqs nv (faceGoalNv fd.mask) ws (verifyReqWits nv liveM ar (splitLiveGo nv liveM 0 0 bk).1 caList ws deadUs deadWits):=
  hws_len▸@verifyReqWits_sound _ _ _ _ _ _ _ deadWits (activeVars_le fd.mask) hcritAll hcritInp hcritDead
 cases needLive;· exact hgo _ _ hcadj hdReqs hok
 have hci:=@splitLive_inps_crit nv liveM (faceGoalNv fd.mask) gates caList (by rw[hsl'];exact hcritInp)
 dsimp at hci;rw[hsl']at hci
 have hr:=@buildLiveReqsGo_sound _ _ _ _ (buildCadjS icw 3) 5 _ _ _ _ _ (activeVars_le fd.mask) hloS hhiS hcritAll hci hicw hdReqs
 rw[hws_len]at hr;exact hgo _ _ hcadj hr hok
theorem verifyBatchV5Fast_sound {fd:FaceData} (hv:FaceValid fd)
  {hiB efB loSB hiSB loDB hiDB:B16 Nat} {prepped:List ColPrepD} {d ar start cnt colBits cBits auxStream:Nat}
  (hhiB:∀u < (activeVars fd.mask).length,b16Get hiB u=hiC (activeVars fd.mask).length u)
  (hefB:∀u < (activeVars fd.mask).length,b16Get efB u=efCNv fd.mask u)
  (hloS:∀u < (activeVars fd.mask).length,b16Get loSB u=Nat.shiftLeft (loC (activeVars fd.mask).length u) 32)
  (hhiS:∀u < (activeVars fd.mask).length,b16Get hiSB u=Nat.shiftLeft (hiC (activeVars fd.mask).length u) 32)
  (hloD:∀u < (activeVars fd.mask).length,unS (b16Get loDB u)=loC (activeVars fd.mask).length u)
  (hhiD:∀u < (activeVars fd.mask).length,unS (b16Get hiDB u)=hiC (activeVars fd.mask).length u)
  (hprep:∀p∈prepped,ColPrepOK (activeVars fd.mask).length (faceGoalNv fd.mask) p)
  (hcut:LevelImp fd (d+1))
  (hok:verifyBatchV5Fast fd (activeVars fd.mask).length (varsNv (activeVars fd.mask).length)
   hiB efB loSB hiSB loDB hiDB prepped d ar start cnt colBits cBits auxStream=true) :
  RangeImp fd d start (start+cnt):=by
 let nv:=(activeVars fd.mask).length;let goal:=faceGoalNv fd.mask
 unfold verifyBatchV5Fast at hok;obtain⟨hguard,hok⟩:=cond_t hok
 simp[Bool.and_eq_true,Nat.ble_eq,Nat.add_eq]at hguard;obtain⟨hdcap,har2,har16⟩:=hguard
 set kRem:=Nat.sub fd.cap d;set kChild:=Nat.sub kRem 1;set Cpar:=Nat.sub (Nat.add kRem 2) ar
 have hCp:Cpar=fd.cap-d+2-ar:=by simp[Cpar,kRem,Nat.add_eq,Nat.sub_eq]
 set allV:=Nat.sub (Nat.shiftLeft 1 ar) 1;set fullM:=Nat.sub (Nat.shiftLeft 1 d) 1
 set nextTopo:=fd.levels.getD (d+1) (0,0,λ_=>0)
 set rngRes:=readBatchTreeRanges nextTopo start (start+cnt) cBits auxStream
 set nodes:=readNonLeafBatch fd.levels nv d start colBits cBits fd.aBits cnt rngRes.2
 set surv:=collectSwarSurv nv fd.W ar fd.samples nodes
 dsimp only at hok;simp only[forceSurvList_eq,forceN_eq,forceNodes_eq]at hok
 have htree:=readBatchTreeRanges_sound nextTopo start (start+cnt) cBits auxStream
 have hpow2 t:Nat.add (2^t) (2^t)=2^(t+1):=by change 2^t+2^t=_;rw[Nat.pow_succ];omega
 have hlanes:∀{f:NodeRecV5->Nat->Bool} k0 l,verifyAllLanesPhase2F f (2^k0) l=true->∀j (hj:j<l.length),f (l[j]'hj) (2^(k0+j))=true:=λ{f} k0 l=>by
  induction l generalizing k0 with| nil=>exact λ_ _ h=>by simp at h| cons _ _ ih=>
   intro hv2 j hj;unfold verifyAllLanesPhase2F at hv2;dsimp only at hv2;obtain⟨h1,hv2⟩:=cond_t hv2
   cases j with| zero=>simpa using h1| succ j'=>rw[hpow2]at hv2;simpa[show k0+(j'+1)=(k0+1)+j' by omega]using ih (k0+1) hv2 j' (by simp at hj;exact hj)
 have hlane_ok:=hlanes 0 nodes hok
 have har_all nd (hnd:nd∈nodes):(selectLive nd.2.2.1 (decodeBank nd.2.1 (varsNv nv))).length=ar:=by
  obtain⟨q,hq,rfl⟩:=List.getElem_of_mem hnd;have h1:=hlane_ok q hq
  rcases hndq:nodes[q]'hq with ⟨_,_,_,_,_,_,_,_,_⟩;rw[hndq]at h1;unfold verifyOneNodeFast at h1
  simp only[decodeBankFwd_spec,splitLiveCPS_spec,splitLive_ws_eq_selectLive]at h1
  exact Nat.beq_eq.mp (Bool.and_eq_true _ _ |>.mp (cond_t h1).1).1
 obtain⟨hn_len,hn_get⟩:=readNonLeafBatch_spec fd.levels nv d start colBits cBits fd.aBits cnt rngRes.2
 intro idx hlo hhi;let q:=idx-start;have hq_cnt:q<cnt:=by omega
 have ql:q<nodes.length:=hn_len.symm▸hq_cnt
 have hget:=hn_get q hq_cnt;rw[show start+q=idx by omega]at hget
 have h1:=hlane_ok q ql;rw[Nat.zero_add]at h1
 rcases hndEq:nodes[q]'ql with ⟨idx',gates,liveM,needP,needLive,tier,hsExp,deadWits,dlinks⟩
 change (nodes[q]'ql).1=idx/\((nodes[q]'ql).2.1,(nodes[q]'ql).2.2.1)=_ at hget;rw[hndEq]at hget;dsimp at hget
 rw[hndEq,hget.1]at h1;set bk:=decodeBank gates (varsNv nv);set ws:=selectLive liveM bk
 have hws_state:ws=stateOf fd.levels nv d idx:=by simp[ws,bk,stateOf,<-hget.2]
 unfold verifyOneNodeFast at h1;simp only[decodeBankFwd_spec,splitLiveCPS_spec,splitLive_ws_eq_selectLive]at h1;rw[<-hws_state]
 obtain⟨hchk,h1⟩:=cond_t h1;simp only[Bool.and_eq_true,Nat.beq_eq]at hchk
 have hws_len:ws.length=ar:=hchk.1;have hws_nd:ws.Nodup:=nodupN_sound hchk.2
 by_cases hc0:Cpar=0
 ·intro k hk hlive;have hsz:=liveNv_size hlive;rw[List.toFinset_card_of_nodup hws_nd,hws_len]at hsz;omega
 rw[beq_f (show ar≠0 by omega),beq_f hc0,Bool.or_false,Bool.cond_false]at h1
 have runBody {np cadj ri} (hpord:np=true->∃reqs,GoodCadj nv goal ws cadj/\GoodReqs nv goal ws reqs/\ReqIdxOK ws.length reqs ri)
   (hb:verifyOneNodeBody fd nv (d+1) nextTopo.1 (maskC nv) kChild ar Cpar allV fullM (varsNv nv) hiB loDB hiDB prepped rngRes.1
    idx tier liveM gates hsExp dlinks bk ws np cadj ri (2^q) surv=true):ImpossibleNv nv goal (fd.cap-d) ws.toFinset:=by
  set tM:=filterLaneMoves idx rngRes.1;unfold verifyOneNodeBody at hb
  rw[forceNatL_eq,forceN_eq,detList_eq,selectLive_map,forceNatL_eq]at hb
  obtain⟨q0,qn0,q10,k0,eb,hbuf0⟩:=buildExpHintsD_sound nv goal kChild allV gates ws hsExp (by omega) hloD hhiD hv.colsOk _
  rw[show selectLive liveM bk=ws from rfl]at hb;dsimp[bk,varsNv]at hb;rw[eb]at hb
  obtain⟨qps,qnoZ,q11,k11,es,⟨hqps_ok,hqnoZ_ok,hq11_ok,hk11_ok⟩⟩:=scanAutoTierD_sound nv goal kChild allV fullM (autoCount tier) gates ws (by omega) hprep hbuf0 _
  rw[es,forceN_eq]at hb
  obtain⟨preDedup,epd,hpre_ok⟩:=precomputeDedup_sound hv hhiB hcut dlinks _
  dsimp[varsNv]at epd;rw[epd]at hb
  set wsXor:=match dlinks with| []=>0| _::_=>xorAll ws
  obtain⟨h11,hb⟩:=cond_t hb;intro k hk hlive;cases k with
  | zero=>have hsz:=liveNv_size hlive;rw[List.toFinset_card_of_nodup hws_nd,hws_len]at hsz;omega
  | succ k'=>
   have hk':k'<=fd.cap-d-1:=by omega
   obtain⟨ii,jj,op,ka,kb,hij,hjj,hop,hzNot,hzProp,hchildLive⟩:=liveNv_step_choice hws_nd hlive
   have hii:=lt_trans hij hjj;have hne:=Nat.ne_of_lt hij;have hjj16:jj<16:=by omega
   have hii16:=lt_trans hij hjj16;set z:=zN op (listGetN ws ii) (listGetN ws jj);set cws:=buildChildWs 0 ws ii jj z ka kb
   obtain⟨hcws_nd,hcws_fin⟩:=buildChildWs_nodup_toFinset hws_nd hij hjj hzNot
   have hzNotF:z∉ws.toFinset:=λhm=>hzNot (List.mem_toFinset.mp hm)
   have hkill (h:ImpossibleNv nv goal (fd.cap-d-1) (childSet ws ii jj z ka kb)):False:=h k' hk' (hcws_fin▸hchildLive)
   have htm {m:Nat} (hm:m<4) (hka:(m&&&2).beq 2=ka) (hkb:(m % 2).beq 1=kb) (h:anyEq (encMove ii jj op m) tM=true):False:=
    (treeMove_sound hcut htree hii16 hjj16 hop hm hij (hws_state▸hjj) h) k' hk' (by simpa[cws,z,hws_state,hka,hkb]using hchildLive)
   have hsz:=liveNv_size hchildLive
   have hz0:=beq_f hzProp.2.1;have hzm:=beq_f hzProp.2.2;have hza:=Bool.eq_false_iff.mpr λh=>hzNot ((anyEq_iff z ws).mp h)
   by_cases h11_case:ka=true/\kb=true
   ·rcases h11_case with ⟨rfl,rfl⟩
    have hcard:cws.toFinset.card=ar+1:=by rw[hcws_fin];simp[childSet,Finset.card_insert_of_notMem hzNotF,List.toFinset_card_of_nodup hws_nd,hws_len]
    have k11s h:=hkill (kill11_sound hws_nd hii hjj hne hop hzNotF hk11_ok h)
    unfold checkAll11Fast at h11
    rw[show Nat.ble Cpar 2=false from Bool.eq_false_iff.mpr λh=>by have:=Nat.ble_eq.mp h;omega,Bool.false_or]at h11
    rcases cond_o h11 with hka|h11
    ·exact k11s (Or.inl <| by rw[Nat.eq_of_beq_eq_true hka];dsimp only[allV];rw[Nat.sub_eq,shl_one,Nat.testBit_two_pow_sub_one,decide_eq_true (by omega)])
    let FOp:=checkAll11LoopOpF wsXor
    let fOp a b wa wb:=FOp a b wa wb (maskC nv) ws q11 tM preDedup 4
    let P a b:=k11.testBit b=true\/(np=true/\canSolvePI ar (Nat.sub Cpar 2) cadj ri (Nat.xor (Nat.xor allV (2^a)) (2^b))=false)\/fOp a b (listGetN ws a) (listGetN ws b)=true
    have hLJ:∀a j0,checkAll11LoopJF fOp ar Cpar allV k11 np cadj ri a (2^a) (listGetN ws a) j0 (2^j0) (ws.drop j0)=true->∀b,j0<=b->b<ar->P a b:=λa j0=>by
     generalize hl:ws.drop j0=lJ;induction lJ generalizing j0 with
     | nil=>intro _ b _ hb;have:=congrArg List.length hl;simp[hws_len]at this;omega
     | cons _ _ ih=>
      obtain⟨hj0,rfl,hrest⟩:=drop_cons_iff hl;intro hJv b hb1 hb2;unfold checkAll11LoopJF at hJv;dsimp only at hJv;rw[not_beq_land_pow,hpow2]at hJv;obtain⟨hs,hJv⟩:=cond_to hJv
      if e:b=j0 then subst e;simp[Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true']at hs;exact hs.elim (λh=>h.imp id Or.inl) λh=>Or.inr (Or.inr (by simpa[listGetN_eq_getD,List.getD_eq_getElem?_getD,hj0]using h))
      else exact ih (j0+1) hrest.symm hJv b (by omega) hb2
    have hLI:∀i0,checkAll11LoopIF fOp ar Cpar allV k11 np cadj ri i0 (2^i0) (ws.drop i0)=true->∀a b,i0<=a->a<b->b<ar->k11.testBit a=true\/P a b:=λi0=>by
     generalize hl:ws.drop i0=lI;induction lI generalizing i0 with
     | nil=>intro _ a b _ _ hb;have:=congrArg List.length hl;simp[hws_len]at this;omega
     | cons _ _ ih=>
      obtain⟨hi0,rfl,hrest⟩:=drop_cons_iff hl;intro hI a b ha hab hb';unfold checkAll11LoopIF at hI;dsimp only at hI;rw[not_beq_land_pow,hpow2]at hI;obtain⟨hs,hI⟩:=cond_to hI
      if e:a=i0 then subst e;exact hs.imp id λhJ=>hLJ a (a+1) (by simpa[hrest,listGetN_eq_getD,List.getD_eq_getElem?_getD,hi0]using hJ) b (by omega) hb'
      else exact ih (i0+1) hrest.symm hI a b (by omega) hab hb'
    rcases hLI 0 h11 ii jj (Nat.zero_le _) hij (by omega)with hki|hkj|⟨hnp,hcs11⟩|hop4
    ·exact k11s (Or.inl hki)
    ·exact k11s (Or.inr hkj)
    ·obtain⟨reqs,hcadj,hreqs,hri⟩:=hpord hnp;rw[<-shl_one ii,<-shl_one jj]at hcs11
     exact hkill (@pord_child_keep_soundI _ _ _ _ _ _ _ _ _ _ true true hws_nd (by omega) hcadj hreqs hri hii hjj hne hop (Or.inl rfl) hzNotF (by simpa[allV,hws_len,show Cpar-2=fd.cap-d-1+1-ar by omega]using hcs11))
    ·have hOp:∀n,op<n->FOp ii jj (listGetN ws ii) (listGetN ws jj) (maskC nv) ws q11 tM preDedup n=true ->
       anyEq (encMove ii jj op 3) tM=true\/fastCost11ListD2 (detVal z) q11=true\/checkDedupPre wsXor ii jj (listGetN ws ii) (listGetN ws jj) z true true ws preDedup=true:=λn=>by
      induction n with| zero=>intro h;omega| succ op' ih=>
       intro h hO;dsimp[FOp]at hO;unfold checkAll11LoopOpF at hO;dsimp at hO;obtain⟨h1',h2'⟩:=cond_t hO
       if e:op=op' then subst e;rcases cond_o h1' with h0|h1';exact Or.inl h0;rw[forceN_eq,hz0,hzm,Bool.or_false,Bool.cond_false,hza,Bool.cond_false,mkDet_eq]at h1';exact Or.inr (cond_o h1')else exact ih (by omega) h2'
     rcases hOp 4 hop hop4 with h|h|h
     ·exact htm (by decide) rfl rfl h
     ·exact hkill (fastCost11ListD2_sound hws_nd hzNotF hq11_ok h)
     ·exact checkDedupPre_sound hpre_ok hcws_nd h k' hk' hchildLive
   ·let md:=if ka then 2 else if kb then 1 else 0
    have hmdP:md<3/\Nat.beq md 2=ka/\Nat.beq md 1=kb/\(md&&&2).beq 2=ka/\(md % 2).beq 1=kb:=by
     cases ka<;>cases kb<;>first| exact absurd ⟨rfl,rfl⟩ h11_case| (dsimp[md];decide)
    obtain⟨lm,hmem_surv,hlm_q⟩:=collectSwarSurv_sound ar hv.wPos hv.sampsOk har_all ql hij (by omega) hop hmdP.1 (by simpa[hndEq,ws,bk,z,hmdP.2.1,hmdP.2.2.1]using hchildLive)
    have hsurv:∀{f:Nat->Bool} l,checkSurvListFast f (2^q) l=true->(encMove ii jj op md,lm)∈l->f (encMove ii jj op md)=true:=λ{f} l=>by
     induction l with| nil=>intro _ h;simp at h| cons p _ ih=>
      rcases p with ⟨mc',lm'⟩;intro hc hm;unfold checkSurvListFast at hc;dsimp only at hc;obtain⟨hs,htl⟩:=cond_to hc
      exact(List.mem_cons.mp hm).elim (λe=>by rcases Prod.mk.inj e with ⟨rfl,rfl⟩;exact hs.resolve_left λh0=>by have:=not_beq_land_pow lm q;rw[hlm_q,h0]at this;cases this) (ih htl)
    have hc:=hsurv surv hb hmem_surv
    obtain⟨hf1,hf2,hf3,hf4⟩:=@encMove_fields _ _ _ md hii16 hjj16 hop (by omega)
    unfold checkChild01Fast at hc
    rcases cond_o hc with h|hc;· exact htm (by omega) hmdP.2.2.2.1 hmdP.2.2.2.2 h
    simp only[hf1,hf2,hf3,hf4,hmdP.2.1,hmdP.2.2.1,forceN_eq,mkDet_eq,show zN op (listGetN ws ii) (listGetN ws jj)=z from rfl]at hc
    rcases cond_o hc with hbr0|hc
    ·simp only[Bool.and_eq_true,Bool.not_eq_true',Nat.ble_eq]at hbr0
     have h1e {x} (hx:x∈ws.toFinset):(insert z (ws.toFinset.erase x)).card=ar:=by
      rw[Finset.card_insert_of_notMem λhm=>hzNotF (Finset.mem_of_mem_erase hm),Finset.card_erase_of_mem hx,List.toFinset_card_of_nodup hws_nd,hws_len];omega
     have hcard:cws.toFinset.card=ar:=by
      rw[hcws_fin];cases ka<;>cases kb<;>first| (simp[md]at hbr0;done)| exact absurd ⟨rfl,rfl⟩ h11_case| exact h1e (List.mem_toFinset.mpr (listGetN_mem hii))| exact h1e (List.mem_toFinset.mpr (listGetN_mem hjj))
     omega
    rcases cond_o hc with hbr1|hc
    ·simp only[Bool.and_eq_true,Nat.beq_eq]at hbr1
     obtain⟨rfl,rfl⟩:ka=false/\kb=false:=by cases ka<;>cases kb<;>simp[md]at hbr1;exact⟨rfl,rfl⟩
     obtain⟨reqs,hcadj,hreqs,hri⟩:=hpord hbr1.1
     exact hkill (pord_child_00_soundI hws_nd (by omega) hcadj hreqs hri hii hjj hne hop hzNotF (Or.inl hbr1.2.2))
    rcases cond_o hc with hbr2|hc;· exact hkill (checkNoZFast_sound hws_nd hii hjj hne hop hzNotF hqnoZ_ok hbr2)
    rw[hz0,hzm,Bool.or_false,Bool.cond_false,hza,Bool.cond_false]at hc
    rcases cond_o hc with hbr3|hc;· exact hkill (checkWithZListD2_sound hws_nd hii hjj hne hzNotF hqps_ok (by simpa[allV,hws_len]using hbr3))
    rcases cond_o hc with hbr4|hc
    ·obtain⟨hnp,h4⟩:=cond_t hbr4;obtain⟨reqs,hcadj,hreqs,hri⟩:=hpord hnp
     cases hmd0:Nat.beq md 0
     ·rw[hmd0,Bool.cond_false]at h4;obtain⟨_,h4⟩:=cond_t h4;rw[Bool.not_eq_true']at h4
      cases ka<;>cases kb<;>first| (simp[md]at hmd0;done)| exact absurd ⟨rfl,rfl⟩ h11_case|
       exact hkill (pord_child_keep_soundI hws_nd (by omega) hcadj hreqs hri hii hjj hne hop (by simp) hzNotF (by simpa[hws_len,allV,show Cpar-1=fd.cap-d-1+2-ar by omega]using h4))
     ·rw[hmd0,Bool.cond_true,Bool.not_eq_true']at h4
      obtain⟨rfl,rfl⟩:ka=false/\kb=false:=by cases ka<;>cases kb<;>simp[md]at hmd0;exact⟨rfl,rfl⟩
      exact hkill (pord_child_00_soundI hws_nd (by omega) hcadj hreqs hri hii hjj hne hop hzNotF (Or.inr <| by simpa[hws_len,allV,show Cpar=fd.cap-d-1+3-ar by omega]using h4))
    ·exact checkDedupPre_sound hpre_ok hcws_nd hc k' hk' hchildLive
 cases hnp:and needP (and (Nat.ble Cpar 4) (Nat.ble ar 16));· rw[hnp]at h1;exact runBody (λh=>Bool.noConfusion h) h1
 rw[hnp,Bool.cond_true]at h1
 exact @pordSetup_elim _ _ _ _ _ _ (fd.cap-d) _ _ _ hefB hloS hhiS hws_len har16 _
  (λcadj reqs hc hr hb=>by rw[mkReqIdxC_eq]at hb;exact runBody (λ_=>⟨reqs,hc,hr,mkReqIdx_of_goodReqs (by omega) hr⟩) hb) h1
theorem verifyLeafBatchFast_sound {fd:FaceData} (hv:FaceValid fd)
  {efB loSB hiSB:B16 Nat} {d ar start cnt auxStream:Nat}
  (hefB:∀u < (activeVars fd.mask).length,b16Get efB u=efCNv fd.mask u)
  (hloS:∀u < (activeVars fd.mask).length,b16Get loSB u=Nat.shiftLeft (loC (activeVars fd.mask).length u) 32)
  (hhiS:∀u < (activeVars fd.mask).length,b16Get hiSB u=Nat.shiftLeft (hiC (activeVars fd.mask).length u) 32)
  (hok:verifyLeafBatchFast fd (activeVars fd.mask).length (varsNv (activeVars fd.mask).length) efB loSB hiSB d ar start cnt auxStream=true) :
  RangeImp fd d start (start+cnt):=by
 let nv:=(activeVars fd.mask).length;unfold verifyLeafBatchFast at hok;rw[allListRec_iff]at hok
 set kRem:=Nat.sub fd.cap d;set Cleaf:=Nat.sub (Nat.add kRem 2) ar;set allV:=Nat.sub (Nat.shiftLeft 1 ar) 1
 set nodes:=readLeafBatch fd.levels nv d start cnt auxStream
 obtain⟨hn_len,hn_get⟩:=readLeafBatch_spec fd.levels nv d start cnt auxStream
 intro idx hlo hhi;let q:=idx-start;have hq_cnt:q<cnt:=by omega
 have ql:q<nodes.length:=hn_len.symm▸hq_cnt
 have hget:=hn_get q hq_cnt;rw[show start+q=idx by omega]at hget
 have h1:=hok (nodes[q]'ql) (List.getElem_mem ql)
 rcases hnd:nodes[q]'ql with ⟨idx',gates,liveM,needLive,deadWits⟩
 change ((nodes[q]'ql).2.1,(nodes[q]'ql).2.2.1)=_ at hget;rw[hnd]at hget
 rw[hnd]at h1;unfold verifyOneLeafFast at h1;simp only[decodeBankFwd_spec,splitLiveCPS_spec,splitLive_ws_eq_selectLive]at h1
 set ws:=selectLive liveM (decodeBank gates (varsNv nv))
 rw[show stateOf fd.levels nv d idx=ws by simp[ws,stateOf,<-hget]]
 obtain⟨hchk,h1⟩:=cond_t h1;simp only[Bool.and_eq_true,Nat.beq_eq]at hchk
 have hws_len:ws.length=ar:=hchk.1;have hws_nd:ws.Nodup:=nodupN_sound hchk.2
 rcases cond_o h1 with htriv|h1
 ·simp[Bool.or_eq_true,Nat.beq_eq]at htriv;intro k hk hlive
  have hsz:=liveNv_size hlive;rw[List.toFinset_card_of_nodup hws_nd,hws_len]at hsz
  rcases htriv with har0|hc0
  ·have:0<ws.toFinset.card:=by cases k with| zero=>simp[LiveNv]at hlive;simp[hlive]| succ _=>obtain⟨_,_,_,_,_,hS,_⟩:=hlive;rw[hS];exact Finset.card_pos.mpr (Finset.insert_nonempty _ _)
   rw[List.toFinset_card_of_nodup hws_nd,hws_len]at this;omega
  ·dsimp only[Cleaf,kRem]at hc0;simp only[Nat.sub_eq,Nat.add_eq]at hc0;omega
 ·obtain⟨hg,h1⟩:=cond_t h1;simp only[Bool.and_eq_true,Nat.ble_eq]at hg
  exact @pordSetup_elim _ _ _ _ _ _ (fd.cap-d) _ _ _ hefB hloS hhiS hws_len hg.2 _
   (λcadj reqs hc hr hb=>by
    rw[mkReqIdxC_eq,Bool.not_eq_true']at hb
    exact canSolvePI_sound hws_nd (show ws.length<=16 by omega) hc hr
     (mkReqIdx_ok (show ws.length<=16 by omega) reqs λr h=>let⟨a,b,c,_⟩:=hr r h;⟨a,b,c⟩)
     (by rw[hws_len];simpa[Cleaf,kRem,allV]using hb)) h1
private lemma verifyMultiBatchPGo_sound {fc:FaceData} {d:Nat} {f:Nat->Nat->Bool}
  (hf:∀hdr aux,f hdr aux=true->RangeImp fc d (batchStart hdr) (batchStart hdr+batchCnt hdr)) :
  ∀l exp,verifyMultiBatchPGo f exp l=true->RangeImp fc d exp (Nat.add exp (mbSumCnt l))
 | [],exp,_=>λidx h1 h2=>by simp[mbSumCnt]at h2;omega
 | (hdr,aux)::rest,exp,h=>by
  simp only[verifyMultiBatchPGo]at h
  obtain⟨hst,h⟩:=cond_t h;have heq:=Nat.eq_of_beq_eq_true hst
  obtain⟨h1,h⟩:=cond_t h
  have hhd:RangeImp fc d exp (exp+batchCnt hdr):=heq▸hf hdr aux h1
  have htl:=verifyMultiBatchPGo_sound hf rest (Nat.add (batchStart hdr) (batchCnt hdr)) h;rw[heq]at htl
  rw[show Nat.add exp (mbSumCnt ((hdr,aux)::rest))=Nat.add (exp+batchCnt hdr) (mbSumCnt rest) by simp[mbSumCnt,Nat.add_eq];omega]
  exact joinCut hhd htl
theorem verifyMultiBatchP_sound_range
  {fc:FaceData} {d:Nat} (hv:FaceValid fc) (hnext:LevelImp fc (d+1))
  {colBits cBits:Nat} {xs:List (Nat×Nat)}
  (hok:verifyMultiBatchP fc d colBits cBits xs=true) :
  RangeImp fc d (mbStart xs) (mbEnd xs):=by
 let nv:=(activeVars fc.mask).length;have hnv16:nv<=12:=activeVars_le fc.mask
 have mkF (g:Nat->Nat) (k:B16 Nat->Bool):∃t,mkB16C (λu c=>forceN (g u) c) k=k t/\∀u < nv,b16Get t u=g u:=
  let⟨t,e,h⟩:=mkB16C_spec (g:=g) (λ_ _ _=>forceN_eq ..) k;⟨t,e,λu hu=>h u (by omega)⟩
 have mkD (g:Nat->Nat) (k:B16 Nat->Bool):∃t,mkB16C (λu c=>mkDet (g u) c) k=k t/\∀u < nv,unS (b16Get t u)=g u:=
  let⟨t,e,h⟩:=mkB16C_spec (g:=λu=>detVal (g u)) (λ_ _ _=>mkDet_eq ..) k;⟨t,e,λu hu=>by rw[h u (by omega),unS_detVal]⟩
 unfold verifyMultiBatchP at hok;rw[forceFDLeaf_eq,forceNatL_eq]at hok
 obtain⟨efB,e2,h2⟩:=mkF (λu=>fc.efArr.getD u 0) _;rw[e2]at hok
 have hefB:∀u < nv,b16Get efB u=efCNv fc.mask u:=λu hu=>(h2 u hu).trans (hv.efOk u hu)
 obtain⟨loSB,e3,hloS⟩:=mkF (λu=>Nat.shiftLeft (loC nv u) 32) _;rw[e3]at hok
 obtain⟨hiSB,e4,hhiS⟩:=mkF (λu=>Nat.shiftLeft (hiC nv u) 32) _;rw[e4]at hok
 cases hall:allListRec (λp=>batchIsLeaf p.1) xs
 ·rw[hall,Bool.cond_false,forceFDNonLeaf_eq]at hok
  obtain⟨hiB,e1,hhiB⟩:=mkF (hiC nv) _;rw[e1]at hok
  obtain⟨loDB,e5,hloD⟩:=mkD (loC nv) _;rw[e5]at hok
  obtain⟨hiDB,e6,h6⟩:=mkD (b16Get hiB) _;rw[e6]at hok
  have hhiD:∀u < nv,unS (b16Get hiDB u)=hiC nv u:=λu hu=>(h6 u hu).trans (hhiB u hu)
  obtain⟨prepped,e7,hprep⟩:=prepColsD_sound hloD hhiD (λc hc=>let⟨i,hi,e⟩:=List.getElem_of_mem hc;e▸hv.colsOk i (by simpa using hi)) _
  rw[e7]at hok
  exact verifyMultiBatchPGo_sound (λhdr aux h=>by cases hl:batchIsLeaf hdr<;>rw[hl]at h;exact verifyBatchV5Fast_sound hv hhiB hefB hloS hhiS hloD hhiD hprep hnext h;exact verifyLeafBatchFast_sound hv hefB hloS hhiS h) xs (mbStart xs) hok
 ·rw[hall,Bool.cond_true]at hok
  exact verifyMultiBatchPGo_sound (λhdr aux h=>verifyLeafBatchFast_sound hv hefB hloS hhiS h) xs (mbStart xs) hok
theorem stateOf_zero(levels:Array LevelTopo)(nv idx:Nat):stateOf levels nv 0 idx=varsNv nv:=by
 unfold stateOf;simp[decodeNode,decodeBank]
 have hsel:∀(n:Nat)(l:List Nat),l.length=n->selectLive (Nat.sub (Nat.shiftLeft 1 n) 1) l=l:=by
  intro n;induction n with
  | zero=>intro l hl;cases l<;>[rfl;simp at hl]
  | succ k ih=>
   intro l hl;cases l with
   | nil=>simp at hl
   | cons x xs=>
    have hb0:Nat.beq (Nat.land (Nat.sub (Nat.shiftLeft 1 (k+1)) 1) 1) 1=true:=by
     rw[bit0_tb,Nat.sub_eq,shl_one,Nat.testBit_two_pow_sub_one];simp
    have hshr:Nat.shiftRight (Nat.sub (Nat.shiftLeft 1 (k+1)) 1) 1=Nat.sub (Nat.shiftLeft 1 k) 1:=
     Nat.eq_of_testBit_eq λr=>by
      rw[tb_shr,Nat.sub_eq,Nat.sub_eq,shl_one,shl_one,Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow_sub_one]
      simp[show(1+r<k+1)↔(r<k) by omega]
    simp only[selectLive,hb0,Bool.cond_true,hshr];exact congrArg (x::·) (ih xs (by simpa using hl))
 exact hsel nv (varsNv nv) (by simp[varsNv])
theorem allLevels_sound{fd:FaceData}(hv:FaceValid fd)(hcut0:LevelImp fd 0):
  ImpossibleNv (activeVars fd.mask).length (faceGoalNv fd.mask) fd.cap (varsNv (activeVars fd.mask).length).toFinset:=by
 have h0:=hcut0 0 (Nat.zero_le 0) (by rw[hv.rootCount];decide)
 rwa[stateOf_zero]at h0
theorem faceImpossible12{fd:FaceData}(hv:FaceValid fd)(hcut0:LevelImp fd 0):
  Impossible (graphGoal fd.mask) fd.cap (vars fd.mask).toFinset:=
 embed_nv_impossible12 (allLevels_sound hv hcut0)
theorem faceLower {fd:FaceData} {hints:Nat} (hv:FaceValid fd)
  (hroot:faceRootOK fd.mask hints=true) (hcut0:LevelImp fd 0) :
  Face fd.mask (fd.cap+1):=
 embed_nv_to_12 hroot (allLevels_sound hv hcut0)
end Engine
end PEqualNP.Outside.L_meta_52834
namespace PEqualNP.Outside.L_meta_52834
namespace Cert
open Engine
abbrev ps:=applyPackedSteps
abbrev ks:=known_of_packedSteps
abbrev gv:=@graphValidV5_sound
abbrev mb:=@verifyMultiBatchP_sound_range
abbrev jc:=@joinCut
abbrev lz:=@levelImp_empty
abbrev LI:=LevelImp
abbrev FV:=FaceValid
abbrev K:=Known
abbrev kc:=@known_cons
abbrev vg f c e:=graphValidV5 f c e=true
def r0:LevelTopo:=(1,1,fun _=>0)
def z0:LevelTopo:=(0,0,fun _=>0)
def w1(a:Array Nat)(i:Nat):Nat:=a.getD i 0
def w2(a:Array (Array Nat))(i:Nat):Nat:=(a.getD (Nat.shiftRight i 3) #[]).getD (Nat.land i 7) 0
def w3(a:Array (Array (Array Nat)))(i:Nat):Nat:=((a.getD (Nat.shiftRight i 6) #[]).getD (Nat.land (Nat.shiftRight i 3) 7) #[]).getD (Nat.land i 7) 0
def u16(h:Nat):List Nat→List (Nat×Nat)
 | []=>[] | a::r=>(h,a)::u16 (Nat.add h 256) r
def u31(h:Nat):List Nat→List (Nat×Nat)
 | []=>[] | a::r=>(h,a)::u31 (Nat.add h 496) r
def u3(h:Nat):Nat→List (Nat×Nat)
 | 0=>[] | n+1=>(h,1)::u3 (Nat.add h 496) n
def ug(w msk:Nat):Nat→Nat→List Nat→List Nat
 | 0,_,a=>a | n+1,m,a=>ug w msk n (Nat.shiftRight m w) (Nat.land m msk::a)
def u53(xs:List (Nat×Nat)):Array Nat:=(xs.foldr (fun p a=>ug 53 0x1fffffffffffff p.1 p.2 a) []).toArray
def ust(xs:List (Nat×Nat×Nat)):Array Nat:=(xs.foldr (fun p a=>ug p.2.1 (Nat.sub (Nat.shiftLeft 1 p.2.1) 1) p.1 p.2.2 a) []).toArray
abbrev ms:=mkSamplesX
def m0(o:Nat):List (Nat×Nat)→List (Nat×Nat)
 | []=>[] | (p,c)::r=>(p,Nat.xor p (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 c) 1) o))::m0 (Nat.add o c) r
def ms0(xs:List (Nat×Nat)):Array (Nat×Nat):=(m0 0 xs).toArray
lemma fl{fc:FaceData}(hv:FV fc)(h:Nat)(hd:faceRootOK fc.mask h=true)(h0:LI fc 0):Face fc.mask (fc.cap+1):=faceLower hv (hints:=h) hd h0
lemma lc{fc:FaceData}{d a b:Nat}(h:RangeImp fc d a b)(he:a=0∧b=(fc.levels.getD d z0).1:=by decide +kernel):LI fc d:=levelImp_of_range h he
lemma l1{fc:FaceData}{d:Nat}(hv:FV fc)(hn:LI fc (d+1))(cb xb:Nat)(xs:List (Nat×Nat))(hb:verifyMultiBatchP fc d cb xb xs=true)(he:mbStart xs=0∧mbEnd xs=(fc.levels.getD d z0).1:=by decide +kernel):LI fc d:=levelImp_of_range (mb hv hn hb) he
lemma l0{fc:FaceData}{d:Nat}(hv:FV fc)(cb xb:Nat)(xs:List (Nat×Nat))(hb:verifyMultiBatchP fc d cb xb xs=true)(h0:(fc.levels.getD (d+1) z0).1=0:=by decide +kernel)(he:mbStart xs=0∧mbEnd xs=(fc.levels.getD d z0).1:=by decide +kernel):LI fc d:=levelImp_of_range (mb hv (lz fc (d+1) h0) hb) he
def mkFD(m cap W:Nat)(sm:Array (Nat×Nat))(cw:Array Nat)(au:Array (List Nat))(lv:Array LevelTopo)(ab:Nat):FaceData:=
 let nv:=(activeVars m).length;⟨m,cap,W,sm,unpackColsNv cw,au,lv,mkLoArr nv,mkHiArr nv,mkEfArr m,ab⟩
def st:=ust [(16,47,0xc820200a822b884040150517808080a21a0f01010114311822020680613c84040450c178080802a128f21010054245c62020610453d440408a02a70080802a0a8c31010340321e62020610253d040401508570010a08a08f06021412812e),(4,55,0xc000042822826c180008504a04eb000010a0a20b360000214150172),(8,63,0x200000042825035401c00008508508d800380010a11411d0006000214320332e00000042860870c4000000850c20e2b80000010a1881c930000002143203a2),(7,47,0x8040406306678080e0aa1a8f2101c15434562202031834bd04070550c56008080c60e4f6101c154255),(13,63,0x4321201c3503290000ca20386505520040c008601501f880028010c02a06f00000402180a80ee60a00004300a81ec08100008602a03e80000381d015415700006003a031431e00000c074065065c0180000e80c50cdb8000001d018a1cb10000003a03283aa),(16,47,0x8420402782db004070e30f260081009e0bcb1101c38c3a5402038748762804070e30e67b081009e11ed3102023c29d8020383583d2c440706706d61080e0da0f2c2101c19c1cd4020383583730040706707660080e0da0f8e0052c35435e),(1,63,0x700000052c3543d6),(10,47,0x2108140de0f6c0102839c3d984205073879a8040a0eb0ee5888141ce1dab110281dc1f58020503783f3d840b05f09f68881613e17ad3102c27c2dd),(1,63,0x432150302c27c2f9),(5,47,0x20102c2f82ed8020585f057b0840d0ef0fb60081a1de1fcb110343dc3f5)]
def e0:List (Nat×Nat):=[]
lemma k0:K e0:=baseKnown
namespace f0
def c:Array Nat:=#[]
def fc:=mkFD 21 3 6 (ms0 [(23,2),(45,2),(58,2)]) c #[[]] #[r0] 1
lemma g:vg fc c e0:=by decide +kernel
lemma fv:FV fc:=gv k0 g
lemma d0:LI fc 0:=l0 fv 1 1 [(4325378,0)] (by decide +kernel)
end f0
def e1:=(21,4)::e0
lemma k1:K e1:=kc (fl f0.fv 2 (by decide +kernel) f0.d0) k0
def e2:=ps e1 st 0 18
lemma k2:K e2:=ks st 0 18 e1 k1 (by decide +kernel)
namespace f1
def c:=u53 [(4,0x20000288000011000011400001080000a80000024000015000008)]
def fc:=mkFD 85 6 12 (ms0 [(591,3),(1209,3),(2514,3),(3876,3)]) c #[[],[50],[33],[33,50],[16],[16,50],[32,33],[32,33,50],[32,49]] #[r0,(1,1,w1 #[6688]),(3,1,w1 #[0x5a109420a40]),(1,2,w1 #[1088])] 4
abbrev p d b x:=verifyMultiBatchP fc d 2 b x=true
lemma g:vg fc c e2:=by decide +kernel
lemma fv:FV fc:=gv k2 g
lemma d3:LI fc 3:=l0 fv 2 1 [(131075,16)] (by decide +kernel)
lemma b0:p 2 1 [(131076,2065)]:=by decide +kernel
lemma b1:p 2 1 [(4456468,0)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b0) (mb fv d3 b1))
lemma d1:LI fc 1:=l1 fv d2 2 2 [(131076,0xa12a100859061)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 2 1 [(131075,0x1038c1842c811)] (by decide +kernel)
end f1
def e3:=(85,7)::e2
lemma k3:K e3:=kc (fl f1.fv 2 (by decide +kernel) f1.d0) k2
def e4:=ps e3 st 18 20
lemma k4:K e4:=ks st 18 20 e3 k3 (by decide +kernel)
namespace f2
def c:Array Nat:=#[]
def fc:=mkFD 99 3 12 (ms0 [(3467,2),(1788,4),(2286,2),(3891,4)]) c #[[]] #[r0] 1
lemma g:vg fc c e4:=by decide +kernel
lemma fv:FV fc:=gv k4 g
lemma d0:LI fc 0:=l0 fv 1 1 [(4325379,0)] (by decide +kernel)
end f2
def e5:=(99,4)::e4
lemma k5:K e5:=kc (fl f2.fv 1048662 (by decide +kernel) f2.d0) k4
def e6:=ps e5 st 20 42
lemma k6:K e6:=ks st 20 42 e5 k5 (by decide +kernel)
namespace f3
def c:=u53 [(4,0x280002680000114000138000004a00008e000010500004b000004)]
def fc:=mkFD 79 7 24 (ms0 [(4532015,4),(1471218,4),(9981767,4),(14742644,4),(16746632,8)]) c #[[],[49],[16,50],[48,49,50],[32],[32,49],[16,33,50]] #[r0,(3,1,w1 #[0x7a00d401a20]),(8,2,w1 #[0x5a89b5412a873527ca8aa5410a81500]),(3,3,w1 #[0x6a685488218])] 3
abbrev p d b x:=verifyMultiBatchP fc d 2 b x=true
lemma g:vg fc c e6:=by decide +kernel
lemma fv:FV fc:=gv k6 g
lemma d3:LI fc 3:=l0 fv 2 1 [(4587524,0)] (by decide +kernel)
lemma b0:p 2 2 [(524293,0x204450391f0d061)]:=by decide +kernel
lemma b1:p 2 2 [(4325444,0),(4587605,0)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b0) (mb fv d3 b1))
lemma d1:LI fc 1:=l1 fv d2 2 3 [(393221,0x5122670f60b9520b0d00c3201)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 2 2 [(131076,0xcb18a1a124582261861)] (by decide +kernel)
end f3
def e7:=(79,8)::e6
lemma k7:K e7:=kc (fl f3.fv 4146 (by decide +kernel) f3.d0) k6
namespace f4
def c:=u53 [(4,0x20000330000009400811402000080000c60000085000047000008)]
def fc:=mkFD 103 6 25 (ms0 [(9772127,5),(5999586,5),(23231623,5),(25416436,3),(33317656,7)]) c #[[],[32]] #[r0,(2,1,w1 #[255859328]),(1,1,w1 #[1700])] 1
lemma g:vg fc c e7:=by decide +kernel
lemma fv:FV fc:=gv k7 g
lemma d2:LI fc 2:=l0 fv 2 1 [(4325380,0)] (by decide +kernel)
lemma d1:LI fc 1:=l1 fv d2 2 1 [(262149,67601)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 2 1 [(131076,92605473)] (by decide +kernel)
end f4
def e8:=(103,7)::e7
lemma k8:K e8:=kc (fl f4.fv 1048658 (by decide +kernel) f4.d0) k7
namespace f5
def c:=u53 [(5,0x504002a0010002000034800001140001a8000004a0000960000104000063000004)]
def fc:=mkFD 107 6 24 (ms0 [(14060075,2),(1623036,6),(6504204,6),(8645810,4),(16527555,6)]) c #[[]] #[r0,(1,1,w1 #[6722]),(1,1,w1 #[1702])] 1
lemma g:vg fc c e8:=by decide +kernel
lemma fv:FV fc:=gv k8 g
lemma d2:LI fc 2:=l0 fv 3 1 [(4325380,0)] (by decide +kernel)
lemma d1:LI fc 1:=l1 fv d2 3 1 [(131077,2065)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 3 1 [(131076,3089)] (by decide +kernel)
end f5
def e9:=(107,7)::e8
lemma k9:K e9:=kc (fl f5.fv 1052726 (by decide +kernel) f5.d0) k8
def e10:=ps e9 st 42 46
lemma k10:K e10:=ks st 42 46 e9 k9 (by decide +kernel)
namespace f6
def c:=u53 [(11,0x1c000344000008e00018a0000087000095000008380006a0000009000034000000ce0000aa00002040000c4000005200006080000310000244000028800010a0000184000094000009)]
def fc:=mkFD 213 9 20 (ms0 [(69919,4),(140017,4),(282402,4),(586820,4),(1017992,4)]) c #[[],[67],[50],[66,67],[50,67],[66],[33],[33,67],[65,66,67],[65,66],[33,50],[49],[33,50,67],[16],[16,67],[16,50],[16,50,67],[32,33],[32,33,67],[32,33,50],[32,33,50,67],[16,33],[16,33,67],[16,49,50],[16,65,66,67],[32,49],[48,33,50],[48,65,50,67],[32,49,67],[32,49,50],[48,65,66],[32,49,66,67]] #[r0,(1,1,w1 #[6688]),(5,1,w1 #[0x1aa434c85a909520a40]),(15,3,w1 #[0x66512ca2d504aa016532a6a5487b6312a65549ea10d32168414840880]),(15,4,w1 #[0xd4d1b0916456842508599095232801c50a29885213a403440388811101]),(5,4,w1 #[0x11002a405400a04b100])] 5
abbrev p d b x:=verifyMultiBatchP fc d 4 b x=true
lemma g:vg fc c e10:=by decide +kernel
lemma fv:FV fc:=gv k10 g
lemma d5:LI fc 5:=l0 fv 4 1 [(4849668,0)] (by decide +kernel)
lemma b0:p 4 3 [(262148,0xd4c32062303cae4f4041),(655397,0x89e1c1140933351acc22e1b0b46a332109)]:=by decide +kernel
lemma b1:p 4 3 [(4325492,0),(5111941,0)]:=by decide +kernel
lemma d4:LI fc 4:=lc (jc (mb fv d5 b0) (mb fv d5 b1))
lemma b2:p 3 4 [(131076,0x464190c27384e371c2108ec788623304c369ea710f902e112),(262165,0x77ca728b9f25a11a824048103)]:=by decide +kernel
lemma b3:p 3 4 [(655414,0x79ed134e56138a4f288a52acca98a48cc2a92a1a90a090c8390c4c90780b2)]:=by decide +kernel
lemma b4:p 3 4 [(4587653,0),(4718774,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b2) (jc (mb fv d4 b3) (mb fv d4 b4)))
lemma d2:LI fc 2:=l1 fv d3 4 4 [(393221,0xa602788821096183388e40a022090e8308c432021384c1c9050282),(262198,0x76a1385a1304b023c84208952c472ecb72ccac45ea3c3ca363d15a880de16872520c4113fa0b41aa)] (by decide +kernel)
lemma d1:LI fc 1:=l1 fv d2 4 3 [(131077,0x84442088848211984e00f06810041b2141)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 4 1 [(131076,0x3e70c94264460a0c4c811)] (by decide +kernel)
end f6
def e11:=(213,10)::e10
lemma k11:K e11:=kc (fl f6.fv 2 (by decide +kernel) f6.d0) k10
namespace f7
def c:Array Nat:=#[]
def fc:=mkFD 227 6 23 (ms0 [(1403415,3),(406520,5),(5785434,3),(6355043,5),(8356996,7)]) c #[[]] #[r0] 1
lemma g:vg fc c e11:=by decide +kernel
lemma fv:FV fc:=gv k11 g
lemma d0:LI fc 0:=l0 fv 1 1 [(131076,8)] (by decide +kernel)
end f7
def e12:=(227,7)::e11
lemma k12:K e12:=kc (fl f7.fv 1048662 (by decide +kernel) f7.d0) k11
def e13:=ps e12 st 46 63
lemma k13:K e13:=ks st 46 63 e12 k12 (by decide +kernel)
namespace f8
def c:=u53 [(10,0xc028054002000600003e0000013008815002000180000ec000010c00006e0000106028015002000301100a804000180000f4000008c01402a040000600001f000020)]
def fc:=mkFD 63 8 48 (ms0 [(20148266672895,8),(78108528148242,8),(40322310554695,8),(0xb830ff240f24,8),(0xc0ff88b888b8,8),(0xffc0f0c0f0c0,8)]) c #[[]] #[r0] 1
lemma g:vg fc c e13:=by decide +kernel
lemma fv:FV fc:=gv k13 g
lemma d0:LI fc 0:=l0 fv 4 1 [(131077,32)] (by decide +kernel)
end f8
def e14:=(63,9)::e13
lemma k14:K e14:=kc (fl f8.fv 1052722 (by decide +kernel) f8.d0) k13
namespace f9
def c:=u53 [(11,0x1402005400808100000bc000002800005b000004380002a80000510000128000055000009e000020400001500002a280002e00000194008054020080a0000b200000c5040015002008)]
def fc:=mkFD 95 10 42 (ms0 [(148496216447,7),(1146931982226,5),(327158329863,7),(2680881301412,5),(3850425828408,7),(4396981422144,11)]) c #[[],[66],[49],[32],[64,66],[32,49],[32,66],[64],[32,49,66]] #[r0,(6,1,w1 #[0xf511aa23d406a80d201a20]),(50,3,w1 #[0x4328b6412c82d842a8054036ca29944b2886516c425882a885210aa039b1c,0x6a10f2c05d8c3a88b6032c42d484b09b6216a425485b0875036ca29944b29,0xf621ac43d486a90f611ac23d446a89e651aca3d506aa0d611ea23544ea90,897674003]),(132,6,w2 #[#[0x2a8855036c86d843e6c6c716402c2c58c82a01412262cd8c8b1816260a881501,0x3a9496412a9ad4c5b189430ec215045a1954352c46d88cb1196412ca15045,0x1b9917026e80dc11bb217042a0ad894b019622a842d504aa0b6476a8ad515,0x2a905500aa275887b16d4263fb01d401e8175527b083c5811ba037022a4cdcea,0x5b8b55012ca21d4ab80b760aa025d04bb17510ac215403b9995430ca2995f,0x4b1296592cae54cbe6c887b7212c4d441ca9097256c425c84a9195216c465c67,0x16e86d944babff5455fac05f362bb9b2017602ca45c00b2817642ec4dcd1b83fe5917,0x5b89b752aec19d85b20b6512ca2590cbb0b7616e82d944b28b6412c825d21],#[0x4b0996176c4258ab]]),(90,8,w1 #[0x168614c55b093f55072a61ffd04038a192f141a262c5404fd2a1b32d4a801c54e8a0115201,0x28241950b0917022c28dc18a0a14222e645c982a1370628244c4898916436,0xec2254ca7db23b6576c61ff5001b9a899736025e68639e4c84a9195205e0e88dc08b1212053,0x6c04d881ba112026c60dc11b9117602e64dd80bb037236f6a6254c5b19b5329,0x2e845808bb217606ec4dd08ba907426c4cd800bb015002e44d800bb13603f,0x1b1a36286c64d8c9b9a36400c84dd01b291734c]),(25,7,w1 #[0x1a8915326a44d0e8a88af886079a009e2c609940b0a3e2c545031b2815315e5457a181,0x1a9a36062c94d049b0135026a04d009a894]),(5,5,w1 #[0x4a88d08998133166a61])] 4
abbrev p d b x:=verifyMultiBatchP fc d 4 b x=true
lemma g:vg fc c e14:=by decide +kernel
lemma fv:FV fc:=gv k14 g
lemma d6:LI fc 6:=l0 fv 4 1 [(4849668,0)] (by decide +kernel)
lemma b0:p 5 3 [(1179653,0x6ea1ac183ba8684200800141)]:=by decide +kernel
lemma b1:p 5 3 [(4325524,0),(6160549,0)]:=by decide +kernel
lemma d5:LI fc 5:=lc (jc (mb fv d6 b0) (mb fv d6 b1))
lemma b2:p 4 5 [(393220,0x53084241c394640a8102),(917557,0x201071d731c31018c43104e40a410a)]:=by decide +kernel
lemma b3:p 4 5 [(2097318,0x8528c84210848709c5210883210a4190845ac412),(1311142,0x6ea1adc6421104210841d8332)]:=by decide +kernel
lemma b4:p 4 5 [(4981317,0),(8258214,0),(6423702,0)]:=by decide +kernel
lemma d4:LI fc 4:=lc (jc (mb fv d5 b2) (jc (mb fv d5 b3) (mb fv d5 b4)))
set_option maxHeartbeats 0 in
lemma b5:p 3 7 [(1572869,0x608c08a4210a224e7cc20c9544d4a884c8a887e060c4cca9863a2c8c91923121089093480cbc01480ca8ca1a068c41840442848de182a834808a1804),(2097350,0x74a24d01c60ec1cb141d04c91010ca45a770928b48c4a50f0658a4040dac8459c808851821e50c40435610b0c33)]:=by decide +kernel
lemma b6:p 3 7 [(2097606,0xee2f338c6d0dd640e34c88a1e4e70868a48a72c80851448c5020620618310a10618cb824e18d044c),(1180358,0xc185060c1850620549)]:=by decide +kernel
lemma b7:p 3 7 (u16 2098007 [0x842951432908b0ca6238a55d891c21c9211ea1abe190842138137290878ca2abca4a342882,0x14345367214c8c84211053d91a66a694118e0ca8065716ec6467066eb231a19671a714888481cd2]):=by decide +kernel
lemma b8:p 3 7 [(787799,0x11a62852949d314392ea1a93190841580d0a)]:=by decide +kernel
lemma b9:p 3 7 [(4326837,0),(6161862,0),(7472823,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b5) (jc (mb fv d4 b6) (jc (mb fv d4 b7) (jc (mb fv d4 b8) (mb fv d4 b9)))))
set_option maxHeartbeats 0 in
lemma b10:p 2 8 [(131077,0x12f61798bce28),(2097174,0x707204981ce5698e4184c38c6158a04566a752688439235913889244481fa05987f916cc26621b90e042cb2074010a94842830e830180084c404b210a1f3d106083d2481010814ab10e94cf846a25810708a6240b586b629aa2185805)]:=by decide +kernel
set_option maxHeartbeats 0 in
lemma b11:p 2 8 [(1835286,0x58e4f2a11d88a047826362a195109022ab950d0862433951984e6274230919642266061830e1cd10d0515048224290ad555a8a0ac44045522898c84373166281d41188844ce21768b31abc1a5262043289954aea6c22b91b208481a514995ccd8c42314987cc6221a2148b7c312f8c39a08d18626314861440b606bc19d183a085d),(2097655,0x300480241116123a8741cc6a752994608a645231918c662ce44ac281140095c472d20779a489504aa2791298925e573a209444e625212234abd4a2251140c5cb16ef4d22791dc89a62c6871782040e9c4a61762030e984b1163b708d4598b847f23840f8ccc61a30b30fb22d2aef453272528d37620192cc5464931bbca8d3832218e187ab2b6cfc46c70d0e023f292cda530b87a594c)]:=by decide +kernel
lemma b12:p 2 8 [(393975,0x5f64f4b12d09f44b224b7903b547f03199a920490643588a0c184b209a3)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b10) (jc (mb fv d3 b11) (mb fv d3 b12)))
set_option maxHeartbeats 0 in
lemma d1:LI fc 1:=l1 fv d2 4 6 [(786438,0x2e48d3898433163cca4c41b133c6a5110a2e95c8fa30c3636c1d9419b30e6a110b033062843fe54e8c81222c04d09965ac588411835a65912f52847a72e08af12e2b8480ad12c2b04a92b2284a883929251081122a0640680459011af94421848c8212224307cc598a63f5210a21050082496401)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 4 3 [(131077,0xc6c44a4900666482a0c0602241b2181)] (by decide +kernel)
end f9
def e15:=(95,11)::e14
lemma k15:K e15:=kc (fl f9.fv 4146 (by decide +kernel) f9.d0) k14
namespace f10
def c:=u53 [(11,0x1c0001b4000008a008054002040700006e0000014000027800008181100a8004000a002054008040700006700000820000228080051c0001ac0000108000054008042500006a000005)]
def fc:=mkFD 111 9 44 (ms0 [(5588308444351,6),(379843559362,8),(0xa62424fc90f,6),(3863590535620,8),(0xc03fb8a2e28,6),(0xffc0c0c3030,10)]) c #[[],[49],[32],[32,49]] #[r0,(8,1,w1 #[0x3d446a88d311ea035406900d100aa8]),(18,3,w1 #[0x34c4e98af2c655505b18b5312a65544cb0bb633c5900aa115426c845909b13,630516108]),(8,5,w1 #[0x2ec0dd09ba036226e8ef6c67e2c30e2848])] 2
abbrev p d b x:=verifyMultiBatchP fc d 4 b x=true
lemma g:vg fc c e15:=by decide +kernel
lemma fv:FV fc:=gv k15 g
lemma b0:p 3 1 [(131077,16),(131094,16)]:=by decide +kernel
lemma b1:p 3 1 [(4980774,0)]:=by decide +kernel
lemma d3:LI fc 3:=let h:=lz fc 4 (by decide);lc (jc (mb fv h b0) (mb fv h b1))
lemma b2:p 2 3 [(786437,0x211008808),(1048678,0x840c5030c1fc94880a042)]:=by decide +kernel
lemma b3:p 2 3 [(393447,0x22325c07082b04a)]:=by decide +kernel
lemma b4:p 2 3 [(4325654,0)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b2) (jc (mb fv d3 b3) (mb fv d3 b4)))
lemma d1:LI fc 1:=l1 fv d2 4 5 [(131077,0x24b23444c436a0),(917526,0x9432c6828b85f7244847b511c644211201)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 4 3 [(131077,0x2eb491e30a2f4201)] (by decide +kernel)
end f10
def e16:=(111,10)::e15
lemma k16:K e16:=kc (fl f10.fv 1052722 (by decide +kernel) f10.d0) k15
namespace f11
def c:=u53 [(8,0x380002a8000091c0001cc000010e0000ec00000260000370000203800033800004100001c800001500040aa0200004000066000009)]
def fc:=mkFD 119 9 44 (ms0 [(2287150088959,8),(1493617000202,6),(4814847067155,8),(0x9823fcb082c,8),(0xe03ec2c2fb0,4),(0xffc303030c0,10)]) c #[[],[50],[32],[48,50],[32,50]] #[r0,(3,1,w1 #[0x7a80d501a40]),(17,2,w1 #[0x4b19fd886b10d523cca35947a98d533cb11b6216a42548db28b630aa014c0,9620]),(31,5,w1 #[0xb5212a41d84daa09640717026e045c1aa91963968425082a095420714122420,0x1b1037342ec4dcc9b1817602ca4dd80b2817636c6ad4cba90b5376c41]),(11,5,w1 #[0x35226c08d0a5a08b3112622544d9909520716162622]),(1,4,w1 #[13073])] 3
abbrev p d b x:=verifyMultiBatchP fc d 3 b x=true
lemma g:vg fc c e16:=by decide +kernel
lemma fv:FV fc:=gv k16 g
lemma d5:LI fc 5:=l0 fv 3 1 [(4325380,0)] (by decide +kernel)
lemma b0:p 4 1 [(262149,67601)]:=by decide +kernel
lemma b1:p 4 1 [(5373989,0)]:=by decide +kernel
lemma d4:LI fc 4:=lc (jc (mb fv d5 b0) (mb fv d5 b1))
lemma b2:p 3 4 [(262149,0x23a21498c8d0a0924311),(1179686,0x4241190884642a12a01c8528429070102)]:=by decide +kernel
lemma b3:p 3 4 [(6815926,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b2) (mb fv d4 b3))
lemma b4:p 2 5 [(1048582,0x1b306641c819608a528522d62b31124447901035b08a44c25908e452c802),(917639,0xfb2b4e4871bc0d4f1a1ce48a192246f0352a210a72ae48a1c8b42209e4554342)]:=by decide +kernel
lemma b5:p 2 5 [(4456694,0)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b4) (mb fv d3 b5))
lemma d1:LI fc 1:=l1 fv d2 3 5 [(393222,0x8f0542b25258424e23134a045261119041b92050050d101)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 3 2 [(131077,0x8a149160869061)] (by decide +kernel)
end f11
def e17:=(119,10)::e16
lemma k17:K e17:=kc (fl f11.fv 1048658 (by decide +kernel) f11.d0) k16
namespace f12
def c:=u53 [(10,0xe00019400000a80000cd00000240000478000081c000314000029000009e000040500008e000011280006600000194000138000084a00011a000024500004d000022)]
def fc:=mkFD 207 10 38 (ms0 [(37116517471,5),(11834461154,5),(81763925127,5),(120494985444,5),(137975046408,9),(274610012688,9)]) c #[[],[84],[49],[49,84],[16,50],[16,50,84],[48,49,50],[32],[32,84],[32,49],[16,33,50],[16,33,50,84]] #[r0,(3,1,w1 #[0x6aa0d401a20]),(16,2,w1 #[0x1ec03580eb28d611aa275906aa1ed80db289650aa82d842a8051032c82d90]),(50,4,w1 #[0x6e40dc10aa216406ed1d80aaa1b502a8025905b2054316a86d94cb2871433,0x12a8659479b13797156e2e5945ba95700ac81dd823b4f611ac2f5906aa17372e,0x16c22584cb0a5700cec25d94bb0b760cec15da6a8ad503f2c21580cb0b9654,1527363358]),(31,6,w1 #[0xa1837326e00dc5cb0155037e9801c1948aa217286ec8ff501aa0071432264450c6,0x37306c205800a0116126ca85800980365628009d89b8014126e00dcd3]),(7,5,w1 #[0x26502c404c1098813066c43e2c28]),(1,3,w1 #[2304])] 4
abbrev p d b x:=verifyMultiBatchP fc d 4 b x=true
lemma g:vg fc c e17:=by decide +kernel
lemma fv:FV fc:=gv k17 g
lemma d6:LI fc 6:=l0 fv 4 1 [(4325380,0)] (by decide +kernel)
lemma b0:p 5 1 [(131077,2148369)]:=by decide +kernel
lemma b1:p 5 1 [(4980757,0)]:=by decide +kernel
lemma d5:LI fc 5:=lc (jc (mb fv d6 b0) (mb fv d6 b1))
lemma b2:p 4 3 [(393221,131872),(786486,0x5064284513124908441c1)]:=by decide +kernel
lemma b3:p 4 3 [(7078038,0)]:=by decide +kernel
lemma d4:LI fc 4:=lc (jc (mb fv d5 b2) (mb fv d5 b3))
lemma b4:p 3 5 [(131077,0x82221083308c920082224c010849103640a421a),(2097174,0xc1ca4291672ca0854a501526a28020143060e21a0880c504250c4044128302)]:=by decide +kernel
lemma b5:p 3 5 [(1573143,0x2d8d25b4a538b252e54e138e82b8c94f13ca9b668b2a6898a6d2a10642155454556948328d172a1049b042a)]:=by decide +kernel
lemma b6:p 3 5 [(4325845,0),(4981222,128),(6029895,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b4) (jc (mb fv d4 b5) (mb fv d4 b6)))
set_option maxHeartbeats 0 in
lemma d2:LI fc 2:=l1 fv d3 4 6 [(1179654,0x9642c919c386484819c81c9993604422844c849252184348264a40ca31883484188412430c22052086a90a628610c715428852912e8889603),(917655,0x2b62944588e131a5f6528a22f528850456c3cd8ac13024c4bc97593a26a4d09918c87aa891b2544b488b430b7a347556aa9562867a69aea4849252f5f8825c4621843ea1102084a919310a8c5b)] (by decide +kernel)
lemma d1:LI fc 1:=l1 fv d2 4 4 [(393222,0x2d5cd3e914ea35968aef743b9cd0572ca51e88472194a85648949233f28910984125909a52100a842a241089e4801)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 4 2 [(131077,0x2cd182e642942c0490a9061)] (by decide +kernel)
end f12
def e18:=(207,11)::e17
lemma k18:K e18:=kc (fl f12.fv 4146 (by decide +kernel) f12.d0) k17
def e19:=ps e18 st 63 64
lemma k19:K e19:=ks st 63 64 e18 k18 (by decide +kernel)
namespace f13
def c:=u53 [(7,0x20000394000008e0001cc00000280000a700001040000638000041c00038c000010e0000ce00004050000e2000005)]
def fc:=mkFD 231 9 40 (ms0 [(74243928255,6),(23716442050,6),(163579162887,6),(790680651220,4),(825703368216,8),(0xffe0220820,10)]) c #[[],[32]] #[r0,(2,1,w1 #[223353408]),(4,1,w1 #[0x25885b109520a41]),(1,2,w1 #[1284])] 1
abbrev p d b x:=verifyMultiBatchP fc d 3 b x=true
lemma g:vg fc c e19:=by decide +kernel
lemma fv:FV fc:=gv k19 g
lemma d3:LI fc 3:=l0 fv 3 1 [(131077,16)] (by decide +kernel)
lemma b0:p 2 1 [(393222,1636174865)]:=by decide +kernel
lemma b1:p 2 1 [(4325430,0)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b0) (mb fv d3 b1))
lemma d1:LI fc 1:=l1 fv d2 3 2 [(262150,4236480641)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 3 1 [(131077,2672673)] (by decide +kernel)
end f13
def e20:=(231,10)::e19
lemma k20:K e20:=kc (fl f13.fv 1048658 (by decide +kernel) f13.d0) k19
namespace f14
def c:=u53 [(9,0x80000ab00001038000748000012000032c00002100001d400000270000e300000428200150008101c0001ac000080a0001c200000c50000e8000003)]
def fc:=mkFD 235 9 38 (ms0 [(45857646679,3),(3246788600,7),(12987268120,7),(189116887394,5),(206691156355,7),(274611634692,9)]) c #[[],[33]] #[r0,(3,1,w1 #[0x6a88d210a20]),(8,2,w1 #[0x4b10b6212a414856a08b5112a21500]),(3,3,w1 #[0x2824500aa02])] 1
abbrev p d b x:=verifyMultiBatchP fc d 4 b x=true
lemma g:vg fc c e20:=by decide +kernel
lemma fv:FV fc:=gv k20 g
lemma d3:LI fc 3:=l0 fv 4 1 [(393221,66336)] (by decide +kernel)
lemma b0:p 2 2 [(393221,0x8294a1821),(524342,0x1d64e1831049)]:=by decide +kernel
lemma b1:p 2 2 [(4325494,0)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b0) (mb fv d3 b1))
lemma d1:LI fc 1:=l1 fv d2 4 3 [(131077,16641),(262166,0x22650ff26892121)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 4 2 [(131077,176328801)] (by decide +kernel)
end f14
def e21:=(235,10)::e20
lemma k21:K e21:=kc (fl f14.fv 1052726 (by decide +kernel) f14.d0) k20
def e22:=ps e21 st 64 78
lemma k22:K e22:=ks st 64 78 e21 k21 (by decide +kernel)
namespace f15
def c:=u53 [(16,0x380002a8100052c00017c00008140000fc000002400002a010045500003d800002280001f400000940000de0000205020015002048281000a804021240000fc000100a020054008082501002a001044282001500080a280001dc000020e0000f400000a700007c000003),(9,0x400001502004a2800815002028141000a8010044e0000dc000022700006b000014380003c8000031c0001d800002480000540000aa700007300000c)]
def fc:=mkFD 127 12 72 (ms0 [(0x211448530884708bff,10),(0x8591c0a03c12ffc12,10),(0x426090ac113ff11047,10),(0x1382e030ffc2403c24,10),(0x9c0303ff220b8220b8,10),(0xe003fec0bc2c0bc2c0,8),(0xfffc0300c0300c0300,14)]) c #[[],[66],[49],[49,66],[32],[64,66],[32,49],[64,49,66],[32,66],[64],[32,49,66]] #[r0,(8,1,w1 #[0x3d846b08d311ec035806900d100aca]),(73,3,w1 #[0x5bb097612e42dcc4b98b720a60158429085603ec038ba816522ca4dd48bac,0x97112e46dc82b2896216c42dc4cbb0b7616e215945ba09740a801580ab29,0x7b18d631ae43d886b10d421a647cb8097336e615944b18b6316e055844bb5,0xf711ae235c86b11e761aec35d07b20d641ae23d846b08d313cec35d86b99,0x7b98d731ac63dc06b80d603ac074c4fb93]),(231,7,w2 #[#[0x95116a22dc83b8096216c46d884b94f503a84038a921e6e984c48a891e2a823cb281,0x55416c425885b88b6112c265cc5b289750aa82d8cdb089610a2015502a806,0x97212ec65d85b90b7632e615944bb09742a2025d45b2855036a425483b808,0x7710aa895944b989722ee22dcc5b907700aca65d85bb0b7412e815945b98d,0x97612e21d90dbb0b710aca6d942a9855412ea6d4c2a8896316e62d8c4a991,0xb7412c82d90cba097132e625d84ba05650ac05dd85b2847612ca65042b294,0x56516c825c45ba17702ec42d914b909730ac22dc82b2977416e211d03b918,0x55236e01dccdb9852112e42dc84b9853136e225904ba054212422dd0cba1d],#[0x3804303861cdb905300a4025cc5b99b7032e09d8d5b9856512e425ccbb921,0x165230a061c0c013800709461c0c2816522ca0e1c9c291800302061c9c0b1,0x6b12d635ee23484e991f721a421b9c0916522ca45949c3837587004e101c03d,0x16e815805b19b7416ec15802b0b3f3082dd85ba098653f508e989efa4035436a10c,0x97612c415845c10b6273066dcc5c1b981b706660cab2896316ec25d85c1b4,0x358a17d31bb06358c7c19d761cec3d906b233f3046e085b91963170425885b9c3,0x4ba198612ec25d19f97627fe086c142]]),(139,8,w2 #[#[0x2a985450b8a8b1106282c50d8a931541ae2a245010a18871768a64254cca10b4202,0x2a573c4c4898815442c045848aa115262a353c4827f8a9b9f15180c6c1c5455b898914148,0xaa0654ac7e901d209bfa633485cf8b2916522ca85968a966f16562ca45440aa4151ba,0x722c64767db9896336c7558733db9095292a62d4c2a885502f04154b4b21553b2,0x7088e02c3caa4b736046c2cdd21ba4cf3617de6e0e7cdd28a8016566ca95cdd0d78b08390df,0x16c76dccdba198516ca6e0ac79b2a37526cb97c5941c2537526ea4dd31c01385b3,0x70bafedd14bb1b7497072d904b23b7612edad8c4b1897517066d944b18965b9,0x2ec458c9c283942330065c1c2938503300dd00bb01972320065c1cb8176d7],#[0xdd4090016203044dd41ca137502ec4e549c19376dc]]),(40,8,w1 #[0x12c62d0cdb08ef35346c43dcd405788820f15222a24480e3a90153032623bf486e880871311c,0x2c8c5501aa137526e606059c2138427004e101b8157b6216842508ca10b421f,0x6c80dc49b91ff18106c84d4c1b2136335]),(4,6,w1 #[0x6e60d409b903c4804])] 4
abbrev p d b x:=verifyMultiBatchP fc d 5 b x=true
lemma g:vg fc c e22:=by decide +kernel
lemma fv:FV fc:=gv k22 g
lemma b0:p 6 1 [(131078,16)]:=by decide +kernel
lemma b1:p 6 1 [(4587542,0)]:=by decide +kernel
lemma d6:LI fc 6:=let h:=lz fc 7 (by decide);lc (jc (mb fv h b0) (mb fv h b1))
lemma b2:p 5 2 [(131078,16),(1179671,0x84414190a0c8487386e15081)]:=by decide +kernel
lemma b3:p 5 2 [(4325541,0),(4456630,0),(7733463,0)]:=by decide +kernel
lemma d5:LI fc 5:=lc (jc (mb fv d6 b2) (mb fv d6 b3))
lemma b4:p 4 6 [(2097158,0xc08884210442100c020052061428),(917766,0x841011012025040a)]:=by decide +kernel
lemma b5:p 4 6 [(2097527,0x4917a308813c219a42247bf24e84c8851121d1028d2d28e11c86a0d1046a409f10e422108421458618203),(393847,33296)]:=by decide +kernel
lemma b6:p 4 6 [(2097832,0x84124804a5b83520865248494a349290a32062942194184854dc1a8b10a50e2948441421920a8432),(1049512,0x21104490328e3410728442)]:=by decide +kernel
lemma b7:p 4 6 [(5637158,0),(5899479,0),(8258984,0),(6555544,0)]:=by decide +kernel
lemma d4:LI fc 4:=lc (jc (mb fv d5 b4) (jc (mb fv d5 b5) (jc (mb fv d5 b6) (mb fv d5 b7))))
lemma b8:p 3 8 [(786438,0x84c7e01280950f887da946187118ec79422802108880883b148744a0f20407283c41e412203cd2330d8442843220d1043c5062001),(2097255,0x842120a3142c6e0f1783250841123621b2a1080c82021)]:=by decide +kernel
lemma b9:p 3 8 (u16 2097511 [0x2108484c6a310b10d0861a2920a31429090d8d1508210842041,0x4220a10321082908421084202841062]):=by decide +kernel
lemma b10:p 3 8 (u16 2098023 [0x5166d2153a45a45352112520220128a0e8b0028b37100a83d020940716909084e8420a98342129834020871,0x24908485410598320e464232a52a8850454a923a11608e906863044141cc10045481c708387281083ca18886187a]):=by decide +kernel
lemma b11:p 3 8 (u16 2098535 [0x2103152a268133834b18a061e80f2860c0884220841891,0x11598951494304840a0e4c4262a0110506161c314848a530a40a3825408ab]):=by decide +kernel
lemma b12:p 3 8 (u16 2099047 [0x29019093351988cce52599409504aa3211935080c2884406210290095a,0x406421084208842104420]):=by decide +kernel
lemma b13:p 3 8 [(2099559,0x24d568a4860a22612b08862820640b401a1080c840a410a47088e2071282a4845808b3),(395879,0x2913f51f88fd29298508a604e82780ca065e2ca24f14114089d618)]:=by decide +kernel
lemma b14:p 3 8 (u16 2099864 [0x8421256a772a4a94e852b9896c4e642f1182d2b92f29050a42108420ab4227085c40bc,0x97b9f150849255a428214a5fa3f2e41711f9680c2cc1b9c90fd0727142d9268542030773c490d1460949a4bd06882f4a1abe2a9106430fc]):=by decide +kernel
set_option maxHeartbeats 0 in
lemma b15:p 3 8 [(1838232,0x8214f2ff259c08f04fe2387a5b67454c1d0644749ed9e773911e899c4762398a05c44810dca7013828dd1102378a4eac1419a08e84c024111a448874840286a3113a88d8e82206d81ab8874292c),(1445241,0x130f402bcc1c9a91050807224fc69329c10fd07094c0ccca92c41615e60e4b487c82d3a4da85722a41b40ae054d5b835379841950e6837418356e0e38de21f2)]:=by decide +kernel
lemma b16:p 3 8 [(4328999,0),(4722232,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b8) (jc (mb fv d4 b9) (jc (mb fv d4 b10) (jc (mb fv d4 b11) (jc (mb fv d4 b12) (jc (mb fv d4 b13) (jc (mb fv d4 b14) (jc (mb fv d4 b15) (mb fv d4 b16)))))))))
set_option maxHeartbeats 0 in
lemma b17:p 2 8 [(655366,0x330a9814c1d32ea9714b9d34fa6cb40614f0a6453a29952d0014008a5b29a3ca401e146807451aa50529122040c0802),(2097239,0x6ff794122712fc8a28417a4ca8704322590c9086d1449224625889212946ab44f7dba22b104c97ca489a4f66d2998c7e03168888a4462216b8b91dbc624823b15b8861e2cb66a23811ad2d596b01740b909662e363513a5c204e032d48f42845e2af4a6363b0b1160a3483ad16371415b085528424212908cc4c4261133458bc42462ad10e085c43621a1564c58949903081740aa06502482688b2510a084c41c20f1548849e2d56d625510408256183c4554a57e10180c)]:=by decide +kernel
set_option maxHeartbeats 0 in
lemma b18:p 2 8 [(2097495,0x105e1c86842ac361092160428211619086e9bd912af604482215eb532b37d10a5450501c40e3c58ef377301d866a07519aab915ccd25bcf83f40b619e87e416a33c8fb30c4f227a13d9d2f447623d11c92960b2f4b9826923291b49a48a0121552df52cfd926da59f4444de25214f919086c4a511f104443e9ce8143d0d2a5e12f290181e80f435090081f94e5c394ea26e12e891481cf4d24e84ca268206ad2a5e29af048c4435260a9190c0246a8b9daa70b774922d93090931442b0d2a14aabcc72fc4cb4fa8e457218925c98849641f211c43e8159e8a41023),(524887,0xcc8a3053228a4a6278b087844d23910e889562b23858a48eba5f709d0e0421210d0d0254221110c8d05600b0369839b697891f841c0da14a88341b229558901f40f8b103fe83c31)]:=by decide +kernel
set_option maxHeartbeats 0 in
lemma b19:p 2 8 (u16 2097816 [0x2bb4dec5160e9006a5a49cd08b0b4839dd3c55eebd1a8148836410d08c8404245d098a25ea228e935f2c6b73b145f22c5e98def6c89728ba45935084248891248b38b2ddaeba43252420ad455c41da5632b084791490e43d21ed0e49166bb5d7c5e1e865409b2a502531665b8d84654a2b1759a965bb2d596ccb86563aad9522ab413109b2289c63eba56a6c6c,0x5f70b80edab6c5b6d4beea3baadd16ead2ffd3ee434c9508d356e0b722937900b5a1a88d4856a2b5e2d9a6e2d516a245e7f06cdcdd16fa202d21608b4457d7496f9217ba1708b305c02e41658b7c59c4cd56b8aeba97883eceee2b386591dd196ad89a582d5e19fa52750c26492a9293a1a583c0573073a3dfd05109a28a06a76498e89c3a769136573070826f218e7cd3]):=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b17) (jc (mb fv d3 b18) (mb fv d3 b19)))
set_option maxHeartbeats 0 in
lemma d1:LI fc 1:=l1 fv d2 5 7 [(131078,0x1074b05392b2100b03840644a40542080a838a2ac2102082022a42029f40429),(917527,0x5ac14111d17a1429ab1789a917cd282863ad22211608a11203a10e8b911508911103910d4d18ba0210204d08b85be9178367017083084442816882884a662679411e81a21fa2c41a53862c82c42c9a4c4761e148c30a008e89e88c08d09e08d91f90c91f107121d15a9bb15c15a158889030cfd2348588d88348d48d28a904504a0aaa821425a21a25825625220ef487f861402)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 5 3 [(131078,0x109064e4d428886a4c302822443b4201)] (by decide +kernel)
end f15
def e23:=(127,13)::e22
lemma k23:K e23:=kc (fl f15.fv 1052722 (by decide +kernel) f15.d0) k22
namespace f16
def c:=u53 [(6,0x1600017a000004b0000bb000004580005f000000ac0002bc000041600013e000040b0000b7000008)]
def fc:=mkFD 191 12 69 (ms0 [(0x411424531111c45ff,9),(0x8588e0a0784bfe12,9),(0x826048ac227fc8847,9),(0x13817030ff8901e24,9),(0x11c0181ff442e110b8,9),(0x1e003fec078301e0c0,9),(0x1fffe0100804020100,15)]) c #[[]] #[r0] 1
lemma g:vg fc c e23:=by decide +kernel
lemma fv:FV fc:=gv k23 g
lemma d0:LI fc 0:=l0 fv 3 1 [(131078,16)] (by decide +kernel)
end f16
def e24:=(191,13)::e23
lemma k24:K e24:=kc (fl f16.fv 1052722 (by decide +kernel) f16.d0) k23
namespace f17
def c:=u53 [(16,0x58000578000102c00033c000040a08005400208880000e500000a5000077000000941000a801010540001d6000008a0000ed0000025000073800004280001bc000100e0001d8000006700006d0000423800037000020a00003a8000014800008a0000b450000e8000007),(8,0x28000720000059c00019c000120e0000d600008870000e90000063800073000004940001a8000114e0001c60000185002045010048)]
def fc:=mkFD 239 12 63 (ms0 [(0x914a292090f097f,7),(0x580b070382ff82,9),(0x12614c24127f120f,7),(0x3807038ff840384,9),(0x5c01807f5c285c28,7),(0x6003ff8060306030,11),(0x7ffe004080408040,13)]) c #[[],[49],[32],[32,49]] #[r0,(5,1,w1 #[0x1ac234c46b00d201a20]),(33,3,w1 #[0x53156e425885b8852032ec6dd84bb0b7312e62dc84b905610a4215802980,0x6b82d721ae234c4eb08d313aec35cc6b18d721ac434c87b7312c62dc04b9c,27548]),(84,6,w1 #[0x12e6a5d45b29b6212c42d844b089510a206d944ba85500a200737422a50544b,0x4b91b7216e655844bb097236e42dd82b0953212e615844bb1b7316ec15844,0xc381614700061d4b829720a4225ccdb8077452e2a5cc298097256e265cc9,0xac26e0d29089820d0e24c82c02b739a65b4816991f737ac6758de9083ce120,0x1b06df91032e6258c5c189720a622e08290898357066dc84b1158712c62e0db,0x1a6566184bb35f4c5e]),(46,7,w1 #[0x15182c245465b109725bedcd2f9524ac215834a88ce2a44dc0b71512280c50488803,0xe126f3848de5d8973745fc5c75b8996332a51f9b9b37202a4ce0637152830c45448a839,0x30e0e50dc0a96212e424c9cb0897132e66e085b909628fcdcc9b9cd]),(7,6,w1 #[0x37366c4e5044a88b5157db087c5944])] 2
abbrev p d b x:=verifyMultiBatchP fc d 5 b x=true
lemma g:vg fc c e24:=by decide +kernel
lemma fv:FV fc:=gv k24 g
lemma b0:p 5 1 [(131077,16),(131094,16)]:=by decide +kernel
lemma b1:p 5 1 [(131111,16)]:=by decide +kernel
lemma b2:p 5 1 [(4718647,0)]:=by decide +kernel
lemma d5:LI fc 5:=let h:=lz fc 6 (by decide);lc (jc (mb fv h b0) (jc (mb fv h b1) (mb fv h b2)))
lemma b3:p 4 3 [(786438,0x8221084081),(2097255,0x20ad32a03210842084221246440d1)]:=by decide +kernel
lemma b4:p 4 3 [(262503,800),(524680,0x250ca86440a9)]:=by decide +kernel
lemma b5:p 4 3 [(4325830,0),(4850135,0),(5767720,0)]:=by decide +kernel
lemma d4:LI fc 4:=lc (jc (mb fv d5 b3) (jc (mb fv d5 b4) (mb fv d5 b5)))
lemma b6:p 3 6 [(393222,0x316ad3cac162a957a439e833a0),(2097207,0x838d096e44e3a084221091e195234d847420844202e8630803)]:=by decide +kernel
lemma b7:p 3 6 [(2097463,0x40222082850a21088210310248422),(1835575,0x17f0c7e429145164cea3420c61e288088422081e2c644202e0652)]:=by decide +kernel
lemma b8:p 3 6 [(2097944,0x4cc3410880c1926462a1084149190520e69),(1836056,0x16e44540766ad848245c15eb1c50616d0d08411278d02e99d4d528e5a1cf0ea2)]:=by decide +kernel
lemma b9:p 3 6 [(263417,0x4205602da)]:=by decide +kernel
lemma b10:p 3 6 [(4457752,0),(4326713,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b6) (jc (mb fv d4 b7) (jc (mb fv d4 b8) (jc (mb fv d4 b9) (mb fv d4 b10)))))
set_option maxHeartbeats 0 in
lemma b11:p 2 7 [(2097159,0x97c9bf85e495a6224b96c5a94c38088c2208421a8489424a95890a587163618a95f599e41c82ad2e230a95f1f168ba5228695913049d33a725eba3a5242122991f3aba5ec3c1c1b0740f01bd215232a20c82a0881a506631830803),(524551,0x3022b2a40e660d76992665d172989755095f13c5e71416e3260413)]:=by decide +kernel
lemma b12:p 2 7 [(1704264,0xc6cdcf91a4d939a9849c945212bf43462ed96959a5217e992d23ed93f8d9284259d942a8c8be6e823c525e474441398c0ed48fbcb5ba96b1cd73ccc73a80f1640f68e381562)]:=by decide +kernel
lemma d2:LI fc 2:=lc (jc (mb fv d3 b11) (mb fv d3 b12))
lemma d1:LI fc 1:=l1 fv d2 5 6 [(655367,0x122dc388c7e119781a5e69427c6b9691f068e452548828c4ea232b1540cd224b4226e16b424201)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 5 3 [(131078,0x29161020b4141)] (by decide +kernel)
end f17
def e25:=(239,13)::e24
lemma k25:K e25:=kc (fl f17.fv 1052722 (by decide +kernel) f17.d0) k24
namespace f18
def c:=u53 [(14,0x160001ea000004b0000b70000205000079800002280003d800000560001ae000020a0000e7000008500003b8000201c0003c8000014e0000ec000082700007300004438000730000049c00019c000120e0001c600001850000e200000d)]
def fc:=mkFD 247 12 63 (ms0 [(0x4144288261305ff,9),(96874929022762506,7),(0x8608c1059ff0813,9),(0x11813023fe2c102c,9),(0x5e01c07d60b05eb0,5),(0x6003ff8180c060c0,11),(0x7ffe004201008100,13)]) c #[[],[50],[32],[48,50],[32,50],[48]] #[r0,(2,1,w1 #[224401984]),(12,1,w1 #[0x6b91d761ae6358dedc84b11b7612ec2dcc4b985600a60]),(32,4,w1 #[0x2ec658c4b9a97336e665d8dbb1b7216c425884a91b6512ea154838a891210,0x30f1ee0c4b98963370625cd5c38687130e161c2bb05730b011f5c86b11d650]),(27,5,w1 #[0x38147050eaa415c5aaa05713aa23504ea1838a89151624285500a0994132a60,0x37366e646008c3818603078e6e74e009c1a16522e33])] 3
abbrev p d b x:=verifyMultiBatchP fc d 4 b x=true
lemma g:vg fc c e25:=by decide +kernel
lemma fv:FV fc:=gv k25 g
lemma b0:p 4 1 [(917510,0x210840a420),(1835127,0x41081832102850a148420)]:=by decide +kernel
lemma b1:p 4 1 [(4981079,0)]:=by decide +kernel
lemma d4:LI fc 4:=let h:=lz fc 5 (by decide);lc (jc (mb fv h b0) (mb fv h b1))
lemma b2:p 3 5 [(262150,0x4d2a1912c321b5246231d004423901e819c202),(1835047,0x4683286461a1040c4421212095082c3411c5240432868018a228512)]:=by decide +kernel
lemma b3:p 3 5 [(1966344,0x3ad09e714b4d02874c24945e6e471c5c462ee982a11263142e35a2ce2da8d28a8c45145a594516da0a95ce514d71)]:=by decide +kernel
lemma b4:p 3 5 [(4325879,0)]:=by decide +kernel
lemma d3:LI fc 3:=lc (jc (mb fv d4 b2) (jc (mb fv d4 b3) (mb fv d4 b4)))
lemma d2:LI fc 2:=l1 fv d3 4 5 [(1048583,0x481a42ce6e33c9c5c27b148b34910852fef6190d22ce87297f34190c916361150885021909281c0f02),(524424,0xd669948e2efae09048bbf5a62915a472c50649a0d0a8288a6cc17a)] (by decide +kernel)
lemma d1:LI fc 1:=l1 fv d2 4 4 [(262151,0x148939592133410c510500a4601)] (by decide +kernel)
lemma d0:LI fc 0:=l1 fv d1 4 1 [(131078,0x452c224821)] (by decide +kernel)
end f18
def e26:=(247,13)::e25
lemma k26:K e26:=kc (fl f18.fv 1048658 (by decide +kernel) f18.d0) k25
def e27:=ps e26 st 78 81
lemma k27:K e27:=ks st 78 81 e26 k26 (by decide +kernel)
namespace f19
def c:=u53 [(7,0x340003f4000009a0001fc000002d0000fb000004680007b800004340003bc000041a00017e000080d00007f000080)]
def fc:=mkFD 255 14 17 (ms0 [(19043,2),(17245,2),(37051,2),(35272,3),(67344,2),(70822,0),(15364,3),(122880,3)]) c #[[]] #[r0] 1
lemma g:vg fc c e27:=by decide +kernel
lemma fv:FV fc:=gv k27 g
lemma d0:LI fc 0:=l0 fv 3 1 [(131079,16)] (by decide +kernel)
end f19
def e28:=(255,15)::e27
lemma k28:K e28:=kc (fl f19.fv 1052722 (by decide +kernel) f19.d0) k27
theorem top_lb:Face 255 15:=k28 (255,15) (by decide +kernel)
end Cert
end PEqualNP.Outside.L_meta_52834
theorem PEqualNP.Outside.L_meta_52834 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_52834.Engine.oneNot_combine_52834 PEqualNP.Outside.L_meta_52834.Cert.top_lb
