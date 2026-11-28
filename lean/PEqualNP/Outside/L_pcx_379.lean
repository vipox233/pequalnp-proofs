import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_379_aux
abbrev Zx:=@Fin.ext
abbrev Zc:=@Finset.sum_congr
abbrev Zm:=@Nat.mod_eq_of_lt
abbrev Zt:=@List.take_succ_eq_append_getElem
abbrev Zg:=@List.getElem_finRange
abbrev Zk:=@List.take_of_length_le
abbrev Za:=@List.map_append
abbrev Zl:=@List.foldl_append
abbrev Zo:=@List.foldl_cons
abbrev Zi:=@List.foldl_nil
abbrev Zn:=@List.take_zero
abbrev Zs:=@List.sum_append
abbrev Zp:=@Bool.toNat_false
abbrev Zq:=@Nat.add_zero
abbrev Zw:=@Nat.mul_le_mul_right
abbrev Zu:=@Finset.mem_univ
abbrev Zv:=@Finset.mem_filter
abbrev Zy:=@List.map_replicate
abbrev Zz:=@List.sum_replicate
abbrev Ze:=@Bool.false_eq_true
abbrev Zd:=@dite_true
abbrev Zf:=@dite_false
abbrev Zh:=@ite_true
abbrev Zj:=@ite_false
abbrev Zr:=@dif_pos
abbrev Zb:=@dif_neg
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
def b6 (g:Gate):Prop :=
 ((g.op=.and\/g.op=.or)/\g.inputs.length=2) \/
  (g.op=.not/\g.inputs.length=1)
def xu (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
lemma j4 (g:Gate) (gs:List Gate) (w:List Bool) :
  xu (g :: gs) w=xu gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) :=
 rfl
lemma kn (gs₁ gs₂:List Gate) (w:List Bool) :
  xu (gs₁++gs₂) w=xu gs₂ (xu gs₁ w) :=
 Zl
lemma ko (gs:List Gate) (w:List Bool) :
  (xu gs w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp [xu]
 | cons g gs ih =>
  rw [j4,ih,List.length_append,List.length_singleton,List.length_cons];omega
lemma b7 (w:List Bool) (b:Bool) (i:ℕ) :
   (w++[b]).getD i false=if i=w.length then b else w.getD i false:=by
 split_ifs with h
 . subst h;simp
 . by_cases hlt:i< w.length
   . rw [List.getD_append _ _ _ _ hlt]
   . rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
lemma vd (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i< w.length) :
  (xu gs w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih =>
  rw [j4,ih _ (by simp;omega),b7,ite_eq_right_iff.mpr (by omega)]
def xa (φ:ℕ->ℕ) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map φ⟩
lemma kp (φ:ℕ->ℕ) (g:Gate) (hg:b6 g) :
   b6 (xa φ g):=by
 rcases hg with ⟨hop,hlen⟩ | ⟨hop,hlen⟩
 . left;exact ⟨hop,by simp [xa,hlen]⟩
 . right;exact ⟨hop,by simp [xa,hlen]⟩
lemma kt (φ:ℕ->ℕ) (gs:List Gate) (w₁ w₂:List Bool)
  (hrb:∀ j< gs.length,∀ i ∈ (gs.getD j ⟨.or,[]⟩).inputs,i< w₁.length+j)
  (hφ_lt:∀ i< w₁.length,φ i< w₂.length)
  (hφ_shift:∀ k,φ (w₁.length+k)=w₂.length+k)
  (hφ_init:∀ i< w₁.length,w₂.getD (φ i) false=w₁.getD i false) :
  ∀ i< w₁.length+gs.length,
    (xu (gs.map (xa φ)) w₂).getD (φ i) false =
    (xu gs w₁).getD i false:=by
 induction gs generalizing w₁ w₂ with
 | nil =>
  intro i hi;simpa [xu] using hφ_init i (by simpa using hi)
 | cons g gs ih =>
  intro i hi;rw [List.map_cons,j4,j4]
  have hg_lt:∀ j ∈ g.inputs,j< w₁.length:=by
    intro j hj;have:=hrb 0 (by simp) j (by simpa using hj);omega
  have hbit :
      (xa φ g).op.eval ((xa φ g).inputs.map fun j=>w₂.getD j false) =
      g.op.eval (g.inputs.map fun j=>w₁.getD j false):=by
    simp only [xa,List.map_map];congr 1;apply List.map_congr_left;intro j hj;exact hφ_init j (hg_lt j hj)
  rw [hbit];set b:=g.op.eval (g.inputs.map fun j=>w₁.getD j false);apply ih (w₁++[b]) (w₂++[b])
  . intro j hj x hx;have:=hrb (j+1) (by simp;omega) x (by simpa using hx);simp only [List.length_append,List.length_singleton];omega
  . intro j hj;simp only [List.length_append,List.length_singleton] at hj ⊢
    by_cases hlt:j< w₁.length
    . have:=hφ_lt j hlt;omega
    . have heq:j=w₁.length:=by omega
      rw [heq,show φ w₁.length=w₂.length by simpa using hφ_shift 0];omega
  . intro k;simp only [List.length_append,List.length_singleton];rw [Nat.add_assoc,hφ_shift (1+k),Nat.add_assoc]
  . intro j hj;simp only [List.length_append,List.length_singleton] at hj;rw [b7,b7]
    by_cases hlt:j< w₁.length
    . have hφj:=hφ_lt j hlt;simp only [show φ j≠w₂.length by omega,show j≠w₁.length by omega,Zj];exact hφ_init j hlt
    . have heq:j=w₁.length:=by omega
      subst heq;simp only [show φ w₁.length=w₂.length by simpa using hφ_shift 0,Zh]
  . simp only [List.length_append,List.length_cons] at hi ⊢;omega
def q0 {m k:ℕ} (f:(Fin m->Bool)->(Fin k->Bool)) (B:ℕ):Prop :=
 ∃ (C:Circuit) (out:Fin k->Fin (2+m+C.size)),
  ReadsBack (2+m) C/\C.size<=B/\(∀ g ∈ C.gates,b6 g) /\
  ∀ (x:Fin m->Bool) (j:Fin k),
   (C.wires ([false,true]++List.ofFn x)).getD (out j).1 false=f x j
lemma q0.mono {m k B₁ B₂:ℕ} {f:(Fin m->Bool)->(Fin k->Bool)}
  (hB:B₁<=B₂) (h:q0 f B₁):q0 f B₂:=by
 rcases h with ⟨C,out,hrb,hsz,hvg,hev⟩
 exact ⟨C,out,hrb,le_trans hsz hB,hvg,hev⟩
lemma q0.congr {m k B:ℕ} {f g:(Fin m->Bool)->(Fin k->Bool)}
  (hfg:∀ x,f x=g x) (h:q0 f B):q0 g B:=by
 rcases h with ⟨C,out,hrb,hsz,hvg,hev⟩
 exact ⟨C,out,hrb,hsz,hvg,fun x j=>(hev x j).trans (congrFun (hfg x) j)⟩
def bq {m:ℕ} (x:Fin m->Bool):Bool ⊕ Fin m->Bool
 | Sum.inl b=>b
 | Sum.inr i=>x i
lemma q0.rewire {m k:ℕ} (sel:Fin k->Bool ⊕ Fin m) :
   q0 (fun x j=>bq x (sel j)) 0:=by
 let out:Fin k->Fin (2+m+(⟨[],0⟩:Circuit).size):=fun j =>
   match sel j with
   | Sum.inl false=>⟨0,by simp [Circuit.size]⟩
   | Sum.inl true=>⟨1,by simp [Circuit.size];omega⟩
   | Sum.inr i=>⟨2+i.1,by simp [Circuit.size]⟩
 refine ⟨⟨[],0⟩,out,?_,by simp [Circuit.size],by simp,?_⟩
 . intro j hj;simp at hj
 . intro x j
   cases hsel:sel j with
   | inl b =>
    cases b <;> simp [out,hsel,Circuit.wires,bq]
   | inr i =>
    simp only [out,hsel,Circuit.wires,Zi,bq];have hlen:(List.ofFn x).length=m:=List.length_ofFn;rw [List.getD_eq_getElem _ _ (by simp [hlen];omega)]
    have h1:([false,true]++List.ofFn x)[2+i.1]'(by simp [hlen];omega) =
      (List.ofFn x)[i.1]'(by omega):=by
     rw [List.getElem_append_right (by simp)];simp
    rw [h1,List.getElem_ofFn]
lemma q0.k {m k:ℕ} (c:Fin k->Bool) :
  q0 (fun (_:Fin m->Bool)=>c) 0 :=
 (q0.rewire (fun j=>Sum.inl (c j))).congr (fun _=>rfl)
lemma q0.p {m k:ℕ} (r:Fin k->Fin m) :
  q0 (fun (x:Fin m->Bool) j=>x (r j)) 0 :=
 (q0.rewire (fun j=>Sum.inr (r j))).congr (fun _=>rfl)
lemma q0.id (m:ℕ):q0 (fun (x:Fin m->Bool)=>x) 0 :=
 (q0.p (fun i:Fin m=>i)).congr (fun _=>rfl)
lemma q0.notGate:q0 (fun (x:Fin 1->Bool) (_:Fin 1)=>!(x ⟨0,by omega⟩)) 1:=by
 refine ⟨⟨[⟨.not,[2]⟩],0⟩,fun _=>⟨3,by simp [Circuit.size]⟩,?_,by simp [Circuit.size],?_,?_⟩
 . intro j hj i hi
   have hj0:j=0:=by simp at hj;omega
   subst hj0;simp [gateAt] at hi;omega
 . intro g hg;simp at hg;subst hg;right;exact ⟨rfl,rfl⟩
 . intro x j;simp [Circuit.wires,GateOp.eval,List.ofFn_succ]
lemma q0.andGate :
   q0 (fun (x:Fin 2->Bool) (_:Fin 1)=>x ⟨0,by omega⟩&&x ⟨1,by omega⟩) 1:=by
 refine ⟨⟨[⟨.and,[2,3]⟩],0⟩,fun _=>⟨4,by simp [Circuit.size]⟩,?_,by simp [Circuit.size],?_,?_⟩
 . intro j hj i hi
   have hj0:j=0:=by simp at hj;omega
   subst hj0;simp [gateAt] at hi;omega
 . intro g hg;simp at hg;subst hg;left;exact ⟨Or.inl rfl,rfl⟩
 . intro x j;simp [Circuit.wires,GateOp.eval,List.ofFn_succ]
lemma q0.orGate :
   q0 (fun (x:Fin 2->Bool) (_:Fin 1)=>x ⟨0,by omega⟩||x ⟨1,by omega⟩) 1:=by
 refine ⟨⟨[⟨.or,[2,3]⟩],0⟩,fun _=>⟨4,by simp [Circuit.size]⟩,?_,by simp [Circuit.size],?_,?_⟩
 . intro j hj i hi
   have hj0:j=0:=by simp at hj;omega
   subst hj0;simp [gateAt] at hi;omega
 . intro g hg;simp at hg;subst hg;left;exact ⟨Or.inr rfl,rfl⟩
 . intro x j;simp [Circuit.wires,GateOp.eval,List.ofFn_succ]
lemma q0.c {m k r B₁ B₂:ℕ}
   {f:(Fin m->Bool)->(Fin k->Bool)} {g:(Fin k->Bool)->(Fin r->Bool)}
   (hf:q0 f B₁) (hg:q0 g B₂) :
   q0 (fun x=>g (f x)) (B₁+B₂):=by
 rcases hf with ⟨C₁,out₁,hrb₁,hsz₁,hvg₁,hev₁⟩
 rcases hg with ⟨C₂,out₂,hrb₂,hsz₂,hvg₂,hev₂⟩
 let φ:ℕ->ℕ:=fun i =>
   if h0:i=0 then 0
   else if h1:i=1 then 1
   else if h2:i< 2+k then (out₁ ⟨i-2,by omega⟩).1
   else 2+m+C₁.size+(i-(2+k))
 let C:Circuit:=⟨C₁.gates++C₂.gates.map (xa φ),0⟩
 have hCsz:C.size=C₁.size+C₂.size:=by
   simp [C,Circuit.size]
 have hφ_lt:∀ i< 2+k,φ i< 2+m+C₁.size:=by
   intro i hi;dsimp only [φ]
   split_ifs with h0 h1
   . omega
   . omega
   . exact (out₁ ⟨i-2,by omega⟩).isLt
 have hφ_shift:∀ t,φ (2+k+t)=2+m+C₁.size+t:=by
   intro t;dsimp only [φ]
   simp only [show 2+k+t≠0 by omega,show 2+k+t≠1 by omega,
     show ¬ (2+k+t< 2+k) by omega,Zf]
   omega
 have hout_lt:∀ j:Fin r,φ (out₂ j).1< 2+m+C.size:=by
   intro j;rw [hCsz]
   by_cases hlt:(out₂ j).1< 2+k
   . have:=hφ_lt _ hlt;omega
   . have hlt2:=(out₂ j).isLt
     have heq:(out₂ j).1=2+k+((out₂ j).1-(2+k)):=by omega
     rw [heq,hφ_shift];omega
 refine ⟨C,fun j=>⟨φ (out₂ j).1,hout_lt j⟩,?_,?_,?_,?_⟩
 . intro j hj i hi;simp only [C,List.length_append,List.length_map] at hj
   by_cases h1:j< C₁.gates.length
   . have hgat:gateAt C j=gateAt C₁ j:=by
       simp only [gateAt,C];rw [List.getD_append _ _ _ _ h1]
     rw [hgat] at hi;exact hrb₁ j h1 i hi
   . set j':=j-C₁.gates.length
     have hj':j'< C₂.gates.length:=by omega
     have hgat:gateAt C j=xa φ (gateAt C₂ j'):=by
       simp only [gateAt,C];rw [List.getD_append_right _ _ _ _ (by omega)];rw [List.getD_eq_getElem _ _ (by simp;omega),List.getElem_map];rw [List.getD_eq_getElem _ _ hj']
     rw [hgat] at hi;simp only [xa,List.mem_map] at hi
     rcases hi with ⟨i₀,hi₀,rfl⟩
     have hi₀_lt:=hrb₂ j' hj' i₀ hi₀
     by_cases hlt:i₀ < 2+k
     . have:=hφ_lt i₀ hlt;change φ i₀ < 2+m+j;simp only [Circuit.size] at this;omega
     . have heq:i₀=2+k+(i₀ - (2+k)):=by omega
       rw [heq,hφ_shift];simp only [Circuit.size];omega
 . rw [hCsz];omega
 . intro gate hgate;simp only [C,List.mem_append,List.mem_map] at hgate
   rcases hgate with h1 | ⟨g₀,hg₀,rfl⟩
   . exact hvg₁ gate h1
   . exact kp φ g₀ (hvg₂ g₀ hg₀)
 . intro x j
   change (xu (C₁.gates++C₂.gates.map (xa φ)) ([false,true]++List.ofFn x)).getD
       (φ (out₂ j).1) false=g (f x) j
   rw [kn];set w₁:=[false,true]++List.ofFn (f x);set w₂:=xu C₁.gates ([false,true]++List.ofFn x)
   have hw₁:w₁.length=2+k:=by simp [w₁];omega
   have hw₂:w₂.length=2+m+C₁.size:=by
     simp [w₂,ko,Circuit.size];omega
   have hrem:=kt φ C₂.gates w₁ w₂
     (by intro idx hidx u hu;rw [hw₁];exact hrb₂ idx hidx u hu)
     (by intro u hu;rw [hw₂];exact hφ_lt u (by omega))
     (by intro t;rw [hw₁,hw₂];exact hφ_shift t)
     (by
       intro u hu;rw [hw₁] at hu;dsimp only [φ]
       by_cases h0:u=0
       . subst h0;simp only [Zd];have hp:=vd C₁.gates ([false,true]++List.ofFn x) 0 (by simp);simpa [w₁,w₂] using hp
       . simp only [h0,Zf]
         by_cases h1:u=1
         . subst h1;simp only [Zd];have hp:=vd C₁.gates ([false,true]++List.ofFn x) 1 (by simp);simpa [w₁,w₂] using hp
         . simp only [h1,Zf,hu,Zd]
           have hget:w₁.getD u false=f x ⟨u-2,by omega⟩:=by
            rw [List.getD_eq_getElem _ _ (by omega)]
            have ha:([false,true]++List.ofFn (f x))[u]'(by simp;omega) =
              (List.ofFn (f x))[u-2]'(by simp;omega):=by
             rw [List.getElem_append_right (by simp;omega)];simp
            simpa [w₁,List.getElem_ofFn] using ha
           rw [hget]
           exact hev₁ x ⟨u-2,by omega⟩)
     (out₂ j).1 (by rw [hw₁];exact (out₂ j).isLt)
   rw [hrem];exact hev₂ (f x) j
def q1 {k₁ k₂:ℕ} (a:Fin k₁->Bool) (b:Fin k₂->Bool):Fin (k₁+k₂)->Bool :=
 fun i=>if h:i.1< k₁ then a ⟨i.1,h⟩ else b ⟨i.1-k₁,by omega⟩
lemma kf {k₁ k₂:ℕ} (a:Fin k₁->Bool) (b:Fin k₂->Bool) (i:Fin k₁) :
  q1 a b ⟨i.1,by omega⟩=a i:=by
 simp [q1,i.isLt]
lemma k8 {k₁ k₂:ℕ} (a:Fin k₁->Bool) (b:Fin k₂->Bool) (i:Fin k₂) :
  q1 a b ⟨k₁+i.1,by omega⟩=b i:=by
 simp [q1]
lemma q0.r {m k₁ k₂ B₁ B₂:ℕ}
   {f:(Fin m->Bool)->(Fin k₁->Bool)} {g:(Fin m->Bool)->(Fin k₂->Bool)}
   (hf:q0 f B₁) (hg:q0 g B₂) :
   q0 (fun x=>q1 (f x) (g x)) (B₁+B₂):=by
 rcases hf with ⟨C₁,out₁,hrb₁,hsz₁,hvg₁,hev₁⟩
 rcases hg with ⟨C₂,out₂,hrb₂,hsz₂,hvg₂,hev₂⟩
 let φ:ℕ->ℕ:=fun i=>if i< 2+m then i else C₁.size+i
 let C:Circuit:=⟨C₁.gates++C₂.gates.map (xa φ),0⟩
 have hCsz:C.size=C₁.size+C₂.size:=by simp [C,Circuit.size]
 have hφ_lt:∀ i< 2+m,φ i< 2+m+C₁.size:=by
   intro i hi;simp [φ,hi];omega
 have hφ_shift:∀ t,φ (2+m+t)=2+m+C₁.size+t:=by
   intro t;simp only [φ,show ¬ (2+m+t< 2+m) by omega,Zj];omega
 let out:Fin (k₁+k₂)->Fin (2+m+C.size):=fun j =>
   if h:j.1< k₁ then
     ⟨(out₁ ⟨j.1,h⟩).1,by rw [hCsz];have:=(out₁ ⟨j.1,h⟩).isLt;omega⟩
   else
     ⟨φ (out₂ ⟨j.1-k₁,by omega⟩).1,by
       rw [hCsz];have hlt:=(out₂ ⟨j.1-k₁,by omega⟩).isLt
       dsimp only [φ];split_ifs <;> omega⟩
 refine ⟨C,out,?_,?_,?_,?_⟩
 . intro j hj i hi;simp only [C,List.length_append,List.length_map] at hj
   by_cases h1:j< C₁.gates.length
   . have hgat:gateAt C j=gateAt C₁ j:=by
       simp only [gateAt,C];rw [List.getD_append _ _ _ _ h1]
     rw [hgat] at hi;exact hrb₁ j h1 i hi
   . set j':=j-C₁.gates.length
     have hj':j'< C₂.gates.length:=by omega
     have hgat:gateAt C j=xa φ (gateAt C₂ j'):=by
       simp only [gateAt,C];rw [List.getD_append_right _ _ _ _ (by omega)];rw [List.getD_eq_getElem _ _ (by simp;omega),List.getElem_map];rw [List.getD_eq_getElem _ _ hj']
     rw [hgat] at hi;simp only [xa,List.mem_map] at hi
     rcases hi with ⟨i₀,hi₀,rfl⟩
     have hi₀_lt:=hrb₂ j' hj' i₀ hi₀;dsimp only [φ];split_ifs
     . omega
     . simp only [Circuit.size];omega
 . rw [hCsz];omega
 . intro gate hgate;simp only [C,List.mem_append,List.mem_map] at hgate
   rcases hgate with h1 | ⟨g₀,hg₀,rfl⟩
   . exact hvg₁ gate h1
   . exact kp φ g₀ (hvg₂ g₀ hg₀)
 . intro x j
   change (xu (C₁.gates++C₂.gates.map (xa φ)) ([false,true]++List.ofFn x)).getD
       (out j).1 false=q1 (f x) (g x) j
   rw [kn];set w₁:=[false,true]++List.ofFn x;set w₂:=xu C₁.gates w₁
   have hw₁:w₁.length=2+m:=by simp [w₁];omega
   have hw₂:w₂.length=2+m+C₁.size:=by
     rw [ko,hw₁];rfl
   dsimp only [out,q1]
   by_cases hj:j.1< k₁
   . simp only [hj,Zd];rw [vd _ _ _ (by rw [hw₂];exact (out₁ ⟨j.1,hj⟩).isLt)];exact hev₁ x ⟨j.1,hj⟩
   . simp only [hj,Zf]
     have hrem:=kt φ C₂.gates w₁ w₂
       (by intro idx hidx u hu;rw [hw₁];exact hrb₂ idx hidx u hu)
       (by intro u hu;rw [hw₂];exact hφ_lt u (by omega))
       (by intro t;rw [hw₁,hw₂];exact hφ_shift t)
       (by
        intro u hu;rw [hw₁] at hu;simp only [φ,hu,Zh]
        exact vd C₁.gates w₁ u (by omega))
       (out₂ ⟨j.1-k₁,by omega⟩).1 (by rw [hw₁];exact (out₂ ⟨j.1-k₁,by omega⟩).isLt)
     rw [hrem];exact hev₂ x ⟨j.1-k₁,by omega⟩
lemma q0.boolNot {m B:ℕ} {f:(Fin m->Bool)->Bool}
  (hf:q0 (fun x (_:Fin 1)=>f x) B) :
  q0 (fun x (_:Fin 1)=>!(f x)) (B+1) :=
 (q0.c hf q0.notGate).congr (fun _=>rfl)
lemma q0.a {m B₁ B₂:ℕ} {f g:(Fin m->Bool)->Bool}
  (hf:q0 (fun x (_:Fin 1)=>f x) B₁)
  (hg:q0 (fun x (_:Fin 1)=>g x) B₂) :
  q0 (fun x (_:Fin 1)=>f x&&g x) (B₁+B₂+1):=by
 have hp:=q0.r hf hg;have hc:=q0.c hp q0.andGate;exact hc.congr (fun x=>by funext j;simp [q1])
lemma q0.boolOr {m B₁ B₂:ℕ} {f g:(Fin m->Bool)->Bool}
  (hf:q0 (fun x (_:Fin 1)=>f x) B₁)
  (hg:q0 (fun x (_:Fin 1)=>g x) B₂) :
  q0 (fun x (_:Fin 1)=>f x||g x) (B₁+B₂+1):=by
 have hp:=q0.r hf hg;have hc:=q0.c hp q0.orGate;exact hc.congr (fun x=>by funext j;simp [q1])
lemma q0.x {m B₁ B₂:ℕ} {f g:(Fin m->Bool)->Bool}
  (hf:q0 (fun x (_:Fin 1)=>f x) B₁)
  (hg:q0 (fun x (_:Fin 1)=>g x) B₂) :
  q0 (fun x (_:Fin 1)=>xor (f x) (g x)) (B₁+B₂+4):=by
 have hbase:q0 (fun (u:Fin 2->Bool) (_:Fin 1) =>
   xor (u ⟨0,by omega⟩) (u ⟨1,by omega⟩)) 4:=by
  have h0:q0 (fun (u:Fin 2->Bool) (_:Fin 1)=>u ⟨0,by omega⟩) 0 :=
   q0.p (fun _=>⟨0,by omega⟩)
  have h1:q0 (fun (u:Fin 2->Bool) (_:Fin 1)=>u ⟨1,by omega⟩) 0 :=
   q0.p (fun _=>⟨1,by omega⟩)
  have hor:=q0.boolOr h0 h1;have hand:=q0.a h0 h1;have hnand:=q0.boolNot hand;have hres:=q0.a hor hnand
  exact hres.congr (fun u=>by
   funext j
   cases u ⟨0,by omega⟩ <;> cases u ⟨1,by omega⟩ <;> rfl)
 exact (q0.c (q0.r hf hg) hbase).congr (fun x=>by
  funext j;simp [q1])
lemma q0.boolMux {m B₁ B₂ B₃:ℕ} {s a b:(Fin m->Bool)->Bool}
  (hs:q0 (fun x (_:Fin 1)=>s x) B₁)
  (ha:q0 (fun x (_:Fin 1)=>a x) B₂)
  (hb:q0 (fun x (_:Fin 1)=>b x) B₃) :
  q0 (fun x (_:Fin 1)=>if s x then b x else a x) (B₁+B₂+B₃+4):=by
 have hbase:q0 (fun (u:Fin 3->Bool) (_:Fin 1) =>
   if u ⟨0,by omega⟩ then u ⟨2,by omega⟩ else u ⟨1,by omega⟩) 4:=by
  have hu0:q0 (fun (u:Fin 3->Bool) (_:Fin 1)=>u ⟨0,by omega⟩) 0 :=
   q0.p (fun _=>⟨0,by omega⟩)
  have hu1:q0 (fun (u:Fin 3->Bool) (_:Fin 1)=>u ⟨1,by omega⟩) 0 :=
   q0.p (fun _=>⟨1,by omega⟩)
  have hu2:q0 (fun (u:Fin 3->Bool) (_:Fin 1)=>u ⟨2,by omega⟩) 0 :=
   q0.p (fun _=>⟨2,by omega⟩)
  have hres:=q0.boolOr (q0.a hu0 hu2) (q0.a (q0.boolNot hu0) hu1)
  exact (hres.mono (by omega)).congr (fun u=>by
   funext j
   cases u ⟨0,by omega⟩ <;> cases u ⟨1,by omega⟩ <;> cases u ⟨2,by omega⟩ <;> rfl)
 have hp:=q0.r (q0.r hs ha) hb
 exact ((q0.c hp hbase).mono (by omega)).congr (fun x=>by
  funext j;simp [q1])
lemma q0.f {m k B:ℕ} (f:(Fin m->Bool)->(Fin k->Bool))
  (hf:∀ j:Fin k,q0 (fun x (_:Fin 1)=>f x j) B) :
  q0 f (k*B):=by
 induction k with
 | zero =>
  exact ((q0.k (fun j:Fin 0=>Fin.elim0 j)).mono (by simp)).congr
   (fun _=>by funext j;exact Fin.elim0 j)
 | succ k ih =>
  have hprev:q0 (fun x (j:Fin k)=>f x ⟨j.1,by omega⟩) (k*B) :=
   ih (fun x j=>f x ⟨j.1,by omega⟩) (fun j=>hf ⟨j.1,by omega⟩)
  have hlast:q0 (fun x (_:Fin 1)=>f x ⟨k,by omega⟩) B:=hf ⟨k,by omega⟩;have hp:=q0.r hprev hlast
  exact (hp.mono (by rw [Nat.succ_mul])).congr (fun x=>by
   funext j;dsimp only [q1]
   split_ifs with h
   . rfl
   . have:j.1=k:=by omega
     congr 1;exact Zx this.symm)
lemma q0.b {m k B:ℕ} {f:(Fin m->Bool)->(Fin k->Bool)}
  (hf:q0 f B) (j:Fin k) :
  q0 (fun x (_:Fin 1)=>f x j) B :=
 ((q0.c hf (q0.p (fun (_:Fin 1)=>j))).mono (by omega)).congr (fun _=>rfl)
lemma q0.l {m s T B₀ Bs:ℕ}
  (init:(Fin m->Bool)->(Fin s->Bool))
  (step:Fin T->(Fin m->Bool)->(Fin s->Bool)->(Fin s->Bool))
  (hinit:q0 init B₀)
  (hstep:∀ i:Fin T,q0 (fun p:Fin (m+s)->Bool =>
    step i (fun a=>p ⟨a.1,by omega⟩) (fun b=>p ⟨m+b.1,by omega⟩)) Bs) :
  q0 (fun x=>(List.finRange T).foldl (fun st i=>step i x st) (init x))
    (B₀+T*Bs):=by
 induction T with
 | zero =>
  simpa [List.finRange_zero] using hinit
 | succ T ih =>
  have hprev:=ih
    (fun i x st=>step ⟨i.1,by omega⟩ x st)
    (fun i=>hstep ⟨i.1,by omega⟩)
  have hpair:=q0.r (q0.id m) hprev;have hcomp:=q0.c hpair (hstep ⟨T,by omega⟩)
  have hbound:0+(B₀+T*Bs)+Bs<=B₀+(T+1)*Bs:=by
    rw [Nat.succ_mul];omega
  refine (hcomp.mono hbound).congr (fun x=>?_)
  have hfr:List.finRange (T+1) =
      (List.finRange T).map (fun i:Fin T=>(⟨i.1,by omega⟩:Fin (T+1)))++[⟨T,by omega⟩]:=by
    apply List.ext_getElem
    . simp
    . intro idx h1 h2;simp only [List.length_finRange] at h1;rw [Zg]
      by_cases hlt:idx< T
      . rw [List.getElem_append_left (by simp [hlt]),List.getElem_map,Zg];rfl
      . have heq:idx=T:=by omega
        subst heq;rw [List.getElem_append_right (by simp)];simp
  rw [hfr,Zl,List.foldl_map,Zo,Zi];congr 1
  . funext a;exact kf x _ a
  . funext b;exact k8 x _ b
def q3 (d:ℕ) (v:ℕ):Fin d->Bool :=
 fun i=>v.testBit i.1
def q2 (d:ℕ) (z:Fin d->Bool):ℕ :=
 ∑ i:Fin d,(z i).toNat*2^i.1
lemma vq (d:ℕ) (z:Fin d->Bool):q2 d z< 2^d:=by
 induction d with
 | zero=>simp [q2]
 | succ d ih =>
  rw [q2,Fin.sum_univ_castSucc]
  have hprev:∑ i:Fin d,(z i.castSucc).toNat*2^(i.castSucc:Fin (d+1)).1< 2^d :=
   ih (fun i=>z i.castSucc)
  have hlast:(z (Fin.last d)).toNat*2^(Fin.last d).1<=2^d:=by
   cases z (Fin.last d) <;> simp
  rw [Nat.pow_succ];omega
lemma pa (d v:ℕ):q2 d (q3 d v)=v %2^d:=by
 induction d generalizing v with
 | zero=>simp [q2,Nat.mod_one]
 | succ d ih =>
  rw [q2,Fin.sum_univ_succ];simp only [q3,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,Nat.testBit_zero]
  have htail:∑ i:Fin d,(v.testBit (i.1+1)).toNat*2^(i.1+1) =
     2*q2 d (q3 d (v/2)):=by
   rw [q2,Finset.mul_sum];apply Zc rfl;intro i _;rw [q3,Nat.testBit_div_two,Nat.pow_succ];ring
  rw [htail,ih (v/2)]
  have hmod:v %2^(d+1)=v %2+2*((v/2)%2^d):=by
   rw [Nat.pow_succ,Nat.mul_comm (2^d) 2];have h1:=Nat.div_add_mod (v %(2*2^d)) 2;have h2:v %(2*2^d)%2=v %2:=Nat.mod_mul_right_mod v 2 (2^d);have h3:v %(2*2^d)/2=v/2 %2^d:=Nat.mod_mul_right_div_self v 2 (2^d);omega
  rw [hmod]
  have hb:(decide (v %2=1)).toNat=v %2:=by
   by_cases h:v %2=1
   . simp [h]
   . simp [h];omega
  rw [hb]
lemma q4 {d v:ℕ} (hv:v< 2^d) :
  q2 d (q3 d v)=v:=by
 rw [pa,Zm hv]
lemma qm (d:ℕ) (z:Fin d->Bool) :
  q3 d (q2 d z)=z:=by
 induction d with
 | zero=>funext i;exact Fin.elim0 i
 | succ d ih =>
  funext i
  have hsplit:q2 (d+1) z=(z 0).toNat+2*q2 d (fun j=>z j.succ):=by
    rw [q2,Fin.sum_univ_succ,q2,Finset.mul_sum];simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ];congr 1;apply Zc rfl;intro j _;rw [Nat.pow_succ];ring
  refine Fin.cases ?_ ?_ i
  . simp only [q3,Fin.val_zero,Nat.testBit_zero,hsplit]
    cases z 0 <;> simp
  . intro j;simp only [q3,Fin.val_succ,hsplit];rw [<- Nat.testBit_div_two]
    have hdiv:((z 0).toNat+2*q2 d (fun j=>z j.succ))/2 =
      q2 d (fun j=>z j.succ):=by
     cases z 0 with
     | false=>simp
     | true=>simp;omega
    rw [hdiv];exact congrFun (ih (fun k=>z k.succ)) j
def zb {d:ℕ} (s:Bool) (a b:Fin d->Bool):Fin d->Bool :=
 fun i=>if s then b i else a i
lemma zn {d:ℕ} (a b:Fin d->Bool):zb false a b=a:=rfl
lemma zz {d:ℕ} (a b:Fin d->Bool):zb true a b=b:=rfl
lemma zg {m d Bs Ba Bb:ℕ}
  {s:(Fin m->Bool)->Bool} {a b:(Fin m->Bool)->(Fin d->Bool)}
  (hs:q0 (fun x (_:Fin 1)=>s x) Bs)
  (ha:q0 a Ba) (hb:q0 b Bb) :
  q0 (fun x=>zb (s x) (a x) (b x)) (Bs+Ba+Bb+4*d):=by
 have hbase:q0 (fun u:Fin (1+d+d)->Bool =>
   zb (u ⟨0,by omega⟩)
    (fun i:Fin d=>u ⟨1+i.1,by omega⟩)
    (fun i:Fin d=>u ⟨1+d+i.1,by omega⟩)) (d*4):=by
  apply q0.f;intro i
  have hs0:q0 (fun (u:Fin (1+d+d)->Bool) (_:Fin 1)=>u ⟨0,by omega⟩) 0 :=
   q0.p (fun _=>⟨0,by omega⟩)
  have ha0:q0 (fun (u:Fin (1+d+d)->Bool) (_:Fin 1)=>u ⟨1+i.1,by omega⟩) 0 :=
   q0.p (fun _=>⟨1+i.1,by omega⟩)
  have hb0:q0 (fun (u:Fin (1+d+d)->Bool) (_:Fin 1)=>u ⟨1+d+i.1,by omega⟩) 0 :=
   q0.p (fun _=>⟨1+d+i.1,by omega⟩)
  exact (q0.boolMux hs0 ha0 hb0).mono (by omega)
 have hp:=q0.r (q0.r hs ha) hb
 exact ((q0.c hp hbase).mono (by omega)).congr (fun x=>by
  funext i;simp [zb,q1,show 1+i.1< 1+d by omega])
def jn {d:ℕ} (a:Fin d->Bool):Fin d->Bool:=fun i=>!(a i)
lemma br {m d B:ℕ} {a:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a B):q0 (fun x=>jn (a x)) (B+d):=by
 have hbase:q0 (fun u:Fin d->Bool=>jn u) (d*1) :=
  q0.f _ (fun i=>(q0.boolNot (q0.p (fun _=>i))).mono (by omega))
 exact (q0.c ha hbase).mono (by simp)
def xj {d:ℕ} (a:Fin d->Bool):Bool :=
 (List.finRange d).foldl (fun acc i=>acc||a i) false
lemma ku {d:ℕ} (a:Fin d->Bool) :
  xj a=true ↔ ∃ i:Fin d,a i=true:=by
 have hfold:∀ (l:List (Fin d)) (init:Bool),
   l.foldl (fun acc i=>acc||a i) init=true ↔ init=true\/∃ i ∈ l,a i=true:=by
  intro l
  induction l with
  | nil=>intro init;simp
  | cons x xs ih =>
   intro init;rw [Zo,ih]
   cases init <;> cases hx:a x <;> simp [hx]
 rw [xj,hfold];simp
lemma x3 {d:ℕ} (a:Fin d->Bool) :
   xj a=false ↔ ∀ i:Fin d,a i=false:=by
 cases h:xj a
 . simp only [true_iff];intro i
   cases hi:a i
   . rfl
   . have:=(ku a).mpr ⟨i,hi⟩;rw [h] at this;cases this
 . simp only [Bool.true_eq_false,false_iff,not_forall]
   rcases (ku a).mp h with ⟨i,hi⟩
   exact ⟨i,by rw [hi];decide⟩
lemma jo {m d B:ℕ} {a:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a B):q0 (fun x (_:Fin 1)=>xj (a x)) (B+d):=by
 have hbase:q0 (fun (u:Fin d->Bool) (_:Fin 1)=>xj u) (0+d*1):=by
  have hf:=q0.l (m:=d) (s:=1) (T:=d) (Bs:=1)
   (fun _ _=>false)
   (fun i u st _=>st ⟨0,by omega⟩||u i)
   (q0.k (fun _=>false))
   (fun i =>
    let h1:q0 (fun (p:Fin (d+1)->Bool) (_:Fin 1)=>p ⟨d,by omega⟩) 0 :=
     q0.p (fun _=>⟨d,by omega⟩)
    let h2:q0 (fun (p:Fin (d+1)->Bool) (_:Fin 1)=>p ⟨i.1,by omega⟩) 0 :=
     q0.p (fun _=>⟨i.1,by omega⟩)
    (q0.boolOr h1 h2).mono (by omega))
  refine hf.congr (fun u=>?_)
  have hgen:∀ (l:List (Fin d)) (st:Fin 1->Bool),
    l.foldl (fun st i (_:Fin 1)=>st ⟨0,by omega⟩||u i) st =
    fun _=>l.foldl (fun acc i=>acc||u i) (st ⟨0,by omega⟩):=by
   intro l
   induction l with
   | nil=>intro st;funext j;fin_cases j;rfl
   | cons i l ih=>intro st;exact ih _
  exact hgen (List.finRange d) (fun _=>false)
 exact (q0.c ha hbase).mono (by simp)
def kv {d:ℕ} (a:Fin d->Bool):Bool :=
 (List.finRange d).foldl (fun acc i=>acc&&a i) true
lemma jp {d:ℕ} (a:Fin d->Bool) :
  kv a=true ↔ ∀ i:Fin d,a i=true:=by
 have hfold:∀ (l:List (Fin d)) (init:Bool),
   l.foldl (fun acc i=>acc&&a i) init=true ↔ init=true/\∀ i ∈ l,a i=true:=by
  intro l
  induction l with
  | nil=>intro init;simp
  | cons x xs ih =>
   intro init;rw [Zo,ih]
   cases init <;> cases hx:a x <;> simp [hx]
 rw [kv,hfold];simp
lemma kw {m d B:ℕ} {a:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a B):q0 (fun x (_:Fin 1)=>kv (a x)) (B+d):=by
 have hbase:q0 (fun (u:Fin d->Bool) (_:Fin 1)=>kv u) (0+d*1):=by
  have hf:=q0.l (m:=d) (s:=1) (T:=d) (Bs:=1)
   (fun _ _=>true)
   (fun i u st _=>st ⟨0,by omega⟩&&u i)
   (q0.k (fun _=>true))
   (fun i =>
    let h1:q0 (fun (p:Fin (d+1)->Bool) (_:Fin 1)=>p ⟨d,by omega⟩) 0 :=
     q0.p (fun _=>⟨d,by omega⟩)
    let h2:q0 (fun (p:Fin (d+1)->Bool) (_:Fin 1)=>p ⟨i.1,by omega⟩) 0 :=
     q0.p (fun _=>⟨i.1,by omega⟩)
    (q0.a h1 h2).mono (by omega))
  refine hf.congr (fun u=>?_)
  have hgen:∀ (l:List (Fin d)) (st:Fin 1->Bool),
    l.foldl (fun st i (_:Fin 1)=>st ⟨0,by omega⟩&&u i) st =
    fun _=>l.foldl (fun acc i=>acc&&u i) (st ⟨0,by omega⟩):=by
   intro l
   induction l with
   | nil=>intro st;funext j;fin_cases j;rfl
   | cons i l ih=>intro st;exact ih _
  exact hgen (List.finRange d) (fun _=>true)
 exact (q0.c ha hbase).mono (by simp)
def yb {d:ℕ} (a b:Fin d->Bool):Bool :=
 kv (fun i=>!(xor (a i) (b i)))
lemma p7 {d:ℕ} (a b:Fin d->Bool):yb a b=true ↔ a=b:=by
 rw [yb,jp];constructor
 . intro h;funext i;have:=h i
   cases ha:a i <;> cases hb:b i <;> simp [ha,hb] at this ⊢
 . intro h;subst h;intro i;cases a i <;> rfl
lemma xb {m d Ba:ℕ}
  {a:(Fin m->Bool)->(Fin d->Bool)} (c:ℕ) (ha:q0 a Ba) :
  q0 (fun x (_:Fin 1)=>yb (a x) (q3 d c)) (Ba+2*d):=by
 have hbits:q0 (fun u:Fin d->Bool =>
    fun i:Fin d=>!(xor (u i) (q3 d c i))) (d*1):=by
  apply q0.f;intro i
  cases hc:q3 d c i
  . exact (q0.boolNot (q0.p (fun _=>i))).mono (by omega) |>.congr (fun u=>by
     funext j;cases u i <;> rfl)
  . exact (q0.p (fun _=>i)).mono (by omega) |>.congr (fun u=>by
     funext j;cases u i <;> rfl)
 have hall:=kw hbits;exact ((q0.c ha hall).mono (by omega)).congr (fun x=>by funext j;rfl)
def xk {d:ℕ} (a b:Fin d->Bool) (cin:Bool):ℕ->Bool
 | 0=>cin
 | i+1 =>
  if h:i< d then
   (a ⟨i,h⟩&&b ⟨i,h⟩)||(xk a b cin i&&(a ⟨i,h⟩||b ⟨i,h⟩))
  else false
def yh {d:ℕ} (a b:Fin d->Bool) (cin:Bool):Fin d->Bool :=
 fun i=>xor (xor (a i) (b i)) (xk a b cin i.1)
lemma pt (d:ℕ) (a b:Fin d->Bool) (cin:Bool) :
  q2 d (yh a b cin)+(xk a b cin d).toNat*2^d =
  q2 d a+q2 d b+cin.toNat:=by
 induction d with
 | zero=>simp [q2,xk]
 | succ d ih =>
  have hcar_eq:∀ k ≤ d,
    xk a b cin k=xk (fun i:Fin d=>a i.castSucc) (fun i:Fin d=>b i.castSucc) cin k:=by
   intro k hk
   induction k with
   | zero=>rfl
   | succ k ihk =>
    simp only [xk,show k< d+1 by omega,show k< d by omega,Zd,
     ihk (by omega)]
    rfl
  have hih:=ih (fun i=>a i.castSucc) (fun i=>b i.castSucc)
  have hval_split (z:Fin (d+1)->Bool) :
    q2 (d+1) z=q2 d (fun i=>z i.castSucc)+(z (Fin.last d)).toNat*2^d:=by
   rw [q2,Fin.sum_univ_castSucc,q2];rfl
  rw [hval_split (yh a b cin),hval_split a,hval_split b]
  have hpref:q2 d (fun i=>yh a b cin i.castSucc) =
    q2 d (yh (fun i=>a i.castSucc) (fun i=>b i.castSucc) cin):=by
   unfold q2;apply Zc rfl;intro i _;simp only [yh,Fin.val_castSucc,hcar_eq i.1 (le_of_lt i.isLt)]
  rw [hpref]
  have htop :
    (yh a b cin (Fin.last d)).toNat+2*(xk a b cin (d+1)).toNat =
    (a (Fin.last d)).toNat+(b (Fin.last d)).toNat+(xk a b cin d).toNat:=by
   simp only [yh,xk,Fin.val_last,lt_add_iff_pos_right,zero_lt_one,Zd]
   change (xor (xor (a (Fin.last d)) (b (Fin.last d))) (xk a b cin d)).toNat +
    2*((a (Fin.last d)&&b (Fin.last d)) ||
     (xk a b cin d&&(a (Fin.last d)||b (Fin.last d)))).toNat=_
   cases a (Fin.last d) <;> cases b (Fin.last d) <;> cases xk a b cin d <;> decide
  have hcar_d:=hcar_eq d le_rfl;rw [<- hcar_d] at hih
  have hpow:2^(d+1)=2*2^d:=by rw [Nat.pow_succ,Nat.mul_comm]
  rw [hpow]
  have hmul:(yh a b cin (Fin.last d)).toNat*2^d +
    (xk a b cin (d+1)).toNat*(2*2^d) =
    ((a (Fin.last d)).toNat+(b (Fin.last d)).toNat+(xk a b cin d).toNat)*2^d:=by
   have:=congrArg (·*2^d) htop;linarith
  linarith
lemma qc (d:ℕ) (a b:Fin d->Bool) (cin:Bool) :
  q2 d (yh a b cin)=(q2 d a+q2 d b+cin.toNat)%2^d:=by
 have h:=pt d a b cin
 have hlt:=vq d (yh a b cin);rw [<- h,Nat.add_mul_mod_self_right,Zm hlt]
def qr {d:ℕ} (a b:Fin d->Bool):Fin d->Bool:=yh a b false
def zm {d:ℕ} (a b:Fin d->Bool):Fin d->Bool:=yh a (jn b) true
lemma b8 (d:ℕ) (b:Fin d->Bool) :
  q2 d (jn b)+q2 d b+1=2^d:=by
 induction d with
 | zero=>simp [q2]
 | succ d ih =>
  have hval_split (z:Fin (d+1)->Bool) :
    q2 (d+1) z=q2 d (fun i=>z i.castSucc)+(z (Fin.last d)).toNat*2^d:=by
   rw [q2,Fin.sum_univ_castSucc,q2];rfl
  rw [hval_split (jn b),hval_split b];have hih:=ih (fun i=>b i.castSucc)
  have hlast:(jn b (Fin.last d)).toNat+(b (Fin.last d)).toNat=1:=by
   simp only [jn];cases b (Fin.last d) <;> decide
  have hpow:2^(d+1)=2*2^d:=by rw [Nat.pow_succ,Nat.mul_comm]
  rw [hpow]
  have hmul:(jn b (Fin.last d)).toNat*2^d+(b (Fin.last d)).toNat*2^d=2^d:=by
   have:=congrArg (·*2^d) hlast;linarith
  have hvn:q2 d (fun i=>jn b i.castSucc)=q2 d (jn (fun i=>b i.castSucc)):=rfl;rw [hvn];linarith
lemma wj {d:ℕ} (a b:Fin d->Bool) (hle:q2 d b<=q2 d a) :
  q2 d (zm a b)=q2 d a-q2 d b:=by
 rw [zm,qc];have hnot:=b8 d b;have hlt:=vq d a
 have h1:q2 d a+q2 d (jn b)+true.toNat =
   (q2 d a-q2 d b)+2^d:=by
  simp only [Bool.toNat_true];omega
 rw [h1,Nat.add_mod_right,Zm (by omega)]
lemma kx (d:ℕ) :
  q0 (fun u:Fin (1+d+d)->Bool =>
    yh (fun i:Fin d=>u ⟨1+i.1,by omega⟩)
         (fun i:Fin d=>u ⟨1+d+i.1,by omega⟩)
         (u ⟨0,by omega⟩)) (13*d):=by
 let step:Fin d->(Fin (1+d+d)->Bool)->(Fin (1+d)->Bool)->(Fin (1+d)->Bool) :=
  fun i u st =>
    let cin:=st ⟨0,by omega⟩
    let ai:=u ⟨1+i.1,by omega⟩
    let bi:=u ⟨1+d+i.1,by omega⟩
    let sumBit:=xor (xor ai bi) cin
    let cout:=(ai&&bi)||(cin&&(ai||bi))
    fun j =>
      if j.1=0 then cout
      else if j.1=1+i.1 then sumBit
      else st j
 have hstep:∀ i:Fin d,q0 (fun p:Fin ((1+d+d)+(1+d))->Bool =>
    step i (fun a=>p ⟨a.1,by omega⟩) (fun b=>p ⟨1+d+d+b.1,by omega⟩)) 13:=by
  intro i
  let getCin:(Fin ((1+d+d)+(1+d))->Bool)->Bool:=fun p=>p ⟨1+d+d,by omega⟩
  let getAi:(Fin ((1+d+d)+(1+d))->Bool)->Bool:=fun p=>p ⟨1+i.1,by omega⟩
  let getBi:(Fin ((1+d+d)+(1+d))->Bool)->Bool:=fun p=>p ⟨1+d+i.1,by omega⟩
  have hCin:q0 (fun p (_:Fin 1)=>getCin p) 0:=q0.p (fun _=>⟨1+d+d,by omega⟩)
  have hAi:q0 (fun p (_:Fin 1)=>getAi p) 0:=q0.p (fun _=>⟨1+i.1,by omega⟩);have hBi:q0 (fun p (_:Fin 1)=>getBi p) 0:=q0.p (fun _=>⟨1+d+i.1,by omega⟩)
  have hSum:q0 (fun p (_:Fin 1)=>xor (xor (getAi p) (getBi p)) (getCin p)) 8 :=
    (q0.x (q0.x hAi hBi) hCin).mono (by omega)
  have hCout:q0 (fun p (_:Fin 1) =>
      (getAi p&&getBi p)||(getCin p&&(getAi p||getBi p))) 4 :=
    (q0.boolOr (q0.a hAi hBi) (q0.a hCin (q0.boolOr hAi hBi))).mono (by omega)
  have hboth:=q0.r (q0.r hCout hSum) (q0.id ((1+d+d)+(1+d)))
  have hrew:q0 (fun q:Fin (1+1+((1+d+d)+(1+d)))->Bool =>
      fun j:Fin (1+d) =>
        if j.1=0 then q ⟨0,by omega⟩
        else if j.1=1+i.1 then q ⟨1,by omega⟩
        else q ⟨2+(1+d+d)+j.1,by omega⟩) 0 :=
    (q0.p (fun j:Fin (1+d) =>
      if j.1=0 then ⟨0,by omega⟩
      else if j.1=1+i.1 then ⟨1,by omega⟩
      else ⟨2+(1+d+d)+j.1,by omega⟩)).congr (fun q=>by
        funext j;split_ifs <;> rfl)
  refine ((q0.c hboth hrew).mono (by omega)).congr (fun p=>?_)
  funext j;dsimp only [step,getCin,getAi,getBi]
  split_ifs with h0 h1
  . simp [q1]
  . simp [q1]
  . have hv1:¬ (2+(1+d+d)+j.1< 1+1):=by omega
    simp only [q1,hv1,Zf];congr 1;apply Zx;dsimp;omega
 have hinit:q0 (fun u:Fin (1+d+d)->Bool =>
    fun j:Fin (1+d)=>if j.1=0 then u ⟨0,by omega⟩ else false) 0 :=
  (q0.rewire (fun j:Fin (1+d) =>
    if j.1=0 then Sum.inr ⟨0,by omega⟩ else Sum.inl false)).congr (fun u=>by
      funext j;split_ifs <;> rfl)
 have hfold:=q0.l _ step hinit hstep
 have hproj:q0 (fun st:Fin (1+d)->Bool =>
    fun i:Fin d=>st ⟨1+i.1,by omega⟩) 0 :=
  q0.p (fun i=>⟨1+i.1,by omega⟩)
 refine ((q0.c hfold hproj).mono (by rw [Nat.mul_comm];omega)).congr (fun u=>?_)
 set a:Fin d->Bool:=fun i=>u ⟨1+i.1,by omega⟩
 set b:Fin d->Bool:=fun i=>u ⟨1+d+i.1,by omega⟩
 set cin:Bool:=u ⟨0,by omega⟩
 have hinv:∀ k ≤ d,
    let st:=((List.finRange d).take k).foldl (fun st i=>step i u st)
      (fun j:Fin (1+d)=>if j.1=0 then cin else false)
    st ⟨0,by omega⟩=xk a b cin k /\
    ∀ idx:Fin d,idx.1< k->st ⟨1+idx.1,by omega⟩=yh a b cin idx:=by
  intro k hk
  induction k with
  | zero =>
    simp [xk]
  | succ k ihk =>
    have htake:(List.finRange d).take (k+1) =
        (List.finRange d).take k++[⟨k,by omega⟩]:=by
      rw [Zt (by simp;omega)];simp [Zg]
    rw [htake,Zl,Zo,Zi]
    rcases ihk (by omega) with ⟨hcar,hbits⟩
    constructor
    . simp only [step,Zh,hcar,xk,show k< d by omega,Zd];rfl
    . intro idx hidx;simp only [step,show 1+idx.1≠0 by omega,Zj]
      by_cases heq:idx.1=k
      . simp only [show 1+idx.1=1+k by omega,Zh];have hidx_eq:idx=⟨k,by omega⟩:=Zx heq;rw [hidx_eq];change (a ⟨k,by omega⟩^^b ⟨k,by omega⟩^^_)=(a ⟨k,by omega⟩^^b ⟨k,by omega⟩^^xk a b cin k);exact congrArg (xor (a ⟨k,by omega⟩^^b ⟨k,by omega⟩)) hcar
      . simp only [show 1+idx.1≠1+k by omega,Zj];exact hbits idx (by omega)
 have hfull:=hinv d le_rfl;rw [Zk (by simp)] at hfull;funext i;exact hfull.2 i i.isLt
lemma kq {m d Ba Bb Bc:ℕ}
  {a b:(Fin m->Bool)->(Fin d->Bool)} {c:(Fin m->Bool)->Bool}
  (ha:q0 a Ba) (hb:q0 b Bb) (hc:q0 (fun x (_:Fin 1)=>c x) Bc) :
  q0 (fun x=>yh (a x) (b x) (c x)) (Bc+Ba+Bb+13*d):=by
 have hp:=q0.r (q0.r hc ha) hb
 exact ((q0.c hp (kx d)).mono (by omega)).congr (fun x=>by
  have ha':(fun i:Fin d=>q1 (q1 (fun _:Fin 1=>c x) (a x)) (b x) ⟨1+i.1,by omega⟩)=a x:=by
   funext i;simp [q1,show 1+i.1< 1+d by omega]
  have hb':(fun i:Fin d=>q1 (q1 (fun _:Fin 1=>c x) (a x)) (b x) ⟨1+d+i.1,by omega⟩)=b x:=by
   funext i;simp [q1]
  have hc':q1 (q1 (fun _:Fin 1=>c x) (a x)) (b x) ⟨0,by omega⟩=c x:=by
   simp [q1]
  rw [ha',hb',hc'])
lemma z8 {m d Ba Bb:ℕ}
  {a b:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a Ba) (hb:q0 b Bb) :
  q0 (fun x=>qr (a x) (b x)) (Ba+Bb+13*d) :=
 (kq ha hb (q0.k (fun _=>false))).mono (by omega)
lemma wx {m d Ba Bb:ℕ}
  {a b:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a Ba) (hb:q0 b Bb) :
  q0 (fun x=>zm (a x) (b x)) (Ba+Bb+14*d) :=
 (kq ha (br hb) (q0.k (fun _=>true))).mono (by omega)
def wi {d:ℕ} (a b:Fin d->Bool):Bool :=
 (List.finRange d).foldl
  (fun acc i=>(!(a i)&&b i)||(!(xor (a i) (b i))&&acc)) false
lemma x8 (d:ℕ) (a b:Fin d->Bool) :
  wi a b=decide (q2 d a< q2 d b):=by
 have hgen:∀ k (hk:k<=d),
   ((List.finRange d).take k).foldl
     (fun acc i=>(!(a i)&&b i)||(!(xor (a i) (b i))&&acc)) false =
   decide (q2 k (fun i:Fin k=>a ⟨i.1,by omega⟩) <
       q2 k (fun i:Fin k=>b ⟨i.1,by omega⟩)):=by
  intro k hk
  induction k with
  | zero=>simp [q2]
  | succ k ihk =>
   have htake:(List.finRange d).take (k+1) =
      (List.finRange d).take k++[⟨k,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi,ihk (by omega)]
   have hsp (z:Fin d->Bool) :
      q2 (k+1) (fun i:Fin (k+1)=>z ⟨i.1,by omega⟩) =
      q2 k (fun i:Fin k=>z ⟨i.1,by omega⟩)+(z ⟨k,by omega⟩).toNat*2^k:=by
     rw [q2,Fin.sum_univ_castSucc,q2];rfl
   rw [hsp a,hsp b];have hlt_a:=vq k (fun i:Fin k=>a ⟨i.1,by omega⟩);have hlt_b:=vq k (fun i:Fin k=>b ⟨i.1,by omega⟩)
   cases ha:a ⟨k,by omega⟩ <;> cases hb:b ⟨k,by omega⟩ <;> simp
   . omega
   . omega
 have hfull:=hgen d le_rfl;rw [Zk (by simp)] at hfull;simpa [wi] using hfull
lemma xo {m d Ba Bb:ℕ}
  {a b:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a Ba) (hb:q0 b Bb) :
  q0 (fun x (_:Fin 1)=>wi (a x) (b x)) (Ba+Bb+10*d):=by
 have hbase:q0 (fun (u:Fin (d+d)->Bool) (_:Fin 1) =>
   wi (fun i:Fin d=>u ⟨i.1,by omega⟩) (fun i:Fin d=>u ⟨d+i.1,by omega⟩)) (0+d*10):=by
  have hf:=q0.l (m:=d+d) (s:=1) (T:=d) (Bs:=10)
   (fun _ _=>false)
   (fun i u st _ =>
    (!(u ⟨i.1,by omega⟩)&&u ⟨d+i.1,by omega⟩) ||
    (!(xor (u ⟨i.1,by omega⟩) (u ⟨d+i.1,by omega⟩))&&st ⟨0,by omega⟩))
   (q0.k (fun _=>false))
   (fun i =>
    let hAi:q0 (fun p:Fin ((d+d)+1)->Bool=>fun (_:Fin 1)=>p ⟨i.1,by omega⟩) 0 :=
     q0.p (fun _=>⟨i.1,by omega⟩)
    let hBi:q0 (fun p:Fin ((d+d)+1)->Bool=>fun (_:Fin 1)=>p ⟨d+i.1,by omega⟩) 0 :=
     q0.p (fun _=>⟨d+i.1,by omega⟩)
    let hAcc:q0 (fun p:Fin ((d+d)+1)->Bool=>fun (_:Fin 1)=>p ⟨d+d,by omega⟩) 0 :=
     q0.p (fun _=>⟨d+d,by omega⟩)
    (q0.boolOr
     (q0.a (q0.boolNot hAi) hBi)
     (q0.a (q0.boolNot (q0.x hAi hBi)) hAcc)).mono (by omega))
  refine hf.congr (fun u=>?_)
  have hgen:∀ (l:List (Fin d)) (st:Fin 1->Bool),
    l.foldl (fun st i (_:Fin 1) =>
     (!(u ⟨i.1,by omega⟩)&&u ⟨d+i.1,by omega⟩) ||
     (!(xor (u ⟨i.1,by omega⟩) (u ⟨d+i.1,by omega⟩))&&st ⟨0,by omega⟩)) st =
    fun _=>l.foldl (fun acc i =>
     (!(u ⟨i.1,by omega⟩)&&u ⟨d+i.1,by omega⟩) ||
     (!(xor (u ⟨i.1,by omega⟩) (u ⟨d+i.1,by omega⟩))&&acc)) (st ⟨0,by omega⟩):=by
   intro l
   induction l with
   | nil=>intro st;funext j;fin_cases j;rfl
   | cons i l ih=>intro st;exact ih _
  exact hgen (List.finRange d) (fun _=>false)
 exact ((q0.c (q0.r ha hb) hbase).mono (by rw [Nat.mul_comm];omega)).congr (fun x=>by
  funext j;simp [wi,q1])
def ym {d:ℕ} (a b:Fin d->Bool):Fin d->Bool :=
 zb (wi a b) b a
lemma v0 {d:ℕ} (a b:Fin d->Bool) :
   q2 d (ym a b)=min (q2 d a) (q2 d b):=by
 rw [ym,x8]
 by_cases h:q2 d a< q2 d b
 . rw [decide_eq_true h,zz,Nat.min_eq_left (le_of_lt h)]
 . rw [decide_eq_false h,zn,Nat.min_eq_right (Nat.le_of_not_lt h)]
lemma ky {m d Ba Bb:ℕ}
  {a b:(Fin m->Bool)->(Fin d->Bool)}
  (ha:q0 a Ba) (hb:q0 b Bb) :
  q0 (fun x=>ym (a x) (b x)) (Ba+Bb+14*d):=by
 have hbase:q0 (fun u:Fin (d+d)->Bool =>
   ym (fun i:Fin d=>u ⟨i.1,by omega⟩) (fun i:Fin d=>u ⟨d+i.1,by omega⟩)) (14*d):=by
  have ha0:q0 (fun u:Fin (d+d)->Bool=>fun i:Fin d=>u ⟨i.1,by omega⟩) 0 :=
   q0.p (fun i=>⟨i.1,by omega⟩)
  have hb0:q0 (fun u:Fin (d+d)->Bool=>fun i:Fin d=>u ⟨d+i.1,by omega⟩) 0 :=
   q0.p (fun i=>⟨d+i.1,by omega⟩)
  exact (zg (xo ha0 hb0) hb0 ha0).mono (by omega)
 exact ((q0.c (q0.r ha hb) hbase).mono (by omega)).congr (fun x=>by
  have ha':(fun i:Fin d=>q1 (a x) (b x) ⟨i.1,by omega⟩)=a x:=by
   funext i;exact kf (a x) (b x) i
  have hb':(fun i:Fin d=>q1 (a x) (b x) ⟨d+i.1,by omega⟩)=b x:=by
   funext i;exact k8 (a x) (b x) i
  rw [ha',hb'])
def w3 {K₁ K₂ d₁ d₂ r:ℕ}
  (tbl:Fin K₁->Fin K₂->Bool->(Fin r->Bool))
  (i₁:Fin d₁->Bool) (i₂:Fin d₂->Bool) (p:Bool):Fin r->Bool :=
 if h₁:q2 d₁ i₁ < K₁ then
  if h₂:q2 d₂ i₂ < K₂ then
   tbl ⟨q2 d₁ i₁,h₁⟩ ⟨q2 d₂ i₂,h₂⟩ p
  else fun _=>false
 else fun _=>false
lemma j8 {m K₁ K₂ d₁ d₂ r B₁ B₂ Bp:ℕ}
  (tbl:Fin K₁->Fin K₂->Bool->(Fin r->Bool))
  {i₁:(Fin m->Bool)->(Fin d₁->Bool)}
  {i₂:(Fin m->Bool)->(Fin d₂->Bool)}
  {p:(Fin m->Bool)->Bool}
  (hK₁:K₁<=2^d₁) (hK₂:K₂<=2^d₂)
  (hi₁:q0 i₁ B₁) (hi₂:q0 i₂ B₂)
  (hp:q0 (fun x (_:Fin 1)=>p x) Bp) :
  q0 (fun x=>w3 tbl (i₁ x) (i₂ x) (p x))
    (B₁+B₂+Bp+(K₁*K₂*2)*(2*d₁+2*d₂+4*r+4)):=by
 let N:=K₁*K₂*2
 have hbase:q0 (fun u:Fin (d₁+d₂+1)->Bool =>
    w3 tbl
      (fun j:Fin d₁=>u ⟨j.1,by omega⟩)
      (fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩)
      (u ⟨d₁+d₂,by omega⟩)) (0+N*(2*d₁+2*d₂+4*r+4)):=by
  let decode (idx:Fin N):Fin K₁ × Fin K₂ × Bool :=
    let q:=idx.1/2
    have hK₂pos:0< K₂:=by
      by_contra h0;simp only [Nat.not_lt,Nat.le_zero] at h0
      have:=idx.isLt;simp [N,h0] at this
    (⟨q/K₂,by
        have:=idx.isLt
        exact Nat.div_lt_of_lt_mul (by
          have:q< K₁*K₂:=Nat.div_lt_of_lt_mul (by dsimp [N] at this;omega)
          rwa [Nat.mul_comm])⟩,
     ⟨q %K₂,Nat.mod_lt _ hK₂pos⟩,
     decide (idx.1 %2=1))
  let step:Fin N->(Fin (d₁+d₂+1)->Bool)->(Fin r->Bool)->(Fin r->Bool) :=
    fun idx u acc =>
      let t:=decode idx
      let hit :=
        yb (fun j:Fin d₁=>u ⟨j.1,by omega⟩) (q3 d₁ t.1.1) &&
        yb (fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩) (q3 d₂ t.2.1.1) &&
        (if t.2.2 then u ⟨d₁+d₂,by omega⟩ else !(u ⟨d₁+d₂,by omega⟩))
      zb hit acc (tbl t.1 t.2.1 t.2.2)
  have hstep:∀ idx:Fin N,q0 (fun q:Fin ((d₁+d₂+1)+r)->Bool =>
      step idx (fun a=>q ⟨a.1,by omega⟩) (fun b=>q ⟨d₁+d₂+1+b.1,by omega⟩))
      (2*d₁+2*d₂+4*r+4):=by
    intro idx
    let t:=decode idx
    have hu1:q0 (fun q:Fin ((d₁+d₂+1)+r)->Bool =>
        fun j:Fin d₁=>q ⟨j.1,by omega⟩) 0:=q0.p (fun j=>⟨j.1,by omega⟩)
    have hu2:q0 (fun q:Fin ((d₁+d₂+1)+r)->Bool =>
        fun j:Fin d₂=>q ⟨d₁+j.1,by omega⟩) 0:=q0.p (fun j=>⟨d₁+j.1,by omega⟩)
    have hup:q0 (fun q:Fin ((d₁+d₂+1)+r)->Bool =>
        fun (_:Fin 1)=>if t.2.2 then q ⟨d₁+d₂,by omega⟩ else !(q ⟨d₁+d₂,by omega⟩)) 1:=by
      cases ht:t.2.2
      . exact (q0.boolNot (q0.p (fun _=>⟨d₁+d₂,by omega⟩))).mono (by omega)
      . exact (q0.p (fun _=>⟨d₁+d₂,by omega⟩)).mono (by omega)
    have hacc:q0 (fun q:Fin ((d₁+d₂+1)+r)->Bool =>
        fun b:Fin r=>q ⟨d₁+d₂+1+b.1,by omega⟩) 0 :=
      q0.p (fun b=>⟨d₁+d₂+1+b.1,by omega⟩)
    have hhit:=q0.a
      (q0.a (xb t.1.1 hu1) (xb t.2.1.1 hu2)) hup
    exact (zg hhit hacc (q0.k (tbl t.1 t.2.1 t.2.2))).mono (by omega)
  have hf:=q0.l (fun _=>fun _=>false) step (q0.k _) hstep
  refine hf.congr (fun u=>?_)
  set v1:=q2 d₁ (fun j:Fin d₁=>u ⟨j.1,by omega⟩);set v2:=q2 d₂ (fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩);set vp:=u ⟨d₁+d₂,by omega⟩
  have hhit_iff:∀ idx:Fin N,
      (yb (fun j:Fin d₁=>u ⟨j.1,by omega⟩) (q3 d₁ (decode idx).1.1) &&
       yb (fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩) (q3 d₂ (decode idx).2.1.1) &&
       (if (decode idx).2.2 then vp else !vp))=true ↔
      v1=(decode idx).1.1/\v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=by
    intro idx;simp only [Bool.and_eq_true,p7]
    have h1:(fun j:Fin d₁=>u ⟨j.1,by omega⟩)=q3 d₁ (decode idx).1.1 ↔ v1=(decode idx).1.1:=by
      constructor
      . intro h;rw [show v1=q2 d₁ (q3 d₁ (decode idx).1.1) by exact congrArg (q2 d₁) h];exact q4 (lt_of_lt_of_le (decode idx).1.isLt hK₁)
      . intro h;rw [<- h];exact (qm d₁ _).symm
    have h2:(fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩)=q3 d₂ (decode idx).2.1.1 ↔ v2=(decode idx).2.1.1:=by
      constructor
      . intro h;rw [show v2=q2 d₂ (q3 d₂ (decode idx).2.1.1) by exact congrArg (q2 d₂) h];exact q4 (lt_of_lt_of_le (decode idx).2.1.isLt hK₂)
      . intro h;rw [<- h];exact (qm d₂ _).symm
    have h3:(if (decode idx).2.2 then vp else !vp)=true ↔ vp=(decode idx).2.2:=by
      cases (decode idx).2.2 <;> cases vp <;> decide
    rw [h1,h2,h3,and_assoc]
  have hinv:∀ t ≤ N,
      ((List.finRange N).take t).foldl (fun acc idx=>step idx u acc) (fun _=>false) =
      if h:∃ idx:Fin N,idx.1< t/\v1=(decode idx).1.1 /\
          v2=(decode idx).2.1.1/\vp=(decode idx).2.2 then
        tbl (decode (Classical.choose h)).1 (decode (Classical.choose h)).2.1
          (decode (Classical.choose h)).2.2
      else fun _=>false:=by
    intro t ht
    induction t with
    | zero=>simp
    | succ t iht =>
      have htake:(List.finRange N).take (t+1) =
          (List.finRange N).take t++[⟨t,by omega⟩]:=by
        rw [Zt (by simp;omega)];simp [Zg]
      rw [htake,Zl,Zo,Zi,iht (by omega)]
      set cur:Fin N:=⟨t,by omega⟩
      dsimp only [step]
      by_cases hcur:v1=(decode cur).1.1/\v2=(decode cur).2.1.1/\vp=(decode cur).2.2
      . rw [(hhit_iff cur).mpr hcur,zz]
        have hex:∃ idx:Fin N,idx.1< t+1/\v1=(decode idx).1.1 /\
            v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=⟨cur,by dsimp [cur];omega,hcur⟩
        simp only [hex,Zd];have hc:=Classical.choose_spec hex
        have h1:(decode (Classical.choose hex)).1=(decode cur).1 :=
          Zx (hc.2.1.symm.trans hcur.1)
        have h2:(decode (Classical.choose hex)).2.1=(decode cur).2.1 :=
          Zx (hc.2.2.1.symm.trans hcur.2.1)
        have h3:(decode (Classical.choose hex)).2.2=(decode cur).2.2 :=
          hc.2.2.2.symm.trans hcur.2.2
        simp only [h1,h2,h3]
      . have hf_hit:(yb (fun j:Fin d₁=>u ⟨j.1,by omega⟩) (q3 d₁ (decode cur).1.1) &&
            yb (fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩) (q3 d₂ (decode cur).2.1.1) &&
            (if (decode cur).2.2 then vp else !vp))=false:=by
          cases hv:(yb (fun j:Fin d₁=>u ⟨j.1,by omega⟩) (q3 d₁ (decode cur).1.1) &&
            yb (fun j:Fin d₂=>u ⟨d₁+j.1,by omega⟩) (q3 d₂ (decode cur).2.1.1) &&
            (if (decode cur).2.2 then vp else !vp))
          . rfl
          . exact absurd ((hhit_iff cur).mp hv) hcur
        rw [hf_hit,zn]
        by_cases hprev:∃ idx:Fin N,idx.1< t/\v1=(decode idx).1.1 /\
            v2=(decode idx).2.1.1/\vp=(decode idx).2.2
        . rcases hprev with ⟨idx0,hlt0,h10,h20,h30⟩
          have hex1:∃ idx:Fin N,idx.1< t/\v1=(decode idx).1.1 /\
              v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=⟨idx0,hlt0,h10,h20,h30⟩
          have hex2:∃ idx:Fin N,idx.1< t+1/\v1=(decode idx).1.1 /\
              v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=⟨idx0,by omega,h10,h20,h30⟩
          simp only [hex1,hex2,Zd];have c1:=Classical.choose_spec hex1;have c2:=Classical.choose_spec hex2
          have e1:(decode (Classical.choose hex1)).1=(decode (Classical.choose hex2)).1 :=
            Zx (c1.2.1.symm.trans c2.2.1)
          have e2:(decode (Classical.choose hex1)).2.1=(decode (Classical.choose hex2)).2.1 :=
            Zx (c1.2.2.1.symm.trans c2.2.2.1)
          have e3:(decode (Classical.choose hex1)).2.2=(decode (Classical.choose hex2)).2.2 :=
            c1.2.2.2.symm.trans c2.2.2.2
          simp only [e1,e2,e3]
        . have hno:¬ ∃ idx:Fin N,idx.1< t+1/\v1=(decode idx).1.1 /\
              v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=by
            rintro ⟨idx,hlt,h1,h2,h3⟩
            by_cases heqt:idx.1=t
            . have:idx=cur:=Zx heqt;subst this;exact hcur ⟨h1,h2,h3⟩
            . exact hprev ⟨idx,by omega,h1,h2,h3⟩
          simp only [hprev,hno,Zf]
  have hfull:=hinv N le_rfl;rw [Zk (by simp)] at hfull;rw [hfull]
  change _=if h₁:v1< K₁ then if h₂:v2< K₂ then tbl ⟨v1,h₁⟩ ⟨v2,h₂⟩ vp else fun _=>false else fun _=>false
  by_cases h1:v1< K₁
  . simp only [h1,Zd]
    by_cases h2:v2< K₂
    . simp only [h2,Zd]
      have hidx_val:(v1*K₂+v2)*2+vp.toNat< N:=by
        have:v1*K₂+v2< K₁*K₂:=by
          have:(v1+1)*K₂<=K₁*K₂:=Zw K₂ (by omega);linarith
        have:vp.toNat< 2:=by cases vp <;> decide
        dsimp [N];omega
      let target:Fin N:=⟨(v1*K₂+v2)*2+vp.toNat,hidx_val⟩
      have hdec:(decode target).1.1=v1/\(decode target).2.1.1=v2 /\
          (decode target).2.2=vp:=by
        dsimp only [decode,target]
        have hdiv2:((v1*K₂+v2)*2+vp.toNat)/2=v1*K₂+v2:=by
          cases vp with
          | false=>simp
          | true=>simp;omega
        have hmod2:((v1*K₂+v2)*2+vp.toNat)%2=vp.toNat:=by
          cases vp <;> simp
        rw [hdiv2,hmod2]
        refine ⟨?_,?_,?_⟩
        . rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt h2,Nat.zero_add]
        . rw [Nat.add_comm,Nat.add_mul_mod_self_right,Zm h2]
        . cases vp <;> decide
      have hex:∃ idx:Fin N,idx.1< N/\v1=(decode idx).1.1 /\
          v2=(decode idx).2.1.1/\vp=(decode idx).2.2 :=
        ⟨target,target.isLt,hdec.1.symm,hdec.2.1.symm,hdec.2.2.symm⟩
      simp only [hex,Zd];have hc:=Classical.choose_spec hex;have e1:(decode (Classical.choose hex)).1=⟨v1,h1⟩:=Zx hc.2.1.symm;have e2:(decode (Classical.choose hex)).2.1=⟨v2,h2⟩:=Zx hc.2.2.1.symm;have e3:(decode (Classical.choose hex)).2.2=vp:=hc.2.2.2.symm;simp only [e1,e2,e3]
    . have hno:¬ ∃ idx:Fin N,idx.1< N/\v1=(decode idx).1.1 /\
          v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=by
        rintro ⟨idx,_,_,h2',_⟩;exact h2 (h2' ▸ (decode idx).2.1.isLt)
      simp only [h2,hno,Zf]
  . have hno:¬ ∃ idx:Fin N,idx.1< N/\v1=(decode idx).1.1 /\
        v2=(decode idx).2.1.1/\vp=(decode idx).2.2:=by
      rintro ⟨idx,_,h1',_,_⟩;exact h1 (h1' ▸ (decode idx).1.isLt)
    simp only [h1,hno,Zf]
 have hp2:=q0.r (q0.r hi₁ hi₂) hp
 exact ((q0.c hp2 hbase).mono (by dsimp [N];omega)).congr (fun x=>by
  have h1:(fun k:Fin d₁ =>
      q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x) ⟨k.1,by omega⟩)=i₁ x:=by
    funext k;simp [q1,k.isLt,show k.1< d₁+d₂ by omega]
  have h2:(fun k:Fin d₂ =>
      q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x) ⟨d₁+k.1,by omega⟩)=i₂ x:=by
    funext k;simp [q1,show d₁+k.1< d₁+d₂ by omega]
  have h3:q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x) ⟨d₁+d₂,by omega⟩=p x:=by
    simp [q1]
  rw [h1,h2,h3])
def z6 (n:ℕ) (k:Fin (2*n)):Bool × Fin n :=
 (decide (k.1 %2=0),⟨k.1/2,by omega⟩)
def xl (n:ℕ) (u:Bool × Fin n):Fin (2*n) :=
 ⟨2*u.2.1+(if u.1 then 0 else 1),by
  have:=u.2.isLt
  cases u.1 with
  | false=>simp;omega
  | true=>simp⟩
lemma pj (n:ℕ) (u:Bool × Fin n):z6 n (xl n u)=u:=by
 rcases u with ⟨b,i⟩
 cases b with
 | false =>
  simp only [z6,xl];apply Prod.ext
  . simp
  . apply Zx;dsimp;omega
 | true =>
  simp only [z6,xl,Zh,Zq];apply Prod.ext
  . simp
  . apply Zx;dsimp;omega
lemma v8 (n:ℕ) (k:Fin (2*n)):xl n (z6 n k)=k:=by
 apply Zx;dsimp [z6,xl]
 by_cases h:k.1 %2=0 <;> simp [h] <;> omega
def q8 (n:ℕ) (hn:0< n) (k:Fin (2*n)) (r:ℕ):Fin (2*n) :=
 ⟨(k.1+r)%(2*n),Nat.mod_lt _ (by omega)⟩
def zs (n:ℕ) (hn:0< n) (k:Fin (2*n)):Fin (2*n) :=
 q8 n hn k 1
lemma yg (n:ℕ) (hn:0< n) (k:Fin (2*n)):q8 n hn k 0=k:=by
 apply Zx;simp [q8,Zm k.isLt]
lemma xc (n:ℕ) (hn:0< n) (k:Fin (2*n)) (a b:ℕ) :
  q8 n hn (q8 n hn k a) b=q8 n hn k (a+b):=by
 apply Zx;simp [q8,Nat.add_assoc]
lemma vr (n:ℕ) (hn:0< n) (k:Fin (2*n)) :
  q8 n hn k (2*n)=k:=by
 apply Zx;simp [q8,Zm k.isLt]
def wt (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (d1 d2:ℕ):ℕ :=
 ((Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y =>
  (∀ k,p k=none\/p k=some (y k)) /\
  (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card=d1 /\
  (Finset.univ.filter (fun i:Fin n =>
   y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card=d2)).card
lemma wu (t:ℕ) (p:(Bool × Fin (t+1))->Option Bool)
   (d:Fin (t+1+1) × Fin (t+1+1)) :
   ((Finset.univ:Finset ((Bool × Fin (t+1))->Bool)).filter (fun x =>
     (∀ u,p u=none\/p u=some (x u)) /\
     (Finset.univ.filter (fun i:Fin (t+1)=>x (false,i)≠x (true,i))).card=d.1.1 /\
     (Finset.univ.filter (fun i:Fin (t+1)=>x (false,i)≠x (true,i+1))).card=d.2.1)).card =
   wt (t+1) (by omega) (fun k=>p (z6 (t+1) k)) d.1.1 d.2.1:=by
 have hn:0< t+1:=by omega
 unfold wt
 refine Finset.card_bij (fun x _=>fun k=>x (z6 (t+1) k)) ?_ ?_ ?_
 . intro x hx;simp only [Zv,Zu,true_and] at hx ⊢
   rcases hx with ⟨hp,hd1,hd2⟩
   refine ⟨fun k=>hp (z6 (t+1) k),?_,?_⟩
   . rw [<- hd1];congr 1;ext i
     have h0:z6 (t+1) ⟨2*i.1,by omega⟩=(true,i):=by
      simp [z6,Fin.ext_iff]
     have h1:z6 (t+1) ⟨2*i.1+1,by omega⟩=(false,i):=by
      simp [z6,Fin.ext_iff];omega
     simp [h0,h1,ne_comm]
   . rw [<- hd2];congr 1;ext i
     have h1:z6 (t+1) ⟨2*i.1+1,by omega⟩=(false,i):=by
      simp [z6,Fin.ext_iff];omega
     have h2:z6 (t+1) (zs (t+1) hn ⟨2*i.1+1,by omega⟩)=(true,i+1):=by
      have hval:(i+1:Fin (t+1)).1=(i.1+1)%(t+1):=by
        change (i.1+(1 %(t+1)))%(t+1)=(i.1+1)%(t+1);rw [Nat.add_mod,Nat.mod_mod,<-Nat.add_mod]
      have heq:(2*i.1+1+1)%(2*(t+1))=2*((i.1+1)%(t+1)):=by
        have:2*i.1+1+1=2*(i.1+1):=by omega
        rw [this,Nat.mul_mod_mul_left]
      apply Prod.ext
      . simp only [zs,q8,z6,heq];simp
      . apply Zx;dsimp only [zs,q8,z6];rw [heq,hval];omega
     simp [h1,h2]
 . intro x₁ _ x₂ _ h;funext u;have:=congrFun h (xl (t+1) u);simpa [pj] using this
 . intro y hy;simp only [Zv,Zu,true_and] at hy
   refine ⟨fun u=>y (xl (t+1) u),?_,by funext k;simp [v8]⟩
   simp only [Zv,Zu,true_and]
   rcases hy with ⟨hp,hd1,hd2⟩
   refine ⟨fun u=>by simpa [pj] using hp (xl (t+1) u),?_,?_⟩
   . rw [<- hd1];congr 1;ext i
     have h0:xl (t+1) (true,i)=⟨2*i.1,by omega⟩:=by apply Zx;simp [xl]
     have h1:xl (t+1) (false,i)=⟨2*i.1+1,by omega⟩:=by apply Zx;simp [xl]
     simp [h0,h1,ne_comm]
   . rw [<- hd2];congr 1;ext i
     have h1:xl (t+1) (false,i)=⟨2*i.1+1,by omega⟩:=by apply Zx;simp [xl]
     have h2:xl (t+1) (true,i+1)=zs (t+1) hn ⟨2*i.1+1,by omega⟩:=by
      apply Zx
      have hval:(i+1:Fin (t+1)).1=(i.1+1)%(t+1):=by
        change (i.1+(1 %(t+1)))%(t+1)=(i.1+1)%(t+1);rw [Nat.add_mod,Nat.mod_mod,<-Nat.add_mod]
      simp only [xl,zs,q8,Zh,Zq,hval]
      have:2*i.1+1+1=2*(i.1+1):=by omega
      rw [this,Nat.mul_mod_mul_left]
     simp [h1,h2]
abbrev j5:=ℕ->ℕ->ℤ
def jk:j5:=fun a b=>if a=0/\b=0 then 1 else 0
def v9 (f g:j5):j5:=fun a b=>f a b+g a b
def wr (c:ℤ) (f:j5):j5:=fun a b=>c*f a b
def qt (f g:j5):j5:=fun a b =>
 ∑ i ∈ Finset.range (a+1),∑ j ∈ Finset.range (b+1),f i j*g (a-i) (b-j)
def wp (f:j5):ℕ->j5
 | 0=>jk
 | k+1=>qt f (wp f k)
def bm (a b:ℕ) (c:ℤ):j5:=fun i j=>if i=a/\j=b then c else 0
def zi (a b:ℕ) (s:ℤ):j5:=v9 jk (bm a b s)
def w9 (l:List j5):j5:=l.foldr qt jk
lemma p8 (f g:j5):v9 f g=v9 g f:=by
 funext a b;exact add_comm _ _
lemma wq (f g:j5):qt f g=qt g f:=by
 funext a b;unfold qt;rw [<- Finset.sum_range_reflect (fun i=>∑ j ∈ Finset.range (b+1),f i j*g (a-i) (b-j)) (a+1)];apply Zc rfl;intro i hi;rw [Finset.mem_range] at hi;rw [<- Finset.sum_range_reflect (fun j=>f (a+1-1-i) j*g (a-(a+1-1-i)) (b-j)) (b+1)];apply Zc rfl;intro j hj;rw [Finset.mem_range] at hj
 have ha1:a+1-1-i=a-i:=by omega
 have ha2:a-(a-i)=i:=by omega
 have hb1:b+1-1-j=b-j:=by omega
 have hb2:b-(b-j)=j:=by omega
 rw [ha1,ha2,hb1,hb2,mul_comm]
lemma jq (f:j5):qt jk f=f:=by
 funext a b;unfold qt jk;rw [Finset.sum_eq_single 0]
 . rw [Finset.sum_eq_single 0]
   . simp
   . intro j _ hj;simp [hj]
   . intro h;exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ b)) h
 . intro i _ hi;apply Finset.sum_eq_zero;intro j _;simp [hi]
 . intro h;exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ a)) h
lemma bt (f:j5):qt f jk=f:=by
 rw [wq,jq]
lemma ca (f g h:j5):qt (v9 f g) h=v9 (qt f h) (qt g h):=by
 funext a b;simp only [qt,v9,add_mul,Finset.sum_add_distrib]
lemma ci (f g h:j5):qt f (v9 g h)=v9 (qt f g) (qt f h):=by
 rw [wq,ca,wq g f,wq h f]
lemma pm (c:ℤ) (f g:j5):qt (wr c f) g=wr c (qt f g):=by
 funext a b;simp only [qt,wr,mul_assoc,Finset.mul_sum]
lemma kg (c:ℤ) (f g:j5):qt f (wr c g)=wr c (qt f g):=by
 rw [wq,pm,wq]
lemma ce (c:ℤ) (f g:j5):wr c (v9 f g)=v9 (wr c f) (wr c g):=by
 funext a b;simp [wr,v9,mul_add]
lemma kh (c₁ c₂:ℤ) (f:j5):wr c₁ (wr c₂ f)=wr (c₁*c₂) f:=by
 funext a b;simp [wr,mul_assoc]
lemma vh {α:Type*} [AddCommMonoid α] (x:ℕ) (F:ℕ->ℕ->α) :
   (∑ i ∈ Finset.range (x+1),∑ p ∈ Finset.range (i+1),F p (i-p)) =
   ∑ p ∈ Finset.range (x+1),∑ u ∈ Finset.range (x-p+1),F p u:=by
 have h1:(∑ i ∈ Finset.range (x+1),∑ p ∈ Finset.range (i+1),F p (i-p)) =
    ∑ i ∈ Finset.range (x+1),∑ p ∈ Finset.range (x+1),if p<=i then F p (i-p) else 0:=by
   apply Zc rfl;intro i hi;rw [Finset.mem_range] at hi;rw [<- Finset.sum_filter];congr 1;ext p;simp only [Zv,Finset.mem_range];omega
 rw [h1,Finset.sum_comm];apply Zc rfl;intro p hp;rw [Finset.mem_range] at hp;rw [<- Finset.sum_filter]
 refine Finset.sum_bij (fun i _=>i-p) ?_ ?_ ?_ ?_
 . intro i hi;simp only [Zv,Finset.mem_range] at hi ⊢;omega
 . intro i₁ hi₁ i₂ hi₂ heq;simp only [Zv,Finset.mem_range] at hi₁ hi₂;omega
 . intro u hu;rw [Finset.mem_range] at hu;exact ⟨p+u,by simp only [Zv,Finset.mem_range];omega,by omega⟩
 . intro i _;rfl
lemma zh (f g h:j5):qt (qt f g) h=qt f (qt g h):=by
 funext a b;unfold qt
 calc
  (∑ i ∈ Finset.range (a+1),∑ j ∈ Finset.range (b+1),
   (∑ p ∈ Finset.range (i+1),∑ q ∈ Finset.range (j+1),f p q*g (i-p) (j-q)) *
   h (a-i) (b-j))
  = ∑ i ∈ Finset.range (a+1),∑ p ∈ Finset.range (i+1),
   ∑ j ∈ Finset.range (b+1),∑ q ∈ Finset.range (j+1),
    f p q*g (i-p) (j-q)*h (a-i) (b-j):=by
   apply Zc rfl;intro i _;simp only [Finset.sum_mul];rw [Finset.sum_comm]
 _=∑ p ∈ Finset.range (a+1),∑ u ∈ Finset.range (a-p+1),
   ∑ j ∈ Finset.range (b+1),∑ q ∈ Finset.range (j+1),
    f p q*g u (j-q)*h (a-(p+u)) (b-j):=by
   have:=vh a (fun p u =>
    ∑ j ∈ Finset.range (b+1),∑ q ∈ Finset.range (j+1),
     f p q*g u (j-q)*h (a-(p+u)) (b-j))
   rw [<- this];apply Zc rfl;intro i hi;apply Zc rfl;intro p hp;rw [Finset.mem_range] at hi hp
   have hpu:p+(i-p)=i:=by omega
   simp only [hpu]
 _=∑ p ∈ Finset.range (a+1),∑ u ∈ Finset.range (a-p+1),
   ∑ q ∈ Finset.range (b+1),∑ v ∈ Finset.range (b-q+1),
    f p q*g u v*h (a-p-u) (b-q-v):=by
   apply Zc rfl;intro p _;apply Zc rfl;intro u _;have:=vh b (fun q v=>f p q*g u v*h (a-p-u) (b-q-v));rw [<- this];apply Zc rfl;intro j hj;apply Zc rfl;intro q hq;rw [Finset.mem_range] at hj hq
   have h1:a-(p+u)=a-p-u:=by omega
   have h2:b-q-(j-q)=b-j:=by omega
   rw [h1,h2]
 _=∑ p ∈ Finset.range (a+1),∑ q ∈ Finset.range (b+1),
   f p q*(∑ u ∈ Finset.range (a-p+1),∑ v ∈ Finset.range (b-q+1),
    g u v*h (a-p-u) (b-q-v)):=by
   apply Zc rfl;intro p _;rw [Finset.sum_comm];apply Zc rfl;intro q _;simp only [Finset.mul_sum,mul_assoc]
lemma kb (f:j5) (m k:ℕ):wp f (m+k)=qt (wp f m) (wp f k):=by
 induction m with
 | zero=>simp [wp,jq]
 | succ m ih =>
  rw [Nat.succ_add,wp,wp,ih,zh]
lemma b9:w9 []=jk:=rfl
lemma wd (f:j5) (l:List j5):w9 (f :: l)=qt f (w9 l):=rfl
lemma xm (l₁ l₂:List j5):w9 (l₁++l₂)=qt (w9 l₁) (w9 l₂):=by
 induction l₁ with
 | nil=>simp [w9,jq]
 | cons f l₁ ih=>rw [List.cons_append,wd,wd,ih,zh]
lemma bu (f g:j5):qt f g 0 0=f 0 0*g 0 0:=by
 simp [qt]
lemma bw (a b:ℕ) (c:ℤ) (g:j5) (A B:ℕ) :
   qt (bm a b c) g A B=if a<=A/\b<=B then c*g (A-a) (B-b) else 0:=by
 unfold qt bm
 by_cases h:a<=A/\b<=B
 . rw [if_pos h];rw [Finset.sum_eq_single a]
   . rw [Finset.sum_eq_single b]
     . simp
     . intro j _ hj;simp [hj]
     . intro hb;exact absurd (Finset.mem_range.mpr (by omega)) hb
   . intro i _ hi;apply Finset.sum_eq_zero;intro j _;simp [hi]
   . intro ha;exact absurd (Finset.mem_range.mpr (by omega)) ha
 . rw [if_neg h];apply Finset.sum_eq_zero;intro i hi;apply Finset.sum_eq_zero;intro j hj;rw [Finset.mem_range] at hi hj
   have hne:¬ (i=a/\j=b):=by omega
   simp [hne]
lemma vs (a b:ℕ) (s:ℤ) (g:j5) (A B:ℕ) :
  qt (zi a b s) g A B=g A B+if a<=A/\b<=B then s*g (A-a) (B-b) else 0:=by
 rw [zi,ca,jq];simp only [v9,bw]
lemma bx (a b:ℕ) (hab:0< a+b) (s:ℤ):zi a b s 0 0=1:=by
 have hne:¬ (0=a/\0=b):=by omega
 simp [zi,v9,jk,bm,hne]
lemma pk (m:ℕ) (hm:0< m) :
   qt (zi m m 1) (zi m m (-1))=zi (2*m) (2*m) (-1):=by
 funext A B;rw [vs];simp only [zi,v9,jk,bm,one_mul]
 by_cases hA:A=0/\B=0
 . rcases hA with ⟨hA0,hB0⟩
   rw [hA0,hB0];simp [show m≠0 by omega,show 0≠m by omega]
 . by_cases h1:A=m/\B=m
   . rcases h1 with ⟨hA1,hB1⟩
     rw [hA1,hB1];simp [show m≠0 by omega,show 0≠m by omega,show m≠2*m by omega]
   . by_cases h2:A=2*m/\B=2*m
     . rcases h2 with ⟨hA2,hB2⟩
       rw [hA2,hB2]
       have hle:m<=2*m/\m<=2*m:=by omega
       simp [hle,show 2*m-m=m by omega,show 2*m≠0 by omega,show m≠0 by omega]
     . split_ifs <;> omega
def jr (f:j5):j5:=fun a b=>((a+b:ℕ):ℤ)*f a b
lemma cf (f g:j5) :
  jr (qt f g)=v9 (qt (jr f) g) (qt f (jr g)):=by
 funext a b;simp only [jr,qt,v9,Finset.mul_sum,<-Finset.sum_add_distrib];apply Zc rfl;intro i hi;apply Zc rfl;intro j hj;rw [Finset.mem_range] at hi hj
 have hab:((a+b:ℕ):ℤ)=((i+j:ℕ):ℤ)+(((a-i)+(b-j):ℕ):ℤ):=by
  omega
 rw [hab];ring
def q9 (a b:ℕ) (s:ℤ):j5:=fun A B =>
 if 0< a+b then
  let j:=(A+B)/(a+b)
  if 0< j/\j*a=A/\j*b=B then
   ((a+b:ℕ):ℤ)*(-1:ℤ)^(j-1)*s^j
  else 0
 else 0
lemma pu (a b:ℕ) (hab:0< a+b) (s:ℤ) :
   qt (zi a b s) (q9 a b s)=jr (zi a b s):=by
 funext A B;rw [vs];simp only [q9,hab,Zh,jr,zi,v9,jk,bm]
 by_cases h0:A=0/\B=0
 . rcases h0 with ⟨hA0,hB0⟩
   rw [hA0,hB0];simp
 . by_cases h1:A=a/\B=b
   . rcases h1 with ⟨hA1,hB1⟩
     rw [hA1,hB1];have hj1:(a+b)/(a+b)=1:=Nat.div_self hab;simp [hj1,show ¬ (a=0/\b=0) by omega]
   . have hR:((A+B:ℕ):ℤ)*((if A=0/\B=0 then (1:ℤ) else 0) +
         if A=a/\B=b then s else 0)=0:=by
       simp [h0,h1]
     rw [hR];set j:=(A+B)/(a+b)
     by_cases hmul:0< j/\j*a=A/\j*b=B
     . rcases hmul with ⟨hjpos,hja,hjb⟩
       have hj2:2<=j:=by
         by_contra hlt
         have hj1:j=1:=by omega
         rw [hj1,one_mul] at hja hjb;exact h1 ⟨hja.symm,hjb.symm⟩
       have hle:a<=A/\b<=B:=by
         constructor
         . rw [<- hja];exact Nat.le_mul_of_pos_left a hjpos
         . rw [<- hjb];exact Nat.le_mul_of_pos_left b hjpos
       have hsubA:A-a=(j-1)*a:=by
         rw [<- hja,Nat.sub_mul,one_mul]
       have hsubB:B-b=(j-1)*b:=by
         rw [<- hjb,Nat.sub_mul,one_mul]
       have hj':(A-a+(B-b))/(a+b)=j-1:=by
         rw [hsubA,hsubB,<-Nat.mul_add,Nat.mul_div_cancel _ hab]
       have hsub_cond:0< (A-a+(B-b))/(a+b) /\
           (A-a+(B-b))/(a+b)*a=A-a /\
           (A-a+(B-b))/(a+b)*b=B-b:=by
         rw [hj'];exact ⟨by omega,hsubA.symm,hsubB.symm⟩
       rw [if_pos ⟨hjpos,hja,hjb⟩,if_pos hle,if_pos hsub_cond,hj']
       have hp1:(-1:ℤ)^(j-1)=(-1:ℤ)*(-1:ℤ)^(j-1-1):=by
         have:j-1=(j-1-1)+1:=by omega
         conv_lhs=>rw [this,pow_succ']
       have hp2:s^j=s*s^(j-1):=by
         have:j=(j-1)+1:=by omega
         conv_lhs=>rw [this,pow_succ']
       rw [hp1,hp2];ring
     . simp only [hmul,Zj,zero_add]
       split_ifs with hle hsub
       . rcases hsub with ⟨hj'pos,hj'a,hj'b⟩
         set j':=(A-a+(B-b))/(a+b)
         have hA:(j'+1)*a=A:=by rw [Nat.add_mul,one_mul,hj'a];omega
         have hB:(j'+1)*b=B:=by rw [Nat.add_mul,one_mul,hj'b];omega
         have hdiv:j=j'+1:=by
           show (A+B)/(a+b)=j'+1
           rw [<- hA,<-hB,<-Nat.mul_add,Nat.mul_div_cancel _ hab]
         exact absurd ⟨by omega,by rw [hdiv];exact hA,by rw [hdiv];exact hB⟩ hmul
       . simp
       . rfl
lemma ba (f g₁ g₂:j5) (hf0:f 0 0=1) (heq:qt f g₁=qt f g₂) :
  g₁=g₂:=by
 have hstrong:∀ s A B,A+B=s->g₁ A B=g₂ A B:=by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
   intro A B hAB;have hEval:=congrFun (congrFun heq A) B;unfold qt at hEval
   have hsplit (g:j5) :
     (∑ i ∈ Finset.range (A+1),∑ j ∈ Finset.range (B+1),f i j*g (A-i) (B-j)) =
     f 0 0*g A B +
     (∑ j ∈ Finset.Ico 1 (B+1),f 0 j*g A (B-j)) +
     (∑ i ∈ Finset.Ico 1 (A+1),∑ j ∈ Finset.range (B+1),f i j*g (A-i) (B-j)):=by
    have hA:Finset.range (A+1)=insert 0 (Finset.Ico 1 (A+1)):=by
     ext x;simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Ico];omega
    have hB:Finset.range (B+1)=insert 0 (Finset.Ico 1 (B+1)):=by
     ext x;simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Ico];omega
    rw [hA,Finset.sum_insert (by simp)]
    conv_lhs=>arg 1;rw [hB,Finset.sum_insert (by simp)]
    simp only [Nat.sub_zero,add_assoc]
   rw [hsplit g₁,hsplit g₂,hf0,one_mul,one_mul] at hEval
   have hsum1:(∑ j ∈ Finset.Ico 1 (B+1),f 0 j*g₁ A (B-j)) =
     (∑ j ∈ Finset.Ico 1 (B+1),f 0 j*g₂ A (B-j)):=by
    apply Zc rfl;intro j hj;rw [Finset.mem_Ico] at hj;rw [ih (A+(B-j)) (by omega) A (B-j) rfl]
   have hsum2:(∑ i ∈ Finset.Ico 1 (A+1),∑ j ∈ Finset.range (B+1),f i j*g₁ (A-i) (B-j)) =
     (∑ i ∈ Finset.Ico 1 (A+1),∑ j ∈ Finset.range (B+1),f i j*g₂ (A-i) (B-j)):=by
    apply Zc rfl;intro i hi;apply Zc rfl;intro j hj;rw [Finset.mem_Ico] at hi;rw [Finset.mem_range] at hj;rw [ih ((A-i)+(B-j)) (by omega) (A-i) (B-j) rfl]
   rw [hsum1,hsum2] at hEval;linarith
 funext A B;exact hstrong (A+B) A B rfl
lemma j3 (L:List (ℕ × ℕ × ℤ)) (hL:∀ t ∈ L,0< t.1+t.2.1) :
  let P:=w9 (L.map fun t=>zi t.1 t.2.1 t.2.2)
  let Q:j5:=fun A B=>(L.map fun t=>q9 t.1 t.2.1 t.2.2 A B).sum
  P 0 0=1/\qt P Q=jr P:=by
 induction L with
 | nil =>
  refine ⟨by simp [w9,jk],?_⟩
  funext A B
  by_cases h:A=0/\B=0
  . rcases h with ⟨rfl,rfl⟩;simp [w9,qt,jr,jk]
  . simp [w9,qt,jr,jk,h]
 | cons t L ih =>
  rcases ih (fun u hu=>hL u (List.mem_cons_of_mem _ hu)) with ⟨hP0,hPE⟩
  have ht:0< t.1+t.2.1:=hL t (List.mem_cons_self ..);dsimp only;constructor
  . rw [List.map_cons,wd,bu,bx t.1 t.2.1 ht,hP0,one_mul]
  . rw [List.map_cons,wd,cf]
    have hQ:(fun A B=>(List.map (fun u:ℕ × ℕ × ℤ=>q9 u.1 u.2.1 u.2.2 A B) (t :: L)).sum) =
      v9 (q9 t.1 t.2.1 t.2.2)
       (fun A B=>(List.map (fun u:ℕ × ℕ × ℤ=>q9 u.1 u.2.1 u.2.2 A B) L).sum):=by
     funext A B;simp [v9]
    rw [hQ,ci]
    have h1:qt (qt (zi t.1 t.2.1 t.2.2) (w9 (L.map fun u=>zi u.1 u.2.1 u.2.2)))
      (q9 t.1 t.2.1 t.2.2) =
      qt (jr (zi t.1 t.2.1 t.2.2)) (w9 (L.map fun u=>zi u.1 u.2.1 u.2.2)):=by
     rw [wq (zi t.1 t.2.1 t.2.2),zh,pu t.1 t.2.1 ht,wq]
    have h2:qt (qt (zi t.1 t.2.1 t.2.2) (w9 (L.map fun u=>zi u.1 u.2.1 u.2.2)))
      (fun A B=>(List.map (fun u:ℕ × ℕ × ℤ=>q9 u.1 u.2.1 u.2.2 A B) L).sum) =
      qt (zi t.1 t.2.1 t.2.2) (jr (w9 (L.map fun u=>zi u.1 u.2.1 u.2.2))):=by
     rw [zh,hPE]
    rw [h1,h2]
lemma pw (L₁ L₂:List (ℕ × ℕ × ℤ))
  (hL₁:∀ t ∈ L₁,0< t.1+t.2.1) (hL₂:∀ t ∈ L₂,0< t.1+t.2.1)
  (heq:w9 (L₁.map fun t=>zi t.1 t.2.1 t.2.2) =
    w9 (L₂.map fun t=>zi t.1 t.2.1 t.2.2)) :
  ∀ A B,(L₁.map fun t=>q9 t.1 t.2.1 t.2.2 A B).sum =
    (L₂.map fun t=>q9 t.1 t.2.1 t.2.2 A B).sum:=by
 rcases j3 L₁ hL₁ with ⟨h0₁,hE₁⟩
 rcases j3 L₂ hL₂ with ⟨_,hE₂⟩
 have hmul:qt (w9 (L₁.map fun t=>zi t.1 t.2.1 t.2.2))
   (fun A B=>(L₁.map fun t=>q9 t.1 t.2.1 t.2.2 A B).sum) =
   qt (w9 (L₁.map fun t=>zi t.1 t.2.1 t.2.2))
   (fun A B=>(L₂.map fun t=>q9 t.1 t.2.1 t.2.2 A B).sum):=by
  rw [hE₁,heq,hE₂]
 have hq:=ba _ _ _ h0₁ hmul;intro A B;exact congrFun (congrFun hq A) B
def yq (p:Polynomial ℤ):j5:=fun a b=>if b=0 then p.coeff a else 0
def yr (p:Polynomial ℤ):j5:=fun a b=>if a=0 then p.coeff b else 0
lemma bf (p q:Polynomial ℤ) :
   qt (yq p) (yq q)=yq (p*q):=by
 funext a b
 by_cases hb:b=0
 . subst hb
   simp only [qt,yq,Zh,show (0+1:ℕ)=1 from rfl,Finset.range_one,
     Finset.sum_singleton,Nat.sub_zero,Polynomial.coeff_mul]
   exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k=>p.coeff i*q.coeff k) a).symm
 . simp only [qt,yq,hb,Zj];apply Finset.sum_eq_zero;intro i _;apply Finset.sum_eq_zero;intro j hj;rw [Finset.mem_range] at hj
   by_cases hj0:j=0
   . subst hj0;simp [hb]
   . simp [hj0]
lemma bg (p q:Polynomial ℤ) :
   qt (yr p) (yr q)=yr (p*q):=by
 funext a b
 by_cases ha:a=0
 . subst ha
   simp only [qt,yr,Zh,show (0+1:ℕ)=1 from rfl,Finset.range_one,
     Finset.sum_singleton,Nat.sub_zero,Polynomial.coeff_mul]
   exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k=>p.coeff i*q.coeff k) b).symm
 . simp only [qt,yr,ha,Zj];apply Finset.sum_eq_zero;intro i hi;apply Finset.sum_eq_zero;intro j _;rw [Finset.mem_range] at hi
   by_cases hi0:i=0
   . subst hi0;simp [ha]
   . simp [hi0]
lemma pn (p q:Polynomial ℤ) (a b:ℕ) :
   qt (yq p) (yr q) a b=p.coeff a*q.coeff b:=by
 unfold qt yq yr;rw [Finset.sum_eq_single a]
 . rw [Finset.sum_eq_single 0]
   . simp
   . intro j _ hj;simp [hj]
   . intro h;exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ b)) h
 . intro i hi hia;rw [Finset.mem_range] at hi;apply Finset.sum_eq_zero;intro j _;simp [show a-i≠0 by omega]
 . intro h;exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self a)) h
lemma cb:yq 1=jk:=by
 funext a b
 by_cases ha:a=0 <;> by_cases hb:b=0 <;> simp [yq,jk,ha,hb,Polynomial.coeff_one]
lemma cc:yr 1=jk:=by
 funext a b
 by_cases ha:a=0 <;> by_cases hb:b=0 <;> simp [yr,jk,ha,hb,Polynomial.coeff_one]
lemma bh (p:Polynomial ℤ) (k:ℕ):wp (yq p) k=yq (p^k):=by
 induction k with
 | zero=>simp [wp,cb]
 | succ k ih=>rw [wp,ih,bf,pow_succ']
lemma bj (p:Polynomial ℤ) (k:ℕ):wp (yr p) k=yr (p^k):=by
 induction k with
 | zero=>simp [wp,cc]
 | succ k ih=>rw [wp,ih,bg,pow_succ']
lemma k2 (s:ℤ):zi 1 0 s=yq (1+Polynomial.C s*Polynomial.X):=by
 funext a b
 by_cases hb:b=0
 . subst hb;simp only [zi,v9,jk,bm,yq,Zh,Polynomial.coeff_add,Polynomial.coeff_one]
   match a with
   | 0=>simp
   | 1=>simp [Polynomial.coeff_mul_X]
   | a+2 =>
    rw [Polynomial.coeff_mul_X,Polynomial.coeff_C];simp
 . simp [zi,v9,jk,bm,yq,hb]
lemma k3 (s:ℤ):zi 0 1 s=yr (1+Polynomial.C s*Polynomial.X):=by
 funext a b
 by_cases ha:a=0
 . subst ha;simp only [zi,v9,jk,bm,yr,Zh,Polynomial.coeff_add,Polynomial.coeff_one]
   match b with
   | 0=>simp
   | 1=>simp [Polynomial.coeff_mul_X]
   | b+2 =>
    rw [Polynomial.coeff_mul_X,Polynomial.coeff_C];simp
 . simp [zi,v9,jk,bm,yr,ha]
noncomputable def kr (n d:ℕ):Polynomial ℤ :=
 (1-Polynomial.X)^d*(1+Polynomial.X)^(n-d)
noncomputable def K1 (n d k:ℕ):ℤ:=(kr n d).coeff k
def vt (n d1 d2:ℕ):j5 :=
 qt
  (qt (wp (zi 1 0 (-1)) d1) (wp (zi 1 0 1) (n-d1)))
  (qt (wp (zi 0 1 (-1)) d2) (wp (zi 0 1 1) (n-d2)))
lemma bz (n d1 d2 a b:ℕ) :
  vt n d1 d2 a b=K1 n d1 a*K1 n d2 b:=by
 have h1m:1+Polynomial.C (-1:ℤ)*Polynomial.X=1-Polynomial.X:=by
  simp [sub_eq_add_neg]
 have h1p:1+Polynomial.C (1:ℤ)*Polynomial.X=1+Polynomial.X:=by simp
 unfold vt K1 kr
 rw [k2 (-1),k2 1,k3 (-1),k3 1,
  h1m,h1p,bh,bh,bj,bj,
  bf,bg,pn]
noncomputable def xh (m:ℕ) (p A B:Polynomial ℤ):Polynomial ℤ :=
 ∑ k ∈ Finset.range (m+1),Polynomial.C (p.coeff k)*A^k*B^(m-k)
lemma k9 (m₁ m₂:ℕ) (p₁ p₂ A B:Polynomial ℤ)
  (hp₁:∀ k,m₁ < k->p₁.coeff k=0) (hp₂:∀ k,m₂ < k->p₂.coeff k=0) :
  xh (m₁+m₂) (p₁*p₂) A B=xh m₁ p₁ A B*xh m₂ p₂ A B:=by
 unfold xh;rw [Finset.sum_mul];simp only [Finset.mul_sum]
 let F:ℕ->ℕ->Polynomial ℤ:=fun i j =>
  (Polynomial.C (p₁.coeff i)*A^i*B^(m₁ - i)) *
  (Polynomial.C (p₂.coeff j)*A^j*B^(m₂ - j))
 have hL :
    (∑ k ∈ Finset.range (m₁+m₂+1),Polynomial.C ((p₁*p₂).coeff k)*A^k*B^(m₁+m₂ - k)) =
    ∑ k ∈ Finset.range (m₁+m₂+1),∑ i ∈ Finset.range (k+1),F i (k-i):=by
  apply Zc rfl;intro k hk;rw [Finset.mem_range] at hk
  rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>p₁.coeff i*p₂.coeff j),
    map_sum,Finset.sum_mul,Finset.sum_mul]
  apply Zc rfl;intro i hi;rw [Finset.mem_range] at hi;dsimp only [F]
  by_cases hi1:i<=m₁
  . by_cases hi2:k-i<=m₂
    . rw [map_mul]
      have hA:A^k=A^i*A^(k-i):=by
       rw [<- pow_add];congr 1;omega
      have hB:B^(m₁+m₂ - k)=B^(m₁ - i)*B^(m₂ - (k-i)):=by
       rw [<- pow_add];congr 1;omega
      rw [hA,hB];ring
    . rw [hp₂ (k-i) (by omega)];simp
  . rw [hp₁ i (by omega)];simp
 rw [hL,vh]
 have houter :
    (∑ i ∈ Finset.range (m₁+m₂+1),∑ u ∈ Finset.range (m₁+m₂ - i+1),F i u) =
    ∑ i ∈ Finset.range (m₁+1),∑ u ∈ Finset.range (m₁+m₂ - i+1),F i u:=by
  symm;apply Finset.sum_subset (Finset.range_mono (by omega));intro i hi hni;simp only [Finset.mem_range] at hi hni;apply Finset.sum_eq_zero;intro u _;simp [F,hp₁ i (by omega)]
 rw [houter];apply Zc rfl;intro i hi;rw [Finset.mem_range] at hi;symm;apply Finset.sum_subset (Finset.range_mono (by omega));intro u hu hnu;simp only [Finset.mem_range] at hu hnu;simp [F,hp₂ u (by omega)]
lemma xn (n d k:ℕ) (hd:d<=n) (hk:n< k) :
  (kr n d).coeff k=0:=by
 apply Polynomial.coeff_eq_zero_of_natDegree_lt
 have h1:((1-Polynomial.X:Polynomial ℤ)^d).natDegree<=d:=by
  calc ((1-Polynomial.X:Polynomial ℤ)^d).natDegree
    <= d*(1-Polynomial.X:Polynomial ℤ).natDegree:=Polynomial.natDegree_pow_le
   _<=d*1:=by
        apply Nat.mul_le_mul_left
        have:(1-Polynomial.X:Polynomial ℤ).natDegree<=max (1:Polynomial ℤ).natDegree (Polynomial.X:Polynomial ℤ).natDegree :=
         Polynomial.natDegree_sub_le _ _
        simpa using this
   _=d:=Nat.mul_one d
 have h2:((1+Polynomial.X:Polynomial ℤ)^(n-d)).natDegree<=n-d:=by
  calc ((1+Polynomial.X:Polynomial ℤ)^(n-d)).natDegree
    <= (n-d)*(1+Polynomial.X:Polynomial ℤ).natDegree:=Polynomial.natDegree_pow_le
   _<=(n-d)*1:=by
        apply Nat.mul_le_mul_left
        have:(1+Polynomial.X:Polynomial ℤ).natDegree<=max (1:Polynomial ℤ).natDegree (Polynomial.X:Polynomial ℤ).natDegree :=
         Polynomial.natDegree_add_le _ _
        simpa using this
   _=n-d:=Nat.mul_one _
 have h3:(kr n d).natDegree<=d+(n-d) :=
  le_trans (Polynomial.natDegree_mul_le) (Nat.add_le_add h1 h2)
 omega
lemma bn (n d:ℕ) (hd:d<=n) :
  xh n (kr n d) (1-Polynomial.X) (1+Polynomial.X) =
  Polynomial.C ((2:ℤ)^n)*Polynomial.X^d:=by
 have h1:∀ m,xh m ((1-Polynomial.X)^m) (1-Polynomial.X) (1+Polynomial.X) =
   (Polynomial.C 2*Polynomial.X)^m:=by
  intro m
  induction m with
  | zero=>simp [xh]
  | succ m ih =>
   have hdeg1:∀ k,1< k->(1-Polynomial.X:Polynomial ℤ).coeff k=0:=by
    intro k hk;apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have:(1-Polynomial.X:Polynomial ℤ).natDegree<=max (1:Polynomial ℤ).natDegree (Polynomial.X:Polynomial ℤ).natDegree :=
     Polynomial.natDegree_sub_le _ _
    simp at this;omega
   have hdegm:∀ k,m< k->((1-Polynomial.X:Polynomial ℤ)^m).coeff k=0:=by
    intro k hk;have:=xn m m k le_rfl hk;simpa [kr] using this
   have hsucc:m+1=1+m:=by omega
   have hpow:(1-Polynomial.X:Polynomial ℤ)^(m+1) =
     (1-Polynomial.X)*(1-Polynomial.X)^m:=pow_succ' _ _
   rw [hpow]
   conv_lhs=>rw [hsucc]
   rw [k9 1 m _ _ _ _ hdeg1 hdegm,ih]
   have hbase:xh 1 (1-Polynomial.X) (1-Polynomial.X) (1+Polynomial.X) =
     Polynomial.C 2*Polynomial.X:=by
    simp only [xh,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
     zero_add,Polynomial.coeff_sub,Polynomial.coeff_X_zero,
     sub_zero,Polynomial.coeff_one,Polynomial.coeff_X_one,Zh]
    simp only [show (1:ℕ)≠0 by decide,Zj,zero_sub,map_one,map_neg,
     pow_zero,pow_one,mul_one,Nat.sub_zero,Nat.sub_self]
    have hC2:(Polynomial.C (2:ℤ):Polynomial ℤ)=1+1:=by
     rw [<- map_one Polynomial.C,<-map_add];norm_num
    rw [hC2];ring
   rw [hbase,<-pow_succ']
 have h2:∀ m,xh m ((1+Polynomial.X)^m) (1-Polynomial.X) (1+Polynomial.X) =
   (Polynomial.C 2)^m:=by
  intro m
  induction m with
  | zero=>simp [xh]
  | succ m ih =>
   have hdeg1:∀ k,1< k->(1+Polynomial.X:Polynomial ℤ).coeff k=0:=by
    intro k hk;apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle:(1+Polynomial.X:Polynomial ℤ).natDegree<=1:=by
     calc (1+Polynomial.X:Polynomial ℤ).natDegree
       <= max (1:Polynomial ℤ).natDegree (Polynomial.X:Polynomial ℤ).natDegree :=
           Polynomial.natDegree_add_le _ _
      _<=1:=by simp
    omega
   have hdegm:∀ k,m< k->((1+Polynomial.X:Polynomial ℤ)^m).coeff k=0:=by
    intro k hk;have:=xn m 0 k (Nat.zero_le m) hk;simpa [kr] using this
   have hsucc:m+1=1+m:=by omega
   have hpow:(1+Polynomial.X:Polynomial ℤ)^(m+1) =
     (1+Polynomial.X)*(1+Polynomial.X)^m:=pow_succ' _ _
   rw [hpow]
   conv_lhs=>rw [hsucc]
   rw [k9 1 m _ _ _ _ hdeg1 hdegm,ih]
   have hbase:xh 1 (1+Polynomial.X) (1-Polynomial.X) (1+Polynomial.X) =
     Polynomial.C 2:=by
    simp only [xh,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
     zero_add,Polynomial.coeff_add,Polynomial.coeff_X_zero,
     Polynomial.coeff_one,add_zero,Polynomial.coeff_X_one,Zh]
    simp only [show (1:ℕ)≠0 by decide,Zj,zero_add,map_one,
     pow_zero,pow_one,mul_one,Nat.sub_zero,Nat.sub_self]
    have hC2:(Polynomial.C (2:ℤ):Polynomial ℤ)=1+1:=by
     rw [<- map_one Polynomial.C,<-map_add];norm_num
    rw [hC2];ring
   rw [hbase,<-pow_succ']
 have hdegd:∀ k,d< k->((1-Polynomial.X:Polynomial ℤ)^d).coeff k=0:=by
  intro k hk;simpa [kr] using xn d d k le_rfl hk
 have hdegnd:∀ k,n-d< k->((1+Polynomial.X:Polynomial ℤ)^(n-d)).coeff k=0:=by
  intro k hk;simpa [kr] using xn (n-d) 0 k (Nat.zero_le _) hk
 have hsplit:n=d+(n-d):=by omega
 unfold kr
 conv_lhs=>arg 1;rw [hsplit]
 rw [k9 d (n-d) _ _ _ _ hdegd hdegnd,h1 d,h2 (n-d)];rw [mul_pow,<-map_pow,<-map_pow]
 have:Polynomial.C ((2:ℤ)^d)*Polynomial.X^d*Polynomial.C ((2:ℤ)^(n-d)) =
   Polynomial.C ((2:ℤ)^d*(2:ℤ)^(n-d))*Polynomial.X^d:=by
  rw [map_mul];ring
 rw [this,<-pow_add,<-hsplit]
lemma p9 (n d r:ℕ) (hd:d<=n) :
  ∑ k ∈ Finset.range (n+1),K1 n d k*K1 n k r=if r=d then (2:ℤ)^n else 0:=by
 have h:=congrArg (fun p:Polynomial ℤ=>p.coeff r) (bn n d hd);rw [xh,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow] at h
 have hsum:(∑ k ∈ Finset.range (n+1),
   Polynomial.C ((kr n d).coeff k)*(1-Polynomial.X)^k*(1+Polynomial.X)^(n-k)).coeff r =
   ∑ k ∈ Finset.range (n+1),K1 n d k*K1 n k r:=by
  change (Polynomial.lcoeff ℤ r) (∑ k ∈ Finset.range (n+1),_)=_;rw [map_sum];apply Zc rfl;intro k _;change (Polynomial.C ((kr n d).coeff k)*(1-Polynomial.X)^k*(1+Polynomial.X)^(n-k)).coeff r=_;rw [mul_assoc,Polynomial.coeff_C_mul];rfl
 rw [hsum] at h;rw [h]
 split_ifs <;> simp
def pb (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool):j5:=fun a b =>
 ∑ d1 ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
  (wt n hn p d1 d2:ℤ)*vt n d1 d2 a b
lemma ki (n:ℕ) (hn:0< n) (p q:Fin (2*n)->Option Bool) :
   pb n hn p=pb n hn q ↔
   ∀ d1 ≤ n,∀ d2 ≤ n,wt n hn p d1 d2=wt n hn q d1 d2:=by
 constructor
 . intro heq r1 hr1 r2 hr2
   have hinv (f:Fin (2*n)->Option Bool) :
      (∑ a ∈ Finset.range (n+1),∑ b ∈ Finset.range (n+1),
        pb n hn f a b*K1 n a r1*K1 n b r2) =
      ((2:ℤ)^n*(2:ℤ)^n)*(wt n hn f r1 r2:ℤ):=by
    unfold pb
    have h1 :
        (∑ a ∈ Finset.range (n+1),∑ b ∈ Finset.range (n+1),
         (∑ d1 ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
           (wt n hn f d1 d2:ℤ)*vt n d1 d2 a b)*K1 n a r1*K1 n b r2) =
        ∑ d1 ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
         (wt n hn f d1 d2:ℤ) *
         ((∑ a ∈ Finset.range (n+1),K1 n d1 a*K1 n a r1) *
          (∑ b ∈ Finset.range (n+1),K1 n d2 b*K1 n b r2)):=by
      simp only [bz,Finset.sum_mul,Finset.mul_sum]
      calc
        (∑ a ∈ Finset.range (n+1),∑ b ∈ Finset.range (n+1),
         ∑ d1 ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
           (wt n hn f d1 d2:ℤ)*(K1 n d1 a*K1 n d2 b)*K1 n a r1*K1 n b r2)
        = ∑ a ∈ Finset.range (n+1),∑ d1 ∈ Finset.range (n+1),
         ∑ b ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
           (wt n hn f d1 d2:ℤ)*(K1 n d1 a*K1 n d2 b)*K1 n a r1*K1 n b r2:=by
         apply Zc rfl;intro a _;exact Finset.sum_comm
      _=∑ d1 ∈ Finset.range (n+1),∑ a ∈ Finset.range (n+1),
         ∑ b ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
           (wt n hn f d1 d2:ℤ)*(K1 n d1 a*K1 n d2 b)*K1 n a r1*K1 n b r2 :=
         Finset.sum_comm
      _=∑ d1 ∈ Finset.range (n+1),∑ a ∈ Finset.range (n+1),
         ∑ d2 ∈ Finset.range (n+1),∑ b ∈ Finset.range (n+1),
           (wt n hn f d1 d2:ℤ)*(K1 n d1 a*K1 n d2 b)*K1 n a r1*K1 n b r2:=by
         apply Zc rfl;intro d1 _;apply Zc rfl;intro a _;exact Finset.sum_comm
      _=∑ d1 ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
         ∑ b ∈ Finset.range (n+1),∑ a ∈ Finset.range (n+1),
           (wt n hn f d1 d2:ℤ)*(K1 n d1 a*K1 n a r1*(K1 n d2 b*K1 n b r2)):=by
         apply Zc rfl;intro d1 _;rw [Finset.sum_comm];apply Zc rfl;intro d2 _;rw [Finset.sum_comm];apply Zc rfl;intro b _;apply Zc rfl;intro a _;ring
    rw [h1];rw [Finset.sum_eq_single r1]
    . rw [Finset.sum_eq_single r2]
      . rw [p9 n r1 r1 hr1,p9 n r2 r2 hr2];simp [mul_comm]
      . intro d2 hd2 hne;rw [Finset.mem_range] at hd2;rw [p9 n d2 r2 (by omega)];simp [Ne.symm hne]
      . intro h;exact absurd (Finset.mem_range.mpr (by omega)) h
    . intro d1 hd1 hne;rw [Finset.mem_range] at hd1;apply Finset.sum_eq_zero;intro d2 _;rw [p9 n d1 r1 (by omega)];simp [Ne.symm hne]
    . intro h;exact absurd (Finset.mem_range.mpr (by omega)) h
   have hp:=hinv p;have hq:=hinv q;rw [heq] at hp
   have hmul:((2:ℤ)^n*(2:ℤ)^n)*(wt n hn p r1 r2:ℤ) =
      ((2:ℤ)^n*(2:ℤ)^n)*(wt n hn q r1 r2:ℤ):=hp.symm.trans hq
   have hpos:((2:ℤ)^n*(2:ℤ)^n)≠0:=by positivity
   have hcast:(wt n hn p r1 r2:ℤ)=(wt n hn q r1 r2:ℤ) :=
    mul_left_cancel₀ hpos hmul
   exact Int.ofNat.inj hcast
 . intro h;funext a b;unfold pb;apply Zc rfl;intro d1 hd1;apply Zc rfl;intro d2 hd2;rw [Finset.mem_range] at hd1 hd2;rw [h d1 (by omega) d2 (by omega)]
lemma yt {l₁ l₂:List j5} (h:l₁.Perm l₂):w9 l₁=w9 l₂:=by
 induction h with
 | nil=>rfl
 | cons x _ ih=>simp [wd,ih]
 | swap x y l=>simp only [wd,<-zh,wq x y]
 | trans _ _ ih₁ ih₂=>exact ih₁.trans ih₂
lemma ve (k:ℕ) (f:j5):w9 (List.replicate k f)=wp f k:=by
 induction k with
 | zero=>rfl
 | succ k ih=>simp [List.replicate_succ,wd,wp,ih]
lemma c9 {α:Type*} (l:List α) (P:α->Bool) (f g:j5) :
  w9 (l.map fun x=>if P x then f else g) =
  qt (wp f (l.countP P)) (wp g (l.length-l.countP P)):=by
 induction l with
 | nil=>simp [w9,wp,jq]
 | cons x xs ih =>
  rw [List.map_cons,wd,ih];have hle:xs.countP P<=xs.length:=List.countP_le_length
  cases hx:P x with
  | true =>
   simp only [Zh,List.countP_cons,hx,List.length_cons]
   have hsub:xs.length+1-(xs.countP P+1)=xs.length-xs.countP P:=by omega
   rw [hsub,wp,zh]
  | false =>
   simp only [Ze,Zj,List.countP_cons,hx,List.length_cons,Zq]
   have hsub:xs.length+1-xs.countP P=(xs.length-xs.countP P)+1:=by omega
   rw [hsub,wp,wq g (qt _ _),zh,wq (wp g _) g]
def wb (col:Bool) (dis:Bool):j5 :=
 match col,dis with
 | false,false=>zi 1 0 1
 | false,true=>zi 1 0 (-1)
 | true,false=>zi 0 1 1
 | true,true=>zi 0 1 (-1)
lemma kz (n:ℕ) (hn:0< n) (y:Fin (2*n)->Bool) :
  w9 ((List.finRange (2*n)).map fun k =>
   wb (decide (k.1 %2=1)) (decide (y k≠y (zs n hn k)))) =
  vt n
   (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card
   (Finset.univ.filter (fun i:Fin n =>
     y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card:=by
 let evens:List (Fin (2*n)):=(List.finRange n).map fun i=>⟨2*i.1,by omega⟩
 let odds:List (Fin (2*n)):=(List.finRange n).map fun i=>⟨2*i.1+1,by omega⟩
 have hperm:(List.finRange (2*n)).Perm (evens++odds):=by
  have hnod1:(List.finRange (2*n)).Nodup:=List.nodup_finRange _
  have hnod2:(evens++odds).Nodup:=by
   rw [List.nodup_append]
   refine ⟨?_,?_,?_⟩
   . exact (List.nodup_finRange n).map (fun a b h=>Zx (by
      have:=congrArg Fin.val h;dsimp at this;omega))
   . exact (List.nodup_finRange n).map (fun a b h=>Zx (by
      have:=congrArg Fin.val h;dsimp at this;omega))
   . intro a ha b hb hab;subst hab;simp only [evens,odds,List.mem_map,List.mem_finRange,true_and] at ha hb
     rcases ha with ⟨i,rfl⟩;rcases hb with ⟨j,hj⟩
     have:=congrArg Fin.val hj;dsimp at this;omega
  exact (List.perm_ext_iff_of_nodup hnod1 hnod2).mpr fun k=>by
   simp only [List.mem_finRange,true_iff,List.mem_append,evens,odds,List.mem_map,true_and]
   by_cases hpar:k.1 %2=0
   . left;exact ⟨⟨k.1/2,by omega⟩,Zx (by dsimp;omega)⟩
   . right;exact ⟨⟨k.1/2,by omega⟩,Zx (by dsimp;omega)⟩
 rw [yt (hperm.map _),Za,xm]
 have hEv :
   w9 (evens.map fun k=>wb (decide (k.1 %2=1)) (decide (y k≠y (zs n hn k)))) =
   qt (wp (zi 1 0 (-1))
      (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card)
     (wp (zi 1 0 1)
      (n-(Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card)):=by
  have hmap:(evens.map fun k=>wb (decide (k.1 %2=1)) (decide (y k≠y (zs n hn k)))) =
     (List.finRange n).map fun i =>
      if decide (y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩) then zi 1 0 (-1) else zi 1 0 1:=by
   simp only [evens,List.map_map];apply List.map_congr_left;intro i _
   have hmod:(2*i.1)%2=0:=by omega
   have hnxt:zs n hn ⟨2*i.1,by omega⟩=⟨2*i.1+1,by omega⟩:=by
     apply Zx;simp [zs,q8,Zm (show 2*i.1+1< 2*n by omega)]
   simp only [Function.comp_apply,hmod,show (0:ℕ)≠1 by decide,decide_false,hnxt]
   cases decide (y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩) <;> rfl
  rw [hmap,c9]
  have hcnt:(List.finRange n).countP (fun i:Fin n=>decide (y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)) =
     (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card:=by
   rw [List.countP_eq_length_filter]
   have hset:(Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)) =
      ((List.finRange n).filter (fun i:Fin n=>decide (y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩))).toFinset:=by
     ext i;simp
   rw [hset,List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  rw [hcnt,List.length_finRange]
 have hOd :
   w9 (odds.map fun k=>wb (decide (k.1 %2=1)) (decide (y k≠y (zs n hn k)))) =
   qt (wp (zi 0 1 (-1))
      (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card)
     (wp (zi 0 1 1)
      (n-(Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card)):=by
  have hmap:(odds.map fun k=>wb (decide (k.1 %2=1)) (decide (y k≠y (zs n hn k)))) =
     (List.finRange n).map fun i =>
      if decide (y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩)) then zi 0 1 (-1) else zi 0 1 1:=by
   simp only [odds,List.map_map];apply List.map_congr_left;intro i _
   have hmod:(2*i.1+1)%2=1:=by omega
   simp only [Function.comp_apply,hmod,decide_true]
   cases decide (y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩)) <;> rfl
  rw [hmap,c9]
  have hcnt:(List.finRange n).countP (fun i:Fin n=>decide (y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))) =
     (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card:=by
   rw [List.countP_eq_length_filter]
   have hset:(Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))) =
      ((List.finRange n).filter (fun i:Fin n=>decide (y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩)))).toFinset:=by
     ext i;simp
   rw [hset,List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  rw [hcnt,List.length_finRange]
 rw [hEv,hOd];rfl
lemma xy (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (a b:ℕ) :
  pb n hn p a b =
  ∑ y ∈ (Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>∀ k,p k=none\/p k=some (y k)),
   w9 ((List.finRange (2*n)).map fun k =>
    wb (decide (k.1 %2=1)) (decide (y k≠y (zs n hn k)))) a b:=by
 let S:=(Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>∀ k,p k=none\/p k=some (y k))
 let f1 (y:Fin (2*n)->Bool):ℕ :=
  (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card
 let f2 (y:Fin (2*n)->Bool):ℕ :=
  (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card
 have hpart :
   (∑ y ∈ S,vt n (f1 y) (f2 y) a b) =
   ∑ d1 ∈ Finset.range (n+1),∑ d2 ∈ Finset.range (n+1),
    (wt n hn p d1 d2:ℤ)*vt n d1 d2 a b:=by
  have hmaps:∀ y ∈ S,(f1 y,f2 y) ∈ (Finset.range (n+1)) ×ˢ (Finset.range (n+1)):=by
   intro y _;simp only [Finset.mem_product,Finset.mem_range]
   have h1:f1 y<=n:=by
    simpa [f1] using Finset.card_filter_le (Finset.univ:Finset (Fin n)) _
   have h2:f2 y<=n:=by
    simpa [f2] using Finset.card_filter_le (Finset.univ:Finset (Fin n)) _
   omega
  rw [<- Finset.sum_product'];rw [<- Finset.sum_fiberwise_of_maps_to hmaps];apply Zc rfl;intro d _
  rcases d with ⟨d1,d2⟩
  have hconst:∑ y ∈ S.filter (fun y=>(f1 y,f2 y)=(d1,d2)),vt n (f1 y) (f2 y) a b =
    ∑ _y ∈ S.filter (fun y=>(f1 y,f2 y)=(d1,d2)),vt n d1 d2 a b:=by
   apply Zc rfl;intro y hy;simp only [Zv,Prod.mk.injEq] at hy;rw [hy.2.1,hy.2.2]
  rw [hconst,Finset.sum_const,nsmul_eq_mul];congr 1;congr 1;unfold wt;congr 1;ext y;simp only [S,f1,f2,Zv,Zu,true_and,Prod.mk.injEq]
 rw [pb,<-hpart];apply Zc rfl;intro y _;rw [kz n hn y]
def wl (c:Bool) (L:ℕ):ℕ × ℕ :=
 if L %2=0 then (L/2,L/2)
 else if c=false then (L/2+1,L/2)
 else (L/2,L/2+1)
def y6 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
  (start:Fin (2*n)) (len:ℕ) (bStart bEnd:Bool):j5:=fun a b =>
 if h0:len=0 then jk a b
 else
  ∑ f ∈ (Finset.univ:Finset (Fin len->Bool)).filter (fun f =>
   f ⟨0,by omega⟩=bStart /\
   ∀ r:Fin len,0< r.1->p (q8 n hn start r.1)=none\/p (q8 n hn start r.1)=some (f r)),
   w9 ((List.finRange len).map fun r =>
    wb (decide ((q8 n hn start r.1).1 %2=1))
     (decide (f r≠if h:r.1+1< len then f ⟨r.1+1,h⟩ else bEnd))) a b
lemma y1 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
  (start:Fin (2*n)) (len:ℕ) (hlen:1<=len) (bStart bEnd:Bool)
  (hunp:∀ r,1<=r->r< len->p (q8 n hn start r)=none) :
  y6 n hn p start len bStart bEnd =
  wr ((2:ℤ)^(len-1))
   (zi (wl (decide (start.1 %2=1)) len).1
         (wl (decide (start.1 %2=1)) len).2
         (if bStart=bEnd then 1 else -1)):=by
 induction len generalizing start bStart with
 | zero=>omega
 | succ m ih =>
  cases m with
  | zero =>
   funext a b
   simp only [y6,Nat.add_eq_zero_iff,one_ne_zero,and_false,Zf,
     Nat.sub_self,pow_zero,wr,one_mul]
   let f0:Fin 1->Bool:=fun _=>bStart
   have hfilt:(Finset.univ:Finset (Fin 1->Bool)).filter (fun f =>
       f ⟨0,by omega⟩=bStart /\
       ∀ r:Fin 1,0< r.1->p (q8 n hn start r.1)=none\/p (q8 n hn start r.1)=some (f r)) =
       {f0}:=by
     ext f;simp only [Zv,Zu,true_and,Finset.mem_singleton];constructor
     . intro ⟨hf0,_⟩;funext r;fin_cases r;exact hf0
     . intro hf;subst hf;exact ⟨rfl,fun r hr=>by omega⟩
   rw [hfilt,Finset.sum_singleton]
   simp only [List.finRange_succ,List.finRange_zero,List.map_nil,List.map_cons,
     wd,b9,bt,Fin.val_zero,yg,Nat.zero_add,
     lt_self_iff_false,Zf,f0]
   by_cases hc:start.1 %2=1
   . simp only [hc,decide_true,wl,Nat.one_mod,one_ne_zero,Zj,
       show (true=false)=False by decide,Nat.zero_div]
     cases bStart <;> cases bEnd <;> simp [wb]
   . simp only [hc,decide_false,wl,Nat.one_mod,one_ne_zero,Zj,
       Zh,Nat.zero_div]
     cases bStart <;> cases bEnd <;> simp [wb]
  | succ m =>
   set L:=m+1
   have hL:1<=L:=by omega
   have hstep :
       y6 n hn p start (L+1) bStart bEnd =
       v9
         (qt (wb (decide (start.1 %2=1)) (decide (bStart≠false)))
              (y6 n hn p (q8 n hn start 1) L false bEnd))
         (qt (wb (decide (start.1 %2=1)) (decide (bStart≠true)))
              (y6 n hn p (q8 n hn start 1) L true bEnd)):=by
     funext a b
     have hS:∀ b1:Bool,
         qt (wb (decide (start.1 %2=1)) (decide (bStart≠b1)))
           (y6 n hn p (q8 n hn start 1) L b1 bEnd) a b =
         ∑ g ∈ (Finset.univ:Finset (Fin L->Bool)).filter (fun g =>
           g ⟨0,by omega⟩=b1 /\
           ∀ r:Fin L,0< r.1->p (q8 n hn (q8 n hn start 1) r.1)=none \/
             p (q8 n hn (q8 n hn start 1) r.1)=some (g r)),
           qt (wb (decide (start.1 %2=1)) (decide (bStart≠b1)))
             (w9 ((List.finRange L).map fun r =>
              wb (decide ((q8 n hn (q8 n hn start 1) r.1).1 %2=1))
               (decide (g r≠if h:r.1+1< L then g ⟨r.1+1,h⟩ else bEnd)))) a b:=by
       intro b1;unfold qt y6;simp only [show L≠0 by omega,Zf,Finset.mul_sum]
       conv_lhs=>arg 2;ext i;rw [Finset.sum_comm]
       rw [Finset.sum_comm]
     rw [v9,hS false,hS true];simp only [y6,show L+1≠0 by omega,Zf]
     let Sfull:=(Finset.univ:Finset (Fin (L+1)->Bool)).filter (fun f =>
       f ⟨0,by omega⟩=bStart /\
       ∀ r:Fin (L+1),0< r.1->p (q8 n hn start r.1)=none\/p (q8 n hn start r.1)=some (f r))
     have hsplit:Sfull=Sfull.filter (fun f=>f ⟨1,by omega⟩=false) ∪
         Sfull.filter (fun f=>f ⟨1,by omega⟩=true):=by
       ext f;simp only [Finset.mem_union,Zv]
       cases f ⟨1,by omega⟩ <;> simp
     have hdisj:Disjoint (Sfull.filter (fun f=>f ⟨1,by omega⟩=false))
         (Sfull.filter (fun f=>f ⟨1,by omega⟩=true)):=by
       rw [Finset.disjoint_filter];intro f _ h1 h2;rw [h1] at h2;cases h2
     change ∑ f ∈ Sfull,_=_;rw [hsplit,Finset.sum_union hdisj]
     have hbranch (b1:Bool) :
         (∑ f ∈ Sfull.filter (fun f=>f ⟨1,by omega⟩=b1),
           w9 ((List.finRange (L+1)).map fun r =>
             wb (decide ((q8 n hn start r.1).1 %2=1))
              (decide (f r≠if h:r.1+1< L+1 then f ⟨r.1+1,h⟩ else bEnd))) a b) =
         ∑ g ∈ (Finset.univ:Finset (Fin L->Bool)).filter (fun g =>
           g ⟨0,by omega⟩=b1 /\
           ∀ r:Fin L,0< r.1->p (q8 n hn (q8 n hn start 1) r.1)=none \/
             p (q8 n hn (q8 n hn start 1) r.1)=some (g r)),
           qt (wb (decide (start.1 %2=1)) (decide (bStart≠b1)))
             (w9 ((List.finRange L).map fun r =>
              wb (decide ((q8 n hn (q8 n hn start 1) r.1).1 %2=1))
               (decide (g r≠if h:r.1+1< L then g ⟨r.1+1,h⟩ else bEnd)))) a b:=by
       refine Finset.sum_bij (fun f _=>fun r:Fin L=>f r.succ) ?_ ?_ ?_ ?_
       . intro f hf;simp only [Sfull,Zv,Zu,true_and] at hf ⊢
         refine ⟨hf.2,fun r hr=>?_⟩
         rw [xc];simpa [Nat.add_comm] using hf.1.2 r.succ (by simp)
       . intro f₁ hf₁ f₂ hf₂ heq;simp only [Sfull,Zv,Zu,true_and] at hf₁ hf₂;funext r
         refine Fin.cases ?_ ?_ r
         . exact hf₁.1.1.trans hf₂.1.1.symm
         . intro j;exact congrFun heq j
       . intro g hg;simp only [Zv,Zu,true_and] at hg
         let f:Fin (L+1)->Bool:=fun r=>Fin.cases bStart g r
         refine ⟨f,?_,?_⟩
         . simp only [Sfull,Zv,Zu,true_and]
           refine ⟨⟨rfl,fun r hr=>?_⟩,hg.1⟩
           have hr_pos:1<=r.1:=by omega
           have hlt:r.1< L+1:=r.isLt;left;exact hunp r.1 hr_pos hlt
         . funext r;rfl
       . intro f hf;simp only [Sfull,Zv,Zu,true_and] at hf
         refine congrFun (congrFun ?_ a) b
         rw [List.finRange_succ,List.map_cons,wd,List.map_map];congr 1
         . congr 1
           . simp [yg]
           . simp only [Fin.val_zero,Nat.zero_add,show 1< L+1 by omega,Zd];have hf0:f 0=bStart:=hf.1.1;have hf1:f ⟨1,by omega⟩=b1:=hf.2;rw [hf0,hf1]
         . congr 1;apply List.map_congr_left;intro r _;simp only [Function.comp_apply,Fin.val_succ,xc];rw [Nat.add_comm 1 r.1];congr 1
           by_cases hlt:r.1+1< L
           . simp [hlt,show r.1+1+1< L+1 by omega]
           . simp [hlt,show ¬ (r.1+1+1< L+1) by omega]
     rw [hbranch false,hbranch true]
   rw [hstep]
   have hunp':∀ r,1<=r->r< L->p (q8 n hn (q8 n hn start 1) r)=none:=by
     intro r hr1 hr2;rw [xc];exact hunp (1+r) (by omega) (by omega)
   rw [ih (q8 n hn start 1) hL false hunp',ih (q8 n hn start 1) hL true hunp']
   have hcol_flip:decide ((q8 n hn start 1).1 %2=1)=!(decide (start.1 %2=1)):=by
     apply Bool.eq_iff_iff.mpr;simp only [decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not];have hval:(q8 n hn start 1).1=(start.1+1)%(2*n):=rfl;rw [hval,Nat.mod_mul_right_mod (start.1+1) 2 n];omega
   rw [hcol_flip];set c:=decide (start.1 %2=1);set ab:=wl (!c) L
   have hcomb (z_a z_b:ℕ) (hs:Bool) :
       v9
         (qt (zi z_a z_b 1) (wr ((2:ℤ)^(L-1)) (zi ab.1 ab.2 (if hs then 1 else -1))))
         (qt (zi z_a z_b (-1)) (wr ((2:ℤ)^(L-1)) (zi ab.1 ab.2 (if hs then -1 else 1)))) =
       wr ((2:ℤ)^L) (zi (ab.1+z_a) (ab.2+z_b) (if hs then 1 else -1)):=by
     rw [kg,kg,<-ce]
     have hpow:(2:ℤ)^L=(2:ℤ)^(L-1)*2:=by
       have:L=(L-1)+1:=by omega
       conv_lhs=>rw [this,pow_succ]
     rw [hpow,<-kh];congr 1;funext A B;rw [v9,vs,vs];simp only [wr,zi,v9,jk,bm]
     cases hs <;> (split_ifs <;> try omega <;> ring)
   have hab_eq:(wl c (L+1)).1=ab.1+(if c=false then 1 else 0) /\
       (wl c (L+1)).2=ab.2+(if c=false then 0 else 1):=by
     dsimp only [ab,wl]
     by_cases hpar:L %2=0
     . have hpar':(L+1)%2≠0:=by omega
       cases c <;> simp [hpar,hpar'] <;> omega
     . have hpar':(L+1)%2=0:=by omega
       cases c <;> simp [hpar,hpar'] <;> omega
   have hLsub:L+1-1=L:=by omega
   rw [hLsub,hab_eq.1,hab_eq.2]
   cases hc:c with
   | false =>
     simp only [Zh]
     cases bStart <;> cases bEnd
     . simpa [wb] using hcomb 1 0 true
     . simpa [wb] using hcomb 1 0 false
     . rw [p8];simpa [wb] using hcomb 1 0 false
     . rw [p8];simpa [wb] using hcomb 1 0 true
   | true =>
     simp only [show (true=false)=False by decide,Zj]
     cases bStart <;> cases bEnd
     . simpa [wb] using hcomb 0 1 true
     . simpa [wb] using hcomb 0 1 false
     . rw [p8];simpa [wb] using hcomb 0 1 false
     . rw [p8];simpa [wb] using hcomb 0 1 true
lemma px (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
   (start:Fin (2*n)) (t len:ℕ) (ht0:0< t) (htl:t< len)
   (bStart bMid bEnd:Bool) (hmid:p (q8 n hn start t)=some bMid) :
   y6 n hn p start len bStart bEnd =
   qt (y6 n hn p start t bStart bMid)
        (y6 n hn p (q8 n hn start t) (len-t) bMid bEnd):=by
 funext a b
 let S:=(Finset.univ:Finset (Fin len->Bool)).filter (fun f =>
   f ⟨0,by omega⟩=bStart /\
   ∀ r:Fin len,0< r.1->p (q8 n hn start r.1)=none\/p (q8 n hn start r.1)=some (f r))
 let S₁:=(Finset.univ:Finset (Fin t->Bool)).filter (fun f =>
   f ⟨0,by omega⟩=bStart /\
   ∀ r:Fin t,0< r.1->p (q8 n hn start r.1)=none\/p (q8 n hn start r.1)=some (f r))
 let S₂:=(Finset.univ:Finset (Fin (len-t)->Bool)).filter (fun f =>
   f ⟨0,by omega⟩=bMid /\
   ∀ r:Fin (len-t),0< r.1 ->
     p (q8 n hn (q8 n hn start t) r.1)=none \/
     p (q8 n hn (q8 n hn start t) r.1)=some (f r))
 let wFull (f:Fin len->Bool):j5 :=
   w9 ((List.finRange len).map fun r =>
     wb (decide ((q8 n hn start r.1).1 %2=1))
       (decide (f r≠if h:r.1+1< len then f ⟨r.1+1,h⟩ else bEnd)))
 let w1 (f:Fin t->Bool):j5 :=
   w9 ((List.finRange t).map fun r =>
     wb (decide ((q8 n hn start r.1).1 %2=1))
       (decide (f r≠if h:r.1+1< t then f ⟨r.1+1,h⟩ else bMid)))
 let w2 (f:Fin (len-t)->Bool):j5 :=
   w9 ((List.finRange (len-t)).map fun r =>
     wb (decide ((q8 n hn (q8 n hn start t) r.1).1 %2=1))
       (decide (f r≠if h:r.1+1< len-t then f ⟨r.1+1,h⟩ else bEnd)))
 have hL:y6 n hn p start len bStart bEnd a b=∑ f ∈ S,wFull f a b:=by
   simp only [y6,show len≠0 by omega,Zf];rfl
 have hR:qt (y6 n hn p start t bStart bMid)
     (y6 n hn p (q8 n hn start t) (len-t) bMid bEnd) a b =
     ∑ fg ∈ S₁ ×ˢ S₂,qt (w1 fg.1) (w2 fg.2) a b:=by
   rw [Finset.sum_product];unfold qt y6;simp only [show t≠0 by omega,show len-t≠0 by omega,Zf]
   calc
     (∑ i ∈ Finset.range (a+1),∑ j ∈ Finset.range (b+1),
       (∑ f₁ ∈ S₁,w1 f₁ i j)*(∑ f₂ ∈ S₂,w2 f₂ (a-i) (b-j)))
     = ∑ i ∈ Finset.range (a+1),∑ j ∈ Finset.range (b+1),
       ∑ f₁ ∈ S₁,∑ f₂ ∈ S₂,w1 f₁ i j*w2 f₂ (a-i) (b-j):=by
       apply Zc rfl;intro i _;apply Zc rfl;intro j _;rw [Finset.sum_mul];apply Zc rfl;intro f₁ _;rw [Finset.mul_sum]
   _=∑ i ∈ Finset.range (a+1),∑ f₁ ∈ S₁,
       ∑ j ∈ Finset.range (b+1),∑ f₂ ∈ S₂,w1 f₁ i j*w2 f₂ (a-i) (b-j):=by
       apply Zc rfl;intro i _;exact Finset.sum_comm
   _=∑ f₁ ∈ S₁,∑ i ∈ Finset.range (a+1),
       ∑ j ∈ Finset.range (b+1),∑ f₂ ∈ S₂,w1 f₁ i j*w2 f₂ (a-i) (b-j) :=
       Finset.sum_comm
   _=∑ f₁ ∈ S₁,∑ i ∈ Finset.range (a+1),
       ∑ f₂ ∈ S₂,∑ j ∈ Finset.range (b+1),w1 f₁ i j*w2 f₂ (a-i) (b-j):=by
       apply Zc rfl;intro f₁ _;apply Zc rfl;intro i _;exact Finset.sum_comm
   _=∑ f₁ ∈ S₁,∑ f₂ ∈ S₂,
       ∑ i ∈ Finset.range (a+1),∑ j ∈ Finset.range (b+1),w1 f₁ i j*w2 f₂ (a-i) (b-j):=by
       apply Zc rfl;intro f₁ _;exact Finset.sum_comm
 rw [hL,hR]
 refine Finset.sum_bij (fun f _ =>
   (fun r:Fin t=>f ⟨r.1,by omega⟩,fun r:Fin (len-t)=>f ⟨t+r.1,by omega⟩))
   ?_ ?_ ?_ ?_
 . intro f hf;simp only [S,S₁,S₂,Finset.mem_product,Zv,Zu,true_and] at hf ⊢
   have hft:f ⟨t,htl⟩=bMid:=by
     have:=hf.2 ⟨t,htl⟩ ht0;rw [hmid] at this
     rcases this with h | h
     . cases h
     . exact Option.some.inj h.symm
   refine ⟨⟨hf.1,fun r hr=>hf.2 ⟨r.1,by omega⟩ hr⟩,
          ⟨by simpa using hft,fun r hr=>?_⟩⟩
   rw [xc];have hrl:=r.isLt;exact hf.2 ⟨t+r.1,by omega⟩ (show 0< t+r.1 by omega)
 . intro f₁ _ f₂ _ heq;simp only [Prod.mk.injEq] at heq;funext r
   by_cases hr:r.1< t
   . exact congrFun heq.1 ⟨r.1,hr⟩
   . have:=congrFun heq.2 ⟨r.1-t,by omega⟩;dsimp only at this;have hidx:(⟨t+(r.1-t),by omega⟩:Fin len)=r:=Zx (by dsimp;omega);rwa [hidx] at this
 . intro fg hfg;simp only [S₁,S₂,Finset.mem_product,Zv,Zu,true_and] at hfg
   let f:Fin len->Bool:=fun r =>
     if hr:r.1< t then fg.1 ⟨r.1,hr⟩ else fg.2 ⟨r.1-t,by omega⟩
   refine ⟨f,?_,?_⟩
   . simp only [S,Zv,Zu,true_and]
     refine ⟨by simp [f,ht0,hfg.1.1],fun r hr=>?_⟩
     by_cases hlt:r.1< t
     . simp only [f,hlt,Zd];exact hfg.1.2 ⟨r.1,hlt⟩ hr
     . simp only [f,hlt,Zf]
       by_cases heqt:r.1=t
       . have hreq:q8 n hn start r.1=q8 n hn start t:=by rw [heqt]
         have h0:(⟨r.1-t,by omega⟩:Fin (len-t))=⟨0,by omega⟩:=Zx (by dsimp;omega);rw [hreq,hmid,h0,hfg.2.1];right;rfl
       . have hrl:=r.isLt;have h2:=hfg.2.2 ⟨r.1-t,by omega⟩ (show 0< r.1-t by omega);rw [xc,show t+(r.1-t)=r.1 by omega] at h2;exact h2
   . apply Prod.ext
     . funext r;simp [f,r.isLt]
     . funext r;simp [f]
 . intro f hf;simp only [S,Zv,Zu,true_and] at hf
   have hft:f ⟨t,htl⟩=bMid:=by
     have:=hf.2 ⟨t,htl⟩ ht0;rw [hmid] at this
     rcases this with h | h
     . cases h
     . exact Option.some.inj h.symm
   refine congrFun (congrFun ?_ a) b
   dsimp only [wFull,w1,w2]
   have hsplit_fr:List.finRange len =
       (List.finRange t).map (fun r:Fin t=>(⟨r.1,by omega⟩:Fin len)) ++
       (List.finRange (len-t)).map (fun r:Fin (len-t)=>(⟨t+r.1,by omega⟩:Fin len)):=by
     apply List.ext_getElem
     . simp;omega
     . intro i hi1 hi2;simp only [List.length_finRange] at hi1;rw [Zg]
       by_cases hlt:i< t
       . rw [List.getElem_append_left (by simp [hlt]),List.getElem_map,Zg];rfl
       . rw [List.getElem_append_right (by simp;omega),List.getElem_map,Zg];apply Zx;simp;omega
   rw [hsplit_fr,Za,xm,List.map_map,List.map_map];congr 1
   . congr 1;apply List.map_congr_left;intro r _;simp only [Function.comp_apply];congr 1
     by_cases hlt:r.1+1< t
     . simp [hlt,show r.1+1< len by omega]
     . have heq:r.1+1=t:=by omega
       simp only [hlt,Zf,show r.1+1< len by omega,Zd];have:(⟨r.1+1,by omega⟩:Fin len)=⟨t,htl⟩:=Zx heq;rw [this,hft]
   . congr 1;apply List.map_congr_left;intro r _;simp only [Function.comp_apply,xc];congr 1
     by_cases hlt:r.1+1< len-t
     . have hidx:(⟨t+r.1+1,by omega⟩:Fin len)=⟨t+(r.1+1),by omega⟩ :=
         Zx (by dsimp;omega)
       simp only [hlt,show t+r.1+1< len by omega,Zd,hidx]
     . simp [hlt,show ¬ (t+r.1+1< len) by omega]
lemma xz (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
   (k₀:Fin (2*n)) (b₀:Bool) (hk₀:p k₀=some b₀) :
   pb n hn p=y6 n hn p k₀ (2*n) b₀ b₀:=by
 funext a b;rw [xy n hn p a b];simp only [y6,show 2*n≠0 by omega,Zf]
 refine Finset.sum_bij (fun y _=>fun r:Fin (2*n)=>y (q8 n hn k₀ r.1)) ?_ ?_ ?_ ?_
 . intro y hy;simp only [Zv,Zu,true_and] at hy ⊢
   refine ⟨?_,fun r _=>hy (q8 n hn k₀ r.1)⟩
   have:=hy k₀;rw [hk₀] at this
   rcases this with h | h
   . cases h
   . simp only [Fin.val_zero,yg];exact Option.some.inj h.symm
 . intro y₁ _ y₂ _ heq;funext k
   let r:Fin (2*n):=⟨(2*n+k.1-k₀.1)%(2*n),Nat.mod_lt _ (by omega)⟩
   have hr:q8 n hn k₀ r.1=k:=by
     apply Zx;simp only [q8,r]
     have h1:(k₀.1+(2*n+k.1-k₀.1)%(2*n))%(2*n) =
         (k₀.1+(2*n+k.1-k₀.1))%(2*n):=by
       rw [Nat.add_mod,Nat.mod_mod,<-Nat.add_mod]
     rw [h1]
     have h2:k₀.1+(2*n+k.1-k₀.1)=2*n+k.1:=by have:=k₀.isLt;omega
     rw [h2,Nat.add_mod_left,Zm k.isLt]
   have:=congrFun heq r;rwa [hr] at this
 . intro f hf;simp only [Zv,Zu,true_and] at hf
   let y:Fin (2*n)->Bool:=fun k =>
     f ⟨(2*n+k.1-k₀.1)%(2*n),Nat.mod_lt _ (by omega)⟩
   have hy_add:∀ r:Fin (2*n),y (q8 n hn k₀ r.1)=f r:=by
     intro r;dsimp only [y,q8];congr 1;apply Zx;dsimp only
     have hsub:(2*n+(k₀.1+r.1)%(2*n)-k₀.1)%(2*n)=r.1:=by
       have hklt:=k₀.isLt;have hrlt:=r.isLt
       by_cases hlt:k₀.1+r.1< 2*n
       . rw [Zm hlt]
         have:2*n+(k₀.1+r.1)-k₀.1=2*n+r.1:=by omega
         rw [this,Nat.add_mod_left,Zm hrlt]
       . have hmod:(k₀.1+r.1)%(2*n)=k₀.1+r.1-2*n:=by
          rw [Nat.mod_eq_sub_mod (by omega),Zm (by omega)]
         rw [hmod]
         have:2*n+(k₀.1+r.1-2*n)-k₀.1=r.1:=by omega
         rw [this,Zm hrlt]
     exact hsub
   refine ⟨y,?_,by funext r;exact hy_add r⟩
   simp only [Zv,Zu,true_and];intro k
   let r:Fin (2*n):=⟨(2*n+k.1-k₀.1)%(2*n),Nat.mod_lt _ (by omega)⟩
   have hr:q8 n hn k₀ r.1=k:=by
     apply Zx;simp only [q8,r]
     have h1:(k₀.1+(2*n+k.1-k₀.1)%(2*n))%(2*n) =
         (k₀.1+(2*n+k.1-k₀.1))%(2*n):=by
       rw [Nat.add_mod,Nat.mod_mod,<-Nat.add_mod]
     rw [h1]
     have h2:k₀.1+(2*n+k.1-k₀.1)=2*n+k.1:=by have:=k₀.isLt;omega
     rw [h2,Nat.add_mod_left,Zm k.isLt]
   rw [<- hr,hy_add r]
   by_cases hr0:r.1=0
   . have hr_eq:r=⟨0,by omega⟩:=Zx hr0;rw [hr_eq,show (⟨0,by omega⟩:Fin (2*n)).1=0 from rfl,yg,hf.1,hk₀];right;rfl
   . exact hf.2 r (by omega)
 . intro y hy;simp only [Zv,Zu,true_and] at hy
   have hy0:y k₀=b₀:=by
     have:=hy k₀;rw [hk₀] at this
     rcases this with h | h
     . cases h
     . exact Option.some.inj h.symm
   refine congrFun (congrFun ?_ a) b
   have hperm:(List.finRange (2*n)).Perm
       ((List.finRange (2*n)).map fun r:Fin (2*n)=>q8 n hn k₀ r.1):=by
     have hnod1:=List.nodup_finRange (2*n)
     have hnod2:((List.finRange (2*n)).map fun r:Fin (2*n)=>q8 n hn k₀ r.1).Nodup:=by
       apply hnod1.map;intro r₁ r₂ h
       have hv:=congrArg Fin.val h
       simp only [q8] at hv;have hr1:=r₁.isLt;have hr2:=r₂.isLt;have hk:=k₀.isLt;apply Zx
       by_cases h1:k₀.1+r₁.1< 2*n <;> by_cases h2:k₀.1+r₂.1< 2*n
       . rw [Zm h1,Zm h2] at hv;omega
       . rw [Zm h1,Nat.mod_eq_sub_mod (by omega),Zm (by omega)] at hv;omega
       . rw [Nat.mod_eq_sub_mod (by omega),Zm (by omega),Zm h2] at hv;omega
       . rw [Nat.mod_eq_sub_mod (by omega),Zm (by omega),
           Nat.mod_eq_sub_mod (by omega),Zm (by omega)] at hv;omega
     exact (List.perm_ext_iff_of_nodup hnod1 hnod2).mpr fun k=>by
       simp only [List.mem_finRange,true_iff,List.mem_map,true_and]
       refine ⟨⟨(2*n+k.1-k₀.1)%(2*n),Nat.mod_lt _ (by omega)⟩,?_⟩
       apply Zx;simp only [q8]
       have h1:(k₀.1+(2*n+k.1-k₀.1)%(2*n))%(2*n) =
          (k₀.1+(2*n+k.1-k₀.1))%(2*n):=by
         rw [Nat.add_mod,Nat.mod_mod,<-Nat.add_mod]
       rw [h1]
       have h2:k₀.1+(2*n+k.1-k₀.1)=2*n+k.1:=by have:=k₀.isLt;omega
       rw [h2,Nat.add_mod_left,Zm k.isLt]
   rw [yt (hperm.map _),List.map_map];congr 1;apply List.map_congr_left;intro r _;simp only [Function.comp_apply];congr 1
   by_cases hlt:r.1+1< 2*n
   . simp only [hlt,Zd,zs,xc]
   . have heq:r.1+1=2*n:=by omega
     simp only [hlt,Zf];rw [zs,xc,heq,vr,hy0]
lemma cg (n:ℕ) (hn:0< n) :
  pb n hn (fun _=>none)=wr ((2:ℤ)^(2*n)) (zi n n 1):=by
 have hsplit:pb n hn (fun _=>none) =
   v9 (pb n hn (fun k=>if k=⟨0,by omega⟩ then some false else none))
        (pb n hn (fun k=>if k=⟨0,by omega⟩ then some true else none)):=by
  funext a b;rw [v9,xy,xy,xy]
  have hU:(Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun _=>True) =
     ((Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>y ⟨0,by omega⟩=false)) ∪
     ((Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>y ⟨0,by omega⟩=true)):=by
   ext y;simp only [Finset.mem_union,Zv,Zu,true_and]
   cases y ⟨0,by omega⟩ <;> simp
  have hdisj:Disjoint
     ((Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>y ⟨0,by omega⟩=false))
     ((Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>y ⟨0,by omega⟩=true)):=by
   rw [Finset.disjoint_filter];intro y _ h1 h2;rw [h1] at h2;cases h2
  have h0:(Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>∀ k,(none:Option Bool)=none\/none=some (y k)) =
     (Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun _=>True):=by
   ext y;simp
  have h1 (b0:Bool) :
     (Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y =>
       ∀ k,(if k=⟨0,by omega⟩ then some b0 else none)=none \/
         (if k=⟨0,by omega⟩ then some b0 else none)=some (y k)) =
     (Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y=>y ⟨0,by omega⟩=b0):=by
   ext y;simp only [Zv,Zu,true_and];constructor
   . intro h;have:=h ⟨0,by omega⟩;simp only [Zh] at this
     rcases this with hc | hc
     . cases hc
     . exact (Option.some.inj hc).symm
   . intro hb k
     by_cases hk:k=⟨0,by omega⟩
     . subst hk;right;simp [hb]
     . left;simp [hk]
  rw [h0,h1 false,h1 true,hU,Finset.sum_union hdisj]
 rw [hsplit]
 rw [xz n hn _ ⟨0,by omega⟩ false (by simp),
   xz n hn _ ⟨0,by omega⟩ true (by simp)]
 have hunp (b0:Bool):∀ r,1<=r->r< 2*n ->
   (if q8 n hn ⟨0,by omega⟩ r=⟨0,by omega⟩ then some b0 else none)=none:=by
  intro r hr1 hr2
  have hne:q8 n hn ⟨0,by omega⟩ r≠⟨0,by omega⟩:=by
   intro h
   have hv:=congrArg Fin.val h
   simp only [q8,Nat.zero_add,Zm hr2] at hv;omega
  simp [hne]
 rw [y1 n hn _ ⟨0,by omega⟩ (2*n) (by omega) false false (hunp false),
   y1 n hn _ ⟨0,by omega⟩ (2*n) (by omega) true true (hunp true)]
 have hac:wl (decide ((⟨0,by omega⟩:Fin (2*n)).1 %2=1)) (2*n)=(n,n):=by
  simp [wl]
 rw [hac];funext a b;simp only [v9,wr,Zh]
 have hpow:(2:ℤ)^(2*n)=(2:ℤ)^(2*n-1)+(2:ℤ)^(2*n-1):=by
  have:2*n=(2*n-1)+1:=by omega
  conv_lhs=>rw [this,pow_succ]
  ring
 rw [hpow];ring
def xd (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ):List (ℕ × ℕ × ℤ) :=
 ((List.finRange n).flatMap fun j =>
  List.replicate (oddC j false false) (j.1+1,j.1,1) ++
  List.replicate (oddC j false true) (j.1+1,j.1,-1) ++
  List.replicate (oddC j true false) (j.1,j.1+1,1) ++
  List.replicate (oddC j true true) (j.1,j.1+1,-1)) ++
 ((List.finRange n).flatMap fun j =>
  List.replicate (ep j) (j.1+1,j.1+1,1) ++
  List.replicate (em j) (j.1+1,j.1+1,-1))
def wy (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ):j5 :=
 w9 ((xd n oddC ep em).map fun t=>zi t.1 t.2.1 t.2.2)
lemma p2 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) :
  ∀ t ∈ xd n oddC ep em,0< t.1+t.2.1:=by
 intro t ht
 simp only [xd,List.mem_append,List.mem_flatMap,List.mem_finRange,true_and,
  List.mem_replicate] at ht
 rcases ht with ⟨j,(((⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩) | ⟨_,rfl⟩)⟩ | ⟨j,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ <;> (dsimp;omega)
lemma vf (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ)
   (F:ℕ × ℕ × ℤ->ℤ) :
   ((xd n oddC ep em).map F).sum =
   (∑ j:Fin n,
    ((oddC j false false:ℤ)*F (j.1+1,j.1,1) +
     (oddC j false true:ℤ)*F (j.1+1,j.1,-1) +
     (oddC j true false:ℤ)*F (j.1,j.1+1,1) +
     (oddC j true true:ℤ)*F (j.1,j.1+1,-1))) +
   (∑ j:Fin n,
    ((ep j:ℤ)*F (j.1+1,j.1+1,1) +
     (em j:ℤ)*F (j.1+1,j.1+1,-1))):=by
 have hrep (k:ℕ) (x:ℕ × ℕ × ℤ):((List.replicate k x).map F).sum=(k:ℤ)*F x:=by
   rw [Zy,Zz,nsmul_eq_mul]
 have hfin (g:Fin n->ℤ):((List.finRange n).map g).sum=∑ j:Fin n,g j:=by
   rw [<- Fin.sum_univ_def]
 have hflat (l:List (Fin n)) (g:Fin n->List ℤ) :
    (l.flatMap g).sum=(l.map fun x=>(g x).sum).sum:=by
   induction l with
   | nil=>simp
   | cons x xs ih=>simp [List.flatMap_cons,Zs,ih]
 unfold xd;rw [Za,Zs];congr 1
 . rw [List.map_flatMap,hflat (List.finRange n) _,hfin];apply Zc rfl;intro j _;simp only [Za,Zs,hrep]
 . rw [List.map_flatMap,hflat (List.finRange n) _,hfin];apply Zc rfl;intro j _;simp only [Za,Zs,hrep]
lemma va (n:ℕ)
   (oddC₁ oddC₂:Fin n->Bool->Bool->ℕ) (ep₁ em₁ ep₂ em₂:Fin n->ℕ)
   (hred₁:∀ j:Fin n,ep₁ j=0\/em₁ j=0)
   (hred₂:∀ j:Fin n,ep₂ j=0\/em₂ j=0)
   (heq:wy n oddC₁ ep₁ em₁=wy n oddC₂ ep₂ em₂) :
   oddC₁=oddC₂/\ep₁=ep₂/\em₁=em₂:=by
 have hlog:=pw (xd n oddC₁ ep₁ em₁) (xd n oddC₂ ep₂ em₂)
   (p2 n oddC₁ ep₁ em₁) (p2 n oddC₂ ep₂ em₂) heq
 have hlog_eval (A B:ℕ) :
     (∑ j:Fin n,
       ((oddC₁ j false false:ℤ)*q9 (j.1+1) j.1 1 A B +
        (oddC₁ j false true:ℤ)*q9 (j.1+1) j.1 (-1) A B +
        (oddC₁ j true false:ℤ)*q9 j.1 (j.1+1) 1 A B +
        (oddC₁ j true true:ℤ)*q9 j.1 (j.1+1) (-1) A B)) +
     (∑ j:Fin n,
       ((ep₁ j:ℤ)*q9 (j.1+1) (j.1+1) 1 A B +
        (em₁ j:ℤ)*q9 (j.1+1) (j.1+1) (-1) A B)) =
     (∑ j:Fin n,
       ((oddC₂ j false false:ℤ)*q9 (j.1+1) j.1 1 A B +
        (oddC₂ j false true:ℤ)*q9 (j.1+1) j.1 (-1) A B +
        (oddC₂ j true false:ℤ)*q9 j.1 (j.1+1) 1 A B +
        (oddC₂ j true true:ℤ)*q9 j.1 (j.1+1) (-1) A B)) +
     (∑ j:Fin n,
       ((ep₂ j:ℤ)*q9 (j.1+1) (j.1+1) 1 A B +
        (em₂ j:ℤ)*q9 (j.1+1) (j.1+1) (-1) A B)):=by
   have h1:=vf n oddC₁ ep₁ em₁ (fun t=>q9 t.1 t.2.1 t.2.2 A B);have h2:=vf n oddC₂ ep₂ em₂ (fun t=>q9 t.1 t.2.1 t.2.2 A B);rw [<- h1,<-h2];exact hlog A B
 have hbLog_zero_of_ne_diff {a b A B:ℕ} {s:ℤ}
     (h:∀ k:ℕ,0< k->k*a=A->k*b≠B):q9 a b s A B=0:=by
   unfold q9
   by_cases hpos:0< a+b
   . simp only [hpos,Zh]
     split_ifs with hcond
     . exact absurd hcond.2.2 (h _ hcond.1 hcond.2.1)
     . rfl
   . simp [hpos]
 have hbLog_one (a b:ℕ) (hab:0< a+b) (s:ℤ) :
     q9 a b s a b=((a+b:ℕ):ℤ)*s:=by
   unfold q9;rw [if_pos hab];have hdiv:(a+b)/(a+b)=1:=Nat.div_self hab;simp [hdiv]
 have hbLog_two (a b:ℕ) (hab:0< a+b) (s:ℤ) :
     q9 a b s (2*a) (2*b)=-((a+b:ℕ):ℤ)*s^2:=by
   unfold q9;rw [if_pos hab]
   have hdiv:(2*a+2*b)/(a+b)=2:=by
     rw [<- Nat.mul_add,Nat.mul_div_cancel _ hab]
   simp [hdiv]
 have hodd0:∀ j0:Fin n,oddC₁ j0 false false=oddC₂ j0 false false /\
     oddC₁ j0 false true=oddC₂ j0 false true:=by
   intro j0
   have he1 (oc:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) :
       (∑ j:Fin n,
         ((oc j false false:ℤ)*q9 (j.1+1) j.1 1 (j0.1+1) j0.1 +
          (oc j false true:ℤ)*q9 (j.1+1) j.1 (-1) (j0.1+1) j0.1 +
          (oc j true false:ℤ)*q9 j.1 (j.1+1) 1 (j0.1+1) j0.1 +
          (oc j true true:ℤ)*q9 j.1 (j.1+1) (-1) (j0.1+1) j0.1)) +
       (∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (j0.1+1) j0.1 +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (j0.1+1) j0.1)) =
       ((2*j0.1+1:ℕ):ℤ)*((oc j0 false false:ℤ)-(oc j0 false true:ℤ)):=by
     have hev0:∀ j:Fin n,q9 (j.1+1) (j.1+1) 1 (j0.1+1) j0.1=0 /\
         q9 (j.1+1) (j.1+1) (-1) (j0.1+1) j0.1=0:=fun j =>
       ⟨hbLog_zero_of_ne_diff (fun k _ h1 h2=>by omega),
        hbLog_zero_of_ne_diff (fun k _ h1 h2=>by omega)⟩
     have hsum2:(∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (j0.1+1) j0.1 +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (j0.1+1) j0.1))=0:=by
       apply Finset.sum_eq_zero;intro j _;rw [(hev0 j).1,(hev0 j).2];ring
     rw [hsum2,add_zero,Finset.sum_eq_single j0]
     . have ht1:q9 j0.1 (j0.1+1) 1 (j0.1+1) j0.1=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at h2;omega
           omega)
       have ht2:q9 j0.1 (j0.1+1) (-1) (j0.1+1) j0.1=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at h2;omega
           omega)
       rw [ht1,ht2,hbLog_one (j0.1+1) j0.1 (by omega) 1,
           hbLog_one (j0.1+1) j0.1 (by omega) (-1)]
       have hlen:j0.1+1+j0.1=2*j0.1+1:=by omega
       rw [hlen];ring
     . intro j _ hjne
       have hvalne:j.1≠j0.1:=fun h=>hjne (Zx h)
       have h1:q9 (j.1+1) j.1 1 (j0.1+1) j0.1=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=1:=by omega
           subst this;simp at hb;exact hvalne hb)
       have h2:q9 (j.1+1) j.1 (-1) (j0.1+1) j0.1=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=1:=by omega
           subst this;simp at hb;exact hvalne hb)
       have h3:q9 j.1 (j.1+1) 1 (j0.1+1) j0.1=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at hb;omega
           omega)
       have h4:q9 j.1 (j.1+1) (-1) (j0.1+1) j0.1=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at hb;omega
           omega)
       rw [h1,h2,h3,h4];ring
     . intro h;exact absurd (Zu j0) h
   have he2 (oc:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) :
       (∑ j:Fin n,
         ((oc j false false:ℤ)*q9 (j.1+1) j.1 1 (2*(j0.1+1)) (2*j0.1) +
          (oc j false true:ℤ)*q9 (j.1+1) j.1 (-1) (2*(j0.1+1)) (2*j0.1) +
          (oc j true false:ℤ)*q9 j.1 (j.1+1) 1 (2*(j0.1+1)) (2*j0.1) +
          (oc j true true:ℤ)*q9 j.1 (j.1+1) (-1) (2*(j0.1+1)) (2*j0.1))) +
       (∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (2*(j0.1+1)) (2*j0.1) +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (2*(j0.1+1)) (2*j0.1))) =
       -((2*j0.1+1:ℕ):ℤ)*((oc j0 false false:ℤ)+(oc j0 false true:ℤ)):=by
     have hsum2:(∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (2*(j0.1+1)) (2*j0.1) +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (2*(j0.1+1)) (2*j0.1)))=0:=by
       apply Finset.sum_eq_zero;intro j _
       have h1:q9 (j.1+1) (j.1+1) 1 (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k _ ha hb=>by omega)
       have h2:q9 (j.1+1) (j.1+1) (-1) (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k _ ha hb=>by omega)
       rw [h1,h2];ring
     rw [hsum2,add_zero,Finset.sum_eq_single j0]
     . have ht1:q9 j0.1 (j0.1+1) 1 (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at h2;omega
           omega)
       have ht2:q9 j0.1 (j0.1+1) (-1) (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at h2;omega
           omega)
       rw [ht1,ht2,hbLog_two (j0.1+1) j0.1 (by omega) 1,
           hbLog_two (j0.1+1) j0.1 (by omega) (-1)]
       have hlen:j0.1+1+j0.1=2*j0.1+1:=by omega
       rw [hlen];ring
     . intro j _ hjne
       have hvalne:j.1≠j0.1:=fun h=>hjne (Zx h)
       have h1:q9 (j.1+1) j.1 1 (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=2:=by omega
           subst this;omega)
       have h2:q9 (j.1+1) j.1 (-1) (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=2:=by omega
           subst this;omega)
       have h3:q9 j.1 (j.1+1) 1 (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at hb;omega
           omega)
       have h4:q9 j.1 (j.1+1) (-1) (2*(j0.1+1)) (2*j0.1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at hb;omega
           omega)
       rw [h1,h2,h3,h4];ring
     . intro h;exact absurd (Zu j0) h
   have eq1:=hlog_eval (j0.1+1) j0.1;rw [he1 oddC₁ ep₁ em₁,he1 oddC₂ ep₂ em₂] at eq1;have eq2:=hlog_eval (2*(j0.1+1)) (2*j0.1);rw [he2 oddC₁ ep₁ em₁,he2 oddC₂ ep₂ em₂] at eq2
   have hpos:((2*j0.1+1:ℕ):ℤ)≠0:=by omega
   have hdiff:(oddC₁ j0 false false:ℤ)-(oddC₁ j0 false true:ℤ) =
       (oddC₂ j0 false false:ℤ)-(oddC₂ j0 false true:ℤ) :=
     mul_left_cancel₀ hpos eq1
   have hsum:(oddC₁ j0 false false:ℤ)+(oddC₁ j0 false true:ℤ) =
       (oddC₂ j0 false false:ℤ)+(oddC₂ j0 false true:ℤ):=by
     have:-((2*j0.1+1:ℕ):ℤ)≠0:=by omega
     exact mul_left_cancel₀ this eq2
   constructor <;> omega
 have hodd1:∀ j0:Fin n,oddC₁ j0 true false=oddC₂ j0 true false /\
     oddC₁ j0 true true=oddC₂ j0 true true:=by
   intro j0
   have he1 (oc:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) :
       (∑ j:Fin n,
         ((oc j false false:ℤ)*q9 (j.1+1) j.1 1 j0.1 (j0.1+1) +
          (oc j false true:ℤ)*q9 (j.1+1) j.1 (-1) j0.1 (j0.1+1) +
          (oc j true false:ℤ)*q9 j.1 (j.1+1) 1 j0.1 (j0.1+1) +
          (oc j true true:ℤ)*q9 j.1 (j.1+1) (-1) j0.1 (j0.1+1))) +
       (∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 j0.1 (j0.1+1) +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) j0.1 (j0.1+1))) =
       ((2*j0.1+1:ℕ):ℤ)*((oc j0 true false:ℤ)-(oc j0 true true:ℤ)):=by
     have hsum2:(∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 j0.1 (j0.1+1) +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) j0.1 (j0.1+1)))=0:=by
       apply Finset.sum_eq_zero;intro j _
       have h1:q9 (j.1+1) (j.1+1) 1 j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k _ ha hb=>by omega)
       have h2:q9 (j.1+1) (j.1+1) (-1) j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k _ ha hb=>by omega)
       rw [h1,h2];ring
     rw [hsum2,add_zero,Finset.sum_eq_single j0]
     . have ht1:q9 (j0.1+1) j0.1 1 j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at h1;omega
           omega)
       have ht2:q9 (j0.1+1) j0.1 (-1) j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at h1;omega
           omega)
       rw [ht1,ht2,hbLog_one j0.1 (j0.1+1) (by omega) 1,
           hbLog_one j0.1 (j0.1+1) (by omega) (-1)]
       have hlen:j0.1+(j0.1+1)=2*j0.1+1:=by omega
       rw [hlen];ring
     . intro j _ hjne
       have hvalne:j.1≠j0.1:=fun h=>hjne (Zx h)
       have h1:q9 (j.1+1) j.1 1 j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at ha;omega
           omega)
       have h2:q9 (j.1+1) j.1 (-1) j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=j0.1:=by rw [Nat.mul_add,mul_one] at ha;omega
           omega)
       have h3:q9 j.1 (j.1+1) 1 j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=1:=by omega
           subst this;simp at ha;exact hvalne ha)
       have h4:q9 j.1 (j.1+1) (-1) j0.1 (j0.1+1)=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=1:=by omega
           subst this;simp at ha;exact hvalne ha)
       rw [h1,h2,h3,h4];ring
     . intro h;exact absurd (Zu j0) h
   have he2 (oc:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) :
       (∑ j:Fin n,
         ((oc j false false:ℤ)*q9 (j.1+1) j.1 1 (2*j0.1) (2*(j0.1+1)) +
          (oc j false true:ℤ)*q9 (j.1+1) j.1 (-1) (2*j0.1) (2*(j0.1+1)) +
          (oc j true false:ℤ)*q9 j.1 (j.1+1) 1 (2*j0.1) (2*(j0.1+1)) +
          (oc j true true:ℤ)*q9 j.1 (j.1+1) (-1) (2*j0.1) (2*(j0.1+1)))) +
       (∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (2*j0.1) (2*(j0.1+1)) +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (2*j0.1) (2*(j0.1+1)))) =
       -((2*j0.1+1:ℕ):ℤ)*((oc j0 true false:ℤ)+(oc j0 true true:ℤ)):=by
     have hsum2:(∑ j:Fin n,
         ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (2*j0.1) (2*(j0.1+1)) +
          (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (2*j0.1) (2*(j0.1+1))))=0:=by
       apply Finset.sum_eq_zero;intro j _
       have h1:q9 (j.1+1) (j.1+1) 1 (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k _ ha hb=>by omega)
       have h2:q9 (j.1+1) (j.1+1) (-1) (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k _ ha hb=>by omega)
       rw [h1,h2];ring
     rw [hsum2,add_zero,Finset.sum_eq_single j0]
     . have ht1:q9 (j0.1+1) j0.1 1 (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at h1;omega
           omega)
       have ht2:q9 (j0.1+1) j0.1 (-1) (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k hk h1 h2=>by
           have:k*j0.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at h1;omega
           omega)
       rw [ht1,ht2,hbLog_two j0.1 (j0.1+1) (by omega) 1,
           hbLog_two j0.1 (j0.1+1) (by omega) (-1)]
       have hlen:j0.1+(j0.1+1)=2*j0.1+1:=by omega
       rw [hlen];ring
     . intro j _ hjne
       have hvalne:j.1≠j0.1:=fun h=>hjne (Zx h)
       have h1:q9 (j.1+1) j.1 1 (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at ha;omega
           omega)
       have h2:q9 (j.1+1) j.1 (-1) (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have:k*j.1+k=2*j0.1:=by rw [Nat.mul_add,mul_one] at ha;omega
           omega)
       have h3:q9 j.1 (j.1+1) 1 (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=2:=by omega
           subst this;omega)
       have h4:q9 j.1 (j.1+1) (-1) (2*j0.1) (2*(j0.1+1))=0 :=
         hbLog_zero_of_ne_diff (fun k hk ha hb=>by
           have hsub:k*(j.1+1)-k*j.1=k:=by rw [Nat.mul_add,mul_one];omega
           have:k=2:=by omega
           subst this;omega)
       rw [h1,h2,h3,h4];ring
     . intro h;exact absurd (Zu j0) h
   have eq1:=hlog_eval j0.1 (j0.1+1);rw [he1 oddC₁ ep₁ em₁,he1 oddC₂ ep₂ em₂] at eq1;have eq2:=hlog_eval (2*j0.1) (2*(j0.1+1));rw [he2 oddC₁ ep₁ em₁,he2 oddC₂ ep₂ em₂] at eq2
   have hpos:((2*j0.1+1:ℕ):ℤ)≠0:=by omega
   have hdiff:(oddC₁ j0 true false:ℤ)-(oddC₁ j0 true true:ℤ) =
       (oddC₂ j0 true false:ℤ)-(oddC₂ j0 true true:ℤ) :=
     mul_left_cancel₀ hpos eq1
   have hsum:(oddC₁ j0 true false:ℤ)+(oddC₁ j0 true true:ℤ) =
       (oddC₂ j0 true false:ℤ)+(oddC₂ j0 true true:ℤ):=by
     have:-((2*j0.1+1:ℕ):ℤ)≠0:=by omega
     exact mul_left_cancel₀ this eq2
   constructor <;> omega
 have hodd_eq:oddC₁=oddC₂:=by
   funext j c sig
   cases c <;> cases sig
   . exact (hodd0 j).1
   . exact (hodd0 j).2
   . exact (hodd1 j).1
   . exact (hodd1 j).2
 have heven_eq:∀ k (hk:k< n),ep₁ ⟨k,hk⟩=ep₂ ⟨k,hk⟩/\em₁ ⟨k,hk⟩=em₂ ⟨k,hk⟩:=by
   intro k
   induction k using Nat.strong_induction_on with
   | ind k ih =>
     intro hk
     set j0:Fin n:=⟨k,hk⟩
     have hev_eval:=hlog_eval (k+1) (k+1)
     have hodd_zero (oc:Fin n->Bool->Bool->ℕ) :
         (∑ j:Fin n,
           ((oc j false false:ℤ)*q9 (j.1+1) j.1 1 (k+1) (k+1) +
            (oc j false true:ℤ)*q9 (j.1+1) j.1 (-1) (k+1) (k+1) +
            (oc j true false:ℤ)*q9 j.1 (j.1+1) 1 (k+1) (k+1) +
            (oc j true true:ℤ)*q9 j.1 (j.1+1) (-1) (k+1) (k+1)))=0:=by
       apply Finset.sum_eq_zero;intro j _
       have h1:q9 (j.1+1) j.1 1 (k+1) (k+1)=0 :=
         hbLog_zero_of_ne_diff (fun m hm ha hb=>by rw [Nat.mul_add,mul_one] at ha;omega)
       have h2:q9 (j.1+1) j.1 (-1) (k+1) (k+1)=0 :=
         hbLog_zero_of_ne_diff (fun m hm ha hb=>by rw [Nat.mul_add,mul_one] at ha;omega)
       have h3:q9 j.1 (j.1+1) 1 (k+1) (k+1)=0 :=
         hbLog_zero_of_ne_diff (fun m hm ha hb=>by rw [Nat.mul_add,mul_one] at hb;omega)
       have h4:q9 j.1 (j.1+1) (-1) (k+1) (k+1)=0 :=
         hbLog_zero_of_ne_diff (fun m hm ha hb=>by rw [Nat.mul_add,mul_one] at hb;omega)
       rw [h1,h2,h3,h4];ring
     rw [hodd_zero oddC₁,hodd_zero oddC₂,zero_add,zero_add] at hev_eval
     have hsplit_sum (ep em:Fin n->ℕ) :
         (∑ j:Fin n,
           ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (k+1) (k+1) +
            (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (k+1) (k+1))) =
         ((ep j0:ℤ)*q9 (k+1) (k+1) 1 (k+1) (k+1) +
          (em j0:ℤ)*q9 (k+1) (k+1) (-1) (k+1) (k+1)) +
         ∑ j ∈ Finset.univ.erase j0,
           ((ep j:ℤ)*q9 (j.1+1) (j.1+1) 1 (k+1) (k+1) +
            (em j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (k+1) (k+1)):=by
       rw [<- Finset.add_sum_erase _ _ (Zu j0)]
     rw [hsplit_sum ep₁ em₁,hsplit_sum ep₂ em₂] at hev_eval
     have hrest :
         (∑ j ∈ Finset.univ.erase j0,
           ((ep₁ j:ℤ)*q9 (j.1+1) (j.1+1) 1 (k+1) (k+1) +
            (em₁ j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (k+1) (k+1))) =
         (∑ j ∈ Finset.univ.erase j0,
           ((ep₂ j:ℤ)*q9 (j.1+1) (j.1+1) 1 (k+1) (k+1) +
            (em₂ j:ℤ)*q9 (j.1+1) (j.1+1) (-1) (k+1) (k+1))):=by
       apply Zc rfl;intro j hj;rw [Finset.mem_erase] at hj
       by_cases hlt:j.1< k
       . have hij:=ih j.1 hlt j.isLt;have hjeq:(⟨j.1,j.isLt⟩:Fin n)=j:=Zx rfl;rw [hjeq] at hij;rw [hij.1,hij.2]
       . have hgt:k< j.1:=by
           have:j.1≠k:=fun h=>hj.1 (Zx h)
           omega
         have h1:q9 (j.1+1) (j.1+1) 1 (k+1) (k+1)=0 :=
           hbLog_zero_of_ne_diff (fun m hm ha _=>by
             have:j.1+1<=m*(j.1+1):=Nat.le_mul_of_pos_left _ hm
             omega)
         have h2:q9 (j.1+1) (j.1+1) (-1) (k+1) (k+1)=0 :=
           hbLog_zero_of_ne_diff (fun m hm ha _=>by
             have:j.1+1<=m*(j.1+1):=Nat.le_mul_of_pos_left _ hm
             omega)
         rw [h1,h2];ring
     rw [hrest] at hev_eval
     have hterm :
         (ep₁ j0:ℤ)*q9 (k+1) (k+1) 1 (k+1) (k+1) +
         (em₁ j0:ℤ)*q9 (k+1) (k+1) (-1) (k+1) (k+1) =
         (ep₂ j0:ℤ)*q9 (k+1) (k+1) 1 (k+1) (k+1) +
         (em₂ j0:ℤ)*q9 (k+1) (k+1) (-1) (k+1) (k+1):=by
       linarith
     rw [hbLog_one (k+1) (k+1) (by omega) 1,hbLog_one (k+1) (k+1) (by omega) (-1)] at hterm
     have hpos:((k+1+(k+1):ℕ):ℤ)≠0:=by omega
     have hdiff:(ep₁ j0:ℤ)-(em₁ j0:ℤ)=(ep₂ j0:ℤ)-(em₂ j0:ℤ):=by
       apply mul_left_cancel₀ hpos;linarith
     rcases hred₁ j0 with h1 | h1 <;> rcases hred₂ j0 with h2 | h2 <;> constructor <;> omega
 refine ⟨hodd_eq,?_,?_⟩
 . funext j;exact (heven_eq j.1 j.isLt).1
 . funext j;exact (heven_eq j.1 j.isLt).2
def v2:ℕ->ℕ
 | 0=>0
 | m+1=>if (m+1)%2=0 then 1+v2 ((m+1)/2) else 0
termination_by m=>m
lemma cj {m:ℕ} (h:m %2=1):v2 m=0:=by
 cases m with
 | zero=>omega
 | succ m=>unfold v2;simp [show (m+1)%2≠0 by omega]
lemma c3 {m:ℕ} (hm:0< m):v2 (2*m)=1+v2 m:=by
 cases m with
 | zero=>omega
 | succ m =>
  have heq:2*(m+1)=(2*m+1)+1:=by omega
  rw [heq]
  conv_lhs=>unfold v2
  simp [show (2*m+1+1)%2=0 by omega,show (2*m+1+1)/2=m+1 by omega]
lemma vb (m:ℕ):2*v2 m<=m:=by
 induction m using Nat.strong_induction_on with
 | ind m ih =>
  cases m with
  | zero=>simp [v2]
  | succ m =>
   unfold v2
   by_cases h:(m+1)%2=0
   . simp only [h,Zh]
     have hlt:(m+1)/2< m+1:=by omega
     have:=ih ((m+1)/2) hlt;omega
   . simp [h]
def we (n:ℕ) (m:Fin n) (st:(Fin n->ℕ) × (Fin n->ℕ) × ℕ) :
  (Fin n->ℕ) × (Fin n->ℕ) × ℕ :=
 let ep:=st.1
 let em:=st.2.1
 let fus:=st.2.2
 let pr:=min (ep m) (em m)
 let ep':Fin n->ℕ:=fun j=>if j=m then ep j-pr else ep j
 let em':Fin n->ℕ:=fun j =>
  if j=m then em j-pr
  else if j.1+1=2*(m.1+1) then em j+pr
  else em j
 (ep',em',fus+pr)
def z0 (n:ℕ) (ep em:Fin n->ℕ):(Fin n->ℕ) × (Fin n->ℕ) × ℕ :=
 (List.finRange n).foldl (fun st m=>we n m st) (ep,em,0)
lemma j6 {α:Type*} (l:List α) (g:α->List j5) :
  w9 (l.flatMap g)=w9 (l.map fun x=>w9 (g x)):=by
 induction l with
 | nil=>rfl
 | cons x xs ih=>rw [List.flatMap_cons,xm,List.map_cons,wd,ih]
lemma jt (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (m:Fin n)
   (ep em:Fin n->ℕ) (fus:ℕ)
   (hlen:∑ j:Fin n,2*(j.1+1)*(ep j+em j)<=2*n) :
   let st':=we n m (ep,em,fus)
   wy n oddC st'.1 st'.2.1=wy n oddC ep em /\
   (∀ j:Fin n,j.1< m.1->st'.1 j=ep j/\st'.2.1 j=em j) /\
   (st'.1 m=0\/st'.2.1 m=0) /\
   (∑ j:Fin n,2*(j.1+1)*(st'.1 j+st'.2.1 j)) =
     (∑ j:Fin n,2*(j.1+1)*(ep j+em j)) /\
   (∑ j:Fin n,st'.2.1 j)%2=(∑ j:Fin n,em j)%2 /\
   (∑ j:Fin n,(st'.1 j+st'.2.1 j))+st'.2.2=(∑ j:Fin n,(ep j+em j))+fus /\
   (∑ j:Fin n,st'.2.1 j*v2 (j.1+1)) =
     (∑ j:Fin n,em j*v2 (j.1+1))+min (ep m) (em m):=by
 set pr:=min (ep m) (em m)
 dsimp only [we]
 by_cases hpr:pr=0
 . simp only [show min (ep m) (em m)=0 from hpr,Nat.sub_zero,Zq,ite_self,
     true_and,and_true]
   have:min (ep m) (em m)=0:=hpr
   refine ⟨fun _ _=>trivial,by omega⟩
 . have hpr_pos:0< pr:=by omega
   have h2m_le:2*(m.1+1)<=n:=by
     have hterm:2*(m.1+1)*(ep m+em m) <=
        ∑ j:Fin n,2*(j.1+1)*(ep j+em j) :=
       Finset.single_le_sum (f:=fun j:Fin n=>2*(j.1+1)*(ep j+em j))
        (fun j _=>Nat.zero_le _) (Zu m)
     have hge2:2<=ep m+em m:=by omega
     have:2*(m.1+1)*2<=2*(m.1+1)*(ep m+em m) :=
       Nat.mul_le_mul_left _ hge2
     omega
   let m2:Fin n:=⟨2*(m.1+1)-1,by omega⟩
   have hm2_val:m2.1+1=2*(m.1+1):=by dsimp [m2];omega
   have hm2_ne:m2≠m:=by
     intro h;have:=congrArg Fin.val h;dsimp [m2] at this;omega
   have hm2_iff:∀ j:Fin n,(j.1+1=2*(m.1+1)) ↔ j=m2:=by
     intro j;constructor
     . intro h;apply Zx;dsimp [m2];omega
     . intro h;rw [h];exact hm2_val
   set ep':Fin n->ℕ:=fun j=>if j=m then ep j-pr else ep j
   set em':Fin n->ℕ:=fun j =>
     if j=m then em j-pr
     else if j.1+1=2*(m.1+1) then em j+pr else em j
   have hep'_m:ep' m=ep m-pr:=by simp [ep']
   have hem'_m:em' m=em m-pr:=by simp [em']
   have hep'_m2:ep' m2=ep m2:=by simp [ep',hm2_ne]
   have hem'_m2:em' m2=em m2+pr:=by simp [em',hm2_ne,hm2_val]
   have hother:∀ j:Fin n,j≠m->j≠m2->ep' j=ep j/\em' j=em j:=by
     intro j h1 h2
     have h3:j.1+1≠2*(m.1+1):=fun hc=>h2 ((hm2_iff j).mp hc)
     simp [ep',em',h1,h3]
   have hsum_split (F:Fin n->ℕ) :
       (∑ j:Fin n,F j)=F m+F m2+∑ j ∈ (Finset.univ.erase m).erase m2,F j:=by
     rw [<- Finset.add_sum_erase _ _ (Zu m)];have hm2_mem:m2 ∈ Finset.univ.erase m:=Finset.mem_erase.mpr ⟨hm2_ne,Zu m2⟩;rw [<- Finset.add_sum_erase _ _ hm2_mem,add_assoc]
   have hpr_le1:pr<=ep m:=Nat.min_le_left _ _;have hpr_le2:pr<=em m:=Nat.min_le_right _ _
   refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
   . unfold wy xd;rw [Za,xm,Za,xm];congr 1;rw [List.map_flatMap,j6,List.map_flatMap,j6]
     let g (a b:Fin n->ℕ) (j:Fin n):j5 :=
       qt (wp (zi (j.1+1) (j.1+1) 1) (a j))
           (wp (zi (j.1+1) (j.1+1) (-1)) (b j))
     have hrewrite (a b:Fin n->ℕ) :
        w9 ((List.finRange n).map fun j =>
          w9 ((List.replicate (a j) (j.1+1,j.1+1,(1:ℤ)) ++
                 List.replicate (b j) (j.1+1,j.1+1,(-1:ℤ))).map
             fun t=>zi t.1 t.2.1 t.2.2)) =
        w9 ((List.finRange n).map (g a b)):=by
       congr 1;apply List.map_congr_left;intro j _
       rw [Za,xm,Zy,Zy,
        ve,ve]
     rw [hrewrite ep' em',hrewrite ep em]
     have hperm2:(List.finRange n).Perm
        (m :: m2 :: (List.finRange n).filter (fun j=>decide (j≠m/\j≠m2))):=by
       have hnod1:=List.nodup_finRange n
       have hnod2:(m :: m2 :: (List.finRange n).filter (fun j=>decide (j≠m/\j≠m2))).Nodup:=by
        rw [List.nodup_cons,List.nodup_cons]
        refine ⟨by simp [hm2_ne.symm],by simp,hnod1.filter _⟩
       exact (List.perm_ext_iff_of_nodup hnod1 hnod2).mpr fun j=>by
        simp only [List.mem_finRange,true_iff,List.mem_cons,List.mem_filter,true_and,
          decide_eq_true_eq]
        by_cases h1:j=m
        . left;exact h1
        . by_cases h2:j=m2
          . right;left;exact h2
          . right;right;exact ⟨h1,h2⟩
     rw [yt (hperm2.map (g ep' em')),yt (hperm2.map (g ep em))];simp only [List.map_cons,wd,<-zh];congr 1
     . dsimp only [g];rw [hep'_m,hem'_m,hep'_m2,hem'_m2,hm2_val]
       have hpow_pair:∀ k,
          qt (wp (zi (m.1+1) (m.1+1) 1) k)
              (wp (zi (m.1+1) (m.1+1) (-1)) k) =
          wp (zi (2*(m.1+1)) (2*(m.1+1)) (-1)) k:=by
        intro k
        induction k with
        | zero=>simp [wp,jq]
        | succ k ih =>
          simp only [wp]
          calc qt (qt (zi (m.1+1) (m.1+1) 1) (wp (zi (m.1+1) (m.1+1) 1) k))
                   (qt (zi (m.1+1) (m.1+1) (-1)) (wp (zi (m.1+1) (m.1+1) (-1)) k))
             = qt (qt (zi (m.1+1) (m.1+1) 1) (zi (m.1+1) (m.1+1) (-1)))
                  (qt (wp (zi (m.1+1) (m.1+1) 1) k) (wp (zi (m.1+1) (m.1+1) (-1)) k)):=by
                simp only [zh];congr 1;rw [<- zh,wq (wp _ k) (zi _ _ (-1)),zh]
          _=qt (zi (2*(m.1+1)) (2*(m.1+1)) (-1))
                  (wp (zi (2*(m.1+1)) (2*(m.1+1)) (-1)) k):=by
                rw [pk (m.1+1) (by omega),ih]
       have he1:ep m=(ep m-pr)+pr:=by omega
       have he2:em m=(em m-pr)+pr:=by omega
       conv_rhs=>rw [he1,he2]
       rw [kb,kb,kb];rw [<- hpow_pair pr];set A1:=wp (zi (m.1+1) (m.1+1) 1) (ep m-pr);set A2:=wp (zi (m.1+1) (m.1+1) 1) pr;set B1:=wp (zi (m.1+1) (m.1+1) (-1)) (em m-pr);set B2:=wp (zi (m.1+1) (m.1+1) (-1)) pr;set C1:=wp (zi (2*(m.1+1)) (2*(m.1+1)) 1) (ep m2);set C2:=wp (zi (2*(m.1+1)) (2*(m.1+1)) (-1)) (em m2)
       calc qt (qt A1 B1) (qt C1 (qt C2 (qt A2 B2)))
        = qt (qt A1 B1) (qt (qt A2 B2) (qt C1 C2)):=by
             congr 1;rw [wq C2 (qt A2 B2),<-zh,wq C1 (qt A2 B2),zh]
       _=qt (qt (qt A1 B1) (qt A2 B2)) (qt C1 C2):=by rw [<- zh]
       _=qt (qt (qt A1 A2) (qt B1 B2)) (qt C1 C2):=by
             congr 1;simp only [zh];congr 1;rw [<- zh B1 A2 B2,wq B1 A2,zh]
     . congr 1;apply List.map_congr_left;intro j hj;simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] at hj;dsimp only [g];rw [(hother j hj.1 hj.2).1,(hother j hj.1 hj.2).2]
   . intro j hj
     have hne1:j≠m:=fun h=>by rw [h] at hj;omega
     have hne2:j≠m2:=fun h=>by rw [h] at hj;dsimp [m2] at hj;omega
     exact hother j hne1 hne2
   . change ep' m=0\/em' m=0;rw [hep'_m,hem'_m];omega
   . rw [hsum_split (fun j=>2*(j.1+1)*(ep' j+em' j)),
        hsum_split (fun j=>2*(j.1+1)*(ep j+em j))]
     have hrest:∑ j ∈ (Finset.univ.erase m).erase m2,2*(j.1+1)*(ep' j+em' j) =
        ∑ j ∈ (Finset.univ.erase m).erase m2,2*(j.1+1)*(ep j+em j):=by
       apply Zc rfl;intro j hj;simp only [Finset.mem_erase] at hj;rw [(hother j hj.2.1 hj.1).1,(hother j hj.2.1 hj.1).2]
     rw [hrest,hep'_m,hem'_m,hep'_m2,hem'_m2,hm2_val]
     have hmain:2*(m.1+1)*(ep m-pr+(em m-pr)) +
        2*(2*(m.1+1))*(ep m2+(em m2+pr)) =
        2*(m.1+1)*(ep m+em m)+2*(2*(m.1+1))*(ep m2+em m2):=by
       zify [hpr_le1,hpr_le2];ring
     omega
   . rw [hsum_split em',hsum_split em]
     have hrest:∑ j ∈ (Finset.univ.erase m).erase m2,em' j =
        ∑ j ∈ (Finset.univ.erase m).erase m2,em j:=by
       apply Zc rfl;intro j hj;simp only [Finset.mem_erase] at hj;exact (hother j hj.2.1 hj.1).2
     rw [hrest,hem'_m,hem'_m2]
     have:em m-pr+(em m2+pr)=em m+em m2:=by omega
     rw [this]
   . rw [hsum_split (fun j=>ep' j+em' j),hsum_split (fun j=>ep j+em j)]
     have hrest:∑ j ∈ (Finset.univ.erase m).erase m2,(ep' j+em' j) =
        ∑ j ∈ (Finset.univ.erase m).erase m2,(ep j+em j):=by
       apply Zc rfl;intro j hj;simp only [Finset.mem_erase] at hj;rw [(hother j hj.2.1 hj.1).1,(hother j hj.2.1 hj.1).2]
     rw [hrest,hep'_m,hem'_m,hep'_m2,hem'_m2];omega
   . rw [hsum_split (fun j=>em' j*v2 (j.1+1)),
        hsum_split (fun j=>em j*v2 (j.1+1))]
     have hrest:∑ j ∈ (Finset.univ.erase m).erase m2,em' j*v2 (j.1+1) =
        ∑ j ∈ (Finset.univ.erase m).erase m2,em j*v2 (j.1+1):=by
       apply Zc rfl;intro j hj;simp only [Finset.mem_erase] at hj;rw [(hother j hj.2.1 hj.1).2]
     rw [hrest,hem'_m,hem'_m2,hm2_val,c3 (by omega:0< m.1+1)]
     have hmain:(em m-pr)*v2 (m.1+1)+(em m2+pr)*(1+v2 (m.1+1)) =
        em m*v2 (m.1+1)+em m2*(1+v2 (m.1+1))+pr:=by
       zify [hpr_le2];ring
     omega
lemma y2 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ)
  (hlen:∑ j:Fin n,2*(j.1+1)*(ep j+em j)<=2*n) :
  let res:=z0 n ep em
  wy n oddC res.1 res.2.1=wy n oddC ep em /\
  (∀ j:Fin n,res.1 j=0\/res.2.1 j=0) /\
  (∑ j:Fin n,2*(j.1+1)*(res.1 j+res.2.1 j)) =
   (∑ j:Fin n,2*(j.1+1)*(ep j+em j)) /\
  (∑ j:Fin n,res.2.1 j)%2=(∑ j:Fin n,em j)%2 /\
  (∑ j:Fin n,(res.1 j+res.2.1 j))+res.2.2=∑ j:Fin n,(ep j+em j) /\
  (∑ j:Fin n,res.2.1 j*v2 (j.1+1)) =
   (∑ j:Fin n,em j*v2 (j.1+1))+res.2.2 /\
  ∑ j:Fin n,res.2.1 j*v2 (j.1+1)<=n:=by
 have hinv:∀ k ≤ n,
   let st:=((List.finRange n).take k).foldl (fun st m=>we n m st) (ep,em,0)
   wy n oddC st.1 st.2.1=wy n oddC ep em /\
   (∀ j:Fin n,j.1< k->st.1 j=0\/st.2.1 j=0) /\
   (∑ j:Fin n,2*(j.1+1)*(st.1 j+st.2.1 j)) =
     (∑ j:Fin n,2*(j.1+1)*(ep j+em j)) /\
   (∑ j:Fin n,st.2.1 j)%2=(∑ j:Fin n,em j)%2 /\
   (∑ j:Fin n,(st.1 j+st.2.1 j))+st.2.2=∑ j:Fin n,(ep j+em j) /\
   (∑ j:Fin n,st.2.1 j*v2 (j.1+1)) =
     (∑ j:Fin n,em j*v2 (j.1+1))+st.2.2:=by
  intro k hk
  induction k with
  | zero =>
   simp
  | succ k ihk =>
   have htake:(List.finRange n).take (k+1) =
        (List.finRange n).take k++[⟨k,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi];set st:=((List.finRange n).take k).foldl (fun st m=>we n m st) (ep,em,0)
   rcases ihk (by omega) with ⟨hbiv,hdisj,hlen',hpar,hcnt,hphi⟩
   have hlen_st:∑ j:Fin n,2*(j.1+1)*(st.1 j+st.2.1 j)<=2*n:=by
     change ∑ j:Fin n,2*(j.1+1)*(st.1 j+st.2.1 j)=_ at hlen'
     omega
   have hstep:=jt n oddC ⟨k,by omega⟩ st.1 st.2.1 st.2.2 hlen_st
   rcases hstep with ⟨sbiv,sprev,scur,slen,spar,scnt,sphi⟩
   refine ⟨sbiv.trans hbiv,?_,slen.trans hlen',spar.trans hpar,scnt.trans hcnt,?_⟩
   . intro j hj
     by_cases hlt:j.1< k
     . rcases sprev j (show j.1< (⟨k,by omega⟩:Fin n).1 from hlt) with ⟨h1,h2⟩
       rw [h1,h2];exact hdisj j hlt
     . have heq:j=⟨k,by omega⟩:=Zx (by dsimp;omega)
       rw [heq];exact scur
   . change (∑ j:Fin n,(we n ⟨k,by omega⟩ st).2.1 j*v2 (j.1+1)) =
         (∑ j:Fin n,em j*v2 (j.1+1))+(st.2.2+min (st.1 ⟨k,by omega⟩) (st.2.1 ⟨k,by omega⟩))
     rw [sphi,hphi];omega
 have hfull:=hinv n le_rfl;rw [Zk (by simp)] at hfull
 rcases hfull with ⟨hbiv,hdisj,hlen',hpar,hcnt,hphi⟩
 refine ⟨hbiv,fun j=>hdisj j j.isLt,hlen',hpar,hcnt,hphi,?_⟩
 have hbound:2*∑ j:Fin n,(z0 n ep em).2.1 j*v2 (j.1+1) <=
   ∑ j:Fin n,2*(j.1+1)*((z0 n ep em).1 j+(z0 n ep em).2.1 j):=by
  rw [Finset.mul_sum];apply Finset.sum_le_sum;intro j _;have hv:=vb (j.1+1)
  calc 2*((z0 n ep em).2.1 j*v2 (j.1+1))
   = (z0 n ep em).2.1 j*(2*v2 (j.1+1)):=by ring
  _<=(z0 n ep em).2.1 j*(j.1+1):=Nat.mul_le_mul_left _ hv
  _<=2*(j.1+1)*((z0 n ep em).1 j+(z0 n ep em).2.1 j):=by nlinarith
 change (∑ j:Fin n,2*(j.1+1)*((z0 n ep em).1 j+(z0 n ep em).2.1 j))=_ at hlen';omega
def y9 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (i:Fin (2*n)) (L:ℕ):Bool :=
 decide (1<=L/\L<=2*n)&&(p i).isSome&&(p (q8 n hn i L)).isSome &&
  (List.range (L-1)).all (fun r=>!(p (q8 n hn i (r+1))).isSome)
def z2 (n:ℕ) (p:Fin (2*n)->Option Bool):ℕ :=
 (Finset.univ.filter (fun k:Fin (2*n)=>(p k).isSome)).card
def zv (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (i:Fin (2*n)) (L:ℕ):Bool :=
 decide (p i≠p (q8 n hn i L))
def z3 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (j:Fin n) (c sig:Bool):ℕ :=
 (Finset.univ.filter (fun i:Fin (2*n) =>
  y9 n hn p i (2*j.1+1)=true /\
  decide (i.1 %2=1)=c /\
  zv n hn p i (2*j.1+1)=sig)).card
def qo (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (j:Fin n):ℕ :=
 (Finset.univ.filter (fun i:Fin (2*n) =>
  y9 n hn p i (2*(j.1+1))=true /\
  zv n hn p i (2*(j.1+1))=false)).card
def qd (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (j:Fin n):ℕ :=
 (Finset.univ.filter (fun i:Fin (2*n) =>
  y9 n hn p i (2*(j.1+1))=true /\
  zv n hn p i (2*(j.1+1))=true)).card
lemma y3 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
   (i:Fin (2*n)) (L:ℕ) :
   y9 n hn p i L=true ↔
   1<=L/\L<=2*n/\(p i).isSome=true/\(p (q8 n hn i L)).isSome=true /\
   ∀ r,1<=r->r< L->p (q8 n hn i r)=none:=by
 unfold y9
 simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
   Bool.not_eq_true',Option.isSome_eq_false_iff,Option.isNone_iff_eq_none]
 constructor
 . rintro ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩
   refine ⟨h1,h2,h3,h4,fun r hr1 hr2=>?_⟩
   have:=h5 (r-1) (by omega);rwa [show r-1+1=r by omega] at this
 . rintro ⟨h1,h2,h3,h4,h5⟩;exact ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,fun r hr=>h5 (r+1) (by omega) (by omega)⟩
lemma bb (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
   (i:Fin (2*n)) {L₁ L₂:ℕ}
   (h₁:y9 n hn p i L₁=true) (h₂:y9 n hn p i L₂=true):L₁=L₂:=by
 rw [y3] at h₁ h₂
 by_contra hne
 rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
 . have hnone:=h₂.2.2.2.2 L₁ h₁.1 hlt;rw [hnone] at h₁;simp at h₁
 . have hnone:=h₁.2.2.2.2 L₂ h₂.1 hgt;rw [hnone] at h₂;simp at h₂
def xv (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
  (start:Fin (2*n)):ℕ->ℕ->ℕ
 | _,0=>0
 | cur,fuel+1 =>
  if (p (q8 n hn start cur)).isSome then cur
  else xv n hn p start (cur+1) fuel
lemma pc (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
  (start:Fin (2*n)) (cur fuel:ℕ)
  (hex:∃ r,cur<=r/\r< cur+fuel/\(p (q8 n hn start r)).isSome=true) :
  let L:=xv n hn p start cur fuel
  cur<=L/\L< cur+fuel/\(p (q8 n hn start L)).isSome=true /\
  ∀ r,cur<=r->r< L->p (q8 n hn start r)=none:=by
 induction fuel generalizing cur with
 | zero =>
  rcases hex with ⟨r,h1,h2,_⟩;omega
 | succ fuel ih =>
  dsimp only [xv]
  split_ifs with hcur
  . exact ⟨le_rfl,by omega,hcur,fun r h1 h2=>by omega⟩
  . have hex':∃ r,cur+1<=r/\r< cur+1+fuel/\(p (q8 n hn start r)).isSome=true:=by
      rcases hex with ⟨r,h1,h2,h3⟩
      by_cases heq:r=cur
      . subst heq;exact absurd h3 hcur
      . exact ⟨r,by omega,by omega,h3⟩
    rcases ih (cur+1) hex' with ⟨h1,h2,h3,h4⟩
    refine ⟨by omega,by omega,h3,fun r hr1 hr2=>?_⟩
    by_cases heq:r=cur
    . subst heq
      cases hp:p (q8 n hn start r)
      . rfl
      . rw [hp] at hcur;simp at hcur
    . exact h4 r (by omega) hr2
def yu (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
  (start:Fin (2*n)) (rem:ℕ):List (Fin (2*n) × ℕ) :=
 if h0:rem=0 then []
 else
  let L:=xv n hn p start 1 rem
  if hL:1<=L/\L<=rem then
   (start,L) :: yu n hn p (q8 n hn start L) (rem-L)
  else []
termination_by rem
def zr (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (a:Fin (2*n) × ℕ) :
  ℕ × ℕ × ℤ :=
 let ab:=wl (decide (a.1.1 %2=1)) a.2
 (ab.1,ab.2,if zv n hn p a.1 a.2 then -1 else 1)
lemma pl (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) :
  ∀ (rem:ℕ) (start:Fin (2*n)) (bStart bEnd:Bool),
   1<=rem->rem<=2*n ->
   p start=some bStart->p (q8 n hn start rem)=some bEnd ->
   let ws:=yu n hn p start rem
   (ws.map Prod.snd).sum=rem /\
   ws.length<=rem /\
   y6 n hn p start rem bStart bEnd =
     wr ((2:ℤ)^(rem-ws.length))
       (w9 (ws.map fun a=>let t:=zr n hn p a;zi t.1 t.2.1 t.2.2)) /\
   (∀ a ∈ ws,y9 n hn p a.1 a.2=true) /\
   (ws.map Prod.fst).Nodup /\
   (∀ i:Fin (2*n),i ∈ ws.map Prod.fst ↔
     ∃ r:ℕ,r< rem/\q8 n hn start r=i/\(p i).isSome=true) /\
   ((ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=0)):ℤ) -
    (ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=1)):ℤ) =
    (if (q8 n hn start rem).1 %2=1 then 1 else 0) -
    (if start.1 %2=1 then 1 else 0)) /\
   ((ws.countP (fun a=>zv n hn p a.1 a.2)%2=1) ↔ bStart≠bEnd):=by
 intro rem
 induction rem using Nat.strong_induction_on with
 | ind rem ih =>
  intro start bStart bEnd hrem1 hrem2 hps hpe
  have hex:∃ r,1<=r/\r< 1+rem/\(p (q8 n hn start r)).isSome=true :=
   ⟨rem,hrem1,by omega,by rw [hpe];rfl⟩
  rcases pc n hn p start 1 rem hex with ⟨hL1,hL2,hLpin,hLunp⟩
  set L:=xv n hn p start 1 rem
  have hLle:L<=rem:=by omega
  have hws_eq:yu n hn p start rem =
     (start,L) :: yu n hn p (q8 n hn start L) (rem-L):=by
   conv_lhs=>unfold yu
   have h1:1<=xv n hn p start 1 rem:=hL1;have h2:xv n hn p start 1 rem<=rem:=hLle;simp only [show rem≠0 by omega,Zf,h1,h2,and_self,Zd];rfl
  have hisArc0:y9 n hn p start L=true:=by
   rw [y3];exact ⟨hL1,by omega,by rw [hps];rfl,hLpin,hLunp⟩
  cases hpL:p (q8 n hn start L) with
  | none=>rw [hpL] at hLpin;simp at hLpin
  | some bMid =>
   have hsign0:zv n hn p start L=decide (bStart≠bMid):=by
     simp [zv,hps,hpL]
   by_cases hLr:L=rem
   . have hbEq:bMid=bEnd:=Option.some.inj (by rw [<- hLr,hpL] at hpe;exact hpe);subst hbEq
     have hnil:yu n hn p (q8 n hn start L) (rem-L)=[]:=by
       rw [show rem-L=0 by omega];unfold yu;simp
     rw [hws_eq,hnil]
     refine ⟨by simp [hLr],by omega,?_,?_,by simp,?_,?_,?_⟩
     . rw [List.map_cons,List.map_nil,wd,b9,bt,List.length_singleton];rw [y1 n hn p start rem hrem1 bStart bMid (fun r hr1 hr2=>hLunp r hr1 (by omega))];congr 1;dsimp only [zr];rw [hsign0,hLr]
       cases bStart <;> cases bMid <;> rfl
     . intro a ha;simp at ha;rw [ha];exact hisArc0
     . intro i;simp only [List.map_cons,List.map_nil,List.mem_singleton];constructor
       . intro hi;rw [hi];exact ⟨0,by omega,yg n hn start,by rw [hps];rfl⟩
       . rintro ⟨r,hr1,hr2,hr3⟩
         by_cases hr0:r=0
         . subst hr0;rw [yg] at hr2;exact hr2.symm
         . have hnone:=hLunp r (by omega) (by omega);rw [hr2] at hnone;rw [hnone] at hr3;simp at hr3
     . simp only [List.countP_cons,List.countP_nil,Nat.zero_add,<-hLr]
       have hmodL:(q8 n hn start L).1 %2=(start.1+L)%2 :=
         Nat.mod_mul_right_mod (start.1+L) 2 n
       rw [hmodL]
       rcases (show start.1 %2=0\/start.1 %2=1 by omega) with hs | hs <;>
       rcases (show L %2=0\/L %2=1 by omega) with hLp | hLp
       . simp [hs,hLp,show (start.1+L)%2=0 by omega]
       . simp [hs,hLp,show (start.1+L)%2=1 by omega]
       . simp [hs,hLp,show (start.1+L)%2=1 by omega]
       . simp [hs,hLp,show (start.1+L)%2=0 by omega]
     . simp only [List.countP_cons,List.countP_nil,Nat.zero_add,hsign0]
       cases bStart <;> cases bMid <;> decide
   . have hLlt:L< rem:=by omega
     have hrem'1:1<=rem-L:=by omega
     have hrem'2:rem-L<=2*n:=by omega
     have hpe':p (q8 n hn (q8 n hn start L) (rem-L))=some bEnd:=by
       rw [xc,show L+(rem-L)=rem by omega];exact hpe
     rcases ih (rem-L) (by omega) (q8 n hn start L) bMid bEnd hrem'1 hrem'2 hpL hpe' with
       ⟨ih_sum,ih_len,ih_seg,ih_arc,ih_nod,ih_mem,ih_col,ih_sig⟩
     rw [hws_eq];set tail:=yu n hn p (q8 n hn start L) (rem-L)
     refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
     . simp only [List.map_cons,List.sum_cons,ih_sum];omega
     . simp only [List.length_cons];omega
     . rw [px n hn p start L rem hL1 hLlt bStart bMid bEnd hpL];rw [y1 n hn p start L hL1 bStart bMid hLunp,ih_seg];rw [pm,kg,kh,List.map_cons,wd,List.length_cons]
       have hpow:(2:ℤ)^(L-1)*(2:ℤ)^(rem-L-tail.length) =
           (2:ℤ)^(rem-(tail.length+1)):=by
         rw [<- pow_add];congr 1;omega
       rw [hpow];congr 2;dsimp only [zr];rw [hsign0]
       cases bStart <;> cases bMid <;> rfl
     . intro a ha;simp only [List.mem_cons] at ha
       rcases ha with rfl | ha
       . exact hisArc0
       . exact ih_arc a ha
     . rw [List.map_cons,List.nodup_cons]
       refine ⟨?_,ih_nod⟩
       intro hmem
       rcases (ih_mem start).mp hmem with ⟨r,hr1,hr2,_⟩
       rw [xc] at hr2
       have hval:=congrArg Fin.val hr2
       simp only [q8] at hval
       have hlr_pos:0< L+r:=by omega
       have hlr_lt:L+r< 2*n:=by omega
       have hst:=start.isLt
       by_cases hlt:start.1+(L+r)< 2*n
       . rw [Zm hlt] at hval;omega
       . rw [Nat.mod_eq_sub_mod (by omega),Zm (by omega)] at hval;omega
     . intro i;simp only [List.map_cons,List.mem_cons,ih_mem];constructor
       . rintro (hi | ⟨r,hr1,hr2,hr3⟩)
         . rw [hi];exact ⟨0,by omega,yg n hn start,by rw [hps];rfl⟩
         . rw [xc] at hr2;exact ⟨L+r,by omega,hr2,hr3⟩
       . rintro ⟨r,hr1,hr2,hr3⟩
         by_cases hr0:r=0
         . left;subst hr0;rw [yg] at hr2;exact hr2.symm
         . by_cases hrL:r< L
           . have hnone:=hLunp r (by omega) hrL;rw [hr2] at hnone;rw [hnone] at hr3;simp at hr3
           . right
             refine ⟨r-L,by omega,?_,hr3⟩
             rw [xc,show L+(r-L)=r by omega];exact hr2
     . simp only [List.countP_cons,Nat.cast_add];rw [xc,show L+(rem-L)=rem by omega] at ih_col
       have hmodL:(q8 n hn start L).1 %2=(start.1+L)%2 :=
         Nat.mod_mul_right_mod (start.1+L) 2 n
       rw [hmodL] at ih_col
       have hhead :
           ((if decide (L %2=1/\start.1 %2=0) then 1 else 0:ℕ):ℤ) -
           ((if decide (L %2=1/\start.1 %2=1) then 1 else 0:ℕ):ℤ) =
           (if (start.1+L)%2=1 then 1 else 0) -
           (if start.1 %2=1 then 1 else 0):=by
         rcases (show start.1 %2=0\/start.1 %2=1 by omega) with hs | hs <;>
         rcases (show L %2=0\/L %2=1 by omega) with hLp | hLp
         . simp [hs,hLp,show (start.1+L)%2=0 by omega]
         . simp [hs,hLp,show (start.1+L)%2=1 by omega]
         . simp [hs,hLp,show (start.1+L)%2=1 by omega]
         . simp [hs,hLp,show (start.1+L)%2=0 by omega]
       linarith
     . simp only [List.countP_cons,hsign0]
       cases bStart <;> cases bMid <;> cases bEnd <;> simp at ih_sig ⊢ <;> omega
lemma kc (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
   (k₀:Fin (2*n)) (b₀:Bool) (hk₀:p k₀=some b₀) :
   let ws:=yu n hn p k₀ (2*n)
   ws.Nodup /\
   ws.length=z2 n p /\
   (∀ a:Fin (2*n) × ℕ,a ∈ ws ↔ y9 n hn p a.1 a.2=true):=by
 rcases pl n hn p (2*n) k₀ b₀ b₀ (by omega) le_rfl hk₀ (by rw [vr];exact hk₀) with
   ⟨_,_,_,harc,hnod_fst,hmem_fst,_,_⟩
 set ws:=yu n hn p k₀ (2*n);have hnod:ws.Nodup:=List.Nodup.of_map Prod.fst hnod_fst
 have hmem_pin:∀ i:Fin (2*n),i ∈ ws.map Prod.fst ↔ (p i).isSome=true:=by
   intro i;rw [hmem_fst i];constructor
   . rintro ⟨_,_,_,h⟩;exact h
   . intro hp
     let r:=(2*n+i.1-k₀.1)%(2*n)
     refine ⟨r,Nat.mod_lt _ (by omega),?_,hp⟩
     apply Zx;simp only [q8,r]
     have h1:(k₀.1+(2*n+i.1-k₀.1)%(2*n))%(2*n) =
       (k₀.1+(2*n+i.1-k₀.1))%(2*n):=by
      rw [Nat.add_mod,Nat.mod_mod,<-Nat.add_mod]
     rw [h1]
     have h2:k₀.1+(2*n+i.1-k₀.1)=2*n+i.1:=by have:=k₀.isLt;omega
     rw [h2,Nat.add_mod_left,Zm i.isLt]
 refine ⟨hnod,?_,?_⟩
 . have hset:(Finset.univ.filter (fun i:Fin (2*n)=>(p i).isSome))=(ws.map Prod.fst).toFinset:=by
     ext i;simp [hmem_pin]
   unfold z2;rw [hset,List.toFinset_card_of_nodup hnod_fst,List.length_map]
 . intro a;constructor
   . exact harc a
   . intro his
     have hpin:(p a.1).isSome=true:=((y3 n hn p a.1 a.2).mp his).2.2.1
     have hfst:a.1 ∈ ws.map Prod.fst:=(hmem_pin a.1).mpr hpin
     rw [List.mem_map] at hfst
     rcases hfst with ⟨a',ha',heq1⟩
     have his':y9 n hn p a.1 a'.2=true:=by rw [<- heq1];exact harc a' ha'
     have heq2:a'.2=a.2:=bb n hn p a.1 his' his;have haeq:a'=a:=Prod.ext heq1 heq2;rwa [<- haeq]
lemma xf (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
  (hpin:0< z2 n p) :
  pb n hn p=wr ((2:ℤ)^(2*n-z2 n p))
    (wy n (z3 n hn p) (qo n hn p) (qd n hn p)) /\
  (∑ j:Fin n,(2*j.1+1) *
      (z3 n hn p j false false+z3 n hn p j false true +
       z3 n hn p j true false+z3 n hn p j true true)) +
  (∑ j:Fin n,2*(j.1+1)*(qo n hn p j+qd n hn p j))=2*n /\
  (∑ j:Fin n,
      (z3 n hn p j false false+z3 n hn p j false true +
       z3 n hn p j true false+z3 n hn p j true true)) +
  (∑ j:Fin n,(qo n hn p j+qd n hn p j))=z2 n p /\
  (∑ j:Fin n,(z3 n hn p j false false+z3 n hn p j false true)) =
  (∑ j:Fin n,(z3 n hn p j true false+z3 n hn p j true true)) /\
  ((∑ j:Fin n,(z3 n hn p j false true+z3 n hn p j true true)) +
   (∑ j:Fin n,qd n hn p j))%2=0:=by
 have hex:∃ k₀:Fin (2*n),(p k₀).isSome=true:=by
  have hne:(Finset.univ.filter (fun k:Fin (2*n)=>(p k).isSome)).Nonempty :=
    Finset.card_pos.mp hpin
  rcases hne with ⟨k₀,hk₀⟩
  exact ⟨k₀,by simpa using hk₀⟩
 rcases hex with ⟨k₀,hk₀_some⟩
 cases hk₀:p k₀ with
 | none=>rw [hk₀] at hk₀_some;simp at hk₀_some
 | some b₀ =>
  rcases pl n hn p (2*n) k₀ b₀ b₀ (by omega) le_rfl hk₀ (by rw [vr];exact hk₀) with
    ⟨hsum,_,hseg,_,_,_,hcol,hsig⟩
  rcases kc n hn p k₀ b₀ hk₀ with ⟨hnod,hlen,hiff⟩
  set ws:=yu n hn p k₀ (2*n)
  have hcnt_fixedL (L:ℕ) (Q:Fin (2*n)->Bool) :
      ws.countP (fun a=>decide (a.2=L)&&Q a.1) =
      (Finset.univ.filter (fun i:Fin (2*n)=>y9 n hn p i L=true/\Q i=true)).card:=by
    rw [List.countP_eq_length_filter];have hnod_f:(ws.filter (fun a=>decide (a.2=L)&&Q a.1)).Nodup:=hnod.filter _;rw [<- List.toFinset_card_of_nodup hnod_f]
    refine Finset.card_bij (fun a _=>a.1) ?_ ?_ ?_
    . intro a ha
      simp only [List.mem_toFinset,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq,
        Zv,Zu,true_and] at ha ⊢
      exact ⟨by rw [<- ha.2.1];exact (hiff a).mp ha.1,ha.2.2⟩
    . intro a₁ ha₁ a₂ ha₂ heq;simp only [List.mem_toFinset,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at ha₁ ha₂;exact Prod.ext heq (ha₁.2.1.trans ha₂.2.1.symm)
    . intro i hi;simp only [Zv,Zu,true_and] at hi;exact ⟨(i,L),by simp [List.mem_toFinset,List.mem_filter,(hiff (i,L)).mpr hi.1,hi.2],rfl⟩
  have hws_odd (j:Fin n) (c sig:Bool) :
      ws.countP (fun a=>decide (a.2=2*j.1+1) &&
        (decide (decide (a.1.1 %2=1)=c)&&decide (zv n hn p a.1 (2*j.1+1)=sig))) =
      z3 n hn p j c sig:=by
    rw [hcnt_fixedL (2*j.1+1) (fun i =>
      decide (decide (i.1 %2=1)=c)&&decide (zv n hn p i (2*j.1+1)=sig))]
    unfold z3;apply congrArg Finset.card;ext i;simp [and_assoc]
  have hws_evP (j:Fin n) :
      ws.countP (fun a=>decide (a.2=2*(j.1+1)) &&
        decide (zv n hn p a.1 (2*(j.1+1))=false)) =
      qo n hn p j:=by
    rw [hcnt_fixedL (2*(j.1+1)) (fun i=>decide (zv n hn p i (2*(j.1+1))=false))];unfold qo;apply congrArg Finset.card;ext i;simp
  have hws_evM (j:Fin n) :
      ws.countP (fun a=>decide (a.2=2*(j.1+1)) &&
        decide (zv n hn p a.1 (2*(j.1+1))=true)) =
      qd n hn p j:=by
    rw [hcnt_fixedL (2*(j.1+1)) (fun i=>decide (zv n hn p i (2*(j.1+1))=true))];unfold qd;apply congrArg Finset.card;ext i;simp
  have hperm_fac:(ws.map (zr n hn p)).Perm
      (xd n (z3 n hn p) (qo n hn p) (qd n hn p)):=by
    rw [List.perm_iff_count];intro t
    have hcount_inv :
        (xd n (z3 n hn p) (qo n hn p) (qd n hn p)).count t =
        (∑ j:Fin n,
          ((if (j.1+1,j.1,(1:ℤ))=t then z3 n hn p j false false else 0) +
           (if (j.1+1,j.1,(-1:ℤ))=t then z3 n hn p j false true else 0) +
           (if (j.1,j.1+1,(1:ℤ))=t then z3 n hn p j true false else 0) +
           (if (j.1,j.1+1,(-1:ℤ))=t then z3 n hn p j true true else 0))) +
        (∑ j:Fin n,
          ((if (j.1+1,j.1+1,(1:ℤ))=t then qo n hn p j else 0) +
           (if (j.1+1,j.1+1,(-1:ℤ))=t then qd n hn p j else 0))):=by
      have hz:=vf n (z3 n hn p) (qo n hn p) (qd n hn p)
        (fun x=>if x=t then (1:ℤ) else 0)
      have hL_z:(((xd n (z3 n hn p) (qo n hn p) (qd n hn p)).map
          fun x=>if x=t then (1:ℤ) else 0).sum) =
          ((xd n (z3 n hn p) (qo n hn p) (qd n hn p)).count t:ℤ):=by
        generalize xd n (z3 n hn p) (qo n hn p) (qd n hn p)=l
        induction l with
        | nil=>simp
        | cons x xs ih =>
          simp only [List.map_cons,List.sum_cons,List.count_cons,ih]
          by_cases hx:x=t
          . subst hx;simp [add_comm]
          . simp [hx]
      rw [hL_z] at hz;apply Int.ofNat.inj;simp only [Int.ofNat_eq_coe];rw [hz]
      push_cast
      congr 1 <;> (apply Zc rfl;intro j _;split_ifs <;> ring)
    rw [hcount_inv,List.count_eq_countP,List.countP_map]
    have hws_part:∀ (F:Fin (2*n) × ℕ->ℕ),
        (ws.map F).sum =
        (∑ j:Fin n,
          ((ws.filter (fun a=>decide (a.2=2*j.1+1))).map F).sum) +
        (∑ j:Fin n,
          ((ws.filter (fun a=>decide (a.2=2*(j.1+1)))).map F).sum):=by
      intro F
      have hlen_range:∀ a ∈ ws,1<=a.2/\a.2<=2*n:=by
        intro a ha;have h:=(y3 n hn p a.1 a.2).mp ((hiff a).mp ha);exact ⟨h.1,h.2.1⟩
      have hpart_list:∀ l:List (Fin (2*n) × ℕ),
          (∀ a ∈ l,1<=a.2/\a.2<=2*n) ->
          (l.map F).sum =
          (∑ j:Fin n,((l.filter (fun a=>decide (a.2=2*j.1+1))).map F).sum) +
          (∑ j:Fin n,((l.filter (fun a=>decide (a.2=2*(j.1+1)))).map F).sum):=by
        intro l hl
        induction l with
        | nil=>simp
        | cons a as ihas =>
          have ha:=hl a (List.mem_cons_self ..);have has:=ihas (fun x hx=>hl x (List.mem_cons_of_mem _ hx));simp only [List.map_cons,List.sum_cons,has,List.filter_cons]
          by_cases hpar:a.2 %2=1
          . let j0:Fin n:=⟨a.2/2,by omega⟩
            have hj0:a.2=2*j0.1+1:=by dsimp [j0];omega
            have h1:(∑ j:Fin n,(((if decide (a.2=2*j.1+1) then a :: as.filter (fun x=>decide (x.2=2*j.1+1)) else as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum)) =
              F a+∑ j:Fin n,((as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum:=by
             rw [<- Finset.add_sum_erase Finset.univ _ (Zu j0),
               <- Finset.add_sum_erase Finset.univ (fun j:Fin n=>((as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum) (Zu j0)]
             have hhit:decide (a.2=2*j0.1+1)=true:=decide_eq_true hj0;rw [hhit];simp only [Zh,List.map_cons,List.sum_cons]
             have hrest:∀ j ∈ Finset.univ.erase j0,
               (((if decide (a.2=2*j.1+1) then a :: as.filter (fun x=>decide (x.2=2*j.1+1)) else as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum) =
               ((as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum:=by
              intro j hj;rw [Finset.mem_erase] at hj
              have hne:a.2≠2*j.1+1:=fun h=>hj.1 (Zx (by omega))
              rw [decide_eq_false hne];simp
             rw [Zc rfl hrest];omega
            have h2:(∑ j:Fin n,(((if decide (a.2=2*(j.1+1)) then a :: as.filter (fun x=>decide (x.2=2*(j.1+1))) else as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum)) =
              ∑ j:Fin n,((as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum:=by
             apply Zc rfl;intro j _
             have hne:a.2≠2*(j.1+1):=by omega
             rw [decide_eq_false hne];simp
            rw [h1,h2];omega
          . let j0:Fin n:=⟨a.2/2-1,by omega⟩
            have hj0:a.2=2*(j0.1+1):=by dsimp [j0];omega
            have h1:(∑ j:Fin n,(((if decide (a.2=2*j.1+1) then a :: as.filter (fun x=>decide (x.2=2*j.1+1)) else as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum)) =
              ∑ j:Fin n,((as.filter (fun x=>decide (x.2=2*j.1+1))).map F).sum:=by
             apply Zc rfl;intro j _
             have hne:a.2≠2*j.1+1:=by omega
             rw [decide_eq_false hne];simp
            have h2:(∑ j:Fin n,(((if decide (a.2=2*(j.1+1)) then a :: as.filter (fun x=>decide (x.2=2*(j.1+1))) else as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum)) =
              F a+∑ j:Fin n,((as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum:=by
             rw [<- Finset.add_sum_erase Finset.univ _ (Zu j0),
               <- Finset.add_sum_erase Finset.univ (fun j:Fin n=>((as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum) (Zu j0)]
             have hhit:decide (a.2=2*(j0.1+1))=true:=decide_eq_true hj0;rw [hhit];simp only [Zh,List.map_cons,List.sum_cons]
             have hrest:∀ j ∈ Finset.univ.erase j0,
               (((if decide (a.2=2*(j.1+1)) then a :: as.filter (fun x=>decide (x.2=2*(j.1+1))) else as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum) =
               ((as.filter (fun x=>decide (x.2=2*(j.1+1)))).map F).sum:=by
              intro j hj;rw [Finset.mem_erase] at hj
              have hne:a.2≠2*(j.1+1):=fun h=>hj.1 (Zx (by omega))
              rw [decide_eq_false hne];simp
             rw [Zc rfl hrest];omega
            rw [h1,h2];omega
      exact hpart_list ws hlen_range
    have hcount_as_sum (Q:Fin (2*n) × ℕ->Bool) :
        ws.countP Q=(ws.map fun a=>if Q a then 1 else 0).sum:=by
      generalize ws=l;induction l with | nil=>simp | cons a as ih =>
        simp only [List.countP_cons,List.map_cons,List.sum_cons,ih];cases Q a <;> simp <;> omega
    rw [hcount_as_sum,hws_part];simp only [Function.comp_apply]
    have hsum_map_add (l:List (Fin (2*n) × ℕ)) (f₁ f₂:Fin (2*n) × ℕ->ℕ) :
        (l.map fun x=>f₁ x+f₂ x).sum=(l.map f₁).sum+(l.map f₂).sum:=by
      induction l with | nil=>simp | cons x xs ih=>simp [ih];omega
    have hsum_ite (l:List (Fin (2*n) × ℕ)) (P:Prop) [Decidable P] (f:Fin (2*n) × ℕ->ℕ) :
        (l.map fun x=>if P then f x else 0).sum=if P then (l.map f).sum else 0:=by
      by_cases hP:P <;> simp [hP]
    congr 1
    . apply Zc rfl;intro j _;rw [<- hws_odd j false false,<-hws_odd j false true,<-hws_odd j true false,<-hws_odd j true true]
      have hcf (c sig:Bool) :
          ws.countP (fun a=>decide (a.2=2*j.1+1) &&
            (decide (decide (a.1.1 %2=1)=c)&&decide (zv n hn p a.1 (2*j.1+1)=sig))) =
          ((ws.filter (fun a=>decide (a.2=2*j.1+1))).map fun a =>
            if decide (decide (a.1.1 %2=1)=c)&&decide (zv n hn p a.1 (2*j.1+1)=sig) then 1 else 0).sum:=by
        generalize ws=l;induction l with | nil=>simp | cons a as ih =>
          simp only [List.countP_cons,List.filter_cons,ih]
          by_cases h1:a.2=2*j.1+1
          . by_cases h2:decide (a.1.1 %2=1)=c/\zv n hn p a.1 (2*j.1+1)=sig <;>
             simp [h1,h2] <;> omega
          . simp [h1]
      rw [hcf false false,hcf false true,hcf true false,hcf true true]
      have hterm:∀ a ∈ ws.filter (fun a=>decide (a.2=2*j.1+1)),
          (if (zr n hn p a == t) then 1 else 0) =
          (if (j.1+1,j.1,(1:ℤ))=t then (if decide (decide (a.1.1 %2=1)=false)&&decide (zv n hn p a.1 (2*j.1+1)=false) then 1 else 0) else 0) +
          (if (j.1+1,j.1,(-1:ℤ))=t then (if decide (decide (a.1.1 %2=1)=false)&&decide (zv n hn p a.1 (2*j.1+1)=true) then 1 else 0) else 0) +
          (if (j.1,j.1+1,(1:ℤ))=t then (if decide (decide (a.1.1 %2=1)=true)&&decide (zv n hn p a.1 (2*j.1+1)=false) then 1 else 0) else 0) +
          (if (j.1,j.1+1,(-1:ℤ))=t then (if decide (decide (a.1.1 %2=1)=true)&&decide (zv n hn p a.1 (2*j.1+1)=true) then 1 else 0) else 0):=by
        intro a ha
        rcases a with ⟨ai,aL⟩
        simp only [List.mem_filter,decide_eq_true_eq] at ha
        rcases ha with ⟨_,rfl⟩
        have hodd_mod:(2*j.1+1)%2≠0:=by omega
        have hodd_div:(2*j.1+1)/2=j.1:=by omega
        dsimp only [zr]
        by_cases hc:ai.1 %2=1 <;> by_cases hs:zv n hn p ai (2*j.1+1)=true <;>
          simp [wl,hodd_mod,hodd_div,hc,hs]
      rw [List.map_congr_left hterm,hsum_map_add,hsum_map_add,hsum_map_add,
        hsum_ite,hsum_ite,hsum_ite,hsum_ite]
    . apply Zc rfl;intro j _;rw [<- hws_evP j,<-hws_evM j]
      have hcf (sig:Bool) :
          ws.countP (fun a=>decide (a.2=2*(j.1+1))&&decide (zv n hn p a.1 (2*(j.1+1))=sig)) =
          ((ws.filter (fun a=>decide (a.2=2*(j.1+1)))).map fun a =>
            if decide (zv n hn p a.1 (2*(j.1+1))=sig) then 1 else 0).sum:=by
        generalize ws=l;induction l with | nil=>simp | cons a as ih =>
          simp only [List.countP_cons,List.filter_cons,ih]
          by_cases h1:a.2=2*(j.1+1)
          . by_cases h2:zv n hn p a.1 (2*(j.1+1))=sig <;>
             simp [h1,h2] <;> omega
          . simp [h1]
      rw [hcf false,hcf true]
      have hterm:∀ a ∈ ws.filter (fun a=>decide (a.2=2*(j.1+1))),
          (if (zr n hn p a == t) then 1 else 0) =
          (if (j.1+1,j.1+1,(1:ℤ))=t then (if decide (zv n hn p a.1 (2*(j.1+1))=false) then 1 else 0) else 0) +
          (if (j.1+1,j.1+1,(-1:ℤ))=t then (if decide (zv n hn p a.1 (2*(j.1+1))=true) then 1 else 0) else 0):=by
        intro a ha
        rcases a with ⟨ai,aL⟩
        simp only [List.mem_filter,decide_eq_true_eq] at ha
        rcases ha with ⟨_,rfl⟩
        have hev_mod:(2*(j.1+1))%2=0:=by omega
        have hev_div:(2*(j.1+1))/2=j.1+1:=by omega
        dsimp only [zr]
        by_cases hs:zv n hn p ai (2*(j.1+1))=true <;>
          simp [wl,hev_mod,hev_div,hs]
      rw [List.map_congr_left hterm,hsum_map_add,hsum_ite,hsum_ite]
  have hperm_sum (F:ℕ × ℕ × ℤ->ℕ) :
      ((ws.map (zr n hn p)).map F).sum =
      ((xd n (z3 n hn p) (qo n hn p) (qd n hn p)).map F).sum :=
    (hperm_fac.map F).sum_eq
  have hinv_nat (F:ℕ × ℕ × ℤ->ℕ) :
      ((xd n (z3 n hn p) (qo n hn p) (qd n hn p)).map F).sum =
      (∑ j:Fin n,
        (z3 n hn p j false false*F (j.1+1,j.1,1) +
         z3 n hn p j false true*F (j.1+1,j.1,-1) +
         z3 n hn p j true false*F (j.1,j.1+1,1) +
         z3 n hn p j true true*F (j.1,j.1+1,-1))) +
      (∑ j:Fin n,
        (qo n hn p j*F (j.1+1,j.1+1,1) +
         qd n hn p j*F (j.1+1,j.1+1,-1))):=by
    have hz:=vf n (z3 n hn p) (qo n hn p) (qd n hn p) (fun x=>(F x:ℤ))
    have hcast:(((xd n (z3 n hn p) (qo n hn p) (qd n hn p)).map F).sum:ℤ) =
        ((xd n (z3 n hn p) (qo n hn p) (qd n hn p)).map (fun x=>(F x:ℤ))).sum:=by
      generalize xd n (z3 n hn p) (qo n hn p) (qd n hn p)=l
      induction l with | nil=>simp | cons x xs ih=>simp [ih]
    apply Int.ofNat.inj;simp only [Int.ofNat_eq_coe];rw [hcast,hz];push_cast;rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  . rw [xz n hn p k₀ b₀ hk₀,hseg,hlen];congr 1;unfold wy
    have hmap_eq:(ws.map fun a=>let t:=zr n hn p a;zi t.1 t.2.1 t.2.2) =
        (ws.map (zr n hn p)).map (fun t=>zi t.1 t.2.1 t.2.2):=by
      rw [List.map_map];rfl
    rw [hmap_eq];exact yt (hperm_fac.map _)
  . have h:=hperm_sum (fun t=>t.1+t.2.1);rw [hinv_nat] at h
    have hL_eq:((ws.map (zr n hn p)).map (fun t=>t.1+t.2.1)).sum=(ws.map Prod.snd).sum:=by
      rw [List.map_map];congr 1;apply List.map_congr_left;intro a _;simp only [Function.comp_apply,zr,wl]
      by_cases hp2:a.2 %2=0 <;> cases decide (a.1.1 %2=1) <;> simp [hp2] <;> omega
    rw [hL_eq,hsum] at h;dsimp only at h;rw [h];congr 1 <;> (apply Zc rfl;intro j _;ring)
  . have h:=hperm_sum (fun _=>1);rw [hinv_nat] at h
    have hL_eq:((ws.map (zr n hn p)).map (fun _=>1)).sum=ws.length:=by
      rw [List.map_map];generalize ws=l;induction l with | nil=>simp | cons _ _ ih=>simp [ih];omega
    rw [hL_eq,hlen] at h;rw [h];congr 1 <;> (apply Zc rfl;intro j _;ring)
  . have h0:=hperm_sum (fun t=>if t.1 > t.2.1 then 1 else 0);have h1:=hperm_sum (fun t=>if t.2.1 > t.1 then 1 else 0);rw [hinv_nat] at h0 h1
    have hws0:((ws.map (zr n hn p)).map (fun t=>if t.1 > t.2.1 then 1 else 0)).sum =
        ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=0)):=by
      rw [List.map_map]
      generalize ws=l;induction l with | nil=>simp | cons a as ih =>
        simp only [List.map_cons,List.sum_cons,List.countP_cons,Function.comp_apply,ih,zr,wl]
        by_cases hp2:a.2 %2=0 <;> by_cases hc:a.1.1 %2=0 <;>
          simp [hp2,hc,show a.1.1 %2=1 ↔ a.1.1 %2≠0 by omega,
              show a.2 %2=1 ↔ a.2 %2≠0 by omega] <;> omega
    have hws1:((ws.map (zr n hn p)).map (fun t=>if t.2.1 > t.1 then 1 else 0)).sum =
        ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=1)):=by
      rw [List.map_map]
      generalize ws=l;induction l with | nil=>simp | cons a as ih =>
        simp only [List.map_cons,List.sum_cons,List.countP_cons,Function.comp_apply,ih,zr,wl]
        by_cases hp2:a.2 %2=0 <;> by_cases hc:a.1.1 %2=1 <;>
          simp [hp2,hc,show a.2 %2=1 ↔ a.2 %2≠0 by omega] <;> omega
    rw [hws0] at h0;rw [hws1] at h1;rw [vr] at hcol
    have heq_cnt:ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=0)) =
        ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=1)):=by omega
    have h0':∑ j:Fin n,(z3 n hn p j false false+z3 n hn p j false true) =
        ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=0)):=by
      rw [h0];simp
    have h1':∑ j:Fin n,(z3 n hn p j true false+z3 n hn p j true true) =
        ws.countP (fun a=>decide (a.2 %2=1/\a.1.1 %2=1)):=by
      rw [h1];simp
    omega
  . have hm:=hperm_sum (fun t=>if t.2.2=-1 then 1 else 0);rw [hinv_nat] at hm
    have hwsm:((ws.map (zr n hn p)).map (fun t=>if t.2.2=-1 then 1 else 0)).sum =
        ws.countP (fun a=>zv n hn p a.1 a.2):=by
      rw [List.map_map]
      generalize ws=l;induction l with | nil=>simp | cons a as ih =>
        simp only [List.map_cons,List.sum_cons,List.countP_cons,Function.comp_apply,ih,zr]
        by_cases h:zv n hn p a.1 a.2=true <;> simp [h] <;> omega
    rw [hwsm] at hm
    have hne_self:¬ (b₀≠b₀):=fun h=>h rfl
    have hpar0:ws.countP (fun a=>zv n hn p a.1 a.2)%2=0:=by
      have hnot1:ws.countP (fun a=>zv n hn p a.1 a.2)%2≠1 :=
        fun h=>hne_self (hsig.mp h)
      omega
    have hm':(∑ j:Fin n,(z3 n hn p j false true+z3 n hn p j true true)) +
        (∑ j:Fin n,qd n hn p j) =
        ws.countP (fun a=>zv n hn p a.1 a.2):=by
      rw [hm];simp
    omega
def zp (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) :
  Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ) :=
 if z2 n p=0 then none
 else
  let red:=z0 n (qo n hn p) (qd n hn p)
  some (z3 n hn p,red.1,red.2.1,red.2.2)
lemma p3 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) :
   pb n hn p 0 0=(2:ℤ)^(2*n-z2 n p):=by
 by_cases hp:z2 n p=0
 . have hall:p=fun _=>none:=by
    funext k
    cases hpk:p k
    . rfl
    . exfalso;have hpos:0< z2 n p:=Finset.card_pos.mpr ⟨k,by simp [hpk]⟩;omega
   rw [hp,hall,Nat.sub_zero,cg n hn];simp [wr,zi,v9,jk,bm,show n≠0 by omega,show 0≠n by omega]
 . rcases xf n hn p (by omega) with ⟨hH,_,_,_,_⟩
   rw [hH]
   have h00:wy n (z3 n hn p) (qo n hn p) (qd n hn p) 0 0=1 :=
    (j3 _ (p2 n _ _ _)).1
   simp [wr,h00]
lemma yv (n:ℕ) (hn:0< n) (p q:Fin (2*n)->Option Bool) :
   (∀ d1 ≤ n,∀ d2 ≤ n,wt n hn p d1 d2=wt n hn q d1 d2) ↔
   zp n hn p=zp n hn q:=by
 rw [<- ki];constructor
 . intro hH
   have h00:(2:ℤ)^(2*n-z2 n p)=(2:ℤ)^(2*n-z2 n q):=by
     rw [<- p3 n hn p,<-p3 n hn q,hH]
   have hpow_inj:2*n-z2 n p=2*n-z2 n q:=by
     have hnat:2^(2*n-z2 n p)=2^(2*n-z2 n q):=by
       exact_mod_cast h00
     exact Nat.pow_right_injective (by decide:1< 2) hnat
   have hp_le:z2 n p<=2*n:=by
     simpa [z2] using Finset.card_filter_le (Finset.univ:Finset (Fin (2*n))) _
   have hq_le:z2 n q<=2*n:=by
     simpa [z2] using Finset.card_filter_le (Finset.univ:Finset (Fin (2*n))) _
   have hnum_eq:z2 n p=z2 n q:=by omega
   unfold zp
   by_cases hp0:z2 n p=0
   . simp [hp0,<-hnum_eq]
   . have hq0:z2 n q≠0:=by omega
     simp only [hp0,hq0,Zj,Option.some.injEq,Prod.mk.injEq]
     rcases xf n hn p (by omega) with ⟨hHp,hlenp,hcntp,_,_⟩
     rcases xf n hn q (by omega) with ⟨hHq,hlenq,hcntq,_,_⟩
     rcases y2 n (z3 n hn p) (qo n hn p) (qd n hn p) (by omega) with
       ⟨hrbivp,hdisjp,_,_,hrcntp,_,_⟩
     rcases y2 n (z3 n hn q) (qo n hn q) (qd n hn q) (by omega) with
       ⟨hrbivq,hdisjq,_,_,hrcntq,_,_⟩
     have hscale_eq :
        wr ((2:ℤ)^(2*n-z2 n p))
          (wy n (z3 n hn p) (z0 n (qo n hn p) (qd n hn p)).1
           (z0 n (qo n hn p) (qd n hn p)).2.1) =
        wr ((2:ℤ)^(2*n-z2 n p))
          (wy n (z3 n hn q) (z0 n (qo n hn q) (qd n hn q)).1
           (z0 n (qo n hn q) (qd n hn q)).2.1):=by
       rw [hrbivp,hrbivq,<-hHp,hH,hHq,hnum_eq]
     have hinv_eq :
        wy n (z3 n hn p) (z0 n (qo n hn p) (qd n hn p)).1
          (z0 n (qo n hn p) (qd n hn p)).2.1 =
        wy n (z3 n hn q) (z0 n (qo n hn q) (qd n hn q)).1
          (z0 n (qo n hn q) (qd n hn q)).2.1:=by
       funext a b;have h:=congrFun (congrFun hscale_eq a) b;exact mul_left_cancel₀ (by positivity:((2:ℤ)^(2*n-z2 n p))≠0) h
     rcases va n _ _ _ _ _ _ hdisjp hdisjq hinv_eq with ⟨ho,hep,hem⟩
     refine ⟨ho,hep,hem,?_⟩
     rw [<- hrcntp] at hcntp;rw [<- hrcntq] at hcntq;rw [ho,hep,hem] at hcntp;omega
 . intro hcan;unfold zp at hcan
   by_cases hp0:z2 n p=0
   . by_cases hq0:z2 n q=0
     . have hallp:p=fun _=>none:=by
        funext k;cases hpk:p k
        . rfl
        . exfalso;have:0< z2 n p:=Finset.card_pos.mpr ⟨k,by simp [hpk]⟩;omega
       have hallq:q=fun _=>none:=by
        funext k;cases hqk:q k
        . rfl
        . exfalso;have:0< z2 n q:=Finset.card_pos.mpr ⟨k,by simp [hqk]⟩;omega
       rw [hallp,hallq]
     . simp [hp0,hq0] at hcan
   . by_cases hq0:z2 n q=0
     . simp [hp0,hq0] at hcan
     . simp only [hp0,hq0,Zj,Option.some.injEq,Prod.mk.injEq] at hcan
       rcases hcan with ⟨ho,hep,hem,hfus⟩
       rcases xf n hn p (by omega) with ⟨hHp,hlenp,hcntp,_,_⟩
       rcases xf n hn q (by omega) with ⟨hHq,hlenq,hcntq,_,_⟩
       rcases y2 n (z3 n hn p) (qo n hn p) (qd n hn p) (by omega) with
        ⟨hrbivp,_,_,_,hrcntp,_,_⟩
       rcases y2 n (z3 n hn q) (qo n hn q) (qd n hn q) (by omega) with
        ⟨hrbivq,_,_,_,hrcntq,_,_⟩
       have hnum_eq:z2 n p=z2 n q:=by
        rw [<- hcntp,<-hcntq,<-hrcntp,<-hrcntq,ho,hep,hem,hfus]
       rw [hHp,hHq,hnum_eq,<-hrbivp,<-hrbivq,ho,hep,hem]
def ql (w:ℕ->ℕ) (c:ℕ):ℕ :=
 ((List.range c).map w).sum
lemma wf (w:ℕ->ℕ) (c:ℕ):ql w (c+1)=ql w c+w c:=by
 simp [ql,List.range_succ]
lemma xg (w:ℕ->ℕ) {a b:ℕ} (h:a<=b):ql w a<=ql w b:=by
 induction h with
 | refl=>exact le_rfl
 | step _ ih=>rw [wf];omega
def zw (w:ℕ->ℕ) (t r:ℕ):Bool × ℕ × ℕ :=
 (List.range t).foldl
  (fun st c =>
   if st.1 then st
   else if st.2.2< w c then (true,c,st.2.2)
   else (false,c,st.2.2-w c))
  (false,0,r)
def yi (w:ℕ->ℕ) (K r:ℕ):ℕ × ℕ :=
 (zw w (K+1) r).2
lemma vu (w:ℕ->ℕ) (t r:ℕ) :
  let st:=zw w t r
  (r< ql w t->st.1=true/\st.2.1< t/\st.2.2< w st.2.1/\r=ql w st.2.1+st.2.2) /\
  (ql w t<=r->st.1=false/\st.2.2=r-ql w t):=by
 induction t with
 | zero =>
  simp [zw,ql]
 | succ t ih =>
  rcases ih with ⟨ih1,ih2⟩
  have hstep:zw w (t+1) r =
      let st:=zw w t r
      if st.1 then st
      else if st.2.2< w t then (true,t,st.2.2)
      else (false,t,st.2.2-w t):=by
    unfold zw;rw [List.range_succ,Zl];rfl
  rw [hstep,wf];set st:=zw w t r;constructor
  . intro hlt
    by_cases hprev:r< ql w t
    . rcases ih1 hprev with ⟨h1,h2,h3,h4⟩
      dsimp only;rw [h1];simp only [Zh];exact ⟨h1,by omega,h3,h4⟩
    . rcases ih2 (by omega) with ⟨h1,h2⟩
      dsimp only;rw [h1];simp only [Ze,Zj]
      have hlt':st.2.2< w t:=by omega
      rw [if_pos hlt'];dsimp only;exact ⟨rfl,by omega,hlt',by omega⟩
  . intro hge
    rcases ih2 (by omega) with ⟨h1,h2⟩
    dsimp only;rw [h1];simp only [Ze,Zj]
    have hnotlt:¬ (st.2.2< w t):=by omega
    rw [if_neg hnotlt];dsimp only;exact ⟨rfl,by omega⟩
lemma je (w:ℕ->ℕ) (K r:ℕ) (hr:r< ql w (K+1)) :
  let res:=yi w K r
  res.1<=K/\res.2< w res.1/\r=ql w res.1+res.2:=by
 rcases (vu w (K+1) r).1 hr with ⟨_,h1,h2,h3⟩
 dsimp only [yi];exact ⟨by omega,h2,h3⟩
lemma py (w:ℕ->ℕ) {c₁ c₂ r₁ r₂:ℕ}
   (h₁:r₁ < w c₁) (h₂:r₂ < w c₂)
   (heq:ql w c₁+r₁=ql w c₂+r₂) :
   c₁=c₂/\r₁=r₂:=by
 rcases lt_trichotomy c₁ c₂ with hlt | heqc | hgt
 . have hm:=xg w (show c₁+1<=c₂ by omega);rw [wf] at hm;omega
 . exact ⟨heqc,by rw [heqc] at heq;omega⟩
 . have hm:=xg w (show c₂+1<=c₁ by omega);rw [wf] at hm;omega
lemma j9 (w:ℕ->ℕ) (K c r':ℕ) (hc:c<=K) (hr':r'< w c) :
  ql w c+r'< ql w (K+1) /\
  yi w K (ql w c+r')=(c,r'):=by
 have hlt:ql w c+r'< ql w (K+1):=by
  have hm:=xg w (show c+1<=K+1 by omega);rw [wf] at hm;omega
 refine ⟨hlt,?_⟩
 rcases je w K (ql w c+r') hlt with ⟨_,h2,h3⟩
 rcases py w h2 hr' h3.symm with ⟨e1,e2⟩
 exact Prod.ext e1 e2
def yn (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ):ℕ :=
 ∑ j:Fin n,(2*j.1+1) *
  (oddC j false false+oddC j false true+oddC j true false+oddC j true true)
def zj (n:ℕ) (ep em:Fin n->ℕ):ℕ :=
 ∑ j:Fin n,2*(j.1+1)*(ep j+em j)
def jl (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ):ℕ :=
 ∑ j:Fin n,(oddC j false false+oddC j false true)
def j7 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ):ℕ :=
 ∑ j:Fin n,(oddC j true false+oddC j true true)
def jf (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ):ℕ :=
 ∑ j:Fin n,(oddC j false true+oddC j true true)
def wc (n:ℕ) (em:Fin n->ℕ):ℕ :=
 ∑ j:Fin n,em j
def wz (n:ℕ) (em:Fin n->ℕ):ℕ :=
 ∑ j:Fin n,em j*v2 (j.1+1)
def ju (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) (fus:ℕ):Prop :=
 (∀ j:Fin n,ep j=0\/em j=0) /\
 yn n oddC+zj n ep em=2*n /\
 jl n oddC=j7 n oddC /\
 (jf n oddC+wc n em)%2=0 /\
 fus<=wz n em
def xp (n:ℕ) :
  Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ)->Prop
 | none=>True
 | some (oddC,ep,em,fus)=>ju n oddC ep em fus
lemma x1 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) :
   xp n (zp n hn p):=by
 unfold zp
 split_ifs with h0
 . trivial
 . rcases xf n hn p (by omega) with ⟨_,hlen,_,hbal,hpar⟩
   rcases y2 n (z3 n hn p) (qo n hn p) (qd n hn p) (by omega) with
     ⟨_,hdisj,hlen',hpar',_,hphi,_⟩
   refine ⟨hdisj,?_,hbal,?_,?_⟩
   . unfold yn zj;omega
   . unfold jf wc;omega
   . unfold wz;omega
def qe (e:ℕ):ℕ:=2*(e+1)
def q7 (n e:ℕ):ℕ:=(2*n)/qe e
def qw (M cid:ℕ):ℕ :=
 if cid=0 then 0 else if cid<=M then cid else cid-M
def z5 (M cid:ℕ):Bool:=decide (M< cid)
def qy (M ep em:ℕ):ℕ :=
 if 0< em then M+em else ep
lemma ja (M ep em:ℕ) (hd:ep=0\/em=0) (hle:ep+em<=M) :
  qy M ep em<=2*M /\
  qw M (qy M ep em)=ep+em /\
  (if z5 M (qy M ep em) then 0 else qw M (qy M ep em))=ep /\
  (if z5 M (qy M ep em) then qw M (qy M ep em) else 0)=em:=by
 unfold qy qw z5
 rcases hd with rfl | rfl <;> split_ifs <;> simp_all <;> omega
lemma jv (M cid:ℕ) (hc:cid<=2*M) :
  let cnt:=qw M cid
  let isNeg:=z5 M cid
  let ep:=if isNeg then 0 else cnt
  let em:=if isNeg then cnt else 0
  (ep=0\/em=0)/\ep+em=cnt/\cnt<=M/\qy M ep em=cid:=by
 dsimp only;unfold qw z5 qy
 split_ifs <;> simp_all <;> omega
def qx (n rem len allow:ℕ) (par:Bool) (next:ℕ->ℕ->Bool->ℕ) (cid:ℕ):ℕ :=
 let e:=n-(rem+1)
 let L:=qe e
 let M:=q7 n e
 let cnt:=qw M cid
 let isNeg:=z5 M cid
 let dlen:=cnt*L
 let dallow:=if isNeg then cnt*v2 (e+1) else 0
 let dpar:=isNeg&&decide (cnt %2=1)
 if len+dlen<=2*n then next (len+dlen) (allow+dallow) (xor par dpar) else 0
def qi (n:ℕ):ℕ->ℕ->ℕ->Bool->ℕ
 | 0,len,allow,par=>if len=2*n/\par=false then allow+1 else 0
 | rem+1,len,allow,par =>
  let M:=q7 n (n-(rem+1))
  ql (qx n rem len allow par (qi n rem)) (2*M+1)
def za (n:ℕ) (ep em:Fin n->ℕ) (fus:ℕ):ℕ->ℕ->ℕ->Bool->ℕ
 | 0,_,_,_=>fus
 | rem+1,len,allow,par =>
  let e:=n-(rem+1)
  if he:e< n then
   let M:=q7 n e
   let cid:=qy M (ep ⟨e,he⟩) (em ⟨e,he⟩)
   let cnt:=qw M cid
   let isNeg:=z5 M cid
   let dlen:=cnt*qe e
   let dallow:=if isNeg then cnt*v2 (e+1) else 0
   let dpar:=isNeg&&decide (cnt %2=1)
   ql (qx n rem len allow par (qi n rem)) cid +
    za n ep em fus rem (len+dlen) (allow+dallow) (xor par dpar)
  else 0
def ze (n:ℕ) :
  ℕ->ℕ->ℕ->Bool->ℕ->(Fin n->ℕ) × (Fin n->ℕ) × ℕ
 | 0,_,_,_,r=>(fun _=>0,fun _=>0,r)
 | rem+1,len,allow,par,r =>
  let e:=n-(rem+1)
  let M:=q7 n e
  let ch:=yi (qx n rem len allow par (qi n rem)) (2*M) r
  let cid:=ch.1
  let r':=ch.2
  let cnt:=qw M cid
  let isNeg:=z5 M cid
  let epVal:=if isNeg then 0 else cnt
  let emVal:=if isNeg then cnt else 0
  let dlen:=cnt*qe e
  let dallow:=if isNeg then cnt*v2 (e+1) else 0
  let dpar:=isNeg&&decide (cnt %2=1)
  let tail:=ze n rem (len+dlen) (allow+dallow) (xor par dpar) r'
  (fun j=>if j.1=e then epVal else tail.1 j,
   fun j=>if j.1=e then emVal else tail.2.1 j,
   tail.2.2)
lemma vv (n e:ℕ) (he:e< n) (F:Fin n->ℕ) :
   (∑ j:Fin n,if e<=j.1 then F j else 0) =
   F ⟨e,he⟩+(∑ j:Fin n,if e+1<=j.1 then F j else 0):=by
 rw [<- Finset.add_sum_erase Finset.univ (fun j:Fin n=>if e<=j.1 then F j else 0) (Zu ⟨e,he⟩),
    <- Finset.add_sum_erase Finset.univ (fun j:Fin n=>if e+1<=j.1 then F j else 0) (Zu ⟨e,he⟩)]
 simp only [le_refl,Zh,show ¬ (e+1<=e) by omega,Zj,Nat.zero_add];congr 1;apply Zc rfl;intro j hj;rw [Finset.mem_erase] at hj
 have hne:j.1≠e:=fun h=>hj.1 (Zx h)
 by_cases hle:e<=j.1
 . simp [hle,show e+1<=j.1 by omega]
 . simp [hle,show ¬ (e+1<=j.1) by omega]
lemma x4 (par:Bool) (a b:ℕ) :
  xor (xor par (decide (a %2=1))) (decide (b %2=1)) =
  xor par (decide ((a+b)%2=1)):=by
 cases par <;> rcases (show a %2=0\/a %2=1 by omega) with ha | ha <;>
  rcases (show b %2=0\/b %2=1 by omega) with hb | hb <;>
  simp [ha,hb,show (a+b)%2=(a %2+b %2)%2 from Nat.add_mod a b 2]
lemma bc (n:ℕ) (ep em:Fin n->ℕ) (fus:ℕ) :
  ∀ rem ≤ n,∀ (len allow:ℕ) (par:Bool),
    (∀ j:Fin n,n-rem<=j.1->ep j=0\/em j=0) ->
    len+(∑ j:Fin n,if n-rem<=j.1 then 2*(j.1+1)*(ep j+em j) else 0)=2*n ->
    xor par (decide ((∑ j:Fin n,if n-rem<=j.1 then em j else 0)%2=1))=false ->
    fus<=allow+(∑ j:Fin n,if n-rem<=j.1 then em j*v2 (j.1+1) else 0) ->
    za n ep em fus rem len allow par< qi n rem len allow par /\
    let u:=ze n rem len allow par (za n ep em fus rem len allow par)
    (∀ j:Fin n,n-rem<=j.1->u.1 j=ep j/\u.2.1 j=em j)/\u.2.2=fus:=by
 intro rem
 induction rem with
 | zero =>
  intro _ len allow par _ hlen hpar hfus
  have h0:∀ F:Fin n->ℕ,(∑ j:Fin n,if n-0<=j.1 then F j else 0)=0:=by
    intro F;apply Finset.sum_eq_zero;intro j _;have:=j.isLt;simp [show ¬ (n-0<=j.1) by omega]
  rw [h0] at hlen hpar hfus;simp only [Zq,Nat.zero_mod,zero_ne_one,decide_false,Bool.xor_false] at hlen hpar hfus;simp only [za,qi,hlen,hpar,and_self,Zh,ze];exact ⟨by omega,fun j hj=>by have:=j.isLt;omega,trivial⟩
 | succ rem ih =>
  intro hrem len allow par hdisj hlen hpar hfus;set e:=n-(rem+1)
  have he:e< n:=by omega
  have he1:n-rem=e+1:=by omega
  rw [vv n e he] at hlen hpar hfus;dsimp only at hlen hpar hfus
  have hcnt_le_M:ep ⟨e,he⟩+em ⟨e,he⟩<=q7 n e:=by
    unfold q7 qe
    have hterm_le:2*(e+1)*(ep ⟨e,he⟩+em ⟨e,he⟩)<=2*n:=by omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  rcases ja (q7 n e) (ep ⟨e,he⟩) (em ⟨e,he⟩)
    (hdisj ⟨e,he⟩ le_rfl) hcnt_le_M with ⟨hcid_le,hcnt_eq,hep_eq,hem_eq⟩
  set cid:=qy (q7 n e) (ep ⟨e,he⟩) (em ⟨e,he⟩);set cnt:=qw (q7 n e) cid;set isNeg:=z5 (q7 n e) cid;set dlen:=cnt*qe e
  set dallow:=if isNeg then cnt*v2 (e+1) else 0
  set dpar:=isNeg&&decide (cnt %2=1)
  have hdlen_eq:dlen=2*(e+1)*(ep ⟨e,he⟩+em ⟨e,he⟩):=by
    dsimp only [dlen,qe];rw [hcnt_eq];ring
  have hdallow_eq:dallow=em ⟨e,he⟩*v2 (e+1):=by
    dsimp only [dallow]
    by_cases hn:isNeg=true
    . simp only [hn,Zh] at hem_eq ⊢;rw [hem_eq]
    . simp only [hn,Zj] at hem_eq ⊢;rw [<- hem_eq];simp
  have hdpar_eq:dpar=decide (em ⟨e,he⟩ % 2=1):=by
    dsimp only [dpar]
    by_cases hn:isNeg=true
    . simp only [hn,Zh,Bool.true_and] at hem_eq ⊢;rw [hem_eq]
    . simp only [hn,Zj,Bool.false_and] at hem_eq ⊢;rw [<- hem_eq];rfl
  have hlen_le:len+dlen<=2*n:=by omega
  rcases ih (by omega) (len+dlen) (allow+dallow) (xor par dpar)
    (fun j hj=>hdisj j (by omega))
    (by rw [he1];omega)
    (by rw [he1,hdpar_eq,x4];exact hpar)
    (by rw [he1];omega) with ⟨hih_lt,hih_u,hih_f⟩
  have hw_eq:qx n rem len allow par (qi n rem) cid =
      qi n rem (len+dlen) (allow+dallow) (xor par dpar):=by
    change (if len+dlen<=2*n then qi n rem (len+dlen) (allow+dallow) (xor par dpar) else 0)=_;rw [if_pos hlen_le]
  have hrank_eq:za n ep em fus (rem+1) len allow par =
      ql (qx n rem len allow par (qi n rem)) cid +
        za n ep em fus rem (len+dlen) (allow+dallow) (xor par dpar):=by
    simp only [za,show n-(rem+1)< n from he,Zd];rfl
  rcases j9 (qx n rem len allow par (qi n rem))
    (2*q7 n e) cid (za n ep em fus rem (len+dlen) (allow+dallow) (xor par dpar))
    hcid_le (by rw [hw_eq];exact hih_lt) with ⟨hsum_lt,hfind⟩
  refine ⟨?_,?_,?_⟩
  . rw [hrank_eq];exact hsum_lt
  . intro j hj;dsimp only [ze];rw [hrank_eq,hfind]
    change (if j.1=e then (if isNeg then 0 else cnt) else (ze n rem (len+dlen) (allow+dallow) (xor par dpar) _).1 j)=ep j /\
      (if j.1=e then (if isNeg then cnt else 0) else (ze n rem (len+dlen) (allow+dallow) (xor par dpar) _).2.1 j)=em j
    by_cases hje:j.1=e
    . rw [if_pos hje,if_pos hje];have hj_eq:j=⟨e,he⟩:=Zx hje;rw [hj_eq];exact ⟨hep_eq,hem_eq⟩
    . rw [if_neg hje,if_neg hje];exact hih_u j (by omega)
  . dsimp only [ze];rw [hrank_eq,hfind];exact hih_f
lemma po (n:ℕ) :
  ∀ rem ≤ n,∀ (len allow:ℕ) (par:Bool) (r:ℕ),
    r< qi n rem len allow par ->
    let u:=ze n rem len allow par r
    (∀ j:Fin n,j.1< n-rem->u.1 j=0/\u.2.1 j=0) /\
    (∀ j:Fin n,u.1 j=0\/u.2.1 j=0) /\
    len+(∑ j:Fin n,if n-rem<=j.1 then 2*(j.1+1)*(u.1 j+u.2.1 j) else 0)=2*n /\
    xor par (decide ((∑ j:Fin n,if n-rem<=j.1 then u.2.1 j else 0)%2=1))=false /\
    u.2.2<=allow+(∑ j:Fin n,if n-rem<=j.1 then u.2.1 j*v2 (j.1+1) else 0) /\
    za n u.1 u.2.1 u.2.2 rem len allow par=r:=by
 intro rem
 induction rem with
 | zero =>
  intro _ len allow par r hr;simp only [qi] at hr
  split_ifs at hr with hok
  . have h0:∀ F:Fin n->ℕ,(∑ j:Fin n,if n-0<=j.1 then F j else 0)=0:=by
      intro F;apply Finset.sum_eq_zero;intro j _;have:=j.isLt;simp [show ¬ (n-0<=j.1) by omega]
    simp only [ze,za,h0,Zq,Nat.zero_mod,zero_ne_one,
      decide_false,Bool.xor_false]
    exact ⟨fun _ _=>⟨trivial,trivial⟩,fun _=>Or.inl trivial,hok.1,hok.2,by omega,trivial⟩
  . omega
 | succ rem ih =>
  intro hrem len allow par r hr;set e:=n-(rem+1)
  have he:e< n:=by omega
  have he1:n-rem=e+1:=by omega
  simp only [qi] at hr;set M:=q7 n e
  rcases je (qx n rem len allow par (qi n rem)) (2*M) r hr with
    ⟨hcid_le,hr'_lt,hr_eq⟩
  set ch:=yi (qx n rem len allow par (qi n rem)) (2*M) r;set cid:=ch.1;set r':=ch.2;set cnt:=qw M cid;set isNeg:=z5 M cid
  set epVal:=if isNeg then 0 else cnt
  set emVal:=if isNeg then cnt else 0
  set dlen:=cnt*qe e
  set dallow:=if isNeg then cnt*v2 (e+1) else 0
  set dpar:=isNeg&&decide (cnt %2=1)
  have hstep_w:qx n rem len allow par (qi n rem) cid =
      if len+dlen<=2*n then qi n rem (len+dlen) (allow+dallow) (xor par dpar) else 0:=rfl
  rw [hstep_w] at hr'_lt
  have hlen_le:len+dlen<=2*n:=by
    by_contra hnot
    rw [if_neg hnot] at hr'_lt;omega
  have hr'_lt':r'< qi n rem (len+dlen) (allow+dallow) (xor par dpar):=by
    rwa [if_pos hlen_le] at hr'_lt
  rcases ih (by omega) (len+dlen) (allow+dallow) (xor par dpar) r' hr'_lt' with
    ⟨ih_zero,ih_disj,ih_len,ih_par,ih_fus,ih_rank⟩
  rcases jv M cid hcid_le with ⟨hval_disj,hval_sum,_,hval_cid⟩
  set tail:=ze n rem (len+dlen) (allow+dallow) (xor par dpar) r'
  set u1:Fin n->ℕ:=fun j=>if j.1=e then epVal else tail.1 j
  set u2:Fin n->ℕ:=fun j=>if j.1=e then emVal else tail.2.1 j
  have hu_ge:∀ F:ℕ->ℕ->Fin n->ℕ,
      (∑ j:Fin n,if e+1<=j.1 then F (u1 j) (u2 j) j else 0) =
      (∑ j:Fin n,if e+1<=j.1 then F (tail.1 j) (tail.2.1 j) j else 0):=by
    intro F;apply Zc rfl;intro j _
    by_cases h1:e+1<=j.1
    . simp [h1,u1,u2,show j.1≠e by omega]
    . simp [h1]
  have hrank_congr:∀ k ≤ n,∀ a b c (ep₁ em₁ ep₂ em₂:Fin n->ℕ) f,
      (∀ j:Fin n,n-k<=j.1->ep₁ j=ep₂ j/\em₁ j=em₂ j) ->
      za n ep₁ em₁ f k a b c=za n ep₂ em₂ f k a b c:=by
    intro k;induction k with
    | zero=>intro _ _ _ _ _ _ _ _ _ _;rfl
    | succ k ihk =>
      intro hk a b c ep₁ em₁ ep₂ em₂ f hsame;simp only [za,show n-(k+1)< n by omega,Zd]
      rcases hsame ⟨n-(k+1),by omega⟩ le_rfl with ⟨e1,e2⟩
      rw [e1,e2,ihk (by omega) _ _ _ _ _ _ _ _ (fun j hj=>hsame j (by omega))]
  have hdlen_eq:dlen=2*(e+1)*(epVal+emVal):=by
    dsimp only [dlen,qe];rw [hval_sum];ring
  have hdallow_eq:dallow=emVal*v2 (e+1):=by
    dsimp only [dallow,emVal];cases isNeg <;> simp
  have hdpar_eq:dpar=decide (emVal %2=1):=by
    dsimp only [dpar,emVal];by_cases h:isNeg=true <;> simp [h]
  change (∀ j:Fin n,j.1< e->u1 j=0/\u2 j=0) /\
    (∀ j:Fin n,u1 j=0\/u2 j=0) /\
    len+(∑ j:Fin n,if e<=j.1 then 2*(j.1+1)*(u1 j+u2 j) else 0)=2*n /\
    xor par (decide ((∑ j:Fin n,if e<=j.1 then u2 j else 0)%2=1))=false /\
    tail.2.2<=allow+(∑ j:Fin n,if e<=j.1 then u2 j*v2 (j.1+1) else 0) /\
    za n u1 u2 tail.2.2 (rem+1) len allow par=r
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  . intro j hj;simp only [u1,u2,show j.1≠e by omega,Zj];exact ih_zero j (by omega)
  . intro j
    by_cases hje:j.1=e
    . simp only [u1,u2,hje,Zh];exact hval_disj
    . simp only [u1,u2,hje,Zj];exact ih_disj j
  . rw [vv n e he,hu_ge (fun a b j=>2*(j.1+1)*(a+b))];simp only [u1,u2,Zh];rw [he1] at ih_len;omega
  . rw [vv n e he,hu_ge (fun _ b _=>b)];simp only [u2,Zh];rw [<- x4,<-hdpar_eq];rw [he1] at ih_par;exact ih_par
  . rw [vv n e he,hu_ge (fun _ b j=>b*v2 (j.1+1))];simp only [u2,Zh];rw [he1] at ih_fus;omega
  . simp only [za,show n-(rem+1)< n from he,Zd]
    have hu1e:u1 ⟨n-(rem+1),he⟩=epVal:=by simp [u1,e]
    have hu2e:u2 ⟨n-(rem+1),he⟩=emVal:=by simp [u2,e]
    rw [hu1e,hu2e]
    change ql (qx n rem len allow par (qi n rem)) (qy M epVal emVal) +
       za n u1 u2 tail.2.2 rem (len+qw M (qy M epVal emVal)*qe e)
        (allow+if z5 M (qy M epVal emVal)=true then qw M (qy M epVal emVal)*v2 (e+1) else 0)
        (xor par (z5 M (qy M epVal emVal)&&decide (qw M (qy M epVal emVal)%2=1)))=r
    rw [hval_cid]
    rw [hrank_congr rem (by omega) _ _ _ u1 u2 tail.1 tail.2.1 tail.2.2
        (fun j hj=>by simp [u1,u2,show j.1≠e by omega])]
    rw [ih_rank];exact hr_eq.symm
def q6 (n:ℕ) (j:Fin n) (c sig:Bool):ℕ :=
 (if c then 2*n else 0)+2*j.1+sig.toNat
def zf (n o:ℕ):ℕ:=if o< 2*n then o/2 else (o-2*n)/2
def qh (n o:ℕ):Bool:=decide (2*n<=o)
def qf (o:ℕ):Bool:=decide (o %2=1)
def qs (n o:ℕ):ℕ:=2*zf n o+1
def qv (n o:ℕ):ℕ:=(2*n)/qs n o
lemma qp (n o:ℕ) (ho:o< 4*n) :
   zf n o< n /\
   q6 n ⟨zf n o,by unfold zf;split_ifs <;> omega⟩ (qh n o) (qf o)=o:=by
 unfold zf qh qf q6
 by_cases h:o< 2*n
 . refine ⟨by simp [h];omega,?_⟩
   simp only [h,Zh,show ¬ (2*n<=o) by omega,decide_false,Zj,Nat.zero_add]
   rcases (show o %2=0\/o %2=1 by omega) with hm | hm <;> simp [hm] <;> omega
 . refine ⟨by simp [h];omega,?_⟩
   simp only [h,Zj,show 2*n<=o by omega,decide_true,Zh]
   rcases (show o %2=0\/o %2=1 by omega) with hm | hm <;> simp [hm] <;> omega
lemma jg (n:ℕ) (j₁ j₂:Fin n) (c₁ c₂ sig₁ sig₂:Bool)
  (h:q6 n j₁ c₁ sig₁=q6 n j₂ c₂ sig₂) :
  j₁=j₂/\c₁=c₂/\sig₁=sig₂:=by
 unfold q6 at h;have h1:=j₁.isLt;have h2:=j₂.isLt
 cases c₁ <;> cases c₂ <;> cases sig₁ <;> cases sig₂ <;> simp at h
 all_goals first | omega | (exact ⟨Zx (by omega),rfl,rfl⟩)
lemma yw (n:ℕ) (j:Fin n) (c sig:Bool):q6 n j c sig< 4*n:=by
 unfold q6;have:=j.isLt;cases c <;> cases sig <;> simp <;> omega
def qj (n o:ℕ) (F:Fin n->Bool->Bool->ℕ):ℕ :=
 ∑ j:Fin n,
  ((if o<=q6 n j false false then F j false false else 0) +
   (if o<=q6 n j false true then F j false true else 0) +
   (if o<=q6 n j true false then F j true false else 0) +
   (if o<=q6 n j true true then F j true true else 0))
lemma wv (n:ℕ) (F:Fin n->Bool->Bool->ℕ) :
  qj n 0 F=∑ j:Fin n,(F j false false+F j false true+F j true false+F j true true):=by
 unfold qj;simp
lemma jw (n:ℕ) (F:Fin n->Bool->Bool->ℕ) :
  qj n (4*n) F=0:=by
 unfold qj;apply Finset.sum_eq_zero;intro j _;have h1:=yw n j false false;have h2:=yw n j false true;have h3:=yw n j true false;have h4:=yw n j true true
 simp [show ¬ (4*n<=q6 n j false false) by omega,
   show ¬ (4*n<=q6 n j false true) by omega,
   show ¬ (4*n<=q6 n j true false) by omega,
   show ¬ (4*n<=q6 n j true true) by omega]
lemma w6 (n o:ℕ) (ho:o< 4*n) (F:Fin n->Bool->Bool->ℕ) :
  qj n o F =
  F ⟨zf n o,(qp n o ho).1⟩ (qh n o) (qf o) +
  qj n (o+1) F:=by
 set j0:Fin n:=⟨zf n o,(qp n o ho).1⟩
 set c0:=qh n o;set s0:=qf o;have hidx0:q6 n j0 c0 s0=o:=(qp n o ho).2;unfold qj
 rw [<- Finset.add_sum_erase Finset.univ _ (Zu j0),
    <- Finset.add_sum_erase Finset.univ (fun j:Fin n =>
      (if o+1<=q6 n j false false then F j false false else 0) +
      (if o+1<=q6 n j false true then F j false true else 0) +
      (if o+1<=q6 n j true false then F j true false else 0) +
      (if o+1<=q6 n j true true then F j true true else 0)) (Zu j0)]
 have hrest:∀ j ∈ Finset.univ.erase j0,
    ((if o<=q6 n j false false then F j false false else 0) +
     (if o<=q6 n j false true then F j false true else 0) +
     (if o<=q6 n j true false then F j true false else 0) +
     (if o<=q6 n j true true then F j true true else 0)) =
    ((if o+1<=q6 n j false false then F j false false else 0) +
     (if o+1<=q6 n j false true then F j false true else 0) +
     (if o+1<=q6 n j true false then F j true false else 0) +
     (if o+1<=q6 n j true true then F j true true else 0)):=by
  intro j hj;rw [Finset.mem_erase] at hj
  have hne (c s:Bool):q6 n j c s≠o:=by
    intro heq;rw [<- hidx0] at heq;exact hj.1 (jg n j j0 c c0 s s0 heq).1
  have h1:=hne false false;have h2:=hne false true;have h3:=hne true false;have h4:=hne true true
  have hiff (k:ℕ) (hk:k≠o):(if o<=k then (1:ℕ) else 0)=(if o+1<=k then 1 else 0):=by
    split_ifs <;> omega
  congr 1;congr 1;congr 1
  . by_cases h:o<=q6 n j false false <;> simp [h,show o+1<=q6 n j false false ↔ o<=q6 n j false false by omega]
  . by_cases h:o<=q6 n j false true <;> simp [h,show o+1<=q6 n j false true ↔ o<=q6 n j false true by omega]
  . by_cases h:o<=q6 n j true false <;> simp [h,show o+1<=q6 n j true false ↔ o<=q6 n j true false by omega]
  . by_cases h:o<=q6 n j true true <;> simp [h,show o+1<=q6 n j true true ↔ o<=q6 n j true true by omega]
 rw [Zc rfl hrest]
 have hne_same (c s:Bool) (hcs:c≠c0\/s≠s0):q6 n j0 c s≠o:=by
  intro heq;rw [<- hidx0] at heq
  rcases jg n j0 j0 c c0 s s0 heq with ⟨_,ec,es⟩
  rcases hcs with h | h
  . exact h ec
  . exact h es
 have hterm (c s:Bool) :
    (if o<=q6 n j0 c s then F j0 c s else 0) =
    (if c=c0/\s=s0 then F j0 c0 s0 else 0) +
    (if o+1<=q6 n j0 c s then F j0 c s else 0):=by
  by_cases hcs:c=c0/\s=s0
  . rcases hcs with ⟨rfl,rfl⟩
    simp [hidx0]
  . have hne:q6 n j0 c s≠o:=hne_same c s (by tauto);simp only [hcs,Zj,Nat.zero_add]
    by_cases h:o<=q6 n j0 c s <;>
      simp [h,show o+1<=q6 n j0 c s ↔ o<=q6 n j0 c s by omega]
 rw [hterm false false,hterm false true,hterm true false,hterm true true]
 cases c0 <;> cases s0 <;> simp <;> omega
def zc (n rem len bal:ℕ) (par:Bool) (next:ℕ->ℕ->Bool->ℕ) (cnt:ℕ):ℕ :=
 let o:=4*n-(rem+1)
 let L:=qs n o
 let c:=qh n o
 let sig:=qf o
 let dlen:=cnt*L
 let dpar:=sig&&decide (cnt %2=1)
 if c=false then
  if len+dlen<=2*n/\bal+cnt<=n then next (len+dlen) (bal+cnt) (xor par dpar) else 0
 else
  if len+dlen<=2*n/\cnt<=bal then next (len+dlen) (bal-cnt) (xor par dpar) else 0
def qk (n:ℕ):ℕ->ℕ->ℕ->Bool->ℕ
 | 0,len,bal,par=>if bal=0 then qi n n len 0 par else 0
 | rem+1,len,bal,par =>
  let M:=qv n (4*n-(rem+1))
  ql (zc n rem len bal par (qk n rem)) (M+1)
def z1 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) (fus:ℕ) :
  ℕ->ℕ->ℕ->Bool->ℕ
 | 0,len,_,par=>za n ep em fus n len 0 par
 | rem+1,len,bal,par =>
  let o:=4*n-(rem+1)
  if ho:o< 4*n then
   let j:Fin n:=⟨zf n o,(qp n o ho).1⟩
   let c:=qh n o
   let sig:=qf o
   let cnt:=oddC j c sig
   let dlen:=cnt*qs n o
   let dpar:=sig&&decide (cnt %2=1)
   let bal':=if c=false then bal+cnt else bal-cnt
   ql (zc n rem len bal par (qk n rem)) cnt +
    z1 n oddC ep em fus rem (len+dlen) bal' (xor par dpar)
  else 0
def qq (n:ℕ) :
  ℕ->ℕ->ℕ->Bool->ℕ ->
  (Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ
 | 0,len,_,par,r =>
  let ev:=ze n n len 0 par r
  (fun _ _ _=>0,ev.1,ev.2.1,ev.2.2)
 | rem+1,len,bal,par,r =>
  let o:=4*n-(rem+1)
  let M:=qv n o
  let ch:=yi (zc n rem len bal par (qk n rem)) M r
  let cnt:=ch.1
  let r':=ch.2
  let c:=qh n o
  let sig:=qf o
  let dlen:=cnt*qs n o
  let dpar:=sig&&decide (cnt %2=1)
  let bal':=if c=false then bal+cnt else bal-cnt
  let tail:=qq n rem (len+dlen) bal' (xor par dpar) r'
  (fun j c' sig'=>if q6 n j c' sig'=o then cnt else tail.1 j c' sig',
   tail.2.1,tail.2.2.1,tail.2.2.2)
lemma bo (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) (fus:ℕ)
  (he_disj:∀ j:Fin n,ep j=0\/em j=0)
  (he_fus:fus<=wz n em) :
  ∀ rem ≤ 4*n,∀ (len bal:ℕ) (par:Bool),
    len+qj n (4*n-rem) (fun j c sig=>(2*j.1+1)*oddC j c sig)+zj n ep em=2*n ->
    bal+qj n (4*n-rem) (fun j c sig=>if c=false then oddC j c sig else 0) =
      qj n (4*n-rem) (fun j c sig=>if c=true then oddC j c sig else 0) ->
    qj n (4*n-rem) (fun j c sig=>if c=true then oddC j c sig else 0)<=n ->
    xor par (decide ((qj n (4*n-rem) (fun j c sig=>if sig=true then oddC j c sig else 0) +
      wc n em)%2=1))=false ->
    z1 n oddC ep em fus rem len bal par< qk n rem len bal par /\
    let u:=qq n rem len bal par (z1 n oddC ep em fus rem len bal par)
    (∀ j c sig,4*n-rem<=q6 n j c sig->u.1 j c sig=oddC j c sig) /\
    u.2.1=ep/\u.2.2.1=em/\u.2.2.2=fus:=by
 intro rem
 induction rem with
 | zero =>
  intro _ len bal par hlen hbal _ hpar;simp only [Nat.sub_zero,jw,Zq,Nat.zero_add] at hlen hbal hpar;subst hbal;simp only [z1,qk,Zh,qq]
  have hev:=bc n ep em fus n le_rfl len 0 par
    (fun j _=>he_disj j)
    (by simpa [zj] using hlen)
    (by simp only [Nat.sub_self,Nat.zero_le,Zh];exact hpar)
    (by simpa [wz] using he_fus)
  refine ⟨hev.1,fun j c sig hge=>by have:=yw n j c sig;omega,?_,?_,hev.2.2⟩
  . funext j;exact (hev.2.1 j (by omega)).1
  . funext j;exact (hev.2.1 j (by omega)).2
 | succ rem ih =>
  intro hrem len bal par hlen hbal hbal_le hpar;set o:=4*n-(rem+1)
  have ho:o< 4*n:=by omega
  have ho1:4*n-rem=o+1:=by omega
  set j0:Fin n:=⟨zf n o,(qp n o ho).1⟩
  set c0:=qh n o;set s0:=qf o;set cnt:=oddC j0 c0 s0;set dlen:=cnt*qs n o;set dpar:=s0&&decide (cnt %2=1)
  set bal':=if c0=false then bal+cnt else bal-cnt
  rw [w6 n o ho] at hlen hbal_le hpar;rw [w6 n o ho,w6 n o ho] at hbal
  have hdlen_eq:dlen=(2*j0.1+1)*cnt:=by
    dsimp only [dlen,qs,j0];ring
  have hcnt_le_M:cnt<=qv n o:=by
    unfold qv qs;exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by dsimp [j0] at hdlen_eq;nlinarith)
  have hlen_le:len+dlen<=2*n:=by
    change len+((2*j0.1+1)*cnt+_)+zj n ep em=2*n at hlen;omega
  have hbal_step :
      (c0=false->bal+cnt<=n) /\
      (c0=true->cnt<=bal) /\
      bal'+qj n (o+1) (fun j c sig=>if c=false then oddC j c sig else 0) =
        qj n (o+1) (fun j c sig=>if c=true then oddC j c sig else 0) /\
      qj n (o+1) (fun j c sig=>if c=true then oddC j c sig else 0)<=n:=by
    change bal+((if c0=false then cnt else 0)+_)=(if c0=true then cnt else 0)+_ at hbal;change (if c0=true then cnt else 0)+_<=n at hbal_le
    cases hc:c0
    . rw [hc] at hbal hbal_le;simp only [Zh,Ze,Zj,Nat.zero_add] at hbal hbal_le
      refine ⟨fun _=>by omega,(fun h=>by cases h),?_,by omega⟩
      dsimp only [bal'];rw [hc];simp only [Zh];omega
    . rw [hc] at hbal hbal_le;simp only [Zh,Bool.true_eq_false,Zj,Nat.zero_add] at hbal hbal_le
      have hrem0:qj n (o+1) (fun j c sig=>if c=false then oddC j c sig else 0)=0:=by
        unfold qj;apply Finset.sum_eq_zero;intro j _
        have hge2n:2*n<=o:=by
         unfold c0 qh at hc;exact of_decide_eq_true hc
        have hlt1:q6 n j false false< 2*n:=by unfold q6;have:=j.isLt;simp
        have hlt2:q6 n j false true< 2*n:=by unfold q6;have:=j.isLt;simp;omega
        simp [show ¬ (o+1<=q6 n j false false) by omega,
          show ¬ (o+1<=q6 n j false true) by omega]
      rw [hrem0,Zq] at hbal
      refine ⟨(fun h=>by cases h),fun _=>by omega,?_,by omega⟩
      dsimp only [bal'];rw [hc,hrem0];simp only [Bool.true_eq_false,Zj,Zq];omega
  have hpar_step:xor (xor par dpar)
      (decide ((qj n (o+1) (fun j c sig=>if sig=true then oddC j c sig else 0) +
        wc n em)%2=1))=false:=by
    change xor par (decide ((((if s0=true then cnt else 0)+_)+wc n em)%2=1))=false at hpar
    cases hs:s0
    . rw [hs] at hpar;simp only [dpar,hs,Bool.false_and,Bool.xor_false,Ze,Zj,Nat.zero_add] at hpar ⊢;exact hpar
    . rw [hs] at hpar;simp only [dpar,hs,Bool.true_and,Zh] at hpar ⊢;rw [x4,<-Nat.add_assoc];exact hpar
  rcases ih (by omega) (len+dlen) bal' (xor par dpar)
    (by rw [ho1];change len+((2*j0.1+1)*cnt+_)+zj n ep em=2*n at hlen;omega)
    (by rw [ho1];exact hbal_step.2.2.1)
    (by rw [ho1];exact hbal_step.2.2.2)
    (by rw [ho1];exact hpar_step) with ⟨hih_lt,hih_u,hih_ep,hih_em,hih_f⟩
  have hw_eq:zc n rem len bal par (qk n rem) cnt =
      qk n rem (len+dlen) bal' (xor par dpar):=by
    change (if c0=false then
        if len+dlen<=2*n/\bal+cnt<=n then qk n rem (len+dlen) (bal+cnt) (xor par dpar) else 0
      else
        if len+dlen<=2*n/\cnt<=bal then qk n rem (len+dlen) (bal-cnt) (xor par dpar) else 0)=_
    cases hc:c0
    . have hb:=hbal_step.1 hc;dsimp only [bal'];rw [hc];simp only [Zh,hlen_le,hb,and_self]
    . have hb:=hbal_step.2.1 hc;dsimp only [bal'];rw [hc];simp only [Bool.true_eq_false,Zj,hlen_le,hb,and_self,Zh]
  have hrank_eq:z1 n oddC ep em fus (rem+1) len bal par =
      ql (zc n rem len bal par (qk n rem)) cnt +
        z1 n oddC ep em fus rem (len+dlen) bal' (xor par dpar):=by
    simp only [z1,show 4*n-(rem+1)< 4*n from ho,Zd];rfl
  rcases j9 (zc n rem len bal par (qk n rem))
    (qv n o) cnt (z1 n oddC ep em fus rem (len+dlen) bal' (xor par dpar))
    hcnt_le_M (by rw [hw_eq];exact hih_lt) with ⟨hsum_lt,hfind⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  . rw [hrank_eq];exact hsum_lt
  . intro j c sig hge;dsimp only [qq];rw [hrank_eq,hfind];change (if q6 n j c sig=o then cnt else (qq n rem (len+dlen) bal' (xor par dpar) _).1 j c sig)=_
    by_cases heq:q6 n j c sig=o
    . rw [if_pos heq];have hidx0:=(qp n o ho).2;rw [<- hidx0] at heq
      rcases jg n j j0 c c0 sig s0 heq with ⟨rfl,rfl,rfl⟩
      rfl
    . rw [if_neg heq];exact hih_u j c sig (by omega)
  . dsimp only [qq];rw [hrank_eq,hfind];exact hih_ep
  . dsimp only [qq];rw [hrank_eq,hfind];exact hih_em
  . dsimp only [qq];rw [hrank_eq,hfind];exact hih_f
lemma pz (n:ℕ) :
  ∀ rem ≤ 4*n,∀ (len bal:ℕ) (par:Bool) (r:ℕ),
    r< qk n rem len bal par ->
    let u:=qq n rem len bal par r
    (∀ j c sig,q6 n j c sig< 4*n-rem->u.1 j c sig=0) /\
    (∀ j:Fin n,u.2.1 j=0\/u.2.2.1 j=0) /\
    len+qj n (4*n-rem) (fun j c sig=>(2*j.1+1)*u.1 j c sig) +
      zj n u.2.1 u.2.2.1=2*n /\
    bal+qj n (4*n-rem) (fun j c sig=>if c=false then u.1 j c sig else 0) =
      qj n (4*n-rem) (fun j c sig=>if c=true then u.1 j c sig else 0) /\
    xor par (decide ((qj n (4*n-rem) (fun j c sig=>if sig=true then u.1 j c sig else 0) +
      wc n u.2.2.1)%2=1))=false /\
    u.2.2.2<=wz n u.2.2.1 /\
    z1 n u.1 u.2.1 u.2.2.1 u.2.2.2 rem len bal par=r:=by
 intro rem
 induction rem with
 | zero =>
  intro _ len bal par r hr;simp only [qk] at hr
  split_ifs at hr with hb0
  . subst hb0
    rcases po n n le_rfl len 0 par r hr with
      ⟨_,hdisj,hlen,hpar,hfus,hrank⟩
    simp only [qq,z1,Nat.sub_zero,jw,Zq,Nat.zero_add]
    refine ⟨fun _ _ _ _=>trivial,hdisj,?_,trivial,?_,?_,hrank⟩
    . simpa [zj] using hlen
    . simp only [Nat.sub_self,Nat.zero_le,Zh] at hpar;exact hpar
    . simpa [wz] using hfus
  . omega
 | succ rem ih =>
  intro hrem len bal par r hr;set o:=4*n-(rem+1)
  have ho:o< 4*n:=by omega
  have ho1:4*n-rem=o+1:=by omega
  simp only [qk] at hr;set M:=qv n o
  rcases je (zc n rem len bal par (qk n rem)) M r hr with
    ⟨hcnt_le,hr'_lt,hr_eq⟩
  set ch:=yi (zc n rem len bal par (qk n rem)) M r;set cnt:=ch.1;set r':=ch.2
  set j0:Fin n:=⟨zf n o,(qp n o ho).1⟩
  set c0:=qh n o;set s0:=qf o;set dlen:=cnt*qs n o;set dpar:=s0&&decide (cnt %2=1)
  set bal':=if c0=false then bal+cnt else bal-cnt
  have hvalid_step :
      len+dlen<=2*n/\(c0=false->bal+cnt<=n)/\(c0=true->cnt<=bal) /\
      r'< qk n rem (len+dlen) bal' (xor par dpar):=by
    have hw:zc n rem len bal par (qk n rem) cnt =
        if c0=false then
         if len+dlen<=2*n/\bal+cnt<=n then qk n rem (len+dlen) (bal+cnt) (xor par dpar) else 0
        else
         if len+dlen<=2*n/\cnt<=bal then qk n rem (len+dlen) (bal-cnt) (xor par dpar) else 0:=rfl
    rw [hw] at hr'_lt
    cases hc:c0
    . rw [hc] at hr'_lt;simp only [Zh] at hr'_lt
      split_ifs at hr'_lt with hok
      . refine ⟨hok.1,fun _=>hok.2,(fun h=>by cases h),?_⟩
        dsimp only [bal'];rw [hc];exact hr'_lt
      . omega
    . rw [hc] at hr'_lt;simp only [Bool.true_eq_false,Zj] at hr'_lt
      split_ifs at hr'_lt with hok
      . refine ⟨hok.1,(fun h=>by cases h),fun _=>hok.2,?_⟩
        dsimp only [bal'];rw [hc];exact hr'_lt
      . omega
  rcases ih (by omega) (len+dlen) bal' (xor par dpar) r' hvalid_step.2.2.2 with
    ⟨ih_zero,ih_disj,ih_len,ih_bal,ih_par,ih_fus,ih_rank⟩
  set tail:=qq n rem (len+dlen) bal' (xor par dpar) r'
  set uOdd:Fin n->Bool->Bool->ℕ :=
    fun j c' sig'=>if q6 n j c' sig'=o then cnt else tail.1 j c' sig'
  have hu_ge:∀ G:Fin n->Bool->Bool->ℕ->ℕ,
      qj n (o+1) (fun j c s=>G j c s (uOdd j c s)) =
      qj n (o+1) (fun j c s=>G j c s (tail.1 j c s)):=by
    intro G;unfold qj;apply Zc rfl;intro j _;congr 1;congr 1;congr 1
    . by_cases h:o+1<=q6 n j false false <;>
        simp [h,uOdd,show o+1<=q6 n j false false->q6 n j false false≠o by omega]
    . by_cases h:o+1<=q6 n j false true <;>
        simp [h,uOdd,show o+1<=q6 n j false true->q6 n j false true≠o by omega]
    . by_cases h:o+1<=q6 n j true false <;>
        simp [h,uOdd,show o+1<=q6 n j true false->q6 n j true false≠o by omega]
    . by_cases h:o+1<=q6 n j true true <;>
        simp [h,uOdd,show o+1<=q6 n j true true->q6 n j true true≠o by omega]
  have hrank_congr:∀ k ≤ 4*n,∀ a b c (o₁ o₂:Fin n->Bool->Bool->ℕ) ep em f,
      (∀ j c' s',4*n-k<=q6 n j c' s'->o₁ j c' s'=o₂ j c' s') ->
      z1 n o₁ ep em f k a b c=z1 n o₂ ep em f k a b c:=by
    intro k;induction k with
    | zero=>intro _ _ _ _ _ _ _ _ _ _;rfl
    | succ k ihk =>
      intro hk a b c o₁ o₂ ep em f hsame
      have hlt:4*n-(k+1)< 4*n:=by omega
      simp only [z1,hlt,Zd]
      have heq:=hsame ⟨zf n (4*n-(k+1)),(qp n _ hlt).1⟩
        (qh n (4*n-(k+1))) (qf (4*n-(k+1)))
        (by rw [(qp n _ hlt).2])
      rw [heq,ihk (by omega) _ _ _ _ _ _ _ _ (fun j c' s' h=>hsame j c' s' (by omega))]
  have hidx0:q6 n j0 c0 s0=o:=(qp n o ho).2
  have hu_at0:uOdd j0 c0 s0=cnt:=by simp [uOdd,hidx0]
  have hdlen_eq:dlen=(2*j0.1+1)*cnt:=by dsimp [dlen,qs,j0];ring
  change (∀ j c sig,q6 n j c sig< o->uOdd j c sig=0) /\
    (∀ j:Fin n,tail.2.1 j=0\/tail.2.2.1 j=0) /\
    len+qj n o (fun j c sig=>(2*j.1+1)*uOdd j c sig)+zj n tail.2.1 tail.2.2.1=2*n /\
    bal+qj n o (fun j c sig=>if c=false then uOdd j c sig else 0) =
      qj n o (fun j c sig=>if c=true then uOdd j c sig else 0) /\
    xor par (decide ((qj n o (fun j c sig=>if sig=true then uOdd j c sig else 0) +
      wc n tail.2.2.1)%2=1))=false /\
    tail.2.2.2<=wz n tail.2.2.1 /\
    z1 n uOdd tail.2.1 tail.2.2.1 tail.2.2.2 (rem+1) len bal par=r
  refine ⟨?_,ih_disj,?_,?_,?_,ih_fus,?_⟩
  . intro j c sig hlt;simp only [uOdd,show q6 n j c sig≠o by omega,Zj];exact ih_zero j c sig (by omega)
  . rw [w6 n o ho,hu_ge (fun j _ _ v=>(2*j.1+1)*v)];change len+((2*j0.1+1)*uOdd j0 c0 s0+_)+_=_;rw [hu_at0];rw [ho1] at ih_len;omega
  . rw [w6 n o ho,w6 n o ho,
        hu_ge (fun _ c _ v=>if c=false then v else 0),
        hu_ge (fun _ c _ v=>if c=true then v else 0)]
    change bal+((if c0=false then uOdd j0 c0 s0 else 0)+_)=(if c0=true then uOdd j0 c0 s0 else 0)+_;rw [hu_at0];rw [ho1] at ih_bal
    cases hc:c0
    . dsimp only [bal'] at ih_bal;rw [hc] at ih_bal;simp only [Zh,Ze,Zj,Nat.zero_add] at ih_bal ⊢;omega
    . have hle:=hvalid_step.2.2.1 hc;dsimp only [bal'] at ih_bal;rw [hc] at ih_bal;simp only [Zh,Bool.true_eq_false,Zj,Nat.zero_add] at ih_bal ⊢;omega
  . rw [w6 n o ho,hu_ge (fun _ _ s v=>if s=true then v else 0)];change xor par (decide ((((if s0=true then uOdd j0 c0 s0 else 0)+_)+wc n tail.2.2.1)%2=1))=false;rw [hu_at0];rw [ho1] at ih_par
    cases hs:s0
    . dsimp only [dpar] at ih_par;rw [hs] at ih_par;simp only [Bool.false_and,Bool.xor_false,Ze,Zj,Nat.zero_add] at ih_par ⊢;exact ih_par
    . dsimp only [dpar] at ih_par;rw [hs] at ih_par;simp only [Bool.true_and,Zh] at ih_par ⊢;rw [Nat.add_assoc,<-x4];exact ih_par
  . unfold z1
    change (if h:o< 4*n then
        ql (zc n rem len bal par (qk n rem)) (uOdd ⟨zf n o,(qp n o h).1⟩ c0 s0) +
        z1 n uOdd tail.2.1 tail.2.2.1 tail.2.2.2 rem
         (len+uOdd ⟨zf n o,(qp n o h).1⟩ c0 s0*qs n o)
         (if c0=false then bal+uOdd ⟨zf n o,(qp n o h).1⟩ c0 s0 else bal-uOdd ⟨zf n o,(qp n o h).1⟩ c0 s0)
         (xor par (s0&&decide (uOdd ⟨zf n o,(qp n o h).1⟩ c0 s0 %2=1)))
      else 0)=r
    rw [Zr ho]
    change ql (zc n rem len bal par (qk n rem)) (uOdd j0 c0 s0) +
        z1 n uOdd tail.2.1 tail.2.2.1 tail.2.2.2 rem
         (len+uOdd j0 c0 s0*qs n o)
         (if c0=false then bal+uOdd j0 c0 s0 else bal-uOdd j0 c0 s0)
         (xor par (s0&&decide (uOdd j0 c0 s0 %2=1)))=r
    rw [hu_at0]
    rw [hrank_congr rem (by omega) _ _ _ uOdd tail.1 tail.2.1 tail.2.2.1 tail.2.2.2
         (fun j c' s' h=>by simp [uOdd,show q6 n j c' s'≠o by omega])]
    rw [ih_rank];exact hr_eq.symm
def v6 (n:ℕ):ℕ:=qk n (4*n) 0 0 false+1
def x5 (n:ℕ) :
  Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ)->ℕ
 | none=>0
 | some (oddC,ep,em,fus)=>1+z1 n oddC ep em fus (4*n) 0 0 false
def zy (n:ℕ) (r:ℕ) :
  Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ) :=
 if r=0 then none else some (qq n (4*n) 0 0 false (r-1))
lemma x2 (n:ℕ)
  (inv:Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ))
  (hv:xp n inv) :
  x5 n inv< v6 n/\zy n (x5 n inv)=inv:=by
 cases inv with
 | none =>
  simp [x5,zy,v6]
 | some val =>
  rcases val with ⟨oddC,ep,em,fus⟩
  rcases hv with ⟨hdisj,hlen,hbal,hpar,hfus⟩
  have hbal_le:j7 n oddC<=n:=by
   have h1:jl n oddC+j7 n oddC<=yn n oddC:=by
    unfold jl j7 yn;rw [<- Finset.sum_add_distrib];apply Finset.sum_le_sum;intro j _;nlinarith
   omega
  have hspec:=bo n oddC ep em fus hdisj hfus (4*n) le_rfl 0 0 false
   (by
    simp only [Nat.sub_self,wv,Nat.zero_add]
    rw [<- hlen];unfold yn;congr 1;apply Zc rfl;intro j _;ring)
   (by
    simp only [Nat.sub_self,wv,Nat.zero_add,Zh,Bool.true_eq_false,
     Ze,Zj,Zq]
    exact hbal)
   (by
    simp only [Nat.sub_self,wv,Zh,Ze,Zj,Nat.zero_add]
    exact hbal_le)
   (by
    simp only [Nat.sub_self,wv,Zh,Ze,Zj,
     Nat.zero_add,Zq,Bool.false_xor]
    change decide ((jf n oddC+wc n em)%2=1)=false
    simp [show (jf n oddC+wc n em)%2≠1 by omega])
  simp only [x5,zy,v6,show 1+z1 n oddC ep em fus (4*n) 0 0 false≠0 by omega,
   Zj,Nat.add_sub_cancel_left]
  refine ⟨by omega,?_⟩
  congr 1
  refine Prod.ext ?_ (Prod.ext hspec.2.2.1 (Prod.ext hspec.2.2.2.1 hspec.2.2.2.2))
  funext j c sig;exact hspec.2.1 j c sig (by omega)
lemma xq (n:ℕ) (r:ℕ) (hr:r< v6 n) :
   xp n (zy n r)/\x5 n (zy n r)=r:=by
 by_cases h0:r=0
 . subst h0;simp [zy,x5,xp]
 . simp only [zy,h0,Zj,x5,xp]
   have hr':r-1< qk n (4*n) 0 0 false:=by unfold v6 at hr;omega
   rcases pz n (4*n) le_rfl 0 0 false (r-1) hr' with
     ⟨_,hdisj,hlen,hbal,hpar,hfus,hrank⟩
   simp only [Nat.sub_self,wv,Nat.zero_add,Zh,Bool.true_eq_false,
     Ze,Zj,Zq,Bool.false_xor,decide_eq_false_iff_not] at hlen hbal hpar
   refine ⟨⟨hdisj,?_,hbal,?_,hfus⟩,by rw [hrank];omega⟩
   . rw [<- hlen];unfold yn;congr 1;apply Zc rfl;intro j _;ring
   . change (jf n _+wc n _)%2≠1 at hpar
     rcases Nat.mod_two_eq_zero_or_one (jf n _+wc n _) with h | h
     . exact h
     . exact absurd h hpar
def ww (n:ℕ) (j:Fin n) (st:(Fin n->ℕ) × (Fin n->ℕ) × ℕ) :
  (Fin n->ℕ) × (Fin n->ℕ) × ℕ :=
 let ep:=st.1
 let em:=st.2.1
 let remF:=st.2.2
 if h:(j.1+1)%2=0 then
  let s:=min (em j) remF
  let jh:Fin n:=⟨(j.1+1)/2-1,by omega⟩
  (fun k=>if k=jh then ep k+s else ep k,
   fun k=>if k=j then em k-s else if k=jh then em k+s else em k,
   remF-s)
 else st
def x6 (n:ℕ) (ep em:Fin n->ℕ) (fus:ℕ):(Fin n->ℕ) × (Fin n->ℕ) × ℕ :=
 (List.finRange n).foldl
  (fun st i=>ww n ⟨n-1-i.1,by omega⟩ st)
  (ep,em,fus)
lemma k4 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (j:Fin n)
   (ep em:Fin n->ℕ) (remF:ℕ)
   (hrem_le:remF<=∑ k:Fin n,if k.1<=j.1 then em k*v2 (k.1+1) else 0) :
   let st':=ww n j (ep,em,remF)
   wy n oddC st'.1 st'.2.1=wy n oddC ep em /\
   zj n st'.1 st'.2.1=zj n ep em /\
   wc n st'.2.1 %2=wc n em %2 /\
   (∑ k:Fin n,(st'.1 k+st'.2.1 k))+st'.2.2=(∑ k:Fin n,(ep k+em k))+remF /\
   st'.2.2<=∑ k:Fin n,if k.1< j.1 then st'.2.1 k*v2 (k.1+1) else 0:=by
 dsimp only [ww]
 split_ifs with hev
 . set s:=min (em j) remF
   let jh:Fin n:=⟨(j.1+1)/2-1,by omega⟩
   have hjh_val:j.1+1=2*(jh.1+1):=by dsimp [jh];omega
   have hjh_lt:jh.1< j.1:=by dsimp [jh];omega
   have hjh_ne:jh≠j:=fun h=>by rw [h] at hjh_lt;omega
   set ep':Fin n->ℕ:=fun k=>if k=jh then ep k+s else ep k
   set em':Fin n->ℕ:=fun k=>if k=j then em k-s else if k=jh then em k+s else em k
   have hs_le1:s<=em j:=Nat.min_le_left _ _;have hs_le2:s<=remF:=Nat.min_le_right _ _
   have hep'_jh:ep' jh=ep jh+s:=by simp [ep']
   have hep'_j:ep' j=ep j:=by simp [ep',hjh_ne.symm]
   have hem'_j:em' j=em j-s:=by simp [em']
   have hem'_jh:em' jh=em jh+s:=by simp [em',hjh_ne]
   have hother:∀ k:Fin n,k≠j->k≠jh->ep' k=ep k/\em' k=em k:=by
     intro k h1 h2;simp [ep',em',h1,h2]
   have hsum_split (F:Fin n->ℕ) :
       (∑ k:Fin n,F k)=F j+F jh+∑ k ∈ (Finset.univ.erase j).erase jh,F k:=by
     rw [<- Finset.add_sum_erase _ _ (Zu j)];have hmem:jh ∈ Finset.univ.erase j:=Finset.mem_erase.mpr ⟨hjh_ne,Zu jh⟩;rw [<- Finset.add_sum_erase _ _ hmem,add_assoc]
   refine ⟨?_,?_,?_,?_,?_⟩
   . unfold wy xd;rw [Za,xm,Za,xm];congr 1;rw [List.map_flatMap,j6,List.map_flatMap,j6]
     let g (a b:Fin n->ℕ) (k:Fin n):j5 :=
       qt (wp (zi (k.1+1) (k.1+1) 1) (a k))
           (wp (zi (k.1+1) (k.1+1) (-1)) (b k))
     have hrewrite (a b:Fin n->ℕ) :
        w9 ((List.finRange n).map fun k =>
          w9 ((List.replicate (a k) (k.1+1,k.1+1,(1:ℤ)) ++
                 List.replicate (b k) (k.1+1,k.1+1,(-1:ℤ))).map
             fun t=>zi t.1 t.2.1 t.2.2)) =
        w9 ((List.finRange n).map (g a b)):=by
       congr 1;apply List.map_congr_left;intro k _
       rw [Za,xm,Zy,Zy,
        ve,ve]
     rw [hrewrite ep' em',hrewrite ep em]
     have hperm2:(List.finRange n).Perm
        (jh :: j :: (List.finRange n).filter (fun k=>decide (k≠jh/\k≠j))):=by
       have hnod1:=List.nodup_finRange n
       have hnod2:(jh :: j :: (List.finRange n).filter (fun k=>decide (k≠jh/\k≠j))).Nodup:=by
        rw [List.nodup_cons,List.nodup_cons]
        refine ⟨by simp [hjh_ne],by simp,hnod1.filter _⟩
       exact (List.perm_ext_iff_of_nodup hnod1 hnod2).mpr fun k=>by
        simp only [List.mem_finRange,true_iff,List.mem_cons,List.mem_filter,true_and,
          decide_eq_true_eq]
        by_cases h1:k=jh
        . left;exact h1
        . by_cases h2:k=j
          . right;left;exact h2
          . right;right;exact ⟨h1,h2⟩
     rw [yt (hperm2.map (g ep' em')),yt (hperm2.map (g ep em))];simp only [List.map_cons,wd,<-zh];congr 1
     . dsimp only [g];rw [hep'_jh,hem'_jh,hep'_j,hem'_j,hjh_val]
       have hpow_pair:∀ c,
          qt (wp (zi (jh.1+1) (jh.1+1) 1) c)
              (wp (zi (jh.1+1) (jh.1+1) (-1)) c) =
          wp (zi (2*(jh.1+1)) (2*(jh.1+1)) (-1)) c:=by
        intro c;induction c with
        | zero=>simp [wp,jq]
        | succ c ihc =>
          simp only [wp]
          calc qt (qt (zi (jh.1+1) (jh.1+1) 1) (wp (zi (jh.1+1) (jh.1+1) 1) c))
                   (qt (zi (jh.1+1) (jh.1+1) (-1)) (wp (zi (jh.1+1) (jh.1+1) (-1)) c))
             = qt (qt (zi (jh.1+1) (jh.1+1) 1) (zi (jh.1+1) (jh.1+1) (-1)))
                  (qt (wp (zi (jh.1+1) (jh.1+1) 1) c) (wp (zi (jh.1+1) (jh.1+1) (-1)) c)):=by
                simp only [zh];congr 1;rw [<- zh,wq (wp _ c) (zi _ _ (-1)),zh]
          _=_:=by rw [pk (jh.1+1) (by omega),ihc]
       have he_em:em j=(em j-s)+s:=by omega
       conv_rhs=>rw [he_em]
       rw [kb,kb,kb,<-hpow_pair s];set A1:=wp (zi (jh.1+1) (jh.1+1) 1) (ep jh);set A2:=wp (zi (jh.1+1) (jh.1+1) 1) s;set B1:=wp (zi (jh.1+1) (jh.1+1) (-1)) (em jh);set B2:=wp (zi (jh.1+1) (jh.1+1) (-1)) s;set C1:=wp (zi (2*(jh.1+1)) (2*(jh.1+1)) 1) (ep j);set C2:=wp (zi (2*(jh.1+1)) (2*(jh.1+1)) (-1)) (em j-s)
       calc qt (qt (qt A1 A2) (qt B1 B2)) (qt C1 C2)
        = qt (qt (qt A1 B1) (qt A2 B2)) (qt C1 C2):=by
             congr 1;simp only [zh];congr 1;rw [<- zh A2 B1 B2,wq A2 B1,zh]
       _=qt (qt A1 B1) (qt (qt A2 B2) (qt C1 C2)):=by rw [zh]
       _=qt (qt A1 B1) (qt C1 (qt C2 (qt A2 B2))):=by
             congr 1;rw [wq (qt A2 B2) (qt C1 C2),zh]
     . congr 1;apply List.map_congr_left;intro k hk;simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] at hk;dsimp only [g];rw [(hother k hk.2 hk.1).1,(hother k hk.2 hk.1).2]
   . unfold zj
     rw [hsum_split (fun k=>2*(k.1+1)*(ep' k+em' k)),
        hsum_split (fun k=>2*(k.1+1)*(ep k+em k))]
     have hrest:∑ k ∈ (Finset.univ.erase j).erase jh,2*(k.1+1)*(ep' k+em' k) =
        ∑ k ∈ (Finset.univ.erase j).erase jh,2*(k.1+1)*(ep k+em k):=by
       apply Zc rfl;intro k hk;simp only [Finset.mem_erase] at hk;rw [(hother k hk.2.1 hk.1).1,(hother k hk.2.1 hk.1).2]
     rw [hrest,hep'_j,hem'_j,hep'_jh,hem'_jh,hjh_val]
     have:2*(2*(jh.1+1))*(ep j+(em j-s))+2*(jh.1+1)*(ep jh+s+(em jh+s)) =
        2*(2*(jh.1+1))*(ep j+em j)+2*(jh.1+1)*(ep jh+em jh):=by
       zify [hs_le1];ring
     omega
   . unfold wc;rw [hsum_split em',hsum_split em]
     have hrest:∑ k ∈ (Finset.univ.erase j).erase jh,em' k =
        ∑ k ∈ (Finset.univ.erase j).erase jh,em k:=by
       apply Zc rfl;intro k hk;simp only [Finset.mem_erase] at hk;exact (hother k hk.2.1 hk.1).2
     rw [hrest,hem'_j,hem'_jh]
     have:em j-s+(em jh+s)=em j+em jh:=by omega
     rw [this]
   . change (∑ k:Fin n,(ep' k+em' k))+(remF-s)=(∑ k:Fin n,(ep k+em k))+remF;rw [hsum_split (fun k=>ep' k+em' k),hsum_split (fun k=>ep k+em k)]
     have hrest:∑ k ∈ (Finset.univ.erase j).erase jh,(ep' k+em' k) =
        ∑ k ∈ (Finset.univ.erase j).erase jh,(ep k+em k):=by
       apply Zc rfl;intro k hk;simp only [Finset.mem_erase] at hk;rw [(hother k hk.2.1 hk.1).1,(hother k hk.2.1 hk.1).2]
     rw [hrest,hep'_j,hem'_j,hep'_jh,hem'_jh];omega
   . change remF-s<=∑ k:Fin n,if k.1< j.1 then em' k*v2 (k.1+1) else 0
     by_cases hmin:remF<=em j
     . have hs:s=remF:=Nat.min_eq_right hmin
       rw [hs,Nat.sub_self];exact Nat.zero_le _
     . have hs:s=em j:=Nat.min_eq_left (by omega)
       have hdiff :
          (∑ k:Fin n,if k.1<=j.1 then em k*v2 (k.1+1) else 0) =
          em j*v2 (j.1+1)+em jh*v2 (jh.1+1) +
             ∑ k ∈ (Finset.univ.erase j).erase jh,if k.1< j.1 then em k*v2 (k.1+1) else 0:=by
        rw [hsum_split (fun k=>if k.1<=j.1 then em k*v2 (k.1+1) else 0)];simp only [le_refl,Zh,show jh.1<=j.1 by omega];congr 1;apply Zc rfl;intro k hk;simp only [Finset.mem_erase] at hk
        have hne:k.1≠j.1:=fun h=>hk.2.1 (Zx h)
        by_cases hlt:k.1< j.1 <;> simp [hlt,show k.1<=j.1 ↔ k.1< j.1 by omega]
       have hdiff' :
          (∑ k:Fin n,if k.1< j.1 then em' k*v2 (k.1+1) else 0) =
          (em jh+em j)*v2 (jh.1+1) +
             ∑ k ∈ (Finset.univ.erase j).erase jh,if k.1< j.1 then em k*v2 (k.1+1) else 0:=by
        rw [hsum_split (fun k=>if k.1< j.1 then em' k*v2 (k.1+1) else 0)];simp only [lt_irrefl,Zj,Nat.zero_add,hjh_lt,Zh,hem'_jh,hs];congr 1;apply Zc rfl;intro k hk;simp only [Finset.mem_erase] at hk;rw [(hother k hk.2.1 hk.1).2]
       rw [hdiff] at hrem_le;rw [hdiff',hs];rw [hjh_val,c3 (by omega:0< jh.1+1)] at hrem_le
       have hlin:em j*(1+v2 (jh.1+1))+em jh*v2 (jh.1+1) =
          em j+(em jh+em j)*v2 (jh.1+1):=by ring
       omega
 . refine ⟨rfl,rfl,rfl,rfl,?_⟩
   have hv0:v2 (j.1+1)=0:=cj (by omega)
   have hsum_eq :
       (∑ k:Fin n,if k.1<=j.1 then em k*v2 (k.1+1) else 0) =
       (∑ k:Fin n,if k.1< j.1 then em k*v2 (k.1+1) else 0):=by
     apply Zc rfl;intro k _
     by_cases hke:k=j
     . subst hke;simp [hv0]
     . have hne:k.1≠j.1:=fun h=>hke (Zx h)
       by_cases hlt:k.1< j.1 <;> simp [hlt,show k.1<=j.1 ↔ k.1< j.1 by omega]
   rwa [<- hsum_eq]
lemma p4 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) (fus:ℕ)
  (hfus:fus<=wz n em) :
  let res:=x6 n ep em fus
  wy n oddC res.1 res.2.1=wy n oddC ep em /\
  zj n res.1 res.2.1=zj n ep em /\
  wc n res.2.1 %2=wc n em %2 /\
  (∑ k:Fin n,(res.1 k+res.2.1 k))=(∑ k:Fin n,(ep k+em k))+fus /\
  res.2.2=0:=by
 have hinv:∀ t ≤ n,
   let st:=((List.finRange n).take t).foldl
    (fun st i=>ww n ⟨n-1-i.1,by omega⟩ st) (ep,em,fus)
   wy n oddC st.1 st.2.1=wy n oddC ep em /\
   zj n st.1 st.2.1=zj n ep em /\
   wc n st.2.1 %2=wc n em %2 /\
   (∑ k:Fin n,(st.1 k+st.2.1 k))+st.2.2=(∑ k:Fin n,(ep k+em k))+fus /\
   st.2.2<=∑ k:Fin n,if k.1< n-t then st.2.1 k*v2 (k.1+1) else 0:=by
  intro t ht
  induction t with
  | zero =>
   simp only [Zn,Zi,Nat.sub_zero];exact ⟨trivial,trivial,trivial,trivial,by simpa [wz] using hfus⟩
  | succ t iht =>
   have htake:(List.finRange n).take (t+1) =
     (List.finRange n).take t++[⟨t,by omega⟩]:=by
    rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   set st:=((List.finRange n).take t).foldl
    (fun st i=>ww n ⟨n-1-i.1,by omega⟩ st) (ep,em,fus)
   rcases iht (by omega) with ⟨hbiv,hlen,hpar,hcnt,hrem⟩
   have hle_eq:(∑ k:Fin n,if k.1<=n-1-t then st.2.1 k*v2 (k.1+1) else 0) =
     (∑ k:Fin n,if k.1< n-t then st.2.1 k*v2 (k.1+1) else 0):=by
    apply Zc rfl;intro k _
    by_cases h:k.1< n-t <;> simp [h,show k.1<=n-1-t ↔ k.1< n-t by omega]
   have hstep:=k4 n oddC ⟨n-1-t,by omega⟩ st.1 st.2.1 st.2.2 (by rw [hle_eq];exact hrem)
   rcases hstep with ⟨sbiv,slen,spar,scnt,srem⟩
   refine ⟨sbiv.trans hbiv,slen.trans hlen,spar.trans hpar,scnt.trans hcnt,?_⟩
   simpa [show n-1-t=n-(t+1) by omega] using srem
 have hfull:=hinv n le_rfl;rw [Zk (by simp)] at hfull
 rcases hfull with ⟨hbiv,hlen,hpar,hcnt,hrem⟩
 have hzero:(x6 n ep em fus).2.2=0:=by
  have hsum0:(∑ k:Fin n,if k.1< n-n then (x6 n ep em fus).2.1 k*v2 (k.1+1) else 0)=0:=by
   simp
  have hrem':(x6 n ep em fus).2.2 <=
    ∑ k:Fin n,if k.1< n-n then (x6 n ep em fus).2.1 k*v2 (k.1+1) else 0:=hrem
  rw [hsum0] at hrem';omega
 have hcnt':(∑ k:Fin n,((x6 n ep em fus).1 k+(x6 n ep em fus).2.1 k)) +
   (x6 n ep em fus).2.2=(∑ k:Fin n,(ep k+em k))+fus:=hcnt
 exact ⟨hbiv,hlen,hpar,by omega,hzero⟩
def zl {α:Type*}:List α->List α->List α
 | a :: as,b :: bs=>a :: b :: zl as bs
 | _,_=>[]
def qg (n:ℕ) (hn:0< n) :
  List (ℕ × Bool)->ℕ->Bool->(Fin (2*n)->Option Bool)->(Fin (2*n)->Option Bool)
 | [],_,_,p=>p
 | (L,sig) :: rest,pos,bit,p =>
  let p':=fun k:Fin (2*n)=>if k.1=pos then some bit else p k
  qg n hn rest (pos+L) (xor bit sig) p'
def z9:ℕ->List (ℕ × Bool)->List (ℕ × ℕ × ℤ)
 | _,[]=>[]
 | pos,(L,sig) :: rest =>
  let ab:=wl (decide (pos %2=1)) L
  (ab.1,ab.2,if sig then -1 else 1) :: z9 (pos+L) rest
lemma vi (n:ℕ) (hn:0< n) :
  ∀ (arcs:List (ℕ × Bool)) (pos:ℕ) (bit:Bool) (p:Fin (2*n)->Option Bool)
    (hpos:∀ a ∈ arcs,1<=a.1)
    (hsum:pos+(arcs.map Prod.fst).sum<=2*n),
    (∀ k:Fin (2*n),pos<=k.1->p k=none) ->
    let p':=qg n hn arcs pos bit p
    (∀ k:Fin (2*n),k.1< pos\/pos+(arcs.map Prod.fst).sum<=k.1->p' k=p k) /\
    (Finset.univ.filter (fun k:Fin (2*n) =>
     pos<=k.1/\k.1< pos+(arcs.map Prod.fst).sum/\(p' k).isSome)).card=arcs.length /\
    (∀ a rest (heq:arcs=a :: rest),
     p' ⟨pos,by subst heq;have:=hpos a (List.mem_cons_self ..);simp at hsum;omega⟩=some bit /\
     ∀ r (hr1:1<=r) (hr2:r< a.1),
       p' ⟨pos+r,by subst heq;simp at hsum;omega⟩=none):=by
 intro arcs
 induction arcs with
 | nil =>
  intro pos bit p _ _ _
  refine ⟨fun _ _=>rfl,?_,fun _ _ h=>by cases h⟩
  have:Finset.univ.filter (fun k:Fin (2*n)=>pos<=k.1/\k.1< pos+0/\(p k).isSome)=∅:=by
    ext k;simp;omega
  simp only [qg,List.map_nil,List.sum_nil,List.length_nil];exact Finset.card_eq_zero.mpr this
 | cons a rest ih =>
  rcases a with ⟨L,sig⟩
  intro pos bit p hpos hsum hnone;have hL:1<=L:=hpos (L,sig) (List.mem_cons_self ..)
  have hsum':(pos+L)+(rest.map Prod.fst).sum<=2*n:=by simp at hsum;omega
  have hposL:pos+L<=2*n:=by omega
  set p1:Fin (2*n)->Option Bool:=fun k=>if k.1=pos then some bit else p k
  have hnone1:∀ k:Fin (2*n),pos+L<=k.1->p1 k=none:=by
    intro k hk;simp only [p1,show k.1≠pos by omega,Zj];exact hnone k (by omega)
  rcases ih (pos+L) (xor bit sig) p1
    (fun x hx=>hpos x (List.mem_cons_of_mem _ hx)) hsum' hnone1 with ⟨ih_out,ih_card,_⟩
  have hpos_lt:pos< 2*n:=by omega
  have hAtPos:qg n hn ((L,sig) :: rest) pos bit p ⟨pos,hpos_lt⟩=some bit:=by
    change qg n hn rest (pos+L) (xor bit sig) p1 ⟨pos,hpos_lt⟩=some bit;rw [ih_out ⟨pos,hpos_lt⟩ (Or.inl (by dsimp;omega))];simp [p1]
  have hMid:∀ r (hr1:1<=r) (hr2:r< L),
     qg n hn ((L,sig) :: rest) pos bit p ⟨pos+r,by omega⟩=none:=by
    intro r hr1 hr2;change qg n hn rest (pos+L) (xor bit sig) p1 ⟨pos+r,by omega⟩=none;rw [ih_out ⟨pos+r,by omega⟩ (Or.inl (by dsimp;omega))];simp only [p1,show pos+r≠pos by omega,Zj];exact hnone ⟨pos+r,by omega⟩ (by dsimp;omega)
  refine ⟨?_,?_,?_⟩
  . intro k hk;change qg n hn rest (pos+L) (xor bit sig) p1 k=p k;simp only [List.map_cons,List.sum_cons] at hk;rw [ih_out k (by omega)];simp only [p1,show k.1≠pos by omega,Zj]
  . set S:=Finset.univ.filter (fun k:Fin (2*n) =>
     pos<=k.1/\k.1< pos+(((L,sig) :: rest).map Prod.fst).sum /\
     (qg n hn ((L,sig) :: rest) pos bit p k).isSome)
    set T:=Finset.univ.filter (fun k:Fin (2*n) =>
     pos+L<=k.1/\k.1< pos+L+(rest.map Prod.fst).sum /\
     (qg n hn rest (pos+L) (xor bit sig) p1 k).isSome)
    have hS_eq:S=insert ⟨pos,hpos_lt⟩ T:=by
     ext k
     simp only [S,T,Finset.mem_insert,Zv,Zu,true_and,
       List.map_cons,List.sum_cons]
     constructor
     . rintro ⟨h1,h2,h3⟩
       by_cases hk0:k.1=pos
       . left;exact Zx hk0
       . by_cases hkL:k.1< pos+L
         . exfalso;have hnone_k:=hMid (k.1-pos) (by omega) (by omega);have hkeq:(⟨pos+(k.1-pos),by omega⟩:Fin (2*n))=k:=Zx (by dsimp;omega);rw [hkeq] at hnone_k;rw [hnone_k] at h3;simp at h3
         . right;exact ⟨by omega,by omega,h3⟩
     . rintro (rfl | ⟨h1,h2,h3⟩)
       . refine ⟨le_rfl,by dsimp;omega,?_⟩;rw [hAtPos];rfl
       . exact ⟨by omega,by omega,h3⟩
    have hnotmem:(⟨pos,hpos_lt⟩:Fin (2*n)) ∉ T:=by
     simp only [T,Zv];omega
    change S.card=rest.length+1;rw [hS_eq,Finset.card_insert_of_notMem hnotmem,ih_card]
  . intro a' rest' heq
    rcases List.cons.inj heq with ⟨rfl,rfl⟩
    exact ⟨hAtPos,hMid⟩
lemma pd (n:ℕ) (hn:0< n) :
  ∀ (arcs:List (ℕ × Bool)) (pos:ℕ) (bit bEnd:Bool) (p:Fin (2*n)->Option Bool)
   (hne:arcs≠[])
   (hpos:∀ a ∈ arcs,1<=a.1)
   (hsum:pos+(arcs.map Prod.fst).sum=2*n),
   (∀ k:Fin (2*n),pos<=k.1->p k=none) ->
   (arcs.foldl (fun b a=>xor b a.2) bit=bEnd) ->
   (qg n hn arcs pos bit p ⟨0,by omega⟩=some bEnd) ->
   y6 n hn (qg n hn arcs pos bit p)
    ⟨pos,by cases arcs with | nil=>exact absurd rfl hne | cons a _=>have:=hpos a (List.mem_cons_self ..);simp at hsum;omega⟩
    (arcs.map Prod.fst).sum bit bEnd =
   wr ((2:ℤ)^((arcs.map Prod.fst).sum-arcs.length))
    (w9 ((z9 pos arcs).map fun t=>zi t.1 t.2.1 t.2.2)):=by
 intro arcs
 induction arcs with
 | nil=>intro _ _ _ _ hne;exact absurd rfl hne
 | cons a rest ih =>
  rcases a with ⟨L,sig⟩
  intro pos bit bEnd p _ hpos hsum hnone hfold hp0;have hL:1<=L:=hpos (L,sig) (List.mem_cons_self ..)
  have hpos_lt:pos< 2*n:=by simp at hsum;omega
  have hposL_le:pos+L<=2*n:=by simp at hsum;omega
  rcases vi n hn ((L,sig) :: rest) pos bit p hpos (le_of_eq hsum) hnone with
   ⟨_,_,hhead⟩
  rcases hhead (L,sig) rest rfl with ⟨_,hMid⟩
  cases rest with
  | nil =>
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Zq,
    List.length_singleton,z9,wd,b9,bt]
   have hunp:∀ r,1<=r->r< L ->
     qg n hn [(L,sig)] pos bit p (q8 n hn ⟨pos,hpos_lt⟩ r)=none:=by
    intro r hr1 hr2
    have hcyc:q8 n hn ⟨pos,hpos_lt⟩ r=⟨pos+r,by omega⟩:=by
     apply Zx;simp [q8,Zm (show pos+r< 2*n by omega)]
    rw [hcyc];exact hMid r hr1 hr2
   rw [y1 n hn _ ⟨pos,hpos_lt⟩ L hL bit bEnd hunp];simp only [Zo,Zi] at hfold;congr 1;congr 1;subst hfold;cases bit <;> cases sig <;> rfl
  | cons a2 rest2 =>
   set tail:=a2 :: rest2
   have htail_pos:∀ x ∈ tail,1<=x.1:=fun x hx=>hpos x (List.mem_cons_of_mem _ hx)
   have htail_sum:1<=(tail.map Prod.fst).sum:=by
    have:=htail_pos a2 (List.mem_cons_self ..);simp [tail];omega
   have hsum_unfold:pos+(L+(tail.map Prod.fst).sum)=2*n:=by
    simpa [tail] using hsum
   have hposL_lt:pos+L< 2*n:=by omega
   have hcycL:q8 n hn ⟨pos,hpos_lt⟩ L=⟨pos+L,hposL_lt⟩:=by
    apply Zx;simp [q8,Zm hposL_lt]
   set p1:Fin (2*n)->Option Bool:=fun k=>if k.1=pos then some bit else p k
   have hnone1:∀ k:Fin (2*n),pos+L<=k.1->p1 k=none:=by
    intro k hk;simp only [p1,show k.1≠pos by omega,Zj];exact hnone k (by omega)
   have hsum1:(pos+L)+(tail.map Prod.fst).sum=2*n:=by omega
   have hmid_pin:qg n hn ((L,sig) :: tail) pos bit p (q8 n hn ⟨pos,hpos_lt⟩ L) =
     some (xor bit sig):=by
    rw [hcycL]
    exact ((vi n hn tail (pos+L) (xor bit sig) p1 htail_pos (le_of_eq hsum1) hnone1).2.2
     a2 rest2 rfl).1
   rw [px n hn _ ⟨pos,hpos_lt⟩ L (((L,sig) :: tail).map Prod.fst).sum
     (by omega) (by simp;omega) bit (xor bit sig) bEnd hmid_pin]
   have hunp:∀ r,1<=r->r< L ->
     qg n hn ((L,sig) :: tail) pos bit p (q8 n hn ⟨pos,hpos_lt⟩ r)=none:=by
    intro r hr1 hr2
    have hcyc:q8 n hn ⟨pos,hpos_lt⟩ r=⟨pos+r,by omega⟩:=by
     apply Zx;simp [q8,Zm (show pos+r< 2*n by omega)]
    rw [hcyc];exact hMid r hr1 hr2
   rw [y1 n hn _ ⟨pos,hpos_lt⟩ L hL bit (xor bit sig) hunp,hcycL]
   have hsub:(((L,sig) :: tail).map Prod.fst).sum-L=(tail.map Prod.fst).sum:=by simp
   rw [hsub]
   have hih:=ih (pos+L) (xor bit sig) bEnd p1 (by simp [tail]) htail_pos hsum1 hnone1
    (by simpa [tail] using hfold) hp0
   change qt _ (y6 n hn (qg n hn tail (pos+L) (xor bit sig) p1)
    ⟨pos+L,hposL_lt⟩ (tail.map Prod.fst).sum (xor bit sig) bEnd)=_
   rw [hih,pm,kg,kh]
   have hlen_tail_aux:∀ l:List (ℕ × Bool),(∀ x ∈ l,1<=x.1)->l.length<=(l.map Prod.fst).sum:=by
    intro l;induction l with
    | nil=>intro _;simp
    | cons x xs ihx =>
     intro h;have hx:=h x (List.mem_cons_self ..);have hxs:=ihx (fun y hy=>h y (List.mem_cons_of_mem _ hy));simp;omega
   have hlen_tail:tail.length<=(tail.map Prod.fst).sum:=hlen_tail_aux tail htail_pos
   have hpow:(2:ℤ)^(L-1)*(2:ℤ)^((tail.map Prod.fst).sum-tail.length) =
     (2:ℤ)^((((L,sig) :: tail).map Prod.fst).sum-((L,sig) :: tail).length):=by
    rw [<- pow_add];congr 1;simp;omega
   rw [hpow];congr 1;simp only [z9,List.map_cons,wd];congr 1;congr 1
   cases bit <;> cases sig <;> rfl
def y4 (n:ℕ) (ep em:Fin n->ℕ):List (ℕ × Bool) :=
 (List.finRange n).flatMap fun j =>
  List.replicate (ep j) (2*(j.1+1),false) ++
  List.replicate (em j) (2*(j.1+1),true)
def z7 (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (c:Bool):List (ℕ × Bool) :=
 (List.finRange n).flatMap fun j =>
  List.replicate (oddC j c false) (2*j.1+1,false) ++
  List.replicate (oddC j c true) (2*j.1+1,true)
def vj (n:ℕ) (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ):List (ℕ × Bool) :=
 y4 n ep em++zl (z7 n oddC false) (z7 n oddC true)
def wg (n:ℕ) (hn:0< n) :
  Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ) ->
  Fin (2*n)->Option Bool
 | none=>fun _=>none
 | some (oddC,ep,em,fus) =>
  let sp:=x6 n ep em fus
  qg n hn (vj n oddC sp.1 sp.2.1) 0 false (fun _=>none)
lemma vy (pos:ℕ) (l₁ l₂:List (ℕ × Bool)) :
  z9 pos (l₁++l₂) =
  z9 pos l₁++z9 (pos+(l₁.map Prod.fst).sum) l₂:=by
 induction l₁ generalizing pos with
 | nil=>simp [z9]
 | cons a as ih =>
  rcases a with ⟨L,sig⟩
  simp only [List.cons_append,z9,List.map_cons,List.sum_cons,ih,Nat.add_assoc]
lemma yc (n:ℕ) (hn:0< n)
  (inv:Option ((Fin n->Bool->Bool->ℕ) × (Fin n->ℕ) × (Fin n->ℕ) × ℕ))
  (hv:xp n inv) :
  zp n hn (wg n hn inv)=inv:=by
 cases inv with
 | none =>
  simp only [wg,zp]
  have h0:z2 n (fun _=>none)=0:=by simp [z2]
  simp [h0]
 | some val =>
  rcases val with ⟨oddC,ep,em,fus⟩
  rcases hv with ⟨hdisj,hlen,hbal,hpar,hfus⟩
  rcases p4 n oddC ep em fus hfus with ⟨hs_biv,hs_len,hs_par,hs_cnt,_⟩
  set ep'':=(x6 n ep em fus).1;set em'':=(x6 n ep em fus).2.1;set evL:=y4 n ep'' em'';set o0L:=z7 n oddC false;set o1L:=z7 n oddC true;set allL:=vj n oddC ep'' em''
  have hfin_flatMap_sum (f:Fin n->List (ℕ × Bool)) (g:ℕ × Bool->ℕ) :
    (((List.finRange n).flatMap f).map g).sum=∑ j:Fin n,((f j).map g).sum:=by
   have hlist:∀ l:List (Fin n),((l.flatMap f).map g).sum=(l.map fun j=>((f j).map g).sum).sum:=by
    intro l;induction l with
    | nil=>simp
    | cons x xs ih=>simp [List.flatMap_cons,Za,Zs,ih]
   rw [hlist,<-Fin.sum_univ_def]
  have hev_len:(evL.map Prod.fst).sum=zj n ep'' em'':=by
   dsimp only [evL,y4,zj];rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz];ring
  have hev_cnt:evL.length=∑ j:Fin n,(ep'' j+em'' j):=by
   have:=hfin_flatMap_sum (fun j=>List.replicate (ep'' j) (2*(j.1+1),false) ++
    List.replicate (em'' j) (2*(j.1+1),true)) (fun _=>1)
   have hlen_eq:∀ l:List (ℕ × Bool),(l.map (fun _=>1)).sum=l.length:=by
    intro l;induction l with | nil=>simp | cons _ _ ih=>simp [ih];omega
   rw [hlen_eq] at this;dsimp only [evL,y4];rw [this];apply Zc rfl;intro j _;simp [Za,Zy,Zz]
  have ho_cnt (c:Bool):(z7 n oddC c).length =
    ∑ j:Fin n,(oddC j c false+oddC j c true):=by
   have:=hfin_flatMap_sum (fun j=>List.replicate (oddC j c false) (2*j.1+1,false) ++
    List.replicate (oddC j c true) (2*j.1+1,true)) (fun _=>1)
   have hlen_eq:∀ l:List (ℕ × Bool),(l.map (fun _=>1)).sum=l.length:=by
    intro l;induction l with | nil=>simp | cons _ _ ih=>simp [ih];omega
   rw [hlen_eq] at this;dsimp only [z7];rw [this];apply Zc rfl;intro j _;simp [Za,Zy,Zz]
  have ho_len (c:Bool):((z7 n oddC c).map Prod.fst).sum =
    ∑ j:Fin n,(2*j.1+1)*(oddC j c false+oddC j c true):=by
   dsimp only [z7];rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz];ring
  have hzip_perm:∀ l₁ l₂:List (ℕ × Bool),l₁.length=l₂.length ->
    (zl l₁ l₂).Perm (l₁++l₂):=by
   intro l₁;induction l₁ with
   | nil=>intro l₂ h;cases l₂ with | nil=>simp [zl] | cons _ _=>simp at h
   | cons a as ih =>
    intro l₂ h;cases l₂ with
    | nil=>simp at h
    | cons b bs =>
      simp only [zl,List.cons_append];have hp:=ih bs (by simpa using h);exact ((hp.cons b).cons a).trans ((List.perm_middle.symm).cons a)
  have ho_eq_len:o0L.length=o1L.length:=by
   rw [ho_cnt false,ho_cnt true];exact hbal
  have hall_perm:allL.Perm (evL++o0L++o1L):=by
   dsimp only [allL,vj];rw [List.append_assoc];exact (hzip_perm o0L o1L ho_eq_len).append_left evL
  have hall_sum:(allL.map Prod.fst).sum=2*n:=by
   rw [(hall_perm.map Prod.fst).sum_eq,Za,Zs,
      Za,Zs,hev_len,ho_len false,ho_len true]
   have hodd_split:yn n oddC =
      (∑ j:Fin n,(2*j.1+1)*(oddC j false false+oddC j false true)) +
      (∑ j:Fin n,(2*j.1+1)*(oddC j true false+oddC j true true)):=by
    unfold yn;rw [<- Finset.sum_add_distrib];apply Zc rfl;intro j _;ring
   omega
  have hall_pos:∀ a ∈ allL,1<=a.1:=by
   intro a ha;have ha':=hall_perm.subset ha
   simp only [List.mem_append,evL,o0L,o1L,y4,z7,
    List.mem_flatMap,List.mem_replicate] at ha'
   rcases ha' with (⟨j,_,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ | ⟨j,_,⟨_,rfl⟩ | ⟨_,rfl⟩⟩) | ⟨j,_,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ <;> omega
  have hall_ne:allL≠[]:=by
   intro hnil;rw [hnil] at hall_sum;simp at hall_sum;omega
  have hall_len:allL.length =
    (∑ j:Fin n,(oddC j false false+oddC j false true+oddC j true false+oddC j true true)) +
    (∑ j:Fin n,(ep'' j+em'' j)):=by
   rw [hall_perm.length_eq,List.length_append,List.length_append,hev_cnt,ho_cnt false,ho_cnt true]
   have:(∑ j:Fin n,(oddC j false false+oddC j false true)) +
      (∑ j:Fin n,(oddC j true false+oddC j true true)) =
      ∑ j:Fin n,(oddC j false false+oddC j false true+oddC j true false+oddC j true true):=by
    rw [<- Finset.sum_add_distrib];apply Zc rfl;intro j _;omega
   omega
  have hev_neg:evL.countP Prod.snd=wc n em'':=by
   have hcp (l:List (ℕ × Bool)):l.countP Prod.snd=(l.map fun x=>if x.2 then 1 else 0).sum:=by
    induction l with | nil=>simp | cons x xs ih =>
      simp only [List.countP_cons,List.map_cons,List.sum_cons,ih]
      cases x.2 <;> simp <;> omega
   rw [hcp];dsimp only [evL,y4,wc];rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz]
  have ho_neg (c:Bool):(z7 n oddC c).countP Prod.snd=∑ j:Fin n,oddC j c true:=by
   have hcp (l:List (ℕ × Bool)):l.countP Prod.snd=(l.map fun x=>if x.2 then 1 else 0).sum:=by
    induction l with | nil=>simp | cons x xs ih =>
      simp only [List.countP_cons,List.map_cons,List.sum_cons,ih]
      cases x.2 <;> simp <;> omega
   rw [hcp];dsimp only [z7];rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz]
  have hall_fold:allL.foldl (fun b a=>xor b a.2) false=false:=by
   have hfx:∀ (l:List (ℕ × Bool)) (b:Bool),
      l.foldl (fun acc a=>xor acc a.2) b=xor b (decide (l.countP Prod.snd %2=1)):=by
    intro l;induction l with
    | nil=>intro b;simp
    | cons x xs ih =>
      intro b;simp only [Zo,ih,List.countP_cons]
      cases b <;> cases x.2 <;> simp <;>
        rcases (show xs.countP Prod.snd %2=0\/xs.countP Prod.snd %2=1 by omega) with hm | hm <;>
        simp [hm,show (xs.countP Prod.snd+1)%2=(xs.countP Prod.snd %2+1)%2 by omega]
   rw [hfx]
   have hcp_eq:allL.countP Prod.snd=wc n em''+jf n oddC:=by
    rw [hall_perm.countP_eq,List.countP_append,List.countP_append,hev_neg,ho_neg false,ho_neg true]
    have hodd_sum:(∑ j:Fin n,oddC j false true)+(∑ j:Fin n,oddC j true true)=jf n oddC:=by
      unfold jf;exact (Finset.sum_add_distrib).symm
    omega
   rw [hcp_eq];simp [show (wc n em''+jf n oddC)%2≠1 by omega]
  set pR:=wg n hn (some (oddC,ep,em,fus));have hpR_eq:pR=qg n hn allL 0 false (fun _=>none):=rfl
  rcases vi n hn allL 0 false (fun _=>none) hall_pos (le_of_eq (by omega)) (fun _ _=>rfl) with
   ⟨_,hpR_card,hpR_head⟩
  have hnum_pR:z2 n pR=allL.length:=by
   unfold z2;rw [<- hpR_card];apply congrArg Finset.card;ext k;simp [hpR_eq,hall_sum,k.isLt]
  have hpR0:pR ⟨0,by omega⟩=some false:=by
   cases h:allL with
   | nil=>exact absurd h hall_ne
   | cons a rest=>exact (hpR_head a rest h).1
  have hH_pR:pb n hn pR=wr ((2:ℤ)^(2*n-allL.length))
    (w9 ((z9 0 allL).map fun t=>zi t.1 t.2.1 t.2.2)):=by
   rw [xz n hn pR ⟨0,by omega⟩ false hpR0,hpR_eq]
   have hseg:=pd n hn allL 0 false false (fun _=>none)
    hall_ne hall_pos (by omega) (fun _ _=>rfl) hall_fold hpR0
   simpa only [hall_sum] using hseg
  have hfac_ev:∀ pos,pos %2=0 ->
    z9 pos evL =
    (List.finRange n).flatMap (fun j =>
      List.replicate (ep'' j) (j.1+1,j.1+1,(1:ℤ)) ++
      List.replicate (em'' j) (j.1+1,j.1+1,(-1:ℤ))):=by
   have hrep (pos L c:ℕ) (sig:Bool) (hL:L %2=0) (hp:pos %2=0) :
      z9 pos (List.replicate c (L,sig)) =
      List.replicate c (L/2,L/2,if sig then (-1:ℤ) else 1):=by
    induction c generalizing pos with
    | zero=>rfl
    | succ c ihc =>
      simp only [List.replicate_succ,z9,wl,hL,Zh];congr 1;exact ihc (pos+L) (by omega)
   have hgen (l:List (Fin n)) (pos:ℕ) (hp:pos %2=0) :
      z9 pos (l.flatMap fun j =>
        List.replicate (ep'' j) (2*(j.1+1),false) ++
        List.replicate (em'' j) (2*(j.1+1),true)) =
      l.flatMap fun j =>
        List.replicate (ep'' j) (j.1+1,j.1+1,(1:ℤ)) ++
        List.replicate (em'' j) (j.1+1,j.1+1,(-1:ℤ)):=by
    induction l generalizing pos with
    | nil=>rfl
    | cons j js ih =>
      simp only [List.flatMap_cons,vy];have h1:=hrep pos (2*(j.1+1)) (ep'' j) false (by omega) hp
      have hp1:(pos+((List.replicate (ep'' j) (2*(j.1+1),false)).map Prod.fst).sum)%2=0:=by
        simp only [Zy,Zz,smul_eq_mul]
        have:ep'' j*(2*(j.1+1))=2*(ep'' j*(j.1+1)):=by ring
        omega
      have h2:=hrep _ (2*(j.1+1)) (em'' j) true (by omega) hp1
      have hp2:(pos+(((List.replicate (ep'' j) (2*(j.1+1),false) ++
         List.replicate (em'' j) (2*(j.1+1),true)).map Prod.fst).sum))%2=0:=by
        simp only [Za,Zs,Zy,Zz,smul_eq_mul]
        have h1':ep'' j*(2*(j.1+1))=2*(ep'' j*(j.1+1)):=by ring
        have h2':em'' j*(2*(j.1+1))=2*(em'' j*(j.1+1)):=by ring
        omega
      rw [h1,h2,ih _ hp2];simp [show (2*(j.1+1))/2=j.1+1 by omega]
   intro pos hp;exact hgen (List.finRange n) pos hp
  have hfac_zip:∀ (l₀ l₁:List (ℕ × Bool)) (pos:ℕ),
    pos %2=0->l₀.length=l₁.length ->
    (∀ a ∈ l₀,a.1 %2=1)->(∀ a ∈ l₁,a.1 %2=1) ->
    (z9 pos (zl l₀ l₁)).Perm
      ((l₀.map fun a=>(a.1/2+1,a.1/2,if a.2 then (-1:ℤ) else 1)) ++
       (l₁.map fun a=>(a.1/2,a.1/2+1,if a.2 then (-1:ℤ) else 1))):=by
   intro l₀;induction l₀ with
   | nil =>
    intro l₁ pos _ hl _ _
    cases l₁ with | nil=>simp [zl,z9] | cons _ _=>simp at hl
   | cons a as ih =>
    intro l₁ pos hp hl h0 h1
    cases l₁ with
    | nil=>simp at hl
    | cons b bs =>
      rcases a with ⟨La,sa⟩;rcases b with ⟨Lb,sb⟩
      have hLa:La %2=1:=h0 (La,sa) (List.mem_cons_self ..);have hLb:Lb %2=1:=h1 (Lb,sb) (List.mem_cons_self ..)
      have hih:=ih bs (pos+La+Lb) (by omega) (by simpa using hl)
        (fun x hx=>h0 x (List.mem_cons_of_mem _ hx))
        (fun x hx=>h1 x (List.mem_cons_of_mem _ hx))
      simp only [zl,z9,wl,
        show La %2≠0 by omega,show Lb %2≠0 by omega,Zj,
        show pos %2≠1 by omega,show (pos+La)%2=1 by omega,
        decide_false,decide_true,Zh,List.map_cons,List.cons_append]
      set x0:=(La/2+1,La/2,if sa then (-1:ℤ) else 1);set y0:=(Lb/2,Lb/2+1,if sb then (-1:ℤ) else 1);exact ((hih.cons y0).cons x0).trans ((List.perm_middle.symm).cons x0)
  have hfac_odd_perm :
    ((o0L.map fun a:ℕ × Bool=>(a.1/2+1,a.1/2,if a.2 then (-1:ℤ) else 1)) ++
     (o1L.map fun a:ℕ × Bool=>(a.1/2,a.1/2+1,if a.2 then (-1:ℤ) else 1))).Perm
    ((List.finRange n).flatMap fun j =>
      List.replicate (oddC j false false) (j.1+1,j.1,(1:ℤ)) ++
      List.replicate (oddC j false true) (j.1+1,j.1,(-1:ℤ)) ++
      List.replicate (oddC j true false) (j.1,j.1+1,(1:ℤ)) ++
      List.replicate (oddC j true true) (j.1,j.1+1,(-1:ℤ))):=by
   have hgen (l:List (Fin n)) :
      ((l.flatMap fun j =>
         List.replicate (oddC j false false) (j.1+1,j.1,(1:ℤ)) ++
         List.replicate (oddC j false true) (j.1+1,j.1,(-1:ℤ))) ++
       (l.flatMap fun j =>
         List.replicate (oddC j true false) (j.1,j.1+1,(1:ℤ)) ++
         List.replicate (oddC j true true) (j.1,j.1+1,(-1:ℤ)))).Perm
      (l.flatMap fun j =>
        List.replicate (oddC j false false) (j.1+1,j.1,(1:ℤ)) ++
        List.replicate (oddC j false true) (j.1+1,j.1,(-1:ℤ)) ++
        List.replicate (oddC j true false) (j.1,j.1+1,(1:ℤ)) ++
        List.replicate (oddC j true true) (j.1,j.1+1,(-1:ℤ))):=by
    induction l with
    | nil=>simp
    | cons j js ih =>
      simp only [List.flatMap_cons,List.append_assoc]
      set A:=List.replicate (oddC j false false) (j.1+1,j.1,(1:ℤ)) ++
          List.replicate (oddC j false true) (j.1+1,j.1,(-1:ℤ))
      set B:=List.replicate (oddC j true false) (j.1,j.1+1,(1:ℤ)) ++
          List.replicate (oddC j true true) (j.1,j.1+1,(-1:ℤ))
      set X:=js.flatMap fun k =>
         List.replicate (oddC k false false) (k.1+1,k.1,(1:ℤ)) ++
         List.replicate (oddC k false true) (k.1+1,k.1,(-1:ℤ))
      set Y:=js.flatMap fun k =>
         List.replicate (oddC k true false) (k.1,k.1+1,(1:ℤ)) ++
         List.replicate (oddC k true true) (k.1,k.1+1,(-1:ℤ))
      have h1:(A++(X++(B++Y))).Perm (A++(B++(X++Y))):=by
        refine List.Perm.append_left A ?_
        have hp1:(X++(B++Y)).Perm ((X++B)++Y):=List.Perm.of_eq (List.append_assoc X B Y).symm;have hp2:((X++B)++Y).Perm ((B++X)++Y):=List.perm_append_comm.append_right Y;have hp3:((B++X)++Y).Perm (B++(X++Y)):=List.Perm.of_eq (List.append_assoc B X Y);exact (hp1.trans hp2).trans hp3
      have h2:(A++(B++(X++Y))).Perm (A++(B++(js.flatMap fun k =>
         List.replicate (oddC k false false) (k.1+1,k.1,(1:ℤ)) ++
         List.replicate (oddC k false true) (k.1+1,k.1,(-1:ℤ)) ++
         List.replicate (oddC k true false) (k.1,k.1+1,(1:ℤ)) ++
         List.replicate (oddC k true true) (k.1,k.1+1,(-1:ℤ))))) :=
        (ih.append_left B).append_left A
      simpa only [A,B,X,Y,List.append_assoc] using h1.trans h2
   have ho0_map:o0L.map (fun a=>(a.1/2+1,a.1/2,if a.2 then (-1:ℤ) else 1)) =
      (List.finRange n).flatMap fun j =>
        List.replicate (oddC j false false) (j.1+1,j.1,(1:ℤ)) ++
        List.replicate (oddC j false true) (j.1+1,j.1,(-1:ℤ)):=by
    dsimp only [o0L,z7];rw [List.map_flatMap];congr 1;funext j;simp [Za,Zy,show (2*j.1+1)/2=j.1 by omega]
   have ho1_map:o1L.map (fun a=>(a.1/2,a.1/2+1,if a.2 then (-1:ℤ) else 1)) =
      (List.finRange n).flatMap fun j =>
        List.replicate (oddC j true false) (j.1,j.1+1,(1:ℤ)) ++
        List.replicate (oddC j true true) (j.1,j.1+1,(-1:ℤ)):=by
    dsimp only [o1L,z7];rw [List.map_flatMap];congr 1;funext j;simp [Za,Zy,show (2*j.1+1)/2=j.1 by omega]
   rw [ho0_map,ho1_map];exact hgen (List.finRange n)
  have hall_fac_perm:(z9 0 allL).Perm (xd n oddC ep'' em''):=by
   dsimp only [allL,vj];rw [vy,hfac_ev 0 rfl]
   have hev_even:(0+(evL.map Prod.fst).sum)%2=0:=by
    rw [Nat.zero_add,hev_len];unfold zj
    have h2:2 ∣ ∑ j:Fin n,2*(j.1+1)*(ep'' j+em'' j):=by
      apply Finset.dvd_sum;intro j _;exact ⟨(j.1+1)*(ep'' j+em'' j),by ring⟩
    omega
   have ho_odd (c:Bool):∀ a ∈ z7 n oddC c,a.1 %2=1:=by
    intro a ha;simp only [z7,List.mem_flatMap,List.mem_append,List.mem_replicate] at ha
    rcases ha with ⟨j,_,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ <;> omega
   have hzip:=hfac_zip o0L o1L _ hev_even ho_eq_len (ho_odd false) (ho_odd true)
   have hcomb:=(hzip.trans hfac_odd_perm).append_left
    ((List.finRange n).flatMap fun j =>
      List.replicate (ep'' j) (j.1+1,j.1+1,(1:ℤ)) ++
      List.replicate (em'' j) (j.1+1,j.1+1,(-1:ℤ)))
   unfold xd;exact hcomb.trans List.perm_append_comm
  have hH_inv:pb n hn pR=wr ((2:ℤ)^(2*n-z2 n pR)) (wy n oddC ep em):=by
   rw [hH_pR,hnum_pR];congr 1;rw [<- hs_biv];unfold wy;exact yt (hall_fac_perm.map _)
  have hpos_pR:0< z2 n pR:=by
   rw [hnum_pR];cases h:allL with | nil=>exact absurd h hall_ne | cons _ _=>simp
  unfold zp;simp only [show z2 n pR≠0 by omega,Zj,Option.some.injEq,Prod.mk.injEq]
  rcases xf n hn pR hpos_pR with ⟨hHp,hlenp,hcntp,_,_⟩
  rcases y2 n (z3 n hn pR) (qo n hn pR) (qd n hn pR) (by omega) with
   ⟨hrbivp,hdisjp,_,_,hrcntp,_,_⟩
  have hscale_eq :
    wr ((2:ℤ)^(2*n-z2 n pR))
      (wy n (z3 n hn pR)
        (z0 n (qo n hn pR) (qd n hn pR)).1
        (z0 n (qo n hn pR) (qd n hn pR)).2.1) =
    wr ((2:ℤ)^(2*n-z2 n pR)) (wy n oddC ep em):=by
   rw [hrbivp,<-hHp,hH_inv]
  have hinv_eq :
    wy n (z3 n hn pR)
      (z0 n (qo n hn pR) (qd n hn pR)).1
      (z0 n (qo n hn pR) (qd n hn pR)).2.1 =
    wy n oddC ep em:=by
   funext a b;have h:=congrFun (congrFun hscale_eq a) b;exact mul_left_cancel₀ (by positivity:((2:ℤ)^(2*n-z2 n pR))≠0) h
  rcases va n _ _ _ _ _ _ hdisjp hdisj hinv_eq with ⟨ho,hep,hem⟩
  refine ⟨ho,hep,hem,?_⟩
  rw [hnum_pR,hall_len,hs_cnt] at hcntp;rw [<- hrcntp] at hcntp;rw [ho,hep,hem] at hcntp;omega
lemma vl (t:ℕ) :
  let n:=t+1
  let I:=Fin n
  let J:=Fin (n+1)
  let V:=Bool × I
  let X:=V->Bool
  let P:=V->Option Bool
  let hist:=fun (p:P) (d:J × J) =>
    ((Finset.univ:Finset X).filter (fun x =>
     (∀ u,p u=none\/p u=some (x u)) /\
     (Finset.univ.filter (fun i:I=>x (false,i)≠x (true,i))).card=d.1.1 /\
     (Finset.univ.filter (fun i:I=>x (false,i)≠x (true,i+1))).card=d.2.1)).card
  ((Finset.univ:Finset P).image hist).card=v6 n:=by
 intro n I J V X P hist
 have hn:0< n:=by omega
 have hhist_iff (p q:P) :
    hist p=hist q ↔ zp n hn (fun k=>p (z6 n k))=zp n hn (fun k=>q (z6 n k)):=by
  rw [<- yv n hn];constructor
  . intro h d1 hd1 d2 hd2;have hthis:=congrFun h (⟨d1,by omega⟩,⟨d2,by omega⟩);have h1:=wu t p (⟨d1,by omega⟩,⟨d2,by omega⟩);have h2:=wu t q (⟨d1,by omega⟩,⟨d2,by omega⟩);dsimp only [hist,V,I,J,X,P,n] at hthis;dsimp only at h1 h2;rw [<- h1,<-h2];exact hthis
  . intro h;funext d;dsimp only [hist];rw [wu,wu];exact h d.1.1 (by omega) d.2.1 (by omega)
 have hcard:((Finset.univ:Finset P).image hist).card=(Finset.univ:Finset (Fin (v6 n))).card:=by
  refine Finset.card_bij
    (fun h hh =>
     ⟨x5 n (zp n hn (fun k=>(Classical.choose (Finset.mem_image.mp hh)) (z6 n k))),
      (x2 n _ (x1 n hn _)).1⟩)
    (fun _ _=>Zu _) ?_ ?_
  . intro h₁ hh₁ h₂ hh₂ heq;have h1:=(Classical.choose_spec (Finset.mem_image.mp hh₁)).2;have h2:=(Classical.choose_spec (Finset.mem_image.mp hh₂)).2
    have hval:x5 n (zp n hn (fun k=>(Classical.choose (Finset.mem_image.mp hh₁)) (z6 n k))) =
      x5 n (zp n hn (fun k=>(Classical.choose (Finset.mem_image.mp hh₂)) (z6 n k))) :=
     congrArg Fin.val heq
    have hcan:zp n hn (fun k=>(Classical.choose (Finset.mem_image.mp hh₁)) (z6 n k)) =
      zp n hn (fun k=>(Classical.choose (Finset.mem_image.mp hh₂)) (z6 n k)):=by
     rw [<- (x2 n _ (x1 n hn _)).2,hval,
       (x2 n _ (x1 n hn _)).2]
    rw [<- h1,<-h2];exact (hhist_iff _ _).mpr hcan
  . intro r _
    let pCyc:=wg n hn (zy n r.1)
    let pOrig:P:=fun u=>pCyc (xl n u)
    have hp_conv:(fun k=>pOrig (z6 n k))=pCyc:=by
     funext k;dsimp only [pOrig];rw [v8]
    have hmem:hist pOrig ∈ (Finset.univ:Finset P).image hist :=
     Finset.mem_image.mpr ⟨pOrig,Zu _,rfl⟩
    refine ⟨hist pOrig,hmem,?_⟩
    apply Zx;dsimp only;have hch:=(Classical.choose_spec (Finset.mem_image.mp hmem)).2;have hcan:=(hhist_iff _ pOrig).mp hch
    rw [hcan,hp_conv,
      yc n hn (zy n r.1) (xq n r.1 r.isLt).1,
      (xq n r.1 r.isLt).2]
 simpa using hcard
lemma cd (t:ℕ):v6 (t+1)<=2^(4*(t+1)):=by
 let n:=t+1
 let I:=Fin n
 let J:=Fin (n+1)
 let V:=Bool × I
 let X:=V->Bool
 let P:=V->Option Bool
 let hist:=fun (p:P) (d:J × J) =>
  ((Finset.univ:Finset X).filter (fun x =>
   (∀ u,p u=none\/p u=some (x u)) /\
   (Finset.univ.filter (fun i:I=>x (false,i)≠x (true,i))).card=d.1.1 /\
   (Finset.univ.filter (fun i:I=>x (false,i)≠x (true,i+1))).card=d.2.1)).card
 rw [<- vl t]
 have h1:((Finset.univ:Finset P).image hist).card<=(Finset.univ:Finset P).card :=
  Finset.card_image_le
 have h2:(Finset.univ:Finset P).card=3^(2*n):=by
  simp [P,V,I,Fintype.card_fun,Fintype.card_option,Fintype.card_prod]
 have h3:3^(2*n)<=4^(2*n):=Nat.pow_le_pow_left (by omega) _
 have h4:4^(2*n)=2^(4*n):=by
  rw [show (4:ℕ)=2^2 by rfl,<-pow_mul];congr 1;ring
 exact le_trans h1 (by rw [h2];exact le_trans h3 (by rw [h4]))
def xr (p:Fin m->Option Bool) (k:Fin m) (b:Bool):Bool :=
 match p k with
 | none=>true
 | some v=>decide (v=b)
def kj (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (s:ℕ) (hs:s+1< 2*n)
  (prev:Bool->ℕ->ℕ->ℕ) (b:Bool) (c0 c1:ℕ):ℕ :=
 if xr p ⟨s+1,hs⟩ b then
  let term (bPrev:Bool):ℕ :=
   if bPrev≠b then
    if s %2=0 then (if 0< c0 then prev bPrev (c0-1) c1 else 0)
    else (if 0< c1 then prev bPrev c0 (c1-1) else 0)
   else prev bPrev c0 c1
  term false+term true
 else 0
def w7 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (b₀:Bool) :
  ℕ->Bool->ℕ->ℕ->ℕ
 | 0,b,c0,c1 =>
  if b=b₀/\xr p ⟨0,by omega⟩ b₀=true/\c0=0/\c1=0 then 1 else 0
 | s+1,b,c0,c1 =>
  if hs:s+1< 2*n then
   kj n hn p s hs (w7 n hn p b₀ s) b c0 c1
  else 0
def xe (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (d1 d2:ℕ):ℕ :=
 let evalB0 (b₀:Bool):ℕ :=
  let tab:=w7 n hn p b₀ (2*n-1)
  let term (bLast:Bool):ℕ :=
   if bLast≠b₀ then (if 0< d2 then tab bLast d1 (d2-1) else 0)
   else tab bLast d1 d2
  term false+term true
 evalB0 false+evalB0 true
lemma bk (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (b₀:Bool) :
  ∀ s (hs:s< 2*n) (b:Bool) (c0 c1:ℕ),
    w7 n hn p b₀ s b c0 c1 =
    ((Finset.univ:Finset (Fin (s+1)->Bool)).filter (fun y =>
      y ⟨0,by omega⟩=b₀ /\
      y ⟨s,by omega⟩=b /\
      (∀ i:Fin (s+1),xr p ⟨i.1,by omega⟩ (y i)=true) /\
      (Finset.univ.filter (fun e:Fin s=>e.1 %2=0/\y ⟨e.1,by omega⟩≠y ⟨e.1+1,by omega⟩)).card=c0 /\
      (Finset.univ.filter (fun e:Fin s=>e.1 %2=1/\y ⟨e.1,by omega⟩≠y ⟨e.1+1,by omega⟩)).card=c1)).card:=by
 intro s
 induction s with
 | zero =>
  intro _ b c0 c1;simp only [w7]
  split_ifs with h
  . rcases h with ⟨rfl,hal,rfl,rfl⟩
    symm;rw [Finset.card_eq_one]
    refine ⟨fun _=>b,?_⟩
    ext y;simp only [Zv,Zu,true_and,Finset.mem_singleton];constructor
    . intro hy;funext i;fin_cases i;exact hy.1
    . intro hy;subst hy;refine ⟨rfl,rfl,fun i=>by fin_cases i;exact hal,by simp,by simp⟩
  . symm;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro y _ hy;apply h
    refine ⟨hy.2.1.symm.trans hy.1,?_,?_,?_⟩
    . have:=hy.2.2.1 ⟨0,by omega⟩;rwa [hy.1] at this
    . simpa using hy.2.2.2.1.symm
    . simpa using hy.2.2.2.2.symm
 | succ s ih =>
  intro hs b c0 c1;simp only [w7,hs,Zd,kj]
  set S:=(Finset.univ:Finset (Fin (s+2)->Bool)).filter (fun y =>
    y ⟨0,by omega⟩=b₀ /\
    y ⟨s+1,by omega⟩=b /\
    (∀ i:Fin (s+2),xr p ⟨i.1,by omega⟩ (y i)=true) /\
    (Finset.univ.filter (fun e:Fin (s+1)=>e.1 %2=0/\y ⟨e.1,by omega⟩≠y ⟨e.1+1,by omega⟩)).card=c0 /\
    (Finset.univ.filter (fun e:Fin (s+1)=>e.1 %2=1/\y ⟨e.1,by omega⟩≠y ⟨e.1+1,by omega⟩)).card=c1)
  by_cases hal:xr p ⟨s+1,hs⟩ b=true
  . simp only [hal,Zh]
    have hsplit:S.card =
        (S.filter (fun y=>y ⟨s,by omega⟩=false)).card +
        (S.filter (fun y=>y ⟨s,by omega⟩=true)).card:=by
      rw [<- Finset.card_union_of_disjoint]
      . congr 1;ext y;simp only [Finset.mem_union,Zv]
        cases y ⟨s,by omega⟩ <;> simp
      . rw [Finset.disjoint_left];intro y h1 h2;simp only [Zv] at h1 h2;rw [h1.2] at h2;cases h2.2
    rw [hsplit]
    have hbranch (bPrev:Bool) :
        (if bPrev≠b then
          if s %2=0 then (if 0< c0 then w7 n hn p b₀ s bPrev (c0-1) c1 else 0)
          else (if 0< c1 then w7 n hn p b₀ s bPrev c0 (c1-1) else 0)
         else w7 n hn p b₀ s bPrev c0 c1) =
        (S.filter (fun y=>y ⟨s,by omega⟩=bPrev)).card:=by
      have hedge (y:Fin (s+2)->Bool) (r:ℕ) :
          (Finset.univ.filter (fun e:Fin (s+1) =>
            e.1 %2=r/\y ⟨e.1,Nat.lt_succ_of_lt e.isLt⟩≠y ⟨e.1+1,Nat.succ_lt_succ e.isLt⟩)).card =
          (Finset.univ.filter (fun e:Fin s =>
            e.1 %2=r/\y ⟨e.1,Nat.lt_succ_of_lt (Nat.lt_succ_of_lt e.isLt)⟩≠y ⟨e.1+1,Nat.lt_succ_of_lt (Nat.succ_lt_succ e.isLt)⟩)).card +
          if s %2=r/\y ⟨s,Nat.lt_succ_of_lt (Nat.lt_succ_self s)⟩≠y ⟨s+1,Nat.lt_succ_self (s+1)⟩ then 1 else 0:=by
        rw [Finset.card_filter,Finset.card_filter,Fin.sum_univ_castSucc];congr 1
      have hbij (c0' c1':ℕ)
          (hc0:c0=c0'+if s %2=0/\bPrev≠b then 1 else 0)
          (hc1:c1=c1'+if s %2=1/\bPrev≠b then 1 else 0) :
          w7 n hn p b₀ s bPrev c0' c1'=(S.filter (fun y=>y ⟨s,by omega⟩=bPrev)).card:=by
        rw [ih (by omega) bPrev c0' c1']
        refine Finset.card_bij
          (fun y _=>fun i:Fin (s+2)=>if h:i.1< s+1 then y ⟨i.1,h⟩ else b)
          ?_ ?_ ?_
        . intro y hy;simp only [Zv,Zu,true_and,S] at hy ⊢
          rcases hy with ⟨h0,hs',hall,he0,he1⟩
          let y':Fin (s+2)->Bool:=fun i=>if h:i.1< s+1 then y ⟨i.1,h⟩ else b
          refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
          . rw [Zr (Nat.zero_lt_succ s)];exact h0
          . simp
          . intro i
            by_cases hi:i.1< s+1
            . simp only [hi,Zd];exact hall ⟨i.1,hi⟩
            . simp only [hi,Zf];have hieq:(⟨i.1,by omega⟩:Fin (2*n))=⟨s+1,hs⟩:=Zx (by dsimp;omega);rw [hieq];exact hal
          . change (Finset.univ.filter (fun e:Fin (s+1)=>e.1 %2=0/\y' ⟨e.1,by omega⟩≠y' ⟨e.1+1,by omega⟩)).card=c0;rw [hedge y' 0]
            have hy's:y' ⟨s,by omega⟩=bPrev:=by simp [y',hs']
            have hy's1:y' ⟨s+1,by omega⟩=b:=by simp [y']
            have hpref:(Finset.univ.filter (fun e:Fin s=>e.1 %2=0/\y' ⟨e.1,by omega⟩≠y' ⟨e.1+1,by omega⟩)).card=c0':=by
              rw [<- he0];apply congrArg Finset.card;ext e;simp [y',show e.1< s+1 by omega,show e.1+1< s+1 by omega]
            rw [hy's,hy's1,hpref];omega
          . change (Finset.univ.filter (fun e:Fin (s+1)=>e.1 %2=1/\y' ⟨e.1,by omega⟩≠y' ⟨e.1+1,by omega⟩)).card=c1;rw [hedge y' 1]
            have hy's:y' ⟨s,by omega⟩=bPrev:=by simp [y',hs']
            have hy's1:y' ⟨s+1,by omega⟩=b:=by simp [y']
            have hpref:(Finset.univ.filter (fun e:Fin s=>e.1 %2=1/\y' ⟨e.1,by omega⟩≠y' ⟨e.1+1,by omega⟩)).card=c1':=by
              rw [<- he1];apply congrArg Finset.card;ext e;simp [y',show e.1< s+1 by omega,show e.1+1< s+1 by omega]
            rw [hy's,hy's1,hpref];omega
          . simp [hs']
        . intro y₁ _ y₂ _ heq;funext i;have:=congrFun heq ⟨i.1,by omega⟩;simpa [i.isLt] using this
        . intro y hy;simp only [Zv,Zu,true_and,S] at hy
          rcases hy with ⟨⟨h0,hlast,hall,he0,he1⟩,hprev⟩
          refine ⟨fun i:Fin (s+1)=>y ⟨i.1,by omega⟩,?_,?_⟩
          . simp only [Zv,Zu,true_and];rw [hedge y 0,hprev,hlast] at he0;rw [hedge y 1,hprev,hlast] at he1;exact ⟨h0,hprev,fun i=>hall ⟨i.1,by omega⟩,by omega,by omega⟩
          . funext i
            by_cases hi:i.1< s+1
            . simp [hi]
            . have hieq:i=⟨s+1,by omega⟩:=Zx (by dsimp;omega);rw [hieq];simp [hlast]
      split_ifs with hne hs0 hc0
      . exact hbij (c0-1) c1 (by simp [hs0,hne];omega) (by simp [show s %2≠1 by omega])
      . symm;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro y hy hprev;simp only [Zv,Zu,true_and,S] at hy;have:=hedge y 0;rw [hy.2.2.2.1,hprev,hy.2.1] at this;simp [hs0,hne] at this;omega
      . have hs1:s %2=1:=by omega
        exact hbij c0 (c1-1) (by simp [hs0]) (by simp [hs1,hne];omega)
      . have hs1:s %2=1:=by omega
        symm;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro y hy hprev;simp only [Zv,Zu,true_and,S] at hy;have:=hedge y 1;rw [hy.2.2.2.2,hprev,hy.2.1] at this;simp [hs1,hne] at this;omega
      . exact hbij c0 c1 (by simp [hne]) (by simp [hne])
    rw [hbranch false,hbranch true]
  . have halF:xr p ⟨s+1,hs⟩ b=false:=Bool.eq_false_iff.mpr hal;rw [halF];simp only [Ze,Zj];symm;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro y _ hy;have:=hy.2.2.1 ⟨s+1,by omega⟩;rw [hy.2.1] at this;exact hal this
lemma y7 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (d1 d2:ℕ) :
  xe n hn p d1 d2=wt n hn p d1 d2:=by
 unfold xe wt
 set All:=(Finset.univ:Finset (Fin (2*n)->Bool)).filter (fun y =>
  (∀ k,p k=none\/p k=some (y k)) /\
  (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card=d1 /\
  (Finset.univ.filter (fun i:Fin n =>
    y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card=d2)
 have hsplit2 (A:Finset (Fin (2*n)->Bool)) (k:Fin (2*n)) :
    A.card=(A.filter (fun y=>y k=false)).card+(A.filter (fun y=>y k=true)).card:=by
  rw [<- Finset.card_union_of_disjoint]
  . congr 1;ext y;simp only [Finset.mem_union,Zv];cases y k <;> simp
  . rw [Finset.disjoint_left];intro y h1 h2;simp only [Zv] at h1 h2;rw [h1.2] at h2;cases h2.2
 rw [hsplit2 All ⟨0,by omega⟩,hsplit2 (All.filter _) ⟨2*n-1,by omega⟩,
    hsplit2 (All.filter _) ⟨2*n-1,by omega⟩]
 have hcell (b₀ bLast:Bool) :
    (if bLast≠b₀ then
      if 0< d2 then w7 n hn p b₀ (2*n-1) bLast d1 (d2-1) else 0
     else w7 n hn p b₀ (2*n-1) bLast d1 d2) =
    ((All.filter (fun y=>y ⟨0,by omega⟩=b₀)).filter (fun y=>y ⟨2*n-1,by omega⟩=bLast)).card:=by
  have hallows_iff (k:Fin (2*n)) (b:Bool) :
      xr p k b=true ↔ (p k=none\/p k=some b):=by
    unfold xr;cases p k with
    | none=>simp
    | some v=>simp [eq_comm]
  have hcard0 (y:Fin (2*n)->Bool) :
      (Finset.univ.filter (fun e:Fin (2*n-1) =>
        e.1 %2=0/\y ⟨e.1,Nat.lt_of_lt_of_le e.isLt (Nat.sub_le _ _)⟩≠y ⟨e.1+1,Nat.add_lt_of_lt_sub e.isLt⟩)).card =
      (Finset.univ.filter (fun i:Fin n=>y ⟨2*i.1,by omega⟩≠y ⟨2*i.1+1,by omega⟩)).card:=by
    refine Finset.card_bij (fun e _=>⟨e.1/2,by have:=e.isLt;omega⟩) ?_ ?_ ?_
    . intro e he;simp only [Zv,Zu,true_and] at he ⊢
      have h2:2*(e.1/2)=e.1:=by omega
      simpa [h2] using he.2
    . intro e₁ he₁ e₂ he₂ heq;simp only [Zv,Zu,true_and] at he₁ he₂
      have:=congrArg Fin.val heq;dsimp at this
      exact Zx (by omega)
    . intro i hi;have hi_lt:=i.isLt;simp only [Zv,Zu,true_and] at hi
      refine ⟨⟨2*i.1,by omega⟩,?_,Zx (by dsimp;omega)⟩
      simp only [Zv,Zu,true_and];exact ⟨by omega,hi⟩
  have hcard1 (y:Fin (2*n)->Bool) :
      (Finset.univ.filter (fun i:Fin n =>
        y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card =
      (Finset.univ.filter (fun e:Fin (2*n-1) =>
        e.1 %2=1/\y ⟨e.1,Nat.lt_of_lt_of_le e.isLt (Nat.sub_le _ _)⟩≠y ⟨e.1+1,Nat.add_lt_of_lt_sub e.isLt⟩)).card +
      if y ⟨2*n-1,by omega⟩≠y ⟨0,by omega⟩ then 1 else 0:=by
    have hlast_next:zs n hn ⟨2*(n-1)+1,by omega⟩=⟨0,by omega⟩:=by
      apply Zx;simp [zs,q8,show 2*(n-1)+1+1=2*n by omega]
    have hmid_next (i:Fin n) (hi:i.1< n-1) :
        zs n hn ⟨2*i.1+1,by omega⟩=⟨2*i.1+2,by omega⟩:=by
      apply Zx;simp [zs,q8,Zm (show 2*i.1+1+1< 2*n by omega)]
    have hsum_all:(Finset.univ.filter (fun i:Fin n =>
        y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩))).card =
        (Finset.univ.filter (fun i:Fin n =>
         i.1< n-1/\y ⟨2*i.1+1,by omega⟩≠y ⟨(2*i.1+2)%(2*n),Nat.mod_lt _ (by omega)⟩)).card +
        if y ⟨2*n-1,by omega⟩≠y ⟨0,by omega⟩ then 1 else 0:=by
      rw [Finset.card_filter,Finset.card_filter,
         <- Finset.add_sum_erase _ _ (Zu (⟨n-1,by omega⟩:Fin n))]
      have hterm_last :
         (if y ⟨2*(n-1)+1,by omega⟩≠y (zs n hn ⟨2*(n-1)+1,by omega⟩) then 1 else 0) =
         if y ⟨2*n-1,by omega⟩≠y ⟨0,by omega⟩ then 1 else 0:=by
        have hidx:(⟨2*(n-1)+1,by omega⟩:Fin (2*n))=⟨2*n-1,by omega⟩ :=
         Zx (by dsimp;omega)
        rw [hlast_next];simp only [hidx]
      have hterm_rest :
         (∑ i ∈ Finset.univ.erase (⟨n-1,by omega⟩:Fin n),
          if y ⟨2*i.1+1,by omega⟩≠y (zs n hn ⟨2*i.1+1,by omega⟩) then 1 else 0) =
         ∑ i:Fin n,if i.1< n-1/\y ⟨2*i.1+1,by omega⟩≠y ⟨(2*i.1+2)%(2*n),Nat.mod_lt _ (by omega)⟩ then 1 else 0:=by
        rw [<- Finset.add_sum_erase Finset.univ
         (fun i:Fin n=>if i.1< n-1/\y ⟨2*i.1+1,by omega⟩≠y ⟨(2*i.1+2)%(2*n),Nat.mod_lt _ (by omega)⟩ then 1 else 0)
         (Zu (⟨n-1,by omega⟩:Fin n))]
        simp only [lt_irrefl,false_and,Zj,Nat.zero_add];apply Zc rfl;intro i hi;rw [Finset.mem_erase] at hi
        have hlt:i.1< n-1:=by have:=i.isLt;have:i.1≠n-1:=fun h=>hi.1 (Zx h);omega
        have hmod:(⟨(2*i.1+2)%(2*n),Nat.mod_lt _ (by omega)⟩:Fin (2*n))=⟨2*i.1+2,by omega⟩ :=
         Zx (by dsimp;exact Zm (by omega))
        rw [hmid_next i hlt,hmod];simp [hlt]
      rw [hterm_last,hterm_rest];omega
    rw [hsum_all];congr 1
    refine Finset.card_bij (fun i hi=>⟨2*i.1+1,by
      simp only [Zv,Zu,true_and] at hi;omega⟩) ?_ ?_ ?_
    . intro i hi;have hi_lt:=i.isLt;simp only [Zv,Zu,true_and] at hi ⊢;have hlt:=hi.1
      have hmod:(⟨(2*i.1+2)%(2*n),Nat.mod_lt _ (by omega)⟩:Fin (2*n))=⟨2*i.1+2,by omega⟩ :=
        Zx (by dsimp;exact Zm (by omega))
      refine ⟨by omega,?_⟩
      rw [hmod] at hi;exact hi.2
    . intro i₁ _ i₂ _ heq
      have:=congrArg Fin.val heq;dsimp at this;exact Zx (by omega)
    . intro e he;have he_lt:=e.isLt;simp only [Zv,Zu,true_and] at he
      refine ⟨⟨e.1/2,by omega⟩,?_,Zx (by dsimp;omega)⟩
      simp only [Zv,Zu,true_and]
      have h1:2*(e.1/2)+1=e.1:=by omega
      have h2:(2*(e.1/2)+2)%(2*n)=e.1+1:=by
        rw [Zm (by omega)];omega
      refine ⟨by omega,?_⟩
      simpa [h1,h2] using he.2
  have hbij (d2':ℕ) (hd2:d2=d2'+if bLast≠b₀ then 1 else 0) :
      w7 n hn p b₀ (2*n-1) bLast d1 d2' =
      ((All.filter (fun y=>y ⟨0,by omega⟩=b₀)).filter (fun y=>y ⟨2*n-1,by omega⟩=bLast)).card:=by
    rw [bk n hn p b₀ (2*n-1) (by omega) bLast d1 d2']
    refine Finset.card_bij
      (fun y _=>fun k:Fin (2*n)=>y ⟨k.1,by omega⟩) ?_ ?_ ?_
    . intro y hy;simp only [Zv,Zu,true_and,All] at hy ⊢
      rcases hy with ⟨h0,hlast,hall,he0,he1⟩
      let y':Fin (2*n)->Bool:=fun k=>y ⟨k.1,by omega⟩
      refine ⟨⟨⟨?_,?_,?_⟩,h0⟩,hlast⟩
      . intro k;exact (hallows_iff k _).mp (hall ⟨k.1,by omega⟩)
      . change (Finset.univ.filter (fun i:Fin n=>y' ⟨2*i.1,by omega⟩≠y' ⟨2*i.1+1,by omega⟩)).card=d1;rw [<- hcard0 y'];exact he0
      . change (Finset.univ.filter (fun i:Fin n=>y' ⟨2*i.1+1,by omega⟩≠y' (zs n hn ⟨2*i.1+1,by omega⟩))).card=d2;rw [hcard1 y'];dsimp only [y'];simp only [hlast,h0];rw [he1,hd2]
    . intro y₁ _ y₂ _ heq;funext i;have:=congrFun heq ⟨i.1,by omega⟩;exact this
    . intro y hy;simp only [Zv,Zu,true_and,All] at hy
      rcases hy with ⟨⟨⟨hall,he0,he1⟩,h0⟩,hlast⟩
      refine ⟨fun i:Fin (2*n-1+1)=>y ⟨i.1,by omega⟩,?_,?_⟩
      . simp only [Zv,Zu,true_and];rw [hcard1 y,hlast,h0] at he1;rw [<- hcard0 y] at he0;exact ⟨h0,hlast,fun i=>(hallows_iff ⟨i.1,by omega⟩ _).mpr (hall ⟨i.1,by omega⟩),he0,by omega⟩
      . funext k;rfl
  split_ifs with hne hd2
  . exact hbij (d2-1) (by simp [hne];omega)
  . symm;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro y hy hlast;simp only [Zv,Zu,true_and,All] at hy;have:=hcard1 y;rw [hy.1.2.2,hlast,hy.2] at this;simp [hne] at this;omega
  . exact hbij d2 (by simp [hne])
 dsimp only;rw [hcell false false,hcell false true,hcell true false,hcell true true]
def yd {d₁:ℕ} (d₂:ℕ) (a:Fin d₁->Bool):Fin d₂->Bool :=
 fun i=>if h:i.1< d₁ then a ⟨i.1,h⟩ else false
lemma k5 {m d₁ d₂ B:ℕ} {a:(Fin m->Bool)->(Fin d₁->Bool)}
  (ha:q0 a B):q0 (fun x=>yd d₂ (a x)) B:=by
 have hbase:q0 (fun u:Fin d₁->Bool=>yd d₂ u) 0 :=
  (q0.rewire (fun i:Fin d₂ =>
   if h:i.1< d₁ then Sum.inr ⟨i.1,h⟩ else Sum.inl false)).congr (fun u=>by
   funext i;dsimp only [yd,bq];split_ifs <;> rfl)
 exact (q0.c ha hbase).mono (by omega)
lemma pe {d₁ d₂ v:ℕ} (hv:v< 2^d₁) :
   yd d₂ (q3 d₁ v)=q3 d₂ v:=by
 funext i;dsimp only [yd,q3]
 split_ifs with h
 . rfl
 . symm;exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
lemma ji {d₁ d₂:ℕ} (a:Fin d₁->Bool) (hlt:q2 d₁ a< 2^d₂) :
  q2 d₂ (yd d₂ a)=q2 d₁ a:=by
 have h1:a=q3 d₁ (q2 d₁ a):=(qm d₁ a).symm
 conv_lhs=>rw [h1]
 rw [pe (vq d₁ a),q4 hlt]
def q5 {K d:ℕ} (v:Fin (K*d)->Bool) (i:Fin K):Fin d->Bool :=
 fun b=>v ⟨i.1*d+b.1,by
  have hi:=i.isLt;have hb:=b.isLt;have:(i.1+1)*d<=K*d:=Zw d hi
  nlinarith⟩
def qn {K d:ℕ} (f:Fin K->(Fin d->Bool)):Fin (K*d)->Bool :=
 fun p =>
  if hd:d=0 then false
  else f ⟨p.1/d,Nat.div_lt_of_lt_mul (lt_of_lt_of_eq p.isLt (Nat.mul_comm K d))⟩
   ⟨p.1 %d,Nat.mod_lt _ (by omega)⟩
lemma qb {K d:ℕ} (f:Fin K->(Fin d->Bool)) (i:Fin K) :
  q5 (qn f) i=f i:=by
 funext b;have hb:=b.isLt
 have hd:d≠0:=by omega
 simp only [q5,qn,hd,Zf]
 have hdiv:(i.1*d+b.1)/d=i.1:=by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb,Nat.zero_add]
 have hmod:(i.1*d+b.1)%d=b.1:=by
  rw [Nat.add_comm,Nat.add_mul_mod_self_right,Zm hb]
 have hcongr:∀ (i₁ i₂:Fin K) (b₁ b₂:Fin d),i₁.1=i₂.1->b₁.1=b₂.1->f i₁ b₁=f i₂ b₂:=by
  intro i₁ i₂ b₁ b₂ hi hb';rw [Zx hi,Zx hb']
 exact hcongr _ i _ b hdiv hmod
lemma qa {m K d B:ℕ} {v:(Fin m->Bool)->(Fin (K*d)->Bool)}
  (hv:q0 v B) (i:Fin K) :
  q0 (fun x=>q5 (v x) i) B:=by
 have hproj:q0 (fun u:Fin (K*d)->Bool=>q5 u i) 0 :=
  q0.p (fun b=>⟨i.1*d+b.1,by
   have hi:=i.isLt;have hb:=b.isLt;have:(i.1+1)*d<=K*d:=Zw d hi
   nlinarith⟩)
 exact (q0.c hv hproj).mono (by omega)
lemma z4 {m K d B:ℕ} (f:(Fin m->Bool)->Fin K->(Fin d->Bool))
  (hf:∀ i:Fin K,q0 (fun x=>f x i) B) :
  q0 (fun x=>qn (f x)) (K*B):=by
 induction K with
 | zero =>
  exact ((q0.k (fun _:Fin (0*d)=>false)).mono (by simp)).congr (fun x=>by
    funext p;exfalso;have:=p.isLt;simp at this)
 | succ K ih =>
  have hprev:=ih (fun x i=>f x ⟨i.1,by omega⟩) (fun i=>hf ⟨i.1,by omega⟩);have hlast:=hf ⟨K,by omega⟩;have hp:=q0.r hprev hlast
  have hrew:q0 (fun u:Fin (K*d+d)->Bool =>
      fun p:Fin ((K+1)*d)=>u ⟨p.1,lt_of_lt_of_eq p.isLt (Nat.succ_mul K d)⟩) 0 :=
    q0.p _
  refine ((q0.c hp hrew).mono (by rw [Nat.succ_mul];omega)).congr (fun x=>?_)
  funext p
  by_cases hd:d=0
  . exfalso;have:=p.isLt;simp [hd] at this
  . dsimp only [q1,qn];simp only [hd,Zf]
    by_cases hlt:p.1< K*d
    . simp only [hlt,Zd,qn,hd,Zf]
    . simp only [hlt,Zf];have hp_lt:p.1< K*d+d:=lt_of_lt_of_eq p.isLt (Nat.succ_mul K d)
      have hdiv:p.1/d=K:=by
       have h1:K<=p.1/d:=(Nat.le_div_iff_mul_le (by omega)).mpr (by omega);have h2:p.1/d< K+1:=Nat.div_lt_of_lt_mul (by nlinarith);omega
      have hmod:p.1 %d=p.1-K*d:=by
       have hdm:=Nat.div_add_mod p.1 d;rw [hdiv] at hdm;rw [Nat.mul_comm] at hdm;omega
      have hcongr:∀ (i₁ i₂:Fin (K+1)) (b₁ b₂:Fin d),i₁.1=i₂.1->b₁.1=b₂.1->f x i₁ b₁=f x i₂ b₂:=by
       intro i₁ i₂ b₁ b₂ hi hb';rw [Zx hi,Zx hb']
      exact hcongr _ _ _ _ hdiv.symm hmod.symm
def yx {K d r:ℕ} (v:Fin (K*d)->Bool) (en:Bool)
  (idx:Fin r->Bool) (val:Fin d->Bool):Fin (K*d)->Bool :=
 qn (fun j:Fin K=>zb (en&&yb idx (q3 r j.1)) (q5 v j) val)
lemma jx {K d r:ℕ} (v:Fin (K*d)->Bool) (en:Bool)
   (idx:Fin r->Bool) (val:Fin d->Bool) (hK:K<=2^r) (j:Fin K) :
   q5 (yx v en idx val) j =
   if en=true/\j.1=q2 r idx then val else q5 v j:=by
 rw [yx,qb]
 have heq_iff:yb idx (q3 r j.1)=true ↔ j.1=q2 r idx:=by
   rw [p7];constructor
   . intro h;rw [h,q4 (lt_of_lt_of_le j.isLt hK)]
   . intro h;rw [h,qm]
 cases en
 . rw [Bool.false_and,zn,if_neg (by simp)]
 . by_cases hj:j.1=q2 r idx
   . rw [heq_iff.mpr hj,Bool.true_and,zz,if_pos ⟨rfl,hj⟩]
   . have hf:yb idx (q3 r j.1)=false:=by
      cases hv:yb idx (q3 r j.1)
      . rfl
      . exact absurd (heq_iff.mp hv) hj
     rw [hf,Bool.and_false,zn,if_neg (by intro h;exact hj h.2)]
lemma pf {m K d r Bv Be Bi Bval:ℕ}
  {v:(Fin m->Bool)->(Fin (K*d)->Bool)}
  {en:(Fin m->Bool)->Bool}
  {idx:(Fin m->Bool)->(Fin r->Bool)}
  {val:(Fin m->Bool)->(Fin d->Bool)}
  (hv:q0 v Bv) (he:q0 (fun x (_:Fin 1)=>en x) Be)
  (hi:q0 idx Bi) (hval:q0 val Bval) :
  q0 (fun x=>yx (v x) (en x) (idx x) (val x))
   (Bv+Be+Bi+Bval+K*(2*r+4*d+1)):=by
 have hbase:q0 (fun u:Fin (K*d+1+r+d)->Bool =>
   yx
    (fun a:Fin (K*d)=>u ⟨a.1,by omega⟩)
    (u ⟨K*d,by omega⟩)
    (fun a:Fin r=>u ⟨K*d+1+a.1,by omega⟩)
    (fun a:Fin d=>u ⟨K*d+1+r+a.1,by omega⟩))
   (K*(2*r+4*d+1)):=by
  apply z4;intro j
  have hv0:q0 (fun u:Fin (K*d+1+r+d)->Bool =>
    q5 (fun a:Fin (K*d)=>u ⟨a.1,by omega⟩) j) 0 :=
   qa (q0.p (fun a=>⟨a.1,by omega⟩)) j
  have he0:q0 (fun (u:Fin (K*d+1+r+d)->Bool) (_:Fin 1)=>u ⟨K*d,by omega⟩) 0 :=
   q0.p (fun _=>⟨K*d,by omega⟩)
  have hi0:q0 (fun u:Fin (K*d+1+r+d)->Bool =>
    fun a:Fin r=>u ⟨K*d+1+a.1,by omega⟩) 0 :=
   q0.p (fun a=>⟨K*d+1+a.1,by omega⟩)
  have hval0:q0 (fun u:Fin (K*d+1+r+d)->Bool =>
    fun a:Fin d=>u ⟨K*d+1+r+a.1,by omega⟩) 0 :=
   q0.p (fun a=>⟨K*d+1+r+a.1,by omega⟩)
  exact (zg (q0.a he0 (xb j.1 hi0)) hv0 hval0).mono (by omega)
 have hp:=q0.r (q0.r (q0.r hv he) hi) hval
 exact ((q0.c hp hbase).mono (by omega)).congr (fun x=>by
  have h1:(fun a:Fin (K*d) =>
    q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (val x) ⟨a.1,by omega⟩)=v x:=by
   funext a;have ha:=a.isLt;simp only [q1,show a.1< K*d from ha,show a.1< K*d+1 by omega,show a.1< K*d+1+r by omega,Zd]
  have h2:q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (val x) ⟨K*d,by omega⟩=en x:=by
   simp only [q1,show K*d< K*d+1 by omega,show K*d< K*d+1+r by omega,
    show ¬ (K*d< K*d) by omega,Zd,Zf]
  have h3:(fun a:Fin r =>
    q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (val x) ⟨K*d+1+a.1,by omega⟩)=idx x:=by
   funext a;have ha:=a.isLt
   simp only [q1,show K*d+1+a.1< K*d+1+r by omega,
    show ¬ (K*d+1+a.1< K*d+1) by omega,Zd,Zf]
   congr 1;exact Zx (by dsimp;omega)
  have h4:(fun a:Fin d =>
    q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (val x) ⟨K*d+1+r+a.1,by omega⟩)=val x:=by
   funext a;simp only [q1,show ¬ (K*d+1+r+a.1< K*d+1+r) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
  rw [h1,h2,h3,h4])
def jb {K₁ K₂ d r₁ r₂:ℕ} (v:Fin ((K₁*K₂)*d)->Bool)
  (i₁:Fin r₁->Bool) (i₂:Fin r₂->Bool):Fin d->Bool :=
 if h₁:q2 r₁ i₁ < K₁ then
  if h₂:q2 r₂ i₂ < K₂ then
   q5 v ⟨q2 r₁ i₁*K₂+q2 r₂ i₂,by
    have:(q2 r₁ i₁+1)*K₂<=K₁*K₂:=Zw K₂ h₁
    nlinarith⟩
  else fun _=>false
 else fun _=>false
lemma pg {m K₁ K₂ d r₁ r₂ Bv B₁ B₂:ℕ}
  {v:(Fin m->Bool)->(Fin ((K₁*K₂)*d)->Bool)}
  {i₁:(Fin m->Bool)->(Fin r₁->Bool)}
  {i₂:(Fin m->Bool)->(Fin r₂->Bool)}
  (hK₁:K₁<=2^r₁) (hK₂:K₂<=2^r₂)
  (hv:q0 v Bv) (hi₁:q0 i₁ B₁) (hi₂:q0 i₂ B₂) :
  q0 (fun x=>jb (v x) (i₁ x) (i₂ x))
    (Bv+B₁+B₂+(K₁*K₂)*(2*r₁+2*r₂+4*d+1)):=by
 let N:=K₁*K₂
 have hbase:q0 (fun u:Fin (N*d+r₁+r₂)->Bool =>
    jb (K₁:=K₁) (K₂:=K₂)
      (fun a:Fin (N*d)=>u ⟨a.1,by omega⟩)
      (fun a:Fin r₁=>u ⟨N*d+a.1,by omega⟩)
      (fun a:Fin r₂=>u ⟨N*d+r₁+a.1,by omega⟩))
    (0+N*(2*r₁+2*r₂+4*d+1)):=by
  let step:Fin N->(Fin (N*d+r₁+r₂)->Bool)->(Fin d->Bool)->(Fin d->Bool) :=
    fun idx u acc =>
      let hit :=
        yb (fun a:Fin r₁=>u ⟨N*d+a.1,by omega⟩) (q3 r₁ (idx.1/K₂)) &&
        yb (fun a:Fin r₂=>u ⟨N*d+r₁+a.1,by omega⟩) (q3 r₂ (idx.1 %K₂))
      zb hit acc (q5 (fun a:Fin (N*d)=>u ⟨a.1,by omega⟩) idx)
  have hstep:∀ idx:Fin N,q0 (fun q:Fin ((N*d+r₁+r₂)+d)->Bool =>
      step idx (fun a=>q ⟨a.1,by omega⟩) (fun b=>q ⟨N*d+r₁+r₂+b.1,by omega⟩))
      (2*r₁+2*r₂+4*d+1):=by
    intro idx
    have hi10:q0 (fun q:Fin ((N*d+r₁+r₂)+d)->Bool =>
        fun a:Fin r₁=>q ⟨N*d+a.1,by omega⟩) 0:=q0.p _
    have hi20:q0 (fun q:Fin ((N*d+r₁+r₂)+d)->Bool =>
        fun a:Fin r₂=>q ⟨N*d+r₁+a.1,by omega⟩) 0:=q0.p _
    have hacc:q0 (fun q:Fin ((N*d+r₁+r₂)+d)->Bool =>
        fun b:Fin d=>q ⟨N*d+r₁+r₂+b.1,by omega⟩) 0:=q0.p _
    have hent:q0 (fun q:Fin ((N*d+r₁+r₂)+d)->Bool =>
        q5 (fun a:Fin (N*d)=>q ⟨a.1,by omega⟩) idx) 0 :=
      qa (q0.p _) idx
    exact (zg
      (q0.a (xb (idx.1/K₂) hi10) (xb (idx.1 %K₂) hi20))
      hacc hent).mono (by omega)
  have hf:=q0.l (fun _=>fun _=>false) step (q0.k _) hstep
  refine hf.congr (fun u=>?_)
  set vArr:Fin (N*d)->Bool:=fun a=>u ⟨a.1,by omega⟩
  set v1:=q2 r₁ (fun a:Fin r₁=>u ⟨N*d+a.1,by omega⟩);set v2:=q2 r₂ (fun a:Fin r₂=>u ⟨N*d+r₁+a.1,by omega⟩)
  have hhit_iff (idx:Fin N) :
      (yb (fun a:Fin r₁=>u ⟨N*d+a.1,by omega⟩) (q3 r₁ (idx.1/K₂)) &&
       yb (fun a:Fin r₂=>u ⟨N*d+r₁+a.1,by omega⟩) (q3 r₂ (idx.1 %K₂)))=true ↔
      v1=idx.1/K₂/\v2=idx.1 %K₂:=by
    have hK₂pos:0< K₂:=by
      by_contra h0;simp only [Nat.not_lt,Nat.le_zero] at h0
      have:=idx.isLt;simp [N,h0] at this
    have hdiv_lt:idx.1/K₂ < K₁:=Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm];exact idx.isLt);have hmod_lt:idx.1 %K₂ < K₂:=Nat.mod_lt _ hK₂pos;simp only [Bool.and_eq_true,p7];constructor
    . rintro ⟨e1,e2⟩
      refine ⟨?_,?_⟩
      . change q2 r₁ _=_;rw [e1,q4 (lt_of_lt_of_le hdiv_lt hK₁)]
      . change q2 r₂ _=_;rw [e2,q4 (lt_of_lt_of_le hmod_lt hK₂)]
    . rintro ⟨e1,e2⟩;exact ⟨by rw [<- e1,qm],by rw [<- e2,qm]⟩
  have hinv:∀ t (ht:t<=N),
      ((List.finRange N).take t).foldl (fun acc idx=>step idx u acc) (fun _=>false) =
      if h:v1< K₁/\v2< K₂/\v1*K₂+v2< t then
        q5 vArr ⟨v1*K₂+v2,by omega⟩
      else fun _=>false:=by
    intro t ht
    induction t with
    | zero=>simp
    | succ t iht =>
      have htake:(List.finRange N).take (t+1)=(List.finRange N).take t++[⟨t,by omega⟩]:=by
        rw [Zt (by simp;omega)];simp [Zg]
      rw [htake,Zl,Zo,Zi,iht (by omega)]
      set cur:Fin N:=⟨t,by omega⟩
      have hK₂pos:0< K₂:=by
        by_contra h0;simp only [Nat.not_lt,Nat.le_zero] at h0
        have:=cur.isLt;simp [N,h0] at this
      have hdiv_lt:t/K₂ < K₁:=Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm];exact cur.isLt);have hmod_lt:t %K₂ < K₂:=Nat.mod_lt _ hK₂pos;dsimp only [step]
      by_cases hcur:v1=t/K₂/\v2=t %K₂
      . rw [(hhit_iff cur).mpr hcur,zz]
        have ht_eq:v1*K₂+v2=t:=by
          rw [hcur.1,hcur.2,Nat.mul_comm];exact Nat.div_add_mod t K₂
        have hcond:v1< K₁/\v2< K₂/\v1*K₂+v2< t+1:=⟨by omega,by omega,by omega⟩;rw [Zr hcond];congr 1;exact Zx ht_eq.symm
      . have hf_hit:(yb (fun a:Fin r₁=>u ⟨N*d+a.1,by omega⟩) (q3 r₁ (t/K₂)) &&
            yb (fun a:Fin r₂=>u ⟨N*d+r₁+a.1,by omega⟩) (q3 r₂ (t %K₂)))=false:=by
          cases hv':(yb (fun a:Fin r₁=>u ⟨N*d+a.1,by omega⟩) (q3 r₁ (t/K₂)) &&
            yb (fun a:Fin r₂=>u ⟨N*d+r₁+a.1,by omega⟩) (q3 r₂ (t %K₂)))
          . rfl
          . exact absurd ((hhit_iff cur).mp hv') hcur
        rw [hf_hit,zn]
        have hne_t:v1< K₁->v2< K₂->v1*K₂+v2≠t:=by
          intro h1 h2 heq;apply hcur
          refine ⟨?_,?_⟩
          . rw [<- heq,Nat.add_comm,Nat.add_mul_div_right _ _ hK₂pos,Nat.div_eq_of_lt h2,Nat.zero_add]
          . rw [<- heq,Nat.add_comm,Nat.add_mul_mod_self_right,Zm h2]
        by_cases hprev:v1< K₁/\v2< K₂/\v1*K₂+v2< t
        . rw [Zr hprev,Zr ⟨hprev.1,hprev.2.1,by omega⟩]
        . have hnot:¬ (v1< K₁/\v2< K₂/\v1*K₂+v2< t+1):=by
            rintro ⟨h1,h2,h3⟩;have:=hne_t h1 h2;exact hprev ⟨h1,h2,by omega⟩
          rw [Zb hprev,Zb hnot]
  have hfull:=hinv N le_rfl;rw [Zk (by simp)] at hfull;rw [hfull];dsimp only [jb]
  by_cases h1:v1< K₁
  . by_cases h2:v2< K₂
    . have hltN:v1*K₂+v2< N:=by
        have:(v1+1)*K₂<=K₁*K₂:=Zw K₂ h1;dsimp [N];nlinarith
      rw [Zr ⟨h1,h2,hltN⟩,Zr h1,Zr h2]
    . rw [Zb (by tauto),Zr h1,Zb h2]
  . rw [Zb (by tauto),Zb h1]
 have hp:=q0.r (q0.r hv hi₁) hi₂
 exact ((q0.c hp hbase).mono (by dsimp [N];omega)).congr (fun x=>by
  have h1:(fun a:Fin (N*d)=>q1 (q1 (v x) (i₁ x)) (i₂ x) ⟨a.1,by dsimp [N];omega⟩)=v x:=by
    funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;dsimp [N] at this;omega),Zr (by have:=a.isLt;dsimp [N] at this;omega)]
  have h2:(fun a:Fin r₁=>q1 (q1 (v x) (i₁ x)) (i₂ x) ⟨N*d+a.1,by dsimp [N];omega⟩)=i₁ x:=by
    funext a;have ha:=a.isLt
    simp only [q1,show N*d+a.1< K₁*K₂*d+r₁ by dsimp [N];omega,
      show ¬ (N*d+a.1< K₁*K₂*d) by dsimp [N];omega,Zd,Zf]
    congr 1;exact Zx (by dsimp [N];omega)
  have h3:(fun a:Fin r₂=>q1 (q1 (v x) (i₁ x)) (i₂ x) ⟨N*d+r₁+a.1,by dsimp [N];omega⟩)=i₂ x:=by
    funext a;simp only [q1,show ¬ (N*d+r₁+a.1< K₁*K₂*d+r₁) by dsimp [N];omega,Zf];congr 1;exact Zx (by dsimp [N];omega)
  rw [h1,h2,h3])
def vm (n:ℕ) (hn:0< n) (isPin:Fin (2*n)->Bool) (i:Fin (2*n)) (L:ℕ):Bool :=
 decide (1<=L/\L<=2*n)&&isPin i&&isPin (q8 n hn i L) &&
  kv (fun r:Fin (L-1)=>!(isPin (q8 n hn i (r.1+1))))
lemma pp (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool)
   (i:Fin (2*n)) (L:ℕ) :
   vm n hn (fun k=>(p k).isSome) i L=y9 n hn p i L:=by
 unfold vm y9;congr 1
 by_cases h:kv (fun r:Fin (L-1)=>!(p (q8 n hn i (r.1+1))).isSome)=true
 . rw [h];symm;rw [List.all_eq_true];intro r hr;rw [List.mem_range] at hr;exact (jp _).mp h ⟨r,hr⟩
 . have hf:kv (fun r:Fin (L-1)=>!(p (q8 n hn i (r.1+1))).isSome)=false :=
     Bool.eq_false_iff.mpr h
   rw [hf];symm
   cases ha:(List.range (L-1)).all (fun r=>!(p (q8 n hn i (r+1))).isSome)
   . rfl
   . exfalso;apply h;rw [jp];intro r;exact (List.all_eq_true.mp ha) r.1 (List.mem_range.mpr r.isLt)
lemma b3 (n:ℕ) (hn:0< n) (i:Fin (2*n)) (L:ℕ) (hL:L<=2*n) :
  q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1) =>
   vm n hn (fun k=>u ⟨k.1,by omega⟩) i L) (4*n+3):=by
 unfold vm
 have h1:q0 (fun (_:Fin (4*n)->Bool) (_:Fin 1)=>decide (1<=L/\L<=2*n)) 0 :=
  q0.k _
 have h2:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨i.1,by omega⟩) 0 :=
  q0.p _
 have h3:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨(q8 n hn i L).1,by omega⟩) 0 :=
  q0.p _
 have h4:q0 (fun u:Fin (4*n)->Bool =>
   fun r:Fin (L-1)=>!(u ⟨(q8 n hn i (r.1+1)).1,by omega⟩)) ((L-1)*1) :=
  q0.f _ (fun r=>q0.boolNot (q0.p _))
 have h5:=kw h4;exact (q0.a (q0.a (q0.a h1 h2) h3) h5).mono (by omega)
def yj (n:ℕ) (hn:0< n) (Bc:ℕ) (L:ℕ)
  (Q:Fin (2*n)->Bool->Bool->Bool) (u:Fin (4*n)->Bool):Fin Bc->Bool :=
 (List.finRange (2*n)).foldl
  (fun acc i =>
   let isPin:Fin (2*n)->Bool:=fun k=>u ⟨k.1,by omega⟩
   let pinVal:Fin (2*n)->Bool:=fun k=>u ⟨2*n+k.1,by omega⟩
   let hit:=vm n hn isPin i L&&Q i (pinVal i) (pinVal (q8 n hn i L))
   zb hit acc (qr acc (q3 Bc 1)))
  (q3 Bc 0)
lemma ye (n:ℕ) (hn:0< n) (Bc:ℕ) (hBc:2*n< 2^Bc)
  (L:ℕ) (Q:Fin (2*n)->Bool->Bool->Bool)
  (p:Fin (2*n)->Option Bool) (junk:Fin (2*n)->Bool) :
  let u:Fin (4*n)->Bool:=fun k =>
   if h:k.1< 2*n then (p ⟨k.1,h⟩).isSome
   else (p ⟨k.1-2*n,by omega⟩).getD (junk ⟨k.1-2*n,by omega⟩)
  q2 Bc (yj n hn Bc L Q u) =
  (Finset.univ.filter (fun i:Fin (2*n) =>
   y9 n hn p i L=true /\
   Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true)).card:=by
 intro u
 have his:(fun k:Fin (2*n)=>u ⟨k.1,by omega⟩)=fun k=>(p k).isSome:=by
  funext k;simp [u,k.isLt]
 have hval:(fun k:Fin (2*n)=>u ⟨2*n+k.1,by omega⟩)=fun k=>(p k).getD (junk k):=by
  funext k;simp [u]
 have hinv:∀ t ≤ 2*n,
   q2 Bc (((List.finRange (2*n)).take t).foldl
     (fun acc i =>
      let isPin:Fin (2*n)->Bool:=fun k=>u ⟨k.1,by omega⟩
      let pinVal:Fin (2*n)->Bool:=fun k=>u ⟨2*n+k.1,by omega⟩
      let hit:=vm n hn isPin i L&&Q i (pinVal i) (pinVal (q8 n hn i L))
      zb hit acc (qr acc (q3 Bc 1)))
     (q3 Bc 0)) =
   (Finset.univ.filter (fun i:Fin (2*n) =>
     i.1< t/\y9 n hn p i L=true /\
     Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true)).card:=by
  intro t ht
  induction t with
  | zero =>
   simp [q4 (by omega:0< 2^Bc)]
  | succ t iht =>
   have htake:(List.finRange (2*n)).take (t+1)=(List.finRange (2*n)).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   set acc:=((List.finRange (2*n)).take t).foldl
     (fun acc i =>
      let isPin:Fin (2*n)->Bool:=fun k=>u ⟨k.1,by omega⟩
      let pinVal:Fin (2*n)->Bool:=fun k=>u ⟨2*n+k.1,by omega⟩
      let hit:=vm n hn isPin i L&&Q i (pinVal i) (pinVal (q8 n hn i L))
      zb hit acc (qr acc (q3 Bc 1)))
     (q3 Bc 0)
   have hacc_eq:=iht (by omega)
   have hacc_le:q2 Bc acc<=t:=by
     rw [hacc_eq]
     have hsub:Finset.univ.filter (fun i:Fin (2*n) =>
       i.1< t/\y9 n hn p i L=true /\
       Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true) ⊆
       Finset.univ.filter (fun i:Fin (2*n)=>i.1< t):=by
      intro i hi;simp only [Zv,Zu,true_and] at hi ⊢;exact hi.1
     have hcard_lt:(Finset.univ.filter (fun i:Fin (2*n)=>i.1< t)).card=t:=by
      refine (Finset.card_bij (fun i hi=>(⟨i.1,(Zv.mp hi).2⟩:Fin t))
       (fun _ _=>Zu _)
       (fun _ _ _ _ h=>Zx (by simpa using congrArg Fin.val h))
       (fun j _=>⟨⟨j.1,by omega⟩,by simp [j.isLt],Zx rfl⟩)).trans (by simp)
     exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard_lt)
   have hcard_step :
      (Finset.univ.filter (fun i:Fin (2*n) =>
       i.1< t+1/\y9 n hn p i L=true /\
       Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true)).card =
      (Finset.univ.filter (fun i:Fin (2*n) =>
       i.1< t/\y9 n hn p i L=true /\
       Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true)).card +
      if y9 n hn p ⟨t,by omega⟩ L=true /\
        Q ⟨t,by omega⟩ ((p ⟨t,by omega⟩).getD (junk ⟨t,by omega⟩))
          ((p (q8 n hn ⟨t,by omega⟩ L)).getD (junk (q8 n hn ⟨t,by omega⟩ L)))=true
      then 1 else 0:=by
     rw [Finset.card_filter,Finset.card_filter,
       <- Finset.add_sum_erase Finset.univ _ (Zu (⟨t,by omega⟩:Fin (2*n))),
       <- Finset.add_sum_erase Finset.univ (fun i:Fin (2*n) =>
         if i.1< t/\y9 n hn p i L=true /\
            Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true
         then 1 else 0) (Zu (⟨t,by omega⟩:Fin (2*n)))]
     simp only [lt_irrefl,false_and,Zj,Nat.zero_add,Nat.lt_succ_self,true_and]
     have hrest:∀ i ∈ Finset.univ.erase (⟨t,by omega⟩:Fin (2*n)),
       (if i.1< t+1/\y9 n hn p i L=true /\
           Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true
        then 1 else 0) =
       (if i.1< t/\y9 n hn p i L=true /\
           Q i ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=true
        then 1 else 0):=by
      intro i hi;rw [Finset.mem_erase] at hi
      have hne:i.1≠t:=fun h=>hi.1 (Zx h)
      have hiff:i.1< t+1 ↔ i.1< t:=by omega
      simp [hiff]
     rw [Zc rfl hrest];omega
   rw [hcard_step,<-hacc_eq];dsimp only
   have hval_k (k:Fin (2*n)):u ⟨2*n+k.1,by omega⟩=(p k).getD (junk k):=by simp [u]
   have hval_t:u ⟨2*n+t,by omega⟩=(p ⟨t,by omega⟩).getD (junk ⟨t,by omega⟩):=by simp [u]
   simp only [his,pp,hval_k,hval_t]
   by_cases hhit:y9 n hn p ⟨t,by omega⟩ L=true /\
      Q ⟨t,by omega⟩ ((p ⟨t,by omega⟩).getD (junk ⟨t,by omega⟩))
       ((p (q8 n hn ⟨t,by omega⟩ L)).getD (junk (q8 n hn ⟨t,by omega⟩ L)))=true
   . rw [if_pos hhit,show (y9 n hn p ⟨t,by omega⟩ L &&
       Q ⟨t,by omega⟩ ((p ⟨t,by omega⟩).getD (junk ⟨t,by omega⟩))
         ((p (q8 n hn ⟨t,by omega⟩ L)).getD (junk (q8 n hn ⟨t,by omega⟩ L))))=true by simp [hhit]]
     rw [zz,qr,qc,q4 (by omega:1< 2^Bc)];simp only [Zp,Zq,Zm (by omega:q2 Bc acc+1< 2^Bc)]
   . rw [if_neg hhit]
     have hf:(y9 n hn p ⟨t,by omega⟩ L &&
       Q ⟨t,by omega⟩ ((p ⟨t,by omega⟩).getD (junk ⟨t,by omega⟩))
         ((p (q8 n hn ⟨t,by omega⟩ L)).getD (junk (q8 n hn ⟨t,by omega⟩ L))))=false:=by
      cases h1:y9 n hn p ⟨t,by omega⟩ L <;>
       cases h2:Q ⟨t,by omega⟩ ((p ⟨t,by omega⟩).getD (junk ⟨t,by omega⟩))
         ((p (q8 n hn ⟨t,by omega⟩ L)).getD (junk (q8 n hn ⟨t,by omega⟩ L))) <;>
       simp_all
     rw [hf,zn,Zq]
 have hfull:=hinv (2*n) le_rfl;rw [Zk (by simp)] at hfull;rw [yj,hfull];apply congrArg Finset.card;ext i;simp [i.isLt]
lemma yo (n:ℕ) (hn:0< n) (Bc:ℕ) (L:ℕ) (hL:L<=2*n)
  (Q:Fin (2*n)->Bool->Bool->Bool)
  (hQ:∀ i:Fin (2*n),q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1) =>
   Q i (u ⟨2*n+i.1,by omega⟩) (u ⟨2*n+(q8 n hn i L).1,by omega⟩)) 6) :
  q0 (yj n hn Bc L Q) (2*n*(4*n+10+17*Bc)):=by
 have hf:=q0.l (m:=4*n) (s:=Bc) (T:=2*n) (Bs:=4*n+10+17*Bc)
  (fun _=>q3 Bc 0)
  (fun i u acc =>
   let isPin:Fin (2*n)->Bool:=fun k=>u ⟨k.1,by omega⟩
   let pinVal:Fin (2*n)->Bool:=fun k=>u ⟨2*n+k.1,by omega⟩
   let hit:=vm n hn isPin i L&&Q i (pinVal i) (pinVal (q8 n hn i L))
   zb hit acc (qr acc (q3 Bc 1)))
  (q0.k _)
  (fun i =>
   let hu:q0 (fun q:Fin (4*n+Bc)->Bool=>fun a:Fin (4*n)=>q ⟨a.1,by omega⟩) 0 :=
    q0.p _
   let hacc:q0 (fun q:Fin (4*n+Bc)->Bool=>fun b:Fin Bc=>q ⟨4*n+b.1,by omega⟩) 0 :=
    q0.p _
   let harc:=q0.c hu (b3 n hn i L hL)
   let hq:=q0.c hu (hQ i)
   let hhit:=q0.a harc hq
   let hinc:=z8 hacc (q0.k (q3 Bc 1))
   (zg hhit hacc hinc).mono (by omega))
 exact hf.mono (by omega)
def wo (n:ℕ) (hn:0< n) (Bc:ℕ) (u:Fin (4*n)->Bool) :
  Fin (6*n*Bc)->Bool :=
 qn (K:=6*n) (d:=Bc) (fun slot =>
  if h1:slot.1< 4*n then
   let o:=slot.1
   let L:=qs n o
   let c:=qh n o
   let sig:=qf o
   yj n hn Bc L (fun i b1 b2=>decide (decide (i.1 %2=1)=c)&&decide (xor b1 b2=sig)) u
  else if h2:slot.1< 5*n then
   let j:=slot.1-4*n
   yj n hn Bc (2*(j+1)) (fun _ b1 b2=>!(xor b1 b2)) u
  else
   let j:=slot.1-5*n
   yj n hn Bc (2*(j+1)) (fun _ b1 b2=>xor b1 b2) u)
lemma k0 (n:ℕ) (hn:0< n) (Bc:ℕ) :
   q0 (wo n hn Bc) (6*n*(2*n*(4*n+10+17*Bc))):=by
 apply z4;intro slot;dsimp only
 split_ifs with h1 h2
 . have hL:qs n slot.1<=2*n:=by
    have:=(qp n slot.1 h1).1;unfold qs;omega
   refine yo n hn Bc (qs n slot.1) hL _ (fun i=>?_)
   have hb1:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨2*n+i.1,by omega⟩) 0 :=
    q0.p _
   have hb2:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1) =>
      u ⟨2*n+(q8 n hn i (qs n slot.1)).1,by omega⟩) 0:=q0.p _
   have hxor:=q0.x hb1 hb2
   have hsig:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1) =>
      decide (xor (u ⟨2*n+i.1,by omega⟩) (u ⟨2*n+(q8 n hn i (qs n slot.1)).1,by omega⟩)=qf slot.1)) 5:=by
    cases qf slot.1
    . exact (q0.boolNot hxor).congr (fun u=>by funext _;cases xor _ _ <;> rfl)
    . exact (hxor.mono (by omega)).congr (fun u=>by funext _;cases xor _ _ <;> rfl)
   exact (q0.a (q0.k (fun _=>decide (decide (i.1 %2=1)=qh n slot.1))) hsig).mono (by omega)
 . have hL:2*(slot.1-4*n+1)<=2*n:=by omega
   refine yo n hn Bc (2*(slot.1-4*n+1)) hL _ (fun i=>?_)
   have hb1:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨2*n+i.1,by omega⟩) 0 :=
    q0.p _
   have hb2:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1) =>
      u ⟨2*n+(q8 n hn i (2*(slot.1-4*n+1))).1,by omega⟩) 0:=q0.p _
   exact (q0.boolNot (q0.x hb1 hb2)).mono (by omega)
 . have hL:2*(slot.1-5*n+1)<=2*n:=by have:=slot.isLt;omega
   refine yo n hn Bc (2*(slot.1-5*n+1)) hL _ (fun i=>?_)
   have hb1:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨2*n+i.1,by omega⟩) 0 :=
    q0.p _
   have hb2:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1) =>
      u ⟨2*n+(q8 n hn i (2*(slot.1-5*n+1))).1,by omega⟩) 0:=q0.p _
   exact (q0.x hb1 hb2).mono (by omega)
lemma kk (n:ℕ) (hn:0< n) (Bc:ℕ) (hBc:2*n< 2^Bc)
   (p:Fin (2*n)->Option Bool) (junk:Fin (2*n)->Bool) :
   let u:Fin (4*n)->Bool:=fun k =>
     if h:k.1< 2*n then (p ⟨k.1,h⟩).isSome
     else (p ⟨k.1-2*n,by omega⟩).getD (junk ⟨k.1-2*n,by omega⟩)
   let arr:=wo n hn Bc u
   (∀ o:Fin (4*n),
     q2 Bc (q5 arr ⟨o.1,by omega⟩) =
     z3 n hn p ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1)) /\
   (∀ j:Fin n,
     q2 Bc (q5 arr ⟨4*n+j.1,by omega⟩)=qo n hn p j) /\
   (∀ j:Fin n,
     q2 Bc (q5 arr ⟨5*n+j.1,by omega⟩)=qd n hn p j):=by
 intro u arr
 have hsign_eq (i:Fin (2*n)) (L:ℕ) (his:y9 n hn p i L=true) :
     xor ((p i).getD (junk i)) ((p (q8 n hn i L)).getD (junk (q8 n hn i L)))=zv n hn p i L:=by
   have h:=(y3 n hn p i L).mp his
   cases h1:p i with
   | none=>rw [h1] at h;simp at h
   | some b1 =>
     cases h2:p (q8 n hn i L) with
     | none=>rw [h2] at h;simp at h
     | some b2 =>
      simp only [Option.getD_some,zv,h1,h2]
      cases b1 <;> cases b2 <;> decide
 refine ⟨?_,?_,?_⟩
 . intro o;dsimp only [arr,wo];rw [qb,Zr o.isLt];rw [ye n hn Bc hBc _ _ p junk];unfold z3 qs;apply congrArg Finset.card;ext i;simp only [Zv,Zu,true_and,Bool.and_eq_true,decide_eq_true_eq];constructor
   . rintro ⟨his,hc,hs⟩;rw [hsign_eq i _ his] at hs;exact ⟨his,hc,hs⟩
   . rintro ⟨his,hc,hs⟩;rw [<- hsign_eq i _ his] at hs;exact ⟨his,hc,hs⟩
 . intro j;have hj:=j.isLt;dsimp only [arr,wo];rw [qb,Zb (by dsimp;omega),Zr (by dsimp;omega)]
   have hsub:4*n+j.1-4*n=j.1:=by omega
   rw [hsub,ye n hn Bc hBc _ _ p junk];unfold qo;apply congrArg Finset.card;ext i;simp only [Zv,Zu,true_and];constructor
   . rintro ⟨his,hs⟩;rw [hsign_eq i _ his] at hs;exact ⟨his,by cases h:zv n hn p i (2*(j.1+1)) <;> simp [h] at hs ⊢⟩
   . rintro ⟨his,hs⟩;exact ⟨his,by rw [hsign_eq i _ his,hs];rfl⟩
 . intro j;have hj:=j.isLt;dsimp only [arr,wo];rw [qb,Zb (by dsimp;omega),Zb (by dsimp;omega)]
   have hsub:5*n+j.1-5*n=j.1:=by omega
   rw [hsub,ye n hn Bc hBc _ _ p junk];unfold qd;apply congrArg Finset.card;ext i;simp only [Zv,Zu,true_and];constructor
   . rintro ⟨his,hs⟩;rw [hsign_eq i _ his] at hs;exact ⟨his,hs⟩
   . rintro ⟨his,hs⟩;exact ⟨his,by rw [hsign_eq i _ his,hs]⟩
def w4 (n Bc:ℕ) (m:Fin n) (st:Fin ((2*n+1)*Bc)->Bool) :
  Fin ((2*n+1)*Bc)->Bool :=
 let epM:=q5 (K:=2*n+1) (d:=Bc) st ⟨m.1,by omega⟩
 let emM:=q5 (K:=2*n+1) (d:=Bc) st ⟨n+m.1,by omega⟩
 let fus:=q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩
 let pr:=ym epM emM
 qn (K:=2*n+1) (d:=Bc) (fun slot =>
  if slot.1=m.1 then zm epM pr
  else if slot.1=n+m.1 then zm emM pr
  else if slot.1=2*n then qr fus pr
  else if n<=slot.1/\slot.1< 2*n/\(slot.1-n+1)=2*(m.1+1) then
   qr (q5 (K:=2*n+1) (d:=Bc) st slot) pr
  else q5 (K:=2*n+1) (d:=Bc) st slot)
def vw (n Bc:ℕ) (st0:Fin ((2*n+1)*Bc)->Bool) :
  Fin ((2*n+1)*Bc)->Bool :=
 (List.finRange n).foldl (fun st m=>w4 n Bc m st) st0
lemma jy (n Bc:ℕ) (m:Fin n) :
   q0 (w4 n Bc m) (70*Bc):=by
 have hepM:q0 (fun st:Fin ((2*n+1)*Bc)->Bool=>q5 (K:=2*n+1) (d:=Bc) st ⟨m.1,by omega⟩) 0 :=
   qa (q0.id _) _
 have hemM:q0 (fun st:Fin ((2*n+1)*Bc)->Bool=>q5 (K:=2*n+1) (d:=Bc) st ⟨n+m.1,by omega⟩) 0 :=
   qa (q0.id _) _
 have hfus:q0 (fun st:Fin ((2*n+1)*Bc)->Bool=>q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩) 0 :=
   qa (q0.id _) _
 have hpr:q0 (fun st:Fin ((2*n+1)*Bc)->Bool =>
     ym (q5 (K:=2*n+1) (d:=Bc) st ⟨m.1,by omega⟩)
           (q5 (K:=2*n+1) (d:=Bc) st ⟨n+m.1,by omega⟩)) (14*Bc) :=
   (ky hepM hemM).mono (by omega)
 have hst_pr:=q0.r (q0.id ((2*n+1)*Bc)) hpr
 have hbase:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool =>
     let st:Fin ((2*n+1)*Bc)->Bool:=fun a=>u ⟨a.1,by omega⟩
     let pr:Fin Bc->Bool:=fun b=>u ⟨(2*n+1)*Bc+b.1,by omega⟩
     let v1:=zm (q5 (K:=2*n+1) (d:=Bc) st ⟨m.1,by omega⟩) pr
     let v2:=zm (q5 (K:=2*n+1) (d:=Bc) st ⟨n+m.1,by omega⟩) pr
     let v3:=qr (q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩) pr
     let v4:=if h2:2*(m.1+1)<=n then
       qr (q5 (K:=2*n+1) (d:=Bc) st ⟨n+(2*(m.1+1)-1),by omega⟩) pr
     else fun _=>false
     q1 (q1 (q1 (q1 st v1) v2) v3) v4) (56*Bc):=by
   have hst0:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool=>fun a:Fin ((2*n+1)*Bc)=>u ⟨a.1,by omega⟩) 0 :=
     q0.p _
   have hpr0:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool=>fun b:Fin Bc=>u ⟨(2*n+1)*Bc+b.1,by omega⟩) 0 :=
     q0.p _
   have hv1:=wx (qa hst0 ⟨m.1,by omega⟩) hpr0;have hv2:=wx (qa hst0 ⟨n+m.1,by omega⟩) hpr0;have hv3:=z8 (qa hst0 ⟨2*n,by omega⟩) hpr0
   have hv4:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool =>
       if h2:2*(m.1+1)<=n then
         qr (q5 (K:=2*n+1) (d:=Bc) (fun a=>u ⟨a.1,by omega⟩) ⟨n+(2*(m.1+1)-1),by omega⟩)
            (fun b=>u ⟨(2*n+1)*Bc+b.1,by omega⟩)
       else fun _=>false) (13*Bc):=by
     by_cases h2:2*(m.1+1)<=n
     . simp only [h2,Zd];exact (z8 (qa hst0 ⟨n+(2*(m.1+1)-1),by omega⟩) hpr0).mono (by omega)
     . simp only [h2,Zf];exact (q0.k _).mono (by omega)
   exact (q0.r (q0.r (q0.r (q0.r hst0 hv1) hv2) hv3) hv4).mono (by omega)
 have hasm:q0 (fun q:Fin ((((2*n+1)*Bc+Bc)+Bc)+Bc+Bc)->Bool =>
     qn (K:=2*n+1) (d:=Bc) (fun slot =>
       if slot.1=m.1 then fun b=>q ⟨(2*n+1)*Bc+b.1,by omega⟩
       else if slot.1=n+m.1 then fun b=>q ⟨(2*n+1)*Bc+Bc+b.1,by omega⟩
       else if slot.1=2*n then fun b=>q ⟨(2*n+1)*Bc+Bc+Bc+b.1,by omega⟩
       else if n<=slot.1/\slot.1< 2*n/\(slot.1-n+1)=2*(m.1+1) then
         fun b=>q ⟨(2*n+1)*Bc+Bc+Bc+Bc+b.1,by omega⟩
       else q5 (K:=2*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) slot)) 0:=by
   refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
   split_ifs
   . exact q0.p _
   . exact q0.p _
   . exact q0.p _
   . exact q0.p _
   . exact qa (q0.p _) slot
 refine ((q0.c (q0.c hst_pr hbase) hasm).mono (by omega)).congr (fun st=>?_)
 dsimp only [w4];congr 1;funext slot
 have hget_st (s:Fin (2*n+1)) :
     q5 (K:=2*n+1) (d:=Bc)
       (fun a=>q1 st (ym (q5 (K:=2*n+1) (d:=Bc) st ⟨m.1,by omega⟩)
         (q5 (K:=2*n+1) (d:=Bc) st ⟨n+m.1,by omega⟩)) ⟨a.1,by omega⟩) s=q5 st s:=by
   funext b;simp [q5,q1,show s.1*Bc+b.1< (2*n+1)*Bc by
     have hs:=s.isLt;have hb:=b.isLt;have:(s.1+1)*Bc<=(2*n+1)*Bc:=Zw Bc hs;nlinarith]
 have hget_pr:(fun b:Fin Bc=>q1 st (ym
     (q5 (K:=2*n+1) (d:=Bc) st ⟨m.1,by omega⟩)
     (q5 (K:=2*n+1) (d:=Bc) st ⟨n+m.1,by omega⟩)) ⟨(2*n+1)*Bc+b.1,by omega⟩) =
     ym (q5 st ⟨m.1,by omega⟩) (q5 st ⟨n+m.1,by omega⟩):=by
   funext b;simp [q1]
 dsimp only [q1] at hget_st hget_pr
 by_cases h1:slot.1=m.1
 . simp only [h1,Zh];funext b;have hb:=b.isLt;dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zr (by omega),Zb (by omega)];rw [hget_st,hget_pr];congr 1;exact Zx (by dsimp;omega)
 . simp only [h1,Zj]
   by_cases h2:slot.1=n+m.1
   . simp only [h2,Zh];funext b;have hb:=b.isLt;dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zb (by omega)];rw [hget_st,hget_pr];congr 1;exact Zx (by dsimp;omega)
   . simp only [h2,Zj]
     by_cases h3:slot.1=2*n
     . simp only [h3,Zh];funext b;have hb:=b.isLt;dsimp only [q1];rw [Zr (by omega),Zb (by omega)];rw [hget_st,hget_pr];congr 1;exact Zx (by dsimp;omega)
     . simp only [h3,Zj]
       by_cases h4:n<=slot.1/\slot.1< 2*n/\(slot.1-n+1)=2*(m.1+1)
       . simp only [h4,and_self,Zh]
         have h2m:2*(m.1+1)<=n:=by omega
         have hslot_eq:slot=⟨n+(2*(m.1+1)-1),by omega⟩:=Zx (by dsimp;omega)
         have ha:q5 (K:=2*n+1) (d:=Bc) st ⟨n+(2*(m.1+1)-1),by omega⟩=q5 st slot :=
          congrArg (q5 st) hslot_eq.symm
         funext b;have hb:=b.isLt;dsimp only [q1];rw [Zb (by omega),Zr h2m,hget_st,hget_pr,ha];congr 1;exact Zx (by dsimp;omega)
       . simp only [h4,Zj];funext b
         have hlt:slot.1*Bc+b.1< (2*n+1)*Bc:=by
          have hs:=slot.isLt;have hb:=b.isLt;have:(slot.1+1)*Bc<=(2*n+1)*Bc:=Zw Bc hs;nlinarith
         dsimp only [q5,q1];rw [Zr (by omega),Zr (by omega),Zr (by omega),Zr hlt];exact congrFun (hget_st slot) b
lemma kl (n Bc:ℕ) :
  q0 (vw n Bc) (n*(70*Bc)):=by
 have hf:=q0.l (m:=(2*n+1)*Bc) (s:=(2*n+1)*Bc) (T:=n) (Bs:=70*Bc)
  (fun st0=>st0)
  (fun m _ st=>w4 n Bc m st)
  (q0.id _)
  (fun m =>
   let hst:q0 (fun q:Fin ((2*n+1)*Bc+(2*n+1)*Bc)->Bool =>
    fun b:Fin ((2*n+1)*Bc)=>q ⟨(2*n+1)*Bc+b.1,by omega⟩) 0:=q0.p _
   (q0.c hst (jy n Bc m)).mono (by omega))
 exact hf.mono (by omega)
lemma ph (n Bc:ℕ) (hBc:4*n< 2^Bc)
  (ep em:Fin n->ℕ)
  (hlen:∑ j:Fin n,2*(j.1+1)*(ep j+em j)<=2*n)
  (st0:Fin ((2*n+1)*Bc)->Bool)
  (hep0:∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) st0 ⟨j.1,by omega⟩)=ep j)
  (hem0:∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) st0 ⟨n+j.1,by omega⟩)=em j)
  (hfus0:q2 Bc (q5 (K:=2*n+1) (d:=Bc) st0 ⟨2*n,by omega⟩)=0) :
  let resC:=vw n Bc st0
  let res:=z0 n ep em
  (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) resC ⟨j.1,by omega⟩)=res.1 j) /\
  (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) resC ⟨n+j.1,by omega⟩)=res.2.1 j) /\
  q2 Bc (q5 (K:=2*n+1) (d:=Bc) resC ⟨2*n,by omega⟩)=res.2.2:=by
 have hcnt_le (a b:Fin n->ℕ) (hl:∑ j:Fin n,2*(j.1+1)*(a j+b j)<=2*n) :
   ∑ j:Fin n,(a j+b j)<=n:=by
  have h2:2*∑ j:Fin n,(a j+b j)<=∑ j:Fin n,2*(j.1+1)*(a j+b j):=by
   rw [Finset.mul_sum];apply Finset.sum_le_sum;intro j _;nlinarith
  omega
 have hinv:∀ k ≤ n,
   let stC:=((List.finRange n).take k).foldl (fun st m=>w4 n Bc m st) st0
   let st:=((List.finRange n).take k).foldl (fun st m=>we n m st) (ep,em,0)
   (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) stC ⟨j.1,by omega⟩)=st.1 j) /\
   (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) stC ⟨n+j.1,by omega⟩)=st.2.1 j) /\
   q2 Bc (q5 (K:=2*n+1) (d:=Bc) stC ⟨2*n,by omega⟩)=st.2.2 /\
   (∑ j:Fin n,2*(j.1+1)*(st.1 j+st.2.1 j))=(∑ j:Fin n,2*(j.1+1)*(ep j+em j)) /\
   (∑ j:Fin n,(st.1 j+st.2.1 j))+st.2.2=∑ j:Fin n,(ep j+em j):=by
  intro k hk
  induction k with
  | zero=>exact ⟨hep0,hem0,hfus0,rfl,by simp⟩
  | succ k ihk =>
   have htake:(List.finRange n).take (k+1)=(List.finRange n).take k++[⟨k,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi,
       Zl,Zo,Zi]
   set stC:=((List.finRange n).take k).foldl (fun st m=>w4 n Bc m st) st0;set st:=((List.finRange n).take k).foldl (fun st m=>we n m st) (ep,em,0)
   rcases ihk (by omega) with ⟨ih1,ih2,ih3,ihlen,ihcnt⟩
   set m:Fin n:=⟨k,by omega⟩
   have hpr_val:q2 Bc (ym (q5 (K:=2*n+1) (d:=Bc) stC ⟨m.1,by omega⟩)
       (q5 (K:=2*n+1) (d:=Bc) stC ⟨n+m.1,by omega⟩))=min (st.1 m) (st.2.1 m):=by
     rw [v0,ih1 m,ih2 m]
   have hsum_le:∑ j:Fin n,(ep j+em j)<=n:=hcnt_le ep em hlen
   have hst_j_le (j:Fin n):st.1 j+st.2.1 j<=n:=by
     have:=Finset.single_le_sum (f:=fun j:Fin n=>st.1 j+st.2.1 j) (fun _ _=>Nat.zero_le _) (Zu j);omega
   have hstep:=jt n (fun _ _ _=>0) m st.1 st.2.1 st.2.2 (by omega)
   refine ⟨?_,?_,?_,hstep.2.2.2.1.trans ihlen,hstep.2.2.2.2.2.1.trans ihcnt⟩
   . intro j;dsimp only [w4,we];rw [qb]
     by_cases hjm:j=m
     . subst hjm;simp only [Zh];rw [wj _ _ (by rw [ih1 m,hpr_val];exact Nat.min_le_left _ _),ih1 m,hpr_val]
     . have hne:j.1≠m.1:=fun h=>hjm (Zx h)
       simp only [hne,show j.1≠n+m.1 by omega,show j.1≠2*n by omega,
         show ¬ (n<=j.1/\j.1< 2*n/\j.1-n+1=2*(m.1+1)) by omega,
         Zj,hjm]
       exact ih1 j
   . intro j;dsimp only [w4,we];rw [qb]
     by_cases hjm:j=m
     . subst hjm;simp only [show n+m.1≠m.1 by omega,Zj,Zh];rw [wj _ _ (by rw [ih2 m,hpr_val];exact Nat.min_le_right _ _),ih2 m,hpr_val]
     . have hne:j.1≠m.1:=fun h=>hjm (Zx h)
       by_cases h2m:j.1+1=2*(m.1+1)
       . simp only [show n+j.1≠m.1 by omega,show n+j.1≠n+m.1 by omega,
          show n+j.1≠2*n by omega,Zj,
          show n<=n+j.1/\n+j.1< 2*n/\n+j.1-n+1=2*(m.1+1) by omega,
          and_self,Zh,hjm,h2m]
         rw [qr,qc,ih2 j,hpr_val]
         have hlt:st.2.1 j+min (st.1 m) (st.2.1 m)< 2^Bc:=by
          have h1:=hst_j_le j;have h2:=hst_j_le m;omega
         simp [Zm hlt]
       . simp only [show n+j.1≠m.1 by omega,show n+j.1≠n+m.1 by omega,
          show n+j.1≠2*n by omega,
          show ¬ (n<=n+j.1/\n+j.1< 2*n/\n+j.1-n+1=2*(m.1+1)) by omega,
          Zj,hjm,h2m]
         exact ih2 j
   . dsimp only [w4,we];rw [qb];simp only [show 2*n≠m.1 by omega,show 2*n≠n+m.1 by omega,Zj,Zh];rw [qr,qc,ih3,hpr_val]
     have hlt:st.2.2+min (st.1 m) (st.2.1 m)< 2^Bc:=by
       have:=hst_j_le m;omega
     simp [Zm hlt]
 have hfull:=hinv n le_rfl;rw [Zk (by simp)] at hfull;exact ⟨hfull.1,hfull.2.1,hfull.2.2.1⟩
def qu (Bc M C:ℕ) (base cnt:Fin Bc->Bool):Fin Bc->Bool :=
 (List.finRange M).foldl
  (fun acc k=>zb (wi (q3 Bc k.1) cnt) acc (qr acc (q3 Bc C)))
  base
lemma wa {m Bc M C B₁ B₂:ℕ}
  {base cnt:(Fin m->Bool)->(Fin Bc->Bool)}
  (hb:q0 base B₁) (hc:q0 cnt B₂) :
  q0 (fun x=>qu Bc M C (base x) (cnt x)) (B₁+B₂+M*(27*Bc)):=by
 have hbase:q0 (fun u:Fin (Bc+Bc)->Bool =>
   qu Bc M C (fun i=>u ⟨i.1,by omega⟩) (fun i=>u ⟨Bc+i.1,by omega⟩))
   (0+M*(27*Bc)):=by
  refine q0.l
   (fun u=>fun i:Fin Bc=>u ⟨i.1,by omega⟩)
   (fun k u acc=>zb (wi (q3 Bc k.1) (fun i=>u ⟨Bc+i.1,by omega⟩))
    acc (qr acc (q3 Bc C)))
   (q0.p _)
   (fun k =>
    let hcnt:q0 (fun q:Fin ((Bc+Bc)+Bc)->Bool=>fun i:Fin Bc=>q ⟨Bc+i.1,by omega⟩) 0:=q0.p _
    let hacc:q0 (fun q:Fin ((Bc+Bc)+Bc)->Bool=>fun i:Fin Bc=>q ⟨Bc+Bc+i.1,by omega⟩) 0:=q0.p _
    (zg (xo (q0.k _) hcnt) hacc (z8 hacc (q0.k _))).mono (by omega))
 exact ((q0.c (q0.r hb hc) hbase).mono (by omega)).congr (fun x=>by
  have h1:(fun i:Fin Bc=>q1 (base x) (cnt x) ⟨i.1,by omega⟩)=base x:=by
   funext i;exact kf _ _ i
  have h2:(fun i:Fin Bc=>q1 (base x) (cnt x) ⟨Bc+i.1,by omega⟩)=cnt x:=by
   funext i;exact k8 _ _ i
  rw [h1,h2])
lemma w0 (Bc M C:ℕ) (base cnt:Fin Bc->Bool)
  (hM:M<=2^Bc) (hcnt:q2 Bc cnt<=M)
  (hlt:q2 Bc base+q2 Bc cnt*C< 2^Bc) :
  q2 Bc (qu Bc M C base cnt)=q2 Bc base+q2 Bc cnt*C:=by
 have hinv:∀ t ≤ M,
   q2 Bc (((List.finRange M).take t).foldl
     (fun acc k=>zb (wi (q3 Bc k.1) cnt) acc (qr acc (q3 Bc C))) base) =
   q2 Bc base+min t (q2 Bc cnt)*C:=by
  intro t ht
  induction t with
  | zero=>simp
  | succ t iht =>
   have htake:(List.finRange M).take (t+1)=(List.finRange M).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   set acc:=((List.finRange M).take t).foldl
     (fun acc k=>zb (wi (q3 Bc k.1) cnt) acc (qr acc (q3 Bc C))) base
   have hacc:=iht (by omega);rw [x8,q4 (by omega:t< 2^Bc)]
   by_cases hlt':t< q2 Bc cnt
   . rw [decide_eq_true hlt',zz,qr,qc,hacc]
     have hC_lt:C< 2^Bc:=by
      have:1<=q2 Bc cnt:=by omega
      nlinarith
     rw [q4 hC_lt]
     have hmin1:min t (q2 Bc cnt)=t:=Nat.min_eq_left (by omega)
     have hmin2:min (t+1) (q2 Bc cnt)=t+1:=Nat.min_eq_left (by omega)
     rw [hmin1,hmin2]
     have hsum_lt:q2 Bc base+t*C+C< 2^Bc:=by nlinarith
     simp only [Zp,Zq,Zm hsum_lt];ring
   . rw [decide_eq_false hlt',zn,hacc];rw [Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
 have hfull:=hinv M le_rfl;rw [Zk (by simp),Nat.min_eq_right hcnt] at hfull;exact hfull
def y8 {K K₁ K₂ Bc w:ℕ}
  (W:Fin K->Fin K₁->Fin K₂->Bool->ℕ)
  (i₁ i₂:Fin Bc->Bool) (p:Bool) (cnt:Fin Bc->Bool) (acc:Fin w->Bool):Fin w->Bool :=
 (List.finRange K).foldl
  (fun cur k =>
   let wk:=w3 (fun a b par=>q3 w (W k a b par)) i₁ i₂ p
   zb (wi (q3 Bc k.1) cnt) cur (qr cur wk))
  acc
lemma vz {m K K₁ K₂ Bc w B₁ B₂ Bp Bcnt Bacc:ℕ}
  (W:Fin K->Fin K₁->Fin K₂->Bool->ℕ)
  (hK₁:K₁<=2^Bc) (hK₂:K₂<=2^Bc)
  {i₁ i₂ cnt:(Fin m->Bool)->(Fin Bc->Bool)}
  {p:(Fin m->Bool)->Bool}
  {acc:(Fin m->Bool)->(Fin w->Bool)}
  (hi₁:q0 i₁ B₁) (hi₂:q0 i₂ B₂)
  (hp:q0 (fun x (_:Fin 1)=>p x) Bp)
  (hcnt:q0 cnt Bcnt) (hacc:q0 acc Bacc) :
  q0 (fun x=>y8 W (i₁ x) (i₂ x) (p x) (cnt x) (acc x))
   (B₁+B₂+Bp+Bcnt+Bacc+K*((K₁*K₂*2)*(4*Bc+4*w+4)+10*Bc+17*w)):=by
 let M:=Bc+Bc+1+Bc+w
 have hbase:q0 (fun u:Fin M->Bool =>
   y8 W
    (fun a:Fin Bc=>u ⟨a.1,by omega⟩)
    (fun a:Fin Bc=>u ⟨Bc+a.1,by omega⟩)
    (u ⟨Bc+Bc,by omega⟩)
    (fun a:Fin Bc=>u ⟨Bc+Bc+1+a.1,by omega⟩)
    (fun a:Fin w=>u ⟨Bc+Bc+1+Bc+a.1,by omega⟩))
   (0+K*((K₁*K₂*2)*(4*Bc+4*w+4)+10*Bc+17*w)):=by
  refine q0.l
   (fun u=>fun a:Fin w=>u ⟨Bc+Bc+1+Bc+a.1,by omega⟩)
   (fun k u cur =>
    let wk:=w3 (fun a b par=>q3 w (W k a b par))
     (fun a:Fin Bc=>u ⟨a.1,by omega⟩)
     (fun a:Fin Bc=>u ⟨Bc+a.1,by omega⟩)
     (u ⟨Bc+Bc,by omega⟩)
    zb (wi (q3 Bc k.1) (fun a:Fin Bc=>u ⟨Bc+Bc+1+a.1,by omega⟩))
     cur (qr cur wk))
   (q0.p _)
   (fun k =>
    let hi10:q0 (fun q:Fin (M+w)->Bool=>fun a:Fin Bc=>q ⟨a.1,by omega⟩) 0:=q0.p _
    let hi20:q0 (fun q:Fin (M+w)->Bool=>fun a:Fin Bc=>q ⟨Bc+a.1,by omega⟩) 0:=q0.p _
    let hp0:q0 (fun (q:Fin (M+w)->Bool) (_:Fin 1)=>q ⟨Bc+Bc,by omega⟩) 0:=q0.p _
    let hcnt0:q0 (fun q:Fin (M+w)->Bool=>fun a:Fin Bc=>q ⟨Bc+Bc+1+a.1,by omega⟩) 0:=q0.p _
    let hcur0:q0 (fun q:Fin (M+w)->Bool=>fun a:Fin w=>q ⟨M+a.1,by omega⟩) 0:=q0.p _
    let hwk:=j8 (fun a b par=>q3 w (W k a b par)) hK₁ hK₂ hi10 hi20 hp0
    let hlt:=xo (q0.k (q3 Bc k.1)) hcnt0
    let hadd:=z8 hcur0 hwk
    (zg hlt hcur0 hadd).mono (by ring_nf;omega))
 have hpall:=q0.r (q0.r (q0.r (q0.r hi₁ hi₂) hp) hcnt) hacc
 exact ((q0.c hpall hbase).mono (by omega)).congr (fun x=>by
  have h1:(fun a:Fin Bc=>q1 (q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (cnt x)) (acc x) ⟨a.1,by omega⟩)=i₁ x:=by
   funext a;have ha:=a.isLt;simp [q1,show a.1< Bc from ha,show a.1< Bc+Bc by omega,show a.1< Bc+Bc+1 by omega,show a.1< Bc+Bc+1+Bc by omega]
  have h2:(fun a:Fin Bc=>q1 (q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (cnt x)) (acc x) ⟨Bc+a.1,by omega⟩)=i₂ x:=by
   funext a;have ha:=a.isLt;simp [q1,show Bc+a.1< Bc+Bc by omega,show Bc+a.1< Bc+Bc+1 by omega,show Bc+a.1< Bc+Bc+1+Bc by omega]
  have h3:q1 (q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (cnt x)) (acc x) ⟨Bc+Bc,by omega⟩=p x:=by
   simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show Bc+Bc< Bc+Bc+1+Bc by omega,
    show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
  have h4:(fun a:Fin Bc=>q1 (q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (cnt x)) (acc x) ⟨Bc+Bc+1+a.1,by omega⟩)=cnt x:=by
   funext a;have ha:=a.isLt
   simp only [q1,show Bc+Bc+1+a.1< Bc+Bc+1+Bc by omega,
    show ¬ (Bc+Bc+1+a.1< Bc+Bc+1) by omega,Zd,Zf]
   congr 1;exact Zx (by dsimp;omega)
  have h5:(fun a:Fin w=>q1 (q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (cnt x)) (acc x) ⟨Bc+Bc+1+Bc+a.1,by omega⟩)=acc x:=by
   funext a;simp only [q1,show ¬ (Bc+Bc+1+Bc+a.1< Bc+Bc+1+Bc) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
  rw [h1,h2,h3,h4,h5])
lemma vn {K K₁ K₂ Bc w:ℕ}
  (W:Fin K->Fin K₁->Fin K₂->Bool->ℕ)
  (i₁ i₂:Fin Bc->Bool) (p:Bool) (cnt:Fin Bc->Bool) (acc:Fin w->Bool)
  (hK:K<=2^Bc) (h₁:q2 Bc i₁ < K₁) (h₂:q2 Bc i₂ < K₂)
  (hcnt:q2 Bc cnt<=K)
  (wFn:ℕ->ℕ)
  (hwFn:∀ k (hk:k< K),wFn k=W ⟨k,hk⟩ ⟨q2 Bc i₁,h₁⟩ ⟨q2 Bc i₂,h₂⟩ p)
  (hlt:q2 w acc+ql wFn (q2 Bc cnt)< 2^w) :
  q2 w (y8 W i₁ i₂ p cnt acc) =
  q2 w acc+ql wFn (q2 Bc cnt):=by
 have hinv:∀ t ≤ K,
   q2 w (((List.finRange K).take t).foldl
     (fun cur k =>
      let wk:=w3 (fun a b par=>q3 w (W k a b par)) i₁ i₂ p
      zb (wi (q3 Bc k.1) cnt) cur (qr cur wk)) acc) =
   q2 w acc+ql wFn (min t (q2 Bc cnt)):=by
  intro t ht
  induction t with
  | zero=>simp [ql]
  | succ t iht =>
   have htake:(List.finRange K).take (t+1)=(List.finRange K).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   set cur:=((List.finRange K).take t).foldl
     (fun cur k =>
      let wk:=w3 (fun a b par=>q3 w (W k a b par)) i₁ i₂ p
      zb (wi (q3 Bc k.1) cnt) cur (qr cur wk)) acc
   have hcur:=iht (by omega);dsimp only;rw [x8,q4 (by omega:t< 2^Bc)]
   by_cases hlt':t< q2 Bc cnt
   . rw [decide_eq_true hlt',zz,qr,qc,hcur]
     have hlu:w3 (fun a b par=>q3 w (W ⟨t,by omega⟩ a b par)) i₁ i₂ p =
       q3 w (wFn t):=by
      simp only [w3,h₁,h₂,Zd,hwFn t (by omega)]
     rw [hlu];have hpm:=xg wFn (show t+1<=q2 Bc cnt by omega);rw [wf] at hpm
     have hw_lt:wFn t< 2^w:=by omega
     rw [q4 hw_lt];rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega),wf];simp only [Zp,Zq,Zm (by omega:q2 w acc+ql wFn t+wFn t< 2^w)];omega
   . rw [decide_eq_false hlt',zn,hcur];rw [Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
 have hfull:=hinv K le_rfl;rw [Zk (by simp),Nat.min_eq_right hcnt] at hfull;exact hfull
def zk {K K₁ K₂ Bc w:ℕ}
  (W:Fin (K+1)->Fin K₁->Fin K₂->Bool->ℕ)
  (i₁ i₂:Fin Bc->Bool) (p:Bool) (r:Fin w->Bool):Fin (1+Bc+w)->Bool :=
 (List.finRange (K+1)).foldl
  (fun st k =>
   let found:=st ⟨0,by omega⟩
   let ch:Fin Bc->Bool:=fun j=>st ⟨1+j.1,by omega⟩
   let rem:Fin w->Bool:=fun j=>st ⟨1+Bc+j.1,by omega⟩
   let wk:=w3 (fun a b par=>q3 w (W k a b par)) i₁ i₂ p
   let isLt:=wi rem wk
   let take:=!found&&isLt
   let adv:=!found&&!isLt
   q1 (q1 (fun _:Fin 1=>found||take)
    (zb take ch (q3 Bc k.1)))
    (zb adv rem (zm rem wk)))
  (q1 (q1 (fun _:Fin 1=>false) (q3 Bc 0)) r)
lemma v5 {m K K₁ K₂ Bc w B₁ B₂ Bp Br:ℕ}
  (W:Fin (K+1)->Fin K₁->Fin K₂->Bool->ℕ)
  (hK₁:K₁<=2^Bc) (hK₂:K₂<=2^Bc)
  {i₁ i₂:(Fin m->Bool)->(Fin Bc->Bool)}
  {p:(Fin m->Bool)->Bool}
  {r:(Fin m->Bool)->(Fin w->Bool)}
  (hi₁:q0 i₁ B₁) (hi₂:q0 i₂ B₂)
  (hp:q0 (fun x (_:Fin 1)=>p x) Bp) (hr:q0 r Br) :
  q0 (fun x=>zk W (i₁ x) (i₂ x) (p x) (r x))
   (B₁+B₂+Bp+Br+(K+1)*((K₁*K₂*2)*(4*Bc+4*w+4)+4*Bc+28*w+10)):=by
 let M:=Bc+Bc+1+w
 let S:=1+Bc+w
 have hbase:q0 (fun u:Fin M->Bool =>
   zk W
    (fun a:Fin Bc=>u ⟨a.1,by omega⟩)
    (fun a:Fin Bc=>u ⟨Bc+a.1,by omega⟩)
    (u ⟨Bc+Bc,by omega⟩)
    (fun a:Fin w=>u ⟨Bc+Bc+1+a.1,by omega⟩))
   (0+(K+1)*((K₁*K₂*2)*(4*Bc+4*w+4)+4*Bc+28*w+10)):=by
  refine q0.l
   (fun u=>q1 (q1 (fun _:Fin 1=>false) (q3 Bc 0))
    (fun a:Fin w=>u ⟨Bc+Bc+1+a.1,by omega⟩))
   (fun k u st =>
    let found:=st ⟨0,by omega⟩
    let ch:Fin Bc->Bool:=fun j=>st ⟨1+j.1,by omega⟩
    let rem:Fin w->Bool:=fun j=>st ⟨1+Bc+j.1,by omega⟩
    let wk:=w3 (fun a b par=>q3 w (W k a b par))
     (fun a:Fin Bc=>u ⟨a.1,by omega⟩)
     (fun a:Fin Bc=>u ⟨Bc+a.1,by omega⟩)
     (u ⟨Bc+Bc,by omega⟩)
    let isLt:=wi rem wk
    let take:=!found&&isLt
    let adv:=!found&&!isLt
    q1 (q1 (fun _:Fin 1=>found||take)
     (zb take ch (q3 Bc k.1)))
     (zb adv rem (zm rem wk)))
   ((q0.r (q0.r (q0.k (fun _:Fin 1=>false)) (q0.k (q3 Bc 0)))
    (q0.p (fun a:Fin w=>⟨Bc+Bc+1+a.1,by dsimp [M];omega⟩))).mono (by omega:0+0+0<=0))
   (fun k =>
    let hi10:q0 (fun q:Fin (M+S)->Bool=>fun a:Fin Bc=>q ⟨a.1,by omega⟩) 0:=q0.p _
    let hi20:q0 (fun q:Fin (M+S)->Bool=>fun a:Fin Bc=>q ⟨Bc+a.1,by omega⟩) 0:=q0.p _
    let hp0:q0 (fun (q:Fin (M+S)->Bool) (_:Fin 1)=>q ⟨Bc+Bc,by omega⟩) 0:=q0.p _
    let hwk:=j8 (fun a b par=>q3 w (W k a b par)) hK₁ hK₂ hi10 hi20 hp0
    let hstep0:=q0.r (q0.id (M+S)) hwk
    let Bwk:=(K₁*K₂*2)*(4*Bc+4*w+4)
    have hstep1:q0 (fun z:Fin ((M+S)+w)->Bool =>
      let found:=z ⟨M,by dsimp [M,S];omega⟩
      let ch:Fin Bc->Bool:=fun j=>z ⟨M+1+j.1,by dsimp [M,S];omega⟩
      let rem:Fin w->Bool:=fun j=>z ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩
      let wk:Fin w->Bool:=fun j=>z ⟨M+S+j.1,by dsimp [M,S];omega⟩
      let isLt:=wi rem wk
      let take:=!found&&isLt
      let adv:=!found&&!isLt
      q1 (q1 (fun _:Fin 1=>found||take)
       (zb take ch (q3 Bc k.1)))
       (zb adv rem (zm rem wk))) (4*Bc+28*w+10):=by
     have hf0:q0 (fun (z:Fin ((M+S)+w)->Bool) (_:Fin 1)=>z ⟨M,by dsimp [M,S];omega⟩) 0:=q0.p _;have hch0:q0 (fun z:Fin ((M+S)+w)->Bool=>fun j:Fin Bc=>z ⟨M+1+j.1,by dsimp [M,S];omega⟩) 0:=q0.p _;have hrem0:q0 (fun z:Fin ((M+S)+w)->Bool=>fun j:Fin w=>z ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩) 0:=q0.p _;have hwk0:q0 (fun z:Fin ((M+S)+w)->Bool=>fun j:Fin w=>z ⟨M+S+j.1,by dsimp [M,S];omega⟩) 0:=q0.p _;have hlt:=xo hrem0 hwk0;have hsub:=wx hrem0 hwk0;have hpack:=q0.r (q0.r (q0.id ((M+S)+w)) hlt) hsub
     have hfin:q0 (fun y:Fin (((M+S)+w)+1+w)->Bool =>
       let found:=y ⟨M,by dsimp [M,S];omega⟩
       let ch:Fin Bc->Bool:=fun j=>y ⟨M+1+j.1,by dsimp [M,S];omega⟩
       let rem:Fin w->Bool:=fun j=>y ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩
       let isLt:=y ⟨M+S+w,by dsimp [M,S];omega⟩
       let subV:Fin w->Bool:=fun j=>y ⟨M+S+w+1+j.1,by dsimp [M,S];omega⟩
       let take:=!found&&isLt
       let adv:=!found&&!isLt
       q1 (q1 (fun _:Fin 1=>found||take)
        (zb take ch (q3 Bc k.1)))
        (zb adv rem subV)) (4*Bc+4*w+10):=by
      have fy:q0 (fun (y:Fin (((M+S)+w)+1+w)->Bool) (_:Fin 1)=>y ⟨M,by dsimp [M,S];omega⟩) 0:=q0.p _;have chy:q0 (fun y:Fin (((M+S)+w)+1+w)->Bool=>fun j:Fin Bc=>y ⟨M+1+j.1,by dsimp [M,S];omega⟩) 0:=q0.p _;have remy:q0 (fun y:Fin (((M+S)+w)+1+w)->Bool=>fun j:Fin w=>y ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩) 0:=q0.p _;have lty:q0 (fun (y:Fin (((M+S)+w)+1+w)->Bool) (_:Fin 1)=>y ⟨M+S+w,by dsimp [M,S];omega⟩) 0:=q0.p _
      have suby:q0 (fun y:Fin (((M+S)+w)+1+w)->Bool=>fun j:Fin w=>y ⟨M+S+w+1+j.1,by dsimp [M,S];omega⟩) 0:=q0.p _
      have htk:=q0.a (q0.boolNot fy) lty;have hadv:=q0.a (q0.boolNot fy) (q0.boolNot lty)
      exact (q0.r (q0.r (q0.boolOr fy htk) (zg htk chy (q0.k _)))
       (zg hadv remy suby)).mono (by omega)
     exact ((q0.c hpack hfin).mono (by omega)).congr (fun z=>by
      set remZ:Fin w->Bool:=fun j=>z ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩
      set wkZ:Fin w->Bool:=fun j=>z ⟨M+S+j.1,by dsimp [M,S];omega⟩
      have ha:q1 (q1 z (fun _:Fin 1=>wi remZ wkZ)) (zm remZ wkZ) ⟨M,by dsimp [M,S];omega⟩=z ⟨M,by dsimp [M,S];omega⟩:=by
       simp only [q1,show M< M+S+w by dsimp [M,S];omega,show M< M+S+w+1 by dsimp [M,S];omega,Zd]
      have hb:(fun j:Fin Bc=>q1 (q1 z (fun _:Fin 1=>wi remZ wkZ)) (zm remZ wkZ) ⟨M+1+j.1,by dsimp [M,S];omega⟩) =
        fun j:Fin Bc=>z ⟨M+1+j.1,by dsimp [M,S];omega⟩:=by
       funext j;have:=j.isLt;simp only [q1,show M+1+j.1< M+S+w by dsimp [M,S];omega,show M+1+j.1< M+S+w+1 by dsimp [M,S];omega,Zd]
      have hc:(fun j:Fin w=>q1 (q1 z (fun _:Fin 1=>wi remZ wkZ)) (zm remZ wkZ) ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩)=remZ:=by
       funext j;dsimp only [q1,remZ];rw [Zr (by have:=j.isLt;dsimp [M,S];omega),Zr (by have:=j.isLt;dsimp [M,S];omega)]
      have hd:q1 (q1 z (fun _:Fin 1=>wi remZ wkZ)) (zm remZ wkZ) ⟨M+S+w,by dsimp [M,S];omega⟩=wi remZ wkZ:=by
       simp only [q1,show M+S+w< M+S+w+1 by omega,show ¬ (M+S+w< M+S+w) by omega,Zd,Zf]
      have he:(fun j:Fin w=>q1 (q1 z (fun _:Fin 1=>wi remZ wkZ)) (zm remZ wkZ) ⟨M+S+w+1+j.1,by dsimp [M,S];omega⟩)=zm remZ wkZ:=by
       funext j;dsimp only [q1];rw [Zb (by dsimp [M,S];omega)];congr 1;exact Zx (by dsimp;omega)
      dsimp only;rw [ha,hb,hc,hd,he])
    ((q0.c hstep0 hstep1).mono (by dsimp [Bwk];ring_nf;omega)).congr (fun q=>by
     set wkQ:Fin w->Bool:=w3 (fun a b par=>q3 w (W k a b par))
      (fun a:Fin Bc=>q ⟨a.1,by dsimp [M,S];omega⟩)
      (fun a:Fin Bc=>q ⟨Bc+a.1,by dsimp [M,S];omega⟩)
      (q ⟨Bc+Bc,by dsimp [M,S];omega⟩)
     have h1:q1 q wkQ ⟨M,by dsimp [M,S];omega⟩=q ⟨M,by dsimp [M,S];omega⟩:=by
      dsimp only [q1];rw [Zr (by dsimp [M,S];omega)]
     have h2:(fun j:Fin Bc=>q1 q wkQ ⟨M+1+j.1,by dsimp [M,S];omega⟩) =
       fun j:Fin Bc=>q ⟨M+1+j.1,by dsimp [M,S];omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [M,S];omega)]
     have h3:(fun j:Fin w=>q1 q wkQ ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩) =
       fun j:Fin w=>q ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [M,S];omega)]
     have h4:(fun j:Fin w=>q1 q wkQ ⟨M+S+j.1,by dsimp [M,S];omega⟩)=wkQ:=by
      funext j;dsimp only [q1];rw [Zb (by dsimp [M,S];omega)];congr 1;exact Zx (by dsimp;omega)
     dsimp only;rw [h1,h2,h3,h4];have h0':q ⟨M,by dsimp [M,S];omega⟩=q ⟨M+0,by dsimp [M,S];omega⟩:=rfl
     have h1':(fun j:Fin Bc=>q ⟨M+1+j.1,by dsimp [M,S];omega⟩) =
       (fun j:Fin Bc=>q ⟨M+(1+j.1),by dsimp [M,S];omega⟩):=by
      funext j;congr 1;exact Zx (by dsimp;omega)
     have h2':(fun j:Fin w=>q ⟨M+1+Bc+j.1,by dsimp [M,S];omega⟩) =
       (fun j:Fin w=>q ⟨M+(1+Bc+j.1),by dsimp [M,S];omega⟩):=by
      funext j;congr 1;exact Zx (by dsimp;omega)
     rw [h0',h1',h2']))
 have hpall:=q0.r (q0.r (q0.r hi₁ hi₂) hp) hr
 exact ((q0.c hpall hbase).mono (by omega)).congr (fun x=>by
  have h1:(fun a:Fin Bc=>q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (r x) ⟨a.1,by omega⟩)=i₁ x:=by
   funext a;have ha:=a.isLt;simp only [q1,show a.1< Bc from ha,show a.1< Bc+Bc by omega,show a.1< Bc+Bc+1 by omega,Zd]
  have h2:(fun a:Fin Bc=>q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (r x) ⟨Bc+a.1,by omega⟩)=i₂ x:=by
   funext a;have ha:=a.isLt;simp only [q1,show Bc+a.1< Bc+Bc by omega,show Bc+a.1< Bc+Bc+1 by omega,show ¬ (Bc+a.1< Bc) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
  have h3:q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (r x) ⟨Bc+Bc,by omega⟩=p x:=by
   simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
  have h4:(fun a:Fin w=>q1 (q1 (q1 (i₁ x) (i₂ x)) (fun _:Fin 1=>p x)) (r x) ⟨Bc+Bc+1+a.1,by omega⟩)=r x:=by
   funext a;simp only [q1,show ¬ (Bc+Bc+1+a.1< Bc+Bc+1) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
  rw [h1,h2,h3,h4])
lemma vx {K K₁ K₂ Bc w:ℕ}
  (W:Fin (K+1)->Fin K₁->Fin K₂->Bool->ℕ)
  (i₁ i₂:Fin Bc->Bool) (p:Bool) (r:Fin w->Bool)
  (hK:K< 2^Bc) (h₁:q2 Bc i₁ < K₁) (h₂:q2 Bc i₂ < K₂)
  (wFn:ℕ->ℕ)
  (hwFn:∀ k (hk:k< K+1),wFn k=W ⟨k,hk⟩ ⟨q2 Bc i₁,h₁⟩ ⟨q2 Bc i₂,h₂⟩ p)
  (hw_lt:∀ k< K+1,wFn k< 2^w) :
  let res:=zk W i₁ i₂ p r
  let fa:=zw wFn (K+1) (q2 w r)
  res ⟨0,by omega⟩=fa.1 /\
  (fa.1=true->q2 Bc (fun j:Fin Bc=>res ⟨1+j.1,by omega⟩)=fa.2.1) /\
  q2 w (fun j:Fin w=>res ⟨1+Bc+j.1,by omega⟩)=fa.2.2:=by
 have hinv:∀ t ≤ K+1,
   let st:=((List.finRange (K+1)).take t).foldl
     (fun st k =>
       let found:=st ⟨0,by omega⟩
       let ch:Fin Bc->Bool:=fun j=>st ⟨1+j.1,by omega⟩
       let rem:Fin w->Bool:=fun j=>st ⟨1+Bc+j.1,by omega⟩
       let wk:=w3 (fun a b par=>q3 w (W k a b par)) i₁ i₂ p
       let isLt:=wi rem wk
       let take:=!found&&isLt
       let adv:=!found&&!isLt
       q1 (q1 (fun _:Fin 1=>found||take)
        (zb take ch (q3 Bc k.1)))
        (zb adv rem (zm rem wk)))
     (q1 (q1 (fun _:Fin 1=>false) (q3 Bc 0)) r)
   let fa:=zw wFn t (q2 w r)
   st ⟨0,by omega⟩=fa.1 /\
   (fa.1=true->q2 Bc (fun j:Fin Bc=>st ⟨1+j.1,by omega⟩)=fa.2.1) /\
   q2 w (fun j:Fin w=>st ⟨1+Bc+j.1,by omega⟩)=fa.2.2:=by
  intro t ht
  induction t with
  | zero =>
   simp only [Zn,Zi,zw,List.range_zero]
   refine ⟨by simp [q1],(fun h=>by cases h),?_⟩
   have:(fun j:Fin w=>q1 (q1 (fun _:Fin 1=>false) (q3 Bc 0)) r ⟨1+Bc+j.1,by omega⟩)=r:=by
     funext j;simp only [q1,show ¬ (1+Bc+j.1< 1+Bc) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
   rw [this]
  | succ t iht =>
   have htake:(List.finRange (K+1)).take (t+1)=(List.finRange (K+1)).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   have hstep:zw wFn (t+1) (q2 w r) =
       let fa:=zw wFn t (q2 w r)
       if fa.1 then fa
       else if fa.2.2< wFn t then (true,t,fa.2.2)
       else (false,t,fa.2.2-wFn t):=by
     unfold zw;rw [List.range_succ,Zl];rfl
   rw [hstep]
   set st:=((List.finRange (K+1)).take t).foldl
     (fun st k =>
       let found:=st ⟨0,by omega⟩
       let ch:Fin Bc->Bool:=fun j=>st ⟨1+j.1,by omega⟩
       let rem:Fin w->Bool:=fun j=>st ⟨1+Bc+j.1,by omega⟩
       let wk:=w3 (fun a b par=>q3 w (W k a b par)) i₁ i₂ p
       let isLt:=wi rem wk
       let take:=!found&&isLt
       let adv:=!found&&!isLt
       q1 (q1 (fun _:Fin 1=>found||take)
        (zb take ch (q3 Bc k.1)))
        (zb adv rem (zm rem wk)))
     (q1 (q1 (fun _:Fin 1=>false) (q3 Bc 0)) r)
   set fa:=zw wFn t (q2 w r)
   rcases iht (by omega) with ⟨ih1,ih2,ih3⟩
   have hlu:w3 (fun a b par=>q3 w (W ⟨t,by omega⟩ a b par)) i₁ i₂ p =
       q3 w (wFn t):=by
     simp only [w3,h₁,h₂,Zd,hwFn t (by omega)]
   have hlt_eq:wi (fun j:Fin w=>st ⟨1+Bc+j.1,by omega⟩) (q3 w (wFn t)) =
       decide (fa.2.2< wFn t):=by
     rw [x8,ih3,q4 (hw_lt t (by omega))]
   have hv0 (b0:Bool) (c0:Fin Bc->Bool) (r0:Fin w->Bool) :
       q1 (q1 (fun _:Fin 1=>b0) c0) r0 ⟨0,by omega⟩=b0:=by
     simp [q1]
   have hv1 (b0:Bool) (c0:Fin Bc->Bool) (r0:Fin w->Bool) :
       (fun j:Fin Bc=>q1 (q1 (fun _:Fin 1=>b0) c0) r0 ⟨1+j.1,by omega⟩)=c0:=by
     funext j;have:=j.isLt;simp [q1,show 1+j.1< 1+Bc by omega]
   have hv2 (b0:Bool) (c0:Fin Bc->Bool) (r0:Fin w->Bool) :
       (fun j:Fin w=>q1 (q1 (fun _:Fin 1=>b0) c0) r0 ⟨1+Bc+j.1,by omega⟩)=r0:=by
     funext j;simp [q1]
   dsimp only;rw [hlu,ih1,hlt_eq,hv0,hv1,hv2]
   cases hfa:fa.1
   . simp only [Ze,Zj,Bool.not_false,Bool.true_and,Bool.false_or]
     by_cases hcmp:fa.2.2< wFn t
     . rw [if_pos hcmp,decide_eq_true hcmp,Bool.not_true,zz,zn];exact ⟨rfl,fun _=>q4 (by omega:t< 2^Bc),ih3⟩
     . rw [if_neg hcmp,decide_eq_false hcmp,Bool.not_false,zn,zz]
       refine ⟨rfl,(fun h=>by cases h),?_⟩
       rw [wj _ _ (by rw [ih3,q4 (hw_lt t (by omega))];omega),
         ih3,q4 (hw_lt t (by omega))]
   . simp only [Zh,Bool.not_true,Bool.false_and,Bool.true_or,zn];exact ⟨hfa.symm,fun _=>ih2 hfa,ih3⟩
 have hfull:=hinv (K+1) le_rfl;rw [Zk (by simp)] at hfull;exact hfull
def zt (n Bc w:ℕ) (hBc:0< Bc) (o:Fin (4*n))
  (inp:Fin ((6*n+1)*Bc)->Bool) (st:Fin (Bc+Bc+1+w)->Bool) :
  Fin (Bc+Bc+1+w)->Bool :=
 let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
 let bal:Fin Bc->Bool:=fun j=>st ⟨Bc+j.1,by omega⟩
 let par:Bool:=st ⟨Bc+Bc,by omega⟩
 let acc:Fin w->Bool:=fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩
 let cnt:=q5 (K:=6*n+1) (d:=Bc) inp ⟨o.1,by omega⟩
 let rem:=4*n-1-o.1
 let M:=qv n o.1
 let L:=qs n o.1
 let c:=qh n o.1
 let sig:=qf o.1
 let acc':=y8 (K:=M) (K₁:=2*n+1) (K₂:=n+1)
  (fun k a b p=>zc n rem a.1 b.1 p (qk n rem) k.1) len bal par cnt acc
 let len':=qu Bc M L len cnt
 let bal':=if c=false then qr bal cnt else zm bal cnt
 let par':=xor par (sig&&cnt ⟨0,hBc⟩)
 q1 (q1 (q1 len' bal') (fun _:Fin 1=>par')) acc'
def wm (n Bc w:ℕ) (hBc:0< Bc) (e:Fin n)
  (inp:Fin ((6*n+1)*Bc)->Bool) (st:Fin (Bc+Bc+1+w)->Bool) :
  Fin (Bc+Bc+1+w)->Bool :=
 let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
 let allow:Fin Bc->Bool:=fun j=>st ⟨Bc+j.1,by omega⟩
 let par:Bool:=st ⟨Bc+Bc,by omega⟩
 let acc:Fin w->Bool:=fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩
 let epE:=q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+e.1,by omega⟩
 let emE:=q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+e.1,by omega⟩
 let rem:=n-1-e.1
 let M:=q7 n e.1
 let L:=qe e.1
 let cid:=zb (xj emE) epE (qr (q3 Bc M) emE)
 let cnt:=qr epE emE
 let acc':=y8 (K:=2*M) (K₁:=2*n+1) (K₂:=n+1)
  (fun k a b p=>qx n rem a.1 b.1 p (qi n rem) k.1) len allow par cid acc
 let len':=qu Bc M L len cnt
 let allow':=qu Bc M (v2 (e.1+1)) allow emE
 let par':=xor par (emE ⟨0,hBc⟩)
 q1 (q1 (q1 len' allow') (fun _:Fin 1=>par')) acc'
def p5 (n Bc w:ℕ) (hBc:0< Bc) (inp:Fin ((6*n+1)*Bc)->Bool):Fin w->Bool :=
 let st0:Fin (Bc+Bc+1+w)->Bool :=
  q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1)
 let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st) st0
 let stEv0:Fin (Bc+Bc+1+w)->Bool :=
  q1 (q1 (q1 (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
   (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
   (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩)
 let stEnd:=(List.finRange n).foldl (fun st e=>wm n Bc w hBc e inp st) stEv0
 qr (fun j:Fin w=>stEnd ⟨Bc+Bc+1+j.1,by omega⟩)
  (yd w (q5 (K:=6*n+1) (d:=Bc) inp ⟨6*n,by omega⟩))
lemma bd (n Bc w:ℕ) (hBc:0< Bc) (h4n:4*n< 2^Bc) :
  q0 (p5 n Bc w hBc)
   (5*n*(2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w)+100*Bc+20)+13*w):=by
 let M_in:=(6*n+1)*Bc
 let S:=Bc+Bc+1+w
 let Bstep:=2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w)+100*Bc+20
 have hK1:2*n+1<=2^Bc:=by omega
 have hK2:n+1<=2^Bc:=by omega
 have hodd:q0 (fun inp:Fin M_in->Bool =>
   (List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
     (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1)))
   (0+4*n*Bstep):=by
  refine q0.l _ (zt n Bc w hBc) (q0.k _) (fun o=>?_)
  have hM_le:qv n o.1<=2*n:=Nat.div_le_self _ _;have hlen:q0 (fun q:Fin (M_in+S)->Bool=>fun j:Fin Bc=>q ⟨M_in+j.1,by dsimp [S];omega⟩) 0:=q0.p _;have hbal:q0 (fun q:Fin (M_in+S)->Bool=>fun j:Fin Bc=>q ⟨M_in+Bc+j.1,by dsimp [S];omega⟩) 0:=q0.p _;have hpar:q0 (fun (q:Fin (M_in+S)->Bool) (_:Fin 1)=>q ⟨M_in+Bc+Bc,by dsimp [S];omega⟩) 0:=q0.p _;have hacc:q0 (fun q:Fin (M_in+S)->Bool=>fun j:Fin w=>q ⟨M_in+Bc+Bc+1+j.1,by dsimp [S];omega⟩) 0:=q0.p _
  have hcnt:q0 (fun q:Fin (M_in+S)->Bool=>q5 (K:=6*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨o.1,by omega⟩) 0 :=
   qa (q0.p _) _
  have hacc':=vz (K:=qv n o.1) (K₁:=2*n+1) (K₂:=n+1)
   (fun k a b p=>zc n (4*n-1-o.1) a.1 b.1 p (qk n (4*n-1-o.1)) k.1)
   hK1 hK2 hlen hbal hpar hcnt hacc
  have hlen':=wa (M:=qv n o.1) (C:=qs n o.1) hlen hcnt
  have hbal':q0 (fun q:Fin (M_in+S)->Bool =>
     if qh n o.1=false then
      qr (fun j:Fin Bc=>q ⟨M_in+Bc+j.1,by dsimp [S];omega⟩)
         (q5 (K:=6*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨o.1,by omega⟩)
     else
      zm (fun j:Fin Bc=>q ⟨M_in+Bc+j.1,by dsimp [S];omega⟩)
         (q5 (K:=6*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨o.1,by omega⟩)) (14*Bc):=by
   cases qh n o.1
   . exact (z8 hbal hcnt).mono (by omega)
   . exact (wx hbal hcnt).mono (by omega)
  have hpar':=q0.x hpar (q0.a (q0.k (fun _=>qf o.1)) (q0.b hcnt ⟨0,hBc⟩));have hcomb:=q0.r (q0.r (q0.r hlen' hbal') hpar') hacc'
  refine (hcomb.mono ?_).congr (fun q=>by
   dsimp only [zt]
   have hbal_eq:(fun j:Fin Bc=>q ⟨M_in+Bc+j.1,by omega⟩) =
      (fun j:Fin Bc=>q ⟨M_in+(Bc+j.1),by omega⟩):=by
     funext j;congr 1;exact Zx (by dsimp;omega)
   have hpar_eq:q ⟨M_in+Bc+Bc,by omega⟩=q ⟨M_in+(Bc+Bc),by omega⟩:=by
     congr 1;exact Zx (by dsimp;omega)
   have hacc_eq:(fun j:Fin w=>q ⟨M_in+Bc+Bc+1+j.1,by omega⟩) =
      (fun j:Fin w=>q ⟨M_in+(Bc+Bc+1+j.1),by omega⟩):=by
     funext j;congr 1;exact Zx (by dsimp;omega)
   rw [hbal_eq,hpar_eq,hacc_eq])
  have hmul:qv n o.1*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w) +
     qv n o.1*(27*Bc) <=
     2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w):=by
   have:qv n o.1*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w) +
      qv n o.1*(27*Bc) =
      qv n o.1*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+37*Bc+17*w):=by ring
   rw [this];exact le_trans (Zw _ hM_le) (Nat.mul_le_mul_left _ (by omega))
  dsimp [Bstep];omega
 have hev0:q0 (fun inp:Fin M_in->Bool =>
   let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
     (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
   q1 (q1 (q1 (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
     (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
     (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩)) (4*n*Bstep):=by
  have hrew:q0 (fun st:Fin S->Bool =>
     q1 (q1 (q1 (fun j:Fin Bc=>st ⟨j.1,by dsimp [S];omega⟩) (q3 Bc 0))
      (fun _:Fin 1=>st ⟨Bc+Bc,by dsimp [S];omega⟩))
      (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by dsimp [S];omega⟩)) 0 :=
   (q0.r (q0.r (q0.r (q0.p _) (q0.k _)) (q0.p _)) (q0.p _)).mono (by omega)
  exact (q0.c hodd hrew).mono (by omega)
 have hev:q0 (fun inp:Fin M_in->Bool =>
   let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
     (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
   let stEv0:Fin S->Bool :=
     q1 (q1 (q1 (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
      (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
      (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩)
   (List.finRange n).foldl (fun st e=>wm n Bc w hBc e inp st) stEv0)
   (4*n*Bstep+n*Bstep):=by
  refine q0.l _ (wm n Bc w hBc) hev0 (fun e=>?_)
  have hM_le:q7 n e.1<=n:=by
   unfold q7 qe;exact Nat.div_le_of_le_mul (by nlinarith)
  have hlen:q0 (fun q:Fin (M_in+S)->Bool=>fun j:Fin Bc=>q ⟨M_in+j.1,by dsimp [S];omega⟩) 0:=q0.p _;have hall:q0 (fun q:Fin (M_in+S)->Bool=>fun j:Fin Bc=>q ⟨M_in+Bc+j.1,by dsimp [S];omega⟩) 0:=q0.p _;have hpar:q0 (fun (q:Fin (M_in+S)->Bool) (_:Fin 1)=>q ⟨M_in+Bc+Bc,by dsimp [S];omega⟩) 0:=q0.p _;have hacc:q0 (fun q:Fin (M_in+S)->Bool=>fun j:Fin w=>q ⟨M_in+Bc+Bc+1+j.1,by dsimp [S];omega⟩) 0:=q0.p _
  have hepE:q0 (fun q:Fin (M_in+S)->Bool=>q5 (K:=6*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨4*n+e.1,by omega⟩) 0 :=
   qa (q0.p _) _
  have hemE:q0 (fun q:Fin (M_in+S)->Bool=>q5 (K:=6*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨5*n+e.1,by omega⟩) 0 :=
   qa (q0.p _) _
  have hcid:=zg (jo hemE) hepE (z8 (q0.k (q3 Bc (q7 n e.1))) hemE);have hcnt:=z8 hepE hemE
  have hacc':=vz (K:=2*q7 n e.1) (K₁:=2*n+1) (K₂:=n+1)
   (fun k a b p=>qx n (n-1-e.1) a.1 b.1 p (qi n (n-1-e.1)) k.1)
   hK1 hK2 hlen hall hpar hcid hacc
  have hlen':=wa (M:=q7 n e.1) (C:=qe e.1) hlen hcnt;have hall':=wa (M:=q7 n e.1) (C:=v2 (e.1+1)) hall hemE;have hpar':=q0.x hpar (q0.b hemE ⟨0,hBc⟩);have hcomb:=q0.r (q0.r (q0.r hlen' hall') hpar') hacc'
  refine (hcomb.mono ?_).congr (fun q=>by
   dsimp only [wm]
   have hall_eq:(fun j:Fin Bc=>q ⟨M_in+Bc+j.1,by omega⟩) =
      (fun j:Fin Bc=>q ⟨M_in+(Bc+j.1),by omega⟩):=by
     funext j;congr 1;exact Zx (by dsimp;omega)
   have hpar_eq:q ⟨M_in+Bc+Bc,by omega⟩=q ⟨M_in+(Bc+Bc),by omega⟩:=by
     congr 1;exact Zx (by dsimp;omega)
   have hacc_eq:(fun j:Fin w=>q ⟨M_in+Bc+Bc+1+j.1,by omega⟩) =
      (fun j:Fin w=>q ⟨M_in+(Bc+Bc+1+j.1),by omega⟩):=by
     funext j;congr 1;exact Zx (by dsimp;omega)
   rw [hall_eq,hpar_eq,hacc_eq])
  have hmul:2*q7 n e.1*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w) +
     q7 n e.1*(27*Bc)+q7 n e.1*(27*Bc) <=
     2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w):=by
   have:2*q7 n e.1*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w) +
      q7 n e.1*(27*Bc)+q7 n e.1*(27*Bc) =
      q7 n e.1*(2*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w)+54*Bc):=by ring
   rw [this]
   calc q7 n e.1*(2*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w)+54*Bc)
     <= n*(2*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+10*Bc+17*w)+54*Bc):=Zw _ hM_le
   _<=2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w):=by nlinarith
  dsimp [Bstep];omega
 have hacc_end:q0 (fun inp:Fin M_in->Bool =>
   let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
     (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
   let stEv0:Fin S->Bool :=
     q1 (q1 (q1 (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
      (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
      (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩)
   fun j:Fin w=>((List.finRange n).foldl (fun st e=>wm n Bc w hBc e inp st) stEv0) ⟨Bc+Bc+1+j.1,by omega⟩)
   (5*n*Bstep):=by
  have hproj:q0 (fun st:Fin S->Bool=>fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by dsimp [S];omega⟩) 0 :=
   q0.p _
  have hsumB:4*n*Bstep+n*Bstep=5*n*Bstep:=by ring
  exact (q0.c hev hproj).mono (by omega)
 have hfus:q0 (fun inp:Fin M_in->Bool =>
   yd w (q5 (K:=6*n+1) (d:=Bc) inp ⟨6*n,by omega⟩)) 0 :=
  k5 (qa (q0.id M_in) ⟨6*n,by omega⟩)
 exact (z8 hacc_end hfus).mono (by dsimp [Bstep];omega)
lemma b4 (n Bc w:ℕ) (hBc:0< Bc) (h4n:4*n< 2^Bc) (hw:v6 n<=2^w)
  (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) (fus:ℕ)
  (hvalid:ju n oddC ep em fus)
  (inp:Fin ((6*n+1)*Bc)->Bool)
  (hodd:∀ o:Fin (4*n),q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨o.1,by omega⟩) =
    oddC ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1)) :
  let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
    (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
  q2 Bc (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩)+zj n ep em=2*n /\
  xor (stOdd ⟨Bc+Bc,by omega⟩) (decide ((wc n em)%2=1))=false /\
  q2 w (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩) +
    za n ep em fus n (q2 Bc (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩)) 0 (stOdd ⟨Bc+Bc,by omega⟩) =
    1+z1 n oddC ep em fus (4*n) 0 0 false:=by
 rcases hvalid with ⟨hdisj,hlen,hbal,hpar,hfus_le⟩
 have hrank_lt:1+z1 n oddC ep em fus (4*n) 0 0 false< v6 n :=
  (x2 n (some (oddC,ep,em,fus)) ⟨hdisj,hlen,hbal,hpar,hfus_le⟩).1
 have hbal_le_n:j7 n oddC<=n:=by
  have h1:jl n oddC+j7 n oddC<=yn n oddC:=by
    unfold jl j7 yn;rw [<- Finset.sum_add_distrib];apply Finset.sum_le_sum;intro j _;nlinarith
  omega
 have hphi_le_n:wz n em<=n:=by
  have h2:2*wz n em<=zj n ep em:=by
    unfold wz zj;rw [Finset.mul_sum];apply Finset.sum_le_sum;intro j _;have hv:=vb (j.1+1);nlinarith
  omega
 have hv_extract (a b:Fin Bc->Bool) (p:Bool) (c:Fin w->Bool) :
    let st:=q1 (q1 (q1 a b) (fun _:Fin 1=>p)) c
    (fun j:Fin Bc=>st ⟨j.1,by omega⟩)=a /\
    (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)=b /\
    st ⟨Bc+Bc,by omega⟩=p /\
    (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)=c:=by
  refine ⟨?_,?_,?_,?_⟩
  . funext j;have:=j.isLt;simp only [q1,show j.1< Bc from this,show j.1< Bc+Bc by omega,show j.1< Bc+Bc+1 by omega,Zd]
  . funext j;have:=j.isLt;simp only [q1,show Bc+j.1< Bc+Bc by omega,show Bc+j.1< Bc+Bc+1 by omega,show ¬ (Bc+j.1< Bc) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
  . simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
  . funext j;simp only [q1,show ¬ (Bc+Bc+1+j.1< Bc+Bc+1) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
 have hbit0 (v:Fin Bc->Bool):v ⟨0,hBc⟩=decide (q2 Bc v %2=1):=by
  have h:=qm Bc v;have h0:=congrFun h ⟨0,hBc⟩;simpa [q3,Nat.testBit_zero] using h0.symm
 have hodd_inv:∀ t ≤ 4*n,
    let st:=((List.finRange (4*n)).take t).foldl (fun st o=>zt n Bc w hBc o inp st)
      (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
    let lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩)
    let bv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)
    let pv:=st ⟨Bc+Bc,by omega⟩
    let av:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
    lv+qj n t (fun j c sig=>(2*j.1+1)*oddC j c sig)+zj n ep em=2*n /\
    bv+qj n t (fun j c sig=>if c=false then oddC j c sig else 0) =
      qj n t (fun j c sig=>if c=true then oddC j c sig else 0) /\
    qj n t (fun j c sig=>if c=true then oddC j c sig else 0)<=n /\
    xor pv (decide ((qj n t (fun j c sig=>if sig=true then oddC j c sig else 0) +
      wc n em)%2=1))=false /\
    av+z1 n oddC ep em fus (4*n-t) lv bv pv =
      1+z1 n oddC ep em fus (4*n) 0 0 false:=by
  intro t ht
  induction t with
  | zero =>
    simp only [Zn,Zi,Nat.sub_zero]
    rcases hv_extract (q3 Bc 0) (q3 Bc 0) false (q3 w 1) with ⟨e1,e2,e3,e4⟩
    rw [e1,e2,e3,e4,q4 (by omega:0< 2^Bc),
      q4 (by omega:1< 2^w)]
    refine ⟨?_,?_,?_,?_,rfl⟩
    . simp only [wv,Nat.zero_add];rw [<- hlen];unfold yn;congr 1;apply Zc rfl;intro j _;ring
    . simp only [wv,Nat.zero_add,Zh,Bool.true_eq_false,Ze,Zj,Zq];exact hbal
    . simp only [wv,Zh,Ze,Zj,Nat.zero_add];exact hbal_le_n
    . simp only [wv,Zh,Ze,Zj,Nat.zero_add,Zq,Bool.false_xor];change decide ((jf n oddC+wc n em)%2=1)=false;simp [show (jf n oddC+wc n em)%2≠1 by omega]
  | succ t iht =>
    have htake:(List.finRange (4*n)).take (t+1)=(List.finRange (4*n)).take t++[⟨t,by omega⟩]:=by
      rw [Zt (by simp;omega)];simp [Zg]
    rw [htake,Zl,Zo,Zi]
    set st:=((List.finRange (4*n)).take t).foldl (fun st o=>zt n Bc w hBc o inp st)
      (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
    rcases iht (by omega) with ⟨ihl,ihb,ihbl,ihp,iha⟩
    set lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩);set bv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩);set pv:=st ⟨Bc+Bc,by omega⟩;set av:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
    set o:Fin (4*n):=⟨t,by omega⟩
    set rem:=4*n-1-t
    have hrem_eq:4*n-t=rem+1:=by omega
    have hrem_sub:4*n-(rem+1)=t:=by omega
    set j0:Fin n:=⟨zf n t,(qp n t (by omega)).1⟩
    set c0:=qh n t;set s0:=qf t;set cnt:=oddC j0 c0 s0;have hcnt_bits:q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩)=cnt:=hodd o;rw [w6 n t (by omega)] at ihl ihbl ihp;rw [w6 n t (by omega),w6 n t (by omega)] at ihb
    have hcnt_le_M:cnt<=qv n t:=by
      unfold qv qs
      have:(2*j0.1+1)*cnt<=2*n:=by
        change lv+((2*j0.1+1)*cnt+_)+zj n ep em=2*n at ihl;omega
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by dsimp [j0] at this;nlinarith)
    have hM_le_Bc:qv n t<=2^Bc:=le_trans (Nat.div_le_self _ _) (by omega)
    have hlv_le:lv< 2*n+1:=by omega
    have hbv_le:bv< n+1:=by
      change bv+((if c0=false then cnt else 0)+_)=(if c0=true then cnt else 0)+_ at ihb;change (if c0=true then cnt else 0)+_<=n at ihbl;omega
    have hrank_unfold:z1 n oddC ep em fus (rem+1) lv bv pv =
        ql (zc n rem lv bv pv (qk n rem)) cnt +
        z1 n oddC ep em fus rem (lv+cnt*qs n t)
         (if c0=false then bv+cnt else bv-cnt)
         (xor pv (s0&&decide (cnt %2=1))):=by
      simp only [z1,hrem_sub,show t< 4*n by omega,Zd];rfl
    rw [hrem_eq,hrank_unfold] at iha;dsimp only [zt]
    rcases hv_extract _ _ _ _ with ⟨e1,e2,e3,e4⟩
    rw [e1,e2,e3,e4]
    have hlen_new:q2 Bc (qu Bc (qv n t) (qs n t)
        (fun j=>st ⟨j.1,by omega⟩) (q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩)) =
        lv+cnt*qs n t:=by
      rw [w0 Bc (qv n t) (qs n t) _ _ hM_le_Bc
        (by rw [hcnt_bits];exact hcnt_le_M)
        (by rw [hcnt_bits];change lv+((2*j0.1+1)*cnt+_)+zj n ep em=2*n at ihl
            have:cnt*qs n t=(2*j0.1+1)*cnt:=by unfold qs;dsimp [j0];ring
            omega),hcnt_bits]
    have hbal_step :
        (c0=false->bv+cnt<=n)/\(c0=true->cnt<=bv) /\
        (if c0=false then bv+cnt else bv-cnt)+qj n (t+1) (fun j c sig=>if c=false then oddC j c sig else 0) =
         qj n (t+1) (fun j c sig=>if c=true then oddC j c sig else 0) /\
        qj n (t+1) (fun j c sig=>if c=true then oddC j c sig else 0)<=n:=by
      change bv+((if c0=false then cnt else 0)+_)=(if c0=true then cnt else 0)+_ at ihb;change (if c0=true then cnt else 0)+_<=n at ihbl
      cases hc:c0
      . rw [hc] at ihb ihbl;simp only [Zh,Ze,Zj,Nat.zero_add] at ihb ihbl ⊢;exact ⟨fun _=>by omega,(fun h=>by cases h),by omega,by omega⟩
      . rw [hc] at ihb ihbl;simp only [Zh,Bool.true_eq_false,Zj,Nat.zero_add] at ihb ihbl ⊢
        have hrem0:qj n (t+1) (fun j c sig=>if c=false then oddC j c sig else 0)=0:=by
         unfold qj;apply Finset.sum_eq_zero;intro j _;have hge2n:2*n<=t:=of_decide_eq_true (by unfold c0 qh at hc;exact hc)
         have hlt1:q6 n j false false< 2*n:=by unfold q6;have:=j.isLt;simp
         have hlt2:q6 n j false true< 2*n:=by unfold q6;have:=j.isLt;simp;omega
         simp [show ¬ (t+1<=q6 n j false false) by omega,
             show ¬ (t+1<=q6 n j false true) by omega]
        rw [hrem0,Zq] at ihb;exact ⟨(fun h=>by cases h),fun _=>by omega,by rw [hrem0];omega,by omega⟩
    have hbal_new:q2 Bc (if c0=false then qr (fun j=>st ⟨Bc+j.1,by omega⟩) (q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩)
        else zm (fun j=>st ⟨Bc+j.1,by omega⟩) (q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩)) =
        if c0=false then bv+cnt else bv-cnt:=by
      cases hc:c0
      . simp only [Zh];rw [qr,qc,hcnt_bits];have hb:=hbal_step.1 hc;change (bv+cnt+false.toNat)%2^Bc=bv+cnt;simp [Zm (by omega:bv+cnt< 2^Bc)]
      . simp only [Bool.true_eq_false,Zj];have hb:=hbal_step.2.1 hc;rw [wj _ _ (by rw [hcnt_bits];exact hb),hcnt_bits]
    have hpar_new:xor pv (s0&&(q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩) ⟨0,hBc⟩) =
        xor pv (s0&&decide (cnt %2=1)):=by
      rw [hbit0 (q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩),hcnt_bits]
    have hacc_new:q2 w (y8 (K:=qv n t) (K₁:=2*n+1) (K₂:=n+1)
        (fun k a b p=>zc n rem a.1 b.1 p (qk n rem) k.1)
        (fun j=>st ⟨j.1,by omega⟩) (fun j=>st ⟨Bc+j.1,by omega⟩) pv
        (q5 (K:=6*n+1) (d:=Bc) inp ⟨t,by omega⟩)
        (fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩)) =
        av+ql (zc n rem lv bv pv (qk n rem)) cnt:=by
      rw [vn _ _ _ _ _ _ hM_le_Bc hlv_le hbv_le
        (by rw [hcnt_bits];exact hcnt_le_M)
        (zc n rem lv bv pv (qk n rem))
        (fun k _=>rfl)
        (by rw [hcnt_bits];omega),hcnt_bits]
    rw [hlen_new,hbal_new,hpar_new,hacc_new]
    refine ⟨?_,hbal_step.2.2.1,hbal_step.2.2.2,?_,?_⟩
    . change lv+((2*j0.1+1)*cnt+_)+zj n ep em=2*n at ihl
      have:cnt*qs n t=(2*j0.1+1)*cnt:=by unfold qs;dsimp [j0];ring
      omega
    . change xor pv (decide ((((if s0=true then cnt else 0)+_)+wc n em)%2=1))=false at ihp
      cases hs:s0
      . rw [hs] at ihp;simpa only [Bool.false_and,Bool.xor_false,Ze,Zj,Nat.zero_add] using ihp
      . rw [hs] at ihp;simp only [Bool.true_and,Zh] at ihp ⊢;rw [x4,<-Nat.add_assoc];exact ihp
    . have hrem':4*n-(t+1)=rem:=by omega
      rw [hrem'];omega
 have hodd_full:=hodd_inv (4*n) le_rfl;rw [Zk (by simp)] at hodd_full
 set stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
  (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
 rcases hodd_full with ⟨hodl,hodb,_,hodp,hoda⟩
 simp only [jw,Zq,Nat.zero_add,Nat.sub_self,z1] at hodl hodb hodp hoda;exact ⟨hodl,hodp,hoda⟩
lemma c7 (n Bc w:ℕ) (hBc:0< Bc) (h4n:4*n< 2^Bc) (hw:v6 n<=2^w)
  (oddC:Fin n->Bool->Bool->ℕ) (ep em:Fin n->ℕ) (fus:ℕ)
  (hvalid:ju n oddC ep em fus)
  (inp:Fin ((6*n+1)*Bc)->Bool)
  (hodd:∀ o:Fin (4*n),q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨o.1,by omega⟩) =
    oddC ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1))
  (hep:∀ j:Fin n,q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+j.1,by omega⟩)=ep j)
  (hem:∀ j:Fin n,q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+j.1,by omega⟩)=em j)
  (hfus:q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨6*n,by omega⟩)=fus) :
  q2 w (p5 n Bc w hBc inp)=1+z1 n oddC ep em fus (4*n) 0 0 false:=by
 rcases b4 n Bc w hBc h4n hw oddC ep em fus hvalid inp hodd with ⟨hodl,hodp,hoda⟩
 rcases hvalid with ⟨hdisj,hlen,hbal,hpar,hfus_le⟩
 have hrank_lt:1+z1 n oddC ep em fus (4*n) 0 0 false< v6 n :=
  (x2 n (some (oddC,ep,em,fus)) ⟨hdisj,hlen,hbal,hpar,hfus_le⟩).1
 have hphi_le_n:wz n em<=n:=by
  have h2:2*wz n em<=zj n ep em:=by
    unfold wz zj;rw [Finset.mul_sum];apply Finset.sum_le_sum;intro j _;have hv:=vb (j.1+1);nlinarith
  omega
 have hv_extract (a b:Fin Bc->Bool) (p:Bool) (c:Fin w->Bool) :
    let st:=q1 (q1 (q1 a b) (fun _:Fin 1=>p)) c
    (fun j:Fin Bc=>st ⟨j.1,by omega⟩)=a /\
    (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)=b /\
    st ⟨Bc+Bc,by omega⟩=p /\
    (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)=c:=by
  refine ⟨?_,?_,?_,?_⟩
  . funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega),Zr (by have:=j.isLt;omega),Zr j.isLt]
  . funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega),Zr (by have:=j.isLt;omega),Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
  . dsimp only [q1];rw [Zr (by omega),Zb (by omega)]
  . funext j;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have hbit0 (v:Fin Bc->Bool):v ⟨0,hBc⟩=decide (q2 Bc v %2=1):=by
  have h0:=congrFun (qm Bc v) ⟨0,hBc⟩;simpa [q3,Nat.testBit_zero] using h0.symm
 set stOdd:=(List.finRange (4*n)).foldl (fun st o=>zt n Bc w hBc o inp st)
  (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (q3 w 1))
 set stEv0:Fin (Bc+Bc+1+w)->Bool :=
  q1 (q1 (q1 (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
    (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
    (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩)
 have hev_inv:∀ t ≤ n,
    let st:=((List.finRange n).take t).foldl (fun st e=>wm n Bc w hBc e inp st) stEv0
    let lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩)
    let alv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)
    let pv:=st ⟨Bc+Bc,by omega⟩
    let av:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
    lv+(∑ j:Fin n,if t<=j.1 then 2*(j.1+1)*(ep j+em j) else 0)=2*n /\
    alv+(∑ j:Fin n,if t<=j.1 then em j*v2 (j.1+1) else 0)=wz n em /\
    xor pv (decide ((∑ j:Fin n,if t<=j.1 then em j else 0)%2=1))=false /\
    av+za n ep em fus (n-t) lv alv pv =
      1+z1 n oddC ep em fus (4*n) 0 0 false:=by
  intro t ht
  induction t with
  | zero =>
    simp only [Zn,Zi,Nat.sub_zero,Nat.zero_le,Zh]
    rcases hv_extract (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0)
      (stOdd ⟨Bc+Bc,by omega⟩) (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩) with ⟨e1,e2,e3,e4⟩
    dsimp only [stEv0];rw [e1,e2,e3,e4,q4 (by omega:0< 2^Bc),Nat.zero_add];exact ⟨hodl,rfl,hodp,hoda⟩
  | succ t iht =>
    have htake:(List.finRange n).take (t+1)=(List.finRange n).take t++[⟨t,by omega⟩]:=by
      rw [Zt (by simp;omega)];simp [Zg]
    rw [htake,Zl,Zo,Zi];set st:=((List.finRange n).take t).foldl (fun st e=>wm n Bc w hBc e inp st) stEv0
    rcases iht (by omega) with ⟨ihl,ihal,ihp,iha⟩
    set lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩);set alv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩);set pv:=st ⟨Bc+Bc,by omega⟩;set av:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
    set e:Fin n:=⟨t,by omega⟩
    set rem:=n-1-t
    have hrem_eq:n-t=rem+1:=by omega
    have hrem_sub:n-(rem+1)=t:=by omega
    have hep_b:q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+t,by omega⟩)=ep e:=hep e;have hem_b:q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)=em e:=hem e;rw [vv n t (by omega)] at ihl ihal ihp;dsimp only at ihl ihal ihp;change lv+(2*(t+1)*(ep e+em e)+∑ j:Fin n,if t+1<=j.1 then 2*(j.1+1)*(ep j+em j) else 0)=2*n at ihl;change alv+(em e*v2 (t+1)+∑ j:Fin n,if t+1<=j.1 then em j*v2 (j.1+1) else 0)=wz n em at ihal
    have hcnt_le_M:ep e+em e<=q7 n t:=by
      unfold q7 qe
      have h1:2*(t+1)*(ep e+em e)<=2*n:=by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    have hM_le_n:q7 n t<=n:=by
      unfold q7 qe;exact Nat.div_le_of_le_mul (by nlinarith)
    rcases ja (q7 n t) (ep e) (em e) (hdisj e) hcnt_le_M with
      ⟨hcid_le,hcnt_eq,hep_eq,hem_eq⟩
    set cid:=qy (q7 n t) (ep e) (em e)
    have hcid_bits:q2 Bc (zb (xj (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩))
        (q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+t,by omega⟩)
        (qr (q3 Bc (q7 n t)) (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)))=cid:=by
      unfold cid qy
      by_cases hm0:0< em e
      . have hany:xj (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)=true:=by
          cases h:xj (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)
          . have hall0:=(x3 _).mp h
            have hv0:q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)=0:=by
             unfold q2;apply Finset.sum_eq_zero;intro i _;simp [hall0 i]
            omega
          . rfl
        rw [hany,zz,if_pos hm0,qr,qc,
          q4 (by omega:q7 n t< 2^Bc),hem_b]
        simp [Zm (by omega:q7 n t+em e< 2^Bc)]
      . have hany:xj (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)=false:=by
          rw [x3];intro i
          have hb:q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩=q3 Bc 0:=by
            rw [<- qm Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩),hem_b,show em e=0 by omega]
          rw [hb];simp [q3]
        rw [hany,zn,if_neg hm0,hep_b]
    have hcnt_bits:q2 Bc (qr (q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+t,by omega⟩)
        (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩))=ep e+em e:=by
      rw [qr,qc,hep_b,hem_b];simp [Zm (by omega:ep e+em e< 2^Bc)]
    have hlv_le:lv< 2*n+1:=by omega
    have halv_le:alv< n+1:=by omega
    have hrank_unfold:za n ep em fus (rem+1) lv alv pv =
        ql (qx n rem lv alv pv (qi n rem)) cid +
        za n ep em fus rem (lv+(ep e+em e)*qe t)
          (alv+em e*v2 (t+1)) (xor pv (decide (em e %2=1))):=by
      simp only [za,hrem_sub,show t< n by omega,Zd];have hd1:qw (q7 n t) cid=ep e+em e:=hcnt_eq
      have hd2:(if z5 (q7 n t) cid=true then qw (q7 n t) cid*v2 (t+1) else 0) =
          em e*v2 (t+1):=by
        by_cases hneg:z5 (q7 n t) cid=true
        . simp only [hneg,Zh] at hem_eq ⊢;rw [hem_eq]
        . simp only [hneg,Zj] at hem_eq ⊢;rw [<- hem_eq];simp
      have hd3:(z5 (q7 n t) cid&&decide (qw (q7 n t) cid %2=1)) =
          decide (em e %2=1):=by
        by_cases hneg:z5 (q7 n t) cid=true
        . simp only [hneg,Zh,Bool.true_and] at hem_eq ⊢;rw [hem_eq]
        . simp only [hneg,Zj,Bool.false_and] at hem_eq ⊢;rw [<- hem_eq];rfl
      change ql (qx n rem lv alv pv (qi n rem)) cid +
        za n ep em fus rem
          (lv+qw (q7 n t) cid*qe t)
          (alv+if z5 (q7 n t) cid=true then qw (q7 n t) cid*v2 (t+1) else 0)
          (xor pv (z5 (q7 n t) cid&&decide (qw (q7 n t) cid %2=1)))=_
      rw [hd2,hd3,hd1]
    rw [hrem_eq,hrank_unfold] at iha;dsimp only [wm]
    rcases hv_extract _ _ _ _ with ⟨e1,e2,e3,e4⟩
    rw [e1,e2,e3,e4]
    have hlen_new:q2 Bc (qu Bc (q7 n t) (qe t)
        (fun j=>st ⟨j.1,by omega⟩) (qr (q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+t,by omega⟩)
          (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩))) =
        lv+(ep e+em e)*qe t:=by
      rw [w0 Bc (q7 n t) (qe t) _ _ (by omega)
        (by rw [hcnt_bits];exact hcnt_le_M)
        (by rw [hcnt_bits];unfold qe;have:(ep e+em e)*(2*(t+1))=2*(t+1)*(ep e+em e):=(by ring);dsimp only [lv] at ihl;omega),hcnt_bits]
    have hall_new:q2 Bc (qu Bc (q7 n t) (v2 (t+1))
        (fun j=>st ⟨Bc+j.1,by omega⟩) (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)) =
        alv+em e*v2 (t+1):=by
      rw [w0 Bc (q7 n t) (v2 (t+1)) _ _ (by omega)
        (by rw [hem_b];omega) (by rw [hem_b];dsimp only [alv] at ihal;omega),hem_b]
    have hpar_new:xor pv ((q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩) ⟨0,hBc⟩) =
        xor pv (decide (em e %2=1)):=by
      rw [hbit0 (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩),hem_b]
    have hacc_new:q2 w (y8 (K:=2*q7 n t) (K₁:=2*n+1) (K₂:=n+1)
        (fun k a b p=>qx n rem a.1 b.1 p (qi n rem) k.1)
        (fun j=>st ⟨j.1,by omega⟩) (fun j=>st ⟨Bc+j.1,by omega⟩) pv
        (zb (xj (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩))
          (q5 (K:=6*n+1) (d:=Bc) inp ⟨4*n+t,by omega⟩)
          (qr (q3 Bc (q7 n t)) (q5 (K:=6*n+1) (d:=Bc) inp ⟨5*n+t,by omega⟩)))
        (fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩)) =
        av+ql (qx n rem lv alv pv (qi n rem)) cid:=by
      rw [vn _ _ _ _ _ _ (by omega) hlv_le halv_le
        (by rw [hcid_bits];exact hcid_le)
        (qx n rem lv alv pv (qi n rem))
        (fun k _=>rfl)
        (by rw [hcid_bits];omega),hcid_bits]
    rw [hlen_new,hall_new,hpar_new,hacc_new]
    refine ⟨?_,?_,?_,?_⟩
    . unfold qe
      have:(ep e+em e)*(2*(t+1))=2*(t+1)*(ep e+em e):=by ring
      omega
    . omega
    . rw [x4];exact ihp
    . have hrem':n-(t+1)=rem:=by omega
      rw [hrem'];omega
 have hev_full:=hev_inv n le_rfl;rw [Zk (by simp)] at hev_full
 rcases hev_full with ⟨_,_,_,hfa⟩
 simp only [Nat.sub_self,za] at hfa;unfold p5;rw [qr,qc]
 have hfus_lt_w:q2 Bc (q5 (K:=6*n+1) (d:=Bc) inp ⟨6*n,by omega⟩)< 2^w:=by
  rw [hfus];omega
 rw [ji _ hfus_lt_w,hfus];simp only [Zp,Zq]
 have hsum_eq:q2 w (fun j:Fin w=>((List.finRange n).foldl (fun st e=>wm n Bc w hBc e inp st) stEv0) ⟨Bc+Bc+1+j.1,by omega⟩)+fus =
    1+z1 n oddC ep em fus (4*n) 0 0 false:=hfa
 rw [hsum_eq,Zm (by omega)]
def zo (n Bc w:ℕ) (hBc:0< Bc) (o:Fin (4*n))
  (st:Fin (Bc+Bc+1+w+4*n*Bc)->Bool) :
  Fin (Bc+Bc+1+w+4*n*Bc)->Bool :=
 let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
 let bal:Fin Bc->Bool:=fun j=>st ⟨Bc+j.1,by omega⟩
 let par:Bool:=st ⟨Bc+Bc,by omega⟩
 let rem:Fin w->Bool:=fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩
 let arr:Fin (4*n*Bc)->Bool:=fun j=>st ⟨Bc+Bc+1+w+j.1,by omega⟩
 let remSt:=4*n-1-o.1
 let M:=qv n o.1
 let L:=qs n o.1
 let c:=qh n o.1
 let sig:=qf o.1
 let fc:=zk (K:=M) (K₁:=2*n+1) (K₂:=n+1)
  (fun k a b p=>zc n remSt a.1 b.1 p (qk n remSt) k.1) len bal par rem
 let cnt:Fin Bc->Bool:=fun j=>fc ⟨1+j.1,by omega⟩
 let rem':Fin w->Bool:=fun j=>fc ⟨1+Bc+j.1,by omega⟩
 let len':=qu Bc M L len cnt
 let bal':=if c=false then qr bal cnt else zm bal cnt
 let par':=xor par (sig&&cnt ⟨0,hBc⟩)
 let arr':=qn (K:=4*n) (d:=Bc) (fun slot =>
  if slot.1=o.1 then cnt else q5 (K:=4*n) (d:=Bc) arr slot)
 q1 (q1 (q1 (q1 len' bal') (fun _:Fin 1=>par')) rem') arr'
def zx (n Bc w:ℕ) (hBc:0< Bc) (e:Fin n)
  (st:Fin (Bc+Bc+1+w+n*Bc+n*Bc)->Bool) :
  Fin (Bc+Bc+1+w+n*Bc+n*Bc)->Bool :=
 let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
 let allow:Fin Bc->Bool:=fun j=>st ⟨Bc+j.1,by omega⟩
 let par:Bool:=st ⟨Bc+Bc,by omega⟩
 let rem:Fin w->Bool:=fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩
 let epA:Fin (n*Bc)->Bool:=fun j=>st ⟨Bc+Bc+1+w+j.1,by omega⟩
 let emA:Fin (n*Bc)->Bool:=fun j=>st ⟨Bc+Bc+1+w+n*Bc+j.1,by omega⟩
 let remSt:=n-1-e.1
 let M:=q7 n e.1
 let L:=qe e.1
 let fc:=zk (K:=2*M) (K₁:=2*n+1) (K₂:=n+1)
  (fun k a b p=>qx n remSt a.1 b.1 p (qi n remSt) k.1) len allow par rem
 let cid:Fin Bc->Bool:=fun j=>fc ⟨1+j.1,by omega⟩
 let rem':Fin w->Bool:=fun j=>fc ⟨1+Bc+j.1,by omega⟩
 let isNeg:=wi (q3 Bc M) cid
 let epVal:=zb isNeg cid (q3 Bc 0)
 let emVal:=zb isNeg (q3 Bc 0) (zm cid (q3 Bc M))
 let cnt:=qr epVal emVal
 let len':=qu Bc M L len cnt
 let allow':=qu Bc M (v2 (e.1+1)) allow emVal
 let par':=xor par (emVal ⟨0,hBc⟩)
 let epA':=qn (K:=n) (d:=Bc) (fun slot =>
  if slot.1=e.1 then epVal else q5 (K:=n) (d:=Bc) epA slot)
 let emA':=qn (K:=n) (d:=Bc) (fun slot =>
  if slot.1=e.1 then emVal else q5 (K:=n) (d:=Bc) emA slot)
 q1 (q1 (q1 (q1 (q1 len' allow') (fun _:Fin 1=>par')) rem') epA') emA'
def xi (n Bc w:ℕ) (hBc:0< Bc) (z:Fin w->Bool):Fin ((6*n+1)*Bc)->Bool :=
 let stOdd0:Fin (Bc+Bc+1+w+4*n*Bc)->Bool :=
  q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
   (zm z (q3 w 1))) (fun _=>false)
 let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zo n Bc w hBc o st) stOdd0
 let stEv0:Fin (Bc+Bc+1+w+n*Bc+n*Bc)->Bool :=
  q1 (q1 (q1 (q1 (q1
   (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
   (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
   (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩))
   (fun _:Fin (n*Bc)=>false)) (fun _:Fin (n*Bc)=>false)
 let stEv:=(List.finRange n).foldl (fun st e=>zx n Bc w hBc e st) stEv0
 let oddArr:Fin (4*n*Bc)->Bool:=fun j=>stOdd ⟨Bc+Bc+1+w+j.1,by omega⟩
 let epArr:Fin (n*Bc)->Bool:=fun j=>stEv ⟨Bc+Bc+1+w+j.1,by omega⟩
 let emArr:Fin (n*Bc)->Bool:=fun j=>stEv ⟨Bc+Bc+1+w+n*Bc+j.1,by omega⟩
 let fusBits:Fin Bc->Bool:=yd Bc (fun j:Fin w=>stEv ⟨Bc+Bc+1+j.1,by omega⟩)
 qn (K:=6*n+1) (d:=Bc) (fun slot =>
  if h1:slot.1< 4*n then q5 (K:=4*n) (d:=Bc) oddArr ⟨slot.1,h1⟩
  else if h2:slot.1< 5*n then q5 (K:=n) (d:=Bc) epArr ⟨slot.1-4*n,by omega⟩
  else if h3:slot.1< 6*n then q5 (K:=n) (d:=Bc) emArr ⟨slot.1-5*n,by omega⟩
  else fusBits)
lemma pq (n Bc w:ℕ) (hBc:0< Bc) (h4n:4*n< 2^Bc) :
   q0 (xi n Bc w hBc)
     (14*w+5*n*((2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10)+100*Bc+20)):=by
 let S1:=Bc+Bc+1+w+4*n*Bc
 let S2:=Bc+Bc+1+w+n*Bc+n*Bc
 let Bstep:=(2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10)+100*Bc+20
 have hK1:2*n+1<=2^Bc:=by omega
 have hK2:n+1<=2^Bc:=by omega
 have hodd_step (o:Fin (4*n)):q0 (zo n Bc w hBc o) Bstep:=by
   have hM_le:qv n o.1<=2*n:=Nat.div_le_self _ _;have hlen:q0 (fun st:Fin S1->Bool=>fun j:Fin Bc=>st ⟨j.1,by dsimp [S1];omega⟩) 0:=q0.p _;have hbal:q0 (fun st:Fin S1->Bool=>fun j:Fin Bc=>st ⟨Bc+j.1,by dsimp [S1];omega⟩) 0:=q0.p _;have hpar:q0 (fun (st:Fin S1->Bool) (_:Fin 1)=>st ⟨Bc+Bc,by dsimp [S1];omega⟩) 0:=q0.p _;have hrem:q0 (fun st:Fin S1->Bool=>fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by dsimp [S1];omega⟩) 0:=q0.p _
   have hfc:=v5 (K:=qv n o.1) (K₁:=2*n+1) (K₂:=n+1)
     (fun k a b p=>zc n (4*n-1-o.1) a.1 b.1 p (qk n (4*n-1-o.1)) k.1)
     hK1 hK2 hlen hbal hpar hrem
   have hpair1:=q0.r (q0.id S1) hfc
   have hfin:q0 (fun q:Fin (S1+(1+Bc+w))->Bool =>
      let len:Fin Bc->Bool:=fun j=>q ⟨j.1,by dsimp [S1];omega⟩
      let bal:Fin Bc->Bool:=fun j=>q ⟨Bc+j.1,by dsimp [S1];omega⟩
      let par:Bool:=q ⟨Bc+Bc,by dsimp [S1];omega⟩
      let arr:Fin (4*n*Bc)->Bool:=fun j=>q ⟨Bc+Bc+1+w+j.1,by dsimp [S1];omega⟩
      let cnt:Fin Bc->Bool:=fun j=>q ⟨S1+1+j.1,by omega⟩
      let rem':Fin w->Bool:=fun j=>q ⟨S1+1+Bc+j.1,by omega⟩
      let len':=qu Bc (qv n o.1) (qs n o.1) len cnt
      let bal':=if qh n o.1=false then qr bal cnt else zm bal cnt
      let par':=xor par (qf o.1&&cnt ⟨0,hBc⟩)
      let arr':=qn (K:=4*n) (d:=Bc) (fun slot =>
        if slot.1=o.1 then cnt else q5 (K:=4*n) (d:=Bc) arr slot)
      q1 (q1 (q1 (q1 len' bal') (fun _:Fin 1=>par')) rem') arr')
      (qv n o.1*(27*Bc)+14*Bc+10):=by
     have hlen0:q0 (fun q:Fin (S1+(1+Bc+w))->Bool=>fun j:Fin Bc=>q ⟨j.1,by dsimp [S1];omega⟩) 0:=q0.p _;have hbal0:q0 (fun q:Fin (S1+(1+Bc+w))->Bool=>fun j:Fin Bc=>q ⟨Bc+j.1,by dsimp [S1];omega⟩) 0:=q0.p _;have hpar0:q0 (fun (q:Fin (S1+(1+Bc+w))->Bool) (_:Fin 1)=>q ⟨Bc+Bc,by dsimp [S1];omega⟩) 0:=q0.p _;have hcnt0:q0 (fun q:Fin (S1+(1+Bc+w))->Bool=>fun j:Fin Bc=>q ⟨S1+1+j.1,by omega⟩) 0:=q0.p _;have hrem'0:q0 (fun q:Fin (S1+(1+Bc+w))->Bool=>fun j:Fin w=>q ⟨S1+1+Bc+j.1,by omega⟩) 0:=q0.p _;have hlen':=wa (M:=qv n o.1) (C:=qs n o.1) hlen0 hcnt0
     have hbal':q0 (fun q:Fin (S1+(1+Bc+w))->Bool =>
        if qh n o.1=false then qr (fun j:Fin Bc=>q ⟨Bc+j.1,by dsimp [S1];omega⟩) (fun j:Fin Bc=>q ⟨S1+1+j.1,by omega⟩)
        else zm (fun j:Fin Bc=>q ⟨Bc+j.1,by dsimp [S1];omega⟩) (fun j:Fin Bc=>q ⟨S1+1+j.1,by omega⟩)) (14*Bc):=by
      cases qh n o.1
      . exact (z8 hbal0 hcnt0).mono (by omega)
      . exact (wx hbal0 hcnt0).mono (by omega)
     have hpar':=q0.x hpar0 (q0.a (q0.k (fun _=>qf o.1)) (q0.b hcnt0 ⟨0,hBc⟩))
     have harr':q0 (fun q:Fin (S1+(1+Bc+w))->Bool =>
        qn (K:=4*n) (d:=Bc) (fun slot =>
          if slot.1=o.1 then fun j=>q ⟨S1+1+j.1,by omega⟩
          else q5 (K:=4*n) (d:=Bc) (fun j=>q ⟨Bc+Bc+1+w+j.1,by dsimp [S1];omega⟩) slot)) 0:=by
      refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
      split_ifs
      . exact hcnt0
      . exact qa (q0.p _) slot
     exact (q0.r (q0.r (q0.r (q0.r hlen' hbal') hpar') hrem'0) harr').mono (by omega)
   refine ((q0.c hpair1 hfin).mono ?_).congr (fun st=>?_)
   . have hmul:(qv n o.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+4*Bc+28*w+10) +
        qv n o.1*(27*Bc) <=
        (2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10):=by
      have h1:qv n o.1*(27*Bc)<=(qv n o.1+1)*(60*Bc):=by nlinarith
      have h2:(qv n o.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+4*Bc+28*w+10) +
          (qv n o.1+1)*(60*Bc) =
          (qv n o.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10):=by ring
      calc _<=(qv n o.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10):=by linarith
        _<=_:=Zw _ (by omega)
     dsimp [Bstep];omega
   . set fc:=zk (K:=qv n o.1) (K₁:=2*n+1) (K₂:=n+1)
      (fun k a b p=>zc n (4*n-1-o.1) a.1 b.1 p (qk n (4*n-1-o.1)) k.1)
      (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)
      (st ⟨Bc+Bc,by omega⟩) (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
     have h1:(fun j:Fin Bc=>q1 st fc ⟨j.1,by omega⟩)=fun j:Fin Bc=>st ⟨j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h2:(fun j:Fin Bc=>q1 st fc ⟨Bc+j.1,by omega⟩)=fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h3:q1 st fc ⟨Bc+Bc,by omega⟩=st ⟨Bc+Bc,by omega⟩:=by
      dsimp only [q1];rw [Zr (by omega)]
     have h4:(fun j:Fin (4*n*Bc)=>q1 st fc ⟨Bc+Bc+1+w+j.1,by omega⟩) =
        fun j:Fin (4*n*Bc)=>st ⟨Bc+Bc+1+w+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h5:(fun j:Fin Bc=>q1 st fc ⟨S1+1+j.1,by omega⟩)=fun j:Fin Bc=>fc ⟨1+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zb (by dsimp [S1];omega)];congr 1;exact Zx (by dsimp [S1];try omega)
     have h50:q1 st fc ⟨S1+1+0,by omega⟩=fc ⟨1+0,by omega⟩:=congrFun h5 ⟨0,hBc⟩
     have h6:(fun j:Fin w=>q1 st fc ⟨S1+1+Bc+j.1,by omega⟩)=fun j:Fin w=>fc ⟨1+Bc+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zb (by dsimp [S1];omega)];congr 1;exact Zx (by dsimp [S1];try omega)
     dsimp only [zo];rw [h1,h2,h3,h4,h5,h50,h6]
 have hev_step (e:Fin n):q0 (zx n Bc w hBc e) Bstep:=by
   have hM_le:q7 n e.1<=n:=by
     unfold q7 qe;exact Nat.div_le_of_le_mul (by nlinarith)
   have hlen:q0 (fun st:Fin S2->Bool=>fun j:Fin Bc=>st ⟨j.1,by dsimp [S2];omega⟩) 0:=q0.p _;have hall:q0 (fun st:Fin S2->Bool=>fun j:Fin Bc=>st ⟨Bc+j.1,by dsimp [S2];omega⟩) 0:=q0.p _;have hpar:q0 (fun (st:Fin S2->Bool) (_:Fin 1)=>st ⟨Bc+Bc,by dsimp [S2];omega⟩) 0:=q0.p _;have hrem:q0 (fun st:Fin S2->Bool=>fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by dsimp [S2];omega⟩) 0:=q0.p _
   have hfc:=v5 (K:=2*q7 n e.1) (K₁:=2*n+1) (K₂:=n+1)
     (fun k a b p=>qx n (n-1-e.1) a.1 b.1 p (qi n (n-1-e.1)) k.1)
     hK1 hK2 hlen hall hpar hrem
   have hpair1:=q0.r (q0.id S2) hfc
   have hfin:q0 (fun q:Fin (S2+(1+Bc+w))->Bool =>
      let len:Fin Bc->Bool:=fun j=>q ⟨j.1,by dsimp [S2];omega⟩
      let allow:Fin Bc->Bool:=fun j=>q ⟨Bc+j.1,by dsimp [S2];omega⟩
      let par:Bool:=q ⟨Bc+Bc,by dsimp [S2];omega⟩
      let epA:Fin (n*Bc)->Bool:=fun j=>q ⟨Bc+Bc+1+w+j.1,by dsimp [S2];omega⟩
      let emA:Fin (n*Bc)->Bool:=fun j=>q ⟨Bc+Bc+1+w+n*Bc+j.1,by dsimp [S2];omega⟩
      let cid:Fin Bc->Bool:=fun j=>q ⟨S2+1+j.1,by omega⟩
      let rem':Fin w->Bool:=fun j=>q ⟨S2+1+Bc+j.1,by omega⟩
      let isNeg:=wi (q3 Bc (q7 n e.1)) cid
      let epVal:=zb isNeg cid (q3 Bc 0)
      let emVal:=zb isNeg (q3 Bc 0) (zm cid (q3 Bc (q7 n e.1)))
      let cnt:=qr epVal emVal
      let len':=qu Bc (q7 n e.1) (qe e.1) len cnt
      let allow':=qu Bc (q7 n e.1) (v2 (e.1+1)) allow emVal
      let par':=xor par (emVal ⟨0,hBc⟩)
      let epA':=qn (K:=n) (d:=Bc) (fun slot =>
        if slot.1=e.1 then epVal else q5 (K:=n) (d:=Bc) epA slot)
      let emA':=qn (K:=n) (d:=Bc) (fun slot =>
        if slot.1=e.1 then emVal else q5 (K:=n) (d:=Bc) emA slot)
      q1 (q1 (q1 (q1 (q1 len' allow') (fun _:Fin 1=>par')) rem') epA') emA')
      (q7 n e.1*(54*Bc)+80*Bc+10):=by
     have hcid0:q0 (fun q:Fin (S2+(1+Bc+w))->Bool=>fun j:Fin Bc=>q ⟨S2+1+j.1,by omega⟩) 0:=q0.p _;have hisNeg:=xo (q0.k (q3 Bc (q7 n e.1))) hcid0;have hepVal:=zg hisNeg hcid0 (q0.k (q3 Bc 0));have hemVal:=zg hisNeg (q0.k (q3 Bc 0)) (wx hcid0 (q0.k (q3 Bc (q7 n e.1))));have hpair2:=q0.r (q0.r (q0.id (S2+(1+Bc+w))) hepVal) hemVal
     let Q2:=S2+(1+Bc+w)
     have hfin2:q0 (fun y:Fin (Q2+Bc+Bc)->Bool =>
        let len:Fin Bc->Bool:=fun j=>y ⟨j.1,by dsimp [Q2,S2];omega⟩
        let allow:Fin Bc->Bool:=fun j=>y ⟨Bc+j.1,by dsimp [Q2,S2];omega⟩
        let par:Bool:=y ⟨Bc+Bc,by dsimp [Q2,S2];omega⟩
        let epA:Fin (n*Bc)->Bool:=fun j=>y ⟨Bc+Bc+1+w+j.1,by dsimp [Q2,S2];omega⟩
        let emA:Fin (n*Bc)->Bool:=fun j=>y ⟨Bc+Bc+1+w+n*Bc+j.1,by dsimp [Q2,S2];omega⟩
        let rem':Fin w->Bool:=fun j=>y ⟨S2+1+Bc+j.1,by dsimp [Q2];omega⟩
        let epVal:Fin Bc->Bool:=fun j=>y ⟨Q2+j.1,by omega⟩
        let emVal:Fin Bc->Bool:=fun j=>y ⟨Q2+Bc+j.1,by omega⟩
        let cnt:=qr epVal emVal
        let len':=qu Bc (q7 n e.1) (qe e.1) len cnt
        let allow':=qu Bc (q7 n e.1) (v2 (e.1+1)) allow emVal
        let par':=xor par (emVal ⟨0,hBc⟩)
        let epA':=qn (K:=n) (d:=Bc) (fun slot =>
          if slot.1=e.1 then epVal else q5 (K:=n) (d:=Bc) epA slot)
        let emA':=qn (K:=n) (d:=Bc) (fun slot =>
          if slot.1=e.1 then emVal else q5 (K:=n) (d:=Bc) emA slot)
        q1 (q1 (q1 (q1 (q1 len' allow') (fun _:Fin 1=>par')) rem') epA') emA')
        (q7 n e.1*(54*Bc)+13*Bc+4):=by
      have hlen0:q0 (fun y:Fin (Q2+Bc+Bc)->Bool=>fun j:Fin Bc=>y ⟨j.1,by dsimp [Q2,S2];omega⟩) 0:=q0.p _;have hall0:q0 (fun y:Fin (Q2+Bc+Bc)->Bool=>fun j:Fin Bc=>y ⟨Bc+j.1,by dsimp [Q2,S2];omega⟩) 0:=q0.p _;have hpar0:q0 (fun (y:Fin (Q2+Bc+Bc)->Bool) (_:Fin 1)=>y ⟨Bc+Bc,by dsimp [Q2,S2];omega⟩) 0:=q0.p _;have hrem'0:q0 (fun y:Fin (Q2+Bc+Bc)->Bool=>fun j:Fin w=>y ⟨S2+1+Bc+j.1,by dsimp [Q2];omega⟩) 0:=q0.p _;have hepV0:q0 (fun y:Fin (Q2+Bc+Bc)->Bool=>fun j:Fin Bc=>y ⟨Q2+j.1,by omega⟩) 0:=q0.p _;have hemV0:q0 (fun y:Fin (Q2+Bc+Bc)->Bool=>fun j:Fin Bc=>y ⟨Q2+Bc+j.1,by omega⟩) 0:=q0.p _;have hlen':=wa (M:=q7 n e.1) (C:=qe e.1) hlen0 (z8 hepV0 hemV0);have hall':=wa (M:=q7 n e.1) (C:=v2 (e.1+1)) hall0 hemV0;have hpar':=q0.x hpar0 (q0.b hemV0 ⟨0,hBc⟩)
      have hepA':q0 (fun y:Fin (Q2+Bc+Bc)->Bool =>
          qn (K:=n) (d:=Bc) (fun slot =>
            if slot.1=e.1 then fun j=>y ⟨Q2+j.1,by omega⟩
            else q5 (K:=n) (d:=Bc) (fun j=>y ⟨Bc+Bc+1+w+j.1,by dsimp [Q2,S2];omega⟩) slot)) 0:=by
        refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
        split_ifs
        . exact hepV0
        . exact qa (q0.p _) slot
      have hemA':q0 (fun y:Fin (Q2+Bc+Bc)->Bool =>
          qn (K:=n) (d:=Bc) (fun slot =>
            if slot.1=e.1 then fun j=>y ⟨Q2+Bc+j.1,by omega⟩
            else q5 (K:=n) (d:=Bc) (fun j=>y ⟨Bc+Bc+1+w+n*Bc+j.1,by dsimp [Q2,S2];omega⟩) slot)) 0:=by
        refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
        split_ifs
        . exact hemV0
        . exact qa (q0.p _) slot
      exact (q0.r (q0.r (q0.r (q0.r (q0.r hlen' hall') hpar') hrem'0) hepA') hemA').mono (by ring_nf;omega)
     refine ((q0.c hpair2 hfin2).mono (by omega)).congr (fun q=>?_)
     set epV:=zb (wi (q3 Bc (q7 n e.1)) (fun j=>q ⟨S2+1+j.1,by omega⟩)) (fun j=>q ⟨S2+1+j.1,by omega⟩) (q3 Bc 0);set emV:=zb (wi (q3 Bc (q7 n e.1)) (fun j=>q ⟨S2+1+j.1,by omega⟩)) (q3 Bc 0) (zm (fun j=>q ⟨S2+1+j.1,by omega⟩) (q3 Bc (q7 n e.1)))
     have ha:(fun j:Fin Bc=>q1 (q1 q epV) emV ⟨j.1,by dsimp [S2];omega⟩)=fun j=>q ⟨j.1,by dsimp [S2];omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [S2];omega),Zr (by have:=j.isLt;dsimp [S2];omega)]
     have hb:(fun j:Fin Bc=>q1 (q1 q epV) emV ⟨Bc+j.1,by dsimp [S2];omega⟩)=fun j=>q ⟨Bc+j.1,by dsimp [S2];omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [S2];omega),Zr (by have:=j.isLt;dsimp [S2];omega)]
     have hc:q1 (q1 q epV) emV ⟨Bc+Bc,by dsimp [S2];omega⟩=q ⟨Bc+Bc,by dsimp [S2];omega⟩:=by
      dsimp only [q1];rw [Zr (by dsimp [S2];omega),Zr (by dsimp [S2];omega)]
     have hd:(fun j:Fin (n*Bc)=>q1 (q1 q epV) emV ⟨Bc+Bc+1+w+j.1,by dsimp [S2];omega⟩)=fun j=>q ⟨Bc+Bc+1+w+j.1,by dsimp [S2];omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [S2];omega),Zr (by have:=j.isLt;dsimp [S2];omega)]
     have he':(fun j:Fin (n*Bc)=>q1 (q1 q epV) emV ⟨Bc+Bc+1+w+n*Bc+j.1,by dsimp [S2];omega⟩)=fun j=>q ⟨Bc+Bc+1+w+n*Bc+j.1,by dsimp [S2];omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [S2];omega),Zr (by have:=j.isLt;dsimp [S2];omega)]
     have hf:(fun j:Fin w=>q1 (q1 q epV) emV ⟨S2+1+Bc+j.1,by omega⟩)=fun j=>q ⟨S2+1+Bc+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega),Zr (by have:=j.isLt;omega)]
     have hg:(fun j:Fin Bc=>q1 (q1 q epV) emV ⟨Q2+j.1,by omega⟩)=epV:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;dsimp [Q2];omega),Zb (by dsimp [Q2];omega)];exact congrArg epV (Zx (by dsimp [Q2];omega))
     have hh:(fun j:Fin Bc=>q1 (q1 q epV) emV ⟨Q2+Bc+j.1,by omega⟩)=emV:=by
      funext j;dsimp only [q1];rw [Zb (by dsimp [Q2];omega)];exact congrArg emV (Zx (by dsimp [Q2];omega))
     have hh0:q1 (q1 q epV) emV ⟨Q2+Bc+0,by omega⟩=emV ⟨0,hBc⟩:=congrFun hh ⟨0,hBc⟩;dsimp only;rw [ha,hb,hc,hd,he',hf,hg,hh,hh0]
   refine ((q0.c hpair1 hfin).mono ?_).congr (fun st=>?_)
   . have hmul:(2*q7 n e.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+4*Bc+28*w+10) +
        q7 n e.1*(54*Bc) <=
        (2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10):=by
      have h1:q7 n e.1*(54*Bc)<=(2*q7 n e.1+1)*(60*Bc):=by nlinarith
      have h2:(2*q7 n e.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+4*Bc+28*w+10) +
          (2*q7 n e.1+1)*(60*Bc) =
          (2*q7 n e.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10):=by ring
      calc _<=(2*q7 n e.1+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10):=by linarith
        _<=_:=Zw _ (by omega)
     dsimp [Bstep];omega
   . set fc:=zk (K:=2*q7 n e.1) (K₁:=2*n+1) (K₂:=n+1)
      (fun k a b p=>qx n (n-1-e.1) a.1 b.1 p (qi n (n-1-e.1)) k.1)
      (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)
      (st ⟨Bc+Bc,by omega⟩) (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
     have h1:(fun j:Fin Bc=>q1 st fc ⟨j.1,by omega⟩)=fun j:Fin Bc=>st ⟨j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h2:(fun j:Fin Bc=>q1 st fc ⟨Bc+j.1,by omega⟩)=fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h3:q1 st fc ⟨Bc+Bc,by omega⟩=st ⟨Bc+Bc,by omega⟩:=by
      dsimp only [q1];rw [Zr (by omega)]
     have h4:(fun j:Fin (n*Bc)=>q1 st fc ⟨Bc+Bc+1+w+j.1,by omega⟩) =
        fun j:Fin (n*Bc)=>st ⟨Bc+Bc+1+w+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h5:(fun j:Fin (n*Bc)=>q1 st fc ⟨Bc+Bc+1+w+n*Bc+j.1,by omega⟩) =
        fun j:Fin (n*Bc)=>st ⟨Bc+Bc+1+w+n*Bc+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega)]
     have h6:(fun j:Fin Bc=>q1 st fc ⟨S2+1+j.1,by omega⟩)=fun j:Fin Bc=>fc ⟨1+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zb (by dsimp [S2];omega)];congr 1;exact Zx (by dsimp [S2];try omega)
     have h7:(fun j:Fin w=>q1 st fc ⟨S2+1+Bc+j.1,by omega⟩)=fun j:Fin w=>fc ⟨1+Bc+j.1,by omega⟩:=by
      funext j;dsimp only [q1];rw [Zb (by dsimp [S2];omega)];congr 1;exact Zx (by dsimp [S2];try omega)
     dsimp only [zx];rw [h1,h2,h3,h4,h5,h6,h7]
 have hodd_init:q0 (fun z:Fin w->Bool =>
     q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
      (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false)) (14*w) :=
   (q0.r (q0.r (q0.r (q0.r (q0.k _) (q0.k _)) (q0.k _))
     (wx (q0.id w) (q0.k _))) (q0.k _)).mono (by omega)
 have hodd_all:q0 (fun z:Fin w->Bool =>
     (List.finRange (4*n)).foldl (fun st o=>zo n Bc w hBc o st)
      (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
        (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))) (14*w+4*n*Bstep) :=
   q0.l _ (fun o _ st=>zo n Bc w hBc o st) hodd_init
     (fun o=>(q0.c (q0.p (fun j:Fin S1=>⟨w+j.1,by omega⟩)) (hodd_step o)).mono (by omega))
 have hev_all:q0 (fun stOdd:Fin S1->Bool =>
     (List.finRange n).foldl (fun st e=>zx n Bc w hBc e st)
      (q1 (q1 (q1 (q1 (q1
        (fun j:Fin Bc=>stOdd ⟨j.1,by dsimp [S1];omega⟩) (q3 Bc 0))
        (fun _:Fin 1=>stOdd ⟨Bc+Bc,by dsimp [S1];omega⟩))
        (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by dsimp [S1];omega⟩))
        (fun _:Fin (n*Bc)=>false)) (fun _:Fin (n*Bc)=>false))) (0+n*Bstep) :=
   q0.l _ (fun e _ st=>zx n Bc w hBc e st)
     ((q0.r (q0.r (q0.r (q0.r (q0.r
      (q0.p _) (q0.k _)) (q0.p _)) (q0.p _)) (q0.k _)) (q0.k _)).mono (by omega))
     (fun e=>(q0.c (q0.p (fun j:Fin S2=>⟨S1+j.1,by omega⟩)) (hev_step e)).mono (by omega))
 have hboth:=q0.r hodd_all (q0.c hodd_all hev_all)
 have hfinal:q0 (fun q:Fin (S1+S2)->Bool =>
     let oddArr:Fin (4*n*Bc)->Bool:=fun j=>q ⟨Bc+Bc+1+w+j.1,by dsimp [S1];omega⟩
     let epArr:Fin (n*Bc)->Bool:=fun j=>q ⟨S1+Bc+Bc+1+w+j.1,by dsimp [S2];omega⟩
     let emArr:Fin (n*Bc)->Bool:=fun j=>q ⟨S1+Bc+Bc+1+w+n*Bc+j.1,by dsimp [S2];omega⟩
     let fusBits:Fin Bc->Bool:=yd Bc (fun j:Fin w=>q ⟨S1+Bc+Bc+1+j.1,by dsimp [S2];omega⟩)
     qn (K:=6*n+1) (d:=Bc) (fun slot =>
      if h1:slot.1< 4*n then q5 (K:=4*n) (d:=Bc) oddArr ⟨slot.1,h1⟩
      else if h2:slot.1< 5*n then q5 (K:=n) (d:=Bc) epArr ⟨slot.1-4*n,by omega⟩
      else if h3:slot.1< 6*n then q5 (K:=n) (d:=Bc) emArr ⟨slot.1-5*n,by omega⟩
      else fusBits)) 0:=by
   refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
   split_ifs
   . exact qa (q0.p _) _
   . exact qa (q0.p _) _
   . exact qa (q0.p _) _
   . exact k5 (q0.p _)
 have hboth2:q0 (fun z:Fin w->Bool =>
     let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zo n Bc w hBc o st)
      (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
        (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))
     let stEv:=(List.finRange n).foldl (fun st e=>zx n Bc w hBc e st)
      (q1 (q1 (q1 (q1 (q1
        (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
        (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
        (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩))
        (fun _:Fin (n*Bc)=>false)) (fun _:Fin (n*Bc)=>false))
     q1 stOdd stEv) (14*w+5*n*Bstep):=by
   have hcomp:=q0.c hodd_all (q0.r (q0.id S1) hev_all)
   have hsumB:4*n*Bstep+n*Bstep=5*n*Bstep:=by ring
   exact (hcomp.mono (by omega)).congr (fun z=>rfl)
 refine ((q0.c hboth2 hfinal).mono (by dsimp [Bstep];omega)).congr (fun z=>?_)
 dsimp only [xi];congr 1;funext slot
 split_ifs with h1 h2 h3
 . funext b;dsimp only [q5,q1];rw [Zr (by have hb:=b.isLt;have:(slot.1+1)*Bc<=4*n*Bc:=Zw Bc h1;nlinarith)]
 . funext b;dsimp only [q5,q1];rw [Zb (by dsimp [S1];omega)];exact congrArg _ (Zx (by dsimp [S1];omega))
 . funext b;dsimp only [q5,q1];rw [Zb (by dsimp [S1];omega)];exact congrArg _ (Zx (by dsimp [S1];omega))
 . funext b;dsimp only [yd];split_ifs with hb
   . dsimp only [q1];rw [Zb (by dsimp [S1];omega)];exact congrArg _ (Zx (by dsimp [S1];omega))
   . rfl
lemma pi (n Bc w:ℕ) (hBc:0< Bc) (h4n:4*n< 2^Bc) (hw:v6 n<=2^w)
  (z:Fin w->Bool) (hz0:0< q2 w z) (hzl:q2 w z< v6 n) :
  let stOdd:=(List.finRange (4*n)).foldl (fun st o=>zo n Bc w hBc o st)
   (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
     (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))
  let lv:=q2 Bc (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩)
  let pv:=stOdd ⟨Bc+Bc,by omega⟩
  let rv:=q2 w (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩)
  let arr:Fin (4*n*Bc)->Bool:=fun j=>stOdd ⟨Bc+Bc+1+w+j.1,by omega⟩
  let uFull:=qq n (4*n) 0 0 false (q2 w z-1)
  lv<=2*n /\
  qi n n lv 0 pv<=qk n (4*n) 0 0 false /\
  rv< qi n n lv 0 pv /\
  (∀ o:Fin (4*n),q2 Bc (q5 (K:=4*n) (d:=Bc) arr o) =
   uFull.1 ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1)) /\
  (ze n n lv 0 pv rv).1=uFull.2.1 /\
  (ze n n lv 0 pv rv).2.1=uFull.2.2.1 /\
  (ze n n lv 0 pv rv).2.2=uFull.2.2.2:=by
 have hr0:q2 w z-1< qk n (4*n) 0 0 false:=by unfold v6 at hzl;omega
 have hbit0 (v:Fin Bc->Bool):v ⟨0,hBc⟩=decide (q2 Bc v %2=1):=by
  have h0:=congrFun (qm Bc v) ⟨0,hBc⟩;simpa [q3,Nat.testBit_zero] using h0.symm
 have hodd_inv:∀ t ≤ 4*n,
   let st:=((List.finRange (4*n)).take t).foldl (fun st o=>zo n Bc w hBc o st)
     (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
       (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))
   let lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩)
   let bv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)
   let pv:=st ⟨Bc+Bc,by omega⟩
   let rv:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
   let arr:Fin (4*n*Bc)->Bool:=fun j=>st ⟨Bc+Bc+1+w+j.1,by omega⟩
   lv<=2*n/\bv<=n /\
   qk n (4*n-t) lv bv pv<=qk n (4*n) 0 0 false /\
   rv< qk n (4*n-t) lv bv pv /\
   (let uFull:=qq n (4*n) 0 0 false (q2 w z-1)
    let uCur:=qq n (4*n-t) lv bv pv rv
    (∀ o:Fin (4*n),o.1< t->q2 Bc (q5 (K:=4*n) (d:=Bc) arr o) =
       uFull.1 ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1)) /\
    (∀ j c sig,t<=q6 n j c sig->uCur.1 j c sig=uFull.1 j c sig) /\
    uCur.2.1=uFull.2.1/\uCur.2.2.1=uFull.2.2.1/\uCur.2.2.2=uFull.2.2.2):=by
  intro t ht
  induction t with
  | zero =>
   simp only [Zn,Zi,Nat.sub_zero]
   have hlv:q2 Bc (fun j:Fin Bc=>q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨j.1,by omega⟩)=0:=by
     have h:(fun j:Fin Bc=>q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨j.1,by omega⟩)=q3 Bc 0:=by
       funext j;have:=j.isLt;simp only [q1,show j.1< Bc from this,show j.1< Bc+Bc by omega,show j.1< Bc+Bc+1 by omega,show j.1< Bc+Bc+1+w by omega,Zd]
     rw [h,q4 (by omega:0< 2^Bc)]
   have hbv:q2 Bc (fun j:Fin Bc=>q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨Bc+j.1,by omega⟩)=0:=by
     have h:(fun j:Fin Bc=>q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨Bc+j.1,by omega⟩)=q3 Bc 0:=by
       funext j;have:=j.isLt;simp only [q1,show Bc+j.1< Bc+Bc by omega,show Bc+j.1< Bc+Bc+1 by omega,show Bc+j.1< Bc+Bc+1+w by omega,show ¬ (Bc+j.1< Bc) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
     rw [h,q4 (by omega:0< 2^Bc)]
   have hpv:q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨Bc+Bc,by omega⟩=false:=by
     simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show Bc+Bc< Bc+Bc+1+w by omega,show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
   have hrv:q2 w (fun j:Fin w=>q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨Bc+Bc+1+j.1,by omega⟩)=q2 w z-1:=by
     have h:(fun j:Fin w=>q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false)) (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false) ⟨Bc+Bc+1+j.1,by omega⟩)=zm z (q3 w 1):=by
       funext j;have:=j.isLt;simp only [q1,show Bc+Bc+1+j.1< Bc+Bc+1+w by omega,show ¬ (Bc+Bc+1+j.1< Bc+Bc+1) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
     rw [h,wj _ _ (by rw [q4 (by omega:1< 2^w)];omega),q4 (by omega:1< 2^w)]
   rw [hlv,hbv,hpv,hrv];exact ⟨by omega,by omega,le_rfl,hr0,fun o ho=>by omega,fun _ _ _ _=>rfl,rfl,rfl,rfl⟩
  | succ t iht =>
   have htake:(List.finRange (4*n)).take (t+1)=(List.finRange (4*n)).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   set st:=((List.finRange (4*n)).take t).foldl (fun st o=>zo n Bc w hBc o st)
     (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
       (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))
   rcases iht (by omega) with ⟨ih_l,ih_b,ih_dp,ih_r,ih_arr,ih_u1,ih_ep,ih_em,ih_f⟩
   set lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩);set bv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩);set pv:=st ⟨Bc+Bc,by omega⟩;set rv:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩);set remSt:=4*n-1-t
   have hrem_eq:4*n-t=remSt+1:=by omega
   have hrem_sub:4*n-(remSt+1)=t:=by omega
   set M:=qv n t;have hM_le:M<=2*n:=Nat.div_le_self _ _;set wFn:=zc n remSt lv bv pv (qk n remSt)
   have hdp_eq:qk n (remSt+1) lv bv pv=ql wFn (M+1):=by
     simp only [qk,hrem_sub];rfl
   have hr_lt_ps:rv< ql wFn (M+1):=by rw [<- hdp_eq,<-hrem_eq];exact ih_r
   have hw_lt:∀ k< M+1,wFn k< 2^w:=by
     intro k hk;have hm:=xg wFn (show k+1<=M+1 by omega);rw [wf] at hm;rw [<- hdp_eq,<-hrem_eq] at hm;unfold v6 at hw;omega
   have hfc_spec:=vx (K:=M) (K₁:=2*n+1) (K₂:=n+1)
     (fun k a b p=>zc n remSt a.1 b.1 p (qk n remSt) k.1)
     (fun j=>st ⟨j.1,by omega⟩) (fun j=>st ⟨Bc+j.1,by omega⟩) pv
     (fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩)
     (by omega) (by omega) (by omega) wFn (fun k _=>rfl) hw_lt
   rcases (vu wFn (M+1) rv).1 hr_lt_ps with ⟨hfa1,hfa_lt,hfa_r,hfa_eq⟩
   set ch:=yi wFn M rv;have hch_eq:ch=(zw wFn (M+1) rv).2:=rfl
   have hfc_cnt:q2 Bc (fun j:Fin Bc=>(zk (K:=M) (K₁:=2*n+1) (K₂:=n+1)
       (fun k a b p=>zc n remSt a.1 b.1 p (qk n remSt) k.1)
       (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) pv
       (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)) ⟨1+j.1,by omega⟩)=ch.1:=hfc_spec.2.1 hfa1
   have hfc_rem:q2 w (fun j:Fin w=>(zk (K:=M) (K₁:=2*n+1) (K₂:=n+1)
       (fun k a b p=>zc n remSt a.1 b.1 p (qk n remSt) k.1)
       (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) pv
       (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)) ⟨1+Bc+j.1,by omega⟩)=ch.2:=hfc_spec.2.2
   have hw_ch:ch.2< wFn ch.1:=hfa_r
   have hch_valid:lv+ch.1*qs n t<=2*n /\
       (qh n t=false->bv+ch.1<=n)/\(qh n t=true->ch.1<=bv) /\
       ch.2< qk n remSt (lv+ch.1*qs n t)
         (if qh n t=false then bv+ch.1 else bv-ch.1)
         (xor pv (qf t&&decide (ch.1 %2=1))):=by
     dsimp only [wFn,zc] at hw_ch;rw [hrem_sub] at hw_ch
     cases hc:qh n t
     . simp only [hc,Zh] at hw_ch ⊢
       split_ifs at hw_ch with hok
       . exact ⟨hok.1,fun _=>hok.2,(fun h=>by cases h),hw_ch⟩
       . omega
     . simp only [hc,Bool.true_eq_false,Zj] at hw_ch ⊢
       split_ifs at hw_ch with hok
       . exact ⟨hok.1,(fun h=>by cases h),fun _=>hok.2,hw_ch⟩
       . omega
   have hdp_next:qk n remSt (lv+ch.1*qs n t)
       (if qh n t=false then bv+ch.1 else bv-ch.1)
       (xor pv (qf t&&decide (ch.1 %2=1)))<=qk n (4*n) 0 0 false:=by
     have h1:wFn ch.1=qk n remSt (lv+ch.1*qs n t)
         (if qh n t=false then bv+ch.1 else bv-ch.1)
         (xor pv (qf t&&decide (ch.1 %2=1))):=by
       dsimp only [wFn,zc];rw [hrem_sub]
       cases hc:qh n t
       . simp [hc,hch_valid.1,hch_valid.2.1 hc]
       . simp [hc,hch_valid.1,hch_valid.2.2.1 hc]
     have hch_lt:ch.1< M+1:=hfa_lt;have h2:=xg wFn (show ch.1+1<=M+1 by omega);rw [wf,<-hdp_eq,<-hrem_eq,h1] at h2;omega
   have hv_ext (a b:Fin Bc->Bool) (p:Bool) (r':Fin w->Bool) (ar:Fin (4*n*Bc)->Bool) :
       let s:=q1 (q1 (q1 (q1 a b) (fun _:Fin 1=>p)) r') ar
       (fun j:Fin Bc=>s ⟨j.1,by omega⟩)=a /\
       (fun j:Fin Bc=>s ⟨Bc+j.1,by omega⟩)=b /\
       s ⟨Bc+Bc,by omega⟩=p /\
       (fun j:Fin w=>s ⟨Bc+Bc+1+j.1,by omega⟩)=r' /\
       (fun j:Fin (4*n*Bc)=>s ⟨Bc+Bc+1+w+j.1,by omega⟩)=ar:=by
     refine ⟨?_,?_,?_,?_,?_⟩
     . funext j;have:=j.isLt;simp only [q1,show j.1< Bc from this,show j.1< Bc+Bc by omega,show j.1< Bc+Bc+1 by omega,show j.1< Bc+Bc+1+w by omega,Zd]
     . funext j;have:=j.isLt;simp only [q1,show Bc+j.1< Bc+Bc by omega,show Bc+j.1< Bc+Bc+1 by omega,show Bc+j.1< Bc+Bc+1+w by omega,show ¬ (Bc+j.1< Bc) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
     . simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show Bc+Bc< Bc+Bc+1+w by omega,show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
     . funext j;have:=j.isLt;simp only [q1,show Bc+Bc+1+j.1< Bc+Bc+1+w by omega,show ¬ (Bc+Bc+1+j.1< Bc+Bc+1) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
     . funext j;simp only [q1,show ¬ (Bc+Bc+1+w+j.1< Bc+Bc+1+w) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
   dsimp only [zo]
   rcases hv_ext _ _ _ _ _ with ⟨e1,e2,e3,e4,e5⟩
   rw [e1,e2,e3,e4,e5]
   set cntB:Fin Bc->Bool:=fun j=>(zk (K:=M) (K₁:=2*n+1) (K₂:=n+1)
       (fun k a b p=>zc n remSt a.1 b.1 p (qk n remSt) k.1)
       (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) pv
       (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)) ⟨1+j.1,by omega⟩
   have hcntB:q2 Bc cntB=ch.1:=hfc_cnt
   have hlen_n:q2 Bc (qu Bc M (qs n t) (fun j:Fin Bc=>st ⟨j.1,by omega⟩) cntB) =
       lv+ch.1*qs n t:=by
     rw [w0 Bc M (qs n t) _ _ (by omega) (by rw [hcntB,hch_eq];omega)
       (by rw [hcntB];have:=hch_valid.1;dsimp only [lv] at this;omega),hcntB]
   have hbal_n:q2 Bc (if qh n t=false then qr (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) cntB
       else zm (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) cntB) =
       if qh n t=false then bv+ch.1 else bv-ch.1:=by
     cases hc:qh n t
     . simp only [Zh];rw [qr,qc,hcntB];simp only [Zp,Zq];exact Zm (by have:=hch_valid.2.1 hc;dsimp only [bv] at this;omega)
     . simp only [Bool.true_eq_false,Zj];rw [wj _ _ (by rw [hcntB];exact hch_valid.2.2.1 hc),hcntB]
   have hpar_n:xor pv (qf t&&cntB ⟨0,hBc⟩)=xor pv (qf t&&decide (ch.1 %2=1)):=by
     rw [hbit0 cntB,hcntB]
   rw [hlen_n,hbal_n,hpar_n,hfc_rem]
   have hrem':4*n-(t+1)=remSt:=by omega
   rw [hrem']
   have hu_unfold:qq n (remSt+1) lv bv pv rv =
       let tail:=qq n remSt (lv+ch.1*qs n t)
         (if qh n t=false then bv+ch.1 else bv-ch.1)
         (xor pv (qf t&&decide (ch.1 %2=1))) ch.2
       (fun j c' sig'=>if q6 n j c' sig'=t then ch.1 else tail.1 j c' sig',
        tail.2.1,tail.2.2.1,tail.2.2.2):=by
     simp only [qq,hrem_sub];rfl
   rw [hrem_eq,hu_unfold] at ih_u1 ih_ep ih_em ih_f
   refine ⟨hch_valid.1,by cases hc:qh n t <;> simp [hc] <;> [exact hch_valid.2.1 hc;omega],
     hdp_next,hch_valid.2.2.2,?_,?_,ih_ep,ih_em,ih_f⟩
   . intro o ho;rw [qb]
     by_cases hot:o.1=t
     . rw [if_pos hot,hfc_cnt]
       have hidx0:q6 n ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1)=t:=by
         rw [(qp n o.1 o.isLt).2,hot]
       have h:=ih_u1 ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1) (by omega);dsimp only at h;rw [if_pos hidx0] at h;exact h
     . rw [if_neg hot];exact ih_arr o (by omega)
   . intro j c sig hge;have h:=ih_u1 j c sig (by omega);dsimp only at h;rw [if_neg (by omega)] at h;exact h
 have hodd_full:=hodd_inv (4*n) le_rfl;rw [Zk (by simp)] at hodd_full
 set stOdd:=(List.finRange (4*n)).foldl (fun st o=>zo n Bc w hBc o st)
  (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
   (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))
 rcases hodd_full with ⟨hod_l,_,hod_dp,hod_r,hod_arr,_,hod_ep,hod_em,hod_f⟩
 simp only [Nat.sub_self,qk,qq] at hod_dp hod_r hod_ep hod_em hod_f
 have hbv0:q2 Bc (fun j:Fin Bc=>stOdd ⟨Bc+j.1,by omega⟩)=0:=by
  by_contra hne;rw [if_neg hne] at hod_r;omega
 rw [if_pos hbv0] at hod_dp hod_r;exact ⟨hod_l,hod_dp,hod_r,fun o=>hod_arr o o.isLt,hod_ep,hod_em,hod_f⟩
lemma bp (n Bc w:ℕ) (hBc:0< Bc) (h4n:4*n< 2^Bc) (hw:v6 n<=2^w)
   (z:Fin w->Bool) (hz0:0< q2 w z) (hzl:q2 w z< v6 n) :
   let out:=xi n Bc w hBc z
   let u:=qq n (4*n) 0 0 false (q2 w z-1)
   (∀ o:Fin (4*n),q2 Bc (q5 (K:=6*n+1) (d:=Bc) out ⟨o.1,by omega⟩) =
    u.1 ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1)) /\
   (∀ j:Fin n,q2 Bc (q5 (K:=6*n+1) (d:=Bc) out ⟨4*n+j.1,by omega⟩)=u.2.1 j) /\
   (∀ j:Fin n,q2 Bc (q5 (K:=6*n+1) (d:=Bc) out ⟨5*n+j.1,by omega⟩)=u.2.2.1 j) /\
   q2 Bc (q5 (K:=6*n+1) (d:=Bc) out ⟨6*n,by omega⟩)=u.2.2.2:=by
 rcases pi n Bc w hBc h4n hw z hz0 hzl with ⟨hod_l,hod_dp,hod_r,hod_arr,hod_ep,hod_em,hod_f⟩
 have hbit0 (v:Fin Bc->Bool):v ⟨0,hBc⟩=decide (q2 Bc v %2=1):=by
   have h0:=congrFun (qm Bc v) ⟨0,hBc⟩;simpa [q3,Nat.testBit_zero] using h0.symm
 set stOdd:=(List.finRange (4*n)).foldl (fun st o=>zo n Bc w hBc o st)
   (q1 (q1 (q1 (q1 (q3 Bc 0) (q3 Bc 0)) (fun _:Fin 1=>false))
    (zm z (q3 w 1))) (fun _:Fin (4*n*Bc)=>false))
 set stEv0:Fin (Bc+Bc+1+w+n*Bc+n*Bc)->Bool :=
   q1 (q1 (q1 (q1 (q1
    (fun j:Fin Bc=>stOdd ⟨j.1,by omega⟩) (q3 Bc 0))
    (fun _:Fin 1=>stOdd ⟨Bc+Bc,by omega⟩))
    (fun j:Fin w=>stOdd ⟨Bc+Bc+1+j.1,by omega⟩))
    (fun _:Fin (n*Bc)=>false)) (fun _:Fin (n*Bc)=>false)
 have hev_inv:∀ t ≤ n,
    let st:=((List.finRange n).take t).foldl (fun st e=>zx n Bc w hBc e st) stEv0
    let lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩)
    let alv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩)
    let pv:=st ⟨Bc+Bc,by omega⟩
    let rv:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)
    let epA:Fin (n*Bc)->Bool:=fun j=>st ⟨Bc+Bc+1+w+j.1,by omega⟩
    let emA:Fin (n*Bc)->Bool:=fun j=>st ⟨Bc+Bc+1+w+n*Bc+j.1,by omega⟩
    lv<=2*n/\2*alv<=lv /\
    qi n (n-t) lv alv pv<=qk n (4*n) 0 0 false /\
    rv< qi n (n-t) lv alv pv /\
    (let uFull:=qq n (4*n) 0 0 false (q2 w z-1)
     let eCur:=ze n (n-t) lv alv pv rv
     (∀ j:Fin n,j.1< t->q2 Bc (q5 (K:=n) (d:=Bc) epA j)=uFull.2.1 j /\
       q2 Bc (q5 (K:=n) (d:=Bc) emA j)=uFull.2.2.1 j) /\
     (∀ j:Fin n,t<=j.1->eCur.1 j=uFull.2.1 j/\eCur.2.1 j=uFull.2.2.1 j) /\
     eCur.2.2=uFull.2.2.2):=by
   intro t ht
   induction t with
   | zero =>
    simp only [Zn,Zi,Nat.sub_zero]
    have hv0 (a b:Fin Bc->Bool) (p:Bool) (r':Fin w->Bool) (e1 e2:Fin (n*Bc)->Bool) :
        let s:=q1 (q1 (q1 (q1 (q1 a b) (fun _:Fin 1=>p)) r') e1) e2
        (fun j:Fin Bc=>s ⟨j.1,by omega⟩)=a /\
        (fun j:Fin Bc=>s ⟨Bc+j.1,by omega⟩)=b /\
        s ⟨Bc+Bc,by omega⟩=p /\
        (fun j:Fin w=>s ⟨Bc+Bc+1+j.1,by omega⟩)=r':=by
      refine ⟨?_,?_,?_,?_⟩
      . funext j;have:=j.isLt;simp only [q1,show j.1< Bc from this,show j.1< Bc+Bc by omega,show j.1< Bc+Bc+1 by omega,show j.1< Bc+Bc+1+w by omega,show j.1< Bc+Bc+1+w+n*Bc by omega,Zd]
      . funext j;have:=j.isLt;simp only [q1,show Bc+j.1< Bc+Bc by omega,show Bc+j.1< Bc+Bc+1 by omega,show Bc+j.1< Bc+Bc+1+w by omega,show Bc+j.1< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+j.1< Bc) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
      . simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show Bc+Bc< Bc+Bc+1+w by omega,show Bc+Bc< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
      . funext j;have:=j.isLt;simp only [q1,show Bc+Bc+1+j.1< Bc+Bc+1+w by omega,show Bc+Bc+1+j.1< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+Bc+1+j.1< Bc+Bc+1) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
    rcases hv0 _ _ _ _ _ _ with ⟨e1,e2,e3,e4⟩
    dsimp only [stEv0];rw [e1,e2,e3,e4,q4 (by omega:0< 2^Bc)]
    exact ⟨hod_l,by omega,hod_dp,hod_r,fun j hj=>by omega,
      fun j _=>⟨congrFun hod_ep j,congrFun hod_em j⟩,hod_f⟩
   | succ t iht =>
    have htake:(List.finRange n).take (t+1)=(List.finRange n).take t++[⟨t,by omega⟩]:=by
      rw [Zt (by simp;omega)];simp [Zg]
    rw [htake,Zl,Zo,Zi];set st:=((List.finRange n).take t).foldl (fun st e=>zx n Bc w hBc e st) stEv0
    rcases iht (by omega) with ⟨ih_l,ih_al,ih_dp,ih_r,ih_arr,ih_u,ih_f⟩
    set lv:=q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩);set alv:=q2 Bc (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩);set pv:=st ⟨Bc+Bc,by omega⟩;set rv:=q2 w (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩);set remSt:=n-1-t
    have hrem_eq:n-t=remSt+1:=by omega
    have hrem_sub:n-(remSt+1)=t:=by omega
    set M:=q7 n t
    have hM_le:M<=n:=by unfold M q7 qe;exact Nat.div_le_of_le_mul (by nlinarith)
    set wFn:=qx n remSt lv alv pv (qi n remSt)
    have hdp_eq:qi n (remSt+1) lv alv pv=ql wFn (2*M+1):=by
      simp only [qi,hrem_sub];rfl
    have hr_lt_ps:rv< ql wFn (2*M+1):=by rw [<- hdp_eq,<-hrem_eq];exact ih_r
    have hw_lt:∀ k< 2*M+1,wFn k< 2^w:=by
      intro k hk;have hm:=xg wFn (show k+1<=2*M+1 by omega);rw [wf] at hm;rw [<- hdp_eq,<-hrem_eq] at hm;unfold v6 at hw;omega
    have hfc_spec:=vx (K:=2*M) (K₁:=2*n+1) (K₂:=n+1)
      (fun k a b p=>qx n remSt a.1 b.1 p (qi n remSt) k.1)
      (fun j=>st ⟨j.1,by omega⟩) (fun j=>st ⟨Bc+j.1,by omega⟩) pv
      (fun j=>st ⟨Bc+Bc+1+j.1,by omega⟩)
      (by omega) (by omega) (by omega) wFn (fun k _=>rfl) hw_lt
    rcases (vu wFn (2*M+1) rv).1 hr_lt_ps with ⟨hfa1,hfa_lt,hfa_r,_⟩
    set ch:=yi wFn (2*M) rv;have hfc_cnt:=hfc_spec.2.1 hfa1
    have hfc_cid:q2 Bc (fun j:Fin Bc=>(zk (K:=2*M) (K₁:=2*n+1) (K₂:=n+1)
        (fun k a b p=>qx n remSt a.1 b.1 p (qi n remSt) k.1)
        (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) pv
        (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)) ⟨1+j.1,by omega⟩)=ch.1:=hfc_cnt
    have hfc_rem:q2 w (fun j:Fin w=>(zk (K:=2*M) (K₁:=2*n+1) (K₂:=n+1)
        (fun k a b p=>qx n remSt a.1 b.1 p (qi n remSt) k.1)
        (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) pv
        (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)) ⟨1+Bc+j.1,by omega⟩)=ch.2:=hfc_spec.2.2
    set cnt:=qw M ch.1;set isNeg:=z5 M ch.1
    set epV:=if isNeg then 0 else cnt
    set emV:=if isNeg then cnt else 0
    have hch_lt:ch.1< 2*M+1:=hfa_lt
    rcases jv M ch.1 (by omega) with ⟨_,hsum_c,hcnt_le_M,_⟩
    have hvalid_e:lv+cnt*qe t<=2*n /\
        ch.2< qi n remSt (lv+cnt*qe t)
          (alv+if isNeg then cnt*v2 (t+1) else 0)
          (xor pv (isNeg&&decide (cnt %2=1))):=by
      change ch.2< qx n remSt lv alv pv (qi n remSt) ch.1 at hfa_r;dsimp only [qx] at hfa_r;rw [hrem_sub] at hfa_r
      change ch.2< (if lv+cnt*qe t<=2*n then
        qi n remSt (lv+cnt*qe t) (alv+if isNeg then cnt*v2 (t+1) else 0)
          (xor pv (isNeg&&decide (cnt %2=1))) else 0) at hfa_r
      by_cases hok:lv+cnt*qe t<=2*n
      . rw [if_pos hok] at hfa_r;exact ⟨hok,hfa_r⟩
      . rw [if_neg hok] at hfa_r;omega
    have hdp_next:qi n remSt (lv+cnt*qe t)
        (alv+if isNeg then cnt*v2 (t+1) else 0)
        (xor pv (isNeg&&decide (cnt %2=1)))<=qk n (4*n) 0 0 false:=by
      have h1:wFn ch.1=qi n remSt (lv+cnt*qe t)
          (alv+if isNeg then cnt*v2 (t+1) else 0)
          (xor pv (isNeg&&decide (cnt %2=1))):=by
        dsimp only [wFn,qx];rw [hrem_sub];change (if lv+cnt*qe t<=2*n then _ else 0)=_;rw [if_pos hvalid_e.1]
      have h2:=xg wFn (show ch.1+1<=2*M+1 by omega);rw [wf,<-hdp_eq,<-hrem_eq,h1] at h2;omega
    have hv_ext (a b:Fin Bc->Bool) (p:Bool) (r':Fin w->Bool) (e1 e2:Fin (n*Bc)->Bool) :
        let s:=q1 (q1 (q1 (q1 (q1 a b) (fun _:Fin 1=>p)) r') e1) e2
        (fun j:Fin Bc=>s ⟨j.1,by omega⟩)=a /\
        (fun j:Fin Bc=>s ⟨Bc+j.1,by omega⟩)=b /\
        s ⟨Bc+Bc,by omega⟩=p /\
        (fun j:Fin w=>s ⟨Bc+Bc+1+j.1,by omega⟩)=r' /\
        (fun j:Fin (n*Bc)=>s ⟨Bc+Bc+1+w+j.1,by omega⟩)=e1 /\
        (fun j:Fin (n*Bc)=>s ⟨Bc+Bc+1+w+n*Bc+j.1,by omega⟩)=e2:=by
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      . funext j;have:=j.isLt;simp only [q1,show j.1< Bc from this,show j.1< Bc+Bc by omega,show j.1< Bc+Bc+1 by omega,show j.1< Bc+Bc+1+w by omega,show j.1< Bc+Bc+1+w+n*Bc by omega,Zd]
      . funext j;have:=j.isLt;simp only [q1,show Bc+j.1< Bc+Bc by omega,show Bc+j.1< Bc+Bc+1 by omega,show Bc+j.1< Bc+Bc+1+w by omega,show Bc+j.1< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+j.1< Bc) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
      . simp only [q1,show Bc+Bc< Bc+Bc+1 by omega,show Bc+Bc< Bc+Bc+1+w by omega,show Bc+Bc< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+Bc< Bc+Bc) by omega,Zd,Zf]
      . funext j;have:=j.isLt;simp only [q1,show Bc+Bc+1+j.1< Bc+Bc+1+w by omega,show Bc+Bc+1+j.1< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+Bc+1+j.1< Bc+Bc+1) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
      . funext j;have:=j.isLt;simp only [q1,show Bc+Bc+1+w+j.1< Bc+Bc+1+w+n*Bc by omega,show ¬ (Bc+Bc+1+w+j.1< Bc+Bc+1+w) by omega,Zd,Zf];congr 1;exact Zx (by dsimp;omega)
      . funext j;simp only [q1,show ¬ (Bc+Bc+1+w+n*Bc+j.1< Bc+Bc+1+w+n*Bc) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
    dsimp only [zx]
    rcases hv_ext _ _ _ _ _ _ with ⟨e1,e2,e3,e4,e5,e6⟩
    rw [e1,e2,e3,e4,e5,e6]
    set cidB:Fin Bc->Bool:=fun j=>(zk (K:=2*M) (K₁:=2*n+1) (K₂:=n+1)
        (fun k a b p=>qx n remSt a.1 b.1 p (qi n remSt) k.1)
        (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) pv
        (fun j:Fin w=>st ⟨Bc+Bc+1+j.1,by omega⟩)) ⟨1+j.1,by omega⟩
    have hcidB:q2 Bc cidB=ch.1:=hfc_cid
    have hneg_b:wi (q3 Bc M) cidB=isNeg:=by
      rw [x8,q4 (by omega:M< 2^Bc),hcidB];rfl
    have hep_b:q2 Bc (zb (wi (q3 Bc M) cidB) cidB (q3 Bc 0))=epV:=by
      rw [hneg_b];cases hn':isNeg
      . simp only [zn,epV,hn',Zj,cnt,qw]
        rw [hcidB];have hleM:ch.1<=M:=by unfold isNeg z5 at hn';simp at hn';omega
        by_cases h0:ch.1=0 <;> simp [h0,hleM]
      . simp [zz,epV,hn',q4 (by omega:0< 2^Bc)]
    have hem_b:q2 Bc (zb (wi (q3 Bc M) cidB) (q3 Bc 0) (zm cidB (q3 Bc M)))=emV:=by
      rw [hneg_b];cases hn':isNeg
      . simp [zn,emV,hn',q4 (by omega:0< 2^Bc)]
      . have hgtM:M< ch.1:=of_decide_eq_true (by unfold isNeg z5 at hn';exact hn')
        rw [zz,wj _ _ (by rw [hcidB,q4 (by omega:M< 2^Bc)];omega),
          hcidB,q4 (by omega:M< 2^Bc)]
        simp [emV,hn',cnt,qw,show ch.1≠0 by omega,show ¬ (ch.1<=M) by omega]
    set epB:Fin Bc->Bool:=zb (wi (q3 Bc M) cidB) cidB (q3 Bc 0)
    set emB:Fin Bc->Bool:=zb (wi (q3 Bc M) cidB) (q3 Bc 0) (zm cidB (q3 Bc M))
    have hcnt_b:q2 Bc (qr epB emB)=cnt:=by
      rw [qr,qc,hep_b,hem_b,hsum_c];simp only [Zp,Zq];exact Zm (by omega)
    have hdal_eq:emV*v2 (t+1)=if isNeg then cnt*v2 (t+1) else 0:=by
      dsimp only [emV];by_cases h:isNeg=true <;> simp [h]
    have h2al:2*(alv+emV*v2 (t+1))<=lv+cnt*qe t:=by
      have hv:2*v2 (t+1)<=qe t:=by unfold qe;have:=vb (t+1);omega
      have hem_le:emV<=cnt:=by dsimp only [emV];split_ifs <;> omega
      have hm1:emV*(2*v2 (t+1))<=cnt*qe t:=Nat.mul_le_mul hem_le hv
      have hm2:2*(emV*v2 (t+1))=emV*(2*v2 (t+1)):=by ring
      omega
    have hlen_n:q2 Bc (qu Bc M (qe t) (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (qr epB emB)) =
        lv+cnt*qe t:=by
      rw [w0 Bc M (qe t) _ _ (by omega) (by rw [hcnt_b];exact hcnt_le_M)
        (by rw [hcnt_b];have:=hvalid_e.1;dsimp only [lv] at this;omega),hcnt_b]
    have hall_n:q2 Bc (qu Bc M (v2 (t+1)) (fun j:Fin Bc=>st ⟨Bc+j.1,by omega⟩) emB) =
        alv+emV*v2 (t+1):=by
      rw [w0 Bc M (v2 (t+1)) _ _ (by omega)
        (by rw [hem_b];dsimp only [emV];split_ifs <;> omega)
        (by rw [hem_b];have:=hvalid_e.1;dsimp only [alv,lv] at h2al this;omega),hem_b]
    have hpar_n:xor pv (emB ⟨0,hBc⟩)=xor pv (isNeg&&decide (cnt %2=1)):=by
      rw [hbit0 emB,hem_b];dsimp only [emV];by_cases h:isNeg=true <;> simp [h]
    rw [hlen_n,hall_n,hpar_n,hfc_rem]
    have hrem':n-(t+1)=remSt:=by omega
    rw [hrem']
    have hu_unfold:ze n (remSt+1) lv alv pv rv =
        let tail:=ze n remSt (lv+cnt*qe t) (alv+emV*v2 (t+1))
          (xor pv (isNeg&&decide (cnt %2=1))) ch.2
        (fun j=>if j.1=t then epV else tail.1 j,
         fun j=>if j.1=t then emV else tail.2.1 j,tail.2.2):=by
      simp only [ze,hrem_sub,hdal_eq];rfl
    rw [hrem_eq,hu_unfold] at ih_u ih_f
    refine ⟨hvalid_e.1,h2al,by rw [hdal_eq];exact hdp_next,by rw [hdal_eq];exact hvalid_e.2,?_,?_,ih_f⟩
    . intro j hj;rw [qb,qb]
      by_cases hjt:j.1=t
      . rw [if_pos hjt,if_pos hjt,hep_b,hem_b];have h:=ih_u j (by omega);dsimp only at h;rw [if_pos hjt,if_pos hjt] at h;exact h
      . rw [if_neg hjt,if_neg hjt];exact ih_arr j (by omega)
    . intro j hj;have h:=ih_u j (by omega);dsimp only at h;rw [if_neg (by omega),if_neg (by omega)] at h;exact h
 have hev_full:=hev_inv n le_rfl;rw [Zk (by simp)] at hev_full
 rcases hev_full with ⟨_,_,_,_,hev_arr,_,hev_f⟩
 simp only [Nat.sub_self,ze] at hev_f
 refine ⟨?_,?_,?_,?_⟩
 . intro o;dsimp only [xi];rw [qb,Zr o.isLt];exact hod_arr o
 . intro j;have hj:=j.isLt;dsimp only [xi];rw [qb,Zb (by dsimp;omega),Zr (by dsimp;omega)];have heq:(⟨4*n+j.1-4*n,by omega⟩:Fin n)=j:=Zx (by dsimp;omega);rw [heq];exact (hev_arr j j.isLt).1
 . intro j;have hj:=j.isLt;dsimp only [xi];rw [qb,Zb (by dsimp;omega),Zb (by dsimp;omega),Zr (by dsimp;omega)];have heq:(⟨5*n+j.1-5*n,by omega⟩:Fin n)=j:=Zx (by dsimp;omega);rw [heq];exact (hev_arr j j.isLt).2
 . dsimp only [xi];rw [qb,Zb (by dsimp;omega),Zb (by dsimp;omega),Zb (by dsimp;omega)]
   have hlt_fus:q2 w (fun j:Fin w=>((List.finRange n).foldl (fun st e=>zx n Bc w hBc e st) stEv0) ⟨Bc+Bc+1+j.1,by omega⟩)< 2^Bc:=by
    rw [hev_f];have hv:=(xq n (q2 w z) hzl).1;simp only [zy,show q2 w z≠0 by omega,Zj,xp,ju] at hv
    have hphi_le:wz n (qq n (4*n) 0 0 false (q2 w z-1)).2.2.1<=n:=by
      set emU:=(qq n (4*n) 0 0 false (q2 w z-1)).2.2.1;set epU:=(qq n (4*n) 0 0 false (q2 w z-1)).2.1
      have h2:2*wz n emU<=zj n epU emU:=by
        unfold wz zj;rw [Finset.mul_sum];apply Finset.sum_le_sum;intro j _
        have hv2:2*v2 (j.1+1)<=2*(j.1+1):=by have:=vb (j.1+1);omega
        have hm1:2*(emU j*v2 (j.1+1))=emU j*(2*v2 (j.1+1)):=by ring
        have hm2:=Nat.mul_le_mul_left (emU j) hv2
        have hm3:emU j*(2*(j.1+1))<=2*(j.1+1)*(epU j+emU j):=by
          rw [Nat.mul_comm];exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        omega
      have hlen_hv:yn n (qq n (4*n) 0 0 false (q2 w z-1)).1+zj n epU emU=2*n:=hv.2.1;omega
    have hfus_hv:(qq n (4*n) 0 0 false (q2 w z-1)).2.2.2 <=
        wz n (qq n (4*n) 0 0 false (q2 w z-1)).2.2.1:=hv.2.2.2.2
    omega
   rw [ji _ hlt_fus];exact hev_f
def w8 (n Bc:ℕ) (j:Fin n) (st:Fin ((2*n+1)*Bc)->Bool) :
  Fin ((2*n+1)*Bc)->Bool :=
 if h:(j.1+1)%2=0 then
  let emJ:=q5 (K:=2*n+1) (d:=Bc) st ⟨n+j.1,by omega⟩
  let remF:=q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩
  let s:=ym emJ remF
  let jh:=(j.1+1)/2-1
  qn (K:=2*n+1) (d:=Bc) (fun slot =>
   if slot.1=jh then qr (q5 (K:=2*n+1) (d:=Bc) st slot) s
   else if slot.1=n+j.1 then zm emJ s
   else if slot.1=n+jh then qr (q5 (K:=2*n+1) (d:=Bc) st slot) s
   else if slot.1=2*n then zm remF s
   else q5 (K:=2*n+1) (d:=Bc) st slot)
 else st
def yk (n Bc:ℕ) (st0:Fin ((2*n+1)*Bc)->Bool) :
  Fin ((2*n+1)*Bc)->Bool :=
 (List.finRange n).foldl (fun st i=>w8 n Bc ⟨n-1-i.1,by omega⟩ st) st0
lemma ks (n Bc:ℕ) :
  q0 (yk n Bc) (n*(70*Bc)):=by
 have hstep (j:Fin n):q0 (w8 n Bc j) (70*Bc):=by
  unfold w8
  split_ifs with hev
  . let jh:=(j.1+1)/2-1
    have hjh:jh< n:=by have:=j.isLt;dsimp [jh];omega
    have hpr:q0 (fun st:Fin ((2*n+1)*Bc)->Bool =>
        ym (q5 (K:=2*n+1) (d:=Bc) st ⟨n+j.1,by omega⟩)
              (q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩)) (14*Bc) :=
      (ky (qa (q0.id _) _) (qa (q0.id _) _)).mono (by omega)
    have hp1:=q0.r (q0.id ((2*n+1)*Bc)) hpr
    have hbase:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool =>
        let st:Fin ((2*n+1)*Bc)->Bool:=fun a=>u ⟨a.1,by omega⟩
        let s:Fin Bc->Bool:=fun b=>u ⟨(2*n+1)*Bc+b.1,by omega⟩
        q1 (q1 (q1 (q1 st
          (qr (q5 (K:=2*n+1) (d:=Bc) st ⟨jh,by omega⟩) s))
          (zm (q5 (K:=2*n+1) (d:=Bc) st ⟨n+j.1,by omega⟩) s))
          (qr (q5 (K:=2*n+1) (d:=Bc) st ⟨n+jh,by omega⟩) s))
          (zm (q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩) s)) (56*Bc):=by
      have hst0:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool=>fun a:Fin ((2*n+1)*Bc)=>u ⟨a.1,by omega⟩) 0:=q0.p _;have hs0:q0 (fun u:Fin ((2*n+1)*Bc+Bc)->Bool=>fun b:Fin Bc=>u ⟨(2*n+1)*Bc+b.1,by omega⟩) 0:=q0.p _
      exact (q0.r (q0.r (q0.r (q0.r hst0
        (z8 (qa hst0 ⟨jh,by omega⟩) hs0))
        (wx (qa hst0 ⟨n+j.1,by omega⟩) hs0))
        (z8 (qa hst0 ⟨n+jh,by omega⟩) hs0))
        (wx (qa hst0 ⟨2*n,by omega⟩) hs0)).mono (by omega)
    have hasm:q0 (fun q:Fin ((((2*n+1)*Bc+Bc)+Bc)+Bc+Bc)->Bool =>
        qn (K:=2*n+1) (d:=Bc) (fun slot =>
          if slot.1=jh then fun b=>q ⟨(2*n+1)*Bc+b.1,by omega⟩
          else if slot.1=n+j.1 then fun b=>q ⟨(2*n+1)*Bc+Bc+b.1,by omega⟩
          else if slot.1=n+jh then fun b=>q ⟨(2*n+1)*Bc+Bc+Bc+b.1,by omega⟩
          else if slot.1=2*n then fun b=>q ⟨(2*n+1)*Bc+Bc+Bc+Bc+b.1,by omega⟩
          else q5 (K:=2*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) slot)) 0:=by
      refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
      split_ifs
      . exact q0.p _
      . exact q0.p _
      . exact q0.p _
      . exact q0.p _
      . exact qa (q0.p _) slot
    refine ((q0.c (q0.c hp1 hbase) hasm).mono (by omega)).congr (fun st=>?_)
    congr 1;funext slot
    have hst_g (s:Fin (2*n+1)) :
        q5 (K:=2*n+1) (d:=Bc) (fun a=>q1 st (ym (q5 (K:=2*n+1) (d:=Bc) st ⟨n+j.1,by omega⟩)
          (q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩)) ⟨a.1,by omega⟩) s=q5 st s:=by
      funext b;have hs:=s.isLt;have hb:=b.isLt;have:(s.1+1)*Bc<=(2*n+1)*Bc:=Zw Bc hs;simp only [q5,q1,show s.1*Bc+b.1< (2*n+1)*Bc by nlinarith,Zd]
    have hs_g:(fun b:Fin Bc=>q1 st (ym (q5 (K:=2*n+1) (d:=Bc) st ⟨n+j.1,by omega⟩)
        (q5 (K:=2*n+1) (d:=Bc) st ⟨2*n,by omega⟩)) ⟨(2*n+1)*Bc+b.1,by omega⟩) =
        ym (q5 st ⟨n+j.1,by omega⟩) (q5 st ⟨2*n,by omega⟩):=by
      funext b;simp only [q1,show ¬ ((2*n+1)*Bc+b.1< (2*n+1)*Bc) by omega,Zf];congr 1;exact Zx (by dsimp;omega)
    dsimp only [q1] at hst_g hs_g;have hjh_def:(j.1+1)/2-1=jh:=rfl
    by_cases h1:slot.1=jh
    . simp only [hjh_def,h1,Zh];funext b;have hb:=b.isLt;have heq:slot=⟨jh,by omega⟩:=Zx h1;have ha:q5 (K:=2*n+1) (d:=Bc) st ⟨jh,by omega⟩=q5 st slot:=congrArg (q5 st) heq.symm;dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zr (by omega),Zb (by omega)];rw [hst_g,hs_g,ha];congr 1;exact Zx (by dsimp;omega)
    . simp only [hjh_def,h1,Zj]
      by_cases h2:slot.1=n+j.1
      . simp only [h2,Zh];funext b;have hb:=b.isLt;dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zb (by omega)];rw [hst_g,hs_g];congr 1;exact Zx (by dsimp;omega)
      . simp only [h2,Zj]
        by_cases h3:slot.1=n+jh
        . simp only [h3,Zh];funext b;have hb:=b.isLt;have heq:slot=⟨n+jh,by omega⟩:=Zx h3;have ha:q5 (K:=2*n+1) (d:=Bc) st ⟨n+jh,by omega⟩=q5 st slot:=congrArg (q5 st) heq.symm;dsimp only [q1];rw [Zr (by omega),Zb (by omega)];rw [hst_g,hs_g,ha];congr 1;exact Zx (by dsimp;omega)
        . simp only [h3,Zj]
          by_cases h4:slot.1=2*n
          . simp only [h4,Zh];funext b;dsimp only [q1];rw [Zb (by omega),hst_g,hs_g];congr 1;exact Zx (by dsimp;omega)
          . simp only [h4,Zj]
            funext b;have hs:=slot.isLt;have hb:=b.isLt;have hlt:slot.1*Bc+b.1< (2*n+1)*Bc:=by
             have:(slot.1+1)*Bc<=(2*n+1)*Bc:=Zw Bc hs;nlinarith
            dsimp only [q5,q1];rw [Zr (by omega),Zr (by omega),Zr (by omega),Zr hlt];exact congrFun (hst_g slot) b
  . exact (q0.id _).mono (by omega)
 exact (q0.l (B₀:=0) (Bs:=70*Bc) (fun st0=>st0) (fun i _ st=>w8 n Bc ⟨n-1-i.1,by omega⟩ st)
  (q0.id _) (fun i=>(q0.c (q0.p (fun b:Fin ((2*n+1)*Bc)=>⟨(2*n+1)*Bc+b.1,by omega⟩))
    (hstep ⟨n-1-i.1,by omega⟩)).mono (by omega))).mono (by omega)
lemma ps (n Bc:ℕ) (hBc:4*n< 2^Bc)
  (ep em:Fin n->ℕ) (fus:ℕ)
  (hlen:zj n ep em<=2*n) (hfus:fus<=wz n em)
  (st0:Fin ((2*n+1)*Bc)->Bool)
  (hep0:∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) st0 ⟨j.1,by omega⟩)=ep j)
  (hem0:∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) st0 ⟨n+j.1,by omega⟩)=em j)
  (hfus0:q2 Bc (q5 (K:=2*n+1) (d:=Bc) st0 ⟨2*n,by omega⟩)=fus) :
  let resC:=yk n Bc st0
  let res:=x6 n ep em fus
  (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) resC ⟨j.1,by omega⟩)=res.1 j) /\
  (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) resC ⟨n+j.1,by omega⟩)=res.2.1 j):=by
 have hinv:∀ t ≤ n,
   let stC:=((List.finRange n).take t).foldl (fun st i=>w8 n Bc ⟨n-1-i.1,by omega⟩ st) st0
   let st:=((List.finRange n).take t).foldl (fun st i=>ww n ⟨n-1-i.1,by omega⟩ st) (ep,em,fus)
   (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) stC ⟨j.1,by omega⟩)=st.1 j) /\
   (∀ j:Fin n,q2 Bc (q5 (K:=2*n+1) (d:=Bc) stC ⟨n+j.1,by omega⟩)=st.2.1 j) /\
   q2 Bc (q5 (K:=2*n+1) (d:=Bc) stC ⟨2*n,by omega⟩)=st.2.2 /\
   zj n st.1 st.2.1=zj n ep em /\
   st.2.2<=∑ k:Fin n,if k.1< n-t then st.2.1 k*v2 (k.1+1) else 0:=by
  intro t ht
  induction t with
  | zero=>exact ⟨hep0,hem0,hfus0,rfl,by simpa [wz] using hfus⟩
  | succ t iht =>
   have htake:(List.finRange n).take (t+1)=(List.finRange n).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi,
       Zl,Zo,Zi]
   set stC:=((List.finRange n).take t).foldl (fun st i=>w8 n Bc ⟨n-1-i.1,by omega⟩ st) st0;set st:=((List.finRange n).take t).foldl (fun st i=>ww n ⟨n-1-i.1,by omega⟩ st) (ep,em,fus)
   rcases iht (by omega) with ⟨ih1,ih2,ih3,ihlen,ihrem⟩
   set j:Fin n:=⟨n-1-t,by omega⟩
   have hle_eq:(∑ k:Fin n,if k.1<=j.1 then st.2.1 k*v2 (k.1+1) else 0) =
       (∑ k:Fin n,if k.1< n-t then st.2.1 k*v2 (k.1+1) else 0):=by
     apply Zc rfl;intro k _
     by_cases h:k.1< n-t <;> simp [h,j,show k.1<=n-1-t ↔ k.1< n-t by omega]
   have hstep:=k4 n (fun _ _ _=>0) j st.1 st.2.1 st.2.2 (by rw [hle_eq];exact ihrem)
   have hst_le (k:Fin n):st.1 k+st.2.1 k<=n:=by
     have h1:=Finset.single_le_sum (f:=fun k:Fin n=>2*(k.1+1)*(st.1 k+st.2.1 k))
       (fun _ _=>Nat.zero_le _) (Zu k)
     unfold zj at ihlen hlen;nlinarith
   refine ⟨?_,?_,?_,hstep.2.1.trans ihlen,by simpa [j,show n-1-t=n-(t+1) by omega] using hstep.2.2.2.2⟩
   . intro k;dsimp only [w8,ww]
     split_ifs with hev
     . rw [qb]
       set jh:Fin n:=⟨(j.1+1)/2-1,by omega⟩
       have hjh_eq:(j.1+1)/2-1=jh.1:=rfl
       have hs_val:q2 Bc (ym (q5 (K:=2*n+1) (d:=Bc) stC ⟨n+j.1,by omega⟩)
           (q5 (K:=2*n+1) (d:=Bc) stC ⟨2*n,by omega⟩))=min (st.2.1 j) st.2.2:=by
         rw [v0,ih2 j,ih3]
       by_cases hkh:k=jh
       . subst hkh;simp only [hjh_eq,Zh];rw [qr,qc,ih1 jh,hs_val];have h1:=hst_le jh;have h2:=hst_le j;simp [Zm (by omega:st.1 jh+min (st.2.1 j) st.2.2< 2^Bc)]
       . have hne:k.1≠jh.1:=fun h=>hkh (Zx h)
         simp only [hjh_eq,hkh,hne,show k.1≠n+j.1 by omega,show k.1≠n+jh.1 by omega,
           show k.1≠2*n by omega,Zj]
         exact ih1 k
     . exact ih1 k
   . intro k;dsimp only [w8,ww]
     split_ifs with hev
     . rw [qb]
       set jh:Fin n:=⟨(j.1+1)/2-1,by omega⟩
       have hjh_eq:(j.1+1)/2-1=jh.1:=rfl
       have hjh_lt:jh.1< j.1:=by dsimp [jh];omega
       have hs_val:q2 Bc (ym (q5 (K:=2*n+1) (d:=Bc) stC ⟨n+j.1,by omega⟩)
           (q5 (K:=2*n+1) (d:=Bc) stC ⟨2*n,by omega⟩))=min (st.2.1 j) st.2.2:=by
         rw [v0,ih2 j,ih3]
       by_cases hkj:k=j
       . subst hkj;simp only [hjh_eq,show n+j.1≠jh.1 by omega,Zj,Zh];rw [wj _ _ (by rw [ih2 j,hs_val];exact Nat.min_le_left _ _),ih2 j,hs_val]
       . by_cases hkh:k=jh
         . subst hkh
           simp only [hjh_eq,show n+jh.1≠jh.1 by omega,show n+jh.1≠n+j.1 by omega,
            hkj,Zj,Zh]
           rw [qr,qc,ih2 jh,hs_val];have h1:=hst_le jh;have h2:=hst_le j;simp [Zm (by omega:st.2.1 jh+min (st.2.1 j) st.2.2< 2^Bc)]
         . have hne1:k.1≠j.1:=fun h=>hkj (Zx h)
           have hne2:k.1≠jh.1:=fun h=>hkh (Zx h)
           simp only [hjh_eq,show n+k.1≠jh.1 by omega,show n+k.1≠n+j.1 by omega,
            show n+k.1≠n+jh.1 by omega,show n+k.1≠2*n by omega,
            hkj,hkh,Zj]
           exact ih2 k
     . exact ih2 k
   . dsimp only [w8,ww]
     split_ifs with hev
     . rw [qb]
       set jh:Fin n:=⟨(j.1+1)/2-1,by omega⟩
       have hjh_eq:(j.1+1)/2-1=jh.1:=rfl
       have hs_val:q2 Bc (ym (q5 (K:=2*n+1) (d:=Bc) stC ⟨n+j.1,by omega⟩)
           (q5 (K:=2*n+1) (d:=Bc) stC ⟨2*n,by omega⟩))=min (st.2.1 j) st.2.2:=by
         rw [v0,ih2 j,ih3]
       simp only [hjh_eq,show 2*n≠jh.1 by omega,show 2*n≠n+j.1 by omega,
         show 2*n≠n+jh.1 by omega,Zj,Zh]
       rw [wj _ _ (by rw [ih3,hs_val];exact Nat.min_le_right _ _),ih3,hs_val]
     . exact ih3
 have hfull:=hinv n le_rfl;rw [Zk (by simp)] at hfull;exact ⟨hfull.1,hfull.2.1⟩
def yl {K r:ℕ} (v:Fin K->Bool) (en:Bool) (idx:Fin r->Bool) (b:Bool):Fin K->Bool :=
 fun j =>
  let hit:=en&&yb idx (q3 r j.1)
  (!hit&&v j)||(hit&&b)
lemma vg {K r:ℕ} (v:Fin K->Bool) (en:Bool) (idx:Fin r->Bool) (b:Bool)
   (hK:K<=2^r) (j:Fin K) :
   yl v en idx b j=if en=true/\j.1=q2 r idx then b else v j:=by
 dsimp only [yl]
 have heq:yb idx (q3 r j.1)=true ↔ j.1=q2 r idx:=by
   rw [p7];constructor
   . intro h;rw [h,q4 (lt_of_lt_of_le j.isLt hK)]
   . intro h;rw [h,qm]
 cases en
 . simp
 . by_cases hj:j.1=q2 r idx
   . rw [heq.mpr hj];simp [hj]
   . have hf:yb idx (q3 r j.1)=false:=by
      cases h:yb idx (q3 r j.1)
      . rfl
      . exact absurd (heq.mp h) hj
     rw [hf];simp [hj]
lemma k6 {m K r Bv Be Bi Bb:ℕ}
  {v:(Fin m->Bool)->(Fin K->Bool)} {en b:(Fin m->Bool)->Bool}
  {idx:(Fin m->Bool)->(Fin r->Bool)}
  (hv:q0 v Bv) (he:q0 (fun x (_:Fin 1)=>en x) Be)
  (hi:q0 idx Bi) (hb:q0 (fun x (_:Fin 1)=>b x) Bb) :
  q0 (fun x=>yl (v x) (en x) (idx x) (b x)) (Bv+Be+Bi+Bb+K*(4*r+7)):=by
 have hbase:q0 (fun u:Fin (K+1+r+1)->Bool =>
   yl (fun a:Fin K=>u ⟨a.1,by omega⟩) (u ⟨K,by omega⟩)
    (fun a:Fin r=>u ⟨K+1+a.1,by omega⟩) (u ⟨K+1+r,by omega⟩))
   (K*(4*r+7)):=by
  apply q0.f;intro j;have hvj:q0 (fun (u:Fin (K+1+r+1)->Bool) (_:Fin 1)=>u ⟨j.1,by omega⟩) 0:=q0.p _;have he0:q0 (fun (u:Fin (K+1+r+1)->Bool) (_:Fin 1)=>u ⟨K,by omega⟩) 0:=q0.p _;have hi0:q0 (fun u:Fin (K+1+r+1)->Bool=>fun a:Fin r=>u ⟨K+1+a.1,by omega⟩) 0:=q0.p _;have hb0:q0 (fun (u:Fin (K+1+r+1)->Bool) (_:Fin 1)=>u ⟨K+1+r,by omega⟩) 0:=q0.p _;have hhit:=q0.a he0 (xb j.1 hi0);exact (q0.boolOr (q0.a (q0.boolNot hhit) hvj) (q0.a hhit hb0)).mono (by omega)
 have hp:=q0.r (q0.r (q0.r hv he) hi) hb
 refine ((q0.c hp hbase).mono (by omega)).congr (fun x=>?_)
 have h1:(fun a:Fin K=>q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (fun _:Fin 1=>b x) ⟨a.1,by omega⟩)=v x:=by
  funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;omega),Zr (by have:=a.isLt;omega),Zr a.isLt]
 have h2:q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (fun _:Fin 1=>b x) ⟨K,by omega⟩=en x:=by
  dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zb (by omega)]
 have h3:(fun a:Fin r=>q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (fun _:Fin 1=>b x) ⟨K+1+a.1,by omega⟩)=idx x:=by
  funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;omega),Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have h4:q1 (q1 (q1 (v x) (fun _:Fin 1=>en x)) (idx x)) (fun _:Fin 1=>b x) ⟨K+1+r,by omega⟩=b x:=by
  dsimp only [q1];rw [Zb (by omega)]
 rw [h1,h2,h3,h4]
def qz (n Bc:ℕ) (st:Fin (Bc+1+2*n+2*n)->Bool)
  (en:Bool) (L:Fin Bc->Bool) (sig:Bool):Fin (Bc+1+2*n+2*n)->Bool :=
 let pos:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
 let bit:Bool:=st ⟨Bc,by omega⟩
 let isPin:Fin (2*n)->Bool:=fun k=>st ⟨Bc+1+k.1,by omega⟩
 let pinVal:Fin (2*n)->Bool:=fun k=>st ⟨Bc+1+2*n+k.1,by omega⟩
 let isPin':=yl isPin en pos true
 let pinVal':=yl pinVal en pos bit
 let pos':=zb en pos (qr pos L)
 let bit':=xor bit (en&&sig)
 q1 (q1 (q1 pos' (fun _:Fin 1=>bit')) isPin') pinVal'
lemma yf {m n Bc Bst Be BL Bs:ℕ}
  {st:(Fin m->Bool)->(Fin (Bc+1+2*n+2*n)->Bool)}
  {en sig:(Fin m->Bool)->Bool} {L:(Fin m->Bool)->(Fin Bc->Bool)}
  (hst:q0 st Bst) (he:q0 (fun x (_:Fin 1)=>en x) Be)
  (hL:q0 L BL) (hs:q0 (fun x (_:Fin 1)=>sig x) Bs) :
  q0 (fun x=>qz n Bc (st x) (en x) (L x) (sig x))
   (Bst+Be+BL+Bs+(4*n*(4*Bc+7)+17*Bc+5)):=by
 let S:=Bc+1+2*n+2*n
 have hbase:q0 (fun u:Fin (S+1+Bc+1)->Bool =>
   qz n Bc (fun a:Fin S=>u ⟨a.1,by omega⟩) (u ⟨S,by omega⟩)
    (fun a:Fin Bc=>u ⟨S+1+a.1,by omega⟩) (u ⟨S+1+Bc,by omega⟩))
   (4*n*(4*Bc+7)+17*Bc+5):=by
  have hpos:q0 (fun u:Fin (S+1+Bc+1)->Bool=>fun j:Fin Bc=>u ⟨j.1,by dsimp [S];omega⟩) 0:=q0.p _;have hbit:q0 (fun (u:Fin (S+1+Bc+1)->Bool) (_:Fin 1)=>u ⟨Bc,by dsimp [S];omega⟩) 0:=q0.p _;have his:q0 (fun u:Fin (S+1+Bc+1)->Bool=>fun k:Fin (2*n)=>u ⟨Bc+1+k.1,by dsimp [S];omega⟩) 0:=q0.p _;have hval:q0 (fun u:Fin (S+1+Bc+1)->Bool=>fun k:Fin (2*n)=>u ⟨Bc+1+2*n+k.1,by dsimp [S];omega⟩) 0:=q0.p _;have he0:q0 (fun (u:Fin (S+1+Bc+1)->Bool) (_:Fin 1)=>u ⟨S,by omega⟩) 0:=q0.p _;have hL0:q0 (fun u:Fin (S+1+Bc+1)->Bool=>fun j:Fin Bc=>u ⟨S+1+j.1,by omega⟩) 0:=q0.p _;have hs0:q0 (fun (u:Fin (S+1+Bc+1)->Bool) (_:Fin 1)=>u ⟨S+1+Bc,by omega⟩) 0:=q0.p _;have his':=k6 his he0 hpos (q0.k (fun _=>true));have hval':=k6 hval he0 hpos hbit;have hpos':=zg he0 hpos (z8 hpos hL0);have hbit':=q0.x hbit (q0.a he0 hs0);have hcomb:=q0.r (q0.r (q0.r hpos' hbit') his') hval'
  have hsum:2*n*(4*Bc+7)+2*n*(4*Bc+7)=4*n*(4*Bc+7):=by ring
  exact (hcomb.mono (by omega)).congr (fun u=>rfl)
 have hp:=q0.r (q0.r (q0.r hst he) hL) hs
 refine ((q0.c hp hbase).mono (by omega)).congr (fun x=>?_)
 have h1:(fun a:Fin S=>q1 (q1 (q1 (st x) (fun _:Fin 1=>en x)) (L x)) (fun _:Fin 1=>sig x) ⟨a.1,by omega⟩)=st x:=by
  funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;dsimp [S] at this ⊢;omega),Zr (by have:=a.isLt;dsimp [S] at this ⊢;omega),Zr a.isLt]
 have h2:q1 (q1 (q1 (st x) (fun _:Fin 1=>en x)) (L x)) (fun _:Fin 1=>sig x) ⟨S,by omega⟩=en x:=by
  dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zb (by omega)]
 have h3:(fun a:Fin Bc=>q1 (q1 (q1 (st x) (fun _:Fin 1=>en x)) (L x)) (fun _:Fin 1=>sig x) ⟨S+1+a.1,by omega⟩)=L x:=by
  funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;omega),Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have h4:q1 (q1 (q1 (st x) (fun _:Fin 1=>en x)) (L x)) (fun _:Fin 1=>sig x) ⟨S+1+Bc,by omega⟩=sig x:=by
  dsimp only [q1];rw [Zb (by omega)]
 rw [h1,h2,h3,h4]
def y5 (n Bc:ℕ) (st:Fin (Bc+1+2*n+2*n)->Bool)
  (pos:ℕ) (bit:Bool) (p:Fin (2*n)->Option Bool):Prop :=
 q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩)=pos /\
 st ⟨Bc,by omega⟩=bit /\
 ∀ k:Fin (2*n),
  st ⟨Bc+1+k.1,by omega⟩=(p k).isSome /\
  (st ⟨Bc+1+k.1,by omega⟩=true->p k=some (st ⟨Bc+1+2*n+k.1,by omega⟩))
lemma v7 {n Bc:ℕ} (pos':Fin Bc->Bool) (bit':Bool)
   (isPin' pinVal':Fin (2*n)->Bool) :
   let s:=q1 (q1 (q1 pos' (fun _:Fin 1=>bit')) isPin') pinVal'
   (fun j:Fin Bc=>s ⟨j.1,by omega⟩)=pos' /\
   s ⟨Bc,by omega⟩=bit' /\
   (∀ k:Fin (2*n),s ⟨Bc+1+k.1,by omega⟩=isPin' k) /\
   (∀ k:Fin (2*n),s ⟨Bc+1+2*n+k.1,by omega⟩=pinVal' k):=by
 refine ⟨?_,?_,?_,?_⟩
 . funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega),Zr (by have:=j.isLt;omega),Zr j.isLt]
 . dsimp only [q1];rw [Zr (by omega),Zr (by omega),Zb (by omega)]
 . intro k;dsimp only [q1];rw [Zr (by have:=k.isLt;omega),Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 . intro k;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
lemma yp (n Bc:ℕ) (h2n:2*n<=2^Bc)
   (st:Fin (Bc+1+2*n+2*n)->Bool) (L:Fin Bc->Bool) (sig:Bool)
   (pos:ℕ) (bit:Bool) (p:Fin (2*n)->Option Bool)
   (hrep:y5 n Bc st pos bit p) :
   y5 n Bc (qz n Bc st false L sig) pos bit p:=by
 rcases hrep with ⟨hpos,hbit,hpin⟩
 dsimp only [qz]
 rcases v7 (zb false (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (qr (fun j:Fin Bc=>st ⟨j.1,by omega⟩) L))
   (xor (st ⟨Bc,by omega⟩) (false&&sig))
   (yl (fun k:Fin (2*n)=>st ⟨Bc+1+k.1,by omega⟩) false (fun j:Fin Bc=>st ⟨j.1,by omega⟩) true)
   (yl (fun k:Fin (2*n)=>st ⟨Bc+1+2*n+k.1,by omega⟩) false (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (st ⟨Bc,by omega⟩)) with ⟨e1,e2,e3,e4⟩
 refine ⟨?_,?_,fun k=>?_⟩
 . rw [e1,zn];exact hpos
 . rw [e2];simpa using hbit
 . rw [e3 k,e4 k,vg _ _ _ _ h2n k,vg _ _ _ _ h2n k]
   simp only [Ze,false_and,Zj];exact hpin k
lemma yy (n Bc:ℕ) (h2n:2*n<=2^Bc)
   (st:Fin (Bc+1+2*n+2*n)->Bool) (L:Fin Bc->Bool) (sig:Bool)
   (pos:ℕ) (bit:Bool) (p:Fin (2*n)->Option Bool)
   (hrep:y5 n Bc st pos bit p) (hlt:pos+q2 Bc L< 2^Bc) :
   y5 n Bc (qz n Bc st true L sig)
     (pos+q2 Bc L) (xor bit sig) (fun k=>if k.1=pos then some bit else p k):=by
 rcases hrep with ⟨hpos,hbit,hpin⟩
 dsimp only [qz]
 rcases v7 (zb true (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (qr (fun j:Fin Bc=>st ⟨j.1,by omega⟩) L))
   (xor (st ⟨Bc,by omega⟩) (true&&sig))
   (yl (fun k:Fin (2*n)=>st ⟨Bc+1+k.1,by omega⟩) true (fun j:Fin Bc=>st ⟨j.1,by omega⟩) true)
   (yl (fun k:Fin (2*n)=>st ⟨Bc+1+2*n+k.1,by omega⟩) true (fun j:Fin Bc=>st ⟨j.1,by omega⟩) (st ⟨Bc,by omega⟩)) with ⟨e1,e2,e3,e4⟩
 refine ⟨?_,?_,fun k=>?_⟩
 . rw [e1,zz,qr,qc,hpos];simp [Zm hlt]
 . rw [e2,hbit];simp
 . rw [e3 k,e4 k,vg _ _ _ _ h2n k,vg _ _ _ _ h2n k,hpos,hbit]
   by_cases hk:k.1=pos
   . simp [hk]
   . simp [hk];exact hpin k
lemma ya (n:ℕ) (hn:0< n) (l₁ l₂:List (ℕ × Bool))
  (pos:ℕ) (bit:Bool) (p:Fin (2*n)->Option Bool) :
  qg n hn (l₁++l₂) pos bit p =
  qg n hn l₂ (pos+(l₁.map Prod.fst).sum) (l₁.foldl (fun b a=>xor b a.2) bit)
   (qg n hn l₁ pos bit p):=by
 induction l₁ generalizing pos bit p with
 | nil=>simp [qg]
 | cons a as ih =>
  rcases a with ⟨L,sig⟩
  simp only [List.cons_append,qg,List.map_cons,List.sum_cons,Zo,ih,Nat.add_assoc]
def x9 (n Bc L:ℕ) (sig:Bool) (cnt:Fin Bc->Bool)
  (st0:Fin (Bc+1+2*n+2*n)->Bool):Fin (Bc+1+2*n+2*n)->Bool :=
 (List.finRange n).foldl (fun st copy =>
  qz n Bc st (wi (q3 Bc copy.1) cnt) (q3 Bc L) sig) st0
lemma kd {m n Bc Bst Bcnt:ℕ} (L:ℕ) (sig:Bool)
  {cnt:(Fin m->Bool)->(Fin Bc->Bool)}
  {st0:(Fin m->Bool)->(Fin (Bc+1+2*n+2*n)->Bool)}
  (hcnt:q0 cnt Bcnt) (hst0:q0 st0 Bst) :
  q0 (fun x=>x9 n Bc L sig (cnt x) (st0 x))
   (Bcnt+Bst+n*(4*n*(4*Bc+7)+27*Bc+5)):=by
 let S:=Bc+1+2*n+2*n
 have hbase:q0 (fun u:Fin (Bc+S)->Bool =>
   x9 n Bc L sig (fun j:Fin Bc=>u ⟨j.1,by omega⟩) (fun a:Fin S=>u ⟨Bc+a.1,by omega⟩))
   (0+n*(4*n*(4*Bc+7)+27*Bc+5)):=by
  refine q0.l (B₀:=0) (Bs:=4*n*(4*Bc+7)+27*Bc+5)
   (fun u=>fun a:Fin S=>u ⟨Bc+a.1,by omega⟩)
   (fun copy u st=>qz n Bc st (wi (q3 Bc copy.1) (fun j:Fin Bc=>u ⟨j.1,by omega⟩)) (q3 Bc L) sig)
   (q0.p _)
   (fun copy =>
    let hst:q0 (fun q:Fin ((Bc+S)+S)->Bool=>fun a:Fin S=>q ⟨Bc+S+a.1,by omega⟩) 0:=q0.p _
    let hc:q0 (fun q:Fin ((Bc+S)+S)->Bool=>fun j:Fin Bc=>q ⟨j.1,by omega⟩) 0:=q0.p _
    let hen:=xo (q0.k (q3 Bc copy.1)) hc
    (yf hst hen (q0.k _) (q0.k _)).mono (by omega))
 refine ((q0.c (q0.r hcnt hst0) hbase).mono (by omega)).congr (fun x=>?_)
 have h1:(fun j:Fin Bc=>q1 (cnt x) (st0 x) ⟨j.1,by omega⟩)=cnt x:=by
  funext j;dsimp only [q1];rw [Zr j.isLt]
 have h2:(fun a:Fin S=>q1 (cnt x) (st0 x) ⟨Bc+a.1,by omega⟩)=st0 x:=by
  funext a;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 rw [h1,h2]
lemma jc (n Bc L:ℕ) (hn:0< n) (h4n:4*n< 2^Bc) (hL:L< 2^Bc) (sig:Bool)
  (cnt:Fin Bc->Bool) (st0:Fin (Bc+1+2*n+2*n)->Bool)
  (pos:ℕ) (bit:Bool) (p:Fin (2*n)->Option Bool)
  (hrep:y5 n Bc st0 pos bit p)
  (hcnt:q2 Bc cnt<=n) (hlt:pos+q2 Bc cnt*L< 2^Bc) :
  let l:=List.replicate (q2 Bc cnt) (L,sig)
  y5 n Bc (x9 n Bc L sig cnt st0)
   (pos+(l.map Prod.fst).sum) (l.foldl (fun b a=>xor b a.2) bit) (qg n hn l pos bit p):=by
 have hinv:∀ t ≤ n,
   let st:=((List.finRange n).take t).foldl (fun st copy =>
     qz n Bc st (wi (q3 Bc copy.1) cnt) (q3 Bc L) sig) st0
   let l:=List.replicate (min t (q2 Bc cnt)) (L,sig)
   y5 n Bc st (pos+(l.map Prod.fst).sum) (l.foldl (fun b a=>xor b a.2) bit) (qg n hn l pos bit p):=by
  intro t ht
  induction t with
  | zero=>simp [qg];exact hrep
  | succ t iht =>
   have htake:(List.finRange n).take (t+1)=(List.finRange n).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi];have ih:=iht (by omega);rw [x8,q4 (by omega:t< 2^Bc)]
   by_cases hlt':t< q2 Bc cnt
   . rw [decide_eq_true hlt']
     have hm1:min t (q2 Bc cnt)=t:=Nat.min_eq_left (by omega)
     have hm2:min (t+1) (q2 Bc cnt)=t+1:=Nat.min_eq_left (by omega)
     rw [hm1] at ih;rw [hm2]
     have hsum_t:((List.replicate t (L,sig)).map Prod.fst).sum=t*L:=by
      simp [Zy,Zz]
     have hlt_step:pos+((List.replicate t (L,sig)).map Prod.fst).sum+q2 Bc (q3 Bc L)< 2^Bc:=by
      rw [hsum_t,q4 hL];nlinarith
     have h1:=yy n Bc (by omega) _ (q3 Bc L) sig _ _ _ ih hlt_step;rw [q4 hL] at h1
     have hrep_snoc:List.replicate (t+1) (L,sig)=List.replicate t (L,sig)++[(L,sig)]:=by
      rw [List.replicate_succ']
     dsimp only;rw [hrep_snoc,ya,Za,Zs,Zl];simpa [qg,Nat.add_assoc] using h1
   . rw [decide_eq_false hlt']
     have hm1:min t (q2 Bc cnt)=q2 Bc cnt:=Nat.min_eq_right (by omega)
     have hm2:min (t+1) (q2 Bc cnt)=q2 Bc cnt:=Nat.min_eq_right (by omega)
     rw [hm1] at ih;rw [hm2];exact yp n Bc (by omega) _ (q3 Bc L) sig _ _ _ ih
 have hfull:=hinv n le_rfl;rw [Zk (by simp),Nat.min_eq_right hcnt] at hfull;exact hfull
def xt (n Bc L:ℕ) (sig:Bool) (cnt:Fin Bc->Bool)
  (st0:Fin (Bc+n*(Bc+1))->Bool):Fin (Bc+n*(Bc+1))->Bool :=
 (List.finRange n).foldl (fun st copy =>
  let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
  let arr:Fin (n*(Bc+1))->Bool:=fun a=>st ⟨Bc+a.1,by omega⟩
  let en:=wi (q3 Bc copy.1) cnt
  let entry:Fin (Bc+1)->Bool:=q1 (q3 Bc L) (fun _:Fin 1=>sig)
  let arr':=yx (K:=n) (d:=Bc+1) arr en len entry
  let len':=zb en len (qr len (q3 Bc 1))
  q1 len' arr') st0
lemma ka {m n Bc Bst Bcnt:ℕ} (L:ℕ) (sig:Bool)
  {cnt:(Fin m->Bool)->(Fin Bc->Bool)}
  {st0:(Fin m->Bool)->(Fin (Bc+n*(Bc+1))->Bool)}
  (hcnt:q0 cnt Bcnt) (hst0:q0 st0 Bst) :
  q0 (fun x=>xt n Bc L sig (cnt x) (st0 x))
   (Bcnt+Bst+n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))):=by
 let S:=Bc+n*(Bc+1)
 have hbase:q0 (fun u:Fin (Bc+S)->Bool =>
   xt n Bc L sig (fun j:Fin Bc=>u ⟨j.1,by omega⟩) (fun a:Fin S=>u ⟨Bc+a.1,by omega⟩))
   (0+n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))):=by
  refine q0.l (B₀:=0) (Bs:=37*Bc+n*(2*Bc+4*(Bc+1)+1))
   (fun u=>fun a:Fin S=>u ⟨Bc+a.1,by omega⟩)
   (fun copy u st =>
    let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
    let arr:Fin (n*(Bc+1))->Bool:=fun a=>st ⟨Bc+a.1,by omega⟩
    let en:=wi (q3 Bc copy.1) (fun j:Fin Bc=>u ⟨j.1,by omega⟩)
    let entry:Fin (Bc+1)->Bool:=q1 (q3 Bc L) (fun _:Fin 1=>sig)
    let arr':=yx (K:=n) (d:=Bc+1) arr en len entry
    let len':=zb en len (qr len (q3 Bc 1))
    q1 len' arr')
   (q0.p _)
   (fun copy =>
    let hc:q0 (fun q:Fin ((Bc+S)+S)->Bool=>fun j:Fin Bc=>q ⟨j.1,by omega⟩) 0:=q0.p _
    let hlen:q0 (fun q:Fin ((Bc+S)+S)->Bool=>fun j:Fin Bc=>q ⟨Bc+S+j.1,by dsimp [S];omega⟩) 0:=q0.p _
    let harr:q0 (fun q:Fin ((Bc+S)+S)->Bool=>fun a:Fin (n*(Bc+1))=>q ⟨Bc+S+Bc+a.1,by dsimp [S];omega⟩) 0:=q0.p _
    let hen:=xo (q0.k (q3 Bc copy.1)) hc
    let harr':=pf harr hen hlen (q0.k _)
    let hlen':=zg hen hlen (z8 hlen (q0.k _))
    ((q0.r hlen' harr').mono (by omega)).congr (fun q=>by
     have ha:(fun a:Fin (n*(Bc+1))=>q ⟨Bc+S+Bc+a.1,by dsimp [S];omega⟩) =
       (fun a:Fin (n*(Bc+1))=>q ⟨Bc+S+(Bc+a.1),by dsimp [S];omega⟩):=by
      funext a;congr 1;exact Zx (by dsimp;omega)
     rw [ha]))
 refine ((q0.c (q0.r hcnt hst0) hbase).mono (by omega)).congr (fun x=>?_)
 have h1:(fun j:Fin Bc=>q1 (cnt x) (st0 x) ⟨j.1,by omega⟩)=cnt x:=by
  funext j;dsimp only [q1];rw [Zr j.isLt]
 have h2:(fun a:Fin S=>q1 (cnt x) (st0 x) ⟨Bc+a.1,by omega⟩)=st0 x:=by
  funext a;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 rw [h1,h2]
def vk (n Bc:ℕ) (st:Fin (Bc+n*(Bc+1))->Bool) (l:List (ℕ × Bool)):Prop :=
 q2 Bc (fun j:Fin Bc=>st ⟨j.1,by omega⟩)=l.length /\
 ∀ i:Fin n,(hi:i.1< l.length) ->
  q2 Bc (fun j:Fin Bc=>q5 (K:=n) (d:=Bc+1) (fun a=>st ⟨Bc+a.1,by omega⟩) i ⟨j.1,by omega⟩)=l[i.1].1 /\
  q5 (K:=n) (d:=Bc+1) (fun a=>st ⟨Bc+a.1,by omega⟩) i ⟨Bc,by omega⟩=l[i.1].2
lemma j1 (n Bc L:ℕ) (h4n:4*n< 2^Bc) (hL:L< 2^Bc) (sig:Bool)
  (cnt:Fin Bc->Bool) (st0:Fin (Bc+n*(Bc+1))->Bool) (l:List (ℕ × Bool))
  (hrep:vk n Bc st0 l) (hfit:l.length+q2 Bc cnt<=n) :
  vk n Bc (xt n Bc L sig cnt st0) (l++List.replicate (q2 Bc cnt) (L,sig)):=by
 have hinv:∀ t ≤ n,
   vk n Bc (((List.finRange n).take t).foldl (fun st copy =>
     let len:Fin Bc->Bool:=fun j=>st ⟨j.1,by omega⟩
     let arr:Fin (n*(Bc+1))->Bool:=fun a=>st ⟨Bc+a.1,by omega⟩
     let en:=wi (q3 Bc copy.1) cnt
     let entry:Fin (Bc+1)->Bool:=q1 (q3 Bc L) (fun _:Fin 1=>sig)
     let arr':=yx (K:=n) (d:=Bc+1) arr en len entry
     let len':=zb en len (qr len (q3 Bc 1))
     q1 len' arr') st0) (l++List.replicate (min t (q2 Bc cnt)) (L,sig)):=by
  intro t ht
  induction t with
  | zero=>simp;exact hrep
  | succ t iht =>
   have htake:(List.finRange n).take (t+1)=(List.finRange n).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi]
   rcases iht (by omega) with ⟨ih_len,ih_el⟩
   set st:=((List.finRange n).take t).foldl _ st0
   have hv_ext (a:Fin Bc->Bool) (b:Fin (n*(Bc+1))->Bool) :
       (fun j:Fin Bc=>q1 a b ⟨j.1,by omega⟩)=a /\
       (fun j:Fin (n*(Bc+1))=>q1 a b ⟨Bc+j.1,by omega⟩)=b:=by
     refine ⟨?_,?_⟩
     . funext j;dsimp only [q1];rw [Zr j.isLt]
     . funext j;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
   rw [x8,q4 (by omega:t< 2^Bc)]
   by_cases hlt':t< q2 Bc cnt
   . rw [decide_eq_true hlt']
     have hm1:min t (q2 Bc cnt)=t:=Nat.min_eq_left (by omega)
     have hm2:min (t+1) (q2 Bc cnt)=t+1:=Nat.min_eq_left (by omega)
     rw [hm1] at ih_len ih_el;rw [hm2]
     rcases hv_ext _ _ with ⟨e1,e2⟩
     refine ⟨?_,?_⟩
     . rw [e1,zz,qr,qc,ih_len,q4 (by omega:1< 2^Bc)];simp only [Zp,Zq,List.length_append,List.length_replicate] at ih_len ⊢;rw [Zm (by omega)];omega
     . intro i hi;rw [e2,jx _ _ _ _ (by omega:n<=2^Bc) i,ih_len]
       have hlen_old:(l++List.replicate t (L,sig)).length=l.length+t:=by simp
       have hrep_snoc:l++List.replicate (t+1) (L,sig)=(l++List.replicate t (L,sig))++[(L,sig)]:=by
         rw [List.replicate_succ',List.append_assoc]
       by_cases hie:i.1=(l++List.replicate t (L,sig)).length
       . rw [if_pos ⟨rfl,hie⟩]
         have hL_eq:(fun j:Fin Bc=>q1 (q3 Bc L) (fun _:Fin 1=>sig) ⟨j.1,by omega⟩)=q3 Bc L:=by
          funext j;dsimp only [q1];rw [Zr j.isLt]
         have hs_eq:q1 (q3 Bc L) (fun _:Fin 1=>sig) ⟨Bc,by omega⟩=sig:=by
          dsimp only [q1];rw [Zb (by omega)]
         rw [hL_eq,hs_eq,q4 hL]
         have hget:(l++List.replicate (t+1) (L,sig))[i.1]'hi=(L,sig):=by
          simp only [hrep_snoc];rw [List.getElem_append_right (by omega)];simp [show i.1-(l++List.replicate t (L,sig)).length=0 by omega]
         rw [hget];exact ⟨rfl,rfl⟩
       . rw [if_neg (fun h=>hie h.2)]
         have hi_old:i.1< (l++List.replicate t (L,sig)).length:=by
          simp only [List.length_append,List.length_replicate] at hi hlen_old hie ⊢;omega
         have hget:(l++List.replicate (t+1) (L,sig))[i.1]'hi=(l++List.replicate t (L,sig))[i.1]'hi_old:=by
          simp only [hrep_snoc];rw [List.getElem_append_left hi_old]
         rw [hget];exact ih_el i hi_old
   . rw [decide_eq_false hlt']
     have hm1:min t (q2 Bc cnt)=q2 Bc cnt:=Nat.min_eq_right (by omega)
     have hm2:min (t+1) (q2 Bc cnt)=q2 Bc cnt:=Nat.min_eq_right (by omega)
     rw [hm1] at ih_len ih_el;rw [hm2]
     rcases hv_ext _ _ with ⟨e1,e2⟩
     refine ⟨?_,?_⟩
     . rw [e1,zn];exact ih_len
     . intro i hi;rw [e2,jx _ _ _ _ (by omega:n<=2^Bc) i];simp only [Ze,false_and,Zj];exact ih_el i hi
 have hfull:=hinv n le_rfl;rw [Zk (by simp),Nat.min_eq_right (by omega)] at hfull;exact hfull
def zu (n Bc:ℕ) (oddCounts:Fin (2*n*Bc)->Bool):Fin (Bc+n*(Bc+1))->Bool :=
 (List.finRange (2*n)).foldl (fun st idx =>
  xt n Bc (2*(idx.1/2)+1) (decide (idx.1 %2=1))
   (q5 (K:=2*n) (d:=Bc) oddCounts idx) st)
  (q1 (q3 Bc 0) (fun _:Fin (n*(Bc+1))=>false))
lemma vc (n Bc:ℕ) :
  q0 (zu n Bc) (2*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1)))):=by
 let S:=Bc+n*(Bc+1)
 have hf:=q0.l (m:=2*n*Bc) (s:=S) (T:=2*n) (B₀:=0)
  (Bs:=n*(37*Bc+n*(2*Bc+4*(Bc+1)+1)))
  (fun _=>q1 (q3 Bc 0) (fun _:Fin (n*(Bc+1))=>false))
  (fun idx u st=>xt n Bc (2*(idx.1/2)+1) (decide (idx.1 %2=1))
   (q5 (K:=2*n) (d:=Bc) u idx) st)
  (q0.k _)
  (fun idx =>
   let hcnt:q0 (fun q:Fin (2*n*Bc+S)->Bool=>q5 (K:=2*n) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) idx) 0 :=
    qa (q0.p _) idx
   let hst:q0 (fun q:Fin (2*n*Bc+S)->Bool=>fun a:Fin S=>q ⟨2*n*Bc+a.1,by omega⟩) 0 :=
    q0.p _
   (ka (2*(idx.1/2)+1) (decide (idx.1 %2=1)) hcnt hst).mono (by omega))
 exact hf.mono (by omega)
lemma j2 (n Bc:ℕ) (h4n:4*n< 2^Bc)
  (oddC:Fin n->Bool->Bool->ℕ) (c:Bool)
  (hlen:(z7 n oddC c).length<=n)
  (oddCounts:Fin (2*n*Bc)->Bool)
  (hcnts:∀ (j:Fin n) (sig:Bool),
   q2 Bc (q5 (K:=2*n) (d:=Bc) oddCounts ⟨2*j.1+sig.toNat,by cases sig <;> simp <;> omega⟩)=oddC j c sig) :
  vk n Bc (zu n Bc oddCounts) (z7 n oddC c):=by
 have hinv:∀ k ≤ n,
   vk n Bc (((List.finRange (2*n)).take (2*k)).foldl (fun st idx =>
    xt n Bc (2*(idx.1/2)+1) (decide (idx.1 %2=1))
     (q5 (K:=2*n) (d:=Bc) oddCounts idx) st)
    (q1 (q3 Bc 0) (fun _:Fin (n*(Bc+1))=>false)))
    (((List.finRange n).take k).flatMap fun j =>
     List.replicate (oddC j c false) (2*j.1+1,false) ++
     List.replicate (oddC j c true) (2*j.1+1,true)):=by
  intro k hk
  induction k with
  | zero =>
   simp only [Nat.mul_zero,Zn,Zi,List.flatMap_nil]
   refine ⟨?_,fun i hi=>by simp at hi⟩
   have h0:(fun j:Fin Bc=>q1 (q3 Bc 0) (fun _:Fin (n*(Bc+1))=>false) ⟨j.1,by omega⟩)=q3 Bc 0:=by
    funext j;dsimp only [q1];rw [Zr j.isLt]
   rw [h0,q4 (by omega:0< 2^Bc)];rfl
  | succ k ihk =>
   have ht1:(List.finRange (2*n)).take (2*(k+1)) =
     (List.finRange (2*n)).take (2*k)++[⟨2*k,by omega⟩,⟨2*k+1,by omega⟩]:=by
    rw [show 2*(k+1)=(2*k+1)+1 by omega,Zt (by simp;omega),
      Zt (by simp;omega)]
    simp [Zg,List.append_assoc]
   have ht2:(List.finRange n).take (k+1)=(List.finRange n).take k++[⟨k,by omega⟩]:=by
    rw [Zt (by simp;omega)];simp [Zg]
   rw [ht1,ht2,Zl,Zo,Zo,Zi,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,<-List.append_assoc]
   have hlen_prefix:(((List.finRange n).take (k+1)).flatMap fun j =>
     List.replicate (oddC j c false) (2*j.1+1,false) ++
     List.replicate (oddC j c true) (2*j.1+1,true)).length<=n:=by
    have hdrop:=congrArg List.length (congrArg (List.flatMap (fun j:Fin n =>
     List.replicate (oddC j c false) (2*j.1+1,false) ++
     List.replicate (oddC j c true) (2*j.1+1,true))) (List.take_append_drop (k+1) (List.finRange n)))
    rw [List.flatMap_append,List.length_append] at hdrop;unfold z7 at hlen;omega
   rw [ht2,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
     List.length_append,List.length_append,List.length_replicate,List.length_replicate] at hlen_prefix
   have ih:=ihk (by omega)
   have hcF:q2 Bc (q5 (K:=2*n) (d:=Bc) oddCounts ⟨2*k,by omega⟩)=oddC ⟨k,by omega⟩ c false:=by
    simpa using hcnts ⟨k,by omega⟩ false
   have hcT:q2 Bc (q5 (K:=2*n) (d:=Bc) oddCounts ⟨2*k+1,by omega⟩)=oddC ⟨k,by omega⟩ c true:=by
    simpa using hcnts ⟨k,by omega⟩ true
   have hstep1:=j1 n Bc (2*k+1) h4n (by omega) false
    (q5 (K:=2*n) (d:=Bc) oddCounts ⟨2*k,by omega⟩) _ _ ih (by rw [hcF];omega)
   rw [hcF] at hstep1
   have hfit2:((((List.finRange n).take k).flatMap fun j =>
     List.replicate (oddC j c false) (2*j.1+1,false) ++
     List.replicate (oddC j c true) (2*j.1+1,true)) ++
     List.replicate (oddC ⟨k,by omega⟩ c false) (2*k+1,false)).length +
     q2 Bc (q5 (K:=2*n) (d:=Bc) oddCounts ⟨2*k+1,by omega⟩)<=n:=by
    rw [List.length_append,List.length_replicate,hcT];omega
   have hstep2:=j1 n Bc (2*k+1) h4n (by omega) true
    (q5 (K:=2*n) (d:=Bc) oddCounts ⟨2*k+1,by omega⟩) _ _ hstep1 hfit2
   rw [hcT] at hstep2
   have hd0:(2*k)/2=k:=by omega
   have hm0:(2*k)%2=0:=by omega
   have hd1:(2*k+1)/2=k:=by omega
   have hm1:(2*k+1)%2=1:=by omega
   simpa only [hd0,hm0,hd1,hm1,show (0:ℕ)≠1 by omega,decide_false,decide_true] using hstep2
 have hfull:=hinv n le_rfl;rw [Zk (by simp),Zk (by simp)] at hfull;exact hfull
def w5 (n Bc:ℕ) (inp:Fin (6*n*Bc)->Bool):Fin (4*n)->Bool :=
 let stInit:Fin (Bc+1+2*n+2*n)->Bool :=
  q1 (q1 (q1 (q3 Bc 0) (fun _:Fin 1=>false)) (fun _:Fin (2*n)=>false)) (fun _:Fin (2*n)=>false)
 let stEv:=(List.finRange (2*n)).foldl (fun st idx =>
  let j:=idx.1/2
  let sig:=decide (idx.1 %2=1)
  let slot:Fin (6*n):=if idx.1 %2=0 then ⟨4*n+j,by omega⟩ else ⟨5*n+j,by omega⟩
  x9 n Bc (2*(j+1)) sig (q5 (K:=6*n) (d:=Bc) inp slot) st) stInit
 let odd0In:Fin (2*n*Bc)->Bool:=qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨i.1,by omega⟩)
 let odd1In:Fin (2*n*Bc)->Bool:=qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨2*n+i.1,by omega⟩)
 let o0:=zu n Bc odd0In
 let o1:=zu n Bc odd1In
 let len0:Fin Bc->Bool:=fun j=>o0 ⟨j.1,by omega⟩
 let arr0:Fin (n*(Bc+1))->Bool:=fun a=>o0 ⟨Bc+a.1,by omega⟩
 let arr1:Fin (n*(Bc+1))->Bool:=fun a=>o1 ⟨Bc+a.1,by omega⟩
 let stEnd:=(List.finRange n).foldl (fun st i =>
  let en:=wi (q3 Bc i.1) len0
  let e0:=q5 (K:=n) (d:=Bc+1) arr0 i
  let e1:=q5 (K:=n) (d:=Bc+1) arr1 i
  let st1:=qz n Bc st en (fun j:Fin Bc=>e0 ⟨j.1,by omega⟩) (e0 ⟨Bc,by omega⟩)
  qz n Bc st1 en (fun j:Fin Bc=>e1 ⟨j.1,by omega⟩) (e1 ⟨Bc,by omega⟩)) stEv
 fun k:Fin (4*n)=>stEnd ⟨Bc+1+k.1,by omega⟩
lemma jz (n Bc:ℕ) :
  q0 (w5 n Bc)
   (2*n*(n*(4*n*(4*Bc+7)+27*Bc+5)) +
    4*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))) +
    n*(2*(4*n*(4*Bc+7)+17*Bc+5)+20*Bc)):=by
 let S:=Bc+1+2*n+2*n
 let L:=Bc+n*(Bc+1)
 have hstEv:q0 (fun inp:Fin (6*n*Bc)->Bool =>
   (List.finRange (2*n)).foldl (fun st idx =>
     let j:=idx.1/2
     let sig:=decide (idx.1 %2=1)
     let slot:Fin (6*n):=if idx.1 %2=0 then ⟨4*n+j,by omega⟩ else ⟨5*n+j,by omega⟩
     x9 n Bc (2*(j+1)) sig (q5 (K:=6*n) (d:=Bc) inp slot) st)
     (q1 (q1 (q1 (q3 Bc 0) (fun _:Fin 1=>false)) (fun _:Fin (2*n)=>false)) (fun _:Fin (2*n)=>false)))
   (0+2*n*(n*(4*n*(4*Bc+7)+27*Bc+5))):=by
  refine q0.l (B₀:=0) (Bs:=n*(4*n*(4*Bc+7)+27*Bc+5)) _ _ (q0.k _) (fun idx=>?_)
  let slot:Fin (6*n):=if idx.1 %2=0 then ⟨4*n+idx.1/2,by omega⟩ else ⟨5*n+idx.1/2,by omega⟩
  have hcnt:q0 (fun q:Fin (6*n*Bc+S)->Bool=>q5 (K:=6*n) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) slot) 0 :=
   qa (q0.p _) slot
  have hst:q0 (fun q:Fin (6*n*Bc+S)->Bool=>fun a:Fin S=>q ⟨6*n*Bc+a.1,by omega⟩) 0 :=
   q0.p _
  exact (kd (2*(idx.1/2+1)) (decide (idx.1 %2=1)) hcnt hst).mono (by omega)
 have ho0:q0 (fun inp:Fin (6*n*Bc)->Bool =>
   zu n Bc (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨i.1,by omega⟩)))
   (2*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1)))):=by
  have hin:q0 (fun inp:Fin (6*n*Bc)->Bool =>
     qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨i.1,by omega⟩)) 0 :=
   (z4 (B:=0) _ (fun i=>qa (q0.id _) _)).mono (by simp)
  exact (q0.c hin (vc n Bc)).mono (by omega)
 have ho1:q0 (fun inp:Fin (6*n*Bc)->Bool =>
   zu n Bc (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨2*n+i.1,by omega⟩)))
   (2*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1)))):=by
  have hin:q0 (fun inp:Fin (6*n*Bc)->Bool =>
     qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨2*n+i.1,by omega⟩)) 0 :=
   (z4 (B:=0) _ (fun i=>qa (q0.id _) _)).mono (by simp)
  exact (q0.c hin (vc n Bc)).mono (by omega)
 have hpre:=q0.r (q0.r hstEv ho0) ho1
 have hinter:q0 (fun q:Fin (S+L+L)->Bool =>
   let stEv:Fin S->Bool:=fun a=>q ⟨a.1,by omega⟩
   let len0:Fin Bc->Bool:=fun j=>q ⟨S+j.1,by dsimp [L];omega⟩
   let arr0:Fin (n*(Bc+1))->Bool:=fun a=>q ⟨S+Bc+a.1,by dsimp [L];omega⟩
   let arr1:Fin (n*(Bc+1))->Bool:=fun a=>q ⟨S+L+Bc+a.1,by dsimp [L];omega⟩
   let stEnd:=(List.finRange n).foldl (fun st i =>
     let en:=wi (q3 Bc i.1) len0
     let e0:=q5 (K:=n) (d:=Bc+1) arr0 i
     let e1:=q5 (K:=n) (d:=Bc+1) arr1 i
     let st1:=qz n Bc st en (fun j:Fin Bc=>e0 ⟨j.1,by omega⟩) (e0 ⟨Bc,by omega⟩)
     qz n Bc st1 en (fun j:Fin Bc=>e1 ⟨j.1,by omega⟩) (e1 ⟨Bc,by omega⟩)) stEv
   fun k:Fin (4*n)=>stEnd ⟨Bc+1+k.1,by omega⟩)
   (n*(2*(4*n*(4*Bc+7)+17*Bc+5)+20*Bc)):=by
  have hfold:q0 (fun q:Fin (S+L+L)->Bool =>
     (List.finRange n).foldl (fun st i =>
      let en:=wi (q3 Bc i.1) (fun j:Fin Bc=>q ⟨S+j.1,by dsimp [L];omega⟩)
      let e0:=q5 (K:=n) (d:=Bc+1) (fun a=>q ⟨S+Bc+a.1,by dsimp [L];omega⟩) i
      let e1:=q5 (K:=n) (d:=Bc+1) (fun a=>q ⟨S+L+Bc+a.1,by dsimp [L];omega⟩) i
      let st1:=qz n Bc st en (fun j:Fin Bc=>e0 ⟨j.1,by omega⟩) (e0 ⟨Bc,by omega⟩)
      qz n Bc st1 en (fun j:Fin Bc=>e1 ⟨j.1,by omega⟩) (e1 ⟨Bc,by omega⟩))
      (fun a:Fin S=>q ⟨a.1,by omega⟩))
     (0+n*(2*(4*n*(4*Bc+7)+17*Bc+5)+20*Bc)):=by
   refine q0.l (B₀:=0) (Bs:=2*(4*n*(4*Bc+7)+17*Bc+5)+20*Bc) _ _ (q0.p _) (fun i=>?_)
   have hst:q0 (fun z:Fin ((S+L+L)+S)->Bool=>fun a:Fin S=>z ⟨S+L+L+a.1,by omega⟩) 0:=q0.p _;have hlen0:q0 (fun z:Fin ((S+L+L)+S)->Bool=>fun j:Fin Bc=>z ⟨S+j.1,by dsimp [L];omega⟩) 0:=q0.p _;have hen:=xo (q0.k (q3 Bc i.1)) hlen0
   have he0:q0 (fun z:Fin ((S+L+L)+S)->Bool=>q5 (K:=n) (d:=Bc+1) (fun a=>z ⟨S+Bc+a.1,by dsimp [L];omega⟩) i) 0 :=
     qa (q0.p _) i
   have he1:q0 (fun z:Fin ((S+L+L)+S)->Bool=>q5 (K:=n) (d:=Bc+1) (fun a=>z ⟨S+L+Bc+a.1,by dsimp [L];omega⟩) i) 0 :=
     qa (q0.p _) i
   have hst1:=yf hst hen
     (q0.c he0 (q0.p (fun j:Fin Bc=>(⟨j.1,by omega⟩:Fin (Bc+1)))))
     (q0.c he0 (q0.p (fun _:Fin 1=>(⟨Bc,by omega⟩:Fin (Bc+1)))))
   have hst2:=yf hst1 hen
     (q0.c he1 (q0.p (fun j:Fin Bc=>(⟨j.1,by omega⟩:Fin (Bc+1)))))
     (q0.c he1 (q0.p (fun _:Fin 1=>(⟨Bc,by omega⟩:Fin (Bc+1)))))
   exact hst2.mono (by omega)
  exact (q0.c hfold (q0.p (fun k:Fin (4*n)=>⟨Bc+1+k.1,by omega⟩))).mono (by omega)
 have hsumO:2*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))) +
   2*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))) =
   4*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))):=by ring
 refine ((q0.c hpre hinter).mono (by omega)).congr (fun inp=>?_)
 dsimp only [w5]
 set stEv:=(List.finRange (2*n)).foldl (fun st idx =>
  let j:=idx.1/2
  let sig:=decide (idx.1 %2=1)
  let slot:Fin (6*n):=if idx.1 %2=0 then ⟨4*n+j,by omega⟩ else ⟨5*n+j,by omega⟩
  x9 n Bc (2*(j+1)) sig (q5 (K:=6*n) (d:=Bc) inp slot) st)
  (q1 (q1 (q1 (q3 Bc 0) (fun _:Fin 1=>false)) (fun _:Fin (2*n)=>false)) (fun _:Fin (2*n)=>false))
 set o0:=zu n Bc (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨i.1,by omega⟩));set o1:=zu n Bc (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨2*n+i.1,by omega⟩))
 have e1:(fun a:Fin S=>q1 (q1 stEv o0) o1 ⟨a.1,by omega⟩)=stEv:=by
  funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;omega),Zr a.isLt]
 have e2:(fun j:Fin Bc=>q1 (q1 stEv o0) o1 ⟨S+j.1,by omega⟩)=fun j:Fin Bc=>o0 ⟨j.1,by omega⟩:=by
  funext j;dsimp only [q1];rw [Zr (by have:=j.isLt;omega),Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have e3:(fun a:Fin (n*(Bc+1))=>q1 (q1 stEv o0) o1 ⟨S+Bc+a.1,by omega⟩)=fun a=>o0 ⟨Bc+a.1,by omega⟩:=by
  funext a;dsimp only [q1];rw [Zr (by have:=a.isLt;omega),Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have e4:(fun a:Fin (n*(Bc+1))=>q1 (q1 stEv o0) o1 ⟨S+L+Bc+a.1,by omega⟩)=fun a=>o1 ⟨Bc+a.1,by omega⟩:=by
  funext a;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 rw [e1,e2,e3,e4]
lemma ke (n Bc:ℕ) (hn:0< n) (h4n:4*n< 2^Bc)
  (oddC:Fin n->Bool->Bool->ℕ) (ep'' em'':Fin n->ℕ)
  (hlen:yn n oddC+zj n ep'' em''=2*n)
  (hbal:jl n oddC=j7 n oddC)
  (inp:Fin (6*n*Bc)->Bool)
  (hodd:∀ o:Fin (4*n),q2 Bc (q5 (K:=6*n) (d:=Bc) inp ⟨o.1,by omega⟩) =
   oddC ⟨zf n o.1,(qp n o.1 o.isLt).1⟩ (qh n o.1) (qf o.1))
  (hep:∀ j:Fin n,q2 Bc (q5 (K:=6*n) (d:=Bc) inp ⟨4*n+j.1,by omega⟩)=ep'' j)
  (hem:∀ j:Fin n,q2 Bc (q5 (K:=6*n) (d:=Bc) inp ⟨5*n+j.1,by omega⟩)=em'' j) :
  let out:=w5 n Bc inp
  let p:=qg n hn (vj n oddC ep'' em'') 0 false (fun _=>none)
  ∀ k:Fin (2*n),
   out ⟨k.1,by omega⟩=(p k).isSome /\
   (out ⟨k.1,by omega⟩=true->p k=some (out ⟨2*n+k.1,by omega⟩)):=by
 intro out p
 have hfin_flatMap_sum (f:Fin n->List (ℕ × Bool)) (g:ℕ × Bool->ℕ) :
   (((List.finRange n).flatMap f).map g).sum=∑ j:Fin n,((f j).map g).sum:=by
  have hlist:∀ l:List (Fin n),((l.flatMap f).map g).sum=(l.map fun j=>((f j).map g).sum).sum:=by
   intro l;induction l with | nil=>simp | cons x xs ih=>simp [List.flatMap_cons,Za,Zs,ih]
  rw [hlist,<-Fin.sum_univ_def]
 have hev_sum:((y4 n ep'' em'').map Prod.fst).sum=zj n ep'' em'':=by
  unfold y4 zj;rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz];ring
 have ho_len (c:Bool):((z7 n oddC c).map Prod.fst).sum =
   ∑ j:Fin n,(2*j.1+1)*(oddC j c false+oddC j c true):=by
  unfold z7;rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz];ring
 have ho_cnt (c:Bool):(z7 n oddC c).length=∑ j:Fin n,(oddC j c false+oddC j c true):=by
  have hlen_eq:∀ l:List (ℕ × Bool),(l.map (fun _=>1)).sum=l.length:=by
   intro l;induction l with | nil=>simp | cons _ _ ih=>simp [ih];omega
  rw [<- hlen_eq];unfold z7;rw [hfin_flatMap_sum];apply Zc rfl;intro j _;simp [Za,Zy,Zz]
 have ho0_eq_o1:(z7 n oddC false).length=(z7 n oddC true).length:=by
  rw [ho_cnt false,ho_cnt true];exact hbal
 have ho_le_n:(z7 n oddC false).length<=n:=by
  have h1:jl n oddC+j7 n oddC<=yn n oddC:=by
   unfold jl j7 yn;rw [<- Finset.sum_add_distrib];apply Finset.sum_le_sum;intro j _;nlinarith
  rw [ho_cnt false];unfold jl at h1 hbal;omega
 have hev_inv:∀ k ≤ n,
   let st:=((List.finRange (2*n)).take (2*k)).foldl (fun st idx =>
     let j:=idx.1/2
     let sig:=decide (idx.1 %2=1)
     let slot:Fin (6*n):=if idx.1 %2=0 then ⟨4*n+j,by omega⟩ else ⟨5*n+j,by omega⟩
     x9 n Bc (2*(j+1)) sig (q5 (K:=6*n) (d:=Bc) inp slot) st)
     (q1 (q1 (q1 (q3 Bc 0) (fun _:Fin 1=>false)) (fun _:Fin (2*n)=>false)) (fun _:Fin (2*n)=>false))
   let l:=((List.finRange n).take k).flatMap fun j =>
     List.replicate (ep'' j) (2*(j.1+1),false)++List.replicate (em'' j) (2*(j.1+1),true)
   y5 n Bc st (l.map Prod.fst).sum (l.foldl (fun b a=>xor b a.2) false) (qg n hn l 0 false (fun _=>none)):=by
  intro k hk
  induction k with
  | zero =>
   simp only [Nat.mul_zero,Zn,Zi,List.flatMap_nil,List.map_nil,List.sum_nil,qg]
   rcases v7 (q3 Bc 0) false (fun _:Fin (2*n)=>false) (fun _:Fin (2*n)=>false) with ⟨e1,e2,e3,e4⟩
   exact ⟨by rw [e1,q4 (by omega:0< 2^Bc)],e2,fun k=>⟨by rw [e3 k];rfl,fun h=>by rw [e3 k] at h;cases h⟩⟩
  | succ k ihk =>
   have ht1:(List.finRange (2*n)).take (2*(k+1)) =
      (List.finRange (2*n)).take (2*k)++[⟨2*k,by omega⟩,⟨2*k+1,by omega⟩]:=by
     rw [show 2*(k+1)=(2*k+1)+1 by omega,Zt (by simp;omega),
       Zt (by simp;omega)]
     simp [Zg,List.append_assoc]
   have ht2:(List.finRange n).take (k+1)=(List.finRange n).take k++[⟨k,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [ht1,ht2,Zl,Zo,Zo,Zi,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   have ih:=ihk (by omega)
   have hsum_le:(((((List.finRange n).take (k+1)).flatMap fun j =>
      List.replicate (ep'' j) (2*(j.1+1),false)++List.replicate (em'' j) (2*(j.1+1),true)).map Prod.fst).sum)<=2*n:=by
     have hdrop:=congrArg (fun l=>(l.map Prod.fst).sum) (congrArg (List.flatMap (fun j:Fin n =>
      List.replicate (ep'' j) (2*(j.1+1),false)++List.replicate (em'' j) (2*(j.1+1),true)))
      (List.take_append_drop (k+1) (List.finRange n)))
     rw [List.flatMap_append,Za,Zs] at hdrop
     have:(((List.finRange n).flatMap fun j =>
       List.replicate (ep'' j) (2*(j.1+1),false)++List.replicate (em'' j) (2*(j.1+1),true)).map Prod.fst).sum =
       zj n ep'' em'':=hev_sum
     omega
   rw [ht2,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      Za,Zs,Za,Zs,
      Zy,Zy,Zz,Zz,smul_eq_mul,smul_eq_mul] at hsum_le
   dsimp only at hsum_le;have hep_k:q2 Bc (q5 (K:=6*n) (d:=Bc) inp ⟨4*n+k,by omega⟩)=ep'' ⟨k,by omega⟩:=hep ⟨k,by omega⟩;have hem_k:q2 Bc (q5 (K:=6*n) (d:=Bc) inp ⟨5*n+k,by omega⟩)=em'' ⟨k,by omega⟩:=hem ⟨k,by omega⟩
   have hep_mul:ep'' ⟨k,by omega⟩*(2*(k+1))<=2*n:=by omega
   have hem_mul:em'' ⟨k,by omega⟩*(2*(k+1))<=2*n:=by omega
   have hep_le:ep'' ⟨k,by omega⟩<=n:=by nlinarith
   have hem_le:em'' ⟨k,by omega⟩<=n:=by nlinarith
   have hstep1:=jc n Bc (2*(k+1)) hn h4n (by omega) false
     (q5 (K:=6*n) (d:=Bc) inp ⟨4*n+k,by omega⟩) _ _ _ _ ih (by rw [hep_k];exact hep_le) (by rw [hep_k];omega)
   rw [hep_k] at hstep1
   have hfit2:(((((List.finRange n).take k).flatMap fun j =>
      List.replicate (ep'' j) (2*(j.1+1),false)++List.replicate (em'' j) (2*(j.1+1),true)).map Prod.fst).sum +
      ((List.replicate (ep'' ⟨k,by omega⟩) (2*(k+1),false)).map Prod.fst).sum) +
      q2 Bc (q5 (K:=6*n) (d:=Bc) inp ⟨5*n+k,by omega⟩)*(2*(k+1))< 2^Bc:=by
     rw [hem_k,Zy,Zz,smul_eq_mul];dsimp only;omega
   have hstep2:=jc n Bc (2*(k+1)) hn h4n (by omega) true
     (q5 (K:=6*n) (d:=Bc) inp ⟨5*n+k,by omega⟩) _ _ _ _ hstep1 (by rw [hem_k];exact hem_le) hfit2
   rw [hem_k] at hstep2
   have hdiv0:(2*k)/2=k:=by omega
   have hmod0:(2*k)%2=0:=by omega
   have hdiv1:(2*k+1)/2=k:=by omega
   have hmod1:(2*k+1)%2=1:=by omega
   dsimp only;simp only [hdiv0,hmod0,hdiv1,hmod1,Zh,show (1:ℕ)≠0 by omega,show (0:ℕ)≠1 by omega,Zj,decide_false,decide_true]
   rw [<- List.append_assoc,ya,ya,Za,Zs,
      Za,Zs,Zl,Zl]
   simpa only [Nat.zero_add,Nat.add_assoc] using hstep2
 have hev_full:=hev_inv n le_rfl;rw [Zk (by simp),Zk (by simp)] at hev_full
 have ho0_rep:vk n Bc (zu n Bc
   (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨i.1,by omega⟩)))
   (z7 n oddC false):=by
  apply j2 n Bc h4n oddC false ho_le_n;intro j sig;rw [qb]
  have hidx:(2*j.1+sig.toNat)< 4*n:=by cases sig <;> simp <;> omega
  have h:=hodd ⟨2*j.1+sig.toNat,hidx⟩
  have hj_eq:(⟨zf n (2*j.1+sig.toNat),(qp n _ hidx).1⟩:Fin n)=j:=by
   apply Zx;unfold zf;cases sig <;> simp [show 2*j.1< 2*n by omega,show 2*j.1+1< 2*n by omega] <;> omega
  have hc_eq:qh n (2*j.1+sig.toNat)=false:=by
   unfold qh;cases sig <;> simp [show ¬ (2*n<=2*j.1) by omega,show ¬ (2*n<=2*j.1+1) by omega]
  have hs_eq:qf (2*j.1+sig.toNat)=sig:=by
   unfold qf;cases sig <;> simp [show (2*j.1)%2=0 by omega,show (2*j.1+1)%2=1 by omega]
  rw [hj_eq,hc_eq,hs_eq] at h;exact h
 have ho1_rep:vk n Bc (zu n Bc
   (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨2*n+i.1,by omega⟩)))
   (z7 n oddC true):=by
  apply j2 n Bc h4n oddC true (by omega);intro j sig;rw [qb]
  have hidx:2*n+(2*j.1+sig.toNat)< 4*n:=by cases sig <;> simp <;> omega
  have h:=hodd ⟨2*n+(2*j.1+sig.toNat),hidx⟩
  have hj_eq:(⟨zf n (2*n+(2*j.1+sig.toNat)),(qp n _ hidx).1⟩:Fin n)=j:=by
   apply Zx;unfold zf;cases sig <;> simp [show ¬ (2*n+2*j.1< 2*n) by omega,show ¬ (2*n+(2*j.1+1)< 2*n) by omega] <;> omega
  have hc_eq:qh n (2*n+(2*j.1+sig.toNat))=true:=by
   unfold qh;cases sig <;> simp [show 2*n<=2*n+2*j.1 by omega,show 2*n<=2*n+(2*j.1+1) by omega]
  have hs_eq:qf (2*n+(2*j.1+sig.toNat))=sig:=by
   unfold qf;cases sig <;> simp [show (2*n+2*j.1)%2=0 by omega,show (2*n+(2*j.1+1))%2=1 by omega]
  rw [hj_eq,hc_eq,hs_eq] at h;exact h
 set evL:=y4 n ep'' em'';set o0L:=z7 n oddC false;set o1L:=z7 n oddC true
 have hzip_take:∀ (l₀ l₁:List (ℕ × Bool)) (t:ℕ) (ht:t< l₀.length) (h1:t< l₁.length),
   zl (l₀.take (t+1)) (l₁.take (t+1)) =
   zl (l₀.take t) (l₁.take t)++[l₀[t]'ht,l₁[t]'h1]:=by
  intro l₀;induction l₀ with
  | nil=>intro _ _ ht;simp at ht
  | cons a as ih =>
   intro l₁ t ht h1;cases l₁ with
   | nil=>simp at h1
   | cons b bs =>
     cases t with
     | zero=>simp [zl]
     | succ t =>
      simp only [List.take_succ_cons,zl,List.cons_append,List.getElem_cons_succ];rw [ih bs t (by simpa using ht) (by simpa using h1)]
 have hzip_sum:∀ (l₀ l₁:List (ℕ × Bool)),l₀.length=l₁.length ->
   ((zl l₀ l₁).map Prod.fst).sum=(l₀.map Prod.fst).sum+(l₁.map Prod.fst).sum:=by
  intro l₀;induction l₀ with
  | nil=>intro l₁ h;cases l₁ with | nil=>simp [zl] | cons _ _=>simp at h
  | cons a as ih =>
   intro l₁ h;cases l₁ with
   | nil=>simp at h
   | cons b bs =>
     simp only [zl,List.map_cons,List.sum_cons,ih bs (by simpa using h)];omega
 have hall_sum_le:(evL.map Prod.fst).sum+(o0L.map Prod.fst).sum+(o1L.map Prod.fst).sum=2*n:=by
  rw [hev_sum,ho_len false,ho_len true]
  have:yn n oddC=(∑ j:Fin n,(2*j.1+1)*(oddC j false false+oddC j false true)) +
     (∑ j:Fin n,(2*j.1+1)*(oddC j true false+oddC j true true)):=by
   unfold yn;rw [<- Finset.sum_add_distrib];apply Zc rfl;intro j _;ring
  omega
 set stEv:=(List.finRange (2*n)).foldl (fun st idx =>
  let j:=idx.1/2
  let sig:=decide (idx.1 %2=1)
  let slot:Fin (6*n):=if idx.1 %2=0 then ⟨4*n+j,by omega⟩ else ⟨5*n+j,by omega⟩
  x9 n Bc (2*(j+1)) sig (q5 (K:=6*n) (d:=Bc) inp slot) st)
  (q1 (q1 (q1 (q3 Bc 0) (fun _:Fin 1=>false)) (fun _:Fin (2*n)=>false)) (fun _:Fin (2*n)=>false))
 set o0:=zu n Bc (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨i.1,by omega⟩));set o1:=zu n Bc (qn (K:=2*n) (d:=Bc) (fun i=>q5 (K:=6*n) (d:=Bc) inp ⟨2*n+i.1,by omega⟩))
 have hinter_inv:∀ t ≤ n,
   let st:=((List.finRange n).take t).foldl (fun st i =>
     let en:=wi (q3 Bc i.1) (fun j:Fin Bc=>o0 ⟨j.1,by omega⟩)
     let e0:=q5 (K:=n) (d:=Bc+1) (fun a=>o0 ⟨Bc+a.1,by omega⟩) i
     let e1:=q5 (K:=n) (d:=Bc+1) (fun a=>o1 ⟨Bc+a.1,by omega⟩) i
     let st1:=qz n Bc st en (fun j:Fin Bc=>e0 ⟨j.1,by omega⟩) (e0 ⟨Bc,by omega⟩)
     qz n Bc st1 en (fun j:Fin Bc=>e1 ⟨j.1,by omega⟩) (e1 ⟨Bc,by omega⟩)) stEv
   let l:=evL++zl (o0L.take t) (o1L.take t)
   y5 n Bc st (l.map Prod.fst).sum (l.foldl (fun b a=>xor b a.2) false) (qg n hn l 0 false (fun _=>none)):=by
  intro t ht
  induction t with
  | zero =>
   simp only [Zn,Zi,zl,List.append_nil];exact hev_full
  | succ t iht =>
   have htake:(List.finRange n).take (t+1)=(List.finRange n).take t++[⟨t,by omega⟩]:=by
     rw [Zt (by simp;omega)];simp [Zg]
   rw [htake,Zl,Zo,Zi];have ih:=iht (by omega);rw [x8,q4 (by omega:t< 2^Bc),ho0_rep.1]
   by_cases hlt':t< o0L.length
   . rw [decide_eq_true hlt']
     have hlt1:t< o1L.length:=by omega
     rcases ho0_rep.2 ⟨t,by omega⟩ hlt' with ⟨hL0,hs0⟩
     rcases ho1_rep.2 ⟨t,by omega⟩ hlt1 with ⟨hL1,hs1⟩
     dsimp only at hL0 hL1 hs0 hs1
     have hsum_take:(((evL++zl (o0L.take (t+1)) (o1L.take (t+1))).map Prod.fst).sum)<=2*n:=by
      rw [Za,Zs,hzip_sum _ _ (by simp;omega)]
      have h0:((o0L.take (t+1)).map Prod.fst).sum<=(o0L.map Prod.fst).sum:=by
       have:=congrArg (fun l=>(l.map Prod.fst).sum) (List.take_append_drop (t+1) o0L);rw [Za,Zs] at this;omega
      have h1:((o1L.take (t+1)).map Prod.fst).sum<=(o1L.map Prod.fst).sum:=by
       have:=congrArg (fun l=>(l.map Prod.fst).sum) (List.take_append_drop (t+1) o1L);rw [Za,Zs] at this;omega
      omega
     rw [hzip_take o0L o1L t hlt' hlt1] at hsum_take ⊢;rw [<- List.append_assoc,Za,Zs] at hsum_take;simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Zq] at hsum_take;set e0:=q5 (K:=n) (d:=Bc+1) (fun a=>o0 ⟨Bc+a.1,by omega⟩) ⟨t,by omega⟩;set e1:=q5 (K:=n) (d:=Bc+1) (fun a=>o1 ⟨Bc+a.1,by omega⟩) ⟨t,by omega⟩;have h1:=yy n Bc (by omega) _ (fun j:Fin Bc=>e0 ⟨j.1,by omega⟩) (e0 ⟨Bc,by omega⟩) _ _ _ ih (by rw [hL0];omega);rw [hL0,hs0] at h1;have h2:=yy n Bc (by omega) _ (fun j:Fin Bc=>e1 ⟨j.1,by omega⟩) (e1 ⟨Bc,by omega⟩) _ _ _ h1 (by rw [hL1];omega);rw [hL1,hs1] at h2;dsimp only;rw [hs0,hs1,<-List.append_assoc,ya,Za,Zs,Zl]
     simpa only [qg,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Zo,Zi,
      Nat.zero_add,Zq,Nat.add_assoc] using h2
   . rw [decide_eq_false hlt']
     have h0:o0L.take (t+1)=o0L.take t:=by
      rw [Zk (by omega),Zk (by omega)]
     have h1:o1L.take (t+1)=o1L.take t:=by
      rw [Zk (by omega),Zk (by omega)]
     rw [h0,h1];exact yp n Bc (by omega) _ _ _ _ _ _ (yp n Bc (by omega) _ _ _ _ _ _ ih)
 have hfull:=hinter_inv n le_rfl;rw [Zk (by simp),Zk ho_le_n,Zk (by omega)] at hfull;intro k;have hk:=hfull.2.2 k;dsimp only [out,w5,p,vj]
 refine ⟨hk.1,fun h=>?_⟩
 set stEnd:=(List.finRange n).foldl (fun st i =>
  let en:=wi (q3 Bc i.1) (fun j:Fin Bc=>o0 ⟨j.1,by omega⟩)
  let e0:=q5 (K:=n) (d:=Bc+1) (fun a=>o0 ⟨Bc+a.1,by omega⟩) i
  let e1:=q5 (K:=n) (d:=Bc+1) (fun a=>o1 ⟨Bc+a.1,by omega⟩) i
  let st1:=qz n Bc st en (fun j:Fin Bc=>e0 ⟨j.1,by omega⟩) (e0 ⟨Bc,by omega⟩)
  qz n Bc st1 en (fun j:Fin Bc=>e1 ⟨j.1,by omega⟩) (e1 ⟨Bc,by omega⟩)) stEv
 have hbit_eq:stEnd ⟨Bc+1+(2*n+k.1),by omega⟩=stEnd ⟨Bc+1+2*n+k.1,by omega⟩ :=
  congrArg stEnd (Zx (by dsimp;omega))
 rw [hbit_eq];exact hk.2 h
def vo (n:ℕ) (u:Fin (4*n)->Bool) (k:Fin (2*n)) (b:Bool):Bool :=
 !(u ⟨k.1,by omega⟩)||!(xor (u ⟨2*n+k.1,by omega⟩) b)
lemma p6 (n:ℕ) (p:Fin (2*n)->Option Bool) (junk:Fin (2*n)->Bool)
  (k:Fin (2*n)) (b:Bool) :
  vo n (fun j=>if h:j.1< 2*n then (p ⟨j.1,h⟩).isSome
   else (p ⟨j.1-2*n,by omega⟩).getD (junk ⟨j.1-2*n,by omega⟩)) k b=xr p k b:=by
 unfold vo xr;simp only [k.isLt,Zd,show ¬ (2*n+k.1< 2*n) by omega,Zf,Nat.add_sub_cancel_left]
 cases p k with
 | none=>simp
 | some v=>simp only [Option.isSome_some,Option.getD_some];cases v <;> cases b <;> decide
lemma jj (n:ℕ) (k:Fin (2*n)) (b:Bool) :
  q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>vo n u k b) 7:=by
 unfold vo;have h1:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨k.1,by omega⟩) 0:=q0.p _;have h2:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>u ⟨2*n+k.1,by omega⟩) 0:=q0.p _;exact (q0.boolOr (q0.boolNot h1) (q0.boolNot (q0.x h2 (q0.k _)))).mono (by omega)
def zd (n:ℕ) (b:Bool) (c0 c1:ℕ):ℕ :=
 (b.toNat*(n+1)+c0)*(n+1)+c1
lemma zq (n:ℕ) (b:Bool) {c0 c1:ℕ} (h0:c0< n+1) (h1:c1< n+1) :
  zd n b c0 c1< 2*(n+1)*(n+1):=by
 unfold zd;cases b <;> simp <;> nlinarith
def xw (n:ℕ) (hn:0< n) (b₀:Bool) (u:Fin (4*n)->Bool) :
  Fin ((2*(n+1)*(n+1))*(2*n+1))->Bool :=
 qn (K:=2*(n+1)*(n+1)) (d:=2*n+1) (fun idx =>
  if idx.1=zd n b₀ 0 0 then
   zb (vo n u ⟨0,by omega⟩ b₀) (q3 (2*n+1) 0) (q3 (2*n+1) 1)
  else q3 (2*n+1) 0)
def xx (n:ℕ) (hn:0< n) (s:Fin (2*n-1)) (u:Fin (4*n)->Bool)
  (prev:Fin ((2*(n+1)*(n+1))*(2*n+1))->Bool) :
  Fin ((2*(n+1)*(n+1))*(2*n+1))->Bool :=
 let M:=n+1
 qn (K:=2*M*M) (d:=2*n+1) (fun idx =>
  let b:Bool:=decide (M*M<=idx.1)
  let rem:=idx.1 %(M*M)
  let c0:=rem/M
  let c1:=rem %M
  let term (bPrev:Bool):Fin (2*n+1)->Bool :=
   if bPrev≠b then
    if s.1 %2=0 then
     if 0< c0 then q5 (K:=2*M*M) (d:=2*n+1) prev ⟨zd n bPrev (c0-1) c1,
      zq n bPrev (by have:rem< M*M:=Nat.mod_lt _ (by positivity);have:c0< M:=Nat.div_lt_of_lt_mul this;omega)
       (Nat.mod_lt _ (by omega))⟩
     else q3 (2*n+1) 0
    else
     if 0< c1 then q5 (K:=2*M*M) (d:=2*n+1) prev ⟨zd n bPrev c0 (c1-1),
      zq n bPrev (Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by positivity))) (by have:=Nat.mod_lt rem (show 0< M by omega);omega)⟩
     else q3 (2*n+1) 0
   else q5 (K:=2*M*M) (d:=2*n+1) prev ⟨zd n bPrev c0 c1,
    zq n bPrev (Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by positivity))) (Nat.mod_lt _ (by omega))⟩
  zb (vo n u ⟨s.1+1,by omega⟩ b) (q3 (2*n+1) 0) (qr (term false) (term true)))
def wn (n:ℕ) (hn:0< n) (b₀:Bool) (u:Fin (4*n)->Bool) :
  Fin (((n+1)*(n+1))*(2*n+1))->Bool :=
 let tab:=(List.finRange (2*n-1)).foldl (fun prev s=>xx n hn s u prev) (xw n hn b₀ u)
 let M:=n+1
 qn (K:=M*M) (d:=2*n+1) (fun idx =>
  let d1:=idx.1/M
  let d2:=idx.1 %M
  let term (bLast:Bool):Fin (2*n+1)->Bool :=
   if bLast≠b₀ then
    if 0< d2 then q5 (K:=2*M*M) (d:=2*n+1) tab ⟨zd n bLast d1 (d2-1),
     zq n bLast (Nat.div_lt_of_lt_mul idx.isLt) (by have:=Nat.mod_lt idx.1 (show 0< M by omega);omega)⟩
    else q3 (2*n+1) 0
   else q5 (K:=2*M*M) (d:=2*n+1) tab ⟨zd n bLast d1 d2,
    zq n bLast (Nat.div_lt_of_lt_mul idx.isLt) (Nat.mod_lt _ (by omega))⟩
  qr (term false) (term true))
def ys (n:ℕ) (hn:0< n) (b:ℕ) (inp:Fin (4*n+2*b)->Bool):Fin (2*n+1)->Bool :=
 let u:Fin (4*n)->Bool:=fun k=>inp ⟨k.1,by omega⟩
 let d1:Fin b->Bool:=fun j=>inp ⟨4*n+j.1,by omega⟩
 let d2:Fin b->Bool:=fun j=>inp ⟨4*n+b+j.1,by omega⟩
 let t0:=wn n hn false u
 let t1:=wn n hn true u
 let tot:=qn (K:=(n+1)*(n+1)) (d:=2*n+1) (fun idx =>
  qr (q5 (K:=(n+1)*(n+1)) (d:=2*n+1) t0 idx)
   (q5 (K:=(n+1)*(n+1)) (d:=2*n+1) t1 idx))
 jb (K₁:=n+1) (K₂:=n+1) (d:=2*n+1) tot d1 d2
lemma jd (n:ℕ) (hn:0< n) (b₀:Bool) :
  q0 (wn n hn b₀)
    (2*(n+1)*(n+1)*(4*(2*n+1)+7) +
     (2*n-1)*(2*(n+1)*(n+1)*(17*(2*n+1)+7)) +
     (n+1)*(n+1)*(13*(2*n+1))):=by
 let M:=n+1
 let K:=2*M*M
 let W:=2*n+1
 have hinit:q0 (xw n hn b₀) (K*(4*W+7)):=by
  apply z4;intro idx
  split_ifs
  . exact (zg (jj n ⟨0,by omega⟩ b₀) (q0.k _) (q0.k _)).mono (by omega)
  . exact (q0.k _).mono (by omega)
 have htab:q0 (fun u:Fin (4*n)->Bool =>
    (List.finRange (2*n-1)).foldl (fun prev s=>xx n hn s u prev) (xw n hn b₀ u))
    (K*(4*W+7)+(2*n-1)*(K*(17*W+7))):=by
  refine q0.l (B₀:=K*(4*W+7)) (Bs:=K*(17*W+7)) _ _ hinit (fun s=>?_)
  dsimp only [xx];apply z4;intro idx;have hu:q0 (fun q:Fin (4*n+K*W)->Bool=>fun a:Fin (4*n)=>q ⟨a.1,by omega⟩) 0:=q0.p _;have hprev:q0 (fun q:Fin (4*n+K*W)->Bool=>fun a:Fin (K*W)=>q ⟨4*n+a.1,by omega⟩) 0:=q0.p _;have hal:=q0.c hu (jj n ⟨s.1+1,by omega⟩ (decide (M*M<=idx.1)))
  have hterm (bPrev:Bool):q0 (fun q:Fin (4*n+K*W)->Bool =>
      if bPrev≠decide (M*M<=idx.1) then
       if s.1 %2=0 then
        if 0< idx.1 %(M*M)/M then
         q5 (K:=K) (d:=W) (fun a=>q ⟨4*n+a.1,by omega⟩) ⟨zd n bPrev (idx.1 %(M*M)/M-1) (idx.1 %(M*M)%M),
          zq n bPrev (by have:=Nat.div_lt_of_lt_mul (Nat.mod_lt idx.1 (show 0< M*M by positivity));omega) (Nat.mod_lt _ (by omega))⟩
        else q3 W 0
       else
        if 0< idx.1 %(M*M)%M then
         q5 (K:=K) (d:=W) (fun a=>q ⟨4*n+a.1,by omega⟩) ⟨zd n bPrev (idx.1 %(M*M)/M) (idx.1 %(M*M)%M-1),
          zq n bPrev (Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by positivity))) (by have:=Nat.mod_lt (idx.1 %(M*M)) (show 0< M by omega);omega)⟩
        else q3 W 0
      else q5 (K:=K) (d:=W) (fun a=>q ⟨4*n+a.1,by omega⟩) ⟨zd n bPrev (idx.1 %(M*M)/M) (idx.1 %(M*M)%M),
       zq n bPrev (Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by positivity))) (Nat.mod_lt _ (by omega))⟩) 0:=by
    split_ifs
    . exact qa hprev _
    . exact q0.k _
    . exact qa hprev _
    . exact q0.k _
    . exact qa hprev _
  exact (zg hal (q0.k _) (z8 (hterm false) (hterm true))).mono (by omega)
 have hfin:q0 (fun tab:Fin (K*W)->Bool =>
    qn (K:=M*M) (d:=W) (fun idx =>
      let d1:=idx.1/M
      let d2:=idx.1 %M
      let term (bLast:Bool):Fin W->Bool :=
       if bLast≠b₀ then
        if 0< d2 then q5 (K:=K) (d:=W) tab ⟨zd n bLast d1 (d2-1),
         zq n bLast (Nat.div_lt_of_lt_mul idx.isLt) (by have:=Nat.mod_lt idx.1 (show 0< M by omega);omega)⟩
        else q3 W 0
       else q5 (K:=K) (d:=W) tab ⟨zd n bLast d1 d2,
        zq n bLast (Nat.div_lt_of_lt_mul idx.isLt) (Nat.mod_lt _ (by omega))⟩
      qr (term false) (term true))) (M*M*(13*W)):=by
  apply z4;intro idx;dsimp only
  have hterm (bLast:Bool):q0 (fun tab:Fin (K*W)->Bool =>
      if bLast≠b₀ then
       if 0< idx.1 %M then q5 (K:=K) (d:=W) tab ⟨zd n bLast (idx.1/M) (idx.1 %M-1),
        zq n bLast (Nat.div_lt_of_lt_mul idx.isLt) (by have:=Nat.mod_lt idx.1 (show 0< M by omega);omega)⟩
       else q3 W 0
      else q5 (K:=K) (d:=W) tab ⟨zd n bLast (idx.1/M) (idx.1 %M),
       zq n bLast (Nat.div_lt_of_lt_mul idx.isLt) (Nat.mod_lt _ (by omega))⟩) 0:=by
    split_ifs
    . exact qa (q0.id _) _
    . exact q0.k _
    . exact qa (q0.id _) _
  exact (z8 (hterm false) (hterm true)).mono (by omega)
 exact (q0.c htab hfin).mono (by dsimp [K,M,W];omega)
lemma k1 (n:ℕ) (hn:0< n) (b:ℕ) (hb:n+1<=2^b) :
  q0 (ys n hn b)
   (2*(2*(n+1)*(n+1)*(4*(2*n+1)+7) +
      (2*n-1)*(2*(n+1)*(n+1)*(17*(2*n+1)+7)) +
      (n+1)*(n+1)*(13*(2*n+1))) +
    (n+1)*(n+1)*(13*(2*n+1)) +
    (n+1)*(n+1)*(4*b+4*(2*n+1)+1)):=by
 let M:=n+1
 let W:=2*n+1
 have hu:q0 (fun inp:Fin (4*n+2*b)->Bool=>fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩) 0:=q0.p _;have hd1:q0 (fun inp:Fin (4*n+2*b)->Bool=>fun j:Fin b=>inp ⟨4*n+j.1,by omega⟩) 0:=q0.p _;have hd2:q0 (fun inp:Fin (4*n+2*b)->Bool=>fun j:Fin b=>inp ⟨4*n+b+j.1,by omega⟩) 0:=q0.p _;have ht0:=q0.c hu (jd n hn false);have ht1:=q0.c hu (jd n hn true);have hpair:=q0.r ht0 ht1
 have hadd:q0 (fun q:Fin ((M*M*W)+(M*M*W))->Bool =>
   qn (K:=M*M) (d:=W) (fun idx =>
     qr (q5 (K:=M*M) (d:=W) (fun a=>q ⟨a.1,by omega⟩) idx)
       (q5 (K:=M*M) (d:=W) (fun a=>q ⟨M*M*W+a.1,by omega⟩) idx))) (M*M*(13*W)):=by
  apply z4;intro idx;exact (z8 (qa (q0.p _) idx) (qa (q0.p _) idx)).mono (by omega)
 have htot:q0 (fun inp:Fin (4*n+2*b)->Bool =>
   qn (K:=M*M) (d:=W) (fun idx =>
     qr (q5 (K:=M*M) (d:=W) (wn n hn false (fun k=>inp ⟨k.1,by omega⟩)) idx)
       (q5 (K:=M*M) (d:=W) (wn n hn true (fun k=>inp ⟨k.1,by omega⟩)) idx)))
   (2*(2*M*M*(4*W+7)+(2*n-1)*(2*M*M*(17*W+7))+M*M*(13*W))+M*M*(13*W)):=by
  refine ((q0.c hpair hadd).mono (by dsimp [M,W];omega)).congr (fun inp=>?_)
  congr 1;funext idx
  have e1:(fun a:Fin (M*M*W)=>q1 (wn n hn false (fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩))
     (wn n hn true (fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩)) ⟨a.1,by dsimp [M,W];omega⟩) =
     wn n hn false (fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩):=by
   funext a;dsimp only [q1];rw [Zr a.isLt]
  have e2:(fun a:Fin (M*M*W)=>q1 (wn n hn false (fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩))
     (wn n hn true (fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩)) ⟨M*M*W+a.1,by dsimp [M,W];omega⟩) =
     wn n hn true (fun k:Fin (4*n)=>inp ⟨k.1,by omega⟩):=by
   funext a;dsimp only [q1];rw [Zb (by dsimp [M,W];omega)];congr 1;exact Zx (by dsimp [M,W];omega)
  rw [e1,e2]
 exact (pg (K₁:=M) (K₂:=M) (d:=W) hb hb htot hd1 hd2).mono (by
  dsimp [M,W];have h4:2*b+2*b+4*(2*n+1)+1=4*b+4*(2*n+1)+1:=by omega
  rw [h4])
lemma c8 (n:ℕ) (hn:0< n) (p:Fin (2*n)->Option Bool) (b₀:Bool)
  (s:ℕ) (hs:s< 2*n) (b:Bool) (c0 c1:ℕ) :
  w7 n hn p b₀ s b c0 c1<=2^(2*n):=by
 rw [bk n hn p b₀ s hs b c0 c1]
 have h1:(Finset.filter (fun y:Fin (s+1)->Bool =>
   y ⟨0,by omega⟩=b₀/\y ⟨s,by omega⟩=b /\
   (∀ i:Fin (s+1),xr p ⟨i.1,by omega⟩ (y i)=true) /\
   (Finset.univ.filter (fun e:Fin s=>e.1 %2=0/\y ⟨e.1,by omega⟩≠y ⟨e.1+1,by omega⟩)).card=c0 /\
   (Finset.univ.filter (fun e:Fin s=>e.1 %2=1/\y ⟨e.1,by omega⟩≠y ⟨e.1+1,by omega⟩)).card=c1)
   Finset.univ).card<=(Finset.univ:Finset (Fin (s+1)->Bool)).card :=
  Finset.card_filter_le _ _
 have h2:(Finset.univ:Finset (Fin (s+1)->Bool)).card=2^(s+1):=by
  simp [Fintype.card_fun]
 exact le_trans h1 (by rw [h2];exact Nat.pow_le_pow_right (by omega) (by omega))
lemma km (n:ℕ) (hn:0< n) (b:ℕ) (hb:n+1<=2^b)
  (p:Fin (2*n)->Option Bool) (junk:Fin (2*n)->Bool)
  (d1 d2:Fin (n+1)) :
  let inp:Fin (4*n+2*b)->Bool:=fun k =>
    if h1:k.1< 2*n then (p ⟨k.1,h1⟩).isSome
    else if h2:k.1< 4*n then (p ⟨k.1-2*n,by omega⟩).getD (junk ⟨k.1-2*n,by omega⟩)
    else if h3:k.1< 4*n+b then d1.1.testBit (k.1-4*n)
    else d2.1.testBit (k.1-(4*n+b))
  q2 (2*n+1) (ys n hn b inp)=xe n hn p d1.1 d2.1:=by
 intro inp
 let M:=n+1
 let W:=2*n+1
 set u:Fin (4*n)->Bool:=fun k=>inp ⟨k.1,by omega⟩
 have hu_eq:u=fun j:Fin (4*n)=>if h:j.1< 2*n then (p ⟨j.1,h⟩).isSome
    else (p ⟨j.1-2*n,by omega⟩).getD (junk ⟨j.1-2*n,by omega⟩):=by
  funext j;dsimp only [u,inp]
  by_cases h1:j.1< 2*n
  . simp [h1]
  . simp [h1,j.isLt]
 have hd1_eq:(fun j:Fin b=>inp ⟨4*n+j.1,by omega⟩)=q3 b d1.1:=by
  funext j;dsimp only [inp,q3];have hj:=j.isLt
  simp [show ¬ (4*n+j.1< 2*n) by omega,show ¬ (4*n+j.1< 4*n) by omega,
        show 4*n+j.1< 4*n+b by omega]
 have hd2_eq:(fun j:Fin b=>inp ⟨4*n+b+j.1,by omega⟩)=q3 b d2.1:=by
  funext j;dsimp only [inp,q3]
  simp [show ¬ (4*n+b+j.1< 2*n) by omega,show ¬ (4*n+b+j.1< 4*n) by omega,
        show ¬ (4*n+b+j.1< 4*n+b) by omega]
 have hpow_lt:2^(2*n)< 2^W:=Nat.pow_lt_pow_right (by omega) (by dsimp [W];omega)
 have hW_pow:1< 2^W:=by
  have:2^1<=2^W:=Nat.pow_le_pow_right (by omega) (by dsimp [W];omega);omega
 have hdec (b':Bool) (c0 c1:ℕ) (h0:c0< M) (h1:c1< M) :
    decide (M*M<=zd n b' c0 c1)=b' /\
    (zd n b' c0 c1)%(M*M)/M=c0 /\
    (zd n b' c0 c1)%(M*M)%M=c1:=by
  have hlt_mm:c0*M+c1< M*M:=by nlinarith
  have hrew:zd n b' c0 c1=b'.toNat*(M*M)+(c0*M+c1):=by unfold zd;dsimp [M];ring
  have hmod:(zd n b' c0 c1)%(M*M)=c0*M+c1:=by
    rw [hrew,Nat.add_comm,Nat.add_mul_mod_self_right,Zm hlt_mm]
  refine ⟨?_,?_,?_⟩
  . rw [hrew];cases b' <;> simp <;> omega
  . rw [hmod,Nat.add_comm,Nat.add_mul_div_right _ _ (by dsimp [M];omega),Nat.div_eq_of_lt h1,Nat.zero_add]
  . rw [hmod,Nat.add_comm,Nat.add_mul_mod_self_right,Zm h1]
 have hevalB0 (b₀:Bool) (i1 i2:Fin M) :
    q2 W (q5 (K:=M*M) (d:=W) (wn n hn b₀ u) ⟨i1.1*M+i2.1,by
      have:=i1.isLt;have:=i2.isLt;nlinarith⟩) =
    (if false≠b₀ then (if 0< i2.1 then w7 n hn p b₀ (2*n-1) false i1.1 (i2.1-1) else 0)
     else w7 n hn p b₀ (2*n-1) false i1.1 i2.1) +
    (if true≠b₀ then (if 0< i2.1 then w7 n hn p b₀ (2*n-1) true i1.1 (i2.1-1) else 0)
     else w7 n hn p b₀ (2*n-1) true i1.1 i2.1):=by
  have hstep_inv:∀ t ≤ 2*n-1,
      ∀ (b':Bool) (c0 c1:ℕ) (h0:c0< M) (h1:c1< M),
        q2 W (q5 (K:=2*M*M) (d:=W)
          (((List.finRange (2*n-1)).take t).foldl (fun prev s=>xx n hn s u prev) (xw n hn b₀ u))
          ⟨zd n b' c0 c1,zq n b' h0 h1⟩) =
        w7 n hn p b₀ t b' c0 c1:=by
    intro t ht
    induction t with
    | zero =>
      intro b' c0 c1 h0 h1;simp only [Zn,Zi,xw,qb,w7]
      have hiff:zd n b' c0 c1=zd n b₀ 0 0 ↔ b'=b₀/\c0=0/\c1=0:=by
        constructor
        . intro h;have d1':=hdec b' c0 c1 h0 h1;have d2':=hdec b₀ 0 0 (by dsimp [M];omega) (by dsimp [M];omega);rw [h] at d1';exact ⟨d1'.1.symm.trans d2'.1,d1'.2.1.symm.trans d2'.2.1,d1'.2.2.symm.trans d2'.2.2⟩
        . rintro ⟨rfl,rfl,rfl⟩;rfl
      by_cases hhit:zd n b' c0 c1=zd n b₀ 0 0
      . rw [if_pos hhit]
        rcases hiff.mp hhit with ⟨rfl,rfl,rfl⟩
        rw [hu_eq,p6]
        cases hal:xr p ⟨0,by omega⟩ b'
        . simp [zn];exact q4 (by omega:0< 2^W)
        . simp [zz];exact q4 hW_pow
      . rw [if_neg hhit,q4 (by omega:0< 2^W)];rw [if_neg (fun hc=>hhit (hiff.mpr ⟨hc.1,hc.2.2.1,hc.2.2.2⟩))]
    | succ t iht =>
      intro b' c0 c1 h0 h1
      have htake:(List.finRange (2*n-1)).take (t+1)=(List.finRange (2*n-1)).take t++[⟨t,by omega⟩]:=by
        rw [Zt (by simp;omega)];simp [Zg]
      rw [htake,Zl,Zo,Zi];set prevTab:=((List.finRange (2*n-1)).take t).foldl (fun prev s=>xx n hn s u prev) (xw n hn b₀ u);dsimp only [xx];rw [qb]
      rcases hdec b' c0 c1 h0 h1 with ⟨db,dc0,dc1⟩
      dsimp only [M] at db dc0 dc1;simp only [db,dc0,dc1,w7,show t+1< 2*n by omega,Zd,kj];rw [hu_eq,p6]
      cases hal:xr p ⟨t+1,by omega⟩ b'
      . simp [zn];exact q4 (by omega:0< 2^W)
      . rw [zz,if_pos rfl,qr,qc]
        have ht_val (bPrev:Bool) :
            q2 W (if bPrev≠b' then
             if t %2=0 then
              if 0< c0 then q5 (K:=2*M*M) (d:=W) prevTab ⟨zd n bPrev (c0-1) c1,zq n bPrev (by omega) h1⟩ else q3 W 0
             else
              if 0< c1 then q5 (K:=2*M*M) (d:=W) prevTab ⟨zd n bPrev c0 (c1-1),zq n bPrev h0 (by omega)⟩ else q3 W 0
            else q5 (K:=2*M*M) (d:=W) prevTab ⟨zd n bPrev c0 c1,zq n bPrev h0 h1⟩) =
            if bPrev≠b' then
             if t %2=0 then (if 0< c0 then w7 n hn p b₀ t bPrev (c0-1) c1 else 0)
             else (if 0< c1 then w7 n hn p b₀ t bPrev c0 (c1-1) else 0)
            else w7 n hn p b₀ t bPrev c0 c1:=by
          split_ifs
          . exact iht (by omega) bPrev (c0-1) c1 (by omega) h1
          . exact q4 (by omega:0< 2^W)
          . exact iht (by omega) bPrev c0 (c1-1) h0 (by omega)
          . exact q4 (by omega:0< 2^W)
          . exact iht (by omega) bPrev c0 c1 h0 h1
        rw [ht_val false,ht_val true]
        have hsum_eq :
            (if false≠b' then if t %2=0 then if 0< c0 then w7 n hn p b₀ t false (c0-1) c1 else 0
             else if 0< c1 then w7 n hn p b₀ t false c0 (c1-1) else 0 else w7 n hn p b₀ t false c0 c1) +
            (if true≠b' then if t %2=0 then if 0< c0 then w7 n hn p b₀ t true (c0-1) c1 else 0
             else if 0< c1 then w7 n hn p b₀ t true c0 (c1-1) else 0 else w7 n hn p b₀ t true c0 c1) =
            w7 n hn p b₀ (t+1) b' c0 c1:=by
          simp only [w7,show t+1< 2*n by omega,Zd,kj,hal,Zh]
        have hle:=c8 n hn p b₀ (t+1) (by omega) b' c0 c1;simp only [Zp,Zq];rw [Zm (by omega)]
  have hfull:=hstep_inv (2*n-1) le_rfl;rw [Zk (by simp)] at hfull;dsimp only [wn];rw [qb]
  have hdiv:(i1.1*M+i2.1)/(n+1)=i1.1:=by
    dsimp [M];rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt i2.isLt,Nat.zero_add]
  have hmod:(i1.1*M+i2.1)%(n+1)=i2.1:=by
    dsimp [M];rw [Nat.add_comm,Nat.add_mul_mod_self_right,Zm i2.isLt]
  simp only [hdiv,hmod];set fullTab:=(List.finRange (2*n-1)).foldl (fun prev s=>xx n hn s u prev) (xw n hn b₀ u);rw [qr,qc]
  have hlast (bLast:Bool) :
      q2 W (if bLast≠b₀ then
        if 0< i2.1 then q5 (K:=2*M*M) (d:=W) fullTab ⟨zd n bLast i1.1 (i2.1-1),zq n bLast i1.isLt (by omega)⟩ else q3 (2*n+1) 0
      else q5 (K:=2*M*M) (d:=W) fullTab ⟨zd n bLast i1.1 i2.1,zq n bLast i1.isLt i2.isLt⟩) =
      if bLast≠b₀ then (if 0< i2.1 then w7 n hn p b₀ (2*n-1) bLast i1.1 (i2.1-1) else 0)
      else w7 n hn p b₀ (2*n-1) bLast i1.1 i2.1:=by
    split_ifs
    . exact hfull bLast i1.1 (i2.1-1) i1.isLt (by omega)
    . exact q4 (by omega:0< 2^W)
    . exact hfull bLast i1.1 i2.1 i1.isLt i2.isLt
  rw [hlast false,hlast true]
  have hcyc_le:xe n hn p i1.1 i2.1<=2^(2*n):=by
    rw [y7,wt];exact le_trans (Finset.card_filter_le _ _) (by simp [Fintype.card_fun])
  have hpart_le :
      (if false≠b₀ then (if 0< i2.1 then w7 n hn p b₀ (2*n-1) false i1.1 (i2.1-1) else 0)
       else w7 n hn p b₀ (2*n-1) false i1.1 i2.1) +
      (if true≠b₀ then (if 0< i2.1 then w7 n hn p b₀ (2*n-1) true i1.1 (i2.1-1) else 0)
       else w7 n hn p b₀ (2*n-1) true i1.1 i2.1)<=xe n hn p i1.1 i2.1:=by
    unfold xe;cases b₀ <;> dsimp only <;> omega
  simp only [Zp,Zq];rw [Zm (by omega)]
 dsimp only [ys];rw [hd1_eq,hd2_eq];have hv1:q2 b (q3 b d1.1)=d1.1:=q4 (lt_of_lt_of_le d1.isLt hb);have hv2:q2 b (q3 b d2.1)=d2.1:=q4 (lt_of_lt_of_le d2.isLt hb);dsimp only [jb];rw [Zr (by rw [hv1];exact d1.isLt),Zr (by rw [hv2];exact d2.isLt)]
 have hidx_eq:(⟨q2 b (q3 b d1.1)*(n+1)+q2 b (q3 b d2.1),
    by have h1:(q2 b (q3 b d1.1)+1)*(n+1)<=(n+1)*(n+1):=Zw _ (by rw [hv1];exact d1.isLt)
       have h2:q2 b (q3 b d2.1)< n+1:=by rw [hv2];exact d2.isLt
       nlinarith⟩:Fin ((n+1)*(n+1))) =
    ⟨d1.1*(n+1)+d2.1,by have:=d1.isLt;have:=d2.isLt;nlinarith⟩:=by
  apply Zx;dsimp;rw [hv1,hv2]
 rw [hidx_eq,qb,qr,qc,hevalB0 false d1 d2,hevalB0 true d1 d2]
 have hcyc_le:xe n hn p d1.1 d2.1<=2^(2*n):=by
  rw [y7,wt];exact le_trans (Finset.card_filter_le _ _) (by simp [Fintype.card_fun])
 change ((xe n hn p d1.1 d2.1)+false.toNat)%2^W=xe n hn p d1.1 d2.1;simp only [Zp,Zq];exact Zm (by omega)
lemma yz {A m:ℕ} (hm:3<=m) (hA:A<=6561*m^5):A<=m^16:=by
 have h1:6561<=m^8:=by
  calc (6561:ℕ)=3^8:=by norm_num
   _<=m^8:=Nat.pow_le_pow_left hm 8
 have h2:6561*m^5<=m^13:=by
  calc 6561*m^5<=m^8*m^5:=Zw _ h1
   _=m^13:=by rw [<- pow_add]
 exact le_trans hA (le_trans h2 (Nat.pow_le_pow_right (by omega) (by omega)))
lemma bl (n:ℕ) (hn:0< n):1< v6 n:=by
 let p0:Fin (2*n)->Option Bool:=fun _=>some false
 have hnp:z2 n p0=2*n:=by simp [z2,p0]
 have hcan:zp n hn p0=some (z3 n hn p0,(z0 n (qo n hn p0) (qd n hn p0)).1,
   (z0 n (qo n hn p0) (qd n hn p0)).2.1,
   (z0 n (qo n hn p0) (qd n hn p0)).2.2):=by
  unfold zp;simp [hnp,show 2*n≠0 by omega]
 have hspec:=(x2 n (zp n hn p0) (x1 n hn p0)).1;rw [hcan] at hspec;simp only [x5] at hspec;omega
def wh (n:ℕ) (k:Fin (4*n)):Fin (4*n) :=
 if h:k.1< 2*n then
  let u:=z6 n ⟨k.1,h⟩
  ⟨(if u.1 then n else 0)+u.2.1,by have:=u.2.isLt;cases u.1 <;> simp <;> omega⟩
 else
  let u:=z6 n ⟨k.1-2*n,by omega⟩
  ⟨2*n+(if u.1 then n else 0)+u.2.1,by have:=u.2.isLt;cases u.1 <;> simp <;> omega⟩
def jm (n Bc w:ℕ) (hn:0< n) (hBc:0< Bc) (u:Fin (4*n)->Bool):Fin w->Bool :=
 let anyPin:=xj (fun k:Fin (2*n)=>u ⟨k.1,by omega⟩)
 let cnts:=wo n hn Bc u
 let evIn:Fin ((2*n+1)*Bc)->Bool:=qn (K:=2*n+1) (d:=Bc) (fun slot =>
  if h:slot.1< 2*n then q5 (K:=6*n) (d:=Bc) cnts ⟨4*n+slot.1,by omega⟩
  else q3 Bc 0)
 let evRed:=vw n Bc evIn
 let rankIn:Fin ((6*n+1)*Bc)->Bool:=qn (K:=6*n+1) (d:=Bc) (fun slot =>
  if h:slot.1< 4*n then q5 (K:=6*n) (d:=Bc) cnts ⟨slot.1,by omega⟩
  else q5 (K:=2*n+1) (d:=Bc) evRed ⟨slot.1-4*n,by omega⟩)
 zb anyPin (q3 w 0) (p5 n Bc w hBc rankIn)
def x7 (n Bc w:ℕ) (hBc:0< Bc) (z:Fin w->Bool):Fin (4*n)->Bool :=
 let isPos:=xj z
 let unr:=xi n Bc w hBc z
 let evIn:Fin ((2*n+1)*Bc)->Bool:=qn (K:=2*n+1) (d:=Bc) (fun slot =>
  q5 (K:=6*n+1) (d:=Bc) unr ⟨4*n+slot.1,by omega⟩)
 let evSp:=yk n Bc evIn
 let recIn:Fin (6*n*Bc)->Bool:=qn (K:=6*n) (d:=Bc) (fun slot =>
  if h:slot.1< 4*n then q5 (K:=6*n+1) (d:=Bc) unr ⟨slot.1,by omega⟩
  else q5 (K:=2*n+1) (d:=Bc) evSp ⟨slot.1-4*n,by omega⟩)
 let pins:=w5 n Bc recIn
 fun k:Fin (4*n)=>if k.1< 2*n then isPos&&pins k else pins k
def b5 (n Bc w b:ℕ) (hn:0< n) (hBc:0< Bc) (inp:Fin (w+2*b)->Bool):Fin (2*n+1)->Bool :=
 let cycPins:=x7 n Bc w hBc (fun j:Fin w=>inp ⟨j.1,by omega⟩)
 ys n hn b (q1 cycPins (fun j:Fin (2*b)=>inp ⟨w+j.1,by omega⟩))
lemma c4 (n Bc w:ℕ) (hn:0< n) (hBc:0< Bc) (h4n:4*n< 2^Bc)
  (hBc_m:Bc<=2*(n+2)) (hw_m:w<=4*(n+2)) :
  q0 (fun x:Fin (4*n)->Bool=>jm n Bc w hn hBc (fun k=>x (wh n k))) ((n+2)^16):=by
 set m:=n+2
 have hm3:3<=m:=by dsimp [m];omega
 have hcnts:=k0 n hn Bc
 have hevIn:q0 (fun c:Fin (6*n*Bc)->Bool=>qn (K:=2*n+1) (d:=Bc) (fun slot =>
    if h:slot.1< 2*n then q5 (K:=6*n) (d:=Bc) c ⟨4*n+slot.1,by omega⟩
    else q3 Bc 0)) 0:=by
  refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
  split_ifs
  . exact qa (q0.id _) _
  . exact q0.k _
 have hevRed:=q0.c hevIn (kl n Bc);have hpair1:=q0.r (q0.id (6*n*Bc)) hevRed
 have hrankIn:q0 (fun q:Fin (6*n*Bc+(2*n+1)*Bc)->Bool =>
    qn (K:=6*n+1) (d:=Bc) (fun slot =>
      if h:slot.1< 4*n then q5 (K:=6*n) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨slot.1,by omega⟩
      else q5 (K:=2*n+1) (d:=Bc) (fun a=>q ⟨6*n*Bc+a.1,by omega⟩) ⟨slot.1-4*n,by omega⟩)) 0:=by
  refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
  split_ifs
  . exact qa (q0.p _) _
  . exact qa (q0.p _) _
 have hrOut:q0 (fun u:Fin (4*n)->Bool =>
    let cnts:=wo n hn Bc u
    let evIn:Fin ((2*n+1)*Bc)->Bool:=qn (K:=2*n+1) (d:=Bc) (fun slot =>
      if h:slot.1< 2*n then q5 (K:=6*n) (d:=Bc) cnts ⟨4*n+slot.1,by omega⟩
      else q3 Bc 0)
    let evRed:=vw n Bc evIn
    let rankIn:Fin ((6*n+1)*Bc)->Bool:=qn (K:=6*n+1) (d:=Bc) (fun slot =>
      if h:slot.1< 4*n then q5 (K:=6*n) (d:=Bc) cnts ⟨slot.1,by omega⟩
      else q5 (K:=2*n+1) (d:=Bc) evRed ⟨slot.1-4*n,by omega⟩)
    p5 n Bc w hBc rankIn)
    (6*n*(2*n*(4*n+10+17*Bc))+n*(70*Bc) +
     (5*n*(2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w)+100*Bc+20)+13*w)):=by
  have hc1:=q0.c hcnts (q0.c (q0.c hpair1 hrankIn) (bd n Bc w hBc h4n))
  refine (hc1.mono (by omega)).congr (fun u=>?_)
  congr 1;congr 1;funext slot;split_ifs
  . congr 1;funext a;dsimp only [q1];rw [Zr a.isLt]
  . congr 1;funext a;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have hany:q0 (fun (u:Fin (4*n)->Bool) (_:Fin 1)=>xj (fun k:Fin (2*n)=>u ⟨k.1,by omega⟩)) (2*n) :=
  (jo (q0.p _)).mono (by omega)
 have hcyc:=zg hany (q0.k (q3 w 0)) hrOut;have htot:=q0.c (q0.p (wh n)) hcyc
 refine htot.mono (yz hm3 ?_)
 have h1:4*Bc+4*w+4<=28*m:=by omega
 have h2:(2*n+1)*(n+1)*2*(4*Bc+4*w+4)<=112*m^3:=by
  have:2*n+1<=2*m:=by dsimp [m];omega
  have:n+1<=m:=by dsimp [m];omega
  calc (2*n+1)*(n+1)*2*(4*Bc+4*w+4)
    <= (2*m)*m*2*(28*m):=by gcongr
    _=112*m^3:=by ring
 have h3:64*Bc+17*w<=196*m:=by omega
 have h4:(2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w<=308*m^3:=by
  have:m<=m^3:=le_self_pow₀ (by omega) (by omega);omega
 have h5:2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w)<=616*m^4:=by
  calc _<=(2*m)*(308*m^3):=by gcongr;dsimp [m];omega
    _=616*m^4:=by ring
 have h6:5*n*(2*n*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+17*w)+100*Bc+20)<=4180*m^5:=by
  have:100*Bc+20<=220*m^4:=by have:m<=m^4:=le_self_pow₀ (by omega) (by omega);omega
  calc _<=(5*m)*(836*m^4):=by
        gcongr
        . dsimp [m];omega
        . omega
    _=4180*m^5:=by ring
 have h7:6*n*(2*n*(4*n+10+17*Bc))<=576*m^3:=by
  have:4*n+10+17*Bc<=48*m:=by dsimp [m];omega
  calc _<=6*m*(2*m*(48*m)):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
    _=576*m^3:=by ring
 have h8:n*(70*Bc)<=140*m^2:=by
  calc _<=m*(70*(2*m)):=by gcongr;dsimp [m];omega
    _=140*m^2:=by ring
 have hm1:m<=m^5:=le_self_pow₀ (by omega) (by omega);have hm2:m^2<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);have hm3':m^3<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);omega
lemma k7 (n Bc w:ℕ) (hn:0< n) (hBc:0< Bc) (h4n:4*n< 2^Bc)
  (hBc_m:Bc<=2*(n+2)) (hw_m:w<=4*(n+2)) :
  q0 (x7 n Bc w hBc) (5900*(n+2)^5):=by
 set m:=n+2
 have hm3:3<=m:=by dsimp [m];omega
 have hunr:=pq n Bc w hBc h4n
 have hevIn:q0 (fun u:Fin ((6*n+1)*Bc)->Bool =>
    qn (K:=2*n+1) (d:=Bc) (fun slot=>q5 (K:=6*n+1) (d:=Bc) u ⟨4*n+slot.1,by omega⟩)) 0 :=
  (z4 (B:=0) _ (fun slot=>qa (q0.id _) _)).mono (by simp)
 have hevSp:=q0.c hevIn (ks n Bc);have hpair1:=q0.r (q0.id ((6*n+1)*Bc)) hevSp
 have hrecIn:q0 (fun q:Fin ((6*n+1)*Bc+(2*n+1)*Bc)->Bool =>
    qn (K:=6*n) (d:=Bc) (fun slot =>
      if h:slot.1< 4*n then q5 (K:=6*n+1) (d:=Bc) (fun a=>q ⟨a.1,by omega⟩) ⟨slot.1,by omega⟩
      else q5 (K:=2*n+1) (d:=Bc) (fun a=>q ⟨(6*n+1)*Bc+a.1,by omega⟩) ⟨slot.1-4*n,by omega⟩)) 0:=by
  refine (z4 (B:=0) _ (fun slot=>?_)).mono (by simp)
  split_ifs
  . exact qa (q0.p _) _
  . exact qa (q0.p _) _
 have hpins:q0 (fun z:Fin w->Bool =>
    let unr:=xi n Bc w hBc z
    let evIn:Fin ((2*n+1)*Bc)->Bool:=qn (K:=2*n+1) (d:=Bc) (fun slot =>
      q5 (K:=6*n+1) (d:=Bc) unr ⟨4*n+slot.1,by omega⟩)
    let evSp:=yk n Bc evIn
    let recIn:Fin (6*n*Bc)->Bool:=qn (K:=6*n) (d:=Bc) (fun slot =>
      if h:slot.1< 4*n then q5 (K:=6*n+1) (d:=Bc) unr ⟨slot.1,by omega⟩
      else q5 (K:=2*n+1) (d:=Bc) evSp ⟨slot.1-4*n,by omega⟩)
    w5 n Bc recIn)
    (14*w+5*n*((2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10)+100*Bc+20) +
     n*(70*Bc) +
     (2*n*(n*(4*n*(4*Bc+7)+27*Bc+5)) +
      4*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1))) +
      n*(2*(4*n*(4*Bc+7)+17*Bc+5)+20*Bc))):=by
  have hc:=q0.c hunr (q0.c (q0.c hpair1 hrecIn) (jz n Bc))
  refine (hc.mono (by omega)).congr (fun z=>?_)
  congr 1;congr 1;funext slot;split_ifs
  . congr 1;funext a;dsimp only [q1];rw [Zr a.isLt]
  . congr 1;funext a;dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
 have hpos:=jo (q0.id w);have hpair2:=q0.r hpos hpins
 have hmask:q0 (fun q:Fin (1+4*n)->Bool =>
    fun k:Fin (4*n)=>if k.1< 2*n then q ⟨0,by omega⟩&&q ⟨1+k.1,by omega⟩ else q ⟨1+k.1,by omega⟩) (4*n):=by
  refine (q0.f (B:=1) _ (fun k=>?_)).mono (by omega)
  split_ifs
  . exact q0.a (q0.p _) (q0.p _)
  . exact (q0.p _).mono (by omega)
 have hcomb:q0 (x7 n Bc w hBc) _:=((q0.c hpair2 hmask).mono le_rfl).congr (fun z=>by
  funext k;dsimp only [x7];set unr:=xi n Bc w hBc z
  set evIn:Fin ((2*n+1)*Bc)->Bool:=qn (K:=2*n+1) (d:=Bc) (fun slot =>
    q5 (K:=6*n+1) (d:=Bc) unr ⟨4*n+slot.1,by omega⟩)
  set evSp:=yk n Bc evIn
  set recIn:Fin (6*n*Bc)->Bool:=qn (K:=6*n) (d:=Bc) (fun slot =>
    if h:slot.1< 4*n then q5 (K:=6*n+1) (d:=Bc) unr ⟨slot.1,by omega⟩
    else q5 (K:=2*n+1) (d:=Bc) evSp ⟨slot.1-4*n,by omega⟩)
  have e0:q1 (fun _:Fin 1=>xj z) (w5 n Bc recIn) ⟨0,by omega⟩=xj z:=by
    dsimp only [q1];rw [Zr (by omega)]
  have ek:q1 (fun _:Fin 1=>xj z) (w5 n Bc recIn) ⟨1+k.1,by omega⟩=w5 n Bc recIn k:=by
    dsimp only [q1];rw [Zb (by omega)];congr 1;exact Zx (by dsimp;omega)
  split_ifs <;> simp only [e0,ek])
 refine hcomb.mono ?_
 have h1:4*Bc+4*w+4<=28*m:=by omega
 have h2:(2*n+1)*(n+1)*2*(4*Bc+4*w+4)<=112*m^3:=by
  calc _<=(2*m)*m*2*(28*m):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
    _=112*m^3:=by ring
 have h3:64*Bc+28*w+10<=250*m:=by omega
 have h4:(2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10<=362*m^3:=by
  have:m<=m^3:=le_self_pow₀ (by omega) (by omega);omega
 have h5:(2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10)<=724*m^4:=by
  calc _<=(2*m)*(362*m^3):=by gcongr;dsimp [m];omega
    _=724*m^4:=by ring
 have h6:5*n*((2*n+1)*((2*n+1)*(n+1)*2*(4*Bc+4*w+4)+64*Bc+28*w+10)+100*Bc+20)<=4720*m^5:=by
  have:100*Bc+20<=220*m^4:=by have:m<=m^4:=le_self_pow₀ (by omega) (by omega);omega
  calc _<=(5*m)*(944*m^4):=by
        gcongr
        . dsimp [m];omega
        . omega
    _=4720*m^5:=by ring
 have h7:n*(70*Bc)<=140*m^2:=by
  calc _<=m*(70*(2*m)):=by gcongr;dsimp [m];omega
    _=140*m^2:=by ring
 have h8:2*n*(n*(4*n*(4*Bc+7)+27*Bc+5))<=240*m^4:=by
  have ha:4*n*(4*Bc+7)<=60*m^2:=by
    have:4*Bc+7<=15*m:=by omega
    calc _<=4*m*(15*m):=by gcongr;dsimp [m];omega
      _=60*m^2:=by ring
  have hb':27*Bc+5<=60*m^2:=by have:m<=m^2:=le_self_pow₀ (by omega) (by omega);omega
  calc _<=2*m*(m*(120*m^2)):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
        . omega
    _=240*m^4:=by ring
 have h9:4*n*(n*(37*Bc+n*(2*Bc+4*(Bc+1)+1)))<=376*m^4:=by
  have ha:n*(2*Bc+4*(Bc+1)+1)<=17*m^2:=by
    have:2*Bc+4*(Bc+1)+1<=17*m:=by omega
    calc _<=m*(17*m):=by gcongr;dsimp [m];omega
      _=17*m^2:=by ring
  have hb':37*Bc<=77*m^2:=by have:m<=m^2:=le_self_pow₀ (by omega) (by omega);omega
  calc _<=4*m*(m*(94*m^2)):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
        . omega
    _=376*m^4:=by ring
 have h10:n*(2*(4*n*(4*Bc+7)+17*Bc+5)+20*Bc)<=240*m^3:=by
  have ha:4*n*(4*Bc+7)<=60*m^2:=by
    have:4*Bc+7<=15*m:=by omega
    calc _<=4*m*(15*m):=by gcongr;dsimp [m];omega
      _=60*m^2:=by ring
  have hb':17*Bc+5<=40*m^2:=by have:m<=m^2:=le_self_pow₀ (by omega) (by omega);omega
  have hc':20*Bc<=40*m^2:=by have:m<=m^2:=le_self_pow₀ (by omega) (by omega);omega
  calc _<=m*(240*m^2):=by
        gcongr
        . dsimp [m];omega
        . omega
    _=240*m^3:=by ring
 have hm1:m<=m^5:=le_self_pow₀ (by omega) (by omega);have hm2:m^2<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);have hm3':m^3<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);have hm4:m^4<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);omega
lemma be (n Bc w b:ℕ) (hn:0< n) (hBc:0< Bc) (h4n:4*n< 2^Bc)
  (hb_pow:n+1<=2^b) (hBc_m:Bc<=2*(n+2)) (hw_m:w<=4*(n+2)) (hb_m:b<=n+2) :
  q0 (b5 n Bc w b hn hBc) ((n+2)^16):=by
 set m:=n+2
 have hm3:3<=m:=by dsimp [m];omega
 have hrep_hc:=k7 n Bc w hn hBc h4n hBc_m hw_m;have h1:=q0.c (q0.p (fun j:Fin w=>(⟨j.1,by omega⟩:Fin (w+2*b)))) hrep_hc;have h2:q0 (fun inp:Fin (w+2*b)->Bool=>fun j:Fin (2*b)=>inp ⟨w+j.1,by omega⟩) 0:=q0.p _;have h3:=q0.c (q0.r h1 h2) (k1 n hn b hb_pow)
 refine h3.mono (yz hm3 ?_)
 have ha:2*(n+1)*(n+1)*(4*(2*n+1)+7)<=30*m^3:=by
  have:4*(2*n+1)+7<=15*m:=by dsimp [m];omega
  calc _<=2*m*m*(15*m):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
   _=30*m^3:=by ring
 have hb':(2*n-1)*(2*(n+1)*(n+1)*(17*(2*n+1)+7))<=164*m^4:=by
  have:17*(2*n+1)+7<=41*m:=by dsimp [m];omega
  calc _<=(2*m)*(2*m*m*(41*m)):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
        . dsimp [m];omega
   _=164*m^4:=by ring
 have hc':(n+1)*(n+1)*(13*(2*n+1))<=26*m^3:=by
  have:13*(2*n+1)<=26*m:=by dsimp [m];omega
  calc _<=m*m*(26*m):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
   _=26*m^3:=by ring
 have hd':(n+1)*(n+1)*(4*b+4*(2*n+1)+1)<=13*m^3:=by
  have:4*b+4*(2*n+1)+1<=13*m:=by dsimp [m];omega
  calc _<=m*m*(13*m):=by
        gcongr
        . dsimp [m];omega
        . dsimp [m];omega
   _=13*m^3:=by ring
 have hm3':m^3<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);have hm4:m^4<=m^5:=Nat.pow_le_pow_right (by omega) (by omega);have hm5:(n+2)^5=m^5:=rfl;rw [hm5];omega
lemma c5 (n Bc w:ℕ) (hn:0< n) (hBc:0< Bc) (h4n:4*n< 2^Bc) (hw:v6 n<=2^w)
   (pCyc:Fin (2*n)->Option Bool) (jCyc:Fin (2*n)->Bool) :
   q2 w (jm n Bc w hn hBc (fun k:Fin (4*n) =>
     if h:k.1< 2*n then (pCyc ⟨k.1,h⟩).isSome
     else (pCyc ⟨k.1-2*n,by omega⟩).getD (jCyc ⟨k.1-2*n,by omega⟩))) =
   x5 n (zp n hn pCyc):=by
 have hN_gt1:1< v6 n:=bl n hn
 set u:Fin (4*n)->Bool:=fun k =>
   if h:k.1< 2*n then (pCyc ⟨k.1,h⟩).isSome
   else (pCyc ⟨k.1-2*n,by omega⟩).getD (jCyc ⟨k.1-2*n,by omega⟩)
 dsimp only [jm]
 by_cases hnp:z2 n pCyc=0
 . have hallF:∀ k:Fin (2*n),u ⟨k.1,by omega⟩=false:=by
     intro k
     have hnone:pCyc k=none:=by
       by_contra hne
       have hmem:k ∈ Finset.univ.filter (fun k:Fin (2*n)=>(pCyc k).isSome):=by
         simp [Option.isSome_iff_ne_none,hne]
       have:0< z2 n pCyc:=Finset.card_pos.mpr ⟨k,hmem⟩;omega
     simp [u,k.isLt,hnone]
   have hanyF:xj (fun k:Fin (2*n)=>u ⟨k.1,by omega⟩)=false :=
     (x3 _).mpr hallF
   rw [hanyF,zn,q4 (by omega:0< 2^w)];unfold zp;rw [if_pos hnp];rfl
 . have hpos:0< z2 n pCyc:=by omega
   have hanyT:xj (fun k:Fin (2*n)=>u ⟨k.1,by omega⟩)=true:=by
     cases h:xj (fun k:Fin (2*n)=>u ⟨k.1,by omega⟩)
     . exfalso;have hf:=(x3 _).mp h
       have:z2 n pCyc=0:=by
         unfold z2;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro k _;have:=hf k;simp [u,k.isLt] at this;simp [this]
       omega
     . rfl
   rw [hanyT,zz];have hex:=kk n hn Bc (by omega) pCyc jCyc;have hH:=xf n hn pCyc hpos
   have hev_len:∑ j:Fin n,2*(j.1+1)*(qo n hn pCyc j+qd n hn pCyc j)<=2*n:=by
     have:=hH.2.1;unfold zj at this;omega
   have hred:=ph n Bc h4n (qo n hn pCyc) (qd n hn pCyc) hev_len
     (qn (K:=2*n+1) (d:=Bc) (fun slot =>
       if h:slot.1< 2*n then q5 (K:=6*n) (d:=Bc) (wo n hn Bc u) ⟨4*n+slot.1,by omega⟩
       else q3 Bc 0))
     (fun j=>by rw [qb,Zr (by have:=j.isLt;dsimp;omega)];exact hex.2.1 j)
     (fun j=>by
       rw [qb,Zr (by have:=j.isLt;dsimp;omega)];have heq:(⟨4*n+(n+j.1),by omega⟩:Fin (6*n))=⟨5*n+j.1,by omega⟩:=Zx (by dsimp;omega)
       rw [heq];exact hex.2.2 j)
     (by rw [qb,Zb (by dsimp;omega),q4 (by omega:0< 2^Bc)])
   have hcan:zp n hn pCyc=some (z3 n hn pCyc,
       (z0 n (qo n hn pCyc) (qd n hn pCyc)).1,
       (z0 n (qo n hn pCyc) (qd n hn pCyc)).2.1,
       (z0 n (qo n hn pCyc) (qd n hn pCyc)).2.2):=by
     unfold zp;rw [if_neg hnp]
   have hv:=x1 n hn pCyc;rw [hcan] at hv ⊢;unfold x5;apply c7 n Bc w hBc h4n hw _ _ _ _ hv
   . intro o;rw [qb,Zr o.isLt];exact hex.1 o
   . intro j;rw [qb,Zb (by dsimp;omega)];have heq:(⟨4*n+j.1-4*n,by omega⟩:Fin (2*n+1))=⟨j.1,by omega⟩:=Zx (by dsimp;omega);rw [heq];exact hred.1 j
   . intro j;rw [qb,Zb (by dsimp;omega)];have heq:(⟨5*n+j.1-4*n,by omega⟩:Fin (2*n+1))=⟨n+j.1,by omega⟩:=Zx (by dsimp;omega);rw [heq];exact hred.2.1 j
   . rw [qb,Zb (by dsimp;omega)];have heq:(⟨6*n-4*n,by omega⟩:Fin (2*n+1))=⟨2*n,by omega⟩:=Zx (by dsimp;omega);rw [heq];exact hred.2.2
lemma c6 (n Bc w:ℕ) (hn:0< n) (hBc:0< Bc) (h4n:4*n< 2^Bc) (hw:v6 n<=2^w)
   (z:Fin w->Bool) (hz:q2 w z< v6 n) :
   let pCyc:=wg n hn (zy n (q2 w z))
   ∀ k:Fin (2*n),x7 n Bc w hBc z ⟨k.1,by omega⟩=(pCyc k).isSome /\
    (x7 n Bc w hBc z ⟨k.1,by omega⟩=true->pCyc k=some (x7 n Bc w hBc z ⟨2*n+k.1,by omega⟩)):=by
 intro pCyc;dsimp only [x7]
 by_cases hz0:q2 w z=0
 . have hanyF:xj z=false:=by
    rw [x3];intro i
    have:z=q3 w 0:=by rw [<- qm w z,hz0]
    rw [this];simp [q3]
   have hp_none:pCyc=fun _=>none:=by simp [pCyc,zy,hz0,wg]
   intro k;simp only [k.isLt,Zh,hanyF,Bool.false_and,hp_none];exact ⟨rfl,fun h=>by cases h⟩
 . have hanyT:xj z=true:=by
    cases h:xj z
    . exfalso;have hf:=(x3 _).mp h
      have:q2 w z=0:=by unfold q2;apply Finset.sum_eq_zero;intro i _;simp [hf i]
      omega
    . rfl
   have hunr:=bp n Bc w hBc h4n hw z (by omega) hz;have huc:=xq n (q2 w z) hz;simp only [zy,hz0,Zj,xp,ju] at huc;set u:=qq n (4*n) 0 0 false (q2 w z-1);have huc_len:yn n u.1+zj n u.2.1 u.2.2.1=2*n:=huc.1.2.1
   set evIn:Fin ((2*n+1)*Bc)->Bool:=qn (K:=2*n+1) (d:=Bc) (fun slot =>
    q5 (K:=6*n+1) (d:=Bc) (xi n Bc w hBc z) ⟨4*n+slot.1,by omega⟩)
   have hsp:=ps n Bc h4n u.2.1 u.2.2.1 u.2.2.2 (by omega) huc.1.2.2.2.2
    evIn
    (fun j=>by rw [qb];exact hunr.2.1 j)
    (fun j=>by
      rw [qb];have heq:(⟨4*n+(n+j.1),by omega⟩:Fin (6*n+1))=⟨5*n+j.1,by omega⟩:=Zx (by dsimp;omega)
      rw [heq];exact hunr.2.2.1 j)
    (by
      rw [qb];have heq:(⟨4*n+2*n,by omega⟩:Fin (6*n+1))=⟨6*n,by omega⟩:=Zx (by dsimp;omega)
      rw [heq];exact hunr.2.2.2)
   have hsp_spec:=p4 n u.1 u.2.1 u.2.2.1 u.2.2.2 huc.1.2.2.2.2
   have hrec:=ke n Bc hn h4n u.1 (x6 n u.2.1 u.2.2.1 u.2.2.2).1 (x6 n u.2.1 u.2.2.1 u.2.2.2).2.1
    (by have:=hsp_spec.2.1;omega) huc.1.2.2.1
    (qn (K:=6*n) (d:=Bc) (fun slot =>
      if h:slot.1< 4*n then q5 (K:=6*n+1) (d:=Bc) (xi n Bc w hBc z) ⟨slot.1,by omega⟩
      else q5 (K:=2*n+1) (d:=Bc) (yk n Bc evIn) ⟨slot.1-4*n,by omega⟩))
    (fun o=>by rw [qb,Zr o.isLt];exact hunr.1 o)
    (fun j=>by
      rw [qb,Zb (by dsimp;omega)];have heq:(⟨4*n+j.1-4*n,by omega⟩:Fin (2*n+1))=⟨j.1,by omega⟩:=Zx (by dsimp;omega)
      rw [heq];exact hsp.1 j)
    (fun j=>by
      rw [qb,Zb (by dsimp;omega)];have heq:(⟨5*n+j.1-4*n,by omega⟩:Fin (2*n+1))=⟨n+j.1,by omega⟩:=Zx (by dsimp;omega)
      rw [heq];exact hsp.2 j)
   have hp_eq:pCyc=qg n hn (vj n u.1 (x6 n u.2.1 u.2.2.1 u.2.2.2).1 (x6 n u.2.1 u.2.2.1 u.2.2.2).2.1) 0 false (fun _=>none):=by
    simp [pCyc,zy,hz0,wg,u]
   intro k;simp only [k.isLt,Zh,hanyT,Bool.true_and,show ¬ (2*n+k.1< 2*n) by omega,Zj,hp_eq];exact hrec k
end PEqualNP.Outside.L_pcx_379_aux

theorem PEqualNP.Outside.L_pcx_379 : (∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let X := V → Bool
  let P := V → Option Bool
  let hist := fun (p : P) (d : J × J) =>
    ((Finset.univ : Finset X).filter (fun x =>
      (∀ u, p u = none ∨ p u = some (x u)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i+1))).card = d.2.val)).card
  let N := ((Finset.univ : Finset P).image hist).card
  let w := Nat.clog 2 N
  let b := 1 + Nat.log 2 n
  let raw := fun x : X => List.ofFn (fun i : I => x (false,i)) ++ List.ofFn (fun i : I => x (true,i))
  let val := fun (k : ℕ) (z : Fin k → Bool) => ∑ i : Fin k, (z i).toNat * 2^i.val
  let valid := fun (inputs : ℕ) (g : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ (n+2)^C ∧
      ∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1)
  ∃ (enc rep query : PEqualNP.CircuitLowerBounds.Circuit)
    (codeWire : Fin w → Fin (2+4*n+enc.size))
    (pinWire : Bool → V → Fin (2+w+rep.size))
    (countWire : Fin (2*n+1) → Fin (2+w+2*b+query.size)),
    valid (2+4*n) enc ∧ valid (2+w) rep ∧ valid (2+w+2*b) query ∧
    let rank := fun (p : P) (junk : X) =>
      let z := enc.wires ([false,true] ++ raw (fun u => (p u).isSome) ++ raw (fun u => (p u).getD (junk u)))
      fun i : Fin w => z.getD (codeWire i).val false
    let repr := fun (z : Fin w → Bool) (u : V) =>
      let ws := rep.wires ([false,true] ++ List.ofFn z)
      if ws.getD (pinWire false u).val false then some (ws.getD (pinWire true u).val false) else none
    let answer := fun (z : Fin w → Bool) (d : J × J) =>
      let ws := query.wires ([false,true] ++ List.ofFn z ++
        List.ofFn (fun i : Fin b => d.1.val.testBit i.val) ++ List.ofFn (fun i : Fin b => d.2.val.testBit i.val))
      val (2*n+1) (fun i => ws.getD (countWire i).val false)
    (∀ (p : P) (junk : X), val w (rank p junk) < N ∧ hist (repr (rank p junk)) = hist p ∧
      ∀ d, answer (rank p junk) d = hist p d) ∧
    (∀ (p q : P) (a b' : X), rank p a = rank q b' ↔ hist p = hist q) ∧
    ∀ z : Fin w → Bool, val w z < N → ∀ junk : X, rank (repr z) junk = z) := by
 open PEqualNP.Outside.L_pcx_379_aux in
 refine ⟨16,by omega,fun t=>?_⟩
 dsimp only;set n:=t+1
 set I:=Fin n
 set J:=Fin (n+1)
 set V:=Bool × I;set X:=V->Bool;set P:=V->Option Bool
 set hist:P->J × J->ℕ:=fun p d =>
   ((Finset.univ:Finset X).filter (fun x =>
     (∀ u,p u=none\/p u=some (x u)) /\
     (Finset.univ.filter (fun i:I=>x (false,i)≠x (true,i))).card=d.1.1 /\
     (Finset.univ.filter (fun i:I=>x (false,i)≠x (true,i+1))).card=d.2.1)).card
 set N:=((Finset.univ:Finset P).image hist).card;set w:=Nat.clog 2 N;set b:=1+Nat.log 2 n
 have hn:0< n:=by omega
 have hN_eq:N=v6 n:=vl t;have hN_gt1:1< v6 n:=bl n hn;have hN_le:v6 n<=2^(4*n):=cd t
 have hw_le_pow:v6 n<=2^w:=by rw [<- hN_eq];exact Nat.le_pow_clog (by omega) N
 have hw_le:w<=4*n:=by
   calc w=Nat.clog 2 (v6 n):=by dsimp only [w];rw [hN_eq]
     _<=Nat.clog 2 (2^(4*n)):=Nat.clog_mono_right 2 hN_le
     _=4*n:=Nat.clog_pow 2 (4*n) (by omega)
 have hb_pow:n+1<=2^b:=by
   have hlt:n< 2^(Nat.log 2 n+1):=Nat.lt_pow_succ_log_self (by omega) n
   have hbe:b=Nat.log 2 n+1:=by dsimp [b];omega
   rw [hbe];omega
 have hb_le:b<=n+1:=by
   have:Nat.log 2 n<=n:=Nat.log_le_self 2 n;dsimp [b];omega
 set Bc:=3+Nat.log 2 n
 have hBc_pos:0< Bc:=by dsimp [Bc];omega
 have h4n_lt:4*n< 2^Bc:=by
   have:2^Bc=4*2^b:=by
     have:Bc=2+b:=by dsimp [Bc,b];omega
     rw [this,pow_add];norm_num
   omega
 have hBc_le:Bc<=n+3:=by
   have:Nat.log 2 n<=n:=Nat.log_le_self 2 n;dsimp [Bc];omega
 have henc_hc:q0 (fun x:Fin (4*n)->Bool=>jm n Bc w hn hBc_pos (fun k=>x (wh n k))) ((n+2)^16) :=
   c4 n Bc w hn hBc_pos h4n_lt (by omega) (by omega)
 have hrep_hc16:q0 (x7 n Bc w hBc_pos) ((n+2)^16) :=
   (k7 n Bc w hn hBc_pos h4n_lt (by omega) (by omega)).mono
     (yz (by omega) (by omega))
 have hquery_hc:q0 (b5 n Bc w b hn hBc_pos) ((n+2)^16) :=
   be n Bc w b hn hBc_pos h4n_lt hb_pow (by omega) (by omega) (by omega)
 rcases henc_hc with ⟨enc,codeWire,henc_rb,henc_sz,henc_vg,henc_ev⟩
 rcases hrep_hc16 with ⟨rep,repOut,hrep_rb,hrep_sz,hrep_vg,hrep_ev⟩
 rcases hquery_hc with ⟨query,countWire0,hq_rb0,hq_sz,hq_vg,hq_ev⟩
 let countWire:Fin (2*n+1)->Fin (2+w+2*b+query.size):=fun i =>
   ⟨(countWire0 i).1,by have:=(countWire0 i).isLt;omega⟩
 have hq_rb:PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+w+2*b) query:=by
   rwa [show 2+w+2*b=2+(w+2*b) by omega]
 let pinWire:Bool->V->Fin (2+w+rep.size):=fun sel u =>
   if sel then repOut ⟨2*n+(xl n u).1,by omega⟩ else repOut ⟨(xl n u).1,by omega⟩
 refine ⟨enc,rep,query,codeWire,pinWire,countWire,
   ⟨henc_rb,henc_sz,henc_vg⟩,⟨hrep_rb,hrep_sz,hrep_vg⟩,⟨hq_rb,hq_sz,hq_vg⟩,?_⟩
 let rank:P->X->(Fin w->Bool):=fun p junk =>
   let z:=enc.wires ([false,true] ++
     (List.ofFn (fun i:I=>(p (false,i)).isSome)++List.ofFn (fun i:I=>(p (true,i)).isSome)) ++
     (List.ofFn (fun i:I=>(p (false,i)).getD (junk (false,i)))++List.ofFn (fun i:I=>(p (true,i)).getD (junk (true,i)))))
   fun i:Fin w=>z.getD (codeWire i).1 false
 let repr:(Fin w->Bool)->V->Option Bool:=fun z u =>
   let ws:=rep.wires ([false,true]++List.ofFn z)
   if ws.getD (pinWire false u).1 false then some (ws.getD (pinWire true u).1 false) else none
 let answer:(Fin w->Bool)->J × J->ℕ:=fun z d =>
   let ws:=query.wires ([false,true]++List.ofFn z ++
     List.ofFn (fun i:Fin b=>d.1.1.testBit i.1)++List.ofFn (fun i:Fin b=>d.2.1.testBit i.1))
   q2 (2*n+1) (fun i=>ws.getD (countWire i).1 false)
 have hrank_eq (p:P) (junk:X) :
     rank p junk=jm n Bc w hn hBc_pos (fun k:Fin (4*n) =>
       if h:k.1< 2*n then (p (z6 n ⟨k.1,h⟩)).isSome
       else (p (z6 n ⟨k.1-2*n,by omega⟩)).getD (junk (z6 n ⟨k.1-2*n,by omega⟩))):=by
   let xIn:Fin (4*n)->Bool:=fun k =>
     if h1:k.1< n then (p (false,⟨k.1,h1⟩)).isSome
     else if h2:k.1< 2*n then (p (true,⟨k.1-n,by omega⟩)).isSome
     else if h3:k.1< 3*n then (p (false,⟨k.1-2*n,by omega⟩)).getD (junk (false,⟨k.1-2*n,by omega⟩))
     else (p (true,⟨k.1-3*n,by omega⟩)).getD (junk (true,⟨k.1-3*n,by omega⟩))
   have hlist :
       [false,true] ++
         (List.ofFn (fun i:I=>(p (false,i)).isSome)++List.ofFn (fun i:I=>(p (true,i)).isSome)) ++
         (List.ofFn (fun i:I=>(p (false,i)).getD (junk (false,i)))++List.ofFn (fun i:I=>(p (true,i)).getD (junk (true,i)))) =
       [false,true]++List.ofFn xIn:=by
     rw [List.append_assoc];congr 1;apply List.ext_getElem
     . simp;omega
     . intro i hi1 hi2;simp only [List.length_append,List.length_ofFn] at hi1 hi2;rw [List.getElem_ofFn];dsimp only [xIn]
       by_cases h1:i< n
       . rw [List.getElem_append_left (by simp;omega),List.getElem_append_left (by simp;omega),List.getElem_ofFn,Zr h1]
       . by_cases h2:i< 2*n
         . rw [List.getElem_append_left (by simp;omega),List.getElem_append_right (by simp;omega)];simp only [List.length_ofFn,List.getElem_ofFn,Zb h1,Zr h2]
         . rw [List.getElem_append_right (by simp;omega)];simp only [List.length_append,List.length_ofFn]
           by_cases h3:i< 3*n
           . rw [List.getElem_append_left (by simp;omega),List.getElem_ofFn,Zb h1,Zb h2,Zr h3];have heq:(⟨i-(n+n),by omega⟩:I)=⟨i-2*n,by omega⟩:=Zx (by dsimp;omega);rw [heq]
           . rw [List.getElem_append_right (by simp;omega),List.getElem_ofFn,Zb h1,Zb h2,Zb h3];simp only [List.length_ofFn];have heq:(⟨i-(n+n)-n,by omega⟩:I)=⟨i-3*n,by omega⟩:=Zx (by dsimp;omega);rw [heq]
   funext i;dsimp only [rank];rw [hlist,henc_ev xIn i];dsimp only
   refine congrFun (congrArg (jm n Bc w hn hBc_pos) ?_) i
   funext k;dsimp only [xIn]
   by_cases hk:k.1< 2*n
   . rw [Zr hk];have hv_lt:(z6 n ⟨k.1,hk⟩).2.1< n:=(z6 n ⟨k.1,hk⟩).2.isLt
     by_cases h1:(z6 n ⟨k.1,hk⟩).1=true
     . have hr:(wh n k).1=n+(z6 n ⟨k.1,hk⟩).2.1:=by
         unfold wh;rw [Zr hk];dsimp only;rw [if_pos h1]
       rw [Zb (by rw [hr];omega),Zr (by rw [hr];omega)]
       have hveq:(true,(⟨(wh n k).1-n,by rw [hr];omega⟩:I))=z6 n ⟨k.1,hk⟩ :=
         Prod.ext h1.symm (Zx (by dsimp;rw [hr];omega))
       rw [hveq]
     . have hf:(z6 n ⟨k.1,hk⟩).1=false:=Bool.eq_false_iff.mpr h1
       have hr:(wh n k).1=(z6 n ⟨k.1,hk⟩).2.1:=by
         unfold wh;rw [Zr hk];dsimp only;rw [if_neg h1,Nat.zero_add]
       rw [Zr (by rw [hr];omega)]
       have hveq:(false,(⟨(wh n k).1,by rw [hr];omega⟩:I))=z6 n ⟨k.1,hk⟩ :=
         Prod.ext hf.symm (Zx (by dsimp;rw [hr]))
       rw [hveq]
   . rw [Zb hk];have hv_lt:(z6 n ⟨k.1-2*n,by omega⟩).2.1< n:=(z6 n ⟨k.1-2*n,by omega⟩).2.isLt
     by_cases h1:(z6 n ⟨k.1-2*n,by omega⟩).1=true
     . have hr:(wh n k).1=3*n+(z6 n ⟨k.1-2*n,by omega⟩).2.1:=by
         unfold wh;rw [Zb hk];dsimp only;rw [if_pos h1];omega
       rw [Zb (by rw [hr];omega),Zb (by rw [hr];omega),Zb (by rw [hr];omega)]
       have hveq:(true,(⟨(wh n k).1-3*n,by rw [hr];omega⟩:I))=z6 n ⟨k.1-2*n,by omega⟩ :=
         Prod.ext h1.symm (Zx (by dsimp;rw [hr];omega))
       rw [hveq]
     . have hf:(z6 n ⟨k.1-2*n,by omega⟩).1=false:=Bool.eq_false_iff.mpr h1
       have hr:(wh n k).1=2*n+(z6 n ⟨k.1-2*n,by omega⟩).2.1:=by
         unfold wh;rw [Zb hk];dsimp only;rw [if_neg h1];omega
       rw [Zb (by rw [hr];omega),Zb (by rw [hr];omega),Zr (by rw [hr];omega)]
       have hveq:(false,(⟨(wh n k).1-2*n,by rw [hr];omega⟩:I))=z6 n ⟨k.1-2*n,by omega⟩ :=
         Prod.ext hf.symm (Zx (by dsimp;rw [hr];omega))
       rw [hveq]
 have hval_rank (p:P) (junk:X) :
     q2 w (rank p junk)=x5 n (zp n hn (fun k=>p (z6 n k))):=by
   rw [hrank_eq];exact c5 n Bc w hn hBc_pos h4n_lt hw_le_pow (fun k=>p (z6 n k)) (fun k=>junk (z6 n k))
 have hrepr_cyc (z:Fin w->Bool) (hz:q2 w z< v6 n) :
     let pCyc:=wg n hn (zy n (q2 w z))
     (∀ k:Fin (2*n),x7 n Bc w hBc_pos z ⟨k.1,by omega⟩=(pCyc k).isSome /\
       (x7 n Bc w hBc_pos z ⟨k.1,by omega⟩=true->pCyc k=some (x7 n Bc w hBc_pos z ⟨2*n+k.1,by omega⟩))) /\
     (∀ u:V,repr z u=pCyc (xl n u)):=by
   intro pCyc;have hcore:=c6 n Bc w hn hBc_pos h4n_lt hw_le_pow z hz
   refine ⟨hcore,fun u=>?_⟩
   dsimp only [repr,pinWire];simp only [Ze,Zj,Zh];rw [hrep_ev z _,hrep_ev z _]
   rcases hcore (xl n u) with ⟨h1,h2⟩
   cases his:x7 n Bc w hBc_pos z ⟨(xl n u).1,by omega⟩
   . simp only [Ze,Zj];rw [his] at h1;change false=(pCyc (xl n u)).isSome at h1
     cases hp:pCyc (xl n u)
     . rfl
     . simp [hp] at h1
   . simp only [Zh];exact (h2 his).symm
 have hhist_iff (p q:P) :
     hist p=hist q ↔ zp n hn (fun k=>p (z6 n k))=zp n hn (fun k=>q (z6 n k)):=by
   rw [<- yv n hn];constructor
   . intro h d1 hd1 d2 hd2;have h1:=wu t p (⟨d1,by omega⟩,⟨d2,by omega⟩);have h2:=wu t q (⟨d1,by omega⟩,⟨d2,by omega⟩);have hthis:=congrFun h (⟨d1,by omega⟩,⟨d2,by omega⟩);dsimp only [hist,V,I,J,X,P,n] at hthis;dsimp only at h1 h2;rw [<- h1,<-h2];exact hthis
   . intro h;funext d;dsimp only [hist];rw [wu,wu];exact h d.1.1 (by omega) d.2.1 (by omega)
 have hanswer_eq (z:Fin w->Bool) (hz:q2 w z< v6 n) (d:J × J) :
     answer z d=hist (repr z) d:=by
   let qIn:Fin (w+2*b)->Bool:=fun k =>
     if h1:k.1< w then z ⟨k.1,h1⟩
     else if h2:k.1< w+b then d.1.1.testBit (k.1-w)
     else d.2.1.testBit (k.1-(w+b))
   have hlist :
       [false,true]++List.ofFn z ++
         List.ofFn (fun i:Fin b=>d.1.1.testBit i.1) ++
         List.ofFn (fun i:Fin b=>d.2.1.testBit i.1) =
       [false,true]++List.ofFn qIn:=by
     rw [List.append_assoc,List.append_assoc];congr 1;apply List.ext_getElem
     . simp;omega
     . intro i hi1 hi2;simp only [List.length_append,List.length_ofFn] at hi1 hi2;rw [List.getElem_ofFn];dsimp only [qIn]
       by_cases h1:i< w
       . rw [List.getElem_append_left (by simp;omega),List.getElem_ofFn,Zr h1]
       . rw [List.getElem_append_right (by simp;omega)];simp only [List.length_ofFn]
         by_cases h2:i< w+b
         . rw [List.getElem_append_left (by simp;omega),List.getElem_ofFn,Zb h1,Zr h2]
         . rw [List.getElem_append_right (by simp;omega),List.getElem_ofFn,Zb h1,Zb h2];simp only [List.length_ofFn];congr 1;omega
   have hans:answer z d=q2 (2*n+1) (b5 n Bc w b hn hBc_pos qIn):=by
     dsimp only [answer,countWire];congr 1;funext i;rw [hlist,hq_ev qIn i]
   rw [hans];set pCyc:=wg n hn (zy n (q2 w z))
   rcases hrepr_cyc z hz with ⟨hcore,hru⟩
   let jFake:Fin (2*n)->Bool:=fun k=>x7 n Bc w hBc_pos z ⟨2*n+k.1,by omega⟩
   have hq_in:q1 (x7 n Bc w hBc_pos (fun j:Fin w=>qIn ⟨j.1,by omega⟩)) (fun j:Fin (2*b)=>qIn ⟨w+j.1,by omega⟩) =
       fun k:Fin (4*n+2*b) =>
         if h1:k.1< 2*n then (pCyc ⟨k.1,h1⟩).isSome
         else if h2:k.1< 4*n then (pCyc ⟨k.1-2*n,by omega⟩).getD (jFake ⟨k.1-2*n,by omega⟩)
         else if h3:k.1< 4*n+b then d.1.1.testBit (k.1-4*n)
         else d.2.1.testBit (k.1-(4*n+b)):=by
     have hz_q:(fun j:Fin w=>qIn ⟨j.1,by omega⟩)=z:=by
       funext j;dsimp only [qIn];rw [Zr j.isLt]
     rw [hz_q];funext k
     by_cases h1:k.1< 2*n
     . dsimp only [q1];rw [Zr (by omega),Zr h1];exact (hcore ⟨k.1,h1⟩).1
     . by_cases h2:k.1< 4*n
       . dsimp only [q1];rw [Zr h2,Zb h1,Zr h2]
         rcases hcore ⟨k.1-2*n,by omega⟩ with ⟨hs,hv⟩
         cases hp:pCyc ⟨k.1-2*n,by omega⟩ with
         | none =>
           dsimp only [jFake,Option.getD_none];congr 1;exact Zx (by dsimp;omega)
         | some v =>
           have his:x7 n Bc w hBc_pos z ⟨k.1-2*n,by omega⟩=true:=by
             rw [hs];change (pCyc ⟨k.1-2*n,by omega⟩).isSome=true;rw [hp];rfl
           have hval:=hv his;change pCyc ⟨k.1-2*n,by omega⟩=some _ at hval;rw [hp] at hval;cases hval;dsimp only [Option.getD_some];congr 1;exact Zx (by dsimp;omega)
       . dsimp only [q1];rw [Zb h2,Zb h1,Zb h2];dsimp only [qIn]
         by_cases h3:k.1< 4*n+b
         . rw [Zr h3,Zb (by omega),Zr (by omega)];congr 1;omega
         . rw [Zb h3,Zb (by omega),Zb (by omega)];congr 1;omega
   have hq_spec:=km n hn b hb_pow pCyc jFake d.1 d.2;dsimp only [b5];rw [hq_in,hq_spec,y7];dsimp only [hist];rw [wu]
   have hp_eq:pCyc=fun k=>repr z (z6 n k):=by funext k;rw [hru,v8]
   rw [hp_eq]
 change (∀ (p:P) (junk:X),q2 w (rank p junk)< N/\hist (repr (rank p junk))=hist p /\
     ∀ d,answer (rank p junk) d=hist p d) /\
   (∀ (p q:P) (a b':X),rank p a=rank q b' ↔ hist p=hist q) /\
   ∀ z:Fin w->Bool,q2 w z< N->∀ junk:X,rank (repr z) junk=z
 refine ⟨?_,?_,?_⟩
 . intro p junk;have hv:=hval_rank p junk;have hspec:=x2 n (zp n hn (fun k=>p (z6 n k))) (x1 n hn _)
   have hltN:q2 w (rank p junk)< N:=by rw [hv,hN_eq];exact hspec.1
   have hlt_dp:q2 w (rank p junk)< v6 n:=by rwa [<- hN_eq]
   have hrepr_eq:hist (repr (rank p junk))=hist p:=by
     rw [hhist_iff]
     have hconv:(fun k=>repr (rank p junk) (z6 n k))=wg n hn (zy n (q2 w (rank p junk))):=by
       funext k;rw [(hrepr_cyc (rank p junk) hlt_dp).2,v8]
     rw [hconv,hv,hspec.2,yc n hn _ (x1 n hn _)]
   refine ⟨hltN,hrepr_eq,fun d=>?_⟩
   rw [hanswer_eq (rank p junk) hlt_dp d,hrepr_eq]
 . intro p q a b';rw [hhist_iff];constructor
   . intro heq;have h1:=hval_rank p a;have h2:=hval_rank q b';rw [heq] at h1
     have hrc:x5 n (zp n hn (fun k=>p (z6 n k))) =
         x5 n (zp n hn (fun k=>q (z6 n k))):=h1.symm.trans h2
     have hs1:=(x2 n (zp n hn (fun k=>p (z6 n k))) (x1 n hn _)).2;have hs2:=(x2 n (zp n hn (fun k=>q (z6 n k))) (x1 n hn _)).2;rw [<- hs1,hrc,hs2]
   . intro hcan;have h1:=hval_rank p a;have h2:=hval_rank q b';rw [hcan] at h1;have hv:q2 w (rank p a)=q2 w (rank q b'):=h1.trans h2.symm;rw [<- qm w (rank p a),hv,qm w (rank q b')]
 . intro z hz junk
   have hz_dp:q2 w z< v6 n:=by change q2 w z< N at hz;rwa [<- hN_eq]
   have hv:=hval_rank (repr z) junk
   have hconv:(fun k=>repr z (z6 n k))=wg n hn (zy n (q2 w z)):=by
     funext k;rw [(hrepr_cyc z hz_dp).2,v8]
   rw [hconv,yc n hn _ (xq n (q2 w z) hz_dp).1,
       (xq n (q2 w z) hz_dp).2] at hv
   rw [<- qm w (rank (repr z) junk),hv,qm w z]
