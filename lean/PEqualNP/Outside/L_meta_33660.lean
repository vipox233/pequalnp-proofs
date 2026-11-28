import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33660
abbrev dF:=List.finRange
lemma dG {p:Prop} [Decidable p]:(decide p=true)↔p:=by simp
lemma dH {a b:Bool}:((a||b)=true)↔(a=true∨b=true):=by simp
lemma dI {a b:Bool}:((a&&b)=true)↔(a=true∧b=true):=by simp
lemma dJ {α:Type*} {l:List α} {i:ℕ} (h:i < l.length):l.take (i+1)=l.take i++[l[i]]:=List.take_succ_eq_append_getElem h
lemma dK {α:Type*} {s:Finset α} {p:α→Prop} [DecidablePred p] {a:α}:a∈s.filter p↔a∈s∧p a:=Finset.mem_filter
lemma dL {α:Type*} [Fintype α] (x:α):x∈(Finset.univ:Finset α):=Finset.mem_univ x
lemma dM {a b:Bool}:a=b↔(a=true↔b=true):=Bool.eq_iff_iff
section CircuitDSL
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
lemma yE (gs:List Gate) (w:List Bool) :
  (gs.foldl (fun acc g=>acc ++ [g.op.eval (g.inputs.map fun i=>acc.getD i false)]) w).length =
   w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
  simp only [List.foldl_cons,List.length_cons]
  rw [ih,List.length_append,List.length_singleton]
  omega
lemma yD (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length) :
  (gs.foldl (fun acc g=>acc ++ [g.op.eval (g.inputs.map fun j=>acc.getD j false)]) w).getD i false =
   w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  have hi':i < (w ++ [g.op.eval (g.inputs.map fun j=>w.getD j false)]).length:=by
   rw [List.length_append,List.length_singleton];omega
  rw [ih _ hi']
  simp only [List.getD,List.getElem?_append_left hi]
structure CB (nIn:ℕ) where
 gates:List Gate
 fanIn:∀ g∈gates,
  g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length ≤ 2
 reads:∀ j < gates.length,∀ i∈(gates.getD j ⟨GateOp.or,[]⟩).inputs,i < nIn+j
def CB.zO (nIn:ℕ):CB nIn:=
 ⟨[],fun _ h=>absurd h (by simp),fun _ h=>absurd h (by simp)⟩
def CB.val {nIn:ℕ} (c:CB nIn) (x:List Bool) (w:ℕ):Bool:=
 (Circuit.wires ⟨c.gates,0⟩ x).getD w false
def CB.Qa {nIn:ℕ} (c₁ c₂:CB nIn):Prop:=
 ∃ extra:List Gate,c₂.gates=c₁.gates ++ extra
lemma CB.zi {nIn:ℕ} (c:CB nIn):c.Qa c:=
 ⟨[],by simp⟩
lemma CB.q0 {nIn:ℕ} {c₁ c₂ c₃:CB nIn}
  (h12:c₁.Qa c₂) (h23:c₂.Qa c₃):c₁.Qa c₃:=by
 obtain ⟨e1,he1⟩:=h12
 obtain ⟨e2,he2⟩:=h23
 exact ⟨e1 ++ e2,by rw [he2,he1,List.append_assoc]⟩
lemma CB.ys {nIn:ℕ} {c₁ c₂:CB nIn} (h:c₁.Qa c₂) :
  c₁.gates.length ≤ c₂.gates.length:=by
 obtain ⟨e,he⟩:=h
 rw [he,List.length_append]
 omega
lemma CB.zr {nIn:ℕ} {c₁ c₂:CB nIn} (h:c₁.Qa c₂)
  {x:List Bool} (hx:x.length=nIn) {w:ℕ} (hw:w < nIn+c₁.gates.length) :
  c₂.val x w=c₁.val x w:=by
 obtain ⟨extra,he⟩:=h
 unfold CB.val Circuit.wires
 rw [he,List.foldl_append]
 have hlen:(c₁.gates.foldl
   (fun acc g=>acc ++ [g.op.eval (g.inputs.map fun i=>acc.getD i false)]) x).length =
   nIn+c₁.gates.length:=by
  rw [yE,hx]
 exact yD extra _ w (by omega)
def CB.push {nIn:ℕ} (c:CB nIn) (g:Gate)
  (hfan:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length ≤ 2)
  (hreads:∀ i∈g.inputs,i < nIn+c.gates.length):CB nIn:=
 {gates:=c.gates ++ [g]
  fanIn:=by
   intro g' hg'
   rw [List.mem_append,List.mem_singleton] at hg'
   rcases hg' with h1 | rfl
   ·exact c.fanIn g' h1
   ·exact hfan
  reads:=by
   intro j hj i hi
   rw [List.length_append,List.length_singleton] at hj
   by_cases hlt:j < c.gates.length
   ·have hgd:(c.gates ++ [g]).getD j ⟨GateOp.or,[]⟩=c.gates.getD j ⟨GateOp.or,[]⟩:=by
     simp only [List.getD,List.getElem?_append_left hlt]
    rw [hgd] at hi
    exact c.reads j hlt i hi
   ·have heq:j=c.gates.length:=by omega
    subst heq
    have hgd:(c.gates ++ [g]).getD c.gates.length ⟨GateOp.or,[]⟩=g:=by
     simp [List.getD]
    rw [hgd] at hi
    exact hreads i hi }
lemma CB.yz {nIn:ℕ} (c:CB nIn) (g:Gate) (hf) (hr) :
  c.Qa (c.push g hf hr):=⟨[g],rfl⟩
lemma CB.jl {nIn:ℕ} (c:CB nIn) (g:Gate) (hf) (hr) :
  (c.push g hf hr).gates.length=c.gates.length+1:=by
 simp [CB.push]
lemma CB.g1 {nIn:ℕ} (c:CB nIn) (g:Gate) (hf) (hr)
  {x:List Bool} (hx:x.length=nIn) :
  (c.push g hf hr).val x (nIn+c.gates.length)=g.op.eval (g.inputs.map (c.val x)):=by
 unfold CB.val Circuit.wires CB.push
 dsimp only
 rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
 set ws:=c.gates.foldl
  (fun acc g=>acc ++ [g.op.eval (g.inputs.map fun i=>acc.getD i false)]) x
 have hlen:ws.length=nIn+c.gates.length:=by rw [yE,hx]
 rw [← hlen]
 simp [List.getD]
structure Q4 (nIn:ℕ) (c:CB nIn) (f:(Fin nIn->Bool)->Bool) where
 w:ℕ
 hw:w < nIn+c.gates.length
 heval:∀ x:Fin nIn->Bool,c.val (List.ofFn x) w=f x
def Q4.lift {nIn:ℕ} {c c':CB nIn} {f:(Fin nIn->Bool)->Bool}
  (hext:c.Qa c') (v:Q4 nIn c f):Q4 nIn c' f:=
 {w:=v.w
  hw:=Nat.lt_of_lt_of_le v.hw (Nat.add_le_add_left (CB.ys hext) nIn)
  heval:=fun x=>by
   rw [CB.zr hext (List.length_ofFn) v.hw,v.heval x] }
def Q4.cast {nIn:ℕ} {c:CB nIn} {f g:(Fin nIn->Bool)->Bool}
  (h:∀ x,f x=g x) (v:Q4 nIn c f):Q4 nIn c g:=
 {w:=v.w,hw:=v.hw,heval:=fun x=>(v.heval x).trans (h x) }
def Q4.input {nIn:ℕ} (c:CB nIn) (i:Fin nIn) :
  Q4 nIn c (fun x=>x i):=
 {w:=i.val
  hw:=by omega
  heval:=fun x=>by
   unfold CB.val Circuit.wires
   have hi:i.val < (List.ofFn x).length:=by simp
   rw [yD c.gates (List.ofFn x) i.val hi]
   simp [List.getD] }
structure Q2 (nIn:ℕ) (c:CB nIn) (m:ℕ) (f:(Fin nIn->Bool)->Fin m->Bool) where
 ws:Fin m->ℕ
 hws:∀ i,ws i < nIn+c.gates.length
 heval:∀ x i,c.val (List.ofFn x) (ws i)=f x i
def Q2.lift {nIn:ℕ} {c c':CB nIn} {m:ℕ} {f:(Fin nIn->Bool)->Fin m->Bool}
  (hext:c.Qa c') (v:Q2 nIn c m f):Q2 nIn c' m f:=
 {ws:=v.ws
  hws:=fun i=>Nat.lt_of_lt_of_le (v.hws i) (Nat.add_le_add_left (CB.ys hext) nIn)
  heval:=fun x i=>by
   rw [CB.zr hext (List.length_ofFn) (v.hws i),v.heval x i] }
def Q2.at {nIn:ℕ} {c:CB nIn} {m:ℕ} {f:(Fin nIn->Bool)->Fin m->Bool}
  (v:Q2 nIn c m f) (i:Fin m):Q4 nIn c (fun x=>f x i):=
 ⟨v.ws i,v.hws i,fun x=>v.heval x i⟩
def Q2.cast {nIn:ℕ} {c:CB nIn} {m:ℕ} {f g:(Fin nIn->Bool)->Fin m->Bool}
  (h:∀ x i,f x i=g x i) (v:Q2 nIn c m f):Q2 nIn c m g:=
 ⟨v.ws,v.hws,fun x i=>(v.heval x i).trans (h x i)⟩
structure Q9 (nIn:ℕ) (c:CB nIn) (W:ℕ) (f:(Fin nIn->Bool)->ℕ) where
 vec:Q2 nIn c W (fun x i=>(f x).testBit i.val)
 hlt:∀ x,f x < 2^W
def Q9.lift {nIn:ℕ} {c c':CB nIn} {W:ℕ} {f:(Fin nIn->Bool)->ℕ}
  (hext:c.Qa c') (v:Q9 nIn c W f):Q9 nIn c' W f:=
 ⟨v.vec.lift hext,v.hlt⟩
def Q9.cast {nIn:ℕ} {c:CB nIn} {W:ℕ} {f g:(Fin nIn->Bool)->ℕ}
  (h:∀ x,f x=g x) (v:Q9 nIn c W f):Q9 nIn c W g:=
 ⟨v.vec.cast (fun x i=>by rw [h x]),fun x=>by rw [← h x];exact v.hlt x⟩
structure Q0 (nIn:ℕ) (c:CB nIn) (B:ℕ) (F:CB nIn->Type) where
 c':CB nIn
 ext:c.Qa c'
 hsize:c'.gates.length ≤ c.gates.length+B
 val:F c'
def Q0.pure {nIn:ℕ} {c:CB nIn} {F:CB nIn->Type} (v:F c) :
  Q0 nIn c 0 F:=
 ⟨c,CB.zi c,by simp,v⟩
def Q0.weaken {nIn:ℕ} {c:CB nIn} {B B':ℕ} {F:CB nIn->Type}
  (h:B ≤ B') (r:Q0 nIn c B F):Q0 nIn c B' F:=
 ⟨r.c',r.ext,r.hsize.trans (Nat.add_le_add_left h _),r.val⟩
def Q0.bind {nIn:ℕ} {c:CB nIn} {B₁ B₂:ℕ} {F₁ F₂:CB nIn->Type}
  (r:Q0 nIn c B₁ F₁)
  (k:∀ c₁,c.Qa c₁->F₁ c₁->Q0 nIn c₁ B₂ F₂) :
  Q0 nIn c (B₁+B₂) F₂:=
 let r2:=k r.c' r.ext r.val
 ⟨r2.c',CB.q0 r.ext r2.ext,
  r2.hsize.trans (by have:=r.hsize;omega),r2.val⟩
def Q0.qe {nIn:ℕ} {Bstep:ℕ} (N:ℕ)
  (Acc:(k:ℕ)->k ≤ N->CB nIn->Type)
  (c:CB nIn) (init:Acc 0 (Nat.zero_le N) c)
  (step:∀ (i:ℕ) (hi:i < N) (c₁:CB nIn),c.Qa c₁ ->
   Acc i (Nat.le_of_lt hi) c₁->Q0 nIn c₁ Bstep (Acc (i+1) hi)) :
  Q0 nIn c (N*Bstep) (Acc N le_rfl):=by
 let rec go:∀ (k:ℕ) (hk:k ≤ N),Q0 nIn c (k*Bstep) (Acc k hk)
  | 0,hk=>⟨c,CB.zi c,by simp,init⟩
  | k+1,hk=>
   let prev:=go k (Nat.le_of_succ_le hk)
   let nxt:=step k hk prev.c' prev.ext prev.val
   ⟨nxt.c',CB.q0 prev.ext nxt.ext,
    nxt.hsize.trans (by
     have hp:=prev.hsize
     rw [Nat.succ_mul]
     omega),
    nxt.val⟩
 exact go N le_rfl
def vJ {nIn:ℕ} (c:CB nIn) (b:Bool) :
  Q0 nIn c 1 (fun c'=>Q4 nIn c' (fun _=>b)):=
 let g:Gate:=if b then ⟨GateOp.and,[]⟩ else ⟨GateOp.or,[]⟩
 have hf:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length ≤ 2:=by
  cases b <;> simp [g]
 have hr:∀ i∈g.inputs,i < nIn+c.gates.length:=by
  cases b <;> simp [g]
 let c':=c.push g hf hr
 ⟨c',CB.yz c g hf hr,by rw [CB.jl],
  ⟨nIn+c.gates.length,by rw [CB.jl];omega,fun x=>by
   rw [CB.g1 c g hf hr List.length_ofFn]
   cases b <;> rfl⟩⟩
def y2 {nIn:ℕ} (c:CB nIn) {f:(Fin nIn->Bool)->Bool} (a:Q4 nIn c f) :
  Q0 nIn c 1 (fun c'=>Q4 nIn c' (fun x=>!(f x))):=
 let g:Gate:=⟨GateOp.not,[a.w]⟩
 have hf:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length ≤ 2:=by
  simp [g]
 have hr:∀ i∈g.inputs,i < nIn+c.gates.length:=by
  intro i hi;simp [g] at hi;rw [hi];exact a.hw
 let c':=c.push g hf hr
 ⟨c',CB.yz c g hf hr,by rw [CB.jl],
  ⟨nIn+c.gates.length,by rw [CB.jl];omega,fun x=>by
   rw [CB.g1 c g hf hr List.length_ofFn]
   simp [g,GateOp.eval,a.heval x]⟩⟩
def vg {nIn:ℕ} (c:CB nIn) {f g:(Fin nIn->Bool)->Bool}
  (a:Q4 nIn c f) (b:Q4 nIn c g) :
  Q0 nIn c 1 (fun c'=>Q4 nIn c' (fun x=>f x&&g x)):=
 let gt:Gate:=⟨GateOp.and,[a.w,b.w]⟩
 have hf:gt.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\gt.inputs.length ≤ 2:=by
  simp [gt]
 have hr:∀ i∈gt.inputs,i < nIn+c.gates.length:=by
  intro i hi;simp [gt] at hi;rcases hi with rfl | rfl;exact a.hw;exact b.hw
 let c':=c.push gt hf hr
 ⟨c',CB.yz c gt hf hr,by rw [CB.jl],
  ⟨nIn+c.gates.length,by rw [CB.jl];omega,fun x=>by
   rw [CB.g1 c gt hf hr List.length_ofFn]
   simp [gt,GateOp.eval,a.heval x,b.heval x]⟩⟩
def yr {nIn:ℕ} (c:CB nIn) {f g:(Fin nIn->Bool)->Bool}
  (a:Q4 nIn c f) (b:Q4 nIn c g) :
  Q0 nIn c 1 (fun c'=>Q4 nIn c' (fun x=>f x||g x)):=
 let gt:Gate:=⟨GateOp.or,[a.w,b.w]⟩
 have hf:gt.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\gt.inputs.length ≤ 2:=by
  simp [gt]
 have hr:∀ i∈gt.inputs,i < nIn+c.gates.length:=by
  intro i hi;simp [gt] at hi;rcases hi with rfl | rfl;exact a.hw;exact b.hw
 let c':=c.push gt hf hr
 ⟨c',CB.yz c gt hf hr,by rw [CB.jl],
  ⟨nIn+c.gates.length,by rw [CB.jl];omega,fun x=>by
   rw [CB.g1 c gt hf hr List.length_ofFn]
   simp [gt,GateOp.eval,a.heval x,b.heval x]⟩⟩
def g2 {nIn:ℕ} (c:CB nIn) {f g:(Fin nIn->Bool)->Bool}
  (a:Q4 nIn c f) (b:Q4 nIn c g) :
  Q0 nIn c 4 (fun c'=>Q4 nIn c' (fun x=>xor (f x) (g x))):=
 Q0.weaken (by omega)<|
 (yr c a b).bind fun c1 h1 vor=>
 (vg c1 (a.lift h1) (b.lift h1)).bind fun c2 h2 vand=>
 (y2 c2 vand).bind fun c3 h3 vnand=>
 (vg c3 (vor.lift (CB.q0 h2 h3)) vnand).bind fun c4 _ vres=>
 Q0.pure (vres.cast fun x=>by cases f x <;> cases g x <;> rfl)
def dj {nIn:ℕ} (c:CB nIn) {f g:(Fin nIn->Bool)->Bool}
  (a:Q4 nIn c f) (b:Q4 nIn c g) :
  Q0 nIn c 5 (fun c'=>Q4 nIn c' (fun x=>decide (f x=g x))):=
 Q0.weaken (by omega)<|
 (g2 c a b).bind fun c1 _ vx=>
 (y2 c1 vx).bind fun c2 _ vres=>
 Q0.pure (vres.cast fun x=>by cases f x <;> cases g x <;> rfl)
def ds {nIn:ℕ} (c:CB nIn) {fc ft fe:(Fin nIn->Bool)->Bool}
  (cond:Q4 nIn c fc) (t:Q4 nIn c ft) (e:Q4 nIn c fe) :
  Q0 nIn c 4 (fun c'=>Q4 nIn c' (fun x=>if fc x=true then ft x else fe x)):=
 Q0.weaken (by omega)<|
 (y2 c cond).bind fun c1 h1 vnc=>
 (vg c1 (cond.lift h1) (t.lift h1)).bind fun c2 h2 vt=>
 (vg c2 (vnc.lift h2) (e.lift (CB.q0 h1 h2))).bind fun c3 h3 ve=>
 (yr c3 (vt.lift h3) ve).bind fun c4 _ vres=>
 Q0.pure (vres.cast fun x=>by cases fc x <;> cases ft x <;> cases fe x <;> rfl)
def j8 {nIn:ℕ} {Bstep:ℕ} (m:ℕ) (f:(Fin nIn->Bool)->Fin m->Bool)
  (c:CB nIn)
  (build:∀ (i:Fin m) (c1:CB nIn),c.Qa c1 ->
   Q0 nIn c1 Bstep (fun c'=>Q4 nIn c' (fun x=>f x i))) :
  Q0 nIn c (m*Bstep) (fun c'=>Q2 nIn c' m f):=by
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=
  ∀ (i:Fin m),i.val < k->Q4 nIn c1 (fun x=>f x i)
 have hfold:=Q0.qe m Acc c (fun _ hi=>absurd hi (by omega))
  (fun k hk c1 h1 acc=>
   (build ⟨k,hk⟩ c1 h1).bind fun c2 h2 vk=>
   Q0.pure fun i hi=>
    if hlt:i.val < k then (acc i hlt).lift h2
    else
     have heq:i=⟨k,hk⟩:=Fin.ext (by dsimp;omega)
     heq▸vk)
 refine ⟨hfold.c',hfold.ext,by simpa using hfold.hsize,?_⟩
 exact ⟨fun i=>(hfold.val i i.isLt).w,fun i=>(hfold.val i i.isLt).hw,
  fun x i=>(hfold.val i i.isLt).heval x⟩
def vq {nIn:ℕ} (c:CB nIn) (m:ℕ) (v:Fin m->Bool) :
  Q0 nIn c (m*1) (fun c'=>Q2 nIn c' m (fun _ i=>v i)):=
 j8 m (fun _ i=>v i) c (fun i c1 _=>vJ c1 (v i))
def qS {nIn:ℕ} (c:CB nIn) (W:ℕ) (n:ℕ) (hn:n < 2^W) :
  Q0 nIn c (W*1) (fun c'=>Q9 nIn c' W (fun _=>n)):=
 Q0.weaken (by omega)<|
 (vq c W (fun i=>n.testBit i.val)).bind fun _ _ v=>
  Q0.pure (Q9.mk v (fun _=>hn))
def vd {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {fc:(Fin nIn->Bool)->Bool} {ft fe:(Fin nIn->Bool)->Fin m->Bool}
  (cond:Q4 nIn c fc) (t:Q2 nIn c m ft) (e:Q2 nIn c m fe) :
  Q0 nIn c (m*4) (fun c'=>Q2 nIn c' m (fun x i=>if fc x=true then ft x i else fe x i)):=
 j8 m (fun x i=>if fc x=true then ft x i else fe x i) c fun i c1 h1=>
  ds c1 (cond.lift h1) ((t.at i).lift h1) ((e.at i).lift h1)
def vH {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fc:(Fin nIn->Bool)->Bool} {ft fe:(Fin nIn->Bool)->ℕ}
  (cond:Q4 nIn c fc) (t:Q9 nIn c W ft) (e:Q9 nIn c W fe) :
  Q0 nIn c (W*4) (fun c'=>Q9 nIn c' W (fun x=>if fc x=true then ft x else fe x)):=
 Q0.weaken (by omega)<|
 (vd c cond t.vec e.vec).bind fun _ _ v=>
  Q0.pure (Q9.mk
   (v.cast (fun x i=>by split_ifs <;> rfl))
   (fun x=>by split_ifs;exact t.hlt x;exact e.hlt x))
def j3 {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {f g:(Fin nIn->Bool)->Fin m->Bool}
  (a:Q2 nIn c m f) (b:Q2 nIn c m g) :
  Q0 nIn c (m*4) (fun c'=>Q2 nIn c' m (fun x i=>xor (f x i) (g x i))):=
 j8 m (fun x i=>xor (f x i) (g x i)) c fun i c1 h1=>
  g2 c1 ((a.at i).lift h1) ((b.at i).lift h1)
def gF {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {f g:(Fin nIn->Bool)->Fin m->Bool}
  (a:Q2 nIn c m f) (b:Q2 nIn c m g) :
  Q0 nIn c (1+m*6) (fun c'=>Q4 nIn c' (fun x=>decide (f x=g x))):=
 Q0.weaken (by omega)<|
 (vJ c true).bind fun c0 h0 vtrue=>
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=
  Q4 nIn c1 (fun x=>decide (∀ i:Fin m,i.val < k->f x i=g x i))
 have hinit:Acc 0 (Nat.zero_le m) c0:=
  vtrue.cast fun _=>by simp
 (Q0.qe (Bstep:=6) m Acc c0 hinit fun k hk c1 h1 acc=>
  Q0.weaken (by omega)<|
  (dj c1 ((a.at ⟨k,hk⟩).lift (CB.q0 h0 h1))
   ((b.at ⟨k,hk⟩).lift (CB.q0 h0 h1))).bind fun c2 h2 veq=>
  (vg c2 (acc.lift h2) veq).bind fun c3 _ vand=>
  Q0.pure<|vand.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dI,dG]
   constructor
   ·rintro ⟨hprev,hcur⟩ i hi
    by_cases hlt:i.val < k
    ·exact hprev i hlt
    ·have heq:i=⟨k,hk⟩:=Fin.ext (by dsimp;omega)
     rw [heq];exact hcur
   ·intro hall
    exact ⟨fun i hi=>hall i (by omega),hall ⟨k,hk⟩ (by dsimp;omega)⟩).bind fun cF _ vres=>
 Q0.pure<|vres.cast fun x=>by
  apply Bool.eq_iff_iff.mpr
  simp only [dG]
  exact ⟨fun h=>funext fun i=>h i i.isLt,fun h i _=>congrFun h i⟩
def zg {nIn:ℕ} (c:CB nIn) {m:ℕ} {f:(Fin nIn->Bool)->Fin m->Bool}
  (a:Q2 nIn c m f) :
  Q0 nIn c (1+m*1) (fun c'=>Q4 nIn c' (fun x=>decide (∃ i:Fin m,f x i=true))):=
 Q0.weaken (by omega)<|
 (vJ c false).bind fun c0 h0 vfalse=>
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=
  Q4 nIn c1 (fun x=>decide (∃ i:Fin m,i.val < k/\f x i=true))
 have hinit:Acc 0 (Nat.zero_le m) c0:=
  vfalse.cast fun _=>by simp
 (Q0.qe (Bstep:=1) m Acc c0 hinit fun k hk c1 h1 acc=>
  (yr c1 acc ((a.at ⟨k,hk⟩).lift (CB.q0 h0 h1))).bind fun c2 _ vor=>
  Q0.pure<|vor.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dH,dG]
   constructor
   ·rintro (⟨i,hi,hf⟩ | hcur)
    ·exact ⟨i,by omega,hf⟩
    ·exact ⟨⟨k,hk⟩,by dsimp;omega,hcur⟩
   ·rintro ⟨i,hi,hf⟩
    by_cases hlt:i.val < k
    ·left;exact ⟨i,hlt,hf⟩
    ·right
     have heq:i=⟨k,hk⟩:=Fin.ext (by dsimp;omega)
     rwa [← heq]).bind fun cF _ vres=>
 Q0.pure<|vres.cast fun x=>by
  apply Bool.eq_iff_iff.mpr
  simp only [dG]
  exact ⟨fun ⟨i,_,hf⟩=>⟨i,hf⟩,fun ⟨i,hf⟩=>⟨i,i.isLt,hf⟩⟩
lemma jN (a k:ℕ) :
  a % 2^(k+1)=a % 2^k+2^k*(a.testBit k).toNat:=by
 have hP:0 < 2^k:=Nat.two_pow_pos k
 have h2:(a / 2^k) % 2=(a.testBit k).toNat:=by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt:(a / 2^k) % 2 < 2:=Nat.mod_lt _ (by omega)
  by_cases h:(a / 2^k) % 2=1 <;> simp [h] <;> omega
 have hpow:2^(k+1)=2^k*2:=pow_succ 2 k
 have hdm1:a=2^k*(a / 2^k)+a % 2^k:=(Nat.div_add_mod a (2^k)).symm
 have hdm2:a / 2^k=2*(a / 2^k / 2)+(a / 2^k) % 2:=(Nat.div_add_mod _ 2).symm
 have hlt1:a % 2^k < 2^k:=Nat.mod_lt a hP
 have hlt2:(a / 2^k) % 2 < 2:=Nat.mod_lt _ (by omega)
 have hcomb:a=(a % 2^k+2^k*((a / 2^k) % 2))+2^(k+1)*(a / 2^k / 2):=by
  conv_lhs=>rw [hdm1,hdm2]
  rw [hpow];ring
 have hrem_lt:a % 2^k+2^k*((a / 2^k) % 2) < 2^(k+1):=by
  rw [hpow];nlinarith
 conv_lhs=>rw [hcomb]
 rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hrem_lt,h2]
lemma yB (a b k:ℕ) (c:Bool) :
  let ca:=(a % 2^k+b % 2^k+c.toNat) / 2^k
  let ba:=a.testBit k
  let bb:=b.testBit k
  let bc:=decide (ca=1)
  (a % 2^(k+1)+b % 2^(k+1)+c.toNat).testBit k=xor (xor ba bb) bc /\
  (a % 2^(k+1)+b % 2^(k+1)+c.toNat) / 2^(k+1) =
   ((ba&&bb)||(bc&&xor ba bb)).toNat:=by
 have ha:=jN a k
 have hb:=jN b k
 set P:=2^k
 have hP:0 < P:=Nat.two_pow_pos k
 set s:=a % P+b % P+c.toNat
 have hs_lt:s < 2*P:=by
  have h1:=Nat.mod_lt a hP
  have h2:=Nat.mod_lt b hP
  cases c <;> simp [s] <;> omega
 have hca_le:s / P ≤ 1:=by
  have hlt:s / P < 2:=(Nat.div_lt_iff_lt_mul hP).mpr (by omega)
  omega
 have hs_eq:s=s % P+P*(s / P):=by
  have:=Nat.div_add_mod s P;omega
 have htot:a % 2^(k+1)+b % 2^(k+1)+c.toNat =
   s % P+P*((a.testBit k).toNat+(b.testBit k).toNat+s / P):=by
  rw [ha,hb]
  have hsdef:s=a % P+b % P+c.toNat:=rfl
  linarith [hs_eq]
 set q:=(a.testBit k).toNat+(b.testBit k).toNat+s / P
 have hdiv:(a % 2^(k+1)+b % 2^(k+1)+c.toNat) / P=q:=by
  rw [htot,mul_comm P q,Nat.add_mul_div_right _ _ hP,Nat.div_eq_of_lt (Nat.mod_lt s hP),zero_add]
 have hdiv2:(a % 2^(k+1)+b % 2^(k+1)+c.toNat) / 2^(k+1)=q / 2:=by
  calc (a % 2^(k+1)+b % 2^(k+1)+c.toNat) / 2^(k+1)
    = (a % 2^(k+1)+b % 2^(k+1)+c.toNat) / (P*2):=by rw [pow_succ]
   _=((a % 2^(k+1)+b % 2^(k+1)+c.toNat) / P) / 2:=(Nat.div_div_eq_div_mul _ P 2).symm
   _=q / 2:=by rw [hdiv]
 have hbit:(a % 2^(k+1)+b % 2^(k+1)+c.toNat).testBit k=decide (q % 2=1):=by
  rw [Nat.testBit_eq_decide_div_mod_eq,hdiv]
 have hc_cases:s / P=0\/s / P=1:=by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hca_le with h0 | h1
  ·exact Or.inl h0
  ·exact Or.inr h1
 dsimp only
 rw [hbit,hdiv2]
 rcases hc_cases with hc | hc <;>
  cases ha':a.testBit k <;> cases hb':b.testBit k <;>
  simp [q,hc,ha',hb']
def gT {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb) :
  Q0 nIn c (1+W*11) (fun c'=>Q9 nIn c' W (fun x=>(fa x+fb x) % 2^W)):=
 Q0.weaken (by omega)<|
 (vJ c false).bind fun c0 h0 vfalse=>
 let Acc (k:ℕ) (_:k ≤ W) (c1:CB nIn):Type:=
  (∀ i:Fin W,i.val < k->Q4 nIn c1 (fun x=>(fa x+fb x).testBit i.val)) ×
  Q4 nIn c1 (fun x=>decide ((fa x % 2^k+fb x % 2^k) / 2^k=1))
 have hinit:Acc 0 (Nat.zero_le W) c0:=
  ⟨fun _ hi=>absurd hi (by omega),vfalse.cast fun _=>by simp only [pow_zero,Nat.mod_one,add_zero,Nat.zero_div];decide⟩
 (Q0.qe (Bstep:=11) W Acc c0 hinit fun k hk c1 h1 ⟨bits,carry⟩=>
  Q0.weaken (by omega)<|
  let ba:=(a.vec.at ⟨k,hk⟩).lift (CB.q0 h0 h1)
  let bb:=(b.vec.at ⟨k,hk⟩).lift (CB.q0 h0 h1)
  (g2 c1 ba bb).bind fun c2 h2 vx=>
  (g2 c2 vx (carry.lift h2)).bind fun c3 h3 vsum=>
  (vg c3 (ba.lift (CB.q0 h2 h3)) (bb.lift (CB.q0 h2 h3))).bind fun c4 h4 vand1=>
  (vg c4 (carry.lift (CB.q0 h2 (CB.q0 h3 h4)))
   (vx.lift (CB.q0 h3 h4))).bind fun c5 h5 vand2=>
  (yr c5 (vand1.lift h5) vand2).bind fun c6 h6 vcarry=>
  let hall:=CB.q0 h2 (CB.q0 h3 (CB.q0 h4 (CB.q0 h5 h6)))
  let h36:=CB.q0 h4 (CB.q0 h5 h6)
  Q0.pure
   ⟨fun i hi=>
    if hlt:i.val < k then (bits i hlt).lift hall
    else
     have heq:i=⟨k,hk⟩:=Fin.ext (by dsimp;omega)
     heq▸(vsum.lift h36).cast fun x=>by
      have hst:=(yB (fa x) (fb x) k false).1
      simp only [Bool.toNat_false,add_zero] at hst
      have hmod:(fa x % 2^(k+1)+fb x % 2^(k+1)).testBit k =
        (fa x+fb x).testBit k:=by
       have h1:(fa x % 2^(k+1)+fb x % 2^(k+1)) % 2^(k+1) =
         (fa x+fb x) % 2^(k+1):=by
        rw [Nat.add_mod,Nat.mod_mod,Nat.mod_mod,← Nat.add_mod]
       have h2:=congrArg (fun n=>n.testBit k) h1
       simp only [Nat.testBit_mod_two_pow,show k < k+1 by omega,decide_true,Bool.true_and] at h2
       exact h2
      rw [← hmod,hst],
   vcarry.cast fun x=>by
    have hst:=(yB (fa x) (fb x) k false).2
    simp only [Bool.toNat_false,add_zero] at hst
    rw [hst]
    cases ((fa x).testBit k&&(fb x).testBit k ||
     decide ((fa x % 2^k+fb x % 2^k) / 2^k=1) &&
     xor ((fa x).testBit k) ((fb x).testBit k)) <;> rfl⟩).bind fun cF _ ⟨bits,_⟩=>
 Q0.pure
  ⟨⟨fun i=>(bits i i.isLt).w,fun i=>(bits i i.isLt).hw,fun x i=>by
    rw [(bits i i.isLt).heval x,Nat.testBit_mod_two_pow]
    simp [i.isLt]⟩,
  fun x=>Nat.mod_lt _ (Nat.two_pow_pos W)⟩
def g4 {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb) :
  Q0 nIn c (1+W*10) (fun c'=>Q4 nIn c' (fun x=>decide (fa x < fb x))):=
 Q0.weaken (by omega)<|
 (vJ c false).bind fun c0 h0 vfalse=>
 let Acc (k:ℕ) (_:k ≤ W) (c1:CB nIn):Type:=
  Q4 nIn c1 (fun x=>decide (fa x % 2^k < fb x % 2^k))
 have hinit:Acc 0 (Nat.zero_le W) c0:=
  vfalse.cast fun _=>by simp only [pow_zero,Nat.mod_one];decide
 (Q0.qe (Bstep:=10) W Acc c0 hinit fun k hk c1 h1 acc=>
  Q0.weaken (by omega)<|
  let ba:=(a.vec.at ⟨k,hk⟩).lift (CB.q0 h0 h1)
  let bb:=(b.vec.at ⟨k,hk⟩).lift (CB.q0 h0 h1)
  (y2 c1 ba).bind fun c2 h2 vna=>
  (vg c2 vna (bb.lift h2)).bind fun c3 h3 vlt=>
  (dj c3 (ba.lift (CB.q0 h2 h3)) (bb.lift (CB.q0 h2 h3))).bind fun c4 h4 veq=>
  (vg c4 veq (acc.lift (CB.q0 h2 (CB.q0 h3 h4)))).bind fun c5 h5 vboth=>
  (yr c5 (vlt.lift (CB.q0 h4 h5)) vboth).bind fun c6 _ vres=>
  Q0.pure<|vres.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dH,dI,Bool.not_eq_true',dG]
   have ha:=jN (fa x) k
   have hb:=jN (fb x) k
   have hP:0 < 2^k:=Nat.two_pow_pos k
   have ham:=Nat.mod_lt (fa x) hP
   have hbm:=Nat.mod_lt (fb x) hP
   rw [ha,hb]
   cases hta:(fa x).testBit k <;> cases htb:(fb x).testBit k <;> simp <;> omega).bind fun cF _ vres=>
 Q0.pure<|vres.cast fun x=>by
  rw [Nat.mod_eq_of_lt (a.hlt x),Nat.mod_eq_of_lt (b.hlt x)]
def dt {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb) :
  Q0 nIn c (2+W*10) (fun c'=>Q4 nIn c' (fun x=>decide (fa x ≤ fb x))):=
 Q0.weaken (by omega)<|
 (g4 c b a).bind fun c1 _ vlt=>
 (y2 c1 vlt).bind fun c2 _ vres=>
 Q0.pure<|vres.cast fun x=>by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',decide_eq_false_iff_not,dG,not_lt]
def dz {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb)
  (hle:∀ x,fb x ≤ fa x) :
  Q0 nIn c (1+W*12) (fun c'=>Q9 nIn c' W (fun x=>fa x - fb x)):=
 Q0.weaken (by omega)<|
 (vJ c true).bind fun c0 h0 vtrue=>
 let Acc (k:ℕ) (_:k ≤ W) (c1:CB nIn):Type:=
  (∀ i:Fin W,i.val < k->Q4 nIn c1 (fun x=>(fa x - fb x).testBit i.val)) ×
  Q4 nIn c1 (fun x=>decide ((fa x % 2^k+((2^W - 1 - fb x) % 2^k)+1) / 2^k=1))
 have hinit:Acc 0 (Nat.zero_le W) c0:=
  ⟨fun _ hi=>absurd hi (by omega),vtrue.cast fun _=>by simp only [pow_zero,Nat.mod_one,add_zero,zero_add,Nat.div_one];decide⟩
 (Q0.qe (Bstep:=12) W Acc c0 hinit fun k hk c1 h1 ⟨bits,carry⟩=>
  Q0.weaken (by omega)<|
  let ba:=(a.vec.at ⟨k,hk⟩).lift (CB.q0 h0 h1)
  let bb:=(b.vec.at ⟨k,hk⟩).lift (CB.q0 h0 h1)
  (y2 c1 bb).bind fun c2 h2 vnb=>
  (g2 c2 (ba.lift h2) vnb).bind fun c3 h3 vx=>
  (g2 c3 vx (carry.lift (CB.q0 h2 h3))).bind fun c4 h4 vsum=>
  (vg c4 (ba.lift (CB.q0 h2 (CB.q0 h3 h4)))
   (vnb.lift (CB.q0 h3 h4))).bind fun c5 h5 vand1=>
  (vg c5 (carry.lift (CB.q0 h2 (CB.q0 h3 (CB.q0 h4 h5))))
   (vx.lift (CB.q0 h4 h5))).bind fun c6 h6 vand2=>
  (yr c6 (vand1.lift h6) vand2).bind fun c7 h7 vcarry=>
  let hall:=CB.q0 h2 (CB.q0 h3 (CB.q0 h4
   (CB.q0 h5 (CB.q0 h6 h7))))
  let h47:=CB.q0 h5 (CB.q0 h6 h7)
  have hnb:∀ x,(!(fb x).testBit k)=(2^W - 1 - fb x).testBit k:=by
   intro x
   have hblt:=b.hlt x
   have hP:0 < 2^k:=Nat.two_pow_pos k
   have hsplit:2^W=2^k*2^(W - k):=by
    rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt hk)]
   have hpos2:1 ≤ 2^(W - k):=Nat.one_le_two_pow
   have hq_le:fb x / 2^k < 2^(W - k):=by
    rw [Nat.div_lt_iff_lt_mul hP,mul_comm,← hsplit];exact hblt
   have hmod_lt:fb x % 2^k < 2^k:=Nat.mod_lt _ hP
   have hdm:fb x=(fb x / 2^k)*2^k+fb x % 2^k:=by
    rw [mul_comm];exact (Nat.div_add_mod _ _).symm
   have h1:(2^(W - k) - 1)*2^k+2^k=2^W:=by
    rw [← Nat.add_one_mul,Nat.sub_add_cancel hpos2,mul_comm,hsplit]
   have h2:(2^(W - k) - 1 - fb x / 2^k)*2^k+(fb x / 2^k)*2^k =
     (2^(W - k) - 1)*2^k:=by
    rw [← Nat.add_mul,Nat.sub_add_cancel (by omega)]
   have hsub_eq:2^W - 1 - fb x =
     (2^k - 1 - fb x % 2^k)+(2^(W - k) - 1 - fb x / 2^k)*2^k:=by
    omega
   have hdiv_eq:(2^W - 1 - fb x) / 2^k=2^(W - k) - 1 - fb x / 2^k:=by
    rw [hsub_eq,Nat.add_mul_div_right _ _ hP,Nat.div_eq_of_lt (by omega),zero_add]
   have heven:2 ∣ 2^(W - k):=dvd_pow_self 2 (by omega)
   obtain ⟨r,hr⟩:=heven
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hdiv_eq]
   have hm1:(2^(W - k) - 1 - fb x / 2^k) % 2=1 - (fb x / 2^k) % 2:=by omega
   have hm2:(fb x / 2^k) % 2 < 2:=Nat.mod_lt _ (by omega)
   by_cases hmod:(fb x / 2^k) % 2=1 <;> simp [hm1,hmod] <;> omega
  Q0.pure
   ⟨fun i hi=>
    if hlt:i.val < k then (bits i hlt).lift hall
    else
     have heq:i=⟨k,hk⟩:=Fin.ext (by dsimp;omega)
     heq▸(vsum.lift h47).cast fun x=>by
      have hst:=(yB (fa x) (2^W - 1 - fb x) k true).1
      simp only [Bool.toNat_true] at hst
      dsimp only
      rw [hnb x,← hst]
      have hmod:(fa x % 2^(k+1)+(2^W - 1 - fb x) % 2^(k+1)+1) % 2^(k+1) =
        (fa x - fb x) % 2^(k+1):=by
       have hle':=hle x
       have hblt:=b.hlt x
       have hEq:fa x+(2^W - 1 - fb x)+1=(fa x - fb x)+2^W:=by omega
       have hdvd:2^(k+1) ∣ 2^W:=Nat.pow_dvd_pow 2 hk
       obtain ⟨q,hq⟩:=hdvd
       have h1:(fa x % 2^(k+1)+(2^W - 1 - fb x) % 2^(k+1)+1) % 2^(k+1) =
         (fa x+(2^W - 1 - fb x)+1) % 2^(k+1):=by
        simp only [Nat.add_mod,Nat.mod_mod]
       rw [h1,hEq,hq,Nat.add_mul_mod_self_left]
      have h2:=congrArg (fun n=>n.testBit k) hmod
      simp only [Nat.testBit_mod_two_pow,show k < k+1 by omega,decide_true,Bool.true_and] at h2
      exact h2,
   vcarry.cast fun x=>by
    have hst:=(yB (fa x) (2^W - 1 - fb x) k true).2
    simp only [Bool.toNat_true] at hst
    dsimp only
    rw [hnb x,hst]
    cases ((fa x).testBit k&&(2^W - 1 - fb x).testBit k ||
     decide ((fa x % 2^k+(2^W - 1 - fb x) % 2^k+1) / 2^k=1) &&
     xor ((fa x).testBit k) ((2^W - 1 - fb x).testBit k)) <;> rfl⟩).bind fun cF _ ⟨bits,_⟩=>
 Q0.pure
  ⟨⟨fun i=>(bits i i.isLt).w,fun i=>(bits i i.isLt).hw,fun x i=>(bits i i.isLt).heval x⟩,
  fun x=>Nat.lt_of_le_of_lt (Nat.sub_le _ _) (a.hlt x)⟩
def z4 {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb)
  (hsum:∀ x,fa x+fb x < 2^W) :
  Q0 nIn c (1+W*11) (fun c'=>Q9 nIn c' W (fun x=>fa x+fb x)):=
 Q0.weaken (by omega)<|
 (gT c a b).bind fun _ _ r=>
  Q0.pure (r.cast fun x=>Nat.mod_eq_of_lt (hsum x))
def dh {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb) :
  Q0 nIn c (1+W*14) (fun c'=>Q9 nIn c' W (fun x=>max (fa x) (fb x))):=
 Q0.weaken (by omega)<|
 (g4 c a b).bind fun c1 h1 vlt=>
 (vH c1 vlt (b.lift h1) (a.lift h1)).bind fun _ _ vres=>
 Q0.pure<|vres.cast fun x=>by
  by_cases h:fa x < fb x
  ·simp [h,max_eq_right (Nat.le_of_lt h)]
  ·simp [h,max_eq_left (not_lt.mp h)]
def dA {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb) :
  Q0 nIn c (1+W*14) (fun c'=>Q9 nIn c' W (fun x=>min (fa x) (fb x))):=
 Q0.weaken (by omega)<|
 (g4 c a b).bind fun c1 h1 vlt=>
 (vH c1 vlt (a.lift h1) (b.lift h1)).bind fun _ _ vres=>
 Q0.pure<|vres.cast fun x=>by
  by_cases h:fa x < fb x
  ·simp [h,min_eq_left (Nat.le_of_lt h)]
  ·simp [h,min_eq_right (not_lt.mp h)]
def zH {nIn:ℕ} (c:CB nIn) {W:ℕ}
  {fa fb:(Fin nIn->Bool)->ℕ}
  (a:Q9 nIn c W fa) (b:Q9 nIn c W fb) :
  Q0 nIn c (1+W*6) (fun c'=>Q4 nIn c' (fun x=>decide (fa x=fb x))):=
 Q0.weaken (by omega)<|
 (gF c a.vec b.vec).bind fun _ _ v=>
  Q0.pure<|v.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dG]
   constructor
   ·intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi:i < W
    ·exact congrFun h ⟨i,hi⟩
    ·rw [Nat.testBit_lt_two_pow ((a.hlt x).trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hi))),
       Nat.testBit_lt_two_pow ((b.hlt x).trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hi)))]
   ·intro h;funext i;rw [h]
def gP {nIn:ℕ} (c:CB nIn) {N W:ℕ} (hW:1 ≤ W) (hNW:N < 2^W)
  {f:(Fin nIn->Bool)->Fin N->Bool} (a:Q2 nIn c N f) :
  Q0 nIn c (W*2+N*(1+W*15))
   (fun c'=>Q9 nIn c' W (fun x=>(Finset.univ.filter (fun i:Fin N=>f x i=true)).card)):=
 Q0.weaken (by omega)<|
 (qS c W 0 (Nat.two_pow_pos W)).bind fun c0 h0 v0=>
 (qS c0 W 1 (Nat.one_lt_two_pow (by omega))).bind fun c1 h1 v1=>
 let Acc (k:ℕ) (_:k ≤ N) (c2:CB nIn):Type:=
  Q9 nIn c2 W (fun x=>(Finset.univ.filter (fun i:Fin N=>i.val < k/\f x i=true)).card)
 have hinit:Acc 0 (Nat.zero_le N) c1:=
  (v0.lift h1).cast fun x=>by
   have:(Finset.univ.filter fun i:Fin N=>i.val < 0/\f x i=true)=∅:=by
    ext i;simp
   rw [this,Finset.card_empty]
 (Q0.qe (Bstep:=1+W*15) N Acc c1 hinit fun k hk c2 h2 acc=>
  Q0.weaken (by omega)<|
  let h02:=CB.q0 h0 (CB.q0 h1 h2)
  have hsum:∀ x,
    (Finset.univ.filter (fun i:Fin N=>i.val < k/\f x i=true)).card+1 < 2^W:=by
   intro x
   have hcard:(Finset.univ.filter (fun i:Fin N=>i.val < k/\f x i=true)).card ≤ k:=by
    have hsub:Finset.univ.filter (fun i:Fin N=>i.val < k/\f x i=true) ⊆
      Finset.univ.filter (fun i:Fin N=>i.val < k):=by
     intro i hi
     simp only [dK,dL,true_and] at hi ⊢
     exact hi.1
    have hc2:(Finset.univ.filter (fun i:Fin N=>i.val < k)).card ≤ k:=by
     have hmap:(Finset.univ.filter (fun i:Fin N=>i.val < k)).card ≤ (Finset.range k).card:=by
      refine Finset.card_le_card_of_injOn (fun i:Fin N=>i.val) ?_ (fun _ _ _ _ h=>Fin.ext h)
      intro i hi
      simp only [Finset.mem_coe,dK,dL,true_and] at hi
      simp only [Finset.mem_coe,Finset.mem_range]
      exact hi
     simpa using hmap
    exact (Finset.card_le_card hsub).trans hc2
   omega
  (z4 c2 acc (v1.lift h2) hsum).bind fun c3 h3 vplus=>
  (vH c3 ((a.at ⟨k,hk⟩).lift (CB.q0 h02 h3)) vplus (acc.lift h3)).bind fun _ _ vres=>
  Q0.pure<|vres.cast fun x=>by
   set S0:=Finset.univ.filter (fun i:Fin N=>i.val < k/\f x i=true)
   set S1:=Finset.univ.filter (fun i:Fin N=>i.val < k+1/\f x i=true)
   by_cases hfx:f x ⟨k,hk⟩=true
   ·simp only [hfx,↓reduceIte]
    have hnot:(⟨k,hk⟩:Fin N)∉S0:=by simp [S0]
    have heq:S1=insert ⟨k,hk⟩ S0:=by
     ext i
     simp only [S1,S0,Finset.mem_insert,dK,dL,true_and]
     constructor
     ·rintro ⟨hlt,hf⟩
      by_cases hlk:i.val < k
      ·right;exact ⟨hlk,hf⟩
      ·left;exact Fin.ext (by dsimp;omega)
     ·rintro (rfl | ⟨hlk,hf⟩)
      ·exact ⟨by dsimp;omega,hfx⟩
      ·exact ⟨by omega,hf⟩
    change S0.card+1=S1.card
    rw [heq,Finset.card_insert_of_notMem hnot]
   ·simp only [hfx,Bool.false_eq_true,↓reduceIte]
    have heq:S1=S0:=by
     ext i
     simp only [S1,S0,dK,dL,true_and]
     constructor
     ·rintro ⟨hlt,hf⟩
      by_cases hlk:i.val < k
      ·exact ⟨hlk,hf⟩
      ·have hi:i=⟨k,hk⟩:=Fin.ext (by dsimp;omega)
       rw [hi] at hf;exact absurd hf hfx
     ·rintro ⟨hlk,hf⟩;exact ⟨by omega,hf⟩
    change S0.card=S1.card
    rw [heq]).bind fun cF _ vres=>
 Q0.pure<|vres.cast fun x=>by
  congr 1;ext i;simp
end CircuitDSL
section GF2LinAlg
abbrev Q1 (m:ℕ):Type:=Fin m->Bool
abbrev Q6 (m:ℕ):Type:=Fin m->Q1 m
def q2 (m:ℕ):Q1 m:=fun _=>false
def q5 {m:ℕ} (u v:Q1 m):Q1 m:=fun i=>xor (u i) (v i)
def qN (m:ℕ):Q6 m:=fun _=>q2 m
def q4 {m:ℕ} (v:Q1 m):Fin m->ZMod 2:=
 fun i=>if v i=true then 1 else 0
lemma qh (m:ℕ):q4 (q2 m)=0:=by
 funext i;simp [q4,q2]
lemma qE {m:ℕ} (u v:Q1 m):q4 (q5 u v)=q4 u+q4 v:=by
 funext i
 cases hu:u i <;> cases hv:v i <;> simp [q4,q5,hu,hv]
 rfl
lemma v7 {m:ℕ}:Function.Injective (@q4 m):=by
 intro u v h
 funext i
 have hi:=congrFun h i
 simp only [q4] at hi
 cases hu:u i <;> cases hv:v i <;> simp [hu,hv] at hi ⊢
lemma qD (z:ZMod 2):z=0\/z=1:=by
 revert z;decide
lemma yZ {z:ZMod 2} (h:z ≠ 0):z=1:=by
 revert h;revert z;decide
lemma qM {m:ℕ} (x:Fin m->ZMod 2):x+x=0:=by
 funext i
 simp only [Pi.add_apply,Pi.zero_apply]
 rcases qD (x i) with h | h <;> rw [h] <;> decide
lemma yX {m:ℕ} (x y:Fin m->ZMod 2):x=y ↔ x+y=0:=by
 constructor
 ·rintro rfl;exact qM x
 ·intro h
  calc x=x+(y+y):=by rw [qM,add_zero]
   _=(x+y)+y:=(add_assoc _ _ _).symm
   _=y:=by rw [h,zero_add]
def Q3 {m:ℕ} (T:Q6 m):Prop:=
 ∀ c:Fin m,T c=q2 m\/(T c c=true/\∀ c':Fin m,c'.val < c.val->T c c'=false)
def q6 {m:ℕ} (T:Q6 m):Submodule (ZMod 2) (Fin m->ZMod 2):=
 Submodule.span (ZMod 2) (Set.range (fun c:Fin m=>q4 (T c)))
def q3 {m:ℕ} (T:Q6 m):ℕ:=
 (Finset.univ.filter fun c:Fin m=>T c c=true).card
lemma jE (m:ℕ):Q3 (qN m):=
 fun _=>Or.inl rfl
lemma y6 (m:ℕ):q6 (qN m)=⊥:=by
 unfold q6 qN
 rw [Submodule.span_eq_bot]
 rintro _ ⟨c,rfl⟩
 exact qh m
lemma vS {m:ℕ} {T:Q6 m} (hT:Q3 T)
  (c:Fin m) (hc:T c c=false):T c=q2 m:=by
 rcases hT c with h0 | ⟨h1,_⟩
 ·exact h0
 ·rw [hc] at h1;exact Bool.noConfusion h1
lemma yi {m:ℕ} {T:Q6 m} (hT:Q3 T) :
  LinearIndependent (ZMod 2) (fun c:{c:Fin m // T c c=true}=>q4 (T c.1)):=by
 rw [Fintype.linearIndependent_iff]
 intro g hg
 by_contra hne
 push Not at hne
 let S:=Finset.univ.filter fun c:{c:Fin m // T c c=true}=>g c ≠ 0
 have hSne:S.Nonempty:=by
  obtain ⟨c,hc⟩:=hne
  exact ⟨c,Finset.mem_filter.mpr ⟨dL c,hc⟩⟩
 let c0:=S.min' hSne
 have hc0_mem:c0∈S:=Finset.min'_mem S hSne
 have hc0_nz:g c0 ≠ 0:=(Finset.mem_filter.mp hc0_mem).2
 have hc0_eq1:g c0=1:=by
  generalize g c0=z at hc0_nz
  revert hc0_nz;revert z;decide
 have hval:=congrFun hg c0.1
 simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hval
 have hzero_other:∀ c:{c:Fin m // T c c=true},c ≠ c0->g c*q4 (T c.1) c0.1=0:=by
  intro c hcc0
  by_cases hgc:g c=0
  ·rw [hgc,zero_mul]
  ·have hcS:c∈S:=Finset.mem_filter.mpr ⟨dL c,hgc⟩
   have hle:c0 ≤ c:=Finset.min'_le S c hcS
   have hlt:c0.1.val < c.1.val:=by
    have h1:c0.1.val ≤ c.1.val:=hle
    have h2:c0.1.val ≠ c.1.val:=fun e=>hcc0 (Subtype.ext (Fin.ext e)).symm
    omega
   rcases hT c.1 with h0 | ⟨_,hlow⟩
   ·rw [h0,qh];simp
   ·have hf:T c.1 c0.1=false:=hlow c0.1 hlt
    simp [q4,hf]
 rw [Finset.sum_eq_single c0 (fun c _ hne=>hzero_other c hne) (fun h=>absurd (dL c0) h)] at hval
 rw [hc0_eq1,one_mul] at hval
 simp only [q4,c0.2,↓reduceIte] at hval
 exact one_ne_zero hval
lemma jR {m:ℕ} {T:Q6 m} (hT:Q3 T) :
  q6 T=Submodule.span (ZMod 2) (Set.range (fun c:{c:Fin m // T c c=true}=>q4 (T c.1))):=by
 apply le_antisymm
 ·rw [q6,Submodule.span_le]
  rintro _ ⟨c,rfl⟩
  by_cases hc:T c c=true
  ·exact Submodule.subset_span ⟨⟨c,hc⟩,rfl⟩
  ·have h0:T c=q2 m:=vS hT c (Bool.eq_false_iff.mpr hc)
   dsimp only
   rw [h0,qh]
   exact Submodule.zero_mem _
 ·rw [Submodule.span_le]
  rintro _ ⟨⟨c,_⟩,rfl⟩
  exact Submodule.subset_span ⟨c,rfl⟩
lemma qo {m:ℕ} {T:Q6 m} (hT:Q3 T) :
  Module.finrank (ZMod 2) (q6 T)=q3 T:=by
 rw [jR hT,finrank_span_eq_card (yi hT)]
 simp only [q3,Fintype.card_subtype]
lemma vZ {m:ℕ} {T:Q6 m} (hT:Q3 T)
  {u:Fin m->ZMod 2} (hu:u∈q6 T) (hpiv:∀ c:Fin m,T c c=true->u c=0) :
  u=0:=by
 rw [jR hT,Submodule.mem_span_range_iff_exists_fun] at hu
 obtain ⟨g,rfl⟩:=hu
 have hg0:∀ c:{c:Fin m // T c c=true},g c=0:=by
  by_contra hne
  push Not at hne
  let S:=Finset.univ.filter fun c:{c:Fin m // T c c=true}=>g c ≠ 0
  have hSne:S.Nonempty:=by
   obtain ⟨c,hc⟩:=hne
   exact ⟨c,Finset.mem_filter.mpr ⟨dL c,hc⟩⟩
  let c0:=S.min' hSne
  have hc0_nz:g c0 ≠ 0:=(Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
  have hc0_eq1:g c0=1:=by
   generalize g c0=z at hc0_nz;revert hc0_nz;revert z;decide
  have hval:(∑ c:{c:Fin m // T c c=true},g c • q4 (T c.1)) c0.1=0:=hpiv c0.1 c0.2
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hval
  have hzero_other:∀ c:{c:Fin m // T c c=true},c ≠ c0->g c*q4 (T c.1) c0.1=0:=by
   intro c hcc0
   by_cases hgc:g c=0
   ·rw [hgc,zero_mul]
   ·have hle:c0 ≤ c:=Finset.min'_le S c (Finset.mem_filter.mpr ⟨dL c,hgc⟩)
    have hlt:c0.1.val < c.1.val:=by
     have h1:c0.1.val ≤ c.1.val:=hle
     have h2:c0.1.val ≠ c.1.val:=fun e=>hcc0 (Subtype.ext (Fin.ext e)).symm
     omega
    rcases hT c.1 with h0 | ⟨_,hlow⟩
    ·rw [h0,qh];simp
    ·simp [q4,hlow c0.1 hlt]
  rw [Finset.sum_eq_single c0 (fun c _ hne=>hzero_other c hne) (fun h=>absurd (dL c0) h)] at hval
  rw [hc0_eq1,one_mul] at hval
  simp only [q4,c0.2,↓reduceIte] at hval
  exact one_ne_zero hval
 simp [hg0]
def je {m:ℕ} (c:Fin m) (st:Q6 m × Q1 m):Q6 m × Q1 m:=
 let T:=st.1
 let v:=st.2
 if v c=true then
  if T c c=true then (T,q5 v (T c))
  else (Function.update T c v,q2 m)
 else (T,v)
def qC {m:ℕ} (T:Q6 m) (v:Q1 m):Q6 m:=
 ((dF m).foldl (fun st c=>je c st) (T,v)).1
lemma jG {m:ℕ} (T:Q6 m) (hT:Q3 T) (v:Q1 m) :
  Q3 (qC T v) /\
   q6 (qC T v)=q6 T ⊔ Submodule.span (ZMod 2) {q4 v}:=by
 have hgo:∀ (k:ℕ) (hk:k ≤ m),
   let st:=((dF m).take k).foldl (fun st c=>je c st) (T,v)
   Q3 st.1 /\
   (∀ i:Fin m,i.val < k->st.2 i=false) /\
   q6 st.1 ⊔ Submodule.span (ZMod 2) {q4 st.2} =
    q6 T ⊔ Submodule.span (ZMod 2) {q4 v}:=by
  intro k
  induction k with
  | zero=>
   intro _
   refine ⟨hT,fun _ hi=>absurd hi (by omega),rfl⟩
  | succ k ih=>
   intro hk
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)]
    simp
   obtain ⟨hE,hlow,hsp⟩:=ih (Nat.le_of_succ_le hk)
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF m).take k).foldl (fun st c=>je c st) (T,v)
   set c:Fin m:=⟨k,hk⟩
   unfold je
   by_cases hvc:st.2 c=true
   ·simp only [hvc,↓reduceIte]
    by_cases hTc:st.1 c c=true
    ·simp only [hTc,↓reduceIte]
     refine ⟨hE,?_,?_⟩
     ·intro i hi
      by_cases hlt:i.val < k
      ·have h1:=hlow i hlt
       have h2:st.1 c i=false:=by
        rcases hE c with h0 | ⟨_,hcl⟩
        ·rw [h0];rfl
        ·exact hcl i hlt
       simp [q5,h1,h2]
      ·have heq:i=c:=Fin.ext (by dsimp [c];omega)
       rw [heq];simp [q5,hvc,hTc]
     ·rw [← hsp]
      have hmem:q4 (st.1 c)∈q6 st.1:=Submodule.subset_span ⟨c,rfl⟩
      apply le_antisymm
      ·refine sup_le le_sup_left ?_
       rw [Submodule.span_singleton_le_iff_mem,qE]
       exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hmem)
      ·refine sup_le le_sup_left ?_
       rw [Submodule.span_singleton_le_iff_mem]
       have hEq:q4 st.2=q4 (q5 st.2 (st.1 c))+q4 (st.1 c):=by
        rw [qE,add_assoc,qM,add_zero]
       rw [hEq]
       exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hmem)
    ·simp only [hTc,Bool.false_eq_true,↓reduceIte]
     have hTc0:st.1 c=q2 m:=vS hE c (Bool.eq_false_iff.mpr hTc)
     refine ⟨?_,fun _ _=>rfl,?_⟩
     ·intro j
      by_cases hjc:j=c
      ·subst hjc;right;rw [Function.update_self];exact ⟨hvc,hlow⟩
      ·rw [Function.update_of_ne hjc];exact hE j
     ·rw [← hsp,qh,Submodule.span_zero_singleton,sup_bot_eq]
      apply le_antisymm
      ·rw [q6,Submodule.span_le]
       rintro _ ⟨j,rfl⟩
       dsimp only
       by_cases hjc:j=c
       ·subst hjc;rw [Function.update_self]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
       ·rw [Function.update_of_ne hjc]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨j,rfl⟩)
      ·refine sup_le ?_ ?_
       ·rw [q6,Submodule.span_le]
        rintro _ ⟨j,rfl⟩
        dsimp only
        by_cases hjc:j=c
        ·subst hjc;rw [hTc0,qh];exact Submodule.zero_mem _
        ·exact Submodule.subset_span ⟨j,by dsimp only;rw [Function.update_of_ne hjc]⟩
       ·rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span ⟨c,by dsimp only;rw [Function.update_self]⟩
   ·simp only [hvc,Bool.false_eq_true,↓reduceIte]
    refine ⟨hE,?_,hsp⟩
    intro i hi
    by_cases hlt:i.val < k
    ·exact hlow i hlt
    ·have heq:i=c:=Fin.ext (by dsimp [c];omega)
     rw [heq];exact Bool.eq_false_iff.mpr hvc
 obtain ⟨hE,hlow,hsp⟩:=hgo m le_rfl
 have htake:(dF m).take m=dF m:=by simp
 rw [htake] at hE hlow hsp
 have hv0:((dF m).foldl (fun st c=>je c st) (T,v)).2=q2 m:=by
  funext i;exact hlow i i.isLt
 rw [hv0,qh,Submodule.span_zero_singleton,sup_bot_eq] at hsp
 exact ⟨hE,hsp⟩
def jd {m:ℕ} (T:Q6 m) (c:Fin m) (v:Q1 m):Q1 m:=
 if v c=true/\T c c=true then q5 v (T c) else v
def q8 {m:ℕ} (T:Q6 m) (v:Q1 m):Q1 m:=
 (dF m).foldl (fun acc c=>jd T c acc) v
lemma y8 {m:ℕ} (T:Q6 m) (hT:Q3 T) (v:Q1 m) :
  q4 (q8 T v)+q4 v∈q6 T /\
   ∀ c:Fin m,T c c=true->q8 T v c=false:=by
 have hgo:∀ (k:ℕ) (hk:k ≤ m),
   let r:=((dF m).take k).foldl (fun acc c=>jd T c acc) v
   q4 r+q4 v∈q6 T /\
   ∀ c:Fin m,c.val < k->T c c=true->r c=false:=by
  intro k
  induction k with
  | zero=>
   intro _
   dsimp only
   rw [List.take_zero,List.foldl_nil]
   exact ⟨by rw [qM];exact Submodule.zero_mem _,fun _ hi=>absurd hi (by omega)⟩
  | succ k ih=>
   intro hk
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   obtain ⟨hmem,hpiv⟩:=ih (Nat.le_of_succ_le hk)
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set r:=((dF m).take k).foldl (fun acc c=>jd T c acc) v
   set c:Fin m:=⟨k,hk⟩
   unfold jd
   by_cases hcond:r c=true/\T c c=true
   ·simp only [hcond,and_self,↓reduceIte]
    refine ⟨?_,?_⟩
    ·have h1:q4 (q5 r (T c))+q4 v=(q4 r+q4 v)+q4 (T c):=by
      rw [qE];abel
     rw [h1]
     exact Submodule.add_mem _ hmem (Submodule.subset_span ⟨c,rfl⟩)
    ·intro j hj hTj
     by_cases hlt:j.val < k
     ·have h1:=hpiv j hlt hTj
      have h2:T c j=false:=by
       rcases hT c with h0 | ⟨_,hcl⟩
       ·rw [h0];rfl
       ·exact hcl j hlt
      simp [q5,h1,h2]
     ·have heq:j=c:=Fin.ext (by dsimp [c];omega)
      rw [heq];simp [q5,hcond.1,hcond.2]
   ·simp only [hcond,↓reduceIte]
    refine ⟨hmem,?_⟩
    intro j hj hTj
    by_cases hlt:j.val < k
    ·exact hpiv j hlt hTj
    ·have heq:j=c:=Fin.ext (by dsimp [c];omega)
     rw [heq] at hTj ⊢
     have:r c ≠ true:=fun h=>hcond ⟨h,hTj⟩
     exact Bool.eq_false_iff.mpr this
 have h:=hgo m le_rfl
 have htake:(dF m).take m=dF m:=by simp
 rw [htake] at h
 exact ⟨h.1,fun c hc=>h.2 c c.isLt hc⟩
lemma qG {m:ℕ} {T:Q6 m} (hT:Q3 T) (v:Q1 m) :
  q8 T v=q2 m ↔ q4 v∈q6 T:=by
 obtain ⟨hmem,hpiv⟩:=y8 T hT v
 constructor
 ·intro h0
  rw [h0,qh,zero_add] at hmem
  exact hmem
 ·intro hv
  have hr_mem:q4 (q8 T v)∈q6 T:=by
   have h1:q4 (q8 T v)=(q4 (q8 T v)+q4 v)+q4 v:=by
    rw [add_assoc,qM,add_zero]
   rw [h1]
   exact Submodule.add_mem _ hmem hv
  have hr_zero:q4 (q8 T v)=0:=
   vZ hT hr_mem fun c hc=>by simp [q4,hpiv c hc]
  exact v7 (hr_zero.trans (qh m).symm)
lemma jc {m:ℕ} {T:Q6 m} (hT:Q3 T) (u v:Q1 m) :
  q8 T (q5 u v)=q5 (q8 T u) (q8 T v):=by
 obtain ⟨hu_m,hu_p⟩:=y8 T hT u
 obtain ⟨hv_m,hv_p⟩:=y8 T hT v
 obtain ⟨huv_m,huv_p⟩:=y8 T hT (q5 u v)
 have hdiff_mem:q4 (q8 T (q5 u v))+q4 (q5 (q8 T u) (q8 T v))∈q6 T:=by
  have hEq:q4 (q8 T (q5 u v))+q4 (q5 (q8 T u) (q8 T v)) =
    (q4 (q8 T (q5 u v))+q4 (q5 u v)) +
    ((q4 (q8 T u)+q4 u)+(q4 (q8 T v)+q4 v)):=by
   rw [qE,qE]
   calc q4 (q8 T (q5 u v))+(q4 (q8 T u)+q4 (q8 T v))
     = q4 (q8 T (q5 u v))+(q4 (q8 T u)+q4 (q8 T v)) +
      ((q4 u+q4 u)+(q4 v+q4 v)):=by rw [qM,qM,add_zero,add_zero]
    _=_:=by abel
  rw [hEq]
  exact Submodule.add_mem _ huv_m (Submodule.add_mem _ hu_m hv_m)
 have hdiff_zero:q4 (q8 T (q5 u v))+q4 (q5 (q8 T u) (q8 T v))=0:=by
  refine vZ hT hdiff_mem fun c hc=>?_
  simp only [Pi.add_apply,q4,q5,huv_p c hc,hu_p c hc,hv_p c hc]
  decide
 exact v7 ((yX _ _).mpr hdiff_zero)
lemma yL {m:ℕ} {T:Q6 m} (hT:Q3 T) :
  q8 T (q2 m)=q2 m:=
 (qG hT _).mpr (by rw [qh];exact Submodule.zero_mem _)
def qH {m:ℕ} (c:Fin m) (st:Q6 m × Q6 m × Q1 m × Q1 m) :
  Q6 m × Q6 m × Q1 m × Q1 m:=
 let Pr:=st.1
 let Pl:=st.2.1
 let r:=st.2.2.1
 let l:=st.2.2.2
 if r c=true then
  if Pr c c=true then (Pr,Pl,q5 r (Pr c),q5 l (Pl c))
  else (Function.update Pr c r,Function.update Pl c l,q2 m,q2 m)
 else (Pr,Pl,r,l)
def y3 {m:ℕ} (T_R:Q6 m) (st:Q6 m × Q6 m × Q6 m) (u:Q1 m) :
  Q6 m × Q6 m × Q6 m:=
 let r0:=q8 T_R u
 let res:=(dF m).foldl (fun s c=>qH c s) (st.1,st.2.1,r0,u)
 (res.1,res.2.1,qC st.2.2 res.2.2.2)
def vv {m:ℕ} (T_L T_R:Q6 m):Q6 m × Q6 m × Q6 m:=
 (dF m).foldl (fun st i=>y3 T_R st (T_L i)) (qN m,qN m,qN m)
def jb {m:ℕ} (Pr Pl:Q6 m) (c:Fin m) (st:Q1 m × Q1 m) :
  Q1 m × Q1 m:=
 if st.1 c=true/\Pr c c=true then (q5 st.1 (Pr c),q5 st.2 (Pl c)) else st
def zs {m:ℕ} (Pr Pl T_R:Q6 m) (y:Q1 m):Bool × Q1 m:=
 let res:=(dF m).foldl (fun st c=>jb Pr Pl c st) (q8 T_R y,q2 m)
 (decide (res.1=q2 m),res.2)
lemma gC {m:ℕ} (T:Q6 m) (hT:Q3 T) (vs:List (Q1 m)) :
  Q3 (vs.foldl qC T) /\
   q6 (vs.foldl qC T) =
    q6 T ⊔ Submodule.span (ZMod 2) ((vs.map q4).toFinset:Set (Fin m->ZMod 2)):=by
 induction vs generalizing T with
 | nil=>simp [hT]
 | cons v vs ih=>
  simp only [List.foldl_cons,List.map_cons,List.toFinset_cons,Finset.coe_insert]
  obtain ⟨hE1,hsp1⟩:=jG T hT v
  obtain ⟨hE2,hsp2⟩:=ih (qC T v) hE1
  refine ⟨hE2,?_⟩
  rw [hsp2,hsp1,Submodule.span_insert,sup_assoc]
lemma zq {m:ℕ} (T_R:Q6 m) (hR:Q3 T_R)
  (U:Submodule (ZMod 2) (Fin m->ZMod 2))
  (Pr Pl:Q6 m) (hPr:Q3 Pr)
  (hPlU:∀ c:Fin m,q4 (Pl c)∈U)
  (hRel:∀ c:Fin m,Pr c=q8 T_R (Pl c))
  (u:Q1 m) :
  let res:=(dF m).foldl (fun s c=>qH c s) (Pr,Pl,q8 T_R u,u)
  Q3 res.1 /\
  (∀ c:Fin m,q4 (res.2.1 c)∈U ⊔ Submodule.span (ZMod 2) {q4 u}) /\
  (∀ c:Fin m,res.1 c=q8 T_R (res.2.1 c)) /\
  q6 res.1=q6 Pr ⊔ Submodule.span (ZMod 2) {q4 (q8 T_R u)} /\
  q4 res.2.2.2∈(U ⊔ Submodule.span (ZMod 2) {q4 u}) ⊓ q6 T_R /\
  (q4 (q8 T_R u)∈q6 Pr ->
   ∃ w:Fin m->ZMod 2,w∈U/\q4 u=q4 res.2.2.2+w /\
    q4 (q8 T_R u)∈q6 Pr):=by
 have hgo:∀ (k:ℕ) (hk:k ≤ m),
   let res:=((dF m).take k).foldl (fun s c=>qH c s) (Pr,Pl,q8 T_R u,u)
   Q3 res.1 /\
   (∀ c:Fin m,q4 (res.2.1 c)∈U ⊔ Submodule.span (ZMod 2) {q4 u}) /\
   (∀ c:Fin m,res.1 c=q8 T_R (res.2.1 c)) /\
   res.2.2.1=q8 T_R res.2.2.2 /\
   q4 res.2.2.2∈U ⊔ Submodule.span (ZMod 2) {q4 u} /\
   (∀ i:Fin m,i.val < k->res.2.2.1 i=false) /\
   q6 res.1 ⊔ Submodule.span (ZMod 2) {q4 res.2.2.1} =
    q6 Pr ⊔ Submodule.span (ZMod 2) {q4 (q8 T_R u)} /\
   (q4 (q8 T_R u)∈q6 Pr ->
    res.1=Pr/\res.2.1=Pl/\q4 u+q4 res.2.2.2∈U):=by
  intro k
  induction k with
  | zero=>
   intro _
   dsimp only
   rw [List.take_zero,List.foldl_nil]
   refine ⟨hPr,fun c=>Submodule.mem_sup_left (hPlU c),hRel,rfl,
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _),
    fun _ hi=>absurd hi (by omega),rfl,
    fun _=>⟨rfl,rfl,by rw [qM];exact Submodule.zero_mem _⟩⟩
  | succ k ih=>
   intro hk
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   obtain ⟨hE,hPlm,hRr,hrl,hlm,hlow,hsp,hinPr⟩:=ih (Nat.le_of_succ_le hk)
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF m).take k).foldl (fun s c=>qH c s) (Pr,Pl,q8 T_R u,u)
   set c:Fin m:=⟨k,hk⟩
   unfold qH
   by_cases hrc:st.2.2.1 c=true
   ·simp only [hrc,↓reduceIte]
    by_cases hPc:st.1 c c=true
    ·simp only [hPc,↓reduceIte]
     refine ⟨hE,hPlm,hRr,?_,?_,?_,?_,?_⟩
     ·rw [jc hR,← hrl,← hRr c]
     ·rw [qE];exact Submodule.add_mem _ hlm (hPlm c)
     ·intro i hi
      by_cases hlt:i.val < k
      ·have h1:=hlow i hlt
       have h2:st.1 c i=false:=by
        rcases hE c with h0 | ⟨_,hcl⟩
        ·rw [h0];rfl
        ·exact hcl i hlt
       simp [q5,h1,h2]
      ·have heq:i=c:=Fin.ext (by dsimp [c];omega)
       rw [heq];simp [q5,hrc,hPc]
     ·rw [← hsp]
      have hmem:q4 (st.1 c)∈q6 st.1:=Submodule.subset_span ⟨c,rfl⟩
      apply le_antisymm
      ·refine sup_le le_sup_left ?_
       rw [Submodule.span_singleton_le_iff_mem,qE]
       exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hmem)
      ·refine sup_le le_sup_left ?_
       rw [Submodule.span_singleton_le_iff_mem]
       have hEq:q4 st.2.2.1=q4 (q5 st.2.2.1 (st.1 c))+q4 (st.1 c):=by
        rw [qE,add_assoc,qM,add_zero]
       rw [hEq]
       exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hmem)
     ·intro huPr
      obtain ⟨h1,h2,h3⟩:=hinPr huPr
      refine ⟨h1,h2,?_⟩
      rw [qE,← add_assoc,h2]
      exact Submodule.add_mem _ h3 (hPlU c)
    ·simp only [hPc,Bool.false_eq_true,↓reduceIte]
     have hPc0:st.1 c=q2 m:=vS hE c (Bool.eq_false_iff.mpr hPc)
     refine ⟨?_,?_,?_,(yL hR).symm,by rw [qh];exact Submodule.zero_mem _,
      fun _ _=>rfl,?_,?_⟩
     ·intro j
      by_cases hjc:j=c
      ·subst hjc;right;rw [Function.update_self];exact ⟨hrc,hlow⟩
      ·rw [Function.update_of_ne hjc];exact hE j
     ·intro j
      by_cases hjc:j=c
      ·subst hjc;rw [Function.update_self];exact hlm
      ·rw [Function.update_of_ne hjc];exact hPlm j
     ·intro j
      by_cases hjc:j=c
      ·subst hjc;rw [Function.update_self,Function.update_self];exact hrl
      ·rw [Function.update_of_ne hjc,Function.update_of_ne hjc];exact hRr j
     ·rw [← hsp,qh,Submodule.span_zero_singleton,sup_bot_eq]
      apply le_antisymm
      ·rw [q6,Submodule.span_le]
       rintro _ ⟨j,rfl⟩
       dsimp only
       by_cases hjc:j=c
       ·subst hjc;rw [Function.update_self]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
       ·rw [Function.update_of_ne hjc]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨j,rfl⟩)
      ·refine sup_le ?_ ?_
       ·rw [q6,Submodule.span_le]
        rintro _ ⟨j,rfl⟩
        dsimp only
        by_cases hjc:j=c
        ·subst hjc;rw [hPc0,qh];exact Submodule.zero_mem _
        ·exact Submodule.subset_span ⟨j,by dsimp only;rw [Function.update_of_ne hjc]⟩
       ·rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span ⟨c,by dsimp only;rw [Function.update_self]⟩
     ·intro huPr
      exfalso
      obtain ⟨h1,_,_⟩:=hinPr huPr
      have hst_in:q4 st.2.2.1∈q6 Pr:=by
       have hle:Submodule.span (ZMod 2) {q4 st.2.2.1} ≤ q6 Pr:=by
        have h2:q6 st.1 ⊔ Submodule.span (ZMod 2) {q4 st.2.2.1}=q6 Pr:=by
         rw [hsp,sup_eq_left,Submodule.span_singleton_le_iff_mem];exact huPr
        rw [← h2];exact le_sup_right
       exact hle (Submodule.mem_span_singleton_self _)
      rw [← h1] at hst_in
      rw [jR hE,Submodule.mem_span_range_iff_exists_fun] at hst_in
      obtain ⟨g,hg⟩:=hst_in
      have hzc:∀ j:{j:Fin m // st.1 j j=true},j.1.val < k->g j=0:=by
       intro j hjk
       by_contra hnz
       let S:=Finset.univ.filter fun j':{j':Fin m // st.1 j' j'=true}=>j'.1.val < k/\g j' ≠ 0
       have hSne:S.Nonempty:=⟨j,Finset.mem_filter.mpr ⟨dL j,hjk,hnz⟩⟩
       let j0:=S.min' hSne
       have hj0m:=(Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
       have hj0_eq1:g j0=1:=yZ hj0m.2
       have hval:=congrFun hg j0.1
       simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hval
       have hlo0:q4 st.2.2.1 j0.1=0:=by simp [q4,hlow j0.1 hj0m.1]
       rw [hlo0] at hval
       have hoth:∀ j':{j':Fin m // st.1 j' j'=true},j' ≠ j0->g j'*q4 (st.1 j'.1) j0.1=0:=by
        intro j' hj'ne
        by_cases hgj:g j'=0
        ·rw [hgj,zero_mul]
        ·have hlt:j0.1.val < j'.1.val:=by
          by_cases hjk':j'.1.val < k
          ·have hle:j0 ≤ j':=Finset.min'_le S j' (Finset.mem_filter.mpr ⟨dL j',hjk',hgj⟩)
           have h1:j0.1.val ≤ j'.1.val:=hle
           have h2:j0.1.val ≠ j'.1.val:=fun e=>hj'ne (Subtype.ext (Fin.ext e)).symm
           omega
          ·have hj0k:j0.1.val < k:=hj0m.1;omega
         rcases hE j'.1 with h0 | ⟨_,hcl⟩
         ·rw [h0,qh];simp
         ·simp [q4,hcl j0.1 hlt]
       rw [Finset.sum_eq_single j0 (fun j' _ h=>hoth j' h) (fun h=>absurd (dL j0) h)] at hval
       rw [hj0_eq1,one_mul] at hval
       simp only [q4,j0.2,↓reduceIte] at hval
       exact one_ne_zero hval
      have hval:=congrFun hg c
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hval
      rw [show q4 st.2.2.1 c=1 by simp [q4,hrc]] at hval
      have hall0:∀ j:{j:Fin m // st.1 j j=true},g j*q4 (st.1 j.1) c=0:=by
       intro j
       by_cases hjk:j.1.val < k
       ·rw [hzc j hjk,zero_mul]
       ·have hne:j.1 ≠ c:=fun e=>hPc (e▸j.2)
        have hgt:c.val < j.1.val:=by
         have:j.1.val ≠ c.val:=fun e=>hne (Fin.ext e)
         dsimp [c] at this ⊢;omega
        rcases hE j.1 with h0 | ⟨_,hcl⟩
        ·rw [h0,qh];simp
        ·simp [q4,hcl c hgt]
      have hsum0:(∑ j:{j:Fin m // st.1 j j=true},g j*q4 (st.1 j.1) c)=0:=
       Finset.sum_eq_zero (fun j _=>hall0 j)
      rw [hsum0] at hval
      exact one_ne_zero hval.symm
   ·simp only [hrc,Bool.false_eq_true,↓reduceIte]
    refine ⟨hE,hPlm,hRr,hrl,hlm,?_,hsp,hinPr⟩
    intro i hi
    by_cases hlt:i.val < k
    ·exact hlow i hlt
    ·have heq:i=c:=Fin.ext (by dsimp [c];omega)
     rw [heq];exact Bool.eq_false_iff.mpr hrc
 obtain ⟨hE,hPlm,hRr,hrl,hlm,hlow,hsp,hinPr⟩:=hgo m le_rfl
 have htake:(dF m).take m=dF m:=by simp
 rw [htake] at hE hPlm hRr hrl hlm hlow hsp hinPr
 set res:=(dF m).foldl (fun s c=>qH c s) (Pr,Pl,q8 T_R u,u)
 have hr0:res.2.2.1=q2 m:=by funext i;exact hlow i i.isLt
 rw [hr0,qh,Submodule.span_zero_singleton,sup_bot_eq] at hsp
 have hl_in_R:q4 res.2.2.2∈q6 T_R:=
  (qG hR res.2.2.2).mp (hrl.symm.trans hr0)
 refine ⟨hE,hPlm,hRr,hsp,⟨hlm,hl_in_R⟩,fun huPr=>?_⟩
 obtain ⟨_,_,hdiff⟩:=hinPr huPr
 refine ⟨q4 u+q4 res.2.2.2,hdiff,?_,huPr⟩
 calc q4 u=q4 res.2.2.2+(q4 u+q4 res.2.2.2):=by rw [add_comm (q4 u),← add_assoc,qM,zero_add]
lemma jW {m:ℕ} (T_L T_R:Q6 m) (hR:Q3 T_R) :
  let res:=vv T_L T_R
  Q3 res.1/\Q3 res.2.2 /\
  (∀ c:Fin m,q4 (res.2.1 c)∈q6 T_L/\res.1 c=q8 T_R (res.2.1 c)) /\
  q6 res.2.2=q6 T_L ⊓ q6 T_R /\
  (∀ v:Q1 m,q4 v∈q6 T_L->q4 (q8 T_R v)∈q6 res.1):=by
 let U (k:ℕ):Submodule (ZMod 2) (Fin m->ZMod 2):=
  Submodule.span (ZMod 2) (((dF m).take k).map (fun i=>q4 (T_L i)) |>.toFinset:Set (Fin m->ZMod 2))
 have hgo:∀ (k:ℕ) (hk:k ≤ m),
   let res:=((dF m).take k).foldl (fun st i=>y3 T_R st (T_L i))
    (qN m,qN m,qN m)
   Q3 res.1/\Q3 res.2.2 /\
   (∀ c:Fin m,q4 (res.2.1 c)∈U k/\res.1 c=q8 T_R (res.2.1 c)) /\
   q6 res.2.2=U k ⊓ q6 T_R /\
   (∀ v:Q1 m,q4 v∈U k->q4 (q8 T_R v)∈q6 res.1):=by
  intro k
  induction k with
  | zero=>
   intro _
   dsimp only
   rw [List.take_zero,List.foldl_nil]
   have hU0:U 0=⊥:=by simp [U]
   refine ⟨jE m,jE m,
    fun _=>⟨by dsimp only [qN];rw [qh];exact Submodule.zero_mem _,(yL hR).symm⟩,
    by rw [y6,hU0,bot_inf_eq],
    fun v hv=>by
     rw [hU0,Submodule.mem_bot] at hv
     have hv0:v=q2 m:=v7 (hv.trans (qh m).symm)
     rw [hv0,yL hR,qh];exact Submodule.zero_mem _⟩
  | succ k ih=>
   intro hk
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   have hUsucc:U (k+1)=U k ⊔ Submodule.span (ZMod 2) {q4 (T_L ⟨k,hk⟩)}:=by
    simp only [U,htake,List.map_append,List.map_singleton,List.toFinset_append,
     List.toFinset_cons,List.toFinset_nil,Finset.coe_union,Finset.coe_insert,
     Finset.coe_empty,Submodule.span_union]
    congr 2
    ext v;simp
   obtain ⟨hPr,hTi,hRel,hInt,hIm⟩:=ih (Nat.le_of_succ_le hk)
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF m).take k).foldl (fun st i=>y3 T_R st (T_L i))
    (qN m,qN m,qN m)
   set u:=T_L ⟨k,hk⟩
   have hpair:=zq T_R hR (U k) st.1 st.2.1 hPr
    (fun c=>(hRel c).1) (fun c=>(hRel c).2) u
   obtain ⟨hPr',hPl',hRel',hSpPr',hInInt',hInPr'⟩:=hpair
   unfold y3
   set pres:=(dF m).foldl (fun s c=>qH c s) (st.1,st.2.1,q8 T_R u,u)
   obtain ⟨hTi',hSpTi'⟩:=jG st.2.2 hTi pres.2.2.2
   have hIm':∀ v:Q1 m,q4 v∈U (k+1)->q4 (q8 T_R v)∈q6 pres.1:=by
    intro v hv
    rw [hUsucc,Submodule.mem_sup] at hv
    obtain ⟨w,hw,z,hz,hvwz⟩:=hv
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨α,rfl⟩:=hz
    have hw_vec:∃ wb:Q1 m,q4 wb=w:=
     ⟨fun i=>decide (w i=1),by
      funext i;simp only [q4]
      rcases qD (w i) with hc | hc <;> simp [hc]⟩
    obtain ⟨wb,rfl⟩:=hw_vec
    rcases qD α with rfl | rfl
    ·simp only [zero_smul,add_zero] at hvwz
     have hveq:v=wb:=v7 hvwz.symm
     rw [hveq,hSpPr']
     exact Submodule.mem_sup_left (hIm wb hw)
    ·simp only [one_smul] at hvwz
     have hveq:v=q5 wb u:=v7 (hvwz.symm.trans (qE wb u).symm)
     rw [hveq,jc hR,qE,hSpPr']
     exact Submodule.add_mem _ (Submodule.mem_sup_left (hIm wb hw))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
   have hInt':q6 (qC st.2.2 pres.2.2.2)=U (k+1) ⊓ q6 T_R:=by
    rw [hSpTi',hInt,hUsucc]
    apply le_antisymm
    ·refine sup_le ?_ ?_
     ·exact inf_le_inf_right _ le_sup_left
     ·rw [Submodule.span_singleton_le_iff_mem];exact hInInt'
    ·intro x ⟨hxU,hxR⟩
     rw [SetLike.mem_coe,Submodule.mem_sup] at hxU
     rw [SetLike.mem_coe] at hxR
     obtain ⟨w,hw,z,hz,hwx⟩:=hxU
     rw [Submodule.mem_span_singleton] at hz
     obtain ⟨α,rfl⟩:=hz
     rcases qD α with rfl | rfl
     ·simp only [zero_smul,add_zero] at hwx
      subst hwx
      exact Submodule.mem_sup_left ⟨hw,hxR⟩
     ·simp only [one_smul] at hwx
      have hw_vec:∃ wb:Q1 m,q4 wb=w:=
       ⟨fun i=>decide (w i=1),by
        funext i;simp only [q4]
        rcases qD (w i) with hc | hc <;> simp [hc]⟩
      obtain ⟨wb,rfl⟩:=hw_vec
      have hxor_in:q4 (q5 wb u)∈q6 T_R:=by
       rw [qE,hwx];exact hxR
      have hred0:q8 T_R (q5 wb u)=q2 m:=
       (qG hR _).mpr hxor_in
      have hred_eq:q8 T_R u=q8 T_R wb:=by
       rw [jc hR] at hred0
       exact v7 ((yX _ _).mpr (by
        rw [add_comm,← qE,hred0,qh]))
      have hu_in_Pr:q4 (q8 T_R u)∈q6 st.1:=by
       rw [hred_eq];exact hIm wb hw
      obtain ⟨w',hw'U,hu_eq,_⟩:=hInPr' hu_in_Pr
      have hx_eq:x=(q4 wb+w')+q4 pres.2.2.2:=by
       rw [← hwx,hu_eq];abel
      rw [hx_eq]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨Submodule.add_mem _ hw hw'U,?_⟩)
       (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      have h1:q4 wb+w'=x+q4 pres.2.2.2:=by
       rw [hx_eq,add_assoc,qM,add_zero]
      rw [h1]
      exact Submodule.add_mem _ hxR hInInt'.2
   refine ⟨hPr',hTi',fun c=>⟨hUsucc▸hPl' c,hRel' c⟩,hInt',hIm'⟩
 have h:=hgo m le_rfl
 have htake:(dF m).take m=dF m:=by simp
 have hUm:U m=q6 T_L:=by
  unfold U q6
  rw [htake]
  congr 1
  ext v
  simp only [Finset.mem_coe,List.mem_toFinset,List.mem_map,List.mem_finRange,true_and,Set.mem_range]
 rw [htake,hUm] at h
 exact h
lemma gj {m:ℕ} (T_L T_R:Q6 m) (hR:Q3 T_R) (y:Q1 m) :
  let ib:=vv T_L T_R
  let res:=zs ib.1 ib.2.1 T_R y
  (res.1=true ↔ q4 y∈q6 T_L ⊔ q6 T_R) /\
  (res.1=true->q4 res.2∈q6 T_L/\q4 res.2+q4 y∈q6 T_R):=by
 obtain ⟨hPr,_,hRel,_,hIm⟩:=jW T_L T_R hR
 set Pr:=(vv T_L T_R).1
 set Pl:=(vv T_L T_R).2.1
 have hgo:∀ (k:ℕ) (hk:k ≤ m),
   let st:=((dF m).take k).foldl (fun st c=>jb Pr Pl c st) (q8 T_R y,q2 m)
   q4 st.2∈q6 T_L /\
   st.1=q8 T_R (q5 st.2 y) /\
   (∀ c:Fin m,c.val < k->Pr c c=true->st.1 c=false):=by
  intro k
  induction k with
  | zero=>
   intro _
   dsimp only
   rw [List.take_zero,List.foldl_nil]
   refine ⟨by rw [qh];exact Submodule.zero_mem _,?_,fun _ hi=>absurd hi (by omega)⟩
   have h0:q5 (q2 m) y=y:=by funext i;simp [q5,q2]
   rw [h0]
  | succ k ih=>
   intro hk
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   obtain ⟨hlm,hst1,hpiv⟩:=ih (Nat.le_of_succ_le hk)
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF m).take k).foldl (fun st c=>jb Pr Pl c st) (q8 T_R y,q2 m)
   set c:Fin m:=⟨k,hk⟩
   unfold jb
   by_cases hcond:st.1 c=true/\Pr c c=true
   ·simp only [hcond,and_self,↓reduceIte]
    refine ⟨?_,?_,?_⟩
    ·rw [qE];exact Submodule.add_mem _ hlm (hRel c).1
    ·have h1:q5 (q5 st.2 (Pl c)) y=q5 (q5 st.2 y) (Pl c):=by
      funext i;simp only [q5];cases st.2 i <;> cases Pl c i <;> cases y i <;> decide
     rw [h1,jc hR,← hst1,← (hRel c).2]
    ·intro j hj hPj
     by_cases hlt:j.val < k
     ·have h1:=hpiv j hlt hPj
      have h2:Pr c j=false:=by
       rcases hPr c with h0 | ⟨_,hcl⟩
       ·rw [h0];rfl
       ·exact hcl j hlt
      simp [q5,h1,h2]
     ·have heq:j=c:=Fin.ext (by dsimp [c];omega)
      rw [heq];simp [q5,hcond.1,hcond.2]
   ·simp only [hcond,↓reduceIte]
    refine ⟨hlm,hst1,?_⟩
    intro j hj hPj
    by_cases hlt:j.val < k
    ·exact hpiv j hlt hPj
    ·have heq:j=c:=Fin.ext (by dsimp [c];omega)
     rw [heq] at hPj ⊢
     exact Bool.eq_false_iff.mpr fun h=>hcond ⟨h,hPj⟩
 obtain ⟨hlm,hst1,hpiv⟩:=hgo m le_rfl
 have htake:(dF m).take m=dF m:=by simp
 rw [htake] at hlm hst1 hpiv
 set res:=(dF m).foldl (fun st c=>jb Pr Pl c st) (q8 T_R y,q2 m)
 dsimp only [zs]
 have hiff:res.1=q2 m ↔ q4 y∈q6 T_L ⊔ q6 T_R:=by
  constructor
  ·intro h0
   have hinR:q4 (q5 res.2 y)∈q6 T_R:=
    (qG hR _).mp (hst1.symm.trans h0)
   have hy:q4 y=q4 res.2+q4 (q5 res.2 y):=by
    rw [qE,← add_assoc,qM,zero_add]
   rw [hy]
   exact Submodule.add_mem _ (Submodule.mem_sup_left hlm) (Submodule.mem_sup_right hinR)
  ·intro hy
   rw [Submodule.mem_sup] at hy
   obtain ⟨wL,hwL,wR,hwR,hsum⟩:=hy
   have hwL_vec:∃ wb:Q1 m,q4 wb=wL:=
    ⟨fun i=>decide (wL i=1),by
     funext i;simp only [q4]
     rcases qD (wL i) with hc | hc <;> simp [hc]⟩
   obtain ⟨wb,rfl⟩:=hwL_vec
   have hdiffR:q4 (q5 wb y)∈q6 T_R:=by
    rw [qE,← hsum,← add_assoc,qM,zero_add];exact hwR
   have hred_eq:q8 T_R y=q8 T_R wb:=by
    have h0:=(qG hR _).mpr hdiffR
    rw [jc hR] at h0
    exact v7 ((yX _ _).mpr (by rw [add_comm,← qE,h0,qh]))
   have hres1_in:q4 res.1∈q6 Pr:=by
    rw [hst1,jc hR,hred_eq,← jc hR]
    exact hIm (q5 res.2 wb) (by rw [qE];exact Submodule.add_mem _ hlm hwL)
   have hres1_0:q4 res.1=0:=
    vZ hPr hres1_in fun c hc=>by simp [q4,hpiv c c.isLt hc]
   exact v7 (hres1_0.trans (qh m).symm)
 constructor
 ·simp only [dG];exact hiff
 ·intro h1
  simp only [dG] at h1
  refine ⟨hlm,?_⟩
  have hinR:q4 (q5 res.2 y)∈q6 T_R:=
   (qG hR _).mp (hst1.symm.trans h1)
  rwa [qE] at hinR
structure Q8 (nIn:ℕ) (c:CB nIn) (m:ℕ) (f:(Fin nIn->Bool)->Q6 m) where
 rows:∀ i:Fin m,Q2 nIn c m (fun x=>f x i)
def Q8.lift {nIn:ℕ} {c c':CB nIn} {m:ℕ} {f:(Fin nIn->Bool)->Q6 m}
  (hext:c.Qa c') (T:Q8 nIn c m f):Q8 nIn c' m f:=
 ⟨fun i=>(T.rows i).lift hext⟩
def Q8.cast {nIn:ℕ} {c:CB nIn} {m:ℕ} {f g:(Fin nIn->Bool)->Q6 m}
  (h:∀ x,f x=g x) (T:Q8 nIn c m f):Q8 nIn c m g:=
 ⟨fun i=>(T.rows i).cast fun x j=>by rw [h x]⟩
def y0 {nIn:ℕ} (c:CB nIn) (m:ℕ) :
  Q0 nIn c (m*(m*1)) (fun c'=>Q8 nIn c' m (fun _=>qN m)):=by
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=
  ∀ i:Fin m,i.val < k->Q2 nIn c1 m (fun _=>q2 m)
 have hfold:=Q0.qe (Bstep:=m*1) m Acc c (fun _ hi=>absurd hi (by omega))
  (fun k hk c1 _ acc=>
   (vq c1 m (q2 m)).bind fun c2 h2 vrow=>
   Q0.pure fun i hi=>
    if hlt:i.val < k then (acc i hlt).lift h2 else vrow)
 exact ⟨hfold.c',hfold.ext,hfold.hsize,⟨fun i=>hfold.val i i.isLt⟩⟩
def jD {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {fT:(Fin nIn->Bool)->Q6 m} {fv:(Fin nIn->Bool)->Q1 m}
  (T:Q8 nIn c m fT) (v:Q2 nIn c m fv) :
  Q0 nIn c (m*1+m*(16*m+4)) (fun c'=>Q8 nIn c' m (fun x=>qC (fT x) (fv x))):=
 Q0.weaken (by omega)<|
 (vq c m (q2 m)).bind fun c0 h0 vzero=>
 let stAt (k:ℕ) (x:Fin nIn->Bool):Q6 m × Q1 m:=
  ((dF m).take k).foldl (fun st c=>je c st) (fT x,fv x)
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=
  Q8 nIn c1 m (fun x=>(stAt k x).1) × Q2 nIn c1 m (fun x=>(stAt k x).2)
 have hinit:Acc 0 (Nat.zero_le m) c0:=
  ⟨(T.lift h0).cast (fun _=>rfl),(v.lift h0).cast (fun _ _=>rfl)⟩
 (Q0.qe (Bstep:=16*m+4) m Acc c0 hinit fun k hk c1 h1 ⟨Tc,vc⟩=>
  Q0.weaken (by omega)<|
  let ci:Fin m:=⟨k,hk⟩
  let vbit:=vc.at ci
  let haspiv:=(Tc.rows ci).at ci
  (vg c1 vbit haspiv).bind fun c2 h2 vxorCond=>
  (y2 c2 (haspiv.lift h2)).bind fun c3 h3 vnoPiv=>
  (vg c3 (vbit.lift (CB.q0 h2 h3)) vnoPiv).bind fun c4 h4 vinstCond=>
  (j3 c4 (vc.lift (CB.q0 h2 (CB.q0 h3 h4)))
   ((Tc.rows ci).lift (CB.q0 h2 (CB.q0 h3 h4)))).bind fun c5 h5 vxor=>
  let h15:=CB.q0 h2 (CB.q0 h3 (CB.q0 h4 h5))
  (vd c5 (vxorCond.lift (CB.q0 h3 (CB.q0 h4 h5))) vxor (vc.lift h15)).bind fun c6 h6 v1=>
  (vd c6 (vinstCond.lift (CB.q0 h5 h6))
   (vzero.lift (CB.q0 h1 (CB.q0 h15 h6))) v1).bind fun c7 h7 vnew=>
  (vd c7 (vinstCond.lift (CB.q0 h5 (CB.q0 h6 h7)))
   (vc.lift (CB.q0 h15 (CB.q0 h6 h7)))
   ((Tc.rows ci).lift (CB.q0 h15 (CB.q0 h6 h7)))).bind fun c8 h8 rowNew=>
  let hall:=CB.q0 h15 (CB.q0 h6 (CB.q0 h7 h8))
  have htake:(dF m).take (k+1)=(dF m).take k ++ [ci]:=by
   rw [dJ (by simp;omega)];simp [ci]
  have hstep:∀ x,stAt (k+1) x=je ci (stAt k x):=fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨⟨fun r=>
     if hr:r=ci then
      (hr▸rowNew).cast fun x j=>by
       subst hr
       rw [hstep x];unfold je
       by_cases hvc:(stAt k x).2 ci=true <;> by_cases htc:(stAt k x).1 ci ci=true <;>
        simp [hvc,htc]
     else
      ((Tc.rows r).lift hall).cast fun x j=>by
       rw [hstep x];unfold je
       by_cases hvc:(stAt k x).2 ci=true <;> by_cases htc:(stAt k x).1 ci ci=true <;>
        simp [hvc,htc,Function.update_of_ne hr]⟩,
   (vnew.lift h8).cast fun x j=>by
     rw [hstep x];unfold je
     by_cases hvc:(stAt k x).2 ci=true <;> by_cases htc:(stAt k x).1 ci ci=true <;>
      simp [q5,hvc,htc]⟩).bind fun cF _ ⟨TF,_⟩=>
 Q0.pure<|TF.cast fun x=>by
  simp only [stAt,qC]
  have ht:(dF m).take m=dF m:=by simp
  rw [ht]
def yR {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {fT:(Fin nIn->Bool)->Q6 m} {fv:(Fin nIn->Bool)->Q1 m}
  (T:Q8 nIn c m fT) (v:Q2 nIn c m fv) :
  Q0 nIn c (m*(8*m+1)) (fun c'=>Q2 nIn c' m (fun x=>q8 (fT x) (fv x))):=
 Q0.weaken (by omega)<|
 let stAt (k:ℕ) (x:Fin nIn->Bool):Q1 m:=
  ((dF m).take k).foldl (fun acc c=>jd (fT x) c acc) (fv x)
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=Q2 nIn c1 m (stAt k)
 have hinit:Acc 0 (Nat.zero_le m) c:=v.cast (fun _ _=>rfl)
 (Q0.qe (Bstep:=8*m+1) m Acc c hinit fun k hk c1 h1 vc=>
  Q0.weaken (by omega)<|
  let ci:Fin m:=⟨k,hk⟩
  let Trow:=(T.rows ci).lift h1
  (vg c1 (vc.at ci) (Trow.at ci)).bind fun c2 h2 vcond=>
  (j3 c2 (vc.lift h2) (Trow.lift h2)).bind fun c3 h3 vxor=>
  (vd c3 (vcond.lift h3) vxor (vc.lift (CB.q0 h2 h3))).bind fun _ _ vnew=>
  have htake:(dF m).take (k+1)=(dF m).take k ++ [ci]:=by
   rw [dJ (by simp;omega)];simp [ci]
  have hstep:∀ x,stAt (k+1) x=jd (fT x) ci (stAt k x):=fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure<|vnew.cast fun x j=>by
   rw [hstep x];unfold jd
   by_cases h1':stAt k x ci=true <;> by_cases h2':fT x ci ci=true <;> simp [q5,h1',h2']).bind fun _ _ vF=>
 Q0.pure<|vF.cast fun x j=>by
  simp only [stAt,q8]
  have ht:(dF m).take m=dF m:=by simp
  rw [ht]
def d8 {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {fPr fPl:(Fin nIn->Bool)->Q6 m} {fr fl:(Fin nIn->Bool)->Q1 m}
  (Pr:Q8 nIn c m fPr) (Pl:Q8 nIn c m fPl)
  (r:Q2 nIn c m fr) (l:Q2 nIn c m fl) :
  Q0 nIn c (m*1+m*(32*m+4))
   (fun c'=>
    let res:=fun x=>(dF m).foldl (fun s c=>qH c s) (fPr x,fPl x,fr x,fl x)
    Q8 nIn c' m (fun x=>(res x).1) × Q8 nIn c' m (fun x=>(res x).2.1) ×
    Q2 nIn c' m (fun x=>(res x).2.2.2)):=
 Q0.weaken (by omega)<|
 (vq c m (q2 m)).bind fun c0 h0 vzero=>
 let stAt (k:ℕ) (x:Fin nIn->Bool):Q6 m × Q6 m × Q1 m × Q1 m:=
  ((dF m).take k).foldl (fun s c=>qH c s) (fPr x,fPl x,fr x,fl x)
 let Acc (k:ℕ) (_:k ≤ m) (c1:CB nIn):Type:=
  Q8 nIn c1 m (fun x=>(stAt k x).1) × Q8 nIn c1 m (fun x=>(stAt k x).2.1) ×
  Q2 nIn c1 m (fun x=>(stAt k x).2.2.1) × Q2 nIn c1 m (fun x=>(stAt k x).2.2.2)
 have hinit:Acc 0 (Nat.zero_le m) c0:=
  ⟨(Pr.lift h0).cast (fun _=>rfl),(Pl.lift h0).cast (fun _=>rfl),
  (r.lift h0).cast (fun _ _=>rfl),(l.lift h0).cast (fun _ _=>rfl)⟩
 (Q0.qe (Bstep:=32*m+4) m Acc c0 hinit fun k hk c1 h1 ⟨Prc,Plc,rc,lc⟩=>
  Q0.weaken (by omega)<|
  let ci:Fin m:=⟨k,hk⟩
  let rbit:=rc.at ci
  let haspiv:=(Prc.rows ci).at ci
  (vg c1 rbit haspiv).bind fun c2 h2 vxorCond=>
  (y2 c2 (haspiv.lift h2)).bind fun c3 h3 vnoPiv=>
  (vg c3 (rbit.lift (CB.q0 h2 h3)) vnoPiv).bind fun c4 h4 vinstCond=>
  let h14:=CB.q0 h2 (CB.q0 h3 h4)
  (j3 c4 (rc.lift h14) ((Prc.rows ci).lift h14)).bind fun c5 h5 rxor=>
  (j3 c5 (lc.lift (CB.q0 h14 h5)) ((Plc.rows ci).lift (CB.q0 h14 h5))).bind fun c6 h6 lxor=>
  let h16:=CB.q0 h14 (CB.q0 h5 h6)
  (vd c6 (vxorCond.lift (CB.q0 h3 (CB.q0 h4 (CB.q0 h5 h6)))) (rxor.lift h6) (rc.lift h16)).bind fun c7 h7 r1=>
  (vd c7 (vinstCond.lift (CB.q0 h5 (CB.q0 h6 h7)))
   (vzero.lift (CB.q0 h1 (CB.q0 h16 h7))) r1).bind fun c8 h8 rnew=>
  let h68:=CB.q0 h7 h8
  (vd c8 (vxorCond.lift (CB.q0 h3 (CB.q0 h4 (CB.q0 h5 (CB.q0 h6 h68)))))
   (lxor.lift h68) (lc.lift (CB.q0 h16 h68))).bind fun c9 h9 l1=>
  (vd c9 (vinstCond.lift (CB.q0 h5 (CB.q0 h6 (CB.q0 h68 h9))))
   (vzero.lift (CB.q0 h1 (CB.q0 h16 (CB.q0 h68 h9)))) l1).bind fun c10 h10 lnew=>
  let h1_10:=CB.q0 h16 (CB.q0 h68 (CB.q0 h9 h10))
  let h4_10:=CB.q0 h5 (CB.q0 h6 (CB.q0 h68 (CB.q0 h9 h10)))
  (vd c10 (vinstCond.lift h4_10) (rc.lift h1_10) ((Prc.rows ci).lift h1_10)).bind fun c11 h11 PrRow=>
  (vd c11 (vinstCond.lift (CB.q0 h4_10 h11)) (lc.lift (CB.q0 h1_10 h11))
   ((Plc.rows ci).lift (CB.q0 h1_10 h11))).bind fun c12 h12 PlRow=>
  let hall:=CB.q0 h1_10 (CB.q0 h11 h12)
  have htake:(dF m).take (k+1)=(dF m).take k ++ [ci]:=by
   rw [dJ (by simp;omega)];simp [ci]
  have hstep:∀ x,stAt (k+1) x=qH ci (stAt k x):=fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨⟨fun row=>
     if hr:row=ci then
      (hr▸(PrRow.lift h12)).cast fun x j=>by
       subst hr
       rw [hstep x];unfold qH
       by_cases hrc:(stAt k x).2.2.1 ci=true <;> by_cases hpc:(stAt k x).1 ci ci=true <;> simp [hrc,hpc]
     else
      ((Prc.rows row).lift hall).cast fun x j=>by
       rw [hstep x];unfold qH
       by_cases hrc:(stAt k x).2.2.1 ci=true <;> by_cases hpc:(stAt k x).1 ci ci=true <;>
        simp [hrc,hpc,Function.update_of_ne hr]⟩,
   ⟨fun row=>
     if hr:row=ci then
      (hr▸PlRow).cast fun x j=>by
       subst hr
       rw [hstep x];unfold qH
       by_cases hrc:(stAt k x).2.2.1 ci=true <;> by_cases hpc:(stAt k x).1 ci ci=true <;> simp [hrc,hpc]
     else
      ((Plc.rows row).lift hall).cast fun x j=>by
       rw [hstep x];unfold qH
       by_cases hrc:(stAt k x).2.2.1 ci=true <;> by_cases hpc:(stAt k x).1 ci ci=true <;>
        simp [hrc,hpc,Function.update_of_ne hr]⟩,
   (rnew.lift (CB.q0 h9 (CB.q0 h10 (CB.q0 h11 h12)))).cast fun x j=>by
     rw [hstep x];unfold qH
     by_cases hrc:(stAt k x).2.2.1 ci=true <;> by_cases hpc:(stAt k x).1 ci ci=true <;> simp [q5,hrc,hpc],
   (lnew.lift (CB.q0 h11 h12)).cast fun x j=>by
     rw [hstep x];unfold qH
     by_cases hrc:(stAt k x).2.2.1 ci=true <;> by_cases hpc:(stAt k x).1 ci ci=true <;> simp [q5,hrc,hpc]⟩).bind fun _ _ ⟨PrF,PlF,_,lF⟩=>
 Q0.pure
  ⟨PrF.cast fun x=>by simp only [stAt];rw [show (dF m).take m=dF m by simp],
  PlF.cast fun x=>by simp only [stAt];rw [show (dF m).take m=dF m by simp],
  lF.cast fun x j=>by simp only [stAt];rw [show (dF m).take m=dF m by simp]⟩
def yA {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {fL fR:(Fin nIn->Bool)->Q6 m}
  (T_L:Q8 nIn c m fL) (T_R:Q8 nIn c m fR) :
  Q0 nIn c (3*(m*m)+m*(56*m*m+11*m))
   (fun c'=>
    Q8 nIn c' m (fun x=>(vv (fL x) (fR x)).1) ×
    Q8 nIn c' m (fun x=>(vv (fL x) (fR x)).2.1) ×
    Q8 nIn c' m (fun x=>(vv (fL x) (fR x)).2.2)):=
 Q0.weaken (by nlinarith)<|
 (y0 c m).bind fun c0 h0 zPr=>
 (y0 c0 m).bind fun c1 h1 zPl=>
 (y0 c1 m).bind fun c2 h2 zTi=>
 let h02:=CB.q0 h0 (CB.q0 h1 h2)
 let stAt (k:ℕ) (x:Fin nIn->Bool):Q6 m × Q6 m × Q6 m:=
  ((dF m).take k).foldl (fun st i=>y3 (fR x) st (fL x i))
   (qN m,qN m,qN m)
 let Acc (k:ℕ) (_:k ≤ m) (c3:CB nIn):Type:=
  Q8 nIn c3 m (fun x=>(stAt k x).1) ×
  Q8 nIn c3 m (fun x=>(stAt k x).2.1) ×
  Q8 nIn c3 m (fun x=>(stAt k x).2.2)
 have hinit:Acc 0 (Nat.zero_le m) c2:=
  ⟨(zPr.lift (CB.q0 h1 h2)).cast (fun _=>rfl),
  (zPl.lift h2).cast (fun _=>rfl),
  zTi.cast (fun _=>rfl)⟩
 (Q0.qe (Bstep:=56*m*m+11*m) m Acc c2 hinit fun k hk c3 h3 ⟨Prc,Plc,Tic⟩=>
  Q0.weaken (by nlinarith)<|
  let h03:=CB.q0 h02 h3
  let u:=(T_L.rows ⟨k,hk⟩).lift h03
  (yR c3 (T_R.lift h03) u).bind fun c4 h4 r0=>
  (d8 c4 (Prc.lift h4) (Plc.lift h4) r0 (u.lift h4)).bind fun c5 h5 ⟨Pr',Pl',lrem⟩=>
  (jD c5 (Tic.lift (CB.q0 h4 h5)) lrem).bind fun c6 h6 Ti'=>
  have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
   rw [dJ (by simp;omega)];simp
  Q0.pure
   ⟨(Pr'.lift h6).cast fun x=>by
     simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,y3],
   (Pl'.lift h6).cast fun x=>by
     simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,y3],
   Ti'.cast fun x=>by
     simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,y3]⟩).bind fun _ _ ⟨PrF,PlF,TiF⟩=>
 Q0.pure
  ⟨PrF.cast fun x=>by simp only [stAt,vv];rw [show (dF m).take m=dF m by simp],
  PlF.cast fun x=>by simp only [stAt,vv];rw [show (dF m).take m=dF m by simp],
  TiF.cast fun x=>by simp only [stAt,vv];rw [show (dF m).take m=dF m by simp]⟩
def dd {nIn:ℕ} (c:CB nIn) {m:ℕ}
  {fPr fPl fR:(Fin nIn->Bool)->Q6 m} {fy:(Fin nIn->Bool)->Q1 m}
  (Pr:Q8 nIn c m fPr) (Pl:Q8 nIn c m fPl) (T_R:Q8 nIn c m fR)
  (y:Q2 nIn c m fy) :
  Q0 nIn c (24*m*m+10*m+2)
   (fun c'=>
    Q4 nIn c' (fun x=>(zs (fPr x) (fPl x) (fR x) (fy x)).1) ×
    Q2 nIn c' m (fun x=>(zs (fPr x) (fPl x) (fR x) (fy x)).2)):=
 Q0.weaken (by nlinarith)<|
 (vq c m (q2 m)).bind fun c0 h0 vzero=>
 (yR c0 (T_R.lift h0) (y.lift h0)).bind fun c1 h1 r0=>
 let stAt (k:ℕ) (x:Fin nIn->Bool):Q1 m × Q1 m:=
  ((dF m).take k).foldl (fun st c=>jb (fPr x) (fPl x) c st)
   (q8 (fR x) (fy x),q2 m)
 let Acc (k:ℕ) (_:k ≤ m) (c2:CB nIn):Type:=
  Q2 nIn c2 m (fun x=>(stAt k x).1) × Q2 nIn c2 m (fun x=>(stAt k x).2)
 have hinit:Acc 0 (Nat.zero_le m) c1:=
  ⟨r0.cast (fun _ _=>rfl),(vzero.lift h1).cast (fun _ _=>rfl)⟩
 (Q0.qe (Bstep:=16*m+1) m Acc c1 hinit fun k hk c2 h2 ⟨rc,lc⟩=>
  Q0.weaken (by omega)<|
  let ci:Fin m:=⟨k,hk⟩
  let h02:=CB.q0 h0 (CB.q0 h1 h2)
  let PrRow:=(Pr.rows ci).lift h02
  let PlRow:=(Pl.rows ci).lift h02
  (vg c2 (rc.at ci) (PrRow.at ci)).bind fun c3 h3 vcond=>
  (j3 c3 (rc.lift h3) (PrRow.lift h3)).bind fun c4 h4 rxor=>
  (j3 c4 (lc.lift (CB.q0 h3 h4)) (PlRow.lift (CB.q0 h3 h4))).bind fun c5 h5 lxor=>
  (vd c5 (vcond.lift (CB.q0 h4 h5)) (rxor.lift h5) (rc.lift (CB.q0 h3 (CB.q0 h4 h5)))).bind fun c6 h6 rnew=>
  (vd c6 (vcond.lift (CB.q0 h4 (CB.q0 h5 h6))) (lxor.lift h6)
   (lc.lift (CB.q0 h3 (CB.q0 h4 (CB.q0 h5 h6))))).bind fun c7 h7 lnew=>
  have htake:(dF m).take (k+1)=(dF m).take k ++ [ci]:=by
   rw [dJ (by simp;omega)];simp [ci]
  have hstep:∀ x,stAt (k+1) x=jb (fPr x) (fPl x) ci (stAt k x):=fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨(rnew.lift h7).cast fun x j=>by
     rw [hstep x];unfold jb
     by_cases h1':(stAt k x).1 ci=true <;> by_cases h2':fPr x ci ci=true <;> simp [q5,h1',h2'],
   lnew.cast fun x j=>by
     rw [hstep x];unfold jb
     by_cases h1':(stAt k x).1 ci=true <;> by_cases h2':fPr x ci ci=true <;> simp [q5,h1',h2']⟩).bind fun cF hF ⟨rF,lF⟩=>
 (gF cF rF (vzero.lift (CB.q0 h1 hF))).bind fun cG hG vok=>
 Q0.pure
  ⟨vok.cast fun x=>by
    have hfold:(stAt m x).1 =
      ((dF m).foldl (fun st c=>jb (fPr x) (fPl x) c st)
       (q8 (fR x) (fy x),q2 m)).1:=by
     simp only [stAt,show (dF m).take m=dF m by simp]
    simp only [zs,hfold],
  (lF.lift hG).cast fun x j=>by
    simp only [stAt,zs]
    rw [show (dF m).take m=dF m by simp]⟩
def dv {nIn:ℕ} (c:CB nIn) {m W:ℕ} (hW:1 ≤ W) (hmW:m < 2^W)
  {fT:(Fin nIn->Bool)->Q6 m} (T:Q8 nIn c m fT) :
  Q0 nIn c (W*2+m*(1+W*15)) (fun c'=>Q9 nIn c' W (fun x=>q3 (fT x))):=
 let diag:Q2 nIn c m (fun x i=>fT x i i):=
  ⟨fun i=>(T.rows i).ws i,fun i=>(T.rows i).hws i,fun x i=>(T.rows i).heval x i⟩
 gP c hW hmW diag
end GF2LinAlg
section PlanMath
def yy (r:ℕ) (col:Bool):ℕ:=
 if col then 7*r - 2 else 5*r - 3
def vo (r:ℕ) (col:Bool):ℕ:=
 if col then 3*r+1 else 2*r - 2
def jh {k:ℕ} (hk:0 < k) (j:Fin k):Fin k:=
 ⟨(j.val+k - 1) % k,Nat.mod_lt _ hk⟩
def d5 {k:ℕ} (hk:0 < k) (j:Fin k):Fin k:=
 ⟨(j.val+1) % k,Nat.mod_lt _ hk⟩
lemma gp {k:ℕ} (hk:0 < k) (j:Fin k):d5 hk (jh hk j)=j:=by
 apply Fin.ext
 dsimp only [d5,jh]
 by_cases hj:j.val=0
 ·have h1:(j.val+k - 1) % k=k - 1:=by
   rw [hj,zero_add,Nat.mod_eq_of_lt (by omega)]
  rw [h1,Nat.sub_add_cancel hk,Nat.mod_self,hj]
 ·have h1:(j.val+k - 1) % k=j.val - 1:=by
   have h2:j.val+k - 1=(j.val - 1)+k:=by omega
   rw [h2,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  rw [h1,Nat.sub_add_cancel (by omega),Nat.mod_eq_of_lt j.isLt]
lemma gq {k:ℕ} (hk:0 < k) (j:Fin k):jh hk (d5 hk j)=j:=by
 apply Fin.ext
 dsimp only [d5,jh]
 by_cases hj:j.val+1 < k
 ·have h1:(j.val+1) % k=j.val+1:=Nat.mod_eq_of_lt hj
  rw [h1]
  have h2:j.val+1+k - 1=j.val+k:=by omega
  rw [h2,Nat.add_mod_right,Nat.mod_eq_of_lt j.isLt]
 ·have h1:(j.val+1) % k=0:=by rw [show j.val+1=k by omega,Nat.mod_self]
  rw [h1,zero_add,Nat.mod_eq_of_lt (by omega)]
  omega
def dr {k:ℕ} (hk:0 < k):Fin k ≃ Fin k where
 toFun:=jh hk
 invFun:=d5 hk
 left_inv:=gp hk
 right_inv:=gq hk
def vi {k:ℕ} (S:Finset (Fin k)):ℕ:=
 ((Finset.univ:Finset (Fin k)).filter (fun j=>j∈S/\∀ z∈S,(z.val+1) % k ≠ j.val)).card
def qz (k h:ℕ):Finset (Finset (Fin k)):=
 Finset.univ.filter (fun S:Finset (Fin k)=>vi S ≤ h)
lemma yh {k:ℕ} (hk:0 < k) (S:Finset (Fin k)) :
  vi S=(Finset.univ.filter (fun j:Fin k=>j∈S/\jh hk j∉S)).card:=by
 unfold vi
 congr 1
 ext j
 simp only [dK,dL,true_and]
 constructor
 ·rintro ⟨hj,hall⟩
  refine ⟨hj,fun hcp=>hall (jh hk j) hcp ?_⟩
  exact congrArg Fin.val (gp hk j)
 ·rintro ⟨hj,hncp⟩
  refine ⟨hj,fun z hz heq=>hncp ?_⟩
  have hcs:d5 hk z=j:=Fin.ext heq
  have hzeq:z=jh hk j:=by rw [← hcs,gq hk]
  rwa [← hzeq]
lemma yn {k:ℕ}:vi (∅:Finset (Fin k))=0:=by
 simp [vi]
lemma d7 {k:ℕ} (hk:0 < k):vi (Finset.univ:Finset (Fin k))=0:=by
 rw [yh hk]
 simp
lemma yw {k:ℕ} (hk:0 < k) (S:Finset (Fin k)) :
  (Finset.univ.filter (fun j:Fin k=>j∈S/\jh hk j∉S)).card =
   (Finset.univ.filter (fun j:Fin k=>j∉S/\jh hk j∈S)).card:=by
 set A:=Finset.univ.filter (fun j:Fin k=>j∈S/\jh hk j∉S)
 set B:=Finset.univ.filter (fun j:Fin k=>j∉S/\jh hk j∈S)
 have hsum0:(∑ j:Fin k,((if j∈S then (1:ℤ) else 0) - (if jh hk j∈S then 1 else 0)))=0:=by
  rw [Finset.sum_sub_distrib]
  have heq:(∑ j:Fin k,if jh hk j∈S then (1:ℤ) else 0) =
    ∑ j:Fin k,if j∈S then (1:ℤ) else 0:=
   Equiv.sum_comp (dr hk) (fun j=>if j∈S then (1:ℤ) else 0)
  rw [heq,sub_self]
 have hterm:∀ j:Fin k,
   ((if j∈S then (1:ℤ) else 0) - (if jh hk j∈S then 1 else 0)) =
   (if j∈A then (1:ℤ) else 0) - (if j∈B then 1 else 0):=by
  intro j
  by_cases h1:j∈S <;> by_cases h2:jh hk j∈S <;> simp [A,B,h1,h2]
 have hsumAB:(∑ j:Fin k,((if j∈S then (1:ℤ) else 0) - (if jh hk j∈S then 1 else 0))) =
   (A.card:ℤ) - (B.card:ℤ):=by
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_boole]
 omega
lemma yO {k h:ℕ} (hk:0 < k) :
  (qz k h).card ≤ 2*k^(2*h):=by
 let decode:Bool × (Fin (2*h)->Fin k)->Finset (Fin k):=fun p=>
  Finset.univ.filter (fun j:Fin k=>
   xor p.1 (decide (Odd (Finset.univ.filter (fun r:Fin (2*h)=>(p.2 r).val ≤ j.val)).card))=true)
 have hsub:qz k h ⊆ Finset.univ.image decode:=by
  intro S hS
  have hle:vi S ≤ h:=(Finset.mem_filter.mp hS).2
  set A:=Finset.univ.filter (fun j:Fin k=>j∈S/\jh hk j∉S)
  set B:=Finset.univ.filter (fun j:Fin k=>j∉S/\jh hk j∈S)
  set T:=A∪B
  have hdisj:Disjoint A B:=by
   rw [Finset.disjoint_left]
   intro j hjA hjB
   exact (Finset.mem_filter.mp hjB).2.1 (Finset.mem_filter.mp hjA).2.1
  have hTcard:T.card ≤ 2*h:=by
   have hBA:B.card=A.card:=(yw hk S).symm
   have hA:A.card=vi S:=(yh hk S).symm
   rw [Finset.card_union_of_disjoint hdisj,hBA,hA]
   omega
  have hTmem:∀ j:Fin k,j∈T ↔ (decide (j∈S) ≠ decide (jh hk j∈S)):=by
   intro j
   simp only [T,A,B,Finset.mem_union,dK,dL,true_and]
   by_cases h1:j∈S <;> by_cases h2:jh hk j∈S <;> simp [h1,h2]
  set T':=T.erase ⟨0,hk⟩
  have hT'le:T'.card ≤ 2*h:=(Finset.card_erase_le).trans hTcard
  set L:=T'.toList
  have hLlen:L.length ≤ 2*h:=by rw [Finset.length_toList];exact hT'le
  have hLnd:L.Nodup:=Finset.nodup_toList T'
  let pts:Fin (2*h)->Fin k:=fun r=>
   if hr:r.val < L.length then L[r.val]'hr else ⟨0,hk⟩
  let pad:=2*h - L.length
  let b0:Bool:=xor (decide (⟨0,hk⟩∈S)) (decide (Odd pad))
  have hcnt:∀ j:Fin k,
    (Finset.univ.filter (fun r:Fin (2*h)=>(pts r).val ≤ j.val)).card =
     pad+(T'.filter (fun z=>z.val ≤ j.val)).card:=by
   intro j
   set F:=Finset.univ.filter (fun r:Fin (2*h)=>(pts r).val ≤ j.val)
   set F1:=F.filter (fun r:Fin (2*h)=>r.val < L.length)
   set F2:=F.filter (fun r:Fin (2*h)=>¬ (r.val < L.length))
   have hsplit:F.card=F1.card+F2.card:=by
    rw [← Finset.card_union_of_disjoint]
    ·congr 1;ext r;simp only [F1,F2,Finset.mem_union,dK];tauto
    ·rw [Finset.disjoint_left];intro r h1 h2
     exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
   have hF2:F2.card=pad:=by
    have hEq:F2=Finset.univ.filter (fun r:Fin (2*h)=>L.length ≤ r.val):=by
     ext r
     simp only [F2,F,dK,dL,true_and,not_lt]
     constructor
     ·exact fun h=>h.2
     ·intro hge
      refine ⟨?_,hge⟩
      simp only [pts,show ¬ r.val < L.length by omega,↓reduceDIte]
      exact Nat.zero_le _
    rw [hEq]
    have hcomp:(Finset.univ.filter (fun r:Fin (2*h)=>r.val < L.length)).card +
      (Finset.univ.filter (fun r:Fin (2*h)=>L.length ≤ r.val)).card=2*h:=by
     rw [← Finset.card_union_of_disjoint]
     ·have hu:Finset.univ.filter (fun r:Fin (2*h)=>r.val < L.length) ∪
        Finset.univ.filter (fun r:Fin (2*h)=>L.length ≤ r.val)=Finset.univ:=by
       ext r;simp only [Finset.mem_union,dK,dL,true_and]
       exact iff_true_intro (lt_or_ge r.val L.length)
      rw [hu,Finset.card_univ,Fintype.card_fin]
     ·rw [Finset.disjoint_left];intro r h1 h2
      simp only [dK,dL,true_and] at h1 h2;omega
    have hltc:(Finset.univ.filter (fun r:Fin (2*h)=>r.val < L.length)).card=L.length:=by
     conv_rhs=>rw [← Fintype.card_fin L.length,← Finset.card_univ]
     refine Finset.card_bij (fun (r:Fin (2*h)) hr=>
      (⟨r.val,(Finset.mem_filter.mp hr).2⟩:Fin L.length))
      ?_ ?_ ?_
     ·intro _ _;exact dL _
     ·intro a _ b _ h;exact Fin.ext (by simpa using congrArg Fin.val h)
     ·intro i _
      exact ⟨⟨i.val,lt_of_lt_of_le i.isLt hLlen⟩,
       Finset.mem_filter.mpr ⟨dL _,i.isLt⟩,Fin.ext rfl⟩
    omega
   have hF1:F1.card=(T'.filter (fun z=>z.val ≤ j.val)).card:=by
    refine Finset.card_bij (fun r _=>pts r) ?_ ?_ ?_
    ·intro r hr
     simp only [F1,F,dK,dL,true_and] at hr
     simp only [dK]
     refine ⟨?_,hr.1⟩
     have hmemL:pts r∈L:=by
      simp only [pts,hr.2,↓reduceDIte]
      exact List.getElem_mem hr.2
     exact Finset.mem_toList.mp hmemL
    ·intro r1 hr1 r2 hr2 heq
     simp only [F1,F,dK,dL,true_and] at hr1 hr2
     simp only [pts,hr1.2,hr2.2,↓reduceDIte] at heq
     have hv:=(List.Nodup.getElem_inj_iff hLnd).mp heq
     exact Fin.ext hv
    ·intro z hz
     simp only [dK] at hz
     have hzL:z∈L:=Finset.mem_toList.mpr hz.1
     obtain ⟨idx,hidx,hget⟩:=List.mem_iff_getElem.mp hzL
     refine ⟨⟨idx,lt_of_lt_of_le hidx hLlen⟩,?_,?_⟩
     ·simp only [F1,F,dK,dL,true_and,pts,hidx,↓reduceDIte,hget]
      exact ⟨hz.2,trivial⟩
     ·simp only [pts,hidx,↓reduceDIte,hget]
   omega
  have hmatch:∀ i:ℕ,(hi:i < k) ->
    xor b0 (decide (Odd (Finset.univ.filter (fun r:Fin (2*h)=>(pts r).val ≤ i)).card)) =
     decide ((⟨i,hi⟩:Fin k)∈S):=by
   intro i
   induction i with
   | zero=>
    intro hi
    have h0:(Finset.univ.filter (fun r:Fin (2*h)=>(pts r).val ≤ 0)).card=pad:=by
     have hc:=hcnt ⟨0,hi⟩
     have hemp:T'.filter (fun z=>z.val ≤ 0)=∅:=by
      ext z
      simp only [T',dK,Finset.mem_erase,Finset.notMem_empty,iff_false,not_and]
      rintro ⟨hne,_⟩ hle0
      exact hne (Fin.ext (by dsimp;omega))
     rw [hemp,Finset.card_empty,add_zero] at hc
     exact hc
    rw [h0]
    simp only [b0]
    cases decide (⟨0,hk⟩∈S) <;> cases decide (Odd pad) <;> rfl
   | succ i ih=>
    intro hi
    have hi0:i < k:=Nat.lt_of_succ_le (Nat.le_of_lt hi)
    have hih:=ih hi0
    set c0:=(Finset.univ.filter (fun r:Fin (2*h)=>(pts r).val ≤ i)).card
    set c1:=(Finset.univ.filter (fun r:Fin (2*h)=>(pts r).val ≤ i+1)).card
    have hc0:c0=pad+(T'.filter (fun z=>z.val ≤ i)).card:=hcnt ⟨i,hi0⟩
    have hc1:c1=pad+(T'.filter (fun z=>z.val ≤ i+1)).card:=hcnt ⟨i+1,hi⟩
    have hcp:jh hk ⟨i+1,hi⟩=⟨i,hi0⟩:=by
     apply Fin.ext
     dsimp only [jh]
     have h1:i+1+k - 1=i+k:=by omega
     rw [h1,Nat.add_mod_right,Nat.mod_eq_of_lt hi0]
    by_cases hmem:(⟨i+1,hi⟩:Fin k)∈T'
    ·have hnot:(⟨i+1,hi⟩:Fin k)∉T'.filter (fun z=>z.val ≤ i):=by
      simp only [dK];omega
     have hins:T'.filter (fun z=>z.val ≤ i+1) =
       insert ⟨i+1,hi⟩ (T'.filter (fun z=>z.val ≤ i)):=by
      ext z
      simp only [dK,Finset.mem_insert]
      constructor
      ·rintro ⟨hz,hle⟩
       by_cases hle':z.val ≤ i
       ·right;exact ⟨hz,hle'⟩
       ·left;exact Fin.ext (by dsimp;omega)
      ·rintro (rfl | ⟨hz,hle'⟩)
       ·exact ⟨hmem,le_rfl⟩
       ·exact ⟨hz,by omega⟩
     have hc1eq:c1=c0+1:=by
      rw [hc1,hc0,hins,Finset.card_insert_of_notMem hnot];omega
     have hmemT:(⟨i+1,hi⟩:Fin k)∈T:=Finset.mem_of_mem_erase hmem
     have hdiff:decide ((⟨i+1,hi⟩:Fin k)∈S) ≠ decide ((⟨i,hi0⟩:Fin k)∈S):=by
      rw [← hcp];exact (hTmem ⟨i+1,hi⟩).mp hmemT
     have hodd:decide (Odd c1)=!decide (Odd c0):=by
      rw [hc1eq]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true',decide_eq_false_iff_not,dG,Nat.odd_iff]
      omega
     change xor b0 (decide (Odd c1))=decide ((⟨i+1,hi⟩:Fin k)∈S)
     rw [hodd]
     have hih':xor b0 (decide (Odd c0))=decide ((⟨i,hi0⟩:Fin k)∈S):=hih
     have hbool:∀ (a b c d:Bool),xor a b=d->c ≠ d->xor a (!b)=c:=by
      decide
     exact hbool b0 (decide (Odd c0)) (decide ((⟨i+1,hi⟩:Fin k)∈S))
      (decide ((⟨i,hi0⟩:Fin k)∈S)) hih' hdiff
    ·have heqF:T'.filter (fun z=>z.val ≤ i+1)=T'.filter (fun z=>z.val ≤ i):=by
      ext z
      simp only [dK]
      constructor
      ·rintro ⟨hz,hle⟩
       refine ⟨hz,?_⟩
       by_contra hgt
       have hzeq:z=⟨i+1,hi⟩:=Fin.ext (by dsimp;omega)
       rw [hzeq] at hz
       exact hmem hz
      ·rintro ⟨hz,hle⟩;exact ⟨hz,by omega⟩
     have hc1eq:c1=c0:=by rw [hc1,hc0,heqF]
     have hnotT:(⟨i+1,hi⟩:Fin k)∉T:=by
      intro hT'
      exact hmem (Finset.mem_erase.mpr ⟨fun e=>by have:=congrArg Fin.val e;dsimp at this;omega,hT'⟩)
     have hsame:decide ((⟨i+1,hi⟩:Fin k)∈S)=decide ((⟨i,hi0⟩:Fin k)∈S):=by
      rw [← hcp]
      by_contra hne
      exact hnotT ((hTmem ⟨i+1,hi⟩).mpr hne)
     change xor b0 (decide (Odd c1))=decide ((⟨i+1,hi⟩:Fin k)∈S)
     rw [hc1eq,hsame];exact hih
  refine Finset.mem_image.mpr ⟨(b0,pts),dL _,?_⟩
  ext j
  simp only [decode,dK,dL,true_and]
  rw [hmatch j.val j.isLt]
  simp
 calc (qz k h).card
   ≤ (Finset.univ.image decode).card:=Finset.card_le_card hsub
  _ ≤ (Finset.univ:Finset (Bool × (Fin (2*h)->Fin k))).card:=Finset.card_image_le
  _=2*k^(2*h):=by simp [Fintype.card_prod]
def qK {m:ℕ} (v:Q1 m):Bool:=
 (dF m).any (fun i=>v i)
lemma d2 {m:ℕ} (a:Fin (2^m)) :
  qK (fun i:Fin m=>a.val.testBit i.val)=decide (a.val ≠ 0):=by
 apply Bool.eq_iff_iff.mpr
 simp only [qK,List.any_eq_true,List.mem_finRange,true_and,dG]
 constructor
 ·rintro ⟨i,hi⟩ h0
  rw [h0,Nat.zero_testBit] at hi
  exact Bool.false_ne_true hi
 ·intro hne
  by_contra hall
  push_neg at hall
  apply hne
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj:j < m
  ·exact Bool.eq_false_iff.mpr (hall ⟨j,hj⟩)
  ·exact Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hj)))
def y4 (k r:ℕ) (col:Bool) (p z:Fin k):Bool:=
 decide (∃ t:Fin (yy r col+1),(p.val+t.val) % k=z.val)
def d3 {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (p:Fin k) (col:Bool):Finset (Fin k):=
 Finset.univ.filter (fun z=>
  qK (if col then Bb p else Ab p)=true/\y4 k r col p z=true)
def qq {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (p:Fin k):Finset (Fin k):=
 d3 r Ab Bb p false∪d3 r Ab Bb p true
def qi {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)):Finset (Fin k):=
 S.biUnion (qq r Ab Bb)
def qw {k m:ℕ} (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)) :
  Submodule (ZMod 2) (Fin m->ZMod 2):=
 Submodule.span (ZMod 2) {v:Fin m->ZMod 2 | ∃ p∈S,v=q4 (Ab p)\/v=q4 (Bb p)}
def z0 {k m:ℕ} (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)):List (Q1 m):=
 (dF k).flatMap (fun p=>if p∈S then [Ab p,Bb p] else [])
def vV {k m:ℕ} (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)):Q6 m:=
 (z0 Ab Bb S).foldl qC (qN m)
lemma yl {k m:ℕ} (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)) :
  Q3 (vV Ab Bb S)/\q6 (vV Ab Bb S)=qw Ab Bb S:=by
 obtain ⟨hE,hsp⟩:=gC (qN m) (jE m) (z0 Ab Bb S)
 refine ⟨hE,?_⟩
 unfold vV
 rw [hsp,y6,bot_sup_eq]
 unfold qw
 congr 1
 ext v
 simp only [Finset.mem_coe,List.mem_toFinset,List.mem_map,z0,List.mem_flatMap,
  List.mem_finRange,true_and,Set.mem_setOf_eq]
 constructor
 ·rintro ⟨w,⟨p,hp⟩,rfl⟩
  by_cases hpS:p∈S
  ·simp only [hpS,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hp
   rcases hp with rfl | rfl
   ·exact ⟨p,hpS,Or.inl rfl⟩
   ·exact ⟨p,hpS,Or.inr rfl⟩
  ·simp only [hpS,↓reduceIte,List.not_mem_nil] at hp
 ·rintro ⟨p,hpS,rfl | rfl⟩
  ·exact ⟨Ab p,⟨p,by simp [hpS]⟩,rfl⟩
  ·exact ⟨Bb p,⟨p,by simp [hpS]⟩,rfl⟩
noncomputable def qL {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (p:Fin k):ℕ:=
 ((qi r Ab Bb S∩qi r Ab Bb Sᶜ)∪qq r Ab Bb p).card +
  Module.finrank (ZMod 2) (qw Ab Bb S ⊓ qw Ab Bb Sᶜ:Submodule (ZMod 2) (Fin m->ZMod 2))
lemma dc {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (p:Fin k):qL r Ab Bb S p ≤ k+m:=by
 unfold qL
 have h1:((qi r Ab Bb S∩qi r Ab Bb Sᶜ)∪qq r Ab Bb p).card ≤ k:=by
  calc ((qi r Ab Bb S∩qi r Ab Bb Sᶜ)∪qq r Ab Bb p).card
    ≤ (Finset.univ:Finset (Fin k)).card:=Finset.card_le_univ _
   _=k:=by simp
 have h2:Module.finrank (ZMod 2) (qw Ab Bb S ⊓ qw Ab Bb Sᶜ:Submodule (ZMod 2) (Fin m->ZMod 2)) ≤ m:=by
  calc Module.finrank (ZMod 2) (qw Ab Bb S ⊓ qw Ab Bb Sᶜ:Submodule (ZMod 2) (Fin m->ZMod 2))
    ≤ Module.finrank (ZMod 2) (Fin m->ZMod 2):=Submodule.finrank_le _
   _=m:=by simp
 omega
lemma z9 {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (p:Fin k) :
  qL r Ab Bb S p =
   ((qi r Ab Bb S∩qi r Ab Bb Sᶜ)∪qq r Ab Bb p).card +
    q3 (vv (vV Ab Bb S) (vV Ab Bb Sᶜ)).2.2:=by
 unfold qL
 congr 1
 obtain ⟨_,hspL⟩:=yl Ab Bb S
 obtain ⟨hER,hspR⟩:=yl Ab Bb Sᶜ
 obtain ⟨_,hETi,_,hspTi,_⟩:=jW (vV Ab Bb S) (vV Ab Bb Sᶜ) hER
 rw [← hspL,← hspR,← hspTi,qo hETi]
noncomputable def jg {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m) :
  ℕ->Finset (Fin k)->ℕ
 | 0,_=>0
 | t+1,S=>
  (dF k).foldl (fun acc p=>
   if p∉S/\vi (insert p S) ≤ h then
    min acc (max (qL r Ab Bb S p) (jg r h Ab Bb t (insert p S)))
   else acc) (k+m+1)
noncomputable def qQ {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)):ℕ:=
 jg r h Ab Bb (k - S.card) S
lemma yT {α:Type*} (L:List α) (f:α->ℕ->ℕ) (init:ℕ)
  (hf:∀ a x,f a x ≤ x):L.foldl (fun acc a=>f a acc) init ≤ init:=by
 induction L generalizing init with
 | nil=>exact le_rfl
 | cons a t ih=>
  simp only [List.foldl_cons]
  exact (ih (f a init)).trans (hf a init)
lemma gg {α:Type*} (L:List α) (P:α->Prop) [DecidablePred P]
  (val:α->ℕ) (init:ℕ) (a:α) (ha:a∈L) (hP:P a) :
  L.foldl (fun acc x=>if P x then min acc (val x) else acc) init ≤ val a:=by
 induction L generalizing init with
 | nil=>cases ha
 | cons b t ih=>
  simp only [List.foldl_cons]
  have hstep:∀ x y,(if P x then min y (val x) else y) ≤ y:=by
   intro x y;split_ifs <;> simp
  rcases List.mem_cons.mp ha with rfl | hmem
  ·simp only [hP,↓reduceIte]
   exact (yT t (fun x y=>if P x then min y (val x) else y) (min init (val a)) hstep).trans
    (min_le_right _ _)
  ·exact ih _ hmem
lemma zh {α:Type*} (L:List α) (P:α->Prop) [DecidablePred P]
  (val:α->ℕ) (init:ℕ) :
  let res:=L.foldl (fun acc x=>if P x then min acc (val x) else acc) init
  res=init\/∃ a∈L,P a/\res=val a:=by
 induction L generalizing init with
 | nil=>left;rfl
 | cons b t ih=>
  dsimp only [List.foldl_cons]
  by_cases hP:P b
  ·simp only [hP,↓reduceIte]
   rcases ih (min init (val b)) with heq | ⟨a,ha,hPa,heq⟩
   ·rcases min_cases init (val b) with ⟨hm,_⟩ | ⟨hm,_⟩
    ·left;rw [heq,hm]
    ·right;exact ⟨b,List.mem_cons_self,hP,heq.trans hm⟩
   ·right;exact ⟨a,List.mem_cons_of_mem b ha,hPa,heq⟩
  ·simp only [hP,↓reduceIte]
   rcases ih init with heq | ⟨a,ha,hPa,heq⟩
   ·left;exact heq
   ·right;exact ⟨a,List.mem_cons_of_mem b ha,hPa,heq⟩
lemma dq {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m) :
  qQ r h Ab Bb Finset.univ=0:=by
 simp [qQ,jg]
lemma d1 {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (p:Fin k) (hp:p∉S) (harc:vi (insert p S) ≤ h) :
  qQ r h Ab Bb S ≤ max (qL r Ab Bb S p) (qQ r h Ab Bb (insert p S)):=by
 have hcard:S.card < k:=by
  have hlt:S.card < (insert p S).card:=by rw [Finset.card_insert_of_notMem hp];omega
  exact lt_of_lt_of_le hlt (by simpa using Finset.card_le_univ (insert p S))
 have hsub:k - S.card=(k - (insert p S).card)+1:=by
  rw [Finset.card_insert_of_notMem hp];omega
 unfold qQ
 rw [hsub]
 dsimp only [jg]
 exact gg (dF k) (fun q=>q∉S/\vi (insert q S) ≤ h)
  (fun q=>max (qL r Ab Bb S q) (jg r h Ab Bb (k - (insert p S).card) (insert q S)))
  (k+m+1) p (List.mem_finRange p) ⟨hp,harc⟩
lemma dD {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)) :
  qQ r h Ab Bb S ≤ k+m+1:=by
 unfold qQ
 cases hsub:k - S.card with
 | zero=>simp [jg]
 | succ t=>
  dsimp only [jg]
  exact yT (dF k) _ (k+m+1) (fun a x=>by split_ifs <;> simp)
lemma yc {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (hSc:S.card < k) (hlt:qQ r h Ab Bb S ≤ k+m) :
  ∃ p:Fin k,p∉S/\vi (insert p S) ≤ h /\
   max (qL r Ab Bb S p) (qQ r h Ab Bb (insert p S)) ≤ qQ r h Ab Bb S:=by
 have hsub:k - S.card=(k - (S.card+1))+1:=by omega
 unfold qQ at hlt ⊢
 rw [hsub] at hlt ⊢
 dsimp only [jg] at hlt ⊢
 rcases zh (dF k)
  (fun q=>q∉S/\vi (insert q S) ≤ h)
  (fun q=>max (qL r Ab Bb S q) (jg r h Ab Bb (k - (S.card+1)) (insert q S)))
  (k+m+1) with heq | ⟨p,_,⟨hp,harc⟩,heq⟩
 ·omega
 ·refine ⟨p,hp,harc,?_⟩
  rw [Finset.card_insert_of_notMem hp,← heq]
noncomputable def jV {k m:ℕ} (hk:0 < k) (r h:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (opt:ℕ):Fin k:=
 (dF k).foldr (fun p acc=>
  if p∉S/\vi (insert p S) ≤ h /\
   max (qL r Ab Bb S p) (qQ r h Ab Bb (insert p S)) ≤ opt
  then p else acc) ⟨0,hk⟩
lemma z6 {α:Type*} [LinearOrder α] (L:List α) (hsorted:L.Pairwise (· < ·))
  (P:α->Prop) [DecidablePred P] (d:α) (hex:∃ a∈L,P a) :
  let res:=L.foldr (fun x acc=>if P x then x else acc) d
  res∈L/\P res/\∀ a∈L,P a->res ≤ a:=by
 induction L with
 | nil=>obtain ⟨a,ha,_⟩:=hex;cases ha
 | cons b t ih=>
  obtain ⟨hblt,hts⟩:=List.pairwise_cons.mp hsorted
  dsimp only [List.foldr_cons]
  by_cases hPb:P b
  ·simp only [hPb,↓reduceIte]
   refine ⟨List.mem_cons_self,trivial,fun a ha _=>?_⟩
   rcases List.mem_cons.mp ha with rfl | hmem
   ·exact le_rfl
   ·exact le_of_lt (hblt a hmem)
  ·simp only [hPb,↓reduceIte]
   have hex':∃ a∈t,P a:=by
    obtain ⟨a,ha,hPa⟩:=hex
    rcases List.mem_cons.mp ha with rfl | hmem
    ·exact absurd hPa hPb
    ·exact ⟨a,hmem,hPa⟩
   obtain ⟨hmem,hP,hmin⟩:=ih hts hex'
   refine ⟨List.mem_cons_of_mem b hmem,hP,fun a ha hPa=>?_⟩
   rcases List.mem_cons.mp ha with rfl | hmt
   ·exact absurd hPa hPb
   ·exact hmin a hmt hPa
lemma jH (k:ℕ):(dF k).Pairwise (· < ·):=by
 rw [List.pairwise_iff_getElem]
 intro i j hi hj hij
 simp only [List.getElem_finRange]
 exact hij
lemma zP {k m:ℕ} (hk:0 < k) (r h:ℕ) (Ab Bb:Fin k->Q1 m)
  (S:Finset (Fin k)) (opt:ℕ)
  (hex:∃ p:Fin k,p∉S/\vi (insert p S) ≤ h /\
   max (qL r Ab Bb S p) (qQ r h Ab Bb (insert p S)) ≤ opt) :
  let p:=jV hk r h Ab Bb S opt
  p∉S/\vi (insert p S) ≤ h /\
   max (qL r Ab Bb S p) (qQ r h Ab Bb (insert p S)) ≤ opt /\
   ∀ q:Fin k,q∉S->vi (insert q S) ≤ h ->
    max (qL r Ab Bb S q) (qQ r h Ab Bb (insert q S)) ≤ opt->p ≤ q:=by
 have hex':∃ p∈dF k,p∉S/\vi (insert p S) ≤ h /\
   max (qL r Ab Bb S p) (qQ r h Ab Bb (insert p S)) ≤ opt:=by
  obtain ⟨p,hp⟩:=hex;exact ⟨p,List.mem_finRange p,hp⟩
 obtain ⟨_,⟨h1,h2,h3⟩,hmin⟩:=
  z6 (dF k) (jH k) _ ⟨0,hk⟩ hex'
 exact ⟨h1,h2,h3,fun q hq1 hq2 hq3=>hmin q (List.mem_finRange q) ⟨hq1,hq2,hq3⟩⟩
noncomputable def qj {k m:ℕ} (hk:0 < k) (r h:ℕ) (Ab Bb:Fin k->Q1 m) :
  ℕ->Finset (Fin k)
 | 0=>∅
 | u+1=>
  let S:=qj hk r h Ab Bb u
  insert (jV hk r h Ab Bb S (qQ r h Ab Bb ∅)) S
noncomputable def qW {k m:ℕ} (hk:0 < k) (r h:ℕ) (Ab Bb:Fin k->Q1 m) (i:Fin k):Fin k:=
 jV hk r h Ab Bb (qj hk r h Ab Bb i.val) (qQ r h Ab Bb ∅)
def jO {k:ℕ} (h:ℕ) (o:Fin k->Fin k):Prop:=
 Function.Bijective o/\∀ u:Fin (k+1),vi ((List.ofFn o).take u.val).toFinset ≤ h
noncomputable def qU {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k):ℕ:=
 (Finset.univ:Finset (Fin k)).sup (fun i=>
  let L:=(List.ofFn o).take i.val
  let R:=(List.ofFn o).drop i.val
  ((qi r Ab Bb L.toFinset∩qi r Ab Bb R.toFinset)∪qq r Ab Bb (o i)).card +
   Module.finrank (ZMod 2) (qw Ab Bb L.toFinset ⊓ qw Ab Bb R.toFinset:Submodule (ZMod 2) (Fin m->ZMod 2)))
lemma da {k h:ℕ} (hk:0 < k) (hh:0 < h):jO h (id:Fin k->Fin k):=by
 refine ⟨Function.bijective_id,fun u=>?_⟩
 set S:=((List.ofFn (id:Fin k->Fin k)).take u.val).toFinset
 have hmem:∀ j:Fin k,j∈S ↔ j.val < u.val:=by
  intro j
  simp only [S,List.mem_toFinset,List.mem_iff_getElem,List.length_take,List.length_ofFn,
   List.getElem_take,List.getElem_ofFn,id_eq]
  constructor
  ·rintro ⟨i,hi,hjeq⟩
   have hv:=congrArg Fin.val hjeq
   dsimp at hv;omega
  ·intro hlt
   exact ⟨j.val,by omega,Fin.ext rfl⟩
 by_cases hu0:u.val=0
 ·have hSe:S=∅:=by ext j;rw [hmem];simp [hu0]
  rw [hSe,yn];exact Nat.zero_le _
 ·by_cases huk:u.val=k
  ·have hSu:S=Finset.univ:=by ext j;rw [hmem];simp [huk,j.isLt]
   rw [hSu,d7 hk];exact Nat.zero_le _
  ·rw [yh hk]
   have hsub:Finset.univ.filter (fun j:Fin k=>j∈S/\jh hk j∉S) ⊆ {⟨0,hk⟩}:=by
    intro j hj
    simp only [dK,dL,true_and,hmem] at hj
    simp only [Finset.mem_singleton]
    by_contra hne
    have hpos:0 < j.val:=by
     have:j.val ≠ 0:=fun e=>hne (Fin.ext e)
     omega
    have hcp:(jh hk j).val=j.val - 1:=by
     dsimp only [jh]
     have h1:j.val+k - 1=(j.val - 1)+k:=by omega
     rw [h1,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    exact hj.2 (by omega)
   calc (Finset.univ.filter (fun j:Fin k=>j∈S/\jh hk j∉S)).card
     ≤ ({⟨0,hk⟩}:Finset (Fin k)).card:=Finset.card_le_card hsub
    _=1:=Finset.card_singleton _
    _ ≤ h:=hh
lemma zj {k:ℕ} (o:Fin k->Fin k) (ho:Function.Bijective o) (u:ℕ) :
  ((List.ofFn o).drop u).toFinset=(((List.ofFn o).take u).toFinset)ᶜ:=by
 ext x
 simp only [List.mem_toFinset,Finset.mem_compl,List.mem_iff_getElem,List.length_drop,
  List.length_take,List.length_ofFn,List.getElem_drop,List.getElem_take,List.getElem_ofFn]
 obtain ⟨j,rfl⟩:=ho.2 x
 constructor
 ·rintro ⟨i,hi,heq⟩ ⟨i',hi',heq'⟩
  have hj1:⟨u+i,by omega⟩=j:=ho.1 heq
  have hj2:⟨i',by omega⟩=j:=ho.1 heq'
  have h1:=congrArg Fin.val hj1
  have h2:=congrArg Fin.val hj2
  dsimp at h1 h2;omega
 ·intro hnot
  have hge:u ≤ j.val:=by
   by_contra hlt
   push_neg at hlt
   exact hnot ⟨j.val,by omega,rfl⟩
  exact ⟨j.val - u,by omega,by congr 1;apply Fin.ext;dsimp;omega⟩
lemma zR {k:ℕ} (o:Fin k->Fin k) (ho:Function.Bijective o)
  (u:ℕ) (hu:u ≤ k):(((List.ofFn o).take u).toFinset).card=u:=by
 have hnd:((List.ofFn o).take u).Nodup:=
  (List.nodup_ofFn.mpr ho.1).sublist (List.take_sublist u _)
 rw [List.toFinset_card_of_nodup hnd,List.length_take,List.length_ofFn,Nat.min_eq_left hu]
lemma jY {k:ℕ} (o:Fin k->Fin k) (i:Fin k) :
  ((List.ofFn o).take (i.val+1)).toFinset=insert (o i) ((List.ofFn o).take i.val).toFinset:=by
 rw [dJ (by simp),List.toFinset_append,List.toFinset_cons,
  List.toFinset_nil,Finset.union_comm,Finset.insert_union,Finset.empty_union]
 simp
lemma vR {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m)
  (o:Fin k->Fin k) (ho:Function.Bijective o) :
  qU r Ab Bb o =
   (Finset.univ:Finset (Fin k)).sup (fun i=>
    qL r Ab Bb ((List.ofFn o).take i.val).toFinset (o i)):=by
 unfold qU qL
 congr 1;funext i
 dsimp only
 rw [zj o ho i.val]
lemma jI {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m)
  (z:Fin k->Fin k) (hz:jO h z) :
  ∀ t:ℕ,t ≤ k ->
   qQ r h Ab Bb ((List.ofFn z).take (k - t)).toFinset ≤ qU r Ab Bb z:=by
 intro t
 induction t with
 | zero=>
  intro _
  have hSu:((List.ofFn z).take (k - 0)).toFinset=Finset.univ:=by
   apply Finset.eq_univ_of_card
   rw [zR z hz.1 (k - 0) (by omega),Fintype.card_fin];omega
  rw [hSu,dq]
  exact Nat.zero_le _
 | succ t ih=>
  intro ht
  have hu:k - (t+1) < k:=by omega
  let i:Fin k:=⟨k - (t+1),hu⟩
  have hi1:k - t=i.val+1:=by dsimp [i];omega
  set S:=((List.ofFn z).take i.val).toFinset
  have hnot:z i∉S:=by
   simp only [S,List.mem_toFinset,List.mem_iff_getElem,List.length_take,List.length_ofFn,
    List.getElem_take,List.getElem_ofFn,not_exists]
   intro j hj heq
   have hjeq:(⟨j,by omega⟩:Fin k)=i:=hz.1.1 heq
   have hv:=congrArg Fin.val hjeq
   dsimp at hv;omega
  have hins:insert (z i) S=((List.ofFn z).take (k - t)).toFinset:=by
   rw [hi1,jY z i]
  have harc:vi (insert (z i) S) ≤ h:=by
   rw [hins]
   exact hz.2 ⟨k - t,by omega⟩
  have hle1:=d1 r h Ab Bb S (z i) hnot harc
  have hstep_le:qL r Ab Bb S (z i) ≤ qU r Ab Bb z:=by
   rw [vR r Ab Bb z hz.1]
   exact Finset.le_sup (f:=fun j:Fin k=>qL r Ab Bb ((List.ofFn z).take j.val).toFinset (z j))
    (dL i)
  have hih:qQ r h Ab Bb (insert (z i) S) ≤ qU r Ab Bb z:=by
   rw [hins];exact ih (by omega)
  exact hle1.trans (max_le hstep_le hih)
lemma j5 {k m:ℕ} (r h:ℕ) (Ab Bb:Fin k->Q1 m)
  (z:Fin k->Fin k) (hz:jO h z) :
  qQ r h Ab Bb ∅ ≤ qU r Ab Bb z:=by
 have h1:=jI r h Ab Bb z hz k le_rfl
 simpa using h1
lemma yd {k m:ℕ} (hk:0 < k) (hh:0 < h) (r:ℕ)
  (Ab Bb:Fin k->Q1 m):qQ r h Ab Bb ∅ ≤ k+m:=by
 have h1:=j5 r h Ab Bb id (da hk hh)
 rw [vR r Ab Bb id Function.bijective_id] at h1
 refine h1.trans (Finset.sup_le fun i _=>dc r Ab Bb _ _)
lemma ju {k m:ℕ} (hk:0 < k) (hh:0 < h) (r:ℕ)
  (Ab Bb:Fin k->Q1 m) :
  ∀ u:ℕ,u ≤ k ->
   (qj hk r h Ab Bb u).card=u /\
   vi (qj hk r h Ab Bb u) ≤ h /\
   qQ r h Ab Bb (qj hk r h Ab Bb u) ≤ qQ r h Ab Bb ∅ /\
   qj hk r h Ab Bb u=((List.ofFn (qW hk r h Ab Bb)).take u).toFinset /\
   ∀ i:Fin k,i.val < u ->
    qW hk r h Ab Bb i∉qj hk r h Ab Bb i.val /\
    qL r Ab Bb (qj hk r h Ab Bb i.val) (qW hk r h Ab Bb i) ≤ qQ r h Ab Bb ∅:=by
 intro u
 induction u with
 | zero=>
  intro _
  refine ⟨by simp [qj],by simp [qj,yn],le_rfl,
   by simp [qj],fun _ hi=>absurd hi (by omega)⟩
 | succ u ih=>
  intro hu
  obtain ⟨hcard,harc,hdp,htake,hprev⟩:=ih (Nat.le_of_succ_le hu)
  have hlt:qQ r h Ab Bb (qj hk r h Ab Bb u) ≤ k+m:=
   hdp.trans (yd hk hh r Ab Bb)
  obtain ⟨q,hq1,hq2,hq3⟩:=
   yc r h Ab Bb (qj hk r h Ab Bb u) (by omega) hlt
  have hspec:=zP hk r h Ab Bb (qj hk r h Ab Bb u) (qQ r h Ab Bb ∅)
   ⟨q,hq1,hq2,hq3.trans hdp⟩
  set p:=jV hk r h Ab Bb (qj hk r h Ab Bb u) (qQ r h Ab Bb ∅)
  have hp_not:p∉qj hk r h Ab Bb u:=hspec.1
  have hp_arc:vi (insert p (qj hk r h Ab Bb u)) ≤ h:=hspec.2.1
  have hp_max:max (qL r Ab Bb (qj hk r h Ab Bb u) p)
    (qQ r h Ab Bb (insert p (qj hk r h Ab Bb u))) ≤ qQ r h Ab Bb ∅:=hspec.2.2.1
  refine ⟨?_,hp_arc,(le_max_right _ _).trans hp_max,?_,?_⟩
  ·dsimp only [qj]
   rw [Finset.card_insert_of_notMem hp_not,hcard]
  ·dsimp only [qj]
   have hts:=jY (qW hk r h Ab Bb) ⟨u,hu⟩
   rw [hts,← htake]
   rfl
  ·intro i hi
   by_cases hiu:i.val < u
   ·exact hprev i hiu
   ·have hieq:i=⟨u,hu⟩:=Fin.ext (by dsimp;omega)
    subst hieq
    exact ⟨hp_not,(le_max_left _ _).trans hp_max⟩
lemma zG {k m:ℕ} (hk:0 < k) (hh:0 < h) (r:ℕ)
  (Ab Bb:Fin k->Q1 m) :
  let o:=qW hk r h Ab Bb
  jO h o /\
  qU r Ab Bb o=qQ r h Ab Bb ∅ /\
  (∀ z:Fin k->Fin k,jO h z->qU r Ab Bb o ≤ qU r Ab Bb z) /\
  (∀ z:Fin k->Fin k,jO h z->qU r Ab Bb z=qU r Ab Bb o ->
   z=o\/∃ i:Fin k,o i < z i/\∀ j:Fin k,j < i->o j=z j):=by
 set o:=qW hk r h Ab Bb
 have hinv:=ju hk hh r Ab Bb
 have hinj:Function.Injective o:=by
  intro a b hab
  by_contra hne
  have hlt_or:a.val < b.val\/b.val < a.val:=by
   have:a.val ≠ b.val:=fun e=>hne (Fin.ext e)
   omega
  rcases hlt_or with hlt | hlt
  ·have hnot:=((hinv k le_rfl).2.2.2.2 b b.isLt).1
   have hmem:o a∈qj hk r h Ab Bb b.val:=by
    rw [(hinv b.val (Nat.le_of_lt b.isLt)).2.2.2.1]
    simp only [List.mem_toFinset,List.mem_iff_getElem,List.length_take,List.length_ofFn,
     List.getElem_take,List.getElem_ofFn]
    exact ⟨a.val,by omega,rfl⟩
   rw [hab] at hmem
   exact hnot hmem
  ·have hnot:=((hinv k le_rfl).2.2.2.2 a a.isLt).1
   have hmem:o b∈qj hk r h Ab Bb a.val:=by
    rw [(hinv a.val (Nat.le_of_lt a.isLt)).2.2.2.1]
    simp only [List.mem_toFinset,List.mem_iff_getElem,List.length_take,List.length_ofFn,
     List.getElem_take,List.getElem_ofFn]
    exact ⟨b.val,by omega,rfl⟩
   rw [← hab] at hmem
   exact hnot hmem
 have hbij:Function.Bijective o:=Finite.injective_iff_bijective.mp hinj
 have hall:jO h o:=by
  refine ⟨hbij,fun u=>?_⟩
  rw [← (hinv u.val (Nat.le_of_lt_succ u.isLt)).2.2.2.1]
  exact (hinv u.val (Nat.le_of_lt_succ u.isLt)).2.1
 have hwidth_eq:qU r Ab Bb o=qQ r h Ab Bb ∅:=by
  apply le_antisymm
  ·rw [vR r Ab Bb o hbij]
   refine Finset.sup_le fun i _=>?_
   rw [← (hinv i.val (Nat.le_of_lt i.isLt)).2.2.2.1]
   exact ((hinv k le_rfl).2.2.2.2 i i.isLt).2
  ·exact j5 r h Ab Bb o hall
 refine ⟨hall,hwidth_eq,fun z hz=>?_,fun z hz hzw=>?_⟩
 ·rw [hwidth_eq];exact j5 r h Ab Bb z hz
 ·by_cases heq:z=o
  ·left;exact heq
  ·right
   have hex_ne:∃ i:Fin k,z i ≠ o i:=by
    by_contra h
    push_neg at h
    exact heq (funext h)
   set D:=Finset.univ.filter (fun i:Fin k=>z i ≠ o i)
   have hDne:D.Nonempty:=by
    obtain ⟨i,hi⟩:=hex_ne
    exact ⟨i,Finset.mem_filter.mpr ⟨dL i,hi⟩⟩
   set i:=D.min' hDne
   have hi_ne:z i ≠ o i:=(Finset.mem_filter.mp (Finset.min'_mem D hDne)).2
   have hlt_eq:∀ j:Fin k,j < i->o j=z j:=by
    intro j hji
    by_contra hne'
    have hjD:j∈D:=Finset.mem_filter.mpr ⟨dL j,Ne.symm hne'⟩
    exact absurd (Finset.min'_le D j hjD) (not_le_of_gt hji)
   have htake_eq:((List.ofFn z).take i.val).toFinset=qj hk r h Ab Bb i.val:=by
    rw [(hinv i.val (Nat.le_of_lt i.isLt)).2.2.2.1]
    congr 1
    apply List.ext_getElem
    ·simp
    ·intro t ht1 ht2
     simp only [List.length_take,List.length_ofFn] at ht1
     simp only [List.getElem_take,List.getElem_ofFn]
     exact (hlt_eq ⟨t,by omega⟩ (by change t < i.val;omega)).symm
   have hzi_not:z i∉qj hk r h Ab Bb i.val:=by
    rw [← htake_eq]
    simp only [List.mem_toFinset,List.mem_iff_getElem,List.length_take,List.length_ofFn,
     List.getElem_take,List.getElem_ofFn,not_exists]
    intro t ht heq'
    have hteq:(⟨t,by omega⟩:Fin k)=i:=hz.1.1 heq'
    have hv:=congrArg Fin.val hteq
    dsimp at hv;omega
   have hzi_ins:insert (z i) (qj hk r h Ab Bb i.val)=((List.ofFn z).take (i.val+1)).toFinset:=by
    rw [← htake_eq,← jY z i]
   have hzi_arc:vi (insert (z i) (qj hk r h Ab Bb i.val)) ≤ h:=by
    rw [hzi_ins];exact hz.2 ⟨i.val+1,by omega⟩
   have hzi_step:qL r Ab Bb (qj hk r h Ab Bb i.val) (z i) ≤ qQ r h Ab Bb ∅:=by
    rw [← htake_eq,← hwidth_eq,← hzw,vR r Ab Bb z hz.1]
    exact Finset.le_sup (f:=fun j:Fin k=>qL r Ab Bb ((List.ofFn z).take j.val).toFinset (z j))
     (dL i)
   have hzi_dp:qQ r h Ab Bb (insert (z i) (qj hk r h Ab Bb i.val)) ≤ qQ r h Ab Bb ∅:=by
    rw [hzi_ins,← hwidth_eq,← hzw]
    have h2:=jI r h Ab Bb z hz (k - (i.val+1)) (by omega)
    rwa [Nat.sub_sub_self (by omega)] at h2
   have hspec:=zP hk r h Ab Bb (qj hk r h Ab Bb i.val) (qQ r h Ab Bb ∅)
    ⟨z i,hzi_not,hzi_arc,max_le hzi_step hzi_dp⟩
   have hle_oi:o i ≤ z i:=
    hspec.2.2.2 (z i) hzi_not hzi_arc (max_le hzi_step hzi_dp)
   exact ⟨i,lt_of_le_of_ne hle_oi (Ne.symm hi_ne),hlt_eq⟩
end PlanMath
section PlanCircuit
def Q0.gU {nIn:ℕ} (Bstep:ℕ->ℕ) (N:ℕ)
  (Acc:(j:ℕ)->j ≤ N->CB nIn->Type)
  (c:CB nIn) (init:Acc 0 (Nat.zero_le N) c)
  (step:∀ (j:ℕ) (hj:j < N) (c₁:CB nIn),c.Qa c₁ ->
   Acc j (Nat.le_of_lt hj) c₁->Q0 nIn c₁ (Bstep j) (Acc (j+1) hj)) :
  Q0 nIn c (∑ j∈Finset.range N,Bstep j) (Acc N le_rfl):=by
 let rec go:∀ (t:ℕ) (ht:t ≤ N),Q0 nIn c (∑ j∈Finset.range t,Bstep j) (Acc t ht)
  | 0,ht=>⟨c,CB.zi c,by simp,init⟩
  | t+1,ht=>
   let prev:=go t (Nat.le_of_succ_le ht)
   let nxt:=step t ht prev.c' prev.ext prev.val
   ⟨nxt.c',CB.q0 prev.ext nxt.ext,
    nxt.hsize.trans (by
     have hp:=prev.hsize
     rw [Finset.sum_range_succ]
     omega),
    nxt.val⟩
 exact go N le_rfl
lemma jp (N:ℕ):N+1 < 2^(N+2):=by
 induction N with
 | zero=>decide
 | succ n ih=>
  rw [show n+1+2=(n+2)+1 by omega,pow_succ]
  omega
lemma qv {m:ℕ} (v:Q1 m) :
  qK v=decide (∃ i:Fin m,v i=true):=by
 apply Bool.eq_iff_iff.mpr
 simp [qK]
def gK {nIn:ℕ} (c:CB nIn) {k m:ℕ}
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (S:Finset (Fin k)) :
  Q0 nIn c (m*m+k*(42*m*m+12*m))
   (fun c'=>Q8 nIn c' m (fun x=>vV (fA x) (fB x) S)):=
 Q0.weaken (by nlinarith)<|
 (y0 c m).bind fun c0 h0 zT=>
 let preVecs (j:ℕ) (x:Fin nIn->Bool):List (Q1 m):=
  ((dF k).take j).flatMap (fun p=>if p∈S then [fA x p,fB x p] else [])
 let Acc (j:ℕ) (_:j ≤ k) (c1:CB nIn):Type:=
  Q8 nIn c1 m (fun x=>(preVecs j x).foldl qC (qN m))
 have hinit:Acc 0 (Nat.zero_le k) c0:=
  zT.cast (fun _=>by simp [preVecs])
 (Q0.qe (Bstep:=42*m*m+12*m) k Acc c0 hinit fun j hj c1 h1 Tc=>
  let pj:Fin k:=⟨j,hj⟩
  have htake:(dF k).take (j+1)=(dF k).take j ++ [pj]:=by
   rw [dJ (by simp;omega)];simp [pj]
  if hmem:pj∈S then
   Q0.weaken (by nlinarith)<|
   let h01:=CB.q0 h0 h1
   (jD c1 Tc ((Ab pj).lift h01)).bind fun c2 h2 T1=>
   (jD c2 T1 ((Bb pj).lift (CB.q0 h01 h2))).bind fun _ _ T2=>
   Q0.pure<|T2.cast fun x=>by
    simp only [preVecs,htake,List.flatMap_append,List.flatMap_singleton,hmem,↓reduceIte,
     List.foldl_append,List.foldl_cons,List.foldl_nil]
  else
   Q0.weaken (by nlinarith)<|
   Q0.pure<|Tc.cast fun x=>by
    simp only [preVecs,htake,List.flatMap_append,List.flatMap_singleton,hmem,↓reduceIte,
     List.append_nil]).bind fun _ _ TF=>
 Q0.pure<|TF.cast fun x=>by
  simp only [preVecs,vV,z0,show (dF k).take k=dF k by simp]
def gn {nIn:ℕ} (c:CB nIn) {k m:ℕ} (r:ℕ)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p)) :
  Q0 nIn c (1+k*(2*m+3))
   (fun c'=>∀ p:Fin k,Q2 nIn c' k (fun x z=>decide (z∈qq r (fA x) (fB x) p))):=
 Q0.weaken (by omega)<|
 (vJ c false).bind fun c0 h0 vfalse=>
 let Acc (j:ℕ) (_:j ≤ k) (c1:CB nIn):Type:=
  ∀ p:Fin k,p.val < j ->
   Q4 nIn c1 (fun x=>qK (fA x p)) ×
   Q4 nIn c1 (fun x=>qK (fB x p)) ×
   Q4 nIn c1 (fun x=>qK (fA x p)||qK (fB x p))
 have hinit:Acc 0 (Nat.zero_le k) c0:=fun _ hp=>absurd hp (by omega)
 (Q0.qe (Bstep:=2*m+3) k Acc c0 hinit fun j hj c1 h1 acc=>
  Q0.weaken (by omega)<|
  let pj:Fin k:=⟨j,hj⟩
  let h01:=CB.q0 h0 h1
  (zg c1 ((Ab pj).lift h01)).bind fun c2 h2 vA=>
  (zg c2 ((Bb pj).lift (CB.q0 h01 h2))).bind fun c3 h3 vB=>
  let vA':=(vA.lift h3).cast (fun x=>(qv (fA x pj)).symm)
  let vB':=vB.cast (fun x=>(qv (fB x pj)).symm)
  (yr c3 vA' vB').bind fun c4 h4 vAB=>
  let hall:=CB.q0 h2 (CB.q0 h3 h4)
  Q0.pure fun p hp=>
   if hlt:p.val < j then
    let pr:=acc p hlt
    ⟨pr.1.lift hall,pr.2.1.lift hall,pr.2.2.lift hall⟩
   else
    have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
    heq▸⟨vA'.lift h4,vB'.lift h4,vAB⟩).bind fun cF hF nzs=>
 Q0.pure fun p=>
  let pr:=nzs p p.isLt
  let vf:=vfalse.lift hF
  let wireFor (z:Fin k):Q4 nIn cF (fun x=>decide (z∈qq r (fA x) (fB x) p)):=
   match hf:y4 k r false p z,ht:y4 k r true p z with
   | true,true=>pr.2.2.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp [qq,d3,hf,ht]
   | true,false=>pr.1.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp [qq,d3,hf,ht]
   | false,true=>pr.2.1.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp [qq,d3,hf,ht]
   | false,false=>vf.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp [qq,d3,hf,ht]
  ⟨fun z=>(wireFor z).w,fun z=>(wireFor z).hw,fun x z=>(wireFor z).heval x⟩
def gm {nIn:ℕ} (c:CB nIn) {k m:ℕ} (r:ℕ)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p)))
  (S:Finset (Fin k)) :
  Q0 nIn c (k*(1+k))
   (fun c'=>Q2 nIn c' k (fun x z=>decide (z∈qi r (fA x) (fB x) S))):=
 j8 k (fun x z=>decide (z∈qi r (fA x) (fB x) S)) c fun z c1 h1=>
  Q0.weaken (by omega)<|
  (vJ c1 false).bind fun c2 h2 vfalse=>
  let Acc (j:ℕ) (_:j ≤ k) (c3:CB nIn):Type:=
   Q4 nIn c3 (fun x=>decide (∃ p∈S,p.val < j/\z∈qq r (fA x) (fB x) p))
  have hinit:Acc 0 (Nat.zero_le k) c2:=
   vfalse.cast fun _=>by simp
  (Q0.qe (Bstep:=1) k Acc c2 hinit fun j hj c3 h3 acc=>
   let pj:Fin k:=⟨j,hj⟩
   if hmem:pj∈S then
    (yr c3 acc (((scopes pj).at z).lift (CB.q0 h1 (CB.q0 h2 h3)))).bind fun _ _ vor=>
    Q0.pure<|vor.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dH,dG]
     constructor
     ·rintro (⟨p,hpS,hlt,hzs⟩ | hzs)
      ·exact ⟨p,hpS,by omega,hzs⟩
      ·exact ⟨pj,hmem,by dsimp [pj];omega,hzs⟩
     ·rintro ⟨p,hpS,hlt,hzs⟩
      by_cases hlt':p.val < j
      ·left;exact ⟨p,hpS,hlt',hzs⟩
      ·right
       have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
       rwa [← heq]
   else
    Q0.weaken (by omega)<|
    Q0.pure<|acc.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dG]
     constructor
     ·rintro ⟨p,hpS,hlt,hzs⟩;exact ⟨p,hpS,by omega,hzs⟩
     ·rintro ⟨p,hpS,hlt,hzs⟩
      refine ⟨p,hpS,?_,hzs⟩
      by_contra hge
      have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
      rw [heq] at hpS
      exact hmem hpS).bind fun _ _ vres=>
  Q0.pure<|vres.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dG,qi,Finset.mem_biUnion]
   exact ⟨fun ⟨p,hpS,_,hzs⟩=>⟨p,hpS,hzs⟩,fun ⟨p,hpS,hzs⟩=>⟨p,hpS,p.isLt,hzs⟩⟩
noncomputable def gx {nIn:ℕ} (c:CB nIn) {k m:ℕ} (r:ℕ)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p)))
  (S:Finset (Fin k)) :
  Q0 nIn c (250*(k+m+2)^3)
   (fun c'=>∀ p:Fin k,Q9 nIn c' (k+m+2) (fun x=>qL r (fA x) (fB x) S p)):=
 let Wc:=k+m+2
 have hWc1:1 ≤ Wc:=by dsimp [Wc];omega
 have hmWc:m < 2^Wc:=lt_of_le_of_lt (by omega) (jp (k+m))
 have hkWc:k < 2^Wc:=lt_of_le_of_lt (by omega) (jp (k+m))
 Q0.weaken (by
  dsimp only [Wc]
  set N:=k+m+2
  have hkN:k+2 ≤ N:=by omega
  have hmN:m+2 ≤ N:=by omega
  have h2N:2 ≤ N:=by omega
  have hN2:N^2=N*N:=by ring
  have hN3:N^3=N*(N*N):=by ring
  have hmm:m*m ≤ N*N:=Nat.mul_le_mul (by omega) (by omega)
  have hkmm:k*(m*m) ≤ N*(N*N):=Nat.mul_le_mul (by omega) hmm
  have hmmm:m*(m*m) ≤ N*(N*N):=Nat.mul_le_mul (by omega) hmm
  have hkm:k*m ≤ N*N:=Nat.mul_le_mul (by omega) (by omega)
  have hkk:k*k ≤ N*N:=Nat.mul_le_mul (by omega) (by omega)
  have hkN2:k*(k*N) ≤ N*(N*N):=Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) le_rfl)
  have hN2leN3:N*N ≤ N*(N*N):=Nat.le_mul_of_pos_left _ (by omega)
  have h1:k*(1+k) ≤ N*N:=by nlinarith
  have h2:m*m+k*(42*m*m+12*m) ≤ 55*(N*(N*N)):=by
   have ha:k*(42*m*m+12*m)=42*(k*(m*m))+12*(k*m):=by ring
   linarith
  have h3:3*(m*m)+m*(56*m*m+11*m) ≤ 70*(N*(N*N)):=by
   have ha:m*(56*m*m+11*m)=56*(m*(m*m))+11*(m*m):=by ring
   linarith
  have h4:N*2+m*(1+N*15) ≤ 18*(N*N):=by nlinarith
  have h5:k*(k*1+(N*2+k*(1+N*15))+(1+N*11)) ≤ 31*(N*(N*N)):=by
   have ha:k*(k*1+(N*2+k*(1+N*15))+(1+N*11)) =
     15*(k*(k*N))+2*(k*k)+13*(k*N)+k:=by ring
   have hkN1:k*N ≤ N*N:=Nat.mul_le_mul (by omega) le_rfl
   have hkN3:k ≤ N*(N*N):=by nlinarith
   linarith
  have hk10:k*(1+0) ≤ N*N:=by nlinarith
  rw [hN3];linarith)<|
 (gm c r scopes S).bind fun c1 h1 poolS=>
 (gm c1 r (fun p=>(scopes p).lift h1) Sᶜ).bind fun c2 h2 poolSc=>
 let h02:=CB.q0 h1 h2
 (j8 k (fun x z=>decide (z∈qi r (fA x) (fB x) S∩qi r (fA x) (fB x) Sᶜ)) c2
  fun z c3 h3=>
   (vg c3 ((poolS.at z).lift (CB.q0 h2 h3)) ((poolSc.at z).lift h3)).bind fun _ _ vand=>
   Q0.pure<|vand.cast fun x=>by
    apply Bool.eq_iff_iff.mpr;simp).bind fun c3 h3 cutPool=>
 let h03:=CB.q0 h02 h3
 (gK c3 (fun p=>(Ab p).lift h03) (fun p=>(Bb p).lift h03) S).bind fun c4 h4 T_L=>
 let h04:=CB.q0 h03 h4
 (gK c4 (fun p=>(Ab p).lift h04) (fun p=>(Bb p).lift h04) Sᶜ).bind fun c5 h5 T_R=>
 (yA c5 (T_L.lift h5) T_R).bind fun c6 h6 ⟨_,_,T_int⟩=>
 (dv c6 hWc1 hmWc T_int).bind fun c7 h7 rankInt=>
 let h37:=CB.q0 h4 (CB.q0 h5 (CB.q0 h6 h7))
 let h07:=CB.q0 h03 h37
 let Acc (j:ℕ) (_:j ≤ k) (c8:CB nIn):Type:=
  ∀ p:Fin k,p.val < j->Q9 nIn c8 Wc (fun x=>qL r (fA x) (fB x) S p)
 have hinit:Acc 0 (Nat.zero_le k) c7:=fun _ hp=>absurd hp (by omega)
 (Q0.qe (Bstep:=k*1+(Wc*2+k*(1+Wc*15))+(1+Wc*11)) k Acc c7 hinit
  fun j hj c8 h8 acc=>
  Q0.weaken (by omega)<|
  let pj:Fin k:=⟨j,hj⟩
  let h08:=CB.q0 h07 h8
  (j8 k (fun x z=>decide (z∈(qi r (fA x) (fB x) S∩qi r (fA x) (fB x) Sᶜ)∪qq r (fA x) (fB x) pj)) c8
   fun z c9 h9=>
    (yr c9 ((cutPool.at z).lift (CB.q0 h37 (CB.q0 h8 h9)))
     (((scopes pj).at z).lift (CB.q0 h08 h9))).bind fun _ _ vor=>
    Q0.pure<|vor.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp).bind fun c9 h9 unionP=>
  (gP c9 hWc1 hkWc unionP).bind fun c10 h10 cardP=>
  have hsum:∀ x,
    (Finset.univ.filter (fun z:Fin k=>
     decide (z∈(qi r (fA x) (fB x) S∩qi r (fA x) (fB x) Sᶜ)∪qq r (fA x) (fB x) pj)=true)).card +
    q3 (vv (vV (fA x) (fB x) S) (vV (fA x) (fB x) Sᶜ)).2.2 < 2^Wc:=by
   intro x
   have hc1:(Finset.univ.filter (fun z:Fin k=>
     decide (z∈(qi r (fA x) (fB x) S∩qi r (fA x) (fB x) Sᶜ)∪qq r (fA x) (fB x) pj)=true)).card ≤ k:=
    (Finset.card_le_univ _).trans (by simp)
   have hc2:q3 (vv (vV (fA x) (fB x) S) (vV (fA x) (fB x) Sᶜ)).2.2 ≤ m:=
    (Finset.card_le_univ _).trans (by simp)
   exact lt_of_le_of_lt (by omega) (jp (k+m))
  (z4 c10 cardP (rankInt.lift (CB.q0 h8 (CB.q0 h9 h10))) hsum).bind fun c11 h11 costP=>
  let hall:=CB.q0 h9 (CB.q0 h10 h11)
  Q0.pure fun p hp=>
   if hlt:p.val < j then (acc p hlt).lift hall
   else
    have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
    heq▸costP.cast fun x=>by
     rw [z9 r (fA x) (fB x) S pj]
     congr 1;congr 1;ext z;simp).bind fun _ _ costs=>
 Q0.pure fun p=>costs p p.isLt
noncomputable def qP (k h s:ℕ):List (Finset (Fin k)):=
 ((qz k h).filter (fun S=>S.card=s)).toList
lemma jy (k h:ℕ) :
  (∑ t∈Finset.range (k+1),(qP k h (k - t)).length)=(qz k h).card:=by
 have hmaps:∀ S∈qz k h,S.card∈Finset.range (k+1):=by
  intro S _
  rw [Finset.mem_range]
  have hle:S.card ≤ k:=by simpa using Finset.card_le_univ S
  omega
 have hfib:=Finset.card_eq_sum_card_fiberwise hmaps
 rw [hfib]
 have href:=Finset.sum_range_reflect (fun s=>((qz k h).filter (fun S=>S.card=s)).card) (k+1)
 have heq:∑ t∈Finset.range (k+1),(qP k h (k - t)).length =
   ∑ t∈Finset.range (k+1),((qz k h).filter (fun S=>S.card=k+1 - 1 - t)).card:=by
  refine Finset.sum_congr rfl fun t _=>?_
  simp only [qP,Finset.length_toList,Nat.add_sub_cancel]
 rw [heq,href]
lemma vG {k h s:ℕ} {S:Finset (Fin k)} :
  S∈qP k h s ↔ S∈qz k h/\S.card=s:=by
 simp [qP]
noncomputable def d9 {nIn:ℕ} (c:CB nIn) {k m:ℕ} (hk:0 < k) (r h:ℕ)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p))) :
  Q0 nIn c (2*k^(2*h)*(300*(k+m+2)^3))
   (fun c'=>
    (∀ S:Finset (Fin k),S∈qz k h ->
     Q9 nIn c' (k+m+2) (fun x=>qQ r h (fA x) (fB x) S)) ×
    (∀ S:Finset (Fin k),S∈qz k h->∀ p:Fin k,
     Q9 nIn c' (k+m+2) (fun x=>qL r (fA x) (fB x) S p))):=
 let Wc:=k+m+2
 let BS:=300*Wc^3
 have hsum_le:(∑ t∈Finset.range (k+1),(qP k h (k - t)).length*BS) ≤
   2*k^(2*h)*BS:=by
  rw [← Finset.sum_mul,jy]
  exact Nat.mul_le_mul_right BS (yO hk)
 Q0.weaken hsum_le<|
 let Acc (u:ℕ) (_:u ≤ k+1) (c1:CB nIn):Type:=
  (∀ S:Finset (Fin k),S∈qz k h->k - S.card < u ->
   Q9 nIn c1 Wc (fun x=>qQ r h (fA x) (fB x) S)) ×
  (∀ S:Finset (Fin k),S∈qz k h->k - S.card < u->∀ p:Fin k,
   Q9 nIn c1 Wc (fun x=>qL r (fA x) (fB x) S p))
 have hinit:Acc 0 (Nat.zero_le (k+1)) c:=
  ⟨fun _ _ hlt=>absurd hlt (by omega),fun _ _ hlt _=>absurd hlt (by omega)⟩
 (Q0.gU (fun t=>(qP k h (k - t)).length*BS) (k+1) Acc c hinit
  fun t ht c1 h1 ⟨prevDP,prevSC⟩=>
  let L:=qP k h (k - t)
  let LAcc (idx:ℕ) (hidxL:idx ≤ L.length) (c2:CB nIn):Type:=
   (∀ (i:ℕ) (hi:i < idx),
    Q9 nIn c2 Wc (fun x=>qQ r h (fA x) (fB x) (L[i]'(lt_of_lt_of_le hi hidxL)))) ×
   (∀ (i:ℕ) (hi:i < idx) (p:Fin k),
    Q9 nIn c2 Wc (fun x=>qL r (fA x) (fB x) (L[i]'(lt_of_lt_of_le hi hidxL)) p))
  have hLinit:LAcc 0 (Nat.zero_le L.length) c1:=
   ⟨fun _ hi=>absurd hi (by omega),fun _ hi _=>absurd hi (by omega)⟩
  Q0.weaken (by dsimp only [L];omega)<|
  (Q0.qe (Bstep:=BS) L.length LAcc c1 hLinit fun idx hidx c2 h2 ⟨curDP,curSC⟩=>
   let S:=L[idx]'hidx
   have hSm:S∈qz k h/\S.card=k - t:=
    vG.mp (List.getElem_mem hidx)
   let h02:=CB.q0 h1 h2
   have hBS_ge:250*Wc^3+(Wc+k*((1+Wc*14)+(1+Wc*14))) ≤ BS:=by
    dsimp only [BS,Wc]
    set N:=k+m+2
    have hkN:k+2 ≤ N:=by omega
    have h2N:2 ≤ N:=by omega
    have hN3:N^3=N*(N*N):=by ring
    have hN2le3:N*N ≤ N*(N*N):=Nat.le_mul_of_pos_left _ (by omega)
    have hrest:N+k*((1+N*14)+(1+N*14)) ≤ 50*(N*N):=by nlinarith
    rw [hN3];linarith
   Q0.weaken hBS_ge<|
   (gx c2 r (fun p=>(Ab p).lift h02) (fun p=>(Bb p).lift h02)
    (fun p=>(scopes p).lift h02) S).bind fun c3 h3 costsS=>
   match ht0:t with
   | 0=>
    Q0.weaken (by omega)<|
    (qS c3 Wc 0 (Nat.two_pow_pos Wc)).bind fun c4 h4 v0=>
    let dpS:Q9 nIn c4 Wc (fun x=>qQ r h (fA x) (fB x) S):=
     v0.cast fun x=>by
      have hSc:S.card=k:=by rw [hSm.2,ht0];omega
      simp [qQ,hSc,jg]
    let h24:=CB.q0 h3 h4
    Q0.pure
     ⟨fun i hi=>
      if hlt:i < idx then (curDP i hlt).lift h24
      else
       have heq:i=idx:=by omega
       dpS.cast fun x=>by congr 1;simp only [S,heq],
     fun i hi p=>
      if hlt:i < idx then (curSC i hlt p).lift h24
      else
       have heq:i=idx:=by omega
       ((costsS p).lift h4).cast fun x=>by congr 1;simp only [S,heq]⟩
   | t'+1=>
    Q0.weaken (by omega)<|
    (qS c3 Wc (k+m+1) (jp (k+m))).bind fun c4 h4 vinf=>
    let pVal (j:ℕ) (x:Fin nIn->Bool):ℕ:=
     ((dF k).take j).foldl (fun acc p=>
      if p∉S/\vi (insert p S) ≤ h then
       min acc (max (qL r (fA x) (fB x) S p) (jg r h (fA x) (fB x) t' (insert p S)))
      else acc) (k+m+1)
    let PAcc (j:ℕ) (_:j ≤ k) (c5:CB nIn):Type:=
     Q9 nIn c5 Wc (pVal j)
    have hPinit:PAcc 0 (Nat.zero_le k) c4:=vinf.cast (fun _=>by simp [pVal])
    (Q0.qe (Bstep:=(1+Wc*14)+(1+Wc*14)) k PAcc c4 hPinit fun j hj c5 h5 accP=>
     let pj:Fin k:=⟨j,hj⟩
     have htake:(dF k).take (j+1)=(dF k).take j ++ [pj]:=by
      rw [dJ (by simp;omega)];simp [pj]
     if hok:pj∉S/\vi (insert pj S) ≤ h then
      have hinsV:insert pj S∈qz k h:=
       Finset.mem_filter.mpr ⟨dL _,hok.2⟩
      have hSc_lt:S.card < k:=by
       have:S.card < (insert pj S).card:=by rw [Finset.card_insert_of_notMem hok.1];omega
       exact lt_of_lt_of_le this (by simpa using Finset.card_le_univ (insert pj S))
      have hinsSub:k - (insert pj S).card=t':=by
       rw [Finset.card_insert_of_notMem hok.1,hSm.2,ht0];omega
      have h15:=CB.q0 h2 (CB.q0 h3 (CB.q0 h4 h5))
      let dpIns:Q9 nIn c5 Wc (fun x=>jg r h (fA x) (fB x) t' (insert pj S)):=
       ((prevDP (insert pj S) hinsV (by omega)).lift h15).cast fun x=>by
        simp only [qQ,hinsSub]
      Q0.weaken (by omega)<|
      (dh c5 ((costsS pj).lift (CB.q0 h4 h5)) dpIns).bind fun c6 h6 vmx=>
      (dA c6 (accP.lift h6) vmx).bind fun _ _ vmn=>
      Q0.pure<|vmn.cast fun x=>by
       simp only [pVal,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,hok,
        not_false_eq_true,and_self,↓reduceIte]
     else
      Q0.weaken (by omega)<|
      Q0.pure<|accP.cast fun x=>by
       simp only [pVal,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,hok,↓reduceIte]).bind
     fun cF hF dpS0=>
    let h2F:=CB.q0 h3 (CB.q0 h4 hF)
    let dpS:Q9 nIn cF Wc (fun x=>qQ r h (fA x) (fB x) S):=
     dpS0.cast fun x=>by
      have hsub:k - S.card=t'+1:=by rw [hSm.2,ht0];omega
      simp only [pVal,qQ,hsub,jg,show (dF k).take k=dF k by simp]
    Q0.pure
     ⟨fun i hi=>
      if hlt:i < idx then (curDP i hlt).lift h2F
      else
       have heq:i=idx:=by omega
       dpS.cast fun x=>by congr 1;simp only [S,heq],
     fun i hi p=>
      if hlt:i < idx then (curSC i hlt p).lift h2F
      else
       have heq:i=idx:=by omega
       ((costsS p).lift (CB.q0 h4 hF)).cast fun x=>by congr 1;simp only [S,heq]⟩).bind fun cL hL ⟨layerDP,layerSC⟩=>
  Q0.pure
   ⟨fun S hS hlt=>
    if hprev:k - S.card < t then (prevDP S hS hprev).lift hL
    else
     have hcard:S.card=k - t:=by
      have hle:S.card ≤ k:=by simpa using Finset.card_le_univ S
      omega
     have hmemL:S∈L:=vG.mpr ⟨hS,hcard⟩
     let idx:=L.idxOf S
     have hidx:idx < L.length:=List.idxOf_lt_length_iff.mpr hmemL
     have hget:L[idx]'hidx=S:=List.getElem_idxOf hidx
     (layerDP idx hidx).cast fun x=>by rw [hget],
   fun S hS hlt p=>
    if hprev:k - S.card < t then (prevSC S hS hprev p).lift hL
    else
     have hcard:S.card=k - t:=by
      have hle:S.card ≤ k:=by simpa using Finset.card_le_univ S
      omega
     have hmemL:S∈L:=vG.mpr ⟨hS,hcard⟩
     let idx:=L.idxOf S
     have hidx:idx < L.length:=List.idxOf_lt_length_iff.mpr hmemL
     have hget:L[idx]'hidx=S:=List.getElem_idxOf hidx
     (layerSC idx hidx p).cast fun x=>by rw [hget]⟩).bind fun _ _ ⟨allDP,allSC⟩=>
 Q0.pure
  ⟨fun S hS=>allDP S hS (by omega),
  fun S hS p=>allSC S hS (by omega) p⟩
lemma y5 {α:Type*} [LinearOrder α] (L:List α)
  (hsorted:L.Pairwise (· < ·)) (P:α->Prop) [DecidablePred P] (d:α)
  (hex:∃ a∈L,P a) (x:α) (hx:x∈L) :
  L.foldr (fun y acc=>if P y then y else acc) d=x ↔
   P x/\∀ y∈L,y < x->¬ P y:=by
 obtain ⟨hmem,hP,hmin⟩:=z6 L hsorted P d hex
 set r:=L.foldr (fun y acc=>if P y then y else acc) d
 constructor
 ·rintro rfl
  refine ⟨hP,fun y hy hlt hPy=>?_⟩
  exact absurd (hmin y hy hPy) (not_le_of_gt hlt)
 ·rintro ⟨hPx,hnone⟩
  apply le_antisymm
  ·exact hmin x hx hPx
  ·by_contra hlt
   push Not at hlt
   exact hnone r hmem hlt hP
noncomputable def gZ {nIn:ℕ} (c:CB nIn) {k m:ℕ}
  (r h:ℕ) (hk:0 < k) (hh:0 < h)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (dpW:∀ S:Finset (Fin k),S∈qz k h ->
   Q9 nIn c (k+m+2) (fun x=>qQ r h (fA x) (fB x) S))
  (scW:∀ S:Finset (Fin k),S∈qz k h->∀ p:Fin k,
   Q9 nIn c (k+m+2) (fun x=>qL r (fA x) (fB x) S p)) :
  Q0 nIn c (2*k^(2*h)*(40*(k+m+2)^2)+k*k+1)
   (fun c'=>∀ i:Fin k,Q2 nIn c' k (fun x p=>decide (qW hk r h (fA x) (fB x) i=p))):=
 let Wc:=k+m+2
 have hempV:(∅:Finset (Fin k))∈qz k h:=
  Finset.mem_filter.mpr ⟨dL _,by simp [yn]⟩
 let optW:=dpW ∅ hempV
 let BStep (step:ℕ):ℕ:=
  (qP k h step).length*(k*(3+Wc*24)+(1+k*4)+k) +
  k*(1+(qP k h step).length) +
  (qP k h (step+1)).length*(1+k)
 have hsum_le:1+(∑ step∈Finset.range k,BStep step) ≤
   2*k^(2*h)*(40*Wc^2)+k*k+1:=by
  have hsum1:∑ step∈Finset.range k,(qP k h step).length ≤ (qz k h).card:=by
   have htot:=jy k h
   have hrev:∑ step∈Finset.range (k+1),(qP k h step).length=(qz k h).card:=by
    rw [← htot]
    have:=Finset.sum_range_reflect (fun s=>(qP k h s).length) (k+1)
    simpa [Nat.add_sub_cancel] using this.symm
   rw [← hrev,Finset.sum_range_succ]
   omega
  have hsum2:∑ step∈Finset.range k,(qP k h (step+1)).length ≤ (qz k h).card:=by
   have htot:=jy k h
   have hrev:∑ step∈Finset.range (k+1),(qP k h step).length=(qz k h).card:=by
    rw [← htot]
    have:=Finset.sum_range_reflect (fun s=>(qP k h s).length) (k+1)
    simpa [Nat.add_sub_cancel] using this.symm
   rw [← hrev,Finset.sum_range_succ']
   omega
  have hvc:(qz k h).card ≤ 2*k^(2*h):=yO hk
  set C1:=k*(3+Wc*24)+(1+k*4)+k+k
  set C2:=1+k
  have hsplit:∑ step∈Finset.range k,BStep step =
    (∑ step∈Finset.range k,(qP k h step).length)*C1 +
    (∑ step∈Finset.range k,(qP k h (step+1)).length)*C2 +
    k*k:=by
   simp only [BStep,C1,C2]
   rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
   have ha:∑ step∈Finset.range k,k*(1+(qP k h step).length) =
     k*k+(∑ step∈Finset.range k,(qP k h step).length)*k:=by
    have h1:∀ step,k*(1+(qP k h step).length)=k+(qP k h step).length*k:=by
     intro step;ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,← Finset.sum_mul]
   rw [← Finset.sum_mul,← Finset.sum_mul,ha]
   ring
  rw [hsplit]
  have hcoeff:C1+C2 ≤ 40*Wc^2:=by
   dsimp only [C1,C2,Wc]
   set N:=k+m+2
   have hkN:k+2 ≤ N:=by omega
   have h2N:2 ≤ N:=by omega
   nlinarith
  have hmul1:(∑ step∈Finset.range k,(qP k h step).length)*C1 +
    (∑ step∈Finset.range k,(qP k h (step+1)).length)*C2 ≤
    (qz k h).card*(C1+C2):=by
   conv_rhs=>rw [Nat.mul_add]
   exact Nat.add_le_add (Nat.mul_le_mul_right C1 hsum1) (Nat.mul_le_mul_right C2 hsum2)
  have hmul2:(qz k h).card*(C1+C2) ≤ 2*k^(2*h)*(40*Wc^2):=
   Nat.mul_le_mul hvc hcoeff
  omega
 Q0.weaken hsum_le<|
 (vJ c true).bind fun c0 h0 vtrue=>
 let Acc (step:ℕ) (_:step ≤ k) (c1:CB nIn):Type:=
  (∀ S:Finset (Fin k),S∈qz k h->S.card=step ->
   Q4 nIn c1 (fun x=>decide (qj hk r h (fA x) (fB x) step=S))) ×
  (∀ i:Fin k,i.val < step ->
   Q2 nIn c1 k (fun x p=>decide (qW hk r h (fA x) (fB x) i=p)))
 have hinit:Acc 0 (Nat.zero_le k) c0:=
  ⟨fun S _ hcard=>
   vtrue.cast fun _=>by
    have hSe:S=∅:=Finset.card_eq_zero.mp hcard
    simp [qj,hSe],
  fun _ hi=>absurd hi (by omega)⟩
 (Q0.gU BStep k Acc c0 hinit fun step hstep c1 h1 ⟨actCur,ordCur⟩=>
  let L0:=qP k h step
  let L1:=qP k h (step+1)
  let BPickS:=k*(3+Wc*24)+(1+k*4)+k
  Q0.weaken (by dsimp only [BStep,BPickS,L0,L1];omega)<|
  let PickAcc (idx:ℕ) (hidxL:idx ≤ L0.length) (c2:CB nIn):Type:=
   ∀ (i:ℕ) (hi:i < idx),
    Q2 nIn c2 k (fun x p=>
     decide (qj hk r h (fA x) (fB x) step=L0[i]'(lt_of_lt_of_le hi hidxL) /\
      jV hk r h (fA x) (fB x) (L0[i]'(lt_of_lt_of_le hi hidxL)) (qQ r h (fA x) (fB x) ∅)=p))
  have hPinit:PickAcc 0 (Nat.zero_le L0.length) c1:=fun _ hi=>absurd hi (by omega)
  (Q0.qe (Bstep:=BPickS) L0.length PickAcc c1 hPinit fun idx hidx c2 h2 pickPrev=>
   Q0.weaken (by dsimp only [BPickS];omega)<|
   let S:=L0[idx]'hidx
   have hSm:S∈qz k h/\S.card=step:=vG.mp (List.getElem_mem hidx)
   let okPred (x:Fin nIn->Bool) (p:Fin k):Bool:=
    decide (p∉S/\vi (insert p S) ≤ h /\
     max (qL r (fA x) (fB x) S p) (qQ r h (fA x) (fB x) (insert p S)) ≤ qQ r h (fA x) (fB x) ∅)
   let h02:=CB.q0 h0 (CB.q0 h1 h2)
   (j8 (Bstep:=3+Wc*24) k okPred c2 fun p c3 h3=>
    let h03:=CB.q0 h02 h3
    if hsp:p∉S/\vi (insert p S) ≤ h then
     have hinsV:insert p S∈qz k h:=Finset.mem_filter.mpr ⟨dL _,hsp.2⟩
     Q0.weaken (by omega)<|
     (dh c3 ((scW S hSm.1 p).lift h03) ((dpW (insert p S) hinsV).lift h03)).bind fun c4 h4 vmx=>
     (dt c4 vmx (optW.lift (CB.q0 h03 h4))).bind fun _ _ vle=>
     Q0.pure<|vle.cast fun x=>by
      apply Bool.eq_iff_iff.mpr;simp [okPred,hsp]
    else
     Q0.weaken (by omega)<|
     (vJ c3 false).bind fun _ _ vf=>
     Q0.pure<|vf.cast fun x=>by
      apply Bool.eq_iff_iff.mpr
      simp only [okPred,Bool.false_eq_true,dG,false_iff]
      intro ⟨h1',h2',_⟩;exact hsp ⟨h1',h2'⟩).bind fun c3 h3 vOk=>
   (vJ c3 false).bind fun c4 h4 vfalse=>
   let FAcc (j:ℕ) (_:j ≤ k) (c5:CB nIn):Type:=
    Q4 nIn c5 (fun x=>decide (∃ q:Fin k,q.val < j/\okPred x q=true)) ×
    (∀ p:Fin k,p.val < j ->
     Q4 nIn c5 (fun x=>decide (okPred x p=true/\∀ q:Fin k,q < p->okPred x q ≠ true)))
   have hFinit:FAcc 0 (Nat.zero_le k) c4:=
    ⟨vfalse.cast (fun _=>by simp),fun _ hp=>absurd hp (by omega)⟩
   (Q0.qe (Bstep:=4) k FAcc c4 hFinit fun j hj c5 h5 ⟨vSeen,vFirst⟩=>
    Q0.weaken (by omega)<|
    let pj:Fin k:=⟨j,hj⟩
    let okj:=(vOk.at pj).lift (CB.q0 h4 h5)
    (y2 c5 vSeen).bind fun c6 h6 vNSeen=>
    (vg c6 (okj.lift h6) vNSeen).bind fun c7 h7 vPick=>
    (yr c7 (vSeen.lift (CB.q0 h6 h7)) (okj.lift (CB.q0 h6 h7))).bind fun c8 h8 vSeen'=>
    let h58:=CB.q0 h6 (CB.q0 h7 h8)
    Q0.pure
     ⟨vSeen'.cast fun x=>by
       apply Bool.eq_iff_iff.mpr
       simp only [dH,dG]
       constructor
       ·rintro (⟨q,hq,hok⟩ | hok)
        ·exact ⟨q,by omega,hok⟩
        ·exact ⟨pj,by dsimp [pj];omega,hok⟩
       ·rintro ⟨q,hq,hok⟩
        by_cases hlt:q.val < j
        ·left;exact ⟨q,hlt,hok⟩
        ·right
         have heq:q=pj:=Fin.ext (by dsimp [pj];omega)
         rwa [← heq],
     fun p hp=>
       if hlt:p.val < j then (vFirst p hlt).lift h58
       else
        have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
        heq▸(vPick.lift h8).cast fun x=>by
         apply Bool.eq_iff_iff.mpr
         simp only [dI,Bool.not_eq_true',decide_eq_false_iff_not,
          dG,not_exists,not_and]
         constructor
         ·rintro ⟨hok,hno⟩
          exact ⟨hok,fun q hqp=>hno q hqp⟩
         ·rintro ⟨hok,hno⟩
          exact ⟨hok,fun q hqj=>hno q hqj⟩⟩).bind fun c5 h5 ⟨_,vFirst⟩=>
   let h25:=CB.q0 h3 (CB.q0 h4 h5)
   let actS:=(actCur S hSm.1 hSm.2).lift (CB.q0 h2 h25)
   (j8 (Bstep:=1) k (fun x p=>decide (qj hk r h (fA x) (fB x) step=S /\
     jV hk r h (fA x) (fB x) S (qQ r h (fA x) (fB x) ∅)=p)) c5 fun p c6 h6=>
    (vg c6 (actS.lift h6) ((vFirst p p.isLt).lift h6)).bind fun _ _ vand=>
    Q0.pure<|vand.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dI,dG]
     constructor
     ·rintro ⟨hSt,hok,hnone⟩
      refine ⟨hSt,?_⟩
      have hinv:=ju hk hh r (fA x) (fB x) step (Nat.le_of_lt hstep)
      have hdp:qQ r h (fA x) (fB x) S ≤ qQ r h (fA x) (fB x) ∅:=hSt▸hinv.2.2.1
      have hlt_km:qQ r h (fA x) (fB x) S ≤ k+m:=
       hdp.trans (yd hk hh r (fA x) (fB x))
      obtain ⟨q,hq1,hq2,hq3⟩:=
       yc r h (fA x) (fB x) S (by omega) hlt_km
      have hex:∃ a∈dF k,a∉S/\vi (insert a S) ≤ h /\
        max (qL r (fA x) (fB x) S a) (qQ r h (fA x) (fB x) (insert a S)) ≤
         qQ r h (fA x) (fB x) ∅:=
       ⟨q,List.mem_finRange q,hq1,hq2,hq3.trans hdp⟩
      rw [jV,y5 (dF k) (jH k) _ ⟨0,hk⟩ hex p
       (List.mem_finRange p)]
      refine ⟨?_,fun q _ hqp hqok=>hnone q hqp (by simp only [okPred,dG];exact hqok)⟩
      simpa only [okPred,dG] using hok
     ·rintro ⟨hSt,hbn⟩
      refine ⟨hSt,?_⟩
      have hinv:=ju hk hh r (fA x) (fB x) step (Nat.le_of_lt hstep)
      have hdp:qQ r h (fA x) (fB x) S ≤ qQ r h (fA x) (fB x) ∅:=hSt▸hinv.2.2.1
      have hlt_km:qQ r h (fA x) (fB x) S ≤ k+m:=
       hdp.trans (yd hk hh r (fA x) (fB x))
      obtain ⟨q,hq1,hq2,hq3⟩:=
       yc r h (fA x) (fB x) S (by omega) hlt_km
      have hex:∃ a∈dF k,a∉S/\vi (insert a S) ≤ h /\
        max (qL r (fA x) (fB x) S a) (qQ r h (fA x) (fB x) (insert a S)) ≤
         qQ r h (fA x) (fB x) ∅:=
       ⟨q,List.mem_finRange q,hq1,hq2,hq3.trans hdp⟩
      have hiff:=(y5 (dF k) (jH k) _ ⟨0,hk⟩ hex p
       (List.mem_finRange p)).mp hbn
      refine ⟨by simp only [okPred,dG];exact hiff.1,fun q hqp hqok=>?_⟩
      exact hiff.2 q (List.mem_finRange q) hqp (by simpa only [okPred,dG] using hqok)).bind fun c6 h6 vPickS=>
   let h26:=CB.q0 h25 h6
   Q0.pure fun i hi=>
    if hlt:i < idx then (pickPrev i hlt).lift h26
    else
     have heq:i=idx:=by omega
     vPickS.cast fun x p=>by congr 1;simp only [S,heq]).bind fun cP hP picks=>
  (j8 (Bstep:=1+L0.length) k (fun x p=>decide (qW hk r h (fA x) (fB x) ⟨step,hstep⟩=p)) cP fun p c2 h2=>
   Q0.weaken (by omega)<|
   (vJ c2 false).bind fun c3 h3 vfalse=>
   let OAcc (j:ℕ) (hjL:j ≤ L0.length) (c4:CB nIn):Type:=
    Q4 nIn c4 (fun x=>decide (∃ (i:ℕ) (hi:i < j),
     qj hk r h (fA x) (fB x) step=L0[i]'(lt_of_lt_of_le hi hjL) /\
     jV hk r h (fA x) (fB x) (L0[i]'(lt_of_lt_of_le hi hjL)) (qQ r h (fA x) (fB x) ∅)=p))
   have hOinit:OAcc 0 (Nat.zero_le L0.length) c3:=vfalse.cast fun _=>by simp
   (Q0.qe (Bstep:=1) L0.length OAcc c3 hOinit fun j hj c4 h4 acc=>
    (yr c4 acc (((picks j hj).at p).lift (CB.q0 h2 (CB.q0 h3 h4)))).bind fun _ _ vor=>
    Q0.pure<|vor.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dH,dG]
     constructor
     ·rintro (⟨i,hi,h1',h2'⟩ | ⟨h1',h2'⟩)
      ·exact ⟨i,by omega,h1',h2'⟩
      ·exact ⟨j,by omega,h1',h2'⟩
     ·rintro ⟨i,hi,h1',h2'⟩
      by_cases hlt:i < j
      ·left;exact ⟨i,hlt,h1',h2'⟩
      ·right
       have heq:i=j:=by omega
       subst heq;exact ⟨h1',h2'⟩).bind fun _ _ vres=>
   Q0.pure<|vres.cast fun x=>by
    apply Bool.eq_iff_iff.mpr
    simp only [dG]
    constructor
    ·rintro ⟨i,hi,hSt,hbn⟩
     unfold qW
     dsimp only
     rw [hSt];exact hbn
    ·intro hbo
     have hinv:=ju hk hh r (fA x) (fB x) step (Nat.le_of_lt hstep)
     have hmem:qj hk r h (fA x) (fB x) step∈L0:=
      vG.mpr ⟨Finset.mem_filter.mpr ⟨dL _,hinv.2.1⟩,hinv.1⟩
     obtain ⟨i,hi,hget⟩:=List.mem_iff_getElem.mp hmem
     refine ⟨i,hi,hget.symm,?_⟩
     rw [hget];exact hbo).bind fun cO hO ordStep=>
  let NAcc (idx:ℕ) (hidxL:idx ≤ L1.length) (c2:CB nIn):Type:=
   ∀ (i:ℕ) (hi:i < idx),
    Q4 nIn c2 (fun x=>decide (qj hk r h (fA x) (fB x) (step+1)=L1[i]'(lt_of_lt_of_le hi hidxL)))
  have hNinit:NAcc 0 (Nat.zero_le L1.length) cO:=fun _ hi=>absurd hi (by omega)
  (Q0.qe (Bstep:=1+k) L1.length NAcc cO hNinit fun idx hidx c2 h2 actNPrev=>
   Q0.weaken (by omega)<|
   let S':=L1[idx]'hidx
   have hS'm:S'∈qz k h/\S'.card=step+1:=vG.mp (List.getElem_mem hidx)
   (vJ c2 false).bind fun c3 h3 vfalse=>
   let EAcc (j:ℕ) (_:j ≤ k) (c4:CB nIn):Type:=
    Q4 nIn c4 (fun x=>decide (∃ p:Fin k,p.val < j/\p∈S'/\S'.erase p∈qz k h /\
     qj hk r h (fA x) (fB x) step=S'.erase p /\
     jV hk r h (fA x) (fB x) (S'.erase p) (qQ r h (fA x) (fB x) ∅)=p))
   have hEinit:EAcc 0 (Nat.zero_le k) c3:=vfalse.cast fun _=>by simp
   (Q0.qe (Bstep:=1) k EAcc c3 hEinit fun j hj c4 h4 acc=>
    let pj:Fin k:=⟨j,hj⟩
    if hpre:pj∈S'/\S'.erase pj∈qz k h then
     have hcardE:(S'.erase pj).card=step:=by
      rw [Finset.card_erase_of_mem hpre.1,hS'm.2];omega
     have hmemL0:S'.erase pj∈L0:=vG.mpr ⟨hpre.2,hcardE⟩
     let idx0:=L0.idxOf (S'.erase pj)
     have hidx0:idx0 < L0.length:=List.idxOf_lt_length_iff.mpr hmemL0
     have hget0:L0[idx0]'hidx0=S'.erase pj:=List.getElem_idxOf hidx0
     let hP4:=CB.q0 hO (CB.q0 h2 (CB.q0 h3 h4))
     (yr c4 acc (((picks idx0 hidx0).at pj).lift hP4)).bind fun _ _ vor=>
     Q0.pure<|vor.cast fun x=>by
      apply Bool.eq_iff_iff.mpr
      simp only [dH,dG,hget0]
      constructor
      ·rintro (⟨p,hp,h1',h2',h3',h4'⟩ | ⟨h3',h4'⟩)
       ·exact ⟨p,by omega,h1',h2',h3',h4'⟩
       ·exact ⟨pj,by dsimp [pj];omega,hpre.1,hpre.2,h3',h4'⟩
      ·rintro ⟨p,hp,h1',h2',h3',h4'⟩
       by_cases hlt:p.val < j
       ·left;exact ⟨p,hlt,h1',h2',h3',h4'⟩
       ·right
        have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
        subst heq;exact ⟨h3',h4'⟩
    else
     Q0.weaken (by omega)<|
     Q0.pure<|acc.cast fun x=>by
      apply Bool.eq_iff_iff.mpr
      simp only [dG]
      constructor
      ·rintro ⟨p,hp,h1',h2',h3',h4'⟩;exact ⟨p,by omega,h1',h2',h3',h4'⟩
      ·rintro ⟨p,hp,h1',h2',h3',h4'⟩
       refine ⟨p,?_,h1',h2',h3',h4'⟩
       by_contra hge
       have heq:p=pj:=Fin.ext (by dsimp [pj];omega)
       rw [heq] at h1' h2'
       exact hpre ⟨h1',h2'⟩).bind fun c4 h4 vres=>
   let h24:=CB.q0 h3 h4
   let actS':Q4 nIn c4 (fun x=>decide (qj hk r h (fA x) (fB x) (step+1)=S')):=
    vres.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dG]
     constructor
     ·rintro ⟨p,_,hpS',_,hSt,hbn⟩
      dsimp only [qj]
      rw [hSt,hbn,Finset.insert_erase hpS']
     ·intro heq
      have hinv:=ju hk hh r (fA x) (fB x) (step+1) hstep
      have hinv0:=ju hk hh r (fA x) (fB x) step (Nat.le_of_lt hstep)
      set p:=jV hk r h (fA x) (fB x) (qj hk r h (fA x) (fB x) step) (qQ r h (fA x) (fB x) ∅)
      have hp_not:p∉qj hk r h (fA x) (fB x) step:=(hinv.2.2.2.2 ⟨step,hstep⟩ (by dsimp;omega)).1
      have hpS':p∈S':=by rw [← heq];exact Finset.mem_insert_self p _
      have her:S'.erase p=qj hk r h (fA x) (fB x) step:=by
       rw [← heq];exact Finset.erase_insert hp_not
      refine ⟨p,p.isLt,hpS',?_,her.symm,by rw [her]⟩
      rw [her];exact Finset.mem_filter.mpr ⟨dL _,hinv0.2.1⟩
   Q0.pure fun i hi=>
    if hlt:i < idx then (actNPrev i hlt).lift h24
    else
     have heq:i=idx:=by omega
     actS'.cast fun x=>by congr 1;simp only [S',heq]).bind fun cN hN actNext=>
  let h1N:=CB.q0 hP (CB.q0 hO hN)
  Q0.pure
   ⟨fun S' hS' hcard=>
    have hmem:S'∈L1:=vG.mpr ⟨hS',hcard⟩
    let idx:=L1.idxOf S'
    have hidx:idx < L1.length:=List.idxOf_lt_length_iff.mpr hmem
    have hget:L1[idx]'hidx=S':=List.getElem_idxOf hidx
    (actNext idx hidx).cast fun x=>by rw [hget],
   fun i hi=>
    if hlt:i.val < step then (ordCur i hlt).lift h1N
    else
     have heq:i=⟨step,hstep⟩:=Fin.ext (by dsimp;omega)
     heq▸(ordStep.lift hN)⟩).bind fun _ _ ⟨_,ordAll⟩=>
 Q0.pure fun i=>ordAll i i.isLt
noncomputable def df {nIn:ℕ} (c:CB nIn) {k m:ℕ}
  (r h:ℕ) (hk:0 < k) (hh:0 < h)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p)) :
  Q0 nIn c (700*k^(2*h)*(k+m+2)^3)
   (fun c'=>
    Q9 nIn c' (k+m+2) (fun x=>qQ r h (fA x) (fB x) ∅) ×
    (∀ i:Fin k,Q2 nIn c' k (fun x p=>decide (qW hk r h (fA x) (fB x) i=p)))):=
 have hbound:(1+k*(2*m+3))+(2*k^(2*h)*(300*(k+m+2)^3) +
   ((2*k^(2*h)*(40*(k+m+2)^2)+k*k+1)+0)) ≤
   700*k^(2*h)*(k+m+2)^3:=by
  have hpow:1 ≤ k^(2*h):=Nat.one_le_pow _ _ hk
  set N:=k+m+2
  have hkN:k+2 ≤ N:=by omega
  have hmN:m+2 ≤ N:=by omega
  have h2N:2 ≤ N:=by omega
  have hN3:N^3=N*(N*N):=by ring
  have hN2:N^2=N*N:=by ring
  have hN2le3:N*N ≤ N*(N*N):=Nat.le_mul_of_pos_left _ (by omega)
  have h1:1+k*(2*m+3)+(k*k+1) ≤ 6*(N*N):=by nlinarith
  have h2:40*N^2 ≤ 20*N^3:=by rw [hN2,hN3];nlinarith
  have h3:6*N^3 ≤ 6*k^(2*h)*N^3:=by
   calc 6*N^3=6*1*N^3:=by ring
    _ ≤ 6*k^(2*h)*N^3:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 hpow)
  have h4:2*k^(2*h)*(40*N^2) ≤ 2*k^(2*h)*(20*N^3):=
   Nat.mul_le_mul_left _ h2
  have h1':1+k*(2*m+3)+(k*k+1) ≤ 6*N^3:=by rw [hN3];linarith
  calc (1+k*(2*m+3))+(2*k^(2*h)*(300*N^3) +
     ((2*k^(2*h)*(40*N^2)+k*k+1)+0))
    = (1+k*(2*m+3)+(k*k+1))+2*k^(2*h)*(300*N^3) +
     2*k^(2*h)*(40*N^2):=by ring
   _ ≤ 6*k^(2*h)*N^3+2*k^(2*h)*(300*N^3) +
     2*k^(2*h)*(20*N^3):=by linarith
   _ ≤ 700*k^(2*h)*N^3:=by
     have h646:6*k^(2*h)*N^3+2*k^(2*h)*(300*N^3) +
      2*k^(2*h)*(20*N^3)=646*(k^(2*h)*N^3):=by ring
     have h700:700*k^(2*h)*N^3=700*(k^(2*h)*N^3):=by ring
     rw [h646,h700]
     exact Nat.mul_le_mul_right _ (by decide)
 Q0.weaken hbound<|
 (gn c r Ab Bb).bind fun c1 h1 scopes=>
 (d9 c1 hk r h (fun p=>(Ab p).lift h1) (fun p=>(Bb p).lift h1) scopes).bind fun c2 h2 ⟨dpW,scW⟩=>
 (gZ c2 r h hk hh dpW scW).bind fun c3 h3 ordOH=>
 have hempV:(∅:Finset (Fin k))∈qz k h:=
  Finset.mem_filter.mpr ⟨dL _,by simp [yn]⟩
 Q0.pure ⟨(dpW ∅ hempV).lift h3,ordOH⟩
lemma qd (a x:ℕ):((List.range a).map (fun i=>x.testBit i)).length=a:=by
 simp
lemma yk (a x i:ℕ) (hi:i < a) :
  ((List.range a).map (fun t=>x.testBit t)).getD i false=x.testBit i:=by
 simp [List.getD,hi]
lemma qp {k m:ℕ} (A:Fin k->Fin (2^m)) :
  ((dF k).flatMap (fun p=>(List.range m).map (fun i=>(A p).val.testBit i))).length=k*m:=by
 rw [List.length_flatMap]
 simp [List.map_const',List.sum_replicate]
lemma z3 {k m:ℕ} (A:Fin k->Fin (2^m)) (p:Fin k) (q:Fin m) :
  ((dF k).flatMap (fun p'=>(List.range m).map (fun i=>(A p').val.testBit i))).getD (p.val*m+q.val) false =
   (A p).val.testBit q.val:=by
 have hrec:∀ (L:List (Fin k)) (t:ℕ) (ht:t < L.length),
   (L.flatMap (fun p'=>(List.range m).map (fun i=>(A p').val.testBit i))).getD (t*m+q.val) false =
    (A (L[t]'ht)).val.testBit q.val:=by
  intro L
  induction L with
  | nil=>intro _ ht;cases ht
  | cons a as ih=>
   intro t ht
   rw [List.flatMap_cons]
   cases t with
   | zero=>
    simp only [zero_mul,zero_add,List.getElem_cons_zero]
    have hlen:((List.range m).map (fun i=>(A a).val.testBit i)).length=m:=by simp
    simp only [List.getD,List.getElem?_append_left (by rw [hlen];exact q.isLt)]
    simp [q.isLt]
   | succ t'=>
    have hlen:((List.range m).map (fun i=>(A a).val.testBit i)).length=m:=by simp
    have hge:m ≤ (t'+1)*m+q.val:=by nlinarith [q.isLt]
    unfold List.getD
    rw [List.getElem?_append_right (by rw [hlen];exact hge),hlen]
    have hsub:(t'+1)*m+q.val - m=t'*m+q.val:=by
     rw [Nat.add_mul,one_mul];omega
    rw [hsub]
    have hih:=ih t' (by simpa using ht)
    simpa [List.getD] using hih
 have h1:=hrec (dF k) p.val (by simp)
 simpa using h1
lemma yp {k:ℕ} (a b:Fin k)
  (h:∀ t:Fin k,a.val.testBit t.val=b.val.testBit t.val):a=b:=by
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro t
 by_cases ht:t < k
 ·exact h ⟨t,ht⟩
 ·have ha:a.val < 2^t:=a.isLt.trans (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp ht)))
  have hb:b.val < 2^t:=b.isLt.trans (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp ht)))
  rw [Nat.testBit_lt_two_pow ha,Nat.testBit_lt_two_pow hb]
noncomputable def zF (k r m h:ℕ) (hk:0 < k) (hh:0 < h) :
  Q0 (2*k*m+2*k) (CB.zO (2*k*m+2*k))
   (800*k^(2*h)*(k+m+2)^3)
   (fun c'=>Q4 (2*k*m+2*k) c' fun x=>
    let fA:Fin k->Q1 m:=fun p q=>
     x ⟨p.val*m+q.val,by have:=p.isLt;have:=q.isLt;nlinarith⟩
    let fB:Fin k->Q1 m:=fun p q=>
     x ⟨k*m+p.val*m+q.val,by have:=p.isLt;have:=q.isLt;nlinarith⟩
    let fI:Fin k->Bool:=fun t=>x ⟨2*k*m+t.val,by have:=t.isLt;omega⟩
    let fJ:Fin k->Bool:=fun t=>x ⟨2*k*m+k+t.val,by have:=t.isLt;omega⟩
    decide (∃ j0:Fin k,fJ=(fun t:Fin k=>j0.val.testBit t.val) /\
     ∃ p:Fin k,p.val.testBit j0.val=true /\
      ∃ i0:Fin k,fI=(fun t:Fin k=>i0.val.testBit t.val) /\
       qW hk r h fA fB i0=p)):=
 let nIn:=2*k*m+2*k
 let c0:=CB.zO nIn
 let fA:(Fin nIn->Bool)->Fin k->Q1 m:=fun x p q=>
  x ⟨p.val*m+q.val,by dsimp [nIn];have:=p.isLt;have:=q.isLt;nlinarith⟩
 let fB:(Fin nIn->Bool)->Fin k->Q1 m:=fun x p q=>
  x ⟨k*m+p.val*m+q.val,by dsimp [nIn];have:=p.isLt;have:=q.isLt;nlinarith⟩
 let fI:(Fin nIn->Bool)->Fin k->Bool:=fun x t=>
  x ⟨2*k*m+t.val,by dsimp [nIn];have:=t.isLt;omega⟩
 let fJ:(Fin nIn->Bool)->Fin k->Bool:=fun x t=>
  x ⟨2*k*m+k+t.val,by dsimp [nIn];have:=t.isLt;omega⟩
 let Ab0:∀ p:Fin k,Q2 nIn c0 m (fun x=>fA x p):=fun p=>
  ⟨fun q=>p.val*m+q.val,fun q=>by dsimp [nIn,c0,CB.zO];have:=p.isLt;have:=q.isLt;nlinarith,
  fun x q=>(Q4.input c0 ⟨p.val*m+q.val,by dsimp [nIn];have:=p.isLt;have:=q.isLt;nlinarith⟩).heval x⟩
 let Bb0:∀ p:Fin k,Q2 nIn c0 m (fun x=>fB x p):=fun p=>
  ⟨fun q=>k*m+p.val*m+q.val,fun q=>by dsimp [nIn,c0,CB.zO];have:=p.isLt;have:=q.isLt;nlinarith,
  fun x q=>(Q4.input c0 ⟨k*m+p.val*m+q.val,by dsimp [nIn];have:=p.isLt;have:=q.isLt;nlinarith⟩).heval x⟩
 let vI0:Q2 nIn c0 k fI:=
  ⟨fun t=>2*k*m+t.val,fun t=>by dsimp [nIn,c0,CB.zO];have:=t.isLt;omega,
  fun x t=>(Q4.input c0 ⟨2*k*m+t.val,by dsimp [nIn];have:=t.isLt;omega⟩).heval x⟩
 let vJ0:Q2 nIn c0 k fJ:=
  ⟨fun t=>2*k*m+k+t.val,fun t=>by dsimp [nIn,c0,CB.zO];have:=t.isLt;omega,
  fun x t=>(Q4.input c0 ⟨2*k*m+k+t.val,by dsimp [nIn];have:=t.isLt;omega⟩).heval x⟩
 have htot:700*k^(2*h)*(k+m+2)^3 +
   (k*(k*1+(1+k*6))+(k*(k*1+(1+k*6)) +
    (k*(1+k*2)+(k*(1+k*1)+(1+(k*2+0)))))) ≤
   800*k^(2*h)*(k+m+2)^3:=by
  have h1le:1 ≤ k^(2*h):=Nat.one_le_pow _ _ hk
  set N:=k+m+2
  have hkN:k+2 ≤ N:=by omega
  have h2N:2 ≤ N:=by omega
  have hN3:N^3=N*(N*N):=by ring
  have hN2le3:N*N ≤ N*(N*N):=Nat.le_mul_of_pos_left _ (by omega)
  have hsmall:k*(k*1+(1+k*6))+(k*(k*1+(1+k*6)) +
    (k*(1+k*2)+(k*(1+k*1)+(1+(k*2+0))))) ≤ 100*(N*N):=by nlinarith
  have hmul:100*N^3 ≤ 100*k^(2*h)*N^3:=by
   calc 100*N^3=100*1*N^3:=by ring
    _ ≤ 100*k^(2*h)*N^3:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 100 h1le)
  have hsmall':k*(k*1+(1+k*6))+(k*(k*1+(1+k*6)) +
    (k*(1+k*2)+(k*(1+k*1)+(1+(k*2+0))))) ≤ 100*k^(2*h)*N^3:=by
   calc _ ≤ 100*(N*N):=hsmall
    _ ≤ 100*N^3:=by rw [hN3];linarith
    _ ≤ 100*k^(2*h)*N^3:=hmul
  have h800:700*k^(2*h)*N^3+100*k^(2*h)*N^3=800*k^(2*h)*N^3:=by ring
  linarith
 Q0.weaken htot<|
 (df c0 r h hk hh Ab0 Bb0).bind fun c1 h1 ⟨_,ordOH⟩=>
 (j8 (Bstep:=k*1+(1+k*6)) k (fun x i0=>decide (fI x=fun t:Fin k=>i0.val.testBit t.val)) c1 fun i0 c2 h2=>
  (vq c2 k (fun t:Fin k=>i0.val.testBit t.val)).bind fun c3 h3 ci0=>
  (gF c3 (vI0.lift (CB.q0 h1 (CB.q0 h2 h3))) ci0)).bind fun c2 h2 eqI=>
 (j8 (Bstep:=k*1+(1+k*6)) k (fun x j0=>decide (fJ x=fun t:Fin k=>j0.val.testBit t.val)) c2 fun j0 c3 h3=>
  (vq c3 k (fun t:Fin k=>j0.val.testBit t.val)).bind fun c4 h4 cj0=>
  (gF c4 (vJ0.lift (CB.q0 h1 (CB.q0 h2 (CB.q0 h3 h4)))) cj0)).bind fun c3 h3 eqJ=>
 (j8 (Bstep:=1+k*2) k (fun x p=>decide (∃ i0:Fin k,fI x=(fun t:Fin k=>i0.val.testBit t.val) /\
   qW hk r h (fA x) (fB x) i0=p)) c3 fun p c4 h4=>
  Q0.weaken (by omega)<|
  (vJ c4 false).bind fun c5 h5 vfalse=>
  let Acc (s:ℕ) (_:s ≤ k) (c6:CB nIn):Type:=
   Q4 nIn c6 (fun x=>decide (∃ i0:Fin k,i0.val < s/\fI x=(fun t:Fin k=>i0.val.testBit t.val) /\
    qW hk r h (fA x) (fB x) i0=p))
  have hinit:Acc 0 (Nat.zero_le k) c5:=vfalse.cast fun _=>by simp
  (Q0.qe (Bstep:=2) k Acc c5 hinit fun s hs c6 h6 acc=>
   let si:Fin k:=⟨s,hs⟩
   let h26:=CB.q0 h3 (CB.q0 h4 (CB.q0 h5 h6))
   let h16:=CB.q0 h2 h26
   (vg c6 ((eqI.at si).lift h26) (((ordOH si).at p).lift h16)).bind fun c7 h7 vand=>
   (yr c7 (acc.lift h7) vand).bind fun _ _ vor=>
   Q0.pure<|vor.cast fun x=>by
    apply Bool.eq_iff_iff.mpr
    simp only [dH,dI,dG]
    constructor
    ·rintro (⟨i0,hi0,h1',h2'⟩ | ⟨h1',h2'⟩)
     ·exact ⟨i0,by omega,h1',h2'⟩
     ·exact ⟨si,by dsimp [si];omega,h1',h2'⟩
    ·rintro ⟨i0,hi0,h1',h2'⟩
     by_cases hlt:i0.val < s
     ·left;exact ⟨i0,hlt,h1',h2'⟩
     ·right
      have heq:i0=si:=Fin.ext (by dsimp [si];omega)
      subst heq;exact ⟨h1',h2'⟩).bind fun _ _ vres=>
  Q0.pure<|vres.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dG]
   exact ⟨fun ⟨i0,_,h1',h2'⟩=>⟨i0,h1',h2'⟩,fun ⟨i0,h1',h2'⟩=>⟨i0,i0.isLt,h1',h2'⟩⟩).bind fun c4 h4 oiOH=>
 (j8 (Bstep:=1+k*1) k (fun x j0=>decide (∃ p:Fin k,p.val.testBit j0.val=true /\
   ∃ i0:Fin k,fI x=(fun t:Fin k=>i0.val.testBit t.val) /\
    qW hk r h (fA x) (fB x) i0=p)) c4 fun j0 c5 h5=>
  Q0.weaken (by omega)<|
  (vJ c5 false).bind fun c6 h6 vfalse=>
  let Acc (s:ℕ) (_:s ≤ k) (c7:CB nIn):Type:=
   Q4 nIn c7 (fun x=>decide (∃ p:Fin k,p.val < s/\p.val.testBit j0.val=true /\
    ∃ i0:Fin k,fI x=(fun t:Fin k=>i0.val.testBit t.val) /\
     qW hk r h (fA x) (fB x) i0=p))
  have hinit:Acc 0 (Nat.zero_le k) c6:=vfalse.cast fun _=>by simp
  (Q0.qe (Bstep:=1) k Acc c6 hinit fun s hs c7 h7 acc=>
   let sp:Fin k:=⟨s,hs⟩
   if htb:sp.val.testBit j0.val=true then
    (yr c7 acc ((oiOH.at sp).lift (CB.q0 h5 (CB.q0 h6 h7)))).bind fun _ _ vor=>
    Q0.pure<|vor.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dH,dG]
     constructor
     ·rintro (⟨p,hp,h1',h2'⟩ | h2')
      ·exact ⟨p,by omega,h1',h2'⟩
      ·exact ⟨sp,by dsimp [sp];omega,htb,h2'⟩
     ·rintro ⟨p,hp,h1',h2'⟩
      by_cases hlt:p.val < s
      ·left;exact ⟨p,hlt,h1',h2'⟩
      ·right
       have heq:p=sp:=Fin.ext (by dsimp [sp];omega)
       subst heq;exact h2'
   else
    Q0.weaken (by omega)<|
    Q0.pure<|acc.cast fun x=>by
     apply Bool.eq_iff_iff.mpr
     simp only [dG]
     constructor
     ·rintro ⟨p,hp,h1',h2'⟩;exact ⟨p,by omega,h1',h2'⟩
     ·rintro ⟨p,hp,h1',h2'⟩
      refine ⟨p,?_,h1',h2'⟩
      by_contra hge
      have heq:p=sp:=Fin.ext (by dsimp [sp];omega)
      rw [heq] at h1'
      exact htb h1').bind fun _ _ vres=>
  Q0.pure<|vres.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dG]
   exact ⟨fun ⟨p,_,h1',h2'⟩=>⟨p,h1',h2'⟩,fun ⟨p,h1',h2'⟩=>⟨p,p.isLt,h1',h2'⟩⟩).bind fun c5 h5 bitJ=>
 (vJ c5 false).bind fun c6 h6 vfalse=>
 let FAcc (s:ℕ) (_:s ≤ k) (c7:CB nIn):Type:=
  Q4 nIn c7 (fun x=>decide (∃ j0:Fin k,j0.val < s/\fJ x=(fun t:Fin k=>j0.val.testBit t.val) /\
   ∃ p:Fin k,p.val.testBit j0.val=true /\
    ∃ i0:Fin k,fI x=(fun t:Fin k=>i0.val.testBit t.val) /\
     qW hk r h (fA x) (fB x) i0=p))
 have hFinit:FAcc 0 (Nat.zero_le k) c6:=vfalse.cast fun _=>by simp
 (Q0.qe (Bstep:=2) k FAcc c6 hFinit fun s hs c7 h7 acc=>
  let sj:Fin k:=⟨s,hs⟩
  let h37:=CB.q0 h4 (CB.q0 h5 (CB.q0 h6 h7))
  let h57:=CB.q0 h6 h7
  (vg c7 ((eqJ.at sj).lift h37) ((bitJ.at sj).lift h57)).bind fun c8 h8 vand=>
  (yr c8 (acc.lift h8) vand).bind fun _ _ vor=>
  Q0.pure<|vor.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dH,dI,dG]
   constructor
   ·rintro (⟨j0,hj0,h1',h2'⟩ | ⟨h1',h2'⟩)
    ·exact ⟨j0,by omega,h1',h2'⟩
    ·exact ⟨sj,by dsimp [sj];omega,h1',h2'⟩
   ·rintro ⟨j0,hj0,h1',h2'⟩
    by_cases hlt:j0.val < s
    ·left;exact ⟨j0,hlt,h1',h2'⟩
    ·right
     have heq:j0=sj:=Fin.ext (by dsimp [sj];omega)
     subst heq;exact ⟨h1',h2'⟩).bind fun _ _ vout=>
 Q0.pure<|vout.cast fun x=>by
  apply Bool.eq_iff_iff.mpr
  simp only [dG]
  exact ⟨fun ⟨j0,_,h1',h2'⟩=>⟨j0,h1',h2'⟩,fun ⟨j0,h1',h2'⟩=>⟨j0,j0.isLt,h1',h2'⟩⟩
noncomputable def gi (k r m h:ℕ) (hk:0 < k) (hh:0 < h) :
  {C:PEqualNP.CircuitLowerBounds.Circuit //
   PEqualNP.MetaComplexity.FanInTwo C /\
   PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k*m+2*k) C /\
   C.size ≤ 2^48*(k+r+m+5)^(4*h+16) /\
   ∀ (A B:Fin k->Fin (2^m)) (i j:Fin k),
    let Ab:Fin k->Q1 m:=fun p q=>(A p).val.testBit q.val
    let Bb:Fin k->Q1 m:=fun p q=>(B p).val.testBit q.val
    let bits:=fun (a x:ℕ)=>(List.range a).map (fun t=>x.testBit t)
    let pack:=fun (X:Fin k->Fin (2^m))=>(dF k).flatMap (fun p=>bits m (X p).val)
    C.eval (pack A ++ pack B ++ bits k i.val ++ bits k j.val) =
     (qW hk r h Ab Bb i).val.testBit j.val }:=by
 let nIn:=2*k*m+2*k
 let res:=zF k r m h hk hh
 let C:PEqualNP.CircuitLowerBounds.Circuit:=⟨res.c'.gates,res.val.w⟩
 refine ⟨C,?_,?_,?_,?_⟩
 ·intro g hg;exact res.c'.fanIn g hg
 ·intro j hj i hi
  have hgd:PEqualNP.MetaComplexity.NestedCover.gateAt C j=res.c'.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[]⟩:=by
   simp [PEqualNP.MetaComplexity.NestedCover.gateAt,C,List.getD,hj]
  rw [hgd] at hi
  exact res.c'.reads j hj i hi
 ·have hsz:C.size ≤ 800*k^(2*h)*(k+m+2)^3:=by
   have h1:=res.hsize
   simpa [C,PEqualNP.CircuitLowerBounds.Circuit.size,CB.zO] using h1
  have hN:k+m+2 ≤ k+r+m+5:=by omega
  have hkN:k ≤ k+r+m+5:=by omega
  have hpow1:k^(2*h) ≤ (k+r+m+5)^(4*h):=
   (Nat.pow_le_pow_left hkN (2*h)).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hpow2:(k+m+2)^3 ≤ (k+r+m+5)^16:=
   (Nat.pow_le_pow_left hN 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc C.size ≤ 800*k^(2*h)*(k+m+2)^3:=hsz
   _ ≤ 2^48*(k+r+m+5)^(4*h)*(k+r+m+5)^16:=
     Nat.mul_le_mul (Nat.mul_le_mul (by decide) hpow1) hpow2
   _=2^48*(k+r+m+5)^(4*h+16):=by rw [mul_assoc,← pow_add]
 ·intro A B i j
  dsimp only
  set bits:=fun (a x:ℕ)=>(List.range a).map (fun t=>x.testBit t)
  set pack:=fun (X:Fin k->Fin (2^m))=>(dF k).flatMap (fun p=>bits m (X p).val)
  set inp:=pack A ++ pack B ++ bits k i.val ++ bits k j.val
  have hinp_len:inp.length=nIn:=by
   simp only [inp,pack,bits,List.length_append,qp,qd,nIn];ring
  let x:Fin nIn->Bool:=fun idx=>inp.getD idx.val false
  have hofFn:List.ofFn x=inp:=by
   apply List.ext_getElem
   ·simp [hinp_len]
   ·intro t ht1 ht2
    simp only [List.getElem_ofFn,x,List.getD,List.getElem?_eq_getElem ht2,Option.getD_some]
  have h2km:2*k*m=k*m+k*m:=by ring
  have hfA:(fun (p:Fin k) (q:Fin m)=>x ⟨p.val*m+q.val,by dsimp [nIn];have:=p.isLt;have:=q.isLt;nlinarith⟩) =
    fun p q=>(A p).val.testBit q.val:=by
   funext p q
   simp only [x,inp,List.append_assoc,List.getD]
   have hlt:p.val*m+q.val < (pack A).length:=by
    rw [qp];have:=p.isLt;have:=q.isLt;nlinarith
   rw [List.getElem?_append_left hlt]
   exact z3 A p q
  have hfB:(fun (p:Fin k) (q:Fin m)=>x ⟨k*m+p.val*m+q.val,by dsimp [nIn];have:=p.isLt;have:=q.isLt;nlinarith⟩) =
    fun p q=>(B p).val.testBit q.val:=by
   funext p q
   simp only [x,inp,List.append_assoc,List.getD]
   have hge1:(pack A).length ≤ k*m+p.val*m+q.val:=by rw [qp];omega
   rw [List.getElem?_append_right hge1,qp]
   have hsub1:k*m+p.val*m+q.val - k*m=p.val*m+q.val:=by omega
   rw [hsub1]
   have hlt2:p.val*m+q.val < (pack B).length:=by
    rw [qp];have:=p.isLt;have:=q.isLt;nlinarith
   rw [List.getElem?_append_left hlt2]
   exact z3 B p q
  have hfI:(fun (t:Fin k)=>x ⟨2*k*m+t.val,by dsimp [nIn];have:=t.isLt;omega⟩) =
    fun t=>i.val.testBit t.val:=by
   funext t
   simp only [x,inp,List.append_assoc,List.getD]
   have hge1:(pack A).length ≤ 2*k*m+t.val:=by rw [qp];omega
   rw [List.getElem?_append_right hge1,qp]
   have hsub1:2*k*m+t.val - k*m=k*m+t.val:=by omega
   rw [hsub1]
   have hge2:(pack B).length ≤ k*m+t.val:=by rw [qp];omega
   rw [List.getElem?_append_right hge2,qp]
   have hsub2:k*m+t.val - k*m=t.val:=by omega
   rw [hsub2]
   have hlt3:t.val < (bits k i.val).length:=by rw [qd];exact t.isLt
   rw [List.getElem?_append_left hlt3]
   exact yk k i.val t.val t.isLt
  have hfJ:(fun (t:Fin k)=>x ⟨2*k*m+k+t.val,by dsimp [nIn];have:=t.isLt;omega⟩) =
    fun t=>j.val.testBit t.val:=by
   funext t
   simp only [x,inp,List.append_assoc,List.getD]
   have hge1:(pack A).length ≤ 2*k*m+k+t.val:=by rw [qp];omega
   rw [List.getElem?_append_right hge1,qp]
   have hsub1:2*k*m+k+t.val - k*m=k*m+k+t.val:=by omega
   rw [hsub1]
   have hge2:(pack B).length ≤ k*m+k+t.val:=by rw [qp];omega
   rw [List.getElem?_append_right hge2,qp]
   have hsub2:k*m+k+t.val - k*m=k+t.val:=by omega
   rw [hsub2]
   have hge3:(bits k i.val).length ≤ k+t.val:=by rw [qd];omega
   rw [List.getElem?_append_right hge3,qd]
   have hsub3:k+t.val - k=t.val:=by omega
   rw [hsub3]
   exact yk k j.val t.val t.isLt
  have hev:C.eval inp=res.c'.val (List.ofFn x) res.val.w:=by
   rw [hofFn];rfl
  rw [hev,res.val.heval x]
  dsimp only
  rw [hfA,hfB,hfI,hfJ]
  apply Bool.eq_iff_iff.mpr
  simp only [dG]
  constructor
  ·rintro ⟨j0,hj0,p,hptb,i0,hi0,hpbo⟩
   have hjeq:j=j0:=yp j j0 (fun t=>congrFun hj0 t)
   have hieq:i=i0:=yp i i0 (fun t=>congrFun hi0 t)
   subst hjeq;subst hieq;subst hpbo
   exact hptb
  ·intro htb
   exact ⟨j,rfl,qW hk r h (fun p q=>(A p).val.testBit q.val) (fun p q=>(B p).val.testBit q.val) i,
    htb,i,rfl,rfl⟩
end PlanCircuit
section StateLightCone
def jf (k d w:ℕ):ℕ:=
 ((w <<< (d % k)) ||| (w >>> (k - d % k))) % 2^k
def yV (k w:ℕ):ℕ:=
 (List.range k).foldl (fun acc i=>acc ||| ((xor (w.testBit i)
  (!(w.testBit ((i+1) % k))&&w.testBit ((i+2) % k))).toNat <<< i)) 0
def vI (k r:ℕ) (col:Bool) (w name:ℕ) (c:Fin r->Fin (2^k)):ℕ:=
 let g:=if col then 2 else 1
 (dF r).foldl (fun x j=>
  yV k (x ^^^ jf k g x ^^^ jf k (k - g) x) ^^^
   jf k (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
  (jf k (if col then 3 else 1) w ^^^ name)
lemma g0 (k d w:ℕ):jf k d w < 2^k:=
 Nat.mod_lt _ (Nat.two_pow_pos k)
lemma vn {k:ℕ} (hk:0 < k) {w:ℕ} (hw:w < 2^k) (d i:ℕ) (hi:i < k) :
  (jf k d w).testBit i=w.testBit ((i+k - d % k) % k):=by
 unfold jf
 rw [Nat.testBit_mod_two_pow]
 simp only [hi,decide_true,Bool.true_and,Nat.testBit_or,Nat.testBit_shiftLeft,
  Nat.testBit_shiftRight,ge_iff_le]
 set s:=d % k
 have hs:s < k:=Nat.mod_lt d hk
 by_cases hsi:s ≤ i
 ·have hge:k ≤ k - s+i:=by omega
  have h0:w.testBit (k - s+i)=false:=
   Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right (by omega) hge))
  have hm:(i+k - s) % k=i - s:=by
   have h1:i+k - s=(i - s)+k:=by omega
   rw [h1,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  simp [hsi,h0,hm]
 ·have hlt:i+k - s < k:=by omega
  have hm:(i+k - s) % k=k - s+i:=by
   rw [Nat.mod_eq_of_lt hlt];omega
  simp [hsi,hm]
lemma yq (k w:ℕ) :
  yV k w < 2^k /\
  ∀ i < k,(yV k w).testBit i =
   xor (w.testBit i) (!(w.testBit ((i+1) % k))&&w.testBit ((i+2) % k)):=by
 let f (i:ℕ):Bool:=xor (w.testBit i) (!(w.testBit ((i+1) % k))&&w.testBit ((i+2) % k))
 have hgo:∀ t:ℕ,
   let acc:=(List.range t).foldl (fun acc i=>acc ||| ((f i).toNat <<< i)) 0
   acc < 2^t/\∀ i < t,acc.testBit i=f i:=by
  intro t
  induction t with
  | zero=>
   simp only [List.range_zero,List.foldl_nil,pow_zero]
   exact ⟨by omega,fun _ hi=>absurd hi (by omega)⟩
  | succ t ih=>
   obtain ⟨hlt,hbits⟩:=ih
   dsimp only
   rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set prev:=(List.range t).foldl (fun acc i=>acc ||| ((f i).toNat <<< i)) 0
   have hshift_lt:(f t).toNat <<< t < 2^(t+1):=by
    rw [Nat.shiftLeft_eq,pow_succ]
    cases f t <;> simp <;> have:=Nat.two_pow_pos t <;> omega
   have hprev_lt:prev < 2^(t+1):=hlt.trans (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self t))
   refine ⟨Nat.or_lt_two_pow hprev_lt hshift_lt,fun i hi=>?_⟩
   rw [Nat.testBit_or,Nat.testBit_shiftLeft]
   by_cases hit:i < t
   ·have hnot:¬ (t ≤ i):=by omega
    simp [hnot,hbits i hit]
   ·have heq:i=t:=by omega
    subst heq
    have hprev0:prev.testBit i=false:=Nat.testBit_lt_two_pow hlt
    simp only [hprev0,Bool.false_or,le_refl,decide_true,Bool.true_and,Nat.sub_self]
    cases f i <;> rfl
 exact hgo k
lemma jC {k:ℕ} (hk:0 < k) (p u d:ℕ) (hdu:d ≤ u) :
  ((p+u) % k+k - d % k) % k=(p+(u - d)) % k:=by
 set a:=(p+(u - d)) % k
 set b:=d % k
 have ha:a < k:=Nat.mod_lt _ hk
 have hb:b < k:=Nat.mod_lt _ hk
 have hpu:(p+u) % k=(a+b) % k:=by
  have h1:p+u=p+(u - d)+d:=by omega
  rw [h1,Nat.add_mod]
 rw [hpu]
 by_cases hab:a+b < k
 ·rw [Nat.mod_eq_of_lt hab]
  have h1:a+b+k - b=a+k:=by omega
  rw [h1,Nat.add_mod_right,Nat.mod_eq_of_lt ha]
 ·have hmod:(a+b) % k=a+b - k:=by
   have h1:a+b=(a+b - k)+k:=by omega
   conv_lhs=>rw [h1]
   rw [Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  have h2:a+b - k+k - b=a:=by omega
  rw [h2,Nat.mod_eq_of_lt ha]
lemma ga {k:ℕ} (hk:0 < k) (p u g:ℕ) (hg:g ≤ 2) :
  ((p+u) % k+k - (k - g) % k) % k=(p+u+g) % k:=by
 by_cases hg0:g=0
 ·subst hg0;simp
 ·by_cases hk1:k=1
  ·subst hk1;simp only [Nat.mod_one]
  ·by_cases hk2:k=2
   ·subst hk2
    have hcases:g=1\/g=2:=by omega
    rcases hcases with rfl | rfl <;> omega
   ·have hkg':k - g < k:=by omega
    rw [Nat.mod_eq_of_lt hkg']
    have h1:(p+u) % k+k - (k - g)=(p+u) % k+g:=by omega
    rw [h1,Nat.mod_add_mod]
lemma yQ {k r:ℕ} (hk:0 < k) (hr:4 ≤ r) (col:Bool)
  {w₁ w₂ name:ℕ} (hw₁:w₁ < 2^k) (hw₂:w₂ < 2^k) (hname:name < 2^k)
  (c:Fin r->Fin (2^k)) (p:Fin k)
  (hagree:∀ t:Fin (yy r col+1),
   w₁.testBit ((p.val+t.val) % k)=w₂.testBit ((p.val+t.val) % k)) :
  (vI k r col w₁ name c).testBit ((p.val+vo r col) % k) =
   (vI k r col w₂ name c).testBit ((p.val+vo r col) % k):=by
 have hag:∀ t:ℕ,t ≤ yy r col ->
   w₁.testBit ((p.val+t) % k)=w₂.testBit ((p.val+t) % k):=
  fun t ht=>hagree ⟨t,Nat.lt_succ_of_le ht⟩
 let g:=if col then 2 else 1
 have hg_le:g ≤ 2:=by dsimp [g];cases col <;> simp
 let stepOne (w:ℕ) (x:ℕ) (j:Fin r):ℕ:=
  yV k (x ^^^ jf k g x ^^^ jf k (k - g) x) ^^^
   jf k (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val
 let stAt (w:ℕ) (t:ℕ):ℕ:=
  ((dF r).take t).foldl (stepOne w) (jf k (if col then 3 else 1) w ^^^ name)
 have hst_succ:∀ w t (ht:t < r),stAt w (t+1)=stepOne w (stAt w t) ⟨t,ht⟩:=by
  intro w t ht
  have htake:(dF r).take (t+1)=(dF r).take t ++ [⟨t,ht⟩]:=by
   rw [dJ (by simp;omega)];simp
  simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
 have hst_lt:∀ w t,stAt w t < 2^k:=by
  intro w t
  induction t with
  | zero=>
   simp only [stAt,List.take_zero,List.foldl_nil]
   exact Nat.xor_lt_two_pow (g0 k _ w) hname
  | succ t ih=>
   by_cases ht:t < r
   ·rw [hst_succ w t ht]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (yq k _).1 (g0 k _ w)) (c ⟨t,ht⟩).isLt
   ·have htake:(dF r).take (t+1)=(dF r).take t:=by
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]
    simpa only [stAt,htake] using ih
 have hmix_eq:∀ {x₁ x₂:ℕ} (hx₁:x₁ < 2^k) (hx₂:x₂ < 2^k) (u:ℕ),
   g ≤ u ->
   (∀ d:ℕ,u - g ≤ d->d ≤ u+g+2 ->
    x₁.testBit ((p.val+d) % k)=x₂.testBit ((p.val+d) % k)) ->
   (yV k (x₁ ^^^ jf k g x₁ ^^^ jf k (k - g) x₁)).testBit ((p.val+u) % k) =
    (yV k (x₂ ^^^ jf k g x₂ ^^^ jf k (k - g) x₂)).testBit ((p.val+u) % k):=by
  intro x₁ x₂ hx₁ hx₂ u hgu hxd
  have hlt:=Nat.mod_lt (p.val+u) hk
  rw [(yq k _).2 _ hlt,(yq k _).2 _ hlt]
  have hy:∀ a:ℕ,a ≤ 2 ->
    (x₁ ^^^ jf k g x₁ ^^^ jf k (k - g) x₁).testBit (((p.val+u) % k+a) % k) =
    (x₂ ^^^ jf k g x₂ ^^^ jf k (k - g) x₂).testBit (((p.val+u) % k+a) % k):=by
   intro a ha
   have hpos:((p.val+u) % k+a) % k=(p.val+(u+a)) % k:=by
    rw [Nat.mod_add_mod,add_assoc]
   rw [hpos]
   have hmodlt:=Nat.mod_lt (p.val+(u+a)) hk
   simp only [Nat.testBit_xor]
   rw [vn hk hx₁ _ _ hmodlt,vn hk hx₂ _ _ hmodlt,
     vn hk hx₁ _ _ hmodlt,vn hk hx₂ _ _ hmodlt,
     jC hk p.val (u+a) g (by omega),
     ga hk p.val (u+a) g hg_le]
   rw [hxd (u+a) (by omega) (by omega),
     hxd (u+a - g) (by omega) (by omega),
     show p.val+(u+a)+g=p.val+(u+a+g) by omega,
     hxd (u+a+g) (by omega) (by omega)]
  have hy0:=hy 0 (by omega)
  simp only [add_zero,Nat.mod_mod] at hy0
  rw [hy0,hy 1 (by omega),hy 2 (by omega)]
 cases col
 ·have hind:∀ t:ℕ,t ≤ r ->
    ∀ u:ℕ,r - 2+t ≤ u->u ≤ 5*r - 2 - 3*t ->
     (stAt w₁ t).testBit ((p.val+u) % k)=(stAt w₂ t).testBit ((p.val+u) % k):=by
   intro t
   induction t with
   | zero=>
    intro _ u hlo hhi
    simp only [stAt,List.take_zero,List.foldl_nil,Nat.testBit_xor,Bool.false_eq_true,↓reduceIte]
    have hlt:=Nat.mod_lt (p.val+u) hk
    rw [vn hk hw₁ _ _ hlt,vn hk hw₂ _ _ hlt,
      jC hk p.val u 1 (by omega),
      hag (u - 1) (by dsimp [yy];omega)]
   | succ t ih=>
    intro ht u hlo hhi
    rw [hst_succ w₁ t ht,hst_succ w₂ t ht]
    dsimp only [stepOne]
    simp only [Nat.testBit_xor,Bool.false_eq_true,↓reduceIte]
    have hlt:=Nat.mod_lt (p.val+u) hk
    have hm:=hmix_eq (hst_lt w₁ t) (hst_lt w₂ t) u (by dsimp [g];omega)
     (fun d hd1 hd2=>ih (Nat.le_of_succ_le ht) d (by dsimp [g] at hd1;omega) (by dsimp [g] at hd2;omega))
    rw [hm,vn hk hw₁ _ _ hlt,vn hk hw₂ _ _ hlt,
      jC hk p.val u (2*t) (by omega),
      hag (u - 2*t) (by dsimp [yy];omega)]
  have hfin:=hind r le_rfl (2*r - 2) (by omega) (by omega)
  have htr:(dF r).take r=dF r:=by simp
  simpa [stAt,vI,stepOne,g,vo,htr] using hfin
 ·have hind:∀ t:ℕ,t ≤ r ->
    ∀ u:ℕ,r+1+2*t ≤ u->u ≤ 7*r+1 - 4*t ->
     (stAt w₁ t).testBit ((p.val+u) % k)=(stAt w₂ t).testBit ((p.val+u) % k):=by
   intro t
   induction t with
   | zero=>
    intro _ u hlo hhi
    simp only [stAt,List.take_zero,List.foldl_nil,Nat.testBit_xor,↓reduceIte]
    have hlt:=Nat.mod_lt (p.val+u) hk
    rw [vn hk hw₁ _ _ hlt,vn hk hw₂ _ _ hlt,
      jC hk p.val u 3 (by omega),
      hag (u - 3) (by dsimp [yy];omega)]
   | succ t ih=>
    intro ht u hlo hhi
    rw [hst_succ w₁ t ht,hst_succ w₂ t ht]
    dsimp only [stepOne]
    simp only [Nat.testBit_xor,↓reduceIte]
    have hlt:=Nat.mod_lt (p.val+u) hk
    have hm:=hmix_eq (hst_lt w₁ t) (hst_lt w₂ t) u (by dsimp [g];omega)
     (fun d hd1 hd2=>ih (Nat.le_of_succ_le ht) d (by dsimp [g] at hd1;omega) (by dsimp [g] at hd2;omega))
    rw [hm,vn hk hw₁ _ _ hlt,vn hk hw₂ _ _ hlt,
      jC hk p.val u (3*(t+1)+1) (by omega),
      hag (u - (3*(t+1)+1)) (by dsimp [yy];omega)]
  have hfin:=hind r le_rfl (3*r+1) (by omega) (by omega)
  have htr:(dF r).take r=dF r:=by simp
  simpa [stAt,vI,stepOne,g,vo,htr] using hfin
def g3 {nIn:ℕ} {c:CB nIn} {k:ℕ} (hk:0 < k) (d:ℕ)
  {fw:(Fin nIn->Bool)->ℕ} (hw:∀ x,fw x < 2^k)
  (vw:Q2 nIn c k (fun x i=>(fw x).testBit i.val)) :
  Q2 nIn c k (fun x i=>(jf k d (fw x)).testBit i.val):=
 ⟨fun i=>vw.ws ⟨(i.val+k - d % k) % k,Nat.mod_lt _ hk⟩,
 fun i=>vw.hws _,
 fun x i=>by
  rw [vw.heval x,vn hk (hw x) d i.val i.isLt]⟩
def dw {nIn:ℕ} (c:CB nIn) {k:ℕ} (hk:0 < k)
  {fw:(Fin nIn->Bool)->ℕ}
  (vw:Q2 nIn c k (fun x i=>(fw x).testBit i.val)) :
  Q0 nIn c (k*6) (fun c'=>Q2 nIn c' k (fun x i=>(yV k (fw x)).testBit i.val)):=
 j8 (Bstep:=6) k (fun x i=>(yV k (fw x)).testBit i.val) c fun i c1 h1=>
  Q0.weaken (by omega)<|
  let b0:=(vw.at i).lift h1
  let b1:=(vw.at ⟨(i.val+1) % k,Nat.mod_lt _ hk⟩).lift h1
  let b2:=(vw.at ⟨(i.val+2) % k,Nat.mod_lt _ hk⟩).lift h1
  (y2 c1 b1).bind fun c2 h2 vnb1=>
  (vg c2 vnb1 (b2.lift h2)).bind fun c3 h3 vand=>
  (g2 c3 (b0.lift (CB.q0 h2 h3)) vand).bind fun _ _ vres=>
  Q0.pure<|vres.cast fun x=>((yq k (fw x)).2 i.val i.isLt).symm
def gO {nIn:ℕ} (c:CB nIn) {k r:ℕ} (hk:0 < k) (col:Bool)
  {fw fname:(Fin nIn->Bool)->ℕ} {fc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  (hw:∀ x,fw x < 2^k) (hname:∀ x,fname x < 2^k)
  (vw:Q2 nIn c k (fun x i=>(fw x).testBit i.val))
  (vname:Q2 nIn c k (fun x i=>(fname x).testBit i.val))
  (vc:∀ j:Fin r,Q2 nIn c k (fun x i=>(fc x j).val.testBit i.val)) :
  Q0 nIn c (k*4+r*(k*22))
   (fun c'=>Q2 nIn c' k (fun x i=>(vI k r col (fw x) (fname x) (fc x)).testBit i.val)):=
 Q0.weaken (by omega)<|
 let g:=if col then 2 else 1
 let stepOne (x:Fin nIn->Bool) (acc:ℕ) (j:Fin r):ℕ:=
  yV k (acc ^^^ jf k g acc ^^^ jf k (k - g) acc) ^^^
   jf k (if col then 3*(j.val+1)+1 else 2*j.val) (fw x) ^^^ (fc x j).val
 let stAt (t:ℕ) (x:Fin nIn->Bool):ℕ:=
  ((dF r).take t).foldl (stepOne x) (jf k (if col then 3 else 1) (fw x) ^^^ fname x)
 have hst_lt:∀ t x,stAt t x < 2^k:=by
  intro t x
  induction t with
  | zero=>
   simp only [stAt,List.take_zero,List.foldl_nil]
   exact Nat.xor_lt_two_pow (g0 k _ _) (hname x)
  | succ t ih=>
   by_cases ht:t < r
   ·have htake:(dF r).take (t+1)=(dF r).take t ++ [⟨t,ht⟩]:=by
     rw [dJ (by simp;omega)];simp
    simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,stepOne]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (yq k _).1 (g0 k _ _)) (fc x ⟨t,ht⟩).isLt
   ·have htake:(dF r).take (t+1)=(dF r).take t:=by
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]
    simpa only [stAt,htake] using ih
 let vrot0:=g3 hk (if col then 3 else 1) hw vw
 (j3 c vrot0 vname).bind fun c0 h0 vinit=>
 let Acc (t:ℕ) (_:t ≤ r) (c1:CB nIn):Type:=
  Q2 nIn c1 k (fun x i=>(stAt t x).testBit i.val)
 have hinit:Acc 0 (Nat.zero_le r) c0:=
  vinit.cast fun x i=>by simp only [stAt,List.take_zero,List.foldl_nil,Nat.testBit_xor]
 (Q0.qe (Bstep:=k*22) r Acc c0 hinit fun t ht c1 h1 vx=>
  Q0.weaken (by omega)<|
  let jt:Fin r:=⟨t,ht⟩
  let h01:=CB.q0 h0 h1
  let vrg:=g3 hk g (hst_lt t) vx
  let vrkg:=g3 hk (k - g) (hst_lt t) vx
  (j3 c1 vx vrg).bind fun c2 h2 vx1=>
  (j3 c2 vx1 (vrkg.lift h2)).bind fun c3 h3 vx2=>
  let vx2':Q2 nIn c3 k (fun x i=>(stAt t x ^^^ jf k g (stAt t x) ^^^ jf k (k - g) (stAt t x)).testBit i.val):=
   vx2.cast fun x i=>by simp only [Nat.testBit_xor]
  (dw c3 hk vx2').bind fun c4 h4 vstep=>
  let h04:=CB.q0 h01 (CB.q0 h2 (CB.q0 h3 h4))
  let vrw:=g3 hk (if col then 3*(jt.val+1)+1 else 2*jt.val) hw (vw.lift h04)
  (j3 c4 vstep vrw).bind fun c5 h5 vx3=>
  (j3 c5 vx3 ((vc jt).lift (CB.q0 h04 h5))).bind fun _ _ vres=>
  have htake:(dF r).take (t+1)=(dF r).take t ++ [jt]:=by
   rw [dJ (by simp;omega)];simp [jt]
  Q0.pure<|vres.cast fun x i=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,stepOne,Nat.testBit_xor]).bind
  fun _ _ vF=>
 Q0.pure<|vF.cast fun x i=>by
  simp only [stAt,vI,stepOne,g,show (dF r).take r=dF r by simp]
end StateLightCone
section StaticGL
def qu {B:ℕ} (v:Q1 B):ℕ:=
 ∑ t:Fin B,if v t=true then 2^t.val else 0
lemma ya {B:ℕ} (v:Q1 B):qu v < 2^B:=by
 induction B with
 | zero=>simp [qu]
 | succ n ih=>
  unfold qu
  rw [Fin.sum_univ_castSucc]
  have h1:(∑ i:Fin n,if v i.castSucc=true then 2^i.castSucc.val else 0) < 2^n:=
   ih (fun i=>v i.castSucc)
  have h2:(if v (Fin.last n)=true then 2^(Fin.last n).val else 0) ≤ 2^n:=by
   split_ifs <;> simp
  rw [pow_succ];omega
def qa {B:ℕ} (v:Q1 B):Fin (2^B):=
 ⟨qu v,ya v⟩
def v8 (B:ℕ) (idx:Fin (2^B)):Q1 B:=
 fun t=>idx.val.testBit t.val
lemma qb {B:ℕ} (v:Q1 B) (t:Fin B) :
  (qu v).testBit t.val=v t:=by
 induction B with
 | zero=>exact Fin.elim0 t
 | succ n ih=>
  unfold qu
  rw [Fin.sum_univ_castSucc]
  set lo:=∑ i:Fin n,if v i.castSucc=true then 2^i.val else 0
  have hlo_lt:lo < 2^n:=ya (fun i=>v i.castSucc)
  have hval:(∑ i:Fin n,if v i.castSucc=true then 2^i.castSucc.val else 0) +
    (if v (Fin.last n)=true then 2^(Fin.last n).val else 0) =
    lo+2^n*(v (Fin.last n)).toNat:=by
   simp only [lo,Fin.val_castSucc,Fin.val_last]
   cases v (Fin.last n) <;> simp
  rw [hval]
  by_cases hlt:t.val < n
  ·have ht_eq:t=(⟨t.val,hlt⟩:Fin n).castSucc:=Fin.ext rfl
   rw [ht_eq]
   have hmod:(lo+2^n*(v (Fin.last n)).toNat) % 2^n=lo:=by
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlo_lt]
   have htb:=congrArg (fun a=>a.testBit t.val) hmod
   simp only [Nat.testBit_mod_two_pow,hlt,decide_true,Bool.true_and] at htb
   rw [Fin.val_castSucc,htb]
   exact ih (fun i=>v i.castSucc) ⟨t.val,hlt⟩
  ·have hteq:t=Fin.last n:=Fin.ext (by simp;omega)
   rw [hteq,Fin.val_last]
   rw [Nat.testBit_eq_decide_div_mod_eq]
   have hdiv:(lo+2^n*(v (Fin.last n)).toNat) / 2^n=(v (Fin.last n)).toNat:=by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hlo_lt,zero_add]
   rw [hdiv]
   cases v (Fin.last n) <;> decide
lemma vK {B:ℕ} (v:Q1 B):v8 B (qa v)=v:=by
 funext t;exact qb v t
lemma dE {B:ℕ} (idx:Fin (2^B)):qa (v8 B idx)=idx:=by
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro t
 by_cases ht:t < B
 ·exact qb (v8 B idx) ⟨t,ht⟩
 ·have h1:(qa (v8 B idx)).val < 2^t:=
   (qa _).isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp ht))
  have h2:idx.val < 2^t:=
   idx.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp ht))
  rw [Nat.testBit_lt_two_pow h1,Nat.testBit_lt_two_pow h2]
def j2 {B:ℕ} (u v:Fin B) (x:Q1 B):Q1 B:=
 fun t=>if t=u then x v else if t=v then x u else x t
def zX {B:ℕ} (src dst:Fin B) (x:Q1 B):Q1 B:=
 fun t=>if t=dst then xor (x dst) (x src) else x t
def v6 {B:ℕ} (t:Fin B) (x:Q1 B):Q1 B:=
 fun s=>if s=t then !(x t) else x s
def vY {B:ℕ} (idx:Fin (2^B)) (u v:Fin B):Fin (2^B):=
 qa (j2 u v (v8 B idx))
def zQ {B:ℕ} (idx:Fin (2^B)) (src dst:Fin B):Fin (2^B):=
 qa (zX src dst (v8 B idx))
def jw {B:ℕ} (idx:Fin (2^B)) (t:Fin B):Fin (2^B):=
 qa (v6 t (v8 B idx))
abbrev Qd (B:ℕ):Type:=Fin B->Fin B->Bool
def vT (B:ℕ):Qd B:=fun r c=>decide (r=c)
def yo {α:Type*} (L:List α) (f:α->Bool):Bool:=
 L.foldl (fun acc a=>xor acc (f a)) false
def b2z (b:Bool):ZMod 2:=if b then 1 else 0
lemma gH (a b:Bool):b2z (xor a b)=b2z a+b2z b:=by
 cases a <;> cases b <;> decide
lemma du (a b:Bool):b2z (a&&b)=b2z a*b2z b:=by
 cases a <;> cases b <;> decide
lemma zo {α:Type*} (L:List α) (f:α->Bool) :
  b2z (yo L f)=(L.map (fun a=>b2z (f a))).sum:=by
 have hgen:∀ (init:Bool),
   b2z (L.foldl (fun acc a=>xor acc (f a)) init) =
    b2z init+(L.map (fun a=>b2z (f a))).sum:=by
  induction L with
  | nil=>intro init;simp
  | cons a t ih=>
   intro init
   simp only [List.foldl_cons,List.map_cons,List.sum_cons]
   rw [ih (xor init (f a)),gH,add_assoc]
 have h0:=hgen false
 rw [show b2z false=0 from rfl,zero_add] at h0
 exact h0
def v3 {B:ℕ} (M N:Qd B):Qd B:=
 fun r c=>yo (dF B) (fun t=>M r t&&N t c)
def qT {B:ℕ} (M:Qd B) (v:Q1 B):Q1 B:=
 fun r=>yo (dF B) (fun t=>M r t&&v t)
def qm {B:ℕ} (M:Qd B):Matrix (Fin B) (Fin B) (ZMod 2):=
 fun r c=>b2z (M r c)
lemma yP {m:ℕ} (v:Q1 m) (i:Fin m):q4 v i=b2z (v i):=rfl
lemma y1 {B:ℕ} {M N:Qd B} (h:qm M=qm N):M=N:=by
 funext r c
 have hrc:=congrFun (congrFun h r) c
 simp only [qm,b2z] at hrc
 cases hM:M r c <;> cases hN:N r c <;> simp_all
lemma jj (B:ℕ):qm (vT B)=1:=by
 ext r c
 simp only [qm,b2z,vT,Matrix.one_apply]
 by_cases h:r=c <;> simp [h]
lemma vC {B:ℕ} (M N:Qd B) :
  qm (v3 M N)=qm M*qm N:=by
 ext r c
 change b2z (yo (dF B) (fun t=>M r t&&N t c)) =
  ∑ t:Fin B,b2z (M r t)*b2z (N t c)
 rw [zo,← Fin.sum_univ_def]
 refine Finset.sum_congr rfl fun t _=>du (M r t) (N t c)
lemma vX {B:ℕ} (M:Qd B) (v:Q1 B) :
  q4 (qT M v)=(qm M).mulVec (q4 v):=by
 funext r
 change b2z (yo (dF B) (fun t=>M r t&&v t)) =
  ∑ t:Fin B,b2z (M r t)*b2z (v t)
 rw [zo,← Fin.sum_univ_def]
 refine Finset.sum_congr rfl fun t _=>du (M r t) (v t)
lemma jU {B:ℕ} (A M N:Qd B) :
  v3 (v3 A M) N=v3 A (v3 M N):=by
 apply y1
 simp only [vC,Matrix.mul_assoc]
lemma yv {B:ℕ} (M:Qd B):v3 (vT B) M=M:=by
 apply y1;simp [vC,jj]
lemma vU {B:ℕ} (M:Qd B):v3 M (vT B)=M:=by
 apply y1;simp [vC,jj]
lemma jr {B:ℕ} (M N:Qd B) (v:Q1 B) :
  qT (v3 M N) v=qT M (qT N v):=by
 apply v7
 simp only [vX,vC,Matrix.mulVec_mulVec]
lemma yj {B:ℕ} (v:Q1 B):qT (vT B) v=v:=by
 apply v7;simp [vX,jj]
def Q7 {B:ℕ} (M:Qd B):Prop:=
 ∃ N:Qd B,v3 M N=vT B
lemma g7 {B:ℕ} {M N:Qd B} (h:v3 M N=vT B) :
  v3 N M=vT B:=by
 apply y1
 rw [vC,jj]
 have h1:qm M*qm N=1:=by rw [← vC,h,jj]
 have hdet:(qm M).det*(qm N).det=1:=by rw [← Matrix.det_mul,h1,Matrix.det_one]
 have hu:IsUnit (qm M).det:=isUnit_iff_exists_inv.mpr ⟨_,hdet⟩
 have hlinv:(qm M)⁻¹*qm M=1:=Matrix.nonsing_inv_mul _ hu
 have hNeq:qm N=(qm M)⁻¹:=by
  calc qm N=1*qm N:=(Matrix.one_mul _).symm
   _=((qm M)⁻¹*qm M)*qm N:=by rw [hlinv]
   _=(qm M)⁻¹*(qm M*qm N):=Matrix.mul_assoc _ _ _
   _=(qm M)⁻¹:=by rw [h1,Matrix.mul_one]
 rw [hNeq,hlinv]
def qJ {B:ℕ} (M:Qd B) (u v:Fin B):Qd B:=
 fun r c=>if c=u then M r v else if c=v then M r u else M r c
def vD {B:ℕ} (M:Qd B) (src dst:Fin B):Qd B:=
 fun r c=>if c=dst then xor (M r dst) (M r src) else M r c
lemma jX {B:ℕ} (A M:Qd B) (u v:Fin B) :
  v3 A (qJ M u v)=qJ (v3 A M) u v:=by
 funext r c
 dsimp only [qJ]
 by_cases hcu:c=u
 ·subst hcu;simp [v3,qJ]
 ·by_cases hcv:c=v
  ·subst hcv;simp [v3,qJ,hcu]
  ·simp [v3,qJ,hcu,hcv]
lemma ye {B:ℕ} (A M:Qd B) (src dst:Fin B) :
  v3 A (vD M src dst)=vD (v3 A M) src dst:=by
 apply y1
 ext r c
 rw [vC]
 by_cases hcd:c=dst
 ·subst hcd
  simp only [qm,vD,↓reduceIte,Matrix.mul_apply,gH]
  have h1:=congrFun (congrFun (vC A M) r) c
  have h2:=congrFun (congrFun (vC A M) r) src
  simp only [qm,Matrix.mul_apply] at h1 h2
  rw [h1,h2,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _=>by ring
 ·simp only [qm,vD,hcd,↓reduceIte,Matrix.mul_apply]
  have h1:=congrFun (congrFun (vC A M) r) c
  simpa [qm,Matrix.mul_apply] using h1.symm
lemma gE {B:ℕ} (M:Qd B) (u v:Fin B) (x:Q1 B) :
  qT (qJ M u v) x=qT M (j2 u v x):=by
 apply v7
 rw [vX,vX]
 funext r
 simp only [Matrix.mulVec,dotProduct,qm,yP]
 have hcomp:=Equiv.sum_comp (Equiv.swap u v) (fun t:Fin B=>b2z (M r t)*b2z (j2 u v x t))
 rw [← hcomp]
 refine Finset.sum_congr rfl fun t _=>?_
 by_cases htu:t=u
 ·subst htu;by_cases hvt:v=t <;> simp [qJ,j2,Equiv.swap_apply_left,hvt]
 ·by_cases htv:t=v
  ·subst htv;simp [qJ,j2,htu,Equiv.swap_apply_right]
  ·simp [qJ,j2,htu,htv,Equiv.swap_apply_of_ne_of_ne htu htv]
lemma gV {B:ℕ} (M:Qd B) {src dst:Fin B} (hne:src ≠ dst) (x:Q1 B) :
  qT (vD M src dst) x=qT M (zX dst src x):=by
 apply v7
 rw [vX,vX]
 funext r
 simp only [Matrix.mulVec,dotProduct,qm,yP]
 have hsplit:∀ f:Fin B->ZMod 2,
   ∑ t:Fin B,f t=f src+f dst+∑ t∈(Finset.univ.erase src).erase dst,f t:=by
  intro f
  have hmem1:dst∈Finset.univ.erase src:=Finset.mem_erase.mpr ⟨hne.symm,dL dst⟩
  rw [← Finset.add_sum_erase _ f (dL src),← Finset.add_sum_erase _ f hmem1,add_assoc]
 rw [hsplit,hsplit]
 have hrest:∑ t∈(Finset.univ.erase src).erase dst,b2z (vD M src dst r t)*b2z (x t) =
   ∑ t∈(Finset.univ.erase src).erase dst,b2z (M r t)*b2z (zX dst src x t):=by
  refine Finset.sum_congr rfl fun t ht=>?_
  have htd:t ≠ dst:=(Finset.mem_erase.mp ht).1
  have hts:t ≠ src:=(Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
  simp [vD,zX,htd,hts]
 rw [hrest]
 congr 1
 simp only [vD,zX,hne,hne.symm,↓reduceIte,gH]
 ring
lemma gh {B:ℕ} (M:Qd B) (u v:Fin B) :
  qJ (qJ M u v) u v=M:=by
 funext r c;unfold qJ
 by_cases h1:c=u <;> by_cases h2:c=v <;> by_cases h3:u=v <;> simp_all
lemma gD {B:ℕ} (M:Qd B) {src dst:Fin B} (hne:src ≠ dst) :
  vD (vD M src dst) src dst=M:=by
 funext r c;unfold vD
 by_cases h:c=dst
 ·subst h;simp [hne]
 ·simp [h]
lemma zC {B:ℕ} {M:Qd B} (hM:Q7 M) (u v:Fin B) :
  Q7 (qJ M u v):=by
 obtain ⟨N,hN⟩:=hM
 refine ⟨v3 (qJ (vT B) u v) N,?_⟩
 have h1:qJ M u v=v3 M (qJ (vT B) u v):=by
  rw [jX,vU]
 have h2:v3 (qJ (vT B) u v) (qJ (vT B) u v)=vT B:=by
  rw [jX,vU,gh]
 rw [h1,jU,← jU (qJ (vT B) u v),h2,yv,hN]
lemma zI {B:ℕ} {M:Qd B} (hM:Q7 M)
  {src dst:Fin B} (hne:src ≠ dst):Q7 (vD M src dst):=by
 obtain ⟨N,hN⟩:=hM
 refine ⟨v3 (vD (vT B) src dst) N,?_⟩
 have h1:vD M src dst=v3 M (vD (vT B) src dst):=by
  rw [ye,vU]
 have h2:v3 (vD (vT B) src dst) (vD (vT B) src dst)=vT B:=by
  rw [ye,vU,gD _ hne]
 rw [h1,jU,← jU (vD (vT B) src dst),h2,yv,hN]
lemma yM {B:ℕ} {M:Qd B} (hM:Q7 M)
  (row:Fin B) (hprev:∀ r:Fin B,r.val < row.val->∀ c:Fin B,M r c=decide (r=c)) :
  ∃ piv:Fin B,row.val ≤ piv.val/\M row piv=true:=by
 by_contra hno
 push Not at hno
 obtain ⟨N,hN⟩:=hM
 have hEq:=congrFun (congrFun (congrArg qm hN) row) row
 rw [vC,jj,Matrix.one_apply_eq] at hEq
 have hrow_comb:∀ c:Fin B,qm M row c =
   ∑ r:Fin B,(if r.val < row.val then qm M row r else 0)*qm M r c:=by
  intro c
  by_cases hcr:c.val < row.val
  ·rw [Finset.sum_eq_single c]
   ·simp only [hcr,↓reduceIte,qm,hprev c hcr c,decide_true,b2z,mul_one]
   ·intro r _ hrc
    by_cases hrr:r.val < row.val
    ·simp only [hrr,↓reduceIte,qm,hprev r hrr c,hrc,decide_false,b2z,Bool.false_eq_true,mul_zero]
    ·simp only [hrr,↓reduceIte,zero_mul]
   ·intro h;exact absurd (dL c) h
  ·have h0:M row c=false:=Bool.eq_false_iff.mpr (hno c (by omega))
   simp only [qm,h0,b2z,Bool.false_eq_true,↓reduceIte]
   symm
   apply Finset.sum_eq_zero
   intro r _
   by_cases hrr:r.val < row.val
   ·have hne:r ≠ c:=fun e=>by subst e;omega
    simp only [hrr,↓reduceIte,qm,hprev r hrr c,hne,decide_false,b2z,Bool.false_eq_true,mul_zero]
   ·simp only [hrr,↓reduceIte,zero_mul]
 have hcalc:(qm M*qm N) row row=0:=by
  simp only [Matrix.mul_apply]
  have hrew:(∑ c:Fin B,qm M row c*qm N c row) =
    ∑ c:Fin B,(∑ r:Fin B,(if r.val < row.val then qm M row r else 0)*qm M r c)*qm N c row:=
   Finset.sum_congr rfl fun c _=>by rw [hrow_comb c]
  rw [hrew]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  simp_rw [mul_assoc,← Finset.mul_sum]
  by_cases hrr:r.val < row.val
  ·have hMNr:(∑ c:Fin B,qm M r c*qm N c row)=0:=by
    have h2:=congrFun (congrFun (congrArg qm hN) r) row
    rw [vC,jj,Matrix.one_apply_ne (fun e=>by subst e;omega),Matrix.mul_apply] at h2
    exact h2
   rw [hMNr,mul_zero]
  ·simp only [hrr,↓reduceIte,zero_mul]
 rw [hcalc] at hEq
 exact zero_ne_one hEq
def qc {m:ℕ} (T:Q6 m) (B:ℕ):Fin B->Q1 m:=
 ((dF m).foldl (fun (st:ℕ × (Fin B->Q1 m)) c=>
  if T c c=true then
   (st.1+1,fun j=>if j.val=st.1 then T c else st.2 j)
  else st) (0,fun _=>q2 m)).2
def qf {m:ℕ} (T:Q6 m) (v:Q1 m) (B:ℕ):Q1 B:=
 ((dF m).foldl (fun (st:ℕ × Q1 m × Q1 B) c=>
  if T c c=true then
   let b:=st.2.1 c
   let cur':=if b=true then q5 st.2.1 (T c) else st.2.1
   let out':=fun j:Fin B=>if j.val=st.1 then b else st.2.2 j
   (st.1+1,cur',out')
  else st) (0,v,q2 B)).2.2
def q1 {m B:ℕ} (T:Q6 m) (x:Q1 B):Q1 m:=
 (dF B).foldl (fun acc t=>if x t=true then q5 acc (qc T B t) else acc)
  (q2 m)
lemma jv {m B:ℕ} (T:Q6 m) (hT:Q3 T) (hB:q3 T ≤ B) :
  (∀ j:Fin B,q3 T ≤ j.val->qc T B j=q2 m) /\
  (∀ j:Fin B,j.val < q3 T->∃ c:Fin m,T c c=true/\qc T B j=T c /\
   j.val=(Finset.univ.filter (fun c':Fin m=>c'.val < c.val/\T c' c'=true)).card) /\
  (∀ c:Fin m,T c c=true->∃ j:Fin B,j.val < q3 T/\qc T B j=T c /\
   j.val=(Finset.univ.filter (fun c':Fin m=>c'.val < c.val/\T c' c'=true)).card):=by
 let cntBefore (k:ℕ):ℕ:=(Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)).card
 have hgo:∀ k ≤ m,
   let st:=((dF m).take k).foldl (fun (st:ℕ × (Fin B->Q1 m)) c=>
    if T c c=true then (st.1+1,fun j=>if j.val=st.1 then T c else st.2 j) else st)
    (0,fun _=>q2 m)
   st.1=cntBefore k /\
   (∀ j:Fin B,cntBefore k ≤ j.val->st.2 j=q2 m) /\
   (∀ j:Fin B,j.val < cntBefore k->∃ c:Fin m,c.val < k/\T c c=true/\st.2 j=T c /\
    j.val=cntBefore c.val) /\
   (∀ c:Fin m,c.val < k->T c c=true ->
    ∃ j:Fin B,j.val=cntBefore c.val/\st.2 j=T c):=by
  intro k
  induction k with
  | zero=>
   intro _
   have hc0:cntBefore 0=0:=by simp [cntBefore]
   simp only [List.take_zero,List.foldl_nil,hc0]
   exact ⟨trivial,fun _ _=>trivial,fun _ h=>absurd h (by omega),fun _ h=>absurd h (by omega)⟩
  | succ k ih=>
   intro hk
   obtain ⟨hcnt,hge,hlt,hmap⟩:=ih (Nat.le_of_succ_le hk)
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF m).take k).foldl (fun (st:ℕ × (Fin B->Q1 m)) c=>
    if T c c=true then (st.1+1,fun j=>if j.val=st.1 then T c else st.2 j) else st)
    (0,fun _=>q2 m)
   set ck:Fin m:=⟨k,hk⟩
   by_cases hTk:T ck ck=true
   ·have hcnt1:cntBefore (k+1)=cntBefore k+1:=by
     have hnot:ck∉Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true):=by simp [ck]
     have hins:Finset.univ.filter (fun c:Fin m=>c.val < k+1/\T c c=true) =
       insert ck (Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)):=by
      ext c;simp only [dK,dL,true_and,Finset.mem_insert]
      constructor
      ·rintro ⟨hlt',hTc⟩
       by_cases hc:c.val < k
       ·right;exact ⟨hc,hTc⟩
       ·left;exact Fin.ext (by dsimp [ck];omega)
      ·rintro (rfl | ⟨hlt',hTc⟩)
       ·exact ⟨by dsimp [ck];omega,hTk⟩
       ·exact ⟨by omega,hTc⟩
     simp only [cntBefore,hins,Finset.card_insert_of_notMem hnot]
    have hcnt_le:cntBefore (k+1) ≤ q3 T:=by
     apply Finset.card_le_card;intro c hc
     simp only [dK,dL,true_and] at hc ⊢;exact hc.2
    simp only [hTk,↓reduceIte]
    refine ⟨by rw [hcnt,hcnt1],?_,?_,?_⟩
    ·intro j hj
     have hne:j.val ≠ st.1:=by omega
     simp only [hne,↓reduceIte];exact hge j (by omega)
    ·intro j hj
     by_cases heq:j.val=st.1
     ·simp only [heq,↓reduceIte];exact ⟨ck,by dsimp [ck];omega,hTk,rfl,hcnt⟩
     ·simp only [heq,↓reduceIte]
      obtain ⟨c,hck,hTc,hsc,hjv⟩:=hlt j (by omega)
      exact ⟨c,by omega,hTc,hsc,hjv⟩
    ·intro c hck hTc
     by_cases hlt':c.val < k
     ·obtain ⟨j,hjv,hjs⟩:=hmap c hlt' hTc
      have hne:j.val ≠ st.1:=by
       have hle':cntBefore c.val < cntBefore k:=by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun z hz=>by
         simp only [dK,dL,true_and] at hz ⊢
         exact ⟨by omega,hz.2⟩,fun he=>?_⟩
        have hc_in:c∈Finset.univ.filter (fun z:Fin m=>z.val < k/\T z z=true):=
         Finset.mem_filter.mpr ⟨dL c,hlt',hTc⟩
        rw [← he] at hc_in
        simp only [dK,dL,true_and] at hc_in
        omega
       omega
      exact ⟨j,hjv,by simp [hne,hjs]⟩
     ·have hceq:c=ck:=Fin.ext (by dsimp [ck];omega)
      subst hceq
      refine ⟨⟨cntBefore k,by omega⟩,rfl,?_⟩
      simp [hcnt]
   ·have hcnt1:cntBefore (k+1)=cntBefore k:=by
     unfold cntBefore
     congr 1;ext c;simp only [dK,dL,true_and]
     constructor
     ·rintro ⟨hlt',hTc⟩
      refine ⟨?_,hTc⟩
      by_contra hge'
      have hceq:c=ck:=Fin.ext (by dsimp [ck];omega)
      rw [hceq] at hTc;exact hTk hTc
     ·rintro ⟨hlt',hTc⟩;exact ⟨by omega,hTc⟩
    simp only [hTk,Bool.false_eq_true,↓reduceIte]
    refine ⟨by rw [hcnt,hcnt1],fun j hj=>hge j (by omega),
     fun j hj=>by
      obtain ⟨c,hck,hTc,hsc,hjv⟩:=hlt j (by omega)
      exact ⟨c,by omega,hTc,hsc,hjv⟩,
     fun c hck hTc=>by
      have hlt':c.val < k:=by
       by_contra hge'
       have hceq:c=ck:=Fin.ext (by dsimp [ck];omega)
       rw [hceq] at hTc;exact hTk hTc
      exact hmap c hlt' hTc⟩
 have hm:=hgo m le_rfl
 have hcntm:cntBefore m=q3 T:=by
  unfold cntBefore q3;congr 1;ext c;simp
 have htm:(dF m).take m=dF m:=by simp
 rw [htm,hcntm] at hm
 refine ⟨hm.2.1,fun j hj=>?_,fun c hTc=>?_⟩
 ·obtain ⟨c,_,hTc,hrow,hjv⟩:=hm.2.2.1 j hj
  exact ⟨c,hTc,hrow,hjv⟩
 ·obtain ⟨j,hjv,hrow⟩:=hm.2.2.2 c c.isLt hTc
  have hjlt:j.val < q3 T:=by
   rw [hjv]
   apply Finset.card_lt_card
   rw [Finset.ssubset_iff_subset_ne]
   refine ⟨fun z hz=>by
    simp only [dK,dL,true_and] at hz ⊢;exact hz.2,fun he=>?_⟩
   have hcm:c∈Finset.univ.filter (fun z:Fin m=>T z z=true):=
    Finset.mem_filter.mpr ⟨dL c,hTc⟩
   rw [← he] at hcm
   simp only [dK,dL,true_and] at hcm
   omega
  exact ⟨j,hjlt,hrow,hjv⟩
lemma qg {m B:ℕ} (T:Q6 m) (hT:Q3 T) (hB:q3 T ≤ B) :
  (∀ v j,q3 T ≤ j.val->qf T v B j=false) /\
  (∀ v,q4 v∈q6 T->q1 T (qf T v B)=v) /\
  (∀ x:Q1 B,(∀ j:Fin B,q3 T ≤ j.val->x j=false) ->
   qf T (q1 T x) B=x) /\
  (∀ x:Q1 B,q4 (q1 T x)∈q6 T) /\
  (∀ x y:Q1 B,q1 T (q5 x y)=q5 (q1 T x) (q1 T y)):=by
 obtain ⟨hpr_ge,hpr_lt,hpr_map⟩:=jv T hT hB
 have hrec_sum:∀ x:Q1 B,q4 (q1 T x) =
   ∑ t:Fin B,(if x t=true then (1:ZMod 2) else 0) • q4 (qc T B t):=by
  intro x
  have hgo:∀ k ≤ B,
    q4 (((dF B).take k).foldl
     (fun acc t=>if x t=true then q5 acc (qc T B t) else acc) (q2 m)) =
    ∑ t:Fin B,if t.val < k then (if x t=true then (1:ZMod 2) else 0) • q4 (qc T B t) else 0:=by
   intro k
   induction k with
   | zero=>simp [qh]
   | succ k ih=>
    intro hk
    have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
     rw [dJ (by simp;omega)];simp
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    set prev:=((dF B).take k).foldl
     (fun acc t=>if x t=true then q5 acc (qc T B t) else acc) (q2 m)
    have hterm:q4 (if x ⟨k,hk⟩=true then q5 prev (qc T B ⟨k,hk⟩) else prev) =
      q4 prev+(if x ⟨k,hk⟩=true then (1:ZMod 2) else 0) • q4 (qc T B ⟨k,hk⟩):=by
     cases x ⟨k,hk⟩ <;> simp [qE]
    rw [hterm,ih (Nat.le_of_succ_le hk)]
    conv_rhs=>rw [← Finset.add_sum_erase _ _ (dL (⟨k,hk⟩:Fin B))]
    have hrest:∀ t∈Finset.univ.erase (⟨k,hk⟩:Fin B),
      (if t.val < k+1 then (if x t=true then (1:ZMod 2) else 0) • q4 (qc T B t) else 0) =
      (if t.val < k then (if x t=true then (1:ZMod 2) else 0) • q4 (qc T B t) else 0):=by
     intro t ht
     have hne:t.val ≠ k:=fun e=>(Finset.mem_erase.mp ht).1 (Fin.ext e)
     have hiff:t.val < k+1 ↔ t.val < k:=by omega
     simp [hiff]
    rw [Finset.sum_congr rfl hrest]
    have hself:(if (⟨k,hk⟩:Fin B).val < k then
      (if x ⟨k,hk⟩=true then (1:ZMod 2) else 0) • q4 (qc T B ⟨k,hk⟩) else 0)=0:=by simp
    conv_lhs=>
     rw [← Finset.add_sum_erase _ (fun t:Fin B=>if t.val < k then
      (if x t=true then (1:ZMod 2) else 0) • q4 (qc T B t) else 0) (dL ⟨k,hk⟩),
      hself,zero_add]
    simp only [Nat.lt_succ_self,↓reduceIte,add_comm]
  have hm:=hgo B le_rfl
  have htm:(dF B).take B=dF B:=by simp
  rw [htm] at hm
  simpa [q1] using hm
 have hrec_mem:∀ x:Q1 B,q4 (q1 T x)∈q6 T:=by
  intro x
  rw [hrec_sum]
  refine Submodule.sum_mem _ fun t _=>?_
  apply Submodule.smul_mem
  by_cases ht:t.val < q3 T
  ·obtain ⟨c,_,hrow,_⟩:=hpr_lt t ht
   rw [hrow];exact Submodule.subset_span ⟨c,rfl⟩
  ·rw [hpr_ge t (by omega),qh];exact Submodule.zero_mem _
 have hrec_xor:∀ x y:Q1 B,
   q1 T (q5 x y)=q5 (q1 T x) (q1 T y):=by
  intro x y
  apply v7
  rw [qE,hrec_sum,hrec_sum,hrec_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _=>?_
  rw [← add_smul]
  congr 1
  change b2z (xor (x t) (y t))=b2z (x t)+b2z (y t)
  exact gH (x t) (y t)
 have hcoords_go:∀ (v:Q1 m) (k:ℕ) (hk:k ≤ m),
   let st:=((dF m).take k).foldl (fun (st:ℕ × Q1 m × Q1 B) c=>
    if T c c=true then
     let b:=st.2.1 c
     let cur':=if b=true then q5 st.2.1 (T c) else st.2.1
     let out':=fun j:Fin B=>if j.val=st.1 then b else st.2.2 j
     (st.1+1,cur',out')
    else st) (0,v,q2 B)
   st.1=(Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)).card /\
   st.2.1=((dF m).take k).foldl (fun acc c=>jd T c acc) v /\
   (∀ j:Fin B,(Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)).card ≤ j.val->st.2.2 j=false) /\
   q4 v=q4 st.2.1+q4 (q1 T st.2.2):=by
  intro v k
  induction k with
  | zero=>
   intro _
   have hc0:(Finset.univ.filter (fun c:Fin m=>c.val < 0/\T c c=true)).card=0:=by simp
   simp only [List.take_zero,List.foldl_nil,hc0]
   refine ⟨trivial,trivial,fun _ _=>rfl,?_⟩
   rw [hrec_sum]
   simp [q2]
  | succ k ih=>
   intro hk
   obtain ⟨hcnt,hred,hge,hsum⟩:=ih (Nat.le_of_succ_le hk)
   have htake:(dF m).take (k+1)=(dF m).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,
     List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF m).take k).foldl (fun (st:ℕ × Q1 m × Q1 B) c=>
    if T c c=true then
     let b:=st.2.1 c
     let cur':=if b=true then q5 st.2.1 (T c) else st.2.1
     let out':=fun j:Fin B=>if j.val=st.1 then b else st.2.2 j
     (st.1+1,cur',out')
    else st) (0,v,q2 B)
   set ck:Fin m:=⟨k,hk⟩
   by_cases hTk:T ck ck=true
   ·have hcnt1:(Finset.univ.filter (fun c:Fin m=>c.val < k+1/\T c c=true)).card =
      (Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)).card+1:=by
     have hnot:ck∉Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true):=by simp [ck]
     have hins:Finset.univ.filter (fun c:Fin m=>c.val < k+1/\T c c=true) =
       insert ck (Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)):=by
      ext c;simp only [dK,dL,true_and,Finset.mem_insert]
      constructor
      ·rintro ⟨hlt',hTc⟩
       by_cases hc:c.val < k
       ·right;exact ⟨hc,hTc⟩
       ·left;exact Fin.ext (by dsimp [ck];omega)
      ·rintro (rfl | ⟨hlt',hTc⟩)
       ·exact ⟨by dsimp [ck];omega,hTk⟩
       ·exact ⟨by omega,hTc⟩
     rw [hins,Finset.card_insert_of_notMem hnot]
    obtain ⟨j0,hj0lt,hj0row,hj0val⟩:=hpr_map ck hTk
    have hj0st:j0.val=st.1:=by rw [hj0val,hcnt]
    simp only [hTk,↓reduceIte]
    refine ⟨by rw [hcnt,hcnt1],?_,?_,?_⟩
    ·rw [← hred];unfold jd;simp [hTk]
    ·intro j hj
     have hne:j.val ≠ st.1:=by omega
     simp only [hne,↓reduceIte];exact hge j (by omega)
    ·rw [hsum]
     set out':Q1 B:=fun j=>if j.val=st.1 then st.2.1 ck else st.2.2 j
     have hout_diff:q4 (q1 T out') =
       q4 (q1 T st.2.2)+(if st.2.1 ck=true then (1:ZMod 2) else 0) • q4 (T ck):=by
      rw [hrec_sum,hrec_sum,← Finset.add_sum_erase _ _ (dL j0),
        ← Finset.add_sum_erase _ _ (dL j0)]
      have hrest:∀ t∈Finset.univ.erase j0,
        (if out' t=true then (1:ZMod 2) else 0) • q4 (qc T B t) =
        (if st.2.2 t=true then (1:ZMod 2) else 0) • q4 (qc T B t):=by
       intro t ht
       have hne:t.val ≠ st.1:=fun e=>(Finset.mem_erase.mp ht).1 (Fin.ext (e.trans hj0st.symm))
       simp [out',hne]
      rw [Finset.sum_congr rfl hrest]
      have hst2j0:st.2.2 j0=false:=hge j0 (by omega)
      simp only [out',hj0st,↓reduceIte,hj0row,hst2j0,Bool.false_eq_true,zero_smul,zero_add]
      rw [add_comm]
     rw [hout_diff]
     cases hcur:st.2.1 ck
     ·simp
     ·simp only [↓reduceIte,one_smul,qE]
      have h1:q4 st.2.1+q4 (T ck)+(q4 (q1 T st.2.2)+q4 (T ck)) =
        q4 st.2.1+q4 (q1 T st.2.2)+(q4 (T ck)+q4 (T ck)):=by abel
      rw [h1,qM,add_zero]
   ·have hcnt1:(Finset.univ.filter (fun c:Fin m=>c.val < k+1/\T c c=true)).card =
      (Finset.univ.filter (fun c:Fin m=>c.val < k/\T c c=true)).card:=by
     congr 1;ext c;simp only [dK,dL,true_and]
     constructor
     ·rintro ⟨hlt',hTc⟩
      refine ⟨?_,hTc⟩
      by_contra hge'
      have hceq:c=ck:=Fin.ext (by dsimp [ck];omega)
      rw [hceq] at hTc;exact hTk hTc
     ·rintro ⟨hlt',hTc⟩;exact ⟨by omega,hTc⟩
    simp only [hTk,Bool.false_eq_true,↓reduceIte]
    refine ⟨by rw [hcnt,hcnt1],?_,fun j hj=>hge j (by omega),hsum⟩
    rw [← hred];unfold jd;simp [hTk]
 have hge_all:∀ v j,q3 T ≤ j.val->qf T v B j=false:=by
  intro v j hj
  have hm:=hcoords_go v m le_rfl
  have htm:(dF m).take m=dF m:=by simp
  have hcm:(Finset.univ.filter (fun c:Fin m=>c.val < m/\T c c=true)).card=q3 T:=by
   unfold q3;congr 1;ext c;simp
  rw [htm,hcm] at hm
  exact hm.2.2.1 j hj
 have hrec_coords:∀ v,q4 v∈q6 T->q1 T (qf T v B)=v:=by
  intro v hv
  have hm:=hcoords_go v m le_rfl
  have htm:(dF m).take m=dF m:=by simp
  rw [htm] at hm
  have hred0:q8 T v=q2 m:=(qG hT v).mpr hv
  apply v7
  have hsum:=hm.2.2.2
  have hcur0:q4 (((dF m).foldl (fun (st:ℕ × Q1 m × Q1 B) c=>
    if T c c=true then
     let b:=st.2.1 c
     let cur':=if b=true then q5 st.2.1 (T c) else st.2.1
     let out':=fun j:Fin B=>if j.val=st.1 then b else st.2.2 j
     (st.1+1,cur',out')
    else st) (0,v,q2 B)).2.1)=0:=by
   rw [hm.2.1];change q4 (q8 T v)=0;rw [hred0,qh]
  rw [hcur0,zero_add] at hsum
  exact hsum.symm
 have hcoords_rec:∀ x:Q1 B,(∀ j:Fin B,q3 T ≤ j.val->x j=false) ->
   qf T (q1 T x) B=x:=by
  intro x hx
  set y:=qf T (q1 T x) B
  have hrec_eq:q1 T y=q1 T x:=hrec_coords _ (hrec_mem x)
  have hdiff0:q4 (q1 T (q5 y x))=0:=by
   rw [hrec_xor,hrec_eq,qE,qM]
  by_contra hne
  have hex:∃ j:Fin B,y j ≠ x j:=by
   by_contra hall;push Not at hall;exact hne (funext hall)
  have hsum0:∑ t:Fin B,(if q5 y x t=true then (1:ZMod 2) else 0) • q4 (qc T B t)=0:=by
   rw [← hrec_sum,hdiff0]
  have hlin:=yi hT
  let coeff:{c:Fin m // T c c=true}->ZMod 2:=fun c=>
   let j:=Classical.choose (hpr_map c.1 c.2)
   if q5 y x j=true then 1 else 0
  have hsum_piv:∑ c:{c:Fin m // T c c=true},coeff c • q4 (T c.1)=0:=by
   rw [← hsum0]
   have hsub_sum:∑ t∈Finset.univ.filter (fun t:Fin B=>t.val < q3 T),
      (if q5 y x t=true then (1:ZMod 2) else 0) • q4 (qc T B t) =
     ∑ t:Fin B,(if q5 y x t=true then (1:ZMod 2) else 0) • q4 (qc T B t):=by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ hnot
    have hge:q3 T ≤ t.val:=by
     simp only [dK,dL,true_and,not_lt] at hnot;exact hnot
    rw [hpr_ge t hge,qh,smul_zero]
   rw [← hsub_sum]
   refine Finset.sum_bij (fun (c:{c:Fin m // T c c=true}) _=>Classical.choose (hpr_map c.1 c.2)) ?_ ?_ ?_ ?_
   ·intro c _
    exact Finset.mem_filter.mpr ⟨dL _,(Classical.choose_spec (hpr_map c.1 c.2)).1⟩
   ·intro c1 _ c2 _ heq
    have h1:=(Classical.choose_spec (hpr_map c1.1 c1.2)).2.1
    have h2:=(Classical.choose_spec (hpr_map c2.1 c2.2)).2.1
    rw [heq] at h1
    have hTeq:T c1.1=T c2.1:=h1.symm.trans h2
    by_contra hne'
    have hlt_or:c1.1.val < c2.1.val\/c2.1.val < c1.1.val:=by
     have:c1.1.val ≠ c2.1.val:=fun e=>hne' (Subtype.ext (Fin.ext e))
     omega
    rcases hlt_or with hlt' | hlt'
    ·rcases hT c2.1 with h0 | ⟨_,hcl⟩
     ·have:=congrFun h0 c2.1;rw [c2.2] at this;exact Bool.false_ne_true this.symm
     ·have:=congrFun hTeq c1.1;rw [c1.2,hcl c1.1 hlt'] at this;exact Bool.false_ne_true this.symm
    ·rcases hT c1.1 with h0 | ⟨_,hcl⟩
     ·have:=congrFun h0 c1.1;rw [c1.2] at this;exact Bool.false_ne_true this.symm
     ·have:=congrFun hTeq c2.1;rw [c2.2,hcl c2.1 hlt'] at this;exact Bool.false_ne_true this
   ·intro j hj
    have hjlt:j.val < q3 T:=(Finset.mem_filter.mp hj).2
    obtain ⟨c,hTc,_,hjv⟩:=hpr_lt j hjlt
    refine ⟨⟨c,hTc⟩,dL _,?_⟩
    exact Fin.ext ((Classical.choose_spec (hpr_map c hTc)).2.2.trans hjv.symm)
   ·intro c _
    simp only [coeff,(Classical.choose_spec (hpr_map c.1 c.2)).2.1]
  have hcoeff0:∀ c:{c:Fin m // T c c=true},coeff c=0:=
   Fintype.linearIndependent_iff.mp hlin coeff hsum_piv
  obtain ⟨j,hjne⟩:=hex
  have hjlt:j.val < q3 T:=by
   by_contra hge
   push Not at hge
   dsimp only [y] at hjne
   rw [hge_all _ j hge,hx j hge] at hjne
   exact hjne rfl
  obtain ⟨c,hTc,_,hjv⟩:=hpr_lt j hjlt
  have hjeq:Classical.choose (hpr_map c hTc)=j:=
   Fin.ext ((Classical.choose_spec (hpr_map c hTc)).2.2.trans hjv.symm)
  have hc0:=hcoeff0 ⟨c,hTc⟩
  simp only [coeff,hjeq] at hc0
  have hxf:q5 y x j=false:=by
   cases h:q5 y x j
   ·rfl
   ·simp [h] at hc0
  have hyx:y j=x j:=by
   unfold q5 at hxf
   cases hyj:y j <;> cases hxj:x j <;> simp_all
  exact hjne hyx
 exact ⟨hge_all,hrec_coords,hcoords_rec,hrec_mem,hrec_xor⟩
lemma jJ {m B:ℕ} (T:Q6 m) (hT:Q3 T) (hB:q3 T ≤ B) :
  qf T (q2 m) B=q2 B:=by
 have h1:=(qg T hT hB).2.2.1 (q2 B) (fun _ _=>rfl)
 have hrec0:q1 T (q2 B)=q2 m:=by
  apply v7
  have hgo:∀ k ≤ B,
    ((dF B).take k).foldl
     (fun acc t=>if q2 B t=true then q5 acc (qc T B t) else acc)
     (q2 m)=q2 m:=by
   intro k
   induction k with
   | zero=>intro _;simp
   | succ k ih=>
    intro hk
    have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
     rw [dJ (by simp;omega)];simp
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,ih (Nat.le_of_succ_le hk)]
    rfl
  have hm:=hgo B le_rfl
  have htm:(dF B).take B=dF B:=by simp
  rw [htm] at hm
  rw [show q1 T (q2 B)=q2 m from hm]
 rw [hrec0] at h1
 exact h1
lemma yY {m B:ℕ} (T:Q6 m) (hT:Q3 T) (hB:q3 T ≤ B)
  {u v:Q1 m} (hu:q4 u∈q6 T) (hv:q4 v∈q6 T) :
  qf T (q5 u v) B=q5 (qf T u B) (qf T v B):=by
 obtain ⟨hge,hrc,hcr,_,hrx⟩:=qg T hT hB
 have h1:q1 T (q5 (qf T u B) (qf T v B))=q5 u v:=by
  rw [hrx,hrc u hu,hrc v hv]
 have h2:=hcr (q5 (qf T u B) (qf T v B)) (fun j hj=>by
  simp [q5,hge u j hj,hge v j hj])
 rw [h1] at h2
 exact h2
def qk {m:ℕ} (T_U T_M:Q6 m) (B:ℕ):Qd B:=
 let rowsU:=qc T_U B
 let st1:=(dF B).foldl (fun (st:ℕ × Q6 B × (Fin B->Q1 B)) j=>
  let col:=qf T_M (rowsU j) B
  if qK col=true then
   (st.1+1,qC st.2.1 col,fun c=>if c.val=st.1 then col else st.2.2 c)
  else st) (0,qN B,fun _=>q2 B)
 let st2:=(dF B).foldl (fun (st:ℕ × Q6 B × (Fin B->Q1 B)) r=>
  let er:Q1 B:=fun i=>decide (i=r)
  if qK (q8 st.2.1 er)=true then
   (st.1+1,qC st.2.1 er,fun c=>if c.val=st.1 then er else st.2.2 c)
  else st) st1
 fun r c=>st2.2.2 c r
lemma ji {B:ℕ} (v:Q1 B) :
  qK v=true ↔ q4 v ≠ 0:=by
 rw [qv,dG]
 constructor
 ·rintro ⟨i,hi⟩ h0
  have h1:=congrFun h0 i
  simp [q4,hi] at h1
 ·intro hne
  by_contra hall
  push Not at hall
  apply hne
  funext i
  simp [q4,Bool.eq_false_iff.mpr (hall i)]
lemma jQ {B:ℕ} {T:Q6 B} (hT:Q3 T)
  {v:Q1 B} (hnot:q4 v∉q6 T) :
  q3 (qC T v)=q3 T+1:=by
 obtain ⟨hE',hsp'⟩:=jG T hT v
 rw [← qo hE',← qo hT,hsp']
 have hinf:(q6 T ⊓ Submodule.span (ZMod 2) {q4 v}:Submodule (ZMod 2) (Fin B->ZMod 2))=⊥:=by
  rw [eq_bot_iff]
  intro x ⟨hxT,hxv⟩
  rw [SetLike.mem_coe] at hxT hxv
  rw [Submodule.mem_span_singleton] at hxv
  obtain ⟨a,rfl⟩:=hxv
  rcases qD a with rfl | rfl
  ·simp
  ·simp only [one_smul] at hxT;exact absurd hxT hnot
 have h1:Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {q4 v}:Submodule (ZMod 2) (Fin B->ZMod 2))=1:=
  finrank_span_singleton (fun h0=>hnot (h0.symm▸Submodule.zero_mem _))
 have hgrass:=Submodule.finrank_sup_add_finrank_inf_eq (q6 T) (Submodule.span (ZMod 2) {q4 v})
 rw [hinf,finrank_bot,add_zero,h1] at hgrass
 exact hgrass
lemma zV {m B:ℕ} {T_U T_M:Q6 m}
  (hU:Q3 T_U) (hM:Q3 T_M)
  (hsub:q6 T_U ≤ q6 T_M) (hBM:q3 T_M ≤ B) :
  let G:=qk T_U T_M B
  Q7 G /\
  (∀ j:Fin B,j.val < q3 T_U->(fun r=>G r j)=qf T_M (qc T_U B j) B) /\
  (∀ i j:Fin B,(q3 T_M ≤ i.val\/q3 T_M ≤ j.val)->G i j=decide (i=j)):=by
 have hBU:q3 T_U ≤ q3 T_M:=by
  rw [← qo hU,← qo hM]
  exact Submodule.finrank_mono hsub
 have hBU_le:q3 T_U ≤ B:=hBU.trans hBM
 obtain ⟨hprU_ge,hprU_lt,_⟩:=jv T_U hU hBU_le
 obtain ⟨hM_ge,hM_rc,hM_cr,hM_mem,hM_xor⟩:=qg T_M hM hBM
 obtain ⟨hU_ge,hU_rc,hU_cr,hU_mem,hU_xor⟩:=qg T_U hU hBU_le
 have h0r:q1 T_M (q2 B)=q2 m:=by
  have h1:=hM_rc (q2 m) (by rw [qh];exact Submodule.zero_mem _)
  rwa [jJ T_M hM hBM] at h1
 let rowsU:=qc T_U B
 let step1 (st:ℕ × Q6 B × (Fin B->Q1 B)) (j:Fin B):=
  let col:=qf T_M (rowsU j) B
  if qK col=true then
   (st.1+1,qC st.2.1 col,fun c=>if c.val=st.1 then col else st.2.2 c)
  else st
 have hph1:∀ k ≤ B,
   let st:=((dF B).take k).foldl step1 (0,qN B,fun _=>q2 B)
   st.1=min k (q3 T_U) /\
   Q3 st.2.1 /\
   q3 st.2.1=st.1 /\
   q6 st.2.1=Submodule.span (ZMod 2) {v:Fin B->ZMod 2 | ∃ c:Fin B,c.val < st.1/\v=q4 (st.2.2 c)} /\
   (∀ c:Fin B,c.val < st.1->st.2.2 c=qf T_M (rowsU c) B) /\
   (∀ v:Fin B->ZMod 2,v∈q6 st.2.1->∀ r:Fin B,q3 T_M ≤ r.val->v r=0):=by
  intro k
  induction k with
  | zero=>
   intro _
   simp only [List.take_zero,List.foldl_nil,Nat.zero_min]
   refine ⟨trivial,jE B,by simp [q3,qN,q2],?_,
    fun _ h=>absurd h (by omega),fun v hv r _=>?_⟩
   ·rw [y6];symm;rw [Submodule.span_eq_bot];rintro _ ⟨_,h,_⟩;omega
   ·rw [y6,Submodule.mem_bot] at hv;simp [hv]
  | succ k ih=>
   intro hk
   obtain ⟨hcnt,hE,hrk,hsp,hcols,hsupp⟩:=ih (Nat.le_of_succ_le hk)
   have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF B).take k).foldl step1 (0,qN B,fun _=>q2 B)
   set jk:Fin B:=⟨k,hk⟩
   set col:=qf T_M (rowsU jk) B
   by_cases hltU:k < q3 T_U
   ·have hst1:st.1=k:=by rw [hcnt];omega
    obtain ⟨c0,hTc0,hrow0,hcv0⟩:=hprU_lt jk hltU
    have hrow_inM:q4 (rowsU jk)∈q6 T_M:=
     hsub (by dsimp only [rowsU];rw [hrow0];exact Submodule.subset_span ⟨c0,rfl⟩)
    have hcol_rec:q1 T_M col=rowsU jk:=hM_rc _ hrow_inM
    have hcol_nz:qK col=true:=by
     rw [ji]
     intro h0
     have hcol0:col=q2 B:=v7 (h0.trans (qh B).symm)
     have hrz:rowsU jk=q2 m:=by rw [← hcol_rec,hcol0,h0r]
     have hbad:=congrFun (hrow0.symm.trans hrz) c0
     rw [hTc0] at hbad;exact Bool.false_ne_true hbad.symm
    have hnot_in:q4 col∉q6 st.2.1:=by
     intro hin
     rw [hsp,Submodule.mem_span_set] at hin
     obtain ⟨g,hgsupp,hgsum⟩:=hin
     have hmem_span:q4 (rowsU jk)∈Submodule.span (ZMod 2)
       {w:Fin m->ZMod 2 | ∃ c:Fin B,c.val < k/\w=q4 (rowsU c)}:=by
      have hlin_rec:∀ v:Fin B->ZMod 2,
        v∈Submodule.span (ZMod 2) {v | ∃ c:Fin B,c.val < k/\v=q4 (st.2.2 c)} ->
        q4 (q1 T_M (fun i=>decide (v i=1))) ∈
         Submodule.span (ZMod 2) {w:Fin m->ZMod 2 | ∃ c:Fin B,c.val < k/\w=q4 (rowsU c)}:=by
       intro v hv
       refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
       ·rintro _ ⟨c,hck,rfl⟩
        have hdec:(fun i:Fin B=>decide (q4 (st.2.2 c) i=1))=st.2.2 c:=by
         funext i;simp only [q4];by_cases h:st.2.2 c i=true <;> simp [h]
        rw [hdec,hcols c (by omega)]
        obtain ⟨c1,_,hrow1,_⟩:=hprU_lt c (by omega)
        rw [hM_rc _ (hsub (by dsimp only [rowsU];rw [hrow1];exact Submodule.subset_span ⟨c1,rfl⟩))]
        exact Submodule.subset_span ⟨c,hck,rfl⟩
       ·have hdec:(fun i:Fin B=>decide ((0:Fin B->ZMod 2) i=1))=q2 B:=by
         funext i;simp [q2]
        rw [hdec,h0r,qh];exact Submodule.zero_mem _
       ·intro x y _ _ hx hy
        have hdec:(fun i:Fin B=>decide ((x+y) i=1)) =
          q5 (fun i=>decide (x i=1)) (fun i=>decide (y i=1)):=by
         funext i;simp only [Pi.add_apply,q5]
         rcases qD (x i) with h1 | h1 <;>
          rcases qD (y i) with h2 | h2 <;> simp [h1,h2] <;> decide
        rw [hdec,hM_xor,qE];exact Submodule.add_mem _ hx hy
       ·intro a x _ hx
        rcases qD a with rfl | rfl
        ·simp only [zero_smul]
         have hdec:(fun i:Fin B=>decide ((0:Fin B->ZMod 2) i=1))=q2 B:=by
          funext i;simp [q2]
         rw [hdec,h0r,qh];exact Submodule.zero_mem _
        ·simpa only [one_smul] using hx
      have h1:=hlin_rec (q4 col) (by
       have:q4 col∈q6 st.2.1:=by rw [hsp,Submodule.mem_span_set];exact ⟨g,hgsupp,hgsum⟩
       rw [hsp,hst1] at this;exact this)
      have hdec:(fun i:Fin B=>decide (q4 col i=1))=col:=by
       funext i;simp only [q4];by_cases h:col i=true <;> simp [h]
      rwa [hdec,hcol_rec] at h1
     have hsub_ne:Submodule.span (ZMod 2) {w:Fin m->ZMod 2 | ∃ c:Fin B,c.val < k/\w=q4 (rowsU c)} ≤
       Submodule.span (ZMod 2) {w:Fin m->ZMod 2 | ∃ c':Fin m,T_U c' c'=true/\c' ≠ c0/\w=q4 (T_U c')}:=by
      rw [Submodule.span_le]
      rintro _ ⟨c,hck,rfl⟩
      obtain ⟨c',hTc',hrow',hcv'⟩:=hprU_lt c (by omega)
      have hne:c' ≠ c0:=by
       intro heq;subst heq
       have hjk:jk.val=k:=rfl
       omega
      dsimp only [rowsU];rw [hrow'];exact Submodule.subset_span ⟨c',hTc',hne,rfl⟩
     have hin_ne:=hsub_ne hmem_span
     dsimp only [rowsU] at hin_ne
     rw [hrow0] at hin_ne
     have hlin:=yi hU
     have hnot_mem:q4 (T_U c0)∉Submodule.span (ZMod 2)
       ((fun x:{c:Fin m // T_U c c=true}=>q4 (T_U x.1)) '' {x | x ≠ ⟨c0,hTc0⟩}):=by
      have:=hlin.notMem_span_image (x:=⟨c0,hTc0⟩) (s:={x | x ≠ ⟨c0,hTc0⟩}) (by simp)
      exact this
     apply hnot_mem
     refine Submodule.span_mono ?_ hin_ne
     rintro _ ⟨c',hTc',hne,rfl⟩
     exact ⟨⟨c',hTc'⟩,fun e=>hne (congrArg Subtype.val e),rfl⟩
    obtain ⟨hE',hsp'⟩:=jG st.2.1 hE col
    have hrk':=jQ hE hnot_in
    dsimp only [step1]
    rw [show qf T_M (rowsU jk) B=col from rfl,if_pos hcol_nz]
    dsimp only
    refine ⟨by omega,hE',by omega,?_,?_,?_⟩
    ·rw [hsp',hsp]
     apply le_antisymm
     ·refine sup_le ?_ ?_
      ·rw [Submodule.span_le];rintro _ ⟨c,hc,rfl⟩
       have hne:c.val ≠ st.1:=by omega
       exact Submodule.subset_span ⟨c,by omega,by simp [hne]⟩
      ·rw [Submodule.span_singleton_le_iff_mem]
       exact Submodule.subset_span ⟨jk,by dsimp [jk];omega,by simp [jk,hst1]⟩
     ·rw [Submodule.span_le];rintro _ ⟨c,hc,rfl⟩
      by_cases hlt':c.val < st.1
      ·have hne:c.val ≠ st.1:=by omega
       simp only [hne,↓reduceIte]
       exact Submodule.mem_sup_left (Submodule.subset_span ⟨c,hlt',rfl⟩)
      ·have heq:c.val=st.1:=by omega
       simp only [heq,↓reduceIte]
       exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    ·intro c hc
     by_cases hlt':c.val < st.1
     ·have hne:c.val ≠ st.1:=by omega
      simp only [hne,↓reduceIte];exact hcols c hlt'
     ·have heq:c.val=st.1:=by omega
      have hceq:c=jk:=Fin.ext (by dsimp [jk];omega)
      rw [if_pos heq,hceq]
    ·intro v hv r hr
     rw [hsp',Submodule.mem_sup] at hv
     obtain ⟨w1,hw1,w2,hw2,rfl⟩:=hv
     rw [Submodule.mem_span_singleton] at hw2
     obtain ⟨a,rfl⟩:=hw2
     simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hsupp w1 hw1 r hr,zero_add]
     have hcolr:q4 col r=0:=by simp [q4,col,hM_ge _ r hr]
     rw [hcolr,mul_zero]
   ·have hrow0:rowsU jk=q2 m:=hprU_ge jk (by dsimp [jk];omega)
    have hcol0:col=q2 B:=by
     rw [show col=qf T_M (q2 m) B by simp [col,hrow0]]
     exact jJ T_M hM hBM
    have hnzf:qK col ≠ true:=by rw [hcol0];simp [qK,q2]
    dsimp only [step1]
    rw [show qf T_M (rowsU jk) B=col from rfl,if_neg hnzf]
    exact ⟨by omega,hE,hrk,hsp,hcols,hsupp⟩
 have hst1:=hph1 B le_rfl
 have hBtake:(dF B).take B=dF B:=by simp
 rw [hBtake,Nat.min_eq_right hBU_le] at hst1
 set st1:=(dF B).foldl step1 (0,qN B,fun _=>q2 B)
 obtain ⟨hst1_cnt,hst1_E,hst1_rk,hst1_sp,hst1_cols,hst1_supp⟩:=hst1
 let step2 (st:ℕ × Q6 B × (Fin B->Q1 B)) (r:Fin B):=
  let er:Q1 B:=fun i=>decide (i=r)
  if qK (q8 st.2.1 er)=true then
   (st.1+1,qC st.2.1 er,fun c=>if c.val=st.1 then er else st.2.2 c)
  else st
 have hph2:∀ k ≤ B,
   let st:=((dF B).take k).foldl step2 st1
   Q3 st.2.1 /\
   st.1=q3 st.2.1 /\
   st.1 ≤ B /\
   q6 st.2.1=Submodule.span (ZMod 2) {v:Fin B->ZMod 2 | ∃ c:Fin B,c.val < st.1/\v=q4 (st.2.2 c)} /\
   (∀ c:Fin B,c.val < q3 T_U->st.2.2 c=qf T_M (rowsU c) B) /\
   (∀ r:Fin B,r.val < k->q4 (fun i:Fin B=>decide (i=r))∈q6 st.2.1) /\
   (∀ v:Fin B->ZMod 2,v∈q6 st.2.1->∀ r:Fin B,max k (q3 T_M) ≤ r.val->v r=0) /\
   (q3 T_M ≤ k->st.1=k/\∀ c:Fin B,q3 T_M ≤ c.val->c.val < k->st.2.2 c=fun i=>decide (i=c)):=by
  intro k
  induction k with
  | zero=>
   intro _
   simp only [List.take_zero,List.foldl_nil,Nat.zero_max]
   refine ⟨hst1_E,hst1_rk.symm,by omega,hst1_sp,fun c hc=>hst1_cols c (by omega),
    fun _ h=>absurd h (by omega),hst1_supp,fun h0=>?_⟩
   have hTM0:q3 T_M=0:=by omega
   exact ⟨by omega,fun _ _ h=>absurd h (by omega)⟩
  | succ k ih=>
   intro hk
   obtain ⟨hE,hrk,hleB,hsp,hcolsU,hhas,hsupp,hhi⟩:=ih (Nat.le_of_succ_le hk)
   have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF B).take k).foldl step2 st1
   set rk:Fin B:=⟨k,hk⟩
   set erk:Q1 B:=fun i=>decide (i=rk)
   have hst1_geU:q3 T_U ≤ st.1:=by
    have hst_le:∀ s r,s.1 ≤ (step2 s r).1:=fun s r=>by dsimp only [step2];split_ifs <;> omega
    have hinc:∀ t ≤ B,st1.1 ≤ (((dF B).take t).foldl step2 st1).1:=by
     intro t;induction t with
     | zero=>intro _;simp
     | succ t iht=>
      intro ht
      have ht':(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
       rw [dJ (by simp;omega)];simp
      rw [ht',List.foldl_append,List.foldl_cons,List.foldl_nil]
      exact (iht (Nat.le_of_succ_le ht)).trans (hst_le _ _)
    have hge':st1.1 ≤ st.1:=hinc k (Nat.le_of_succ_le hk)
    omega
   have hspan_top_le:∀ n:ℕ,n ≤ B ->
     (∀ r:Fin B,r.val < n->q4 (fun i:Fin B=>decide (i=r))∈q6 st.2.1) ->
     (∀ v:Fin B->ZMod 2,v∈q6 st.2.1->∀ r:Fin B,n ≤ r.val->v r=0) ->
     q3 st.2.1=n:=by
    intro n hn hhas' hsupp'
    let Ssub:Submodule (ZMod 2) (Fin B->ZMod 2):=
     Submodule.span (ZMod 2) (Set.range (fun r:{r:Fin B // r.val < n}=>q4 (fun i:Fin B=>decide (i=r.1))))
    have hEq:q6 st.2.1=Ssub:=by
     apply le_antisymm
     ·intro v hv
      have hdecomp:v=∑ r:{r:Fin B // r.val < n},v r.1 • q4 (fun i:Fin B=>decide (i=r.1)):=by
       funext i
       simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,q4]
       by_cases hi:i.val < n
       ·rw [Finset.sum_eq_single ⟨i,hi⟩]
        ·simp
        ·intro r _ hne;have:i ≠ r.1:=fun e=>hne (Subtype.ext e.symm);simp [this]
        ·intro h;exact absurd (dL _) h
       ·rw [hsupp' v hv i (by omega)]
        symm;apply Finset.sum_eq_zero;intro r _
        have:i ≠ r.1:=fun e=>hi (e▸r.2);simp [this]
      rw [hdecomp]
      exact Submodule.sum_mem _ fun r _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨r,rfl⟩)
     ·rw [Submodule.span_le];rintro _ ⟨r,rfl⟩;exact hhas' r.1 r.2
    rw [← qo hE,hEq]
    have hli:LinearIndependent (ZMod 2) (fun r:{r:Fin B // r.val < n}=>q4 (fun i:Fin B=>decide (i=r.1))):=by
     rw [Fintype.linearIndependent_iff]
     intro g hg r
     have h1:=congrFun hg r.1
     simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,q4] at h1
     rw [Finset.sum_eq_single r] at h1
     ·simpa using h1
     ·intro r' _ hne;have:r.1 ≠ r'.1:=fun e=>hne (Subtype.ext e.symm);simp [this]
     ·intro h;exact absurd (dL r) h
    rw [finrank_span_eq_card hli]
    have hcard:Fintype.card {r:Fin B // r.val < n}=n:=by
     rw [Fintype.card_subtype]
     conv_rhs=>rw [← Fintype.card_fin n,← Finset.card_univ]
     refine Finset.card_bij (fun (r:Fin B) hr=>(⟨r.val,(Finset.mem_filter.mp hr).2⟩:Fin n)) ?_ ?_ ?_
     ·intro _ _;exact dL _
     ·intro a _ b _ h;exact Fin.ext (by simpa using congrArg Fin.val h)
     ·intro i _;exact ⟨⟨i.val,lt_of_lt_of_le i.isLt hn⟩,Finset.mem_filter.mpr ⟨dL _,i.isLt⟩,Fin.ext rfl⟩
    exact hcard
   by_cases hred:qK (q8 st.2.1 erk)=true
   ·have hnot:q4 erk∉q6 st.2.1:=by
     intro hin
     have h0:=(qG hE erk).mpr hin
     rw [h0] at hred;simp [qK,q2] at hred
    obtain ⟨hE',hsp'⟩:=jG st.2.1 hE erk
    have hrk':=jQ hE hnot
    have hleB':q3 (qC st.2.1 erk) ≤ B:=by
     unfold q3;exact (Finset.card_le_univ _).trans (by simp)
    dsimp only [step2]
    rw [show (fun i=>decide (i=rk))=erk from rfl,if_pos hred]
    dsimp only
    refine ⟨hE',by omega,by omega,?_,?_,?_,?_,?_⟩
    ·rw [hsp',hsp]
     apply le_antisymm
     ·refine sup_le ?_ ?_
      ·rw [Submodule.span_le];rintro _ ⟨c,hc,rfl⟩
       have hne:c.val ≠ st.1:=by omega
       exact Submodule.subset_span ⟨c,by omega,by simp [hne]⟩
      ·rw [Submodule.span_singleton_le_iff_mem]
       exact Submodule.subset_span ⟨⟨st.1,by omega⟩,by dsimp;omega,by simp [erk]⟩
     ·rw [Submodule.span_le];rintro _ ⟨c,hc,rfl⟩
      by_cases hlt':c.val < st.1
      ·have hne:c.val ≠ st.1:=by omega
       simp only [hne,↓reduceIte]
       exact Submodule.mem_sup_left (Submodule.subset_span ⟨c,hlt',rfl⟩)
      ·have heq:c.val=st.1:=by omega
       simp only [heq,↓reduceIte]
       exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    ·intro c hc
     have hne:c.val ≠ st.1:=by omega
     simp only [hne,↓reduceIte];exact hcolsU c hc
    ·intro r hr
     rw [hsp']
     by_cases hlt':r.val < k
     ·exact Submodule.mem_sup_left (hhas r hlt')
     ·have hreq:r=rk:=Fin.ext (by dsimp [rk];omega)
      rw [hreq];exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    ·intro v hv r hr
     rw [hsp',Submodule.mem_sup] at hv
     obtain ⟨w1,hw1,w2,hw2,rfl⟩:=hv
     rw [Submodule.mem_span_singleton] at hw2
     obtain ⟨a,rfl⟩:=hw2
     simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hsupp w1 hw1 r (by omega),zero_add]
     have hne:r ≠ rk:=fun e=>by subst e;dsimp [rk] at hr;omega
     simp [q4,erk,hne]
    ·intro hTM_le
     by_cases hTM_k:q3 T_M ≤ k
     ·obtain ⟨hst_k,hst_hi⟩:=hhi hTM_k
      refine ⟨by omega,fun c hc1 hc2=>?_⟩
      by_cases hck:c.val < k
      ·have hne:c.val ≠ st.1:=by omega
       simp only [hne,↓reduceIte];exact hst_hi c hc1 hck
      ·have hceq:c=rk:=Fin.ext (by dsimp [rk];omega)
       have hceq':c.val=st.1:=by omega
       rw [if_pos hceq',hceq]
     ·have hTM_eq:q3 T_M=k+1:=by omega
      have hrk_eq:q3 (qC st.2.1 erk)=k+1:=by
       have hhas_new:∀ r:Fin B,r.val < k+1->q4 (fun i:Fin B=>decide (i=r))∈q6 (qC st.2.1 erk):=by
        intro r hr;rw [hsp']
        by_cases hlt':r.val < k
        ·exact Submodule.mem_sup_left (hhas r hlt')
        ·have hreq:r=rk:=Fin.ext (by dsimp [rk];omega)
         rw [hreq];exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
       have hsupp_new:∀ v:Fin B->ZMod 2,v∈q6 (qC st.2.1 erk)->∀ r:Fin B,k+1 ≤ r.val->v r=0:=by
        intro v hv r hr;rw [hsp',Submodule.mem_sup] at hv
        obtain ⟨w1,hw1,w2,hw2,rfl⟩:=hv
        rw [Submodule.mem_span_singleton] at hw2;obtain ⟨a,rfl⟩:=hw2
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hsupp w1 hw1 r (by omega),zero_add]
        have hne:r ≠ rk:=fun e=>by subst e;dsimp [rk] at hr;omega
        simp [q4,erk,hne]
       let Ssub:Submodule (ZMod 2) (Fin B->ZMod 2):=
        Submodule.span (ZMod 2) (Set.range (fun r:{r:Fin B // r.val < k+1}=>q4 (fun i:Fin B=>decide (i=r.1))))
       have hEq:q6 (qC st.2.1 erk)=Ssub:=by
        apply le_antisymm
        ·intro v hv
         have hdecomp:v=∑ r:{r:Fin B // r.val < k+1},v r.1 • q4 (fun i:Fin B=>decide (i=r.1)):=by
          funext i;simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,q4]
          by_cases hi:i.val < k+1
          ·rw [Finset.sum_eq_single ⟨i,hi⟩]
           ·simp
           ·intro r _ hne;have:i ≠ r.1:=fun e=>hne (Subtype.ext e.symm);simp [this]
           ·intro h;exact absurd (dL _) h
          ·rw [hsupp_new v hv i (by omega)]
           symm;apply Finset.sum_eq_zero;intro r _
           have:i ≠ r.1:=fun e=>hi (e▸r.2);simp [this]
         rw [hdecomp];exact Submodule.sum_mem _ fun r _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨r,rfl⟩)
        ·rw [Submodule.span_le];rintro _ ⟨r,rfl⟩;exact hhas_new r.1 r.2
       rw [← qo hE',hEq]
       have hli:LinearIndependent (ZMod 2) (fun r:{r:Fin B // r.val < k+1}=>q4 (fun i:Fin B=>decide (i=r.1))):=by
        rw [Fintype.linearIndependent_iff];intro g hg r
        have h1:=congrFun hg r.1
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,q4] at h1
        rw [Finset.sum_eq_single r] at h1
        ·simpa using h1
        ·intro r' _ hne;have:r.1 ≠ r'.1:=fun e=>hne (Subtype.ext e.symm);simp [this]
        ·intro h;exact absurd (dL r) h
       rw [finrank_span_eq_card hli,Fintype.card_subtype]
       conv_rhs=>rw [← Fintype.card_fin (k+1),← Finset.card_univ]
       refine Finset.card_bij (fun (r:Fin B) hr=>(⟨r.val,(Finset.mem_filter.mp hr).2⟩:Fin (k+1))) ?_ ?_ ?_
       ·intro _ _;exact dL _
       ·intro a _ b _ h;exact Fin.ext (by simpa using congrArg Fin.val h)
       ·intro i _;exact ⟨⟨i.val,lt_of_lt_of_le i.isLt hk⟩,Finset.mem_filter.mpr ⟨dL _,i.isLt⟩,Fin.ext rfl⟩
      exact ⟨by omega,fun _ hc1 hc2=>absurd (hc1.trans_lt hc2) (by omega)⟩
   ·have hin:q4 erk∈q6 st.2.1:=by
     have h0:q8 st.2.1 erk=q2 B:=by
      by_contra hne
      apply hred
      rw [ji]
      intro hz;exact hne (v7 (hz.trans (qh B).symm))
     exact (qG hE erk).mp h0
    have hlt_TM:k < q3 T_M:=by
     by_contra hge
     have h0:=hsupp (q4 erk) hin rk (by dsimp [rk];omega)
     simp [q4,erk] at h0
    dsimp only [step2]
    rw [show (fun i=>decide (i=rk))=erk from rfl,if_neg hred]
    refine ⟨hE,hrk,hleB,hsp,hcolsU,?_,?_,?_⟩
    ·intro r hr
     by_cases hlt':r.val < k
     ·exact hhas r hlt'
     ·have hreq:r=rk:=Fin.ext (by dsimp [rk];omega)
      rw [hreq];exact hin
    ·intro v hv r hr
     exact hsupp v hv r (by omega)
    ·intro hTM_le
     have hTM_eq:q3 T_M=k+1:=by omega
     have hrk_eq:q3 st.2.1=k+1:=hspan_top_le (k+1) hk
      (fun r hr=>by
       by_cases hlt':r.val < k
       ·exact hhas r hlt'
       ·have hreq:r=rk:=Fin.ext (by dsimp [rk];omega);rw [hreq];exact hin)
      (fun v hv r hr=>hsupp v hv r (by omega))
     exact ⟨by omega,fun _ hc1 hc2=>absurd (hc1.trans_lt hc2) (by omega)⟩
 have hst2:=hph2 B le_rfl
 rw [hBtake] at hst2
 set st2:=(dF B).foldl step2 st1
 obtain ⟨_,_,_,hst2_sp,hst2_colsU,hst2_has,_,hst2_hi⟩:=hst2
 obtain ⟨hst2_cnt,hst2_id⟩:=hst2_hi hBM
 refine ⟨?_,?_,?_⟩
 ·
  have htop:q6 st2.2.1=⊤:=by
   rw [eq_top_iff]
   intro v _
   have hdec:v=∑ r:Fin B,v r • q4 (fun i:Fin B=>decide (i=r)):=by
    funext i;simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,q4]
    rw [Finset.sum_eq_single i]
    ·simp
    ·intro r _ hne;have:i ≠ r:=hne.symm;simp [this]
    ·intro h;exact absurd (dL i) h
   rw [hdec]
   exact Submodule.sum_mem _ fun r _=>Submodule.smul_mem _ _ (hst2_has r r.isLt)
  have hrange:Submodule.span (ZMod 2) (Set.range (fun c:Fin B=>q4 (st2.2.2 c)))=⊤:=by
   rw [← htop,hst2_sp]
   congr 1;ext v
   constructor
   ·rintro ⟨c,rfl⟩;exact ⟨c,by omega,rfl⟩
   ·rintro ⟨c,_,rfl⟩;exact ⟨c,rfl⟩
  have hcoeff:∀ r:Fin B,∃ g:Fin B->ZMod 2,
    ∑ c:Fin B,g c • q4 (st2.2.2 c)=q4 (fun i:Fin B=>decide (i=r)):=by
   intro r
   have hmem:q4 (fun i:Fin B=>decide (i=r)) ∈
     Submodule.span (ZMod 2) (Set.range (fun c:Fin B=>q4 (st2.2.2 c))):=by
    rw [hrange];exact Submodule.mem_top
   rw [Submodule.mem_span_range_iff_exists_fun] at hmem
   exact hmem
  let N:Qd B:=fun c r=>decide (Classical.choose (hcoeff r) c=1)
  refine ⟨N,?_⟩
  apply y1
  rw [vC,jj]
  have hGdef:∀ i c,qk T_U T_M B i c=st2.2.2 c i:=fun _ _=>rfl
  ext i r
  simp only [Matrix.mul_apply,Matrix.one_apply,qm,hGdef,b2z]
  have hspec:=congrFun (Classical.choose_spec (hcoeff r)) i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,q4,dG] at hspec
  rw [← hspec]
  refine Finset.sum_congr rfl fun c _=>?_
  simp only [N]
  rcases qD (Classical.choose (hcoeff r) c) with h0 | h1
  ·simp [h0]
  ·simp [h1]
 ·intro j hj
  funext r
  exact congrFun (hst2_colsU j hj) r
 ·intro i j hij
  have hGdef:∀ i' c',qk T_U T_M B i' c'=st2.2.2 c' i':=fun _ _=>rfl
  rw [hGdef]
  rcases hij with hi | hj
  ·by_cases hjm:q3 T_M ≤ j.val
   ·exact congrFun (hst2_id j hjm j.isLt) i
   ·have hne:i ≠ j:=fun e=>by subst e;omega
    simp only [hne,decide_false]
    have hcol_in:q4 (st2.2.2 j)∈q6 (((dF B).take (q3 T_M)).foldl step2 st1).2.1:=by
     have hTM:=hph2 (q3 T_M) hBM
     obtain ⟨_,_,_,hTM_sp,_,_,_,hTM_hi⟩:=hTM
     obtain ⟨hTM_cnt,_⟩:=hTM_hi le_rfl
     have hst_eq:st2.2.2 j=(((dF B).take (q3 T_M)).foldl step2 st1).2.2 j:=by
      have hpres:∀ t,q3 T_M ≤ t->t ≤ B ->
        (((dF B).take t).foldl step2 st1).2.2 j =
        (((dF B).take (q3 T_M)).foldl step2 st1).2.2 j:=by
       intro t hge ht
       induction t with
       | zero=>
        have h0:q3 T_M=0:=by omega
        rw [h0]
       | succ t iht=>
        by_cases hgt:q3 T_M ≤ t
        ·have htake:(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
          rw [dJ (by simp;omega)];simp
         rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
         have hcnt_t:=((hph2 t (Nat.le_of_succ_le ht)).2.2.2.2.2.2.2 hgt).1
         dsimp only [step2]
         split_ifs with h1
         ·dsimp only
          have hne_jt:j.val ≠ (((dF B).take t).foldl step2 st1).1:=by omega
          rw [if_neg hne_jt]
          exact iht hgt (Nat.le_of_succ_le ht)
         ·exact iht hgt (Nat.le_of_succ_le ht)
        ·have:t+1=q3 T_M:=by omega
         rw [this]
      have h1:=hpres B hBM le_rfl
      rwa [hBtake] at h1
     rw [hst_eq,hTM_sp]
     exact Submodule.subset_span ⟨j,by omega,rfl⟩
    have h0:=(hph2 (q3 T_M) hBM).2.2.2.2.2.2.1 _ hcol_in i (by simp [hi])
    simp only [q4] at h0
    cases hval:st2.2.2 j i
    ·rfl
    ·simp [hval] at h0
  ·exact congrFun (hst2_id j hj j.isLt) i
def z5 {B:ℕ} {α:Type*}
  (onSwap:Fin B->Fin B->α->α) (onAdd:Fin B->Fin B->α->α)
  (row:Fin B) (st:Qd B × α):Qd B × α:=
 let isPiv (c:Fin B):Bool:=
  decide (row.val ≤ c.val/\st.1 row c=true /\
   ∀ c':Fin B,row.val ≤ c'.val->c'.val < c.val->st.1 row c'=false)
 let st1:=(dF B).foldl (fun s c=>
  if isPiv c=true then (qJ s.1 row c,onSwap row c s.2) else s) st
 (dF B).foldl (fun s c=>
  if c ≠ row/\s.1 row c=true then (vD s.1 row c,onAdd row c s.2) else s) st1
def yt {B:ℕ} {α:Type*}
  (onSwap:Fin B->Fin B->α->α) (onAdd:Fin B->Fin B->α->α)
  (G:Qd B) (init:α):Qd B × α:=
 (dF B).foldl (fun st row=>z5 onSwap onAdd row st) (G,init)
lemma zN {B:ℕ} {α:Type*}
  (onSwap:Fin B->Fin B->α->α) (onAdd:Fin B->Fin B->α->α)
  (Inv:Qd B->α->Prop)
  (hSwap:∀ M a u v,Inv M a->Inv (qJ M u v) (onSwap u v a))
  (hAdd:∀ M a src dst,src ≠ dst->Inv M a->Inv (vD M src dst) (onAdd src dst a))
  {G:Qd B} (hG:Q7 G) {init:α} (hinit:Inv G init) :
  let res:=yt onSwap onAdd G init
  res.1=vT B/\Inv (vT B) res.2:=by
 have hgo:∀ k ≤ B,
   let st:=((dF B).take k).foldl (fun st row=>z5 onSwap onAdd row st) (G,init)
   Q7 st.1/\Inv st.1 st.2 /\
   (∀ r:Fin B,r.val < k->∀ c:Fin B,st.1 r c=decide (r=c)):=by
  intro k
  induction k with
  | zero=>
   intro _;simp only [List.take_zero,List.foldl_nil]
   exact ⟨hG,hinit,fun _ h=>absurd h (by omega)⟩
  | succ k ih=>
   intro hk
   obtain ⟨hM,hI,hprev⟩:=ih (Nat.le_of_succ_le hk)
   have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   set st:=((dF B).take k).foldl (fun st row=>z5 onSwap onAdd row st) (G,init)
   set row:Fin B:=⟨k,hk⟩
   have hex:=yM hM row hprev
   set Pset:=Finset.univ.filter (fun c:Fin B=>row.val ≤ c.val/\st.1 row c=true)
   have hPne:Pset.Nonempty:=by
    obtain ⟨piv,hp1,hp2⟩:=hex
    exact ⟨piv,Finset.mem_filter.mpr ⟨dL _,hp1,hp2⟩⟩
   set piv:=Pset.min' hPne
   have hpiv_m:=(Finset.mem_filter.mp (Finset.min'_mem Pset hPne)).2
   let isPiv (c:Fin B):Bool:=
    decide (row.val ≤ c.val/\st.1 row c=true /\
     ∀ c':Fin B,row.val ≤ c'.val->c'.val < c.val->st.1 row c'=false)
   have hisPiv_iff:∀ c:Fin B,isPiv c=true ↔ c=piv:=by
    intro c
    simp only [isPiv,dG]
    constructor
    ·rintro ⟨hc1,hc2,hmin⟩
     have hle1:piv ≤ c:=Finset.min'_le Pset c (Finset.mem_filter.mpr ⟨dL _,hc1,hc2⟩)
     apply le_antisymm
     ·by_contra hgt;push Not at hgt
      have h0:=hmin piv hpiv_m.1 hgt
      rw [hpiv_m.2] at h0;exact Bool.false_ne_true h0.symm
     ·exact hle1
    ·rintro rfl
     refine ⟨hpiv_m.1,hpiv_m.2,fun c' hc1' hlt'=>?_⟩
     by_contra hne
     have ht:st.1 row c'=true:=by cases h:st.1 row c' <;> simp_all
     have hle:=Finset.min'_le Pset c' (Finset.mem_filter.mpr ⟨dL _,hc1',ht⟩)
     have:piv.val ≤ c'.val:=hle
     omega
   have hst1_eq:(dF B).foldl
     (fun s c=>if isPiv c=true then (qJ s.1 row c,onSwap row c s.2) else s) st =
     (qJ st.1 row piv,onSwap row piv st.2):=by
    have hstep:∀ t ≤ B,
      ((dF B).take t).foldl
       (fun s c=>if isPiv c=true then (qJ s.1 row c,onSwap row c s.2) else s) st =
      if piv.val < t then (qJ st.1 row piv,onSwap row piv st.2) else st:=by
     intro t
     induction t with
     | zero=>intro _;simp
     | succ t iht=>
      intro ht
      have ht':(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
       rw [dJ (by simp;omega)];simp
      rw [ht',List.foldl_append,List.foldl_cons,List.foldl_nil,iht (Nat.le_of_succ_le ht)]
      by_cases heq:(⟨t,ht⟩:Fin B)=piv
      ·have hp1:isPiv ⟨t,ht⟩=true:=(hisPiv_iff _).mpr heq
       have hpv:piv.val=t:=congrArg Fin.val heq.symm
       have hnot:¬ piv.val < t:=by omega
       have hlt:piv.val < t+1:=by omega
       rw [if_neg hnot,if_pos hlt,if_pos hp1,heq]
      ·have hp0:isPiv ⟨t,ht⟩=false:=Bool.eq_false_iff.mpr fun h=>heq ((hisPiv_iff _).mp h)
       have hiff:piv.val < t+1 ↔ piv.val < t:=by
        have hne':piv.val ≠ t:=fun e=>heq (Fin.ext e.symm)
        omega
       simp [hp0,hiff]
    have hm:=hstep B le_rfl
    have htm:(dF B).take B=dF B:=by simp
    rw [htm,if_pos piv.isLt] at hm
    exact hm
   unfold z5
   dsimp only
   rw [show (dF B).foldl (fun s c=>
    if decide (row.val ≤ c.val/\st.1 row c=true /\
     ∀ c':Fin B,row.val ≤ c'.val->c'.val < c.val->st.1 row c'=false)=true
    then (qJ s.1 row c,onSwap row c s.2) else s) st =
    (qJ st.1 row piv,onSwap row piv st.2) from hst1_eq]
   set st1:=(qJ st.1 row piv,onSwap row piv st.2)
   have hst1_inv:Q7 st1.1:=zC hM row piv
   have hst1_I:Inv st1.1 st1.2:=hSwap st.1 st.2 row piv hI
   have hst1_prev:∀ r:Fin B,r.val < k->∀ c:Fin B,st1.1 r c=decide (r=c):=by
    intro r hr c
    dsimp only [st1,qJ]
    have hne1:r ≠ row:=fun e=>by subst e;dsimp [row] at hr;omega
    have hne2:r ≠ piv:=fun e=>by subst e;have:=hpiv_m.1;dsimp [row] at this;omega
    by_cases h1:c=row
    ·subst h1;simp [hprev r hr piv,hne1,hne2]
    ·by_cases h2:c=piv
     ·subst h2;simp [h1,hprev r hr row,hne1,hne2]
     ·simp [h1,h2,hprev r hr c]
   have hst1_diag:st1.1 row row=true:=by
    dsimp only [st1,qJ];simp;exact hpiv_m.2
   have hadd_loop:∀ t ≤ B,
     let s:=((dF B).take t).foldl
      (fun s c=>if c ≠ row/\s.1 row c=true then (vD s.1 row c,onAdd row c s.2) else s) st1
     Q7 s.1/\Inv s.1 s.2 /\
     (∀ r:Fin B,r.val < k->∀ c:Fin B,s.1 r c=decide (r=c)) /\
     s.1 row row=true /\
     (∀ c:Fin B,c.val < t->s.1 row c=decide (row=c)):=by
    intro t
    induction t with
    | zero=>
     intro _;simp only [List.take_zero,List.foldl_nil]
     exact ⟨hst1_inv,hst1_I,hst1_prev,hst1_diag,fun _ h=>absurd h (by omega)⟩
    | succ t iht=>
     intro ht
     obtain ⟨hMs,hIs,hps,hds,hcs⟩:=iht (Nat.le_of_succ_le ht)
     have ht':(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
      rw [dJ (by simp;omega)];simp
     dsimp only
     rw [ht',List.foldl_append,List.foldl_cons,List.foldl_nil]
     set s:=((dF B).take t).foldl
      (fun s c=>if c ≠ row/\s.1 row c=true then (vD s.1 row c,onAdd row c s.2) else s) st1
     set ct:Fin B:=⟨t,ht⟩
     by_cases hcond:ct ≠ row/\s.1 row ct=true
     ·rw [if_pos hcond]
      refine ⟨zI hMs hcond.1.symm,hAdd s.1 s.2 row ct hcond.1.symm hIs,?_,?_,?_⟩
      ·intro r hr c
       dsimp only [vD]
       by_cases hc:c=ct
       ·subst hc
        have hne_r:r ≠ row:=fun e=>by subst e;dsimp [row] at hr;omega
        simp [hps r hr row,hne_r,hps r hr ct]
       ·simp [hc,hps r hr c]
      ·simp [vD,hcond.1.symm,hds]
      ·intro c hc
       by_cases hlt':c.val < t
       ·have hne:c ≠ ct:=fun e=>by subst e;dsimp [ct] at hlt';omega
        simp [vD,hne,hcs c hlt']
       ·have hceq:c=ct:=Fin.ext (by dsimp [ct];omega)
        subst hceq
        simp [vD,hcond.1.symm,hcond.2,hds]
     ·rw [if_neg hcond]
      refine ⟨hMs,hIs,hps,hds,fun c hc=>?_⟩
      by_cases hlt':c.val < t
      ·exact hcs c hlt'
      ·have hceq:c=ct:=Fin.ext (by dsimp [ct];omega)
       subst hceq
       by_cases hcr:ct=row
       ·rw [hcr];simp [hds]
       ·have hf:s.1 row ct=false:=by
         by_contra hne'
         have ht':s.1 row ct=true:=by cases h:s.1 row ct <;> simp_all
         exact hcond ⟨hcr,ht'⟩
        simp [hf,Ne.symm hcr]
   obtain ⟨hMf,hIf,hpf,_,hcf⟩:=hadd_loop B le_rfl
   have htm:(dF B).take B=dF B:=by simp
   rw [htm] at hMf hIf hpf hcf
   refine ⟨hMf,hIf,fun r hr c=>?_⟩
   by_cases hlt':r.val < k
   ·exact hpf r hlt' c
   ·have hreq:r=row:=Fin.ext (by dsimp [row];omega)
    subst hreq;exact hcf c c.isLt
 obtain ⟨_,hIf,hall⟩:=hgo B le_rfl
 have htm:(dF B).take B=dF B:=by simp
 rw [htm] at hIf hall
 have hid:(yt onSwap onAdd G init).1=vT B:=by
  funext r c;exact hall r r.isLt c
 exact ⟨hid,hid▸hIf⟩
def j1 {B:ℕ} (G:Qd B):Qd B:=
 (yt (fun u v M=>qJ M u v) (fun src dst M=>vD M src dst) G (vT B)).2
lemma jF {B:ℕ} {G:Qd B} (hG:Q7 G) :
  v3 G (j1 G)=vT B/\v3 (j1 G) G=vT B:=by
 have h:=(zN (fun u v M=>qJ M u v) (fun src dst M=>vD M src dst)
  (fun M N=>v3 G N=M)
  (fun M N u v hMN=>by rw [jX,hMN])
  (fun M N src dst _ hMN=>by rw [ye,hMN])
  hG (vU G)).2
 exact ⟨h,g7 h⟩
def jZ {B:ℕ} (G:Qd B) (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 (yt (fun u v tbl idx=>tbl (vY idx u v))
  (fun src dst tbl idx=>tbl (zQ idx dst src)) G DP).2
lemma zx {B:ℕ} {G:Qd B} (hG:Q7 G) (DP:Fin (2^B)->ℕ)
  (x:Q1 B) :
  jZ G DP (qa x)=DP (qa (qT (j1 G) x)):=by
 obtain ⟨_,hInvG⟩:=jF hG
 have h:=(zN
  (fun u v (tbl:Fin (2^B)->ℕ) idx=>tbl (vY idx u v))
  (fun src dst (tbl:Fin (2^B)->ℕ) idx=>tbl (zQ idx dst src))
  (fun M tbl=>∀ v:Q1 B,tbl (qa v)=DP (qa (qT (v3 (j1 G) M) v)))
  (fun M tbl u v hI w=>by
   dsimp only [vY]
   rw [vK,hI,jX,gE])
  (fun M tbl src dst hne hI w=>by
   dsimp only [zQ]
   rw [vK,hI,ye,gV _ hne])
  hG (fun w=>by rw [hInvG,yj])).2
 have hx:=h x
 rwa [vU] at hx
lemma dp {B:ℕ} {G:Qd B} (hG:Q7 G)
  (DP:Fin (2^B)->ℕ) (x:Q1 B) :
  jZ G DP (qa (qT G x))=DP (qa x):=by
 rw [zx hG DP (qT G x),← jr,(jF hG).2,yj]
end StaticGL
section StaticGLCircuit
abbrev CB.Qa.trans {nIn:ℕ} {c₁ c₂ c₃:CB nIn}
  (h12:c₁.Qa c₂) (h23:c₂.Qa c₃):c₁.Qa c₃:=
 CB.q0 h12 h23
structure Qv (nIn:ℕ) (c:CB nIn) (B:ℕ) (f:(Fin nIn->Bool)->Qd B) where
 cols:∀ col:Fin B,Q2 nIn c B (fun x r=>f x r col)
def Qv.lift {nIn B:ℕ} {c c':CB nIn} {f:(Fin nIn->Bool)->Qd B}
  (hext:c.Qa c') (M:Qv nIn c B f):Qv nIn c' B f:=
 ⟨fun col=>(M.cols col).lift hext⟩
def Qv.cast {nIn B:ℕ} {c:CB nIn} {f g:(Fin nIn->Bool)->Qd B}
  (h:∀ x r col,f x r col=g x r col) (M:Qv nIn c B f):Qv nIn c B g:=
 ⟨fun col=>(M.cols col).cast (fun x r=>h x r col)⟩
def Qv.at {nIn B:ℕ} {c:CB nIn} {f:(Fin nIn->Bool)->Qd B}
  (M:Qv nIn c B f) (r col:Fin B):Q4 nIn c (fun x=>f x r col):=
 (M.cols col).at r
structure SDP (nIn:ℕ) (c:CB nIn) (B W:ℕ) (f:(Fin nIn->Bool)->Fin (2^B)->ℕ) where
 tbl:∀ idx:Fin (2^B),Q9 nIn c W (fun x=>f x idx)
def SDP.lift {nIn B W:ℕ} {c c':CB nIn} {f:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (hext:c.Qa c') (D:SDP nIn c B W f):SDP nIn c' B W f:=
 ⟨fun idx=>(D.tbl idx).lift hext⟩
def SDP.cast {nIn B W:ℕ} {c:CB nIn} {f g:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (h:∀ x idx,f x idx=g x idx) (D:SDP nIn c B W f):SDP nIn c B W g:=
 ⟨fun idx=>(D.tbl idx).cast (fun x=>h x idx)⟩
def yW {nIn N M:ℕ} (c:CB nIn)
  {fIdx:(Fin nIn->Bool)->Fin N} {fVec:(Fin nIn->Bool)->Fin N->Fin M->Bool}
  (oh:Q2 nIn c N (fun x i=>decide (fIdx x=i)))
  (vecs:∀ i:Fin N,Q2 nIn c M (fun x=>fVec x i)) :
  Q0 nIn c (M*(1+N*2)) (fun c'=>Q2 nIn c' M (fun x=>fVec x (fIdx x))):=
 j8 (Bstep:=1+N*2) M (fun x j=>fVec x (fIdx x) j) c fun j c0 h0=>
  Q0.weaken (by omega)<|
  (vJ c0 false).bind fun c1 h1 vf=>
  let Acc (t:ℕ) (_:t ≤ N) (c2:CB nIn):Type:=
   Q4 nIn c2 (fun x=>decide (∃ i:Fin N,i.val < t/\fIdx x=i/\fVec x i j=true))
  have hinit:Acc 0 (Nat.zero_le N) c1:=vf.cast fun _=>by simp
  (Q0.qe (Bstep:=2) N Acc c1 hinit fun t ht c2 h2 acc=>
   let ti:Fin N:=⟨t,ht⟩
   let h02:=h0.trans (h1.trans h2)
   (vg c2 ((oh.at ti).lift h02) (((vecs ti).at j).lift h02)).bind fun c3 h3 vand=>
   (yr c3 (acc.lift h3) vand).bind fun _ _ vor=>
   Q0.pure<|vor.cast fun x=>by
    apply Bool.eq_iff_iff.mpr
    simp only [dH,dI,dG]
    constructor
    ·rintro (⟨i,hi,h1',h2'⟩ | ⟨h1',h2'⟩)
     ·exact ⟨i,by omega,h1',h2'⟩
     ·exact ⟨ti,by dsimp [ti];omega,h1',h2'⟩
    ·rintro ⟨i,hi,h1',h2'⟩
     by_cases hlt:i.val < t
     ·left;exact ⟨i,hlt,h1',h2'⟩
     ·right;have heq:i=ti:=Fin.ext (by dsimp [ti];omega);subst heq;exact ⟨h1',h2'⟩).bind fun _ _ vF=>
  Q0.pure<|vF.cast fun x=>by
   apply Bool.eq_iff_iff.mpr
   simp only [dG]
   exact ⟨fun ⟨i,_,h1',h2'⟩=>h1'▸h2',fun h=>⟨fIdx x,(fIdx x).isLt,rfl,h⟩⟩
def gS {nIn:ℕ} (c:CB nIn) (B:ℕ) (M:Qd B) :
  Q0 nIn c (B*B) (fun c'=>Qv nIn c' B (fun _=>M)):=
 let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=
  ∀ col:Fin B,col.val < t->Q2 nIn c1 B (fun _ r=>M r col)
 have hinit:Acc 0 (Nat.zero_le B) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=B) B Acc c hinit fun t ht c1 _ acc=>
  Q0.weaken (by omega)<|
  let ct:Fin B:=⟨t,ht⟩
  (vq c1 B (fun r=>M r ct)).bind fun _ h2 vc=>
  Q0.pure fun col hcol=>
   if hlt:col.val < t then (acc col hlt).lift h2
   else
    have heq:col=ct:=Fin.ext (by dsimp [ct];omega)
    heq▸vc).bind fun _ _ all=>
 Q0.pure ⟨fun col=>all col col.isLt⟩
def gd {nIn m:ℕ} (c:CB nIn)
  {fp:(Fin nIn->Bool)->Bool} {f1 f2:(Fin nIn->Bool)->Q6 m}
  (cond:Q4 nIn c fp) (T1:Q8 nIn c m f1) (T2:Q8 nIn c m f2) :
  Q0 nIn c (m*(4*m))
   (fun c'=>Q8 nIn c' m (fun x=>if fp x=true then f1 x else f2 x)):=
 let Acc (t:ℕ) (_:t ≤ m) (c1:CB nIn):Type:=
  ∀ r:Fin m,r.val < t->Q2 nIn c1 m (fun x j=>(if fp x=true then f1 x else f2 x) r j)
 have hinit:Acc 0 (Nat.zero_le m) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=4*m) m Acc c hinit fun t ht c1 h1 acc=>
  Q0.weaken (by omega)<|
  let rt:Fin m:=⟨t,ht⟩
  (vd c1 (cond.lift h1) ((T1.rows rt).lift h1) ((T2.rows rt).lift h1)).bind fun _ h2 vrow=>
  Q0.pure fun r hr=>
   if hlt:r.val < t then (acc r hlt).lift h2
   else
    have heq:r=rt:=Fin.ext (by dsimp [rt];omega)
    heq▸vrow.cast fun x j=>by by_cases h:fp x=true <;> simp [h]).bind fun _ _ all=>
 Q0.pure ⟨fun r=>all r r.isLt⟩
def zL {nIn B:ℕ} (c:CB nIn)
  {fp:(Fin nIn->Bool)->Bool} {fM:(Fin nIn->Bool)->Qd B}
  (u v:Fin B) (cond:Q4 nIn c fp) (M:Qv nIn c B fM) :
  Q0 nIn c (8*B)
   (fun c'=>Qv nIn c' B (fun x=>if fp x=true then qJ (fM x) u v else fM x)):=
 Q0.weaken (by omega)<|
 (vd c cond (M.cols v) (M.cols u)).bind fun c1 h1 colU=>
 (vd c1 (cond.lift h1) ((M.cols u).lift h1) ((M.cols v).lift h1)).bind fun _ h2 colV=>
 Q0.pure ⟨fun col=>
  if hcu:col=u then
   (colU.lift h2).cast fun x r=>by subst hcu;by_cases h:fp x=true <;> simp [h,qJ]
  else if hcv:col=v then
   colV.cast fun x r=>by subst hcv;by_cases h:fp x=true <;> simp [h,qJ,hcu]
  else
   ((M.cols col).lift (h1.trans h2)).cast fun x r=>by by_cases h:fp x=true <;> simp [h,qJ,hcu,hcv]⟩
def g6 {nIn B:ℕ} (c:CB nIn)
  {fp:(Fin nIn->Bool)->Bool} {fM:(Fin nIn->Bool)->Qd B}
  (src dst:Fin B) (cond:Q4 nIn c fp) (M:Qv nIn c B fM) :
  Q0 nIn c (8*B)
   (fun c'=>Qv nIn c' B (fun x=>if fp x=true then vD (fM x) src dst else fM x)):=
 Q0.weaken (by omega)<|
 (j3 c (M.cols dst) (M.cols src)).bind fun c1 h1 xV=>
 (vd c1 (cond.lift h1) xV ((M.cols dst).lift h1)).bind fun _ h2 colDst=>
 Q0.pure ⟨fun col=>
  if hcd:col=dst then
   colDst.cast fun x r=>by subst hcd;by_cases h:fp x=true <;> simp [h,vD]
  else
   ((M.cols col).lift (h1.trans h2)).cast fun x r=>by by_cases h:fp x=true <;> simp [h,vD,hcd]⟩
def g5 {nIn B W:ℕ} (c:CB nIn)
  {fp:(Fin nIn->Bool)->Bool} {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (u v:Fin B) (cond:Q4 nIn c fp) (D:SDP nIn c B W fD) :
  Q0 nIn c (2^B*(4*W))
   (fun c'=>SDP nIn c' B W (fun x idx=>if fp x=true then fD x (vY idx u v) else fD x idx)):=
 let Acc (t:ℕ) (_:t ≤ 2^B) (c1:CB nIn):Type:=
  ∀ idx:Fin (2^B),idx.val < t ->
   Q9 nIn c1 W (fun x=>if fp x=true then fD x (vY idx u v) else fD x idx)
 have hinit:Acc 0 (Nat.zero_le _) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=4*W) (2^B) Acc c hinit fun t ht c1 h1 acc=>
  Q0.weaken (by omega)<|
  let it:Fin (2^B):=⟨t,ht⟩
  (vH c1 (cond.lift h1) ((D.tbl (vY it u v)).lift h1) ((D.tbl it).lift h1)).bind fun _ h2 vnew=>
  Q0.pure fun idx hidx=>
   if hlt:idx.val < t then (acc idx hlt).lift h2
   else
    have heq:idx=it:=Fin.ext (by dsimp [it];omega)
    heq▸vnew).bind fun _ _ all=>
 Q0.pure ⟨fun idx=>all idx idx.isLt⟩
def dl {nIn B W:ℕ} (c:CB nIn)
  {fp:(Fin nIn->Bool)->Bool} {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (src dst:Fin B) (cond:Q4 nIn c fp) (D:SDP nIn c B W fD) :
  Q0 nIn c (2^B*(4*W))
   (fun c'=>SDP nIn c' B W (fun x idx=>if fp x=true then fD x (zQ idx dst src) else fD x idx)):=
 let Acc (t:ℕ) (_:t ≤ 2^B) (c1:CB nIn):Type:=
  ∀ idx:Fin (2^B),idx.val < t ->
   Q9 nIn c1 W (fun x=>if fp x=true then fD x (zQ idx dst src) else fD x idx)
 have hinit:Acc 0 (Nat.zero_le _) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=4*W) (2^B) Acc c hinit fun t ht c1 h1 acc=>
  Q0.weaken (by omega)<|
  let it:Fin (2^B):=⟨t,ht⟩
  (vH c1 (cond.lift h1) ((D.tbl (zQ it dst src)).lift h1) ((D.tbl it).lift h1)).bind fun _ h2 vnew=>
  Q0.pure fun idx hidx=>
   if hlt:idx.val < t then (acc idx hlt).lift h2
   else
    have heq:idx=it:=Fin.ext (by dsimp [it];omega)
    heq▸vnew).bind fun _ _ all=>
 Q0.pure ⟨fun idx=>all idx idx.isLt⟩
def QH (m B W:ℕ):ℕ:=
 2*W+B*m+m*(1+15*W+B*(2+7*W+4*m))
def zB {nIn m B W:ℕ} (c:CB nIn)
  (hW:1 ≤ W) (hmW:m < 2^W) (hBW:B < 2^W)
  {fT:(Fin nIn->Bool)->Q6 m} (T:Q8 nIn c m fT) :
  Q0 nIn c (QH m B W)
   (fun c'=>∀ j:Fin B,Q2 nIn c' m (fun x=>qc (fT x) B j)):=
 Q0.weaken (by unfold QH;omega)<|
 (qS c W 0 (Nat.two_pow_pos W)).bind fun c0 h0 v0=>
 (qS c0 W 1 (Nat.one_lt_two_pow (by omega))).bind fun c1 h1 v1=>
 let ZAcc (s:ℕ) (_:s ≤ B) (c2:CB nIn):Type:=
  ∀ j:Fin B,j.val < s->Q2 nIn c2 m (fun _=>q2 m)
 have hZinit:ZAcc 0 (Nat.zero_le B) c1:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=m) B ZAcc c1 hZinit fun s hs c2 _ zacc=>
  Q0.weaken (by omega)<|
  (vq c2 m (q2 m)).bind fun _ h3 vz=>
  Q0.pure fun j hj=>
   if hlt:j.val < s then (zacc j hlt).lift h3 else vz).bind fun c2 h2 zrows=>
 let stAt (t:ℕ) (x:Fin nIn->Bool):ℕ × (Fin B->Q1 m):=
  ((dF m).take t).foldl (fun st col=>
   if fT x col col=true then (st.1+1,fun j=>if j.val=st.1 then fT x col else st.2 j) else st)
   (0,fun _=>q2 m)
 have hst_le:∀ t x,(stAt t x).1 ≤ t:=by
  intro t x;induction t with
  | zero=>simp [stAt]
  | succ t ih=>
   by_cases ht:t < m
   ·have htake:(dF m).take (t+1)=(dF m).take t ++ [⟨t,ht⟩]:=by
     rw [dJ (by simp;omega)];simp
    simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    split_ifs <;> dsimp only [stAt] at ih <;> omega
   ·have htake:(dF m).take (t+1)=(dF m).take t:=by
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]
    simp only [stAt,htake];dsimp only [stAt] at ih;omega
 let Acc (t:ℕ) (_:t ≤ m) (c3:CB nIn):Type:=
  Q9 nIn c3 W (fun x=>(stAt t x).1) × (∀ j:Fin B,Q2 nIn c3 m (fun x=>(stAt t x).2 j))
 have hinit:Acc 0 (Nat.zero_le m) c2:=
  ⟨(v0.lift (h1.trans h2)).cast (fun _=>rfl),fun j=>(zrows j j.isLt).cast (fun _ _=>rfl)⟩
 let h02:=h0.trans (h1.trans h2)
 (Q0.qe (Bstep:=1+15*W+B*(2+7*W+4*m)) m Acc c2 hinit fun t ht c3 h3 ⟨cnt,rows⟩=>
  Q0.weaken (by omega)<|
  let ct:Fin m:=⟨t,ht⟩
  let h03:=h02.trans h3
  let isPiv:=((T.rows ct).at ct).lift h03
  have hsum:∀ x,(stAt t x).1+1 < 2^W:=fun x=>by have:=hst_le t x;omega
  (z4 c3 cnt (v1.lift (h2.trans h3)) hsum).bind fun c4 h4 cnt1=>
  (vH c4 (isPiv.lift h4) cnt1 (cnt.lift h4)).bind fun c5 h5 cnt'=>
  let RAcc (s:ℕ) (_:s ≤ B) (c6:CB nIn):Type:=
   ∀ j:Fin B,j.val < s->Q2 nIn c6 m (fun x=>
    if fT x ct ct=true then (if j.val=(stAt t x).1 then fT x ct else (stAt t x).2 j) else (stAt t x).2 j)
  have hRinit:RAcc 0 (Nat.zero_le B) c5:=fun _ h=>absurd h (by omega)
  let h35:=h4.trans h5
  (Q0.qe (Bstep:=2+7*W+4*m) B RAcc c5 hRinit fun s hs c6 h6 racc=>
   Q0.weaken (by omega)<|
   let js:Fin B:=⟨s,hs⟩
   let h36:=h35.trans h6
   (qS c6 W s (lt_trans hs hBW)).bind fun c7 h7 cs=>
   (zH c7 (cnt.lift (h36.trans h7)) cs).bind fun c8 h8 veq=>
   (vg c8 (isPiv.lift (h36.trans (h7.trans h8))) veq).bind fun c9 h9 vupd=>
   let h69:=h7.trans (h8.trans h9)
   (vd c9 vupd ((T.rows ct).lift (h03.trans (h36.trans h69)))
    ((rows js).lift (h36.trans h69))).bind fun _ h10 vrow=>
   Q0.pure fun j hj=>
    if hlt:j.val < s then (racc j hlt).lift (h69.trans h10)
    else
     have heq:j=js:=Fin.ext (by dsimp [js];omega)
     heq▸vrow.cast fun x q=>by
      by_cases h1':fT x ct ct=true <;> by_cases h2':(stAt t x).1=s
      ·simp [js,h1',h2']
      ·simp [js,h1',h2',Ne.symm h2']
      ·simp [js,h1',h2']
      ·simp [js,h1',h2']).bind fun _ h6 rows'=>
  have htake:(dF m).take (t+1)=(dF m).take t ++ [ct]:=by
   rw [dJ (by simp;omega)];simp [ct]
  have hstep:∀ x,stAt (t+1) x =
    (if fT x ct ct=true then ((stAt t x).1+1,fun j=>if j.val=(stAt t x).1 then fT x ct else (stAt t x).2 j)
    else stAt t x):=fun x=>by
   change ((dF m).take (t+1)).foldl _ _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨(cnt'.lift h6).cast fun x=>by rw [hstep x];by_cases h:fT x ct ct=true <;> simp [h],
   fun j=>(rows' j j.isLt).cast fun x q=>by rw [hstep x];by_cases h:fT x ct ct=true <;> simp [h]⟩).bind fun _ _ ⟨_,rowsF⟩=>
 Q0.pure fun j=>(rowsF j).cast fun x q=>by
  simp only [stAt,qc,show (dF m).take m=dF m by simp]
def Qk (m B W:ℕ):ℕ:=
 2*W+B+m*(2+8*m+15*W+B*(6+7*W))
def yS {nIn m B W:ℕ} (c:CB nIn)
  (hW:1 ≤ W) (hmW:m < 2^W) (hBW:B < 2^W)
  {fT:(Fin nIn->Bool)->Q6 m} {fv:(Fin nIn->Bool)->Q1 m}
  (T:Q8 nIn c m fT) (v:Q2 nIn c m fv) :
  Q0 nIn c (Qk m B W)
   (fun c'=>Q2 nIn c' B (fun x=>qf (fT x) (fv x) B)):=
 Q0.weaken (by unfold Qk;omega)<|
 (qS c W 0 (Nat.two_pow_pos W)).bind fun c0 h0 v0=>
 (qS c0 W 1 (Nat.one_lt_two_pow (by omega))).bind fun c1 h1 v1=>
 (vq c1 B (q2 B)).bind fun c2 h2 vzb=>
 let stAt (t:ℕ) (x:Fin nIn->Bool):ℕ × Q1 m × Q1 B:=
  ((dF m).take t).foldl (fun st col=>
   if fT x col col=true then
    let b:=st.2.1 col
    (st.1+1,if b=true then q5 st.2.1 (fT x col) else st.2.1,
     fun j=>if j.val=st.1 then b else st.2.2 j)
   else st) (0,fv x,q2 B)
 have hst_le:∀ t x,(stAt t x).1 ≤ t:=by
  intro t x;induction t with
  | zero=>simp [stAt]
  | succ t ih=>
   by_cases ht:t < m
   ·have htake:(dF m).take (t+1)=(dF m).take t ++ [⟨t,ht⟩]:=by
     rw [dJ (by simp;omega)];simp
    simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    split_ifs <;> dsimp only [stAt] at ih <;> omega
   ·have htake:(dF m).take (t+1)=(dF m).take t:=by
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]
    simp only [stAt,htake];dsimp only [stAt] at ih;omega
 let Acc (t:ℕ) (_:t ≤ m) (c3:CB nIn):Type:=
  Q9 nIn c3 W (fun x=>(stAt t x).1) × Q2 nIn c3 m (fun x=>(stAt t x).2.1) ×
  Q2 nIn c3 B (fun x=>(stAt t x).2.2)
 let h02:=h0.trans (h1.trans h2)
 have hinit:Acc 0 (Nat.zero_le m) c2:=
  ⟨(v0.lift (h1.trans h2)).cast (fun _=>rfl),(v.lift h02).cast (fun _ _=>rfl),vzb.cast (fun _ _=>rfl)⟩
 (Q0.qe (Bstep:=2+8*m+15*W+B*(6+7*W)) m Acc c2 hinit fun t ht c3 h3 ⟨cnt,cur,out⟩=>
  Q0.weaken (by omega)<|
  let ct:Fin m:=⟨t,ht⟩
  let h03:=h02.trans h3
  let isPiv:=((T.rows ct).at ct).lift h03
  let bval:=cur.at ct
  (vg c3 isPiv bval).bind fun c4 h4 vdo=>
  (j3 c4 (cur.lift h4) ((T.rows ct).lift (h03.trans h4))).bind fun c5 h5 vxor=>
  (vd c5 (vdo.lift h5) vxor (cur.lift (h4.trans h5))).bind fun c6 h6 cur'=>
  have hsum:∀ x,(stAt t x).1+1 < 2^W:=fun x=>by have:=hst_le t x;omega
  let h36:=h4.trans (h5.trans h6)
  (z4 c6 (cnt.lift h36) (v1.lift (h2.trans (h3.trans h36))) hsum).bind fun c7 h7 cnt1=>
  (vH c7 (isPiv.lift (h36.trans h7)) cnt1 (cnt.lift (h36.trans h7))).bind fun c8 h8 cnt'=>
  let h38:=h36.trans (h7.trans h8)
  (j8 (Bstep:=6+7*W) B (fun x j=>
    if fT x ct ct=true then (if j.val=(stAt t x).1 then (stAt t x).2.1 ct else (stAt t x).2.2 j)
    else (stAt t x).2.2 j) c8 fun j c9 h9=>
   Q0.weaken (by omega)<|
   let h39:=h38.trans h9
   (qS c9 W j.val (lt_trans j.isLt hBW)).bind fun c10 h10 cj=>
   (zH c10 (cnt.lift (h39.trans h10)) cj).bind fun c11 h11 veq=>
   (vg c11 (isPiv.lift (h39.trans (h10.trans h11))) veq).bind fun c12 h12 vupd=>
   let h9_12:=h10.trans (h11.trans h12)
   (ds c12 vupd (bval.lift (h39.trans h9_12)) ((out.at j).lift (h39.trans h9_12))).bind fun _ _ vm=>
   Q0.pure<|vm.cast fun x=>by
    by_cases h1':fT x ct ct=true <;> by_cases h2':(stAt t x).1=j.val
    ·simp [h1',h2']
    ·simp [h1',h2',Ne.symm h2']
    ·simp [h1',h2']
    ·simp [h1',h2']).bind fun _ h9 out'=>
  have htake:(dF m).take (t+1)=(dF m).take t ++ [ct]:=by
   rw [dJ (by simp;omega)];simp [ct]
  have hstep:∀ x,stAt (t+1) x =
    (if fT x ct ct=true then
     let b:=(stAt t x).2.1 ct
     ((stAt t x).1+1,if b=true then q5 (stAt t x).2.1 (fT x ct) else (stAt t x).2.1,
      fun j=>if j.val=(stAt t x).1 then b else (stAt t x).2.2 j)
    else stAt t x):=fun x=>by
   change ((dF m).take (t+1)).foldl _ _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨(cnt'.lift h9).cast fun x=>by rw [hstep x];by_cases h:fT x ct ct=true <;> simp [h],
   (cur'.lift (h7.trans (h8.trans h9))).cast fun x q=>by
     rw [hstep x];by_cases h1':fT x ct ct=true <;> by_cases h2':(stAt t x).2.1 ct=true <;> simp [h1',h2',q5],
   out'.cast fun x j=>by rw [hstep x];by_cases h:fT x ct ct=true <;> simp [h]⟩).bind fun _ _ ⟨_,_,outF⟩=>
 Q0.pure<|outF.cast fun x j=>by
  simp only [stAt,qf,show (dF m).take m=dF m by simp]
def gc {nIn m B:ℕ} (c:CB nIn)
  {fT:(Fin nIn->Bool)->Q6 m} {fx:(Fin nIn->Bool)->Q1 B}
  (rows:∀ t:Fin B,Q2 nIn c m (fun x=>qc (fT x) B t))
  (vx:Q2 nIn c B fx) :
  Q0 nIn c (m+B*(8*m))
   (fun c'=>Q2 nIn c' m (fun x=>q1 (fT x) (fx x))):=
 Q0.weaken (by omega)<|
 (vq c m (q2 m)).bind fun c0 h0 vz=>
 let stAt (t:ℕ) (x:Fin nIn->Bool):Q1 m:=
  ((dF B).take t).foldl (fun acc j=>
   if fx x j=true then q5 acc (qc (fT x) B j) else acc) (q2 m)
 let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=Q2 nIn c1 m (stAt t)
 have hinit:Acc 0 (Nat.zero_le B) c0:=vz.cast (fun _ _=>rfl)
 (Q0.qe (Bstep:=8*m) B Acc c0 hinit fun t ht c1 h1 acc=>
  Q0.weaken (by omega)<|
  let jt:Fin B:=⟨t,ht⟩
  let h01:=h0.trans h1
  (j3 c1 acc ((rows jt).lift h01)).bind fun c2 h2 vxor=>
  (vd c2 ((vx.at jt).lift (h01.trans h2)) vxor (acc.lift h2)).bind fun _ _ vnew=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [jt]:=by
   rw [dJ (by simp;omega)];simp [jt]
  Q0.pure<|vnew.cast fun x q=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   by_cases h:fx x jt=true <;> simp [h,q5]).bind fun _ _ vF=>
 Q0.pure<|vF.cast fun x q=>by
  simp only [stAt,q1,show (dF B).take B=dF B by simp]
def QF (m B W:ℕ):ℕ:=
 QH m B W+2*W+2*B*B +
 B*(Qk m B W+2+25*B*B+7*B+15*W+B*(2+7*W+4*B)) +
 B*(2+33*B*B+9*B+15*W+B*(2+7*W+4*B))
def zn {nIn m B W:ℕ} (c:CB nIn)
  (hW:1 ≤ W) (hmW:m < 2^W) (h2BW:2*B < 2^W)
  {fU fM:(Fin nIn->Bool)->Q6 m}
  (T_U:Q8 nIn c m fU) (T_M:Q8 nIn c m fM) :
  Q0 nIn c (QF m B W)
   (fun c'=>Qv nIn c' B (fun x=>qk (fU x) (fM x) B)):=
 have hBW:B < 2^W:=by have:=Nat.two_pow_pos W;omega
 Q0.weaken (by unfold QF;nlinarith)<|
 (zB c hW hmW hBW T_U).bind fun c0 h0 rowsU=>
 (qS c0 W 0 (Nat.two_pow_pos W)).bind fun c1 h1 v0=>
 (qS c1 W 1 (Nat.one_lt_two_pow (by omega))).bind fun c2 h2 v1=>
 (y0 c2 B).bind fun c3 h3 zT=>
 (gS c3 B (fun _ _=>false)).bind fun c4 h4 zM=>
 let h04:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
 let h24:=h3.trans h4
 let step1 (x:Fin nIn->Bool) (st:ℕ × Q6 B × (Fin B->Q1 B)) (j:Fin B):=
  let col:=qf (fM x) (qc (fU x) B j) B
  if qK col=true then
   (st.1+1,qC st.2.1 col,fun col'=>if col'.val=st.1 then col else st.2.2 col')
  else st
 let st1At (t:ℕ) (x:Fin nIn->Bool):=
  ((dF B).take t).foldl (step1 x) (0,qN B,fun _=>q2 B)
 have hst1_le:∀ t x,(st1At t x).1 ≤ t:=by
  intro t x;induction t with
  | zero=>simp [st1At]
  | succ t ih=>
   by_cases ht:t < B
   ·have htake:(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
     rw [dJ (by simp;omega)];simp
    have hstep:st1At (t+1) x=step1 x (st1At t x) ⟨t,ht⟩:=by
     change ((dF B).take (t+1)).foldl (step1 x) _=_
     rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [hstep];dsimp only [step1];split_ifs <;> omega
   ·have htake:(dF B).take (t+1)=(dF B).take t:=by
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]
    simp only [st1At,htake];dsimp only [st1At] at ih;omega
 let Acc1 (t:ℕ) (_:t ≤ B) (c5:CB nIn):Type:=
  Q9 nIn c5 W (fun x=>(st1At t x).1) × Q8 nIn c5 B (fun x=>(st1At t x).2.1) ×
  (∀ col:Fin B,Q2 nIn c5 B (fun x=>(st1At t x).2.2 col))
 have hinit1:Acc1 0 (Nat.zero_le B) c4:=
  ⟨(v0.lift (h2.trans h24)).cast (fun _=>rfl),(zT.lift h4).cast (fun _=>rfl),
  fun col=>(zM.cols col).cast (fun _ _=>rfl)⟩
 let BStep1:=Qk m B W+2+25*B*B+7*B+15*W+B*(2+7*W+4*B)
 (Q0.qe (Bstep:=BStep1) B Acc1 c4 hinit1 fun t ht c5 h5 ⟨cnt,Tcols,cols⟩=>
  Q0.weaken (by dsimp only [BStep1];nlinarith)<|
  let jt:Fin B:=⟨t,ht⟩
  let h05:=h04.trans h5
  (yS c5 hW hmW hBW (T_M.lift h05) ((rowsU jt).lift (h1.trans (h2.trans (h24.trans h5))))).bind fun c6 h6 vcol=>
  (zg c6 vcol).bind fun c7 h7 vnz0=>
  let vnz:=vnz0.cast fun x=>(qv _).symm
  let h57:=h6.trans h7
  (jD c7 (Tcols.lift h57) (vcol.lift h7)).bind fun c8 h8 Tins=>
  (gd c8 (vnz.lift h8) Tins (Tcols.lift (h57.trans h8))).bind fun c9 h9 Tcols'=>
  have hsum:∀ x,(st1At t x).1+1 < 2^W:=fun x=>by have:=hst1_le t x;omega
  let h59:=h57.trans (h8.trans h9)
  (z4 c9 (cnt.lift h59) (v1.lift (h24.trans (h5.trans h59))) hsum).bind fun c10 h10 cnt1=>
  (vH c10 (vnz.lift (h8.trans (h9.trans h10))) cnt1 (cnt.lift (h59.trans h10))).bind fun c11 h11 cnt'=>
  let h5_11:=h59.trans (h10.trans h11)
  let CAcc (s:ℕ) (_:s ≤ B) (c12:CB nIn):Type:=
   ∀ col:Fin B,col.val < s->Q2 nIn c12 B (fun x=>
    if qK (qf (fM x) (qc (fU x) B jt) B)=true then
     (if col.val=(st1At t x).1 then qf (fM x) (qc (fU x) B jt) B else (st1At t x).2.2 col)
    else (st1At t x).2.2 col)
  have hCinit:CAcc 0 (Nat.zero_le B) c11:=fun _ h=>absurd h (by omega)
  (Q0.qe (Bstep:=2+7*W+4*B) B CAcc c11 hCinit fun s hs c12 h12 cacc=>
   Q0.weaken (by omega)<|
   let cs:Fin B:=⟨s,hs⟩
   let h5_12:=h5_11.trans h12
   (qS c12 W s (lt_trans hs hBW)).bind fun c13 h13 vsc=>
   (zH c13 (cnt.lift (h5_12.trans h13)) vsc).bind fun c14 h14 veq=>
   (vg c14 (vnz.lift (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans (h13.trans h14))))))) veq).bind fun c15 h15 vupd=>
   let h12_15:=h13.trans (h14.trans h15)
   (vd c15 vupd (vcol.lift (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans h12_15)))))))
    ((cols cs).lift (h5_12.trans h12_15))).bind fun _ h16 vnew=>
   Q0.pure fun col hcol=>
    if hlt:col.val < s then (cacc col hlt).lift (h12_15.trans h16)
    else
     have heq:col=cs:=Fin.ext (by dsimp [cs];omega)
     heq▸vnew.cast fun x r=>by
      by_cases h1':qK (qf (fM x) (qc (fU x) B jt) B)=true <;>
       by_cases h2':(st1At t x).1=s
      ·simp [cs,h1',h2']
      ·simp [cs,h1',h2',Ne.symm h2']
      ·simp [cs,h1',h2']
      ·simp [cs,h1',h2']).bind fun _ h12 cols'=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [jt]:=by
   rw [dJ (by simp;omega)];simp [jt]
  have hstep:∀ x,st1At (t+1) x=step1 x (st1At t x) jt:=fun x=>by
   change ((dF B).take (t+1)).foldl (step1 x) _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨(cnt'.lift h12).cast fun x=>by
     rw [hstep x];dsimp only [step1]
     by_cases h:qK (qf (fM x) (qc (fU x) B jt) B)=true <;> simp [h],
   (Tcols'.lift (h10.trans (h11.trans h12))).cast fun x=>by
     rw [hstep x];dsimp only [step1]
     by_cases h:qK (qf (fM x) (qc (fU x) B jt) B)=true <;> simp [h],
   fun col=>(cols' col col.isLt).cast fun x r=>by
     rw [hstep x];dsimp only [step1]
     by_cases h:qK (qf (fM x) (qc (fU x) B jt) B)=true <;> simp [h]⟩).bind fun c5 h5 ⟨cnt1,Tcols1,cols1⟩=>
 let step2 (st:ℕ × Q6 B × (Fin B->Q1 B)) (r:Fin B):=
  let er:Q1 B:=fun i=>decide (i=r)
  if qK (q8 st.2.1 er)=true then
   (st.1+1,qC st.2.1 er,fun col'=>if col'.val=st.1 then er else st.2.2 col')
  else st
 let st2At (t:ℕ) (x:Fin nIn->Bool):=
  ((dF B).take t).foldl step2 (st1At B x)
 have hst2_le:∀ t x,(st2At t x).1 ≤ B+t:=by
  intro t x;induction t with
  | zero=>simp [st2At];exact hst1_le B x
  | succ t ih=>
   by_cases ht:t < B
   ·have htake:(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
     rw [dJ (by simp;omega)];simp
    have hstep:st2At (t+1) x=step2 (st2At t x) ⟨t,ht⟩:=by
     change ((dF B).take (t+1)).foldl step2 _=_
     rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [hstep];dsimp only [step2];split_ifs <;> omega
   ·have htake:(dF B).take (t+1)=(dF B).take t:=by
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]
    simp only [st2At,htake];dsimp only [st2At] at ih;omega
 let Acc2 (t:ℕ) (_:t ≤ B) (c6:CB nIn):Type:=
  Q9 nIn c6 W (fun x=>(st2At t x).1) × Q8 nIn c6 B (fun x=>(st2At t x).2.1) ×
  (∀ col:Fin B,Q2 nIn c6 B (fun x=>(st2At t x).2.2 col))
 have hinit2:Acc2 0 (Nat.zero_le B) c5:=
  ⟨cnt1.cast (fun _=>rfl),Tcols1.cast (fun _=>rfl),fun col=>(cols1 col).cast (fun _ _=>rfl)⟩
 let BStep2:=2+33*B*B+9*B+15*W+B*(2+7*W+4*B)
 (Q0.qe (Bstep:=BStep2) B Acc2 c5 hinit2 fun t ht c6 h6 ⟨cnt,Tcols,cols⟩=>
  Q0.weaken (by dsimp only [BStep2];nlinarith)<|
  let rt:Fin B:=⟨t,ht⟩
  let er:Q1 B:=fun i=>decide (i=rt)
  (vq c6 B er).bind fun c7 h7 ver=>
  (yR c7 (Tcols.lift h7) ver).bind fun c8 h8 vred=>
  (zg c8 vred).bind fun c9 h9 vnz0=>
  let vnz:=vnz0.cast fun x=>(qv _).symm
  let h69:=h7.trans (h8.trans h9)
  (jD c9 (Tcols.lift h69) (ver.lift (h8.trans h9))).bind fun c10 h10 Tins=>
  (gd c10 (vnz.lift h10) Tins (Tcols.lift (h69.trans h10))).bind fun c11 h11 Tcols'=>
  have hsum:∀ x,(st2At t x).1+1 < 2^W:=fun x=>by have:=hst2_le t x;omega
  let h6_11:=h69.trans (h10.trans h11)
  (z4 c11 (cnt.lift h6_11) (v1.lift (h24.trans (h5.trans (h6.trans h6_11)))) hsum).bind fun c12 h12 cnt1'=>
  (vH c12 (vnz.lift (h10.trans (h11.trans h12))) cnt1' (cnt.lift (h6_11.trans h12))).bind fun c13 h13 cnt'=>
  let h6_13:=h6_11.trans (h12.trans h13)
  let CAcc (s:ℕ) (_:s ≤ B) (c14:CB nIn):Type:=
   ∀ col:Fin B,col.val < s->Q2 nIn c14 B (fun x=>
    if qK (q8 (st2At t x).2.1 er)=true then
     (if col.val=(st2At t x).1 then er else (st2At t x).2.2 col)
    else (st2At t x).2.2 col)
  have hCinit:CAcc 0 (Nat.zero_le B) c13:=fun _ h=>absurd h (by omega)
  (Q0.qe (Bstep:=2+7*W+4*B) B CAcc c13 hCinit fun s hs c14 h14 cacc=>
   Q0.weaken (by omega)<|
   let cs:Fin B:=⟨s,hs⟩
   let h6_14:=h6_13.trans h14
   (qS c14 W s (lt_trans hs hBW)).bind fun c15 h15 vsc=>
   (zH c15 (cnt.lift (h6_14.trans h15)) vsc).bind fun c16 h16 veq=>
   (vg c16 (vnz.lift (h10.trans (h11.trans (h12.trans (h13.trans (h14.trans (h15.trans h16))))))) veq).bind fun c17 h17 vupd=>
   let h14_17:=h15.trans (h16.trans h17)
   (vd c17 vupd (ver.lift (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans (h13.trans (h14.trans h14_17))))))))
    ((cols cs).lift (h6_14.trans h14_17))).bind fun _ h18 vnew=>
   Q0.pure fun col hcol=>
    if hlt:col.val < s then (cacc col hlt).lift (h14_17.trans h18)
    else
     have heq:col=cs:=Fin.ext (by dsimp [cs];omega)
     heq▸vnew.cast fun x r=>by
      by_cases h1':qK (q8 (st2At t x).2.1 er)=true <;>
       by_cases h2':(st2At t x).1=s
      ·simp [cs,h1',h2']
      ·simp [cs,h1',h2',Ne.symm h2']
      ·simp [cs,h1',h2']
      ·simp [cs,h1',h2']).bind fun _ h14 cols'=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [rt]:=by
   rw [dJ (by simp;omega)];simp [rt]
  have hstep:∀ x,st2At (t+1) x=step2 (st2At t x) rt:=fun x=>by
   change ((dF B).take (t+1)).foldl step2 _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨(cnt'.lift h14).cast fun x=>by
     rw [hstep x];dsimp only [step2]
     by_cases h:qK (q8 (st2At t x).2.1 er)=true <;> simp [er,h],
   (Tcols'.lift (h12.trans (h13.trans h14))).cast fun x=>by
     rw [hstep x];dsimp only [step2]
     by_cases h:qK (q8 (st2At t x).2.1 er)=true <;> simp [er,h],
   fun col=>(cols' col col.isLt).cast fun x r=>by
     rw [hstep x];dsimp only [step2]
     by_cases h:qK (q8 (st2At t x).2.1 er)=true <;> simp [er,h]⟩).bind fun _ _ ⟨_,_,colsF⟩=>
 Q0.pure ⟨fun col=>(colsF col).cast fun x r=>by
  simp only [st2At,st1At,qk,step1,step2,show (dF B).take B=dF B by simp]⟩
def QK (B BSwap BAdd:ℕ):ℕ:=
 B*(B*(2+2*B)+B*(8*B+BSwap)+B*(1+8*B+BAdd))
def gQ {nIn B:ℕ} {α:Type}
  (S:CB nIn->((Fin nIn->Bool)->α)->Type)
  (liftS:∀ {c₁ c₂ f},c₁.Qa c₂->S c₁ f->S c₂ f)
  (castS:∀ {c f g},(∀ x,f x=g x)->S c f->S c g)
  (onSwap:Fin B->Fin B->α->α) (onAdd:Fin B->Fin B->α->α)
  (BSwap BAdd:ℕ)
  (mkCondSwap:∀ (c:CB nIn) {fa:(Fin nIn->Bool)->α} {fp:(Fin nIn->Bool)->Bool}
   (u v:Fin B),Q4 nIn c fp->S c fa ->
   Q0 nIn c BSwap (fun c'=>S c' (fun x=>if fp x=true then onSwap u v (fa x) else fa x)))
  (mkCondAdd:∀ (c:CB nIn) {fa:(Fin nIn->Bool)->α} {fp:(Fin nIn->Bool)->Bool}
   (src dst:Fin B),Q4 nIn c fp->S c fa ->
   Q0 nIn c BAdd (fun c'=>S c' (fun x=>if fp x=true then onAdd src dst (fa x) else fa x)))
  (c:CB nIn) {fG:(Fin nIn->Bool)->Qd B} {finit:(Fin nIn->Bool)->α}
  (G:Qv nIn c B fG) (init:S c finit) :
  Q0 nIn c (QK B BSwap BAdd)
   (fun c'=>Qv nIn c' B (fun x=>(yt onSwap onAdd (fG x) (finit x)).1) ×
        S c' (fun x=>(yt onSwap onAdd (fG x) (finit x)).2)):=
 let stAt (t:ℕ) (x:Fin nIn->Bool):Qd B × α:=
  ((dF B).take t).foldl (fun st row=>z5 onSwap onAdd row st) (fG x,finit x)
 let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=
  Qv nIn c1 B (fun x=>(stAt t x).1) × S c1 (fun x=>(stAt t x).2)
 have hinit:Acc 0 (Nat.zero_le B) c:=⟨G.cast (fun _ _ _=>rfl),castS (fun _=>rfl) init⟩
 Q0.weaken (by unfold QK;omega)<|
 (Q0.qe (Bstep:=B*(2+2*B)+B*(8*B+BSwap)+B*(1+8*B+BAdd)) B Acc c hinit fun t ht c1 _ ⟨Mc,ac⟩=>
  Q0.weaken (by omega)<|
  let row:Fin B:=⟨t,ht⟩
  let isPivFn (x:Fin nIn->Bool) (col:Fin B):Bool:=
   decide (row.val ≤ col.val/\(stAt t x).1 row col=true /\
    ∀ c':Fin B,row.val ≤ c'.val->c'.val < col.val->(stAt t x).1 row c'=false)
  (j8 (Bstep:=2+2*B) B isPivFn c1 fun col c2 h2=>
   Q0.weaken (by omega)<|
   (vJ c2 (decide (row.val ≤ col.val))).bind fun c3 h3 vge=>
   (vg c3 vge ((Mc.at row col).lift (h2.trans h3))).bind fun c4 h4 vbase=>
   let PAcc (s:ℕ) (_:s ≤ B) (c5:CB nIn):Type:=
    Q4 nIn c5 (fun x=>decide (row.val ≤ col.val/\(stAt t x).1 row col=true /\
     ∀ c':Fin B,c'.val < s->row.val ≤ c'.val->c'.val < col.val->(stAt t x).1 row c'=false))
   have hPinit:PAcc 0 (Nat.zero_le B) c4:=vbase.cast fun x=>by
    apply Bool.eq_iff_iff.mpr;simp only [dI,dG]
    exact ⟨fun ⟨h1',h2'⟩=>⟨h1',h2',fun _ h=>absurd h (by omega)⟩,fun ⟨h1',h2',_⟩=>⟨h1',h2'⟩⟩
   (Q0.qe (Bstep:=2) B PAcc c4 hPinit fun s hs c5 h5 pacc=>
    let cs:Fin B:=⟨s,hs⟩
    if hcond:row.val ≤ s/\s < col.val then
     (y2 c5 ((Mc.at row cs).lift (h2.trans (h3.trans (h4.trans h5))))).bind fun c6 h6 vnot=>
     (vg c6 (pacc.lift h6) vnot).bind fun _ _ vand=>
     Q0.pure<|vand.cast fun x=>by
      apply Bool.eq_iff_iff.mpr
      simp only [dI,Bool.not_eq_true',dG]
      constructor
      ·rintro ⟨⟨h1',h2',h3'⟩,hnf⟩
       refine ⟨h1',h2',fun c' hc' hr' hlt'=>?_⟩
       by_cases hls:c'.val < s
       ·exact h3' c' hls hr' hlt'
       ·have heq:c'=cs:=Fin.ext (by dsimp [cs];omega)
        rw [heq];exact hnf
      ·rintro ⟨h1',h2',h3'⟩
       exact ⟨⟨h1',h2',fun c' hc' hr' hlt'=>h3' c' (by omega) hr' hlt'⟩,
        h3' cs (by dsimp [cs];omega) hcond.1 hcond.2⟩
    else
     Q0.weaken (by omega)<|
     Q0.pure<|pacc.cast fun x=>by
      apply Bool.eq_iff_iff.mpr;simp only [dG]
      constructor
      ·rintro ⟨h1',h2',h3'⟩
       refine ⟨h1',h2',fun c' hc' hr' hlt'=>?_⟩
       by_cases hls:c'.val < s
       ·exact h3' c' hls hr' hlt'
       ·have:c'.val=s:=by omega
        exact absurd ⟨by omega,by omega⟩ hcond
      ·rintro ⟨h1',h2',h3'⟩
       exact ⟨h1',h2',fun c' hc' hr' hlt'=>h3' c' (by omega) hr' hlt'⟩).bind fun _ _ pF=>
   Q0.pure<|pF.cast fun x=>by
    apply Bool.eq_iff_iff.mpr;simp only [isPivFn,dG]
    exact ⟨fun ⟨h1',h2',h3'⟩=>⟨h1',h2',fun c' hr' hlt'=>h3' c' c'.isLt hr' hlt'⟩,
       fun ⟨h1',h2',h3'⟩=>⟨h1',h2',fun c' _ hr' hlt'=>h3' c' hr' hlt'⟩⟩).bind fun c2 h2 visPiv=>
  let s1At (s:ℕ) (x:Fin nIn->Bool):Qd B × α:=
   ((dF B).take s).foldl
    (fun st col=>if isPivFn x col=true then (qJ st.1 row col,onSwap row col st.2) else st)
    (stAt t x)
  let S1Acc (s:ℕ) (_:s ≤ B) (c3:CB nIn):Type:=
   Qv nIn c3 B (fun x=>(s1At s x).1) × S c3 (fun x=>(s1At s x).2)
  have hS1init:S1Acc 0 (Nat.zero_le B) c2:=
   ⟨(Mc.lift h2).cast (fun _ _ _=>rfl),castS (fun _=>rfl) (liftS h2 ac)⟩
  (Q0.qe (Bstep:=8*B+BSwap) B S1Acc c2 hS1init fun s hs c3 h3 ⟨M1,a1⟩=>
   Q0.weaken (by omega)<|
   let cs:Fin B:=⟨s,hs⟩
   let vp:=(visPiv.at cs).lift h3
   (zL c3 row cs vp M1).bind fun c4 h4 M1'=>
   (mkCondSwap c4 row cs (vp.lift h4) (liftS h4 a1)).bind fun _ h5 a1'=>
   have htake:(dF B).take (s+1)=(dF B).take s ++ [cs]:=by
    rw [dJ (by simp;omega)];simp [cs]
   Q0.pure
    ⟨(M1'.lift h5).cast fun x r col=>by
      simp only [s1At,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
      by_cases h:isPivFn x cs=true <;> simp [h],
    castS (fun x=>by
      simp only [s1At,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
      by_cases h:isPivFn x cs=true <;> simp [h]) a1'⟩).bind fun c3 _ ⟨Ms1,as1⟩=>
  let s2At (s:ℕ) (x:Fin nIn->Bool):Qd B × α:=
   ((dF B).take s).foldl
    (fun st col=>if col ≠ row/\st.1 row col=true then (vD st.1 row col,onAdd row col st.2) else st)
    (s1At B x)
  let S2Acc (s:ℕ) (_:s ≤ B) (c4:CB nIn):Type:=
   Qv nIn c4 B (fun x=>(s2At s x).1) × S c4 (fun x=>(s2At s x).2)
  have hS2init:S2Acc 0 (Nat.zero_le B) c3:=⟨Ms1.cast (fun _ _ _=>rfl),castS (fun _=>rfl) as1⟩
  (Q0.qe (Bstep:=1+8*B+BAdd) B S2Acc c3 hS2init fun s hs c4 _ ⟨M2,a2⟩=>
   let cs:Fin B:=⟨s,hs⟩
   have htake:(dF B).take (s+1)=(dF B).take s ++ [cs]:=by
    rw [dJ (by simp;omega)];simp [cs]
   have hstep2:∀ x,s2At (s+1) x =
     (if cs ≠ row/\(s2At s x).1 row cs=true then (vD (s2At s x).1 row cs,onAdd row cs (s2At s x).2)
     else s2At s x):=fun x=>by
    change ((dF B).take (s+1)).foldl _ _=_
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   if hne:cs ≠ row then
    Q0.weaken (by omega)<|
    let vc:=M2.at row cs
    (g6 c4 row cs vc M2).bind fun c5 h5 M2'=>
    (mkCondAdd c5 row cs (vc.lift h5) (liftS h5 a2)).bind fun _ h6 a2'=>
    Q0.pure
     ⟨(M2'.lift h6).cast fun x r col=>by
       rw [hstep2 x];by_cases h:(s2At s x).1 row cs=true <;> simp [hne,h],
     castS (fun x=>by
       rw [hstep2 x];by_cases h:(s2At s x).1 row cs=true <;> simp [hne,h]) a2'⟩
   else
    Q0.weaken (by omega)<|
    Q0.pure
     ⟨M2.cast fun x r col=>by rw [hstep2 x];simp [hne],
     castS (fun x=>by rw [hstep2 x];simp [hne]) a2⟩).bind fun _ _ ⟨Ms2,as2⟩=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [row]:=by
   rw [dJ (by simp;omega)];simp [row]
  have hstep:∀ x,stAt (t+1) x=s2At B x:=fun x=>by
   change ((dF B).take (t+1)).foldl _ _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   have hBtake:(dF B).take B=dF B:=by simp
   simp only [z5,s2At,s1At,isPivFn,hBtake]
   rfl
  Q0.pure
   ⟨Ms2.cast fun x r col=>by rw [hstep x],
   castS (fun x=>by rw [hstep x]) as2⟩).bind fun _ _ ⟨MF,aF⟩=>
 Q0.pure
  ⟨MF.cast fun x r col=>by
    simp only [stAt,yt,show (dF B).take B=dF B by simp],
  castS (fun x=>by
    simp only [stAt,yt,show (dF B).take B=dF B by simp]) aF⟩
def QE (B:ℕ):ℕ:=
 B*B+QK B (8*B) (8*B)
def dC {nIn B:ℕ} (c:CB nIn)
  {fG:(Fin nIn->Bool)->Qd B} (G:Qv nIn c B fG) :
  Q0 nIn c (QE B) (fun c'=>Qv nIn c' B (fun x=>j1 (fG x))):=
 Q0.weaken (by unfold QE;omega)<|
 (gS c B (vT B)).bind fun c0 h0 idM=>
 (gQ (fun c f=>Qv nIn c B f) (fun h M=>M.lift h) (fun h M=>M.cast fun x r col=>congrFun (congrFun (h x) r) col)
  (fun u v M=>qJ M u v) (fun src dst M=>vD M src dst) (8*B) (8*B)
  (fun c _ _ u v cond M=>zL c u v cond M)
  (fun c _ _ src dst cond M=>g6 c src dst cond M)
  c0 (G.lift h0) idM).bind fun _ _ ⟨_,res⟩=>
 Q0.pure<|res.cast fun _ _ _=>rfl
def QC (B W:ℕ):ℕ:=
 QK B (2^B*(4*W)) (2^B*(4*W))
def de {nIn B W:ℕ} (c:CB nIn)
  {fG:(Fin nIn->Bool)->Qd B} {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (G:Qv nIn c B fG) (D:SDP nIn c B W fD) :
  Q0 nIn c (QC B W) (fun c'=>SDP nIn c' B W (fun x=>jZ (fG x) (fD x))):=
 Q0.weaken (by unfold QC;omega)<|
 (gQ (fun c f=>SDP nIn c B W f) (fun h D=>D.lift h) (fun h D=>D.cast fun x idx=>congrFun (h x) idx)
  (fun u v tbl idx=>tbl (vY idx u v)) (fun src dst tbl idx=>tbl (zQ idx dst src))
  (2^B*(4*W)) (2^B*(4*W))
  (fun c _ _ u v cond D=>Q0.weaken (by omega)<|(g5 c u v cond D).bind fun _ _ r=>
   Q0.pure<|r.cast fun x idx=>by split_ifs <;> rfl)
  (fun c _ _ src dst cond D=>Q0.weaken (by omega)<|(dl c src dst cond D).bind fun _ _ r=>
   Q0.pure<|r.cast fun x idx=>by split_ifs <;> rfl)
  c G D).bind fun _ _ ⟨_,res⟩=>
 Q0.pure<|res.cast fun _ _=>rfl
end StaticGLCircuit
section SelectMath
def jM (k r:ℕ) (col:Bool) (w name:ℕ) (c:Fin r->Fin (2^k)) (p:Fin k):Bool:=
 (vI k r col w name c).testBit ((p.val+vo r col) % k)
def qR (k r m:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (w:ℕ) (p:Fin k):Q1 m:=
 q5
  (if qK (Ab p)&&jM k r false w nr cr p then Ab p else q2 m)
  (if qK (Bb p)&&jM k r true w nc cc p then Bb p else q2 m)
def v4 (k r m:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (w:ℕ):Q1 m:=
 (dF k).foldl (fun acc p=>q5 acc (qR k r m Ab Bb nr nc cr cc w p)) (q2 m)
def v5 (k r m:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (i:ℕ) (w:ℕ):Q1 m:=
 ((dF k).take i).foldl (fun acc t=>q5 acc (qR k r m Ab Bb nr nc cr cc w (o t))) (q2 m)
lemma jx {k r m:ℕ} (hk:0 < k) (hr:4 ≤ r)
  (Ab Bb:Fin k->Q1 m) {nr nc:ℕ} (hnr:nr < 2^k) (hnc:nc < 2^k)
  (cr cc:Fin r->Fin (2^k)) (p:Fin k)
  {w1 w2:ℕ} (hw1:w1 < 2^k) (hw2:w2 < 2^k)
  (hag:∀ z∈qq r Ab Bb p,w1.testBit z.val=w2.testBit z.val) :
  qR k r m Ab Bb nr nc cr cc w1 p=qR k r m Ab Bb nr nc cr cc w2 p:=by
 unfold qR
 congr 1
 ·by_cases hA:qK (Ab p)=true
  ·have htb:jM k r false w1 nr cr p=jM k r false w2 nr cr p:=by
    unfold jM
    refine yQ hk hr false hw1 hw2 hnr cr p fun t=>?_
    have hmem:(⟨(p.val+t.val) % k,Nat.mod_lt _ hk⟩:Fin k)∈qq r Ab Bb p:=by
     apply Finset.mem_union_left
     simp only [d3,dK,dL,true_and,y4,dG]
     exact ⟨hA,t,rfl⟩
    exact hag _ hmem
   simp [hA,htb]
  ·simp [hA]
 ·by_cases hB:qK (Bb p)=true
  ·have htb:jM k r true w1 nc cc p=jM k r true w2 nc cc p:=by
    unfold jM
    refine yQ hk hr true hw1 hw2 hnc cc p fun t=>?_
    have hmem:(⟨(p.val+t.val) % k,Nat.mod_lt _ hk⟩:Fin k)∈qq r Ab Bb p:=by
     apply Finset.mem_union_right
     simp only [d3,dK,dL,true_and,y4,dG]
     exact ⟨hB,t,rfl⟩
    exact hag _ hmem
   simp [hB,htb]
  ·simp [hB]
lemma zY {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (w:ℕ) (p:Fin k) :
  q4 (qR k r m Ab Bb nr nc cr cc w p) ∈
   Submodule.span (ZMod 2) ({q4 (Ab p),q4 (Bb p)}:Set (Fin m->ZMod 2)):=by
 unfold qR
 rw [qE]
 refine Submodule.add_mem _ ?_ ?_
 ·split_ifs
  ·exact Submodule.subset_span (by simp)
  ·rw [qh];exact Submodule.zero_mem _
 ·split_ifs
  ·exact Submodule.subset_span (by simp)
  ·rw [qh];exact Submodule.zero_mem _
lemma yN {k m:ℕ} (f:Fin k->Q1 m) :
  ∀ t ≤ k,q4 (((dF k).take t).foldl (fun acc p=>q5 acc (f p)) (q2 m)) =
   ∑ p∈Finset.univ.filter (fun p:Fin k=>p.val < t),q4 (f p):=by
 intro t
 induction t with
 | zero=>intro _;simp [qh]
 | succ t ih=>
  intro ht
  have htake:(dF k).take (t+1)=(dF k).take t ++ [⟨t,ht⟩]:=by
   rw [dJ (by simp;omega)];simp
  rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,qE,ih (Nat.le_of_succ_le ht)]
  have hnot:(⟨t,ht⟩:Fin k)∉Finset.univ.filter (fun p:Fin k=>p.val < t):=by simp
  have hins:Finset.univ.filter (fun p:Fin k=>p.val < t+1) =
    insert ⟨t,ht⟩ (Finset.univ.filter (fun p:Fin k=>p.val < t)):=by
   ext p;simp only [dK,dL,true_and,Finset.mem_insert]
   constructor
   ·intro hp;by_cases hlt:p.val < t
    ·right;exact hlt
    ·left;exact Fin.ext (by dsimp;omega)
   ·rintro (rfl | hp)
    ·dsimp;omega
    ·omega
  rw [hins,Finset.sum_insert hnot,add_comm]
lemma z8 {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (w:ℕ) :
  q4 (v4 k r m Ab Bb nr nc cr cc w) =
   ∑ p:Fin k,q4 (qR k r m Ab Bb nr nc cr cc w p):=by
 have h:=yN (qR k r m Ab Bb nr nc cr cc w) k le_rfl
 rw [show (dF k).take k=dF k by simp] at h
 have hf:Finset.univ.filter (fun p:Fin k=>p.val < k)=Finset.univ:=by ext p;simp
 rw [hf] at h;exact h
lemma vW {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (w:ℕ) {i:ℕ} (hi:i ≤ k) :
  q4 (v5 k r m Ab Bb nr nc cr cc o i w) =
   ∑ t∈Finset.univ.filter (fun t:Fin k=>t.val < i),q4 (qR k r m Ab Bb nr nc cr cc w (o t)):=
 yN (fun t=>qR k r m Ab Bb nr nc cr cc w (o t)) i hi
lemma gw {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (w:ℕ) :
  v5 k r m Ab Bb nr nc cr cc o 0 w=q2 m:=rfl
lemma zm {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (w:ℕ) {i:ℕ} (hi:i < k) :
  v5 k r m Ab Bb nr nc cr cc o (i+1) w =
   q5 (v5 k r m Ab Bb nr nc cr cc o i w) (qR k r m Ab Bb nr nc cr cc w (o ⟨i,hi⟩)):=by
 unfold v5
 have htake:(dF k).take (i+1)=(dF k).take i ++ [⟨i,hi⟩]:=by
  rw [dJ (by simp;omega)];simp
 rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
lemma j6 {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) {o:Fin k->Fin k} (ho:Function.Bijective o) (w:ℕ) :
  v5 k r m Ab Bb nr nc cr cc o k w=v4 k r m Ab Bb nr nc cr cc w:=by
 apply v7
 rw [vW _ _ _ _ _ _ _ _ le_rfl,z8]
 have hf:Finset.univ.filter (fun t:Fin k=>t.val < k)=Finset.univ:=by ext t;simp
 rw [hf]
 exact Equiv.sum_comp (Equiv.ofBijective o ho) (fun p=>q4 (qR k r m Ab Bb nr nc cr cc w p))
lemma yx {k r m:ℕ}
  (A B:Fin k->Fin (2^m)) (nr nc:Fin (2^k)) (cr cc:Fin r->Fin (2^k))
  (y:Fin (2^m)) (w:Fin (2^k)) :
  let Ab:Fin k->Q1 m:=fun p q=>(A p).val.testBit q.val
  let Bb:Fin k->Q1 m:=fun p q=>(B p).val.testBit q.val
  let repNat:=(dF k).foldl (fun z p=>
   let bf:=(vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k)
   let bt:=(vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k)
   (z ^^^ (if bf then (A p).val else 0)) ^^^ (if bt then (B p).val else 0)) 0
  repNat=y.val ↔ v4 k r m Ab Bb nr.val nc.val cr cc w.val=fun q=>y.val.testBit q.val:=by
 dsimp only
 set Ab:Fin k->Q1 m:=fun p q=>(A p).val.testBit q.val
 set Bb:Fin k->Q1 m:=fun p q=>(B p).val.testBit q.val
 have hgo:∀ t ≤ k,
   let z:=((dF k).take t).foldl (fun z p=>
    let bf:=(vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k)
    let bt:=(vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k)
    (z ^^^ (if bf then (A p).val else 0)) ^^^ (if bt then (B p).val else 0)) 0
   let v:=((dF k).take t).foldl (fun acc p=>q5 acc (qR k r m Ab Bb nr.val nc.val cr cc w.val p)) (q2 m)
   z < 2^m/\∀ q:Fin m,z.testBit q.val=v q:=by
  intro t
  induction t with
  | zero=>intro _;simp [Nat.two_pow_pos,q2]
  | succ t ih=>
   intro ht
   obtain ⟨hzlt,hztb⟩:=ih (Nat.le_of_succ_le ht)
   have htake:(dF k).take (t+1)=(dF k).take t ++ [⟨t,ht⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,
     List.foldl_append,List.foldl_cons,List.foldl_nil]
   set p:Fin k:=⟨t,ht⟩
   have hltA:(if (vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k)=true then (A p).val else 0) < 2^m:=by
    split_ifs
    ·exact (A p).isLt
    ·exact Nat.two_pow_pos m
   have hltB:(if (vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k)=true then (B p).val else 0) < 2^m:=by
    split_ifs
    ·exact (B p).isLt
    ·exact Nat.two_pow_pos m
   refine ⟨Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hzlt hltA) hltB,fun q=>?_⟩
   simp only [Nat.testBit_xor,hztb q,q5,qR,jM]
   have hAbit:(if (vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k)=true then (A p).val else 0).testBit q.val =
     (if qK (Ab p)&&(vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k) then Ab p else q2 m) q:=by
    by_cases hnz:qK (Ab p)=true
    ·cases (vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k) <;> simp [hnz,Ab,q2]
    ·have h0:Ab p q=false:=by
      by_contra hq
      have hqt:Ab p q=true:=by cases h:Ab p q <;> simp_all
      exact hnz ((qv (Ab p)).trans (decide_eq_true ⟨q,hqt⟩))
     cases (vI k r false w.val nr.val cr).testBit ((p.val+vo r false) % k) <;> simp [hnz,q2,Ab] at h0 ⊢ <;> exact h0
   have hBbit:(if (vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k)=true then (B p).val else 0).testBit q.val =
     (if qK (Bb p)&&(vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k) then Bb p else q2 m) q:=by
    by_cases hnz:qK (Bb p)=true
    ·cases (vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k) <;> simp [hnz,Bb,q2]
    ·have h0:Bb p q=false:=by
      by_contra hq
      have hqt:Bb p q=true:=by cases h:Bb p q <;> simp_all
      exact hnz ((qv (Bb p)).trans (decide_eq_true ⟨q,hqt⟩))
     cases (vI k r true w.val nc.val cc).testBit ((p.val+vo r true) % k) <;> simp [hnz,q2,Bb] at h0 ⊢ <;> exact h0
   rw [hAbit,hBbit,Bool.xor_assoc]
   rfl
 obtain ⟨hlt,htb⟩:=hgo k le_rfl
 rw [show (dF k).take k=dF k by simp] at hlt htb
 change _=y.val ↔ _
 constructor
 ·intro heq;funext q;exact (htb q).symm.trans (congrArg (fun n=>n.testBit q.val) heq)
 ·intro heq
  apply Nat.eq_of_testBit_eq;intro q
  by_cases hq:q < m
  ·exact (htb ⟨q,hq⟩).trans (congrFun heq ⟨q,hq⟩)
  ·rw [Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
     Nat.testBit_lt_two_pow (y.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
def vQ {k:ℕ} (o:Fin k->Fin k) (i:ℕ):Fin k->Bool:=
 fun p=>decide (∃ t:Fin k,t.val < i/\o t=p)
def jq {k:ℕ} (o:Fin k->Fin k) (i:ℕ):Fin k->Bool:=
 fun p=>decide (∃ t:Fin k,i ≤ t.val/\o t=p)
def Qb {k:ℕ} (o:Fin k->Fin k) (i:ℕ):Finset (Fin k):=
 Finset.univ.filter (fun p=>vQ o i p=true)
def Qq {k:ℕ} (o:Fin k->Fin k) (i:ℕ):Finset (Fin k):=
 Finset.univ.filter (fun p=>jq o i p=true)
lemma QT {k:ℕ} (o:Fin k->Fin k) (i:ℕ) :
  Qb o i=((List.ofFn o).take i).toFinset:=by
 ext p
 simp only [Qb,vQ,dK,dL,true_and,dG,
  List.mem_toFinset,List.mem_iff_getElem,List.length_take,List.length_ofFn,List.getElem_take,
  List.getElem_ofFn]
 constructor
 ·rintro ⟨t,hti,rfl⟩;exact ⟨t.val,lt_min hti t.isLt,rfl⟩
 ·rintro ⟨j,hj,rfl⟩;exact ⟨⟨j,(lt_min_iff.mp hj).2⟩,(lt_min_iff.mp hj).1,rfl⟩
lemma QS {k:ℕ} (o:Fin k->Fin k) (i:ℕ) :
  Qq o i=((List.ofFn o).drop i).toFinset:=by
 ext p
 simp only [Qq,jq,dK,dL,true_and,dG,
  List.mem_toFinset,List.mem_iff_getElem,List.length_drop,List.length_ofFn,List.getElem_drop,
  List.getElem_ofFn]
 constructor
 ·rintro ⟨t,hti,rfl⟩
  refine ⟨t.val - i,by omega,?_⟩
  congr 1;apply Fin.ext;dsimp;omega
 ·rintro ⟨j,hj,rfl⟩
  exact ⟨⟨i+j,by omega⟩,by dsimp;omega,rfl⟩
lemma QI {k:ℕ} (o:Fin k->Fin k):Qb o 0=∅:=by
 ext p;simp [Qb,vQ]
lemma QM {k:ℕ} (o:Fin k->Fin k):Qq o k=∅:=by
 ext p;simp only [Qq,jq,dK,dL,true_and,dG,
  Finset.notMem_empty,iff_false];rintro ⟨t,ht,_⟩;omega
lemma QR {k:ℕ} {o:Fin k->Fin k} (ho:Function.Bijective o):Qb o k=Finset.univ:=by
 ext p;simp only [Qb,vQ,dK,dL,true_and,dG,iff_true]
 obtain ⟨t,rfl⟩:=ho.2 p;exact ⟨t,t.isLt,rfl⟩
lemma QX {k:ℕ} {o:Fin k->Fin k} (ho:Function.Bijective o):Qq o 0=Finset.univ:=by
 ext p;simp only [Qq,jq,dK,dL,true_and,dG,iff_true]
 obtain ⟨t,rfl⟩:=ho.2 p;exact ⟨t,Nat.zero_le _,rfl⟩
lemma QN {k:ℕ} (o:Fin k->Fin k) {i:ℕ} (hi:i < k) :
  Qb o (i+1)=insert (o ⟨i,hi⟩) (Qb o i):=by
 ext p;simp only [Qb,vQ,dK,dL,true_and,dG,Finset.mem_insert]
 constructor
 ·rintro ⟨t,hti,rfl⟩
  by_cases hlt:t.val < i
  ·right;exact ⟨t,hlt,rfl⟩
  ·left;congr 1;exact Fin.ext (by dsimp;omega)
 ·rintro (rfl | ⟨t,hti,rfl⟩)
  ·exact ⟨⟨i,hi⟩,by dsimp;omega,rfl⟩
  ·exact ⟨t,by omega,rfl⟩
lemma QU {k:ℕ} (o:Fin k->Fin k) {i:ℕ} (hi:i < k) :
  Qq o i=insert (o ⟨i,hi⟩) (Qq o (i+1)):=by
 ext p;simp only [Qq,jq,dK,dL,true_and,dG,Finset.mem_insert]
 constructor
 ·rintro ⟨t,hti,rfl⟩
  by_cases hgt:i+1 ≤ t.val
  ·right;exact ⟨t,hgt,rfl⟩
  ·left;congr 1;exact Fin.ext (by dsimp;omega)
 ·rintro (rfl | ⟨t,hti,rfl⟩)
  ·exact ⟨⟨i,hi⟩,by dsimp;omega,rfl⟩
  ·exact ⟨t,by omega,rfl⟩
lemma QO {k:ℕ} {o:Fin k->Fin k} (ho:Function.Bijective o) (i:ℕ) :
  Qb o i∪Qq o i=Finset.univ:=by
 ext p;simp only [Qb,Qq,vQ,jq,Finset.mem_union,dK,
  dL,true_and,dG,iff_true]
 obtain ⟨t,rfl⟩:=ho.2 p
 by_cases h:t.val < i
 ·left;exact ⟨t,h,rfl⟩
 ·right;exact ⟨t,by omega,rfl⟩
lemma QQ {k:ℕ} (o:Fin k->Fin k) {i j:ℕ} (hij:i ≤ j):Qb o i ⊆ Qb o j:=by
 intro p hp;simp only [Qb,vQ,dK,dL,true_and,dG] at hp ⊢
 obtain ⟨t,ht,rfl⟩:=hp;exact ⟨t,by omega,rfl⟩
lemma QP {k:ℕ} (o:Fin k->Fin k) {i j:ℕ} (hij:i ≤ j):Qq o j ⊆ Qq o i:=by
 intro p hp;simp only [Qq,jq,dK,dL,true_and,dG] at hp ⊢
 obtain ⟨t,ht,rfl⟩:=hp;exact ⟨t,by omega,rfl⟩
lemma jS {k r m:ℕ} (Ab Bb:Fin k->Q1 m) (nr nc:ℕ)
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (w:ℕ) {i:ℕ} (hi:i ≤ k) :
  q4 (v5 k r m Ab Bb nr nc cr cc o i w)∈qw Ab Bb (Qb o i):=by
 rw [vW _ _ _ _ _ _ _ _ hi]
 refine Submodule.sum_mem _ fun t ht=>?_
 have hti:t.val < i:=(Finset.mem_filter.mp ht).2
 have hmemL:o t∈Qb o i:=Finset.mem_filter.mpr ⟨dL _,decide_eq_true ⟨t,hti,rfl⟩⟩
 refine Submodule.span_mono ?_ (zY Ab Bb nr nc cr cc w (o t))
 intro v hv
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
 rcases hv with rfl | rfl
 ·exact ⟨o t,hmemL,Or.inl rfl⟩
 ·exact ⟨o t,hmemL,Or.inr rfl⟩
lemma vM {k r m:ℕ} (hk:0 < k) (hr:4 ≤ r)
  (Ab Bb:Fin k->Q1 m) {nr nc:ℕ} (hnr:nr < 2^k) (hnc:nc < 2^k)
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k)
  {i:ℕ} (hi:i ≤ k) {w1 w2:ℕ} (hw1:w1 < 2^k) (hw2:w2 < 2^k)
  (hag:∀ z∈qi r Ab Bb (Qb o i),w1.testBit z.val=w2.testBit z.val) :
  v5 k r m Ab Bb nr nc cr cc o i w1=v5 k r m Ab Bb nr nc cr cc o i w2:=by
 apply v7
 rw [vW _ _ _ _ _ _ _ _ hi,vW _ _ _ _ _ _ _ _ hi]
 refine Finset.sum_congr rfl fun t ht=>?_
 have hti:t.val < i:=(Finset.mem_filter.mp ht).2
 have hmemL:o t∈Qb o i:=Finset.mem_filter.mpr ⟨dL _,decide_eq_true ⟨t,hti,rfl⟩⟩
 congr 1
 exact jx hk hr Ab Bb hnr hnc cr cc (o t) hw1 hw2 fun z hz=>
  hag z (Finset.mem_biUnion.mpr ⟨o t,hmemL,hz⟩)
def yC {k m:ℕ} (Ab Bb:Fin k->Q1 m) (mask:Fin k->Bool):Q6 m:=
 (dF k).foldl (fun T p=>if mask p=true then qC (qC T (Ab p)) (Bb p) else T) (qN m)
lemma yf {k m:ℕ} (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)) :
  yC Ab Bb (fun p=>decide (p∈S))=vV Ab Bb S:=by
 unfold yC vV z0
 have hgo:∀ L:List (Fin k),∀ T:Q6 m,
   L.foldl (fun T p=>if decide (p∈S)=true then qC (qC T (Ab p)) (Bb p) else T) T =
   (L.flatMap (fun p=>if p∈S then [Ab p,Bb p] else [])).foldl qC T:=by
  intro L
  induction L with
  | nil=>intro T;rfl
  | cons p rest ih=>
   intro T
   simp only [List.foldl_cons,List.flatMap_cons]
   by_cases hp:p∈S
   ·simp only [hp,decide_true,↓reduceIte,List.cons_append,List.nil_append,List.foldl_cons]
    exact ih _
   ·simp only [hp,decide_false,Bool.false_eq_true,↓reduceIte,List.nil_append]
    exact ih _
 exact hgo (dF k) (qN m)
def y9 {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (mask:Fin k->Bool):Fin k->Bool:=
 fun z=>decide (∃ p:Fin k,mask p=true/\z∈qq r Ab Bb p)
lemma zz {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (S:Finset (Fin k)) (z:Fin k) :
  y9 r Ab Bb (fun p=>decide (p∈S)) z=decide (z∈qi r Ab Bb S):=by
 apply Bool.eq_iff_iff.mpr
 simp [y9,qi,Finset.mem_biUnion]
def Q5 {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ):Finset (Fin k):=
 qi r Ab Bb (Qb o i)∩qi r Ab Bb (Qq o i)
def Qi {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:Fin k):Finset (Fin k):=
 Q5 r Ab Bb o i.val∪qq r Ab Bb (o i)
lemma QV {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) :
  Q5 r Ab Bb o 0=∅:=by
 simp [Q5,QI,qi]
lemma QW {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) :
  Q5 r Ab Bb o k=∅:=by
 simp [Q5,QM,qi]
lemma zy {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:Fin k) :
  qi r Ab Bb (Qb o (i.val+1))=qi r Ab Bb (Qb o i.val)∪qq r Ab Bb (o i):=by
 rw [QN o i.isLt]
 ext z;simp [qi,Finset.mem_biUnion,or_comm]
lemma jP {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m)
  (o:Fin k->Fin k) (i:Fin k) {z:Fin k} (hz:z∈qq r Ab Bb (o i)) :
  z∈qi r Ab Bb (Qb o i.val) ↔ z∈Q5 r Ab Bb o i.val:=by
 have hzR:z∈qi r Ab Bb (Qq o i.val):=
  Finset.mem_biUnion.mpr ⟨o i,Finset.mem_filter.mpr ⟨dL _,decide_eq_true ⟨i,le_rfl,rfl⟩⟩,hz⟩
 simp [Q5,hzR]
lemma QG {k m:ℕ} (r:ℕ) (Ab Bb:Fin k->Q1 m)
  (o:Fin k->Fin k) (i:Fin k) :
  Q5 r Ab Bb o (i.val+1) ⊆ Qi r Ab Bb o i:=by
 intro z hz
 simp only [Q5,Finset.mem_inter] at hz
 rw [zy,Finset.mem_union] at hz
 rcases hz.1 with hzL | hzS
 ·apply Finset.mem_union_left
  refine Finset.mem_inter.mpr ⟨hzL,?_⟩
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (QP o (Nat.le_succ i.val)) hz.2
 ·exact Finset.mem_union_right _ hzS
def yH {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ):Q6 m:=
 yC Ab Bb (vQ o i)
def yg {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ):Q6 m:=
 yC Ab Bb (jq o i)
def vL {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ):Q6 m:=
 (vv (yH Ab Bb o i) (yg Ab Bb o i)).2.2
def qF {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m) (o:Fin k->Fin k) (i:ℕ):Q1 m:=
 let ib:=vv (yH Ab Bb o i) (yg Ab Bb o i)
 (zs ib.1 ib.2.1 (yg Ab Bb o i) y).2
def jT {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m) (o:Fin k->Fin k):Bool:=
 let ib:=vv (yH Ab Bb o k) (qN m)
 (zs ib.1 ib.2.1 (qN m) y).1
def j7 {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:Fin k):Q6 m:=
 (vv (yH Ab Bb o (i.val+1)) (yg Ab Bb o i.val)).2.2
lemma za {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ) :
  Q3 (yH Ab Bb o i)/\q6 (yH Ab Bb o i)=qw Ab Bb (Qb o i):=by
 have h:yH Ab Bb o i=vV Ab Bb (Qb o i):=by
  unfold yH
  rw [show vQ o i=fun p=>decide (p∈Qb o i) by funext p;simp [Qb]]
  exact yf Ab Bb (Qb o i)
 rw [h];exact yl Ab Bb (Qb o i)
lemma yF {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ) :
  Q3 (yg Ab Bb o i)/\q6 (yg Ab Bb o i)=qw Ab Bb (Qq o i):=by
 have h:yg Ab Bb o i=vV Ab Bb (Qq o i):=by
  unfold yg
  rw [show jq o i=fun p=>decide (p∈Qq o i) by funext p;simp [Qq]]
  exact yf Ab Bb (Qq o i)
 rw [h];exact yl Ab Bb (Qq o i)
lemma vO {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:ℕ) :
  Q3 (vL Ab Bb o i) /\
  q6 (vL Ab Bb o i)=qw Ab Bb (Qb o i) ⊓ qw Ab Bb (Qq o i):=by
 obtain ⟨_,hspL⟩:=za Ab Bb o i
 obtain ⟨hER,hspR⟩:=yF Ab Bb o i
 have hib:=jW (yH Ab Bb o i) (yg Ab Bb o i) hER
 refine ⟨hib.2.1,?_⟩
 unfold vL;rw [hib.2.2.2.1,hspL,hspR]
lemma yG {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:Fin k) :
  Q3 (j7 Ab Bb o i) /\
  q6 (j7 Ab Bb o i)=qw Ab Bb (Qb o (i.val+1)) ⊓ qw Ab Bb (Qq o i.val):=by
 obtain ⟨_,hspL⟩:=za Ab Bb o (i.val+1)
 obtain ⟨hER,hspR⟩:=yF Ab Bb o i.val
 have hib:=jW (yH Ab Bb o (i.val+1)) (yg Ab Bb o i.val) hER
 refine ⟨hib.2.1,?_⟩
 unfold j7;rw [hib.2.2.2.1,hspL,hspR]
lemma zJ {k m:ℕ} (Ab Bb:Fin k->Q1 m) (S1 S2:Finset (Fin k)) :
  qw Ab Bb (S1∪S2)=qw Ab Bb S1 ⊔ qw Ab Bb S2:=by
 unfold qw
 rw [← Submodule.span_union]
 congr 1;ext v;simp only [Set.mem_union,Set.mem_setOf_eq,Finset.mem_union]
 constructor
 ·rintro ⟨p,hp1 | hp2,hv⟩
  ·left;exact ⟨p,hp1,hv⟩
  ·right;exact ⟨p,hp2,hv⟩
 ·rintro (⟨p,hp,hv⟩ | ⟨p,hp,hv⟩)
  ·exact ⟨p,Or.inl hp,hv⟩
  ·exact ⟨p,Or.inr hp,hv⟩
lemma zZ {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m)
  {o:Fin k->Fin k} (ho:Function.Bijective o) :
  jT Ab Bb y o=true ↔ q4 y∈qw Ab Bb Finset.univ:=by
 obtain ⟨_,hspL⟩:=za Ab Bb o k
 have hsy:=gj (yH Ab Bb o k) (qN m) (jE m) y
 unfold jT
 rw [hsy.1,hspL,QR ho,y6,sup_bot_eq]
lemma yI {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m)
  {o:Fin k->Fin k} (ho:Function.Bijective o) (hok:jT Ab Bb y o=true) (i:ℕ) :
  q4 (qF Ab Bb y o i)∈qw Ab Bb (Qb o i) /\
  q4 y+q4 (qF Ab Bb y o i)∈qw Ab Bb (Qq o i):=by
 obtain ⟨_,hspL⟩:=za Ab Bb o i
 obtain ⟨hER,hspR⟩:=yF Ab Bb o i
 have hsy:=gj (yH Ab Bb o i) (yg Ab Bb o i) hER y
 have hy_in:q4 y∈q6 (yH Ab Bb o i) ⊔ q6 (yg Ab Bb o i):=by
  rw [hspL,hspR,← zJ,QO ho i]
  exact (zZ Ab Bb y ho).mp hok
 have hok_i:=hsy.1.mpr hy_in
 obtain ⟨hl,hr⟩:=hsy.2 hok_i
 rw [hspL] at hl;rw [hspR,add_comm] at hr
 exact ⟨hl,hr⟩
lemma dm {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m)
  {o:Fin k->Fin k} (ho:Function.Bijective o) (hok:jT Ab Bb y o=true) :
  qF Ab Bb y o 0=q2 m:=by
 have hl:=(yI Ab Bb y ho hok 0).1
 have hemp:qw Ab Bb (Qb o 0)=⊥:=by
  rw [QI];unfold qw;rw [Submodule.span_eq_bot];rintro _ ⟨_,h,_⟩;simp at h
 rw [hemp,Submodule.mem_bot] at hl
 exact v7 (hl.trans (qh m).symm)
lemma dn {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m)
  {o:Fin k->Fin k} (ho:Function.Bijective o) (hok:jT Ab Bb y o=true) :
  qF Ab Bb y o k=y:=by
 have hr:=(yI Ab Bb y ho hok k).2
 have hemp:qw Ab Bb (Qq o k)=⊥:=by
  rw [QM];unfold qw;rw [Submodule.span_eq_bot];rintro _ ⟨_,h,_⟩;simp at h
 rw [hemp,Submodule.mem_bot] at hr
 apply v7
 have h1:=congrArg (fun v=>v+q4 y) hr
 simp only [zero_add] at h1
 have h2:q4 y+q4 (qF Ab Bb y o k)+q4 y=q4 (qF Ab Bb y o k)+(q4 y+q4 y):=by abel
 rw [h2,qM,add_zero] at h1
 exact h1
lemma gu {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) :
  q3 (vL Ab Bb o 0)=0:=by
 obtain ⟨hE,hsp⟩:=vO Ab Bb o 0
 rw [← qo hE,hsp,QI]
 have hemp:qw Ab Bb ∅=⊥:=by
  unfold qw;rw [Submodule.span_eq_bot];rintro _ ⟨_,h,_⟩;simp at h
 rw [hemp,bot_inf_eq,finrank_bot]
lemma zl {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) :
  q3 (vL Ab Bb o k)=0:=by
 obtain ⟨hE,hsp⟩:=vO Ab Bb o k
 rw [← qo hE,hsp,QM]
 have hemp:qw Ab Bb ∅=⊥:=by
  unfold qw;rw [Submodule.span_eq_bot];rintro _ ⟨_,h,_⟩;simp at h
 rw [hemp,inf_bot_eq,finrank_bot]
lemma gv {k m:ℕ} (Ab Bb:Fin k->Q1 m) (y:Q1 m)
  {o:Fin k->Fin k} (ho:Function.Bijective o) (hok:jT Ab Bb y o=true) (i:Fin k) :
  q6 (vL Ab Bb o i.val) ≤ q6 (j7 Ab Bb o i) /\
  q6 (vL Ab Bb o (i.val+1)) ≤ q6 (j7 Ab Bb o i) /\
  q4 (Ab (o i))∈q6 (j7 Ab Bb o i) /\
  q4 (Bb (o i))∈q6 (j7 Ab Bb o i) /\
  q4 (q5 (qF Ab Bb y o i.val) (qF Ab Bb y o (i.val+1)))∈q6 (j7 Ab Bb o i):=by
 have hspM:=(yG Ab Bb o i).2
 have hspTi:=(vO Ab Bb o i.val).2
 have hspTi1:=(vO Ab Bb o (i.val+1)).2
 have hmonoL:qw Ab Bb (Qb o i.val) ≤ qw Ab Bb (Qb o (i.val+1)):=by
  apply Submodule.span_mono;rintro _ ⟨p,hp,hv⟩;exact ⟨p,QQ o (Nat.le_succ _) hp,hv⟩
 have hmonoR:qw Ab Bb (Qq o (i.val+1)) ≤ qw Ab Bb (Qq o i.val):=by
  apply Submodule.span_mono;rintro _ ⟨p,hp,hv⟩;exact ⟨p,QP o (Nat.le_succ _) hp,hv⟩
 have hoL:o i∈Qb o (i.val+1):=by rw [QN o i.isLt];exact Finset.mem_insert_self _ _
 have hoR:o i∈Qq o i.val:=by rw [QU o i.isLt];exact Finset.mem_insert_self _ _
 obtain ⟨hL0,hR0⟩:=yI Ab Bb y ho hok i.val
 obtain ⟨hL1,hR1⟩:=yI Ab Bb y ho hok (i.val+1)
 refine ⟨?_,?_,?_,?_,?_⟩
 ·rw [hspTi,hspM];exact inf_le_inf_right _ hmonoL
 ·rw [hspTi1,hspM];exact inf_le_inf_left _ hmonoR
 ·rw [hspM];exact ⟨Submodule.subset_span ⟨o i,hoL,Or.inl rfl⟩,Submodule.subset_span ⟨o i,hoR,Or.inl rfl⟩⟩
 ·rw [hspM];exact ⟨Submodule.subset_span ⟨o i,hoL,Or.inr rfl⟩,Submodule.subset_span ⟨o i,hoR,Or.inr rfl⟩⟩
 ·rw [hspM,qE]
  refine ⟨Submodule.add_mem _ (hmonoL hL0) hL1,?_⟩
  have hsum:=Submodule.add_mem _ hR0 (hmonoR hR1)
  have heq:(q4 y+q4 (qF Ab Bb y o i.val))+(q4 y+q4 (qF Ab Bb y o (i.val+1))) =
    q4 (qF Ab Bb y o i.val)+q4 (qF Ab Bb y o (i.val+1)):=by
   have h1:(q4 y+q4 (qF Ab Bb y o i.val))+(q4 y+q4 (qF Ab Bb y o (i.val+1))) =
     (q4 y+q4 y)+(q4 (qF Ab Bb y o i.val)+q4 (qF Ab Bb y o (i.val+1))):=by abel
   rw [h1,qM,zero_add]
  rwa [heq] at hsum
lemma gX {k m:ℕ} (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k) (i:Fin k) :
  q3 (j7 Ab Bb o i) ≤ q3 (vL Ab Bb o i.val)+2:=by
 obtain ⟨hEM,hspM⟩:=yG Ab Bb o i
 obtain ⟨hEi,hspTi⟩:=vO Ab Bb o i.val
 rw [← qo hEM,← qo hEi,hspM,hspTi]
 set U:Submodule (ZMod 2) (Fin m->ZMod 2):=qw Ab Bb (Qb o i.val)
 set U':Submodule (ZMod 2) (Fin m->ZMod 2):=qw Ab Bb (Qb o (i.val+1))
 set W:Submodule (ZMod 2) (Fin m->ZMod 2):=qw Ab Bb (Qq o i.val)
 have hU_le:U ≤ U':=by
  apply Submodule.span_mono;rintro _ ⟨p,hp,hv⟩;exact ⟨p,QQ o (Nat.le_succ _) hp,hv⟩
 have hU'_eq:U'=U ⊔ Submodule.span (ZMod 2) ({q4 (Ab (o i)),q4 (Bb (o i))}:Set (Fin m->ZMod 2)):=by
  dsimp only [U',U]
  rw [QN o i.isLt,Finset.insert_eq,zJ,sup_comm]
  congr 1;unfold qw;congr 1;ext v;simp
 have hfin2:Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({q4 (Ab (o i)),q4 (Bb (o i))}:Set (Fin m->ZMod 2))) ≤ 2:=by
  have hsp2:Submodule.span (ZMod 2) ({q4 (Ab (o i)),q4 (Bb (o i))}:Set (Fin m->ZMod 2)) =
    Submodule.span (ZMod 2) {q4 (Ab (o i))} ⊔ Submodule.span (ZMod 2) {q4 (Bb (o i))}:=by
   rw [← Submodule.span_union,Set.singleton_union]
  rw [hsp2]
  have hg:=Submodule.finrank_sup_add_finrank_inf_eq
   (Submodule.span (ZMod 2) {q4 (Ab (o i))}) (Submodule.span (ZMod 2) {q4 (Bb (o i))})
  have h1:Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {q4 (Ab (o i))}) ≤ 1:=by
   by_cases h0:q4 (Ab (o i))=0
   ·rw [h0,Submodule.span_zero_singleton,finrank_bot];omega
   ·rw [finrank_span_singleton h0]
  have h2:Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {q4 (Bb (o i))}) ≤ 1:=by
   by_cases h0:q4 (Bb (o i))=0
   ·rw [h0,Submodule.span_zero_singleton,finrank_bot];omega
   ·rw [finrank_span_singleton h0]
  omega
 have hU'_le:Module.finrank (ZMod 2) U' ≤ Module.finrank (ZMod 2) U+2:=by
  rw [hU'_eq]
  have hg:=Submodule.finrank_sup_add_finrank_inf_eq U
   (Submodule.span (ZMod 2) ({q4 (Ab (o i)),q4 (Bb (o i))}:Set (Fin m->ZMod 2)))
  omega
 have hg1:=Submodule.finrank_sup_add_finrank_inf_eq U W
 have hg2:=Submodule.finrank_sup_add_finrank_inf_eq U' W
 have hsup_le:Module.finrank (ZMod 2) (U ⊔ W:Submodule (ZMod 2) (Fin m->ZMod 2)) ≤
   Module.finrank (ZMod 2) (U' ⊔ W:Submodule (ZMod 2) (Fin m->ZMod 2)):=
  Submodule.finrank_mono (sup_le_sup_right hU_le W)
 omega
lemma d6 {k r m b:ℕ} (Ab Bb:Fin k->Q1 m) {o:Fin k->Fin k}
  (hw:qU r Ab Bb o ≤ b) (i:Fin k) :
  (Qi r Ab Bb o i).card+q3 (j7 Ab Bb o i) ≤ b+2:=by
 have h1:=gX Ab Bb o i
 have h2:(Qi r Ab Bb o i).card+q3 (vL Ab Bb o i.val) ≤ qU r Ab Bb o:=by
  have hsup:((Qi r Ab Bb o i).card+q3 (vL Ab Bb o i.val)) ≤
    (Finset.univ:Finset (Fin k)).sup (fun j=>
     let L:=((List.ofFn o).take j.val).toFinset
     let R:=((List.ofFn o).drop j.val).toFinset
     ((qi r Ab Bb L∩qi r Ab Bb R)∪qq r Ab Bb (o j)).card +
      Module.finrank (ZMod 2) (qw Ab Bb L ⊓ qw Ab Bb R:Submodule (ZMod 2) (Fin m->ZMod 2))):=by
   have hle:=Finset.le_sup (f:=fun j:Fin k=>
     let L:=((List.ofFn o).take j.val).toFinset
     let R:=((List.ofFn o).drop j.val).toFinset
     ((qi r Ab Bb L∩qi r Ab Bb R)∪qq r Ab Bb (o j)).card +
      Module.finrank (ZMod 2) (qw Ab Bb L ⊓ qw Ab Bb R:Submodule (ZMod 2) (Fin m->ZMod 2)))
    (dL i)
   dsimp only at hle
   rw [← QT,← QS] at hle
   obtain ⟨hEi,hspTi⟩:=vO Ab Bb o i.val
   rwa [← qo hEi,hspTi]
  exact hsup
 omega
abbrev Ql (k B:ℕ):=Fin k->Fin B->Bool
def q7 {k B:ℕ} (M:Ql k B):Fin B->Bool:=
 fun s=>decide (∃ z:Fin k,M z s=true)
def qO {B:ℕ} (u:Fin B->Bool):Fin B->Bool:=
 fun s=>decide (u s=false/\∀ s':Fin B,s.val < s'.val->u s'=true)
def qV {B:ℕ} (u:Fin B->Bool):Fin B->Bool:=
 fun s=>decide (u s=true/\∀ s':Fin B,s'.val < s.val->u s'=false)
def y7 {k B:ℕ} (M:Ql k B) (uOH vOH:Fin B->Bool):Ql k B:=
 fun z s=>
  if uOH s=true then decide (∃ v:Fin B,vOH v=true/\M z v=true)
  else if vOH s=true then decide (∃ u:Fin B,uOH u=true/\M z u=true)
  else M z s
def qn {k B:ℕ} (M:Ql k B) (z:Fin k) (cond:Bool):Ql k B:=
 if cond=true then
  let oh:=qO (q7 M)
  fun z' s=>if z'=z then oh s else M z' s
 else M
def qA {k B:ℕ} (M:Ql k B) (z:Fin k) (cond:Bool):Ql k B:=
 if cond=true then
  let sOH:=M z
  let loOH:=qV (q7 M)
  let M1:Ql k B:=fun z' s=>if z'=z then false else M z' s
  y7 M1 sOH loOH
 else M
def QA {k B:ℕ} (M:Ql k B) (S:Finset (Fin k)):Prop:=
 S.card ≤ B /\
 (∀ z∈S,∃ s:Fin B,B - S.card ≤ s.val/\M z=fun t=>decide (t=s)) /\
 (∀ z∉S,M z=fun _=>false) /\
 (∀ z1 z2:Fin k,∀ s:Fin B,M z1 s=true->M z2 s=true->z1=z2) /\
 (∀ s:Fin B,q7 M s=decide (B - S.card ≤ s.val))
lemma gW (k B:ℕ):QA (fun (_:Fin k) (_:Fin B)=>false) ∅:=by
 refine ⟨Nat.zero_le B,fun _ h=>absurd h (by simp),fun _ _=>rfl,
  fun _ _ _ h=>absurd h (by simp),fun s=>?_⟩
 simp only [q7,Finset.card_empty,Nat.sub_zero,Bool.false_eq_true,exists_false,decide_false]
 symm;exact decide_eq_false (by omega)
lemma gI {k B:ℕ} {M:Ql k B} {S:Finset (Fin k)}
  (hInv:QA M S) {z:Fin k} (hz:z∉S) (hroom:S.card < B) :
  let sNew:Fin B:=⟨B - 1 - S.card,by omega⟩
  qO (q7 M)=(fun t=>decide (t=sNew)) /\
  QA (qn M z true) (insert z S):=by
 obtain ⟨hcard,hmem,hnot,hinj,hused⟩:=hInv
 set sNew:Fin B:=⟨B - 1 - S.card,by omega⟩
 have hoh:qO (q7 M)=fun t=>decide (t=sNew):=by
  funext t
  apply Bool.eq_iff_iff.mpr
  simp only [qO,hused,dG,decide_eq_false_iff_not,not_le]
  constructor
  ·rintro ⟨hlt,hall⟩
   apply Fin.ext;dsimp only [sNew]
   by_contra hne
   have hlt2:t.val < B - 1 - S.card:=by omega
   have hbad:=hall sNew (by dsimp [sNew];omega)
   dsimp [sNew] at hbad;omega
  ·rintro rfl
   exact ⟨by dsimp [sNew];omega,fun s' hs'=>by dsimp [sNew] at hs';omega⟩
 refine ⟨hoh,?_⟩
 have hcard':(insert z S).card=S.card+1:=Finset.card_insert_of_notMem hz
 refine ⟨by omega,?_,?_,?_,?_⟩
 ·intro z' hz'
  rw [Finset.mem_insert] at hz'
  rcases hz' with rfl | hzS
  ·refine ⟨sNew,by dsimp [sNew];omega,?_⟩
   funext t;simp [qn,hoh]
  ·obtain ⟨s,hs,hMs⟩:=hmem z' hzS
   have hne:z' ≠ z:=fun e=>hz (e▸hzS)
   refine ⟨s,by omega,?_⟩
   funext t;simp [qn,hne,hMs]
 ·intro z' hz'
  have hne:z' ≠ z:=fun e=>hz' (e▸Finset.mem_insert_self z S)
  have hnotS:z'∉S:=fun h=>hz' (Finset.mem_insert_of_mem h)
  funext t;simp [qn,hne,hnot z' hnotS]
 ·intro z1 z2 s h1 h2
  simp only [qn,↓reduceIte,hoh] at h1 h2
  by_cases e1:z1=z <;> by_cases e2:z2=z
  ·exact e1.trans e2.symm
  ·simp only [e1,e2,↓reduceIte,dG] at h1 h2
   subst h1
   have hu:q7 M sNew=true:=by simp [q7];exact ⟨z2,h2⟩
   rw [hused sNew] at hu;simp only [dG,sNew] at hu;omega
  ·simp only [e1,e2,↓reduceIte,dG] at h1 h2
   subst h2
   have hu:q7 M sNew=true:=by simp [q7];exact ⟨z1,h1⟩
   rw [hused sNew] at hu;simp only [dG,sNew] at hu;omega
  ·simp only [e1,e2,↓reduceIte] at h1 h2
   exact hinj z1 z2 s h1 h2
 ·intro s
  apply Bool.eq_iff_iff.mpr
  simp only [q7,qn,↓reduceIte,hoh,dG,hcard']
  constructor
  ·rintro ⟨z',hz'⟩
   by_cases ez:z'=z
   ·simp only [ez,↓reduceIte,dG] at hz';subst hz';dsimp [sNew];omega
   ·simp only [ez,↓reduceIte] at hz'
    have hu:q7 M s=true:=by simp [q7];exact ⟨z',hz'⟩
    rw [hused s] at hu;simp only [dG] at hu;omega
  ·intro hs
   by_cases heq:s=sNew
   ·subst heq;exact ⟨z,by simp⟩
   ·have hs':B - S.card ≤ s.val:=by
     have:s.val ≠ B - 1 - S.card:=fun e=>heq (Fin.ext e)
     omega
    have hu:q7 M s=true:=by rw [hused s];exact decide_eq_true hs'
    simp only [q7,dG] at hu
    obtain ⟨z',hz'⟩:=hu
    have hne:z' ≠ z:=fun e=>by subst e;rw [hnot z' hz] at hz';simp at hz'
    exact ⟨z',by simp [hne,hz']⟩
lemma gr {k B:ℕ} {M:Ql k B} {S:Finset (Fin k)}
  (hInv:QA M S) {z:Fin k} (hz:z∈S) :
  let sLo:Fin B:=⟨B - S.card,by have:=Finset.card_pos.mpr ⟨z,hz⟩;have:=hInv.1;omega⟩
  qV (q7 M)=(fun t=>decide (t=sLo)) /\
  QA (qA M z true) (S.erase z) /\
  (∀ sZ:Fin B,M z=(fun t=>decide (t=sZ)) ->
   ∀ z':Fin k,∀ t:Fin B,
    qA M z true z' t =
     if z'=z then false else M z' (if t=sZ then sLo else if t=sLo then sZ else t)):=by
 obtain ⟨hcard,hmem,hnot,hinj,hused⟩:=hInv
 have hpos:0 < S.card:=Finset.card_pos.mpr ⟨z,hz⟩
 set sLo:Fin B:=⟨B - S.card,by omega⟩
 have hlo:qV (q7 M)=fun t=>decide (t=sLo):=by
  funext t
  apply Bool.eq_iff_iff.mpr
  simp only [qV,hused,dG,decide_eq_false_iff_not,not_le]
  constructor
  ·rintro ⟨hge,hall⟩
   apply Fin.ext;dsimp only [sLo]
   by_contra hne
   have hbad:=hall sLo (by dsimp [sLo];omega)
   dsimp [sLo] at hbad;omega
  ·rintro rfl
   exact ⟨by dsimp [sLo];omega,fun s' hs'=>by dsimp [sLo] at hs';omega⟩
 obtain ⟨sZ,hsZ_ge,hMz⟩:=hmem z hz
 have hform:∀ sZ':Fin B,M z=(fun t=>decide (t=sZ')) ->
   ∀ z':Fin k,∀ t:Fin B,
    qA M z true z' t =
     if z'=z then false else M z' (if t=sZ' then sLo else if t=sLo then sZ' else t):=by
  intro sZ' hMz' z' t
  simp only [qA,↓reduceIte,y7,hMz',hlo]
  by_cases h1:t=sZ'
  ·subst h1
   simp only [decide_true,↓reduceIte]
   apply Bool.eq_iff_iff.mpr;simp only [dG]
   by_cases ez:z'=z
   ·simp [ez]
   ·simp only [ez,↓reduceIte]
    exact ⟨fun ⟨v,hv,hm⟩=>hv▸hm,fun hm=>⟨sLo,rfl,hm⟩⟩
  ·by_cases h2:t=sLo
   ·subst h2
    simp only [h1,decide_false,Bool.false_eq_true,decide_true,↓reduceIte]
    apply Bool.eq_iff_iff.mpr;simp only [dG]
    by_cases ez:z'=z
    ·simp [ez]
    ·simp only [ez,↓reduceIte]
     exact ⟨fun ⟨u,hu,hm⟩=>hu▸hm,fun hm=>⟨sZ',rfl,hm⟩⟩
   ·simp [h1,h2]
 have hcard':(S.erase z).card=S.card - 1:=Finset.card_erase_of_mem hz
 refine ⟨hlo,?_,hform⟩
 have hF:=hform sZ hMz
 refine ⟨by omega,?_,?_,?_,?_⟩
 ·intro z' hz'
  have hne:z' ≠ z:=(Finset.mem_erase.mp hz').1
  have hzS:z'∈S:=(Finset.mem_erase.mp hz').2
  obtain ⟨s',hs'_ge,hMz'⟩:=hmem z' hzS
  have hs'_ne:s' ≠ sZ:=fun e=>hne (hinj z' z s' (by rw [hMz'];simp) (by rw [hMz,e];simp))
  by_cases hsl:s'=sLo
  ·refine ⟨sZ,?_,?_⟩
   ·have hsZ_ne_lo:sZ ≠ sLo:=fun e=>hs'_ne (hsl.trans e.symm)
    have:sZ.val ≠ B - S.card:=fun e=>hsZ_ne_lo (Fin.ext e)
    omega
   ·funext t;rw [hF z' t];simp only [hne,↓reduceIte,hMz',hsl]
    by_cases h1:t=sZ
    ·simp [h1]
    ·by_cases h2:t=sLo
     ·simp [h2,show sLo ≠ sZ from fun e=>h1 (h2.trans e),show sZ ≠ sLo from fun e=>h1 (h2.trans e.symm)]
     ·simp [h1,h2]
  ·refine ⟨s',?_,?_⟩
   ·have:s'.val ≠ B - S.card:=fun e=>hsl (Fin.ext e)
    omega
   ·funext t;rw [hF z' t];simp only [hne,↓reduceIte,hMz']
    by_cases h1:t=sZ
    ·simp [h1,Ne.symm hsl,Ne.symm hs'_ne]
    ·by_cases h2:t=sLo
     ·simp [h1,h2,show sLo ≠ sZ from fun e=>h1 (h2.trans e),Ne.symm hsl,Ne.symm hs'_ne]
     ·simp [h1,h2]
 ·intro z' hz'
  funext t;rw [hF z' t]
  by_cases ez:z'=z
  ·simp [ez]
  ·have hnotS:z'∉S:=fun h=>hz' (Finset.mem_erase.mpr ⟨ez,h⟩)
   simp [ez,hnot z' hnotS]
 ·intro z1 z2 s h1 h2
  rw [hF z1 s] at h1;rw [hF z2 s] at h2
  by_cases e1:z1=z;· simp [e1] at h1
  by_cases e2:z2=z;· simp [e2] at h2
  simp only [e1,e2,↓reduceIte] at h1 h2
  exact hinj z1 z2 _ h1 h2
 ·intro s
  apply Bool.eq_iff_iff.mpr
  simp only [q7,dG,hcard']
  constructor
  ·rintro ⟨z',hz'⟩
   rw [hF z' s] at hz'
   by_cases ez:z'=z;· simp [ez] at hz'
   simp only [ez,↓reduceIte] at hz'
   have hne_lo:s ≠ sLo:=by
    intro heq;subst heq
    by_cases heq2:sLo=sZ
    ·rw [if_pos heq2] at hz'
     exact ez (hinj z' z sLo hz' (by rw [hMz,heq2];simp))
    ·rw [if_neg heq2,if_pos rfl] at hz'
     exact ez (hinj z' z sZ hz' (by rw [hMz];simp))
   have hu:q7 M (if s=sZ then sLo else if s=sLo then sZ else s)=true:=by
    simp [q7];exact ⟨z',hz'⟩
   rw [hused] at hu;simp only [dG] at hu
   have hne_val:s.val ≠ B - S.card:=fun e=>hne_lo (Fin.ext e)
   by_cases h1:s=sZ
   ·subst h1;omega
   ·simp only [h1,hne_lo,↓reduceIte] at hu;omega
  ·intro hs
   have hne_lo:s ≠ sLo:=by intro e;subst e;dsimp [sLo] at hs;omega
   set s':=if s=sZ then sLo else s
   have hs'_ge:B - S.card ≤ s'.val:=by
    dsimp only [s']
    split_ifs
    ·dsimp [sLo];omega
    ·omega
   have hu:q7 M s'=true:=by rw [hused s'];exact decide_eq_true hs'_ge
   simp only [q7,dG] at hu
   obtain ⟨z',hz'⟩:=hu
   have hne_z:z' ≠ z:=by
    intro e;subst e;rw [hMz] at hz';simp only [dG,s'] at hz'
    by_cases h1:s=sZ
    ·rw [if_pos h1] at hz';exact hne_lo (h1.trans hz'.symm)
    ·rw [if_neg h1] at hz';exact h1 hz'
   refine ⟨z',?_⟩
   rw [hF z' s];simp only [hne_z,↓reduceIte,hne_lo];exact hz'
lemma j4 {B:ℕ} {α:Type*} (s0:Fin B) (f:Fin B->α->α) (init:α) :
  (dF B).foldl (fun a s=>if s=s0 then f s a else a) init=f s0 init:=by
 have hgo:∀ t ≤ B,((dF B).take t).foldl (fun a s=>if s=s0 then f s a else a) init =
   if s0.val < t then f s0 init else init:=by
  intro t;induction t with
  | zero=>intro _;simp
  | succ t ih=>
   intro ht
   have htake:(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
    rw [dJ (by simp;omega)];simp
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,ih (Nat.le_of_succ_le ht)]
   by_cases heq:(⟨t,ht⟩:Fin B)=s0
   ·have hv:s0.val=t:=congrArg Fin.val heq.symm
    rw [if_pos heq,if_neg (by omega),if_pos (by omega),heq]
   ·have hv:s0.val ≠ t:=fun e=>heq (Fin.ext e.symm)
    have hiff:s0.val < t+1 ↔ s0.val < t:=by omega
    simp [heq,hiff]
 have hm:=hgo B le_rfl
 rw [show (dF B).take B=dF B by simp,if_pos s0.isLt] at hm
 exact hm
lemma yU {α β:Type*} (L:List β) (init:α) :
  L.foldl (fun a _=>a) init=init:=by
 induction L with
 | nil=>rfl
 | cons _ _ ih=>exact ih
lemma qx {m B:ℕ} {T:Q6 m} (hT:Q3 T) (hB:q3 T ≤ B)
  {x y:Q1 B} (hag:∀ t:Fin B,t.val < q3 T->x t=y t) :
  q1 T x=q1 T y:=by
 have hge:=(jv T hT hB).1
 have hgo:∀ k ≤ B,
   ((dF B).take k).foldl (fun acc t=>if x t=true then q5 acc (qc T B t) else acc) (q2 m) =
   ((dF B).take k).foldl (fun acc t=>if y t=true then q5 acc (qc T B t) else acc) (q2 m):=by
  intro k;induction k with
  | zero=>intro _;rfl
  | succ k ih=>
   intro hk
   have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,
     List.foldl_append,List.foldl_cons,List.foldl_nil,ih (Nat.le_of_succ_le hk)]
   by_cases hlt:k < q3 T
   ·rw [hag ⟨k,hk⟩ hlt]
   ·rw [hge ⟨k,hk⟩ (by dsimp;omega)]
    have hz:∀ v:Q1 m,q5 v (q2 m)=v:=fun v=>by funext q;simp [q5,q2]
    split_ifs <;> simp [hz]
 have hm:=hgo B le_rfl
 rw [show (dF B).take B=dF B by simp] at hm
 exact hm
lemma jK {m B:ℕ} {T_U T_M:Q6 m}
  (hU:Q3 T_U) (hM:Q3 T_M)
  (hsub:q6 T_U ≤ q6 T_M) (hBM:q3 T_M ≤ B) :
  let G:=qk T_U T_M B
  Q7 G /\
  (∀ x:Q1 B,∀ t:Fin B,q3 T_M ≤ t.val->qT G x t=x t) /\
  (∀ x:Q1 B,(∀ t:Fin B,q3 T_U ≤ t.val->t.val < q3 T_M->x t=false) ->
   q1 T_M (qT G x)=q1 T_U x) /\
  (∀ y:Q1 B,
   (q4 (q1 T_M y)∈q6 T_U ↔
    ∀ t:Fin B,q3 T_U ≤ t.val->t.val < q3 T_M->qT (j1 G) y t=false)):=by
 obtain ⟨hInv,hColsU,hBlk⟩:=zV hU hM hsub hBM
 have hBU:q3 T_U ≤ q3 T_M:=by
  rw [← qo hU,← qo hM];exact Submodule.finrank_mono hsub
 have hBU_le:q3 T_U ≤ B:=hBU.trans hBM
 obtain ⟨hM_ge,hM_rc,hM_cr,hM_mem,hM_xor⟩:=qg T_M hM hBM
 obtain ⟨hU_ge,hU_rc,_,hU_mem,_⟩:=qg T_U hU hBU_le
 set G:=qk T_U T_M B
 have hhi:∀ x:Q1 B,∀ t:Fin B,q3 T_M ≤ t.val->qT G x t=x t:=by
  intro x t ht
  have h1:=congrFun (vX G x) t
  simp only [Matrix.mulVec,dotProduct,qm,yP] at h1
  rw [Finset.sum_eq_single t] at h1
  ·rw [hBlk t t (Or.inl ht)] at h1;simp only [decide_true,b2z,↓reduceIte,one_mul] at h1
   cases hG:qT G x t <;> cases hx:x t <;> simp_all [b2z]
  ·intro j _ hj;rw [hBlk t j (Or.inl ht),decide_eq_false hj.symm];simp [b2z]
  ·intro h;exact absurd (dL t) h
 have hrec:∀ x:Q1 B,(∀ t:Fin B,q3 T_U ≤ t.val->t.val < q3 T_M->x t=false) ->
   q1 T_M (qT G x)=q1 T_U x:=by
  intro x hgap
  let xLo:Q1 B:=fun t=>if t.val < q3 T_U then x t else false
  let cLo:Q1 B:=qf T_M (q1 T_U xLo) B
  have hlo_eq:∀ r:Fin B,r.val < q3 T_M->qT G x r=cLo r:=by
   intro r hr
   have hcoord_lin:∀ k ≤ B,
     qf T_M (((dF B).take k).foldl
      (fun acc j=>if xLo j=true then q5 acc (qc T_U B j) else acc) (q2 m)) B =
     fun i=>yo ((dF B).take k) (fun j=>G i j&&xLo j):=by
    intro k;induction k with
    | zero=>
     intro _;simp only [List.take_zero,List.foldl_nil,yo]
     exact jJ T_M hM hBM
    | succ k ih=>
     intro hk
     have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
      rw [dJ (by simp;omega)];simp
     rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
     have hprev_mem:q4 (((dF B).take k).foldl
       (fun acc j=>if xLo j=true then q5 acc (qc T_U B j) else acc) (q2 m))∈q6 T_M:=by
      apply hsub
      have hrec_eq:((dF B).take k).foldl
        (fun acc j=>if xLo j=true then q5 acc (qc T_U B j) else acc) (q2 m) =
        q1 T_U (fun j=>if j.val < k then xLo j else false):=by
       unfold q1
       have hgo2:∀ t ≤ B,
         ((dF B).take t).foldl
          (fun acc j=>if (if j.val < k then xLo j else false)=true then q5 acc (qc T_U B j) else acc) (q2 m) =
         ((dF B).take (min t k)).foldl
          (fun acc j=>if xLo j=true then q5 acc (qc T_U B j) else acc) (q2 m):=by
        intro t;induction t with
        | zero=>intro _;simp
        | succ t iht=>
         intro ht
         have ht':(dF B).take (t+1)=(dF B).take t ++ [⟨t,ht⟩]:=by
          rw [dJ (by simp;omega)];simp
         rw [ht',List.foldl_append,List.foldl_cons,List.foldl_nil,iht (Nat.le_of_succ_le ht)]
         by_cases htk:t < k
         ·have hm1:min (t+1) k=t+1:=by omega
          have hm2:min t k=t:=by omega
          rw [hm1,hm2,ht',List.foldl_append,List.foldl_cons,List.foldl_nil]
          simp [htk]
         ·have hm1:min (t+1) k=k:=by omega
          have hm2:min t k=k:=by omega
          rw [hm1,hm2];simp [htk]
       have:=hgo2 B le_rfl
       rw [show (dF B).take B=dF B by simp,Nat.min_eq_right (Nat.le_of_succ_le hk)] at this
       exact this.symm
      rw [hrec_eq];exact hU_mem _
     set jk:Fin B:=⟨k,hk⟩
     have hfold_step:∀ i,yo ((dF B).take k ++ [jk]) (fun j=>G i j&&xLo j) =
       xor (yo ((dF B).take k) (fun j=>G i j&&xLo j)) (G i jk&&xLo jk):=fun i=>by
      simp [yo]
     by_cases hxjk:xLo jk=true
     ·have hltU:k < q3 T_U:=by
       by_contra hge
       have hxf:xLo jk=false:=by simp [xLo,jk,show ¬ k < q3 T_U by omega]
       rw [hxf] at hxjk;exact Bool.false_ne_true hxjk
      obtain ⟨c0,_,hrow0,_⟩:=(jv T_U hU hBU_le).2.1 jk hltU
      have hjk_mem:q4 (qc T_U B jk)∈q6 T_M:=
       hsub (by rw [hrow0];exact Submodule.subset_span ⟨c0,rfl⟩)
      rw [if_pos hxjk,yY T_M hM hBM hprev_mem hjk_mem,ih (Nat.le_of_succ_le hk)]
      funext i;rw [hfold_step i];simp only [q5,hxjk,Bool.and_true]
      rw [congrFun (hColsU jk hltU) i]
     ·have hxf:xLo jk=false:=Bool.eq_false_iff.mpr hxjk
      rw [if_neg hxjk,ih (Nat.le_of_succ_le hk)]
      funext i;rw [hfold_step i];simp [hxf]
   have hfull:=hcoord_lin B le_rfl
   rw [show (dF B).take B=dF B by simp] at hfull
   have hcLo_r:cLo r=qT G xLo r:=congrFun hfull r
   rw [hcLo_r]
   have h1:=congrFun (vX G x) r
   have h2:=congrFun (vX G xLo) r
   simp only [Matrix.mulVec,dotProduct,qm,yP] at h1 h2
   have hsum_eq:(∑ j:Fin B,b2z (G r j)*b2z (x j))=∑ j:Fin B,b2z (G r j)*b2z (xLo j):=by
    refine Finset.sum_congr rfl fun j _=>?_
    by_cases hjU:j.val < q3 T_U
    ·simp [xLo,hjU]
    ·by_cases hjM:j.val < q3 T_M
     ·rw [hgap j (by omega) hjM];simp [xLo,hjU]
     ·have hne:r ≠ j:=fun e=>by subst e;omega
      rw [hBlk r j (Or.inr (by omega)),decide_eq_false hne];simp [b2z]
   rw [hsum_eq,← h2] at h1
   cases ha:qT G x r <;> cases hb:qT G xLo r
   ·rfl
   ·rw [ha,hb] at h1;exact absurd h1 (by decide)
   ·rw [ha,hb] at h1;exact absurd h1 (by decide)
   ·rfl
  rw [qx hM hBM hlo_eq]
  rw [hM_rc _ (hsub (hU_mem xLo))]
  exact qx hU hBU_le (fun t ht=>by simp [xLo,ht])
 refine ⟨hInv,hhi,hrec,fun y=>?_⟩
 obtain ⟨hGinv,hinvG⟩:=jF hInv
 set x:=qT (j1 G) y
 have hGx:qT G x=y:=by rw [← jr,hGinv,yj]
 constructor
 ·intro hin
  let x':Q1 B:=fun t=>
   if t.val < q3 T_U then qf T_U (q1 T_M y) B t
   else if q3 T_M ≤ t.val then y t else false
  have hx'gap:∀ t:Fin B,q3 T_U ≤ t.val->t.val < q3 T_M->x' t=false:=by
   intro t h1 h2;dsimp [x'];rw [if_neg (by omega),if_neg (by omega)]
  have hGx'_rec:q1 T_M (qT G x')=q1 T_M y:=by
   rw [hrec x' hx'gap]
   rw [qx hU hBU_le (y:=qf T_U (q1 T_M y) B) (fun t ht=>by simp [x',ht])]
   exact hU_rc _ hin
  have hGx'_eq:qT G x'=y:=by
   funext t
   by_cases ht:t.val < q3 T_M
   ·have hlo1:(fun j:Fin B=>if j.val < q3 T_M then qT G x' j else false) =
      (fun j:Fin B=>if j.val < q3 T_M then y j else false):=by
     have hc1:=hM_cr (fun j=>if j.val < q3 T_M then qT G x' j else false) (fun j hj=>by simp [show ¬ j.val < q3 T_M by omega])
     have hc2:=hM_cr (fun j=>if j.val < q3 T_M then y j else false) (fun j hj=>by simp [show ¬ j.val < q3 T_M by omega])
     rw [qx hM hBM (y:=qT G x') (fun j hj=>by simp [hj])] at hc1
     rw [qx hM hBM (y:=y) (fun j hj=>by simp [hj])] at hc2
     rw [← hc1,← hc2,hGx'_rec]
    have:=congrFun hlo1 t;simpa [ht] using this
   ·rw [hhi x' t (by omega)];dsimp [x'];rw [if_neg (by omega),if_pos (by omega)]
  have hx_eq:x=x':=by
   calc x=qT (j1 G) (qT G x'):=by rw [hGx'_eq]
    _=x':=by rw [← jr,hinvG,yj]
  rw [hx_eq];exact hx'gap
 ·intro hgap
  rw [← hGx,hrec x hgap];exact hU_mem x
def jm (B:ℕ) (s:Fin B) (fix val:Bool) (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 fun idx=>
  let bit:=v8 B idx s
  let base:=DP (if bit=true then jw idx s else idx)
  if fix=true then (if bit=val then base else 0) else base
def qY (B:ℕ) (cond:Bool) (oh:Fin B->Bool) (fix val:Bool)
  (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 (dF B).foldl (fun D s=>if cond&&oh s then jm B s fix val D else D) DP
def vh (B:ℕ) (t:Fin B) (fl:Fin (2^B)->Bool)
  (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 fun idx=>if fl idx=true then DP (jw idx t) else DP idx
def j9 (B k:ℕ) (s:Fin B) (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 fun idx=>if v8 B idx s=false then (DP idx+DP (jw idx s)) % 2^(k+1) else 0
def qZ (B k:ℕ) (cond:Bool) (oh:Fin B->Bool)
  (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 (dF B).foldl (fun D s=>if cond&&oh s then j9 B k s D else D) DP
def qI (B:ℕ) (cond:Bool) (uOH vOH:Fin B->Bool)
  (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 (dF B).foldl (fun D u=>
  (dF B).foldl (fun D' v=>
   if cond&&uOH u&&vOH v then (fun idx=>D' (vY idx u v)) else D') D) DP
def zE (B:ℕ) (keep:Fin (2^B)->Bool) (DP:Fin (2^B)->ℕ):Fin (2^B)->ℕ:=
 fun idx=>if keep idx=true then DP idx else 0
def qB {k m:ℕ} (r b:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k)
  (i:Fin k) (M:Ql k (b+2)):Ql k (b+2):=
 (dF k).foldl (fun Mc z=>
  qn Mc z (decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val))) M
def vN {k m:ℕ} (r b:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k)
  (i:Fin k) (M:Ql k (b+2)):Ql k (b+2):=
 (dF k).foldl (fun Mc z=>
  qA Mc z (decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1)))) M
def qt {k m:ℕ} (r b:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k)
  (t:ℕ):Ql k (b+2):=
 ((dF k).take t).foldl (fun M i=>
  vN r b Ab Bb o i (qB r b Ab Bb o i M)) (fun _ _=>false)
def jL {k B:ℕ} (M:Ql k B) (sc:Fin k->Bool) (idx:Fin (2^B)):ℕ:=
 qu (fun z:Fin k=>sc z&&decide (∃ s:Fin B,M z s=true/\v8 B idx s=true))
def jB {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr:Fin (2^k))
  (cr:Fin r->Fin (2^k)) (o:Fin k->Fin k) (i:Fin k) (idx:Fin (2^(b+2))):Bool:=
 let Mmid:=qB r b Ab Bb o i (qt r b Ab Bb o i.val)
 let wLoc:=jL Mmid (fun z=>decide (z∈qq r Ab Bb (o i))) idx
 qK (Ab (o i))&&jM k r false wLoc nr.val cr (o i)
def jA {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nc:Fin (2^k))
  (cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (i:Fin k) (idx:Fin (2^(b+2))):Bool:=
 let Mmid:=qB r b Ab Bb o i (qt r b Ab Bb o i.val)
 let wLoc:=jL Mmid (fun z=>decide (z∈qq r Ab Bb (o i))) idx
 qK (Bb (o i))&&jM k r true wLoc nc.val cc (o i)
def vP {k m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k)
  (i:Fin k) (idx:Fin (2^(b+2))):Bool:=
 !qK (q8 (yg Ab Bb o (i.val+1)) (q1 (j7 Ab Bb o i) (v8 (b+2) idx)))
def zD {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (y:Q1 m) (o:Fin k->Fin k)
  (prefFix prefVal:Fin k->Bool) (i:Fin k) (DP:Fin (2^(b+2))->ℕ):Fin (2^(b+2))->ℕ:=
 let B:=b+2
 let TM:=j7 Ab Bb o i
 let Min:=qt r b Ab Bb o i.val
 let DP1:=jZ (qk (vL Ab Bb o i.val) TM B) DP
 let st2:=(dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
  let cond:=decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val)
  (qn st.1 z cond,qY B cond (qO (q7 st.1)) (prefFix z) (prefVal z) st.2))
  (Min,DP1)
 let cdy:=qf TM (q5 (qF Ab Bb y o i.val) (qF Ab Bb y o (i.val+1))) B
 let cA:=qf TM (Ab (o i)) B
 let cB:=qf TM (Bb (o i)) B
 let DP3:=(dF B).foldl (fun D t=>
  vh B t (fun idx=>
   xor (cdy t) (xor (cA t&&jB b Ab Bb nr cr o i idx) (cB t&&jA b Ab Bb nc cc o i idx))) D) st2.2
 let st4:=(dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
  let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))
  let loOH:=qV (q7 st.1)
  (qA st.1 z cond,qI B cond (st.1 z) loOH (qZ B k cond (st.1 z) st.2)))
  (st2.1,DP3)
 let DP5:=zE B (vP b Ab Bb o i) st4.2
 jZ (j1 (qk (vL Ab Bb o (i.val+1)) TM B)) DP5
def ym (k:ℕ) (poolAll prefFix:Fin k->Bool) (val:ℕ):ℕ:=
 (dF k).foldl (fun acc z=>if !poolAll z&&!prefFix z then (acc+acc) % 2^(k+1) else acc) val
def qX {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (y:Q1 m) (o:Fin k->Fin k)
  (prefFix prefVal:Fin k->Bool):ℕ:=
 if jT Ab Bb y o=true then
  let DP0:Fin (2^(b+2))->ℕ:=fun idx=>if idx.val=0 then 1 else 0
  let DPF:=(dF k).foldl (fun D i=>zD b Ab Bb nr nc cr cc y o prefFix prefVal i D) DP0
  ym k (y9 r Ab Bb (vQ o k)) prefFix (DPF ⟨0,Nat.two_pow_pos _⟩)
 else 0
def d4 {k:ℕ} (prefFix prefVal:Fin k->Bool) (w:Fin (2^k)):Prop:=
 ∀ z:Fin k,prefFix z=true->w.val.testBit z.val=prefVal z
def v9 {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (prefFix prefVal:Fin k->Bool)
  (P:Finset (Fin k)) (M:Ql k (b+2)) (T:Q6 m) (i:ℕ) (lvec:Q1 m)
  (x:Q1 (b+2)):Finset (Fin (2^k)):=
 Finset.univ.filter fun w=>
  (∀ z:Fin k,z∉P->w.val.testBit z.val=false) /\
  (∀ z:Fin k,z∈P->prefFix z=true->w.val.testBit z.val=prefVal z) /\
  (∀ z:Fin k,∀ s:Fin (b+2),M z s=true->w.val.testBit z.val=x s) /\
  q5 (v5 k r m Ab Bb nr.val nc.val cr cc o i w.val) lvec=q1 T x
def QJ {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (o:Fin k->Fin k) (prefFix prefVal:Fin k->Bool)
  (P S:Finset (Fin k)) (M:Ql k (b+2)) (T:Q6 m) (i:ℕ) (lvec:Q1 m)
  (DP:Fin (2^(b+2))->ℕ):Prop:=
 ∀ x:Q1 (b+2),
  DP (qa x) =
   if (∃ t:Fin (b+2),q3 T ≤ t.val/\t.val < b+2 - S.card/\x t=true) then 0
   else (v9 b Ab Bb nr nc cr cc o prefFix prefVal P M T i lvec x).card
lemma zU {B:ℕ} (d:ℕ) (fl:Fin (2^B)->Fin B->Bool)
  (hhi:∀ x t,d ≤ t.val->fl (qa x) t=false)
  (hdep:∀ x y t,(∀ s:Fin B,d ≤ s.val->x s=y s)->fl (qa x) t=fl (qa y) t)
  (DP:Fin (2^B)->ℕ) (x:Q1 B) :
  ((dF B).foldl (fun D t=>vh B t (fun idx=>fl idx t) D) DP) (qa x) =
   DP (qa (q5 x (fl (qa x)))):=by
 have hgo:∀ k ≤ B,∀ y:Q1 B,
   (((dF B).take k).foldl (fun D t=>vh B t (fun idx=>fl idx t) D) DP) (qa y) =
   DP (qa (fun s=>if s.val < k then xor (y s) (fl (qa y) s) else y s)):=by
  intro k;induction k with
  | zero=>intro _ y;simp
  | succ k ih=>
   intro hk y
   have htake:(dF B).take (k+1)=(dF B).take k ++ [⟨k,hk⟩]:=by
    rw [dJ (by simp;omega)];simp
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   dsimp only [vh]
   set tk:Fin B:=⟨k,hk⟩
   by_cases hfl:fl (qa y) tk=true
   ·rw [if_pos hfl]
    have hlt:k < d:=by by_contra hge;have:=hhi y tk (by dsimp [tk];omega);rw [hfl] at this;exact Bool.false_ne_true this.symm
    have hfp:jw (qa y) tk=qa (v6 tk y):=by simp [jw,vK]
    rw [hfp,ih (Nat.le_of_succ_le hk)]
    congr 2;funext s
    have hfl_eq:fl (qa (v6 tk y)) s=fl (qa y) s:=
     hdep _ _ s (fun s' hs'=>by
      have hne:s' ≠ tk:=fun e=>by subst e;dsimp [tk] at hs';omega
      simp [v6,hne])
    rw [hfl_eq]
    by_cases hls:s.val < k
    ·have hne:s ≠ tk:=fun e=>by subst e;dsimp [tk] at hls;omega
     simp [hls,show s.val < k+1 by omega,v6,hne]
    ·by_cases heq:s=tk
     ·subst heq;simp [tk,hfl,v6]
     ·have hge:¬ s.val < k+1:=by have:s.val ≠ k:=fun e=>heq (Fin.ext e);omega
      simp [hls,hge,v6,heq]
   ·have hflf:fl (qa y) tk=false:=Bool.eq_false_iff.mpr hfl
    rw [if_neg hfl,ih (Nat.le_of_succ_le hk)]
    congr 2;funext s
    by_cases hls:s.val < k
    ·simp [hls,show s.val < k+1 by omega]
    ·by_cases heq:s=tk
     ·subst heq;simp [tk,hflf]
     ·have hge:¬ s.val < k+1:=by have:s.val ≠ k:=fun e=>heq (Fin.ext e);omega
      simp [hls,hge]
 have hm:=hgo B le_rfl x
 rw [show (dF B).take B=dF B by simp] at hm
 rw [hm];congr 2;funext s;simp [q5]
lemma yu {k:ℕ} (w:Fin (2^k)) (z:Fin k) :
  let w':Fin (2^k):=⟨w.val ^^^ 2^z.val,Nat.xor_lt_two_pow w.isLt (Nat.pow_lt_pow_right (by omega) z.isLt)⟩
  (∀ z':Fin k,w'.val.testBit z'.val=if z'=z then !(w.val.testBit z.val) else w.val.testBit z'.val) /\
  (w'.val ^^^ 2^z.val=w.val):=by
 dsimp only
 refine ⟨fun z'=>?_,?_⟩
 ·rw [Nat.testBit_xor,Nat.testBit_two_pow]
  by_cases heq:z'=z
  ·subst heq;simp
  ·have hne:z.val ≠ z'.val:=fun e=>heq (Fin.ext e.symm)
   simp [heq,hne]
 ·apply Nat.eq_of_testBit_eq;intro t;simp [Nat.testBit_xor]
lemma z7 {k r m b:ℕ} (hk:0 < k) (hr:4 ≤ r)
  (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k)) (cr cc:Fin r->Fin (2^k))
  (y:Q1 m) {o:Fin k->Fin k} (ho:Function.Bijective o)
  (hw:qU r Ab Bb o ≤ b) (prefFix prefVal:Fin k->Bool) :
  qX b Ab Bb nr nc cr cc y o prefFix prefVal =
   ((Finset.univ:Finset (Fin (2^k))).filter
    (fun w:Fin (2^k)=>v4 k r m Ab Bb nr.val nc.val cr cc w.val=y /\
     ∀ z:Fin k,prefFix z=true->w.val.testBit z.val=prefVal z)).card:=by
 set B:=b+2
 by_cases hok:jT Ab Bb y o=true
 ·simp only [qX,hok,↓reduceIte]
  have hmain:∀ t ≤ k,
    let DPt:=((dF k).take t).foldl (fun D i=>zD b Ab Bb nr nc cr cc y o prefFix prefVal i D)
     (fun idx=>if idx.val=0 then 1 else 0)
    let Mt:=qt r b Ab Bb o t
    QA Mt (Q5 r Ab Bb o t) /\
    QJ b Ab Bb nr nc cr cc o prefFix prefVal
     (qi r Ab Bb (Qb o t)) (Q5 r Ab Bb o t) Mt (vL Ab Bb o t) t (qF Ab Bb y o t) DPt:=by
   intro t
   induction t with
   | zero=>
    intro _
    simp only [List.take_zero,List.foldl_nil,qt,QV,dm Ab Bb y ho hok]
    refine ⟨gW k B,fun x=>?_⟩
    have h0rk:=gu Ab Bb o
    have h0rec:q1 (vL Ab Bb o 0) x=q2 m:=by
     have:=(qg (vL Ab Bb o 0) (vO Ab Bb o 0).1 (by omega)).2.2.2.1 x
     have hbot:q6 (vL Ab Bb o 0)=⊥:=by
      rw [← Submodule.finrank_eq_zero (R:=ZMod 2),qo (vO Ab Bb o 0).1,h0rk]
     rw [hbot,Submodule.mem_bot] at this
     exact v7 (this.trans (qh m).symm)
    have hpack0:(qa x).val=0 ↔ ∀ t:Fin B,x t=false:=by
     constructor
     ·intro h0 t
      have h1:=vK x;rw [show qa x=⟨0,Nat.two_pow_pos B⟩ from Fin.ext h0] at h1
      have:=congrFun h1 t;simp [v8] at this;exact this
     ·intro hall
      change qu x=0;unfold qu
      exact Finset.sum_eq_zero fun t _=>by simp [hall t]
    dsimp only
    by_cases hall0:∀ t:Fin B,x t=false
    ·have hno:¬ ∃ t:Fin B,q3 (vL Ab Bb o 0) ≤ t.val/\t.val < B - (∅:Finset (Fin k)).card/\x t=true:=by
      rintro ⟨t,_,_,ht⟩;rw [hall0 t] at ht;exact Bool.false_ne_true ht
     rw [if_pos (hpack0.mpr hall0),if_neg hno]
     have hsing:v9 b Ab Bb nr nc cr cc o prefFix prefVal
       (qi r Ab Bb (Qb o 0)) (fun _ _=>false) (vL Ab Bb o 0) 0 (q2 m) x={⟨0,Nat.two_pow_pos k⟩}:=by
      ext w;simp only [v9,dK,dL,true_and,Finset.mem_singleton,
       QI,qi,Finset.biUnion_empty,Finset.notMem_empty,not_false_eq_true,forall_true_left,
       false_implies,Bool.false_eq_true,gw,h0rec]
      constructor
      ·rintro ⟨hz,_,_,_⟩
       apply Fin.ext;apply Nat.eq_of_testBit_eq;intro q
       by_cases hq:q < k
       ·simpa using hz ⟨q,hq⟩
       ·rw [Nat.testBit_lt_two_pow (w.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),Nat.zero_testBit]
      ·rintro rfl;refine ⟨fun _=>by simp,fun _=>trivial,fun _ _=>trivial,?_⟩
       funext q;simp [q5,q2]
     rw [hsing,Finset.card_singleton]
    ·have hex:∃ t:Fin B,q3 (vL Ab Bb o 0) ≤ t.val/\t.val < B - (∅:Finset (Fin k)).card/\x t=true:=by
      push Not at hall0;obtain ⟨t,ht⟩:=hall0
      exact ⟨t,by omega,by simp [B],by cases h:x t <;> simp_all⟩
     rw [if_neg (fun h0=>hall0 (hpack0.mp h0)),if_pos hex]
   | succ t ih=>
    intro ht
    obtain ⟨hM_in,hDP_in⟩:=ih (Nat.le_of_succ_le ht)
    set i:Fin k:=⟨t,ht⟩
    have hiv:i.val=t:=rfl
    have htake:(dF k).take (t+1)=(dF k).take t ++ [i]:=by
     rw [dJ (by simp;omega)];simp [i]
    dsimp only
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    have hM_step:qt r b Ab Bb o (t+1) =
      vN r b Ab Bb o i (qB r b Ab Bb o i (qt r b Ab Bb o t)):=by
     unfold qt;rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [hM_step]
    set Min:=qt r b Ab Bb o t
    set DP0:=((dF k).take t).foldl (fun D j=>zD b Ab Bb nr nc cr cc y o prefFix prefVal j D)
     (fun idx=>if idx.val=0 then 1 else 0)
    set TM:=j7 Ab Bb o i
    set Ti0:=vL Ab Bb o t
    set Ti1:=vL Ab Bb o (t+1)
    have hroom:(Qi r Ab Bb o i).card+q3 TM ≤ B:=d6 Ab Bb hw i
    have hEM:=(yG Ab Bb o i).1
    have hETi0:=(vO Ab Bb o t).1
    have hETi1:=(vO Ab Bb o (t+1)).1
    obtain ⟨hsub0,hsub1,hAinM,hBinM,hdyInM⟩:=gv Ab Bb y ho hok i
    have hBM:q3 TM ≤ B:=by omega
    have hF_sub_A:Q5 r Ab Bb o t ⊆ Qi r Ab Bb o i:=Finset.subset_union_left
    have hF1_sub_A:Q5 r Ab Bb o (t+1) ⊆ Qi r Ab Bb o i:=QG r Ab Bb o i
    have hFcard:(Q5 r Ab Bb o t).card ≤ (Qi r Ab Bb o i).card:=Finset.card_le_card hF_sub_A
    have hF1card:(Q5 r Ab Bb o (t+1)).card ≤ (Qi r Ab Bb o i).card:=Finset.card_le_card hF1_sub_A
    have hBU0:q3 Ti0 ≤ q3 TM:=by
     rw [← qo hETi0,← qo hEM];exact Submodule.finrank_mono hsub0
    have hBU1:q3 Ti1 ≤ q3 TM:=by
     rw [← qo hETi1,← qo hEM];exact Submodule.finrank_mono hsub1
    set G_in:=qk Ti0 TM B
    obtain ⟨hGin_inv,hGin_hi,hGin_rec,hGin_iff⟩:=jK hETi0 hEM hsub0 hBM
    set DP1:=jZ G_in DP0
    have hDP1:QJ b Ab Bb nr nc cr cc o prefFix prefVal
      (qi r Ab Bb (Qb o t)) (Q5 r Ab Bb o t) Min TM t (qF Ab Bb y o t) DP1:=by
     intro x
     dsimp only [DP1]
     rw [zx hGin_inv DP0 x]
     set u:=qT (j1 G_in) x
     have hGu:qT G_in u=x:=by rw [← jr,(jF hGin_inv).1,yj]
     have hu_hi:∀ s:Fin B,q3 TM ≤ s.val->u s=x s:=fun s hs=>by
      rw [← hGu,hGin_hi u s hs]
     rw [hDP_in u]
     by_cases hgapM:∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Q5 r Ab Bb o t).card/\x s=true
     ·rw [if_pos hgapM]
      obtain ⟨s,hs1,hs2,hs3⟩:=hgapM
      rw [if_pos ⟨s,by omega,hs2,by rw [hu_hi s hs1];exact hs3⟩]
     ·rw [if_neg hgapM]
      by_cases hgapU:∃ s:Fin B,q3 Ti0 ≤ s.val/\s.val < B - (Q5 r Ab Bb o t).card/\u s=true
      ·rw [if_pos hgapU]
       have hnot_in:q4 (q1 TM x)∉q6 Ti0:=by
        intro hin
        have hu0:=(hGin_iff x).mp hin
        obtain ⟨s,hs1,hs2,hs3⟩:=hgapU
        by_cases hsM:s.val < q3 TM
        ·have huf:u s=false:=hu0 s hs1 hsM
         rw [huf] at hs3;exact Bool.false_ne_true hs3
        ·exact hgapM ⟨s,by omega,hs2,by rw [← hu_hi s (by omega)];exact hs3⟩
       symm;unfold v9;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
       intro w _ ⟨_,_,_,hrep⟩
       apply hnot_in;rw [← hrep,qE,(vO Ab Bb o t).2]
       have hL:q4 (v5 k r m Ab Bb nr.val nc.val cr cc o t w.val)+q4 (qF Ab Bb y o t)∈qw Ab Bb (Qb o t):=
        Submodule.add_mem _ (jS _ _ _ _ _ _ _ _ (Nat.le_of_succ_le ht)) (yI Ab Bb y ho hok t).1
       have hR:q4 (v5 k r m Ab Bb nr.val nc.val cr cc o t w.val)+q4 (qF Ab Bb y o t)∈qw Ab Bb (Qq o t):=by
        have hm:=(qg TM hEM hBM).2.2.2.1 x
        rw [← hrep,qE,(yG Ab Bb o i).2] at hm
        exact hm.2
       exact ⟨hL,hR⟩
      ·rw [if_neg hgapU]
       have hu_mid:∀ s:Fin B,q3 Ti0 ≤ s.val->s.val < q3 TM->u s=false:=by
        intro s hs1 hs2
        by_contra hne;apply hgapU
        exact ⟨s,hs1,by omega,by cases h:u s <;> simp_all⟩
       have hrec_eq:q1 Ti0 u=q1 TM x:=by
        rw [← hGu,hGin_rec u hu_mid]
       congr 1;ext w;simp only [v9,dK,dL,true_and,hrec_eq]
       constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> refine ⟨h1,h2,fun z s hMs=>?_,h4⟩
       ·have hsge:B - (Q5 r Ab Bb o t).card ≤ s.val:=by
         have hused:=hM_in.2.2.2.2 s
         have:q7 Min s=true:=by simp [q7];exact ⟨z,hMs⟩
         rw [hused] at this;exact of_decide_eq_true this
        rw [← hu_hi s (by omega)];exact h3 z s hMs
       ·have hsge:B - (Q5 r Ab Bb o t).card ≤ s.val:=by
         have hused:=hM_in.2.2.2.2 s
         have:q7 Min s=true:=by simp [q7];exact ⟨z,hMs⟩
         rw [hused] at this;exact of_decide_eq_true this
        rw [hu_hi s (by omega)];exact h3 z s hMs
    let introSet (u:ℕ):Finset (Fin k):=
     Finset.univ.filter fun z:Fin k=>z.val < u/\z∈qq r Ab Bb (o i)/\z∉Q5 r Ab Bb o t
    let st2At (u:ℕ):=
     ((dF k).take u).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
      let cond:=decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o t)
      (qn st.1 z cond,qY B cond (qO (q7 st.1)) (prefFix z) (prefVal z) st.2))
      (Min,DP1)
    have hst2_M:∀ u ≤ k,(st2At u).1 =
      ((dF k).take u).foldl (fun Mc z=>
       qn Mc z (decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o t))) Min:=by
     intro u;induction u with
     | zero=>intro _;rfl
     | succ u ihu=>
      intro hu
      have htu:(dF k).take (u+1)=(dF k).take u ++ [⟨u,hu⟩]:=by
       rw [dJ (by simp;omega)];simp
      dsimp only [st2At];rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil,
       List.foldl_append,List.foldl_cons,List.foldl_nil,ihu (Nat.le_of_succ_le hu)]
    have hstep2:∀ u ≤ k,
      QA (st2At u).1 (Q5 r Ab Bb o t∪introSet u) /\
      QJ b Ab Bb nr nc cr cc o prefFix prefVal
       (qi r Ab Bb (Qb o t)∪introSet u) (Q5 r Ab Bb o t∪introSet u)
       (st2At u).1 TM t (qF Ab Bb y o t) (st2At u).2:=by
     intro u;induction u with
     | zero=>
      intro _
      have h0:introSet 0=∅:=by ext z;simp [introSet]
      simpa [st2At,h0] using ⟨hM_in,hDP1⟩
     | succ u ihu=>
      intro hu
      obtain ⟨hMu,hDPu⟩:=ihu (Nat.le_of_succ_le hu)
      set zu:Fin k:=⟨u,hu⟩
      have htu:(dF k).take (u+1)=(dF k).take u ++ [zu]:=by
       rw [dJ (by simp;omega)];simp [zu]
      set cond:=decide (zu∈qq r Ab Bb (o i))&&!decide (zu∈Q5 r Ab Bb o t)
      have hst2_step:st2At (u+1) =
        (qn (st2At u).1 zu cond,qY B cond (qO (q7 (st2At u).1)) (prefFix zu) (prefVal zu) (st2At u).2):=by
       change ((dF k).take (u+1)).foldl _ _=_
       rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil]
      by_cases hc:cond=true
      ·have hzu_sc:zu∈qq r Ab Bb (o i):=by simp [cond] at hc;exact hc.1
       have hzu_nF:zu∉Q5 r Ab Bb o t:=by simp [cond] at hc;exact hc.2
       have hzu_nP:zu∉qi r Ab Bb (Qb o t):=fun h=>
        hzu_nF ((jP r Ab Bb o i hzu_sc).mp h)
       have hzu_nS:zu∉Q5 r Ab Bb o t∪introSet u:=by
        simp only [Finset.mem_union,introSet,dK,dL,true_and,not_or]
        exact ⟨hzu_nF,fun h=>by dsimp [zu] at h;omega⟩
       have hzu_nPu:zu∉qi r Ab Bb (Qb o t)∪introSet u:=by
        simp only [Finset.mem_union,introSet,dK,dL,true_and,not_or]
        exact ⟨hzu_nP,fun h=>by dsimp [zu] at h;omega⟩
       have hSu_sub:Q5 r Ab Bb o t∪introSet u ⊆ Qi r Ab Bb o i:=by
        intro z hz;rw [Finset.mem_union] at hz
        rcases hz with h1 | h2
        ·exact Finset.mem_union_left _ h1
        ·exact Finset.mem_union_right _ (Finset.mem_filter.mp h2).2.2.1
       have hS_lt:(Q5 r Ab Bb o t∪introSet u).card < B:=by
        have hss:Q5 r Ab Bb o t∪introSet u ⊂ Qi r Ab Bb o i:=by
         rw [Finset.ssubset_iff_subset_ne];refine ⟨hSu_sub,fun he=>hzu_nS (he▸Finset.mem_union_right _ hzu_sc)⟩
        have:=Finset.card_lt_card hss;omega
       have hins_eq:Q5 r Ab Bb o t∪introSet (u+1)=insert zu (Q5 r Ab Bb o t∪introSet u):=by
        ext z;simp only [Finset.mem_union,introSet,dK,dL,true_and,Finset.mem_insert]
        constructor
        ·rintro (hF | ⟨hlt,hsc,hnF⟩)
         ·right;left;exact hF
         ·by_cases hlt':z.val < u
          ·right;right;exact ⟨hlt',hsc,hnF⟩
          ·left;exact Fin.ext (by dsimp [zu];omega)
        ·rintro (rfl | hF | ⟨hlt,hsc,hnF⟩)
         ·right;exact ⟨by dsimp [zu];omega,hzu_sc,hzu_nF⟩
         ·left;exact hF
         ·right;exact ⟨by omega,hsc,hnF⟩
       have hPins_eq:qi r Ab Bb (Qb o t)∪introSet (u+1)=insert zu (qi r Ab Bb (Qb o t)∪introSet u):=by
        ext z;simp only [Finset.mem_union,introSet,dK,dL,true_and,Finset.mem_insert]
        constructor
        ·rintro (hP | ⟨hlt,hsc,hnF⟩)
         ·right;left;exact hP
         ·by_cases hlt':z.val < u
          ·right;right;exact ⟨hlt',hsc,hnF⟩
          ·left;exact Fin.ext (by dsimp [zu];omega)
        ·rintro (rfl | hP | ⟨hlt,hsc,hnF⟩)
         ·right;exact ⟨by dsimp [zu];omega,hzu_sc,hzu_nF⟩
         ·left;exact hP
         ·right;exact ⟨by omega,hsc,hnF⟩
       obtain ⟨hoh,hMu'⟩:=gI hMu hzu_nS hS_lt
       set sNew:Fin B:=⟨B - 1 - (Q5 r Ab Bb o t∪introSet u).card,by omega⟩
       have hcard_ins:(Q5 r Ab Bb o t∪introSet (u+1)).card=(Q5 r Ab Bb o t∪introSet u).card+1:=by
        rw [hins_eq,Finset.card_insert_of_notMem hzu_nS]
       have hsNew_ge:q3 TM ≤ sNew.val:=by
        have hss:(Q5 r Ab Bb o t∪introSet u).card+1 ≤ (Qi r Ab Bb o i).card:=by
         rw [← Finset.card_insert_of_notMem hzu_nS,← hins_eq]
         apply Finset.card_le_card;intro z hz;rw [Finset.mem_union] at hz
         rcases hz with h1 | h2
         ·exact Finset.mem_union_left _ h1
         ·exact Finset.mem_union_right _ (Finset.mem_filter.mp h2).2.2.1
        dsimp [sNew];omega
       rw [hst2_step,hc]
       refine ⟨hins_eq▸hMu',fun x=>?_⟩
       have hcond_fold:qY B true (qO (q7 (st2At u).1)) (prefFix zu) (prefVal zu) (st2At u).2 =
         jm B sNew (prefFix zu) (prefVal zu) (st2At u).2:=by
        unfold qY;simp only [Bool.true_and,hoh,dG]
        exact j4 sNew (fun s D=>jm B s (prefFix zu) (prefVal zu) D) _
       rw [hcond_fold]
       dsimp only [jm]
       rw [vK]
       set x0:Q1 B:=if x sNew=true then v6 sNew x else x
       have hx0_pack:(if x sNew=true then jw (qa x) sNew else qa x)=qa x0:=by
        dsimp [x0];split_ifs <;> simp [jw,vK]
       have hx0_sNew:x0 sNew=false:=by dsimp [x0];cases h:x sNew <;> simp [h,v6]
       have hx0_other:∀ s:Fin B,s ≠ sNew->x0 s=x s:=fun s hs=>by
        dsimp [x0];split_ifs <;> simp [v6,hs]
       have hrec_x0:q1 TM x0=q1 TM x:=
        qx hEM hBM (fun s hs=>hx0_other s (fun e=>by
         subst e;change sNew.val < q3 TM at hs;omega))
       rw [hx0_pack,hDPu x0]
       have hgap_iff:(∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Q5 r Ab Bb o t∪introSet u).card/\x0 s=true) ↔
         (∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Q5 r Ab Bb o t∪introSet (u+1)).card/\x s=true):=by
        rw [hcard_ins]
        constructor
        ·rintro ⟨s,hs1,hs2,hs3⟩
         have hne:s ≠ sNew:=fun e=>by subst e;rw [hx0_sNew] at hs3;exact Bool.false_ne_true hs3
         have hval:s.val ≠ B - 1 - (Q5 r Ab Bb o t∪introSet u).card:=fun e=>hne (Fin.ext e)
         exact ⟨s,hs1,by omega,by rw [← hx0_other s hne];exact hs3⟩
        ·rintro ⟨s,hs1,hs2,hs3⟩
         have hne:s ≠ sNew:=fun e=>by subst e;dsimp [sNew] at hs2;omega
         exact ⟨s,hs1,by omega,by rw [hx0_other s hne];exact hs3⟩
       by_cases hgap:∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Q5 r Ab Bb o t∪introSet (u+1)).card/\x s=true
       ·rw [if_pos hgap,if_pos (hgap_iff.mpr hgap)];split_ifs <;> rfl
       ·rw [if_neg hgap,if_neg (fun h=>hgap (hgap_iff.mp h))]
        by_cases hfix_bad:prefFix zu=true/\x sNew ≠ prefVal zu
        ·rw [if_pos hfix_bad.1,if_neg hfix_bad.2]
         symm;unfold v9;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
         intro w _ ⟨_,h2,h3,_⟩
         have hmemP:zu∈qi r Ab Bb (Qb o t)∪introSet (u+1):=by rw [hPins_eq];exact Finset.mem_insert_self _ _
         have h1':=h2 zu hmemP hfix_bad.1
         have h2':=h3 zu sNew (by simp [qn,hoh])
         exact hfix_bad.2 (h2'.symm.trans h1')
        ·have hkeep:(if prefFix zu=true then if x sNew=prefVal zu then
           (v9 b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o t)∪introSet u)
            (st2At u).1 TM t (qF Ab Bb y o t) x0).card else 0
           else (v9 b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o t)∪introSet u)
            (st2At u).1 TM t (qF Ab Bb y o t) x0).card) =
           (v9 b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o t)∪introSet u)
            (st2At u).1 TM t (qF Ab Bb y o t) x0).card:=by
          by_cases hf:prefFix zu=true
          ·have heq:x sNew=prefVal zu:=by by_contra hne;exact hfix_bad ⟨hf,hne⟩
           simp [hf,heq]
          ·simp [hf]
         rw [hkeep]
         refine Finset.card_bij (fun (w:Fin (2^k)) _=>
          if x sNew=true then ⟨w.val ^^^ 2^zu.val,Nat.xor_lt_two_pow w.isLt (Nat.pow_lt_pow_right (by omega) zu.isLt)⟩ else w) ?_ ?_ ?_
         ·intro w hw
          simp only [v9,dK,dL,true_and] at hw ⊢
          obtain ⟨hw1,hw2,hw3,hw4⟩:=hw
          have hwzu0:w.val.testBit zu.val=false:=hw1 zu hzu_nPu
          set w':Fin (2^k):=if x sNew=true then ⟨w.val ^^^ 2^zu.val,Nat.xor_lt_two_pow w.isLt (Nat.pow_lt_pow_right (by omega) zu.isLt)⟩ else w
          have hw'_bit:∀ z':Fin k,w'.val.testBit z'.val=if z'=zu then x sNew else w.val.testBit z'.val:=by
           intro z';dsimp [w']
           by_cases hxs:x sNew=true
           ·rw [if_pos hxs,(yu w zu).1 z'];split_ifs <;> simp [hwzu0,hxs]
           ·have hxsf:x sNew=false:=Bool.eq_false_iff.mpr hxs
            rw [if_neg hxs]
            split_ifs with e
            ·subst e;exact hwzu0.trans hxsf.symm
            ·rfl
          have hrep_eq:v5 k r m Ab Bb nr.val nc.val cr cc o t w'.val=v5 k r m Ab Bb nr.val nc.val cr cc o t w.val:=
           vM hk hr Ab Bb nr.isLt nc.isLt cr cc o (Nat.le_of_succ_le ht) w'.isLt w.isLt fun z hz=>by
            have hne:z ≠ zu:=fun e=>hzu_nP (e▸hz)
            rw [hw'_bit z,if_neg hne]
          refine ⟨fun z hz=>?_,fun z hz hpf=>?_,fun z s hMs=>?_,?_⟩
          ·have hne:z ≠ zu:=fun e=>hz (by rw [hPins_eq,e];exact Finset.mem_insert_self _ _)
           have hnotu:z∉qi r Ab Bb (Qb o t)∪introSet u:=fun h=>hz (by rw [hPins_eq];exact Finset.mem_insert_of_mem h)
           rw [hw'_bit z,if_neg hne];exact hw1 z hnotu
          ·rw [hPins_eq,Finset.mem_insert] at hz
           rcases hz with rfl | hzu'
           ·rw [hw'_bit zu,if_pos rfl];by_contra hne;exact hfix_bad ⟨hpf,hne⟩
           ·have hne:z ≠ zu:=fun e=>hzu_nPu (e▸hzu')
            rw [hw'_bit z,if_neg hne];exact hw2 z hzu' hpf
          ·simp only [qn,↓reduceIte,hoh] at hMs
           by_cases ez:z=zu
           ·subst ez;simp only [↓reduceIte,dG] at hMs;rw [hMs,hw'_bit zu,if_pos rfl]
           ·simp only [ez,↓reduceIte] at hMs
            have hs_ne:s ≠ sNew:=by
             intro e;subst e
             have hu':q7 (st2At u).1 sNew=true:=by simp [q7];exact ⟨z,hMs⟩
             rw [hMu.2.2.2.2 sNew] at hu';simp only [dG,sNew] at hu';omega
            rw [hw'_bit z,if_neg ez,hw3 z s hMs,hx0_other s hs_ne]
          ·rw [hrep_eq,hw4,hrec_x0]
         ·intro w1 _ w2 _ heq
          by_cases hxs:x sNew=true
          ·simp only [hxs,↓reduceIte] at heq
           apply Fin.ext
           have h1:=congrArg (fun a:Fin (2^k)=>a.val ^^^ 2^zu.val) heq
           dsimp only at h1;rw [(yu w1 zu).2,(yu w2 zu).2] at h1;exact h1
          ·simpa [hxs] using heq
         ·intro w' hw'
          simp only [v9,dK,dL,true_and] at hw'
          obtain ⟨hw1,hw2,hw3,hw4⟩:=hw'
          have hw'zu:w'.val.testBit zu.val=x sNew:=hw3 zu sNew (by simp [qn,hoh])
          set w:Fin (2^k):=if x sNew=true then ⟨w'.val ^^^ 2^zu.val,Nat.xor_lt_two_pow w'.isLt (Nat.pow_lt_pow_right (by omega) zu.isLt)⟩ else w'
          have hw_bit:∀ z':Fin k,w.val.testBit z'.val=if z'=zu then false else w'.val.testBit z'.val:=by
           intro z';dsimp [w]
           by_cases hxs:x sNew=true
           ·rw [if_pos hxs,(yu w' zu).1 z'];split_ifs <;> simp [hw'zu,hxs]
           ·have hxsf:x sNew=false:=Bool.eq_false_iff.mpr hxs
            rw [if_neg hxs]
            split_ifs with e
            ·subst e;rw [hw'zu,hxsf]
            ·rfl
          have hrep_eq:v5 k r m Ab Bb nr.val nc.val cr cc o t w.val=v5 k r m Ab Bb nr.val nc.val cr cc o t w'.val:=
           vM hk hr Ab Bb nr.isLt nc.isLt cr cc o (Nat.le_of_succ_le ht) w.isLt w'.isLt fun z hz=>by
            have hne:z ≠ zu:=fun e=>hzu_nP (e▸hz)
            rw [hw_bit z,if_neg hne]
          refine ⟨w,Finset.mem_filter.mpr ⟨dL w,?_,?_,?_,?_⟩,?_⟩
          ·intro z hz;by_cases ez:z=zu
           ·rw [ez,hw_bit zu,if_pos rfl]
           ·rw [hw_bit z,if_neg ez];exact hw1 z (by rw [hPins_eq,Finset.mem_insert];push Not;exact ⟨ez,hz⟩)
          ·intro z hz hpf
           have hne:z ≠ zu:=fun e=>hzu_nPu (e▸hz)
           rw [hw_bit z,if_neg hne];exact hw2 z (by rw [hPins_eq];exact Finset.mem_insert_of_mem hz) hpf
          ·intro z s hMs
           have hne:z ≠ zu:=fun e=>by subst e;rw [hMu.2.2.1 zu hzu_nS] at hMs;simp at hMs
           have hs_ne:s ≠ sNew:=by
            intro e;subst e
            have hu':q7 (st2At u).1 sNew=true:=by simp [q7];exact ⟨z,hMs⟩
            rw [hMu.2.2.2.2 sNew] at hu';simp only [dG,sNew] at hu';omega
           rw [hw_bit z,if_neg hne,hx0_other s hs_ne]
           exact hw3 z s (by simp [qn,hne,hMs])
          ·rw [hrep_eq,hw4,hrec_x0]
          ·dsimp [w];by_cases hxs:x sNew=true
           ·simp only [hxs,↓reduceIte];apply Fin.ext;exact (yu w' zu).2
           ·simp [hxs]
      ·have hcf:cond=false:=Bool.eq_false_iff.mpr hc
       have heq_set:introSet (u+1)=introSet u:=by
        ext z;simp only [introSet,dK,dL,true_and]
        constructor
        ·rintro ⟨hlt,hsc,hnF⟩;refine ⟨?_,hsc,hnF⟩
         by_contra hge;have ez:z=zu:=Fin.ext (by dsimp [zu];omega)
         subst ez;exact hc (by simp [cond,hsc,hnF])
        ·rintro ⟨hlt,hsc,hnF⟩;exact ⟨by omega,hsc,hnF⟩
       rw [hst2_step,hcf,heq_set]
       have hnoop:qY B false (qO (q7 (st2At u).1)) (prefFix zu) (prefVal zu) (st2At u).2=(st2At u).2:=by
        unfold qY;simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte];exact yU _ _
       dsimp only [qn];rw [hnoop];exact ⟨hMu,hDPu⟩
    obtain ⟨hM_mid0,hDP2_0⟩:=hstep2 k le_rfl
    have hktake:(dF k).take k=dF k:=by simp
    have hintro_full:Q5 r Ab Bb o t∪introSet k=Qi r Ab Bb o i:=by
     ext z;simp only [Finset.mem_union,introSet,dK,dL,true_and,Qi,hiv]
     by_cases hF:z∈Q5 r Ab Bb o t <;> simp [hF]
    have hP_full:qi r Ab Bb (Qb o t)∪introSet k=qi r Ab Bb (Qb o (t+1)):=by
     rw [← hiv,zy r Ab Bb o i]
     ext z;simp only [Finset.mem_union,introSet,dK,dL,true_and,hiv]
     by_cases hsc:z∈qq r Ab Bb (o i)
     ·have hiff:=jP r Ab Bb o i hsc
      rw [hiv] at hiff
      by_cases hF:z∈Q5 r Ab Bb o t <;> simp [hsc,hF,hiff]
     ·simp [hsc]
    rw [hintro_full] at hM_mid0 hDP2_0
    rw [hP_full] at hDP2_0
    have hM_mid_eq:(st2At k).1=qB r b Ab Bb o i Min:=by
     have:=hst2_M k le_rfl;rwa [hktake] at this
    set Mmid:=qB r b Ab Bb o i Min
    rw [hM_mid_eq] at hM_mid0 hDP2_0
    set cdy:=qf TM (q5 (qF Ab Bb y o t) (qF Ab Bb y o (t+1))) B
    set cA:=qf TM (Ab (o i)) B
    set cB:=qf TM (Bb (o i)) B
    set fl:Fin (2^B)->Fin B->Bool:=fun idx s=>
     xor (cdy s) (xor (cA s&&jB b Ab Bb nr cr o i idx) (cB s&&jA b Ab Bb nc cc o i idx))
    have hfl_hi:∀ x s,q3 TM ≤ s.val->fl (qa x) s=false:=by
     intro x s hs
     have hge:=(qg TM hEM hBM).1
     simp [fl,cdy,cA,cB,hge _ s hs]
    have hwLoc_dep:∀ x y':Q1 B,(∀ s:Fin B,q3 TM ≤ s.val->x s=y' s) ->
      jL Mmid (fun z=>decide (z∈qq r Ab Bb (o i))) (qa x) =
      jL Mmid (fun z=>decide (z∈qq r Ab Bb (o i))) (qa y'):=by
     intro x y' hag
     unfold jL;congr 1;funext z;simp only [vK]
     congr 1;apply Bool.eq_iff_iff.mpr;simp only [dG]
     constructor <;> rintro ⟨s,hMs,hsx⟩ <;> refine ⟨s,hMs,?_⟩
     ·have hge:B - (Qi r Ab Bb o i).card ≤ s.val:=by
       have hu:=hM_mid0.2.2.2.2 s;have:q7 Mmid s=true:=by simp [q7];exact ⟨z,hMs⟩
       rw [hu] at this;exact of_decide_eq_true this
      rw [← hag s (by omega)];exact hsx
     ·have hge:B - (Qi r Ab Bb o i).card ≤ s.val:=by
       have hu:=hM_mid0.2.2.2.2 s;have:q7 Mmid s=true:=by simp [q7];exact ⟨z,hMs⟩
       rw [hu] at this;exact of_decide_eq_true this
      rw [hag s (by omega)];exact hsx
    have hfl_dep:∀ x y' s,(∀ s':Fin B,q3 TM ≤ s'.val->x s'=y' s')->fl (qa x) s=fl (qa y') s:=by
     intro x y' s hag
     have hw':=hwLoc_dep x y' hag
     dsimp only [Mmid,Min] at hw'
     simp only [fl,jB,jA,hiv,hw']
    set DP3:=(dF B).foldl (fun D s=>vh B s (fun idx=>fl idx s) D) (st2At k).2
    have hDP3:QJ b Ab Bb nr nc cr cc o prefFix prefVal
      (qi r Ab Bb (Qb o (t+1))) (Qi r Ab Bb o i) Mmid TM (t+1) (qF Ab Bb y o (t+1)) DP3:=by
     intro x
     dsimp only [DP3]
     rw [zU (q3 TM) fl hfl_hi hfl_dep (st2At k).2 x,hDP2_0]
     set dvec:=fl (qa x)
     have hgap_iff:(∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Qi r Ab Bb o i).card/\q5 x dvec s=true) ↔
       (∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Qi r Ab Bb o i).card/\x s=true):=by
      constructor <;> rintro ⟨s,hs1,hs2,hs3⟩ <;> exact ⟨s,hs1,hs2,by simpa [q5,dvec,hfl_hi x s hs1] using hs3⟩
     by_cases hgap:∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Qi r Ab Bb o i).card/\x s=true
     ·rw [if_pos hgap,if_pos (hgap_iff.mpr hgap)]
     ·rw [if_neg hgap,if_neg (fun h=>hgap (hgap_iff.mp h))]
      congr 1;ext w;simp only [v9,dK,dL,true_and]
      have hvar_eq:∀ z s,Mmid z s=true->q5 x dvec s=x s:=fun z s hMs=>by
       have hge:B - (Qi r Ab Bb o i).card ≤ s.val:=by
        have hu:=hM_mid0.2.2.2.2 s;have:q7 Mmid s=true:=by simp [q7];exact ⟨z,hMs⟩
        rw [hu] at this;exact of_decide_eq_true this
       simp [q5,dvec,hfl_hi x s (by omega)]
      have hrec_dvec:∀ (h3:∀ z s,Mmid z s=true->w.val.testBit z.val=x s),
        q1 TM dvec=q5 (q5 (qF Ab Bb y o t) (qF Ab Bb y o (t+1)))
         (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i)):=by
       intro h3
       set wLoc:=jL Mmid (fun z=>decide (z∈qq r Ab Bb (o i))) (qa x)
       have hwLoc_lt:wLoc < 2^k:=ya _
       have hwLoc_ag:∀ z∈qq r Ab Bb (o i),wLoc.testBit z.val=w.val.testBit z.val:=by
        intro z hz
        dsimp only [wLoc,jL]
        rw [qb _ z]
        obtain ⟨s,_,hMs⟩:=hM_mid0.2.1 z (Finset.mem_union_right _ hz)
        have hbit:decide (∃ s':Fin (b+2),Mmid z s'=true/\v8 (b+2) (qa x) s'=true)=x s:=by
         apply Bool.eq_iff_iff.mpr;simp only [dG,vK,hMs]
         exact ⟨fun ⟨s',hs',hx'⟩=>hs'▸hx',fun hx'=>⟨s,rfl,hx'⟩⟩
        simp only [hz,decide_true,Bool.true_and,hbit]
        exact (h3 z s (by rw [hMs];simp)).symm
       have hterm_eq:qR k r m Ab Bb nr.val nc.val cr cc w.val (o i) =
         q5 (if jB b Ab Bb nr cr o i (qa x)=true then Ab (o i) else q2 m)
             (if jA b Ab Bb nc cc o i (qa x)=true then Bb (o i) else q2 m):=by
        rw [← jx hk hr Ab Bb nr.isLt nc.isLt cr cc (o i) hwLoc_lt w.isLt hwLoc_ag]
        rfl
       have hcoords_dvec:dvec=qf TM
         (q5 (q5 (qF Ab Bb y o t) (qF Ab Bb y o (t+1)))
          (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))) B:=by
        have hterm_inM:q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))∈q6 TM:=by
         rw [hterm_eq,qE]
         refine Submodule.add_mem _ ?_ ?_
         ·split_ifs
          ·exact hAinM
          ·rw [qh];exact Submodule.zero_mem _
         ·split_ifs
          ·exact hBinM
          ·rw [qh];exact Submodule.zero_mem _
        rw [yY TM hEM hBM hdyInM hterm_inM,hterm_eq]
        have h1_inM:q4 (if jB b Ab Bb nr cr o i (qa x)=true then Ab (o i) else q2 m)∈q6 TM:=by
         split_ifs
         ·exact hAinM
         ·rw [qh];exact Submodule.zero_mem _
        have h2_inM:q4 (if jA b Ab Bb nc cc o i (qa x)=true then Bb (o i) else q2 m)∈q6 TM:=by
         split_ifs
         ·exact hBinM
         ·rw [qh];exact Submodule.zero_mem _
        rw [yY TM hEM hBM h1_inM h2_inM]
        funext s
        have hcf:qf TM (if jB b Ab Bb nr cr o i (qa x)=true then Ab (o i) else q2 m) B s =
          (cA s&&jB b Ab Bb nr cr o i (qa x)):=by
         cases hb':jB b Ab Bb nr cr o i (qa x)
         ·simp [jJ TM hEM hBM,q2]
         ·simp [cA]
        have hct:qf TM (if jA b Ab Bb nc cc o i (qa x)=true then Bb (o i) else q2 m) B s =
          (cB s&&jA b Ab Bb nc cc o i (qa x)):=by
         cases hb':jA b Ab Bb nc cc o i (qa x)
         ·simp [jJ TM hEM hBM,q2]
         ·simp [cB]
        dsimp only [dvec,fl,q5,cdy];rw [hcf,hct]
       rw [hcoords_dvec]
       refine (qg TM hEM hBM).2.1 _ (by
        rw [qE];refine Submodule.add_mem _ hdyInM ?_
        rw [hterm_eq,qE];refine Submodule.add_mem _ ?_ ?_
        ·split_ifs
         ·exact hAinM
         ·rw [qh];exact Submodule.zero_mem _
        ·split_ifs
         ·exact hBinM
         ·rw [qh];exact Submodule.zero_mem _)
      have hrx:=(qg TM hEM hBM).2.2.2.2 x dvec
      constructor
      ·rintro ⟨h1,h2,h3,h4⟩
       have h3':∀ z s,Mmid z s=true->w.val.testBit z.val=x s:=fun z s hMs=>(h3 z s hMs).trans (hvar_eq z s hMs)
       refine ⟨h1,h2,h3',?_⟩
       rw [hrx,hrec_dvec h3'] at h4
       apply v7;rw [zm _ _ _ _ _ _ _ _ ht]
       have h4':=congrArg q4 h4
       simp only [qE] at h4' ⊢
       have hadd:=congrArg (fun v=>v+(q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1)) +
        q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i)))) h4'
       have hl:q4 (v5 k r m Ab Bb nr.val nc.val cr cc o t w.val)+q4 (qF Ab Bb y o t) +
         (q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1))+q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))) =
         q4 (v5 k r m Ab Bb nr.val nc.val cr cc o t w.val)+q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i)) +
         q4 (qF Ab Bb y o (t+1))+(q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o t)):=by abel
       have hr':q4 (q1 TM x)+(q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1)) +
         q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))) +
         (q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1))+q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))) =
         q4 (q1 TM x)+((q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1)) +
          q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))) +
          (q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1)) +
          q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i)))):=by abel
       rw [hl,hr',qM,qM,add_zero,add_zero] at hadd
       exact hadd
      ·rintro ⟨h1,h2,h3,h4⟩
       refine ⟨h1,h2,fun z s hMs=>(h3 z s hMs).trans (hvar_eq z s hMs).symm,?_⟩
       rw [hrx,hrec_dvec h3]
       apply v7;rw [zm _ _ _ _ _ _ _ _ ht] at h4
       have h4':=congrArg q4 h4
       simp only [qE] at h4' ⊢
       have hadd:=congrArg (fun v=>v+(q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1)) +
        q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i)))) h4'
       have hl:q4 (v5 k r m Ab Bb nr.val nc.val cr cc o t w.val)+q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i)) +
         q4 (qF Ab Bb y o (t+1)) +
         (q4 (qF Ab Bb y o t)+q4 (qF Ab Bb y o (t+1))+q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))) =
         q4 (v5 k r m Ab Bb nr.val nc.val cr cc o t w.val)+q4 (qF Ab Bb y o t) +
         (q4 (qF Ab Bb y o (t+1))+q4 (qF Ab Bb y o (t+1))) +
         (q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))+q4 (qR k r m Ab Bb nr.val nc.val cr cc w.val (o i))):=by abel
       rw [hl,qM,qM,add_zero,add_zero] at hadd
       exact hadd
    let remSet (u:ℕ):Finset (Fin k):=
     Qi r Ab Bb o i \ (Finset.univ.filter fun z:Fin k=>z.val < u/\z∈Qi r Ab Bb o i/\z∉Q5 r Ab Bb o (t+1))
    let st4At (u:ℕ):=
     ((dF k).take u).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
      let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (t+1))
      let loOH:=qV (q7 st.1)
      (qA st.1 z cond,qI B cond (st.1 z) loOH (qZ B k cond (st.1 z) st.2)))
      (Mmid,DP3)
    have hst4_M:∀ u ≤ k,(st4At u).1 =
      ((dF k).take u).foldl (fun Mc z=>
       qA Mc z (decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (t+1)))) Mmid:=by
     intro u;induction u with
     | zero=>intro _;rfl
     | succ u ihu=>
      intro hu
      have htu:(dF k).take (u+1)=(dF k).take u ++ [⟨u,hu⟩]:=by
       rw [dJ (by simp;omega)];simp
      dsimp only [st4At];rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil,
       List.foldl_append,List.foldl_cons,List.foldl_nil,ihu (Nat.le_of_succ_le hu)]
    have hstep4:∀ u ≤ k,
      QA (st4At u).1 (remSet u) /\
      QJ b Ab Bb nr nc cr cc o prefFix prefVal
       (qi r Ab Bb (Qb o (t+1))) (remSet u)
       (st4At u).1 TM (t+1) (qF Ab Bb y o (t+1)) (st4At u).2:=by
     intro u;induction u with
     | zero=>
      intro _
      have h0:remSet 0=Qi r Ab Bb o i:=by ext z;simp [remSet]
      simpa [st4At,h0] using ⟨hM_mid0,hDP3⟩
     | succ u ihu=>
      intro hu
      obtain ⟨hMu,hDPu⟩:=ihu (Nat.le_of_succ_le hu)
      set zu:Fin k:=⟨u,hu⟩
      have htu:(dF k).take (u+1)=(dF k).take u ++ [zu]:=by
       rw [dJ (by simp;omega)];simp [zu]
      dsimp only [st4At];rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil]
      set cond:=decide (zu∈Qi r Ab Bb o i)&&!decide (zu∈Q5 r Ab Bb o (t+1))
      by_cases hc:cond=true
      ·have hzu_A:zu∈Qi r Ab Bb o i:=by simp [cond] at hc;exact hc.1
       have hzu_nF:zu∉Q5 r Ab Bb o (t+1):=by simp [cond] at hc;exact hc.2
       have hzu_in:zu∈remSet u:=by
        simp only [remSet,Finset.mem_sdiff,dK,dL,true_and]
        exact ⟨hzu_A,fun h=>by dsimp [zu] at h;omega⟩
       have herase:remSet (u+1)=(remSet u).erase zu:=by
        ext z;simp only [remSet,Finset.mem_sdiff,dK,dL,true_and,Finset.mem_erase]
        constructor
        ·rintro ⟨hA,hnot⟩
         refine ⟨fun ez=>hnot (by rw [ez];exact ⟨by dsimp [zu];omega,hzu_A,hzu_nF⟩),
          hA,fun ⟨hlt,h1,h2⟩=>hnot ⟨by omega,h1,h2⟩⟩
        ·rintro ⟨hne,hA,hnot⟩
         refine ⟨hA,fun ⟨hlt,h1,h2⟩=>hnot ⟨?_,h1,h2⟩⟩
         have:z.val ≠ u:=fun e=>hne (Fin.ext e);omega
       obtain ⟨hlo,hMu',hform⟩:=gr hMu hzu_in
       obtain ⟨sZ,hsZ_ge,hMzu⟩:=hMu.2.1 zu hzu_in
       have hpos:0 < (remSet u).card:=Finset.card_pos.mpr ⟨zu,hzu_in⟩
       set sLo:Fin B:=⟨B - (remSet u).card,by have:=hMu.1;omega⟩
       have hrem_le:(remSet u).card ≤ (Qi r Ab Bb o i).card:=Finset.card_le_card Finset.sdiff_subset
       have hsLo_geM:q3 TM ≤ sLo.val:=by dsimp [sLo];omega
       have hsZ_geM:q3 TM ≤ sZ.val:=by omega
       have hcard_er:(remSet (u+1)).card=(remSet u).card - 1:=by
        rw [herase,Finset.card_erase_of_mem hzu_in]
       rw [hc]
       refine ⟨herase▸hMu',fun x=>?_⟩
       have hsum_eq:qZ B k true ((st4At u).1 zu) (st4At u).2=j9 B k sZ (st4At u).2:=by
        unfold qZ;simp only [Bool.true_and,hMzu,dG]
        exact j4 sZ (fun s D=>j9 B k s D) _
       have hswap_eq:∀ D:Fin (2^B)->ℕ,
         qI B true ((st4At u).1 zu) (qV (q7 (st4At u).1)) D =
         fun idx=>D (vY idx sZ sLo):=by
        intro D;unfold qI
        simp only [Bool.true_and,hMzu,hlo,dI,dG]
        have hinner:∀ u':Fin B,∀ D':Fin (2^B)->ℕ,
          (dF B).foldl (fun D'' v=>if u'=sZ/\v=sLo then (fun idx=>D'' (vY idx u' v)) else D'') D' =
          if u'=sZ then (fun idx=>D' (vY idx sZ sLo)) else D':=by
         intro u' D'
         by_cases hu':u'=sZ
         ·subst hu';simp only [true_and,↓reduceIte]
          exact j4 sLo (fun v D'' idx=>D'' (vY idx u' v)) D'
         ·simp only [hu',false_and,↓reduceIte];exact yU _ _
        have houter:(dF B).foldl (fun D' u'=>
          (dF B).foldl (fun D'' v=>if u'=sZ/\v=sLo then (fun idx=>D'' (vY idx u' v)) else D'') D') D =
          (dF B).foldl (fun D' u'=>if u'=sZ then (fun idx=>D' (vY idx sZ sLo)) else D') D:=by
         congr 1;funext D' u';exact hinner u' D'
        rw [houter]
        exact j4 sZ (fun _ D' idx=>D' (vY idx sZ sLo)) D
       rw [hsum_eq,hswap_eq]
       dsimp only [j9]
       set xs:=j2 sZ sLo x
       have hsw_pack:vY (qa x) sZ sLo=qa xs:=by simp [vY,vK,xs]
       rw [hsw_pack,vK]
       have hxs_sZ:xs sZ=x sLo:=by dsimp [xs,j2];by_cases h:sZ=sLo <;> simp [h]
       have hrec_xs:q1 TM xs=q1 TM x:=
        qx hEM hBM (fun s hs=>by
         change s.val < q3 TM at hs
         have h1:s ≠ sZ:=fun e=>by subst e;omega
         have h2:s ≠ sLo:=fun e=>by subst e;omega
         simp [xs,j2,h1,h2])
       have hrec_xsf:q1 TM (v6 sZ xs)=q1 TM x:=by
        rw [← hrec_xs]
        exact qx hEM hBM (fun s hs=>by
         change s.val < q3 TM at hs
         have h1:s ≠ sZ:=fun e=>by subst e;omega
         simp [v6,h1])
       have hgap_xs:(∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (remSet (u+1)).card/\x s=true) ↔
         x sLo=true\/(∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (remSet u).card/\xs s=true):=by
        rw [hcard_er]
        constructor
        ·rintro ⟨s,hs1,hs2,hs3⟩
         by_cases heq:s=sLo
         ·left;exact heq▸hs3
         ·right;have hlt:s.val < B - (remSet u).card:=by
           have:s.val ≠ B - (remSet u).card:=fun e=>heq (Fin.ext e);omega
          have hneZ:s ≠ sZ:=fun e=>by subst e;omega
          exact ⟨s,hs1,hlt,by simp [xs,j2,hneZ,heq,hs3]⟩
        ·rintro (hloT | ⟨s,hs1,hs2,hs3⟩)
         ·exact ⟨sLo,hsLo_geM,by dsimp [sLo];omega,hloT⟩
         ·have hneZ:s ≠ sZ:=fun e=>by subst e;omega
          have hneL:s ≠ sLo:=fun e=>by subst e;dsimp [sLo] at hs2;omega
          exact ⟨s,hs1,by omega,by simpa [xs,j2,hneZ,hneL] using hs3⟩
       by_cases hgap:∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (remSet (u+1)).card/\x s=true
       ·rw [if_pos hgap]
        rcases hgap_xs.mp hgap with hloT | hgap0
        ·rw [hxs_sZ,hloT];simp
        ·by_cases hxs0:xs sZ=false
         ·rw [if_pos hxs0]
          have hfp:jw (qa xs) sZ=qa (v6 sZ xs):=by simp [jw,vK]
          rw [hfp,hDPu xs,hDPu (v6 sZ xs),if_pos hgap0]
          have hgap1:∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (remSet u).card/\v6 sZ xs s=true:=by
           obtain ⟨s,hs1,hs2,hs3⟩:=hgap0
           have hneZ:s ≠ sZ:=fun e=>by subst e;omega
           exact ⟨s,hs1,hs2,by simp [v6,hneZ,hs3]⟩
          rw [if_pos hgap1];simp
         ·rw [if_neg hxs0]
       ·rw [if_neg hgap]
        have hnot2:=mt hgap_xs.mpr hgap
        push Not at hnot2
        have hloF:x sLo=false:=Bool.eq_false_iff.mpr hnot2.1
        rw [if_pos (hxs_sZ.trans hloF)]
        have hfp:jw (qa xs) sZ=qa (v6 sZ xs):=by simp [jw,vK]
        rw [hfp,hDPu xs,hDPu (v6 sZ xs)]
        have hng0:¬ ∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (remSet u).card/\xs s=true:=by
         rintro ⟨s,hs1,hs2,hs3⟩;exact hnot2.2 s hs1 hs2 hs3
        have hng1:¬ ∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (remSet u).card/\v6 sZ xs s=true:=by
         rintro ⟨s,hs1,hs2,hs3⟩
         have hneZ:s ≠ sZ:=fun e=>by subst e;omega
         exact hnot2.2 s hs1 hs2 (by simpa [v6,hneZ] using hs3)
        rw [if_neg hng0,if_neg hng1]
        set S0:=v9 b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o (t+1))) (st4At u).1 TM (t+1) (qF Ab Bb y o (t+1)) xs
        set S1:=v9 b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o (t+1))) (st4At u).1 TM (t+1) (qF Ab Bb y o (t+1)) (v6 sZ xs)
        set ST:=v9 b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o (t+1))) (qA (st4At u).1 zu true) TM (t+1) (qF Ab Bb y o (t+1)) x
        have hdisj:Disjoint S0 S1:=by
         rw [Finset.disjoint_left];intro w hw0 hw1
         have h0:=(Finset.mem_filter.mp hw0).2.2.2.1 zu sZ (by rw [hMzu];simp)
         have h1:=(Finset.mem_filter.mp hw1).2.2.2.1 zu sZ (by rw [hMzu];simp)
         rw [hxs_sZ,hloF] at h0
         have:v6 sZ xs sZ=true:=by simp [v6,hxs_sZ,hloF]
         rw [this] at h1;rw [h0] at h1;exact Bool.false_ne_true h1
        have hunion:S0∪S1=ST:=by
         have hF:=hform sZ hMzu
         ext w;simp only [Finset.mem_union,S0,S1,ST,v9,dK,dL,true_and,hrec_xs,hrec_xsf]
         have hxs_form:∀ z':Fin k,z' ≠ zu->∀ s:Fin B,(st4At u).1 z' s=true ->
           (s ≠ sZ/\(xs s=x (if s=sLo then sZ else s))/\(v6 sZ xs s=x (if s=sLo then sZ else s))):=by
          intro z' hne s hMs
          have hsne:s ≠ sZ:=fun e=>hne (hMu.2.2.2.1 z' zu s hMs (by rw [hMzu,e];simp))
          refine ⟨hsne,?_,?_⟩
          ·by_cases h:s=sLo
           ·subst h;simp [xs,j2,hsne]
           ·simp [xs,j2,hsne,h]
          ·by_cases h:s=sLo
           ·subst h;simp [v6,xs,j2,hsne]
           ·simp [v6,xs,j2,hsne,h]
         constructor
         ·rintro (⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4⟩) <;> refine ⟨h1,h2,fun z' s hMs=>?_,h4⟩
          ·rw [hF z' s] at hMs
           by_cases ez:z'=zu;· simp [ez] at hMs
           simp only [ez,↓reduceIte] at hMs
           have h5:=h3 z' _ hMs
           have h6:=hxs_form z' ez _ hMs
           rw [h6.2.1] at h5
           by_cases h1':s=sZ
           ·subst h1';simp [show s=sLo->s=sZ from fun _=>rfl] at h5;exact h5
           ·by_cases h2':s=sLo
            ·subst h2';simp [h1'] at h6
            ·simp [h1',h2'] at h5;exact h5
          ·rw [hF z' s] at hMs
           by_cases ez:z'=zu;· simp [ez] at hMs
           simp only [ez,↓reduceIte] at hMs
           have h5:=h3 z' _ hMs
           have h6:=hxs_form z' ez _ hMs
           rw [h6.2.2] at h5
           by_cases h1':s=sZ
           ·subst h1';simp [show s=sLo->s=sZ from fun _=>rfl] at h5;exact h5
           ·by_cases h2':s=sLo
            ·subst h2';simp [h1'] at h6
            ·simp [h1',h2'] at h5;exact h5
         ·rintro ⟨h1,h2,h3,h4⟩
          cases hwz:w.val.testBit zu.val
          ·left;refine ⟨h1,h2,fun z' s hMs=>?_,h4⟩
           by_cases ez:z'=zu
           ·subst ez;rw [hMzu] at hMs;simp only [dG] at hMs;subst hMs
            rw [hwz,hxs_sZ,hloF]
           ·obtain ⟨hsne,hxs_e,_⟩:=hxs_form z' ez s hMs
            rw [hxs_e]
            by_cases hlo':s=sLo
            ·subst hlo';simp only [↓reduceIte]
             exact h3 z' sZ (by rw [hF z' sZ];simp [ez,hMs])
            ·simp only [hlo',↓reduceIte]
             exact h3 z' s (by rw [hF z' s];simp [ez,hsne,hlo',hMs])
          ·right;refine ⟨h1,h2,fun z' s hMs=>?_,h4⟩
           by_cases ez:z'=zu
           ·subst ez;rw [hMzu] at hMs;simp only [dG] at hMs;subst hMs
            rw [hwz];simp [v6,hxs_sZ,hloF]
           ·obtain ⟨hsne,_,hxs_e⟩:=hxs_form z' ez s hMs
            rw [hxs_e]
            by_cases hlo':s=sLo
            ·subst hlo';simp only [↓reduceIte]
             exact h3 z' sZ (by rw [hF z' sZ];simp [ez,hMs])
            ·simp only [hlo',↓reduceIte]
             exact h3 z' s (by rw [hF z' s];simp [ez,hsne,hlo',hMs])
        have hsum_card:S0.card+S1.card=ST.card:=by rw [← Finset.card_union_of_disjoint hdisj,hunion]
        have hST_lt:ST.card < 2^(k+1):=by
         have h1:ST.card ≤ 2^k:=by simpa using Finset.card_le_univ ST
         have h2:0 < 2^k:=Nat.two_pow_pos k
         rw [pow_succ];omega
        rw [hsum_card,Nat.mod_eq_of_lt hST_lt]
      ·have hcf:cond=false:=Bool.eq_false_iff.mpr hc
       have heq_set:remSet (u+1)=remSet u:=by
        ext z;simp only [remSet,Finset.mem_sdiff,dK,dL,true_and]
        constructor
        ·rintro ⟨hA,hnot⟩;exact ⟨hA,fun ⟨hlt,h1,h2⟩=>hnot ⟨by omega,h1,h2⟩⟩
        ·rintro ⟨hA,hnot⟩;refine ⟨hA,fun ⟨hlt,h1,h2⟩=>hnot ⟨?_,h1,h2⟩⟩
         by_contra hge;have ez:z=zu:=Fin.ext (by dsimp [zu];omega)
         subst ez;exact hc (by simp [cond,h1,h2])
       rw [hcf,heq_set]
       have hnoop1:qZ B k false ((st4At u).1 zu) (st4At u).2=(st4At u).2:=by
        unfold qZ;simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte];exact yU _ _
       have hnoop2:qI B false ((st4At u).1 zu) (qV (q7 (st4At u).1)) (st4At u).2=(st4At u).2:=by
        unfold qI;simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte]
        have h1:∀ D:Fin (2^B)->ℕ,(dF B).foldl (fun D' (_:Fin B)=>D') D=D:=fun D=>yU _ _
        simp only [h1]
       change QA (qA (st4At u).1 zu false) (remSet u) /\
        QJ b Ab Bb nr nc cr cc o prefFix prefVal (qi r Ab Bb (Qb o (t+1))) (remSet u)
         (qA (st4At u).1 zu false) TM (t+1) (qF Ab Bb y o (t+1))
         (qI B false ((st4At u).1 zu) (qV (q7 (st4At u).1))
          (qZ B k false ((st4At u).1 zu) (st4At u).2))
       rw [hnoop1,hnoop2];exact ⟨hMu,hDPu⟩
    obtain ⟨hM_out0,hDP4_0⟩:=hstep4 k le_rfl
    have hrem_full:remSet k=Q5 r Ab Bb o (t+1):=by
     ext z;simp only [remSet,Finset.mem_sdiff,dK,dL,true_and]
     constructor
     ·rintro ⟨hA,hnot⟩;by_contra hnF;exact hnot ⟨z.isLt,hA,hnF⟩
     ·intro hF;exact ⟨hF1_sub_A hF,fun h=>h.2.2 hF⟩
    rw [hrem_full] at hM_out0 hDP4_0
    have hM_out_eq:(st4At k).1=vN r b Ab Bb o i Mmid:=by
     have:=hst4_M k le_rfl;rwa [hktake] at this
    set Mout:=vN r b Ab Bb o i Mmid
    rw [hM_out_eq] at hM_out0 hDP4_0
    set G_out:=qk Ti1 TM B
    obtain ⟨hGout_inv,hGout_hi,hGout_rec,hGout_iff⟩:=jK hETi1 hEM hsub1 hBM
    have hGoutInv_inv:Q7 (j1 G_out):=⟨G_out,(jF hGout_inv).2⟩
    have hinv_inv:j1 (j1 G_out)=G_out:=by
     obtain ⟨h1,_⟩:=jF hGoutInv_inv
     obtain ⟨h2,_⟩:=jF hGout_inv
     calc j1 (j1 G_out)=v3 (vT B) (j1 (j1 G_out)):=(yv _).symm
      _=v3 (v3 G_out (j1 G_out)) (j1 (j1 G_out)):=by rw [h2]
      _=v3 G_out (v3 (j1 G_out) (j1 (j1 G_out))):=jU _ _ _
      _=G_out:=by rw [h1,vU]
    refine ⟨hM_out0,fun x=>?_⟩
    dsimp only [zD]
    have hst2_eq:(dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
      let cond:=decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val)
      (qn st.1 z cond,qY B cond (qO (q7 st.1)) (prefFix z) (prefVal z) st.2))
      (Min,DP1)=st2At k:=by dsimp [st2At];rw [hktake]
    rw [hst2_eq,hM_mid_eq]
    have hst4_eq:(dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
      let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))
      let loOH:=qV (q7 st.1)
      (qA st.1 z cond,qI B cond (st.1 z) loOH (qZ B k cond (st.1 z) st.2)))
      (Mmid,DP3)=st4At k:=by dsimp [st4At];rw [hktake]
    change jZ (j1 G_out) (zE B (vP b Ab Bb o i) ((dF k).foldl _ (Mmid,DP3)).2) (qa x)=_
    rw [hst4_eq,zx hGoutInv_inv _ x,hinv_inv]
    set y':=qT G_out x
    have hy'_hi:∀ s:Fin B,q3 TM ≤ s.val->y' s=x s:=hGout_hi x
    have hkeep_iff:vP b Ab Bb o i (qa y')=true ↔ q4 (q1 TM y')∈q6 Ti1:=by
     simp only [vP,vK,Bool.not_eq_true']
     have hred_iff:qK (q8 (yg Ab Bb o (t+1)) (q1 TM y'))=false ↔
       q8 (yg Ab Bb o (t+1)) (q1 TM y')=q2 m:=by
      constructor
      ·intro hf;by_contra hne
       have h1:=(ji _).mpr (fun h0=>hne (v7 (h0.trans (qh m).symm)))
       rw [h1] at hf;exact Bool.false_ne_true hf.symm
      ·intro h0;rw [h0];simp [qK,q2]
     rw [hred_iff,qG (yF Ab Bb o (t+1)).1,
       (yF Ab Bb o (t+1)).2,(vO Ab Bb o (t+1)).2]
     have hinL:q4 (q1 TM y')∈qw Ab Bb (Qb o (t+1)):=by
      have:=(qg TM hEM hBM).2.2.2.1 y'
      rw [(yG Ab Bb o i).2] at this;exact this.1
     exact ⟨fun hR=>⟨hinL,hR⟩,fun h=>h.2⟩
    dsimp only [zE]
    by_cases hgap1:∃ s:Fin B,q3 Ti1 ≤ s.val/\s.val < B - (Q5 r Ab Bb o (t+1)).card/\x s=true
    ·rw [if_pos hgap1]
     by_cases hk1:vP b Ab Bb o i (qa y')=true
     ·rw [if_pos hk1,hDP4_0 y']
      have hx_mid:∀ s:Fin B,q3 Ti1 ≤ s.val->s.val < q3 TM->x s=false:=by
       have h1:=(hGout_iff y').mp (hkeep_iff.mp hk1)
       have hxeq:qT (j1 G_out) y'=x:=by rw [← jr,(jF hGout_inv).2,yj]
       rwa [hxeq] at h1
      obtain ⟨s,hs1,hs2,hs3⟩:=hgap1
      have hsM:q3 TM ≤ s.val:=by
       by_contra hlt;rw [hx_mid s hs1 (by omega)] at hs3;exact Bool.false_ne_true hs3
      rw [if_pos ⟨s,hsM,hs2,by rw [hy'_hi s hsM];exact hs3⟩]
     ·rw [if_neg hk1]
    ·rw [if_neg hgap1]
     have hx_mid:∀ s:Fin B,q3 Ti1 ≤ s.val->s.val < q3 TM->x s=false:=by
      intro s hs1 hs2;by_contra hne
      exact hgap1 ⟨s,hs1,by omega,by cases h:x s <;> simp_all⟩
     have hrec_eq:q1 TM y'=q1 Ti1 x:=hGout_rec x hx_mid
     have hk1:vP b Ab Bb o i (qa y')=true:=by
      rw [hkeep_iff,hrec_eq];exact (qg Ti1 hETi1 (by omega)).2.2.2.1 x
     have hngM:¬ ∃ s:Fin B,q3 TM ≤ s.val/\s.val < B - (Q5 r Ab Bb o (t+1)).card/\y' s=true:=by
      rintro ⟨s,hs1,hs2,hs3⟩
      exact hgap1 ⟨s,by omega,hs2,by rw [← hy'_hi s hs1];exact hs3⟩
     rw [if_pos hk1,hDP4_0 y',if_neg hngM]
     congr 1;ext w;simp only [v9,dK,dL,true_and,hrec_eq]
     constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> refine ⟨h1,h2,fun z s hMs=>?_,h4⟩
     ·have hsge:B - (Q5 r Ab Bb o (t+1)).card ≤ s.val:=by
       have hu:=hM_out0.2.2.2.2 s;have:q7 Mout s=true:=by simp [q7];exact ⟨z,hMs⟩
       rw [hu] at this;exact of_decide_eq_true this
      rw [← hy'_hi s (by omega)];exact h3 z s hMs
     ·have hsge:B - (Q5 r Ab Bb o (t+1)).card ≤ s.val:=by
       have hu:=hM_out0.2.2.2.2 s;have:q7 Mout s=true:=by simp [q7];exact ⟨z,hMs⟩
       rw [hu] at this;exact of_decide_eq_true this
      rw [hy'_hi s (by omega)];exact h3 z s hMs
  obtain ⟨hMk,hDPk⟩:=hmain k le_rfl
  have hktake:(dF k).take k=dF k:=by simp
  rw [hktake] at hDPk
  have hDP0_val:=hDPk (q2 B)
  have hpack0:qa (q2 B)=⟨0,Nat.two_pow_pos B⟩:=by
   apply Fin.ext;change qu (q2 B)=0;unfold qu;simp [q2]
  have hng0:¬ ∃ t:Fin B,q3 (vL Ab Bb o k) ≤ t.val/\t.val < B - (Q5 r Ab Bb o k).card/\q2 B t=true:=by
   rintro ⟨_,_,_,h⟩;simp [q2] at h
  rw [hpack0,if_neg hng0] at hDP0_val
  set Pk:=qi r Ab Bb (Qb o k)
  have hrec0:q1 (vL Ab Bb o k) (q2 B)=q2 m:=by
   have:=(qg (vL Ab Bb o k) (vO Ab Bb o k).1 (by rw [zl];omega)).2.2.2.1 (q2 B)
   have hbot:q6 (vL Ab Bb o k)=⊥:=by
    rw [← Submodule.finrank_eq_zero (R:=ZMod 2),qo (vO Ab Bb o k).1,zl]
   rw [hbot,Submodule.mem_bot] at this;exact v7 (this.trans (qh m).symm)
  have hS0_eq:v9 b Ab Bb nr nc cr cc o prefFix prefVal Pk (qt r b Ab Bb o k)
    (vL Ab Bb o k) k (qF Ab Bb y o k) (q2 B) =
    Finset.univ.filter fun w:Fin (2^k)=>
     (∀ z:Fin k,z∉Pk->w.val.testBit z.val=false) /\
     (∀ z:Fin k,z∈Pk->prefFix z=true->w.val.testBit z.val=prefVal z) /\
     v4 k r m Ab Bb nr.val nc.val cr cc w.val=y:=by
   ext w;simp only [v9,dK,dL,true_and,
    j6 _ _ _ _ _ _ ho,dn Ab Bb y ho hok,hrec0]
   have hMk0:∀ z s,qt r b Ab Bb o k z s=false:=fun z s=>by
    rw [hMk.2.2.1 z (by rw [QW];simp)]
   have hxor0:q5 (v4 k r m Ab Bb nr.val nc.val cr cc w.val) y=q2 m ↔
     v4 k r m Ab Bb nr.val nc.val cr cc w.val=y:=by
    constructor
    ·intro h;funext q;have:=congrFun h q;simp only [q5,q2] at this
     cases h1:v4 k r m Ab Bb nr.val nc.val cr cc w.val q <;> cases h2:y q <;> simp_all
    ·intro h;rw [h];funext q;simp [q5,q2]
   simp [hMk0,hxor0]
  set Sbase:=Finset.univ.filter fun w:Fin (2^k)=>
   (∀ z:Fin k,z∉Pk->w.val.testBit z.val=false) /\
   (∀ z:Fin k,z∈Pk->prefFix z=true->w.val.testBit z.val=prefVal z) /\
   v4 k r m Ab Bb nr.val nc.val cr cc w.val=y
  set Ufree:=Finset.univ.filter fun z:Fin k=>z∉Pk/\prefFix z=false
  set Sfull:=Finset.univ.filter fun w:Fin (2^k)=>
   v4 k r m Ab Bb nr.val nc.val cr cc w.val=y /\
   ∀ z:Fin k,prefFix z=true->w.val.testBit z.val=prefVal z
  have hprod:Sfull.card=Sbase.card*2^Ufree.card:=by
   set Qq':=Finset.univ.filter fun v:Fin (2^k)=>
    (∀ z:Fin k,z∈Pk->v.val.testBit z.val=false) /\
    (∀ z:Fin k,z∉Pk->prefFix z=true->v.val.testBit z.val=prefVal z)
   have hRcard:Qq'.card=2^Ufree.card:=by
    have hbij:Qq'.card=(Finset.powerset Ufree).card:=by
     refine Finset.card_bij (fun (v:Fin (2^k)) _=>Ufree.filter fun z=>v.val.testBit z.val=true) ?_ ?_ ?_
     ·intro v _;exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
     ·intro v1 hv1 v2 hv2 heq
      obtain ⟨h1a,h1b⟩:=(Finset.mem_filter.mp hv1).2
      obtain ⟨h2a,h2b⟩:=(Finset.mem_filter.mp hv2).2
      apply Fin.ext;apply Nat.eq_of_testBit_eq;intro q
      by_cases hq:q < k
      ·set z:Fin k:=⟨q,hq⟩
       by_cases hzP:z∈Pk
       ·rw [h1a z hzP,h2a z hzP]
       ·by_cases hpf:prefFix z=true
        ·rw [h1b z hzP hpf,h2b z hzP hpf]
        ·have hzU:z∈Ufree:=Finset.mem_filter.mpr ⟨dL _,hzP,Bool.eq_false_iff.mpr hpf⟩
         have hiff:=Finset.ext_iff.mp heq z
         simp only [dK,hzU,true_and] at hiff
         exact Bool.eq_iff_iff.mpr hiff
      ·rw [Nat.testBit_lt_two_pow (v1.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
         Nat.testBit_lt_two_pow (v2.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
     ·intro T hT
      have hTsub:T ⊆ Ufree:=Finset.mem_powerset.mp hT
      let bv:Q1 k:=fun z=>
       if z∈Pk then false else if prefFix z=true then prefVal z else decide (z∈T)
      refine ⟨qa bv,Finset.mem_filter.mpr ⟨dL _,?_,?_⟩,?_⟩
      ·intro z hz;change (qu bv).testBit z.val=false;rw [qb _ z];simp [bv,hz]
      ·intro z hz hpf;change (qu bv).testBit z.val=prefVal z;rw [qb _ z];simp [bv,hz,hpf]
      ·ext z;simp only [dK]
       constructor
       ·rintro ⟨hzU,hbit⟩
        change (qu bv).testBit z.val=true at hbit
        rw [qb _ z] at hbit
        obtain ⟨hzP,hpf⟩:=(Finset.mem_filter.mp hzU).2
        simpa [bv,hzP,hpf] using hbit
       ·intro hzT
        have hzU:=hTsub hzT
        obtain ⟨hzP,hpf⟩:=(Finset.mem_filter.mp hzU).2
        refine ⟨hzU,?_⟩
        change (qu bv).testBit z.val=true
        rw [qb _ z];simp [bv,hzP,hpf,hzT]
    rw [hbij,Finset.card_powerset]
   rw [← hRcard,← Finset.card_product]
   refine Finset.card_bij (fun (w:Fin (2^k)) _=>
    (qa (fun z:Fin k=>decide (z∈Pk)&&w.val.testBit z.val),
    qa (fun z:Fin k=>!decide (z∈Pk)&&w.val.testBit z.val))) ?_ ?_ ?_
   ·intro w hw
    obtain ⟨hrep,hmp⟩:=(Finset.mem_filter.mp hw).2
    rw [Finset.mem_product]
    set w1:=qa (fun z:Fin k=>decide (z∈Pk)&&w.val.testBit z.val)
    set w2:=qa (fun z:Fin k=>!decide (z∈Pk)&&w.val.testBit z.val)
    have hrep1:v4 k r m Ab Bb nr.val nc.val cr cc w1.val=v4 k r m Ab Bb nr.val nc.val cr cc w.val:=by
     rw [← j6 _ _ _ _ _ _ ho,← j6 _ _ _ _ _ _ ho]
     exact vM hk hr Ab Bb nr.isLt nc.isLt cr cc o le_rfl w1.isLt w.isLt fun z hz=>by
      change (qu _).testBit z.val=_;rw [qb _ z];simp [Pk,hz]
    refine ⟨Finset.mem_filter.mpr ⟨dL _,?_,?_,hrep1.trans hrep⟩,
        Finset.mem_filter.mpr ⟨dL _,?_,?_⟩⟩
    ·intro z hz;change (qu _).testBit z.val=false;rw [qb _ z];simp [hz]
    ·intro z hz hpf;change (qu _).testBit z.val=prefVal z;rw [qb _ z];simp [hz,hmp z hpf]
    ·intro z hz;change (qu _).testBit z.val=false;rw [qb _ z];simp [hz]
    ·intro z hz hpf;change (qu _).testBit z.val=prefVal z;rw [qb _ z];simp [hz,hmp z hpf]
   ·intro w1 _ w2 _ heq
    have h1:=congrArg Prod.fst heq;have h2:=congrArg Prod.snd heq
    apply Fin.ext;apply Nat.eq_of_testBit_eq;intro q
    by_cases hq:q < k
    ·set z:Fin k:=⟨q,hq⟩
     by_cases hz:z∈Pk
     ·have:=congrArg (fun a:Fin (2^k)=>a.val.testBit z.val) h1
      change (qu _).testBit z.val=(qu _).testBit z.val at this
      rw [qb _ z,qb _ z] at this;simpa [hz] using this
     ·have:=congrArg (fun a:Fin (2^k)=>a.val.testBit z.val) h2
      change (qu _).testBit z.val=(qu _).testBit z.val at this
      rw [qb _ z,qb _ z] at this;simpa [hz] using this
    ·rw [Nat.testBit_lt_two_pow (w1.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
       Nat.testBit_lt_two_pow (w2.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
   ·rintro ⟨w1,w2⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨h1a,h1b,h1r⟩:=(Finset.mem_filter.mp hp.1).2
    obtain ⟨h2a,h2b⟩:=(Finset.mem_filter.mp hp.2).2
    set w:Fin (2^k):=⟨w1.val ^^^ w2.val,Nat.xor_lt_two_pow w1.isLt w2.isLt⟩
    have hw_bit:∀ z:Fin k,w.val.testBit z.val=if z∈Pk then w1.val.testBit z.val else w2.val.testBit z.val:=fun z=>by
     dsimp [w];rw [Nat.testBit_xor]
     by_cases hz:z∈Pk
     ·simp [hz,h2a z hz]
     ·simp [hz,h1a z hz]
    have hrep:v4 k r m Ab Bb nr.val nc.val cr cc w.val=y:=by
     rw [← j6 _ _ _ _ _ _ ho,← h1r,← j6 _ _ _ _ _ _ ho]
     exact vM hk hr Ab Bb nr.isLt nc.isLt cr cc o le_rfl w.isLt w1.isLt fun z hz=>by
      rw [hw_bit z,if_pos hz]
    refine ⟨w,Finset.mem_filter.mpr ⟨dL w,hrep,fun z hpf=>?_⟩,?_⟩
    ·rw [hw_bit z];by_cases hz:z∈Pk
     ·simp [hz,h1b z hz hpf]
     ·simp [hz,h2b z hz hpf]
    ·apply Prod.ext <;> apply Fin.ext <;> apply Nat.eq_of_testBit_eq <;> intro q
     ·by_cases hq:q < k
      ·set z:Fin k:=⟨q,hq⟩
       change (qu _).testBit z.val=_
       rw [qb _ z,hw_bit z]
       by_cases hz:z∈Pk
       ·simp [hz,z]
       ·simp [hz];exact h1a z hz
      ·rw [Nat.testBit_lt_two_pow ((qa _).isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
         Nat.testBit_lt_two_pow (w1.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
     ·by_cases hq:q < k
      ·set z:Fin k:=⟨q,hq⟩
       change (qu _).testBit z.val=_
       rw [qb _ z,hw_bit z]
       by_cases hz:z∈Pk
       ·simp [hz];exact h2a z hz
       ·simp [hz,z]
      ·rw [Nat.testBit_lt_two_pow ((qa _).isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
         Nat.testBit_lt_two_pow (w2.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
  have hSfull_le:Sbase.card*2^Ufree.card ≤ 2^k:=by
   rw [← hprod];simpa using Finset.card_le_univ Sfull
  have hpm:y9 r Ab Bb (vQ o k)=fun z=>decide (z∈Pk):=by
   funext z
   rw [show vQ o k=fun p=>decide (p∈Qb o k) by funext p;simp [Qb]]
   exact zz r Ab Bb (Qb o k) z
  have hshift:∀ t ≤ k,
    ((dF k).take t).foldl (fun acc z=>
     if !decide (z∈Pk)&&!prefFix z then (acc+acc) % 2^(k+1) else acc) Sbase.card =
    Sbase.card*2^(Ufree.filter fun z:Fin k=>z.val < t).card:=by
   intro t;induction t with
   | zero=>intro _;simp [Ufree]
   | succ t iht=>
    intro ht
    have htu:(dF k).take (t+1)=(dF k).take t ++ [⟨t,ht⟩]:=by
     rw [dJ (by simp;omega)];simp
    rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil,iht (Nat.le_of_succ_le ht)]
    set zt:Fin k:=⟨t,ht⟩
    by_cases hzU:zt∈Ufree
    ·have hz1:zt∉Pk:=(Finset.mem_filter.mp hzU).2.1
     have hz2:prefFix zt=false:=(Finset.mem_filter.mp hzU).2.2
     have hins:Ufree.filter (fun z:Fin k=>z.val < t+1)=insert zt (Ufree.filter (fun z:Fin k=>z.val < t)):=by
      ext z;simp only [dK,Finset.mem_insert]
      constructor
      ·rintro ⟨h1,h2⟩
       by_cases hlt:z.val < t
       ·right;exact ⟨h1,hlt⟩
       ·left;exact Fin.ext (by dsimp [zt];omega)
      ·rintro (rfl | ⟨h1,h2⟩)
       ·exact ⟨hzU,by dsimp [zt];omega⟩
       ·exact ⟨h1,by omega⟩
     have hnot:zt∉Ufree.filter (fun z:Fin k=>z.val < t):=by simp [zt]
     rw [hins,Finset.card_insert_of_notMem hnot,pow_succ]
     have hsub_le:(Ufree.filter fun z:Fin k=>z.val < t).card+1 ≤ Ufree.card:=by
      rw [← Finset.card_insert_of_notMem hnot,← hins];exact Finset.card_le_card (Finset.filter_subset _ _)
     have hlt2:Sbase.card*(2^(Ufree.filter fun z:Fin k=>z.val < t).card*2) < 2^(k+1):=by
      have h1:2^((Ufree.filter fun z:Fin k=>z.val < t).card+1) ≤ 2^Ufree.card:=
       Nat.pow_le_pow_right (by omega) hsub_le
      rw [pow_succ] at h1
      have h2:=Nat.mul_le_mul_left Sbase.card h1
      have h3:0 < 2^k:=Nat.two_pow_pos k
      rw [pow_succ];omega
     simp only [hz1,decide_false,Bool.not_false,hz2,Bool.and_self,↓reduceIte]
     rw [show Sbase.card*2^(Ufree.filter fun z:Fin k=>z.val < t).card +
       Sbase.card*2^(Ufree.filter fun z:Fin k=>z.val < t).card =
       Sbase.card*(2^(Ufree.filter fun z:Fin k=>z.val < t).card*2) by ring]
     exact Nat.mod_eq_of_lt hlt2
    ·have hcondF:(!decide (zt∈Pk)&&!prefFix zt)=false:=by
      by_contra hne;apply hzU
      have ht':(!decide (zt∈Pk)&&!prefFix zt)=true:=by cases h:(!decide (zt∈Pk)&&!prefFix zt) <;> simp_all
      simp only [dI,Bool.not_eq_true',decide_eq_false_iff_not] at ht'
      exact Finset.mem_filter.mpr ⟨dL _,ht'.1,ht'.2⟩
     have heq:Ufree.filter (fun z:Fin k=>z.val < t+1)=Ufree.filter (fun z:Fin k=>z.val < t):=by
      ext z;simp only [dK]
      constructor
      ·rintro ⟨h1,h2⟩;refine ⟨h1,?_⟩
       by_contra hge;have ez:z=zt:=Fin.ext (by dsimp [zt];omega);exact hzU (ez▸h1)
      ·rintro ⟨h1,h2⟩;exact ⟨h1,by omega⟩
     rw [hcondF,heq];rfl
  rw [hDP0_val,hS0_eq,ym,hpm]
  have hs:=hshift k le_rfl
  rw [hktake,show Ufree.filter (fun z:Fin k=>z.val < k)=Ufree by ext z;simp] at hs
  exact hs.trans hprod.symm
 ·unfold qX;rw [if_neg hok]
  symm;rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro w _ ⟨hrep,_⟩
  apply hok;rw [zZ Ab Bb y ho,← hrep,← j6 _ _ _ _ _ _ ho,← QR ho]
  exact jS _ _ _ _ _ _ _ _ le_rfl
def ja {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (y:Q1 m) (o:Fin k->Fin k)
  (st:ℕ × (Fin k->Bool) × (Fin k->Bool)) (step:Fin k):ℕ × (Fin k->Bool) × (Fin k->Bool):=
 let pos:Fin k:=⟨k - 1 - step.val,by omega⟩
 let fix':Fin k->Bool:=fun z=>if z=pos then true else st.2.1 z
 let val0:Fin k->Bool:=fun z=>if z=pos then false else st.2.2 z
 let val1:Fin k->Bool:=fun z=>if z=pos then true else st.2.2 z
 let c0:=qX b Ab Bb nr nc cr cc y o fix' val0
 if st.1 < c0 then (st.1,fix',val0) else (st.1 - c0,fix',val1)
def jn {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (y:Q1 m) (o:Fin k->Fin k) (t:ℕ):Fin k->Bool:=
 ((dF k).foldl (ja b Ab Bb nr nc cr cc y o) (t,fun _=>false,fun _=>false)).2.2
lemma db {k r m b:ℕ} (hk:0 < k) (hr:4 ≤ r)
  (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k)) (cr cc:Fin r->Fin (2^k))
  (y:Q1 m) {o:Fin k->Fin k} (ho:Function.Bijective o) (hw:qU r Ab Bb o ≤ b)
  (t:Fin (2^(k+1))) (j:Fin (k+1)) :
  let hit:Fin (2^k)->Prop:=fun w=>v4 k r m Ab Bb nr.val nc.val cr cc w.val=y
  let tot:=qX b Ab Bb nr nc cr cc y o (fun _=>false) (fun _=>false)
  let bits:=jn b Ab Bb nr nc cr cc y o t.val
  (decide (t.val < tot)&&(decide (j.val=0) ||
   (if hj:j.val=0 then false else bits ⟨j.val - 1,by omega⟩))) =
   decide (∃ w:Fin (2^k),hit w/\Nat.card {z:Fin (2^k) // z < w/\hit z}=t.val /\
    (j.val=0\/w.val.testBit (j.val - 1)=true)):=by
 dsimp only
 set hit:Fin (2^k)->Prop:=fun w=>v4 k r m Ab Bb nr.val nc.val cr cc w.val=y
 have htot:qX b Ab Bb nr nc cr cc y o (fun _=>false) (fun _=>false) =
   (Finset.univ.filter fun w:Fin (2^k)=>hit w).card:=by
  rw [z7 hk hr Ab Bb nr nc cr cc y ho hw]
  apply congrArg Finset.card;ext w;simp [hit]
 have hcard_lt:∀ w:Fin (2^k),Nat.card {z:Fin (2^k) // z < w/\hit z} =
   (Finset.univ.filter fun z:Fin (2^k)=>z.val < w.val/\hit z).card:=by
  intro w;rw [Nat.card_eq_fintype_card,Fintype.card_subtype];rfl
 have huniq:∀ w1 w2:Fin (2^k),hit w1->hit w2 ->
   (Finset.univ.filter fun z:Fin (2^k)=>z.val < w1.val/\hit z).card =
   (Finset.univ.filter fun z:Fin (2^k)=>z.val < w2.val/\hit z).card->w1=w2:=by
  intro w1 w2 h1 h2 heq
  by_contra hne
  have hor:w1.val < w2.val\/w2.val < w1.val:=by have:w1.val ≠ w2.val:=fun e=>hne (Fin.ext e);omega
  rcases hor with hlt | hlt
  ·have hss:(Finset.univ.filter fun z:Fin (2^k)=>z.val < w1.val/\hit z) ⊂
     (Finset.univ.filter fun z:Fin (2^k)=>z.val < w2.val/\hit z):=by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun z hz=>by simp only [dK,dL,true_and] at hz ⊢;exact ⟨by omega,hz.2⟩,
     fun he=>by
      have hm:w1∈Finset.univ.filter fun z:Fin (2^k)=>z.val < w2.val/\hit z:=
       Finset.mem_filter.mpr ⟨dL _,hlt,h1⟩
      rw [← he] at hm;simp at hm⟩
   exact absurd heq (ne_of_lt (Finset.card_lt_card hss))
  ·have hss:(Finset.univ.filter fun z:Fin (2^k)=>z.val < w2.val/\hit z) ⊂
     (Finset.univ.filter fun z:Fin (2^k)=>z.val < w1.val/\hit z):=by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun z hz=>by simp only [dK,dL,true_and] at hz ⊢;exact ⟨by omega,hz.2⟩,
     fun he=>by
      have hm:w2∈Finset.univ.filter fun z:Fin (2^k)=>z.val < w1.val/\hit z:=
       Finset.mem_filter.mpr ⟨dL _,hlt,h2⟩
      rw [← he] at hm;simp at hm⟩
   exact absurd heq.symm (ne_of_lt (Finset.card_lt_card hss))
 by_cases ht_lt:t.val < qX b Ab Bb nr nc cr cc y o (fun _=>false) (fun _=>false)
 ·have hloop:∀ s ≤ k,
    let st:=((dF k).take s).foldl (ja b Ab Bb nr nc cr cc y o) (t.val,fun _=>false,fun _=>false)
    (∀ z:Fin k,st.2.1 z=decide (k - s ≤ z.val)) /\
    ∃ p:ℕ,p < 2^s /\
     (∀ z:Fin k,k - s ≤ z.val->st.2.2 z=p.testBit (z.val - (k - s))) /\
     (Finset.univ.filter fun w:Fin (2^k)=>hit w/\w.val < p*2^(k - s)).card+st.1=t.val /\
     st.1 < (Finset.univ.filter fun w:Fin (2^k)=>hit w/\p*2^(k - s) ≤ w.val/\w.val < (p+1)*2^(k - s)).card:=by
   intro s;induction s with
   | zero=>
    intro _;simp only [List.take_zero,List.foldl_nil,Nat.sub_zero,pow_zero]
    refine ⟨fun z=>by symm;exact decide_eq_false (by omega),0,by omega,fun z hz=>by omega,by simp,?_⟩
    rw [htot] at ht_lt
    simpa [Fin.isLt] using ht_lt
   | succ s ihs=>
    intro hs
    obtain ⟨hfix,p,hp_lt,hval,hsum,hrem⟩:=ihs (Nat.le_of_succ_le hs)
    have hts:(dF k).take (s+1)=(dF k).take s ++ [⟨s,hs⟩]:=by
     rw [dJ (by simp;omega)];simp
    dsimp only;rw [hts,List.foldl_append,List.foldl_cons,List.foldl_nil]
    set st:=((dF k).take s).foldl (ja b Ab Bb nr nc cr cc y o) (t.val,fun _=>false,fun _=>false)
    set pos:Fin k:=⟨k - 1 - s,by omega⟩
    set fix':Fin k->Bool:=fun z=>if z=pos then true else st.2.1 z
    set val0:Fin k->Bool:=fun z=>if z=pos then false else st.2.2 z
    set val1:Fin k->Bool:=fun z=>if z=pos then true else st.2.2 z
    have hfix':∀ z:Fin k,fix' z=decide (k - (s+1) ≤ z.val):=fun z=>by
     dsimp [fix',pos];rw [hfix z]
     by_cases ez:z=⟨k - 1 - s,by omega⟩
     ·subst ez;simp;omega
     ·have hne:z.val ≠ k - 1 - s:=fun e=>ez (Fin.ext e)
      have hiff:k - s ≤ z.val ↔ k - (s+1) ≤ z.val:=by omega
      simp [ez,hiff]
    have hpow_split:2^(k - s)=2*2^(k - (s+1)):=by
     rw [show k - s=(k - (s+1))+1 by omega,pow_succ,mul_comm]
    have hmatch_iff:∀ (bit:Bool) (w:Fin (2^k)),
      d4 fix' (if bit then val1 else val0) w ↔
       (2*p+bit.toNat)*2^(k - (s+1)) ≤ w.val/\w.val < (2*p+bit.toNat+1)*2^(k - (s+1)):=by
     intro bit w
     have hdiv_iff:w.val / 2^(k - (s+1))=2*p+bit.toNat ↔
       (2*p+bit.toNat)*2^(k - (s+1)) ≤ w.val/\w.val < (2*p+bit.toNat+1)*2^(k - (s+1)):=by
      have hP:0 < 2^(k - (s+1)):=Nat.two_pow_pos _
      constructor
      ·intro hd
       have hm:=Nat.div_add_mod w.val (2^(k - (s+1)))
       have hml:=Nat.mod_lt w.val hP
       rw [hd,mul_comm] at hm
       constructor
       ·omega
       ·have:(2*p+bit.toNat+1)*2^(k - (s+1))=(2*p+bit.toNat)*2^(k - (s+1))+2^(k - (s+1)):=by ring
        omega
      ·rintro ⟨h1,h2⟩
       have hq1:2*p+bit.toNat ≤ w.val / 2^(k - (s+1)):=(Nat.le_div_iff_mul_le hP).mpr h1
       have hq2:w.val / 2^(k - (s+1)) < 2*p+bit.toNat+1:=(Nat.div_lt_iff_lt_mul hP).mpr h2
       omega
     rw [← hdiv_iff]
     constructor
     ·intro hmp
      apply Nat.eq_of_testBit_eq;intro q
      rw [Nat.testBit_div_two_pow]
      by_cases hq:q < s+1
      ·set z:Fin k:=⟨k - (s+1)+q,by omega⟩
       have hz_fix:fix' z=true:=by rw [hfix' z];exact decide_eq_true (by dsimp [z];omega)
       have htb:=hmp z hz_fix
       have hval_q:(if bit then val1 else val0) z=(2*p+bit.toNat).testBit q:=by
        by_cases hq0:q=0
        ·subst hq0
         have ez:z=pos:=Fin.ext (by dsimp [z,pos];omega)
         rw [ez];cases bit <;> simp [val0,val1,Nat.testBit_zero]
        ·have hne:z ≠ pos:=fun e=>hq0 (by have:=congrArg Fin.val e;dsimp [z,pos] at this;omega)
         have hge:k - s ≤ z.val:=by dsimp [z];omega
         have hvz:(if bit then val1 else val0) z=st.2.2 z:=by cases bit <;> simp [val0,val1,hne]
         rw [hvz,hval z hge]
         have hq1:q=(q - 1)+1:=by omega
         rw [show z.val - (k - s)=q - 1 by dsimp [z];omega]
         conv_rhs=>rw [hq1]
         cases bit <;> simp [Nat.testBit_succ,show (2*p+1) / 2=p by omega]
       simpa [z,add_comm] using htb.trans hval_q
      ·have h1:w.val / 2^(k - (s+1)) < 2^(s+1):=by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),← pow_add,show s+1+(k - (s+1))=k by omega];exact w.isLt
       have h2:2*p+bit.toNat < 2^(s+1):=by cases bit <;> simp [pow_succ] <;> omega
       rw [← Nat.testBit_div_two_pow,
         Nat.testBit_lt_two_pow (h1.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
         Nat.testBit_lt_two_pow (h2.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
     ·intro hdiv z hzfix
      rw [hfix' z,dG] at hzfix
      set q:=z.val - (k - (s+1))
      have hq:k - (s+1)+q=z.val:=by omega
      have h1:=congrArg (fun n=>n.testBit q) hdiv
      rw [Nat.testBit_div_two_pow,add_comm,hq] at h1
      rw [h1]
      by_cases hq0:q=0
      ·have ez:z=pos:=Fin.ext (by dsimp [pos];omega)
       rw [ez,hq0];cases bit <;> simp [val0,val1,Nat.testBit_zero]
      ·have hne:z ≠ pos:=fun e=>hq0 (by have:=congrArg Fin.val e;dsimp [pos] at this;omega)
       have hge:k - s ≤ z.val:=by omega
       have hvz:(if bit then val1 else val0) z=st.2.2 z:=by cases bit <;> simp [val0,val1,hne]
       rw [hvz,hval z hge]
       have hq1:q=(q - 1)+1:=by omega
       rw [show z.val - (k - s)=q - 1 by omega]
       conv_lhs=>rw [hq1]
       cases bit <;> simp [Nat.testBit_succ,show (2*p+1) / 2=p by omega]
    set c0:=qX b Ab Bb nr nc cr cc y o fix' val0
    have hc0_eq:c0=(Finset.univ.filter fun w:Fin (2^k)=>
      hit w/\(2*p)*2^(k - (s+1)) ≤ w.val/\w.val < (2*p+1)*2^(k - (s+1))).card:=by
     dsimp [c0];rw [z7 hk hr Ab Bb nr nc cr cc y ho hw]
     apply congrArg Finset.card;ext w;simp only [dK,dL,true_and,hit]
     exact and_congr_right fun _=>by simpa [d4] using hmatch_iff false w
    have hsplit_card :
      (Finset.univ.filter fun w:Fin (2^k)=>hit w/\p*2^(k - s) ≤ w.val/\w.val < (p+1)*2^(k - s)).card =
      c0+(Finset.univ.filter fun w:Fin (2^k)=>hit w/\(2*p+1)*2^(k - (s+1)) ≤ w.val/\w.val < (2*p+2)*2^(k - (s+1))).card:=by
     rw [hc0_eq,← Finset.card_union_of_disjoint]
     ·apply congrArg Finset.card;ext w;simp only [dK,dL,true_and,Finset.mem_union,hpow_split]
      have h1:p*(2*2^(k - (s+1)))=2*p*2^(k - (s+1)):=by ring
      have h2:(p+1)*(2*2^(k - (s+1)))=(2*p+2)*2^(k - (s+1)):=by ring
      rw [h1,h2];constructor
      ·rintro ⟨hw',ha,hb⟩;by_cases hm:w.val < (2*p+1)*2^(k - (s+1))
       ·left;exact ⟨hw',ha,hm⟩
       ·right;exact ⟨hw',by omega,hb⟩
      ·rintro (⟨hw',ha,hb⟩ | ⟨hw',ha,hb⟩)
       ·exact ⟨hw',ha,lt_of_lt_of_le hb (Nat.mul_le_mul_right _ (by omega))⟩
       ·exact ⟨hw',le_trans (Nat.mul_le_mul_right _ (by omega)) ha,hb⟩
     ·rw [Finset.disjoint_left];intro w h1 h2
      simp only [dK,dL,true_and] at h1 h2;omega
    have hunr_eq:ja b Ab Bb nr nc cr cc y o st ⟨s,hs⟩ =
      if st.1 < c0 then (st.1,fix',val0) else (st.1 - c0,fix',val1):=rfl
    rw [hunr_eq]
    by_cases hlt:st.1 < c0
    ·rw [if_pos hlt]
     refine ⟨hfix',2*p,by rw [pow_succ];omega,fun z hz=>?_,?_,?_⟩
     ·by_cases ez:z=pos
      ·rw [ez];dsimp only [val0,pos]
       rw [if_pos rfl,show k - 1 - s - (k - (s+1))=0 by omega,Nat.testBit_zero];simp
      ·have hge:k - s ≤ z.val:=by have:z.val ≠ k - 1 - s:=fun e=>ez (Fin.ext e);omega
       dsimp only [val0];rw [if_neg ez,hval z hge]
       have hq1:z.val - (k - (s+1))=(z.val - (k - s))+1:=by omega
       rw [hq1,Nat.testBit_succ];simp
     ·rw [show 2*p*2^(k - (s+1))=p*2^(k - s) by rw [hpow_split];ring];exact hsum
     ·rwa [← hc0_eq]
    ·rw [if_neg hlt]
     refine ⟨hfix',2*p+1,by rw [pow_succ];omega,fun z hz=>?_,?_,?_⟩
     ·by_cases ez:z=pos
      ·rw [ez];dsimp only [val1,pos]
       rw [if_pos rfl,show k - 1 - s - (k - (s+1))=0 by omega,Nat.testBit_zero];simp
      ·have hge:k - s ≤ z.val:=by have:z.val ≠ k - 1 - s:=fun e=>ez (Fin.ext e);omega
       dsimp only [val1];rw [if_neg ez,hval z hge]
       have hq1:z.val - (k - (s+1))=(z.val - (k - s))+1:=by omega
       rw [hq1,Nat.testBit_succ];simp [show (2*p+1) / 2=p by omega]
     ·have hle_u:(Finset.univ.filter fun w:Fin (2^k)=>hit w/\w.val < (2*p+1)*2^(k - (s+1))).card =
        (Finset.univ.filter fun w:Fin (2^k)=>hit w/\w.val < p*2^(k - s)).card+c0:=by
       rw [hc0_eq,← Finset.card_union_of_disjoint]
       ·apply congrArg Finset.card;ext w;simp only [dK,dL,true_and,Finset.mem_union,hpow_split]
        have h1:p*(2*2^(k - (s+1)))=2*p*2^(k - (s+1)):=by ring
        rw [h1];constructor
        ·rintro ⟨hw',ha⟩;by_cases hm:w.val < 2*p*2^(k - (s+1))
         ·left;exact ⟨hw',hm⟩
         ·right;exact ⟨hw',by omega,ha⟩
        ·rintro (⟨hw',ha⟩ | ⟨hw',_,hb⟩)
         ·exact ⟨hw',lt_of_lt_of_le ha (Nat.mul_le_mul_right _ (by omega))⟩
         ·exact ⟨hw',hb⟩
       ·rw [Finset.disjoint_left];intro w h1 h2
        simp only [dK,dL,true_and,hpow_split] at h1 h2
        have h1':p*(2*2^(k - (s+1)))=2*p*2^(k - (s+1)):=by ring
        omega
      rw [hle_u];omega
     ·rw [hsplit_card] at hrem;rw [show 2*p+1+1=2*p+2 by omega];omega
  obtain ⟨_,p,hp_lt,hval,hsum,hrem⟩:=hloop k le_rfl
  have hktake:(dF k).take k=dF k:=by simp
  rw [hktake,Nat.sub_self] at hval hsum hrem
  rw [pow_zero] at hsum hrem
  set w0:Fin (2^k):=⟨p,hp_lt⟩
  have hsing_card:(Finset.univ.filter fun w:Fin (2^k)=>hit w/\p*1 ≤ w.val/\w.val < (p+1)*1).card =
    if hit w0 then 1 else 0:=by
   by_cases hw0:hit w0
   ·rw [if_pos hw0]
    have heq:(Finset.univ.filter fun w:Fin (2^k)=>hit w/\p*1 ≤ w.val/\w.val < (p+1)*1)={w0}:=by
     ext w;simp only [dK,dL,true_and,Finset.mem_singleton]
     constructor
     ·rintro ⟨_,h1,h2⟩;exact Fin.ext (by dsimp [w0];omega)
     ·rintro rfl;exact ⟨hw0,by dsimp [w0];omega,by dsimp [w0];omega⟩
    rw [heq,Finset.card_singleton]
   ·rw [if_neg hw0,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    rintro w _ ⟨hw',h1,h2⟩;exact hw0 (by convert hw';exact Fin.ext (by dsimp [w0];omega))
  rw [hsing_card] at hrem
  have hw0_hit:hit w0:=by by_contra hno;rw [if_neg hno] at hrem;omega
  have hrem0:((dF k).foldl (ja b Ab Bb nr nc cr cc y o) (t.val,fun _=>false,fun _=>false)).1=0:=by
   rw [if_pos hw0_hit] at hrem;omega
  have hcnt0:(Finset.univ.filter fun z:Fin (2^k)=>z.val < w0.val/\hit z).card=t.val:=by
   rw [hrem0,add_zero,mul_one] at hsum
   convert hsum using 2;ext z;simp [w0,and_comm]
  simp only [ht_lt,decide_true,Bool.true_and]
  apply Bool.eq_iff_iff.mpr;simp only [dH,dG]
  by_cases hj0:j.val=0
  ·simp only [hj0,↓reduceDIte,true_or,true_iff]
   exact ⟨w0,hw0_hit,by rw [hcard_lt,hcnt0],trivial⟩
  ·simp only [hj0,↓reduceDIte,false_or]
   have hbit:jn b Ab Bb nr nc cr cc y o t.val ⟨j.val - 1,by omega⟩=w0.val.testBit (j.val - 1):=by
    simpa [jn,w0] using hval ⟨j.val - 1,by omega⟩ (Nat.zero_le _)
   rw [hbit]
   constructor
   ·intro htb;exact ⟨w0,hw0_hit,by rw [hcard_lt,hcnt0],htb⟩
   ·rintro ⟨w,hwh,hwcnt,htb⟩
    rw [hcard_lt] at hwcnt
    have hweq:w=w0:=huniq w w0 hwh hw0_hit (hwcnt.trans hcnt0.symm)
    rwa [← hweq]
 ·simp only [ht_lt,decide_false,Bool.false_and]
  symm;apply decide_eq_false
  rintro ⟨w,hwh,hwcnt,_⟩
  rw [hcard_lt] at hwcnt;rw [htot] at ht_lt
  have hss:(Finset.univ.filter fun z:Fin (2^k)=>z.val < w.val/\hit z) ⊂
    (Finset.univ.filter fun z:Fin (2^k)=>hit z):=by
   rw [Finset.ssubset_iff_subset_ne]
   refine ⟨fun z hz=>by simp only [dK,dL,true_and] at hz ⊢;exact hz.2,
    fun he=>by
     have hm:w∈Finset.univ.filter fun z:Fin (2^k)=>hit z:=Finset.mem_filter.mpr ⟨dL _,hwh⟩
     rw [← he] at hm;simp at hm⟩
  have:=Finset.card_lt_card hss;omega
end SelectMath
section SelectCircuit
lemma g9 {k m b:ℕ} (hb:b ≤ k+m) :
  2*(b+2) < 2^(k+m+4):=by
 have h1:k+m+1 ≤ 2^(k+m):=Nat.lt_two_pow_self
 have h2:2^(k+m+4)=16*2^(k+m):=by rw [pow_add];ring
 omega
def Qs (k m:ℕ):ℕ:=
 m*m+k*(36*m*m+10*m)
def gl {nIn k m:ℕ} (c:CB nIn)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m} {fMask:(Fin nIn->Bool)->Fin k->Bool}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (mask:Q2 nIn c k fMask) :
  Q0 nIn c (Qs k m) (fun c'=>Q8 nIn c' m (fun x=>yC (fA x) (fB x) (fMask x))):=
 Q0.weaken (by unfold Qs;nlinarith)<|
 (y0 c m).bind fun c0 h0 zT=>
 let stAt (t:ℕ) (x:Fin nIn->Bool):Q6 m:=
  ((dF k).take t).foldl
   (fun T p=>if fMask x p=true then qC (qC T (fA x p)) (fB x p) else T) (qN m)
 let Acc (t:ℕ) (_:t ≤ k) (c1:CB nIn):Type:=Q8 nIn c1 m (stAt t)
 have hinit:Acc 0 (Nat.zero_le k) c0:=zT.cast (fun _=>rfl)
 (Q0.qe (Bstep:=36*m*m+10*m) k Acc c0 hinit fun t ht c1 h1 Tc=>
  Q0.weaken (by nlinarith)<|
  let pt:Fin k:=⟨t,ht⟩
  let h01:=h0.trans h1
  (jD c1 Tc ((Ab pt).lift h01)).bind fun c2 h2 T1=>
  (jD c2 T1 ((Bb pt).lift (h01.trans h2))).bind fun c3 h3 T2=>
  (gd c3 ((mask.at pt).lift (h01.trans (h2.trans h3))) T2 (Tc.lift (h2.trans h3))).bind fun _ _ T'=>
  have htake:(dF k).take (t+1)=(dF k).take t ++ [pt]:=by
   rw [dJ (by simp;omega)];simp [pt]
  Q0.pure<|T'.cast fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]).bind fun _ _ TF=>
 Q0.pure<|TF.cast fun x=>by
  simp only [stAt,yC,show (dF k).take k=dF k by simp]
def zf {nIn k m:ℕ} (c:CB nIn) (r:ℕ)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m} {fMask:(Fin nIn->Bool)->Fin k->Bool}
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p)))
  (mask:Q2 nIn c k fMask) :
  Q0 nIn c (k*(1+k*2))
   (fun c'=>Q2 nIn c' k (fun x=>y9 r (fA x) (fB x) (fMask x))):=
 j8 (Bstep:=1+k*2) k (fun x z=>y9 r (fA x) (fB x) (fMask x) z) c fun z c0 h0=>
  Q0.weaken (by omega)<|
  (vJ c0 false).bind fun c1 h1 vf=>
  let Acc (t:ℕ) (_:t ≤ k) (c2:CB nIn):Type:=
   Q4 nIn c2 (fun x=>decide (∃ p:Fin k,p.val < t/\fMask x p=true/\z∈qq r (fA x) (fB x) p))
  have hinit:Acc 0 (Nat.zero_le k) c1:=vf.cast fun _=>by simp
  (Q0.qe (Bstep:=2) k Acc c1 hinit fun t ht c2 h2 acc=>
   let pt:Fin k:=⟨t,ht⟩
   let h02:=h0.trans (h1.trans h2)
   (vg c2 ((mask.at pt).lift h02) (((scopes pt).at z).lift h02)).bind fun c3 h3 vand=>
   (yr c3 (acc.lift h3) vand).bind fun _ _ vor=>
   Q0.pure<|vor.cast fun x=>by
    apply Bool.eq_iff_iff.mpr;simp only [dH,dI,dG]
    constructor
    ·rintro (⟨p,hp,h1',h2'⟩ | ⟨h1',h2'⟩)
     ·exact ⟨p,by omega,h1',h2'⟩
     ·exact ⟨pt,by dsimp [pt];omega,h1',h2'⟩
    ·rintro ⟨p,hp,h1',h2'⟩
     by_cases hlt:p.val < t
     ·left;exact ⟨p,hlt,h1',h2'⟩
     ·right;have heq:p=pt:=Fin.ext (by dsimp [pt];omega);subst heq;exact ⟨h1',h2'⟩).bind fun _ _ vF=>
  Q0.pure<|vF.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [y9,dG]
   exact ⟨fun ⟨p,_,h1',h2'⟩=>⟨p,h1',h2'⟩,fun ⟨p,h1',h2'⟩=>⟨p,p.isLt,h1',h2'⟩⟩
def zA {nIn k:ℕ} (c:CB nIn) (lo hi:ℕ)
  {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (ordOH:∀ t:Fin k,Q2 nIn c k (fun x p=>decide (fo x t=p))) :
  Q0 nIn c (k*(1+k))
   (fun c'=>Q2 nIn c' k (fun x p=>decide (∃ t:Fin k,lo ≤ t.val/\t.val < hi/\fo x t=p))):=
 j8 (Bstep:=1+k) k (fun x p=>decide (∃ t:Fin k,lo ≤ t.val/\t.val < hi/\fo x t=p)) c fun p c0 h0=>
  Q0.weaken (by omega)<|
  (vJ c0 false).bind fun c1 h1 vf=>
  let Acc (s:ℕ) (_:s ≤ k) (c2:CB nIn):Type:=
   Q4 nIn c2 (fun x=>decide (∃ t:Fin k,t.val < s/\lo ≤ t.val/\t.val < hi/\fo x t=p))
  have hinit:Acc 0 (Nat.zero_le k) c1:=vf.cast fun _=>by simp
  (Q0.qe (Bstep:=1) k Acc c1 hinit fun s hs c2 h2 acc=>
   let st:Fin k:=⟨s,hs⟩
   if hcond:lo ≤ s/\s < hi then
    (yr c2 acc (((ordOH st).at p).lift (h0.trans (h1.trans h2)))).bind fun _ _ vor=>
    Q0.pure<|vor.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp only [dH,dG]
     constructor
     ·rintro (⟨t,ht,h1',h2',h3'⟩ | h3')
      ·exact ⟨t,by omega,h1',h2',h3'⟩
      ·exact ⟨st,by dsimp [st];omega,hcond.1,hcond.2,h3'⟩
     ·rintro ⟨t,ht,h1',h2',h3'⟩
      by_cases hlt:t.val < s
      ·left;exact ⟨t,hlt,h1',h2',h3'⟩
      ·right;have heq:t=st:=Fin.ext (by dsimp [st];omega);subst heq;exact h3'
   else
    Q0.weaken (by omega)<|
    Q0.pure<|acc.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp only [dG]
     constructor
     ·rintro ⟨t,ht,h1',h2',h3'⟩;exact ⟨t,by omega,h1',h2',h3'⟩
     ·rintro ⟨t,ht,h1',h2',h3'⟩
      refine ⟨t,?_,h1',h2',h3'⟩
      by_contra hge;exact hcond ⟨by omega,by omega⟩).bind fun _ _ vF=>
  Q0.pure<|vF.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [dG]
   exact ⟨fun ⟨t,_,h1',h2',h3'⟩=>⟨t,h1',h2',h3'⟩,fun ⟨t,h1',h2',h3'⟩=>⟨t,t.isLt,h1',h2',h3'⟩⟩
structure Qo (nIn:ℕ) (c:CB nIn) (k B:ℕ) (f:(Fin nIn->Bool)->Ql k B) where
 rows:∀ z:Fin k,Q2 nIn c B (fun x=>f x z)
def Qo.lift {nIn k B:ℕ} {c c':CB nIn} {f:(Fin nIn->Bool)->Ql k B}
  (h:c.Qa c') (M:Qo nIn c k B f):Qo nIn c' k B f:=
 ⟨fun z=>(M.rows z).lift h⟩
def Qo.cast {nIn k B:ℕ} {c:CB nIn} {f g:(Fin nIn->Bool)->Ql k B}
  (h:∀ x z s,f x z s=g x z s) (M:Qo nIn c k B f):Qo nIn c k B g:=
 ⟨fun z=>(M.rows z).cast (fun x s=>h x z s)⟩
def dk {nIn:ℕ} (c:CB nIn) (k B:ℕ) (M:Ql k B) :
  Q0 nIn c (k*B) (fun c'=>Qo nIn c' k B (fun _=>M)):=
 let Acc (t:ℕ) (_:t ≤ k) (c1:CB nIn):Type:=
  ∀ z:Fin k,z.val < t->Q2 nIn c1 B (fun _=>M z)
 have hinit:Acc 0 (Nat.zero_le k) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=B) k Acc c hinit fun t ht c1 _ acc=>
  Q0.weaken (by omega)<|
  let zt:Fin k:=⟨t,ht⟩
  (vq c1 B (M zt)).bind fun _ h2 vz=>
  Q0.pure fun z hz=>
   if hlt:z.val < t then (acc z hlt).lift h2
   else
    have heq:z=zt:=Fin.ext (by dsimp [zt];omega)
    heq▸vz).bind fun _ _ all=>
 Q0.pure ⟨fun z=>all z z.isLt⟩
def gk {nIn k B:ℕ} (c:CB nIn) {fM:(Fin nIn->Bool)->Ql k B}
  (M:Qo nIn c k B fM) :
  Q0 nIn c (B*(1+k)) (fun c'=>Q2 nIn c' B (fun x=>q7 (fM x))):=
 j8 (Bstep:=1+k) B (fun x s=>q7 (fM x) s) c fun s c0 h0=>
  Q0.weaken (by omega)<|
  (vJ c0 false).bind fun c1 h1 vf=>
  let Acc (t:ℕ) (_:t ≤ k) (c2:CB nIn):Type:=
   Q4 nIn c2 (fun x=>decide (∃ z:Fin k,z.val < t/\fM x z s=true))
  have hinit:Acc 0 (Nat.zero_le k) c1:=vf.cast fun _=>by simp
  (Q0.qe (Bstep:=1) k Acc c1 hinit fun t ht c2 h2 acc=>
   let zt:Fin k:=⟨t,ht⟩
   (yr c2 acc (((M.rows zt).at s).lift (h0.trans (h1.trans h2)))).bind fun _ _ vor=>
   Q0.pure<|vor.cast fun x=>by
    apply Bool.eq_iff_iff.mpr;simp only [dH,dG]
    constructor
    ·rintro (⟨z,hz,h1'⟩ | h1')
     ·exact ⟨z,by omega,h1'⟩
     ·exact ⟨zt,by dsimp [zt];omega,h1'⟩
    ·rintro ⟨z,hz,h1'⟩
     by_cases hlt:z.val < t
     ·left;exact ⟨z,hlt,h1'⟩
     ·right;have heq:z=zt:=Fin.ext (by dsimp [zt];omega);subst heq;exact h1').bind fun _ _ vF=>
  Q0.pure<|vF.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [q7,dG]
   exact ⟨fun ⟨z,_,h1'⟩=>⟨z,h1'⟩,fun ⟨z,h1'⟩=>⟨z,z.isLt,h1'⟩⟩
def di {nIn B:ℕ} (c:CB nIn) {fu:(Fin nIn->Bool)->Fin B->Bool}
  (u:Q2 nIn c B fu) :
  Q0 nIn c (B*(1+B)) (fun c'=>Q2 nIn c' B (fun x=>qO (fu x))):=
 j8 (Bstep:=1+B) B (fun x s=>qO (fu x) s) c fun s c0 h0=>
  Q0.weaken (by omega)<|
  (y2 c0 ((u.at s).lift h0)).bind fun c1 h1 vnu=>
  let Acc (t:ℕ) (_:t ≤ B) (c2:CB nIn):Type:=
   Q4 nIn c2 (fun x=>decide (fu x s=false/\∀ s':Fin B,s'.val < t->s.val < s'.val->fu x s'=true))
  have hinit:Acc 0 (Nat.zero_le B) c1:=vnu.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [Bool.not_eq_true',dG]
   exact ⟨fun h=>⟨h,fun _ ht=>absurd ht (by omega)⟩,fun h=>h.1⟩
  (Q0.qe (Bstep:=1) B Acc c1 hinit fun t ht c2 h2 acc=>
   let st:Fin B:=⟨t,ht⟩
   if hgt:s.val < t then
    (vg c2 acc ((u.at st).lift (h0.trans (h1.trans h2)))).bind fun _ _ vand=>
    Q0.pure<|vand.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp only [dI,dG]
     constructor
     ·rintro ⟨⟨h1',h2'⟩,h3'⟩
      refine ⟨h1',fun s' hs' hlt=>?_⟩
      by_cases hl:s'.val < t
      ·exact h2' s' hl hlt
      ·have heq:s'=st:=Fin.ext (by dsimp [st];omega);subst heq;exact h3'
     ·rintro ⟨h1',h2'⟩
      exact ⟨⟨h1',fun s' hs' hlt=>h2' s' (by omega) hlt⟩,h2' st (by dsimp [st];omega) hgt⟩
   else
    Q0.weaken (by omega)<|
    Q0.pure<|acc.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp only [dG]
     constructor
     ·rintro ⟨h1',h2'⟩;refine ⟨h1',fun s' hs' hlt=>h2' s' (by omega) hlt⟩
     ·rintro ⟨h1',h2'⟩;exact ⟨h1',fun s' hs' hlt=>h2' s' (by omega) hlt⟩).bind fun _ _ vF=>
  Q0.pure<|vF.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [qO,dG]
   exact ⟨fun ⟨h1',h2'⟩=>⟨h1',fun s' hlt=>h2' s' s'.isLt hlt⟩,
      fun ⟨h1',h2'⟩=>⟨h1',fun s' _ hlt=>h2' s' hlt⟩⟩
def dg {nIn B:ℕ} (c:CB nIn) {fu:(Fin nIn->Bool)->Fin B->Bool}
  (u:Q2 nIn c B fu) :
  Q0 nIn c (B*(2*B)) (fun c'=>Q2 nIn c' B (fun x=>qV (fu x))):=
 j8 (Bstep:=2*B) B (fun x s=>qV (fu x) s) c fun s c0 h0=>
  Q0.weaken (by omega)<|
  let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=
   Q4 nIn c1 (fun x=>decide (fu x s=true/\∀ s':Fin B,s'.val < t->s'.val < s.val->fu x s'=false))
  have hinit:Acc 0 (Nat.zero_le B) c0:=((u.at s).lift h0).cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [dG]
   exact ⟨fun h=>⟨h,fun _ ht=>absurd ht (by omega)⟩,fun h=>h.1⟩
  (Q0.qe (Bstep:=2) B Acc c0 hinit fun t ht c1 h1 acc=>
   let st:Fin B:=⟨t,ht⟩
   if hlt:t < s.val then
    (y2 c1 ((u.at st).lift (h0.trans h1))).bind fun c2 h2 vnu=>
    (vg c2 (acc.lift h2) vnu).bind fun _ _ vand=>
    Q0.pure<|vand.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp only [dI,Bool.not_eq_true',dG]
     constructor
     ·rintro ⟨⟨h1',h2'⟩,h3'⟩
      refine ⟨h1',fun s' hs' hls=>?_⟩
      by_cases hl:s'.val < t
      ·exact h2' s' hl hls
      ·have heq:s'=st:=Fin.ext (by dsimp [st];omega);subst heq;exact h3'
     ·rintro ⟨h1',h2'⟩
      exact ⟨⟨h1',fun s' hs' hls=>h2' s' (by omega) hls⟩,h2' st (by dsimp [st];omega) hlt⟩
   else
    Q0.weaken (by omega)<|
    Q0.pure<|acc.cast fun x=>by
     apply Bool.eq_iff_iff.mpr;simp only [dG]
     constructor
     ·rintro ⟨h1',h2'⟩;exact ⟨h1',fun s' hs' hls=>h2' s' (by omega) hls⟩
     ·rintro ⟨h1',h2'⟩;exact ⟨h1',fun s' hs' hls=>h2' s' (by omega) hls⟩).bind fun _ _ vF=>
  Q0.pure<|vF.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [qV,dG]
   exact ⟨fun ⟨h1',h2'⟩=>⟨h1',fun s' hls=>h2' s' s'.isLt hls⟩,
      fun ⟨h1',h2'⟩=>⟨h1',fun s' _ hls=>h2' s' hls⟩⟩
def gG {nIn B:ℕ} (c:CB nIn) {foh fv:(Fin nIn->Bool)->Fin B->Bool}
  (oh:Q2 nIn c B foh) (v:Q2 nIn c B fv) :
  Q0 nIn c (1+B*2) (fun c'=>Q4 nIn c' (fun x=>decide (∃ s:Fin B,foh x s=true/\fv x s=true))):=
 Q0.weaken (by omega)<|
 (vJ c false).bind fun c0 h0 vf=>
 let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=
  Q4 nIn c1 (fun x=>decide (∃ s:Fin B,s.val < t/\foh x s=true/\fv x s=true))
 have hinit:Acc 0 (Nat.zero_le B) c0:=vf.cast fun _=>by simp
 (Q0.qe (Bstep:=2) B Acc c0 hinit fun t ht c1 h1 acc=>
  let st:Fin B:=⟨t,ht⟩
  let h01:=h0.trans h1
  (vg c1 ((oh.at st).lift h01) ((v.at st).lift h01)).bind fun c2 h2 vand=>
  (yr c2 (acc.lift h2) vand).bind fun _ _ vor=>
  Q0.pure<|vor.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [dH,dI,dG]
   constructor
   ·rintro (⟨s,hs,h1',h2'⟩ | ⟨h1',h2'⟩)
    ·exact ⟨s,by omega,h1',h2'⟩
    ·exact ⟨st,by dsimp [st];omega,h1',h2'⟩
   ·rintro ⟨s,hs,h1',h2'⟩
    by_cases hlt:s.val < t
    ·left;exact ⟨s,hlt,h1',h2'⟩
    ·right;have heq:s=st:=Fin.ext (by dsimp [st];omega);subst heq;exact ⟨h1',h2'⟩).bind fun _ _ vF=>
 Q0.pure<|vF.cast fun x=>by
  apply Bool.eq_iff_iff.mpr;simp only [dG]
  exact ⟨fun ⟨s,_,h1',h2'⟩=>⟨s,h1',h2'⟩,fun ⟨s,h1',h2'⟩=>⟨s,s.isLt,h1',h2'⟩⟩
def gL {nIn k B:ℕ} (c:CB nIn)
  {fM:(Fin nIn->Bool)->Ql k B} {fu fv:(Fin nIn->Bool)->Fin B->Bool}
  (M:Qo nIn c k B fM) (uOH:Q2 nIn c B fu) (vOH:Q2 nIn c B fv) :
  Q0 nIn c (k*(2+12*B))
   (fun c'=>Qo nIn c' k B (fun x=>y7 (fM x) (fu x) (fv x))):=
 let Acc (t:ℕ) (_:t ≤ k) (c1:CB nIn):Type:=
  ∀ z:Fin k,z.val < t->Q2 nIn c1 B (fun x=>y7 (fM x) (fu x) (fv x) z)
 have hinit:Acc 0 (Nat.zero_le k) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=2+12*B) k Acc c hinit fun t ht c1 h1 acc=>
  Q0.weaken (by omega)<|
  let zt:Fin k:=⟨t,ht⟩
  (gG c1 (vOH.lift h1) ((M.rows zt).lift h1)).bind fun c2 h2 valV=>
  (gG c2 (uOH.lift (h1.trans h2)) ((M.rows zt).lift (h1.trans h2))).bind fun c3 h3 valU=>
  let h13:=h1.trans (h2.trans h3)
  (j8 (Bstep:=8) B (fun x s=>y7 (fM x) (fu x) (fv x) zt s) c3 fun s c4 h4=>
   Q0.weaken (by omega)<|
   let h14:=h13.trans h4
   (ds c4 ((vOH.at s).lift h14) (valU.lift h4) (((M.rows zt).at s).lift h14)).bind fun c5 h5 m1=>
   (ds c5 ((uOH.at s).lift (h14.trans h5)) (valV.lift (h3.trans (h4.trans h5))) m1).bind fun _ _ m2=>
   Q0.pure<|m2.cast fun _=>rfl).bind fun _ h4 vrow=>
  let hall:=h2.trans (h3.trans h4)
  Q0.pure fun z hz=>
   if hlt:z.val < t then (acc z hlt).lift hall
   else
    have heq:z=zt:=Fin.ext (by dsimp [zt];omega)
    heq▸vrow).bind fun _ _ all=>
 Q0.pure ⟨fun z=>all z z.isLt⟩
def Qg (k B:ℕ):ℕ:=
 B*(1+k)+B*(1+B)+B*4
def gy {nIn k B:ℕ} (c:CB nIn)
  {fM:(Fin nIn->Bool)->Ql k B} {fcond:(Fin nIn->Bool)->Bool}
  (M:Qo nIn c k B fM) (z:Fin k) (cond:Q4 nIn c fcond) :
  Q0 nIn c (Qg k B)
   (fun c'=>Q2 nIn c' B (fun x=>qO (q7 (fM x))) ×
        Qo nIn c' k B (fun x=>qn (fM x) z (fcond x))):=
 Q0.weaken (by unfold Qg;omega)<|
 (gk c M).bind fun c1 h1 vu=>
 (di c1 vu).bind fun c2 h2 voh=>
 let h12:=h1.trans h2
 (vd c2 (cond.lift h12) voh ((M.rows z).lift h12)).bind fun _ h3 vrow=>
 Q0.pure
  ⟨voh.lift h3,
  ⟨fun z'=>
   if ez:z'=z then
    vrow.cast fun x s=>by subst ez;unfold qn;by_cases h:fcond x=true <;> simp [h]
   else
    ((M.rows z').lift (h12.trans h3)).cast fun x s=>by unfold qn;by_cases h:fcond x=true <;> simp [h,ez]⟩⟩
def Qe (k B:ℕ):ℕ:=
 B*(1+k)+B*(2*B)+B+k*(2+12*B)+k*(4*B)
def gb {nIn k B:ℕ} (c:CB nIn)
  {fM:(Fin nIn->Bool)->Ql k B} {fcond:(Fin nIn->Bool)->Bool}
  (M:Qo nIn c k B fM) (z:Fin k) (cond:Q4 nIn c fcond) :
  Q0 nIn c (Qe k B)
   (fun c'=>Q2 nIn c' B (fun x=>qV (q7 (fM x))) ×
        Qo nIn c' k B (fun x=>qA (fM x) z (fcond x))):=
 Q0.weaken (by unfold Qe;omega)<|
 (gk c M).bind fun c1 h1 vu=>
 (dg c1 vu).bind fun c2 h2 vlo=>
 (vq c2 B (fun _=>false)).bind fun c3 h3 vfz=>
 let h13:=h1.trans (h2.trans h3)
 let M1:Qo nIn c3 k B (fun x z' s=>if z'=z then false else fM x z' s):=
  ⟨fun z'=>if ez:z'=z then vfz.cast (fun _ _=>by simp [ez])
       else ((M.rows z').lift h13).cast (fun _ _=>by simp [ez])⟩
 (gL c3 M1 ((M.rows z).lift h13) (vlo.lift h3)).bind fun c4 h4 Msw=>
 let h14:=h13.trans h4
 let Acc (t:ℕ) (_:t ≤ k) (c5:CB nIn):Type:=
  ∀ z':Fin k,z'.val < t->Q2 nIn c5 B (fun x=>qA (fM x) z (fcond x) z')
 have hinit:Acc 0 (Nat.zero_le k) c4:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=4*B) k Acc c4 hinit fun t ht c5 h5 acc=>
  Q0.weaken (by omega)<|
  let zt:Fin k:=⟨t,ht⟩
  (vd c5 (cond.lift (h14.trans h5)) ((Msw.rows zt).lift h5) ((M.rows zt).lift (h14.trans h5))).bind fun _ h6 vr=>
  Q0.pure fun z' hz'=>
   if hlt:z'.val < t then (acc z' hlt).lift h6
   else
    have heq:z'=zt:=Fin.ext (by dsimp [zt];omega)
    heq▸vr.cast fun x s=>by unfold qA;by_cases h:fcond x=true <;> simp [h]).bind fun _ h5 all=>
 Q0.pure ⟨vlo.lift (h3.trans (h4.trans h5)),⟨fun z'=>all z' z'.isLt⟩⟩
def Qw (B W:ℕ):ℕ:=
 W+B*(5+2^B*(8*W))
def d0 {nIn B W:ℕ} (c:CB nIn)
  {fcond ffix fval:(Fin nIn->Bool)->Bool} {foh:(Fin nIn->Bool)->Fin B->Bool}
  {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (cond:Q4 nIn c fcond) (oh:Q2 nIn c B foh)
  (fix:Q4 nIn c ffix) (val:Q4 nIn c fval) (D:SDP nIn c B W fD) :
  Q0 nIn c (Qw B W)
   (fun c'=>SDP nIn c' B W (fun x=>qY B (fcond x) (foh x) (ffix x) (fval x) (fD x))):=
 Q0.weaken (by unfold Qw;omega)<|
 (qS c W 0 (Nat.two_pow_pos W)).bind fun c0 h0 vzero=>
 let stAt (t:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
  ((dF B).take t).foldl
   (fun tbl s=>if fcond x&&foh x s then jm B s (ffix x) (fval x) tbl else tbl) (fD x)
 let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=SDP nIn c1 B W (stAt t)
 have hinit:Acc 0 (Nat.zero_le B) c0:=(D.lift h0).cast (fun _ _=>rfl)
 (Q0.qe (Bstep:=5+2^B*(8*W)) B Acc c0 hinit fun t ht c1 h1 Dc=>
  Q0.weaken (by omega)<|
  let st:Fin B:=⟨t,ht⟩
  let h01:=h0.trans h1
  (vg c1 (cond.lift h01) ((oh.at st).lift h01)).bind fun c2 h2 vcs=>
  (y2 c2 (fix.lift (h01.trans h2))).bind fun c3 h3 vnfix=>
  (y2 c3 (val.lift (h01.trans (h2.trans h3)))).bind fun c4 h4 vnval=>
  (yr c4 (vnfix.lift h4) vnval).bind fun c5 h5 vallowF=>
  (yr c5 (vnfix.lift (h4.trans h5)) (val.lift (h01.trans (h2.trans (h3.trans (h4.trans h5)))))).bind fun c6 h6 vallowT=>
  let h16:=h2.trans (h3.trans (h4.trans (h5.trans h6)))
  let h06:=h01.trans h16
  let IAcc (u:ℕ) (_:u ≤ 2^B) (c7:CB nIn):Type:=
   ∀ idx:Fin (2^B),idx.val < u ->
    Q9 nIn c7 W (fun x=>
     if fcond x&&foh x st then jm B st (ffix x) (fval x) (stAt t x) idx else stAt t x idx)
  have hIinit:IAcc 0 (Nat.zero_le _) c6:=fun _ h=>absurd h (by omega)
  (Q0.qe (Bstep:=8*W) (2^B) IAcc c6 hIinit fun u hu c7 h7 iacc=>
   let iu:Fin (2^B):=⟨u,hu⟩
   if hbit:v8 B iu st=true then
    Q0.weaken (by omega)<|
    let base:=(Dc.tbl (jw iu st)).lift (h16.trans h7)
    (vH c7 (vallowT.lift h7) base (vzero.lift (h1.trans (h16.trans h7)))).bind fun c8 h8 vres=>
    (vH c8 (vcs.lift (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8)))))) vres
     ((Dc.tbl iu).lift (h16.trans (h7.trans h8)))).bind fun _ h9 vout=>
    Q0.pure fun idx hidx=>
     if hlt:idx.val < u then (iacc idx hlt).lift (h8.trans h9)
     else
      have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
      heq▸vout.cast fun x=>by
       dsimp only [jm];rw [hbit]
       cases hc:fcond x&&foh x st <;> cases hfx:ffix x <;> cases hvl:fval x <;> simp [hc,hfx,hvl]
   else
    Q0.weaken (by omega)<|
    let base:=(Dc.tbl iu).lift (h16.trans h7)
    (vH c7 (vallowF.lift (h6.trans h7)) base (vzero.lift (h1.trans (h16.trans h7)))).bind fun c8 h8 vres=>
    (vH c8 (vcs.lift (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8)))))) vres
     ((Dc.tbl iu).lift (h16.trans (h7.trans h8)))).bind fun _ h9 vout=>
    Q0.pure fun idx hidx=>
     if hlt:idx.val < u then (iacc idx hlt).lift (h8.trans h9)
     else
      have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
      heq▸vout.cast fun x=>by
       have hbf:v8 B iu st=false:=Bool.eq_false_iff.mpr hbit
       dsimp only [jm];rw [hbf]
       cases hc:fcond x&&foh x st <;> cases hfx:ffix x <;> cases hvl:fval x <;> simp [hc,hfx,hvl]).bind fun _ _ all=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [st]:=by
   rw [dJ (by simp;omega)];simp [st]
  Q0.pure ⟨fun idx=>(all idx idx.isLt).cast fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   by_cases h:(fcond x&&foh x st)=true <;> simp [h]⟩).bind fun _ _ DF=>
 Q0.pure<|DF.cast fun x idx=>by
  simp only [stAt,qY,show (dF B).take B=dF B by simp]
def gf {nIn B W:ℕ} (c:CB nIn) (t:Fin B)
  {ffl:(Fin nIn->Bool)->Fin (2^B)->Bool} {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (fl:Q2 nIn c (2^B) ffl) (D:SDP nIn c B W fD) :
  Q0 nIn c (2^B*(4*W))
   (fun c'=>SDP nIn c' B W (fun x=>vh B t (ffl x) (fD x))):=
 let Acc (u:ℕ) (_:u ≤ 2^B) (c1:CB nIn):Type:=
  ∀ idx:Fin (2^B),idx.val < u->Q9 nIn c1 W (fun x=>vh B t (ffl x) (fD x) idx)
 have hinit:Acc 0 (Nat.zero_le _) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=4*W) (2^B) Acc c hinit fun u hu c1 h1 acc=>
  Q0.weaken (by omega)<|
  let iu:Fin (2^B):=⟨u,hu⟩
  (vH c1 ((fl.at iu).lift h1) ((D.tbl (jw iu t)).lift h1) ((D.tbl iu).lift h1)).bind fun _ h2 vnew=>
  Q0.pure fun idx hidx=>
   if hlt:idx.val < u then (acc idx hlt).lift h2
   else
    have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
    heq▸vnew.cast fun _=>rfl).bind fun _ _ all=>
 Q0.pure ⟨fun idx=>all idx idx.isLt⟩
def Qn (B W:ℕ):ℕ:=
 W+B*(1+2^B*(1+15*W))
def gR {nIn B k:ℕ} (c:CB nIn)
  {fcond:(Fin nIn->Bool)->Bool} {foh:(Fin nIn->Bool)->Fin B->Bool}
  {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (cond:Q4 nIn c fcond) (oh:Q2 nIn c B foh) (D:SDP nIn c B (k+1) fD) :
  Q0 nIn c (Qn B (k+1))
   (fun c'=>SDP nIn c' B (k+1) (fun x=>qZ B k (fcond x) (foh x) (fD x))):=
 Q0.weaken (by unfold Qn;omega)<|
 (qS c (k+1) 0 (Nat.two_pow_pos _)).bind fun c0 h0 vzero=>
 let stAt (t:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
  ((dF B).take t).foldl
   (fun tbl s=>if fcond x&&foh x s then j9 B k s tbl else tbl) (fD x)
 let Acc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=SDP nIn c1 B (k+1) (stAt t)
 have hinit:Acc 0 (Nat.zero_le B) c0:=(D.lift h0).cast (fun _ _=>rfl)
 (Q0.qe (Bstep:=1+2^B*(1+15*(k+1))) B Acc c0 hinit fun t ht c1 h1 Dc=>
  Q0.weaken (by omega)<|
  let st:Fin B:=⟨t,ht⟩
  let h01:=h0.trans h1
  (vg c1 (cond.lift h01) ((oh.at st).lift h01)).bind fun c2 h2 vcs=>
  let IAcc (u:ℕ) (_:u ≤ 2^B) (c3:CB nIn):Type:=
   ∀ idx:Fin (2^B),idx.val < u ->
    Q9 nIn c3 (k+1) (fun x=>
     if fcond x&&foh x st then j9 B k st (stAt t x) idx else stAt t x idx)
  have hIinit:IAcc 0 (Nat.zero_le _) c2:=fun _ h=>absurd h (by omega)
  (Q0.qe (Bstep:=1+15*(k+1)) (2^B) IAcc c2 hIinit fun u hu c3 h3 iacc=>
   let iu:Fin (2^B):=⟨u,hu⟩
   if hbit:v8 B iu st=false then
    Q0.weaken (by omega)<|
    (gT c3 ((Dc.tbl iu).lift (h2.trans h3)) ((Dc.tbl (jw iu st)).lift (h2.trans h3))).bind fun c4 h4 vsum=>
    (vH c4 (vcs.lift (h3.trans h4)) vsum ((Dc.tbl iu).lift (h2.trans (h3.trans h4)))).bind fun _ h5 vout=>
    Q0.pure fun idx hidx=>
     if hlt:idx.val < u then (iacc idx hlt).lift (h4.trans h5)
     else
      have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
      heq▸vout.cast fun x=>by dsimp only [j9];simp [hbit]
   else
    Q0.weaken (by omega)<|
    (vH c3 (vcs.lift h3) (vzero.lift (h1.trans (h2.trans h3))) ((Dc.tbl iu).lift (h2.trans h3))).bind fun _ h4 vout=>
    Q0.pure fun idx hidx=>
     if hlt:idx.val < u then (iacc idx hlt).lift h4
     else
      have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
      heq▸vout.cast fun x=>by dsimp only [j9];simp [hbit]).bind fun _ _ all=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [st]:=by
   rw [dJ (by simp;omega)];simp [st]
  Q0.pure ⟨fun idx=>(all idx idx.isLt).cast fun x=>by
   simp only [stAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   by_cases h:(fcond x&&foh x st)=true <;> simp [h]⟩).bind fun _ _ DF=>
 Q0.pure<|DF.cast fun x idx=>by
  simp only [stAt,qZ,show (dF B).take B=dF B by simp]
def Qr (B W:ℕ):ℕ:=
 B*(B*(2+2^B*(4*W)))
def ge {nIn B W:ℕ} (c:CB nIn)
  {fcond:(Fin nIn->Bool)->Bool} {fu fv:(Fin nIn->Bool)->Fin B->Bool}
  {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (cond:Q4 nIn c fcond) (uOH:Q2 nIn c B fu) (vOH:Q2 nIn c B fv)
  (D:SDP nIn c B W fD) :
  Q0 nIn c (Qr B W)
   (fun c'=>SDP nIn c' B W (fun x=>qI B (fcond x) (fu x) (fv x) (fD x))):=
 Q0.weaken (by unfold Qr;omega)<|
 let outAt (t:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
  ((dF B).take t).foldl (fun D0 u=>
   (dF B).foldl (fun D1 v=>
    if fcond x&&fu x u&&fv x v then (fun idx=>D1 (vY idx u v)) else D1) D0) (fD x)
 let OAcc (t:ℕ) (_:t ≤ B) (c1:CB nIn):Type:=SDP nIn c1 B W (outAt t)
 have hOinit:OAcc 0 (Nat.zero_le B) c:=D.cast (fun _ _=>rfl)
 (Q0.qe (Bstep:=B*(2+2^B*(4*W))) B OAcc c hOinit fun t ht c1 h1 Do=>
  let ut:Fin B:=⟨t,ht⟩
  let inAt (s:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
   ((dF B).take s).foldl (fun D1 v=>
    if fcond x&&fu x ut&&fv x v then (fun idx=>D1 (vY idx ut v)) else D1) (outAt t x)
  let IAcc (s:ℕ) (_:s ≤ B) (c2:CB nIn):Type:=SDP nIn c2 B W (inAt s)
  have hIinit:IAcc 0 (Nat.zero_le B) c1:=Do.cast (fun _ _=>rfl)
  (Q0.qe (Bstep:=2+2^B*(4*W)) B IAcc c1 hIinit fun s hs c2 h2 Di=>
   Q0.weaken (by omega)<|
   let vs:Fin B:=⟨s,hs⟩
   let h02:=h1.trans h2
   (vg c2 (cond.lift h02) ((uOH.at ut).lift h02)).bind fun c3 h3 vc1=>
   (vg c3 vc1 ((vOH.at vs).lift (h02.trans h3))).bind fun c4 h4 vc2=>
   (g5 c4 ut vs vc2 (Di.lift (h3.trans h4))).bind fun _ _ D'=>
   have htake:(dF B).take (s+1)=(dF B).take s ++ [vs]:=by
    rw [dJ (by simp;omega)];simp [vs]
   Q0.pure<|D'.cast fun x idx=>by
    simp only [inAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    by_cases h:(fcond x&&fu x ut&&fv x vs)=true <;> simp [h]).bind fun _ _ DiF=>
  have htake:(dF B).take (t+1)=(dF B).take t ++ [ut]:=by
   rw [dJ (by simp;omega)];simp [ut]
  Q0.pure<|DiF.cast fun x idx=>by
   simp only [outAt,inAt,htake,List.foldl_append,List.foldl_cons,List.foldl_nil,
    show (dF B).take B=dF B by simp]).bind fun _ _ DF=>
 Q0.pure<|DF.cast fun x idx=>by
  simp only [outAt,qI,show (dF B).take B=dF B by simp]
def dB {nIn B W:ℕ} (c:CB nIn)
  {fkeep:(Fin nIn->Bool)->Fin (2^B)->Bool} {fD:(Fin nIn->Bool)->Fin (2^B)->ℕ}
  (keep:Q2 nIn c (2^B) fkeep) (D:SDP nIn c B W fD) :
  Q0 nIn c (W+2^B*(4*W))
   (fun c'=>SDP nIn c' B W (fun x=>zE B (fkeep x) (fD x))):=
 Q0.weaken (by omega)<|
 (qS c W 0 (Nat.two_pow_pos W)).bind fun c0 h0 vzero=>
 let Acc (u:ℕ) (_:u ≤ 2^B) (c1:CB nIn):Type:=
  ∀ idx:Fin (2^B),idx.val < u->Q9 nIn c1 W (fun x=>zE B (fkeep x) (fD x) idx)
 have hinit:Acc 0 (Nat.zero_le _) c0:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=4*W) (2^B) Acc c0 hinit fun u hu c1 h1 acc=>
  Q0.weaken (by omega)<|
  let iu:Fin (2^B):=⟨u,hu⟩
  let h01:=h0.trans h1
  (vH c1 ((keep.at iu).lift h01) ((D.tbl iu).lift h01) (vzero.lift h1)).bind fun _ h2 vnew=>
  Q0.pure fun idx hidx=>
   if hlt:idx.val < u then (acc idx hlt).lift h2
   else
    have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
    heq▸vnew.cast fun _=>rfl).bind fun _ _ all=>
 Q0.pure ⟨fun idx=>all idx idx.isLt⟩
def gz {nIn k:ℕ} (c:CB nIn)
  {fpool ffix:(Fin nIn->Bool)->Fin k->Bool} {fval:(Fin nIn->Bool)->ℕ}
  (poolAll:Q2 nIn c k fpool) (prefFix:Q2 nIn c k ffix) (val:Q9 nIn c (k+1) fval) :
  Q0 nIn c (k*(4+15*(k+1)))
   (fun c'=>Q9 nIn c' (k+1) (fun x=>ym k (fpool x) (ffix x) (fval x))):=
 let stAt (t:ℕ) (x:Fin nIn->Bool):ℕ:=
  ((dF k).take t).foldl
   (fun acc z=>if !fpool x z&&!ffix x z then (acc+acc) % 2^(k+1) else acc) (fval x)
 let Acc (t:ℕ) (_:t ≤ k) (c1:CB nIn):Type:=Q9 nIn c1 (k+1) (stAt t)
 have hinit:Acc 0 (Nat.zero_le k) c:=val.cast (fun _=>rfl)
 Q0.weaken (by omega)<|
 (Q0.qe (Bstep:=4+15*(k+1)) k Acc c hinit fun t ht c1 h1 acc=>
  Q0.weaken (by omega)<|
  let zt:Fin k:=⟨t,ht⟩
  have htake:(dF k).take (t+1)=(dF k).take t ++ [zt]:=by
   rw [dJ (by simp;omega)];simp [zt]
  have hstep:∀ x,stAt (t+1) x =
    if (!fpool x zt&&!ffix x zt)=true then (stAt t x+stAt t x) % 2^(k+1) else stAt t x:=fun x=>by
   change ((dF k).take (t+1)).foldl _ _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  (y2 c1 ((poolAll.at zt).lift h1)).bind fun c2 h2 vnp=>
  (y2 c2 ((prefFix.at zt).lift (h1.trans h2))).bind fun c3 h3 vnf=>
  (vg c3 (vnp.lift h3) vnf).bind fun c4 h4 vcond=>
  let h14:=h2.trans (h3.trans h4)
  (gT c4 (acc.lift h14) (acc.lift h14)).bind fun c5 h5 vdbl=>
  (vH c5 (vcond.lift h5) vdbl (acc.lift (h14.trans h5))).bind fun _ _ vnew=>
  Q0.pure<|vnew.cast fun x=>(hstep x).symm).bind fun _ _ vF=>
 Q0.pure<|vF.cast fun x=>by
  simp only [stAt,ym,show (dF k).take k=dF k by simp]
def qy {k m:ℕ} (r b:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k)
  (i:Fin k) (u:ℕ):Ql k (b+2):=
 ((dF k).take u).foldl (fun Mc z=>
  qn Mc z (decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val)))
  (qt r b Ab Bb o i.val)
def ql {k m:ℕ} (r b:ℕ) (Ab Bb:Fin k->Q1 m) (o:Fin k->Fin k)
  (i:Fin k) (u:ℕ):Ql k (b+2):=
 ((dF k).take u).foldl (fun Mc z=>
  qA Mc z (decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))))
  (qB r b Ab Bb o i (qt r b Ab Bb o i.val))
def jz {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (y:Q1 m) (o:Fin k->Fin k)
  (i:Fin k) (t:Fin (b+2)) (idx:Fin (2^(b+2))):Bool:=
 let TM:=j7 Ab Bb o i
 let cdy:=qf TM (q5 (qF Ab Bb y o i.val) (qF Ab Bb y o (i.val+1))) (b+2)
 let cA:=qf TM (Ab (o i)) (b+2)
 let cB:=qf TM (Bb (o i)) (b+2)
 xor (cdy t) (xor (cA t&&jB b Ab Bb nr cr o i idx) (cB t&&jA b Ab Bb nc cc o i idx))
lemma g8 {k r m:ℕ} (b:ℕ) (Ab Bb:Fin k->Q1 m) (nr nc:Fin (2^k))
  (cr cc:Fin r->Fin (2^k)) (y:Q1 m) (o:Fin k->Fin k)
  (prefFix prefVal:Fin k->Bool) (i:Fin k) (DP:Fin (2^(b+2))->ℕ) :
  let B:=b+2
  let TM:=j7 Ab Bb o i
  let DP1:=jZ (qk (vL Ab Bb o i.val) TM B) DP
  let DP2:=(dF k).foldl (fun D z=>
   qY B (decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val))
    (qO (q7 (qy r b Ab Bb o i z.val))) (prefFix z) (prefVal z) D) DP1
  let DP3:=(dF B).foldl (fun D t=>
   vh B t (jz b Ab Bb nr nc cr cc y o i t) D) DP2
  let DP4:=(dF k).foldl (fun D z=>
   let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))
   let Mz:=ql r b Ab Bb o i z.val
   qI B cond (Mz z) (qV (q7 Mz)) (qZ B k cond (Mz z) D)) DP3
  let DP5:=zE B (vP b Ab Bb o i) DP4
  zD b Ab Bb nr nc cr cc y o prefFix prefVal i DP =
   jZ (j1 (qk (vL Ab Bb o (i.val+1)) TM B)) DP5:=by
 dsimp only [zD]
 let B:=b+2
 let TM:=j7 Ab Bb o i
 let DP1:=jZ (qk (vL Ab Bb o i.val) TM B) DP
 have hst2:∀ u ≤ k,
   let st:=((dF k).take u).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
    let cond:=decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val)
    (qn st.1 z cond,qY B cond (qO (q7 st.1)) (prefFix z) (prefVal z) st.2))
    (qt r b Ab Bb o i.val,DP1)
   st.1=qy r b Ab Bb o i u /\
   st.2=((dF k).take u).foldl (fun D z=>
    qY B (decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val))
     (qO (q7 (qy r b Ab Bb o i z.val))) (prefFix z) (prefVal z) D) DP1:=by
  intro u;induction u with
  | zero=>intro _;exact ⟨rfl,rfl⟩
  | succ u ih=>
   intro hu
   obtain ⟨h1,h2⟩:=ih (Nat.le_of_succ_le hu)
   have htu:(dF k).take (u+1)=(dF k).take u ++ [⟨u,hu⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only;rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil,
    List.foldl_append,List.foldl_cons,List.foldl_nil]
   refine ⟨?_,?_⟩
   ·rw [h1];symm;unfold qy;rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil]
   ·rw [h1,h2]
 have hktake:(dF k).take k=dF k:=by simp
 obtain ⟨h2M,h2D⟩:=hst2 k le_rfl
 rw [hktake] at h2M h2D
 have h2M':qy r b Ab Bb o i k=qB r b Ab Bb o i (qt r b Ab Bb o i.val):=by
  unfold qy qB;rw [hktake]
 rw [h2M'] at h2M
 let DP3:=(dF B).foldl (fun D t=>vh B t (jz b Ab Bb nr nc cr cc y o i t) D)
  ((dF k).foldl (fun D z=>
   qY B (decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val))
    (qO (q7 (qy r b Ab Bb o i z.val))) (prefFix z) (prefVal z) D) DP1)
 have hst4:∀ u ≤ k,
   let st:=((dF k).take u).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
    let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))
    let loOH:=qV (q7 st.1)
    (qA st.1 z cond,qI B cond (st.1 z) loOH (qZ B k cond (st.1 z) st.2)))
    (qB r b Ab Bb o i (qt r b Ab Bb o i.val),DP3)
   st.1=ql r b Ab Bb o i u /\
   st.2=((dF k).take u).foldl (fun D z=>
    let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))
    let Mz:=ql r b Ab Bb o i z.val
    qI B cond (Mz z) (qV (q7 Mz)) (qZ B k cond (Mz z) D)) DP3:=by
  intro u;induction u with
  | zero=>intro _;exact ⟨rfl,rfl⟩
  | succ u ih=>
   intro hu
   obtain ⟨h1,h2⟩:=ih (Nat.le_of_succ_le hu)
   have htu:(dF k).take (u+1)=(dF k).take u ++ [⟨u,hu⟩]:=by
    rw [dJ (by simp;omega)];simp
   dsimp only;rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil,
    List.foldl_append,List.foldl_cons,List.foldl_nil]
   refine ⟨?_,?_⟩
   ·rw [h1];symm;unfold ql;rw [htu,List.foldl_append,List.foldl_cons,List.foldl_nil]
   ·rw [h1,h2]
 obtain ⟨_,h4D⟩:=hst4 k le_rfl
 rw [hktake] at h4D
 change jZ (j1 (qk (vL Ab Bb o (i.val+1)) TM B))
  (zE B (vP b Ab Bb o i)
   (((dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
    let cond:=decide (z∈Qi r Ab Bb o i)&&!decide (z∈Q5 r Ab Bb o (i.val+1))
    let loOH:=qV (q7 st.1)
    (qA st.1 z cond,qI B cond (st.1 z) loOH (qZ B k cond (st.1 z) st.2)))
    (((dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
     let cond:=decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val)
     (qn st.1 z cond,qY B cond (qO (q7 st.1)) (prefFix z) (prefVal z) st.2))
     (qt r b Ab Bb o i.val,DP1)).1,
    (dF B).foldl (fun D t=>vh B t (jz b Ab Bb nr nc cr cc y o i t) D)
     (((dF k).foldl (fun (st:Ql k B × (Fin (2^B)->ℕ)) z=>
      let cond:=decide (z∈qq r Ab Bb (o i))&&!decide (z∈Q5 r Ab Bb o i.val)
      (qn st.1 z cond,qY B cond (qO (q7 st.1)) (prefFix z) (prefVal z) st.2))
      (qt r b Ab Bb o i.val,DP1)).2))).2))=_
 rw [h2M,h2D]
 exact congrArg (jZ _ ∘ zE _ _) h4D
structure Qp (nIn:ℕ) (c:CB nIn) {k r m:ℕ} (b:ℕ)
  (fA fB:(Fin nIn->Bool)->Fin k->Q1 m)
  (fnr fnc:(Fin nIn->Bool)->Fin (2^k))
  (fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k))
  (fy:(Fin nIn->Bool)->Q1 m)
  (fo:(Fin nIn->Bool)->Fin k->Fin k) where
 okAll:Q4 nIn c (fun x=>jT (fA x) (fB x) (fy x) (fo x))
 poolAll:Q2 nIn c k (fun x=>y9 r (fA x) (fB x) (vQ (fo x) k))
 Gin:∀ i:Fin k,Qv nIn c (b+2)
  (fun x=>qk (vL (fA x) (fB x) (fo x) i.val) (j7 (fA x) (fB x) (fo x) i) (b+2))
 GoutInv:∀ i:Fin k,Qv nIn c (b+2)
  (fun x=>j1 (qk (vL (fA x) (fB x) (fo x) (i.val+1)) (j7 (fA x) (fB x) (fo x) i) (b+2)))
 introCond:∀ i:Fin k,Q2 nIn c k
  (fun x z=>decide (z∈qq r (fA x) (fB x) (fo x i))&&!decide (z∈Q5 r (fA x) (fB x) (fo x) i.val))
 introOH:∀ i:Fin k,∀ z:Fin k,Q2 nIn c (b+2)
  (fun x=>qO (q7 (qy r b (fA x) (fB x) (fo x) i z.val)))
 flArr:∀ i:Fin k,∀ t:Fin (b+2),Q2 nIn c (2^(b+2))
  (fun x idx=>jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) i t idx)
 forgetCond:∀ i:Fin k,Q2 nIn c k
  (fun x z=>decide (z∈Qi r (fA x) (fB x) (fo x) i)&&!decide (z∈Q5 r (fA x) (fB x) (fo x) (i.val+1)))
 forgetSOH:∀ i:Fin k,∀ z:Fin k,Q2 nIn c (b+2)
  (fun x=>ql r b (fA x) (fB x) (fo x) i z.val z)
 forgetLoOH:∀ i:Fin k,∀ z:Fin k,Q2 nIn c (b+2)
  (fun x=>qV (q7 (ql r b (fA x) (fB x) (fo x) i z.val)))
 keepArr:∀ i:Fin k,Q2 nIn c (2^(b+2))
  (fun x idx=>vP b (fA x) (fB x) (fo x) i idx)
def Qp.lift {nIn k r m b:ℕ} {c c':CB nIn}
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fnr fnc:(Fin nIn->Bool)->Fin (2^k)}
  {fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (h:c.Qa c') (P:Qp nIn c b fA fB fnr fnc fcr fcc fy fo) :
  Qp nIn c' b fA fB fnr fnc fcr fcc fy fo:=
 ⟨P.okAll.lift h,P.poolAll.lift h,fun i=>(P.Gin i).lift h,fun i=>(P.GoutInv i).lift h,
 fun i=>(P.introCond i).lift h,fun i z=>(P.introOH i z).lift h,fun i t=>(P.flArr i t).lift h,
 fun i=>(P.forgetCond i).lift h,fun i z=>(P.forgetSOH i z).lift h,
 fun i z=>(P.forgetLoOH i z).lift h,fun i=>(P.keepArr i).lift h⟩
structure Qu (nIn:ℕ) (c:CB nIn) {k m:ℕ} (r:ℕ)
  (fA fB:(Fin nIn->Bool)->Fin k->Q1 m) (fy:(Fin nIn->Bool)->Q1 m)
  (fo:(Fin nIn->Bool)->Fin k->Fin k) where
 TL:∀ s:Fin (k+1),Q8 nIn c m (fun x=>yH (fA x) (fB x) (fo x) s.val)
 TR:∀ s:Fin (k+1),Q8 nIn c m (fun x=>yg (fA x) (fB x) (fo x) s.val)
 Ti:∀ s:Fin (k+1),Q8 nIn c m (fun x=>vL (fA x) (fB x) (fo x) s.val)
 Ly:∀ s:Fin (k+1),Q2 nIn c m (fun x=>qF (fA x) (fB x) (fy x) (fo x) s.val)
 Fm:∀ s:Fin (k+1),Q2 nIn c k (fun x z=>decide (z∈Q5 r (fA x) (fB x) (fo x) s.val))
 okAll:Q4 nIn c (fun x=>jT (fA x) (fB x) (fy x) (fo x))
 poolAll:Q2 nIn c k (fun x=>y9 r (fA x) (fB x) (vQ (fo x) k))
def Qm (k m:ℕ):ℕ:=
 k*(1+k)+k*(1+k)+Qs k m+Qs k m +
 (3*(m*m)+m*(56*m*m+11*m))+(24*m*m+10*m+2) +
 k*(1+k*2)+k*(1+k*2)+k
def Qj (k m:ℕ):ℕ:=
 (k+1)*Qm k m+m*(m*1) +
 (3*(m*m)+m*(56*m*m+11*m))+(24*m*m+10*m+2) +
 k*(1+k)+k*(1+k*2)
def gB {nIn k m:ℕ} (c:CB nIn) (r:ℕ)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m} {fy:(Fin nIn->Bool)->Q1 m}
  {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (y:Q2 nIn c m fy)
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p)))
  (ordOH:∀ t:Fin k,Q2 nIn c k (fun x p=>decide (fo x t=p))) :
  Q0 nIn c (Qj k m) (fun c'=>Qu nIn c' r fA fB fy fo):=
 Q0.weaken (by unfold Qj;omega)<|
 let Acc (u:ℕ) (_:u ≤ k+1) (c1:CB nIn):Type:=
  ∀ s:Fin (k+1),s.val < u ->
   Q8 nIn c1 m (fun x=>yH (fA x) (fB x) (fo x) s.val) ×
   Q8 nIn c1 m (fun x=>yg (fA x) (fB x) (fo x) s.val) ×
   Q8 nIn c1 m (fun x=>vL (fA x) (fB x) (fo x) s.val) ×
   Q2 nIn c1 m (fun x=>qF (fA x) (fB x) (fy x) (fo x) s.val) ×
   Q2 nIn c1 k (fun x z=>decide (z∈Q5 r (fA x) (fB x) (fo x) s.val))
 have hinit:Acc 0 (Nat.zero_le _) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=Qm k m) (k+1) Acc c hinit fun u hu c1 h1 acc=>
  Q0.weaken (by unfold Qm;omega)<|
  let su:Fin (k+1):=⟨u,hu⟩
  (zA c1 0 u (fun t=>(ordOH t).lift h1)).bind fun c2 h2 pm0=>
  let pm:Q2 nIn c2 k (fun x=>vQ (fo x) u):=pm0.cast fun x p=>by
   apply Bool.eq_iff_iff.mpr;simp [vQ]
  (zA c2 u k (fun t=>(ordOH t).lift (h1.trans h2))).bind fun c3 h3 sm0=>
  let sm:Q2 nIn c3 k (fun x=>jq (fo x) u):=sm0.cast fun x p=>by
   apply Bool.eq_iff_iff.mpr;simp [jq,Fin.isLt]
  let h03:=h1.trans (h2.trans h3)
  (gl c3 (fun p=>(Ab p).lift h03) (fun p=>(Bb p).lift h03) (pm.lift h3)).bind fun c4 h4 TLs=>
  let h04:=h03.trans h4
  (gl c4 (fun p=>(Ab p).lift h04) (fun p=>(Bb p).lift h04) (sm.lift h4)).bind fun c5 h5 TRs=>
  (yA c5 (TLs.lift h5) TRs).bind fun c6 h6 ⟨Prs,Pls,Tis⟩=>
  let h06:=h04.trans (h5.trans h6)
  (dd c6 Prs Pls (TRs.lift h6) (y.lift h06)).bind fun c7 h7 ⟨_,Lys⟩=>
  let h07:=h06.trans h7
  let h27:=h3.trans (h4.trans (h5.trans (h6.trans h7)))
  let h37:=h4.trans (h5.trans (h6.trans h7))
  (zf c7 r (fun p=>(scopes p).lift h07) (pm.lift h27)).bind fun c8 h8 pL=>
  (zf c8 r (fun p=>(scopes p).lift (h07.trans h8)) (sm.lift (h37.trans h8))).bind fun c9 h9 pR=>
  (j8 (Bstep:=1) k (fun x z=>decide (z∈Q5 r (fA x) (fB x) (fo x) u)) c9 fun z c10 h10=>
   (vg c10 ((pL.at z).lift (h9.trans h10)) ((pR.at z).lift h10)).bind fun _ _ vand=>
   Q0.pure<|vand.cast fun x=>by
    have hpL:vQ (fo x) u=fun p=>decide (p∈Qb (fo x) u):=by funext p;simp [Qb]
    have hpR:jq (fo x) u=fun p=>decide (p∈Qq (fo x) u):=by funext p;simp [Qq]
    rw [hpL,hpR,zz,zz]
    apply Bool.eq_iff_iff.mpr;simp [Q5]).bind fun _ h10 Fms=>
  let h1F:=h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans h10)))))))
  let h4F:=h5.trans (h6.trans (h7.trans (h8.trans (h9.trans h10))))
  let h5F:=h6.trans (h7.trans (h8.trans (h9.trans h10)))
  let h6F:=h7.trans (h8.trans (h9.trans h10))
  let h7F:=h8.trans (h9.trans h10)
  Q0.pure fun s hs=>
   if hlt:s.val < u then
    let p:=acc s hlt
    ⟨p.1.lift h1F,p.2.1.lift h1F,p.2.2.1.lift h1F,p.2.2.2.1.lift h1F,p.2.2.2.2.lift h1F⟩
   else
    have heq:s=su:=Fin.ext (by dsimp [su];omega)
    heq▸⟨(TLs.lift h4F).cast (fun _=>rfl),(TRs.lift h5F).cast (fun _=>rfl),
       (Tis.lift h6F).cast (fun _=>rfl),(Lys.lift h7F).cast (fun _ _=>rfl),Fms⟩).bind fun c1 h1 all=>
 (y0 c1 m).bind fun c2 h2 zT=>
 let TLk:=(all ⟨k,by omega⟩ (by omega)).1.lift h2
 (yA c2 TLk zT).bind fun c3 h3 ⟨Prk,Plk,_⟩=>
 (dd c3 Prk Plk (zT.lift h3) (y.lift (h1.trans (h2.trans h3)))).bind fun c4 h4 ⟨okA,_⟩=>
 let h04:=h1.trans (h2.trans (h3.trans h4))
 (zA c4 0 k (fun t=>(ordOH t).lift h04)).bind fun c5 h5 pmk0=>
 let pmk:Q2 nIn c5 k (fun x=>vQ (fo x) k):=pmk0.cast fun x p=>by
  apply Bool.eq_iff_iff.mpr;simp [vQ]
 (zf c5 r (fun p=>(scopes p).lift (h04.trans h5)) pmk).bind fun _ h6 pAll=>
 let h1F:=h2.trans (h3.trans (h4.trans (h5.trans h6)))
 Q0.pure
  ⟨fun s=>(all s s.isLt).1.lift h1F,
  fun s=>(all s s.isLt).2.1.lift h1F,
  fun s=>(all s s.isLt).2.2.1.lift h1F,
  fun s=>(all s s.isLt).2.2.2.1.lift h1F,
  fun s=>(all s s.isLt).2.2.2.2.lift h1F,
  (okA.lift (h5.trans h6)).cast (fun _=>rfl),
  pAll⟩
def Qz (k r m B:ℕ):ℕ:=
 k*(2+B)+2*(k*4+r*(k*22))+2*(1+k*2)+2 +
 B+(m+B*(8*m))+m*(8*m+1)+(1+m)+1
def Qy (k m B W:ℕ):ℕ:=
 (3*(m*m)+m*(56*m*m+11*m))+2*QF m B W+QE B +
 k*(1+k*2)+k+2*k+2*k +
 k*Qg k B+k*Qe k B +
 2*(m*(1+k*2))+2*(1+m)+m*4 +
 3*Qk m B W+QH m B W
def Qx (k r m B:ℕ):ℕ:=
 2^B*Qz k r m B+B*(2^B*10)
def Qf (k r m B W:ℕ):ℕ:=
 Qy k m B W+Qx k r m B
structure QL (nIn:ℕ) (c:CB nIn) {k m:ℕ} (r b:ℕ)
  (fA fB:(Fin nIn->Bool)->Fin k->Q1 m) (fy:(Fin nIn->Bool)->Q1 m)
  (fo:(Fin nIn->Bool)->Fin k->Fin k) (i:Fin k) where
 Mmid:Qo nIn c k (b+2) (fun x=>qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val))
 Mout:Qo nIn c k (b+2) (fun x=>vN r b (fA x) (fB x) (fo x) i
  (qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val)))
 Gin:Qv nIn c (b+2) (fun x=>qk (vL (fA x) (fB x) (fo x) i.val) (j7 (fA x) (fB x) (fo x) i) (b+2))
 GoutInv:Qv nIn c (b+2) (fun x=>j1 (qk (vL (fA x) (fB x) (fo x) (i.val+1)) (j7 (fA x) (fB x) (fo x) i) (b+2)))
 scOi:Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) (fo x i)))
 introCond:Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) (fo x i))&&!decide (z∈Q5 r (fA x) (fB x) (fo x) i.val))
 introOH:∀ z:Fin k,Q2 nIn c (b+2) (fun x=>qO (q7 (qy r b (fA x) (fB x) (fo x) i z.val)))
 forgetCond:Q2 nIn c k (fun x z=>decide (z∈Qi r (fA x) (fB x) (fo x) i)&&!decide (z∈Q5 r (fA x) (fB x) (fo x) (i.val+1)))
 forgetSOH:∀ z:Fin k,Q2 nIn c (b+2) (fun x=>ql r b (fA x) (fB x) (fo x) i z.val z)
 forgetLoOH:∀ z:Fin k,Q2 nIn c (b+2) (fun x=>qV (q7 (ql r b (fA x) (fB x) (fo x) i z.val)))
 nzA:Q4 nIn c (fun x=>qK (fA x (fo x i)))
 nzB:Q4 nIn c (fun x=>qK (fB x (fo x i)))
 cdy:Q2 nIn c (b+2) (fun x=>qf (j7 (fA x) (fB x) (fo x) i) (q5 (qF (fA x) (fB x) (fy x) (fo x) i.val) (qF (fA x) (fB x) (fy x) (fo x) (i.val+1))) (b+2))
 cA:Q2 nIn c (b+2) (fun x=>qf (j7 (fA x) (fB x) (fo x) i) (fA x (fo x i)) (b+2))
 cB:Q2 nIn c (b+2) (fun x=>qf (j7 (fA x) (fB x) (fo x) i) (fB x (fo x i)) (b+2))
 pivM:∀ t:Fin (b+2),Q2 nIn c m (fun x=>qc (j7 (fA x) (fB x) (fo x) i) (b+2) t)
def gN {nIn k r m b W:ℕ} (c:CB nIn)
  (hW:1 ≤ W) (hmW:m < 2^W) (h2BW:2*(b+2) < 2^W)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p)))
  (ordOH:∀ t:Fin k,Q2 nIn c k (fun x p=>decide (fo x t=p)))
  (T:Qu nIn c r fA fB fy fo)
  (i:Fin k)
  (Min:Qo nIn c k (b+2) (fun x=>qt r b (fA x) (fB x) (fo x) i.val)) :
  Q0 nIn c (Qy k m (b+2) W) (fun c'=>QL nIn c' r b fA fB fy fo i):=
 have hBW:b+2 < 2^W:=by have:=Nat.two_pow_pos W;omega
 let i0:Fin (k+1):=⟨i.val,by omega⟩
 let i1:Fin (k+1):=⟨i.val+1,by omega⟩
 Q0.weaken (by unfold Qy;omega)<|
 (yA c (T.TL i1) (T.TR i0)).bind fun c1 h1 ⟨_,_,TM⟩=>
 (zn c1 hW hmW h2BW ((T.Ti i0).lift h1) TM).bind fun c2 h2 Gin=>
 let h02:=h1.trans h2
 (zn c2 hW hmW h2BW ((T.Ti i1).lift h02) (TM.lift h2)).bind fun c3 h3 Gout=>
 (dC c3 Gout).bind fun c4 h4 GoutInv=>
 let h04:=h02.trans (h3.trans h4)
 (yW c4 ((ordOH i).lift h04) (fun p=>(scopes p).lift h04)).bind fun c5 h5 scOi=>
 let h05:=h04.trans h5
 (j8 (Bstep:=1) k (fun x z=>decide (z∈Qi r (fA x) (fB x) (fo x) i)) c5 fun z c6 h6=>
  (yr c6 (((T.Fm i0).at z).lift (h05.trans h6)) ((scOi.at z).lift h6)).bind fun _ _ vor=>
  Q0.pure<|vor.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp [Qi,i0]).bind fun c6 h6 Ai=>
 let h06:=h05.trans h6
 (j8 (Bstep:=2) k (fun x z=>decide (z∈qq r (fA x) (fB x) (fo x i))&&!decide (z∈Q5 r (fA x) (fB x) (fo x) i.val)) c6 fun z c7 h7=>
  (y2 c7 (((T.Fm i0).at z).lift (h06.trans h7))).bind fun c8 h8 vnf=>
  (vg c8 ((scOi.at z).lift (h6.trans (h7.trans h8))) vnf).bind fun _ _ vand=>
  Q0.pure<|vand.cast fun x=>by simp [i0]).bind fun c7 h7 introCond=>
 let h07:=h06.trans h7
 (j8 (Bstep:=2) k (fun x z=>decide (z∈Qi r (fA x) (fB x) (fo x) i)&&!decide (z∈Q5 r (fA x) (fB x) (fo x) (i.val+1))) c7 fun z c8 h8=>
  (y2 c8 (((T.Fm i1).at z).lift (h07.trans h8))).bind fun c9 h9 vnf=>
  (vg c9 ((Ai.at z).lift (h7.trans (h8.trans h9))) vnf).bind fun _ _ vand=>
  Q0.pure<|vand.cast fun x=>by simp [i1]).bind fun c8 h8 forgetCond=>
 let h08:=h07.trans h8
 let IAcc (u:ℕ) (_:u ≤ k) (c9:CB nIn):Type:=
  Qo nIn c9 k (b+2) (fun x=>qy r b (fA x) (fB x) (fo x) i u) ×
  (∀ z:Fin k,z.val < u->Q2 nIn c9 (b+2) (fun x=>qO (q7 (qy r b (fA x) (fB x) (fo x) i z.val))))
 have hIinit:IAcc 0 (Nat.zero_le k) c8:=
  ⟨(Min.lift h08).cast (fun _ _ _=>rfl),fun _ h=>absurd h (by omega)⟩
 (Q0.qe (Bstep:=Qg k (b+2)) k IAcc c8 hIinit fun u hu c9 h9 ⟨Mc,ohs⟩=>
  let zu:Fin k:=⟨u,hu⟩
  (gy c9 Mc zu ((introCond.at zu).lift (h8.trans h9))).bind fun _ h10 ⟨oh,M'⟩=>
  have htake:(dF k).take (u+1)=(dF k).take u ++ [zu]:=by
   rw [dJ (by simp;omega)];simp [zu]
  Q0.pure
   ⟨M'.cast fun x z s=>by
     simp only [qy,htake,List.foldl_append,List.foldl_cons,List.foldl_nil],
   fun z hz=>
    if hlt:z.val < u then (ohs z hlt).lift h10
    else
     have heq:z=zu:=Fin.ext (by dsimp [zu];omega)
     heq▸oh.cast (fun _ _=>rfl)⟩).bind fun c9 h9 ⟨Mmid0,introOH⟩=>
 have hktake:(dF k).take k=dF k:=by simp
 let Mmid:Qo nIn c9 k (b+2) (fun x=>qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val)):=
  Mmid0.cast fun x z s=>by simp only [qy,qB,hktake]
 let FAcc (u:ℕ) (_:u ≤ k) (c10:CB nIn):Type:=
  Qo nIn c10 k (b+2) (fun x=>ql r b (fA x) (fB x) (fo x) i u) ×
  (∀ z:Fin k,z.val < u->Q2 nIn c10 (b+2) (fun x=>ql r b (fA x) (fB x) (fo x) i z.val z)) ×
  (∀ z:Fin k,z.val < u->Q2 nIn c10 (b+2) (fun x=>qV (q7 (ql r b (fA x) (fB x) (fo x) i z.val))))
 have hFinit:FAcc 0 (Nat.zero_le k) c9:=
  ⟨Mmid.cast (fun _ _ _=>rfl),fun _ h=>absurd h (by omega),fun _ h=>absurd h (by omega)⟩
 (Q0.qe (Bstep:=Qe k (b+2)) k FAcc c9 hFinit fun u hu c10 h10 ⟨Mc,sohs,lohs⟩=>
  let zu:Fin k:=⟨u,hu⟩
  (gb c10 Mc zu ((forgetCond.at zu).lift (h9.trans h10))).bind fun _ h11 ⟨lo,M'⟩=>
  have htake:(dF k).take (u+1)=(dF k).take u ++ [zu]:=by
   rw [dJ (by simp;omega)];simp [zu]
  Q0.pure
   ⟨M'.cast fun x z s=>by
     simp only [ql,htake,List.foldl_append,List.foldl_cons,List.foldl_nil],
   fun z hz=>
    if hlt:z.val < u then (sohs z hlt).lift h11
    else
     have heq:z=zu:=Fin.ext (by dsimp [zu];omega)
     heq▸((Mc.rows zu).lift h11).cast (fun _ _=>rfl),
   fun z hz=>
    if hlt:z.val < u then (lohs z hlt).lift h11
    else
     have heq:z=zu:=Fin.ext (by dsimp [zu];omega)
     heq▸lo.cast (fun _ _=>rfl)⟩).bind fun c10 h10 ⟨Mout0,fSOH,fLoOH⟩=>
 let Mout:Qo nIn c10 k (b+2) (fun x=>vN r b (fA x) (fB x) (fo x) i
   (qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val))):=
  Mout0.cast fun x z s=>by simp only [ql,vN,hktake]
 let h010:=h08.trans (h9.trans h10)
 (yW c10 ((ordOH i).lift h010) (fun p=>(Ab p).lift h010)).bind fun c11 h11 Abi=>
 let h011:=h010.trans h11
 (yW c11 ((ordOH i).lift h011) (fun p=>(Bb p).lift h011)).bind fun c12 h12 Bbi=>
 (zg c12 (Abi.lift h12)).bind fun c13 h13 nzA0=>
 let nzA:Q4 nIn c13 (fun x=>qK (fA x (fo x i))):=nzA0.cast fun x=>(qv _).symm
 (zg c13 (Bbi.lift h13)).bind fun c14 h14 nzB0=>
 let nzB:Q4 nIn c14 (fun x=>qK (fB x (fo x i))):=nzB0.cast fun x=>(qv _).symm
 let h014:=h011.trans (h12.trans (h13.trans h14))
 (j3 c14 ((T.Ly i0).lift h014) ((T.Ly i1).lift h014)).bind fun c15 h15 dy=>
 let h115:=h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans (h13.trans (h14.trans h15))))))))))))
 (yS c15 hW hmW hBW (TM.lift h115) dy).bind fun c16 h16 cdy=>
 let h116:=h115.trans h16
 (yS c16 hW hmW hBW (TM.lift h116) (Abi.lift (h12.trans (h13.trans (h14.trans (h15.trans h16)))))).bind fun c17 h17 cA=>
 let h117:=h116.trans h17
 (yS c17 hW hmW hBW (TM.lift h117) (Bbi.lift (h13.trans (h14.trans (h15.trans (h16.trans h17)))))).bind fun c18 h18 cB=>
 let h118:=h117.trans h18
 (zB c18 hW hmW hBW (TM.lift h118)).bind fun _ h19 pivM=>
 let h1019:=h11.trans (h12.trans (h13.trans (h14.trans (h15.trans (h16.trans (h17.trans (h18.trans h19)))))))
 let h919:=h10.trans h1019
 let h819:=h9.trans h919
 let h719:=h8.trans h819
 let h519:=h6.trans (h7.trans h719)
 let h419:=h5.trans h519
 let h219:=h3.trans (h4.trans h419)
 let h1319:=h14.trans (h15.trans (h16.trans (h17.trans (h18.trans h19))))
 let h1419:=h15.trans (h16.trans (h17.trans (h18.trans h19)))
 let h1619:=h17.trans (h18.trans h19)
 let h1719:=h18.trans h19
 Q0.pure
  ⟨Mmid.lift h919,Mout.lift h1019,(Gin.lift h219).cast (fun _ _ _=>rfl),
  (GoutInv.lift h419).cast (fun _ _ _=>rfl),scOi.lift h519,introCond.lift h719,
  fun z=>(introOH z z.isLt).lift h919,forgetCond.lift h819,
  fun z=>(fSOH z z.isLt).lift h1019,fun z=>(fLoOH z z.isLt).lift h1019,
  nzA.lift h1319,nzB.lift h1419,
  (cdy.lift h1619).cast (fun _ _=>rfl),(cA.lift h1719).cast (fun _ _=>rfl),
  (cB.lift h19).cast (fun _ _=>rfl),fun t=>(pivM t).cast (fun _ _=>rfl)⟩
set_option maxHeartbeats 800000 in
def gM {nIn k r m b:ℕ} (c:CB nIn) (hk:0 < k)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fnr fnc:(Fin nIn->Bool)->Fin (2^k)}
  {fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (nr:Q2 nIn c k (fun x q=>(fnr x).val.testBit q.val))
  (nc:Q2 nIn c k (fun x q=>(fnc x).val.testBit q.val))
  (cr:∀ j:Fin r,Q2 nIn c k (fun x q=>(fcr x j).val.testBit q.val))
  (cc:∀ j:Fin r,Q2 nIn c k (fun x q=>(fcc x j).val.testBit q.val))
  (ordOH:∀ t:Fin k,Q2 nIn c k (fun x p=>decide (fo x t=p)))
  (i:Fin k)
  (TRi1:Q8 nIn c m (fun x=>yg (fA x) (fB x) (fo x) (i.val+1)))
  (PA:QL nIn c r b fA fB fy fo i) :
  Q0 nIn c (Qx k r m (b+2))
   (fun c'=>
    (∀ t:Fin (b+2),Q2 nIn c' (2^(b+2)) (fun x idx=>jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) i t idx)) ×
    Q2 nIn c' (2^(b+2)) (fun x idx=>vP b (fA x) (fB x) (fo x) i idx)):=
 Q0.weaken (by unfold Qx;omega)<|
 let IdxAcc (u:ℕ) (_:u ≤ 2^(b+2)) (c20:CB nIn):Type:=
  (∀ idx:Fin (2^(b+2)),idx.val < u->Q4 nIn c20 (fun x=>jB b (fA x) (fB x) (fnr x) (fcr x) (fo x) i idx)) ×
  (∀ idx:Fin (2^(b+2)),idx.val < u->Q4 nIn c20 (fun x=>jA b (fA x) (fB x) (fnc x) (fcc x) (fo x) i idx)) ×
  (∀ idx:Fin (2^(b+2)),idx.val < u->Q4 nIn c20 (fun x=>vP b (fA x) (fB x) (fo x) i idx))
 have hIdxInit:IdxAcc 0 (Nat.zero_le _) c:=
  ⟨fun _ h=>absurd h (by omega),fun _ h=>absurd h (by omega),fun _ h=>absurd h (by omega)⟩
 (Q0.qe (Bstep:=Qz k r m (b+2)) (2^(b+2)) IdxAcc c hIdxInit fun u hu c20 h20 ⟨bfs,bts,kps⟩=>
  Q0.weaken (by unfold Qz;omega)<|
  let iu:Fin (2^(b+2)):=⟨u,hu⟩
  let wLocFn (x:Fin nIn->Bool):ℕ:=
   jL (qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val))
    (fun z=>decide (z∈qq r (fA x) (fB x) (fo x i))) iu
  (j8 (Bstep:=2+(b+2)) k (fun x z=>(wLocFn x).testBit z.val) c20 fun z c21 h21=>
   Q0.weaken (by omega)<|
   (vJ c21 false).bind fun c22 h22 vf=>
   let WAcc (s:ℕ) (_:s ≤ b+2) (c23:CB nIn):Type:=
    Q4 nIn c23 (fun x=>decide (∃ s':Fin (b+2),s'.val < s /\
     qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val) z s'=true /\
     v8 (b+2) iu s'=true))
   have hWinit:WAcc 0 (Nat.zero_le _) c22:=vf.cast fun _=>by simp
   (Q0.qe (Bstep:=1) (b+2) WAcc c22 hWinit fun s hs c23 h23 wacc=>
    let ss:Fin (b+2):=⟨s,hs⟩
    if hbit:v8 (b+2) iu ss=true then
     (yr c23 wacc (((PA.Mmid.rows z).at ss).lift (h20.trans (h21.trans (h22.trans h23))))).bind fun _ _ vor=>
     Q0.pure<|vor.cast fun x=>by
      apply Bool.eq_iff_iff.mpr;simp only [dH,dG]
      constructor
      ·rintro (⟨s',hs',h1',h2'⟩ | h1')
       ·exact ⟨s',by omega,h1',h2'⟩
       ·exact ⟨ss,by dsimp [ss];omega,h1',hbit⟩
      ·rintro ⟨s',hs',h1',h2'⟩
       by_cases hlt:s'.val < s
       ·left;exact ⟨s',hlt,h1',h2'⟩
       ·right;have heq:s'=ss:=Fin.ext (by dsimp [ss];omega);subst heq;exact h1'
    else
     Q0.weaken (by omega)<|
     Q0.pure<|wacc.cast fun x=>by
      apply Bool.eq_iff_iff.mpr;simp only [dG]
      constructor
      ·rintro ⟨s',hs',h1',h2'⟩;exact ⟨s',by omega,h1',h2'⟩
      ·rintro ⟨s',hs',h1',h2'⟩
       refine ⟨s',?_,h1',h2'⟩
       by_contra hge;have heq:s'=ss:=Fin.ext (by dsimp [ss];omega);rw [heq] at h2';exact hbit h2').bind fun c23 h23 vany=>
   (vg c23 ((PA.scOi.at z).lift (h20.trans (h21.trans (h22.trans h23)))) vany).bind fun _ _ vand=>
   Q0.pure<|vand.cast fun x=>by
    dsimp only [wLocFn,jL];rw [qb _ z]
    congr 1;apply Bool.eq_iff_iff.mpr;simp only [dG]
    exact ⟨fun ⟨s',_,h1',h2'⟩=>⟨s',h1',h2'⟩,fun ⟨s',h1',h2'⟩=>⟨s',s'.isLt,h1',h2'⟩⟩).bind fun c21 h21 vwLoc=>
  let h021:=h20.trans h21
  have hwLoc_lt:∀ x,wLocFn x < 2^k:=fun x=>ya _
  (gO c21 hk false hwLoc_lt (fun x=>(fnr x).isLt) vwLoc (nr.lift h021) (fun j=>(cr j).lift h021)).bind fun c22 h22 stF=>
  let h022:=h021.trans h22
  (gO c22 hk true hwLoc_lt (fun x=>(fnc x).isLt) (vwLoc.lift h22) (nc.lift h022) (fun j=>(cc j).lift h022)).bind fun c23 h23 stT=>
  let h023:=h022.trans h23
  let stFrot:Q2 nIn c23 k (fun x p=>(vI k r false (wLocFn x) (fnr x).val (fcr x)).testBit ((p.val+vo r false) % k)):=
   ⟨fun p=>((stF.at ⟨(p.val+vo r false) % k,Nat.mod_lt _ hk⟩).lift h23).w,
   fun p=>((stF.at ⟨(p.val+vo r false) % k,Nat.mod_lt _ hk⟩).lift h23).hw,
   fun x p=>((stF.at ⟨(p.val+vo r false) % k,Nat.mod_lt _ hk⟩).lift h23).heval x⟩
  let stTrot:Q2 nIn c23 k (fun x p=>(vI k r true (wLocFn x) (fnc x).val (fcc x)).testBit ((p.val+vo r true) % k)):=
   ⟨fun p=>(stT.at ⟨(p.val+vo r true) % k,Nat.mod_lt _ hk⟩).w,
   fun p=>(stT.at ⟨(p.val+vo r true) % k,Nat.mod_lt _ hk⟩).hw,
   fun x p=>(stT.at ⟨(p.val+vo r true) % k,Nat.mod_lt _ hk⟩).heval x⟩
  (gG c23 ((ordOH i).lift h023) stFrot).bind fun c24 h24 bitF=>
  (gG c24 ((ordOH i).lift (h023.trans h24)) (stTrot.lift h24)).bind fun c25 h25 bitT=>
  let h025:=h023.trans (h24.trans h25)
  (vg c25 (PA.nzA.lift h025) (bitF.lift h25)).bind fun c26 h26 vbf=>
  (vg c26 (PA.nzB.lift (h025.trans h26)) (bitT.lift h26)).bind fun c27 h27 vbt=>
  (vq c27 (b+2) (v8 (b+2) iu)).bind fun c28 h28 vxiu=>
  let h028:=h025.trans (h26.trans (h27.trans h28))
  (gc c28 (fun t=>(PA.pivM t).lift h028) vxiu).bind fun c29 h29 vrec=>
  (yR c29 (TRi1.lift (h028.trans h29)) vrec).bind fun c30 h30 vred=>
  (zg c30 vred).bind fun c31 h31 vnzR=>
  (y2 c31 vnzR).bind fun _ h32 vkp=>
  let h26F:=h27.trans (h28.trans (h29.trans (h30.trans (h31.trans h32))))
  let h27F:=h28.trans (h29.trans (h30.trans (h31.trans h32)))
  let h20F:=h21.trans (h22.trans (h23.trans (h24.trans (h25.trans (h26.trans h26F)))))
  Q0.pure
   ⟨fun idx hidx=>
    if hlt:idx.val < u then (bfs idx hlt).lift h20F
    else
     have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
     heq▸(vbf.lift h26F).cast fun x=>by
      dsimp only [jB,jM,wLocFn]
      congr 1;apply Bool.eq_iff_iff.mpr;simp only [dG]
      exact ⟨fun ⟨p,hp,ht⟩=>hp▸ht,fun ht=>⟨fo x i,rfl,ht⟩⟩,
   fun idx hidx=>
    if hlt:idx.val < u then (bts idx hlt).lift h20F
    else
     have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
     heq▸(vbt.lift h27F).cast fun x=>by
      dsimp only [jA,jM,wLocFn]
      congr 1;apply Bool.eq_iff_iff.mpr;simp only [dG]
      exact ⟨fun ⟨p,hp,ht⟩=>hp▸ht,fun ht=>⟨fo x i,rfl,ht⟩⟩,
   fun idx hidx=>
    if hlt:idx.val < u then (kps idx hlt).lift h20F
    else
     have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
     heq▸vkp.cast fun x=>by
      dsimp only [vP];rw [qv]⟩).bind fun c20 h20 ⟨bfAll,btAll,kpAll⟩=>
 let FlAcc (s:ℕ) (_:s ≤ b+2) (c21:CB nIn):Type:=
  ∀ t:Fin (b+2),t.val < s->Q2 nIn c21 (2^(b+2))
   (fun x idx=>jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) i t idx)
 have hFlInit:FlAcc 0 (Nat.zero_le _) c20:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=2^(b+2)*10) (b+2) FlAcc c20 hFlInit fun s hs c21 h21 flacc=>
  let ts:Fin (b+2):=⟨s,hs⟩
  (j8 (Bstep:=10) (2^(b+2)) (fun x idx=>jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) i ts idx) c21 fun idx c22 h22=>
   Q0.weaken (by omega)<|
   let h2022:=h21.trans h22
   let h022:=h20.trans h2022
   (vg c22 ((PA.cA.at ts).lift h022) ((bfAll idx idx.isLt).lift h2022)).bind fun c23 h23 va=>
   (vg c23 ((PA.cB.at ts).lift (h022.trans h23)) ((btAll idx idx.isLt).lift (h2022.trans h23))).bind fun c24 h24 vb=>
   (g2 c24 (va.lift h24) vb).bind fun c25 h25 vx1=>
   (g2 c25 ((PA.cdy.at ts).lift (h022.trans (h23.trans (h24.trans h25)))) vx1).bind fun _ _ vx2=>
   Q0.pure<|vx2.cast fun _=>rfl).bind fun _ h22 vfl=>
  Q0.pure fun t ht=>
   if hlt:t.val < s then (flacc t hlt).lift h22
   else
    have heq:t=ts:=Fin.ext (by dsimp [ts];omega)
    heq▸vfl).bind fun _ h21 flAll=>
 Q0.pure
  ⟨fun t=>flAll t t.isLt,
  ⟨fun idx=>((kpAll idx idx.isLt).lift h21).w,
   fun idx=>((kpAll idx idx.isLt).lift h21).hw,
   fun x idx=>((kpAll idx idx.isLt).lift h21).heval x⟩⟩
def gY {nIn k r m b W:ℕ} (c:CB nIn)
  (hk:0 < k) (hW:1 ≤ W) (hmW:m < 2^W) (h2BW:2*(b+2) < 2^W)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fnr fnc:(Fin nIn->Bool)->Fin (2^k)}
  {fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (nr:Q2 nIn c k (fun x q=>(fnr x).val.testBit q.val))
  (nc:Q2 nIn c k (fun x q=>(fnc x).val.testBit q.val))
  (cr:∀ j:Fin r,Q2 nIn c k (fun x q=>(fcr x j).val.testBit q.val))
  (cc:∀ j:Fin r,Q2 nIn c k (fun x q=>(fcc x j).val.testBit q.val))
  (scopes:∀ p:Fin k,Q2 nIn c k (fun x z=>decide (z∈qq r (fA x) (fB x) p)))
  (ordOH:∀ t:Fin k,Q2 nIn c k (fun x p=>decide (fo x t=p)))
  (T:Qu nIn c r fA fB fy fo)
  (i:Fin k)
  (Min:Qo nIn c k (b+2) (fun x=>qt r b (fA x) (fB x) (fo x) i.val)) :
  Q0 nIn c (Qf k r m (b+2) W)
   (fun c'=>
    Qo nIn c' k (b+2) (fun x=>vN r b (fA x) (fB x) (fo x) i
     (qB r b (fA x) (fB x) (fo x) i (qt r b (fA x) (fB x) (fo x) i.val))) ×
    Qv nIn c' (b+2) (fun x=>qk (vL (fA x) (fB x) (fo x) i.val) (j7 (fA x) (fB x) (fo x) i) (b+2)) ×
    Qv nIn c' (b+2) (fun x=>j1 (qk (vL (fA x) (fB x) (fo x) (i.val+1)) (j7 (fA x) (fB x) (fo x) i) (b+2))) ×
    Q2 nIn c' k (fun x z=>decide (z∈qq r (fA x) (fB x) (fo x i))&&!decide (z∈Q5 r (fA x) (fB x) (fo x) i.val)) ×
    (∀ z:Fin k,Q2 nIn c' (b+2) (fun x=>qO (q7 (qy r b (fA x) (fB x) (fo x) i z.val)))) ×
    (∀ t:Fin (b+2),Q2 nIn c' (2^(b+2)) (fun x idx=>jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) i t idx)) ×
    Q2 nIn c' k (fun x z=>decide (z∈Qi r (fA x) (fB x) (fo x) i)&&!decide (z∈Q5 r (fA x) (fB x) (fo x) (i.val+1))) ×
    (∀ z:Fin k,Q2 nIn c' (b+2) (fun x=>ql r b (fA x) (fB x) (fo x) i z.val z)) ×
    (∀ z:Fin k,Q2 nIn c' (b+2) (fun x=>qV (q7 (ql r b (fA x) (fB x) (fo x) i z.val)))) ×
    Q2 nIn c' (2^(b+2)) (fun x idx=>vP b (fA x) (fB x) (fo x) i idx)):=
 Q0.weaken (by unfold Qf;omega)<|
 (gN c hW hmW h2BW Ab Bb scopes ordOH T i Min).bind fun c1 h1 PA=>
 (gM c1 hk (nr.lift h1) (nc.lift h1) (fun j=>(cr j).lift h1) (fun j=>(cc j).lift h1)
  (fun t=>(ordOH t).lift h1) i ((T.TR ⟨i.val+1,by omega⟩).lift h1) PA).bind fun _ h2 ⟨flAll,kpAll⟩=>
 Q0.pure
  ⟨PA.Mout.lift h2,PA.Gin.lift h2,PA.GoutInv.lift h2,PA.introCond.lift h2,
  fun z=>(PA.introOH z).lift h2,flAll,PA.forgetCond.lift h2,
  fun z=>(PA.forgetSOH z).lift h2,fun z=>(PA.forgetLoOH z).lift h2,kpAll⟩
def Qc (k r m B W:ℕ):ℕ:=
 (1+k*(2*m+3))+Qj k m+k*B+k*Qf k r m B W
def gA {nIn k r m b W:ℕ} (c:CB nIn)
  (hk:0 < k) (hW:1 ≤ W) (hmW:m < 2^W) (h2BW:2*(b+2) < 2^W)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fnr fnc:(Fin nIn->Bool)->Fin (2^k)}
  {fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  (Ab:∀ p:Fin k,Q2 nIn c m (fun x=>fA x p))
  (Bb:∀ p:Fin k,Q2 nIn c m (fun x=>fB x p))
  (nr:Q2 nIn c k (fun x q=>(fnr x).val.testBit q.val))
  (nc:Q2 nIn c k (fun x q=>(fnc x).val.testBit q.val))
  (cr:∀ j:Fin r,Q2 nIn c k (fun x q=>(fcr x j).val.testBit q.val))
  (cc:∀ j:Fin r,Q2 nIn c k (fun x q=>(fcc x j).val.testBit q.val))
  (y:Q2 nIn c m fy)
  (ordOH:∀ t:Fin k,Q2 nIn c k (fun x p=>decide (fo x t=p))) :
  Q0 nIn c (Qc k r m (b+2) W)
   (fun c'=>Qp nIn c' b fA fB fnr fnc fcr fcc fy fo):=
 let B:=b+2
 Q0.weaken (by unfold Qc;dsimp only [B];omega)<|
 (gn c r Ab Bb).bind fun c1 h1 scopes=>
 (gB c1 r (fun p=>(Ab p).lift h1) (fun p=>(Bb p).lift h1)
  (y.lift h1) scopes (fun t=>(ordOH t).lift h1)).bind fun c2 h2 T=>
 (dk c2 k B (fun _ _=>false)).bind fun c3 h3 M0=>
 let h03:=h1.trans (h2.trans h3)
 let T3:Qu nIn c3 r fA fB fy fo:=
  ⟨fun s=>(T.TL s).lift h3,fun s=>(T.TR s).lift h3,fun s=>(T.Ti s).lift h3,
  fun s=>(T.Ly s).lift h3,fun s=>(T.Fm s).lift h3,T.okAll.lift h3,T.poolAll.lift h3⟩
 let StepData (c':CB nIn) (i:Fin k):Type:=
  Qv nIn c' B (fun x=>qk (vL (fA x) (fB x) (fo x) i.val) (j7 (fA x) (fB x) (fo x) i) B) ×
  Qv nIn c' B (fun x=>j1 (qk (vL (fA x) (fB x) (fo x) (i.val+1)) (j7 (fA x) (fB x) (fo x) i) B)) ×
  Q2 nIn c' k (fun x z=>decide (z∈qq r (fA x) (fB x) (fo x i))&&!decide (z∈Q5 r (fA x) (fB x) (fo x) i.val)) ×
  (∀ z:Fin k,Q2 nIn c' B (fun x=>qO (q7 (qy r b (fA x) (fB x) (fo x) i z.val)))) ×
  (∀ t:Fin B,Q2 nIn c' (2^B) (fun x idx=>jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) i t idx)) ×
  Q2 nIn c' k (fun x z=>decide (z∈Qi r (fA x) (fB x) (fo x) i)&&!decide (z∈Q5 r (fA x) (fB x) (fo x) (i.val+1))) ×
  (∀ z:Fin k,Q2 nIn c' B (fun x=>ql r b (fA x) (fB x) (fo x) i z.val z)) ×
  (∀ z:Fin k,Q2 nIn c' B (fun x=>qV (q7 (ql r b (fA x) (fB x) (fo x) i z.val)))) ×
  Q2 nIn c' (2^B) (fun x idx=>vP b (fA x) (fB x) (fo x) i idx)
 let liftSD {c' c'':CB nIn} {i:Fin k} (h:c'.Qa c'') (d:StepData c' i):StepData c'' i:=
  ⟨d.1.lift h,d.2.1.lift h,d.2.2.1.lift h,fun z=>(d.2.2.2.1 z).lift h,
  fun t=>(d.2.2.2.2.1 t).lift h,d.2.2.2.2.2.1.lift h,fun z=>(d.2.2.2.2.2.2.1 z).lift h,
  fun z=>(d.2.2.2.2.2.2.2.1 z).lift h,d.2.2.2.2.2.2.2.2.lift h⟩
 let Acc (u:ℕ) (_:u ≤ k) (c4:CB nIn):Type:=
  Qo nIn c4 k B (fun x=>qt r b (fA x) (fB x) (fo x) u) ×
  (∀ i:Fin k,i.val < u->StepData c4 i)
 have hinit:Acc 0 (Nat.zero_le k) c3:=⟨M0.cast (fun _ _ _=>rfl),fun _ h=>absurd h (by omega)⟩
 (Q0.qe (Bstep:=Qf k r m B W) k Acc c3 hinit fun u hu c4 h4 ⟨Mc,dats⟩=>
  let iu:Fin k:=⟨u,hu⟩
  let h04:=h03.trans h4
  let T4:Qu nIn c4 r fA fB fy fo:=
   ⟨fun s=>(T3.TL s).lift h4,fun s=>(T3.TR s).lift h4,fun s=>(T3.Ti s).lift h4,
   fun s=>(T3.Ly s).lift h4,fun s=>(T3.Fm s).lift h4,T3.okAll.lift h4,T3.poolAll.lift h4⟩
  (gY c4 hk hW hmW h2BW (fun p=>(Ab p).lift h04) (fun p=>(Bb p).lift h04)
   (nr.lift h04) (nc.lift h04) (fun j=>(cr j).lift h04) (fun j=>(cc j).lift h04)
   (fun p=>(scopes p).lift (h2.trans (h3.trans h4))) (fun t=>(ordOH t).lift h04) T4 iu Mc).bind fun _ h5 res=>
  have htake:(dF k).take (u+1)=(dF k).take u ++ [iu]:=by
   rw [dJ (by simp;omega)];simp [iu]
  Q0.pure
   ⟨res.1.cast fun x z s=>by
     have hstep:qt r b (fA x) (fB x) (fo x) (u+1) =
       vN r b (fA x) (fB x) (fo x) iu (qB r b (fA x) (fB x) (fo x) iu (qt r b (fA x) (fB x) (fo x) u)):=by
      unfold qt;rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
     rw [hstep],
   fun i hi=>
    if hlt:i.val < u then liftSD h5 (dats i hlt)
    else
     have heq:i=iu:=Fin.ext (by dsimp [iu];omega)
     heq▸res.2⟩).bind fun _ h4 ⟨_,datsF⟩=>
 Q0.pure
  ⟨T3.okAll.lift h4,T3.poolAll.lift h4,
  fun i=>(datsF i i.isLt).1,
  fun i=>(datsF i i.isLt).2.1,
  fun i=>(datsF i i.isLt).2.2.1,
  fun i=>(datsF i i.isLt).2.2.2.1,
  fun i=>(datsF i i.isLt).2.2.2.2.1,
  fun i=>(datsF i i.isLt).2.2.2.2.2.1,
  fun i=>(datsF i i.isLt).2.2.2.2.2.2.1,
  fun i=>(datsF i i.isLt).2.2.2.2.2.2.2.1,
  fun i=>(datsF i i.isLt).2.2.2.2.2.2.2.2⟩
def QD (k B:ℕ):ℕ:=
 QC B (k+1)+k*Qw B (k+1)+B*(2^B*(4*(k+1))) +
 k*(Qn B (k+1)+Qr B (k+1))+((k+1)+2^B*(4*(k+1))) +
 QC B (k+1)
def Qh (k B:ℕ):ℕ:=
 2^B*(k+1)+k*QD k B+k*(4+15*(k+1))+(k+1)+(k+1)*4
def zK {nIn k r m b:ℕ} (c:CB nIn)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fnr fnc:(Fin nIn->Bool)->Fin (2^k)}
  {fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  {ffix fval:(Fin nIn->Bool)->Fin k->Bool}
  (P:Qp nIn c b fA fB fnr fnc fcr fcc fy fo)
  (prefFix:Q2 nIn c k ffix) (prefVal:Q2 nIn c k fval) :
  Q0 nIn c (Qh k (b+2))
   (fun c'=>Q9 nIn c' (k+1)
    (fun x=>qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) (ffix x) (fval x))):=
 let B:=b+2
 Q0.weaken (by unfold Qh;dsimp only [B];omega)<|
 let ZAcc (u:ℕ) (_:u ≤ 2^B) (c0:CB nIn):Type:=
  ∀ idx:Fin (2^B),idx.val < u->Q9 nIn c0 (k+1) (fun _=>if idx.val=0 then 1 else 0)
 have hZinit:ZAcc 0 (Nat.zero_le _) c:=fun _ h=>absurd h (by omega)
 (Q0.qe (Bstep:=k+1) (2^B) ZAcc c hZinit fun u hu c0 _ zacc=>
  Q0.weaken (by omega)<|
  let iu:Fin (2^B):=⟨u,hu⟩
  have hlt:(if iu.val=0 then 1 else 0) < 2^(k+1):=by
   have h2:2 ≤ 2^(k+1):=by rw [pow_succ];have:=Nat.two_pow_pos k;omega
   split_ifs <;> omega
  (qS c0 (k+1) (if iu.val=0 then 1 else 0) hlt).bind fun _ h1 v=>
  Q0.pure fun idx hidx=>
   if hlt':idx.val < u then (zacc idx hlt').lift h1
   else
    have heq:idx=iu:=Fin.ext (by dsimp [iu];omega)
    heq▸v).bind fun c0 h0 initTbl=>
 let DP0:SDP nIn c0 B (k+1) (fun _ idx=>if idx.val=0 then 1 else 0):=
  ⟨fun idx=>initTbl idx idx.isLt⟩
 let dpAt (t:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
  ((dF k).take t).foldl
   (fun D i=>zD b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) (ffix x) (fval x) i D)
   (fun idx=>if idx.val=0 then 1 else 0)
 let Acc (t:ℕ) (_:t ≤ k) (c1:CB nIn):Type:=SDP nIn c1 B (k+1) (dpAt t)
 have hinit:Acc 0 (Nat.zero_le k) c0:=DP0.cast (fun _ _=>rfl)
 (Q0.qe (Bstep:=QD k B) k Acc c0 hinit fun t ht c1 h1 Dc=>
  Q0.weaken (by unfold QD;dsimp only [B];omega)<|
  let it:Fin k:=⟨t,ht⟩
  let h01:=h0.trans h1
  (de c1 ((P.Gin it).lift h01) Dc).bind fun c2 h2 DP1=>
  let d2At (u:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
   ((dF k).take u).foldl (fun D z=>
    qY B (decide (z∈qq r (fA x) (fB x) (fo x it))&&!decide (z∈Q5 r (fA x) (fB x) (fo x) it.val))
     (qO (q7 (qy r b (fA x) (fB x) (fo x) it z.val))) (ffix x z) (fval x z) D)
    (jZ (qk (vL (fA x) (fB x) (fo x) it.val) (j7 (fA x) (fB x) (fo x) it) B) (dpAt t x))
  let A2 (u:ℕ) (_:u ≤ k) (c3:CB nIn):Type:=SDP nIn c3 B (k+1) (d2At u)
  have hA2:A2 0 (Nat.zero_le k) c2:=DP1.cast (fun _ _=>rfl)
  (Q0.qe (Bstep:=Qw B (k+1)) k A2 c2 hA2 fun u hu c3 h3 D2c=>
   let zu:Fin k:=⟨u,hu⟩
   let h03:=h01.trans (h2.trans h3)
   (d0 c3 (((P.introCond it).at zu).lift h03) ((P.introOH it zu).lift h03)
    ((prefFix.at zu).lift h03) ((prefVal.at zu).lift h03) D2c).bind fun _ _ D2'=>
   have htake:(dF k).take (u+1)=(dF k).take u ++ [zu]:=by
    rw [dJ (by simp;omega)];simp [zu]
   have hstep2:∀ x,d2At (u+1) x=qY B
     (decide (zu∈qq r (fA x) (fB x) (fo x it))&&!decide (zu∈Q5 r (fA x) (fB x) (fo x) it.val))
     (qO (q7 (qy r b (fA x) (fB x) (fo x) it zu.val))) (ffix x zu) (fval x zu) (d2At u x):=fun x=>by
    change ((dF k).take (u+1)).foldl _ _=_
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   Q0.pure<|D2'.cast fun x idx=>by rw [hstep2 x]).bind fun c3 h3 DP2=>
  let d3At (s:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
   ((dF B).take s).foldl
    (fun D q=>vh B q (jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) it q) D)
    (d2At k x)
  let A3 (s:ℕ) (_:s ≤ B) (c4:CB nIn):Type:=SDP nIn c4 B (k+1) (d3At s)
  have hA3:A3 0 (Nat.zero_le B) c3:=DP2.cast (fun _ _=>rfl)
  let h03:=h01.trans (h2.trans h3)
  (Q0.qe (Bstep:=2^B*(4*(k+1))) B A3 c3 hA3 fun s hs c4 h4 D3c=>
   let qs:Fin B:=⟨s,hs⟩
   (gf c4 qs ((P.flArr it qs).lift (h03.trans h4)) D3c).bind fun _ _ D3'=>
   have htake:(dF B).take (s+1)=(dF B).take s ++ [qs]:=by
    rw [dJ (by simp;omega)];simp [qs]
   have hstep3:∀ x,d3At (s+1) x=vh B qs
     (jz b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) it qs) (d3At s x):=fun x=>by
    change ((dF B).take (s+1)).foldl _ _=_
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   Q0.pure<|D3'.cast fun x idx=>by rw [hstep3 x]).bind fun c4 h4 DP3=>
  let d4At (u:ℕ) (x:Fin nIn->Bool):Fin (2^B)->ℕ:=
   ((dF k).take u).foldl (fun D z=>
    let cond:=decide (z∈Qi r (fA x) (fB x) (fo x) it)&&!decide (z∈Q5 r (fA x) (fB x) (fo x) (it.val+1))
    let Mz:=ql r b (fA x) (fB x) (fo x) it z.val
    qI B cond (Mz z) (qV (q7 Mz)) (qZ B k cond (Mz z) D)) (d3At B x)
  let A4 (u:ℕ) (_:u ≤ k) (c5:CB nIn):Type:=SDP nIn c5 B (k+1) (d4At u)
  have hA4:A4 0 (Nat.zero_le k) c4:=DP3.cast (fun _ _=>rfl)
  let h04:=h03.trans h4
  (Q0.qe (Bstep:=Qn B (k+1)+Qr B (k+1)) k A4 c4 hA4 fun u hu c5 h5 D4c=>
   let zu:Fin k:=⟨u,hu⟩
   let h05:=h04.trans h5
   (gR c5 (((P.forgetCond it).at zu).lift h05) ((P.forgetSOH it zu).lift h05) D4c).bind fun c6 h6 D4a=>
   let h06:=h05.trans h6
   (ge c6 (((P.forgetCond it).at zu).lift h06) ((P.forgetSOH it zu).lift h06)
    ((P.forgetLoOH it zu).lift h06) D4a).bind fun _ _ D4'=>
   have htake:(dF k).take (u+1)=(dF k).take u ++ [zu]:=by
    rw [dJ (by simp;omega)];simp [zu]
   have hstep4:∀ x,d4At (u+1) x =
     let cond:=decide (zu∈Qi r (fA x) (fB x) (fo x) it)&&!decide (zu∈Q5 r (fA x) (fB x) (fo x) (it.val+1))
     let Mz:=ql r b (fA x) (fB x) (fo x) it zu.val
     qI B cond (Mz zu) (qV (q7 Mz)) (qZ B k cond (Mz zu) (d4At u x)):=fun x=>by
    change ((dF k).take (u+1)).foldl _ _=_
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
   Q0.pure<|D4'.cast fun x idx=>by rw [hstep4 x]).bind fun c5 h5 DP4=>
  let h05:=h04.trans h5
  (dB c5 ((P.keepArr it).lift h05) DP4).bind fun c6 h6 DP5=>
  (de c6 ((P.GoutInv it).lift (h05.trans h6)) DP5).bind fun _ _ DP6=>
  have htake:(dF k).take (t+1)=(dF k).take t ++ [it]:=by
   rw [dJ (by simp;omega)];simp [it]
  have hstep:∀ x,dpAt (t+1) x =
    zD b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) (ffix x) (fval x) it (dpAt t x):=fun x=>by
   change ((dF k).take (t+1)).foldl _ _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure<|DP6.cast fun x idx=>by
   rw [hstep x,g8]
   dsimp only [d4At,d3At,d2At,B]
   rw [show (dF k).take k=dF k by simp,
     show (dF (b+2)).take (b+2)=dF (b+2) by simp]).bind fun c1 h1 DPF=>
 let h01:=h0.trans h1
 (gz c1 (P.poolAll.lift h01) (prefFix.lift h01) (DPF.tbl ⟨0,Nat.two_pow_pos B⟩)).bind fun c2 h2 vsh=>
 (qS c2 (k+1) 0 (Nat.two_pow_pos _)).bind fun c3 h3 vz=>
 (vH c3 (P.okAll.lift (h01.trans (h2.trans h3))) (vsh.lift h3) vz).bind fun _ _ vres=>
 Q0.pure<|vres.cast fun x=>by
  unfold qX;dsimp only [dpAt,B]
  rw [show (dF k).take k=dF k by simp]
def QB (k B:ℕ):ℕ:=
 k+k+1+(k+1)+Qh k B +
 k*(Qh k B+(1+(k+1)*10)+(k+1)*4+(1+(k+1)*12)+(k+1)*4+k*4)
def dx {nIn k r m b:ℕ} (c:CB nIn)
  {fA fB:(Fin nIn->Bool)->Fin k->Q1 m}
  {fnr fnc:(Fin nIn->Bool)->Fin (2^k)}
  {fcr fcc:(Fin nIn->Bool)->Fin r->Fin (2^k)}
  {fy:(Fin nIn->Bool)->Q1 m} {fo:(Fin nIn->Bool)->Fin k->Fin k}
  {ft:(Fin nIn->Bool)->ℕ}
  (P:Qp nIn c b fA fB fnr fnc fcr fcc fy fo)
  (vt:Q9 nIn c (k+1) ft) :
  Q0 nIn c (QB k (b+2))
   (fun c'=>
    Q9 nIn c' (k+1) (fun x=>qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) (fun _=>false) (fun _=>false)) ×
    Q2 nIn c' k (fun x=>jn b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) (ft x))):=
 let B:=b+2
 Q0.weaken (by unfold QB;dsimp only [B];omega)<|
 (vq c k (fun _=>false)).bind fun c0 h0 vfVec=>
 (vq c0 k (fun _=>false)).bind fun c1 h1 vfVec2=>
 (vJ c1 true).bind fun c2 h2 vtrue=>
 (qS c2 (k+1) 0 (Nat.two_pow_pos _)).bind fun c3 h3 vzero=>
 let h03:=h0.trans (h1.trans (h2.trans h3))
 (zK c3 (P.lift h03) (vfVec.lift (h1.trans (h2.trans h3))) (vfVec2.lift (h2.trans h3))).bind fun c4 h4 vtot=>
 let h04:=h03.trans h4
 let stAt (s:ℕ) (x:Fin nIn->Bool):ℕ × (Fin k->Bool) × (Fin k->Bool):=
  ((dF k).take s).foldl
   (ja b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x))
   (ft x,fun _=>false,fun _=>false)
 let Acc (s:ℕ) (_:s ≤ k) (c5:CB nIn):Type:=
  Q9 nIn c5 (k+1) (fun x=>(stAt s x).1) ×
  Q2 nIn c5 k (fun x=>(stAt s x).2.1) ×
  Q2 nIn c5 k (fun x=>(stAt s x).2.2)
 have hinit:Acc 0 (Nat.zero_le k) c4:=
  ⟨(vt.lift h04).cast (fun _=>rfl),
  (vfVec.lift (h1.trans (h2.trans (h3.trans h4)))).cast (fun _ _=>rfl),
  (vfVec2.lift (h2.trans (h3.trans h4))).cast (fun _ _=>rfl)⟩
 (Q0.qe (Bstep:=Qh k B+(1+(k+1)*10)+(k+1)*4+(1+(k+1)*12)+(k+1)*4+k*4)
   k Acc c4 hinit fun s hs c5 h5 ⟨rem,fx,vl⟩=>
  Q0.weaken (by dsimp only [B];omega)<|
  let st:Fin k:=⟨s,hs⟩
  let pos:Fin k:=⟨k - 1 - s,by omega⟩
  let h05:=h04.trans h5
  let vtrue5:=vtrue.lift (h3.trans (h4.trans h5))
  let vf5:=(vfVec.at pos).lift (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  let fix':Q2 nIn c5 k (fun x z=>if z=pos then true else (stAt s x).2.1 z):=
   ⟨fun z=>if z=pos then vtrue5.w else fx.ws z,
   fun z=>by split_ifs;exact vtrue5.hw;exact fx.hws z,
   fun x z=>by split_ifs;exact vtrue5.heval x;exact fx.heval x z⟩
  let val0:Q2 nIn c5 k (fun x z=>if z=pos then false else (stAt s x).2.2 z):=
   ⟨fun z=>if z=pos then vf5.w else vl.ws z,
   fun z=>by split_ifs;exact vf5.hw;exact vl.hws z,
   fun x z=>by split_ifs;exact vf5.heval x;exact vl.heval x z⟩
  let val1:Q2 nIn c5 k (fun x z=>if z=pos then true else (stAt s x).2.2 z):=
   ⟨fun z=>if z=pos then vtrue5.w else vl.ws z,
   fun z=>by split_ifs;exact vtrue5.hw;exact vl.hws z,
   fun x z=>by split_ifs;exact vtrue5.heval x;exact vl.heval x z⟩
  (zK c5 (P.lift h05) fix' val0).bind fun c6 h6 vc0=>
  (g4 c6 (rem.lift h6) vc0).bind fun c7 h7 goLeft=>
  (vH c7 goLeft (vzero.lift (h4.trans (h5.trans (h6.trans h7)))) (vc0.lift h7)).bind fun c8 h8 c0Clamp=>
  have hle:∀ x,(if decide ((stAt s x).1 < qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x)
     (fun z=>if z=pos then true else (stAt s x).2.1 z) (fun z=>if z=pos then false else (stAt s x).2.2 z))=true
    then 0 else qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x)
     (fun z=>if z=pos then true else (stAt s x).2.1 z) (fun z=>if z=pos then false else (stAt s x).2.2 z)) ≤ (stAt s x).1:=by
   intro x;split_ifs with h
   ·exact Nat.zero_le _
   ·simp only [dG] at h;omega
  let h58:=h6.trans (h7.trans h8)
  (dz c8 (rem.lift h58) c0Clamp hle).bind fun c9 h9 remSub=>
  let h79:=h8.trans h9
  (vH c9 (goLeft.lift h79) (rem.lift (h58.trans h9)) remSub).bind fun c10 h10 rem'=>
  let h510:=h58.trans (h9.trans h10)
  (vd c10 (goLeft.lift (h79.trans h10)) (val0.lift h510) (val1.lift h510)).bind fun _ h11 val'=>
  have htake:(dF k).take (s+1)=(dF k).take s ++ [st]:=by
   rw [dJ (by simp;omega)];simp [st]
  have hstep:∀ x,stAt (s+1) x=ja b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x) (stAt s x) st:=fun x=>by
   change ((dF k).take (s+1)).foldl _ _=_
   rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
  Q0.pure
   ⟨(rem'.lift h11).cast fun x=>by
     rw [hstep x];unfold ja
     set c0v:=qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x)
      (fun z=>if z=pos then true else (stAt s x).2.1 z) (fun z=>if z=pos then false else (stAt s x).2.2 z)
     change (if decide ((stAt s x).1 < c0v)=true then (stAt s x).1 else (stAt s x).1 - (if decide ((stAt s x).1 < c0v)=true then 0 else c0v)) =
      (if (stAt s x).1 < c0v then ((stAt s x).1,_,_) else ((stAt s x).1 - c0v,_,_)).1
     by_cases h:(stAt s x).1 < c0v <;> simp [h],
   (fix'.lift (h510.trans h11)).cast fun x z=>by
     rw [hstep x];unfold ja
     set c0v:=qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x)
      (fun z=>if z=pos then true else (stAt s x).2.1 z) (fun z=>if z=pos then false else (stAt s x).2.2 z)
     change (if z=pos then true else (stAt s x).2.1 z) =
      (if (stAt s x).1 < c0v then (_,fun z=>if z=pos then true else (stAt s x).2.1 z,_)
      else (_,fun z=>if z=pos then true else (stAt s x).2.1 z,_)).2.1 z
     by_cases h:(stAt s x).1 < c0v <;> simp [h],
   val'.cast fun x z=>by
     rw [hstep x];unfold ja
     set c0v:=qX b (fA x) (fB x) (fnr x) (fnc x) (fcr x) (fcc x) (fy x) (fo x)
      (fun z=>if z=pos then true else (stAt s x).2.1 z) (fun z=>if z=pos then false else (stAt s x).2.2 z)
     change (if decide ((stAt s x).1 < c0v)=true then (if z=pos then false else (stAt s x).2.2 z)
         else (if z=pos then true else (stAt s x).2.2 z)) =
      (if (stAt s x).1 < c0v then (_,_,fun z=>if z=pos then false else (stAt s x).2.2 z)
      else (_,_,fun z=>if z=pos then true else (stAt s x).2.2 z)).2.2 z
     by_cases h:(stAt s x).1 < c0v <;> simp [h]⟩).bind fun _ h5 ⟨_,_,valF⟩=>
 Q0.pure
  ⟨vtot.lift h5,
  valF.cast fun x z=>by
   simp only [stAt,jn,show (dF k).take k=dF k by simp]⟩
def jo {nIn:ℕ} (c:CB nIn) (len:ℕ) (idx:Fin len->Fin nIn) :
  Q2 nIn c len (fun x q=>x (idx q)):=
 ⟨fun q=>(idx q).val,fun q=>(Q4.input c (idx q)).hw,fun x q=>(Q4.input c (idx q)).heval x⟩
def vE (k r m:ℕ):ℕ:=
 2*k+2*r*k+2*k*m+m+2*(k+1)
def zb {k r m:ℕ} (x:Fin (vE k r m)->Bool):Fin (2^k):=
 qa (fun q:Fin k=>x ⟨q.val,by dsimp [vE];omega⟩)
def zc {k r m:ℕ} (x:Fin (vE k r m)->Bool):Fin (2^k):=
 qa (fun q:Fin k=>x ⟨k+q.val,by dsimp [vE];omega⟩)
def zd {k r m:ℕ} (x:Fin (vE k r m)->Bool) (j:Fin r):Fin (2^k):=
 qa (fun q:Fin k=>x ⟨2*k+j.val*k+q.val,by dsimp [vE];have:=j.isLt;have:=q.isLt;nlinarith⟩)
def ze {k r m:ℕ} (x:Fin (vE k r m)->Bool) (j:Fin r):Fin (2^k):=
 qa (fun q:Fin k=>x ⟨2*k+r*k+j.val*k+q.val,by dsimp [vE];have:=j.isLt;have:=q.isLt;nlinarith⟩)
def yK {k r m:ℕ} (x:Fin (vE k r m)->Bool) (p:Fin k) (q:Fin m):Bool:=
 x ⟨2*k+2*r*k+p.val*m+q.val,by dsimp [vE];have:=p.isLt;have:=q.isLt;nlinarith⟩
def yJ {k r m:ℕ} (x:Fin (vE k r m)->Bool) (p:Fin k) (q:Fin m):Bool:=
 x ⟨2*k+2*r*k+k*m+p.val*m+q.val,by dsimp [vE];have:=p.isLt;have:=q.isLt;nlinarith⟩
def zS {k r m:ℕ} (x:Fin (vE k r m)->Bool) (q:Fin m):Bool:=
 x ⟨2*k+2*r*k+2*k*m+q.val,by dsimp [vE];have:=q.isLt;omega⟩
def zv {k r m:ℕ} (x:Fin (vE k r m)->Bool):Fin (2^(k+1)):=
 qa (fun q:Fin (k+1)=>x ⟨2*k+2*r*k+2*k*m+m+q.val,by dsimp [vE];have:=q.isLt;omega⟩)
def zw {k r m:ℕ} (x:Fin (vE k r m)->Bool):Fin (2^(k+1)):=
 qa (fun q:Fin (k+1)=>x ⟨2*k+2*r*k+2*k*m+m+(k+1)+q.val,by dsimp [vE];have:=q.isLt;omega⟩)
def Qt (k r m b h:ℕ):ℕ:=
 700*k^(2*h)*(k+m+2)^3+(k+m+2)+(2+(k+m+2)*10) +
 Qc k r m (b+2) (k+m+4)+QB k (b+2) +
 (1+(k+1)*10)+(k+1)+(1+(k+1)*6) +
 (1+k*((k+1)+(1+(k+1)*6)+2))+3
noncomputable def zk (k r m b h:ℕ)
  (hk:0 < k) (hb:b ≤ k+m) (hh:0 < h) :
  Q0 (vE k r m) (CB.zO (vE k r m)) (Qt k r m b h)
   (fun c'=>Q4 (vE k r m) c' (fun x=>
    let o:=qW hk r h (yK x) (yJ x)
    let tot:=qX b (yK x) (yJ x) (zb x) (zc x) (zd x) (ze x) (zS x) o (fun _=>false) (fun _=>false)
    let bits:=jn b (yK x) (yJ x) (zb x) (zc x) (zd x) (ze x) (zS x) o (zv x).val
    decide (qQ r h (yK x) (yJ x) ∅ ≤ b) &&
    (decide ((zv x).val < tot) &&
    (decide ((zw x).val=0)||decide (∃ s:Fin k,(zw x).val=s.val+1/\bits s=true))))):=
 let nIn:=vE k r m
 let c0:=CB.zO nIn
 let vnr:Q2 nIn c0 k (fun x q=>(zb x).val.testBit q.val):=
  (jo c0 k (fun q=>⟨q.val,by dsimp [nIn,vE];omega⟩)).cast fun x q=>
   (qb _ q).symm
 let vnc:Q2 nIn c0 k (fun x q=>(zc x).val.testBit q.val):=
  (jo c0 k (fun q=>⟨k+q.val,by dsimp [nIn,vE];omega⟩)).cast fun x q=>
   (qb _ q).symm
 let vcr (j:Fin r):Q2 nIn c0 k (fun x q=>(zd x j).val.testBit q.val):=
  (jo c0 k (fun q=>⟨2*k+j.val*k+q.val,by dsimp [nIn,vE];have:=j.isLt;have:=q.isLt;nlinarith⟩)).cast fun x q=>
   (qb _ q).symm
 let vcc (j:Fin r):Q2 nIn c0 k (fun x q=>(ze x j).val.testBit q.val):=
  (jo c0 k (fun q=>⟨2*k+r*k+j.val*k+q.val,by dsimp [nIn,vE];have:=j.isLt;have:=q.isLt;nlinarith⟩)).cast fun x q=>
   (qb _ q).symm
 let vA (p:Fin k):Q2 nIn c0 m (fun x=>yK x p):=
  jo c0 m (fun q=>⟨2*k+2*r*k+p.val*m+q.val,by dsimp [nIn,vE];have:=p.isLt;have:=q.isLt;nlinarith⟩)
 let vB (p:Fin k):Q2 nIn c0 m (fun x=>yJ x p):=
  jo c0 m (fun q=>⟨2*k+2*r*k+k*m+p.val*m+q.val,by dsimp [nIn,vE];have:=p.isLt;have:=q.isLt;nlinarith⟩)
 let vy:Q2 nIn c0 m zS:=
  jo c0 m (fun q=>⟨2*k+2*r*k+2*k*m+q.val,by dsimp [nIn,vE];have:=q.isLt;omega⟩)
 let vt:Q9 nIn c0 (k+1) (fun x=>(zv x).val):=
  ⟨(jo c0 (k+1) (fun q=>⟨2*k+2*r*k+2*k*m+m+q.val,by dsimp [nIn,vE];have:=q.isLt;omega⟩)).cast fun x q=>
   (qb _ q).symm,
  fun x=>(zv x).isLt⟩
 let vj:Q9 nIn c0 (k+1) (fun x=>(zw x).val):=
  ⟨(jo c0 (k+1) (fun q=>⟨2*k+2*r*k+2*k*m+m+(k+1)+q.val,by dsimp [nIn,vE];have:=q.isLt;omega⟩)).cast fun x q=>
   (qb _ q).symm,
  fun x=>(zw x).isLt⟩
 have hbLt:b < 2^(k+m+2):=lt_of_le_of_lt hb (lt_trans (by omega) Nat.lt_two_pow_self)
 have hW:1 ≤ k+m+4:=by omega
 have hmW:m < 2^(k+m+4):=lt_trans (by omega) Nat.lt_two_pow_self
 have h2BW:2*(b+2) < 2^(k+m+4):=g9 hb
 Q0.weaken (by unfold Qt;omega)<|
 (df c0 r h hk hh vA vB).bind fun c1 h1 ⟨vdpW,ordOH⟩=>
 (qS c1 (k+m+2) b hbLt).bind fun c2 h2 vb=>
 (dt c2 (vdpW.lift h2) vb).bind fun c3 h3 vWidthOk=>
 let h03:=h1.trans (h2.trans h3)
 (gA c3 hk hW hmW h2BW (fun p=>(vA p).lift h03) (fun p=>(vB p).lift h03)
  (vnr.lift h03) (vnc.lift h03) (fun j=>(vcr j).lift h03) (fun j=>(vcc j).lift h03)
  (vy.lift h03) (fun t=>(ordOH t).lift (h2.trans h3))).bind fun c4 h4 P=>
 let h04:=h03.trans h4
 (dx c4 P (vt.lift h04)).bind fun c5 h5 ⟨vtot,vbits⟩=>
 let h05:=h04.trans h5
 (g4 c5 (vt.lift h05) vtot).bind fun c6 h6 vtLt=>
 (qS c6 (k+1) 0 (Nat.two_pow_pos _)).bind fun c7 h7 vz0=>
 (zH c7 (vj.lift (h05.trans (h6.trans h7))) vz0).bind fun c8 h8 vj0=>
 (vJ c8 false).bind fun c9 h9 vfalse=>
 let JAcc (u:ℕ) (_:u ≤ k) (c10:CB nIn):Type:=
  Q4 nIn c10 (fun x=>decide (∃ s:Fin k,s.val < u/\(zw x).val=s.val+1 /\
   jn b (yK x) (yJ x) (zb x) (zc x) (zd x) (ze x) (zS x) (qW hk r h (yK x) (yJ x)) (zv x).val s=true))
 have hJinit:JAcc 0 (Nat.zero_le k) c9:=vfalse.cast fun _=>by simp
 let h59:=h6.trans (h7.trans (h8.trans h9))
 let h09:=h05.trans h59
 (Q0.qe (Bstep:=(k+1)+(1+(k+1)*6)+2) k JAcc c9 hJinit fun u hu c10 h10 jacc=>
  Q0.weaken (by omega)<|
  let su:Fin k:=⟨u,hu⟩
  have hu1:u+1 < 2^(k+1):=lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  (qS c10 (k+1) (u+1) hu1).bind fun c11 h11 cu1=>
  (zH c11 (vj.lift (h09.trans (h10.trans h11))) cu1).bind fun c12 h12 veq=>
  (vg c12 veq ((vbits.at su).lift (h59.trans (h10.trans (h11.trans h12))))).bind fun c13 h13 vand=>
  (yr c13 (jacc.lift (h11.trans (h12.trans h13))) vand).bind fun _ _ vor=>
  Q0.pure<|vor.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [dH,dI,dG]
   constructor
   ·rintro (⟨s,hs,h1',h2'⟩ | ⟨h1',h2'⟩)
    ·exact ⟨s,by omega,h1',h2'⟩
    ·exact ⟨su,by dsimp [su];omega,h1',h2'⟩
   ·rintro ⟨s,hs,h1',h2'⟩
    by_cases hlt:s.val < u
    ·left;exact ⟨s,hlt,h1',h2'⟩
    ·right;have heq:s=su:=Fin.ext (by dsimp [su];omega);subst heq;exact ⟨h1',h2'⟩).bind fun c10 h10 vjBit0=>
 let vjBit:Q4 nIn c10 (fun x=>decide (∃ s:Fin k,(zw x).val=s.val+1 /\
   jn b (yK x) (yJ x) (zb x) (zc x) (zd x) (ze x) (zS x) (qW hk r h (yK x) (yJ x)) (zv x).val s=true)):=
  vjBit0.cast fun x=>by
   apply Bool.eq_iff_iff.mpr;simp only [dG]
   exact ⟨fun ⟨s,_,h1',h2'⟩=>⟨s,h1',h2'⟩,fun ⟨s,h1',h2'⟩=>⟨s,s.isLt,h1',h2'⟩⟩
 (yr c10 (vj0.lift (h9.trans h10)) vjBit).bind fun c11 h11 vor=>
 (vg c11 (vtLt.lift (h7.trans (h8.trans (h9.trans (h10.trans h11))))) vor).bind fun c12 h12 vand1=>
 (vg c12 (vWidthOk.lift (h4.trans (h5.trans (h59.trans (h10.trans (h11.trans h12)))))) vand1).bind fun _ _ vout=>
 Q0.pure<|vout.cast fun _=>rfl
set_option maxHeartbeats 600000 in
lemma zp {k r m b h:ℕ} (hk:0 < k) (hb:b ≤ k+m) (hh:0 < h) :
  Qt k r m b h ≤ 2^52*((k+r+m+5)^(4*h+20)+(k+r+m+5)^20*2^b):=by
 set N:=k+r+m+5
 set B:=b+2
 set W:=k+m+4
 set Wc:=k+1
 have h1:k ≤ N:=by omega
 have h2:r ≤ N:=by omega
 have h3:m ≤ N:=by omega
 have h4:B ≤ N:=by omega
 have h5:W ≤ N:=by omega
 have h6:Wc ≤ N:=by omega
 have hkm2:k+m+2 ≤ N:=by omega
 have h2B:2^B=4*2^b:=by dsimp [B];rw [pow_add];ring
 have h2bp:1 ≤ 2^b:=Nat.one_le_pow _ _ (by omega)
 have hN1:1 ≤ N:=by omega
 have hN2:N ≤ N^2:=by rw [pow_two];exact Nat.le_mul_of_pos_right N (by omega)
 have hN3:N^2 ≤ N^3:=by rw [pow_succ];exact Nat.le_mul_of_pos_right _ (by omega)
 have hN4:N^3 ≤ N^4:=by rw [pow_succ];exact Nat.le_mul_of_pos_right _ (by omega)
 have hN5':N^4 ≤ N^5:=by rw [pow_succ];exact Nat.le_mul_of_pos_right _ (by omega)
 have hN6:N^5 ≤ N^6:=by rw [pow_succ];exact Nat.le_mul_of_pos_right _ (by omega)
 have hN6_20:N^6 ≤ N^20:=Nat.pow_le_pow_right hN1 (by omega)
 have hmul2:∀ a c,a ≤ N->c ≤ N->a*c ≤ N^2:=fun a c ha hc=>by rw [pow_two];exact Nat.mul_le_mul ha hc
 have hmul3:∀ a c d,a ≤ N->c ≤ N->d ≤ N->a*(c*d) ≤ N^3:=fun a c d ha hc hd=>by
  rw [show N^3=N*N^2 by ring];exact Nat.mul_le_mul ha (hmul2 c d hc hd)
 have hplan:700*k^(2*h)*(k+m+2)^3 ≤ 700*N^(4*h+20):=by
  have hp1:k^(2*h) ≤ N^(4*h):=
   (Nat.pow_le_pow_left h1 _).trans (Nat.pow_le_pow_right hN1 (by omega))
  have hp2:(k+m+2)^3 ≤ N^20:=
   (Nat.pow_le_pow_left hkm2 3).trans (Nat.pow_le_pow_right hN1 (by omega))
  calc 700*k^(2*h)*(k+m+2)^3
    ≤ 700*N^(4*h)*N^20:=Nat.mul_le_mul (Nat.mul_le_mul_left 700 hp1) hp2
   _=700*N^(4*h+20):=by rw [mul_assoc,← pow_add]
 have htm:Qs k m ≤ 50*N^3:=by
  unfold Qs
  have hA:=hmul2 m m h3 h3
  have hB:=hmul3 k m m h1 h3 h3
  have hC:=hmul2 k m h1 h3
  have hE:k*(36*m*m+10*m)=36*(k*(m*m))+10*(k*m):=by ring
  rw [hE];omega
 have hts:Qm k m ≤ 250*N^3:=by
  unfold Qm
  have hA:=hmul2 k k h1 h1
  have hB:=hmul2 m m h3 h3
  have hC:=hmul3 m m m h3 h3 h3
  have hE:k*(1+k)+k*(1+k)+Qs k m+Qs k m +
    (3*(m*m)+m*(56*m*m+11*m))+(24*m*m+10*m+2) +
    k*(1+k*2)+k*(1+k*2)+k =
    5*k+6*(k*k)+2*Qs k m+38*(m*m)+56*(m*(m*m))+10*m+2:=by ring
  rw [hE];omega
 have hpt:Qj k m ≤ 400*N^4:=by
  unfold Qj
  have h1':(k+1)*Qm k m ≤ N*(250*N^3):=Nat.mul_le_mul h6 hts
  have h1'':N*(250*N^3)=250*N^4:=by ring
  have hA:=hmul2 m m h3 h3
  have hB:=hmul3 m m m h3 h3 h3
  have hC:=hmul2 k k h1 h1
  have hE:(k+1)*Qm k m+m*(m*1)+(3*(m*m)+m*(56*m*m+11*m))+(24*m*m+10*m+2) +
    k*(1+k)+k*(1+k*2) =
    (k+1)*Qm k m+39*(m*m)+56*(m*(m*m))+10*m+2+2*k+3*(k*k):=by ring
  rw [hE];omega
 have hpiv:QH m B W ≤ 40*N^3:=by
  unfold QH
  have hA:=hmul2 B m h4 h3;have hB:=hmul2 m W h3 h5
  have hC:=hmul3 m B W h3 h4 h5;have hD:=hmul3 m B m h3 h4 h3;have hF:=hmul2 m B h3 h4
  have hE:2*W+B*m+m*(1+15*W+B*(2+7*W+4*m)) =
    2*W+B*m+m+15*(m*W)+2*(m*B)+7*(m*(B*W))+4*(m*(B*m)):=by ring
  rw [hE];omega
 have hcrd:Qk m B W ≤ 50*N^3:=by
  unfold Qk
  have hA:=hmul2 m m h3 h3;have hB:=hmul2 m W h3 h5
  have hC:=hmul3 m B W h3 h4 h5;have hD:=hmul2 m B h3 h4
  have hE:2*W+B+m*(2+8*m+15*W+B*(6+7*W)) =
    2*W+B+2*m+8*(m*m)+15*(m*W)+6*(m*B)+7*(m*(B*W)):=by ring
  rw [hE];omega
 have hext:QF m B W ≤ 250*N^4:=by
  unfold QF
  have hBB:=hmul2 B B h4 h4;have hBW:=hmul2 B W h4 h5
  have hB3:=hmul3 B B B h4 h4 h4;have hB2W:=hmul3 B B W h4 h4 h5
  have hBc:B*Qk m B W ≤ N*(50*N^3):=Nat.mul_le_mul h4 hcrd
  have hBc2:N*(50*N^3)=50*N^4:=by ring
  have hE:QH m B W+2*W+2*B*B +
    B*(Qk m B W+2+25*B*B+7*B+15*W+B*(2+7*W+4*B)) +
    B*(2+33*B*B+9*B+15*W+B*(2+7*W+4*B)) =
    QH m B W+2*W+22*(B*B)+B*Qk m B W+4*B+66*(B*(B*B)) +
    30*(B*W)+14*(B*(B*W)):=by ring
  rw [hE];omega
 have hinv:QE B ≤ 50*N^4:=by
  unfold QE QK
  have hBB:=hmul2 B B h4 h4;have hB3:=hmul3 B B B h4 h4 h4
  have hE:B*B+B*(B*(2+2*B)+B*(8*B+8*B)+B*(1+8*B+8*B)) =
    4*(B*B)+34*(B*(B*B)):=by ring
  rw [hE];omega
 have hpush:QC B Wc ≤ 120*(N^3*2^b):=by
  unfold QC QK
  have hBB:=hmul2 B B h4 h4;have hB3:=hmul3 B B B h4 h4 h4;have hB2W:=hmul3 B B Wc h4 h4 h6
  have hE:B*(B*(2+2*B)+B*(8*B+2^B*(4*Wc))+B*(1+8*B+2^B*(4*Wc))) =
    3*(B*B)+18*(B*(B*B))+32*(B*(B*Wc)*2^b):=by rw [h2B];ring
  rw [hE]
  have hA:3*(B*B)+18*(B*(B*B)) ≤ 21*(N^3*2^b):=
   (show 3*(B*B)+18*(B*(B*B)) ≤ 21*N^3 by omega).trans (Nat.mul_le_mul_left 21 (Nat.le_mul_of_pos_right _ (by omega)))
  have hB':32*(B*(B*Wc)*2^b) ≤ 32*(N^3*2^b):=
   Nat.mul_le_mul_left 32 (Nat.mul_le_mul_right _ hB2W)
  omega
 have hsi:Qg k B ≤ 10*N^2:=by
  unfold Qg
  have hA:=hmul2 B k h4 h1;have hB:=hmul2 B B h4 h4
  have hE:B*(1+k)+B*(1+B)+B*4=6*B+B*k+B*B:=by ring
  rw [hE];omega
 have hsf:Qe k B ≤ 30*N^2:=by
  unfold Qe
  have hA:=hmul2 B k h4 h1;have hB:=hmul2 B B h4 h4;have hC:=hmul2 k B h1 h4
  have hE:B*(1+k)+B*(2*B)+B+k*(2+12*B)+k*(4*B) =
    2*B+B*k+2*(B*B)+2*k+16*(k*B):=by ring
  rw [hE];omega
 have hidx:Qz k r m B ≤ 100*N^2:=by
  unfold Qz
  have hA:=hmul2 k B h1 h4;have hB:=hmul2 r k h2 h1
  have hC:=hmul2 B m h4 h3;have hD:=hmul2 m m h3 h3
  have hE:k*(2+B)+2*(k*4+r*(k*22))+2*(1+k*2)+2 +
    B+(m+B*(8*m))+m*(8*m+1)+(1+m)+1 =
    14*k+k*B+44*(r*k)+B+3*m+8*(B*m)+8*(m*m)+6:=by ring
  rw [hE];omega
 have hsp:Qf k r m B W ≤ 2000*(N^4*2^b):=by
  unfold Qf Qy Qx
  have hm2:=hmul2 m m h3 h3;have hm3:=hmul3 m m m h3 h3 h3
  have hk2:=hmul2 k k h1 h1;have hmk:=hmul2 m k h3 h1
  have hksi:k*Qg k B ≤ N*(10*N^2):=Nat.mul_le_mul h1 hsi
  have hksf:k*Qe k B ≤ N*(30*N^2):=Nat.mul_le_mul h1 hsf
  have h10:N*(10*N^2)=10*N^3:=by ring
  have h30:N*(30*N^2)=30*N^3:=by ring
  have hE1:(3*(m*m)+m*(56*m*m+11*m))+2*QF m B W+QE B +
    k*(1+k*2)+k+2*k+2*k+k*Qg k B+k*Qe k B +
    2*(m*(1+k*2))+2*(1+m)+m*4+3*Qk m B W+QH m B W =
    14*(m*m)+56*(m*(m*m))+2*QF m B W+QE B+6*k+2*(k*k) +
    k*Qg k B+k*Qe k B+8*m+4*(m*k)+2+3*Qk m B W+QH m B W:=by ring
  have hpol:(3*(m*m)+m*(56*m*m+11*m))+2*QF m B W+QE B +
    k*(1+k*2)+k+2*k+2*k+k*Qg k B+k*Qe k B +
    2*(m*(1+k*2))+2*(1+m)+m*4+3*Qk m B W+QH m B W ≤ 1000*(N^4*2^b):=
   (by rw [hE1];omega:_ ≤ 1000*N^4).trans (Nat.mul_le_mul_left 1000 (Nat.le_mul_of_pos_right _ (by omega)))
  have h2bi:2^B*Qz k r m B ≤ 400*(N^4*2^b):=by
   rw [h2B];calc 4*2^b*Qz k r m B ≤ 4*2^b*(100*N^2):=Nat.mul_le_mul_left _ hidx
    _=400*(N^2*2^b):=by ring
    _ ≤ 400*(N^4*2^b):=Nat.mul_le_mul_left 400 (Nat.mul_le_mul_right _ (hN3.trans hN4))
  have hfl:B*(2^B*10) ≤ 40*(N^4*2^b):=by
   rw [h2B,show B*(4*2^b*10)=40*(B*2^b) by ring]
   exact Nat.mul_le_mul_left 40 (Nat.mul_le_mul_right _ (h4.trans (hN2.trans (hN3.trans hN4))))
  omega
 have hpre:Qc k r m B W ≤ 3000*(N^5*2^b):=by
  unfold Qc
  have hkm:=hmul2 k m h1 h3;have hkB:=hmul2 k B h1 h4
  have hksp:k*Qf k r m B W ≤ 2000*(N^5*2^b):=by
   calc k*Qf k r m B W ≤ N*(2000*(N^4*2^b)):=Nat.mul_le_mul h1 hsp
    _=2000*(N^5*2^b):=by ring
  have hE:1+k*(2*m+3)=1+2*(k*m)+3*k:=by ring
  have hrest:(1+k*(2*m+3))+Qj k m+k*B ≤ 500*(N^5*2^b):=
   (by rw [hE];omega:_ ≤ 500*N^5).trans (Nat.mul_le_mul_left 500 (Nat.le_mul_of_pos_right _ (by omega)))
  omega
 have hdi:Qw B Wc ≤ 60*(N^2*2^b):=by
  unfold Qw
  have hBWc:=hmul2 B Wc h4 h6
  have hE:Wc+B*(5+2^B*(8*Wc))=Wc+5*B+32*(B*Wc*2^b):=by rw [h2B];ring
  rw [hE]
  have hA:Wc+5*B ≤ 6*(N^2*2^b):=
   (show Wc+5*B ≤ 6*N^2 by omega).trans (Nat.mul_le_mul_left 6 (Nat.le_mul_of_pos_right _ (by omega)))
  have hB':32*(B*Wc*2^b) ≤ 32*(N^2*2^b):=Nat.mul_le_mul_left 32 (Nat.mul_le_mul_right _ hBWc)
  omega
 have hds:Qn B Wc ≤ 100*(N^2*2^b):=by
  unfold Qn
  have hBWc:=hmul2 B Wc h4 h6
  have hE:Wc+B*(1+2^B*(1+15*Wc))=Wc+B+4*(B*2^b)+60*(B*Wc*2^b):=by rw [h2B];ring
  rw [hE]
  have hA:Wc+B ≤ 2*(N^2*2^b):=
   (show Wc+B ≤ 2*N^2 by omega).trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ (by omega)))
  have hB1:4*(B*2^b) ≤ 4*(N^2*2^b):=Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ (h4.trans hN2))
  have hB2:60*(B*Wc*2^b) ≤ 60*(N^2*2^b):=Nat.mul_le_mul_left 60 (Nat.mul_le_mul_right _ hBWc)
  omega
 have hdsw:Qr B Wc ≤ 40*(N^3*2^b):=by
  unfold Qr
  have hBB:=hmul2 B B h4 h4;have hB2W:=hmul3 B B Wc h4 h4 h6
  have hE:B*(B*(2+2^B*(4*Wc)))=2*(B*B)+16*(B*(B*Wc)*2^b):=by rw [h2B];ring
  rw [hE]
  have hA:2*(B*B) ≤ 2*(N^3*2^b):=
   (show 2*(B*B) ≤ 2*N^3 by omega).trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ (by omega)))
  have hB':16*(B*(B*Wc)*2^b) ≤ 16*(N^3*2^b):=Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right _ hB2W)
  omega
 have hdpst:QD k B ≤ 600*(N^4*2^b):=by
  unfold QD;rw [show k+1=Wc from rfl]
  have hBWc:=hmul2 B Wc h4 h6
  have hkdi:k*Qw B Wc ≤ 60*(N^4*2^b):=by
   calc k*Qw B Wc ≤ N*(60*(N^2*2^b)):=Nat.mul_le_mul h1 hdi
    _=60*(N^3*2^b):=by ring
    _ ≤ 60*(N^4*2^b):=Nat.mul_le_mul_left 60 (Nat.mul_le_mul_right _ hN4)
  have hds3:Qn B Wc ≤ 100*(N^3*2^b):=hds.trans (Nat.mul_le_mul_left 100 (Nat.mul_le_mul_right _ hN3))
  have hkdsw:k*(Qn B Wc+Qr B Wc) ≤ 140*(N^4*2^b):=by
   calc k*(Qn B Wc+Qr B Wc) ≤ N*(140*(N^3*2^b)):=Nat.mul_le_mul h1 (by omega)
    _=140*(N^4*2^b):=by ring
  have hpush4:QC B Wc ≤ 120*(N^4*2^b):=hpush.trans (Nat.mul_le_mul_left 120 (Nat.mul_le_mul_right _ hN4))
  have hfl:B*(2^B*(4*Wc)) ≤ 16*(N^4*2^b):=by
   rw [h2B,show B*(4*2^b*(4*Wc))=16*(B*Wc*2^b) by ring]
   exact Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right _ (hBWc.trans (hN3.trans hN4)))
  have hmk:Wc+2^B*(4*Wc) ≤ 17*(N^4*2^b):=by
   rw [h2B,show Wc+4*2^b*(4*Wc)=Wc+16*(Wc*2^b) by ring]
   have h1':Wc ≤ N^4*2^b:=(h6.trans (hN2.trans (hN3.trans hN4))).trans (Nat.le_mul_of_pos_right _ (by omega))
   have h2':16*(Wc*2^b) ≤ 16*(N^4*2^b):=Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right _ (h6.trans (hN2.trans (hN3.trans hN4))))
   omega
  omega
 have hcp:Qh k B ≤ 700*(N^5*2^b):=by
  unfold Qh;rw [show k+1=Wc from rfl]
  have hkdp:k*QD k B ≤ 600*(N^5*2^b):=by
   calc k*QD k B ≤ N*(600*(N^4*2^b)):=Nat.mul_le_mul h1 hdpst
    _=600*(N^5*2^b):=by ring
  have h1':2^B*Wc ≤ 4*(N^5*2^b):=by
   rw [h2B,show 4*2^b*Wc=4*(Wc*2^b) by ring]
   exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ (h6.trans (hN2.trans (hN3.trans (hN4.trans hN5')))))
  have hkW:=hmul2 k Wc h1 h6
  have hE:k*(4+15*Wc)+Wc+Wc*4=4*k+15*(k*Wc)+5*Wc:=by ring
  have hsh:k*(4+15*Wc)+Wc+Wc*4 ≤ 30*(N^5*2^b):=
   (by rw [hE];omega:_ ≤ 30*N^5).trans (Nat.mul_le_mul_left 30 (Nat.le_mul_of_pos_right _ (by omega)))
  omega
 have hunr:QB k B ≤ 1500*(N^6*2^b):=by
  unfold QB;rw [show k+1=Wc from rfl]
  have hlin:(1+Wc*10)+Wc*4+(1+Wc*12)+Wc*4+k*4 ≤ 50*(N^5*2^b):=
   (by omega:_ ≤ 50*N^5).trans (Nat.mul_le_mul_left 50 (Nat.le_mul_of_pos_right _ (by omega)))
  have hkst:k*(Qh k B+(1+Wc*10)+Wc*4+(1+Wc*12)+Wc*4+k*4) ≤ 750*(N^6*2^b):=by
   calc k*(Qh k B+(1+Wc*10)+Wc*4+(1+Wc*12)+Wc*4+k*4)
     ≤ N*(750*(N^5*2^b)):=Nat.mul_le_mul h1 (by omega)
    _=750*(N^6*2^b):=by ring
  have hcp6:Qh k B ≤ 700*(N^6*2^b):=hcp.trans (Nat.mul_le_mul_left 700 (Nat.mul_le_mul_right _ hN6))
  have hlo:k+k+1+Wc ≤ 50*(N^6*2^b):=
   (by omega:_ ≤ 50*N^6).trans (Nat.mul_le_mul_left 50 (Nat.le_mul_of_pos_right _ (by omega)))
  omega
 have hkW:=hmul2 k Wc h1 h6
 have hEtail:1+k*(Wc+(1+Wc*6)+2)=1+3*k+7*(k*Wc):=by ring
 have htail:(k+m+2)+(2+(k+m+2)*10)+(1+Wc*10)+Wc+(1+Wc*6) +
   (1+k*(Wc+(1+Wc*6)+2))+3 ≤ 500*(N^6*2^b):=
  (by rw [hEtail];omega:_ ≤ 500*N^6).trans (Nat.mul_le_mul_left 500 (Nat.le_mul_of_pos_right _ (by omega)))
 have hpre6:Qc k r m B W ≤ 3000*(N^6*2^b):=
  hpre.trans (Nat.mul_le_mul_left 3000 (Nat.mul_le_mul_right _ hN6))
 have h5000:5000*(N^6*2^b) ≤ 5000*(N^20*2^b):=
  Nat.mul_le_mul_left 5000 (Nat.mul_le_mul_right _ hN6_20)
 have htot2b:Qc k r m B W+QB k B +
   ((k+m+2)+(2+(k+m+2)*10)+(1+Wc*10)+Wc+(1+Wc*6) +
    (1+k*(Wc+(1+Wc*6)+2))+3) ≤ 5000*(N^20*2^b):=by omega
 have h52c1:700 ≤ 2^52:=(by decide:700 ≤ 2^10).trans (Nat.pow_le_pow_right (by omega) (by omega))
 have h52c2:5000 ≤ 2^52:=(by decide:5000 ≤ 2^13).trans (Nat.pow_le_pow_right (by omega) (by omega))
 have h52a:700*N^(4*h+20) ≤ 2^52*N^(4*h+20):=Nat.mul_le_mul_right _ h52c1
 have h52b:5000*(N^20*2^b) ≤ 2^52*(N^20*2^b):=Nat.mul_le_mul_right _ h52c2
 have hcore_eq:Qt k r m b h=700*k^(2*h)*(k+m+2)^3 +
   (Qc k r m B W+QB k B +
    ((k+m+2)+(2+(k+m+2)*10)+(1+Wc*10)+Wc+(1+Wc*6) +
     (1+k*(Wc+(1+Wc*6)+2))+3)):=by
  unfold Qt;dsimp only [B,W,Wc];ring
 rw [hcore_eq,mul_add (2^52)]
 exact Nat.add_le_add (hplan.trans h52a) (htot2b.trans h52b)
lemma qr {k r:ℕ} (c:Fin r->Fin (2^k)) :
  ((dF r).flatMap (fun j=>(List.range k).map (fun i=>(c j).val.testBit i))).length=r*k:=by
 simp [List.length_flatMap,List.map_const',List.sum_replicate,smul_eq_mul]
lemma gJ {k r:ℕ} (c:Fin r->Fin (2^k)) (j:Fin r) (q:Fin k) :
  (((dF r).flatMap (fun j=>(List.range k).map (fun i=>(c j).val.testBit i)))[j.val*k+q.val]?).getD false =
   (c j).val.testBit q.val:=by
 exact z3 c j q
lemma q9?_left {α:Type} (L1 L2:List α) {i:ℕ} (h:i < L1.length) :
  (L1 ++ L2)[i]?=L1[i]?:=List.getElem?_append_left h
lemma q9?_right {α:Type} (L1 L2:List α) {i:ℕ} (h:L1.length ≤ i) :
  (L1 ++ L2)[i]?=L2[i - L1.length]?:=List.getElem?_append_right h
noncomputable def zW (k r m b h:ℕ)
  (hk:0 < k) (hr:4 ≤ r) (hb:b ≤ k+m) (hh:0 < h) :
  {C:PEqualNP.CircuitLowerBounds.Circuit //
   PEqualNP.MetaComplexity.FanInTwo C /\
   PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k+2*r*k+2*k*m+m+2*(k+1)) C /\
   C.size ≤ 2^52*((k+r+m+5)^(4*h+20)+(k+r+m+5)^20*2^b) /\
   ∀ (A B:Fin k->Fin (2^m)) (nr nc:Fin (2^k)) (cr cc:Fin r->Fin (2^k))
    (y:Fin (2^m)) (t:Fin (2^(k+1))) (j:Fin (k+1)),
    let Ab:Fin k->Q1 m:=fun p q=>(A p).val.testBit q.val
    let Bb:Fin k->Q1 m:=fun p q=>(B p).val.testBit q.val
    let yb:Q1 m:=fun q=>y.val.testBit q.val
    let o:=qW hk r h Ab Bb
    let bits:=fun (a x:ℕ)=>(List.range a).map (fun i=>x.testBit i)
    let sched:=fun (c:Fin r->Fin (2^k))=>(dF r).flatMap (fun j=>bits k (c j).val)
    let pack:=fun (X:Fin k->Fin (2^m))=>(dF k).flatMap (fun p=>bits m (X p).val)
    let hit:Fin (2^k)->Prop:=fun w=>v4 k r m Ab Bb nr.val nc.val cr cc w.val=yb
    C.eval (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ pack A ++ pack B ++
     bits m y.val ++ bits (k+1) t.val ++ bits (k+1) j.val) =
     decide (qU r Ab Bb o ≤ b/\∃ w:Fin (2^k),hit w /\
      Nat.card {z:Fin (2^k) // z < w/\hit z}=t.val /\
      (j.val=0\/w.val.testBit (j.val - 1)=true)) }:=by
 let nIn:=vE k r m
 let res:=zk k r m b h hk hb hh
 let C:PEqualNP.CircuitLowerBounds.Circuit:=⟨res.c'.gates,res.val.w⟩
 refine ⟨C,?_,?_,?_,?_⟩
 ·intro g hg;exact res.c'.fanIn g hg
 ·intro j hj i hi
  have hgd:PEqualNP.MetaComplexity.NestedCover.gateAt C j=res.c'.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[]⟩:=by
   simp [PEqualNP.MetaComplexity.NestedCover.gateAt,C,List.getD,hj]
  rw [hgd] at hi;exact res.c'.reads j hj i hi
 ·have h1:=res.hsize
  have hsz:C.size ≤ Qt k r m b h:=by simpa [C,PEqualNP.CircuitLowerBounds.Circuit.size,CB.zO] using h1
  exact hsz.trans (zp hk hb hh)
 ·intro A B nr nc cr cc y t j
  dsimp only
  set bits:=fun (a x:ℕ)=>(List.range a).map (fun i=>x.testBit i)
  set sched:=fun (c:Fin r->Fin (2^k))=>(dF r).flatMap (fun j=>bits k (c j).val)
  set pack:=fun (X:Fin k->Fin (2^m))=>(dF k).flatMap (fun p=>bits m (X p).val)
  set inp:=bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ pack A ++ pack B ++
   bits m y.val ++ bits (k+1) t.val ++ bits (k+1) j.val
  have h2rk:2*r*k=r*k+r*k:=by ring
  have h2km:2*k*m=k*m+k*m:=by ring
  have hinp_len:inp.length=nIn:=by
   simp only [inp,bits,sched,pack,List.length_append,qd,qr]
   dsimp only [nIn,vE];ring
  let x:Fin nIn->Bool:=fun idx=>inp.getD idx.val false
  have hofFn:List.ofFn x=inp:=by
   apply List.ext_getElem
   ·simp [hinp_len]
   ·intro idx h1 h2
    simp only [List.getElem_ofFn,x,List.getD,List.getElem?_eq_getElem h2,Option.getD_some]
  have hpack_val_fin:∀ {a:ℕ} (v:Fin (2^a)),qa (fun q:Fin a=>v.val.testBit q.val)=v:=by
   intro a v;apply Fin.ext;apply Nat.eq_of_testBit_eq;intro q
   by_cases hq:q < a
   ·change (qu _).testBit (⟨q,hq⟩:Fin a).val=_;rw [qb]
   ·rw [Nat.testBit_lt_two_pow ((qa _).isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),
      Nat.testBit_lt_two_pow (v.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq)))]
  have hnr:zb x=nr:=by
   unfold zb;convert hpack_val_fin nr using 1;congr 1;funext q
   simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_left _ _ (by rw [qd];exact q.isLt)]
   exact yk k nr.val q.val q.isLt
  have hnc:zc x=nc:=by
   unfold zc;convert hpack_val_fin nc using 1;congr 1;funext q
   simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     show k+q.val - k=q.val by omega,
     q9?_left _ _ (by rw [qd];exact q.isLt)]
   exact yk k nc.val q.val q.isLt
  have hcr:zd x=cr:=by
   funext j0;unfold zd;convert hpack_val_fin (cr j0) using 1;congr 1;funext q
   simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     show 2*k+j0.val*k+q.val - k - k=j0.val*k+q.val by omega,
     q9?_left _ _ (by rw [qr];have:=j0.isLt;have:=q.isLt;nlinarith)]
   exact gJ cr j0 q
  have hcc:ze x=cc:=by
   funext j0;unfold ze;convert hpack_val_fin (cc j0) using 1;congr 1;funext q
   simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qr];omega),qr,
     show 2*k+r*k+j0.val*k+q.val - k - k - r*k=j0.val*k+q.val by omega,
     q9?_left _ _ (by rw [qr];have:=j0.isLt;have:=q.isLt;nlinarith)]
   exact gJ cc j0 q
  have hA:yK x=fun p q=>(A p).val.testBit q.val:=by
   funext p q;unfold yK;simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qr];omega),qr,
     show 2*k+2*r*k+p.val*m+q.val - k - k - r*k - r*k=p.val*m+q.val by omega,
     q9?_left _ _ (by rw [qp];have:=p.isLt;have:=q.isLt;nlinarith)]
   exact z3 A p q
  have hB:yJ x=fun p q=>(B p).val.testBit q.val:=by
   funext p q;unfold yJ;simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qp];omega),qp,
     show 2*k+2*r*k+k*m+p.val*m+q.val - k - k - r*k - r*k - k*m=p.val*m+q.val by omega,
     q9?_left _ _ (by rw [qp];have:=p.isLt;have:=q.isLt;nlinarith)]
   exact z3 B p q
  have hy:zS x=fun q=>y.val.testBit q.val:=by
   funext q;unfold zS;simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qp];omega),qp,
     q9?_right _ _ (by rw [qp];omega),qp,
     show 2*k+2*r*k+2*k*m+q.val - k - k - r*k - r*k - k*m - k*m=q.val by omega,
     q9?_left _ _ (by rw [qd];exact q.isLt)]
   exact yk m y.val q.val q.isLt
  have ht:zv x=t:=by
   unfold zv;convert hpack_val_fin t using 1;congr 1;funext q
   simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qp];omega),qp,
     q9?_right _ _ (by rw [qp];omega),qp,
     q9?_right _ _ (by rw [qd];omega),qd,
     show 2*k+2*r*k+2*k*m+m+q.val - k - k - r*k - r*k - k*m - k*m - m=q.val by omega,
     q9?_left _ _ (by rw [qd];exact q.isLt)]
   exact yk (k+1) t.val q.val q.isLt
  have hj:zw x=⟨j.val,lt_trans j.isLt Nat.lt_two_pow_self⟩:=by
   unfold zw
   have hjv:j.val < 2^(k+1):=lt_trans j.isLt Nat.lt_two_pow_self
   convert hpack_val_fin (⟨j.val,hjv⟩:Fin (2^(k+1))) using 1;congr 1;funext q
   simp only [x,inp,List.append_assoc,List.getD]
   rw [q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qr];omega),qr,
     q9?_right _ _ (by rw [qp];omega),qp,
     q9?_right _ _ (by rw [qp];omega),qp,
     q9?_right _ _ (by rw [qd];omega),qd,
     q9?_right _ _ (by rw [qd];omega),qd,
     show 2*k+2*r*k+2*k*m+m+(k+1)+q.val - k - k - r*k - r*k - k*m - k*m - m - (k+1)=q.val by omega]
   exact yk (k+1) j.val q.val q.isLt
  have hev:C.eval inp=res.c'.val (List.ofFn x) res.val.w:=by rw [hofFn];rfl
  rw [hev,res.val.heval x]
  dsimp only
  rw [hnr,hnc,hcr,hcc,hA,hB,hy,ht,hj]
  set Ab:Fin k->Q1 m:=fun p q=>(A p).val.testBit q.val
  set Bb:Fin k->Q1 m:=fun p q=>(B p).val.testBit q.val
  set yb:Q1 m:=fun q=>y.val.testBit q.val
  set o:=qW hk r h Ab Bb
  obtain ⟨hall,hwidth,_,_⟩:=zG hk hh r Ab Bb
  rw [← hwidth]
  change (decide (qU r Ab Bb o ≤ b) &&
    (decide (t.val < qX b Ab Bb nr nc cr cc yb o (fun _=>false) (fun _=>false)) &&
    (decide (j.val=0)||decide (∃ s:Fin k,j.val=s.val+1/\jn b Ab Bb nr nc cr cc yb o t.val s=true)))) =
   decide (qU r Ab Bb o ≤ b/\∃ w:Fin (2^k),v4 k r m Ab Bb nr.val nc.val cr cc w.val=yb /\
    Nat.card {z:Fin (2^k) // z < w/\v4 k r m Ab Bb nr.val nc.val cr cc z.val=yb}=t.val /\
    (j.val=0\/w.val.testBit (j.val - 1)=true))
  by_cases hw:qU r Ab Bb o ≤ b
  ·simp only [hw,decide_true,Bool.true_and,true_and]
   have hunr:=db hk hr Ab Bb nr nc cr cc yb hall.1 hw t j
   dsimp only at hunr
   refine (congrArg (fun b1=>decide (t.val < qX b Ab Bb nr nc cr cc yb o (fun _=>false) (fun _=>false)) &&
     (decide (j.val=0)||b1)) ?_).trans hunr
   apply Bool.eq_iff_iff.mpr;simp only [dG]
   by_cases hj0:j.val=0
   ·simp [hj0]
   ·simp only [hj0,↓reduceDIte]
    constructor
    ·rintro ⟨s,hs,hbit⟩
     have heq:s=⟨j.val - 1,by omega⟩:=Fin.ext (by dsimp;omega)
     rwa [← heq]
    ·intro hbit;exact ⟨⟨j.val - 1,by omega⟩,by dsimp;omega,hbit⟩
  ·simp [hw]
end SelectCircuit
end PEqualNP.Outside.L_meta_33660

theorem PEqualNP.Outside.L_meta_33660 : (∀ (k r m b h : Nat), 0 < k → 4 ≤ r → b ≤ k+m → 0 < h → h ≤ k →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let O := Fin k → Fin k
  let V := Fin m → ZMod 2
  let W := Fin (2^k)
  let Y := Fin (2^m)
  let vec := fun (w : Nat) (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  let pack := fun (A : Fin k → Y) => (List.finRange k).flatMap (fun p => bits m (A p).val)
  ∃ Plan Select : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo Plan ∧ PEqualNP.MetaComplexity.FanInTwo Select ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k*m+2*k) Plan ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k+2*r*k+2*k*m+m+2*(k+1)) Select ∧
    Plan.size ≤ 2^48*(k+r+m+5)^(4*h+16) ∧
    Select.size ≤ 2^52*((k+r+m+5)^(4*h+20)+(k+r+m+5)^20*2^b) ∧
    ∀ (A B : Fin k → Y),
      let span := fun (ps : List (Fin k)) => Submodule.span (ZMod 2)
        (↑((ps.flatMap (fun p => [vec (A p).val, vec (B p).val])).toFinset) : Set V)
      let arc := fun (p : Fin k) (col : Bool) =>
        (Finset.univ : Finset (Fin k)).filter (fun z =>
          (if col then (B p).val else (A p).val) ≠ 0 ∧
          ∃ h : Fin (reach col + 1), (p.val+h.val)%k = z.val)
      let scope := fun p => arc p false ∪ arc p true
      let pool := fun (ps : List (Fin k)) => ps.toFinset.biUnion scope
      let allowed := fun (o : O) => Function.Bijective o ∧ ∀ u : Fin (k+1),
        let S := ((List.ofFn o).take u.val).toFinset
        ((Finset.univ : Finset (Fin k)).filter (fun j => j ∈ S ∧
          ∀ z ∈ S, (z.val+1)%k ≠ j.val)).card ≤ h
      let width := fun (o : O) => (Finset.univ : Finset (Fin k)).sup (fun i =>
        let L := (List.ofFn o).take i.val
        let R := (List.ofFn o).drop i.val
        ((pool L ∩ pool R) ∪ scope (o i)).card +
          Module.finrank (ZMod 2) (span L ⊓ span R : Submodule (ZMod 2) V))
      ∃ o : O, allowed o ∧ (∀ z : O, allowed z → width o ≤ width z) ∧
        (∀ z : O, allowed z → width z = width o → z = o ∨
          ∃ i : Fin k, o i < z i ∧ ∀ j : Fin k, j < i → o j = z j) ∧
        (∀ i j : Fin k,
          Plan.eval (pack A ++ pack B ++ bits k i.val ++ bits k j.val) = (o i).val.testBit j.val) ∧
        ∀ (nr nc : W) (cr cc : Fin r → W) (y : Y) (t : Fin (2^(k+1))) (j : Fin (k+1)),
        let report := fun (w : W) => (List.finRange k).foldl (fun z p =>
          let bit := fun col : Bool => (state col w.val (if col then nc.val else nr.val)
            (if col then cc else cr)).testBit ((p.val+delay col)%k)
          (z ^^^ (if bit false then (A p).val else 0)) ^^^
            (if bit true then (B p).val else 0)) (0 : Nat)
        let hit := fun w => report w = y.val
        Select.eval (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ pack A ++ pack B ++
          bits m y.val ++ bits (k+1) t.val ++ bits (k+1) j.val) =
          decide (width o ≤ b ∧ ∃ w : W, hit w ∧ Nat.card {z : W // z < w ∧ hit z} = t.val ∧
            (j.val = 0 ∨ w.val.testBit (j.val-1) = true))) := by
 intro k r m b h hk hr hb hh _
 intro O V W Y vec rot step state reach delay bits sched pack
 let PRes:=PEqualNP.Outside.L_meta_33660.gi k r m h hk hh
 let SRes:=PEqualNP.Outside.L_meta_33660.zW k r m b h hk hr hb hh
 refine ⟨PRes.1,SRes.1,PRes.2.1,SRes.2.1,PRes.2.2.1,SRes.2.2.1,PRes.2.2.2.1,SRes.2.2.2.1,?_⟩
 intro A B span arc scope pool allowed width
 set Ab:Fin k->PEqualNP.Outside.L_meta_33660.Q1 m:=fun p q=>(A p).val.testBit q.val
 set Bb:Fin k->PEqualNP.Outside.L_meta_33660.Q1 m:=fun p q=>(B p).val.testBit q.val
 have hvecA:∀ p:Fin k,vec (A p).val=PEqualNP.Outside.L_meta_33660.q4 (Ab p):=fun p=>by
  funext i;simp [vec,Ab,PEqualNP.Outside.L_meta_33660.q4]
 have hvecB:∀ p:Fin k,vec (B p).val=PEqualNP.Outside.L_meta_33660.q4 (Bb p):=fun p=>by
  funext i;simp [vec,Bb,PEqualNP.Outside.L_meta_33660.q4]
 have hspan:∀ ps:List (Fin k),span ps=PEqualNP.Outside.L_meta_33660.qw Ab Bb ps.toFinset:=by
  intro ps;dsimp only [span];unfold PEqualNP.Outside.L_meta_33660.qw;congr 1;ext v
  simp only [Finset.mem_coe,List.mem_toFinset,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false,
   hvecA,hvecB]
  constructor <;> rintro ⟨p,hp,hv⟩ <;> exact ⟨p,by simpa using hp,hv⟩
 have hnz:∀ v:Fin (2^m),v.val ≠ 0 ↔ PEqualNP.Outside.L_meta_33660.qK (fun q:Fin m=>v.val.testBit q.val)=true:=by
  intro v
  rw [PEqualNP.Outside.L_meta_33660.qv,decide_eq_true_eq]
  constructor
  ·intro hne
   by_contra hall;push Not at hall
   apply hne;apply Nat.eq_of_testBit_eq;intro q
   by_cases hq:q < m
   ·rw [Nat.zero_testBit];exact Bool.eq_false_iff.mpr (hall ⟨q,hq⟩)
   ·rw [Nat.testBit_lt_two_pow (v.isLt.trans_le (Nat.pow_le_pow_right (by omega) (not_lt.mp hq))),Nat.zero_testBit]
  ·rintro ⟨q,hq⟩ hv;rw [hv,Nat.zero_testBit] at hq;exact Bool.false_ne_true hq
 have hreach:∀ col:Bool,reach col=PEqualNP.Outside.L_meta_33660.yy r col:=fun col=>by
  cases col <;> simp [reach,PEqualNP.Outside.L_meta_33660.yy]
 have harc:∀ (p:Fin k) (col:Bool),arc p col=PEqualNP.Outside.L_meta_33660.d3 r Ab Bb p col:=by
  intro p col;ext z
  simp only [arc,PEqualNP.Outside.L_meta_33660.d3,Finset.mem_filter,Finset.mem_univ,true_and,
   PEqualNP.Outside.L_meta_33660.y4,decide_eq_true_eq]
  cases col
  ·simp only [Bool.false_eq_true,↓reduceIte,hnz (A p)]
   exact and_congr Iff.rfl ⟨fun ⟨t,ht⟩=>⟨⟨t.val,by rw [← hreach];exact t.isLt⟩,ht⟩,
    fun ⟨t,ht⟩=>⟨⟨t.val,by rw [hreach];exact t.isLt⟩,ht⟩⟩
  ·simp only [↓reduceIte,hnz (B p)]
   exact and_congr Iff.rfl ⟨fun ⟨t,ht⟩=>⟨⟨t.val,by rw [← hreach];exact t.isLt⟩,ht⟩,
    fun ⟨t,ht⟩=>⟨⟨t.val,by rw [hreach];exact t.isLt⟩,ht⟩⟩
 have hscope:∀ p:Fin k,scope p=PEqualNP.Outside.L_meta_33660.qq r Ab Bb p:=fun p=>by
  ext z;simp [scope,PEqualNP.Outside.L_meta_33660.qq,harc]
 have hpool:∀ ps:List (Fin k),pool ps=PEqualNP.Outside.L_meta_33660.qi r Ab Bb ps.toFinset:=fun ps=>by
  ext z;simp [pool,PEqualNP.Outside.L_meta_33660.qi,hscope]
 have hallowed:∀ z:O,allowed z ↔ PEqualNP.Outside.L_meta_33660.jO h z:=by
  intro z;dsimp only [allowed];unfold PEqualNP.Outside.L_meta_33660.jO PEqualNP.Outside.L_meta_33660.vi
  refine and_congr_right fun _=>forall_congr' fun u=>?_
  apply Iff.of_eq;congr 1;congr 1;ext j;simp
 have hwidth:∀ z:O,width z=PEqualNP.Outside.L_meta_33660.qU r Ab Bb z:=by
  intro z;dsimp only [width];unfold PEqualNP.Outside.L_meta_33660.qU
  refine Finset.sup_congr rfl fun i _=>?_
  dsimp only;congr 1
  ·congr 1;ext q;simp [hpool,hscope]
  ·rw [hspan,hspan]
 set o:=PEqualNP.Outside.L_meta_33660.qW hk r h Ab Bb
 obtain ⟨ho_all,_,ho_min,ho_lex⟩:=PEqualNP.Outside.L_meta_33660.zG hk hh r Ab Bb
 refine ⟨o,(hallowed o).mpr ho_all,fun z hz=>by rw [hwidth o,hwidth z];exact ho_min z ((hallowed z).mp hz),
  fun z hz hweq=>ho_lex z ((hallowed z).mp hz) (by rwa [← hwidth z,← hwidth o]),
  fun i j=>PRes.2.2.2.2 A B i j,?_⟩
 intro nr nc cr cc y t j report hit
 have hsel:=SRes.2.2.2.2 A B nr nc cr cc y t j
 dsimp only at hsel
 rw [hsel,hwidth o]
 apply Bool.eq_iff_iff.mpr;simp only [decide_eq_true_eq]
 have hdelay:∀ col:Bool,delay col=PEqualNP.Outside.L_meta_33660.vo r col:=fun col=>by
  cases col <;> simp [delay,PEqualNP.Outside.L_meta_33660.vo]
 have hstate:∀ col w name c,state col w name c=PEqualNP.Outside.L_meta_33660.vI k r col w name c:=fun col w name c=>by
  cases col <;> simp [state,rot,step,PEqualNP.Outside.L_meta_33660.vI,PEqualNP.Outside.L_meta_33660.jf,PEqualNP.Outside.L_meta_33660.yV]
 have hhit_iff:∀ w:W,
   (PEqualNP.Outside.L_meta_33660.v4 k r m Ab Bb nr.val nc.val cr cc w.val=fun q=>y.val.testBit q.val) ↔ hit w:=fun w=>by
  refine (PEqualNP.Outside.L_meta_33660.yx A B nr nc cr cc y w).symm.trans (Iff.of_eq ?_)
  dsimp only [hit,report]
  congr 1;apply congrArg (fun f=>List.foldl f 0 (List.finRange k))
  funext z p
  simp only [Bool.false_eq_true,↓reduceIte,hstate,hdelay]
 refine and_congr_right fun _=>exists_congr fun w=>?_
 refine and_congr (hhit_iff w) (and_congr_left fun _=>?_)
 have hsub:{z:W // z < w/\PEqualNP.Outside.L_meta_33660.v4 k r m Ab Bb nr.val nc.val cr cc z.val=fun q=>y.val.testBit q.val} ≃
   {z:W // z < w/\hit z}:=
  Equiv.subtypeEquivRight fun z=>and_congr_right fun _=>hhit_iff z
 rw [Nat.card_congr hsub]
