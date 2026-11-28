import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30172

namespace Windmill

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity




lemma bFT:(false=true)=False:=Bool.false_eq_true

lemma bTA {b:Bool}:(true&&b)=b:=Bool.true_and b

lemma bOT {a b:Bool}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b

lemma bAT {a b:Bool}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b

lemma bNF:(!false)=true:=Bool.not_false

lemma bNT {b:Bool}:((!b)=true)=(b=false):=Bool.not_eq_true' b

lemma lAA {α:Type _} (l1 l2 l3:List α):(l1++l2)++l3=l1++(l2++l3):=List.append_assoc l1 l2 l3

lemma lMC {α β:Type _} {f : α->β} {a : α} {l:List α}:(a::l).map f=f a::l.map f:=List.map_cons

lemma lMM {α:Type _} {a b : α} {l:List α}:a ∈ b::l ↔ a=b\/a ∈ l:=List.mem_cons

lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons

lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append

lemma lRC {α:Type _} {a : α} {l:List α}:(a::l).reverse=l.reverse++[a]:=List.reverse_cons

lemma lFC {α β:Type _} {f : α->β->β} {b : β} {a : α} {l:List α}:(a::l).foldr f b=f a (l.foldr f b):=List.foldr_cons

lemma lAL {α:Type _} {p : α->Bool} {l:List α}:l.all p=true ↔ ∀ x ∈ l,p x=true:=List.all_eq_true

lemma lAN {α:Type _} {p : α->Bool} {l:List α}:l.any p=true ↔ ∃ x ∈ l,p x=true:=List.any_eq_true

lemma nTB {n i:Nat}:(2 ^ n - 1).testBit i=decide (i < n):=by simp [Nat.testBit_two_pow_sub_one]

lemma nEQ {x y:Nat} (h:∀ i,x.testBit i=y.testBit i):x=y:=Nat.eq_of_testBit_eq h

lemma nTO {x y i:Nat}:(x|||y).testBit i=(x.testBit i||y.testBit i):=by simp [Nat.testBit_or]

lemma nTA {x y i:Nat}:(x&&&y).testBit i=(x.testBit i&&y.testBit i):=by simp [Nat.testBit_and]

lemma nTX {x y i:Nat}:(x^^^y).testBit i=(x.testBit i ^^ y.testBit i):=by simp [Nat.testBit_xor]

lemma nTS {x k i:Nat}:(x >>> k).testBit i=x.testBit (k+i):=by simp [Nat.testBit_shiftRight]

lemma nLO {x y:Nat}:Nat.lor x y=x|||y:=Nat.lor_eq

lemma nLA {x y:Nat}:Nat.land x y=x&&&y:=Nat.land_eq

lemma nXO {x y:Nat}:Nat.xor x y=x^^^y:=Nat.xor_eq

lemma nZT {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i

lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f

lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f

lemma lMA {α β:Type _} {f : α->β} {l1 l2:List α}:(l1++l2).map f=l1.map f++l2.map f:=List.map_append

lemma lLM {α β:Type _} (f : α->β) {l:List α}:(l.map f).length=l.length:=List.length_map f

lemma lRR {α:Type _} {l:List α}:l.reverse.reverse=l:=List.reverse_reverse l

lemma lANil {α:Type _} {l:List α}:l++[]=l:=List.append_nil l

lemma lCA {α:Type _} {a : α} {l1 l2:List α}:(a::l1)++l2=a::(l1++l2):=List.cons_append

lemma lPM {α:Type _} {a : α} {l₁ l₂:List α}:(l₁++a::l₂).Perm (a::(l₁++l₂)):=List.perm_middle

lemma nAC (a b:Nat):a+b=b+a:=Nat.add_comm a b

lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d

lemma nAZ {a:Nat}:a+0=a:=Nat.add_zero a

lemma nZL (a:Nat) : 0<=a:=Nat.zero_le a

lemma bOS {a:Bool}:(a||a)=a:=Bool.or_self a

lemma bOTR {a:Bool}:(a||true)=true:=Bool.or_true a

lemma bTOR {a:Bool}:(true||a)=true:=Bool.true_or a

lemma bATR {a:Bool}:(a&&true)=a:=Bool.and_true a

lemma bBT {a:Bool}:(a ^^ true)=!a:=Bool.bne_true a

lemma n2P (n:Nat) : 0 < 2 ^ n:=Nat.two_pow_pos n

lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map

lemma fCD {α β γ:Type _} (f : β->γ) (g : α->β):f ∘ g=fun x => f (g x):=Function.comp_def f g

lemma lPR {α:Type _} (l:List α):l.Perm l:=List.Perm.refl l

lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h

lemma lPC {α:Type _} (x : α) {l1 l2:List α} (h:l1.Perm l2):(x::l1).Perm (x::l2):=List.Perm.cons x h

abbrev BFn (n : ℕ):=(Fin n->Bool)->Bool

def q3 (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma zd (gs gs':List Gate) (w:List Bool) :
   q3 (gs++gs') w=q3 gs' (q3 gs w):=by
 simp [q3,List.foldl_append]

lemma y1 (gs:List Gate):∀ w:List Bool,
   ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   have:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht];simp

lemma qu (gs:List Gate) (w:List Bool) :
   (q3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=y1 gs w
 rw [ht];simp [hl]

lemma ve (gs:List Gate) (w:List Bool) (i : ℕ) (h:i < w.length) :
   (q3 gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=y1 gs w
 rw [ht,List.getD_append _ _ _ _ h]

def Ok (g:Gate):Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2

lemma q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
   (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 . exact List.getD_append _ _ _ _ hj
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]

lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
 simp

lemma z2 {α:Type} (L:List α) (S d : α) (k : ℕ) (h:L.length=k) :
   (L++[S]).getD k d=S:=by
 subst h;simp

def yb {n : ℕ} (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
 (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma q71 {n : ℕ} (l:List ℕ) (F : ℕ->Finset (Fin n)) (i:Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]

lemma kf {n : ℕ} (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
   i ∈ yb L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 q71 _ _ _

def zb {n : ℕ} (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
 gs.foldl (fun L g => L++[yb L g]) L

def qr (n : ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n => {i}

def q207 {n : ℕ} (x y:Fin n->Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
 L.length=w.length/\w.length=w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false

lemma k6 {n : ℕ} (x y:Fin n->Bool) (gs:List Gate) :
   ∀ (L:List (Finset (Fin n))) (w w':List Bool),q207 x y L w w' ->
     q207 x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil => intro L w w' h;exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[yb L g])
     (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w'++[g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0] at hj
     rw [h1,z0,h2,z0]
     congr 1
     apply List.map_congr_left
     intro a ha
     exact h3 a (fun i hi => hj i ((kf L g i).2 ⟨a,ha,hi⟩))
   . rw [q8 _ _ _ _ hjl] at hj
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact h3 j hj

lemma j4 {n : ℕ} (x y:Fin n->Bool) :
   q207 x y (qr n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 . have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [qr,hjn])
   simp [hjn,hx]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]

def Cnt {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))):Prop :=
 ∀ W:Finset ℕ,(W.biUnion fun j => L.getD j ∅).card<=t+W.card

lemma q166 {n : ℕ}:Cnt 0 (qr n):=by
 intro W
 refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _
 by_cases hjn:j < n
 . simp [qr,hjn]
 . rw [lGD _ _ (by simp [qr];omega)];simp

lemma q194 {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))) (g:Gate) (hg:g.inputs.length<=2)
   (h:Cnt t L):Cnt (t+1) (L++[yb L g]):=by
 intro W
 by_cases hW:L.length ∈ W
 . have hsub:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅):=by
     intro i hi
     rw [Finset.mem_biUnion] at hi ⊢
     obtain ⟨j,hjW,hij⟩:=hi
     by_cases hjl:j=L.length
     . subst hjl
       rw [z0] at hij
       obtain ⟨a,ha,hia⟩:=(kf L g i).1 hij
       exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
     . rw [q8 _ _ _ _ hjl] at hij
       exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
   have hc1:(W.erase L.length ∪ g.inputs.toFinset).card<=(W.card - 1)+2:=by
     refine le_trans (Finset.card_union_le _ _) ?_
     rw [Finset.card_erase_of_mem hW]
     exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
   have hWpos : 1<=W.card:=Finset.card_pos.2 ⟨_,hW⟩
   have:=h (W.erase L.length ∪ g.inputs.toFinset)
   have:=Finset.card_le_card hsub
   omega
 . have heq:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       = (W.biUnion fun j => L.getD j ∅):=by
     apply Finset.biUnion_congr rfl
     intro j hj
     exact q8 _ _ _ _ (fun e => hW (e ▸ hj))
   rw [heq]
   have:=h W
   omega

lemma q118 {n : ℕ} (gs:List Gate):∀ (t : ℕ) (L:List (Finset (Fin n))),
   (∀ g ∈ gs,Ok g)->Cnt t L->Cnt (t+gs.length) (zb gs L):=by
 induction gs with
 | nil => intro t L _ h;exact h
 | cons g gs ih =>
   intro t L hok h
   have:=ih (t+1) (L++[yb L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
     (q194 t L g (hok g List.mem_cons_self).2 h)
   rw [lLC,show t+(gs.length+1)=t+1+gs.length by omega]
   exact this

lemma q117 (n : ℕ) (f:(Fin n->Bool)->Bool) (T:Finset (Fin n))
   (hdep:∀ i ∈ T,∃ x:Fin n->Bool,f (Function.update x i (!x i))≠f x)
   (s : ℕ) (h:HasCircuitSize n f s):T.card<=s+1:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set S:=(zb C.gates (qr n)).getD C.output ∅ with hS
 have hall:T ⊆ S:=by
   intro i hiT
   by_contra hi
   obtain ⟨x,hx⟩:=hdep i hiT
   apply hx
   have hag:=(k6 (Function.update x i (!x i)) x C.gates _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠i:=fun e => hi (e ▸ hk)
       simp [fUN this])
   rw [← hev,← hev]
   exact hag
 have hc:=q118 C.gates 0 (qr n) ok q166 {C.output}
 simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc
 rw [← hS] at hc
 have:=Finset.card_le_card hall
 omega

def vg (g:Gate):Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g

lemma q107 (g:Gate) (F : ℕ->Bool) :
   (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g
 cases op <;> simp only [vg]
 cases inputs <;> simp [GateOp.eval]

def NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)

lemma q45 (g:Gate) (h:Ok g):NOk (vg g):=by
 obtain ⟨op,inputs⟩:=g
 obtain ⟨hop,hlen⟩:=h
 rcases hop with h | h | h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg] <;> omega

lemma jd (gs:List Gate):∀ w:List Bool,
   q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil => intro w;rfl
 | cons g gs ih =>
   intro w
   have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
       (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
   have s2:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [s1,s2,q107,ih]

abbrev Stat:=Sum Bool ℕ

def ze (w:List Bool):Stat->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false

def qn (m : ℕ):Stat->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m

def wr (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | Sum.inl c::_ => (none,Sum.inl (!c))
 | Sum.inr j::_ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)

def ko (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)

def ji (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)

def qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
 match op with
 | GateOp.and => ko m ins
 | GateOp.or => ji m ins
 | GateOp.not => wr m ins
 | _ => (none,Sum.inl false)

def q161 (m : ℕ) (g:Gate):Prop :=
 (g.op=GateOp.not/\∃ j,j < m/\g.inputs=[j]) \/
 ((g.op=GateOp.and\/g.op=GateOp.or)/\∃ j k,j < m/\k < m/\g.inputs=[j,k])

lemma j2 {m : ℕ} {g:Gate} (h:q161 m g):∀ a ∈ g.inputs,a < m:=by
 rcases h with ⟨_,j,hj,hin⟩ | ⟨_,j,k,hj,hk,hin⟩
 . intro a ha;simp [hin] at ha;omega
 . intro a ha;simp [hin] at ha;rcases ha with rfl | rfl <;> omega

def yq (n : ℕ) (gs:List Gate):Prop :=
 ∀ p g,gs[p]?=some g->q161 (n+p) g

lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp [wr] at hg <;> (subst hg;simp [Ok])
 . simp at hg
 . simp at hg

lemma q80 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hv:∀ s ∈ ins,qn m s) :
   ∀ g ∈ (qg op m ins).1,q161 m g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg
   subst hg
   exact Or.inr ⟨Or.inl rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg
   subst hg
   exact Or.inr ⟨Or.inr rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [wr] at hg
   subst hg
   exact Or.inl ⟨rfl,_,hv (Sum.inr _) (by simp),rfl⟩
 . simp at hg
 . simp at hg

lemma jh (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
   (qg op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ko]
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]

lemma kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
   (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
   (hv:∀ s ∈ ins,qn w.length s) :
   qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
   ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
     = op.eval (ins.map (ze w)):=by
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,wr,qn,ze,GateOp.eval,q3]

def qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
 (acc.1++[(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2++(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
 gs.foldl (qa n) acc

lemma k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
   elim n (g::gs) acc=elim n gs (qa n acc g):=rfl

lemma jz (n : ℕ) (pre post:List Gate) (acc:List Stat × List Gate) :
   elim n (pre++post) acc=elim n post (elim n pre acc):=by
 simp [elim,List.foldl_append]

lemma q50 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
   intro acc
   rw [k4,ih]
   simp only [qa,lLA,lLC,List.length_nil]
   omega

lemma wy (n k : ℕ) (d:Stat) (gs:List Gate):∀ acc:List Stat × List Gate,
   k < acc.1.length->(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
   intro acc hk
   rw [k4,ih (qa n acc g) (by simp [qa];omega)]
   exact q8 _ _ _ _ (by omega)

lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by
 cases o <;> simp

lemma q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil => intro acc h;exact h
 | cons g gs ih =>
   intro acc h
   apply ih (qa n acc g)
   intro g' hg'
   rcases List.mem_append.1 hg' with h1 | h1
   . exact h g' h1
   . exact q151 _ _ _ g' (by simpa using h1)

lemma q29 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).2.length<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (qa n acc g)
   have h2:(qa n acc g).2.length<=acc.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   rw [k4,lLC];omega

lemma zt (n k : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->k < acc.1.length->(∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) ->
   (∃ g ∈ gs,k ∈ g.inputs)->(elim n gs acc).2.length+1<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
   intro acc hok hk hc hex
   rw [k4,lLC]
   by_cases hkg:k ∈ g.inputs
   . obtain ⟨c,hc⟩:=hc
     have hnok:=hok g List.mem_cons_self
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hnok.1.1
       . simpa using hnok.1.2
       . intro h;simpa using hnok.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
     have h2:(qa n acc g).2.length=acc.2.length:=by
       show (acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
       rw [hnone];simp
     have:=q29 n gs (qa n acc g)
     omega
   . have hex':∃ g' ∈ gs,k ∈ g'.inputs:=by
       obtain ⟨g',hg',hk'⟩:=hex
       rcases List.mem_cons.1 hg' with rfl | h
       . exact absurd hk' hkg
       . exact ⟨g',h,hk'⟩
     have h1:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       (by simp [qa];omega)
       (by
         obtain ⟨c,hc⟩:=hc
         refine ⟨c,?_⟩
         simp only [qa]
         rw [q8 _ _ _ _ (by omega)];exact hc)
       hex'
     have h2:(qa n acc g).2.length<=acc.2.length+1:=by
       simp only [qa,lLA]
       have:=y2 (qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
       omega
     omega

lemma km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h

lemma jg (w t:List Bool):∀ s:Stat,qn w.length s ->
   ze (w++t) s=ze w s
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length/\∀ i : ℕ,
   qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
   ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false

lemma j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=q3 acc.2 y with hw'
   have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw'];exact (hi a).1)
   rw [lw'] at hs
   set r:=qg g.op (n+acc.2.length) ins with hr
   have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,lMMp]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
     rw [zd]
   obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
   refine ⟨by simp [qa,hl],?_⟩
   intro i
   show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
     ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
   rw [hnew,lLA,← nAA]
   by_cases hil:i=acc.1.length
   . subst hil
     rw [z0,hl,z0]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
     refine ⟨km (by omega) _ (hi i).1,?_⟩
     rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
     exact (hi i).2

lemma q100 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,Ok g)->(∀ i,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) ->
   yq n acc.2->yq n (elim n gs acc).2:=by
 induction gs with
 | nil => intro acc _ _ hc;exact hc
 | cons g gs ih =>
   intro acc hok hv hc
   have hstep:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   apply hstep
   . intro i
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 (List.replicate (n+acc.2.length) false) ins
       (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         simpa using hv a)
     simp only [List.length_replicate] at hs
     show qn (n+(acc.2++_).length) ((acc.1++[_]).getD i (Sum.inl false))
     rw [lLA,← nAA]
     by_cases hil:i=acc.1.length
     . subst hil;rw [z0];exact hs.1
     . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
   . intro p g' hp
     simp only [qa] at hp
     by_cases hlt:p < acc.2.length
     . rw [List.getElem?_append_left hlt] at hp
       exact hc p g' hp
     . rw [List.getElem?_append_right (by omega)] at hp
       set r:=qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
       cases ho:r.1 with
       | none => simp [ho] at hp
       | some g0 =>
         rw [ho] at hp
         have hp0:p - acc.2.length=0:=by
           have:=(List.getElem?_eq_some_iff.1 hp).1
           simp at this;omega
         have hpeq:p=acc.2.length:=by omega
         rw [hp0] at hp
         simp at hp
         subst hp
         rw [hpeq]
         exact q80 g.op (n+acc.2.length) _ (by
           intro s hs
           obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
           exact hv a) g0 (by rw [← hr,ho];rfl)

def qd (n : ℕ) (b:Bool):List Stat :=
 List.ofFn (fun i:Fin n => Sum.inr (i : ℕ))++[Sum.inl b]

lemma kp (n : ℕ) (b:Bool) :
   (qd n b).getD n (Sum.inl false)=Sum.inl b :=
 z2 _ _ _ _ (by simp)

lemma q159 (n : ℕ) (b:Bool) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i
 have l1:(List.ofFn (fun i:Fin n => (Sum.inr (i : ℕ):Stat))).length=n:=by simp
 have l2:(List.ofFn y).length=n:=by simp
 by_cases hin:i=n
 . subst hin
   simp only [qd]
   rw [z2 _ _ _ _ l1,z2 _ _ _ _ l2]
   exact ⟨trivial,rfl⟩
 . simp only [qd]
   rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases hlt:i < n
   . simp [hlt,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
     exact ⟨trivial,rfl⟩

lemma q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
   List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
 rw [List.ofFn_succ']
 simp

lemma jr (n : ℕ) (gs:List Gate):∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,n ∉ g.inputs)->(∀ j : ℕ,j≠n->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj

lemma q74 (m j : ℕ) (h:j < m) :
   (qr m).getD j ∅={⟨j,h⟩}:=by
 simp [qr,h]

lemma yi (n : ℕ):∀ j : ℕ,j≠n ->
   Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j hj
 by_cases hlt:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,hlt⟩}:=q74 (n+1) j hlt
   rw [e,Finset.mem_singleton]
   intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp

lemma q115 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s',s'+1<=s/\HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 set acc:=elim n gs (qd n b,[]) with hacc
 have hinv:∀ y:Fin n->Bool,
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool))) acc:=by
   intro y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ y:Fin n->Bool,
     ze (q3 acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
       = f (Fin.snoc y b):=by
   intro y
   rw [((hinv y).2 C.output).2,hevg]
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst];rfl
 | inr j =>
   have hlen:acc.2.length+1<=s:=by
     by_cases hread:∃ g ∈ gs,n ∈ g.inputs
     . have:=zt n n gs (qd n b,[]) hnok (by simp [qd])
         ⟨b,z2 _ _ _ _ (by simp)⟩ hread
       rw [← hacc] at this
       have hl:gs.length=C.gates.length:=by simp [hgs]
       simp only [List.length_nil,zero_add] at this
       omega
     . exfalso
       push Not at hread
       have hout:C.output≠n:=by
         intro e
         rw [e,hacc,wy n n _ gs _ (by simp [qd])] at hst
         have hb:(qd n b).getD n (Sum.inl false)=Sum.inl b :=
           z2 _ _ _ _ (by simp)
         rw [show ((qd n b,([]:List Gate))).1=qd n b from rfl,hb] at hst
         cases hst
       obtain ⟨x,hx⟩:=hdep
       apply hx
       have hns:=jr n gs (qr (n+1)) hread (yi n) C.output hout
       have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
         (j4 _ _)).2.2 C.output (by
           intro k hk
           have:k≠Fin.last n:=fun e => hns (e ▸ hk)
           simp [fUN this])
       rw [← hevg,← hevg]
       exact hag
   refine ⟨acc.2.length,hlen,⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval y
   rw [hst] at this
   exact this

lemma q79 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (b:Bool)
   (hand:op=GateOp.and->b=false) (hor:op=GateOp.or->b=true)
   (hc:Sum.inl b ∈ ins):∃ c,(qg op m ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 . have:=hand rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ko]
 . have:=hor rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]

lemma vs (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (c:Bool) (hc:acc.1.getD k (Sum.inl false)=Sum.inl c) :
   (qa n acc g).2.length=acc.2.length:=by
 have hnone:(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
   apply jh
   . exact hg.1.1
   . simpa using hg.1.2
   . intro h;simpa using hg.2 h
   . exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
 show (acc.2++(qg g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
 rw [hnone];simp

def wl (g:Gate):Bool :=
 match g.op with
 | GateOp.or => true
 | _ => false

lemma q90 (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (hc:acc.1.getD k (Sum.inl false)=Sum.inl (wl g)) :
   ∃ c,(qa n acc g).1.getD acc.1.length (Sum.inl false)=Sum.inl c:=by
 have e:(qa n acc g).1.getD acc.1.length (Sum.inl false)
     = (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2:=z0 _ _ _
 rw [e]
 apply q79 _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
   (wl g)
 . intro h;simp [wl,h]
 . intro h;simp [wl,h]
 . exact List.mem_map.2 ⟨k,hk,hc⟩

lemma q53 {n : ℕ} (pre post:List Gate) (L:List (Finset (Fin n))) :
   zb (pre++post) L=zb post (zb pre L):=by
 simp [zb,List.foldl_append]

lemma q54 {n : ℕ} (gs:List Gate):∀ L:List (Finset (Fin n)),
   (zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil => intro L;rfl
 | cons g gs ih =>
   intro L
   have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl
   rw [h,ih]
   simp only [lLA,lLC,List.length_nil]
   omega

lemma q124 (n : ℕ) (D : ℕ->Prop) (gs:List Gate) :
   ∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,∀ a ∈ g.inputs,¬ D a)->(∀ j : ℕ,¬ D j->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,¬ D j->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (hno g List.mem_cons_self a ha) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj

lemma q173 (n : ℕ) (gs:List Gate) (hnok:∀ g ∈ gs,NOk g) (o : ℕ)
   (hdep:Fin.last n ∈ (zb gs (qr (n+1))).getD o ∅)
   (hout:∀ b c,(elim n gs (qd n b,[])).1.getD o (Sum.inl false)≠Sum.inl c) :
   ∃ b,(elim n gs (qd n b,[])).2.length+2<=gs.length:=by
 have hon:o≠n:=by
   intro e
   apply hout false false
   rw [e,wy n n _ gs _ (by simp [qd])]
   exact kp n false
 by_cases hread:∃ g ∈ gs,n ∈ g.inputs
 swap
 . exfalso
   push Not at hread
   exact jr n gs (qr (n+1)) hread (yi n) o hon hdep
 obtain ⟨g,hg,hng⟩:=hread
 obtain ⟨pre,post,rfl⟩:=List.append_of_mem hg
 have hgn:NOk g:=hnok g hg
 have hpren:∀ g' ∈ pre,NOk g':=fun g' h => hnok g' (List.mem_append_left _ h)
 have hpostn:∀ g' ∈ post,NOk g' :=
   fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have hsplit:∀ b,elim n (pre++g::post) (qd n b,[])
     = elim n post (qa n (elim n pre (qd n b,[])) g) :=
   fun b => by rw [jz,k4]
 have hAn:∀ b,(elim n pre (qd n b,[])).1.getD n (Sum.inl false)=Sum.inl b:=by
   intro b
   rw [wy n n _ pre _ (by simp [qd])]
   exact kp n b
 have hAl:∀ b,(elim n pre (qd n b,[])).1.length=n+1+pre.length:=by
   intro b
   rw [q50]
   simp [qd]
 have hA2:∀ b,(elim n pre (qd n b,[])).2.length<=0+pre.length :=
   fun b => q29 n pre (qd n b,[])
 have hB2:=fun b => vs n (elim n pre (qd n b,[])) g hgn n hng b (hAn b)
 have hBl:∀ b,(qa n (elim n pre (qd n b,[])) g).1.length
     = n+1+pre.length+1:=by
   intro b
   simp [qa,hAl b]
 have hBn:∀ b,(qa n (elim n pre (qd n b,[])) g).1.getD n (Sum.inl false)
     = Sum.inl b:=by
   intro b
   show ((elim n pre (qd n b,[])).1++[_]).getD n _=_
   rw [q8 _ _ _ _ (by rw [hAl b];omega)]
   exact hAn b
 have hF:=fun b => q29 n post (qa n (elim n pre (qd n b,[])) g)
 have hlen:(pre++g::post).length=pre.length+post.length+1:=by
   simp only [lLA,lLC];omega
 by_cases h1:∃ g' ∈ pre,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:(elim n pre (qd n false,[])).2.length+1<=0+pre.length :=
     zt n n pre (qd n false,[]) hpren (by simp [qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 by_cases h2:∃ g' ∈ post,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:=zt n n post (qa n (elim n pre (qd n false,[])) g) hpostn
     (by rw [hBl];omega) ⟨false,hBn false⟩ h2
   have:=hA2 false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 obtain ⟨c,hc⟩:=q90 n (elim n pre (qd n (wl g),[])) g hgn n hng
   (hAn (wl g))
 rw [hAl (wl g)] at hc
 refine ⟨wl g,?_⟩
 by_cases h3:∃ g' ∈ post,(n+1+pre.length) ∈ g'.inputs
 . have a1:=zt n (n+1+pre.length) post
     (qa n (elim n pre (qd n (wl g),[])) g) hpostn
     (by rw [hBl];omega) ⟨c,hc⟩ h3
   have:=hA2 (wl g)
   have:=hB2 (wl g)
   rw [hsplit,hlen]
   omega
 . exfalso
   have hom:o≠n+1+pre.length:=by
     intro e
     apply hout (wl g) c
     rw [hsplit,e,wy n _ _ post _ (by rw [hBl];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (pre++g::post) (qr (n+1))
       = zb post (zb pre (qr (n+1))
         ++ [yb (zb pre (qr (n+1))) g]):=by
     rw [q53];rfl
   rw [hs] at hdep
   have hL:=jr n pre (qr (n+1)) h1 (yi n)
   have hLl:(zb pre (qr (n+1))).length=n+1+pre.length:=by
     rw [q54]
     simp [qr]
   refine q124 n (fun j => j=n\/j=n+1+pre.length) post _ ?_ ?_ o
     (by simp [hon,hom]) hdep
   . intro g' hg' a ha hD
     rcases hD with rfl | rfl
     . exact h2 g' hg' ha
     . exact h3 g' hg' ha
   . intro j hj
     have hj':j≠n/\j≠n+1+pre.length:=by
       constructor
       . exact fun e => hj (Or.inl e)
       . exact fun e => hj (Or.inr e)
     rw [q8 _ _ _ _ (by rw [hLl];exact hj'.2)]
     exact hL j hj'.1

lemma q114 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∀ b:Bool,∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hl:gs.length=C.gates.length:=by simp [hgs]
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 have hinv:∀ (b:Bool) (y:Fin n->Bool),
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)))
       (elim n gs (qd n b,[])):=by
   intro b y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ (b:Bool) (y:Fin n->Bool),
     ze (q3 (elim n gs (qd n b,[])).2 (List.ofFn y))
       ((elim n gs (qd n b,[])).1.getD C.output (Sum.inl false))=f (Fin.snoc y b):=by
   intro b y
   rw [((hinv b y).2 C.output).2,hevg]
 have hout:∀ b c,
     (elim n gs (qd n b,[])).1.getD C.output (Sum.inl false)≠Sum.inl c:=by
   intro b c hst
   obtain ⟨y,y',hne⟩:=hnc b
   apply hne
   rw [← hval b y,← hval b y',hst];rfl
 have hsupp:Fin.last n ∈ (zb gs (qr (n+1))).getD C.output ∅:=by
   by_contra hns
   obtain ⟨x,hx⟩:=hdep
   apply hx
   have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠Fin.last n:=fun e => hns (e ▸ hk)
       simp [fUN this])
   rw [← hevg,← hevg]
   exact hag
 obtain ⟨b,hb⟩:=q173 n gs hnok C.output hsupp hout
 cases hst:(elim n gs (qd n b,[])).1.getD C.output (Sum.inl false) with
 | inl c => exact absurd hst (hout b c)
 | inr j =>
   refine ⟨b,(elim n gs (qd n b,[])).2.length,by omega,
     ⟨(elim n gs (qd n b,[])).2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval b y
   rw [hst] at this
   exact this

def wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
 if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m

def jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩

def q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
 ⟨C.gates.map (jt n m π),wmap n m π C.output⟩

def step (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
 n<=W.length/\W'.length+n=W.length+m /\
   ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false

lemma q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
   (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv:(jt n m π g).op.eval
     ((jt n m π g).inputs.map fun i => W'.getD i false)
     = g.op.eval (g.inputs.map fun i => W.getD i false):=by
   simp only [jt,lMMp]
   congr 1
   apply List.map_congr_left
   intro a _
   exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w
 simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 . have hlt:wmap n m π w < W'.length:=by
     unfold wmap
     split
     . have:=(π ⟨w,by assumption⟩).2;omega
     . omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
   exact h3 w
 . have he:wmap n m π w=W'.length:=by
     unfold wmap
     split
     . omega
     . omega
   rw [he,hw,z0,z0]
 . have hge:W'.length+1<=wmap n m π w:=by
     unfold wmap
     split
     . omega
     . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]

lemma q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
   ∀ W W':List Bool,Rel n m π W W' ->
     Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   exact ih _ _ (q182 n m π W W' g h)

lemma q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
   Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w
 unfold wmap
 split
 . rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 . rename_i hw
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]

lemma yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
   (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨q174 n m π C,?_,?_,?_⟩
 . intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
 . simpa [q174,Circuit.size] using hsz
 . intro x
   show _=h (x ∘ π)
   rw [← hev (x ∘ π)]
   have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
   exact this

lemma ks (n : ℕ) (p:Fin (n+1)) (x:Fin (n+1)->Bool) (b:Bool) :
   (Fin.snoc (fun j:Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
       Fin (n+1)->Bool) ∘ (Equiv.swap p (Fin.last n))
     = Function.update x p b:=by
 funext j
 simp only [Function.comp_apply]
 by_cases hj:j=p
 . subst hj
   rw [Equiv.swap_apply_left,Fin.snoc_last,fUS]
 . have hl:Equiv.swap p (Fin.last n) j≠Fin.last n:=by
     intro e
     apply hj
     have:=congrArg (Equiv.swap p (Fin.last n)) e
     rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain ⟨t,ht⟩:=Fin.exists_castSucc_eq.2 hl
   rw [← ht,Fin.snoc_castSucc,ht,Equiv.swap_apply_self,fUN hj]

lemma q70 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s' : ℕ,s'+1<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   obtain ⟨x,y,hxy⟩:=hnc
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨s',hs,h'⟩:=q115 n _ b s hdep' hnc' hg
 refine ⟨s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''

lemma q141 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∀ b:Bool,∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∀ b:Bool,∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   intro b
   obtain ⟨x,y,hxy⟩:=hnc b
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨b,s',hs,h'⟩:=q114 n _ s hdep' hnc' hg
 refine ⟨b,s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''

def val (gs:List Gate) (n : ℕ) (a : ℕ):BFn n :=
 fun x => (q3 gs (List.ofFn x)).getD a false

lemma q172 (gs:List Gate) (n : ℕ) (i:Fin n):val gs n i=fun x => x i:=by
 funext x
 unfold val
 rw [ve _ _ _ (by simp)]
 simp

lemma q60 {α:Type} (gs:List α) (p : ℕ) (g : α) (hp:gs[p]?=some g) :
   ∃ pre post,gs=pre++g::post/\pre.length=p:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hp).1
 have hget:gs[p]=g:=(List.getElem?_eq_some_iff.1 hp).2
 refine ⟨gs.take p,gs.drop (p+1),?_,by simp;omega⟩
 have h1:gs=gs.take p++gs.drop p:=(List.take_append_drop p gs).symm
 have h2:gs.drop p=gs[p]::gs.drop (p+1):=List.drop_eq_getElem_cons hlt
 exact h1.trans (by rw [h2,hget])

lemma q103 (n : ℕ) (gs:List Gate) (p : ℕ) (g:Gate) (hp:gs[p]?=some g)
   (hlt:∀ a ∈ g.inputs,a < n+p) (x:Fin n->Bool) :
   val gs n (n+p) x=g.op.eval (g.inputs.map fun a => val gs n a x):=by
 obtain ⟨pre,post,rfl,hlen⟩:=q60 gs p g hp
 unfold val
 have h1:q3 (pre++g::post) (List.ofFn x)=q3 post
     (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]):=by
   rw [zd];rfl
 have hl:(q3 pre (List.ofFn x)).length=n+p:=by
   rw [qu];simp [hlen]
 rw [h1,ve _ _ _ (by simp [hl]),z2 _ _ _ _ hl]
 congr 1
 apply List.map_congr_left
 intro a ha
 have hal:=hlt a ha
 have e1:=ve post (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]) a
       (by simp [hl];omega)
 rw [e1,List.getD_append _ _ _ _ (by omega)]

def vi (n : ℕ):List Stat:=List.ofFn fun i:Fin n => Sum.inr (i : ℕ)

lemma q165 (n : ℕ) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y) (vi n,[]):=by
 refine ⟨by simp [vi],?_⟩
 intro i
 by_cases hlt:i < n
 . simp [vi,hlt,qn,ze,q3]
 . rw [lGD _ _ (by simp [vi];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩

lemma q48 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,yq n gs/\gs.length<=s/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set acc:=elim n C.gates (vi n,[]) with hacc
 have hinv:∀ y:Fin n->Bool,Inv n (List.ofFn y) (q3 C.gates (List.ofFn y)) acc :=
   fun y => j7 n _ (by simp) C.gates _ _ ok (q165 n y)
 have hcl:yq n acc.2:=by
   apply q100 n C.gates (vi n,[]) ok
   . intro i
     by_cases hlt:i < n
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
   . intro p g hp;simp at hp
 have hlen:acc.2.length<=s:=by
   have:=q29 n C.gates (vi n,[])
   rw [← hacc] at this
   simp only [List.length_nil,zero_add] at this
   omega
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=((hinv y).2 C.output).2
   have e2:=((hinv y').2 C.output).2
   rw [hst] at e1 e2
   have h1:(q3 C.gates (List.ofFn y)).getD C.output false=f y:=hev y
   have h2:(q3 C.gates (List.ofFn y')).getD C.output false=f y':=hev y'
   rw [← h1,← h2,← e1,← e2];rfl
 | inr j =>
   have hj:j < n+acc.2.length:=by
     obtain ⟨y,_,_⟩:=hnc
     have:=((hinv y).2 C.output).1
     rw [hst] at this
     exact this
   refine ⟨acc.2,j,hcl,hlen,hj,?_⟩
   intro x
   have e1:=((hinv x).2 C.output).2
   rw [hst] at e1
   exact e1.trans (hev x)

def qk {α:Type} (b:Bool) (x : α) (xs:List α):List α :=
 if b then x::xs else xs

def Run {α:Type} (inv : α->α) (meet join : α->α->α) (y : α) (t : ℕ) (ws:List α):Prop :=
 ∀ P : ℕ->List α->Prop,P 0 [y] ->
   (∀ {s xs zs},List.Perm xs zs->P s xs->P s zs) ->
   (∀ {s a r} (neg save:Bool),P s ((if neg then inv a else a)::qk save a r) ->
     P (s+1) (a::r)) ->
   (∀ {s a b r} (c ka kb:Bool),
     P s ((if c then meet a b else join a b)::qk ka a (qk kb b r)) ->
     P (s+1) (a::b::r))->P t ws

lemma Run.done {α inv meet join y} : @Run α inv meet join y 0 [y]:=fun _ d _ _ _ => d

lemma Run.perm {α inv meet join y s xs zs} (p:List.Perm xs zs)
   (h : @Run α inv meet join y s xs):Run inv meet join y s zs :=
 fun P d q u b => q p (h P d q u b)

lemma Run.one {α inv meet join y s a r} (neg save:Bool)
   (h : @Run α inv meet join y s ((if neg then inv a else a)::qk save a r)) :
   Run inv meet join y (s+1) (a::r):=fun P d q u b => u neg save (h P d q u b)

lemma Run.two {α inv meet join y s a b r} (c ka kb:Bool)
   (h : @Run α inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))) :
   Run inv meet join y (s+1) (a::b::r):=fun P d q u v => v c ka kb (h P d q u v)

lemma Run.fold {α inv meet join y} {P:∀ t ws,@Run α inv meet join y t ws->Prop}
   (done:P 0 [y] Run.done)
   (perm:∀ {s xs zs} (hp:List.Perm xs zs) (h:Run inv meet join y s xs),
     P s xs h->P s zs (Run.perm hp h))
   (one:∀ {s a r} (neg save:Bool)
     (h:Run inv meet join y s ((if neg then inv a else a)::qk save a r)),
     P _ _ h->P _ _ (Run.one neg save h))
   (two:∀ {s a b r} (c ka kb:Bool)
     (h:Run inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))),
     P _ _ h->P _ _ (Run.two c ka kb h))
   {t ws} (h:Run inv meet join y t ws):P t ws h:=by
 have hex:=h (fun s xs => ∃ h':Run inv meet join y s xs,P s xs h')
   ⟨Run.done,done⟩
   (fun hp ⟨h',ih⟩ => ⟨Run.perm hp h',perm hp h' ih⟩)
   (fun n k ⟨h',ih⟩ => ⟨Run.one n k h',one n k h' ih⟩)
   (fun c a b ⟨h',ih⟩ => ⟨Run.two c a b h',two c a b h' ih⟩)
 exact hex.elim fun _ hp => hp

lemma wd {α β:Type} (e : α->β) (b:Bool) (x : α) (xs:List α) :
   (qk b x xs).map e=qk b (e x) (xs.map e):=by cases b <;> simp [qk]

lemma wa {α:Type} (b:Bool) (x a : α) (xs:List α) :
   a ∈ qk b x xs ↔ (b=true/\a=x)\/a ∈ xs:=by cases b <;> simp [qk]

lemma q36 {α:Type} (b:Bool) (x : α) (xs:List α) (h:xs.Nodup) (hx:x ∉ xs) :
   (qk b x xs).Nodup:=by
 cases b
 . simpa [qk] using h
 . simpa [qk] using And.intro hx h

lemma Run.map {α β:Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
   {inv' : β->β} {meet' join' : β->β->β}
   (hi:∀ a,e (inv a)=inv' (e a)) (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {y : α} {s : ℕ} {ws:List α} (h:Run inv meet join y s ws) :
   Run inv' meet' join' (e y) s (ws.map e):=by
 induction h using Run.fold with
 | done => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map e) ih
 | @one s a rest neg save _ ih =>
   have e1:((if neg then inv a else a)::qk save a rest).map e
       = (if neg then inv' (e a) else e a)::qk save (e a) (rest.map e):=by
     cases neg <;> simp [wd,hi]
   rw [e1] at ih
   exact Run.one neg save ih
 | @two s a b rest conj ka kb _ ih =>
   have e1:((if conj then meet a b else join a b)::qk ka a (qk kb b rest)).map e
       = (if conj then meet' (e a) (e b) else join' (e a) (e b))
           :: qk ka (e a) (qk kb (e b) (rest.map e)):=by
     cases conj <;> simp [wd,hm,hj]
   rw [e1] at ih
   exact Run.two conj ka kb ih

def wn (n : ℕ) (gs:List Gate) (o a : ℕ):Prop :=
 ∀ P : ℕ->Prop,P o ->
   (∀ q g,gs[q]?=some g->P (n+q)->∀ u ∈ g.inputs,P u)->P a

lemma q34 (n : ℕ) (gs:List Gate) (o : ℕ):wn n gs o o :=
 fun _ ho _ => ho

lemma q33 {n : ℕ} {gs:List Gate} {o q u : ℕ} {g:Gate}
   (hq:gs[q]?=some g) (hr:wn n gs o (n+q)) (hu:u ∈ g.inputs) :
   wn n gs o u :=
 fun P ho hs => hs q g hq (hr P ho hs) u hu

lemma q66 {n : ℕ} {gs:List Gate} {o a : ℕ} (h:wn n gs o a) :
   a=o\/∃ q g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q):=by
 apply h (fun x => x=o\/∃ q g,gs[q]?=some g/\x ∈ g.inputs/\wn n gs o (n+q))
 . exact Or.inl rfl
 . intro q g hq hP u hu
   refine Or.inr ⟨q,g,hq,hu,?_⟩
   rcases hP with rfl | ⟨q',g',hq',hin',hr'⟩
   . exact q34 n gs (n+q)
   . exact q33 hq' hr' hin'

def q11 (n : ℕ) (gs:List Gate) (o p a : ℕ):Prop :=
 a=o\/∃ q,p<=q/\∃ g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q)

open Classical in
noncomputable def liveList (gs:List Gate) (n o p : ℕ):List ℕ :=
 (List.range (n+p)).filter (fun a => decide (q11 n gs o p a))

lemma qw (gs:List Gate) (n o p a : ℕ) :
   a ∈ liveList gs n o p ↔ a < n+p/\q11 n gs o p a:=by
 simp [liveList]

lemma vy (gs:List Gate) (n o p : ℕ):(liveList gs n o p).Nodup :=
 List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ}:BFn n->BFn n:=fun a x => !a x

abbrev meetF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x&&b x

abbrev joinF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x||b x

lemma q73 (n : ℕ) (gs:List Gate) (o : ℕ) (hcl:yq n gs)
   (p : ℕ) (g:Gate) (hg:gs[p]?=some g) (hr:wn n gs o (n+p)) (a : ℕ) :
   a ∈ liveList gs n o (p+1) ↔
     a=n+p\/(a ∈ liveList gs n o p/\(a ∈ g.inputs->q11 n gs o (p+1) a)):=by
 rw [qw,qw]
 constructor
 . rintro ⟨hlt,hl⟩
   by_cases ha:a=n+p
   . exact Or.inl ha
   . refine Or.inr ⟨⟨by omega,?_⟩,fun _ => hl⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
 . rintro (rfl | ⟨⟨hlt,hl⟩,himp⟩)
   . refine ⟨by omega,?_⟩
     rcases q66 hr with h | ⟨q,g',hg',hin,hrq⟩
     . exact Or.inl h
     . refine Or.inr ⟨q,?_,g',hg',hin,hrq⟩
       have:=j2 (hcl q g' hg') _ hin
       omega
   . refine ⟨by omega,?_⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . by_cases hqp:q=p
       . subst hqp
         rw [hg] at hg'
         cases hg'
         exact himp hin
       . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩

def gfn {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)):BFn n :=
 fun x => A.any (fun a => x a)||E.any (fun e => x e.1&&x e.2)

def j9 {α:Type} [BEq α]:List α->List α->List α
 | [],acc => acc.reverse
 | a::t,acc => if acc.contains a then j9 t acc else j9 t (a::acc)

def q206 {α:Type} [BEq α] (l:List α):List α:=j9 l []

lemma ww {α:Type} [DecidableEq α]:∀ (l acc:List α) (x : α),
   x ∈ j9 l acc ↔ x ∈ l\/x ∈ acc
 | [],acc,x => by simp [j9]
 | a::t,acc,x => by
   simp only [j9]
   by_cases h:acc.contains a=true
   . simp only [h,↓reduceIte,ww,lMM]
     have ha:a ∈ acc:=by simpa using h
     constructor
     . rintro (ht | hacc)
       . exact Or.inl (Or.inr ht)
       . exact Or.inr hacc
     . rintro ((rfl | ht) | hacc)
       . exact Or.inr ha
       . exact Or.inl ht
       . exact Or.inr hacc
   . simp only [h,bFT,↓reduceIte,ww,lMM]
     tauto

lemma q23 {α:Type} [DecidableEq α] (l:List α) (x : α) :
   x ∈ q206 l ↔ x ∈ l:=by
 simpa [q206] using ww l [] x

def fix0A {n : ℕ} (A:List (Fin n)) (p:Fin n):List (Fin n) :=
 A.filter (·!=p)

def fix0E {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 E.filter (fun e => e.1!=p&&e.2!=p)

def nbrs {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 E.filterMap (fun e => if e.1==p then some e.2 else if e.2==p then some e.1 else none)

def fix1A {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 q206 (A++nbrs E p)

def fix1E {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 let A1:=fix1A A E p
 E.filter (fun e => e.1!=p&&e.2!=p&&!A1.contains e.1&&!A1.contains e.2)

def depCheck {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):Bool :=
 A.contains p ||
   (E.all (fun e => e.1!=e.2) &&
     E.any (fun e => (e.1==p&&!A.contains e.2)||(e.2==p&&!A.contains e.1)))

def isoCheck {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k)) (π:Fin n->Fin k):Bool :=
 E.all (fun e => Eb.any (fun e' => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1))) &&
 Eb.all (fun e' => E.any (fun e => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1)))

lemma q176 {n : ℕ} (A:List (Fin n)) (hnd:A.Nodup) :
   ∀ s : ℕ,HasCircuitSize n (gfn A []) s->A.length - 1<=s:=by
 intro s h
 have hd:=q117 n (gfn A []) A.toFinset (by
   intro i hi
   have hiA:i ∈ A:=List.mem_toFinset.1 hi
   refine ⟨fun _ => false,?_⟩
   have h0:gfn A [] (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A [] (Function.update (fun _ => false) i true)=true:=by
     simp only [gfn,List.any_nil,Bool.or_false,lAN]
     exact ⟨i,hiA,by simp⟩
   simpa [h0,h1]) s h
 rw [List.toFinset_card_of_nodup hnd] at hd
 omega

lemma q99 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n))
   (h:(!A.isEmpty||!E.isEmpty)=true) :
   ∃ x y:Fin n->Bool,gfn A E x≠gfn A E y:=by
 refine ⟨fun _ => false,fun _ => true,?_⟩
 have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
 have h1:gfn A E (fun _ => true)=true:=by
   cases A with
   | cons a t => simp [gfn]
   | nil =>
     cases E with
     | nil => simp at h
     | cons e t => simp [gfn]
 rw [h0,h1];decide

lemma q154 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (h:depCheck A E p=true) :
   ∃ x:Fin n->Bool,gfn A E (Function.update x p (!x p))≠gfn A E x:=by
 simp only [depCheck,bOT,bAT,List.contains_eq_mem,decide_eq_true_eq,
   lAL,lAN,bne_iff_ne,beq_iff_eq,bNT,
   decide_eq_false_iff_not] at h
 rcases h with hpA | ⟨hloop,⟨e,heE,⟨rfl,hqA⟩ | ⟨rfl,hqA⟩⟩⟩
 . refine ⟨fun _ => false,?_⟩
   have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A E (Function.update (fun _ => false) p true)=true:=by
     simp only [gfn,bOT,lAN]
     exact Or.inl ⟨p,hpA,by simp⟩
   simpa [h0,h1]
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.2),?_⟩
   have h0:gfn A E (fun i => decide (i=e.2))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.2)) e.1 (!decide (e.1=e.2)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [hne]
     . simp [fUN (Ne.symm hne)]
   rw [h0,h1];decide
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.1),?_⟩
   have h0:gfn A E (fun i => decide (i=e.1))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.1)) e.2 (!decide (e.2=e.1)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [fUN hne]
     . simp [Ne.symm hne]
   rw [h0,h1];decide

lemma zo {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n) :
   (fun x => gfn A E (Function.update x p false))=gfn (fix0A A p) (fix0E E p):=by
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix0A,fix0E,bOT,lAN,List.mem_filter,
   bAT,bne_iff_ne]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . by_cases hap:a=p
     . subst hap;simp at hxa
     . exact Or.inl ⟨a,⟨ha,hap⟩,by simpa [fUN hap] using hxa⟩
   . by_cases h1p:e.1=p
     . rw [h1p,fUS] at h1;cases h1
     . by_cases h2p:e.2=p
       . rw [h2p,fUS] at h2;cases h2
       . exact Or.inr ⟨e,⟨he,h1p,h2p⟩,
           by simpa [fUN h1p] using h1,
           by simpa [fUN h2p] using h2⟩
 . rintro (⟨a,⟨ha,hap⟩,hxa⟩ | ⟨e,⟨he,h1p,h2p⟩,h1,h2⟩)
   . exact Or.inl ⟨a,ha,by simpa [fUN hap] using hxa⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using h1,
       by simpa [fUN h2p] using h2⟩

lemma q109 {n : ℕ} (E:List (Fin n × Fin n)) (p q:Fin n) :
   q ∈ nbrs E p ↔ ∃ e ∈ E,(e.1=p/\e.2=q)\/(e.1≠p/\e.2=p/\e.1=q):=by
 simp only [nbrs,List.mem_filterMap,beq_iff_eq]
 constructor
 . rintro ⟨e,he,h⟩
   split_ifs at h with h1 h2
   . cases h;exact ⟨e,he,Or.inl ⟨h1,rfl⟩⟩
   . cases h;exact ⟨e,he,Or.inr ⟨h1,h2,rfl⟩⟩
 . rintro ⟨e,he,⟨h1,h2⟩ | ⟨h1,h2,h3⟩⟩
   . exact ⟨e,he,by rw [if_pos h1,h2]⟩
   . exact ⟨e,he,by rw [if_neg h1,if_pos h2,h3]⟩

lemma kx {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true) :
   (fun x => gfn A E (Function.update x p true))=gfn (fix1A A E p) (fix1E A E p):=by
 have hpnot:p ∉ A:=by simpa [List.contains_eq_mem] using hpA
 have hne:∀ e ∈ E,e.1≠e.2:=by simpa [lAL,bne_iff_ne] using hloop
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix1E,bOT,lAN,bAT,List.mem_filter,
   bne_iff_ne,bNT,List.contains_eq_mem,decide_eq_false_iff_not]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . have hap:a≠p:=fun h => hpnot (h ▸ ha)
     refine Or.inl ⟨a,?_,by simpa [fUN hap] using hxa⟩
     rw [fix1A,q23];exact List.mem_append_left _ ha
   . by_cases h1p:e.1=p
     . have h2p:e.2≠p:=fun h => hne e he (h1p.trans h.symm)
       refine Or.inl ⟨e.2,?_,by simpa [fUN h2p] using h2⟩
       rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.2).2 ⟨e,he,Or.inl ⟨h1p,rfl⟩⟩)
     . by_cases h2p:e.2=p
       . refine Or.inl ⟨e.1,?_,by simpa [fUN h1p] using h1⟩
         rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.1).2 ⟨e,he,Or.inr ⟨h1p,h2p,rfl⟩⟩)
       . have hx1:x e.1=true:=by simpa [fUN h1p] using h1
         have hx2:x e.2=true:=by simpa [fUN h2p] using h2
         by_cases m1:e.1 ∈ fix1A A E p
         . exact Or.inl ⟨e.1,m1,hx1⟩
         . by_cases m2:e.2 ∈ fix1A A E p
           . exact Or.inl ⟨e.2,m2,hx2⟩
           . exact Or.inr ⟨e,⟨he,⟨⟨h1p,h2p⟩,m1⟩,m2⟩,hx1,hx2⟩
 . rintro (⟨a,ha,hxa⟩ | ⟨e,⟨he,⟨⟨h1p,h2p⟩,_⟩,_⟩,hx1,hx2⟩)
   . rw [fix1A,q23,List.mem_append] at ha
     rcases ha with haA | han
     . have hap:a≠p:=fun h => hpnot (h ▸ haA)
       exact Or.inl ⟨a,haA,by simpa [fUN hap] using hxa⟩
     . obtain ⟨e,he,⟨h1,rfl⟩ | ⟨h1,h2,rfl⟩⟩:=(q109 E p a).1 han
       . have h2p:e.2≠p:=fun h => hne e he (h1.trans h.symm)
         exact Or.inr ⟨e,he,by simp [h1],by simpa [fUN h2p] using hxa⟩
       . exact Or.inr ⟨e,he,by simpa [fUN h1] using hxa,by simp [h2]⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using hx1,
       by simpa [fUN h2p] using hx2⟩

lemma q190 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hA:A'=fix0A A p) (hE:E'=fix0E E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p false))=gfn A' E':=by
   rw [hA,hE];exact zo A E p
 have hnc':∃ x y,gfn A E (Function.update x p false)≠gfn A E (Function.update y p false):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p false s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega

lemma q189 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA:A'=fix1A A E p) (hE:E'=fix1E A E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p true))=gfn A' E':=by
   rw [hA,hE];exact kx A E p hpA hloop
 have hnc':∃ x y,gfn A E (Function.update x p true)≠gfn A E (Function.update y p true):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p true s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega

lemma q155 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1))
   (A0:List (Fin (n+1))) (E0:List (Fin (n+1) × Fin (n+1)))
   (A1:List (Fin (n+1))) (E1:List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA0:A0=fix0A A p) (hE0:E0=fix0E E p)
   (hA1:A1=fix1A A E p) (hE1:E1=fix1E A E p)
   (hnc0:(!A0.isEmpty||!E0.isEmpty)=true)
   (hnc1:(!A1.isEmpty||!E1.isEmpty)=true)
   (ih0:∀ s,HasCircuitSize (n+1) (gfn A0 E0) s->k<=s)
   (ih1:∀ s,HasCircuitSize (n+1) (gfn A1 E1) s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+2<=s:=by
 intro s h
 have hres0:(fun x => gfn A E (Function.update x p false))=gfn A0 E0:=by
   rw [hA0,hE0];exact zo A E p
 have hres1:(fun x => gfn A E (Function.update x p true))=gfn A1 E1:=by
   rw [hA1,hE1];exact kx A E p hpA hloop
 have hnc:∀ b:Bool,∃ x y,gfn A E (Function.update x p b)≠gfn A E (Function.update y p b):=by
   intro b
   cases b with
   | false =>
     obtain ⟨x,y,hxy⟩:=q99 A0 E0 hnc0
     exact ⟨x,y,by simpa [congrFun hres0] using hxy⟩
   | true =>
     obtain ⟨x,y,hxy⟩:=q99 A1 E1 hnc1
     exact ⟨x,y,by simpa [congrFun hres1] using hxy⟩
 obtain ⟨b,s',hs',h'⟩:=q141 n (gfn A E) p s (q154 A E p hdep) hnc h
 cases b with
 | false => rw [hres0] at h';have:=ih0 s' h';omega
 | true => rw [hres1] at h';have:=ih1 s' h';omega

lemma q204 {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true) :
   (fun y:Fin k->Bool => gfn [] E (y ∘ π))=gfn [] Eb:=by
 simp only [isoCheck,bAT,lAL,lAN,
   bOT,beq_iff_eq] at hiso
 obtain ⟨h1,h2⟩:=hiso
 funext y
 apply Bool.eq_iff_iff.2
 simp only [gfn,List.any_nil,Bool.false_or,lAN,bAT,Function.comp_apply]
 constructor
 . rintro ⟨e,he,hy1,hy2⟩
   obtain ⟨e',he',⟨a,b⟩ | ⟨a,b⟩⟩:=h1 e he
   . exact ⟨e',he',a ▸ hy1,b ▸ hy2⟩
   . exact ⟨e',he',b ▸ hy2,a ▸ hy1⟩
 . rintro ⟨e',he',hy1,hy2⟩
   obtain ⟨e,he,⟨a,b⟩ | ⟨a,b⟩⟩:=h2 e' he'
   . exact ⟨e,he,a.symm ▸ hy1,b.symm ▸ hy2⟩
   . exact ⟨e,he,a.symm ▸ hy2,b.symm ▸ hy1⟩

lemma q191 {n k val : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true)
   (hb:∀ s : ℕ,HasCircuitSize k (gfn [] Eb) s->val<=s) :
   ∀ s : ℕ,HasCircuitSize n (gfn [] E) s->val<=s:=by
 intro s h
 have h':=yn π (gfn [] E) s h
 rw [q204 E Eb π hiso] at h'
 exact hb s h'

lemma q202 {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
   xs.length<=s+1:=by
 induction h using Run.fold with
 | done => simp
 | perm hp _ ih => rwa [← hp.length_eq]
 | one neg save h ih => cases save <;> simp_all [qk] <;> omega
 | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [qk] <;> omega

lemma q101 {m : ℕ} {g:Gate} (h:q161 m g):NOk g:=by
 rcases h with ⟨hop,j,_,hin⟩ | ⟨hop,j,k,_,_,hin⟩
 . exact ⟨⟨by simp [hop],by simp [hin]⟩,fun _ => by simp [hin]⟩
 . refine ⟨⟨?_,by simp [hin]⟩,fun hnot => ?_⟩
   . rcases hop with h1 | h1 <;> simp [h1]
   . rcases hop with h1 | h1 <;> rw [h1] at hnot <;> cases hnot

lemma ja {n : ℕ} {gs:List Gate} (h:yq n gs):∀ g ∈ gs,NOk g:=by
 intro g hg
 obtain ⟨p,hp,rfl⟩:=List.getElem_of_mem hg
 exact q101 (h p gs[p] (List.getElem?_eq_getElem hp))

lemma q157 {n : ℕ} {gs:List Gate} (h:yq n gs) (p : ℕ):yq n (gs.take p):=by
 intro q g hq
 have hlt:q < (gs.take p).length:=(List.getElem?_eq_some_iff.1 hq).1
 have hqp:q < p:=by simp at hlt;omega
 rw [List.getElem?_take_of_lt hqp] at hq
 exact h q g hq

def InvR (R : ℕ->Prop) (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length /\
 (∀ i : ℕ,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) /\
 (∀ i : ℕ,R i->ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false)

lemma q175 (R : ℕ->Prop) (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g) ->
     (∀ q g,gs[q]?=some g->R (acc.1.length+q)->∀ a ∈ g.inputs,R a) ->
     InvR R n y w acc ->
     InvR R n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ _ h;exact h
 | cons g gs ih =>
   intro w acc hok hR h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   . intro q g' hq hRq a ha
     have hlen:(qa n acc g).1.length=acc.1.length+1:=by simp [qa]
     rw [hlen] at hRq
     exact hR (q+1) g' (by simpa using hq) (by simpa [nAA,nAC 1 q] using hRq) a ha
   . obtain ⟨hl,hv,he⟩:=h
     set w':=q3 acc.2 y with hw'
     have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         rw [lw'];exact hv a)
     rw [lw'] at hs
     set r:=qg g.op (n+acc.2.length) ins with hr
     have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
       rw [zd]
     obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
     refine ⟨by simp [qa,hl],?_,?_⟩
     . intro i
       show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false))
       rw [lLA,← nAA]
       by_cases hil:i=acc.1.length
       . subst hil;rw [z0];exact hs.1
       . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
     . intro i hi
       show ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
       rw [hnew]
       by_cases hil:i=acc.1.length
       . subst hil
         rw [z0,hl,z0,hs.2]
         congr 1
         rw [hins,lMMp]
         apply List.map_congr_left
         intro a ha
         exact he a (hR 0 g rfl (by simpa using hi) a ha)
       . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
         rw [ht,jg _ _ _ (by rw [lw'];exact hv i)]
         exact he i hi

lemma y7 (n : ℕ) (f:BFn n) (pre post:List Gate) (g:Gate) (o : ℕ)
   (hcl:yq n (pre++g::post)) (ho:o < n+(pre++g::post).length)
   (hev:∀ x,val (pre++g::post) n o x=f x)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (st:Stat) (hstV:qn (n+pre.length) st)
   (hcond:(∀ x,ze (q3 pre (List.ofFn x)) st=val (pre++g::post) n (n+pre.length) x) \/
            ¬ wn n (pre++g::post) o (n+pre.length)) :
   ∃ gs' o',yq n gs'/\gs'.length<=pre.length+post.length /\
     o' < n+gs'.length/\∀ x,val gs' n o' x=f x:=by
 set gs:=pre++g::post with hgs
 set p:=pre.length with hp
 set acc0:List Stat × List Gate:=(vi (n+p)++[st],pre) with hacc0
 set acc:=elim n post acc0 with hacc
 have hok_post:∀ g' ∈ post,Ok g':=fun g' hg' =>
   (ja hcl g' (List.mem_append_right _ (List.mem_cons_of_mem _ hg'))).1
 have hcl_pre:yq n pre:=by
   have:pre=gs.take p:=by simp [hgs,hp]
   rw [this];exact q157 hcl p
 have hv0:∀ i,qn (n+acc0.2.length) (acc0.1.getD i (Sum.inl false)):=by
   intro i
   simp only [hacc0,hp]
   by_cases hip:i=n+pre.length
   . subst hip;rw [z2 _ _ _ _ (by simp [vi])];exact hstV
   . rw [q8 _ _ _ _ (by simp [vi];omega)]
     by_cases hlt:i < n+pre.length
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
 have hcl':yq n acc.2:=q100 n post acc0 hok_post hv0 hcl_pre
 have hlen':acc.2.length<=pre.length+post.length:=by
   simpa [hacc,hacc0] using q29 n post acc0
 have hinv_all:∀ x:Fin n->Bool,
     qn (n+acc.2.length) (acc.1.getD o (Sum.inl false)) /\
     ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))=f x:=by
   intro x
   have hsplit:q3 gs (List.ofFn x)=q3 post (q3 (pre++[g]) (List.ofFn x)):=by
     have:gs=(pre++[g])++post:=by simp [hgs]
     rw [this,zd]
   have hl1:(q3 (pre++[g]) (List.ofFn x)).length=n+p+1:=by
     rw [qu];simp [hp];omega
   have hval_lt:∀ i < n+p,(q3 (pre++[g]) (List.ofFn x)).getD i false =
       (q3 pre (List.ofFn x)).getD i false:=by
     intro i hi
     rw [zd,ve _ _ _ (by rw [qu];simp;omega)]
   rcases hcond with hval_eq | hdead
   . have hinv0:Inv n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],?_⟩
       intro i
       refine ⟨hv0 i,?_⟩
       simp only [hacc0]
       by_cases hip:i=n+p
       . subst hip
         rw [z2 _ _ _ _ (by simp [vi])]
         have h1:=hval_eq x
         unfold val at h1
         rw [hsplit,ve _ _ _ (by omega)] at h1
         exact h1
       . rw [q8 _ _ _ _ (by simp [vi];omega)]
         by_cases hlt:i < n+p
         . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
             Option.getD_some,ze]
           exact (hval_lt i hlt).symm
         . rw [lGD _ _ (by simp [vi];omega),
               lGD _ _ (by omega)];rfl
     have hres:=j7 n (List.ofFn x) (by simp) post _ acc0 hok_post hinv0
     rw [← hsplit] at hres
     have h1:=hres.2 o
     exact ⟨h1.1,h1.2.trans (hev x)⟩
   . have hinv0:InvR (wn n gs o) n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],hv0,?_⟩
       intro i hi
       simp only [hacc0]
       have hne:i≠n+p:=fun e => hdead (e ▸ hi)
       rw [q8 _ _ _ _ (by simp [vi];omega)]
       by_cases hlt:i < n+p
       . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
           Option.getD_some,ze]
         exact (hval_lt i hlt).symm
       . rw [lGD _ _ (by simp [vi];omega),
             lGD _ _ (by omega)];rfl
     have hR:∀ q g',post[q]?=some g'->wn n gs o (acc0.1.length+q)->∀ a ∈ g'.inputs,wn n gs o a:=by
       intro q g' hq hRq a ha
       have hidx:gs[p+1+q]?=some g':=by
         have:gs=(pre++[g])++post:=by simp [hgs]
         rw [this,List.getElem?_append_right (by simp [hp])]
         simpa [hp,Nat.add_sub_cancel_left] using hq
       have hlen0:acc0.1.length=n+p+1:=by simp [hacc0,vi]
       rw [hlen0] at hRq
       exact q33 hidx (by simpa [nAA] using hRq) ha
     have hres:=q175 (wn n gs o) n (List.ofFn x) (by simp) post _ acc0 hok_post hR hinv0
     rw [← hsplit] at hres
     exact ⟨hres.2.1 o,(hres.2.2 o (q34 n gs o)).trans (hev x)⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=(hinv_all y).2
   have e2:=(hinv_all y').2
   rw [hst] at e1 e2
   exact e1.symm.trans e2
 | inr j =>
   obtain ⟨y,_,_⟩:=hnc
   have hj:=(hinv_all y).1
   rw [hst] at hj
   refine ⟨acc.2,j,hcl',hlen',hj,?_⟩
   intro x
   have e:=(hinv_all x).2
   rw [hst] at e
   exact e

structure MinClean (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ):Prop where
 hcl:yq n gs
 ho:o < n+gs.length
 hev:∀ x,val gs n o x=f x
 hreach:∀ p < gs.length,wn n gs o (n+p)
 hncG:∀ p < gs.length,∀ c:Bool,val gs n (n+p)≠fun _ => c
 hndup:∀ p < gs.length,∀ u < n+p,val gs n (n+p)≠val gs n u

open Classical in
lemma q56 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,MinClean n f gs o/\gs.length<=s:=by
 have hex:∃ k,∃ gs o,yq n gs/\gs.length=k/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
   obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=q48 n f s hnc h
   exact ⟨gs.length,gs,o,hcl,rfl,ho,hev⟩
 set k:=Nat.find hex with hk
 obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=Nat.find_spec hex
 have hle:k<=s:=by
   obtain ⟨gs0,o0,hcl0,hlen0,ho0,hev0⟩:=q48 n f s hnc h
   exact le_trans (Nat.find_min' hex ⟨gs0,o0,hcl0,rfl,ho0,hev0⟩) hlen0
 have hmin:∀ gs' o',yq n gs'->o' < n+gs'.length->(∀ x,val gs' n o' x=f x)->gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev'
   rw [hlen]
   exact Nat.find_min' hex ⟨gs',o',hcl',rfl,ho',hev'⟩
 refine ⟨gs,o,⟨hcl,ho,hev,?_,?_,?_⟩,by omega⟩
 . intro p hp
   by_contra hnr
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl false) trivial (Or.inr hnr)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp c heqc
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl c) trivial
       (Or.inl fun x => by rw [heqc];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp u hu hequ
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inr u) hu
       (Or.inl fun x => by
         rw [hequ];unfold val
         rw [zd,ve _ _ _ (by rw [qu];simp;omega)];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega

def wf (n : ℕ) (v:Fin n):List Stat :=
 List.ofFn fun i:Fin n => if i=v then Sum.inl false else Sum.inr (i : ℕ)

lemma q139 (n : ℕ) (v:Fin n) (x:Fin n->Bool) :
   Inv n (List.ofFn x) (List.ofFn (Function.update x v false)) (wf n v,[]):=by
 refine ⟨by simp [wf],?_⟩
 intro i
 by_cases hlt:i < n
 . by_cases hiv:(⟨i,hlt⟩:Fin n)=v
   . subst hiv;simp [wf,hlt,qn,ze]
   . simp [wf,hlt,hiv,qn,ze,q3,fUN hiv]
 . rw [lGD _ _ (by simp [wf];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩

lemma wz (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (v:Fin n) (B : ℕ)
   (hcl:yq n gs) (hev:∀ x,val gs n o x=f x)
   (hnc0:∃ x y:Fin n->Bool,f (Function.update x v false)≠f (Function.update y v false))
   (hlb:∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->B<=s') :
   (∀ c,(elim n gs (wf n v,[])).1.getD o (Sum.inl false)≠Sum.inl c) /\
   B<=(elim n gs (wf n v,[])).2.length:=by
 set acc:=elim n gs (wf n v,[]) with hacc
 have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) acc :=
   fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hcl g hg).1) (q139 n v x)
 have hval:∀ x,ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))
     = f (Function.update x v false):=fun x => ((hinv x).2 o).2.trans (hev _)
 have hno:∀ c,acc.1.getD o (Sum.inl false)≠Sum.inl c:=by
   intro c hc
   obtain ⟨x,y,hne⟩:=hnc0
   apply hne
   rw [← hval x,← hval y,hc];rfl
 refine ⟨hno,?_⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c => exact absurd hst (hno c)
 | inr j =>
   apply hlb acc.2.length
   refine ⟨⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro x;have:=hval x;rw [hst] at this;exact this

lemma k3 (n u w : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->u < acc.1.length->w < acc.1.length ->
   (∃ cu,acc.1.getD u (Sum.inl false)=Sum.inl cu) ->
   (∃ cw,acc.1.getD w (Sum.inl false)=Sum.inl cw) ->
   (∃ g₁ ∈ gs,u ∈ g₁.inputs) ->
   (∃ g₂ ∈ gs,w ∈ g₂.inputs) ->
   (∀ g ∈ gs,¬ (u ∈ g.inputs/\w ∈ g.inputs)) ->
   (elim n gs acc).2.length+2<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ _ _ h1 _ _;obtain ⟨g,hg,_⟩:=h1;simp at hg
 | cons g gs ih =>
   intro acc hok hu hw hcu hcw hg1 hg2 hdisj
   rw [k4,lLC]
   have hgn:NOk g:=hok g List.mem_cons_self
   have hgsn:∀ g' ∈ gs,NOk g':=fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
   by_cases hug:u ∈ g.inputs
   . have hwg:w ∉ g.inputs:=fun h => hdisj g List.mem_cons_self ⟨hug,h⟩
     obtain ⟨cu,hcu⟩:=hcu
     have h0:=vs n acc g hgn u hug cu hcu
     have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
       obtain ⟨g',hg',hw'⟩:=hg2
       rcases List.mem_cons.1 hg' with rfl | hmem
       . exact absurd hw' hwg
       . exact ⟨g',hmem,hw'⟩
     have h1:=zt n w gs (qa n acc g) hgsn (by simp [qa];omega)
       (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
       hg2'
     omega
   . by_cases hwg:w ∈ g.inputs
     . obtain ⟨cw,hcw⟩:=hcw
       have h0:=vs n acc g hgn w hwg cw hcw
       have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have h1:=zt n u gs (qa n acc g) hgsn (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         hg1'
       omega
     . have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
         obtain ⟨g',hg',hw'⟩:=hg2
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hw' hwg
         . exact ⟨g',hmem,hw'⟩
       have h1:=ih (qa n acc g) hgsn (by simp [qa];omega) (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
         hg1' hg2' (fun g' hg' => hdisj g' (List.mem_cons_of_mem _ hg'))
       have h2:(qa n acc g).2.length<=acc.2.length+1:=by
         simp only [qa,lLA]
         have:=y2 (qg g.op (n+acc.2.length)
           (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
         omega
       omega

inductive TagRun {α:Type} (inv : α->α) (meet join : α->α->α) (zero one goal : α) :
   ℕ->List (α × ℕ)->Prop where
 | done (tg : ℕ):TagRun inv meet join zero one goal 0 [(goal,tg)]
 | perm {s xs zs}:List.Perm xs zs ->
     TagRun inv meet join zero one goal s xs ->
     TagRun inv meet join zero one goal s zs
 | uNot {s a ta r} (save:Bool) :
     ta≠1->ta≠2->(ta=3->save=false) ->
     inv a≠zero->inv a≠one->inv a≠a->(∀ x ∈ r,x.1≠inv a) ->
     TagRun inv meet join zero one goal s
       ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Bool) :
     ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
     join a b≠zero->join a b≠one ->
     join a b≠a->join a b≠b->(∀ x ∈ r,x.1≠join a b) ->
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Bool) :
     ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
     meet a b≠zero->meet a b≠one ->
     meet a b≠a->meet a b≠b->(∀ x ∈ r,x.1≠meet a b) ->
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)

lemma TagRun.toRun {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   Run inv meet join goal s (ws.map Prod.fst):=by
 induction h with
 | done _ => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map Prod.fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   have e:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst)
       = (if true then inv a else a)::qk save a (r.map Prod.fst):=by
     cases save <;> simp [qk]
   rw [e] at ih
   exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst)
       = (if false then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map Prod.fst)
       = (if true then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two true ka kb ih

lemma TagRun.len_le {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   ws.length<=s+1:=by
 have:=q202 h.toRun
 simpa using this

lemma TagRun.map {α β:Type} (e : α->β) (hinj:Function.Injective e)
   {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {inv' : β->β} {meet' join' : β->β->β} {zero' one' goal' : β}
   (h0:e zero=zero') (h1:e one=one') (hg:e goal=goal')
   (hi:∀ a,e (inv a)=inv' (e a))
   (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   TagRun inv' meet' join' zero' one' goal' s (ws.map fun p => (e p.1,p.2)):=by
 induction h with
 | done tg => rw [← hg];exact TagRun.done tg
 | perm hp _ ih => exact TagRun.perm (hp.map _) ih
 | @uNot s a ta r save h1t h2t h3t hnz hno hna hnr _ ih =>
   have e1:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fun p => (e p.1,p.2))
       = (inv' (e a),if ta=3 then 2 else 0)::qk save (e a,0) (r.map fun p => (e p.1,p.2)):=by
     cases save <;> simp [qk,hi]
   rw [e1] at ih
   refine TagRun.uNot save h1t h2t h3t ?_ ?_ ?_ ?_ ih
   . rw [← hi,← h0];exact fun h => hnz (hinj h)
   . rw [← hi,← h1];exact fun h => hno (hinj h)
   . rw [← hi];exact fun h => hna (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hi];exact fun h => hnr y hy (hinj h)
 | @bOr s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fun p => (e p.1,p.2))
       = (join' (e a) (e b),0)::qk ka (e a,if ta=3 then 1 else 0) (qk kb (e b,if tb=3 then 1 else 0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hj]
   rw [e1] at ih
   refine TagRun.bOr ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hj,← h0];exact fun h => hnz (hinj h)
   . rw [← hj,← h1];exact fun h => hno (hinj h)
   . rw [← hj];exact fun h => hna (hinj h)
   . rw [← hj];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hj];exact fun h => hnr y hy (hinj h)
 | @bAnd s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fun p => (e p.1,p.2))
       = (meet' (e a) (e b),if ta=3\/tb=3 then 1 else 0)::qk ka (e a,0) (qk kb (e b,0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hm]
   rw [e1] at ih
   refine TagRun.bAnd ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hm,← h0];exact fun h => hnz (hinj h)
   . rw [← hm,← h1];exact fun h => hno (hinj h)
   . rw [← hm];exact fun h => hna (hinj h)
   . rw [← hm];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hm];exact fun h => hnr y hy (hinj h)

def v3 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ):List Stat × List Gate :=
 elim n (gs.take p) (wf n v,[])

lemma vb (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (hp:p<=gs.length) :
   (v3 n gs v p).1.length=n+p:=by
 unfold v3
 rw [q50]
 simp [wf,List.length_take,Nat.min_eq_left hp]

lemma q30 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (g:Gate) (hg:gs[p]?=some g) :
   v3 n gs v (p+1)=qa n (v3 n gs v p) g:=by
 unfold v3
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 rw [List.take_succ_eq_append_getElem hlt,hge,jz,k4]
 rfl

lemma zj (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) :
   elim n (gs.drop p) (v3 n gs v p)=elim n gs (wf n v,[]):=by
 unfold v3
 rw [← jz,List.take_append_drop]

def yf (n : ℕ) (gs:List Gate) (f:BFn n) (p a tg : ℕ):Prop :=
 match tg with
 | 0 => True
 | 1 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 2 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl true /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 3 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+2
 | _ => False

lemma q12 {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ}
   (h:yf n gs f p a tg):tg<=3:=by
 match tg with
 | 0 | 1 | 2 | 3 => omega
 | _+4 => exact False.elim h

lemma vv {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ} {g:Gate}
   (hg:gs[p]?=some g) (ha:a < n+p) (h:yf n gs f p a tg) :
   yf n gs f (p+1) a tg:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 have hdrop:gs.drop p=g::gs.drop (p+1):=by rw [List.drop_eq_getElem_cons hlt,hge]
 have step_aux:∀ v c B,
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl c ->
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
     (v3 n gs v (p+1)).1.getD a (Sum.inl false)=Sum.inl c /\
     (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length <=
       (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
   intro v c B hget hbd
   have hsucc:=q30 n gs v p g hg
   have hfl:=vb n gs v p (by omega)
   constructor
   . rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
   . have heq:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
       rw [zj,zj]
     have hlen2:(v3 n gs v (p+1)).2.length<=(v3 n gs v p).2.length+1:=by
       rw [hsucc];simp only [qa,lLA]
       have:=y2 (qg g.op (n+(v3 n gs v p).2.length)
         (g.inputs.map fun i => (v3 n gs v p).1.getD i (Sum.inl false))).1
       omega
     have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
     rw [heq];omega
 match tg with
 | 0 => trivial
 | 1 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 1 hget hbd⟩
 | 2 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v true 1 hget hbd⟩
 | 3 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 2 hget hbd⟩
 | _+4 => exact False.elim h

lemma zr {n : ℕ} {gs:List Gate} {o p u : ℕ} {f:BFn n} {v:Fin n} {c:Bool}
   (hm:MinClean n f gs o) (hp:p<=gs.length)
   (hlive:u ∈ liveList gs n o p)
   (hnc:∃ x y,f (Function.update x v false)≠f (Function.update y v false))
   (hconst:(v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c) :
   ∃ g' ∈ gs.drop p,u ∈ g'.inputs:=by
 have ⟨hlt,hl⟩:=(qw gs n o p u).1 hlive
 rcases hl with rfl | ⟨q,hq,g',hg',hin,_⟩
 . exfalso
   have hfl:=vb n gs v p hp
   have heq:(elim n gs (wf n v,[])).1.getD u (Sum.inl false)=Sum.inl c:=by
     rw [← zj n gs v p,wy n u _ _ _ (by omega)];exact hconst
   have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) (elim n gs (wf n v,[])) :=
     fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hm.hcl g hg).1) (q139 n v x)
   obtain ⟨x,y,hne⟩:=hnc
   apply hne
   have e1:=((hinv x).2 u).2.trans (hm.hev _)
   have e2:=((hinv y).2 u).2.trans (hm.hev _)
   rw [heq] at e1 e2
   exact e1.symm.trans e2
 . have hqlt:q < gs.length:=(List.getElem?_eq_some_iff.1 hg').1
   have hqeq:gs[q]=g':=(List.getElem?_eq_some_iff.1 hg').2
   refine ⟨g',?_,hin⟩
   have:g'=(gs.drop p)[q - p]'(by simp;omega):=by
     rw [List.getElem_drop];simp [show p+(q - p)=q by omega,hqeq]
   rw [this]
   exact List.getElem_mem _

lemma q21 {n : ℕ} {gs:List Gate} {o p j : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length)
   (hval:∀ x,val gs n (n+p) x=!(val gs n j x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by
   intro e;have h0:=hval (fun _ => false);rw [e] at h0
   cases hv:val gs n (n+p) (fun _ => false) <;> rw [hv] at h0 <;> cases h0
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;exact hne (hj.trans hnp.symm)
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hncG q hrlt false
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hncG q hrlt true
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne

lemma q22 {n : ℕ} {gs:List Gate} {o p j k : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length) (hjlt:j < n+p)
   (hval:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by omega
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;omega
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hndup q hrlt (n+p) (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hndup q hrlt j (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne

lemma q193 {n : ℕ} {gs:List Gate} (hcl:yq n gs) (p : ℕ) :
   ∀ g ∈ gs.drop p,NOk g:=fun g hg => ja hcl g (List.mem_of_mem_drop hg)

open Classical in
lemma q123 (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (hm:MinClean n f gs o) :
   ∀ d p,p+d=gs.length ->
     ∀ tg : ℕ->ℕ,(∀ a ∈ liveList gs n o p,yf n gs f p a (tg a)) ->
       TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f d
         ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
 intro d
 induction d with
 | zero =>
   intro p hp tg _
   have hperm : [o].Perm (liveList gs n o p):=by
     refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
     intro a
     rw [qw,List.mem_singleton]
     constructor
     . rintro rfl;exact ⟨by have:=hm.ho;omega,Or.inl rfl⟩
     . rintro ⟨_,h | ⟨q,hq,g',hg',_,_⟩⟩
       . exact h
       . have:=(List.getElem?_eq_some_iff.1 hg').1;omega
   have hf:val gs n o=f:=funext hm.hev
   have h1:([(f,tg o)]).Perm ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
     rw [← hf];exact hperm.map (fun a => (val gs n a,tg a))
   exact TagRun.perm h1 (TagRun.done (tg o))
 | succ d ih =>
   intro p hp tg hok
   have hplt:p < gs.length:=by omega
   obtain ⟨g,hg⟩:∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hplt⟩
   have hr:wn n gs o (n+p):=hm.hreach p hplt
   have hstep:=q73 n gs o hm.hcl p g hg hr
   have hin:∀ a ∈ g.inputs,a ∈ liveList gs n o p:=fun a ha =>
     (qw _ _ _ _ _).2 ⟨j2 (hm.hcl p g hg) a ha,Or.inr ⟨p,le_rfl,g,hg,ha,hr⟩⟩
   have hnew:∀ a ∈ liveList gs n o p,a≠n+p:=fun a ha =>
     Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
   have hvg:=q103 n gs p g hg (j2 (hm.hcl p g hg))
   have hnd0:=vy gs n o p
   have hdrop:gs.drop p=g::gs.drop (p+1):=by
     rw [List.drop_eq_getElem_cons hplt];have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2;rw [hge]
   have hgn:NOk g:=q101 (hm.hcl p g hg)
   have hdrop_nok:=q193 hm.hcl (p+1)
   have hnz:val gs n (n+p)≠fun _ => false:=hm.hncG p hplt false
   have hno:val gs n (n+p)≠fun _ => true:=hm.hncG p hplt true
   have hnd:∀ a ∈ liveList gs n o p,val gs n a≠val gs n (n+p):=fun a ha e =>
     hm.hndup p hplt a ((qw _ _ _ _ _).1 ha).1 e.symm
   rcases hm.hcl p g hg with ⟨hop,j,hj,hinp⟩ | ⟨hop,j,k,hj,hk,hinp⟩
   ·
     have hjm:j ∈ liveList gs n o p:=hin j (by simp [hinp])
     have hval:val gs n (n+p)=invF (val gs n j):=by
       funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
     have hsave_not:∀ v c B,
         (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
         (v3 n gs v p).1.getD j (Sum.inl false)=Sum.inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
         2<=B /\
         (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c) /\
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (q11 n gs o (p+1) j->3<=B):=by
       intro v c B hncv hget hbd
       have hsucc:=q30 n gs v p g hg
       have hfl:=vb n gs v p (by omega)
       have hfl1:=vb n gs v (p+1) (by omega)
       have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
         rw [hsucc];exact vs n _ g hgn j (by simp [hinp]) c hget
       have hout_c:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c):=by
         rw [hsucc];simp only [qa]
         rw [z2 _ _ _ _ hfl,hop,hinp]
         simp only [lMC,List.map_nil,hget,qg,wr]
       have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
         rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
       have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw [heq_e,h0];omega
       have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
       have hread_np:=zr hm (by omega) hnp_live hncv hout_c
       have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
         (by omega) ⟨!c,hout_c⟩ hread_np
       refine ⟨by omega,hout_c,hbd1,?_⟩
       intro hjlive
       have hj_live1:j ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hjlive⟩
       have hj_c1:(v3 n gs v (p+1)).1.getD j (Sum.inl false)=Sum.inl c:=by
         rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
       have hread_j:=zr hm (by omega) hj_live1 hncv hj_c1
       have hdisj:=q21 hm hplt (fun x => congrFun hval x)
       have hkill2:=k3 n j (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
         hdrop_nok (by omega) (by omega) ⟨c,hj_c1⟩ ⟨!c,hout_c⟩ hread_j hread_np hdisj
       omega
     have ht1:tg j≠1:=by
       intro h1;have hw:=hok j hjm;rw [h1] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 1 hncv hget hbd).1;omega
     have ht2:tg j≠2:=by
       intro h2;have hw:=hok j hjm;rw [h2] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v true 1 hncv hget hbd).1;omega
     have ht3:tg j=3->decide (q11 n gs o (p+1) j)=false:=by
       intro h3;simp only [decide_eq_false_iff_not];intro hjlive
       have hw:=hok j hjm;rw [h3] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 2 hncv hget hbd).2.2.2 hjlive;omega
     set tg' : ℕ->ℕ:=fun a =>
       if a=n+p then (if tg j=3 then 2 else 0)
       else if a=j then 0
       else tg a
     have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
       intro a ha
       simp only [tg']
       by_cases hanp:a=n+p
       . subst hanp;simp only [↓reduceIte]
         by_cases h3:tg j=3
         . simp only [h3,↓reduceIte]
           have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           obtain ⟨_,hout_c,hbd1,_⟩:=hsave_not v false 2 hncv hget hbd
           exact ⟨v,hncv,hout_c,by omega⟩
         . simp only [h3,↓reduceIte];trivial
       . simp only [hanp,↓reduceIte]
         by_cases haj:a=j
         . simp only [haj,↓reduceIte];trivial
         . simp only [haj,↓reduceIte]
           have ha0:a ∈ liveList gs n o p:=by
             rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
             . exact absurd rfl hanp
             . exact h1
           exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
     have IH:=ih (p+1) (by omega) tg' hok'
     have hp1:(liveList gs n o p).Perm (j::(liveList gs n o p).erase j):=List.perm_cons_erase hjm
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
         rw [wa];rintro (⟨_,h⟩ | h)
         . exact hnew j hjm h.symm
         . exact hnew _ (List.mem_of_mem_erase h) rfl
       . intro a
         rw [hstep a,lMM,wa,hnd0.mem_erase_iff,hinp,List.mem_singleton]
         simp only [decide_eq_true_eq]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 haj,haj⟩)
             . exact Or.inr (Or.inr ⟨haj,h1⟩)
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,h2⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨h2,fun h => absurd h h1⟩
     have hmap_rest:((liveList gs n o p).erase j).map (fun a => (val gs n a,tg' a)) =
         ((liveList gs n o p).erase j).map (fun a => (val gs n a,tg a)):=by
       apply List.map_congr_left
       intro a ha
       have h1:a≠j:=(hnd0.mem_erase_iff.1 ha).1
       have h2:a≠n+p:=hnew a (List.mem_of_mem_erase ha)
       simp [tg',h1,h2]
     have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)).map (fun a => (val gs n a,tg' a)) =
         qk (decide (q11 n gs o (p+1) j)) (val gs n j,0) (((liveList gs n o p).erase j).map fun a => (val gs n a,tg a)):=by
       rw [wd,hmap_rest]
       have hjne:j≠n+p:=by omega
       simp [tg',hjne]
     have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
     rw [lMC,hmap_kept,hval] at IH'
     have htgnp:tg' (n+p)=(if tg j=3 then 2 else 0):=by simp [tg']
     rw [htgnp] at IH'
     refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
     refine TagRun.uNot (decide (q11 n gs o (p+1) j)) ht1 ht2 ht3
       (hval ▸ hnz) (hval ▸ hno) (fun e => hnd j hjm (hval ▸ e.symm)) ?_ IH'
     intro x hx
     obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
     exact hval ▸ hnd a (List.mem_of_mem_erase ha)
   ·
     have hjk:j≠k:=by
       intro e;subst e
       apply hm.hndup p hplt j hj
       funext x;rw [hvg x,hinp]
       rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
     have hjm:=hin j (by simp [hinp])
     have hkm:=hin k (by simp [hinp])
     have hke:k ∈ (liveList gs n o p).erase j:=(hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm,hkm⟩
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hnr2:(((liveList gs n o p).erase j).erase k).Nodup:=hnr.erase k
     have hp1:(liveList gs n o p).Perm (j::k::((liveList gs n o p).erase j).erase k) :=
       (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
     have hmr:∀ a,a ∈ ((liveList gs n o p).erase j).erase k ↔ a≠k/\a≠j/\a ∈ liveList gs n o p:=by
       intro a;rw [hnr.mem_erase_iff,hnd0.mem_erase_iff]
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k
             (((liveList gs n o p).erase j).erase k))):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ (q36 _ _ _ hnr2 ?_) ?_⟩
         . rw [wa,wa]
           rintro (⟨_,h⟩ | ⟨_,h⟩ | h)
           . exact hnew j hjm h.symm
           . exact hnew k hkm h.symm
           . exact hnew _ ((hmr _).1 h).2.2 rfl
         . rw [hmr];simp
         . rw [wa,hmr]
           rintro (⟨_,h⟩ | h)
           . exact hjk h
           . exact h.2.1 rfl
       . intro a
         rw [hstep a,lMM,wa,wa,hmr a]
         simp only [decide_eq_true_eq,hinp,lMM,List.not_mem_nil,or_false]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj),haj⟩)
             . by_cases hak:a=k
               . exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak),hak⟩))
               . exact Or.inr (Or.inr (Or.inr ⟨hak,haj,h1⟩))
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,rfl⟩ | ⟨h1,h2,h3⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨hkm,fun _ => h1⟩
           . exact Or.inr ⟨h3,fun h => by rcases h with h | h <;> contradiction⟩
     rcases hop with hop | hop
     ·
       have hval:val gs n (n+p)=meetF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hand_const:∀ (u w_other : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (hval_u:∀ x,val gs n (n+p) x=(val gs n u x&&val gs n w_other x))
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=false ->
             2<=B /\
             (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false /\
             (q11 n gs o (p+1) u->3<=B)) /\
           (c=true->q11 n gs o (p+1) u->2<=B):=by
         intro u wo hu hult hvalu v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hbd1,?_,?_⟩
         . intro hcf;subst hcf
           have hout_f:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ko]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ko]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_f
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hout_f⟩ hread_np
           refine ⟨by omega,hout_f,?_⟩
           intro hulive
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hdisj:=q22 hm hplt hult hvalu
           have hkill2:=k3 n u (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
             hdrop_nok (by omega) (by omega) ⟨false,hu_c1⟩ ⟨false,hout_f⟩ hread_u hread_np hdisj
           omega
         . intro hct hulive;subst hct
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hu_c1⟩ hread_u
           omega
       have hval_j:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x):=fun x => congrFun hval x
       have hval_k:∀ x,val gs n (n+p) x=(val gs n k x&&val gs n j x):=fun x => by
         rw [hval_j x,Bool.and_comm]
       have hta1:tg j≠1:=by
         intro h1;have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const j k (by simp [hinp]) hj hval_j v false 1 hncv hget hbd).2.1 rfl
         omega
       have htb1:tg k≠1:=by
         intro h1;have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const k j (by simp [hinp]) hk hval_k v false 1 hncv hget hbd).2.1 rfl
         omega
       have hta_save:tg j=1\/tg j=2\/tg j=3->decide (q11 n gs o (p+1) j)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hjlive
         rcases h123 with h1 | h2 | h3
         . exact hta1 h1
         . have hw:=hok j hjm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const j k (by simp [hinp]) hj hval_j v true 1 hncv hget hbd).2.2 rfl hjlive;omega
         . have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd).2.1 rfl).2.2 hjlive;omega
       have htb_save:tg k=1\/tg k=2\/tg k=3->decide (q11 n gs o (p+1) k)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hklive
         rcases h123 with h1 | h2 | h3
         . exact htb1 h1
         . have hw:=hok k hkm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const k j (by simp [hinp]) hk hval_k v true 1 hncv hget hbd).2.2 rfl hklive;omega
         . have hw:=hok k hkm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd).2.1 rfl).2.2 hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then (if tg j=3\/tg k=3 then 1 else 0)
         else if a=j\/a=k then 0
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . subst hanp;simp only [↓reduceIte]
           by_cases h3:tg j=3\/tg k=3
           . simp only [h3,↓reduceIte]
             rcases h3 with hj3 | hk3
             . have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
             . have hw:=hok k hkm;rw [hk3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
           . simp only [h3,↓reduceIte];trivial
         . simp only [hanp,↓reduceIte]
           by_cases hajk:a=j\/a=k
           . simp only [hajk,↓reduceIte];trivial
           . simp only [hajk,↓reduceIte]
             have ha0:a ∈ liveList gs n o p:=by
               rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
               . exact absurd rfl hanp
               . exact h1
             exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         simp [tg',hjne,hkne]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=(if tg j=3\/tg k=3 then 1 else 0):=by simp [tg']
       rw [htgnp] at IH'
       have hjle3:=q12 (hok j hjm)
       have hkle3:=q12 (hok k hkm)
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bAnd (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta1 htb1 (fun h => hta_save (by omega)) (fun h => htb_save (by omega))
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
     ·
       have hval:val gs n (n+p)=joinF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hor_const:∀ (u : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c /\
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=true->2<=B) /\
           (c=false->q11 n gs o (p+1) u->2<=B):=by
         intro u hu hult v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hu_c1,hbd1,?_,?_⟩
         . intro hct;subst hct
           have hout_t:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl true:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ji]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ji]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_t
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hout_t⟩ hread_np
           omega
         . intro hcf hulive;subst hcf
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hu_c1⟩ hread_u
           omega
       have hta2:tg j≠2:=by
         intro h2;have hw:=hok j hjm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v true 1 hncv hget hbd).2.2.1 rfl;omega
       have htb2:tg k≠2:=by
         intro h2;have hw:=hok k hkm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v true 1 hncv hget hbd).2.2.1 rfl;omega
       have hta1:tg j=1->decide (q11 n gs o (p+1) j)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hjlive
         have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v false 1 hncv hget hbd).2.2.2 rfl hjlive;omega
       have htb1:tg k=1->decide (q11 n gs o (p+1) k)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hklive
         have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v false 1 hncv hget hbd).2.2.2 rfl hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then 0
         else if a=j then (if tg j=3 then 1 else 0)
         else if a=k then (if tg k=3 then 1 else 0)
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . simp [hanp,yf]
         . simp only [hanp,↓reduceIte]
           by_cases haj:a=j
           . rw [haj];simp only [↓reduceIte]
             by_cases hj3:tg j=3
             . simp only [hj3,↓reduceIte]
               have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hor_const j (by simp [hinp]) hj v false 2 hncv hget hbd
               exact ⟨v,hncv,hh.1,by omega⟩
             . simp only [hj3,↓reduceIte];trivial
           . simp only [haj,↓reduceIte]
             by_cases hak:a=k
             . rw [hak];simp only [↓reduceIte]
               by_cases hk3:tg k=3
               . simp only [hk3,↓reduceIte]
                 have hw:=hok k hkm;rw [hk3] at hw
                 obtain ⟨v,hncv,hget,hbd⟩:=hw
                 have hh:=hor_const k (by simp [hinp]) hk v false 2 hncv hget hbd
                 exact ⟨v,hncv,hh.1,by omega⟩
               . simp only [hk3,↓reduceIte];trivial
             . simp only [hak,↓reduceIte]
               have ha0:a ∈ liveList gs n o p:=by
                 rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
                 . exact absurd rfl hanp
                 . exact h1
               exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,if tg j=3 then 1 else 0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,if tg k=3 then 1 else 0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         have hkj:k≠j:=fun e => hjk e.symm
         simp [tg',hjne,hkne,hkj]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=0:=by simp [tg']
       rw [htgnp] at IH'
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bOr (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta2 htb2 hta1 htb1
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2

lemma q133 {n : ℕ} {gs:List Gate} {o : ℕ} {f:BFn n}
   (hev:∀ x,val gs n o x=f x) (v:Fin n)
   (hdep:∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x) :
   (v : ℕ) ∈ liveList gs n o 0:=by
 rw [qw]
 refine ⟨by omega,?_⟩
 by_contra hnl
 have hnr : ¬ wn n gs o (v : ℕ):=by
   intro hr
   rcases q66 hr with heq | ⟨q,g,hg,hin,hrq⟩
   . exact hnl (Or.inl heq)
   . exact hnl (Or.inr ⟨q,nZL q,g,hg,hin,hrq⟩)
 obtain ⟨x,hx⟩:=hdep
 apply hx
 rw [← hev,← hev]
 have hagree:∀ (p : ℕ),∀ i < n+p,wn n gs o i ->
     (q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).getD i false =
     (q3 (gs.take p) (List.ofFn x)).getD i false:=by
   intro p
   induction p with
   | zero =>
     intro i hi hr
     simp only [List.take_zero,q3,List.foldl_nil]
     have hlt:i < n:=by omega
     have hne:(⟨i,hlt⟩:Fin n)≠v:=fun e => hnr (by simpa [← e] using hr)
     simp [hlt,fUN hne]
   | succ p ih =>
     intro i hi hr
     by_cases hp:p < gs.length
     . have htake:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem hp
       rw [htake,zd,zd]
       have hlen1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       have hlen2:(q3 (gs.take p) (List.ofFn x)).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       by_cases hip:i=n+p
       . subst hip
         show (q3 (gs.take p) _++[_]).getD (n+p) false=(q3 (gs.take p) _++[_]).getD (n+p) false
         rw [z2 _ _ _ _ hlen1,z2 _ _ _ _ hlen2]
         congr 1
         apply List.map_congr_left
         intro a ha
         have hra:wn n gs o a:=q33 (List.getElem?_eq_getElem hp) hr ha
         by_cases halt:a < n+p
         . exact ih a halt hra
         . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
       . show (q3 (gs.take p) _++[_]).getD i false=(q3 (gs.take p) _++[_]).getD i false
         rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
         exact ih i (by omega) hr
     . have htake:gs.take (p+1)=gs.take p:=by
         rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
       rw [htake]
       by_cases hlt:i < n+p
       . exact ih i hlt hr
       . have hl1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         have hl2:(q3 (gs.take p) (List.ofFn x)).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         rw [lGD _ _ (by omega),lGD _ _ (by omega)]
 have ho_lt:o < n+gs.length:=by
   by_contra hge
   have hfalse:∀ y:Fin n->Bool,val gs n o y=false:=fun y =>
     lGD _ _ (by rw [qu];simp;omega)
   exact hx (by rw [← hev,← hev,hfalse,hfalse])
 have h:=hagree gs.length o ho_lt (q34 n gs o)
 rw [List.take_length] at h
 exact h

open Classical in
lemma q88 {n : ℕ} (f:BFn n) (cap : ℕ) (initTags:Fin n->ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (hdep:∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s'))
   (s : ℕ) (hs:s<=cap) (hc:HasCircuitSize n f s) :
   ∃ s',s'<=cap /\
     TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s'
       (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)):=by
 obtain ⟨gs,o,hm,hlen⟩:=q56 n f s hnc hc
 have hlive0:liveList gs n o 0=List.range n:=by
   have hsub:=(List.filter_sublist (l:=List.range (n+0)) (p:=fun a => decide (q11 n gs o 0 a)))
   simp only [nAZ] at hsub
   refine List.Sublist.eq_of_length hsub ?_
   have hperm:(List.range n).Perm (liveList gs n o 0):=by
     refine (List.perm_ext_iff_of_nodup List.nodup_range (vy gs n o 0)).2 ?_
     intro a
     rw [List.mem_range]
     constructor
     . intro ha;exact q133 hm.hev ⟨a,ha⟩ (hdep ⟨a,ha⟩)
     . intro ha;exact by simpa using ((qw gs n o 0 a).1 ha).1
   exact hperm.length_eq.symm
 set tg : ℕ->ℕ:=fun a => if h:a < n then initTags ⟨a,h⟩ else 0
 have hok0:∀ a ∈ liveList gs n o 0,yf n gs f 0 a (tg a):=by
   intro a ha
   rw [hlive0,List.mem_range] at ha
   have hta:tg a=initTags ⟨a,ha⟩:=by simp [tg,ha]
   rw [hta]
   rcases htag ⟨a,ha⟩ with h0 | ⟨h1,hnc0,hlb⟩ | ⟨h3,hnc0,hlb⟩
   . rw [h0];trivial
   . rw [h1]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 1) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
   . rw [h3]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 2) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
 have htr:=q123 n f gs o hm gs.length 0 (by omega) tg hok0
 refine ⟨gs.length,by omega,?_⟩
 have heq:(liveList gs n o 0).map (fun a => (val gs n a,tg a)) =
     List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i):=by
   rw [hlive0]
   apply List.ext_getElem
   . simp
   . intro i h1 h2
     have hi:i < n:=by simpa using h2
     simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
     exact Prod.ext (q172 gs n ⟨i,hi⟩) (by simp [tg,hi])
 rw [← heq]
 exact htr

def zm {α:Type} (x:Nat) (f:Nat->α) : α :=
 match x with
 | 0 => f 0
 | n+1 => f (Nat.succ n)

lemma v5 {α:Type} (x:Nat) (f:Nat->α):zm x f=f x:=by
 cases x <;> rfl

structure Cfg where
 k:Nat
 sh0:Nat
 sh1:Nat
 shTT:Nat
 all1v:Nat
 goalv:Nat
 lok:Nat
 m0all:Nat
 m0:Nat
 a29_0:Nat
 b5_0:Nat
 m1:Nat
 m12:Nat
 a29_1:Nat
 b5_1:Nat

def q76 (sw:Nat × Nat × Nat × Nat) (w:Nat):Nat :=
 let (d,m01,m10,mEq):=sw
 Nat.lor (Nat.lor (Nat.land w mEq) (Nat.shiftRight (Nat.land w m01) d))
         (Nat.shiftLeft (Nat.land w m10) d)

def ym:List (Nat × Nat × Nat × Nat)->Nat->Nat
 | [],w => w
 | sw::rest,w => ym rest (q76 sw w)

def q72 (sh:Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (Nat.shiftRight w sh) fun v => (v,tg)::q72 sh rest

def wx (g:List (Nat × Nat × Nat × Nat)):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (ym g w) fun v => (v,tg)::wx g rest

def M128:Nat:=0x9e3779b97f4a7c15f39cc0605cedc835

def q211:Nat:=0x517cc1b727220a95b3650d1e9a87c3f1

def q210:Nat:=0xbf58476d1ce4e5b994d049bb133111eb

def q209:Nat:=0x2545f4914f6cdd1d6c62272e07bb0142

def q208 (salt w tg:Nat):Nat :=
 let s:=match tg with
   | 0 => salt
   | 1 => Nat.xor salt q211
   | 2 => Nat.xor salt q210
   | _ => Nat.xor salt q209
 zm (Nat.xor (Nat.xor w (Nat.shiftRight w 61)) s) fun x =>
 Nat.shiftRight (Nat.mul x (Nat.xor x M128)) 104

def q199 (salt:Nat):Nat->List (Nat × Nat)->Nat
 | acc,[] => acc
 | acc,(w,tg)::rest => zm (Nat.add acc (q208 salt w tg)) fun acc' => q199 salt acc' rest

def q75 (salt:Nat) (ws:List (Nat × Nat)):Nat:=Nat.land (q199 salt 0 ws) 0xFFFFFF

def q205 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 24 i)) 0xFFFFFF

def q192 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 32 i)) 0xFFFFFFFF

def q167 (T h:Nat):Nat->Nat->Nat->Nat
 | 0,lo,_ => lo
 | fuel+1,lo,hi =>
   if Nat.ble (Nat.add lo 2) hi then
     zm (Nat.div (Nat.add lo hi) 2) fun mid =>
     if Nat.ble (q205 T mid) h then q167 T h fuel mid hi else q167 T h fuel lo mid
   else lo

def q85 (NN FL HT:Nat->Nat) (s h:Nat):Nat :=
 let n:=NN s
 if Nat.beq n 0 then 999999
 else
   let ht:=HT s
   zm (q167 ht h (FL s) 0 n) fun j =>
   if Nat.beq (q205 ht j) h then j else 999999

def twEq (a b:Nat × Nat):Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2

def jy (x:Nat × Nat):List (Nat × Nat)->Option (List (Nat × Nat))
 | [] => none
 | a::rest =>
   if twEq x a then some rest
   else match jy x rest with
     | none => none
     | some r => some (a::r)

def jk:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],[] => true
 | a::as,bs => match jy a bs with
   | none => false
   | some bs' => jk as bs'
 | _,_ => false

def twLt (a b:Nat × Nat):Bool :=
 if Nat.beq a.1 b.1 then Nat.blt a.2 b.2 else Nat.blt a.1 b.1

def q62 (x:Nat × Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => [x]
 | a::rest => if twLt x a then x::a::rest else a::q62 x rest

def q125:List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | a::rest => q62 a (q125 rest)

def q158:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],_ => false
 | _,[] => false
 | a::as,b::bs =>
   if twEq a b then q158 as bs else twLt a b

def q69 (g:List (Nat × Nat × Nat × Nat)) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let ws':=q125 (wx g ws)
 if q158 ws' ws then ws' else ws

def q35:List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->List (Nat × Nat)
 | [],ws => ws
 | g::rest,ws => q35 rest (q69 g ws)

def q186 (gens:List (List (Nat × Nat × Nat × Nat))) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let s0:=q125 ws
 match gens with
 | [] => s0
 | [g] => q69 g s0
 | _ => q35 gens (q35 gens s0)

def qi (m0 w0:Nat):Nat :=
 zm (Nat.land w0 m0) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m0) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m0) fun c =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 3) m0)) fun nd =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 4) m0)) fun ne =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 5) m0)) fun nf =>
 Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
         (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))

def yg (sh1 m1 m12 w:Nat):Nat :=
 zm (Nat.shiftRight w sh1) fun w0 =>
 zm (Nat.land w0 m1) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m1) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m1) fun c =>
 zm (Nat.land (Nat.shiftRight w0 3) m1) fun d =>
 zm (Nat.land (Nat.shiftRight w0 4) m1) fun e =>
 zm (Nat.land (Nat.shiftRight w0 5) m1) fun f =>
 zm (Nat.xor m1 d) fun nd =>
 zm (Nat.xor m1 e) fun ne =>
 zm (Nat.xor m1 f) fun nf =>
 zm (Nat.xor m1 a) fun na =>
 zm (Nat.xor m1 b) fun nb =>
 zm (Nat.xor m1 c) fun nc =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))) fun v1 =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))) fun v2 =>
 zm (Nat.lor v1 v2) fun u =>
 zm (Nat.land u m12) fun hi =>
 Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                     (Nat.land (Nat.land u m1) (Nat.xor m1 (Nat.shiftRight hi 1))))

inductive PList where
 | nil:PList
 | cons (w tg alo ahi nahi cw uw a0 v0w v1w postC postU postV0 postV1:Nat) (tail:PList):PList

def kt (c:Cfg):List (Nat × Nat)->Nat × Nat × Nat × Nat × PList
 | [] => (0,0,0,0,PList.nil)
 | (w,tg)::rest =>
   let (pC,pU,pV0,pV1,tl):=kt c rest
   let alo:=Nat.land w c.lok
   let ahi:=Nat.land (Nat.shiftRight w c.k) c.lok
   let nahi:=Nat.xor c.lok ahi
   let cw:=Nat.xor alo ahi
   let uw:=Nat.land cw ahi
   let a0:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
   let v0w:=qi c.m0 a0
   let v1w:=yg c.sh1 c.m1 c.m12 w
   (Nat.lor cw pC,Nat.lor uw pU,Nat.add v0w pV0,Nat.add v1w pV1,
    PList.cons w tg alo ahi nahi cw uw a0 v0w v1w pC pU pV0 pV1 tl)

def q164:List (Nat × Nat)->Nat
 | [] => 0
 | _::rest => Nat.add 1 (q164 rest)

def yz (x:Nat):List (Nat × Nat)->Bool
 | [] => false
 | (a,_)::rest => if Nat.beq x a then true else yz x rest

def qx:List (Nat × Nat)->List (Nat × Nat)->List (Nat × Nat)
 | [],ys => ys
 | a::xs,ys => qx xs (a::ys)

def pToList:PList->List (Nat × Nat)
 | PList.nil => []
 | PList.cons w tg _ _ _ _ _ _ _ _ _ _ _ _ tl => (w,tg)::pToList tl

def qj (all1v:Nat) (ws:List (Nat × Nat)) (w:Nat):Bool :=
 !(Nat.beq w 0)&&!(Nat.beq w all1v)&&!(yz w ws)

def qb (c:Cfg) (v0Acc v0w:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add (Nat.add v0Acc v0w) c.a29_0) c.b5_0) c.b5_0

def z3 (c:Cfg) (v1Tot:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add v1Tot c.a29_1) c.b5_1) c.b5_1

def ke (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     Nat.beq (Nat.land missU (Nat.lor alo blo)) 0 &&
     qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.lor a0 b0)) &&
     (let w:=Nat.lor a b;qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       Nat.beq (Nat.land missU (Nat.lor nahi nbhi)) 0 &&
       qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.land a0 b0)) &&
       (let w:=Nat.land a b;let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0;
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))))
     if andHit then true
     else ke c ws onSurv a ta alo nahi a0 pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post

def q98 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if ke c ws onSurv a ta alo nahi a0 pre preU preV0 [] suf then true
   else q98 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf

def vx (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0 v0a:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if okOrB&&qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else if okOrB&&!(Nat.beq tb 1) then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w &&
         onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if okAndB&&qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else if okAndB&&Nat.beq tb 0 then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w &&
           onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else false
     if andHit then true
     else vx c ws onSurv a ta alo nahi a0 v0a pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post

def js (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if vx c ws onSurv a ta alo nahi a0 v0a pre preU preV0 [] suf then true
   else js c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf

def we (c:Cfg) (ws:List (Nat × Nat))
   (a ta alo nahi a0 v0a:Nat):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | pmU,pmV0,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         (okOrB&&qj c.all1v ws w) ||
         (!(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
         (!(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
       else if okOrB&&!(Nat.beq tb 1) then
         qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws (Nat.lor a b)
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           (okAndB&&qj c.all1v ws w) ||
           (Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
           (Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
         else if okAndB&&Nat.beq tb 0 then
           qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws (Nat.land a b)
         else false
     if andHit then true
     else we c ws a ta alo nahi a0 v0a (Nat.lor pmU ub) (Nat.add pmV0 v0b) post

def q26 (c:Cfg) (ws:List (Nat × Nat)):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | preU,preV0,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if we c ws a ta alo nahi a0 v0a preU preV0 suf then true
   else q26 c ws (Nat.lor preU ua) (Nat.add preV0 v0a) suf

def w7 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ _ cw ua a0 v0a _ _ postU postV0 _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let uw:=Nat.land cw alo;
      Nat.beq (Nat.lor (Nat.lor preU postU) uw) c.lok &&
      qb c (Nat.add preV0 postV0) (qi c.m0 (Nat.xor a0 c.m0all)) &&
      (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
       qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))))
   if hit then true
   else w7 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf

def kd (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi a0 v0a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | pmC,pmU,pmV0,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
            qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else
         Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
         qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post)))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
              qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else
           Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
           qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post)))
     if andHit then true
     else kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV0 v0b) (Nat.add pmV1 v1b) ((b,tb)::mid) post

def q96 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 v0a v1a _ _ _ _ suf =>
   if kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre preC preU preV0 preV1 [] suf then true
   else q96 c ws hasUp onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf

def w6 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo _ _ ca ua a0 v0a v1a postC postU postV0 postV1 suf =>
   let hit :=
     if Nat.beq ta 1||Nat.beq ta 2 then false
     else
       let w:=Nat.xor a c.all1v
       let wt:=if Nat.beq ta 3 then 2 else 0
       let uw:=Nat.land ca alo
       let rC:=Nat.lor preC postC
       let rU:=Nat.lor preU postU
       let rV0:=Nat.add preV0 postV0
       let rV1:=Nat.add preV1 postV1
       (Nat.beq (Nat.lor rC ca) c.lok &&
        (Nat.beq (Nat.lor rU uw) c.lok||z3 c (Nat.add rV1 v1a)) &&
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&Nat.beq (Nat.lor rU ca) c.lok &&
        qb c (Nat.add rV0 v0a) (qi c.m0 (Nat.xor a0 c.m0all)) &&
        qj c.all1v ws w&&onSurv ((w,0)::(a,0)::qx pre (pToList suf)))
   if hit then true
   else w6 c ws onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf

def kc (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi ca a0 v1a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | pmC,pmU,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 _ v1b postC postU _ postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       let v1w:=yg c.sh1 c.m1 c.m12 w
       let ta':=if Nat.beq ta 3 then 1 else 0
       let tb':=if Nat.beq tb 3 then 1 else 0
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest)) ||
         (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&qb c totV0 (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))
       else
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         let v1w:=yg c.sh1 c.m1 c.m12 w
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest)) ||
           (Nat.beq ta 0&&Nat.beq tb 0&&qb c totV0 (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::ws))
         else
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest))
     if andHit then true
     else kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV1 v1b) ((b,tb)::mid) post

def q94 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | preC,preU,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 _ v1a _ _ _ _ suf =>
   if kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre preC preU preV1 [] suf then true
   else q94 c ws hasUp totV0 onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV1 v1a) ((a,ta)::pre) suf

def w5 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta _ _ _ ca _ _ _ _ postC _ _ _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor (Nat.lor preC postC) ca) c.lok&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&onSurv ((w,0)::ws))))
   if hit then true
   else w5 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf

def k9 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi ca:Nat) (pre:List (Nat × Nat)):Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | pmC,mid,PList.cons b tb blo bhi _ cb _ _ _ _ postC _ _ _ post =>
   let rC:=Nat.lor pmC postC
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     (let w:=Nat.lor a b
      let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
      let ta':=if Nat.beq ta 3 then 1 else 0
      let tb':=if Nat.beq tb 3 then 1 else 0
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,0)::rest)) ||
       (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,0)::(a,ta')::rest)) ||
       (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,0)::(b,tb')::rest)) ||
       (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       (let w:=Nat.land a b
        let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
        let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
        qj c.all1v ws w &&
        ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,wt)::rest)) ||
         (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,wt)::(a,0)::rest)) ||
         (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,wt)::(b,0)::rest)) ||
         (Nat.beq ta 0&&Nat.beq tb 0&&onSurv ((w,0)::ws))))
     if andHit then true
     else k9 c ws onSurv a ta alo ahi ca pre (Nat.lor pmC cb) ((b,tb)::mid) post

def q92 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta alo ahi _ ca _ _ _ _ _ _ _ _ suf =>
   if k9 c ws onSurv a ta alo ahi ca pre preC [] suf then true
   else q92 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf

def j6 (c:Cfg) (ws:List (Nat × Nat)):Bool :=
 match ws with
 | [(a,_)] => Nat.beq (Nat.xor a c.all1v) c.goalv
 | [(a,_),(b,_)] => Nat.beq (Nat.lor a b) c.goalv||Nat.beq (Nat.land a b) c.goalv
 | _ => false

def scanAll (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws onSurv 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws onSurv 0 0 [] pl||q96 c ws hasUp onSurv 0 0 0 0 [] pl
     else hasUp&&js c ws onSurv 0 0 [] pl
   | 2 => w6 c ws onSurv 0 0 0 0 [] pl||q94 c ws hasUp totV0 onSurv 0 0 0 [] pl
   | _ => w5 c ws onSurv 0 [] pl||q92 c ws onSurv 0 [] pl

def scanInline (c:Cfg) (s:Nat) (ws:List (Nat × Nat)):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws (fun _ => true) 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws (fun _ => true) 0 0 [] pl||q96 c ws hasUp (fun _ => true) 0 0 0 0 [] pl
     else hasUp&&q26 c ws 0 0 pl
   | 2 => w6 c ws (fun _ => true) 0 0 0 0 [] pl||q94 c ws hasUp totV0 (fun _ => true) 0 0 0 [] pl
   | _ => w5 c ws (fun _ => true) 0 [] pl||q92 c ws (fun _ => true) 0 [] pl

def q42 (pid:Nat):Nat->Nat->Nat × Nat
 | 0,j => (0,j)
 | fuel+1,j =>
   let t:=Nat.div (Nat.mul (Nat.add j 1) j) 2
   if Nat.ble t pid then q42 pid fuel (Nat.add j 1)
   else (Nat.sub pid (Nat.div (Nat.mul j (Nat.sub j 1)) 2),j)

def jw:Nat->List (Nat × Nat)->Nat × Nat
 | _,[] => (0,0)
 | 0,a::_ => a
 | k+1,_::rest => jw k rest

def q38:Nat->List (Nat × Nat)->List (Nat × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::q38 k rest

def q203 (all1v code:Nat) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 if Nat.ble code 32 then
   zm (Nat.sub code 1) fun c =>
   zm (Nat.shiftRight c 1) fun i =>
   let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=jw i ws
   let wt:=if Nat.beq ta 3 then 2 else 0
   zm (Nat.xor a all1v) fun w =>
   let r:=q38 i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   zm (Nat.sub code 33) fun rem =>
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=jw i ws
   let (b,tb):=jw j ws
   let r:=q38 i (q38 j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     zm (Nat.land a b) fun w =>
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (w,wt)::r2
   else
     zm (Nat.lor a b) fun w =>
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (w,0)::r2

def q120 (all1v:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (Nat × Nat)
 | 0,_,_ => xs
 | d+1,s,j =>
   zm (q192 (PT s) j) fun e =>
   zm (Nat.land e 1023) fun code =>
   if Nat.beq code 0 then xs
   else zm (Nat.land (Nat.shiftRight e 10) 8191) fun pidx =>
     q203 all1v code (q120 all1v xs PT d (Nat.add s 1) pidx)

def Rgen (all1v cap:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat) (s j:Nat):List (Nat × Nat) :=
 q120 all1v xs PT (Nat.sub cap s) s j

def findAutGen (shTT salt:Nat) (gens:List (List (Nat × Nat × Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT PT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let zsc:=q186 gens (q72 shTT zs)
 zm (q75 salt zsc) fun h =>
 zm (q85 NN FL HT s h) fun j =>
 if Nat.beq j 999999 then false
 else
   zm (Nat.shiftRight (q192 (PT s) j) 23) fun aidx =>
   jk zsc (wx (aut aidx) (Rtt s j))

def bar (cfg:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (R:Nat->Nat->List (Nat × Nat)):Nat->Nat->Bool
 | 0,i => match R 0 i with
   | [(w,_)] => !(Nat.beq w cfg.goalv)
   | _ => true
 | s+1,i =>
   let ws:=R (Nat.add s 1) i
   !(scanAll cfg s ws fun zs =>
       !(findFn s zs)&&(Nat.beq s 0||scanInline cfg (Nat.sub s 1) zs))

def span (f:Nat->Bool):Nat->Nat->Bool
 | 0,_ => true
 | n+1,i => f i&&span f n (Nat.add i 1)

def q1 (n r:Nat):Fin n->Bool:=fun i => r.testBit i.val

def q146 {n:Nat} (x:Fin n->Bool):Nat :=
 (List.finRange n).foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0

lemma qp {m:Nat} (hm:m≠0):(1:Nat).testBit m=false:=by
 cases m with
 | zero => contradiction
 | succ k => simp [Nat.testBit_succ]

lemma z7 {x m:Nat} (h:x.testBit m=true) :
   (x / 2 ^ m) % 2=1:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 exact of_decide_eq_true h

lemma z5 {x m:Nat} (h:x.testBit m=false) :
   (x / 2 ^ m) % 2=0:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 have:=of_decide_eq_false h
 omega

lemma zg {x m:Nat} (h:x.testBit m=true) : 2 ^ m<=x:=by
 have h1:=z7 h
 have h2 : 1<=x / 2 ^ m:=by generalize x / 2 ^ m=q at h1 ⊢;omega
 have h3:=Nat.mul_le_mul_right (2 ^ m) h2
 have h4:=Nat.div_mul_le_self x (2 ^ m)
 omega

lemma vz {y m:Nat} (h:y.testBit m=false) :
   y % 2 ^ (m+1) < 2 ^ m:=by
 have h0:(y / 2 ^ m) % 2=0:=z5 h
 have h1:y % 2 ^ (m+1) / 2 ^ m=(y / 2 ^ m) % 2:=by
   rw [Nat.pow_succ,Nat.mod_mul_right_div_self]
 have h2:y % 2 ^ (m+1) / 2 ^ m=0:=by rw [h1,h0]
 exact (Nat.div_eq_zero_iff.1 h2).resolve_left (Nat.ne_of_gt (n2P m))

lemma vk {y m:Nat} (h:y.testBit m=false) (k:Nat) :
   (y+2 ^ m).testBit k=if k=m then true else y.testBit k:=by
 by_cases hkm:k=m
 . subst hkm
   have h0:=z5 h
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.add_div_right _ (n2P k)]
   simp;omega
 . simp only [hkm,↓reduceIte]
   by_cases hlt:k < m
   . have hdv : 2 ^ m=2 ^ k*2 ^ (m - k):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hlt)]
     have hge : 1<=m - k:=by omega
     have hev : 2 ^ (m - k) % 2=0:=by
       obtain ⟨q,hq⟩:=Nat.exists_eq_add_of_le' hge
       rw [hq,Nat.pow_succ];omega
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hdv,
         Nat.mul_comm (2 ^ k),Nat.add_mul_div_right _ _ (n2P k)]
     have:(y / 2 ^ k+2 ^ (m - k)) % 2=(y / 2 ^ k) % 2:=by omega
     rw [this]
   . have hge:m+1<=k:=by omega
     have hrem:y % 2 ^ (m+1)+2 ^ m < 2 ^ (m+1):=by
       have hltm:=vz h
       have hpw : 2 ^ (m+1)=2 ^ m*2:=Nat.pow_succ 2 m
       omega
     have hdiv1:(y+2 ^ m) / 2 ^ (m+1)=y / 2 ^ (m+1):=by
       have hd:y=2 ^ (m+1)*(y / 2 ^ (m+1))+y % 2 ^ (m+1) :=
         (Nat.div_add_mod y (2 ^ (m+1))).symm
       conv_lhs => rw [hd,nAA]
       rw [Nat.mul_add_div (n2P (m+1)),Nat.div_eq_of_lt hrem,nAZ]
     have hpow : 2 ^ k=2 ^ (m+1)*2 ^ (k - (m+1)):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' hge]
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hpow,
         ← Nat.div_div_eq_div_mul,← Nat.div_div_eq_div_mul,hdiv1]

lemma qs {y m:Nat} (h:y.testBit m=false) :
   y+2 ^ m=y^^^2 ^ m:=by
 apply nEQ;intro k
 rw [vk h,nTX,Nat.testBit_two_pow]
 by_cases hkm:k=m
 . subst hkm;simp [h]
 . simp [hkm,Ne.symm hkm]

lemma jl {n:Nat} (x:Fin n->Bool) (k:Nat) :
   (q146 x).testBit k=if h:k < n then x ⟨k,h⟩ else false:=by
 have hgen:∀ (l:List (Fin n)),l.Nodup ->
     (l.foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0).testBit k =
     if h:k < n then (if ⟨k,h⟩ ∈ l then x ⟨k,h⟩ else false) else false:=by
   intro l hnd
   induction l with
   | nil => simp
   | cons a t ih =>
     obtain ⟨hat,hndt⟩:=List.nodup_cons.1 hnd
     simp only [lFC]
     have iht:=ih hndt
     by_cases hxa:x a=true
     . simp only [hxa,↓reduceIte,nTO,Nat.testBit_shiftLeft,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . subst heq;simp [hxa]
         . have hne:k≠a.val:=fun e => heq (Fin.ext e)
           have h0:(decide (a.val<=k)&&(1:Nat).testBit (k - a.val))=false:=by
             cases hle:decide (a.val<=k)
             . simp
             . have hle':a.val<=k:=of_decide_eq_true hle
               simp [qp (by omega:k - a.val≠0)]
           simp [heq,h0]
       . have hne:a.val < k:=by omega
         simp [hk,qp (by omega:k - a.val≠0)]
     . simp only [hxa,bFT,↓reduceIte,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . rw [heq];simp [hat,hxa]
         . simp [heq]
       . simp [hk]
 have h:=hgen (List.finRange n) (List.nodup_finRange n)
 simpa [q146,List.mem_finRange] using h

lemma q178 {n:Nat} (x:Fin n->Bool):q146 x < 2 ^ n:=by
 apply Nat.lt_pow_two_of_testBit
 intro k hk
 rw [jl]
 simp [show ¬ k < n by omega]

lemma q57 {n:Nat} (x:Fin n->Bool):q1 n (q146 x)=x:=by
 funext i
 simp [q1,jl,i.isLt]

def encL {n:Nat} (rows:List Nat) (f:BFn n):Nat :=
 rows.foldr (fun r acc => acc*2+if f (q1 n r) then 1 else 0) 0

def encTT (n:Nat) (f:BFn n):Nat:=encL (List.range (2 ^ n)) f

lemma z8 {n:Nat} (rows:List Nat) (f:BFn n) (i:Nat) :
   (encL rows f).testBit i=match rows[i]? with | some r => f (q1 n r) | none => false:=by
 induction rows generalizing i with
 | nil => simp [encL]
 | cons r rest ih =>
   have hcons:encL (r::rest) f=encL rest f*2+if f (q1 n r) then 1 else 0:=rfl
   rw [hcons]
   cases i with
   | zero =>
     cases h:f (q1 n r) <;> simp [h,Nat.testBit_zero]
   | succ k =>
     rw [Nat.testBit_succ]
     have hd:(encL rest f*2+if f (q1 n r) then 1 else 0) / 2=encL rest f:=by
       cases h:f (q1 n r) <;> simp only [h,↓reduceIte,bFT] <;> omega
     rw [hd]
     exact ih k

lemma q39 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => false)=0:=by
 apply nEQ;intro i
 rw [z8];cases rows[i]? <;> simp

lemma q177 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => true)=2 ^ rows.length - 1:=by
 apply nEQ;intro i
 rw [z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]

lemma q160 {n:Nat} (rows:List Nat) (f:BFn n) :
   encL rows (invF f)=Nat.xor (encL rows f) (2 ^ rows.length - 1):=by
 apply nEQ;intro i
 rw [nXO,nTX,z8,z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi,invF]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]

lemma q143 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (meetF f g)=Nat.land (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLA,nTA,z8,z8,z8]
 cases rows[i]? <;> simp [meetF]

lemma q144 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (joinF f g)=Nat.lor (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLO,nTO,z8,z8,z8]
 cases rows[i]? <;> simp [joinF]

lemma vr {n:Nat} (f:BFn n) (r:Nat) :
   (encTT n f).testBit r=if r < 2 ^ n then f (q1 n r) else false:=by
 unfold encTT;rw [z8]
 by_cases hr:r < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]

lemma yc {n:Nat}:Function.Injective (encTT n):=by
 intro f g h
 funext x
 have h1:=congrArg (fun m => m.testBit (q146 x)) h
 rw [vr,vr] at h1
 simp only [q178 x,↓reduceIte,q57] at h1
 exact h1

lemma q116 {n:Nat} (pre:List Nat) (f:BFn n) :
   Nat.shiftRight (encL (pre++List.range (2 ^ n)) f) pre.length=encTT n f:=by
 apply nEQ;intro i
 change ((encL (pre++List.range (2 ^ n)) f) >>> pre.length).testBit i=(encTT n f).testBit i
 rw [Nat.shiftRight_eq_div_pow,Nat.testBit_div_two_pow,z8,vr]
 rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel]
 by_cases hi:i < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hi])];simp [hi]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hi]

lemma q89 {n:Nat} (pre:List Nat) :
   Function.Injective (encL (n:=n) (pre++List.range (2 ^ n))):=by
 intro f g h
 apply yc
 rw [← q116 pre f,← q116 pre g,h]

def yh {n:Nat} (i j:Fin n) (x:Fin n->Bool):Fin n->Bool :=
 fun k => x (if k=i then j else if k=j then i else k)

lemma q104 {n:Nat} (i j:Fin n) (x:Fin n->Bool) :
   yh i j (yh i j x)=x:=by
 funext k;unfold yh
 by_cases h1:k=i
 . rw [h1];by_cases h2:j=i <;> simp [h2]
 . by_cases h2:k=j
   . rw [h2];simp [Ne.symm h1]
   . simp [h1,h2]

def yu (i j r:Nat):Nat :=
 let bi:=r.testBit i
 let bj:=r.testBit j
 if bi==bj then r else Nat.xor r (Nat.lor (1 <<< i) (1 <<< j))

lemma q162 {n i j r:Nat} (hi:i < n) (hj:j < n) (hr:r < 2 ^ n) :
   yu i j r < 2 ^ n:=by
 unfold yu;dsimp only
 split
 . exact hr
 . apply Nat.lt_pow_two_of_testBit
   intro k hk
   rw [nXO,nTX,nLO,nTO,
       Nat.testBit_shiftLeft,Nat.testBit_shiftLeft]
   have hr0:r.testBit k=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hk))
   simp [hr0,qp (by omega:k - i≠0),qp (by omega:k - j≠0)]

lemma z9 {n i j r:Nat} (hi:i < n) (hj:j < n) :
   q1 n (yu i j r)=yh ⟨i,hi⟩ ⟨j,hj⟩ (q1 n r):=by
 funext k
 simp only [q1,yh,yu]
 by_cases heq:r.testBit i=r.testBit j
 . simp only [heq,beq_self_eq_true,↓reduceIte]
   by_cases hki:k=⟨i,hi⟩
   . rw [hki];simp [heq]
   . by_cases hkj:k=⟨j,hj⟩
     . rw [hkj];split <;> simp [heq]
     . simp [hki,hkj]
 . have hbeq:(r.testBit i==r.testBit j)=false:=beq_false_of_ne heq
   simp only [hbeq,bFT,↓reduceIte,nXO,nTX,nLO,
     nTO,Nat.testBit_shiftLeft]
   by_cases hki:k=⟨i,hi⟩
   . subst hki
     simp only [↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
     cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
   . by_cases hkj:k=⟨j,hj⟩
     . subst hkj
       simp only [hki,↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
       cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
     . have h1:k.val≠i:=fun e => hki (Fin.ext e)
       have h2:k.val≠j:=fun e => hkj (Fin.ext e)
       have hb:∀ m,k.val≠m->(decide (m<=k.val)&&(1:Nat).testBit (k.val - m))=false:=by
         intro m hne
         cases hle:decide (m<=k.val)
         . simp
         . have hle':m<=k.val:=of_decide_eq_true hle
           simp [qp (by omega:k.val - m≠0)]
       simp [hki,hkj,hb i h1,hb j h2]

def w9 (n i j:Nat):Nat × Nat × Nat × Nat :=
 let d:=2 ^ j - 2 ^ i
 let N:=2 ^ n
 let m01:=(List.range N).foldr (fun x acc => acc*2+if !(x.testBit i)&&x.testBit j then 1 else 0) 0
 let m10:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i&&!(x.testBit j) then 1 else 0) 0
 let mEq:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i==x.testBit j then 1 else 0) 0
 (d,m01,m10,mEq)

lemma jx (N:Nat) (P:Nat->Bool) (r:Nat) :
   ((List.range N).foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
   if r < N then P r else false:=by
 have hgen:∀ (l:List Nat) (r:Nat),
     (l.foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
     match l[r]? with | some x => P x | none => false:=by
   intro l
   induction l with
   | nil => intro r;simp
   | cons a t ih =>
     intro r;simp only [lFC]
     cases r with
     | zero => cases h:P a <;> simp [h,Nat.testBit_zero]
     | succ k =>
       rw [Nat.testBit_succ]
       have hd:((t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0)*2+if P a then 1 else 0) / 2
           = t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0:=by
         cases P a <;> simp only [↓reduceIte,bFT] <;> omega
       rw [hd];exact ih k
 rw [hgen]
 by_cases hr:r < N
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]

lemma j3 {n i j:Nat} (hij:i < j) (hjn:j < n) (g:BFn n) :
   q76 (w9 n i j) (encTT n g) =
     encTT n (fun x => g (yh ⟨i,by omega⟩ ⟨j,hjn⟩ x)):=by
 have hi:i < n:=by omega
 have hpow : 2 ^ i < 2 ^ j:=Nat.pow_lt_pow_right (by omega) hij
 have hsub_bit:∀ x m,x.testBit m=true->x - 2 ^ m+2 ^ m=x/\(x - 2 ^ m).testBit m=false:=by
   intro x m hm
   have hle : 2 ^ m<=x:=zg hm
   refine ⟨Nat.sub_add_cancel hle,?_⟩
   rw [Nat.testBit_eq_decide_div_mod_eq]
   have hd:(x - 2 ^ m) / 2 ^ m=x / 2 ^ m - 1:=by
     have h1:x=(x - 2 ^ m)+2 ^ m:=(Nat.sub_add_cancel hle).symm
     have h2:((x - 2 ^ m)+2 ^ m) / 2 ^ m=(x - 2 ^ m) / 2 ^ m+1 :=
       Nat.add_div_right (x - 2 ^ m) (n2P m)
     rw [← h1] at h2;rw [h2];simp
   have hm1:=z7 hm
   rw [hd];simp;generalize x / 2 ^ m=q at hm1 ⊢;omega
 have hsw_val:∀ (a b:Nat),a < b->b < n->∀ x < 2 ^ n,
     (x.testBit a=false->x.testBit b=true->x - (2 ^ b - 2 ^ a)=yu a b x) /\
     (x.testBit a=true->x.testBit b=false->x+(2 ^ b - 2 ^ a)=yu a b x):=by
   intro a b hab hbn x _
   have hpa : 2 ^ a < 2 ^ b:=Nat.pow_lt_pow_right (by omega) hab
   have hsh:∀ (m k:Nat),(decide (m<=k)&&(1:Nat).testBit (k - m))=decide (m=k):=by
     intro m k
     by_cases hmk:m=k
     . subst hmk;simp
     . cases hle:decide (m<=k)
       . simp [hmk]
       . have hle':m<=k:=of_decide_eq_true hle
         simp [hmk,qp (by omega:k - m≠0)]
   constructor
   . intro ha0 hb1
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x b hb1
     have hsub_a0:(x - 2 ^ b).testBit a=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit a) h2
       rw [nTX,Nat.testBit_two_pow,ha0] at htb
       have hba:b≠a:=by omega
       simp [hba] at htb;exact htb
     have h2:x - (2 ^ b - 2 ^ a)=(x - 2 ^ b)+2 ^ a:=by
       conv_lhs => rw [← hsub_eq]
       rw [Nat.add_sub_assoc (Nat.sub_le _ _),Nat.sub_sub_self (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ b)^^^2 ^ b:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ b)+2 ^ a=(x - 2 ^ b)^^^2 ^ a:=qs hsub_a0
     unfold yu;dsimp only
     simp only [ha0,hb1]
     change ((x - 2 ^ b)+2 ^ a).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
   . intro ha1 hb0
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x a ha1
     have hsub_b0:(x - 2 ^ a).testBit b=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit b) h2
       rw [nTX,Nat.testBit_two_pow,hb0] at htb
       have hab':a≠b:=by omega
       simp [hab'] at htb;exact htb
     have h2:x+(2 ^ b - 2 ^ a)=(x - 2 ^ a)+2 ^ b:=by
       conv_lhs => rw [← hsub_eq]
       rw [nAA,Nat.add_sub_cancel' (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ a)^^^2 ^ a:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ a)+2 ^ b=(x - 2 ^ a)^^^2 ^ b:=qs hsub_b0
     unfold yu;dsimp only
     simp only [ha1,hb0]
     change ((x - 2 ^ a)+2 ^ b).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
 have hodd_ji:(2 ^ (j - i) - 1) % 2=1:=by
   have hge : 1<=j - i:=by omega
   have hev : 2 ^ (j - i) % 2=0:=by
     obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge
     rw [hm,Nat.pow_succ];omega
   have hpos : 2<=2 ^ (j - i):=by
     have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge;simpa using this
   omega
 have hflip_add_i:∀ r,(r+(2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r+(2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i+(2 ^ (j - i) - 1):=by
     rw [hdv,Nat.mul_comm,Nat.add_mul_div_right _ _ (n2P i)]
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q;generalize 2 ^ (j - i) - 1=c at hodd_ji ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hflip_sub_i:∀ r,2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r hle
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r - (2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i - (2 ^ (j - i) - 1):=by
     have h2:r=(r - (2 ^ j - 2 ^ i))+(2 ^ j - 2 ^ i):=(Nat.sub_add_cancel hle).symm
     have h3:((r - (2 ^ j - 2 ^ i))+2 ^ i*(2 ^ (j - i) - 1)) / 2 ^ i
         = (r - (2 ^ j - 2 ^ i)) / 2 ^ i+(2 ^ (j - i) - 1):=by
       rw [Nat.mul_comm (2 ^ i),Nat.add_mul_div_right _ _ (n2P i)]
     rw [← hdv,← h2] at h3;rw [h3,Nat.add_sub_cancel]
   have hle_div : 2 ^ (j - i) - 1<=r / 2 ^ i:=by
     rw [hdv] at hle
     exact (Nat.le_div_iff_mul_le (n2P i)).2 (by rw [Nat.mul_comm];exact hle)
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q at hle_div ⊢;generalize 2 ^ (j - i) - 1=c at hodd_ji hle_div ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hshl_tb:∀ (x d k:Nat),(Nat.shiftLeft x d).testBit k=(decide (d<=k)&&x.testBit (k - d)):=by
   intro x d k
   change (x <<< d).testBit k=_
   rw [Nat.testBit_shiftLeft]
 apply nEQ
 intro r
 unfold q76 w9
 simp only [nLO,nLA,Nat.shiftRight_eq,Nat.shiftRight_eq_div_pow,
   nTO,nTA,Nat.testBit_div_two_pow,hshl_tb,
   jx,vr]
 by_cases hr:r < 2 ^ n
 . simp only [hr,↓reduceIte]
   have hsw:=hsw_val i j hij hjn r hr
   cases hri:r.testBit i <;> cases hrj:r.testBit j
   ·
     have h00_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h00_eq]
     have hmid:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hsub_j : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
       intro hle
       have h1:(r - (2 ^ j - 2 ^ i))+2 ^ j=r+2 ^ i:=by omega
       have hle_div : 1<=r / 2 ^ j:=by
         have hne0:r / 2 ^ j≠0:=by
           intro hz
           have hlt:r < 2 ^ j:=(Nat.div_eq_zero_iff.1 hz).resolve_left (Nat.ne_of_gt (n2P j))
           have hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ i:=by omega
           have hbi:(r - (2 ^ j - 2 ^ i)).testBit i=false:=Nat.testBit_lt_two_pow hlt2
           have:=hsub_i hle;rw [hbi] at this;cases this
         generalize r / 2 ^ j=q at hne0 ⊢;omega
       have hsub_div:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=r / 2 ^ j - 1:=by
         have h2:(r+2 ^ i) / 2 ^ j=r / 2 ^ j:=by
           have hrem:r % 2 ^ j+2 ^ i < 2 ^ j:=by
             have hm0:(r % 2 ^ j).testBit i=false:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
             have hlt1:r % 2 ^ j < 2 ^ j:=Nat.mod_lt r (n2P j)
             apply Nat.lt_pow_two_of_testBit;intro k hk
             rw [vk hm0]
             have hne:k≠i:=by omega
             simp only [hne,↓reduceIte]
             exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) hk))
           have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
           conv_lhs => rw [hdiv,nAA]
           rw [Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hrem,nAZ]
         have h3:((r - (2 ^ j - 2 ^ i))+2 ^ j) / 2 ^ j=(r - (2 ^ j - 2 ^ i)) / 2 ^ j+1 :=
           Nat.add_div_right _ (n2P j)
         rw [h1,h2] at h3;omega
       have hrj0:=z5 hrj
       rw [Nat.testBit_eq_decide_div_mod_eq,hsub_div];simp
       generalize r / 2 ^ j=q at hle_div hrj0 ⊢;omega
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_j hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
   ·
     have hle_j : 2 ^ j<=r:=zg hrj
     have hle : 2 ^ j - 2 ^ i<=r:=le_trans (Nat.sub_le _ _) hle_j
     have hsw_eq:r - (2 ^ j - 2 ^ i)=yu i j r:=hsw.1 hri hrj
     have hsw_lt:r - (2 ^ j - 2 ^ i) < 2 ^ n:=by omega
     have hsw_i:(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r - (2 ^ j - 2 ^ i)).testBit j=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hmid_i:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_i]
     rw [hterm1]
     simp [hle,hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have hsw_eq:r+(2 ^ j - 2 ^ i)=yu i j r:=hsw.2 hri hrj
     have hsw_lt:r+(2 ^ j - 2 ^ i) < 2 ^ n:=by rw [hsw_eq];exact q162 hi hjn hr
     have hsw_i:(r+(2 ^ j - 2 ^ i)).testBit i=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r+(2 ^ j - 2 ^ i)).testBit j=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm2]
     simp [hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have h11_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h11_eq]
     have hmid_j:(r+(2 ^ j - 2 ^ i)).testBit j=false:=by
       have hle_i : 2 ^ i<=r:=zg hri
       have hsub_rem:(r - 2 ^ i) / 2 ^ j=r / 2 ^ j:=by
         have hm1:(r % 2 ^ j).testBit i=true:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
         have hmod_i : 2 ^ i<=r % 2 ^ j:=zg hm1
         have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
         have hsub:r - 2 ^ i=2 ^ j*(r / 2 ^ j)+(r % 2 ^ j - 2 ^ i):=by omega
         have hlt:r % 2 ^ j - 2 ^ i < 2 ^ j:=lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt r (n2P j))
         rw [hsub,Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hlt,nAZ]
       have h1:r+(2 ^ j - 2 ^ i)=(r - 2 ^ i)+2 ^ j:=by omega
       rw [Nat.testBit_eq_decide_div_mod_eq,h1,Nat.add_div_right _ (n2P j),hsub_rem]
       have hr1:=z7 hrj
       simp;omega
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_j]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
 ·
   have hge1 : ¬ (r+(2 ^ j - 2 ^ i) < 2 ^ n):=by omega
   simp only [hr,hge1,↓reduceIte,Bool.and_false,Bool.false_or]
   by_cases hle : 2 ^ j - 2 ^ i<=r
   . by_cases hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ n
     . have hsub_j:(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
         have hge_q : 2 ^ (n - j) - 1<=(r - (2 ^ j - 2 ^ i)) / 2 ^ j:=by
           have h1 : 2 ^ j*(2 ^ (n - j) - 1)=2 ^ n - 2 ^ j:=by
             rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           have h2 : 2 ^ n - 2 ^ j<=r - (2 ^ j - 2 ^ i) :=
             le_trans (Nat.sub_le_sub_left (Nat.sub_le _ _) _) (Nat.sub_le_sub_right (by omega : 2 ^ n<=r) _)
           exact (Nat.le_div_iff_mul_le (n2P j)).2 (by rw [Nat.mul_comm,h1];exact h2)
         have hlt_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j < 2 ^ (n - j):=by
           have h1 : 2 ^ n=2 ^ j*2 ^ (n - j):=by
             rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           exact (Nat.div_lt_iff_lt_mul (n2P j)).2 (by rw [Nat.mul_comm,← h1];exact hlt2)
         have heq_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=2 ^ (n - j) - 1:=by omega
         rw [Nat.testBit_eq_decide_div_mod_eq,heq_q]
         have hge1' : 1<=n - j:=by omega
         have hev : 2 ^ (n - j) % 2=0:=by
           obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge1'
           rw [hm,Nat.pow_succ];omega
         have hpos : 2<=2 ^ (n - j):=by
           have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge1';simpa using this
         simp;omega
       simp [hle,hlt2,hsub_j]
     . simp [hle,hlt2]
   . simp [hle]

def q163 (n:Nat) (ps:List (Nat × Nat)):List (Nat × Nat × Nat × Nat) :=
 ps.map fun p => w9 n p.1 p.2

def kq (n:Nat) (ps:List (Nat × Nat)):Bool :=
 ps.all fun p => decide (p.1 < p.2)&&decide (p.2 < n)

def zc {n:Nat}:List (Nat × Nat)->(Fin n->Bool)->(Fin n->Bool)
 | [],x => x
 | (i,j)::rest,x =>
   if h:i < n/\j < n then yh ⟨i,h.1⟩ ⟨j,h.2⟩ (zc rest x)
   else zc rest x

lemma wv {n:Nat} (ps:List (Nat × Nat)) (x:Fin n->Bool) :
   zc ps.reverse (zc ps x)=x:=by
 have hcomp:∀ (a b:List (Nat × Nat)) (y:Fin n->Bool),
     zc (a++b) y=zc a (zc b y):=by
   intro a;induction a with
   | nil => intro b y;rfl
   | cons p t ih =>
     intro b y;rcases p with ⟨i,j⟩
     simp only [lCA,zc];split <;> rw [ih]
 induction ps generalizing x with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨i,j⟩
   simp only [lRC,hcomp,zc]
   split
   . rename_i h
     rw [q104,ih]
   . exact ih x

lemma jm {n:Nat} (ps:List (Nat × Nat)) (hv:kq n ps=true) (g:BFn n) :
   ym (q163 n ps) (encTT n g)=encTT n (fun x => g (zc ps x)):=by
 induction ps generalizing g with
 | nil => rfl
 | cons p rest ih =>
   rcases p with ⟨i,j⟩
   simp only [kq,List.all_cons,bAT,decide_eq_true_eq] at hv
   obtain ⟨⟨hij,hjn⟩,hrest⟩:=hv
   change ym (w9 n i j::q163 n rest) (encTT n g)=_
   simp only [ym]
   rw [j3 hij hjn g,ih hrest]
   congr 1;funext x
   have hlt:i < n/\j < n:=by omega
   simp only [zc]
   split
   . rfl
   . contradiction

def vh {n:Nat} (f:BFn n) (sws:List (Nat × Nat × Nat × Nat)):Prop :=
 ∃ π:(Fin n->Bool)->(Fin n->Bool),
   Function.Bijective π/\(∀ x,f (π x)=f x) /\
   ∀ g:BFn n,ym sws (encTT n g)=encTT n (fun x => g (π x))

lemma kw {n:Nat} (f:BFn n) (ps:List (Nat × Nat))
   (hv:kq n ps=true)
   (hfix:ym (q163 n ps) (encTT n f)=encTT n f) :
   vh f (q163 n ps):=by
 refine ⟨zc ps,?_,?_,fun g => jm ps hv g⟩
 . constructor
   . intro x y h
     have:=congrArg (zc ps.reverse) h
     simpa [wv] using this
   . intro y
     refine ⟨zc ps.reverse y,?_⟩
     have:=wv ps.reverse y
     simpa using this
 . intro x
   rw [jm ps hv f] at hfix
   exact congrFun (yc hfix) x

lemma q138 {n:Nat} (f:BFn n):vh f [] :=
 ⟨id,Function.bijective_id,fun _ => rfl,fun _ => rfl⟩

lemma wp {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (π:(Fin n->Bool)->(Fin n->Bool)) (hbij:Function.Bijective π) (hfix:∀ x,f (π x)=f x)
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws) :
   TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s
     (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 let φ:BFn n->BFn n:=fun g x => g (π x)
 have hφ:Function.Injective φ:=by
   intro g1 g2 heq;funext y
   obtain ⟨x,rfl⟩:=hbij.2 y
   exact congrFun heq x
 exact @TagRun.map (BFn n) (BFn n) φ hφ
   invF meetF joinF (fun _ => false) (fun _ => true) f
   invF meetF joinF (fun _ => false) (fun _ => true) f
   rfl rfl (funext hfix) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) s ws h

def z6 (x i:Nat):Nat:=(x / 64 ^ i) % 64

lemma q185 (i:Nat) : 64 ^ i=2 ^ (6*i):=by
 rw [show (64:Nat)=2 ^ 6 by decide,← Nat.pow_mul]

lemma qo (x i k:Nat) :
   (z6 x i).testBit k=if k < 6 then x.testBit (6*i+k) else false:=by
 unfold z6
 rw [q185,show (64:Nat)=2 ^ 6 by decide,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
 by_cases hk:k < 6
 . simp [hk,nAC]
 . simp [hk]

lemma wg {x y:Nat} (h:∀ i,z6 x i=z6 y i):x=y:=by
 apply nEQ;intro k
 have h1:=congrArg (fun z => z.testBit (k % 6)) (h (k / 6))
 have hm:k % 6 < 6:=Nat.mod_lt k (by decide)
 rw [qo,qo] at h1
 simp only [hm,↓reduceIte,Nat.div_add_mod] at h1
 exact h1

lemma z1 (x i:Nat):z6 (x / 64) i=z6 x (i+1):=by
 unfold z6
 rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (64 ^ i) 64]

lemma q24:∀ {x y:Nat},(∀ i,z6 y i<=z6 x i)->y<=x:=by
 intro x y h
 induction hn:x+y using Nat.strong_induction_on generalizing x y with
 | _ n ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   by_cases hq:x / 64+y / 64 < x+y
   . have hdiv:y / 64<=x / 64 :=
       ih (x / 64+y / 64) (by omega) (fun i => by rw [z1,z1];exact h (i+1)) rfl
     omega
   . omega

lemma q25 {x y:Nat} (h:∀ j,z6 x j+z6 y j < 64) (i:Nat) :
   z6 (x+y) i=z6 x i+z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   have hdiv:(x+y) / 64=x / 64+y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))

lemma q188 {x y:Nat} (h:∀ j,z6 y j<=z6 x j) (i:Nat) :
   z6 (x - y) i=z6 x i - z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   have hdiv:(x - y) / 64=x / 64 - y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))

lemma v9 (x y i:Nat):z6 (Nat.land x y) i=Nat.land (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTA]

lemma wb (x y i:Nat):z6 (Nat.lor x y) i=Nat.lor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLO,nLO,nTO,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTO]

lemma q110 (x y i:Nat):z6 (Nat.xor x y) i=Nat.xor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nXO,nXO,nTX,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTX]

def qe (m val:Nat):Nat :=
 match m with
 | 0 => 0
 | m'+1 => val+64*qe m' val

lemma v0 (m val i:Nat) (hv:val < 64) :
   z6 (qe m val) i=if i < m then val else 0:=by
 induction m generalizing i with
 | zero => simp [qe,z6]
 | succ m ih =>
   cases i with
   | zero => simp only [qe,z6,Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,↓reduceIte];omega
   | succ k =>
     rw [← z1]
     have hd:qe (m+1) val / 64=qe m val:=by simp only [qe];omega
     rw [hd,ih k]
     by_cases h:k < m <;> simp [h,show k+1 < m+1 ↔ k < m by omega]

def v6 (a b c d e f:Bool):Nat :=
 let nd:=!d;let ne:=!e;let nf:=!f
 (if nd&&b then 1 else 0)+(if nd&&c then 1 else 0) +
 (if a&&ne then 1 else 0)+(if a&&nf then 1 else 0) -
 (if (a&&nd)&&((b||c)&&(ne||nf)) then 1 else 0)

def zq (a b c d e f:Bool):Nat :=
 max (v6 a b c d e f) (v6 (!a) (!b) (!c) (!d) (!e) (!f))

lemma q122:v6 true true true false false false=3:=by decide

lemma yr:∀ a b c d e f:Bool,v6 a b c d e f<=3:=by decide

lemma q52:∀ a b c d e f:Bool,zq a b c d e f<=3:=by decide

lemma k7:∀ a b c d e f:Bool,v6 a b c d e f<=zq a b c d e f:=by decide

lemma jp:∀ a b c d e f:Bool,zq (!a) (!b) (!c) (!d) (!e) (!f)=zq a b c d e f:=by decide

lemma w4:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide

lemma kl:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide

lemma q14 (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=w4 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=kl (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_or]
 omega

lemma je (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=kl a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=w4 (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_and]
 omega

lemma wc (w s m i:Nat) :
   z6 (Nat.land (Nat.shiftRight w s) (qe m 1)) i =
     if i < m then (if w.testBit (6*i+s) then 1 else 0) else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (w >>> s).testBit (6*i)=_
     rw [nTS,nAC s (6*i)]
     cases h:w.testBit (6*i+s) <;> simp [h]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     cases w.testBit (6*i+s) <;> simp [qp (by omega:k'+1≠0)]
 . simp [hi,nLA]

lemma yy (m w0 i:Nat) :
   z6 (qi (qe m 1) w0) i =
     if i < m then
       v6 (w0.testBit (6*i)) (w0.testBit (6*i+1)) (w0.testBit (6*i+2))
               (w0.testBit (6*i+3)) (w0.testBit (6*i+4)) (w0.testBit (6*i+5))
     else 0:=by
 unfold qi
 simp only [v5]
 have hbit:∀ s j,z6 (Nat.land (Nat.shiftRight w0 s) (qe m 1)) j =
     if j < m then (if w0.testBit (6*j+s) then 1 else 0) else 0:=fun s j => wc w0 s m j
 have hbit0:∀ j,z6 (Nat.land w0 (qe m 1)) j =
     if j < m then (if w0.testBit (6*j) then 1 else 0) else 0:=fun j => by
   have:=hbit 0 j;simpa using this
 have hxor:∀ s j,z6 (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1))) j =
     if j < m then (if !(w0.testBit (6*j+s)) then 1 else 0) else 0:=by
   intro s j
   rw [q110,v0 m 1 j (by decide),hbit s j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte];cases w0.testBit (6*j+s) <;> decide
   . simp [hj]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set nd:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 3) (qe m 1))
 set ne:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 4) (qe m 1))
 set nf:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 5) (qe m 1))
 have h_and_b:∀ bx by_:Bool,
     Nat.land (if bx then 1 else 0) (if by_ then 1 else 0)=if bx&&by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have h_or_b:∀ bx by_:Bool,
     Nat.lor (if bx then 1 else 0) (if by_ then 1 else 0)=if bx||by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have hL:∀ j,z6 (Nat.land nd b) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+1) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 1 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL2:∀ j,z6 (Nat.land nd c) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+2) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 2 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL3:∀ j,z6 (Nat.land a ne) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+4)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 4 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL4:∀ j,z6 (Nat.land a nf) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+5)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 5 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hSub:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j =
     if j < m then (if (w0.testBit (6*j)&&!(w0.testBit (6*j+3))) &&
       ((w0.testBit (6*j+1)||w0.testBit (6*j+2)) &&
        (!(w0.testBit (6*j+4))||!(w0.testBit (6*j+5)))) then 1 else 0) else 0:=by
   intro j
   rw [v9 (Nat.land a nd),v9 a nd,v9 (Nat.lor b c),wb b c,wb ne nf,
       hbit0 j,hxor 3 j,hbit 1 j,hbit 2 j,hxor 4 j,hxor 5 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,h_and_b,h_or_b]
   . simp [hj]
 have hSum1:∀ j,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j:=fun j =>
   q25 (fun l => by rw [hL l,hL2 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSum2:∀ j,z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) j =
     z6 (Nat.land a ne) j+z6 (Nat.land a nf) j:=fun j =>
   q25 (fun l => by rw [hL3 l,hL4 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSumAll:∀ j,z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j+(z6 (Nat.land a ne) j+z6 (Nat.land a nf) j):=by
   intro j
   have hlt:∀ l,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) l+z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) l < 64:=by
     intro l;rw [hSum1 l,hSum2 l,hL l,hL2 l,hL3 l,hL4 l]
     by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> split <;> split <;> omega
   change z6 (_+_) j=_
   rw [q25 hlt j,hSum1 j,hSum2 j]
 have hSubLe:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j <=
     z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j:=by
   intro j;rw [hSumAll j,hSub j,hL j,hL2 j,hL3 j,hL4 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte]
     cases w0.testBit (6*j) <;> cases w0.testBit (6*j+1) <;> cases w0.testBit (6*j+2) <;>
       cases w0.testBit (6*j+3) <;> cases w0.testBit (6*j+4) <;> cases w0.testBit (6*j+5) <;> decide
   . simp [hj]
 change z6 (_ - _) i=_
 rw [q188 hSubLe i,hSumAll i,hSub i,hL i,hL2 i,hL3 i,hL4 i]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte,v6]
   omega
 . simp [hi]

lemma q51:∀ v1 v2:Nat,v1<=3->v2<=3 ->
   let u:=Nat.lor v1 v2
   let hi:=Nat.land u 2
   Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                       (Nat.land (Nat.land u 1) (Nat.xor 1 (Nat.shiftRight hi 1))))=max v1 v2:=by
 intro v1 v2 h1 h2
 interval_cases v1 <;> interval_cases v2 <;> decide

lemma ya {v:Nat} (hv:∀ j,z6 v j<=3) (i:Nat) :
   z6 (Nat.land v (Nat.shiftRight v 1)) i=Nat.land (z6 v i) (Nat.shiftRight (z6 v i) 1):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo]
 by_cases hk:k < 6
 . simp only [hk,↓reduceIte,nTA]
   change (v.testBit (6*i+k)&&(v >>> 1).testBit (6*i+k)) =
     (v.testBit (6*i+k)&&((z6 v i) >>> 1).testBit k)
   rw [nTS,nTS,qo]
   by_cases hk5:k < 5
   . have hk1 : 1+k < 6:=by omega
     simp only [hk1,↓reduceIte]
     have : 1+(6*i+k)=6*i+(1+k):=by omega
     rw [this]
   . have hk_eq:k=5:=by omega
     subst hk_eq
     have hvi:z6 v i < 4:=by have:=hv i;omega
     have htb5:(z6 v i).testBit 5=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hvi (by decide))
     rw [qo] at htb5
     simp only [show 5 < 6 by decide,↓reduceIte] at htb5
     simp [htb5]
 . simp [hk]

lemma jv {hi:Nat} (hhi:∀ j,z6 hi j=0\/z6 hi j=2) (i:Nat) :
   z6 (Nat.land (Nat.shiftRight hi 1) (qe m 1)) i =
     if i < m then Nat.shiftRight (z6 hi i) 1 else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (hi >>> 1).testBit (6*i)=((z6 hi i) >>> 1).testBit 0
     rw [nTS,nTS,qo]
     simp [nAC]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     rcases hhi i with h0 | h2
     . rw [h0];simp
     . rw [h2];change false=((2 >>> 1:Nat).testBit (k'+1));simp [qp (by omega:k'+1≠0)]
 . simp [hm,nLA]

lemma kh (sh1 m w i:Nat) :
   z6 (yg sh1 (qe m 1) (qe m 2) w) i =
     if i < m then
       zq (w.testBit (sh1+6*i)) (w.testBit (sh1+6*i+1)) (w.testBit (sh1+6*i+2))
               (w.testBit (sh1+6*i+3)) (w.testBit (sh1+6*i+4)) (w.testBit (sh1+6*i+5))
     else 0:=by
 unfold yg
 simp only [v5]
 set w0:=Nat.shiftRight w sh1
 have hw0:∀ k,w0.testBit k=w.testBit (sh1+k):=fun k => by
   change (w >>> sh1).testBit k=_;rw [nTS,nAC]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set d:=Nat.land (Nat.shiftRight w0 3) (qe m 1)
 set e:=Nat.land (Nat.shiftRight w0 4) (qe m 1)
 set f:=Nat.land (Nat.shiftRight w0 5) (qe m 1)
 set nd:=Nat.xor (qe m 1) d
 set ne:=Nat.xor (qe m 1) e
 set nf:=Nat.xor (qe m 1) f
 set na:=Nat.xor (qe m 1) a
 set nb:=Nat.xor (qe m 1) b
 set nc:=Nat.xor (qe m 1) c
 set v1:=Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                   (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
 set v2:=Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                   (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))
 have hv1_eq:v1=qi (qe m 1) w0:=by
   unfold qi;simp only [v5];rfl
 have hv1:∀ j,z6 v1 j=if j < m then
     v6 (w0.testBit (6*j)) (w0.testBit (6*j+1)) (w0.testBit (6*j+2))
             (w0.testBit (6*j+3)) (w0.testBit (6*j+4)) (w0.testBit (6*j+5)) else 0:=by
   intro j;rw [hv1_eq,yy]
 have hv2_eq:v2=qi (qe m 1) (Nat.xor w0 (2 ^ (6*m) - 1)):=by
   have hbit_inv:∀ s,s < 6->Nat.land (Nat.shiftRight (Nat.xor w0 (2 ^ (6*m) - 1)) s) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1)):=by
     intro s hs
     apply wg;intro j
     rw [wc,q110,v0 m 1 j (by decide),wc]
     by_cases hj:j < m
     . have hlt : 6*j+s < 6*m:=by omega
       simp only [hj,↓reduceIte,nXO,nTX,nTB,hlt,decide_true]
       cases w0.testBit (6*j+s) <;> decide
     . simp [hj]
   have hbit_inv0:Nat.land (Nat.xor w0 (2 ^ (6*m) - 1)) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land w0 (qe m 1)):=by
     have:=hbit_inv 0 (by decide);simpa using this
   have hxor_inv:∀ x,Nat.xor (qe m 1) (Nat.xor (qe m 1) x)=x:=by
     intro x;apply nEQ;intro k
     rw [nXO,nXO,nTX,nTX]
     cases (qe m 1).testBit k <;> cases x.testBit k <;> decide
   unfold qi;simp only [v5]
   rw [hbit_inv0,hbit_inv 1 (by decide),hbit_inv 2 (by decide),
       hbit_inv 3 (by decide),hbit_inv 4 (by decide),hbit_inv 5 (by decide),
       hxor_inv,hxor_inv,hxor_inv]
 have hv2:∀ j,z6 v2 j=if j < m then
     v6 (!(w0.testBit (6*j))) (!(w0.testBit (6*j+1))) (!(w0.testBit (6*j+2)))
             (!(w0.testBit (6*j+3))) (!(w0.testBit (6*j+4))) (!(w0.testBit (6*j+5))) else 0:=by
   intro j;rw [hv2_eq,yy]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,nXO,nTX,nTB]
     simp only [show 6*j < 6*m by omega,show 6*j+1 < 6*m by omega,
       show 6*j+2 < 6*m by omega,show 6*j+3 < 6*m by omega,
       show 6*j+4 < 6*m by omega,show 6*j+5 < 6*m by omega,
       decide_true,bBT]
   . simp [hj]
 have hv1_le3:∀ j,z6 v1 j<=3:=fun j => by
   rw [hv1 j];split;exact yr _ _ _ _ _ _;omega
 have hv2_le3:∀ j,z6 v2 j<=3:=fun j => by
   rw [hv2 j];split;exact yr _ _ _ _ _ _;omega
 set u:=Nat.lor v1 v2
 set hi:=Nat.land u (qe m 2)
 have hhi_lane:∀ j,z6 hi j=if j < m then Nat.land (Nat.lor (z6 v1 j) (z6 v2 j)) 2 else 0:=by
   intro j;rw [v9,wb,v0 m 2 j (by decide)]
   by_cases hj:j < m <;> simp [hj,nLA]
 have hhi02:∀ j,z6 hi j=0\/z6 hi j=2:=by
   intro j;rw [hhi_lane j]
   split
   . have h1:=hv1_le3 j;have h2:=hv2_le3 j
     generalize z6 v1 j=x at h1;generalize z6 v2 j=y at h2
     interval_cases x <;> interval_cases y <;> decide
   . left;rfl
 have hlast:z6 (Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1))) i =
     if i < m then Nat.land (Nat.land (Nat.lor (z6 v1 i) (z6 v2 i)) 1) (Nat.xor 1 (Nat.shiftRight (z6 hi i) 1)) else 0:=by
   have hrew:Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1)) =
       Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight hi 1) (qe m 1))):=by
     apply nEQ;intro k
     simp only [nLA,nXO,nTA,nTX]
     cases (qe m 1).testBit k <;> simp
   rw [hrew,v9,v9,wb,q110,v0 m 1 i (by decide),
       jv (m:=m) hhi02 i]
   by_cases hm:i < m <;> simp [hm,nLA]
 rw [wb,wb,wb,ya hv1_le3 i,
     ya hv2_le3 i,hlast,hhi_lane i]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   have hmain:=q51 (z6 v1 i) (z6 v2 i) (hv1_le3 i) (hv2_le3 i)
   simp only at hmain
   rw [hmain,hv1 i,hv2 i]
   simp only [hm,↓reduceIte,hw0,zq]
   have ha1:sh1+(6*i+1)=sh1+6*i+1:=by omega
   have ha2:sh1+(6*i+2)=sh1+6*i+2:=by omega
   have ha3:sh1+(6*i+3)=sh1+6*i+3:=by omega
   have ha4:sh1+(6*i+4)=sh1+6*i+4:=by omega
   have ha5:sh1+(6*i+5)=sh1+6*i+5:=by omega
   rw [ha1,ha2,ha3,ha4,ha5]
 . simp only [hm,↓reduceIte,hv1 i,hv2 i];decide

lemma q47 {α:Type} (f : α->Nat) (m:Nat)
   (hf:∀ x i,z6 (f x) i<=(if i < m then 3 else 0))
   (xs:List α) (hlen:xs.length<=11) (i:Nat) :
   z6 (xs.foldr (fun x acc => Nat.add (f x) acc) 0) i=(xs.map fun x => z6 (f x) i).sum /\
   (xs.map fun x => z6 (f x) i).sum<=if i < m then 3*xs.length else 0:=by
 induction xs generalizing i with
 | nil => simp [z6]
 | cons a t ih =>
   simp only [lLC] at hlen
   have ih_all:∀ j,z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j =
       (t.map fun x => z6 (f x) j).sum /\
       (t.map fun x => z6 (f x) j).sum<=if j < m then 3*t.length else 0 :=
     fun j => ih (by omega) j
   have hlt:∀ j,z6 (f a) j+z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j < 64:=by
     intro j
     have h1:=hf a j
     have ⟨h2,h3⟩:=ih_all j
     rw [h2]
     by_cases hj:j < m <;> simp only [hj,↓reduceIte] at h1 h3 <;> omega
   simp only [lFC,lMC,List.sum_cons,lLC]
   have hadd:=q25 hlt i
   have hfa:=hf a i
   have ⟨h2,h3⟩:=ih_all i
   refine ⟨?_,?_⟩
   . change z6 (_+_) i=_;rw [hadd,h2]
   . by_cases hi:i < m <;> simp only [hi,↓reduceIte] at hfa h3 ⊢ <;> omega

lemma ky (S m:Nat)
   (hS_bound:∀ i,z6 S i<=if i < m then 33 else 0)
   (hS_ge3:∀ i < m,3<=z6 S i) :
   Nat.beq (Nat.land (Nat.add S (qe m 29)) (qe m 32)) (qe m 32)=true:=by
 rw [Nat.beq_eq]
 apply wg;intro i
 have hlt:∀ j,z6 S j+z6 (qe m 29) j < 64:=by
   intro j;rw [v0 m 29 j (by decide)]
   have hb:=hS_bound j
   by_cases hj:j < m <;> simp only [hj,↓reduceIte] at hb ⊢ <;> omega
 rw [v9]
 change Nat.land (z6 (S+qe m 29) i) (z6 (qe m 32) i)=z6 (qe m 32) i
 rw [q25 hlt i,v0 m 29 i (by decide),v0 m 32 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   have hb:=hS_bound i;simp only [hi,↓reduceIte] at hb
   have hge:=hS_ge3 i hi
   have h1 : 32<=z6 S i+29:=by omega
   have h2:z6 S i+29 < 64:=by omega
   generalize z6 S i+29=v at h1 h2
   interval_cases v <;> decide
 . simp [hi,nLA]

def j5 (rp:Nat):Nat->Nat->List Nat
 | 0,_ => []
 | m+1,idx => Nat.land (Nat.shiftRight rp (Nat.mul 7 idx)) 127::j5 rp m (Nat.add idx 1)

lemma q32 (rp m idx:Nat):(j5 rp m idx).length=m:=by
 induction m generalizing idx with
 | zero => rfl
 | succ m ih => simp [j5,ih]

def q106 (rp shTT:Nat):List Nat:=j5 rp shTT 0

def allRows (n rp shTT:Nat):List Nat:=q106 rp shTT++List.range (2 ^ n)

lemma jj (rp shTT:Nat):(q106 rp shTT).length=shTT :=
 q32 rp shTT 0

lemma zl (n rp shTT:Nat):(allRows n rp shTT).length=shTT+2 ^ n:=by
 simp [allRows,jj]

structure CfgOk (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Prop where
 sh0_eq:c.sh0=2*c.k
 sh0_le:c.sh0<=c.sh1
 sh1_le:c.sh1<=c.shTT
 p0_dvd:(c.sh1 - c.sh0) % 6=0
 p1_dvd:(c.shTT - c.sh1) % 6=0
 all1v_eq:c.all1v=2 ^ (c.shTT+2 ^ n) - 1
 goalv_eq:c.goalv=encL (allRows n rp c.shTT) f
 lok_eq:c.lok=2 ^ c.k - 1
 m0all_eq:c.m0all=2 ^ (6*((c.sh1 - c.sh0) / 6)) - 1
 m0_eq:c.m0=qe ((c.sh1 - c.sh0) / 6) 1
 a29_0_eq:c.a29_0=qe ((c.sh1 - c.sh0) / 6) 29
 b5_0_eq:c.b5_0=qe ((c.sh1 - c.sh0) / 6) 32
 m1_eq:c.m1=qe ((c.shTT - c.sh1) / 6) 1
 m12_eq:c.m12=qe ((c.shTT - c.sh1) / 6) 2
 a29_1_eq:c.a29_1=qe ((c.shTT - c.sh1) / 6) 29
 b5_1_eq:c.b5_1=qe ((c.shTT - c.sh1) / 6) 32
 cov_ok:∀ i < c.k,
   f (q1 n ((allRows n rp c.shTT).getD i 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.k+i) 0))=true
 p0_ok:∀ i < (c.sh1 - c.sh0) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+5) 0))=false
 p1_ok:∀ i < (c.shTT - c.sh1) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+5) 0))=false

def w3 (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Bool :=
 let np0:=(c.sh1 - c.sh0) / 6
 let np1:=(c.shTT - c.sh1) / 6
 Nat.beq c.sh0 (2*c.k) &&
 Nat.ble c.sh0 c.sh1 &&
 Nat.ble c.sh1 c.shTT &&
 Nat.beq ((c.sh1 - c.sh0) % 6) 0 &&
 Nat.beq ((c.shTT - c.sh1) % 6) 0 &&
 Nat.beq c.all1v (2 ^ (c.shTT+2 ^ n) - 1) &&
 Nat.beq c.goalv (encL (allRows n rp c.shTT) f) &&
 Nat.beq c.lok (2 ^ c.k - 1) &&
 Nat.beq c.m0all (2 ^ (6*np0) - 1) &&
 Nat.beq c.m0 (qe np0 1) &&
 Nat.beq c.a29_0 (qe np0 29) &&
 Nat.beq c.b5_0 (qe np0 32) &&
 Nat.beq c.m1 (qe np1 1) &&
 Nat.beq c.m12 (qe np1 2) &&
 Nat.beq c.a29_1 (qe np1 29) &&
 Nat.beq c.b5_1 (qe np1 32) &&
 Nat.beq (Nat.land c.goalv c.lok) 0 &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.k) c.lok) c.lok &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh0) c.m0all) (qe np0 7) &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh1) (2 ^ (6*np1) - 1)) (qe np1 7)

lemma qm {n:Nat} (rows:List Nat) (f:BFn n) {idx:Nat} (h:idx < rows.length) :
   (encL rows f).testBit idx=f (q1 n (rows.getD idx 0)):=by
 rw [z8,List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]

lemma jn (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg)
   (h:w3 n f rp c=true):CfgOk n f rp c:=by
 unfold w3 at h
 simp only [bAT,Nat.beq_eq,Nat.ble_eq] at h
 rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh0,h01⟩,h1t⟩,hp0d⟩,hp1d⟩,hall1⟩,hgoal⟩,hlok⟩,hm0all⟩,
   hm0⟩,ha29_0⟩,hb5_0⟩,hm1⟩,hm12⟩,ha29_1⟩,hb5_1⟩,hcov0⟩,hcov1⟩,hp0m⟩,hp1m⟩
 have hlen:(allRows n rp c.shTT).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hbit_goal:∀ idx < c.shTT,c.goalv.testBit idx=f (q1 n ((allRows n rp c.shTT).getD idx 0)):=by
   intro idx hidx
   rw [hgoal,qm _ _ (by rw [hlen];exact Nat.lt_add_right (2 ^ n) hidx)]
 have hlane7:∀ (sh m:Nat),sh+6*m<=c.shTT ->
     Nat.land (Nat.shiftRight c.goalv sh) (2 ^ (6*m) - 1)=qe m 7 ->
     ∀ i < m,
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+1) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+2) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+3) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+4) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+5) 0))=false:=by
   intro sh m hbound heq i hi
   have htb:∀ off < 6,f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+off) 0))=(7:Nat).testBit off:=by
     intro off hoff
     have h1:=congrArg (fun z => z6 z i) heq
     rw [v0 m 7 i (by decide)] at h1
     simp only [hi,↓reduceIte] at h1
     have h2:=congrArg (fun z => z.testBit off) h1
     rw [qo] at h2
     simp only [hoff,↓reduceIte,nLA,nTA,nTB,
       show 6*i+off < 6*m by omega,decide_true,bATR] at h2
     change (c.goalv >>> sh).testBit (6*i+off)=_ at h2
     rw [nTS,← nAA] at h2
     rw [← hbit_goal (sh+6*i+off) (by omega)]
     exact h2
   exact ⟨by simpa using htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
          htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)⟩
 refine ⟨hsh0,h01,h1t,hp0d,hp1d,hall1,hgoal,hlok,hm0all,hm0,ha29_0,hb5_0,hm1,hm12,ha29_1,hb5_1,?_,?_,?_⟩
 . intro i hi
   constructor
   . have h1:=congrArg (fun z => z.testBit i) hcov0
     rw [nLA,nTA,hlok,nTB,nZT] at h1
     simp only [hi,decide_true,bATR] at h1
     rw [← hbit_goal i (by omega)];exact h1
   . have h1:=congrArg (fun z => z.testBit i) hcov1
     rw [nLA,nTA,hlok,nTB] at h1
     simp only [hi,decide_true,bATR] at h1
     change (c.goalv >>> c.k).testBit i=true at h1
     rw [nTS] at h1
     rw [← hbit_goal (c.k+i) (by omega)];exact h1
 . apply hlane7 c.sh0 ((c.sh1 - c.sh0) / 6) (by omega)
   rw [← hm0all];exact hp0m
 . apply hlane7 c.sh1 ((c.shTT - c.sh1) / 6) (by omega) hp1m

def AllTagsLe3 {α:Type} (ws:List (α × Nat)):Prop:=∀ p ∈ ws,p.2<=3

lemma AllTagsLe3.perm {α:Type} {xs ys:List (α × Nat)} (hp:xs.Perm ys)
   (h:AllTagsLe3 xs):AllTagsLe3 ys :=
 fun p hm => h p (hp.symm.subset hm)

lemma TagRun.inv_zero {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal 0 ws) :
   ∃ tg,ws=[(goal,tg)]:=by
 generalize hs:(0:Nat)=s at h
 induction h with
 | done tg => exact ⟨tg,rfl⟩
 | perm hp _ ih =>
   obtain ⟨tg,rfl⟩:=ih hs
   exact ⟨tg,List.perm_singleton.1 hp.symm⟩
 | uNot _ _ _ _ _ _ _ _ _ => cases hs
 | bOr _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _ => cases hs

lemma TagRun.inv_succ {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s:Nat} {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal (s+1) ws) :
   (∃ a ta r save,ws.Perm ((a,ta)::r) /\
     ta≠1/\ta≠2/\(ta=3->save=false) /\
     inv a≠zero/\inv a≠one/\inv a≠a/\(∀ x ∈ r,x.1≠inv a) /\
     TagRun inv meet join zero one goal s ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r)) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠2/\tb≠2/\(ta=1->ka=false)/\(tb=1->kb=false) /\
     join a b≠zero/\join a b≠one/\join a b≠a/\join a b≠b/\(∀ x ∈ r,x.1≠join a b) /\
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r))) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠1/\tb≠1/\(ta≠0->ka=false)/\(tb≠0->kb=false) /\
     meet a b≠zero/\meet a b≠one/\meet a b≠a/\meet a b≠b/\(∀ x ∈ r,x.1≠meet a b) /\
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize hs:s+1=s' at h
 induction h with
 | done _ => cases hs
 | perm hp _ ih =>
   rcases ih hs with ⟨a,ta,r,save,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩
   . exact Or.inl ⟨a,ta,r,save,hp.symm.trans hp',rest⟩
   . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
   . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
 | @uNot s0 a ta r save h1 h2 h3 h4 h5 h6 h7 hsub _ =>
   cases hs
   exact Or.inl ⟨a,ta,r,save,lPR _,h1,h2,h3,h4,h5,h6,h7,hsub⟩
 | @bOr s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
 | @bAnd s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)

lemma q68 {α:Type} {ws:List α} {a : α} {r:List α} (hp:ws.Perm (a::r)) :
   ∃ pre suf,ws=pre++a::suf/\r.Perm (pre++suf):=by
 have hmem:a ∈ ws:=hp.symm.subset (by simp)
 obtain ⟨pre,suf,hws⟩:=List.append_of_mem hmem
 refine ⟨pre,suf,hws,?_⟩
 rw [hws] at hp
 exact (List.perm_cons a).1 (hp.symm.trans lPM)

lemma q67 {α:Type} {ws:List α} {a b : α} {r:List α} (hp:ws.Perm (a::b::r)) :
   (∃ pre mid suf,ws=pre++a::mid++b::suf/\r.Perm (pre++mid++suf)) \/
   (∃ pre mid suf,ws=pre++b::mid++a::suf/\r.Perm (pre++mid++suf)):=by
 obtain ⟨p1,s1,hws,hbr⟩:=q68 hp
 have hmem:b ∈ p1++s1:=hbr.subset (by simp)
 rcases List.mem_append.1 hmem with hbp | hbs
 . obtain ⟨pre,mid,hp1⟩:=List.append_of_mem hbp
   right
   refine ⟨pre,mid,s1,by rw [hws,hp1,lAA,lCA],?_⟩
   rw [hp1,lAA] at hbr
   have hmid:(pre++b::(mid++s1)).Perm (b::(pre++(mid++s1))):=lPM
   have h1:=(List.perm_cons b).1 (hbr.trans hmid)
   simpa [lAA] using h1
 . obtain ⟨mid,suf,hs1⟩:=List.append_of_mem hbs
   left
   refine ⟨p1,mid,suf,by simp [hws,hs1,lAA],?_⟩
   rw [hs1] at hbr
   have hmid:((p1++mid)++b::suf).Perm (b::((p1++mid)++suf)):=lPM
   rw [← lAA] at hbr
   exact (List.perm_cons b).1 (hbr.trans hmid)

lemma z4 {α:Type} (k:Bool) (a : α) (r:List α) (x : α) :
   x ∈ qk k a r ↔ (k=true/\x=a)\/x ∈ r:=by
 cases k <;> simp [qk]

lemma yd {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (u v:Fin n->Bool) (hu:f u=false) (hv:f v=true) :
   ∃ p ∈ ws,p.1 u≠p.1 v:=by
 induction h with
 | done tg => exact ⟨(f,tg),by simp,by simp [hu,hv]⟩
 | perm hp _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   exact ⟨p,hp.subset hm,hne⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . exact ⟨(a,ta),by simp,fun e => hne (by dsimp only at e;simp [invF,e])⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . exact ⟨p,by simp [hm3],hne⟩
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [joinF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [meetF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩

lemma zk {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (joinF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [joinF,Bool.or_eq_false_iff,bOT] at hu hv
   rcases hv with hva | hvb
   . exact ⟨(a,ta),by simp,hu.1,hva⟩
   . exact ⟨(b,tb),by simp,hu.2,hvb⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩

lemma za {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (meetF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [meetF,Bool.and_eq_false_iff,bAT] at hu hv
   rcases hu with hua | hub
   . exact ⟨(a,ta),by simp,hua,hv.1⟩
   . exact ⟨(b,tb),by simp,hub,hv.2⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩

lemma qf {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1) :
   ∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true:=by
 induction h with
 | done tg => intro u v hu hv;exact ⟨(f,tg),by simp,hu,hv⟩
 | perm hp _ ih =>
   intro u v hu hv
   obtain ⟨p,hm,h1,h2⟩:=ih (by rw [hp.length_eq];exact hlen) u v hu hv
   exact ⟨p,hp.subset hm,h1,h2⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact zk (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact za (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)

lemma kk {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1)
   (r0 r1 r2 r3 r4 r5:Fin n->Bool)
   (h0:f r0=true) (h1:f r1=true) (h2:f r2=true)
   (h3:f r3=false) (h4:f r4=false) (h5:f r5=false) :
   3<=(ws.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
 induction h with
 | done tg => simp [h0,h1,h2,h3,h4,h5,q122]
 | perm hp _ ih =>
   rw [← (hp.map _).sum_eq]
   exact ih (by rw [hp.length_eq];exact hlen)
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at hih ⊢
   have hsub6:=w4 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at hih ⊢
   have hsub6:=kl (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega

lemma qh {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s) :
   (∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) \/
   (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum):=by
 induction h with
 | done tg => simp at hlen
 | perm hp _ ih =>
   rcases ih (by rw [hp.length_eq];exact hlen) with hcov | hsym
   . left;intro u v hu hv
     obtain ⟨p,hm,h1,h2⟩:=hcov u v hu hv
     exact ⟨p,hp.subset hm,h1,h2⟩
   . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     rw [← (hp.map _).sum_eq]
     exact hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save
   . right
     intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hv:=kk hsub (by simp [qk] at hlen ⊢;omega) r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hle_s:∀ l:List (BFn n × Nat),
         (l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
         (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
       intro l;induction l with
       | nil => simp
       | cons x t iht =>
         simp only [lMC,List.sum_cons]
         have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5)
         omega
     have hs:=le_trans hv (hle_s _)
     simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs ⊢
     exact hs
   . simp [qk] at hlen hle;omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact zk (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at h1 ⊢
       have hsub6:=q14 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact zk (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact zk (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact za (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at h1 ⊢
       have hsub6:=je (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact za (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact za (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega

abbrev aR (n rp:Nat) (c:Cfg):=allRows n rp c.shTT

abbrev TR {n:Nat} (f:BFn n):=TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f

lemma qz {a b:Nat} (h:a=b):Nat.beq a b=true:=Eq.mpr Nat.beq_eq h

lemma q0 (a:Nat):Nat.beq a a=true:=Eq.mpr Nat.beq_eq rfl

lemma q2 {a b:Nat} (h:a≠b):Nat.beq a b=false:=by
 cases hb:Nat.beq a b
 . rfl
 . exact absurd (Eq.mp Nat.beq_eq hb) h

lemma y3 {a b:Nat} (h:Nat.beq a b=false):a≠b :=
 fun e => by subst e;rw [q0] at h;cases h

lemma zh {a b:Nat}:(Nat.beq a b=false) ↔ a≠b :=
 ⟨y3,q2⟩

lemma q4 {b e:Bool} (h:e=true):(if b=true then true else e)=true:=by
 cases b <;> simp [h]

lemma q5 {b e:Bool} (h:b=true):(if b=true then true else e)=true:=by
 rw [h];rfl

lemma v8 (a b:Nat):Nat.add a b=a+b:=rfl

def encWs {n:Nat} (rows:List Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encL rows p.1,p.2)

abbrev eW {n:Nat} (rp:Nat) (c:Cfg) (ws:List (BFn n × Nat)):=encWs (aR n rp c) ws

abbrev eL {n:Nat} (rp:Nat) (c:Cfg) (g:BFn n):=encL (aR n rp c) g

lemma q41 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (joinF a b)=Nat.lor (eL rp c a) (eL rp c b):=q144 _ a b

lemma q40 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (meetF a b)=Nat.land (eL rp c a) (eL rp c b):=q143 _ a b

def encTTWs (n:Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encTT n p.1,p.2)

lemma qy {n:Nat} (rows:List Nat) (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encWs rows (p::ws)=(encL rows p.1,p.2)::encWs rows ws:=rfl

lemma kj {n:Nat} (rows:List Nat) (xs ys:List (BFn n × Nat)) :
   encWs rows (xs++ys)=encWs rows xs++encWs rows ys:=lMA

lemma q49 {n:Nat} (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encTTWs n (p::ws)=(encTT n p.1,p.2)::encTTWs n ws:=rfl

lemma q18 (xs ys:List (Nat × Nat)):qx xs ys=xs.reverse++ys:=by
 induction xs generalizing ys with
 | nil => rfl
 | cons a t ih => simp [qx,ih,lAA]

lemma q187 (ws:List (Nat × Nat)):q164 ws=ws.length:=by
 induction ws with
 | nil => rfl
 | cons _ t ih => simp [q164,ih,v8];omega

lemma wh (x:Nat) (ws:List (Nat × Nat)) :
   yz x ws=false ↔ ∀ p ∈ ws,p.1≠x:=by
 induction ws with
 | nil => simp [yz]
 | cons a t ih =>
   rcases a with ⟨w,tg⟩
   simp only [yz,lMM,forall_eq_or_imp]
   by_cases h:x=w
   . subst h;simp [q0]
   . simp [q2 h,ih,Ne.symm h]

lemma jo {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (ws:List (BFn n × Nat)) (g:BFn n)
   (h0:g≠fun _ => false) (h1:g≠fun _ => true) (hmem:∀ p ∈ ws,p.1≠g) :
   qj c.all1v (eW rp c ws) (eL rp c g)=true:=by
 have hinj:=q89 (n:=n) (q106 rp c.shTT)
 have hlen:(aR n rp c).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hne0:eL rp c g≠0:=fun e => by
   rw [← q39 (n:=n) (aR n rp c)] at e;exact h0 (hinj e)
 have hne1:eL rp c g≠c.all1v:=fun e => by
   rw [hc.all1v_eq,← hlen,← q177 (n:=n) (aR n rp c)] at e;exact h1 (hinj e)
 have hnc:yz (eL rp c g) (eW rp c ws)=false:=by
   rw [wh]
   intro p hp;rcases List.mem_map.1 hp with ⟨q,hq,rfl⟩
   exact fun e => hmem q hq (hinj e)
 unfold qj
 simp [q2 hne0,q2 hne1,hnc]

lemma qc {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (joinF a b)=Nat.lor (encL rows a) (encL rows b):=q144 rows a b

lemma q9 {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (meetF a b)=Nat.land (encL rows a) (encL rows b):=q143 rows a b

lemma q145 {n:Nat} (rows:List Nat) (a:BFn n) :
   encL rows (invF a)=Nat.xor (encL rows a) (2 ^ rows.length - 1):=q160 rows a

lemma qv {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:BFn n) :
   eL rp c (invF a)=Nat.xor (eL rp c a) c.all1v:=by
 unfold eL;rw [q160,zl,← hc.all1v_eq]

def wi (c:Cfg) (w:Nat):Nat:=Nat.land w c.lok

def q63 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.k) c.lok

def k1 (c:Cfg) (w:Nat):Nat:=Nat.xor c.lok (q63 c w)

def wC (c:Cfg) (w:Nat):Nat:=Nat.xor (wi c w) (q63 c w)

def wU (c:Cfg) (w:Nat):Nat:=Nat.land (wC c w) (q63 c w)

def wA0 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.sh0) c.m0all

def wV0 (c:Cfg) (w:Nat):Nat:=qi c.m0 (wA0 c w)

def wV1 (c:Cfg) (w:Nat):Nat:=yg c.sh1 c.m1 c.m12 w

def yx (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wC c p.1) acc) 0

def v4 (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wU c p.1) acc) 0

def zf (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0

def va (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0

lemma qq (a b d:Nat):Nat.lor (Nat.lor a b) d=Nat.lor a (Nat.lor b d):=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_assoc]

lemma q7 (a b:Nat):Nat.lor a b=Nat.lor b a:=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_comm]

lemma q108 (a b:Nat):Nat.land a b=Nat.land b a:=by
 apply nEQ;intro i;simp [nLA,nTA,Bool.and_comm]

lemma q46 (a:Nat):Nat.lor 0 a=a:=by
 apply nEQ;intro i;simp [nLO,nTO]

lemma qt (a b:Nat):Nat.add a b=Nat.add b a:=nAC a b

lemma y9 (a b d:Nat):Nat.add (Nat.add a b) d=Nat.add a (Nat.add b d):=nAA a b d

lemma yp (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):yx c (p::ws)=Nat.lor (wC c p.1) (yx c ws):=rfl

lemma vo (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):v4 c (p::ws)=Nat.lor (wU c p.1) (v4 c ws):=rfl

lemma k0 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):zf c (p::ws)=Nat.add (wV0 c p.1) (zf c ws):=rfl

lemma w1 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):va c (p::ws)=Nat.add (wV1 c p.1) (va c ws):=rfl

lemma vc (c:Cfg) (xs ys:List (Nat × Nat)):yx c (xs++ys)=Nat.lor (yx c xs) (yx c ys):=by
 induction xs with | nil => simp [yx,q46] | cons a t ih => simp only [lCA,yx,lFC] at ih ⊢;rw [ih,qq]

lemma zu (c:Cfg) (xs ys:List (Nat × Nat)):v4 c (xs++ys)=Nat.lor (v4 c xs) (v4 c ys):=by
 induction xs with | nil => simp [v4,q46] | cons a t ih => simp only [lCA,v4,lFC] at ih ⊢;rw [ih,qq]

lemma zy (c:Cfg) (xs ys:List (Nat × Nat)):zf c (xs++ys)=Nat.add (zf c xs) (zf c ys):=by
 induction xs with | nil => simp [zf,v8] | cons a t ih => simp only [lCA,zf,lFC,v8] at ih ⊢;omega

lemma y6 (c:Cfg) (xs ys:List (Nat × Nat)):va c (xs++ys)=Nat.add (va c xs) (va c ys):=by
 induction xs with | nil => simp [va,v8] | cons a t ih => simp only [lCA,va,lFC,v8] at ih ⊢;omega

lemma yo (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):yx c xs=yx c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [yx,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [yx,lFC];rw [← qq,q7 (wC c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma y0 (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):v4 c xs=v4 c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [v4,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [v4,lFC];rw [← qq,q7 (wU c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma vu (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):zf c xs=zf c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [zf,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [zf,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma kz (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):va c xs=va c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [va,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [va,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma q149 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (yx c ws).testBit i=ws.any (fun p => (wC c p.1).testBit i):=by
 induction ws with
 | nil => simp [yx]
 | cons _ _ ih => simp only [yx,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]

lemma q148 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (v4 c ws).testBit i=ws.any (fun p => (wU c p.1).testBit i):=by
 induction ws with
 | nil => simp [v4]
 | cons _ _ ih => simp only [v4,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]

lemma zw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wi c w).testBit i=if i < c.k then w.testBit i else false:=by
 unfold wi;rw [nLA,nTA,hc.lok_eq,nTB]
 by_cases hi:i < c.k <;> simp [hi]

lemma vl {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (q63 c w).testBit i=if i < c.k then w.testBit (c.k+i) else false:=by
 unfold q63;rw [nLA,nTA,hc.lok_eq,nTB]
 change ((w >>> c.k).testBit i&&decide (i < c.k))=_
 rw [nTS];by_cases hi:i < c.k <;> simp [hi]

lemma q13 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (k1 c w).testBit i=if i < c.k then !(w.testBit (c.k+i)) else false:=by
 unfold k1;rw [nXO,nTX,hc.lok_eq,nTB,vl hc]
 by_cases hi:i < c.k <;> simp [hi]

lemma vp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wC c w).testBit i=if i < c.k then (w.testBit i ^^ w.testBit (c.k+i)) else false:=by
 unfold wC;rw [nXO,nTX,zw hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]

lemma vd {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wU c w).testBit i=if i < c.k then (!(w.testBit i)&&w.testBit (c.k+i)) else false:=by
 unfold wU;rw [nLA,nTA,vp hc,vl hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases w.testBit i <;> cases w.testBit (c.k+i) <;> decide
 . simp [hi]

lemma q197 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wC c (Nat.xor a c.all1v)=wC c a:=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vp hc,vp hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]

lemma q168 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wU c (Nat.xor a c.all1v)=Nat.land (wC c a) (wi c a):=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vd hc,nLA,nTA,vp hc,zw hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]

lemma q78 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   Nat.lor (wU c (Nat.xor a c.all1v)) (wU c a)=wC c a:=by
 rw [q168 hc];apply nEQ;intro i
 rw [nLO,nLA,nTO,nTA,vp hc,zw hc,vd hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]

lemma q169 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.lor a b)=Nat.xor (Nat.lor (wi c a) (wi c b)) (Nat.lor (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLO,nLO,nLO,
     nTX,nTO,nTO,nTO,nTO,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]

lemma q121 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.land a b)=Nat.xor (Nat.land (wi c a) (wi c b)) (Nat.land (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLA,nLA,nLA,
     nTX,nTA,nTA,nTA,nTA,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]

lemma q170 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wA0 c (Nat.xor a c.all1v)=Nat.xor (wA0 c a) c.m0all:=by
 have h2n:=n2P n
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nXO,nTA,nTX,hc.m0all_eq,nTB]
 change (((a^^^c.all1v) >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) =
   (((a >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) ^^ decide (i < 6*((c.sh1 - c.sh0) / 6)))
 rw [nTS,nTS,nTX,hc.all1v_eq,nTB]
 by_cases hi:i < 6*((c.sh1 - c.sh0) / 6)
 . simp [hi,show c.sh0+i < c.shTT+2 ^ n by omega]
 . simp [hi]

lemma q198 (c:Cfg) (a b:Nat):wA0 c (Nat.lor a b)=Nat.lor (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nLO,nTA,nTO]
 change (((a|||b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)||((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTO]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide

lemma q171 (c:Cfg) (a b:Nat):wA0 c (Nat.land a b)=Nat.land (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nTA]
 change (((a&&&b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)&&((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTA]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide

lemma q200 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wV1 c (Nat.xor a c.all1v)=wV1 c a:=by
 have h2n:=n2P n
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 apply wg;intro i;unfold wV1
 rw [hc.m1_eq,hc.m12_eq,kh,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show c.sh1+6*i < c.shTT+2 ^ n by omega,show c.sh1+6*i+1 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+2 < c.shTT+2 ^ n by omega,show c.sh1+6*i+3 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+4 < c.shTT+2 ^ n by omega,show c.sh1+6*i+5 < c.shTT+2 ^ n by omega,
     decide_true,bBT,jp]
 . simp [hi]

lemma y4 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.lor a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0/\Nat.land (Nat.xor c.lok rU) (wi c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,zw hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])

lemma q10 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.lor a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,zw hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]

lemma vw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.land a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0/\Nat.land (Nat.xor c.lok rU) (k1 c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,q13 hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])

lemma jb {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.land a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,q13 hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]

lemma wk {m x y:Nat} (hx:Nat.land m x=0) (hy:Nat.land m y=0) :
   Nat.land m (Nat.lor x y)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hx
 have h2:=congrArg (fun z => z.testBit i) hy
 simp only [nLA,nLO,nTA,nTO,nZT] at h1 h2 ⊢
 revert h1 h2;cases m.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> decide

lemma zz {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u≠p.1 v) :
   yx c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q149,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hne⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vp hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega)]
   cases h1:p.1 (q1 n ((aR n rp c).getD i 0)) <;>
     cases h2:p.1 (q1 n ((aR n rp c).getD (c.k+i) 0)) <;> simp_all
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vp hc,if_neg hi] at htb;cases htb

lemma q6 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) :
   v4 c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q148,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hpu,hpv⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vd hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),hpu,hpv];rfl
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vd hc,if_neg hi] at htb;cases htb

lemma q112 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV0 c (eL rp c g)) i =
     if i < (c.sh1 - c.sh0) / 6 then
       let rows:=aR n rp c
       v6 (g (q1 n (rows.getD (c.sh0+6*i) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 unfold wV0;rw [hc.m0_eq,yy]
 by_cases hi:i < (c.sh1 - c.sh0) / 6
 . simp only [hi,↓reduceIte]
   have htb:∀ off < 6,(wA0 c (eL rp c g)).testBit (6*i+off) =
       g (q1 n ((aR n rp c).getD (c.sh0+6*i+off) 0)):=by
     intro off hoff;unfold wA0
     rw [nLA,nTA,hc.m0all_eq,nTB]
     simp only [show 6*i+off < 6*((c.sh1 - c.sh0) / 6) by omega,decide_true,bATR]
     change ((eL rp c g) >>> c.sh0).testBit (6*i+off)=_
     rw [nTS,← nAA,qm _ _ (by rw [hlen];omega)]
   rw [show 6*i=6*i+0 by omega,htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
       htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)]
   simp only [nAZ]
 . simp [hi]

lemma q111 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV1 c (eL rp c g)) i =
     if i < (c.shTT - c.sh1) / 6 then
       let rows:=aR n rp c
       zq (g (q1 n (rows.getD (c.sh1+6*i) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte]
   rw [qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega)]
 . simp [hi]

lemma zi {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {g:BFn n} {tg:Nat} {r:List (BFn n × Nat)}
   (hs:s<=10)
   (htr:TR f s ((g,tg)::r))
   (hlen:((g,tg)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (wV0 c (eL rp c g))=true:=by
 set rows:=aR n rp c
 set m:=(c.sh1 - c.sh0) / 6
 have hsum:Nat.add (zf c (encWs rows r)) (wV0 c (encL rows g))=zf c (encWs rows ((g,tg)::r)):=by
   simp only [encWs,lMC,zf,lFC,v8];omega
 unfold qb;rw [hsum,hc.a29_0_eq,hc.b5_0_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV0 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV0;rw [hc.m0_eq,yy];split;exact yr _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV0 c p.1) m hf_le (encWs rows ((g,tg)::r)) (by rw [encWs,lLM,hlen];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ((g,tg)::r)).length=s+1:=by rw [encWs,lLM,hlen]
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ((g,tg)::r)).map fun p => z6 (wV0 c p.1) i) =
       ((g,tg)::r).map fun p =>
         v6 (p.1 (q1 n (rows.getD (c.sh0+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q112 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p0_ok i hi
   exact kk htr hlen _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'

lemma vt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)} (hlen:ws.length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (va c (eW rp c ws))=true:=by
 set rows:=aR n rp c
 set m:=(c.shTT - c.sh1) / 6
 unfold z3;rw [hc.a29_1_eq,hc.b5_1_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV1 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh];split;exact q52 _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV1 c p.1) m hf_le (encWs rows ws) (by rw [encWs,lLM];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ws).length=ws.length:=lLM _
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ws).map fun p => z6 (wV1 c p.1) i) =
       ws.map fun p =>
         zq (p.1 (q1 n (rows.getD (c.sh1+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q111 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p1_ok i hi
   exact hsym _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'

abbrev PN (c:Cfg) (w tg:Nat) (l2:List (Nat × Nat)) (pl2:PList):PList :=
 PList.cons w tg (wi c w) (q63 c w) (k1 c w) (wC c w) (wU c w) (wA0 c w) (wV0 c w) (wV1 c w)
   (yx c l2) (v4 c l2) (zf c l2) (va c l2) pl2

inductive PListSpec (c:Cfg):PList->List (Nat × Nat)->Prop where
 | nil:PListSpec c PList.nil []
 | cons (w tg:Nat) (tl:PList) (rest:List (Nat × Nat)) :
     PListSpec c tl rest ->
     PListSpec c
       (PN c w tg rest tl)
       ((w,tg)::rest)

lemma q82 (c:Cfg) (ws:List (Nat × Nat)) :
   ∃ pl,kt c ws=(yx c ws,v4 c ws,zf c ws,va c ws,pl)/\PListSpec c pl ws:=by
 induction ws with
 | nil => exact ⟨PList.nil,rfl,PListSpec.nil⟩
 | cons p rest ih =>
   rcases p with ⟨w,tg⟩;obtain ⟨tl,htl,hsp⟩:=ih
   refine ⟨_,?_,PListSpec.cons w tg tl rest hsp⟩;simp only [kt,htl];rfl

lemma PListSpec.pToList {c:Cfg} {pl:PList} {ws:List (Nat × Nat)} (h:PListSpec c pl ws) :
   pToList pl=ws:=by
 induction h with | nil => rfl | cons _ _ _ _ _ ih => exact congrArg _ ih

lemma q84 (c:Cfg) (ws:List (Nat × Nat)) (a ta alo nahi a0 v0a:Nat)
   (pre mid:List (Nat × Nat)) (pmU pmV0:Nat) (pl:PList) :
   we c ws a ta alo nahi a0 v0a pmU pmV0 pl =
     vx c ws (fun _ => true) a ta alo nahi a0 v0a pre pmU pmV0 mid pl:=by
 induction pl generalizing pmU pmV0 mid with
 | nil => rfl
 | cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post ih =>
   simp only [we,vx]
   have hor :
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          okOrB&&qj c.all1v ws w||!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)
        else false) =
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          if (okOrB&&qj c.all1v ws w&&true)=true then true
          else if (!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land blo).beq 0 <;> cases qj c.all1v ws (a.lor b) <;>
         cases ta.beq 1 <;> cases tb.beq 1 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.lor b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0)) <;> rfl
       . split <;> simp
   have hand :
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          okAndB&&qj c.all1v ws w||ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)
        else false) =
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          if (okAndB&&qj c.all1v ws w&&true)=true then true
          else if (ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land nbhi).beq 0 <;> cases qj c.all1v ws (a.land b) <;>
         cases ta.beq 0 <;> cases tb.beq 0 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.land b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0)) <;> rfl
       . split <;> simp
   rw [hor,hand,ih ((b,tb)::mid) (Nat.lor pmU ub) (Nat.add pmV0 v0b)]

lemma q140 (c:Cfg) (ws:List (Nat × Nat)) (preU preV0:Nat) (pre:List (Nat × Nat)) (pl:PList) :
   q26 c ws preU preV0 pl=js c ws (fun _ => true) preU preV0 pre pl:=by
 induction pl generalizing preU preV0 pre with
 | nil => rfl
 | cons a ta alo ahi nahi ca ua a0 v0a v1a postC postU postV0 postV1 suf ih =>
   simp only [q26,js,q84 c ws a ta alo nahi a0 v0a pre [] preU preV0 suf]
   split;rfl;exact ih _ _ _

lemma wu (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) :
   scanInline c s ws=scanAll c s ws (fun _ => true):=by
 unfold scanInline scanAll
 split
 . rfl
 . cases kt c ws with
   | mk totC r1 => cases r1 with
   | mk totU r2 => cases r2 with
   | mk totV0 r3 => cases r3 with
   | mk totV1 pl =>
     dsimp only
     cases Nat.sub (Nat.add s 2) (q164 ws) with
     | zero => rfl
     | succ d =>
       cases d with
       | zero =>
         cases z3 c totV1
         . simp only [bFT,↓reduceIte];rw [q140 c ws 0 0 []]
         . rfl
       | succ d2 => cases d2 <;> rfl

lemma y8 {α:Type} (x : α) (a b:List α):(x::a++b).Perm (a++x::b) :=
 List.perm_middle.symm

lemma v7 {α:Type} (p:List α) (x : α) (a b:List α) :
   (p++x::a++b).Perm (p++a++x::b):=by
 simpa [lAA] using (lPM (a:=x) (l₁:=a) (l₂:=b)).symm.append_left p

lemma q130 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w7 c ws onSurv (v4 c (pre++l1)) (zf c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w7 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w7;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q128 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w6 c ws onSurv (yx c (pre++l1)) (v4 c (pre++l1)) (zf c (pre++l1)) (va c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w6 c ws onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w6;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q126 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w5 c ws onSurv (yx c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w5 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w5;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q132 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold ke;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q97 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q98 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q98;apply q5
     apply q132 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q98;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q105 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold vx;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q65 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   js c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold js;apply q5
     apply q105 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold js;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q131 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV0 pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid))
   (hV0:pmV0=zf c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmC pmU pmV0 pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV0 pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kd;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q95 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q96 c ws hasUp onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q96;apply q5
     apply q131 c ws hasUp onSurv a ta pre mid l2 [] b tb preC preU preV0 preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV0]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q96;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q129 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre pmC pmU pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kc;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q93 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q94 c ws hasUp totV0 onSurv preC preU preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q94;apply q5
     apply q129 c ws hasUp totV0 onSurv a ta pre mid l2 [] b tb preC preU preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q94;apply q4
     apply ih ((w,tg)::pre) _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q127 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2)) (hC:pmC=yx c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre
       (yx c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre pmC mid pl=true:=by
 induction m1 generalizing mid pmC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold k9;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q91 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q92 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q92;apply q5
     apply q127 c ws onSurv a ta pre mid l2 [] b tb preC tl htl (by simp [hC])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q92;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2

lemma q81 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (htr:TR f 1 ws) :
   j6 c (eW rp c ws)=true:=by
 set rows:=aR n rp c
 have hlen_rows:=zl n rp c.shTT
 rcases htr.inv_succ with
   ⟨a,ta,r,save,hperm,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases save <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hinv,_⟩,rfl⟩:=heq
     rw [List.perm_singleton.1 hperm];simp only [encWs,lMC,List.map_nil,j6,Nat.beq_eq]
     rw [← qv hc,hinv,hc.goalv_eq]
   . cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hj,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . left;rw [← qc,hj,hc.goalv_eq]
     . left;rw [q7,← qc,hj,hc.goalv_eq]
   all_goals cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hm,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . right;rw [← q9,hm,hc.goalv_eq]
     . right;rw [q108,← q9,hm,hc.goalv_eq]
   all_goals cases heq.2

lemma jc {α:Type} {a w : α} {ta:Nat} {r:List (α × Nat)} {save:Bool}
   (h:AllTagsLe3 ((a,ta)::r)):AllTagsLe3 ((w,if ta=3 then 2 else 0)::qk save (a,0) r):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . exact h p (List.mem_cons_of_mem _ hp3)

lemma k5 {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;split <;> omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;split <;> omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))

lemma yw {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))

lemma kv {n:Nat} (a b:BFn n):joinF a b=joinF b a:=by funext x;simp [joinF,Bool.or_comm]

lemma ku {n:Nat} (a b:BFn n):meetF a b=meetF b a:=by funext x;simp [meetF,Bool.and_comm]

lemma q137 {α:Type} (ka kb:Bool) (a b : α) (r:List α) :
   (qk ka a (qk kb b r)).Perm (qk kb b (qk ka a r)):=by
 cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte]
 . exact lPR _
 . exact lPR _
 . exact lPR _
 . exact List.Perm.swap _ _ _

lemma ql {α:Type} (l1 mid l2:List α) (a b : α) :
   (l1++a::mid++b::l2).Perm (a::b::(l1++mid++l2)):=by
 have h1:(l1++a::(mid++b::l2)).Perm (a::(l1++mid++b::l2)):=by
   simpa [lAA] using (lPM (a:=a) (l₁:=l1) (l₂:=mid++b::l2))
 have h2:(l1++mid++b::l2).Perm (b::(l1++mid++l2)) :=
   lPM (a:=b) (l₁:=l1++mid) (l₂:=l2)
 simpa [lAA] using h1.trans (lPC a h2)

lemma q135 (a b d:Nat):Nat.lor (Nat.lor d b) a=Nat.lor a (Nat.lor b d):=by
 rw [q7 _ a,q7 d b]

lemma jq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((joinF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.lor (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.lor (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,qc,q169 hc] at h0
 rw [q7];exact h0

lemma wq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((meetF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.land (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.land (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,q9,q121 hc] at h0
 rw [q7];exact h0

lemma zx {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((w,tw)::(x,tx)::r)) :
   Nat.lor (Nat.lor (yx c (eW rp c r)) (wC c (eL rp c x)))
     (wC c (eL rp c w))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp] at h0
 rw [q135];exact h0

lemma zp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (wi c (eL rp c a))=0:=by
 apply q10 hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0

lemma zn {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (k1 c (eL rp c a))=0:=by
 apply jb hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0

lemma yj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)} (hlen:((w,tw)::(x,tx)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,tw)::(x,tx)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h1:=vt hc hlen hsym
 simp only [qy,w1] at h1
 have heq:Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (wV1 c (eL rp c w)) =
     Nat.add (wV1 c (eL rp c w))
       (Nat.add (wV1 c (eL rp c x)) (va c (eW rp c r))):=by
   simp only [v8];omega
 rw [show yg c.sh1 c.m1 c.m12 (eL rp c w)=wV1 c (eL rp c w) from rfl,heq]
 exact h1

lemma k2 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.lor (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0;rw [q7];exact h0

lemma yt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.land (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0;rw [q7];exact h0

lemma kr {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::r))
   (hlen:((joinF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q41,q198] at h0;exact h0

lemma k8 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::r))
   (hlen:((meetF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q40,q171] at h0;exact h0

lemma vq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::(x,tx)::r))
   (hlen:((joinF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q41,q198] at h0;exact h0

lemma vf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::(x,tx)::r))
   (hlen:((meetF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q40,q171] at h0;exact h0

lemma q16 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::r))
   (hlen:((invF a,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0

lemma q15 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::(a,tx)::r))
   (hlen:((invF a,t)::(a,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c a)))
     (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0

lemma jf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w:BFn n} {t:Nat} {r:List (BFn n × Nat)} (hlen:((w,t)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,t)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (va c (eW rp c r)) (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h0:=vt hc hlen hsym
 simp only [qy,w1] at h0;rw [qt] at h0;exact h0

lemma q17 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b)
   (onSurv:List (Nat × Nat)->Bool)
   (hon:∀ zs_b,AllTagsLe3 zs_b ->
     TR f s zs_b ->
     onSurv (eW rp c zs_b)=true) :
   scanAll c s (eW rp c ws_b) onSurv=true:=by
 cases s with
 | zero => unfold scanAll;simp only [q0,↓reduceIte];exact q81 hc htr
 | succ s' =>
   have hs_nz:Nat.beq (s'+1) 0=false:=q2 (Nat.succ_ne_zero s')
   unfold scanAll;simp only [hs_nz,bFT,↓reduceIte]
   obtain ⟨pl,hprep,hsp⟩:=q82 c (eW rp c ws_b)
   rw [hprep];dsimp only;rw [q187,show (eW rp c ws_b).length=ws_b.length from lLM _]
   have hws_len_le:ws_b.length<=s'+3:=htr.len_le
   have hun_split:∀ {a ta r save},ws_b.Perm ((a,ta)::r) ->
       ta≠1->ta≠2->(ta=3->save=false) ->
       invF a≠(fun _ => false)->invF a≠(fun _ => true)->invF a≠a->(∀ x ∈ r,x.1≠invF a) ->
       TR f (s'+1) ((invF a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
       ∃ l1 l2,ws_b=l1++(a,ta)::l2/\(save=true->ta=0) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (invF a))=true /\
         AllTagsLe3 ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) /\
         TR f (s'+1)
           ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)):=by
     intro a ta r save hp h1 h2 h3 h0 h1' hna hnr hsub
     have hvw:=jo hc ws_b (invF a) h0 h1' fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm;exact hnr p hpm2
     have htags':=htags.perm hp
     have hta_le:ta<=3:=htags' (a,ta) (by simp)
     have hsave0:save=true->ta=0:=fun hst => by
       have hne3:ta≠3:=fun e => by rw [h3 e] at hst;cases hst
       omega
     obtain ⟨l1,l2,hws,hrp⟩:=q68 hp
     have hkp:((invF a,if ta=3 then 2 else 0)::qk save (a,0) r).Perm
         ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) :=
       lPC _ (by cases save <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _)
     exact ⟨l1,l2,hws,hsave0,hvw,(jc htags').perm hkp,TagRun.perm hkp hsub⟩
   have hor_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
       joinF a b≠(fun _ => false)->joinF a b≠(fun _ => true)->joinF a b≠a->joinF a b≠b->(∀ x ∈ r,x.1≠joinF a b) ->
       TR f (s'+1)
         ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠2/\tb'≠2/\(ta'=1->ka'=false)/\(tb'=1->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (joinF a' b'))=true /\
         AllTagsLe3 ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (joinF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF b a,0)::qk kb (b,if tb=3 then 1 else 0) (qk ka (a,if ta=3 then 1 else 0) (l1++mid++l2))):=by
         rw [kv b a];apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [kv a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
   have hand_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
       meetF a b≠(fun _ => false)->meetF a b≠(fun _ => true)->meetF a b≠a->meetF a b≠b->(∀ x ∈ r,x.1≠meetF a b) ->
       TR f (s'+1)
         ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠1/\tb'≠1/\(ta'≠0->ka'=false)/\(tb'≠0->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (meetF a' b'))=true /\
         AllTagsLe3 ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (meetF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF b a,if tb=3\/ta=3 then 1 else 0)::qk kb (b,0) (qk ka (a,0) (l1++mid++l2))):=by
         have hcond:(if tb=3\/ta=3 then 1 else 0)=(if ta=3\/tb=3 then 1 else 0):=by
           by_cases h1:ta=3 <;> by_cases h2:tb=3 <;> simp [h1,h2]
         rw [ku b a,hcond]
         apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [ku a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
   have hacc_rest:∀ (l1 mid l2:List (BFn n × Nat)),
       Nat.lor (yx c ([]++eW rp c l1++eW rp c mid)) (yx c (eW rp c l2))=yx c (eW rp c (l1++mid++l2)) /\
       Nat.lor (v4 c ([]++eW rp c l1++eW rp c mid)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++mid++l2)) /\
       Nat.add (zf c ([]++eW rp c l1++eW rp c mid)) (zf c (eW rp c l2))=zf c (eW rp c (l1++mid++l2)) /\
       Nat.add (va c ([]++eW rp c l1++eW rp c mid)) (va c (eW rp c l2))=va c (eW rp c (l1++mid++l2)) /\
       qx ((eW rp c l1).reverse++[]) (qx (eW rp c mid).reverse (eW rp c l2))=eW rp c (l1++mid++l2):=by
     intro l1 mid l2
     refine ⟨?_,?_,?_,?_,?_⟩
     . rw [← vc];simp [encWs,lAA]
     . rw [← zu];simp [encWs,lAA]
     . rw [← zy];simp [encWs,lAA]
     . rw [← y6];simp [encWs,lAA]
     . simp [q18,encWs,lAA]
   generalize hsl:Nat.sub (Nat.add (s'+1) 2) ws_b.length=slack
   cases slack with
   | zero =>
     have hlen:ws_b.length=s'+3:=by simp at hsl;omega
     have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc (qf htr hlen)
     simp only [hup,q0,bTA]
     rcases htr.inv_succ with
       ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
     . have hle:=hsub.len_le;have hp_len:=hp.length_eq
       cases save <;> simp [qk] at hlen hle hp_len <;> omega
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q5
       have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=k2 hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
       have hval0:=kr hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← qc,hvw,bTA]
       exact hsurv
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q4;apply q5
       have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=yt hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
       have hval0:=k8 hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← q9,hvw,hwt,bTA]
       exact hsurv
   | succ slack' =>
     cases slack' with
     | zero =>
       have hlen:ws_b.length=s'+2:=by simp at hsl;omega
       have hlen11:ws_b.length<=11:=by omega
       cases hsym1:z3 c (va c (eW rp c ws_b))
       . have hno_sym : ¬ (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
             3<=(ws_b.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :=
           fun h => by rw [vt hc hlen11 h] at hsym1;cases hsym1
         have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc ((qh htr hlen).resolve_right hno_sym)
         simp only [bFT,↓reduceIte,hup,q0,bTA]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . exfalso;have hle:=hsub.len_le;have hp_len:=hp.length_eq
           cases save
           . apply hno_sym;intro r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hv:=kk hsub (by simp [qk] at hlen hp_len ⊢;omega) r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hle_s:∀ l:List (BFn n × Nat),(l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
                 (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
               intro l;induction l with | nil => simp | cons x t iht => simp only [lMC,List.sum_cons];have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5);omega
             have hs1:=le_trans hv (hle_s _)
             simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs1
             rw [(hp.map _).sum_eq];exact hs1
           . simp [qk] at hlen hle hp_len;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,joinF] at h1s ⊢
               have:=q14 (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=k2 hc hch_up_p
             have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← qc,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [kv] at h0;exact zp hc h0
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))) 0=true:=qz hm2
             split
             . apply q4;apply q4
               simp only [q2 htb1,bNF,hokB,hval0,← qc,hvw,bTA,htb3];exact hsurv
             . simp only [hokB,q2 htb1,bNF,bTA,↓reduceIte,hval0,← qc,hvw,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zp hc (qf hsub' hch_len)
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             simp only [q2 hta1,bNF,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,meetF] at h1s ⊢
               have:=je (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=yt hc hch_up_p
             have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← q9,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [ku] at h0;exact zn hc h0
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))) 0=true:=qz hm2
             have hwt0:(if ta'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by subst htb0;simp [Nat.beq_eq]
             split
             . apply q4;apply q4
               rw [hwt];simp only [qz htb0,hokB,hval0,← q9,hvw,bTA];exact hsurv
             . rw [hwt0];simp only [hokB,qz htb0,bTA,↓reduceIte,hval0,← q9,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zn hc (qf hsub' hch_len)
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             rw [hwt];simp only [qz hta0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
       ·
         simp only [↓reduceIte,bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,_,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+l2.length+1=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           cases save
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc,q168 hc] at h0u
               rw [q7];exact h0u
             have hval0:=q16 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
             apply q130 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 pl hsp' rfl rfl
             intro pl2 hpl2;unfold w7;dsimp only;rw [hpl2.pToList,q18];apply q5
             have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
             have h1v:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [h1u,h1v,lANil,lRR,← kj,q2 hta1,q2 hta2,
               bNF,hch_up,q0,hval0,← qv hc,hvw,hta3b,bTA]
             exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=jq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=k2 hc hcu
               have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← qc,hvw];exact hsurv
             . have hcs':=jf hc (by omega:((joinF a' b',0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← qc,hcs',bOTR,bTA,hvw];exact hsurv
               . simp only [hcov,q0,← qc,hcs',bTA,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               rw [kv] at hcu;exact zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             simp only [q2 htb1,bNF,hm2,q0,hval0,← qc,hvw,bTA,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             simp only [q2 hta1,bNF,hm1,q0,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=wq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=yt hc hcu
               have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← q9,hvw,hwt];exact hsurv
             . have hcs':=jf hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← q9,hcs',bOTR,bTA,hvw,hwt];exact hsurv
               . simp only [hcov,q0,← q9,hcs',bTA,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               rw [ku] at hcu;exact zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             rw [hwt];simp only [qz htb0,hm2,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             rw [hwt];simp only [qz hta0,hm1,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
     | succ slack'' =>
       cases slack'' with
       | zero =>
         have hlen:ws_b.length=s'+1:=by simp at hsl;omega
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hl_eq:l1.length+l2.length+1=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q128 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold w6;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
           have h1v0:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
           have h1v1:Nat.add (va c ([]++eW rp c l1)) (va c (eW rp c l2))=va c (eW rp c (l1++l2)):=by rw [← y6];simp [encWs]
           simp only [h1c,h1u,h1v0,h1v1,lANil,lRR,q2 hta1,q2 hta2,
             bOS,bFT,↓reduceIte,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+1:=by simp;omega
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hor_u:(Nat.beq (Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))) c.lok ||
                 z3 c (Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a))))=true:=by
               rcases qh hsub' hch_len with hcu | hcs
               . have h0u:=q6 hc hcu
                 simp only [qy,vo,qv hc,q168 hc] at h0u
                 rw [q7] at h0u;rw [h0u,q0];rfl
               . have h1s:=vt hc (by omega:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length<=11) hcs
                 simp only [qy,w1,qv hc,q200 hc] at h1s
                 have hcomm:Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a)) =
                     Nat.add (wV1 c (eL rp c a)) (va c (eW rp c (l1++l2))):=by simp;omega
                 rw [hcomm,h1s];simp
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,hor_u,← qv hc,hvw,hta3b,← kj,bTA];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl
             rw [h03] at htc hsub'
             have hch_len:((invF a,0)::(a,0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc] at h0u
               rw [← qq,q78 hc,q7] at h0u;exact h0u
             have hval0:=q15 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hta0,q0,hch_up,hval0,← qv hc,hvw,← kj,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=jq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← qc,hvw,bTA,bOT]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
                 rw [kv] at hcu;exact zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               simp only [q2 htb1,bNF,hcov,hm2,q0,bTOR,← qc,hvw,htb3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,htb3b,bTA];exact hsurv
               . right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,hvw,htb3b,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               simp only [q2 hta1,bNF,hcov,hm1,q0,bTOR,← qc,hvw,hta3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,hta3b,bTA];exact hsurv
               . left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,hvw,hta3b,bTA];exact hsurv
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have htot_eq:zf c (eW rp c ((a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)))=zf c (eW rp c ws_b):=by
               have h1:zf c (eW rp c ws_b)=zf c (eW rp c ((a',ta')::(b',tb')::(l1++mid++l2))):=by
                 rw [hws];exact vu c ((ql l1 mid l2 _ _).map _)
               rw [h1];rfl
             have hval0:=kr hc hs hsub' hch_len;rw [htot_eq] at hval0
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [q2 hta1,q2 htb1,bNF,hval0,← qc,hvw,hta3b,htb3b,bTA]
             exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=wq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← q9,hvw,bTA,bOT,hwt_or]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
                 rw [ku] at hcu;exact zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               rw [hwt_or];simp only [qz htb0,hcov,hm2,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               rw [hwt_or];simp only [qz hta0,hcov,hm1,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_len:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             have hval0:=k8 hc hs (TagRun.perm hch_perm hsub') (by rw [← hch_perm.length_eq];exact hch_len)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [hta0,htb0,q0,hval0,← q9,hvw,bTA];exact hsurv
       | succ _ =>
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q126 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 pl hsp' rfl
           intro pl2 hpl2;unfold w5;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           simp only [h1c,lANil,lRR,q2 hta1,q2 hta2,
             bNF,bTA,← qv hc,hvw,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,bTA,hta3b,← kj];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl;rw [h03] at htc hsub'
             have hch_perm:((invF a,0)::(a,0)::(l1++l2)).Perm ((invF a,0)::ws_b) :=
               lPC _ (by rw [hws,hta0];exact List.perm_middle.symm)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hta0,q0,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← qc,hvw,bOT]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [jq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;right;simp only [q2 htb1,bNF,hcov,q0,htb3b,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;left;right;simp only [q2 hta1,bNF,hcov,q0,hta3b,bTA];exact hon _ htc hsub'
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             right;simp only [q2 hta1,q2 htb1,bNF,hta3b,htb3b,bTA];exact hon _ htc hsub'
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q4;apply q5
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← q9,hvw,bOT,hwt_or]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [wq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;right;simp only [qz htb0,q0,hcov,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;left;right;simp only [qz hta0,q0,hcov,bTA];exact hon _ htc hsub'
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             right;simp only [hta0,htb0,q0,bTA]
             exact hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')

lemma wj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b) :
   scanInline c s (eW rp c ws_b)=true:=by
 rw [wu]
 exact q17 hc hs htags htr (fun _ => true) (fun _ _ _ => rfl)

def ki {n:Nat}:Nat->List (BFn n × Nat)->BFn n × Nat
 | _,[] => ((fun _ => false),0)
 | 0,a::_ => a
 | k+1,_::rest => ki k rest

def yl {n:Nat}:Nat->List (BFn n × Nat)->List (BFn n × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::yl k rest

def q136 {n:Nat} (code:Nat) (ws:List (BFn n × Nat)):List (BFn n × Nat) :=
 if Nat.ble code 32 then
   let c:=Nat.sub code 1;let i:=Nat.shiftRight c 1;let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=ki i ws;let wt:=if Nat.beq ta 3 then 2 else 0
   let w:=invF a;let r:=yl i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   let rem:=Nat.sub code 33
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=ki i ws;let (b,tb):=ki j ws
   let r:=yl i (yl j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (meetF a b,wt)::r2
   else
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (joinF a b,0)::r2

def q31 {n:Nat} (xs_b:List (BFn n × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (BFn n × Nat)
 | 0,_,_ => xs_b
 | d+1,s,j =>
   let e:=q192 (PT s) j;let code:=Nat.land e 1023
   if Nat.beq code 0 then xs_b
   else q136 code (q31 xs_b PT d (Nat.add s 1) (Nat.land (Nat.shiftRight e 10) 8191))

def RgenB {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat):List (BFn n × Nat) :=
 q31 xs_b PT (Nat.sub cap s) s j

lemma q27 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   jw i (encWs rows ws)=(encL rows (ki i ws).1,(ki i ws).2):=by
 induction i generalizing ws with
 | zero => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ _ => rfl
 | succ k ih => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ t => exact ih t

lemma q28 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   q38 i (encWs rows ws)=encWs rows (yl i ws):=by
 induction i generalizing ws with
 | zero => cases ws <;> rfl
 | succ k ih => cases ws with | nil => rfl | cons p t => simp only [qy,q38,yl,ih]

lemma q153 {n:Nat} (rows:List Nat) (code:Nat) (ws:List (BFn n × Nat)) :
   q203 (2 ^ rows.length - 1) code (encWs rows ws)=encWs rows (q136 code ws):=by
 unfold q203 q136;simp only [v5]
 split
 . simp only [q27,q28];split <;> simp [encWs,q145]
 . simp only [q27,q28]
   split
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,q9]
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,qc]

lemma q119 {n:Nat} (rows:List Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (d s j:Nat) :
   q120 (2 ^ rows.length - 1) (encWs rows xs_b) PT d s j=encWs rows (q31 xs_b PT d s j):=by
 induction d generalizing s j with
 | zero => rfl
 | succ d ih => simp only [q120,q31,v5];split;rfl;rw [ih,q153]

lemma q102 {n:Nat} (rows:List Nat) (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ rows.length - 1) cap (encWs rows xs_b) PT s j=encWs rows (RgenB cap xs_b PT s j) :=
 q119 rows xs_b PT (Nat.sub cap s) s j

lemma q150 {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ (2 ^ n) - 1) cap (encTTWs n xs_b) PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 have hlen:(List.range (2 ^ n)).length=2 ^ n:=List.length_range
 simpa [encTTWs,encWs,encTT,hlen] using q102 (List.range (2 ^ n)) cap xs_b PT s j

lemma wm {n:Nat} (i:Nat) (ws:List (BFn n × Nat)):(yl i ws).Sublist ws:=by
 induction i generalizing ws with
 | zero => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons a (List.Sublist.refl t)
 | succ k ih => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons_cons a (ih t)

lemma vj {α:Type} (b:Bool) (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (if b then x::l else l):=by
 intro p hp;cases b
 . exact hl p hp
 . rcases List.mem_cons.1 hp with rfl | h'
   . exact hx
   . exact hl p h'

lemma vn {α:Type} (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (x::l):=by
 intro p hp;rcases List.mem_cons.1 hp with rfl | h';exact hx;exact hl p h'

lemma q43 {n:Nat} (code:Nat) {ws:List (BFn n × Nat)} (h:AllTagsLe3 ws) :
   AllTagsLe3 (q136 code ws):=by
 unfold q136
 have her:∀ i,AllTagsLe3 (yl i ws):=fun i p hp => h p ((wm i ws).subset hp)
 have her2:∀ i j,AllTagsLe3 (yl i (yl j ws)):=fun i j p hp => her j p ((wm i _).subset hp)
 split
 . dsimp only;split
   . exact vn _ _ (by split <;> omega) (vn _ _ (by omega) (her _))
   . exact vn _ _ (by split <;> omega) (her _)
 . dsimp only;split
   . exact vn _ _ (by split <;> omega)
       (vj _ _ _ (by omega) (vj _ _ _ (by omega) (her2 _ _)))
   . exact vn _ _ (by omega)
       (vj _ _ _ (by split <;> omega) (vj _ _ _ (by split <;> omega) (her2 _ _)))

lemma q59 {n:Nat} (cap:Nat) {xs_b:List (BFn n × Nat)} (h:AllTagsLe3 xs_b)
   (PT:Nat->Nat) (s j:Nat):AllTagsLe3 (RgenB cap xs_b PT s j):=by
 unfold RgenB;generalize Nat.sub cap s=d
 induction d generalizing s j with
 | zero => exact h
 | succ d ih => simp only [q31];split;exact h;exact q43 _ (ih _ _)

lemma q195 (T h fuel lo hi:Nat) (hlo:lo < hi):q167 T h fuel lo hi < hi:=by
 induction fuel generalizing lo hi with
 | zero => exact hlo
 | succ fuel ih =>
   simp only [q167,v5];split
   . rename_i hle;have hle':lo+2<=hi:=Eq.mp Nat.ble_eq hle
     have hdiv:Nat.div (Nat.add lo hi) 2=(lo+hi) / 2:=rfl
     have hmid_lt:Nat.div (Nat.add lo hi) 2 < hi:=by rw [hdiv];omega
     have hlo_lt_mid:lo < Nat.div (Nat.add lo hi) 2:=by rw [hdiv];omega
     split;exact ih _ hi hmid_lt;exact lt_trans (ih lo _ hlo_lt_mid) hmid_lt
   . exact hlo

lemma j8 (NN FL HT:Nat->Nat) (s h:Nat) (hne:q85 NN FL HT s h≠999999) :
   q85 NN FL HT s h < NN s:=by
 unfold q85 at hne ⊢;simp only [v5] at hne ⊢
 cases hz:Nat.beq (NN s) 0
 . rw [hz] at hne;simp only [bFT,↓reduceIte] at hne ⊢
   have hpos : 0 < NN s:=by have:=y3 hz;omega
   cases hm:Nat.beq (q205 (HT s) (q167 (HT s) h (FL s) 0 (NN s))) h
   . rw [hm] at hne;simp only [bFT,↓reduceIte] at hne;exact absurd rfl hne
   . simp only [↓reduceIte];exact q195 (HT s) h (FL s) 0 (NN s) hpos
 . rw [hz] at hne;exact absurd rfl hne

lemma q181 (a b:Nat × Nat):twEq a b=true ↔ a=b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;simp [twEq,Nat.beq_eq]

lemma q142 (x:Nat × Nat) (bs bs':List (Nat × Nat)) (h:jy x bs=some bs'):bs.Perm (x::bs'):=by
 induction bs generalizing bs' with
 | nil => simp [jy] at h
 | cons a t ih =>
   simp only [jy] at h;split at h
   . rename_i heq;cases h;rw [(q181 x a).1 heq]
   . cases he:jy x t with
     | none => rw [he] at h;cases h
     | some r => rw [he] at h;cases h;exact (lPC a (ih r he)).trans (List.Perm.swap x a r)

lemma y5 (xs ys:List (Nat × Nat)) (h:jk xs ys=true):xs.Perm ys:=by
 induction xs generalizing ys with
 | nil => cases ys with | nil => exact List.Perm.nil | cons _ _ => simp [jk] at h
 | cons a t ih =>
   simp only [jk] at h
   cases he:jy a ys with
   | none => rw [he] at h;cases h
   | some ys' => rw [he] at h;exact (lPC a (ih ys' h)).trans (q142 a ys ys' he).symm

lemma q113 (x:Nat × Nat) (xs:List (Nat × Nat)):(q62 x xs).Perm (x::xs):=by
 induction xs with | nil => exact lPR _ | cons a t ih => simp only [q62];split;exact lPR _;exact (lPC a ih).trans (List.Perm.swap x a t)

lemma q64 (xs:List (Nat × Nat)):(q125 xs).Perm xs:=by
 induction xs with | nil => exact List.Perm.nil | cons a t ih => exact (q113 a (q125 t)).trans (lPC a ih)

lemma kg {n:Nat} (rp shTT:Nat) (ws:List (BFn n × Nat)) :
   q72 shTT (encWs (allRows n rp shTT) ws)=encTTWs n ws:=by
 induction ws with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨g,tg⟩;simp only [qy,q49,q72,v5,ih]
   have hsh:=q116 (n:=n) (q106 rp shTT) g
   rw [jj rp shTT] at hsh;rw [allRows,hsh]

lemma yk {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g) (ws:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     wx g (encTTWs n ws)=encTTWs n (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 obtain ⟨π,hbij,hfix,happ⟩:=hg;refine ⟨π,hbij,hfix,?_⟩
 induction ws with | nil => rfl | cons p t ih => rcases p with ⟨h,tg⟩;simp only [q49,lMC,wx,v5,happ,ih]

lemma yv {α β:Type} {f : α->β} (hf:Function.Injective f) :
   ∀ {xs ys:List α},(xs.map f).Perm (ys.map f)->xs.Perm ys
 | [],ys,hp => by cases ys with | nil => exact List.Perm.nil | cons _ _ => exact absurd hp.length_eq (by simp)
 | x::xs,ys,hp => by
   have hmem:f x ∈ ys.map f:=hp.subset (by simp)
   obtain ⟨y,hy,heq⟩:=List.mem_map.1 hmem
   have hxy:y=x:=hf heq;subst hxy
   obtain ⟨l1,l2,rfl⟩:=List.append_of_mem hy
   have hp2:(f y::xs.map f).Perm (f y::(l1++l2).map f) :=
     hp.trans (by simpa [lMA] using (lPM (a:=f y) (l₁:=l1.map f) (l₂:=l2.map f)))
   exact (lPC y (yv hf (List.Perm.cons_inv hp2))).trans List.perm_middle.symm

lemma zv {n:Nat} (xs ys:List (BFn n × Nat)):(encTTWs n xs).Perm (encTTWs n ys) ↔ xs.Perm ys:=by
 constructor
 . intro hp
   have hinj:Function.Injective (fun p:BFn n × Nat => (encTT n p.1,p.2)):=fun ⟨_,_⟩ ⟨_,_⟩ e => by
     simp only [Prod.mk.injEq] at e;exact Prod.ext (yc e.1) e.2
   exact yv hinj hp
 . exact fun hp => hp.map _

lemma q19 {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g)
   (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q69 g ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q69;dsimp only;split
 . obtain ⟨π,hbij,hfix,hmg⟩:=yk hg ws_b;refine ⟨π,hbij,hfix,?_⟩
   have hmap_eq:∀ l,wx g l=l.map (fun p => (ym g p.1,p.2)):=fun l => by
     induction l with | nil => rfl | cons p t ih => simp [wx,v5,ih]
   have hmgp:(wx g ws).Perm (wx g (encTTWs n ws_b)):=by rw [hmap_eq,hmap_eq];exact hp.map _
   exact (q64 _).trans (hmgp.trans (by rw [hmg]))
 . exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hp⟩

lemma q20 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q35 gens ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 induction gens generalizing ws ws_b with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa [q35] using hp⟩
 | cons g rest ih =>
   obtain ⟨π1,hb1,hf1,hp1⟩:=q19 (hgens g (by simp)) ws ws_b hp
   obtain ⟨π2,hb2,hf2,hp2⟩:=ih (fun g' hm => hgens g' (List.mem_cons_of_mem g hm)) (q69 g ws) _ hp1
   exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [q35,lMMp,fCD] using hp2⟩

lemma q152 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws_b:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q186 gens (encTTWs n ws_b)).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q186;have hs0:=q64 (encTTWs n ws_b)
 cases gens with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hs0⟩
 | cons g rest =>
   cases rest with
   | nil => exact q19 (hgens g (by simp)) _ ws_b hs0
   | cons g2 rest2 =>
     obtain ⟨π1,hb1,hf1,hp1⟩:=q20 (g::g2::rest2) hgens _ ws_b hs0
     obtain ⟨π2,hb2,hf2,hp2⟩:=q20 (g::g2::rest2) hgens _ _ hp1
     exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hp2⟩

def w2 {n:Nat} (f:BFn n) (rows:List Nat) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Prop :=
 ∀ s zs_b,findFn s (encWs rows zs_b)=true ->
   ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),
     Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (zs_b.map fun p => ((fun x => p.1 (π x)),p.2)).Perm (R_bfn s j)

lemma q55 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (gens:List (List (Nat × Nat × Nat × Nat))) (hgens:∀ g ∈ gens,vh f g)
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (haut:∀ k,vh f (aut k))
   (NN FL HT PT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutGen shTT salt gens aut Rtt NN FL HT PT):=by
 intro s zs_b h;unfold findAutGen at h;simp only [v5,kg] at h
 split at h;· cases h
 . rename_i hne_b
   have hne:=y3 (Bool.eq_false_iff.2 hne_b)
   set j:=q85 NN FL HT s (q75 salt (q186 gens (encTTWs n zs_b)))
   have hj:j < NN s:=j8 NN FL HT s _ hne
   set aidx:=Nat.shiftRight (q192 (PT s) j) 23
   obtain ⟨π1,hb1,hf1,hori⟩:=q152 gens hgens zs_b
   obtain ⟨π2,hb2,hf2,hmg⟩:=yk (haut aidx) (R_bfn s j)
   rw [hRtt,hmg] at h
   have hperm_b:=(zv _ _).1 (hori.symm.trans (y5 _ _ h))
   obtain ⟨π2_inv,hleft,hright⟩:=Function.bijective_iff_has_inverse.1 hb2
   have hinv_bij:Function.Bijective π2_inv:=Function.bijective_iff_has_inverse.2 ⟨π2,hright,hleft⟩
   have hinv_fix:∀ x,f (π2_inv x)=f x:=fun x => by have:=hf2 (π2_inv x);rw [hright x] at this;exact this.symm
   refine ⟨j,hj,π1 ∘ π2_inv,hb1.comp hinv_bij,fun x => by simp [hf1,hinv_fix],?_⟩
   have hmap_inv:=hperm_b.map (fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2))
   have hrhs:(((R_bfn s j).map fun p => ((fun x => p.1 (π2 x)),p.2)).map fun p => ((fun x => p.1 (π2_inv x)),p.2))=R_bfn s j:=by
     rw [lMMp]
     have hfg:((fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2)) ∘ fun p:BFn n × Nat => ((fun x => p.1 (π2 x)),p.2))=id:=by
       funext ⟨g,tg⟩;simp only [fCD,id];congr 1;funext x;exact congrArg g (hright x)
     rw [hfg,List.map_id]
   rw [hrhs] at hmap_inv
   simpa [lMMp,fCD] using hmap_inv

lemma span_sound (P:Nat->Bool) (len start:Nat) (h:span P len start=true) :
   ∀ i,start<=i->i < start+len->P i=true:=by
 induction len generalizing start with
 | zero => intro i h1 h2;omega
 | succ m ih =>
   simp only [span,bAT] at h;intro i h1 h2
   by_cases heq:i=start
   . subst heq;exact h.1
   . exact ih (start+1) h.2 i (by omega) (by omega)

lemma q179 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (cap:Nat) (hcap:cap<=11) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (R:Nat->Nat->List (Nat × Nat))
   (hR:∀ s j,R s j=eW rp c (R_bfn s j))
   (hTags:∀ s j,AllTagsLe3 (R_bfn s j))
   (findFn:Nat->List (Nat × Nat)->Bool)
   (hFind:w2 f (aR n rp c) NN R_bfn findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true) :
   ∀ s ≤ cap,∀ i < NN s,
     ¬ TR f s (R_bfn s i):=by
 intro s;induction s with
 | zero =>
   intro _ i hi htr;have hb:=hBar 0 (nZL cap) i hi;obtain ⟨tg,heq⟩:=htr.inv_zero
   simp only [bar,hR,heq,encWs,lMC,List.map_nil,hc.goalv_eq,q0] at hb;cases hb
 | succ s ih =>
   intro hs i hi htr
   have hih:=ih (by omega)
   have hb:=hBar (s+1) hs i hi
   simp only [bar,v8] at hb
   have hscan_false:scanAll c s (R (s+1) i)
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=false:=by simpa using hb
   have hscan_true:scanAll c s (eW rp c (R_bfn (s+1) i))
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=true:=by
     apply q17 hc (by omega:s<=10) (hTags (s+1) i) htr
     intro zs_b hzt htr_z
     have hnf:findFn s (eW rp c zs_b)=false:=by
       cases hf:findFn s (eW rp c zs_b)
       . rfl
       . exfalso;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s zs_b hf
         exact hih j hj (TagRun.perm hperm (wp π hbij hfix htr_z))
     simp only [hnf,bNF,bTA]
     cases s with
     | zero => rfl
     | succ s' =>
       simp only [q2 (Nat.succ_ne_zero s'),Bool.false_or]
       exact wj hc (by omega:s'<=10) hzt htr_z
   rw [hR,hscan_true] at hscan_false;cases hscan_false

def checkGenList (n:Nat) (f:BFn n):List (List (Nat × Nat × Nat × Nat))->List (List (Nat × Nat))->Bool
 | [],[] => true
 | sw::sws,ps::pss =>
   kq n ps&&(q163 n ps==sw)&&(ym sw (encTT n f)==encTT n f)&&checkGenList n f sws pss
 | _,_ => false

lemma ye (n:Nat) (f:BFn n) (gsw:List (List (Nat × Nat × Nat × Nat)))
   (gsp:List (List (Nat × Nat))) (h:checkGenList n f gsw gsp=true) :
   ∀ sw ∈ gsw,vh f sw:=by
 induction gsw generalizing gsp with
 | nil => intro _ hm;cases hm
 | cons sw sws ih =>
   cases gsp with
   | nil => simp [checkGenList] at h
   | cons ps pss =>
     simp only [checkGenList,bAT,beq_iff_eq] at h
     obtain ⟨⟨⟨hv,hmk⟩,hfix⟩,hrest⟩:=h
     intro g hg;rcases List.mem_cons.1 hg with rfl | hg2
     . rw [← hmk] at hfix ⊢;exact kw f ps hv hfix
     . exact ih pss hrest g hg2

def checkAutFn (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat))):Bool :=
 (List.range autp.length).all fun i =>
   let ps:=autp.getD i []
   kq n ps&&(q163 n ps==aut i)&&(ym (aut i) (encTT n f)==encTT n f)

lemma q58 (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat))
   (autp:List (List (Nat × Nat))) (h:checkAutFn n f aut autp=true) (hdef:∀ i ≥ autp.length,aut i=[]) :
   ∀ i,vh f (aut i):=by
 intro i;by_cases hi:i < autp.length
 . have h1:=List.all_eq_true.1 h i (List.mem_range.2 hi)
   simp only [bAT,beq_iff_eq] at h1
   obtain ⟨⟨hv,hmk⟩,hfix⟩:=h1;rw [← hmk] at hfix ⊢;exact kw f (autp.getD i []) hv hfix
 . rw [hdef i (by omega)];exact q138 f

def w8 (n:Nat) (f:BFn n):Bool :=
 let t:=encTT n f;!(Nat.beq t 0)&&!(Nat.beq t (2 ^ (2 ^ n) - 1))

lemma ju (n:Nat) (f:BFn n) (h:w8 n f=true) :
   ∃ y y':Fin n->Bool,f y≠f y':=by
 unfold w8 at h;simp only [bAT,bNT,zh] at h
 obtain ⟨hne0,hne1⟩:=h
 have hex1:∃ r < 2 ^ n,f (q1 n r)=true:=by
   by_contra hall;push Not at hall;apply hne0;apply nEQ;intro r
   rw [vr,nZT];split;exact Bool.eq_false_iff.2 (hall r ‹_›);rfl
 have hex0:∃ r < 2 ^ n,f (q1 n r)=false:=by
   by_contra hall;push Not at hall;apply hne1;apply nEQ;intro r
   rw [vr,nTB];split
   . rename_i hr;have:f (q1 n r)=true:=by cases hf:f (q1 n r);exact absurd hf (hall r hr);rfl
     simp [hr,this]
   . rename_i hr;simp [hr]
 obtain ⟨r1,_,h1⟩:=hex1;obtain ⟨r0,_,h0⟩:=hex0
 exact ⟨q1 n r1,q1 n r0,by rw [h1,h0];decide⟩

def q77 (n:Nat) (f:BFn n):Bool :=
 (List.finRange n).all fun v =>
   (List.range (2 ^ n)).any fun r => let x:=q1 n r;f (Function.update x v (!x v))!=f x

lemma q44 (n:Nat) (f:BFn n) (h:q77 n f=true) :
   ∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x:=by
 intro v;have h1:=List.all_eq_true.1 h v (List.mem_finRange v)
 obtain ⟨r,_,hr⟩:=List.any_eq_true.1 h1;exact ⟨q1 n r,bne_iff_ne.1 hr⟩

def q147 (c:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (xs:List (Nat × Nat)) (s0:Nat):Bool :=
 findFn s0 xs||!(Nat.beq s0 0||scanInline c (Nat.sub s0 1) xs)

def verifyBase (n cap:Nat) (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Bool :=
 let rows:=aR n rp c
 let xs_b:=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 Nat.ble cap 11&&w3 n f rp c&&w8 n f&&q77 n f &&
 ((List.finRange n).all fun i => Nat.ble (initTags i) 3) &&
 (xs==encWs rows xs_b)&&(xstt==encTTWs n xs_b) &&
 ((List.range (cap+1)).all fun s0 => Nat.blt (Nat.add s0 1) n||q147 c findFn xs s0)

lemma prove_base {n cap:Nat} (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (NN PT:Nat->Nat) (findFn:Nat->List (Nat × Nat)->Bool)
   (hBase:verifyBase n cap f rp c initTags xs xstt findFn=true)
   (hFind:w2 f (aR n rp c) NN
     (RgenB cap (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)) PT) findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 unfold verifyBase at hBase
 simp only [bAT,Nat.ble_eq,beq_iff_eq] at hBase
 rcases hBase with ⟨⟨⟨⟨⟨⟨⟨hcap,hcfg_b⟩,hnc_b⟩,hdep_b⟩,htags_b⟩,hxs⟩,hxstt⟩,hroots⟩
 have hc:=jn n f rp c hcfg_b
 have hnc:=ju n f hnc_b
 have hdep:=q44 n f hdep_b
 set xs_b:List (BFn n × Nat):=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 have hTags_xs:AllTagsLe3 xs_b:=fun p hp => by
   rw [List.mem_ofFn] at hp;obtain ⟨i,rfl⟩:=hp
   exact Eq.mp Nat.ble_eq (List.all_eq_true.1 htags_b i (List.mem_finRange i))
 have hlen_rows:=zl n rp c.shTT
 have hR:∀ s j,Rgen c.all1v cap xs PT s j=eW rp c (RgenB cap xs_b PT s j):=fun s j => by
   rw [hxs,hc.all1v_eq,← hlen_rows,q102]
 have hNoRun:=q179 hc cap hcap NN (RgenB cap xs_b PT) (Rgen c.all1v cap xs PT) hR
   (fun s j => q59 cap hTags_xs PT s j) findFn hFind hBar
 intro t hcirc;by_contra hlt;have hle:t<=cap:=by omega
 obtain ⟨s0,hs0,htr⟩:=q88 f cap initTags hnc hdep htag t hle hcirc
 have hroot:=List.all_eq_true.1 hroots s0 (List.mem_range.2 (by omega))
 simp only [bOT] at hroot
 rcases hroot with hlen_small | hchk
 . have hlt_n:s0+1 < n:=by simpa [Nat.blt_eq,v8] using hlen_small
   have htr_len:n<=s0+1:=by simpa using htr.len_le
   omega
 . unfold q147 at hchk;simp only [bOT] at hchk
   rcases hchk with hfound | hkill
   . rw [hxs] at hfound;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s0 xs_b hfound
     exact hNoRun s0 hs0 j hj (TagRun.perm hperm (wp π hbij hfix htr))
   . simp only [bNT,Bool.or_eq_false_iff,zh] at hkill
     obtain ⟨hs0_nz,hinl_f⟩:=hkill
     cases s0 with
     | zero => exact hs0_nz rfl
     | succ s' =>
       rw [hxs] at hinl_f;have hinl_t:=wj hc (by omega:s'<=10) hTags_xs htr
       change scanInline c s' (eW rp c xs_b)=false at hinl_f
       rw [hinl_t] at hinl_f;cases hinl_f

lemma Rgen_encTTWs_eq {n all1tt cap:Nat} (hall:all1tt=2 ^ 2 ^ n - 1)
   (xs_b:List (BFn n × Nat)) (xstt:List (Nat × Nat)) (hxs:xstt=encTTWs n xs_b)
   (PT:Nat->Nat) (s j:Nat) :
   Rgen all1tt cap xstt PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 rw [hall,hxs];exact q150 cap xs_b PT s j

lemma span_all_sound {P:Nat->Nat->Bool} {cap:Nat} {NN:Nat->Nat}
   (h:(List.range (cap+1)).all (fun s => span (P s) (NN s) 0)=true) :
   ∀ s ≤ cap,∀ i < NN s,P s i=true:=fun s hs i hi =>
 span_sound (P s) (NN s) 0 (List.all_eq_true.1 h s (List.mem_range.2 (by omega))) i (nZL _) (by omega)

lemma fun_eq_of_encTT {n:Nat} (f g:BFn n) (h:Nat.beq (encTT n f) (encTT n g)=true):f=g :=
 yc (Eq.mp Nat.beq_eq h)

lemma prove_baseGen {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (haut:checkAutFn n f aut autp=true)
   (hdef:∀ i ≥ autp.length,aut i=[])
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q55 f rp c.shTT salt gsw (ye n f gsw gsp hgen)
     aut (q58 n f aut autp haut hdef) NN FL HT PT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag

structure BaseEntry where
 k:Nat
 E:List (Fin k × Fin k)
 lb:Nat

def BaseTableOk (bs:List BaseEntry):Prop :=
 ∀ b ∈ bs,∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s

def q61 {n:Nat}:List (Fin n)->Bool
 | [] => true
 | a::t => !t.contains a&&q61 t

lemma q83 {n:Nat} (l:List (Fin n)) (h:q61 l=true):l.Nodup:=by
 induction l with
 | nil => exact List.nodup_nil
 | cons a t ih =>
   simp only [q61,bAT,bNT] at h
   exact List.nodup_cons.2 ⟨by simpa [List.contains_eq_mem] using h.1,ih h.2⟩

inductive GTree (n:Nat) where
 | emp
 | base (idx:Nat) (π:List Nat)
 | f0 (p:Fin n) (t:GTree n)
 | f1 (p:Fin n) (t:GTree n)
 | b2 (p:Fin n) (t0 t1:GTree n)

def checkGTree (bs:List BaseEntry) (n:Nat)
   (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1))) (req:Nat):GTree (n+1)->Bool
 | GTree.emp => E.isEmpty&&q61 A&&Nat.ble req (A.length - 1)
 | GTree.base idx π =>
   match bs[idx]? with
   | none => false
   | some b =>
     if h : 0 < b.k then
       A.isEmpty&&Nat.ble req b.lb &&
       isoCheck E b.E (fun i => ⟨π.getD i.1 0 % b.k,Nat.mod_lt _ h⟩)
     else false
 | GTree.f0 p t =>
   let A':=fix0A A p;let E':=fix0E E p
   depCheck A E p&&(!A'.isEmpty||!E'.isEmpty)&&checkGTree bs n A' E' (req - 1) t
 | GTree.f1 p t =>
   let A':=fix1A A E p;let E':=fix1E A E p
   depCheck A E p&&!A.contains p&&E.all (fun e => e.1!=e.2) &&
     (!A'.isEmpty||!E'.isEmpty)&&checkGTree bs n A' E' (req - 1) t
 | GTree.b2 p t0 t1 =>
   let A0:=fix0A A p;let E0:=fix0E E p
   let A1:=fix1A A E p;let E1:=fix1E A E p
   depCheck A E p&&!A.contains p&&E.all (fun e => e.1!=e.2) &&
     (!A0.isEmpty||!E0.isEmpty)&&(!A1.isEmpty||!E1.isEmpty) &&
     checkGTree bs n A0 E0 (req - 2) t0&&checkGTree bs n A1 E1 (req - 2) t1

lemma checkGTree_sound (bs:List BaseEntry) (hbs:BaseTableOk bs) {n:Nat}
   (t:GTree (n+1)) (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1))) (req:Nat)
   (h:checkGTree bs n A E req t=true) :
   ∀ s:Nat,HasCircuitSize (n+1) (gfn A E) s->req<=s:=by
 induction t generalizing A E req with
 | emp =>
   simp only [checkGTree,bAT,List.isEmpty_iff] at h
   rcases h with ⟨⟨rfl,hnd⟩,hle⟩
   intro s hs;have h1:=q176 A (q83 A hnd) s hs
   have h2:req<=A.length - 1:=Eq.mp Nat.ble_eq hle;omega
 | base idx π =>
   unfold checkGTree at h
   cases hb:bs[idx]? with
   | none => rw [hb] at h;cases h
   | some b =>
     rw [hb] at h;dsimp only at h
     split at h
     . rename_i hk
       simp only [bAT,List.isEmpty_iff] at h
       rcases h with ⟨⟨rfl,hle⟩,hiso⟩
       have hbmem:b ∈ bs:=List.mem_of_getElem? hb
       intro s hs
       have h1:=q191 E b.E (fun i => ⟨π.getD i.1 0 % b.k,Nat.mod_lt _ hk⟩) hiso (hbs b hbmem) s hs
       have h2:req<=b.lb:=Eq.mp Nat.ble_eq hle;omega
     . cases h
 | f0 p t ih =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨hdep,hnc⟩,hsub⟩
   intro s hs;have h1:=q190 A E p (fix0A A p) (fix0E E p) (req - 1) hdep rfl rfl hnc (ih _ _ _ hsub) s hs;omega
 | f1 p t ih =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨⟨⟨hdep,hpA⟩,hloop⟩,hnc⟩,hsub⟩
   intro s hs;have h1:=q189 A E p (fix1A A E p) (fix1E A E p) (req - 1) hdep hpA hloop rfl rfl hnc (ih _ _ _ hsub) s hs;omega
 | b2 p t0 t1 ih0 ih1 =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨⟨⟨⟨⟨hdep,hpA⟩,hloop⟩,hnc0⟩,hnc1⟩,hsub0⟩,hsub1⟩
   intro s hs
   have h1:=q155 A E p (fix0A A p) (fix0E E p) (fix1A A E p) (fix1E A E p) (req - 2)
     hdep hpA hloop rfl rfl rfl rfl hnc0 hnc1 (ih0 _ _ _ hsub0) (ih1 _ _ _ hsub1) s hs;omega

def checkTags (bs:List BaseEntry) (n cap:Nat) (E:List (Fin (n+1) × Fin (n+1)))
   (initTags:Fin (n+1)->Nat) (trees:List (GTree (n+1))):Bool :=
 (List.finRange (n+1)).all fun v =>
   let tg:=initTags v
   let E0:=fix0E E v
   let tr:=trees.getD v.1 GTree.emp
   Nat.beq tg 0 ||
   (Nat.beq tg 1&&!E0.isEmpty&&checkGTree bs n [] E0 (cap - 1) tr) ||
   (Nat.beq tg 3&&!E0.isEmpty&&checkGTree bs n [] E0 (cap - 2) tr)

lemma checkTags_sound (bs:List BaseEntry) (hbs:BaseTableOk bs) {n cap:Nat}
   (f:BFn (n+1)) (E:List (Fin (n+1) × Fin (n+1))) (initTags:Fin (n+1)->Nat)
   (trees:List (GTree (n+1)))
   (hf:Nat.beq (encTT (n+1) f) (encTT (n+1) (gfn [] E))=true)
   (h:checkTags bs n cap E initTags trees=true) :
   ∀ v:Fin (n+1),initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize (n+1) (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize (n+1) (fun x => f (Function.update x v false)) s'->cap - 2<=s'):=by
 have hfeq:f=gfn [] E:=fun_eq_of_encTT _ _ hf
 intro v
 have hv:=List.all_eq_true.1 h v (List.mem_finRange v)
 simp only [bOT,bAT] at hv
 rcases hv with (h0 | ⟨⟨h1,hnc⟩,htr⟩) | ⟨⟨h3,hnc⟩,htr⟩
 . exact Or.inl (Eq.mp Nat.beq_eq h0)
 . refine Or.inr (Or.inl ⟨Eq.mp Nat.beq_eq h1,?_,?_⟩)
   . have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     obtain ⟨x,y,hxy⟩:=q99 [] (fix0E E v) (by simp [hnc])
     exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
   . intro s' hs'
     have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     rw [hres] at hs';exact checkGTree_sound bs hbs _ [] (fix0E E v) (cap - 1) htr s' hs'
 . refine Or.inr (Or.inr ⟨Eq.mp Nat.beq_eq h3,?_,?_⟩)
   . have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     obtain ⟨x,y,hxy⟩:=q99 [] (fix0E E v) (by simp [hnc])
     exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
   . intro s' hs'
     have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     rw [hres] at hs';exact checkGTree_sound bs hbs _ [] (fix0E E v) (cap - 2) htr s' hs'

lemma baseTable_cons (b:BaseEntry) (bs:List BaseEntry)
   (hb:∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s)
   (hbs:BaseTableOk bs):BaseTableOk (b::bs):=fun x hx => by
 rcases List.mem_cons.1 hx with rfl | hx2;exact hb;exact hbs x hx2


def E_K4:List (Fin 4×Fin 4):=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
abbrev f_K4:=gfn [] E_K4
def r_K4:=0x4020228283080808a0a0c002022428310080890a0c202022428300080860a0c2020218283080808c1218202022848600101090c14404042430500202060a0c0040428305101010a0c142020224303002020c0a0c0020228283100808a0a0c202022828300080890a0c402022428308080890a0c002021828308080860a0c2020230506080808c1218202022848600101090c14404042430500202060a0c0040428305101010a0c1438b1a3878f1e3c78e1a2c3860a0c5090630485182830e1a2c70d0e385871a2c38c14243050630509181828a0c0c48506202020200404040400000004081010204040810102044081010204040810102040000000000080808804044040220202
def x_K4:=[(0x2aaa8b2cf3cf2cb28a1450c104d0cb2cb3cf3cb2c828a1450c107beedb0dbe5927884001c01c0248,0),(0x33331555145155545528a14e39305555545145555345528a14e3b7f76876f6aa5c90800e00e00481,0),(0x3c3c028820a21a69614d33934e23820a20828869a59614d33934effb85bbdb34e921007007000812,0),(0x3fc02410490400018612440490450490412410000618612440491ffc36df6dc79242038038000124,0)]
def xt_K4:=[(0xaaaa,0),(0xcccc,0),(0xf0f0,0),(0xff00,0)]
def tg_K4:Fin 4->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>0
def c_K4:Cfg:=⟨55,110,218,302,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fba071c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffff80000000000000,0x7fffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_K4:Nat->Nat
 | 3=>2
 | 4=>3
 | 5=>1
 | _=>0
def L_K4:Nat->Nat
 | 3=>2
 | 4=>3
 | 5=>0
 | _=>0
def H_K4:Nat->Nat
 | 3=>0xd6b949c9409e
 | 4=>0x73fe3c4f63d4204318
 | 5=>0xc9409e
 | _=>0
def P_K4:Nat->Nat
 | 3=>0x80043900000835
 | 4=>0x240000002809000001
 | 5=>0x0
 | _=>0
def gs_K4:List (List (Nat×Nat×Nat×Nat)):=[[(4,0xf00,0xf0,0xf00f)],[(2,0x3030,0xc0c,0xc3c3)],[(4,0xf00,0xf0,0xf00f),(2,0x3030,0xc0c,0xc3c3)],[(4,0xf00,0xf0,0xf00f),(6,0x3300,0xcc,0xcc33)],[(6,0x3300,0xcc,0xcc33)],[(1,0x4444,0x2222,0x9999)]]
def gsp_K4:List (List (Nat×Nat)):=[[(2,3)],[(1,2)],[(2,3),(1,2)],[(2,3),(1,3)],[(1,3)],[(0,1)]]
def au_K4:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(4,0xf00,0xf0,0xf00f)]
 | 2=>[(2,0x3030,0xc0c,0xc3c3)]
 | 3=>[(4,0xf00,0xf0,0xf00f),(2,0x3030,0xc0c,0xc3c3)]
 | 4=>[(4,0xf00,0xf0,0xf00f),(6,0x3300,0xcc,0xcc33)]
 | 5=>[(6,0x3300,0xcc,0xcc33)]
 | 6=>[(1,0x4444,0x2222,0x9999)]
 | 7=>[(4,0xf00,0xf0,0xf00f),(1,0x4444,0x2222,0x9999)]
 | 8=>[(2,0x3030,0xc0c,0xc3c3),(1,0x4444,0x2222,0x9999)]
 | 9=>[(4,0xf00,0xf0,0xf00f),(2,0x3030,0xc0c,0xc3c3),(1,0x4444,0x2222,0x9999)]
 | 10=>[(4,0xf00,0xf0,0xf00f),(6,0x3300,0xcc,0xcc33),(1,0x4444,0x2222,0x9999)]
 | 11=>[(6,0x3300,0xcc,0xcc33),(1,0x4444,0x2222,0x9999)]
 | 12=>[(2,0x3030,0xc0c,0xc3c3),(3,0x5050,0xa0a,0xa5a5)]
 | 13=>[(4,0xf00,0xf0,0xf00f),(2,0x3030,0xc0c,0xc3c3),(3,0x5050,0xa0a,0xa5a5)]
 | 14=>[(3,0x5050,0xa0a,0xa5a5)]
 | 15=>[(4,0xf00,0xf0,0xf00f),(3,0x5050,0xa0a,0xa5a5)]
 | 16=>[(6,0x3300,0xcc,0xcc33),(3,0x5050,0xa0a,0xa5a5)]
 | 17=>[(4,0xf00,0xf0,0xf00f),(6,0x3300,0xcc,0xcc33),(3,0x5050,0xa0a,0xa5a5)]
 | 18=>[(4,0xf00,0xf0,0xf00f),(6,0x3300,0xcc,0xcc33),(7,0x5500,0xaa,0xaa55)]
 | 19=>[(6,0x3300,0xcc,0xcc33),(7,0x5500,0xaa,0xaa55)]
 | 20=>[(4,0xf00,0xf0,0xf00f),(7,0x5500,0xaa,0xaa55)]
 | 21=>[(7,0x5500,0xaa,0xaa55)]
 | 22=>[(4,0xf00,0xf0,0xf00f),(2,0x3030,0xc0c,0xc3c3),(7,0x5500,0xaa,0xaa55)]
 | 23=>[(2,0x3030,0xc0c,0xc3c3),(7,0x5500,0xaa,0xaa55)]
 | _=>[]
def ap_K4:List (List (Nat×Nat)):=[[],[(2,3)],[(1,2)],[(2,3),(1,2)],[(2,3),(1,3)],[(1,3)],[(0,1)],[(2,3),(0,1)],[(1,2),(0,1)],[(2,3),(1,2),(0,1)],[(2,3),(1,3),(0,1)],[(1,3),(0,1)],[(1,2),(0,2)],[(2,3),(1,2),(0,2)],[(0,2)],[(2,3),(0,2)],[(1,3),(0,2)],[(2,3),(1,3),(0,2)],[(2,3),(1,3),(0,3)],[(1,3),(0,3)],[(2,3),(0,3)],[(0,3)],[(2,3),(1,2),(0,3)],[(1,2),(0,3)]]
lemma ok_K4:(List.range 6).all (fun s=>span ((bar c_K4 (findAutGen c_K4.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_K4 au_K4 (Rgen 0xffff 5 xt_K4 P_K4) N_K4 L_K4 H_K4 P_K4) (Rgen c_K4.all1v 5 x_K4 P_K4)) s) (N_K4 s) 0)=true:=by decide +kernel
lemma lb_K4:∀ t,HasCircuitSize 4 f_K4 t->6<=t:=prove_baseGen f_K4 r_K4 0x9e3779b97f4a7c15f39cc0605cedc835 c_K4 (fun _=>0) x_K4 xt_K4 gs_K4 gsp_K4 au_K4 ap_K4 N_K4 L_K4 H_K4 P_K4 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 24<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_K4) (fun _=>Or.inl rfl)


def E_K4e:List (Fin 4×Fin 4):=[(0,1),(0,2),(0,3),(1,2),(1,3)]
abbrev f_K4e:=gfn [] E_K4e
def r_K4e:=0x1060a121420c0428485103010a0c14004182430510106090c14004042430510101090c1400c042430508301090c140080818283001010a0c144040428305003010a0c1420c0428305001060a121820c0228486080808a12186020228486001060a121420c0428485103010a0c14004182430510106090c14004042430510101090c1400c042430508301090c140080818283001010a0c144040428305003010a0c1420c04283050e2c68e1e0c5871e182831e284831e3c70d161c485141878e1a2c70d0e385871a2c38a1218283142430514243051c283031a242831010101003060c102040808102040404000000010202046081020204080810202040800000000183060c040410118202011820202
def x_K4e:=[(0xaaaa0c304514514514304104108a28a0c3045145145143041041efbbdf2dbeb551f100040c00e00510,0),(0xcccc10c38208a28a28538e38e14555510c38208a28a28538e38edfddecf6f75aaf1200083007000a01,0),(0xf0f06714db6d34d3cce4d34f36718616714db6d34d3cce4d34f3b9e8f57bda633aa470f0023800f0aa,0),(0xff00396d0cb049145101245143961a6396d0cb049145101245147a8efabf6d8cccc87f0003c000f0cc,0)]
def xt_K4e:=[(0xaaaa,0),(0xcccc,0),(0xf0f0,0),(0xff00,0)]
def tg_K4e:Fin 4->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>0
def c_K4e:Cfg:=⟨60,120,228,312,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xeee81c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7fffffffffffffff000000000000000,0xfffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_K4e:Nat->Nat
 | 3=>1
 | 4=>1
 | _=>0
def L_K4e:Nat->Nat
 | 3=>0
 | 4=>0
 | _=>0
def H_K4e:Nat->Nat
 | 3=>0xc9409e
 | 4=>0xc9409e
 | _=>0
def P_K4e:Nat->Nat
 | 3=>0x0
 | 4=>0x0
 | _=>0
def gs_K4e:List (List (Nat×Nat×Nat×Nat)):=[[(4,0xf00,0xf0,0xf00f)],[(1,0x4444,0x2222,0x9999)],[(4,0xf00,0xf0,0xf00f),(1,0x4444,0x2222,0x9999)]]
def gsp_K4e:List (List (Nat×Nat)):=[[(2,3)],[(0,1)],[(2,3),(0,1)]]
def au_K4e:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(4,0xf00,0xf0,0xf00f)]
 | 2=>[(1,0x4444,0x2222,0x9999)]
 | 3=>[(4,0xf00,0xf0,0xf00f),(1,0x4444,0x2222,0x9999)]
 | _=>[]
def ap_K4e:List (List (Nat×Nat)):=[[],[(2,3)],[(0,1)],[(2,3),(0,1)]]
lemma ok_K4e:(List.range 5).all (fun s=>span ((bar c_K4e (findAutGen c_K4e.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_K4e au_K4e (Rgen 0xffff 4 xt_K4e P_K4e) N_K4e L_K4e H_K4e P_K4e) (Rgen c_K4e.all1v 4 x_K4e P_K4e)) s) (N_K4e s) 0)=true:=by decide +kernel
lemma lb_K4e:∀ t,HasCircuitSize 4 f_K4e t->5<=t:=prove_baseGen f_K4e r_K4e 0x9e3779b97f4a7c15f39cc0605cedc835 c_K4e (fun _=>0) x_K4e xt_K4e gs_K4e gsp_K4e au_K4e ap_K4e N_K4e L_K4e H_K4e P_K4e rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 4<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_K4e) (fun _=>Or.inl rfl)

def bases4:List BaseEntry:=[⟨4,E_K4,6⟩,⟨4,E_K4e,5⟩]
lemma bases4Ok:BaseTableOk bases4:=
  baseTable_cons _ _ lb_K4 (  baseTable_cons _ _ lb_K4e (fun _ h => by cases h))


def E_C0:List (Fin 5×Fin 5):=[(0,2),(1,3),(2,3),(0,4),(1,4),(2,4),(3,4)]
abbrev f_C0:=gfn [] E_C0
def r_C0:=0x10108142430404206088c101081422304022060a0a10088142428402206088a100881222282012060a05080481424142012060885080481222144042060a0c100881824282012050885080481118142011244605080448c1414404206090c10108142430404206088c101081422304022060a0a10088142428402206088a100881222282012060a05080481424142012060885080481222144042060a0c1008818242820120508853a60b92223c51f3464b151c34f1b305ca111e3029d3660b94243c60a3868c962a4c70d161c60a0a70d192c5499d363ce1a323868b3c5c79c2c5470d0e6cb8f345898e161cc952634587305091118282982230505284860a0a4888a0a64c16284c911303860b145068c0e1490b144438508102040810203060c183060c102040810204081010204081020408100000000000000000081020408102040809122440810204080c183040810204080c1830408102040808102040810000000000000912244890c183060c0c1830624406080c1012018203044048806048091040304
def x_C0:=[(0xaaaaaaaa0020800020914534c001355d6400020800020914534c0013ad555ba42dc97cb65f2ff1290ac512d701fc01ff00001c000703f01f07c512d0,0),(0xcccccccc0800114d15400801004c00000820800114d15400801004c037ab48ad56d2ad5eaffcb242551658ba01fffe000000000e07fc0000ff965882,0),(0xf0f0f0f05515421000239618530258e3951551542100023961853025a53e6f369b6cd66ffb5554a5a89867c3fe0000000000000ff8000000f8186003,0),(0xff00ff0086586586584400402594008a3a5865865865844004025940c7cf8dc7e3b71ffb359a68d63160fb180000000000001ff00000001f00600318,0),(0xffff000038e38e38e38e38e38e38e30400e38e38e38e38e38e38e38ef9f3f1f8fc07fb8dc6e38f18c67f842400000000003fe0000000000000008424,0)]
def xt_C0:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def tg_C0:Fin 5->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>0 | 4=>0
def c_C0:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffefca01c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C0:Nat->Nat
 | 4=>2
 | 5=>2
 | 6=>1
 | _=>0
def L_C0:Nat->Nat
 | 4=>2
 | 5=>2
 | 6=>0
 | _=>0
def H_C0:Nat->Nat
 | 4=>0x39476a1d5e81
 | 5=>0xe8c5291ab02e
 | 6=>0x6ed0be
 | _=>0
def P_C0:Nat->Nat
 | 4=>0x8000420000004a
 | 5=>0x4c0080003a
 | 6=>0x0
 | _=>0
def gs_C0:List (List (Nat×Nat×Nat×Nat)):=[[(4,0xf000f00,0xf000f0,0xf00ff00f),(1,0x44444444,0x22222222,0x99999999)]]
def gsp_C0:List (List (Nat×Nat)):=[[(2,3),(0,1)]]
def au_C0:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(4,0xf000f00,0xf000f0,0xf00ff00f),(1,0x44444444,0x22222222,0x99999999)]
 | _=>[]
def ap_C0:List (List (Nat×Nat)):=[[],[(2,3),(0,1)]]
lemma ok_C0:(List.range 7).all (fun s=>span ((bar c_C0 (findAutGen c_C0.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C0 au_C0 (Rgen 0xffffffff 6 xt_C0 P_C0) N_C0 L_C0 H_C0 P_C0) (Rgen c_C0.all1v 6 x_C0 P_C0)) s) (N_C0 s) 0)=true:=by decide +kernel
lemma lb_C0:∀ t,HasCircuitSize 5 f_C0 t->7<=t:=prove_baseGen f_C0 r_C0 0x9e3779b97f4a7c15f39cc0605cedc835 c_C0 (fun _=>0) x_C0 xt_C0 gs_C0 gsp_C0 au_C0 ap_C0 N_C0 L_C0 H_C0 P_C0 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C0) (fun _=>Or.inl rfl)


def E_C1:List (Fin 5×Fin 5):=[(1,2),(0,3),(2,3),(1,4),(2,4),(3,4)]
abbrev f_C1:=gfn [] E_C1
def r_C1:=0x202029418240041460606201051818180041430486080450c12184012260a09100489824244010a50609104429418242021460606080850c12184042260a0c08088942418202144860608088921818404226090c1010894243008a0a50609222829418242022260a06080889824182022250486080889212184012260a09100489824244010a506091044294182420214606060808512181820214304861010898283020222509063a60b921e24f9a3258a8e1a78d982e5078c1274d982e5090f1818e1a3258a931c345873a6cb9c3464b152678d8f3868c8e1a2ce971e70b151c3439b2e3cd162638587325498d161cc142430486305090930486090c506090c484863460a942648c981a305892a5070c0e189920e1858908102040810183060c183060810204081020404081020408102040000000000000000022448902040810202850a102040810202850a102040810203060c10204081020204081020400000000002244891142850a14142850a0c183142028406088900a10181224050806088900a10508
def x_C1:=[(0xaaaaaaaa240002499659640088200208229a4820a299659640002208aeaaae90b7e5b2f97cbfc211122ab8ab03f807fc00e000381c0fc0f07f2ab8a8,0),(0xcccccccc0092492400800196404dd5420904114d15400800197590133b56a2b55b6af55abff2c9248d8c22fe03fff800000070001ff0000f878c22c2,0),(0xf0f0f0f03934d594200e3a39539638d154e3a386584200e3a38e54e5aa7cf4de6db359bfed555542e930cfccfc0000000000003fe00000007830c00c,0),(0xff00ff004ce38e3a59638ce3a500a0a58534c41020a59638ce28e940cf9f3f1b8edc7fecd669a69b32c3f3030000000000007fc00000000f80c00303,0),(0xffff000090490000e38450400e38430e38490e38c30e38450410038ef3e7c7e3f0ffee371b8e38ec44ff0c300000000000ff8000000000f000030c30,0)]
def xt_C1:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def tg_C1:Fin 5->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>0 | 4=>0
def c_C1:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffcfac01c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C1:Nat->Nat
 | 4=>9
 | 5=>7
 | 6=>1
 | _=>0
def L_C1:Nat->Nat
 | 4=>5
 | 5=>4
 | 6=>0
 | _=>0
def H_C1:Nat->Nat
 | 4=>0xe255fdb2eb838cb814825c356ed0bf5a43ec488614398b99097693
 | 5=>0xe8c529ca81c088cb61740de8706c896ed0be37efce
 | 6=>0x6ed0be
 | _=>0
def P_C1:Nat->Nat
 | 4=>0x8420080004200000c710000103100001435008010390000103a0000004a00000c51
 | 5=>0x4c000000640000003e0000006800000042000000000000002a
 | 6=>0x0
 | _=>0
def gs_C1:List (List (Nat×Nat×Nat×Nat)):=[[(12,0xf0f0000,0xf0f0,0xf0f00f0f)]]
def gsp_C1:List (List (Nat×Nat)):=[[(2,4)]]
def au_C1:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(12,0xf0f0000,0xf0f0,0xf0f00f0f)]
 | _=>[]
def ap_C1:List (List (Nat×Nat)):=[[],[(2,4)]]
lemma ok_C1:(List.range 7).all (fun s=>span ((bar c_C1 (findAutGen c_C1.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C1 au_C1 (Rgen 0xffffffff 6 xt_C1 P_C1) N_C1 L_C1 H_C1 P_C1) (Rgen c_C1.all1v 6 x_C1 P_C1)) s) (N_C1 s) 0)=true:=by decide +kernel
lemma lb_C1:∀ t,HasCircuitSize 5 f_C1 t->7<=t:=prove_baseGen f_C1 r_C1 0x9e3779b97f4a7c15f39cc0605cedc835 c_C1 (fun _=>0) x_C1 xt_C1 gs_C1 gsp_C1 au_C1 ap_C1 N_C1 L_C1 H_C1 P_C1 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C1) (fun _=>Or.inl rfl)


def E_C2:List (Fin 5×Fin 5):=[(0,2),(1,3),(1,4),(2,4),(3,4)]
abbrev f_C2:=gfn [] E_C2
def r_C2:=0x223031414142090c50505001089828144042260a05001089424142022250905024461814140910c48505022431214148890c48505083019214142012260a0508048942414402226090a0230192141488c0648505082419214141111860a1220208982428404226090a20088982428202226090a20086182848008226090a00088982428401226090a040489824284022260a0a100889424282012260a0508048942414402226090a243c51f3464b151c34f1b305ca0f0a74d982e5090f1470d192c5498e1a2c39d365ce1a3258a933c7479d363ce1a323868b3c5c79c2c5470d0e6cb8f345898e161cc952634587305090a0a60a120a60a0a0a605052848505242829c3260b142648c981c2c5152834385264870b14343850810203060c183060c102040810204040810204081020000000000000000011224481020408101830609122440810204080c183040810204080c18304081020408081020408100000000044891223060c18244890c18306060c18c122030406088900c0c111202418122406091030304
def x_C2:=[(0xaaaaaaaa851249249c71c71259648a696502082080082186082196485555e916fcb7cb65f2ff0889128a57971fc07f801c01c000703f07870e8a5790,0),(0xcccccccc28a00009208e38e38009338e3a10c34d34434c38d14c0093fab52bab6d5ad5eaffcb31126c2ce2fa1fff8000000000e07fc00000fe2ce202,0),(0xf0f0f0f076d4d3565249249c6394045184a01002028000000212394053e7cd4db66f66ffb5554aa993309f27e0000000000e00ff80000078f1308027,0),(0xff00ff0049212400038249248402549248c5651453151651658440257cf971f1db8fffb359a6945625c3e43c00000000000fff000000007f01c0043c,0),(0xffff000090438e38e51412410e38e124117b8eb8e9ce38e38e38e38e9f3e7e7e1ffdb8dc6e38e764c9ff18c0000000001ff0000000000780000318c0,0)]
def xt_C2:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def tg_C2:Fin 5->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>0 | 4=>0
def c_C2:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffceca01c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C2:Nat->Nat
 | 4=>4
 | 5=>7
 | 6=>1
 | _=>0
def L_C2:Nat->Nat
 | 4=>3
 | 5=>4
 | 6=>0
 | _=>0
def H_C2:Nat->Nat
 | 4=>0xa3d09080a4b86ed0be122ec1
 | 5=>0xbd968c8ae224753fea70abbd4011883525c915acdc
 | 6=>0x6ed0be
 | _=>0
def P_C2:Nat->Nat
 | 4=>0x1071000000320000143500000051
 | 5=>0x5c00000044000000480000005200000060000000340000002e
 | 6=>0x0
 | _=>0
def gs_C2:List (List (Nat×Nat×Nat×Nat)):=[[(6,0x33003300,0xcc00cc,0xcc33cc33)]]
def gsp_C2:List (List (Nat×Nat)):=[[(1,3)]]
def au_C2:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(6,0x33003300,0xcc00cc,0xcc33cc33)]
 | _=>[]
def ap_C2:List (List (Nat×Nat)):=[[],[(1,3)]]
lemma ok_C2:(List.range 7).all (fun s=>span ((bar c_C2 (findAutGen c_C2.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C2 au_C2 (Rgen 0xffffffff 6 xt_C2 P_C2) N_C2 L_C2 H_C2 P_C2) (Rgen c_C2.all1v 6 x_C2 P_C2)) s) (N_C2 s) 0)=true:=by decide +kernel
lemma lb_C2:∀ t,HasCircuitSize 5 f_C2 t->7<=t:=prove_baseGen f_C2 r_C2 0x9e3779b97f4a7c15f39cc0605cedc835 c_C2 (fun _=>0) x_C2 xt_C2 gs_C2 gsp_C2 au_C2 ap_C2 N_C2 L_C2 H_C2 P_C2 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C2) (fun _=>Or.inl rfl)


def E_C3:List (Fin 5×Fin 5):=[(0,1),(0,2),(0,3),(1,3),(2,3),(0,4),(1,4),(2,4),(3,4)]
abbrev f_C3:=gfn [] E_C3
def r_C3:=0x80881422142021030485084040c12142022048883080840a120c1101028483042031418281080c4860a00108182830002206090a0010814221400410304850008812220c002102848304200911828406024460a08088182830202206090a080881422142021030485084040c12142022048883080840a120c110102848300108182830002206090a0010814221400410304850008812220c0021028483042031418281080c4860a3a6c79f3868a931a2cf1d305c9111e284833c6cc17284478c1214e9b2e3ce1a3258a931c34587182848506509110a0cc14243051c3464b152670d191c3459e2e3ce162a38687345898e161cc95263458730509111828485065090c14141982c50911303860a12506052428191121c28310204060c183060c182040810204081020404081020408102040808102040000000000000000020408102020408102008102040902040810202040810204060c1820408102040408102040808102040810000000000000000183060c183080c101012018202024040120200901018202
def x_C3:=[(0xaaaaaaaa0c30c30c30000000c30c330c0000c30c30c30000c30c3000f3d5b56fcb739c0596cb2ff13861093f00000003c00003e0000003f000010920,3),(0xcccccccc410015565a6d013000555851413410015565013000555a6d7566dd21d5b4a4aaabd5fcb24aaa50e51fc00ffc0000000001c0fc0007ea5005,1),(0xf0f0f0f096596080038a4c05550000928e09659608004c055500038abab489b6e6d949534dff5554954c67061ffff0000000000001ff000007ec6006,1),(0xff00ff0000e38038e4d314500e00e4e314500e38038e14500e00e4d3fcf8ee3b78ee027c7f669a68e190fa48e000000000007c007e00000000100248,3),(0xffff000038040e01010438e38038010438e38040e01038e380380104df3f0fc3bf00739ff1b8e38f061f849000000000000f801f8000000000008490,3)]
def xt_C3:=[(0xaaaaaaaa,3),(0xcccccccc,1),(0xf0f0f0f0,1),(0xff00ff00,3),(0xffff0000,3)]
def tg_C3:Fin 5->Nat | 0=>3 | 1=>1 | 2=>1 | 3=>3 | 4=>3
def c_C3:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffefea81c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C3:Nat->Nat
 | 3=>8
 | 4=>10
 | 5=>13
 | 6=>4
 | 7=>1
 | _=>0
def L_C3:Nat->Nat
 | 3=>4
 | 4=>5
 | 5=>5
 | 6=>3
 | 7=>0
 | _=>0
def H_C3:Nat->Nat
 | 3=>0xe97321ac015d99e3e466cd56570b834566a92344820393a2
 | 4=>0xbf74ee9cc9f582032a605cd15af2673e3b84202d8c1b31130ef57004a8f4
 | 5=>0xe1861edaaac1d19475d11fb3c6c828c1f1439cc9f597f3106329cf3f6056392b9c30f4341b3113
 | 6=>0xc6c8289cc9f597f310392b9c
 | 7=>0x9cc9f5
 | _=>0
def P_C3:Nat->Nat
 | 3=>0x246904001c690280044100001c3100000c2d000018510200183104001829
 | 4=>0x2c410000000004002c2d00001027000004910000102300000c42000020010400102b04002c91
 | 5=>0xc020400007a0280040702800001000008310400043100000000040008010000006900000c240000083c0000007200000c01
 | 6=>0x3100000000040000010000003c
 | 7=>0x0
 | _=>0
def gs_C3:List (List (Nat×Nat×Nat×Nat)):=[[(8,0xff0000,0xff00,0xff0000ff)],[(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)],[(8,0xff0000,0xff00,0xff0000ff),(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)],[(7,0x55005500,0xaa00aa,0xaa55aa55)],[(8,0xff0000,0xff00,0xff0000ff),(7,0x55005500,0xaa00aa,0xaa55aa55)],[(2,0x30303030,0xc0c0c0c,0xc3c3c3c3),(7,0x55005500,0xaa00aa,0xaa55aa55)]]
def gsp_C3:List (List (Nat×Nat)):=[[(3,4)],[(1,2)],[(3,4),(1,2)],[(0,3)],[(3,4),(0,3)],[(1,2),(0,3)]]
def au_C3:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(8,0xff0000,0xff00,0xff0000ff)]
 | 2=>[(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)]
 | 3=>[(8,0xff0000,0xff00,0xff0000ff),(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)]
 | 4=>[(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | 5=>[(8,0xff0000,0xff00,0xff0000ff),(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | 6=>[(2,0x30303030,0xc0c0c0c,0xc3c3c3c3),(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | 7=>[(8,0xff0000,0xff00,0xff0000ff),(2,0x30303030,0xc0c0c0c,0xc3c3c3c3),(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | 8=>[(8,0xff0000,0xff00,0xff0000ff),(15,0x55550000,0xaaaa,0xaaaa5555)]
 | 9=>[(15,0x55550000,0xaaaa,0xaaaa5555)]
 | 10=>[(8,0xff0000,0xff00,0xff0000ff),(2,0x30303030,0xc0c0c0c,0xc3c3c3c3),(15,0x55550000,0xaaaa,0xaaaa5555)]
 | 11=>[(2,0x30303030,0xc0c0c0c,0xc3c3c3c3),(15,0x55550000,0xaaaa,0xaaaa5555)]
 | _=>[]
def ap_C3:List (List (Nat×Nat)):=[[],[(3,4)],[(1,2)],[(3,4),(1,2)],[(0,3)],[(3,4),(0,3)],[(1,2),(0,3)],[(3,4),(1,2),(0,3)],[(3,4),(0,4)],[(0,4)],[(3,4),(1,2),(0,4)],[(1,2),(0,4)]]
lemma ok_C3:(List.range 8).all (fun s=>span ((bar c_C3 (findAutGen c_C3.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C3 au_C3 (Rgen 0xffffffff 7 xt_C3 P_C3) N_C3 L_C3 H_C3 P_C3) (Rgen c_C3.all1v 7 x_C3 P_C3)) s) (N_C3 s) 0)=true:=by decide +kernel
lemma lb_C3:∀ t,HasCircuitSize 5 f_C3 t->8<=t:=prove_baseGen f_C3 r_C3 0x9e3779b97f4a7c15f39cc0605cedc835 c_C3 tg_C3 x_C3 xt_C3 gs_C3 gsp_C3 au_C3 ap_C3 N_C3 L_C3 H_C3 P_C3 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 12<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C3) (checkTags_sound bases4 bases4Ok f_C3 E_C3 tg_C3 [.base 1 [0,2,3,0,1],.base 0 [0,0,1,2,3],.base 0 [0,1,0,2,3],.base 1 [0,2,3,0,1],.base 1 [0,2,3,1,0]] (by decide +kernel) (by decide))


def E_C4:List (Fin 5×Fin 5):=[(0,2),(1,2),(0,3),(2,3),(0,4),(1,4),(2,4),(3,4)]
abbrev f_C4:=gfn [] E_C4
def r_C4:=0x10042111824084064430502101890c140082060a0c0020818222400120608890008814241800120508851004818282440120609091004814222440120488891004214182440120608890020818283000820608890004818222400220509060004814221408a084460902282141824401204460910042111824084064830502101910c140840624305100481828244012060909100481422244012048889100421418244012060889223c3053c74b8f3e68c962a3869e3660b94223c6090a74d982e5090f1818e1a3258a931c34587182430530488893868c962a4cf1b1e70d191c3459c2c5470d0e6cb8f345898e161cc9526345873050911182430530486090c488890c14d18284c911303058928386070c14906222c48510204080810204060c183060c1820408102040810204040810204081020400000000000000000204081008102042040810204050a142040810204040810204080c18304081020408081020408100000000000000142850a140c183060c508080c1012010181202840304048042028404
def x_C4:=[(0xaaaaaaaa56db400d30134514d34530034c04e5855569b6d4514d3453d7aaade90b7532d965f2ff151345314f00fe007fc000000000703f0007c53140,3),(0xcccccccc00a2800004c000200400000001301040000e28a0020040006bd5a42b55b2457aaaffcb224ca625b400ffff8000000038007fc000ffe62584,1),(0xf0f0f0f02934c30001450801003800c000514a3822934d30801003807f9f36cde6db09acdfb5554b28c84fd10f0000000000f0001f80000000084011,0),(0xff00ff008c01155450009658618e55551400134e38c00049658618e54de7c771b8ec9e3ff359a68cb130f606f00000000000003fe0000000f8300606,3),(0xffff000010400e38e38e38e38e10e38e38e38410c10410038e38e10e8ef9f87e3f00eff71c6e38f0c63f882800000000000f0fc00000000000008828,0)]
def xt_C4:=[(0xaaaaaaaa,3),(0xcccccccc,1),(0xf0f0f0f0,0),(0xff00ff00,3),(0xffff0000,0)]
def tg_C4:Fin 5->Nat | 0=>3 | 1=>1 | 2=>0 | 3=>3 | 4=>0
def c_C4:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffefae01c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C4:Nat->Nat
 | 3=>3
 | 4=>20
 | 5=>23
 | 6=>9
 | 7=>1
 | _=>0
def L_C4:Nat->Nat
 | 3=>3
 | 4=>6
 | 5=>6
 | 6=>5
 | 7=>0
 | _=>0
def H_C4:Nat->Nat
 | 3=>0xda7d6a4d178c2bc6ba
 | 4=>0xf62a90f10538e069fed967f9d298eece8d5fc9ac79c793ffa5db5ea5bf23a0e82f9e9f06846e5171a6146bc14668c2644a291a46fc8d28529c1e37db
 | 5=>0xf64261e5a727c828c2c1d60cc1d60bb446cbab1887a5db5da5a23a9fa4248ec6c4817a077bcc667298bc70fe6f5e37b25036bc4fc79f4f66432db1f216e23616c645018c5f
 | 6=>0xfb7770c71335c1d60ba5db5d9d581097c7145e37b21d870d16c645
 | 7=>0xc1d60b
 | _=>0
def P_C4:Nat->Nat
 | 3=>0x8000410180282d00801c2d
 | 4=>0x3d0080584101004c2900004039010024490100543b000040710080585100000035018014420000247100002451008050410100145200004c390080587100004c2a0080342d0100087500004442
 | 5=>0x80007601001c390100005a00000435000000000000143a00001468000018230080008200800062010014010100007a00800c330000143000001c510000183c008008760100143200001c3a0000144c000000720000182c00001464
 | 6=>0x100000100000068000000000000002300800006008000050000003c000000640000002c
 | 7=>0x0
 | _=>0
def gs_C4:List (List (Nat×Nat×Nat×Nat)):=[[(12,0xf0f0000,0xf0f0,0xf0f00f0f)],[(7,0x55005500,0xaa00aa,0xaa55aa55)],[(12,0xf0f0000,0xf0f0,0xf0f00f0f),(7,0x55005500,0xaa00aa,0xaa55aa55)]]
def gsp_C4:List (List (Nat×Nat)):=[[(2,4)],[(0,3)],[(2,4),(0,3)]]
def au_C4:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(12,0xf0f0000,0xf0f0,0xf0f00f0f)]
 | 2=>[(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | 3=>[(12,0xf0f0000,0xf0f0,0xf0f00f0f),(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | _=>[]
def ap_C4:List (List (Nat×Nat)):=[[],[(2,4)],[(0,3)],[(2,4),(0,3)]]
lemma ok_C4:(List.range 8).all (fun s=>span ((bar c_C4 (findAutGen c_C4.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C4 au_C4 (Rgen 0xffffffff 7 xt_C4 P_C4) N_C4 L_C4 H_C4 P_C4) (Rgen c_C4.all1v 7 x_C4 P_C4)) s) (N_C4 s) 0)=true:=by decide +kernel
lemma lb_C4:∀ t,HasCircuitSize 5 f_C4 t->8<=t:=prove_baseGen f_C4 r_C4 0x9e3779b97f4a7c15f39cc0605cedc835 c_C4 tg_C4 x_C4 xt_C4 gs_C4 gsp_C4 au_C4 ap_C4 N_C4 L_C4 H_C4 P_C4 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 4<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C4) (checkTags_sound bases4 bases4Ok f_C4 E_C4 tg_C4 [.base 1 [0,2,0,3,1],.base 0 [0,0,1,2,3],.emp,.base 1 [2,3,0,0,1],.emp] (by decide +kernel) (by decide))


def E_C5:List (Fin 5×Fin 5):=[(0,2),(0,3),(2,3),(0,4),(1,4),(2,4),(3,4)]
abbrev f_C5:=gfn [] E_C5
def r_C5:=0x10108142430404206088c101081422304012060a09100481824244012050889100481222242012060a05080481424142012060885080481222144042060a0c10048182224201205088508048111814201205048510108182430404205090c10108182230404205088c100481828244012060909100481422244012048889080481828142012050905080481822142012048885080450c12144042060a0c1004818222420120508851678e982e4888f127cd192c5470d3c6cc17284478c1214e9b305ca121e30e1a3258a931c34587182429c3464b152678d8f3868c8e1a2cf171e70b151c3439b2e3cd162638587325498d161cc1424446090a6090c125090c0a488890a68c16284c911303860b125070c0e1491116243850c102040810204080c183060c183040810204081020408081020408102040000000000000000020408102040810202850a102040810203060c102040810203060c1020408102020408102040000000000002850a14183060c0c1830628406080c1012018203024050806048101420304
def x_C5:=[(0xaaaaaaaa0020914534d14534c04d35530000824514d34514d34c04d3abd556f48b765b2d97cbfc588b8518df007f003fc000000001c0fc00078518c0,0),(0xcccccccc080000080100080100000000082000002004002004200000cd6ad21595b0af57abff2c82245652aa807fffc00000070381ff0007ffd6528a,1),(0xf0f0f0f05515420040239618530258e54554550801008e5861953025694f9b66e6db359bfed55529589867c3ff80000000000003fe00000078186003,0),(0xff00ff008658659618440040259400829619619658611001003a5940f1f3e3b8f8edc7fecd669a359160fb0c00000000000007fc000000078060030c,0),(0xffff000038e38e38e38e38e38e38e30c38e38e38e38e38e38e00e38e7e7cfc3f3f01fee371b8e3c6667f843000000000000ff8000000000000008430,0)]
def xt_C5:=[(0xaaaaaaaa,0),(0xcccccccc,1),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def tg_C5:Fin 5->Nat | 0=>0 | 1=>1 | 2=>0 | 3=>0 | 4=>0
def c_C5:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffefaa01c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C5:Nat->Nat
 | 4=>13
 | 5=>22
 | 6=>9
 | 7=>1
 | _=>0
def L_C5:Nat->Nat
 | 4=>5
 | 5=>6
 | 6=>5
 | 7=>0
 | _=>0
def H_C5:Nat->Nat
 | 4=>0xde3367beabb3aa0db4a0024097de587ecf7a72f85c706c8967082b65274c542c922c84280e5f59
 | 5=>0xf9955af326b9e90e33e10539ba47f7b032549de4589dab3593816f8c105e88244e5a4e2f52656950e9d1476f3e3c5b8a2f7cb62c84281e662b17d8c30ecf4002aaa8
 | 6=>0xec8c4e9de4585e042c5a4e2f478b2f35d034303f382b4b420ecf40
 | 7=>0x5a4e2f
 | _=>0
def P_C5:Nat->Nat
 | 4=>0x105a018028390180283a000000710280405a008050390180285102000835020000510000203b020050310000484d0100503a
 | 5=>0x1c6400001c56000020710000003b0200005a02001c5a000014230000106201802052000020390200007a0000003500801c440000205101001852000018390080185100801c3a01001c6800001c4c0080143c02001c50
 | 6=>0x30000000230000005800000000000000540000000a00000009020000010000002c
 | 7=>0x0
 | _=>0
def gs_C5:List (List (Nat×Nat×Nat×Nat)):=[[(4,0xf000f00,0xf000f0,0xf00ff00f)],[(3,0x50505050,0xa0a0a0a,0xa5a5a5a5)],[(4,0xf000f00,0xf000f0,0xf00ff00f),(3,0x50505050,0xa0a0a0a,0xa5a5a5a5)],[(4,0xf000f00,0xf000f0,0xf00ff00f),(7,0x55005500,0xaa00aa,0xaa55aa55)],[(7,0x55005500,0xaa00aa,0xaa55aa55)]]
def gsp_C5:List (List (Nat×Nat)):=[[(2,3)],[(0,2)],[(2,3),(0,2)],[(2,3),(0,3)],[(0,3)]]
def au_C5:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(4,0xf000f00,0xf000f0,0xf00ff00f)]
 | 2=>[(3,0x50505050,0xa0a0a0a,0xa5a5a5a5)]
 | 3=>[(4,0xf000f00,0xf000f0,0xf00ff00f),(3,0x50505050,0xa0a0a0a,0xa5a5a5a5)]
 | 4=>[(4,0xf000f00,0xf000f0,0xf00ff00f),(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | 5=>[(7,0x55005500,0xaa00aa,0xaa55aa55)]
 | _=>[]
def ap_C5:List (List (Nat×Nat)):=[[],[(2,3)],[(0,2)],[(2,3),(0,2)],[(2,3),(0,3)],[(0,3)]]
lemma ok_C5:(List.range 8).all (fun s=>span ((bar c_C5 (findAutGen c_C5.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C5 au_C5 (Rgen 0xffffffff 7 xt_C5 P_C5) N_C5 L_C5 H_C5 P_C5) (Rgen c_C5.all1v 7 x_C5 P_C5)) s) (N_C5 s) 0)=true:=by decide +kernel
lemma lb_C5:∀ t,HasCircuitSize 5 f_C5 t->8<=t:=prove_baseGen f_C5 r_C5 0x9e3779b97f4a7c15f39cc0605cedc835 c_C5 tg_C5 x_C5 xt_C5 gs_C5 gsp_C5 au_C5 ap_C5 N_C5 L_C5 H_C5 P_C5 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 6<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C5) (checkTags_sound bases4 bases4Ok f_C5 E_C5 tg_C5 [.emp,.base 0 [0,0,1,2,3],.emp,.emp,.emp] (by decide +kernel) (by decide))


def E_C6:List (Fin 5×Fin 5):=[(0,3),(1,3),(0,4),(2,4),(3,4)]
abbrev f_C6:=gfn [] E_C6
def r_C6:=0xc0c81822282832060a090a00818222418020608890c2091828284022460a0a06209182228402246088a0620918222440124608890620091142418804445090620911142440124445090a20914222418824508891004914222428824505090620914142440124505090a2011114243082460a0a10089182828188246088a1008918222818804445090a20918222428824445090620918222440124608890620911142440124445093464b151c34f1b305ca111e24e9b305ca0f1470d192c5498e1a2ca111424f1b2e70d192c5499e3a3ce1a323868b3e58a931c3459e2e5078a3a5ca111e24e162a3869b2e4478a1268b131c2cc9526345982844509305088a30505093860b962a50991346078e1a2c5092c5070a2644689060c183060c1020408102040808102040810200000000000000003870e1c9122440810204080c183040810204080e1c3870e1c3860c183060a142850a142040810203060c18306081020408081020408000000002448912183060c18203860a1018124403860a0c10124406082440608
def x_C6:=[(0xaaaaaaaa4b18e30008828d3b659558e34e18519400220a58e58d3955555f516d596cbb6adcbe97e5212b2d0ffc03f803c0000fe0fc1f83e0002b2d00,0),(0xccccccccc50020a59a59a088aaa8a22820aa8a2a966966a20aa08a8aab495ab4bab55dbb495b7ca21232b6b8fffc0003f8000fff001ffc00f032b688,0),(0xf0f0f0f08228008820000000000009041241048220800008200000003e6a74da2cde6edeebea294844bc38e200000003c01c0fffffe000000fbc3822,0),(0xff00ff001451455655655654d34e34518534e34d59559535535654e3cf8f9f1cf71ff8f38e73ce739bc0ff3300000000001ff000000000000fc00033,0),(0xffff000038e38e38e38e38e10430c38e38c30c10e38e38438c38e30cf3f3e7e33ffb8f1cf39c739cecffc0cc000000003fe0000000000000f000c0cc,0)]
def xt_C6:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def tg_C6:Fin 5->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>0 | 4=>0
def c_C6:Cfg:=⟨128,256,364,448,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffaee001c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_C6:Nat->Nat
 | 4=>1
 | 5=>1
 | _=>0
def L_C6:Nat->Nat
 | 4=>0
 | 5=>0
 | _=>0
def H_C6:Nat->Nat
 | 4=>0xc7f4a0
 | 5=>0x6ed0be
 | _=>0
def P_C6:Nat->Nat
 | 4=>0x800023
 | 5=>0x0
 | _=>0
def gs_C6:List (List (Nat×Nat×Nat×Nat)):=[[(8,0xff0000,0xff00,0xff0000ff),(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)]]
def gsp_C6:List (List (Nat×Nat)):=[[(3,4),(1,2)]]
def au_C6:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(8,0xff0000,0xff00,0xff0000ff),(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)]
 | _=>[]
def ap_C6:List (List (Nat×Nat)):=[[],[(3,4),(1,2)]]
lemma ok_C6:(List.range 6).all (fun s=>span ((bar c_C6 (findAutGen c_C6.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_C6 au_C6 (Rgen 0xffffffff 5 xt_C6 P_C6) N_C6 L_C6 H_C6 P_C6) (Rgen c_C6.all1v 5 x_C6 P_C6)) s) (N_C6 s) 0)=true:=by decide +kernel
lemma lb_C6:∀ t,HasCircuitSize 5 f_C6 t->6<=t:=prove_baseGen f_C6 r_C6 0x9e3779b97f4a7c15f39cc0605cedc835 c_C6 (fun _=>0) x_C6 xt_C6 gs_C6 gsp_C6 au_C6 ap_C6 N_C6 L_C6 H_C6 P_C6 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_C6) (fun _=>Or.inl rfl)

def bases5:List BaseEntry:=[⟨5,E_C0,7⟩,⟨5,E_C1,7⟩,⟨5,E_C2,7⟩,⟨5,E_C3,8⟩,⟨5,E_C4,8⟩,⟨5,E_C5,8⟩,⟨5,E_C6,6⟩]
lemma bases5Ok:BaseTableOk bases5:=
  baseTable_cons _ _ lb_C0 (  baseTable_cons _ _ lb_C1 (  baseTable_cons _ _ lb_C2 (  baseTable_cons _ _ lb_C3 (  baseTable_cons _ _ lb_C4 (  baseTable_cons _ _ lb_C5 (  baseTable_cons _ _ lb_C6 (fun _ h => by cases h)))))))


def E_G0:List (Fin 6×Fin 6):=[(0,2),(1,3),(0,4),(2,4),(3,4),(1,5),(2,5),(3,5),(4,5)]
abbrev f_G0:=gfn [] E_G0
def r_G0:=0x20844a8304440224c0c0a10089182828402246088a08050b0481420142a120508050a4441480842c141820110b0485040242a110a080491422148041890c1410089223028201429088520050b0504480142c121120050b0444480112a0c1120844a8304440224c0c0a100892230284022460a0a1008918222820142c120508050a84814201429110508050a42214221245088520210b0506080442c121410090a84428201245088514e1a3262b15294c9519c3464b15263868b0ee5ab35aad3b868c98ac54a532546e9b333c6cbb868c989c3464b1526f172d3c747b95aace9b1ee162a5270d191c345b65c9cf171ed16264a70b151c343b3569cd971ec95264668b131c2c3b152951992a4c68b0ec14244460a11141582848888856088c1422294243050505506088a0a911141415111141593058a5426488d1316070c982c5099152a0d181c2c5254858a0d0e151a21c2c51322343850200000000000000000000000000000000000850a142850a0408102040810204048912244891020408102040810203060c183060912244891220408102040810204060c183060c1020408102040810203060c183060810204081020408101020408102040810200000000000000010a142850a12448912244860c183060c122448912183060c18183060c9101824406080c12140304880c1018142809100c0c121404880906050a018244122030304
def x_G0:=[(0xaaaaaaaaaaaaaaaa6400026596482084c001b6596596400000996596d32082130965bfe25962597f8965897f897ff814308128544523851e5f800007e00000001f8000001f801ff803f000f83c4523851e40,3),(0xcccccccccccccccc0196590000800132007400000800197596400020080004c892aad964afe4aaa592bf92bfffe25888444212aa160a2e4bf20000000007e00000001f801fffe000000fc007fe160a2e4812,3),(0xf0f0f0f0f0f0f0f00000808e39404c095d0250020000000020238e596501302524d36aa932a937eaa4dfffe592a4a92491150d44984c09fc8700000000000007e0001fffe000000000003f07c0984c080087,3),(0xff00ff00ff00ff003a396500401302500a8c008000e3a38e59401000004c0940c71c74d1c4d1c7ffffeaa4caa4c93249026ad088e070fe10e400000000000007ffffe0000000000000003ff800e0700010e4,3),(0xffff0000ffff00008ce38e1000259403a32829659638ce28e38400008e96500e781f871e07fffcd3471347134711c4722b8c611301ff3060180000000007fff80000000000000000000fc000030000306018,3),(0xffffffff0000000050400038e38e38e00410c38e38450410000e38e31038e3807fe007ffff1e071c781c781c781e0783cc308623ff80c18300000007fff80000000000000000000003f00000000180c18300,3)]
def xt_G0:=[(0xaaaaaaaaaaaaaaaa,3),(0xcccccccccccccccc,3),(0xf0f0f0f0f0f0f0f0,3),(0xff00ff00ff00ff00,3),(0xffff0000ffff0000,3),(0xffffffff00000000,3)]
def tg_G0:Fin 6->Nat | 0=>3 | 1=>3 | 2=>3 | 3=>3 | 4=>3 | 5=>3
def c_G0:Cfg:=⟨200,400,508,592,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffffffcfffaeca01c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffff,0x41041041041041041041041041,0x75d75d75d75d75d75d75d75d75d,0x820820820820820820820820820,0x41041041041041041041,0x82082082082082082082,0x75d75d75d75d75d75d75d,0x820820820820820820820⟩
def N_G0:Nat->Nat
 | 5=>11
 | 6=>99
 | 7=>99
 | 8=>14
 | 9=>1
 | _=>0
def L_G0:Nat->Nat
 | 5=>5
 | 6=>8
 | 7=>8
 | 8=>5
 | 9=>0
 | _=>0
def H_G0:Nat->Nat
 | 5=>0xfbf1f6f7e05aed934ed61e34d1834bcd6564cc459826bf351dd4bc119d0f0a9c9c
 | 6=>0xfe61dcfcb1cdfbc7f6f5d150ef8560ee3418eac0b6e9dfaee7cb76e76f87e696d2e309e8e0a8c3e0742cde7b5adcfe0bd84a7dd7c869ce2e9fcdcb0fcbca78c95ce5c71ad7c70c29c64193c34208c27abac27325bc5e8dbad9c2b4e507b22dffb1f87fb1ce8fb05c0ba93139a364a8a1ace79d3f09953b3b930241920b6c914a0b9145f99112af90ecb78eb77a8dfc378a49718926a881f97981afcb807b277ce14c785afc7808d874505273f6d3721ac9719ca96d819b68e3d9640d0763f61462e36761030b60af2c5fa6485d93da5c2c835925b058601156c3a4539eb150dc614ba04048e79448230643da7541904a402ec43ecb9438ff2e38123734910433bbbf31e6232f969d29a3cd23877b1d77ee1ae8341adbb81aa1ff19f44e164d1c158b9b1126d610808b
 | 7=>0xffe2eefe61dcfbe4a3fbd6acf7bf77f70825f4abdaf1aa86eb48f3eac0b6e4e976e3dc6fe2b08bdccf3ddcc09ad79713d5acc7d47823d2dab4ce9348ce8a14c4dbbec3a3b2c06f2dbdf4adbdb728bb5cc9b7bbe3b27680b1f87fb1796bb05c0bae8228ad58fd990e2696604e9145f98e581d8e377289b48186f43c86083d800ba57f3ef37dcc3c7a0d4677847773f95d7296b2711d956ed8b468b3b465de7f65bb1764db5a6424e75e84395df92f5df3e756c3a455e33555644f552b2f52780351ea0d50dc6150aec94d3772493e4a3ee31d3ebdb23c1d50390e1c3749f0349d71339a1332e70b30b5cb2f0d872b145f29429d2895c51fc7741d77ee1d1c701c2209161cda10caaa102f7a0fb2c00ed6be0cdb9c0cc5f50b071e075a0d062afb05d34804923f02a502
 | 8=>0xfbd6ace4e976dcc09ace9348b1796b8e581d7f3ef37a0d4655e3354d37723ebdb23c1d502f0d871d1c70
 | 9=>0x1d1c70
 | _=>0
def P_G0:Nat->Nat
 | 5=>0x8030790080a83d00004c7a008088920000b4710080887a0000f42d0081109d0000a8590080e82d00004079
 | 6=>0x80706c0000807a0000f8b200010c5a0080c87a0001708a0080704200011430008148a20080f82f008144a200816c5a008138b20080847a0000cca2008184a20001142c008084420001547a0080845a0080408a0081647a00003c2f0081488a0081849a0081647200010ca20000743d0001583d000020a2000120b200000ca2000070820001205700017c820001707a0080f8a20000e0ba0001247500816c8a008040ba0081843e00817082008150a2000118b200010c2f00803c3b00012c7a008040aa00814c9d00010c590081487a00001081008014cd00809c71000144b2008120a2000174a2008138aa000114940000cc7a008184aa00012c5a0080c88a0081645a00812c9900817841008040a2008118a200816c7a008118aa0000cc5a0001603d0080c03e0080707a00000c5a008148ba0001205500016c6a0001648a008148b20080ec750000e0a2008000410000e0b20080d03e008040b200003ca2000134550081649400017c8a000084410081648c0000487a0080b03d000170920080c89a0080408200808494
 | 7=>0x80348c00800c6c0000200b0000003c008030a2000030aa000004520080285a0080200900800c4200000064000024b4000010b4000010620000004c000024c4008034a2008028a2000008070000002400800c2c0000309a000034940000303f000020070000249a00802c7a0000280100002c7200000c8200000054000034820000346c00802005008008090000288c00802ca2008000010000286c00800c740000340100000c020000349a00000094000028020080000900800c94000034620080347a0000249400800c840080305400003402008004a200800c8c0000246c00002c01000034c400800c3c0000303d00000084008024a2000004bc00002c74000014c400800c7a0000048a0080005c000010c400002cc400800072008000050080040200002872000034bc0080300100000c01000028c40000002c00000494000024620000048200800c540000348a0000000000003074008024020000080b0000200300801474000014aa0000109400802401000030c400802894000010aa0000049a0000180b0080047a
 | 8=>0x3c000000640000004c0000002400000054008000010000009400800009000000840000007400800072008000050000002c00000000
 | 9=>0x0
 | _=>0
def gs_G0:List (List (Nat×Nat×Nat×Nat)):=[[(16,0xffff00000000,0xffff0000,0xffff00000000ffff),(4,0xf000f000f000f00,0xf000f000f000f0,0xf00ff00ff00ff00f),(1,0x4444444444444444,0x2222222222222222,0x9999999999999999)]]
def gsp_G0:List (List (Nat×Nat)):=[[(4,5),(2,3),(0,1)]]
def au_G0:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[(16,0xffff00000000,0xffff0000,0xffff00000000ffff),(4,0xf000f000f000f00,0xf000f000f000f0,0xf00ff00ff00ff00f),(1,0x4444444444444444,0x2222222222222222,0x9999999999999999)]
 | _=>[]
def ap_G0:List (List (Nat×Nat)):=[[],[(4,5),(2,3),(0,1)]]
lemma ok_G0:(List.range 10).all (fun s=>span ((bar c_G0 (findAutGen c_G0.shTT 0x9e3779b97f4a7c15f39cc0605cedc835 gs_G0 au_G0 (Rgen 0xffffffffffffffff 9 xt_G0 P_G0) N_G0 L_G0 H_G0 P_G0) (Rgen c_G0.all1v 9 x_G0 P_G0)) s) (N_G0 s) 0)=true:=by decide +kernel
lemma lb_G0:∀ t,HasCircuitSize 6 f_G0 t->10<=t:=prove_baseGen f_G0 r_G0 0x9e3779b97f4a7c15f39cc0605cedc835 c_G0 tg_G0 x_G0 xt_G0 gs_G0 gsp_G0 au_G0 ap_G0 N_G0 L_G0 H_G0 P_G0 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound ok_G0) (checkTags_sound bases5 bases5Ok f_G0 E_G0 tg_G0 [.base 0 [0,0,1,2,3,4],.base 0 [0,0,2,1,4,3],.base 1 [0,1,0,2,3,4],.base 1 [1,0,2,0,4,3],.base 2 [0,1,2,3,0,4],.base 2 [1,0,3,2,4,0]] (by decide +kernel) (by decide))


end Windmill
open Windmill PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fix {n : ℕ} (f : BFn n) (p : Fin n) (b : Bool) : BFn n :=
  fun x => f (Function.update x p b)

def depends {n : ℕ} (f : BFn n) (p : Fin n) : Prop :=
  ∃ x : Fin n → Bool, fix f p (!x p) x ≠ f x

def nonconstant {n : ℕ} (f : BFn n) : Prop :=
  ∃ x y : Fin n → Bool, f x ≠ f y



lemma arm_lower {n k s : ℕ} {f g : BFn (n+1)} {leaf inner : Fin (n+1)}
    (usesLeaf : depends f leaf)
    (usesInner : ∀ b : Bool, depends (fix f leaf b) inner)
    (vary : nonconstant g)
    (reduce : ∀ b : Bool, fix (fix f leaf b) inner false = g)
    (lower : ∀ t, HasCircuitSize (n+1) g t → k ≤ t)
    (small : HasCircuitSize (n+1) f s) : k + 3 ≤ s := by
  have varySlice (b : Bool) : nonconstant (fix f leaf b) := by
    obtain ⟨x, y, hxy⟩ := vary
    exact ⟨Function.update x inner false, Function.update y inner false, by
      simpa only [← reduce b, fix] using hxy⟩
  obtain ⟨b, t, ht, first⟩ := q141 n f leaf s usesLeaf varySlice small
  have varyTwice : nonconstant (fix (fix f leaf b) inner false) := (reduce b).symm ▸ vary
  obtain ⟨u, hu, second⟩ :=
    q70 n (fix f leaf b) inner false t (usesInner b) varyTwice first
  have hk := lower u (reduce b ▸ second)
  omega



def target8 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 7) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 7)
def witness : List Gate := [⟨.or, [5, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [11, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [12, 6]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩]
theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 20⟩ (List.ofFn x) = target8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, target8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem liftedLower (s : ℕ) (hc : HasCircuitSize 8 target8 s) : 13 ≤ s := by
  let g := fix (fix target8 4 false) 1 false
  apply arm_lower (n := 7) (leaf := 4) (inner := 1) (g := g) (k := 10) _ _ _ _ _ hc
  · exact ⟨(fun i : Fin 8 => (18 : ℕ).testBit i.val), by decide⟩
  · intro bit
    cases bit
    · exact ⟨(fun i : Fin 8 => (34 : ℕ).testBit i.val), by decide⟩
    · exact ⟨(fun _ => false), by decide⟩
  · exact ⟨(fun i : Fin 8 => (129 : ℕ).testBit i.val), (fun _ => false), by decide⟩
  · intro bit
    cases bit <;> funext x
    · rfl
    · exact (by decide +kernel : ∀ y : Fin 8 → Bool, fix (fix target8 4 true) 1 false y = g y) x
  · intro t small
    let π : Fin 8 → Fin 6 := ![4, 0, 1, 2, 0, 3, 0, 5]
    have reduced := yn π g t small
    have eqn : (fun x : Fin 6 → Bool => g (x ∘ π)) = Windmill.f_G0 := by
      funext x
      exact (by decide +kernel : ∀ y : Fin 6 → Bool, g (y ∘ π) = Windmill.f_G0 y) x
    rw [eqn] at reduced
    exact Windmill.lb_G0 t reduced
end PEqualNP.Outside.L_meta_30172
open PEqualNP.Outside.L_meta_30172 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_30172 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  have h : HasCircuitSize 8 target8 gates.length := ⟨⟨gates,o⟩, legal, le_rfl, fun x => (computes x).trans (graph_correct x).symm⟩
  have large := liftedLower gates.length h
  have hw : witness.length ≤ 13 := by decide
  exact ⟨witness, 20, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
