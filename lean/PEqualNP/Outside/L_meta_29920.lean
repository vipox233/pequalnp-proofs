import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29920.C7Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
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
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg]
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
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [ko, Ok]
   subst g
   simp
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [ji, Ok]
   subst g
   simp
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp_all [wr, Ok]
   subst g
   simp
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
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
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



def probe (m : ℕ) (i : Fin 7) : Bool := (2*m).testBit i.val

def path (m : ℕ) : Bool :=
  (m.testBit 0 && m.testBit 1) || (m.testBit 1 && m.testBit 2) ||
  (m.testBit 2 && m.testBit 3) || (m.testBit 3 && m.testBit 4) ||
  (m.testBit 4 && m.testBit 5)

def upd (p : Fin 6) (v : Bool) (m : Fin 64) : Fin 64 :=
  Fin.ofNat 64 (if v then m.val ||| (2^p.val) else m.val &&& (63 - 2^p.val))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem probe_upd : ∀ p : Fin 6, ∀ v : Bool, ∀ m : Fin 64,
    Function.update (probe m.val) p.succ v = probe (upd p v m).val := by decide +kernel

def mark (a b m : ℕ) : Option Bool :=
  if a.testBit m then some false else if b.testBit m then some true else none

def Fits (f : BFn 7) (a b : ℕ) := ∀ (m : Fin 64) (v : Bool), mark a b m.val = some v → f (probe m.val) = v
def Bound (a b k : ℕ) := ∀ (f : BFn 7) (s : ℕ), Fits f a b → HasCircuitSize 7 f s → k ≤ s
def fixP (f : BFn 7) (p : Fin 6) (b : Bool) : BFn 7 := fun x => f (Function.update x p.succ b)
abbrev Sep (a b : ℕ) (p : Fin 6) (m : Fin 64) (v : Bool) : Prop :=
  mark a b m.val = some v ∧ mark a b (upd p (!(probe m.val p.succ)) m).val = some (!v)
abbrev Mixed (a b : ℕ) (u w : Fin 64) : Prop := mark a b u.val = some false ∧ mark a b w.val = some true
abbrev Pull (a b c d : ℕ) (p : Fin 6) (v : Bool) : Prop :=
  ∀ (m : Fin 64) (z : Bool), mark c d m.val = some z → mark a b (upd p v m).val = some z

lemma depOf {f a b p m v} (h : Fits f a b) (sep : Sep a b p m v) :
    ∃ x : Fin 7 → Bool, f (Function.update x p.succ (!x p.succ)) ≠ f x := by
  refine ⟨probe m.val, ?_⟩
  rw [probe_upd, h _ _ sep.1, h _ _ sep.2]
  cases v <;> decide

lemma pullOf {f a b c d p v} (h : Fits f a b) (hp : Pull a b c d p v) : Fits (fixP f p v) c d := by
  intro m z hz
  unfold fixP
  rw [probe_upd]
  exact h _ _ (hp m z hz)

lemma mixedOf {f a b u w} (h : Fits f a b) (hm : Mixed a b u w) : ∃ x y, f x ≠ f y := by
  exact ⟨probe u.val, probe w.val, by rw [h _ _ hm.1, h _ _ hm.2]; decide⟩

lemma zeroBound (a b : ℕ) : Bound a b 0 := fun _ _ _ _ => Nat.zero_le _

lemma oneStep {a b c d k} (p : Fin 6) (v : Bool) (m u w : Fin 64) (z : Bool)
    (sep : Sep a b p m z) (proj : Pull a b c d p v) (mix : Mixed c d u w)
    (child : Bound c d k) : Bound a b (k+1) := by
  intro f s h hc
  have sub := pullOf h proj
  obtain ⟨t, ht, hct⟩ := q70 6 f p.succ v s (depOf h sep) (mixedOf sub mix) hc
  have := child _ _ sub hct
  omega

lemma twoStep {a b c d e f' k} (p : Fin 6) (m u w u' w' : Fin 64) (z : Bool)
    (sep : Sep a b p m z) (pa : Pull a b c d p false) (pb : Pull a b e f' p true)
    (ma : Mixed c d u w) (mb : Mixed e f' u' w') (la : Bound c d k) (lb : Bound e f' k) :
    Bound a b (k+2) := by
  intro f s h hc
  have ha := pullOf h pa
  have hb := pullOf h pb
  have non (v : Bool) : ∃ x y, fixP f p v x ≠ fixP f p v y := by
    cases v
    · exact mixedOf ha ma
    · exact mixedOf hb mb
  obtain ⟨v,t, ht, hct⟩ := q141 6 f p.succ s (depOf h sep) non hc
  cases v
  · have := la _ _ ha hct
    omega
  · have := lb _ _ hb hct
    omega

lemma addPoint {f a b c d} (m : Fin 64) (v : Bool) (h : Fits f a b) (val : f (probe m.val) = v)
    (atM : mark c d m.val = some v) (away : ∀ i : Fin 64, i ≠ m → mark c d i.val = mark a b i.val) :
    Fits f c d := by
  intro i z hz
  by_cases hi : i = m
  · subst i
    rw [atM] at hz
    exact (Option.some.inj hz) ▸ val
  · exact h _ _ ((away i hi) ▸ hz)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound0 : Bound 0x3f003f003f003f 0xf0c0f0c0f0c0f0c0 2 := twoStep 1 4 0 12 0 4 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xff00ff00ff00ff 0xf000f000f000f000) (zeroBound 0xf000f000f000f 0xf0f0f0f0f0f0f0f0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound1 : Bound 0xfff0fff0fff0fff 0xf000f000f000f000 1 := oneStep 2 true 8 0 8 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xff00ff00ff00ff 0xff00ff00ff00ff00)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound2 : Bound 0x333033303330333 0xfcccfcccfcccfccc 2 := oneStep 1 false 0 0 12 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound3 : Bound 0x237023702370237 0xf8c8f8c8f8c8f8c8 4 := twoStep 0 2 0 6 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound0 bound2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound4 : Bound 0x22023700220237 0xffc8f8c8ffc8f8c8 5 := oneStep 4 false 9 0 3 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound3

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound5 : Bound 0xff000000ff 0xffffff00ffffff00 1 := oneStep 3 false 0 0 16 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xffff0000ffff 0xffff0000ffff0000)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound6 : Bound 0xfff00000fff 0xfffff000fffff000 2 := oneStep 2 true 8 0 8 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound5

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound7 : Bound 0xf3f00000f3f 0xfffff0c0fffff0c0 3 := oneStep 1 false 4 0 12 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound8 : Bound 0x33300000333 0xfffffcccfffffccc 3 := oneStep 1 false 0 0 12 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound9 : Bound 0x73700000737 0xfffff8c8fffff8c8 5 := twoStep 0 2 0 6 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound7 bound8

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound10 : Bound 0x73700220237 0xfffff8c8ffc8f8c8 7 := twoStep 5 17 0 3 0 3 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound4 bound9

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound11 : Bound 0xafafafafafafafaf 0x5050505050505050 1 := oneStep 0 false 4 0 4 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xf0f0f0f0f0f0f0f 0xf0f0f0f0f0f0f0f0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound12 : Bound 0x505050505050505 0xfafafafafafafafa 1 := oneStep 0 false 0 0 4 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xf0f0f0f0f0f0f0f 0xf0f0f0f0f0f0f0f0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound13 : Bound 0x2727272727272727 0xd8d8d8d8d8d8d8d8 3 := twoStep 1 1 0 4 0 1 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound11 bound12

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound14 : Bound 0x227022702270227 0xf8d8f8d8f8d8f8d8 4 := oneStep 3 false 5 0 3 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound13

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound15 : Bound 0xf3f0f3f0f3f0f3f 0xf0c0f0c0f0c0f0c0 2 := oneStep 1 false 4 0 12 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound16 : Bound 0x737073707370737 0xf8c8f8c8f8c8f8c8 4 := twoStep 0 2 0 6 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound15 bound2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound17 : Bound 0x737073702270227 0xf8c8f8c8f8d8f8d8 6 := twoStep 5 4 0 3 0 3 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound14 bound16

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound18 : Bound 0x73700220227 0xfffff8c8ffc8f8d8 7 := oneStep 4 false 9 0 3 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound17

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound19 : Bound 0x73700220227 0xfffff8c8ffc8f8c8 7 := by
  intro f s h hc
  cases hv : f (probe 4) with
  | false =>
    refine bound10 f s ?_ hc
    exact addPoint 4 false h hv (by decide +kernel) (by decide +kernel)
  | true =>
    refine bound18 f s ?_ hc
    exact addPoint 4 true h hv (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound20 : Bound 0x333033303330333 0xf0ccf0ccf0ccf0cc 2 := oneStep 1 false 0 0 12 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound21 : Bound 0xf3f0f3f03330333 0xf0c0f0c0f0ccf0cc 4 := twoStep 5 2 0 2 0 6 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound20 bound15

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound22 : Bound 0xf3f00000333 0xfffff0c0ffc0f0cc 5 := oneStep 4 false 8 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound21

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound23 : Bound 0xffffffffffff 0xffff000000000000 1 := oneStep 4 true 32 0 32 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xffffffff 0xffffffff00000000)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound24 : Bound 0xffff00ffffff 0xffff0000ff000000 2 := oneStep 3 false 16 0 48 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound23

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound25 : Bound 0xff00ff00ff 0xffffff00ff00ff00 2 := oneStep 3 false 0 0 48 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound23

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound26 : Bound 0xfff00ff0fff 0xfffff000ff00f000 4 := twoStep 2 8 0 24 0 8 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound24 bound25

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound27 : Bound 0x33300330333 0xfffffcccffccfccc 5 := oneStep 1 false 0 0 12 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound26

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound28 : Bound 0x73700220333 0xfffff8c8ffc8f8cc 7 := twoStep 0 34 0 2 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound22 bound27

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound29 : Bound 0xffff00000000 0xffff00000000ffff 1 := oneStep 4 false 32 32 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xffffffff00000000 0xffffffff)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound30 : Bound 0xffff00003333 0xffff00000000cccc 2 := oneStep 1 true 0 32 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound29

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound31 : Bound 0x333333333333 0xffffcccccccccccc 2 := oneStep 1 false 0 0 48 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound23

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound32 : Bound 0x777722223333 0xffff88888888cccc 4 := twoStep 0 34 0 2 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound30 bound31

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound33 : Bound 0x2222222222222222 0x9999999999999999 1 := oneStep 0 true 0 0 2 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0x3333333333333333 0xcccccccccccccccc)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound34 : Bound 0x7777777777777777 0x8888888888888888 1 := oneStep 0 true 2 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0x3333333333333333 0xcccccccccccccccc)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound35 : Bound 0x7777777722222222 0x8888888899999999 3 := twoStep 5 0 1 0 0 3 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound33 bound34

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound36 : Bound 0x777700002222 0xffff8888ffff9999 4 := oneStep 4 false 1 1 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound35

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound37 : Bound 0x777700222233 0xffff8888ff8899cc 6 := twoStep 3 0 0 2 1 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound32 bound36

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound38 : Bound 0x73700220233 0xfffff8c8ffc8f9cc 7 := oneStep 2 false 9 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound37

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound39 : Bound 0x73700220233 0xfffff8c8ffc8f8cc 7 := by
  intro f s h hc
  cases hv : f (probe 8) with
  | false =>
    refine bound28 f s ?_ hc
    exact addPoint 8 false h hv (by decide +kernel) (by decide +kernel)
  | true =>
    refine bound38 f s ?_ hc
    exact addPoint 8 true h hv (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound40 : Bound 0xffff00000f0f 0xffff00000000f0f0 2 := oneStep 2 true 0 32 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound29

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound41 : Bound 0xf0f00000000 0xfffff0f0f0f0ffff 2 := oneStep 2 false 32 32 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound29

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound42 : Bound 0x3f3f00000303 0xffffc0c0c0c0fcfc 4 := twoStep 1 0 0 4 32 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound40 bound41

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound43 : Bound 0xf3f00000003 0xfffff0c0ffc0f0fc 5 := oneStep 3 false 36 0 2 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound42

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound44 : Bound 0x73700220223 0xfffff8c8ffc8f8dc 7 := twoStep 0 4 0 2 0 2 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound43 bound27

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound45 : Bound 0x73700220223 0xfffff8c8ffc8f8cc 7 := by
  intro f s h hc
  cases hv : f (probe 4) with
  | false =>
    refine bound39 f s ?_ hc
    exact addPoint 4 false h hv (by decide +kernel) (by decide +kernel)
  | true =>
    refine bound44 f s ?_ hc
    exact addPoint 4 true h hv (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound46 : Bound 0x73700220223 0xfffff8c8ffc8f8c8 7 := by
  intro f s h hc
  cases hv : f (probe 2) with
  | false =>
    refine bound19 f s ?_ hc
    exact addPoint 2 false h hv (by decide +kernel) (by decide +kernel)
  | true =>
    refine bound45 f s ?_ hc
    exact addPoint 2 true h hv (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound47 : Bound 0xf000f000f000f0 0xf00ff00ff00ff00f 1 := oneStep 2 true 0 0 8 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (zeroBound 0xff00ff00ff00ff 0xff00ff00ff00ff00)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound48 : Bound 0xfff0fff00f000f0 0xf000f000f00ff00f 3 := twoStep 5 0 4 0 0 12 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound47 bound1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound49 : Bound 0xfff000000f0 0xfffff000ff00f00f 4 := oneStep 4 false 32 4 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound48

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound50 : Bound 0xf3f00000030 0xfffff0c0ffc0f0c3 5 := oneStep 1 false 4 4 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound49

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound51 : Bound 0x73700220232 0xfffff8c8ffc8f8c9 7 := twoStep 0 0 4 0 0 2 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound50 bound27

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound52 : Bound 0xffffaaaaaaaa 0xffff000000005555 3 := twoStep 0 0 32 0 0 48 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound29 bound23

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound53 : Bound 0xffff00aaaaaa 0xffff0000ff000055 4 := oneStep 3 false 17 1 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound52

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound54 : Bound 0xff00000000 0xffffff00ff00ffff 2 := oneStep 3 false 32 32 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound29

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound55 : Bound 0xff00aa00aa 0xffffff00ff00ff55 4 := twoStep 0 0 32 0 0 8 true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound54 bound25

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound56 : Bound 0xfff00aa0aaa 0xfffff000ff00f055 6 := twoStep 2 9 1 0 1 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bound53 bound55

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound57 : Bound 0x73700220222 0xfffff8c8ffc8f8d9 7 := oneStep 1 false 1 1 0 false (by decide +kernel) (by decide +kernel) (by decide +kernel) bound56

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound58 : Bound 0x73700220222 0xfffff8c8ffc8f8c9 7 := by
  intro f s h hc
  cases hv : f (probe 4) with
  | false =>
    refine bound51 f s ?_ hc
    exact addPoint 4 false h hv (by decide +kernel) (by decide +kernel)
  | true =>
    refine bound57 f s ?_ hc
    exact addPoint 4 true h hv (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bound59 : Bound 0x73700220222 0xfffff8c8ffc8f8c8 7 := by
  intro f s h hc
  cases hv : f (probe 0) with
  | false =>
    refine bound46 f s ?_ hc
    exact addPoint 0 false h hv (by decide +kernel) (by decide +kernel)
  | true =>
    refine bound58 f s ?_ hc
    exact addPoint 0 true h hv (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem prefix_lower (f : (Fin 7 → Bool) → Bool) (s : ℕ) (hc : HasCircuitSize 7 f s)
    (hs : ∀ m : Fin 64, (m.val.testBit 0 || m.val.testBit 5 || path m.val) = true → f (probe m.val) = path m.val) : 7 ≤ s := by
  refine bound59 f s ?_ hc
  intro m v hv
  have tab : ∀ (m : Fin 64) (v : Bool), mark 0x73700220222 0xfffff8c8ffc8f8c8 m.val = some v →
      (m.val.testBit 0 || m.val.testBit 5 || path m.val) = true ∧ path m.val = v := by decide +kernel
  exact (hs m (tab m v hv).1).trans (tab m v hv).2
end PEqualNP.Outside.L_meta_29920.C7Lower



namespace PEqualNP.Outside.L_meta_29920.C7Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def valAt (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun k => w.getD k false)
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun v g => v ++ [valAt g v]) w

theorem run_add (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_extends (gs : List Gate) (w : List Bool) :
    ∃ a : List Bool, run gs w = w ++ a ∧ a.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨a, e, l⟩ := ih (w ++ [valAt g w])
    exact ⟨valAt g w :: a, by simpa [run, List.append_assoc] using e, by simp [l]⟩

theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨a, e, l⟩ := run_extends gs w
  simp [e, l]

def agrees (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ k, k ≠ 0 → u.getD k false = v.getD k false

theorem val_agrees (g : Gate) (u v : List Bool) (h : agrees u v) (hg : 0 ∉ g.inputs) :
    valAt g u = valAt g v := by
  unfold valAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h.2 j (fun e => hg (e ▸ hj))

theorem push_agrees (u v : List Bool) (a : Bool) (h : agrees u v) :
    agrees (u ++ [a]) (v ++ [a]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases lt : j < u.length
  · rw [List.getD_append _ _ _ _ lt, List.getD_append _ _ _ _ (h.1 ▸ lt)]
    exact h.2 j hj
  · by_cases eq : j = u.length
    · simp [eq,h.1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; have := h.1; omega)]

theorem prefix_agrees (gs : List Gate) (u v : List Bool) (h : agrees u v)
    (hs : ∀ g ∈ gs, 0 ∉ g.inputs) : agrees (run gs u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    change agrees (run gs (u ++ [valAt g u])) (run gs (v ++ [valAt g v]))
    rw [val_agrees g u v h (hs g (by simp))]
    exact ih _ _ (push_agrees _ _ _ h) (fun t ht => hs _ (by simp [ht]))

theorem pair_inputs (l : List Nat) (j : Nat) (hn : l.length ≤ 2) (h0 : 0 ∈ l)
    (hj : j ∈ l) (ne : j ≠ 0) : l = [0,j] ∨ l = [j,0] := by
  rcases l with _ | ⟨a, l⟩
  · simp at h0
  rcases l with _ | ⟨b, l⟩
  · simp at h0 hj
    omega
  rcases l with _ | ⟨c,l⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 hj
    rcases h0 with ha | hb <;> rcases hj with hja | hjb <;> simp_all
  · simp at hn

def input (m : Nat) (b : Bool) (i : Fin 7) : Bool :=
  if i = 0 then b else (2*m).testBit i.val

def cycle (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

theorem inputs_agree (m : Nat) :
    agrees (List.ofFn (input m false)) (List.ofFn (input m true)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases h : j < 7
  · interval_cases j <;> simp_all [input]
  · simp [h]

def pref (pre : List Gate) (m : Nat) (b : Bool) : List Bool := run pre (List.ofFn (input m b))

theorem plen {pre : List Gate} (hl : pre.length = 8) (m : Nat) (b : Bool) :
    (pref pre m b).length = 15 := by simp [pref,run_len,hl]

theorem first (pre : List Gate) (m : Nat) (b : Bool) : (pref pre m b).getD 0 false = b := by
  obtain ⟨t,e,_⟩ := run_extends pre (List.ofFn (input m b))
  unfold pref
  rw [e, List.getD_append _ _ _ _ (by simp)]
  simp [input]

def lastTwo (u : List Bool) (g h : Gate) : List Bool :=
  let v := u ++ [valAt g u]
  v ++ [valAt h v]

theorem assembled (pre : List Gate) (g h : Gate) (o m : Nat) (b : Bool) :
    Circuit.eval ⟨pre ++ [g,h],o⟩ (List.ofFn (input m b)) =
      (lastTwo (pref pre m b) g h).getD o false := by
  change (run (pre ++ [g,h]) _).getD o false = _
  rw [run_add]
  rfl

theorem early (u : List Bool) (g h : Gate) (o : Nat) (ho : o < u.length) :
    (lastTwo u g h).getD o false = u.getD o false := by
  unfold lastTwo
  rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ ho]

theorem sideval (pre : List Gate) (m : Nat) (b : Bool) (g : Gate) (j : Nat)
    (hg : g.op = GateOp.or) (hp : g.inputs = [0,j] ∨ g.inputs = [j,0]) :
    valAt g (pref pre m b) = (b || (pref pre m b).getD j false) := by
  have e : ((pref pre m b)[0]?).getD false = b := first pre m b
  rcases hp with l | l <;> simp [valAt,hg,l,GateOp.eval,e,Bool.or_comm]

theorem output_effect (pre : List Gate) (g h : Gate) (j o : Nat)
    (hl : pre.length = 8) (hn : ∀ k ∈ pre, 0 ∉ k.inputs)
    (hg : g.op = GateOp.or) (hp : g.inputs = [0,j] ∨ g.inputs = [j,0])
    (ha : h.op = GateOp.and) (hh : 15 ∈ h.inputs) (hz : 0 ∉ h.inputs)
    (comp : ∀ x : Fin 7 → Bool, Circuit.eval ⟨pre ++ [g,h],o⟩ (List.ofFn x) = cycle x)
    (m : Nat) :
    let u := run pre (List.ofFn (input m false))
    (cycle (input m false) = true → u.getD j false = true) ∧
    (cycle (input m false) ≠ cycle (input m true) → u.getD j false = false) := by
  change (cycle (input m false) = true → (pref pre m false).getD j false = true) ∧ _
  have agree (n : Nat) : agrees (pref pre n false) (pref pre n true) :=
    prefix_agrees pre _ _ (inputs_agree n) hn
  have output (n : Nat) (b : Bool) :
      (lastTwo (pref pre n b) g h).getD o false = cycle (input n b) :=
    (assembled pre g h o n b).symm.trans (comp _)
  have late : 15 ≤ o := by
    by_contra! lt
    have short (n : Nat) (b : Bool) : (pref pre n b).getD o false = cycle (input n b) :=
      (early _ g h o (by rw [plen hl]; exact lt)).symm.trans (output n b)
    by_cases oz : o = 0
    · have e := short 0 true
      rw [oz,first] at e
      exact (by decide : true ≠ cycle (input 0 true)) e
    · have e := (short 1 false).symm.trans (((agree 1).2 o oz).trans (short 1 true))
      exact (by decide : cycle (input 1 false) ≠ cycle (input 1 true)) e
  constructor
  · intro hv
    by_contra! bad
    have gv : valAt g (pref pre m false) = false := by simpa [sideval pre m false g j hg hp] using bad
    let v := pref pre m false ++ [valAt g (pref pre m false)]
    have wire15 : v.getD 15 false = false := by
      have e := plen hl m false
      change (pref pre m false ++ [_]).getD 15 false = false
      rw [← e]
      simpa using gv
    have hv0 : valAt h v = false := by
      have ex : false ∈ h.inputs.map (fun i => v.getD i false) := List.mem_map.mpr ⟨15,hh,wire15⟩
      simp only [valAt,ha,GateOp.eval,List.all_eq_false] 
      exact ⟨false,ex,by decide⟩
    have lengthv : v.length = 16 := by simp [v,plen hl]
    have hout : (lastTwo (pref pre m false) g h).getD o false = false := by
      change (v ++ [valAt h v]).getD o false = false
      by_cases h15 : o = 15
      · rw [h15,List.getD_append _ _ _ _ (by omega),wire15]
      by_cases h16 : o = 16
      · rw [h16,← lengthv];simpa using hv0
      exact List.getD_eq_default _ _ (by simp; omega)
    rw [output, hv] at hout
    contradiction
  · intro hd
    by_contra! nonzero
    have eqg : valAt g (pref pre m false) = valAt g (pref pre m true) := by
      have good : (pref pre m false).getD j false = true := Bool.eq_true_of_not_eq_false nonzero
      rw [sideval pre m false g j hg hp,sideval pre m true g j hg hp,good]
      rfl
    have hpre : agrees (pref pre m false ++ [valAt g (pref pre m false)])
        (pref pre m true ++ [valAt g (pref pre m true)]) := by
      rw [eqg]
      exact push_agrees _ _ _ (agree m)
    have eh := val_agrees h _ _ hpre hz
    have hfinal : agrees (lastTwo (pref pre m false) g h) (lastTwo (pref pre m true) g h) := by
      dsimp only [lastTwo]
      rw [eh]
      exact push_agrees _ _ _ hpre
    exact hd ((output m false).symm.trans ((hfinal.2 o (by omega)).trans (output m true)))

def sample (m : Nat) (i : Fin 7) : Bool := (2 * m).testBit i.val

def edgePath (m : Nat) : Bool :=
  (m.testBit 0 && m.testBit 1) || (m.testBit 1 && m.testBit 2) ||
  (m.testBit 2 && m.testBit 3) || (m.testBit 3 && m.testBit 4) ||
  (m.testBit 4 && m.testBit 5)

theorem short_prefix (pre : List Gate) (m j : Nat) (hl : pre.length = 8)
    (lo : 7 ≤ j) (hi : j ≤ 12) :
    (run (pre.take (j-6)) (List.ofFn (input m false))).getD j false =
      (pref pre m false).getD j false := by
  let w := List.ofFn (input m false)
  let a := pre.take (j-6)
  let b := pre.drop (j-6)
  have cut : a ++ b = pre := List.take_append_drop _ _
  have index : j < (run a w).length := by simp [a,w,run_len,hl]; omega
  change (run a w).getD j false = (run pre w).getD j false
  conv_rhs => rw [← cut,run_add]
  obtain ⟨t,e,_⟩ := run_extends b (run a w)
  rw [e,List.getD_append _ _ _ _ index]

theorem solve (lower : ∀ (f : (Fin 7 → Bool) → Bool) (s : Nat), HasCircuitSize 7 f s →
    (∀ m : Fin 64, (m.val.testBit 0 || m.val.testBit 5 || edgePath m.val) = true →
      f (sample m.val) = edgePath m.val) → 7 ≤ s)
    (C : Circuit) (i k : Fin C.gates.length) (j : Nat) (hi : i.val = 8)
    (fan : FanInTwo C) (sz : C.size = 10) (comp : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle x)
    (h0 : 0 ∈ (C.gates.get i).inputs)
    (unique : ∀ v : Fin C.gates.length, 0 ∈ (C.gates.get v).inputs → v = i)
    (hor : (C.gates.get i).op = GateOp.or) (hand : (C.gates.get k).op = GateOp.and)
    (later : i.val < k.val) (readi : 7 + i.val ∈ (C.gates.get k).inputs)
    (readj : j ∈ (C.gates.get i).inputs) (lo : 7 ≤ j) (lim : j ≤ 12) : False := by
  have len : C.gates.length = 10 := sz
  have hk : k.val = 9 := by have := k.isLt; omega
  let pre := C.gates.take 8
  let g := C.gates.get i
  let h := C.gates.get k
  have eight : pre.length = 8 := by simp [pre,len]
  have d8 : 8 < C.gates.length := by omega
  have d9 : 9 < C.gates.length := by omega
  have eqi : i = ⟨8,d8⟩ := Fin.ext hi
  have eqk : k = ⟨9,d9⟩ := Fin.ext hk
  have spl : pre ++ [g,h] = C.gates := by
    calc
      pre ++ [g,h] = pre ++ C.gates.drop 8 := by
        apply congrArg (pre ++ ·)
        rw [List.drop_eq_getElem_cons d8, List.drop_eq_getElem_cons d9]
        have last : C.gates.drop 10 = [] := List.drop_eq_nil_iff.mpr (by omega)
        change [g,h] = C.gates[8] :: C.gates[9] :: C.gates.drop 10
        rw [last]
        simp only [g,h,eqi,eqk,List.get_eq_getElem]
      _ = _ := List.take_append_drop _ _
  have pre0 : ∀ t ∈ pre, 0 ∉ t.inputs := by
    intro t ht z
    obtain ⟨n,hn,e⟩ := List.mem_iff_getElem.mp ht
    have nb : n < C.gates.length := by omega
    have same : C.gates[n] = t := by simpa [pre] using e
    have collapse := unique ⟨n,nb⟩ (by simpa [List.get_eq_getElem,same] using z)
    have := congrArg Fin.val collapse
    change n = i.val at this
    omega
  have hz : 0 ∉ h.inputs := by
    intro z
    have e := congrArg Fin.val (unique k z)
    omega
  have hp := pair_inputs g.inputs j (fan g (List.get_mem _ _)).2 h0 readj (by omega)
  have hw : 15 ∈ h.inputs := by simpa [hi,h] using readi
  have realiz : ∀ x : Fin 7 → Bool, Circuit.eval ⟨pre ++ [g,h],C.output⟩ (List.ofFn x) = cycle x := by
    intro x
    rw [spl]
    exact comp x
  let small : Circuit := ⟨pre.take (j-6),j⟩
  let f := fun x : Fin 7 → Bool => small.eval (List.ofFn x)
  have cost : HasCircuitSize 7 f (j-6) := by
    refine ⟨small, ?_, ?_, fun _ => rfl⟩
    · intro t ht
      exact fan t (List.mem_of_mem_take (List.mem_of_mem_take ht))
    · change (pre.take (j-6)).length ≤ _
      simp
  have enough := lower f (j-6) cost (by
    intro m allowed
    have xeq : sample m.val = input m.val false := by
      exact (by decide +kernel : ∀ n : Fin 64, sample n.val = input n.val false) m
    have edge : cycle (input m.val false) = edgePath m.val :=
      (by decide +kernel : ∀ n : Fin 64, cycle (input n.val false) = edgePath n.val) m
    have flip : cycle (input m.val true) = (m.val.testBit 0 || m.val.testBit 5 || edgePath m.val) :=
      (by decide +kernel : ∀ n : Fin 64, cycle (input n.val true) = (n.val.testBit 0 || n.val.testBit 5 || edgePath n.val)) m
    obtain ⟨pos,neg⟩ := output_effect pre g h j C.output eight pre0 hor hp hand hw hz realiz m.val
    rw [xeq]
    change (run (pre.take (j-6)) _).getD j false = _
    rw [short_prefix pre m.val j eight lo lim]
    cases ee : edgePath m.val with
    | false => exact neg (by rw [edge,ee,flip,allowed]; decide)
    | true => exact pos (edge.trans ee))
  omega

end PEqualNP.Outside.L_meta_29920.C7Bridge


theorem PEqualNP.Outside.L_meta_29920 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 11 ∈ (C.gates.get i).inputs ∧ 11 ≠ 0 ∧ 11 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 11 false = true) := by
  rintro ⟨C, i, k, hi, fan, sz, comp, h0, unique, hor, hand, later, readi, readj, _nonzero, _prior, _witness⟩
  exact PEqualNP.Outside.L_meta_29920.C7Bridge.solve PEqualNP.Outside.L_meta_29920.C7Lower.prefix_lower C i k 11
    hi fan sz comp h0 unique hor hand later readi readj (by decide) (by decide)
