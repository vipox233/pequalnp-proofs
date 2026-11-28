import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_931
open Sum (inl inr)
open Function (update update_of_ne update_self iterate_add_apply)
abbrev Q0:=List Bool
abbrev Q1:=List ℕ
abbrev Q2:=List (List ℕ)
abbrev Q3 (n:ℕ):=Finset (Fin n)
abbrev Q4 (n:ℕ):=Finset (Finset (Fin n))
abbrev Q5:=Polynomial ℕ
abbrev Q6 {α β αΓ βΓ:Type}:=@PEqualNP.Library.ComputableInPolyTime α β αΓ βΓ
lemma qa {α:Type*} {s:Finset α} {p:α→Prop} [DecidablePred p] {a:α}:
 a∈s.filter p↔a∈s∧p a:=Finset.mem_filter
lemma qd {α:Type*} [DecidableEq α] {a b:α}:
 a∈({b}:Finset α)↔a=b:=Finset.mem_singleton
lemma qe {α:Type*} [DecidableEq α] {a b:α} {s:Finset α}:
 a∈insert b s↔a=b∨a∈s:=Finset.mem_insert
lemma qc {α:Type*} {s t:Finset α}:
 Disjoint s t↔∀ ⦃a⦄,a∈s→a∉t:=Finset.disjoint_left
lemma qg {α:Type*} [DecidableEq α] {s t:Finset α} {a:α}:
 a∈s \ t↔a∈s∧a∉t:=Finset.mem_sdiff
lemma qh {α:Type*} [DecidableEq α] {s:Finset α} {a b:α}:
 a∈s.erase b↔a≠b∧a∈s:=Finset.mem_erase
lemma qE {α:Type*} [DecidableEq α] {s:Finset α} {a b:α} (h:a∈s.erase b):
 a∈s:=Finset.mem_of_mem_erase h
lemma qj {α β:Type*} [DecidableEq β] {s:Finset α} {t:α→Finset β} {b:β}:
 b∈s.biUnion t↔∃ a∈s,b∈t a:=Finset.mem_biUnion
lemma ql {α:Type*} [DecidableEq α] {s t:Finset α} {a:α}:
 a∈s ∪ t↔a∈s∨a∈t:=Finset.mem_union
lemma qm {α:Type*} [DecidableEq α] {s t:Finset α} {a:α}:
 a∈s ∩ t↔a∈s∧a∈t:=Finset.mem_inter
lemma qN {α β:Type*} [DecidableEq β] {f:α→β} {s:Finset α} {b:β}:
 b∈s.image f↔∃ a∈s,f a=b:=Finset.mem_image
lemma qJ {α:Type*} [Fintype α] (a:α):
 a∈(Finset.univ:Finset α):=Finset.mem_univ a
lemma qH {α:Type*} {s t:Finset α} (h:s⊆t):
 s.card≤t.card:=Finset.card_le_card h
lemma qU {α:Type*} {s:Finset α}:
 0<s.card↔s.Nonempty:=Finset.card_pos
lemma zo {α:Type*} {s t:Finset α} (h1:s⊆t) (h2:t.card≤ s.card):
 s=t:=Finset.eq_of_subset_of_card_le h1 h2
lemma vi {n m:ℕ}:
 m∈Finset.range n↔m<n:=Finset.mem_range
lemma v7 {α:Type*} {s t:Finset α}:
 s∈t.powerset↔s⊆t:=Finset.mem_powerset
lemma zD {α:Type*} {n:ℕ} {s t:Finset α}:
 t∈s.powersetCard n↔t⊆s∧t.card=n:=Finset.mem_powersetCard
lemma zu {α:Type*} [DecidableEq α] {s:Finset α} {a:α} (h:a∈s):
 (s.erase a).card=s.card-1:=Finset.card_erase_of_mem h
lemma z3 {α:Type*} (a:α):
 ({a}:Finset α).card=1:=Finset.card_singleton a
lemma zv {α:Type*} [DecidableEq α] {a b:α} (h:a≠b):
 ({a,b}:Finset α).card=2:=Finset.card_pair h
lemma vj {α:Type*} [DecidableEq α] (a:α) (s:Finset α):
 s.erase a⊆s:=Finset.erase_subset a s
lemma zQ {α:Type*} {a:α} {s:Finset α}:
 a∈(s:Set α)↔a∈s:=Finset.mem_coe
lemma vx {α:Type*} [DecidableEq α] (a:α) (s:Finset α):
 a∈insert a s:=Finset.mem_insert_self a s
lemma vD {α:Type*} [DecidableEq α] {s t:Finset α}:
 s ∩ t⊆s:=Finset.inter_subset_left
lemma vE {α:Type*} {s t:Finset α}:
 ¬ Disjoint s t↔∃ a,a∈s∧a∈t:=Finset.not_disjoint_iff
lemma yk {α:Type*} [DecidableEq α] {s:Finset α}:
 s.card=2↔∃ x y,x≠y∧s={x,y}:=Finset.card_eq_two
lemma yv {α:Type*} (p:α→Prop) [DecidablePred p] (s:Finset α):
 s.filter p⊆s:=Finset.filter_subset p s
lemma qf {α:Type*} {l:List α} {i:ℕ} {d:α}:
 l.getD i d=l[i]?.getD d:=List.getD_eq_getElem?_getD
lemma qn {α:Type*} {l:List α} {i:ℕ} (h:i<l.length):
 l[i]∈l:=List.getElem_mem h
lemma qI {α:Type*} {a:α} {as:List α}:
 (a::as).length=as.length+1:=List.length_cons
lemma qQ {α β:Type*} {f:α→β} {b:β} {l:List α}:
 b∈l.map f↔∃ a∈l,f a=b:=List.mem_map
lemma qw {m n:ℕ}:
 m∈List.range n↔m<n:=List.mem_range
lemma zM {α β:Type*} {f:α→β} {l:List α}:
 (l.map f).length=l.length:=List.length_map f
lemma qX {α:Type*} {l:List α}:
 l++[]=l:=List.append_nil l
lemma vJ {α:Type*} {l:List α}:
 l.reverse.length=l.length:=List.length_reverse
lemma vo {α:Type*} {l:List α} {i:ℕ} (h:l.length≤ i):
 l.take i=l:=List.take_of_length_le h
lemma z4 {α:Type*} {a b:α}:
 a∈[b]↔a=b:=List.mem_singleton
lemma zT {α:Type*} {a b:α} {l:List α}:
 a∈b::l↔a=b∨a∈l:=List.mem_cons
lemma zP {n:ℕ}:
 List.range (n+1)=List.range n++[n]:=List.range_succ
lemma vI {α:Type*} {a:α} {l:List α}:
 a∈l↔∃ (i:ℕ) (h:i<l.length),l[i]=a:=List.mem_iff_getElem
lemma zO {R:Type*} [Semiring R] {p q:Polynomial R} {x:R}:
 (p+q).eval x=p.eval x+q.eval x:=Polynomial.eval_add
lemma z9 {R:Type*} [CommSemiring R] {p q:Polynomial R} {x:R}:
 (p * q).eval x=p.eval x * q.eval x:=Polynomial.eval_mul
lemma vT {R:Type*} [Semiring R] {a x:R}:
 (Polynomial.C a).eval x=a:=Polynomial.eval_C
lemma ze {α:Type*} (f:α→α) (n:ℕ) (x:α):
 f^[n+1] x=f^[n] (f x):=Function.iterate_succ_apply f n x
lemma qM {α:Type*} (f:α→α) (n:ℕ) (x:α):
 f^[n+1] x=f (f^[n] x):=Function.iterate_succ_apply' f n x
lemma yt {a b:ℕ} (h:¬ b<a):a≤b:=Nat.le_of_not_lt h
namespace Lib
abbrev qF (f:Q0→Q0):Prop:=Q6 (fun x:Q0=>x) (fun x:Q0=>x) f
end Lib
section
namespace Lib.qC
open Turing
lemma j9 {σ:Type} (f:σ→Option σ) (n:ℕ):
 (flip bind f)^[n] none=none:=by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [ze]; exact ih
lemma kV {σ τ:Type} (f:σ→Option σ) (g:τ→Option τ) (emb:σ→τ)
 (h:∀ c c',f c=some c'→ g (emb c)=some (emb c')):
 ∀ (n:ℕ) (a b:σ),(flip bind f)^[n] (some a)=some b→
   (flip bind g)^[n] (some (emb a))=some (emb b):=by
 intro n;induction n with
 | zero=>intro a b hab;have:a=b:=Option.some.inj hab;rw [this]; rfl
 | succ n ih=>
   intro a b hab;rw [ze] at hab ⊢
   cases hfa:f a with
   | none=>have e:flip bind f (some a)=none:=hfa;rw [e,j9] at hab;exact absurd hab (by simp)
   | some c=>have e:flip bind f (some a)=some c:=hfa;have e':flip bind g (some (emb a))=some (emb c):=h a c hfa;rw [e] at hab;rw [e'];exact ih c b hab
section vM
variable {K:Type} [DecidableEq K] {Γ:K→Type} {Λ σ:Type}
def vM:TM2.Stmt Γ Λ σ→ℕ
 | .push _ _ q=>vM q+1
 | .peek _ _ q=>vM q
 | .pop _ _ q=>vM q
 | .load _ q=>vM q
 | .branch _ q₁ q₂=>max (vM q₁) (vM q₂)
 | .goto _=>0
 | .halt=>0
lemma qau (q:TM2.Stmt Γ Λ σ) (v:σ) (S:∀ k,List (Γ k)) (k:K):
 ((TM2.stepAux q v S).stk k).length≤(S k).length+vM q:=by
 induction q generalizing v S with
 | push k' f q ih=>
   simp only [TM2.stepAux,vM];refine (ih _ _).trans ?_
   by_cases h:k=k'
   · subst h;rw [update_self,qI]; omega
   · rw [update_of_ne h]; omega
 | peek k' f q ih=>exact ih _ _
 | pop k' f q ih=>
   simp only [TM2.stepAux,vM];refine (ih _ _).trans ?_
   by_cases h:k=k'
   · subst h;rw [update_self,List.length_tail]; omega
   · rw [update_of_ne h]
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [TM2.stepAux,vM]
   cases f v
   · exact (ih₂ v S).trans (by have:=le_max_right (vM q₁) (vM q₂); omega)
   · exact (ih₁ v S).trans (by have:=le_max_left (vM q₁) (vM q₂); omega)
 | goto f=>simp [TM2.stepAux,vM]
 | halt=>simp [TM2.stepAux,vM]
end vM
noncomputable def yh (tm:FinTM2):ℕ:=(@Finset.univ tm.Λ tm.ΛFin).sup fun l=>vM (tm.m l)
lemma qbP (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
 (h:TM2.step tm.m c=some c') (k:tm.K):
 (c'.stk k).length≤(c.stk k).length+yh tm:=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
   simp only [TM2.step,Option.some.injEq] at h;subst h;refine (qau _ _ _ _).trans ?_
   have:vM (tm.m l)≤yh tm:=Finset.le_sup (f:=fun l=>vM (tm.m l)) (@qJ tm.Λ tm.ΛFin l)
   simpa using this
lemma jR (tm:FinTM2) (k:tm.K):
 ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),(flip bind (TM2.step tm.m))^[n] (some a)=some b→
   (b.stk k).length≤(a.stk k).length+yh tm * n:=by
 intro n;induction n with
 | zero=>intro a b hab;have:a=b:=Option.some.inj hab;rw [this]; simp
 | succ n ih=>
   intro a b hab;rw [ze] at hab
   cases hfa:TM2.step tm.m a with
   | none=>have e:flip bind (TM2.step tm.m) (some a)=none:=hfa;rw [e,j9] at hab;exact absurd hab (by simp)
   | some c=>have e:flip bind (TM2.step tm.m) (some a)=some c:=hfa;rw [e] at hab;have h1:=ih c b hab;have h2:=qbP tm a c hfa k;rw [Nat.mul_succ]; omega
lemma zH (tm:FinTM2) (s:List (tm.Γ tm.k₀)):
 initList tm s=
  (⟨some tm.main,tm.initialState,update (fun _=>[]) tm.k₀ s⟩:
    TM2.Cfg tm.Γ tm.Λ tm.σ):=by
 unfold initList;congr 1
 funext k
 by_cases h:k=tm.k₀
 · subst h; simp
 · simp [h]
lemma zG (tm:FinTM2) (s:List (tm.Γ tm.k₁)):
 haltList tm s=
  (⟨none,tm.initialState,update (fun _=>[]) tm.k₁ s⟩:
    TM2.Cfg tm.Γ tm.Λ tm.σ):=by
 unfold haltList;congr 1
 funext k
 by_cases h:k=tm.k₁
 · subst h; simp
 · simp [h]
lemma y7 (p:Q5) {x y:ℕ} (h:x≤y):p.eval x≤p.eval y:=by
 induction p using Polynomial.induction_on' with
 | add p q hp hq=>rw [zO,zO]; exact add_le_add hp hq
 | monomial d c=>rw [Polynomial.eval_monomial,Polynomial.eval_monomial];exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.qC
end
section
namespace Lib.qC
open Turing
def jQ:Q0→TM2.Stmt (fun _:Unit=>Bool) Unit Bool
 | []=>.halt
 | a::l=>.push () (fun _=>a) (jQ l)
def vq (l:Q0):Unit→TM2.Stmt (fun _:Unit=>Bool) Unit Bool:=
 fun _=>.pop () (fun _ o=>o.isSome)
  (.branch (fun s=>s)
    (.load (fun _=>false) (.goto fun _=>()))
    (jQ l.reverse))
def ku (l:Q0):FinTM2 where
 K:=Unit
 k₀:=()
 k₁:=()
 Γ _:=Bool
 Λ:=Unit
 main:=()
 σ:=Bool
 initialState:=false
 m:=vq l
abbrev jB:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
lemma kO (S T:Q0):
 update (fun _:Unit=>S) () T=fun _=>T:=by
 funext k
 simp
lemma w1 (l:Q0) (v:Bool) (S:Q0):
 TM2.stepAux (jQ l) v (fun _:Unit=>S)=
  (⟨none,v,fun _=>l.reverse++S⟩:jB):=by
 induction l generalizing S with
 | nil=>rfl
 | cons a l ih=>simp only [jQ,TM2.stepAux];rw [kO,ih];simp
lemma qaj (l:Q0) (x:Bool) (a:Q0):
 TM2.step (vq l) (⟨some (),false,fun _=>x::a⟩:jB)=
  some ⟨some (),false,fun _=>a⟩:=by
 simp only [TM2.step,vq,TM2.stepAux];rw [kO];simp
lemma qaN (l:Q0):
 TM2.step (vq l) (⟨some (),false,fun _=>[]⟩:jB)=
  some ⟨none,false,fun _=>l⟩:=by
 simp only [TM2.step,vq,TM2.stepAux];rw [kO];simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
 rw [w1];simp
lemma qak (l:Q0) (a:Q0):
 (flip bind (TM2.step (vq l)))^[a.length+1]
   (some (⟨some (),false,fun _=>a⟩:jB))=
   some ⟨none,false,fun _=>l⟩:=by
 induction a with
 | nil=>exact qaN l
 | cons x a ih=>
   rw [qI,ze]
   have e:flip bind (TM2.step (vq l))
    (some (⟨some (),false,fun _=>x::a⟩:jB))=
    some ⟨some (),false,fun _=>a⟩:=qaj l x a
   rw [e,ih]
lemma qaO (l:Q0) (a:Q0):
 (flip bind (TM2.step (vq l)))^[a.length+1]
   (some (initList (ku l) a))=some (haltList (ku l) l):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (vq l)))^[a.length+1]
  (some c)) (zH (ku l) a)).trans
  (Eq.trans ?_ (congrArg some (zG (ku l) l)).symm)
 show (flip bind (TM2.step (vq l)))^[a.length+1]
  (some (⟨some (),false,update (fun _=>[]) () a⟩:jB))=
  some (⟨none,false,update (fun _=>[]) () l⟩:jB)
 rw [kO,kO];exact qak l a
lemma yO (l:Q0):
 Nonempty (Turing.TM2ComputableInPolyTime (fun x:Q0=>x)
  (fun x:Q0=>x) (fun _:Q0=>l)):=
 ⟨{
   tm:=ku l
   inputAlphabet:=Equiv.refl _
   outputAlphabet:=Equiv.refl _
   time:=Polynomial.X+1
   outputsFun:=fun a=>
    { steps:=a.length+1
      evals_in_steps:=by
       have hm:∀ l:Q0,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
       exact (congrArg (fun x=>(flip bind (TM2.step (vq l)))^[a.length+1]
        (some (initList (ku l) x))) (hm a)).trans
        ((qaO l a).trans
          (congrArg (fun x=>some (haltList (ku l) x)) (hm l).symm))
      steps_le_m:=by simp } }⟩
end Lib.qC
end
section
namespace Lib.qC
open Turing
section update
variable {ι:Type} [DecidableEq ι] {β:ι→Type}
lemma wQ (E:∀ i,β i) {a b c:ι} (hab:a≠b) (hac:a≠c)
 (x x':β a) (y:β b) (z:β c):
 update (update (update (update E a x) b y) c z) a x'=
  update (update (update E a x') b y) c z:=by
 rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
lemma wR (E:∀ i,β i) {a b c:ι} (hbc:b≠c)
 (x:β a) (y y':β b) (z:β c):
 update (update (update (update E a x) b y) c z) b y'=
  update (update (update E a x) b y') c z:=by
 rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Option (M1.K ⊕ M2.K)
abbrev CΓ:CK M1 M2→Type
 | none=>M2.Γ M2.k₀
 | some (inl k)=>M1.Γ k
 | some (inr k)=>M2.Γ k
abbrev CΛ:Type:=M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ:Type:=M1.σ×M2.σ×Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q=>.push (some (inl k)) (fun s=>f s.1) (tr1 q)
 | .peek k f q=>.peek (some (inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
 | .pop k f q=>.pop (some (inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (tr1 q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (tr1 q₁) (tr1 q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr (inr false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q=>.push (some (inr k)) (fun s=>f s.2.1) (tr2 q)
 | .peek k f q=>.peek (some (inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .pop k f q=>.pop (some (inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .load a q=>.load (fun s=>(s.1,a s.2.1,s.2.2)) (tr2 q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.2.1) (tr2 q₁) (tr2 q₂)
 | .goto f=>.goto (fun s=>inr (inl (f s.2.1)))
 | .halt=>.halt
variable (M1 M2)
def tA (φ:M1.Γ M1.k₁→M2.Γ M2.k₀):
    Option (M2.Γ M2.k₀)→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none=>.goto (fun _=>inr (inl M2.main))
 | some d=>
   .pop (some (inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map φ))
     (.branch (fun s=>s.2.2.isSome)
       (.push none (fun s=>s.2.2.getD d) (.goto fun _=>inr (inr false)))
       (.goto fun _=>inr (inr true)))
def tB:Option (M2.Γ M2.k₀)→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none=>.goto (fun _=>inr (inl M2.main))
 | some d=>
   .pop none (fun s o=>(s.1,s.2.1,o))
     (.branch (fun s=>s.2.2.isSome)
       (.push (some (inr M2.k₀)) (fun s=>s.2.2.getD d)
         (.goto fun _=>inr (inr true)))
       (.goto fun _=>inr (inl M2.main)))
def yZ (φ:M1.Γ M1.k₁→M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):
    CΛ M1 M2→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | inl l=>tr1 (M1.m l)
 | inr (inl l)=>tr2 (M2.m l)
 | inr (inr false)=>tA M1 M2 φ d
 | inr (inr true)=>tB M1 M2 d
def comp (φ:M1.Γ M1.k₁→M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2:=haveI:=M1.kFin
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
   m:=yZ M1 M2 φ d }
variable {M1 M2}
def ud (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
 | none=>[]
 | some (inl k)=>S k
 | some (inr _)=>[]
def ue (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
 | none=>[]
 | some (inl _)=>[]
 | some (inr k)=>S k
lemma kA (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)):
 (ud (update S k x):∀ k,List (CΓ M1 M2 k))=
   update (ud S) (some (inl k)) x:=by
 funext j
 rcases j with _|j|j
 · rw [update_of_ne (by simp)]; rfl
 · by_cases h:j=k
   · subst h;rw [update_self];show update S j x j=x;rw [update_self]
   · rw [update_of_ne (by simpa using h)];show update S k x j=S j;rw [update_of_ne h]
 · rw [update_of_ne (by simp)]; rfl
lemma kB (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)):
 (ue (update S k x):∀ k,List (CΓ M1 M2 k))=
   update (ue S) (some (inr k)) x:=by
 funext j
 rcases j with _|j|j
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · by_cases h:j=k
   · subst h;rw [update_self];show update S j x j=x;rw [update_self]
   · rw [update_of_ne (by simpa using h)];show update S k x j=S j;rw [update_of_ne h]
lemma wI:
 (ud (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
 funext j; rcases j with _|j|j <;> rfl
lemma wJ:
 (ue (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
 funext j; rcases j with _|j|j <;> rfl
def qao (w:M2.σ×Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ):
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2):=
 ⟨some (c.l.elim (inr (inr false)) inl),(c.var,w),ud c.stk⟩
def qap (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ):
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2):=
 ⟨c.l.map (fun l=>inr (inl l)),(u,c.var,b),ue c.stk⟩
lemma qfk (w:M2.σ×Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
 (S:∀ k,List (M1.Γ k)):
 TM2.stepAux (tr1 q) ((v,w):Cσ M1 M2) (ud S)=qao w (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>have:=ih v (update S k (f v::S k));rw [kA] at this;exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>have:=ih (f v (S k).head?) (update S k (S k).tail);rw [kA] at this;exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [tr1,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
lemma qfl (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
 (S:∀ k,List (M2.Γ k)):
 TM2.stepAux (tr2 q) ((u,v,b):Cσ M1 M2) (ue S)=qap u b (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>have:=ih v (update S k (f v::S k));rw [kB] at this;exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>have:=ih (f v (S k).head?) (update S k (S k).tail);rw [kB] at this;exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [tr2,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
variable (φ:M1.Γ M1.k₁→M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
lemma qfe (w:M2.σ×Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
 (h:TM2.step M1.m c=some c'):
 TM2.step (yZ M1 M2 φ d) (qao w c)=some (qao w c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>simp only [TM2.step,Option.some.injEq] at h;subst h;exact congrArg some (qfk w (M1.m l) v S)
lemma qff (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
 (h:TM2.step M2.m c=some c'):
 TM2.step (yZ M1 M2 φ d) (qap u b c)=some (qap u b c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>simp only [TM2.step,Option.some.injEq] at h;subst h;exact congrArg some (qfl u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k):=
 update (update (update (fun _=>[])
  (some (inl M1.k₁)) l) none t) (some (inr M2.k₀)) u
lemma qc6 (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 (st l t u:∀ k,List (CΓ M1 M2 k)) (some (inl M1.k₁))=l:=by
 unfold st;rw [update_of_ne (by simp),update_of_ne (by simp),update_self]
lemma qby (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:=by
 unfold st;rw [update_of_ne (by simp),update_self]
lemma qeU (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 (st l t u:∀ k,List (CΓ M1 M2 k)) (some (inr M2.k₀))=u:=by
 unfold st;rw [update_self]
lemma qae (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (inl M1.k₁)) l'=st l' t u:=
 wQ _ (by simp) (by simp) _ _ _ _
lemma jS (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)):
 update (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u:=
 wR _ (by simp) _ _ _ _
lemma qcs (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)):
 update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (inr M2.k₀)) u'=st l t u':=
 Function.update_idem _ _ _
lemma qdv (l:List (M1.Γ M1.k₁)):
 (st l [] []:∀ k,List (CΓ M1 M2 k))=
   update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (inl M1.k₁)) l:=by
 unfold st;rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [update_of_ne (by simp)]
 · rw [update_of_ne (by simp),update_of_ne (by simp)]
lemma qeT (u:List (M2.Γ M2.k₀)):
 (st [] [] u:∀ k,List (CΓ M1 M2 k))=
   update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (inr M2.k₀)) u:=by
 unfold st;congr 1;rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [update_of_ne (by simp)]
end Lib.qC
end
section
namespace Lib.qC
open Turing
variable {M1 M2:FinTM2} (φ:M1.Γ M1.k₁→M2.Γ M2.k₀)
abbrev kR (M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
lemma qct (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 TM2.step (yZ M1 M2 φ (some dd))
  (⟨some (inr (inr false)),(v1,v2,b),st (x::l) t u⟩:kR M1 M2)=
  some ⟨some (inr (inr false)),(v1,v2,some (φ x)),st l (φ x::t) u⟩:=by
 simp only [TM2.step,yZ,tA,TM2.stepAux];rw [qc6];simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,Option.getD_some]
 rw [qae,qby,jS]
lemma qc7 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (t u:List (M2.Γ M2.k₀)):
 TM2.step (yZ M1 M2 φ (some dd))
  (⟨some (inr (inr false)),(v1,v2,b),st [] t u⟩:kR M1 M2)=
  some ⟨some (inr (inr true)),(v1,v2,none),st [] t u⟩:=by
 simp only [TM2.step,yZ,tA,TM2.stepAux];rw [qc6];simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
 rw [qae]
lemma qcu (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)):
 TM2.step (yZ M1 M2 φ (some dd))
  (⟨some (inr (inr true)),(v1,v2,b),st [] (x::t) u⟩:kR M1 M2)=
  some ⟨some (inr (inr true)),(v1,v2,some x),st [] t (x::u)⟩:=by
 simp only [TM2.step,yZ,tB,TM2.stepAux];rw [qby];simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
 rw [jS,qeU,qcs]
lemma qc8 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (u:List (M2.Γ M2.k₀)):
 TM2.step (yZ M1 M2 φ (some dd))
  (⟨some (inr (inr true)),(v1,v2,b),st [] [] u⟩:kR M1 M2)=
  some ⟨some (inr (inl M2.main)),(v1,v2,none),st [] [] u⟩:=by
 simp only [TM2.step,yZ,tB,TM2.stepAux];rw [qby];simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [jS]
lemma qe7 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)):
 ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
   (flip bind (TM2.step (yZ M1 M2 φ (some dd))))^[l.length+1]
     (some (⟨some (inr (inr false)),(v1,v2,b),st l t u⟩:kR M1 M2))=
     some ⟨some (inr (inr true)),(v1,v2,none),st [] ((l.map φ).reverse++t) u⟩:=by
 intro l;induction l with
 | nil=>intro t b; exact qc7 φ dd v1 v2 b t u
 | cons x l ih=>
   intro t b;rw [qI,ze]
   have e:flip bind (TM2.step (yZ M1 M2 φ (some dd)))
    (some (⟨some (inr (inr false)),(v1,v2,b),st (x::l) t u⟩:kR M1 M2))=
    some ⟨some (inr (inr false)),(v1,v2,some (φ x)),st l (φ x::t) u⟩:=
    qct φ dd v1 v2 b x l t u
   rw [e,ih];simp
lemma qe8 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ):
 ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
   (flip bind (TM2.step (yZ M1 M2 φ (some dd))))^[t.length+1]
     (some (⟨some (inr (inr true)),(v1,v2,b),st [] t u⟩:kR M1 M2))=
     some ⟨some (inr (inl M2.main)),(v1,v2,none),st [] [] (t.reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro u b; exact qc8 φ dd v1 v2 b u
 | cons x t ih=>
   intro u b;rw [qI,ze]
   have e:flip bind (TM2.step (yZ M1 M2 φ (some dd)))
    (some (⟨some (inr (inr true)),(v1,v2,b),st [] (x::t) u⟩:kR M1 M2))=
    some ⟨some (inr (inr true)),(v1,v2,some x),st [] t (x::u)⟩:=
    qcu φ dd v1 v2 b x t u
   rw [e,ih];simp
lemma qdE (d:Option (M2.Γ M2.k₀)) (hd:d=none→IsEmpty (M2.Γ M2.k₀))
 (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)):
 ∃ n,n≤2 * o.length+2∧
   (flip bind (TM2.step (yZ M1 M2 φ d)))^[n]
     (some (⟨some (inr (inr false)),(v1,v2,none),
       update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (inl M1.k₁)) o⟩:
       kR M1 M2))=
     some ⟨some (inr (inl M2.main)),(v1,v2,none),
      update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (inr M2.k₀))
       (o.map φ)⟩:=by
 cases d with
 | none=>
   have:=hd rfl
   have ho:o=[]:=by
    cases o with
    | nil=>rfl
    | cons x _=>exact (IsEmpty.false (φ x)).elim
   subst ho;refine ⟨1,by omega,?_⟩
   show some _=some _;simp only [yZ,tA,TM2.stepAux,List.map_nil];rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
 | some dd=>
   refine ⟨((o.map φ).reverse++[]).length+1+(o.length+1),by simp; omega,?_⟩
   rw [iterate_add_apply,← qdv,qe7,qe8,← qeT];simp
lemma qcM (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)):
 qao (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:=by
 rw [zH];refine Eq.trans ?_ (zH (comp M1 M2 φ d) i).symm
 show (⟨_,_,ud _⟩:kR M1 M2)=_;rw [kA,wI];rfl
lemma qcL (w:M2.σ×Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)):
 qao w (haltList M1 o)=
  (⟨some (inr (inr false)),(M1.initialState,w),
    update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (inl M1.k₁)) o⟩:
    kR M1 M2):=by
 rw [zG];show (⟨_,_,ud _⟩:kR M1 M2)=_;rw [kA,wI];rfl
lemma qcO (u:M1.σ) (i:List (M2.Γ M2.k₀)):
 qap u none (initList M2 i)=
  (⟨some (inr (inl M2.main)),(u,M2.initialState,none),
    update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (inr M2.k₀)) i⟩:
    kR M1 M2):=by
 rw [zH];show (⟨_,_,ue _⟩:kR M1 M2)=_;rw [kB,wJ];rfl
lemma qcN (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)):
 qap M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:=by
 rw [zG];refine Eq.trans ?_ (zG (comp M1 M2 φ d) o).symm
 show (⟨_,_,ue _⟩:kR M1 M2)=_;rw [kB,wJ];rfl
lemma qa7 (d:Option (M2.Γ M2.k₀)) (hd:d=none→IsEmpty (M2.Γ M2.k₀))
 (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
 (h1:(flip bind (TM2.step M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
 (h2:(flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ)))=some (haltList M2 o2)):
 ∃ n,n≤ s1+(2 * o1.length+2)+s2∧o1.length≤ i.length+yh M1 * s1∧
   (flip bind (TM2.step (yZ M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i))=
     some (haltList (comp M1 M2 φ d) o2):=by
 have p1:=kV (TM2.step M1.m) (TM2.step (yZ M1 M2 φ d))
  (qao (M2.initialState,none)) (qfe φ d _) s1 _ _ h1
 rw [qcM φ d,qcL] at p1;obtain ⟨nt,hnt,pt⟩:=qdE φ d hd M1.initialState M2.initialState o1
 have p2:=kV (TM2.step M2.m) (TM2.step (yZ M1 M2 φ d))
  (qap M1.initialState none) (qff φ d _ _) s2 _ _ h2
 rw [qcO,qcN φ d] at p2;refine ⟨s2+(nt+s1),by omega,?_,?_⟩
 · have:=jR M1 M1.k₁ s1 _ _ h1;rw [zG,zH] at this;simp only [update_self] at this;refine this.trans (Nat.add_le_add_right ?_ _)
   by_cases h:M1.k₁=M1.k₀
   · rw [h,update_self]
   · rw [update_of_ne h]; simp
 · rw [iterate_add_apply,iterate_add_apply,p1,pt,p2];rfl
lemma qaM {α β γ αΓ βΓ γΓ:Type} (ea:α→List αΓ) (eb:β→List βΓ)
 (ec:γ→List γΓ) (f:α→β) (g:β→γ) (c1:TM2ComputableInPolyTime ea eb f)
 (c2:TM2ComputableInPolyTime eb ec g):
 Nonempty (TM2ComputableInPolyTime ea ec (fun a=>g (f a))):=by
 classical
 let φ:c1.tm.Γ c1.tm.k₁→c2.tm.Γ c2.tm.k₀:=fun x=>c2.inputAlphabet.invFun (c1.outputAlphabet x)
 let d:Option (c2.tm.Γ c2.tm.k₀):=if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
 have hd:d=none→IsEmpty (c2.tm.Γ c2.tm.k₀):=by
  intro h;by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
  · simp [d,hn] at h
  · exact not_nonempty_iff.mp hn
 let T:Q5:=c1.time+(Polynomial.C 2 * (Polynomial.X+Polynomial.C (yh c1.tm) * c1.time)+Polynomial.C 2)+c2.time.comp (Polynomial.X+Polynomial.C (yh c1.tm) * c1.time)
 have key:∀ a,∃ n,n≤T.eval (ea a).length∧
  (flip bind (TM2.step (yZ c1.tm c2.tm φ d)))^[n]
    (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a))))=
    some (haltList (comp c1.tm c2.tm φ d)
     (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
  intro a;have r1:=c1.outputsFun a;have r2:=c2.outputsFun (f a)
  have hφ:(List.map c1.outputAlphabet.invFun (eb (f a))).map φ=
   List.map c2.inputAlphabet.invFun (eb (f a)):=by
   rw [List.map_map];refine List.map_congr_left fun y _=>?_
   show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_;exact congrArg _ (c1.outputAlphabet.right_inv y)
  have h2:(flip bind (TM2.step c2.tm.m))^[r2.steps]
   (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ)))=
   some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
   rw [hφ]; exact r2.evals_in_steps
  obtain ⟨n,hn,h1,h0⟩:=qa7 φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2;refine ⟨n,hn.trans ?_,h0⟩
  have b1:=r1.steps_le_m;have b2:=r2.steps_le_m;simp only [zM] at h1
  have hmul:yh c1.tm * r1.steps≤
   yh c1.tm * Polynomial.eval (ea a).length c1.time:=Nat.mul_le_mul_left _ b1
  have b3:Polynomial.eval (eb (f a)).length c2.time≤
   Polynomial.eval ((ea a).length+yh c1.tm * Polynomial.eval (ea a).length c1.time)
    c2.time:=y7 _ (by omega)
  simp only [T,zO,z9,vT,Polynomial.eval_X,Polynomial.eval_comp,zM];omega
 exact ⟨{
  tm:=comp c1.tm c2.tm φ d
  inputAlphabet:=c1.inputAlphabet
  outputAlphabet:=c2.outputAlphabet
  time:=T
  outputsFun:=fun a=>⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,(Classical.choose_spec (key a)).1⟩ }⟩
end Lib.qC
end
section
namespace Lib.qC
open Turing
variable {Γ₀ Γ₁:Type}
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool→Type
 | some false=>Γ₀
 | none=>Option Γ₀
 | some true=>Γ₁
def yq (φ:Γ₀→Option Γ₁) (d:Option Γ₁):Bool→TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
 | false=>
   .pop (some false) (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push none (fun s=>s) (.goto fun _=>false))
       (.goto fun _=>true))
 | true=>
   .pop none (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (.branch (fun s=>(s.bind φ).isSome)
         (match d with
           | some dd=>.push (some true) (fun s=>(s.bind φ).getD dd) (.goto fun _=>true)
           | none=>.goto fun _=>true)
         (.goto fun _=>true))
       .halt)
def fm [Fintype Γ₀] (φ:Γ₀→Option Γ₁) (d:Option Γ₁):FinTM2 where
 K:=Option Bool
 k₀:=some false
 k₁:=some true
 Γ:=FΓ Γ₀ Γ₁
 Λ:=Bool
 main:=false
 σ:=Option Γ₀
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
 m:=yq φ d
def vL (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k):=
 update (update (update (fun _=>[])
  (some false) l) none t) (some true) u
lemma qbg (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 vL l t u (some false)=l:=by
 unfold vL;rw [update_of_ne (by simp),update_of_ne (by simp),update_self]
lemma wX (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 vL l t u none=t:=by
 unfold vL;rw [update_of_ne (by simp),update_self]
lemma qdm (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 vL l t u (some true)=u:=by
 unfold vL;rw [update_self]
lemma j8 (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 update (vL l t u) (some false) l'=vL l' t u:=
 wQ _ (by simp) (by simp) _ _ _ _
lemma uX (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁):
 update (vL l t u) none t'=vL l t' u:=
 wR _ (by simp) _ _ _ _
lemma qbh (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁):
 update (vL l t u) (some true) u'=vL l t u':=
 Function.update_idem _ _ _
lemma qcf (l:List Γ₀):
 (vL l [] []:∀ k,List (FΓ Γ₀ Γ₁ k))=
   update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:=by
 unfold vL;rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [update_of_ne (by simp)]
 · rw [update_of_ne (by simp),update_of_ne (by simp)]
lemma qdl (u:List Γ₁):
 (vL [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k))=
   update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:=by
 unfold vL;congr 1;rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [update_of_ne (by simp)]
abbrev jh (Γ₀ Γ₁:Type):Type:=TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ:Γ₀→Option Γ₁) (d:Option Γ₁)
lemma qdj (b:Option Γ₀) (x:Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (yq φ d) (⟨some false,b,vL (x::l) t u⟩:jh Γ₀ Γ₁)=
  some ⟨some false,some x,vL l (some x::t) u⟩:=by
 simp only [TM2.step,yq,TM2.stepAux];rw [qbg];simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
 rw [j8,wX,uX]
lemma qd0 (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (yq φ d) (⟨some false,b,vL [] t u⟩:jh Γ₀ Γ₁)=
  some ⟨some true,none,vL [] t u⟩:=by
 simp only [TM2.step,yq,TM2.stepAux];rw [qbg];simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [j8]
lemma qdk (hd:d=none→∀ x,φ x=none) (b:Option Γ₀) (x:Γ₀)
 (t:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (yq φ d) (⟨some true,b,vL [] (some x::t) u⟩:jh Γ₀ Γ₁)=
  some ⟨some true,some x,vL [] t ((φ x).toList++u)⟩:=by
 simp only [TM2.step,yq,TM2.stepAux];rw [wX];simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,Bool.cond_true,Option.bind_some]
 rw [uX]
 cases hφ:φ x with
 | none=>simp
 | some y=>
   cases d with
   | none=>rw [hd rfl x] at hφ; exact absurd hφ (by simp)
   | some dd=>simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,Option.toList_some,List.singleton_append];rw [qdm,qbh];simp [hφ]
lemma qd1 (b:Option Γ₀) (u:List Γ₁):
 TM2.step (yq φ d) (⟨some true,b,vL [] [] u⟩:jh Γ₀ Γ₁)=
  some ⟨none,none,vL [] [] u⟩:=by
 simp only [TM2.step,yq,TM2.stepAux];rw [wX];simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,Bool.cond_false]
 rw [uX]
lemma qd2 (u:List Γ₁):
 ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
   (flip bind (TM2.step (yq φ d)))^[l.length+1]
     (some (⟨some false,b,vL l t u⟩:jh Γ₀ Γ₁))=
     some ⟨some true,none,vL [] (l.reverse.map some++t) u⟩:=by
 intro l;induction l with
 | nil=>intro t b; exact qd0 φ d b t u
 | cons x l ih=>
   intro t b;rw [qI,ze]
   have e:flip bind (TM2.step (yq φ d))
    (some (⟨some false,b,vL (x::l) t u⟩:jh Γ₀ Γ₁))=
    some ⟨some false,some x,vL l (some x::t) u⟩:=qdj φ d b x l t u
   rw [e,ih];simp
lemma qd3 (hd:d=none→∀ x,φ x=none):
 ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
   (flip bind (TM2.step (yq φ d)))^[t.length+1]
     (some (⟨some true,b,vL [] (t.map some) u⟩:jh Γ₀ Γ₁))=
     some ⟨none,none,vL [] [] ((t.filterMap φ).reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro u b; exact qd1 φ d b u
 | cons x t ih=>
   intro u b;rw [qI,ze]
   have e:flip bind (TM2.step (yq φ d))
    (some (⟨some true,b,vL [] ((x::t).map some) u⟩:jh Γ₀ Γ₁))=
    some ⟨some true,some x,vL [] (t.map some) ((φ x).toList++u)⟩:=
    qdk φ d hd b x (t.map some) u
   rw [e,ih]
   cases hφ:φ x <;> simp [hφ]
lemma qeK [Fintype Γ₀] (hd:d=none→∀ x,φ x=none) (l:List Γ₀):
 (flip bind (TM2.step (yq φ d)))^[l.length+1+(l.length+1)]
   (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (yq φ d)))^[l.length+1+(l.length+1)]
  (some c)) (zH (fm φ d) l)).trans
  (Eq.trans ?_ (congrArg some (zG (fm φ d) (l.filterMap φ))).symm)
 show (flip bind (TM2.step (yq φ d)))^[l.length+1+(l.length+1)]
  (some (⟨some false,none,update (fun _=>[]) (some false) l⟩:jh Γ₀ Γ₁))=
  some (⟨none,none,update (fun _=>[]) (some true) (l.filterMap φ)⟩:jh Γ₀ Γ₁)
 rw [iterate_add_apply,← qcf,qd2,← qdl];have:=qd3 φ d hd l.reverse [] none;rw [vJ] at this;simpa [List.filterMap_reverse] using this
lemma yS {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (φ:αΓ→Option βΓ)
 (h:∀ a,eb (f a)=(ea a).filterMap φ):
 Nonempty (TM2ComputableInPolyTime ea eb f):=by
 classical
 let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
 have hd:d=none→∀ x,φ x=none:=by
  intro hdn x;by_cases hn:Nonempty βΓ
  · simp [d,hn] at hdn
  · cases hφ:φ x with
    | none=>rfl
    | some y=>exact absurd ⟨y⟩ hn
 exact ⟨{
  tm:=fm φ d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 2
  outputsFun:=fun a=>
   { steps:=(ea a).length+1+((ea a).length+1)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      have:=qeK φ d hd (ea a)
      exact (congrArg (fun l=>(flip bind (TM2.step (yq φ d)))^[(ea a).length+1 +
       ((ea a).length+1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
       (this.trans (congrArg (fun l=>some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
     steps_le_m:=by simp only [zO,z9,vT,Polynomial.eval_X];omega } }⟩
end Lib.qC
end
section
namespace Lib.qC
open Turing
inductive TPK:Type
 | inp|t1|t2|t3|out
 deriving DecidableEq
instance:Fintype TPK:=Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x=>by cases x <;> simp)
inductive TPL:Type
 | a|b|c|e
 deriving DecidableEq
instance:Fintype TPL:=Fintype.ofList [.a,.b,.c,.e] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁:Type}
abbrev TPΓ (Γ₀ Γ₁:Type):TPK→Type
 | .inp=>Γ₀
 | .t1=>Option Γ₀
 | .t2=>Option Γ₀
 | .t3=>Option Γ₀
 | .out=>Γ₁
def uS (φ:Γ₀→Option Γ₁) (d:Option Γ₁) (lbl:TPL):
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀):=
 .branch (fun s=>(s.bind φ).isSome)
   (match d with
     | some dd=>.push .out (fun s=>(s.bind φ).getD dd) (.goto fun _=>lbl)
     | none=>.goto fun _=>lbl)
   (.goto fun _=>lbl)
def zC (φ₁ φ₂:Γ₀→Option Γ₁) (d:Option Γ₁):
    TPL→TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
 | .a=>
   .pop .inp (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push .t1 (fun s=>s) (.goto fun _=>.a))
       (.goto fun _=>.b))
 | .b=>
   .pop .t1 (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (.push .t2 (fun s=>s) (uS φ₂ d .b))
       (.goto fun _=>.c))
 | .c=>
   .pop .t2 (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (.push .t3 (fun s=>s) (.goto fun _=>.c))
       (.goto fun _=>.e))
 | .e=>
   .pop .t3 (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (uS φ₁ d .e)
       .halt)
def tp [Fintype Γ₀] (φ₁ φ₂:Γ₀→Option Γ₁) (d:Option Γ₁):FinTM2 where
 K:=TPK
 k₀:=.inp
 k₁:=.out
 Γ:=TPΓ Γ₀ Γ₁
 Λ:=TPL
 main:=.a
 σ:=Option Γ₀
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
 m:=zC φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
 | .inp=>l
 | .t1=>a
 | .t2=>b
 | .t3=>c
 | .out=>u
lemma wN (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):
 update (st5 l a b c u) .inp l'=st5 l' a b c u:=by
 funext k; cases k <;> simp [st5]
lemma uO (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁):
 update (st5 l a b c u) .t1 a'=st5 l a' b c u:=by
 funext k; cases k <;> simp [st5]
lemma uP (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁):
 update (st5 l a b c u) .t2 b'=st5 l a b' c u:=by
 funext k; cases k <;> simp [st5]
lemma uQ (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁):
 update (st5 l a b c u) .t3 c'=st5 l a b c' u:=by
 funext k; cases k <;> simp [st5]
lemma wO (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁):
 update (st5 l a b c u) .out u'=st5 l a b c u':=by
 funext k; cases k <;> simp [st5]
lemma qc5 (l:List Γ₀):
 (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k))=
   update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:=by
 funext k; cases k <;> simp [st5]
lemma qed (u:List Γ₁):
 (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k))=
   update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:=by
 funext k; cases k <;> simp [st5]
abbrev v9 (Γ₀ Γ₁:Type):Type:=TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂:Γ₀→Option Γ₁) (d:Option Γ₁)
lemma qdx (s:Option Γ₀) (x:Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
 (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .a,s,st5 (x::l) a b c u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .a,some x,st5 l (some x::a) b c u⟩:=by
 simp [TM2.step,zC,TM2.stepAux,st5,wN,uO]
lemma qee (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .b,none,st5 [] a b c u⟩:=by
 simp [TM2.step,zC,TM2.stepAux,st5,wN]
lemma qdy (hd:d=none→∀ x,φ₂ x=none) (s:Option Γ₀) (x:Γ₀)
 (a b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x::a) b c u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .b,some x,st5 [] a (some x::b) c ((φ₂ x).toList++u)⟩:=by
 cases hφ:φ₂ x with
 | none=>
   cases d <;>
    simp [TM2.step,zC,uS,TM2.stepAux,st5,uO,uP,hφ]
 | some y=>
   cases d with
   | none=>rw [hd rfl x] at hφ; exact absurd hφ (by simp)
   | some dd=>simp [TM2.step,zC,uS,TM2.stepAux,st5,uO,uP,wO,hφ]
lemma qef (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .c,none,st5 [] [] b c u⟩:=by
 simp [TM2.step,zC,TM2.stepAux,st5,uO]
lemma qdz (s:Option Γ₀) (x:Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x::b) c u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .c,some x,st5 [] [] b (some x::c) u⟩:=by
 simp [TM2.step,zC,TM2.stepAux,st5,uP,uQ]
lemma qeg (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .e,none,st5 [] [] [] c u⟩:=by
 simp [TM2.step,zC,TM2.stepAux,st5,uP]
lemma qdA (hd:d=none→∀ x,φ₁ x=none) (s:Option Γ₀) (x:Γ₀)
 (c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x::c) u⟩:v9 Γ₀ Γ₁)=
  some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList++u)⟩:=by
 cases hφ:φ₁ x with
 | none=>
   cases d <;>
    simp [TM2.step,zC,uS,TM2.stepAux,st5,uQ,hφ]
 | some y=>
   cases d with
   | none=>rw [hd rfl x] at hφ; exact absurd hφ (by simp)
   | some dd=>simp [TM2.step,zC,uS,TM2.stepAux,st5,uQ,wO,hφ]
lemma qeh (s:Option Γ₀) (u:List Γ₁):
 TM2.step (zC φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:v9 Γ₀ Γ₁)=
  some ⟨none,none,st5 [] [] [] [] u⟩:=by
 simp [TM2.step,zC,TM2.stepAux,st5,uQ]
lemma qei (b c:List (Option Γ₀)) (u:List Γ₁):
 ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
   (flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1]
     (some (⟨some .a,s,st5 l a b c u⟩:v9 Γ₀ Γ₁))=
     some ⟨some .b,none,st5 [] (l.reverse.map some++a) b c u⟩:=by
 intro l;induction l with
 | nil=>intro a s; exact qee φ₁ φ₂ d s a b c u
 | cons x l ih=>
   intro a s;rw [qI,ze]
   have e:flip bind (TM2.step (zC φ₁ φ₂ d))
    (some (⟨some .a,s,st5 (x::l) a b c u⟩:v9 Γ₀ Γ₁))=
    some ⟨some .a,some x,st5 l (some x::a) b c u⟩:=qdx φ₁ φ₂ d s x l a b c u
   rw [e,ih];simp
lemma qej (hd:d=none→∀ x,φ₂ x=none) (c:List (Option Γ₀)):
 ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
   (flip bind (TM2.step (zC φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:v9 Γ₀ Γ₁))=
     some ⟨some .c,none,
      st5 [] [] (t.reverse.map some++b) c ((t.filterMap φ₂).reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro b u s; exact qef φ₁ φ₂ d s b c u
 | cons x t ih=>
   intro b u s;rw [qI,ze]
   have e:flip bind (TM2.step (zC φ₁ φ₂ d))
    (some (⟨some .b,s,st5 [] ((x::t).map some) b c u⟩:v9 Γ₀ Γ₁))=
    some ⟨some .b,some x,st5 [] (t.map some) (some x::b) c ((φ₂ x).toList++u)⟩:=
    qdy φ₁ φ₂ d hd s x (t.map some) b c u
   rw [e,ih]
   cases hφ:φ₂ x <;> simp [hφ]
lemma qek (u:List Γ₁):
 ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
   (flip bind (TM2.step (zC φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:v9 Γ₀ Γ₁))=
     some ⟨some .e,none,st5 [] [] [] (t.reverse.map some++c) u⟩:=by
 intro t;induction t with
 | nil=>intro c s; exact qeg φ₁ φ₂ d s c u
 | cons x t ih=>
   intro c s;rw [qI,ze]
   have e:flip bind (TM2.step (zC φ₁ φ₂ d))
    (some (⟨some .c,s,st5 [] [] ((x::t).map some) c u⟩:v9 Γ₀ Γ₁))=
    some ⟨some .c,some x,st5 [] [] (t.map some) (some x::c) u⟩:=
    qdz φ₁ φ₂ d s x (t.map some) c u
   rw [e,ih];simp
lemma qel (hd:d=none→∀ x,φ₁ x=none):
 ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
   (flip bind (TM2.step (zC φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:v9 Γ₀ Γ₁))=
     some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse++u)⟩:=by
 intro t;induction t with
 | nil=>intro u s; exact qeh φ₁ φ₂ d s u
 | cons x t ih=>
   intro u s;rw [qI,ze]
   have e:flip bind (TM2.step (zC φ₁ φ₂ d))
    (some (⟨some .e,s,st5 [] [] [] ((x::t).map some) u⟩:v9 Γ₀ Γ₁))=
    some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList++u)⟩:=
    qdA φ₁ φ₂ d hd s x (t.map some) u
   rw [e,ih]
   cases hφ:φ₁ x <;> simp [hφ]
lemma qeV [Fintype Γ₀] (hd₁:d=none→∀ x,φ₁ x=none)
 (hd₂:d=none→∀ x,φ₂ x=none) (l:List Γ₀):
 (flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1)+(l.length+1)]
   (some (initList (tp φ₁ φ₂ d) l))=
   some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1 +
  (l.length+1)+(l.length+1)+(l.length+1)]
  (some c)) (zH (tp φ₁ φ₂ d) l)).trans
  (Eq.trans ?_ (congrArg some (zG (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂))).symm)
 show (flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1)+(l.length+1)]
  (some (⟨some .a,none,update (fun _=>[]) .inp l⟩:v9 Γ₀ Γ₁))=
  some (⟨none,none,update (fun _=>[]) .out
   (l.filterMap φ₁++l.filterMap φ₂)⟩:v9 Γ₀ Γ₁)
 have hA:(flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .a,none,st5 l [] [] [] []⟩:v9 Γ₀ Γ₁))=
  some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:=by
  simpa using qei φ₁ φ₂ d [] [] [] l [] none
 have hB:(flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:v9 Γ₀ Γ₁))=
  some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:=by
  have:=qej φ₁ φ₂ d hd₂ [] l.reverse [] [] none;rw [vJ] at this;simpa [List.filterMap_reverse] using this
 have hC:(flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:v9 Γ₀ Γ₁))=
  some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:=by
  simpa using qek φ₁ φ₂ d (l.filterMap φ₂) l [] none
 have hE:(flip bind (TM2.step (zC φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:v9 Γ₀ Γ₁))=
  some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁++l.filterMap φ₂)⟩:=by
  have:=qel φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none;rw [vJ] at this;simpa [List.filterMap_reverse] using this
 rw [iterate_add_apply,iterate_add_apply,iterate_add_apply,← qc5,hA,hB,hC,hE,qed]
lemma kg {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (φ₁ φ₂:αΓ→Option βΓ)
 (h:∀ a,eb (f a)=(ea a).filterMap φ₁++(ea a).filterMap φ₂):
 Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
 classical
 let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
 have hd:∀ φ:αΓ→Option βΓ,d=none→∀ x,φ x=none:=by
  intro φ hdn x;by_cases hn:Nonempty βΓ
  · simp [d,hn] at hdn
  · cases hφ:φ x with
    | none=>rfl
    | some y=>exact absurd ⟨y⟩ hn
 exact ⟨{
  tm:=tp φ₁ φ₂ d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 4 * Polynomial.X+Polynomial.C 4
  outputsFun:=fun a=>
   { steps:=(ea a).length+1+((ea a).length+1)+((ea a).length+1) +
      ((ea a).length+1)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      have:=qeV φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
      exact (congrArg (fun l=>(flip bind (TM2.step (zC φ₁ φ₂ d)))^[(ea a).length+1 +
       ((ea a).length+1)+((ea a).length+1)+((ea a).length+1)]
       (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
       (this.trans (congrArg (fun l=>some (haltList (tp φ₁ φ₂ d) l))
         ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
     steps_le_m:=by simp only [zO,z9,vT,Polynomial.eval_X];omega } }⟩
end Lib.qC
end
section
namespace Lib.qC
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
abbrev ji:M.K ⊕ FX→Type
 | inl k=>M.Γ k
 | inr FX.I=>Bool ⊕ Bool
 | inr FX.W=>Bool
 | inr FX.T=>Bool
 | inr FX.O=>Bool ⊕ Bool
abbrev qa2:Type:=M.Λ ⊕ FL
abbrev qa3:Type:=M.σ×Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool)→Bool
 | none=>false
 | some (inl b)=>b
 | some (inr b)=>b
def wv:Option (Bool ⊕ Bool)→Bool
 | some (inl _)=>true
 | _=>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ→TM2.Stmt (ji M) (qa2 M) (qa3 M)
 | .push k f q=>.push (inl k) (fun s=>f s.1) (trF q)
 | .peek k f q=>.peek (inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
 | .pop k f q=>.pop (inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (trF q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trF q₁) (trF q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr FL.l3)
variable (M)
def qB (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool):
    qa2 M→TM2.Stmt (ji M) (qa2 M) (qa3 M)
 | inl l=>trF (M.m l)
 | inr FL.l1=>
   .pop (inr FX.I) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.branch (fun s=>wv s.2)
         (.push (inr FX.T) (fun s=>bit s.2) (.goto fun _=>inr FL.l1))
         (.push (inr FX.W) (fun s=>bit s.2) (.goto fun _=>inr FL.l1)))
       (.goto fun _=>inr FL.l2))
 | inr FL.l2=>
   .pop (inr FX.T) (fun s o=>(s.1,o.map inl))
     (.branch (fun s=>s.2.isSome)
       (.push (inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>inr FL.l2))
       (.goto fun _=>inl M.main))
 | inr FL.l3=>
   .pop (inr FX.W) (fun s o=>(s.1,o.map inl))
     (.branch (fun s=>s.2.isSome)
       (.push (inr FX.O) (fun s=>inr (bit s.2)) (.goto fun _=>inr FL.l3))
       (.goto fun _=>inr FL.l4))
 | inr FL.l4=>
   .pop (inl M.k₁) (fun s o=>(s.1,o.map fun y=>inl (e₁ y)))
     (.branch (fun s=>s.2.isSome)
       (.push (inr FX.T) (fun s=>bit s.2) (.goto fun _=>inr FL.l4))
       (.goto fun _=>inr FL.l5))
 | inr FL.l5=>
   .pop (inr FX.T) (fun s o=>(s.1,o.map inl))
     (.branch (fun s=>s.2.isSome)
       (.push (inr FX.O) (fun s=>inl (bit s.2)) (.goto fun _=>inr FL.l5))
       .halt)
def kv (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool):FinTM2:=haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ FX
   k₀:=inr FX.I
   k₁:=inr FX.O
   Γ:=ji M
   Λ:=qa2 M
   main:=inr FL.l1
   σ:=qa3 M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
   m:=qB M e₀ e₁ }
variable {M}
def qW (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:Q0)
    (o:List (Bool ⊕ Bool)):∀ k,List (ji M k)
 | inl k=>S k
 | inr FX.I=>i
 | inr FX.W=>w
 | inr FX.T=>t
 | inr FX.O=>o
section qW
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:Q0)
 (o:List (Bool ⊕ Bool))
lemma k7 (k:M.K) (x:List (M.Γ k)):
 update (qW S i w t o) (inl k) x=qW (update S k x) i w t o:=by
 funext j
 rcases j with j|j
 · by_cases h:j=k
   · subst h;rw [update_self];show x=update S j x j;rw [update_self]
   · rw [update_of_ne (by simpa using h)];show S j=update S k x j;rw [update_of_ne h]
 · rw [update_of_ne (by simp)]; cases j <;> rfl
lemma uF (i':List (Bool ⊕ Bool)):
 update (qW S i w t o) (inr FX.I) i'=qW S i' w t o:=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma jM (w':Q0):
 update (qW S i w t o) (inr FX.W) w'=qW S i w' t o:=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma kC (t':Q0):
 update (qW S i w t o) (inr FX.T) t'=qW S i w t' o:=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma jL (o':List (Bool ⊕ Bool)):
 update (qW S i w t o) (inr FX.O) o'=qW S i w t o':=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
end qW
abbrev va (M:FinTM2):Type:=TM2.Cfg (ji M) (qa2 M) (qa3 M)
def wW (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:Q0)
    (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):va M:=
 ⟨some (c.l.elim (inr FL.l3) inl),(c.var,b),qW c.stk i w t o⟩
lemma qfm (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:Q0)
 (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)):
 TM2.stepAux (trF q) ((v,b):qa3 M) (qW S i w t o)=
  wW b i w t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>have:=ih v (update S k (f v::S k));rw [← k7] at this;exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>have:=ih (f v (S k).head?) (update S k (S k).tail);rw [← k7] at this;exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [trF,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
lemma qfg (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool) (b:Option (Bool ⊕ Bool))
 (i:List (Bool ⊕ Bool)) (w t:Q0) (o:List (Bool ⊕ Bool))
 (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c'):
 TM2.step (qB M e₀ e₁) (wW b i w t o c)=some (wW b i w t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>simp only [TM2.step,Option.some.injEq] at h;subst h;exact congrArg some (qfm b i w t o (M.m l) v S)
end Lib.qC
end
section
namespace Lib.qC
open Turing
lemma zy {σ:Type} (f:σ→Option σ) {a b:ℕ} {x y z:σ}
 (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z):
 (flip bind f)^[b+a] (some x)=some z:=by
 rw [iterate_add_apply,h₁,h₂]
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
section qW
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:Q0)
 (o:List (Bool ⊕ Bool))
@[simp] theorem qfw (k:M.K):qW S i w t o (inl k)=S k:=rfl
@[simp] theorem qfv:qW S i w t o (inr FX.I)=i:=rfl
@[simp] theorem qfz:qW S i w t o (inr FX.W)=w:=rfl
@[simp] theorem qfy:qW S i w t o (inr FX.T)=t:=rfl
@[simp] theorem qfx:qW S i w t o (inr FX.O)=o:=rfl
end qW
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:Q0) (o:List (Bool ⊕ Bool))
lemma qeD (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l1),(v,b),qW S (inl a::i) w t o⟩:va M)=
  some ⟨some (inr FL.l1),(v,some (inl a)),qW S i w (a::t) o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,uF,kC,wv,bit]
lemma qeE (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l1),(v,b),qW S (inr a::i) w t o⟩:va M)=
  some ⟨some (inr FL.l1),(v,some (inr a)),qW S i (a::w) t o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,uF,jM,wv,bit]
lemma qeF (b:Option (Bool ⊕ Bool)) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l1),(v,b),qW S [] w t o⟩:va M)=
  some ⟨some (inr FL.l2),(v,none),qW S [] w t o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,uF]
lemma qe2:∀ (i:List (Bool ⊕ Bool)) (w t:Q0) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (qB M e₀ e₁)))^[i.length+1]
   (some (⟨some (inr FL.l1),(v,b),qW S i w t o⟩:va M))=
   some ⟨some (inr FL.l2),(v,none),qW S [] ((i.filterMap Sum.getRight?).reverse++w)
    ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i;induction i with
 | nil=>intro w t b; exact qeF e₀ e₁ v S w o b t
 | cons x i ih=>
   intro w t b;rw [qI,ze]
   cases x with
   | inl a=>
     have e:flip bind (TM2.step (qB M e₀ e₁))
      (some (⟨some (inr FL.l1),(v,b),qW S (inl a::i) w t o⟩:va M))=
      some ⟨some (inr FL.l1),(v,some (inl a)),qW S i w (a::t) o⟩:=
      qeD e₀ e₁ v S w o b a i t
     rw [e,ih]; simp [List.filterMap_cons]
   | inr a=>
     have e:flip bind (TM2.step (qB M e₀ e₁))
      (some (⟨some (inr FL.l1),(v,b),qW S (inr a::i) w t o⟩:va M))=
      some ⟨some (inr FL.l1),(v,some (inr a)),qW S i (a::w) t o⟩:=
      qeE e₀ e₁ v S w o b a i t
     rw [e,ih]; simp [List.filterMap_cons]
lemma qdW (b:Option (Bool ⊕ Bool)) (a:Bool) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l2),(v,b),qW S [] w (a::t) o⟩:va M)=
  some ⟨some (inr FL.l2),(v,some (inl a)),
   qW (update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,kC,k7,bit]
lemma qeG (b:Option (Bool ⊕ Bool)):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l2),(v,b),qW S [] w [] o⟩:va M)=
  some ⟨some (inl M.main),(v,none),qW S [] w [] o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,kC]
lemma qe3:∀ (t:Q0) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (qB M e₀ e₁)))^[t.length+1]
   (some (⟨some (inr FL.l2),(v,b),qW S [] w t o⟩:va M))=
   some ⟨some (inl M.main),(v,none),
    qW (update S M.k₀ (t.reverse.map e₀++S M.k₀)) [] w [] o⟩:=by
 intro t;induction t with
 | nil=>
   intro S b;have:update S M.k₀ (([]:Q0).reverse.map e₀++S M.k₀)=S:=by simp
   rw [this];exact qeG e₀ e₁ v S w o b
 | cons a t ih=>
   intro S b;rw [qI,ze]
   have e:flip bind (TM2.step (qB M e₀ e₁))
    (some (⟨some (inr FL.l2),(v,b),qW S [] w (a::t) o⟩:va M))=
    some ⟨some (inr FL.l2),(v,some (inl a)),qW (update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=qdW e₀ e₁ v S w o b a t
   rw [e,ih]; simp
lemma qdX (b:Option (Bool ⊕ Bool)) (a:Bool) (w:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l3),(v,b),qW S [] (a::w) [] o⟩:va M)=
  some ⟨some (inr FL.l3),(v,some (inl a)),qW S [] w [] (inr a::o)⟩:=by
 simp [TM2.step,qB,TM2.stepAux,jM,jL,bit]
lemma qeH (b:Option (Bool ⊕ Bool)):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l3),(v,b),qW S [] [] [] o⟩:va M)=
  some ⟨some (inr FL.l4),(v,none),qW S [] [] [] o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,jM]
lemma qe4:∀ (w:Q0) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (qB M e₀ e₁)))^[w.length+1]
   (some (⟨some (inr FL.l3),(v,b),qW S [] w [] o⟩:va M))=
   some ⟨some (inr FL.l4),(v,none),qW S [] [] [] (w.reverse.map inr++o)⟩:=by
 intro w;induction w with
 | nil=>intro o b; exact qeH e₀ e₁ v S o b
 | cons a w ih=>
   intro o b;rw [qI,ze]
   have e:flip bind (TM2.step (qB M e₀ e₁))
    (some (⟨some (inr FL.l3),(v,b),qW S [] (a::w) [] o⟩:va M))=
    some ⟨some (inr FL.l3),(v,some (inl a)),qW S [] w [] (inr a::o)⟩:=
    qdX e₀ e₁ v S o b a w
   rw [e,ih]; simp
lemma qdY (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l4),(v,b),qW (update S M.k₁ (y::m)) [] [] t o⟩:va M)=
  some ⟨some (inr FL.l4),(v,some (inl (e₁ y))),
   qW (update S M.k₁ m) [] [] (e₁ y::t) o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,kC,k7,bit]
lemma qeI (b:Option (Bool ⊕ Bool)) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l4),(v,b),qW (update S M.k₁ []) [] [] t o⟩:va M)=
  some ⟨some (inr FL.l5),(v,none),qW (update S M.k₁ []) [] [] t o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,k7]
lemma qe5:∀ (m:List (M.Γ M.k₁)) (t:Q0) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (qB M e₀ e₁)))^[m.length+1]
   (some (⟨some (inr FL.l4),(v,b),qW (update S M.k₁ m) [] [] t o⟩:va M))=
   some ⟨some (inr FL.l5),(v,none),
    qW (update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
 intro m;induction m with
 | nil=>intro t b; exact qeI e₀ e₁ v S o b t
 | cons y m ih=>
   intro t b;rw [qI,ze]
   have e:flip bind (TM2.step (qB M e₀ e₁))
    (some (⟨some (inr FL.l4),(v,b),qW (update S M.k₁ (y::m)) [] [] t o⟩:va M))=
    some ⟨some (inr FL.l4),(v,some (inl (e₁ y))),qW (update S M.k₁ m) [] [] (e₁ y::t) o⟩:=qdY e₀ e₁ v S o b y m t
   rw [e,ih]; simp
lemma qdZ (b:Option (Bool ⊕ Bool)) (a:Bool) (t:Q0):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l5),(v,b),qW S [] [] (a::t) o⟩:va M)=
  some ⟨some (inr FL.l5),(v,some (inl a)),qW S [] [] t (inl a::o)⟩:=by
 simp [TM2.step,qB,TM2.stepAux,kC,jL,bit]
lemma qeJ (b:Option (Bool ⊕ Bool)):
 TM2.step (qB M e₀ e₁)
  (⟨some (inr FL.l5),(v,b),qW S [] [] [] o⟩:va M)=
  some ⟨none,(v,none),qW S [] [] [] o⟩:=by
 simp [TM2.step,qB,TM2.stepAux,kC]
lemma qe6:∀ (t:Q0) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (qB M e₀ e₁)))^[t.length+1]
   (some (⟨some (inr FL.l5),(v,b),qW S [] [] t o⟩:va M))=
   some ⟨none,(v,none),qW S [] [] [] (t.reverse.map inl++o)⟩:=by
 intro t;induction t with
 | nil=>intro o b; exact qeJ e₀ e₁ v S o b
 | cons a t ih=>
   intro o b;rw [qI,ze]
   have e:flip bind (TM2.step (qB M e₀ e₁))
    (some (⟨some (inr FL.l5),(v,b),qW S [] [] (a::t) o⟩:va M))=
    some ⟨some (inr FL.l5),(v,some (inl a)),qW S [] [] t (inl a::o)⟩:=
    qdZ e₀ e₁ v S o b a t
   rw [e,ih]; simp
end Lib.qC
end
section
namespace Lib.qC
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
lemma qbi:(qW (fun _=>[]) [] [] [] []:∀ k,List (ji M k))=fun _=>[]:=by funext j; rcases j with j|(_|_|_|_) <;> rfl
lemma qcg (i:List (Bool ⊕ Bool)):
 (qW (fun _=>[]) i [] [] []:∀ k,List (ji M k))=
   update (fun _=>[]:∀ k,List (ji M k)) (inr FX.I) i:=
 (uF (fun _=>[]) [] [] [] [] i).symm.trans (by rw [qbi])
lemma qch (o:List (Bool ⊕ Bool)):
 (qW (fun _=>[]) [] [] [] o:∀ k,List (ji M k))=
   update (fun _=>[]:∀ k,List (ji M k)) (inr FX.O) o:=
 (jL (fun _=>[]) [] [] [] [] o).symm.trans (by rw [qbi])
lemma qcQ (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:Q0)
 (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)):
 wW b i w t o (initList M l)=
  (⟨some (inl M.main),(M.initialState,b),
    qW (update (fun _=>[]) M.k₀ l) i w t o⟩:va M):=by
 rw [zH]; rfl
lemma qcP (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:Q0)
 (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)):
 wW b i w t o (haltList M m)=
  (⟨some (inr FL.l3),(M.initialState,b),
    qW (update (fun _=>[]) M.k₁ m) i w t o⟩:va M):=by
 rw [zG]; rfl
lemma k5 {γ δ:Type} (l:List γ):
 l.filterMap (fun _=>(none:Option δ))=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp
lemma k4 (x w:Q0):
 (encodePair (x,w)).filterMap Sum.getLeft?=x:=by
 have h1:(Sum.getLeft? ∘ (inl:Bool→Bool ⊕ Bool):Bool→Option Bool)=some:=rfl;have h2:(Sum.getLeft? ∘ (inr:Bool→Bool ⊕ Bool):Bool→Option Bool)=fun _=>none:=rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,List.filterMap_some,k5,qX]
lemma kS (x w:Q0):
 (encodePair (x,w)).filterMap Sum.getRight?=w:=by
 have h1:(Sum.getRight? ∘ (inl:Bool→Bool ⊕ Bool):Bool→Option Bool)=fun _=>none:=rfl
 have h2:(Sum.getRight? ∘ (inr:Bool→Bool ⊕ Bool):Bool→Option Bool)=some:=rfl;simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,List.filterMap_some,k5,List.nil_append]
lemma v3 (x w:Q0):
 (encodePair (x,w)).length=x.length+w.length:=by
 simp [encodePair]
lemma qcR (x w0:Q0) (m:List (M.Γ M.k₁)) (s:ℕ)
 (h:(flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)):
 ∃ n,n≤ s+2 * x.length+2 * w0.length+2 * m.length+5∧
   (flip bind (TM2.step (qB M e₀ e₁)))^[n]
     (some (initList (kv M e₀ e₁) (encodePair (x,w0))))=
     some (haltList (kv M e₀ e₁) (encodePair (m.map e₁,w0))):=by
 have q1:(flip bind (TM2.step (qB M e₀ e₁)))^[(encodePair (x,w0)).length+1]
  (some (initList (kv M e₀ e₁) (encodePair (x,w0))))=
  some (⟨some (inr FL.l2),(M.initialState,none),
   qW (fun _=>[]) [] w0.reverse x.reverse []⟩:va M):=by
  have:=qe2 e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,w0)) [] [] none;rw [k4,kS,qX,qX,qcg] at this
  exact (congrArg (fun c=>(flip bind (TM2.step (qB M e₀ e₁)))^[
   (encodePair (x,w0)).length+1] (some c))
   (zH (kv M e₀ e₁) (encodePair (x,w0)))).trans this
 have q2:(flip bind (TM2.step (qB M e₀ e₁)))^[x.reverse.length+1]
  (some (⟨some (inr FL.l2),(M.initialState,none),
    qW (fun _=>[]) [] w0.reverse x.reverse []⟩:va M))=
  some (wW none [] w0.reverse [] [] (initList M (x.map e₀))):=by
  have:=qe3 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _=>[]) none;rw [qcQ];simpa using this
 have q3:=kV (TM2.step M.m) (TM2.step (qB M e₀ e₁))
  (wW none [] w0.reverse [] []) (qfg e₀ e₁ none [] w0.reverse [] []) s _ _ h
 rw [qcP] at q3
 have q4:(flip bind (TM2.step (qB M e₀ e₁)))^[w0.reverse.length+1]
  (some (⟨some (inr FL.l3),(M.initialState,none),
    qW (update (fun _=>[]) M.k₁ m) [] w0.reverse [] []⟩:va M))=
  some (⟨some (inr FL.l4),(M.initialState,none),
   qW (update (fun _=>[]) M.k₁ m) [] [] [] (w0.map inr)⟩:va M):=by
  have:=qe4 e₀ e₁ M.initialState (update (fun _=>[]) M.k₁ m) w0.reverse [] none;simpa using this
 have q5:(flip bind (TM2.step (qB M e₀ e₁)))^[m.length+1]
  (some (⟨some (inr FL.l4),(M.initialState,none),
    qW (update (fun _=>[]) M.k₁ m) [] [] [] (w0.map inr)⟩:va M))=
  some (⟨some (inr FL.l5),(M.initialState,none),
   qW (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map inr)⟩:va M):=by
  have:=qe5 e₀ e₁ M.initialState (fun _=>[]) (w0.map inr) m [] none;simpa using this
 have q6:(flip bind (TM2.step (qB M e₀ e₁)))^[(m.reverse.map e₁).length+1]
  (some (⟨some (inr FL.l5),(M.initialState,none),
    qW (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map inr)⟩:va M))=
  some (haltList (kv M e₀ e₁) (encodePair (m.map e₁,w0))):=by
  have:=qe6 e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (w0.map inr) none;rw [qch] at this;refine this.trans (Eq.trans ?_ (congrArg some (zG (kv M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
  simp [encodePair];rfl
 refine ⟨_,?_,zy _ (zy _ (zy _ (zy _ (zy _ q1 q2) q3) q4) q5) q6⟩
 simp only [v3,vJ,zM];omega
lemma qaq (f:Q0→Q0)
 (c:TM2ComputableInPolyTime (fun x:Q0=>x) (fun x:Q0=>x) f):
 Nonempty (TM2ComputableInPolyTime encodePair encodePair
  (fun p:Q0×Q0=>(f p.1,p.2))):=by
 let e₀:Bool→c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun;let e₁:c.tm.Γ c.tm.k₁→Bool:=c.outputAlphabet
 let T:Q5:=c.time+Polynomial.C 2 * (Polynomial.X+Polynomial.C (yh c.tm) * c.time)+Polynomial.C 2 * Polynomial.X+Polynomial.C 5
 have key:∀ p:Q0×Q0,∃ n,n≤T.eval (encodePair p).length∧
  (flip bind (TM2.step (qB c.tm e₀ e₁)))^[n]
    (some (initList (kv c.tm e₀ e₁) (encodePair p)))=
    some (haltList (kv c.tm e₀ e₁) (encodePair (f p.1,p.2))):=by
  rintro ⟨x,w⟩
  have hs:∃ s,s≤Polynomial.eval x.length c.time∧
   (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀)))=some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))):=
   ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
  obtain ⟨s,b1,h⟩:=hs;obtain ⟨n,hn,h0⟩:=qcR e₀ e₁ x w _ s h
  have hm:(List.map c.outputAlphabet.invFun (f x)).map e₁=f x:=by
   rw [List.map_map]
   conv_rhs=>rw [← List.map_id (f x)]
   exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
  rw [hm] at h0;refine ⟨n,hn.trans ?_,h0⟩
  have h':=h;rw [zG,zH] at h';have h1:=jR c.tm c.tm.k₁ s _ _ h';simp only [update_self,zM] at h1
  have hin:((update (fun _=>[]:∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
   c.tm.k₁).length≤x.length:=by
   by_cases hk:c.tm.k₁=c.tm.k₀
   · rw [hk,update_self,zM]
   · rw [update_of_ne hk]; simp
  have b2:Polynomial.eval x.length c.time≤Polynomial.eval (x.length+w.length) c.time:=y7 _ (by omega)
  have hmul:yh c.tm * s≤
   yh c.tm * Polynomial.eval (x.length+w.length) c.time:=
   Nat.mul_le_mul_left _ (b1.trans b2)
  simp only [T,zO,z9,vT,Polynomial.eval_X,v3,zM];omega
 exact ⟨{
  tm:=kv c.tm e₀ e₁
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun p=>
   { steps:=Classical.choose (key p)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      exact (congrArg (fun l=>(flip bind (TM2.step (qB c.tm e₀ e₁)))^[
       Classical.choose (key p)] (some (initList (kv c.tm e₀ e₁) l)))
       (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
       (congrArg (fun l=>some (haltList (kv c.tm e₀ e₁) l))
         (hm _ (encodePair (f p.1,p.2))).symm))
     steps_le_m:=(Classical.choose_spec (key p)).1 } }⟩
end Lib.qC
end
section
namespace Lib.qC.jE
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
abbrev ItΓ:M.K ⊕ IX→Type
 | inl k=>M.Γ k
 | inr IX.I=>Bool ⊕ Bool
 | inr IX.C=>Bool
 | inr IX.T=>Bool
 | inr IX.O=>Bool
abbrev ItΛ:Type:=M.Λ ⊕ IL
abbrev Itσ:Type:=M.σ×Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ→TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | .push k f q=>.push (inl k) (fun s=>f s.1) (trI q)
 | .peek k f q=>.peek (inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
 | .pop k f q=>.pop (inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (trI q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trI q₁) (trI q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr IL.l4)
variable (M)
def qt (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool):
    ItΛ M→TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | inl l=>trI (M.m l)
 | inr IL.l1=>
   .pop (inr IX.I) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.branch (fun s=>wv s.2)
         (.push (inr IX.T) (fun s=>bit s.2) (.goto fun _=>inr IL.l1))
         (.push (inr IX.C) (fun s=>bit s.2) (.goto fun _=>inr IL.l1)))
       (.goto fun _=>inr IL.l2))
 | inr IL.l2=>
   .pop (inr IX.T) (fun s o=>(s.1,o.map inl))
     (.branch (fun s=>s.2.isSome)
       (.push (inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>inr IL.l2))
       (.goto fun _=>inr IL.l3))
 | inr IL.l3=>
   .pop (inr IX.C) (fun s o=>(s.1,o.map inl))
     (.branch (fun s=>s.2.isSome)
       (.goto fun _=>inl M.main)
       (.goto fun _=>inr IL.l5))
 | inr IL.l4=>
   .pop (inl M.k₁) (fun s o=>(s.1,o.map fun y=>inl (e₁ y)))
     (.branch (fun s=>s.2.isSome)
       (.push (inr IX.T) (fun s=>bit s.2) (.goto fun _=>inr IL.l4))
       (.goto fun _=>inr IL.l2))
 | inr IL.l5=>
   .pop (inl M.k₀) (fun s o=>(s.1,o.map fun y=>inl (d₀ y)))
     (.branch (fun s=>s.2.isSome)
       (.push (inr IX.T) (fun s=>bit s.2) (.goto fun _=>inr IL.l5))
       (.goto fun _=>inr IL.l6))
 | inr IL.l6=>
   .pop (inr IX.T) (fun s o=>(s.1,o.map inl))
     (.branch (fun s=>s.2.isSome)
       (.push (inr IX.O) (fun s=>bit s.2) (.goto fun _=>inr IL.l6))
       .halt)
def ya (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool):FinTM2:=haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ IX
   k₀:=inr IX.I
   k₁:=inr IX.O
   Γ:=ItΓ M
   Λ:=ItΛ M
   main:=inr IL.l1
   σ:=Itσ M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
   m:=qt M e₀ d₀ e₁ }
variable {M}
def qP (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:Q0):
    ∀ k,List (ItΓ M k)
 | inl k=>S k
 | inr IX.I=>i
 | inr IX.C=>cn
 | inr IX.T=>t
 | inr IX.O=>o
section qP
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:Q0)
@[simp] theorem qfC (k:M.K):qP S i cn t o (inl k)=S k:=rfl
@[simp] theorem qfB:qP S i cn t o (inr IX.I)=i:=rfl
@[simp] theorem qfA:qP S i cn t o (inr IX.C)=cn:=rfl
@[simp] theorem qfE:qP S i cn t o (inr IX.T)=t:=rfl
@[simp] theorem qfD:qP S i cn t o (inr IX.O)=o:=rfl
lemma kb (k:M.K) (x:List (M.Γ k)):
 update (qP S i cn t o) (inl k) x=qP (update S k x) i cn t o:=by
 funext j
 rcases j with j|j
 · by_cases h:j=k
   · subst h;rw [update_self];show x=update S j x j;rw [update_self]
   · rw [update_of_ne (by simpa using h)];show S j=update S k x j;rw [update_of_ne h]
 · rw [update_of_ne (by simp)]; cases j <;> rfl
lemma uH (i':List (Bool ⊕ Bool)):
 update (qP S i cn t o) (inr IX.I) i'=qP S i' cn t o:=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma jN (cn':Q0):
 update (qP S i cn t o) (inr IX.C) cn'=qP S i cn' t o:=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma kc (t':Q0):
 update (qP S i cn t o) (inr IX.T) t'=qP S i cn t' o:=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma w9 (o':Q0):
 update (qP S i cn t o) (inr IX.O) o'=qP S i cn t o':=by
 funext j
 rcases j with j|(_|_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
end qP
abbrev vt (M:FinTM2):Type:=TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def jI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0)
    (c:TM2.Cfg M.Γ M.Λ M.σ):vt M:=
 ⟨some (c.l.elim (inr IL.l4) inl),(c.var,b),qP c.stk i cn t o⟩
lemma qfn (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0)
 (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)):
 TM2.stepAux (trI q) ((v,b):Itσ M) (qP S i cn t o)=
  jI b i cn t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>have:=ih v (update S k (f v::S k));rw [← kb] at this;exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>have:=ih (f v (S k).head?) (update S k (S k).tail);rw [← kb] at this;exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [trI,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
lemma qdI (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool)
 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0)
 (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c'):
 TM2.step (qt M e₀ d₀ e₁) (jI b i cn t o c)=some (jI b i cn t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>simp only [TM2.step,Option.some.injEq] at h;subst h;exact congrArg some (qfn b i cn t o (M.m l) v S)
lemma qaD (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0)
 (l:List (M.Γ M.k₀)):
 jI b i cn t o (initList M l)=
  (⟨some (inl M.main),(M.initialState,b),
    qP (update (fun _=>[]) M.k₀ l) i cn t o⟩:vt M):=by
 rw [zH]; rfl
lemma qaC (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0)
 (m:List (M.Γ M.k₁)):
 jI b i cn t o (haltList M m)=
  (⟨some (inr IL.l4),(M.initialState,b),
    qP (update (fun _=>[]) M.k₁ m) i cn t o⟩:vt M):=by
 rw [zG]; rfl
lemma qbk:(qP (fun _=>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _=>[]:=by funext j; rcases j with j|(_|_|_|_) <;> rfl
lemma w7 (i:List (Bool ⊕ Bool)):
 (qP (fun _=>[]) i [] [] []:∀ k,List (ItΓ M k))=
   update (fun _=>[]:∀ k,List (ItΓ M k)) (inr IX.I) i:=
 (uH (fun _=>[]) [] [] [] [] i).symm.trans (by rw [qbk])
lemma w8 (o:Q0):
 (qP (fun _=>[]) [] [] [] o:∀ k,List (ItΓ M k))=
   update (fun _=>[]:∀ k,List (ItΓ M k)) (inr IX.O) o:=
 (w9 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [qbk])
end Lib.qC.jE
end
section
namespace Lib.qC.jE
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
lemma qeL (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l1),(v,b),qP S (inl a::i) cn t o⟩:vt M)=
  some ⟨some (inr IL.l1),(v,some (inl a)),qP S i cn (a::t) o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,uH,kc,wv,bit]
lemma qeM (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l1),(v,b),qP S (inr a::i) cn t o⟩:vt M)=
  some ⟨some (inr IL.l1),(v,some (inr a)),qP S i (a::cn) t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,uH,jN,wv,bit]
lemma qeN (b:Option (Bool ⊕ Bool)) (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l1),(v,b),qP S [] cn t o⟩:vt M)=
  some ⟨some (inr IL.l2),(v,none),qP S [] cn t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,uH]
lemma qcT (o:Q0):
 ∀ (i:List (Bool ⊕ Bool)) (cn t:Q0) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[i.length+1]
    (some (⟨some (inr IL.l1),(v,b),qP S i cn t o⟩:vt M))=
   some ⟨some (inr IL.l2),(v,none),qP S [] ((i.filterMap Sum.getRight?).reverse++cn)
    ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i;induction i with
 | nil=>intro cn t b; exact qeN e₀ d₀ e₁ v S b cn t o
 | cons x i ih=>
   intro cn t b;rw [qI,ze]
   cases x with
   | inl a=>
     have e:(flip bind (TM2.step (qt M e₀ d₀ e₁)))
      (some (⟨some (inr IL.l1),(v,b),qP S (inl a::i) cn t o⟩:vt M))=
      some ⟨some (inr IL.l1),(v,some (inl a)),qP S i cn (a::t) o⟩:=
      qeL e₀ d₀ e₁ v S b a i cn t o
     rw [e,ih]; simp [List.filterMap_cons]
   | inr a=>
     have e:(flip bind (TM2.step (qt M e₀ d₀ e₁)))
      (some (⟨some (inr IL.l1),(v,b),qP S (inr a::i) cn t o⟩:vt M))=
      some ⟨some (inr IL.l1),(v,some (inr a)),qP S i (a::cn) t o⟩:=
      qeM e₀ d₀ e₁ v S b a i cn t o
     rw [e,ih]; simp [List.filterMap_cons]
lemma qd6 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l2),(v,b),qP S i cn (a::t) o⟩:vt M)=
  some ⟨some (inr IL.l2),(v,some (inl a)),
   qP (update S M.k₀ (e₀ a::S M.k₀)) i cn t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kc,kb,bit]
lemma qeO (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l2),(v,b),qP S i cn [] o⟩:vt M)=
  some ⟨some (inr IL.l3),(v,none),qP S i cn [] o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kc]
lemma w6 (i:List (Bool ⊕ Bool)) (cn o:Q0):
 ∀ (t:Q0) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[t.length+1]
    (some (⟨some (inr IL.l2),(v,b),qP S i cn t o⟩:vt M))=
   some ⟨some (inr IL.l3),(v,none),
    qP (update S M.k₀ (t.reverse.map e₀++S M.k₀)) i cn [] o⟩:=by
 intro t;induction t with
 | nil=>
   intro S b;have:update S M.k₀ (([]:Q0).reverse.map e₀++S M.k₀)=S:=by simp
   rw [this];exact qeO e₀ d₀ e₁ v S b i cn o
 | cons a t ih=>
   intro S b;rw [qI,ze]
   have e:(flip bind (TM2.step (qt M e₀ d₀ e₁)))
    (some (⟨some (inr IL.l2),(v,b),qP S i cn (a::t) o⟩:vt M))=
    some ⟨some (inr IL.l2),(v,some (inl a)),qP (update S M.k₀ (e₀ a::S M.k₀)) i cn t o⟩:=
    qd6 e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih]; simp
lemma qb7 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l3),(v,b),qP S i (a::cn) t o⟩:vt M)=
  some ⟨some (inl M.main),(v,some (inl a)),qP S i cn t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,jN]
lemma qcS (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l3),(v,b),qP S i [] t o⟩:vt M)=
  some ⟨some (inr IL.l5),(v,none),qP S i [] t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,jN]
lemma qd7 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
 (i:List (Bool ⊕ Bool)) (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l4),(v,b),qP (update S M.k₁ (y::m)) i cn t o⟩:vt M)=
  some ⟨some (inr IL.l4),(v,some (inl (e₁ y))),
   qP (update S M.k₁ m) i cn (e₁ y::t) o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kc,kb,bit]
lemma qeP (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l4),(v,b),qP (update S M.k₁ []) i cn t o⟩:vt M)=
  some ⟨some (inr IL.l2),(v,none),qP (update S M.k₁ []) i cn t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kb]
lemma qcU (i:List (Bool ⊕ Bool)) (cn o:Q0):
 ∀ (m:List (M.Γ M.k₁)) (t:Q0) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[m.length+1]
    (some (⟨some (inr IL.l4),(v,b),qP (update S M.k₁ m) i cn t o⟩:vt M))=
   some ⟨some (inr IL.l2),(v,none),
    qP (update S M.k₁ []) i cn (m.reverse.map e₁++t) o⟩:=by
 intro m;induction m with
 | nil=>intro t b; exact qeP e₀ d₀ e₁ v S b i cn t o
 | cons y m ih=>
   intro t b;rw [qI,ze]
   have e:(flip bind (TM2.step (qt M e₀ d₀ e₁)))
    (some (⟨some (inr IL.l4),(v,b),qP (update S M.k₁ (y::m)) i cn t o⟩:vt M))=
    some ⟨some (inr IL.l4),(v,some (inl (e₁ y))),qP (update S M.k₁ m) i cn (e₁ y::t) o⟩:=
    qd7 e₀ d₀ e₁ v S b y m i cn t o
   rw [e,ih]; simp
lemma qd8 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
 (i:List (Bool ⊕ Bool)) (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l5),(v,b),qP (update S M.k₀ (y::m)) i cn t o⟩:vt M)=
  some ⟨some (inr IL.l5),(v,some (inl (d₀ y))),
   qP (update S M.k₀ m) i cn (d₀ y::t) o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kc,kb,bit]
lemma qeQ (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l5),(v,b),qP (update S M.k₀ []) i cn t o⟩:vt M)=
  some ⟨some (inr IL.l6),(v,none),qP (update S M.k₀ []) i cn t o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kb]
lemma qcV (i:List (Bool ⊕ Bool)) (cn o:Q0):
 ∀ (m:List (M.Γ M.k₀)) (t:Q0) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[m.length+1]
    (some (⟨some (inr IL.l5),(v,b),qP (update S M.k₀ m) i cn t o⟩:vt M))=
   some ⟨some (inr IL.l6),(v,none),
    qP (update S M.k₀ []) i cn (m.reverse.map d₀++t) o⟩:=by
 intro m;induction m with
 | nil=>intro t b; exact qeQ e₀ d₀ e₁ v S b i cn t o
 | cons y m ih=>
   intro t b;rw [qI,ze]
   have e:(flip bind (TM2.step (qt M e₀ d₀ e₁)))
    (some (⟨some (inr IL.l5),(v,b),qP (update S M.k₀ (y::m)) i cn t o⟩:vt M))=
    some ⟨some (inr IL.l5),(v,some (inl (d₀ y))),qP (update S M.k₀ m) i cn (d₀ y::t) o⟩:=
    qd8 e₀ d₀ e₁ v S b y m i cn t o
   rw [e,ih]; simp
lemma qd9 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l6),(v,b),qP S i cn (a::t) o⟩:vt M)=
  some ⟨some (inr IL.l6),(v,some (inl a)),qP S i cn t (a::o)⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kc,w9,bit]
lemma qeR (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:Q0):
 TM2.step (qt M e₀ d₀ e₁)
  (⟨some (inr IL.l6),(v,b),qP S i cn [] o⟩:vt M)=
  some ⟨none,(v,none),qP S i cn [] o⟩:=by
 simp [TM2.step,qt,TM2.stepAux,kc]
lemma qcW (i:List (Bool ⊕ Bool)) (cn:Q0):
 ∀ (t o:Q0) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[t.length+1]
    (some (⟨some (inr IL.l6),(v,b),qP S i cn t o⟩:vt M))=
   some ⟨none,(v,none),qP S i cn [] (t.reverse++o)⟩:=by
 intro t;induction t with
 | nil=>intro o b; exact qeR e₀ d₀ e₁ v S b i cn o
 | cons a t ih=>
   intro o b;rw [qI,ze]
   have e:(flip bind (TM2.step (qt M e₀ d₀ e₁)))
    (some (⟨some (inr IL.l6),(v,b),qP S i cn (a::t) o⟩:vt M))=
    some ⟨some (inr IL.l6),(v,some (inl a)),qP S i cn t (a::o)⟩:=
    qd9 e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih]; simp
lemma kG (k:M.K):
 update (fun _=>[]:∀ k,List (M.Γ k)) k []=fun _=>[]:=
 Function.update_eq_self k (fun _=>[]:∀ k,List (M.Γ k))
lemma qcY (g:Q0→Q0) (k:ℕ) (p:Q5)
 (hk:∀ y:Q0,(g y).length≤y.length+k)
 (hd:∀ a,d₀ (e₀ a)=a)
 (hrun:∀ z:Q0,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧(flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧m.map e₁=g z):
 ∀ (cn z:Q0) (L:ℕ) (b:Option (Bool ⊕ Bool)),z.length+k * cn.length≤L→
   ∃ n,n≤cn.length * (p.eval L+2 * L+3)+2 * L+3∧
     ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[n]
        (some (⟨some (inr IL.l3),(M.initialState,b),
          qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:vt M))=
       some ⟨none,(M.initialState,none),
        qP (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
 intro cn;induction cn with
 | nil=>
   intro z L b hL
   have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
    rw [List.map_reverse,List.reverse_reverse,List.map_map]
    conv_rhs=>rw [← List.map_id z]
    exact List.map_congr_left fun a _=>hd a
   have q1:((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[1]
    (some (⟨some (inr IL.l3),(M.initialState,b),
      qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:vt M))=
    some ⟨some (inr IL.l5),(M.initialState,none),
     qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:=
    qcS e₀ d₀ e₁ M.initialState _ b [] [] []
   have q2:=qcV e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none;rw [kG,qX] at q2
   have q3:=qcW e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
    ((z.map e₀).reverse.map d₀) [] none
   rw [qX,hz] at q3;refine ⟨_,?_,zy _ (zy _ q1 q2) q3⟩
   simp only [vJ,zM,List.length_nil] at hL ⊢;omega
 | cons a cn ih=>
   intro z L b hL;obtain ⟨s,m,hs,hm,hmg⟩:=hrun z;rw [qI] at hL;have hgz:(g z).length≤z.length+k:=hk z;have hkk:k * (cn.length+1)=k * cn.length+k:=Nat.mul_succ _ _;have hml:m.length=(g z).length:=by rw [← hmg,zM]
   have q1:((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[1]
    (some (⟨some (inr IL.l3),(M.initialState,b),
      qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] (a::cn) [] []⟩:vt M))=
    some (jI (some (inl a)) [] cn [] [] (initList M (z.map e₀))):=by
    rw [qaD];exact qb7 e₀ d₀ e₁ M.initialState _ b a [] cn [] []
   have q2:=kV (TM2.step M.m) (TM2.step (qt M e₀ d₀ e₁))
    (jI (some (inl a)) [] cn [] []) (qdI e₀ d₀ e₁ (some (inl a)) [] cn [] [])
    s _ _ hm
   rw [qaC] at q2;have q3:=qcU e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (inl a));rw [kG,qX,List.map_reverse,hmg] at q3;have q4:=w6 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none;rw [qX,List.reverse_reverse] at q4;obtain ⟨n,hn,q5⟩:=ih (g z) L none (by omega);have e:g^[(a::cn).length] z=g^[cn.length] (g z):=ze g _ z;rw [e];refine ⟨_,?_,zy _ (zy _ (zy _ (zy _ q1 q2) q3) q4) q5⟩
   have hp:p.eval z.length≤p.eval L:=y7 p (by omega);rw [vJ,qI,Nat.succ_mul];generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢;omega
lemma qdn (g:Q0→Q0) (k:ℕ) (p:Q5)
 (hk:∀ y:Q0,(g y).length≤y.length+k)
 (hd:∀ a,d₀ (e₀ a)=a)
 (hrun:∀ z:Q0,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧(flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧m.map e₁=g z)
 (y u:Q0) (L:ℕ) (hL:y.length+k * u.length≤L):
 ∃ n,n≤u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5∧
   ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[n] (some (initList (ya M e₀ d₀ e₁) (encodePair (y,u))))=
     some (haltList (ya M e₀ d₀ e₁) (g^[u.length] y)):=by
 have q1:((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
  (some (initList (ya M e₀ d₀ e₁) (encodePair (y,u))))=
  some (⟨some (inr IL.l2),(M.initialState,none),
   qP (fun _=>[]) [] u.reverse y.reverse []⟩:vt M):=by
  have:=qcT e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none;rw [k4,kS,qX,qX,w7] at this
  exact (congrArg (fun c=>((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
   (zH (ya M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have q2:=w6 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none;rw [qX,List.reverse_reverse] at q2
 obtain ⟨n,hn,q3⟩:=qcY e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
  (by rw [vJ]; exact hL)
 rw [vJ] at hn q3;rw [w8] at q3
 have q3':((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[n]
  (some (⟨some (inr IL.l3),(M.initialState,none),
    qP (update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:vt M))=
  some (haltList (ya M e₀ d₀ e₁) (g^[u.length] y)):=
  q3.trans (congrArg some (zG (ya M e₀ d₀ e₁) (g^[u.length] y))).symm
 refine ⟨_,?_,zy _ (zy _ q1 q2) q3'⟩
 rw [v3,vJ];omega
lemma uB (g:Q0→Q0)
 (c:Turing.TM2ComputableInPolyTime (fun x:Q0=>x) (fun x:Q0=>x) g)
 (k:ℕ) (hk:∀ y:Q0,(g y).length≤y.length+k):
 Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:Q0=>x)
  (fun p:Q0×Q0=>g^[p.2.length] p.1)):=by
 let e₀:Bool→c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun;let d₀:c.tm.Γ c.tm.k₀→Bool:=c.inputAlphabet;let e₁:c.tm.Γ c.tm.k₁→Bool:=c.outputAlphabet;let W:Q5:=Polynomial.X+Polynomial.C k * Polynomial.X
 let T:Q5:=Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3)+Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
 have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
 have h0:∀ z:Q0,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
  s≤c.time.eval z.length∧
  (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀)))=
    some (haltList c.tm m)∧m.map e₁=g z:=by
  intro z;refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),(c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
  rw [List.map_map]
  conv_rhs=>rw [← List.map_id (g z)]
  exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
 have key:∀ q:Q0×Q0,∃ n,n≤T.eval (encodePair q).length∧
  (flip bind (TM2.step (qt c.tm e₀ d₀ e₁)))^[n]
    (some (initList (ya c.tm e₀ d₀ e₁) (encodePair q)))=
    some (haltList (ya c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
  rintro ⟨y,u⟩;have hku:k * u.length≤k * (y.length+u.length):=Nat.mul_le_mul_left _ (by omega)
  obtain ⟨n,hn,hr⟩:=qdn e₀ d₀ e₁ g k c.time hk hd h0 y u
   (y.length+u.length+k * (y.length+u.length)) (by omega)
  refine ⟨n,hn.trans ?_,hr⟩
  simp only [T,W,zO,z9,vT,Polynomial.eval_X,Polynomial.eval_comp,v3]
  have h1:u.length * (Polynomial.eval (y.length+u.length+k * (y.length+u.length))
        c.time+2 * (y.length+u.length+k * (y.length+u.length))+3)≤
   (y.length+u.length) * (Polynomial.eval (y.length+u.length+k * (y.length+u.length)) c.time+2 * (y.length+u.length+k * (y.length+u.length))+3):=
   Nat.mul_le_mul_right _ (by omega)
  generalize k * (y.length+u.length)=B at h1 ⊢;omega
 exact ⟨{
  tm:=ya c.tm e₀ d₀ e₁
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun q=>
   { steps:=Classical.choose (key q)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      exact (congrArg (fun l=>(flip bind (TM2.step (qt c.tm e₀ d₀ e₁)))^[
       Classical.choose (key q)] (some (initList (ya c.tm e₀ d₀ e₁) l)))
       (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
       (congrArg (fun l=>some (haltList (ya c.tm e₀ d₀ e₁) l))
         (hm _ (g^[q.2.length] q.1)).symm))
     steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
end Lib.qC.jE
end
section
namespace Lib.qC.jE
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool)
lemma qaU (g:Q0→Q0) (p:Q5)
 (hd:∀ a,d₀ (e₀ a)=a)
 (hrun:∀ z:Q0,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧(flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧m.map e₁=g z):
 ∀ (cn z:Q0) (L:ℕ) (b:Option (Bool ⊕ Bool)),(∀ j≤cn.length,(g^[j] z).length≤L)→
   ∃ n,n≤cn.length * (p.eval L+2 * L+3)+2 * L+3∧
     ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[n]
        (some (⟨some (inr IL.l3),(M.initialState,b),
          qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:vt M))=
       some ⟨none,(M.initialState,none),
        qP (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
 intro cn;induction cn with
 | nil=>
   intro z L b hL
   have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
    rw [List.map_reverse,List.reverse_reverse,List.map_map]
    conv_rhs=>rw [← List.map_id z]
    exact List.map_congr_left fun a _=>hd a
   have q1:((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[1]
    (some (⟨some (inr IL.l3),(M.initialState,b),
      qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:vt M))=
    some ⟨some (inr IL.l5),(M.initialState,none),
     qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:=
    qcS e₀ d₀ e₁ M.initialState _ b [] [] []
   have q2:=qcV e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none;rw [kG,qX] at q2
   have q3:=qcW e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
    ((z.map e₀).reverse.map d₀) [] none
   rw [qX,hz] at q3;refine ⟨_,?_,zy _ (zy _ q1 q2) q3⟩
   have hz0:z.length≤L:=hL 0 (Nat.zero_le _);simp only [vJ,zM,List.length_nil] at hz0 ⊢;omega
 | cons a cn ih=>
   intro z L b hL;obtain ⟨s,m,hs,hm,hmg⟩:=hrun z;rw [qI] at hL;have hz0:z.length≤L:=hL 0 (Nat.zero_le _);have hgz:(g z).length≤L:=hL 1 (by omega);have hml:m.length=(g z).length:=by rw [← hmg,zM]
   have q1:((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[1]
    (some (⟨some (inr IL.l3),(M.initialState,b),
      qP (update (fun _=>[]) M.k₀ (z.map e₀)) [] (a::cn) [] []⟩:vt M))=
    some (jI (some (inl a)) [] cn [] [] (initList M (z.map e₀))):=by
    rw [qaD];exact qb7 e₀ d₀ e₁ M.initialState _ b a [] cn [] []
   have q2:=kV (TM2.step M.m) (TM2.step (qt M e₀ d₀ e₁))
    (jI (some (inl a)) [] cn [] []) (qdI e₀ d₀ e₁ (some (inl a)) [] cn [] [])
    s _ _ hm
   rw [qaC] at q2;have q3:=qcU e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (inl a));rw [kG,qX,List.map_reverse,hmg] at q3;have q4:=w6 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none;rw [qX,List.reverse_reverse] at q4
   obtain ⟨n,hn,q5⟩:=ih (g z) L none (fun j hj=>by have:=hL (j+1) (by omega);rwa [ze] at this)
   have e:g^[(a::cn).length] z=g^[cn.length] (g z):=ze g _ z;rw [e];refine ⟨_,?_,zy _ (zy _ (zy _ (zy _ q1 q2) q3) q4) q5⟩
   have hp:p.eval z.length≤p.eval L:=y7 p (by omega);rw [vJ,qI,Nat.succ_mul];generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢;omega
lemma qbl (g:Q0→Q0) (p:Q5)
 (hd:∀ a,d₀ (e₀ a)=a)
 (hrun:∀ z:Q0,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧(flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧m.map e₁=g z)
 (y u:Q0) (L:ℕ) (hL:∀ j≤u.length,(g^[j] y).length≤L):
 ∃ n,n≤u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5∧
   ((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[n] (some (initList (ya M e₀ d₀ e₁) (encodePair (y,u))))=
     some (haltList (ya M e₀ d₀ e₁) (g^[u.length] y)):=by
 have q1:((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
  (some (initList (ya M e₀ d₀ e₁) (encodePair (y,u))))=
  some (⟨some (inr IL.l2),(M.initialState,none),
   qP (fun _=>[]) [] u.reverse y.reverse []⟩:vt M):=by
  have:=qcT e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none;rw [k4,kS,qX,qX,w7] at this
  exact (congrArg (fun c=>((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
   (zH (ya M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have q2:=w6 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none;rw [qX,List.reverse_reverse] at q2
 obtain ⟨n,hn,q3⟩:=qaU e₀ d₀ e₁ g p hd hrun u.reverse y L none
  (by rw [vJ]; exact hL)
 rw [vJ] at hn q3;rw [w8] at q3
 have q3':((flip bind (TM2.step (qt M e₀ d₀ e₁))))^[n]
  (some (⟨some (inr IL.l3),(M.initialState,none),
    qP (update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:vt M))=
  some (haltList (ya M e₀ d₀ e₁) (g^[u.length] y)):=
  q3.trans (congrArg some (zG (ya M e₀ d₀ e₁) (g^[u.length] y))).symm
 refine ⟨_,?_,zy _ (zy _ q1 q2) q3'⟩
 rw [v3,vJ];omega
lemma jn (g:Q0→Q0) (m:Q0→ℕ)
 (hm:∀ y:Q0,m (g y)≤ m y)
 (hg:∀ y:Q0,(g y).length≤y.length+m y) (y:Q0):
 ∀ j:ℕ,m (g^[j] y)≤ m y∧(g^[j] y).length≤y.length+j * m y:=by
 intro j;induction j with
 | zero=>simp
 | succ j ih=>rw [qM,Nat.succ_mul];have h1:=hm (g^[j] y);have h2:=hg (g^[j] y);obtain ⟨i1,i2⟩:=ih;generalize j * m y=A at i2 ⊢;exact ⟨by omega,by omega⟩
lemma qaV (A B L V y u:ℕ) (hLV:L≤V) (hAB:A≤B):
 A+2 * L+2 * y+u+5≤B+2 * V+3 * (y+u)+5:=by
 omega
lemma jw (g:Q0→Q0)
 (c:Turing.TM2ComputableInPolyTime (fun x:Q0=>x) (fun x:Q0=>x) g)
 (m:Q0→ℕ) (a:ℕ)
 (hm:∀ y:Q0,m (g y)≤ m y)
 (hg:∀ y:Q0,(g y).length≤y.length+m y)
 (ha:∀ y:Q0,m y≤a * y.length+a):
 Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:Q0=>x) (fun p:Q0×Q0=>g^[p.2.length] p.1)):=by
 let e₀:Bool→c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun;let d₀:c.tm.Γ c.tm.k₀→Bool:=c.inputAlphabet;let e₁:c.tm.Γ c.tm.k₁→Bool:=c.outputAlphabet
 let W:Q5:=Polynomial.X+Polynomial.X * (Polynomial.C a * Polynomial.X+Polynomial.C a)
 let T:Q5:=Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3)+Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
 have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
 have h0:∀ z:Q0,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
  s≤c.time.eval z.length∧
  (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀)))=
    some (haltList c.tm m)∧m.map e₁=g z:=by
  intro z;refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),(c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
  rw [List.map_map]
  conv_rhs=>rw [← List.map_id (g z)]
  exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
 have key:∀ q:Q0×Q0,∃ n,n≤T.eval (encodePair q).length∧
  (flip bind (TM2.step (qt c.tm e₀ d₀ e₁)))^[n]
    (some (initList (ya c.tm e₀ d₀ e₁) (encodePair q)))=
    some (haltList (ya c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
  rintro ⟨y,u⟩
  have hL:∀ j≤u.length,
   (g^[j] y).length≤y.length+u.length * (a * y.length+a):=by
   intro j hj;have h1:=(jn g m hm hg y j).2;have h2:j * m y≤u.length * (a * y.length+a):=Nat.mul_le_mul hj (ha y);omega
  obtain ⟨n,hn,hr⟩:=qbl e₀ d₀ e₁ g c.time hd h0 y u
   (y.length+u.length * (a * y.length+a)) hL
  have hLV:y.length+u.length * (a * y.length+a)≤
   (y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a):=
   Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
  have hp:=y7 c.time hLV
  have h3:u.length * (Polynomial.eval (y.length+u.length * (a * y.length+a)) c.time +
        2 * (y.length+u.length * (a * y.length+a))+3)≤
   (y.length+u.length) * (Polynomial.eval ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a)) c.time+2 * ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a))+3):=
   Nat.mul_le_mul (by omega) (by omega)
  refine ⟨n,hn.trans ?_,hr⟩
  simp only [T,W,zO,z9,vT,Polynomial.eval_X,Polynomial.eval_comp,v3];exact qaV _ _ _ _ _ _ hLV h3
 exact ⟨{
  tm:=ya c.tm e₀ d₀ e₁
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun q=>
   { steps:=Classical.choose (key q)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      exact (congrArg (fun l=>(flip bind (TM2.step (qt c.tm e₀ d₀ e₁)))^[
       Classical.choose (key q)] (some (initList (ya c.tm e₀ d₀ e₁) l)))
       (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
       (congrArg (fun l=>some (haltList (ya c.tm e₀ d₀ e₁) l))
         (hm _ (g^[q.2.length] q.1)).symm))
     steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
end Lib.qC.jE
end
section
namespace Lib.qC
open PEqualNP.Library
open Turing
inductive MulK
 | I|A|B|C|O
 deriving DecidableEq
instance:Fintype MulK:=Fintype.ofList [.I,.A,.B,.C,.O] (fun x=>by cases x <;> simp)
inductive MulL
 | split|outer|copy|back|clean
 deriving DecidableEq
instance:Fintype MulL:=Fintype.ofList [.split,.outer,.copy,.back,.clean] (fun x=>by cases x <;> simp)
abbrev qag:MulK→Type
 | .I=>Bool ⊕ Bool
 | .A=>Bool
 | .B=>Bool
 | .C=>Bool
 | .O=>Bool
def v5:MulL→TM2.Stmt qag MulL (Option Bool)
 | .split=>
   .pop .I (fun _ o=>o.map Sum.isLeft)
     (.branch (fun s=>s.isSome)
       (.branch (fun s=>s == some true)
         (.push .A (fun _=>true) (.goto fun _=>.split))
         (.push .B (fun _=>true) (.goto fun _=>.split)))
       (.goto fun _=>.outer))
 | .outer=>
   .pop .A (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.goto fun _=>.copy)
       (.goto fun _=>.clean))
 | .copy=>
   .pop .B (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push .C (fun _=>true) (.push .O (fun _=>true) (.goto fun _=>.copy)))
       (.goto fun _=>.back))
 | .back=>
   .pop .C (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push .B (fun _=>true) (.goto fun _=>.back))
       (.goto fun _=>.outer))
 | .clean=>
   .pop .B (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.goto fun _=>.clean)
       .halt)
def jP:FinTM2 where
 K:=MulK
 k₀:=.I
 k₁:=.O
 Γ:=qag
 Λ:=MulL
 main:=.split
 σ:=Option Bool
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
 m:=v5
def zh (i:List (Bool ⊕ Bool)) (a b c o:Q0):∀ k,List (qag k)
 | .I=>i
 | .A=>a
 | .B=>b
 | .C=>c
 | .O=>o
@[simp] theorem qfI (i:List (Bool ⊕ Bool)) (a b c o:Q0):
   zh i a b c o .I=i:=rfl
@[simp] theorem qfF (i:List (Bool ⊕ Bool)) (a b c o:Q0):
   zh i a b c o .A=a:=rfl
@[simp] theorem qfG (i:List (Bool ⊕ Bool)) (a b c o:Q0):
   zh i a b c o .B=b:=rfl
@[simp] theorem qfH (i:List (Bool ⊕ Bool)) (a b c o:Q0):
   zh i a b c o .C=c:=rfl
@[simp] theorem qfJ (i:List (Bool ⊕ Bool)) (a b c o:Q0):
   zh i a b c o .O=o:=rfl
@[simp] theorem qfc (i i':List (Bool ⊕ Bool)) (a b c o:Q0):
   update (zh i a b c o) .I i'=zh i' a b c o:=by
  funext k; cases k <;> simp [zh]
@[simp] theorem qe9 (i:List (Bool ⊕ Bool)) (a a' b c o:Q0):
   update (zh i a b c o) .A a'=zh i a' b c o:=by
  funext k; cases k <;> simp [zh]
@[simp] theorem qfa (i:List (Bool ⊕ Bool)) (a b b' c o:Q0):
   update (zh i a b c o) .B b'=zh i a b' c o:=by
  funext k; cases k <;> simp [zh]
@[simp] theorem qfb (i:List (Bool ⊕ Bool)) (a b c c' o:Q0):
   update (zh i a b c o) .C c'=zh i a b c' o:=by
  funext k; cases k <;> simp [zh]
@[simp] theorem qfd (i:List (Bool ⊕ Bool)) (a b c o o':Q0):
   update (zh i a b c o) .O o'=zh i a b c o':=by
  funext k; cases k <;> simp [zh]
lemma qcm (i:List (Bool ⊕ Bool)):
 zh i [] [] [] []=update (fun _=>[]:∀ k,List (qag k)) .I i:=by
 funext k; cases k <;> simp [zh]
lemma qds (o:Q0):
 zh [] [] [] [] o=update (fun _=>[]:∀ k,List (qag k)) .O o:=by
 funext k; cases k <;> simp [zh]
abbrev MulCfg:Type:=TM2.Cfg qag MulL (Option Bool)
abbrev zf:Option MulCfg→Option MulCfg:=flip bind (TM2.step v5)
lemma qc2 (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:Q0):
 zf (some ⟨some .split,s,zh (inl y::i) a b c o⟩)=
  some ⟨some .split,some true,zh i (true::a) b c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qc3 (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:Q0):
 zf (some ⟨some .split,s,zh (inr y::i) a b c o⟩)=
  some ⟨some .split,some false,zh i a (true::b) c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qc4 (s:Option Bool) (a b c o:Q0):
 zf (some ⟨some .split,s,zh [] a b c o⟩)=
  some ⟨some .outer,none,zh [] a b c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qcp (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:Q0):
 zf (some ⟨some .outer,s,zh i (y::a) b c o⟩)=
  some ⟨some .copy,some y,zh i a b c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qc1 (s:Option Bool) (i:List (Bool ⊕ Bool)) (b c o:Q0):
 zf (some ⟨some .outer,s,zh i [] b c o⟩)=
  some ⟨some .clean,none,zh i [] b c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qcE (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:Q0):
 zf (some ⟨some .copy,s,zh i a (y::b) c o⟩)=
  some ⟨some .copy,some y,zh i a b (true::c) (true::o)⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qdh (s:Option Bool) (i:List (Bool ⊕ Bool)) (a c o:Q0):
 zf (some ⟨some .copy,s,zh i a [] c o⟩)=
  some ⟨some .back,none,zh i a [] c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qcB (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:Q0):
 zf (some ⟨some .back,s,zh i a b (y::c) o⟩)=
  some ⟨some .back,some y,zh i a (true::b) c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qdf (s:Option Bool) (i:List (Bool ⊕ Bool)) (a b o:Q0):
 zf (some ⟨some .back,s,zh i a b [] o⟩)=
  some ⟨some .outer,none,zh i a b [] o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qca (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:Q0):
 zf (some ⟨some .clean,s,zh i a (y::b) c o⟩)=
  some ⟨some .clean,some y,zh i a b c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
lemma qcD (s:Option Bool) (i:List (Bool ⊕ Bool)) (a c o:Q0):
 zf (some ⟨some .clean,s,zh i a [] c o⟩)=
  some ⟨none,none,zh i a [] c o⟩:=by
 simp [zf,flip,TM2.step,v5,TM2.stepAux]
abbrev rep (n:ℕ):Q0:=List.replicate n true
lemma kd (n:ℕ):true::rep n=rep (n+1):=rfl
lemma qcq (a:Q0):
 ∀ (w:Q0) (b:ℕ) (s:Option Bool),
   zf^[w.length+1] (some ⟨some .split,s,zh (w.map inr) a (rep b) [] []⟩)=
    some ⟨some .outer,none,zh [] a (rep (w.length+b)) [] []⟩:=by
 intro w;induction w with
 | nil=>intro b s; simpa using qc4 s a (rep b) [] []
 | cons y w ih=>intro b s;rw [qI,ze,List.map_cons,qc3,kd,ih];rw [show w.length+(b+1)=w.length+1+b from by omega]
lemma qcr (w:Q0):
 ∀ (x:Q0) (a:ℕ) (s:Option Bool),
   zf^[x.length+(w.length+1)]
    (some ⟨some .split,s,zh (x.map inl++w.map inr) (rep a) [] [] []⟩)=
    some ⟨some .outer,none,zh [] (rep (x.length+a)) (rep w.length) [] []⟩:=by
 intro x;induction x with
 | nil=>intro a s;simpa using qcq (rep a) w 0 s
 | cons y x ih=>
   intro a s
   rw [qI,show x.length+1+(w.length+1)=(x.length+(w.length+1))+1
    from by omega,ze,List.map_cons,List.cons_append,qc2,
    kd,ih]
   rw [show x.length+(a+1)=x.length+1+a from by omega]
lemma qdg (a:Q0):
 ∀ (b c o:ℕ) (s:Option Bool),
   zf^[b+1] (some ⟨some .copy,s,zh [] a (rep b) (rep c) (rep o)⟩)=
    some ⟨some .back,none,zh [] a [] (rep (b+c)) (rep (b+o))⟩:=by
 intro b;induction b with
 | zero=>intro c o s; simpa using qdh s [] a (rep c) (rep o)
 | succ b ih=>intro c o s;rw [ze,← kd b,qcE,kd,kd,ih];rw [show b+(c+1)=b+1+c from by omega,show b+(o+1)=b+1+o from by omega]
lemma qde (a o:Q0):
 ∀ (c b:ℕ) (s:Option Bool),
   zf^[c+1] (some ⟨some .back,s,zh [] a (rep b) (rep c) o⟩)=
    some ⟨some .outer,none,zh [] a (rep (c+b)) [] o⟩:=by
 intro c;induction c with
 | zero=>intro b s; simpa using qdf s [] a (rep b) o
 | succ c ih=>intro b s;rw [ze,← kd c,qcB,kd,ih];rw [show c+(b+1)=c+1+b from by omega]
lemma qc0 (b:ℕ):
 ∀ (a o:ℕ) (s:Option Bool),
   zf^[a * (2 * b+3)+1] (some ⟨some .outer,s,zh [] (rep a) (rep b) [] (rep o)⟩)=
    some ⟨some .clean,none,zh [] [] (rep b) [] (rep (a * b+o))⟩:=by
 intro a;induction a with
 | zero=>intro o s; simpa using qc1 s [] (rep b) [] (rep o)
 | succ a ih=>
   intro o s
   rw [show (a+1) * (2 * b+3)+1=(a * (2 * b+3)+1)+((b+1)+((b+1)+1))
    from by ring,iterate_add_apply zf (a * (2 * b+3)+1),
    iterate_add_apply zf (b+1) ((b+1)+1),
    ze zf (b+1),← kd a,qcp]
   have h1:zf^[b+1]
    (some ⟨some .copy,some true,zh [] (rep a) (rep b) [] (rep o)⟩)=
    some ⟨some .back,none,zh [] (rep a) [] (rep b) (rep (b+o))⟩:=
    qdg (rep a) b 0 o (some true)
   rw [h1]
   have h2:zf^[b+1]
    (some ⟨some .back,none,zh [] (rep a) [] (rep b) (rep (b+o))⟩)=
    some ⟨some .outer,none,zh [] (rep a) (rep b) [] (rep (b+o))⟩:=
    qde (rep a) (rep (b+o)) b 0 none
   rw [h2,ih];rw [show a * b+(b+o)=(a+1) * b+o from by ring]
lemma qcC (o:Q0):
 ∀ (b:ℕ) (s:Option Bool),
   zf^[b+1] (some ⟨some .clean,s,zh [] [] (rep b) [] o⟩)=
    some ⟨none,none,zh [] [] [] [] o⟩:=by
 intro b;induction b with
 | zero=>intro s; simpa using qcD s [] [] [] o
 | succ b ih=>intro s;rw [ze,← kd b,qca,ih]
def kT (x w:ℕ):ℕ:=(w+1)+((x * (2 * w+3)+1)+(x+(w+1)))
lemma qec (x w:Q0):
 (flip bind (TM2.step v5))^[kT x.length w.length]
   (some (initList jP (x.map inl++w.map inr)))=
   some (haltList jP (rep (x.length * w.length))):=by
 refine (congrArg (fun c=>(flip bind (TM2.step v5))^[kT x.length w.length]
  (some c)) (zH jP _)).trans
  (Eq.trans ?_ (congrArg some (zG jP _)).symm)
 show zf^[kT x.length w.length]
  (some (⟨some .split,none,update (fun _=>[]) .I
    (x.map inl++w.map inr)⟩:MulCfg))=
  some (⟨none,none,update (fun _=>[]) .O (rep (x.length * w.length))⟩:MulCfg)
 rw [← qcm,← qds,kT,iterate_add_apply zf (w.length+1),iterate_add_apply zf (x.length * (2 * w.length+3)+1)]
 have h1:zf^[x.length+(w.length+1)]
  (some ⟨some .split,none,zh (x.map inl++w.map inr) [] [] [] []⟩)=
  some ⟨some .outer,none,zh [] (rep x.length) (rep w.length) [] []⟩:=
  qcr w x 0 none
 rw [h1]
 have h2:zf^[x.length * (2 * w.length+3)+1]
  (some ⟨some .outer,none,zh [] (rep x.length) (rep w.length) [] []⟩)=
  some ⟨some .clean,none,zh [] [] (rep w.length) [] (rep (x.length * w.length))⟩:=
  qc0 w.length x.length 0 none
 rw [h2,qcC]
lemma wc:
 Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:Q0=>x)
  (fun p:Q0×Q0=>List.replicate (p.1.length * p.2.length) true)):=by
 exact ⟨{
  tm:=jP
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2 * Polynomial.X ^ 2+Polynomial.C 5 * Polynomial.X+Polynomial.C 3
  outputsFun:=fun p=>
   { steps:=kT p.1.length p.2.length
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      have:=qec p.1 p.2
      exact (congrArg (fun l=>(flip bind (TM2.step v5))^[kT p.1.length
       p.2.length] (some (initList jP l))) (hm _ (encodePair p))).trans
       (this.trans (congrArg (fun l=>some (haltList jP l)) (hm Bool _).symm))
     steps_le_m:=by simp only [zO,z9,vT,Polynomial.eval_X,Polynomial.eval_pow,encodePair,List.length_append,zM,kT];nlinarith [Nat.zero_le (p.1.length * p.1.length),Nat.zero_le (p.2.length * p.2.length),Nat.zero_le (p.1.length * p.2.length)] } }⟩
end Lib.qC
end
section
namespace Lib.qC
open PEqualNP.Library
private theorem zV {α β γ:Type} (h:α→β) (φ:β→Option γ) (g:α→γ)
 (hφ:∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ=l.map g:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [hφ,ih]
private theorem yR {α β γ:Type} (h:α→β) (φ:β→Option γ)
 (hφ:∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [hφ,ih]
lemma qG {α β γ αΓ βΓ γΓ:Type} {ea:α→List αΓ} {eb:β→List βΓ}
 {ec:γ→List γΓ} {f:α→β} {g:β→γ}
 (hf:Q6 ea eb f)
 (hg:Q6 eb ec g):
 Q6 ea ec (fun a=>g (f a)):=by
 obtain ⟨c1⟩:=hf;obtain ⟨c2⟩:=hg;exact qaM ea eb ec f g c1 c2
lemma wU:
 Q6 PEqualNP.Library.encodePair
  PEqualNP.Library.encodePair (fun p:Q0×Q0=>(p.2,p.1)):=by
 refine kg _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some (inl b)) s)
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some (inr b)) (fun _=>none) s) ?_
 rintro ⟨x,w⟩;simp only [encodePair,List.filterMap_append]
 rw [yR inl _ (fun _=>rfl) x,
  zV inr _ inl (fun _=>rfl) w,
  zV inl _ inr (fun _=>rfl) x,
  yR inr _ (fun _=>rfl) w]
 simp
lemma qdK:
 Q6 (fun x:Q0=>x)
  PEqualNP.Library.encodePair (fun x:Q0=>(x,x)):=by
 refine kg _ _ _
  (fun b:Bool=>some (inl b)) (fun b:Bool=>some (inr b)) ?_
 intro x
 have h1:=zV (fun b:Bool=>b) (fun b:Bool=>some (inl (β:=Bool) b))
  inl (fun _=>rfl) x
 have h2:=zV (fun b:Bool=>b) (fun b:Bool=>some (inr (α:=Bool) b))
  inr (fun _=>rfl) x
 simp only [List.map_id'] at h1 h2;simp only [encodePair,h1,h2]
lemma qdL:
 Q6 PEqualNP.Library.encodePair
  (fun x:Q0=>x) (fun p:Q0×Q0=>p.1):=by
 refine yS _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_
 rintro ⟨x,w⟩;simp only [encodePair,List.filterMap_append]
 rw [zV inl _ (fun b=>b) (fun _=>rfl) x,
  yR inr _ (fun _=>rfl) w]
 simp
lemma qdM:
 Q6 PEqualNP.Library.encodePair
  (fun x:Q0=>x) (fun p:Q0×Q0=>p.2):=by
 refine yS _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_
 rintro ⟨x,w⟩;simp only [encodePair,List.filterMap_append]
 rw [yR inl _ (fun _=>rfl) x,
  zV inr _ (fun b=>b) (fun _=>rfl) w]
 simp
lemma jF:
 Q6 PEqualNP.Library.encodePair
  (fun x:Q0=>x) (fun p:Q0×Q0=>p.1++p.2):=by
 refine yS _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_
 rintro ⟨x,w⟩;simp only [encodePair,List.filterMap_append]
 rw [zV inl _ (fun b=>b) (fun _=>rfl) x,
  zV inr _ (fun b=>b) (fun _=>rfl) w]
 simp
lemma u8 {f:Q0→Q0}
 (hf:Q6 (fun x:Q0=>x)
   (fun x:Q0=>x) f):
 Q6 PEqualNP.Library.encodePair
  PEqualNP.Library.encodePair (fun p:Q0×Q0=>(f p.1,p.2)):=by
 obtain ⟨c⟩:=hf;exact qaq f c
lemma qcd {g:Q0→Q0}
 (hg:Q6 (fun x:Q0=>x)
   (fun x:Q0=>x) g):
 Q6 PEqualNP.Library.encodePair
  PEqualNP.Library.encodePair (fun p:Q0×Q0=>(p.1,g p.2)):=
 qG (qG wU (u8 hg)) wU
lemma yI {f g:Q0→Q0}
 (hf:Q6 (fun x:Q0=>x)
   (fun x:Q0=>x) f)
 (hg:Q6 (fun x:Q0=>x)
   (fun x:Q0=>x) g):
 Q6 (fun x:Q0=>x)
  PEqualNP.Library.encodePair (fun x:Q0=>(f x,g x)):=
 qG (qG qdK (qcd hg)) (u8 hf)
lemma yP:
 Q6 (fun x:Q0=>x)
  (fun x:Q0=>x) (fun x:Q0=>x):=by
 refine yS _ _ _ (fun b:Bool=>some b) ?_
 intro x
 have h:=zV (fun b:Bool=>b) (fun b:Bool=>some b) (fun b=>b)
  (fun _=>rfl) x
 simp only [List.map_id'] at h;exact h.symm
end Lib.qC
end
section
namespace Lib.qC
open Turing PEqualNP.Library
lemma yV (f:Q0→Q0)
 (hf:Q6 (fun x:Q0=>x) (fun x:Q0=>x) f):
 ∃ q:Q5,∀ x:Q0,(f x).length≤q.eval x.length:=by
 obtain ⟨c⟩:=hf;refine ⟨Polynomial.X+Polynomial.C (yh c.tm) * c.time,fun x=>?_⟩
 obtain ⟨⟨steps,hev⟩,hle⟩:=c.outputsFun x
 have hev':(flip bind (TM2.step c.tm.m))^[steps]
  (some (⟨some c.tm.main,c.tm.initialState,update (fun _=>[]) c.tm.k₀
    (List.map c.inputAlphabet.invFun x)⟩:TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ))=
  some (⟨none,c.tm.initialState,update (fun _=>[]) c.tm.k₁
   (List.map c.outputAlphabet.invFun (f x))⟩:TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ):=by
  rw [← zH,← zG]; exact hev
 have key:=jR c.tm c.tm.k₁ steps _ _ hev';simp only [update_self,zM] at key
 have hin:((update (fun _=>([]:List _)) c.tm.k₀
  (List.map c.inputAlphabet.invFun x):∀ k,List (c.tm.Γ k)) c.tm.k₁).length≤x.length:=by
  by_cases hk:c.tm.k₁=c.tm.k₀
  · rw [hk]; simp
  · rw [update_of_ne hk]; simp
 rw [zO,Polynomial.eval_X,z9,vT]
 calc (f x).length≤x.length+yh c.tm * steps:=key.trans (by omega)
  _≤x.length+yh c.tm * c.time.eval x.length:=Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _
end Lib.qC
end
section
namespace Lib.qC
open Turing
def qD {Γ₀ Γ₁ Q:Type} (δ:Q→Γ₀→Q×Option Γ₁) (fin:Q→Option Γ₁):
    Q→List Γ₀→List Γ₁
 | q,[]=>(fin q).toList
 | q,a::l=>(δ q a).2.toList++qD δ fin (δ q a).1 l
def z6 {Γ₀ Γ₁ Q:Type} (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁):
    Q→List Γ₀→List Γ₁
 | q,[]=>(fin q).toList
 | q,a::l=>(δ q a).2.1.toList++(δ q a).2.2.toList++z6 δ fin (δ q a).1 l
lemma wA {Γ₀ Γ₁ Q:Type} (δ:Q→Γ₀→Q×Option Γ₁) (fin:Q→Option Γ₁)
 (q:Q) (l:List Γ₀):
 qD δ fin q l=z6 (fun q a=>((δ q a).1,(δ q a).2,none)) fin q l:=by
 induction l generalizing q with
 | nil=>rfl
 | cons a l ih=>simp [qD,z6,ih]
inductive TrK:Type
 | inp|tmp|out
 deriving DecidableEq
instance:Fintype TrK:=Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK→Type
 | .inp=>Γ₀
 | .tmp=>Q×Option Γ₀
 | .out=>Γ₁
abbrev TrS (Γ₀ Q:Type):Type:=Q×Option Γ₀×Bool
def qcw (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁):
    Q×Option Γ₀→Option Γ₁
 | (q,some a)=>(δ q a).2.1
 | (q,none)=>fin q
def qcx (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁):Q×Option Γ₀→Option Γ₁
 | (q,some a)=>(δ q a).2.2
 | (_,none)=>none
def jU (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁)
    (e:Q×Option Γ₀):List Γ₁:=
 (qcw δ fin e).toList++(qcx δ e).toList
def y5 (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁):Q→List Γ₀→List (Q×Option Γ₀)
 | q,[]=>[(q,none)]
 | q,a::l=>(q,some a)::y5 δ (δ q a).1 l
lemma qaw (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (q:Q) (l:List Γ₀):
 (y5 δ q l).length=l.length+1:=by
 induction l generalizing q with
 | nil=>rfl
 | cons a l ih=>simp [y5,ih]
lemma qbR (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁) (q:Q)
 (l:List Γ₀):(y5 δ q l).flatMap (jU δ fin)=z6 δ fin q l:=by
 induction l generalizing q with
 | nil=>simp [y5,jU,qcw,qcx,z6]
 | cons a l ih=>simp [y5,jU,qcw,qcx,z6,ih]
def jz (o:TrS Γ₀ Q→Option Γ₁) (d:Option Γ₁)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)):
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q):=
 .branch (fun s=>(o s).isSome)
   (match d with
     | some dd=>.push .out (fun s=>(o s).getD dd) next
     | none=>next)
   next
def vY (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁) (q₀:Q)
    (d:Option Γ₁):Bool→TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
 | false=>
   .pop .inp (fun s o=>(s.1,o,o.isSome))
     (.branch (fun s=>s.2.2)
       (.push .tmp (fun s=>(s.1,s.2.1))
         (.load (fun s=>(match s.2.1 with
            | some a=>(δ s.1 a).1
            | none=>s.1,none,false))
           (.goto fun _=>false)))
       (.push .tmp (fun s=>(s.1,none))
         (.load (fun _=>(q₀,none,false)) (.goto fun _=>true))))
 | true=>
   .pop .tmp (fun _ o=>match o with
     | some e=>(e.1,e.2,true)
     | none=>(q₀,none,false))
     (.branch (fun s=>s.2.2)
       (jz (fun s=>qcx δ (s.1,s.2.1)) d
         (jz (fun s=>qcw δ fin (s.1,s.2.1)) d (.goto fun _=>true)))
       .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁)
    (fin:Q→Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
 K:=TrK
 k₀:=.inp
 k₁:=.out
 Γ:=TrΓ Γ₀ Γ₁ Q
 Λ:=Bool
 main:=false
 σ:=TrS Γ₀ Q
 initialState:=(q₀,none,false)
 Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
 m:=vY δ fin q₀ d
def vd (l:List Γ₀) (t:List (Q×Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
 | .inp=>l
 | .tmp=>t
 | .out=>u
lemma wg (l l':List Γ₀) (t:List (Q×Option Γ₀)) (u:List Γ₁):
 update (vd l t u) .inp l'=vd l' t u:=by
 funext k; cases k <;> simp [vd]
lemma k8 (l:List Γ₀) (t t':List (Q×Option Γ₀)) (u:List Γ₁):
 update (vd l t u) .tmp t'=vd l t' u:=by
 funext k; cases k <;> simp [vd]
lemma qbz (l:List Γ₀) (t:List (Q×Option Γ₀)) (u u':List Γ₁):
 update (vd l t u) .out u'=vd l t u':=by
 funext k; cases k <;> simp [vd]
lemma qcy (l:List Γ₀):
 (vd l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k))=
   update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:=by
 funext k; cases k <;> simp [vd]
lemma qdD (u:List Γ₁):
 (vd [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k))=
   update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:=by
 funext k; cases k <;> simp [vd]
abbrev kQ (Γ₀ Γ₁ Q:Type):Type:=TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
lemma jf (o:TrS Γ₀ Q→Option Γ₁) (d:Option Γ₁) (hd:∀ _:Γ₁,d≠none)
 (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
 (t:List (Q×Option Γ₀)) (u:List Γ₁):
 TM2.stepAux (jz o d next) s (vd l t u)=
  TM2.stepAux next s (vd l t ((o s).toList++u)):=by
 cases ho:o s with
 | none=>cases d <;> simp [jz,TM2.stepAux,ho]
 | some y=>
   cases d with
   | none=>exact absurd rfl (hd y)
   | some dd=>simp [jz,TM2.stepAux,ho,vd,qbz]
variable (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁) (q₀:Q)
 (d:Option Γ₁)
lemma qdB (s:TrS Γ₀ Q) (a:Γ₀) (l:List Γ₀) (t:List (Q×Option Γ₀))
 (u:List Γ₁):
 TM2.step (vY δ fin q₀ d) (⟨some false,s,vd (a::l) t u⟩:kQ Γ₀ Γ₁ Q)=
  some ⟨some false,((δ s.1 a).1,none,false),vd l ((s.1,some a)::t) u⟩:=by
 simp [TM2.step,vY,TM2.stepAux,vd,wg,k8]
lemma qem (s:TrS Γ₀ Q) (t:List (Q×Option Γ₀)) (u:List Γ₁):
 TM2.step (vY δ fin q₀ d) (⟨some false,s,vd [] t u⟩:kQ Γ₀ Γ₁ Q)=
  some ⟨some true,(q₀,none,false),vd [] ((s.1,none)::t) u⟩:=by
 simp [TM2.step,vY,TM2.stepAux,vd,wg,k8]
lemma qdC (hd:∀ _:Γ₁,d≠none) (s:TrS Γ₀ Q) (e:Q×Option Γ₀)
 (t:List (Q×Option Γ₀)) (u:List Γ₁):
 TM2.step (vY δ fin q₀ d) (⟨some true,s,vd [] (e::t) u⟩:kQ Γ₀ Γ₁ Q)=
  some ⟨some true,(e.1,e.2,true),vd [] t (jU δ fin e++u)⟩:=by
 simp only [TM2.step,vY,TM2.stepAux];have e1:(vd [] (e::t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e::t:=rfl;rw [e1];simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
 rw [k8,jf _ _ hd,jf _ _ hd];simp [TM2.stepAux,jU]
lemma qen (s:TrS Γ₀ Q) (u:List Γ₁):
 TM2.step (vY δ fin q₀ d) (⟨some true,s,vd [] [] u⟩:kQ Γ₀ Γ₁ Q)=
  some ⟨none,(q₀,none,false),vd [] [] u⟩:=by
 simp [TM2.step,vY,TM2.stepAux,vd,k8]
lemma qeo (u:List Γ₁):
 ∀ (l:List Γ₀) (t:List (Q×Option Γ₀)) (s:TrS Γ₀ Q),
   (flip bind (TM2.step (vY δ fin q₀ d)))^[l.length+1]
     (some (⟨some false,s,vd l t u⟩:kQ Γ₀ Γ₁ Q))=
     some ⟨some true,(q₀,none,false),vd [] ((y5 δ s.1 l).reverse++t) u⟩:=by
 intro l;induction l with
 | nil=>intro t s; exact qem δ fin q₀ d s t u
 | cons a l ih=>
   intro t s;rw [qI,ze]
   have e:flip bind (TM2.step (vY δ fin q₀ d))
    (some (⟨some false,s,vd (a::l) t u⟩:kQ Γ₀ Γ₁ Q))=
    some ⟨some false,((δ s.1 a).1,none,false),vd l ((s.1,some a)::t) u⟩:=
    qdB δ fin q₀ d s a l t u
   rw [e,ih];simp [y5]
lemma qep (hd:∀ _:Γ₁,d≠none):
 ∀ (t:List (Q×Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
   (flip bind (TM2.step (vY δ fin q₀ d)))^[t.length+1]
     (some (⟨some true,s,vd [] t u⟩:kQ Γ₀ Γ₁ Q))=
     some ⟨none,(q₀,none,false),vd [] [] (t.reverse.flatMap (jU δ fin)++u)⟩:=by
 intro t;induction t with
 | nil=>intro u s; exact qen δ fin q₀ d s u
 | cons e t ih=>
   intro u s;rw [qI,ze]
   have e':flip bind (TM2.step (vY δ fin q₀ d))
    (some (⟨some true,s,vd [] (e::t) u⟩:kQ Γ₀ Γ₁ Q))=
    some ⟨some true,(e.1,e.2,true),vd [] t (jU δ fin e++u)⟩:=
    qdC δ fin q₀ d hd s e t u
   rw [e',ih];simp [List.flatMap_append]
lemma qeq [Fintype Γ₀] [Fintype Q] (hd:∀ _:Γ₁,d≠none) (l:List Γ₀):
 (flip bind (TM2.step (vY δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
   (some (initList (trM δ fin q₀ d) l))=
   some (haltList (trM δ fin q₀ d) (z6 δ fin q₀ l)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (vY δ fin q₀ d)))^[l.length+1+1 +
  (l.length+1)] (some c)) (zH (trM δ fin q₀ d) l)).trans
  (Eq.trans ?_ (congrArg some (zG (trM δ fin q₀ d) (z6 δ fin q₀ l))).symm)
 show (flip bind (TM2.step (vY δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
  (some (⟨some false,(q₀,none,false),update (fun _=>[]) .inp l⟩:
    kQ Γ₀ Γ₁ Q))=
  some (⟨none,(q₀,none,false),update (fun _=>[]) .out (z6 δ fin q₀ l)⟩:
   kQ Γ₀ Γ₁ Q)
 have hA:(flip bind (TM2.step (vY δ fin q₀ d)))^[l.length+1]
  (some (⟨some false,(q₀,none,false),vd l [] []⟩:kQ Γ₀ Γ₁ Q))=
  some ⟨some true,(q₀,none,false),vd [] (y5 δ q₀ l).reverse []⟩:=by
  have:=qeo δ fin q₀ d [] l [] (q₀,none,false);rw [qX] at this;exact this
 have hB:(flip bind (TM2.step (vY δ fin q₀ d)))^[l.length+1+1]
  (some (⟨some true,(q₀,none,false),vd [] (y5 δ q₀ l).reverse []⟩:kQ Γ₀ Γ₁ Q))=
  some ⟨none,(q₀,none,false),vd [] [] (z6 δ fin q₀ l)⟩:=by
  have:=qep δ fin q₀ d hd (y5 δ q₀ l).reverse [] (q₀,none,false);rw [vJ,qaw,List.reverse_reverse,qbR,qX] at this;exact this
 rw [iterate_add_apply,← qcy,hA,hB,qdD]
lemma uA {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (δ:Q→αΓ→Q×Option βΓ×Option βΓ)
 (fin:Q→Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=z6 δ fin q₀ (ea a)):
 Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
 classical
 let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
 have hd:∀ _:βΓ,d≠none:=by intro y;have hn:Nonempty βΓ:=⟨y⟩;simp [d,hn]
 exact ⟨{
  tm:=trM δ fin q₀ d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 3
  outputsFun:=fun a=>
   { steps:=(ea a).length+1+1+((ea a).length+1)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=fun γ l=>by simp
      have:=qeq δ fin q₀ d hd (ea a)
      exact (congrArg (fun l=>(flip bind (TM2.step (vY δ fin q₀ d)))^[(ea a).length +
       1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
       (hm αΓ (ea a))).trans
       (this.trans (congrArg (fun l=>some (haltList (trM δ fin q₀ d) l))
         ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
     steps_le_m:=by simp only [zO,z9,vT,Polynomial.eval_X];omega } }⟩
lemma yJ {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (δ:Q→αΓ→Q×Option βΓ) (fin:Q→Option βΓ) (q₀:Q)
 (h:∀ a,eb (f a)=qD δ fin q₀ (ea a)):
 Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=
 uA ea eb f (fun q a=>((δ q a).1,(δ q a).2,none)) fin q₀
  (fun a=>(h a).trans (wA δ fin q₀ (ea a)))
end Lib.qC
end
section
namespace Lib.qC
open PEqualNP.Library
private theorem qbW {f g:Q0→Q0}
 (hf:Q6 (fun x:Q0=>x)
   (fun x:Q0=>x) f)
 (hg:Q6 (fun x:Q0=>x)
   (fun x:Q0=>x) g):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun x:Q0=>List.replicate ((f x).length * (g x).length) true):=
 qG (yI hf hg) wc
private theorem qbw
 (hconst:∀ l:Q0,Q6
   (fun x:Q0=>x) (fun x:Q0=>x) (fun _:Q0=>l))
 (n:ℕ):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun x:Q0=>List.replicate (x.length ^ n) true):=by
 induction n with
 | zero=>simpa using hconst [true]
 | succ n ih=>
   have h:=qbW yP ih
   have e:(fun x:Q0=>
    List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true)=
    (fun x:Q0=>List.replicate (x.length ^ (n+1)) true):=by
    funext x
    rw [List.length_replicate,pow_succ,Nat.mul_comm]
   rw [← e];exact h
lemma qai
 (hconst:∀ l:Q0,Q6
   (fun x:Q0=>x) (fun x:Q0=>x) (fun _:Q0=>l))
 (p:Q5):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun x:Q0=>List.replicate (p.eval x.length) true):=by
 induction p using Polynomial.induction_on' with
 | add p q hp hq=>
   have h:=qG (yI hp hq) jF
   have e:(fun x:Q0=>List.replicate (p.eval x.length) true++
    List.replicate (q.eval x.length) true)=
    (fun x:Q0=>List.replicate ((p+q).eval x.length) true):=by
    funext x
    rw [zO,List.replicate_add]
   rw [← e];exact h
 | monomial n a=>
   have h:=qbW (hconst (List.replicate a true)) (qbw hconst n)
   have e:(fun x:Q0=>List.replicate ((List.replicate a true).length *
    (List.replicate (x.length ^ n) true).length) true)=
    (fun x:Q0=>List.replicate ((Polynomial.monomial n a).eval x.length) true):=by
    funext x
    rw [List.length_replicate,List.length_replicate,Polynomial.eval_monomial]
   rw [← e];exact h
end Lib.qC
end
section
lemma Lib.qes:∀ p:Q5,
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun x:Q0=>List.replicate (p.eval x.length) true):=
 fun p=>Lib.qC.qai
  (fun l=>Lib.qC.yO l) p
end
section
namespace Lib.ve
def un (n:ℕ):Q0:=List.replicate n true
def qv (a b:Q0):Q0:=un a.length++false::(a++b)
def Q9 (s:Q0):Q0×Q0:=(((s.dropWhile id).tail).take (s.takeWhile id).length,((s.dropWhile id).tail).drop (s.takeWhile id).length)
lemma qk (a b:Q0):Q9 (qv a b)=(a,b):=by
 have h1:(qv a b).takeWhile id=un a.length:=by simp [qv,un]
 have h2:(qv a b).dropWhile id=false::(a++b):=by simp [qv,un]
 simp [Q9,h1,h2,un]
end Lib.ve
end
section
namespace Lib.ve
@[simp] theorem qfu:un 0=[]:=rfl
@[simp] theorem za (n:ℕ):(un n).length=n:=List.length_replicate
lemma uT (n:ℕ):un (n+1)=true::un n:=rfl
lemma qfK {a b:ℕ} (h:un a=un b):a=b:=by have:=congrArg List.length h;simpa [un] using this
def hd (s:Q0):Q0:=s.takeWhile id
def sel (f a b:Q0):Q0:=if f=[] then a else b
def uk (u v:Q0):Q0:=un (u.length * v.length)
lemma yE (s:Q0):
 2 * (Q9 s).1.length+(Q9 s).2.length≤ s.length:=by
 have h:=congrArg List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s));simp only [List.length_append] at h;simp only [Q9,List.length_take,List.length_drop,List.length_tail];omega
lemma zW (a b:Q0):(qv a b).length=2 * a.length+b.length+1:=by simp [qv]; omega
end Lib.ve
end
section
namespace Lib.ve
open PEqualNP.Library Lib.qC
private theorem u7 {α β αΓ βΓ:Type} {ea:α→List αΓ} {eb:β→List βΓ}
 {f f':α→β} (h:Q6 ea eb f) (e:∀ a,f a=f' a):
 Q6 ea eb f':=by
 obtain rfl:f=f':=funext e;exact h
private theorem qb6 {A B C:Type} (φl:A→Option C) (φr:B→Option C) (x:List A)
 (w:List B):
 (x.map inl++w.map inr).filterMap (Sum.elim φl φr)=
   x.filterMap φl++w.filterMap φr:=by
 have h1:∀ x:List A,(x.map inl).filterMap (Sum.elim φl φr)=x.filterMap φl:=by
  intro x; induction x with
  | nil=>rfl
  | cons a l ih=>simp [List.filterMap_cons,ih]
 have h2:∀ w:List B,(w.map inr).filterMap (Sum.elim φl φr)=w.filterMap φr:=by
  intro w; induction w with
  | nil=>rfl
  | cons a l ih=>simp [List.filterMap_cons,ih]
 rw [List.filterMap_append,h1,h2]
private theorem qar {A C:Type} (g:A→C) (l:List A):
 l.filterMap (fun a=>some (g a))=l.map g:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [ih]
private theorem qd4 {A C:Type} (l:List A):
 l.filterMap (fun _:A=>(none:Option C))=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp
lemma qcH:
 Q6 encodePair (fun x:Q0=>x)
  (fun p:Q0×Q0=>qv p.1 p.2):=by
 have hA:Q6 encodePair encodePair
  (fun p:Q0×Q0=>(p.1,p.1++p.2)):=by
  refine kg _ _ _
   (Sum.elim (fun b:Bool=>some (inl b)) (fun _:Bool=>none))
   (Sum.elim (fun b:Bool=>some (inr b)) (fun b:Bool=>some (inr b))) ?_
  rintro ⟨x,w⟩;simp only [encodePair];rw [qb6,qb6,qar,qar,qar,qd4];simp
 have hU:Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun a:Q0=>a.map (fun _=>true)++[false]):=by
  refine yJ _ _ _ (fun (_:Unit) (_:Bool)=>((),some true))
   (fun _=>some false) () ?_
  intro a;induction a with
  | nil=>rfl
  | cons b l ih=>simp only [qD,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢;rw [← ih]; rfl
 refine u7 (qG (qG hA (u8 hU)) jF) ?_
 rintro ⟨x,w⟩;simp [qv,un]
lemma jk:
 Q6 encodePair (fun x:Q0=>x)
  (fun p:Q0×Q0=>if p.1=[] then p.2 else []):=by
 obtain ⟨c⟩:=yO [];have hI:=jE.uB (fun _:Q0=>([]:Q0)) c 0 (by simp);refine u7 (qG wU hI) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil=>simp
 | cons b l=>simp [qM]
lemma qan:
 Q6 encodePair (fun x:Q0=>x)
  (fun p:Q0×Q0=>if p.1=[] then [] else p.2):=by
 have h0:Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun x:Q0=>if x=[] then [true] else []):=
  qG (yI yP (yO [true])) jk
 refine u7 (qG (u8 h0) jk) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil=>simp
 | cons b l=>simp
private def ug (u:Q0):Q0:=u.flatMap (fun b=>[true,b])
private def y3 (v:Q0):Q0:=v.flatMap (fun b=>[false,b])
private def twD:Bool→Bool→Bool×Option Bool
 | true,true=>(true,some true)
 | _,_=>(false,none)
private theorem qer (l:Q0):
 qD twD (fun _=>none) false l=[]∧
  qD twD (fun _=>none) true l=l.takeWhile id:=by
 induction l with
 | nil=>exact ⟨rfl,rfl⟩
 | cons b l ih=>cases b <;> simp [qD,twD,ih.1,ih.2]
private def e0D:Bool→Bool→Bool×Option Bool×Option Bool
 | false,true=>(false,none,none)
 | false,false=>(true,none,none)
 | true,b=>(true,some false,some b)
private theorem qbf (l:Q0):
 z6 e0D (fun _=>none) true l=y3 l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [z6,e0D,y3,ih]
private theorem qaQ (l:Q0):
 z6 e0D (fun _=>none) false l=y3 (l.dropWhile id).tail:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>cases b <;> simp [z6,e0D,ih,qbf]
private def mkD:Bool×Bool→Bool→(Bool×Bool)×Option Bool
 | (d,false),t=>((d||!t,true),some (t||!d))
 | (d,true),b=>((d,false),some b)
private def mk (l:Q0):Q0:=qD mkD (fun _=>none) (false,false) l
private theorem qcl (q:Bool×Bool) (l:Q0):
 (qD mkD (fun _=>none) q l).length=l.length:=by
 induction l generalizing q with
 | nil=>rfl
 | cons b l ih=>obtain ⟨d,ph⟩:=q; cases ph <;> simp [qD,mkD,ih]
private theorem qdr (v:Q0):
 qD mkD (fun _=>none) (true,false) (y3 v)=y3 v:=by
 induction v with
 | nil=>rfl
 | cons b v ih=>simp [qD,mkD,y3] at ih ⊢; exact ih
private theorem qab (u r:Q0):
 qD mkD (fun _=>none) (false,false) (ug u++r)=
  ug u++qD mkD (fun _=>none) (false,false) r:=by
 induction u with
 | nil=>rfl
 | cons b u ih=>simp [qD,mkD,ug] at ih ⊢; exact ih
private theorem qeS (u:Q0):mk (ug u++y3 [])=ug u++y3 []:=by unfold mk; rw [qab]; rfl
private theorem qea (u:Q0) (b:Bool) (v:Q0):
 mk (ug u++y3 (b::v))=ug (u++[b])++y3 v:=by
 unfold mk;rw [qab]
 have h:qD mkD (fun _=>none) (false,false) (y3 (b::v))=
  true::b::y3 v:=by
  have h':=qdr v;simp [qD,mkD,y3] at h' ⊢;exact h'
 rw [h];simp [ug]
private theorem qeb (k:ℕ):∀ u t:Q0,
 mk^[k] (ug u++y3 t)=ug (u++t.take k)++y3 (t.drop k):=by
 induction k with
 | zero=>intro u t; simp
 | succ k ih=>
   intro u t;rw [ze]
   cases t with
   | nil=>rw [qeS,ih]; simp
   | cons b t=>rw [qea,ih]; simp
private def dcD:Option Bool→Bool→Option Bool×Option (Bool ⊕ Bool)
 | none,t=>(some t,none)
 | some t,b=>(none,some (if t then inl b else inr b))
private theorem qe0 (v:Q0):
 qD dcD (fun _=>none) none (y3 v)=v.map inr:=by
 induction v with
 | nil=>rfl
 | cons b v ih=>simp [qD,dcD,y3] at ih ⊢; exact ih
private theorem qe1 (u r:Q0):
 qD dcD (fun _=>none) none (ug u++r)=
  u.map inl++qD dcD (fun _=>none) none r:=by
 induction u with
 | nil=>rfl
 | cons b u ih=>simp [qD,dcD,ug] at ih ⊢; exact ih
private def rawDec (l:List (Bool ⊕ Bool)):Q0×Q0:=(l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private theorem qaY (u v:Q0):
 rawDec (u.map inl++v.map inr)=(u,v):=by
 have h1:∀ x:Q0,(x.map (inl (β:=Bool))).filterMap Sum.getLeft?=x:=by
  intro x; induction x with
  | nil=>rfl
  | cons a l ih=>exact congrArg (a::·) ih
 have h2:∀ x:Q0,(x.map (inr (α:=Bool))).filterMap Sum.getLeft?=[]:=by
  intro x; induction x with
  | nil=>rfl
  | cons a l ih=>exact ih
 have h3:∀ x:Q0,(x.map (inl (β:=Bool))).filterMap Sum.getRight?=[]:=by
  intro x; induction x with
  | nil=>rfl
  | cons a l ih=>exact ih
 have h4:∀ x:Q0,(x.map (inr (α:=Bool))).filterMap Sum.getRight?=x:=by
  intro x; induction x with
  | nil=>rfl
  | cons a l ih=>exact congrArg (a::·) ih
 simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,qX,List.nil_append]
lemma wH:
 Q6 (fun x:Q0=>x) encodePair Q9:=by
 have hTw:Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s:Q0=>s.takeWhile id):=
  yJ _ _ _ twD (fun _=>none) true (fun s=>(qer s).2.symm)
 have hE0:Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s:Q0=>y3 (s.dropWhile id).tail):=
  uA _ _ _ e0D (fun _=>none) false (fun s=>(qaQ s).symm)
 have hMk:Q6 (fun x:Q0=>x) (fun x:Q0=>x) mk:=yJ _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl)
 obtain ⟨cMk⟩:=hMk;have hIt:=jE.uB mk cMk 0 (fun y=>by simp [mk,qcl])
 have hDc:Q6 (fun x:Q0=>x) (fun l:List (Bool ⊕ Bool)=>l)
  (fun l:Q0=>qD dcD (fun _=>none) none l):=
  yJ _ _ _ dcD (fun _=>none) none (fun _=>rfl)
 have h0:Q6 (fun l:List (Bool ⊕ Bool)=>l) encodePair rawDec:=by
  refine kg _ _ _
   (fun s:Bool ⊕ Bool=>(Sum.getLeft? s).map inl)
   (fun s:Bool ⊕ Bool=>(Sum.getRight? s).map inr) ?_
  intro l;simp only [rawDec,encodePair,List.map_filterMap]
 refine u7 (qG (qG (qG (yI hE0 hTw) hIt) hDc) h0) ?_
 intro s;have h:=qeb (s.takeWhile id).length [] (s.dropWhile id).tail;have e:ug []++y3 (s.dropWhile id).tail=y3 (s.dropWhile id).tail:=rfl;rw [e] at h;simp only [h,List.nil_append];rw [qe1,qe0,qaY];rfl
end Lib.ve
end
section
namespace Lib.ve
open PEqualNP.Library Lib.qC
private theorem j7 {α β αΓ βΓ:Type} {ea:α→List αΓ} {eb:β→List βΓ}
 {f f':α→β} (h:Q6 ea eb f) (e:∀ a,f a=f' a):
 Q6 ea eb f':=by
 obtain rfl:f=f':=funext e;exact h
private def hdD:Bool→Bool→Bool×Option Bool
 | true,true=>(true,some true)
 | _,_=>(false,none)
private theorem qd5 (l:Q0):
 qD hdD (fun _=>none) false l=[]∧
  qD hdD (fun _=>none) true l=l.takeWhile id:=by
 induction l with
 | nil=>exact ⟨rfl,rfl⟩
 | cons b l ih=>cases b <;> simp [qD,hdD,ih.1,ih.2]
lemma qet:
 Q6 (fun x:Q0=>x) (fun x:Q0=>x) hd:=
 yJ _ _ _ hdD (fun _=>none) true (fun s=>(qd5 s).2.symm)
private def tlD:Bool→Bool→Bool×Option Bool
 | false,_=>(true,none)
 | true,b=>(true,some b)
private theorem qdw (l:Q0):qD tlD (fun _=>none) true l=l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [qD,tlD,ih]
private theorem qda (l:Q0):qD tlD (fun _=>none) false l=l.tail:=by
 cases l with
 | nil=>rfl
 | cons b l=>simp [qD,tlD,qdw]
lemma wV:
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s:Q0=>s.tail):=
 yJ _ _ _ tlD (fun _=>none) false (fun s=>(qda s).symm)
lemma yp (l:Q0):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun _:Q0=>l):=
 yO l
lemma qdi:
 Q6 encodePair (fun x:Q0=>x)
  (fun p:Q0×Q0=>uk p.1 p.2):=
 j7 wc (fun _=>rfl)
lemma zz:
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s:Q0=>(Q9 s).1):=
 j7 (qG wH qdL) (fun _=>rfl)
lemma zA:
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s:Q0=>(Q9 s).2):=
 j7 (qG wH qdM) (fun _=>rfl)
lemma y9 {u v:Q0→Q0}
 (hu:Q6 (fun x:Q0=>x) (fun x:Q0=>x) u)
 (hv:Q6 (fun x:Q0=>x) (fun x:Q0=>x) v):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s=>u s++v s):=
 j7 (qG (yI hu hv) jF) (fun _=>rfl)
lemma qy {u v:Q0→Q0}
 (hu:Q6 (fun x:Q0=>x) (fun x:Q0=>x) u)
 (hv:Q6 (fun x:Q0=>x) (fun x:Q0=>x) v):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s=>qv (u s) (v s)):=
 j7 (qG (yI hu hv) qcH) (fun _=>rfl)
lemma ja {u v:Q0→Q0}
 (hu:Q6 (fun x:Q0=>x) (fun x:Q0=>x) u)
 (hv:Q6 (fun x:Q0=>x) (fun x:Q0=>x) v):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s=>uk (u s) (v s)):=
 j7 (qG (yI hu hv) qdi) (fun _=>rfl)
lemma qbX {f a b:Q0→Q0}
 (hf:Q6 (fun x:Q0=>x) (fun x:Q0=>x) f)
 (ha:Q6 (fun x:Q0=>x) (fun x:Q0=>x) a)
 (hb:Q6 (fun x:Q0=>x) (fun x:Q0=>x) b):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s=>sel (f s) (a s) (b s)):=by
 have h1:=qG (yI hf ha) jk;have h2:=qG (yI hf hb) qan;refine j7 (y9 h1 h2) ?_
 intro s;by_cases h:f s=[] <;> simp [sel,h]
lemma wG {g cnt arg:Q0→Q0}
 (hg:Q6 (fun x:Q0=>x) (fun x:Q0=>x) g)
 (hgl:∀ s,(g s).length≤ s.length)
 (hcnt:Q6 (fun x:Q0=>x) (fun x:Q0=>x) cnt)
 (harg:Q6 (fun x:Q0=>x) (fun x:Q0=>x) arg):
 Q6 (fun x:Q0=>x) (fun x:Q0=>x)
  (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 have hI:Q6 encodePair (fun x:Q0=>x)
  (fun p:Q0×Q0=>g^[p.2.length] p.1):=
  jE.uB g c 0 (fun y=>by simpa using hgl y)
 exact j7 (qG (yI harg hcnt) hI) (fun _=>rfl)
end Lib.ve
end
section
namespace Lib.ve
open PEqualNP.Library Lib.qC
private theorem qcF {f f':Q0→Q0} (h:Lib.qF f) (e:∀ a,f a=f' a):Lib.qF f':=by obtain rfl:f=f':=funext e; exact h
lemma qbV {f:Q0→Q0} (hf:Lib.qF f):Lib.qF (fun y=>hd (f y)):=qG hf qet
lemma j6 {f:Q0→Q0} (hf:Lib.qF f):Lib.qF (fun y=>(f y).tail):=qG hf wV
lemma qZ {f:Q0→Q0} (hf:Lib.qF f):
 Lib.qF (fun y=>(Q9 (f y)).1):=qG (g:=fun s=>(Q9 s).1) hf zz
lemma qo {f:Q0→Q0} (hf:Lib.qF f):
 Lib.qF (fun y=>(Q9 (f y)).2):=qG (g:=fun s=>(Q9 s).2) hf zA
lemma yB (b:Bool) {f:Q0→Q0} (hf:Lib.qF f):
 Lib.qF (fun y=>b::f y):=
 qcF (y9 (yp [b]) hf) (fun _=>rfl)
end Lib.ve
end
section
namespace Lib.j4
open PEqualNP.Library Lib.qC Lib.ve
lemma zk {f f':Q0→Q0} (h:Lib.qF f) (e:∀ a,f a=f' a):
 Lib.qF f':=by
 obtain rfl:f=f':=funext e;exact h
lemma u9 {g cnt arg:Q0→Q0} (hg:Lib.qF g)
 (m:Q0→ℕ) (a:ℕ) (hm:∀ y,m (g y)≤ m y)
 (hgl:∀ y,(g y).length≤y.length+m y) (ha:∀ y,m y≤a * y.length+a)
 (hcnt:Lib.qF cnt) (harg:Lib.qF arg):
 Lib.qF (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 exact zk (qG (yI harg hcnt) (jE.jw g c m a hm hgl ha))
  (fun _=>rfl)
def tk (p w:Q0):Q0:=(Q9 (uk p [true]++false::w)).1
lemma qa1 (p w:Q0):tk p w=w.take p.length:=by
 have h1:(uk p [true]++false::w).takeWhile id=un p.length:=by simp [uk,un]
 have h2:(uk p [true]++false::w).dropWhile id=false::w:=by simp [uk,un]
 simp [tk,Q9,h1,h2,un]
lemma qaI (p w:Q0):(tk p w).length≤p.length:=by rw [qa1,List.length_take];exact Nat.min_le_left _ _
lemma qa8 {p w:Q0→Q0} (hp:Lib.qF p) (hw:Lib.qF w):
 Lib.qF (fun s=>tk (p s) (w s)):=
 qZ (y9 (ja hp (yp [true])) (yB false hw))
def uL (f:Q0→Q0) (y:Q0):Q0:=qv (Q9 y).1 (qv (Q9 (Q9 y).2).1.tail (qv (Q9 (Q9 (Q9 y).2).2).1 (tk (Q9 y).1 (f (qv (Q9 (Q9 y).2).1.tail (Q9 (Q9 (Q9 y).2).2).1))++(Q9 (Q9 (Q9 y).2).2).2)))
lemma qcG {f:Q0→Q0} (hf:Lib.qF f):Lib.qF (uL f):=by have h1:Lib.qF (fun y=>(Q9 y).1):=zz;have h2:Lib.qF (fun y=>(Q9 y).2):=zA;have hr:=j6 (qZ h2);have h3:=qo h2;have h0:=qZ h3;have h4:=qo h3;exact qy h1 (qy hr (qy h0 (y9 (qa8 h1 (qG (qy hr h0) hf)) h4)))
lemma qbI (f:Q0→Q0) (pad r arg acc:Q0):
 uL f (qv pad (qv r (qv arg acc)))=
  qv pad (qv r.tail (qv arg (tk pad (f (qv r.tail arg))++acc))):=by
 simp only [uL,qk]
lemma qaT (f:Q0→Q0) (y:Q0):
 (Q9 (uL f y)).1.length+3≤(Q9 y).1.length+3:=by
 simp only [uL,qk];exact le_rfl
lemma qbp (f:Q0→Q0) (y:Q0):
 (uL f y).length≤y.length+((Q9 y).1.length+3):=by
 have h1:=yE y;have h2:=yE (Q9 y).2;have h3:=yE (Q9 (Q9 y).2).2
 have h4:=qaI (Q9 y).1 (f (qv (Q9 (Q9 y).2).1.tail
       (Q9 (Q9 (Q9 y).2).2).1))
 have h5:(Q9 (Q9 y).2).1.tail.length≤(Q9 (Q9 y).2).1.length:=by simp
 simp only [uL,zW,List.length_append];omega
lemma qck (f:Q0→Q0) (pad arg:Q0) (n:ℕ)
 (hpad:∀ i<n,(f (qv (un i) arg)).length≤pad.length) (acc:Q0):
 (uL f)^[n] (qv pad (qv (un n) (qv arg acc)))=
   qv pad (qv [] (qv arg
    ((List.range n).flatMap (fun i=>f (qv (un i) arg))++acc))):=by
 induction n generalizing acc with
 | zero=>simp
 | succ n ih=>
   rw [ze,qbI,uT,List.tail_cons,qa1,
    vo (hpad n (by omega)),ih (fun i hi=>hpad i (by omega)),
    zP,List.flatMap_append]
   simp
lemma ka {f cnt arg:Q0→Q0} (hf:Lib.qF f) (hcnt:Lib.qF cnt)
 (harg:Lib.qF arg):
 Lib.qF (fun s=>(List.range (cnt s).length).flatMap fun i=>f (qv (un i) (arg s))):=by
 obtain ⟨P,hP⟩:=yV f hf
 have h1:Lib.qF (fun s=>List.replicate (P.eval (qv (cnt s) (arg s)).length) true):=qG (qy hcnt harg) (Lib.qes P)
 have hun:Lib.qF (fun s=>uk (cnt s) [true]):=ja hcnt (yp [true]);have h0:=qy h1 (qy hun (qy harg (yp [])))
 have hit:=u9 (qcG hf) (fun y=>(Q9 y).1.length+3) 3
  (qaT f) (qbp f)
  (fun y=>by have:=yE y; omega) hcnt h0
 have h2:=qo (qo (qo hit));refine zk h2 (fun s=>?_)
 have e:uk (cnt s) [true]=un (cnt s).length:=by simp [uk]
 have hb:∀ i<(cnt s).length,(f (qv (un i) (arg s))).length≤
  (List.replicate (P.eval (qv (cnt s) (arg s)).length) true).length:=by
  intro i hi;rw [List.length_replicate];refine (hP _).trans (y7 P ?_)
  rw [zW,zW,za];omega
 show (Q9 (Q9 (Q9 ((uL f)^[(cnt s).length] (qv _ (qv (uk (cnt s) [true]) (qv (arg s) []))))).2).2).2=_;rw [e,qck f _ (arg s) (cnt s).length hb,qk,qk,qk];simp
end Lib.j4
end
namespace Lib.R
open PEqualNP.Library Lib.qC Lib.ve Lib.j4
def zn (v:Q1):Q0:=v.flatMap (fun a=>false::un a)
def dbl (w:Q0):Q0:=w.flatMap (fun b=>[true,b])
def zR (S:Q2):Q0:=S.flatMap (fun v=>false::dbl (zn v))
def yx:Q0→ℕ×Q1
 | []=>(0,[])
 | true::r=>((yx r).1+1,(yx r).2)
 | false::r=>(0,(yx r).1::(yx r).2)
def vK (w:Q0):Q1:=(yx w).2
def dr:Q0→Q0×List (Q0)
 | []=>([],[])
 | false::r=>(([]:Q0),(dr r).1::(dr r).2)
 | true::b::r=>(b::(dr r).1,(dr r).2)
 | [true]=>([],[])
def ko (w:Q0):Q2:=(dr w).2.map vK
@[local simp] theorem qfs:zn []=[]:=rfl
@[local simp] theorem wu (a:ℕ) (v:Q1):zn (a::v)=false::(un a++zn v):=rfl
@[local simp] theorem qft (v w:Q1):zn (v++w)=zn v++zn w:=by simp [zn]
@[local simp] theorem qfp:dbl []=[]:=rfl
@[local simp] theorem qb3 (b:Bool) (w:Q0):dbl (b::w)=true::b::dbl w:=rfl
@[local simp] theorem qfq:zR []=[]:=rfl
@[local simp] theorem ju (v:Q1) (S:Q2):
   zR (v::S)=false::(dbl (zn v)++zR S):=rfl
@[local simp] theorem qfr (S T:Q2):zR (S++T)=zR S++zR T:=by simp [zR]
lemma qdQ (a:ℕ) (w:Q0):yx (un a++w)=((yx w).1+a,(yx w).2):=by
 induction a with
 | zero=>rfl
 | succ a ih=>simp only [uT,List.cons_append,yx,ih,Nat.add_assoc]
lemma zU (v:Q1):vK (zn v)=v:=by
 have:∀ v,yx (zn v)=(0,v):=by
  intro v; induction v with
  | nil=>rfl
  | cons a v ih=>simp [yx,qdQ,ih]
 simp [vK,this]
lemma qdP (w:Q0):un (yx w).1++zn (yx w).2=w:=by
 induction w with
 | nil=>rfl
 | cons b w ih=>cases b <;> simp [yx,uT,ih]
lemma qba (w:Q0):zn (vK w)=w.dropWhile id:=by
 induction w with
 | nil=>rfl
 | cons b w ih=>
   cases b
   · simpa [vK,yx] using qdP w
   · simpa [vK,yx] using ih
lemma qdO (x w:Q0):dr (dbl x++w)=(x++(dr w).1,(dr w).2):=by
 induction x with
 | nil=>rfl
 | cons b x ih=>simp [dr,ih]
lemma yl (S:Q2):ko (zR S)=S:=by
 have:∀ S,dr (zR S)=([],S.map zn):=by
  intro S; induction S with
  | nil=>rfl
  | cons v S ih=>simp [dr,qdO,ih]
 simp [ko,this,Function.comp_def,zU]
def qi (f:Q0→ℕ):Prop:=Lib.qF (fun s=>un (f s))
def qS (f:Q0→Q1):Prop:=Lib.qF (fun s=>zn (f s))
def LLR (f:Q0→Q2):Prop:=Lib.qF (fun s=>zR (f s))
lemma wq {Q:Type} [Fintype Q] (δ:Q→Bool→Q×Option Bool) (fin:Q→Option Bool)
 (q:Q):Lib.qF (qD δ fin q):=yJ _ _ _ δ fin q (fun _=>rfl)
lemma qcI {Q:Type} [Fintype Q] (δ:Q→Bool→Q×Option Bool×Option Bool)
 (fin:Q→Option Bool) (q:Q):Lib.qF (z6 δ fin q):=
 uA _ _ _ δ fin q (fun _=>rfl)
lemma qbb (φ:Bool→Option Bool):Lib.qF (fun w=>w.filterMap φ):=
 zk (wq (fun (_:Unit) b=>((),φ b)) (fun _=>none) ()) (fun w=>by
  induction w with
  | nil=>rfl
  | cons b l ih=>simp only [qD]; rw [ih]; cases h:φ b <;> simp [h])
lemma qex {Q:Type} (δ:Q→Bool→Q×Option Bool) (q:Q) (l:Q0):
 (qD δ (fun _=>none) q l).length≤l.length:=by
 induction l generalizing q with
 | nil=>simp [qD]
 | cons a l ih=>
   simp only [qD,List.length_append,qI];have:=ih (δ q a).1
   cases (δ q a).2 <;> simp <;> omega
lemma qbd {Q:Type} (δ:Q→Bool→Q×Option Bool) (fin:Q→Option Bool) (q q':Q)
 (h1:δ q true=(q',none)) (h2:∀ b,δ q' b=(q,none)) (x y:Q0):
 qD δ fin q (dbl x++y)=qD δ fin q y:=by
 induction x with
 | nil=>rfl
 | cons b x ih=>simp only [qb3,List.cons_append,qD,h1,h2]; simpa using ih
lemma qa9:Lib.qF dbl:=
 zk (qcI (fun (_:Unit) b=>((),some true,some b)) (fun _=>none) ()) (fun w=>by
  induction w with
  | nil=>rfl
  | cons b l ih=>simp only [z6]; rw [ih]; rfl)
def wt:Bool→Bool→Bool×Option Bool
 | false,true=>(false,none)
 | false,false=>(true,some false)
 | true,b=>(true,some b)
lemma qbY:Lib.qF (fun l=>l.dropWhile id):=by
 have ht:∀ l,qD wt (fun _=>none) true l=l:=by
  intro l; induction l with
  | nil=>rfl
  | cons b l ih=>simp [qD,wt,ih]
 refine zk (wq wt (fun _=>none) false) (fun l=>?_)
 induction l with
 | nil=>rfl
 | cons b l ih=>cases b <;> simp [qD,wt,ih,ht]
lemma qbe (x:ℕ) (w:Q0):Q9 (un x++false::w)=(w.take x,w.drop x):=by
 have h1:(un x++false::w).takeWhile id=un x:=by simp [un]
 have h2:(un x++false::w).dropWhile id=false::w:=by simp [un]
 simp [Q9,h1,h2]
lemma qeB (l:Q0):hd l=un (l.takeWhile id).length:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>
   cases b
   · simp [hd,un]
   · simp only [hd,List.takeWhile_cons,id_eq,↓reduceIte,qI,un,List.replicate_succ] at ih ⊢;exact congrArg (true::·) ih
lemma qcJ {α:Type} (l:List α) (i:ℕ) (d:α):(l.drop i).headD d=l.getD i d:=by
 induction l generalizing i with
 | nil=>simp
 | cons a l ih=>cases i <;> simp
lemma qb4 {α:Type} (E:List α→Q0) (f:Q0→Q0)
 (hf:∀ S,f (E S)=E S.tail) (n:ℕ) (S:List α):f^[n] (E S)=E (S.drop n):=by
 induction n generalizing S with
 | zero=>rfl
 | succ n ih=>rw [ze,hf,ih,List.drop_tail]
def jb (g:Q0→Q0) (y:Q0):Q0:=qv (Q9 y).1 (tk (Q9 y).1 (g (Q9 y).2))
lemma qeu (g:Q0→Q0) (y:Q0):
 (Q9 (jb g y)).1.length+1≤(Q9 y).1.length+1:=by
 simp [jb,qk]
lemma qev (g:Q0→Q0) (y:Q0):
 (jb g y).length≤y.length+((Q9 y).1.length+1):=by
 have h1:=yE y;have h2:=qaI (Q9 y).1 (g (Q9 y).2);simp only [jb,zW]; omega
lemma qew (y:Q0):(Q9 y).1.length+1≤1 * y.length+1:=by have:=yE y; omega
lemma qdN (g:Q0→Q0) (pad y:Q0) (n:ℕ)
 (h:∀ i≤n,(g^[i] y).length≤pad.length):
 (jb g)^[n] (qv pad y)=qv pad (g^[n] y):=by
 induction n with
 | zero=>rfl
 | succ n ih=>
   rw [qM (jb g),ih (fun i hi=>h i (by omega)),
    qM g]
   simp only [jb,qk,qa1];have:=h (n+1) le_rfl;rw [qM] at this;rw [vo this]
lemma qaP {g cnt arg:Q0→Q0} (hg:Lib.qF g) (hcnt:Lib.qF cnt)
 (harg:Lib.qF arg) (P:Q5)
 (hb:∀ s,∀ i≤(cnt s).length,(g^[i] (arg s)).length≤P.eval s.length):
 Lib.qF (fun s=>g^[(cnt s).length] (arg s)):=by
 have hG:Lib.qF (jb g):=qy zz (qa8 zz (qG zA hg))
 have hit:=u9 hG (fun y=>(Q9 y).1.length+1) 1 (qeu g) (qev g) qew
  hcnt (qy (Lib.qes P) harg)
 exact zk (qo hit) (fun s=>by rw [qdN g _ _ _ (fun i hi=>by simpa using hb s i hi),qk])
lemma y6 {F init cnt:Q0→Q0} (hF:Lib.qF F) (hi:Lib.qF init)
 (hc:Lib.qF cnt) (P:Q5)
 (hb:∀ s,∀ i≤(cnt s).length,
   ((fun a=>F (qv a s))^[i] (init s)).length≤P.eval s.length):
 Lib.qF (fun s=>(fun a=>F (qv a s))^[(cnt s).length] (init s)):=by
 have e:∀ s i a,(fun y=>qv (F y) (Q9 y).2)^[i] (qv a s)=
  qv ((fun a=>F (qv a s))^[i] a) s:=by
  intro s i; induction i with
  | zero=>intro a; rfl
  | succ i ih=>intro a; simp only [ze,qk,ih]
 have h:=qaP (qy hF zA) hc (qy hi yP)
  (Polynomial.C 2 * P+Polynomial.X+Polynomial.C 1) (fun s i hi=>by rw [e,zW]; have:=hb s i hi;simp only [zO,z9,vT,Polynomial.eval_X];omega)
 exact zk (qZ h) (fun s=>by rw [e,qk])
lemma qdT (F:Q0→Q0) (φ:ℕ→ℕ) (s:Q0)
 (hF:∀ x,F (qv (un x) s)=un (φ x)):
 ∀ i x,(fun a=>F (qv a s))^[i] (un x)=un (φ^[i] x):=by
 intro i; induction i with
 | zero=>intro x; rfl
 | succ i ih=>intro x; simp only [ze,hF,ih]
lemma jc {φ:Q0→ℕ→ℕ} {x0 n:Q0→ℕ}
 (hφ:qi (fun t=>φ (Q9 t).2 (Q9 t).1.length)) (hx:qi x0) (hn:qi n)
 (P:Q5) (hb:∀ s,∀ i≤n s,(φ s)^[i] (x0 s)≤P.eval s.length):
 qi (fun s=>(φ s)^[n s] (x0 s)):=by
 have e:∀ s i x,(fun a=>un (φ (Q9 (qv a s)).2 (Q9 (qv a s)).1.length))^[i]
  (un x)=un ((φ s)^[i] x):=fun s=>
  qdT (fun t=>un (φ (Q9 t).2 (Q9 t).1.length)) (φ s) s
   (fun x=>by simp only [qk,za])
 have h:=y6 (F:=fun t=>un (φ (Q9 t).2 (Q9 t).1.length))
  (init:=fun s=>un (x0 s)) (cnt:=fun s=>un (n s)) hφ hx hn P
  (fun s i hi=>by rw [e,za]; exact hb s i (by simpa using hi))
 exact zk h (fun s=>by rw [za,e])
lemma qb1 (C:ℕ→Prop) [DecidablePred C] (i:ℕ):
 (fun q=>if C q then q else q+1)^[i] 0≤ i:=by
 induction i with
 | zero=>exact le_rfl
 | succ i ih=>rw [qM]; split_ifs <;> omega
lemma qb2 (C:ℕ→Prop) [DecidablePred C] (m:ℕ) (hC:∀ q,C q↔m<q+1) (i:ℕ):
 (fun q=>if C q then q else q+1)^[i] 0=min i m:=by
 induction i with
 | zero=>simp
 | succ i ih=>
   rw [qM,ih];split_ifs with h
   · have:=(hC _).1 h; omega
   · have:=mt (hC _).2 h; omega
lemma w4 {a:Q0→ℕ} (ha:qi a):∃ P:Q5,∀ s,a s≤P.eval s.length:=by obtain ⟨P,hP⟩:=yV _ ha;exact ⟨P,fun s=>by simpa using hP s⟩
lemma qb5 (n:ℕ) (x y:Q0):sel (un n) x y=if n=0 then x else y:=by cases n <;> simp [sel,un]
lemma qb (k:ℕ):qi (fun _=>k):=yp (un k)
lemma yY {p:Q0→Q0} (hp:Lib.qF p):qi (fun s=>(p s).length):=zk (ja hp (yp [true])) (fun s=>by simp [uk])
lemma q9 {a b:Q0→ℕ} (ha:qi a) (hb:qi b):qi (fun s=>a s+b s):=zk (y9 ha hb) (fun s=>by simp only [un,List.replicate_add])
lemma yj {a b:Q0→ℕ} (ha:qi a) (hb:qi b):qi (fun s=>a s-b s):=
 zk (qo (y9 hb (yB false ha))) (fun s=>by rw [qbe]; simp [un])
lemma vn {a b:Q0→ℕ} (ha:qi a) (hb:qi b):qi (fun s=>a s * b s):=zk (ja ha hb) (fun s=>by simp [uk])
lemma qb0 {a b:Q0→ℕ} {x y:Q0→Q0} (ha:qi a) (hb:qi b)
 (hx:Lib.qF x) (hy:Lib.qF y):Lib.qF (fun s=>if a s<b s then x s else y s):=
 zk (qbX (yj hb ha) hy hx) (fun s=>by
  dsimp only; rw [qb5]; by_cases h:a s<b s
  · simp only [h,↓reduceIte,show ¬ b s-a s=0 by omega,↓reduceIte]
  · simp only [h,↓reduceIte,show b s-a s=0 by omega,↓reduceIte])
lemma qbZ {a b:Q0→ℕ} {x y:Q0→Q0} (ha:qi a) (hb:qi b)
 (hx:Lib.qF x) (hy:Lib.qF y):Lib.qF (fun s=>if a s=b s then x s else y s):=
 zk (qbX (q9 (yj ha hb) (yj hb ha)) hx hy) (fun s=>by
  dsimp only; rw [qb5]; by_cases h:a s=b s
  · simp only [h,↓reduceIte,show b s-b s+(b s-b s)=0 by omega]
  · simp only [h,↓reduceIte,show ¬ a s-b s+(b s-a s)=0 by omega])
lemma kz {a b x y:Q0→ℕ} (ha:qi a) (hb:qi b) (hx:qi x) (hy:qi y):
 qi (fun s=>if a s<b s then x s else y s):=
 zk (qb0 ha hb hx hy) (fun s=>by dsimp only; split_ifs <;> rfl)
lemma z5 {a b x y:Q0→ℕ} (ha:qi a) (hb:qi b) (hx:qi x) (hy:qi y):
 qi (fun s=>if a s=b s then x s else y s):=
 zk (qbZ ha hb hx hy) (fun s=>by dsimp only; split_ifs <;> rfl)
lemma qs:qi (fun t=>(Q9 t).1.length):=yY zz
lemma qz {a:Q0→ℕ} (ha:qi a):qi (fun t=>a (Q9 t).2):=by
 unfold qi at *
 exact qG (f:=fun t=>(Q9 t).2) (g:=fun s=>un (a s)) zA ha
lemma uo {a b:Q0→ℕ} (ha:qi a) (hb:qi b):qi (fun s=>a s / b s):=by
 obtain ⟨P,hP⟩:=w4 ha
 have hφ:=kz (qz ha) (vn (q9 qs (qb 1)) (qz hb)) qs
  (q9 qs (qb 1))
 have h:=jc (φ:=fun s q=>if a s<(q+1) * b s then q else q+1) hφ
  (qb 0) ha P (fun s i hi=>(qb1 _ i).trans (hi.trans (hP s)))
 refine zk (z5 hb (qb 0) (qb 0) h) (fun s=>?_)
 dsimp only;by_cases h0:b s=0
 · simp [h0]
 · simp only [h0,↓reduceIte]
   rw [qb2 (fun q=>a s<(q+1) * b s) (a s / b s)
    (fun q=>(Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero h0)).symm) (a s),
    min_eq_right (Nat.div_le_self _ _)]
lemma qbt {a b:Q0→ℕ} (ha:qi a) (hb:qi b):qi (fun s=>a s % b s):=zk (yj ha (vn hb (uo ha hb))) (fun s=>by dsimp only; rw [Nat.mod_eq_sub_mul_div])
lemma qbc (i x:ℕ):(fun x=>x / 2)^[i] x=x / 2 ^ i:=by
 induction i generalizing x with
 | zero=>simp
 | succ i ih=>rw [ze,ih,Nat.div_div_eq_div_mul,pow_succ']
lemma qaB {a b:Q0→ℕ} (ha:qi a) (hb:qi b):
 qi (fun s=>a s / 2 ^ b s):=by
 obtain ⟨P,hP⟩:=w4 ha
 have h:=jc (φ:=fun _ x=>x / 2) (uo qs (qb 2)) ha hb P
  (fun s i _=>by rw [qbc]; exact (Nat.div_le_self _ _).trans (hP s))
 exact zk h (fun s=>by dsimp only; rw [qbc])
lemma qaG {a:Q0→ℕ} (ha:qi a):qi (fun s=>(a s).log2):=by
 obtain ⟨P,hP⟩:=w4 ha
 have hφ:=kz (qaB (qz ha) (q9 qs (qb 1))) (qb 1)
  qs (q9 qs (qb 1))
 have h:=jc (φ:=fun s q=>if a s / 2 ^ (q+1)<1 then q else q+1) hφ
  (qb 0) ha P (fun s i hi=>(qb1 _ i).trans (hi.trans (hP s)))
 refine zk h (fun s=>?_)
 dsimp only
 rw [qb2 (fun q=>a s / 2 ^ (q+1)<1) (a s).log2 (fun q=>?_) (a s),
  min_eq_right (Nat.log2_le_self _)]
 rcases Nat.eq_zero_or_pos (a s) with h0|h0
 · simp [h0]
 · rw [Nat.div_lt_iff_lt_mul (by positivity),one_mul,Nat.log2_lt h0.ne']
lemma qbu {a b:Q0→ℕ} (ha:qi a) (hb:qi b):
 qi (fun s=>if (a s).testBit (b s) then 1 else 0):=
 zk (qbt (qaB ha hb) (qb 2)) (fun s=>by dsimp only; rw [Nat.testBit_eq_decide_div_mod_eq];rcases Nat.mod_two_eq_zero_or_one (a s / 2 ^ b s) with h|h <;> simp [h])
lemma qcK (i:ℕ):(fun x=>x+x)^[i] 1=2 ^ i:=by
 induction i with
 | zero=>rfl
 | succ i ih=>rw [qM,ih,pow_succ]; omega
lemma qcZ {b:Q0→ℕ} (hb:qi b) (P:Q5)
 (hP:∀ s,2 ^ b s≤P.eval s.length):qi (fun s=>2 ^ b s):=by
 have h:=jc (φ:=fun _ x=>x+x) (q9 qs qs) (qb 1) hb P
  (fun s i hi=>by rw [qcK]; exact (Nat.pow_le_pow_right (by norm_num) hi).trans (hP s))
 exact zk h (fun s=>by dsimp only; rw [qcK])
lemma jG {a b:Q0→ℕ} {x y:Q0→Q0} (ha:qi a) (hb:qi b)
 (hx:Lib.qF x) (hy:Lib.qF y):Lib.qF (fun s=>if a s<b s then x s else y s):=
 qb0 ha hb hx hy
lemma yQ {a b:Q0→ℕ} {x y:Q0→Q0} (ha:qi a) (hb:qi b)
 (hx:Lib.qF x) (hy:Lib.qF y):Lib.qF (fun s=>if a s=b s then x s else y s):=
 qbZ ha hb hx hy
lemma qdt {p:Q0→Q0} {k:Q0→ℕ} (hp:Lib.qF p) (hk:qi k):
 qi (fun s=>if (p s).getD (k s) false then 1 else 0):=by
 have h:=qG (qa8 (yp [true]) (qo (y9 hk (yB false hp))))
  (qbb (fun b=>if b then some true else none))
 refine zk h (fun s=>?_)
 simp only [qa1,qbe,List.length_singleton];rw [qf,← List.head?_drop]
 rcases (p s).drop (k s) with _|⟨_|_,l⟩ <;> simp [un]
lemma qac {p:Q0→Q0} {k:Q0→ℕ} (hp:Lib.qF p) (hk:qi k):
 qi (fun s=>(((p s).drop (k s)).takeWhile id).length):=
 zk (qbV (qo (y9 hk (yB false hp)))) (fun s=>by rw [qbe]; exact qeB _)
lemma vv {p:Q0→Q0} (hp:Lib.qF p):qS (fun s=>vK (p s)):=zk (qG hp qbY) (fun _=>(qba _).symm)
lemma jV:qS (fun _=>[]):=yp []
lemma qT {a:Q0→ℕ} (ha:qi a):qS (fun s=>[a s]):=zk (yB false ha) (fun s=>by simp)
lemma zI {v w:Q0→Q1} (hv:qS v) (hw:qS w):
 qS (fun s=>v s++w s):=
 zk (y9 hv hw) (fun s=>by simp)
lemma qdR (a:ℕ) (w:Q0):(un a++w).dropWhile id=w.dropWhile id:=by
 induction a with
 | zero=>rfl
 | succ a ih=>simpa [uT] using ih
lemma qdV (v:Q1):(zn v).takeWhile id=[]:=by cases v <;> rfl
lemma qdU (v:Q1):((zn v).tail).dropWhile id=zn v.tail:=by
 cases v with
 | nil=>rfl
 | cons a v=>simp only [wu,List.tail_cons,qdR]; cases v <;> rfl
lemma qdS (w:Q1):hd (zn w).tail=un (w.headD 0):=by
 cases w with
 | nil=>rfl
 | cons a w=>simp only [wu,List.tail_cons,hd,List.headD_cons];rw [List.takeWhile_append_of_pos (by simp [un]),qdV,qX]
lemma qO {v:Q0→Q1} {i:Q0→ℕ} (hv:qS v) (hi:qi i):
 qi (fun s=>(v s).getD (i s) 0):=by
 have h:=wG (g:=fun y=>(y.tail).dropWhile id) (qG wV qbY)
  (fun y=>(List.IsSuffix.length_le (List.dropWhile_suffix (l:=y.tail) id)).trans (by simp))
  hi hv
 exact zk (qbV (j6 h)) (fun s=>by rw [za,qb4 zn (fun y=>(y.tail).dropWhile id) qdU,qdS,qcJ])
lemma vg {v:Q0→Q1} (hv:qS v):qi (fun s=>(v s).length):=by
 have e:∀ v:Q1,(zn v).filterMap (fun b=>if b then none else some true)=un v.length:=by
  intro v; induction v with
  | nil=>rfl
  | cons a v ih=>simp only [wu,List.filterMap_cons,List.filterMap_append,ih];simp [un,List.filterMap_replicate_of_none,List.replicate_succ]
 exact zk (qG hv (qbb _)) (fun s=>e _)
lemma zJ {v:Q0→Q1} (hv:qS v):qi (fun s=>(v s).sum):=by
 have e:∀ v:Q1,(zn v).filterMap (fun b=>if b then some true else none)=un v.sum:=by
  intro v; induction v with
  | nil=>rfl
  | cons a v ih=>simp only [wu,List.filterMap_cons,List.filterMap_append,ih];simp [un]
 exact zk (qG hv (qbb _)) (fun s=>e _)
lemma u1 {A:Q0→Q0} {n:Q0→ℕ} {G:ℕ→Q0→ℕ}
 (hA:Lib.qF A) (hn:qi n) (hG:qi (fun t=>G (Q9 t).1.length (Q9 t).2)):
 qS (fun s=>(List.range (n s)).map (fun i=>G i (A s))):=
 zk (ka (yB false hG) hn hA) (fun s=>by simp [zn,List.flatMap_map,qk])
lemma qdb {A:Q0→Q0} {n:Q0→ℕ} {H:ℕ→Q0→Q1}
 (hA:Lib.qF A) (hn:qi n) (hH:qS (fun t=>H (Q9 t).1.length (Q9 t).2)):
 qS (fun s=>(List.range (n s)).flatMap (fun i=>H i (A s))):=
 zk (ka hH hn hA) (fun s=>by simp [zn,List.flatMap_assoc,qk])
def k3:Bool→Bool→Bool×Option Bool
 | false,true=>(false,none)
 | false,false=>(true,none)
 | true,true=>(false,some true)
 | true,false=>(true,some false)
def jt (q:Bool):Option Bool:=if q then some false else none
lemma qcb {v:Q0→Q1} (hv:qS v):
 Lib.qF (fun s=>(v s).map (fun a=>decide (a≠0))):=by
 have hu:∀ (a:ℕ) w,qD k3 jt false (un a++w)=qD k3 jt false w:=by
  intro a w; induction a with
  | zero=>rfl
  | succ a ih=>simpa [uT,qD,k3] using ih
 have e:∀ v:Q1,qD k3 jt false (zn v)=v.map (fun a=>decide (a≠0))∧
  qD k3 jt true (zn v)=false::v.map (fun a=>decide (a≠0)):=by
  intro v; induction v with
  | nil=>exact ⟨rfl,rfl⟩
  | cons a v ih=>
    have key:qD k3 jt true (un a++zn v)=
     decide (a≠0)::v.map (fun a=>decide (a≠0)):=by
     cases a with
     | zero=>exact ih.2
     | succ a=>simp [uT,qD,k3,hu,ih.1]
    simp [qD,k3,key]
 exact zk (qG hv (wq k3 jt false)) (fun s=>(e _).1)
def uW:Bool×Bool×Bool→Bool→(Bool×Bool×Bool)×Option Bool×Option Bool
 | (_,false,_),false=>((true,false,true),some false,none)
 | (r,false,d),true=>((r,true,d),none,none)
 | (false,true,_),_=>((false,false,false),none,none)
 | (true,true,d),b=>if d&&b then ((true,false,true),none,none) else ((true,false,false),some true,some b)
def w5 (d:Bool) (x:Q0):Q0:=if d then x.dropWhile id else x
lemma qez (w:Q0):∀ d,z6 uW (fun _=>none) (true,false,d) w=
 dbl (w5 d (dr w).1)++zR ((dr w).2.map vK):=by
 induction w using dr.induct with
 | case1=>intro d; cases d <;> rfl
 | case2 r ih=>intro d; simp [z6,uW,dr,ih,w5,qba]
 | case3 b r ih=>intro d; cases d <;> cases b <;> simp [z6,uW,dr,ih,w5]
 | case4=>intro d; cases d <;> rfl
lemma qey (w:Q0):z6 uW (fun _=>none) (false,false,false) w=
 zR (ko w):=by
 induction w using dr.induct with
 | case1=>rfl
 | case2 r ih=>simp [z6,uW,dr,ko,qez,w5,qba]
 | case3 b r ih=>simpa [z6,uW,dr,ko] using ih
 | case4=>rfl
lemma kZ {p:Q0→Q0} (hp:Lib.qF p):LLR (fun s=>ko (p s)):=zk (qG hp (qcI uW (fun _=>none) (false,false,false))) (fun _=>qey _)
lemma uj:LLR (fun _=>[]):=yp []
lemma uK {v:Q0→Q1} (hv:qS v):LLR (fun s=>[v s]):=zk (yB false (qG hv qa9)) (fun s=>by simp)
def uv:Bool×Bool→Bool→(Bool×Bool)×Option Bool
 | (false,false),false=>((true,false),some false)
 | (false,false),true=>((false,true),none)
 | (false,true),_=>((false,false),none)
 | (true,_),b=>((true,false),some b)
def uw:Bool×Bool→Bool→(Bool×Bool)×Option Bool
 | (false,false),false=>((true,false),none)
 | (false,false),true=>((false,true),none)
 | (false,true),b=>((false,false),some b)
 | (true,_),_=>((true,false),none)
lemma qeA (S:Q2):
 qD uv (fun _=>none) (false,false) (zR S).tail=zR S.tail:=by
 have hc:∀ x l,qD uv (fun _=>none) (true,x) l=l:=by
  intro x l; induction l generalizing x with
  | nil=>rfl
  | cons b l ih=>simp [qD,uv,ih]
 cases S with
 | nil=>rfl
 | cons v S=>
   simp only [ju,List.tail_cons];rw [qbd uv _ (false,false) (false,true) rfl (fun _=>rfl)]
   cases S with
   | nil=>rfl
   | cons w S=>simp [qD,uv,hc]
lemma qeC (S:Q2):
 qD uw (fun _=>none) (false,false) (zR S).tail=zn (S.headD []):=by
 have hd0:∀ x l,qD uw (fun _=>none) (true,x) l=[]:=by
  intro x l; induction l generalizing x with
  | nil=>rfl
  | cons b l ih=>simp [qD,uw,ih]
 have hb:∀ x y,qD uw (fun _=>none) (false,false) (dbl x++y)=
  x++qD uw (fun _=>none) (false,false) y:=by
  intro x y; induction x with
  | nil=>rfl
  | cons b x ih=>simp [qD,uw,ih]
 cases S with
 | nil=>rfl
 | cons v S=>
   simp only [ju,List.tail_cons,List.headD_cons];rw [hb]
   cases S with
   | nil=>simp [qD]
   | cons w S=>simp [qD,uw,hd0]
lemma vw {S:Q0→Q2} {j:Q0→ℕ} (hS:LLR S) (hj:qi j):
 qS (fun s=>(S s).getD (j s) []):=by
 have h:=wG (g:=fun y=>qD uv (fun _=>none) (false,false) y.tail)
  (qG wV (wq uv _ (false,false)))
  (fun y=>(qex _ _ _).trans (by simp)) hj hS
 exact zk (qG (j6 h) (wq uw (fun _=>none) (false,false))) (fun s=>by
  rw [za,qb4 zR (fun y=>qD uv (fun _=>none) (false,false) y.tail)
   qeA,qeC,qcJ])
def w3:Bool→Bool→Bool×Option Bool
 | false,false=>(false,some true)
 | false,true=>(true,none)
 | true,_=>(false,none)
lemma vr {S:Q0→Q2} (hS:LLR S):qi (fun s=>(S s).length):=by
 have e:∀ S:Q2,qD w3 (fun _=>none) false (zR S)=un S.length:=by
  intro S; induction S with
  | nil=>rfl
  | cons v S ih=>simp only [ju,qD,w3,Option.toList_some];rw [qbd w3 _ false true rfl (fun _=>rfl),ih]; rfl
 exact zk (qG hS (wq w3 _ false)) (fun s=>e _)
lemma qb8 {A:Q0→Q0} {n:Q0→ℕ} {H:ℕ→Q0→Q1}
 (hA:Lib.qF A) (hn:qi n) (hH:qS (fun t=>H (Q9 t).1.length (Q9 t).2)):
 LLR (fun s=>(List.range (n s)).map (fun i=>H i (A s))):=
 zk (ka (yB false (qG hH qa9)) hn hA) (fun s=>by simp [zR,List.flatMap_map,qk])
lemma qdp {A:Q0→Q0} {n:Q0→ℕ} {H:ℕ→Q0→Q2}
 (hA:Lib.qF A) (hn:qi n) (hH:LLR (fun t=>H (Q9 t).1.length (Q9 t).2)):
 LLR (fun s=>(List.range (n s)).flatMap (fun i=>H i (A s))):=
 zk (ka hH hn hA) (fun s=>by simp [zR,List.flatMap_assoc,qk])
lemma vy (v:Q1):(zn v).length=v.length+v.sum:=by
 induction v with
 | nil=>rfl
 | cons a v ih=>simp [ih]; omega
lemma kp (S:Q2):
 (zR S).length≤S.length+2 * (S.map (fun v=>v.length+v.sum)).sum:=by
 have hd:∀ w,(dbl w).length=2 * w.length:=by
  intro w; induction w with
  | nil=>rfl
  | cons b w ih=>simp [ih]; omega
 induction S with
 | nil=>simp
 | cons v S ih=>simp only [ju,qI,List.length_append,hd,vy,List.map_cons,List.sum_cons];omega
lemma z8 {a:Q0→ℕ} (ha:qi a):∃ P:Q5,∀ s,a s≤P.eval s.length:=w4 ha
end Lib.R
namespace Lib.qb9
open PEqualNP.Library
def q22 {K:Type} {Γ:K→Type} {Λ σ:Type}:Turing.TM2.Stmt Γ Λ σ→Set (Σ k,Γ k)
 | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,Γ k)) ∪ q22 q
 | .peek _ _ q=>q22 q
 | .pop _ _ q=>q22 q
 | .load _ q=>q22 q
 | .branch _ q₁ q₂=>q22 q₁ ∪ q22 q₂
 | .goto _=>∅
 | .halt=>∅
lemma qfh {K:Type} {Γ:K→Type} {Λ σ:Type} [Finite σ]
 (q:Turing.TM2.Stmt Γ Λ σ):(q22 q).Finite:=by
 induction q with
 | push _ _ _ ih=>exact (Set.finite_range _).union ih
 | peek _ _ _ ih=>exact ih
 | pop _ _ _ ih=>exact ih
 | load _ _ ih=>exact ih
 | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
 | goto _=>exact Set.finite_empty
 | halt=>exact Set.finite_empty
def q29 {K:Type} [DecidableEq K] {Γ:K→Type} {Λ σ:Type}
    (T:∀ k,Set (Γ k)):
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩:Σ j,Γ j)∈q22 q→s∈T k)→
    Turing.TM2.Stmt (fun k=>{s:Γ k // s∈T k}) Λ σ
 | .push k g q,h=>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
     (q29 T q (fun j s hs=>h j s (Or.inr hs)))
 | .peek k f q,h=>.peek k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
 | .pop k f q,h=>.pop k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
 | .load a q,h=>.load a (q29 T q h)
 | .branch f q₁ q₂,h=>.branch f
     (q29 T q₁ (fun j s hs=>h j s (Or.inl hs)))
     (q29 T q₂ (fun j s hs=>h j s (Or.inr hs)))
 | .goto f,_=>.goto f
 | .halt,_=>.halt
def q67 {K:Type} {Γ:K→Type} {Λ σ:Type} (T:∀ k,Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s:Γ k // s∈T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ:=
 ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma qfj {K:Type} {Γ:K→Type} {Λ σ:Type} (T:∀ k,Set (Γ k)):
 Function.Injective (q67 (Λ:=Λ) (σ:=σ) T):=by
 rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h;simp only [q67,Turing.TM2.Cfg.mk.injEq] at h;obtain ⟨rfl,rfl,hS⟩:=h;congr 1
 funext k
 exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma q84 {K:Type} [DecidableEq K] {Γ:K→Type} (T:∀ k,Set (Γ k))
 (S:∀ k,List {s:Γ k // s∈T k}) (k:K) (l:List {s:Γ k // s∈T k}):
 (fun j=>(update S k l j).map Subtype.val)=
   update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
 funext j
 by_cases h:j=k
 · subst h;simp
 · simp [h]
lemma qfi {K:Type} [DecidableEq K] {Γ:K→Type} {Λ σ:Type}
 (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
 (hq:∀ k s,(⟨k,s⟩:Σ j,Γ j)∈q22 q→s∈T k)
 (v:σ) (S:∀ k,List {s:Γ k // s∈T k}):
 q67 T (Turing.TM2.stepAux (q29 T q hq) v S)=
  Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
 induction q generalizing v S with
 | push k g q ih=>simp only [q29,Turing.TM2.stepAux];rw [ih,q84];rfl
 | peek k f q ih=>simp only [q29,Turing.TM2.stepAux];exact (ih hq _ _).trans (by rw [List.head?_map])
 | pop k f q ih=>simp only [q29,Turing.TM2.stepAux];exact (ih hq _ _).trans (by rw [q84,List.head?_map,List.map_tail])
 | load a q ih=>simp only [q29,Turing.TM2.stepAux];exact ih hq (a v) S
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [q29,Turing.TM2.stepAux]
   cases f v
   · exact ih₂ _ v S
   · exact ih₁ _ v S
 | goto f=>rfl
 | halt=>rfl
end Lib.qb9
namespace Lib.qb9
open PEqualNP.Library
lemma qaL (c:Turing.TM2ComputableAux Bool Bool):
 ∃ M:Turing.TM2ComputableAux Bool Bool,(∀ i,Finite (M.tm.Γ i))∧
   ∀ (x y:Q0) (t:ℕ),
     Nonempty (Turing.TM2OutputsInTime c.tm (x.map c.inputAlphabet.invFun) (some (y.map c.outputAlphabet.invFun)) t)→
     Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some (y.map M.outputAlphabet.invFun)) t):=by
 classical
 let _:DecidableEq c.tm.K:=c.tm.kDecidableEq;let _:Fintype c.tm.K:=c.tm.kFin;let _:Fintype c.tm.Λ:=c.tm.ΛFin;let _:Fintype c.tm.σ:=c.tm.σFin;let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
 let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k=>{s|k=c.tm.k₀∨k=c.tm.k₁∨(⟨k,s⟩:Σ j,c.tm.Γ j)∈⋃ l:c.tm.Λ,q22 (c.tm.m l)}
 let e₀:{s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀:=
  { toFun:=Subtype.val,invFun:=fun s=>⟨s,Or.inl rfl⟩,
    left_inv:=fun _=>rfl,right_inv:=fun _=>rfl }
 let e₁:{s:c.tm.Γ c.tm.k₁ // s∈T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁:=
  { toFun:=Subtype.val,invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩,
    left_inv:=fun _=>rfl,right_inv:=fun _=>rfl }
 let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
 let tm':Turing.FinTM2:=
  { K:=c.tm.K,kDecidableEq:=c.tm.kDecidableEq,kFin:=c.tm.kFin,
    k₀:=c.tm.k₀,k₁:=c.tm.k₁,
    Γ:=fun k=>{s:c.tm.Γ k // s∈T k},
    Λ:=c.tm.Λ,main:=c.tm.main,ΛFin:=c.tm.ΛFin,
    σ:=c.tm.σ,initialState:=c.tm.initialState,σFin:=c.tm.σFin,
    Γk₀Fin:=hΓ0Fin,
    m:=fun l=>q29 T (c.tm.m l) (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
 have h8:∀ j:tm'.K,Finite (tm'.Γ j):=by
  intro j;by_cases h0:j=c.tm.k₀
  · subst h0; exact Finite.of_fintype _
  · by_cases h1:j=c.tm.k₁
    · subst h1;have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm;exact Finite.of_equiv _ e₁.symm
    · have h7:(⋃ l:c.tm.Λ,q22 (c.tm.m l)).Finite:=
       Set.finite_iUnion fun l=>qfh (c.tm.m l)
      have:Finite ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)):=h7.to_subtype
      refine Finite.of_injective (f:=fun x:tm'.Γ j=>
       (⟨⟨j,x.1⟩,by
         rcases x.2 with h|h|h
         · exact (h0 h).elim
         · exact (h1 h).elim
         · exact h⟩:↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)))) ?_
      intro x y hxy;have h1':=congrArg (fun z=>z.1) hxy;exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
 have h2:∀ cfg:tm'.Cfg,Option.map (q67 T) (tm'.step cfg)=c.tm.step (q67 T cfg):=by
  rintro ⟨l,v,S⟩
  cases l with
  | none=>rfl
  | some l=>
    change some (q67 T (Turing.TM2.stepAux (q29 T (c.tm.m l) _) v S))=
     some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
    exact congrArg some (qfi T (c.tm.m l) _ v S)
 have h4:∀ (steps:ℕ) (cfg:tm'.Cfg),
  Option.map (q67 T) ((flip bind tm'.step)^[steps] (some cfg))=
   (flip bind c.tm.step)^[steps] (some (q67 T cfg)):=by
  intro steps;induction steps with
  | zero=>intro cfg; rfl
  | succ steps ih=>
    intro cfg;rw [qM,qM]
    cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
    | none=>have hih:=ih cfg; rw [hcur] at hih; rw [← hih]; rfl
    | some cfg'=>have hih:=ih cfg; rw [hcur] at hih; rw [← hih]; exact h2 cfg'
 let M:Turing.TM2ComputableAux Bool Bool:={ tm:=tm',inputAlphabet:=e₀.trans c.inputAlphabet,outputAlphabet:=e₁.trans c.outputAlphabet }
 refine ⟨M,h8,fun x y t ⟨r⟩=>⟨{
  steps:=r.steps
  steps_le_m:=r.steps_le_m
  evals_in_steps:=by
   have h3:=r.evals_in_steps
   have h5:q67 T (Turing.initList tm' (x.map (e₀.trans c.inputAlphabet).invFun))=
    Turing.initList c.tm (x.map c.inputAlphabet.invFun):=by
    simp only [q67,Turing.initList];congr 1; funext k;by_cases hk:k=c.tm.k₀
    · subst hk; dsimp only [tm'];simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]; rfl
    · dsimp only [tm'];simp only [hk,↓reduceDIte,List.map_nil]
   have h6:q67 T (Turing.haltList tm' (y.map (e₁.trans c.outputAlphabet).invFun))=
    Turing.haltList c.tm (y.map c.outputAlphabet.invFun):=by
    simp only [q67,Turing.haltList];congr 1; funext k;by_cases hk:k=c.tm.k₁
    · subst hk; dsimp only [tm'];simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]; rfl
    · dsimp only [tm'];simp only [hk,↓reduceDIte,List.map_nil]
   apply Option.map_injective (qfj T);rw [h4,h5,h3];exact (congrArg some h6).symm }⟩⟩
end Lib.qb9
namespace Lib.qC.qdG
open Turing PEqualNP.Library Lib.qC
inductive WX
 | I|T|O
 deriving DecidableEq
instance:Fintype WX:=Fintype.ofList [WX.I,WX.T,WX.O] (fun x=>by cases x <;> simp)
inductive WL
 | l1|l2|l3|l4|l5|l6
 deriving DecidableEq
instance:Fintype WL:=Fintype.ofList [WL.l1,WL.l2,WL.l3,WL.l4,WL.l5,WL.l6] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev WΓ:M.K ⊕ WX→Type
 | inl k=>M.Γ k
 | inr WX.I=>Bool
 | inr WX.T=>Bool
 | inr WX.O=>Bool
abbrev WΛ:Type:=M.Λ ⊕ WL
abbrev Wσ:Type:=M.σ×Option Bool
variable {M}
def trW:TM2.Stmt M.Γ M.Λ M.σ→TM2.Stmt (WΓ M) (WΛ M) (Wσ M)
 | .push k f q=>.push (inl k) (fun s=>f s.1) (trW q)
 | .peek k f q=>.peek (inl k) (fun s o=>(f s.1 o,s.2)) (trW q)
 | .pop k f q=>.pop (inl k) (fun s o=>(f s.1 o,s.2)) (trW q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (trW q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trW q₁) (trW q₂)
 | .goto f=>.goto (fun s=>inl (f s.1))
 | .halt=>.goto (fun _=>inr WL.l3)
variable (M)
def q0 (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool):
    WΛ M→TM2.Stmt (WΓ M) (WΛ M) (Wσ M)
 | inl l=>trW (M.m l)
 | inr WL.l1=>
   .pop (inr WX.I) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.push (inr WX.T) (fun s=>s.2.getD false) (.goto fun _=>inr WL.l1))
       (.goto fun _=>inr WL.l2))
 | inr WL.l2=>
   .pop (inr WX.T) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.push (inl M.k₀) (fun s=>e₀ (s.2.getD false)) (.goto fun _=>inr WL.l2))
       (.goto fun _=>inl M.main))
 | inr WL.l3=>
   .pop (inl M.k₁) (fun s o=>(s.1,o.map e₁))
     (.branch (fun s=>s.2.getD false)
       (.goto fun _=>inr WL.l4)
       (.goto fun _=>inr WL.l5))
 | inr WL.l4=>
   .pop (inl M.k₁) (fun s o=>(s.1,o.map e₁))
     (.branch (fun s=>s.2.isSome)
       (.push (inr WX.T) (fun s=>s.2.getD false) (.goto fun _=>inr WL.l4))
       (.goto fun _=>inr WL.l2))
 | inr WL.l5=>
   .pop (inl M.k₁) (fun s o=>(s.1,o.map e₁))
     (.branch (fun s=>s.2.isSome)
       (.push (inr WX.T) (fun s=>s.2.getD false) (.goto fun _=>inr WL.l5))
       (.goto fun _=>inr WL.l6))
 | inr WL.l6=>
   .pop (inr WX.T) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.push (inr WX.O) (fun s=>s.2.getD false) (.goto fun _=>inr WL.l6))
       .halt)
def u2 (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool):FinTM2:=haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ WX
   k₀:=inr WX.I
   k₁:=inr WX.O
   Γ:=WΓ M
   Λ:=WΛ M
   main:=inr WL.l1
   σ:=Wσ M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype Bool)
   m:=q0 M e₀ e₁ }
variable {M}
def zt (S:∀ k,List (M.Γ k)) (i t o:Q0):∀ k,List (WΓ M k)
 | inl k=>S k
 | inr WX.I=>i
 | inr WX.T=>t
 | inr WX.O=>o
section zt
variable (S:∀ k,List (M.Γ k)) (i t o:Q0)
lemma yW (k:M.K) (x:List (M.Γ k)):
 update (zt S i t o) (inl k) x=zt (update S k x) i t o:=by
 letI:=M.kDecidableEq
 funext j
 rcases j with j|j
 · by_cases h:j=k
   · subst h; rw [update_self]; show x=update S j x j; rw [update_self]
   · rw [update_of_ne (by simpa using h)]; show S j=update S k x j; rw [update_of_ne h]
 · rw [update_of_ne (by simp)]; cases j <;> rfl
lemma jW (i':Q0):update (zt S i t o) (inr WX.I) i'=zt S i' t o:=by
 funext j; rcases j with j|(_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma kh (t':Q0):update (zt S i t o) (inr WX.T) t'=zt S i t' o:=by
 funext j; rcases j with j|(_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
 · rw [update_of_ne (by simp)]; rfl
lemma qaf (o':Q0):update (zt S i t o) (inr WX.O) o'=zt S i t o':=by
 funext j; rcases j with j|(_|_|_)
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_of_ne (by simp)]; rfl
 · rw [update_self]; rfl
end zt
abbrev kl (M:FinTM2):Type:=TM2.Cfg (WΓ M) (WΛ M) (Wσ M)
def jm (b:Option Bool) (i t o:Q0) (c:TM2.Cfg M.Γ M.Λ M.σ):kl M:=⟨some (c.l.elim (inr WL.l3) inl),(c.var,b),zt c.stk i t o⟩
lemma qfo (b:Option Bool) (i t o:Q0)
 (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)):
 TM2.stepAux (trW q) ((v,b):Wσ M) (zt S i t o)=
  jm b i t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>have:=ih v (update S k (f v::S k)); rw [← yW] at this; exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>have:=ih (f v (S k).head?) (update S k (S k).tail); rw [← yW] at this; exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [trW,TM2.stepAux]; cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
lemma qdJ (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
 (b:Option Bool) (i t o:Q0)
 (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c'):
 TM2.step (q0 M e₀ e₁) (jm b i t o c)=some (jm b i t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>simp only [TM2.step,Option.some.injEq] at h; subst h;exact congrArg some (qfo b i t o (M.m l) v S)
lemma qaF (b:Option Bool) (i t o:Q0) (l:List (M.Γ M.k₀)):
 jm b i t o (initList M l)=
  (⟨some (inl M.main),(M.initialState,b),
    zt (update (fun _=>[]) M.k₀ l) i t o⟩:kl M):=by
 rw [zH]; rfl
lemma qaE (b:Option Bool) (i t o:Q0) (m:List (M.Γ M.k₁)):
 jm b i t o (haltList M m)=
  (⟨some (inr WL.l3),(M.initialState,b),
    zt (update (fun _=>[]) M.k₁ m) i t o⟩:kl M):=by
 rw [zG]; rfl
lemma qbE:(zt (fun _=>[]) [] [] []:∀ k,List (WΓ M k))=fun _=>[]:=by funext j; rcases j with j|(_|_|_) <;> rfl
lemma qcz (i:Q0):
 (zt (fun _=>[]) i [] []:∀ k,List (WΓ M k))=
   update (fun _=>[]:∀ k,List (WΓ M k)) (inr WX.I) i:=
 (jW (fun _=>[]) [] [] [] i).symm.trans (by rw [qbE])
lemma qcA (o:Q0):
 (zt (fun _=>[]) [] [] o:∀ k,List (WΓ M k))=
   update (fun _=>[]:∀ k,List (WΓ M k)) (inr WX.O) o:=
 (qaf (fun _=>[]) [] [] [] o).symm.trans (by rw [qbE])
section loops
variable (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool) (v:M.σ)
lemma qeW (S:∀ k,List (M.Γ k)) (o:Q0):
 ∀ (i t:Q0) (b:Option Bool),
 ((flip bind (TM2.step (q0 M e₀ e₁))))^[i.length+1]
    (some (⟨some (inr WL.l1),(v,b),zt S i t o⟩:kl M))=
   some ⟨some (inr WL.l2),(v,none),zt S [] (i.reverse++t) o⟩:=by
 intro i; induction i with
 | nil=>intro t b; simp [flip,TM2.step,q0,TM2.stepAux,zt,jW]
 | cons a i ih=>
   intro t b;rw [qI,ze]
   have h0:(flip bind (TM2.step (q0 M e₀ e₁)))
    (some (⟨some (inr WL.l1),(v,b),zt S (a::i) t o⟩:kl M))=
    some ⟨some (inr WL.l1),(v,some a),zt S i (a::t) o⟩:=by
    simp [flip,TM2.step,q0,TM2.stepAux,zt,jW,kh]
   rw [h0,ih]; simp
lemma qdc (i o:Q0):
 ∀ (t:Q0) (S:∀ k,List (M.Γ k)) (b:Option Bool),
 ((flip bind (TM2.step (q0 M e₀ e₁))))^[t.length+1]
    (some (⟨some (inr WL.l2),(v,b),zt S i t o⟩:kl M))=
   some ⟨some (inl M.main),(v,none),
    zt (update S M.k₀ (t.reverse.map e₀++S M.k₀)) i [] o⟩:=by
 intro t; induction t with
 | nil=>
   intro S b
   have h1:update S M.k₀ (S M.k₀)=S:=by let _:=M.kDecidableEq; funext k; by_cases h:k=M.k₀ <;> simp [h]
   simp [flip,TM2.step,q0,TM2.stepAux,zt,kh,h1]
 | cons a t ih=>
   intro S b;rw [qI,ze]
   have h0:(flip bind (TM2.step (q0 M e₀ e₁)))
    (some (⟨some (inr WL.l2),(v,b),zt S i (a::t) o⟩:kl M))=
    some ⟨some (inr WL.l2),(v,some a),
     zt (update S M.k₀ (e₀ a::S M.k₀)) i t o⟩:=by
    simp [flip,TM2.step,q0,TM2.stepAux,zt,kh,yW]
   rw [h0,ih];let _:=M.kDecidableEq;simp [Function.update_idem]
lemma qeX (S:∀ k,List (M.Γ k)) (i o:Q0):
 ∀ (m:List (M.Γ M.k₁)) (t:Q0) (b:Option Bool),
 ((flip bind (TM2.step (q0 M e₀ e₁))))^[m.length+1]
    (some (⟨some (inr WL.l4),(v,b),zt (update S M.k₁ m) i t o⟩:kl M))=
   some ⟨some (inr WL.l2),(v,none),
    zt (update S M.k₁ []) i ((m.map e₁).reverse++t) o⟩:=by
 intro m; induction m with
 | nil=>intro t b;let _:=M.kDecidableEq;simp [flip,TM2.step,q0,TM2.stepAux,zt,yW,Function.update_idem]
 | cons y m ih=>
   intro t b;rw [qI,ze]
   have h0:(flip bind (TM2.step (q0 M e₀ e₁)))
    (some (⟨some (inr WL.l4),(v,b),zt (update S M.k₁ (y::m)) i t o⟩:kl M))=
    some ⟨some (inr WL.l4),(v,some (e₁ y)),
     zt (update S M.k₁ m) i (e₁ y::t) o⟩:=by
    let _:=M.kDecidableEq;simp [flip,TM2.step,q0,TM2.stepAux,zt,yW,kh,Function.update_idem]
   rw [h0,ih]; simp
lemma qeY (S:∀ k,List (M.Γ k)) (i o:Q0):
 ∀ (m:List (M.Γ M.k₁)) (t:Q0) (b:Option Bool),
 ((flip bind (TM2.step (q0 M e₀ e₁))))^[m.length+1]
    (some (⟨some (inr WL.l5),(v,b),zt (update S M.k₁ m) i t o⟩:kl M))=
   some ⟨some (inr WL.l6),(v,none),
    zt (update S M.k₁ []) i ((m.map e₁).reverse++t) o⟩:=by
 intro m; induction m with
 | nil=>intro t b;let _:=M.kDecidableEq;simp [flip,TM2.step,q0,TM2.stepAux,zt,yW,Function.update_idem]
 | cons y m ih=>
   intro t b;rw [qI,ze]
   have h0:(flip bind (TM2.step (q0 M e₀ e₁)))
    (some (⟨some (inr WL.l5),(v,b),zt (update S M.k₁ (y::m)) i t o⟩:kl M))=
    some ⟨some (inr WL.l5),(v,some (e₁ y)),
     zt (update S M.k₁ m) i (e₁ y::t) o⟩:=by
    let _:=M.kDecidableEq;simp [flip,TM2.step,q0,TM2.stepAux,zt,yW,kh,Function.update_idem]
   rw [h0,ih]; simp
lemma qeZ (S:∀ k,List (M.Γ k)) (i:Q0):
 ∀ (t o:Q0) (b:Option Bool),
 ((flip bind (TM2.step (q0 M e₀ e₁))))^[t.length+1]
    (some (⟨some (inr WL.l6),(v,b),zt S i t o⟩:kl M))=
   some ⟨none,(v,none),zt S i [] (t.reverse++o)⟩:=by
 intro t; induction t with
 | nil=>intro o b; simp [flip,TM2.step,q0,TM2.stepAux,zt,kh]
 | cons a t ih=>
   intro o b;rw [qI,ze]
   have h0:(flip bind (TM2.step (q0 M e₀ e₁)))
    (some (⟨some (inr WL.l6),(v,b),zt S i (a::t) o⟩:kl M))=
    some ⟨some (inr WL.l6),(v,some a),zt S i t (a::o)⟩:=by
    simp [flip,TM2.step,q0,TM2.stepAux,zt,kh,qaf]
   rw [h0,ih]; simp
lemma qdd (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (b:Option Bool):
 TM2.step (q0 M e₀ e₁)
  (⟨some (inr WL.l3),(v,b),zt (update (fun _=>[]) M.k₁ (y::m)) [] [] []⟩:kl M)=
  some ⟨some (if e₁ y then inr WL.l4 else inr WL.l5),(v,some (e₁ y)),
   zt (update (fun _=>[]) M.k₁ m) [] [] []⟩:=by
 let _:=M.kDecidableEq
 cases h:e₁ y <;> simp [TM2.step,q0,TM2.stepAux,zt,yW,Function.update_idem,h]
end loops
lemma qaA (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
 (g:Q0→Q0) (p:Q5)
 (hrun:∀ z:Q0,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧(flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧m.map e₁=g z):
 ∀ (k:ℕ) (st:ℕ→Q0) (out:Q0) (L:ℕ) (b:Option Bool),(∀ j<k,g (st j)=true::st (j+1))→ g (st k)=false::out→(∀ j≤k,(st j).length≤L)→ out.length≤L→
   ∃ n,n≤(k+1) * (p.eval L+2 * L+3)∧
     ((flip bind (TM2.step (q0 M e₀ e₁))))^[n]
        (some (jm b [] [] [] (initList M ((st 0).map e₀))))=
       some ⟨none,(M.initialState,none),zt (fun _=>[]) [] [] out⟩:=by
 intro k;induction k with
 | zero=>
   intro st out L b _ hlast hL hout;obtain ⟨s,m,hs,hm,hmg⟩:=hrun (st 0);rw [hlast] at hmg
   cases m with
   | nil=>simp at hmg
   | cons y m'=>
     simp only [List.map_cons,List.cons.injEq] at hmg;obtain ⟨hy,hm'⟩:=hmg
     have q1:=kV (TM2.step M.m) (TM2.step (q0 M e₀ e₁))
      (jm b [] [] []) (qdJ e₀ e₁ b [] [] []) s _ _ hm
     rw [qaE] at q1
     have q2:((flip bind (TM2.step (q0 M e₀ e₁))))^[1]
      (some (⟨some (inr WL.l3),(M.initialState,b),
        zt (update (fun _=>[]) M.k₁ (y::m')) [] [] []⟩:kl M))=
      some ⟨some (inr WL.l5),(M.initialState,some false),
       zt (update (fun _=>[]) M.k₁ m') [] [] []⟩:=by
      simpa [Function.iterate_one,flip,hy] using qdd e₀ e₁ M.initialState y m' b
     have q3:=qeY e₀ e₁ M.initialState (fun _=>[]) [] [] m' [] (some false)
     have h0:(update (fun _=>[]:∀ k,List (M.Γ k)) M.k₁ [])=fun _=>[]:=by let _:=M.kDecidableEq; funext j; by_cases h:j=M.k₁ <;> simp [h]
     rw [h0,hm',qX] at q3;have q4:=qeZ e₀ e₁ M.initialState (fun _=>[]) [] out.reverse [] none;rw [List.reverse_reverse,qX] at q4
     have h1:((flip bind (TM2.step (q0 M e₀ e₁))))^[(out.reverse.length+1)+(m'.length+1)+1+s]
      (some (jm b [] [] [] (initList M ((st 0).map e₀))))=
      some ⟨none,(M.initialState,none),zt (fun _=>[]) [] [] out⟩:=by
      rw [iterate_add_apply _ _ s,q1,iterate_add_apply _ _ 1,q2,iterate_add_apply _ _ (m'.length+1),q3,q4]
     refine ⟨_,?_,h1⟩
     have hp:p.eval (st 0).length≤p.eval L:=y7 p (hL 0 le_rfl);have hml:m'.length=out.length:=by rw [← hm',zM]
     simp only [vJ] at hml ⊢;omega
 | succ k ih=>
   intro st out L b hstep hlast hL hout;obtain ⟨s,m,hs,hm,hmg⟩:=hrun (st 0);rw [hstep 0 (Nat.succ_pos k)] at hmg
   cases m with
   | nil=>simp at hmg
   | cons y m'=>
     simp only [List.map_cons,List.cons.injEq] at hmg;obtain ⟨hy,hm'⟩:=hmg
     have q1:=kV (TM2.step M.m) (TM2.step (q0 M e₀ e₁))
      (jm b [] [] []) (qdJ e₀ e₁ b [] [] []) s _ _ hm
     rw [qaE] at q1
     have q2:((flip bind (TM2.step (q0 M e₀ e₁))))^[1]
      (some (⟨some (inr WL.l3),(M.initialState,b),
        zt (update (fun _=>[]) M.k₁ (y::m')) [] [] []⟩:kl M))=
      some ⟨some (inr WL.l4),(M.initialState,some true),
       zt (update (fun _=>[]) M.k₁ m') [] [] []⟩:=by
      simpa [Function.iterate_one,flip,hy] using qdd e₀ e₁ M.initialState y m' b
     have q3:=qeX e₀ e₁ M.initialState (fun _=>[]) [] [] m' [] (some true)
     have h0:(update (fun _=>[]:∀ k,List (M.Γ k)) M.k₁ [])=fun _=>[]:=by let _:=M.kDecidableEq; funext j; by_cases h:j=M.k₁ <;> simp [h]
     rw [h0,hm',qX] at q3;have q4:=qdc e₀ e₁ M.initialState [] [] (st 1).reverse (fun _=>[]) none;rw [List.reverse_reverse,qX,← qaF] at q4
     obtain ⟨n,hn,q5⟩:=ih (fun j=>st (j+1)) out L none
      (fun j hj=>hstep (j+1) (by omega)) hlast
      (fun j hj=>hL (j+1) (by omega)) hout
     have h1:((flip bind (TM2.step (q0 M e₀ e₁))))^[n+((st 1).reverse.length+1)+(m'.length+1)+1+s]
      (some (jm b [] [] [] (initList M ((st 0).map e₀))))=
      some ⟨none,(M.initialState,none),zt (fun _=>[]) [] [] out⟩:=by
      rw [iterate_add_apply _ _ s,q1,iterate_add_apply _ _ 1,q2,iterate_add_apply _ _ (m'.length+1),q3,iterate_add_apply _ _ ((st 1).reverse.length+1),q4,q5]
     refine ⟨_,?_,h1⟩
     have hp:p.eval (st 0).length≤p.eval L:=y7 p (hL 0 (Nat.zero_le _));have hml:m'.length=(st 1).length:=by rw [← hm',zM]
     have hs1:(st 1).length≤L:=hL 1 (by omega);simp only [vJ]
     have hmul:(k+1+1) * (p.eval L+2 * L+3)=
      (k+1) * (p.eval L+2 * L+3)+(p.eval L+2 * L+3):=by ring
     omega
lemma qa0 (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
 (g:Q0→Q0) (p:Q5)
 (hrun:∀ z:Q0,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧(flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧m.map e₁=g z)
 (k:ℕ) (st:ℕ→Q0) (out:Q0) (L:ℕ)
 (hstep:∀ j<k,g (st j)=true::st (j+1))
 (hlast:g (st k)=false::out)
 (hL:∀ j≤k,(st j).length≤L) (hout:out.length≤L):
 ∃ n,n≤(k+1) * (p.eval L+2 * L+3)+2 * L+2∧
   ((flip bind (TM2.step (q0 M e₀ e₁))))^[n]
      (some (initList (u2 M e₀ e₁) (st 0)))=
     some (haltList (u2 M e₀ e₁) out):=by
 have q1:=qeW e₀ e₁ M.initialState (fun _=>[]) [] (st 0) [] none;rw [qX] at q1;have q2:=qdc e₀ e₁ M.initialState [] [] (st 0).reverse (fun _=>[]) none;rw [List.reverse_reverse,qX,← qaF] at q2;obtain ⟨n,hn,q3⟩:=qaA e₀ e₁ g p hrun k st out L none hstep hlast hL hout
 have h0:(⟨some (inr WL.l1),(M.initialState,none),
  zt (fun _=>[]) (st 0) [] []⟩:kl M)=initList (u2 M e₀ e₁) (st 0):=
  (congrArg (TM2.Cfg.mk (some (inr WL.l1)) (M.initialState,none)) (qcz (st 0))).trans
    (zH (u2 M e₀ e₁) (st 0)).symm
 have h1:(⟨none,(M.initialState,none),zt (fun _=>[]) [] [] out⟩:kl M)=
  haltList (u2 M e₀ e₁) out:=
  (congrArg (TM2.Cfg.mk none (M.initialState,none)) (qcA out)).trans
    (zG (u2 M e₀ e₁) out).symm
 rw [h0] at q1; rw [h1] at q3;refine ⟨n+((st 0).reverse.length+1)+((st 0).length+1),?_,?_⟩
 · have hs0:(st 0).length≤L:=hL 0 (Nat.zero_le _);simp only [vJ]; omega
 · rw [iterate_add_apply _ _ ((st 0).length+1),q1,iterate_add_apply _ _ ((st 0).reverse.length+1),q2,q3];rfl
lemma j2 (P:Q5):
 ∃ D:ℕ,∀ m:ℕ,P.eval m≤(m+2) ^ D:=by
 obtain ⟨A,hA⟩:∃ A:ℕ,∀ m,P.eval m≤A * (m+2) ^ P.natDegree:=by
  refine ⟨P.sum (fun _ c=>c),fun m=>?_⟩
  rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  calc ∑ i∈P.support,P.coeff i * m ^ i≤∑ i∈P.support,P.coeff i * (m+2) ^ P.natDegree:=by
        refine Finset.sum_le_sum fun i hi=>Nat.mul_le_mul_left _ ?_
        have h0:i≤P.natDegree:=Polynomial.le_natDegree_of_mem_supp i hi
        exact (Nat.pow_le_pow_left (by omega) i).trans
         (Nat.pow_le_pow_right (by omega) h0)
   _=(∑ i∈P.support,P.coeff i) * (m+2) ^ P.natDegree:=by rw [Finset.sum_mul]
 refine ⟨A+P.natDegree,fun m=>?_⟩
 have hA2:A≤(m+2) ^ A:=(Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega) A)
 calc P.eval m≤A * (m+2) ^ P.natDegree:=hA m
  _≤(m+2) ^ A * (m+2) ^ P.natDegree:=Nat.mul_le_mul_right _ hA2
  _=(m+2) ^ (A+P.natDegree):=(pow_add _ _ _).symm
lemma qaz
 (init step:Q0→Q0)
 (hinit:Lib.qF init) (hstep:Lib.qF step)
 (PL:Q5):
 ∃ (M:Turing.TM2ComputableAux Bool Bool) (C:ℕ),(∀ i,Finite (M.tm.Γ i))∧
   ∀ (x out:Q0) (k t:ℕ) (st:ℕ→Q0),st 0=init x→(∀ j<k,step (st j)=true::st (j+1))→step (st k)=false::out→(∀ j≤k,(st j).length≤PL.eval x.length)→ out.length≤PL.eval x.length→k≤(x.length+2) ^ t→
     Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (out.map M.outputAlphabet.invFun))
      ((x.length+2) ^ (t+C))):=by
 classical
 obtain ⟨c1⟩:=hinit;obtain ⟨c2⟩:=hstep;let e₀:Bool→c2.tm.Γ c2.tm.k₀:=c2.inputAlphabet.invFun;let e₁:c2.tm.Γ c2.tm.k₁→Bool:=c2.outputAlphabet;let Mw:FinTM2:=u2 c2.tm e₀ e₁;let φ:c1.tm.Γ c1.tm.k₁→Mw.Γ Mw.k₀:=fun s=>c1.outputAlphabet s
 let d:Option (Mw.Γ Mw.k₀):=some true;let Mc:FinTM2:=comp c1.tm Mw φ d
 let Maux:Turing.TM2ComputableAux Bool Bool:={ tm:=Mc,inputAlphabet:=c1.inputAlphabet,outputAlphabet:=Equiv.refl Bool }
 let Q:Q5:=c1.time+c2.time.comp PL+Polynomial.C 6 * PL+Polynomial.C 10
 obtain ⟨D,hD⟩:=j2 Q;obtain ⟨M,ha,h3⟩:=Lib.qb9.qaL Maux;refine ⟨M,D+1,ha,fun x out k t st h5 hst h7 hL h9 hk=>?_⟩
 apply h3 x out ((x.length+2) ^ (t+(D+1)))
 have h6:∀ z:Q0,∃ (s:ℕ) (m:List (c2.tm.Γ c2.tm.k₁)),
  s≤c2.time.eval z.length∧
  (flip bind (TM2.step c2.tm.m))^[s] (some (initList c2.tm (z.map e₀)))=
    some (haltList c2.tm m)∧m.map e₁=step z:=by
  intro z;refine ⟨(c2.outputsFun z).steps,(step z).map c2.outputAlphabet.invFun,(c2.outputsFun z).steps_le_m,(c2.outputsFun z).evals_in_steps,?_⟩
  rw [List.map_map]
  conv_rhs=>rw [← List.map_id (step z)]
  exact List.map_congr_left fun y _=>c2.outputAlphabet.right_inv y
 obtain ⟨n2,hn2,h2⟩:=qa0 e₀ e₁ step c2.time h6 k st out
  (PL.eval x.length) hst h7 hL h9
 have r1:=c1.outputsFun x
 have hφ:((init x).map c1.outputAlphabet.invFun).map φ=st 0:=by
  rw [h5,List.map_map]
  conv_rhs=>rw [← List.map_id (init x)]
  exact List.map_congr_left fun y _=>c1.outputAlphabet.right_inv y
 rw [← hφ] at h2
 obtain ⟨nt,hnt,-,ht⟩:=qa7 φ d (fun h=>by simp [d] at h)
  (x.map c1.inputAlphabet.invFun) ((init x).map c1.outputAlphabet.invFun) out
  r1.steps n2 r1.evals_in_steps h2
 have hlen1:((init x).map c1.outputAlphabet.invFun).length≤PL.eval x.length:=by rw [zM,← h5]; exact hL 0 (Nat.zero_le _)
 have h4:nt≤(x.length+2) ^ (t+(D+1)):=by
  have hQ:Q.eval x.length=c1.time.eval x.length+c2.time.eval (PL.eval x.length) +
   6 * PL.eval x.length+10:=by
   simp [Q,zO,z9,Polynomial.eval_comp]
  have hr1:r1.steps≤c1.time.eval x.length:=r1.steps_le_m
  have h8:nt≤(k+1) * Q.eval x.length:=by
   have h1:r1.steps+(2 * ((init x).map c1.outputAlphabet.invFun).length+2) +
    (2 * PL.eval x.length+2)≤(k+1) * (c1.time.eval x.length+4 * PL.eval x.length+7):=by
    have hle:r1.steps+(2 * ((init x).map c1.outputAlphabet.invFun).length+2) +
     (2 * PL.eval x.length+2)≤c1.time.eval x.length+4 * PL.eval x.length+7:=by omega
    exact hle.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos k))
   have h2':(k+1) * (c2.time.eval (PL.eval x.length)+2 * PL.eval x.length+3) +
    (k+1) * (c1.time.eval x.length+4 * PL.eval x.length+7)=
    (k+1) * Q.eval x.length:=by
    rw [hQ,← Nat.mul_add]; congr 1; omega
   omega
  have hk1:k+1≤(x.length+2) ^ (t+1):=by
   have hb:1≤(x.length+2) ^ t:=Nat.one_le_pow _ _ (by omega)
   calc k+1≤(x.length+2) ^ t+(x.length+2) ^ t:=Nat.add_le_add hk hb
    _=(x.length+2) ^ t * 2:=by omega
    _≤(x.length+2) ^ t * (x.length+2):=Nat.mul_le_mul_left _ (by omega)
    _=(x.length+2) ^ (t+1):=(pow_succ _ _).symm
  calc nt≤(k+1) * Q.eval x.length:=h8
   _≤(x.length+2) ^ (t+1) * (x.length+2) ^ D:=Nat.mul_le_mul hk1 (hD x.length)
   _=(x.length+2) ^ ((t+1)+D):=(pow_add _ _ _).symm
   _=(x.length+2) ^ (t+(D+1)):=by congr 1; omega
 have h0:out.map Maux.outputAlphabet.invFun=out:=List.map_id out;refine ⟨{ steps:=nt,evals_in_steps:=?_,steps_le_m:=h4 }⟩
 change (flip Option.bind (TM2.step Mc.m))^[nt]
  (some (initList Mc (x.map c1.inputAlphabet.invFun)))=
  some (haltList Mc (out.map Maux.outputAlphabet.invFun))
 rw [h0];exact ht
end Lib.qC.qdG
namespace jC
def cores {n:Nat} (H:Q4 n):(Q4 n):=((H.product H).image (fun z=>z.1 ∩ z.2)).filter (fun c=>c.card=2)
def ordinary {n:Nat} (H:Q4 n):(Q3 n):=Finset.univ \ (cores H).biUnion id
def base {n:Nat} (H:Q4 n):(Q4 n):=H.filter (fun R=>R⊆ordinary H)
def outer {n:Nat} (H:Q4 n) (c:Q3 n):(Q3 n):=(H.filter (fun R=>c⊆R)).biUnion id \ c
def step {n:Nat} (B:Q4 n) (V:Q3 n):(Q3 n):=V ∪ (B.filter (fun R=>¬ Disjoint R V)).biUnion id
def zX {n:Nat} (H:Q4 n) (c:Q3 n):
    (Q4 n):=
 H.filter (fun R=>c⊆R)
lemma zq {n:Nat} {H:(Q4 n)} (hH3:∀ R∈H,R.card=3)
 {c:(Q3 n)}:
 c∈cores H↔c.card=2∧∃ R₁∈H,∃ R₂∈H,R₁≠R₂∧R₁ ∩ R₂=c:=by
 simp only [cores,Finset.product_eq_sprod,qa,qN,Finset.mem_product,Prod.exists];constructor
 · rintro ⟨⟨R₁,R₂,⟨h1,h2⟩,rfl⟩,hc⟩;refine ⟨hc,R₁,h1,R₂,h2,?_,rfl⟩
   intro heq;subst heq;rw [Finset.inter_self,hH3 R₁ h1] at hc;omega
 · rintro ⟨hc,R₁,h1,R₂,h2,_,rfl⟩;exact ⟨⟨R₁,R₂,⟨h1,h2⟩,rfl⟩,hc⟩
lemma vR {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {c:(Q3 n)} (hc:c∈cores H):
 (zX H c).card=2∧∀ u∈c,H.filter (fun R=>u∈R)=zX H c:=by
 rcases (zq hH3).mp hc with ⟨hcc,R₁,h1,R₂,h2,hne,h3⟩
 have h6:c⊆R₁:=h3▸vD;have h5:c⊆R₂:=h3▸Finset.inter_subset_right;have h1m:R₁∈zX H c:=qa.mpr ⟨h1,h6⟩;have h2m:R₂∈zX H c:=qa.mpr ⟨h2,h5⟩
 have hge:2≤(zX H c).card:=by
  have h7:({R₁,R₂}:Finset _)⊆zX H c:=by intro R hR;simp only [qe,qd] at hR;rcases hR with rfl|rfl <;> assumption
  have hpc:({R₁,R₂}:Finset _).card=2:=zv hne;exact hpc▸qH h7
 have h0:∀ u∈c,zX H c⊆H.filter (fun R=>u∈R):=by intro u hu R hR;simp only [zX,qa] at hR ⊢;exact ⟨hR.1,hR.2 hu⟩
 obtain ⟨u₀,hu₀⟩:c.Nonempty:=qU.mp (by omega)
 have hle:(zX H c).card≤2:=(qH (h0 u₀ hu₀)).trans (hdeg u₀)
 have h4:(zX H c).card=2:=le_antisymm hle hge;refine ⟨h4,fun u hu=>?_⟩
 exact (zo (h0 u hu) (by rw [h4]; exact hdeg u)).symm
lemma zd {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {c₁ c₂:(Q3 n)} (h1:c₁∈cores H) (h2:c₂∈cores H) (hne:c₁≠c₂):
 Disjoint c₁ c₂:=by
 rw [qc];intro u hu1 hu2;apply hne;have eq1:=(vR hH3 hdeg h1).2 u hu1;have eq2:=(vR hH3 hdeg h2).2 u hu2;have h5:zX H c₁=zX H c₂:=eq1.symm.trans eq2;have hc1:=((zq hH3).mp h1).1;have hc2:=((zq hH3).mp h2).1;rcases yk.mp (vR hH3 hdeg h1).1 with ⟨R₁,R₂,hc,h7⟩
 have h4:R₁∈zX H c₁:=by rw [h7]; simp
 have h3:R₂∈zX H c₁:=by rw [h7]; simp
 have hf:R₁∈H:=(qa.mp h4).1;have he:R₂∈H:=(qa.mp h3).1
 have h9:c₁⊆R₁ ∩ R₂:=Finset.subset_inter (qa.mp h4).2 (qa.mp h3).2
 have h8:c₂⊆R₁ ∩ R₂:=by rw [h5] at h4 h3;exact Finset.subset_inter (qa.mp h4).2 (qa.mp h3).2
 have h0:(R₁ ∩ R₂).card≤2:=by
  by_contra hgt;have h6:3≤(R₁ ∩ R₂).card:=by omega
  have hb:R₁ ∩ R₂=R₁:=zo vD (by rw [hH3 R₁ hf]; exact h6)
  have ha:R₁ ∩ R₂=R₂:=zo Finset.inter_subset_right (by rw [hH3 R₂ he]; exact h6)
  exact hc (hb.symm.trans ha)
 have e1:c₁=R₁ ∩ R₂:=zo h9 (by rw [hc1]; exact h0);have e2:c₂=R₁ ∩ R₂:=zo h8 (by rw [hc2]; exact h0);exact e1.trans e2.symm
lemma jr {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {R c₁ c₂:(Q3 n)} (hR:R∈H)
 (h1:c₁∈cores H) (h2:c₂∈cores H) (hs1:c₁⊆R) (hs2:c₂⊆R):c₁=c₂:=by
 by_contra hne;have h3:=zd hH3 hdeg h1 h2 hne;have h0:(c₁ ∪ c₂).card≤R.card:=qH (Finset.union_subset hs1 hs2);rw [Finset.card_union_of_disjoint h3,((zq hH3).mp h1).1,((zq hH3).mp h2).1,hH3 R hR] at h0;omega
lemma u6 {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {R:(Q3 n)} (hR:R∈H):
 R∈base H∨∃ c∈cores H,c⊆R:=by
 by_cases h1:R⊆ordinary H
 · exact Or.inl (qa.mpr ⟨hR,h1⟩)
 · right;rw [Finset.not_subset] at h1;rcases h1 with ⟨u,huR,h0⟩
   simp only [ordinary,qg,qJ,true_and,not_not,qj,id_eq] at h0;rcases h0 with ⟨c,hc,huc⟩
   have h2:R∈zX H c:=by rw [← (vR hH3 hdeg hc).2 u huc];exact qa.mpr ⟨hR,huR⟩
   exact ⟨c,hc,(qa.mp h2).2⟩
lemma vP {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {c:(Q3 n)} (hc:c∈cores H):
 ∃ x y,x≠y∧x∈ordinary H∧y∈ordinary H∧
   outer H c={x,y}∧zX H c={insert x c,insert y c}:=by
 have hcc:=((zq hH3).mp hc).1;rcases yk.mp (vR hH3 hdeg hc).1 with ⟨R₁,R₂,hf,h2⟩
 have hb:R₁∈zX H c:=by rw [h2]; simp
 have h9:R₂∈zX H c:=by rw [h2]; simp
 have he:R₁∈H:=(qa.mp hb).1;have ha:R₂∈H:=(qa.mp h9).1;have hc1:c⊆R₁:=(qa.mp hb).2;have hc2:c⊆R₂:=(qa.mp h9).2
 have h6:(R₁ \ c).card=1:=by rw [Finset.card_sdiff_of_subset hc1,hH3 R₁ he,hcc]
 have h5:(R₂ \ c).card=1:=by rw [Finset.card_sdiff_of_subset hc2,hH3 R₂ ha,hcc]
 rcases Finset.card_eq_one.mp h6 with ⟨x,hx⟩
 rcases Finset.card_eq_one.mp h5 with ⟨y,hy⟩
 have h4:x∈R₁∧x∉c:=by
  have:x∈R₁ \ c:=by rw [hx]; simp
  exact qg.mp this
 have h3:y∈R₂∧y∉c:=by
  have:y∈R₂ \ c:=by rw [hy]; simp
  exact qg.mp this
 have h1:R₁=insert x c:=by
  ext u;by_cases huc:u∈c
  · simp [huc,hc1 huc]
  · have:u∈R₁ \ c↔u=x:=by rw [hx]; simp
    simp only [qg,huc,not_false_eq_true,and_true] at this;simp [this,huc]
 have h0:R₂=insert y c:=by
  ext u;by_cases huc:u∈c
  · simp [huc,hc2 huc]
  · have:u∈R₂ \ c↔u=y:=by rw [hy]; simp
    simp only [qg,huc,not_false_eq_true,and_true] at this;simp [this,huc]
 have hxy:x≠y:=by intro h;apply hf;rw [h1,h0,h]
 have h7:∀ z R,R∈H→c⊆R→z∈R→z∉c→z∈ordinary H:=by
  intro z R hRH hcR hzR hzc;simp only [ordinary,qg,qJ,true_and,qj,id_eq,not_exists,not_and];intro c' hc' hzc'
  have hRm':R∈zX H c':=by rw [← (vR hH3 hdeg hc').2 z hzc'];exact qa.mpr ⟨hRH,hzR⟩
  have h8:=jr hH3 hdeg hRH hc hc' hcR (qa.mp hRm').2;exact hzc (h8▸hzc')
 refine ⟨x,y,hxy,h7 x R₁ he hc1 h4.1 h4.2,h7 y R₂ ha hc2 h3.1 h3.2,?_,?_⟩
 · ext u;simp only [outer,qg,qj,id_eq,qe,qd];change (∃ R∈zX H c,u∈R)∧u∉c↔u=x∨u=y;rw [h2,h1,h0];constructor
   · rintro ⟨⟨R,hR,huR⟩,huc⟩;simp only [qe,qd] at hR;rcases hR with rfl|rfl
     · simp only [qe,huc,or_false] at huR; exact Or.inl huR
     · simp only [qe,huc,or_false] at huR; exact Or.inr huR
   · rintro (h|h)
     · rw [h]; exact ⟨⟨insert x c,by simp,by simp⟩,h4.2⟩
     · rw [h]; exact ⟨⟨insert y c,by simp,by simp⟩,h3.2⟩
 · rw [h2,h1,h0]
lemma jx {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {c:(Q3 n)} (hc:c∈cores H):
 (outer H c).card=2:=by
 rcases vP hH3 hdeg hc with ⟨x,y,hxy,_,_,h0,_⟩
 rw [h0,zv hxy]
lemma zE {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {c:(Q3 n)} (hc:c∈cores H):
 outer H c⊆ordinary H:=by
 rcases vP hH3 hdeg hc with ⟨x,y,_,hx,hy,h0,_⟩
 rw [h0];intro u hu;simp only [qe,qd] at hu;rcases hu with rfl|rfl <;> assumption
lemma wE {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 {R₁ R₂:(Q3 n)} (h1:R₁∈base H) (h2:R₂∈base H) (hne:R₁≠R₂):
 (R₁ ∩ R₂).card≤1:=by
 by_contra hgt;have h1H:R₁∈H:=(qa.mp h1).1;have h2H:R₂∈H:=(qa.mp h2).1;have h6:R₁⊆ordinary H:=(qa.mp h1).2
 have hle2:(R₁ ∩ R₂).card≤2:=by
  by_contra hgt2;have h4:3≤(R₁ ∩ R₂).card:=by omega
  have e1:=zo vD
   (by rw [hH3 R₁ h1H]; exact h4)
  have e2:=zo Finset.inter_subset_right
   (by rw [hH3 R₂ h2H]; exact h4)
  exact hne (e1.symm.trans e2)
 have h3:(R₁ ∩ R₂).card=2:=by omega
 have h5:R₁ ∩ R₂∈cores H:=(zq hH3).mpr ⟨h3,R₁,h1H,R₂,h2H,hne,rfl⟩;obtain ⟨u,hu⟩:(R₁ ∩ R₂).Nonempty:=qU.mp (by omega);have h0:u∈ordinary H:=h6 (qm.mp hu).1;simp only [ordinary,qg,qj,id_eq] at h0;exact h0.2 ⟨R₁ ∩ R₂,h5,hu⟩
lemma zY {α:Type*} (f:α→α) (k:Nat) (x:α):
 (List.range k).foldl (fun V _=>f V) x=f^[k] x:=by
 induction k with
 | zero=>rfl
 | succ k ih=>rw [zP,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,qM]
lemma qc9 {n:Nat} (B:Q4 n) {V W:(Q3 n)} (h:V⊆W):
 step B V⊆step B W:=by
 intro u hu;simp only [step,ql,qj,qa,id_eq] at hu ⊢;rcases hu with huV|⟨R,⟨hRB,hnd⟩,huR⟩
 · exact Or.inl (h huV)
 · refine Or.inr ⟨R,⟨hRB,?_⟩,huR⟩
   intro hd;exact hnd (hd.mono_right h)
lemma jo {n:Nat} (B:Q4 n) (V:Q3 n):
 V⊆step B V:=Finset.subset_union_left
lemma uE {n:Nat} (B:Q4 n) (k:Nat)
 {V W:(Q3 n)} (h:V⊆W):
 (step B)^[k] V⊆(step B)^[k] W:=by
 induction k with
 | zero=>exact h
 | succ k ih=>rw [qM,qM];exact qc9 B ih
lemma j3 {n:Nat} (B:Q4 n) (k:Nat) (V:Q3 n):
 V⊆(step B)^[k] V:=by
 induction k with
 | zero=>exact Finset.Subset.rfl
 | succ k ih=>rw [qM];exact ih.trans (jo B _)
lemma ux {n:Nat} (B:Q4 n) {V:(Q3 n)}
 (hfix:step B V=V) (k:Nat):(step B)^[k] V=V:=by
 induction k with
 | zero=>rfl
 | succ k ih=>rw [qM,ih,hfix]
lemma wD {n:Nat} (B:Q4 n) (k:Nat):
 ∀ u v:Fin n,v∈(step B)^[k] {u}→u∈(step B)^[k] {v}:=by
 induction k with
 | zero=>intro u v h;simp only [Function.iterate_zero,id_eq,qd] at h ⊢;exact h.symm
 | succ k ih=>
   intro u v h;rw [qM] at h;simp only [step,ql,qj,qa,id_eq] at h;rcases h with hv|⟨R,⟨hRB,hnd⟩,hvR⟩
   · rw [qM];exact jo B _ (ih u v hv)
   · rw [vE] at hnd;rcases hnd with ⟨w,hwR,hwk⟩
     have huw:u∈(step B)^[k] {w}:=ih u w hwk
     have h0:w∈step B {v}:=by
      simp only [step,ql,qj,qa,id_eq];refine Or.inr ⟨R,⟨hRB,?_⟩,hwR⟩
      rw [vE];exact ⟨v,hvR,Finset.mem_singleton_self v⟩
     rw [ze];exact uE B k (Finset.singleton_subset_iff.mpr h0) huw
def vF {n:Nat} (C:Q3 n) (T:Q4 n):Prop:=C.Nonempty∧∀ S:Q3 n,S.Nonempty→S ⊂ C→∃ R∈T,¬ Disjoint R S∧¬ R⊆S
lemma u3 {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C) (hconn:vF C T):
 C.card≤2 * T.card+1:=by
 have h9:∀ m:Nat,∀ S:Q3 n,S.Nonempty→S⊆C→(C \ S).card≤ m→
  C.card-S.card≤2 * (T.filter (fun R=>¬ R⊆S)).card:=by
  intro m;induction m with
  | zero=>
    intro S _ hSC h0
    have h2:S=C:=by have hce:(C \ S).card=0:=Nat.eq_zero_of_le_zero h0;rw [Finset.card_sdiff_of_subset hSC] at hce;exact zo hSC (by omega)
    rw [h2,Nat.sub_self];exact Nat.zero_le _
  | succ m ih=>
    intro S hSne hSC hle;by_cases h2:S=C
    · rw [h2,Nat.sub_self]; exact Nat.zero_le _
    · have ha:S ⊂ C:=Finset.ssubset_iff_subset_ne.mpr ⟨hSC,h2⟩;rcases hconn.2 S hSne ha with ⟨R,hRT,hnd,h4⟩
      set S':=S ∪ R;have h5:S'⊆C:=Finset.union_subset hSC (hsub R hRT)
      have hSS':S ⊂ S':=by
       refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,?_⟩
       intro heq;exact h4 (heq▸Finset.subset_union_right)
      have hcard_lt:S.card<S'.card:=Finset.card_lt_card hSS'
      have h8:(C \ S').card≤ m:=by rw [Finset.card_sdiff_of_subset h5];rw [Finset.card_sdiff_of_subset hSC] at hle;have:=qH h5;have:=qH hSC;omega
      have hstep:=ih S' (hSne.mono Finset.subset_union_left) h5 h8
      have hS'card:S'.card≤S.card+2:=by
       have h1:1≤(S ∩ R).card:=by
        rw [vE] at hnd;rcases hnd with ⟨x,hxR,hxS⟩
        exact qU.mpr ⟨x,qm.mpr ⟨hxS,hxR⟩⟩
       have hu:=Finset.card_union_add_card_inter S R;rw [h3 R hRT] at hu;change S'.card+(S ∩ R).card=S.card+3 at hu;omega
      have hTdrop:(T.filter (fun R'=>¬ R'⊆S')).card+1≤
       (T.filter (fun R'=>¬ R'⊆S)).card:=by
       have hRm:R∈T.filter (fun R'=>¬ R'⊆S):=qa.mpr ⟨hRT,h4⟩
       have hRnm:R∉T.filter (fun R'=>¬ R'⊆S'):=by simp [qa,S']
       have h6:T.filter (fun R'=>¬ R'⊆S')⊆
        (T.filter (fun R'=>¬ R'⊆S)).erase R:=by
        intro R' hR';simp only [qa,qh] at hR' ⊢;refine ⟨?_,hR'.1,fun hs=>hR'.2 (hs.trans Finset.subset_union_left)⟩
        intro heq;exact hR'.2 (heq▸Finset.subset_union_right)
       have hc1:=qH h6;rw [zu hRm] at hc1;have hpos:1≤(T.filter (fun R'=>¬ R'⊆S)).card:=qU.mpr ⟨R,hRm⟩;omega
      have hCS':=qH h5;omega
 obtain ⟨u,huC⟩:=hconn.1
 have h1:=h9 C.card {u} ⟨u,Finset.mem_singleton_self u⟩
  (Finset.singleton_subset_iff.mpr huC) (qH Finset.sdiff_subset)
 have h7:T.filter (fun R=>¬ R⊆{u})=T:=by ext R;simp only [qa,and_iff_left_iff_imp];intro hRT hsub1;have:=qH hsub1;rw [h3 R hRT,z3] at this;omega
 rw [h7,z3] at h1;omega
lemma yo {n:Nat} {M:(Q4 n)}
 (h2:∀ g∈M,g.card=2)
 (hdisj:∀ g∈M,∀ h∈M,g≠h→Disjoint g h):
 (M.biUnion id).card=2 * M.card:=by
 rw [Finset.card_biUnion (t:=id) (fun g hg h hh hne=>hdisj g hg h hh hne)];simp only [id_eq];rw [Finset.sum_const_nat (fun g hg=>h2 g hg),mul_comm]
lemma u4 {n:Nat} {T:(Q4 n)}
 (hlin:∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 {g R₁ R₂:(Q3 n)} (hg2:g.card=2)
 (h1:R₁∈T) (h2:R₂∈T) (hs1:g⊆R₁) (hs2:g⊆R₂):R₁=R₂:=by
 by_contra hne;have hle:=hlin R₁ h1 R₂ h2 hne;have hge:=qH (Finset.subset_inter hs1 hs2);omega
lemma kW {n:Nat} {M:(Q4 n)}
 (h2:∀ g∈M,g.card=2)
 (hdisj:∀ g∈M,∀ h∈M,g≠h→Disjoint g h)
 {R g₁ g₂:(Q3 n)} (hR3:R.card=3)
 (h1:g₁∈M) (h2m:g₂∈M) (hs1:g₁⊆R) (hs2:g₂⊆R):g₁=g₂:=by
 by_contra hne;have hd:=hdisj g₁ h1 g₂ h2m hne;have hle:=qH (Finset.union_subset hs1 hs2);rw [Finset.card_union_of_disjoint hd,h2 g₁ h1,h2 g₂ h2m,hR3] at hle;omega
lemma vu {n:Nat} {T M:(Q4 n)}
 (h3:∀ R∈T,R.card=3)
 (hlin:∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 (h2:∀ g∈M,g.card=2)
 (hdisj:∀ g∈M,∀ h∈M,g≠h→Disjoint g h)
 (hcov:∀ R∈T,∃ g∈M,g⊆R):
 (M.filter (fun g=>∃ R∈T,g⊆R)).card=T.card:=by
 classical
 refine (Finset.card_nbij'
  (fun R=>if h:R∈T then Classical.choose (hcov R h) else ∅)
  (fun g=>if h:∃ R∈T,g⊆R then Classical.choose h else ∅)
  ?_ ?_ ?_ ?_).symm
 · intro R hR;simp only [zQ] at hR ⊢;simp only [hR,↓reduceDIte,qa];have h0:=Classical.choose_spec (hcov R hR);exact ⟨h0.1,R,hR,h0.2⟩
 · intro g hg;simp only [zQ] at hg ⊢;have hex:∃ R∈T,g⊆R:=(qa.mp hg).2;simp only [hex,↓reduceDIte];exact (Classical.choose_spec hex).1
 · intro R hR;simp only [zQ] at hR;simp only [hR,↓reduceDIte];have h0:=Classical.choose_spec (hcov R hR);have hex:∃ R'∈T,Classical.choose (hcov R hR)⊆R':=⟨R,hR,h0.2⟩;simp only [hex,↓reduceDIte];have h1:=Classical.choose_spec hex;exact u4 hlin (h2 _ h0.1) h1.1 hR h1.2 h0.2
 · intro g hg;simp only [zQ] at hg;rcases qa.mp hg with ⟨hgM,hex⟩
   simp only [hex,↓reduceDIte];have h0:=Classical.choose_spec hex;simp only [h0.1,↓reduceDIte];have h1:=Classical.choose_spec (hcov _ h0.1);exact kW h2 hdisj (h3 _ h0.1) h1.1 hgM h1.2 h0.2
def zg {n:Nat} (C:Q3 n) (T:Q4 n) (r:Fin n):
    Finset ((Q4 n)):=
 Finset.univ.filter fun M=>
  (∀ g∈M,g.card=2∧g⊆C.erase r)∧
  (∀ g∈M,∀ h∈M,g≠h→Disjoint g h)∧
  (∀ R∈T,∃ g∈M,g⊆R)
def zi {n:Nat} (C:Q3 n) (T:Q4 n):
    Finset ((Q4 n)):=
 Finset.univ.filter fun M=>
  (∀ g∈M,g.card=2∧g⊆C)∧
  (∀ g∈M,∀ h∈M,g≠h→Disjoint g h)∧
  (∀ R∈T,∃ g∈M,g⊆R)
lemma yg {n:Nat} {C:(Q3 n)} {T:(Q4 n)} {r:Fin n}
 (h3:∀ R∈T,R.card=3)
 (hlin:∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 (hr:r∈C) (hcard:C.card=2 * T.card+1)
 {M:(Q4 n)} (hM:M∈zg C T r):
 M.card=T.card∧M.biUnion id=C.erase r∧∀ g∈M,∃ R∈T,g⊆R:=by
 simp only [zg,qa,qJ,true_and] at hM;rcases hM with ⟨h7,h5,ha⟩
 have h2:∀ g∈M,g.card=2:=fun g hg=>(h7 g hg).1
 have h4:=vu h3 hlin h2 h5 ha;have hc:T.card≤M.card:=h4▸qH (yv _ M)
 have h6:M.biUnion id⊆C.erase r:=by
  intro u hu;rcases qj.mp hu with ⟨g,hgM,hug⟩
  exact (h7 g hgM).2 hug
 have h1:(M.biUnion id).card=2 * M.card:=yo h2 h5;have h0:(C.erase r).card=2 * T.card:=by rw [zu hr,hcard]; omega
 have he:M.card≤T.card:=by have:=qH h6;rw [h1,h0] at this;omega
 have h8:M.card=T.card:=le_antisymm he hc
 have hb:M.biUnion id=C.erase r:=zo h6 (by rw [h1,h0,h8])
 have h9:M.filter (fun g=>∃ R∈T,g⊆R)=M:=zo (yv _ M) (by rw [h4,h8])
 refine ⟨h8,hb,fun g hg=>?_⟩
 rw [← h9] at hg;exact (qa.mp hg).2
lemma vA {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3)
 (hlin:∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 (hcard:C.card=2 * T.card)
 {M:(Q4 n)} (hM:M∈zi C T):
 M.card=T.card∧M.biUnion id=C∧∀ g∈M,∃ R∈T,g⊆R:=by
 simp only [zi,qa,qJ,true_and] at hM;rcases hM with ⟨h6,h4,h9⟩
 have h2:∀ g∈M,g.card=2:=fun g hg=>(h6 g hg).1
 have h1:=vu h3 hlin h2 h4 h9;have hb:T.card≤M.card:=h1▸qH (yv _ M)
 have h5:M.biUnion id⊆C:=by
  intro u hu;rcases qj.mp hu with ⟨g,hgM,hug⟩
  exact (h6 g hgM).2 hug
 have h0:(M.biUnion id).card=2 * M.card:=yo h2 h4
 have hc:M.card≤T.card:=by have:=qH h5;rw [h0,hcard] at this;omega
 have h7:M.card=T.card:=le_antisymm hc hb
 have ha:M.biUnion id=C:=zo h5 (by rw [h0,hcard,h7])
 have h8:M.filter (fun g=>∃ R∈T,g⊆R)=M:=zo (yv _ M) (by rw [h1,h7])
 refine ⟨h7,ha,fun g hg=>?_⟩
 rw [← h8] at hg;exact (qa.mp hg).2
def vO {n:Nat} (T:Q4 n) (u:Fin n):Nat:=(T.filter (fun R=>u∈R)).card
def V2 {n:Nat} (C:Q3 n) (T:Q4 n):(Q3 n):=C.filter (fun u=>vO T u=2)
def v8 {n:Nat} (C:Q3 n) (T:Q4 n) (R:Q3 n):Nat:=(R ∩ V2 C T).card
lemma jH {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C) (hconn:vF C T)
 (hTne:T.Nonempty) {u:Fin n} (hu:u∈C):
 1≤vO T u:=by
 obtain ⟨R₀,hR₀⟩:=hTne;have h0:3≤C.card:=(h3 R₀ hR₀)▸qH (hsub R₀ hR₀)
 have hss:({u}:Q3 n) ⊂ C:=by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hu,?_⟩
  intro heq;rw [← heq,z3] at h0;omega
 rcases hconn.2 {u} ⟨u,Finset.mem_singleton_self u⟩ hss with ⟨R,hRT,hnd,_⟩
 rw [vE] at hnd;rcases hnd with ⟨w,hwR,hwu⟩
 rw [qd] at hwu;subst hwu;exact qU.mpr ⟨R,qa.mpr ⟨hRT,hwR⟩⟩
lemma qbQ {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C):
 C.sum (vO T)=3 * T.card:=by
 have h1:C.sum (vO T)=C.sum (fun u=>T.sum (fun R=>if u∈R then 1 else 0)):=by
  refine Finset.sum_congr rfl fun u _=>?_
  rw [vO,Finset.card_filter]
 rw [h1,Finset.sum_comm]
 have h2:T.sum (fun R=>C.sum (fun u=>if u∈R then 1 else 0))=T.sum (fun R=>R.card):=by
  refine Finset.sum_congr rfl fun R hRT=>?_
  rw [← Finset.card_filter];congr 1;ext u;simp only [qa,and_iff_right_iff_imp];exact fun hu=>hsub R hRT hu
 rw [h2,Finset.sum_const_nat (fun R hR=>h3 R hR),mul_comm]
lemma uu {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C)
 (hdeg:∀ u,vO T u≤2) (hconn:vF C T) (hTne:T.Nonempty):
 C.card+(V2 C T).card=3 * T.card:=by
 rw [← qbQ h3 hsub]
 have h1:∀ u∈C,vO T u=1+if vO T u=2 then 1 else 0:=by intro u hu;have hge:=jH h3 hsub hconn hTne hu;have hle:=hdeg u;split_ifs <;> omega
 rw [Finset.sum_congr rfl h1,Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _=>rfl),
  mul_one,← Finset.card_filter]
 rfl
lemma wP {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (hsub:∀ R∈T,R⊆C):
 T.sum (v8 C T)=2 * (V2 C T).card:=by
 have h1:T.sum (v8 C T)=T.sum (fun R=>(V2 C T).sum (fun u=>if u∈R then 1 else 0)):=by
  refine Finset.sum_congr rfl fun R _=>?_
  dsimp only [v8];rw [← Finset.card_filter];congr 1;ext u;simp only [qm,qa,and_comm]
 rw [h1,Finset.sum_comm]
 have h2:(V2 C T).sum (fun u=>T.sum (fun R=>if u∈R then 1 else 0))=
  (V2 C T).sum (fun _=>2):=by
  refine Finset.sum_congr rfl fun u hu=>?_
  rw [← Finset.card_filter];exact (qa.mp hu).2
 rw [h2,Finset.sum_const_nat (fun _ _=>rfl),mul_comm]
lemma ks {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C)
 (hdeg:∀ u,vO T u≤2) (hconn:vF C T)
 (hCgt:3<C.card) {R:(Q3 n)} (hRT:R∈T):
 1≤v8 C T R:=by
 have h2:R ⊂ C:=by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub R hRT,?_⟩
  intro heq;rw [← heq] at hCgt;have:=h3 R hRT;omega
 have h4:R.Nonempty:=qU.mp (by rw [h3 R hRT]; omega);rcases hconn.2 R h4 h2 with ⟨R',h5,hnd,h1⟩
 have hne:R'≠R:=fun heq=>h1 (heq▸Finset.Subset.rfl)
 rw [vE] at hnd;rcases hnd with ⟨v,hvR',hvR⟩
 have hv2:vO T v=2:=by
  have hle:=hdeg v
  have hge:2≤vO T v:=by
   have h0:({R,R'}:Finset _)⊆T.filter (fun X=>v∈X):=by
    intro X hX;simp only [qe,qd] at hX;rcases hX with rfl|rfl
    · exact qa.mpr ⟨hRT,hvR⟩
    · exact qa.mpr ⟨h5,hvR'⟩
   have:=qH h0;rwa [zv hne.symm] at this
  omega
 exact qU.mpr ⟨v,qm.mpr ⟨hvR,qa.mpr ⟨hsub R hRT hvR,hv2⟩⟩⟩
lemma kr {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C)
 (hdeg:∀ u,vO T u≤2) (hconn:vF C T)
 {R:(Q3 n)} (hRT:R∈T) {v:Fin n} (hleaf:R ∩ V2 C T={v}):
 let C':=C \ (R.erase v);let T':=T.erase R
 v∈R∧v∈C'∧C'.card+2=C.card∧T'.card+1=T.card∧
 (∀ w∈R.erase v,∀ R'∈T',w∉R')∧
 (∀ R'∈T',R'⊆C')∧vF C' T':=by
 have hg:v∈R ∩ V2 C T:=by rw [hleaf]; simp
 have hvR:v∈R:=(qm.mp hg).1;have hvC:v∈C:=hsub R hRT hvR;have hvC':v∈C \ (R.erase v):=qg.mpr ⟨hvC,by simp⟩;have h1:R.erase v⊆C:=(vj v R).trans (hsub R hRT);have h0:(R.erase v).card=2:=by rw [zu hvR,h3 R hRT]
 have hb:(C \ (R.erase v)).card+2=C.card:=by rw [Finset.card_sdiff_of_subset h1,h0];have:=qH h1;rw [h0] at this;omega
 have h8:(T.erase R).card+1=T.card:=by rw [zu hRT];have:=qU.mpr ⟨R,hRT⟩;omega
 have h4:∀ w∈R.erase v,∀ R'∈T.erase R,w∉R':=by
  intro w hw R' hR' hwR';rcases qh.mp hw with ⟨hwv,hwR⟩
  rcases qh.mp hR' with ⟨h2,h6⟩
  have hw2:vO T w=2:=by
   have hle:=hdeg w
   have hge:2≤vO T w:=by
    have hp:({R,R'}:Finset _)⊆T.filter (fun X=>w∈X):=by
     intro X hX;simp only [qe,qd] at hX;rcases hX with rfl|rfl
     · exact qa.mpr ⟨hRT,hwR⟩
     · exact qa.mpr ⟨h6,hwR'⟩
    have:=qH hp;rwa [zv h2.symm] at this
   omega
  have hf:w∈R ∩ V2 C T:=qm.mpr ⟨hwR,qa.mpr ⟨hsub R hRT hwR,hw2⟩⟩
  rw [hleaf,qd] at hf;exact hwv hf
 have hsub':∀ R'∈T.erase R,R'⊆C \ (R.erase v):=by
  intro R' hR' u huR';refine qg.mpr ⟨hsub R' (qE hR') huR',fun hu=>?_⟩
  exact h4 u hu R' hR' huR'
 have hconn':vF (C \ (R.erase v)) (T.erase R):=by
  refine ⟨⟨v,hvC'⟩,fun S hSne hSss=>?_⟩
  by_cases hvS:v∈S
  · set Sbig:=S ∪ R
    have h5:Sbig⊆C:=Finset.union_subset (hSss.1.trans Finset.sdiff_subset) (hsub R hRT)
    have ha:Sbig≠C:=by
     intro heq;apply hSss.2;intro x hxC';have hc:x∈Sbig:=heq.symm▸(qg.mp hxC').1;rcases ql.mp hc with hxS|hxR
     · exact hxS
     · by_cases hxv:x=v
       · exact hxv▸hvS
       · exact absurd (qh.mpr ⟨hxv,hxR⟩) (qg.mp hxC').2
    have h9:Sbig ⊂ C:=Finset.ssubset_iff_subset_ne.mpr ⟨h5,ha⟩;rcases hconn.2 Sbig (hSne.mono Finset.subset_union_left) h9 with ⟨R',h6,hnd,h7⟩
    have h2:R'≠R:=fun heq=>h7 (heq▸Finset.subset_union_right)
    have hi:R'∈T.erase R:=qh.mpr ⟨h2,h6⟩;refine ⟨R',hi,?_,fun hs=>h7 (hs.trans Finset.subset_union_left)⟩
    rw [vE] at hnd ⊢;rcases hnd with ⟨w,hwR',he⟩
    rcases ql.mp he with hwS|hwR
    · exact ⟨w,hwR',hwS⟩
    · by_cases hwv:w=v
      · exact ⟨v,hwv▸hwR',hvS⟩
      · exact absurd hwR' (h4 w (qh.mpr ⟨hwv,hwR⟩) R' hi)
  · have hh:S ⊂ C:=lt_of_lt_of_le hSss Finset.sdiff_subset;rcases hconn.2 S hSne hh with ⟨R',h6,hnd,h7⟩
    have h2:R'≠R:=by
     intro heq;subst heq;rw [vE] at hnd;rcases hnd with ⟨w,hwR,hwS⟩
     have hwC':=hSss.1 hwS;by_cases hwv:w=v
     · exact hvS (hwv▸hwS)
     · exact (qg.mp hwC').2 (qh.mpr ⟨hwv,hwR⟩)
    exact ⟨R',qh.mpr ⟨h2,h6⟩,hnd,h7⟩
 exact ⟨hvR,hvC',hb,h8,h4,hsub',hconn'⟩
lemma jO {n:Nat} {C:(Q3 n)} {T:(Q4 n)} {r:Fin n}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C)
 (hdeg:∀ u,vO T u≤2)
 (hlin:∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 (hconn:vF C T)
 (hr:r∈C) (hcard:C.card=2 * T.card+1)
 {R:(Q3 n)} (hRT:R∈T) (hrR:r∉R)
 {v:Fin n} (hleaf:R ∩ V2 C T={v}):
 (zg C T r).card=(zg (C \ (R.erase v)) (T.erase R) r).card:=by
 have hp:=kr h3 hsub hdeg hconn hRT hleaf;rcases hp with ⟨hvR,hvC',hC'card,hT'card,h5,hsub',hconn'⟩
 set g₀:=R.erase v;have hg₀2:g₀.card=2:=by rw [zu hvR,h3 R hRT]
 have hrC':r∈C \ g₀:=qg.mpr ⟨hr,fun h=>hrR (qE h)⟩
 have hg₀sub:g₀⊆C.erase r:=by
  intro w hw
  exact qh.mpr ⟨fun h=>hrR (h▸qE hw),
   hsub R hRT (qE hw)⟩
 have h2:∀ M∈zg C T r,g₀∈M:=by
  intro M hM;rcases yg h3 hlin hr hcard hM with ⟨_,hf,he⟩
  have h0:=(qa.mp hM).2;rcases h0.2.2 R hRT with ⟨gR,h8,hc⟩
  have h9:g₀⊆gR:=by
   intro w hwg₀;have hwU:w∈M.biUnion id:=by rw [hf]; exact hg₀sub hwg₀
   rcases qj.mp hwU with ⟨g,hgM,hwg⟩
   rcases he g hgM with ⟨R',hi,hgR'⟩
   have h4:R'=R:=by by_contra hne;exact h5 w hwg₀ R' (qh.mpr ⟨hne,hi⟩) (hgR' hwg)
   rw [h4] at hgR'
   have h7:=kW (fun x hx=>(h0.1 x hx).1) h0.2.1 (h3 R hRT)
    hgM h8 hgR' hc
   exact h7▸hwg
  have hg₀eq:g₀=gR:=zo h9 (by rw [hg₀2,(h0.1 gR h8).1])
  exact hg₀eq▸h8
 refine Finset.card_nbij' (fun M=>M.erase g₀) (fun M'=>insert g₀ M') ?_ ?_ ?_ ?_
 · intro M hM;simp only [zQ] at hM ⊢;have hg₀M:=h2 M hM;have h0:=(qa.mp hM).2;simp only [zg,qa,qJ,true_and];refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
   · rcases qh.mp hg with ⟨hb,hgM⟩
     refine ⟨(h0.1 g hgM).1,fun u hug=>?_⟩
     have hu1:=(h0.1 g hgM).2 hug;rcases qh.mp hu1 with ⟨hur,huC⟩
     have ha:=h0.2.1 g hgM g₀ hg₀M hb;exact qh.mpr ⟨hur,qg.mpr ⟨huC,qc.mp ha hug⟩⟩
   · exact h0.2.1 g (qE hg) h (qE hh) hne
   · rcases h0.2.2 R' (qE hR') with ⟨g,hgM,hgR'⟩
     refine ⟨g,qh.mpr ⟨?_,hgM⟩,hgR'⟩
     intro h7;subst h7;obtain ⟨w,hwg₀⟩:g₀.Nonempty:=qU.mp (by omega);exact h5 w hwg₀ R' hR' (hgR' hwg₀)
 · intro M' hM';simp only [zQ] at hM' ⊢;have h1:=(qa.mp hM').2;simp only [zg,qa,qJ,true_and]
   have h6:∀ g∈M',Disjoint g₀ g:=by intro g hg;rw [qc];intro w hwg₀ hwg;have hw:=(h1.1 g hg).2 hwg;exact (qg.mp (qE hw)).2 hwg₀
   refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
   · rcases qe.mp hg with rfl|hgM'
     · exact ⟨hg₀2,hg₀sub⟩
     · refine ⟨(h1.1 g hgM').1,fun u hug=>?_⟩
       rcases qh.mp ((h1.1 g hgM').2 hug) with ⟨hur,huC'⟩
       exact qh.mpr ⟨hur,(qg.mp huC').1⟩
   · rcases qe.mp hg with rfl|hgM' <;>
     rcases qe.mp hh with rfl|hhM'
     · exact absurd rfl hne
     · exact h6 h hhM'
     · exact (h6 g hgM').symm
     · exact h1.2.1 g hgM' h hhM' hne
   · by_cases h4:R'=R
     · rw [h4];exact ⟨g₀,vx g₀ M',vj v R⟩
     · rcases h1.2.2 R' (qh.mpr ⟨h4,hR'⟩) with ⟨g,hgM',hgR'⟩
       exact ⟨g,Finset.mem_insert_of_mem hgM',hgR'⟩
 · intro M hM;exact Finset.insert_erase (h2 M hM)
 · intro M' hM'
   have hg₀nm:g₀∉M':=by intro hg₀M';have h1:=(qa.mp hM').2;obtain ⟨w,hwg₀⟩:g₀.Nonempty:=qU.mp (by omega);have hw:=(h1.1 g₀ hg₀M').2 hwg₀;exact (qg.mp (qE hw)).2 hwg₀
   exact Finset.erase_insert hg₀nm
lemma km {n:Nat}:
 ∀ m:Nat,∀ C:Q3 n,∀ T:Q4 n,∀ r:Fin n,T.card=m→(∀ R∈T,R.card=3)→(∀ R∈T,R⊆C)→(∀ u,vO T u≤2)→(∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)→vF C T→ r∈C→C.card=2 * T.card+1→
   (zg C T r).card=1:=by
 intro m;induction m with
 | zero=>
   intro C T r hm _ _ _ _ _ hr h4;have hTe:T=∅:=Finset.card_eq_zero.mp hm;have hCe:C.erase r=∅:=Finset.card_eq_zero.mp (by rw [zu hr,h4,hm])
   have heq:zg C T r={∅}:=by
    ext M;simp only [zg,qa,qJ,true_and,qd,hTe,hCe,Finset.notMem_empty,IsEmpty.forall_iff,implies_true,and_true];constructor
    · intro hM;refine Finset.eq_empty_of_forall_notMem fun g hg=>?_
      have h1:=(hM.1 g hg).1;have h2:=Finset.subset_empty.mp (hM.1 g hg).2;rw [h2,Finset.card_empty] at h1;omega
    · rintro rfl; simp
   rw [heq,z3]
 | succ m ih=>
   intro C T r hm h3 h0 hdeg hlin h5 hr h4;by_cases hm0:m=0
   · subst hm0;rcases Finset.card_eq_one.mp hm with ⟨R,hf⟩
     have hRT:R∈T:=by rw [hf]; simp
     have hRC:R=C:=zo (h0 R hRT) (by rw [h3 R hRT,h4,hm])
     have heq:zg C T r={{C.erase r}}:=by
      ext M;simp only [zg,qa,qJ,true_and,qd];constructor
      · rintro ⟨hb,hJ,hV⟩;rcases hV R hRT with ⟨g,hgM,hgR⟩
        have hg2:=(hb g hgM).1;have hi:=(hb g hgM).2
        have hU:g=C.erase r:=zo hi (by rw [hg2,zu hr,h4,hm])
        have h00:M={g}:=by
         ext g';simp only [qd];constructor
         · intro hq;by_contra hne;have hd:=hJ g' hq g hgM hne;have hle:=qH (Finset.union_subset (hb g' hq).2 hi);rw [Finset.card_union_of_disjoint hd,(hb g' hq).1,hg2,zu hr,h4,hm] at hle;omega
         · rintro rfl; exact hgM
        rw [h00,hU]
      · rintro rfl;refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
        · rw [qd] at hg; subst hg;exact ⟨by rw [zu hr,h4,hm],Finset.Subset.rfl⟩
        · rw [qd] at hg hh; exact absurd (hg.trans hh.symm) hne
        · rw [hf,qd] at hR'; subst hR';exact ⟨C.erase r,Finset.mem_singleton_self _,hRC▸vj r C⟩
     rw [heq,z3]
   · have hTge2:2≤T.card:=by omega
     have hY:T.Nonempty:=qU.mp (by omega);have hS:3<C.card:=by omega
     have hV2:(V2 C T).card=T.card-1:=by have:=uu h3 h0 hdeg h5 hY;omega
     have hsum:T.sum (v8 C T)=2 * (T.card-1):=by rw [wP h0,hV2]
     set L:=T.filter (fun R=>v8 C T R=1)
     have hQ:2≤L.card:=by
      have hlb:L.card+2 * (T \ L).card≤T.sum (v8 C T):=by
       have hk:T.sum (v8 C T)=L.sum (v8 C T)+(T \ L).sum (v8 C T):=by rw [← Finset.sum_union Finset.disjoint_sdiff,Finset.union_sdiff_of_subset (yv _ T)]
       rw [hk]
       have hLsum:L.sum (v8 C T)=L.card:=by rw [Finset.sum_const_nat (fun R hR=>(qa.mp hR).2),mul_one]
       have hRsum:2 * (T \ L).card≤(T \ L).sum (v8 C T):=by
        calc 2 * (T \ L).card=(T \ L).sum (fun _=>2):=by
              rw [Finset.sum_const_nat (fun _ _=>rfl),mul_comm]
         _≤(T \ L).sum (v8 C T):=by
              refine Finset.sum_le_sum fun R hR=>?_
              rcases qg.mp hR with ⟨hRT,hZ⟩
              have hpos:=ks h3 h0 hdeg h5 hS hRT;have hne1:v8 C T R≠1:=fun h1=>hZ (qa.mpr ⟨hRT,h1⟩)
              omega
       omega
      have hsd:(T \ L).card=T.card-L.card:=Finset.card_sdiff_of_subset (yv _ T);have hLle:L.card≤T.card:=qH (yv _ T);omega
     by_cases hex:∃ R∈L,r∉R
     · rcases hex with ⟨R,hRL,hrR⟩
       have hRT:R∈T:=(qa.mp hRL).1;have h1:(R ∩ V2 C T).card=1:=(qa.mp hRL).2;rcases Finset.card_eq_one.mp h1 with ⟨v,hv⟩
       rw [jO h3 h0 hdeg hlin h5 hr h4 hRT hrR hv];have hp:=kr h3 h0 hdeg h5 hRT hv;rcases hp with ⟨hvR,_,hC'card,hT'card,_,h0',h5'⟩
       refine ih (C \ (R.erase v)) (T.erase R) r (by omega)
        (fun R' hR'=>h3 R' (qE hR'))
        h0'
        (fun u=>(qH (Finset.filter_subset_filter _ (vj R T))).trans (hdeg u))
        (fun R₁ h1 R₂ h2=>hlin R₁ (qE h1) R₂ (qE h2))
        h5'
        (qg.mpr ⟨hr,fun h=>hrR (qE h)⟩)
        (by omega)
     · push_neg at hex
       have hj:L⊆T.filter (fun R=>r∈R):=fun R hR=>qa.mpr ⟨(qa.mp hR).1,hex R hR⟩
       have hP:L.card≤2:=(qH hj).trans (hdeg r);have hL2:L.card=2:=le_antisymm hP hQ;rcases yk.mp hL2 with ⟨R₁,R₂,hK,hA⟩
       have hx:R₁∈L:=by rw [hA]; simp
       have ht:R₂∈L:=by rw [hA]; simp
       have h8:R₁∈T:=(qa.mp hx).1;have h7:R₂∈T:=(qa.mp ht).1;have hr1:r∈R₁:=hex R₁ hx;have hr2:r∈R₂:=hex R₂ ht
       have hC:r∈V2 C T:=by
        refine qa.mpr ⟨hr,?_⟩
        have hge:2≤vO T r:=hL2▸qH hj;exact le_antisymm (hdeg r) hge
       have hN:R₁ ∩ V2 C T={r}:=by
        refine (zo ?_ ?_).symm
        · exact Finset.singleton_subset_iff.mpr (qm.mpr ⟨hr1,hC⟩)
        · rw [z3]; exact le_of_eq (qa.mp hx).2
       have hL:R₂ ∩ V2 C T={r}:=by
        refine (zo ?_ ?_).symm
        · exact Finset.singleton_subset_iff.mpr (qm.mpr ⟨hr2,hC⟩)
        · rw [z3]; exact le_of_eq (qa.mp ht).2
       have hT2:T.card=2:=by
        by_contra hne2;have hCge7:7≤C.card:=by omega
        have hs:(R₁ ∪ R₂).card≤5:=by have:=Finset.card_union_add_card_inter R₁ R₂;have h1:1≤(R₁ ∩ R₂).card:=qU.mpr ⟨r,qm.mpr ⟨hr1,hr2⟩⟩;rw [h3 R₁ h8,h3 R₂ h7] at this;omega
        have hW:R₁ ∪ R₂ ⊂ C:=by
         refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset (h0 R₁ h8) (h0 R₂ h7),?_⟩
         intro heq; rw [heq] at hs; omega
        rcases h5.2 (R₁ ∪ R₂) ⟨r,Finset.mem_union_left _ hr1⟩ hW with ⟨R',hy,hnd,hD⟩
        have he:R'≠R₁:=fun h=>hD (h▸Finset.subset_union_left)
        have hc:R'≠R₂:=fun h=>hD (h▸Finset.subset_union_right)
        rw [vE] at hnd;rcases hnd with ⟨w,hwR',hwU⟩
        have hw2:vO T w=2:=by
         rcases ql.mp hwU with hw1|hw2'
         · have hp:({R₁,R'}:Finset _)⊆T.filter (fun X=>w∈X):=by
            intro X hX; simp only [qe,qd] at hX;rcases hX with rfl|rfl
            · exact qa.mpr ⟨h8,hw1⟩
            · exact qa.mpr ⟨hy,hwR'⟩
           have hge:2≤vO T w:=(zv he.symm)▸qH hp;exact le_antisymm (hdeg w) hge
         · have hp:({R₂,R'}:Finset _)⊆T.filter (fun X=>w∈X):=by
            intro X hX; simp only [qe,qd] at hX;rcases hX with rfl|rfl
            · exact qa.mpr ⟨h7,hw2'⟩
            · exact qa.mpr ⟨hy,hwR'⟩
           have hge:2≤vO T w:=(zv hc.symm)▸qH hp;exact le_antisymm (hdeg w) hge
        have hwr:w=r:=by
         rcases ql.mp hwU with hw1|hw2'
         · have:w∈R₁ ∩ V2 C T:=qm.mpr ⟨hw1,qa.mpr ⟨h0 R₁ h8 hw1,hw2⟩⟩;rwa [hN,qd] at this
         · have:w∈R₂ ∩ V2 C T:=qm.mpr ⟨hw2',qa.mpr ⟨h0 R₂ h7 hw2',hw2⟩⟩;rwa [hL,qd] at this
        subst hwr
        have hT:({R₁,R₂,R'}:Finset _)⊆T.filter (fun X=>w∈X):=by
         intro X hX; simp only [qe,qd] at hX;rcases hX with rfl|rfl|rfl
         · exact qa.mpr ⟨h8,hr1⟩
         · exact qa.mpr ⟨h7,hr2⟩
         · exact qa.mpr ⟨hy,hwR'⟩
        have hc3:({R₁,R₂,R'}:Finset _).card=3:=by rw [Finset.card_insert_of_notMem,zv hc.symm];simp [hK,he.symm]
        have:=hc3▸qH hT;have hdw:=hdeg w;dsimp only [vO] at hdw;omega
       have hf:T={R₁,R₂}:=
        (zo (yv _ T)
          (by rw [hL2,hT2])).symm.trans hA
       have hl:R₁ ∩ R₂={r}:=by
        have hle:=hlin R₁ h8 R₂ h7 hK;refine (zo ?_ ?_).symm
        · exact Finset.singleton_subset_iff.mpr (qm.mpr ⟨hr1,hr2⟩)
        · rw [z3]; exact hle
       have ha:(R₁.erase r).card=2:=by rw [zu hr1,h3 R₁ h8]
       have h9:(R₂.erase r).card=2:=by rw [zu hr2,h3 R₂ h7]
       have h6:Disjoint (R₁.erase r) (R₂.erase r):=by rw [qc];intro u hu1 hu2;have huI:u∈R₁ ∩ R₂:=qm.mpr ⟨qE hu1,qE hu2⟩;rw [hl,qd] at huI;exact (qh.mp hu1).1 huI
       have heq:zg C T r={{R₁.erase r,R₂.erase r}}:=by
        ext M;simp only [zg,qa,qJ,true_and,qd];constructor
        · intro hM
          have hO:M∈zg C T r:=by simp only [zg,qa,qJ,true_and]; exact hM
          rcases yg h3 hlin hr h4 hO with ⟨hz,_,_⟩
          rcases hM.2.2 R₁ h8 with ⟨g₁,ho,hI⟩
          rcases hM.2.2 R₂ h7 with ⟨g₂,hn,hG⟩
          have hH:g₁=R₁.erase r:=by
           refine zo (fun u hu=>qh.mpr
            ⟨(qh.mp ((hM.1 g₁ ho).2 hu)).1,hI hu⟩) ?_
           rw [ha,(hM.1 g₁ ho).1]
          have hF:g₂=R₂.erase r:=by
           refine zo (fun u hu=>qh.mpr
            ⟨(qh.mp ((hM.1 g₂ hn).2 hu)).1,hG hu⟩) ?_
           rw [h9,(hM.1 g₂ hn).1]
          have hE:R₁.erase r≠R₂.erase r:=by intro h;obtain ⟨w,hw⟩:(R₁.erase r).Nonempty:=qU.mp (by omega);exact qc.mp h6 hw (h▸hw)
          have hB:({R₁.erase r,R₂.erase r}:Finset _)⊆M:=by
           intro g hg; simp only [qe,qd] at hg;rcases hg with rfl|rfl
           · exact hH▸ho
           · exact hF▸hn
          exact (zo hB (by rw [zv hE,hz,hT2])).symm
        · rintro rfl;refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
          · simp only [qe,qd] at hg;rcases hg with rfl|rfl
            · exact ⟨ha,Finset.erase_subset_erase r (h0 R₁ h8)⟩
            · exact ⟨h9,Finset.erase_subset_erase r (h0 R₂ h7)⟩
          · simp only [qe,qd] at hg hh;rcases hg with rfl|rfl <;> rcases hh with rfl|rfl
            · exact absurd rfl hne
            · exact h6
            · exact h6.symm
            · exact absurd rfl hne
          · rw [hf] at hR'; simp only [qe,qd] at hR';rcases hR' with h|h
            · rw [h]; exact ⟨R₁.erase r,by simp,vj r R₁⟩
            · rw [h]; exact ⟨R₂.erase r,by simp,vj r R₂⟩
       rw [heq,z3]
lemma u0 {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C)
 (hdeg:∀ u,vO T u≤2)
 (hlin:∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 (hconn:vF C T)
 (hcard:C.card=2 * T.card)
 {R:(Q3 n)} (hRT:R∈T)
 {v:Fin n} (hleaf:R ∩ V2 C T={v}):
 (zi C T).card=(zi (C \ (R.erase v)) (T.erase R)).card:=by
 have hp:=kr h3 hsub hdeg hconn hRT hleaf;rcases hp with ⟨hvR,_,_,_,h5,_,_⟩
 set g₀:=R.erase v;have hg₀2:g₀.card=2:=by rw [zu hvR,h3 R hRT]
 have hg₀sub:g₀⊆C:=(vj v R).trans (hsub R hRT)
 have h2:∀ M∈zi C T,g₀∈M:=by
  intro M hM;rcases vA h3 hlin hcard hM with ⟨_,hf,he⟩
  have h0:=(qa.mp hM).2;rcases h0.2.2 R hRT with ⟨gR,h8,hc⟩
  have h9:g₀⊆gR:=by
   intro w hwg₀;have hwU:w∈M.biUnion id:=by rw [hf]; exact hg₀sub hwg₀
   rcases qj.mp hwU with ⟨g,hgM,hwg⟩
   rcases he g hgM with ⟨R',hi,hgR'⟩
   have h4:R'=R:=by by_contra hne;exact h5 w hwg₀ R' (qh.mpr ⟨hne,hi⟩) (hgR' hwg)
   rw [h4] at hgR'
   have h7:=kW (fun x hx=>(h0.1 x hx).1) h0.2.1 (h3 R hRT)
    hgM h8 hgR' hc
   exact h7▸hwg
  have hg₀eq:g₀=gR:=zo h9 (by rw [hg₀2,(h0.1 gR h8).1])
  exact hg₀eq▸h8
 refine Finset.card_nbij' (fun M=>M.erase g₀) (fun M'=>insert g₀ M') ?_ ?_ ?_ ?_
 · intro M hM;simp only [zQ] at hM ⊢;have hg₀M:=h2 M hM;have h0:=(qa.mp hM).2;simp only [zi,qa,qJ,true_and];refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
   · rcases qh.mp hg with ⟨hb,hgM⟩
     have ha:=h0.2.1 g hgM g₀ hg₀M hb
     exact ⟨(h0.1 g hgM).1,fun u hug=>qg.mpr ⟨(h0.1 g hgM).2 hug,qc.mp ha hug⟩⟩
   · exact h0.2.1 g (qE hg) h (qE hh) hne
   · rcases h0.2.2 R' (qE hR') with ⟨g,hgM,hgR'⟩
     refine ⟨g,qh.mpr ⟨?_,hgM⟩,hgR'⟩
     intro h7;subst h7;obtain ⟨w,hwg₀⟩:g₀.Nonempty:=qU.mp (by omega);exact h5 w hwg₀ R' hR' (hgR' hwg₀)
 · intro M' hM';simp only [zQ] at hM' ⊢;have h1:=(qa.mp hM').2;simp only [zi,qa,qJ,true_and]
   have h6:∀ g∈M',Disjoint g₀ g:=by intro g hg;rw [qc];intro w hwg₀ hwg;exact (qg.mp ((h1.1 g hg).2 hwg)).2 hwg₀
   refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
   · rcases qe.mp hg with rfl|hgM'
     · exact ⟨hg₀2,hg₀sub⟩
     · exact ⟨(h1.1 g hgM').1,((h1.1 g hgM').2).trans Finset.sdiff_subset⟩
   · rcases qe.mp hg with rfl|hgM' <;>
     rcases qe.mp hh with rfl|hhM'
     · exact absurd rfl hne
     · exact h6 h hhM'
     · exact (h6 g hgM').symm
     · exact h1.2.1 g hgM' h hhM' hne
   · by_cases h4:R'=R
     · rw [h4];exact ⟨g₀,vx g₀ M',vj v R⟩
     · rcases h1.2.2 R' (qh.mpr ⟨h4,hR'⟩) with ⟨g,hgM',hgR'⟩
       exact ⟨g,Finset.mem_insert_of_mem hgM',hgR'⟩
 · intro M hM;exact Finset.insert_erase (h2 M hM)
 · intro M' hM'
   have hg₀nm:g₀∉M':=by intro hg₀M';have h1:=(qa.mp hM').2;obtain ⟨w,hwg₀⟩:g₀.Nonempty:=qU.mp (by omega);exact (qg.mp ((h1.1 g₀ hg₀M').2 hwg₀)).2 hwg₀
   exact Finset.erase_insert hg₀nm
lemma js {n:Nat} {C:(Q3 n)} {T:(Q4 n)}
 (h3:∀ R∈T,R.card=3) (hsub:∀ R∈T,R⊆C)
 (hdeg:∀ u,vO T u≤2) (hconn:vF C T)
 (hall2:∀ R∈T,v8 C T R=2)
 {R₀:(Q3 n)} (hR₀:R₀∈T) {a₀ v₁ v₂:Fin n}
 (hR₀V2:R₀ ∩ V2 C T={v₁,v₂}) (hv12:v₁≠v₂)
 (ha₀:R₀ \ V2 C T={a₀}):
 vF (C.erase a₀) (T.erase R₀):=by
 have ha₀m:a₀∈R₀ \ V2 C T:=by rw [ha₀]; simp
 have ha₀R₀:a₀∈R₀:=(qg.mp ha₀m).1;have ha₀nV2:a₀∉V2 C T:=(qg.mp ha₀m).2;have ha₀C:a₀∈C:=hsub R₀ hR₀ ha₀R₀;have hj:v₁∈R₀ ∩ V2 C T:=by rw [hR₀V2]; simp
 have hi:v₂∈R₀ ∩ V2 C T:=by rw [hR₀V2]; simp
 have hv1R₀:v₁∈R₀:=(qm.mp hj).1;have hv2R₀:v₂∈R₀:=(qm.mp hi).1;have hg:v₁∈V2 C T:=(qm.mp hj).2;have hf:v₂∈V2 C T:=(qm.mp hi).2;have hv1a₀:v₁≠a₀:=fun h=>ha₀nV2 (h▸hg)
 have hv2a₀:v₂≠a₀:=fun h=>ha₀nV2 (h▸hf)
 have ha₀only:∀ R'∈T.erase R₀,a₀∉R':=by
  intro R' hR' ha₀R';rcases qh.mp hR' with ⟨hne,h8⟩
  have hge:2≤vO T a₀:=by
   have hp:({R₀,R'}:Finset _)⊆T.filter (fun X=>a₀∈X):=by
    intro X hX; simp only [qe,qd] at hX;rcases hX with rfl|rfl
    · exact qa.mpr ⟨hR₀,ha₀R₀⟩
    · exact qa.mpr ⟨h8,ha₀R'⟩
   exact (zv hne.symm)▸qH hp
  exact ha₀nV2 (qa.mpr ⟨ha₀C,le_antisymm (hdeg a₀) hge⟩)
 have hR₀eq:R₀={a₀,v₁,v₂}:=by
  ext u;by_cases hu:u∈V2 C T
  · have:u∈R₀↔u∈R₀ ∩ V2 C T:=by simp [hu]
    rw [this,hR₀V2];have hua:u≠a₀:=fun h=>ha₀nV2 (h▸hu)
    simp [hua]
  · have:u∈R₀↔u∈R₀ \ V2 C T:=by simp [hu]
    rw [this,ha₀];have hu1:u≠v₁:=fun h=>hu (h▸hg)
    have hu2:u≠v₂:=fun h=>hu (h▸hf)
    simp [hu1,hu2]
 refine ⟨⟨v₁,qh.mpr ⟨hv1a₀,hsub R₀ hR₀ hv1R₀⟩⟩,fun S hSne he=>?_⟩
 by_contra hno;push_neg at hno
 have h5:∀ R'∈T.erase R₀,R'⊆S∨Disjoint R' S:=by
  intro R' hR';by_cases hd:Disjoint R' S
  · exact Or.inr hd
  · exact Or.inl (hno R' hR' hd)
 have h0:¬ (v₁∉S∧v₂∉S):=by
  rintro ⟨h1,h2⟩;have ha₀S:a₀∉S:=fun h=>(qh.mp (he.1 h)).1 rfl
  have hdR₀:Disjoint R₀ S:=by rw [hR₀eq,qc];intro u hu;simp only [qe,qd] at hu;rcases hu with rfl|rfl|rfl <;> assumption
  have hl:S ⊂ C:=lt_of_lt_of_le he (vj a₀ C);rcases hconn.2 S hSne hl with ⟨R,hRT,hnd,hb⟩
  have hr:R≠R₀:=fun h=>hnd (h▸hdR₀)
  rcases h5 R (qh.mpr ⟨hr,hRT⟩) with hs|hd
  · exact hb hs
  · exact hnd hd
 have h4:¬ (v₁∈S∧v₂∈S):=by
  rintro ⟨h1,h2⟩;set S':=insert a₀ S
  have hm:S' ⊂ C:=by
   refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset ha₀C (he.1.trans (vj a₀ C)),?_⟩
   intro heq;apply he.2;intro x hx;rcases qh.mp hx with ⟨hxa,hxC⟩
   have hxS':x∈S':=heq.symm▸hxC;rcases qe.mp hxS' with rfl|hxS
   · exact absurd rfl hxa
   · exact hxS
  rcases hconn.2 S' (hSne.mono (Finset.subset_insert a₀ S)) hm with ⟨R,hRT,hnd,hb⟩
  by_cases hn:R=R₀
  · subst hn;apply hb;rw [hR₀eq];intro u hu; simp only [qe,qd] at hu;rcases hu with h|h|h
    · rw [h]; exact vx a₀ S
    · rw [h]; exact Finset.mem_insert_of_mem h1
    · rw [h]; exact Finset.mem_insert_of_mem h2
  · have hRm:R∈T.erase R₀:=qh.mpr ⟨hn,hRT⟩;rcases h5 R hRm with hs|hd
    · exact hb (hs.trans (Finset.subset_insert a₀ S))
    · apply hnd;rw [Finset.disjoint_right];intro u huS';rcases qe.mp huS' with rfl|huS
      · exact ha₀only R hRm
      · exact Finset.disjoint_right.mp hd huS
 have h6:∀ w w',(w=v₁∧w'=v₂∨w=v₂∧w'=v₁)→w∈S→w'∉S→False:=by
  intro w w' hww hwS hw'nS;have hwR₀:w∈R₀:=by rcases hww with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  have ho:w∈V2 C T:=by rcases hww with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  have hw'V2:w'∈V2 C T:=by rcases hww with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  set TS:=(T.erase R₀).filter (fun R'=>R'⊆S)
  have hv:TS.sum (v8 C T)=2 * TS.card:=by
   rw [Finset.sum_const_nat (fun R' hR'=>hall2 R' (qE (qa.mp hR').1)),
    mul_comm]
  have h9:TS.sum (v8 C T)=(S ∩ V2 C T).sum (fun u=>(TS.filter (fun R'=>u∈R')).card):=by
   have hA:TS.sum (v8 C T)=TS.sum (fun R'=>(S ∩ V2 C T).sum (fun u=>if u∈R' then 1 else 0)):=by
    refine Finset.sum_congr rfl fun R' hR'=>?_
    dsimp only [v8];rw [← Finset.card_filter];congr 1;ext u;simp only [qm,qa];constructor
    · rintro ⟨huR',h7⟩;exact ⟨⟨(qa.mp hR').2 huR',h7⟩,huR'⟩
    · rintro ⟨⟨_,h7⟩,huR'⟩;exact ⟨huR',h7⟩
   rw [hA,Finset.sum_comm];refine Finset.sum_congr rfl fun u _=>?_
   rw [Finset.card_filter]
  have hc:∀ u∈S ∩ V2 C T,(TS.filter (fun R'=>u∈R')).card=if u=w then 1 else 2:=by
   intro u hu;rcases qm.mp hu with ⟨huS,h7⟩
   have hu2:(T.filter (fun R'=>u∈R')).card=2:=(qa.mp h7).2
   have hq:TS.filter (fun R'=>u∈R')=(T.filter (fun R'=>u∈R')).erase R₀:=by
    ext R';simp only [TS,qa,qh];constructor
    · rintro ⟨⟨⟨hne,h8⟩,_⟩,huR'⟩;exact ⟨hne,h8,huR'⟩
    · rintro ⟨hne,h8,huR'⟩;have ht:R'∈T.erase R₀:=qh.mpr ⟨hne,h8⟩;rcases h5 R' ht with hs|hd
      · exact ⟨⟨⟨hne,h8⟩,hs⟩,huR'⟩
      · exact absurd huS (qc.mp hd huR')
   rw [hq];by_cases huw:u=w
   · subst huw;rw [if_pos rfl,zu (qa.mpr ⟨hR₀,hwR₀⟩),hu2]
   · rw [if_neg huw]
     have huR₀:u∉R₀:=by
      intro h;have:u∈R₀ ∩ V2 C T:=qm.mpr ⟨h,h7⟩;rw [hR₀V2] at this;simp only [qe,qd] at this;rcases hww with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · rcases this with rfl|rfl
        · exact huw rfl
        · exact hw'nS huS
      · rcases this with rfl|rfl
        · exact hw'nS huS
        · exact huw rfl
     rw [Finset.erase_eq_of_notMem (s:=T.filter (fun R'=>u∈R'))
      (fun h=>huR₀ (qa.mp h).2),hu2]
  rw [Finset.sum_congr rfl hc] at h9;have hh:w∈S ∩ V2 C T:=qm.mpr ⟨hwS,ho⟩;rw [← Finset.add_sum_erase _ _ hh,if_pos rfl] at h9
  have hk:((S ∩ V2 C T).erase w).sum (fun u=>if u=w then 1 else 2)=
   2 * ((S ∩ V2 C T).erase w).card:=by
   rw [Finset.sum_const_nat (fun u hu=>if_neg (qh.mp hu).1),mul_comm]
  rw [hk,hv] at h9;omega
 by_cases h1:v₁∈S
 · by_cases h2:v₂∈S
   · exact h4 ⟨h1,h2⟩
   · exact h6 v₁ v₂ (Or.inl ⟨rfl,rfl⟩) h1 h2
 · by_cases h2:v₂∈S
   · exact h6 v₂ v₁ (Or.inr ⟨rfl,rfl⟩) h2 h1
   · exact h0 ⟨h1,h2⟩
lemma u5 {n:Nat}:
 ∀ m:Nat,∀ C:Q3 n,∀ T:Q4 n,T.card=m→(∀ R∈T,R.card=3)→(∀ R∈T,R⊆C)→(∀ u,vO T u≤2)→(∀ R₁∈T,∀ R₂∈T,R₁≠R₂→(R₁ ∩ R₂).card≤1)→vF C T→C.card=2 * T.card→
   (zi C T).card=2:=by
 intro m;induction m with
 | zero=>intro C T hm _ _ _ _ h6 h7;have:=qU.mpr h6.1;omega
 | succ m ih=>
   intro C T hm h3 h0 h8 hlin h6 h7
   have hTge3:3≤T.card:=by
    by_contra hlt;by_cases h1:T.card=1
    · rcases Finset.card_eq_one.mp h1 with ⟨R,hi⟩
      have hRT:R∈T:=by rw [hi]; simp
      have:=qH (h0 R hRT);rw [h3 R hRT] at this;omega
    · have h2:T.card=2:=by omega
      rcases yk.mp h2 with ⟨R₁,R₂,hne,hi⟩
      have h1T:R₁∈T:=by rw [hi]; simp
      have h2T:R₂∈T:=by rw [hi]; simp
      have hu:=Finset.card_union_add_card_inter R₁ R₂;have hle:=hlin R₁ h1T R₂ h2T hne;have hsubU:=qH (Finset.union_subset (h0 R₁ h1T) (h0 R₂ h2T));rw [h3 R₁ h1T,h3 R₂ h2T] at hu;omega
   have hC:T.Nonempty:=qU.mp (by omega);have hD:3<C.card:=by omega
   have hV2:(V2 C T).card=T.card:=by have:=uu h3 h0 h8 h6 hC;omega
   have hsum:T.sum (v8 C T)=2 * T.card:=by rw [wP h0,hV2]
   by_cases he:∃ R∈T,v8 C T R=1
   · rcases he with ⟨R,hRT,hE⟩
     rcases Finset.card_eq_one.mp hE with ⟨v,hv⟩
     rw [u0 h3 h0 h8 hlin h6 h7 hRT hv];have hp:=kr h3 h0 h8 h6 hRT hv;rcases hp with ⟨_,_,hC'card,hT'card,_,h0',h6'⟩
     exact ih (C \ (R.erase v)) (T.erase R) (by omega)
      (fun R' hR'=>h3 R' (qE hR'))
      h0'
      (fun u=>(qH (Finset.filter_subset_filter _ (vj R T))).trans (h8 u))
      (fun R₁ h1 R₂ h2=>hlin R₁ (qE h1) R₂ (qE h2))
      h6'
      (by omega)
   · push_neg at he
     have h9:∀ R∈T,2≤v8 C T R:=by intro R hRT;have hpos:=ks h3 h0 h8 h6 hD hRT;have hne1:=he R hRT;omega
     have hl:∀ R∈T,v8 C T R=2:=by
      intro R hRT;by_contra hne2;have hgt2:3≤v8 C T R:=by have:=h9 R hRT; omega
      have hsumge:2 * T.card+1≤T.sum (v8 C T):=by
       rw [← Finset.add_sum_erase _ _ hRT]
       have hk:2 * (T.erase R).card≤(T.erase R).sum (v8 C T):=by
        calc 2 * (T.erase R).card=(T.erase R).sum (fun _=>2):=by
              rw [Finset.sum_const_nat (fun _ _=>rfl),mul_comm]
         _≤(T.erase R).sum (v8 C T):=Finset.sum_le_sum fun R' hR'=>h9 R' (qE hR')
       rw [zu hRT] at hk;change 2 * (T.card-1)≤∑ x∈T.erase R,v8 C T x at hk;omega
      omega
     obtain ⟨R₀,hR₀⟩:=hC;have hA:(R₀ ∩ V2 C T).card=2:=hl R₀ hR₀;rcases yk.mp hA with ⟨v₁,v₂,hy,hR₀V2⟩
     have hs:(R₀ \ V2 C T).card=1:=by have h:=Finset.card_sdiff_add_card_inter R₀ (V2 C T);rw [h3 R₀ hR₀,hA] at h;omega
     rcases Finset.card_eq_one.mp hs with ⟨a₀,ha₀⟩
     have h6':=js h3 h0 h8 h6 hl hR₀ hR₀V2 hy ha₀;have ha₀m:a₀∈R₀ \ V2 C T:=by rw [ha₀]; simp
     have ha₀R₀:a₀∈R₀:=(qg.mp ha₀m).1;have ha₀nV2:a₀∉V2 C T:=(qg.mp ha₀m).2;have ha₀C:a₀∈C:=h0 R₀ hR₀ ha₀R₀;have ho:v₁∈R₀ ∩ V2 C T:=by rw [hR₀V2]; simp
     have hn:v₂∈R₀ ∩ V2 C T:=by rw [hR₀V2]; simp
     have hv1R₀:v₁∈R₀:=(qm.mp ho).1;have hv2R₀:v₂∈R₀:=(qm.mp hn).1;have hv1a₀:v₁≠a₀:=fun h=>ha₀nV2 (h▸(qm.mp ho).2)
     have hv2a₀:v₂≠a₀:=fun h=>ha₀nV2 (h▸(qm.mp hn).2)
     have ha₀only:∀ R'∈T.erase R₀,a₀∉R':=by
      intro R' hR' ha₀R';rcases qh.mp hR' with ⟨hne,ht⟩
      have hge:2≤vO T a₀:=by
       have hp:({R₀,R'}:Finset _)⊆T.filter (fun X=>a₀∈X):=by
        intro X hX; simp only [qe,qd] at hX;rcases hX with rfl|rfl
        · exact qa.mpr ⟨hR₀,ha₀R₀⟩
        · exact qa.mpr ⟨ht,ha₀R'⟩
       exact (zv hne.symm)▸qH hp
      exact ha₀nV2 (qa.mpr ⟨ha₀C,le_antisymm (h8 a₀) hge⟩)
     have h0':∀ R'∈T.erase R₀,R'⊆C.erase a₀:=fun R' hR' u hu=>
      qh.mpr ⟨fun h=>ha₀only R' hR' (h▸hu),
       h0 R' (qE hR') hu⟩
     have hR₀eq:R₀={a₀,v₁,v₂}:=by
      ext u;by_cases hu:u∈V2 C T
      · have:u∈R₀↔u∈R₀ ∩ V2 C T:=by simp [hu]
        rw [this,hR₀V2];have hua:u≠a₀:=fun h=>ha₀nV2 (h▸hu)
        simp [hua]
      · have:u∈R₀↔u∈R₀ \ V2 C T:=by simp [hu]
        rw [this,ha₀];have hu1:u≠v₁:=fun h=>hu (h▸(qm.mp ho).2)
        have hu2:u≠v₂:=fun h=>hu (h▸(qm.mp hn).2)
        simp [hu1,hu2]
     set g₁:(Q3 n):={a₀,v₁};set g₂:(Q3 n):={a₀,v₂};set F₁:=(zi C T).filter (fun M=>g₁∈M);set F₂:=(zi C T).filter (fun M=>g₂∈M)
     have hx:Disjoint F₁ F₂:=by
      rw [qc];intro M hM1 hM2;have h4:=(qa.mp (qa.mp hM1).1).2;have hg1:g₁∈M:=(qa.mp hM1).2;have hg2:g₂∈M:=(qa.mp hM2).2
      have hr:g₁≠g₂:=by intro h;have:v₁∈g₂:=h▸(by simp [g₁]);simp [g₂,hv1a₀,hy] at this
      have hd:=h4.2.1 g₁ hg1 g₂ hg2 hr;exact qc.mp hd (by simp [g₁]:a₀∈g₁) (by simp [g₂])
     have hj:zi C T=F₁ ∪ F₂:=by
      ext M;simp only [F₁,F₂,ql,qa];constructor
      · intro hM;rcases vA h3 hlin h7 hM with ⟨_,hJ,hI⟩
        have h4:=(qa.mp hM).2;have ha₀U:a₀∈M.biUnion id:=by rw [hJ]; exact ha₀C
        rcases qj.mp ha₀U with ⟨g,hgM,ha₀g⟩
        dsimp only [id_eq] at ha₀g;rcases hI g hgM with ⟨R',ht,hgR'⟩
        have hb:R'=R₀:=by by_contra hne;exact ha₀only R' (qh.mpr ⟨hne,ht⟩) (hgR' ha₀g)
        rw [hb] at hgR'
        have hH:(g.erase a₀).card=1:=by rw [zu ha₀g,(h4.1 g hgM).1]
        rcases Finset.card_eq_one.mp hH with ⟨w,hw⟩
        have hwm:w∈g.erase a₀:=by rw [hw]; simp
        rcases qh.mp hwm with ⟨hwa₀,hwg⟩
        have hc:g={a₀,w}:=by
         ext u;by_cases hua:u=a₀
         · rw [hua]; simp [ha₀g]
         · have:u∈g.erase a₀↔u=w:=by rw [hw]; simp
           rw [qh] at this;have hz:u∈g↔u=w:=by tauto
           simp [qe,qd,hua,hz]
        have hwR₀:w∈R₀:=hgR' hwg;rw [hR₀eq] at hwR₀;simp only [qe,qd,hwa₀,false_or] at hwR₀;rcases hwR₀ with hwv|hwv
        · rw [hwv] at hc; rw [hc] at hgM; exact Or.inl ⟨hM,hgM⟩
        · rw [hwv] at hc; rw [hc] at hgM; exact Or.inr ⟨hM,hgM⟩
      · rintro (⟨hM,_⟩|⟨hM,_⟩) <;> exact hM
     have hB:∀ w:Fin n,w∈R₀→w≠a₀→
      ((zi C T).filter (fun M=>({a₀,w}:Q3 n)∈M)).card=
      (zg (C.erase a₀) (T.erase R₀) w).card:=by
      intro w hwR₀ hwa₀;set gw:(Q3 n):={a₀,w};have hG:gw.card=2:=zv hwa₀.symm
      have hq:gw⊆C:=by
       intro u hu; simp only [gw,qe,qd] at hu;rcases hu with rfl|rfl
       · exact ha₀C
       · exact h0 R₀ hR₀ hwR₀
      refine Finset.card_nbij' (fun M=>M.erase gw) (fun M'=>insert gw M') ?_ ?_ ?_ ?_
      · intro M hM;simp only [zQ] at hM ⊢;rcases qa.mp hM with ⟨hMF,hF⟩
        have h4:=(qa.mp hMF).2;simp only [zg,qa,qJ,true_and];refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩
        · rcases qh.mp hg with ⟨hr,hgM⟩
          have hd:=h4.2.1 g hgM gw hF hr;refine ⟨(h4.1 g hgM).1,fun u hug=>?_⟩
          have hun:u∉gw:=qc.mp hd hug;simp only [gw,qe,qd,not_or] at hun;exact qh.mpr ⟨hun.2,qh.mpr ⟨hun.1,(h4.1 g hgM).2 hug⟩⟩
        · exact h4.2.1 g (qE hg) h (qE hh) hne
        · rcases h4.2.2 R' (qE hR') with ⟨g,hgM,hgR'⟩
          refine ⟨g,qh.mpr ⟨?_,hgM⟩,hgR'⟩
          intro hc;exact ha₀only R' hR' (hgR' (hc▸vx a₀ {w}))
      · intro M' hM';simp only [zQ] at hM' ⊢;have h5:=(qa.mp hM').2;simp only [qa,zi,qJ,true_and]
        have hf:∀ g∈M',Disjoint gw g:=by
         intro g hg;rw [qc];intro u hugw hug;have hu:=(h5.1 g hg).2 hug;rcases qh.mp hu with ⟨huw,hua⟩
         rcases qh.mp hua with ⟨hua₀,_⟩
         simp only [gw,qe,qd] at hugw;rcases hugw with rfl|rfl
         · exact hua₀ rfl
         · exact huw rfl
        refine ⟨⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_⟩,
         vx gw M'⟩
        · rcases qe.mp hg with rfl|hgM'
          · exact ⟨hG,hq⟩
          · exact ⟨(h5.1 g hgM').1,((h5.1 g hgM').2).trans ((vj w _).trans (vj a₀ C))⟩
        · rcases qe.mp hg with rfl|hgM' <;>
          rcases qe.mp hh with rfl|hhM'
          · exact absurd rfl hne
          · exact hf h hhM'
          · exact (hf g hgM').symm
          · exact h5.2.1 g hgM' h hhM' hne
        · by_cases hb:R'=R₀
          · subst hb;refine ⟨gw,vx gw M',fun u hu=>?_⟩
            simp only [gw,qe,qd] at hu;rcases hu with rfl|rfl <;> assumption
          · rcases h5.2.2 R' (qh.mpr ⟨hb,hR'⟩) with ⟨g,hgM',hgR'⟩
            exact ⟨g,Finset.mem_insert_of_mem hgM',hgR'⟩
      · intro M hM;exact Finset.insert_erase (qa.mp hM).2
      · intro M' hM'
        have hnm:gw∉M':=by intro h;have h5:=(qa.mp hM').2;have hu:=(h5.1 gw h).2 (vx a₀ {w});exact (qh.mp (qE hu)).1 rfl
        exact Finset.erase_insert hnm
     have h7':(C.erase a₀).card=2 * (T.erase R₀).card+1:=by rw [zu ha₀C,zu hR₀,h7];omega
     have hc1:(zg (C.erase a₀) (T.erase R₀) v₁).card=1:=
      km (T.erase R₀).card (C.erase a₀) (T.erase R₀) v₁ rfl
       (fun R' hR'=>h3 R' (qE hR'))
       h0'
       (fun u=>(qH (Finset.filter_subset_filter _ (vj R₀ T))).trans (h8 u))
       (fun R₁ h1 R₂ h2=>hlin R₁ (qE h1) R₂ (qE h2))
       h6'
       (qh.mpr ⟨hv1a₀,h0 R₀ hR₀ hv1R₀⟩)
       h7'
     have hc2:(zg (C.erase a₀) (T.erase R₀) v₂).card=1:=
      km (T.erase R₀).card (C.erase a₀) (T.erase R₀) v₂ rfl
       (fun R' hR'=>h3 R' (qE hR'))
       h0'
       (fun u=>(qH (Finset.filter_subset_filter _ (vj R₀ T))).trans (h8 u))
       (fun R₁ h1 R₂ h2=>hlin R₁ (qE h1) R₂ (qE h2))
       h6'
       (qh.mpr ⟨hv2a₀,h0 R₀ hR₀ hv2R₀⟩)
       h7'
     rw [hj,Finset.card_union_of_disjoint hx,hB v₁ hv1R₀ hv1a₀,hB v₂ hv2R₀ hv2a₀,hc1,hc2]
lemma uc {α:Type} {β:α→Type} [DecidableEq α] [∀ a,DecidableEq (β a)]
 (s:Finset α) (t:∀ a,Finset (β a)):
 (s.pi t).card=s.prod (fun a=>(t a).card):=by
 induction s using Finset.induction_on with
 | empty=>simp [Finset.pi_empty]
 | insert a s ha ih=>
   rw [Finset.pi_insert ha,Finset.prod_insert ha,← ih];rw [Finset.card_biUnion]
   · have hc:∀ b∈t a,((s.pi t).image (Finset.Pi.cons s a b)).card=(s.pi t).card:=
      fun b _=>Finset.card_image_of_injective _ (Finset.Pi.cons_injective ha)
     rw [Finset.sum_const_nat hc]
   · intro b₁ _ b₂ _ hne;dsimp only [Function.onFun];rw [qc];intro f hf1 hf2;rcases qN.mp hf1 with ⟨g₁,_,rfl⟩
     rcases qN.mp hf2 with ⟨g₂,_,heq⟩
     have:=congr_fun (congr_fun heq a) (vx a s);simp only [Finset.Pi.cons_same] at this;exact hne this.symm
def zw {n:Nat} (H:Q4 n) (c:Q3 n):
    Finset ((Q4 n)):=
 Finset.univ.filter fun P=>
  P.card=2∧
  (∀ g∈P,g.card=2∧(g ∩ c).card=1∧(g ∩ outer H c).card=1)∧
  (∀ g∈P,∀ h∈P,g≠h→Disjoint g h)
def vk {n:Nat} (M:Q4 n) (c:Q3 n):
    (Q4 n):=
 M.filter (fun g=>¬ Disjoint g c)
lemma qY {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {c:(Q3 n)} (hc:c∈cores H):
 (zw H c).card=2∧
 ∀ P∈zw H c,P.biUnion id=c ∪ outer H c∧(∀ R∈zX H c,∃ g∈P,g⊆R)∧
   (∀ g∈P,¬ Disjoint g c∧g⊆c ∪ outer H c):=by
 have hcc:c.card=2:=((zq hH3).mp hc).1;rcases yk.mp hcc with ⟨a,b,hab,h0⟩
 rcases vP hH3 hdeg hc with ⟨x,y,hxy,hxord,hyord,h4,hf⟩
 have h3:Disjoint c (outer H c):=Finset.disjoint_sdiff;have hax:a≠x:=fun h=>qc.mp h3 (by rw [h0]; simp:a∈c) (by rw [h4,← h]; simp)
 have hay:a≠y:=fun h=>qc.mp h3 (by rw [h0]; simp:a∈c) (by rw [h4,← h]; simp)
 have hbx:b≠x:=fun h=>qc.mp h3 (by rw [h0]; simp:b∈c) (by rw [h4,← h]; simp)
 have hby:b≠y:=fun h=>qc.mp h3 (by rw [h0]; simp:b∈c) (by rw [h4,← h]; simp)
 set P₁:(Q4 n):={{a,x},{b,y}};set P₂:(Q4 n):={{a,y},{b,x}}
 have hn:P₁≠P₂:=by
  intro h;have hm:({a,x}:Q3 n)∈P₂:=h▸(by simp [P₁]);simp only [P₂,qe,qd] at hm;rcases hm with h1|h2
  · have:x∈({a,y}:Q3 n):=h1▸(by simp);simp [hax.symm,hxy] at this
  · have:a∈({b,x}:Q3 n):=h2▸(by simp);simp [hab,hax] at this
 have hl:P₁∈zw H c:=by
  simp only [zw,qa,qJ,true_and]
  have hne:({a,x}:Q3 n)≠{b,y}:=by intro h; have:a∈({b,y}:Q3 n):=h▸(by simp); simp [hab,hay] at this
  refine ⟨zv hne,fun g hg=>?_,fun g hg h hh hne'=>?_⟩
  · simp only [P₁,qe,qd] at hg;rcases hg with rfl|rfl
    · refine ⟨zv hax,?_,?_⟩
      · have:({a,x}:Q3 n) ∩ c={a}:=by
         ext u; rw [h0]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rfl
           · rcases h2 with h2|h2
             · exact absurd h2.symm hax
             · exact absurd h2.symm hbx
         · rintro rfl; exact ⟨Or.inl rfl,Or.inl rfl⟩
        rw [this,z3]
      · have:({a,x}:Q3 n) ∩ outer H c={x}:=by
         ext u; rw [h4]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rcases h2 with h2|h2
             · exact absurd h2 hax
             · exact absurd h2 hay
           · rfl
         · rintro rfl; exact ⟨Or.inr rfl,Or.inl rfl⟩
        rw [this,z3]
    · refine ⟨zv hby,?_,?_⟩
      · have:({b,y}:Q3 n) ∩ c={b}:=by
         ext u; rw [h0]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rfl
           · rcases h2 with h2|h2
             · exact absurd h2.symm hay
             · exact absurd h2.symm hby
         · rintro rfl; exact ⟨Or.inl rfl,Or.inr rfl⟩
        rw [this,z3]
      · have:({b,y}:Q3 n) ∩ outer H c={y}:=by
         ext u; rw [h4]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rcases h2 with h2|h2
             · exact absurd h2 hbx
             · exact absurd h2 hby
           · rfl
         · rintro rfl; exact ⟨Or.inr rfl,Or.inr rfl⟩
        rw [this,z3]
  · simp only [P₁,qe,qd] at hg hh;rcases hg with rfl|rfl <;> rcases hh with rfl|rfl
    · exact absurd rfl hne'
    · rw [qc]; intro u hu1 hu2;simp only [qe,qd] at hu1 hu2;rcases hu1 with rfl|rfl <;> rcases hu2 with h|h
      · exact hab h
      · exact hay h
      · exact hbx h.symm
      · exact hxy h
    · rw [qc]; intro u hu1 hu2;simp only [qe,qd] at hu1 hu2;rcases hu1 with rfl|rfl <;> rcases hu2 with h|h
      · exact hab h.symm
      · exact hbx h
      · exact hay h.symm
      · exact hxy h.symm
    · exact absurd rfl hne'
 have hk:P₂∈zw H c:=by
  simp only [zw,qa,qJ,true_and]
  have hne:({a,y}:Q3 n)≠{b,x}:=by intro h; have:a∈({b,x}:Q3 n):=h▸(by simp); simp [hab,hax] at this
  refine ⟨zv hne,fun g hg=>?_,fun g hg h hh hne'=>?_⟩
  · simp only [P₂,qe,qd] at hg;rcases hg with rfl|rfl
    · refine ⟨zv hay,?_,?_⟩
      · have:({a,y}:Q3 n) ∩ c={a}:=by
         ext u; rw [h0]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rfl
           · rcases h2 with h2|h2
             · exact absurd h2.symm hay
             · exact absurd h2.symm hby
         · rintro rfl; exact ⟨Or.inl rfl,Or.inl rfl⟩
        rw [this,z3]
      · have:({a,y}:Q3 n) ∩ outer H c={y}:=by
         ext u; rw [h4]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rcases h2 with h2|h2
             · exact absurd h2 hax
             · exact absurd h2 hay
           · rfl
         · rintro rfl; exact ⟨Or.inr rfl,Or.inr rfl⟩
        rw [this,z3]
    · refine ⟨zv hbx,?_,?_⟩
      · have:({b,x}:Q3 n) ∩ c={b}:=by
         ext u; rw [h0]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rfl
           · rcases h2 with h2|h2
             · exact absurd h2.symm hax
             · exact absurd h2.symm hbx
         · rintro rfl; exact ⟨Or.inl rfl,Or.inr rfl⟩
        rw [this,z3]
      · have:({b,x}:Q3 n) ∩ outer H c={x}:=by
         ext u; rw [h4]; simp only [qm,qe,qd];constructor
         · rintro ⟨rfl|rfl,h2⟩
           · rcases h2 with h2|h2
             · exact absurd h2 hbx
             · exact absurd h2 hby
           · rfl
         · rintro rfl; exact ⟨Or.inr rfl,Or.inl rfl⟩
        rw [this,z3]
  · simp only [P₂,qe,qd] at hg hh;rcases hg with rfl|rfl <;> rcases hh with rfl|rfl
    · exact absurd rfl hne'
    · rw [qc]; intro u hu1 hu2;simp only [qe,qd] at hu1 hu2;rcases hu1 with rfl|rfl <;> rcases hu2 with h|h
      · exact hab h
      · exact hax h
      · exact hby h.symm
      · exact hxy h.symm
    · rw [qc]; intro u hu1 hu2;simp only [qe,qd] at hu1 hu2;rcases hu1 with rfl|rfl <;> rcases hu2 with h|h
      · exact hab h.symm
      · exact hby h
      · exact hax h.symm
      · exact hxy h
    · exact absurd rfl hne'
 have h9:zw H c={P₁,P₂}:=by
  ext P;simp only [qe,qd];constructor
  · intro hP;simp only [zw,qa,qJ,true_and] at hP;rcases hP with ⟨hP2,ho,hs⟩
    rcases yk.mp hP2 with ⟨g₁,g₂,hw,h8⟩
    have hg1:g₁∈P:=by rw [h8]; simp
    have hg2:g₂∈P:=by rw [h8]; simp
    have h5:∀ g∈P,∃ p∈c,∃ q∈outer H c,g={p,q}:=by
     intro g hg;rcases ho g hg with ⟨hg2',hgc,hgo⟩
     rcases Finset.card_eq_one.mp hgc with ⟨p,hp⟩
     rcases Finset.card_eq_one.mp hgo with ⟨q,hq⟩
     have hpm:p∈g ∩ c:=by rw [hp]; simp
     have hqm:q∈g ∩ outer H c:=by rw [hq]; simp
     have hpq:p≠q:=fun h=>qc.mp h3
      (qm.mp hpm).2 (h▸(qm.mp hqm).2)
     have hv:({p,q}:Q3 n)⊆g:=by
      intro u hu; simp only [qe,qd] at hu;rcases hu with rfl|rfl
      · exact (qm.mp hpm).1
      · exact (qm.mp hqm).1
     refine ⟨p,(qm.mp hpm).2,q,(qm.mp hqm).2,?_⟩
     exact (zo hv (by rw [zv hpq,hg2'])).symm
    rcases h5 g₁ hg1 with ⟨p₁,hj,q₁,hb,h7⟩
    rcases h5 g₂ hg2 with ⟨p₂,hi,q₂,ha,h6⟩
    have ht:Disjoint g₁ g₂:=hs g₁ hg1 g₂ hg2 hw
    have hr:p₁≠p₂:=fun h=>qc.mp ht
     (by rw [h7]; simp:p₁∈g₁) (by rw [h6,← h]; simp)
    have he:q₁≠q₂:=fun h=>qc.mp ht
     (by rw [h7]; simp:q₁∈g₁) (by rw [h6,← h]; simp)
    rw [h0] at hj hi;rw [h4] at hb ha;simp only [qe,qd] at hj hi hb ha;rcases hj with rfl|rfl <;> rcases hi with rfl|rfl
    · exact absurd rfl hr
    · rcases hb with rfl|rfl <;> rcases ha with rfl|rfl
      · exact absurd rfl he
      · left; rw [h8,h7,h6]
      · right; rw [h8,h7,h6]
      · exact absurd rfl he
    · rcases hb with rfl|rfl <;> rcases ha with rfl|rfl
      · exact absurd rfl he
      · right; rw [h8,h7,h6,Finset.pair_comm]
      · left; rw [h8,h7,h6,Finset.pair_comm]
      · exact absurd rfl he
    · exact absurd rfl hr
  · rintro (rfl|rfl)
    · exact hl
    · exact hk
 refine ⟨by rw [h9,zv hn],fun P hP=>?_⟩
 rw [h9] at hP;simp only [qe,qd] at hP;rcases hP with rfl|rfl
 · refine ⟨?_,?_,?_⟩
   · ext u; rw [h4,h0]; simp [P₁,or_assoc,or_comm,or_left_comm]
   · intro R hR; rw [hf] at hR; simp only [qe,qd] at hR;rcases hR with rfl|rfl
     · refine ⟨{a,x},by simp [P₁],fun u hu=>?_⟩
       simp only [qe,qd] at hu;rcases hu with h|h
       · rw [h]; exact Finset.mem_insert_of_mem (by rw [h0]; simp)
       · rw [h]; exact vx x c
     · refine ⟨{b,y},by simp [P₁],fun u hu=>?_⟩
       simp only [qe,qd] at hu;rcases hu with h|h
       · rw [h]; exact Finset.mem_insert_of_mem (by rw [h0]; simp)
       · rw [h]; exact vx y c
   · intro g hg; simp only [P₁,qe,qd] at hg;rcases hg with rfl|rfl
     · refine ⟨fun hd=>qc.mp hd (by simp:a∈({a,x}:Q3 n)) (by rw [h0]; simp),fun u hu=>?_⟩
       rw [h4,h0]; simp only [qe,qd,ql] at hu ⊢;tauto
     · refine ⟨fun hd=>qc.mp hd (by simp:b∈({b,y}:Q3 n)) (by rw [h0]; simp),fun u hu=>?_⟩
       rw [h4,h0]; simp only [qe,qd,ql] at hu ⊢;tauto
 · refine ⟨?_,?_,?_⟩
   · ext u; rw [h4,h0]; simp [P₂,or_assoc,or_comm,or_left_comm]
   · intro R hR; rw [hf] at hR; simp only [qe,qd] at hR;rcases hR with rfl|rfl
     · refine ⟨{b,x},by simp [P₂],fun u hu=>?_⟩
       simp only [qe,qd] at hu;rcases hu with h|h
       · rw [h]; exact Finset.mem_insert_of_mem (by rw [h0]; simp)
       · rw [h]; exact vx x c
     · refine ⟨{a,y},by simp [P₂],fun u hu=>?_⟩
       simp only [qe,qd] at hu;rcases hu with h|h
       · rw [h]; exact Finset.mem_insert_of_mem (by rw [h0]; simp)
       · rw [h]; exact vx y c
   · intro g hg; simp only [P₂,qe,qd] at hg;rcases hg with rfl|rfl
     · refine ⟨fun hd=>qc.mp hd (by simp:a∈({a,y}:Q3 n)) (by rw [h0]; simp),fun u hu=>?_⟩
       rw [h4,h0]; simp only [qe,qd,ql] at hu ⊢;tauto
     · refine ⟨fun hd=>qc.mp hd (by simp:b∈({b,x}:Q3 n)) (by rw [h0]; simp),fun u hu=>?_⟩
       rw [h4,h0]; simp only [qe,qd,ql] at hu ⊢;tauto
lemma vB {n:Nat} {H M:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 (h2:∀ g∈M,g.card=2)
 (hdisj:∀ g∈M,∀ h∈M,g≠h→Disjoint g h)
 {c:(Q3 n)} (hc:c∈cores H)
 (hcov:∀ R∈zX H c,∃ g∈M,g⊆R):
 (c∈M∧vk M c={c})∨(c∉M∧vk M c∈zw H c):=by
 by_cases hcM:c∈M
 · left;refine ⟨hcM,?_⟩
   ext g;simp only [vk,qa,qd];constructor
   · rintro ⟨hgM,hnd⟩;by_contra hne;exact hnd (hdisj g hgM c hcM hne)
   · rintro h;rw [h];have hcc:=((zq hH3).mp hc).1;obtain ⟨u,hu⟩:c.Nonempty:=qU.mp (by omega);exact ⟨hcM,fun hd=>qc.mp hd hu hu⟩
 · right;refine ⟨hcM,?_⟩
   have hcc:=((zq hH3).mp hc).1;rcases vP hH3 hdeg hc with ⟨x,y,hxy,_,_,hb,he⟩
   have h0:Disjoint c (outer H c):=Finset.disjoint_sdiff;have hf:x∉c:=fun h=>qc.mp h0 h (by rw [hb]; simp)
   have hn:y∉c:=fun h=>qc.mp h0 h (by rw [hb]; simp)
   have ht:insert x c∈zX H c:=by rw [he]; simp
   have hs:insert y c∈zX H c:=by rw [he]; simp
   rcases hcov _ ht with ⟨g₁,h3,h9⟩
   rcases hcov _ hs with ⟨g₂,h1,h4⟩
   have hr:g₁≠c:=fun h=>hcM (h▸h3)
   have hq:g₂≠c:=fun h=>hcM (h▸h1)
   have hi:x∈g₁:=by
    by_contra hxn
    have h6:g₁⊆c:=fun u hu=>by
     rcases qe.mp (h9 hu) with rfl|huc
     · exact absurd hu hxn
     · exact huc
    exact hr (zo h6 (by rw [h2 g₁ h3,hcc]))
   have ho:y∈g₂:=by
    by_contra hyn
    have h6:g₂⊆c:=fun u hu=>by
     rcases qe.mp (h4 hu) with rfl|huc
     · exact absurd hu hyn
     · exact huc
    exact hq (zo h6 (by rw [h2 g₂ h1,hcc]))
   have ha:g₁≠g₂:=by
    intro heq;have hp:x∈insert y c:=h4 (heq▸hi);rcases qe.mp hp with h|h
    · exact hxy h
    · exact hf h
   have hl:Disjoint g₁ g₂:=hdisj g₁ h3 g₂ h1 ha
   have h8:(g₁ ∩ c).card=1:=by
    have heq:g₁ ∩ c=g₁.erase x:=by
     ext u;simp only [qm,qh];constructor
     · rintro ⟨hu1,huc⟩; exact ⟨fun h=>hf (h▸huc),hu1⟩
     · rintro ⟨hux,hu1⟩;rcases qe.mp (h9 hu1) with h|huc
       · exact absurd h hux
       · exact ⟨hu1,huc⟩
    rw [heq,zu hi,h2 g₁ h3]
   have h7:(g₂ ∩ c).card=1:=by
    have heq:g₂ ∩ c=g₂.erase y:=by
     ext u;simp only [qm,qh];constructor
     · rintro ⟨hu2,huc⟩; exact ⟨fun h=>hn (h▸huc),hu2⟩
     · rintro ⟨huy,hu2⟩;rcases qe.mp (h4 hu2) with h|huc
       · exact absurd h huy
       · exact ⟨hu2,huc⟩
    rw [heq,zu ho,h2 g₂ h1]
   have hk:(g₁ ∩ outer H c).card=1:=by
    have heq:g₁ ∩ outer H c={x}:=by
     ext u;simp only [qm,qd,hb,qe];constructor
     · rintro ⟨hu1,rfl|rfl⟩
       · rfl
       · rcases qe.mp (h9 hu1) with h|huc
         · exact absurd h.symm hxy
         · exact absurd huc hn
     · rintro rfl; exact ⟨hi,Or.inl rfl⟩
    rw [heq,z3]
   have hj:(g₂ ∩ outer H c).card=1:=by
    have heq:g₂ ∩ outer H c={y}:=by
     ext u;simp only [qm,qd,hb,qe];constructor
     · rintro ⟨hu2,rfl|rfl⟩
       · rcases qe.mp (h4 hu2) with h|huc
         · exact absurd h hxy
         · exact absurd huc hf
       · rfl
     · rintro rfl; exact ⟨ho,Or.inr rfl⟩
    rw [heq,z3]
   have hm:c⊆g₁ ∪ g₂:=by
    have h6:(g₁ ∩ c) ∪ (g₂ ∩ c)⊆c:=Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hdi:Disjoint (g₁ ∩ c) (g₂ ∩ c):=hl.mono vD vD
    have heq:(g₁ ∩ c) ∪ (g₂ ∩ c)=c:=
     zo h6
      (by rw [Finset.card_union_of_disjoint hdi,h8,h7,hcc])
    rw [← heq]
    exact Finset.union_subset (vD.trans Finset.subset_union_left)
     (vD.trans Finset.subset_union_right)
   have h5:vk M c={g₁,g₂}:=by
    ext g;simp only [vk,qa,qe,qd];constructor
    · rintro ⟨hgM,hnd⟩;rw [vE] at hnd;rcases hnd with ⟨u,hug,huc⟩
      rcases ql.mp (hm huc) with hu1|hu2
      · left; by_contra hne; exact qc.mp (hdisj g hgM g₁ h3 hne) hug hu1
      · right; by_contra hne; exact qc.mp (hdisj g hgM g₂ h1 hne) hug hu2
    · rintro (h|h)
      · rw [h];obtain ⟨u,hu⟩:(g₁ ∩ c).Nonempty:=qU.mp (by omega);exact ⟨h3,fun hd=>qc.mp hd (qm.mp hu).1 (qm.mp hu).2⟩
      · rw [h];obtain ⟨u,hu⟩:(g₂ ∩ c).Nonempty:=qU.mp (by omega);exact ⟨h1,fun hd=>qc.mp hd (qm.mp hu).1 (qm.mp hu).2⟩
   rw [h5];simp only [zw,qa,qJ,true_and];refine ⟨zv ha,fun g hg=>?_,fun g hg h hh hne=>?_⟩
   · simp only [qe,qd] at hg;rcases hg with h|h
     · rw [h]; exact ⟨h2 g₁ h3,h8,hk⟩
     · rw [h]; exact ⟨h2 g₂ h1,h7,hj⟩
   · simp only [qe,qd] at hg hh;rcases hg with rfl|rfl <;> rcases hh with rfl|rfl
     · exact absurd rfl hne
     · exact hl
     · exact hl.symm
     · exact absurd rfl hne
def left {n:Nat} (H:Q4 n) (S:Q4 n):(Q3 n):=ordinary H \ S.biUnion (outer H)
def reduced {n:Nat} (H:Q4 n) (S:Q4 n):
    (Q4 n):=
 (base H).image (fun R=>R ∩ left H S)
def q7 {n:Nat} (U:Q3 n) (F:Q4 n) (s:Nat):
    Finset ((Q4 n)):=
 Finset.univ.filter fun N=>
  (∀ g∈N,g.card=2∧g⊆U)∧
  (∀ g∈N,∀ h∈N,g≠h→Disjoint g h)∧
  (∀ R∈F,∃ g∈N,g⊆R)∧
  N.card=s
lemma k2 {n:Nat} (U:Q3 n) (F:Q4 n) (s:Nat):
 Nat.card {N:(Q4 n) // (∀ g∈N,g.card=2∧g⊆U)∧
  (∀ g∈N,∀ h∈N,g≠h→Disjoint g h)∧
  (∀ R∈F,∃ g∈N,g⊆R)∧N.card=s}=(q7 U F s).card:=by
 rw [Nat.card_eq_fintype_card,Fintype.card_subtype];rfl
lemma jy {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (S:Q4 n)
 {R' T':(Q3 n)} (hR':R'∈reduced H S) (hT':T'∈reduced H S) (hne:R'≠T'):
 (R' ∩ T').card≤1:=by
 rcases qN.mp hR' with ⟨R,hR,rfl⟩
 rcases qN.mp hT' with ⟨T,hT,rfl⟩
 have hRT:R≠T:=fun h=>hne (h▸rfl)
 exact (qH (Finset.inter_subset_inter vD vD)).trans (wE hH3 hR hT hRT)
def yd {n:Nat} (H M:Q4 n):(Q4 n):=(cores H).filter (fun c=>c∉M)
def qa4 {n:Nat} (H M:Q4 n):(Q4 n):=M \ (cores H).biUnion (vk M)
lemma yi {n:Nat} (M:Q4 n) (c:Q3 n):vk M c⊆M:=yv _ _
lemma yw {n:Nat} {H M:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 (h2:∀ g∈M,g.card=2)
 (hdisj:∀ g∈M,∀ h∈M,g≠h→Disjoint g h)
 (hcov:∀ R∈H,∃ g∈M,g⊆R)
 {c₁ c₂:(Q3 n)} (h1:c₁∈cores H) (h2c:c₂∈cores H) (hne:c₁≠c₂):
 Disjoint (vk M c₁) (vk M c₂):=by
 rw [qc];intro g hg1 hg2;have h6:=vB hH3 hdeg h2 hdisj h1 (fun R hR=>hcov R (qa.mp hR).1)
 have h5:g⊆c₁ ∪ outer H c₁:=by
  rcases h6 with ⟨_,hmc⟩|⟨_,hmc⟩
  · rw [hmc,qd] at hg1; rw [hg1]; exact Finset.subset_union_left
  · exact ((qY hH3 hdeg h1).2 _ hmc).2.2 g hg1 |>.2
 have h4:¬ Disjoint g c₂:=(qa.mp hg2).2;rw [vE] at h4;rcases h4 with ⟨u,hug,h3⟩
 rcases ql.mp (h5 hug) with h7|huo1
 · exact qc.mp (zd hH3 hdeg h1 h2c hne) h7 h3
 · have h0:=zE hH3 hdeg h1 huo1;simp only [ordinary,qg,qj,id_eq] at h0;exact h0.2 ⟨c₂,h2c,h3⟩
lemma y8 {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 {S:(Q4 n)} (hS:S⊆cores H):
 (S.biUnion (outer H)).card=2 * S.card↔
   ∀ c₁∈S,∀ c₂∈S,c₁≠c₂→Disjoint (outer H c₁) (outer H c₂):=by
 have h6:S.sum (fun c=>(outer H c).card)=2 * S.card:=by rw [Finset.sum_const_nat (fun c hc=>jx hH3 hdeg (hS hc)),mul_comm]
 constructor
 · intro hcard c₁ h1 c₂ h2 hne;by_contra hnd;rw [vE] at hnd;rcases hnd with ⟨u,hu1,hu2⟩
   have hlt:(S.biUnion (outer H)).card<S.sum (fun c=>(outer H c).card):=by
    have h3:S.biUnion (outer H)=outer H c₁ ∪ ((S.erase c₁).biUnion (outer H)):=by rw [← Finset.biUnion_insert,Finset.insert_erase h1]
    have hle2:((S.erase c₁).biUnion (outer H)).card≤(S.erase c₁).sum (fun c=>(outer H c).card):=Finset.card_biUnion_le
    have h4:u∈outer H c₁ ∩ (S.erase c₁).biUnion (outer H):=qm.mpr ⟨hu1,qj.mpr ⟨c₂,qh.mpr ⟨hne.symm,h2⟩,hu2⟩⟩
    have hpos:0<(outer H c₁ ∩ (S.erase c₁).biUnion (outer H)).card:=qU.mpr ⟨u,h4⟩;have hun:=Finset.card_union_add_card_inter (outer H c₁) ((S.erase c₁).biUnion (outer H))
    have h0:S.sum (fun c=>(outer H c).card)=
     (outer H c₁).card+(S.erase c₁).sum (fun c=>(outer H c).card):=by
     rw [← Finset.add_sum_erase S (fun c=>(outer H c).card) h1]
    rw [h3,h0];omega
   omega
 · intro h5;rw [Finset.card_biUnion (fun c₁ h1 c₂ h2 hne=>h5 c₁ h1 c₂ h2 hne),h6]
lemma wB {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 (s:Nat):
 (q7 Finset.univ H s).card=
   ((cores H).powerset.filter (fun S=>(S.biUnion (outer H)).card=2 * S.card∧
     (cores H).card+S.card≤ s)).sum (fun S=>2 ^ S.card * (q7 (left H S) (reduced H S) (s-(cores H).card-S.card)).card):=by
 classical
 set goodS:=(cores H).powerset.filter (fun S=>(S.biUnion (outer H)).card=2 * S.card∧
  (cores H).card+S.card≤ s)
 have hX:∀ M∈q7 Finset.univ H s,yd H M∈goodS:=by
  intro M hM;simp only [q7,qa,qJ,true_and] at hM;rcases hM with ⟨hr,h5,hb,hH⟩
  have h2:∀ g∈M,g.card=2:=fun g hg=>(hr g hg).1
  have h0:yd H M⊆cores H:=yv _ _;simp only [goodS,qa,v7];refine ⟨h0,?_,?_⟩
  · rw [y8 hH3 hdeg h0];intro c₁ h1 c₂ h2c hne;rw [qc];intro u hu1 hu2;have h1c:c₁∈cores H:=h0 h1;have h2c':c₂∈cores H:=h0 h2c;have h1n:c₁∉M:=(qa.mp h1).2;have h2n:c₂∉M:=(qa.mp h2c).2;have h04:=vB hH3 hdeg h2 h5 h1c (fun R hR=>hb R (qa.mp hR).1);have h03:=vB hH3 hdeg h2 h5 h2c' (fun R hR=>hb R (qa.mp hR).1);have hm1:vk M c₁∈zw H c₁:=by rcases h04 with ⟨hc,_⟩|⟨_,hm⟩; exact absurd hc h1n; exact hm
    have hm2:vk M c₂∈zw H c₂:=by rcases h03 with ⟨hc,_⟩|⟨_,hm⟩; exact absurd hc h2n; exact hm
    have hu1':u∈(vk M c₁).biUnion id:=by rw [((qY hH3 hdeg h1c).2 _ hm1).1]; exact Finset.mem_union_right _ hu1
    have hu2':u∈(vk M c₂).biUnion id:=by rw [((qY hH3 hdeg h2c').2 _ hm2).1]; exact Finset.mem_union_right _ hu2
    rcases qj.mp hu1' with ⟨g₁,hg1,h0a⟩
    rcases qj.mp hu2' with ⟨g₂,hg2,h09⟩
    have hx:g₁≠g₂:=fun heq=>qc.mp (yw hH3 hdeg h2 h5 hb h1c h2c' hne) hg1 (heq▸hg2)
    exact qc.mp (h5 g₁ (yi M c₁ hg1) g₂ (yi M c₂ hg2) hx) h0a h09
  · have hv:(cores H).biUnion (vk M)⊆M:=by
     intro g hg; rcases qj.mp hg with ⟨c,_,hgc⟩; exact yi M c hgc
    have hbi:((cores H).biUnion (vk M)).card=(cores H).card+(yd H M).card:=by
     rw [Finset.card_biUnion (fun c₁ h1 c₂ h2c hne=>yw hH3 hdeg h2 h5 hb h1 h2c hne)]
     have hq:(cores H).sum (fun c=>(vk M c).card)=
      (cores H).sum (fun c=>1+if c∈yd H M then 1 else 0):=by
      refine Finset.sum_congr rfl fun c hc=>?_
      have hi:=vB hH3 hdeg h2 h5 hc (fun R hR=>hb R (qa.mp hR).1);by_cases hcM:c∈M
      · have hna:c∉yd H M:=by simp [yd,hcM]
        rcases hi with ⟨_,hmc⟩|⟨hn,_⟩
        · simp [hmc,hna]
        · exact absurd hcM hn
      · have ha:c∈yd H M:=qa.mpr ⟨hc,hcM⟩;rcases hi with ⟨hc',_⟩|⟨_,hmc⟩
        · exact absurd hc' hcM
        · have h2c':=(qa.mp hmc).2.1;simp [h2c',ha]
     rw [hq,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,Finset.sum_boole,Nat.cast_id];congr 1;rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr h0]
    have:=qH hv;omega
 rw [Finset.card_eq_sum_card_fiberwise hX];refine Finset.sum_congr rfl fun S hS=>?_
 simp only [goodS,qa,v7] at hS;rcases hS with ⟨h0,hF,hSsize⟩
 have hl:=(y8 hH3 hdeg h0).mp hF;set F_S:=(q7 Finset.univ H s).filter (fun M=>yd H M=S);set P_S:=S.pi (zw H);set N_S:=q7 (left H S) (reduced H S) (s-(cores H).card-S.card)
 have hO:P_S.card=2 ^ S.card:=by
  rw [uc]
  calc S.prod (fun c=>(zw H c).card)=S.prod (fun _=>2):=Finset.prod_congr rfl (fun c hc=>(qY hH3 hdeg (h0 hc)).1)
   _=2 ^ S.card:=Finset.prod_const 2
 rw [← hO,← Finset.card_product]
 refine Finset.card_nbij'
  (fun M=>(fun c _=>vk M c,qa4 H M))
  (fun z=>(cores H \ S) ∪ (S.attach.biUnion (fun c=>z.1 c.1 c.2)) ∪ z.2)
  ?_ ?_ ?_ ?_
 · intro M hM;simp only [zQ,F_S,qa] at hM;rcases hM with ⟨hMV,ho⟩
   simp only [q7,qa,qJ,true_and] at hMV;rcases hMV with ⟨hr,h5,hb,hH⟩
   have h2:∀ g∈M,g.card=2:=fun g hg=>(hr g hg).1
   simp only [zQ,Finset.mem_product,P_S,Finset.mem_pi,N_S,q7,qa,qJ,true_and];refine ⟨fun c hc=>?_,?_,?_,?_,?_⟩
   · have hcS:c∈yd H M:=ho.symm▸hc;have hi:=vB hH3 hdeg h2 h5 (h0 hc) (fun R hR=>hb R (qa.mp hR).1);rcases hi with ⟨hcM,_⟩|⟨_,hmc⟩
     · exact absurd hcM (qa.mp hcS).2
     · exact hmc
   · intro g hg;have hgM:g∈M:=(qg.mp hg).1;have hk:g∉(cores H).biUnion (vk M):=(qg.mp hg).2;refine ⟨h2 g hgM,fun u hug=>?_⟩
     simp only [left,ordinary,qg,qJ,true_and,qj,id_eq]
     refine ⟨fun ⟨c,hc,huc⟩=>hk (qj.mpr ⟨c,hc,
      qa.mpr ⟨hgM,fun hd=>qc.mp hd hug huc⟩⟩),?_⟩
     rintro ⟨c,hcS,huo⟩;have hcS':c∈yd H M:=ho.symm▸hcS;have hcn:c∉M:=(qa.mp hcS').2;have hi:=vB hH3 hdeg h2 h5 (h0 hcS) (fun R hR=>hb R (qa.mp hR).1)
     have hmc:vk M c∈zw H c:=by rcases hi with ⟨hcM,_⟩|⟨_,hmc⟩; exact absurd hcM hcn; exact hmc
     have hJ:u∈(vk M c).biUnion id:=by rw [((qY hH3 hdeg (h0 hcS)).2 _ hmc).1]; exact Finset.mem_union_right _ huo
     rcases qj.mp hJ with ⟨g',hy,hug'⟩
     have hx:g≠g':=fun heq=>hk (qj.mpr ⟨c,h0 hcS,heq▸hy⟩)
     exact qc.mp (h5 g hgM g' (yi M c hy) hx) hug hug'
   · intro g hg h hh hne;exact h5 g (qg.mp hg).1 h (qg.mp hh).1 hne
   · intro R' hR';rcases qN.mp hR' with ⟨R,hR,rfl⟩
     have hRH:R∈H:=(qa.mp hR).1;have hI:R⊆ordinary H:=(qa.mp hR).2;rcases hb R hRH with ⟨g,hgM,hgR⟩
     have hk:g∉(cores H).biUnion (vk M):=by
      intro hE;rcases qj.mp hE with ⟨c,hc,hgc⟩
      have hnd:¬ Disjoint g c:=(qa.mp hgc).2;rw [vE] at hnd;rcases hnd with ⟨u,hug,huc⟩
      have h3:=hI (hgR hug);simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c,hc,huc⟩
     have hZ:g∈qa4 H M:=qg.mpr ⟨hgM,hk⟩;refine ⟨g,hZ,Finset.subset_inter hgR fun u hug=>?_⟩
     simp only [left,qg,qj];refine ⟨hI (hgR hug),?_⟩
     rintro ⟨c,hcS,huo⟩;have hcS':c∈yd H M:=ho.symm▸hcS;have hcn:c∉M:=(qa.mp hcS').2;have hi:=vB hH3 hdeg h2 h5 (h0 hcS) (fun R hR=>hb R (qa.mp hR).1)
     have hmc:vk M c∈zw H c:=by rcases hi with ⟨hcM,_⟩|⟨_,hmc⟩; exact absurd hcM hcn; exact hmc
     have hJ:u∈(vk M c).biUnion id:=by rw [((qY hH3 hdeg (h0 hcS)).2 _ hmc).1]; exact Finset.mem_union_right _ huo
     rcases qj.mp hJ with ⟨g',hy,hug'⟩
     have hx:g≠g':=fun heq=>hk (qj.mpr ⟨c,h0 hcS,heq▸hy⟩)
     exact qc.mp (h5 g hgM g' (yi M c hy) hx) hug hug'
   · have hv:(cores H).biUnion (vk M)⊆M:=by
      intro g hg; rcases qj.mp hg with ⟨c,_,hgc⟩; exact yi M c hgc
     have hbi:((cores H).biUnion (vk M)).card=(cores H).card+S.card:=by
      rw [Finset.card_biUnion (fun c₁ h1 c₂ h2c hne=>yw hH3 hdeg h2 h5 hb h1 h2c hne)]
      have hq:(cores H).sum (fun c=>(vk M c).card)=
       (cores H).sum (fun c=>1+if c∈S then 1 else 0):=by
       refine Finset.sum_congr rfl fun c hc=>?_
       have hi:=vB hH3 hdeg h2 h5 hc (fun R hR=>hb R (qa.mp hR).1);by_cases hcM:c∈M
       · have hna:c∉S:=by rw [← ho]; simp [yd,hcM]
         rcases hi with ⟨_,hmc⟩|⟨hn,_⟩
         · simp [hmc,hna]
         · exact absurd hcM hn
       · have ha:c∈S:=by rw [← ho]; exact qa.mpr ⟨hc,hcM⟩
         rcases hi with ⟨hc',_⟩|⟨_,hmc⟩
         · exact absurd hc' hcM
         · simp [(qa.mp hmc).2.1,ha]
      rw [hq,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,Finset.sum_boole,Nat.cast_id];congr 1;rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr h0]
     rw [qa4,Finset.card_sdiff_of_subset hv,hH,hbi];omega
 · rintro ⟨f,N⟩ hz;simp only [zQ,Finset.mem_product,P_S,Finset.mem_pi,N_S,q7,qa,qJ,true_and] at hz;rcases hz with ⟨hf,h6,hC,h06,hP⟩
   set A:=cores H \ S;set B:=S.attach.biUnion (fun c=>f c.1 c.2);set M:=A ∪ B ∪ N
   have hp:∀ g∈B,∃ c:Q3 n,∃ hc:c∈S,g∈f c hc∧g.card=2∧
    ¬ Disjoint g c∧g⊆c ∪ outer H c:=by
    intro g hg;rcases qj.mp hg with ⟨⟨c,hc⟩,_,hgf⟩
    have hcm:=hf c hc;have hG:=(qa.mp hcm).2.2.1 g hgf;have h00:=((qY hH3 hdeg (h0 hc)).2 _ hcm).2.2 g hgf;exact ⟨c,hc,hgf,hG.1,h00.1,h00.2⟩
   have h9:∀ g∈A,∀ h∈B,Disjoint g h:=by
    intro g hg h hh;rcases qg.mp hg with ⟨hgC,hgS⟩
    rcases hp h hh with ⟨c,hcS,_,_,_,hY⟩
    have hne:g≠c:=fun e=>hgS (e▸hcS)
    rw [qc];intro u hug huh;rcases ql.mp (hY huh) with huc|huo
    · exact qc.mp (zd hH3 hdeg hgC (h0 hcS) hne) hug huc
    · have h3:=zE hH3 hdeg (h0 hcS) huo;simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨g,hgC,hug⟩
   have h8:∀ g∈A,∀ h∈N,Disjoint g h:=by intro g hg h hh;have hgC:g∈cores H:=(qg.mp hg).1;rw [qc];intro u hug huh;have h4:=(h6 h hh).2 huh;simp only [left,ordinary,qg,qj,id_eq] at h4;exact h4.1.2 ⟨g,hgC,hug⟩
   have h7:∀ g∈B,∀ h∈N,Disjoint g h:=by
    intro g hg h hh;rcases hp g hg with ⟨c,hcS,_,_,_,hw⟩
    rw [qc];intro u hug huh;have h4:=(h6 h hh).2 huh;simp only [left,ordinary,qg,qj,id_eq] at h4;rcases ql.mp (hw hug) with huc|huo
    · exact h4.1.2 ⟨c,h0 hcS,huc⟩
    · exact h4.2 ⟨c,hcS,huo⟩
   have hs:∀ g∈B,∀ h∈B,g≠h→Disjoint g h:=by
    intro g hg h hh hne;rcases hp g hg with ⟨c₁,h1,hg1,_,_,h0c⟩
    rcases hp h hh with ⟨c₂,h2,hh2,_,_,h0b⟩
    by_cases hc:c₁=c₂
    · subst hc;exact (qa.mp (hf c₁ h1)).2.2.2 g hg1 h hh2 hne
    · rw [qc];intro u hug huh;rcases ql.mp (h0c hug) with hU|hu1o <;>
      rcases ql.mp (h0b huh) with hT|hu2o
      · exact qc.mp (zd hH3 hdeg (h0 h1) (h0 h2) hc) hU hT
      · have h3:=zE hH3 hdeg (h0 h2) hu2o;simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c₁,h0 h1,hU⟩
      · have h3:=zE hH3 hdeg (h0 h1) hu1o;simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c₂,h0 h2,hT⟩
      · exact qc.mp (hl c₁ h1 c₂ h2 hc) hu1o hu2o
   have h2M:∀ g∈M,g.card=2:=by
    intro g hg;rcases ql.mp hg with hAB|hN
    · rcases ql.mp hAB with hA|hB
      · exact ((zq hH3).mp (qg.mp hA).1).1
      · rcases hp g hB with ⟨_,_,_,hg2,_,_⟩; exact hg2
    · exact (h6 g hN).1
   have hL:∀ g∈M,∀ h∈M,g≠h→Disjoint g h:=by
    intro g hg h hh hne;rcases ql.mp hg with h08|hN1 <;> rcases ql.mp hh with h07|hN2
    · rcases ql.mp h08 with hA1|hB1 <;> rcases ql.mp h07 with hA2|hB2
      · exact zd hH3 hdeg (qg.mp hA1).1 (qg.mp hA2).1 hne
      · exact h9 g hA1 h hB2
      · exact (h9 h hA2 g hB1).symm
      · exact hs g hB1 h hB2 hne
    · rcases ql.mp h08 with hA1|hB1
      · exact h8 g hA1 h hN2
      · exact h7 g hB1 h hN2
    · rcases ql.mp h07 with hA2|hB2
      · exact (h8 h hA2 g hN1).symm
      · exact (h7 h hB2 g hN1).symm
    · exact hC g hN1 h hN2 hne
   have hD:Disjoint A B:=by
    rw [qc]; intro g hgA hgB;have hne:g.Nonempty:=qU.mp (by rw [((zq hH3).mp (qg.mp hgA).1).1]; omega);rcases hne with ⟨u,hu⟩
    exact qc.mp (h9 g hgA g hgB) hu hu
   have ht:Disjoint (A ∪ B) N:=by
    rw [qc]; intro g hgAB hgN;have hne:g.Nonempty:=qU.mp (by rw [(h6 g hgN).1]; omega);rcases hne with ⟨u,hu⟩
    rcases ql.mp hgAB with hgA|hgB
    · exact qc.mp (h8 g hgA g hgN) hu hu
    · exact qc.mp (h7 g hgB g hgN) hu hu
   have hQ:B.card=2 * S.card:=by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_const_nat (fun c _=>(qa.mp (hf c.1 c.2)).2.1),Finset.card_attach,mul_comm]
    · intro c₁ _ c₂ _ hne;dsimp only [Function.onFun];rw [qc]; intro g hg1 hg2;have hgB1:g∈B:=qj.mpr ⟨c₁,Finset.mem_attach _ _,hg1⟩;have hg2':g.card=2:=(qa.mp (hf c₁.1 c₁.2)).2.2.1 g hg1 |>.1;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega);have hW:=((qY hH3 hdeg (h0 c₁.2)).2 _ (hf c₁.1 c₁.2)).2.2 g hg1 |>.2;have hV:=((qY hH3 hdeg (h0 c₂.2)).2 _ (hf c₂.1 c₂.2)).2.2 g hg2 |>.2;have h02:c₁.1≠c₂.1:=fun e=>hne (Subtype.ext e)
      rcases ql.mp (hW hu) with hu1|hu1 <;> rcases ql.mp (hV hu) with hu2|hu2
      · exact qc.mp (zd hH3 hdeg (h0 c₁.2) (h0 c₂.2) h02) hu1 hu2
      · have h3:=zE hH3 hdeg (h0 c₂.2) hu2;simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c₁.1,h0 c₁.2,hu1⟩
      · have h3:=zE hH3 hdeg (h0 c₁.2) hu1;simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c₂.1,h0 c₂.2,hu2⟩
      · exact qc.mp (hl c₁.1 c₁.2 c₂.1 c₂.2 h02) hu1 hu2
   simp only [zQ,F_S,qa,q7,qJ,true_and];refine ⟨⟨fun g hg=>⟨h2M g hg,Finset.subset_univ _⟩,hL,?_,?_⟩,?_⟩
   · intro R hR;rcases u6 hH3 hdeg hR with hRb|⟨c,hc,hcR⟩
     · rcases h06 (R ∩ left H S) (qN.mpr ⟨R,hRb,rfl⟩) with ⟨g,hgN,hw⟩
       exact ⟨g,Finset.mem_union_right _ hgN,hw.trans vD⟩
     · by_cases hcS:c∈S
       · have h05:R∈zX H c:=qa.mpr ⟨hR,hcR⟩;rcases ((qY hH3 hdeg hc).2 _ (hf c hcS)).2.1 R h05 with ⟨g,hgf,hgR⟩
         exact ⟨g,Finset.mem_union_left _ (Finset.mem_union_right _ (qj.mpr ⟨⟨c,hcS⟩,Finset.mem_attach _ _,hgf⟩)),hgR⟩
       · exact ⟨c,Finset.mem_union_left _ (Finset.mem_union_left _ (qg.mpr ⟨hc,hcS⟩)),hcR⟩
   · rw [Finset.card_union_of_disjoint ht,Finset.card_union_of_disjoint hD,Finset.card_sdiff_of_subset h0,hQ,hP];have:=qH h0;omega
   · ext c;simp only [yd,qa];constructor
     · rintro ⟨hc,hcM⟩;by_contra hcS;exact hcM (Finset.mem_union_left _ (Finset.mem_union_left _ (qg.mpr ⟨hc,hcS⟩)))
     · intro hcS;refine ⟨h0 hcS,fun hcM=>?_⟩
       rcases ql.mp hcM with hAB|hN
       · rcases ql.mp hAB with hA|hB
         · exact (qg.mp hA).2 hcS
         · rcases hp c hB with ⟨c',he,hcf,_,_,_⟩
           have hG:=(qa.mp (hf c' he)).2.2.1 c hcf;have hcc:c.card=2:=((zq hH3).mp (h0 hcS)).1;obtain ⟨u,hu⟩:(c ∩ outer H c').Nonempty:=qU.mp (by omega);have h3:=zE hH3 hdeg (h0 he) (qm.mp hu).2;simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c,h0 hcS,(qm.mp hu).1⟩
       · have h01:=(h6 c hN).2;have hcc:c.card=2:=((zq hH3).mp (h0 hcS)).1;obtain ⟨u,hu⟩:c.Nonempty:=qU.mp (by omega);have h4:=h01 hu;simp only [left,ordinary,qg,qj,id_eq] at h4;exact h4.1.2 ⟨c,h0 hcS,hu⟩
 · intro M hM;simp only [zQ,F_S,qa] at hM;rcases hM with ⟨hMV,ho⟩
   simp only [q7,qa,qJ,true_and] at hMV;rcases hMV with ⟨hr,h5,hb,_⟩
   have h2:∀ g∈M,g.card=2:=fun g hg=>(hr g hg).1
   ext g;simp only [ql,qg,qj,Finset.mem_attach,true_and,Subtype.exists,qa4];constructor
   · rintro ((⟨hgC,hgS⟩|⟨c,hcS,hgc⟩)|⟨hgM,_⟩)
     · by_contra h0d;exact hgS (ho▸qa.mpr ⟨hgC,h0d⟩)
     · exact yi M c hgc
     · exact hgM
   · intro hgM;by_cases hE:g∈(cores H).biUnion (vk M)
     · left;rcases qj.mp hE with ⟨c,hc,hgc⟩
       by_cases hcS:c∈S
       · right; exact ⟨c,hcS,hgc⟩
       · left
         have hcM:c∈M:=by by_contra hcn; exact hcS (ho▸qa.mpr ⟨hc,hcn⟩)
         have hi:=vB hH3 hdeg h2 h5 hc (fun R hR=>hb R (qa.mp hR).1);rcases hi with ⟨_,hmc⟩|⟨hn,_⟩
         · rw [hmc,qd] at hgc; exact ⟨hgc▸hc,hgc▸hcS⟩
         · exact absurd hcM hn
     · right; exact ⟨hgM,fun ⟨c,hc,hgc⟩=>hE (qj.mpr ⟨c,hc,hgc⟩)⟩
 · rintro ⟨f,N⟩ hz;simp only [zQ,Finset.mem_product,P_S,Finset.mem_pi,N_S,q7,qa,qJ,true_and] at hz;rcases hz with ⟨hf,h6,hC,_,_⟩
   set A:=cores H \ S;set B:=S.attach.biUnion (fun c=>f c.1 c.2);set M:=A ∪ B ∪ N
   have hj:∀ c∈cores H,vk M c=if h:c∈S then f c h else {c}:=by
    intro c hc;split_ifs with hcS
    · ext g;simp only [vk,qa];constructor
      · rintro ⟨hgM,hnd⟩;rcases ql.mp hgM with hAB|hN
        · rcases ql.mp hAB with hA|hB
          · rcases qg.mp hA with ⟨hgC,hgS⟩
            have hne:g≠c:=fun e=>hgS (e▸hcS)
            exact absurd (zd hH3 hdeg hgC hc hne) hnd
          · rcases qj.mp hB with ⟨⟨c',he⟩,_,hgf⟩
            by_cases heq:c'=c
            · subst heq; exact hgf
            · exfalso; apply hnd;have hK:=((qY hH3 hdeg (h0 he)).2 _ (hf c' he)).2.2 g hgf |>.2;rw [qc]; intro u hug huc;rcases ql.mp (hK hug) with huc'|huo'
              · exact qc.mp (zd hH3 hdeg (h0 he) hc heq) huc' huc
              · have h3:=zE hH3 hdeg (h0 he) huo';simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c,hc,huc⟩
        · exfalso; apply hnd;rw [qc]; intro u hug huc;have h4:=(h6 g hN).2 hug;simp only [left,ordinary,qg,qj,id_eq] at h4;exact h4.1.2 ⟨c,hc,huc⟩
      · intro hgf
        refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (qj.mpr ⟨⟨c,hcS⟩,Finset.mem_attach _ _,hgf⟩)),
         ((qY hH3 hdeg hc).2 _ (hf c hcS)).2.2 g hgf |>.1⟩
    · ext g;simp only [vk,qa,qd];constructor
      · rintro ⟨hgM,hnd⟩;rcases ql.mp hgM with hAB|hN
        · rcases ql.mp hAB with hA|hB
          · by_contra hne;exact hnd (zd hH3 hdeg (qg.mp hA).1 hc hne)
          · exfalso; apply hnd;rcases qj.mp hB with ⟨⟨c',he⟩,_,hgf⟩
            have hne:c'≠c:=fun e=>hcS (e▸he)
            have hK:=((qY hH3 hdeg (h0 he)).2 _ (hf c' he)).2.2 g hgf |>.2;rw [qc]; intro u hug huc;rcases ql.mp (hK hug) with huc'|huo'
            · exact qc.mp (zd hH3 hdeg (h0 he) hc hne) huc' huc
            · have h3:=zE hH3 hdeg (h0 he) huo';simp only [ordinary,qg,qj,id_eq] at h3;exact h3.2 ⟨c,hc,huc⟩
        · exfalso; apply hnd;rw [qc]; intro u hug huc;have h4:=(h6 g hN).2 hug;simp only [left,ordinary,qg,qj,id_eq] at h4;exact h4.1.2 ⟨c,hc,huc⟩
      · rintro hgc;rw [hgc];have hcc:c.card=2:=((zq hH3).mp hc).1;obtain ⟨u,hu⟩:c.Nonempty:=qU.mp (by omega)
        exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (qg.mpr ⟨hc,hcS⟩)),
         fun hd=>qc.mp hd hu hu⟩
   ext1
   · funext c hc
     change vk M c=f c hc;rw [hj c (h0 hc),dif_pos hc]
   · ext g;simp only [qa4,qg,qj];constructor
     · rintro ⟨hgM,hk⟩;rcases ql.mp hgM with hAB|hN
       · rcases ql.mp hAB with hA|hB
         · exfalso; apply hk;have hgC:=(qg.mp hA).1;have hgS:=(qg.mp hA).2;refine ⟨g,hgC,?_⟩
           rw [hj g hgC,dif_neg hgS]; exact Finset.mem_singleton_self g
         · exfalso; apply hk;rcases qj.mp hB with ⟨⟨c,hcS⟩,_,hgf⟩
           refine ⟨c,h0 hcS,?_⟩
           rw [hj c (h0 hcS),dif_pos hcS]; exact hgf
       · exact hN
     · intro hgN;refine ⟨Finset.mem_union_right _ hgN,?_⟩
       rintro ⟨c,hc,hgc⟩;have hnd:¬ Disjoint g c:=(qa.mp hgc).2;rw [vE] at hnd;rcases hnd with ⟨u,hug,huc⟩
       have h4:=(h6 g hgN).2 hug;simp only [left,ordinary,qg,qj,id_eq] at h4;exact h4.1.2 ⟨c,hc,huc⟩
lemma uY {n:Nat} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 (t s:Nat):
 (q7 Finset.univ H s).card % 2 ^ t=
   ((cores H).powerset.filter (fun S=>S.card<t∧(S.biUnion (outer H)).card=2 * S.card∧
     (cores H).card+S.card≤ s)).sum (fun S=>2 ^ S.card * (q7 (left H S) (reduced H S) (s-(cores H).card-S.card)).card) % 2 ^ t:=by
 rw [wB hH3 hdeg s]
 set A:=(cores H).powerset.filter (fun S=>(S.biUnion (outer H)).card=2 * S.card∧
  (cores H).card+S.card≤ s)
 set F:Q4 n→Nat:=fun S=>2 ^ S.card * (q7 (left H S) (reduced H S) (s-(cores H).card-S.card)).card
 have h0:A.sum F=(A.filter (fun S=>S.card<t)).sum F +
  (A.filter (fun S=>¬ S.card<t)).sum F:=
  (Finset.sum_filter_add_sum_filter_not A (fun S=>S.card<t) F).symm
 have h2:2 ^ t ∣ (A.filter (fun S=>¬ S.card<t)).sum F:=by
  refine Finset.dvd_sum fun S hS=>?_
  have hge:t≤S.card:=yt (qa.mp hS).2;exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge) _
 have h1:A.filter (fun S=>S.card<t)=
  (cores H).powerset.filter (fun S=>S.card<t∧(S.biUnion (outer H)).card=2 * S.card∧
    (cores H).card+S.card≤ s):=by
  ext S; simp only [A,qa]; tauto
 rw [h0,h1,Nat.add_mod,Nat.mod_eq_zero_of_dvd h2,add_zero,Nat.mod_mod]
lemma qam {n:Nat} {U:(Q3 n)} {F:(Q4 n)} {s:Nat}
 {R:(Q3 n)} (hR:R∈F) (hR1:R.card≤1):
 (q7 U F s).card=0:=by
 rw [Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem];intro N hN;simp only [q7,qa,qJ,true_and] at hN;rcases hN.2.2.1 R hR with ⟨g,hgN,hgR⟩
 have h2:=(hN.1 g hgN).1;have hle:=qH hgR;omega
lemma qal {n:Nat} {U:(Q3 n)} {F:(Q4 n)} {s:Nat}
 {e:(Q3 n)} (he:e∈F) (he2:e.card=2) (heU:e⊆U)
 (hlin:∀ R∈F,R≠e→(R ∩ e).card≤1):
 (q7 U F s).card=
   if s=0 then 0 else (q7 (U \ e) ((F.erase e).image (fun R=>R \ e)) (s-1)).card:=by
 classical
 have h1:∀ N∈q7 U F s,e∈N:=by
  intro N hN;simp only [q7,qa,qJ,true_and] at hN;rcases hN.2.2.1 e he with ⟨g,hgN,hge⟩
  have h8:g=e:=zo hge (by rw [(hN.1 g hgN).1,he2]);exact h8▸hgN
 by_cases hs:s=0
 · subst hs; rw [if_pos rfl,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem];intro N hN;have heN:=h1 N hN;have hc:N.card=0:=(qa.mp hN).2.2.2.2;have hpos:0<N.card:=qU.mpr ⟨e,heN⟩;omega
 · rw [if_neg hs];refine Finset.card_nbij' (fun N=>N.erase e) (fun N'=>insert e N') ?_ ?_ ?_ ?_
   · intro N hN;have heN:=h1 N hN;simp only [zQ,q7,qa,qJ,true_and] at hN ⊢;rcases hN with ⟨h0,h2,h5,h4⟩
     refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R' hR'=>?_,?_⟩
     · rcases qh.mp hg with ⟨hne,hgN⟩
       refine ⟨(h0 g hgN).1,fun u hug=>qg.mpr ⟨(h0 g hgN).2 hug,
        fun hue=>qc.mp (h2 g hgN e heN hne) hug hue⟩⟩
     · exact h2 g (qE hg) h (qE hh) hne
     · rcases qN.mp hR' with ⟨R,h9,rfl⟩
       rcases qh.mp h9 with ⟨hRe,hRF⟩
       rcases h5 R hRF with ⟨g,hgN,hgR⟩
       have hge:g≠e:=by intro hge;have hle:=hlin R hRF hRe;have h7:e⊆R ∩ e:=Finset.subset_inter (hge▸hgR) Finset.Subset.rfl;have:=qH h7;omega
       refine ⟨g,qh.mpr ⟨hge,hgN⟩,fun u hug=>qg.mpr ⟨hgR hug,fun hue=>qc.mp (h2 g hgN e heN hge) hug hue⟩⟩
     · rw [zu heN,h4]
   · intro N' hN';simp only [zQ,q7,qa,qJ,true_and] at hN' ⊢;rcases hN' with ⟨h0,h2,h5,h4⟩
     have h3:e∉N':=by intro heN';obtain ⟨u,hu⟩:e.Nonempty:=qU.mp (by omega);exact (qg.mp ((h0 e heN').2 hu)).2 hu
     refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,fun R hR=>?_,?_⟩
     · rcases qe.mp hg with rfl|hgN'
       · exact ⟨he2,heU⟩
       · exact ⟨(h0 g hgN').1,(h0 g hgN').2.trans Finset.sdiff_subset⟩
     · rcases qe.mp hg with rfl|hgN' <;> rcases qe.mp hh with rfl|hhN'
       · exact absurd rfl hne
       · exact qc.mpr fun u hue huh=>(qg.mp ((h0 h hhN').2 huh)).2 hue
       · exact qc.mpr fun u hug hue=>(qg.mp ((h0 g hgN').2 hug)).2 hue
       · exact h2 g hgN' h hhN' hne
     · by_cases hRe:R=e
       · rw [hRe]; exact ⟨e,vx e N',Finset.Subset.rfl⟩
       · rcases h5 (R \ e) (qN.mpr ⟨R,qh.mpr ⟨hRe,hR⟩,rfl⟩) with ⟨g,hgN',h6⟩
         exact ⟨g,Finset.mem_insert_of_mem hgN',h6.trans Finset.sdiff_subset⟩
     · rw [Finset.card_insert_of_notMem h3,h4]; omega
   · intro N hN;exact Finset.insert_erase (h1 N hN)
   · intro N' hN';simp only [zQ,q7,qa,qJ,true_and] at hN'
     have h3:e∉N':=by intro heN';obtain ⟨u,hu⟩:e.Nonempty:=qU.mp (by omega);exact (qg.mp ((hN'.1 e heN').2 hu)).2 hu
     exact Finset.erase_insert h3
def vV:Nat→Nat→Nat
 | _,0=>1
 | 0,_+1=>0
 | 1,_+1=>0
 | r+2,m+1=>vV (r+1) (m+1)+(r+1) * vV r m
def zr {α:Type} [DecidableEq α] (A:Finset α) (m:Nat):Finset (Finset (Finset α)):=
 ((A.powersetCard 2).powerset).filter fun Q=>(∀ g∈Q,∀ h∈Q,g≠h→Disjoint g h)∧Q.card=m
lemma wy {α:Type} [DecidableEq α]:
 ∀ (r:Nat) (A:Finset α) (m:Nat),A.card=r→(zr A m).card=vV r m:=by
 intro r;induction r using Nat.strong_induction_on with
 | ind r ih=>
   intro A m hA
   cases m with
   | zero=>
     have heq:zr A 0={∅}:=by
      ext Q; simp only [zr,qa,v7,qd];constructor
      · rintro ⟨_,_,h0⟩; exact Finset.card_eq_zero.mp h0
      · rintro rfl; simp
     rw [heq,z3]; cases r <;> rfl
   | succ m=>
     cases r with
     | zero=>
       have hAe:A=∅:=Finset.card_eq_zero.mp hA;subst hAe
       have heq:zr (∅:Finset α) (m+1)=∅:=by rw [Finset.eq_empty_iff_forall_notMem]; intro Q hQ;simp only [zr,qa,v7] at hQ;obtain ⟨g,hgQ⟩:Q.Nonempty:=qU.mp (by omega);have hg2:=zD.mp (hQ.1 hgQ);have:=qH hg2.1;simp [hg2.2] at this
       rw [heq,Finset.card_empty]; rfl
     | succ r'=>
       obtain ⟨a,haA⟩:A.Nonempty:=qU.mp (by omega);set B:=A.erase a;have h6:B.card=r':=by rw [zu haA,hA]; omega
       have hk:zr A (m+1)=
        (zr A (m+1)).filter (fun Q=>a∉Q.biUnion id) ∪
        (zr A (m+1)).filter (fun Q=>a∈Q.biUnion id):=by
        ext Q; simp only [ql,qa]; tauto
       have hf:Disjoint ((zr A (m+1)).filter (fun Q=>a∉Q.biUnion id))
        ((zr A (m+1)).filter (fun Q=>a∈Q.biUnion id)):=by
        rw [qc]; intro Q h1 h2;exact (qa.mp h1).2 (qa.mp h2).2
       rw [hk,Finset.card_union_of_disjoint hf]
       have hl:(zr A (m+1)).filter (fun Q=>a∉Q.biUnion id)=zr B (m+1):=by
        ext Q;simp only [zr,qa,v7,qj,id_eq,not_exists,not_and];constructor
        · rintro ⟨⟨h4,h3,h5⟩,hi⟩;refine ⟨fun g hgQ=>?_,h3,h5⟩
          have hg:=zD.mp (h4 hgQ);exact zD.mpr ⟨fun u hug=>qh.mpr ⟨fun hua=>hi g hgQ (hua▸hug),hg.1 hug⟩,hg.2⟩
        · rintro ⟨h4,h3,h5⟩;refine ⟨⟨fun g hgQ=>?_,h3,h5⟩,fun g hgQ hag=>?_⟩
          · have hg:=zD.mp (h4 hgQ);exact zD.mpr ⟨hg.1.trans (vj a A),hg.2⟩
          · exact (qh.mp ((zD.mp (h4 hgQ)).1 hag)).1 rfl
       rw [hl,ih r' (by omega) B (m+1) h6]
       cases r' with
       | zero=>
         have hBe:B=∅:=Finset.card_eq_zero.mp h6
         have ht:A={a}:=by
          ext x; by_cases hx:x=a
          · subst hx; simp [haA]
          · simp only [qd,hx,iff_false]; intro hxA;have:x∈B:=qh.mpr ⟨hx,hxA⟩;rw [hBe] at this; exact Finset.notMem_empty x this
         have hem:(zr A (m+1)).filter (fun Q=>a∈Q.biUnion id)=∅:=by
          rw [Finset.eq_empty_iff_forall_notMem]; intro Q hQ;simp only [zr,qa,v7,qj,id_eq] at hQ;rcases hQ.2 with ⟨g,hgQ,_⟩
          have hg:=zD.mp (hQ.1.1 hgQ);have:=qH hg.1;rw [ht,z3,hg.2] at this; omega
         rw [hem,Finset.card_empty]; rfl
       | succ r''=>
         have h7:∀ Q∈(zr A (m+1)).filter (fun Q=>a∈Q.biUnion id),
          ∃! b:α,b∈B∧({a,b}:Finset α)∈Q:=by
          intro Q hQ;simp only [zr,qa,v7,qj,id_eq] at hQ;rcases hQ with ⟨⟨h4,h3,_⟩,⟨g,hgQ,hag⟩⟩
          have hg:=zD.mp (h4 hgQ);have hg1:(g.erase a).card=1:=by rw [zu hag,hg.2]
          rcases Finset.card_eq_one.mp hg1 with ⟨b,hb⟩
          have hbm:b∈g.erase a:=by rw [hb]; simp
          rcases qh.mp hbm with ⟨hba,hbg⟩
          have hbB:b∈B:=qh.mpr ⟨hba,hg.1 hbg⟩
          have hm:g={a,b}:=by
           ext u; by_cases hua:u=a
           · subst hua; simp [hag]
           · have h1:u∈g.erase a↔u=b:=by rw [hb]; simp
             simp only [qh,qe,qd,hua,false_or] at h1 ⊢;exact ⟨fun h=>h1.mp ⟨hua,h⟩,fun h=>(h1.mpr h).2⟩
          refine ⟨b,⟨hbB,hm▸hgQ⟩,fun b' ⟨hq,hQ'⟩=>?_⟩
          by_contra hne
          have h8:({a,b'}:Finset α)≠{a,b}:=by
           intro h; have:b'∈({a,b}:Finset α):=h▸(by simp);simp only [qe,qd] at this;rcases this with rfl|h'
           · exact (qh.mp hq).1 rfl
           · exact hne h'
          exact qc.mp (h3 _ hQ' _ (hm▸hgQ) h8)
           (vx a _) (vx a _)
         set W:=(zr A (m+1)).filter (fun Q=>a∈Q.biUnion id)
         have hn:W=B.biUnion (fun b=>W.filter (fun Q=>({a,b}:Finset α)∈Q)):=by
          ext Q; simp only [qj,qa];constructor
          · intro hQ; rcases h7 Q hQ with ⟨b,⟨hbB,h9⟩,_⟩; exact ⟨b,hbB,hQ,h9⟩
          · rintro ⟨_,_,hQ,_⟩; exact hQ
         have ha:∀ b₁∈B,∀ b₂∈B,b₁≠b₂→
          Disjoint (W.filter (fun Q=>({a,b₁}:Finset α)∈Q))
           (W.filter (fun Q=>({a,b₂}:Finset α)∈Q)):=by
          intro b₁ h1 b₂ h2 hne;rw [qc]; intro Q hQ1 hQ2;rcases qa.mp hQ1 with ⟨hQW,hs⟩
          rcases qa.mp hQ2 with ⟨_,hr⟩
          rcases h7 Q hQW with ⟨b,_,hc⟩
          exact hne ((hc b₁ ⟨h1,hs⟩).trans (hc b₂ ⟨h2,hr⟩).symm)
         rw [show ((zr A (m+1)).filter (fun Q=>a∈Q.biUnion id)).card=W.card from rfl,
          hn,Finset.card_biUnion (fun b₁ h1 b₂ h2 hne=>ha b₁ h1 b₂ h2 hne)]
         have hj:∀ b∈B,(W.filter (fun Q=>({a,b}:Finset α)∈Q)).card=vV r'' m:=by
          intro b hbB;have hba:b≠a:=(qh.mp hbB).1;have hp:(B.erase b).card=r'':=by rw [zu hbB,h6]; omega
          rw [← ih r'' (by omega) (B.erase b) m hp];refine Finset.card_nbij' (fun Q=>Q.erase {a,b}) (fun Q'=>insert {a,b} Q') ?_ ?_ ?_ ?_
          · intro Q hQ;simp only [zQ,W,zr,qa,v7] at hQ ⊢;rcases hQ with ⟨⟨⟨h4,h3,h5⟩,_⟩,h9⟩
            refine ⟨fun g hg=>?_,fun g hg h hh hne=>?_,?_⟩
            · rcases qh.mp hg with ⟨ho,hgQ⟩
              have hg2:=zD.mp (h4 hgQ);have hd:=h3 g hgQ {a,b} h9 ho;refine zD.mpr ⟨fun u hug=>?_,hg2.2⟩
              have huA:=hg2.1 hug;have hua:u≠a:=fun e=>qc.mp hd hug (e▸by simp)
              have hub:u≠b:=fun e=>qc.mp hd hug (e▸by simp)
              exact qh.mpr ⟨hub,qh.mpr ⟨hua,huA⟩⟩
            · exact h3 g (qE hg) h (qE hh) hne
            · rw [zu h9,h5]; omega
          · intro Q' hQ';simp only [zQ,W,zr,qa,v7] at hQ' ⊢;rcases hQ' with ⟨h4,h3,h5⟩
            have he:({a,b}:Finset α)∉Q':=by intro hin;have h1:=(zD.mp (h4 hin)).1 (by simp:b∈({a,b}:Finset α));exact (qh.mp h1).1 rfl
            refine ⟨⟨⟨fun g hg=>?_,fun g hg h hh hne=>?_,?_⟩,?_⟩,vx _ _⟩
            · rcases qe.mp hg with rfl|hgQ'
              · refine zD.mpr ⟨fun u hu=>?_,zv hba.symm⟩
                simp only [qe,qd] at hu;rcases hu with rfl|rfl; exact haA; exact (qh.mp hbB).2
              · have hg2:=zD.mp (h4 hgQ');exact zD.mpr ⟨hg2.1.trans ((vj b B).trans (vj a A)),hg2.2⟩
            · rcases qe.mp hg with rfl|hgQ' <;> rcases qe.mp hh with rfl|hhQ'
              · exact absurd rfl hne
              · rw [qc]; intro u hu1 hu2;have h2:=(zD.mp (h4 hhQ')).1 hu2;simp only [qe,qd] at hu1;rcases hu1 with rfl|rfl
                · exact (qh.mp (qE h2)).1 rfl
                · exact (qh.mp h2).1 rfl
              · rw [qc]; intro u hu1 hu2;have h1:=(zD.mp (h4 hgQ')).1 hu1;simp only [qe,qd] at hu2;rcases hu2 with rfl|rfl
                · exact (qh.mp (qE h1)).1 rfl
                · exact (qh.mp h1).1 rfl
              · exact h3 g hgQ' h hhQ' hne
            · rw [Finset.card_insert_of_notMem he,h5]
            · exact qj.mpr ⟨{a,b},vx _ _,by simp⟩
          · intro Q hQ;exact Finset.insert_erase (qa.mp hQ).2
          · intro Q' hQ';simp only [zQ,zr,qa,v7] at hQ'
            have he:({a,b}:Finset α)∉Q':=by intro hin;have h1:=(zD.mp (hQ'.1 hin)).1 (by simp:b∈({a,b}:Finset α));exact (qh.mp h1).1 rfl
            exact Finset.erase_insert he
         rw [Finset.sum_const_nat hj,h6];rfl
def qr {n:Nat} (F:Q4 n) (u:Fin n):(Q3 n):=(List.range n).foldl (fun V _=>step F V) {u}
def vC {n:Nat} (U:Q3 n) (F:Q4 n):(Q4 n):=U.image (qr F)
def vh {n:Nat} (F:Q4 n) (C:Q3 n):Nat:=(F.filter (fun R=>R⊆C)).card
def ky {n:Nat} (U:Q3 n) (F:Q4 n):(Q4 n):=(vC U F).filter (fun C=>C.card=2 * vh F C+1)
def kX {n:Nat} (U:Q3 n) (F:Q4 n):(Q4 n):=(vC U F).filter (fun C=>C.card=2 * vh F C)
abbrev jj {n:Nat} (U:Q3 n) (F:Q4 n):Prop:=∃ C∈vC U F,C.card<2 * vh F C
lemma j0 {n:Nat} (F:Q4 n) (u:Fin n):
 step F (qr F u)=qr F u:=by
 unfold qr; rw [zY];by_contra hne
 have h0:∀ k≤n,((step F)^[k] {u}).card≥k+1:=by
  intro k hk; induction k with
  | zero=>simp
  | succ k ih=>
    have hk':k≤n:=Nat.le_of_succ_le hk
    have h2:step F ((step F)^[k] {u})≠(step F)^[k] {u}:=by
     intro heq; apply hne;have h1:(step F)^[n] {u}=(step F)^[(n-k)+k] {u}:=by rw [Nat.sub_add_cancel hk']
     rw [h1,iterate_add_apply,ux F heq,heq]
    have hss:(step F)^[k] {u} ⊂ (step F)^[k+1] {u}:=by rw [qM];exact Finset.ssubset_iff_subset_ne.mpr ⟨jo F _,h2.symm⟩
    have:=Finset.card_lt_card hss; have:=ih hk'; omega
 have hbig:=h0 n le_rfl
 have hle:((step F)^[n] {u}).card≤n:=by simpa [Fintype.card_fin] using Finset.card_le_univ ((step F)^[n] {u})
 omega
lemma z7 {n:Nat} (F:Q4 n) (u:Fin n):u∈qr F u:=by unfold qr; rw [zY]; exact j3 F n {u} (Finset.mem_singleton_self u)
lemma qat {n:Nat} (F:Q4 n) {u v:Fin n} (h:v∈qr F u):
 u∈qr F v:=by
 unfold qr at h ⊢; rw [zY] at h ⊢; exact wD F n u v h
lemma vG {n:Nat} (F:Q4 n) {u v:Fin n} (h:v∈qr F u):
 qr F v=qr F u:=by
 have h0:∀ a b,b∈qr F a→qr F b⊆qr F a:=fun a b hab=>by
  calc qr F b=(step F)^[n] {b}:=by unfold qr; rw [zY]
   _⊆(step F)^[n] (qr F a):=uE F n (Finset.singleton_subset_iff.mpr hab)
   _=qr F a:=ux F (j0 F a) n
 exact Finset.Subset.antisymm (h0 u v h) (h0 v u (qat F h))
lemma ye {n:Nat} {U:(Q3 n)} {F:(Q4 n)}
 (hFU:∀ R∈F,R⊆U) {u:Fin n} (hu:u∈U):qr F u⊆U:=by
 unfold qr; rw [zY]
 have h0:∀ k,(step F)^[k] {u}⊆U:=by
  intro k; induction k with
  | zero=>exact Finset.singleton_subset_iff.mpr hu
  | succ k ih=>
    rw [qM]; intro w hw;simp only [step,ql,qj,qa,id_eq] at hw;rcases hw with hw'|⟨R,⟨hRF,_⟩,hwR⟩
    · exact ih hw'
    · exact hFU R hRF hwR
 exact h0 n
lemma qu {n:Nat} (U:Q3 n) (F:Q4 n)
 {C₁ C₂:(Q3 n)} (h1:C₁∈vC U F) (h2:C₂∈vC U F) (hne:C₁≠C₂):
 Disjoint C₁ C₂:=by
 rw [qc]; intro w hw1 hw2; apply hne;rcases qN.mp h1 with ⟨u₁,_,rfl⟩
 rcases qN.mp h2 with ⟨u₂,_,rfl⟩
 exact (vG F hw1).symm.trans (vG F hw2)
lemma y2 {n:Nat} (F:Q4 n) {R:(Q3 n)}
 (hR:R∈F) {u:Fin n} (hu:u∈R):R⊆qr F u:=by
 have h1:R⊆step F (qr F u):=fun w hw=>by simp only [step,ql,qj,qa,id_eq];exact Or.inr ⟨R,⟨hR,vE.mpr ⟨u,hu,z7 F u⟩⟩,hw⟩
 rwa [j0 F u] at h1
lemma j1 {n:Nat} {U:(Q3 n)} {F:(Q4 n)}
 (h3:∀ R∈F,R.card=3) (hFU:∀ R∈F,R⊆U):
 F=(vC U F).biUnion (fun C=>F.filter (fun R=>R⊆C)):=by
 ext R; simp only [qj,qa];constructor
 · intro hR;obtain ⟨u,hu⟩:R.Nonempty:=qU.mp (by rw [h3 R hR]; omega);exact ⟨qr F u,qN.mpr ⟨u,hFU R hR hu,rfl⟩,hR,y2 F hR hu⟩
 · rintro ⟨_,_,hR,_⟩; exact hR
lemma jD {n:Nat} {U:(Q3 n)} {F:(Q4 n)}
 (h3:∀ R∈F,R.card=3) (hFU:∀ R∈F,R⊆U):
 F.card=(vC U F).sum (vh F):=by
 have heq:=j1 h3 hFU
 conv_lhs=>rw [heq]
 rw [Finset.card_biUnion]
 · rfl
 · intro C₁ h1 C₂ h2 hne;dsimp only [Function.onFun]; rw [qc]; intro R hR1 hR2;obtain ⟨u,hu⟩:R.Nonempty:=qU.mp (by rw [h3 R (qa.mp hR1).1]; omega)
   exact qc.mp (qu U F h1 h2 hne)
    ((qa.mp hR1).2 hu) ((qa.mp hR2).2 hu)
lemma kU {n:Nat} {U:(Q3 n)} {F:(Q4 n)}
 {C:(Q3 n)} (hC:C∈vC U F):
 vF C (F.filter (fun R=>R⊆C)):=by
 rcases qN.mp hC with ⟨u₀,_,rfl⟩
 refine ⟨⟨u₀,z7 F u₀⟩,fun S hSne hSss=>?_⟩
 obtain ⟨a,haS⟩:=hSne;have hCa:qr F u₀=qr F a:=(vG F (hSss.1 haS)).symm
 have h4:¬ (step F)^[n] {a}⊆S:=by
  have heq:(step F)^[n] {a}=qr F u₀:=by rw [hCa]; unfold qr; rw [zY]
  rw [heq]; exact hSss.2
 have hex:∃ k<n,(step F)^[k] {a}⊆S∧¬ (step F)^[k+1] {a}⊆S:=by
  by_contra hall; push_neg at hall
  have h5:∀ k≤n,(step F)^[k] {a}⊆S:=by
   intro k hk; induction k with
   | zero=>exact Finset.singleton_subset_iff.mpr haS
   | succ k ih=>exact hall k (Nat.lt_of_succ_le hk) (ih (Nat.le_of_succ_le hk))
  exact h4 (h5 n le_rfl)
 rcases hex with ⟨k,_,h1,h0⟩
 rw [qM,Finset.not_subset] at h0;rcases h0 with ⟨w,hw1,hwS⟩
 simp only [step,ql,qj,qa,id_eq] at hw1;rcases hw1 with hwk|⟨R,⟨hRF,hnd⟩,hwR⟩
 · exact absurd (h1 hwk) hwS
 · have h3:¬ Disjoint R S:=fun hd=>hnd (hd.mono_right h1)
   have h2:¬ R⊆S:=fun hs=>hwS (hs hwR)
   have hRC:R⊆qr F u₀:=by
    rcases vE.mp h3 with ⟨x,hxR,hxS⟩
    rw [← vG F (hSss.1 hxS)];exact y2 F hRF hxR
   exact ⟨R,qa.mpr ⟨hRF,hRC⟩,h3,h2⟩
lemma uV {n:Nat} {U:(Q3 n)} {F:(Q4 n)}
 (h3:∀ R∈F,R.card=3) (hFU:∀ R∈F,R⊆U)
 (hdeg:∀ u,vO F u≤2)
 (hlin:∀ R₁∈F,∀ R₂∈F,R₁≠R₂→(R₁ ∩ R₂).card≤1)
 (s:Nat):
 (q7 U F s).card=if jj U F∨s<F.card then 0
   else 2 ^ (kX U F).card * ((ky U F).prod Finset.card) *
    vV (ky U F).card (s-F.card):=by
 classical
 have h0k:∀ C∈vC U F,C.card≤2 * vh F C+1:=fun C hC=>
  u3 (fun R hR=>h3 R (qa.mp hR).1)
   (fun R hR=>(qa.mp hR).2) (kU hC)
 have hU_biUnion:U=(vC U F).biUnion id:=by
  ext u; simp only [vC,qj,qN,id_eq];constructor
  · intro hu; exact ⟨qr F u,⟨u,hu,rfl⟩,z7 F u⟩
  · rintro ⟨_,⟨v,hv,rfl⟩,huv⟩; exact ye hFU hv huv
 have h11:∀ N∈q7 U F s,¬ jj U F∧F.card≤ s:=by
  intro N hN;simp only [q7,qa,qJ,true_and] at hN;rcases hN with ⟨ho,hi,hG,hZ⟩
  have h2:∀ g∈N,g.card=2:=fun g hg=>(ho g hg).1
  have h18:F.card≤ s:=by rw [← hZ,← vu h3 hlin h2 hi hG];exact qH (yv _ N)
  refine ⟨?_,h18⟩
  rintro ⟨C,hC,hClt⟩;set FC:=F.filter (fun R=>R⊆C);set NC:=N.filter (fun g=>∃ R∈FC,g⊆R)
  have h0l:NC.card=FC.card:=vu
   (fun R hR=>h3 R (qa.mp hR).1)
   (fun R₁ h1 R₂ h2' hne=>hlin R₁ (qa.mp h1).1 R₂ (qa.mp h2').1 hne)
   h2 hi (fun R hR=>hG R (qa.mp hR).1)
  have h0y:NC.biUnion id⊆C:=by
   intro u hu; rcases qj.mp hu with ⟨g,h1g,hug⟩
   rcases (qa.mp h1g).2 with ⟨R,h0e,hgR⟩
   exact (qa.mp h0e).2 (hgR hug)
  have hbi:=yo (M:=NC) (fun g hg=>h2 g (qa.mp hg).1)
   (fun g hg h hh hne=>hi g (qa.mp hg).1 h (qa.mp hh).1 hne)
  have:=qH h0y;rw [hbi,h0l] at this;change 2 * vh F C≤C.card at this;omega
 by_cases hn:jj U F∨s<F.card
 · rw [if_pos hn,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem];intro N hN; have ⟨hnb,hle⟩:=h11 N hN;rcases hn with hb|hlt
   · exact hnb hb
   · omega
 · rw [if_neg hn];have h12:¬ jj U F:=fun h=>hn (Or.inl h)
   have h18:F.card≤ s:=yt (fun h=>hn (Or.inr h))
   have h9:∀ C∈vC U F,C∈ky U F∨C∈kX U F:=by
    intro C hC;have hle:=h0k C hC;have hge:2 * vh F C≤C.card:=yt fun h=>h12 ⟨C,hC,h⟩
    by_cases h:C.card=2 * vh F C
    · exact Or.inr (qa.mpr ⟨hC,h⟩)
    · exact Or.inl (qa.mpr ⟨hC,by omega⟩)
   have hk:Disjoint (ky U F) (kX U F):=by rw [qc]; intro C h1 h2;have:=(qa.mp h1).2; have:=(qa.mp h2).2; omega
   set Cyc:=kX U F;set Tr:=ky U F;set P_cyc:=Cyc.pi (fun C=>zi C (F.filter (fun R=>R⊆C)));set P_tr:=Tr.pi id;set P_m:=zr Tr (s-F.card)
   have h0q:∀ C:Q3 n,∀ u,vO (F.filter (fun R=>R⊆C)) u≤2:=fun C u=>(qH (Finset.filter_subset_filter _ (yv _ F))).trans (hdeg u)
   have hl:∀ C:Q3 n,∀ R₁∈F.filter (fun R=>R⊆C),
    ∀ R₂∈F.filter (fun R=>R⊆C),R₁≠R₂→(R₁ ∩ R₂).card≤1:=fun C R₁ h1 R₂ h2 hne=>
    hlin R₁ (qa.mp h1).1 R₂ (qa.mp h2).1 hne
   have h05:∀ C∈Cyc,(zi C (F.filter (fun R=>R⊆C))).card=2:=by
    intro C hC;rcases qa.mp hC with ⟨hCp,hCc⟩
    exact u5 (vh F C) C (F.filter (fun R=>R⊆C)) rfl
     (fun R hR=>h3 R (qa.mp hR).1) (fun R hR=>(qa.mp hR).2)
     (h0q C) (hl C) (kU hCp) hCc
   have hO:∀ C∈Tr,∀ r∈C,(zg C (F.filter (fun R=>R⊆C)) r).card=1:=by
    intro C hC r hr;rcases qa.mp hC with ⟨hCp,hCc⟩
    exact km (vh F C) C (F.filter (fun R=>R⊆C)) r rfl
     (fun R hR=>h3 R (qa.mp hR).1) (fun R hR=>(qa.mp hR).2)
     (h0q C) (hl C) (kU hCp) hr hCc
   let treeM:(C:Q3 n)→(r:Fin n)→(Q4 n):=fun C r=>if h:(zg C (F.filter (fun R=>R⊆C)) r).Nonempty then h.choose else ∅
   have h5:∀ C∈Tr,∀ r∈C,treeM C r∈zg C (F.filter (fun R=>R⊆C)) r:=by
    intro C hC r hr
    have hne:(zg C (F.filter (fun R=>R⊆C)) r).Nonempty:=qU.mp (by rw [hO C hC r hr]; omega)
    simp only [treeM,hne,↓reduceDIte];exact hne.choose_spec
   have hQ:∀ C∈Tr,∀ r∈C,∀ M∈zg C (F.filter (fun R=>R⊆C)) r,M=treeM C r:=by
    intro C hC r hr M hM;have h1:=hO C hC r hr;rcases Finset.card_eq_one.mp h1 with ⟨M₀,hM₀⟩
    have h1':M=M₀:=by rw [hM₀] at hM; exact qd.mp hM
    have h2':treeM C r=M₀:=by have:=h5 C hC r hr; rw [hM₀] at this; exact qd.mp this
    exact h1'.trans h2'.symm
   have h02:P_cyc.card=2 ^ Cyc.card:=by
    rw [uc]
    calc Cyc.prod (fun C=>(zi C (F.filter (fun R=>R⊆C))).card)=Cyc.prod (fun _=>2):=Finset.prod_congr rfl h05
     _=2 ^ Cyc.card:=Finset.prod_const 2
   have h06:P_tr.card=Tr.prod Finset.card:=by rw [uc]; rfl
   have h0f:P_m.card=vV Tr.card (s-F.card):=wy Tr.card Tr (s-F.card) rfl
   rw [← h02,← h06,← h0f,← Finset.card_product,← Finset.card_product]
   let Nint:Q4 n→(Q3 n)→(Q4 n):=fun N C=>N.filter (fun g=>∃ R∈F.filter (fun R=>R⊆C),g⊆R)
   have h7:∀ N∈q7 U F s,
    (∀ C∈Cyc,Nint N C∈zi C (F.filter (fun R=>R⊆C)))∧
    (∀ C∈Tr,∃! r:Fin n,r∈C∧r∉(Nint N C).biUnion id)∧
    (∀ C∈Tr,∀ r∈C,r∉(Nint N C).biUnion id→Nint N C=treeM C r):=by
    intro N hN;simp only [q7,qa,qJ,true_and] at hN;rcases hN with ⟨ho,hi,hG,_⟩
    have h2:∀ g∈N,g.card=2:=fun g hg=>(ho g hg).1
    have h03:∀ C∈vC U F,(Nint N C).card=vh F C:=fun C _=>
     vu (fun R hR=>h3 R (qa.mp hR).1) (hl C)
      h2 hi (fun R hR=>hG R (qa.mp hR).1)
    have hs:∀ C∈vC U F,∀ g∈Nint N C,g⊆C:=by
     intro C _ g hg;rcases (qa.mp hg).2 with ⟨R,h0e,hgR⟩
     exact hgR.trans (qa.mp h0e).2
    refine ⟨?_,?_,?_⟩
    · intro C hC;simp only [zi,qa,qJ,true_and]
      refine ⟨fun g hg=>⟨h2 g (qa.mp hg).1,hs C (qa.mp hC).1 g hg⟩,
       fun g hg h hh hne=>hi g (qa.mp hg).1 h (qa.mp hh).1 hne,
       fun R hR=>?_⟩
      rcases hG R hR.1 with ⟨g,hgN,hgR⟩
      exact ⟨g,qa.mpr ⟨hgN,R,qa.mpr hR,hgR⟩,hgR⟩
    · intro C hC;have hCp:=(qa.mp hC).1;have hCc:=(qa.mp hC).2
      have h00:(Nint N C).biUnion id⊆C:=fun u hu=>by rcases qj.mp hu with ⟨g,hg,hug⟩; exact hs C hCp g hg hug
      have hbi:((Nint N C).biUnion id).card=2 * vh F C:=by
       rw [yo (fun g hg=>h2 g (qa.mp hg).1)
        (fun g hg h hh hne=>hi g (qa.mp hg).1 h (qa.mp hh).1 hne),
        h03 C hCp]
      have hP:(C \ (Nint N C).biUnion id).card=1:=by rw [Finset.card_sdiff_of_subset h00,hCc,hbi]; omega
      rcases Finset.card_eq_one.mp hP with ⟨r,hr⟩
      have hrm:r∈C \ (Nint N C).biUnion id:=by rw [hr]; simp
      refine ⟨r,qg.mp hrm,fun r' hr'=>?_⟩
      have:r'∈C \ (Nint N C).biUnion id:=qg.mpr hr';rw [hr,qd] at this; exact this
    · intro C hC r hr h0t;have hCp:=(qa.mp hC).1;refine hQ C hC r hr (Nint N C) ?_
      simp only [zg,qa,qJ,true_and]
      refine ⟨fun g hg=>⟨h2 g (qa.mp hg).1,fun u hug=>
       qh.mpr ⟨fun hur=>h0t (qj.mpr ⟨g,hg,hur▸hug⟩),
        hs C hCp g hg hug⟩⟩,
       fun g hg h hh hne=>hi g (qa.mp hg).1 h (qa.mp hh).1 hne,
       fun R hR=>?_⟩
      rcases hG R hR.1 with ⟨g,hgN,hgR⟩
      exact ⟨g,qa.mpr ⟨hgN,R,qa.mpr hR,hgR⟩,hgR⟩
   let getRoot:(N:Q4 n)→(C:Q3 n)→(hC:C∈Tr)→Fin n:=
    fun N C hC=>
     if h:(C \ (Nint N C).biUnion id).Nonempty then h.choose
     else (qN.mp (qa.mp hC).1).choose
   have hf:∀ N∈q7 U F s,∀ C (hC:C∈Tr),
    getRoot N C hC∈C∧getRoot N C hC∉(Nint N C).biUnion id:=by
    intro N hN C hC;rcases (h7 N hN).2.1 C hC with ⟨r,⟨hrC,h0a⟩,_⟩
    have hne:(C \ (Nint N C).biUnion id).Nonempty:=⟨r,qg.mpr ⟨hrC,h0a⟩⟩;simp only [getRoot,hne,↓reduceDIte];exact qg.mp hne.choose_spec
   have hU:∀ N∈q7 U F s,∀ C (hC:C∈Tr),∀ r∈C,
    r∉(Nint N C).biUnion id→ getRoot N C hC=r:=by
    intro N hN C hC r hrC h0a;rcases (h7 N hN).2.1 C hC with ⟨r₀,_,h0n⟩
    have hg:=hf N hN C hC;exact (h0n (getRoot N C hC) hg).trans (h0n r ⟨hrC,h0a⟩).symm
   let Nextra:Q4 n→(Q4 n):=fun N=>N.filter (fun g=>¬ ∃ R∈F,g⊆R)
   let toQ:Q4 n→Finset ((Q4 n)):=fun N=>(Nextra N).image (fun g=>g.image (qr F))
   let pairOf:(∀ C∈Tr,Fin n)→(Q4 n)→(Q3 n):=fun r e=>(Tr.attach.filter (fun C=>C.1∈e)).image (fun C=>r C.1 C.2)
   let fromTriple:((∀ C∈Cyc,(Q4 n))×(∀ C∈Tr,Fin n))×
       Finset ((Q4 n))→(Q4 n):=fun z=>
    (Cyc.attach.biUnion (fun C=>z.1.1 C.1 C.2)) ∪
    (Tr.attach.biUnion (fun C=>treeM C.1 (z.1.2 C.1 C.2))) ∪
    (z.2.image (pairOf z.1.2))
   have h4:∀ (r:∀ C∈Tr,Fin n),(∀ C (hC:C∈Tr),r C hC∈C)→
    ∀ {C₁ C₂:(Q3 n)} (h1:C₁∈Tr) (h2:C₂∈Tr),C₁≠C₂→
      pairOf r {C₁,C₂}={r C₁ h1,r C₂ h2}∧r C₁ h1≠r C₂ h2:=by
    intro r hr C₁ C₂ h1 h2 hne
    have h0r:r C₁ h1≠r C₂ h2:=fun heq=>qc.mp (qu U F (qa.mp h1).1 (qa.mp h2).1 hne) (hr C₁ h1) (heq▸hr C₂ h2)
    refine ⟨?_,h0r⟩
    ext u; simp only [pairOf,qN,qa,Finset.mem_attach,true_and,qe,qd];constructor
    · rintro ⟨⟨C,hC⟩,rfl|rfl,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl|rfl)
      · exact ⟨⟨C₁,h1⟩,Or.inl rfl,rfl⟩
      · exact ⟨⟨C₂,h2⟩,Or.inr rfl,rfl⟩
   have h0:∀ C∈vC U F,∀ u∈C,qr F u=C:=by intro C hC u hu; rcases qN.mp hC with ⟨v,_,rfl⟩; exact vG F hu
   have hx:vC U F=Cyc ∪ Tr:=by
    ext C; simp only [ql];constructor
    · intro hC; rcases h9 C hC with h|h; exact Or.inr h; exact Or.inl h
    · rintro (h|h); exact (qa.mp h).1; exact (qa.mp h).1
   have h6:∀ N∈q7 U F s,∀ g∈Nextra N,
    ∃ (u v:Fin n) (hu:qr F u∈Tr) (hv:qr F v∈Tr),u≠v∧qr F u≠qr F v∧g={u,v}∧
      getRoot N (qr F u) hu=u∧getRoot N (qr F v) hv=v:=by
    intro N hN g hg;rcases qa.mp hg with ⟨hgN,h1f⟩
    simp only [q7,qa,qJ,true_and] at hN;rcases hN with ⟨ho,hi,hG,hZ⟩
    have hN':N∈q7 U F s:=qa.mpr ⟨qJ _,ho,hi,hG,hZ⟩;rcases yk.mp (ho g hgN).1 with ⟨u,v,huv,hV⟩
    have hpt:∀ w∈g,∃ hw:qr F w∈Tr,getRoot N (qr F w) hw=w:=by
     intro w hwg;have hwU:w∈U:=(ho g hgN).2 hwg;have hwP:qr F w∈vC U F:=qN.mpr ⟨w,hwU,rfl⟩
     have h0m:w∉(Nint N (qr F w)).biUnion id:=by
      intro h19;rcases qj.mp h19 with ⟨h,hh,hwh⟩
      rcases qa.mp hh with ⟨hhN,R,h0e,hhR⟩
      have hne:g≠h:=fun e=>h1f ⟨R,(qa.mp h0e).1,e▸hhR⟩
      exact qc.mp (hi g hgN h hhN hne) hwg hwh
     have h0z:qr F w∈Tr:=by
      rcases h9 _ hwP with h|h
      · exact h
      · exfalso;have h14:=(h7 N hN').1 _ h
        have hbi:=(vA (fun R hR=>h3 R (qa.mp hR).1)
         (hl _) (qa.mp h).2 h14).2.1
        exact h0m (hbi.symm▸z7 F w)
     exact ⟨h0z,hU N hN' (qr F w) h0z w (z7 F w) h0m⟩
    rcases hpt u (hV▸by simp) with ⟨h1b,hur⟩
    rcases hpt v (hV▸by simp) with ⟨h1a,hvr⟩
    have hj:qr F u≠qr F v:=by intro heq; apply huv;rw [← hur,← hvr]; congr 1
    exact ⟨u,v,h1b,h1a,huv,hj,hV,hur,hvr⟩
   refine Finset.card_nbij'
    (fun N=>((fun C _=>Nint N C,fun C hC=>getRoot N C hC),toQ N))
    fromTriple ?_ ?_ ?_ ?_
   · intro N hN;simp only [zQ] at hN ⊢;have hNV:=hN;simp only [q7,qa,qJ,true_and] at hNV;rcases hNV with ⟨ho,hi,hG,hZ⟩
     have h2:∀ g∈N,g.card=2:=fun g hg=>(ho g hg).1
     simp only [Finset.mem_product,P_cyc,P_tr,P_m,Finset.mem_pi,id_eq,zr,qa,v7];refine ⟨⟨(h7 N hN).1,fun C hC=>(hf N hN C hC).1⟩,?_,?_,?_⟩
     · intro e he;rcases qN.mp he with ⟨g,hg,rfl⟩
       rcases h6 N hN g hg with ⟨u,v,hu,hv,_,hj,rfl,_,_⟩
       have h01:({u,v}:Q3 n).image (qr F)={qr F u,qr F v}:=by ext C; simp
       rw [h01];refine zD.mpr ⟨fun C hC=>?_,zv hj⟩
       simp only [qe,qd] at hC;rcases hC with rfl|rfl; exact hu; exact hv
     · intro e₁ he₁ e₂ he₂ hne;rcases qN.mp he₁ with ⟨g₁,hg₁,rfl⟩
       rcases qN.mp he₂ with ⟨g₂,hg₂,rfl⟩
       have h1e:g₁≠g₂:=fun h=>hne (h▸rfl)
       rcases h6 N hN g₁ hg₁ with ⟨u₁,v₁,hu₁,hv₁,_,_,hA,hru₁,hrv₁⟩
       rcases h6 N hN g₂ hg₂ with ⟨u₂,v₂,hu₂,hv₂,_,_,hI,hru₂,hrv₂⟩
       rw [qc]; intro C hC1 hC2;rw [hA] at hC1; rw [hI] at hC2;simp only [qN,qe,qd] at hC1 hC2;have hhd:=hi g₁ (qa.mp hg₁).1 g₂ (qa.mp hg₂).1 h1e;rw [hA,hI] at hhd;rcases hC1 with ⟨a,ha|ha,haC⟩ <;> rcases hC2 with ⟨b,hb|hb,hbC⟩
       · have heq:qr F u₁=qr F u₂:=by rw [← ha,← hb,haC,hbC]
         have hu:u₁=u₂:=by rw [← hru₁,← hru₂]; congr 1
         exact qc.mp hhd (by simp:u₁∈({u₁,v₁}:Q3 n)) (by rw [hu]; simp)
       · have heq:qr F u₁=qr F v₂:=by rw [← ha,← hb,haC,hbC]
         have hu:u₁=v₂:=by rw [← hru₁,← hrv₂]; congr 1
         exact qc.mp hhd (by simp:u₁∈({u₁,v₁}:Q3 n)) (by rw [hu]; simp)
       · have heq:qr F v₁=qr F u₂:=by rw [← ha,← hb,haC,hbC]
         have hv:v₁=u₂:=by rw [← hrv₁,← hru₂]; congr 1
         exact qc.mp hhd (by simp:v₁∈({u₁,v₁}:Q3 n)) (by rw [hv]; simp)
       · have heq:qr F v₁=qr F v₂:=by rw [← ha,← hb,haC,hbC]
         have hv:v₁=v₂:=by rw [← hrv₁,← hrv₂]; congr 1
         exact qc.mp hhd (by simp:v₁∈({u₁,v₁}:Q3 n)) (by rw [hv]; simp)
     · have h1d:Set.InjOn (fun g:Q3 n=>g.image (qr F)) (Nextra N:Set _):=by
        intro g₁ hg₁ g₂ hg₂ heq;dsimp only at heq;rcases h6 N hN g₁ hg₁ with ⟨u₁,v₁,hu₁,hv₁,h10,_,hA,hru₁,hrv₁⟩
        rcases h6 N hN g₂ hg₂ with ⟨u₂,v₂,hu₂,hv₂,_,_,hI,hru₂,hrv₂⟩
        have h1:qr F u₁∈g₂.image (qr F):=by rw [← heq]; exact qN.mpr ⟨u₁,hA▸by simp,rfl⟩
        have h2:qr F v₁∈g₂.image (qr F):=by rw [← heq]; exact qN.mpr ⟨v₁,hA▸by simp,rfl⟩
        rw [hI] at h1 h2;simp only [qN,qe,qd] at h1 h2;rcases h1 with ⟨a,ha|ha,haC⟩ <;> rcases h2 with ⟨b,hb|hb,hbC⟩
        · have e1:u₁=u₂:=by rw [← hru₁,← hru₂]; congr 1; rw [← haC,ha]
          have e2:v₁=u₂:=by rw [← hrv₁,← hru₂]; congr 1; rw [← hbC,hb]
          exact absurd (e1.trans e2.symm) h10
        · have e1:u₁=u₂:=by rw [← hru₁,← hru₂]; congr 1; rw [← haC,ha]
          have e2:v₁=v₂:=by rw [← hrv₁,← hrv₂]; congr 1; rw [← hbC,hb]
          rw [hA,hI,e1,e2]
        · have e1:u₁=v₂:=by rw [← hru₁,← hrv₂]; congr 1; rw [← haC,ha]
          have e2:v₁=u₂:=by rw [← hrv₁,← hru₂]; congr 1; rw [← hbC,hb]
          rw [hA,hI,e1,e2,Finset.pair_comm]
        · have e1:u₁=v₂:=by rw [← hru₁,← hrv₂]; congr 1; rw [← haC,ha]
          have e2:v₁=v₂:=by rw [← hrv₁,← hrv₂]; congr 1; rw [← hbC,hb]
          exact absurd (e1.trans e2.symm) h10
       rw [Finset.card_image_of_injOn h1d];have h0s:=Finset.card_filter_add_card_filter_not (s:=N) (p:=fun g=>∃ R∈F,g⊆R);have h0u:=vu h3 hlin h2 hi hG;rw [h0u,hZ] at h0s;change (N.filter (fun g=>¬ ∃ R∈F,g⊆R)).card=s-F.card;omega
   · rintro ⟨⟨fc,r⟩,Q⟩ hz;simp only [zQ,Finset.mem_product,P_cyc,P_tr,P_m,Finset.mem_pi,id_eq,zr,qa,v7] at hz;rcases hz with ⟨⟨hfc,hr⟩,hQsub,hQdisj,hQcard⟩
     set N_cyc:=Cyc.attach.biUnion (fun C=>fc C.1 C.2);set N_tr:=Tr.attach.biUnion (fun C=>treeM C.1 (r C.1 C.2));set N_ex:=Q.image (pairOf r)
     have hq:∀ g∈N_cyc,∃ (C:Q3 n) (hC:C∈Cyc),
      g∈fc C hC∧g.card=2∧g⊆C:=by
      intro g hg; rcases qj.mp hg with ⟨⟨C,hC⟩,_,hgf⟩
      have hm:=(qa.mp (hfc C hC)).2.1 g hgf;exact ⟨C,hC,hgf,hm.1,hm.2⟩
     have hS:∀ g∈N_tr,∃ (C:Q3 n) (hC:C∈Tr),
      g∈treeM C (r C hC)∧g.card=2∧g⊆C.erase (r C hC):=by
      intro g hg; rcases qj.mp hg with ⟨⟨C,hC⟩,_,hgf⟩
      have hm:=(qa.mp (h5 C hC (r C hC) (hr C hC))).2.1 g hgf;exact ⟨C,hC,hgf,hm.1,hm.2⟩
     have hJ:∀ g∈N_ex,∃ (e:Q4 n) (C₁ C₂:Q3 n)
      (h1:C₁∈Tr) (h2:C₂∈Tr),e∈Q∧C₁≠C₂∧e={C₁,C₂}∧
      g={r C₁ h1,r C₂ h2}∧r C₁ h1≠r C₂ h2:=by
      intro g hg; rcases qN.mp hg with ⟨e,heQ,rfl⟩
      have he2:=zD.mp (hQsub heQ);rcases yk.mp he2.2 with ⟨C₁,C₂,hj,hW⟩
      have h1:C₁∈Tr:=he2.1 (hW▸by simp);have h2:C₂∈Tr:=he2.1 (hW▸by simp);have hp:=h4 r hr h1 h2 hj;exact ⟨e,C₁,C₂,h1,h2,heQ,hj,hW,hW▸hp.1,hp.2⟩
     have hD:∀ g∈N_cyc,∀ h∈N_tr,Disjoint g h:=by
      intro g hg h hh;rcases hq g hg with ⟨C₁,h1,_,_,hg1⟩
      rcases hS h hh with ⟨C₂,h2,_,_,hh2⟩
      have hne:C₁≠C₂:=fun e=>qc.mp hk h2 (e▸h1)
      exact (qu U F (qa.mp h1).1 (qa.mp h2).1 hne).mono
       hg1 (hh2.trans (vj _ _))
     have hE:∀ g∈N_cyc,∀ h∈N_ex,Disjoint g h:=by
      intro g hg h hh;rcases hq g hg with ⟨C,hC,_,_,hgC⟩
      rcases hJ h hh with ⟨_,C₁,C₂,h1,h2,_,_,_,rfl,_⟩
      rw [qc]; intro u hug huh;simp only [qe,qd] at huh;rcases huh with rfl|rfl
      · have hne:C≠C₁:=fun e=>qc.mp hk h1 (e▸hC)
        exact qc.mp (qu U F (qa.mp hC).1 (qa.mp h1).1 hne) (hgC hug) (hr C₁ h1)
      · have hne:C≠C₂:=fun e=>qc.mp hk h2 (e▸hC)
        exact qc.mp (qu U F (qa.mp hC).1 (qa.mp h2).1 hne) (hgC hug) (hr C₂ h2)
     have hB:∀ g∈N_tr,∀ h∈N_ex,Disjoint g h:=by
      intro g hg h hh;rcases hS g hg with ⟨C,hC,_,_,hgC⟩
      rcases hJ h hh with ⟨_,C₁,C₂,h1,h2,_,_,_,rfl,_⟩
      rw [qc]; intro u hug huh;simp only [qe,qd] at huh;rcases huh with rfl|rfl
      · by_cases heq:C=C₁
        · subst heq; exact (qh.mp (hgC hug)).1 rfl
        · exact qc.mp (qu U F (qa.mp hC).1 (qa.mp h1).1 heq) (qE (hgC hug)) (hr C₁ h1)
      · by_cases heq:C=C₂
        · subst heq; exact (qh.mp (hgC hug)).1 rfl
        · exact qc.mp (qu U F (qa.mp hC).1 (qa.mp h2).1 heq) (qE (hgC hug)) (hr C₂ h2)
     have h0d:∀ g∈N_cyc,∀ h∈N_cyc,g≠h→Disjoint g h:=by
      intro g hg h hh hne;rcases hq g hg with ⟨C₁,h1,hg1,_,h09⟩
      rcases hq h hh with ⟨C₂,h2,hh2,_,h08⟩
      by_cases hc:C₁=C₂
      · subst hc; exact (qa.mp (hfc C₁ h1)).2.2.1 g hg1 h hh2 hne
      · exact (qu U F (qa.mp h1).1 (qa.mp h2).1 hc).mono h09 h08
     have h0b:∀ g∈N_tr,∀ h∈N_tr,g≠h→Disjoint g h:=by
      intro g hg h hh hne;rcases hS g hg with ⟨C₁,h1,hg1,_,h09⟩
      rcases hS h hh with ⟨C₂,h2,hh2,_,h08⟩
      by_cases hc:C₁=C₂
      · subst hc; exact (qa.mp (h5 C₁ h1 (r C₁ h1) (hr C₁ h1))).2.2.1 g hg1 h hh2 hne
      · exact (qu U F (qa.mp h1).1 (qa.mp h2).1 hc).mono
         (h09.trans (vj _ _)) (h08.trans (vj _ _))
     have h0c:∀ g∈N_ex,∀ h∈N_ex,g≠h→Disjoint g h:=by
      intro g hg h hh hne;rcases hJ g hg with ⟨e₁,C₁,C₂,h1,h2,he1,_,hL,rfl,_⟩
      rcases hJ h hh with ⟨e₂,D₁,D₂,hd1,hd2,he2,_,hK,rfl,_⟩
      have h1h:e₁≠e₂:=by
       intro heq; apply hne
       have h1':pairOf r e₁={r C₁ h1,r C₂ h2}:=hL▸(h4 r hr h1 h2 (by
        intro h; subst h; have:=(zD.mp (hQsub he1)).2; rw [hL] at this; simp at this)).1
       have h2':pairOf r e₂={r D₁ hd1,r D₂ hd2}:=hK▸(h4 r hr hd1 hd2 (by
        intro h; subst h; have:=(zD.mp (hQsub he2)).2; rw [hK] at this; simp at this)).1
       rw [← h1',← h2',heq]
      have hed:=hQdisj e₁ he1 e₂ he2 h1h
      have hy:∀ X∈e₁,∀ Y∈e₂,X≠Y:=fun X hX Y hY hXY=>qc.mp hed hX (hXY▸hY)
      rw [qc]; intro u hu1 hu2;simp only [qe,qd] at hu1 hu2;rcases hu1 with rfl|rfl <;> rcases hu2 with heq|heq
      · exact qc.mp (qu U F (qa.mp h1).1
         (qa.mp hd1).1 (hy C₁ (hL▸by simp) D₁ (hK▸by simp)))
         (hr C₁ h1) (heq▸hr D₁ hd1)
      · exact qc.mp (qu U F (qa.mp h1).1
         (qa.mp hd2).1 (hy C₁ (hL▸by simp) D₂ (hK▸by simp)))
         (hr C₁ h1) (heq▸hr D₂ hd2)
      · exact qc.mp (qu U F (qa.mp h2).1
         (qa.mp hd1).1 (hy C₂ (hL▸by simp) D₁ (hK▸by simp)))
         (hr C₂ h2) (heq▸hr D₁ hd1)
      · exact qc.mp (qu U F (qa.mp h2).1
         (qa.mp hd2).1 (hy C₂ (hL▸by simp) D₂ (hK▸by simp)))
         (hr C₂ h2) (heq▸hr D₂ hd2)
     simp only [zQ,q7,qa,qJ,true_and,fromTriple];refine ⟨?_,?_,?_,?_⟩
     · intro g hg;rcases ql.mp hg with hct|hex
       · rcases ql.mp hct with hc|ht
         · rcases hq g hc with ⟨C,hC,_,hg2,hgC⟩
           rcases qN.mp (qa.mp hC).1 with ⟨u,huU,rfl⟩
           exact ⟨hg2,hgC.trans (ye hFU huU)⟩
         · rcases hS g ht with ⟨C,hC,_,hg2,hgC⟩
           rcases qN.mp (qa.mp hC).1 with ⟨u,huU,rfl⟩
           exact ⟨hg2,(hgC.trans (vj _ _)).trans (ye hFU huU)⟩
       · rcases hJ g hex with ⟨_,C₁,C₂,h1,h2,_,_,_,rfl,h0r⟩
         refine ⟨zv h0r,fun u hu=>?_⟩
         simp only [qe,qd] at hu;rcases hu with rfl|rfl
         · rcases qN.mp (qa.mp h1).1 with ⟨a,haU,hCa⟩
           exact ye hFU haU (hCa▸hr C₁ h1)
         · rcases qN.mp (qa.mp h2).1 with ⟨a,haU,hCa⟩
           exact ye hFU haU (hCa▸hr C₂ h2)
     · intro g hg h hh hne;rcases ql.mp hg with h17|he1 <;> rcases ql.mp hh with h16|he2
       · rcases ql.mp h17 with hc1|ht1 <;> rcases ql.mp h16 with hc2|ht2
         · exact h0d g hc1 h hc2 hne
         · exact hD g hc1 h ht2
         · exact (hD h hc2 g ht1).symm
         · exact h0b g ht1 h ht2 hne
       · rcases ql.mp h17 with hc1|ht1
         · exact hE g hc1 h he2
         · exact hB g ht1 h he2
       · rcases ql.mp h16 with hc2|ht2
         · exact (hE h hc2 g he1).symm
         · exact (hB h ht2 g he1).symm
       · exact h0c g he1 h he2 hne
     · intro R hR;obtain ⟨u,hu⟩:R.Nonempty:=qU.mp (by rw [h3 R hR]; omega);have hCp:qr F u∈vC U F:=qN.mpr ⟨u,hFU R hR hu,rfl⟩
       have hRC:R∈F.filter (fun R'=>R'⊆qr F u):=qa.mpr ⟨hR,y2 F hR hu⟩
       rcases h9 _ hCp with hT|hC
       · rcases (qa.mp (h5 _ hT (r _ hT) (hr _ hT))).2.2.2 R hRC with ⟨g,hg,hgR⟩
         exact ⟨g,Finset.mem_union_left _ (Finset.mem_union_right _ (qj.mpr ⟨⟨qr F u,hT⟩,Finset.mem_attach _ _,hg⟩)),hgR⟩
       · rcases (qa.mp (hfc _ hC)).2.2.2 R hRC with ⟨g,hg,hgR⟩
         exact ⟨g,Finset.mem_union_left _ (Finset.mem_union_left _ (qj.mpr ⟨⟨qr F u,hC⟩,Finset.mem_attach _ _,hg⟩)),hgR⟩
     · have h15:Disjoint N_cyc N_tr:=by
        rw [qc]; intro g h1 h2;rcases hq g h1 with ⟨_,_,_,hg2,_⟩
        obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega);exact qc.mp (hD g h1 g h2) hu hu
       have h0x:Disjoint (N_cyc ∪ N_tr) N_ex:=by
        rw [qc]; intro g h1 h2;rcases hJ g h2 with ⟨_,C₁,C₂,hc1,hc2,_,_,_,hV,_⟩
        have hm:r C₁ hc1∈g:=hV▸by simp
        rcases ql.mp h1 with hc|ht
        · exact qc.mp (hE g hc g h2) hm hm
        · exact qc.mp (hB g ht g h2) hm hm
       have h0j:N_cyc.card=Cyc.sum (vh F):=by
        rw [Finset.card_biUnion]
        · trans Cyc.attach.sum (fun C=>vh F C.1)
          · refine Finset.sum_congr rfl fun C _=>?_
            exact (vA (fun R hR=>h3 R (qa.mp hR).1) (hl C)
             (qa.mp C.2).2 (hfc C.1 C.2)).1
          · exact Finset.sum_attach Cyc (vh F)
        · intro C₁ _ C₂ _ hne;dsimp only [Function.onFun]; rw [qc]; intro g hg1 hg2;have h1:=(qa.mp (hfc C₁.1 C₁.2)).2.1 g hg1;have h2:=(qa.mp (hfc C₂.1 C₂.2)).2.1 g hg2;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega)
          exact qc.mp (qu U F (qa.mp C₁.2).1
           (qa.mp C₂.2).1 (fun e=>hne (Subtype.ext e))) (h1.2 hu) (h2.2 hu)
       have h0g:N_tr.card=Tr.sum (vh F):=by
        rw [Finset.card_biUnion]
        · trans Tr.attach.sum (fun C=>vh F C.1)
          · refine Finset.sum_congr rfl fun C _=>?_
            exact (yg (fun R hR=>h3 R (qa.mp hR).1) (hl C)
             (hr C.1 C.2) (qa.mp C.2).2 (h5 C.1 C.2 (r C.1 C.2) (hr C.1 C.2))).1
          · exact Finset.sum_attach Tr (vh F)
        · intro C₁ _ C₂ _ hne;dsimp only [Function.onFun]; rw [qc]; intro g hg1 hg2;have h1:=(qa.mp (h5 C₁.1 C₁.2 (r C₁.1 C₁.2) (hr C₁.1 C₁.2))).2.1 g hg1;have h2:=(qa.mp (h5 C₂.1 C₂.2 (r C₂.1 C₂.2) (hr C₂.1 C₂.2))).2.1 g hg2;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega)
          exact qc.mp (qu U F (qa.mp C₁.2).1
           (qa.mp C₂.2).1 (fun e=>hne (Subtype.ext e)))
           (qE (h1.2 hu)) (qE (h2.2 hu))
       have h0i:N_ex.card=s-F.card:=by
        rw [Finset.card_image_of_injOn,hQcard];intro e₁ he₁ e₂ he₂ heq;have h0w:=zD.mp (hQsub he₁);have h0v:=zD.mp (hQsub he₂);rcases yk.mp h0w.2 with ⟨C₁,C₂,hj,rfl⟩
        rcases yk.mp h0v.2 with ⟨D₁,D₂,h1j,rfl⟩
        have h1:C₁∈Tr:=h0w.1 (by simp); have h2:C₂∈Tr:=h0w.1 (by simp);have hd1:D₁∈Tr:=h0v.1 (by simp); have hd2:D₂∈Tr:=h0v.1 (by simp);rw [(h4 r hr h1 h2 hj).1,(h4 r hr hd1 hd2 h1j).1] at heq;have hm1:r C₁ h1∈({r D₁ hd1,r D₂ hd2}:Q3 n):=heq▸by simp
        have hm2:r C₂ h2∈({r D₁ hd1,r D₂ hd2}:Q3 n):=heq▸by simp
        have h8:∀ {X Y:(Q3 n)} (hX:X∈Tr) (hY:Y∈Tr),
         r X hX=r Y hY→X=Y:=fun {X Y} hX hY hxy=>by
         have h1c:=h0 X (qa.mp hX).1 (r X hX) (hr X hX);have h2c:=h0 Y (qa.mp hY).1 (r Y hY) (hr Y hY);rw [← h1c,hxy,h2c]
        simp only [qe,qd] at hm1 hm2;rcases hm1 with e1|e1 <;> rcases hm2 with e2|e2
        · exact absurd ((h8 h1 hd1 e1).trans (h8 h2 hd1 e2).symm) hj
        · rw [h8 h1 hd1 e1,h8 h2 hd2 e2]
        · rw [h8 h1 hd2 e1,h8 h2 hd1 e2,Finset.pair_comm]
        · exact absurd ((h8 h1 hd2 e1).trans (h8 h2 hd2 e2).symm) hj
       rw [Finset.card_union_of_disjoint h0x,Finset.card_union_of_disjoint h15,h0j,h0g,h0i,← Finset.sum_union hk.symm,← hx,← jD h3 hFU];omega
   · intro N hN;simp only [zQ] at hN;have h0o:∀ C (hC:C∈Tr),getRoot N C hC∈C:=fun C hC=>(hf N hN C hC).1
     ext g;simp only [fromTriple,ql,qj,Finset.mem_attach,true_and,Subtype.exists,qN,toQ];constructor
     · rintro ((⟨C,hC,hgf⟩|⟨C,hC,hgf⟩)|⟨e,⟨g',hg',rfl⟩,rfl⟩)
       · exact (qa.mp hgf).1
       · have htr:=(h7 N hN).2.2 C hC (getRoot N C hC) (hf N hN C hC).1 (hf N hN C hC).2;rw [← htr] at hgf; exact (qa.mp hgf).1
       · rcases h6 N hN g' hg' with ⟨u,v,hu,hv,_,hj,rfl,hru,hrv⟩
         have h01:({u,v}:Q3 n).image (qr F)={qr F u,qr F v}:=by ext C; simp
         rw [h01,(h4 (fun C hC=>getRoot N C hC) h0o hu hv hj).1,hru,hrv];exact (qa.mp hg').1
     · intro hgN;by_cases hex:∃ R∈F,g⊆R
       · left;rcases hex with ⟨R,hRF,hgR⟩
         obtain ⟨u,huR⟩:R.Nonempty:=qU.mp (by rw [h3 R hRF]; omega);have hCp:qr F u∈vC U F:=qN.mpr ⟨u,hFU R hRF huR,rfl⟩
         have hRC:R∈F.filter (fun R'=>R'⊆qr F u):=qa.mpr ⟨hRF,y2 F hRF huR⟩
         have h0p:g∈Nint N (qr F u):=qa.mpr ⟨hgN,R,hRC,hgR⟩;rcases h9 _ hCp with hT|hC
         · right;have htr:=(h7 N hN).2.2 _ hT (getRoot N _ hT) (hf N hN _ hT).1 (hf N hN _ hT).2;exact ⟨qr F u,hT,htr▸h0p⟩
         · left; exact ⟨qr F u,hC,h0p⟩
       · right;have h13:g∈Nextra N:=qa.mpr ⟨hgN,hex⟩;rcases h6 N hN g h13 with ⟨u,v,hu,hv,_,hj,hV,hru,hrv⟩
         refine ⟨g.image (qr F),⟨g,h13,rfl⟩,?_⟩
         have h01:g.image (qr F)={qr F u,qr F v}:=by rw [hV]; ext C; simp
         rw [h01,(h4 (fun C hC=>getRoot N C hC) h0o hu hv hj).1,hru,hrv,← hV]
   · rintro ⟨⟨fc,r⟩,Q⟩ hz;simp only [zQ,Finset.mem_product,P_cyc,P_tr,P_m,Finset.mem_pi,id_eq,zr,qa,v7] at hz;rcases hz with ⟨⟨hfc,hr⟩,hQsub,hQdisj,hQcard⟩
     set N:=fromTriple ((fc,r),Q)
     have hF:∀ e∈Q,∀ R∈F,¬ pairOf r e⊆R:=by
      intro e heQ R hRF h00;have hep:=zD.mp (hQsub heQ);rcases yk.mp hep.2 with ⟨C₁,C₂,hj,rfl⟩
      have h1:C₁∈Tr:=hep.1 (by simp); have h2:C₂∈Tr:=hep.1 (by simp);rw [(h4 r hr h1 h2 hj).1] at h00;have hR1:r C₁ h1∈R:=h00 (by simp);have hR2:r C₂ h2∈R:=h00 (by simp)
      have hH:qr F (r C₁ h1)=qr F (r C₂ h2):=(vG F (y2 F hRF hR1 hR2)).symm
      rw [h0 C₁ (qa.mp h1).1 _ (hr C₁ h1),h0 C₂ (qa.mp h2).1 _ (hr C₂ h2)] at hH;exact hj hH
     have h07:∀ C (hC:C∈Cyc),Nint N C=fc C hC:=by
      intro C hC;ext g; simp only [Nint,qa,N,fromTriple,ql,qj,Finset.mem_attach,true_and,Subtype.exists,qN];constructor
      · rintro ⟨((⟨C',hC',hgf⟩|⟨C',hC',hgf⟩)|⟨e,heQ,rfl⟩),⟨R,⟨hRF,hRC⟩,hgR⟩⟩
        · by_cases heq:C'=C
          · subst heq; exact hgf
          · exfalso;have h1:=(qa.mp (hfc C' hC')).2.1 g hgf;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega);exact qc.mp (qu U F (qa.mp hC').1 (qa.mp hC).1 heq) (h1.2 hu) (hRC (hgR hu))
        · exfalso;have h1:=(qa.mp (h5 C' hC' (r C' hC') (hr C' hC'))).2.1 g hgf;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega);have hne:C'≠C:=fun e=>qc.mp hk hC' (e▸hC)
          exact qc.mp (qu U F (qa.mp hC').1 (qa.mp hC).1 hne) (qE (h1.2 hu)) (hRC (hgR hu))
        · exact absurd hgR (hF e heQ R hRF)
      · intro hgf
        have ht:=vA (fun R hR=>h3 R (qa.mp hR).1) (hl C)
         (qa.mp hC).2 (hfc C hC)
        rcases ht.2.2 g hgf with ⟨R,hRC,hgR⟩
        exact ⟨Or.inl (Or.inl ⟨C,hC,hgf⟩),R,qa.mp hRC,hgR⟩
     have h0h:∀ C (hC:C∈Tr),Nint N C=treeM C (r C hC):=by
      intro C hC;ext g; simp only [Nint,qa,N,fromTriple,ql,qj,Finset.mem_attach,true_and,Subtype.exists,qN];constructor
      · rintro ⟨((⟨C',hC',hgf⟩|⟨C',hC',hgf⟩)|⟨e,heQ,rfl⟩),⟨R,⟨hRF,hRC⟩,hgR⟩⟩
        · exfalso;have h1:=(qa.mp (hfc C' hC')).2.1 g hgf;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega);have hne:C'≠C:=fun e=>qc.mp hk hC (e▸hC')
          exact qc.mp (qu U F (qa.mp hC').1 (qa.mp hC).1 hne) (h1.2 hu) (hRC (hgR hu))
        · by_cases heq:C'=C
          · subst heq; exact hgf
          · exfalso;have h1:=(qa.mp (h5 C' hC' (r C' hC') (hr C' hC'))).2.1 g hgf;obtain ⟨u,hu⟩:g.Nonempty:=qU.mp (by omega);exact qc.mp (qu U F (qa.mp hC').1 (qa.mp hC).1 heq) (qE (h1.2 hu)) (hRC (hgR hu))
        · exact absurd hgR (hF e heQ R hRF)
      · intro hgf
        have ht:=yg (fun R hR=>h3 R (qa.mp hR).1) (hl C)
         (hr C hC) (qa.mp hC).2 (h5 C hC (r C hC) (hr C hC))
        rcases ht.2.2 g hgf with ⟨R,hRC,hgR⟩
        exact ⟨Or.inl (Or.inr ⟨C,hC,hgf⟩),R,qa.mp hRC,hgR⟩
     have h04:Nextra N=Q.image (pairOf r):=by
      ext g; simp only [Nextra,qa,N,fromTriple,ql,qj,Finset.mem_attach,true_and,Subtype.exists,qN];constructor
      · rintro ⟨((⟨C,hC,hgf⟩|⟨C,hC,hgf⟩)|⟨e,heQ,rfl⟩),hnoR⟩
        · exfalso
          have ht:=vA (fun R hR=>h3 R (qa.mp hR).1) (hl C)
           (qa.mp hC).2 (hfc C hC)
          rcases ht.2.2 g hgf with ⟨R,hRC,hgR⟩
          exact hnoR ⟨R,(qa.mp hRC).1,hgR⟩
        · exfalso
          have ht:=yg (fun R hR=>h3 R (qa.mp hR).1) (hl C)
           (hr C hC) (qa.mp hC).2 (h5 C hC (r C hC) (hr C hC))
          rcases ht.2.2 g hgf with ⟨R,hRC,hgR⟩
          exact hnoR ⟨R,(qa.mp hRC).1,hgR⟩
        · exact ⟨e,heQ,rfl⟩
      · rintro ⟨e,heQ,rfl⟩;exact ⟨Or.inr ⟨e,heQ,rfl⟩,fun ⟨R,hRF,h00⟩=>hF e heQ R hRF h00⟩
     ext1
     · ext1
       · funext C hC; exact h07 C hC
       · funext C hC
         have hbi:=(yg (fun R hR=>h3 R (qa.mp hR).1) (hl C)
          (hr C hC) (qa.mp hC).2 (h5 C hC (r C hC) (hr C hC))).2.1
         have hP:C \ (Nint N C).biUnion id={r C hC}:=by
          rw [h0h C hC,hbi]; ext u;simp only [qg,qh,qd];constructor
          · rintro ⟨huC,h0t⟩; by_contra hne; exact h0t ⟨hne,huC⟩
          · rintro rfl; exact ⟨hr C hC,fun h=>h.1 rfl⟩
         have hne:(C \ (Nint N C).biUnion id).Nonempty:=⟨r C hC,by rw [hP]; simp⟩;change (if h:(C \ (Nint N C).biUnion id).Nonempty then h.choose else _)=r C hC;rw [dif_pos hne];set x:=hne.choose;have hm:x∈C \ (Nint N C).biUnion id:=hne.choose_spec;rw [hP,qd] at hm;exact hm
     · simp only [toQ,h04,Finset.image_image];ext e; simp only [qN,Function.comp_apply];constructor
       · rintro ⟨e',h1i,rfl⟩;have hep:=zD.mp (hQsub h1i);rcases yk.mp hep.2 with ⟨C₁,C₂,hj,rfl⟩
         have h1:C₁∈Tr:=hep.1 (by simp); have h2:C₂∈Tr:=hep.1 (by simp);rw [(h4 r hr h1 h2 hj).1]
         have h01:({r C₁ h1,r C₂ h2}:Q3 n).image (qr F)={C₁,C₂}:=by
          ext C; simp only [qN,qe,qd];constructor
          · rintro ⟨u,rfl|rfl,rfl⟩
            · exact Or.inl (h0 C₁ (qa.mp h1).1 _ (hr C₁ h1))
            · exact Or.inr (h0 C₂ (qa.mp h2).1 _ (hr C₂ h2))
          · rintro (hH|hH)
            · exact ⟨r C₁ h1,Or.inl rfl,hH▸h0 C₁ (qa.mp h1).1 _ (hr C₁ h1)⟩
            · exact ⟨r C₂ h2,Or.inr rfl,hH▸h0 C₂ (qa.mp h2).1 _ (hr C₂ h2)⟩
         rwa [h01]
       · intro heQ;have hep:=zD.mp (hQsub heQ);rcases yk.mp hep.2 with ⟨C₁,C₂,hj,hW⟩
         have h1:C₁∈Tr:=hep.1 (hW▸by simp); have h2:C₂∈Tr:=hep.1 (hW▸by simp);refine ⟨e,heQ,?_⟩
         rw [hW,(h4 r hr h1 h2 hj).1];ext C; simp only [qN,qe,qd];constructor
         · rintro ⟨u,rfl|rfl,rfl⟩
           · exact Or.inl (h0 C₁ (qa.mp h1).1 _ (hr C₁ h1))
           · exact Or.inr (h0 C₂ (qa.mp h2).1 _ (hr C₂ h2))
         · rintro (hH|hH)
           · exact ⟨r C₁ h1,Or.inl rfl,hH▸h0 C₁ (qa.mp h1).1 _ (hr C₁ h1)⟩
           · exact ⟨r C₂ h2,Or.inr rfl,hH▸h0 C₂ (qa.mp h2).1 _ (hr C₂ h2)⟩
end jC
namespace Alg
open PEqualNP.Library Lib.qC Lib.ve Lib.j4 Lib.R
lemma je {p:Q0→Q0} {a:Q0→ℕ} (hp:Lib.qF p) (ha:qi a):
 qi (fun s=>a (p s)):=by
 unfold qi at *; exact qG (f:=p) (g:=fun s=>un (a s)) hp ha
lemma k1 {p:Q0→Q0} {v:Q0→Q1} (hp:Lib.qF p) (hv:qS v):
 qS (fun s=>v (p s)):=by
 unfold qS at *; exact qG (f:=p) (g:=fun s=>zn (v s)) hp hv
lemma qdo {p:Q0→Q0} {S:Q0→Q2} (hp:Lib.qF p) (hS:LLR S):
 LLR (fun s=>S (p s)):=by
 unfold LLR at *; exact qG (f:=p) (g:=fun s=>zR (S s)) hp hS
lemma k9 {α:Type} (p:α→Bool) (l:List α):(l.takeWhile p).length≤l.length:=by
 induction l with
 | nil=>simp
 | cons a l ih=>simp only [List.takeWhile_cons]; split_ifs <;> simp <;> omega
abbrev g (v:Q1) (i:ℕ):ℕ:=v.getD i 0
abbrev gg (S:Q2) (i:ℕ):Q1:=S.getD i []
lemma qbH (n i:ℕ) (f:ℕ→ℕ) (hi:i<n):
 g ((List.range n).map f) i=f i:=by
 simp [g,qf,hi]
lemma yK (n i:ℕ) (f:ℕ→Q1) (hi:i<n):
 gg ((List.range n).map f) i=f i:=by
 simp [gg,qf,hi]
def qV:Q1→ℕ
 | []=>0
 | b::bs=>b+2 * qV bs
lemma kP (u v:Q1):qV (u++v)=qV u+2 ^ u.length * qV v:=by
 induction u with
 | nil=>simp [qV]
 | cons b u ih=>simp only [List.cons_append,qV,qI,ih,pow_succ];ring
lemma wS (u:Q1) (hu:∀ b∈u,b≤1):qV u<2 ^ u.length:=by
 induction u with
 | nil=>simp [qV]
 | cons b u ih=>simp only [qV,qI,pow_succ];have hb:b≤1:=hu b (by simp);have hu':=ih (fun x hx=>hu x (by simp [hx]));omega
lemma yF (u:Q1) (k:ℕ):
 qV (u.take (k+1))=qV (u.take k)+2 ^ k * g u k:=by
 by_cases hk:k<u.length
 · have h1:u.take (k+1)=u.take k++[u[k]]:=List.take_succ_eq_append_getElem hk;rw [h1,kP,List.length_take_of_le (by omega),qV,qV];have hg:g u k=u[k]:=by simp [g,qf,hk]
   rw [hg]; ring
 · have hle:u.length≤k:=yt hk;rw [vo (by omega),vo hle];have hg:g u k=0:=by simp [g,qf,List.getElem?_eq_none hle]
   rw [hg]; simp
def qA (t a:ℕ):Q1:=(List.range t).map (fun i=>if a.testBit i then 1 else 0)
lemma zl (t a:ℕ):(qA t a).length=t:=by simp [qA]
lemma zS (t a:ℕ):∀ b∈qA t a,b≤1:=by intro b hb; simp only [qA,qQ] at hb;rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
lemma vz (t a:ℕ):qV (qA t a)=a % 2 ^ t:=by
 induction t with
 | zero=>simp [qA,qV,Nat.mod_one]
 | succ t ih=>rw [qA,zP,List.map_append,List.map_singleton,kP,zM,List.length_range,← qA,ih,qV,qV,mul_zero,add_zero];rw [Nat.testBit_eq_decide_div_mod_eq,Nat.mod_pow_succ];rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ t) with h|h <;> simp [h] <;> ring
lemma ym {t a:Q0→ℕ} (ht:qi t) (ha:qi a):
 qS (fun s=>qA (t s) (a s)):=
 u1 (A:=fun s=>un (a s)) (G:=fun i y=>if y.length.testBit i then 1 else 0)
  ha ht (qbu (yY zA) qs) |> fun h=>
  zk h (fun s=>by simp [qA,za])
def ke (t k:ℕ) (u:Q1):Q1:=(List.range t).map (fun i=>if i<k then 0 else g u (i-k))
lemma wM (t k:ℕ) (u:Q1):(ke t k u).length=t:=by simp [ke]
lemma qbx (t k:ℕ) (u:Q1) (hu:∀ b∈u,b≤1):∀ b∈ke t k u,b≤1:=by
 intro b hb; simp only [ke,qQ] at hb;rcases hb with ⟨i,_,rfl⟩; split_ifs
 · omega
 · by_cases hi:i-k<u.length
   · have:g u (i-k)=u[i-k]:=by simp [g,qf,hi]
     rw [this]; exact hu _ (qn hi)
   · have:g u (i-k)=0:=by
      simp [g,qf,List.getElem?_eq_none (yt hi)]
     omega
lemma qaJ (t k:ℕ) (u:Q1) (hlen:u.length=t) (hu:∀ b∈u,b≤1):
 qV (ke t k u)=(2 ^ k * qV u) % 2 ^ t:=by
 have h6:∀ m,m≤t→qV ((List.range m).map (fun i=>if i<k then 0 else g u (i-k)))=
  if m≤k then 0 else 2 ^ k * qV (u.take (m-k)):=by
  intro m; induction m with
  | zero=>intro _; simp [qV]
  | succ m ih=>
    intro hm
    rw [zP,List.map_append,List.map_singleton,kP,
     zM,List.length_range,ih (by omega),qV,qV,mul_zero,add_zero]
    by_cases hmk:m<k
    · simp [hmk,show m≤k by omega,show m+1≤k by omega]
    · by_cases h5:m=k
      · subst h5;simp only [lt_irrefl,↓reduceIte,le_refl,show ¬ m+1≤ m by omega,Nat.add_sub_cancel_left,Nat.sub_self];have h1:=yF u 0;simp only [List.take_zero,qV,zero_add,pow_zero,one_mul] at h1;rw [h1]; ring
      · simp only [hmk,show ¬ m≤k by omega,show ¬ m+1≤k by omega,↓reduceIte];have h3:m+1-k=(m-k)+1:=by omega
        rw [h3,yF,mul_add,← mul_assoc,← pow_add,Nat.add_sub_of_le (by omega)]
 have h1:=h6 t le_rfl;change qV (ke t k u)=_;rw [ke,h1];split_ifs with htk
 · symm; exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 htk) _)
 · have h0:u=u.take (t-k)++u.drop (t-k):=(List.take_append_drop (t-k) u).symm
   have h2:qV u=qV (u.take (t-k))+2 ^ (t-k) * qV (u.drop (t-k)):=by
    conv_lhs=>rw [h0]
    rw [kP,List.length_take_of_le (by omega)]
   have h4:2 ^ k * qV u=2 ^ k * qV (u.take (t-k))+2 ^ t * qV (u.drop (t-k)):=by rw [h2,mul_add,← mul_assoc,← pow_add,Nat.add_sub_of_le (by omega)]
   have hlt:2 ^ k * qV (u.take (t-k))<2 ^ t:=by
    have hv:qV (u.take (t-k))<2 ^ (u.take (t-k)).length:=wS _ (fun b hb=>hu b (List.mem_of_mem_take hb))
    rw [List.length_take_of_le (by omega)] at hv
    calc 2 ^ k * qV (u.take (t-k))<2 ^ k * 2 ^ (t-k):=Nat.mul_lt_mul_of_pos_left hv (by positivity)
     _=2 ^ t:=by rw [← pow_add,Nat.add_sub_of_le (by omega)]
   rw [h4,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlt]
lemma qaK {t k:Q0→ℕ} {u:Q0→Q1}
 (ht:qi t) (hk:qi k) (hu:qS u):
 qS (fun s=>ke (t s) (k s) (u s)):=
 u1 (A:=id) (G:=fun i s=>if i<k s then 0 else g (u s) (i-k s)) yP ht
  (kz qs (qz hk) (qb 0) (qO (k1 zA hu) (yj qs (qz hk))))
def vN (u v:Q1) (st:ℕ×Q1):ℕ×Q1:=
 let i:=st.2.length
 let s:=g u i+g v i+st.1
 (s / 2,st.2++[s % 2])
def kI (t:ℕ) (u v:Q1):Q1:=((vN u v)^[t] (0,[])).2
lemma qa5 (u v:Q1) (hu:∀ b∈u,b≤1) (hv:∀ b∈v,b≤1):
 ∀ k,let p:=(vN u v)^[k] (0,[])
   p.2.length=k∧p.1≤1∧(∀ b∈p.2,b≤1)∧
   qV p.2+2 ^ k * p.1=qV (u.take k)+qV (v.take k):=by
 intro k; induction k with
 | zero=>simp [qV]
 | succ k ih=>
   rcases ih with ⟨h0,hc,hb,h2⟩
   rw [qM];dsimp only [vN];set p:=(vN u v)^[k] (0,[])
   have hgu:g u p.2.length≤1:=by
    by_cases hi:p.2.length<u.length
    · have:g u p.2.length=u[p.2.length]:=by simp [g,qf,hi]
      rw [this]; exact hu _ (qn hi)
    · have:g u p.2.length=0:=by
       simp [g,qf,List.getElem?_eq_none (yt hi)]
      omega
   have hgv:g v p.2.length≤1:=by
    by_cases hi:p.2.length<v.length
    · have:g v p.2.length=v[p.2.length]:=by simp [g,qf,hi]
      rw [this]; exact hv _ (qn hi)
    · have:g v p.2.length=0:=by
       simp [g,qf,List.getElem?_eq_none (yt hi)]
      omega
   refine ⟨by simp [h0],by omega,?_,?_⟩
   · intro b hbm; simp only [List.mem_append,z4] at hbm;rcases hbm with h1|rfl; exact hb b h1; omega
   · rw [kP,h0,qV,qV,mul_zero,add_zero,yF,yF,pow_succ];have hdm:(g u k+g v k+p.1) % 2+2 * ((g u k+g v k+p.1) / 2)=g u k+g v k+p.1:=by omega
     calc qV p.2+2 ^ k * ((g u k+g v k+p.1) % 2)+2 ^ k * 2 * ((g u k+g v k+p.1) / 2)=qV p.2+2 ^ k * ((g u k+g v k+p.1) % 2+2 * ((g u k+g v k+p.1) / 2)):=by ring
      _=qV p.2+2 ^ k * (g u k+g v k+p.1):=by rw [hdm]
      _=(qV p.2+2 ^ k * p.1)+2 ^ k * g u k+2 ^ k * g v k:=by ring
      _=(qV (u.take k)+qV (v.take k))+2 ^ k * g u k+2 ^ k * g v k:=by rw [h2]
      _=(qV (u.take k)+2 ^ k * g u k)+(qV (v.take k)+2 ^ k * g v k):=by ring
lemma j5 (t:ℕ) (u v:Q1) (hul:u.length=t) (hvl:v.length=t)
 (hu:∀ b∈u,b≤1) (hv:∀ b∈v,b≤1):
 (kI t u v).length=t∧(∀ b∈kI t u v,b≤1)∧
 qV (kI t u v)=(qV u+qV v) % 2 ^ t:=by
 unfold kI;rcases qa5 u v hu hv t with ⟨h1,_,hb,h0⟩
 rw [vo (by omega),vo (by omega)] at h0;refine ⟨h1,hb,?_⟩
 have hlt:qV ((vN u v)^[t] (0,[])).2<2 ^ t:=by simpa only [h1] using wS ((vN u v)^[t] (0,[])).2 hb
 rw [← h0,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlt]
lemma kn (u v:Q1) (k:ℕ):
 let p:=(vN u v)^[k] (0,[])
 p.2.length=k∧(∀ b∈p.2,b≤1)∧p.1≤u.sum+v.sum:=by
 induction k with
 | zero=>simp
 | succ k ih=>
   rcases ih with ⟨h0,hb,hc⟩
   rw [qM];dsimp only [vN];set p:=(vN u v)^[k] (0,[])
   have hgu:g u p.2.length≤u.sum:=by
    by_cases hi:p.2.length<u.length
    · have:g u p.2.length=u[p.2.length]:=by simp [g,qf,hi]
      rw [this]; exact List.le_sum_of_mem (qn hi)
    · have:g u p.2.length=0:=by
       simp [g,qf,List.getElem?_eq_none (yt hi)]
      omega
   have hgv:g v p.2.length≤v.sum:=by
    by_cases hi:p.2.length<v.length
    · have:g v p.2.length=v[p.2.length]:=by simp [g,qf,hi]
      rw [this]; exact List.le_sum_of_mem (qn hi)
    · have:g v p.2.length=0:=by
       simp [g,qf,List.getElem?_eq_none (yt hi)]
      omega
   refine ⟨by simp [h0],?_,by omega⟩
   intro b hbm; simp only [List.mem_append,z4] at hbm;rcases hbm with h1|rfl; exact hb b h1; omega
lemma wj {t:Q0→ℕ} {u v:Q0→Q1}
 (ht:qi t) (hu:qS u) (hv:qS v):
 qS (fun s=>kI (t s) (u s) (v s)):=by
 obtain ⟨Pt,hPt⟩:=z8 ht;obtain ⟨Pu,hPu⟩:=z8 (zJ hu);obtain ⟨Pv,hPv⟩:=z8 (zJ hv)
 let F:Q0→Q0:=fun z=>
  let st:=(Q9 z).1;let s:=(Q9 z).2;let c:=(Q9 st).1.length;let out:=vK (Q9 st).2;let sum:=g (u s) out.length+g (v s) out.length+c
  qv (un (sum / 2)) (zn (out++[sum % 2]))
 have hF:Lib.qF F:=by
  have hst:=zz;have hs:=zA;have hc:qi (fun z=>(Q9 (Q9 z).1).1.length):=yY (qZ hst);have h4:qS (fun z=>vK (Q9 (Q9 z).1).2):=vv (qo hst);have hi:qi (fun z=>(vK (Q9 (Q9 z).1).2).length):=vg h4
  have h0:qi (fun z=>g (u (Q9 z).2) (vK (Q9 (Q9 z).1).2).length +
   g (v (Q9 z).2) (vK (Q9 (Q9 z).1).2).length +
   (Q9 (Q9 z).1).1.length):=
   q9 (q9 (qO (k1 hs hu) hi) (qO (k1 hs hv) hi)) hc
  exact qy (uo h0 (qb 2))
   (zI h4 (qT (qbt h0 (qb 2))))
 have heq:∀ s k,(fun a=>F (qv a s))^[k] (qv (un 0) (zn []))=
  qv (un ((vN (u s) (v s))^[k] (0,[])).1)
   (zn ((vN (u s) (v s))^[k] (0,[])).2):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih];simp only [F,vN,qk,za,zU]
 let PB:Q5:=Polynomial.C 2 * (Pu+Pv)+Polynomial.C 2 * Pt+Polynomial.C 5
 have h5:=y6 hF (yp (qv (un 0) (zn []))) ht PB (fun s i hi=>by
  rw [heq s i,zW,za,vy];rcases kn (u s) (v s) i with ⟨hlen,hb,hc⟩
  have hsum_le:((vN (u s) (v s))^[i] (0,[])).2.sum≤ i:=by
   have:((vN (u s) (v s))^[i] (0,[])).2.sum≤((vN (u s) (v s))^[i] (0,[])).2.length * 1:=by simpa only [smul_eq_mul,mul_one] using List.sum_le_length_nsmul _ 1 hb
   omega
  have h1:=hPt s; have h2:=hPu s; have h3:=hPv s;have hi':i≤t s:=by simpa [za] using hi
  simp only [PB,zO,z9,vT];omega)
 exact zk (vv (qo h5)) (fun s=>by dsimp only; rw [za,heq,qk,zU]; rfl)
def yL (t:ℕ) (u v:Q1) (st:ℕ×Q1):ℕ×Q1:=
 let acc':=if g v st.1=0 then st.2 else kI t st.2 (ke t st.1 u)
 (st.1+1,acc')
def kK (t:ℕ) (u v:Q1):Q1:=((yL t u v)^[t] (0,qA t 0)).2
lemma qbq (t:ℕ) (u v:Q1) (hul:u.length=t)
 (hu:∀ b∈u,b≤1) (hv:∀ b∈v,b≤1):
 ∀ k,let p:=(yL t u v)^[k] (0,qA t 0)
   p.1=k∧p.2.length=t∧(∀ b∈p.2,b≤1)∧
   qV p.2=(qV u * qV (v.take k)) % 2 ^ t:=by
 intro k; induction k with
 | zero=>
   refine ⟨rfl,zl t 0,zS t 0,?_⟩
   simp only [Function.iterate_zero_apply];rw [vz]; simp [qV]
 | succ k ih=>
   rcases ih with ⟨hi,h4,hb,h3⟩
   rw [qM];dsimp only [yL];set p:=(yL t u v)^[k] (0,qA t 0)
   have hgv:g v k≤1:=by
    by_cases hk:k<v.length
    · have:g v k=v[k]:=by simp [g,qf,hk]
      rw [this]; exact hv _ (qn hk)
    · have:g v k=0:=by
       simp [g,qf,List.getElem?_eq_none (yt hk)]
      omega
   rw [hi];split_ifs with h0
   · refine ⟨rfl,h4,hb,?_⟩
     rw [h3,yF,h0]; simp
   · have h1:g v k=1:=by omega
     have h2:=j5 t p.2 (ke t k u) h4 (wM t k u) hb (qbx t k u hu);refine ⟨rfl,h2.1,h2.2.1,?_⟩
     rw [h2.2.2,h3,qaJ t k u hul hu,yF,h1,mul_one,mul_add];rw [Nat.add_mod,Nat.mod_mod,Nat.mod_mod,← Nat.add_mod];congr 1; ring
lemma wb (t:ℕ) (u v:Q1) (hul:u.length=t) (hvl:v.length=t)
 (hu:∀ b∈u,b≤1) (hv:∀ b∈v,b≤1):
 (kK t u v).length=t∧(∀ b∈kK t u v,b≤1)∧
 qV (kK t u v)=(qV u * qV v) % 2 ^ t:=by
 rcases qbq t u v hul hu hv t with ⟨_,h1,hb,h0⟩
 rw [vo (by omega)] at h0;exact ⟨h1,hb,h0⟩
lemma jd (t:ℕ) (u v:Q1) (k:ℕ):
 let p:=(yL t u v)^[k] (0,qA t 0)
 p.1=k∧p.2.length=t∧(∀ b∈p.2,b≤1):=by
 induction k with
 | zero=>exact ⟨rfl,zl t 0,zS t 0⟩
 | succ k ih=>
   rcases ih with ⟨hi,h0,hb⟩
   rw [qM];dsimp only [yL];split_ifs
   · exact ⟨by omega,h0,hb⟩
   · rcases kn ((yL t u v)^[k] (0,qA t 0)).2 (ke t _ u) t with ⟨hl2,hb2,_⟩
     exact ⟨by omega,hl2,hb2⟩
lemma wk {t:Q0→ℕ} {u v:Q0→Q1}
 (ht:qi t) (hu:qS u) (hv:qS v):
 qS (fun s=>kK (t s) (u s) (v s)):=by
 obtain ⟨Pt,hPt⟩:=z8 ht
 let F:Q0→Q0:=fun z=>
  let st:=(Q9 z).1;let s:=(Q9 z).2;let i:=(Q9 st).1.length;let acc:=vK (Q9 st).2;let acc':=if g (v s) i=0 then acc else kI (t s) acc (ke (t s) i (u s))
  qv (un (i+1)) (zn acc')
 have hF:Lib.qF F:=by
  have hst:=zz;have hs:=zA;have hi:qi (fun z=>(Q9 (Q9 z).1).1.length):=yY (qZ hst);have h0:qS (fun z=>vK (Q9 (Q9 z).1).2):=vv (qo hst);have hts:qi (fun z=>t (Q9 z).2):=qz ht;have hus:qS (fun z=>u (Q9 z).2):=k1 hs hu;have hvs:qS (fun z=>v (Q9 z).2):=k1 hs hv
  have h0':qS (fun z=>if g (v (Q9 z).2) (Q9 (Q9 z).1).1.length=0
   then vK (Q9 (Q9 z).1).2
   else kI (t (Q9 z).2) (vK (Q9 (Q9 z).1).2)
    (ke (t (Q9 z).2) (Q9 (Q9 z).1).1.length (u (Q9 z).2))):=
   zk (yQ (qO hvs hi) (qb 0) h0 (wj hts h0 (qaK hts hi hus)))
    (fun z=>by dsimp only; split_ifs <;> rfl)
  exact qy (q9 hi (qb 1)) h0'
 have heq:∀ s k,(fun a=>F (qv a s))^[k] (qv (un 0) (zn (qA (t s) 0)))=
  qv (un ((yL (t s) (u s) (v s))^[k] (0,qA (t s) 0)).1)
   (zn ((yL (t s) (u s) (v s))^[k] (0,qA (t s) 0)).2):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih];simp only [F,yL,qk,za,zU]
 let PB:Q5:=Polynomial.C 4 * Pt+Polynomial.C 5
 have h2:=y6 hF (qy (qb 0) (ym ht (qb 0))) ht PB
  (fun s i hi=>by
    rw [heq s i,zW,za,vy];rcases jd (t s) (u s) (v s) i with ⟨hi1,hlen,hb⟩
    have hsum:((yL (t s) (u s) (v s))^[i] (0,qA (t s) 0)).2.sum≤t s:=by have hle:=List.sum_le_length_nsmul _ 1 hb;simp only [smul_eq_mul,mul_one] at hle;omega
    have h1:=hPt s;have hi':i≤t s:=by simpa [za] using hi
    simp only [PB,zO,z9,vT];omega)
 exact zk (vv (qo h2)) (fun s=>by dsimp only; rw [za,heq,qk,zU]; rfl)
lemma qah (t x:ℕ) (v:Q1) (hl:v.length=t) (hb:∀ b∈v,b≤1)
 (hval:qV v=x % 2 ^ t):
 v.map (fun a=>decide (a≠0))=(List.range t).map (fun i=>x.testBit i):=by
 have h2:v=qA t x:=by
  apply List.ext_getElem (by rw [hl,zl]);intro i hi1 hi2;have hit:i<t:=by omega
  have h0:(qV v).testBit i=(v[i] == 1):=by
   clear hval hl hi2 hit x t;induction v generalizing i with
   | nil=>simp at hi1
   | cons b vs ih=>
     have hb0:b≤1:=hb b (by simp)
     cases i with
     | zero=>
       simp only [qV,Nat.testBit_zero,List.getElem_cons_zero];have h1:(b+2 * qV vs) % 2=b % 2:=by omega
       rw [h1];rcases (by omega:b=0∨b=1) with rfl|rfl <;> decide
     | succ i=>
       simp only [qV,Nat.testBit_succ,List.getElem_cons_succ];have h3:(b+2 * qV vs) / 2=qV vs:=by omega
       rw [h3];exact ih (fun y hy=>hb y (by simp [hy])) i (by simpa using hi1)
  have hxt:x.testBit i=(x % 2 ^ t).testBit i:=by rw [Nat.testBit_mod_two_pow,decide_eq_true hit,Bool.true_and]
  simp only [qA,List.getElem_map,List.getElem_range];rw [hxt,← hval,h0];have hvi:v[i]≤1:=hb _ (qn hi1);rcases (by omega:v[i]=0∨v[i]=1) with h|h <;> simp [h]
 rw [h2,qA,List.map_map];refine List.map_congr_left fun i _=>?_
 dsimp only [Function.comp_apply]
 cases x.testBit i <;> decide
def parseN (x:Q0):ℕ:=(x.takeWhile id).length
def parseT (x:Q0):ℕ:=((x.drop (parseN x+1)).takeWhile id).length
def offH (x:Q0):ℕ:=parseN x+1+parseT x+1
def wBit (x:Q0):ℕ:=(parseN x).log2+1
def numTr (x:Q0):ℕ:=(x.length-offH x) / (3 * wBit x)
def wm (x:Q0) (k:ℕ):ℕ:=if x.getD k false then 1 else 0
def uq (x:Q0) (pos w:ℕ):ℕ:=((List.range w).map (fun i=>wm x (pos+i) * 2 ^ i)).sum
def rawH (x:Q0):Q2:=
 (List.range (numTr x)).map (fun r=>(List.range 3).map (fun j=>uq x (offH x+(3 * r+j) * wBit x) (wBit x)))
def inR (R:Q1) (a:ℕ):ℕ:=if ((List.range 3).map (fun j=>if g R j=a then 1 else 0)).sum=0 then 0 else 1
def qdH (x:Q0) (u v w:ℕ):ℕ:=
 if ((List.range (rawH x).length).map (fun r=>inR (gg (rawH x) r) u * inR (gg (rawH x) r) v * inR (gg (rawH x) r) w)).sum=0
 then 0 else 1
lemma kM:qi parseN:=zk (qac yP (qb 0)) (fun s=>by simp [parseN])
lemma wL:qi parseT:=qac yP (q9 kM (qb 1))
lemma qaH:qi offH:=q9 (q9 (q9 kM (qb 1)) wL) (qb 1)
lemma we:qi wBit:=q9 (qaG kM) (qb 1)
lemma qco:qi numTr:=uo (yj (yY yP) qaH) (vn (qb 3) we)
lemma jA (n i:ℕ) (hi:i≤n.log2):2 ^ i≤n+1:=by
 rcases Nat.eq_zero_or_pos n with rfl|hpos
 · simp at hi; subst hi; simp
 · have h1:2 ^ i≤2 ^ n.log2:=Nat.pow_le_pow_right (by norm_num) hi;have h2:2 ^ n.log2≤n:=Nat.log2_self_le hpos.ne';omega
lemma qdq:LLR rawH:=by
 have h0:∀ {pos:Q0→ℕ} {x:Q0→Q0},
  Lib.qF x→qi pos→qi (fun s=>uq (x s) (pos s) (wBit (x s))):=by
  intro pos x hx hpos
  have hG:qi (fun y=>
   wm (x (Q9 y).2) (pos (Q9 y).2+(Q9 y).1.length) *
   2 ^ (min (Q9 y).1.length (parseN (x (Q9 y).2)).log2)):=by
   have hx2:=qG zA hx;have h1:=qz hpos;have h2:=qaG (je hx2 kM)
   have h6:qi (fun y=>if (Q9 y).1.length<(parseN (x (Q9 y).2)).log2
    then (Q9 y).1.length else (parseN (x (Q9 y).2)).log2):=
    kz qs h2 qs h2
   obtain ⟨Px,hPx⟩:=yV _ hx2
   have h5:qi (fun y=>2 ^ (if (Q9 y).1.length<(parseN (x (Q9 y).2)).log2
    then (Q9 y).1.length else (parseN (x (Q9 y).2)).log2)):=
    qcZ h6 (Px+Polynomial.C 1) (fun y=>by
     have h7:(if (Q9 y).1.length<(parseN (x (Q9 y).2)).log2
      then (Q9 y).1.length else (parseN (x (Q9 y).2)).log2)≤
      (parseN (x (Q9 y).2)).log2:=by split_ifs <;> omega
     have hle2:=jA _ _ h7
     have hlen1:parseN (x (Q9 y).2)≤(x (Q9 y).2).length:=k9 _ _
     have hlen2:=hPx y;simp only [zO,vT]; omega)
   exact zk (vn (qdt hx2 (q9 h1 qs)) h5) (fun y=>by dsimp only [wm]; congr 1; split_ifs <;> simp [Nat.min_def, *] <;> omega)
  have h3:=u1 (A:=id)
   (G:=fun i s=>wm (x s) (pos s+i) * 2 ^ (min i (parseN (x s)).log2))
   yP (je hx we) hG
  exact zk (zJ h3) (fun s=>by
   dsimp only [id_eq,uq]; congr 2;refine List.map_congr_left fun i hi=>?_
   have h8:i<wBit (x s):=qw.mp hi;have h9:i≤(parseN (x s)).log2:=by unfold wBit at h8; omega
   rw [Nat.min_eq_left h9])
 have h4:qS (fun t=>(List.range 3).map (fun j=>
  uq (Q9 t).2 (offH (Q9 t).2+(3 * (Q9 t).1.length+j) * wBit (Q9 t).2)
   (wBit (Q9 t).2))):=
  u1 (A:=id)
   (G:=fun j t=>uq (Q9 t).2
     (offH (Q9 t).2+(3 * (Q9 t).1.length+j) * wBit (Q9 t).2)
     (wBit (Q9 t).2))
   yP (qb 3)
   (h0 (qo zA) (q9 (je (qo zA) qaH) (vn (q9 (vn (qb 3) (yY (qZ zA))) qs) (je (qo zA) we))))
 exact qb8 (A:=id)
  (H:=fun r s=>(List.range 3).map (fun j=>uq s (offH s+(3 * r+j) * wBit s) (wBit s)))
  yP qco h4
lemma wz (n t:ℕ) (H:Q4 n)
 (hH3:∀ R∈H,R.card=3):
 let header:=fun k:Nat=>List.replicate k true++[false]
 let bits:=fun (w x:Nat)=>(List.range w).map (fun i=>x.testBit i)
 let x:=header n++header t++H.toList.flatMap
  (fun R=>R.toList.flatMap (fun u=>bits (n.log2+1) u.val))
 parseN x=n∧parseT x=t∧
 rawH x=H.toList.map (fun R=>R.toList.map Fin.val)∧
 (∀ u v w:Fin n,u≠v→u≠w→v≠w→
   (qdH x u.val v.val w.val=1↔({u,v,w}:Q3 n)∈H)):=by
 intro header bits x;set rest:=H.toList.flatMap (fun R=>R.toList.flatMap (fun u=>bits (n.log2+1) u.val))
 have he:x=List.replicate n true++false::(List.replicate t true++false::rest):=by simp [x,header,rest,List.append_assoc]
 have hN:parseN x=n:=by simp only [parseN,he];rw [List.takeWhile_append_of_pos (by simp),List.takeWhile_cons];simp
 have hx:x.drop (parseN x+1)=List.replicate t true++false::rest:=by
  rw [hN,he]
  have:List.replicate n true++false::(List.replicate t true++false::rest)=
   (List.replicate n true++[false])++(List.replicate t true++false::rest):=by
   simp [List.append_assoc]
  rw [this,List.drop_left' (by simp)]
 have hT:parseT x=t:=by simp only [parseT,hx];rw [List.takeWhile_append_of_pos (by simp),List.takeWhile_cons];simp
 have hB:offH x=n+1+t+1:=by simp [offH,hN,hT]
 have hw:wBit x=n.log2+1:=by simp [wBit,hN]
 have h6:x.drop (offH x)=rest:=by
  rw [hB,he]
  have:List.replicate n true++false::(List.replicate t true++false::rest)=
   (List.replicate n true++[false]++List.replicate t true++[false])++rest:=by
   simp [List.append_assoc]
  rw [this,List.drop_left' (by simp; omega)]
 have hl:∀ R∈H.toList,R.toList.length=3:=fun R hR=>by rw [Finset.length_toList]; exact hH3 R (Finset.mem_toList.mp hR)
 have hg:rest.length=H.toList.length * (3 * (n.log2+1)):=by
  have hfl:∀ (L:List ((Q3 n))),(∀ R∈L,R.toList.length=3)→
   (L.flatMap (fun R=>R.toList.flatMap (fun u=>bits (n.log2+1) u.val))).length=
     L.length * (3 * (n.log2+1)):=by
   intro L; induction L with
   | nil=>intro _; simp
   | cons R L ih=>
     intro hL
     simp only [List.flatMap_cons,List.length_append,qI,
      ih (fun R' hR'=>hL R' (by simp [hR']))]
     have hR3:R.toList.length=3:=hL R (by simp)
     have hv:(R.toList.flatMap (fun u=>bits (n.log2+1) u.val)).length=3 * (n.log2+1):=by simp only [List.length_flatMap,bits,zM,List.length_range,List.map_const',List.sum_replicate,smul_eq_mul,hR3]
     rw [hv]; ring
  exact hfl H.toList hl
 have hk:numTr x=H.toList.length:=by
  have hxl:x.length=offH x+rest.length:=by
   have:=congrArg List.length h6;rw [List.length_drop] at this;have hoff_le:offH x≤x.length:=by rw [hB,he]; simp; omega
   omega
  simp only [numTr,hxl,Nat.add_sub_cancel_left,hg,hw];exact Nat.mul_div_cancel _ (by positivity)
 have hc:∀ (k:ℕ) (m:ℕ),m<2 ^ k→
  ((List.range k).map (fun i=>(if m.testBit i then 1 else 0) * 2 ^ i)).sum=m:=by
  intro k; induction k with
  | zero=>intro m hm; simp at hm ⊢; omega
  | succ k ih=>
    intro m hm;rw [zP,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton];have hH:m % 2 ^ k<2 ^ k:=Nat.mod_lt _ (by positivity)
    have hI:(List.range k).map (fun i=>(if m.testBit i then 1 else 0) * 2 ^ i)=
     (List.range k).map (fun i=>(if (m % 2 ^ k).testBit i then 1 else 0) * 2 ^ i):=by
     refine List.map_congr_left fun i hi=>?_
     rw [Nat.testBit_mod_two_pow,decide_eq_true (qw.mp hi),Bool.true_and]
    rw [hI,ih (m % 2 ^ k) hH,Nat.testBit_eq_decide_div_mod_eq]
    have hdiv_lt:m / 2 ^ k<2:=by rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [pow_succ,mul_comm] using hm
    have hdm:=Nat.mod_add_div m (2 ^ k)
    match hq:m / 2 ^ k with
    | 0=>simp [hq]; rw [hq,mul_zero,add_zero] at hdm; exact hdm
    | 1=>simp [hq]; rw [hq,mul_one] at hdm; omega
    | q+2=>omega
 have ho:∀ p,x.getD (offH x+p) false=rest.getD p false:=fun p=>by rw [qf,qf,← h6,List.getElem?_drop]
 have h5:∀ {α:Type} (c:ℕ) (L:List α) (f:α→Q0),
  (∀ a∈L,(f a).length=c)→∀ (r i:ℕ) (hr:r<L.length),i<c→
  (L.flatMap f).getD (r * c+i) false=(f (L[r]'hr)).getD i false:=by
  intro α c L f hf;induction L with
  | nil=>intro r _ hr; simp at hr
  | cons a L ih=>
    intro r i hr hi
    cases r with
    | zero=>
      simp only [zero_mul,zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [qf,List.getElem?_append_left (by rw [hf a (by simp)]; exact hi),
       ← qf]
    | succ r=>
      simp only [List.flatMap_cons,List.getElem_cons_succ];have hu:(f a).length=c:=hf a (by simp)
      rw [qf,List.getElem?_append_right (by rw [hu]; nlinarith),
       hu,show (r+1) * c+i-c=r * c+i by rw [Nat.add_mul,one_mul]; omega,
       ← qf]
      exact ih (fun b hb=>hf b (by simp [hb])) r i (by simpa using hr) hi
 have hA:rawH x=H.toList.map (fun R=>R.toList.map Fin.val):=by
  apply List.ext_getElem (by simp [rawH,hk]);intro r hr1 hr2;have hr:r<H.toList.length:=by simpa [rawH,hk] using hr1
  simp only [rawH,List.getElem_map,List.getElem_range];set R:=H.toList[r];have hR3:R.toList.length=3:=hl R (qn hr);apply List.ext_getElem (by simp [hR3]);intro j hj1 hj2;have hj:j<3:=by simpa using hj1
  simp only [List.getElem_map,List.getElem_range,uq,hw];set u:Fin n:=R.toList[j]'(by omega)
  have hp:∀ i∈List.range (n.log2+1),
   wm x (offH x+(3 * r+j) * (n.log2+1)+i) * 2 ^ i=
    (if u.val.testBit i then 1 else 0) * 2 ^ i:=by
   intro i hi;have hC:i<n.log2+1:=qw.mp hi;congr 1; simp only [wm];rw [Nat.add_assoc,ho];have hG:(3 * r+j) * (n.log2+1)+i=r * (3 * (n.log2+1))+(j * (n.log2+1)+i):=by ring
   rw [hG,h5 (3 * (n.log2+1)) H.toList
    (fun R'=>R'.toList.flatMap (fun v=>bits (n.log2+1) v.val))
    (fun R' hR'=>by
      simp only [List.length_flatMap,bits,zM,List.length_range,
       List.map_const',List.sum_replicate,smul_eq_mul,hl R' hR']) r (j * (n.log2+1)+i) hr (by nlinarith)]
   rw [h5 (n.log2+1) R.toList (fun v=>bits (n.log2+1) v.val)
    (fun _ _=>by simp [bits]) j i (by omega) hC]
   have hJ:(bits (n.log2+1) u.val).getD i false=u.val.testBit i:=by simp [bits,qf,hC]
   rw [hJ]
  rw [List.map_congr_left hp]
  have hD:u.val<2 ^ (n.log2+1):=by
   have hn:0<n:=Nat.pos_of_ne_zero (fun h0=>by subst h0; exact u.elim0)
   exact u.isLt.trans (Nat.lt_pow_succ_log_self (b:=2) (by norm_num) n |> fun h=>by rwa [← Nat.log2_eq_log_two] at h)
  exact hc (n.log2+1) u.val hD
 refine ⟨hN,hT,hA,fun u v w huv huw hvw=>?_⟩
 have h4:∀ (R:Q3 n),R.card=3→∀ (a:Fin n),
  inR (R.toList.map Fin.val) a.val=1↔a∈R:=by
  intro R hR3 a;have hu:(R.toList.map Fin.val).length=3:=by simp [hR3]
  have h8:((List.range 3).map (fun j=>if g (R.toList.map Fin.val) j=a.val then 1 else 0)).sum≠0↔
   a∈R:=by
   constructor
   · intro hne;by_contra han;apply hne
     have hh:∀ j∈List.range 3,(if g (R.toList.map Fin.val) j=a.val then 1 else 0)=0:=by
      intro j hj;have hj3:j<3:=qw.mp hj
      have hgj:g (R.toList.map Fin.val) j=(R.toList[j]'(by rw [Finset.length_toList]; omega)).val:=by simp [g,qf,List.getElem?_eq_getElem (show j<R.toList.length by rw [Finset.length_toList]; omega)]
      rw [hgj,if_neg];intro heq;exact han (Finset.mem_toList.mp (Fin.ext heq▸qn _))
     rw [List.map_congr_left hh,List.map_const',List.sum_replicate,smul_eq_mul,mul_zero]
   · intro haR;have haL:a∈R.toList:=Finset.mem_toList.mpr haR;rcases vI.mp haL with ⟨j,hj,hja⟩
     have hj3:j<3:=by rw [Finset.length_toList,hR3] at hj; exact hj
     have hgj:g (R.toList.map Fin.val) j=a.val:=by simp [g,qf,List.getElem?_eq_getElem hj,hja]
     have ht:1∈(List.range 3).map (fun j=>if g (R.toList.map Fin.val) j=a.val then 1 else 0):=qQ.mpr ⟨j,qw.mpr hj3,by rw [hgj]; simp⟩
     have hge:1≤((List.range 3).map (fun j=>if g (R.toList.map Fin.val) j=a.val then 1 else 0)).sum:=List.le_sum_of_mem ht
     omega
  simp only [inR];split_ifs with h0
  · simp [h8.not.mp (not_not.mpr h0)]
  · simp [h8.mp h0]
 have h7:∀ R a,inR R a=0∨inR R a=1:=fun R a=>by simp only [inR]; split_ifs <;> simp
 simp only [qdH,hA,zM]
 have h9:((List.range H.toList.length).map (fun r=>
  inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) u.val *
  inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) v.val *
  inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) w.val)).sum≠0↔
  ({u,v,w}:Q3 n)∈H:=by
  have hs:∀ r (hr:r<H.toList.length),
   let R:=H.toList[r]
   (inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) u.val *
    inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) v.val *
    inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) w.val)=
   if R={u,v,w} then 1 else 0:=by
   intro r hr; dsimp only;set R:=H.toList[r];have hRH:R∈H:=Finset.mem_toList.mp (qn hr)
   have hgg:gg (H.toList.map (fun R=>R.toList.map Fin.val)) r=R.toList.map Fin.val:=by simp [gg,qf,List.getElem?_eq_getElem hr,R]
   rw [hgg]
   have hy:({u,v,w}:Q3 n).card=3:=by rw [Finset.card_insert_of_notMem (by simp [huv,huw]),zv hvw]
   have ha:(u∈R∧v∈R∧w∈R)↔R={u,v,w}:=by
    constructor
    · rintro ⟨huR,hvR,hwR⟩
      have hE:({u,v,w}:Q3 n)⊆R:=by intro z hz; simp only [qe,qd] at hz;rcases hz with rfl|rfl|rfl <;> assumption
      exact (zo hE (by rw [hy,hH3 R hRH])).symm
    · intro hR; rw [hR]; simp
   rcases h7 (R.toList.map Fin.val) u.val with hu0|hu1 <;>
   rcases h7 (R.toList.map Fin.val) v.val with hv0|hv1 <;>
   rcases h7 (R.toList.map Fin.val) w.val with hw0|hw1
   · rw [hu0]; simp; intro heq; have:=(h4 R (hH3 R hRH) u).mpr (ha.mpr heq).1; omega
   · rw [hu0]; simp; intro heq; have:=(h4 R (hH3 R hRH) u).mpr (ha.mpr heq).1; omega
   · rw [hu0]; simp; intro heq; have:=(h4 R (hH3 R hRH) u).mpr (ha.mpr heq).1; omega
   · rw [hu0]; simp; intro heq; have:=(h4 R (hH3 R hRH) u).mpr (ha.mpr heq).1; omega
   · rw [hv0]; simp; intro heq; have:=(h4 R (hH3 R hRH) v).mpr (ha.mpr heq).2.1; omega
   · rw [hv0]; simp; intro heq; have:=(h4 R (hH3 R hRH) v).mpr (ha.mpr heq).2.1; omega
   · rw [hw0]; simp; intro heq; have:=(h4 R (hH3 R hRH) w).mpr (ha.mpr heq).2.2; omega
   · rw [hu1,hv1,hw1];have h1:=(h4 R (hH3 R hRH) u).mp hu1;have h2:=(h4 R (hH3 R hRH) v).mp hv1;have h3:=(h4 R (hH3 R hRH) w).mp hw1;simp [ha.mp ⟨h1,h2,h3⟩]
  constructor
  · intro hne;by_contra hnot;apply hne
    have hh:∀ r∈List.range H.toList.length,
     (inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) u.val *
      inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) v.val *
      inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) w.val)=0:=by
     intro r hr;have hrl:r<H.toList.length:=qw.mp hr;rw [hs r hrl,if_neg];intro heq; exact hnot (heq▸Finset.mem_toList.mp (qn hrl))
    rw [List.map_congr_left hh,List.map_const',List.sum_replicate,smul_eq_mul,mul_zero]
  · intro ht;rcases vI.mp (Finset.mem_toList.mpr ht) with ⟨r,hr,hF⟩
    have h1:1∈(List.range H.toList.length).map (fun r=>
     inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) u.val *
     inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) v.val *
     inR (gg (H.toList.map (fun R=>R.toList.map Fin.val)) r) w.val):=
     qQ.mpr ⟨r,qw.mpr hr,by rw [hs r hr,if_pos hF]⟩
    have:=List.le_sum_of_mem h1;omega
 split_ifs with h0
 · simp [h9.not.mp (not_not.mpr h0)]
 · simp [h9.mp h0]
end Alg
namespace Alg
open PEqualNP.Library Lib.qC Lib.ve Lib.j4 Lib.R
lemma yr {n:Q0→ℕ} (G:ℕ→Q0→ℕ) (hn:qi n)
 (hG:qi (fun t=>G (Q9 t).1.length (Q9 t).2)):
 qS (fun s=>(List.range (n s)).map (fun i=>G i s)):=
 u1 (A:=id) (G:=G) yP hn hG
lemma qcv {n:Q0→ℕ} (H:ℕ→Q0→Q1) (hn:qi n)
 (hH:qS (fun t=>H (Q9 t).1.length (Q9 t).2)):
 qS (fun s=>(List.range (n s)).flatMap (fun i=>H i s)):=
 qdb (A:=id) (H:=H) yP hn hH
lemma qav {n:Q0→ℕ} (H:ℕ→Q0→Q1) (hn:qi n)
 (hH:qS (fun t=>H (Q9 t).1.length (Q9 t).2)):
 LLR (fun s=>(List.range (n s)).map (fun i=>H i s)):=
 qb8 (A:=id) (H:=H) yP hn hH
lemma jT {n:Q0→ℕ} (H:ℕ→Q0→Q2) (hn:qi n)
 (hH:LLR (fun t=>H (Q9 t).1.length (Q9 t).2)):
 LLR (fun s=>(List.range (n s)).flatMap (fun i=>H i s)):=
 qdp (A:=id) (H:=H) yP hn hH
lemma zm {v:Q0→Q1} (hv:qS v):qS (fun t=>v (Q9 t).2):=k1 zA hv
lemma zK {S:Q0→Q2} (hS:LLR S):LLR (fun t=>S (Q9 t).2):=qdo zA hS
lemma k0 {a:Q0→ℕ} (ha:qi a):qi (fun s=>if a s=0 then 0 else 1):=z5 ha (qb 0) (qb 0) (qb 1)
lemma kw {a:Q0→ℕ} (ha:qi a):qi (fun s=>if a s=0 then 1 else 0):=z5 ha (qb 0) (qb 1) (qb 0)
lemma yD {a b:Q0→ℕ} {x y:Q0→Q1}
 (ha:qi a) (hb:qi b) (hx:qS x) (hy:qS y):
 qS (fun s=>if a s=b s then x s else y s):=
 zk (yQ ha hb hx hy) (fun s=>by dsimp only; split_ifs <;> rfl)
lemma qbS {a b:Q0→ℕ} {x y:Q0→Q1}
 (ha:qi a) (hb:qi b) (hx:qS x) (hy:qS y):
 qS (fun s=>if a s<b s then x s else y s):=
 zk (jG ha hb hx hy) (fun s=>by dsimp only; split_ifs <;> rfl)
lemma uI {a b:Q0→ℕ} {x y:Q0→Q2}
 (ha:qi a) (hb:qi b) (hx:LLR x) (hy:LLR y):
 LLR (fun s=>if a s=b s then x s else y s):=
 zk (yQ ha hb hx hy) (fun s=>by dsimp only; split_ifs <;> rfl)
lemma uJ {a b:Q0→ℕ} {x y:Q0→Q2}
 (ha:qi a) (hb:qi b) (hx:LLR x) (hy:LLR y):
 LLR (fun s=>if a s<b s then x s else y s):=
 zk (jG ha hb hx hy) (fun s=>by dsimp only; split_ifs <;> rfl)
def zZ (Hraw:Q2) (u v w:ℕ):ℕ:=
 if ((List.range Hraw.length).map (fun r=>inR (gg Hraw r) u * inR (gg Hraw r) v * inR (gg Hraw r) w)).sum=0
 then 0 else 1
lemma wZ {R:Q0→Q1} {a:Q0→ℕ} (hR:qS R) (ha:qi a):
 qi (fun s=>inR (R s) (a s)):=
 k0 (zJ (yr (fun j s=>if g (R s) j=a s then 1 else 0) (qb 3)
  (z5 (qO (zm hR) qs) (qz ha) (qb 1) (qb 0))))
lemma jZ {Hraw:Q0→Q2} {u v w:Q0→ℕ}
 (hH:LLR Hraw) (hu:qi u) (hv:qi v) (hw:qi w):
 qi (fun s=>zZ (Hraw s) (u s) (v s) (w s)):=
 k0 (zJ (yr (fun r s=>
  inR (gg (Hraw s) r) (u s) * inR (gg (Hraw s) r) (v s) * inR (gg (Hraw s) r) (w s))
  (vr hH)
  (let hr:=vw (zK hH) qs
   vn (vn (wZ hr (qz hu)) (wZ hr (qz hv)))
    (wZ hr (qz hw)))))
def kj (n:ℕ) (Hraw:Q2) (a b:ℕ):Q1:=
 (List.range n).flatMap (fun w=>if w=a then [] else if w=b then [] else if zZ Hraw a b w=1 then [w] else [])
def yH (n:ℕ) (Hraw:Q2):Q2:=
 (List.range n).flatMap (fun a=>(List.range n).flatMap (fun b=>
   if a<b then
    let os:=kj n Hraw a b
    if os.length=2 then [[a,b,g os 0,g os 1]] else []
   else []))
def yN (n:ℕ) (C:Q2):Q1:=
 (List.range n).map (fun u=>
   if ((List.range C.length).map (fun r=>(if g (gg C r) 0=u then 1 else 0)+(if g (gg C r) 1=u then 1 else 0))).sum=0
   then 1 else 0)
def kt (n:ℕ) (Hraw:Q2) (om:Q1):Q2:=
 (List.range n).flatMap (fun u=>(List.range n).flatMap (fun v=>
   if u<v then (List.range n).flatMap (fun w=>
    if v<w then
     if g om u * g om v * g om w * zZ Hraw u v w=1 then [[u,v,w]] else []
    else [])
   else []))
def yM (n t:ℕ):Q2:=(List.range (n / 2+1)).map (fun _=>qA t 0)
def uh (t:ℕ):Q1:=(List.range (t-1)).map (fun _=>0)
def y4 (hdr om idx:Q1) (C B acc:Q2):Q0:=qv (zn hdr) (qv (zn om) (qv (zR C) (qv (zR B) (qv (zn idx) (zR acc)))))
def initSt (x:Q0):Q0:=
 let n:=parseN x
 let t:=parseT x;let Hraw:=rawH x;let C:=yH n Hraw;let om:=yN n C;let B:=kt n Hraw om;let done:=if t=0 then 1 else 0
 y4 [n,t,done] om (uh t) C B (yM n t)
lemma qbC {n a b:Q0→ℕ} {Hraw:Q0→Q2}
 (hn:qi n) (hH:LLR Hraw) (ha:qi a) (hb:qi b):
 qS (fun s=>kj (n s) (Hraw s) (a s) (b s)):=
 qcv (fun w s=>if w=a s then [] else if w=b s then [] else
  if zZ (Hraw s) (a s) (b s) w=1 then [w] else []) hn
  (yD qs (qz ha) jV (yD qs (qz hb) jV (yD (jZ (zK hH) (qz ha) (qz hb) qs) (qb 1) (qT qs) jV)))
lemma qbn {n:Q0→ℕ} {Hraw:Q0→Q2}
 (hn:qi n) (hH:LLR Hraw):LLR (fun s=>yH (n s) (Hraw s)):=
 jT (fun a s=>(List.range (n s)).flatMap (fun b=>
  if a<b then
   let os:=kj (n s) (Hraw s) a b
   if os.length=2 then [[a,b,g os 0,g os 1]] else []
  else [])) hn
  (jT (fun b z=>
    let a:=(Q9 z).1.length;let s:=(Q9 z).2
    if a<b then
     let os:=kj (n s) (Hraw s) a b
     if os.length=2 then [[a,b,g os 0,g os 1]] else []
    else []) (qz hn)
    (by
      have hb:=qs;have ha:=qz qs;have hn2:=qz (qz hn);have hH2:=zK (zK hH);have hos:=qbC hn2 hH2 ha hb
      have hq:=zI (qT ha) (zI (qT hb)
       (zI (qT (qO hos (qb 0))) (qT (qO hos (qb 1)))))
      exact uJ ha hb
       (uI (vg hos) (qb 2) (uK hq) uj) uj))
lemma qbB {n:Q0→ℕ} {C:Q0→Q2}
 (hn:qi n) (hC:LLR C):qS (fun s=>yN (n s) (C s)):=
 yr (fun u s=>if ((List.range (C s).length).map (fun r=>
  (if g (gg (C s) r) 0=u then 1 else 0)+(if g (gg (C s) r) 1=u then 1 else 0))).sum=0
  then 1 else 0) hn
  (kw (zJ (yr (fun r z=>
    (if g (gg (C (Q9 z).2) r) 0=(Q9 z).1.length then 1 else 0) +
    (if g (gg (C (Q9 z).2) r) 1=(Q9 z).1.length then 1 else 0))
    (vr (zK hC))
    (let hrow:=vw (zK (zK hC)) qs
     let hu:=qz qs
     q9
      (z5 (qO hrow (qb 0)) hu (qb 1) (qb 0))
      (z5 (qO hrow (qb 1)) hu (qb 1) (qb 0))))))
lemma qbm {n:Q0→ℕ} {Hraw:Q0→Q2} {om:Q0→Q1}
 (hn:qi n) (hH:LLR Hraw) (hom:qS om):LLR (fun s=>kt (n s) (Hraw s) (om s)):=
 jT (fun u s=>(List.range (n s)).flatMap (fun v=>
  if u<v then (List.range (n s)).flatMap (fun w=>
   if v<w then
    if g (om s) u * g (om s) v * g (om s) w * zZ (Hraw s) u v w=1 then [[u,v,w]] else []
   else [])
  else [])) hn
  (jT (fun v z1=>
    let u:=(Q9 z1).1.length;let s:=(Q9 z1).2
    if u<v then (List.range (n s)).flatMap (fun w=>
     if v<w then
      if g (om s) u * g (om s) v * g (om s) w * zZ (Hraw s) u v w=1 then [[u,v,w]] else []
     else [])
    else []) (qz hn)
    (uJ (qz qs) qs
      (jT (fun w z2=>
        let v:=(Q9 z2).1.length;let u:=(Q9 (Q9 z2).2).1.length;let s:=(Q9 (Q9 z2).2).2
        if v<w then
         if g (om s) u * g (om s) v * g (om s) w * zZ (Hraw s) u v w=1 then [[u,v,w]] else []
        else []) (qz (qz hn))
        (by
          have hw:=qs;have hv:=qz qs;have hu:=qz (qz qs);have hom3:=zm (zm (zm hom));have hH3:=zK (zK (zK hH))
          have hp:=vn (vn (vn (qO hom3 hu) (qO hom3 hv))
           (qO hom3 hw)) (jZ hH3 hu hv hw)
          have htr:=zI (qT hu) (zI (qT hv) (qT hw));exact uJ hv hw (uI hp (qb 1) (uK htr) uj) uj))
      uj))
lemma qcc:Lib.qF initSt:=by
 have hn:=kM;have ht:=wL;have hH:=qdq;have hC:=qbn hn hH;have hom:=qbB hn hC;have hB:=qbm hn hH hom;have h1:=kw ht
 have h0:qS (fun x=>[parseN x,parseT x,if parseT x=0 then 1 else 0]):=zI (qT hn) (zI (qT ht) (qT h1))
 have h2:qS (fun x=>uh (parseT x)):=yr (fun _ _=>0) (yj ht (qb 1)) (qb 0)
 have h3:LLR (fun x=>yM (parseN x) (parseT x)):=
  qav (fun _ x=>qA (parseT x) 0) (q9 (uo hn (qb 2)) (qb 1))
   (ym (qz ht) (qb 0))
 exact qy h0 (qy hom (qy hC (qy hB (qy h2 h3))))
def vH (m:ℕ) (idx:Q1):ℕ:=
 let badRange:=((List.range idx.length).map (fun i=>if m<g idx i then 1 else 0)).sum
 let badOrder:=((List.range (idx.length-1)).map (fun i=>
  if g idx i<g idx (i+1) then 0
  else if g idx i=m then (if g idx (i+1)=m then 0 else 1) else 1)).sum
 if badRange+badOrder=0 then 1 else 0
def zx (m:ℕ) (idx:Q1) (st:ℕ×Q1):ℕ×Q1:=
 let i:=st.2.length
 let d:=g idx i
 if st.1=0 then (0,st.2++[d])
 else if d+1< m+1 then (0,st.2++[d+1])
 else (1,st.2++[0])
def kY (m:ℕ) (idx:Q1):ℕ×Q1:=(zx m idx)^[idx.length] (1,[])
lemma qbs {m:Q0→ℕ} {idx:Q0→Q1}
 (hm:qi m) (hidx:qS idx):qi (fun s=>vH (m s) (idx s)):=by
 have hb1:=zJ (yr (fun i s=>if m s<g (idx s) i then 1 else 0) (vg hidx)
  (kz (qz hm) (qO (zm hidx) qs) (qb 1) (qb 0)))
 have hb2:=zJ (yr (fun i s=>
  if g (idx s) i<g (idx s) (i+1) then 0
  else if g (idx s) i=m s then (if g (idx s) (i+1)=m s then 0 else 1) else 1)
  (yj (vg hidx) (qb 1))
  (let hv0:=qO (zm hidx) qs
   let hv1:=qO (zm hidx) (q9 qs (qb 1))
   let hm':=qz hm
   kz hv0 hv1 (qb 0)
    (z5 hv0 hm' (z5 hv1 hm' (qb 0) (qb 1)) (qb 1))))
 exact kw (q9 hb1 hb2)
lemma wC (m:ℕ) (idx:Q1) (k:ℕ):
 let p:=(zx m idx)^[k] (1,[])
 p.1≤1∧p.2.length=k∧p.2.sum≤(idx.take k).sum+k:=by
 induction k with
 | zero=>simp
 | succ k ih=>
   rcases ih with ⟨hc,hl,hsum⟩
   rw [qM];dsimp only [zx];set p:=(zx m idx)^[k] (1,[])
   have hd:(idx.take k).sum+g idx p.2.length=(idx.take (k+1)).sum:=by
    rw [hl];by_cases hi:k< idx.length
    · rw [List.take_succ_eq_append_getElem hi,List.sum_append,List.sum_singleton];have:g idx k=idx[k]:=by simp [g,qf,hi]
      rw [this]
    · rw [vo (show idx.length≤k by omega),
       vo (show idx.length≤k+1 by omega)]
      have:g idx k=0:=by simp [g,qf,List.getElem?_eq_none (yt hi)]
      omega
   split_ifs <;> refine ⟨by omega,by simp [hl],by simp only [List.sum_append,List.sum_singleton]; omega⟩
lemma qbF {m:Q0→ℕ} {idx:Q0→Q1}
 (hm:qi m) (hidx:qS idx):
 Lib.qF (fun s=>qv (un (kY (m s) (idx s)).1) (zn (kY (m s) (idx s)).2)):=by
 obtain ⟨Pl,hPl⟩:=z8 (vg hidx);obtain ⟨Ps,hPs⟩:=z8 (zJ hidx)
 let F:Q0→Q0:=fun z=>
  let st:=(Q9 z).1;let s:=(Q9 z).2;let c:=(Q9 st).1.length;let out:=vK (Q9 st).2;let d:=g (idx s) out.length
  if c=0 then qv (un 0) (zn (out++[d]))
  else if d+1< m s+1 then qv (un 0) (zn (out++[d+1]))
  else qv (un 1) (zn (out++[0]))
 have hF:Lib.qF F:=by
  have hc:=yY (qZ zz);have h0:=vv (qo zz);have hd:=qO (zm hidx) (vg h0);have hms:=qz hm
  exact yQ hc (qb 0)
   (qy (qb 0) (zI h0 (qT hd)))
   (jG (q9 hd (qb 1)) (q9 hms (qb 1)) (qy (qb 0) (zI h0 (qT (q9 hd (qb 1))))) (qy (qb 1) (zI h0 (qT (qb 0)))))
 have heq:∀ s k,(fun a=>F (qv a s))^[k] (qv (un 1) (zn []))=
  qv (un ((zx (m s) (idx s))^[k] (1,[])).1)
   (zn ((zx (m s) (idx s))^[k] (1,[])).2):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih];simp only [F,zx,qk,za,zU];split_ifs <;> rfl
 let PB:Q5:=Ps+Polynomial.C 2 * Pl+Polynomial.C 5
 have h3:=y6 hF (yp (qv (un 1) (zn []))) (vg hidx) PB (fun s i hi=>by
  rw [heq s i,zW,za,vy];rcases wC (m s) (idx s) i with ⟨hc,hl,hsum⟩
  have htake:((idx s).take i).sum≤(idx s).sum:=by have h1:=congrArg List.sum (List.take_append_drop i (idx s));rw [List.sum_append] at h1; omega
  have hi':i≤(idx s).length:=by simpa [za] using hi
  have h1:=hPl s; have h2:=hPs s;simp only [PB,zO,z9,vT]; omega)
 exact zk h3 (fun s=>by rw [za,heq]; rfl)
def y0 (C:Q2) (idx:Q1):Q2:=(List.range idx.length).flatMap (fun i=>if g idx i<C.length then [gg C (g idx i)] else [])
def yU (Srows:Q2):Q1:=(List.range Srows.length).flatMap (fun r=>[g (gg Srows r) 2,g (gg Srows r) 3])
def yu (v:Q1):ℕ:=
 if ((List.range v.length).map (fun i=>
     ((List.range v.length).map (fun k=>if i<k then (if g v i=g v k then 1 else 0) else 0)).sum)).sum=0
 then 1 else 0
def yX (n:ℕ) (om outFlat:Q1):Q1:=
 (List.range n).map (fun v=>
   if g om v=1 then
    if ((List.range outFlat.length).map (fun i=>if g outFlat i=v then 1 else 0)).sum=0
    then 1 else 0
   else 0)
def zc (um R:Q1):Q1:=(List.range R.length).flatMap (fun i=>if g um (g R i)=1 then [g R i] else [])
def vU (um:Q1) (B:Q2):Q2:=(List.range B.length).map (fun r=>zc um (gg B r))
lemma qbo {C:Q0→Q2} {idx:Q0→Q1}
 (hC:LLR C) (hidx:qS idx):LLR (fun s=>y0 (C s) (idx s)):=
 jT (fun i s=>if g (idx s) i<(C s).length then [gg (C s) (g (idx s) i)] else []) (vg hidx)
  (let hgi:=qO (zm hidx) qs
   uJ hgi (vr (zK hC)) (uK (vw (zK hC) hgi)) uj)
lemma qax {Srows:Q0→Q2} (hS:LLR Srows):
 qS (fun s=>yU (Srows s)):=
 qcv (fun r s=>[g (gg (Srows s) r) 2,g (gg (Srows s) r) 3]) (vr hS)
  (let hrow:=vw (zK hS) qs
   zI (qT (qO hrow (qb 2)))
    (qT (qO hrow (qb 3))))
lemma qbr {v:Q0→Q1} (hv:qS v):qi (fun s=>yu (v s)):=
 kw (zJ (yr (fun i s=>
  ((List.range (v s).length).map (fun k=>if i<k then (if g (v s) i=g (v s) k then 1 else 0) else 0)).sum)
  (vg hv)
  (zJ (yr (fun k z=>
    let i:=(Q9 z).1.length;let s:=(Q9 z).2
    if i<k then (if g (v s) i=g (v s) k then 1 else 0) else 0)
    (vg (zm hv))
    (let hv2:=zm (zm hv)
     let hi:=qz qs
     kz hi qs (z5 (qO hv2 hi) (qO hv2 qs) (qb 1) (qb 0))
      (qb 0))))))
lemma qaZ {n:Q0→ℕ} {om outF:Q0→Q1}
 (hn:qi n) (hom:qS om) (ho:qS outF):
 qS (fun s=>yX (n s) (om s) (outF s)):=
 yr (fun v s=>
  if g (om s) v=1 then
   if ((List.range (outF s).length).map (fun i=>if g (outF s) i=v then 1 else 0)).sum=0
   then 1 else 0
  else 0) hn
  (z5 (qO (zm hom) qs) (qb 1)
    (kw (zJ (yr (fun i z=>if g (outF (Q9 z).2) i=(Q9 z).1.length then 1 else 0)
      (vg (zm ho))
      (z5 (qO (zm (zm ho)) qs) (qz qs) (qb 1) (qb 0)))))
    (qb 0))
lemma jg {um R:Q0→Q1} (hum:qS um) (hR:qS R):
 qS (fun s=>zc (um s) (R s)):=
 qcv (fun i s=>if g (um s) (g (R s) i)=1 then [g (R s) i] else []) (vg hR)
  (let hv:=qO (zm hR) qs
   yD (qO (zm hum) hv) (qb 1) (qT hv) jV)
lemma qaa {um:Q0→Q1} {B:Q0→Q2}
 (hum:qS um) (hB:LLR B):LLR (fun s=>vU (um s) (B s)):=
 qav (fun r s=>zc (um s) (gg (B s) r)) (vr hB)
  (jg (zm hum) (vw (zK hB) qs))
def jv (F:Q2):ℕ:=
 if ((List.range F.length).map (fun r=>if (gg F r).length<2 then 1 else 0)).sum=0
 then 0 else 1
def vl (F:Q2):ℕ:=
 ((List.range F.length).map (fun i=>
   if ((List.range (i+1)).map (fun r=>if (gg F r).length=2 then 1 else 0)).sum=0
   then 1 else 0)).sum
structure PeelSt where
 dead:ℕ
 kF:ℕ
 um:Q1
 F:Q2
def yb (n:ℕ) (st:PeelSt):PeelSt:=if st.dead=1 then st
 else if jv st.F=1 then ⟨1,st.kF,st.um,st.F⟩
 else
  let idx:=vl st.F
  if idx=st.F.length then st
  else
   let e:=gg st.F idx
   let p:=g e 0;let q:=g e 1
   let um':=(List.range n).map (fun v=>if v=p then 0 else if v=q then 0 else if g st.um v=0 then 0 else 1)
   let F':=(List.range st.F.length).flatMap (fun r=>if r=idx then [] else [zc um' (gg st.F r)])
   ⟨0,st.kF+1,um',F'⟩
def kD (n:ℕ) (um:Q1) (F:Q2):PeelSt:=(yb n)^[n] ⟨0,0,um,F⟩
lemma jJ (um R:Q1):
 (zc um R).length+(zc um R).sum≤R.length+R.sum:=by
 have h0:∀ k,k≤R.length→
  let fl:=(List.range k).flatMap (fun i=>if g um (g R i)=1 then [g R i] else [])
  fl.length+fl.sum≤k+(R.take k).sum:=by
  intro k; induction k with
  | zero=>intro _; simp
  | succ k ih=>
    intro hk; dsimp only
    rw [zP,List.flatMap_append,List.flatMap_singleton,
     List.length_append,List.sum_append,List.take_succ_eq_append_getElem (by omega),
     List.sum_append,List.sum_singleton]
    have hprev:=ih (by omega);have hgR:g R k=R[k]'(by omega):=by simp [g,qf,show k<R.length by omega]
    split_ifs <;> simp only [List.length_nil,List.length_singleton,List.sum_nil,List.sum_singleton,hgR] <;> omega
 have h:=h0 R.length le_rfl;rwa [List.take_length] at h
lemma qbN (n:ℕ) (um0:Q1) (F0:Q2)
 (hum0:um0.length=n∧∀ b∈um0,b≤1):
 ∀ k,let st:=(yb n)^[k] ⟨0,0,um0,F0⟩
   st.dead≤1∧st.kF≤k∧st.um.length=n∧(∀ b∈st.um,b≤1)∧
   st.F.length≤F0.length∧
   (st.F.map (fun v=>v.length+v.sum)).sum≤(F0.map (fun v=>v.length+v.sum)).sum:=by
 intro k; induction k with
 | zero=>dsimp only [Function.iterate_zero_apply]; exact ⟨by omega,le_rfl,hum0.1,hum0.2,le_rfl,le_rfl⟩
 | succ k ih=>
   rcases ih with ⟨hd,hk,h0,h4,hfl,hfw⟩
   rw [qM];dsimp only [yb];set st:=(yb n)^[k] ⟨0,0,um0,F0⟩;split_ifs with h1 h2 h3
   · exact ⟨hd,by omega,h0,h4,hfl,hfw⟩
   · dsimp only; exact ⟨le_rfl,by omega,h0,h4,hfl,hfw⟩
   · exact ⟨hd,by omega,h0,h4,hfl,hfw⟩
   · set e:=gg st.F (vl st.F)
     set um':=(List.range n).map (fun v=>if v=g e 0 then 0 else if v=g e 1 then 0 else if g st.um v=0 then 0 else 1)
     set F':=(List.range st.F.length).flatMap (fun r=>if r=vl st.F then [] else [zc um' (gg st.F r)])
     have h7:∀ b∈um',b≤1:=by
      intro b hb; simp only [um',qQ] at hb; rcases hb with ⟨_,_,rfl⟩
      split_ifs <;> omega
     have h6:F'.length≤ st.F.length:=by
      have h5:∀ m,((List.range m).flatMap (fun r=>
       if r=vl st.F then [] else [zc um' (gg st.F r)])).length≤ m:=by
       intro m; induction m with
       | zero=>simp
       | succ m ihm=>rw [zP,List.flatMap_append,List.flatMap_singleton,List.length_append];split_ifs <;> simp only [List.length_nil,List.length_singleton,add_zero] <;> omega
      exact h5 st.F.length
     have h8:(F'.map (fun v=>v.length+v.sum)).sum≤(st.F.map (fun v=>v.length+v.sum)).sum:=by
      have h5:∀ m,m≤ st.F.length→
       (((List.range m).flatMap (fun r=>
         if r=vl st.F then [] else [zc um' (gg st.F r)])).map
         (fun v=>v.length+v.sum)).sum≤((st.F.take m).map (fun v=>v.length+v.sum)).sum:=by
       intro m; induction m with
       | zero=>intro _; simp
       | succ m ihm=>
         intro hm
         rw [zP,List.flatMap_append,List.flatMap_singleton,List.map_append,
          List.sum_append,List.take_succ_eq_append_getElem (by omega),List.map_append,
          List.sum_append,List.map_singleton,List.sum_singleton]
         have hp:=ihm (by omega)
         have hgg:gg st.F m=st.F[m]'(by omega):=by simp [gg,qf,show m<st.F.length by omega]
         split_ifs
         · simp only [List.map_nil,List.sum_nil,add_zero]; omega
         · simp only [List.map_singleton,List.sum_singleton,hgg];have:=jJ um' (st.F[m]'(by omega));omega
      have:=h5 st.F.length le_rfl;rwa [List.take_length] at this
     dsimp only;exact ⟨by omega,by omega,by simp [um'],h7,h6.trans hfl,h8.trans hfw⟩
def vQ (st:PeelSt):Q0:=qv (zn [st.dead,st.kF]) (qv (zn st.um) (zR st.F))
lemma qbJ {F:Q0→Q2} (hF:LLR F):qi (fun s=>jv (F s)):=
 k0 (zJ (yr (fun r s=>if (gg (F s) r).length<2 then 1 else 0) (vr hF)
  (kz (vg (vw (zK hF) qs)) (qb 2) (qb 1) (qb 0))))
lemma qaW {F:Q0→Q2} (hF:LLR F):qi (fun s=>vl (F s)):=
 zJ (yr (fun i s=>
  if ((List.range (i+1)).map (fun r=>if (gg (F s) r).length=2 then 1 else 0)).sum=0
  then 1 else 0) (vr hF)
  (kw (zJ (yr (fun r z=>if (gg (F (Q9 z).2) r).length=2 then 1 else 0)
    (q9 qs (qb 1))
    (z5 (vg (vw (zK (zK hF)) qs)) (qb 2) (qb 1) (qb 0))))))
lemma qbD {n p q:Q0→ℕ} {um:Q0→Q1}
 (hn:qi n) (hp:qi p) (hq:qi q) (hum:qS um):
 qS (fun z=>(List.range (n z)).map (fun v=>if v=p z then 0 else if v=q z then 0 else if g (um z) v=0 then 0 else 1)):=
 yr (fun v z=>if v=p z then 0 else if v=q z then 0 else if g (um z) v=0 then 0 else 1) hn
  (z5 qs (qz hp) (qb 0) (z5 qs (qz hq) (qb 0) (k0 (qO (zm hum) qs))))
lemma qcj {idx:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hidx:qi idx) (hum:qS um) (hF:LLR F):
 LLR (fun z=>(List.range (F z).length).flatMap (fun r=>if r=idx z then [] else [zc (um z) (gg (F z) r)])):=
 jT (fun r z=>if r=idx z then [] else [zc (um z) (gg (F z) r)]) (vr hF)
  (uI qs (qz hidx) uj (uK (jg (zm hum) (vw (zK hF) qs))))
lemma qbG {n:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hn:qi n) (hum:qS um) (hF:LLR F)
 (hum0:∀ s,(um s).length=n s∧∀ b∈um s,b≤1):
 Lib.qF (fun s=>vQ (kD (n s) (um s) (F s))):=by
 obtain ⟨Pn,hPn⟩:=z8 hn;obtain ⟨PF,hPF⟩:=yV _ hF
 have h7:∀ S:Q2,S.length+(S.map (fun v=>v.length+v.sum)).sum≤(zR S).length:=by
  intro S; induction S with
  | nil=>simp
  | cons v S ih=>
    have hd:∀ w:Q0,(dbl w).length=2 * w.length:=fun w=>by
     induction w with
     | nil=>rfl
     | cons _ _ ihw=>simp only [qb3,qI,ihw]; omega
    simp only [ju,qI,List.length_append,hd,vy,List.map_cons,List.sum_cons];omega
 let Step:Q0→Q0:=fun z=>
  let st:=(Q9 z).1;let n':=n (Q9 z).2;let hdr:=vK (Q9 st).1;let dead:=g hdr 0;let kF:=g hdr 1;let um':=vK (Q9 (Q9 st).2).1;let F':=ko (Q9 (Q9 st).2).2
  vQ (yb n' ⟨dead,kF,um',F'⟩)
 have ha:Lib.qF Step:=by
  have hst:=zz;have hn':=qz hn;have h3:=vv (qZ hst);have h4:=qO h3 (qb 0);have hkF:=qO h3 (qb 1);have hum':=vv (qZ (qo hst));have hF':=kZ (qo (qo hst))
  have h2:Lib.qF (fun z=>vQ ⟨g (vK (Q9 (Q9 z).1).1) 0,
   g (vK (Q9 (Q9 z).1).1) 1,
   vK (Q9 (Q9 (Q9 z).1).2).1,
   ko (Q9 (Q9 (Q9 z).1).2).2⟩):=
   qy (zI (qT h4) (qT hkF)) (qy hum' hF')
  have h1:Lib.qF (fun z=>vQ ⟨1,
   g (vK (Q9 (Q9 z).1).1) 1,
   vK (Q9 (Q9 (Q9 z).1).2).1,
   ko (Q9 (Q9 (Q9 z).1).2).2⟩):=
   qy (zI (qT (qb 1)) (qT hkF)) (qy hum' hF')
  have h6:=qaW hF';have he:=vw hF' h6;have hp:=qO he (qb 0);have hq:=qO he (qb 1);have h0:=qbD hn' hp hq hum';have h8:=qcj h6 h0 hF'
  have hb:=qy (zI (qT (qb 0)) (qT (q9 hkF (qb 1))))
   (qy h0 h8)
  exact zk (yQ h4 (qb 1) h2 (yQ (qbJ hF') (qb 1) h1
   (yQ h6 (vr hF') h2 hb))) (fun z=>by
   simp only [Step,yb]; split_ifs <;> rfl)
 have heq:∀ s k,(fun a=>Step (qv a s))^[k] (vQ ⟨0,0,um s,F s⟩)=
  vQ ((yb (n s))^[k] ⟨0,0,um s,F s⟩):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih];simp only [Step,vQ,qk,zU,yl,g,List.getD_cons_zero,List.getD_cons_succ]
 let PB:Q5:=Polynomial.C 10 * Pn+Polynomial.C 4 * PF+Polynomial.C 20
 have h5:Lib.qF (fun s=>vQ ⟨0,0,um s,F s⟩):=qy (zI (qT (qb 0)) (qT (qb 0))) (qy hum hF)
 have h9:=y6 ha h5 hn PB (fun s i hi=>by
  rw [heq s i,vQ,zW,zW,vy,vy];rcases qbN (n s) (um s) (F s) (hum0 s) i with ⟨hd,hk,huml,hc,hfl,hfw⟩
  have hums:((yb (n s))^[i] ⟨0,0,um s,F s⟩).um.sum≤n s:=by have hle:=List.sum_le_length_nsmul _ 1 hc;simp only [smul_eq_mul,mul_one] at hle;omega
  have hFenc:=kp ((yb (n s))^[i] ⟨0,0,um s,F s⟩).F;have hFw0:=h7 (F s);have hPF0:=hPF s;have hPn0:=hPn s;have hi':i≤n s:=by simpa [za] using hi
  simp only [qI,List.length_nil,List.sum_cons,List.sum_nil,PB,zO,z9,vT];omega)
 exact zk h9 (fun s=>by rw [za,heq]; rfl)
def vX (n:ℕ) (F:Q2) (vm:Q1):Q1:=
 (List.range n).map (fun v=>
   if g vm v=1 then 1
   else if ((List.range F.length).map (fun r=>
    (if ((List.range (gg F r).length).map (fun i=>if g (gg F r) i=v then 1 else 0)).sum=0 then 0 else 1) *
    (if ((List.range (gg F r).length).map (fun i=>g vm (g (gg F r) i))).sum=0 then 0 else 1))).sum=0
   then 0 else 1)
def zN (n:ℕ) (F:Q2) (u:ℕ):Q1:=(vX n F)^[n] ((List.range n).map (fun v=>if v=u then 1 else 0))
def y1 (n:ℕ) (um:Q1) (F:Q2) (u:ℕ):ℕ:=
 if g um u=1 then
  if ((List.range u).map (fun v=>g (zN n F u) v)).sum=0 then 1 else 0
 else 0
def yA (n:ℕ) (F:Q2) (u:ℕ):ℕ:=(zN n F u).sum
def yG (n:ℕ) (F:Q2) (u:ℕ):ℕ:=
 let cm:=zN n F u
 ((List.range F.length).map (fun r=>
   if ((List.range (gg F r).length).map (fun i=>1-g cm (g (gg F r) i))).sum=0
   then 1 else 0)).sum
def yT (n:ℕ) (um:Q1) (F:Q2):ℕ:=
 if ((List.range n).map (fun u=>if y1 n um F u=1 then (if yA n F u<2 * yG n F u then 1 else 0) else 0)).sum=0
 then 0 else 1
def kN (n:ℕ) (um:Q1) (F:Q2):ℕ:=
 ((List.range n).map (fun u=>if y1 n um F u=1 then (if yA n F u=2 * yG n F u then 1 else 0) else 0)).sum
def kx (n:ℕ) (um:Q1) (F:Q2):ℕ:=
 ((List.range n).map (fun u=>if y1 n um F u=1 then (if yA n F u=2 * yG n F u+1 then 1 else 0) else 0)).sum
def vZ (n t:ℕ) (um:Q1) (F:Q2) (st:ℕ×Q1):ℕ×Q1:=
 let u:=st.1
 let acc':=if y1 n um F u=1 then
  (if yA n F u=2 * yG n F u+1 then kK t st.2 (qA t (yA n F u)) else st.2)
  else st.2
 (u+1,acc')
def vS (n t:ℕ) (um:Q1) (F:Q2):Q1:=((vZ n t um F)^[n] (0,qA t 1)).2
def vW (t cols:ℕ) (st:ℕ×(Q2)×(Q2)):
    ℕ×(Q2)×(Q2):=
 let r:=st.1;let prev:=st.2.1;let cur:=st.2.2;let rB:=qA t r
 let next:=(List.range cols).map (fun m=>
  if m=0 then qA t 1
  else kI t (gg cur m) (kK t rB (gg prev (m-1))))
 (r+1,cur,next)
def yC (t cols T:ℕ):Q2:=
 let prev0:=(List.range cols).map (fun _=>qA t 0)
 let cur0:=(List.range cols).map (fun m=>if m=0 then qA t 1 else qA t 0)
 ((vW t cols)^[T] (0,prev0,cur0)).2.2
lemma qbU {n:Q0→ℕ} {F:Q0→Q2} {vm:Q0→Q1}
 (hn:qi n) (hF:LLR F) (hvm:qS vm):qS (fun s=>vX (n s) (F s) (vm s)):=
 yr (fun v s=>
  if g (vm s) v=1 then 1
  else if ((List.range (F s).length).map (fun r=>
   (if ((List.range (gg (F s) r).length).map (fun i=>if g (gg (F s) r) i=v then 1 else 0)).sum=0 then 0 else 1) *
   (if ((List.range (gg (F s) r).length).map (fun i=>g (vm s) (g (gg (F s) r) i))).sum=0 then 0 else 1))).sum=0
  then 0 else 1) hn
  (z5 (qO (zm hvm) qs) (qb 1) (qb 1)
    (k0 (zJ (yr (fun r z=>
      let v:=(Q9 z).1.length;let s:=(Q9 z).2
      (if ((List.range (gg (F s) r).length).map (fun i=>if g (gg (F s) r) i=v then 1 else 0)).sum=0 then 0 else 1) *
      (if ((List.range (gg (F s) r).length).map (fun i=>g (vm s) (g (gg (F s) r) i))).sum=0 then 0 else 1))
      (vr (zK hF))
      (by
        have hrow:=vw (zK (zK hF)) qs;have hv2:=qz qs;have hvm2:=zm (zm hvm)
        have h1:=k0 (zJ (yr (fun i y=>
         if g (gg (F (Q9 (Q9 y).2).2) (Q9 y).1.length) i=(Q9 (Q9 y).2).1.length then 1 else 0)
         (vg hrow)
         (z5 (qO (zm hrow) qs) (qz hv2) (qb 1) (qb 0))))
        have h2:=k0 (zJ (yr (fun i y=>
         g (vm (Q9 (Q9 y).2).2)
           (g (gg (F (Q9 (Q9 y).2).2) (Q9 y).1.length) i))
         (vg hrow)
         (qO (zm hvm2) (qO (zm hrow) qs))))
        exact vn h1 h2)))))
lemma uC {n u:Q0→ℕ} {F:Q0→Q2}
 (hn:qi n) (hF:LLR F) (hu:qi u):qS (fun s=>zN (n s) (F s) (u s)):=by
 obtain ⟨Pn,hPn⟩:=z8 hn
 have h2:qS (fun z=>vX (n (Q9 z).2) (F (Q9 z).2) (vK (Q9 z).1)):=qbU (qz hn) (zK hF) (vv zz)
 have h3:qS (fun s=>(List.range (n s)).map (fun v=>if v=u s then 1 else 0)):=
  yr (fun v s=>if v=u s then 1 else 0) hn
   (z5 qs (qz hu) (qb 1) (qb 0))
 have heq:∀ s k,(fun a=>zn (vX (n s) (F s) (vK a)))^[k]
  (zn ((List.range (n s)).map (fun v=>if v=u s then 1 else 0)))=
  zn ((vX (n s) (F s))^[k] ((List.range (n s)).map (fun v=>if v=u s then 1 else 0))):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih,zU]
 have h4:∀ s k,let v:=(vX (n s) (F s))^[k] ((List.range (n s)).map (fun v=>if v=u s then 1 else 0))
  v.length=n s∧∀ b∈v,b≤1:=by
  intro s k; induction k with
  | zero=>
    simp only [Function.iterate_zero_apply];refine ⟨by simp,fun b hb=>?_⟩
    simp only [qQ] at hb; rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
  | succ k _=>
    rw [qM];refine ⟨by simp [vX],fun b hb=>?_⟩
    simp only [vX,qQ] at hb; rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
 let PB:Q5:=Polynomial.C 2 * Pn+Polynomial.C 2
 have h0:=y6 h2 h3 hn PB (fun s i _=>by
  have heq':(fun a=>zn (vX (n (Q9 (qv a s)).2) (F (Q9 (qv a s)).2)
   (vK (Q9 (qv a s)).1)))^[i]
   (zn ((List.range (n s)).map (fun v=>if v=u s then 1 else 0)))=
   zn ((vX (n s) (F s))^[i] ((List.range (n s)).map (fun v=>if v=u s then 1 else 0))):=by
   convert heq s i using 1; congr 1; funext a; simp [qk]
  rw [heq',vy];rcases h4 s i with ⟨hl,hb⟩
  have hs:=by simpa only [smul_eq_mul,mul_one] using List.sum_le_length_nsmul _ 1 hb
  have h1:=hPn s;simp only [PB,zO,z9,vT]; omega)
 exact zk h0 (fun s=>by
  dsimp only; rw [za]; unfold zN
  convert heq s (n s) using 1; congr 1; funext a; simp [qk])
lemma uN {n u:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hn:qi n) (hum:qS um) (hF:LLR F) (hu:qi u):
 qi (fun s=>y1 (n s) (um s) (F s) (u s)):=
 z5 (qO hum hu) (qb 1)
  (kw (zJ (yr (fun v s=>g (zN (n s) (F s) (u s)) v) hu
    (qO (zm (uC hn hF hu)) qs))))
  (qb 0)
lemma uM {n u:Q0→ℕ} {F:Q0→Q2}
 (hn:qi n) (hF:LLR F) (hu:qi u):qi (fun s=>yA (n s) (F s) (u s)):=
 zJ (uC hn hF hu)
lemma ur {n u:Q0→ℕ} {F:Q0→Q2}
 (hn:qi n) (hF:LLR F) (hu:qi u):qi (fun s=>yG (n s) (F s) (u s)):=by
 have hcm:=uC hn hF hu
 exact zJ (yr (fun r s=>
  if ((List.range (gg (F s) r).length).map (fun i=>1-g (zN (n s) (F s) (u s)) (g (gg (F s) r) i))).sum=0
  then 1 else 0) (vr hF)
  (let hrow:=vw (zK hF) qs
   kw (zJ (yr (fun i z=>
    1-g (zN (n (Q9 z).2) (F (Q9 z).2) (u (Q9 z).2))
     (g (gg (F (Q9 z).2) (Q9 z).1.length) i))
    (vg hrow)
    (yj (qb 1) (qO (zm (zm hcm)) (qO (zm hrow) qs)))))))
lemma qcn {n:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hn:qi n) (hum:qS um) (hF:LLR F):qi (fun s=>yT (n s) (um s) (F s)):=
 k0 (zJ (yr (fun u s=>
  if y1 (n s) (um s) (F s) u=1 then
   if yA (n s) (F s) u<2 * yG (n s) (F s) u then 1 else 0
  else 0) hn
  (let hn2:=qz hn; let hum2:=zm hum; let hF2:=zK hF
   z5 (uN hn2 hum2 hF2 qs) (qb 1)
    (kz (uM hn2 hF2 qs) (vn (qb 2) (ur hn2 hF2 qs)) (qb 1) (qb 0)) (qb 0))))
lemma qbK {n:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hn:qi n) (hum:qS um) (hF:LLR F):qi (fun s=>kN (n s) (um s) (F s)):=
 zJ (yr (fun u s=>
  if y1 (n s) (um s) (F s) u=1 then
   if yA (n s) (F s) u=2 * yG (n s) (F s) u then 1 else 0
  else 0) hn
  (let hn2:=qz hn; let hum2:=zm hum; let hF2:=zK hF
   z5 (uN hn2 hum2 hF2 qs) (qb 1)
    (z5 (uM hn2 hF2 qs) (vn (qb 2) (ur hn2 hF2 qs)) (qb 1) (qb 0)) (qb 0)))
lemma qbL {n:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hn:qi n) (hum:qS um) (hF:LLR F):qi (fun s=>kx (n s) (um s) (F s)):=
 zJ (yr (fun u s=>
  if y1 (n s) (um s) (F s) u=1 then
   if yA (n s) (F s) u=2 * yG (n s) (F s) u+1 then 1 else 0
  else 0) hn
  (let hn2:=qz hn; let hum2:=zm hum; let hF2:=zK hF
   z5 (uN hn2 hum2 hF2 qs) (qb 1)
    (z5 (uM hn2 hF2 qs) (q9 (vn (qb 2) (ur hn2 hF2 qs)) (qb 1)) (qb 1) (qb 0)) (qb 0)))
lemma wh (n t:ℕ) (um:Q1) (F:Q2) (k:ℕ):
 let p:=(vZ n t um F)^[k] (0,qA t 1)
 p.1=k∧p.2.length=t∧∀ b∈p.2,b≤1:=by
 induction k with
 | zero=>exact ⟨rfl,zl t 1,zS t 1⟩
 | succ k ih=>
   rcases ih with ⟨h1,h2,h3⟩
   rw [qM];dsimp only [vZ];split_ifs
   · rcases jd t _ (qA t _) t with ⟨_,hl,hb⟩
     exact ⟨by omega,hl,hb⟩
   · exact ⟨by omega,h2,h3⟩
   · exact ⟨by omega,h2,h3⟩
lemma qay {n t:Q0→ℕ} {um:Q0→Q1} {F:Q0→Q2}
 (hn:qi n) (ht:qi t) (hum:qS um) (hF:LLR F):
 qS (fun s=>vS (n s) (t s) (um s) (F s)):=by
 obtain ⟨Pn,hPn⟩:=z8 hn;obtain ⟨Pt,hPt⟩:=z8 ht
 let Step:Q0→Q0:=fun z=>
  let st:=(Q9 z).1;let s:=(Q9 z).2;let u:=(Q9 st).1.length;let acc:=vK (Q9 st).2;let p:=vZ (n s) (t s) (um s) (F s) (u,acc)
  qv (un p.1) (zn p.2)
 have h5:Lib.qF Step:=by
  have hu:=yY (qZ zz);have h0:=vv (qo zz);have hns:=qz hn;have hts:=qz ht;have h6:=zm hum;have hFs:=zK hF;have hcs:=uM hns hFs hu;have hct:=ur hns hFs hu
  have h7:=yD (uN hns h6 hFs hu) (qb 1)
   (yD hcs (q9 (vn (qb 2) hct) (qb 1)) (wk hts h0 (ym hts hcs)) h0) h0
  exact zk (qy (q9 hu (qb 1)) h7) (fun z=>by simp only [Step,vZ])
 have heq:∀ s k,(fun a=>Step (qv a s))^[k] (qv (un 0) (zn (qA (t s) 1)))=
  qv (un ((vZ (n s) (t s) (um s) (F s))^[k] (0,qA (t s) 1)).1)
   (zn ((vZ (n s) (t s) (um s) (F s))^[k] (0,qA (t s) 1)).2):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih];simp only [Step,qk,za,zU]
 let PB:Q5:=Polynomial.C 2 * Pn+Polynomial.C 2 * Pt+Polynomial.C 5
 have h4:=y6 h5 (qy (qb 0) (ym ht (qb 1))) hn PB
  (fun s i hi=>by
    rw [heq s i,zW,za,vy];rcases wh (n s) (t s) (um s) (F s) i with ⟨h1,h2,h3⟩
    have hsum:=by simpa only [smul_eq_mul,mul_one] using List.sum_le_length_nsmul _ 1 h3
    have hi':i≤n s:=by simpa [za] using hi
    have hPn0:=hPn s; have hPt0:=hPt s;simp only [PB,zO,z9,vT]; omega)
 exact zk (vv (qo h4)) (fun s=>by dsimp only; rw [za,heq,qk,zU]; rfl)
lemma wa (t cols:ℕ) (k:ℕ):
 let prev0:=(List.range cols).map (fun _=>qA t 0)
 let cur0:=(List.range cols).map (fun m=>if m=0 then qA t 1 else qA t 0);let p:=(vW t cols)^[k] (0,prev0,cur0)
 p.1=k∧p.2.1.length=cols∧p.2.2.length=cols∧
 (∀ v∈p.2.1,v.length=t∧∀ b∈v,b≤1)∧
 (∀ v∈p.2.2,v.length=t∧∀ b∈v,b≤1):=by
 induction k with
 | zero=>
   dsimp only [Function.iterate_zero_apply];refine ⟨rfl,by simp,by simp,?_,?_⟩
   · intro v hv; simp only [qQ] at hv; rcases hv with ⟨_,_,rfl⟩
     exact ⟨zl t 0,zS t 0⟩
   · intro v hv; simp only [qQ] at hv; rcases hv with ⟨_,_,rfl⟩
     split_ifs
     · exact ⟨zl t 1,zS t 1⟩
     · exact ⟨zl t 0,zS t 0⟩
 | succ k ih=>
   dsimp only;rcases ih with ⟨h1,h2,h3,h4,h5⟩
   rw [qM];dsimp only [vW];refine ⟨by omega,h3,by simp,h5,?_⟩
   intro v hv; simp only [qQ] at hv; rcases hv with ⟨m,_,rfl⟩
   split_ifs
   · exact ⟨zl t 1,zS t 1⟩
   · rcases kn _ _ t with ⟨hl,hb,_⟩
     exact ⟨hl,hb⟩
lemma kJ (t cols:ℕ) (S:Q2)
 (hSl:S.length=cols) (hSb:∀ v∈S,v.length=t∧∀ b∈v,b≤1):
 (zR S).length≤cols+4 * cols * t:=by
 have h1:=kp S
 have h2:(S.map (fun v=>v.length+v.sum)).sum≤cols * (2 * t):=by
  have hle:∀ x∈S.map (fun v=>v.length+v.sum),x≤2 * t:=by
   intro x hx; simp only [qQ] at hx; rcases hx with ⟨v,hv,rfl⟩
   rcases hSb v hv with ⟨hvl,hvb⟩
   have hs:=List.sum_le_length_nsmul v 1 hvb;simp only [smul_eq_mul,mul_one] at hs;omega
  have hs2:=List.sum_le_length_nsmul (S.map (fun v=>v.length+v.sum)) (2 * t) hle;simp only [zM,hSl,smul_eq_mul] at hs2;exact hs2
 nlinarith
lemma wY {t cols r:Q0→ℕ} {prev cur:Q0→Q2}
 (ht:qi t) (hcols:qi cols) (hr:qi r) (hprev:LLR prev) (hcur:LLR cur):
 LLR (fun s=>(List.range (cols s)).map (fun m=>
  if m=0 then qA (t s) 1
  else kI (t s) (gg (cur s) m) (kK (t s) (qA (t s) (r s)) (gg (prev s) (m-1))))):=
 qav (fun m s=>if m=0 then qA (t s) 1
  else kI (t s) (gg (cur s) m) (kK (t s) (qA (t s) (r s)) (gg (prev s) (m-1)))) hcols
  (yD qs (qb 0) (ym (qz ht) (qb 1)) (wj (qz ht) (vw (zK hcur) qs) (wk (qz ht) (ym (qz ht) (qz hr)) (vw (zK hprev) (yj qs (qb 1))))))
lemma qaS {t cols T:Q0→ℕ}
 (ht:qi t) (hcols:qi cols) (hT:qi T):
 LLR (fun s=>yC (t s) (cols s) (T s)):=by
 obtain ⟨Pt,hPt⟩:=z8 ht;obtain ⟨Pc,hPc⟩:=z8 hcols;obtain ⟨PT,hPT⟩:=z8 hT
 let Step:Q0→Q0:=fun z=>
  let st:=(Q9 z).1;let s:=(Q9 z).2;let r:=(Q9 st).1.length;let prev:=ko (Q9 (Q9 st).2).1;let cur:=ko (Q9 (Q9 st).2).2;let p:=vW (t s) (cols s) (r,prev,cur)
  qv (un p.1) (qv (zR p.2.1) (zR p.2.2))
 have h9:Lib.qF Step:=by
  have hr:=yY (qZ zz);have h0:=kZ (qZ (qo zz));have h8:=kZ (qo (qo zz));have h6:=wY (qz ht) (qz hcols) hr h0 h8
  exact zk (qy (q9 hr (qb 1)) (qy h8 h6)) (fun z=>by simp only [Step,vW])
 have ha:Lib.qF (fun s=>
  let prev0:=(List.range (cols s)).map (fun _=>qA (t s) 0);let cur0:=(List.range (cols s)).map (fun m=>if m=0 then qA (t s) 1 else qA (t s) 0)
  qv (un 0) (qv (zR prev0) (zR cur0))):=
  qy (qb 0)
   (qy (qav (fun _ s=>qA (t s) 0) hcols (ym (qz ht) (qb 0)))
     (qav (fun m s=>if m=0 then qA (t s) 1 else qA (t s) 0) hcols
       (yD qs (qb 0) (ym (qz ht) (qb 1)) (ym (qz ht) (qb 0)))))
 have heq:∀ s k,(fun a=>Step (qv a s))^[k]
  (qv (un 0) (qv (zR ((List.range (cols s)).map (fun _=>qA (t s) 0)))
    (zR ((List.range (cols s)).map (fun m=>if m=0 then qA (t s) 1 else qA (t s) 0)))))=
  let p:=(vW (t s) (cols s))^[k]
   (0,(List.range (cols s)).map (fun _=>qA (t s) 0),
     (List.range (cols s)).map (fun m=>if m=0 then qA (t s) 1 else qA (t s) 0))
  qv (un p.1) (qv (zR p.2.1) (zR p.2.2)):=by
  intro s k; induction k with
  | zero=>rfl
  | succ k ih=>rw [qM,qM,ih];simp only [Step,qk,za,yl]
 let PB:Q5:=Polynomial.C 2 * PT+Polynomial.C 4 * Pc+Polynomial.C 16 * Pc * Pt+Polynomial.C 10
 have h7:=y6 h9 ha hT PB (fun s i hi=>by
  rw [heq s i,zW,zW,za];rcases wa (t s) (cols s) i with ⟨h1,h2,h3,h4,h5⟩
  have hl1:=kJ (t s) (cols s) _ h2 h4;have hl2:=kJ (t s) (cols s) _ h3 h5;have hi':i≤T s:=by simpa [za] using hi
  have h1':=hPt s; have h2':=hPc s; have h3':=hPT s;have hmul:cols s * t s≤Pc.eval s.length * Pt.eval s.length:=Nat.mul_le_mul h2' h1';simp only [PB,zO,z9,vT]; nlinarith)
 exact zk (kZ (qo (qo h7))) (fun s=>by dsimp only; rw [za,heq,qk,qk,yl]; rfl)
def stepSt (st:Q0):Q0:=
 let hdr:=vK (Q9 st).1
 let n:=g hdr 0;let t:=g hdr 1;let done:=g hdr 2;let r1:=(Q9 st).2;let om:=vK (Q9 r1).1;let r2:=(Q9 r1).2;let C:=ko (Q9 r2).1;let r3:=(Q9 r2).2;let B:=ko (Q9 r3).1;let r4:=(Q9 r3).2;let idx:=vK (Q9 r4).1;let acc:=ko (Q9 r4).2
 if done=1 then
  false::((List.range (n / 2+1)).flatMap (fun s=>gg acc s)).map (fun a=>decide (a≠0))
 else
  let Srows:=y0 C idx
  let j:=Srows.length;let outF:=yU Srows;let uMask:=yX n om outF;let F0:=vU uMask B;let ps:=kD n uMask F0;let ok:=vH C.length idx * yu outF * (1-ps.dead) * (1-yT n ps.um ps.F)
  let acc':=
   if ok=1 then
    let nc:=kN n ps.um ps.F
    let nt:=kx n ps.um ps.F;let tp:=vS n t ps.um ps.F;let factor:=ke t (j+nc) tp;let mRow:=yC t (n / 2+1) nt;let shift:=C.length+j+ps.kF+ps.F.length
    (List.range (n / 2+1)).map (fun s=>
      if s<shift then gg acc s
      else kI t (gg acc s) (kK t factor (gg mRow (s-shift))))
   else acc
  let od:=kY C.length idx
  true::y4 [n,t,od.1] om od.2 C B acc'
lemma uZ (n:ℕ) (om outF:Q1):
 (yX n om outF).length=n∧∀ b∈yX n om outF,b≤1:=by
 refine ⟨by simp [yX],fun b hb=>?_⟩
 simp only [yX,qQ] at hb;rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
lemma qci {t cols shift:Q0→ℕ} {fac:Q0→Q1}
 {acc mRow:Q0→Q2}
 (ht:qi t) (hcols:qi cols) (hshift:qi shift) (hfac:qS fac)
 (hacc:LLR acc) (hmRow:LLR mRow):
 LLR (fun st=>(List.range (cols st)).map (fun s=>
  if s<shift st then gg (acc st) s
  else kI (t st) (gg (acc st) s) (kK (t st) (fac st) (gg (mRow st) (s-shift st))))):=
 qav (fun s st=>if s<shift st then gg (acc st) s
  else kI (t st) (gg (acc st) s) (kK (t st) (fac st) (gg (mRow st) (s-shift st)))) hcols
  (qbS qs (qz hshift) (vw (zK hacc) qs) (wj (qz ht) (vw (zK hacc) qs) (wk (qz ht) (zm hfac) (vw (zK hmRow) (yj qs (qz hshift))))))
lemma qbA {cols:Q0→ℕ} {acc:Q0→Q2}
 (hcols:qi cols) (hacc:LLR acc):
 qS (fun st=>(List.range (cols st)).flatMap (fun s=>gg (acc st) s)):=
 qcv (fun s st=>gg (acc st) s) hcols (vw (zK hacc) qs)
lemma qaX {ps:Q0→PeelSt} (hp:Lib.qF (fun st=>vQ (ps st))):
 qi (fun st=>(ps st).dead):=
 zk (qO (vv (qZ hp)) (qb 0)) (fun st=>by dsimp only; rw [vQ,qk,zU]; rfl)
lemma qbM {ps:Q0→PeelSt} (hp:Lib.qF (fun st=>vQ (ps st))):
 qi (fun st=>(ps st).kF):=
 zk (qO (vv (qZ hp)) (qb 1)) (fun st=>by dsimp only; rw [vQ,qk,zU]; rfl)
lemma qbT {ps:Q0→PeelSt} (hp:Lib.qF (fun st=>vQ (ps st))):
 qS (fun st=>(ps st).um):=
 zk (vv (qZ (qo hp))) (fun st=>by dsimp only; rw [vQ,qk,qk,zU])
lemma qcX {ps:Q0→PeelSt} (hp:Lib.qF (fun st=>vQ (ps st))):
 LLR (fun st=>(ps st).F):=
 zk (kZ (qo (qo hp))) (fun st=>by dsimp only; rw [vQ,qk,qk,yl])
lemma qdu {od:Q0→ℕ×Q1} (ho:Lib.qF (fun st=>qv (un (od st).1) (zn (od st).2))):
 qi (fun st=>(od st).1):=
 zk (yY (qZ ho)) (fun st=>by dsimp only; rw [qk,za])
lemma qdF {od:Q0→ℕ×Q1} (ho:Lib.qF (fun st=>qv (un (od st).1) (zn (od st).2))):
 qS (fun st=>(od st).2):=
 zk (vv (qo ho)) (fun st=>by dsimp only; rw [qk,zU])
lemma qce:Lib.qF stepSt:=by
 have h2:=vv zz;have hn:=qO h2 (qb 0);have ht:=qO h2 (qb 1);have hh:=qO h2 (qb 2);have hr1:=zA;have hom:=vv (qZ hr1);have hr2:=qo hr1;have hC:=kZ (qZ hr2);have hr3:=qo hr2;have hB:=kZ (qZ hr3);have hr4:=qo hr3;have he:=vv (qZ hr4);have h4:=kZ (qo hr4);have h3:=q9 (uo hn (qb 2)) (qb 1);have hg:=qbA h3 h4;have h6:=yB false (qcb hg);have h5:=qbo hC he;have hj:=vr h5;have ha:=qax h5;have h1:=qaZ hn hom ha;have hF0:=qaa h1 hB;have h0:=qbG hn h1 hF0 (fun st=>uZ _ _ _);have hc:=qaX h0;have hi:=qbM h0;have h8:=qbT h0;have hpF:=qcX h0
 have hok:=vn (vn (vn (qbs (vr hC) he) (qbr ha))
  (yj (qb 1) hc)) (yj (qb 1) (qcn hn h8 hpF))
 have hnc:=qbK hn h8 hpF;have hnt:=qbL hn h8 hpF;have htp:=qay hn ht h8 hpF;have hm:=qaK ht (q9 hj hnc) htp;have hf:=qaS ht h3 hnt;have hb:=q9 (q9 (q9 (vr hC) hj) hi) (vr hpF);have h9:=qci ht h3 hb hm h4 hf;have h4':=uI hok (qb 1) h9 h4;have hod:=qbF (vr hC) he;have hl:=qdu hod;have hk:=qdF hod;have h2':=zI (qT hn) (zI (qT ht) (qT hl));have h7:=yB true (qy h2' (qy hom (qy hC (qy hB (qy hk h4')))))
 exact zk (yQ hh (qb 1) h6 h7) (fun st=>by simp only [stepSt]; split_ifs <;> rfl)
end Alg
namespace ki
open PEqualNP.Library Lib.qC Lib.ve Lib.j4 Lib.R Alg jC
def qx (n:ℕ) (v:Q1):(Q3 n):=Finset.univ.filter (fun u=>u.val∈v)
def qL (n:ℕ) (m:Q1):(Q3 n):=Finset.univ.filter (fun u=>g m u.val=1)
def qR (n:ℕ) (L:Q2):(Q4 n):=(L.map (qx n)).toFinset
lemma zB {n:ℕ} {v:Q1} {u:Fin n}:u∈qx n v↔u.val∈v:=by simp [qx]
lemma q8 {n:ℕ} {m:Q1} {u:Fin n}:u∈qL n m↔g m u.val=1:=by simp [qL]
lemma zj {n:ℕ} {L:Q2} {R:(Q3 n)}:
 R∈qR n L↔∃ v∈L,qx n v=R:=by
 simp [qR]
lemma zF {n:ℕ} {v:Q1} (hnd:v.Nodup) (hlt:∀ a∈v,a<n):
 (qx n v).card=v.length:=by
 have h0:qx n v=(v.attach.map (fun a=>(⟨a.1,hlt a.1 a.2⟩:Fin n))).toFinset:=by
  ext u; simp only [zB,List.mem_toFinset,qQ,List.mem_attach,true_and,Subtype.exists];constructor
  · intro hu; exact ⟨u.val,hu,rfl⟩
  · rintro ⟨a,ha,rfl⟩; exact ha
 rw [h0,List.toFinset_card_of_nodup]
 · simp
 · refine (List.nodup_map_iff_inj_on (List.nodup_attach.mpr hnd)).mpr ?_
   intro x _ y _ hxy;exact Subtype.ext (congrArg Fin.val hxy)
lemma wx {n:ℕ} {m:Q1} (hl:m.length=n) (hb:∀ b∈m,b≤1):
 (qL n m).card=m.sum:=by
 have h1:(qL n m).card=∑ u:Fin n,g m u.val:=by
  rw [qL,Finset.card_filter];refine Finset.sum_congr rfl fun u _=>?_
  have hm:g m u.val≤1:=by
   have hu:u.val< m.length:=hl▸u.isLt;have:g m u.val=m[u.val]:=by simp [g,qf,hu]
   rw [this]; exact hb _ (qn hu)
  rcases (by omega:g m u.val=0∨g m u.val=1) with h|h <;> rw [h] <;> rfl
 rw [h1,Fin.sum_univ_eq_sum_range (fun i=>g m i) n]
 have h0:∀ k,k≤ m.length→∑ i∈Finset.range k,g m i=(m.take k).sum:=by
  intro k; induction k with
  | zero=>intro _; simp
  | succ k ih=>
    intro hk
    rw [Finset.sum_range_succ,ih (by omega),List.take_succ_eq_append_getElem (by omega),
     List.sum_append,List.sum_singleton]
    have:g m k=m[k]'(by omega):=by simp [g,qf,show k< m.length by omega]
    rw [this]
 rw [h0 n (by omega),show m.take n=m from vo (by omega)]
lemma jK {n:ℕ} {a b:Fin n}:qx n [a.val,b.val]={a,b}:=by ext u; simp [zB,Fin.ext_iff]
lemma k6 {n:ℕ} {a b c:Fin n}:qx n [a.val,b.val,c.val]={a,b,c}:=by ext u; simp [zB,Fin.ext_iff]
lemma yc {n:ℕ} {f:ℕ→ℕ} {u:Fin n}:
 g ((List.range n).map f) u.val=f u.val:=qbH n u.val f u.isLt
lemma qK {L:Q1} (hp:L.Pairwise (·<·)):L.Nodup:=hp.imp (fun h=>Nat.ne_of_lt h)
lemma vb {n:ℕ} {um R:Q1} (hRlt:∀ a∈R,a<n):
 qx n (zc um R)=qx n R ∩ qL n um∧
 (R.Pairwise (·<·)→(zc um R).Pairwise (·<·))∧
 (∀ a∈zc um R,a<n):=by
 have h3:∀ a,a∈zc um R↔a∈R∧g um a=1:=by
  intro a; simp only [zc,List.mem_flatMap,qw];constructor
  · rintro ⟨i,hi,h2⟩;split_ifs at h2 with h1
    · simp only [z4] at h2; subst h2;have hgi:g R i=R[i]:=by simp [g,qf,hi]
      exact ⟨hgi▸qn hi,h1⟩
    · simp at h2
  · rintro ⟨haR,hum⟩;rcases vI.mp haR with ⟨i,hi,rfl⟩
    have hgi:g R i=R[i]:=by simp [g,qf,hi]
    refine ⟨i,hi,?_⟩; rw [hgi,if_pos hum]; simp
 have h0:zc um R=R.filter (fun a=>decide (g um a=1)):=by
  have h4:∀ k,k≤R.length→
   (List.range k).flatMap (fun i=>if g um (g R i)=1 then [g R i] else [])=
     (R.take k).filter (fun a=>decide (g um a=1)):=by
   intro k; induction k with
   | zero=>intro _; simp
   | succ k ih=>
     intro hk
     rw [zP,List.flatMap_append,List.flatMap_singleton,ih (by omega),
      List.take_succ_eq_append_getElem (by omega),List.filter_append,List.filter_cons,
      List.filter_nil]
     have hgi:g R k=R[k]'(by omega):=by simp [g,qf,show k<R.length by omega]
     rw [hgi]; by_cases h:g um (R[k]'(by omega))=1 <;> simp [h]
  have:=h4 R.length le_rfl;rwa [List.take_length] at this
 refine ⟨?_,fun hp=>h0▸hp.filter _,fun a ha=>hRlt a (h3 a |>.mp ha).1⟩
 ext u; simp only [zB,qm,q8,h3]
lemma jY {n:ℕ} {H:(Q4 n)} {Hraw:Q2}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 (hTr:∀ u v w:Fin n,u≠v→u≠w→v≠w→(zZ Hraw u.val v.val w.val=1↔({u,v,w}:Q3 n)∈H)):
 let C:=yH n Hraw
 (∀ i<C.length,let row:=gg C i
   g row 0<g row 1∧g row 1<n∧g row 2<g row 3∧g row 3<n∧
   qx n [g row 0,g row 1]∈cores H∧
   outer H (qx n [g row 0,g row 1])=qx n [g row 2,g row 3])∧
 (∀ i<C.length,∀ j<C.length,qx n [g (gg C i) 0,g (gg C i) 1]=qx n [g (gg C j) 0,g (gg C j) 1]→i=j)∧
 (∀ c∈cores H,∃ i<C.length,qx n [g (gg C i) 0,g (gg C i) 1]=c)∧
 C.length=(cores H).card∧
 (yN n C).length=n∧(∀ b∈yN n C,b≤1)∧
 qL n (yN n C)=ordinary H:=by
 intro C
 have hg:∀ (a b:Fin n),a.val<b.val→
  (kj n Hraw a.val b.val).Pairwise (·<·)∧
  (∀ w,w∈kj n Hraw a.val b.val↔∃ u:Fin n,u.val=w∧u≠a∧u≠b∧({a,b,u}:Q3 n)∈H):=by
  intro a b hab;have hne:a≠b:=fun h=>by rw [h] at hab; exact Nat.lt_irrefl _ hab
  have hA:kj n Hraw a.val b.val=
   (List.range n).filter (fun w=>decide (w≠a.val∧w≠b.val∧zZ Hraw a.val b.val w=1)):=by
   have hW:∀ k,(List.range k).flatMap (fun w=>
    if w=a.val then [] else if w=b.val then [] else if zZ Hraw a.val b.val w=1 then [w] else [])=
    (List.range k).filter (fun w=>decide (w≠a.val∧w≠b.val∧zZ Hraw a.val b.val w=1)):=by
    intro k; induction k with
    | zero=>simp
    | succ k ih=>
      rw [zP,List.flatMap_append,List.flatMap_singleton,List.filter_append,List.filter_cons,List.filter_nil,ih]
      by_cases h1:k=a.val <;> by_cases h2:k=b.val <;> by_cases h3:zZ Hraw a.val b.val k=1 <;>
       simp [h1,h2,h3]
   exact hW n
  refine ⟨hA▸List.pairwise_lt_range.filter _,fun w=>?_⟩
  rw [hA,List.mem_filter,qw,decide_eq_true_eq];constructor
  · rintro ⟨hw,hwa,hwb,htr⟩;let u:Fin n:=⟨w,hw⟩;have hua:u≠a:=fun h=>hwa (congrArg Fin.val h)
    have hub:u≠b:=fun h=>hwb (congrArg Fin.val h)
    exact ⟨u,rfl,hua,hub,(hTr a b u hne hua.symm hub.symm).mp htr⟩
  · rintro ⟨u,rfl,hua,hub,h8⟩
    exact ⟨u.isLt,fun h=>hua (Fin.ext h),fun h=>hub (Fin.ext h),
     (hTr a b u hne hua.symm hub.symm).mpr h8⟩
 have hf:∀ row,row∈C↔∃ (a b x y:Fin n),a.val<b.val∧x.val<y.val∧
  row=[a.val,b.val,x.val,y.val]∧({a,b}:Q3 n)∈cores H∧
  outer H {a,b}={x,y}:=by
  intro row;simp only [C,yH,List.mem_flatMap,qw];constructor
  · rintro ⟨a,ha,b,hb,hn⟩;split_ifs at hn with hab hlen
    · simp only [z4] at hn;set af:Fin n:=⟨a,ha⟩;set bf:Fin n:=⟨b,hb⟩;have hne:af≠bf:=fun h=>Nat.ne_of_lt hab (congrArg Fin.val h)
      rcases hg af bf hab with ⟨hpw,h8⟩
      set os:=kj n Hraw a b;rcases List.length_eq_two.mp hlen with ⟨x,y,hos⟩
      rw [hos] at hpw;have hxy:x<y:=by simpa [List.pairwise_cons] using hpw
      have hI:=(h8 x).mp (by rw [hos]; simp);have hH:=(h8 y).mp (by rw [hos]; simp);rcases hI with ⟨xf,rfl,hxa,hxb,hxH⟩
      rcases hH with ⟨yf,rfl,hya,hyb,hyH⟩
      have hB:xf≠yf:=fun h=>Nat.ne_of_lt hxy (congrArg Fin.val h)
      have h00:({af,bf,xf}:Q3 n)≠{af,bf,yf}:=by
       intro h; have:xf∈({af,bf,yf}:Q3 n):=h▸by simp
       simp only [qe,qd] at this;rcases this with h1|h1|h1
       · exact hxa h1
       · exact hxb h1
       · exact hB h1
      have hF:({af,bf,xf}:Q3 n) ∩ {af,bf,yf}={af,bf}:=by
       ext u; simp only [qm,qe,qd];constructor
       · rintro ⟨rfl|rfl|rfl,h2⟩
         · exact Or.inl rfl
         · exact Or.inr rfl
         · rcases h2 with h2|h2|h2
           · exact absurd h2 hxa
           · exact absurd h2 hxb
           · exact absurd h2 hB
       · rintro (rfl|rfl) <;> simp
      have h7:({af,bf}:Q3 n)∈cores H:=(zq hH3).mpr ⟨zv hne,_,hxH,_,hyH,h00,hF⟩
      have hs:row=[af.val,bf.val,xf.val,yf.val]:=by rw [hn,hos]; simp [g,af,bf]
      have ht:outer H {af,bf}={xf,yf}:=by
       rcases vP hH3 hdeg h7 with ⟨p,q,hpq,_,_,h5,hk⟩
       have h1:({af,bf,xf}:Q3 n)∈zX H {af,bf}:=qa.mpr ⟨hxH,fun u hu=>by simp only [qe,qd] at hu ⊢; rcases hu with rfl|rfl <;> simp⟩
       have h2:({af,bf,yf}:Q3 n)∈zX H {af,bf}:=qa.mpr ⟨hyH,fun u hu=>by simp only [qe,qd] at hu ⊢; rcases hu with rfl|rfl <;> simp⟩
       have hT:({xf,yf}:Q3 n)⊆outer H {af,bf}:=by
        intro u hu; simp only [qe,qd] at hu;simp only [outer,qg,qj,id_eq];rcases hu with rfl|rfl
        · exact ⟨⟨_,h1,by simp⟩,by simp [hxa,hxb]⟩
        · exact ⟨⟨_,h2,by simp⟩,by simp [hya,hyb]⟩
       exact (zo hT
        (by rw [zv hB,jx hH3 hdeg h7])).symm
      exact ⟨af,bf,xf,yf,hab,hxy,hs,h7,ht⟩
    · simp at hn
    · simp at hn
  · rintro ⟨a,b,x,y,hab,hxy,rfl,h7,h5⟩;refine ⟨a.val,a.isLt,b.val,b.isLt,?_⟩
    rw [if_pos hab];rcases hg a b hab with ⟨hpw,h8⟩
    set os:=kj n Hraw a.val b.val;have h6:Disjoint ({a,b}:Q3 n) (outer H {a,b}):=Finset.disjoint_sdiff;have hxa:x≠a:=fun h=>qc.mp h6 (by simp:a∈({a,b}:Q3 n)) (by rw [h5,← h]; simp)
    have hxb:x≠b:=fun h=>qc.mp h6 (by simp:b∈({a,b}:Q3 n)) (by rw [h5,← h]; simp)
    have hya:y≠a:=fun h=>qc.mp h6 (by simp:a∈({a,b}:Q3 n)) (by rw [h5,← h]; simp)
    have hyb:y≠b:=fun h=>qc.mp h6 (by simp:b∈({a,b}:Q3 n)) (by rw [h5,← h]; simp)
    have h9:∀ w,w∈os↔w=x.val∨w=y.val:=by
     intro w; rw [h8];constructor
     · rintro ⟨u,rfl,hua,hub,huH⟩
       have huo:u∈outer H {a,b}:=by
        simp only [outer,qg,qj,id_eq,qa]
        exact ⟨⟨{a,b,u},⟨huH,fun z hz=>by simp only [qe,qd] at hz ⊢; rcases hz with rfl|rfl <;> simp⟩,by simp⟩,
         by simp [hua,hub]⟩
       rw [h5] at huo; simp only [qe,qd] at huo;rcases huo with rfl|rfl; exact Or.inl rfl; exact Or.inr rfl
     · rintro (rfl|rfl)
       · rcases vP hH3 hdeg h7 with ⟨p,q,_,_,_,ho,hk⟩
         have hS:x=p∨x=q:=by
          have:x∈({p,q}:Q3 n):=ho▸h5▸by simp
          simpa using this
         have hxR:insert x {a,b}∈zX H {a,b}:=by rw [hk]; rcases hS with rfl|rfl <;> simp
         have hq:({a,b,x}:Q3 n)=insert x {a,b}:=by ext z; simp; tauto
         exact ⟨x,rfl,hxa,hxb,hq▸(qa.mp hxR).1⟩
       · rcases vP hH3 hdeg h7 with ⟨p,q,_,_,_,ho,hk⟩
         have hQ:y=p∨y=q:=by
          have:y∈({p,q}:Q3 n):=ho▸h5▸by simp
          simpa using this
         have hyR:insert y {a,b}∈zX H {a,b}:=by rw [hk]; rcases hQ with rfl|rfl <;> simp
         have hq:({a,b,y}:Q3 n)=insert y {a,b}:=by ext z; simp; tauto
         exact ⟨y,rfl,hya,hyb,hq▸(qa.mp hyR).1⟩
    have hp:os=[x.val,y.val]:=by
     have hnd:os.Nodup:=qK hpw
     have hM:os.toFinset={x.val,y.val}:=by ext w; simp [h9]
     have hK:os.length=2:=by rw [← List.toFinset_card_of_nodup hnd,hM,zv (Nat.ne_of_lt hxy)]
     rcases List.length_eq_two.mp hK with ⟨u₁,u₂,hu⟩
     rw [hu] at hpw;have hlt:u₁<u₂:=by simpa [List.pairwise_cons] using hpw
     have hu1:=(h9 u₁).mp (by rw [hu]; simp);have hu2:=(h9 u₂).mp (by rw [hu]; simp);rcases hu1 with rfl|rfl <;> rcases hu2 with rfl|rfl
     · omega
     · exact hu
     · omega
     · omega
    rw [if_pos (by rw [hp]; rfl),hp]; simp [g]
 have hP:C.Nodup:=by
  have hl:∀ a,((List.range n).flatMap (fun b=>
   if a<b then let os:=kj n Hraw a b; if os.length=2 then [[a,b,g os 0,g os 1]] else [] else [])).Nodup:=by
   intro a;rw [List.nodup_flatMap];refine ⟨fun b _=>by dsimp only; split_ifs <;> simp,?_⟩
   refine List.pairwise_lt_range.imp_of_mem ?_
   intro b₁ _ b₂ _ hlt row h1 h2;dsimp only at h1 h2;split_ifs at h1 <;> split_ifs at h2 <;> simp only [z4,List.not_mem_nil] at h1 h2
   have:=h1.symm.trans h2;simp only [List.cons.injEq] at this;omega
  change (yH n Hraw).Nodup; unfold yH; rw [List.nodup_flatMap];refine ⟨fun a _=>hl a,?_⟩
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro a₁ _ a₂ _ hlt row h1 h2;simp only [List.mem_flatMap,qw] at h1 h2;rcases h1 with ⟨b₁,_,h1⟩; rcases h2 with ⟨b₂,_,h2⟩
  split_ifs at h1 <;> split_ifs at h2 <;> simp only [z4,List.not_mem_nil] at h1 h2
  have:=h1.symm.trans h2;simp only [List.cons.injEq] at this;omega
 have h4:∀ i<C.length,let row:=gg C i
  g row 0<g row 1∧g row 1<n∧g row 2<g row 3∧g row 3<n∧
  qx n [g row 0,g row 1]∈cores H∧
  outer H (qx n [g row 0,g row 1])=qx n [g row 2,g row 3]:=by
  intro i hi; dsimp only;have hgg:gg C i=C[i]:=by simp [gg,qf,hi]
  rw [hgg];rcases (hf C[i]).mp (qn hi) with ⟨a,b,x,y,hab,hxy,hD,h7,h5⟩
  rw [hD]; simp only [g,List.getD_cons_zero,List.getD_cons_succ,jK];exact ⟨hab,b.isLt,hxy,y.isLt,h7,h5⟩
 have hL:∀ i<C.length,∀ j<C.length,
  qx n [g (gg C i) 0,g (gg C i) 1]=qx n [g (gg C j) 0,g (gg C j) 1]→i=j:=by
  intro i hi j hj heq;have hV:gg C i=C[i]:=by simp [gg,qf,hi]
  have hU:gg C j=C[j]:=by simp [gg,qf,hj]
  rw [hV] at heq; rw [hU] at heq;rcases (hf C[i]).mp (qn hi) with ⟨a₁,b₁,x₁,y₁,hG,hC,hri,hci,hoi⟩
  rcases (hf C[j]).mp (qn hj) with ⟨a₂,b₂,x₂,y₂,hZ,hR,hrj,hcj,hoj⟩
  rw [hri,hrj] at heq;simp only [g,List.getD_cons_zero,List.getD_cons_succ,jK] at heq
  have he:a₁=a₂∧b₁=b₂:=by
   have ha1:a₁∈({a₂,b₂}:Q3 n):=heq▸by simp
   have hb1:b₁∈({a₂,b₂}:Q3 n):=heq▸by simp
   simp only [qe,qd] at ha1 hb1;rcases ha1 with rfl|rfl <;> rcases hb1 with rfl|rfl
   · exact absurd hG (Nat.lt_irrefl _)
   · exact ⟨rfl,rfl⟩
   · exact absurd (hG.trans hZ) (Nat.lt_irrefl _)
   · exact absurd hG (Nat.lt_irrefl _)
  rcases he with ⟨rfl,rfl⟩
  have hy:({x₁,y₁}:Q3 n)={x₂,y₂}:=hoi.symm.trans hoj
  have hh:x₁=x₂∧y₁=y₂:=by
   have hx1:x₁∈({x₂,y₂}:Q3 n):=hy▸by simp
   have hy1:y₁∈({x₂,y₂}:Q3 n):=hy▸by simp
   simp only [qe,qd] at hx1 hy1;rcases hx1 with rfl|rfl <;> rcases hy1 with rfl|rfl
   · exact absurd hC (Nat.lt_irrefl _)
   · exact ⟨rfl,rfl⟩
   · exact absurd (hC.trans hR) (Nat.lt_irrefl _)
   · exact absurd hC (Nat.lt_irrefl _)
  rcases hh with ⟨rfl,rfl⟩
  have hO:C[i]=C[j]:=hri.trans hrj.symm;exact (List.Nodup.getElem_inj_iff hP).mp hO
 have hm:∀ c∈cores H,∃ i<C.length,qx n [g (gg C i) 0,g (gg C i) 1]=c:=by
  intro c hc;have hcc:c.card=2:=((zq hH3).mp hc).1;rcases yk.mp hcc with ⟨a,b,hab,rfl⟩
  rcases vP hH3 hdeg hc with ⟨x,y,hxy,_,_,h5,_⟩
  have hv:∀ p q:Fin n,p≠q→∃ p' q':Fin n,p'.val<q'.val∧({p,q}:Q3 n)={p',q'}:=by
   intro p q hpq;by_cases h:p.val<q.val
   · exact ⟨p,q,h,rfl⟩
   · exact ⟨q,p,Nat.lt_of_le_of_ne (yt h) (fun e=>hpq (Fin.ext e.symm)),Finset.pair_comm p q⟩
  rcases hv a b hab with ⟨a',b',hab',he⟩
  rcases hv x y hxy with ⟨x',y',hxy',hh⟩
  rw [he] at hc h5;rw [hh] at h5
  have h8:[a'.val,b'.val,x'.val,y'.val]∈C:=(hf _).mpr ⟨a',b',x',y',hab',hxy',rfl,hc,h5⟩
  rcases vI.mp h8 with ⟨i,hi,heq⟩
  refine ⟨i,hi,?_⟩
  have hgg:gg C i=C[i]:=by simp [gg,qf,hi]
  rw [hgg,heq]; simp [g,jK,he]
 have hN:C.length=(cores H).card:=by
  have hX:(Finset.range C.length).card=(cores H).card:=by
   refine Finset.card_nbij (fun i=>qx n [g (gg C i) 0,g (gg C i) 1]) ?_ ?_ ?_
   · intro i hi; exact (h4 i (vi.mp hi)).2.2.2.2.1
   · intro i hi j hj heq; exact hL i (vi.mp hi) j (vi.mp hj) heq
   · intro c hc; rcases hm c hc with ⟨i,hi,heq⟩; exact ⟨i,vi.mpr hi,heq⟩
  simpa using hX
 have hJ:∀ b∈yN n C,b≤1:=by intro b hb; simp only [yN,qQ] at hb; rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
 have hE:qL n (yN n C)=ordinary H:=by
  ext u; simp only [q8,yN,yc,ordinary,qg,qJ,true_and,qj,id_eq]
  have hx:((List.range C.length).map (fun r=>
   (if g (gg C r) 0=u.val then 1 else 0)+(if g (gg C r) 1=u.val then 1 else 0))).sum=0↔
   ¬ ∃ c∈cores H,u∈c:=by
   constructor
   · intro h0 ⟨c,hc,huc⟩;rcases hm c hc with ⟨r,hr,hD⟩
     rw [← hD,zB,zT,z4] at huc
     have hpos:1≤(if g (gg C r) 0=u.val then 1 else 0)+(if g (gg C r) 1=u.val then 1 else 0):=by
      rcases huc with h1|h1
      · rw [← h1]; split_ifs <;> omega
      · rw [← h1]; split_ifs <;> omega
     have h8:(if g (gg C r) 0=u.val then 1 else 0)+(if g (gg C r) 1=u.val then 1 else 0)∈
      (List.range C.length).map (fun r=>(if g (gg C r) 0=u.val then 1 else 0)+(if g (gg C r) 1=u.val then 1 else 0)):=
      qQ.mpr ⟨r,qw.mpr hr,rfl⟩
     have hle:=List.le_sum_of_mem h8;omega
   · intro hno
     have hY:∀ r∈List.range C.length,
      (if g (gg C r) 0=u.val then 1 else 0)+(if g (gg C r) 1=u.val then 1 else 0)=0:=by
      intro r hr;have hrl:r<C.length:=qw.mp hr;have hc:=(h4 r hrl).2.2.2.2.1;have h1:g (gg C r) 0≠u.val:=fun e=>hno ⟨_,hc,zB.mpr (by rw [← e]; simp)⟩
      have h2:g (gg C r) 1≠u.val:=fun e=>hno ⟨_,hc,zB.mpr (by rw [← e]; simp)⟩
      rw [if_neg h1,if_neg h2]
     rw [List.map_congr_left hY,List.map_const',List.sum_replicate,smul_eq_mul,mul_zero]
  split_ifs with h0
  · simp [hx.mp h0]
  · simp [hx.not.mp h0]
 exact ⟨h4,hL,hm,hN,by simp [yN],hJ,hE⟩
lemma jX {n:ℕ} {H:(Q4 n)} {Hraw:Q2} {om:Q1}
 (hH3:∀ R∈H,R.card=3)
 (hTr:∀ u v w:Fin n,u≠v→u≠w→v≠w→(zZ Hraw u.val v.val w.val=1↔({u,v,w}:Q3 n)∈H))
 (hom_b:∀ b∈om,b≤1)
 (hom_eq:qL n om=ordinary H):
 let B:=kt n Hraw om
 (∀ R∈B,R.Pairwise (·<·)∧R.length=3∧(∀ a∈R,a<n)∧qx n R∈base H)∧
 B.Nodup∧qR n B=base H∧B.length=(base H).card:=by
 intro B
 have h5:∀ row,row∈B↔∃ (u v w:Fin n),u.val<v.val∧v.val<w.val∧
  row=[u.val,v.val,w.val]∧({u,v,w}:Q3 n)∈base H:=by
  intro row; simp only [B,kt,List.mem_flatMap,qw];constructor
  · rintro ⟨u,hu,v,hv,h1⟩;split_ifs at h1 with huv
    · simp only [List.mem_flatMap,qw] at h1;rcases h1 with ⟨w,hw,h2⟩
      split_ifs at h2 with hvw hprod
      · simp only [z4] at h2;let uf:Fin n:=⟨u,hu⟩; let vf:Fin n:=⟨v,hv⟩; let wf:Fin n:=⟨w,hw⟩;have huv':uf≠vf:=fun e=>Nat.ne_of_lt huv (congrArg Fin.val e)
        have huw':uf≠wf:=fun e=>Nat.ne_of_lt (huv.trans hvw) (congrArg Fin.val e)
        have hvw':vf≠wf:=fun e=>Nat.ne_of_lt hvw (congrArg Fin.val e)
        have h4:g om u=1∧g om v=1∧g om w=1∧zZ Hraw u v w=1:=by
         have ha:g om u≤1:=by
          by_cases hl:u<om.length
          · have:g om u=om[u]:=by simp [g,qf,hl]
            rw [this]; exact hom_b _ (qn hl)
          · simp [g,qf,List.getElem?_eq_none (yt hl)]
         have hb:g om v≤1:=by
          by_cases hl:v<om.length
          · have:g om v=om[v]:=by simp [g,qf,hl]
            rw [this]; exact hom_b _ (qn hl)
          · simp [g,qf,List.getElem?_eq_none (yt hl)]
         have hc:g om w≤1:=by
          by_cases hl:w<om.length
          · have:g om w=om[w]:=by simp [g,qf,hl]
            rw [this]; exact hom_b _ (qn hl)
          · simp [g,qf,List.getElem?_eq_none (yt hl)]
         have hd:zZ Hraw u v w≤1:=by simp only [zZ]; split_ifs <;> omega
         rcases (by omega:g om u=0∨g om u=1) with h0|h1 <;>
         rcases (by omega:g om v=0∨g om v=1) with h0'|h1' <;>
         rcases (by omega:g om w=0∨g om w=1) with h0''|h1'' <;>
         rcases (by omega:zZ Hraw u v w=0∨zZ Hraw u v w=1) with h0'''|h1''' <;>
          simp_all
        have hH:({uf,vf,wf}:Q3 n)∈H:=(hTr uf vf wf huv' huw' hvw').mp h4.2.2.2
        have h8:({uf,vf,wf}:Q3 n)⊆ordinary H:=by
         intro z hz; rw [← hom_eq,q8];simp only [qe,qd] at hz;rcases hz with rfl|rfl|rfl
         · exact h4.1
         · exact h4.2.1
         · exact h4.2.2.1
        exact ⟨uf,vf,wf,huv,hvw,h2,qa.mpr ⟨hH,h8⟩⟩
      · simp at h2
      · simp at h2
    · simp at h1
  · rintro ⟨u,v,w,huv,hvw,rfl,hh⟩;rcases qa.mp hh with ⟨hH,h8⟩
    have huv':u≠v:=fun e=>Nat.ne_of_lt huv (congrArg Fin.val e)
    have huw':u≠w:=fun e=>Nat.ne_of_lt (huv.trans hvw) (congrArg Fin.val e)
    have hvw':v≠w:=fun e=>Nat.ne_of_lt hvw (congrArg Fin.val e)
    have hgu:g om u.val=1:=q8.mp (hom_eq.symm▸h8 (by simp));have hgv:g om v.val=1:=q8.mp (hom_eq.symm▸h8 (by simp));have hgw:g om w.val=1:=q8.mp (hom_eq.symm▸h8 (by simp));have htr:zZ Hraw u.val v.val w.val=1:=(hTr u v w huv' huw' hvw').mpr hH;refine ⟨u.val,u.isLt,v.val,v.isLt,?_⟩
    rw [if_pos huv];refine List.mem_flatMap.mpr ⟨w.val,qw.mpr w.isLt,?_⟩
    rw [if_pos hvw,hgu,hgv,hgw,htr]; simp
 have he:B.Nodup:=by
  change (kt n Hraw om).Nodup; unfold kt; rw [List.nodup_flatMap];refine ⟨fun u _=>?_,?_⟩
  · rw [List.nodup_flatMap];refine ⟨fun v _=>?_,?_⟩
    · split_ifs
      · rw [List.nodup_flatMap];refine ⟨fun w _=>by split_ifs <;> simp,?_⟩
        refine List.pairwise_lt_range.imp_of_mem ?_
        intro w₁ _ w₂ _ hlt row h1 h2;dsimp only at h1 h2;split_ifs at h1 <;> split_ifs at h2 <;> simp only [z4,List.not_mem_nil] at h1 h2
        have:=h1.symm.trans h2; simp only [List.cons.injEq] at this; omega
      · simp
    · refine List.pairwise_lt_range.imp_of_mem ?_
      intro v₁ _ v₂ _ hlt row h1 h2;dsimp only at h1 h2;split_ifs at h1 <;> split_ifs at h2 <;> simp only [List.not_mem_nil,List.mem_flatMap,qw] at h1 h2
      rcases h1 with ⟨w₁,_,h1⟩; rcases h2 with ⟨w₂,_,h2⟩
      split_ifs at h1 <;> split_ifs at h2 <;> simp only [z4,List.not_mem_nil] at h1 h2
      have:=h1.symm.trans h2; simp only [List.cons.injEq] at this; omega
  · refine List.pairwise_lt_range.imp_of_mem ?_
    intro u₁ _ u₂ _ hlt row h1 h2;dsimp only at h1 h2;simp only [List.mem_flatMap,qw] at h1 h2;rcases h1 with ⟨v₁,_,h1⟩; rcases h2 with ⟨v₂,_,h2⟩
    split_ifs at h1 <;> split_ifs at h2 <;> simp only [List.not_mem_nil,List.mem_flatMap,qw] at h1 h2
    rcases h1 with ⟨w₁,_,h1⟩; rcases h2 with ⟨w₂,_,h2⟩
    split_ifs at h1 <;> split_ifs at h2 <;> simp only [z4,List.not_mem_nil] at h1 h2
    have:=h1.symm.trans h2; simp only [List.cons.injEq] at this; omega
 have h6:∀ R∈B,R.Pairwise (·<·)∧R.length=3∧(∀ a∈R,a<n)∧qx n R∈base H:=by
  intro R hR;rcases (h5 R).mp hR with ⟨u,v,w,huv,hvw,rfl,hb⟩
  refine ⟨by simp [huv,hvw,huv.trans hvw],rfl,fun a ha=>?_,k6▸hb⟩
  simp only [zT,List.not_mem_nil,or_false] at ha;rcases ha with rfl|rfl|rfl; exact u.isLt; exact v.isLt; exact w.isLt
 have h9:qR n B=base H:=by
  ext R; simp only [zj];constructor
  · rintro ⟨v,hv,rfl⟩; exact (h6 v hv).2.2.2
  · intro hRb;have hR3:R.card=3:=hH3 R (qa.mp hRb).1;rcases Finset.card_eq_three.mp hR3 with ⟨a,b,c,hab,hac,hbc,rfl⟩
    have hf:∃ u v w:Fin n,u.val<v.val∧v.val<w.val∧
     ({a,b,c}:Q3 n)={u,v,w}:=by
     have h1:a.val≠b.val:=fun e=>hab (Fin.ext e)
     have h2:a.val≠c.val:=fun e=>hac (Fin.ext e)
     have h3:b.val≠c.val:=fun e=>hbc (Fin.ext e)
     rcases lt_or_gt_of_ne h1 with ho|hm <;>
     rcases lt_or_gt_of_ne h2 with hn|hj <;>
     rcases lt_or_gt_of_ne h3 with hk|hi
     · exact ⟨a,b,c,ho,hk,rfl⟩
     · exact ⟨a,c,b,hn,hi,by ext z; simp; tauto⟩
     · omega
     · exact ⟨c,a,b,hj,ho,by ext z; simp; tauto⟩
     · exact ⟨b,a,c,hm,hn,by ext z; simp; tauto⟩
     · omega
     · exact ⟨b,c,a,hk,hj,by ext z; simp; tauto⟩
     · exact ⟨c,b,a,hi,hm,by ext z; simp; tauto⟩
    rcases hf with ⟨u,v,w,huv,hvw,heq⟩
    rw [heq] at hRb
    exact ⟨[u.val,v.val,w.val],(h5 _).mpr ⟨u,v,w,huv,hvw,rfl,hRb⟩,
     by rw [k6,← heq]⟩
 have hg:B.length=(base H).card:=by
  rw [← h9,qR,List.toFinset_card_of_nodup]
  · simp
  · refine (List.nodup_map_iff_inj_on he).mpr fun r₁ hr₁ r₂ hr₂ heq=>?_
    rcases (h5 r₁).mp hr₁ with ⟨u₁,v₁,w₁,h1,h2,rfl,_⟩
    rcases (h5 r₂).mp hr₂ with ⟨u₂,v₂,w₂,h3,h4,rfl,_⟩
    rw [k6,k6] at heq
    have h7:∀ x:Fin n,(x=u₁∨x=v₁∨x=w₁)↔(x=u₂∨x=v₂∨x=w₂):=fun x=>by simpa [Finset.ext_iff] using congrFun (congrArg Membership.mem heq) x
    have hu1:=(h7 u₁).mp (Or.inl rfl);have hv1:=(h7 v₁).mp (Or.inr (Or.inl rfl));have hw1:=(h7 w₁).mp (Or.inr (Or.inr rfl));have hu2:=(h7 u₂).mpr (Or.inl rfl);have hv2:=(h7 v₂).mpr (Or.inr (Or.inl rfl));have hw2:=(h7 w₂).mpr (Or.inr (Or.inr rfl))
    have e1:u₁.val=u₂.val:=by
     have hle1:u₁.val≤u₂.val:=by rcases hu2 with e|e|e <;> rw [e] <;> omega
     have hle2:u₂.val≤u₁.val:=by rcases hu1 with e|e|e <;> rw [e] <;> omega
     omega
    have e3:w₁.val=w₂.val:=by
     have hge1:w₂.val≤w₁.val:=by rcases hw2 with e|e|e <;> rw [e] <;> omega
     have hge2:w₁.val≤w₂.val:=by rcases hw1 with e|e|e <;> rw [e] <;> omega
     omega
    have e2:v₁.val=v₂.val:=by rcases hv1 with rfl|rfl|rfl <;> omega
    simp [e1,e2,e3]
 exact ⟨h6,he,h9,hg⟩
def zb (b:ℕ):Q1→ℕ
 | []=>0
 | d::ds=>d+b * zb b ds
def zL (b:ℕ):ℕ→ℕ→Q1
 | 0,_=>[]
 | k+1,v=>(v % b)::zL b k (v / b)
lemma kH (b:ℕ) (u v:Q1):
 zb b (u++v)=zb b u+b ^ u.length * zb b v:=by
 induction u with
 | nil=>simp [zb]
 | cons d u ih=>simp only [List.cons_append,zb,qI,ih,pow_succ]; ring
lemma kL (b:ℕ) (u:Q1) (k:ℕ):
 zb b (u.take (k+1))=zb b (u.take k)+b ^ k * g u k:=by
 by_cases hk:k<u.length
 · rw [List.take_succ_eq_append_getElem hk,kH,List.length_take_of_le (by omega),
    zb,zb]
   have hg:g u k=u[k]:=by simp [g,qf,hk]
   rw [hg]; ring
 · rw [vo (by omega),vo (yt hk)];have hg:g u k=0:=by simp [g,qf,List.getElem?_eq_none (yt hk)]
   rw [hg]; simp
lemma kk (b k v:ℕ) (hb:0<b):
 (zL b k v).length=k∧(∀ d∈zL b k v,d<b)∧
 (v<b ^ k→zb b (zL b k v)=v):=by
 induction k generalizing v with
 | zero=>
   refine ⟨rfl,by simp [zL],fun hv=>?_⟩
   simp at hv; simp [zL,zb,hv]
 | succ k ih=>
   rcases ih (v / b) with ⟨hl,hd,hv'⟩
   refine ⟨by simp [zL,hl],?_,fun hv=>?_⟩
   · intro d hdm; simp only [zL,zT] at hdm;rcases hdm with rfl|h1
     · exact Nat.mod_lt v hb
     · exact hd d h1
   · simp only [zL,zb]
     have h0:v / b<b ^ k:=by rw [Nat.div_lt_iff_lt_mul hb]; simpa [pow_succ,mul_comm] using hv
     rw [hv' h0,Nat.mod_add_div]
lemma kE (b:ℕ) (u:Q1) (hb:0<b) (hd:∀ d∈u,d<b):
 zL b u.length (zb b u)=u:=by
 induction u with
 | nil=>rfl
 | cons d u ih=>
   simp only [qI,zL,zb];have hd0:d<b:=hd d (by simp)
   have h0:(d+b * zb b u) % b=d:=by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd0]
   have h1:(d+b * zb b u) / b=zb b u:=by rw [Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt hd0,zero_add]
   rw [h0,h1,ih (fun x hx=>hd x (by simp [hx]))]
lemma jq (b k:ℕ):zL b k 0=(List.range k).map (fun _=>0):=by
 induction k with
 | zero=>rfl
 | succ k ih=>rw [zL,Nat.zero_mod,Nat.zero_div,ih,List.range_succ_eq_map,List.map_cons,List.map_map];rfl
lemma qbj (m k q:ℕ) (hq:q<(m+1) ^ k):
 kY m (zL (m+1) k q)=if q+1<(m+1) ^ k then (0,zL (m+1) k (q+1))
  else (1,(List.range k).map (fun _=>0)):=by
 set idx:=zL (m+1) k q;rcases kk (m+1) k q (Nat.succ_pos m) with ⟨h5,hbd,h6⟩
 have h8:idx.length=k:=h5
 have h9:∀ l,l≤k→
  let p:=(zx m idx)^[l] (1,[])
  p.1≤1∧p.2.length=l∧(∀ d∈p.2,d≤ m)∧
  zb (m+1) p.2+(m+1) ^ l * p.1=zb (m+1) (idx.take l)+1:=by
  intro l; induction l with
  | zero=>intro _; simp [zb]
  | succ l ih=>
    intro hl;rcases ih (by omega) with ⟨hc,hl',hbd',hv'⟩
    rw [qM];dsimp only [zx];set p:=(zx m idx)^[l] (1,[]);have hdl:l< idx.length:=by omega
    have hgd:g idx l< m+1:=by
     have:g idx l=idx[l]:=by simp [g,qf,hdl]
     rw [this]; exact hbd _ (qn hdl)
    rw [hl'];split_ifs with h1 h2
    · refine ⟨by omega,by simp [hl'],?_,?_⟩
      · intro d hd; simp only [List.mem_append,z4] at hd;rcases hd with hd1|rfl; exact hbd' d hd1; omega
      · rw [kH,hl',zb,zb,mul_zero,add_zero,mul_zero,add_zero,kL];rw [h1,mul_zero,add_zero] at hv'; rw [hv']; ring
    · have hp1:p.1=1:=by omega
      refine ⟨by omega,by simp [hl'],?_,?_⟩
      · intro d hd; simp only [List.mem_append,z4] at hd;rcases hd with hd1|rfl; exact hbd' d hd1; omega
      · rw [kH,hl',zb,zb,mul_zero,add_zero,mul_zero,add_zero,kL];rw [hp1,mul_one] at hv'; linarith
    · have hp1:p.1=1:=by omega
      have hdm:g idx l=m:=by omega
      refine ⟨by omega,by simp [hl'],?_,?_⟩
      · intro d hd; simp only [List.mem_append,z4] at hd;rcases hd with hd1|rfl; exact hbd' d hd1; omega
      · rw [kH,hl',zb,zb,mul_zero,add_zero,mul_zero,add_zero,mul_one,kL,hdm,pow_succ];rw [hp1,mul_one] at hv'; linarith
 rcases h9 k le_rfl with ⟨hc,hpl,h3,h0⟩
 have h4:idx.take k=idx:=vo (by omega);rw [h4,h6 hq] at h0
 have hlt_out:zb (m+1) ((zx m idx)^[k] (1,[])).2<(m+1) ^ k:=by
  have hb:∀ u:Q1,(∀ d∈u,d< m+1)→zb (m+1) u<(m+1) ^ u.length:=by
   intro u; induction u with
   | nil=>intro _; simp [zb]
   | cons d u ih=>
     intro hu; simp only [zb,qI,pow_succ];have hd0:d< m+1:=hu d (by simp);have hu0:=ih (fun x hx=>hu x (by simp [hx]));have h1:(m+1) * zb (m+1) u+d<(m+1) * zb (m+1) u+(m+1):=by omega
     have h2:(m+1) * (zb (m+1) u+1)≤(m+1) * (m+1) ^ u.length:=Nat.mul_le_mul_left _ hu0
     nlinarith
  have:=hb _ (fun d hd=>Nat.lt_succ_of_le (h3 d hd));rwa [hpl] at this
 have ha:kY m idx=(zx m idx)^[k] (1,[]):=by rw [kY,h8]
 rw [ha];split_ifs with hq1
 · have hc0:((zx m idx)^[k] (1,[])).1=0:=by
    by_contra hne; have:((zx m idx)^[k] (1,[])).1=1:=by omega
    rw [this,mul_one] at h0; omega
   rw [hc0,mul_zero,add_zero] at h0
   have htb:=kE (m+1) ((zx m idx)^[k] (1,[])).2 (Nat.succ_pos m)
    (fun d hd=>Nat.lt_succ_of_le (h3 d hd))
   rw [hpl,h0] at htb;exact Prod.ext hc0 htb.symm
 · have h7:q+1=(m+1) ^ k:=by omega
   have hc1:((zx m idx)^[k] (1,[])).1=1:=by
    by_contra hne; have:((zx m idx)^[k] (1,[])).1=0:=by omega
    rw [this,mul_zero,add_zero] at h0; omega
   rw [hc1,mul_one,h7] at h0;have hv0:zb (m+1) ((zx m idx)^[k] (1,[])).2=0:=by omega
   have htb:=kE (m+1) ((zx m idx)^[k] (1,[])).2 (Nat.succ_pos m)
    (fun d hd=>Nat.lt_succ_of_le (h3 d hd))
   rw [hpl,hv0,jq] at htb;exact Prod.ext hc1 htb.symm
end ki
namespace ki
open PEqualNP.Library Lib.qC Lib.ve Lib.j4 Lib.R Alg jC
lemma wF {n:ℕ} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2):
 H.card≤n:=by
 have h1:3 * H.card=∑ R∈H,R.card:=by rw [Finset.sum_const_nat hH3,mul_comm]
 have h2:∑ R∈H,R.card=∑ u:Fin n,(H.filter (fun R=>u∈R)).card:=by
  have h0:∀ R∈H,R.card=∑ u:Fin n,if u∈R then 1 else 0:=fun R _=>by rw [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,Nat.cast_id]
  rw [Finset.sum_congr rfl h0,Finset.sum_comm];refine Finset.sum_congr rfl fun u _=>?_
  rw [Finset.sum_boole,Nat.cast_id]
 have h3:∑ u:Fin n,(H.filter (fun R=>u∈R)).card≤∑ _u:Fin n,2:=Finset.sum_le_sum fun u _=>hdeg u
 simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h3;omega
lemma w2 {n:ℕ} {H:(Q4 n)}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2):
 2 * (cores H).card≤n:=by
 have hbi:((cores H).biUnion id).card=2 * (cores H).card:=
  yo (fun c hc=>((zq hH3).mp hc).1)
   (fun c₁ h1 c₂ h2 hne=>zd hH3 hdeg h1 h2 hne)
 have hle:((cores H).biUnion id).card≤n:=by simpa [Fintype.card_fin] using Finset.card_le_univ ((cores H).biUnion id)
 omega
lemma wK (m:ℕ) (idx:Q1):
 vH m idx=1↔(∀ i< idx.length,g idx i≤ m)∧
  (∀ i,i+1< idx.length→ g idx i<g idx (i+1)∨(g idx i=m∧g idx (i+1)=m)):=by
 simp only [vH]
 have h3:∀ {L:Q1},L.sum=0↔∀ x∈L,x=0:=by
  intro L; induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
 have h1:((List.range idx.length).map (fun i=>if m<g idx i then 1 else 0)).sum=0↔
  ∀ i< idx.length,g idx i≤ m:=by
  rw [h3]; simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro h i hi; specialize h i hi; split_ifs at h with hlt <;> omega
  · intro h i hi; rw [if_neg (Nat.not_lt.mpr (h i hi))]
 have h2:((List.range (idx.length-1)).map (fun i=>
  if g idx i<g idx (i+1) then 0
  else if g idx i=m then (if g idx (i+1)=m then 0 else 1) else 1)).sum=0↔
  ∀ i,i+1< idx.length→ g idx i<g idx (i+1)∨(g idx i=m∧g idx (i+1)=m):=by
  rw [h3]; simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro h i hi;specialize h i (by omega);by_cases hlt:g idx i<g idx (i+1)
    · exact Or.inl hlt
    · rw [if_neg hlt] at h;by_cases he1:g idx i=m
      · rw [if_pos he1] at h;by_cases he2:g idx (i+1)=m
        · exact Or.inr ⟨he1,he2⟩
        · rw [if_neg he2] at h; omega
      · rw [if_neg he1] at h; omega
  · intro h i hi;rcases h i (by omega) with hlt|⟨he1,he2⟩
    · rw [if_pos hlt]
    · rw [if_neg (by omega),if_pos he1,if_pos he2]
 split_ifs with h0
 · rw [Nat.add_eq_zero_iff] at h0;exact ⟨fun _=>⟨h1.mp h0.1,h2.mp h0.2⟩,fun _=>rfl⟩
 · simp only [zero_ne_one,false_iff,not_and];intro ha hb; exact h0 (by rw [h1.mpr ha,h2.mpr hb])
lemma ui {m:ℕ} {idx:Q1} (hc:vH m idx=1):
 ∃ (L:Q1),L.Pairwise (·<·)∧(∀ a∈L,a< m)∧L.length≤ idx.length∧
   idx=L++List.replicate (idx.length-L.length) m:=by
 rcases (wK m idx).mp hc with ⟨hbd,hg⟩
 have hk:∀ i j,i≤j→j< idx.length→ g idx i=m→ g idx j=m:=by
  intro i j hij hj hi;induction j with
  | zero=>
    have hi0:i=0:=by omega
    subst hi0; exact hi
  | succ j ih=>
    by_cases h:i=j+1
    · subst h; exact hi
    · have hm:=ih (by omega) (by omega);rcases hg j hj with hlt|⟨_,h2⟩
      · have:=hbd (j+1) hj; omega
      · exact h2
 set L:=idx.takeWhile (fun d=>decide (d< m))
 have hb:∀ a∈L,a< m:=by
  have htw:∀ (p:ℕ→Bool) (l:Q1) (a:ℕ),a∈l.takeWhile p→p a=true:=by
   intro p l; induction l with
   | nil=>simp
   | cons x xs ih=>
     intro a ha; simp only [List.takeWhile_cons] at ha
     cases hx:p x
     · simp [hx] at ha
     · simp only [hx,↓reduceIte,zT] at ha;rcases ha with rfl|ha'; exact hx; exact ih a ha'
  intro a ha; exact decide_eq_true_eq.mp (htw _ idx a ha)
 have hn:L.length≤ idx.length:=k9 _ _
 have h4:idx=L++idx.drop L.length:=by
  have:L=idx.take L.length:=by
   have hf:=List.takeWhile_prefix (p:=fun d=>decide (d< m)) (l:=idx);rcases hf with ⟨t,ht⟩
   have:(L++t).take L.length=L:=List.take_left;rw [ht] at this; exact this.symm
  conv_lhs=>rw [← List.take_append_drop L.length idx,← this]
 have h8:idx.drop L.length=List.replicate (idx.length-L.length) m:=by
  apply List.ext_getElem (by simp);intro k hk1 hk2;rw [List.length_drop] at hk1;rw [List.getElem_drop,List.getElem_replicate];have hkl:L.length+k< idx.length:=by omega
  have h3:L.length< idx.length:=by omega
  have hfirst_ge:m≤ idx[L.length]:=by
   have h7:∀ (p:ℕ→Bool) (l:Q1) (x:ℕ) (xs:Q1),
    l.dropWhile p=x::xs→p x=false:=by
    intro p l; induction l with
    | nil=>simp
    | cons y ys ih=>
      intro x xs h; simp only [List.dropWhile_cons] at h
      cases hy:p y
      · simp only [hy,Bool.false_eq_true,↓reduceIte,List.cons.injEq] at h;exact h.1▸hy
      · simp only [hy,↓reduceIte] at h; exact ih x xs h
   have hd:=List.takeWhile_append_dropWhile (p:=fun d=>decide (d< m)) (l:=idx)
   have hdw:idx.dropWhile (fun d=>decide (d< m))=idx.drop L.length:=by
    have hh:(L++idx.dropWhile (fun d=>decide (d< m))).drop L.length=
     idx.dropWhile (fun d=>decide (d< m)):=List.drop_left
    rw [hd] at hh; exact hh.symm
   have hne:idx.dropWhile (fun d=>decide (d< m))≠[]:=by rw [hdw]; intro h; have:=congrArg List.length h; simp at this; omega
   cases hcons:idx.dropWhile (fun d=>decide (d< m)) with
   | nil=>exact absurd hcons hne
   | cons x xs=>
     have hx:decide (x< m)=false:=h7 _ idx x xs hcons
     have he:idx[L.length]=x:=by
      have:=congrArg (fun l=>l.head?) (hdw.symm.trans hcons);rw [List.head?_drop,List.getElem?_eq_getElem h3] at this
      exact Option.some.inj this
     rw [he]; simp only [decide_eq_false_iff_not,not_lt] at hx; exact hx
  have h5:g idx L.length=m:=by
   have h1:g idx L.length=idx[L.length]:=by simp [g,qf,h3]
   have h2:=hbd L.length h3;omega
  have hk_eq:=hk L.length (L.length+k) (by omega) hkl h5;have:g idx (L.length+k)=idx[L.length+k]:=by simp [g,qf,hkl]
  omega
 have hl:L.Pairwise (·<·):=by
  have h6:∀ t (ht:t<L.length),idx[t]'(by omega)=L[t]:=fun t ht=>by
   have hq:=congrArg (fun l=>l[t]?) h4;rw [List.getElem?_eq_getElem (by omega),List.getElem?_append_left ht,List.getElem?_eq_getElem ht] at hq
   exact Option.some.inj hq
  rw [List.pairwise_iff_getElem];intro i j hi hj hij
  have ho:∀ d (hid:i+d<L.length),L[i]<L[i+d]'hid∨d=0:=by
   intro d; induction d with
   | zero=>intro _; exact Or.inr rfl
   | succ d ih=>
     intro hid
     have h9:L[i+d]'(by omega)<L[i+d+1]'(by omega):=by
      have h1:L[i+d]'(by omega)=g idx (i+d):=by have:=h6 (i+d) (by omega);simp [g,qf,show i+d< idx.length by omega,this]
      have h2:L[i+d+1]'(by omega)=g idx (i+d+1):=by have:=h6 (i+d+1) (by omega);simp [g,qf,show i+d+1< idx.length by omega,this]
      have hltm:g idx (i+d)< m:=h1▸hb _ (qn (by omega));rcases hg (i+d) (by omega) with hlt|⟨hm,_⟩
      · rw [h1,h2]; exact hlt
      · omega
     rcases ih (by omega) with hlt|rfl
     · exact Or.inl (hlt.trans h9)
     · exact Or.inl (by simpa using h9)
  rcases ho (j-i) (by omega) with hlt|h0
  · convert hlt using 2; omega
  · omega
 exact ⟨L,hl,hb,hn,h8▸h4⟩
lemma ww (v:Q1):yu v=1↔v.Nodup:=by
 simp only [yu]
 have h1:∀ {L:Q1},L.sum=0↔∀ x∈L,x=0:=by
  intro L; induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
 have h2:((List.range v.length).map (fun i=>
  ((List.range v.length).map (fun k=>if i<k then (if g v i=g v k then 1 else 0) else 0)).sum)).sum=0↔
  v.Nodup:=by
  rw [h1,List.nodup_iff_injective_getElem];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro h ⟨i,hi⟩ ⟨j,hj⟩ heq;dsimp only at heq;ext; dsimp only;by_contra hne;rcases lt_or_gt_of_ne hne with hlt|hlt
    · have h0:=(h1.mp (h i hi)) _ (qQ.mpr ⟨j,qw.mpr hj,rfl⟩);have hgi:g v i=v[i]:=by simp [g,qf,hi]
      have hgj:g v j=v[j]:=by simp [g,qf,hj]
      rw [if_pos hlt,hgi,hgj,if_pos heq] at h0; omega
    · have h0:=(h1.mp (h j hj)) _ (qQ.mpr ⟨i,qw.mpr hi,rfl⟩);have hgi:g v i=v[i]:=by simp [g,qf,hi]
      have hgj:g v j=v[j]:=by simp [g,qf,hj]
      rw [if_pos hlt,hgi,hgj,if_pos heq.symm] at h0; omega
  · intro h4 i hi;rw [h1]; intro x hx; rcases qQ.mp hx with ⟨k,hk,rfl⟩
    have hkl:k<v.length:=qw.mp hk;split_ifs with hlt heq
    · have hgi:g v i=v[i]:=by simp [g,qf,hi]
      have hgk:g v k=v[k]:=by simp [g,qf,hkl]
      rw [hgi,hgk] at heq;have h3:=congrArg Fin.val (h4 (a₁:=⟨i,hi⟩) (a₂:=⟨k,hkl⟩) heq);dsimp only at h3;omega
    · rfl
    · rfl
 split_ifs with h0
 · simp [h2.mp h0]
 · simp [h2.not.mp h0]
lemma uU {n:ℕ} {v:Q1} (hlt:∀ a∈v,a<n):
 (qx n v).card=v.length↔v.Nodup:=by
 have h3:qx n v=(v.attach.map (fun a=>(⟨a.1,hlt a.1 a.2⟩:Fin n))).toFinset:=by ext u; simp only [zB,List.mem_toFinset,qQ,List.mem_attach,true_and,Subtype.exists];exact ⟨fun hu=>⟨u.val,hu,rfl⟩,fun ⟨_,ha,h⟩=>h▸ha⟩
 set w:=v.attach.map (fun a=>(⟨a.1,hlt a.1 a.2⟩:Fin n));have h0:w.length=v.length:=by simp [w]
 have h2:w.Nodup↔v.Nodup:=by
  have h4:Function.Injective (fun a:{x // x∈v}=>(⟨a.1,hlt a.1 a.2⟩:Fin n)):=fun x y h=>Subtype.ext (congrArg Fin.val h)
  rw [show w=_ from rfl,List.nodup_map_iff h4,List.nodup_attach]
 rw [h3,← h0,← h2];constructor
 · intro hcard;by_contra hnot
   have hlt':w.toFinset.card<w.length:=by
    have h1:w.toFinset.card=w.dedup.length:=by rw [← List.toFinset_dedup,List.toFinset_card_of_nodup (List.nodup_dedup w)]
    rw [h1]
    exact Nat.lt_of_le_of_ne (List.dedup_sublist w).length_le
     (fun hlen=>hnot (List.Sublist.eq_of_length (List.dedup_sublist w) hlen▸List.nodup_dedup w))
   omega
 · exact List.toFinset_card_of_nodup
def ua (n:ℕ) (U0:Q3 n) (F0:Q4 n) (st:PeelSt):Prop:=st.um.length=n∧(∀ b∈st.um,b≤1)∧(st.dead=1→∀ s,(q7 U0 F0 s).card=0)∧
 (st.dead=0→
   let U:=qL n st.um
   let F:=qR n st.F
   (∀ R∈st.F,R.Pairwise (·<·)∧(∀ a∈R,a<n)∧qx n R⊆U∧R.length≤3)∧
   (∀ R₁∈F,∀ R₂∈F,R₁≠R₂→(R₁ ∩ R₂).card≤1)∧
   ((∀ R∈st.F,2≤R.length)→(∀ i<st.F.length,∀ j<st.F.length,i≠j→qx n (gg st.F i)≠qx n (gg st.F j))∧(∀ u,vO F u≤2))∧
   (∀ s,(q7 U0 F0 s).card=if s<st.kF then 0 else (q7 U F (s-st.kF)).card))
lemma uG (F:Q2):jv F=1↔∃ R∈F,R.length<2:=by
 simp only [jv]
 have h1:∀ {L:Q1},L.sum=0↔∀ x∈L,x=0:=by
  intro L; induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
 have h2:((List.range F.length).map (fun r=>if (gg F r).length<2 then 1 else 0)).sum=0↔
  ∀ R∈F,2≤R.length:=by
  rw [h1]; simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro h R hR; rcases vI.mp hR with ⟨r,hr,rfl⟩
    specialize h r hr;have hgg:gg F r=F[r]:=by simp [gg,qf,hr]
    rw [hgg] at h; split_ifs at h <;> omega
  · intro h r hr;have hgg:gg F r=F[r]:=by simp [gg,qf,hr]
    rw [hgg,if_neg (by have:=h F[r] (qn hr); omega)]
 split_ifs with h0
 · simp only [zero_ne_one,false_iff,not_exists,not_and,not_lt]; exact h2.mp h0
 · simp only [true_iff]; by_contra hall; push_neg at hall; exact h0 (h2.mpr hall)
lemma uz (F:Q2):
 (vl F=F.length∧∀ R∈F,R.length≠2)∨
 (vl F<F.length∧(gg F (vl F)).length=2∧
   ∀ r<vl F,(gg F r).length≠2):=by
 have h7:∀ {L:Q1},L.sum=0↔∀ x∈L,x=0:=by
  intro L; induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
 have h2:∀ i,((List.range (i+1)).map (fun r=>if (gg F r).length=2 then 1 else 0)).sum=0↔
  ∀ r≤ i,(gg F r).length≠2:=by
  intro i; rw [h7];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro h r hr; specialize h r (by omega);by_cases heq:(gg F r).length=2
    · rw [if_pos heq] at h; omega
    · exact heq
  · intro h r hr; rw [if_neg (h r (by omega))]
 by_cases hex:∃ r<F.length,(gg F r).length=2
 · classical
   set k:=Nat.find hex;have h5:k<F.length:=(Nat.find_spec hex).1;have h6:(gg F k).length=2:=(Nat.find_spec hex).2
   have h3:∀ r<k,(gg F r).length≠2:=fun r hr=>by have:=Nat.find_min hex hr; intro heq; exact this ⟨hr.trans h5,heq⟩
   have h4:vl F=k:=by
    simp only [vl]
    have h1:∀ i∈List.range F.length,
     (if ((List.range (i+1)).map (fun r=>if (gg F r).length=2 then 1 else 0)).sum=0 then 1 else 0)=
     if i<k then 1 else 0:=by
     intro i _;by_cases hik:i<k
     · rw [if_pos hik,if_pos ((h2 i).mpr fun r hr=>h3 r (by omega))]
     · rw [if_neg hik,if_neg]; intro h0; exact ((h2 i).mp h0 k (by omega)) h6
    rw [List.map_congr_left h1]
    have h9:∀ m,((List.range m).map (fun i=>if i<k then 1 else 0)).sum=min m k:=by
     intro m; induction m with
     | zero=>simp
     | succ m ih=>rw [zP,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,ih];split_ifs <;> omega
    rw [h9 F.length,min_eq_right (by omega)]
   exact Or.inr ⟨h4▸h5,h4▸h6,fun r hr=>h3 r (h4▸hr)⟩
 · push_neg at hex;have h8:∀ r<F.length,(gg F r).length≠2:=hex
   have h4:vl F=F.length:=by
    simp only [vl]
    have h1:∀ i∈List.range F.length,
     (if ((List.range (i+1)).map (fun r=>if (gg F r).length=2 then 1 else 0)).sum=0 then 1 else 0)=1:=by
     intro i hi;have hil:i<F.length:=qw.mp hi;rw [if_pos ((h2 i).mpr fun r hr=>h8 r (by omega))]
    rw [List.map_congr_left h1,List.map_const',List.sum_replicate,smul_eq_mul,mul_one,List.length_range]
   refine Or.inl ⟨h4,fun R hR=>?_⟩
   rcases vI.mp hR with ⟨r,hr,rfl⟩
   have hgg:gg F r=F[r]:=by simp [gg,qf,hr]
   exact hgg▸h8 r hr
lemma qad {n:ℕ} {U0:(Q3 n)} {F0:(Q4 n)} {st:PeelSt}
 (hgood:ua n U0 F0 st) (hdead01:st.dead≤1):
 ua n U0 F0 (yb n st)∧
 ((yb n st).dead=1∨(∀ R∈(yb n st).F,R.length=3)∨(yb n st).F.length<st.F.length):=by
 rcases hgood with ⟨hE,hF,hC,hc⟩
 unfold yb; dsimp only;split_ifs with h1 h2 h3
 · exact ⟨⟨hE,hF,hC,hc⟩,Or.inl h1⟩
 · have hd0:st.dead=0:=by omega
   rcases hc hd0 with ⟨h4,hx,_,hH⟩
   rcases (uG st.F).mp h2 with ⟨R,hRF,hRlt2⟩
   have hM:(qx n R).card≤1:=by have hp:=h4 R hRF;rw [zF (qK hp.1) hp.2.1]; omega
   have h0:∀ s,(q7 U0 F0 s).card=0:=fun s=>by
    rw [hH s]; split_ifs
    · rfl
    · exact qam (zj.mpr ⟨R,hRF,rfl⟩) hM
   exact ⟨⟨hE,hF,fun _=>h0,fun h=>by dsimp at h; omega⟩,Or.inl rfl⟩
 · have hd0:st.dead=0:=by omega
   rcases hc hd0 with ⟨h4,hx,hT,hH⟩
   have hz:∀ R∈st.F,2≤R.length:=by intro R hR; by_contra hlt;have:jv st.F=1:=(uG st.F).mpr ⟨R,hR,by omega⟩;exact h2 this
   have hX:∀ R∈st.F,R.length≠2:=by
    rcases uz st.F with ⟨_,hY⟩|⟨hlt,_,_⟩
    · exact hY
    · omega
   have hU:∀ R∈st.F,R.length=3:=fun R hR=>by have h1':=hz R hR; have h2':=hX R hR; have h3':=(h4 R hR).2.2.2; omega
   exact ⟨⟨hE,hF,hC,hc⟩,Or.inr (Or.inl hU)⟩
 · have hd0:st.dead=0:=by omega
   rcases hc hd0 with ⟨h4,hx,ho,hH⟩
   have hz:∀ R∈st.F,2≤R.length:=by intro R hR; by_contra hlt;exact h2 ((uG st.F).mpr ⟨R,hR,by omega⟩)
   rcases ho hz with ⟨hS,hT⟩
   rcases uz st.F with ⟨heq,_⟩|⟨h6,hA,_⟩
   · exact absurd heq h3
   set idx:=vl st.F;set e:=gg st.F idx
   have hl:e∈st.F:=by
    have:e=st.F[idx]:=by simp [e,gg,qf,h6]
    rw [this]; exact qn h6
   have h9:=h4 e hl
   have hG:(qx n e).card=2:=by rw [zF (qK h9.1) h9.2.1,hA]
   set p:=g e 0; set q:=g e 1
   have hB:e=[p,q]:=by
    rcases List.length_eq_two.mp hA with ⟨a,b,hab⟩
    rw [hab]; simp [p,q,hab,g]
   set um':=(List.range n).map (fun v=>if v=p then 0 else if v=q then 0 else if g st.um v=0 then 0 else 1)
   set F':=(List.range st.F.length).flatMap (fun r=>if r=idx then [] else [zc um' (gg st.F r)])
   have ht:um'.length=n:=by simp [um']
   have hK:∀ b∈um',b≤1:=by intro b hb; simp only [um',qQ] at hb; rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
   have h8:qL n um'=qL n st.um \ qx n e:=by
    ext u; simp only [q8,um',yc,qg,zB,hB,zT,List.not_mem_nil,or_false]
    have hgu:g st.um u.val≤1:=by
     have hu:u.val<st.um.length:=hE▸u.isLt;have:g st.um u.val=st.um[u.val]:=by simp [g,qf,hu]
     rw [this]; exact hF _ (qn hu)
    rcases (by omega:g st.um u.val=0∨g st.um u.val=1) with hgu'|hgu' <;>
     rw [hgu'] <;> by_cases hp:u.val=p <;> by_cases hq:u.val=q <;> simp [hp,hq]
   have he:qR n F'=((qR n st.F).erase (qx n e)).image (fun R=>R \ qx n e):=by
    ext R; simp only [zj,qN,qh,F',List.mem_flatMap,qw];constructor
    · rintro ⟨v,⟨r,hr,hv⟩,rfl⟩;split_ifs at hv with hI
      · simp at hv
      · simp only [z4] at hv; subst hv
        have h7:gg st.F r∈st.F:=by
         have:gg st.F r=st.F[r]:=by simp [gg,qf,hr]
         rw [this]; exact qn hr
        have hfm:=(vb (um:=um') (h4 _ h7).2.1).1;rw [h8] at hfm;have hg:=(h4 _ h7).2.2.1
        have hh:qx n (gg st.F r) ∩ (qL n st.um \ qx n e)=qx n (gg st.F r) \ qx n e:=by ext u; simp only [qm,qg];exact ⟨fun ⟨h1,_,h3⟩=>⟨h1,h3⟩,fun ⟨h1,h3⟩=>⟨h1,hg h1,h3⟩⟩
        refine ⟨qx n (gg st.F r),⟨hS r hr idx h6 hI,gg st.F r,h7,rfl⟩,(hfm.trans hh).symm⟩
    · rintro ⟨R₀,⟨hZ,w,hwF,rfl⟩,rfl⟩;rcases vI.mp hwF with ⟨r,hr,rfl⟩
      have hgg:gg st.F r=st.F[r]:=by simp [gg,qf,hr]
      have hW:r≠idx:=fun h=>hZ (by rw [← hgg,h])
      have hfm:=(vb (um:=um') (h4 _ hwF).2.1).1;rw [h8] at hfm;have hg:=(h4 _ hwF).2.2.1
      have hh:qx n st.F[r] ∩ (qL n st.um \ qx n e)=qx n st.F[r] \ qx n e:=by ext u; simp only [qm,qg];exact ⟨fun ⟨h1,_,h3⟩=>⟨h1,h3⟩,fun ⟨h1,h3⟩=>⟨h1,hg h1,h3⟩⟩
      refine ⟨zc um' (gg st.F r),⟨r,hr,?_⟩,hgg.symm▸(hfm.trans hh)⟩
      rw [if_neg hW]; simp
   have hm:F'.length<st.F.length:=by
    have hy:∀ m,((List.range m).flatMap (fun r=>
     if r=idx then [] else [zc um' (gg st.F r)])).length=
     if idx< m then m-1 else m:=by
     intro m; induction m with
     | zero=>simp
     | succ m ihm=>rw [zP,List.flatMap_append,List.flatMap_singleton,List.length_append,ihm];split_ifs <;> simp <;> omega
    rw [show F'.length=_ from hy st.F.length,if_pos h6]; omega
   refine ⟨⟨ht,hK,fun h=>by dsimp at h; omega,fun _=>?_⟩,Or.inr (Or.inr hm)⟩
   dsimp only;refine ⟨?_,?_,?_,?_⟩
   · intro R' hR';simp only [F',List.mem_flatMap,qw] at hR';rcases hR' with ⟨r,hr,hv⟩
     split_ifs at hv with hI
     · simp at hv
     · simp only [z4] at hv; subst hv
       have h7:gg st.F r∈st.F:=by
        have:gg st.F r=st.F[r]:=by simp [gg,qf,hr]
        rw [this]; exact qn hr
       have hp:=h4 _ h7;have hfm:=vb (um:=um') hp.2.1;refine ⟨hfm.2.1 hp.1,hfm.2.2,hfm.1.symm▸Finset.inter_subset_right,?_⟩
       rw [← zF (qK (hfm.2.1 hp.1)) hfm.2.2,hfm.1]
       exact (qH vD).trans
        (by rw [zF (qK hp.1) hp.2.1]; exact hp.2.2.2)
   · intro R₁ h1 R₂ h2 hne;rw [he] at h1 h2;rcases qN.mp h1 with ⟨A₁,hA1,rfl⟩
     rcases qN.mp h2 with ⟨A₂,hA2,rfl⟩
     have h00:A₁≠A₂:=fun h=>hne (h▸rfl)
     exact (qH (Finset.inter_subset_inter Finset.sdiff_subset Finset.sdiff_subset)).trans
      (hx A₁ (qE hA1) A₂ (qE hA2) h00)
   · intro hz'
     have hD:F'=((List.range st.F.length).filter (fun r=>decide (r≠idx))).map
      (fun r=>zc um' (gg st.F r)):=by
      have hy:∀ m,(List.range m).flatMap (fun r=>if r=idx then [] else [zc um' (gg st.F r)])=
       ((List.range m).filter (fun r=>decide (r≠idx))).map (fun r=>zc um' (gg st.F r)):=by
       intro m; induction m with
       | zero=>simp
       | succ m ihm=>rw [zP,List.flatMap_append,List.flatMap_singleton,List.filter_append,List.filter_cons,List.filter_nil,List.map_append,ihm];by_cases h:m=idx <;> simp [h]
      exact hy st.F.length
     have hJ:(List.range st.F.length).filter (fun r=>decide (r≠idx))=
      (List.range (st.F.length-1)).map (fun k=>if k< idx then k else k+1):=by
      have hy:∀ m,(List.range m).filter (fun r=>decide (r≠idx))=
       if idx< m then (List.range (m-1)).map (fun k=>if k< idx then k else k+1)
       else List.range m:=by
       intro m; induction m with
       | zero=>simp
       | succ m ihm=>
         rw [zP,List.filter_append,List.filter_cons,List.filter_nil,ihm];by_cases h1:m=idx
         · rw [h1,if_neg (Nat.lt_irrefl _),if_pos (Nat.lt_succ_self _)];simp only [ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,qX,Nat.add_sub_cancel]
           have:(List.range idx).map (fun k=>if k< idx then k else k+1)=List.range idx:=by
            conv_rhs=>rw [← List.map_id (List.range idx)]
            exact List.map_congr_left fun a ha=>by rw [if_pos (qw.mp ha)]; rfl
           exact this.symm
         · by_cases h2:idx< m
           · simp only [h2,show idx< m+1 by omega,↓reduceIte];have hg:m+1-1=(m-1)+1:=by omega
             rw [hg,zP,List.map_append,List.map_singleton]
             simp only [show ¬ (m-1< idx) by omega,↓reduceIte,show m-1+1=m by omega,
              h1,ne_eq,not_false_eq_true,decide_true]
           · simp only [h2,show ¬ idx< m+1 by omega,↓reduceIte,h1,ne_eq,not_false_eq_true,
              decide_true,zP]
      rw [hy st.F.length,if_pos h6]
     have hFl:F'.length=st.F.length-1:=by rw [hD,hJ]; simp
     have h5:∀ k<F'.length,gg F' k=zc um' (gg st.F (if k< idx then k else k+1)):=by
      intro k hk;have hgg:gg F' k=F'[k]:=by simp [gg,qf,hk]
      rw [hgg]; simp only [hD,hJ,List.getElem_map,List.getElem_range]
     refine ⟨fun i hi j hj hij heq=>?_,fun u=>?_⟩
     · set ri:=if i< idx then i else i+1
       set rj:=if j< idx then j else j+1
       have hri:ri<st.F.length:=by dsimp [ri]; split_ifs <;> omega
       have hrj:rj<st.F.length:=by dsimp [rj]; split_ifs <;> omega
       have hP:ri≠rj:=by dsimp [ri,rj]; split_ifs <;> omega
       have hw:=hS ri hri rj hrj hP
       have hf:gg st.F ri∈st.F:=by
        have:gg st.F ri=st.F[ri]:=by simp [gg,qf,hri]
        rw [this]; exact qn hri
       have hn:gg st.F rj∈st.F:=by
        have:gg st.F rj=st.F[rj]:=by simp [gg,qf,hrj]
        rw [this]; exact qn hrj
       have hL:gg F' i∈F':=by
        have:gg F' i=F'[i]:=by simp [gg,qf,hi]
        rw [this]; exact qn hi
       have hfi:=vb (um:=um') (h4 _ hf).2.1;have hfj:=vb (um:=um') (h4 _ hn).2.1
       have hO:qx n (gg F' i)⊆qx n (gg st.F ri):=by rw [h5 i hi,hfi.1]; exact vD
       have hN:qx n (gg F' i)⊆qx n (gg st.F rj):=by rw [heq,h5 j hj,hfj.1]; exact vD
       have hle1:=hx _ (zj.mpr ⟨_,hf,rfl⟩) _ (zj.mpr ⟨_,hn,rfl⟩) hw
       have hcard_ge2:2≤(qx n (gg F' i)).card:=by rw [h5 i hi,zF (qK (hfi.2.1 (h4 _ hf).1)) hfi.2.2,← h5 i hi];exact hz' _ hL
       have:=qH (Finset.subset_inter hO hN);omega
     · unfold vO
       have hg:(qR n F').filter (fun R=>u∈R)⊆
        ((qR n st.F).filter (fun R=>u∈R)).image (fun R=>R \ qx n e):=by
        intro R' hR';rcases qa.mp hR' with ⟨hV,huR'⟩
        rw [he] at hV;rcases qN.mp hV with ⟨A,hAe,rfl⟩
        exact qN.mpr ⟨A,qa.mpr ⟨qE hAe,(qg.mp huR').1⟩,rfl⟩
       exact (qH hg).trans (Finset.card_image_le.trans (hT u))
   · intro s;rw [hH s];by_cases hs:s<st.kF
     · rw [if_pos hs,if_pos (by omega)]
     · rw [if_neg hs]
       have hQ:=qal (U:=qL n st.um) (F:=qR n st.F) (s:=s-st.kF)
        (e:=qx n e) (zj.mpr ⟨e,hl,rfl⟩) hG h9.2.2.1
        (fun R hR hRe=>hx R hR (qx n e) (zj.mpr ⟨e,hl,rfl⟩) hRe)
       rw [hQ,← h8,← he];by_cases hs2:s<st.kF+1
       · have:s-st.kF=0:=by omega
         rw [if_pos hs2,if_pos this]
       · have:s-st.kF≠0:=by omega
         rw [if_neg hs2,if_neg this,show s-st.kF-1=s-(st.kF+1) by omega]
end ki
namespace ki
open PEqualNP.Library Lib.qC Lib.ve Lib.j4 Lib.R Alg jC
lemma qbv {n:ℕ} {U0:(Q3 n)} {F0:(Q4 n)}
 {um0:Q1} {Fl0:Q2}
 (hgood0:ua n U0 F0 ⟨0,0,um0,Fl0⟩) (hF0le:Fl0.length≤n):
 let ps:=kD n um0 Fl0
 ua n U0 F0 ps∧ps.dead≤1∧
 (ps.dead=1∨∀ R∈ps.F,R.length=3):=by
 have h9:∀ k,let st:=(yb n)^[k] ⟨0,0,um0,Fl0⟩
  ua n U0 F0 st∧st.dead≤1∧
  (st.dead=1∨(∀ R∈st.F,R.length=3)∨st.F.length+k≤Fl0.length):=by
  intro k; induction k with
  | zero=>dsimp only [Function.iterate_zero_apply]; exact ⟨hgood0,by omega,Or.inr (Or.inr (by simp))⟩
  | succ k ih=>
    rcases ih with ⟨hg,hd,h4⟩
    rw [qM];set st:=(yb n)^[k] ⟨0,0,um0,Fl0⟩;rcases qad hg hd with ⟨hg',h5⟩
    have hd':(yb n st).dead≤1:=by unfold yb; dsimp only; split_ifs <;> (try dsimp only) <;> omega
    refine ⟨hg',hd',?_⟩
    rcases h4 with h1|h2|h3
    · left; unfold yb; rw [if_pos h1]; exact h1
    · rcases h5 with hs1|hs2|hs3
      · exact Or.inl hs1
      · exact Or.inr (Or.inl hs2)
      ·
       right; left
       have h8:jv st.F≠1:=by intro h; rcases (uG st.F).mp h with ⟨R,hR,hlt⟩; have:=h2 R hR; omega
       have h7:vl st.F=st.F.length:=by
        rcases uz st.F with ⟨heq,_⟩|⟨hlt,heq2,_⟩
        · exact heq
        · have:gg st.F (vl st.F)∈st.F:=by
           have:gg st.F (vl st.F)=st.F[vl st.F]:=by simp [gg,qf,hlt]
           rw [this]; exact qn hlt
          have:=h2 _ this; omega
       unfold yb;by_cases h6:st.dead=1
       · rw [if_pos h6]; exact h2
       · rw [if_neg h6,if_neg h8,if_pos h7]; exact h2
    · rcases h5 with hs1|hs2|hs3
      · exact Or.inl hs1
      · exact Or.inr (Or.inl hs2)
      · exact Or.inr (Or.inr (by omega))
 rcases h9 n with ⟨hg,hd,h4⟩
 refine ⟨hg,hd,?_⟩
 rcases h4 with h1|h2|h3
 · exact Or.inl h1
 · exact Or.inr h2
 · right; intro R hR;have h0:((yb n)^[n] ⟨0,0,um0,Fl0⟩).F.length=0:=by omega
   change R∈((yb n)^[n] ⟨0,0,um0,Fl0⟩).F at hR;rw [List.length_eq_zero_iff.mp h0] at hR; simp at hR
lemma qbO {n:ℕ} {Fl:Q2} {vm:Q1}
 (hvm_len:vm.length=n) (hvm_b:∀ b∈vm,b≤1)
 (hFl_lt:∀ R∈Fl,∀ a∈R,a<n):
 (vX n Fl vm).length=n∧(∀ b∈vX n Fl vm,b≤1)∧
 qL n (vX n Fl vm)=step (qR n Fl) (qL n vm):=by
 have h5:(vX n Fl vm).length=n:=by simp [vX]
 have hb:∀ b∈vX n Fl vm,b≤1:=by intro b hb; simp only [vX,qQ] at hb; rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
 refine ⟨h5,hb,?_⟩
 have h4:∀ {L:Q1},L.sum=0↔∀ x∈L,x=0:=by
  intro L; induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
 ext u;simp only [q8,vX,yc,step,ql,qj,qa,id_eq,zj]
 have h6:∀ (R:Q1) (w:ℕ),
  ((List.range R.length).map (fun i=>if g R i=w then 1 else 0)).sum≠0↔w∈R:=by
  intro R w; rw [ne_eq,h4];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro hne; by_contra hnot; apply hne; intro i hi;have hgi:g R i=R[i]:=by simp [g,qf,hi]
    rw [hgi,if_neg (fun (e:R[i]=w)=>hnot (e▸qn hi))]
  · intro hw hall; rcases vI.mp hw with ⟨i,hi,rfl⟩
    have hgi:g R i=R[i]:=by simp [g,qf,hi]
    have:=hall i hi; rw [hgi,if_pos rfl] at this; omega
 have h9:∀ (R:Q1),(∀ a∈R,a<n)→
  (((List.range R.length).map (fun i=>g vm (g R i))).sum≠0↔¬ Disjoint (qx n R) (qL n vm)):=by
  intro R hRlt; rw [ne_eq,h4,vE];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
  · intro hne; by_contra hnot; apply hne; intro i hi;have hgi:g R i=R[i]:=by simp [g,qf,hi]
    rw [hgi];have ha:R[i]<n:=hRlt _ (qn hi)
    have hv01:g vm R[i]≤1:=by
     have h5':R[i]<vm.length:=hvm_len▸ha;have:g vm R[i]=vm[R[i]]:=by simp [g,qf,h5']
     rw [this]; exact hvm_b _ (qn h5')
    by_contra hnz;have h1:g vm R[i]=1:=by omega
    exact hnot ⟨⟨R[i],ha⟩,zB.mpr (qn hi),q8.mpr h1⟩
  · rintro ⟨w,hwR,hwm⟩ hall;rcases vI.mp (zB.mp hwR) with ⟨i,hi,hwi⟩
    have hgi:g R i=w.val:=by simp [g,qf,hi,hwi]
    have:=hall i hi; rw [hgi,q8.mp hwm] at this; omega
 by_cases hu1:g vm u.val=1
 · simp only [hu1,↓reduceIte,true_iff,true_or]
 · rw [if_neg hu1]
   have hc:((List.range Fl.length).map (fun r=>
    (if ((List.range (gg Fl r).length).map (fun i=>if g (gg Fl r) i=u.val then 1 else 0)).sum=0 then 0 else 1) *
    (if ((List.range (gg Fl r).length).map (fun i=>g vm (g (gg Fl r) i))).sum=0 then 0 else 1))).sum≠0↔
    ∃ R,(∃ v∈Fl,qx n v=R)∧¬ Disjoint R (qL n vm)∧u∈R:=by
    rw [ne_eq,h4];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
    · intro hne; by_contra hnot; apply hne; intro r hr;have hgg:gg Fl r=Fl[r]:=by simp [gg,qf,hr]
      rw [hgg];by_cases h1:((List.range Fl[r].length).map (fun i=>if g Fl[r] i=u.val then 1 else 0)).sum=0
      · rw [if_pos h1,zero_mul]
      · by_cases h2:((List.range Fl[r].length).map (fun i=>g vm (g Fl[r] i))).sum=0
        · rw [if_pos h2,mul_zero]
        · exfalso;have h7:u∈qx n Fl[r]:=zB.mpr ((h6 Fl[r] u.val).mp h1);have hnd:=(h9 Fl[r] (hFl_lt _ (qn hr))).mp h2;exact hnot ⟨qx n Fl[r],⟨Fl[r],qn hr,rfl⟩,hnd,h7⟩
    · rintro ⟨_,⟨v,h8,rfl⟩,hnd,h7⟩ hall;rcases vI.mp h8 with ⟨r,hr,rfl⟩
      have hgg:gg Fl r=Fl[r]:=by simp [gg,qf,hr]
      have h1:=(h6 Fl[r] u.val).mpr (zB.mp h7);have h2:=(h9 Fl[r] (hFl_lt _ h8)).mpr hnd;have:=hall r hr;rw [hgg,if_neg h1,if_neg h2] at this; omega
   split_ifs with h0
   · simp only [zero_ne_one,false_iff,not_or]; exact ⟨hu1,fun ⟨R,⟨h1,h2⟩,h3⟩=>(hc.mpr ⟨R,h1,h2,h3⟩) h0⟩
   · simp only [true_iff]; right;rcases hc.mp h0 with ⟨R,h1,h2,h3⟩; exact ⟨R,⟨h1,h2⟩,h3⟩
lemma uy {n:ℕ} {Fl:Q2} (hFl_lt:∀ R∈Fl,∀ a∈R,a<n) (u:Fin n):
 (zN n Fl u.val).length=n∧(∀ b∈zN n Fl u.val,b≤1)∧
 qL n (zN n Fl u.val)=qr (qR n Fl) u:=by
 have h1:∀ k,let v:=(vX n Fl)^[k] ((List.range n).map (fun v=>if v=u.val then 1 else 0))
  v.length=n∧(∀ b∈v,b≤1)∧qL n v=(step (qR n Fl))^[k] {u}:=by
  intro k; induction k with
  | zero=>
    dsimp only [Function.iterate_zero_apply];refine ⟨by simp,?_,?_⟩
    · intro b hb; simp only [qQ] at hb; rcases hb with ⟨_,_,rfl⟩; split_ifs <;> omega
    · ext w; simp [q8,yc,Fin.ext_iff]
  | succ k ih=>
    rcases ih with ⟨hl,hb,h0⟩
    rw [qM,qM];rcases qbO hl hb hFl_lt with ⟨hl',hb',h0'⟩
    exact ⟨hl',hb',h0'.trans (congrArg _ h0)⟩
 rcases h1 n with ⟨hl,hb,h0⟩
 exact ⟨hl,hb,h0.trans (by unfold qr; rw [zY])⟩
lemma uD {n t:ℕ} {um:Q1} {Fl:Q2}
 (hum_len:um.length=n) (hum_b:∀ b∈um,b≤1)
 (hFl_lt:∀ R∈Fl,∀ a∈R,a<n)
 (hFU:∀ R∈qR n Fl,R⊆qL n um)
 (hFl_inj:∀ i<Fl.length,∀ j<Fl.length,i≠j→qx n (gg Fl i)≠qx n (gg Fl j)):
 let U:=qL n um;let F:=qR n Fl
 (∀ u:Fin n,y1 n um Fl u.val=1↔u∈U∧∀ v∈qr F u,u.val≤v.val)∧
 (∀ u:Fin n,yA n Fl u.val=(qr F u).card)∧
 (∀ u:Fin n,yG n Fl u.val=vh F (qr F u))∧
 (yT n um Fl=1↔jj U F)∧
 kN n um Fl=(kX U F).card∧
 kx n um Fl=(ky U F).card∧
 (vS n t um Fl).length=t∧(∀ b∈vS n t um Fl,b≤1)∧
 qV (vS n t um Fl)=((ky U F).prod Finset.card) % 2 ^ t:=by
 intro U F
 have hx:∀ {L:Q1},L.sum=0↔∀ x∈L,x=0:=by
  intro L; induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
 have h5:∀ u:Fin n,y1 n um Fl u.val=1↔u∈U∧∀ v∈qr F u,u.val≤v.val:=by
  intro u;rcases uy hFl_lt u with ⟨hz,ho,ha⟩
  simp only [y1,U,q8];by_cases hu:g um u.val=1
  · rw [if_pos hu]
    have h0:((List.range u.val).map (fun v=>g (zN n Fl u.val) v)).sum=0↔
     ∀ v∈qr F u,u.val≤v.val:=by
     rw [hx];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
     · intro h v hv; by_contra hlt;have hv1:g (zN n Fl u.val) v.val=1:=q8.mp (ha.symm▸hv);have:=h v.val (by omega); omega
     · intro h v hv;have hvn:v<n:=hv.trans u.isLt
       have hv01:g (zN n Fl u.val) v≤1:=by
        have hvl:v<(zN n Fl u.val).length:=by omega
        have:g (zN n Fl u.val) v=(zN n Fl u.val)[v]:=by simp [g,qf,hvl]
        rw [this]; exact ho _ (qn hvl)
       by_contra hnz;have hv1:g (zN n Fl u.val) v=1:=by omega
       have hle:=h ⟨v,hvn⟩ (ha▸q8.mpr hv1);dsimp only at hle; omega
    split_ifs with h
    · exact ⟨fun _=>⟨hu,h0.mp h⟩,fun _=>rfl⟩
    · exact ⟨fun h1=>absurd h1 (by decide),fun ⟨_,hI⟩=>h (h0.mpr hI)⟩
  · rw [if_neg hu];exact ⟨fun h1=>absurd h1 (by decide),fun ⟨h1,_⟩=>(hu h1).elim⟩
 have h7:∀ u:Fin n,yA n Fl u.val=(qr F u).card:=fun u=>by
  rcases uy hFl_lt u with ⟨hl,hb,hH⟩
  rw [yA,← wx hl hb,hH]
 have h6:∀ u:Fin n,yG n Fl u.val=vh F (qr F u):=fun u=>by
  rcases uy hFl_lt u with ⟨hz,ho,ha⟩
  have hf:∀ r<Fl.length,
   (((List.range (gg Fl r).length).map (fun i=>1-g (zN n Fl u.val) (g (gg Fl r) i))).sum=0)↔
   qx n (gg Fl r)⊆qr F u:=by
   intro r hr
   have hc:gg Fl r∈Fl:=by
    have:gg Fl r=Fl[r]:=by simp [gg,qf,hr]
    rw [this]; exact qn hr
   rw [hx];simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
   · intro h w hw;rcases vI.mp (zB.mp hw) with ⟨i,hi,hwi⟩
     have hgi:g (gg Fl r) i=w.val:=by rw [g,qf,List.getElem?_eq_getElem hi]; exact hwi
     have h0:=h i hi; rw [hgi] at h0
     have hw01:g (zN n Fl u.val) w.val≤1:=by
      have hwl:w.val<(zN n Fl u.val).length:=by omega
      have:g (zN n Fl u.val) w.val=(zN n Fl u.val)[w.val]:=by simp [g,qf,hwl]
      rw [this]; exact ho _ (qn hwl)
     exact ha▸q8.mpr (by omega)
   · intro hh i hi
     have hgi:g (gg Fl r) i=(gg Fl r)[i]:=by rw [g,qf,List.getElem?_eq_getElem hi]; rfl
     have hG:(gg Fl r)[i]<n:=hFl_lt _ hc _ (qn hi)
     have h1:g (zN n Fl u.val) (gg Fl r)[i]=1:=q8.mp (ha.symm▸hh (zB.mpr (show (⟨(gg Fl r)[i],hG⟩:Fin n).val∈gg Fl r from qn hi)))
     rw [hgi,h1]
  have hA:vh F (qr F u)=
   ((Finset.range Fl.length).filter (fun r=>qx n (gg Fl r)⊆qr F u)).card:=by
   symm
   refine Finset.card_nbij (fun r=>qx n (gg Fl r)) ?_ ?_ ?_
   · intro r hr; rcases qa.mp hr with ⟨hrl,hh⟩
     have hc:gg Fl r∈Fl:=by
      have:gg Fl r=Fl[r]'(vi.mp hrl):=by simp [gg,qf,vi.mp hrl]
      rw [this]; exact qn (vi.mp hrl)
     exact qa.mpr ⟨zj.mpr ⟨_,hc,rfl⟩,hh⟩
   · intro r₁ h1 r₂ h2 heq;by_contra hne
     exact hFl_inj r₁ (vi.mp (qa.mp h1).1)
      r₂ (vi.mp (qa.mp h2).1) hne heq
   · intro R hR; rcases qa.mp hR with ⟨hRF,hh⟩
     rcases zj.mp hRF with ⟨v,hD,rfl⟩
     rcases vI.mp hD with ⟨r,hr,rfl⟩
     have hgg:gg Fl r=Fl[r]:=by simp [gg,qf,hr]
     exact ⟨r,qa.mpr ⟨vi.mpr hr,hgg▸hh⟩,hgg▸rfl⟩
  rw [hA,Finset.card_filter]
  have hg:∀ (f:ℕ→ℕ) (m:ℕ),((List.range m).map f).sum=∑ r∈Finset.range m,f r:=by
   intro f m; induction m with
   | zero=>simp
   | succ m ih=>rw [zP,List.map_append,List.map_singleton,List.sum_append,
      List.sum_singleton,Finset.sum_range_succ,ih]
  rw [yG,hg];refine Finset.sum_congr rfl fun r hr=>?_
  have hrl:=vi.mp hr;by_cases hs:qx n (gg Fl r)⊆qr F u
  · rw [if_pos hs,if_pos ((hf r hrl).mpr hs)]
  · rw [if_neg hs,if_neg (fun h0=>hs ((hf r hrl).mp h0))]
 set reps:(Q3 n):=Finset.univ.filter (fun u=>y1 n um Fl u.val=1)
 have h8:∀ P:Q3 n→Prop,[DecidablePred P]→
  (reps.filter (fun u=>P (qr F u))).card=((vC U F).filter P).card:=by
  intro P _;refine Finset.card_nbij (fun u=>qr F u) ?_ ?_ ?_
  · intro u hu; rcases qa.mp hu with ⟨hur,hP⟩
    have huU:=((h5 u).mp (qa.mp hur).2).1;exact qa.mpr ⟨qN.mpr ⟨u,huU,rfl⟩,hP⟩
  · intro u₁ h1 u₂ h2 heq;dsimp only at heq;have hr1:=(h5 u₁).mp (qa.mp (qa.mp h1).1).2;have hr2:=(h5 u₂).mp (qa.mp (qa.mp h2).1).2;have h12:u₁.val≤u₂.val:=hr1.2 u₂ (heq▸z7 F u₂);have h21:u₂.val≤u₁.val:=hr2.2 u₁ (heq.symm▸z7 F u₁);exact Fin.ext (le_antisymm h12 h21)
  · intro C hC; rcases qa.mp hC with ⟨hCp,hPC⟩
    rcases qN.mp hCp with ⟨u₀,hu₀,he⟩
    have hp:C.Nonempty:=⟨u₀,he▸z7 F u₀⟩;set m:=C.min' hp;have hmC:m∈C:=Finset.min'_mem C hp;have hcm:qr F m=C:=by rw [← he]; exact vG F (he▸hmC)
    have hmU:m∈U:=ye hFU hu₀ (he▸hmC)
    exact ⟨m,qa.mpr ⟨qa.mpr ⟨qJ _,
     (h5 m).mpr ⟨hmU,fun v hv=>Finset.min'_le C v (hcm▸hv)⟩⟩,hcm.symm▸hPC⟩,hcm⟩
 have h9:∀ f:ℕ→ℕ,((List.range n).map f).sum=∑ u:Fin n,f u.val:=fun f=>by
  rw [Fin.sum_univ_eq_sum_range f n]
  have hsr:∀ m,((List.range m).map f).sum=∑ i∈Finset.range m,f i:=by
   intro m; induction m with
   | zero=>simp
   | succ k ih=>rw [zP,List.map_append,List.map_singleton,List.sum_append,
      List.sum_singleton,Finset.sum_range_succ,ih]
  exact hsr n
 have hy:yT n um Fl=1↔jj U F:=by
  simp only [yT]
  have h1:((List.range n).map (fun u=>
   if y1 n um Fl u=1 then (if yA n Fl u<2 * yG n Fl u then 1 else 0) else 0)).sum=
   ((vC U F).filter (fun C=>C.card<2 * vh F C)).card:=by
   rw [h9,← h8 (fun C=>C.card<2 * vh F C),Finset.card_filter];rw [Finset.sum_filter];refine Finset.sum_congr rfl fun u _=>?_
   simp only [reps,qa,qJ,true_and,h7 u,h6 u]
  rw [h1];split_ifs with h0
  · simp only [zero_ne_one,false_iff,jj,not_exists,not_and,not_lt];intro C hC; by_contra hlt
    have:0<((vC U F).filter (fun C=>C.card<2 * vh F C)).card:=qU.mpr ⟨C,qa.mpr ⟨hC,by omega⟩⟩
    omega
  · simp only [true_iff,jj];rcases qU.mp (Nat.pos_of_ne_zero h0) with ⟨C,hC⟩
    exact ⟨C,(qa.mp hC).1,(qa.mp hC).2⟩
 have ht:kN n um Fl=(kX U F).card:=by
  rw [kN,h9,kX,← h8 (fun C=>C.card=2 * vh F C),Finset.card_filter,Finset.sum_filter];refine Finset.sum_congr rfl fun u _=>?_
  simp only [reps,qa,qJ,true_and,h7 u,h6 u]
 have hq:kx n um Fl=(ky U F).card:=by
  rw [kx,h9,ky,← h8 (fun C=>C.card=2 * vh F C+1),Finset.card_filter,Finset.sum_filter];refine Finset.sum_congr rfl fun u _=>?_
  simp only [reps,qa,qJ,true_and,h7 u,h6 u]
 have hn:(vS n t um Fl).length=t∧(∀ b∈vS n t um Fl,b≤1)∧
  qV (vS n t um Fl)=((ky U F).prod Finset.card) % 2 ^ t:=by
  have hF:∀ k,k≤n→
   let p:=(vZ n t um Fl)^[k] (0,qA t 1)
   p.1=k∧p.2.length=t∧(∀ b∈p.2,b≤1)∧
   qV p.2=((Finset.range k).prod (fun u=>if y1 n um Fl u=1∧yA n Fl u=2 * yG n Fl u+1 then yA n Fl u else 1)) % 2 ^ t:=by
   intro k; induction k with
   | zero=>
     intro _; refine ⟨rfl,zl t 1,zS t 1,?_⟩
     simp only [Function.iterate_zero_apply];rw [vz]; simp
   | succ k ih=>
     intro hk;rcases ih (by omega) with ⟨h1,h2,h3,h4⟩
     rw [qM,Finset.prod_range_succ];dsimp only [vZ];rw [h1];by_cases hj:y1 n um Fl k=1
     · by_cases htr:yA n Fl k=2 * yG n Fl k+1
       · rw [if_pos hj,if_pos htr,if_pos ⟨hj,htr⟩];have hm:=wb t _ (qA t (yA n Fl k)) h2 (zl t _) h3 (zS t _);refine ⟨rfl,hm.1,hm.2.1,?_⟩
         rw [hm.2.2,h4,vz,Nat.mod_mul_mod,Nat.mul_mod_mod]
       · rw [if_pos hj,if_neg htr,if_neg (fun h=>htr h.2),mul_one];exact ⟨rfl,h2,h3,h4⟩
     · rw [if_neg hj,if_neg (fun h=>hj h.1),mul_one];exact ⟨rfl,h2,h3,h4⟩
  rcases hF n le_rfl with ⟨_,hE,hb,hB⟩
  refine ⟨hE,hb,hB.trans ?_⟩
  congr 1;rw [← Fin.prod_univ_eq_prod_range (fun u=>if y1 n um Fl u=1∧yA n Fl u=2 * yG n Fl u+1 then yA n Fl u else 1) n];rw [← Finset.prod_filter];refine Finset.prod_nbij (fun u=>qr F u) ?_ ?_ ?_ ?_
  · intro u hu;rcases qa.mp hu with ⟨_,hr,htr⟩
    rw [h7 u,h6 u] at htr;exact qa.mpr ⟨qN.mpr ⟨u,((h5 u).mp hr).1,rfl⟩,htr⟩
  · intro u₁ h1 u₂ h2 heq;dsimp only at heq;have hr1:=(h5 u₁).mp (qa.mp h1).2.1;have hr2:=(h5 u₂).mp (qa.mp h2).2.1;exact Fin.ext (le_antisymm (hr1.2 u₂ (heq▸z7 F u₂)) (hr2.2 u₁ (heq.symm▸z7 F u₁)))
  · intro C hC;rcases qa.mp hC with ⟨hCp,hCc⟩
    rcases qN.mp hCp with ⟨u₀,hu₀,he⟩
    have hp:C.Nonempty:=⟨u₀,he▸z7 F u₀⟩;set m:=C.min' hp;have hmC:m∈C:=Finset.min'_mem C hp;have hcm:qr F m=C:=by rw [← he]; exact vG F (he▸hmC)
    have hmU:m∈U:=ye hFU hu₀ (he▸hmC)
    refine ⟨m,qa.mpr ⟨qJ _,
     (h5 m).mpr ⟨hmU,fun v hv=>Finset.min'_le C v (hcm▸hv)⟩,
     by rw [h7 m,h6 m,hcm]; exact hCc⟩,hcm⟩
  · intro u _; exact h7 u
 exact ⟨h5,h7,h6,hy,ht,hq,hn.1,hn.2.1,hn.2.2⟩
lemma qas (t cols T:ℕ):
 (yC t cols T).length=cols∧
 (∀ v∈yC t cols T,v.length=t∧∀ b∈v,b≤1)∧
 ∀ m<cols,qV (gg (yC t cols T) m)=vV T m % 2 ^ t:=by
 have he:∀ r,
  let prev0:=(List.range cols).map (fun _=>qA t 0)
  let cur0:=(List.range cols).map (fun m=>if m=0 then qA t 1 else qA t 0);let p:=(vW t cols)^[r] (0,prev0,cur0)
  p.1=r∧
  p.2.1.length=cols∧p.2.2.length=cols∧
  (∀ v∈p.2.1,v.length=t∧∀ b∈v,b≤1)∧
  (∀ v∈p.2.2,v.length=t∧∀ b∈v,b≤1)∧
  (∀ m<cols,qV (gg p.2.2 m)=vV r m % 2 ^ t)∧
  (∀ r':ℕ,r=r'+1→∀ m<cols,qV (gg p.2.1 m)=vV r' m % 2 ^ t):=by
  intro r; induction r with
  | zero=>
    dsimp only [Function.iterate_zero_apply];refine ⟨rfl,by simp,by simp,?_,?_,?_,fun _ h=>by omega⟩
    · intro v hv; simp only [qQ] at hv; rcases hv with ⟨_,_,rfl⟩
      exact ⟨zl t 0,zS t 0⟩
    · intro v hv; simp only [qQ] at hv; rcases hv with ⟨_,_,rfl⟩
      split_ifs
      · exact ⟨zl t 1,zS t 1⟩
      · exact ⟨zl t 0,zS t 0⟩
    · intro m hm;rw [yK cols m _ hm]
      cases m with
      | zero=>rw [if_pos rfl,vz]; rfl
      | succ m=>rw [if_neg (Nat.succ_ne_zero m),vz]; rfl
  | succ r ih=>
    dsimp only;rcases ih with ⟨h1,h2,h3,h4,h5,h9,h8⟩
    rw [qM];dsimp only [vW];rw [h1]
    set p:=(vW t cols)^[r] (0,(List.range cols).map (fun _=>qA t 0),
     (List.range cols).map (fun m=>if m=0 then qA t 1 else qA t 0))
    refine ⟨rfl,h3,by simp,h5,?_,?_,fun r' hr' m hm=>by
     have h7:r'=r:=by omega
     subst h7; exact h9 m hm⟩
    · intro v hv; simp only [qQ] at hv; rcases hv with ⟨m,_,rfl⟩
      split_ifs
      · exact ⟨zl t 1,zS t 1⟩
      · rcases kn _ _ t with ⟨hl,hb,_⟩; exact ⟨hl,hb⟩
    · intro m hm;rw [yK cols m _ hm]
      cases m with
      | zero=>rw [if_pos rfl,vz]; cases r <;> rfl
      | succ m=>
        rw [if_neg (Nat.succ_ne_zero m),Nat.add_sub_cancel]
        have h6:gg p.2.2 (m+1)∈p.2.2:=by
         have:gg p.2.2 (m+1)=p.2.2[m+1]'(by omega):=by simp [gg,qf,h3,hm]
         rw [this]; exact qn (by omega)
        have h0:gg p.2.1 m∈p.2.1:=by
         have:gg p.2.1 m=p.2.1[m]'(by omega):=by simp [gg,qf,h2,show m<cols by omega]
         rw [this]; exact qn (by omega)
        have hm1:=wb t (qA t r) (gg p.2.1 m) (zl t r)
         (h4 _ h0).1 (zS t r) (h4 _ h0).2
        have ha1:=j5 t (gg p.2.2 (m+1)) (kK t (qA t r) (gg p.2.1 m))
         (h5 _ h6).1 hm1.1 (h5 _ h6).2 hm1.2.1
        rw [ha1.2.2,hm1.2.2,vz,h9 (m+1) hm]
        cases r with
        | zero=>simp [vV]
        | succ r'=>rw [h8 r' rfl m (by omega)];simp only [vV];rw [Nat.add_mod,Nat.mod_mod,Nat.mod_mod,Nat.mul_mod,Nat.mod_mod,Nat.mod_mod,← Nat.mul_mod,← Nat.add_mod]
 rcases he T with ⟨_,_,hc,_,hbd,ha,_⟩
 exact ⟨hc,hbd,ha⟩
end ki
namespace ki
open PEqualNP.Library Lib.qC Lib.ve Lib.j4 Lib.R Alg jC
noncomputable def PL:Q5:=Polynomial.C 100 * Polynomial.X ^ 2+Polynomial.C 100 * Polynomial.X+Polynomial.C 100
def z0 {n:ℕ} (C:Q2) (idx:Q1):(Q4 n):=((y0 C idx).map (fun row=>qx n [g row 0,g row 1])).toFinset
lemma qa6 {n t:ℕ} {H:(Q4 n)} {C:Q2}
 (ht:1≤t)
 (hC_props:∀ i<C.length,let row:=gg C i
   g row 0<g row 1∧g row 1<n∧g row 2<g row 3∧g row 3<n∧
   qx n [g row 0,g row 1]∈cores H∧
   outer H (qx n [g row 0,g row 1])=qx n [g row 2,g row 3])
 (hC_inj:∀ i<C.length,∀ j<C.length,qx n [g (gg C i) 0,g (gg C i) 1]=qx n [g (gg C j) 0,g (gg C j) 1]→i=j)
 (hC_surj:∀ c∈cores H,∃ i<C.length,qx n [g (gg C i) 0,g (gg C i) 1]=c)
 (val:Q4 n→ℕ):
 ((Finset.range ((C.length+1) ^ (t-1))).filter (fun q=>vH C.length (zL (C.length+1) (t-1) q)=1)).sum
   (fun q=>val (z0 C (zL (C.length+1) (t-1) q)))=
 ((cores H).powerset.filter (fun S=>S.card<t)).sum val:=by
 classical
 set m:=C.length;set k:=t-1
 have hh:∀ (L:Q1),(∀ a∈L,a< m)→L.length≤k→
  y0 C (L++List.replicate (k-L.length) m)=L.map (fun a=>gg C a):=by
  intro L h5 h9;set idx:=L++List.replicate (k-L.length) m;have h3:idx.length=k:=by simp [idx]; omega
  have hy:∀ r,r≤k→
   (List.range r).flatMap (fun i=>if g idx i< m then [gg C (g idx i)] else [])=
     (L.take r).map (fun a=>gg C a):=by
   intro r; induction r with
   | zero=>intro _; simp
   | succ r ih=>
     intro hr;rw [zP,List.flatMap_append,List.flatMap_singleton,ih (by omega)];by_cases hrl:r<L.length
     · have hgr:g idx r=L[r]:=by
        have:idx[r]'(by omega)=L[r]:=List.getElem_append_left hrl;simp [g,qf,show r< idx.length by omega,this]
       rw [hgr,if_pos (h5 _ (qn hrl)),List.take_succ_eq_append_getElem hrl,List.map_append,List.map_singleton]
     · have hgr:g idx r=m:=by
        have h1:idx[r]'(by omega)=(List.replicate (k-L.length) m)[r-L.length]'(by simp; omega):=List.getElem_append_right (by omega)
        rw [List.getElem_replicate] at h1;simp [g,qf,show r< idx.length by omega,h1]
       rw [hgr,if_neg (Nat.lt_irrefl m),qX,
        vo (by omega),vo (by omega)]
  rw [y0,h3,hy k le_rfl,vo h9]
 have h0:∀ (L:Q1),L.Pairwise (·<·)→(∀ a∈L,a< m)→L.length≤k→
  let S:=z0 (n:=n) C (L++List.replicate (k-L.length) m)
  S⊆cores H∧S.card=L.length∧
  ∀ i< m,qx n [g (gg C i) 0,g (gg C i) 1]∈S↔i∈L:=by
  intro L hpw h5 h9; dsimp only;rw [z0,hh L h5 h9,List.map_map]
  have hnd:(L.map (fun a=>qx n [g (gg C a) 0,g (gg C a) 1])).Nodup:=by
   refine (List.nodup_map_iff_inj_on (qK hpw)).mpr ?_
   intro a ha b hb heq; exact hC_inj a (h5 a ha) b (h5 b hb) heq
  refine ⟨?_,?_,?_⟩
  · intro c hc; simp only [List.mem_toFinset,qQ,Function.comp_apply] at hc;rcases hc with ⟨a,ha,rfl⟩; exact (hC_props a (h5 a ha)).2.2.2.2.1
  · rw [List.toFinset_card_of_nodup (by simpa only [Function.comp_def] using hnd),zM]
  · intro i hi; simp only [List.mem_toFinset,qQ,Function.comp_apply];constructor
    · rintro ⟨a,ha,heq⟩; have:=hC_inj a (h5 a ha) i hi heq; subst this; exact ha
    · intro hiL; exact ⟨i,hiL,rfl⟩
 let listOfS:Q4 n→Q1:=fun S=>(List.range m).filter (fun i=>decide (qx n [g (gg C i) 0,g (gg C i) 1]∈S))
 let idxOfS:Q4 n→Q1:=fun S=>listOfS S++List.replicate (k-(listOfS S).length) m
 let qOfS:Q4 n→ℕ:=fun S=>zb (m+1) (idxOfS S)
 have hj:∀ S⊆cores H,
  (listOfS S).Pairwise (·<·)∧(∀ a∈listOfS S,a< m)∧
  (listOfS S).length=S.card∧
  (∀ i< m,i∈listOfS S↔qx n [g (gg C i) 0,g (gg C i) 1]∈S):=by
  intro S hS;have hpw:(listOfS S).Pairwise (·<·):=List.pairwise_lt_range.filter _
  have hlt:∀ a∈listOfS S,a< m:=fun a ha=>qw.mp (List.mem_filter.mp ha).1
  have hf:∀ i< m,i∈listOfS S↔qx n [g (gg C i) 0,g (gg C i) 1]∈S:=fun i hi=>by simp [listOfS,hi]
  have hg:(listOfS S).length=S.card:=by
   rw [← List.toFinset_card_of_nodup (qK hpw)];refine Finset.card_nbij (fun i=>qx n [g (gg C i) 0,g (gg C i) 1]) ?_ ?_ ?_
   · intro i hi; exact (hf i (hlt i (List.mem_toFinset.mp hi))).mp (List.mem_toFinset.mp hi)
   · intro i h1 j h2 heq;exact hC_inj i (hlt i (List.mem_toFinset.mp h1)) j (hlt j (List.mem_toFinset.mp h2)) heq
   · intro c hc; rcases hC_surj c (hS hc) with ⟨i,hi,rfl⟩
     exact ⟨i,List.mem_toFinset.mpr ((hf i hi).mpr hc),rfl⟩
  exact ⟨hpw,hlt,hg,hf⟩
 have h6:∀ (L:Q1),L.Pairwise (·<·)→(∀ a∈L,a< m)→L.length≤k→
  vH m (L++List.replicate (k-L.length) m)=1:=by
  intro L hpw h5 h9;set idx:=L++List.replicate (k-L.length) m;have hg:idx.length=k:=by simp [idx]; omega
  rw [wK]
  have ho:∀ i<k,g idx i=if h:i<L.length then L[i] else m:=by
   intro i hi;have h1:g idx i=idx[i]'(by omega):=by simp [g,qf,hg,hi]
   rw [h1];split_ifs with hil
   · exact List.getElem_append_left hil
   · have h2:idx[i]'(by omega)=(List.replicate (k-L.length) m)[i-L.length]'(by simp; omega):=
      List.getElem_append_right (by omega)
     rwa [List.getElem_replicate] at h2
  refine ⟨fun i hi=>?_,fun i hi=>?_⟩
  · rw [ho i (by omega)]; split_ifs with hil
    · exact Nat.le_of_lt (h5 _ (qn hil))
    · exact le_rfl
  · rw [ho i (by omega),ho (i+1) (by omega)];split_ifs with h1 h2
    · exact Or.inl ((List.pairwise_iff_getElem.mp hpw) i (i+1) h1 h2 (by omega))
    · exact Or.inl (h5 _ (qn h1))
    · omega
    · exact Or.inr ⟨rfl,rfl⟩
 have hm:∀ u:Q1,(∀ d∈u,d< m+1)→zb (m+1) u<(m+1) ^ u.length:=by
  intro u; induction u with
  | nil=>intro _; simp [zb]
  | cons d u ih=>intro hu; simp only [zb,qI,pow_succ];have hd0:d< m+1:=hu d (by simp);have hu0:=ih (fun x hx=>hu x (by simp [hx]));have h1:(m+1) * (zb (m+1) u+1)≤(m+1) * (m+1) ^ u.length:=Nat.mul_le_mul_left _ hu0;nlinarith
 refine Finset.sum_nbij' (fun q=>z0 C (zL (m+1) k q)) qOfS ?_ ?_ ?_ ?_ (fun _ _=>rfl)
 · intro q hq;rcases qa.mp hq with ⟨hqr,hp⟩
   rcases ui hp with ⟨L,hpw,h5,h9,h4⟩
   have hg:(zL (m+1) k q).length=k:=(kk (m+1) k q (Nat.succ_pos m)).1;rw [hg] at h9 h4;rw [h4];rcases h0 L hpw h5 h9 with ⟨he,hl,_⟩
   exact qa.mpr ⟨v7.mpr he,by omega⟩
 · intro S hS;rcases qa.mp hS with ⟨hSp,hl⟩
   have he:=v7.mp hSp;rcases hj S he with ⟨hpw,hlt,hg,_⟩
   have hle:(listOfS S).length≤k:=by omega
   have h3:(idxOfS S).length=k:=by simp [idxOfS]; omega
   have h8:∀ d∈idxOfS S,d< m+1:=by intro d hd; simp only [idxOfS,List.mem_append,List.mem_replicate] at hd;rcases hd with h1|⟨_,rfl⟩; exact Nat.lt_succ_of_lt (hlt d h1); exact Nat.lt_succ_self m
   have hn:qOfS S<(m+1) ^ k:=h3▸hm (idxOfS S) h8
   have htb:zL (m+1) k (qOfS S)=idxOfS S:=h3▸kE (m+1) (idxOfS S) (Nat.succ_pos m) h8
   exact qa.mpr ⟨vi.mpr hn,htb▸h6 _ hpw hlt hle⟩
 · intro q hq;rcases qa.mp hq with ⟨hqr,hp⟩
   have hn:=vi.mp hqr;rcases kk (m+1) k q (Nat.succ_pos m) with ⟨hg,_,hv⟩
   rcases ui hp with ⟨L,hpw,h5,h9,h4⟩
   rw [hg] at h9 h4;have h7:=h0 L hpw h5 h9
   have hz:listOfS (z0 (n:=n) C (zL (m+1) k q))=L:=by
    have hw:(listOfS (z0 (n:=n) C (zL (m+1) k q))).Pairwise (·<·):=List.pairwise_lt_range.filter _
    have hk:∀ i,i∈listOfS (z0 (n:=n) C (zL (m+1) k q))↔i∈L:=by
     intro i; simp only [listOfS,List.mem_filter,qw,decide_eq_true_eq];constructor
     · rintro ⟨hi,hf⟩; rw [h4] at hf; exact (h7.2.2 i hi).mp hf
     · intro hiL; exact ⟨h5 i hiL,h4.symm▸(h7.2.2 i (h5 i hiL)).mpr hiL⟩
    have hs:∀ {A B:Q1},A.Pairwise (·<·)→B.Pairwise (·<·)→(∀ x,x∈A↔x∈B)→A=B:=by
     intro A; induction A with
     | nil=>
       intro B _ _ h; cases B with
       | nil=>rfl
       | cons b _=>exfalso; exact absurd ((h b).mpr (by simp)) (by simp)
     | cons a A ih=>
       intro B hpA hpB h; cases B with
       | nil=>exfalso; exact absurd ((h a).mp (by simp)) (by simp)
       | cons b B=>
         rcases List.pairwise_cons.mp hpA with ⟨haA,hpA'⟩
         rcases List.pairwise_cons.mp hpB with ⟨hbB,hpB'⟩
         have hab:a=b:=by
          have h1:=(h a).mp (by simp); have h2:=(h b).mpr (by simp);simp only [zT] at h1 h2;rcases h1 with rfl|h1'; rfl
          rcases h2 with rfl|h2'; rfl
          have:=haA b h2'; have:=hbB a h1'; omega
         subst hab;congr 1;refine ih hpA' hpB' fun x=>?_
         have hx:=h x; simp only [zT] at hx;constructor
         · intro hxA; rcases hx.mp (Or.inr hxA) with rfl|hxB
           · exact absurd (haA x hxA) (Nat.lt_irrefl _)
           · exact hxB
         · intro hxB; rcases hx.mpr (Or.inr hxB) with rfl|hxA
           · exact absurd (hbB x hxB) (Nat.lt_irrefl _)
           · exact hxA
    exact hs hw hpw hk
   simp only [qOfS,idxOfS,hz,← h4];exact hv hn
 · intro S hS;rcases qa.mp hS with ⟨hSp,hl⟩
   have he:=v7.mp hSp;rcases hj S he with ⟨hpw,hlt,hg,hf⟩
   have hle:(listOfS S).length≤k:=by omega
   have h3:(idxOfS S).length=k:=by simp [idxOfS]; omega
   have h8:∀ d∈idxOfS S,d< m+1:=by intro d hd; simp only [idxOfS,List.mem_append,List.mem_replicate] at hd;rcases hd with h1|⟨_,rfl⟩; exact Nat.lt_succ_of_lt (hlt d h1); exact Nat.lt_succ_self m
   have htb:zL (m+1) k (qOfS S)=idxOfS S:=h3▸kE (m+1) (idxOfS S) (Nat.succ_pos m) h8
   rw [htb];have h7:=h0 (listOfS S) hpw hlt hle;ext c; constructor
   · intro hc;rcases hC_surj c (h7.1 hc) with ⟨i,hi,rfl⟩
     exact (hf i hi).mp ((h7.2.2 i hi).mp hc)
   · intro hc;rcases hC_surj c (he hc) with ⟨i,hi,rfl⟩
     exact (h7.2.2 i hi).mpr ((hf i hi).mpr hc)
lemma wT {n t:ℕ} {H:(Q4 n)} {Hraw:Q2}
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2)
 (hTr:∀ u v w:Fin n,u≠v→u≠w→v≠w→(zZ Hraw u.val v.val w.val=1↔({u,v,w}:Q3 n)∈H))
 {idx:Q1} (hcan:vH (yH n Hraw).length idx=1) (hidx_len:idx.length=t-1):
 let C:=yH n Hraw;let om:=yN n C;let B:=kt n Hraw om;let S:(Q4 n):=z0 C idx;let Srows:=y0 C idx;let j:=Srows.length;let outF:=yU Srows;let uMask:=yX n om outF;let F0:=vU uMask B;let ps:=kD n uMask F0;let ok:=vH C.length idx * yu outF * (1-ps.dead) * (1-yT n ps.um ps.F)
 S⊆cores H∧j=S.card∧
 (∀ s≤n / 2,
   let contrib:Q1:=
    if ok=1 then
     let nc:=kN n ps.um ps.F
     let nt:=kx n ps.um ps.F;let tp:=vS n t ps.um ps.F;let factor:=ke t (j+nc) tp;let mRow:=yC t (n / 2+1) nt;let shift:=C.length+j+ps.kF+ps.F.length
     if s<shift then qA t 0 else kK t factor (gg mRow (s-shift))
    else qA t 0
   contrib.length=t∧(∀ b∈contrib,b≤1)∧
   qV contrib=
    (if (S.biUnion (outer H)).card=2 * S.card∧(cores H).card+S.card≤ s then 2 ^ S.card * (q7 (left H S) (reduced H S) (s-(cores H).card-S.card)).card
    else 0) % 2 ^ t):=by
 intro C om B S Srows j outF uMask F0 ps ok;rcases jY hH3 hdeg hTr with ⟨h5,h0i,hC_surj,h0h,hom_l,h0s,hN⟩
 rcases jX hH3 hTr h0s hN with ⟨h6,h11,h03,h0l⟩
 rcases ui hcan with ⟨L,h0z,hh,h10,hY⟩
 have ht:∀ r (hr:r< idx.length),
  idx[r]=(L++List.replicate (idx.length-L.length) C.length)[r]'(by simp; omega):=fun r hr=>by
  have hq:=congrArg (fun l=>l[r]?) hY;rw [List.getElem?_eq_getElem hr,List.getElem?_eq_getElem (by simp; omega)] at hq
  exact Option.some.inj hq
 have h3:y0 C idx=L.map (fun a=>gg C a):=by
  have h0b:∀ r,r≤ idx.length→
   (List.range r).flatMap (fun i=>if g idx i<C.length then [gg C (g idx i)] else [])=
     (L.take r).map (fun a=>gg C a):=by
   intro r; induction r with
   | zero=>intro _; simp
   | succ r ih=>
     intro hr; rw [zP,List.flatMap_append,List.flatMap_singleton,ih (by omega)];by_cases hrl:r<L.length
     · have hgr:g idx r=L[r]:=by
        have:idx[r]'(by omega)=L[r]:=(ht r (by omega)).trans (List.getElem_append_left hrl);simp [g,qf,show r< idx.length by omega,this]
       rw [hgr,if_pos (hh _ (qn hrl)),List.take_succ_eq_append_getElem hrl,List.map_append,List.map_singleton]
     · have hgr:g idx r=C.length:=by
        have h1:idx[r]'(by omega)=(List.replicate (idx.length-L.length) C.length)[r-L.length]'(by simp; omega):=(ht r (by omega)).trans (List.getElem_append_right (by omega))
        rw [List.getElem_replicate] at h1;simp [g,qf,show r< idx.length by omega,h1]
       rw [hgr,if_neg (Nat.lt_irrefl _),qX,
        vo (by omega),vo (by omega)]
  rw [y0,h0b idx.length le_rfl,vo h10]
 have h0g:S⊆cores H:=by intro c hc; simp only [S,z0,h3,List.map_map,List.mem_toFinset,qQ,Function.comp_apply] at hc;rcases hc with ⟨a,ha,rfl⟩; exact (h5 a (hh a ha)).2.2.2.2.1
 have ho:j=S.card:=by
  have hnd:(L.map (fun a=>qx n [g (gg C a) 0,g (gg C a) 1])).Nodup:=
   (List.nodup_map_iff_inj_on (qK h0z)).mpr fun a ha b hb heq=>h0i a (hh a ha) b (hh b hb) heq
  simp only [j,S,Srows,z0,h3,List.map_map,Function.comp_def,List.toFinset_card_of_nodup hnd,zM]
 have hI:outF.length=2 * S.card:=by
  have h0b:∀ (M:Q2),(yU M).length=2 * M.length:=by
   intro M; simp only [yU]
   have hg:∀ k,((List.range k).flatMap (fun r=>[g (gg M r) 2,g (gg M r) 3])).length=2 * k:=by
    intro k; induction k with
    | zero=>simp
    | succ k ih=>rw [zP,List.flatMap_append,List.flatMap_singleton,List.length_append,ih]; simp; omega
   exact hg M.length
  have h1:outF.length=2 * j:=h0b Srows;rw [h1,ho]
 have hM:∀ a∈outF,a<n:=by
  intro a ha; simp only [outF,yU,List.mem_flatMap,qw,zT,List.not_mem_nil,or_false] at ha;rcases ha with ⟨r,hr,h1|h1⟩
  · have hrL:r<L.length:=by simpa [Srows,h3] using hr
    have hgg:gg Srows r=gg C L[r]:=by simp [gg,qf,Srows,h3,List.getElem?_eq_getElem hrL]
    rcases h5 L[r] (hh _ (qn hrL)) with ⟨_,_,h23,h3n,_,_⟩
    rw [h1,hgg]; exact lt_trans h23 h3n
  · have hrL:r<L.length:=by simpa [Srows,h3] using hr
    have hgg:gg Srows r=gg C L[r]:=by simp [gg,qf,Srows,h3,List.getElem?_eq_getElem hrL]
    rcases h5 L[r] (hh _ (qn hrL)) with ⟨_,_,h23,h3n,_,_⟩
    rw [h1,hgg]; exact h3n
 have hl:qx n outF=S.biUnion (outer H):=by
  ext u; simp only [zB,qj,outF,yU,List.mem_flatMap,qw,zT,List.not_mem_nil,or_false];constructor
  · rintro ⟨r,hr,hu⟩;have hrL:r<L.length:=by simpa [Srows,h3] using hr
    have hgg:gg Srows r=gg C L[r]:=by simp [gg,qf,Srows,h3,List.getElem?_eq_getElem hrL]
    have hp:=h5 L[r] (hh _ (qn hrL));refine ⟨qx n [g (gg C L[r]) 0,g (gg C L[r]) 1],?_,?_⟩
    · simp only [S,z0,h3,List.map_map,List.mem_toFinset,qQ,Function.comp_apply];exact ⟨L[r],qn hrL,rfl⟩
    · rw [hp.2.2.2.2.2,zB,zT,z4];rw [hgg] at hu; exact hu
  · rintro ⟨c,hcS,huo⟩;simp only [S,z0,h3,List.map_map,List.mem_toFinset,qQ,Function.comp_apply] at hcS;rcases hcS with ⟨a,haL,rfl⟩
    rcases vI.mp haL with ⟨r,hrL,rfl⟩
    have hr:r<Srows.length:=by simp [Srows,h3,hrL]
    have hgg:gg Srows r=gg C L[r]:=by simp [gg,qf,Srows,h3,List.getElem?_eq_getElem hrL]
    have hp:=h5 L[r] (hh _ (qn hrL));rw [hp.2.2.2.2.2,zB,zT,z4] at huo;exact ⟨r,hr,hgg.symm▸huo⟩
 have h9:yu outF=1↔(S.biUnion (outer H)).card=2 * S.card:=by rw [ww,← uU hM,hl,hI]
 have h7:qL n uMask=left H S:=by
  have h0p:∀ {M:Q1},M.sum=0↔∀ x∈M,x=0:=by
   intro M; induction M with
   | nil=>simp
   | cons a M ih=>simp only [List.sum_cons,Nat.add_eq_zero_iff,ih,zT,forall_eq_or_imp]
  ext u; simp only [q8,uMask,yX,yc,left,qg,← hN,← hl,zB]
  have h0t:((List.range outF.length).map (fun i=>if g outF i=u.val then 1 else 0)).sum=0↔
   u.val∉outF:=by
   rw [h0p]; simp only [qQ,qw,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂];constructor
   · intro h hu; rcases vI.mp hu with ⟨i,hi,hiu⟩
     have hgi:g outF i=u.val:=by simp [g,qf,hi,hiu]
     have:=h i hi; rw [hgi,if_pos rfl] at this; omega
   · intro hno i hi;have hgi:g outF i=outF[i]:=by simp [g,qf,hi]
     rw [hgi,if_neg (fun (e:outF[i]=u.val)=>hno (e▸qn hi))]
  by_cases h1:g om u.val=1
  · rw [if_pos h1]; split_ifs with h0
    · exact ⟨fun _=>⟨h1,h0t.mp h0⟩,fun _=>rfl⟩
    · exact ⟨fun h=>absurd h (by decide),fun ⟨_,hn⟩=>(h0 (h0t.mpr hn)).elim⟩
  · rw [if_neg h1];exact ⟨fun h=>absurd h (by decide),fun ⟨h,_⟩=>(h1 h).elim⟩
 have hT:qR n F0=reduced H S:=by
  ext R; simp only [zj,reduced,qN,F0,vU,qQ,qw];constructor
  · rintro ⟨v,⟨r,hr,rfl⟩,rfl⟩;have hgg:gg B r=B[r]:=by simp [gg,qf,hr]
    have hBp:=h6 _ (hgg▸qn hr);have hfm:=(vb (um:=uMask) hBp.2.2.1).1;rw [h7] at hfm;exact ⟨qx n (gg B r),hBp.2.2.2,hfm.symm⟩
  · rintro ⟨R₀,hR₀,rfl⟩;rcases zj.mp (h03.symm▸hR₀) with ⟨v,hvB,rfl⟩
    rcases vI.mp hvB with ⟨r,hr,rfl⟩
    have hgg:gg B r=B[r]:=by rw [gg,qf,List.getElem?_eq_getElem hr]; rfl
    have hfm:=(vb (um:=uMask) (h6 _ hvB).2.2.1).1;rw [h7] at hfm;exact ⟨zc uMask (gg B r),⟨r,hr,rfl⟩,hgg.symm▸hfm⟩
 have h09:ua n (left H S) (reduced H S) ⟨0,0,uMask,F0⟩:=by
  rcases uZ n om outF with ⟨h12,h13⟩
  refine ⟨h12,h13,fun h=>by dsimp at h; omega,fun _=>?_⟩
  rw [h7,hT];refine ⟨?_,fun R₁ h1 R₂ h2 hne=>jy hH3 S h1 h2 hne,?_,fun s=>by simp⟩
  · intro R' hR';simp only [F0,vU,qQ,qw] at hR';rcases hR' with ⟨r,hr,rfl⟩
    have hgg:gg B r=B[r]:=by simp [gg,qf,hr]
    have hBp:=h6 _ (hgg▸qn hr);have hfm:=vb (um:=uMask) hBp.2.2.1;refine ⟨hfm.2.1 hBp.1,hfm.2.2,by rw [hfm.1,h7]; exact Finset.inter_subset_right,?_⟩
    rw [← zF (qK (hfm.2.1 hBp.1)) hfm.2.2,hfm.1]
    exact (qH vD).trans
     (by rw [zF (qK hBp.1) hBp.2.2.1,hBp.2.1])
  · intro h1c;refine ⟨fun i hi j hj hij heq=>?_,fun u=>?_⟩
    · have hiB:i<B.length:=by simpa [F0,vU] using hi
      have hjB:j<B.length:=by simpa [F0,vU] using hj
      have h0a:gg F0 i=zc uMask (gg B i):=yK B.length i _ hiB;have h1b:gg F0 j=zc uMask (gg B j):=yK B.length j _ hjB
      have h02:gg B i∈B:=by
       have:gg B i=B[i]:=by simp [gg,qf,hiB]
       rw [this]; exact qn hiB
      have h01:gg B j∈B:=by
       have:gg B j=B[j]:=by simp [gg,qf,hjB]
       rw [this]; exact qn hjB
      have hA:=h6 _ h02;have hH:=h6 _ h01
      have h1g:qx n (gg B i)≠qx n (gg B j):=by
       intro h0y;have h0k:gg B i=B[i]:=by simp [gg,qf,hiB]
       have h0j:gg B j=B[j]:=by simp [gg,qf,hjB]
       have h1i:(gg B i).Pairwise (·<·):=hA.1
       have h1h:(gg B j).Pairwise (·<·):=hH.1
       have h05:gg B i=gg B j:=by
        have hO:∀ a,a∈gg B i↔a∈gg B j:=fun a=>by
         constructor
         · intro ha
           have hm:(⟨a,hA.2.2.1 a ha⟩:Fin n)∈qx n (gg B j):=by rw [← h0y]; exact zB.mpr ha
           exact zB.mp hm
         · intro ha
           have hm:(⟨a,hH.2.2.1 a ha⟩:Fin n)∈qx n (gg B i):=by rw [h0y]; exact zB.mpr ha
           exact zB.mp hm
        have h0m:∀ {A₁ A₂:Q1},A₁.Pairwise (·<·)→A₂.Pairwise (·<·)→(∀ x,x∈A₁↔x∈A₂)→A₁=A₂:=by
         intro A₁; induction A₁ with
         | nil=>intro A₂ _ _ h; cases A₂ with|nil=>rfl|cons b _=>exfalso; exact absurd ((h b).mpr (by simp)) (by simp)
         | cons a A₁ ih=>
           intro A₂ hp1 hp2 h; cases A₂ with
           | nil=>exfalso; exact absurd ((h a).mp (by simp)) (by simp)
           | cons b A₂=>
             rcases List.pairwise_cons.mp hp1 with ⟨ha1,hp1'⟩
             rcases List.pairwise_cons.mp hp2 with ⟨hb2,hp2'⟩
             have hab:a=b:=by
              have h1:=(h a).mp (by simp); have h2:=(h b).mpr (by simp);simp only [zT] at h1 h2;rcases h1 with rfl|h1'; rfl; rcases h2 with rfl|h2'; rfl
              have:=ha1 b h2'; have:=hb2 a h1'; omega
             subst hab; congr 1; refine ih hp1' hp2' fun x=>?_
             have hx:=h x; simp only [zT] at hx
             exact ⟨fun h1=>(hx.mp (Or.inr h1)).resolve_left (fun e=>Nat.lt_irrefl _ (e▸ha1 x h1)),
              fun h2=>(hx.mpr (Or.inr h2)).resolve_left (fun e=>Nat.lt_irrefl _ (e▸hb2 x h2))⟩
        exact h0m h1i h1h hO
       rw [h0k,h0j] at h05;exact hij ((List.Nodup.getElem_inj_iff h11).mp h05)
      have hS:=vb (um:=uMask) hA.2.2.1;have h0x:=vb (um:=uMask) hH.2.2.1;have h0r:qx n (gg F0 i)⊆qx n (gg B i):=by rw [h0a,hS.1]; exact vD
      have h0q:qx n (gg F0 i)⊆qx n (gg B j):=by rw [heq,h1b,h0x.1]; exact vD
      have hge2i:2≤(qx n (gg F0 i)).card:=by
       have h16:gg F0 i∈F0:=by
        have:gg F0 i=F0[i]:=by simp [gg,qf,hi]
        rw [this]; exact qn hi
       rw [h0a,zF (qK (hS.2.1 hA.1)) hS.2.2,← h0a];exact h1c _ h16
      have h1a:=wE hH3 hA.2.2.2 hH.2.2.2 h1g;have:=qH (Finset.subset_inter h0r h0q);omega
    · unfold vO
      have h14:(reduced H S).filter (fun R=>u∈R)⊆
       (H.filter (fun R=>u∈R)).image (fun R=>R ∩ left H S):=by
       intro R' hR'; rcases qa.mp hR' with ⟨h1f,huR'⟩
       rcases qN.mp h1f with ⟨R,hRb,rfl⟩
       exact qN.mpr ⟨R,qa.mpr ⟨(qa.mp hRb).1,(qm.mp huR').1⟩,rfl⟩
      exact (qH h14).trans (Finset.card_image_le.trans (hdeg u))
 have h00:F0.length≤n:=by have hbl:B.length=(base H).card:=h0l;have h1a:(base H).card≤H.card:=qH (yv _ _);have hle2:=wF hH3 hdeg;simp only [F0,vU,zM,List.length_range]; omega
 rcases qbv h09 h00 with ⟨hK,hD,h8⟩
 rcases hK with ⟨hB,hC,h06,hL⟩
 refine ⟨h0g,ho,fun s hs=>?_⟩
 dsimp only;have hCl:C.length=(cores H).card:=h0h;have hD':ps.dead≤1:=hD;have h8':ps.dead=1∨∀ R∈ps.F,R.length=3:=h8
 have hE:ok=1↔yu outF=1∧ps.dead=0∧yT n ps.um ps.F=0:=by
  have h1:yu outF≤1:=by unfold yu; split_ifs <;> omega
  have h2:yT n ps.um ps.F≤1:=by unfold yT; split_ifs <;> omega
  have hcan':vH C.length idx=1:=hcan;simp only [ok,hcan',one_mul];rcases (by omega:yu outF=0∨yu outF=1) with ha|ha <;>
  rcases (by omega:ps.dead=0∨ps.dead=1) with hd|hd <;>
  rcases (by omega:yT n ps.um ps.F=0∨yT n ps.um ps.F=1) with hb|hb <;>
   simp [ha,hd,hb]
 by_cases hU:ok=1
 · rw [if_pos hU];rcases hE.mp hU with ⟨h0f,hd0,hb0⟩
   have he:(S.biUnion (outer H)).card=2 * S.card:=h9.mp h0f;rcases hL hd0 with ⟨h4,hX,hf,hZ⟩
   have hy:∀ R∈ps.F,R.length=3:=by rcases h8' with h|h; omega; exact h
   rcases hf (fun R hR=>by have:=hy R hR; omega) with ⟨hF,hG⟩
   have hF3:∀ R∈qR n ps.F,R.card=3:=by
    intro R hR; rcases zj.mp hR with ⟨v,hv,rfl⟩
    have hp:=h4 v hv;rw [zF (qK hp.1) hp.2.1,hy v hv]
   have hFU:∀ R∈qR n ps.F,R⊆qL n ps.um:=by intro R hR; rcases zj.mp hR with ⟨v,hv,rfl⟩; exact (h4 v hv).2.2.1
   have hz:ps.F.length=(qR n ps.F).card:=by
    have h1d:(Finset.range ps.F.length).card=(qR n ps.F).card:=by
     refine Finset.card_nbij (fun r=>qx n (gg ps.F r)) ?_ ?_ ?_
     · intro r hr;have hrl:=vi.mp hr
       have hgg:gg ps.F r=ps.F[r]'hrl:=by rw [gg,qf,List.getElem?_eq_getElem hrl]; rfl
       exact zj.mpr ⟨_,hgg▸qn hrl,rfl⟩
     · intro r₁ h1 r₂ h2 heq; by_contra hne;exact hF r₁ (vi.mp h1) r₂ (vi.mp h2) hne heq
     · intro R hR; rcases zj.mp hR with ⟨v,hv,rfl⟩
       rcases vI.mp hv with ⟨r,hr,rfl⟩
       have hgg:gg ps.F r=ps.F[r]:=by simp [gg,qf,hr]
       exact ⟨r,vi.mpr hr,hgg▸rfl⟩
    simpa using h1d
   rcases uD (t:=t) hB hC (fun R hR=>(h4 R hR).2.1) hFU hF with
    ⟨_,_,_,h08,hW,hV,h0o,h04,h0n⟩
   have h0u:¬ jj (qL n ps.um) (qR n ps.F):=by intro h; have h1:yT n ps.um ps.F=1:=h08.mpr h; omega
   set shift:=C.length+j+ps.kF+ps.F.length;have hk:shift=C.length+j+ps.kF+ps.F.length:=rfl;set factor:=ke t (j+kN n ps.um ps.F) (vS n t ps.um ps.F);set mRow:=yC t (n / 2+1) (kx n ps.um ps.F);have h0d:factor.length=t:=wM t _ _;have h0e:∀ b∈factor,b≤1:=qbx t _ _ h04
   have h0c:qV factor=(2 ^ (S.card+(kX (qL n ps.um) (qR n ps.F)).card) *
    (ky (qL n ps.um) (qR n ps.F)).prod Finset.card) % 2 ^ t:=by
    rw [qaJ t _ _ h0o h04,h0n,ho,hW,Nat.mul_mod_mod]
   rcases qas t (n / 2+1) (kx n ps.um ps.F) with ⟨h18,h0v,h17⟩
   by_cases hJ:s<shift
   · rw [if_pos hJ];refine ⟨zl t 0,zS t 0,?_⟩
     rw [vz];split_ifs with hw
     · rcases hw with ⟨_,h0w⟩
       rw [hk,hCl,ho,hz] at hJ;rw [hZ (s-(cores H).card-S.card)];by_cases hkF:s-(cores H).card-S.card<ps.kF
       · rw [if_pos hkF]; simp
       · rw [if_neg hkF,uV hF3 hFU hG hX];have h19:s-(cores H).card-S.card-ps.kF<(qR n ps.F).card:=by omega
         rw [if_pos (Or.inr h19)]; simp
     · simp
   · rw [if_neg hJ]
     have hshift_eq:shift=(cores H).card+S.card+ps.kF+(qR n ps.F).card:=by rw [hk,hCl,ho,hz]
     have hle_shift:(cores H).card+S.card+ps.kF+(qR n ps.F).card≤ s:=by omega
     have hQ:s-shift<n / 2+1:=by omega
     have hidx_ml:s-shift< mRow.length:=by rw [h18]; exact hQ
     have hP:gg mRow (s-shift)∈mRow:=by
      have:gg mRow (s-shift)=mRow[s-shift]'hidx_ml:=by rw [gg,qf,List.getElem?_eq_getElem hidx_ml]; rfl
      rw [this]; exact qn hidx_ml
     have h07:=wb t factor (gg mRow (s-shift)) h0d (h0v _ hP).1 h0e (h0v _ hP).2;refine ⟨h07.1,h07.2.1,?_⟩
     have hw:(S.biUnion (outer H)).card=2 * S.card∧(cores H).card+S.card≤ s:=⟨he,by omega⟩
     have h15:¬ s-(cores H).card-S.card<(kD n uMask F0).kF:=by change ¬ s-(cores H).card-S.card<ps.kF; omega
     have hnF:¬ s-(cores H).card-S.card-(kD n uMask F0).kF<(qR n (kD n uMask F0).F).card:=by change ¬ s-(cores H).card-S.card-ps.kF<(qR n ps.F).card; omega
     rw [if_pos hw,hZ (s-(cores H).card-S.card),if_neg h15,
      uV hF3 hFU hG hX,if_neg (by rintro (h|h); exact h0u h; exact hnF h)]
     rw [h07.2.2,h0c,h17 (s-shift) hQ,hV,
      show s-shift=s-(cores H).card-S.card-ps.kF-(qR n ps.F).card by omega]
     rw [Nat.mod_mul_mod,Nat.mul_mod_mod,pow_add];congr 1; ring
 · rw [if_neg hU];refine ⟨zl t 0,zS t 0,?_⟩
   rw [vz];split_ifs with hw
   · rcases hw with ⟨he,h0w⟩
     have h0f:yu outF=1:=h9.mpr he;by_cases hd1:ps.dead=1
     · rw [h06 hd1]; simp
     · have hd0:ps.dead=0:=by omega
       have hb1:yT n ps.um ps.F=1:=by
        have hb_le:yT n ps.um ps.F≤1:=by unfold yT; split_ifs <;> omega
        by_contra hne; exact hU (hE.mpr ⟨h0f,hd0,by omega⟩)
       rcases hL hd0 with ⟨h4,hX,hf,hZ⟩
       have hy:∀ R∈ps.F,R.length=3:=by rcases h8' with h|h; omega; exact h
       rcases hf (fun R hR=>by have:=hy R hR; omega) with ⟨hF,hG⟩
       have hF3:∀ R∈qR n ps.F,R.card=3:=by
        intro R hR; rcases zj.mp hR with ⟨v,hv,rfl⟩
        have hp:=h4 v hv;rw [zF (qK hp.1) hp.2.1,hy v hv]
       have hFU:∀ R∈qR n ps.F,R⊆qL n ps.um:=by intro R hR; rcases zj.mp hR with ⟨v,hv,rfl⟩; exact (h4 v hv).2.2.1
       have h1e:jj (qL n ps.um) (qR n ps.F):=(uD (t:=t) hB hC (fun R hR=>(h4 R hR).2.1) hFU hF).2.2.2.1.mp hb1
       rw [hZ (s-(cores H).card-S.card)];split_ifs
       · simp
       · rw [uV hF3 hFU hG hX,if_pos (Or.inl h1e)]; simp
   · simp
def uR (x:Q0):Q0:=
 let t:=parseT x
 if t=0 then []
 else
  let n:=parseN x
  let C:=yH n (rawH x);let K:=(C.length+1) ^ (t-1);let stEnd:=((fun s=>(stepSt s).tail)^[K]) (initSt x)
  (stepSt stEnd).tail
lemma qaR (n t:ℕ) (H:Q4 n)
 (hH3:∀ R∈H,R.card=3)
 (hdeg:∀ u:Fin n,(H.filter (fun R=>u∈R)).card≤2):
 let header:=fun k:Nat=>List.replicate k true++[false]
 let bits:=fun (w x:Nat)=>(List.range w).map (fun i=>x.testBit i)
 let x:=header n++header t++H.toList.flatMap
  (fun R=>R.toList.flatMap (fun u=>bits (n.log2+1) u.val))
 let out:=(List.range (n / 2+1)).flatMap (fun s=>bits t (q7 Finset.univ H s).card)
 uR x=out∧
 ∃ (K:ℕ) (st:ℕ→Q0),st 0=initSt x∧(∀ q<K,stepSt (st q)=true::st (q+1))∧stepSt (st K)=false::out∧(∀ q≤K,(st q).length≤PL.eval x.length)∧out.length≤PL.eval x.length∧
   K≤(x.length+2) ^ t:=by
 intro header bits x out;rcases wz n t H hH3 with ⟨hN0,hT0,hraw,hTr⟩
 have hN:parseN x=n:=hN0;have hT:parseT x=t:=hT0
 have ho:∀ u v w:Fin n,u≠v→u≠w→v≠w→
  (zZ (rawH x) u.val v.val w.val=1↔({u,v,w}:Q3 n)∈H):=hTr
 rcases jY hH3 hdeg ho with ⟨hm,h01,hM,hC_len,hQ,hR,hX⟩
 rcases jX hH3 ho hR hX with ⟨hF,hB_nd,hB_rows,hB_len⟩
 set C:=yH n (rawH x);set om:=yN n C;set B:=kt n (rawH x) om
 have hx_len_ge:n+t+2≤x.length:=by simp only [x,header,List.length_append,List.length_replicate,List.length_singleton]; omega
 have hu:C.length≤n:=by have:=w2 hH3 hdeg; omega
 have hO:B.length≤n:=by have h1:(base H).card≤H.card:=qH (yv _ _);have h2:=wF hH3 hdeg; omega
 have hf:∀ (done:ℕ) (idx:Q1) (acc:Q2),
  done≤1→idx.length≤t→(∀ d∈idx,d≤C.length)→
  acc.length=n / 2+1→(∀ v∈acc,v.length=t∧∀ b∈v,b≤1)→
  (y4 [n,t,done] om idx C B acc).length≤PL.eval x.length:=by
  intro done idx acc hdone hidx_l hidx_b h8 h9
  have h1:(zn [n,t,done]).length≤n+t+4:=by rw [vy]; simp; omega
  have h2:(zn om).length≤2 * n:=by rw [vy,hQ];have hs:=List.sum_le_length_nsmul om 1 hR;simp only [smul_eq_mul,mul_one,hQ] at hs; omega
  have h3:(zR C).length≤10 * n * n+10 * n:=by
   have hl:=kp C
   have hx:∀ v∈C,v.length=4:=by
    intro v hv; simp only [C,yH,List.mem_flatMap,qw] at hv;rcases hv with ⟨a,_,b,_,hW⟩
    split_ifs at hW <;> simp at hW
    rw [hW]; rfl
   have hw:∀ v∈C,v.length+v.sum≤4 * n+4:=by
    intro v hv; rcases vI.mp hv with ⟨i,hi,rfl⟩
    have hgg:gg C i=C[i]:=by simp [gg,qf,hi]
    have hp:=hm i hi;have h07:C[i].length=4:=hx C[i] (qn hi);rcases List.length_eq_four.mp h07 with ⟨a0,a1,a2,a3,heq⟩
    rw [heq] at hgg; rw [hgg] at hp;simp only [g,List.getD_cons_zero,List.getD_cons_succ] at hp;rw [heq]; simp; omega
   have hS:=List.sum_le_length_nsmul (C.map (fun v=>v.length+v.sum)) (4 * n+4) (by
    intro y hy; rcases qQ.mp hy with ⟨v,hv,rfl⟩; exact hw v hv)
   simp only [zM,smul_eq_mul] at hS;have h05:C.length * (4 * n+4)≤n * (4 * n+4):=Nat.mul_le_mul_right _ hu;have h0j:n * (4 * n+4)=4 * (n * n)+4 * n:=by ring
   have h3':10 * n * n=10 * (n * n):=by ring
   omega
  have h4:(zR B).length≤10 * n * n+10 * n:=by
   have hl:=kp B
   have hw:∀ v∈B,v.length+v.sum≤3 * n+3:=by
    intro v hv; rcases hF v hv with ⟨_,hvl,h0b,_⟩
    have hs:=List.sum_le_length_nsmul v n (fun a ha=>Nat.le_of_lt (h0b a ha));simp only [hvl,smul_eq_mul] at hs; omega
   have hS:=List.sum_le_length_nsmul (B.map (fun v=>v.length+v.sum)) (3 * n+3) (by
    intro y hy; rcases qQ.mp hy with ⟨v,hv,rfl⟩; exact hw v hv)
   simp only [zM,smul_eq_mul] at hS;have h05:B.length * (3 * n+3)≤n * (3 * n+3):=Nat.mul_le_mul_right _ hO;have h0j:n * (3 * n+3)=3 * (n * n)+3 * n:=by ring
   have h4':10 * n * n=10 * (n * n):=by ring
   omega
  have h5:(zn idx).length≤t * n+t:=by rw [vy];have hs:=List.sum_le_length_nsmul idx n (fun d hd=>(hidx_b d hd).trans hu);simp only [smul_eq_mul] at hs;have h05:idx.length * n≤t * n:=Nat.mul_le_mul_right _ hidx_l;omega
  have h6:(zR acc).length≤(n / 2+1)+4 * (n / 2+1) * t:=kJ t (n / 2+1) acc h8 h9
  have hnn:n * n≤x.length * x.length:=Nat.mul_le_mul (by omega) (by omega);have htn:t * n≤x.length * x.length:=Nat.mul_le_mul (by omega) (by omega);have h0h:(n / 2+1) * t≤x.length * x.length:=Nat.mul_le_mul (by omega) (by omega);have hsq:x.length ^ 2=x.length * x.length:=sq x.length;have h4nt:4 * (n / 2+1) * t=4 * ((n / 2+1) * t):=by ring
  have h10nn:10 * n * n=10 * (n * n):=by ring
  simp only [y4,zW,PL,zO,z9,Polynomial.eval_pow,Polynomial.eval_X,vT,hsq];omega
 have hk:out.length≤PL.eval x.length:=by
  have h0i:out.length=(n / 2+1) * t:=by simp only [out,List.length_flatMap,bits,zM,List.length_range,List.map_const',List.sum_replicate,smul_eq_mul]
  have h0h:(n / 2+1) * t≤x.length * x.length:=Nat.mul_le_mul (by omega) (by omega);have hsq:x.length ^ 2=x.length * x.length:=sq x.length;simp only [h0i,PL,zO,z9,Polynomial.eval_pow,Polynomial.eval_X,vT,hsq];omega
 by_cases ht0:t=0
 · subst ht0
   have hj:out=[]:=by simp [out,bits]
   have hB:uR x=out:=by simp [uR,hT,hj]
   have hU:stepSt (initSt x)=false::out:=by
    simp only [initSt,hN,hT,↓reduceIte,stepSt,y4,qk,zU,yl,g,List.getD_cons_zero,List.getD_cons_succ,hj];congr 1
    have h08:((List.range (n / 2+1)).flatMap (fun s=>gg (yM n 0) s))=[]:=by rw [List.flatMap_eq_nil_iff]; intro s hs;rw [yM,yK (n / 2+1) s _ (qw.mp hs)]; rfl
    rw [h08]; rfl
   refine ⟨hB,0,fun _=>initSt x,rfl,fun q hq=>by omega,hU,fun q _=>?_,hk,by simp⟩
   simp only [initSt,hN,hT,↓reduceIte]
   exact hf 1 (uh 0) (yM n 0) le_rfl (by simp [uh]) (by simp [uh])
    (by simp [yM]) (fun v hv=>by
      simp only [yM,qQ] at hv; rcases hv with ⟨_,_,rfl⟩
      exact ⟨zl 0 0,zS 0 0⟩)
 ·
  have ht1:1≤t:=Nat.pos_of_ne_zero ht0;set K:=(C.length+1) ^ (t-1);set st:ℕ→Q0:=fun q=>((fun s=>(stepSt s).tail)^[q]) (initSt x)
  let termQ:ℕ→ℕ→ℕ:=fun q s=>
   let idx:=zL (C.length+1) (t-1) q
   if vH C.length idx=1 then
    let S:(Q4 n):=z0 C idx
    if (S.biUnion (outer H)).card=2 * S.card∧(cores H).card+S.card≤ s then
     2 ^ S.card * (q7 (left H S) (reduced H S) (s-(cores H).card-S.card)).card
    else 0
   else 0
  have hY:∀ q,q≤K→
   ∃ (acc:Q2),acc.length=n / 2+1∧(∀ v∈acc,v.length=t∧∀ b∈v,b≤1)∧(∀ s≤n / 2,qV (gg acc s)=(∑ p∈Finset.range q,termQ p s) % 2 ^ t)∧
     st q=y4 [n,t,if q=K then 1 else 0] om
      (if q=K then (List.range (t-1)).map (fun _=>0) else zL (C.length+1) (t-1) q)
      C B acc∧
     (q<K→stepSt (st q)=true::st (q+1)):=by
   intro q; induction q with
   | zero=>
     intro _;have hKpos:0<K:=Nat.pos_of_ne_zero (by positivity);have h0k:(0:ℕ)≠K:=by omega
     refine ⟨yM n t,by simp [yM],?_,?_,?_,?_⟩
     · intro v hv; simp only [yM,qQ] at hv; rcases hv with ⟨_,_,rfl⟩
       exact ⟨zl t 0,zS t 0⟩
     · intro s hs;rw [yM,yK (n / 2+1) s _ (by omega),vz]; simp
     · simp only [st,Function.iterate_zero,id_eq,initSt,hN,hT,ht0,↓reduceIte,h0k,jq,uh,C,om,B]
     · intro _
       have h0d:st 0=y4 [n,t,0] om (zL (C.length+1) (t-1) 0) C B (yM n t):=by simp only [st,Function.iterate_zero,id_eq,initSt,hN,hT,ht0,↓reduceIte,jq,uh,C,om,B]
       have h0c:st 1=(stepSt (st 0)).tail:=rfl;rw [h0c,h0d];simp only [stepSt,y4,qk,zU,yl,g,List.getD_cons_zero,List.getD_cons_succ,zero_ne_one,↓reduceIte,List.tail_cons]
   | succ q ih=>
     intro hq1;rcases ih (by omega) with ⟨acc,h8,h9,hh,hG,hstep_q⟩
     have h0f:q<K:=by omega
     have h04:q≠K:=by omega
     rw [if_neg h04,if_neg h04] at hG;set idx:=zL (C.length+1) (t-1) q;have hA:idx.length=t-1:=(kk (C.length+1) (t-1) q (Nat.succ_pos _)).1
     have hod:kY C.length idx=
      if q+1<K then (0,zL (C.length+1) (t-1) (q+1))
      else (1,(List.range (t-1)).map (fun _=>0)):=qbj C.length (t-1) q h0f
     have hg:stepSt (st q)=
      let Srows:=y0 C idx
      let j:=Srows.length;let outF:=yU Srows;let uMask:=yX n om outF;let F0:=vU uMask B;let ps:=kD n uMask F0;let ok:=vH C.length idx * yu outF * (1-ps.dead) * (1-yT n ps.um ps.F)
      let acc':=
       if ok=1 then
        let nc:=kN n ps.um ps.F
        let nt:=kx n ps.um ps.F;let tp:=vS n t ps.um ps.F;let factor:=ke t (j+nc) tp;let mRow:=yC t (n / 2+1) nt;let shift:=C.length+j+ps.kF+ps.F.length
        (List.range (n / 2+1)).map (fun s=>
          if s<shift then gg acc s
          else kI t (gg acc s) (kK t factor (gg mRow (s-shift))))
       else acc
      let od:=kY C.length idx
      true::y4 [n,t,od.1] om od.2 C B acc':=by
      rw [hG];simp only [stepSt,y4,qk,zU,yl,g,List.getD_cons_zero,List.getD_cons_succ,zero_ne_one,↓reduceIte]
     set Srows:=y0 C idx;set j:=Srows.length;set outF:=yU Srows;set uMask:=yX n om outF;set F0:=vU uMask B;set ps:=kD n uMask F0;set ok:=vH C.length idx * yu outF * (1-ps.dead) * (1-yT n ps.um ps.F)
     set acc':=
      if ok=1 then
       let nc:=kN n ps.um ps.F
       let nt:=kx n ps.um ps.F;let tp:=vS n t ps.um ps.F;let factor:=ke t (j+nc) tp;let mRow:=yC t (n / 2+1) nt;let shift:=C.length+j+ps.kF+ps.F.length
       (List.range (n / 2+1)).map (fun s=>
         if s<shift then gg acc s
         else kI t (gg acc s) (kK t factor (gg mRow (s-shift))))
      else acc
     have hP:st (q+1)=y4 [n,t,if q+1=K then 1 else 0] om
      (if q+1=K then (List.range (t-1)).map (fun _=>0) else zL (C.length+1) (t-1) (q+1))
      C B acc':=by
      have h1:st (q+1)=(stepSt (st q)).tail:=by simp only [st,qM]
      rw [h1,hg,List.tail_cons,hod];by_cases hr:q+1=K
      · rw [if_neg (by omega),if_pos hr,if_pos hr]
      · rw [if_pos (by omega),if_neg hr,if_neg hr]
     have h0:acc'.length=n / 2+1∧(∀ v∈acc',v.length=t∧∀ b∈v,b≤1)∧
      ∀ s≤n / 2,qV (gg acc' s)=(∑ p∈Finset.range (q+1),termQ p s) % 2 ^ t:=by
      by_cases hZ:vH C.length idx=1
      · rcases wT (t:=t) hH3 hdeg ho hZ hA with ⟨_,_,hbr⟩
        have hz:acc'.length=n / 2+1:=by simp only [acc']; split_ifs <;> simp [h8]
        have h7:∀ s≤n / 2,
         (gg acc' s).length=t∧(∀ b∈gg acc' s,b≤1)∧
         qV (gg acc' s)=(∑ p∈Finset.range (q+1),termQ p s) % 2 ^ t:=by
         intro s hs;rcases hbr s hs with ⟨hI,hJ,hc⟩
         have hV:gg acc s∈acc:=by
          have:gg acc s=acc[s]'(by omega):=by simp [gg,qf,h8,show s<n / 2+1 by omega]
          rw [this]; exact qn (by omega)
         rcases h9 _ hV with ⟨hC,hD⟩
         rw [Finset.sum_range_succ]
         have hb:termQ q s=
          if ((z0 (n:=n) C idx).biUnion (outer H)).card=2 * (z0 (n:=n) C idx).card∧(cores H).card+(z0 (n:=n) C idx).card≤ s then
           2 ^ (z0 (n:=n) C idx).card *
             (q7 (left H (z0 C idx)) (reduced H (z0 C idx)) (s-(cores H).card-(z0 (n:=n) C idx).card)).card
          else 0:=by simp only [termQ,idx,hZ,↓reduceIte]
         let contrib:Q1:=
          if ok=1 then
           if s<C.length+j+ps.kF+ps.F.length then qA t 0
           else kK t (ke t (j+kN n ps.um ps.F) (vS n t ps.um ps.F))
            (gg (yC t (n / 2+1) (kx n ps.um ps.F)) (s-(C.length+j+ps.kF+ps.F.length)))
          else qA t 0
         change contrib.length=t at hI;change ∀ b∈contrib,b≤1 at hJ;change qV contrib=_ at hc;by_cases hH:ok=1
         · simp only [acc',hH,↓reduceIte,yK (n / 2+1) s _ (show s<n / 2+1 by omega)];simp only [contrib,hH,↓reduceIte] at hI hJ hc;split_ifs with hlt
           · simp only [hlt,↓reduceIte] at hc;rw [vz,Nat.zero_mod] at hc;refine ⟨hC,hD,?_⟩
             rw [hh s hs,hb,Nat.add_mod,← hc,add_zero,Nat.mod_mod]
           · simp only [hlt,↓reduceIte] at hI hJ hc;have h00:=j5 t (gg acc s) _ hC hI hD hJ;refine ⟨h00.1,h00.2.1,?_⟩
             rw [h00.2.2,hh s hs,hc,hb,Nat.add_mod,Nat.mod_mod,Nat.mod_mod,← Nat.add_mod]
         · simp only [acc',hH,↓reduceIte];simp only [contrib,hH,↓reduceIte] at hc;rw [vz,Nat.zero_mod] at hc;refine ⟨hC,hD,?_⟩
           rw [hh s hs,hb,Nat.add_mod,← hc,add_zero,Nat.mod_mod]
        refine ⟨hz,fun v hv=>?_,fun s hs=>(h7 s hs).2.2⟩
        rcases vI.mp hv with ⟨s,hs,rfl⟩
        have hgg:gg acc' s=acc'[s]:=by simp [gg,qf,hs]
        rw [← hgg]; exact ⟨(h7 s (by omega)).1,(h7 s (by omega)).2.1⟩
      · have h09:vH C.length idx=0:=by
         have:vH C.length idx≤1:=by unfold vH; dsimp only; split_ifs <;> omega
         omega
        have h0g:ok≠1:=by simp [ok,h09]
        have hE:acc'=acc:=by simp [acc',h0g]
        rw [hE];refine ⟨h8,h9,fun s hs=>?_⟩
        rw [hh s hs,Finset.sum_range_succ];have ht0':termQ q s=0:=by simp [termQ,idx,hZ]
        rw [ht0',add_zero]
     refine ⟨acc',h0.1,h0.2.1,h0.2.2,hP,fun hq1lt=>?_⟩
     have h02:st (q+1+1)=(stepSt (st (q+1))).tail:=by simp only [st,qM]
     rw [h02,hP,if_neg (by omega),if_neg (by omega)];simp only [stepSt,y4,qk,zU,yl,g,List.getD_cons_zero,List.getD_cons_succ,zero_ne_one,↓reduceIte,List.tail_cons]
  rcases hY K le_rfl with ⟨accK,hL,ht,hK,h03,_⟩
  rw [if_pos rfl,if_pos rfl] at h03
  have hn:∀ s≤n / 2,qV (gg accK s)=(q7 Finset.univ H s).card % 2 ^ t:=by
   intro s hs;rw [hK s hs,uY hH3 hdeg t s];congr 1
   let fval:Q4 n→ℕ:=fun S=>
    if (S.biUnion (outer H)).card=2 * S.card∧(cores H).card+S.card≤ s then
     2 ^ S.card * (q7 (left H S) (reduced H S) (s-(cores H).card-S.card)).card
    else 0
   have hcs:=qa6 ht1 hm h01 hM fval
   calc _=((Finset.range ((C.length+1) ^ (t-1))).filter
          (fun q=>vH C.length (zL (C.length+1) (t-1) q)=1)).sum
          (fun q=>fval (z0 C (zL (C.length+1) (t-1) q))):=by
         rw [← Finset.sum_filter]
    _=((cores H).powerset.filter (fun S=>S.card<t)).sum fval:=hcs
    _=_:=by dsimp only [fval]; rw [← Finset.sum_filter];congr 1; ext S; simp only [qa]; tauto
  have he:stepSt (st K)=false::out:=by
   rw [h03];simp only [stepSt,y4,qk,zU,yl,g,List.getD_cons_zero,List.getD_cons_succ,↓reduceIte,out];congr 1;rw [List.map_flatMap];refine List.flatMap_congr fun s hs=>?_
   have h0e:s≤n / 2:=by have:=qw.mp hs; omega
   have h06:gg accK s∈accK:=by
    have:gg accK s=accK[s]'(by omega):=by simp [gg,qf,hL,show s<n / 2+1 by omega]
    rw [this]; exact qn (by omega)
   exact qah t (q7 Finset.univ H s).card (gg accK s)
    (ht _ h06).1 (ht _ h06).2 (hn s h0e)
  have hB:uR x=out:=by simp only [uR,hT,ht0,↓reduceIte,hN];change (stepSt (st K)).tail=out;rw [he]; rfl
  have h0a:K≤(x.length+2) ^ t:=by
   calc K=(C.length+1) ^ (t-1):=rfl
    _≤(x.length+2) ^ (t-1):=Nat.pow_le_pow_left (by omega) _
    _≤(x.length+2) ^ t:=Nat.pow_le_pow_right (by omega) (Nat.sub_le t 1)
  refine ⟨hB,K,st,rfl,fun q hq=>(hY q (by omega)).choose_spec.2.2.2.2 hq,he,
   fun q hq=>?_,hk,h0a⟩
  rcases hY q hq with ⟨acc,h8,h9,_,hG,_⟩
  rw [hG];refine hf _ _ acc (by split_ifs <;> omega) ?_ ?_ h8 h9
  · split_ifs
    · simp only [zM,List.length_range]; omega
    · rw [(kk (C.length+1) (t-1) q (Nat.succ_pos _)).1]; omega
  · intro d hd; split_ifs at hd
    · simp only [qQ] at hd; rcases hd with ⟨_,_,rfl⟩; omega
    · exact Nat.le_of_lt_succ ((kk (C.length+1) (t-1) q (Nat.succ_pos _)).2.1 d hd)
end ki
end PEqualNP.Outside.L_lib_931
theorem PEqualNP.Outside.L_lib_931 :
    let header := fun n : Nat => List.replicate n true ++ [false]
    let bits := fun (w x : Nat) => (List.range w).map (fun i => x.testBit i)
    ∃ (f : List Bool → List Bool) (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n t : Nat) (H : Finset (Finset (Fin n))), (∀ R ∈ H, R.card = 3) →
        (∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2) →
        let Rows := Finset (Finset (Fin n))
        let count := fun (U : Finset (Fin n)) (F : Rows) (s : Nat) =>
          Nat.card {N : Rows // (∀ g ∈ N, g.card = 2 ∧ g ⊆ U) ∧
            (∀ g ∈ N, ∀ h ∈ N, g ≠ h → Disjoint g h) ∧
            (∀ R ∈ F, ∃ g ∈ N, g ⊆ R) ∧ N.card = s}
        let shared := (H.product H).image (fun z => z.1 ∩ z.2)
        let cores := shared.filter (fun c => c.card = 2)
        let ordinary := Finset.univ \ cores.biUnion id
        let base := H.filter (fun R => R ⊆ ordinary)
        let outer := fun c : Finset (Fin n) => (H.filter (fun R => c ⊆ R)).biUnion id \ c
        let left := fun S : Rows => ordinary \ S.biUnion outer
        let reduced := fun S : Rows => base.image (fun R => R ∩ left S)
        let hist := fun s : Nat => count Finset.univ H s
        let encode := header n ++ header t ++ H.toList.flatMap
          (fun R => R.toList.flatMap (fun u => bits (n.log2+1) u.val))
        (∀ S ⊆ cores, ∀ R ∈ reduced S, ∀ T ∈ reduced S, R ≠ T → (R ∩ T).card ≤ 1) ∧
        (∀ s : Nat, hist s % (2^t) =
          ((cores.powerset.filter (fun S => S.card < t ∧ (S.biUnion outer).card = 2*S.card ∧
            cores.card+S.card ≤ s)).sum (fun S =>
              2^S.card * count (left S) (reduced S) (s-cores.card-S.card))) % (2^t)) ∧
        f encode = (List.range (n/2+1)).flatMap (fun s => bits t (hist s)) ∧
        Nonempty (Turing.TM2OutputsInTime M.tm (encode.map M.inputAlphabet.invFun)
          (some ((f encode).map M.outputAlphabet.invFun)) ((encode.length+2)^(t+C))) := by
 dsimp only
 obtain ⟨M,C,hFin,hTime⟩:=
  PEqualNP.Outside.L_lib_931.Lib.qC.qdG.qaz
   PEqualNP.Outside.L_lib_931.Alg.initSt
   PEqualNP.Outside.L_lib_931.Alg.stepSt
   PEqualNP.Outside.L_lib_931.Alg.qcc
   PEqualNP.Outside.L_lib_931.Alg.qce
   PEqualNP.Outside.L_lib_931.ki.PL
 refine ⟨PEqualNP.Outside.L_lib_931.ki.uR,M,C,hFin,fun n t H hH3 hdeg=>?_⟩
 rcases PEqualNP.Outside.L_lib_931.ki.qaR n t H hH3 hdeg with
  ⟨heval,K,st,hst0,hstep,hlast,hL,hout,hK⟩
 refine ⟨?_,?_,?_,?_⟩
 · intro S _ R hR T hT hne;exact PEqualNP.Outside.L_lib_931.jC.jy hH3 S hR hT hne
 · intro s;have hmod:=PEqualNP.Outside.L_lib_931.jC.uY hH3 hdeg t s;simp only [PEqualNP.Outside.L_lib_931.jC.k2];exact hmod
 · simpa only [PEqualNP.Outside.L_lib_931.jC.k2] using heval
 · rw [heval];exact hTime _ _ K t st hst0 hstep hlast hL hout hK
