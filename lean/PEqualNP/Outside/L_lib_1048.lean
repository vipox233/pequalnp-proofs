import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1048
section asmP0
namespace Lib
abbrev a4 (f:List Bool→ List Bool):Prop:=PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
end Lib
section
namespace Lib.Machines
open Turing
lemma a4s {σ:Type} (f:σ→ Option σ) (n:ℕ) :
    (flip bind f)^[n] none=none:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply];exact ih
lemma a3r {σ τ:Type} (f:σ→ Option σ) (g:τ→ Option τ) (emb:σ→ τ)
    (h:∀ c c',f c=some c'→ g (emb c)=some (emb c')) :
    ∀ (n:ℕ) (a b : σ),(flip bind f)^[n] (some a)=some b →
      (flip bind g)^[n] (some (emb a))=some (emb b):=by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have:a=b:=Option.some.inj hab
    rw [this];rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa:f a with
    | none =>
      have e:flip bind f (some a)=none:=hfa
      rw [e,a4s] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind f (some a)=some c:=hfa
      have e':flip bind g (some (emb a))=some (emb c):=h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab
section n0
variable {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
def n0:TM2.Stmt Γ Λ σ→ ℕ
  | .push _ _ q=>n0 q+1
  | .peek _ _ q=>n0 q
  | .pop _ _ q=>n0 q
  | .load _ q=>n0 q
  | .branch _ q₁ q₂=>max (n0 q₁) (n0 q₂)
  | .goto _=>0
  | .halt=>0
lemma d58 (q:TM2.Stmt Γ Λ σ) (v:σ) (S:∀ k,List (Γ k)) (k:K) :
    ((TM2.stepAux q v S).stk k).length≤ (S k).length+n0 q:=by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux,n0]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [Function.update_self,List.length_cons];omega
    · rw [Function.update_of_ne h];omega
  | peek k' f q ih=>exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux,n0]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [Function.update_self,List.length_tail];omega
    · rw [Function.update_of_ne h]
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux,n0]
    cases f v
    · exact (ih₂ v S).trans (by have:=le_max_right (n0 q₁) (n0 q₂);omega)
    · exact (ih₁ v S).trans (by have:=le_max_left (n0 q₁) (n0 q₂);omega)
  | goto f=>simp [TM2.stepAux,n0]
  | halt=>simp [TM2.stepAux,n0]
end n0
noncomputable def p7 (tm:FinTM2):ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l=>n0 (tm.m l)
lemma d86 (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h:TM2.step tm.m c=some c') (k:tm.K) :
    (c'.stk k).length≤ (c.stk k).length+p7 tm:=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    refine (d58 _ _ _ _).trans ?_
    have:n0 (tm.m l)≤ p7 tm :=
      Finset.le_sup (f:=fun l=>n0 (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this
lemma a3m (tm:FinTM2) (k:tm.K) :
    ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a)=some b →
      (b.stk k).length≤ (a.stk k).length+p7 tm* n:=by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have:a=b:=Option.some.inj hab
    rw [this];simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa:TM2.step tm.m a with
    | none =>
      have e:flip bind (TM2.step tm.m) (some a)=none:=hfa
      rw [e,a4s] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind (TM2.step tm.m) (some a)=some c:=hfa
      rw [e] at hab
      have h1:=ih c b hab
      have h2:=d86 tm a c hfa k
      rw [Nat.mul_succ];omega
lemma i7 (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold initList
  congr 1
  funext k
  by_cases h:k=tm.k₀
  · subst h;simp
  · simp [h]
lemma i9 (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold haltList
  congr 1
  funext k
  by_cases h:k=tm.k₁
  · subst h;simp
  · simp [h]
lemma a0h (p:Polynomial ℕ) {x y:ℕ} (h:x≤ y):p.eval x≤ p.eval y:=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add,Polynomial.eval_add];exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial,Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def d60:List Bool→ TM2.Stmt (fun _:Unit=>Bool) Unit Bool
  | []=>.halt
  | a::l=>.push () (fun _=>a) (d60 l)
def d3 (l:List Bool):Unit→ TM2.Stmt (fun _:Unit=>Bool) Unit Bool :=
  fun _=>.pop () (fun _ o=>o.isSome)
    (.branch (fun s=>s)
      (.load (fun _=>false) (.goto fun _=>()))
      (d60 l.reverse))
def d20 (l:List Bool):FinTM2 where
  K:=Unit
  k₀:=()
  k₁:=()
  Γ _:=Bool
  Λ:=Unit
  main:=()
  σ:=Bool
  initialState:=false
  m:=d3 l
abbrev a3z:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
lemma d17 (S T:List Bool) :
    Function.update (fun _:Unit=>S) () T=fun _=>T:=by
  funext k
  simp
lemma d42 (l:List Bool) (v:Bool) (S:List Bool) :
    TM2.stepAux (d60 l) v (fun _:Unit=>S) =
      (⟨none,v,fun _=>l.reverse++S⟩:a3z):=by
  induction l generalizing S with
  | nil=>rfl
  | cons a l ih =>
    simp only [d60,TM2.stepAux]
    rw [d17,ih]
    simp
lemma d64 (l:List Bool) (x:Bool) (a:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>x::a⟩:a3z) =
      some ⟨some (),false,fun _=>a⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp
lemma d76 (l:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>[]⟩:a3z) =
      some ⟨none,false,fun _=>l⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  rw [d42]
  simp
lemma d63 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (⟨some (),false,fun _=>a⟩:a3z)) =
      some ⟨none,false,fun _=>l⟩:=by
  induction a with
  | nil=>exact d76 l
  | cons x a ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d3 l))
        (some (⟨some (),false,fun _=>x::a⟩:a3z)) =
        some ⟨some (),false,fun _=>a⟩:=d64 l x a
    rw [e,ih]
lemma d75 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (initList (d20 l) a))=some (haltList (d20 l) l):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (d3 l)))^[a.length+1]
    (some c)) (i7 (d20 l) a)).trans
    (Eq.trans ?_ (congrArg some (i9 (d20 l) l)).symm)
  show (flip bind (TM2.step (d3 l)))^[a.length+1]
    (some (⟨some (),false,Function.update (fun _=>[]) () a⟩:a3z)) =
    some (⟨none,false,Function.update (fun _=>[]) () l⟩:a3z)
  rw [d17,d17]
  exact d63 l a
lemma a01 (l:List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x:List Bool=>x)
      (fun x:List Bool=>x) (fun _:List Bool=>l)) :=
  ⟨{
    tm:=d20 l
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.X+1
    outputsFun:=fun a =>
      { steps:=a.length+1
        evals_in_steps:=by
          have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
          exact (congrArg (fun x=>(flip bind (TM2.step (d3 l)))^[a.length+1]
            (some (initList (d20 l) x))) (hm a)).trans
            ((d75 l a).trans
              (congrArg (fun x=>some (haltList (d20 l) x)) (hm l).symm))
        steps_le_m:=by simp } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
section update
variable {ι:Type} [DecidableEq ι] {β:ι→ Type}
lemma d51 (E:∀ i,β i) {a b c:ι} (hab:a≠b) (hac:a≠c)
    (x x':β a) (y:β b) (z:β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z:=by
  rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
lemma d50 (E:∀ i,β i) {a b c:ι} (hbc:b≠c)
    (x:β a) (y y':β b) (z:β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z:=by
  rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Option (M1.K ⊕ M2.K)
abbrev CΓ:CK M1 M2→ Type
  | none=>M2.Γ M2.k₀
  | some (Sum.inl k)=>M1.Γ k
  | some (Sum.inr k)=>M2.Γ k
abbrev CΛ:Type:=M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ:Type:=M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q=>.push (some (Sum.inl k)) (fun s=>f s.1) (tr1 q)
  | .peek k f q=>.peek (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
  | .pop k f q=>.pop (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
  | .load a q=>.load (fun s=>(a s.1,s.2)) (tr1 q)
  | .branch f q₁ q₂=>.branch (fun s=>f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f=>.goto (fun s=>Sum.inl (f s.1))
  | .halt=>.goto (fun _=>Sum.inr (Sum.inr false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q=>.push (some (Sum.inr k)) (fun s=>f s.2.1) (tr2 q)
  | .peek k f q=>.peek (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .pop k f q=>.pop (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .load a q=>.load (fun s=>(s.1,a s.2.1,s.2.2)) (tr2 q)
  | .branch f q₁ q₂=>.branch (fun s=>f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f=>.goto (fun s=>Sum.inr (Sum.inl (f s.2.1)))
  | .halt=>.halt
variable (M1 M2)
def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀)→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none=>.goto (fun _=>Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map φ))
      (.branch (fun s=>s.2.2.isSome)
        (.push none (fun s=>s.2.2.getD d) (.goto fun _=>Sum.inr (Sum.inr false)))
        (.goto fun _=>Sum.inr (Sum.inr true)))
def tB:Option (M2.Γ M2.k₀)→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none=>.goto (fun _=>Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o=>(s.1,s.2.1,o))
      (.branch (fun s=>s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s=>s.2.2.getD d)
          (.goto fun _=>Sum.inr (Sum.inr true)))
        (.goto fun _=>Sum.inr (Sum.inl M2.main)))
def m3 (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)) :
    CΛ M1 M2→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l=>tr1 (M1.m l)
  | Sum.inr (Sum.inl l)=>tr2 (M2.m l)
  | Sum.inr (Sum.inr false)=>tA M1 M2 φ d
  | Sum.inr (Sum.inr true)=>tB M1 M2 d
def comp (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2 :=
  haveI:=M1.kFin
  haveI:=M2.kFin
  haveI:=M1.ΛFin
  haveI:=M2.ΛFin
  haveI:=M1.σFin
  haveI:=M2.σFin
  haveI:=M2.Γk₀Fin
  { K:=CK M1 M2
    k₀:=some (Sum.inl M1.k₀)
    k₁:=some (Sum.inr M2.k₁)
    Γ:=CΓ M1 M2
    Λ:=CΛ M1 M2
    main:=Sum.inl M1.main
    σ:=Cσ M1 M2
    initialState:=(M1.initialState,M2.initialState,none)
    Γk₀Fin:=M1.Γk₀Fin
    m:=m3 M1 M2 φ d }
variable {M1 M2}
def d49 (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none=>[]
  | some (Sum.inl k)=>S k
  | some (Sum.inr _)=>[]
def d48 (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none=>[]
  | some (Sum.inl _)=>[]
  | some (Sum.inr k)=>S k
lemma d13 (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)) :
    (d49 (Function.update S k x):∀ k,List (CΓ M1 M2 k)) =
      Function.update (d49 S) (some (Sum.inl k)) x:=by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)];rfl
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j=x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j=S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)];rfl
lemma d12 (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)) :
    (d48 (Function.update S k x):∀ k,List (CΓ M1 M2 k)) =
      Function.update (d48 S) (some (Sum.inr k)) x:=by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j=x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j=S j
      rw [Function.update_of_ne h]
lemma d56 :
    (d49 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
  funext j;rcases j with _ | j | j <;> rfl
lemma d55 :
    (d48 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
  funext j;rcases j with _ | j | j <;> rfl
def a88 (w:M2.σ × Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl),(c.var,w),d49 c.stk⟩
def a7u (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l=>Sum.inr (Sum.inl l)),(u,c.var,b),d48 c.stk⟩
lemma c1y (w:M2.σ × Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
    (S:∀ k,List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v,w):Cσ M1 M2) (d49 S)=a88 w (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v::S k))
    rw [d13] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [d13] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
lemma c2l (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
    (S:∀ k,List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u,v,b):Cσ M1 M2) (d48 S)=a7u u b (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v::S k))
    rw [d12] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [d12] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
variable (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
lemma c0b (w:M2.σ × Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h:TM2.step M1.m c=some c') :
    TM2.step (m3 M1 M2 φ d) (a88 w c)=some (a88 w c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (c1y w (M1.m l) v S)
lemma c0n (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h:TM2.step M2.m c=some c') :
    TM2.step (m3 M1 M2 φ d) (a7u u b c)=some (a7u u b c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (c2l u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _=>[])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
lemma b4u (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁))=l:=by
  unfold st
  rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
lemma b0c (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:=by
  unfold st
  rw [Function.update_of_ne (by simp),Function.update_self]
lemma b9o (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))=u:=by
  unfold st
  rw [Function.update_self]
lemma d66 (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l'=st l' t u :=
  d51 _ (by simp) (by simp) _ _ _ _
lemma d41 (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u :=
  d50 _ (by simp) _ _ _ _
lemma d90 (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u'=st l t u' :=
  Function.update_idem _ _ _
lemma d79 (l:List (M1.Γ M1.k₁)) :
    (st l [] []:∀ k,List (CΓ M1 M2 k)) =
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l:=by
  unfold st
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
lemma a9g (u:List (M2.Γ M2.k₀)) :
    (st [] [] u:∀ k,List (CΓ M1 M2 k)) =
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u:=by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {M1 M2:FinTM2} (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀)
abbrev a0e (M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
lemma d89 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    TM2.step (m3 M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x::l) t u⟩:a0e M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x::t) u⟩:=by
  simp only [TM2.step,m3,tA,TM2.stepAux]
  rw [b4u]
  simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
    Option.getD_some]
  rw [d66,b0c,d41]
lemma c1l (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (t u:List (M2.Γ M2.k₀)) :
    TM2.step (m3 M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st [] t u⟩:a0e M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] t u⟩:=by
  simp only [TM2.step,m3,tA,TM2.stepAux]
  rw [b4u]
  simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
  rw [d66]
lemma d88 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)) :
    TM2.step (m3 M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x::t) u⟩:a0e M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x::u)⟩:=by
  simp only [TM2.step,m3,tB,TM2.stepAux]
  rw [b0c]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
  rw [d41,b9o,d90]
lemma c20 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (u:List (M2.Γ M2.k₀)) :
    TM2.step (m3 M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] [] u⟩:a0e M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] u⟩:=by
  simp only [TM2.step,m3,tB,TM2.stepAux]
  rw [b0c]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [d41]
lemma c0a (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)) :
    ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (m3 M1 M2 φ (some dd))))^[l.length+1]
          (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st l t u⟩:a0e M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] ((l.map φ).reverse++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t b;exact c1l φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (m3 M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x::l) t u⟩:a0e M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x::t) u⟩ :=
      d89 φ dd v1 v2 b x l t u
    rw [e,ih]
    simp
lemma c0l (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) :
    ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (m3 M1 M2 φ (some dd))))^[t.length+1]
          (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] t u⟩:a0e M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] (t.reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u b;exact c20 φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (m3 M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x::t) u⟩:a0e M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x::u)⟩ :=
      d88 φ dd v1 v2 b x t u
    rw [e,ih]
    simp
lemma c2n (d:Option (M2.Γ M2.k₀)) (hd:d=none→ IsEmpty (M2.Γ M2.k₀))
    (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)) :
    ∃ n,n ≤ 2 * o.length+2 ∧
      (flip bind (TM2.step (m3 M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,none),
            Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            a0e M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),
          Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩:=by
  cases d with
  | none =>
    have:=hd rfl
    have ho:o=[]:=by
      cases o with
      | nil=>rfl
      | cons x _=>exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1,by omega,?_⟩
    show some _=some _
    simp only [m3,tA,TM2.stepAux,List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse++[]).length+1+(o.length+1),by simp;omega,?_⟩
    rw [Function.iterate_add_apply,← d79,c0a,c0l,← a9g]
    simp
lemma c2s (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)) :
    a88 (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:=by
  rw [i7]
  refine Eq.trans ?_ (i7 (comp M1 M2 φ d) i).symm
  show (⟨_,_,d49 _⟩:a0e M1 M2)=_
  rw [d13,d56]
  rfl
lemma c1b (w:M2.σ × Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)) :
    a88 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)),(M1.initialState,w),
        Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        a0e M1 M2):=by
  rw [i9]
  show (⟨_,_,d49 _⟩:a0e M1 M2)=_
  rw [d13,d56]
  rfl
lemma c1m (u:M1.σ) (i:List (M2.Γ M2.k₀)) :
    a7u u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)),(u,M2.initialState,none),
        Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        a0e M1 M2):=by
  rw [i7]
  show (⟨_,_,d48 _⟩:a0e M1 M2)=_
  rw [d12,d55]
  rfl
lemma c2f (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)) :
    a7u M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:=by
  rw [i9]
  refine Eq.trans ?_ (i9 (comp M1 M2 φ d) o).symm
  show (⟨_,_,d48 _⟩:a0e M1 M2)=_
  rw [d12,d55]
  rfl
lemma a6b (d:Option (M2.Γ M2.k₀)) (hd:d=none→ IsEmpty (M2.Γ M2.k₀))
    (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
    (h1:(flip bind (TM2.step M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
    (h2:(flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n,n ≤ s1+(2 * o1.length+2)+s2∧o1.length ≤ i.length+p7 M1 * s1 ∧
      (flip bind (TM2.step (m3 M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2):=by
  have p1:=a3r (TM2.step M1.m) (TM2.step (m3 M1 M2 φ d))
    (a88 (M2.initialState,none)) (c0b φ d _) s1 _ _ h1
  rw [c2s φ d,c1b] at p1
  obtain ⟨nt,hnt,pt⟩:=c2n φ d hd M1.initialState M2.initialState o1
  have p2:=a3r (TM2.step M2.m) (TM2.step (m3 M1 M2 φ d))
    (a7u M1.initialState none) (c0n φ d _ _) s2 _ _ h2
  rw [c1m,c2f φ d] at p2
  refine ⟨s2+(nt+s1),by omega,?_,?_⟩
  · have:=a3m M1 M1.k₁ s1 _ _ h1
    rw [i9,i7] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h:M1.k₁=M1.k₀
    · rw [h,Function.update_self]
    · rw [Function.update_of_ne h];simp
  · rw [Function.iterate_add_apply,Function.iterate_add_apply,p1,pt,p2]
    rfl
lemma a99 {α β γ αΓ βΓ γΓ:Type} (ea:α→ List αΓ) (eb:β→ List βΓ)
    (ec:γ→ List γΓ) (f:α→ β) (g:β→ γ) (c1:TM2ComputableInPolyTime ea eb f)
    (c2:TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a=>g (f a))):=by
  classical
  let φ:c1.tm.Γ c1.tm.k₁→ c2.tm.Γ c2.tm.k₀ :=
    fun x=>c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d:Option (c2.tm.Γ c2.tm.k₀) :=
    if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd:d=none→ IsEmpty (c2.tm.Γ c2.tm.k₀):=by
    intro h
    by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d,hn] at h
    · exact not_nonempty_iff.mp hn
  let T:Polynomial ℕ :=
    c1.time+(Polynomial.C 2* (Polynomial.X+Polynomial.C (p7 c1.tm)* c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X+Polynomial.C (p7 c1.tm)* c1.time)
  have key:∀ a,∃ n,n≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (m3 c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
    intro a
    have r1:=c1.outputsFun a
    have r2:=c2.outputsFun (f a)
    have hφ:(List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)):=by
      rw [List.map_map]
      refine List.map_congr_left fun y _=>?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2:(flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
      rw [hφ];exact r2.evals_in_steps
    obtain ⟨n,hn,hlen,hrun⟩:=a6b φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n,hn.trans ?_,hrun⟩
    have b1:=r1.steps_le_m
    have b2:=r2.steps_le_m
    simp only [List.length_map] at hlen
    have j1:p7 c1.tm* r1.steps ≤
        p7 c1.tm* Polynomial.eval (ea a).length c1.time:=Nat.mul_le_mul_left _ b1
    have b3:Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length+p7 c1.tm* Polynomial.eval (ea a).length c1.time)
          c2.time:=a0h _ (by omega)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,List.length_map]
    omega
  exact ⟨{
    tm:=comp c1.tm c2.tm φ d
    inputAlphabet:=c1.inputAlphabet
    outputAlphabet:=c2.outputAlphabet
    time:=T
    outputsFun:=fun a =>
      ⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {Γ₀ Γ₁:Type}
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool→ Type
  | some false=>Γ₀
  | none=>Option Γ₀
  | some true=>Γ₁
def q9 (φ:Γ₀→ Option Γ₁) (d:Option Γ₁):Bool→ TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push none (fun s=>s) (.goto fun _=>false))
        (.goto fun _=>true))
  | true =>
    .pop none (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.branch (fun s=>(s.bind φ).isSome)
          (match d with
            | some dd=>.push (some true) (fun s=>(s.bind φ).getD dd) (.goto fun _=>true)
            | none=>.goto fun _=>true)
          (.goto fun _=>true))
        .halt)
def fm [Fintype Γ₀] (φ:Γ₀→ Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=Option Bool
  k₀:=some false
  k₁:=some true
  Γ:=FΓ Γ₀ Γ₁
  Λ:=Bool
  main:=false
  σ:=Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=q9 φ d
def m8 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _=>[])
    (some false) l) none t) (some true) u
lemma d99 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    m8 l t u (some false)=l:=by
  unfold m8
  rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
lemma d81 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    m8 l t u none=t:=by
  unfold m8
  rw [Function.update_of_ne (by simp),Function.update_self]
lemma c15 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    m8 l t u (some true)=u:=by
  unfold m8
  rw [Function.update_self]
lemma d47 (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (m8 l t u) (some false) l'=m8 l' t u :=
  d51 _ (by simp) (by simp) _ _ _ _
lemma d27 (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁) :
    Function.update (m8 l t u) none t'=m8 l t' u :=
  d50 _ (by simp) _ _ _ _
lemma d82 (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁) :
    Function.update (m8 l t u) (some true) u'=m8 l t u' :=
  Function.update_idem _ _ _
lemma d98 (l:List Γ₀) :
    (m8 l [] []:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:=by
  unfold m8
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
lemma c1d (u:List Γ₁) :
    (m8 [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:=by
  unfold m8
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
abbrev a2t (Γ₀ Γ₁:Type):Type:=TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ:Γ₀→ Option Γ₁) (d:Option Γ₁)
lemma c13 (b:Option Γ₀) (x:Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (q9 φ d) (⟨some false,b,m8 (x::l) t u⟩:a2t Γ₀ Γ₁) =
      some ⟨some false,some x,m8 l (some x::t) u⟩:=by
  simp only [TM2.step,q9,TM2.stepAux]
  rw [d99]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
  rw [d47,d81,d27]
lemma c2o (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (q9 φ d) (⟨some false,b,m8 [] t u⟩:a2t Γ₀ Γ₁) =
      some ⟨some true,none,m8 [] t u⟩:=by
  simp only [TM2.step,q9,TM2.stepAux]
  rw [d99]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [d47]
lemma c0w (hd:d=none→ ∀ x,φ x=none) (b:Option Γ₀) (x:Γ₀)
    (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (q9 φ d) (⟨some true,b,m8 [] (some x::t) u⟩:a2t Γ₀ Γ₁) =
      some ⟨some true,some x,m8 [] t ((φ x).toList++u)⟩:=by
  simp only [TM2.step,q9,TM2.stepAux]
  rw [d81]
  simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
    Bool.cond_true,Option.bind_some]
  rw [d27]
  cases hφ:φ x with
  | none=>simp
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,
        Option.toList_some,List.singleton_append]
      rw [c15,d82]
      simp [hφ]
lemma c1g (b:Option Γ₀) (u:List Γ₁) :
    TM2.step (q9 φ d) (⟨some true,b,m8 [] [] u⟩:a2t Γ₀ Γ₁) =
      some ⟨none,none,m8 [] [] u⟩:=by
  simp only [TM2.step,q9,TM2.stepAux]
  rw [d81]
  simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
    Bool.cond_false]
  rw [d27]
lemma c17 (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
      (flip bind (TM2.step (q9 φ d)))^[l.length+1]
          (some (⟨some false,b,m8 l t u⟩:a2t Γ₀ Γ₁)) =
        some ⟨some true,none,m8 [] (l.reverse.map some++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t b;exact c2o φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (q9 φ d))
        (some (⟨some false,b,m8 (x::l) t u⟩:a2t Γ₀ Γ₁)) =
        some ⟨some false,some x,m8 l (some x::t) u⟩:=c13 φ d b x l t u
    rw [e,ih]
    simp
lemma c22 (hd:d=none→ ∀ x,φ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
      (flip bind (TM2.step (q9 φ d)))^[t.length+1]
          (some (⟨some true,b,m8 [] (t.map some) u⟩:a2t Γ₀ Γ₁)) =
        some ⟨none,none,m8 [] [] ((t.filterMap φ).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u b;exact c1g φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (q9 φ d))
        (some (⟨some true,b,m8 [] ((x::t).map some) u⟩:a2t Γ₀ Γ₁)) =
        some ⟨some true,some x,m8 [] (t.map some) ((φ x).toList++u)⟩ :=
      c0w φ d hd b x (t.map some) u
    rw [e,ih]
    cases hφ:φ x <;> simp [hφ]
lemma b8q [Fintype Γ₀] (hd:d=none→ ∀ x,φ x=none) (l:List Γ₀) :
    (flip bind (TM2.step (q9 φ d)))^[l.length+1+(l.length+1)]
        (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (q9 φ d)))^[l.length+1+(l.length+1)]
    (some c)) (i7 (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (i9 (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (q9 φ d)))^[l.length+1+(l.length+1)]
    (some (⟨some false,none,Function.update (fun _=>[]) (some false) l⟩:a2t Γ₀ Γ₁)) =
    some (⟨none,none,Function.update (fun _=>[]) (some true) (l.filterMap φ)⟩:a2t Γ₀ Γ₁)
  rw [Function.iterate_add_apply,← d98,c17,← c1d]
  have:=c22 φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
lemma t4 {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (φ:αΓ→ Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:d=none→ ∀ x,φ x=none:=by
    intro hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ : φ x with
      | none=>rfl
      | some y=>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:=fm φ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2* Polynomial.X+Polynomial.C 2
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=b8q φ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (q9 φ d)))^[(ea a).length+1 +
            ((ea a).length+1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive TPK:Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq
instance:Fintype TPK :=
  Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x=>by cases x <;> simp)
inductive TPL:Type
  | a | b | c | e
  deriving DecidableEq
instance:Fintype TPL :=
  Fintype.ofList [.a,.b,.c,.e] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁:Type}
abbrev TPΓ (Γ₀ Γ₁:Type):TPK→ Type
  | .inp=>Γ₀
  | .t1=>Option Γ₀
  | .t2=>Option Γ₀
  | .t3=>Option Γ₀
  | .out=>Γ₁
def d52 (φ : Γ₀ → Option Γ₁) (d:Option Γ₁) (lbl:TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s=>(s.bind φ).isSome)
    (match d with
      | some dd=>.push .out (fun s=>(s.bind φ).getD dd) (.goto fun _=>lbl)
      | none=>.goto fun _=>lbl)
    (.goto fun _=>lbl)
def f9 (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁) :
    TPL→ TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push .t1 (fun s=>s) (.goto fun _=>.a))
        (.goto fun _=>.b))
  | .b =>
    .pop .t1 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.push .t2 (fun s=>s) (d52 φ₂ d .b))
        (.goto fun _=>.c))
  | .c =>
    .pop .t2 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.push .t3 (fun s=>s) (.goto fun _=>.c))
        (.goto fun _=>.e))
  | .e =>
    .pop .t3 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (d52 φ₁ d .e)
        .halt)
def tp [Fintype Γ₀] (φ₁ φ₂:Γ₀→ Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=TPK
  k₀:=.inp
  k₁:=.out
  Γ:=TPΓ Γ₀ Γ₁
  Λ:=TPL
  main:=.a
  σ:=Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=f9 φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
  | .inp=>l
  | .t1=>a
  | .t2=>b
  | .t3=>c
  | .out=>u
lemma d54 (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .inp l'=st5 l' a b c u:=by
  funext k;cases k <;> simp [st5]
lemma d31 (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t1 a'=st5 l a' b c u:=by
  funext k;cases k <;> simp [st5]
lemma d30 (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t2 b'=st5 l a b' c u:=by
  funext k;cases k <;> simp [st5]
lemma d29 (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t3 c'=st5 l a b c' u:=by
  funext k;cases k <;> simp [st5]
lemma d53 (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁) :
    Function.update (st5 l a b c u) .out u'=st5 l a b c u':=by
  funext k;cases k <;> simp [st5]
lemma c1o (l:List Γ₀) :
    (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:=by
  funext k;cases k <;> simp [st5]
lemma c2a (u:List Γ₁) :
    (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:=by
  funext k;cases k <;> simp [st5]
abbrev p4 (Γ₀ Γ₁:Type):Type:=TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂:Γ₀→ Option Γ₁) (d:Option Γ₁)
lemma c26 (s:Option Γ₀) (x:Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
    (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .a,s,st5 (x::l) a b c u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .a,some x,st5 l (some x::a) b c u⟩:=by
  simp [TM2.step,f9,TM2.stepAux,st5,d54,d31]
lemma c0t (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .b,none,st5 [] a b c u⟩:=by
  simp [TM2.step,f9,TM2.stepAux,st5,d54]
lemma c27 (hd:d=none→ ∀ x,φ₂ x=none) (s:Option Γ₀) (x:Γ₀)
    (a b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x::a) b c u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .b,some x,st5 [] a (some x::b) c ((φ₂ x).toList++u)⟩:=by
  cases hφ:φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step,f9,d52,TM2.stepAux,st5,d31,d30,hφ]
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step,f9,d52,TM2.stepAux,st5,d31,d30,
        d53,hφ]
lemma c0r (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .c,none,st5 [] [] b c u⟩:=by
  simp [TM2.step,f9,TM2.stepAux,st5,d31]
lemma c0x (s:Option Γ₀) (x:Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x::b) c u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .c,some x,st5 [] [] b (some x::c) u⟩:=by
  simp [TM2.step,f9,TM2.stepAux,st5,d30,d29]
lemma c1r (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .e,none,st5 [] [] [] c u⟩:=by
  simp [TM2.step,f9,TM2.stepAux,st5,d30]
lemma c1s (hd:d=none→ ∀ x,φ₁ x=none) (s:Option Γ₀) (x:Γ₀)
    (c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x::c) u⟩:p4 Γ₀ Γ₁) =
      some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList++u)⟩:=by
  cases hφ:φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step,f9,d52,TM2.stepAux,st5,d29,hφ]
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step,f9,d52,TM2.stepAux,st5,d29,d53,hφ]
lemma c16 (s:Option Γ₀) (u:List Γ₁) :
    TM2.step (f9 φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:p4 Γ₀ Γ₁) =
      some ⟨none,none,st5 [] [] [] [] u⟩:=by
  simp [TM2.step,f9,TM2.stepAux,st5,d29]
lemma c0q (b c:List (Option Γ₀)) (u:List Γ₁) :
    ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1]
          (some (⟨some .a,s,st5 l a b c u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .b,none,st5 [] (l.reverse.map some++a) b c u⟩:=by
  intro l
  induction l with
  | nil=>intro a s;exact c0t φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (f9 φ₁ φ₂ d))
        (some (⟨some .a,s,st5 (x::l) a b c u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .a,some x,st5 l (some x::a) b c u⟩:=c26 φ₁ φ₂ d s x l a b c u
    rw [e,ih]
    simp
lemma c24 (hd:d=none→ ∀ x,φ₂ x=none) (c:List (Option Γ₀)) :
    ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (TM2.step (f9 φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .c,none,
          st5 [] [] (t.reverse.map some++b) c ((t.filterMap φ₂).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro b u s;exact c0r φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (f9 φ₁ φ₂ d))
        (some (⟨some .b,s,st5 [] ((x::t).map some) b c u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .b,some x,st5 [] (t.map some) (some x::b) c ((φ₂ x).toList++u)⟩ :=
      c27 φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e,ih]
    cases hφ:φ₂ x <;> simp [hφ]
lemma c2g (u:List Γ₁) :
    ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (TM2.step (f9 φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .e,none,st5 [] [] [] (t.reverse.map some++c) u⟩:=by
  intro t
  induction t with
  | nil=>intro c s;exact c1r φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (f9 φ₁ φ₂ d))
        (some (⟨some .c,s,st5 [] [] ((x::t).map some) c u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .c,some x,st5 [] [] (t.map some) (some x::c) u⟩ :=
      c0x φ₁ φ₂ d s x (t.map some) c u
    rw [e,ih]
    simp
lemma c1v (hd:d=none→ ∀ x,φ₁ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (TM2.step (f9 φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:p4 Γ₀ Γ₁)) =
        some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u s;exact c16 φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (f9 φ₁ φ₂ d))
        (some (⟨some .e,s,st5 [] [] [] ((x::t).map some) u⟩:p4 Γ₀ Γ₁)) =
        some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList++u)⟩ :=
      c1s φ₁ φ₂ d hd s x (t.map some) u
    rw [e,ih]
    cases hφ:φ₁ x <;> simp [hφ]
lemma b8y [Fintype Γ₀] (hd₁:d=none→ ∀ x,φ₁ x=none)
    (hd₂:d=none→ ∀ x,φ₂ x=none) (l:List Γ₀) :
    (flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
        (l.length+1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1 +
    (l.length+1)+(l.length+1)+(l.length+1)]
    (some c)) (i7 (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (i9 (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
      (l.length+1)]
    (some (⟨some .a,none,Function.update (fun _=>[]) .inp l⟩:p4 Γ₀ Γ₁)) =
    some (⟨none,none,Function.update (fun _=>[]) .out
      (l.filterMap φ₁++l.filterMap φ₂)⟩:p4 Γ₀ Γ₁)
  have hA:(flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .a,none,st5 l [] [] [] []⟩:p4 Γ₀ Γ₁)) =
      some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:=by
    simpa using c0q φ₁ φ₂ d [] [] [] l [] none
  have hB:(flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:p4 Γ₀ Γ₁)) =
      some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:=by
    have:=c24 φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC:(flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:p4 Γ₀ Γ₁)) =
      some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:=by
    simpa using c2g φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE:(flip bind (TM2.step (f9 φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        p4 Γ₀ Γ₁)) =
      some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁++l.filterMap φ₂)⟩:=by
    have:=c1v φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
    ← c1o,hA,hB,hC,hE,c2a]
lemma w4 {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (φ₁ φ₂:αΓ→ Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ₁++(ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ φ:αΓ→ Option βΓ,d=none→ ∀ x,φ x=none:=by
    intro φ hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ : φ x with
      | none=>rfl
      | some y=>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:=tp φ₁ φ₂ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 4* Polynomial.X+Polynomial.C 4
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)+((ea a).length+1) +
          ((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=b8y φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (f9 φ₁ φ₂ d)))^[(ea a).length+1 +
            ((ea a).length+1)+((ea a).length+1)+((ea a).length+1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive FX
  | I | W | T | O
  deriving DecidableEq
instance:Fintype FX :=
  Fintype.ofList [FX.I,FX.W,FX.T,FX.O] (fun x=>by cases x <;> simp)
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq
instance:Fintype FL :=
  Fintype.ofList [FL.l1,FL.l2,FL.l3,FL.l4,FL.l5] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev a2s:M.K ⊕ FX→ Type
  | Sum.inl k=>M.Γ k
  | Sum.inr FX.I=>Bool ⊕ Bool
  | Sum.inr FX.W=>Bool
  | Sum.inr FX.T=>Bool
  | Sum.inr FX.O=>Bool ⊕ Bool
abbrev b05:Type:=M.Λ ⊕ FL
abbrev b00:Type:=M.σ × Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool)→ Bool
  | none=>false
  | some (Sum.inl b)=>b
  | some (Sum.inr b)=>b
def a58:Option (Bool ⊕ Bool)→ Bool
  | some (Sum.inl _)=>true
  | _=>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ→ TM2.Stmt (a2s M) (b05 M) (b00 M)
  | .push k f q=>.push (Sum.inl k) (fun s=>f s.1) (trF q)
  | .peek k f q=>.peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
  | .pop k f q=>.pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
  | .load a q=>.load (fun s=>(a s.1,s.2)) (trF q)
  | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trF q₁) (trF q₂)
  | .goto f=>.goto (fun s=>Sum.inl (f s.1))
  | .halt=>.goto (fun _=>Sum.inr FL.l3)
variable (M)
def c0 (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) :
    b05 M→ TM2.Stmt (a2s M) (b05 M) (b00 M)
  | Sum.inl l=>trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o=>(s.1,o))
      (.branch (fun s=>s.2.isSome)
        (.branch (fun s=>a58 s.2)
          (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1)))
        (.goto fun _=>Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr FL.l2))
        (.goto fun _=>Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr FX.O) (fun s=>Sum.inr (bit s.2)) (.goto fun _=>Sum.inr FL.l3))
        (.goto fun _=>Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l4))
        (.goto fun _=>Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr FX.O) (fun s=>Sum.inl (bit s.2)) (.goto fun _=>Sum.inr FL.l5))
        .halt)
def z9 (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ FX
    k₀:=Sum.inr FX.I
    k₁:=Sum.inr FX.O
    Γ:=a2s M
    Λ:=b05 M
    main:=Sum.inr FL.l1
    σ:=b00 M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=c0 M e₀ e₁ }
variable {M}
def d5 (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)):∀ k,List (a2s M k)
  | Sum.inl k=>S k
  | Sum.inr FX.I=>i
  | Sum.inr FX.W=>w
  | Sum.inr FX.T=>t
  | Sum.inr FX.O=>o
section d5
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool))
lemma d23 (k:M.K) (x:List (M.Γ k)) :
    Function.update (d5 S i w t o) (Sum.inl k) x=d5 (Function.update S k x) i w t o:=by
  funext j
  rcases j with j | j
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show x=Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j=Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)];cases j <;> rfl
lemma d33 (i':List (Bool ⊕ Bool)) :
    Function.update (d5 S i w t o) (Sum.inr FX.I) i'=d5 S i' w t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
lemma d45 (w':List Bool) :
    Function.update (d5 S i w t o) (Sum.inr FX.W) w'=d5 S i w' t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
lemma d18 (t':List Bool) :
    Function.update (d5 S i w t o) (Sum.inr FX.T) t'=d5 S i w t' o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
lemma d46 (o':List (Bool ⊕ Bool)) :
    Function.update (d5 S i w t o) (Sum.inr FX.O) o'=d5 S i w t o':=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
end d5
abbrev j6 (M:FinTM2):Type:=TM2.Cfg (a2s M) (b05 M) (b00 M)
def a6e (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):j6 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl),(c.var,b),d5 c.stk i w t o⟩
lemma c0u (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    TM2.stepAux (trF q) ((v,b):b00 M) (d5 S i w t o) =
      a6e b i w t o (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v::S k))
    rw [← d23] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← d23] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
lemma c0o (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool) (b:Option (Bool ⊕ Bool))
    (i:List (Bool ⊕ Bool)) (w t:List Bool) (o:List (Bool ⊕ Bool))
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
    TM2.step (c0 M e₀ e₁) (a6e b i w t o c)=some (a6e b i w t o c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (c0u b i w t o (M.m l) v S)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
lemma l9 {σ:Type} (f:σ→ Option σ) {a b:ℕ} {x y z:σ}
    (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z) :
    (flip bind f)^[b+a] (some x)=some z:=by
  rw [Function.iterate_add_apply,h₁,h₂]
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool)
section d5
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool))
@[simp] lemma c37 (k:M.K):d5 S i w t o (Sum.inl k)=S k:=rfl
@[simp] lemma c33:d5 S i w t o (Sum.inr FX.I)=i:=rfl
@[simp] lemma c34:d5 S i w t o (Sum.inr FX.W)=w:=rfl
@[simp] lemma c31:d5 S i w t o (Sum.inr FX.T)=t:=rfl
@[simp] lemma c36:d5 S i w t o (Sum.inr FX.O)=o:=rfl
end d5
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:List Bool) (o:List (Bool ⊕ Bool))
lemma b94 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),d5 S (Sum.inl a::i) w t o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),d5 S i w (a::t) o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d33,d18,a58,bit]
lemma b9n (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),d5 S (Sum.inr a::i) w t o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),d5 S i (a::w) t o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d33,d45,a58,bit]
lemma b8n (b:Option (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),d5 S [] w t o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l2),(v,none),d5 S [] w t o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d33]
lemma c0c:∀ (i:List (Bool ⊕ Bool)) (w t:List Bool) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (c0 M e₀ e₁)))^[i.length+1]
        (some (⟨some (Sum.inr FL.l1),(v,b),d5 S i w t o⟩:j6 M)) =
      some ⟨some (Sum.inr FL.l2),(v,none),
        d5 S [] ((i.filterMap Sum.getRight?).reverse++w)
          ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
  intro i
  induction i with
  | nil=>intro w t b;exact b8n e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons,Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e:flip bind (TM2.step (c0 M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1),(v,b),d5 S (Sum.inl a::i) w t o⟩:j6 M)) =
          some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),d5 S i w (a::t) o⟩ :=
        b94 e₀ e₁ v S w o b a i t
      rw [e,ih];simp [List.filterMap_cons]
    | inr a =>
      have e:flip bind (TM2.step (c0 M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1),(v,b),d5 S (Sum.inr a::i) w t o⟩:j6 M)) =
          some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),d5 S i (a::w) t o⟩ :=
        b9n e₀ e₁ v S w o b a i t
      rw [e,ih];simp [List.filterMap_cons]
lemma c1w (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l2),(v,b),d5 S [] w (a::t) o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
        d5 (Function.update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d18,d23,bit]
lemma b8s (b:Option (Bool ⊕ Bool)) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l2),(v,b),d5 S [] w [] o⟩:j6 M) =
      some ⟨some (Sum.inl M.main),(v,none),d5 S [] w [] o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d18]
lemma c0f:∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (c0 M e₀ e₁)))^[t.length+1]
        (some (⟨some (Sum.inr FL.l2),(v,b),d5 S [] w t o⟩:j6 M)) =
      some ⟨some (Sum.inl M.main),(v,none),
        d5 (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) [] w [] o⟩:=by
  intro t
  induction t with
  | nil =>
    intro S b
    have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
    rw [this]
    exact b8s e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (c0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2),(v,b),d5 S [] w (a::t) o⟩:j6 M)) =
        some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
          d5 (Function.update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=c1w e₀ e₁ v S w o b a t
    rw [e,ih];simp
lemma c2t (b:Option (Bool ⊕ Bool)) (a:Bool) (w:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l3),(v,b),d5 S [] (a::w) [] o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),d5 S [] w [] (Sum.inr a::o)⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d45,d46,bit]
lemma b8v (b:Option (Bool ⊕ Bool)) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l3),(v,b),d5 S [] [] [] o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l4),(v,none),d5 S [] [] [] o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d45]
lemma c0e:∀ (w:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (c0 M e₀ e₁)))^[w.length+1]
        (some (⟨some (Sum.inr FL.l3),(v,b),d5 S [] w [] o⟩:j6 M)) =
      some ⟨some (Sum.inr FL.l4),(v,none),d5 S [] [] [] (w.reverse.map Sum.inr++o)⟩:=by
  intro w
  induction w with
  | nil=>intro o b;exact b8v e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (c0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3),(v,b),d5 S [] (a::w) [] o⟩:j6 M)) =
        some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),d5 S [] w [] (Sum.inr a::o)⟩ :=
      c2t e₀ e₁ v S o b a w
    rw [e,ih];simp
lemma c1c (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l4),(v,b),d5 (Function.update S M.k₁ (y::m)) [] [] t o⟩ :
          j6 M) =
      some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
        d5 (Function.update S M.k₁ m) [] [] (e₁ y::t) o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d18,d23,bit]
lemma b9u (b:Option (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l4),(v,b),d5 (Function.update S M.k₁ []) [] [] t o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l5),(v,none),d5 (Function.update S M.k₁ []) [] [] t o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d23]
lemma c0p:∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (c0 M e₀ e₁)))^[m.length+1]
        (some (⟨some (Sum.inr FL.l4),(v,b),d5 (Function.update S M.k₁ m) [] [] t o⟩ :
          j6 M)) =
      some ⟨some (Sum.inr FL.l5),(v,none),
        d5 (Function.update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact b9u e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (c0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4),(v,b),d5 (Function.update S M.k₁ (y::m)) [] [] t o⟩ :
          j6 M)) =
        some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
          d5 (Function.update S M.k₁ m) [] [] (e₁ y::t) o⟩:=c1c e₀ e₁ v S o b y m t
    rw [e,ih];simp
lemma c2d (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l5),(v,b),d5 S [] [] (a::t) o⟩:j6 M) =
      some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),d5 S [] [] t (Sum.inl a::o)⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d18,d46,bit]
lemma b99 (b:Option (Bool ⊕ Bool)) :
    TM2.step (c0 M e₀ e₁)
        (⟨some (Sum.inr FL.l5),(v,b),d5 S [] [] [] o⟩:j6 M) =
      some ⟨none,(v,none),d5 S [] [] [] o⟩:=by
  simp [TM2.step,c0,TM2.stepAux,d18]
lemma c0j:∀ (t:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (c0 M e₀ e₁)))^[t.length+1]
        (some (⟨some (Sum.inr FL.l5),(v,b),d5 S [] [] t o⟩:j6 M)) =
      some ⟨none,(v,none),d5 S [] [] [] (t.reverse.map Sum.inl++o)⟩:=by
  intro t
  induction t with
  | nil=>intro o b;exact b99 e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (c0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5),(v,b),d5 S [] [] (a::t) o⟩:j6 M)) =
        some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),d5 S [] [] t (Sum.inl a::o)⟩ :=
      c2d e₀ e₁ v S o b a t
    rw [e,ih];simp
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool)
lemma d97:(d5 (fun _=>[]) [] [] [] []:∀ k,List (a2s M k))=fun _=>[]:=by
  funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
lemma d96 (i:List (Bool ⊕ Bool)) :
    (d5 (fun _=>[]) i [] [] []:∀ k,List (a2s M k)) =
      Function.update (fun _=>[]:∀ k,List (a2s M k)) (Sum.inr FX.I) i :=
  (d33 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d97])
lemma d95 (o:List (Bool ⊕ Bool)) :
    (d5 (fun _=>[]) [] [] [] o:∀ k,List (a2s M k)) =
      Function.update (fun _=>[]:∀ k,List (a2s M k)) (Sum.inr FX.O) o :=
  (d46 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d97])
lemma c1f (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)) :
    a6e b i w t o (initList M l) =
      (⟨some (Sum.inl M.main),(M.initialState,b),
        d5 (Function.update (fun _=>[]) M.k₀ l) i w t o⟩:j6 M):=by
  rw [i7];rfl
lemma c19 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)) :
    a6e b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3),(M.initialState,b),
        d5 (Function.update (fun _=>[]) M.k₁ m) i w t o⟩:j6 M):=by
  rw [i9];rfl
lemma d16 {γ δ:Type} (l:List γ) :
    l.filterMap (fun _=>(none:Option δ))=[]:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp
lemma d26 (x w:List Bool) :
    (encodePair (x,w)).filterMap Sum.getLeft?= x:=by
  have h1:(Sum.getLeft?∘ (Sum.inl:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=some:=rfl
  have h2:(Sum.getLeft?∘ (Sum.inr:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=fun _=>none:=rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,d16,List.append_nil]
lemma d24 (x w:List Bool) :
    (encodePair (x,w)).filterMap Sum.getRight?= w:=by
  have h1:(Sum.getRight?∘ (Sum.inl:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=fun _=>none:=rfl
  have h2:(Sum.getRight?∘ (Sum.inr:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=some:=rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,d16,List.nil_append]
lemma r8 (x w:List Bool) :
    (encodePair (x,w)).length=x.length+w.length:=by
  simp [encodePair]
lemma b42 (x w0:List Bool) (m:List (M.Γ M.k₁)) (s:ℕ)
    (h:(flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)) :
    ∃ n,n ≤ s+2 * x.length+2 * w0.length+2 * m.length+5 ∧
      (flip bind (TM2.step (c0 M e₀ e₁)))^[n]
          (some (initList (z9 M e₀ e₁) (encodePair (x,w0)))) =
        some (haltList (z9 M e₀ e₁) (encodePair (m.map e₁,w0))):=by
  have q1:(flip bind (TM2.step (c0 M e₀ e₁)))^[(encodePair (x,w0)).length+1]
      (some (initList (z9 M e₀ e₁) (encodePair (x,w0)))) =
      some (⟨some (Sum.inr FL.l2),(M.initialState,none),
        d5 (fun _=>[]) [] w0.reverse x.reverse []⟩:j6 M):=by
    have:=c0c e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,w0)) [] [] none
    rw [d26,d24,List.append_nil,List.append_nil,d96] at this
    exact (congrArg (fun c=>(flip bind (TM2.step (c0 M e₀ e₁)))^[
      (encodePair (x,w0)).length+1] (some c))
      (i7 (z9 M e₀ e₁) (encodePair (x,w0)))).trans this
  have q2:(flip bind (TM2.step (c0 M e₀ e₁)))^[x.reverse.length+1]
      (some (⟨some (Sum.inr FL.l2),(M.initialState,none),
        d5 (fun _=>[]) [] w0.reverse x.reverse []⟩:j6 M)) =
      some (a6e none [] w0.reverse [] [] (initList M (x.map e₀))):=by
    have:=c0f e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _=>[]) none
    rw [c1f]
    simpa using this
  have q3:=a3r (TM2.step M.m) (TM2.step (c0 M e₀ e₁))
    (a6e none [] w0.reverse [] []) (c0o e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [c19] at q3
  have q4:(flip bind (TM2.step (c0 M e₀ e₁)))^[w0.reverse.length+1]
      (some (⟨some (Sum.inr FL.l3),(M.initialState,none),
        d5 (Function.update (fun _=>[]) M.k₁ m) [] w0.reverse [] []⟩:j6 M)) =
      some (⟨some (Sum.inr FL.l4),(M.initialState,none),
        d5 (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:j6 M):=by
    have:=c0e e₀ e₁ M.initialState (Function.update (fun _=>[]) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5:(flip bind (TM2.step (c0 M e₀ e₁)))^[m.length+1]
      (some (⟨some (Sum.inr FL.l4),(M.initialState,none),
        d5 (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:j6 M)) =
      some (⟨some (Sum.inr FL.l5),(M.initialState,none),
        d5 (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:j6 M):=by
    have:=c0p e₀ e₁ M.initialState (fun _=>[]) (w0.map Sum.inr) m [] none
    simpa using this
  have q6:(flip bind (TM2.step (c0 M e₀ e₁)))^[(m.reverse.map e₁).length+1]
      (some (⟨some (Sum.inr FL.l5),(M.initialState,none),
        d5 (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:j6 M)) =
      some (haltList (z9 M e₀ e₁) (encodePair (m.map e₁,w0))):=by
    have:=c0j e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [d95] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (i9 (z9 M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_,?_,l9 _ (l9 _ (l9 _ (l9 _ (l9 _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [r8,List.length_reverse,List.length_map]
  omega
lemma a7m (f:List Bool→ List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(f p.1,p.2))):=by
  let e₀:Bool→ c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let e₁:c.tm.Γ c.tm.k₁→ Bool:=c.outputAlphabet
  let T:Polynomial ℕ :=
    c.time+Polynomial.C 2* (Polynomial.X+Polynomial.C (p7 c.tm)* c.time) +
      Polynomial.C 2* Polynomial.X+Polynomial.C 5
  have key:∀ p:List Bool × List Bool,∃ n,n≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (c0 c.tm e₀ e₁)))^[n]
          (some (initList (z9 c.tm e₀ e₁) (encodePair p))) =
        some (haltList (z9 c.tm e₀ e₁) (encodePair (f p.1,p.2))):=by
    rintro ⟨x,w⟩
    have hs:∃ s,s≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
    obtain ⟨s,b1,h⟩:=hs
    obtain ⟨n,hn,hrun⟩:=b42 e₀ e₁ x w _ s h
    have hm:(List.map c.outputAlphabet.invFun (f x)).map e₁=f x:=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n,hn.trans ?_,hrun⟩
    have h':=h
    rw [i9,i7] at h'
    have hlen:=a3m c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self,List.length_map] at hlen
    have hin:((Function.update (fun _=>[]:∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length≤ x.length:=by
      by_cases hk:c.tm.k₁=c.tm.k₀
      · rw [hk,Function.update_self,List.length_map]
      · rw [Function.update_of_ne hk];simp
    have b2:Polynomial.eval x.length c.time≤ Polynomial.eval (x.length+w.length) c.time :=
      a0h _ (by omega)
    have j1:p7 c.tm* s ≤
        p7 c.tm* Polynomial.eval (x.length+w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,r8,List.length_map]
    omega
  exact ⟨{
    tm:=z9 c.tm e₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun p =>
      { steps:=Classical.choose (key p)
        evals_in_steps:=by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (c0 c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (z9 c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l=>some (haltList (z9 c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1,p.2))).symm))
        steps_le_m:=(Classical.choose_spec (key p)).1 } }⟩
end Lib.Machines
end
section
namespace Lib.Machines.Iter
open Turing
inductive IX
  | I | C | T | O
  deriving DecidableEq
instance:Fintype IX :=
  Fintype.ofList [IX.I,IX.C,IX.T,IX.O] (fun x=>by cases x <;> simp)
inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq
instance:Fintype IL :=
  Fintype.ofList [IL.l1,IL.l2,IL.l3,IL.l4,IL.l5,IL.l6] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev ItΓ:M.K ⊕ IX→ Type
  | Sum.inl k=>M.Γ k
  | Sum.inr IX.I=>Bool ⊕ Bool
  | Sum.inr IX.C=>Bool
  | Sum.inr IX.T=>Bool
  | Sum.inr IX.O=>Bool
abbrev ItΛ:Type:=M.Λ ⊕ IL
abbrev Itσ:Type:=M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ→ TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q=>.push (Sum.inl k) (fun s=>f s.1) (trI q)
  | .peek k f q=>.peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
  | .pop k f q=>.pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
  | .load a q=>.load (fun s=>(a s.1,s.2)) (trI q)
  | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trI q₁) (trI q₂)
  | .goto f=>.goto (fun s=>Sum.inl (f s.1))
  | .halt=>.goto (fun _=>Sum.inr IL.l4)
variable (M)
def c5 (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool) :
    ItΛ M→ TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l=>trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o=>(s.1,o))
      (.branch (fun s=>s.2.isSome)
        (.branch (fun s=>a58 s.2)
          (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1))
          (.push (Sum.inr IX.C) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1)))
        (.goto fun _=>Sum.inr IL.l2))
  | Sum.inr IL.l2 =>
    .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr IL.l2))
        (.goto fun _=>Sum.inr IL.l3))
  | Sum.inr IL.l3 =>
    .pop (Sum.inr IX.C) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.goto fun _=>Sum.inl M.main)
        (.goto fun _=>Sum.inr IL.l5))
  | Sum.inr IL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l4))
        (.goto fun _=>Sum.inr IL.l2))
  | Sum.inr IL.l5 =>
    .pop (Sum.inl M.k₀) (fun s o=>(s.1,o.map fun y=>Sum.inl (d₀ y)))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l5))
        (.goto fun _=>Sum.inr IL.l6))
  | Sum.inr IL.l6 =>
    .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr IX.O) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l6))
        .halt)
def a0a (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ IX
    k₀:=Sum.inr IX.I
    k₁:=Sum.inr IX.O
    Γ:=ItΓ M
    Λ:=ItΛ M
    main:=Sum.inr IL.l1
    σ:=Itσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=c5 M e₀ d₀ e₁ }
variable {M}
def d4 (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    ∀ k,List (ItΓ M k)
  | Sum.inl k=>S k
  | Sum.inr IX.I=>i
  | Sum.inr IX.C=>cn
  | Sum.inr IX.T=>t
  | Sum.inr IX.O=>o
section d4
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
@[simp] lemma c2y (k:M.K):d4 S i cn t o (Sum.inl k)=S k:=rfl
@[simp] lemma c2z:d4 S i cn t o (Sum.inr IX.I)=i:=rfl
@[simp] lemma c30:d4 S i cn t o (Sum.inr IX.C)=cn:=rfl
@[simp] lemma c32:d4 S i cn t o (Sum.inr IX.T)=t:=rfl
@[simp] lemma c35:d4 S i cn t o (Sum.inr IX.O)=o:=rfl
lemma d15 (k:M.K) (x:List (M.Γ k)) :
    Function.update (d4 S i cn t o) (Sum.inl k) x=d4 (Function.update S k x) i cn t o:=by
  funext j
  rcases j with j | j
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show x=Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j=Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)];cases j <;> rfl
lemma d32 (i':List (Bool ⊕ Bool)) :
    Function.update (d4 S i cn t o) (Sum.inr IX.I) i'=d4 S i' cn t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
lemma d44 (cn':List Bool) :
    Function.update (d4 S i cn t o) (Sum.inr IX.C) cn'=d4 S i cn' t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
lemma d14 (t':List Bool) :
    Function.update (d4 S i cn t o) (Sum.inr IX.T) t'=d4 S i cn t' o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
lemma d72 (o':List Bool) :
    Function.update (d4 S i cn t o) (Sum.inr IX.O) o'=d4 S i cn t o':=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
end d4
abbrev m9 (M:FinTM2):Type:=TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def a5u (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c:TM2.Cfg M.Γ M.Λ M.σ):m9 M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl),(c.var,b),d4 c.stk i cn t o⟩
lemma c1p (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    TM2.stepAux (trI q) ((v,b):Itσ M) (d4 S i cn t o) =
      a5u b i cn t o (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v::S k))
    rw [← d15] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← d15] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
lemma c09 (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool)
    (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
    TM2.step (c5 M e₀ d₀ e₁) (a5u b i cn t o c)=some (a5u b i cn t o c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (c1p b i cn t o (M.m l) v S)
lemma c23 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (l:List (M.Γ M.k₀)) :
    a5u b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main),(M.initialState,b),
        d4 (Function.update (fun _=>[]) M.k₀ l) i cn t o⟩:m9 M):=by
  rw [i7];rfl
lemma c1u (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (m:List (M.Γ M.k₁)) :
    a5u b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4),(M.initialState,b),
        d4 (Function.update (fun _=>[]) M.k₁ m) i cn t o⟩:m9 M):=by
  rw [i9];rfl
lemma d94:(d4 (fun _=>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _=>[]:=by
  funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
lemma d93 (i:List (Bool ⊕ Bool)) :
    (d4 (fun _=>[]) i [] [] []:∀ k,List (ItΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.I) i :=
  (d32 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d94])
lemma d92 (o:List Bool) :
    (d4 (fun _=>[]) [] [] [] o:∀ k,List (ItΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.O) o :=
  (d72 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d94])
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
lemma b9t (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),d4 S (Sum.inl a::i) cn t o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),d4 S i cn (a::t) o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d32,d14,a58,bit]
lemma c04 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),d4 S (Sum.inr a::i) cn t o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),d4 S i (a::cn) t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d32,d44,a58,bit]
lemma b9g (b:Option (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),d4 S [] cn t o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l2),(v,none),d4 S [] cn t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d32]
lemma b9f (o:List Bool) :
    ∀ (i:List (Bool ⊕ Bool)) (cn t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[i.length+1]
        (some (⟨some (Sum.inr IL.l1),(v,b),d4 S i cn t o⟩:m9 M)) =
      some ⟨some (Sum.inr IL.l2),(v,none),
        d4 S [] ((i.filterMap Sum.getRight?).reverse++cn)
          ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
  intro i
  induction i with
  | nil=>intro cn t b;exact b9g e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons,Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e:(flip bind (TM2.step (c5 M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1),(v,b),d4 S (Sum.inl a::i) cn t o⟩:m9 M)) =
          some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),d4 S i cn (a::t) o⟩ :=
        b9t e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih];simp [List.filterMap_cons]
    | inr a =>
      have e:(flip bind (TM2.step (c5 M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1),(v,b),d4 S (Sum.inr a::i) cn t o⟩:m9 M)) =
          some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),d4 S i (a::cn) t o⟩ :=
        c04 e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih];simp [List.filterMap_cons]
lemma c2p (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2),(v,b),d4 S i cn (a::t) o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
        d4 (Function.update S M.k₀ (e₀ a::S M.k₀)) i cn t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d14,d15,bit]
lemma b96 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2),(v,b),d4 S i cn [] o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l3),(v,none),d4 S i cn [] o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d14]
lemma b3w (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (Sum.inr IL.l2),(v,b),d4 S i cn t o⟩:m9 M)) =
      some ⟨some (Sum.inr IL.l3),(v,none),
        d4 (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) i cn [] o⟩:=by
  intro t
  induction t with
  | nil =>
    intro S b
    have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
    rw [this]
    exact b96 e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (c5 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2),(v,b),d4 S i cn (a::t) o⟩:m9 M)) =
        some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
          d4 (Function.update S M.k₀ (e₀ a::S M.k₀)) i cn t o⟩ :=
      c2p e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih];simp
lemma c1h (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3),(v,b),d4 S i (a::cn) t o⟩:m9 M) =
      some ⟨some (Sum.inl M.main),(v,some (Sum.inl a)),d4 S i cn t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d44]
lemma b98 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3),(v,b),d4 S i [] t o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l5),(v,none),d4 S i [] t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d44]
lemma c1i (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
    (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4),(v,b),d4 (Function.update S M.k₁ (y::m)) i cn t o⟩ :
          m9 M) =
      some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
        d4 (Function.update S M.k₁ m) i cn (e₁ y::t) o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d14,d15,bit]
lemma b8x (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4),(v,b),d4 (Function.update S M.k₁ []) i cn t o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l2),(v,none),d4 (Function.update S M.k₁ []) i cn t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d15]
lemma b9b (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (Sum.inr IL.l4),(v,b),d4 (Function.update S M.k₁ m) i cn t o⟩ :
          m9 M)) =
      some ⟨some (Sum.inr IL.l2),(v,none),
        d4 (Function.update S M.k₁ []) i cn (m.reverse.map e₁++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact b8x e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (c5 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4),(v,b),
          d4 (Function.update S M.k₁ (y::m)) i cn t o⟩:m9 M)) =
        some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
          d4 (Function.update S M.k₁ m) i cn (e₁ y::t) o⟩ :=
      c1i e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih];simp
lemma c2r (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
    (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5),(v,b),d4 (Function.update S M.k₀ (y::m)) i cn t o⟩ :
          m9 M) =
      some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
        d4 (Function.update S M.k₀ m) i cn (d₀ y::t) o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d14,d15,bit]
lemma b8l (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5),(v,b),d4 (Function.update S M.k₀ []) i cn t o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l6),(v,none),d4 (Function.update S M.k₀ []) i cn t o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d15]
lemma b9r (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (m:List (M.Γ M.k₀)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (Sum.inr IL.l5),(v,b),d4 (Function.update S M.k₀ m) i cn t o⟩ :
          m9 M)) =
      some ⟨some (Sum.inr IL.l6),(v,none),
        d4 (Function.update S M.k₀ []) i cn (m.reverse.map d₀++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact b8l e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (c5 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5),(v,b),
          d4 (Function.update S M.k₀ (y::m)) i cn t o⟩:m9 M)) =
        some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
          d4 (Function.update S M.k₀ m) i cn (d₀ y::t) o⟩ :=
      c2r e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih];simp
lemma c1a (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6),(v,b),d4 S i cn (a::t) o⟩:m9 M) =
      some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),d4 S i cn t (a::o)⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d14,d72,bit]
lemma c02 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    TM2.step (c5 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6),(v,b),d4 S i cn [] o⟩:m9 M) =
      some ⟨none,(v,none),d4 S i cn [] o⟩:=by
  simp [TM2.step,c5,TM2.stepAux,d14]
lemma b8t (i:List (Bool ⊕ Bool)) (cn:List Bool) :
    ∀ (t o:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (Sum.inr IL.l6),(v,b),d4 S i cn t o⟩:m9 M)) =
      some ⟨none,(v,none),d4 S i cn [] (t.reverse++o)⟩:=by
  intro t
  induction t with
  | nil=>intro o b;exact c02 e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (c5 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6),(v,b),d4 S i cn (a::t) o⟩:m9 M)) =
        some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),d4 S i cn t (a::o)⟩ :=
      c1a e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih];simp
lemma d28 (k:M.K) :
    Function.update (fun _=>[]:∀ k,List (M.Γ k)) k []=fun _=>[] :=
  Function.update_eq_self k (fun _=>[]:∀ k,List (M.Γ k))
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool)
lemma a91 (g:List Bool→ List Bool) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z) :
    ∀ (cn z:List Bool) (L:ℕ) (b:Option (Bool ⊕ Bool)),
      (∀ j≤ cn.length,(g^[j] z).length≤ L) →
      ∃ n,n ≤ cn.length * (p.eval L+2 * L+3)+2 * L+3 ∧
        ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
              d4 (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:m9 M)) =
          some ⟨none,(M.initialState,none),
            d4 (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
      rw [List.map_reverse,List.reverse_reverse,List.map_map]
      conv_rhs=>rw [← List.map_id z]
      exact List.map_congr_left fun a _=>hd a
    have q1:((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          d4 (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:m9 M)) =
        some ⟨some (Sum.inr IL.l5),(M.initialState,none),
          d4 (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      b98 e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2:=b9r e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none
    rw [d28,List.append_nil] at q2
    have q3:=b8t e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil,hz] at q3
    refine ⟨_,?_,l9 _ (l9 _ q1 q2) q3⟩
    have hz0:z.length≤ L:=hL 0 (Nat.zero_le _)
    simp only [List.length_reverse,List.length_map,List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s,m,hs,hm,hmg⟩:=hrun z
    rw [List.length_cons] at hL
    have hz0:z.length≤ L:=hL 0 (Nat.zero_le _)
    have hgz:(g z).length≤ L:=hL 1 (by omega)
    have hml:m.length=(g z).length:=by rw [← hmg,List.length_map]
    have q1:((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          d4 (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] (a::cn) [] []⟩:m9 M)) =
        some (a5u (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))):=by
      rw [c23]
      exact c1h e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2:=a3r (TM2.step M.m) (TM2.step (c5 M e₀ d₀ e₁))
      (a5u (some (Sum.inl a)) [] cn [] []) (c09 e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [c1u] at q2
    have q3:=b9b e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (Sum.inl a))
    rw [d28,List.append_nil,List.map_reverse,hmg] at q3
    have q4:=b3w e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none
    rw [List.append_nil,List.reverse_reverse] at q4
    obtain ⟨n,hn,q5⟩:=ih (g z) L none (fun j hj=>by
      have:=hL (j+1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e:g^[(a::cn).length] z=g^[cn.length] (g z):=Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_,?_,l9 _ (l9 _ (l9 _ (l9 _ q1 q2) q3) q4) q5⟩
    have hp:p.eval z.length≤ p.eval L:=a0h p (by omega)
    rw [List.length_reverse,List.length_cons,Nat.succ_mul]
    generalize cn.length* (p.eval L+2* L+3)=A at hn ⊢
    omega
lemma a4l (g:List Bool→ List Bool) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z)
    (y u:List Bool) (L:ℕ) (hL:∀ j≤ u.length,(g^[j] y).length≤ L) :
    ∃ n,n ≤ u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5 ∧
      ((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[n] (some (initList (a0a M e₀ d₀ e₁) (encodePair (y,u)))) =
        some (haltList (a0a M e₀ d₀ e₁) (g^[u.length] y)):=by
  have q1:((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
      (some (initList (a0a M e₀ d₀ e₁) (encodePair (y,u)))) =
      some (⟨some (Sum.inr IL.l2),(M.initialState,none),
        d4 (fun _=>[]) [] u.reverse y.reverse []⟩:m9 M):=by
    have:=b9f e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none
    rw [d26,d24,List.append_nil,List.append_nil,d93] at this
    exact (congrArg (fun c=>((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
      (i7 (a0a M e₀ d₀ e₁) (encodePair (y,u)))).trans this
  have q2:=b3w e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none
  rw [List.append_nil,List.reverse_reverse] at q2
  obtain ⟨n,hn,q3⟩:=a91 e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse];exact hL)
  rw [List.length_reverse] at hn q3
  rw [d92] at q3
  have q3':((flip bind (TM2.step (c5 M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3),(M.initialState,none),
        d4 (Function.update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:m9 M)) =
      some (haltList (a0a M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (i9 (a0a M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_,?_,l9 _ (l9 _ q1 q2) q3'⟩
  rw [r8,List.length_reverse]
  omega
lemma d22 (g:List Bool→ List Bool) (m:List Bool→ ℕ)
    (hm:∀ y:List Bool,m (g y)≤ m y)
    (hg:∀ y:List Bool,(g y).length≤ y.length+m y) (y:List Bool) :
    ∀ j:ℕ,m (g^[j] y)≤ m y∧(g^[j] y).length≤ y.length+j* m y:=by
  intro j
  induction j with
  | zero=>simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',Nat.succ_mul]
    have h1:=hm (g^[j] y)
    have h2:=hg (g^[j] y)
    obtain ⟨i1,i2⟩:=ih
    generalize j* m y=A at i2 ⊢
    exact ⟨by omega,by omega⟩
lemma d70 (A B L V y u:ℕ) (hLV:L≤ V) (hAB:A≤ B) :
    A+2* L+2* y+u+5≤ B+2* V+3* (y+u)+5:=by
  omega
lemma a0g (g:List Bool→ List Bool)
    (c:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (m:List Bool→ ℕ) (a:ℕ)
    (hm:∀ y:List Bool,m (g y)≤ m y)
    (hg:∀ y:List Bool,(g y).length≤ y.length+m y)
    (ha:∀ y:List Bool,m y≤ a* y.length+a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>g^[p.2.length] p.1)):=by
  let e₀:Bool→ c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let d₀:c.tm.Γ c.tm.k₀→ Bool:=c.inputAlphabet
  let e₁:c.tm.Γ c.tm.k₁→ Bool:=c.outputAlphabet
  let W:Polynomial ℕ :=
    Polynomial.X+Polynomial.X* (Polynomial.C a* Polynomial.X+Polynomial.C a)
  let T:Polynomial ℕ :=
    Polynomial.X* (c.time.comp W+Polynomial.C 2* W+Polynomial.C 3) +
      Polynomial.C 2* W+Polynomial.C 3* Polynomial.X+Polynomial.C 5
  have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
  have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
      s≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m)∧m.map e₁=g z:=by
    intro z
    refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
  have key:∀ q:List Bool × List Bool,∃ n,n≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (c5 c.tm e₀ d₀ e₁)))^[n]
          (some (initList (a0a c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (a0a c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
    rintro ⟨y,u⟩
    have hL:∀ j≤ u.length,
        (g^[j] y).length≤ y.length+u.length* (a* y.length+a):=by
      intro j hj
      have h1:=(d22 g m hm hg y j).2
      have h2:j* m y≤ u.length* (a* y.length+a):=Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n,hn,hr⟩:=a4l e₀ d₀ e₁ g c.time hd hrun y u
      (y.length+u.length* (a* y.length+a)) hL
    have hLV:y.length+u.length* (a* y.length+a) ≤
        (y.length+u.length)+(y.length+u.length)* (a* (y.length+u.length)+a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp:=a0h c.time hLV
    have j1:u.length* (Polynomial.eval (y.length+u.length* (a* y.length+a)) c.time +
          2* (y.length+u.length* (a* y.length+a))+3) ≤
        (y.length+u.length)* (Polynomial.eval
          ((y.length+u.length)+(y.length+u.length)* (a* (y.length+u.length)+a))
            c.time +
            2 * ((y.length+u.length) +
              (y.length+u.length)* (a* (y.length+u.length)+a))+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n,hn.trans ?_,hr⟩
    simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,r8]
    exact d70 _ _ _ _ _ _ hLV j1
  exact ⟨{
    tm:=a0a c.tm e₀ d₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun q =>
      { steps:=Classical.choose (key q)
        evals_in_steps:=by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (c5 c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (a0a c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l=>some (haltList (a0a c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
lemma a1g (g:List Bool→ List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (k:ℕ) (hk:∀ y:List Bool,(g y).length≤ y.length+k) :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
  a0g g c (fun _=>k) k (fun _=>le_rfl) hk (fun _=>Nat.le_add_left k _)
end Lib.Machines.Iter
end
section
namespace Lib.Machines
open PEqualNP.Library
private lemma d2 {α β γ:Type} (h:α→ β) (φ:β→ Option γ) (g:α→ γ)
    (hφ:∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ= l.map g:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [hφ,ih]
private lemma d8 {α β γ:Type} (h:α→ β) (φ:β→ Option γ)
    (hφ:∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ= []:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [hφ,ih]
lemma a2 {α β γ αΓ βΓ γΓ:Type} {ea:α→ List αΓ} {eb:β→ List βΓ}
    {ec:γ→ List γΓ} {f:α→ β} {g:β→ γ}
    (hf:PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg:PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a=>g (f a)):=by
  obtain ⟨c1⟩:=hf
  obtain ⟨c2⟩:=hg
  exact a99 ea eb ec f g c1 c2
lemma a69 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.2,p.1)):=by
  refine w4 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some (Sum.inl b)) s)
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some (Sum.inr b)) (fun _=>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d8 Sum.inl _ (fun _=>rfl) x,
    d2 Sum.inr _ Sum.inl (fun _=>rfl) w,
    d2 Sum.inl _ Sum.inr (fun _=>rfl) x,
    d8 Sum.inr _ (fun _=>rfl) w]
  simp
lemma b76 :
    PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
      PEqualNP.Library.encodePair (fun x:List Bool=>(x,x)):=by
  refine w4 _ _ _
    (fun b:Bool=>some (Sum.inl b)) (fun b:Bool=>some (Sum.inr b)) ?_
  intro x
  have h1:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inl (β:=Bool) b))
    Sum.inl (fun _=>rfl) x
  have h2:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inr (α:=Bool) b))
    Sum.inr (fun _=>rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair,h1,h2]
lemma b6z :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1):=by
  refine t4 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
    d8 Sum.inr _ (fun _=>rfl) w]
  simp
lemma b75 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.2):=by
  refine t4 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d8 Sum.inl _ (fun _=>rfl) x,
    d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
  simp
lemma a7c :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1++p.2):=by
  refine t4 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
    d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
  simp
lemma a2p {f:List Bool→ List Bool}
    (hf:Lib.a4 f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(f p.1,p.2)):=by
  obtain ⟨c⟩:=hf
  exact a7m f c
lemma b2f {g:List Bool→ List Bool}
    (hg:Lib.a4 g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.1,g p.2)) :=
  a2 (a2 a69 (a2p hg)) a69
lemma x7 {f g:List Bool→ List Bool}
    (hf:Lib.a4 f)
    (hg:Lib.a4 g) :
    PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
      PEqualNP.Library.encodePair (fun x:List Bool=>(f x,g x)) :=
  a2 (a2 b76 (b2f hg)) (a2p hf)
lemma g5 :
    Lib.a4 (fun x:List Bool=>x):=by
  refine t4 _ _ _ (fun b:Bool=>some b) ?_
  intro x
  have h:=d2 (fun b:Bool=>b) (fun b:Bool=>some b) (fun b=>b)
    (fun _=>rfl) x
  simp only [List.map_id'] at h
  exact h.symm
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def c7 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁) :
    Q→ List Γ₀→ List Γ₁
  | q,[]=>(fin q).toList
  | q,a::l=>(δ q a).2.toList++c7 δ fin (δ q a).1 l
def p6 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
    Q→ List Γ₀→ List Γ₁
  | q,[]=>(fin q).toList
  | q,a::l=>(δ q a).2.1.toList++(δ q a).2.2.toList++p6 δ fin (δ q a).1 l
lemma d36 {Γ₀ Γ₁ Q:Type} (δ:Q→ Γ₀→ Q × Option Γ₁) (fin:Q→ Option Γ₁)
    (q:Q) (l:List Γ₀) :
    c7 δ fin q l=p6 (fun q a=>((δ q a).1,(δ q a).2,none)) fin q l:=by
  induction l generalizing q with
  | nil=>rfl
  | cons a l ih=>simp [c7,p6,ih]
inductive TrK:Type
  | inp | tmp | out
  deriving DecidableEq
instance:Fintype TrK :=
  Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK→ Type
  | .inp=>Γ₀
  | .tmp=>Q × Option Γ₀
  | .out=>Γ₁
abbrev TrS (Γ₀ Q:Type):Type:=Q × Option Γ₀ × Bool
def b30 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
    Q × Option Γ₀→ Option Γ₁
  | (q,some a)=>(δ q a).2.1
  | (q,none)=>fin q
def b2b (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁):Q × Option Γ₀→ Option Γ₁
  | (q,some a)=>(δ q a).2.2
  | (_,none)=>none
def a3j (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁)
    (e:Q × Option Γ₀):List Γ₁ :=
  (b30 δ fin e).toList++(b2b δ e).toList
def d21 (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁):Q→ List Γ₀→ List (Q × Option Γ₀)
  | q,[]=>[(q,none)]
  | q,a::l=>(q,some a)::d21 δ (δ q a).1 l
lemma d57 (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (q:Q) (l:List Γ₀) :
    (d21 δ q l).length=l.length+1:=by
  induction l generalizing q with
  | nil=>rfl
  | cons a l ih=>simp [d21,ih]
lemma d85 (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) (q:Q)
    (l:List Γ₀):(d21 δ q l).flatMap (a3j δ fin)=p6 δ fin q l:=by
  induction l generalizing q with
  | nil=>simp [d21,a3j,b30,b2b,p6]
  | cons a l ih=>simp [d21,a3j,b30,b2b,p6,ih]
def d65 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s=>(o s).isSome)
    (match d with
      | some dd=>.push .out (fun s=>(o s).getD dd) next
      | none=>next)
    next
def o4 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
    (d:Option Γ₁):Bool→ TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o=>(s.1,o,o.isSome))
      (.branch (fun s=>s.2.2)
        (.push .tmp (fun s=>(s.1,s.2.1))
          (.load (fun s=>(match s.2.1 with
              | some a=>(δ s.1 a).1
              | none=>s.1,none,false))
            (.goto fun _=>false)))
        (.push .tmp (fun s=>(s.1,none))
          (.load (fun _=>(q₀,none,false)) (.goto fun _=>true))))
  | true =>
    .pop .tmp (fun _ o=>match o with
        | some e=>(e.1,e.2,true)
        | none=>(q₀,none,false))
      (.branch (fun s=>s.2.2)
        (d65 (fun s=>b2b δ (s.1,s.2.1)) d
          (d65 (fun s=>b30 δ fin (s.1,s.2.1)) d (.goto fun _=>true)))
        .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin:Q→ Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
  K:=TrK
  k₀:=.inp
  k₁:=.out
  Γ:=TrΓ Γ₀ Γ₁ Q
  Λ:=Bool
  main:=false
  σ:=TrS Γ₀ Q
  initialState:=(q₀,none,false)
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=o4 δ fin q₀ d
def j7 (l:List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
  | .inp=>l
  | .tmp=>t
  | .out=>u
lemma d40 (l l':List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    Function.update (j7 l t u) .inp l'=j7 l' t u:=by
  funext k;cases k <;> simp [j7]
lemma d19 (l:List Γ₀) (t t':List (Q × Option Γ₀)) (u:List Γ₁) :
    Function.update (j7 l t u) .tmp t'=j7 l t' u:=by
  funext k;cases k <;> simp [j7]
lemma d78 (l:List Γ₀) (t:List (Q × Option Γ₀)) (u u':List Γ₁) :
    Function.update (j7 l t u) .out u'=j7 l t u':=by
  funext k;cases k <;> simp [j7]
lemma d87 (l:List Γ₀) :
    (j7 l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:=by
  funext k;cases k <;> simp [j7]
lemma c2x (u:List Γ₁) :
    (j7 [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:=by
  funext k;cases k <;> simp [j7]
abbrev a0b (Γ₀ Γ₁ Q:Type):Type:=TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
lemma d25 (o:TrS Γ₀ Q→ Option Γ₁) (d:Option Γ₁) (hd:∀ _:Γ₁,d≠none)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.stepAux (d65 o d next) s (j7 l t u) =
      TM2.stepAux next s (j7 l t ((o s).toList++u)):=by
  cases ho:o s with
  | none=>cases d <;> simp [d65,TM2.stepAux,ho]
  | some y =>
    cases d with
    | none=>exact absurd rfl (hd y)
    | some dd=>simp [d65,TM2.stepAux,ho,j7,d78]
variable (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) (q₀:Q)
  (d:Option Γ₁)
lemma c2u (s:TrS Γ₀ Q) (a:Γ₀) (l:List Γ₀) (t:List (Q × Option Γ₀))
    (u:List Γ₁) :
    TM2.step (o4 δ fin q₀ d) (⟨some false,s,j7 (a::l) t u⟩:a0b Γ₀ Γ₁ Q) =
      some ⟨some false,((δ s.1 a).1,none,false),j7 l ((s.1,some a)::t) u⟩:=by
  simp [TM2.step,o4,TM2.stepAux,j7,d40,d19]
lemma c1x (s:TrS Γ₀ Q) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.step (o4 δ fin q₀ d) (⟨some false,s,j7 [] t u⟩:a0b Γ₀ Γ₁ Q) =
      some ⟨some true,(q₀,none,false),j7 [] ((s.1,none)::t) u⟩:=by
  simp [TM2.step,o4,TM2.stepAux,j7,d40,d19]
lemma c1z (hd:∀ _:Γ₁,d≠none) (s:TrS Γ₀ Q) (e:Q × Option Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.step (o4 δ fin q₀ d) (⟨some true,s,j7 [] (e::t) u⟩:a0b Γ₀ Γ₁ Q) =
      some ⟨some true,(e.1,e.2,true),j7 [] t (a3j δ fin e++u)⟩:=by
  simp only [TM2.step,o4,TM2.stepAux]
  have e1:(j7 [] (e::t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e::t:=rfl
  rw [e1]
  simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
  rw [d19,d25 _ _ hd,d25 _ _ hd]
  simp [TM2.stepAux,a3j]
lemma c1e (s:TrS Γ₀ Q) (u:List Γ₁) :
    TM2.step (o4 δ fin q₀ d) (⟨some true,s,j7 [] [] u⟩:a0b Γ₀ Γ₁ Q) =
      some ⟨none,(q₀,none,false),j7 [] [] u⟩:=by
  simp [TM2.step,o4,TM2.stepAux,j7,d19]
lemma c28 (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Q × Option Γ₀)) (s:TrS Γ₀ Q),
      (flip bind (TM2.step (o4 δ fin q₀ d)))^[l.length+1]
          (some (⟨some false,s,j7 l t u⟩:a0b Γ₀ Γ₁ Q)) =
        some ⟨some true,(q₀,none,false),j7 [] ((d21 δ s.1 l).reverse++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t s;exact c1x δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (o4 δ fin q₀ d))
        (some (⟨some false,s,j7 (a::l) t u⟩:a0b Γ₀ Γ₁ Q)) =
        some ⟨some false,((δ s.1 a).1,none,false),j7 l ((s.1,some a)::t) u⟩ :=
      c2u δ fin q₀ d s a l t u
    rw [e,ih]
    simp [d21]
lemma c12 (hd:∀ _:Γ₁,d≠none) :
    ∀ (t:List (Q × Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
      (flip bind (TM2.step (o4 δ fin q₀ d)))^[t.length+1]
          (some (⟨some true,s,j7 [] t u⟩:a0b Γ₀ Γ₁ Q)) =
        some ⟨none,(q₀,none,false),j7 [] [] (t.reverse.flatMap (a3j δ fin)++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u s;exact c1e δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e':flip bind (TM2.step (o4 δ fin q₀ d))
        (some (⟨some true,s,j7 [] (e::t) u⟩:a0b Γ₀ Γ₁ Q)) =
        some ⟨some true,(e.1,e.2,true),j7 [] t (a3j δ fin e++u)⟩ :=
      c1z δ fin q₀ d hd s e t u
    rw [e',ih]
    simp [List.flatMap_append]
lemma c0y [Fintype Γ₀] [Fintype Q] (hd:∀ _:Γ₁,d≠none) (l:List Γ₀) :
    (flip bind (TM2.step (o4 δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (p6 δ fin q₀ l)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (o4 δ fin q₀ d)))^[l.length+1+1 +
    (l.length+1)] (some c)) (i7 (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (i9 (trM δ fin q₀ d) (p6 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (o4 δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
    (some (⟨some false,(q₀,none,false),Function.update (fun _=>[]) .inp l⟩ :
      a0b Γ₀ Γ₁ Q)) =
    some (⟨none,(q₀,none,false),Function.update (fun _=>[]) .out (p6 δ fin q₀ l)⟩ :
      a0b Γ₀ Γ₁ Q)
  have hA:(flip bind (TM2.step (o4 δ fin q₀ d)))^[l.length+1]
      (some (⟨some false,(q₀,none,false),j7 l [] []⟩:a0b Γ₀ Γ₁ Q)) =
      some ⟨some true,(q₀,none,false),j7 [] (d21 δ q₀ l).reverse []⟩:=by
    have:=c28 δ fin q₀ d [] l [] (q₀,none,false)
    rw [List.append_nil] at this
    exact this
  have hB:(flip bind (TM2.step (o4 δ fin q₀ d)))^[l.length+1+1]
      (some (⟨some true,(q₀,none,false),j7 [] (d21 δ q₀ l).reverse []⟩ :
        a0b Γ₀ Γ₁ Q)) =
      some ⟨none,(q₀,none,false),j7 [] [] (p6 δ fin q₀ l)⟩:=by
    have:=c12 δ fin q₀ d hd (d21 δ q₀ l).reverse [] (q₀,none,false)
    rw [List.length_reverse,d57,List.reverse_reverse,d85,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply,← d87,hA,hB,c2x]
lemma a42 {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (δ:Q→ αΓ→ Q × Option βΓ × Option βΓ)
    (fin:Q→ Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=p6 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ _:βΓ,d≠none:=by
    intro y
    have hn:Nonempty βΓ:=⟨y⟩
    simp [d,hn]
  exact ⟨{
    tm:=trM δ fin q₀ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2* Polynomial.X+Polynomial.C 3
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=c0y δ fin q₀ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (o4 δ fin q₀ d)))^[(ea a).length +
            1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
lemma g0 {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (δ:Q→ αΓ→ Q × Option βΓ) (fin:Q→ Option βΓ) (q₀:Q)
    (h:∀ a,eb (f a)=c7 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  a42 ea eb f (fun q a=>((δ q a).1,(δ q a).2,none)) fin q₀
    (fun a=>(h a).trans (d36 δ fin q₀ (ea a)))
end Lib.Machines
end
section
namespace Lib.Machines.Rev
open Turing PEqualNP.Library Lib.Machines
def m3:Unit→ TM2.Stmt (fun _:Bool=>Bool) Unit (Option Bool)
  | () =>
    .pop false (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push true (fun s=>s.getD false) (.load (fun _=>none) (.goto fun _=>())))
        .halt)
def tm:FinTM2 where
  K:=Bool
  k₀:=false
  k₁:=true
  Γ _:=Bool
  Λ:=Unit
  main:=()
  σ:=Option Bool
  initialState:=none
  m:=m3
abbrev a7o:Type:=TM2.Cfg (fun _:Bool=>Bool) Unit (Option Bool)
def st (l u:List Bool):Bool→ List Bool:=fun k=>cond k u l
lemma d79 (l:List Bool) :
    st l []=Function.update (fun _=>([]:List Bool)) false l:=by
  funext k;cases k <;> simp [st]
lemma a9g (u:List Bool) :
    st [] u=Function.update (fun _=>([]:List Bool)) true u:=by
  funext k;cases k <;> simp [st]
lemma c2b (x:Bool) (l u:List Bool) :
    TM2.step m3 (⟨some (),none,st (x::l) u⟩:a7o) =
      some ⟨some (),none,st l (x::u)⟩:=by
  simp only [TM2.step,m3,TM2.stepAux]
  simp only [st,Bool.cond_false,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,
    Option.getD_some,Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
  funext k;cases k <;> simp [st]
lemma c2v (u:List Bool) :
    TM2.step m3 (⟨some (),none,st [] u⟩:a7o)=some ⟨none,none,st [] u⟩:=by
  simp only [TM2.step,m3,TM2.stepAux]
  simp only [st,Bool.cond_false,List.head?_nil,List.tail_nil,Option.isSome_none,
    Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
  funext k;cases k <;> simp [st]
lemma c2c:∀ (l u:List Bool),
    (flip bind (TM2.step m3))^[l.length+1] (some (⟨some (),none,st l u⟩:a7o)) =
      some ⟨none,none,st [] (l.reverse++u)⟩:=by
  intro l
  induction l with
  | nil=>intro u;exact c2v u
  | cons x l ih =>
    intro u
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step m3) (some (⟨some (),none,st (x::l) u⟩:a7o)) =
        some ⟨some (),none,st l (x::u)⟩:=c2b x l u
    rw [e,ih]
    simp
lemma run (l:List Bool) :
    (flip bind (TM2.step m3))^[l.length+1] (some (initList tm l)) =
      some (haltList tm l.reverse):=by
  refine (congrArg (fun c=>(flip bind (TM2.step m3))^[l.length+1] (some c))
    (i7 tm l)).trans (Eq.trans ?_ (congrArg some (i9 tm l.reverse)).symm)
  show (flip bind (TM2.step m3))^[l.length+1]
    (some (⟨some (),none,Function.update (fun _=>[]) false l⟩:a7o)) =
    some (⟨none,none,Function.update (fun _=>[]) true l.reverse⟩:a7o)
  rw [← d79,c2c,← a9g]
  simp
noncomputable def a5e :
    TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x)
      (fun x:List Bool=>x.reverse) where
  tm:=tm
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.X+1
  outputsFun a :=
    { steps:=a.length+1
      evals_in_steps:=by
        have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
        exact (congrArg (fun l=>(flip bind (TM2.step m3))^[a.length+1]
          (some (initList tm l))) (hm a)).trans
          ((run a).trans (congrArg (fun l=>some (haltList tm l)) (hm a.reverse).symm))
      steps_le_m:=by simp }
end Lib.Machines.Rev
end
section
namespace Lib.Universal
def un (n:ℕ):List Bool:=List.replicate n true
def a1 (a b:List Bool):List Bool:=un a.length++false::(a++b)
def a0 (s:List Bool):List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)
lemma a5 (a b:List Bool):a0 (a1 a b)=(a,b):=by
  have h1:(a1 a b).takeWhile id=un a.length:=by
    simp [a1,un]
  have h2:(a1 a b).dropWhile id=false::(a++b):=by
    simp [a1,un]
  simp [a0,h1,h2,un]
end Lib.Universal
end
section
namespace Lib.Universal
@[simp] lemma b6j:un 0=[]:=rfl
@[simp] lemma b4 (n:ℕ):(un n).length=n:=List.length_replicate
lemma a1w (n:ℕ):un (n+1)=true::un n:=rfl
def hd (s:List Bool):List Bool:=s.takeWhile id
def r5 (s:List Bool):List Bool:=(s.dropWhile id).tail
def sel (f a b:List Bool):List Bool:=if f=[] then a else b
def j0 (u v:List Bool):List Bool:=un (u.length* v.length)
def f3 (s:List Bool):List Bool:=s.map fun _=>false
lemma b3h (s:List Bool):(hd s).length≤ s.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix id)
lemma a9z (s:List Bool):(r5 s).length≤ s.length:=by
  have h1:=List.IsSuffix.length_le (List.dropWhile_suffix (p:=id) (l:=s))
  simp only [r5,List.length_tail]
  omega
lemma n7 (s:List Bool) :
    2* (a0 s).1.length+(a0 s).2.length≤ s.length:=by
  have h:=congrArg List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s))
  simp only [List.length_append] at h
  simp only [a0,List.length_take,List.length_drop,List.length_tail]
  omega
lemma a02 (a b:List Bool):(a1 a b).length=2* a.length+b.length+1:=by
  simp [a1];omega
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private lemma d39 {α β αΓ βΓ:Type} {ea:α→ List αΓ} {eb:β→ List βΓ}
    {f f':α→ β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':=by
  obtain rfl:f=f':=funext e
  exact h
private lemma c01 {A B C:Type} (φl:A→ Option C) (φr:B→ Option C) (x:List A)
    (w:List B) :
    (x.map Sum.inl++w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl++w.filterMap φr:=by
  have h1:∀ x:List A,(x.map Sum.inl).filterMap (Sum.elim φl φr)=x.filterMap φl:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>simp [List.filterMap_cons,ih]
  have h2:∀ w:List B,(w.map Sum.inr).filterMap (Sum.elim φl φr)=w.filterMap φr:=by
    intro w;induction w with
    | nil=>rfl
    | cons a l ih=>simp [List.filterMap_cons,ih]
  rw [List.filterMap_append,h1,h2]
private lemma b5v {A C:Type} (g:A→ C) (l:List A) :
    l.filterMap (fun a=>some (g a))=l.map g:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [ih]
private lemma c2i {A C:Type} (l:List A) :
    l.filterMap (fun _:A=>(none:Option C))=[]:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp
lemma b4c :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>a1 p.1 p.2):=by
  have hA:ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(p.1,p.1++p.2)):=by
    refine w4 _ _ _
      (Sum.elim (fun b:Bool=>some (Sum.inl b)) (fun _:Bool=>none))
      (Sum.elim (fun b:Bool=>some (Sum.inr b)) (fun b:Bool=>some (Sum.inr b))) ?_
    rintro ⟨x,w⟩
    simp only [encodePair]
    rw [c01,c01,b5v,b5v,b5v,c2i]
    simp
  have hU:Lib.a4
      (fun a:List Bool=>a.map (fun _=>true)++[false]):=by
    refine g0 _ _ _ (fun (_:Unit) (_:Bool)=>((),some true))
      (fun _=>some false) () ?_
    intro a
    induction a with
    | nil=>rfl
    | cons b l ih =>
      simp only [c7,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢
      rw [← ih];rfl
  refine d39 (a2 (a2 hA (a2p hU)) a7c) ?_
  rintro ⟨x,w⟩
  simp [a1,un]
lemma a2v :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>if p.1=[] then p.2 else []):=by
  obtain ⟨c⟩:=a01 []
  have hI:=Iter.a1g (fun _:List Bool=>([]:List Bool)) c 0 (by simp)
  refine d39 (a2 a69 hI) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil=>simp
  | cons b l=>simp [Function.iterate_succ_apply']
lemma a7s :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>if p.1=[] then [] else p.2):=by
  have hneg:Lib.a4
      (fun x:List Bool=>if x=[] then [true] else []) :=
    a2 (x7 g5 (a01 [true])) a2v
  refine d39 (a2 (a2p hneg) a2v) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil=>simp
  | cons b l=>simp
private def a0w (u:List Bool):List Bool:=u.flatMap (fun b=>[true,b])
private def v3 (v:List Bool):List Bool:=v.flatMap (fun b=>[false,b])
private def twD:Bool→ Bool→ Bool × Option Bool
  | true,true=>(true,some true)
  | _,_=>(false,none)
private lemma c2k (l:List Bool) :
    c7 twD (fun _=>none) false l=[] ∧
      c7 twD (fun _=>none) true l=l.takeWhile id:=by
  induction l with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b l ih=>cases b <;> simp [c7,twD,ih.1,ih.2]
private def e0D:Bool→ Bool→ Bool × Option Bool × Option Bool
  | false,true=>(false,none,none)
  | false,false=>(true,none,none)
  | true,b=>(true,some false,some b)
private lemma d83 (l:List Bool) :
    p6 e0D (fun _=>none) true l=v3 l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [p6,e0D,v3,ih]
private lemma d73 (l:List Bool) :
    p6 e0D (fun _=>none) false l=v3 (l.dropWhile id).tail:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>cases b <;> simp [p6,e0D,ih,d83]
private def mkD:Bool × Bool→ Bool→ (Bool × Bool) × Option Bool
  | (d,false),t=>((d || !t,true),some (t || !d))
  | (d,true),b=>((d,false),some b)
private def mk (l:List Bool):List Bool:=c7 mkD (fun _=>none) (false,false) l
private lemma d91 (q:Bool × Bool) (l:List Bool) :
    (c7 mkD (fun _=>none) q l).length=l.length:=by
  induction l generalizing q with
  | nil=>rfl
  | cons b l ih=>obtain ⟨d,ph⟩:=q;cases ph <;> simp [c7,mkD,ih]
private lemma c18 (v:List Bool) :
    c7 mkD (fun _=>none) (true,false) (v3 v)=v3 v:=by
  induction v with
  | nil=>rfl
  | cons b v ih=>simp [c7,mkD,v3] at ih ⊢;exact ih
private lemma d69 (u r:List Bool) :
    c7 mkD (fun _=>none) (false,false) (a0w u++r) =
      a0w u++c7 mkD (fun _=>none) (false,false) r:=by
  induction u with
  | nil=>rfl
  | cons b u ih=>simp [c7,mkD,a0w] at ih ⊢;exact ih
private lemma b8o (u:List Bool):mk (a0w u++v3 [])=a0w u++v3 []:=by
  unfold mk;rw [d69];rfl
private lemma c1t (u:List Bool) (b:Bool) (v:List Bool) :
    mk (a0w u++v3 (b::v))=a0w (u++[b])++v3 v:=by
  unfold mk
  rw [d69]
  have h:c7 mkD (fun _=>none) (false,false) (v3 (b::v)) =
      true::b::v3 v:=by
    have h':=c18 v
    simp [c7,mkD,v3] at h' ⊢
    exact h'
  rw [h]
  simp [a0w]
private lemma c0v (k:ℕ):∀ u t:List Bool,
    mk^[k] (a0w u++v3 t)=a0w (u++t.take k)++v3 (t.drop k):=by
  induction k with
  | zero=>intro u t;simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil=>rw [b8o,ih];simp
    | cons b t=>rw [c1t,ih];simp
private def dcD:Option Bool→ Bool→ Option Bool × Option (Bool ⊕ Bool)
  | none,t=>(some t,none)
  | some t,b=>(none,some (if t then Sum.inl b else Sum.inr b))
private lemma c0g (v:List Bool) :
    c7 dcD (fun _=>none) none (v3 v)=v.map Sum.inr:=by
  induction v with
  | nil=>rfl
  | cons b v ih=>simp [c7,dcD,v3] at ih ⊢;exact ih
private lemma c0d (u r:List Bool) :
    c7 dcD (fun _=>none) none (a0w u++r) =
      u.map Sum.inl++c7 dcD (fun _=>none) none r:=by
  induction u with
  | nil=>rfl
  | cons b u ih=>simp [c7,dcD,a0w] at ih ⊢;exact ih
private def a72 (l:List (Bool ⊕ Bool)):List Bool × List Bool :=
  (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private lemma d68 (u v:List Bool) :
    a72 (u.map Sum.inl++v.map Sum.inr)=(u,v):=by
  have h1:∀ x:List Bool,(x.map (Sum.inl (β:=Bool))).filterMap Sum.getLeft?= x:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact congrArg (a::·) ih
  have h2:∀ x:List Bool,(x.map (Sum.inr (α:=Bool))).filterMap Sum.getLeft?= []:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact ih
  have h3:∀ x:List Bool,(x.map (Sum.inl (β:=Bool))).filterMap Sum.getRight?= []:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact ih
  have h4:∀ x:List Bool,(x.map (Sum.inr (α:=Bool))).filterMap Sum.getRight?= x:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact congrArg (a::·) ih
  simp only [a72,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
lemma a5p :
    ComputableInPolyTime (fun x:List Bool=>x) encodePair a0:=by
  have hTw:Lib.a4
      (fun s:List Bool=>s.takeWhile id) :=
    g0 _ _ _ twD (fun _=>none) true (fun s=>(c2k s).2.symm)
  have hE0:Lib.a4
      (fun s:List Bool=>v3 (s.dropWhile id).tail) :=
    a42 _ _ _ e0D (fun _=>none) false (fun s=>(d73 s).symm)
  have hMk:Lib.a4 mk :=
    g0 _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl)
  obtain ⟨cMk⟩:=hMk
  have hIt:=Iter.a1g mk cMk 0 (fun y=>by simp [mk,d91])
  have hDc:ComputableInPolyTime (fun x:List Bool=>x) (fun l:List (Bool ⊕ Bool)=>l)
      (fun l:List Bool=>c7 dcD (fun _=>none) none l) :=
    g0 _ _ _ dcD (fun _=>none) none (fun _=>rfl)
  have hRaw:ComputableInPolyTime (fun l:List (Bool ⊕ Bool)=>l) encodePair a72:=by
    refine w4 _ _ _
      (fun s:Bool ⊕ Bool=>(Sum.getLeft? s).map Sum.inl)
      (fun s:Bool ⊕ Bool=>(Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [a72,encodePair,List.map_filterMap]
  refine d39 (a2 (a2 (a2 (x7 hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h:=c0v (s.takeWhile id).length [] (s.dropWhile id).tail
  have e:a0w []++v3 (s.dropWhile id).tail=v3 (s.dropWhile id).tail:=rfl
  rw [e] at h
  simp only [h,List.nil_append]
  rw [c0d,c0g,d68]
  rfl
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private lemma a9k {α β αΓ βΓ:Type} {ea:α→ List αΓ} {eb:β→ List βΓ}
    {f f':α→ β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':=by
  obtain rfl:f=f':=funext e
  exact h
private def hdD:Bool→ Bool→ Bool × Option Bool
  | true,true=>(true,some true)
  | _,_=>(false,none)
private lemma c2q (l:List Bool) :
    c7 hdD (fun _=>none) false l=[] ∧
      c7 hdD (fun _=>none) true l=l.takeWhile id:=by
  induction l with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b l ih=>cases b <;> simp [c7,hdD,ih.1,ih.2]
lemma a2d :
    Lib.a4 hd :=
  g0 _ _ _ hdD (fun _=>none) true (fun s=>(c2q s).2.symm)
private def dnD:Bool→ Bool→ Bool × Option Bool
  | false,true=>(false,none)
  | false,false=>(true,none)
  | true,b=>(true,some b)
private lemma c1q (l:List Bool):c7 dnD (fun _=>none) true l=l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [c7,dnD,ih]
private lemma c1j (l:List Bool) :
    c7 dnD (fun _=>none) false l=(l.dropWhile id).tail:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>cases b <;> simp [c7,dnD,ih,c1q]
lemma z8 :
    Lib.a4 r5 :=
  g0 _ _ _ dnD (fun _=>none) false (fun s=>(c1j s).symm)
private def tlD:Bool→ Bool→ Bool × Option Bool
  | false,_=>(true,none)
  | true,b=>(true,some b)
private lemma c0s (l:List Bool):c7 tlD (fun _=>none) true l=l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [c7,tlD,ih]
private lemma c10 (l:List Bool):c7 tlD (fun _=>none) false l=l.tail:=by
  cases l with
  | nil=>rfl
  | cons b l=>simp [c7,tlD,c0s]
lemma o3 :
    Lib.a4
      (fun s:List Bool=>s.tail) :=
  g0 _ _ _ tlD (fun _=>none) false (fun s=>(c10 s).symm)
private lemma c1n (l:List Bool) :
    c7 (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) () l=f3 l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [c7,f3] at ih ⊢;exact ih
lemma n6 :
    Lib.a4 f3 :=
  g0 _ _ _ (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) ()
    (fun s=>(c1n s).symm)
lemma b0 (l:List Bool) :
    Lib.a4
      (fun _:List Bool=>l) :=
  a01 l
lemma a6 :
    Lib.a4
      (fun s:List Bool=>(a0 s).1) :=
  a9k (a2 a5p b6z) (fun _=>rfl)
lemma a3 :
    Lib.a4
      (fun s:List Bool=>(a0 s).2) :=
  a9k (a2 a5p b75) (fun _=>rfl)
lemma b8 {u v:List Bool→ List Bool}
    (hu:Lib.a4 u)
    (hv:Lib.a4 v) :
    Lib.a4
      (fun s=>u s++v s) :=
  a9k (a2 (x7 hu hv) a7c) (fun _=>rfl)
lemma a7 {u v:List Bool→ List Bool}
    (hu:Lib.a4 u)
    (hv:Lib.a4 v) :
    Lib.a4
      (fun s=>a1 (u s) (v s)) :=
  a9k (a2 (x7 hu hv) b4c) (fun _=>rfl)
lemma d6 {f a b:List Bool→ List Bool}
    (hf:Lib.a4 f)
    (ha:Lib.a4 a)
    (hb:Lib.a4 b) :
    Lib.a4
      (fun s=>sel (f s) (a s) (b s)):=by
  have h1:=a2 (x7 hf ha) a2v
  have h2:=a2 (x7 hf hb) a7s
  refine a9k (b8 h1 h2) ?_
  intro s
  by_cases h:f s=[] <;> simp [sel,h]
end Lib.Universal
end
noncomputable section
open Classical
open PEqualNP.Library Lib.Machines Lib.Universal Lib.Machines.Rev
abbrev a4 (f:List Bool→ List Bool):Prop :=
  ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
lemma b7 {f g:List Bool→ List Bool} (hf:a4 f) (h:∀ x,f x=g x):a4 g:=by
  have:f=g:=funext h
  rwa [← this]
lemma b7c:a4 (fun s:List Bool=>s.reverse):=⟨Rev.a5e⟩
lemma v4 {g cnt arg:List Bool→ List Bool} (k:ℕ)
    (hg:a4 g) (hgl:∀ s,(g s).length≤ s.length+k)
    (hcnt:a4 cnt) (harg:a4 arg) :
    a4 (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.a1g g c k hgl
  exact b7 (a2 (x7 harg hcnt) hI) (fun _=>rfl)
lemma a2i {g cnt arg:List Bool→ List Bool}
    (m:List Bool→ ℕ) (a:ℕ)
    (hg:a4 g)
    (hm:∀ y,m (g y)≤ m y)
    (hgl:∀ y,(g y).length≤ y.length+m y)
    (ha:∀ y,m y≤ a* y.length+a)
    (hcnt:a4 cnt) (harg:a4 arg) :
    a4 (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.a0g g c m a hm hgl ha
  exact b7 (a2 (x7 harg hcnt) hI) (fun _=>rfl)
lemma p0 (a b:List Bool):(a1 a b).length=2* a.length+b.length+1:=by
  simp [a1,un];omega
lemma m7 (y:List Bool) :
    2* (a0 y).1.length+(a0 y).2.length≤ y.length:=by
  dsimp only [a0]
  have hsplit:y=y.takeWhile id++y.dropWhile id:=(List.takeWhile_append_dropWhile (p:=id) (l:=y)).symm
  have hylen:y.length=(y.takeWhile id).length+(y.dropWhile id).length:=by
    conv_lhs=>rw [hsplit]
    exact List.length_append
  set a:=(y.takeWhile id).length
  set t:=(y.dropWhile id).tail
  have htlen:t.length≤ (y.dropWhile id).length:=by
    dsimp only [t];cases y.dropWhile id <;> simp
  have htake:(t.take a).length=min a t.length:=List.length_take
  have hdrop:(t.drop a).length=t.length - a:=List.length_drop
  omega
lemma a5k {g cnt arg:List Bool→ List Bool} (c:ℕ)
    (hg:a4 g)
    (hw:∀ y,(a0 (g y)).1=(a0 y).1)
    (hgl:∀ y,(g y).length≤ y.length+c* (a0 y).1.length+c)
    (hcnt:a4 cnt) (harg:a4 arg) :
    a4 (fun s=>g^[(cnt s).length] (arg s)):=by
  refine a2i (fun y=>c* (a0 y).1.length+c) c hg
    (fun y=>by rw [hw y])
    (fun y=>by have:=hgl y;omega)
    (fun y=>by
      have h1:(a0 y).1.length≤ y.length:=by have:=m7 y;omega
      have h2:=Nat.mul_le_mul_left c h1
      omega)
    hcnt harg
def unL (s:List Bool):List Bool:=List.replicate s.length true
lemma a78 (s:List Bool):(unL s).length=s.length:=List.length_replicate
lemma a1u:a4 unL :=
  g0 _ _ _ (fun (_:Unit) (_:Bool)=>((),some true)) (fun _=>none) () (fun s=>by
    induction s with
    | nil=>rfl
    | cons b l ih=>simp only [c7,unL,List.length_cons,List.replicate_succ];exact congrArg (true::·) ih)
def q79 (s:List Bool):List Bool :=
  a1 (a0 s).1 ((a0 s).2++(a0 s).1)
lemma c2h:a4 q79 :=
  a7 a6 (b8 a3 a6)
lemma q99 (a:List Bool):∀ k b,q79^[k] (a1 (unL a) b)=a1 (unL a) (b++un (k* a.length))
  | 0,b=>by simp [un]
  | k+1,b=>by
    rw [Function.iterate_succ_apply,q79,a5,q99 a k (b++unL a)]
    congr 1
    simp [unL,un,List.append_assoc,← List.replicate_add,Nat.succ_mul,Nat.add_comm]
lemma g9 {u v:List Bool→ List Bool} (hu:a4 u) (hv:a4 v) :
    a4 (fun s=>j0 (u s) (v s)):=by
  have h1:a4 (fun s=>q79^[(u s).length] (a1 (unL (v s)) [])) :=
    a5k 1 c2h (fun y=>by rw [q79,a5])
      (fun y=>by
        rw [q79,p0,List.length_append]
        have:=m7 y
        omega)
      hu (a7 (a2 hv a1u) (b0 []))
  have h2:=a2 h1 a3
  have heq:(fun s=>(a0 (q79^[(u s).length] (a1 (unL (v s)) []))).2)=(fun s=>j0 (u s) (v s)):=by
    funext s
    rw [q99,a5,List.nil_append];rfl
  rwa [heq] at h2
def j3 (s:List Bool):List Bool :=
  match s with
  | true::_=>[true]
  | _=>[]
lemma m6:a4 j3 :=
  g0 _ _ _
    (fun (st:Bool) (b:Bool)=>if st then (false,if b then some true else none) else (false,none))
    (fun _=>none) true (fun s=>by
      have hfalse:∀ l,c7 (fun (st:Bool) (b:Bool) =>
          if st then (false,if b then some true else none) else (false,none))
          (fun _=>none) false l=[]:=by
        intro l;induction l with | nil=>rfl | cons b l ih=>simp [c7,ih]
      cases s with
      | nil=>rfl
      | cons b l=>cases b <;> simp [c7,j3,hfalse])
def m4 (lenU xs:List Bool):List Bool :=
  (a0 (unL lenU++false::xs)).1
def g8 (lenU xs:List Bool):List Bool :=
  (a0 (unL lenU++false::xs)).2
lemma k7 (lenU xs:List Bool):m4 lenU xs=xs.take lenU.length:=by
  have h1:(unL lenU++false::xs).takeWhile id=unL lenU:=by
    simp [unL]
  have h2:(unL lenU++false::xs).dropWhile id=false::xs:=by
    simp [unL]
  simp [m4,a0,h1,h2,a78]
lemma i6 (lenU xs:List Bool):g8 lenU xs=xs.drop lenU.length:=by
  have h1:(unL lenU++false::xs).takeWhile id=unL lenU:=by
    simp [unL]
  have h2:(unL lenU++false::xs).dropWhile id=false::xs:=by
    simp [unL]
  simp [g8,a0,h1,h2,a78]
lemma k4 {u v:List Bool→ List Bool} (hu:a4 u) (hv:a4 v) :
    a4 (fun s=>m4 (u s) (v s)) :=
  b7 (a2 (b8 (a2 hu a1u) (b8 (b0 [false]) hv)) a6) (fun _=>rfl)
lemma e8 {u v:List Bool→ List Bool} (hu:a4 u) (hv:a4 v) :
    a4 (fun s=>g8 (u s) (v s)) :=
  b7 (a2 (b8 (a2 hu a1u) (b8 (b0 [false]) hv)) a3) (fun _=>rfl)
def val:List Bool→ ℕ
  | []=>0
  | b::l=>b.toNat+2* val l
lemma a4i (l:List Bool):val l< 2 ^ l.length:=by
  induction l with
  | nil=>simp [val]
  | cons b l ih =>
    simp only [val,List.length_cons,pow_succ]
    cases b <;> simp <;> omega
lemma a73 (a b:List Bool):val (a++b)=val a+2 ^ a.length* val b:=by
  induction a with
  | nil=>simp [val]
  | cons x l ih =>
    simp only [List.cons_append,val,List.length_cons,pow_succ,ih]
    ring
lemma a74 (k:ℕ):val (List.replicate k false)=0:=by
  induction k with
  | zero=>rfl
  | succ k ih=>simp [List.replicate_succ,val,ih]
lemma w1 (l:List Bool):val (f3 l)=0:=by
  have h:f3 l=List.replicate l.length false:=by
    induction l with
    | nil=>rfl
    | cons _ r ih=>simp [f3,List.replicate_succ,ih]
  rw [h,a74]
lemma q7 (l:List Bool):(f3 l).length=l.length:=by
  induction l with
  | nil=>rfl
  | cons _ r ih=>simp [f3,ih]
lemma a9v (k:ℕ) (l:List Bool):val (l.take k)=val l % 2 ^ k:=by
  induction k generalizing l with
  | zero=>simp [val,Nat.mod_one]
  | succ k ih =>
    cases l with
    | nil=>simp [val]
    | cons b r =>
      simp only [List.take_succ_cons,val,ih,pow_succ']
      have hlt:b.toNat< 2:=by cases b <;> decide
      have hdiv:(b.toNat+2* val r) % (2* 2 ^ k)=b.toNat+2* (val r % 2 ^ k):=by
        have h1:=Nat.div_add_mod (val r) (2 ^ k)
        have h2:val r % 2 ^ k< 2 ^ k:=Nat.mod_lt _ (by positivity)
        have h3:b.toNat+2* val r=(2* 2 ^ k)* (val r / 2 ^ k)+(b.toNat+2* (val r % 2 ^ k)):=by
          linarith
        rw [h3,Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
      exact hdiv.symm
lemma b5u (n:ℕ):val n.bits=n:=by
  induction n using Nat.binaryRec with
  | zero=>simp [val]
  | bit b m ih =>
    by_cases h:b=false∧m=0
    · rcases h with ⟨rfl,rfl⟩;simp [val]
    · rw [Nat.bits_append_bit m b (fun hm=>by subst hm;cases b <;> simp_all)]
      simp only [val,ih,Nat.bit]
      cases b <;> simp <;> omega
lemma k2 (k:ℕ) (hk:0< k):k.bits.length=k.log2+1:=by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases h2:k< 2
    · have hk1:k=1:=by omega
      subst hk1;decide
    · have hdiv_pos:0 < k / 2:=by omega
      have hdiv_lt:k / 2< k:=Nat.div_lt_self hk (by omega)
      have hlog:k.log2=(k / 2).log2+1:=by
        rw [Nat.log2_def];simp [show 2≤ k by omega]
      have hbits:k.bits=(decide (k % 2=1))::(k / 2).bits:=by
        have a0f:k=Nat.bit (decide (k % 2=1)) (k / 2):=by
          cases hmod:k % 2 with
          | zero=>simp [Nat.bit];omega
          | succ r =>
            have hr:r=0:=by omega
            subst hr;simp [Nat.bit];omega
        conv_lhs=>rw [a0f]
        rw [Nat.bits_append_bit (k / 2) (decide (k % 2=1)) (fun h0=>by omega)]
      rw [hbits,List.length_cons,ih (k / 2) hdiv_lt hdiv_pos,hlog]
lemma a4w (z h:ℕ):z.testBit h=z.bits.getD h false:=by
  induction h generalizing z with
  | zero =>
    by_cases hz:z=0
    · subst hz;simp
    · have a0f:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
        cases hmod:z % 2 with
        | zero=>simp [Nat.bit];omega
        | succ r =>
          have hr:r=0:=by omega
          subst hr;simp [Nat.bit];omega
      have hbits:z.bits=(decide (z % 2=1))::(z / 2).bits:=by
        conv_lhs=>rw [a0f]
        refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0=>?_
        have hmod1:z % 2=1:=by omega
        simp [hmod1]
      rw [hbits]
      simp [Nat.testBit_zero]
  | succ h ih =>
    by_cases hz:z=0
    · subst hz;simp
    · have a0f:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
        cases hmod:z % 2 with
        | zero=>simp [Nat.bit];omega
        | succ r =>
          have hr:r=0:=by omega
          subst hr;simp [Nat.bit];omega
      have hbits:z.bits=(decide (z % 2=1))::(z / 2).bits:=by
        conv_lhs=>rw [a0f]
        refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0=>?_
        have hmod1:z % 2=1:=by omega
        simp [hmod1]
      rw [hbits,List.getD_cons_succ,← ih (z / 2),Nat.testBit_succ]
def a1e:List Bool→ List Bool
  | []=>[true]
  | false::l=>true::l
  | true::l=>false::a1e l
lemma c25 (l:List Bool):(a1e l).length≤ l.length+1:=by
  induction l with
  | nil=>simp [a1e]
  | cons b l ih=>cases b <;> simp [a1e] <;> omega
lemma c2e (n:ℕ):a1e n.bits=(n+1).bits:=by
  induction n using Nat.binaryRec with
  | zero=>decide
  | bit b m ih =>
    cases b with
    | false =>
      by_cases hm:m=0
      · subst hm;decide
      · have h1:(Nat.bit false m).bits=false::m.bits :=
          Nat.bits_append_bit m false (fun h=>(hm h).elim)
        have h2:Nat.bit false m+1=Nat.bit true m:=by simp [Nat.bit]
        have h3:(Nat.bit true m).bits=true::m.bits :=
          Nat.bits_append_bit m true (fun _=>by simp)
        rw [h1,h2,h3,a1e]
    | true =>
      have h1:(Nat.bit true m).bits=true::m.bits :=
        Nat.bits_append_bit m true (fun _=>by simp)
      have h2:Nat.bit true m+1=Nat.bit false (m+1):=by simp [Nat.bit];omega
      have h3:(Nat.bit false (m+1)).bits=false::(m+1).bits :=
        Nat.bits_append_bit (m+1) false (fun h=>by omega)
      rw [h1,h2,h3,a1e,ih]
lemma c11:a4 a1e:=by
  let δ:Bool→ Bool→ Bool × Option Bool:=fun c b =>
    match c,b with
    | false,b=>(false,some b)
    | true,false=>(false,some true)
    | true,true=>(true,some false)
  let fin:Bool→ Option Bool:=fun c=>if c then some true else none
  refine g0 _ _ _ δ fin true fun s=>?_
  have hfalse:∀ l,c7 δ fin false l=l:=by
    intro l;induction l with | nil=>rfl | cons b r ih=>simp [c7,δ,fin,ih]
  have htrue:∀ l,c7 δ fin true l=a1e l:=by
    intro l
    induction l with
    | nil=>rfl
    | cons b r ih=>cases b <;> simp [c7,δ,fin,a1e,hfalse,ih]
  exact (htrue s).symm
def s5 (u:List Bool):List Bool:=a1e^[u.length] []
lemma w7 (u:List Bool):s5 u=u.length.bits:=by
  dsimp only [s5]
  have h:∀ k,a1e^[k] []=k.bits:=by
    intro k
    induction k with
    | zero=>rfl
    | succ k ih=>rw [Function.iterate_succ_apply',ih,c2e]
  exact h u.length
lemma n9:a4 s5 :=
  v4 1 c11 c25 g5 (b0 [])
def a37 (kU zU:List Bool):List Bool :=
  m4 (s5 kU) (s5 zU++f3 (s5 kU))
lemma a7b {uk uz:List Bool→ List Bool} (hk:a4 uk) (hz:a4 uz) :
    a4 (fun s=>a37 (uk s) (uz s)) :=
  k4 (a2 hk n9)
    (b8 (a2 hz n9) (a2 (a2 hk n9) n6))
lemma a8l (k z:ℕ) (hk:0< k) :
    a37 (un k) (un z)=(List.range (k.log2+1)).map (fun h=>z.testBit h):=by
  dsimp only [a37]
  rw [k7,w7,w7,b4,b4]
  have hlen:k.bits.length=k.log2+1:=k2 k hk
  apply List.ext_getElem
  · rw [List.length_take,List.length_append,q7,hlen,List.length_map,List.length_range]
    omega
  · intro h hh1 hh2
    rw [List.length_map,List.length_range] at hh2
    rw [List.getElem_take,List.getElem_map,List.getElem_range,a4w]
    by_cases hlt:h< z.bits.length
    · rw [List.getElem_append_left hlt,List.getD_eq_getElem _ _ hlt]
    · rw [List.getElem_append_right (by omega)]
      have hbl:∀ (l:List Bool) (i:ℕ) (hi:i< (f3 l).length),(f3 l)[i]=false:=by
        intro l
        induction l with
        | nil=>intro i hi;simp [f3] at hi
        | cons _ r ih =>
          intro i hi
          cases i with
          | zero=>rfl
          | succ i=>exact ih i (by simpa [f3] using hi)
      rw [hbl,List.getD_eq_default _ _ (by omega)]
def g4 (wU x:List Bool):List Bool:=m4 wU (x++f3 wU)
lemma i4 (wU x:List Bool):(g4 wU x).length=wU.length:=by
  dsimp only [g4]
  rw [k7,List.length_take,List.length_append,q7]
  omega
lemma w8 (wU x:List Bool):val (g4 wU x)=val x % 2 ^ wU.length:=by
  dsimp only [g4]
  rw [k7,a9v,a73,w1,mul_zero,add_zero]
lemma n4 {uw ux:List Bool→ List Bool} (hw:a4 uw) (hx:a4 ux) :
    a4 (fun s=>g4 (uw s) (ux s)) :=
  k4 hw (b8 hx (a2 hw n6))
def n3 (wU u:List Bool):List Bool:=g4 wU (s5 u)
lemma n8 (wU u:List Bool):(n3 wU u).length=wU.length:=i4 wU _
lemma a6k (wU u:List Bool):val (n3 wU u)=u.length % 2 ^ wU.length:=by
  dsimp only [n3];rw [w8,w7,b5u]
lemma a64 {uw uu:List Bool→ List Bool} (hw:a4 uw) (hu:a4 uu) :
    a4 (fun s=>n3 (uw s) (uu s)) :=
  n4 hw (a2 hu n9)
def v8 (x:List Bool):List Bool:=x.map (!·)
lemma b2a (x:List Bool):(v8 x).length=x.length:=by simp [v8]
lemma a0x:a4 v8 :=
  g0 _ _ _ (fun (_:Unit) (b:Bool)=>((),some (!b))) (fun _=>none) () fun s=>by
    induction s with
    | nil=>rfl
    | cons b l ih=>simp only [c7,v8,List.map_cons];exact congrArg ((!b)::·) ih
def a2k (wU x:List Bool):List Bool:=m4 wU (false::g4 wU x)
lemma b95 (wU x:List Bool):(a2k wU x).length=wU.length:=by
  dsimp only [a2k];rw [k7,List.length_take,List.length_cons,i4];omega
lemma c21 (wU x:List Bool):val (a2k wU x)=(2* val x) % 2 ^ wU.length:=by
  dsimp only [a2k]
  rw [k7,a9v,val,Bool.toNat_false,zero_add,w8,Nat.mul_mod_mod]
lemma c0z {uw ux:List Bool→ List Bool} (hw:a4 uw) (hx:a4 ux) :
    a4 (fun s=>a2k (uw s) (ux s)) :=
  k4 hw (b8 (b0 [false]) (n4 hw hx))
def q16 (f:List Bool):List Bool:=sel f [false] [true]
lemma q73 {uf:List Bool→ List Bool} (hf:a4 uf) :
    a4 (fun s=>q16 (uf s)) :=
  d6 hf (b0 [false]) (b0 [true])
def a4d (a b:List Bool):List Bool:=sel a (sel b [] [true]) (sel b [true] [])
def b26 (a b c:List Bool):List Bool :=
  sel a (sel b [] (sel c [] [true])) (sel b (sel c [] [true]) [true])
lemma b6e {ua ub:List Bool→ List Bool} (ha:a4 ua) (hb:a4 ub) :
    a4 (fun s=>a4d (ua s) (ub s)) :=
  d6 ha (d6 hb (b0 []) (b0 [true])) (d6 hb (b0 [true]) (b0 []))
lemma c1k {ua ub uc:List Bool→ List Bool} (ha:a4 ua) (hb:a4 ub) (hc:a4 uc) :
    a4 (fun s=>b26 (ua s) (ub s) (uc s)) :=
  d6 ha (d6 hb (b0 []) (d6 hc (b0 []) (b0 [true])))
    (d6 hb (d6 hc (b0 []) (b0 [true])) (b0 [true]))
def a6c (y:List Bool):List Bool :=
  let a:=(a0 y).1
  let r1:=(a0 y).2
  let b:=(a0 r1).1
  let r2:=(a0 r1).2
  let c:=(a0 r2).1
  let acc:=(a0 r2).2
  let ba:=j3 a
  let bb:=j3 b
  let bc:=j3 c
  let sBit:=q16 (a4d (a4d ba bb) bc)
  let c':=b26 ba bb bc
  a1 a.tail (a1 b.tail (a1 c' (sBit++acc)))
lemma c14 (y:List Bool):(a6c y).length≤ y.length+6:=by
  dsimp only [a6c]
  have h1:=m7 y
  have h2:=m7 (a0 y).2
  have h3:=m7 (a0 (a0 y).2).2
  rw [p0,p0,p0,List.length_append]
  have ha:(a0 y).1.tail.length≤ (a0 y).1.length:=by cases (a0 y).1 <;> simp
  have hb:(a0 (a0 y).2).1.tail.length≤ (a0 (a0 y).2).1.length:=by
    cases (a0 (a0 y).2).1 <;> simp
  have hs:(q16 (a4d (a4d (j3 (a0 y).1) (j3 (a0 (a0 y).2).1))
      (j3 (a0 (a0 (a0 y).2).2).1))).length=1:=by
    unfold q16 sel;split_ifs <;> rfl
  have hc:(b26 (j3 (a0 y).1) (j3 (a0 (a0 y).2).1)
      (j3 (a0 (a0 (a0 y).2).2).1)).length≤ 1:=by
    unfold b26 sel;split_ifs <;> simp
  omega
lemma c29:a4 a6c:=by
  have hA:a4 (fun y=>(a0 y).1):=a6
  have hR1:a4 (fun y=>(a0 y).2):=a3
  have hB:a4 (fun y=>(a0 (a0 y).2).1):=b7 (a2 hR1 a6) (fun _=>rfl)
  have hR2:a4 (fun y=>(a0 (a0 y).2).2):=b7 (a2 hR1 a3) (fun _=>rfl)
  have hC:a4 (fun y=>(a0 (a0 (a0 y).2).2).1):=b7 (a2 hR2 a6) (fun _=>rfl)
  have hAcc:a4 (fun y=>(a0 (a0 (a0 y).2).2).2):=b7 (a2 hR2 a3) (fun _=>rfl)
  have hba:=a2 hA m6
  have hbb:=a2 hB m6
  have hbc:=a2 hC m6
  have hs:=q73 (b6e (b6e hba hbb) hbc)
  have hc':=c1k hba hbb hbc
  exact b7 (a7 (a2 hA o3)
    (a7 (a2 hB o3) (a7 hc' (b8 hs hAcc)))) (fun _=>rfl)
def a08 (wU a b:List Bool):List Bool :=
  let fin:=a6c^[wU.length] (a1 (g4 wU a) (a1 (g4 wU b) (a1 [] [])))
  (a0 (a0 (a0 fin).2).2).2.reverse
lemma c2w (k:ℕ):∀ (a b:List Bool) (c:Bool) (acc:List Bool),
    a.length=k→ b.length=k →
    ∃ (acc':List Bool) (c':Bool),
      a6c^[k] (a1 a (a1 b (a1 (if c then [true] else []) acc))) =
        a1 [] (a1 [] (a1 (if c' then [true] else []) (acc'.reverse++acc))) ∧
      acc'.length=k ∧
      val acc'+2 ^ k* c'.toNat=val a+val b+c.toNat:=by
  induction k with
  | zero =>
    intro a b c acc ha hb
    cases a;cases b
    · exact ⟨[],c,by simp,rfl,by simp [val]⟩
    · simp at hb
    · simp at ha
  | succ k ih =>
    intro a b c acc ha hb
    cases a with
    | nil=>simp at ha
    | cons ba ar =>
      cases b with
      | nil=>simp at hb
      | cons bb br =>
        rw [Function.iterate_succ_apply]
        have hstep:a6c (a1 (ba::ar) (a1 (bb::br) (a1 (if c then [true] else []) acc))) =
            a1 ar (a1 br (a1 (if ((ba && bb) || (c && (ba || bb))) then [true] else [])
              (((xor (xor ba bb) c)::acc)))):=by
          dsimp only [a6c]
          simp only [a5,List.tail_cons]
          cases ba <;> cases bb <;> cases c <;> rfl
        rw [hstep]
        obtain ⟨acc',c',hiter,hlen,hval⟩:=ih ar br ((ba && bb) || (c && (ba || bb)))
          ((xor (xor ba bb) c)::acc) (by simpa using ha) (by simpa using hb)
        refine ⟨(xor (xor ba bb) c)::acc',c',?_,by simp [hlen],?_⟩
        · rw [hiter];simp
        · simp only [val,pow_succ']
          have hbit:(xor (xor ba bb) c).toNat+2* ((ba && bb) || (c && (ba || bb))).toNat =
              ba.toNat+bb.toNat+c.toNat:=by
            cases ba <;> cases bb <;> cases c <;> decide
          linarith
lemma a8r (wU a b:List Bool) :
    (a08 wU a b).length=wU.length∧val (a08 wU a b)=(val a+val b) % 2 ^ wU.length:=by
  dsimp only [a08]
  obtain ⟨acc',c',hiter,hlen,hval⟩ :=
    c2w wU.length (g4 wU a) (g4 wU b) false [] (i4 wU a) (i4 wU b)
  simp only [Bool.false_eq_true,↓reduceIte,List.append_nil,Bool.toNat_false,add_zero] at hiter hval
  rw [hiter]
  simp only [a5,List.reverse_reverse]
  refine ⟨hlen,?_⟩
  have hlt:val acc'< 2 ^ wU.length:=by rw [← hlen];exact a4i acc'
  have hmod1:val acc'=(val (g4 wU a)+val (g4 wU b)) % 2 ^ wU.length:=by
    have:val (g4 wU a)+val (g4 wU b)=2 ^ wU.length* c'.toNat+val acc':=by linarith
    rw [this,Nat.mul_add_mod,Nat.mod_eq_of_lt hlt]
  rw [hmod1,w8,w8,Nat.mod_add_mod,Nat.add_mod_mod]
lemma a0z (wU a b:List Bool):(a08 wU a b).length=wU.length:=(a8r wU a b).1
lemma b0r (wU a b:List Bool):val (a08 wU a b)=(val a+val b) % 2 ^ wU.length :=
  (a8r wU a b).2
lemma b0v {uw ua ub:List Bool→ List Bool} (hw:a4 uw) (ha:a4 ua) (hb:a4 ub) :
    a4 (fun s=>a08 (uw s) (ua s) (ub s)):=by
  have hfin:=v4 6 c29 c14 hw
    (a7 (n4 hw ha) (a7 (n4 hw hb) (b0 (a1 [] []))))
  exact a2 (a2 (a2 (a2 hfin a3) a3) a3) b7c
def a68 (y:List Bool):List Bool :=
  let wU:=(a0 y).1
  let r1:=(a0 y).2
  let bRem:=(a0 r1).1
  let r2:=(a0 r1).2
  let aSh:=(a0 r2).1
  let acc:=(a0 r2).2
  let acc':=sel (j3 bRem) (g4 wU acc) (a08 wU acc aSh)
  let aSh':=a2k wU aSh
  a1 wU (a1 bRem.tail (a1 aSh' acc'))
lemma c2j:a4 a68:=by
  have hw:=a6
  have hr1:=a3
  have hb:=a2 hr1 a6
  have hr2:=a2 hr1 a3
  have ha:=a2 hr2 a6
  have hacc:=a2 hr2 a3
  have hacc':=d6 (a2 hb m6) (n4 hw hacc) (b0v hw hacc ha)
  have ha':=c0z hw ha
  exact a7 hw (a7 (a2 hb o3) (a7 ha' hacc'))
def a6f (wU a b:List Bool):List Bool :=
  let fin:=a68^[wU.length] (a1 wU (a1 (g4 wU b) (a1 (g4 wU a) (f3 wU))))
  (a0 (a0 (a0 fin).2).2).2
lemma b5r {uw ua ub:List Bool→ List Bool} (hw:a4 uw) (ha:a4 ua) (hb:a4 ub) :
    a4 (fun s=>a6f (uw s) (ua s) (ub s)):=by
  have hfin:=a5k 4 c2j
    (fun y=>by dsimp only [a68];rw [a5])
    (fun y=>by
      dsimp only [a68]
      set wU:=(a0 y).1;set r1:=(a0 y).2
      set bRem:=(a0 r1).1;set r2:=(a0 r1).2
      set aSh:=(a0 r2).1;set acc:=(a0 r2).2
      have h1:2* wU.length+r1.length≤ y.length:=m7 y
      have h2:2* bRem.length+r2.length≤ r1.length:=m7 r1
      have h3:2* aSh.length+acc.length≤ r2.length:=m7 r2
      rw [p0,p0,p0,b95]
      have hbt:bRem.tail.length≤ bRem.length:=by cases bRem <;> simp
      have hacc:(sel (j3 bRem) (g4 wU acc) (a08 wU acc aSh)).length=wU.length:=by
        unfold sel;split_ifs
        · exact i4 _ _
        · exact a0z _ _ _
      omega)
    hw (a7 hw (a7 (n4 hw hb) (a7 (n4 hw ha) (a2 hw n6))))
  exact b7 (a2 (a2 (a2 hfin a3) a3) a3) (fun _=>rfl)
lemma c2m (wU:List Bool) (k:ℕ):∀ (bRem aSh acc:List Bool),
    bRem.length=k→ aSh.length=wU.length→ acc.length=wU.length →
    ∃ aSh' acc',
      a68^[k] (a1 wU (a1 bRem (a1 aSh acc))) =
        a1 wU (a1 [] (a1 aSh' acc')) ∧
      acc'.length=wU.length ∧
      val acc' % 2 ^ wU.length=(val acc+val aSh* val bRem) % 2 ^ wU.length:=by
  induction k with
  | zero =>
    intro bRem aSh acc hb _ hacc
    cases bRem
    · exact ⟨aSh,acc,rfl,hacc,by simp [val]⟩
    · simp at hb
  | succ k ih =>
    intro bRem aSh acc hb ha hacc
    cases bRem with
    | nil=>simp at hb
    | cons bb br =>
      rw [Function.iterate_succ_apply]
      have hstep:a68 (a1 wU (a1 (bb::br) (a1 aSh acc))) =
          a1 wU (a1 br (a1 (a2k wU aSh) (if bb then a08 wU acc aSh else g4 wU acc))):=by
        dsimp only [a68]
        simp only [a5,List.tail_cons]
        cases bb <;> rfl
      rw [hstep]
      have hacc1_len:(if bb then a08 wU acc aSh else g4 wU acc).length=wU.length:=by
        cases bb <;> simp [a0z,i4]
      obtain ⟨aSh',acc',hiter,hlen',hval'⟩ :=
        ih br (a2k wU aSh) (if bb then a08 wU acc aSh else g4 wU acc)
          (by simpa using hb) (b95 wU aSh) hacc1_len
      refine ⟨aSh',acc',hiter,hlen',?_⟩
      rw [hval',c21]
      have hmod1:val (if bb then a08 wU acc aSh else g4 wU acc) ≡
          val acc+val aSh* bb.toNat [MOD 2 ^ wU.length]:=by
        cases bb with
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,Bool.toNat_false,mul_zero,add_zero,w8]
          exact Nat.mod_modEq _ _
        | true =>
          simp only [↓reduceIte,Bool.toNat_true,mul_one,b0r]
          exact Nat.mod_modEq _ _
      have hmod2:((2* val aSh) % 2 ^ wU.length)* val br ≡ (2* val aSh)* val br [MOD 2 ^ wU.length] :=
        (Nat.mod_modEq _ _).mul_right _
      have hcomb:=hmod1.add hmod2
      have hrew:val acc+val aSh* bb.toNat+2* val aSh* val br =
          val acc+val aSh* (bb.toNat+2* val br):=by ring
      rw [hrew] at hcomb
      simpa only [Nat.ModEq,val] using hcomb
lemma a8o (wU a b:List Bool) :
    (a6f wU a b).length=wU.length∧val (a6f wU a b)=(val a* val b) % 2 ^ wU.length:=by
  dsimp only [a6f]
  obtain ⟨aSh',acc',hiter,hlen,hval⟩ :=
    c2m wU wU.length (g4 wU b) (g4 wU a) (f3 wU)
      (i4 wU b) (i4 wU a) (q7 wU)
  rw [hiter]
  simp only [a5]
  refine ⟨hlen,?_⟩
  rw [w1,zero_add,w8,w8] at hval
  have hlt:val acc'< 2 ^ wU.length:=by rw [← hlen];exact a4i acc'
  rw [Nat.mod_eq_of_lt hlt] at hval
  rw [hval,Nat.mod_mul_mod,Nat.mul_mod_mod]
lemma b13 (wU a b:List Bool):(a6f wU a b).length=wU.length:=(a8o wU a b).1
lemma b58 (wU a b:List Bool):val (a6f wU a b)=(val a* val b) % 2 ^ wU.length :=
  (a8o wU a b).2
def u6 (s:List Bool):List Bool:=s.filter id
lemma u8:a4 u6 :=
  g0 _ _ _ (fun (_:Unit) (b:Bool)=>((),if b then some true else none))
    (fun _=>none) () fun s=>by
      induction s with
      | nil=>rfl
      | cons b r ih=>cases b <;> simp [c7,u6] at ih ⊢ <;> exact ih
lemma a9c (n:ℕ) (r:List Bool):hd (un n++false::r)=un n:=by
  induction n with
  | zero=>simp [hd]
  | succ n ih=>simpa [hd,a1w] using ih
lemma a61 (n:ℕ) (r:List Bool):r5 (un n++false::r)=r:=by
  induction n with
  | zero=>simp [r5]
  | succ n ih=>simpa [r5,a1w] using ih
lemma a5x (p:Polynomial ℕ):∃ a d:ℕ,∀ m:ℕ,1≤ m→ p.eval m≤ a* m ^ d:=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a,d,h⟩:=hp
    obtain ⟨b,e,h'⟩:=hq
    refine ⟨a+b,d+e,fun m hm=>?_⟩
    rw [Polynomial.eval_add,Nat.add_mul]
    have h1:m ^ d≤ m ^ (d+e):=Nat.pow_le_pow_right hm (by omega)
    have h2:m ^ e≤ m ^ (d+e):=Nat.pow_le_pow_right hm (by omega)
    exact add_le_add ((h m hm).trans (Nat.mul_le_mul_left _ h1))
      ((h' m hm).trans (Nat.mul_le_mul_left _ h2))
  | monomial d c=>exact ⟨c,d,fun m _=>by rw [Polynomial.eval_monomial]⟩
lemma a4v (f:List Bool→ List Bool) (hf:a4 f) :
    ∃ q:Polynomial ℕ,∀ x:List Bool,(f x).length≤ q.eval x.length:=by
  obtain ⟨c⟩:=hf
  refine ⟨Polynomial.X+Polynomial.C (p7 c.tm)* c.time,fun x=>?_⟩
  obtain ⟨⟨steps,hev⟩,hle⟩:=c.outputsFun x
  have hev':(flip bind (Turing.TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main,c.tm.initialState,Function.update (fun _=>[]) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩:Turing.TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none,c.tm.initialState,Function.update (fun _=>[]) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩:Turing.TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ):=by
    rw [← i7,← i9];exact hev
  have key:=a3m c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self,List.length_map] at key
  have hin:((Function.update (fun _=>([]:List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x):∀ k,List (c.tm.Γ k)) c.tm.k₁).length≤ x.length:=by
    by_cases hk:c.tm.k₁=c.tm.k₀
    · rw [hk];simp
    · rw [Function.update_of_ne hk];simp
  rw [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
  calc (f x).length ≤ x.length+p7 c.tm * steps:=key.trans (by omega)
    _ ≤ x.length+p7 c.tm * c.time.eval x.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _
lemma b3r (p:Polynomial ℕ):a4 (fun x:List Bool=>List.replicate (p.eval x.length) true):=by
  have hpow:∀ n,a4 (fun x:List Bool=>List.replicate (x.length ^ n) true):=by
    intro n
    induction n with
    | zero=>exact b7 (b0 [true]) (fun x=>by simp)
    | succ n ih=>exact b7 (g9 g5 ih) (fun x=>by simp [j0,un,pow_succ,Nat.mul_comm])
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>exact b7 (b8 hp hq) (fun x=>by rw [Polynomial.eval_add,List.replicate_add])
  | monomial n a=>
    refine b7 (g9 (b0 (List.replicate a true)) (hpow n)) (fun x=>?_)
    simp [j0,un,Polynomial.eval_monomial]
def a2e (f:List Bool→ List Bool) (y:List Bool):List Bool :=
  a1 (a0 y).1 (a1 (a0 (a0 y).2).1.tail
    (a1 (a0 (a0 (a0 y).2).2).1
      (m4 (a0 y).1 (f (a1 (a0 (a0 y).2).1.tail
        (a0 (a0 (a0 y).2).2).1))++(a0 (a0 (a0 y).2).2).2)))
lemma b3a {f:List Bool→ List Bool} (hf:a4 f):a4 (a2e f):=by
  have h1:a4 (fun y=>(a0 y).1):=a6
  have h2:a4 (fun y=>(a0 y).2):=a3
  have hr:=a2 (a2 h2 a6) o3
  have h3:=a2 h2 a3
  have harg:=a2 h3 a6
  have hacc:=a2 h3 a3
  exact a7 h1 (a7 hr (a7 harg
    (b8 (k4 h1 (a2 (a7 hr harg) hf)) hacc)))
lemma b15 (f:List Bool→ List Bool) (pad r arg acc:List Bool) :
    a2e f (a1 pad (a1 r (a1 arg acc))) =
      a1 pad (a1 r.tail (a1 arg (m4 pad (f (a1 r.tail arg))++acc))):=by
  simp only [a2e,a5]
lemma a9j (f:List Bool→ List Bool) (y:List Bool) :
    (a2e f y).length≤ y.length+((a0 y).1.length+3):=by
  have h1:=n7 y
  have h2:=n7 (a0 y).2
  have h3:=n7 (a0 (a0 y).2).2
  have h4:(m4 (a0 y).1 (f (a1 (a0 (a0 y).2).1.tail
        (a0 (a0 (a0 y).2).2).1))).length≤ (a0 y).1.length:=by
    rw [k7,List.length_take];exact Nat.min_le_left _ _
  have h5:(a0 (a0 y).2).1.tail.length≤ (a0 (a0 y).2).1.length:=by simp
  simp only [a2e,a02,List.length_append]
  omega
lemma b2s (f:List Bool→ List Bool) (pad arg:List Bool) (n:ℕ)
    (hpad:∀ i< n,(f (a1 (un i) arg)).length≤ pad.length) (acc:List Bool) :
    (a2e f)^[n] (a1 pad (a1 (un n) (a1 arg acc))) =
      a1 pad (a1 [] (a1 arg
        ((List.range n).flatMap (fun i=>f (a1 (un i) arg))++acc))):=by
  induction n generalizing acc with
  | zero=>simp
  | succ n ih =>
    rw [Function.iterate_succ_apply,b15,a1w,List.tail_cons,k7,
      List.take_of_length_le (hpad n (by omega)),ih (fun i hi=>hpad i (by omega)),
      List.range_succ,List.flatMap_append]
    simp
lemma d9 {f cnt arg:List Bool→ List Bool} (hf:a4 f) (hcnt:a4 cnt)
    (harg:a4 arg) :
    a4 (fun s=>(List.range (cnt s).length).flatMap fun i=>f (a1 (un i) (arg s))):=by
  obtain ⟨P,hP⟩:=a4v f hf
  have hpad:a4 (fun s=>List.replicate (P.eval (a1 (cnt s) (arg s)).length) true) :=
    a2 (a7 hcnt harg) (b3r P)
  have hun:a4 (fun s=>j0 (cnt s) [true]):=g9 hcnt (b0 [true])
  have hinit:=a7 hpad (a7 hun (a7 harg (b0 [])))
  have hit:=a2i (fun y=>(a0 y).1.length+3) 3 (b3a hf)
    (fun y=>by simp only [a2e,a5];exact le_rfl) (a9j f)
    (fun y=>by have:=n7 y;omega) hcnt hinit
  have hout:=a2 (a2 (a2 hit a3) a3) a3
  refine b7 hout (fun s=>?_)
  have e:j0 (cnt s) [true]=un (cnt s).length:=by simp [j0]
  have hb:∀ i< (cnt s).length,(f (a1 (un i) (arg s))).length ≤
      (List.replicate (P.eval (a1 (cnt s) (arg s)).length) true).length:=by
    intro i hi
    rw [List.length_replicate]
    refine (hP _).trans (a0h P ?_)
    rw [a02,a02,b4]
    omega
  show (a0 (a0 (a0 ((a2e f)^[(cnt s).length]
    (a1 _ (a1 (j0 (cnt s) [true]) (a1 (arg s) []))))).2).2).2=_
  rw [e,b2s f _ (arg s) (cnt s).length hb,a5,a5,a5]
  simp
end
def n5 {K:Type} {Γ:K→ Type} {Λ σ:Type}:Turing.TM2.Stmt Γ Λ σ→ Set (Σ k,Γ k)
  | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,Γ k))∪ n5 q
  | .peek _ _ q=>n5 q
  | .pop _ _ q=>n5 q
  | .load _ q=>n5 q
  | .branch _ q₁ q₂=>n5 q₁∪ n5 q₂
  | .goto _=>∅
  | .halt=>∅
lemma a5z {K:Type} {Γ:K→ Type} {Λ σ:Type} [Finite σ]
    (q:Turing.TM2.Stmt Γ Λ σ):(n5 q).Finite:=by
  induction q with
  | push _ _ _ ih=>exact (Set.finite_range _).union ih
  | peek _ _ _ ih=>exact ih
  | pop _ _ _ ih=>exact ih
  | load _ _ ih=>exact ih
  | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
  | goto _=>exact Set.finite_empty
  | halt=>exact Set.finite_empty
def t6 {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T:∀ k,Set (Γ k)) :
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩:Σ j,Γ j)∈ n5 q→ s∈ T k) →
    Turing.TM2.Stmt (fun k=>{s:Γ k // s∈ T k}) Λ σ
  | .push k g q,h=>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
      (t6 T q (fun j s hs=>h j s (Or.inr hs)))
  | .peek k f q,h=>.peek k (fun v o=>f v (o.map Subtype.val)) (t6 T q h)
  | .pop k f q,h=>.pop k (fun v o=>f v (o.map Subtype.val)) (t6 T q h)
  | .load a q,h=>.load a (t6 T q h)
  | .branch f q₁ q₂,h=>.branch f
      (t6 T q₁ (fun j s hs=>h j s (Or.inl hs)))
      (t6 T q₂ (fun j s hs=>h j s (Or.inr hs)))
  | .goto f,_=>.goto f
  | .halt,_=>.halt
def y7 {K : Type} {Γ : K → Type} {Λ σ : Type} (T : ∀ k, Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s:Γ k // s∈ T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
  ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma b2c {K:Type} {Γ:K→ Type} {Λ σ:Type} (T:∀ k,Set (Γ k)) :
    Function.Injective (y7 (Λ:=Λ) (σ:=σ) T):=by
  rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
  simp only [y7,Turing.TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl,rfl,hS⟩:=h
  congr 1
  funext k
  exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma a1j {K:Type} [DecidableEq K] {Γ:K→ Type} (T:∀ k,Set (Γ k))
    (S:∀ k,List {s:Γ k // s∈ T k}) (k:K) (l:List {s:Γ k // s∈ T k}) :
    (fun j=>(Function.update S k l j).map Subtype.val) =
      Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
  funext j
  by_cases h:j= k
  · subst h; simp
  · simp [h]
lemma a82 {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
    (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
    (hq:∀ k s,(⟨k,s⟩:Σ j,Γ j)∈ n5 q→ s∈ T k)
    (v:σ) (S:∀ k,List {s:Γ k // s∈ T k}) :
    y7 T (Turing.TM2.stepAux (t6 T q hq) v S) =
      Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
  induction q generalizing v S with
  | push k g q ih =>
    simp only [t6,Turing.TM2.stepAux]
    rw [ih,a1j]
    rfl
  | peek k f q ih =>
    simp only [t6,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [List.head?_map])
  | pop k f q ih =>
    simp only [t6,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [a1j,List.head?_map,List.map_tail])
  | load a q ih =>
    simp only [t6,Turing.TM2.stepAux]
    exact ih hq (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [t6,Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ v S
    · exact ih₁ _ v S
  | goto f=>rfl
  | halt=>rfl
lemma b0x (c:Turing.TM2ComputableAux Bool Bool) :
    ∃ c' : Turing.TM2ComputableAux Bool Bool, (∀ j, Finite (c'.tm.Γ j)) ∧
      ∀ (x y : List Bool) (s : ℕ),
        Turing.TM2OutputsInTime c.tm (x.map c.inputAlphabet.invFun)
            (some (y.map c.outputAlphabet.invFun)) s →
        Nonempty (Turing.TM2OutputsInTime c'.tm (x.map c'.inputAlphabet.invFun)
            (some (y.map c'.outputAlphabet.invFun)) s):=by
  classical
  let _:DecidableEq c.tm.K:=c.tm.kDecidableEq
  let _:Fintype c.tm.K:=c.tm.kFin
  let _:Fintype c.tm.Λ:=c.tm.ΛFin
  let _:Fintype c.tm.σ:=c.tm.σFin
  let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
  let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k =>
    {s | k= c.tm.k₀∨ k= c.tm.k₁ ∨
      (⟨k,s⟩:Σ j,c.tm.Γ j)∈ ⋃ l:c.tm.Λ,n5 (c.tm.m l)}
  let e₀:{s:c.tm.Γ c.tm.k₀ // s∈ T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀ :=
    { toFun := Subtype.val
      invFun:=fun s=>⟨s,Or.inl rfl⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let e₁:{s:c.tm.Γ c.tm.k₁ // s∈ T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁ :=
    { toFun := Subtype.val
      invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s∈ T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
  let tm':Turing.FinTM2 :=
    { K := c.tm.K
      kDecidableEq:=c.tm.kDecidableEq
      kFin:=c.tm.kFin
      k₀:=c.tm.k₀
      k₁:=c.tm.k₁
      Γ:=fun k=>{s:c.tm.Γ k // s∈ T k}
      Λ:=c.tm.Λ
      main:=c.tm.main
      ΛFin:=c.tm.ΛFin
      σ:=c.tm.σ
      initialState:=c.tm.initialState
      σFin:=c.tm.σFin
      Γk₀Fin:=hΓ0Fin
      m := fun l => t6 T (c.tm.m l)
        (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
  have hFin:∀ j:tm'.K,Finite (tm'.Γ j):=by
    intro j
    by_cases h0:j= c.tm.k₀
    · subst h0; exact Finite.of_fintype _
    · by_cases h1 : j = c.tm.k₁
      · subst h1
        have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin:(⋃ l:c.tm.Λ,n5 (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l=>a5z (c.tm.m l)
        have:Finite ↥(⋃ l:c.tm.Λ,n5 (c.tm.m l)):=hUfin.to_subtype
        refine Finite.of_injective (f:=fun x:tm'.Γ j =>
            (⟨⟨j,x.1⟩,by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩:↥(⋃ l:c.tm.Λ,n5 (c.tm.m l)))) ?_
        intro x y hxy
        have h1':=congrArg (fun z=>z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep:∀ cfg:tm'.Cfg,
      Option.map (y7 T) (tm'.step cfg)= c.tm.step (y7 T cfg):=by
    rintro ⟨l,v,S⟩
    cases l with
    | none=>rfl
    | some l =>
      change some (y7 T (Turing.TM2.stepAux (t6 T (c.tm.m l) _) v S)) =
        some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
      exact congrArg some (a82 T (c.tm.m l) _ v S)
  have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
      Option.map (y7 T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (y7 T cfg)):=by
    intro steps
    induction steps with
    | zero=>intro cfg; rfl
    | succ steps ih =>
      intro cfg
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
      | none =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]; rfl
      | some cfg' =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]
        exact hstep cfg'
  refine ⟨⟨tm',e₀.trans c.inputAlphabet,e₁.trans c.outputAlphabet⟩,hFin,?_⟩
  intro x y s h
  refine ⟨{ steps:=h.steps,evals_in_steps:=?_,steps_le_m:=h.steps_le_m }⟩
  have horig:=h.evals_in_steps
  have hinit:y7 T (Turing.initList tm' (x.map (e₀.trans c.inputAlphabet).invFun)) =
      Turing.initList c.tm (x.map c.inputAlphabet.invFun):=by
    simp only [y7,Turing.initList]
    congr 1; funext k
    by_cases hk:k= c.tm.k₀
    · subst hk
      dsimp only [tm']
      simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]
      rfl
    · dsimp only [tm']
      simp only [hk,↓reduceDIte,List.map_nil]
  have hhalt:y7 T (Turing.haltList tm' (y.map (e₁.trans c.outputAlphabet).invFun)) =
      Turing.haltList c.tm (y.map c.outputAlphabet.invFun):=by
    simp only [y7,Turing.haltList]
    congr 1; funext k
    by_cases hk:k= c.tm.k₁
    · subst hk
      dsimp only [tm']
      simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]
      rfl
    · dsimp only [tm']
      simp only [hk,↓reduceDIte,List.map_nil]
  apply Option.map_injective (b2c T)
  rw [hiter,hinit,horig]
  exact (congrArg some hhalt).symm
end asmP0
section asmP1
open Finset
section Tree
variable {t:ℕ} (par:Fin (t+1)→ Fin (t+1))
def p9 (T:Fin (t+1)→ Prop) (a:Fin (t+1)):Prop :=
  T a∧ ∀ i,T i→ i≠ a→ i≠ 0∧ T (par i)
lemma a56 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) :
    ∀ (m:ℕ) (x:Fin (t+1)),par^[m] x≤ x:=by
  intro m
  induction m with
  | zero=>intro x; simp
  | succ m ih =>
    intro x
    rw [Function.iterate_succ_apply]
    refine le_trans (ih (par x)) ?_
    by_cases hx:x= 0
    · subst hx; rw [hpar0]
    · exact le_of_lt (hpar x hx)
lemma b4m (hpar0:par 0= 0):∀ m:ℕ,par^[m] 0= 0:=by
  intro m
  induction m with
  | zero=>simp
  | succ m ih=>rw [Function.iterate_succ_apply,hpar0,ih]
lemma b6q (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (m:ℕ)
    (x:Fin (t+1)) (hx:x≠ 0):par^[m+1] x< x:=by
  rw [Function.iterate_succ_apply]
  exact lt_of_le_of_lt (a56 par hpar hpar0 m (par x)) (hpar x hx)
lemma b0t (hpar:∀ i,i≠ 0→ par i< i) {T:Fin (t+1)→ Prop} {a:Fin (t+1)}
    (h:p9 par T a) :
    ∀ n,∀ i:Fin (t+1),i.val= n→ T i→ ∃ d,par^[d] i= a∧ ∀ d'≤ d,T (par^[d'] i):=by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hin hTi
    by_cases hia:i= a
    · refine ⟨0, by simp [hia], fun d' hd' => ?_⟩
      have:d'= 0:=by omega
      subst this; simpa using hTi
    · obtain ⟨hi0, hTp⟩ := h.2 i hTi hia
      have hlt:(par i).val< n:=by
        have:=Fin.lt_iff_val_lt_val.mp (hpar i hi0)
        omega
      obtain ⟨d,hd,hpath⟩:=ih _ hlt (par i) rfl hTp
      refine ⟨d+1,?_,?_⟩
      · rw [Function.iterate_succ_apply]; exact hd
      · intro d' hd'
        cases d' with
        | zero=>simpa using hTi
        | succ d'' =>
          rw [Function.iterate_succ_apply]
          exact hpath d'' (by omega)
lemma c0h (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) {α:Type*}
    (mem:α→ Fin (t+1)→ Prop) (S:Finset α) (hS:S.Nonempty)
    (htop:∀ e∈ S,∃ a,p9 par (mem e) a)
    (hpw:∀ e∈ S,∀ f∈ S,∃ i,mem e i∧ mem f i) :
    ∃ i,∀ e∈ S,mem e i:=by
  classical
  choose! top htop' using htop
  obtain ⟨e₀,he₀,hmax⟩:=S.exists_max_image (fun e=>top e) hS
  refine ⟨top e₀,fun e he=>?_⟩
  obtain ⟨n,hn1,hn0⟩:=hpw e he e₀ he₀
  obtain ⟨d0,hd0,-⟩:=b0t par hpar (htop' e₀ he₀) n.val n rfl hn0
  obtain ⟨de,hde,hpath⟩:=b0t par hpar (htop' e he) n.val n rfl hn1
  by_cases hle:d0≤ de
  · have := hpath d0 hle
    rwa [hd0] at this
  · have hsplit:par^[d0] n= par^[d0 - de] (par^[de] n):=by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [hde] at hsplit
    by_cases hz:top e= 0
    · have : top e₀ = top e := by rw [← hd0, hsplit, hz, b4m par hpar0]
      rw [this]; exact (htop' e he).1
    · exfalso
      have hlt:=b6q par hpar hpar0 (d0 - de - 1) (top e) hz
      have h1:d0 - de - 1+ 1= d0 - de:=by omega
      rw [h1,← hsplit,hd0] at hlt
      exact absurd (hmax e he) (not_le.mpr hlt)
lemma a0l (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) {α:Type*}
    (mem:α→ Fin (t+1)→ Prop) [∀ e i,Decidable (mem e i)] (S:Finset α)
    (hS:S.Nonempty) (htop:∀ e∈ S,∃ a,p9 par (mem e) a)
    (hc:∃ i,∀ e∈ S,mem e i) :
    (univ.filter (fun i:Fin (t+1) =>
      (∀ e∈ S,mem e i)∧ ¬ (i≠ 0∧ ∀ e∈ S,mem e (par i)))).card= 1:=by
  classical
  choose! top htop' using htop
  have key:∀ i,(∀ e∈ S,mem e i)→ ¬ (i≠ 0∧ ∀ e∈ S,mem e (par i)) →
      ∃ e∈ S,i= top e:=by
    intro i hi hn
    by_cases h0:i= 0
    · obtain ⟨e, he⟩ := hS
      refine ⟨e,he,?_⟩
      by_contra hne
      exact ((htop' e he).2 i (hi e he) hne).1 h0
    · push_neg at hn
      obtain ⟨e,he,hne⟩:=hn h0
      refine ⟨e,he,?_⟩
      by_contra hne'
      exact hne ((htop' e he).2 i (hi e he) hne').2
  have anc:∀ i j,(∀ e∈ S,mem e i)→ (∀ e∈ S,mem e j) →
      ¬ (i≠ 0∧ ∀ e∈ S,mem e (par i))→ i≤ j:=by
    intro i j hi hj hn
    obtain ⟨e,he,rfl⟩:=key i hi hn
    obtain ⟨d,hd,-⟩:=b0t par hpar (htop' e he) j.val j rfl (hj e he)
    rw [← hd]; exact a56 par hpar hpar0 d j
  obtain ⟨i1,hi1⟩:=hc
  have hFne:(univ.filter (fun i:Fin (t+1)=>∀ e∈ S,mem e i)).Nonempty :=
    ⟨i1,mem_filter.mpr ⟨mem_univ _,hi1⟩⟩
  set F:=univ.filter (fun i:Fin (t+1)=>∀ e∈ S,mem e i) with hF
  have hi0F:F.min' hFne∈ F:=F.min'_mem hFne
  have hi0C:∀ e∈ S,mem e (F.min' hFne):=(mem_filter.mp hi0F).2
  have hi0n:¬ (F.min' hFne≠ 0∧ ∀ e∈ S,mem e (par (F.min' hFne))):=by
    rintro ⟨hne,hp⟩
    have hmem:par (F.min' hFne)∈ F:=mem_filter.mpr ⟨mem_univ _,hp⟩
    have:=F.min'_le (par (F.min' hFne)) hmem
    exact absurd (hpar _ hne) (not_lt.mpr this)
  rw [card_eq_one]
  refine ⟨F.min' hFne,?_⟩
  ext i
  simp only [mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨hi, hn⟩
    exact le_antisymm (anc i _ hi hi0C hn) (anc _ i hi0C hi hi0n)
  · rintro rfl; exact ⟨hi0C,hi0n⟩
lemma a15 {α:Type*} [DecidableEq α] (Y:Finset α) (p:α→ Prop)
    [DecidablePred p] :
    (Y.filter p).powerset= Y.powerset.filter (fun S=>∀ e∈ S,p e):=by
  ext S
  simp only [mem_powerset,mem_filter]
  constructor
  · intro h
    exact ⟨fun x hx=>(mem_filter.mp (h hx)).1,fun x hx=>(mem_filter.mp (h hx)).2⟩
  · rintro ⟨h1, h2⟩ x hx
    exact mem_filter.mpr ⟨h1 hx,h2 x hx⟩
lemma b5i (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) {α:Type*}
    [DecidableEq α] (mem:α→ Fin (t+1)→ Prop) [∀ e i,Decidable (mem e i)] (Y:Finset α)
    (htop:∀ e∈ Y,∃ a,p9 par (mem e) a) (μ:Finset α→ ℤ) (h0:μ ∅= 0)
    (hsupp:∀ S⊆ Y,μ S≠ 0→ ∃ i,∀ e∈ S,mem e i) :
    ∑ S ∈ Y.powerset, μ S = ∑ i : Fin (t+1),
      (∑ S∈ (Y.filter (fun e=>mem e i)).powerset,μ S -
        ∑ S∈ (Y.filter (fun e=>mem e i∧ i≠ 0∧ mem e (par i))).powerset,μ S):=by
  classical
  have per:∀ S∈ Y.powerset,∑ i:Fin (t+1),
      ((if ∀ e∈ S,mem e i then μ S else 0) -
        (if ∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) then μ S else 0))= μ S:=by
    intro S hS
    by_cases hμ:μ S= 0
    · simp [hμ]
    · have hne:S.Nonempty:=by
        rw [nonempty_iff_ne_empty]; rintro rfl; exact hμ h0
      have hc:=hsupp S (mem_powerset.mp hS) hμ
      have hcard:=a0l par hpar hpar0 mem S hne
        (fun e he=>htop e (mem_powerset.mp hS he)) hc
      have hpt:∀ i:Fin (t+1),((if ∀ e∈ S,mem e i then μ S else 0) -
          (if ∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) then μ S else 0)) =
          if ((∀ e∈ S,mem e i)∧ ¬ (i≠ 0∧ ∀ e∈ S,mem e (par i))) then μ S else 0:=by
        intro i
        obtain ⟨e0,he0⟩:=hne
        by_cases h1:∀ e∈ S,mem e i
        · by_cases h2 : i ≠ 0 ∧ ∀ e ∈ S, mem e (par i)
          · have h3:∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) :=
              fun e he=>⟨h1 e he,h2.1,h2.2 e he⟩
            rw [if_pos h1,if_pos h3,if_neg (fun h=>h.2 h2)]; ring
          · have h3:¬ ∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) :=
              fun h=>h2 ⟨(h e0 he0).2.1,fun e he=>(h e he).2.2⟩
            rw [if_pos h1,if_neg h3,if_pos ⟨h1,h2⟩]; ring
        · have h3:¬ ∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) :=
            fun h=>h1 (fun e he=>(h e he).1)
          rw [if_neg h1,if_neg h3,if_neg (fun h=>h1 h.1)]; ring
      rw [sum_congr rfl (fun i _=>hpt i),← sum_filter,sum_const,hcard,one_smul]
  calc ∑ S ∈ Y.powerset, μ S
      = ∑ S ∈ Y.powerset, ∑ i : Fin (t+1),
          ((if ∀ e∈ S,mem e i then μ S else 0) -
            (if ∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) then μ S else 0)) :=
        (sum_congr rfl per).symm
    _ = ∑ i : Fin (t+1), ∑ S ∈ Y.powerset,
          ((if ∀ e∈ S,mem e i then μ S else 0) -
            (if ∀ e∈ S,mem e i∧ i≠ 0∧ mem e (par i) then μ S else 0)):=sum_comm
    _ = _ := by
        refine sum_congr rfl (fun i _=>?_)
        rw [a15,a15,sum_filter,sum_filter,← sum_sub_distrib]
end Tree
section Rows
variable {k:ℕ}
def a3w (b:Bool):ℤ:=if b then 1 else -1
def a05 (rows:List (Finset (Fin k × Fin k) × Bool)) (Q:Finset (Fin k × Fin k)):ℤ :=
  ((rows.filter (fun t=>t.2 && decide (Q⊆ t.1))).length:ℤ) -
    ((rows.filter (fun t=>!t.2 && decide (Q⊆ t.1))).length:ℤ)
def a0k (rows:List (Finset (Fin k × Fin k) × Bool)) (Q:Finset (Fin k × Fin k)):ℕ :=
  (rows.filter (fun r=>decide (decide ((Q∩ r.1).Nonempty)= r.2))).length
def w3 (rows:List (Finset (Fin k × Fin k) × Bool)) (Y:Finset (Fin k × Fin k)):ℤ :=
  ((rows.filter (fun t=>t.2 && decide ((Y∩ t.1).Nonempty))).length:ℤ) -
    ((rows.filter (fun t=>!t.2 && decide ((Y∩ t.1).Nonempty))).length:ℤ)
def k6 (rows:List (Finset (Fin k × Fin k) × Bool)):ℕ :=
  (rows.filter (fun r=>!r.2)).length
def mob (rows:List (Finset (Fin k × Fin k) × Bool)) (S:Finset (Fin k × Fin k)):ℤ :=
  if S= ∅ then 0 else (-1) ^ (S.card+ 1)* a05 rows S
lemma b0m (r:Finset (Fin k × Fin k) × Bool) rows Q :
    a05 (r::rows) Q= a05 rows Q+ (if Q⊆ r.1 then a3w r.2 else 0):=by
  obtain ⟨R,b⟩:=r
  unfold a05 a3w
  cases b <;> by_cases h:Q⊆ R <;> simp [List.filter_cons,h] <;> ring
lemma a2l (r:Finset (Fin k × Fin k) × Bool) rows Y :
    w3 (r::rows) Y= w3 rows Y+ (if (Y∩ r.1).Nonempty then a3w r.2 else 0):=by
  obtain ⟨R,b⟩:=r
  unfold w3 a3w
  cases b <;> by_cases h:(Y∩ R).Nonempty <;> simp [List.filter_cons,h] <;> ring
lemma b4r (rows:List (Finset (Fin k × Fin k) × Bool)) Q :
    (a0k rows Q:ℤ)= k6 rows+ w3 rows Q:=by
  induction rows with
  | nil=>simp [a0k,k6,w3]
  | cons r rows ih =>
    rw [a2l]
    obtain ⟨R,b⟩:=r
    unfold a0k k6 a3w at *
    cases b <;> by_cases h:(Q∩ R).Nonempty <;> simp [List.filter_cons,h] at* <;> linarith
lemma b7x (Y R:Finset (Fin k × Fin k)) :
    (if (Y∩ R).Nonempty then (1:ℤ) else 0) =
      ∑ S∈ Y.powerset,(if S= ∅ then 0 else (-1) ^ (S.card+ 1)* (if S⊆ R then 1 else 0)):=by
  classical
  have A:∑ S∈ Y.powerset,(-1:ℤ) ^ S.card* (if S⊆ R then 1 else 0) =
      if Y∩ R= ∅ then 1 else 0:=by
    rw [← sum_powerset_neg_one_pow_card]
    have hset:(Y∩ R).powerset= Y.powerset.filter (fun S=>S⊆ R):=by
      ext S; simp [subset_inter_iff]
    rw [hset,sum_filter]
    refine sum_congr rfl (fun S _=>?_)
    split_ifs <;> simp
  have B:∀ S:Finset (Fin k × Fin k),
      (if S= ∅ then (0:ℤ) else (-1) ^ (S.card+ 1)* (if S⊆ R then 1 else 0)) =
        -((-1:ℤ) ^ S.card* (if S⊆ R then 1 else 0))+ (if S= ∅ then 1 else 0):=by
    intro S
    by_cases hS:S= ∅
    · subst hS; simp
    · rw [if_neg hS,if_neg hS,pow_succ]; ring
  rw [sum_congr rfl (fun S _=>B S),sum_add_distrib,sum_neg_distrib,A]
  rw [sum_ite_eq' Y.powerset ∅ (fun _=>(1:ℤ))]
  simp only [empty_mem_powerset,if_true]
  by_cases h:Y∩ R= ∅
  · rw [if_pos h,if_neg (by rw [h]; simp)]; ring
  · rw [if_neg h,if_pos (nonempty_iff_ne_empty.mpr h)]; ring
lemma a6a (rows:List (Finset (Fin k × Fin k) × Bool)) (Y:Finset (Fin k × Fin k)) :
    w3 rows Y= ∑ S∈ Y.powerset,mob rows S:=by
  induction rows with
  | nil=>simp [w3,mob,a05]
  | cons r rows ih =>
    have hm:∀ S,mob (r::rows) S= mob rows S +
        a3w r.2* (if S= ∅ then 0 else (-1) ^ (S.card+ 1)* (if S⊆ r.1 then 1 else 0)):=by
      intro S
      unfold mob
      rw [b0m]
      by_cases hS:S= ∅
      · simp [hS]
      · rw [if_neg hS, if_neg hS, if_neg hS]
        split_ifs <;> ring
    rw [a2l,ih,sum_congr rfl (fun S _=>hm S),sum_add_distrib,← mul_sum,← b7x]
    split_ifs <;> ring
end Rows
section Main
variable {k:ℕ}
def c6 (k:ℕ) (e:Fin k × Fin k):ℕ:=k+ e.1.val* k+ e.2.val
def a1b (E Q:Finset (Fin k × Fin k)):Prop :=
  Q⊆ E∧ ∀ e∈ Q,∀ f∈ Q,e≠ f→ Disjoint ({e.1,e.2}:Finset (Fin k)) {f.1,f.2}
lemma a3a (E:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
    (t:ℕ) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
    (hpar0:par 0= 0) (hpar:∀ i,i≠ 0→ par i< i)
    (hconn:∀ e∈ E,∃ a,c6 k e∈ B a ∧
      ∀ i,c6 k e∈ B i→ i≠ a→ i≠ 0∧ c6 k e∈ B (par i))
    (htog:∀ e∈ E,∀ f∈ E,e≠ f →
      (∃ Q,a1b E Q∧ e∈ Q∧ f∈ Q∧ a05 rows Q≠ 0) →
        ∃ i,c6 k e∈ B i∧ c6 k f∈ B i)
    (Q:Finset (Fin k × Fin k)) (hQ:a1b E Q) :
    (a0k rows Q:ℤ)= k6 rows+ ∑ i:Fin (t+1),
      (w3 rows (Q.filter (fun e=>c6 k e∈ B i)) -
        w3 rows (Q.filter (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i)))):=by
  classical
  have htop:∀ e∈ Q,∃ a,p9 par (fun i=>c6 k e∈ B i) a :=
    fun e he=>hconn e (hQ.1 he)
  have hsupp:∀ S⊆ Q,mob rows S≠ 0→ ∃ i,∀ e∈ S,c6 k e∈ B i:=by
    intro S hSQ hμ
    have hne:S≠ ∅:=by rintro rfl; exact hμ (by simp [mob])
    have hsig:a05 rows S≠ 0:=by
      intro h; apply hμ; simp [mob,hne,h]
    have hvalS:a1b E S :=
      ⟨hSQ.trans hQ.1,fun e he f hf hef=>hQ.2 e (hSQ he) f (hSQ hf) hef⟩
    refine c0h par hpar hpar0 (fun e i=>c6 k e∈ B i) S (nonempty_iff_ne_empty.mpr hne)
      (fun e he=>htop e (hSQ he)) ?_
    intro e he f hf
    by_cases hef:e= f
    · subst hef
      obtain ⟨a,ha,-⟩:=hconn e (hQ.1 (hSQ he))
      exact ⟨a,ha,ha⟩
    · exact htog e (hQ.1 (hSQ he)) f (hQ.1 (hSQ hf)) hef ⟨S,hvalS,he,hf,hsig⟩
  rw [b4r,a6a]
  congr 1
  rw [b5i par hpar hpar0 (fun e i=>c6 k e∈ B i) Q htop (mob rows) (by simp [mob]) hsupp]
  refine sum_congr rfl (fun i _=>?_)
  rw [a6a,a6a]
end Main
section Hist
def x0 (a b:ℕ):ℕ→ ℕ→ ℕ:=fun s z=>if s= a∧ z= b then 1 else 0
def j1 (f g:ℕ→ ℕ→ ℕ):ℕ→ ℕ→ ℕ:=fun s z =>
  ∑ a∈ Finset.range (s+1),∑ b∈ Finset.range (z+1),f a b* g (s - a) (z - b)
lemma a36 (g:ℕ→ ℕ→ ℕ):j1 0 g= 0:=by
  funext s z; simp [j1]
lemma a2g (f:ℕ→ ℕ→ ℕ):j1 f 0= 0:=by
  funext s z; simp [j1]
lemma a9a (f1 f2 g:ℕ→ ℕ→ ℕ):j1 (f1+ f2) g= j1 f1 g+ j1 f2 g:=by
  funext s z; simp [j1,add_mul,Finset.sum_add_distrib]
lemma a7t (f g1 g2:ℕ→ ℕ→ ℕ):j1 f (g1+ g2)= j1 f g1+ j1 f g2:=by
  funext s z; simp [j1,mul_add,Finset.sum_add_distrib]
lemma a1h {ι:Type*} [DecidableEq ι] (S:Finset ι) (f:ι→ ℕ→ ℕ→ ℕ)
    (g:ℕ→ ℕ→ ℕ):j1 (∑ x∈ S,f x) g= ∑ x∈ S,j1 (f x) g:=by
  refine Finset.induction_on S ?_ ?_
  · simp [a36]
  · intro x S hx ih
    rw [Finset.sum_insert hx,Finset.sum_insert hx,a9a,ih]
lemma a0v {ι:Type*} [DecidableEq ι] (S:Finset ι) (f:ℕ→ ℕ→ ℕ)
    (g:ι→ ℕ→ ℕ→ ℕ):j1 f (∑ x∈ S,g x)= ∑ x∈ S,j1 f (g x):=by
  refine Finset.induction_on S ?_ ?_
  · simp [a2g]
  · intro x S hx ih
    rw [Finset.sum_insert hx,Finset.sum_insert hx,a7t,ih]
lemma b5p (c c':Prop) [Decidable c] [Decidable c'] (f g:ℕ→ ℕ→ ℕ) :
    j1 (if c then f else 0) (if c' then g else 0)= if c∧ c' then j1 f g else 0:=by
  by_cases h:c <;> by_cases h':c' <;> simp [h,h',a36,a2g]
lemma a8v (a b c d:ℕ):j1 (x0 a b) (x0 c d)= x0 (a+c) (b+d):=by
  funext s z
  simp only [j1,x0]
  by_cases h:s= a+ c∧ z= b+ d
  · rw [if_pos h, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · rw [if_pos ⟨rfl,rfl⟩,if_pos ⟨by omega,by omega⟩]
    · intro b' _ hb'; rw [if_neg (fun h'=>hb' h'.2)]; simp
    · intro hb; exfalso; exact hb (Finset.mem_range.mpr (by omega))
    · intro a' _ ha'; apply Finset.sum_eq_zero; intro b' _
      rw [if_neg (fun h'=>ha' h'.1)]; simp
    · intro ha; exfalso; exact ha (Finset.mem_range.mpr (by omega))
  · rw [if_neg h]
    apply Finset.sum_eq_zero; intro a' ha'; apply Finset.sum_eq_zero; intro b' hb'
    rw [Finset.mem_range] at ha' hb'
    by_cases h1:a'= a∧ b'= b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [if_pos ⟨rfl,rfl⟩,if_neg (by omega),mul_zero]
    · rw [if_neg h1]; simp
end Hist
section DP
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
abbrev b61 (i:Fin (t+1)) (e:Fin k × Fin k) (v:Fin k):Prop :=
  c6 k e∈ B i∧ v.val∈ B i∧ ¬ (i≠ 0∧ c6 k e∈ B (par i)∧ v.val∈ B (par i))
def sig (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)):Finset (Fin k × Fin k) :=
  Q.filter (fun e=>c6 k e∈ B i)
def a5d (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)) (v:Fin k):ℕ :=
  (Q.filter (fun e=>(v= e.1∨ v= e.2)∧ b61 par B i e v)).card
def w9 (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)):ℕ :=
  (Q.filter (fun e=>c6 k e∈ B i∧ ¬ (i≠ 0∧ c6 k e∈ B (par i)))).card
def a04 (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)):ℤ :=
  w3 rows (Q.filter (fun e=>c6 k e∈ B i)) -
    w3 rows (Q.filter (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i)))
def r9 (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)):ℕ :=
  (a04 rows par B i Q+ 2* (rows.length:ℤ)).toNat
def b9 (U:Finset (Fin (t+1))):Finset (Fin k × Fin k) :=
  E.filter (fun e=>∃ a∈ U,c6 k e∈ B a)
def m0 (U:Finset (Fin (t+1))) (Q:Finset (Fin k × Fin k)) (v:Fin k):ℕ :=
  ∑ a∈ U,a5d par B a Q v
abbrev n1 (U:Finset (Fin (t+1))) (Q:Finset (Fin k × Fin k)):Prop :=
  (∀ e∈ b9 E B U,e∈ P→ e∈ Q)∧ (∀ e∈ Q,e∉ H)∧ ∀ v:Fin k,m0 par B U Q v≤ 1
def g3 (U:Finset (Fin (t+1))) (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)):Finset (Fin k) :=
  Finset.univ.filter (fun v=>v.val∈ B i∧ m0 par B U Q v= 1)
def wIn (U:Finset (Fin (t+1))) (Q:Finset (Fin k × Fin k)):ℕ→ ℕ→ ℕ :=
  x0 (∑ a∈ U,w9 par B a Q) (∑ a∈ U,r9 rows par B a Q)
def a7e (i:Fin (t+1)) (σ:Finset (Fin k × Fin k)) (τ:Finset (Fin k)):ℕ→ ℕ→ ℕ :=
  if σ⊆ b9 E B {i}∧ n1 E P H par B {i} σ∧ g3 par B {i} i σ= τ then
    wIn rows par B {i} σ else 0
def msg (tabj : Finset (Fin k × Fin k) → Finset (Fin k) → ℕ → ℕ → ℕ) (i j : Fin (t+1))
    (σ':Finset (Fin k × Fin k)) (τ':Finset (Fin k)):ℕ→ ℕ→ ℕ :=
  ∑ σj ∈ (sig B j E).powerset, ∑ τj ∈ (Finset.univ.filter (fun v : Fin k => v.val ∈ B j)).powerset,
    if sig B i σj= σ'∧ τj.filter (fun v=>v.val∈ B i)= τ' then tabj σj τj else 0
def a54 (tabj : Finset (Fin k × Fin k) → Finset (Fin k) → ℕ → ℕ → ℕ) (i j : Fin (t+1))
    (acc:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ→ ℕ→ ℕ) :
    Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ→ ℕ→ ℕ:=fun σ τ =>
  ∑ τ1∈ τ.powerset,j1 (acc σ τ1) (msg E B tabj i j (sig B j σ) (τ \ τ1))
def k8 (i:Fin (t+1)):List (Fin (t+1)) :=
  (List.finRange (t+1)).filter (fun j=>decide (i< j∧ par j= i))
def a1i:ℕ→ Fin (t+1)→ Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ→ ℕ→ ℕ
  | 0,i=>a7e E P H rows par B i
  | n+1,i=>(k8 par i).foldl (fun acc j=>a54 E B (a1i n j) i j acc)
      (a7e E P H rows par B i)
def p3:ℕ→ ℕ→ ℕ :=
  ∑ σ ∈ (sig B 0 E).powerset, ∑ τ ∈ (Finset.univ.filter (fun v : Fin k => v.val ∈ B 0)).powerset,
    a1i E P H rows par B (t+1) 0 σ τ
def t0 (s j:ℕ):ℕ :=
  if P⊆ E then p3 E P H rows par B s (j+ 2* rows.length* (t+1) - k6 rows) else 0
end DP
end asmP1
section asmP2
open Finset
section DP2
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
def k0 (i:Fin (t+1)):Finset (Fin (t+1)) :=
  Finset.univ.filter (fun j=>(List.range (t+1)).any (fun d=>decide (par^[d] j= i))= true)
def Sem (U : Finset (Fin (t+1))) (i : Fin (t+1)) (σ : Finset (Fin k × Fin k))
    (τ:Finset (Fin k)):ℕ→ ℕ→ ℕ :=
  ∑ Q ∈ (b9 E B U).powerset,
    if n1 E P H par B U Q∧ sig B i Q= σ∧ g3 par B U i Q= τ then wIn rows par B U Q else 0
end DP2
section L2
variable {t:ℕ} (par:Fin (t+1)→ Fin (t+1))
lemma a0m (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) :
    ∀ m (x:Fin (t+1)),x.val≤ m→ par^[m] x= 0:=by
  intro m
  induction m with
  | zero =>
    intro x hx
    simp only [Function.iterate_zero,id_eq]
    exact Fin.ext (by rw [Fin.val_zero]; omega)
  | succ m ih =>
    intro x hx
    rw [Function.iterate_succ_apply]
    apply ih
    by_cases h:x= 0
    · subst h; rw [hpar0]; simp
    · have:=Fin.lt_def.mp (hpar x h); omega
lemma o0 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (i m:Fin (t+1)) :
    m∈ k0 par i↔ ∃ d,par^[d] m= i:=by
  unfold k0
  rw [Finset.mem_filter,List.any_eq_true]
  constructor
  · rintro ⟨-,d,-,hd⟩; exact ⟨d,of_decide_eq_true hd⟩
  · rintro ⟨d, hd⟩
    refine ⟨Finset.mem_univ _,?_⟩
    by_cases hdt:d< t+1
    · exact ⟨d,List.mem_range.mpr hdt,decide_eq_true hd⟩
    · refine ⟨t, List.mem_range.mpr (by omega), decide_eq_true ?_⟩
      have h1:=a0m par hpar hpar0 d m (by have:=m.isLt; omega)
      have h2:=a0m par hpar hpar0 t m (by have:=m.isLt; omega)
      rw [h2,← hd,h1]
lemma a2r (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (i:Fin (t+1)) :
    i∈ k0 par i:=(o0 par hpar hpar0 i i).mpr ⟨0,rfl⟩
lemma b1e (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (j m:Fin (t+1))
    (h:m∈ k0 par j):j≤ m:=by
  obtain ⟨d,hd⟩:=(o0 par hpar hpar0 j m).mp h
  rw [← hd]; exact a56 par hpar hpar0 d m
lemma a6n (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (i j m:Fin (t+1))
    (hm:m∈ k0 par j) (hj:j∈ k0 par i):m∈ k0 par i:=by
  obtain ⟨d1,hd1⟩:=(o0 par hpar hpar0 j m).mp hm
  obtain ⟨d2,hd2⟩:=(o0 par hpar hpar0 i j).mp hj
  refine (o0 par hpar hpar0 i m).mpr ⟨d2+ d1,?_⟩
  rw [Function.iterate_add_apply,hd1,hd2]
lemma a30 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (i j:Fin (t+1))
    (hj:par j= i):j∈ k0 par i :=
  (o0 par hpar hpar0 i j).mpr ⟨1,by simpa using hj⟩
lemma a5l (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (i m:Fin (t+1))
    (hm:m∈ k0 par i):m= i∨ ∃ j,i< j∧ par j= i∧ m∈ k0 par j:=by
  obtain ⟨d,hd⟩:=(o0 par hpar hpar0 i m).mp hm
  induction d generalizing i with
  | zero=>left; simpa using hd
  | succ d ih =>
    rw [Function.iterate_succ_apply'] at hd
    by_cases hj0:par^[d] m= 0
    · rw [hj0, hpar0] at hd
      subst hd
      exact ih 0 (by rw [o0 par hpar hpar0]; exact ⟨d,hj0⟩) hj0
    · right
      refine ⟨par^[d] m,?_,hd,(o0 par hpar hpar0 _ m).mpr ⟨d,rfl⟩⟩
      rw [← hd]; exact hpar _ hj0
lemma a8h (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) (i j j':Fin (t+1))
    (hij:i< j) (hj:par j= i) (hij':i< j') (hj':par j'= i) (hne:j≠ j') :
    Disjoint (k0 par j) (k0 par j'):=by
  rw [Finset.disjoint_left]
  intro m hm hm'
  obtain ⟨d,hd⟩:=(o0 par hpar hpar0 j m).mp hm
  obtain ⟨d',hd'⟩:=(o0 par hpar hpar0 j' m).mp hm'
  have key:∀ (a b:Fin (t+1)) (da db:ℕ),i< a→ par a= i→ i< b→ a≠ b →
      par^[da] m= a→ par^[db] m= b→ da≤ db→ False:=by
    intro a b da db ha hpa hb hab hda hdb hle
    have:par^[db - da] a= b:=by
      rw [← hda,← Function.iterate_add_apply]; rw [← hdb]; congr 1; omega
    cases hc:db - da with
    | zero=>rw [hc] at this; exact hab (by simpa using this)
    | succ c =>
      rw [hc,Function.iterate_succ_apply,hpa] at this
      have:=a56 par hpar hpar0 c i
      rw [‹par^[c] i= b›] at this
      exact absurd hb (not_lt.mpr this)
  by_cases hle:d≤ d'
  · exact key j j' d d' hij hj hij' hne hd hd' hle
  · exact key j' j d' d hij' hj' hij (Ne.symm hne) hd' hd (by omega)
lemma b4x (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0) :
    k0 par 0= Finset.univ:=by
  ext m
  simp only [Finset.mem_univ,iff_true]
  exact (o0 par hpar hpar0 0 m).mpr ⟨m.val,a0m par hpar hpar0 _ m le_rfl⟩
lemma a7d (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    {T:Fin (t+1)→ Prop} {top:Fin (t+1)} (htop:p9 par T top)
    (i j a b:Fin (t+1)) (hj:par j= i) (ha:a∉ k0 par j) (hb:b∈ k0 par j)
    (hTa:T a) (hTb:T b):T j∧ T i:=by
  obtain ⟨dj,hdj⟩:=(o0 par hpar hpar0 j b).mp hb
  obtain ⟨db,hdb,hpath⟩:=b0t par hpar htop b.val b rfl hTb
  obtain ⟨da,hda,-⟩:=b0t par hpar htop a.val a rfl hTa
  by_cases hle:db≤ dj
  · exfalso; apply ha
    refine (o0 par hpar hpar0 j a).mpr ⟨(dj - db)+ da,?_⟩
    rw [Function.iterate_add_apply,hda,← hdb,← Function.iterate_add_apply]
    rw [← hdj]; congr 1; omega
  · have h1 := hpath dj (by omega)
    have h2:=hpath (dj+ 1) (by omega)
    rw [hdj] at h1
    rw [Function.iterate_succ_apply',hdj,hj] at h2
    exact ⟨h1,h2⟩
end L2
lemma a4p {α M:Type*} [DecidableEq α] [AddCommMonoid M] (A C:Finset α)
    (F:Finset α→ M) :
    ∑ Q ∈ (A ∪ C).powerset, F Q =
      ∑ Q1∈ A.powerset,∑ Q2∈ C.powerset,if Q1∩ C= Q2∩ A then F (Q1∪ Q2) else 0:=by
  have h1:(∑ Q1∈ A.powerset,∑ Q2∈ C.powerset,if Q1∩ C= Q2∩ A then F (Q1∪ Q2) else 0) =
      ∑ p∈ (A.powerset ×ˢ C.powerset).filter (fun p=>p.1∩ C= p.2∩ A),F (p.1∪ p.2):=by
    rw [Finset.sum_filter,Finset.sum_product]
  rw [h1]
  symm
  refine Finset.sum_bij' (fun p _=>p.1∪ p.2) (fun Q _=>(Q∩ A,Q∩ C)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨Q1, Q2⟩ hp
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_powerset] at hp ⊢
    exact Finset.union_subset_union hp.1.1 hp.1.2
  · intro Q hQ
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_powerset] at hQ ⊢
    refine ⟨⟨Finset.inter_subset_right,Finset.inter_subset_right⟩,?_⟩
    rw [Finset.inter_assoc,Finset.inter_assoc,Finset.inter_comm A C]
  · rintro ⟨Q1, Q2⟩ hp
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_powerset] at hp
    obtain ⟨⟨h1,h2⟩,hc⟩:=hp
    simp only [Prod.mk.injEq]
    constructor
    · ext x; simp only [Finset.mem_inter, Finset.mem_union]
      have:=Finset.ext_iff.mp hc x; simp only [Finset.mem_inter] at this
      have:=@h1 x; have:=@h2 x; tauto
    · ext x; simp only [Finset.mem_inter, Finset.mem_union]
      have:=Finset.ext_iff.mp hc x; simp only [Finset.mem_inter] at this
      have:=@h1 x; have:=@h2 x; tauto
  · intro Q hQ
    simp only [Finset.mem_powerset] at hQ
    ext x; simp only [Finset.mem_union,Finset.mem_inter]
    have:=@hQ x; simp only [Finset.mem_union] at this; tauto
  · intro p hp; rfl
section L3
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
lemma l0 (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)) (e:Fin k × Fin k) :
    e∈ sig B i Q↔ e∈ Q∧ c6 k e∈ B i:=Finset.mem_filter
lemma f8 (U:Finset (Fin (t+1))) (e:Fin k × Fin k) :
    e∈ b9 E B U↔ e∈ E∧ ∃ a∈ U,c6 k e∈ B a:=Finset.mem_filter
lemma k3 (U:Finset (Fin (t+1))) (i:Fin (t+1)) (Q:Finset (Fin k × Fin k))
    (v:Fin k):v∈ g3 par B U i Q↔ v.val∈ B i∧ m0 par B U Q v= 1:=by
  simp [g3]
lemma a0c (U D:Finset (Fin (t+1))) :
    b9 E B (U∪ D)= b9 E B U∪ b9 E B D:=by
  ext e; simp only [f8,Finset.mem_union]
  constructor
  · rintro ⟨he, a, ha | ha, hb⟩
    · exact Or.inl ⟨he,a,ha,hb⟩
    · exact Or.inr ⟨he,a,ha,hb⟩
  · rintro (⟨he, a, ha, hb⟩ | ⟨he, a, ha, hb⟩)
    · exact ⟨he,a,Or.inl ha,hb⟩
    · exact ⟨he,a,Or.inr ha,hb⟩
lemma o5 (U D:Finset (Fin (t+1))) (Q1 Q2:Finset (Fin k × Fin k))
    (hQ2:Q2⊆ b9 E B D) (hc:Q1∩ b9 E B D= Q2∩ b9 E B U)
    (a:Fin (t+1)) (ha:a∈ U) (p:Fin k × Fin k→ Prop) [DecidablePred p]
    (hp:∀ e,p e→ c6 k e∈ B a):(Q1∪ Q2).filter p= Q1.filter p:=by
  ext e
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨h | h, hpe⟩
    · exact ⟨h,hpe⟩
    · refine ⟨?_, hpe⟩
      have hA:e∈ b9 E B U :=
        (f8 E B U e).mpr ⟨((f8 E B D e).mp (hQ2 h)).1,a,ha,hp e hpe⟩
      have:e∈ Q2∩ b9 E B U:=Finset.mem_inter.mpr ⟨h,hA⟩
      rw [← hc] at this; exact (Finset.mem_inter.mp this).1
  · rintro ⟨h,hpe⟩; exact ⟨Or.inl h,hpe⟩
lemma u0 (U D:Finset (Fin (t+1))) (Q1 Q2:Finset (Fin k × Fin k))
    (hQ1:Q1⊆ b9 E B U) (hc:Q1∩ b9 E B D= Q2∩ b9 E B U)
    (b:Fin (t+1)) (hb:b∈ D) (p:Fin k × Fin k→ Prop) [DecidablePred p]
    (hp:∀ e,p e→ c6 k e∈ B b):(Q1∪ Q2).filter p= Q2.filter p:=by
  ext e
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨h | h, hpe⟩
    · refine ⟨?_, hpe⟩
      have hC:e∈ b9 E B D :=
        (f8 E B D e).mpr ⟨((f8 E B U e).mp (hQ1 h)).1,b,hb,hp e hpe⟩
      have:e∈ Q1∩ b9 E B D:=Finset.mem_inter.mpr ⟨h,hC⟩
      rw [hc] at this; exact (Finset.mem_inter.mp this).1
    · exact ⟨h,hpe⟩
  · rintro ⟨h,hpe⟩; exact ⟨Or.inr h,hpe⟩
lemma a5m (U D:Finset (Fin (t+1))) (hdisj:Disjoint U D)
    (Q1 Q2:Finset (Fin k × Fin k)) (hQ1:Q1⊆ b9 E B U) (hQ2:Q2⊆ b9 E B D)
    (hc:Q1∩ b9 E B D= Q2∩ b9 E B U) (v:Fin k) :
    m0 par B (U∪ D) (Q1∪ Q2) v= m0 par B U Q1 v+ m0 par B D Q2 v:=by
  unfold m0
  rw [Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    unfold a5d
    rw [o5 E B U D Q1 Q2 hQ2 hc a ha _ (fun e h=>h.2.1)]
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    unfold a5d
    rw [u0 E B U D Q1 Q2 hQ1 hc b hb _ (fun e h=>h.2.1)]
lemma b3k (U D:Finset (Fin (t+1))) (hdisj:Disjoint U D)
    (Q1 Q2:Finset (Fin k × Fin k)) (hQ1:Q1⊆ b9 E B U) (hQ2:Q2⊆ b9 E B D)
    (hc:Q1∩ b9 E B D= Q2∩ b9 E B U) :
    wIn rows par B (U∪ D) (Q1∪ Q2)= j1 (wIn rows par B U Q1) (wIn rows par B D Q2):=by
  unfold wIn
  rw [a8v,Finset.sum_union hdisj,Finset.sum_union hdisj]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl (fun a ha => ?_)
      unfold w9
      rw [o5 E B U D Q1 Q2 hQ2 hc a ha _ (fun e h=>h.1)]
    · refine Finset.sum_congr rfl (fun b hb => ?_)
      unfold w9
      rw [u0 E B U D Q1 Q2 hQ1 hc b hb _ (fun e h=>h.1)]
  · congr 1
    · refine Finset.sum_congr rfl (fun a ha => ?_)
      unfold r9 a04
      rw [o5 E B U D Q1 Q2 hQ2 hc a ha _ (fun e h=>h),
        o5 E B U D Q1 Q2 hQ2 hc a ha _ (fun e h=>h.1)]
    · refine Finset.sum_congr rfl (fun b hb => ?_)
      unfold r9 a04
      rw [u0 E B U D Q1 Q2 hQ1 hc b hb _ (fun e h=>h),
        u0 E B U D Q1 Q2 hQ1 hc b hb _ (fun e h=>h.1)]
lemma a4b (U:Finset (Fin (t+1))) (Q:Finset (Fin k × Fin k)) (v:Fin k)
    (h:m0 par B U Q v≠ 0):∃ a∈ U,v.val∈ B a:=by
  unfold m0 at h
  obtain ⟨a,ha,hne⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
  unfold a5d at hne
  obtain ⟨e,he⟩:=Finset.card_ne_zero.mp hne
  exact ⟨a,ha,(Finset.mem_filter.mp he).2.2.2.1⟩
lemma b4n (U D:Finset (Fin (t+1))) (i j:Fin (t+1)) (hi:i∈ U) (hj:j∈ D)
    (hdisj:Disjoint U D)
    (hsep:∀ x:ℕ,∀ a∈ U,∀ b∈ D,x∈ B a→ x∈ B b→ x∈ B i∧ x∈ B j)
    (Q1 Q2:Finset (Fin k × Fin k)) (hQ1:Q1⊆ b9 E B U) (hQ2:Q2⊆ b9 E B D)
    (σ:Finset (Fin k × Fin k)) (τ:Finset (Fin k)) :
    ((n1 E P H par B U Q1∧ sig B i Q1= σ∧ g3 par B U i Q1∈ τ.powerset) ∧
      (n1 E P H par B D Q2∧ sig B i (sig B j Q2)= sig B j σ ∧
        (g3 par B D j Q2).filter (fun v=>v.val∈ B i)= τ \ g3 par B U i Q1)) ↔
    (Q1∩ b9 E B D= Q2∩ b9 E B U ∧
      (n1 E P H par B (U∪ D) (Q1∪ Q2)∧ sig B i (Q1∪ Q2)= σ ∧
        g3 par B (U∪ D) i (Q1∪ Q2)= τ)):=by
  have K1:∀ e,e∈ b9 E B U→ e∈ b9 E B D →
      c6 k e∈ B i∧ c6 k e∈ B j:=by
    intro e hA hC
    obtain ⟨-,a,ha,hta⟩:=(f8 E B U e).mp hA
    obtain ⟨-,b,hb,htb⟩:=(f8 E B D e).mp hC
    exact hsep _ a ha b hb hta htb
  have hEC:∀ e,e∈ E→ c6 k e∈ B j→ e∈ b9 E B D :=
    fun e he h=>(f8 E B D e).mpr ⟨he,j,hj,h⟩
  have hQ1E:∀ e∈ Q1,e∈ E:=fun e he=>((f8 E B U e).mp (hQ1 he)).1
  have N1:∀ v:Fin k,m0 par B U Q1 v≠ 0→ m0 par B D Q2 v≠ 0 →
      v.val∈ B i∧ v.val∈ B j:=by
    intro v h1 h2
    obtain ⟨a,ha,hva⟩:=a4b par B U Q1 v h1
    obtain ⟨b,hb,hvb⟩:=a4b par B D Q2 v h2
    exact hsep _ a ha b hb hva hvb
  have N2:∀ v:Fin k,v.val∈ B i→ m0 par B D Q2 v≠ 0→ v.val∈ B j:=by
    intro v hv h2
    obtain ⟨b,hb,hvb⟩:=a4b par B D Q2 v h2
    exact (hsep _ i hi b hb hv hvb).2
  constructor
  · rintro ⟨⟨⟨P1, H1, C1⟩, hs1, ht1⟩, ⟨P2, H2, C2⟩, hs2, ht2⟩
    have hc:Q1∩ b9 E B D= Q2∩ b9 E B U:=by
      ext e
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨he1, heC⟩
        have ht:=K1 e (hQ1 he1) heC
        have h3:e∈ sig B j σ:=by
          rw [l0,← hs1,l0]; exact ⟨⟨he1,ht.1⟩,ht.2⟩
        rw [← hs2,l0,l0] at h3
        exact ⟨h3.1.1,hQ1 he1⟩
      · rintro ⟨he2, heA⟩
        have ht:=K1 e heA (hQ2 he2)
        have h3:e∈ sig B i (sig B j Q2):=by
          rw [l0,l0]; exact ⟨⟨he2,ht.2⟩,ht.1⟩
        rw [hs2,l0,← hs1,l0] at h3
        exact ⟨h3.1.1,hQ2 he2⟩
    have hcnt:=a5m E par B U D hdisj Q1 Q2 hQ1 hQ2 hc
    have hnot:∀ v,m0 par B U Q1 v≠ 0→ m0 par B D Q2 v≠ 0→ False:=by
      intro v h1 h2
      obtain ⟨hvi,hvj⟩:=N1 v h1 h2
      have hv1:v∈ g3 par B U i Q1 :=
        (k3 par B U i Q1 v).mpr ⟨hvi,by have:=C1 v; omega⟩
      have hv2:v∈ (g3 par B D j Q2).filter (fun v=>v.val∈ B i) :=
        Finset.mem_filter.mpr ⟨(k3 par B D j Q2 v).mpr ⟨hvj,by have:=C2 v; omega⟩,hvi⟩
      rw [ht2,Finset.mem_sdiff] at hv2
      exact hv2.2 hv1
    refine ⟨hc,⟨?_,?_,?_⟩,?_,?_⟩
    · intro e he hP
      rw [a0c,Finset.mem_union] at he
      rcases he with he | he
      · exact Finset.mem_union_left _ (P1 e he hP)
      · exact Finset.mem_union_right _ (P2 e he hP)
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact H1 e he
      · exact H2 e he
    · intro v
      rw [hcnt]
      have:=C1 v; have:=C2 v
      by_cases h1:m0 par B U Q1 v= 0
      · omega
      · by_cases h2 : m0 par B D Q2 v = 0
        · omega
        · exact (hnot v h1 h2).elim
    · unfold sig
      rw [o5 E B U D Q1 Q2 hQ2 hc i hi _ (fun e h=>h)]
      exact hs1
    · ext v
      rw [k3,hcnt]
      have c1le:=C1 v; have c2le:=C2 v; have hn:=hnot v
      constructor
      · rintro ⟨hvi, hsum⟩
        by_cases h1:m0 par B U Q1 v= 1
        · exact Finset.mem_powerset.mp ht1 ((k3 par B U i Q1 v).mpr ⟨hvi,h1⟩)
        · have h2 : m0 par B D Q2 v = 1 := by omega
          have hvj:=N2 v hvi (by omega)
          have:v∈ (g3 par B D j Q2).filter (fun v=>v.val∈ B i) :=
            Finset.mem_filter.mpr ⟨(k3 par B D j Q2 v).mpr ⟨hvj,h2⟩,hvi⟩
          rw [ht2] at this; exact (Finset.mem_sdiff.mp this).1
      · intro hv
        by_cases hvt:v∈ g3 par B U i Q1
        · obtain ⟨hvi, h1⟩ := (k3 par B U i Q1 v).mp hvt
          refine ⟨hvi,?_⟩
          have:m0 par B D Q2 v= 0:=by
            by_contra h2; exact hn (by omega) h2
          omega
        · have : v ∈ τ \ g3 par B U i Q1 := Finset.mem_sdiff.mpr ⟨hv, hvt⟩
          rw [← ht2,Finset.mem_filter,k3] at this
          obtain ⟨⟨-,h2⟩,hvi⟩:=this
          refine ⟨hvi,?_⟩
          have:m0 par B U Q1 v≠ 1:=fun h1 =>
            hvt ((k3 par B U i Q1 v).mpr ⟨hvi,h1⟩)
          omega
  · rintro ⟨hc, ⟨P', H', C'⟩, hs, ht⟩
    have hcnt:=a5m E par B U D hdisj Q1 Q2 hQ1 hQ2 hc
    refine ⟨⟨⟨?_,?_,?_⟩,?_,?_⟩,⟨?_,?_,?_⟩,?_,?_⟩
    · intro e he hP
      have:=P' e (by rw [a0c]; exact Finset.mem_union_left _ he) hP
      rcases Finset.mem_union.mp this with h | h
      · exact h
      · have : e ∈ Q2 ∩ b9 E B U := Finset.mem_inter.mpr ⟨h, he⟩
        rw [← hc] at this; exact (Finset.mem_inter.mp this).1
    · intro e he; exact H' e (Finset.mem_union_left _ he)
    · intro v; have:=C' v; rw [hcnt] at this; omega
    · rw [← hs]; unfold sig
      rw [o5 E B U D Q1 Q2 hQ2 hc i hi _ (fun e h=>h)]
    · rw [Finset.mem_powerset]; intro v hv
      rw [← ht,k3,hcnt]
      obtain ⟨hvi,h1⟩:=(k3 par B U i Q1 v).mp hv
      have:=C' v; rw [hcnt] at this
      exact ⟨hvi,by omega⟩
    · intro e he hP
      have:=P' e (by rw [a0c]; exact Finset.mem_union_right _ he) hP
      rcases Finset.mem_union.mp this with h | h
      · have : e ∈ Q1 ∩ b9 E B D := Finset.mem_inter.mpr ⟨h, he⟩
        rw [hc] at this; exact (Finset.mem_inter.mp this).1
      · exact h
    · intro e he; exact H' e (Finset.mem_union_right _ he)
    · intro v; have:=C' v; rw [hcnt] at this; omega
    · ext e
      rw [l0,l0,l0,← hs,l0,Finset.mem_union]
      constructor
      · rintro ⟨⟨he2,hj'⟩,hi'⟩; exact ⟨⟨Or.inr he2,hi'⟩,hj'⟩
      · rintro ⟨⟨he1 | he2, hi'⟩, hj'⟩
        · have:e∈ Q1∩ b9 E B D :=
            Finset.mem_inter.mpr ⟨he1,hEC e (hQ1E e he1) hj'⟩
          rw [hc] at this; exact ⟨⟨(Finset.mem_inter.mp this).1,hj'⟩,hi'⟩
        · exact ⟨⟨he2,hj'⟩,hi'⟩
    · ext v
      rw [Finset.mem_filter,k3,Finset.mem_sdiff,← ht,k3,k3,hcnt]
      have:=C' v; rw [hcnt] at this
      constructor
      · rintro ⟨⟨hvj, h2⟩, hvi⟩
        exact ⟨⟨hvi,by omega⟩,fun h=>by have:=h.2; omega⟩
      · rintro ⟨⟨hvi, hsum⟩, hn1⟩
        have h1:m0 par B U Q1 v≠ 1:=fun h=>hn1 ⟨hvi,h⟩
        have h2:m0 par B D Q2 v= 1:=by omega
        exact ⟨⟨N2 v hvi (by omega),h2⟩,hvi⟩
lemma b8c (D:Finset (Fin (t+1))) (i j:Fin (t+1)) (σ':Finset (Fin k × Fin k))
    (τ':Finset (Fin k)) :
    msg E B (Sem E P H rows par B D j) i j σ' τ' =
      ∑ Q ∈ (b9 E B D).powerset, if n1 E P H par B D Q ∧ sig B i (sig B j Q) = σ' ∧
        (g3 par B D j Q).filter (fun v=>v.val∈ B i)= τ' then wIn rows par B D Q else 0:=by
  unfold msg Sem
  have h1:∀ σj τj,(if sig B i σj= σ'∧ τj.filter (fun v=>v.val∈ B i)= τ' then
      ∑ Q ∈ (b9 E B D).powerset, (if n1 E P H par B D Q ∧ sig B j Q = σj ∧
        g3 par B D j Q= τj then wIn rows par B D Q else 0) else 0) =
      ∑ Q ∈ (b9 E B D).powerset, if (n1 E P H par B D Q ∧ sig B i (sig B j Q) = σ' ∧
        (g3 par B D j Q).filter (fun v=>v.val∈ B i)= τ') ∧
          (sig B j Q= σj∧ g3 par B D j Q= τj) then wIn rows par B D Q else 0:=by
    intro σj τj
    split_ifs with hc
    · refine Finset.sum_congr rfl (fun Q _ => ?_)
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨ho,hs,ht⟩; subst hs; subst ht; exact ⟨⟨ho,hc.1,hc.2⟩,rfl,rfl⟩
      · rintro ⟨⟨ho,-,-⟩,hs,ht⟩; exact ⟨ho,hs,ht⟩
    · symm; apply Finset.sum_eq_zero; intro Q _
      rw [if_neg]; rintro ⟨⟨-,hs',ht'⟩,hs,ht⟩; subst hs; subst ht; exact hc ⟨hs',ht'⟩
  simp only [h1]
  rw [Finset.sum_congr rfl (fun σj _=>Finset.sum_comm),Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Q hQ=>?_)
  rw [Finset.sum_eq_single (sig B j Q),Finset.sum_eq_single (g3 par B D j Q)]
  · exact if_congr ⟨fun h=>h.1,fun h=>⟨h,rfl,rfl⟩⟩ rfl rfl
  · intro τj _ hne; rw [if_neg (fun h=>hne h.2.2.symm)]
  · intro hn; exfalso; apply hn
    rw [Finset.mem_powerset]; intro v hv
    rw [k3] at hv; simp [hv.1]
  · intro σj _ hne; apply Finset.sum_eq_zero; intro τj _
    rw [if_neg (fun h=>hne h.2.1.symm)]
  · intro hn; exfalso; apply hn
    rw [Finset.mem_powerset]; intro e he
    rw [l0] at he ⊢
    exact ⟨((f8 E B D e).mp (Finset.mem_powerset.mp hQ he.1)).1,he.2⟩
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
lemma a6l (U D:Finset (Fin (t+1))) (i j:Fin (t+1)) (hi:i∈ U) (hj:j∈ D)
    (hdisj:Disjoint U D)
    (hsep:∀ x:ℕ,∀ a∈ U,∀ b∈ D,x∈ B a→ x∈ B b→ x∈ B i∧ x∈ B j) :
    a54 E B (Sem E P H rows par B D j) i j (Sem E P H rows par B U i) =
      Sem E P H rows par B (U∪ D) i:=by
  funext σ τ
  unfold a54
  simp only [b8c]
  have L:(∑ τ1∈ τ.powerset,j1 (Sem E P H rows par B U i σ τ1)
      (∑ Q2∈ (b9 E B D).powerset,if n1 E P H par B D Q2 ∧
        sig B i (sig B j Q2)= sig B j σ ∧
        (g3 par B D j Q2).filter (fun v=>v.val∈ B i)= τ \ τ1 then
          wIn rows par B D Q2 else 0)) =
      ∑ Q1 ∈ (b9 E B U).powerset, ∑ Q2 ∈ (b9 E B D).powerset,
        if ((n1 E P H par B U Q1∧ sig B i Q1= σ∧ g3 par B U i Q1∈ τ.powerset) ∧
          (n1 E P H par B D Q2∧ sig B i (sig B j Q2)= sig B j σ ∧
            (g3 par B D j Q2).filter (fun v=>v.val∈ B i)= τ \ g3 par B U i Q1)) then
          j1 (wIn rows par B U Q1) (wIn rows par B D Q2) else 0:=by
    unfold Sem
    simp only [a1h]
    simp only [a0v]
    simp only [b5p]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Q1 _=>?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Q2 _=>?_)
    have hterm:∀ τ1∈ τ.powerset,
        (if (n1 E P H par B U Q1∧ sig B i Q1= σ∧ g3 par B U i Q1= τ1) ∧
          (n1 E P H par B D Q2∧ sig B i (sig B j Q2)= sig B j σ ∧
            (g3 par B D j Q2).filter (fun v=>v.val∈ B i)= τ \ τ1) then
          j1 (wIn rows par B U Q1) (wIn rows par B D Q2) else 0) =
        if g3 par B U i Q1= τ1 then
          (if (n1 E P H par B U Q1∧ sig B i Q1= σ) ∧
            (n1 E P H par B D Q2∧ sig B i (sig B j Q2)= sig B j σ ∧
              (g3 par B D j Q2).filter (fun v=>v.val∈ B i)= τ \ g3 par B U i Q1) then
            j1 (wIn rows par B U Q1) (wIn rows par B D Q2) else 0) else 0:=by
      intro τ1 _
      by_cases h:g3 par B U i Q1= τ1
      · subst h; rw [if_pos rfl]
        exact if_congr ⟨fun h=>⟨⟨h.1.1,h.1.2.1⟩,h.2⟩,fun h=>⟨⟨h.1.1,h.1.2,rfl⟩,h.2⟩⟩
          rfl rfl
      · rw [if_neg h,if_neg (fun h'=>h h'.1.2.2)]
    rw [Finset.sum_congr rfl hterm,Finset.sum_ite_eq]
    by_cases hsub:g3 par B U i Q1∈ τ.powerset
    · rw [if_pos hsub]
      exact if_congr ⟨fun h=>⟨⟨h.1.1,h.1.2,hsub⟩,h.2⟩,fun h=>⟨⟨h.1.1,h.1.2.1⟩,h.2⟩⟩
        rfl rfl
    · rw [if_neg hsub,if_neg (fun h=>hsub h.1.2.2)]
  rw [L]
  unfold Sem
  have hpow:(b9 E B (U∪ D)).powerset= (b9 E B U∪ b9 E B D).powerset:=by
    rw [a0c]
  rw [hpow,a4p]
  beta_reduce
  refine Finset.sum_congr rfl (fun Q1 hQ1=>Finset.sum_congr rfl (fun Q2 hQ2=>?_))
  rw [Finset.mem_powerset] at hQ1 hQ2
  rw [← ite_and]
  have hiff:=b4n E P H par B U D i j hi hj hdisj hsep Q1 Q2 hQ1 hQ2 σ τ
  by_cases hX:(n1 E P H par B U Q1∧ sig B i Q1= σ∧ g3 par B U i Q1∈ τ.powerset) ∧
      (n1 E P H par B D Q2∧ sig B i (sig B j Q2)= sig B j σ ∧
        (g3 par B D j Q2).filter (fun v=>v.val∈ B i)= τ \ g3 par B U i Q1)
  · rw [if_pos hX,if_pos (hiff.mp hX),
      b3k E rows par B U D hdisj Q1 Q2 hQ1 hQ2 (hiff.mp hX).1]
  · rw [if_neg hX,if_neg (fun h=>hX (hiff.mpr h))]
lemma b0k (i:Fin (t+1)):Sem E P H rows par B {i} i= a7e E P H rows par B i:=by
  funext σ τ
  unfold Sem a7e
  have hsig:∀ Q∈ (b9 E B {i}).powerset,sig B i Q= Q:=by
    intro Q hQ
    ext e
    rw [l0]
    constructor
    · exact fun h=>h.1
    · intro he
      refine ⟨he,?_⟩
      obtain ⟨-,a,ha,hta⟩:=(f8 E B {i} e).mp (Finset.mem_powerset.mp hQ he)
      rw [Finset.mem_singleton] at ha; subst ha; exact hta
  have hterm:∀ Q∈ (b9 E B {i}).powerset,
      (if n1 E P H par B {i} Q∧ sig B i Q= σ∧ g3 par B {i} i Q= τ then
        wIn rows par B {i} Q else 0) =
      if σ= Q then (if n1 E P H par B {i} Q∧ g3 par B {i} i Q= τ then
        wIn rows par B {i} Q else 0) else 0:=by
    intro Q hQ
    rw [hsig Q hQ]
    by_cases h:σ= Q
    · subst h; rw [if_pos rfl]
      exact if_congr ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,rfl,h.2⟩⟩ rfl rfl
    · rw [if_neg h,if_neg (fun h'=>h h'.2.1.symm)]
  rw [Finset.sum_congr rfl hterm,Finset.sum_ite_eq]
  by_cases h1:σ∈ (b9 E B {i}).powerset
  · rw [if_pos h1]
    exact if_congr ⟨fun h=>⟨Finset.mem_powerset.mp h1,h⟩,fun h=>h.2⟩ rfl rfl
  · rw [if_neg h1,if_neg (fun h=>h1 (Finset.mem_powerset.mpr h.1))]
lemma v9 (i j:Fin (t+1)):j∈ k8 par i↔ i< j∧ par j= i:=by
  simp [k8]
lemma b5k (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconn:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top) (i:Fin (t+1))
    (tabj:Fin (t+1)→ (Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ→ ℕ→ ℕ))
    (htab:∀ j,i< j→ par j= i→ tabj j= Sem E P H rows par B (k0 par j) j) :
    ∀ (l : List (Fin (t+1))) (U : Finset (Fin (t+1))), l.Nodup → (∀ j ∈ l, i < j ∧ par j = i) →
      i∈ U→ (∀ j∈ l,Disjoint U (k0 par j)) →
      l.foldl (fun acc j=>a54 E B (tabj j) i j acc) (Sem E P H rows par B U i) =
        Sem E P H rows par B (U∪ l.toFinset.biUnion (k0 par)) i:=by
  intro l
  induction l with
  | nil=>intro U _ _ _ _; simp
  | cons j l ih =>
    intro U hnd hl hiU hdisj
    rw [List.foldl_cons]
    have hj:=hl j (by simp)
    have hdj:Disjoint U (k0 par j):=hdisj j (by simp)
    have hsep:∀ x:ℕ,∀ a∈ U,∀ b∈ k0 par j,x∈ B a→ x∈ B b→ x∈ B i∧ x∈ B j:=by
      intro x a ha b hb hxa hxb
      obtain ⟨top,htop⟩:=hconn x a hxa
      have:=a7d par hpar hpar0 htop i j a b hj.2
        (Finset.disjoint_left.mp hdj ha) hb hxa hxb
      exact ⟨this.2,this.1⟩
    have hnd':=List.nodup_cons.mp hnd
    have hdisj':∀ j'∈ l,Disjoint (U∪ k0 par j) (k0 par j'):=by
      intro j' hj'
      rw [Finset.disjoint_union_left]
      refine ⟨hdisj j' (by simp [hj']),?_⟩
      have hj'c:=hl j' (by simp [hj'])
      exact a8h par hpar hpar0 i j j' hj.1 hj.2 hj'c.1 hj'c.2
        (fun h=>hnd'.1 (h ▸ hj'))
    rw [htab j hj.1 hj.2,a6l E P H rows par B U (k0 par j) i j hiU
      (a2r par hpar hpar0 j) hdj hsep,
      ih (U∪ k0 par j) hnd'.2 (fun j' hj'=>hl j' (by simp [hj']))
        (Finset.mem_union_left _ hiU) hdisj']
    rw [List.toFinset_cons,Finset.biUnion_insert,Finset.union_assoc]
lemma a7n (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconn:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top) :
    ∀ n (i : Fin (t+1)), t - i.val < n →
      a1i E P H rows par B n i= Sem E P H rows par B (k0 par i) i:=by
  intro n
  induction n with
  | zero=>intro i h; omega
  | succ n ih =>
    intro i hi
    rw [a1i,← b0k]
    have hnd:(k8 par i).Nodup:=List.Nodup.filter _ (List.nodup_finRange _)
    have hch:∀ j∈ k8 par i,i< j∧ par j= i:=fun j hj=>(v9 par i j).mp hj
    have hdisj:∀ j∈ k8 par i,Disjoint {i} (k0 par j):=by
      intro j hj
      rw [Finset.disjoint_singleton_left]
      intro h
      have:=b1e par hpar hpar0 j i h
      exact absurd (hch j hj).1 (not_lt.mpr this)
    have htab:∀ j,i< j→ par j= i →
        a1i E P H rows par B n j= Sem E P H rows par B (k0 par j) j:=by
      intro j hij _
      apply ih
      have:=Fin.lt_def.mp hij; have:=j.isLt; omega
    rw [b5k E P H rows par B hpar hpar0 hconn i (fun j=>a1i E P H rows par B n j) htab
      (k8 par i) {i} hnd hch (Finset.mem_singleton_self i) hdisj]
    congr 1
    ext m
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,List.mem_toFinset]
    constructor
    · rintro (rfl | ⟨j, hj, hm⟩)
      · exact a2r par hpar hpar0 m
      · exact a6n par hpar hpar0 i j m hm (a30 par hpar hpar0 i j (hch j hj).2)
    · intro hm
      rcases a5l par hpar hpar0 i m hm with h | ⟨j,hij,hpj,hmj⟩
      · exact Or.inl h
      · exact Or.inr ⟨j,(v9 par i j).mpr ⟨hij,hpj⟩,hmj⟩
end L3
section L45
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
def s4 (w:ℕ):Prop :=
  let ends:=fun e:Fin k × Fin k=>({e.1,e.2}:Finset (Fin k))
  let valid:=fun Q:Finset (Fin k × Fin k)=>Q⊆ E ∧
    ∀ e∈ Q,∀ f∈ Q,e≠ f→ Disjoint (ends e) (ends f)
  let signed:=fun Q:Finset (Fin k × Fin k) =>
    ((rows.filter (fun t=>t.2 && decide (Q⊆ t.1))).length:Int) -
      ((rows.filter (fun t=>!t.2 && decide (Q⊆ t.1))).length:Int)
  let together:=fun e f=>∃ Q,valid Q∧ e∈ Q∧ f∈ Q∧ signed Q≠ 0
  let tag:=fun e:Fin k × Fin k=>k+e.1.val*k+e.2.val
  let vertices:=(Finset.range k)∪ E.image tag
  par 0= 0∧ (∀ i,i≠ 0→ par i< i) ∧
    (∀ i,B i⊆ vertices∧ (B i).card≤ w+1) ∧
    (∀ v∈ vertices,∃ a,v∈ B a∧ ∀ i,v∈ B i→ i≠ a→ i≠ 0∧ v∈ B (par i)) ∧
    (∀ e∈ E,(∃ i,tag e∈ B i∧ e.1.val∈ B i)∧ (∃ i,tag e∈ B i∧ e.2.val∈ B i)) ∧
    ∀ e∈ E,∀ f∈ E,e≠ f→ together e f→ ∃ i,tag e∈ B i∧ tag f∈ B i
def b3i (s j:ℕ):ℕ :=
  let ends:=fun e:Fin k × Fin k=>({e.1,e.2}:Finset (Fin k))
  let valid:=fun Q:Finset (Fin k × Fin k)=>Q⊆ E ∧
    ∀ e∈ Q,∀ f∈ Q,e≠ f→ Disjoint (ends e) (ends f)
  let score:=fun Q:Finset (Fin k × Fin k)=>(rows.filter
    (fun r=>decide (decide ((Q∩ r.1).Nonempty)= r.2))).length
  (E.powerset.filter (fun Q=>valid Q∧ P⊆ Q∧ Disjoint Q H∧ Q.card= s∧ score Q= j)).card
lemma b6u (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (e:Fin k × Fin k) (v:Fin k) (hc:∃ i,c6 k e∈ B i∧ v.val∈ B i) :
    (Finset.univ.filter (fun a=>b61 par B a e v)).card= 1:=by
  obtain ⟨i0,h1,h2⟩:=hc
  have:=a0l par hpar hpar0 (fun (x:ℕ) a=>x∈ B a) {c6 k e,v.val} (by simp)
    (by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hconnX _ i0 h1
      · exact hconnX _ i0 h2)
    ⟨i0,by simp [h1,h2]⟩
  refine Eq.trans ?_ this
  congr 1
  apply Finset.filter_congr
  intro a _
  simp only [b61,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,and_assoc]
lemma b82 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (e:Fin k × Fin k) (hc:∃ i,c6 k e∈ B i) :
    (Finset.univ.filter (fun a=>c6 k e∈ B a∧ ¬ (a≠ 0∧ c6 k e∈ B (par a)))).card= 1:=by
  obtain ⟨i0,h1⟩:=hc
  have:=a0l par hpar hpar0 (fun (x:ℕ) a=>x∈ B a) {c6 k e} (by simp)
    (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx; exact hconnX _ i0 h1)
    ⟨i0,by simp [h1]⟩
  refine Eq.trans ?_ this
  congr 1
  apply Finset.filter_congr
  intro a _
  simp only [Finset.mem_singleton,forall_eq]
lemma a9y (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hinc:∀ e∈ E,(∃ i,c6 k e∈ B i∧ e.1.val∈ B i)∧ (∃ i,c6 k e∈ B i∧ e.2.val∈ B i))
    (Q:Finset (Fin k × Fin k)) (hQ:Q⊆ E) (v:Fin k) :
    m0 par B Finset.univ Q v= (Q.filter (fun e=>v= e.1∨ v= e.2)).card:=by
  unfold m0 a5d
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he=>?_)
  by_cases h:v= e.1∨ v= e.2
  · simp only [h, true_and, if_true]
    rw [← Finset.card_filter]
    apply b6u par B hpar hpar0 hconnX
    rcases h with rfl | rfl
    · exact (hinc e (hQ he)).1
    · exact (hinc e (hQ he)).2
  · simp [h]
lemma a3s (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a)
    (Q:Finset (Fin k × Fin k)) (hQ:Q⊆ E) :
    ∑ a,w9 par B a Q= Q.card:=by
  unfold w9
  simp only [Finset.card_filter]
  rw [Finset.sum_comm,Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun e he=>?_)
  rw [← Finset.card_filter]
  exact b82 par B hpar hpar0 hconnX e (hcover e (hQ he))
lemma a4q (Q:Finset (Fin k × Fin k)) :
    (∀ v:Fin k,(Q.filter (fun e=>v= e.1∨ v= e.2)).card≤ 1) ↔
      ∀ e∈ Q,∀ f∈ Q,e≠ f→ Disjoint ({e.1,e.2}:Finset (Fin k)) {f.1,f.2}:=by
  constructor
  · intro h e he f hf hef
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hv'
    have:=Finset.card_le_one.mp (h v) e (Finset.mem_filter.mpr ⟨he,hv⟩) f
      (Finset.mem_filter.mpr ⟨hf,hv'⟩)
    exact hef this
  · intro h v
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    have hva:v∈ ({a.1,a.2}:Finset (Fin k)):=by
      simp only [Finset.mem_insert,Finset.mem_singleton]; exact ha.2
    have hvb:v∈ ({b.1,b.2}:Finset (Fin k)):=by
      simp only [Finset.mem_insert,Finset.mem_singleton]; exact hb.2
    exact Finset.disjoint_left.mp (h a ha.1 b hb.1 hab) hva hvb
lemma b1i (Y:Finset (Fin k × Fin k)):-(rows.length:ℤ)≤ w3 rows Y:=by
  unfold w3
  have:=List.length_filter_le (fun t=>!t.2 && decide ((Y∩ t.1).Nonempty)) rows
  omega
lemma b1s (Y:Finset (Fin k × Fin k)):w3 rows Y≤ (rows.length:ℤ):=by
  unfold w3
  have:=List.length_filter_le (fun t=>t.2 && decide ((Y∩ t.1).Nonempty)) rows
  omega
lemma a2y (a:Fin (t+1)) (Q:Finset (Fin k × Fin k)) :
    ((r9 rows par B a Q:ℕ):ℤ)= a04 rows par B a Q+ 2* rows.length:=by
  unfold r9
  rw [Int.toNat_of_nonneg]
  unfold a04
  have:=b1i rows (Q.filter (fun e=>c6 k e∈ B a))
  have:=b1s rows (Q.filter (fun e=>c6 k e∈ B a∧ a≠ 0∧ c6 k e∈ B (par a)))
  omega
lemma a6j (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) :
    p3 E P H rows par B= ∑ Q∈ E.powerset,
      if n1 E P H par B Finset.univ Q then wIn rows par B Finset.univ Q else 0:=by
  have hEU:b9 E B Finset.univ= E:=by
    ext e; rw [f8]
    constructor
    · exact fun h=>h.1
    · intro he; obtain ⟨a,ha⟩:=hcover e he; exact ⟨he,a,Finset.mem_univ _,ha⟩
  have hpow:(b9 E B Finset.univ).powerset= E.powerset:=by rw [hEU]
  unfold p3
  have htab:a1i E P H rows par B (t+1) 0= Sem E P H rows par B Finset.univ 0:=by
    rw [a7n E P H rows par B hpar hpar0 hconnX (t+1) 0 (by simp),b4x par hpar hpar0]
  rw [htab]
  unfold Sem
  rw [Finset.sum_congr rfl (fun σ _=>Finset.sum_comm),Finset.sum_comm,hpow]
  refine Finset.sum_congr rfl (fun Q hQ=>?_)
  rw [Finset.sum_eq_single (sig B 0 Q),Finset.sum_eq_single (g3 par B Finset.univ 0 Q)]
  · exact if_congr ⟨fun h=>h.1,fun h=>⟨h,rfl,rfl⟩⟩ rfl rfl
  · intro τ _ hne; rw [if_neg (fun h=>hne h.2.2.symm)]
  · intro hn; exfalso; apply hn
    rw [Finset.mem_powerset]; intro v hv
    rw [k3] at hv; simp [hv.1]
  · intro σ _ hne; apply Finset.sum_eq_zero; intro τ _
    rw [if_neg (fun h=>hne h.2.1.symm)]
  · intro hn; exfalso; apply hn
    rw [Finset.mem_powerset]; intro e he
    rw [l0] at he ⊢
    exact ⟨Finset.mem_powerset.mp hQ he.1,he.2⟩
lemma a3o (w:ℕ) (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2)
    (hH:∀ e∈ H,e.1< e.2) (hd:s4 E rows par B w) :
    ∀ s j,t0 E P H rows par B s j= b3i E P H rows s j:=by
  intro s j
  dsimp only [s4] at hd
  obtain ⟨hpar0,hpar,hbag,hconn,hinc,htog⟩:=hd
  have hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top :=
    fun x a hx=>hconn x ((hbag a).1 hx)
  have hconnE:∀ e∈ E,∃ a,c6 k e∈ B a ∧
      ∀ i,c6 k e∈ B i→ i≠ a→ i≠ 0∧ c6 k e∈ B (par i) :=
    fun e he=>hconn _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))
  have hcover:∀ e∈ E,∃ a,c6 k e∈ B a :=
    fun e he=>by obtain ⟨a,ha,-⟩:=hconnE e he; exact ⟨a,ha⟩
  have hEU:b9 E B Finset.univ= E:=by
    ext e; rw [f8]
    constructor
    · exact fun h=>h.1
    · intro he; obtain ⟨a,ha⟩:=hcover e he; exact ⟨he,a,Finset.mem_univ _,ha⟩
  unfold t0 b3i
  dsimp only
  by_cases hPE:P⊆ E
  · rw [if_pos hPE, a6j E P H rows par B hpar hpar0 hconnX hcover]
    simp only [Finset.sum_apply]
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun Q hQ=>?_)
    have hQE:Q⊆ E:=Finset.mem_powerset.mp hQ
    have hcnt:=a9y E par B hpar hpar0 hconnX hinc Q hQE
    have key:n1 E P H par B Finset.univ Q↔ a1b E Q∧ P⊆ Q∧ Disjoint Q H:=by
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨hQE,(a4q Q).mp (fun v=>by rw [← hcnt]; exact h3 v)⟩,
          fun e he=>h1 e (by rw [hEU]; exact hPE he) he,
          Finset.disjoint_left.mpr (fun e he heH=>h2 e he heH)⟩
      · rintro ⟨hv, h2, h3⟩
        exact ⟨fun e _ he=>h2 he,fun e he heH=>Finset.disjoint_left.mp h3 he heH,
          fun v=>by rw [hcnt]; exact (a4q Q).mpr hv.2 v⟩
    have hsz:=a3s E par B hpar hpar0 hconnX hcover Q hQE
    have hnf:k6 rows≤ rows.length:=List.length_filter_le _ _
    by_cases hok:n1 E P H par B Finset.univ Q
    · have hv := key.mp hok
      have hsc:=a3a E rows t par B hpar0 hpar hconnE htog Q hv.1
      have hds:((∑ a,r9 rows par B a Q:ℕ):ℤ) =
          (a0k rows Q:ℤ) - k6 rows+ 2* ((rows.length* (t+1):ℕ):ℤ):=by
        push_cast
        rw [Finset.sum_congr rfl (fun a _=>a2y rows par B a Q),
          Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hsc]
        unfold a04
        simp only [nsmul_eq_mul]
        push_cast
        ring
      rw [if_pos hok]
      unfold wIn x0
      rw [hsz]
      have hz:j+ 2* rows.length* (t+1) - k6 rows =
          j+ 2* (rows.length* (t+1)) - k6 rows:=by
        rw [Nat.mul_assoc]
      have hM:rows.length≤ rows.length* (t+1):=Nat.le_mul_of_pos_right _ (by omega)
      rw [hz]
      have hsc':a0k rows Q= (rows.filter
          (fun r=>decide (decide ((Q∩ r.1).Nonempty)= r.2))).length:=rfl
      generalize rows.length* (t+1)= M at hds hM
      by_cases hC:Q.card= s∧ a0k rows Q= j
      · rw [if_pos ⟨hC.1.symm,by omega⟩,if_pos ⟨hv.1,hv.2.1,hv.2.2,hC.1,hC.2⟩]
      · rw [if_neg (fun h=>hC ⟨h.1.symm,by omega⟩),
          if_neg (fun h=>hC ⟨h.2.2.2.1,h.2.2.2.2⟩)]
    · rw [if_neg hok, if_neg (fun h => hok (key.mpr ⟨h.1, h.2.1, h.2.2.1⟩))]
      rfl
  · rw [if_neg hPE]
    symm
    rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro Q hQ hc
    exact hPE (hc.2.1.trans (Finset.mem_powerset.mp hQ))
end L45
section Fuel
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
lemma a0r {α β:Type*} (F G:β→ α→ β) :
    ∀ (l:List α) (a:β),(∀ j∈ l,∀ b,F b j= G b j)→ l.foldl F a= l.foldl G a:=by
  intro l
  induction l with
  | nil=>intro a _; simp only [List.foldl_nil]
  | cons j l ih =>
    intro a h
    simp only [List.foldl_cons]
    rw [h j (by simp)]
    exact ih _ (fun j' hj'=>h j' (by simp [hj']))
lemma b1a:∀ n m (i:Fin (t+1)),t - i.val< n→ t - i.val< m →
    a1i E P H rows par B n i= a1i E P H rows par B m i:=by
  intro n
  induction n with
  | zero=>intro m i h; omega
  | succ n ih =>
    intro m i hn hm
    cases m with
    | zero=>omega
    | succ m =>
      rw [a1i,a1i]
      apply a0r
      intro j hj b
      have hij:=((v9 par i j).mp hj).1
      have:=Fin.lt_def.mp hij; have:=j.isLt
      rw [ih m j (by omega) (by omega)]
end Fuel
section KronBase
def kap (R s z:ℕ):ℕ:=s* (R+1)+ z
def Kh (X R M Z:ℕ) (h:ℕ→ ℕ→ ℕ):ℕ :=
  ∑ s∈ Finset.range (M+1),∑ z∈ Finset.range (Z+1),h s z* X ^ kap R s z
def Bd (M Z:ℕ) (h:ℕ→ ℕ→ ℕ):Prop:=∀ s z,h s z≠ 0→ s≤ M∧ z≤ Z
variable (X R M Z:ℕ)
lemma b1r:Kh X R M Z 0= 0:=by simp [Kh]
lemma b8f (f g:ℕ→ ℕ→ ℕ):Kh X R M Z (f+ g)= Kh X R M Z f+ Kh X R M Z g:=by
  simp [Kh,add_mul,Finset.sum_add_distrib]
lemma a3e {ι:Type*} [DecidableEq ι] (S:Finset ι) (f:ι→ ℕ→ ℕ→ ℕ) :
    Kh X R M Z (∑ x∈ S,f x)= ∑ x∈ S,Kh X R M Z (f x):=by
  refine Finset.induction_on S ?_ ?_
  · simp only [Finset.sum_empty]; exact b1r X R M Z
  · intro x S hx ih
    rw [Finset.sum_insert hx,Finset.sum_insert hx,b8f,ih]
lemma b3c (c:Prop) [Decidable c] (h:ℕ→ ℕ→ ℕ) :
    Kh X R M Z (if c then h else 0)= if c then Kh X R M Z h else 0:=by
  split_ifs
  · rfl
  · exact b1r X R M Z
lemma b8b (c:ℕ) (h:ℕ→ ℕ→ ℕ):Kh X R M Z (c • h)= c* Kh X R M Z h:=by
  simp [Kh,Finset.mul_sum,mul_assoc]
lemma b1q (a b:ℕ) :
    Kh X R M Z (x0 a b)= if a≤ M∧ b≤ Z then X ^ kap R a b else 0:=by
  simp only [Kh,x0]
  by_cases h:a≤ M∧ b≤ Z
  · rw [if_pos h, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro z _ hz; simp [hz]
    · intro hb; exfalso; exact hb (Finset.mem_range.mpr (by omega))
    · intro s _ hs; apply Finset.sum_eq_zero; intro z _; simp [hs]
    · intro ha; exfalso; exact ha (Finset.mem_range.mpr (by omega))
  · rw [if_neg h]
    apply Finset.sum_eq_zero; intro s hs; apply Finset.sum_eq_zero; intro z hz
    rw [Finset.mem_range] at hs hz
    rw [if_neg (by omega)]; simp
lemma a0f (h:ℕ→ ℕ→ ℕ) (hb:Bd M Z h) :
    h= ∑ s∈ Finset.range (M+1),∑ z∈ Finset.range (Z+1),h s z • x0 s z:=by
  funext a b
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,x0]
  by_cases hab:h a b= 0
  · rw [hab]; symm; apply Finset.sum_eq_zero; intro s _; apply Finset.sum_eq_zero; intro z _
    by_cases h2:a= s∧ b= z
    · obtain ⟨rfl,rfl⟩:=h2; simp [hab]
    · simp [h2]
  · obtain ⟨ha, hb'⟩ := hb a b hab
    rw [Finset.sum_eq_single a,Finset.sum_eq_single b]
    · simp
    · intro z _ hz; simp [Ne.symm hz]
    · intro h'; exfalso; exact h' (Finset.mem_range.mpr (by omega))
    · intro s _ hs; apply Finset.sum_eq_zero; intro z _; simp [Ne.symm hs]
    · intro h'; exfalso; exact h' (Finset.mem_range.mpr (by omega))
lemma a7v (c:ℕ) (f g:ℕ→ ℕ→ ℕ):j1 (c • f) g= c • j1 f g:=by
  funext s z; simp [j1,Finset.mul_sum,mul_assoc]
lemma a79 (c:ℕ) (f g:ℕ→ ℕ→ ℕ):j1 f (c • g)= c • j1 f g:=by
  funext s z; simp [j1,Finset.mul_sum,mul_left_comm]
lemma b7p (f g:ℕ→ ℕ→ ℕ) (s1 z1 s2 z2:ℕ) :
    f s1 z1* g s2 z2≤ j1 f g (s1+s2) (z1+z2):=by
  unfold j1
  calc f s1 z1 * g s2 z2 = f s1 z1 * g (s1 + s2 - s1) (z1 + z2 - z1) := by simp
    _ ≤ ∑ b ∈ Finset.range (z1+z2+1), f s1 b * g (s1 + s2 - s1) (z1 + z2 - b) :=
        Finset.single_le_sum (f:=fun b=>f s1 b* g (s1+ s2 - s1) (z1+ z2 - b))
          (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    _ ≤ _ := Finset.single_le_sum
          (f:=fun a=>∑ b∈ Finset.range (z1+z2+1),f a b* g (s1+ s2 - a) (z1+ z2 - b))
          (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr (by omega))
lemma b8h (f g:ℕ→ ℕ→ ℕ) (hf:Bd M Z f) (hg:Bd M Z g) (hfg:Bd M Z (j1 f g)) :
    Kh X R M Z (j1 f g)= Kh X R M Z f* Kh X R M Z g:=by
  have e1:j1 f g= ∑ s1∈ Finset.range (M+1),∑ z1∈ Finset.range (Z+1),
      ∑ s2 ∈ Finset.range (M+1), ∑ z2 ∈ Finset.range (Z+1),
        (f s1 z1* g s2 z2) • x0 (s1+s2) (z1+z2):=by
    conv_lhs=>rw [a0f M Z f hf,a0f M Z g hg]
    rw [a1h]; refine Finset.sum_congr rfl (fun s1 _=>?_)
    rw [a1h]; refine Finset.sum_congr rfl (fun z1 _=>?_)
    rw [a7v,a0v,Finset.smul_sum]
    refine Finset.sum_congr rfl (fun s2 _=>?_)
    rw [a0v,Finset.smul_sum]; refine Finset.sum_congr rfl (fun z2 _=>?_)
    rw [a79,a8v,smul_smul]
  rw [e1]
  simp only [a3e,b8b,b1q]
  unfold Kh
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun s1 _=>?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s2 _=>?_)
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun z1 _=>Finset.sum_congr rfl (fun z2 _=>?_))
  by_cases h0:f s1 z1* g s2 z2= 0
  · rcases Nat.mul_eq_zero.mp h0 with h | h <;> simp [h]
  · have hle := b7p f g s1 z1 s2 z2
    have hne:j1 f g (s1+s2) (z1+z2)≠ 0:=by
      intro h; rw [h] at hle; exact h0 (Nat.le_zero.mp hle)
    obtain ⟨h1,h2⟩:=hfg _ _ hne
    rw [if_pos ⟨h1,h2⟩]
    unfold kap
    rw [show (s1+s2)*(R+1)+ (z1+z2)= (s1*(R+1)+z1)+ (s2*(R+1)+z2) by ring,pow_add]
    ring
lemma b7y:Bd M Z 0:=fun s z h=>absurd rfl h
lemma b0f {ι:Type*} (S:Finset ι) (f:ι→ ℕ→ ℕ→ ℕ) (h:∀ x∈ S,Bd M Z (f x)) :
    Bd M Z (∑ x∈ S,f x):=by
  intro s z hs
  simp only [Finset.sum_apply] at hs
  obtain ⟨x,hx,hne⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  exact h x hx s z hne
lemma b4s (c:Prop) [Decidable c] (h:ℕ→ ℕ→ ℕ) (hb:Bd M Z h) :
    Bd M Z (if c then h else 0):=by
  split_ifs
  · exact hb
  · exact b7y M Z
lemma b7u (a b:ℕ) (ha:a≤ M) (hb:b≤ Z):Bd M Z (x0 a b):=by
  intro s z h
  simp only [x0] at h
  split_ifs at h with h'
  · omega
  · exact absurd rfl h
lemma c0i (f g:ℕ→ ℕ→ ℕ) (hle:∀ s z,f s z≤ g s z) (hg:Bd M Z g):Bd M Z f:=by
  intro s z h
  exact hg s z (fun h'=>h (Nat.le_zero.mp (h' ▸ hle s z)))
lemma b33 (hX:0< X):∀ (L:ℕ) (c:ℕ→ ℕ),(∀ e< L,c e< X) →
    (∑ e∈ Finset.range L,c e* X ^ e)< X ^ L ∧
      ∀ e< L,(∑ e'∈ Finset.range L,c e'* X ^ e') / X ^ e % X= c e:=by
  intro L
  induction L with
  | zero=>intro c _; simp
  | succ L ih =>
    intro c hc
    obtain ⟨ih1,ih2⟩:=ih (fun e=>c (e+1)) (fun e he=>hc (e+1) (by omega))
    have hsplit:(∑ e∈ Finset.range (L+1),c e* X ^ e) =
        c 0+ X* ∑ e∈ Finset.range L,c (e+1)* X ^ e:=by
      rw [Finset.sum_range_succ',Finset.mul_sum]
      simp only [pow_succ,pow_zero,mul_one]
      rw [add_comm]; congr 1
      refine Finset.sum_congr rfl (fun e _=>?_); ring
    rw [hsplit]
    have hc0:=hc 0 (by omega)
    constructor
    · have : (∑ e ∈ Finset.range L, c (e+1) * X ^ e) + 1 ≤ X ^ L := ih1
      calc c 0 + X * ∑ e ∈ Finset.range L, c (e+1) * X ^ e
          < X+ X* ∑ e∈ Finset.range L,c (e+1)* X ^ e:=by omega
        _= X* ((∑ e∈ Finset.range L,c (e+1)* X ^ e)+ 1):=by ring
        _≤ X* X ^ L:=Nat.mul_le_mul_left _ this
        _= X ^ (L+1):=by ring
    · intro e he
      cases e with
      | zero =>
        simp only [pow_zero,Nat.div_one]
        rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hc0]
      | succ e =>
        rw [pow_succ,mul_comm (X ^ e) X,← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ hX,Nat.div_eq_of_lt hc0,zero_add]
        exact ih2 e (by omega)
lemma b7s (G:ℕ→ ℕ→ ℕ):∀ M:ℕ,
    ∑ s ∈ Finset.range (M+1), ∑ u ∈ Finset.range (R+1), G s u =
      ∑ e∈ Finset.range ((M+1)*(R+1)),G (e / (R+1)) (e % (R+1)):=by
  intro M
  induction M with
  | zero =>
    simp only [zero_add,Finset.sum_range_one,one_mul]
    refine Finset.sum_congr rfl (fun e he=>?_)
    rw [Finset.mem_range] at he
    rw [Nat.div_eq_of_lt he,Nat.mod_eq_of_lt he]
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,show (M+1+1)*(R+1)= (M+1)*(R+1)+ (R+1) by ring,
      Finset.sum_range_add (fun e=>G (e / (R+1)) (e % (R+1))) ((M+1)*(R+1)) (R+1)]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_range] at hu
    rw [show (M+1)*(R+1)+ u= (R+1)*(M+1)+ u by ring,Nat.mul_add_div (by omega),
      Nat.mul_add_mod,Nat.div_eq_of_lt hu,Nat.mod_eq_of_lt hu,add_zero]
end KronBase
section KronDP
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ) (X:ℕ)
def y0 (i:Fin (t+1)) (σ:Finset (Fin k × Fin k)) (τ:Finset (Fin k)):ℕ :=
  if σ⊆ b9 E B {i}∧ n1 E P H par B {i} σ∧ g3 par B {i} i σ= τ then
    X ^ kap rows.length (w9 par B i σ) (r9 rows par B i σ) else 0
def a6h (kt : Finset (Fin k × Fin k) → Finset (Fin k) → ℕ) (i j : Fin (t+1))
    (σ':Finset (Fin k × Fin k)) (τ':Finset (Fin k)):ℕ :=
  ∑ σj ∈ (sig B j E).powerset, ∑ τj ∈ (Finset.univ.filter (fun v : Fin k => v.val ∈ B j)).powerset,
    if sig B i σj= σ'∧ τj.filter (fun v=>v.val∈ B i)= τ' then kt σj τj else 0
def s0 (kt : Finset (Fin k × Fin k) → Finset (Fin k) → ℕ) (i j : Fin (t+1))
    (kacc:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ) :
    Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ:=fun σ τ =>
  ∑ τ1∈ τ.powerset,kacc σ τ1* a6h E B kt i j (sig B j σ) (τ \ τ1)
def p8:ℕ→ Fin (t+1)→ Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ
  | 0,i=>y0 E P H rows par B X i
  | n+1,i=>(k8 par i).foldl (fun kacc j=>s0 E B (p8 n j) i j kacc)
      (y0 E P H rows par B X i)
def a35:ℕ :=
  ∑ σ ∈ (sig B 0 E).powerset, ∑ τ ∈ (Finset.univ.filter (fun v : Fin k => v.val ∈ B 0)).powerset,
    p8 E P H rows par B X (t+1) 0 σ τ
lemma b6a (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)):w9 par B i Q≤ Q.card :=
  Finset.card_filter_le _ _
lemma a8k (i:Fin (t+1)) (Q:Finset (Fin k × Fin k)) :
    r9 rows par B i Q≤ 4* rows.length:=by
  have h:=a2y rows par B i Q
  unfold a04 at h
  have:=b1s rows (Q.filter (fun e=>c6 k e∈ B i))
  have:=b1i rows (Q.filter (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i)))
  omega
lemma b8p (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) (M Z:ℕ) (hM:E.card≤ M)
    (hZ:4* rows.length* (t+1)≤ Z) (U:Finset (Fin (t+1))) (i:Fin (t+1))
    (σ:Finset (Fin k × Fin k)) (τ:Finset (Fin k)):Bd M Z (Sem E P H rows par B U i σ τ):=by
  unfold Sem
  apply b0f; intro Q hQ; apply b4s; unfold wIn
  have hQE:Q⊆ E:=fun e he=>((f8 E B U e).mp (Finset.mem_powerset.mp hQ he)).1
  apply b7u
  · calc ∑ a ∈ U, w9 par B a Q ≤ ∑ a, w9 par B a Q :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ U)
      _= Q.card:=a3s E par B hpar hpar0 hconnX hcover Q hQE
      _≤ E.card:=Finset.card_le_card hQE
      _≤ M:=hM
  · calc ∑ a ∈ U, r9 rows par B a Q ≤ U.card • (4 * rows.length) :=
          Finset.sum_le_card_nsmul _ _ _ (fun a _=>a8k rows par B a Q)
      _ ≤ (t+1) * (4 * rows.length) := by
          rw [smul_eq_mul]; apply Nat.mul_le_mul_right
          simpa using Finset.card_le_univ U
      _≤ Z:=by nlinarith
lemma b9w (M Z:ℕ) (hM:E.card≤ M) (hZ:4* rows.length≤ Z) (i:Fin (t+1))
    (σ:Finset (Fin k × Fin k)) (τ:Finset (Fin k)) :
    Kh X rows.length M Z (a7e E P H rows par B i σ τ)= y0 E P H rows par B X i σ τ:=by
  unfold a7e y0
  rw [b3c]
  split_ifs with h
  · unfold wIn
    rw [Finset.sum_singleton,Finset.sum_singleton,b1q,if_pos]
    constructor
    · have hσE : σ ⊆ E := fun e he => ((f8 E B {i} e).mp (h.1 he)).1
      exact (b6a par B i σ).trans ((Finset.card_le_card hσE).trans hM)
    · exact (a8k rows par B i σ).trans hZ
  · rfl
lemma c0k (M Z:ℕ) (tabj:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ→ ℕ→ ℕ)
    (i j:Fin (t+1)) (σ':Finset (Fin k × Fin k)) (τ':Finset (Fin k)) :
    Kh X rows.length M Z (msg E B tabj i j σ' τ') =
      a6h E B (fun σ τ=>Kh X rows.length M Z (tabj σ τ)) i j σ' τ':=by
  unfold msg a6h
  rw [a3e]; refine Finset.sum_congr rfl (fun σj _=>?_)
  rw [a3e]; refine Finset.sum_congr rfl (fun τj _=>?_)
  rw [b3c]
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
lemma c03 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) (M Z:ℕ) (hM:E.card≤ M)
    (hZ:4* rows.length* (t+1)≤ Z)
    (U D:Finset (Fin (t+1))) (i j:Fin (t+1)) (hi:i∈ U) (hj:j∈ D)
    (hdisj:Disjoint U D)
    (hsep:∀ x:ℕ,∀ a∈ U,∀ b∈ D,x∈ B a→ x∈ B b→ x∈ B i∧ x∈ B j) :
    s0 E B (fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B D j σ τ)) i j
        (fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B U i σ τ)) =
      fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B (U∪ D) i σ τ):=by
  funext σ τ
  have hbd:=fun U i σ τ=>b8p E P H rows par B hpar hpar0 hconnX hcover M Z hM hZ U i σ τ
  rw [← a6l E P H rows par B U D i j hi hj hdisj hsep]
  have hst:=a6l E P H rows par B U D i j hi hj hdisj hsep
  unfold s0 a54
  rw [a3e]
  refine Finset.sum_congr rfl (fun τ1 hτ1=>?_)
  rw [← c0k]
  have hmsg:Bd M Z (msg E B (Sem E P H rows par B D j) i j (sig B j σ) (τ \ τ1)):=by
    unfold msg
    apply b0f; intro σj _; apply b0f; intro τj _; apply b4s; exact hbd D j σj τj
  refine (b8h X rows.length M Z _ _ (hbd U i σ τ1) hmsg ?_).symm
  refine c0i M Z _ _ ?_ (hbd (U∪ D) i σ τ)
  intro s z
  rw [← hst]
  unfold a54
  rw [Finset.sum_apply,Finset.sum_apply]
  exact Finset.single_le_sum
    (f:=fun τ1=>j1 (Sem E P H rows par B U i σ τ1)
      (msg E B (Sem E P H rows par B D j) i j (sig B j σ) (τ \ τ1)) s z)
    (fun _ _=>Nat.zero_le _) hτ1
lemma b9d (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) (M Z:ℕ) (hM:E.card≤ M)
    (hZ:4* rows.length* (t+1)≤ Z) (i:Fin (t+1)) :
    ∀ (l : List (Fin (t+1))) (U : Finset (Fin (t+1))), l.Nodup → (∀ j ∈ l, i < j ∧ par j = i) →
      i∈ U→ (∀ j∈ l,Disjoint U (k0 par j)) →
      l.foldl (fun kacc j=>s0 E B
          (fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B (k0 par j) j σ τ)) i j kacc)
        (fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B U i σ τ)) =
      fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B (U∪ l.toFinset.biUnion (k0 par)) i σ τ):=by
  intro l
  induction l with
  | nil=>intro U _ _ _ _; simp
  | cons j l ih =>
    intro U hnd hl hiU hdisj
    rw [List.foldl_cons]
    have hj:=hl j (by simp)
    have hdj:Disjoint U (k0 par j):=hdisj j (by simp)
    have hsep:∀ x:ℕ,∀ a∈ U,∀ b∈ k0 par j,x∈ B a→ x∈ B b→ x∈ B i∧ x∈ B j:=by
      intro x a ha b hb hxa hxb
      obtain ⟨top,htop⟩:=hconnX x a hxa
      have:=a7d par hpar hpar0 htop i j a b hj.2
        (Finset.disjoint_left.mp hdj ha) hb hxa hxb
      exact ⟨this.2,this.1⟩
    have hnd':=List.nodup_cons.mp hnd
    have hdisj':∀ j'∈ l,Disjoint (U∪ k0 par j) (k0 par j'):=by
      intro j' hj'
      rw [Finset.disjoint_union_left]
      refine ⟨hdisj j' (by simp [hj']),?_⟩
      have hj'c:=hl j' (by simp [hj'])
      exact a8h par hpar hpar0 i j j' hj.1 hj.2 hj'c.1 hj'c.2
        (fun h=>hnd'.1 (h ▸ hj'))
    rw [c03 E P H rows par B X hpar hpar0 hconnX hcover M Z hM hZ U (k0 par j) i j hiU
      (a2r par hpar hpar0 j) hdj hsep,
      ih (U∪ k0 par j) hnd'.2 (fun j' hj'=>hl j' (by simp [hj']))
        (Finset.mem_union_left _ hiU) hdisj']
    rw [List.toFinset_cons,Finset.biUnion_insert,Finset.union_assoc]
lemma a80 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) (M Z:ℕ) (hM:E.card≤ M)
    (hZ:4* rows.length* (t+1)≤ Z) :
    ∀ n (i : Fin (t+1)), t - i.val < n →
      p8 E P H rows par B X n i =
        fun σ τ=>Kh X rows.length M Z (a1i E P H rows par B n i σ τ):=by
  have hZ1:4* rows.length≤ Z:=le_trans (by nlinarith) hZ
  intro n
  induction n with
  | zero=>intro i h; omega
  | succ n ih =>
    intro i hi
    have hnd:(k8 par i).Nodup:=List.Nodup.filter _ (List.nodup_finRange _)
    have hch:∀ j∈ k8 par i,i< j∧ par j= i :=
      fun j hj=>(v9 par i j).mp hj
    have hdisj:∀ j∈ k8 par i,Disjoint {i} (k0 par j):=by
      intro j hj
      rw [Finset.disjoint_singleton_left]
      intro h
      have:=b1e par hpar hpar0 j i h
      exact absurd (hch j hj).1 (not_lt.mpr this)
    have hlt:∀ j∈ k8 par i,t - j.val< n:=by
      intro j hj
      have:=Fin.lt_def.mp (hch j hj).1; have:=j.isLt; omega
    rw [p8]
    have e1:(k8 par i).foldl (fun kacc j=>s0 E B (p8 E P H rows par B X n j) i j kacc)
        (y0 E P H rows par B X i) =
        (k8 par i).foldl (fun kacc j=>s0 E B
          (fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B (k0 par j) j σ τ)) i j kacc)
          (fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B {i} i σ τ)):=by
      have hl:y0 E P H rows par B X i =
          fun σ τ=>Kh X rows.length M Z (Sem E P H rows par B {i} i σ τ):=by
        funext σ τ; rw [b0k,b9w E P H rows par B X M Z hM hZ1]
      rw [hl]
      apply a0r
      intro j hj b
      rw [ih j (hlt j hj),a7n E P H rows par B hpar hpar0 hconnX n j (hlt j hj)]
    rw [e1,b9d E P H rows par B X hpar hpar0 hconnX hcover M Z hM hZ i (k8 par i) {i}
      hnd hch (Finset.mem_singleton_self i) hdisj]
    rw [a7n E P H rows par B hpar hpar0 hconnX (n+1) i hi]
    funext σ τ
    congr 2
    ext m
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,List.mem_toFinset]
    constructor
    · rintro (rfl | ⟨j, hj, hm⟩)
      · exact a2r par hpar hpar0 m
      · exact a6n par hpar hpar0 i j m hm (a30 par hpar hpar0 i j (hch j hj).2)
    · intro hm
      rcases a5l par hpar hpar0 i m hm with h | ⟨j,hij,hpj,hmj⟩
      · exact Or.inl h
      · exact Or.inr ⟨j,(v9 par i j).mpr ⟨hij,hpj⟩,hmj⟩
lemma b47 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) (M Z:ℕ) (hM:E.card≤ M)
    (hZ:4* rows.length* (t+1)≤ Z) :
    a35 E P H rows par B X= Kh X rows.length M Z (p3 E P H rows par B):=by
  unfold a35 p3
  rw [a80 E P H rows par B X hpar hpar0 hconnX hcover M Z hM hZ (t+1) 0 (by simp)]
  rw [a3e]; refine Finset.sum_congr rfl (fun σ _=>?_)
  rw [a3e]
end KronDP
section KronOut
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
lemma a6p (w:ℕ) (hd:s4 E rows par B w) :
    par 0= 0∧ (∀ i,i≠ 0→ par i< i) ∧
    (∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top) ∧
    (∀ e∈ E,∃ a,c6 k e∈ B a ∧
      ∀ i,c6 k e∈ B i→ i≠ a→ i≠ 0∧ c6 k e∈ B (par i)) ∧
    (∀ e∈ E,(∃ i,c6 k e∈ B i∧ e.1.val∈ B i)∧ (∃ i,c6 k e∈ B i∧ e.2.val∈ B i)) ∧
    (∀ e∈ E,∀ f∈ E,e≠ f→ (∃ Q,a1b E Q∧ e∈ Q∧ f∈ Q∧ a05 rows Q≠ 0) →
        ∃ i,c6 k e∈ B i∧ c6 k f∈ B i):=by
  dsimp only [s4] at hd
  obtain ⟨hpar0,hpar,hbag,hconn,hinc,htog⟩:=hd
  exact ⟨hpar0,hpar,fun x a hx=>hconn x ((hbag a).1 hx),
    fun e he=>hconn _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)),hinc,htog⟩
lemma b2y (hpar0:par 0= 0) (hpar:∀ i,i≠ 0→ par i< i)
    (hconnE:∀ e∈ E,∃ a,c6 k e∈ B a ∧
      ∀ i,c6 k e∈ B i→ i≠ a→ i≠ 0∧ c6 k e∈ B (par i))
    (htog:∀ e∈ E,∀ f∈ E,e≠ f→ (∃ Q,a1b E Q∧ e∈ Q∧ f∈ Q∧ a05 rows Q≠ 0) →
        ∃ i,c6 k e∈ B i∧ c6 k f∈ B i)
    (Q:Finset (Fin k × Fin k)) (hQ:a1b E Q) :
    ((∑ a,r9 rows par B a Q:ℕ):ℤ) =
      (a0k rows Q:ℤ) - k6 rows+ 2* ((rows.length* (t+1):ℕ):ℤ):=by
  have hsc:=a3a E rows t par B hpar0 hpar hconnE htog Q hQ
  push_cast
  rw [Finset.sum_congr rfl (fun a _=>a2y rows par B a Q),
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hsc]
  unfold a04
  simp only [nsmul_eq_mul]
  push_cast
  ring
lemma b60 (w:ℕ) (hd:s4 E rows par B w) (s z:ℕ) :
    p3 E P H rows par B s z≤ 2 ^ E.card:=by
  obtain ⟨hpar0,hpar,hconnX,hconnE,-,-⟩:=a6p E rows par B w hd
  have hcover:∀ e∈ E,∃ a,c6 k e∈ B a :=
    fun e he=>by obtain ⟨a,ha,-⟩:=hconnE e he; exact ⟨a,ha⟩
  rw [a6j E P H rows par B hpar hpar0 hconnX hcover]
  simp only [Finset.sum_apply]
  calc _ ≤ E.powerset.card • 1 := by
        apply Finset.sum_le_card_nsmul
        intro Q _
        by_cases h:n1 E P H par B Finset.univ Q
        · rw [if_pos h]; simp only [wIn,x0]; split_ifs <;> omega
        · rw [if_neg h]; simp
    _= 2 ^ E.card:=by rw [Finset.card_powerset,smul_eq_mul,mul_one]
lemma b34 (w:ℕ) (hd:s4 E rows par B w) (s z:ℕ)
    (hne:p3 E P H rows par B s z≠ 0) :
    s ≤ E.card ∧ 2 * rows.length * (t+1) - k6 rows ≤ z ∧
      z≤ 2* rows.length* (t+1) - k6 rows+ rows.length:=by
  obtain ⟨hpar0,hpar,hconnX,hconnE,hinc,htog⟩:=a6p E rows par B w hd
  have hcover:∀ e∈ E,∃ a,c6 k e∈ B a :=
    fun e he=>by obtain ⟨a,ha,-⟩:=hconnE e he; exact ⟨a,ha⟩
  rw [a6j E P H rows par B hpar hpar0 hconnX hcover] at hne
  simp only [Finset.sum_apply] at hne
  obtain ⟨Q,hQ,hQne⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  have hQE:=Finset.mem_powerset.mp hQ
  by_cases hok:n1 E P H par B Finset.univ Q
  · rw [if_pos hok] at hQne
    simp only [wIn,x0] at hQne
    by_cases hsz:s= ∑ a,w9 par B a Q∧ z= ∑ a,r9 rows par B a Q
    · obtain ⟨rfl, rfl⟩ := hsz
      have hv:a1b E Q:=⟨hQE,(a4q Q).mp (fun v=>by
        rw [← a9y E par B hpar hpar0 hconnX hinc Q hQE v]; exact hok.2.2 v)⟩
      have h1:=b2y E rows par B hpar0 hpar hconnE htog Q hv
      have hsc:a0k rows Q≤ rows.length:=List.length_filter_le _ _
      have hnf:k6 rows≤ rows.length:=List.length_filter_le _ _
      have hRA:rows.length≤ rows.length* (t+1):=Nat.le_mul_of_pos_right _ (by omega)
      rw [a3s E par B hpar hpar0 hconnX hcover Q hQE]
      rw [show 2* rows.length* (t+1)= 2* (rows.length* (t+1)) by ring]
      generalize rows.length* (t+1)= A at h1 hRA
      refine ⟨Finset.card_le_card hQE,?_,?_⟩ <;> omega
    · rw [if_neg hsz] at hQne; exact absurd rfl hQne
  · rw [if_neg hok] at hQne; exact absurd rfl hQne
lemma b50 (w:ℕ) (hd:s4 E rows par B w) (X M Z:ℕ)
    (hZ:4* rows.length* (t+1)≤ Z) :
    Kh X rows.length M Z (p3 E P H rows par B) =
      X ^ (2 * rows.length * (t+1) - k6 rows) *
        ∑ e ∈ Finset.range ((M+1)*(rows.length+1)),
          p3 E P H rows par B (e / (rows.length+1))
            (2* rows.length* (t+1) - k6 rows+ e % (rows.length+1))* X ^ e:=by
  obtain ⟨D0,hD0⟩:∃ D0,D0= 2* rows.length* (t+1) - k6 rows:=⟨_,rfl⟩
  rw [← hD0]
  have hsupp:=b34 E P H rows par B w hd
  rw [← hD0] at hsupp
  have hA:2* rows.length* (t+1)+ rows.length≤ 4* rows.length* (t+1):=by nlinarith
  have hDZ:D0+ rows.length≤ Z:=by omega
  unfold Kh
  have hrow:∀ s∈ Finset.range (M+1),
      ∑ z∈ Finset.range (Z+1),p3 E P H rows par B s z* X ^ kap rows.length s z =
      X ^ D0 * ∑ u ∈ Finset.range (rows.length+1),
        p3 E P H rows par B s (D0+ u)* X ^ (s* (rows.length+1)+ u):=by
    intro s _
    rw [Finset.mul_sum]
    have himg:(Finset.range (rows.length+1)).image (fun u=>D0+ u)⊆ Finset.range (Z+1):=by
      intro z hz
      simp only [Finset.mem_image,Finset.mem_range] at hz ⊢
      obtain ⟨u,hu,rfl⟩:=hz; omega
    have hsub:=Finset.sum_subset himg
      (f:=fun z=>p3 E P H rows par B s z* X ^ kap rows.length s z) (by
        intro z _ hz
        by_cases h0:p3 E P H rows par B s z= 0
        · simp only [h0,zero_mul]
        · exfalso; apply hz
          obtain ⟨_,h1,h2⟩:=hsupp s z h0
          simp only [Finset.mem_image,Finset.mem_range]
          exact ⟨z - D0,by omega,by omega⟩)
    rw [← hsub,Finset.sum_image (fun a _ b _ h=>by simpa using h)]
    refine Finset.sum_congr rfl (fun u _=>?_)
    unfold kap
    rw [show s* (rows.length+1)+ (D0+ u)= D0+ (s*(rows.length+1)+u) by ring,pow_add]
    ring
  rw [Finset.sum_congr rfl hrow,← Finset.mul_sum]
  congr 1
  rw [b7s rows.length
    (fun s u=>p3 E P H rows par B s (D0+ u)* X ^ (s* (rows.length+1)+ u)) M]
  refine Finset.sum_congr rfl (fun e _=>?_)
  rw [Nat.div_add_mod']
lemma b65 (w:ℕ) (hd:s4 E rows par B w) (W:ℕ) (hEW:E.card< W) (M Z:ℕ)
    (hZ:4* rows.length* (t+1)≤ Z) :
    Kh (2^W) rows.length M Z (p3 E P H rows par B) <
        2 ^ (W* ((M+1)*(rows.length+1)*(4*t+5))) ∧
    ∀ s j, s ≤ M → j ≤ rows.length →
      Kh (2^W) rows.length M Z (p3 E P H rows par B) /
          (2^W) ^ (kap rows.length s (j+ (2* rows.length* (t+1) - k6 rows))) % 2^W =
        p3 E P H rows par B s (j+ (2* rows.length* (t+1) - k6 rows)):=by
  have hX:0< 2^W:=by positivity
  have hc:∀ e< (M+1)*(rows.length+1),p3 E P H rows par B (e / (rows.length+1))
      (2* rows.length* (t+1) - k6 rows+ e % (rows.length+1))< 2^W :=
    fun e _=>lt_of_le_of_lt (b60 E P H rows par B w hd _ _)
      (Nat.pow_lt_pow_right (by norm_num) hEW)
  obtain ⟨hlt,hdig⟩:=b33 (2^W) hX _ _ hc
  rw [b50 E P H rows par B w hd (2^W) M Z hZ]
  obtain ⟨D0,hD0⟩:∃ D0,D0= 2* rows.length* (t+1) - k6 rows:=⟨_,rfl⟩
  rw [← hD0] at hlt hdig ⊢
  constructor
  · have hDle:D0+ (M+1)*(rows.length+1)≤ (M+1)*(rows.length+1)*(4*t+5):=by
      have:D0≤ 2* rows.length* (t+1):=by omega
      nlinarith
    calc (2^W) ^ D0 * _ < (2^W) ^ D0 * (2^W) ^ ((M+1)*(rows.length+1)) :=
          (Nat.mul_lt_mul_left (by positivity)).mpr hlt
      _= (2^W) ^ (D0+ (M+1)*(rows.length+1)):=by rw [pow_add]
      _≤ (2^W) ^ ((M+1)*(rows.length+1)*(4*t+5)):=Nat.pow_le_pow_right hX hDle
      _= 2 ^ (W* ((M+1)*(rows.length+1)*(4*t+5))):=by rw [← pow_mul]
  · intro s j hs hj
    have he:s* (rows.length+1)+ j< (M+1)*(rows.length+1):=by nlinarith
    unfold kap
    rw [show s* (rows.length+1)+ (j+ D0)= D0+ (s*(rows.length+1)+j) by ring,pow_add,
      Nat.mul_div_mul_left _ _ (by positivity),hdig _ he]
    rw [show s*(rows.length+1)+j= (rows.length+1)*s+ j by ring,Nat.mul_add_div (by omega),
      Nat.mul_add_mod,Nat.div_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),
      Nat.add_zero,Nat.add_comm D0 j]
lemma b3v (w:ℕ) (hd:s4 E rows par B w) (W:ℕ) (hEW:E.card< W) (M:ℕ)
    (hM:E.card≤ M) :
    a35 E P H rows par B (2^W)< 2 ^ (W* ((M+1)*(rows.length+1)*(4*t+5))) ∧
    ∀ s j, s ≤ M → j ≤ rows.length → P ⊆ E →
      t0 E P H rows par B s j= a35 E P H rows par B (2^W) /
          (2^W) ^ (kap rows.length s (j+ (2* rows.length* (t+1) - k6 rows))) % 2^W:=by
  obtain ⟨hpar0,hpar,hconnX,hconnE,-,-⟩:=a6p E rows par B w hd
  have hcover:∀ e∈ E,∃ a,c6 k e∈ B a :=
    fun e he=>by obtain ⟨a,ha,-⟩:=hconnE e he; exact ⟨a,ha⟩
  have hK:=b47 E P H rows par B (2^W) hpar hpar0 hconnX hcover M
    (4* rows.length* (t+1)) hM le_rfl
  obtain ⟨h1,h2⟩:=b65 E P H rows par B w hd W hEW M (4* rows.length* (t+1)) le_rfl
  rw [hK]
  refine ⟨h1,fun s j hs hj hPE=>?_⟩
  rw [h2 s j hs hj]
  unfold t0
  rw [if_pos hPE]
  have hnf:k6 rows≤ rows.length:=List.length_filter_le _ _
  have:k6 rows≤ 2* rows.length* (t+1):=by nlinarith
  congr 1
  omega
lemma b53 (hpar:∀ i,i≠ 0→ par i< i) (hpar0:par 0= 0)
    (hconnX:∀ x a,x∈ B a→ ∃ top,p9 par (fun i=>x∈ B i) top)
    (hcover:∀ e∈ E,∃ a,c6 k e∈ B a) (X M:ℕ) (hM:E.card≤ M) (i:Fin (t+1)) :
    p8 E P H rows par B X (t+1) i =
      (k8 par i).foldl (fun kacc j=>s0 E B (p8 E P H rows par B X (t+1) j) i j kacc)
        (y0 E P H rows par B X i):=by
  rw [p8]
  apply a0r
  intro j hj b
  have hij:=Fin.lt_def.mp ((v9 par i j).mp hj).1
  have:=j.isLt
  rw [a80 E P H rows par B X hpar hpar0 hconnX hcover M (4* rows.length* (t+1)) hM le_rfl
      t j (by omega),
    a80 E P H rows par B X hpar hpar0 hconnX hcover M (4* rows.length* (t+1)) hM le_rfl
      (t+1) j (by omega),
    b1a E P H rows par B t (t+1) j (by omega) (by omega)]
end KronOut
end asmP2
section asmP3
namespace Dec
def header (z:Nat):List Bool:=List.replicate z true++[false]
def pairs (n:Nat):List (Fin n × Fin n):=(List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j=>decide (i< j))).map (fun j=>(i,j)))
def bits (width value:Nat):List Bool:=(List.range width).map (fun h=>value.testBit h)
def mask {k:Nat} (A:Finset (Fin k × Fin k)):List Bool :=
  (pairs k).map (fun e=>decide (e∈ A))
def tag (k:Nat) (e:Fin k × Fin k):Nat:=k+ e.1.val* k+ e.2.val
def layout (k:Nat):List Nat:=List.range k++(pairs k).map (tag k)
def a9 (k:Nat) (S:Finset Nat):List Bool:=(layout k).map (fun v=>decide (v∈ S))
def i8 (t:Nat):Nat:=(t+1).log2+ 1
def j5 (k t : Nat) (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset Nat)
    (i:Fin (t+1)):List Bool :=
  bits (i8 t) (par i).val++a9 k (B i)
def treeword (k t : Nat) (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset Nat) :
    List Bool :=
  header (t+1)++(List.finRange (t+1)).flatMap (j5 k t par B)
def j8 {k:Nat} (r:Finset (Fin k × Fin k) × Bool):List Bool:=r.2::mask r.1
def a8 (k w : Nat) (E P H : Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool))
    (t:Nat) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat):List Bool :=
  header k++header w++mask E++mask P++mask H++header rows.length ++
    rows.flatMap j8++treeword k t par B
lemma q0 {k:Nat} (e:Fin k × Fin k):e∈ pairs k↔ e.1< e.2:=by
  obtain ⟨a,b⟩:=e
  simp [pairs]
lemma a2z (a n:Nat) :
    ((List.range n).filter (fun j=>decide (a< j))).length= n - (a+1):=by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [List.range_succ,List.filter_append,List.length_append,ih]
    by_cases h:a< n
    · simp [h]; omega
    · simp [h]; omega
lemma a1m (n:Nat) (i:Fin n) :
    ((List.finRange n).filter (fun j=>decide (i< j))).length= n - (i.val+1):=by
  rw [← a2z i.val n,← List.map_coe_finRange_eq_range,List.filter_map,
    List.length_map]
  rfl
lemma a90 (k:Nat) :
    ((List.range k).map (fun i=>k - (i+1))).sum= k.choose 2:=by
  induction k with
  | zero=>simp
  | succ k ih =>
    rw [List.range_succ_eq_map,List.map_cons,List.sum_cons,List.map_map]
    have:((List.range k).map ((fun i=>k+ 1 - (i+ 1))∘ Nat.succ)) =
        (List.range k).map (fun i=>k - (i+1)):=by
      apply List.map_congr_left; intro i _; simp
    rw [this,ih,Nat.choose_succ_succ,Nat.choose_one_right]
    simp
lemma a48 (k:Nat):(pairs k).length= k.choose 2:=by
  rw [pairs,List.length_flatMap]
  simp only [List.length_map,a1m]
  rw [← a90 k,← List.map_coe_finRange_eq_range,List.map_map]
  rfl
def b6 (k:Nat):Nat:=k* (k - 1) / 2
lemma s8 (k:Nat):(pairs k).length= b6 k:=by
  rw [a48,Nat.choose_two_right,b6]
lemma a0q {α β:Type} (L:List α) (f:α→ List β) (c:Nat)
    (hf:∀ a,(f a).length= c):(L.flatMap f).length= L.length* c:=by
  induction L with
  | nil=>simp
  | cons a L ih=>simp [List.flatMap_cons,hf,ih,Nat.succ_mul]; omega
def m1:List Bool→ Nat × List Bool
  | []=>(0,[])
  | false::r=>(0,r)
  | true::r=>((m1 r).1+ 1,(m1 r).2)
lemma a5g (z:Nat) (r:List Bool) :
    m1 (header z++r)= (z,r):=by
  induction z with
  | zero=>simp [header,m1]
  | succ n ih =>
    simp only [header,List.replicate_succ,List.cons_append,List.append_assoc] at ih ⊢
    simp only [m1,ih]
def a28:Nat→ Nat→ List Bool→ List (List Bool) × List Bool
  | 0,_,l=>([],l)
  | n+1,len,l=>(l.take len::(a28 n len (l.drop len)).1,(a28 n len (l.drop len)).2)
lemma a0s {α:Type} (f:α→ List Bool) (len:Nat)
    (hf:∀ a,(f a).length= len) :
    ∀ (L : List α) (n : Nat), L.length = n → ∀ r : List Bool,
      a28 n len (L.flatMap f++r)= (L.map f,r)
  | [],n,hn,r=>by subst hn; simp [a28]
  | a :: L, n, hn, r => by
    subst hn
    have h:=a0s f len hf L L.length rfl r
    simp only [List.length_cons,a28,List.flatMap_cons,List.append_assoc,List.map_cons]
    rw [List.take_left' (hf a),List.drop_left' (hf a),h]
structure Data where
  k:Nat
  w:Nat
  E:List Bool
  P:List Bool
  H:List Bool
  rows:List (Bool × List Bool)
  t:Nat
  nodes:List (List Bool × List Bool)
def c9 (x:List Bool):Data :=
  let k:=(m1 x).1
  let x1:=(m1 x).2
  let w:=(m1 x1).1
  let x2:=(m1 x1).2
  let m:=b6 k
  let x3:=x2.drop m
  let x4:=x3.drop m
  let x5:=x4.drop m
  let n:=(m1 x5).1
  let x6:=(m1 x5).2
  let rs:=a28 n (m+1) x6
  let t1:=(m1 rs.2).1
  let x8:=(m1 rs.2).2
  let pw:=t1.log2+ 1
  let ns:=(a28 t1 (pw+ (k+ m)) x8).1
  { k := k, w := w, E := x2.take m, P := x3.take m, H := x4.take m,
    rows:=rs.1.map (fun r=>(r.headD false,r.tail)),
    t:=t1 - 1,
    nodes:=ns.map (fun c=>(c.take pw,c.drop pw)) }
lemma a10 {k:Nat} (A:Finset (Fin k × Fin k)):(mask A).length= b6 k:=by
  rw [mask,List.length_map,s8]
lemma a44 (k:Nat):(layout k).length= k+ b6 k:=by
  rw [layout,List.length_append,List.length_range,List.length_map,s8]
lemma k2 (w v:Nat):(bits w v).length= w:=by
  simp [bits]
lemma m2 (k:Nat) (S:Finset Nat):(a9 k S).length= k+ b6 k:=by
  rw [a9,List.length_map,a44]
lemma a07 {k:Nat} (r:Finset (Fin k × Fin k) × Bool) :
    (j8 r).length= b6 k+ 1:=by
  rw [j8,List.length_cons,a10]
lemma a0n (k t:Nat) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat)
    (i:Fin (t+1)):(j5 k t par B i).length= i8 t+ (k+ b6 k):=by
  rw [j5,List.length_append,k2,m2]
def o7 (k w : Nat) (E P H : Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat):Data :=
  { k := k, w := w, E := mask E, P := mask P, H := mask H,
    rows:=rows.map (fun r=>(r.2,mask r.1)),
    t:=t,
    nodes:=(List.finRange (t+1)).map
      (fun i=>(bits (i8 t) (par i).val,a9 k (B i))) }
lemma o8 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) :
    c9 (a8 k w E P H rows t par B)= o7 k w E P H rows t par B:=by
  have e1:a8 k w E P H rows t par B= header k++(header w++(mask E++(mask P ++
      (mask H++(header rows.length++(rows.flatMap j8++(header (t+1) ++
      ((List.finRange (t+1)).flatMap (j5 k t par B)++[])))))))):=by
    simp [a8,treeword]
  have hr:=a0s j8 (b6 k+ 1) a07 rows rows.length rfl
  have hn:=a0s (j5 k t par B) ((t+1).log2+ 1+ (k+ b6 k))
    (a0n k t par B) (List.finRange (t+1)) (t+1) (List.length_finRange)
  rw [c9,e1,o7]
  simp only [a5g,List.take_left' (a10 _),List.drop_left' (a10 _),
    hr,hn]
  simp only [List.map_map,Data.mk.injEq,true_and,Nat.add_sub_cancel]
  constructor
  · apply List.map_congr_left; intro r _; simp [j8]
  · apply List.map_congr_left; intro i _
    simp only [Function.comp,j5,i8]
    rw [List.take_left' (k2 _ _),List.drop_left' (k2 _ _)]
def a1a:List Bool→ Nat
  | []=>0
  | b::l=>b.toNat+ 2* a1a l
lemma a8u (w v:Nat):bits (w+1) v= v.testBit 0::bits w (v / 2):=by
  simp only [bits,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left; intro h _
  simp [Nat.testBit_succ]
lemma a09 (w v:Nat) (h:v< 2^w):a1a (bits w v)= v:=by
  induction w generalizing v with
  | zero=>simp at h; subst h; rfl
  | succ w ih =>
    rw [a8u,a1a,ih (v/2) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h)]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> simp [h2] <;> omega
lemma u5 (t:Nat) (v:Nat) (h:v< t+1):v< 2 ^ i8 t :=
  lt_trans h Nat.lt_log2_self
lemma b2v (t:Nat) (par:Fin (t+1)→ Fin (t+1)) (i:Fin (t+1)) :
    a1a (bits (i8 t) (par i).val)= (par i).val :=
  a09 _ _ (u5 t _ (par i).isLt)
lemma a4z {α β:Type} (l:List α) (f:α→ β) :
    l.zip (l.map f)= l.map (fun a=>(a,f a)):=by
  induction l <;> simp_all
def o9 (k:Nat) (bs:List Bool):Finset (Fin k × Fin k) :=
  ((((pairs k).zip bs).filter (fun p=>p.2)).map Prod.fst).toFinset
lemma a18 {k:Nat} (A:Finset (Fin k × Fin k)) (e:Fin k × Fin k) :
    e∈ o9 k (mask A)↔ e∈ A∧ e.1< e.2:=by
  simp only [o9,mask,a4z,List.mem_toFinset,List.mem_map,List.mem_filter,
    q0]
  constructor
  · rintro ⟨_,⟨⟨a,ha,rfl⟩,h⟩,rfl⟩; exact ⟨of_decide_eq_true h,ha⟩
  · rintro ⟨h1,h2⟩; exact ⟨(e,true),⟨⟨e,h2,by simp [h1]⟩,rfl⟩,rfl⟩
lemma v5 {k:Nat} (A:Finset (Fin k × Fin k)) :
    o9 k (mask A)= A.filter (fun e=>e.1< e.2):=by
  ext e; rw [a18,Finset.mem_filter]
lemma w6 {k:Nat} (A:Finset (Fin k × Fin k)) (hA:∀ e∈ A,e.1< e.2) :
    o9 k (mask A)= A:=by
  ext e; rw [a18]; exact ⟨fun h=>h.1,fun h=>⟨h,hA e h⟩⟩
lemma a0p (k v:Nat) :
    v∈ layout k↔ v< k∨ ∃ e:Fin k × Fin k,e.1< e.2∧ tag k e= v:=by
  simp [layout,q0]
def a16 (k:Nat) (bs:List Bool):Finset Nat :=
  ((((layout k).zip bs).filter (fun p=>p.2)).map Prod.fst).toFinset
lemma a33 (k:Nat) (S:Finset Nat) (v:Nat) :
    v∈ a16 k (a9 k S)↔ v∈ S∧ v∈ layout k:=by
  simp only [a16,a9,a4z,List.mem_toFinset,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨_,⟨⟨a,ha,rfl⟩,h⟩,rfl⟩; exact ⟨of_decide_eq_true h,ha⟩
  · rintro ⟨h1,h2⟩; exact ⟨(v,true),⟨⟨v,h2,by simp [h1]⟩,rfl⟩,rfl⟩
lemma a2u {k:Nat} (E:Finset (Fin k × Fin k)) (hE:∀ e∈ E,e.1< e.2) :
    ∀ v∈ (Finset.range k∪ E.image (tag k)),v∈ layout k:=by
  intro v hv
  rw [a0p]
  simp only [Finset.mem_union,Finset.mem_range,Finset.mem_image] at hv
  rcases hv with h | ⟨e,he,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e,hE e he,rfl⟩
lemma a5f {k:Nat} (E:Finset (Fin k × Fin k)) (hE:∀ e∈ E,e.1< e.2)
    (S:Finset Nat) (hS:S⊆ Finset.range k∪ E.image (tag k)) :
    a16 k (a9 k S)= S:=by
  ext v; rw [a33]
  exact ⟨fun h=>h.1,fun h=>⟨h,a2u E hE v (hS h)⟩⟩
def a51 (k n:Nat) (cnt:Nat→ Nat→ Nat):List Bool :=
  (List.range (k/2+1)).flatMap (fun s=>(List.range (n+1)).flatMap
    (fun j=>bits (b6 k+ 1) (cnt s j)))
lemma a5r {k:Nat} (E:Finset (Fin k × Fin k)) (hE:∀ e∈ E,e.1< e.2) :
    E.card≤ b6 k:=by
  have:E⊆ (pairs k).toFinset:=fun e he=>by
    rw [List.mem_toFinset,q0]; exact hE e he
  calc E.card ≤ (pairs k).toFinset.card := Finset.card_le_card this
    _≤ (pairs k).length:=List.toFinset_card_le _
    _= b6 k:=s8 k
lemma a13 (k:Nat) (e:Fin k × Fin k):k≤ tag k e:=by
  simp only [tag]; omega
lemma y6 (k:Nat):Function.Injective (tag k):=by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simp only [tag] at h
  have hk:0< k:=Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have h1:b.val+ a.val* k= d.val+ c.val* k:=by omega
  have h2:=congrArg (· % k) h1
  have h3:=congrArg (· / k) h1
  simp only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt b.isLt,Nat.mod_eq_of_lt d.isLt] at h2
  simp only [Nat.add_mul_div_right _ _ hk,Nat.div_eq_of_lt b.isLt,Nat.div_eq_of_lt d.isLt,
    zero_add] at h3
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext h3,Fin.ext h2⟩
lemma a3k {k:Nat} (Q A:Finset (Fin k × Fin k))
    (hQ:∀ e∈ Q,e.1< e.2):Q⊆ o9 k (mask A)↔ Q⊆ A:=by
  rw [v5]
  constructor
  · intro h e he; exact (Finset.mem_filter.mp (h he)).1
  · intro h e he; exact Finset.mem_filter.mpr ⟨h he,hQ e he⟩
lemma a0y {k:Nat} (Q A:Finset (Fin k × Fin k))
    (hQ:∀ e∈ Q,e.1< e.2):(Q∩ o9 k (mask A)).Nonempty↔ (Q∩ A).Nonempty:=by
  rw [v5]
  constructor
  · rintro ⟨e, he⟩
    rw [Finset.mem_inter,Finset.mem_filter] at he
    exact ⟨e,Finset.mem_inter.mpr ⟨he.1,he.2.1⟩⟩
  · rintro ⟨e, he⟩
    rw [Finset.mem_inter] at he
    exact ⟨e,Finset.mem_inter.mpr ⟨he.1,Finset.mem_filter.mpr ⟨he.2,hQ e he.1⟩⟩⟩
lemma a66 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat):(c9 (a8 k w E P H rows t par B)).k= k:=by
  rw [o8]; rfl
lemma b06 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat):(c9 (a8 k w E P H rows t par B)).t= t:=by
  rw [o8]; rfl
lemma q8 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) :
    (c9 (a8 k w E P H rows t par B)).rows.length= rows.length:=by
  rw [o8,o7,List.length_map]
def t5 (k : Nat) (E P H : Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (s j:Nat):Nat :=
  let ends:=fun e:Fin k × Fin k=>({e.1,e.2}:Finset (Fin k))
  let valid:=fun Q:Finset (Fin k × Fin k)=>Q⊆ E ∧
    ∀ e∈ Q,∀ f∈ Q,e≠ f→ Disjoint (ends e) (ends f)
  let score:=fun Q:Finset (Fin k × Fin k)=>(rows.filter
    (fun r=>decide (decide ((Q∩ r.1).Nonempty)= r.2))).length
  (E.powerset.filter (fun Q =>
    valid Q∧ P⊆ Q∧ Disjoint Q H∧ Q.card= s∧ score Q= j)).card
def f7 (k : Nat) (E : Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (width t:Nat)
    (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat):Prop :=
  let ends:=fun e:Fin k × Fin k=>({e.1,e.2}:Finset (Fin k))
  let valid:=fun Q:Finset (Fin k × Fin k)=>Q⊆ E ∧
    ∀ e∈ Q,∀ f∈ Q,e≠ f→ Disjoint (ends e) (ends f)
  let signed:=fun Q:Finset (Fin k × Fin k) =>
    ((rows.filter (fun t=>t.2 && decide (Q⊆ t.1))).length:Int) -
      ((rows.filter (fun t=>!t.2 && decide (Q⊆ t.1))).length:Int)
  let together:=fun e f=>∃ Q,valid Q∧ e∈ Q∧ f∈ Q∧ signed Q≠ 0
  let tag:=fun e:Fin k × Fin k=>k+e.1.val*k+e.2.val
  let vertices:=(Finset.range k)∪ E.image tag
  par 0= 0∧ (∀ i,i≠ 0→ par i< i) ∧
    (∀ i,B i⊆ vertices∧ (B i).card≤ width+1) ∧
    (∀ v∈ vertices,∃ a,v∈ B a∧ ∀ i,v∈ B i→ i≠ a→ i≠ 0∧ v∈ B (par i)) ∧
    (∀ e∈ E,(∃ i,tag e∈ B i∧ e.1.val∈ B i)∧ (∃ i,tag e∈ B i∧ e.2.val∈ B i)) ∧
    ∀ e∈ E,∀ f∈ E,e≠ f→ together e f→ ∃ i,tag e∈ B i∧ tag f∈ B i
def a59 (k : Nat) (E P H : Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)):List Bool :=
  (List.range (k/2+1)).flatMap (fun s=>(List.range (rows.length+1)).flatMap
    (fun j=>bits ((pairs k).length+1) (t5 k E P H rows s j)))
def dE (d:Data):Finset (Fin d.k × Fin d.k):=o9 d.k d.E
def dP (d:Data):Finset (Fin d.k × Fin d.k):=o9 d.k d.P
def dH (d:Data):Finset (Fin d.k × Fin d.k):=o9 d.k d.H
def r6 (d:Data):List (Finset (Fin d.k × Fin d.k) × Bool) :=
  d.rows.map (fun r=>(o9 d.k r.2,r.1))
def a52 (d:Data) (i:Nat):List Bool × List Bool:=d.nodes.getD i ([],[])
def a6i (d:Data):Fin (d.t+1)→ Fin (d.t+1) :=
  fun i=>⟨a1a (a52 d i.val).1 % (d.t+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
def dB (d:Data):Fin (d.t+1)→ Finset Nat:=fun i=>a16 d.k (a52 d i.val).2
def a57 (C:Data→ Nat→ Nat→ Nat) (d:Data):List Bool :=
  a51 d.k d.rows.length (C d)
lemma v6 (k:Nat) (bs:List Bool):∀ e∈ o9 k bs,e.1< e.2:=by
  intro e he
  simp only [o9,List.mem_toFinset,List.mem_map,List.mem_filter] at he
  obtain ⟨⟨a,b⟩,⟨hp,_⟩,rfl⟩:=he
  exact (q0 _).mp (List.of_mem_zip hp).1
lemma a1n (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hE:∀ e∈ E,e.1< e.2) :
    dE (o7 k w E P H rows t par B)= E:=w6 E hE
lemma a3n (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hP:∀ e∈ P,e.1< e.2) :
    dP (o7 k w E P H rows t par B)= P:=w6 P hP
lemma b29 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hH:∀ e∈ H,e.1< e.2) :
    dH (o7 k w E P H rows t par B)= H:=w6 H hH
def z3 {k : Nat} (rows : List (Finset (Fin k × Fin k) × Bool)) :
    List (Finset (Fin k × Fin k) × Bool) :=
  rows.map (fun r=>(r.1.filter (fun e=>e.1< e.2),r.2))
lemma a47 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) :
    r6 (o7 k w E P H rows t par B)= z3 rows:=by
  simp only [r6,o7,z3,List.map_map]
  apply List.map_congr_left; intro r _
  simp [v5]
lemma a43 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (i:Fin (t+1)) :
    a52 (o7 k w E P H rows t par B) i.val =
      (bits (i8 t) (par i).val,a9 k (B i)):=by
  simp [a52,o7,List.getElem?_eq_getElem (show i.val< (List.finRange (t+1)).length by
    rw [List.length_finRange]; exact i.isLt)]
lemma a4j (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (i:Fin (t+1)) :
    a6i (o7 k w E P H rows t par B) i= par i:=by
  apply Fin.ext
  show a1a (a52 (o7 k w E P H rows t par B) i.val).1 % (t+1)= (par i).val
  rw [a43,b2v,Nat.mod_eq_of_lt (par i).isLt]
lemma b08 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) :
    a6i (o7 k w E P H rows t par B)= par :=
  funext (fun i=>a4j k w E P H rows t par B i)
lemma b37 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hE:∀ e∈ E,e.1< e.2)
    (hB:∀ i,B i⊆ Finset.range k∪ E.image (tag k)) :
    dB (o7 k w E P H rows t par B)= B :=
  funext (fun (i:Fin (t+1))=>by
    show a16 k (a52 (o7 k w E P H rows t par B) i.val).2= B i
    rw [a43]
    exact a5f E hE (B i) (hB i))
lemma a1p {k:Nat} (Q A:Finset (Fin k × Fin k))
    (hQ:∀ e∈ Q,e.1< e.2) :
    (Q∩ A.filter (fun e=>e.1< e.2)).Nonempty↔ (Q∩ A).Nonempty:=by
  rw [← v5]; exact a0y Q A hQ
lemma a1k {k:Nat} (Q A:Finset (Fin k × Fin k))
    (hQ:∀ e∈ Q,e.1< e.2):Q⊆ A.filter (fun e=>e.1< e.2)↔ Q⊆ A:=by
  rw [← v5]; exact a3k Q A hQ
lemma a8y {k:Nat} (rows:List (Finset (Fin k × Fin k) × Bool))
    (Q:Finset (Fin k × Fin k)) (hQ:∀ e∈ Q,e.1< e.2) :
    ((z3 rows).filter (fun r=>decide (decide ((Q∩ r.1).Nonempty)= r.2))).length =
      (rows.filter (fun r=>decide (decide ((Q∩ r.1).Nonempty)= r.2))).length:=by
  rw [z3,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro r _
  simp only [Function.comp_apply,a1p Q r.1 hQ]
lemma a5h {k:Nat} (rows:List (Finset (Fin k × Fin k) × Bool))
    (Q:Finset (Fin k × Fin k)) (hQ:∀ e∈ Q,e.1< e.2) :
    ((z3 rows).filter (fun t=>t.2 && decide (Q⊆ t.1))).length =
      (rows.filter (fun t=>t.2 && decide (Q⊆ t.1))).length:=by
  rw [z3,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro r _
  simp only [Function.comp_apply,a1k Q r.1 hQ]
lemma a5i {k:Nat} (rows:List (Finset (Fin k × Fin k) × Bool))
    (Q:Finset (Fin k × Fin k)) (hQ:∀ e∈ Q,e.1< e.2) :
    ((z3 rows).filter (fun t=>!t.2 && decide (Q⊆ t.1))).length =
      (rows.filter (fun t=>!t.2 && decide (Q⊆ t.1))).length:=by
  rw [z3,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro r _
  simp only [Function.comp_apply,a1k Q r.1 hQ]
lemma a5j {k:Nat} (E P H:Finset (Fin k × Fin k)) (hE:∀ e∈ E,e.1< e.2)
    (rows:List (Finset (Fin k × Fin k) × Bool)) (s j:Nat) :
    t5 k E P H (z3 rows) s j= t5 k E P H rows s j:=by
  simp only [t5]
  refine congrArg Finset.card (Finset.filter_congr fun Q hQ=>?_)
  have hQ':∀ e∈ Q,e.1< e.2:=fun e he=>hE e (Finset.mem_powerset.mp hQ he)
  rw [a8y rows Q hQ']
lemma a4c {k:Nat} (E:Finset (Fin k × Fin k)) (hE:∀ e∈ E,e.1< e.2)
    (rows:List (Finset (Fin k × Fin k) × Bool)) (width t:Nat)
    (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat)
    (h:f7 k E rows width t par B):f7 k E (z3 rows) width t par B:=by
  simp only [f7] at h ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
  refine ⟨h1,h2,h3,h4,h5,fun e he f hf hef hto=>h6 e he f hf hef ?_⟩
  obtain ⟨Q,hv,heQ,hfQ,hs⟩:=hto
  have hQ':∀ e∈ Q,e.1< e.2:=fun e he=>hE e (hv.1 he)
  refine ⟨Q,hv,heQ,hfQ,?_⟩
  rwa [a5h rows Q hQ',a5i rows Q hQ'] at hs
lemma a77 {k:Nat} (E:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (width t:Nat)
    (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat)
    (h:f7 k E rows width t par B) :
    ∀ i,B i⊆ Finset.range k∪ E.image (tag k):=fun i=>(h.2.2.1 i).1
lemma a46 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat)
    (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) (hH:∀ e∈ H,e.1< e.2) (s j:Nat) :
    t5 (c9 (a8 k w E P H rows t par B)).k
      (dE (c9 (a8 k w E P H rows t par B)))
      (dP (c9 (a8 k w E P H rows t par B)))
      (dH (c9 (a8 k w E P H rows t par B)))
      (r6 (c9 (a8 k w E P H rows t par B))) s j =
    t5 k E P H rows s j:=by
  rw [o8,a1n k w E P H rows t par B hE,a3n k w E P H rows t par B hP,
    b29 k w E P H rows t par B hH,a47]
  exact a5j E P H hE rows s j
lemma a38 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hE:∀ e∈ E,e.1< e.2)
    (hdec:f7 k E rows w t par B) :
    f7 (c9 (a8 k w E P H rows t par B)).k
      (dE (c9 (a8 k w E P H rows t par B)))
      (r6 (c9 (a8 k w E P H rows t par B)))
      (c9 (a8 k w E P H rows t par B)).w
      (c9 (a8 k w E P H rows t par B)).t
      (a6i (c9 (a8 k w E P H rows t par B)))
      (dB (c9 (a8 k w E P H rows t par B))):=by
  have hB:=a77 E rows w t par B hdec
  rw [o8,a1n k w E P H rows t par B hE,a47,b08,
    b37 k w E P H rows t par B hE hB]
  exact a4c E hE rows w t par B hdec
lemma o6 {α β:Type} (l:List α) (f g:α→ List β)
    (h:∀ a∈ l,f a= g a):l.flatMap f= l.flatMap g:=by
  induction l with
  | nil=>rfl
  | cons a l ih =>
    rw [List.flatMap_cons,List.flatMap_cons,h a List.mem_cons_self,
      ih (fun b hb=>h b (List.mem_cons_of_mem a hb))]
lemma a8x (C:Data→ Nat→ Nat→ Nat) (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat)
    (hC:∀ s j,s≤ k/2→ j≤ rows.length →
      C (c9 (a8 k w E P H rows t par B)) s j= t5 k E P H rows s j) :
    a57 C (c9 (a8 k w E P H rows t par B))= a59 k E P H rows:=by
  unfold a57 a59 a51
  rw [a66,q8,s8]
  apply o6; intro s hs
  apply o6; intro j hj
  rw [List.mem_range] at hs hj
  rw [hC s j (by omega) (by omega)]
def a41
    (t0:(k w:Nat)→ Finset (Fin k × Fin k)→ Finset (Fin k × Fin k) →
      Finset (Fin k × Fin k)→ List (Finset (Fin k × Fin k) × Bool)→ (t:Nat) →
      (Fin (t+1)→ Fin (t+1))→ (Fin (t+1)→ Finset Nat)→ Nat→ Nat→ Nat)
    (d:Data):Nat→ Nat→ Nat :=
  t0 d.k d.w (dE d) (dP d) (dH d) (r6 d) d.t (a6i d) (dB d)
lemma b39
    (t0:(k w:Nat)→ Finset (Fin k × Fin k)→ Finset (Fin k × Fin k) →
      Finset (Fin k × Fin k)→ List (Finset (Fin k × Fin k) × Bool)→ (t:Nat) →
      (Fin (t+1)→ Fin (t+1))→ (Fin (t+1)→ Finset Nat)→ Nat→ Nat→ Nat)
    (hdp:∀ (k w:Nat) (E P H:Finset (Fin k × Fin k))
      (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
      (B:Fin (t+1)→ Finset Nat),
      (∀ e∈ E,e.1< e.2)→ (∀ e∈ P,e.1< e.2)→ (∀ e∈ H,e.1< e.2) →
      f7 k E rows w t par B→ ∀ s j,s≤ k/2→ j≤ rows.length →
      t0 k w E P H rows t par B s j= t5 k E P H rows s j)
    (k w:Nat) (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
    (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) (hH:∀ e∈ H,e.1< e.2)
    (t:Nat) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat)
    (hdec:f7 k E rows w t par B) :
    a57 (a41 t0) (c9 (a8 k w E P H rows t par B)) =
      a59 k E P H rows:=by
  refine a8x _ k w E P H rows t par B (fun s j hs hj=>?_)
  have hs':s≤ (c9 (a8 k w E P H rows t par B)).k / 2:=by
    rw [a66]; exact hs
  have hj':j≤ (r6 (c9 (a8 k w E P H rows t par B))).length:=by
    rw [r6,List.length_map,q8]; exact hj
  exact (hdp _ _ _ _ _ _ _ _ _ (v6 _ _) (v6 _ _) (v6 _ _)
    (a38 k w E P H rows t par B hE hdec) s j hs' hj').trans
    (a46 k w E P H rows t par B hE hP hH s j)
end Dec
end asmP3
section asmP4
namespace Dec
open Lib.Universal
def a14 (s:List Bool):List Bool:=un (s.length / 2)
lemma a6v:∀ s:List Bool,
    Lib.Machines.c7 (fun (q _:Bool)=>(!q,if q then some true else none))
      (fun _=>none) false s= a14 s ∧
    Lib.Machines.c7 (fun (q _:Bool)=>(!q,if q then some true else none))
      (fun _=>none) true s= un ((s.length+ 1) / 2)
  | []=>⟨rfl,rfl⟩
  | b :: l => by
    obtain ⟨h1,h2⟩:=a6v l
    refine ⟨?_,?_⟩
    · simp [Lib.Machines.c7,h2,a14]
    · rw [show un (((b::l).length+ 1) / 2)= true::un (l.length / 2) by
          rw [← a1w]; congr 1; simp; omega]
      simp [Lib.Machines.c7,h1,a14]
lemma a6x:a4 a14 :=
  Lib.Machines.g0 _ _ _ (fun (q _:Bool)=>(!q,if q then some true else none))
    (fun _=>none) false (fun s=>(a6v s).1.symm)
def b0o (y:List Bool):List Bool:=r5 y
def psK (y:List Bool):List Bool:=hd (b0o y)
def b24 (y:List Bool):List Bool:=r5 (b0o y)
def psW (y:List Bool):List Bool:=hd (b24 y)
def a8d (y:List Bool):List Bool:=r5 (b24 y)
def psM (y:List Bool):List Bool:=a14 (j0 (psK y) (psK y).tail)
def a7q (y:List Bool):List Bool:=g8 (psM y) (a8d y)
def b02 (y:List Bool):List Bool:=g8 (psM y) (a7q y)
def b1z (y:List Bool):List Bool:=g8 (psM y) (b02 y)
def psN (y:List Bool):List Bool:=hd (b1z y)
def a86 (y:List Bool):List Bool:=r5 (b1z y)
def a89 (y:List Bool):List Bool:=j0 (psN y) ([true]++psM y)
def a7j (y:List Bool):List Bool:=g8 (a89 y) (a86 y)
def psT (y:List Bool):List Bool:=hd (a7j y)
def p5 (y:List Bool):List Bool :=
  a1 (hd y) (a1 (psK y) (a1 (psW y) (a1 (psM y)
    (a1 (m4 (psM y) (a8d y)) (a1 (m4 (psM y) (a7q y))
    (a1 (m4 (psM y) (b02 y)) (a1 (psN y) (a1 (m4 (a89 y) (a86 y))
    (a1 (psT y) (a1 (unL (s5 (psT y))) (r5 (a7j y))))))))))))
lemma b0e:a4 b0o:=z8
lemma y9:a4 psK:=b7 (Lib.Machines.a2 b0e a2d) (fun _=>rfl)
lemma b0n:a4 b24:=b7 (Lib.Machines.a2 b0e z8) (fun _=>rfl)
lemma b1g:a4 psW:=b7 (Lib.Machines.a2 b0n a2d) (fun _=>rfl)
lemma a5q:a4 a8d:=b7 (Lib.Machines.a2 b0n z8) (fun _=>rfl)
lemma r7:a4 psM:=b7 (Lib.Machines.a2 (g9 y9 (Lib.Machines.a2 y9 o3)) a6x) (fun _=>rfl)
lemma a62:a4 a7q:=e8 r7 a5q
lemma a9u:a4 b02:=e8 r7 a62
lemma a9q:a4 b1z:=e8 r7 a9u
lemma a1q:a4 psN:=b7 (Lib.Machines.a2 a9q a2d) (fun _=>rfl)
lemma a5w:a4 a86:=b7 (Lib.Machines.a2 a9q z8) (fun _=>rfl)
lemma a65:a4 a89:=g9 a1q (b8 (b0 [true]) r7)
lemma a5t:a4 a7j:=e8 a65 a5w
lemma y8:a4 psT:=b7 (Lib.Machines.a2 a5t a2d) (fun _=>rfl)
lemma b2t:a4 p5:=b7 (
  a7 a2d (a7 y9 (a7 b1g (a7 r7
    (a7 (k4 r7 a5q) (a7 (k4 r7 a62)
    (a7 (k4 r7 a9u) (a7 a1q
    (a7 (k4 a65 a5w) (a7 y8
    (a7 (Lib.Machines.a2 (Lib.Machines.a2 y8 n9) a1u) (Lib.Machines.a2 a5t z8))))))))))))
  (fun _=>rfl)
lemma a4o (z:Nat) (r:List Bool):header z++r= un z++false::r:=by
  simp [header,un]
lemma a8q (p k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (y:List Bool) (hy:y= un p++false::a8 k w E P H rows t par B) :
    hd y= un p∧ psK y= un k∧ psW y= un w∧ psM y= un (b6 k) ∧
    m4 (psM y) (a8d y)= mask E∧ m4 (psM y) (a7q y)= mask P ∧
    m4 (psM y) (b02 y)= mask H∧ psN y= un rows.length ∧
    m4 (a89 y) (a86 y)= rows.flatMap j8∧ psT y= un (t+1) ∧
    r5 (a7j y)= (List.finRange (t+1)).flatMap (j5 k t par B):=by
  subst hy
  have e:a8 k w E P H rows t par B= un k++false::(un w++false::(mask E ++
      (mask P++(mask H++(un rows.length++false::(rows.flatMap j8 ++
      (un (t+1)++false::(List.finRange (t+1)).flatMap (j5 k t par B)))))))):=by
    simp only [a8,treeword,List.append_assoc,a4o,List.cons_append]
  have hR:(rows.flatMap j8).length= rows.length* ([true]++un (b6 k)).length:=by
    rw [a0q _ _ _ a07]; simp
  have hm:=a10 (k:=k)
  have hM:psM (un p++false::a8 k w E P H rows t par B)= un (b6 k):=by
    simp only [psM,psK,b0o,e,a61,a9c,a14,j0,b4,List.length_tail,
      b6]
  simp only [a7j,psT,a89,psN,a86,b1z,b02,a7q,a8d,psW,b24,psK,b0o,hM]
  simp only [e,a9c,a61,k7,i6,b4,List.take_left' (hm _),
    List.drop_left' (hm _),j0,← hR,List.take_left' rfl,List.drop_left' rfl,and_self]
lemma a45 (p k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) :
    p5 (un p++false::a8 k w E P H rows t par B) =
      a1 (un p) (a1 (un k) (a1 (un w) (a1 (un (b6 k))
        (a1 (mask E) (a1 (mask P) (a1 (mask H) (a1 (un rows.length)
        (a1 (rows.flatMap j8) (a1 (un (t+1))
        (a1 (un (i8 t)) ((List.finRange (t+1)).flatMap (j5 k t par B)))))))))))):=by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩:=a8q p k w E P H rows t par B _ rfl
  rw [p5,h4,h5,h6,h8,h10,h0,h1,h2,h3,h7,h9]
  simp only [unL,w7,b4,PEqualNP.Outside.L_lib_1048.k2 (t+1) (Nat.succ_pos t)]
  rfl
def j4:Nat→ List Bool→ List Bool
  | 0,z=>(a0 z).1
  | i+1,z=>j4 i (a0 z).2
def a31:Nat→ List Bool→ List Bool
  | 0,z=>z
  | i+1,z=>a31 i (a0 z).2
lemma a8e:∀ i,a4 (j4 i)
  | 0=>a6
  | i+1=>b7 (Lib.Machines.a2 a3 (a8e i)) (fun _=>rfl)
lemma a6m:∀ i,a4 (a31 i)
  | 0=>Lib.Machines.g5
  | i+1=>b7 (Lib.Machines.a2 a3 (a6m i)) (fun _=>rfl)
end Dec
end asmP4
section asmP5
namespace Dec
open Lib.Universal
def u1 (z:List Bool):List Bool:=(a0 z).1
def u2 (z:List Bool):List Bool:=(a0 z).2
lemma s7:a4 u1:=a6
lemma j2:a4 u2:=a3
def b5 (lenU iU s:List Bool):List Bool:=m4 lenU (g8 (j0 iU lenU) s)
lemma k5 {ul ui us:List Bool→ List Bool} (hl:a4 ul) (hi:a4 ui)
    (hs:a4 us):a4 (fun z=>b5 (ul z) (ui z) (us z)) :=
  b7 (k4 hl (e8 (g9 hi hl) hs)) (fun _=>rfl)
lemma u9 {α:Type} (f:α→ List Bool) (c:ℕ) (hf:∀ a,(f a).length= c) :
    ∀ (L:List α) (i:ℕ) (hi:i< L.length),((L.flatMap f).drop (i* c)).take c= f (L[i]'hi)
  | [],i,hi=>by simp at hi
  | a::L,0,_=>by simp [List.take_left' (hf a)]
  | a :: L, i+1, hi => by
    rw [List.flatMap_cons,show (i+ 1)* c= c+ i* c by ring,← List.drop_drop,
      List.drop_left' (hf a)]
    exact u9 f c hf L i (by simpa using hi)
lemma l8 {α:Type} (f:α→ List Bool) (c:ℕ) (hf:∀ a,(f a).length= c)
    (L:List α) (i:ℕ) (hi:i< L.length) (lenU iU:List Bool) (hl:lenU.length= c)
    (hiU:iU.length= i):b5 lenU iU (L.flatMap f)= f (L[i]'hi):=by
  rw [b5,k7,i6]
  simp only [j0,b4,hl,hiU]
  exact u9 f c hf L i hi
lemma a1d {α:Type} (h:α→ List Bool) :
    ∀ (L : List α) (g : ℕ → List Bool), (∀ j (hj : j < L.length), g j = h L[j]) →
      (List.range L.length).flatMap g= L.flatMap h
  | [],_,_=>rfl
  | a :: L, g, hg => by
    rw [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.flatMap_cons,hg 0 (by simp)]
    congr 1
    exact a1d h L _ (fun j hj=>hg (j+1) (by simpa using hj))
lemma b0s:∀ (n:Nat) (l:List Bool),val (l.drop n)= val l / 2 ^ n
  | 0,l=>by simp
  | n+1,[]=>by simp [val]
  | n+1, b :: l => by
    rw [List.drop_succ_cons,b0s n l,val,pow_succ',← Nat.div_div_eq_div_mul]
    congr 1; cases b <;> simp; omega
lemma a9n:∀ l:List Bool,bits l.length (val l)= l
  | []=>rfl
  | b :: l => by
    have h1:val (b::l) / 2= val l:=by simp only [val]; cases b <;> simp; omega
    have h2:(val (b::l)).testBit 0= b:=by
      rw [Nat.testBit_zero]; cases b <;> simp [val]
    rw [List.length_cons,a8u,h1,h2,a9n l]
lemma b4w (W n:Nat) (N:List Bool) :
    g4 (un W) (N.drop n)= bits W (val N / 2 ^ n % 2 ^ W):=by
  have h:=a9n (g4 (un W) (N.drop n))
  rw [i4,b4,w8,b4,b0s] at h
  exact h.symm
lemma b1x (W v:Nat):f3 (bits W v)= bits W 0:=by
  simp [f3,bits]
lemma a98 {α:Type} (l:List α) (f:α→ List Bool) :
    f3 (l.flatMap f)= l.flatMap (fun a=>f3 (f a)):=by
  simp [f3,List.map_flatMap]
def nF {α:Type} (rows:List (α × Bool)):Nat:=(rows.filter (fun r=>!r.2)).length
def gW (y:List Bool):List Bool:=[true]++psM y
def gR1 (y:List Bool):List Bool:=[true]++psN y
def gS1 (y:List Bool):List Bool:=[true]++a14 (psK y)
def b1y (y:List Bool):List Bool:=m4 (a89 y) (a86 y)
def gME (y:List Bool):List Bool:=m4 (psM y) (a8d y)
def gMP (y:List Bool):List Bool:=m4 (psM y) (a7q y)
def nfF (z:List Bool):List Bool:=sel (j3 (b5 (gW (u2 z)) (u1 z) (b1y (u2 z)))) [true] []
def gNF (y:List Bool):List Bool:=(List.range (psN y).length).flatMap (fun j=>nfF (a1 (un j) y))
def gD0 (y:List Bool):List Bool:=g8 (gNF y) (j0 (psN y++psN y) (psT y))
def gWt (y:List Bool):List Bool :=
  j0 (j0 (j0 (gW y) (gW y)) (gR1 y)) ([true]++(psT y++psT y++psT y++psT y))
def peF (z:List Bool):List Bool :=
  sel (j3 (g8 (u1 z) (gMP (u2 z)))) [] (sel (j3 (g8 (u1 z) (gME (u2 z)))) [true] [])
def gPE (y:List Bool):List Bool :=
  sel ((List.range (psM y).length).flatMap (fun q=>peF (a1 (un q) y))) [true] []
def a24 (y:List Bool):List Bool:=a1 (gW y) (a1 (gR1 y) (a1 (gD0 y) (a1 (gWt y) (gPE y))))
lemma a3d:a4 gW:=b8 (b0 [true]) r7
lemma a5b:a4 gR1:=b8 (b0 [true]) a1q
lemma b7t:a4 gS1:=b8 (b0 [true]) (b7 (Lib.Machines.a2 y9 a6x) (fun _=>rfl))
lemma b3b:a4 b1y:=k4 a65 a5w
lemma b7i:a4 gME:=k4 r7 a5q
lemma b7l:a4 gMP:=k4 r7 a62
lemma b7m:a4 nfF:=b7 (d6 (Lib.Machines.a2 (k5
  (Lib.Machines.a2 j2 a3d) s7 (Lib.Machines.a2 j2 b3b)) m6)
  (b0 [true]) (b0 [])) (fun _=>rfl)
lemma b86:a4 gNF:=b7 (d9 b7m a1q Lib.Machines.g5) (fun _=>rfl)
lemma b1l:a4 gD0:=e8 b86 (g9 (b8 a1q a1q) y8)
lemma b80:a4 gWt:=g9 (g9 (g9 a3d a3d) a5b)
  (b8 (b0 [true]) (b8 (b8 (b8 y8 y8) y8) y8))
lemma b88:a4 peF:=b7 (d6
  (Lib.Machines.a2 (e8 s7 (Lib.Machines.a2 j2 b7l)) m6)
  (b0 []) (d6
  (Lib.Machines.a2 (e8 s7 (Lib.Machines.a2 j2 b7i)) m6)
  (b0 [true]) (b0 []))) (fun _=>rfl)
lemma b1m:a4 gPE:=b7 (d6 (d9 b88 r7 Lib.Machines.g5)
  (b0 [true]) (b0 [])) (fun _=>rfl)
lemma b2w:a4 a24 :=
  a7 a3d (a7 a5b (a7 b1l (a7 b80 b1m)))
lemma b84 {k:Nat} (rows:List (Finset (Fin k × Fin k) × Bool)) :
    (rows.flatMap (fun r=>sel (j3 (j8 r)) [true] [])).length= nF rows:=by
  induction rows with
  | nil=>rfl
  | cons r rs ih =>
    obtain ⟨A,b⟩:=r
    cases b <;> simp [nF,j8,j3,sel] at ih ⊢ <;> omega
lemma a6s {k:Nat} (A:Finset (Fin k × Fin k)) (q:Nat) (hq:q< (pairs k).length) :
    j3 ((mask A).drop q)= if (pairs k)[q]∈ A then [true] else []:=by
  rw [List.drop_eq_getElem_cons (by rw [mask,List.length_map]; exact hq)]
  by_cases h:(pairs k)[q]∈ A <;> simp [mask,j3,h]
lemma a4y {k:Nat} (E P:Finset (Fin k × Fin k)) (hP:∀ e∈ P,e.1< e.2) :
    (pairs k).flatMap (fun e=>if e∈ P∧ e∉ E then [true] else [])= []↔ P⊆ E:=by
  simp only [List.flatMap_eq_nil_iff,ite_eq_right_iff,List.cons_ne_nil,imp_false,not_and,
    not_not]
  exact ⟨fun h e he=>h e ((q0 e).mpr (hP e he)) he,fun h e _ he=>h he⟩
lemma a0d (p k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hP:∀ e∈ P,e.1< e.2) (y:List Bool)
    (hy:y= un p++false::a8 k w E P H rows t par B) :
    gW y= un (b6 k+ 1)∧ gR1 y= un (rows.length+ 1)∧ gS1 y= un (k/2+ 1) ∧
    gD0 y= un (2* rows.length* (t+1) - nF rows) ∧
    gWt y= un ((b6 k+ 1)* (b6 k+ 1)* (rows.length+ 1)* (4* t+ 5)) ∧
    gPE y= (if P⊆ E then [true] else []):=by
  obtain ⟨-,hK,-,hM,hE,hP',-,hN,hR,hT,-⟩:=a8q p k w E P H rows t par B y hy
  have hW:gW y= un (b6 k+ 1):=by rw [gW,hM]; rfl
  have hNF:(gNF y).length= nF rows:=by
    rw [gNF,hN,b4,← b84]
    congr 1
    refine a1d _ rows _ (fun j hj=>?_)
    simp only [nfF,u1,u2,a5,hW,b1y,hR]
    rw [l8 j8 _ a07 rows j hj _ _ (by simp) (by simp)]
  refine ⟨hW,by rw [gR1,hN]; rfl,by rw [gS1,hK,a14,b4]; rfl,?_,?_,?_⟩
  · rw [gD0,i6,hNF,hN,hT,j0,List.length_append,b4,b4,
      show (rows.length+ rows.length)* (t+ 1)= 2* rows.length* (t+ 1) by ring]
    simp only [un,List.drop_replicate]
  · rw [gWt, hW, gR1, hN, hT]
    simp only [j0,b4,List.length_append,List.length_singleton]
    exact congrArg un (by ring)
  · rw [gPE, hM, b4]
    have hpl:=s8 k
    have hfl:(List.range (b6 k)).flatMap (fun q=>peF (a1 (un q) y)) =
        (pairs k).flatMap (fun e=>if e∈ P∧ e∉ E then [true] else []):=by
      rw [← hpl]
      refine a1d _ _ _ (fun q hq=>?_)
      simp only [peF,u1,u2,a5,gMP,gME,hE,hP',i6,b4,
        a6s _ q hq]
      by_cases h1:(pairs k)[q]∈ P <;> by_cases h2:(pairs k)[q]∈ E <;> simp [h1,h2,sel]
    rw [hfl]
    by_cases h:P⊆ E
    · simp only [h,↓reduceIte,(a4y E P hP).mpr h,sel]
    · have h':¬ ((pairs k).flatMap (fun e=>if e∈ P∧ e∉ E then [true] else [])= []) :=
        fun h'=>h ((a4y E P hP).mp h')
      simp only [h,h',↓reduceIte,sel]
def b2u (z:List Bool):List Bool :=
  g4 (gW (u2 (u2 (u2 z)))) (g8 (j0 (j0 (u1 (u2 z)) (gR1 (u2 (u2 (u2 z)))) ++
    (u1 z++gD0 (u2 (u2 (u2 z))))) (gW (u2 (u2 (u2 z))))) (u1 (u2 (u2 z))))
def b2o (z:List Bool):List Bool :=
  (List.range (gR1 (u2 (u2 z))).length).flatMap (fun j=>b2u (a1 (un j) z))
def a6o (z:List Bool):List Bool :=
  (List.range (gS1 (u2 z)).length).flatMap (fun s=>b2o (a1 (un s) z))
def b25 (z:List Bool):List Bool:=sel (gPE (u2 z)) (f3 (a6o z)) (a6o z)
lemma b4g:a4 b2u:=by
  have hy:a4 (fun z=>u2 (u2 (u2 z))) :=
    Lib.Machines.a2 (Lib.Machines.a2 j2 j2) j2
  exact b7 (n4 (Lib.Machines.a2 hy a3d) (e8 (g9 (b8
    (g9 (Lib.Machines.a2 j2 s7) (Lib.Machines.a2 hy a5b))
    (b8 s7 (Lib.Machines.a2 hy b1l))) (Lib.Machines.a2 hy a3d))
    (Lib.Machines.a2 (Lib.Machines.a2 j2 j2) s7))) (fun _=>rfl)
lemma b3p:a4 b2o:=b7 (d9 b4g
  (Lib.Machines.a2 (Lib.Machines.a2 j2 j2) a5b) Lib.Machines.g5) (fun _=>rfl)
lemma a8t:a4 a6o:=b7 (d9 b3p
  (Lib.Machines.a2 j2 b7t) Lib.Machines.g5) (fun _=>rfl)
lemma b5l:a4 b25 :=
  d6 (Lib.Machines.a2 j2 b1m) (Lib.Machines.a2 a8t n6) a8t
lemma b5f (N:List Bool) (p k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) (hP:∀ e∈ P,e.1< e.2) :
    b25 (a1 N (un p++false::a8 k w E P H rows t par B)) =
      (List.range (k/2+1)).flatMap (fun s=>(List.range (rows.length+1)).flatMap (fun j =>
        bits (b6 k+ 1) (if P⊆ E then val N / 2 ^ ((s* (rows.length+ 1) +
          (j+ (2* rows.length* (t+1) - nF rows)))* (b6 k+ 1)) % 2 ^ (b6 k+ 1)
          else 0))):=by
  obtain ⟨hW,hR1,hS1,hD0,-,hPE⟩:=a0d p k w E P H rows t par B hP _ rfl
  have hS:a6o (a1 N (un p++false::a8 k w E P H rows t par B)) =
      (List.range (k/2+1)).flatMap (fun s=>(List.range (rows.length+1)).flatMap (fun j =>
        bits (b6 k+ 1) (val N / 2 ^ ((s* (rows.length+ 1) +
          (j+ (2* rows.length* (t+1) - nF rows)))* (b6 k+ 1)) % 2 ^ (b6 k+ 1)))):=by
    simp only [a6o,b2o,b2u,u1,u2,a5,hW,hR1,hS1,hD0,b4,i6,
      j0,List.length_append,b4w]
  simp only [b25,u2,a5,hPE,hS]
  by_cases h:P⊆ E
  · simp [h,sel]
  · simp [h,sel,a98,b1x]
lemma a4n {α β:Type} (l:List α) (p:α→ Bool) (f:α→ List β) :
    (l.filter p).flatMap f= l.flatMap (fun a=>if p a then f a else []):=by
  induction l with
  | nil=>rfl
  | cons a l ih=>cases h:p a <;> simp [h,ih]
lemma a2c {β:Type} (n:Nat) (F:Nat→ List β) :
    (List.finRange n).flatMap (fun i=>F i.val)= (List.range n).flatMap F:=by
  rw [← List.map_coe_finRange_eq_range,List.flatMap_map]
lemma a94 (k:Nat) (g:Nat→ Nat→ List Bool) :
    (pairs k).flatMap (fun e=>g e.1.val e.2.val) =
      (List.range k).flatMap (fun a=>(List.range k).flatMap (fun b=>if a< b then g a b else [])):=by
  rw [pairs,List.flatMap_assoc,← a2c k]
  apply o6; intro i _
  rw [List.flatMap_map,a4n,← a2c k]
  apply o6; intro j _
  simp only [decide_eq_true_eq]; rfl
def epL (y:List Bool):List Bool:=[true]++(psK y++psK y)
def epF (z:List Bool):List Bool :=
  sel (g8 (u1 (u2 z)) (u1 z)) [] (g4 (epL (u2 (u2 z))) (u1 (u2 z)++([false]++u1 z)))
def epJ (z:List Bool):List Bool:=(List.range (psK (u2 z)).length).flatMap (fun b=>epF (a1 (un b) z))
def b93 (y:List Bool):List Bool:=(List.range (psK y).length).flatMap (fun a=>epJ (a1 (un a) y))
lemma b78:a4 epL:=b8 (b0 [true]) (b8 y9 y9)
lemma b6r:a4 epF:=b7 (d6 (e8 (Lib.Machines.a2 j2 s7) s7)
  (b0 []) (n4 (Lib.Machines.a2 (Lib.Machines.a2 j2 j2) b78)
  (b8 (Lib.Machines.a2 j2 s7) (b8 (b0 [false]) s7)))) (fun _=>rfl)
lemma b7g:a4 epJ:=b7 (d9 b6r (Lib.Machines.a2 j2 y9)
  Lib.Machines.g5) (fun _=>rfl)
lemma b57:a4 b93:=b7 (d9 b7g y9 Lib.Machines.g5) (fun _=>rfl)
def z5 (bb:List Bool):List Nat:=(List.range bb.length).filter (fun q=>bb.getD q false)
def mrL (y:List Bool):List Bool:=[true]++(psK y++psM y)
def mqF (z:List Bool):List Bool :=
  sel (j3 (g8 (u1 z) (u1 (u2 z)))) [] (g4 (mrL (u2 (u2 z))) ([true]++u1 z))
def b97 (z:List Bool):List Bool :=
  g4 (j0 ([true]++psW (u2 z)) (mrL (u2 z)))
    ((List.range (u1 z).length).flatMap (fun q=>mqF (a1 (un q) z)))
def ndL (y:List Bool):List Bool:=unL (s5 (psT y))++(psK y++psM y)
def b6g (z:List Bool):List Bool :=
  g8 (unL (s5 (psT (u2 z)))) (b5 (ndL (u2 z)) (u1 z) (r5 (a7j (u2 z))))
def b9s (z:List Bool):List Bool:=b97 (a1 (b6g z) (u2 z))
def b8z (y:List Bool):List Bool:=(List.range (psT y).length).flatMap (fun i=>b9s (a1 (un i) y))
lemma b1p:a4 mrL:=b8 (b0 [true]) (b8 y9 r7)
lemma b7f:a4 mqF:=b7 (d6 (Lib.Machines.a2 (e8 s7
  (Lib.Machines.a2 j2 s7)) m6) (b0 []) (n4
  (Lib.Machines.a2 (Lib.Machines.a2 j2 j2) b1p)
  (b8 (b0 [true]) s7))) (fun _=>rfl)
lemma b5a:a4 b97:=b7 (n4 (g9 (b8 (b0 [true])
  (Lib.Machines.a2 j2 b1g)) (Lib.Machines.a2 j2 b1p))
  (d9 b7f s7 Lib.Machines.g5)) (fun _=>rfl)
lemma b81:a4 ndL:=b8 (Lib.Machines.a2 (Lib.Machines.a2 y8
  n9) a1u) (b8 y9 r7)
lemma b3t:a4 b6g:=e8 (Lib.Machines.a2 (Lib.Machines.a2
  (Lib.Machines.a2 j2 y8) n9) a1u) (k5
  (Lib.Machines.a2 j2 b81) s7 (Lib.Machines.a2 (Lib.Machines.a2
  j2 a5t) z8))
lemma b5h:a4 b9s:=b7 (Lib.Machines.a2 (a7 b3t j2) b5a)
  (fun _=>rfl)
lemma b55:a4 b8z:=b7 (d9 b5h y8 Lib.Machines.g5)
  (fun _=>rfl)
def gZ (y:List Bool):List Bool:=a1 (p5 y) (a1 (a24 y) (a1 (b8z y) (b93 y)))
def G (mid:List Bool→ List Bool) (y:List Bool):List Bool:=b25 (a1 (mid (gZ y)) y)
lemma b9v:a4 gZ:=a7 b2t (a7 b2w (a7 b55 b57))
lemma G_cpt (mid:List Bool→ List Bool) (hmid:a4 mid):a4 (G mid) :=
  b7 (Lib.Machines.a2 (a7 (Lib.Machines.a2 b9v hmid) Lib.Machines.g5)
    b5l) (fun _=>rfl)
lemma a9p (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat) :
    nF (r6 (c9 (a8 k w E P H rows t par B)))= nF rows:=by
  rw [o8]
  simp [nF,r6,o7,List.filter_map,Function.comp_def]
abbrev b69:Type:=(k:Nat)→ Finset (Fin k × Fin k)→ Finset (Fin k × Fin k)→ Finset (Fin k × Fin k) →
      List (Finset (Fin k × Fin k) × Bool)→ (t:Nat)→ (Fin (t+1)→ Fin (t+1)) →
      (Fin (t+1)→ Finset Nat)→ Nat→ Nat→ Nat
def b1n (tot:b69):Prop :=
  ∀ (k w:Nat) (E P H:Finset (Fin k × Fin k))
      (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
      (B:Fin (t+1)→ Finset Nat),
      (∀ e∈ E,e.1< e.2)→ (∀ e∈ P,e.1< e.2)→ (∀ e∈ H,e.1< e.2) →
      f7 k E rows w t par B→ ∀ s j,s≤ k/2→ j≤ rows.length →
      (if P⊆ E then tot k E P H rows t par B s (j+ 2* rows.length* (t+1) - nF rows) else 0) =
        t5 k E P H rows s j
def a7f (tot:b69) (mid:List Bool→ List Bool):Prop :=
  ∀ (k w:Nat) (E P H:Finset (Fin k × Fin k))
      (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
      (B:Fin (t+1)→ Finset Nat),
      (∀ e∈ E,e.1< e.2)→ (∀ e∈ P,e.1< e.2)→ (∀ e∈ H,e.1< e.2) →
      f7 k E rows w t par B→ P⊆ E→ ∀ s j,s≤ k/2→ j≤ rows.length →
      val (mid (gZ (un (2^(w+1))++false::a8 k w E P H rows t par B))) /
        2 ^ ((s* (rows.length+ 1)+ (j+ (2* rows.length* (t+1) - nF rows)))* (b6 k+ 1))
        % 2 ^ (b6 k+ 1) =
      tot (c9 (a8 k w E P H rows t par B)).k (dE (c9 (a8 k w E P H rows t par B)))
        (dP (c9 (a8 k w E P H rows t par B))) (dH (c9 (a8 k w E P H rows t par B)))
        (r6 (c9 (a8 k w E P H rows t par B))) (c9 (a8 k w E P H rows t par B)).t
        (a6i (c9 (a8 k w E P H rows t par B))) (dB (c9 (a8 k w E P H rows t par B)))
        s (j+ 2* rows.length* (t+1) - nF rows)
lemma G_spec (mid:List Bool→ List Bool) (tot:b69) (htot:b1n tot) (hmid:a7f tot mid)
    (k w:Nat) (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
    (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) (hH:∀ e∈ H,e.1< e.2)
    (t:Nat) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset Nat)
    (hdec:f7 k E rows w t par B) :
    G mid (un (2^(w+1))++false::a8 k w E P H rows t par B)= a59 k E P H rows:=by
  rw [← b39 (fun k w E P H rows t par B s j =>
      if P⊆ E then tot k E P H rows t par B s (j+ 2* rows.length* (t+1) - nF rows) else 0)
    htot k w E P H rows hE hP hH t par B hdec,G,b5f _ _ k w E P H rows t par B hP]
  unfold a57 a41 a51
  simp only [a66,q8]
  apply o6; intro s hs; apply o6; intro j hj
  rw [List.mem_range] at hs hj
  have hsub:dP (c9 (a8 k w E P H rows t par B))⊆ dE (c9 (a8 k w E P H rows t par B))
      ↔ P⊆ E:=by
    rw [o8,a3n _ _ _ _ _ _ _ _ _ hP,a1n _ _ _ _ _ _ _ _ _ hE]
    exact Iff.rfl
  have hRl:(r6 (c9 (a8 k w E P H rows t par B))).length= rows.length:=by
    rw [r6,List.length_map,q8]
  by_cases h:P⊆ E
  · have h' := hsub.mpr h
    have he:j+ 2* (r6 (c9 (a8 k w E P H rows t par B))).length *
        ((c9 (a8 k w E P H rows t par B)).t+ 1) -
        nF (r6 (c9 (a8 k w E P H rows t par B))) =
        j+ 2* rows.length* (t+1) - nF rows:=by rw [hRl,b06,a9p]
    simp only [h,h',↓reduceIte]
    rw [hmid k w E P H rows t par B hE hP hH hdec h s j (by omega) (by omega),he]
  · have h':¬ (dP (c9 (a8 k w E P H rows t par B)) ⊆
        dE (c9 (a8 k w E P H rows t par B))):=fun h'=>h (hsub.mp h')
    rw [ite_eq_right h,ite_eq_right h']
end Dec
end asmP5
section asmP6
namespace Dec
open Lib.Universal
lemma a5y (k s:Nat) (hs:s≤ k / 2):s≤ b6 k:=by
  by_cases hk:2≤ k
  · exact le_trans hs (Nat.div_le_div_right (Nat.le_mul_of_pos_right k (by omega)))
  · have : k / 2 = 0 := by omega
    omega
lemma a93 (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat)
    (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) (hH:∀ e∈ H,e.1< e.2)
    (hd:f7 k E rows w t par B) (hPE:P⊆ E) (s j:Nat) (_hs:s≤ k/2)
    (_hj:j≤ rows.length) :
    t0 E P H rows par B s j =
      p3 (dE (c9 (a8 k w E P H rows t par B))) (dP (c9 (a8 k w E P H rows t par B)))
        (dH (c9 (a8 k w E P H rows t par B))) (r6 (c9 (a8 k w E P H rows t par B)))
        (a6i (c9 (a8 k w E P H rows t par B))) (dB (c9 (a8 k w E P H rows t par B)))
        s (j+ 2* rows.length* (t+1) - nF rows):=by
  have h1:=a3o E P H rows par B w hE hP hH hd s j
  have h2:=a46 k w E P H rows t par B hE hP hH s j
  have h3:=a3o (dE (c9 (a8 k w E P H rows t par B)))
    (dP (c9 (a8 k w E P H rows t par B))) (dH (c9 (a8 k w E P H rows t par B)))
    (r6 (c9 (a8 k w E P H rows t par B))) (a6i (c9 (a8 k w E P H rows t par B)))
    (dB (c9 (a8 k w E P H rows t par B))) (c9 (a8 k w E P H rows t par B)).w
    (v6 _ _) (v6 _ _) (v6 _ _)
    (a38 k w E P H rows t par B hE hd) s j
  have hsub:dP (c9 (a8 k w E P H rows t par B))⊆ dE (c9 (a8 k w E P H rows t par B))
      ↔ P⊆ E:=by
    rw [o8,a3n _ _ _ _ _ _ _ _ _ hP,a1n _ _ _ _ _ _ _ _ _ hE]
    exact Iff.rfl
  have hRl:(r6 (c9 (a8 k w E P H rows t par B))).length= rows.length:=by
    rw [r6,List.length_map,q8]
  have he:j+ 2* (r6 (c9 (a8 k w E P H rows t par B))).length *
      ((c9 (a8 k w E P H rows t par B)).t+ 1) -
      nF (r6 (c9 (a8 k w E P H rows t par B)))= j+ 2* rows.length* (t+1) - nF rows:=by
    rw [hRl,b06,a9p]
  rw [h1]
  refine h2.symm.trans (h3.symm.trans ?_)
  unfold t0
  rw [ite_eq_left (hsub.mpr hPE)]
  exact congrArg _ he
end Dec
end asmP6
section asmP7
namespace Dec
open Lib.Universal
lemma a12 (k:ℕ):(pairs k).Nodup:=by
  rw [pairs,List.nodup_flatMap]
  refine ⟨fun i _=>((List.nodup_finRange k).filter _).map (fun a b h=>(Prod.mk.inj h).2),?_⟩
  refine (List.nodup_finRange k).imp (fun {a b} hab=>?_)
  intro x hx hy
  simp only [List.mem_map] at hx hy
  obtain ⟨_,_,rfl⟩:=hx
  obtain ⟨_,_,h⟩:=hy
  exact hab (Prod.mk.inj h).1.symm
lemma a29 (k:ℕ):(layout k).Nodup:=by
  refine List.Nodup.append List.nodup_range ((a12 k).map (y6 k)) ?_
  intro x hx hy
  rw [List.mem_range] at hx
  obtain ⟨e,_,rfl⟩:=List.mem_map.mp hy
  exact absurd (a13 k e) (by omega)
end Dec
end asmP7
section asmP8
open Turing PEqualNP.Library Lib.Machines Lib.Universal
def a25 (F:List Bool→ List Bool) (s:List Bool):List Bool :=
  a1 (true::(a0 s).1) (g4 (a0 s).2 (F s))
def a1o (F:List Bool→ List Bool):ℕ→ ℕ→ List Bool→ List Bool
  | _,0,r=>r
  | i,n+ 1,r=>a1o F (i+ 1) n (g4 r (F (a1 (un i) r)))
lemma b0l (F:List Bool→ List Bool) (i:ℕ) (r:List Bool) :
    a25 F (a1 (un i) r)= a1 (un (i+ 1)) (g4 r (F (a1 (un i) r))):=by
  simp only [a25,a5,a1w]
lemma b0y (F:List Bool→ List Bool) :
    ∀ (n i:ℕ) (r:List Bool),(a25 F)^[n] (a1 (un i) r)= a1 (un (i+ n)) (a1o F i n r):=by
  intro n
  induction n with
  | zero=>intro i r; rfl
  | succ n ih =>
    intro i r
    rw [Function.iterate_succ_apply,b0l,ih,a1o,show i+ 1+ n= i+ (n+ 1) by omega]
lemma a97 (F:List Bool→ List Bool) (s:List Bool) :
    (a25 F s).length≤ s.length+ 3:=by
  have h:=m7 s
  simp only [a25,p0,List.length_cons,i4]
  omega
lemma b2r {F:List Bool→ List Bool} (hF:a4 F):a4 (a25 F) :=
  b7 (a7 (b8 (b0 [true]) a6) (n4 a3 hF))
    (fun _=>rfl)
def a3b (F cnt arg:List Bool→ List Bool) (s:List Bool):List Bool :=
  (a0 ((a25 F)^[(cnt s).length] (a1 [] (arg s)))).2
lemma a3q {F cnt arg:List Bool→ List Bool} (hF:a4 F) (hcnt:a4 cnt)
    (harg:a4 arg):a4 (a3b F cnt arg) :=
  b7 (a2 (v4 3 (b2r hF) (a97 F) hcnt
    (a7 (b0 []) harg)) a3) (fun _=>rfl)
lemma a4x (F cnt arg:List Bool→ List Bool) (s:List Bool) :
    a3b F cnt arg s= a1o F 0 (cnt s).length (arg s):=by
  have h:=b0y F (cnt s).length 0 (arg s)
  rw [b6j] at h
  rw [a3b,h,a5]
lemma a8s (r x:List Bool) (h:x.length= r.length):g4 r x= x:=by
  rw [g4,k7,← h,List.take_left' rfl]
def sF (wf f:List Bool→ List Bool) (s:List Bool):List Bool :=
  a1 (a0 (a0 s).2).1 (a08 (wf (a0 (a0 s).2).1) (a0 (a0 s).2).2
    (f (a1 (a0 s).1 (a0 (a0 s).2).1)))
lemma b54 (wf f:List Bool→ List Bool) (i e acc:List Bool) :
    sF wf f (a1 i (a1 e acc))= a1 e (a08 (wf e) acc (f (a1 i e))):=by
  simp only [sF,a5]
lemma b8r {wf f:List Bool→ List Bool} (hw:a4 wf) (hf:a4 f):a4 (sF wf f):=by
  have hE:=a2 a3 a6
  have hA:=a2 a3 a3
  exact b7 (a7 hE (b0v (a2 hE hw) hA
    (a2 (a7 a6 hE) hf))) (fun _=>rfl)
def a1z (wf f cnt arg:List Bool→ List Bool) (s:List Bool):List Bool :=
  (a0 (a3b (sF wf f) cnt (fun s=>a1 (arg s) (f3 (wf (arg s)))) s)).2
lemma a3t {wf f cnt arg:List Bool→ List Bool} (hw:a4 wf) (hf:a4 f)
    (hcnt:a4 cnt) (harg:a4 arg):a4 (a1z wf f cnt arg) :=
  b7 (a2 (a3q (b8r hw hf) hcnt
    (a7 harg (a2 (a2 harg hw) n6))) a3) (fun _=>rfl)
lemma b9k (wf f:List Bool→ List Bool) (e:List Bool) :
    ∀ (n i : ℕ) (acc : List Bool), acc.length = (wf e).length →
      ∃ acc', a1o (sF wf f) i n (a1 e acc) = a1 e acc' ∧ acc'.length = (wf e).length ∧
        val acc'= (val acc+ ∑ μ∈ Finset.range n,(val (f (a1 (un (i+ μ)) e)):ℕ)) %
          2 ^ (wf e).length:=by
  intro n
  induction n with
  | zero =>
    intro i acc h
    refine ⟨acc,rfl,h,?_⟩
    rw [Finset.sum_range_zero,add_zero,Nat.mod_eq_of_lt (h ▸ a4i acc)]
  | succ n ih =>
    intro i acc h
    have e1:sF wf f (a1 (un i) (a1 e acc))= a1 e (a08 (wf e) acc (f (a1 (un i) e))) :=
      b54 wf f _ e acc
    have hl:(a1 e (a08 (wf e) acc (f (a1 (un i) e)))).length= (a1 e acc).length:=by
      simp only [p0,a0z,h]
    obtain ⟨acc',h1,h2,h3⟩:=ih (i+ 1) _ (a0z _ _ _)
    refine ⟨acc',?_,h2,?_⟩
    · rw [a1o,e1,a8s _ _ hl,h1]
    · have hs:(∑ μ∈ Finset.range (n+ 1),(val (f (a1 (un (i+ μ)) e)):ℕ)) =
          (∑ μ∈ Finset.range n,(val (f (a1 (un (i+ 1+ μ)) e)):ℕ)) +
            val (f (a1 (un i) e)):=by
        rw [Finset.sum_range_succ']
        refine congrArg₂ (·+ ·) (Finset.sum_congr rfl fun μ _=>?_) (by rw [add_zero])
        rw [show i+ (μ+ 1)= i+ 1+ μ by omega]
      rw [h3,b0r,Nat.mod_add_mod,hs]
      congr 1
      ring
lemma a2h (wf f cnt arg:List Bool→ List Bool) (s:List Bool) :
    (a1z wf f cnt arg s).length= (wf (arg s)).length ∧
    val (a1z wf f cnt arg s) =
      (∑ μ∈ Finset.range (cnt s).length,(val (f (a1 (un μ) (arg s))):ℕ)) %
        2 ^ (wf (arg s)).length:=by
  obtain ⟨acc',h1,h2,h3⟩:=b9k wf f (arg s) (cnt s).length 0 (f3 (wf (arg s)))
    (q7 _)
  rw [w1,zero_add] at h3
  simp only [zero_add] at h3
  have e:a1z wf f cnt arg s= acc':=by rw [a1z,a4x,h1,a5]
  rw [e]
  exact ⟨h2,h3⟩
end asmP8
section asmP9
open Turing PEqualNP.Library Lib.Machines Lib.Universal
def b5 (lenU iU s:List Bool):List Bool:=m4 lenU (g8 (j0 iU lenU) s)
lemma k5 {ul ui us:List Bool→ List Bool} (hl:a4 ul) (hi:a4 ui)
    (hs:a4 us):a4 (fun z=>b5 (ul z) (ui z) (us z)) :=
  b7 (k4 hl (e8 (g9 hi hl) hs)) (fun _=>rfl)
lemma b3e (lenU iU s:List Bool) :
    b5 lenU iU s= (s.drop (iU.length* lenU.length)).take lenU.length:=by
  rw [b5,k7,i6]; simp [j0]
def ilv:List Bool→ List Bool→ List Bool
  | [],_=>[]
  | x::a,b=>x::b.headD false::ilv a b.tail
def hdL (a:List Bool):List Bool:=[a.headD false]
lemma b1j:a4 hdL :=
  g0 _ _ _ (fun (d:Bool) (x:Bool)=>if d then (true,none) else (true,some x))
    (fun d=>if d then none else some false) false (fun a=>by
      have hdone:∀ l:List Bool,c7 (fun (d:Bool) (x:Bool) =>
          if d then (true,none) else (true,some x)) (fun d=>if d then none else some false)
          true l= []:=by
        intro l; induction l with
        | nil=>rfl
        | cons x l ih=>simp [c7,ih]
      cases a with
      | nil=>rfl
      | cons x l=>simp [hdL,c7,hdone])
def a3y (s:List Bool):List Bool :=
  a1 (a0 s).1.tail (a1 (a0 (a0 s).2).1.tail
    ((a0 (a0 s).2).2++(hdL (a0 s).1++hdL (a0 (a0 s).2).1)))
lemma b1c (a b o:List Bool) :
    a3y (a1 a (a1 b o))= a1 a.tail (a1 b.tail (o++[a.headD false,b.headD false])):=by
  simp [a3y,a5,hdL]
lemma b0w (s:List Bool):(a3y s).length≤ s.length+ 4:=by
  have h1:=m7 s
  have h2:=m7 (a0 s).2
  simp only [a3y,p0,List.length_append,List.length_tail,hdL,List.length_singleton]
  omega
lemma b4l:a4 a3y:=by
  have hB:=a2 a3 a6
  have hO:=a2 a3 a3
  exact b7 (a7 (a2 a6 o3) (a7 (a2 hB o3)
    (b8 hO (b8 (a2 a6 b1j) (a2 hB b1j))))) (fun _=>rfl)
lemma b22 (a:List Bool):∀ (b o:List Bool),
    a3y^[a.length] (a1 a (a1 b o))= a1 [] (a1 (b.drop a.length) (o++ilv a b)):=by
  induction a with
  | nil=>intro b o; simp [ilv]
  | cons x a ih =>
    intro b o
    rw [List.length_cons,Function.iterate_succ_apply,b1c,List.headD_cons,
      List.tail_cons,ih]
    simp [ilv,List.drop_tail]
lemma b1w {u v:List Bool→ List Bool} (hu:a4 u) (hv:a4 v) :
    a4 (fun s=>ilv (u s) (v s)):=by
  have hit:a4 (fun s=>a3y^[(u s).length] (a1 (u s) (a1 (v s) []))) :=
    v4 4 b4l b0w hu (a7 hu (a7 hv (b0 [])))
  exact b7 (a2 (a2 hit a3) a3)
    (fun s=>by simp only [b22,a5,List.nil_append])
def bwL (op:Bool→ Bool→ Bool):List Bool→ List Bool→ List Bool
  | [],_=>[]
  | x::a,b=>op x (b.headD false)::bwL op a b.tail
def bwδ (op:Bool→ Bool→ Bool):Option Bool→ Bool→ Option Bool × Option Bool
  | none,x=>(some x,none)
  | some x,y=>(none,some (op x y))
lemma b8i (op:Bool→ Bool→ Bool) (a b:List Bool) :
    c7 (bwδ op) (fun _=>none) none (ilv a b)= bwL op a b:=by
  induction a generalizing b with
  | nil=>rfl
  | cons x a ih=>simp [ilv,c7,bwδ,bwL,ih]
lemma s9 (op:Bool→ Bool→ Bool) {u v:List Bool→ List Bool} (hu:a4 u)
    (hv:a4 v):a4 (fun s=>bwL op (u s) (v s)):=by
  have h:a4 (fun s=>c7 (bwδ op) (fun _=>none) none s) :=
    g0 _ _ _ (bwδ op) (fun _=>none) none (fun _=>rfl)
  exact b7 (a2 (b1w hu hv) h) (fun s=>b8i op _ _)
lemma t7 (op:Bool→ Bool→ Bool) (a b:List Bool):(bwL op a b).length= a.length:=by
  induction a generalizing b with
  | nil=>rfl
  | cons x a ih=>simp [bwL,ih]
lemma a7h (op:Bool→ Bool→ Bool) (a b:List Bool) (h:b.length= a.length) :
    bwL op a b= List.zipWith op a b:=by
  induction a generalizing b with
  | nil=>rfl
  | cons x a ih =>
    cases b with
    | nil=>simp at h
    | cons y b => simp only [bwL, List.headD_cons, List.tail_cons, List.zipWith_cons_cons]
                  rw [ih b (by simpa using h)]
def eqF (a b:List Bool):List Bool:=sel (u6 (bwL xor a b)) [true] []
lemma a1r {u v:List Bool→ List Bool} (hu:a4 u) (hv:a4 v) :
    a4 (fun s=>eqF (u s) (v s)) :=
  d6 (a2 (s9 xor hu hv) u8) (b0 [true]) (b0 [])
lemma a6w (a b:List Bool) (h:b.length= a.length) :
    eqF a b= if a= b then [true] else []:=by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil=>rfl
    | cons y b=>simp at h
  | cons x a ih =>
    cases b with
    | nil=>simp at h
    | cons y b =>
      have h':b.length= a.length:=by simpa using h
      have:=ih b h'
      simp only [eqF,sel,u6,bwL,List.headD_cons,List.tail_cons] at this ⊢
      cases x <;> cases y <;> simp_all
def a9d (a:List Bool):List Bool:=sel (u6 a) [true] []
lemma b46 {u:List Bool→ List Bool} (hu:a4 u):a4 (fun s=>a9d (u s)) :=
  d6 (a2 hu u8) (b0 [true]) (b0 [])
def lkT (z:List Bool):List Bool :=
  let ν:=(a0 z).1
  let e:=(a0 z).2
  let wU:=(a0 e).1
  let mU:=(a0 (a0 e).2).1
  let T:=(a0 (a0 (a0 e).2).2).1
  let b:=(a0 (a0 (a0 e).2).2).2
  sel (eqF (n3 mU ν) b) (f3 wU) (b5 wU ν T)
lemma b6y:a4 lkT:=by
  have hν:=a6
  have he:=a3
  have hw:=a2 he a6
  have hr:=a2 he a3
  have hm:=a2 hr a6
  have hr2:=a2 hr a3
  have hT:=a2 hr2 a6
  have hb:=a2 hr2 a3
  exact b7 (d6 (a1r (a64 hm hν) hb) (a2 hw n6)
    (k5 hw hν hT)) (fun _=>rfl)
def lkB (wU mU pU T b:List Bool):List Bool :=
  a1z (fun e=>(a0 e).1) lkT (fun s=>(a0 s).1) (fun s=>(a0 s).2)
    (a1 pU (a1 wU (a1 mU (a1 T b))))
lemma b79 {uw um up ut ub:List Bool→ List Bool} (hw:a4 uw) (hm:a4 um)
    (hp:a4 up) (ht:a4 ut) (hb:a4 ub) :
    a4 (fun s=>lkB (uw s) (um s) (up s) (ut s) (ub s)):=by
  have h:a4 (a1z (fun e=>(a0 e).1) lkT (fun s=>(a0 s).1)
      (fun s=>(a0 s).2)) :=
    a3t a6 b6y a6 a3
  exact b7 (a2 (a7 hp (a7 hw (a7 hm (a7 ht hb)))) h)
    (fun _=>rfl)
lemma b56 (wU mU pU T b:List Bool) (hb:b.length= mU.length) :
    (lkB wU mU pU T b).length= wU.length ∧
    val (lkB wU mU pU T b)= (∑ ν∈ Finset.range pU.length,
      (if n3 mU (un ν)= b then val (b5 wU (un ν) T) else 0:ℕ)) % 2 ^ wU.length:=by
  obtain ⟨h1,h2⟩:=a2h (fun e=>(a0 e).1) lkT (fun s=>(a0 s).1)
    (fun s=>(a0 s).2) (a1 pU (a1 wU (a1 mU (a1 T b))))
  simp only [a5] at h1 h2
  unfold lkB
  refine ⟨h1,?_⟩
  rw [h2]
  refine congrArg (· % 2 ^ wU.length) (Finset.sum_congr rfl fun ν _=>?_)
  simp only [lkT,a5]
  rw [a6w _ _ (by rw [hb,n8])]
  by_cases he:n3 mU (un ν)= b
  · rw [if_pos he,if_pos he]; rfl
  · rw [if_neg he,if_neg he]; exact w1 _
def eW (e:List Bool):List Bool:=(a0 e).1
def eM (e:List Bool):List Bool:=(a0 (a0 e).2).1
def eP (e:List Bool):List Bool:=(a0 (a0 (a0 e).2).2).1
def eNM (e:List Bool):List Bool:=(a0 (a0 (a0 (a0 e).2).2).2).1
def eSJ (e:List Bool):List Bool:=(a0 (a0 (a0 (a0 (a0 e).2).2).2).2).1
def eA (e:List Bool):List Bool :=
  (a0 (a0 (a0 (a0 (a0 (a0 e).2).2).2).2).2).1
def eMs (e:List Bool):List Bool :=
  (a0 (a0 (a0 (a0 (a0 (a0 e).2).2).2).2).2).2
lemma b45:a4 eW:=a6
lemma b8g:a4 eM:=b7 (a2 a3 a6) (fun _=>rfl)
lemma b0h:a4 eP :=
  b7 (a2 (a2 a3 a3) a6) (fun _=>rfl)
lemma b6t:a4 eNM :=
  b7 (a2 (a2 (a2 a3 a3) a3) a6)
    (fun _=>rfl)
lemma b72:a4 eSJ :=
  b7 (a2 (a2 (a2 (a2 a3 a3) a3)
    a3) a6) (fun _=>rfl)
lemma b9p:a4 eA :=
  b7 (a2 (a2 (a2 (a2 (a2 a3 a3)
    a3) a3) a3) a6) (fun _=>rfl)
lemma b7v:a4 eMs :=
  b7 (a2 (a2 (a2 (a2 (a2 a3 a3)
    a3) a3) a3) a3) (fun _=>rfl)
lemma f5 (wU mU pU NM SJ A M:List Bool) :
    let e:=a1 wU (a1 mU (a1 pU (a1 NM (a1 SJ (a1 A M)))))
    eW e= wU∧ eM e= mU∧ eP e= pU∧ eNM e= NM∧ eSJ e= SJ∧ eA e= A∧ eMs e= M:=by
  simp [eW,eM,eP,eNM,eSJ,eA,eMs,a5]
def a4a (NM ι μ:List Bool):List Bool :=
  sel (eqF (bwL and μ (v8 NM)) (bwL and ι (v8 NM))) []
    (a9d (bwL and (bwL and μ NM) (v8 ι)))
def a3h (NM SJ ι μ:List Bool):List Bool :=
  bwL or (bwL and ι (bwL and (v8 NM) SJ)) (bwL and (bwL and ι NM) (v8 μ))
def a26 (z:List Bool):List Bool :=
  let μU:=(a0 z).1
  let ιU:=(a0 (a0 z).2).1
  let e:=(a0 (a0 z).2).2
  let μ:=n3 (eM e) μU
  let ι:=n3 (eM e) ιU
  sel (a4a (eNM e) ι μ) (f3 (eW e))
    (a6f (eW e) (b5 (eW e) μU (eA e)) (lkB (eW e) (eM e) (eP e) (eMs e) (a3h (eNM e) (eSJ e) ι μ)))
lemma b2q {un' ui um:List Bool→ List Bool} (hn:a4 un') (hi:a4 ui)
    (hm:a4 um):a4 (fun s=>a4a (un' s) (ui s) (um s)) :=
  d6 (a1r (s9 and hm (a2 hn a0x)) (s9 and hi (a2 hn a0x)))
    (b0 []) (b46 (s9 and (s9 and hm hn) (a2 hi a0x)))
lemma b6f {un' us ui um:List Bool→ List Bool} (hn:a4 un') (hs:a4 us)
    (hi:a4 ui) (hm:a4 um):a4 (fun s=>a3h (un' s) (us s) (ui s) (um s)) :=
  s9 or (s9 and hi (s9 and (a2 hn a0x) hs))
    (s9 and (s9 and hi hn) (a2 hm a0x))
lemma b2j:a4 a26:=by
  have hμ:=a6
  have hι:=a2 a3 a6
  have he:=a2 a3 a3
  have hW:=a2 he b45
  have hM:=a2 he b8g
  have hP:=a2 he b0h
  have hNM:=a2 he b6t
  have hSJ:=a2 he b72
  have hA:=a2 he b9p
  have hMs:=a2 he b7v
  have hμm:=a64 hM hμ
  have hιm:=a64 hM hι
  exact b7 (d6 (b2q hNM hιm hμm) (a2 hW n6)
    (b5r hW (k5 hW hμ hA) (b79 hW hM hP hMs (b6f hNM hSJ hιm hμm))))
    (fun _=>rfl)
def a2f (y:List Bool):List Bool :=
  a1z (fun a=>eW (a0 a).2) a26 (fun a=>eP (a0 a).2) (fun a=>a) y
lemma b3d:a4 a2f :=
  a3t (b7 (a2 a3 b45) (fun _=>rfl)) b2j
    (b7 (a2 a3 b0h) (fun _=>rfl)) g5
def a17 (env:List Bool):List Bool :=
  (List.range (eP env).length).flatMap fun i=>a2f (a1 (un i) env)
lemma b35:a4 a17:=d9 b3d b0h g5
lemma u9 {α:Type} (f:α→ List Bool) (c:ℕ) (hf:∀ a,(f a).length= c) :
    ∀ (L : List α) (i : ℕ) (hi : i < L.length),
      ((L.flatMap f).drop (i* c)).take c= f (L[i]'hi):=by
  intro L
  induction L with
  | nil=>intro i hi; simp at hi
  | cons a L ih =>
    intro i hi
    cases i with
    | zero=>simp [List.take_left' (hf a)]
    | succ i =>
      have e:(i+ 1)* c= c+ i* c:=by ring
      rw [List.flatMap_cons,e,← List.drop_drop,List.drop_left' (hf a)]
      exact ih i (by simpa using hi)
lemma l8 {α:Type} (f:α→ List Bool) (c:ℕ) (hf:∀ a,(f a).length= c)
    (L:List α) (i:ℕ) (hi:i< L.length) (lenU iU:List Bool) (hl:lenU.length= c)
    (hiU:iU.length= i):b5 lenU iU (L.flatMap f)= f (L[i]'hi):=by
  rw [b3e,hl,hiU]
  exact u9 f c hf L i hi
lemma b17 (μ ι:ℕ) (e:List Bool) :
    (a26 (a1 (un μ) (a1 (un ι) e))).length= (eW e).length ∧
    val (a26 (a1 (un μ) (a1 (un ι) e))) =
      if a4a (eNM e) (n3 (eM e) (un ι)) (n3 (eM e) (un μ))= [] then 0 else
        (val (b5 (eW e) (un μ) (eA e))* val (lkB (eW e) (eM e) (eP e) (eMs e)
          (a3h (eNM e) (eSJ e) (n3 (eM e) (un ι)) (n3 (eM e) (un μ))))) %
          2 ^ (eW e).length:=by
  simp only [a26,a5]
  unfold sel
  split
  · exact ⟨q7 _,w1 _⟩
  · exact ⟨b13 _ _ _,b58 _ _ _⟩
lemma a3x (ι:ℕ) (e:List Bool) :
    (a2f (a1 (un ι) e)).length= (eW e).length ∧
    val (a2f (a1 (un ι) e))= (∑ μ∈ Finset.range (eP e).length,
      (val (a26 (a1 (un μ) (a1 (un ι) e))):ℕ)) % 2 ^ (eW e).length:=by
  have h:=a2h (fun a=>eW (a0 a).2) a26 (fun a=>eP (a0 a).2) (fun a=>a)
    (a1 (un ι) e)
  simp only [a5] at h
  exact h
lemma b2i (e:List Bool) (ι:ℕ) (hι:ι< (eP e).length) :
    b5 (eW e) (un ι) (a17 e)= a2f (a1 (un ι) e):=by
  have h:=l8 (fun i=>a2f (a1 (un i) e)) (eW e).length
    (fun i=>(a3x i e).1) (List.range (eP e).length) ι (by simpa using hι) (eW e) (un ι)
    rfl (b4 ι)
  rw [a17,h,List.getElem_range]
lemma a95 (e:List Bool):(a17 e).length= (eP e).length* (eW e).length:=by
  rw [a17,List.length_flatMap]
  simp [fun i=>(a3x i e).1]
end asmP9
section asmP10
open Turing PEqualNP.Library Lib.Machines Lib.Universal
def a27 (LU iU arr r:List Bool):List Bool :=
  m4 (j0 iU LU) arr++(r++g8 (j0 (true::iU) LU) arr)
lemma a4m {ul ui ua ur:List Bool→ List Bool} (hl:a4 ul) (hi:a4 ui)
    (ha:a4 ua) (hr:a4 ur):a4 (fun s=>a27 (ul s) (ui s) (ua s) (ur s)) :=
  b7 (b8 (k4 (g9 hi hl) ha) (b8 hr
    (e8 (g9 (b8 (b0 [true]) hi) hl) ha))) (fun _=>rfl)
lemma b73 (c:ℕ):∀ (L:List (List Bool)) (k:ℕ),(∀ a∈ L,a.length= c) →
    (L.flatMap id).take (k* c)= (L.take k).flatMap id:=by
  intro L
  induction L with
  | nil=>intro k _; simp
  | cons a L ih =>
    intro k hL
    have ha:a.length= c:=hL a (by simp)
    cases k with
    | zero=>simp
    | succ k =>
      rw [show (k+ 1)* c= c+ k* c by ring,List.flatMap_cons,List.take_append,
        List.take_of_length_le (by simp [ha]),show c+ k* c - (id a).length= k* c by simp [ha],
        ih k (fun b hb=>hL b (by simp [hb]))]
      simp
lemma b6n (c:ℕ):∀ (L:List (List Bool)) (k:ℕ),(∀ a∈ L,a.length= c) →
    (L.flatMap id).drop (k* c)= (L.drop k).flatMap id:=by
  intro L
  induction L with
  | nil=>intro k _; simp
  | cons a L ih =>
    intro k hL
    have ha:a.length= c:=hL a (by simp)
    cases k with
    | zero=>simp
    | succ k =>
      rw [show (k+ 1)* c= c+ k* c by ring,List.flatMap_cons,List.drop_append,
        List.drop_of_length_le (by simp [ha]),show c+ k* c - (id a).length= k* c by simp [ha],
        ih k (fun b hb=>hL b (by simp [hb]))]
      simp
lemma a22 (LU:List Bool) (recs:List (List Bool))
    (hrec:∀ r∈ recs,r.length= LU.length) (i:ℕ) (hi:i< recs.length) (r:List Bool) :
    a27 LU (un i) (recs.flatMap id) r= (recs.set i r).flatMap id:=by
  rw [a27,k7,i6]
  simp only [j0,b4,List.length_cons]
  rw [List.set_eq_take_append_cons_drop,if_pos hi,List.flatMap_append,List.flatMap_cons,
    b73 _ recs i hrec,b6n _ recs (i+ 1) hrec]
  rfl
section
variable (nU LU leaf test step:List Bool→ List Bool)
def a7z (z:List Bool):List Bool :=
  let jU:=(a0 z).1
  let iU:=(a0 (a0 (a0 z).2).1).1
  let G:=(a0 (a0 (a0 z).2).1).2
  let T:=(a0 (a0 z).2).2
  a1 (a1 iU G) (sel (test (a1 iU (a1 jU G))) T
    (a27 (LU G) iU T (step (a1 iU (a1 jU (a1 G T))))))
def a71 (z:List Bool):List Bool :=
  let i'U:=(a0 z).1
  let G:=(a0 (a0 z).2).1
  let T:=(a0 (a0 z).2).2
  let iU:=g8 (true::i'U) (nU G)
  let T1:=a27 (LU G) iU T (leaf (a1 iU G))
  a1 G (a0 (a3b (a7z LU test step) (fun s=>nU (a0 (a0 s).1).2)
    (fun s=>s) (a1 (a1 iU G) T1))).2
def a7a (G:List Bool):List Bool :=
  (a0 (a3b (a71 nU LU leaf test step) (fun s=>nU (a0 s).1) (fun s=>s)
    (a1 G (f3 (j0 (nU G) (LU G)))))).2
end
lemma b5t {LU test step:List Bool→ List Bool} (hL:a4 LU) (ht:a4 test)
    (hs:a4 step):a4 (a7z LU test step):=by
  have hj:=a6
  have hiG:=a2 a3 a6
  have hi:=a2 hiG a6
  have hG:=a2 hiG a3
  have hT:=a2 a3 a3
  exact b7 (a7 (a7 hi hG) (d6 (a2 (a7 hi (a7 hj hG)) ht)
    hT (a4m (a2 hG hL) hi hT
      (a2 (a7 hi (a7 hj (a7 hG hT))) hs)))) (fun _=>rfl)
lemma b3m {nU LU leaf test step:List Bool→ List Bool} (hn:a4 nU) (hL:a4 LU)
    (hl:a4 leaf) (ht:a4 test) (hs:a4 step):a4 (a71 nU LU leaf test step):=by
  have hi':=a6
  have hG:=a2 a3 a6
  have hT:=a2 a3 a3
  have hi:=e8 (b8 (b0 [true]) hi') (a2 hG hn)
  have hT1:=a4m (a2 hG hL) hi hT (a2 (a7 hi hG) hl)
  have hloop:=a3q (b5t hL ht hs) (a2 (a2 a6 a3) hn)
    g5
  exact b7 (a7 hG (a2 (a2 (a7 (a7 hi hG) hT1) hloop)
    a3)) (fun _=>rfl)
lemma b2h {nU LU leaf test step:List Bool→ List Bool} (hn:a4 nU) (hL:a4 LU)
    (hl:a4 leaf) (ht:a4 test) (hs:a4 step) :
    a4 (a7a nU LU leaf test step):=by
  have hloop:=a3q (b3m hn hL hl ht hs) (a2 a6 hn) g5
  exact b7 (a2 (a2 (a7 g5 (a2 (g9 hn hL) n6)) hloop)
    a3) (fun _=>rfl)
end asmP10
section asmP11
open Turing PEqualNP.Library Lib.Machines Lib.Universal
lemma a8g {α:Type} (F:List Bool→ List Bool) (ab:α→ List Bool) (g:ℕ→ α→ α)
    (P:α→ Prop) (K:ℕ)
    (hP:∀ k a,k< K→ P a→ P (g k a))
    (hF:∀ k a,k< K→ P a→ F (a1 (un k) (ab a))= ab (g k a))
    (hl:∀ k a,k< K→ P a→ (ab (g k a)).length= (ab a).length) :
    ∀ n i a, i + n ≤ K → P a →
      a1o F i n (ab a)= ab ((List.range n).foldl (fun b m=>g (i+ m) b) a):=by
  intro n
  induction n with
  | zero=>intro i a _ _; rfl
  | succ n ih =>
    intro i a hK ha
    have hk:i< K:=by omega
    have e:∀ m,i+ 1+ m= i+ (m+ 1):=fun m=>by omega
    rw [a1o,hF i a hk ha,a8s _ _ (hl i a hk ha),
      ih (i+ 1) (g i a) (by omega) (hP i a hk ha),List.range_succ_eq_map,List.foldl_cons,
      List.foldl_map]
    simp only [add_zero,e]
section
variable (leaf test step:List Bool→ List Bool) (G:List Bool)
def z4 (i:ℕ) (Ts:List (List Bool)) (j:ℕ):List (List Bool) :=
  if test (a1 (un i) (a1 (un j) G))= [] then Ts
  else Ts.set i (step (a1 (un i) (a1 (un j) (a1 G (Ts.flatMap id)))))
def a11 (N:ℕ) (Ts:List (List Bool)) (i':ℕ):List (List Bool) :=
  (List.range N).foldl (z4 test step G (N - 1 - i'))
    (Ts.set (N - 1 - i') (leaf (a1 (un (N - 1 - i')) G)))
def a1x (N L:ℕ):List (List Bool) :=
  (List.range N).foldl (a11 leaf test step G N) (List.replicate N (List.replicate L false))
end
lemma a0u (N L:ℕ) (Ts:List (List Bool)) (h1:Ts.length= N)
    (h2:∀ r∈ Ts,r.length= L):(Ts.flatMap id).length= N* L:=by
  induction Ts generalizing N with
  | nil=>simp at h1; simp [← h1]
  | cons a Ts ih =>
    simp only [List.length_cons] at h1
    rw [List.flatMap_cons,List.length_append,ih (N - 1) (by omega) (fun r hr=>h2 r (by simp [hr]))]
    have ha:(id a).length= L:=h2 a (by simp)
    rw [ha]
    obtain ⟨M,rfl⟩:∃ M,N= M+ 1:=⟨N - 1,by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
lemma a7i (N L:ℕ) (Ts:List (List Bool)) (h1:Ts.length= N)
    (h2:∀ r∈ Ts,r.length= L) (i:ℕ) (r:List Bool) (hr:r.length= L) :
    (Ts.set i r).length= N∧ ∀ q∈ Ts.set i r,q.length= L:=by
  refine ⟨by rw [List.length_set,h1],fun q hq=>?_⟩
  rcases List.mem_or_eq_of_mem_set hq with h | h
  · exact h2 q h
  · rw [h,hr]
lemma a84 (N L:ℕ) :
    (List.replicate N (List.replicate L false)).flatMap id= List.replicate (N* L) false:=by
  induction N with
  | zero=>simp
  | succ N ih =>
    rw [List.replicate_succ,List.flatMap_cons,ih,id,← List.replicate_add]
    congr 1; ring
def z6 (N L:ℕ) (Ts:List (List Bool)):Prop:=Ts.length= N∧ ∀ r∈ Ts,r.length= L
lemma a5v (test step:List Bool→ List Bool) (G:List Bool) (N L:ℕ)
    (hstep:∀ i< N,∀ j< N,∀ T:List Bool,T.length= N* L →
      (step (a1 (un i) (a1 (un j) (a1 G T)))).length= L)
    (i:ℕ) (hi:i< N) (k:ℕ) (hk:k< N) (a:List (List Bool)) (ha:z6 N L a) :
    z6 N L (z4 test step G i a k):=by
  unfold z4
  split
  · exact ha
  · exact a7i N L a ha.1 ha.2 i _ (hstep i hi k hk _ (a0u N L a ha.1 ha.2))
lemma a81 (test step:List Bool→ List Bool) (G:List Bool) (N L:ℕ)
    (hstep:∀ i< N,∀ j< N,∀ T:List Bool,T.length= N* L →
      (step (a1 (un i) (a1 (un j) (a1 G T)))).length= L)
    (i:ℕ) (hi:i< N):∀ (l:List ℕ) (a:List (List Bool)),(∀ k∈ l,k< N) →
      z6 N L a→ z6 N L (l.foldl (z4 test step G i) a):=by
  intro l
  induction l with
  | nil=>intro a _ ha; exact ha
  | cons k l ih =>
    intro a hl' ha
    exact ih _ (fun m hm=>hl' m (by simp [hm]))
      (a5v test step G N L hstep i hi k (hl' k (by simp)) a ha)
lemma b2k (LU test step:List Bool→ List Bool) (G:List Bool) (L:ℕ)
    (hL:(LU G).length= L) (N i:ℕ) (hi:i< N) (k:ℕ) (a:List (List Bool))
    (ha:z6 N L a) :
    a7z LU test step (a1 (un k) (a1 (a1 (un i) G) (a.flatMap id))) =
      a1 (a1 (un i) G) ((z4 test step G i a k).flatMap id):=by
  unfold a7z
  simp only [a5]
  unfold z4 sel
  split
  · rfl
  · rw [a22 (LU G) a (fun r hr=>(ha.2 r hr).trans hL.symm) i (by rw [ha.1]; exact hi)]
lemma b3u (LU test step:List Bool→ List Bool) (G:List Bool) (N L:ℕ)
    (hL:(LU G).length= L)
    (hstep:∀ i< N,∀ j< N,∀ T:List Bool,T.length= N* L →
      (step (a1 (un i) (a1 (un j) (a1 G T)))).length= L)
    (i:ℕ) (hi:i< N) (Ts:List (List Bool)) (hTs:z6 N L Ts) :
    a1o (a7z LU test step) 0 N (a1 (a1 (un i) G) (Ts.flatMap id)) =
      a1 (a1 (un i) G) (((List.range N).foldl (z4 test step G i) Ts).flatMap id):=by
  have hl:∀ k a,k< N→ z6 N L a →
      (a1 (a1 (un i) G) ((z4 test step G i a k).flatMap id)).length =
        (a1 (a1 (un i) G) (a.flatMap id)).length:=by
    intro k a hk ha
    have h1:=a5v test step G N L hstep i hi k hk a ha
    simp only [p0,a0u N L _ h1.1 h1.2,a0u N L _ ha.1 ha.2]
  have h:=@a8g (List (List Bool)) (a7z LU test step)
    (fun a=>a1 (a1 (un i) G) (a.flatMap id)) (fun k a=>z4 test step G i a k)
    (z6 N L) N (fun k a hk ha=>a5v test step G N L hstep i hi k hk a ha)
    (fun k a _ ha=>b2k LU test step G L hL N i hi k a ha) hl N 0 Ts (by omega) hTs
  simp only [zero_add] at h
  exact h
lemma b10 (nU LU leaf test step:List Bool→ List Bool) (G:List Bool) (N L:ℕ)
    (hn:nU G= un N) (hL:(LU G).length= L)
    (hleaf:∀ i< N,(leaf (a1 (un i) G)).length= L)
    (hstep:∀ i< N,∀ j< N,∀ T:List Bool,T.length= N* L →
      (step (a1 (un i) (a1 (un j) (a1 G T)))).length= L)
    (k:ℕ) (hk:k< N) (a:List (List Bool)) (ha:z6 N L a) :
    a71 nU LU leaf test step (a1 (un k) (a1 G (a.flatMap id))) =
      a1 G ((a11 leaf test step G N a k).flatMap id):=by
  have hi:N - 1 - k< N:=by omega
  have hiU:g8 (true::un k) (un N)= un (N - 1 - k):=by
    rw [i6,List.length_cons,b4,un,List.drop_replicate]
    congr 1; omega
  have h0:=a7i N L a ha.1 ha.2 (N - 1 - k) _ (hleaf _ hi)
  have hset:=a22 (LU G) a (fun r hr=>(ha.2 r hr).trans hL.symm) (N - 1 - k)
    (by rw [ha.1]; exact hi) (leaf (a1 (un (N - 1 - k)) G))
  have hin:=b3u LU test step G N L hL hstep (N - 1 - k) hi _ h0
  unfold a71
  simp only [a5]
  rw [hn,hiU,hset,a4x]
  simp only [a5]
  rw [hn,b4,hin,a5]
  rfl
lemma b4o (nU LU leaf test step:List Bool→ List Bool) (G:List Bool) (N L:ℕ)
    (hn:nU G= un N) (hL:(LU G).length= L)
    (hleaf:∀ i< N,(leaf (a1 (un i) G)).length= L)
    (hstep:∀ i< N,∀ j< N,∀ T:List Bool,T.length= N* L →
      (step (a1 (un i) (a1 (un j) (a1 G T)))).length= L) :
    a7a nU LU leaf test step G= (a1x leaf test step G N L).flatMap id:=by
  have hPo:∀ k a,k< N→ z6 N L a→ z6 N L (a11 leaf test step G N a k):=by
    intro k a hk ha
    have hi:N - 1 - k< N:=by omega
    exact a81 test step G N L hstep _ hi (List.range N) _
      (fun m hm=>List.mem_range.mp hm) (a7i N L a ha.1 ha.2 (N - 1 - k) _ (hleaf _ hi))
  have hlo:∀ k a,k< N→ z6 N L a →
      (a1 G ((a11 leaf test step G N a k).flatMap id)).length= (a1 G (a.flatMap id)).length:=by
    intro k a hk ha
    have h1:=hPo k a hk ha
    simp only [p0,a0u N L _ h1.1 h1.2,a0u N L _ ha.1 ha.2]
  have hstart:z6 N L (List.replicate N (List.replicate L false)) :=
    ⟨List.length_replicate,fun r hr=>by rw [List.eq_of_mem_replicate hr,List.length_replicate]⟩
  have h:=@a8g (List (List Bool)) (a71 nU LU leaf test step)
    (fun a=>a1 G (a.flatMap id)) (fun k a=>a11 leaf test step G N a k) (z6 N L) N hPo
    (fun k a hk ha=>b10 nU LU leaf test step G N L hn hL hleaf hstep k hk a ha) hlo N 0
    _ (by omega) hstart
  simp only [zero_add] at h
  have hblank:f3 (j0 (nU G) (LU G)) =
      (List.replicate N (List.replicate L false)).flatMap id:=by
    rw [a84,f3,j0,hn,b4,hL,un]
    simp
  rw [a7a,a4x]
  simp only [a5]
  rw [hblank,hn,b4,h,a5]
  rfl
end asmP11
section asmP12
open Turing PEqualNP.Library Lib.Machines Lib.Universal
lemma a5n (l:List Bool):∀ x,(val l).testBit x= l.getD x false:=by
  induction l with
  | nil=>intro x; simp [val]
  | cons b l ih =>
    intro x
    have e:val (b::l)= Nat.bit b (val l):=by
      cases b <;> simp [val,Nat.bit] <;> ring
    rw [e]
    cases x with
    | zero=>simp [Nat.testBit_bit_zero]
    | succ x=>rw [Nat.testBit_bit_succ,ih]; simp
lemma a2m (mU:List Bool) (ι x:ℕ) :
    (n3 mU (un ι)).getD x false= (decide (x< mU.length) && ι.testBit x):=by
  rw [← a5n,a6k,b4,Nat.testBit_mod_two_pow]
lemma a21 (op:Bool→ Bool→ Bool) (a b:List Bool) (x:ℕ) :
    (bwL op a b).getD x false =
      (decide (x< a.length) && op (a.getD x false) (b.getD x false)):=by
  induction a generalizing b x with
  | nil=>simp [bwL]
  | cons y a ih =>
    cases x with
    | zero=>cases b <;> simp [bwL]
    | succ x =>
      rw [bwL,List.getD_cons_succ,ih,List.length_cons,List.getD_cons_succ]
      cases b with
      | nil=>simp
      | cons z b=>simp [List.getD_cons_succ]
lemma a19 (a:List Bool) (x:ℕ) :
    (v8 a).getD x false= (decide (x< a.length) && !(a.getD x false)):=by
  unfold v8
  by_cases h:x< a.length
  · simp [List.getD_eq_getElem?_getD,h]
  · simp [List.getD_eq_getElem?_getD,h,List.getElem?_eq_none (Nat.le_of_not_lt h)]
lemma a8w (a b:List Bool) (h:a.length= b.length)
    (hx:∀ x< a.length,a.getD x false= b.getD x false):a= b:=by
  apply List.ext_getElem h
  intro x h1 h2
  have:=hx x h1
  rwa [List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2] at this
lemma b4y (a:List Bool) :
    a9d a= if ∀ x< a.length,a.getD x false= false then [true] else []:=by
  have hp:u6 a= []↔ ∀ x< a.length,a.getD x false= false:=by
    unfold u6
    rw [List.filter_eq_nil_iff]
    constructor
    · intro h x hx
      rw [List.getD_eq_getElem _ _ hx]
      have:=h _ (List.getElem_mem hx)
      simpa using this
    · intro h y hy
      obtain ⟨x,hx,rfl⟩:=List.getElem_of_mem hy
      have:=h x hx
      rw [List.getD_eq_getElem _ _ hx] at this
      simp [this]
  unfold a9d sel
  by_cases h:∀ x< a.length,a.getD x false= false
  · rw [if_pos (hp.mpr h),if_pos h]
  · rw [if_neg (fun h'=>h (hp.mp h')),if_neg h]
lemma b14 (mU NM:List Bool) (hNM:NM.length= mU.length) (ι μ:ℕ) :
    a4a NM (n3 mU (un ι)) (n3 mU (un μ)) =
      if ∀ x< mU.length,(μ.testBit x && !(NM.getD x false))= (ι.testBit x && !(NM.getD x false)) ∧
          (μ.testBit x && NM.getD x false→ ι.testBit x)
      then [true] else []:=by
  unfold a4a
  rw [a6w _ _ (by simp [t7,n8]),b4y]
  have hA:(bwL and (n3 mU (un μ)) (v8 NM)= bwL and (n3 mU (un ι)) (v8 NM)) ↔
      ∀ x< mU.length,(μ.testBit x && !(NM.getD x false))= (ι.testBit x && !(NM.getD x false)):=by
    constructor
    · intro h x hx
      have:=congrArg (fun l=>l.getD x false) h
      simp only [a21,a2m,a19,n8,hNM,hx,decide_true,
        Bool.true_and] at this
      exact this
    · intro h
      apply a8w _ _ (by simp [t7,n8])
      intro x hx
      simp only [t7,n8] at hx
      simp only [a21,a2m,a19,n8,hNM,hx,decide_true,Bool.true_and]
      exact h x hx
  have hB:(∀ x< (bwL and (bwL and (n3 mU (un μ)) NM) (v8 (n3 mU (un ι)))).length,
      (bwL and (bwL and (n3 mU (un μ)) NM) (v8 (n3 mU (un ι)))).getD x false= false) ↔
      ∀ x< mU.length,(μ.testBit x && NM.getD x false→ ι.testBit x):=by
    simp only [t7,n8,a21,a2m,a19]
    constructor
    · intro h x hx h1
      have:=h x hx
      simp only [hx,decide_true,Bool.true_and] at this
      revert this h1
      cases μ.testBit x <;> cases NM.getD x false <;> cases ι.testBit x <;> simp
    · intro h x hx
      have:=h x hx
      simp only [hx,decide_true,Bool.true_and]
      revert this
      cases μ.testBit x <;> cases NM.getD x false <;> cases ι.testBit x <;> simp
  have hC:(∀ x< mU.length,(μ.testBit x && !(NM.getD x false))= (ι.testBit x && !(NM.getD x false)) ∧
      (μ.testBit x && NM.getD x false→ ι.testBit x)) ↔
      (∀ x< mU.length,(μ.testBit x && !(NM.getD x false))= (ι.testBit x && !(NM.getD x false))) ∧
      (∀ x< mU.length,(μ.testBit x && NM.getD x false→ ι.testBit x)) :=
    ⟨fun h=>⟨fun x hx=>(h x hx).1,fun x hx=>(h x hx).2⟩,fun h x hx=>⟨h.1 x hx,h.2 x hx⟩⟩
  simp only [hA,hB,hC]
  by_cases a:∀ x< mU.length,(μ.testBit x && !(NM.getD x false))= (ι.testBit x && !(NM.getD x false))
  · by_cases b : ∀ x < mU.length, (μ.testBit x && NM.getD x false → ι.testBit x)
    · rw [if_pos a,if_pos b,if_pos ⟨a,b⟩]; rfl
    · rw [if_pos a,if_neg b,if_neg (fun h=>b h.2)]; rfl
  · rw [if_neg a]
    show ([]:List Bool)= _
    rw [if_neg (fun h=>a (And.left h))]
lemma b3o (mU NM SJ:List Bool) (hNM:NM.length= mU.length)
    (hSJ:SJ.length= mU.length) (ι μ x:ℕ) :
    (val (a3h NM SJ (n3 mU (un ι)) (n3 mU (un μ)))).testBit x =
      (decide (x< mU.length) && ((ι.testBit x && !(NM.getD x false) && SJ.getD x false) ||
        (ι.testBit x && NM.getD x false && !(μ.testBit x)))):=by
  rw [a5n]
  unfold a3h
  simp only [a21,t7,n8,a2m,a19,b2a,hNM,hSJ]
  by_cases hx:x< mU.length
  · simp only [hx, decide_true, Bool.true_and]
    cases ι.testBit x <;> cases NM.getD x false <;> cases SJ.getD x false <;>
      cases μ.testBit x <;> rfl
  · simp [hx]
lemma b11 (mU NM SJ ι μ:List Bool) (hι:ι.length= mU.length) :
    (a3h NM SJ ι μ).length= mU.length:=by
  simp [a3h,t7,hι]
end asmP12
section asmP13
open Finset
def f0 (S:Finset ℕ):ℕ:=∑ x∈ S,2 ^ x
lemma k9 (S:Finset ℕ) (x:ℕ):(f0 S).testBit x= decide (x∈ S):=by
  have h:=Finset.toFinset_bitIndices_sum_two_pow S
  have e:x∈ S↔ (f0 S).testBit x= true:=by
    rw [← Nat.mem_bitIndices,← List.mem_toFinset]
    unfold f0
    rw [h]
  by_cases hx:x∈ S
  · rw [decide_eq_true hx]; exact e.mp hx
  · rw [decide_eq_false hx]
    cases hb:(f0 S).testBit x
    · rfl
    · exact absurd (e.mpr hb) hx
lemma a2b (S:Finset ℕ) (m:ℕ) (h:S⊆ range m):f0 S< 2 ^ m :=
  Nat.geomSum_lt (le_refl 2) (fun k hk=>mem_range.mp (h hk))
def mTg (m ι:ℕ) (nm:ℕ→ Bool):Finset ℕ:=(range m).filter (fun x=>ι.testBit x && !nm x)
def mNm (m ι:ℕ) (nm:ℕ→ Bool):Finset ℕ:=(range m).filter (fun x=>ι.testBit x && nm x)
abbrev mgP (m ι μ:ℕ) (nm:ℕ→ Bool):Prop :=
  ∀ x< m,(μ.testBit x && !nm x)= (ι.testBit x && !nm x)∧ (μ.testBit x && nm x→ ι.testBit x)
lemma a76 (m ι:ℕ) (nm:ℕ→ Bool) (Y:Finset ℕ) (hY:Y⊆ mNm m ι nm) :
    mgP m ι (f0 (mTg m ι nm∪ Y)) nm:=by
  intro x hx
  rw [k9]
  have hY':x∈ Y→ (ι.testBit x && nm x)= true:=fun h=>by
    have:=hY h; simp only [mNm,mem_filter] at this; exact this.2
  by_cases hn:nm x= true
  · have hT : x ∉ mTg m ι nm := by simp [mTg, hn]
    refine ⟨by simp [hn],fun h=>?_⟩
    have hm:x∈ Y:=by
      simp only [hn,Bool.and_true,decide_eq_true_eq,mem_union] at h
      exact h.resolve_left hT
    have:=hY' hm
    simp only [Bool.and_eq_true] at this
    exact this.1
  · have hn' : nm x = false := by simpa using hn
    have hY0:x∉ Y:=fun h=>by have:=hY' h; simp [hn'] at this
    refine ⟨?_,fun h=>by simp [hn'] at h⟩
    simp only [hn',Bool.not_false,Bool.and_true,mem_union,hY0,or_false,mTg,mem_filter,
      mem_range,hx,true_and]
    cases ι.testBit x <;> rfl
lemma b7n (m ι:ℕ) (nm:ℕ→ Bool) (g:ℕ→ ℕ) :
    (∑ μ∈ range (2 ^ m),if mgP m ι μ nm then g μ else 0) =
      ∑ Y∈ (mNm m ι nm).powerset,g (f0 (mTg m ι nm∪ Y)):=by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun μ=>(range m).filter (fun x=>μ.testBit x && nm x))
    (fun Y=>f0 (mTg m ι nm∪ Y)) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Finset.mem_filter,Finset.mem_range] at hμ
    rw [Finset.mem_powerset]
    intro x hx
    simp only [mem_filter,mem_range,Bool.and_eq_true] at hx
    have:=(hμ.2 x hx.1).2 (by simp [hx.2.1,hx.2.2])
    simp [mNm,hx.1,this,hx.2.2]
  · intro Y hY
    rw [Finset.mem_powerset] at hY
    rw [Finset.mem_filter,Finset.mem_range]
    refine ⟨a2b _ m (union_subset (filter_subset _ _) (hY.trans (filter_subset _ _))),
      a76 m ι nm Y hY⟩
  · intro μ hμ
    rw [Finset.mem_filter,Finset.mem_range] at hμ
    apply Nat.eq_of_testBit_eq
    intro x
    rw [k9]
    by_cases hx:x< m
    · have hc := hμ.2 x hx
      by_cases hn:nm x= true
      · simp [mTg,hn,hx]
      · have hn' : nm x = false := by simpa using hn
        simp only [hn',Bool.not_false,Bool.and_true] at hc
        simp [mTg,hn',hx,hc.1]
    · have h0:μ.testBit x= false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hμ.1 (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [mTg,hx,h0]
  · intro Y hY
    rw [Finset.mem_powerset] at hY
    ext x
    simp only [mem_filter,mem_range,k9,Bool.and_eq_true,decide_eq_true_eq,
      mem_union,mTg]
    constructor
    · rintro ⟨hx, h1 | h1, hn⟩
      · simp [hn] at h1
      · exact h1
    · intro h
      have:=hY h
      simp only [mNm,mem_filter,mem_range,Bool.and_eq_true] at this
      exact ⟨this.1,Or.inr h,this.2.2⟩
  · intro μ hμ
    rw [Finset.mem_filter,Finset.mem_range] at hμ
    congr 1
    apply Nat.eq_of_testBit_eq
    intro x
    rw [k9]
    by_cases hx:x< m
    · have hc := hμ.2 x hx
      by_cases hn:nm x= true
      · simp [mTg,hn,hx]
      · have hn' : nm x = false := by simpa using hn
        simp only [hn',Bool.not_false,Bool.and_true] at hc
        simp [mTg,hn',hx,hc.1]
    · have h0:μ.testBit x= false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hμ.1 (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [mTg,hx,h0]
lemma b5j (m ι:ℕ) (nm sj:ℕ→ Bool) (Y:Finset ℕ) (hY:Y⊆ mNm m ι nm) (ν:ℕ)
    (hν:∀ x,ν.testBit x= (decide (x< m) && ((ι.testBit x && !nm x && sj x) ||
      (ι.testBit x && nm x && !(f0 (mTg m ι nm∪ Y)).testBit x)))) :
    ν= f0 ((mTg m ι nm).filter (fun x=>sj x)∪ (mNm m ι nm \ Y)):=by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [hν,k9,k9]
  have hY':x∈ Y→ x< m∧ ι.testBit x= true∧ nm x= true:=fun h=>by
    have:=hY h; simp only [mNm,mem_filter,mem_range,Bool.and_eq_true] at this; exact this
  by_cases hx:x< m
  · by_cases hn : nm x = true
    · by_cases hy : x ∈ Y
      · simp [mTg,mNm,hx,hn,hy]
      · simp [mTg,mNm,hx,hn,hy]
    · have hn' : nm x = false := by simpa using hn
      have hy:x∉ Y:=fun h=>by
        have h2:=(hY' h).2.2
        rw [hn'] at h2
        exact Bool.false_ne_true h2
      simp [mTg,mNm,hx,hn',hy]
  · have hy : x ∉ Y := fun h => hx (hY' h).1
    simp [mTg,mNm,hx,hy]
end asmP13
section asmP14
namespace LT
open Lib.Machines Lib.Universal
lemma cc {f g:List Bool→ List Bool} (hf:a4 f) (hg:a4 g):a4 (fun s=>g (f s)) :=
  a2 hf hg
def b2 (φ:Bool→ Bool→ Bool) (u v:List Bool):List Bool :=
  sel (j3 u) (sel (j3 v) [φ false false] [φ false true])
    (sel (j3 v) [φ true false] [φ true true])
lemma b48 (φ:Bool→ Bool→ Bool) {u v:List Bool→ List Bool} (hu:a4 u)
    (hv:a4 v):a4 (fun s=>b2 φ (u s) (v s)) :=
  d6 (cc hu m6) (d6 (cc hv m6) (b0 _) (b0 _))
    (d6 (cc hv m6) (b0 _) (b0 _))
lemma a3u (u:List Bool):j3 u= if u.headD false then [true] else []:=by
  rcases u with _ | ⟨_ | _,_⟩ <;> rfl
lemma a9e (φ:Bool→ Bool→ Bool) (u v:List Bool) :
    b2 φ u v= [φ (u.headD false) (v.headD false)]:=by
  unfold b2
  rw [a3u,a3u]
  cases u.headD false <;> cases v.headD false <;> rfl
lemma a8f (φ:Bool→ Bool→ Bool) (u v:List Bool):(b2 φ u v).length= 1:=by
  rw [a9e]; rfl
def zwS (φ:Bool→ Bool→ Bool) (y:List Bool):List Bool :=
  a1 (a0 y).1.tail (a1 (a0 (a0 y).2).1.tail
    ((a0 (a0 y).2).2++b2 φ (a0 y).1 (a0 (a0 y).2).1))
lemma b4j (φ:Bool→ Bool→ Bool) (a b acc:List Bool) :
    zwS φ (a1 a (a1 b acc))= a1 a.tail (a1 b.tail (acc++b2 φ a b)):=by
  simp only [zwS,a5]
lemma b6v (φ:Bool→ Bool→ Bool):a4 (zwS φ):=by
  have h2:a4 (fun y=>(a0 y).2):=a3
  have ha:a4 (fun y=>(a0 y).1):=a6
  have hb:=cc h2 a6
  have hc:=cc h2 a3
  exact a7 (cc ha o3) (a7 (cc hb o3) (b8 hc (b48 φ ha hb)))
lemma b6l (φ:Bool→ Bool→ Bool) (y:List Bool):(zwS φ y).length≤ y.length+ 3:=by
  have h1:=n7 y
  have h2:=n7 (a0 y).2
  simp only [zwS,a02,List.length_append,a8f,List.length_tail]
  omega
lemma a9t (φ:Bool→ Bool→ Bool):∀ (a b acc:List Bool),a.length≤ b.length →
    (zwS φ)^[a.length] (a1 a (a1 b acc)) =
      a1 [] (a1 (b.drop a.length) (acc++List.zipWith φ a b))
  | [],b,acc,_=>by simp
  | x::a,[],acc,h=>by simp at h
  | x :: a, y :: b, acc, h => by
    rw [List.length_cons,Function.iterate_succ_apply,b4j,List.tail_cons,List.tail_cons,
      a9t φ a b _ (by simp at h; omega)]
    simp [a9e]
def zw (φ:Bool→ Bool→ Bool) (a b:List Bool):List Bool :=
  (a0 (a0 ((zwS φ)^[a.length] (a1 a (a1 b [])))).2).2
lemma b27 (φ:Bool→ Bool→ Bool) (a b:List Bool) (h:a.length≤ b.length) :
    zw φ a b= List.zipWith φ a b:=by
  rw [zw,a9t φ a b [] h]; simp [a5]
lemma y4 (φ:Bool→ Bool→ Bool) {a b:List Bool→ List Bool} (ha:a4 a)
    (hb:a4 b):a4 (fun s=>zw φ (a s) (b s)) :=
  cc (cc (v4 3 (b6v φ) (b6l φ) ha (a7 ha (a7 hb (b0 []))))
    a3) a3
def i5:List Bool→ List Bool→ List Bool
  | [],_=>[]
  | false::b,l=>false::i5 b l
  | true::b,l=>l.headD false::i5 b l.tail
def f6:List Bool→ List Bool→ List Bool
  | [],l=>l
  | false::b,l=>f6 b l
  | true::b,l=>f6 b l.tail
def scS (y:List Bool):List Bool :=
  a1 (a0 y).1.tail (a1 (sel (j3 (a0 y).1) (a0 (a0 y).2).1
    (a0 (a0 y).2).1.tail)
    ((a0 (a0 y).2).2++b2 (· && ·) (a0 y).1 (a0 (a0 y).2).1))
lemma b4d (b l acc:List Bool) :
    scS (a1 b (a1 l acc)) =
      a1 b.tail (a1 (sel (j3 b) l l.tail) (acc++b2 (· && ·) b l)):=by
  simp only [scS,a5]
lemma b7d:a4 scS:=by
  have h2:a4 (fun y=>(a0 y).2):=a3
  have ha:a4 (fun y=>(a0 y).1):=a6
  have hb:=cc h2 a6
  have hc:=cc h2 a3
  exact a7 (cc ha o3) (a7 (d6 (cc ha m6) hb (cc hb o3))
    (b8 hc (b48 _ ha hb)))
lemma b7a (y:List Bool):(scS y).length≤ y.length+ 3:=by
  have h1:=n7 y
  have h2:=n7 (a0 y).2
  have h3:(sel (j3 (a0 y).1) (a0 (a0 y).2).1
      (a0 (a0 y).2).1.tail).length≤ (a0 (a0 y).2).1.length:=by
    unfold sel; split_ifs <;> simp
  simp only [scS,a02,List.length_append,a8f,List.length_tail]
  omega
lemma a5s:∀ (b l acc:List Bool),
    scS^[b.length] (a1 b (a1 l acc))= a1 [] (a1 (f6 b l) (acc++i5 b l))
  | [],l,acc=>by simp [f6,i5]
  | c :: b, l, acc => by
    rw [List.length_cons,Function.iterate_succ_apply,b4d,List.tail_cons]
    cases c
    · rw [show sel (j3 (false :: b)) l l.tail = l from rfl, a5s b l]
      simp [f6,i5,a9e]
    · rw [show sel (j3 (true :: b)) l l.tail = l.tail from rfl, a5s b l.tail]
      simp [f6,i5,a9e]
def scF (b l:List Bool):List Bool:=scS^[b.length] (a1 b (a1 l []))
lemma b04 (b l:List Bool):scF b l= a1 [] (a1 (f6 b l) (i5 b l)):=by
  rw [scF,a5s]; simp
lemma a85 {b l:List Bool→ List Bool} (hb:a4 b) (hl:a4 l) :
    a4 (fun s=>scF (b s) (l s)) :=
  v4 3 b7d b7a hb (a7 hb (a7 hl (b0 [])))
def a3v (q s:List Bool):List Bool:=j3 (g8 q s)
lemma a70:∀ (s:List Bool) (n:ℕ),(s.drop n).headD false= s.getD n false
  | [],n=>by simp
  | a::s,0=>rfl
  | a::s,n+1=>by simpa using a70 s n
lemma b5w (q s:List Bool):a3v q s= if s.getD q.length false then [true] else []:=by
  rw [a3v,a3u,i6,a70]
lemma a4r {q s:List Bool→ List Bool} (hq:a4 q) (hs:a4 s) :
    a4 (fun z=>a3v (q z) (s z)) :=
  cc (e8 hq hs) m6
def fld:ℕ→ List Bool→ List Bool
  | 0,z=>(a0 z).1
  | n+1,z=>fld n (a0 z).2
def rst:ℕ→ List Bool→ List Bool
  | 0,z=>z
  | n+1,z=>rst n (a0 z).2
lemma a1v:∀ n,a4 (fld n)
  | 0=>a6
  | n+1=>b7 (cc a3 (a1v n)) (fun _=>rfl)
lemma b1o:∀ n,a4 (rst n)
  | 0=>g5
  | n+1=>b7 (cc a3 (b1o n)) (fun _=>rfl)
end LT
end asmP14
section asmP15
namespace LT
open Lib.Machines Lib.Universal
def ev (z:List Bool):List Bool:=(a0 z).2
def F (n:ℕ) (z:List Bool):List Bool:=fld n (ev z)
def bI (z:List Bool):List Bool:=fld 10 (ev z)
def bP (z:List Bool):List Bool:=rst 11 (ev z)
def xS (z:List Bool):List Bool:=scF (bI z) (s5 (a0 z).1)
def rem (z:List Bool):List Bool:=(a0 (a0 (xS z)).2).1
def xx (z:List Bool):List Bool:=(a0 (a0 (xS z)).2).2
def xT (z:List Bool):List Bool:=g8 (F 0 z) (xx z)
def bIT (z:List Bool):List Bool:=g8 (F 0 z) (bI z)
def bPT (z:List Bool):List Bool:=g8 (F 0 z) (bP z)
def bd1 (z:List Bool):List Bool:=u6 (zw (fun a b=>a && !b) (xT z) (F 5 z))
def bd2 (z:List Bool):List Bool :=
  u6 (zw (fun a b=>a && !b) (zw (· && ·) (zw (· && ·) (bIT z) (F 5 z)) (F 6 z)) (xT z))
def bd3 (z:List Bool):List Bool:=u6 (zw (· && ·) (xT z) (F 7 z))
def cM (w:List Bool):List Bool :=
  zw (· && ·) (xT (a0 w).2) (Dec.b5 (F 1 (a0 w).2) (a0 w).1 (F 9 (a0 w).2))
def cS (w:List Bool):List Bool :=
  sel (a3v (a0 w).1 (bI (a0 w).2)) []
    (u6 (sel (a3v (a0 w).1 (bP (a0 w).2)) (cM w)
      (zw (fun a b=>a && !b) (cM w) (bPT (a0 w).2))))
def nmF (w:List Bool):List Bool :=
  sel (g8 [true] (cS w)) (a4d (a3v (a0 w).1 (xx (a0 w).2)) (cS w)) [true]
def bd4 (z:List Bool):List Bool :=
  (List.range (F 0 z).length).flatMap (fun v=>nmF (a1 (un v) z))
def rr (w:List Bool):List Bool:=Dec.b5 (true::F 1 (a0 w).2) (a0 w).1 (F 8 (a0 w).2)
def h1 (w:List Bool):List Bool:=u6 (zw (· && ·) (xT (a0 w).2) (rr w).tail)
def h2 (w:List Bool):List Bool :=
  u6 (zw (· && ·) (zw (· && ·) (xT (a0 w).2) (bPT (a0 w).2)) (rr w).tail)
def rwF (w:List Bool):List Bool :=
  sel (sel (h1 w) [] (sel (h2 w) [true] [])) [true,true] (sel (j3 (rr w)) [true] [true,true,true])
def dsc (z:List Bool):List Bool :=
  (List.range (F 2 z).tail.length).flatMap (fun r=>rwF (a1 (un r) z))
def dsz (z:List Bool):List Bool:=u6 (zw (fun a b=>a && !b) (xT z) (bPT z))
def b03 (z:List Bool):List Bool :=
  sel (rem z++bd1 z++bd2 z++bd3 z++bd4 z)
    (g4 (F 4 z) (f3 (j0 (F 3 z) (j0 (dsz z) (F 2 z)++dsc z))++[true])) (f3 (F 4 z))
def a9f (pU env:List Bool):List Bool :=
  (List.range pU.length).flatMap (fun i=>b03 (a1 (un i) env))
lemma b0i:a4 ev :=
  b7 (a3) (fun _=>rfl)
lemma t8 (n:ℕ):a4 (F n) :=
  b7 (cc b0i (a1v n)) (fun _=>rfl)
lemma b0b:a4 bI :=
  b7 (cc b0i (a1v 10)) (fun _=>rfl)
lemma b3l:a4 bP :=
  b7 (cc b0i (b1o 11)) (fun _=>rfl)
lemma b3z:a4 xS :=
  b7 (a85 b0b (cc a6 n9)) (fun _=>rfl)
lemma b89:a4 rem :=
  b7 (cc (cc b3z a3) a6) (fun _=>rfl)
lemma b43:a4 xx :=
  b7 (cc (cc b3z a3) a3) (fun _=>rfl)
lemma a20:a4 xT :=
  b7 (e8 (t8 0) b43) (fun _=>rfl)
lemma b6m:a4 bIT :=
  b7 (e8 (t8 0) b0b) (fun _=>rfl)
lemma a8c:a4 bPT :=
  b7 (e8 (t8 0) b3l) (fun _=>rfl)
lemma b7j:a4 bd1 :=
  b7 (cc (y4 (fun a b=>a && !b) a20 (t8 5)) u8) (fun _=>rfl)
lemma b7w:a4 bd2 :=
  b7 (cc (y4 (fun a b=>a && !b) (y4 (· && ·) (y4 (· && ·) b6m (t8 5)) (t8 6)) a20) u8) (fun _=>rfl)
lemma b74:a4 bd3 :=
  b7 (cc (y4 (· && ·) a20 (t8 7)) u8) (fun _=>rfl)
lemma y3 {f:List Bool→ List Bool} (hf:a4 f):a4 (fun w=>f (a0 w).2) :=
  b7 (cc a3 hf) (fun _=>rfl)
lemma b3j:a4 cM :=
  b7 (y4 (· && ·) (y3 a20) (Dec.k5 (y3 (t8 1)) a6 (y3 (t8 9)))) (fun _=>rfl)
lemma b49:a4 cS :=
  b7 (d6 (a4r a6 (y3 b0b)) (b0 [])
    (cc (d6 (a4r a6 (y3 b3l)) b3j
      (y4 (fun a b=>a && !b) b3j (y3 a8c))) u8)) (fun _=>rfl)
lemma b6p:a4 nmF :=
  b7 (d6 (e8 (b0 [true]) b49)
    (b6e (a4r a6 (y3 b43)) b49) (b0 [true])) (fun _=>rfl)
lemma b77:a4 bd4 :=
  b7 (d9 b6p (t8 0) g5) (fun _=>rfl)
lemma a9x:a4 rr :=
  b7 (Dec.k5 (b8 (b0 [true]) (y3 (t8 1))) a6 (y3 (t8 8))) (fun _=>rfl)
lemma b9h:a4 h1 :=
  b7 (cc (y4 (· && ·) (y3 a20) (cc a9x o3)) u8) (fun _=>rfl)
lemma c06:a4 h2 :=
  b7 (cc (y4 (· && ·) (y4 (· && ·) (y3 a20) (y3 a8c)) (cc a9x o3)) u8) (fun _=>rfl)
lemma b7o:a4 rwF :=
  b7 (d6 (d6 b9h (b0 []) (d6 c06 (b0 [true]) (b0 [])))
    (b0 [true,true]) (d6 (cc a9x m6) (b0 [true]) (b0 [true,true,true]))) (fun _=>rfl)
lemma b7h:a4 dsc :=
  b7 (d9 b7o (cc (t8 2) o3) g5) (fun _=>rfl)
lemma b7e:a4 dsz :=
  b7 (cc (y4 (fun a b=>a && !b) a20 a8c) u8) (fun _=>rfl)
lemma b62:a4 b03 :=
  b7 (d6 (b8 (b8 (b8 (b8 b89 b7j) b7w) b74) b77)
    (n4 (t8 4) (b8 (cc (g9 (t8 3)
      (b8 (g9 b7e (t8 2)) b7h)) n6) (b0 [true])))
    (cc (t8 4) n6)) (fun _=>rfl)
lemma b3q {pU env:List Bool→ List Bool} (hp:a4 pU) (he:a4 env) :
    a4 (fun s=>a9f (pU s) (env s)) :=
  b7 (d9 b62 hp he) (fun _=>rfl)
end LT
end asmP15
section asmP16
namespace LT
open Lib.Machines Lib.Universal Dec
def a7g (k:ℕ):List Bool :=
  (List.range k).flatMap (fun v=>(pairs k).map (fun e=>decide (v= e.1.val∨ v= e.2.val)))
def i3 (k W Wt : ℕ) (E P H : Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (Bi Bp:Finset ℕ):List Bool :=
  a1 (un k) (a1 (un (b6 k)) (a1 (un (rows.length+1)) (a1 (un W) (a1 (un Wt)
  (a1 (mask E) (a1 (mask P) (a1 (mask H) (a1 (rows.flatMap j8) (a1 (a7g k)
  (a1 (a9 k Bi) (a9 k Bp)))))))))))
section Env
variable (k W Wt:ℕ) (E P H:Finset (Fin k × Fin k))
  (rows:List (Finset (Fin k × Fin k) × Bool)) (Bi Bp:Finset ℕ) (u:List Bool)
lemma f5 :
    F 0 (a1 u (i3 k W Wt E P H rows Bi Bp))= un k ∧
    F 1 (a1 u (i3 k W Wt E P H rows Bi Bp))= un (b6 k) ∧
    F 2 (a1 u (i3 k W Wt E P H rows Bi Bp))= un (rows.length+1) ∧
    F 3 (a1 u (i3 k W Wt E P H rows Bi Bp))= un W ∧
    F 4 (a1 u (i3 k W Wt E P H rows Bi Bp))= un Wt ∧
    F 5 (a1 u (i3 k W Wt E P H rows Bi Bp))= mask E ∧
    F 6 (a1 u (i3 k W Wt E P H rows Bi Bp))= mask P ∧
    F 7 (a1 u (i3 k W Wt E P H rows Bi Bp))= mask H ∧
    F 8 (a1 u (i3 k W Wt E P H rows Bi Bp))= rows.flatMap j8 ∧
    F 9 (a1 u (i3 k W Wt E P H rows Bi Bp))= a7g k ∧
    bI (a1 u (i3 k W Wt E P H rows Bi Bp))= a9 k Bi ∧
    bP (a1 u (i3 k W Wt E P H rows Bi Bp))= a9 k Bp:=by
  simp only [F,bI,bP,ev,fld,rst,i3,a5,and_self]
end Env
lemma y2 {α:Type} (φ:Bool→ Bool→ Bool) (L:List α) (f g:α→ Bool) :
    zw φ (L.map f) (L.map g)= L.map (fun e=>φ (f e) (g e)):=by
  rw [b27 _ _ _ (by simp)]
  induction L with
  | nil=>rfl
  | cons a L ih=>simp [ih]
lemma a00 {α:Type} (L:List α) (f:α→ Bool) :
    u6 (L.map f)= []↔ ∀ e∈ L,f e= false:=by
  simp [u6,List.filter_eq_nil_iff]
lemma a1y {α:Type} (L:List α) (f:α→ Bool) :
    (u6 (L.map f)).length= (L.filter f).length:=by
  induction L with
  | nil=>rfl
  | cons a L ih=>cases h:f a <;> simp [u6,List.filter_cons,h] at ih ⊢ <;> omega
lemma a6z (k:ℕ) (S:Finset ℕ) :
    a9 k S= (List.range k).map (fun v=>decide (v∈ S)) ++
      (pairs k).map (fun e=>decide (tag k e∈ S)):=by
  simp [a9,layout,List.map_append,List.map_map,Function.comp_def]
lemma a2a (k:ℕ) (S:Finset ℕ) :
    g8 (un k) (a9 k S)= (pairs k).map (fun e=>decide (tag k e∈ S)):=by
  rw [i6,a6z,b4,List.drop_left' (by simp)]
lemma a1f (k:ℕ) (S:Finset ℕ) (v:ℕ) (hv:v< k) :
    a3v (un v) (a9 k S)= if v∈ S then [true] else []:=by
  rw [b5w,b4,a6z,List.getD_append _ _ _ _ (by simpa using hv)]
  simp [hv]
lemma b52 (k v:ℕ) (hv:v< k) :
    Dec.b5 (un (b6 k)) (un v) (a7g k) =
      (pairs k).map (fun e=>decide (v= e.1.val∨ v= e.2.val)):=by
  rw [a7g,Dec.l8 _ (b6 k) (fun a=>by simp [s8]) _ v (by simpa using hv)
    _ _ (by simp) (by simp)]
  simp
lemma b5e (k:ℕ) (rows:List (Finset (Fin k × Fin k) × Bool)) (r:ℕ)
    (hr:r< rows.length) :
    Dec.b5 (true::un (b6 k)) (un r) (rows.flatMap j8)= j8 (rows[r]'hr) :=
  Dec.l8 _ (b6 k+ 1) (fun a=>a07 a) _ r hr _ _ (by simp) (by simp)
end LT
end asmP16
section asmP17
namespace LT
open Lib.Machines Lib.Universal Dec
lemma a12 (k:ℕ):(pairs k).Nodup:=by
  unfold pairs
  rw [List.nodup_flatMap]
  refine ⟨fun i _=>((List.nodup_finRange k).filter _).map (fun a b h=>by simpa using h),?_⟩
  refine (List.nodup_finRange k).pairwise_of_forall_ne (fun a _ b _ hab=>?_)
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro e he he'
  simp only [List.mem_map] at he he'
  obtain ⟨x,_,rfl⟩:=he
  obtain ⟨y,_,hy⟩:=he'
  exact hab (congrArg Prod.fst hy).symm
lemma a29 (k:ℕ):(layout k).Nodup:=by
  unfold layout
  rw [List.nodup_append]
  refine ⟨List.nodup_range,(a12 k).map (y6 k),?_⟩
  intro a ha b hb hab
  simp only [List.mem_range] at ha
  simp only [List.mem_map] at hb
  obtain ⟨e,_,rfl⟩:=hb
  have:=a13 k e
  omega
def j9 (L:List ℕ) (x:List Bool):List ℕ:=((L.zip x).filter (·.2)).map (·.1)
lemma m5 (a:ℕ) (L:List ℕ) (b:Bool) (x:List Bool) :
    j9 (a::L) (b::x)= if b then a::j9 L x else j9 L x:=by
  cases b <;> simp [j9,List.filter_cons]
lemma a06:∀ (L:List ℕ) (x:List Bool),∀ v∈ j9 L x,v∈ L
  | [],x,v,h=>by simp [j9] at h
  | a::L,[],v,h=>by simp [j9] at h
  | a :: L, b :: x, v, h => by
    rw [m5] at h
    split_ifs at h
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (a06 L x v h)
    · exact List.mem_cons_of_mem _ (a06 L x v h)
lemma b0d:∀ (L:List ℕ) (x:List Bool),L.Nodup→ L.length= x.length →
    x= L.map (fun v=>decide (v∈ j9 L x))
  | [],[],_,_=>rfl
  | [],_::_,_,h=>by simp at h
  | _::_,[],_,h=>by simp at h
  | a :: L, b :: x, hn, hl => by
    rw [List.nodup_cons] at hn
    have ih:=b0d L x hn.2 (by simpa using hl)
    rw [List.map_cons,m5]
    have hnot:a∉ j9 L x:=fun h=>hn.1 (a06 L x a h)
    have hmap:∀ c:List ℕ,(∀ v∈ L,v∉ c) →
        L.map (fun v=>decide (v∈ c++j9 L x))= L.map (fun v=>decide (v∈ j9 L x)):=by
      intro c hc
      apply List.map_congr_left
      intro v hv
      simp [hc v hv]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [decide_eq_false hnot,← ih]
    · simp only [↓reduceIte, List.mem_cons, true_or, decide_true]
      have:=hmap [a] (fun v hv h=>hn.1 (by simp at h; exact h ▸ hv))
      simp only [List.singleton_append] at this
      rw [show (L.map fun v=>decide (v= a∨ v∈ j9 L x)) =
        L.map (fun v=>decide (v∈ a::j9 L x)) from by simp,this,← ih]
lemma a23:∀ (b l:List Bool),(i5 b l).length= b.length
  | [],_=>rfl
  | false::b,l=>by simp [i5,a23 b l]
  | true::b,l=>by simp [i5,a23 b l.tail]
lemma y5 (S:Finset ℕ):∀ (L:List ℕ) (l:List Bool),
    ∀ v∈ j9 L (i5 (L.map (fun v=>decide (v∈ S))) l),v∈ S
  | [],l,v,h=>by simp [j9,i5] at h
  | a :: L, l, v, h => by
    by_cases ha:a∈ S
    · rw [List.map_cons, decide_eq_true ha, i5, m5] at h
      split_ifs at h
      · rcases List.mem_cons.mp h with h | h
        · exact h ▸ ha
        · exact y5 S L l.tail v h
      · exact y5 S L l.tail v h
    · rw [List.map_cons, decide_eq_false ha, i5, m5] at h
      exact y5 S L l v h
def Xs (k:ℕ) (Bi:Finset ℕ) (ι:ℕ):Finset ℕ :=
  (j9 (layout k) (i5 (a9 k Bi) ι.bits)).toFinset
lemma a1c (k:ℕ) (Bi:Finset ℕ) (ι:ℕ):Xs k Bi ι⊆ Bi:=by
  intro v hv
  rw [Xs,List.mem_toFinset] at hv
  exact y5 Bi (layout k) ι.bits v hv
lemma a4k (k:ℕ) (Bi:Finset ℕ) (ι:ℕ):∀ v∈ Xs k Bi ι,v∈ layout k:=by
  intro v hv
  rw [Xs,List.mem_toFinset] at hv
  exact a06 _ _ v hv
lemma a83 (k:ℕ) (Bi:Finset ℕ) (ι:ℕ) :
    i5 (a9 k Bi) ι.bits= a9 k (Xs k Bi ι):=by
  have h:=b0d (layout k) (i5 (a9 k Bi) ι.bits) (a29 k)
    (by rw [a23,a9,List.length_map])
  rw [h,Xs,a9]
  refine List.map_congr_left (fun v _=>?_)
  simp
lemma a0t (k:ℕ) (Bi:Finset ℕ) (ι:ℕ) (e:Fin k × Fin k) (h:tag k e∈ Xs k Bi ι) :
    e.1< e.2:=by
  have h1:=(a0p k _).mp (a4k k Bi ι _ h)
  rcases h1 with h1 | ⟨e',h2,h3⟩
  · have:=a13 k e; omega
  · rw [← y6 k h3]; exact h2
end LT
end asmP17
section asmP18
namespace LT
open Lib.Machines Lib.Universal Dec
section Eval
variable (k W Wt:ℕ) (E P H:Finset (Fin k × Fin k))
  (rows:List (Finset (Fin k × Fin k) × Bool)) (Bi Bp:Finset ℕ) (ι:ℕ)
lemma b6i:xS (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= a1 [] (a1 (f6 (a9 k Bi) ι.bits) (a9 k (Xs k Bi ι))):=by
  rw [xS,(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.2.2.1,a5,
    w7,b4,b04,a83]
lemma b9i:rem (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= f6 (a9 k Bi) ι.bits:=by
  rw [rem,b6i,a5,a5]
lemma b6h:xx (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= a9 k (Xs k Bi ι):=by
  rw [xx,b6i,a5,a5]
lemma a3f:xT (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= (pairs k).map (fun e=>decide (tag k e∈ (Xs k Bi ι))):=by
  rw [xT,b6h,(f5 k W Wt E P H rows Bi Bp (un ι)).1,a2a]
lemma b8m:bIT (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= (pairs k).map (fun e=>decide (tag k e∈ Bi)):=by
  rw [bIT,(f5 k W Wt E P H rows Bi Bp (un ι)).1,
    (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.2.2.1,a2a]
lemma b07:bPT (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= (pairs k).map (fun e=>decide (tag k e∈ Bp)):=by
  rw [bPT,(f5 k W Wt E P H rows Bi Bp (un ι)).1,
    (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.2.2.2,a2a]
lemma b8e:bd1 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= []↔ ∀ e∈ pairs k,tag k e∈ (Xs k Bi ι)→ e∈ E:=by
  rw [bd1,a3f,(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.1,mask,y2,
    a00]
  simp
lemma b8k:bd2 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= []↔ ∀ e∈ pairs k,tag k e∈ Bi→ e∈ E→ e∈ P→ tag k e∈ (Xs k Bi ι):=by
  rw [bd2,a3f,b8m,(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.1,
    (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.1,mask,mask,y2,y2,
    y2,a00]
  simp
lemma b9m:bd3 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= []↔ ∀ e∈ pairs k,tag k e∈ (Xs k Bi ι)→ e∉ H:=by
  rw [bd3,a3f,(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.1,mask,y2,
    a00]
  simp
lemma b9z:(dsz (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))).length =
    ((pairs k).filter (fun e=>decide (tag k e∈ (Xs k Bi ι)) && !decide (tag k e∈ Bp))).length:=by
  rw [dsz,a3f,b07,y2,a1y]
def w2 (v:ℕ):ℕ :=
  if v∈ Bi then ((pairs k).filter (fun e=>decide (tag k e∈ (Xs k Bi ι)) &&
    decide (v= e.1.val∨ v= e.2.val) && !(decide (v∈ Bp) && decide (tag k e∈ Bp)))).length
  else 0
lemma c0m (v:ℕ) (hv:v< k):(cS (a1 (un v) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))).length= w2 k Bi Bp ι v:=by
  have hcM:cM (a1 (un v) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= (pairs k).map (fun e=>decide (tag k e∈ (Xs k Bi ι)) &&
      decide (v= e.1.val∨ v= e.2.val)):=by
    simp only [cM,a5]
    rw [a3f,(f5 k W Wt E P H rows Bi Bp (un ι)).2.1,
      (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.2.1,b52 k v hv,y2]
  simp only [cS,a5]
  rw [(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.2.2.1,
    (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.2.2.2,a1f k _ v hv,
    a1f k _ v hv,hcM,b07,y2,w2]
  by_cases hi:v∈ Bi
  · by_cases hp : v ∈ Bp
    · simp only [hi,hp,↓reduceIte,sel,reduceCtorEq,a1y,decide_true,Bool.true_and]
    · simp only [hi,hp,↓reduceIte,sel,reduceCtorEq,a1y,decide_false,
        Bool.false_and,Bool.not_false,Bool.and_true]
  · simp [hi,sel]
lemma b19 (f a b:List Bool) (hb:b≠ []):sel f a b= []↔ f= []∧ a= []:=by
  unfold sel; split_ifs with h <;> simp [h,hb]
lemma a9s (a b:List Bool):a4d a b= []↔ (a= []↔ b= []):=by
  unfold a4d sel; split_ifs <;> simp_all
lemma b9q (v:ℕ) (hv:v< k):nmF (a1 (un v) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= [] ↔
    w2 k Bi Bp ι v≤ 1∧ (v∈ (Xs k Bi ι)↔ w2 k Bi Bp ι v= 1):=by
  rw [nmF,b19 _ _ _ (by simp),a9s]
  simp only [a5]
  rw [b6h,
    a1f k _ v hv,i6,List.drop_eq_nil_iff,
    ← List.length_eq_zero_iff (l:=cS (a1 (un v) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))),c0m _ _ _ _ _ _ _ _ _ _ _ hv]
  simp only [List.length_cons,List.length_nil,zero_add]
  generalize w2 k Bi Bp ι v= c
  by_cases hx:v∈ (Xs k Bi ι) <;> simp [hx] <;> omega
lemma b9e:bd4 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))= []↔ ∀ v< k,w2 k Bi Bp ι v≤ 1∧ (v∈ (Xs k Bi ι)↔ w2 k Bi Bp ι v= 1):=by
  rw [bd4,(f5 k W Wt E P H rows Bi Bp (un ι)).1,b4,List.flatMap_eq_nil_iff]
  simp only [List.mem_range]
  exact forall₂_congr (fun v hv=>b9q k W Wt E P H rows Bi Bp ι v hv)
def a2x (r:Finset (Fin k × Fin k) × Bool):ℕ :=
  if (∃ e∈ pairs k,tag k e∈ (Xs k Bi ι)∧ e∈ r.1)∧ ¬ (∃ e∈ pairs k,tag k e∈ (Xs k Bi ι)∧ tag k e∈ Bp∧ e∈ r.1)
  then (if r.2 then 3 else 1) else 2
lemma b92 (r:ℕ) (hr:r< rows.length) :
    (rwF (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))).length= a2x k Bi Bp ι (rows[r]'hr):=by
  have hrr:rr (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= j8 (rows[r]'hr):=by
    simp only [rr,a5]
    rw [(f5 k W Wt E P H rows Bi Bp (un ι)).2.1,
      (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.2.2.2.2.1,b5e k rows r hr]
  have e1:h1 (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= []↔ ¬ ∃ e∈ pairs k,tag k e∈ (Xs k Bi ι)∧ e∈ (rows[r]'hr).1:=by
    rw [h1,hrr]
    simp only [a5]
    rw [a3f,j8,List.tail_cons,mask,y2,a00]
    simp
  have e2:h2 (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= [] ↔
      ¬ ∃ e∈ pairs k,tag k e∈ (Xs k Bi ι)∧ tag k e∈ Bp∧ e∈ (rows[r]'hr).1:=by
    rw [h2,hrr]
    simp only [a5]
    rw [a3f,b07,j8,List.tail_cons,mask,y2,y2,
      a00]
    simp [and_assoc]
  have e3:j3 (rr (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))))= if (rows[r]'hr).2 then [true] else []:=by
    rw [hrr,j8,a3u]; rfl
  rw [rwF,e3,a2x]
  by_cases c1:h1 (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= []
  · have c1' := e1.mp c1
    simp [sel,c1,c1']
  · have c1':∃ e∈ pairs k,tag k e∈ (Xs k Bi ι)∧ e∈ (rows[r]'hr).1:=by
      by_contra h; exact c1 (e1.mpr h)
    by_cases c2:h2 (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))= []
    · have c2' := e2.mp c2
      cases hb:(rows[r]'hr).2 <;> simp [sel,c1,c2,c1',c2',hb]
    · have c2':∃ e∈ pairs k,tag k e∈ (Xs k Bi ι)∧ tag k e∈ Bp∧ e∈ (rows[r]'hr).1:=by
        by_contra h; exact c2 (e2.mpr h)
      simp [sel,c1,c2,c2']
lemma b9l:(dsc (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))).length= (rows.map (a2x k Bi Bp ι)).sum:=by
  rw [dsc,(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.1,a1w,List.tail_cons,b4,
    List.length_flatMap]
  rw [show (List.map (fun r=>(rwF (a1 (un r) (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))).length) (List.range rows.length)) =
      rows.map (a2x k Bi Bp ι) from ?_]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map,List.getElem_range]
  exact b92 k W Wt E P H rows Bi Bp ι n (by simpa using h1)
open Classical in
lemma b6k:b03 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)) =
    if f6 (a9 k Bi) ι.bits= []∧ (∀ e∈ pairs k,tag k e∈ (Xs k Bi ι)→ e∈ E) ∧
      (∀ e∈ pairs k,tag k e∈ Bi→ e∈ E→ e∈ P→ tag k e∈ (Xs k Bi ι)) ∧
      (∀ e∈ pairs k,tag k e∈ (Xs k Bi ι)→ e∉ H) ∧
      (∀ v< k,w2 k Bi Bp ι v≤ 1∧ (v∈ (Xs k Bi ι)↔ w2 k Bi Bp ι v= 1))
    then g4 (un Wt) (List.replicate (W* (((pairs k).filter (fun e=>decide (tag k e∈ (Xs k Bi ι)) &&
      !decide (tag k e∈ Bp))).length* (rows.length+ 1)+ (rows.map (a2x k Bi Bp ι)).sum)) false
      ++ [true])
    else f3 (un Wt):=by
  rw [b03,(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.2.1]
  have hb:f3 (j0 (F 3 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))) (j0 (dsz (a1 (un ι) (i3 k W Wt E P H rows Bi Bp))) (F 2 (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))++dsc (a1 (un ι) (i3 k W Wt E P H rows Bi Bp)))) =
      List.replicate (W* (((pairs k).filter (fun e=>decide (tag k e∈ (Xs k Bi ι)) &&
      !decide (tag k e∈ Bp))).length* (rows.length+ 1)+ (rows.map (a2x k Bi Bp ι)).sum)) false:=by
    rw [(f5 k W Wt E P H rows Bi Bp (un ι)).2.2.2.1,
      (f5 k W Wt E P H rows Bi Bp (un ι)).2.2.1]
    rw [f3,j0,j0,List.length_append,b9z,b9l]
    simp only [un,List.map_replicate,List.length_replicate]
  rw [hb]
  unfold sel
  simp only [List.append_eq_nil_iff,b9i,b8e,b8k,b9m,b9e]
  split_ifs <;> simp_all
end Eval
end LT
end asmP18
section asmP19
namespace LT
open Lib.Machines Lib.Universal Dec
lemma b12 {k:ℕ} (q:Fin k × Fin k→ Prop) [DecidablePred q]
    (hq:∀ e,q e→ e.1< e.2) :
    ((pairs k).filter (fun e=>decide (q e))).length= (Finset.univ.filter q).card:=by
  have hnd:((pairs k).filter (fun e=>decide (q e))).Nodup:=(a12 k).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter,
    Finset.mem_univ,true_and,q0]
  exact ⟨fun h=>h.2,fun h=>⟨hq e h,h⟩⟩
lemma a49 {k:ℕ} (q:Fin k × Fin k→ Bool) (hq:∀ e,q e= true→ e.1< e.2) :
    ((pairs k).filter q).length= (Finset.univ.filter (fun e=>q e= true)).card:=by
  have h:=b12 (k:=k) (fun e=>q e= true) hq
  simpa using h
lemma b51 {k:ℕ} (Y:Finset (Fin k × Fin k)):w3 [] Y= 0:=by
  simp [w3]
section Bridge
variable (k W Wt:ℕ) (E P H:Finset (Fin k × Fin k))
  (rows:List (Finset (Fin k × Fin k) × Bool)) {t:ℕ} (par:Fin (t+1)→ Fin (t+1))
  (B:Fin (t+1)→ Finset ℕ) (i:Fin (t+1)) (ι:ℕ)
def u7:Finset ℕ:=if i= 0 then ∅ else B (par i)
lemma a3p (x:ℕ):x∈ u7 par B i↔ i≠ 0∧ x∈ B (par i):=by
  unfold u7; split_ifs with h <;> simp [h]
def c8:Finset (Fin k × Fin k):=Finset.univ.filter (fun e=>c6 k e∈ Xs k (B i) ι)
def g6:Finset (Fin k):=Finset.univ.filter (fun v=>v.val∈ Xs k (B i) ι)
lemma b6b (r:Finset (Fin k × Fin k) × Bool) :
    (a2x k (B i) (u7 par B i) ι r:ℤ)= 2 +
      ((if (c8 k B i ι∩ r.1).Nonempty then a3w r.2 else 0) -
       (if (((c8 k B i ι).filter (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i))) ∩
          r.1).Nonempty then a3w r.2 else 0)):=by
  have e1:(c8 k B i ι∩ r.1).Nonempty↔ ∃ e∈ pairs k,tag k e∈ Xs k (B i) ι∧ e∈ r.1:=by
    constructor
    · rintro ⟨e, he⟩
      simp only [Finset.mem_inter,c8,Finset.mem_filter,Finset.mem_univ,true_and] at he
      exact ⟨e,(q0 e).mpr (a0t k _ ι e he.1),he.1,he.2⟩
    · rintro ⟨e, _, h1, h2⟩
      exact ⟨e,by simp [c8,Finset.mem_inter]; exact ⟨h1,h2⟩⟩
  have e2:((c8 k B i ι).filter (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i)) ∩
      r.1).Nonempty ↔
      ∃ e∈ pairs k,tag k e∈ Xs k (B i) ι∧ tag k e∈ u7 par B i∧ e∈ r.1:=by
    constructor
    · rintro ⟨e, he⟩
      simp only [Finset.mem_inter,c8,Finset.mem_filter,Finset.mem_univ,true_and] at he
      exact ⟨e,(q0 e).mpr (a0t k _ ι e he.1.1),he.1.1,
        (a3p par B i _).mpr he.1.2.2,he.2⟩
    · rintro ⟨e, _, h1, h2, h3⟩
      refine ⟨e,?_⟩
      have h2':=(a3p par B i _).mp h2
      simp only [Finset.mem_inter,c8,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨⟨h1,a1c k _ ι h1,h2'⟩,h3⟩
  unfold a2x
  obtain ⟨R,b⟩:=r
  by_cases c1:(c8 k B i ι∩ R).Nonempty <;>
    by_cases c2:((c8 k B i ι).filter (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i)) ∩
      R).Nonempty
  · rw [if_neg (fun h=>h.2 (e2.mp c2)),if_pos c1,if_pos c2]; simp
  · rw [if_pos ⟨e1.mp c1, fun h => c2 (e2.mpr h)⟩, if_pos c1, if_neg c2]
    cases b <;> simp [a3w]
  · exfalso
    obtain ⟨e,he⟩:=c2
    exact c1 ⟨e,by simp only [Finset.mem_inter,Finset.mem_filter] at he ⊢; exact ⟨he.1.1,he.2⟩⟩
  · rw [if_neg (fun h=>c1 (e1.mpr h.1)),if_neg c1,if_neg c2]; simp
lemma b3f:(rows.map (a2x k (B i) (u7 par B i) ι)).sum =
    r9 rows par B i (c8 k B i ι):=by
  unfold r9 a04
  have hs:(c8 k B i ι).filter (fun e=>c6 k e∈ B i)= c8 k B i ι:=by
    ext e; simp only [Finset.mem_filter,and_iff_left_iff_imp]
    intro h; simp only [c8,Finset.mem_filter] at h; exact a1c k _ ι h.2
  rw [hs]
  suffices h:((rows.map (a2x k (B i) (u7 par B i) ι)).sum:ℤ) =
      w3 rows (c8 k B i ι) - w3 rows ((c8 k B i ι).filter
        (fun e=>c6 k e∈ B i∧ i≠ 0∧ c6 k e∈ B (par i)))+ 2* (rows.length:ℤ) by
    rw [← h]; exact (Int.toNat_natCast _).symm
  induction rows with
  | nil=>simp [b51]
  | cons r rows ih =>
    rw [List.map_cons,List.sum_cons,Nat.cast_add,ih,a2l,a2l,b6b,
      List.length_cons]
    push_cast
    ring
lemma b5n:((pairs k).filter (fun e=>decide (tag k e∈ Xs k (B i) ι) &&
    !decide (tag k e∈ u7 par B i))).length= w9 par B i (c8 k B i ι):=by
  rw [a49 _ (fun e he=>a0t k _ ι e (by simp at he; exact he.1)),w9]
  congr 1
  ext e
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,c8,a3p,Bool.and_eq_true,
    decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1,h2⟩; exact ⟨h1,a1c k _ ι h1,h2⟩
  · rintro ⟨h1,_,h2⟩; exact ⟨h1,h2⟩
lemma b9j (v:Fin k):m0 par B {i} (c8 k B i ι) v= w2 k (B i) (u7 par B i) ι v.val:=by
  rw [m0,Finset.sum_singleton,a5d,w2]
  split_ifs with hv
  · rw [a49 _ (fun e he => a0t k _ ι e (by simp at he; exact he.1.1))]
    congr 1
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,c8,a3p,Fin.ext_iff,
      Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    constructor
    · rintro ⟨h1, h2, _, _, h3⟩
      refine ⟨⟨h1,h2⟩,?_⟩
      by_contra hc
      push_neg at hc
      exact h3 ⟨hc.1.1,hc.2.2,hc.1.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1,h2,a1c k _ ι h1,hv,fun ⟨a,c,b⟩=>?_⟩
      rcases h3 with h3 | h3
      · exact h3 ⟨a,b⟩
      · exact h3 ⟨a,c⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro e - ⟨-,-,h,-⟩
    exact hv h
lemma a9o (v:ℕ) (hv:v∉ B i):w2 k (B i) (u7 par B i) ι v= 0:=by
  simp [w2,hv]
lemma b67 (hE:∀ e∈ E,e.1< e.2) :
    (f6 (a9 k (B i)) ι.bits= []∧ (∀ e∈ pairs k,tag k e∈ Xs k (B i) ι→ e∈ E) ∧
      (∀ e∈ pairs k,tag k e∈ B i→ e∈ E→ e∈ P→ tag k e∈ Xs k (B i) ι) ∧
      (∀ e∈ pairs k,tag k e∈ Xs k (B i) ι→ e∉ H) ∧
      (∀ v< k,w2 k (B i) (u7 par B i) ι v≤ 1 ∧
        (v∈ Xs k (B i) ι↔ w2 k (B i) (u7 par B i) ι v= 1))) ↔
    (f6 (a9 k (B i)) ι.bits= []∧ c8 k B i ι⊆ b9 E B {i} ∧
        n1 E P H par B {i} (c8 k B i ι)∧ g3 par B {i} i (c8 k B i ι)= g6 k B i ι):=by
  have hX:∀ e:Fin k × Fin k,e∈ c8 k B i ι↔ tag k e∈ Xs k (B i) ι:=by
    intro e; simp [c8]; rfl
  have c1:(∀ e∈ pairs k,tag k e∈ Xs k (B i) ι→ e∈ E)↔ c8 k B i ι⊆ b9 E B {i}:=by
    constructor
    · intro h e he
      rw [hX] at he
      exact (f8 E B {i} e).mpr ⟨h e ((q0 e).mpr (a0t k _ ι e he)) he,
        i,Finset.mem_singleton_self i,a1c k _ ι he⟩
    · intro h e _ he
      exact ((f8 E B {i} e).mp (h ((hX e).mpr he))).1
  have c2:(∀ e∈ pairs k,tag k e∈ B i→ e∈ E→ e∈ P→ tag k e∈ Xs k (B i) ι) ↔
      (∀ e∈ b9 E B {i},e∈ P→ e∈ c8 k B i ι):=by
    constructor
    · intro h e he hp
      obtain ⟨hE',a,ha,hb⟩:=(f8 E B {i} e).mp he
      rw [Finset.mem_singleton] at ha
      subst ha
      exact (hX e).mpr (h e ((q0 e).mpr (hE e hE')) hb hE' hp)
    · intro h e _ hb hE' hp
      exact (hX e).mp (h e ((f8 E B {i} e).mpr ⟨hE',i,Finset.mem_singleton_self i,hb⟩) hp)
  have c3:(∀ e∈ pairs k,tag k e∈ Xs k (B i) ι→ e∉ H)↔ (∀ e∈ c8 k B i ι,e∉ H):=by
    constructor
    · intro h e he
      rw [hX] at he
      exact h e ((q0 e).mpr (a0t k _ ι e he)) he
    · intro h e _ he
      exact h e ((hX e).mpr he)
  have c4:(∀ v< k,w2 k (B i) (u7 par B i) ι v≤ 1 ∧
        (v∈ Xs k (B i) ι↔ w2 k (B i) (u7 par B i) ι v= 1)) ↔
      ((∀ v:Fin k,m0 par B {i} (c8 k B i ι) v≤ 1) ∧
        g3 par B {i} i (c8 k B i ι)= g6 k B i ι):=by
    simp only [b9j,Finset.ext_iff,k3,g6,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      refine ⟨fun v=>(h v.val v.isLt).1,fun v=>?_⟩
      by_cases hb:v.val∈ B i
      · exact ⟨fun h'=>(h v.val v.isLt).2.mpr h'.2,fun h'=>⟨hb,(h v.val v.isLt).2.mp h'⟩⟩
      · rw [a9o k par B i ι _ hb]
        exact ⟨fun h'=>absurd h'.1 hb,fun h'=>absurd (a1c k _ ι h') hb⟩
    · rintro ⟨h1, h2⟩ v hv
      refine ⟨h1 ⟨v,hv⟩,?_⟩
      have:=h2 ⟨v,hv⟩
      by_cases hb:v∈ B i
      · exact ⟨fun h'=>(this.mpr h').2,fun h'=>this.mp ⟨hb,h'⟩⟩
      · rw [a9o k par B i ι _ hb]
        exact ⟨fun h'=>absurd (a1c k _ ι h') hb,fun h'=>absurd h' (by omega)⟩
  rw [c1,c2,c3,c4]
  simp only [n1,and_assoc]
lemma b66 (hE:∀ e∈ E,e.1< e.2) :
    b03 (a1 (un ι) (i3 k W Wt E P H rows (B i) (u7 par B i))) =
      if f6 (a9 k (B i)) ι.bits= []∧ c8 k B i ι⊆ b9 E B {i} ∧
        n1 E P H par B {i} (c8 k B i ι)∧ g3 par B {i} i (c8 k B i ι)= g6 k B i ι
      then g4 (un Wt) (List.replicate (W* (w9 par B i (c8 k B i ι)* (rows.length+ 1) +
        r9 rows par B i (c8 k B i ι))) false++[true])
      else f3 (un Wt):=by
  rw [b6k,b5n,b3f]
  have key:=b67 k E P H par B i ι hE
  by_cases h:f6 (a9 k (B i)) ι.bits= []∧ (∀ e∈ pairs k,tag k e∈ Xs k (B i) ι→ e∈ E) ∧
      (∀ e∈ pairs k,tag k e∈ B i→ e∈ E→ e∈ P→ tag k e∈ Xs k (B i) ι) ∧
      (∀ e∈ pairs k,tag k e∈ Xs k (B i) ι→ e∉ H) ∧
      (∀ v< k,w2 k (B i) (u7 par B i) ι v≤ 1 ∧
        (v∈ Xs k (B i) ι↔ w2 k (B i) (u7 par B i) ι v= 1))
  · rw [if_pos h,if_pos (key.mp h)]
  · rw [if_neg h,if_neg (fun h'=>h (key.mpr h'))]
lemma b4e (p:ℕ) (hE:∀ e∈ E,e.1< e.2) :
    a9f (un p) (i3 k W Wt E P H rows (B i) (u7 par B i)) =
      (List.range p).flatMap (fun ι =>
        if f6 (a9 k (B i)) ι.bits= []∧ c8 k B i ι⊆ b9 E B {i} ∧
          n1 E P H par B {i} (c8 k B i ι)∧ g3 par B {i} i (c8 k B i ι)= g6 k B i ι
        then g4 (un Wt) (List.replicate (W* (w9 par B i (c8 k B i ι)* (rows.length+ 1) +
          r9 rows par B i (c8 k B i ι))) false++[true])
        else f3 (un Wt)):=by
  rw [a9f,b4]
  exact List.flatMap_congr (fun ι _=>b66 k W Wt E P H rows par B i ι hE)
end Bridge
end LT
end asmP19
section asmP20
namespace LT
open Lib.Machines Lib.Universal
def dU (x y:List Bool):List Bool:=g8 x y++g8 y x
def ic4 (z:List Bool):List Bool :=
  sel (g8 (a0 (a0 z).2).1 (a0 z).1) []
    (sel (dU (a0 (a0 (a0 z).2).2).1 (a0 (a0 z).2).1) [true]
      (sel (dU (a0 (a0 (a0 z).2).2).1 (a0 z).1) [true] [false]))
def ic3 (z:List Bool):List Bool :=
  (List.range (a0 (a0 z).2).2.length).flatMap (fun b=>ic4 (a1 (un b) z))
def ic2 (z:List Bool):List Bool :=
  (List.range (a0 z).2.length).flatMap (fun a=>ic3 (a1 (un a) z))
def b2l (uk:List Bool):List Bool:=(List.range uk.length).flatMap (fun v=>ic2 (a1 (un v) uk))
lemma b44 {x y:List Bool→ List Bool} (hx:a4 x) (hy:a4 y) :
    a4 (fun s=>dU (x s) (y s)) :=
  b7 (b8 (e8 hx hy) (e8 hy hx)) (fun _=>rfl)
lemma b5o:a4 b2l:=by
  have h1:a4 (fun z=>(a0 z).1):=a6
  have h2:a4 (fun z=>(a0 z).2):=a3
  have ha:=cc h2 a6
  have hv:=cc (cc h2 a3) a6
  have h4:a4 ic4:=b7 (d6 (e8 ha h1) (b0 [])
    (d6 (b44 hv ha) (b0 [true]) (d6 (b44 hv h1) (b0 [true])
      (b0 [false])))) (fun _=>rfl)
  have h3:a4 ic3:=b7 (d9 h4 (cc h2 a3) g5) (fun _=>rfl)
  have h2':a4 ic2:=b7 (d9 h3 h2 g5) (fun _=>rfl)
  exact b7 (d9 h2' g5 g5) (fun _=>rfl)
lemma a6t (a b:ℕ):dU (un a) (un b)= []↔ a= b:=by
  rw [dU,i6,i6,b4,b4]
  simp only [un,List.drop_replicate,List.append_eq_nil_iff,List.replicate_eq_nil_iff]
  omega
lemma b7r (k:ℕ):b2l (un k)= a7g k:=by
  rw [b2l,a7g,b4]
  apply List.flatMap_congr; intro v _
  rw [List.map_eq_flatMap,Dec.a94 k (fun a b=>[decide (v= a∨ v= b)])]
  simp only [ic2,a5,b4]
  apply List.flatMap_congr; intro a _
  simp only [ic3,a5,b4]
  apply List.flatMap_congr; intro b _
  simp only [ic4,a5,i6,b4]
  by_cases hab:a< b
  · rw [ite_eq_left hab]
    have hne:(un b).drop a≠ []:=by simp [un]; omega
    unfold sel
    rw [ite_eq_right hne]
    by_cases h1:v= a
    · rw [ite_eq_left ((a6t v a).mpr h1)]; simp [h1]
    · rw [ite_eq_right (fun h => h1 ((a6t v a).mp h))]
      by_cases h2:v= b
      · rw [ite_eq_left ((a6t v b).mpr h2)]; simp [h2]
      · rw [ite_eq_right (fun h=>h2 ((a6t v b).mp h))]; simp [h1,h2]
  · rw [ite_eq_right hab]
    have he:(un b).drop a= []:=by simp [un]; omega
    unfold sel; rw [ite_eq_left he]
def eqF (a b:List Bool):List Bool:=u6 (zw xor a b)
lemma a1r {a b:List Bool→ List Bool} (ha:a4 a) (hb:a4 b) :
    a4 (fun s=>eqF (a s) (b s)) :=
  b7 (cc (y4 xor ha hb) u8) (fun _=>rfl)
lemma b1f:∀ (a b:List Bool),a.length= b.length→ (eqF a b= []↔ a= b):=by
  intro a b h
  rw [eqF,b27 _ _ _ h.le]
  induction a generalizing b with
  | nil=>cases b <;> simp_all [u6]
  | cons x a ih =>
    cases b with
    | nil=>simp at h
    | cons y b =>
      have ih':=ih b (by simpa using h)
      simp only [List.zipWith_cons_cons,u6,List.filter_cons] at ih' ⊢
      cases x <;> cases y <;> simp [ih']
def aPG (w:List Bool):List Bool:=(a0 (a0 w).2).1
def aCG (w:List Bool):List Bool:=(a0 (a0 (a0 w).2).2).1
def a7w (w:List Bool) (iU:List Bool):List Bool :=
  Dec.b5 (Dec.j4 10 (aPG w)++(Dec.j4 1 (aPG w)++Dec.j4 3 (aPG w))) iU
    (Dec.a31 11 (aPG w))
def a4u (w:List Bool) (iU:List Bool):List Bool:=g8 (Dec.j4 10 (aPG w)) (a7w w iU)
def aPj (v:List Bool):List Bool :=
  sel (eqF (a37 (Dec.j4 9 (aPG (a0 v).2)) (a0 v).1)
      (m4 (Dec.j4 10 (aPG (a0 v).2)) (a7w (a0 v).2 (a0 (a0 v).2).1)))
    (a4u (a0 v).2 (a0 v).1) []
def aBP (w:List Bool):List Bool :=
  sel (a0 w).1 (f3 (a4u w (a0 w).1))
    ((List.range (Dec.j4 9 (aPG w)).length).flatMap (fun j=>aPj (a1 (un j) w)))
def a9b (w:List Bool):List Bool :=
  a1 (Dec.j4 1 (aPG w)) (a1 (Dec.j4 3 (aPG w)) (a1 (fld 1 (aCG w))
  (a1 (fld 0 (aCG w)) (a1 (fld 3 (aCG w)) (a1 (Dec.j4 4 (aPG w))
  (a1 (Dec.j4 5 (aPG w)) (a1 (Dec.j4 6 (aPG w)) (a1 (Dec.j4 8 (aPG w))
  (a1 (b2l (Dec.j4 1 (aPG w))) (a1 (a4u w (a0 w).1) (aBP w)))))))))))
def a2o (w:List Bool):List Bool:=a9f (Dec.j4 0 (aPG w)) (a9b w)
lemma b1t:a4 aPG:=b7 (cc (cc a3 a6) g5) (fun _=>rfl)
lemma a7l:a4 aCG :=
  b7 (cc (cc a3 a3) a6) (fun _=>rfl)
lemma s6 (n:ℕ):a4 (fun w=>Dec.j4 n (aPG w)):=cc b1t (Dec.a8e n)
lemma b0a {wf iU:List Bool→ List Bool} (hw:a4 wf) (hi:a4 iU) :
    a4 (fun s=>a7w (wf s) (iU s)) :=
  b7 (Dec.k5 (b8 (cc hw (s6 10)) (b8 (cc hw (s6 1)) (cc hw (s6 3))))
    hi (cc hw (cc b1t (Dec.a6m 11)))) (fun _=>rfl)
lemma a63 {wf iU:List Bool→ List Bool} (hw:a4 wf) (hi:a4 iU) :
    a4 (fun s=>a4u (wf s) (iU s)) :=
  b7 (e8 (cc hw (s6 10)) (b0a hw hi)) (fun _=>rfl)
lemma b7k:a4 aPj:=by
  have h2:a4 (fun v=>(a0 v).2):=a3
  exact b7 (d6 (a1r (a7b (cc h2 (s6 9)) a6)
    (k4 (cc h2 (s6 10)) (b0a h2 (cc h2 a6))))
    (a63 h2 a6) (b0 [])) (fun _=>rfl)
lemma b8d:a4 aBP :=
  b7 (d6 a6 (cc (a63 g5 a6) n6)
    (d9 b7k (s6 9) g5)) (fun _=>rfl)
lemma b3s:a4 a9b :=
  b7 (a7 (s6 1) (a7 (s6 3) (a7 (cc a7l (a1v 1))
  (a7 (cc a7l (a1v 0)) (a7 (cc a7l (a1v 3)) (a7 (s6 4)
  (a7 (s6 5) (a7 (s6 6) (a7 (s6 8)
  (a7 (cc (s6 1) b5o) (a7 (a63 g5 a6) b8d)))))))))))
  (fun _=>rfl)
lemma b4q:a4 a2o:=b7 (b3q (s6 0) b3s) (fun _=>rfl)
end LT
end asmP20
section asmP21
namespace LT
open Lib.Machines Lib.Universal
section Adapt
variable (p k w:ℕ) (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  (t:ℕ) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
lemma a34 (u:List Bool):aPG (a1 u (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B)))= Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B):=by
  simp only [aPG,Dec.gZ,a5]
lemma b8w (u:List Bool):aCG (a1 u (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B)))= Dec.a24 (un p++false::Dec.a8 k w E P H rows t par B):=by
  simp only [aCG,Dec.gZ,a5]
lemma a03 :
    Dec.j4 0 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= un p∧ Dec.j4 1 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= un k ∧
    Dec.j4 3 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= un (Dec.b6 k) ∧
    Dec.j4 4 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= Dec.mask E∧ Dec.j4 5 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= Dec.mask P ∧
    Dec.j4 6 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= Dec.mask H ∧
    Dec.j4 8 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= rows.flatMap Dec.j8 ∧
    Dec.j4 9 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= un (t+1)∧ Dec.j4 10 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= un (Dec.i8 t) ∧
    Dec.a31 11 (Dec.p5 (un p++false::Dec.a8 k w E P H rows t par B))= (List.finRange (t+1)).flatMap (Dec.j5 k t par B):=by
  rw [Dec.a45]
  simp only [Dec.j4,Dec.a31,a5,and_self]
lemma b1h (u:List Bool) (j:Fin (t+1)) :
    a7w (a1 u (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B))) (un j.val)= Dec.j5 k t par B j:=by
  obtain ⟨-,h1,h3,-,-,-,-,-,h10,h11⟩:=a03 p k w E P H rows t par B
  rw [a7w,a34,h1,h3,h10,h11,Dec.l8 (Dec.j5 k t par B) _
    (Dec.a0n k t par B) (List.finRange (t+1)) j.val (by rw [List.length_finRange]; exact j.isLt)
    _ _ (by simp) (by simp)]
  simp
lemma a55 (u:List Bool) (j:Fin (t+1)) :
    a4u (a1 u (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B))) (un j.val)= Dec.a9 k (B j):=by
  obtain ⟨-,-,-,-,-,-,-,-,h10,-⟩:=a03 p k w E P H rows t par B
  rw [a4u,a34,h10,b1h,Dec.j5,i6,b4,
    List.drop_left' (Dec.k2 _ _)]
lemma b5y (a b:ℕ) (ha:a< t+1) (hb:b< t+1) :
    Dec.bits (Dec.i8 t) a= Dec.bits (Dec.i8 t) b↔ a= b:=by
  constructor
  · intro h
    have:=congrArg Dec.a1a h
    rwa [Dec.a09 _ _ (Dec.u5 t a ha),
      Dec.a09 _ _ (Dec.u5 t b hb)] at this
  · rintro rfl; rfl
lemma a7k {β:Type} (n c:ℕ) (hc:c< n) (f:ℕ→ List β) :
    (List.range n).flatMap (fun j=>if j= c then f j else [])= f c:=by
  induction n with
  | zero=>omega
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | h
    · rw [ih h,ite_eq_right (by omega),List.append_nil]
    · subst h
      rw [ite_eq_left rfl]
      have:(List.range c).flatMap (fun j=>if j= c then f j else [])= []:=by
        rw [List.flatMap_eq_nil_iff]; intro j hj; rw [List.mem_range] at hj
        exact ite_eq_right (by omega)
      rw [this,List.nil_append]
lemma c00 (i:Fin (t+1)) :
    aBP (a1 (un i.val) (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B)))= Dec.a9 k (u7 par B i):=by
  obtain ⟨-,-,-,-,-,-,-,h9,h10,-⟩:=a03 p k w E P H rows t par B
  rw [aBP,a5]
  by_cases hi:i= 0
  · subst hi
    have hb:=a55 p k w E P H rows t par B (un 0) 0
    simp only [Fin.val_zero,a5] at hb ⊢
    unfold sel
    rw [ite_eq_left (show un 0= [] from rfl),hb,u7,ite_eq_left (show (0:Fin (t+1))= 0 from rfl)]
    simp [f3,Dec.a9]
  · have hne:un i.val≠ []:=by
      have:i.val≠ 0:=fun h=>hi (Fin.ext h)
      simp [un]; omega
    unfold sel
    rw [ite_eq_right hne,u7,ite_eq_right hi,a34,h9,b4]
    let bagN:ℕ→ List Bool:=fun j=>if h:j< t+1 then Dec.a9 k (B ⟨j,h⟩) else []
    have key:∀ j∈ List.range (t+1),aPj (a1 (un j) (a1 (un i.val) (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B)))) =
        if j= (par i).val then bagN j else []:=by
      intro j hj
      rw [List.mem_range] at hj
      have hrec:=b1h p k w E P H rows t par B (un i.val) i
      have hbag:=a55 p k w E P H rows t par B (un i.val) ⟨j,hj⟩
      have hfw:a37 (un (t+1)) (un j)= Dec.bits (Dec.i8 t) j:=by
        rw [a8l _ _ (Nat.succ_pos t)]; rfl
      have htk:m4 (un (Dec.i8 t)) (Dec.j5 k t par B i) =
          Dec.bits (Dec.i8 t) (par i).val:=by
        rw [k7,Dec.j5,b4,List.take_left' (Dec.k2 _ _)]
      simp only [aPj,a5]
      rw [a34,h9,h10,hrec,hfw,htk,hbag]
      unfold sel
      by_cases hj':j= (par i).val
      · rw [ite_eq_left ((b1f _ _ (by simp [Dec.k2])).mpr (by rw [hj'])),
          ite_eq_left hj']
        simp only [bagN,dif_pos hj]
      · rw [ite_eq_right (fun h=>hj' ((b5y t j _ hj (par i).isLt).mp
          ((b1f _ _ (by simp [Dec.k2])).mp h))),ite_eq_right hj']
    rw [List.flatMap_congr key,a7k (t+1) (par i).val (par i).isLt bagN]
    simp only [bagN,dif_pos (par i).isLt,Fin.eta]
lemma b3n (hP:∀ e∈ P,e.1< e.2) (i:Fin (t+1)) :
    a9b (a1 (un i.val) (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B))) =
      i3 k (Dec.b6 k+ 1) ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1) *
        (4* t+ 5)) E P H rows (B i) (u7 par B i):=by
  obtain ⟨-,h1,h3,h4,h5,h6,h8,-,-,-⟩:=a03 p k w E P H rows t par B
  obtain ⟨hW,hR1,-,-,hWt,-⟩:=Dec.a0d p k w E P H rows t par B hP _ rfl
  have hc:aCG (a1 (un i.val) (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B)))= Dec.a24 (un p++false::Dec.a8 k w E P H rows t par B):=b8w p k w E P H rows t par B _
  rw [a9b,a34,h1,h3,h4,h5,h6,h8,hc,b7r,c00,a5,a55]
  simp only [fld,Dec.a24,a5,hW,hR1,hWt,i3]
lemma a8j (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) (i:Fin (t+1)) :
    a2o (a1 (un i.val) (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B))) =
      (List.range p).flatMap (fun ι =>
        if f6 (Dec.a9 k (B i)) ι.bits= []∧ c8 k B i ι⊆ b9 E B {i} ∧
          n1 E P H par B {i} (c8 k B i ι)∧ g3 par B {i} i (c8 k B i ι)= g6 k B i ι
        then g4 (un ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5)))
          (List.replicate ((Dec.b6 k+ 1)* (w9 par B i (c8 k B i ι)* (rows.length+ 1) +
            r9 rows par B i (c8 k B i ι))) false++[true])
        else f3 (un ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5)))):=by
  obtain ⟨h0,-⟩:=a03 p k w E P H rows t par B
  rw [a2o,a34,h0,b3n p k w E P H rows t par B hP i]
  exact b4e _ _ _ E P H rows par B i p hE
end Adapt
end LT
end asmP21
section asmP22
namespace LT
open Lib.Machines Lib.Universal
def e9 (k:ℕ) (Bi:Finset ℕ):List ℕ:=j9 (Dec.layout k) (Dec.a9 k Bi)
lemma b16 (a:ℕ) (M:List ℕ) (l:List Bool) :
    j9 (a::M) l= match l with
      | []=>[]
      | c::l'=>if c then a::j9 M l' else j9 M l':=by
  cases l with
  | nil=>simp [j9]
  | cons c l'=>exact m5 a M c l'
lemma a6y (M:List ℕ):j9 M []= []:=by simp [j9]
lemma a4e:∀ (L:List ℕ) (b l:List Bool),L.length= b.length →
    j9 L (i5 b l)= j9 (j9 L b) l
  | [],[],l,_=>by simp [j9,i5]
  | [],_::_,_,h=>by simp at h
  | _::_,[],_,h=>by simp at h
  | a :: L, false :: b, l, h => by
    rw [i5,m5,m5]
    simpa using a4e L b l (by simpa using h)
  | a :: L, true :: b, l, h => by
    rw [i5,m5,m5,ite_eq_left rfl]
    have ih:=a4e L b l.tail (by simpa using h)
    cases l with
    | nil =>
      rw [show ([]:List Bool).tail= [] from rfl,a6y] at ih
      simp [ih,a6y]
    | cons c l' =>
      rw [List.headD_cons,List.tail_cons] at *
      rw [b16]
      cases c <;> simp [ih]
lemma b01:∀ (M:List ℕ) (l:List Bool) (v:ℕ),
    v∈ j9 M l↔ ∃ x< M.length,l.getD x false= true∧ M.getD x 0= v
  | [],l,v=>by simp [j9]
  | a::M,[],v=>by simp [j9]
  | a :: M, c :: l, v => by
    rw [m5,apply_ite (fun s=>v∈ s)]
    have ih:=b01 M l v
    constructor
    · intro h
      split_ifs at h with hc
      · rcases List.mem_cons.mp h with h | h
        · exact ⟨0,by simp,by simp [hc],by simp [h]⟩
        · obtain ⟨x, hx, h1, h2⟩ := ih.mp h
          exact ⟨x+1,by simp; omega,by simpa using h1,by simpa using h2⟩
      · obtain ⟨x, hx, h1, h2⟩ := ih.mp h
        exact ⟨x+1,by simp; omega,by simpa using h1,by simpa using h2⟩
    · rintro ⟨x, hx, h1, h2⟩
      cases x with
      | zero =>
        simp at h1 h2
        rw [if_pos h1]; exact List.mem_cons.mpr (Or.inl h2.symm)
      | succ x =>
        have h':=ih.mpr ⟨x,by simpa using hx,by simpa using h1,by simpa using h2⟩
        split_ifs
        · exact List.mem_cons_of_mem _ h'
        · exact h'
lemma b4v (k:ℕ) (Bi:Finset ℕ) (ι v:ℕ) :
    v∈ Xs k Bi ι↔ ∃ x< (e9 k Bi).length,ι.testBit x= true∧ (e9 k Bi).getD x 0= v:=by
  rw [Xs,List.mem_toFinset,a4e _ _ _ (by rw [Dec.a9,List.length_map]),← e9,
    b01]
  simp only [← a4w]
lemma a7y (k:ℕ) (Bi:Finset ℕ) (ι:ℕ) (S:Finset ℕ)
    (hS:∀ x,ι.testBit x= decide (x∈ S)) (hSm:∀ x∈ S,x< (e9 k Bi).length) :
    Xs k Bi ι= S.image (fun x=>(e9 k Bi).getD x 0):=by
  ext v
  rw [b4v,Finset.mem_image]
  constructor
  · rintro ⟨x, -, h1, h2⟩
    rw [hS] at h1
    exact ⟨x,by simpa using h1,h2⟩
  · rintro ⟨x, h1, h2⟩
    exact ⟨x,hSm x h1,by rw [hS]; simpa using h1,h2⟩
lemma b3y {t:ℕ} (k:ℕ) (B:Fin (t+1)→ Finset ℕ) (i:Fin (t+1)) (ι:ℕ) (S:Finset ℕ)
    (hS:∀ x,ι.testBit x= decide (x∈ S)) (hSm:∀ x∈ S,x< (e9 k (B i)).length) :
    c8 k B i ι= Finset.univ.filter (fun e=>∃ x∈ S,(e9 k (B i)).getD x 0= c6 k e):=by
  ext e
  simp [c8,a7y k (B i) ι S hS hSm]
lemma b4h {t:ℕ} (k:ℕ) (B:Fin (t+1)→ Finset ℕ) (i:Fin (t+1)) (ι:ℕ) (S:Finset ℕ)
    (hS:∀ x,ι.testBit x= decide (x∈ S)) (hSm:∀ x∈ S,x< (e9 k (B i)).length) :
    g6 k B i ι= Finset.univ.filter (fun v:Fin k=>∃ x∈ S,(e9 k (B i)).getD x 0= v.val):=by
  ext v
  simp [g6,a7y k (B i) ι S hS hSm]
lemma a3c:∀ (L:List ℕ) (b:List Bool),L.length= b.length →
    j9 L b= ((List.range b.length).filter (fun q=>b.getD q false)).map (fun q=>L.getD q 0)
  | [],[],_=>by simp [j9]
  | [],_::_,h=>by simp at h
  | _::_,[],h=>by simp at h
  | a :: L, c :: b, h => by
    rw [m5,a3c L b (by simpa using h),List.length_cons,List.range_succ_eq_map,
      List.filter_cons,List.filter_map]
    cases c <;> simp [Function.comp_def,List.map_map]
lemma b1d (k:ℕ) (Bi:Finset ℕ) :
    e9 k Bi= (Dec.z5 (Dec.a9 k Bi)).map (fun q=>(Dec.layout k).getD q 0):=by
  rw [e9,a3c _ _ (by rw [Dec.a9,List.length_map]),Dec.z5]
lemma z0 (k:ℕ) (Bi:Finset ℕ) :
    (e9 k Bi).length= (Dec.z5 (Dec.a9 k Bi)).length:=by
  rw [b1d,List.length_map]
lemma a3g:∀ (L:List ℕ) (b:List Bool),L.Nodup→ (j9 L b).Nodup
  | [],b,_=>by simp [j9]
  | a::L,[],_=>by simp [j9]
  | a :: L, c :: b, h => by
    rw [List.nodup_cons] at h
    rw [m5]
    split_ifs
    · exact List.nodup_cons.mpr ⟨fun hm=>h.1 (a06 L b a hm),a3g L b h.2⟩
    · exact a3g L b h.2
lemma a40 (k:ℕ) (Bi:Finset ℕ):(e9 k Bi).Nodup :=
  a3g _ _ (a29 k)
lemma a8b:∀ (b l:List Bool),f6 b l= l.drop (b.count true)
  | [],l=>by simp [f6]
  | false::b,l=>by simp [f6,a8b b l]
  | true :: b, l => by
    rw [f6,a8b b l.tail,List.count_cons_self,List.drop_tail,Nat.add_comm]
lemma a1l:∀ (L:List ℕ) (b:List Bool),L.length= b.length →
    (j9 L b).length= b.count true
  | [],[],_=>by simp [j9]
  | [],_::_,h=>by simp at h
  | _::_,[],h=>by simp at h
  | a :: L, c :: b, h => by
    rw [m5]
    have ih:=a1l L b (by simpa using h)
    cases c <;> simp [ih]
lemma z7 (k:ℕ) (Bi:Finset ℕ) (ι:ℕ) :
    f6 (Dec.a9 k Bi) ι.bits= []↔ ι< 2 ^ (e9 k Bi).length:=by
  rw [a8b,List.drop_eq_nil_iff,e9,a1l _ _ (by rw [Dec.a9,List.length_map]),
    Nat.size_eq_bits_len ι,Nat.size_le]
lemma b5q (k:ℕ) (Bi:Finset ℕ) (x:ℕ) (hx:x< (e9 k Bi).length) :
    (e9 k Bi).getD x 0∈ Bi∧ (e9 k Bi).getD x 0∈ Dec.layout k:=by
  have hm:(e9 k Bi).getD x 0∈ e9 k Bi:=by
    rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem hx
  refine ⟨?_,a06 _ _ _ hm⟩
  have h:=y5 Bi (Dec.layout k) (List.replicate (Dec.layout k).length true)
  have e:i5 ((Dec.layout k).map (fun v=>decide (v∈ Bi)))
      (List.replicate (Dec.layout k).length true)= (Dec.layout k).map (fun v=>decide (v∈ Bi)):=by
    have:∀ (b:List Bool) (n:ℕ),b.length≤ n→ i5 b (List.replicate n true)= b:=by
      intro b
      induction b with
      | nil=>intro n _; rfl
      | cons c b ih =>
        intro n hn
        cases c
        · simp [i5,ih n (by simp at hn; omega)]
        · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
          simp [i5,List.replicate_succ,ih n' (by simp at hn; omega)]
    exact this _ _ (by simp)
  rw [e] at h
  exact h _ hm
def a1t (k:ℕ) (Bi:Finset ℕ) (T:Finset ℕ):Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun e=>∃ x∈ T,(e9 k Bi).getD x 0= c6 k e)
def l7 (k:ℕ) (Bi:Finset ℕ) (Y:Finset ℕ):Finset (Fin k) :=
  Finset.univ.filter (fun v:Fin k=>∃ x∈ Y,(e9 k Bi).getD x 0= v.val)
lemma a0o {t:ℕ} (k:ℕ) (B:Fin (t+1)→ Finset ℕ) (i:Fin (t+1)) (ι:ℕ)
    (T Y:Finset ℕ) (hS:∀ x,ι.testBit x= decide (x∈ T∪ Y))
    (hSm:∀ x∈ T∪ Y,x< (e9 k (B i)).length)
    (hT:∀ x∈ T,¬ (e9 k (B i)).getD x 0< k) (hY:∀ x∈ Y,(e9 k (B i)).getD x 0< k) :
    c8 k B i ι= a1t k (B i) T∧ g6 k B i ι= l7 k (B i) Y:=by
  rw [b3y k B i ι _ hS hSm,b4h k B i ι _ hS hSm]
  constructor
  · ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,a1t,Finset.mem_union]
    constructor
    · rintro ⟨x, hx | hx, h⟩
      · exact ⟨x,hx,h⟩
      · have:=hY x hx; rw [h] at this; have:=Dec.a13 k e; simp only [c6] at *; omega
    · rintro ⟨x,hx,h⟩; exact ⟨x,Or.inl hx,h⟩
  · ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,l7,Finset.mem_union]
    constructor
    · rintro ⟨x, hx | hx, h⟩
      · exact absurd (h ▸ v.isLt) (hT x hx)
      · exact ⟨x,hx,h⟩
    · rintro ⟨x,hx,h⟩; exact ⟨x,Or.inr hx,h⟩
lemma b18 {t:ℕ} (k:ℕ) (B:Fin (t+1)→ Finset ℕ) (i j:Fin (t+1)) (T:Finset ℕ) :
    sig B j (a1t k (B i) T)= a1t k (B i) (T.filter (fun x=>(e9 k (B i)).getD x 0∈ B j)):=by
  ext e
  simp only [sig,a1t,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨x,hx,h⟩,hb⟩; exact ⟨x,⟨hx,h ▸ hb⟩,h⟩
  · rintro ⟨x,⟨hx,hb⟩,h⟩; exact ⟨⟨x,hx,h⟩,h ▸ hb⟩
lemma a3i (k:ℕ) (Bi:Finset ℕ) (x y:ℕ) (hx:x< (e9 k Bi).length)
    (hy:y< (e9 k Bi).length) (h:(e9 k Bi).getD x 0= (e9 k Bi).getD y 0):x= y:=by
  rw [List.getD_eq_getElem _ _ hx,List.getD_eq_getElem _ _ hy] at h
  exact (List.Nodup.getElem_inj_iff (a40 k Bi)).mp h
lemma a92 (k:ℕ) (Bi:Finset ℕ) (Y0 Y:Finset ℕ) (hY:Y⊆ Y0)
    (hY0:∀ x∈ Y0,x< (e9 k Bi).length) :
    l7 k Bi (Y0 \ Y)= l7 k Bi Y0 \ l7 k Bi Y:=by
  ext v
  simp only [l7,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨x, ⟨hx0, hxY⟩, h⟩
    refine ⟨⟨x,hx0,h⟩,?_⟩
    rintro ⟨y,hy,h'⟩
    have:=a3i k Bi x y (hY0 x hx0) (hY0 y (hY hy)) (h.trans h'.symm)
    exact hxY (this ▸ hy)
  · rintro ⟨⟨x, hx0, h⟩, hn⟩
    exact ⟨x,⟨hx0,fun hxY=>hn ⟨x,hxY,h⟩⟩,h⟩
lemma b1b {M:Type*} [AddCommMonoid M] (k:ℕ) (Bi:Finset ℕ) (Y0:Finset ℕ)
    (hY0:∀ x∈ Y0,x< (e9 k Bi).length) (hY0n:∀ x∈ Y0,(e9 k Bi).getD x 0< k)
    (f:Finset (Fin k)→ M) :
    ∑ Y∈ Y0.powerset,f (l7 k Bi Y)= ∑ τ1∈ (l7 k Bi Y0).powerset,f τ1:=by
  refine Finset.sum_bij (fun Y _=>l7 k Bi Y) ?_ ?_ ?_ (fun _ _=>rfl)
  · intro Y hY
    rw [Finset.mem_powerset] at hY ⊢
    intro v hv
    simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    obtain ⟨x,hx,h⟩:=hv
    exact ⟨x,hY hx,h⟩
  · intro Y1 h1 Y2 h2 he
    rw [Finset.mem_powerset] at h1 h2
    ext x
    constructor
    · intro hx
      have hv:(⟨(e9 k Bi).getD x 0,hY0n x (h1 hx)⟩:Fin k)∈ l7 k Bi Y2:=by
        rw [← he]; simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨x,hx,rfl⟩
      simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and] at hv
      obtain ⟨y,hy,h⟩:=hv
      have:=a3i k Bi y x (hY0 y (h2 hy)) (hY0 x (h1 hx)) h
      exact this ▸ hy
    · intro hx
      have hv:(⟨(e9 k Bi).getD x 0,hY0n x (h2 hx)⟩:Fin k)∈ l7 k Bi Y1:=by
        rw [he]; simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨x,hx,rfl⟩
      simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and] at hv
      obtain ⟨y,hy,h⟩:=hv
      have:=a3i k Bi y x (hY0 y (h1 hy)) (hY0 x (h2 hx)) h
      exact this ▸ hy
  · intro τ1 hτ
    rw [Finset.mem_powerset] at hτ
    refine ⟨Y0.filter (fun x=>∃ v∈ τ1,(e9 k Bi).getD x 0= v.val),?_,?_⟩
    · rw [Finset.mem_powerset]; exact Finset.filter_subset _ _
    · ext v
      simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨x, ⟨_, u, hu, h1⟩, h2⟩
        have:u= v:=Fin.ext (h1.symm.trans h2)
        exact this ▸ hu
      · intro hv
        have:=hτ hv
        simp only [l7,Finset.mem_filter,Finset.mem_univ,true_and] at this
        obtain ⟨x,hx,h⟩:=this
        exact ⟨x,⟨hx,v,hv,h⟩,h⟩
end LT
end asmP22
section asmP23
namespace LT
open Lib.Machines Lib.Universal
lemma b59 (n:ℕ):val (List.replicate n false++[true])= 2 ^ n:=by
  rw [a73,a74,List.length_replicate]; simp [val]
lemma b64 (p k w:ℕ) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:ℕ) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset ℕ) (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2)
    (i:Fin (t+1)) (μ:ℕ) (hμ:μ< p) :
    val (Dec.b5 (un ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5)))
      (un μ) (a2o (a1 (un i.val) (Dec.gZ (un p++false::Dec.a8 k w E P H rows t par B))))) =
    if f6 (Dec.a9 k (B i)) μ.bits= [] then
      y0 E P H rows par B (2 ^ (Dec.b6 k+ 1)) i (c8 k B i μ) (g6 k B i μ) %
        2 ^ ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5))
    else 0:=by
  rw [a8j p k w E P H rows t par B hE hP i,Dec.l8 _
    ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5))
    (fun ι=>by split_ifs <;> simp [i4,f3]) (List.range p) μ (by simpa using hμ) _ _
    (by simp) (by simp),List.getElem_range]
  by_cases hv:f6 (Dec.a9 k (B i)) μ.bits= []
  · rw [ite_eq_left hv]
    unfold y0
    by_cases hc:c8 k B i μ⊆ b9 E B {i}∧ n1 E P H par B {i} (c8 k B i μ) ∧
        g3 par B {i} i (c8 k B i μ)= g6 k B i μ
    · rw [ite_eq_left ⟨hv,hc⟩,ite_eq_left hc,w8,b59,b4,kap,← pow_mul]
    · rw [ite_eq_right (fun h=>hc h.2),ite_eq_right hc,w1,Nat.zero_mod]
  · rw [ite_eq_right (fun h=>hv h.1),ite_eq_right hv,w1]
lemma a4h (S:Finset ℕ):∀ (L:List ℕ) (v:ℕ),
    v∈ j9 L (L.map (fun u=>decide (u∈ S)))↔ v∈ L∧ v∈ S
  | [],v=>by simp [j9]
  | a :: L, v => by
    rw [List.map_cons,m5]
    have ih:=a4h S L v
    by_cases ha:a∈ S
    · rw [decide_eq_true ha, ite_eq_left rfl, List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact ⟨Or.inl h,h ▸ ha⟩
        · exact ⟨Or.inr h.1,h.2⟩
      · rintro ⟨h | h, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h,h2⟩
    · rw [decide_eq_false ha, ite_eq_right (by simp), ih, List.mem_cons]
      constructor
      · rintro ⟨h1,h2⟩; exact ⟨Or.inr h1,h2⟩
      · rintro ⟨h | h, h2⟩
        · exact absurd (h ▸ h2) ha
        · exact ⟨h,h2⟩
lemma b0q (k:ℕ) (Bi:Finset ℕ) (v:ℕ):v∈ e9 k Bi↔ v∈ Dec.layout k∧ v∈ Bi :=
  a4h Bi (Dec.layout k) v
lemma c05 (S:Finset ℕ) (n:ℕ) (h:∀ x∈ S,x< n):f0 S< 2 ^ n :=
  Nat.geomSum_lt (le_refl 2) (fun k hk=>h k hk)
lemma a50 {k:ℕ} (E:Finset (Fin k × Fin k)) (hE:∀ e∈ E,e.1< e.2) (v:ℕ)
    (hv:v∈ Finset.range k∪ E.image (c6 k)):v∈ Dec.layout k:=by
  rw [Dec.a0p]
  rcases Finset.mem_union.mp hv with h | h
  · exact Or.inl (Finset.mem_range.mp h)
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨e,hE e he,rfl⟩
lemma a9l {M:Type*} [AddCommMonoid M] (k w:ℕ) (Bi:Finset ℕ)
    (hL:∀ v∈ Bi,v∈ Dec.layout k) (hc:Bi.card≤ w+ 1) (g:Finset ℕ→ M) :
    ∑ ι ∈ Finset.range (2 ^ (w+1)), (if f6 (Dec.a9 k Bi) ι.bits = [] then g (Xs k Bi ι) else 0) =
      ∑ X∈ Bi.powerset,g X:=by
  set n:=(e9 k Bi).length with hn
  have hset:∀ v,v∈ e9 k Bi↔ v∈ Bi:=fun v=>by
    rw [b0q]; exact ⟨fun h=>h.2,fun h=>⟨hL v h,h⟩⟩
  have hnc:n≤ w+ 1:=by
    have:=List.toFinset_card_of_nodup (a40 k Bi)
    have e:(e9 k Bi).toFinset= Bi:=by ext v; simp [hset]
    rw [e] at this; omega
  rw [← Finset.sum_filter]
  have hf:(Finset.range (2 ^ (w+1))).filter (fun ι=>f6 (Dec.a9 k Bi) ι.bits= []) =
      Finset.range (2 ^ n):=by
    ext ι
    simp only [Finset.mem_filter,Finset.mem_range,z7,← hn]
    constructor
    · exact fun h=>h.2
    · intro h; exact ⟨lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hnc),h⟩
  rw [hf]
  have hpos:∀ x,x< n→ (e9 k Bi).getD x 0∈ Bi:=fun x hx=>(b5q k Bi x hx).1
  refine Finset.sum_bij (fun ι _=>Xs k Bi ι) ?_ ?_ ?_ (fun _ _=>rfl)
  · intro ι _
    rw [Finset.mem_powerset]; exact a1c k Bi ι
  · intro a ha b hb he
    rw [Finset.mem_range] at ha hb
    apply Nat.eq_of_testBit_eq
    intro x
    by_cases hx:x< n
    · have key:∀ c,c< 2 ^ n→ (c.testBit x= true↔ (e9 k Bi).getD x 0∈ Xs k Bi c):=by
        intro c _
        rw [b4v]
        constructor
        · intro h; exact ⟨x,hx,h,rfl⟩
        · rintro ⟨y, hy, h1, h2⟩
          exact (a3i k Bi y x hy hx h2) ▸ h1
      have:=(key a ha).trans (he ▸ (key b hb).symm)
      cases h1:a.testBit x <;> cases h2:b.testBit x <;> simp_all
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro X hX
    rw [Finset.mem_powerset] at hX
    refine ⟨f0 ((Finset.range n).filter (fun x=>(e9 k Bi).getD x 0∈ X)),
      Finset.mem_range.mpr (c05 _ n (fun x hx=>by simpa using (Finset.mem_filter.mp hx).1)),?_⟩
    rw [a7y k Bi _ _ (k9 _) (fun x hx=>by simpa using (Finset.mem_filter.mp hx).1)]
    ext v
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨x,⟨_,h⟩,rfl⟩; exact h
    · intro hv
      obtain ⟨x,hx,hxv⟩:=List.getElem_of_mem ((hset v).mpr (hX hv))
      exact ⟨x,⟨hx,by rw [List.getD_eq_getElem _ _ hx,hxv]; exact hv⟩,
        by rw [List.getD_eq_getElem _ _ hx,hxv]⟩
lemma a8n {t:ℕ} (k w:ℕ) (E:Finset (Fin k × Fin k)) (B:Fin (t+1)→ Finset ℕ)
    (i:Fin (t+1)) (hE:∀ e∈ E,e.1< e.2) (hB:B i⊆ Finset.range k∪ E.image (c6 k))
    (hc:(B i).card≤ w+ 1) {M:Type*} [AddCommMonoid M]
    (f:Finset (Fin k × Fin k)→ Finset (Fin k)→ M) :
    ∑ ι ∈ Finset.range (2 ^ (w+1)),
        (if f6 (Dec.a9 k (B i)) ι.bits= [] then f (c8 k B i ι) (g6 k B i ι) else 0) =
      ∑ σ ∈ (sig B i E).powerset,
        ∑ τ∈ (Finset.univ.filter (fun v:Fin k=>v.val∈ B i)).powerset,f σ τ:=by
  have h1:=a9l k w (B i) (fun v hv=>a50 E hE v (hB hv)) hc
    (fun X=>f (Finset.univ.filter (fun e=>c6 k e∈ X)) (Finset.univ.filter (fun v:Fin k=>v.val∈ X)))
  simp only [c8,g6] at h1 ⊢
  rw [h1,← Finset.sum_product']
  have htag:∀ e:Fin k × Fin k,c6 k e∈ B i→ e∈ E:=by
    intro e he
    rcases Finset.mem_union.mp (hB he) with h | h
    · have:=Dec.a13 k e; simp only [Finset.mem_range] at h; simp only [Dec.tag,c6] at *; omega
    · obtain ⟨e', he', h'⟩ := Finset.mem_image.mp h
      exact (Dec.y6 k h') ▸ he'
  refine Finset.sum_bij (fun X _=>(Finset.univ.filter (fun e=>c6 k e∈ X),
      Finset.univ.filter (fun v:Fin k=>v.val∈ X))) ?_ ?_ ?_ (fun _ _=>rfl)
  · intro X hX
    rw [Finset.mem_powerset] at hX
    simp only [Finset.mem_product,Finset.mem_powerset]
    constructor
    · intro e he
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at he
      exact (l0 B i E e).mpr ⟨htag e (hX he),hX he⟩
    · intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      exact hX hv
  · intro X1 h1 X2 h2 he
    rw [Finset.mem_powerset] at h1 h2
    simp only [Prod.mk.injEq] at he
    ext v
    have key:∀ X:Finset ℕ,X⊆ B i→ (v∈ X↔ (∃ hv:v< k,(⟨v,hv⟩:Fin k) ∈
        Finset.univ.filter (fun u:Fin k=>u.val∈ X)) ∨
        ∃ e∈ Finset.univ.filter (fun e=>c6 k e∈ X),c6 k e= v):=by
      intro X hX
      constructor
      · intro hv
        rcases Finset.mem_union.mp (hB (hX hv)) with h | h
        · exact Or.inl ⟨Finset.mem_range.mp h,by simpa using hv⟩
        · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp h
          exact Or.inr ⟨e,by simpa using hv,rfl⟩
      · rintro (⟨_, h⟩ | ⟨e, h, rfl⟩)
        · simpa using h
        · simpa using h
    rw [key X1 h1,key X2 h2,he.1,he.2]
  · rintro ⟨σ, τ⟩ hp
    simp only [Finset.mem_product,Finset.mem_powerset] at hp
    refine ⟨σ.image (c6 k)∪ τ.image (fun v=>v.val),?_,?_⟩
    · rw [Finset.mem_powerset]
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
        exact ((l0 B i E e).mp (hp.1 he)).2
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
        have:=hp.2 hu
        simpa using this
    · simp only [Prod.mk.injEq]
      constructor
      · ext e
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_image]
        constructor
        · rintro (⟨e', he', h⟩ | ⟨u, _, h⟩)
          · exact (Dec.y6 k h) ▸ he'
          · have:=Dec.a13 k e; have:=u.isLt; simp only [Dec.tag,c6] at *; omega
        · intro he; exact Or.inl ⟨e,he,rfl⟩
      · ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_image]
        constructor
        · rintro (⟨e', _, h⟩ | ⟨u, hu, h⟩)
          · have:=Dec.a13 k e'; have:=v.isLt; simp only [Dec.tag,c6] at *; omega
          · exact (Fin.ext h) ▸ hu
        · intro hv; exact Or.inr ⟨v,hv,rfl⟩
end LT
end asmP23
section asmP24
open Turing PEqualNP.Library Lib.Machines Lib.Universal
def mW (e:List Bool):List Bool:=(a0 e).1
def mP (e:List Bool):List Bool:=(a0 (a0 e).2).1
def mBI (e:List Bool):List Bool:=(a0 (a0 (a0 e).2).2).1
def mBJ (e:List Bool):List Bool:=(a0 (a0 (a0 (a0 e).2).2).2).1
def mT (e:List Bool):List Bool:=(a0 (a0 (a0 (a0 e).2).2).2).2
lemma b0j:a4 mW:=a6
lemma b40:a4 mP:=b7 (a2 a3 a6) (fun _=>rfl)
lemma b6w:a4 mBI :=
  b7 (a2 (a2 a3 a3) a6) (fun _=>rfl)
lemma b7q:a4 mBJ :=
  b7 (a2 (a2 (a2 a3 a3) a3) a6)
    (fun _=>rfl)
lemma b90:a4 mT :=
  b7 (a2 (a2 (a2 a3 a3) a3) a3)
    (fun _=>rfl)
def scX (b iU:List Bool):List Bool:=(a0 (a0 (LT.scF b (s5 iU))).2).2
def scR (b iU:List Bool):List Bool:=(a0 (a0 (LT.scF b (s5 iU))).2).1
lemma b4t (b iU:List Bool):scX b iU= LT.i5 b iU.length.bits:=by
  rw [scX,LT.b04,a5,a5,w7]
lemma b8j (b iU:List Bool):scR b iU= LT.f6 b iU.length.bits:=by
  rw [scR,LT.b04,a5,a5,w7]
lemma b1u {ub ui:List Bool→ List Bool} (hb:a4 ub) (hi:a4 ui) :
    a4 (fun s=>scX (ub s) (ui s)) :=
  b7 (a2 (LT.a85 hb (a2 hi n9))
    (a2 a3 a3)) (fun _=>rfl)
lemma b85 {ub ui:List Bool→ List Bool} (hb:a4 ub) (hi:a4 ui) :
    a4 (fun s=>scR (ub s) (ui s)) :=
  b7 (a2 (LT.a85 hb (a2 hi n9))
    (a2 a3 a6)) (fun _=>rfl)
lemma a2n:∀ (b l:List Bool),(LT.i5 b l).length= b.length
  | [],_=>rfl
  | false::b,l=>by simp [LT.i5,a2n b l]
  | true::b,l=>by simp [LT.i5,a2n b l.tail]
def a6q (bI bJ κU ιU:List Bool):List Bool :=
  sel (scR bJ κU) (eqF (bwL and (scX bJ κU) bI) (scX bI ιU)) []
def a32 (z:List Bool):List Bool :=
  let κU:=(a0 z).1
  let ιU:=(a0 (a0 z).2).1
  let e:=(a0 (a0 z).2).2
  sel (a6q (mBI e) (mBJ e) κU ιU) (f3 (mW e)) (b5 (mW e) κU (mT e))
lemma b2e {u1 u2 u3 u4:List Bool→ List Bool} (h1:a4 u1) (h2:a4 u2)
    (h3:a4 u3) (h4:a4 u4):a4 (fun s=>a6q (u1 s) (u2 s) (u3 s) (u4 s)) :=
  d6 (b85 h2 h3) (a1r (s9 and (b1u h2 h3) h1) (b1u h1 h4))
    (b0 [])
lemma b2x:a4 a32:=by
  have hκ:=a6
  have hι:=a2 a3 a6
  have he:=a2 a3 a3
  exact b7 (d6 (b2e (a2 he b6w) (a2 he b7q) hκ hι)
    (a2 (a2 he b0j) n6)
    (k5 (a2 he b0j) hκ (a2 he b90))) (fun _=>rfl)
def a3l (y:List Bool):List Bool :=
  a1z (fun a=>mW (a0 a).2) a32 (fun a=>mP (a0 a).2) (fun a=>a) y
lemma b38:a4 a3l :=
  a3t (b7 (a2 a3 b0j) (fun _=>rfl)) b2x
    (b7 (a2 a3 b40) (fun _=>rfl)) g5
def a6g (e:List Bool):List Bool :=
  (List.range (mP e).length).flatMap fun i=>a3l (a1 (un i) e)
lemma b5d:a4 a6g:=d9 b38 b40 g5
abbrev msC (bI bJ:List Bool) (κ ι:ℕ):Prop :=
  LT.f6 bJ κ.bits= []∧ bwL and (LT.i5 bJ κ.bits) bI= LT.i5 bI ι.bits
lemma b4f (bI bJ:List Bool) (hIJ:bI.length= bJ.length) (κ ι:ℕ) :
    a6q bI bJ (un κ) (un ι)= if msC bI bJ κ ι then [true] else []:=by
  unfold a6q
  rw [b8j,b4t,b4t,b4,b4,
    a6w _ _ (by rw [t7,a2n,a2n,hIJ])]
  unfold sel
  by_cases h1:LT.f6 bJ κ.bits= []
  · rw [if_pos h1]
    by_cases h2:bwL and (LT.i5 bJ κ.bits) bI= LT.i5 bI ι.bits
    · rw [if_pos h2,if_pos ⟨h1,h2⟩]
    · rw [if_neg h2,if_neg (fun h=>h2 h.2)]
  · rw [if_neg h1,if_neg (fun h=>h1 h.1)]
lemma b36 (κ ι:ℕ) (e:List Bool) (hIJ:(mBI e).length= (mBJ e).length) :
    val (a32 (a1 (un κ) (a1 (un ι) e))) =
      if msC (mBI e) (mBJ e) κ ι then val (b5 (mW e) (un κ) (mT e)) else 0:=by
  simp only [a32,a5]
  rw [b4f _ _ hIJ]
  by_cases h:msC (mBI e) (mBJ e) κ ι
  · rw [if_pos h,if_pos h]; rfl
  · rw [if_neg h,if_neg h]; exact w1 _
lemma a6r (ι:ℕ) (e:List Bool) :
    (a3l (a1 (un ι) e)).length= (mW e).length ∧
    val (a3l (a1 (un ι) e))= (∑ κ∈ Finset.range (mP e).length,
      (val (a32 (a1 (un κ) (a1 (un ι) e))):ℕ)) % 2 ^ (mW e).length:=by
  have h:=a2h (fun a=>mW (a0 a).2) a32 (fun a=>mP (a0 a).2) (fun a=>a)
    (a1 (un ι) e)
  simp only [a5] at h
  exact h
lemma b5s (e:List Bool) (ι:ℕ) (hι:ι< (mP e).length) :
    b5 (mW e) (un ι) (a6g e)= a3l (a1 (un ι) e):=by
  have h:=l8 (fun i=>a3l (a1 (un i) e)) (mW e).length
    (fun i=>(a6r i e).1) (List.range (mP e).length) ι (by simpa using hι) (mW e) (un ι)
    rfl (b4 ι)
  rw [a6g,h,List.getElem_range]
end asmP24
section asmP25
open Turing PEqualNP.Library Lib.Machines Lib.Universal
def pf:ℕ→ List Bool→ List Bool
  | 0,s=>(a0 s).1
  | n+ 1,s=>pf n (a0 s).2
def pr:ℕ→ List Bool→ List Bool
  | 0,s=>s
  | n+ 1,s=>pr n (a0 s).2
lemma t9:∀ n,a4 (pf n)
  | 0=>a6
  | n+ 1=>b7 (a2 a3 (t9 n)) (fun _=>rfl)
lemma b4a:∀ n,a4 (pr n)
  | 0=>b7 g5 (fun _=>rfl)
  | n+ 1=>b7 (a2 a3 (b4a n)) (fun _=>rfl)
def zPG (Z:List Bool):List Bool:=pf 0 Z
def zGC (Z:List Bool):List Bool:=pf 1 Z
def zP (Z:List Bool):List Bool:=pf 0 (zPG Z)
def zM (Z:List Bool):List Bool:=[true]++pf 2 (zPG Z)
def zN (Z:List Bool):List Bool:=pf 9 (zPG Z)
def zWt (Z:List Bool):List Bool:=pf 3 (zGC Z)
def zL (Z:List Bool):List Bool:=j0 (zP Z) (zWt Z)
def y1 (Z:List Bool):List Bool:=pf 1 (zPG Z)++f3 (pf 3 (zPG Z))
def a7r (Z iU:List Bool):List Bool :=
  b5 (pf 10 (zPG Z)++(pf 1 (zPG Z)++pf 3 (zPG Z))) iU (pr 11 (zPG Z))
def g7 (Z iU:List Bool):List Bool:=g8 (pf 10 (zPG Z)) (a7r Z iU)
def b20 (Z iU:List Bool):List Bool:=m4 (pf 10 (zPG Z)) (a7r Z iU)
lemma v7:a4 zPG:=t9 0
lemma b6o:a4 zGC:=t9 1
lemma a9h:a4 zP:=b7 (a2 v7 (t9 0)) (fun _=>rfl)
lemma b9a:a4 zM:=b8 (b0 [true]) (a2 v7 (t9 2))
lemma b4i:a4 zN:=b7 (a2 v7 (t9 9)) (fun _=>rfl)
lemma a7x:a4 zWt:=b7 (a2 b6o (t9 3)) (fun _=>rfl)
lemma b0p:a4 zL:=g9 a9h a7x
lemma b31:a4 y1 :=
  b8 (a2 v7 (t9 1)) (a2 (a2 v7 (t9 3)) n6)
lemma b0g {uz ui:List Bool→ List Bool} (hz:a4 uz) (hi:a4 ui) :
    a4 (fun s=>a7r (uz s) (ui s)) :=
  k5 (b8 (a2 (a2 hz v7) (t9 10))
    (b8 (a2 (a2 hz v7) (t9 1)) (a2 (a2 hz v7) (t9 3))))
    hi (a2 (a2 hz v7) (b4a 11))
lemma a9i {uz ui:List Bool→ List Bool} (hz:a4 uz) (hi:a4 ui) :
    a4 (fun s=>g7 (uz s) (ui s)) :=
  e8 (a2 (a2 hz v7) (t9 10)) (b0g hz hi)
lemma b5x {uz ui:List Bool→ List Bool} (hz:a4 uz) (hi:a4 ui) :
    a4 (fun s=>b20 (uz s) (ui s)) :=
  k4 (a2 (a2 hz v7) (t9 10)) (b0g hz hi)
def v0:List Bool→ List Bool→ List Bool
  | [],_=>[]
  | x::b,l=>(if x then [l.headD false] else [])++v0 b l.tail
def gaδ:Option Bool→ Bool→ Option Bool × Option Bool
  | none,x=>(some x,none)
  | some x,y=>(none,if x then some y else none)
lemma b9y (b l:List Bool):c7 gaδ (fun _=>none) none (ilv b l)= v0 b l:=by
  induction b generalizing l with
  | nil=>rfl
  | cons x b ih=>cases x <;> simp [ilv,c7,gaδ,v0,ih]
lemma a8p {ub ul:List Bool→ List Bool} (hb:a4 ub) (hl:a4 ul) :
    a4 (fun s=>v0 (ub s) (ul s)):=by
  have h:a4 (fun s=>c7 gaδ (fun _=>none) none s) :=
    g0 _ _ _ gaδ (fun _=>none) none (fun _=>rfl)
  exact b7 (a2 (b1w hb hl) h) (fun s=>b9y _ _)
def k1 (z:List Bool):List Bool :=
  let iU:=(a0 z).1
  let jU:=(a0 (a0 z).2).1
  let Z:=(a0 (a0 z).2).2
  sel (g8 iU jU) [] (eqF (b20 Z jU) (a37 (zN Z) iU))
lemma b21:a4 k1:=by
  have hi:=a6
  have hj:=a2 a3 a6
  have hZ:=a2 a3 a3
  exact b7 (d6 (e8 hi hj) (b0 [])
    (a1r (b5x hZ hj) (a7b (a2 hZ b4i) hi))) (fun _=>rfl)
def x9 (Z iU jU T:List Bool):List Bool :=
  let bI:=g7 Z iU
  let bJ:=g7 Z jU
  let Tj:=b5 (zL Z) jU T
  a1 (zWt Z) (a1 (zM Z) (a1 (zP Z)
    (a1 (g4 (zM Z) (v0 bI (y1 Z)))
    (a1 (g4 (zM Z) (v0 bI (bwL and bJ (v8 (y1 Z)))))
    (a1 (b5 (zL Z) iU T)
      (a6g (a1 (zWt Z) (a1 (zP Z) (a1 bI (a1 bJ Tj))))))))))
lemma b41 {uz ui uj ut:List Bool→ List Bool} (hz:a4 uz) (hi:a4 ui)
    (hj:a4 uj) (ht:a4 ut):a4 (fun s=>x9 (uz s) (ui s) (uj s) (ut s)):=by
  have hW:=a2 hz a7x
  have hM:=a2 hz b9a
  have hP:=a2 hz a9h
  have hL:=a2 hz b0p
  have hN:=a2 hz b31
  have hbI:=a9i hz hi
  have hbJ:=a9i hz hj
  exact b7 (a7 hW (a7 hM (a7 hP
    (a7 (n4 hM (a8p hbI hN))
    (a7 (n4 hM (a8p hbI (s9 and hbJ (a2 hN a0x))))
    (a7 (k5 hL hi ht)
      (a2 (a7 hW (a7 hP (a7 hbI (a7 hbJ
        (k5 hL hj ht))))) b5d))))))) (fun _=>rfl)
def f4 (z:List Bool):List Bool :=
  a17 (x9 (a0 (a0 (a0 z).2).2).1 (a0 z).1 (a0 (a0 z).2).1
    (a0 (a0 (a0 z).2).2).2)
lemma b28:a4 f4 :=
  b7 (a2 (b41 (a2 (a2 a3 a3) a6)
    a6 (a2 a3 a6)
    (a2 (a2 a3 a3) a3)) b35) (fun _=>rfl)
def a53 (leaf:List Bool→ List Bool) (Z:List Bool):List Bool :=
  a7a zN zL leaf k1 f4 Z
def a8a (leaf:List Bool→ List Bool) (Z:List Bool):List Bool :=
  a1z (fun e=>(a0 e).1) (fun a=>b5 (a0 (a0 a).2).1 (a0 a).1
      (a0 (a0 a).2).2)
    zP (fun Z=>a1 (zWt Z) (b5 (zL Z) [] (a53 leaf Z))) Z
lemma b5b {leaf:List Bool→ List Bool} (hleaf:a4 leaf):a4 (a8a leaf):=by
  have harr:a4 (a53 leaf):=b2h b4i b0p hleaf b21 b28
  have h1:=a2 a3 a6
  have h2:=a2 a3 a3
  have hf:=k5 h1 a6 h2
  have harg:=a7 a7x (k5 b0p (b0 []) harr)
  exact b7 (a3t a6 hf a9h harg) (fun _=>rfl)
end asmP25
section asmP26
open Turing PEqualNP.Library Lib.Machines Lib.Universal
lemma a5o:∀ (a b:List Bool),a.length= b.length→ val a= val b→ a= b
  | [],[],_,_=>rfl
  | [],_::_,h,_=>by simp at h
  | _::_,[],h,_=>by simp at h
  | x :: a, y :: b, h, hv => by
    simp only [val] at hv
    have hl:a.length= b.length:=by simpa using h
    have hx:x= y:=by cases x <;> cases y <;> simp at hv ⊢ <;> omega
    subst hx
    have:val a= val b:=by omega
    rw [a5o a b hl this]
lemma b5c (mU b:List Bool) (hb:b.length= mU.length):n3 mU (un (val b))= b :=
  a5o _ _ (by rw [n8,hb])
    (by rw [a6k,b4,← hb,Nat.mod_eq_of_lt (a4i b)])
lemma b7z (wU mU pU T b:List Bool) (hb:b.length= mU.length)
    (hp:pU.length= 2 ^ mU.length) :
    val (lkB wU mU pU T b)= val (b5 wU (un (val b)) T) % 2 ^ wU.length:=by
  rw [(b56 wU mU pU T b hb).2]
  have hvb:val b< pU.length:=by rw [hp,← hb]; exact a4i b
  have e:∀ ν∈ Finset.range pU.length,
      (if n3 mU (un ν)= b then val (b5 wU (un ν) T) else 0:ℕ) =
        if val b= ν then val (b5 wU (un ν) T) else 0:=by
    intro ν hν
    rw [Finset.mem_range,hp] at hν
    by_cases h:n3 mU (un ν)= b
    · rw [if_pos h, if_pos]
      rw [← h,a6k,b4,Nat.mod_eq_of_lt hν]
    · rw [if_neg h, if_neg]
      rintro rfl
      exact h (b5c mU b hb)
  rw [Finset.sum_congr rfl e,Finset.sum_ite_eq,if_pos (Finset.mem_range.mpr hvb)]
lemma b4b (ι:ℕ) (e:List Bool) (hNM:(eNM e).length= (eM e).length)
    (hSJ:(eSJ e).length= (eM e).length) (hp:(eP e).length= 2 ^ (eM e).length) :
    val (a2f (a1 (un ι) e))= (∑ μ∈ Finset.range (eP e).length,
      (if mgP (eM e).length ι μ (fun x=>(eNM e).getD x false) then
        (val (b5 (eW e) (un μ) (eA e)) *
          (val (b5 (eW e) (un (val (a3h (eNM e) (eSJ e) (n3 (eM e) (un ι))
            (n3 (eM e) (un μ))))) (eMs e)) % 2 ^ (eW e).length)) % 2 ^ (eW e).length
        else 0:ℕ)) % 2 ^ (eW e).length:=by
  rw [(a3x ι e).2]
  refine congrArg (· % 2 ^ (eW e).length) (Finset.sum_congr rfl fun μ _=>?_)
  rw [(b17 μ ι e).2,b14 _ _ hNM,
    b7z _ _ _ _ _ (b11 _ _ _ _ _ (n8 _ _)) hp]
  by_cases h:mgP (eM e).length ι μ (fun x=>(eNM e).getD x false)
  · rw [if_pos h,if_neg (by simp),if_pos h]
  · rw [if_neg h,if_pos rfl,if_neg h]
lemma b3x (ι:ℕ) (e:List Bool) (hIJ:(mBI e).length= (mBJ e).length) :
    val (a3l (a1 (un ι) e))= (∑ κ∈ Finset.range (mP e).length,
      (if msC (mBI e) (mBJ e) κ ι then val (b5 (mW e) (un κ) (mT e)) else 0:ℕ)) %
        2 ^ (mW e).length:=by
  rw [(a6r ι e).2]
  exact congrArg (· % 2 ^ (mW e).length)
    (Finset.sum_congr rfl fun κ _=>b36 κ ι e hIJ)
lemma a4g (Z iU jU T:List Bool) :
    eW (x9 Z iU jU T)= zWt Z∧ eM (x9 Z iU jU T)= zM Z∧ eP (x9 Z iU jU T)= zP Z ∧
    eNM (x9 Z iU jU T)= g4 (zM Z) (v0 (g7 Z iU) (y1 Z)) ∧
    eSJ (x9 Z iU jU T)= g4 (zM Z) (v0 (g7 Z iU) (bwL and (g7 Z jU) (v8 (y1 Z)))) ∧
    eA (x9 Z iU jU T)= b5 (zL Z) iU T ∧
    eMs (x9 Z iU jU T)= a6g (a1 (zWt Z) (a1 (zP Z) (a1 (g7 Z iU)
      (a1 (g7 Z jU) (b5 (zL Z) jU T))))):=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [x9,eW,eM,eP,eNM,eSJ,eA,eMs,a5]
lemma a96 (iU jU Z T:List Bool) :
    (f4 (a1 iU (a1 jU (a1 Z T)))).length= (zL Z).length:=by
  simp only [f4,a5]
  rw [a95]
  obtain ⟨h1,-,h3,-⟩:=a4g Z iU jU T
  rw [h1,h3,zL,j0,b4]
def d7 (Z iU:List Bool) (x:ℕ):Bool:=(g4 (zM Z) (v0 (g7 Z iU) (y1 Z))).getD x false
def w5 (Z iU jU:List Bool) (x:ℕ):Bool :=
  (g4 (zM Z) (v0 (g7 Z iU) (bwL and (g7 Z jU) (v8 (y1 Z))))).getD x false
def a5a (Z iU jU T:List Bool) (ν:ℕ):ℕ :=
  (∑ κ∈ Finset.range (zP Z).length,(if msC (g7 Z iU) (g7 Z jU) κ ν then
    val (b5 (zWt Z) (un κ) (b5 (zL Z) jU T)) else 0:ℕ)) % 2 ^ (zWt Z).length
lemma b9x (Z iU jU T:List Bool) (ν:ℕ) (hν:ν< (zP Z).length)
    (hIJ:(g7 Z iU).length= (g7 Z jU).length) :
    val (b5 (zWt Z) (un ν) (a6g (a1 (zWt Z) (a1 (zP Z) (a1 (g7 Z iU)
      (a1 (g7 Z jU) (b5 (zL Z) jU T)))))))= a5a Z iU jU T ν:=by
  have hmr:=b5s (a1 (zWt Z) (a1 (zP Z) (a1 (g7 Z iU) (a1 (g7 Z jU)
    (b5 (zL Z) jU T))))) ν (by simp only [mP,a5]; exact hν)
  simp only [mW,a5] at hmr
  rw [hmr,b3x _ _ (by simp only [mBI,mBJ,a5]; exact hIJ)]
  simp only [mW,mP,mBI,mBJ,mT,a5]
  rfl
lemma b2p (i j ι:ℕ) (Z T:List Bool) (hp:(zP Z).length= 2 ^ (zM Z).length)
    (hι:ι< (zP Z).length) (hIJ:(g7 Z (un i)).length= (g7 Z (un j)).length) :
    val (b5 (zWt Z) (un ι) (f4 (a1 (un i) (a1 (un j) (a1 Z T))))) =
      (∑ Y∈ (mNm (zM Z).length ι (d7 Z (un i))).powerset,
        (val (b5 (zWt Z) (un (f0 (mTg (zM Z).length ι (d7 Z (un i))∪ Y)))
          (b5 (zL Z) (un i) T)) *
          (a5a Z (un i) (un j) T (f0 ((mTg (zM Z).length ι (d7 Z (un i))).filter
            (fun x=>w5 Z (un i) (un j) x)∪ (mNm (zM Z).length ι (d7 Z (un i)) \ Y))) %
            2 ^ (zWt Z).length)) % 2 ^ (zWt Z).length) % 2 ^ (zWt Z).length:=by
  obtain ⟨hW,hM,hP,hNM,hSJ,hA,hMs⟩:=a4g Z (un i) (un j) T
  have hstep:f4 (a1 (un i) (a1 (un j) (a1 Z T))) =
      a17 (x9 Z (un i) (un j) T):=by simp only [f4,a5]
  have hrec:b5 (zWt Z) (un ι) (a17 (x9 Z (un i) (un j) T)) =
      a2f (a1 (un ι) (x9 Z (un i) (un j) T)):=by
    have h:=b2i (x9 Z (un i) (un j) T) ι (by rw [hP]; exact hι)
    rwa [hW] at h
  have hv:=b4b ι (x9 Z (un i) (un j) T) (by rw [hNM,hM,i4])
    (by rw [hSJ,hM,i4]) (by rw [hP,hM]; exact hp)
  rw [hW,hM,hP,hNM,hSJ,hA,hMs,hp] at hv
  rw [hstep,hrec,hv]
  have enm:(fun x=>(g4 (zM Z) (v0 (g7 Z (un i)) (y1 Z))).getD x false) =
      d7 Z (un i):=rfl
  rw [enm,b7n]
  refine congrArg (· % 2 ^ (zWt Z).length) (Finset.sum_congr rfl fun Y hY=>?_)
  rw [Finset.mem_powerset] at hY
  have hν:=b5j (zM Z).length ι (d7 Z (un i)) (w5 Z (un i) (un j)) Y hY _
    (fun x=>b3o (zM Z) _ _ (i4 _ _) (i4 _ _) ι
      (f0 (mTg (zM Z).length ι (d7 Z (un i))∪ Y)) x)
  have hνp:f0 ((mTg (zM Z).length ι (d7 Z (un i))).filter (fun x=>w5 Z (un i) (un j) x) ∪
      (mNm (zM Z).length ι (d7 Z (un i)) \ Y))< (zP Z).length:=by
    rw [hp]
    exact a2b _ _ (Finset.union_subset
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      (Finset.sdiff_subset.trans (Finset.filter_subset _ _)))
  show (val (b5 (zWt Z) (un (f0 (mTg (zM Z).length ι (d7 Z (un i))∪ Y)))
      (b5 (zL Z) (un i) T))* (val (b5 (zWt Z) (un (val (a3h
      (g4 (zM Z) (v0 (g7 Z (un i)) (y1 Z)))
      (g4 (zM Z) (v0 (g7 Z (un i)) (bwL and (g7 Z (un j)) (v8 (y1 Z)))))
      (n3 (zM Z) (un ι)) (n3 (zM Z) (un (f0 (mTg (zM Z).length ι (d7 Z (un i))∪ Y)))))))
      (a6g (a1 (zWt Z) (a1 (zP Z) (a1 (g7 Z (un i)) (a1 (g7 Z (un j))
        (b5 (zL Z) (un j) T))))))) % 2 ^ (zWt Z).length)) % 2 ^ (zWt Z).length= _
  rw [hν,b9x Z (un i) (un j) T _ hνp hIJ]
end asmP26
section asmP27
open Finset Turing PEqualNP.Library Lib.Machines Lib.Universal
lemma a67 {α:Type} (s:Finset α) (M:ℕ) (f g:α→ ℕ) (h:∀ a,f a % M= g a % M) :
    (∑ a∈ s,f a) % M= (∑ a∈ s,g a) % M:=by
  rw [Finset.sum_nat_mod,Finset.sum_nat_mod s M g]
  exact congrArg (· % M) (Finset.sum_congr rfl fun a _=>h a)
lemma b6d {α β:Type} (s:Finset α) (u:α→ Finset β) (M:ℕ) (f g:α→ β→ ℕ)
    (h:∀ a b,f a b % M= g a b % M) :
    (∑ a∈ s,∑ b∈ u a,f a b) % M= (∑ a∈ s,∑ b∈ u a,g a b) % M :=
  a67 s M _ _ fun a=>a67 (u a) M _ _ fun b=>h a b
section
variable {k t:ℕ} (E:Finset (Fin k × Fin k)) (B:Fin (t+1)→ Finset ℕ) (i j:Fin (t+1))
  (Z T:List Bool) (kt kacc:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ)
  (vI vJ:ℕ→ Prop) [DecidablePred vI] [DecidablePred vJ]
  (σI σJ:ℕ→ Finset (Fin k × Fin k)) (τI τJ:ℕ→ Finset (Fin k))
lemma b68
    (hTj:∀ κ< (zP Z).length,val (b5 (zWt Z) (un κ) (b5 (zL Z) (un j.val) T)) =
      if vJ κ then kt (σJ κ) (τJ κ) % 2 ^ (zWt Z).length else 0)
    (HM:∀ ι',vI ι'→ ∀ f:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ,
      (∑ κ∈ range (zP Z).length,if msC (g7 Z (un i.val)) (g7 Z (un j.val)) κ ι' then
        (if vJ κ then f (σJ κ) (τJ κ) else 0) else 0) =
      ∑ σj ∈ (sig B j E).powerset, ∑ τj ∈ (univ.filter (fun v : Fin k => v.val ∈ B j)).powerset,
        if sig B i σj= σI ι'∧ τj.filter (fun v=>v.val∈ B i)= τI ι' then f σj τj else 0)
    (ι':ℕ) (hv:vI ι') :
    a5a Z (un i.val) (un j.val) T ι'= a6h E B kt i j (σI ι') (τI ι') % 2 ^ (zWt Z).length:=by
  unfold a5a
  have HM':=HM ι' hv (fun σ τ=>kt σ τ % 2 ^ (zWt Z).length)
  have e1:∀ κ∈ range (zP Z).length,
      (if msC (g7 Z (un i.val)) (g7 Z (un j.val)) κ ι' then
        val (b5 (zWt Z) (un κ) (b5 (zL Z) (un j.val) T)) else 0:ℕ) =
      if msC (g7 Z (un i.val)) (g7 Z (un j.val)) κ ι' then
        (if vJ κ then kt (σJ κ) (τJ κ) % 2 ^ (zWt Z).length else 0) else 0 :=
    fun κ hκ=>by rw [hTj κ (mem_range.mp hκ)]
  rw [Finset.sum_congr rfl e1,HM',a6h]
  apply b6d
  intro a b
  split_ifs <;> simp [Nat.mod_mod]
lemma b2n (hp:(zP Z).length= 2 ^ (zM Z).length)
    (hIJ:(g7 Z (un i.val)).length= (g7 Z (un j.val)).length)
    (hTi:∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un i.val) T)) =
      if vI μ then kacc (σI μ) (τI μ) % 2 ^ (zWt Z).length else 0)
    (hTj:∀ κ< (zP Z).length,val (b5 (zWt Z) (un κ) (b5 (zL Z) (un j.val) T)) =
      if vJ κ then kt (σJ κ) (τJ κ) % 2 ^ (zWt Z).length else 0)
    (HM:∀ ι',vI ι'→ ∀ f:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ,
      (∑ κ∈ range (zP Z).length,if msC (g7 Z (un i.val)) (g7 Z (un j.val)) κ ι' then
        (if vJ κ then f (σJ κ) (τJ κ) else 0) else 0) =
      ∑ σj ∈ (sig B j E).powerset, ∑ τj ∈ (univ.filter (fun v : Fin k => v.val ∈ B j)).powerset,
        if sig B i σj= σI ι'∧ τj.filter (fun v=>v.val∈ B i)= τI ι' then f σj τj else 0)
    (HS:∀ ι< (zP Z).length,vI ι →
      (∀ Y⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
        vI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)) ∧
        σI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))= σI ι ∧
        vI (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) ∧
        σI (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) =
          sig B j (σI ι) ∧
        τI (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) =
          τI ι \ τI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))) ∧
      ∀ g : Finset (Fin k) → ℕ, (∑ Y ∈ (mNm (zM Z).length ι (d7 Z (un i.val))).powerset,
        g (τI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))))= ∑ τ1∈ (τI ι).powerset,g τ1)
    (HZ:∀ ι< (zP Z).length,¬ vI ι→ ∀ Y⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
      ¬ vI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)))
    (ι:ℕ) (hι:ι< (zP Z).length) :
    val (b5 (zWt Z) (un ι) (f4 (a1 (un i.val) (a1 (un j.val) (a1 Z T))))) =
      if vI ι then s0 E B kt i j kacc (σI ι) (τI ι) % 2 ^ (zWt Z).length else 0:=by
  rw [b2p i.val j.val ι Z T hp hι hIJ]
  have hbound:∀ Y⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
      f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)< (zP Z).length:=fun Y hY=>by
    rw [hp]
    exact a2b _ _ (union_subset (filter_subset _ _) (hY.trans (filter_subset _ _)))
  by_cases hv:vI ι
  · rw [if_pos hv]
    obtain ⟨H1,H2⟩:=HS ι hι hv
    have e1:∀ Y∈ (mNm (zM Z).length ι (d7 Z (un i.val))).powerset,
        (val (b5 (zWt Z) (un (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)))
          (b5 (zL Z) (un i.val) T)) *
          (a5a Z (un i.val) (un j.val) T (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
            (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) %
            2 ^ (zWt Z).length)) % 2 ^ (zWt Z).length =
        (kacc (σI ι) (τI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))) % 2 ^ (zWt Z).length *
          (a6h E B kt i j (sig B j (σI ι))
            (τI ι \ τI (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))) %
            2 ^ (zWt Z).length % 2 ^ (zWt Z).length)) % 2 ^ (zWt Z).length:=by
      intro Y hY
      rw [mem_powerset] at hY
      obtain ⟨hv1,hs1,hv2,hs2,ht2⟩:=H1 Y hY
      rw [hTi _ (hbound Y hY),if_pos hv1,hs1,b68 E B i j Z T kt vI vJ σI σJ τI τJ hTj HM _ hv2,
        hs2,ht2]
    rw [Finset.sum_congr rfl e1,H2 (fun τ1=>(kacc (σI ι) τ1 % 2 ^ (zWt Z).length *
      (a6h E B kt i j (sig B j (σI ι)) (τI ι \ τ1) % 2 ^ (zWt Z).length % 2 ^ (zWt Z).length)) %
      2 ^ (zWt Z).length),s0]
    apply a67
    intro τ1
    simp only [Nat.mod_mod,Nat.mul_mod]
  · rw [if_neg hv]
    have e0:∀ Y∈ (mNm (zM Z).length ι (d7 Z (un i.val))).powerset,
        (val (b5 (zWt Z) (un (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)))
          (b5 (zL Z) (un i.val) T)) *
          (a5a Z (un i.val) (un j.val) T (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
            (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) %
            2 ^ (zWt Z).length)) % 2 ^ (zWt Z).length= 0:=by
      intro Y hY
      rw [mem_powerset] at hY
      rw [hTi _ (hbound Y hY),if_neg (HZ ι hι hv Y hY),zero_mul,Nat.zero_mod]
    rw [Finset.sum_congr rfl e0,sum_const_zero,Nat.zero_mod]
end
end asmP27
section asmP28
open Turing PEqualNP.Library Lib.Machines Lib.Universal
lemma a2w (c:ℕ) (lenU:List Bool) (hl:lenU.length= c) :
    ∀ (Ts : List (List Bool)) (i : ℕ), (∀ r ∈ Ts, r.length = c) → i < Ts.length →
      b5 lenU (un i) (Ts.flatMap id)= Ts.getD i []:=by
  intro Ts
  induction Ts with
  | nil=>intro i _ hi; simp at hi
  | cons r Ts ih =>
    intro i hr hi
    have hrc:r.length= c:=hr r (by simp)
    cases i with
    | zero =>
      simp only [b5,k7,i6,j0,b4,hl,zero_mul,List.drop_zero,
        List.flatMap_cons,id]
      rw [List.take_left' hrc]; rfl
    | succ i =>
      have:=ih i (fun q hq=>hr q (by simp [hq])) (by simpa using hi)
      simp only [b5,k7,i6,j0,b4,hl] at this ⊢
      rw [List.flatMap_cons,show (i+ 1)* c= c+ i* c by ring,← List.drop_drop,id,
        List.drop_left' hrc,this]
      rfl
lemma a0i (Ts:List (List Bool)) (n m:ℕ) (r:List Bool) (h:m≠ n) :
    (Ts.set n r).getD m []= Ts.getD m []:=by
  simp [List.getD_eq_getElem?_getD,List.getElem?_set,Ne.symm h]
lemma a4f (Ts:List (List Bool)) (n:ℕ) (r:List Bool) (h:n< Ts.length) :
    (Ts.set n r).getD n []= r:=by
  simp [List.getD_eq_getElem?_getD,h]
lemma b0u (Ts:List (List Bool)) (L n:ℕ) (r:List Bool) (h:∀ q∈ Ts,q.length= L)
    (hr:r.length= L):∀ q∈ Ts.set n r,q.length= L:=by
  intro q hq
  rcases List.mem_or_eq_of_mem_set hq with h' | h'
  · exact h q h'
  · rw [h',hr]
lemma a60 {α β:Type*} (c:α→ Prop) [DecidablePred c] (F:β→ α→ β) :
    ∀ (l : List α) (b : β), (l.filter (fun a => decide (c a))).foldl F b =
      l.foldl (fun b a=>if c a then F b a else b) b:=by
  intro l
  induction l with
  | nil=>intro b; rfl
  | cons a l ih =>
    intro b
    by_cases h:c a
    · simp only [List.filter_cons,h,decide_true,if_true,List.foldl_cons]; exact ih _
    · simp only [List.filter_cons, h, decide_false, if_false, List.foldl_cons]
      exact ih _
section Glue
variable {k:ℕ} (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  {t:ℕ} (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ) (Z:List Bool)
  (vld:Fin (t+1)→ ℕ→ Prop) [∀ i ι,Decidable (vld i ι)]
  (sg:Fin (t+1)→ ℕ→ Finset (Fin k × Fin k)) (tu:Fin (t+1)→ ℕ→ Finset (Fin k))
def r0 (i:Fin (t+1)) (kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ) (ι:ℕ):ℕ :=
  if vld i ι then kt (sg i ι) (tu i ι) % 2 ^ (zWt Z).length else 0
def TH (i:Fin (t+1)) (T:List Bool) (kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ):Prop :=
  T.length= (zL Z).length ∧
    ∀ ι< (zP Z).length,val (b5 (zWt Z) (un ι) T)= r0 Z vld sg tu i kt ι
lemma b2m (W:ℕ)
    (htest:∀ i j:Fin (t+1),k1 (a1 (un i.val) (a1 (un j.val) Z))= [] ↔
      ¬ (i< j∧ par j= i))
    (hlen:∀ iU jU T,(f4 (a1 iU (a1 jU (a1 Z T)))).length= (zL Z).length)
    (hstepV:∀ (i j:Fin (t+1)),i< j→ par j= i→ ∀ (T:List Bool)
      (kacc kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ),
      T.length= (t+1)* (zL Z).length →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un i.val) T)) =
        r0 Z vld sg tu i kacc μ) →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un j.val) T)) =
        r0 Z vld sg tu j kt μ) →
      ∀ ι < (zP Z).length, val (b5 (zWt Z) (un ι)
        (f4 (a1 (un i.val) (a1 (un j.val) (a1 Z T))))) =
          r0 Z vld sg tu i (s0 E B kt i j kacc) ι)
    (n:Fin (t+1)) :
    ∀ (l : List (Fin (t+1))) (Ts : List (List Bool))
      (kacc:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ),
      Ts.length= t+1→ (∀ r∈ Ts,r.length= (zL Z).length) →
      TH Z vld sg tu n (Ts.getD n.val []) kacc →
      (∀ j:Fin (t+1),n< j →
        TH Z vld sg tu j (Ts.getD j.val []) (p8 E P H rows par B (2^W) (t+1) j)) →
      (l.foldl (fun Ts j=>z4 k1 f4 Z n.val Ts j.val) Ts).length= t+1 ∧
        (∀ r∈ l.foldl (fun Ts j=>z4 k1 f4 Z n.val Ts j.val) Ts,
          r.length= (zL Z).length) ∧
        (∀ m,m≠ n.val →
          (l.foldl (fun Ts j=>z4 k1 f4 Z n.val Ts j.val) Ts).getD m []= Ts.getD m []) ∧
        TH Z vld sg tu n ((l.foldl (fun Ts j=>z4 k1 f4 Z n.val Ts j.val) Ts).getD
          n.val []) (l.foldl (fun kacc j =>
          if n< j∧ par j= n then s0 E B (p8 E P H rows par B (2^W) (t+1) j) n j kacc
          else kacc) kacc):=by
  intro l
  induction l with
  | nil=>intro Ts kacc h1 h2 h3 _; exact ⟨h1,h2,fun _ _=>rfl,h3⟩
  | cons j l ih =>
    intro Ts kacc h1 h2 h3 h4
    simp only [List.foldl_cons]
    by_cases hc:n< j∧ par j= n
    · have hd:z4 k1 f4 Z n.val Ts j.val= Ts.set n.val
          (f4 (a1 (un n.val) (a1 (un j.val) (a1 Z (Ts.flatMap id))))):=by
        unfold z4; rw [if_neg (fun h=>((htest n j).mp h) hc)]
      rw [if_pos hc,hd]
      have hlenT:(Ts.flatMap id).length= (t+1)* (zL Z).length :=
        (a0u (t+1) _ Ts h1 h2)
      have hn:n.val< Ts.length:=by rw [h1]; exact n.isLt
      have hj:j.val< Ts.length:=by rw [h1]; exact j.isLt
      have hjn:j.val≠ n.val:=fun h=>(lt_irrefl _) (h ▸ Fin.lt_def.mp hc.1)
      have hTH:=h4 j hc.1
      obtain ⟨-,hTi⟩:=h3
      obtain ⟨-,hTj⟩:=hTH
      have hnew:TH Z vld sg tu n (f4 (a1 (un n.val) (a1 (un j.val)
          (a1 Z (Ts.flatMap id))))) (s0 E B (p8 E P H rows par B (2^W) (t+1) j) n j kacc):=by
        refine ⟨hlen _ _ _,?_⟩
        apply hstepV n j hc.1 hc.2 _ kacc _ hlenT
        · intro μ hμ
          rw [a2w _ (zL Z) rfl Ts n.val h2 hn]; exact hTi μ hμ
        · intro μ hμ
          rw [a2w _ (zL Z) rfl Ts j.val h2 hj]; exact hTj μ hμ
      obtain ⟨r1,r2,r3,r4⟩:=ih (Ts.set n.val (f4 (a1 (un n.val) (a1 (un j.val)
          (a1 Z (Ts.flatMap id)))))) (s0 E B (p8 E P H rows par B (2^W) (t+1) j) n j kacc)
        (by rw [List.length_set,h1]) (b0u Ts _ n.val _ h2 (hlen _ _ _)) (by rw [a4f _ _ _ hn]; exact hnew)
        (fun j' hj'=>by
          rw [a0i _ _ _ _ (fun h=>(lt_irrefl _) (h ▸ Fin.lt_def.mp hj'))]
          exact h4 j' hj')
      refine ⟨r1,r2,fun m hm=>?_,r4⟩
      rw [r3 m hm,a0i _ _ _ _ hm]
    · have hd:z4 k1 f4 Z n.val Ts j.val= Ts:=by
        unfold z4; rw [if_pos ((htest n j).mpr hc)]
      rw [if_neg hc,hd]
      exact ih Ts kacc h1 h2 h3 h4
lemma b2d (w W:ℕ) (hd:s4 E rows par B w) (leaf:List Bool→ List Bool)
    (htest:∀ i j:Fin (t+1),k1 (a1 (un i.val) (a1 (un j.val) Z))= [] ↔
      ¬ (i< j∧ par j= i))
    (hlen:∀ iU jU T,(f4 (a1 iU (a1 jU (a1 Z T)))).length= (zL Z).length)
    (hleafV:∀ i:Fin (t+1),TH Z vld sg tu i (leaf (a1 (un i.val) Z))
      (y0 E P H rows par B (2^W) i))
    (hstepV:∀ (i j:Fin (t+1)),i< j→ par j= i→ ∀ (T:List Bool)
      (kacc kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ),
      T.length= (t+1)* (zL Z).length →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un i.val) T)) =
        r0 Z vld sg tu i kacc μ) →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un j.val) T)) =
        r0 Z vld sg tu j kt μ) →
      ∀ ι < (zP Z).length, val (b5 (zWt Z) (un ι)
        (f4 (a1 (un i.val) (a1 (un j.val) (a1 Z T))))) =
          r0 Z vld sg tu i (s0 E B kt i j kacc) ι) :
    (a1x leaf k1 f4 Z (t+1) (zL Z).length).length= t+1 ∧
      (∀ r∈ a1x leaf k1 f4 Z (t+1) (zL Z).length,r.length= (zL Z).length) ∧
      ∀ i : Fin (t+1), TH Z vld sg tu i
        ((a1x leaf k1 f4 Z (t+1) (zL Z).length).getD i.val [])
        (p8 E P H rows par B (2^W) (t+1) i):=by
  obtain ⟨hpar0,hpar,hconnX,hconnE,-,-⟩:=a6p E rows par B w hd
  have hcover:∀ e∈ E,∃ a,c6 k e∈ B a :=
    fun e he=>by obtain ⟨a,ha,-⟩:=hconnE e he; exact ⟨a,ha⟩
  have key:∀ r,r≤ t+1→ ∀ Ts:List (List Bool),Ts.length= t+1 →
      (∀ q∈ Ts,q.length= (zL Z).length) →
      (∀ i:Fin (t+1),t+1 - r≤ i.val→ TH Z vld sg tu i (Ts.getD i.val [])
        (p8 E P H rows par B (2^W) (t+1) i)) →
      ∀ m,r+ m≤ t+1 →
      ((List.range m).foldl (fun Ts i'=>a11 leaf k1 f4 Z (t+1) Ts (r+ i')) Ts).length
        = t+1 ∧ (∀ q ∈ (List.range m).foldl (fun Ts i' => a11 leaf k1 f4 Z (t+1) Ts (r + i'))
          Ts,q.length= (zL Z).length) ∧
        ∀ i : Fin (t+1), t+1 - (r + m) ≤ i.val → TH Z vld sg tu i (((List.range m).foldl
          (fun Ts i'=>a11 leaf k1 f4 Z (t+1) Ts (r+ i')) Ts).getD i.val [])
          (p8 E P H rows par B (2^W) (t+1) i):=by
    intro r hr Ts h1 h2 h3 m
    induction m generalizing r Ts with
    | zero =>
      intro _
      simp only [List.range_zero,List.foldl_nil,Nat.add_zero]
      exact ⟨h1,h2,h3⟩
    | succ m ih =>
      intro hm
      rw [List.range_succ_eq_map,List.foldl_cons,List.foldl_map]
      have hrlt:r< t+1:=by omega
      set n:Fin (t+1):=⟨t+1-1-r,by omega⟩ with hn
      have hnv:t+1-1-(r+0)= n.val:=by simp [hn]
      have hdv:a11 leaf k1 f4 Z (t+1) Ts (r+0) =
          (List.finRange (t+1)).foldl (fun Ts j=>z4 k1 f4 Z n.val Ts j.val)
            (Ts.set n.val (leaf (a1 (un n.val) Z))):=by
        unfold a11
        rw [hnv,← List.map_coe_finRange_eq_range,List.foldl_map]
      have hnL:n.val< Ts.length:=by rw [h1]; exact n.isLt
      obtain ⟨r1,r2,r3,r4⟩:=b2m E P H rows par B Z vld sg tu W htest hlen hstepV n
        (List.finRange (t+1)) (Ts.set n.val (leaf (a1 (un n.val) Z)))
        (y0 E P H rows par B (2^W) n) (by rw [List.length_set,h1])
        (b0u Ts _ _ _ h2 (hleafV n).1) (by rw [a4f _ _ _ hnL]; exact hleafV n)
        (fun j hj=>by
          rw [a0i _ _ _ _ (fun h=>(lt_irrefl _) (h ▸ Fin.lt_def.mp hj))]
          exact h3 j (by have:=Fin.lt_def.mp hj; simp [hn] at this; omega))
      have hrec:(List.finRange (t+1)).foldl (fun kacc j =>
          if n< j∧ par j= n then s0 E B (p8 E P H rows par B (2^W) (t+1) j) n j kacc
          else kacc) (y0 E P H rows par B (2^W) n)= p8 E P H rows par B (2^W) (t+1) n:=by
        rw [b53 E P H rows par B hpar hpar0 hconnX hcover (2^W) E.card le_rfl n,k8,
          a60]
      rw [hrec] at r4
      have:=ih (r+1) (by omega) _ r1 r2 (fun i hi=>by
        by_cases hin:i.val= n.val
        · have : i = n := Fin.ext hin
          subst this; exact r4
        · rw [r3 i.val hin, a0i _ _ _ _ hin]
          exact h3 i (by simp [hn] at hin; omega)) (by omega)
      simp only [hdv] at this ⊢
      have e:∀ i',r+ 1+ i'= r+ (i'+ 1):=fun i'=>by omega
      simp only [e] at this
      simpa [Nat.add_assoc,Nat.add_comm 1] using this
  have hstart:(List.replicate (t+1) (List.replicate (zL Z).length false)).length= t+1 :=
    List.length_replicate
  have:=key 0 (by omega) _ hstart
    (fun q hq=>by rw [List.eq_of_mem_replicate hq,List.length_replicate])
    (fun i hi=>by have:=i.isLt; omega) (t+1) (by omega)
  simp only [zero_add] at this
  exact ⟨this.1,this.2.1,fun i=>this.2.2 i (by omega)⟩
lemma b87 (w W:ℕ) (hd:s4 E rows par B w) (leaf:List Bool→ List Bool)
    (hN:zN Z= un (t+1))
    (htest:∀ i j:Fin (t+1),k1 (a1 (un i.val) (a1 (un j.val) Z))= [] ↔
      ¬ (i< j∧ par j= i))
    (hlen:∀ iU jU T,(f4 (a1 iU (a1 jU (a1 Z T)))).length= (zL Z).length)
    (hleafV:∀ i:Fin (t+1),TH Z vld sg tu i (leaf (a1 (un i.val) Z))
      (y0 E P H rows par B (2^W) i))
    (hstepV:∀ (i j:Fin (t+1)),i< j→ par j= i→ ∀ (T:List Bool)
      (kacc kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ),
      T.length= (t+1)* (zL Z).length →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un i.val) T)) =
        r0 Z vld sg tu i kacc μ) →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un j.val) T)) =
        r0 Z vld sg tu j kt μ) →
      ∀ ι < (zP Z).length, val (b5 (zWt Z) (un ι)
        (f4 (a1 (un i.val) (a1 (un j.val) (a1 Z T))))) =
          r0 Z vld sg tu i (s0 E B kt i j kacc) ι)
    (hbij0:∀ f:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ,
      ∑ ι ∈ Finset.range (zP Z).length, (if vld 0 ι then f (sg 0 ι) (tu 0 ι) else 0) =
        ∑ σ ∈ (sig B 0 E).powerset,
          ∑ τ∈ (Finset.univ.filter (fun v:Fin k=>v.val∈ B 0)).powerset,f σ τ) :
    val (a8a leaf Z)= a35 E P H rows par B (2^W) % 2 ^ (zWt Z).length:=by
  obtain ⟨h1,h2,h3⟩:=b2d E P H rows par B Z vld sg tu w W hd leaf htest hlen hleafV
    hstepV
  have hdrv:=b4o zN zL leaf k1 f4 Z (t+1) (zL Z).length hN rfl
    (fun i hi=>(hleafV ⟨i,hi⟩).1) (fun i _ j _ T _=>hlen (un i) (un j) T)
  have hT0:b5 (zL Z) [] (a53 leaf Z) =
      (a1x leaf k1 f4 Z (t+1) (zL Z).length).getD 0 []:=by
    rw [a53,hdrv]
    exact a2w _ (zL Z) rfl _ 0 h2 (by rw [h1]; omega)
  have hs:=(a2h (fun e=>(a0 e).1) (fun a=>b5 (a0 (a0 a).2).1
    (a0 a).1 (a0 (a0 a).2).2) zP
    (fun Z=>a1 (zWt Z) (b5 (zL Z) [] (a53 leaf Z))) Z).2
  simp only [a5] at hs
  rw [show a8a leaf Z= a1z (fun e=>(a0 e).1) (fun a=>b5 (a0 (a0 a).2).1
    (a0 a).1 (a0 (a0 a).2).2) zP
    (fun Z=>a1 (zWt Z) (b5 (zL Z) [] (a53 leaf Z))) Z from rfl,hs,hT0]
  have hcell:∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ)
      ((a1x leaf k1 f4 Z (t+1) (zL Z).length).getD 0 [])) =
      r0 Z vld sg tu 0 (p8 E P H rows par B (2^W) (t+1) 0) μ:=by
    have:=(h3 0).2
    rw [Fin.val_zero] at this
    exact this
  rw [Finset.sum_congr rfl (fun μ hμ=>hcell μ (Finset.mem_range.mp hμ))]
  have hb:=hbij0 (fun σ τ=>p8 E P H rows par B (2^W) (t+1) 0 σ τ % 2 ^ (zWt Z).length)
  unfold r0
  rw [hb]
  unfold a35
  have e:∀ σ∈ (sig B 0 E).powerset,
      (∑ τ∈ (Finset.univ.filter (fun v:Fin k=>v.val∈ B 0)).powerset,
        p8 E P H rows par B (2^W) (t+1) 0 σ τ % 2 ^ (zWt Z).length) % 2 ^ (zWt Z).length =
      (∑ τ∈ (Finset.univ.filter (fun v:Fin k=>v.val∈ B 0)).powerset,
        p8 E P H rows par B (2^W) (t+1) 0 σ τ) % 2 ^ (zWt Z).length :=
    fun σ _=>(Finset.sum_nat_mod _ _ _).symm
  rw [Finset.sum_nat_mod (sig B 0 E).powerset,Finset.sum_congr rfl e,← Finset.sum_nat_mod]
lemma b63 (w:ℕ) (hd:s4 E rows par B w) (M:ℕ) (hM:E.card≤ M)
    (leaf:List Bool→ List Bool) (hN:zN Z= un (t+1))
    (hWt:(zWt Z).length= (M+1)* ((M+1)*(rows.length+1)*(4*t+5)))
    (htest:∀ i j:Fin (t+1),k1 (a1 (un i.val) (a1 (un j.val) Z))= [] ↔
      ¬ (i< j∧ par j= i))
    (hlen:∀ iU jU T,(f4 (a1 iU (a1 jU (a1 Z T)))).length= (zL Z).length)
    (hleafV:∀ i:Fin (t+1),TH Z vld sg tu i (leaf (a1 (un i.val) Z))
      (y0 E P H rows par B (2^(M+1)) i))
    (hstepV:∀ (i j:Fin (t+1)),i< j→ par j= i→ ∀ (T:List Bool)
      (kacc kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ),
      T.length= (t+1)* (zL Z).length →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un i.val) T)) =
        r0 Z vld sg tu i kacc μ) →
      (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un j.val) T)) =
        r0 Z vld sg tu j kt μ) →
      ∀ ι < (zP Z).length, val (b5 (zWt Z) (un ι)
        (f4 (a1 (un i.val) (a1 (un j.val) (a1 Z T))))) =
          r0 Z vld sg tu i (s0 E B kt i j kacc) ι)
    (hbij0:∀ f:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ,
      ∑ ι ∈ Finset.range (zP Z).length, (if vld 0 ι then f (sg 0 ι) (tu 0 ι) else 0) =
        ∑ σ ∈ (sig B 0 E).powerset,
          ∑ τ∈ (Finset.univ.filter (fun v:Fin k=>v.val∈ B 0)).powerset,f σ τ)
    (hPE:P⊆ E) (s j:ℕ) (hs:s≤ M) (hj:j≤ rows.length) :
    val (a8a leaf Z) / 2 ^ ((s* (rows.length+ 1)+ (j+ (2* rows.length* (t+1) -
      k6 rows)))* (M+ 1)) % 2 ^ (M+ 1)= t0 E P H rows par B s j:=by
  obtain ⟨hlt,hsl⟩:=b3v E P H rows par B w hd (M+1) (by omega) M hM
  rw [b87 E P H rows par B Z vld sg tu w (M+1) hd leaf hN htest hlen hleafV hstepV hbij0,hWt,
    Nat.mod_eq_of_lt hlt,hsl s j hs hj hPE,kap,← pow_mul,Nat.mul_comm (M+1)]
end Glue
end asmP28
section asmP29
namespace LT
open Lib.Machines Lib.Universal
lemma pfq:∀ (n:ℕ) (s:List Bool),pf n s= Dec.j4 n s
  | 0,_=>rfl
  | n+1,s=>pfq n (a0 s).2
lemma prq:∀ (n:ℕ) (s:List Bool),pr n s= Dec.a31 n s
  | 0,_=>rfl
  | n+1,s=>prq n (a0 s).2
lemma b8a (k:ℕ) (X Bi S:Finset ℕ) :
    bwL and (Dec.a9 k X) (Dec.a9 k Bi)= Dec.a9 k S ↔
      ∀ v∈ Dec.layout k,(v∈ X∧ v∈ Bi↔ v∈ S):=by
  rw [a7h _ _ _ (by simp [Dec.a9]),← b27 _ _ _ (by simp [Dec.a9]),Dec.a9,
    Dec.a9,Dec.a9,y2,List.map_inj_left]
  refine forall₂_congr (fun v _=>?_)
  rw [← Bool.decide_and,decide_eq_decide]
lemma a4t {t:ℕ} (k:ℕ) (B:Fin (t+1)→ Finset ℕ) (i j:Fin (t+1)) (κ ι:ℕ) :
    bwL and (i5 (Dec.a9 k (B j)) κ.bits) (Dec.a9 k (B i)) =
        i5 (Dec.a9 k (B i)) ι.bits ↔
      (sig B i (c8 k B j κ)= c8 k B i ι ∧
        (g6 k B j κ).filter (fun v=>v.val∈ B i)= g6 k B i ι):=by
  rw [a83,a83,b8a]
  constructor
  · intro h
    constructor
    · ext e
      simp only [l0,c8,Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases hl:c6 k e∈ Dec.layout k
      · exact h _ hl
      · exact ⟨fun h'=>absurd (a4k k _ κ _ h'.1) hl,fun h'=>absurd (a4k k _ ι _ h') hl⟩
    · ext v
      simp only [g6,Finset.mem_filter,Finset.mem_univ,true_and]
      exact h _ ((Dec.a0p k _).mpr (Or.inl v.isLt))
  · rintro ⟨h1, h2⟩ v hv
    rcases (Dec.a0p k v).mp hv with hv' | ⟨e,-,rfl⟩
    · have := Finset.ext_iff.mp h2 ⟨v, hv'⟩
      simpa [g6] using this
    · have := Finset.ext_iff.mp h1 e
      simp only [l0,c8,Finset.mem_filter,Finset.mem_univ,true_and] at this
      exact this
section Hyps
variable (k w:ℕ) (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  (t:ℕ) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
lemma c07 :
    zN (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))= un (t+1):=by
  rw [zN,zPG,pfq,pfq,Dec.gZ]
  simp only [Dec.j4,a5]
  exact (a03 (2^(w+1)) k w E P H rows t par B).2.2.2.2.2.2.2.1
lemma b6x (hP:∀ e∈ P,e.1< e.2) :
    (zWt (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))).length =
      (Dec.b6 k+ 1)* ((Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5)):=by
  obtain ⟨-,-,-,-,hWt,-⟩:=Dec.a0d (2^(w+1)) k w E P H rows t par B hP _ rfl
  rw [zWt,zGC,pfq,pfq,Dec.gZ]
  simp only [Dec.j4,a5,Dec.a24]
  rw [hWt,b4]
  ring
lemma a9r :
    zP (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))= un (2^(w+1)):=by
  rw [zP,zPG,pfq,pfq,Dec.gZ]
  simp only [Dec.j4,a5]
  exact (a03 (2^(w+1)) k w E P H rows t par B).1
lemma b7b (hP:∀ e∈ P,e.1< e.2) :
    zWt (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) =
      un ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1)* (4* t+ 5)):=by
  obtain ⟨-,-,-,-,hWt,-⟩:=Dec.a0d (2^(w+1)) k w E P H rows t par B hP _ rfl
  rw [zWt,zGC,pfq,pfq,Dec.gZ]
  simp only [Dec.j4,a5,Dec.a24]
  exact hWt
lemma b09 (j:Fin (t+1)) :
    g7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un j.val) =
      Dec.a9 k (B j):=by
  have e:g7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un j.val) =
      a4u (a1 [] (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))) (un j.val):=by
    simp only [g7,a7r,zPG,a4u,a7w,aPG,a5,pfq,prq]
    rfl
  rw [e,a55]
lemma b23 (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) :
    ∀ i : Fin (t+1), TH (Dec.gZ (un (2^(w+1)) ++ false :: Dec.a8 k w E P H rows t par B))
      (fun i ι=>f6 (Dec.a9 k (B i)) ι.bits= []) (c8 k B) (g6 k B) i
      (a2o (a1 (un i.val) (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))))
      (y0 E P H rows par B (2^(Dec.b6 k+ 1)) i):=by
  intro i
  have hp:=a9r k w E P H rows t par B
  have hw:=b7b k w E P H rows t par B hP
  refine ⟨?_,fun ι hι=>?_⟩
  · rw [zL,hp,hw,j0,b4,b4,b4,a8j _ _ _ E P H rows t par B hE hP i,
      Dec.a0q _ _ ((Dec.b6 k+ 1)* (Dec.b6 k+ 1)* (rows.length+ 1) *
        (4* t+ 5)) (fun ι=>by split_ifs <;> simp [i4,f3]),List.length_range]
  · rw [hp, b4] at hι
    unfold r0
    rw [hw,b4]
    exact b64 (2^(w+1)) k w E P H rows t par B hE hP i ι hι
lemma b4k (hE:∀ e∈ E,e.1< e.2) (hdec:Dec.f7 k E rows w t par B) :
    ∀ f : Finset (Fin k × Fin k) → Finset (Fin k) → ℕ,
      ∑ ι ∈ Finset.range (zP (Dec.gZ (un (2^(w+1)) ++ false ::
          Dec.a8 k w E P H rows t par B))).length,
        (if f6 (Dec.a9 k (B 0)) ι.bits= [] then f (c8 k B 0 ι) (g6 k B 0 ι) else 0) =
      ∑ σ ∈ (sig B 0 E).powerset,
        ∑ τ∈ (Finset.univ.filter (fun v:Fin k=>v.val∈ B 0)).powerset,f σ τ:=by
  intro f
  rw [a9r,b4]
  exact a8n k w E B 0 hE (hdec.2.2.1 0).1 (hdec.2.2.1 0).2 f
lemma b8u (hE:∀ e∈ E,e.1< e.2) (hdec:Dec.f7 k E rows w t par B)
    (i j:Fin (t+1)) :
    ∀ ι', f6 (Dec.a9 k (B i)) ι'.bits = [] → ∀ f : Finset (Fin k × Fin k) → Finset (Fin k) → ℕ,
      (∑ κ∈ Finset.range (zP (Dec.gZ (un (2^(w+1))++false ::
          Dec.a8 k w E P H rows t par B))).length,
        if msC (g7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un i.val))
          (g7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un j.val)) κ ι'
        then (if f6 (Dec.a9 k (B j)) κ.bits= [] then f (c8 k B j κ) (g6 k B j κ) else 0)
        else 0) =
      ∑ σj ∈ (sig B j E).powerset,
        ∑ τj ∈ (Finset.univ.filter (fun v : Fin k => v.val ∈ B j)).powerset,
          if sig B i σj= c8 k B i ι'∧ τj.filter (fun v=>v.val∈ B i)= g6 k B i ι'
          then f σj τj else 0:=by
  intro ι' _ f
  rw [a9r,b4,b09 k w E P H rows t par B i,b09 k w E P H rows t par B j]
  have hterm:∀ κ∈ Finset.range (2^(w+1)),
      (if msC (Dec.a9 k (B i)) (Dec.a9 k (B j)) κ ι' then
        (if f6 (Dec.a9 k (B j)) κ.bits= [] then f (c8 k B j κ) (g6 k B j κ) else 0) else 0) =
      if f6 (Dec.a9 k (B j)) κ.bits= [] then
        (if sig B i (c8 k B j κ)= c8 k B i ι' ∧
          (g6 k B j κ).filter (fun v=>v.val∈ B i)= g6 k B i ι'
          then f (c8 k B j κ) (g6 k B j κ) else 0) else 0:=by
    intro κ _
    by_cases h1:f6 (Dec.a9 k (B j)) κ.bits= []
    · by_cases h2:sig B i (c8 k B j κ)= c8 k B i ι' ∧
          (g6 k B j κ).filter (fun v=>v.val∈ B i)= g6 k B i ι'
      · rw [ite_eq_left ⟨h1,(a4t k B i j κ ι').mpr h2⟩,ite_eq_left h1,ite_eq_left h1,
          ite_eq_left h2]
      · rw [ite_eq_right (fun h=>h2 ((a4t k B i j κ ι').mp h.2)),ite_eq_left h1,
          ite_eq_right h2]
    · rw [ite_eq_right (fun h=>h1 h.1),ite_eq_right h1]
  rw [Finset.sum_congr rfl hterm]
  exact a8n k w E B j hE (hdec.2.2.1 j).1 (hdec.2.2.1 j).2
    (fun σ τ=>if sig B i σ= c8 k B i ι'∧ τ.filter (fun v=>v.val∈ B i)= g6 k B i ι'
      then f σ τ else 0)
end Hyps
end LT
end asmP29
section asmP30
open Finset Turing PEqualNP.Library Lib.Machines Lib.Universal
section
variable {k t:ℕ} (B:Fin (t+1)→ Finset ℕ) (i j:Fin (t+1)) (Z:List Bool)
lemma a8z (n m:ℕ) (hnm:n≤ m) (nm:ℕ→ Bool) (ι:ℕ) (hι:ι< 2 ^ n) (x:ℕ) :
    ι.testBit x= decide (x∈ mTg m ι nm∪ mNm m ι nm):=by
  by_cases hx:x< n
  · cases h:ι.testBit x <;> cases hn:nm x <;> simp [mTg,mNm,h,hn,show x< m by omega]
  · have h0:ι.testBit x= false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hι (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [mTg,mNm,h0]
lemma b9c (hm:(LT.e9 k (B i)).length≤ (zM Z).length)
    (hNm:∀ x,d7 Z (un i.val) x =
      decide (x< (LT.e9 k (B i)).length∧ (LT.e9 k (B i)).getD x 0< k))
    (hSj:∀ x,w5 Z (un i.val) (un j.val) x= decide (x< (LT.e9 k (B i)).length ∧
      ¬ (LT.e9 k (B i)).getD x 0< k∧ (LT.e9 k (B i)).getD x 0∈ B j))
    (ι:ℕ) (hv:LT.f6 (Dec.a9 k (B i)) ι.bits= []) :
    (∀ Y⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
        LT.f6 (Dec.a9 k (B i)) (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)).bits= [] ∧
        LT.c8 k B i (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))= LT.c8 k B i ι ∧
        LT.f6 (Dec.a9 k (B i)) (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))).bits= [] ∧
        LT.c8 k B i (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) =
          sig B j (LT.c8 k B i ι) ∧
        LT.g6 k B i (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) =
          LT.g6 k B i ι \ LT.g6 k B i (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))) ∧
      ∀ g : Finset (Fin k) → ℕ, (∑ Y ∈ (mNm (zM Z).length ι (d7 Z (un i.val))).powerset,
        g (LT.g6 k B i (f0 (mTg (zM Z).length ι (d7 Z (un i.val)) ∪ Y)))) =
          ∑ τ1∈ (LT.g6 k B i ι).powerset,g τ1:=by
  set n:=(LT.e9 k (B i)).length with hn
  set m:=(zM Z).length with hmdef
  set nm:=d7 Z (un i.val) with hnmdef
  set mv:=LT.e9 k (B i) with hmv
  have hι:ι< 2 ^ n:=(LT.z7 k (B i) ι).mp hv
  have F1:=a8z n m hm nm ι hι
  have F2T:∀ x∈ mTg m ι nm,x< n∧ ¬ mv.getD x 0< k:=by
    intro x hx
    simp only [mTg,mem_filter,mem_range,Bool.and_eq_true,Bool.not_eq_true'] at hx
    have hxn:x< n:=by
      by_contra h
      have:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hι (Nat.pow_le_pow_right (by omega) (by omega)))
        (i:=x)
      rw [this] at hx; exact absurd hx.2.1 (by simp)
    have h2:=hNm x
    rw [hx.2.2] at h2
    exact ⟨hxn,fun h=>of_decide_eq_false h2.symm ⟨hxn,h⟩⟩
  have F2N:∀ x∈ mNm m ι nm,x< n∧ mv.getD x 0< k:=by
    intro x hx
    simp only [mNm,mem_filter,mem_range,Bool.and_eq_true] at hx
    have h2:=hNm x
    rw [hx.2.2] at h2
    have:=of_decide_eq_true h2.symm
    exact this
  have hsplitι:=LT.a0o k B i ι (mTg m ι nm) (mNm m ι nm) F1
    (fun x hx=>by rcases mem_union.mp hx with h | h; exact (F2T x h).1; exact (F2N x h).1)
    (fun x hx=>(F2T x hx).2) (fun x hx=>(F2N x hx).2)
  have hμ:∀ Y⊆ mNm m ι nm,LT.c8 k B i (f0 (mTg m ι nm∪ Y))= LT.a1t k (B i) (mTg m ι nm) ∧
      LT.g6 k B i (f0 (mTg m ι nm∪ Y))= LT.l7 k (B i) Y:=fun Y hY =>
    LT.a0o k B i _ (mTg m ι nm) Y (k9 _)
      (fun x hx=>by rcases mem_union.mp hx with h | h; exact (F2T x h).1; exact (F2N x (hY h)).1)
      (fun x hx=>(F2T x hx).2) (fun x hx=>(F2N x (hY hx)).2)
  have hsj:(mTg m ι nm).filter (fun x=>w5 Z (un i.val) (un j.val) x) =
      (mTg m ι nm).filter (fun x=>mv.getD x 0∈ B j):=by
    refine Finset.filter_congr fun x hx=>?_
    rw [hSj x,decide_eq_true_iff]
    have:=F2T x hx
    exact ⟨fun h=>h.2.2,fun h=>⟨this.1,this.2,h⟩⟩
  refine ⟨fun Y hY=>?_,fun g=>?_⟩
  · have hνs:=LT.a0o k B i _ ((mTg m ι nm).filter (fun x=>w5 Z (un i.val) (un j.val) x))
      (mNm m ι nm \ Y) (k9 _)
      (fun x hx=>by
        rcases mem_union.mp hx with h | h
        · exact (F2T x (mem_filter.mp h).1).1
        · exact (F2N x (mem_sdiff.mp h).1).1)
      (fun x hx=>(F2T x (mem_filter.mp hx).1).2) (fun x hx=>(F2N x (mem_sdiff.mp hx).1).2)
    refine ⟨(LT.z7 k (B i) _).mpr (a2b _ _ fun x hx=>mem_range.mpr ?_),?_,
      (LT.z7 k (B i) _).mpr (a2b _ _ fun x hx=>mem_range.mpr ?_),?_,?_⟩
    · rcases mem_union.mp hx with h | h
      · exact (F2T x h).1
      · exact (F2N x (hY h)).1
    · rw [(hμ Y hY).1,hsplitι.1]
    · rcases mem_union.mp hx with h | h
      · exact (F2T x (mem_filter.mp h).1).1
      · exact (F2N x (mem_sdiff.mp h).1).1
    · rw [hνs.1,hsplitι.1,LT.b18,hsj]
    · rw [hνs.2,hsplitι.2,(hμ Y hY).2,
        LT.a92 k (B i) _ _ hY (fun x hx=>(F2N x hx).1)]
  · rw [hsplitι.2,← LT.b1b k (B i) (mNm m ι nm) (fun x hx=>(F2N x hx).1)
      (fun x hx=>(F2N x hx).2) g]
    exact Finset.sum_congr rfl fun Y hY=>by rw [(hμ Y (mem_powerset.mp hY)).2]
lemma b91 (hm:(LT.e9 k (B i)).length≤ (zM Z).length)
    (hNm:∀ x,d7 Z (un i.val) x =
      decide (x< (LT.e9 k (B i)).length∧ (LT.e9 k (B i)).getD x 0< k))
    (ι:ℕ) (hι:ι< 2 ^ (zM Z).length) (hnv:¬ LT.f6 (Dec.a9 k (B i)) ι.bits= []) :
    ∀ Y ⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
      ¬ LT.f6 (Dec.a9 k (B i)) (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)).bits= []:=by
  intro Y _ hμ
  rw [LT.z7] at hnv hμ
  obtain ⟨x,hxn,hx⟩:∃ x,(LT.e9 k (B i)).length≤ x∧ ι.testBit x= true:=by
    by_contra h
    push_neg at h
    exact hnv (Nat.lt_pow_two_of_testBit ι fun x hx=>by
      cases hb:ι.testBit x
      · rfl
      · exact absurd hb (h x hx))
  have hxm:x< (zM Z).length:=by
    by_contra h
    have:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hι (Nat.pow_le_pow_right (by omega) (by omega)))
      (i:=x)
    rw [this] at hx; exact absurd hx (by simp)
  have hxT:x∈ mTg (zM Z).length ι (d7 Z (un i.val)):=by
    simp only [mTg,mem_filter,mem_range,hxm,hx,true_and,hNm x]
    simp [show ¬ x< (LT.e9 k (B i)).length by omega]
  have hb:=k9 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y) x
  rw [decide_eq_true (mem_union_left _ hxT)] at hb
  have:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hμ (Nat.pow_le_pow_right (by omega) hxn)) (i:=x)
  rw [this] at hb
  exact absurd hb (by simp)
end
end asmP30
section asmP31
open Finset Turing PEqualNP.Library Lib.Machines Lib.Universal
lemma b4p (x:Bool) (b:List Bool) :
    Dec.z5 (x::b)= (if x then [0] else [])++(Dec.z5 b).map (·+ 1):=by
  unfold Dec.z5
  rw [List.length_cons,List.range_succ_eq_map,List.filter_cons,List.filter_map]
  cases x <;> simp [Function.comp_def]
lemma a6d:∀ (b l:List Bool),l.length= b.length →
    v0 b l= (Dec.z5 b).map (fun q=>l.getD q false)
  | [],l,_=>by simp [v0,Dec.z5]
  | x::b,[],h=>by simp at h
  | x :: b, y :: l, h => by
    rw [v0,List.tail_cons,b4p,a6d b l (by simpa using h),List.map_append,List.map_map]
    cases x <;> simp [Function.comp_def]
lemma a8m (wU g:List Bool) (h:g.length≤ wU.length) (x:ℕ) :
    (g4 wU g).getD x false= if x< g.length then g.getD x false else false:=by
  rw [g4,k7]
  by_cases hx:x< g.length
  · rw [if_pos hx,List.getD_eq_getElem _ _ (by simp; omega),List.getElem_take,
      List.getElem_append_left hx,List.getD_eq_getElem _ _ hx]
  · rw [if_neg hx]
    by_cases hw:x< wU.length
    · rw [List.getD_eq_getElem _ _ (by simp [q7]; omega),List.getElem_take,
        List.getElem_append_right (by omega)]
      simp [f3]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
lemma b1k (b:List Bool) (q:ℕ) (hq:q∈ Dec.z5 b):q< b.length:=by
  unfold Dec.z5 at hq
  exact List.mem_range.mp (List.mem_of_mem_filter hq)
lemma a39 (k q:ℕ) (hq:q< k+ Dec.b6 k) :
    (Dec.layout k).getD q 0< k↔ q< k:=by
  unfold Dec.layout
  by_cases h:q< k
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem _ _ (show q< (List.range k).length by simpa using h),h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have hq':q - (List.range k).length< ((Dec.pairs k).map (Dec.tag k)).length:=by
      simp [Dec.s8]; omega
    rw [List.getD_eq_getElem _ _ hq',List.getElem_map]
    have:=Dec.a13 k ((Dec.pairs k)[q - (List.range k).length]'(by simpa using hq'))
    simp only [h,iff_false,not_lt]
    exact this
lemma a9w (k:ℕ) (S:Finset ℕ) (q:ℕ) (hq:q< k+ Dec.b6 k) :
    (Dec.a9 k S).getD q false= decide ((Dec.layout k).getD q 0∈ S):=by
  have hl:q< (Dec.layout k).length:=by rw [Dec.a44]; exact hq
  rw [Dec.a9,List.getD_eq_getElem _ _ (by simpa using hl),List.getElem_map,
    List.getD_eq_getElem _ _ hl]
lemma a8i (k:ℕ) (S:Finset ℕ) (x:ℕ) (hx:x< (Dec.z5 (Dec.a9 k S)).length) :
    (LT.e9 k S).getD x 0= (Dec.layout k).getD ((Dec.z5 (Dec.a9 k S)).getD x 0) 0:=by
  rw [LT.b1d,List.getD_eq_getElem _ _ (by simpa using hx),List.getElem_map,
    List.getD_eq_getElem _ _ hx]
section
variable (k w:ℕ) (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  (t:ℕ) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
lemma b71:zPG (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) =
    Dec.p5 (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B):=by
  simp only [zPG,pf,Dec.gZ,a5]
lemma b70 :
    let PG:=Dec.p5 (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)
    pf 0 PG= un (2^(w+1))∧ pf 1 PG= un k∧ pf 2 PG= un w∧ pf 3 PG= un (Dec.b6 k) ∧
      pf 9 PG= un (t+1)∧ pf 10 PG= un (Dec.i8 t) ∧
      pr 11 PG= (List.finRange (t+1)).flatMap (Dec.j5 k t par B):=by
  intro PG
  simp only [PG,Dec.a45,pf,pr,a5,and_self]
lemma a1s :
    let Z:=Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)
    zP Z= un (2^(w+1))∧ zM Z= [true]++un w∧ zN Z= un (t+1) ∧
      y1 Z= un k++f3 (un (Dec.b6 k)) ∧
      ∀ i : Fin (t+1), g7 Z (un i.val) = Dec.a9 k (B i) ∧
        b20 Z (un i.val)= Dec.bits (Dec.i8 t) (par i).val:=by
  intro Z
  obtain ⟨h0,h1,h2,h3,h9,h10,h11⟩:=b70 k w E P H rows t par B
  have hZ:zPG Z= Dec.p5 (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B) :=
    b71 k w E P H rows t par B
  refine ⟨by rw [zP,hZ,h0],by rw [zM,hZ,h2],by rw [zN,hZ,h9],
    by rw [y1,hZ,h1,h3],fun i=>?_⟩
  have hrec:a7r Z (un i.val)= Dec.j5 k t par B i:=by
    rw [a7r,hZ,h10,h1,h3,h11]
    rw [l8 (Dec.j5 k t par B) _ (Dec.a0n k t par B)
      (List.finRange (t+1)) i.val (by rw [List.length_finRange]; exact i.isLt) _ _ (by simp) (b4 _),
      List.getElem_finRange]
    rfl
  have hb:(Dec.bits (Dec.i8 t) (par i).val).length= (un (Dec.i8 t)).length:=by
    rw [Dec.k2,b4]
  refine ⟨?_,?_⟩
  · rw [g7,hZ,h10,hrec,Dec.j5,i6,← hb,List.drop_left' rfl]
  · rw [b20,hZ,h10,hrec,Dec.j5,k7,← hb,List.take_left' rfl]
lemma b1v :
    (zP (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))).length =
      2 ^ (zM (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))).length:=by
  obtain ⟨hP,hM,-⟩:=a1s k w E P H rows t par B
  rw [hP,hM]
  simp [b4]
lemma b5m (i j:Fin (t+1)) :
    (g7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un i.val)).length =
      (g7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un j.val)).length:=by
  obtain ⟨-,-,-,-,hB⟩:=a1s k w E P H rows t par B
  rw [(hB i).1,(hB j).1,Dec.m2,Dec.m2]
lemma b32 (i j:Fin (t+1)) :
    k1 (a1 (un i.val) (a1 (un j.val)
      (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))))= [] ↔
      ¬ (i< j∧ par j= i):=by
  obtain ⟨-,-,hN,-,hB⟩:=a1s k w E P H rows t par B
  simp only [k1,a5]
  rw [hN,(hB j).2,a8l _ _ (by omega)]
  have hfw:List.map (fun h=>i.val.testBit h) (List.range ((t+1).log2+ 1)) =
      Dec.bits (Dec.i8 t) i.val:=rfl
  rw [hfw,a6w _ _ (by rw [Dec.k2,Dec.k2]),i6,b4,un,
    List.drop_replicate]
  unfold sel
  by_cases hij:i< j
  · have hne:List.replicate (j.val - i.val) true≠ []:=by
      have:=Fin.lt_def.mp hij; simp; omega
    rw [if_neg hne]
    have hbits:Dec.bits (Dec.i8 t) (par j).val= Dec.bits (Dec.i8 t) i.val↔ par j= i:=by
      constructor
      · intro h
        have h1:=congrArg Dec.a1a h
        rw [Dec.a09 _ _ (Dec.u5 t _ (par j).isLt),
          Dec.a09 _ _ (Dec.u5 t _ i.isLt)] at h1
        exact Fin.ext h1
      · intro h; rw [h]
    by_cases hp:par j= i
    · rw [if_pos (hbits.mpr hp)]; simp [hij,hp]
    · rw [if_neg (fun h=>hp (hbits.mp h))]; simp [hp]
  · have he:List.replicate (j.val - i.val) true= []:=by
      have:¬ (i.val< j.val):=fun h=>hij (Fin.lt_def.mpr h)
      simp; omega
    rw [if_pos he]
    simp [hij]
lemma a5c (hdec:Dec.f7 k E rows w t par B) (i:Fin (t+1)) :
    (LT.e9 k (B i)).length ≤
      (zM (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B))).length:=by
  obtain ⟨-,hM,-⟩:=a1s k w E P H rows t par B
  rw [hM]
  have hc:=(hdec.2.2.1 i).2
  have hsub:(LT.e9 k (B i)).toFinset⊆ B i:=fun v hv =>
    ((LT.b0q k (B i) v).mp (List.mem_toFinset.mp hv)).2
  have h1:=Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (LT.a40 k (B i))] at h1
  simp only [List.length_append,List.length_singleton,b4]
  omega
lemma a75 (k m q:ℕ) (hq:q< k+ m) :
    (un k++f3 (un m)).getD q false= decide (q< k):=by
  by_cases h:q< k
  · rw [List.getD_append _ _ _ _ (by simpa [b4] using h)]
    simp [un,h]
  · rw [List.getD_append_right _ _ _ _ (by simp [b4]; omega)]
    simp only [b4,f3,un,List.map_replicate]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp [h]
lemma a9m (hdec:Dec.f7 k E rows w t par B) (i:Fin (t+1)) (x:ℕ) :
    d7 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un i.val) x =
      decide (x< (LT.e9 k (B i)).length∧ (LT.e9 k (B i)).getD x 0< k):=by
  have hm:=a5c k w E P H rows t par B hdec i
  obtain ⟨-,-,-,hNames,hB⟩:=a1s k w E P H rows t par B
  have hlen:(un k++f3 (un (Dec.b6 k))).length= (Dec.a9 k (B i)).length:=by
    simp [b4,q7,Dec.m2]
  unfold d7
  rw [(hB i).1,hNames,a6d _ _ hlen,
    a8m _ _ (by rw [List.length_map,← LT.z0]; exact hm),List.length_map,
    ← LT.z0]
  by_cases hx:x< (LT.e9 k (B i)).length
  · have hx' : x < (Dec.z5 (Dec.a9 k (B i))).length := by rwa [← LT.z0]
    have hq:=b1k (Dec.a9 k (B i)) ((Dec.z5 (Dec.a9 k (B i))).getD x 0)
      (by rw [List.getD_eq_getElem _ _ hx']; exact List.getElem_mem hx')
    rw [Dec.m2] at hq
    rw [if_pos hx,List.getD_eq_getElem _ _ (by simpa using hx'),List.getElem_map,
      ← List.getD_eq_getElem _ 0 hx',a75 _ _ _ hq,a8i k (B i) x hx']
    simp only [a39 k _ hq]
    simp [hx]
  · rw [if_neg hx]; simp [hx]
lemma b6c (hdec:Dec.f7 k E rows w t par B) (i j:Fin (t+1)) (x:ℕ) :
    w5 (Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)) (un i.val) (un j.val) x =
      decide (x< (LT.e9 k (B i)).length∧ ¬ (LT.e9 k (B i)).getD x 0< k ∧
        (LT.e9 k (B i)).getD x 0∈ B j):=by
  have hm:=a5c k w E P H rows t par B hdec i
  obtain ⟨-,-,-,hNames,hB⟩:=a1s k w E P H rows t par B
  have hlen:(bwL and (Dec.a9 k (B j)) (v8 (un k++f3 (un (Dec.b6 k))))).length =
      (Dec.a9 k (B i)).length:=by
    rw [t7,Dec.m2,Dec.m2]
  unfold w5
  rw [(hB i).1,(hB j).1,hNames,a6d _ _ hlen,
    a8m _ _ (by rw [List.length_map,← LT.z0]; exact hm),List.length_map,
    ← LT.z0]
  by_cases hx:x< (LT.e9 k (B i)).length
  · have hx' : x < (Dec.z5 (Dec.a9 k (B i))).length := by rwa [← LT.z0]
    have hq:=b1k (Dec.a9 k (B i)) ((Dec.z5 (Dec.a9 k (B i))).getD x 0)
      (by rw [List.getD_eq_getElem _ _ hx']; exact List.getElem_mem hx')
    rw [Dec.m2] at hq
    rw [if_pos hx,List.getD_eq_getElem _ _ (by simpa using hx'),List.getElem_map,
      ← List.getD_eq_getElem _ 0 hx',a21,a19,Dec.m2,
      a9w k (B j) _ hq,a75 _ _ _ hq,a8i k (B i) x hx']
    simp only [a39 k _ hq]
    have hl:(un k++f3 (un (Dec.b6 k))).length= k+ Dec.b6 k:=by
      simp [b4,q7]
    rw [hl]
    by_cases h1:(Dec.z5 (Dec.a9 k (B i))).getD x 0< k <;>
      by_cases h2:(Dec.layout k).getD ((Dec.z5 (Dec.a9 k (B i))).getD x 0) 0∈ B j <;>
      simp only [hx,hq,h1,h2,true_and,and_true,not_true_eq_false,not_false_eq_true,
        and_false,false_and,decide_true,decide_false,Bool.true_and,Bool.and_true,
        Bool.false_and,Bool.and_false,Bool.not_true,Bool.not_false]
  · rw [if_neg hx]; simp [hx]
lemma b6s (hdec:Dec.f7 k E rows w t par B) (i j:Fin (t+1)) :
    let Z:=Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)
    ∀ ι < (zP Z).length, LT.f6 (Dec.a9 k (B i)) ι.bits = [] →
      (∀ Y⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
        LT.f6 (Dec.a9 k (B i)) (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)).bits= [] ∧
        LT.c8 k B i (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))= LT.c8 k B i ι ∧
        LT.f6 (Dec.a9 k (B i)) (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))).bits= [] ∧
        LT.c8 k B i (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) =
          sig B j (LT.c8 k B i ι) ∧
        LT.g6 k B i (f0 ((mTg (zM Z).length ι (d7 Z (un i.val))).filter
          (fun x=>w5 Z (un i.val) (un j.val) x)∪ (mNm (zM Z).length ι (d7 Z (un i.val)) \ Y))) =
          LT.g6 k B i ι \ LT.g6 k B i (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y))) ∧
      ∀ g : Finset (Fin k) → ℕ, (∑ Y ∈ (mNm (zM Z).length ι (d7 Z (un i.val))).powerset,
        g (LT.g6 k B i (f0 (mTg (zM Z).length ι (d7 Z (un i.val)) ∪ Y)))) =
          ∑ τ1∈ (LT.g6 k B i ι).powerset,g τ1 :=
  fun ι _ hv=>b9c B i j _ (a5c k w E P H rows t par B hdec i)
    (a9m k w E P H rows t par B hdec i) (b6c k w E P H rows t par B hdec i j) ι hv
lemma b83 (hdec:Dec.f7 k E rows w t par B) (i:Fin (t+1)) :
    let Z:=Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)
    ∀ ι < (zP Z).length, ¬ LT.f6 (Dec.a9 k (B i)) ι.bits = [] →
      ∀ Y ⊆ mNm (zM Z).length ι (d7 Z (un i.val)),
        ¬ LT.f6 (Dec.a9 k (B i)) (f0 (mTg (zM Z).length ι (d7 Z (un i.val))∪ Y)).bits= [] :=
  fun ι hι hnv=>b91 B i _ (a5c k w E P H rows t par B hdec i)
    (a9m k w E P H rows t par B hdec i) ι
    (by rw [← b1v k w E P H rows t par B]; exact hι) hnv
lemma a7p (hdec:Dec.f7 k E rows w t par B) (i j:Fin (t+1)) (T:List Bool)
    (kt kacc:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ) :
    let Z:=Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)
    (∀ μ< (zP Z).length,val (b5 (zWt Z) (un μ) (b5 (zL Z) (un i.val) T)) =
      if LT.f6 (Dec.a9 k (B i)) μ.bits= [] then
        kacc (LT.c8 k B i μ) (LT.g6 k B i μ) % 2 ^ (zWt Z).length else 0) →
    (∀ κ< (zP Z).length,val (b5 (zWt Z) (un κ) (b5 (zL Z) (un j.val) T)) =
      if LT.f6 (Dec.a9 k (B j)) κ.bits= [] then
        kt (LT.c8 k B j κ) (LT.g6 k B j κ) % 2 ^ (zWt Z).length else 0) →
    (∀ ι',LT.f6 (Dec.a9 k (B i)) ι'.bits= []→ ∀ f:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ,
      (∑ κ∈ range (zP Z).length,if msC (g7 Z (un i.val)) (g7 Z (un j.val)) κ ι' then
        (if LT.f6 (Dec.a9 k (B j)) κ.bits= [] then f (LT.c8 k B j κ) (LT.g6 k B j κ) else 0)
        else 0) =
      ∑ σj ∈ (sig B j E).powerset, ∑ τj ∈ (univ.filter (fun v : Fin k => v.val ∈ B j)).powerset,
        if sig B i σj= LT.c8 k B i ι'∧ τj.filter (fun v=>v.val∈ B i)= LT.g6 k B i ι' then
          f σj τj else 0) →
    ∀ ι < (zP Z).length,
      val (b5 (zWt Z) (un ι) (f4 (a1 (un i.val) (a1 (un j.val) (a1 Z T))))) =
        if LT.f6 (Dec.a9 k (B i)) ι.bits= [] then
          s0 E B kt i j kacc (LT.c8 k B i ι) (LT.g6 k B i ι) % 2 ^ (zWt Z).length else 0 :=
  fun hTi hTj HM ι hι=>b2n E B i j _ T kt kacc
    (fun ι=>LT.f6 (Dec.a9 k (B i)) ι.bits= [])
    (fun κ=>LT.f6 (Dec.a9 k (B j)) κ.bits= [])
    (LT.c8 k B i) (LT.c8 k B j) (LT.g6 k B i) (LT.g6 k B j)
    (b1v k w E P H rows t par B) (b5m k w E P H rows t par B i j) hTi hTj HM
    (b6s k w E P H rows t par B hdec i j) (b83 k w E P H rows t par B hdec i) ι hι
end
end asmP31
section asmP32
open Lib.Universal
section Fin
variable (k w:ℕ) (E P H:Finset (Fin k × Fin k)) (rows:List (Finset (Fin k × Fin k) × Bool))
  (t:ℕ) (par:Fin (t+1)→ Fin (t+1)) (B:Fin (t+1)→ Finset ℕ)
def a0j:List Bool:=Dec.gZ (un (2^(w+1))++false::Dec.a8 k w E P H rows t par B)
abbrev b4z {t:ℕ} (B:Fin (t+1)→ Finset ℕ) (i:Fin (t+1)) (ι:ℕ):Prop :=
  LT.f6 (Dec.a9 k (B i)) ι.bits= []
lemma b3g (hE:∀ e∈ E,e.1< e.2) (hP:∀ e∈ P,e.1< e.2) (hH:∀ e∈ H,e.1< e.2)
    (hd:Dec.f7 k E rows w t par B) :
    ∀ (i j : Fin (t+1)), i < j → par j = i → ∀ (T : List Bool)
      (kacc kt:Finset (Fin k × Fin k)→ Finset (Fin k)→ ℕ),
      T.length= (t+1)* (zL (a0j k w E P H rows t par B)).length →
      (∀ μ< (zP (a0j k w E P H rows t par B)).length,
        val (b5 (zWt (a0j k w E P H rows t par B)) (un μ)
          (b5 (zL (a0j k w E P H rows t par B)) (un i.val) T)) =
        r0 (a0j k w E P H rows t par B) (b4z k B) (LT.c8 k B) (LT.g6 k B) i kacc μ) →
      (∀ μ< (zP (a0j k w E P H rows t par B)).length,
        val (b5 (zWt (a0j k w E P H rows t par B)) (un μ)
          (b5 (zL (a0j k w E P H rows t par B)) (un j.val) T)) =
        r0 (a0j k w E P H rows t par B) (b4z k B) (LT.c8 k B) (LT.g6 k B) j kt μ) →
      ∀ ι < (zP (a0j k w E P H rows t par B)).length,
        val (b5 (zWt (a0j k w E P H rows t par B)) (un ι)
          (f4 (a1 (un i.val) (a1 (un j.val) (a1 (a0j k w E P H rows t par B) T))))) =
        r0 (a0j k w E P H rows t par B) (b4z k B) (LT.c8 k B) (LT.g6 k B) i
          (s0 E B kt i j kacc) ι:=by
  intro i j _ _ T kacc kt _ hTi hTj ι hι
  unfold r0 at hTi hTj ⊢
  exact a7p k w E P H rows t par B hd i j T kt kacc hTi hTj
    (LT.b8u k w E P H rows t par B hE hd i j) ι hι
lemma b0z:Dec.a7f (fun _ E P H rows _ par B=>p3 E P H rows par B)
    (a8a LT.a2o):=by
  intro k w E P H rows t par B hE hP hH hdec hPE s j hs hj
  have hd:s4 E rows par B w:=hdec
  have hM:=Dec.a5r E hE
  have key:=b63 E P H rows par B (a0j k w E P H rows t par B)
    (fun i ι=>LT.f6 (Dec.a9 k (B i)) ι.bits= []) (LT.c8 k B) (LT.g6 k B) w hd
    (Dec.b6 k) hM LT.a2o (LT.c07 k w E P H rows t par B)
    (LT.b6x k w E P H rows t par B hP) (b32 k w E P H rows t par B)
    (fun iU jU T=>a96 iU jU _ T) (LT.b23 k w E P H rows t par B hE hP)
    (b3g k w E P H rows t par B hE hP hH hdec) (LT.b4k k w E P H rows t par B hE hdec)
    hPE s j (Dec.a5y k s hs) hj
  exact key.trans (Dec.a93 k w E P H rows t par B hE hP hH hdec hPE s j hs hj)
end Fin
end asmP32
section asmP33
open Turing PEqualNP.Library Lib.Machines Lib.Universal
def mrW (x:List Bool):ℕ:=(hd (r5 x)).length
def mrPad (x:List Bool):List Bool:=un (2 ^ (mrW x+ 1))++false::x
def a2q (x:List Bool):List Bool × List Bool:=(true::false::x,true::hd (r5 x))
def a2j (y:List Bool):List Bool:=hd y++y
lemma a6u (x:List Bool) (j:ℕ) :
    a2j^[j] (true::false::x)= un (2 ^ j)++false::x:=by
  induction j with
  | zero=>rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    show hd (un (2 ^ j)++false::x)++(un (2 ^ j)++false::x)= _
    rw [a9c,← List.append_assoc,pow_succ,mul_two]
    simp only [un,List.replicate_add]
lemma c08 (x:List Bool):mrW x≤ x.length :=
  (b3h _).trans (a9z _)
lemma mrE {f f':List Bool→ List Bool}
    (h:ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f)
    (e:∀ a,f a= f' a) :
    ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f':=by
  obtain rfl:f= f':=funext e
  exact h
lemma b2g :
    ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) a2j :=
  b8 a2d g5
lemma b2z:ComputableInPolyTime (fun x:List Bool=>x) encodePair a2q :=
  x7 (f:=fun x=>true::false::x) (g:=fun x=>true::hd (r5 x))
    (mrE (b8 (b0 [true,false]) g5) (fun _=>rfl))
    (mrE (b8 (b0 [true]) (a2 z8 a2d)) (fun _=>rfl))
lemma a87 (p:Polynomial ℕ):∃ A,1≤ A∧ ∀ m,p.eval m≤ A* (m+ 1) ^ A:=by
  obtain ⟨a,d,h⟩:=a5x p
  refine ⟨a+ d+ 1,by omega,fun m=>?_⟩
  calc p.eval m ≤ p.eval (m + 1) := a0h p (by omega)
    _≤ a* (m+ 1) ^ d:=h (m+ 1) (by omega)
    _ ≤ (a + d + 1) * (m + 1) ^ (a + d + 1) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
lemma b5g (A B P s1 tg s3 n2 n w L:ℕ) (hA:1≤ A) (hB:1≤ B) (hBP:B≤ P)
    (h1:s1≤ A* P) (hg:tg≤ A* P) (h3:s3≤ A* P) (hn:n+ 2≤ B) (hw:w+ 1≤ B)
    (hL:L≤ B)
    (h2:n2≤ (w+ 1)* (tg+ 2* L+ 3)+ 2* L+ 2* (n+ 2)+ (w+ 1)+ 5) :
    s1+ (2* ((n+ 2)+ (w+ 1))+ 2)+ (n2+ (2* L+ 2)+ s3)≤ (3* A+ 25)* (B* P):=by
  have e1:(w+ 1)* (tg+ 2* L+ 3)≤ B* (A* P+ 2* B+ 3):=Nat.mul_le_mul hw (by omega)
  have e2:B* (A* P+ 2* B+ 3)= A* (B* P)+ 2* (B* B)+ 3* B:=by ring
  have e3:B* B≤ B* P:=Nat.mul_le_mul_left B hBP
  have e4:B≤ B* P:=Nat.le_mul_of_pos_right B (by omega)
  have e5:P≤ B* P:=Nat.le_mul_of_pos_left P (by omega)
  have e6:A* P≤ A* (B* P):=Nat.mul_le_mul_left A e5
  have e7:(3* A+ 25)* (B* P)= 3* (A* (B* P))+ 25* (B* P):=by ring
  rw [e7]
  generalize B* P= Q at *
  generalize A* Q= AQ at *
  generalize A* P= AP at *
  generalize B* B= BB at *
  omega
lemma b5z (A K n w:ℕ) (hK:A+ 1≤ K) :
    K* (2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1)≤ 2 ^ (2* K* (w+ 1))* (n+ 2) ^ (2* K):=by
  have h1:K< 2 ^ K:=Nat.lt_two_pow_self
  have hB1:1≤ 2 ^ (w+ 1)* (n+ 2):=Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2:(2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1)≤ (2 ^ (w+ 1)* (n+ 2)) ^ K :=
    Nat.pow_le_pow_right hB1 hK
  have h3:(2 ^ (w+ 1)* (n+ 2)) ^ K= 2 ^ (K* (w+ 1))* (n+ 2) ^ K:=by
    rw [mul_pow,← pow_mul,mul_comm (w+ 1) K]
  have h4:K+ K* (w+ 1)≤ 2* K* (w+ 1):=by nlinarith
  calc K * (2 ^ (w + 1) * (n + 2)) ^ (A + 1) ≤ 2 ^ K * (2 ^ (w + 1) * (n + 2)) ^ K :=
        Nat.mul_le_mul h1.le h2
    _= 2 ^ (K+ K* (w+ 1))* (n+ 2) ^ K:=by rw [h3,← mul_assoc,← pow_add]
    _ ≤ 2 ^ (2 * K * (w + 1)) * (n + 2) ^ (2 * K) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h4)
          (Nat.pow_le_pow_right (by omega) (by omega))
lemma mr_fpt (G:List Bool→ List Bool)
    (hG:ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) G) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : List Bool, Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ((G (mrPad x)).map M.outputAlphabet.invFun))
        (2 ^ (c* (mrW x+ 1))* (x.length+ 2) ^ c)):=by
  classical
  obtain ⟨c1⟩:=b2z
  obtain ⟨cg⟩:=b2g
  obtain ⟨c3⟩:=hG
  obtain ⟨A1,hA1,hp1⟩:=a87 c1.time
  obtain ⟨Ag,hAg,hpg⟩:=a87 cg.time
  obtain ⟨A3,hA3,hp3⟩:=a87 c3.time
  let e₀:Bool→ cg.tm.Γ cg.tm.k₀:=cg.inputAlphabet.invFun
  let d₀:cg.tm.Γ cg.tm.k₀→ Bool:=cg.inputAlphabet
  let e₁:cg.tm.Γ cg.tm.k₁→ Bool:=cg.outputAlphabet
  let Mit:FinTM2:=Iter.a0a cg.tm e₀ d₀ e₁
  let φ2:Mit.Γ Mit.k₁→ c3.tm.Γ c3.tm.k₀:=fun b=>c3.inputAlphabet.invFun b
  let d2:Option (c3.tm.Γ c3.tm.k₀):=some (c3.inputAlphabet.invFun true)
  let M2:FinTM2:=comp Mit c3.tm φ2 d2
  let φ1:c1.tm.Γ c1.tm.k₁→ M2.Γ M2.k₀:=fun s=>c1.outputAlphabet s
  let d1:Option (M2.Γ M2.k₀):=some (Sum.inl true:Bool ⊕ Bool)
  let M1:FinTM2:=comp c1.tm M2 φ1 d1
  let A:=A1+ Ag+ A3
  let K:=3* A+ 25
  have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (cg.tm.Γ cg.tm.k₁)),
      s≤ cg.time.eval z.length ∧
      (flip bind (TM2.step cg.tm.m))^[s] (some (initList cg.tm (z.map e₀))) =
        some (haltList cg.tm m)∧ m.map e₁= a2j z:=by
    intro z
    refine ⟨(cg.outputsFun z).steps,List.map cg.outputAlphabet.invFun (a2j z),
      (cg.outputsFun z).steps_le_m,(cg.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (a2j z)]
    exact List.map_congr_left fun y _=>cg.outputAlphabet.right_inv y
  have key:∀ x:List Bool,∃ n,n≤ 2 ^ (2* K* (mrW x+ 1))* (x.length+ 2) ^ (2* K) ∧
      (flip bind (TM2.step M1.m))^[n] (some (initList M1 (x.map c1.inputAlphabet.invFun))) =
        some (haltList M1 ((G (mrPad x)).map c3.outputAlphabet.invFun)):=by
    intro x
    let n:=x.length
    let w:=mrW x
    let L:=2 ^ (w+ 1)+ 1+ n
    have hw:w≤ n:=c08 x
    have hpadlen:(mrPad x).length= L:=by
      simp only [mrPad,List.length_append,b4,List.length_cons,L,n,w]; omega
    have r1:=c1.outputsFun x
    have hL:∀ j≤ (true::hd (r5 x)).length,
        (a2j^[j] (true::false::x)).length≤ L:=by
      intro j hj
      rw [a6u]
      have hj':j≤ w+ 1:=hj
      have:2 ^ j≤ 2 ^ (w+ 1):=Nat.pow_le_pow_right (by norm_num) hj'
      simp only [List.length_append,b4,List.length_cons,L,n]
      omega
    obtain ⟨n2,hn2,h2run⟩:=Iter.a4l e₀ d₀ e₁ a2j cg.time
      (fun a=>cg.inputAlphabet.right_inv a) hrun (true::false::x) (true::hd (r5 x))
      L hL
    have hiter:a2j^[(true::hd (r5 x)).length] (true::false::x)= mrPad x :=
      a6u x (w+ 1)
    rw [hiter] at h2run
    have r3:=c3.outputsFun (mrPad x)
    obtain ⟨n23,hn23,-,h23⟩:=a6b φ2 d2 (fun h=>by simp [d2] at h)
      (encodePair (a2q x)) (mrPad x) ((G (mrPad x)).map c3.outputAlphabet.invFun)
      n2 r3.steps h2run r3.evals_in_steps
    have hφ1:((encodePair (a2q x)).map c1.outputAlphabet.invFun).map φ1 =
        encodePair (a2q x):=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (encodePair (a2q x))]
      exact List.map_congr_left fun y _=>c1.outputAlphabet.right_inv y
    rw [← hφ1] at h23
    obtain ⟨nt,hnt,-,ht⟩:=a6b φ1 d1 (fun h=>by simp [d1] at h)
      (x.map c1.inputAlphabet.invFun) ((encodePair (a2q x)).map c1.outputAlphabet.invFun)
      ((G (mrPad x)).map c3.outputAlphabet.invFun) r1.steps n23 r1.evals_in_steps h23
    refine ⟨nt,?_,ht⟩
    have hlen1:((encodePair (a2q x)).map c1.outputAlphabet.invFun).length =
        (n+ 2)+ (w+ 1):=by
      simp only [List.length_map,a2q,r8,List.length_cons,n,w,mrW]
    have hnt':nt≤ r1.steps+ (2* ((n+ 2)+ (w+ 1))+ 2)+ n23:=by omega
    have hn23':n23≤ n2+ (2* L+ 2)+ r3.steps:=by
      have e:List.length (α:=Mit.Γ Mit.k₁) (mrPad x)= L:=hpadlen
      omega
    let B:=2 ^ (w+ 1)* (n+ 2)
    have hE2:2≤ 2 ^ (w+ 1):=by
      calc 2 = 2 ^ 1 := rfl
        _≤ 2 ^ (w+ 1):=Nat.pow_le_pow_right (by norm_num) (by omega)
    have hEw:w+ 1< 2 ^ (w+ 1):=Nat.lt_two_pow_self
    have hBexp:B= 2 ^ (w+ 1)* n+ 2* 2 ^ (w+ 1):=by simp only [B]; ring
    have hEn:n≤ 2 ^ (w+ 1)* n:=Nat.le_mul_of_pos_left n (by omega)
    have hB1:1≤ B:=by omega
    have hBn:n+ 2≤ B:=by omega
    have hBw:w+ 1≤ B:=by omega
    have hBL:L+ 1≤ B:=by simp only [L]; omega
    let P:=B ^ A
    have hBP:B≤ P:=Nat.le_self_pow (by omega) B
    have hpow:∀ (Ai m:ℕ),Ai≤ A→ m+ 1≤ B→ Ai* (m+ 1) ^ Ai≤ A* P:=by
      intro Ai m hAi hm
      exact Nat.mul_le_mul hAi ((Nat.pow_le_pow_left hm Ai).trans
        (Nat.pow_le_pow_right (by omega) hAi))
    have b1:r1.steps≤ A* P:=r1.steps_le_m.trans ((hp1 _).trans
      (hpow A1 n (by omega) (by omega)))
    have bg:cg.time.eval L≤ A* P:=(hpg L).trans (hpow Ag L (by omega) hBL)
    have b3':Polynomial.eval (mrPad x).length c3.time≤ A* P:=by
      rw [hpadlen]; exact (hp3 L).trans (hpow A3 L (by omega) hBL)
    have b3:r3.steps≤ A* P:=r3.steps_le_m.trans b3'
    have hn2':n2≤ (w+ 1)* (cg.time.eval L+ 2* L+ 3)+ 2* L+ 2* (n+ 2) +
        (w+ 1)+ 5:=by
      have e:(true::hd (r5 x)).length= w+ 1:=rfl
      have e':(true::false::x).length= n+ 2:=rfl
      rw [e,e'] at hn2
      exact hn2
    have hA:1≤ A:=by omega
    have:=b5g A B P r1.steps (cg.time.eval L) r3.steps n2 n w L hA hB1 hBP b1 bg b3
      hBn hBw (by omega) hn2'
    have hBP':B* P= B ^ (A+ 1):=by simp only [P]; rw [pow_succ,mul_comm]
    have hfin:=b5z A K n w (by omega)
    calc nt ≤ r1.steps + (2 * ((n + 2) + (w + 1)) + 2) + n23 := hnt'
      _≤ r1.steps+ (2* ((n+ 2)+ (w+ 1))+ 2)+ (n2+ (2* L+ 2)+ r3.steps):=by omega
      _≤ K* (B* P):=this
      _= K* (2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1):=by rw [hBP']
      _≤ _:=hfin
  let Mx:Turing.TM2ComputableAux Bool Bool:=⟨M1,c1.inputAlphabet,c3.outputAlphabet⟩
  obtain ⟨M',hfin,htrans⟩:=b0x Mx
  refine ⟨M',2* K,hfin,fun x=>htrans x (G (mrPad x)) _ ?_⟩
  exact { steps := Classical.choose (key x)
          evals_in_steps:=(Classical.choose_spec (key x)).2
          steps_le_m:=(Classical.choose_spec (key x)).1 }
end asmP33
section
open Lib.Universal
lemma asmMid:∃ mid:List Bool→ List Bool,a4 mid ∧
    Dec.a7f (fun _ E P H rows _ par B=>p3 E P H rows par B) mid :=
  ⟨a8a LT.a2o,b5b LT.b4q,b0z⟩
lemma asmTot:Dec.b1n (fun _ E P H rows _ par B=>p3 E P H rows par B) :=
  fun _ w E P H rows _ par B hE hP hH hd s j _ _=>a3o E P H rows par B w hE hP hH hd s j
lemma asm_mrW (k w:Nat) (E P H:Finset (Fin k × Fin k))
    (rows:List (Finset (Fin k × Fin k) × Bool)) (t:Nat) (par:Fin (t+1)→ Fin (t+1))
    (B:Fin (t+1)→ Finset Nat):mrW (Dec.a8 k w E P H rows t par B)= w:=by
  simp only [mrW,Dec.a8,Dec.treeword,List.append_assoc,Dec.a4o,List.cons_append,
    a61,a9c,b4]
end
end PEqualNP.Outside.L_lib_1048
theorem PEqualNP.Outside.L_lib_1048 : (let header := fun z : Nat => List.replicate z true ++ [false]
let pairs := fun n : Nat => (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
let bits := fun (width value : Nat) => (List.range width).map (fun h => value.testBit h)
∃ (M : Turing.TM2ComputableAux Bool Bool) (c : Nat), (∀ i, Finite (M.tm.Γ i)) ∧
∀ (k w : Nat) (E P H : Finset (Fin k × Fin k)) (rows : List (Finset (Fin k × Fin k) × Bool)),
  (∀ e ∈ E, e.1 < e.2) → (∀ e ∈ P, e.1 < e.2) → (∀ e ∈ H, e.1 < e.2) →
  let ends := fun e : Fin k × Fin k => ({e.1,e.2} : Finset (Fin k))
  let valid := fun Q : Finset (Fin k × Fin k) => Q ⊆ E ∧
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)
  let signed := fun Q : Finset (Fin k × Fin k) =>
    ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : Int) -
      ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : Int)
  let together := fun e f => ∃ Q, valid Q ∧ e ∈ Q ∧ f ∈ Q ∧ signed Q ≠ 0
  let tag := fun e : Fin k × Fin k => k+e.1.val*k+e.2.val
  let vertices := (Finset.range k) ∪ E.image tag
  let layout := List.range k ++ (pairs k).map tag
  let decomp := fun (width t : Nat) (par : Fin (t+1) → Fin (t+1))
      (B : Fin (t+1) → Finset Nat) =>
    par 0 = 0 ∧ (∀ i, i ≠ 0 → par i < i) ∧
    (∀ i, B i ⊆ vertices ∧ (B i).card ≤ width+1) ∧
    (∀ v ∈ vertices, ∃ a, v ∈ B a ∧ ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i)) ∧
    (∀ e ∈ E, (∃ i, tag e ∈ B i ∧ e.1.val ∈ B i) ∧ (∃ i, tag e ∈ B i ∧ e.2.val ∈ B i)) ∧
    ∀ e ∈ E, ∀ f ∈ E, e ≠ f → together e f → ∃ i, tag e ∈ B i ∧ tag f ∈ B i
  let treeword := fun (t : Nat) (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset Nat) =>
    header (t+1) ++ (List.finRange (t+1)).flatMap (fun i =>
      bits ((t+1).log2+1) (par i).val ++ layout.map (fun v => decide (v ∈ B i)))
  ∀ (t : Nat) (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset Nat), decomp w t par B →
  let mask := fun A : Finset (Fin k × Fin k) => (pairs k).map (fun e => decide (e ∈ A))
  let x := header k ++ header w ++ mask E ++ mask P ++ mask H ++ header rows.length ++
    rows.flatMap (fun r => r.2 :: mask r.1) ++ treeword t par B
  let score := fun Q : Finset (Fin k × Fin k) => (rows.filter
    (fun r => decide (decide ((Q ∩ r.1).Nonempty) = r.2))).length
  let count := fun s j : Nat => (E.powerset.filter (fun Q =>
    valid Q ∧ P ⊆ Q ∧ Disjoint Q H ∧ Q.card = s ∧ score Q = j)).card
  let out := (List.range (k/2+1)).flatMap (fun s => (List.range (rows.length+1)).flatMap
    (fun j => bits ((pairs k).length+1) (count s j)))
  Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
    (some (out.map M.outputAlphabet.invFun)) (2^(c*(w+1))*(x.length+2)^c))) := by
  intro header pairs bits
  obtain ⟨mid,hmc,hmid⟩:=L_lib_1048.asmMid
  obtain ⟨M,c,hfin,h⟩:=L_lib_1048.mr_fpt (L_lib_1048.Dec.G mid) (L_lib_1048.Dec.G_cpt mid hmc)
  refine ⟨M,c,hfin,?_⟩
  intro k w E P H rows hE hP hH ends valid signed together tag vertices layout decomp treeword t par B
    hdec mask x score count out
  have hw:L_lib_1048.mrW x= w:=L_lib_1048.asm_mrW k w E P H rows t par B
  have hout:L_lib_1048.Dec.G mid (L_lib_1048.mrPad x)= out:=by
    rw [L_lib_1048.mrPad,hw]
    exact L_lib_1048.Dec.G_spec mid _ L_lib_1048.asmTot hmid k w E P H rows hE hP hH t par B hdec
  have h1:=h x
  rw [hw,hout] at h1
  exact h1
