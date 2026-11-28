import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32050
namespace Lib
abbrev CPTs (f:List Bool → List Bool):Prop:=PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
end Lib
section
namespace Lib.Machines
open Turing
theorem d43 {σ : Type} (f : σ → Option σ) (n:ℕ) :
    (flip bind f)^[n] none=none:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply];exact ih
theorem d59 {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h:∀ c c',f c=some c' → g (emb c)=some (emb c')) :
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
      rw [e,d43] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind f (some a)=some c:=hfa
      have e':flip bind g (some (emb a))=some (emb c):=h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab
section pushes
variable {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
def pushes:TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q=>pushes q+1
  | .peek _ _ q=>pushes q
  | .pop _ _ q=>pushes q
  | .load _ q=>pushes q
  | .branch _ q₁ q₂=>max (pushes q₁) (pushes q₂)
  | .goto _=>0
  | .halt=>0
theorem d58 (q:TM2.Stmt Γ Λ σ) (v : σ) (S:∀ k,List (Γ k)) (k:K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length+pushes q:=by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux,pushes]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [Function.update_self,List.length_cons];omega
    · rw [Function.update_of_ne h];omega
  | peek k' f q ih=>exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux,pushes]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [Function.update_self,List.length_tail];omega
    · rw [Function.update_of_ne h]
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux,pushes]
    cases f v
    · exact (ih₂ v S).trans (by have:=le_max_right (pushes q₁) (pushes q₂);omega)
    · exact (ih₁ v S).trans (by have:=le_max_left (pushes q₁) (pushes q₂);omega)
  | goto f=>simp [TM2.stepAux,pushes]
  | halt=>simp [TM2.stepAux,pushes]
end pushes
noncomputable def maxPush (tm:FinTM2):ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l=>pushes (tm.m l)
theorem d86 (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h:TM2.step tm.m c=some c') (k:tm.K) :
    (c'.stk k).length ≤ (c.stk k).length+maxPush tm:=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    refine (d58 _ _ _ _).trans ?_
    have:pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f:=fun l=>pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this
theorem d67 (tm:FinTM2) (k:tm.K) :
    ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a)=some b →
      (b.stk k).length ≤ (a.stk k).length+maxPush tm * n:=by
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
      rw [e,d43] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind (TM2.step tm.m) (some a)=some c:=hfa
      rw [e] at hab
      have h1:=ih c b hab
      have h2:=d86 tm a c hfa k
      rw [Nat.mul_succ];omega
theorem d4 (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold initList
  congr 1
  funext k
  by_cases h:k=tm.k₀
  · subst h;simp
  · simp [h]
theorem d5 (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold haltList
  congr 1
  funext k
  by_cases h:k=tm.k₁
  · subst h;simp
  · simp [h]
theorem d37 (p:Polynomial ℕ) {x y:ℕ} (h:x ≤ y):p.eval x ≤ p.eval y:=by
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
def d60:List Bool → TM2.Stmt (fun _:Unit=>Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _=>a) (d60 l)
def d3 (l:List Bool):Unit → TM2.Stmt (fun _:Unit=>Bool) Unit Bool :=
  fun _ => .pop () (fun _ o=>o.isSome)
    (.branch (fun s=>s)
      (.load (fun _=>false) (.goto fun _=>()))
      (d60 l.reverse))
def d20 (l:List Bool):FinTM2 where
  K:=Unit
  k₀:=()
  k₁:=()
  Γ _:=Bool
  Λ := Unit
  main:=()
  σ := Bool
  initialState:=false
  m:=d3 l
abbrev CLCfg:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
theorem d17 (S T:List Bool) :
    Function.update (fun _:Unit=>S) () T=fun _=>T:=by
  funext k
  simp
theorem d42 (l:List Bool) (v:Bool) (S:List Bool) :
    TM2.stepAux (d60 l) v (fun _:Unit=>S) =
      (⟨none,v,fun _=>l.reverse++S⟩:CLCfg):=by
  induction l generalizing S with
  | nil=>rfl
  | cons a l ih =>
    simp only [d60,TM2.stepAux]
    rw [d17,ih]
    simp
theorem d64 (l:List Bool) (x:Bool) (a:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>x :: a⟩:CLCfg) =
      some ⟨some (),false,fun _=>a⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp
theorem d76 (l:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>[]⟩:CLCfg) =
      some ⟨none,false,fun _=>l⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  rw [d42]
  simp
theorem d63 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (⟨some (),false,fun _=>a⟩:CLCfg)) =
      some ⟨none,false,fun _=>l⟩:=by
  induction a with
  | nil=>exact d76 l
  | cons x a ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d3 l))
        (some (⟨some (),false,fun _=>x :: a⟩:CLCfg)) =
        some ⟨some (),false,fun _=>a⟩:=d64 l x a
    rw [e,ih]
theorem d75 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (initList (d20 l) a))=some (haltList (d20 l) l):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (d3 l)))^[a.length+1]
    (some c)) (d4 (d20 l) a)).trans
    (Eq.trans ?_ (congrArg some (d5 (d20 l) l)).symm)
  show (flip bind (TM2.step (d3 l)))^[a.length+1]
    (some (⟨some (),false,Function.update (fun _=>[]) () a⟩:CLCfg)) =
    some (⟨none,false,Function.update (fun _=>[]) () l⟩:CLCfg)
  rw [d17,d17]
  exact d63 l a
theorem d11 (l:List Bool) :
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
variable {ι : Type} [DecidableEq ι] {β : ι → Type}
theorem d51 (E:∀ i,β i) {a b c : ι} (hab:a≠b) (hac:a≠c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z:=by
  rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
theorem d50 (E:∀ i,β i) {a b c : ι} (hbc:b≠c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z:=by
  rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Option (M1.K ⊕ M2.K)
abbrev CΓ : CK M1 M2 → Type
  | none=>M2.Γ M2.k₀
  | some (Sum.inl k)=>M1.Γ k
  | some (Sum.inr k)=>M2.Γ k
abbrev CΛ : Type:=M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ : Type:=M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s=>f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
  | .load a q => .load (fun s=>(a s.1,s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s=>Sum.inl (f s.1))
  | .halt => .goto (fun _=>Sum.inr (Sum.inr false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s=>f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .load a q => .load (fun s=>(s.1,a s.2.1,s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s=>Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt
variable (M1 M2)
def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _=>Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map φ))
      (.branch (fun s=>s.2.2.isSome)
        (.push none (fun s=>s.2.2.getD d) (.goto fun _=>Sum.inr (Sum.inr false)))
        (.goto fun _=>Sum.inr (Sum.inr true)))
def tB:Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _=>Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o=>(s.1,s.2.1,o))
      (.branch (fun s=>s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s=>s.2.2.getD d)
          (.goto fun _=>Sum.inr (Sum.inr true)))
        (.goto fun _=>Sum.inr (Sum.inl M2.main)))
def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l=>tr1 (M1.m l)
  | Sum.inr (Sum.inl l)=>tr2 (M2.m l)
  | Sum.inr (Sum.inr false)=>tA M1 M2 φ d
  | Sum.inr (Sum.inr true)=>tB M1 M2 d
def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2 :=
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
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main:=Sum.inl M1.main
    σ := Cσ M1 M2
    initialState:=(M1.initialState,M2.initialState,none)
    Γk₀Fin:=M1.Γk₀Fin
    m:=prog M1 M2 φ d }
variable {M1 M2}
def d49 (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none=>[]
  | some (Sum.inl k)=>S k
  | some (Sum.inr _)=>[]
def d48 (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none=>[]
  | some (Sum.inl _)=>[]
  | some (Sum.inr k)=>S k
theorem d13 (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)) :
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
theorem d12 (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)) :
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
theorem d56 :
    (d49 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
  funext j;rcases j with _ | j | j <;> rfl
theorem d55 :
    (d48 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
  funext j;rcases j with _ | j | j <;> rfl
def emb1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl),(c.var,w),d49 c.stk⟩
def emb2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l=>Sum.inr (Sum.inl l)),(u,c.var,b),d48 c.stk⟩
theorem sim1 (w:M2.σ × Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
    (S:∀ k,List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v,w):Cσ M1 M2) (d49 S)=emb1 w (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
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
theorem sim2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
    (S:∀ k,List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u,v,b):Cσ M1 M2) (d48 S)=emb2 u b (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
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
variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
theorem step1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h:TM2.step M1.m c=some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c)=some (emb1 w c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)
theorem step2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h:TM2.step M2.m c=some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c)=some (emb2 u b c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _=>[])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
theorem st_fst (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁))=l:=by
  unfold st
  rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem st_snd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:=by
  unfold st
  rw [Function.update_of_ne (by simp),Function.update_self]
theorem st_thd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))=u:=by
  unfold st
  rw [Function.update_self]
theorem d66 (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l'=st l' t u :=
  d51 _ (by simp) (by simp) _ _ _ _
theorem d41 (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u :=
  d50 _ (by simp) _ _ _ _
theorem d90 (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u'=st l t u' :=
  Function.update_idem _ _ _
theorem d79 (l:List (M1.Γ M1.k₁)) :
    (st l [] []:∀ k,List (CΓ M1 M2 k)) =
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l:=by
  unfold st
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem st_end (u:List (M2.Γ M2.k₀)) :
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
variable {M1 M2:FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)
abbrev CCfg (M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
theorem d89 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩:=by
  simp only [TM2.step,prog,tA,TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
    Option.getD_some]
  rw [d66,st_snd,d41]
theorem d105 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (t u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st [] t u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] t u⟩:=by
  simp only [TM2.step,prog,tA,TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
  rw [d66]
theorem d88 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩:=by
  simp only [TM2.step,prog,tB,TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
  rw [d41,st_thd,d90]
theorem d104 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] [] u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] u⟩:=by
  simp only [TM2.step,prog,tB,TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [d41]
theorem loopA (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)) :
    ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length+1]
          (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st l t u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] ((l.map φ).reverse++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t b;exact d105 φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩ :=
      d89 φ dd v1 v2 b x l t u
    rw [e,ih]
    simp
theorem loopB (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) :
    ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length+1]
          (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] t u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] (t.reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u b;exact d104 φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩ :=
      d88 φ dd v1 v2 b x t u
    rw [e,ih]
    simp
theorem d120 (d:Option (M2.Γ M2.k₀)) (hd:d=none → IsEmpty (M2.Γ M2.k₀))
    (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)) :
    ∃ n,n ≤ 2 * o.length+2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,none),
            Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
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
    simp only [prog,tA,TM2.stepAux,List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse++[]).length+1+(o.length+1),by simp;omega,?_⟩
    rw [Function.iterate_add_apply,← d79,loopA,loopB,← st_end]
    simp
theorem d114 (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:=by
  rw [d4]
  refine Eq.trans ?_ (d4 (comp M1 M2 φ d) i).symm
  show (⟨_,_,d49 _⟩:CCfg M1 M2)=_
  rw [d13,d56]
  rfl
theorem d115 (w:M2.σ × Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)),(M1.initialState,w),
        Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2):=by
  rw [d5]
  show (⟨_,_,d49 _⟩:CCfg M1 M2)=_
  rw [d13,d56]
  rfl
theorem d112 (u:M1.σ) (i:List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)),(u,M2.initialState,none),
        Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2):=by
  rw [d4]
  show (⟨_,_,d48 _⟩:CCfg M1 M2)=_
  rw [d12,d55]
  rfl
theorem d113 (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:=by
  rw [d5]
  refine Eq.trans ?_ (d5 (comp M1 M2 φ d) o).symm
  show (⟨_,_,d48 _⟩:CCfg M1 M2)=_
  rw [d12,d55]
  rfl
theorem d136 (d:Option (M2.Γ M2.k₀)) (hd:d=none → IsEmpty (M2.Γ M2.k₀))
    (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
    (h1:(flip bind (TM2.step M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
    (h2:(flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n,n ≤ s1+(2 * o1.length+2)+s2∧o1.length ≤ i.length+maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2):=by
  have p1:=d59 (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState,none)) (step1 φ d _) s1 _ _ h1
  rw [d114 φ d,d115] at p1
  obtain ⟨nt,hnt,pt⟩:=d120 φ d hd M1.initialState M2.initialState o1
  have p2:=d59 (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [d112,d113 φ d] at p2
  refine ⟨s2+(nt+s1),by omega,?_,?_⟩
  · have:=d67 M1 M1.k₁ s1 _ _ h1
    rw [d5,d4] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h:M1.k₁=M1.k₀
    · rw [h,Function.update_self]
    · rw [Function.update_of_ne h];simp
  · rw [Function.iterate_add_apply,Function.iterate_add_apply,p1,pt,p2]
    rfl
theorem d77 {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1:TM2ComputableInPolyTime ea eb f)
    (c2:TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a=>g (f a))):=by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x=>c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d:Option (c2.tm.Γ c2.tm.k₀) :=
    if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd:d=none → IsEmpty (c2.tm.Γ c2.tm.k₀):=by
    intro h
    by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d,hn] at h
    · exact not_nonempty_iff.mp hn
  let T:Polynomial ℕ :=
    c1.time+(Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time)
  have key:∀ a,∃ n,n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
    intro a
    have r1:=c1.outputsFun a
    have r2:=c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)):=by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2:(flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
      rw [hφ];exact r2.evals_in_steps
    obtain ⟨n,hn,hlen,hrun⟩:=d136 φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n,hn.trans ?_,hrun⟩
    have b1:=r1.steps_le_m
    have b2:=r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul:maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time:=Nat.mul_le_mul_left _ b1
    have b3:Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length+maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time:=d37 _ (by omega)
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
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool → Type
  | some false => Γ₀
  | none=>Option Γ₀
  | some true => Γ₁
def fmProg (φ : Γ₀ → Option Γ₁) (d:Option Γ₁):Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
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
            | some dd => .push (some true) (fun s=>(s.bind φ).getD dd) (.goto fun _=>true)
            | none => .goto fun _=>true)
          (.goto fun _=>true))
        .halt)
def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=Option Bool
  k₀:=some false
  k₁:=some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main:=false
  σ := Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=fmProg φ d
def fst3 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _=>[])
    (some false) l) none t) (some true) u
theorem d99 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u (some false)=l:=by
  unfold fst3
  rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem d81 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u none=t:=by
  unfold fst3
  rw [Function.update_of_ne (by simp),Function.update_self]
theorem d131 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u (some true)=u:=by
  unfold fst3
  rw [Function.update_self]
theorem d47 (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (fst3 l t u) (some false) l'=fst3 l' t u :=
  d51 _ (by simp) (by simp) _ _ _ _
theorem d27 (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁) :
    Function.update (fst3 l t u) none t'=fst3 l t' u :=
  d50 _ (by simp) _ _ _ _
theorem d82 (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁) :
    Function.update (fst3 l t u) (some true) u'=fst3 l t u' :=
  Function.update_idem _ _ _
theorem d98 (l:List Γ₀) :
    (fst3 l [] []:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:=by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem d132 (u:List Γ₁) :
    (fst3 [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:=by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
abbrev FCfg (Γ₀ Γ₁:Type):Type:=TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ : Γ₀ → Option Γ₁) (d:Option Γ₁)
theorem d134 (b:Option Γ₀) (x : Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some false,some x,fst3 l (some x :: t) u⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d99]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
  rw [d47,d81,d27]
theorem d164 (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false,b,fst3 [] t u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some true,none,fst3 [] t u⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d99]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [d47]
theorem d133 (hd:d=none → ∀ x,φ x=none) (b:Option Γ₀) (x : Γ₀)
    (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true,b,fst3 [] (some x :: t) u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some true,some x,fst3 [] t ((φ x).toList++u)⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d81]
  simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
    Bool.cond_true,Option.bind_some]
  rw [d27]
  cases hφ : φ x with
  | none=>simp
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,
        Option.toList_some,List.singleton_append]
      rw [d131,d82]
      simp [hφ]
theorem d163 (b:Option Γ₀) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true,b,fst3 [] [] u⟩:FCfg Γ₀ Γ₁) =
      some ⟨none,none,fst3 [] [] u⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d81]
  simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
    Bool.cond_false]
  rw [d27]
theorem d162 (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length+1]
          (some (⟨some false,b,fst3 l t u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some true,none,fst3 [] (l.reverse.map some++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t b;exact d164 φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (fmProg φ d))
        (some (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some false,some x,fst3 l (some x :: t) u⟩:=d134 φ d b x l t u
    rw [e,ih]
    simp
theorem d161 (hd:d=none → ∀ x,φ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length+1]
          (some (⟨some true,b,fst3 [] (t.map some) u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨none,none,fst3 [] [] ((t.filterMap φ).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u b;exact d163 φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (fmProg φ d))
        (some (⟨some true,b,fst3 [] ((x :: t).map some) u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some true,some x,fst3 [] (t.map some) ((φ x).toList++u)⟩ :=
      d133 φ d hd b x (t.map some) u
    rw [e,ih]
    cases hφ : φ x <;> simp [hφ]
theorem fm_run [Fintype Γ₀] (hd:d=none → ∀ x,φ x=none) (l:List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
        (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
    (some c)) (d4 (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (d5 (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
    (some (⟨some false,none,Function.update (fun _=>[]) (some false) l⟩:FCfg Γ₀ Γ₁)) =
    some (⟨none,none,Function.update (fun _=>[]) (some true) (l.filterMap φ)⟩:FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply,← d98,d162,← d132]
  have:=d161 φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
theorem d7 {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:d=none → ∀ x,φ x=none:=by
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
    time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 2
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=fm_run φ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (fmProg φ d)))^[(ea a).length+1 +
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
abbrev TPΓ (Γ₀ Γ₁:Type):TPK → Type
  | .inp => Γ₀
  | .t1=>Option Γ₀
  | .t2=>Option Γ₀
  | .t3=>Option Γ₀
  | .out => Γ₁
def d52 (φ : Γ₀ → Option Γ₁) (d:Option Γ₁) (lbl:TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s=>(s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s=>(s.bind φ).getD dd) (.goto fun _=>lbl)
      | none => .goto fun _=>lbl)
    (.goto fun _=>lbl)
def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push .t1 (fun s=>s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.push .t2 (fun s=>s) (d52 φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.push .t3 (fun s=>s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (d52 φ₁ d .e)
        .halt)
def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=tpProg φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
  | .inp=>l
  | .t1=>a
  | .t2=>b
  | .t3=>c
  | .out=>u
theorem d54 (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .inp l'=st5 l' a b c u:=by
  funext k;cases k <;> simp [st5]
theorem d31 (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t1 a'=st5 l a' b c u:=by
  funext k;cases k <;> simp [st5]
theorem d30 (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t2 b'=st5 l a b' c u:=by
  funext k;cases k <;> simp [st5]
theorem d29 (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t3 c'=st5 l a b c' u:=by
  funext k;cases k <;> simp [st5]
theorem d53 (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁) :
    Function.update (st5 l a b c u) .out u'=st5 l a b c u':=by
  funext k;cases k <;> simp [st5]
theorem d106 (l:List Γ₀) :
    (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:=by
  funext k;cases k <;> simp [st5]
theorem d151 (u:List Γ₁) :
    (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:=by
  funext k;cases k <;> simp [st5]
abbrev TPCfg (Γ₀ Γ₁:Type):Type:=TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁)
theorem d127 (s:Option Γ₀) (x : Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
    (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d54,d31]
theorem d150 (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .b,none,st5 [] a b c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d54]
theorem d126 (hd:d=none → ∀ x,φ₂ x=none) (s:Option Γ₀) (x : Γ₀)
    (a b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x :: a) b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .b,some x,st5 [] a (some x :: b) c ((φ₂ x).toList++u)⟩:=by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d31,d30,hφ]
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d31,d30,
        d53,hφ]
theorem d149 (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .c,none,st5 [] [] b c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d31]
theorem d125 (s:Option Γ₀) (x : Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x :: b) c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .c,some x,st5 [] [] b (some x :: c) u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d30,d29]
theorem d148 (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .e,none,st5 [] [] [] c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d30]
theorem d124 (hd:d=none → ∀ x,φ₁ x=none) (s:Option Γ₀) (x : Γ₀)
    (c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x :: c) u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList++u)⟩:=by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d29,hφ]
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d29,d53,hφ]
theorem d147 (s:Option Γ₀) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨none,none,st5 [] [] [] [] u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d29]
theorem d146 (b c:List (Option Γ₀)) (u:List Γ₁) :
    ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
          (some (⟨some .a,s,st5 l a b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .b,none,st5 [] (l.reverse.map some++a) b c u⟩:=by
  intro l
  induction l with
  | nil=>intro a s;exact d150 φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:=d127 φ₁ φ₂ d s x l a b c u
    rw [e,ih]
    simp
theorem d145 (hd:d=none → ∀ x,φ₂ x=none) (c:List (Option Γ₀)) :
    ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .c,none,
          st5 [] [] (t.reverse.map some++b) c ((t.filterMap φ₂).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro b u s;exact d149 φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b,s,st5 [] ((x :: t).map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .b,some x,st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList++u)⟩ :=
      d126 φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e,ih]
    cases hφ : φ₂ x <;> simp [hφ]
theorem d144 (u:List Γ₁) :
    ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .e,none,st5 [] [] [] (t.reverse.map some++c) u⟩:=by
  intro t
  induction t with
  | nil=>intro c s;exact d148 φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c,s,st5 [] [] ((x :: t).map some) c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .c,some x,st5 [] [] (t.map some) (some x :: c) u⟩ :=
      d125 φ₁ φ₂ d s x (t.map some) c u
    rw [e,ih]
    simp
theorem d143 (hd:d=none → ∀ x,φ₁ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u s;exact d147 φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e,s,st5 [] [] [] ((x :: t).map some) u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList++u)⟩ :=
      d124 φ₁ φ₂ d hd s x (t.map some) u
    rw [e,ih]
    cases hφ : φ₁ x <;> simp [hφ]
theorem tp_run [Fintype Γ₀] (hd₁:d=none → ∀ x,φ₁ x=none)
    (hd₂:d=none → ∀ x,φ₂ x=none) (l:List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
        (l.length+1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1 +
    (l.length+1)+(l.length+1)+(l.length+1)]
    (some c)) (d4 (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (d5 (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
      (l.length+1)]
    (some (⟨some .a,none,Function.update (fun _=>[]) .inp l⟩:TPCfg Γ₀ Γ₁)) =
    some (⟨none,none,Function.update (fun _=>[]) .out
      (l.filterMap φ₁++l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)
  have hA:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .a,none,st5 l [] [] [] []⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:=by
    simpa using d146 φ₁ φ₂ d [] [] [] l [] none
  have hB:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:=by
    have:=d145 φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:=by
    simpa using d144 φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁++l.filterMap φ₂)⟩:=by
    have:=d143 φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
    ← d106,hA,hB,hC,hE,d151]
theorem d10 {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ₁++(ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ φ : αΓ → Option βΓ,d=none → ∀ x,φ x=none:=by
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
    time:=Polynomial.C 4 * Polynomial.X+Polynomial.C 4
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)+((ea a).length+1) +
          ((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length+1 +
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
abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k=>M.Γ k
  | Sum.inr FX.I=>Bool ⊕ Bool
  | Sum.inr FX.W=>Bool
  | Sum.inr FX.T=>Bool
  | Sum.inr FX.O=>Bool ⊕ Bool
abbrev FstΛ : Type:=M.Λ ⊕ FL
abbrev Fstσ : Type:=M.σ × Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool) → Bool
  | none=>false
  | some (Sum.inl b)=>b
  | some (Sum.inr b)=>b
def isFst:Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _)=>true
  | _=>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s=>f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
  | .load a q => .load (fun s=>(a s.1,s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s=>Sum.inl (f s.1))
  | .halt => .goto (fun _=>Sum.inr FL.l3)
variable (M)
def d0 (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l=>trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o=>(s.1,o))
      (.branch (fun s=>s.2.isSome)
        (.branch (fun s=>isFst s.2)
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
def firstM (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ FX
    k₀:=Sum.inr FX.I
    k₁:=Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main:=Sum.inr FL.l1
    σ := Fstσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=d0 M e₀ e₁ }
variable {M}
def fstk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)):∀ k,List (FstΓ M k)
  | Sum.inl k=>S k
  | Sum.inr FX.I=>i
  | Sum.inr FX.W=>w
  | Sum.inr FX.T=>t
  | Sum.inr FX.O=>o
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool))
theorem d23 (k:M.K) (x:List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x=fstk (Function.update S k x) i w t o:=by
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
theorem d33 (i':List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i'=fstk S i' w t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d45 (w':List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w'=fstk S i w' t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d18 (t':List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t'=fstk S i w t' o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d46 (o':List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o'=fstk S i w t o':=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
end fstk
abbrev FCfg1 (M:FinTM2):Type:=TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)
def embF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl),(c.var,b),fstk c.stk i w t o⟩
theorem simF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    TM2.stepAux (trF q) ((v,b):Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
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
theorem stepF (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) (b:Option (Bool ⊕ Bool))
    (i:List (Bool ⊕ Bool)) (w t:List Bool) (o:List (Bool ⊕ Bool))
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
    TM2.step (d0 M e₀ e₁) (embF b i w t o c)=some (embF b i w t o c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
theorem d6 {σ : Type} (f : σ → Option σ) {a b:ℕ} {x y z : σ}
    (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z) :
    (flip bind f)^[b+a] (some x)=some z:=by
  rw [Function.iterate_add_apply,h₁,h₂]
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool)
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k:M.K):fstk S i w t o (Sum.inl k)=S k:=rfl
@[simp] theorem fstk_I:fstk S i w t o (Sum.inr FX.I)=i:=rfl
@[simp] theorem fstk_W:fstk S i w t o (Sum.inr FX.W)=w:=rfl
@[simp] theorem fstk_T:fstk S i w t o (Sum.inr FX.T)=t:=rfl
@[simp] theorem fstk_O:fstk S i w t o (Sum.inr FX.O)=o:=rfl
end fstk
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:List Bool) (o:List (Bool ⊕ Bool))
theorem f1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inl a :: i) w t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d33,d18,isFst,bit]
theorem f1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inr a :: i) w t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d33,d45,isFst,bit]
theorem f1_nil (b:Option (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),fstk S [] w t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l2),(v,none),fstk S [] w t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d33]
theorem loop1:∀ (i:List (Bool ⊕ Bool)) (w t:List Bool) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[i.length+1]
        (some (⟨some (Sum.inr FL.l1),(v,b),fstk S i w t o⟩:FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2),(v,none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse++w)
          ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
  intro i
  induction i with
  | nil=>intro w t b;exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons,Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e:flip bind (TM2.step (d0 M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inl a :: i) w t o⟩:FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e,ih];simp [List.filterMap_cons]
    | inr a =>
      have e:flip bind (TM2.step (d0 M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inr a :: i) w t o⟩:FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e,ih];simp [List.filterMap_cons]
theorem d168 (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem f2_nil (b:Option (Bool ⊕ Bool)) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w [] o⟩:FCfg1 M) =
      some ⟨some (Sum.inl M.main),(v,none),fstk S [] w [] o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18]
theorem loop2:∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
        (some (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w t o⟩:FCfg1 M)) =
      some ⟨some (Sum.inl M.main),(v,none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) [] w [] o⟩:=by
  intro t
  induction t with
  | nil =>
    intro S b
    have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:=d168 e₀ e₁ v S w o b a t
    rw [e,ih];simp
theorem d167 (b:Option (Bool ⊕ Bool)) (a:Bool) (w:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d45,d46,bit]
theorem f3_nil (b:Option (Bool ⊕ Bool)) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l3),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l4),(v,none),fstk S [] [] [] o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d45]
theorem loop3:∀ (w:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[w.length+1]
        (some (⟨some (Sum.inr FL.l3),(v,b),fstk S [] w [] o⟩:FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4),(v,none),fstk S [] [] [] (w.reverse.map Sum.inr++o)⟩:=by
  intro w
  induction w with
  | nil=>intro o b;exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩ :=
      d167 e₀ e₁ v S o b a w
    rw [e,ih];simp
theorem d166 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem f4_nil (b:Option (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ []) [] [] t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l5),(v,none),fstk (Function.update S M.k₁ []) [] [] t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d23]
theorem loop4:∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
        (some (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5),(v,none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩:=d166 e₀ e₁ v S o b y m t
    rw [e,ih];simp
theorem d165 (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18,d46,bit]
theorem f5_nil (b:Option (Bool ⊕ Bool)) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
      some ⟨none,(v,none),fstk S [] [] [] o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18]
theorem loop5:∀ (t:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
        (some (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] t o⟩:FCfg1 M)) =
      some ⟨none,(v,none),fstk S [] [] [] (t.reverse.map Sum.inl++o)⟩:=by
  intro t
  induction t with
  | nil=>intro o b;exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩ :=
      d165 e₀ e₁ v S o b a t
    rw [e,ih];simp
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool)
theorem d97:(fstk (fun _=>[]) [] [] [] []:∀ k,List (FstΓ M k))=fun _=>[]:=by
  funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d96 (i:List (Bool ⊕ Bool)) :
    (fstk (fun _=>[]) i [] [] []:∀ k,List (FstΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (FstΓ M k)) (Sum.inr FX.I) i :=
  (d33 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d97])
theorem d95 (o:List (Bool ⊕ Bool)) :
    (fstk (fun _=>[]) [] [] [] o:∀ k,List (FstΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (FstΓ M k)) (Sum.inr FX.O) o :=
  (d46 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d97])
theorem d110 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main),(M.initialState,b),
        fstk (Function.update (fun _=>[]) M.k₀ l) i w t o⟩:FCfg1 M):=by
  rw [d4];rfl
theorem d111 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3),(M.initialState,b),
        fstk (Function.update (fun _=>[]) M.k₁ m) i w t o⟩:FCfg1 M):=by
  rw [d5];rfl
theorem d16 {γ δ : Type} (l:List γ) :
    l.filterMap (fun _=>(none:Option δ))=[]:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp
theorem d26 (x w:List Bool) :
    (encodePair (x,w)).filterMap Sum.getLeft? = x:=by
  have h1:(Sum.getLeft? ∘ (Sum.inl:Bool → Bool ⊕ Bool):Bool → Option Bool)=some:=rfl
  have h2:(Sum.getLeft? ∘ (Sum.inr:Bool → Bool ⊕ Bool):Bool → Option Bool)=fun _=>none:=rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,d16,List.append_nil]
theorem d24 (x w:List Bool) :
    (encodePair (x,w)).filterMap Sum.getRight? = w:=by
  have h1:(Sum.getRight? ∘ (Sum.inl:Bool → Bool ⊕ Bool):Bool → Option Bool)=fun _=>none:=rfl
  have h2:(Sum.getRight? ∘ (Sum.inr:Bool → Bool ⊕ Bool):Bool → Option Bool)=some:=rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,d16,List.nil_append]
theorem d9 (x w:List Bool) :
    (encodePair (x,w)).length=x.length+w.length:=by
  simp [encodePair]
theorem d107 (x w0:List Bool) (m:List (M.Γ M.k₁)) (s:ℕ)
    (h:(flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)) :
    ∃ n,n ≤ s+2 * x.length+2 * w0.length+2 * m.length+5 ∧
      (flip bind (TM2.step (d0 M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):=by
  have q1:(flip bind (TM2.step (d0 M e₀ e₁)))^[(encodePair (x,w0)).length+1]
      (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
      some (⟨some (Sum.inr FL.l2),(M.initialState,none),
        fstk (fun _=>[]) [] w0.reverse x.reverse []⟩:FCfg1 M):=by
    have:=loop1 e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,w0)) [] [] none
    rw [d26,d24,List.append_nil,List.append_nil,d96] at this
    exact (congrArg (fun c=>(flip bind (TM2.step (d0 M e₀ e₁)))^[
      (encodePair (x,w0)).length+1] (some c))
      (d4 (firstM M e₀ e₁) (encodePair (x,w0)))).trans this
  have q2:(flip bind (TM2.step (d0 M e₀ e₁)))^[x.reverse.length+1]
      (some (⟨some (Sum.inr FL.l2),(M.initialState,none),
        fstk (fun _=>[]) [] w0.reverse x.reverse []⟩:FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))):=by
    have:=loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _=>[]) none
    rw [d110]
    simpa using this
  have q3:=d59 (TM2.step M.m) (TM2.step (d0 M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [d111] at q3
  have q4:(flip bind (TM2.step (d0 M e₀ e₁)))^[w0.reverse.length+1]
      (some (⟨some (Sum.inr FL.l3),(M.initialState,none),
        fstk (Function.update (fun _=>[]) M.k₁ m) [] w0.reverse [] []⟩:FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4),(M.initialState,none),
        fstk (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:FCfg1 M):=by
    have:=loop3 e₀ e₁ M.initialState (Function.update (fun _=>[]) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5:(flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
      (some (⟨some (Sum.inr FL.l4),(M.initialState,none),
        fstk (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5),(M.initialState,none),
        fstk (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:FCfg1 M):=by
    have:=loop4 e₀ e₁ M.initialState (fun _=>[]) (w0.map Sum.inr) m [] none
    simpa using this
  have q6:(flip bind (TM2.step (d0 M e₀ e₁)))^[(m.reverse.map e₁).length+1]
      (some (⟨some (Sum.inr FL.l5),(M.initialState,none),
        fstk (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):=by
    have:=loop5 e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [d95] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (d5 (firstM M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [d9,List.length_reverse,List.length_map]
  omega
theorem d61 (f:List Bool → List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(f p.1,p.2))):=by
  let e₀:Bool → c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let e₁:c.tm.Γ c.tm.k₁ → Bool:=c.outputAlphabet
  let T:Polynomial ℕ :=
    c.time+Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X+Polynomial.C 5
  have key:∀ p:List Bool × List Bool,∃ n,n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (d0 c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1,p.2))):=by
    rintro ⟨x,w⟩
    have hs:∃ s,s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
    obtain ⟨s,b1,h⟩:=hs
    obtain ⟨n,hn,hrun⟩:=d107 e₀ e₁ x w _ s h
    have hm:(List.map c.outputAlphabet.invFun (f x)).map e₁=f x:=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n,hn.trans ?_,hrun⟩
    have h':=h
    rw [d5,d4] at h'
    have hlen:=d67 c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self,List.length_map] at hlen
    have hin:((Function.update (fun _=>[]:∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length:=by
      by_cases hk:c.tm.k₁=c.tm.k₀
      · rw [hk,Function.update_self,List.length_map]
      · rw [Function.update_of_ne hk];simp
    have b2:Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length+w.length) c.time :=
      d37 _ (by omega)
    have hmul:maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length+w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,d9,List.length_map]
    omega
  exact ⟨{
    tm:=firstM c.tm e₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun p =>
      { steps:=Classical.choose (key p)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (d0 c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l=>some (haltList (firstM c.tm e₀ e₁) l))
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
abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k=>M.Γ k
  | Sum.inr IX.I=>Bool ⊕ Bool
  | Sum.inr IX.C=>Bool
  | Sum.inr IX.T=>Bool
  | Sum.inr IX.O=>Bool
abbrev ItΛ : Type:=M.Λ ⊕ IL
abbrev Itσ : Type:=M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s=>f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
  | .load a q => .load (fun s=>(a s.1,s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s=>Sum.inl (f s.1))
  | .halt => .goto (fun _=>Sum.inr IL.l4)
variable (M)
def d1 (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l=>trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o=>(s.1,o))
      (.branch (fun s=>s.2.isSome)
        (.branch (fun s=>isFst s.2)
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
def iterM (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ IX
    k₀:=Sum.inr IX.I
    k₁:=Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main:=Sum.inr IL.l1
    σ := Itσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=d1 M e₀ d₀ e₁ }
variable {M}
def istk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    ∀ k,List (ItΓ M k)
  | Sum.inl k=>S k
  | Sum.inr IX.I=>i
  | Sum.inr IX.C=>cn
  | Sum.inr IX.T=>t
  | Sum.inr IX.O=>o
section istk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
@[simp] theorem istk_M (k:M.K):istk S i cn t o (Sum.inl k)=S k:=rfl
@[simp] theorem istk_I:istk S i cn t o (Sum.inr IX.I)=i:=rfl
@[simp] theorem istk_C:istk S i cn t o (Sum.inr IX.C)=cn:=rfl
@[simp] theorem istk_T:istk S i cn t o (Sum.inr IX.T)=t:=rfl
@[simp] theorem istk_O:istk S i cn t o (Sum.inr IX.O)=o:=rfl
theorem d15 (k:M.K) (x:List (M.Γ k)) :
    Function.update (istk S i cn t o) (Sum.inl k) x=istk (Function.update S k x) i cn t o:=by
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
theorem d32 (i':List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr IX.I) i'=istk S i' cn t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d44 (cn':List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.C) cn'=istk S i cn' t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d14 (t':List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.T) t'=istk S i cn t' o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d72 (o':List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.O) o'=istk S i cn t o':=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
end istk
abbrev ICfg (M:FinTM2):Type:=TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def embI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c:TM2.Cfg M.Γ M.Λ M.σ):ICfg M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl),(c.var,b),istk c.stk i cn t o⟩
theorem simI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    TM2.stepAux (trI q) ((v,b):Itσ M) (istk S i cn t o) =
      embI b i cn t o (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
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
theorem stepI (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
    (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
    TM2.step (d1 M e₀ d₀ e₁) (embI b i cn t o c)=some (embI b i cn t o c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)
theorem d108 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (l:List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main),(M.initialState,b),
        istk (Function.update (fun _=>[]) M.k₀ l) i cn t o⟩:ICfg M):=by
  rw [d4];rfl
theorem d109 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (m:List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4),(M.initialState,b),
        istk (Function.update (fun _=>[]) M.k₁ m) i cn t o⟩:ICfg M):=by
  rw [d5];rfl
theorem d94:(istk (fun _=>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _=>[]:=by
  funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d93 (i:List (Bool ⊕ Bool)) :
    (istk (fun _=>[]) i [] [] []:∀ k,List (ItΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.I) i :=
  (d32 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d94])
theorem d92 (o:List Bool) :
    (istk (fun _=>[]) [] [] [] o:∀ k,List (ItΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.O) o :=
  (d72 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d94])
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
theorem i1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inl a :: i) cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d32,d14,isFst,bit]
theorem i1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inr a :: i) cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d32,d44,isFst,bit]
theorem i1_nil (b:Option (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),istk S [] cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l2),(v,none),istk S [] cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d32]
theorem iloop1 (o:List Bool) :
    ∀ (i:List (Bool ⊕ Bool)) (cn t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[i.length+1]
        (some (⟨some (Sum.inr IL.l1),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨some (Sum.inr IL.l2),(v,none),
        istk S [] ((i.filterMap Sum.getRight?).reverse++cn)
          ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
  intro i
  induction i with
  | nil=>intro cn t b;exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons,Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inl a :: i) cn t o⟩:ICfg M)) =
          some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih];simp [List.filterMap_cons]
    | inr a =>
      have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inr a :: i) cn t o⟩:ICfg M)) =
          some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih];simp [List.filterMap_cons]
theorem d158 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i2_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2),(v,b),istk S i cn [] o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l3),(v,none),istk S i cn [] o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14]
theorem iloop2 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (Sum.inr IL.l2),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨some (Sum.inr IL.l3),(v,none),
        istk (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) i cn [] o⟩:=by
  intro t
  induction t with
  | nil =>
    intro S b
    have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      d158 e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih];simp
theorem d157 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3),(v,b),istk S i (a :: cn) t o⟩:ICfg M) =
      some ⟨some (Sum.inl M.main),(v,some (Sum.inl a)),istk S i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d44]
theorem i3_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3),(v,b),istk S i [] t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l5),(v,none),istk S i [] t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d44]
theorem d156 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
    (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i4_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ []) i cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l2),(v,none),istk (Function.update S M.k₁ []) i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d15]
theorem iloop4 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l2),(v,none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4),(v,b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      d156 e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih];simp
theorem d155 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
    (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i5_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ []) i cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l6),(v,none),istk (Function.update S M.k₀ []) i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d15]
theorem iloop5 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (m:List (M.Γ M.k₀)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l6),(v,none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5),(v,b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      d155 e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih];simp
theorem d154 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d72,bit]
theorem i6_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6),(v,b),istk S i cn [] o⟩:ICfg M) =
      some ⟨none,(v,none),istk S i cn [] o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14]
theorem iloop6 (i:List (Bool ⊕ Bool)) (cn:List Bool) :
    ∀ (t o:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (Sum.inr IL.l6),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨none,(v,none),istk S i cn [] (t.reverse++o)⟩:=by
  intro t
  induction t with
  | nil=>intro o b;exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩ :=
      d154 e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih];simp
theorem d28 (k:M.K) :
    Function.update (fun _=>[]:∀ k,List (M.Γ k)) k []=fun _=>[] :=
  Function.update_eq_self k (fun _=>[]:∀ k,List (M.Γ k))
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
theorem d71 (g:List Bool → List Bool) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z) :
    ∀ (cn z:List Bool) (L:ℕ) (b:Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length,(g^[j] z).length ≤ L) →
      ∃ n,n ≤ cn.length * (p.eval L+2 * L+3)+2 * L+3 ∧
        ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
              istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:ICfg M)) =
          some ⟨none,(M.initialState,none),
            istk (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
      rw [List.map_reverse,List.reverse_reverse,List.map_map]
      conv_rhs=>rw [← List.map_id z]
      exact List.map_congr_left fun a _=>hd a
    have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l5),(M.initialState,none),
          istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2:=iloop5 e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none
    rw [d28,List.append_nil] at q2
    have q3:=iloop6 e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil,hz] at q3
    refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3⟩
    have hz0:z.length ≤ L:=hL 0 (Nat.zero_le _)
    simp only [List.length_reverse,List.length_map,List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s,m,hs,hm,hmg⟩:=hrun z
    rw [List.length_cons] at hL
    have hz0:z.length ≤ L:=hL 0 (Nat.zero_le _)
    have hgz:(g z).length ≤ L:=hL 1 (by omega)
    have hml:m.length=(g z).length:=by rw [← hmg,List.length_map]
    have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩:ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))):=by
      rw [d108]
      exact d157 e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2:=d59 (TM2.step M.m) (TM2.step (d1 M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [d109] at q2
    have q3:=iloop4 e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (Sum.inl a))
    rw [d28,List.append_nil,List.map_reverse,hmg] at q3
    have q4:=iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none
    rw [List.append_nil,List.reverse_reverse] at q4
    obtain ⟨n,hn,q5⟩:=ih (g z) L none (fun j hj=>by
      have:=hL (j+1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e:g^[(a :: cn).length] z=g^[cn.length] (g z):=Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3) q4) q5⟩
    have hp:p.eval z.length ≤ p.eval L:=d37 p (by omega)
    rw [List.length_reverse,List.length_cons,Nat.succ_mul]
    generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢
    omega
theorem d80 (g:List Bool → List Bool) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z)
    (y u:List Bool) (L:ℕ) (hL:∀ j ≤ u.length,(g^[j] y).length ≤ L) :
    ∃ n,n ≤ u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5 ∧
      ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)):=by
  have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
      some (⟨some (Sum.inr IL.l2),(M.initialState,none),
        istk (fun _=>[]) [] u.reverse y.reverse []⟩:ICfg M):=by
    have:=iloop1 e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none
    rw [d26,d24,List.append_nil,List.append_nil,d93] at this
    exact (congrArg (fun c=>((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
      (d4 (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
  have q2:=iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none
  rw [List.append_nil,List.reverse_reverse] at q2
  obtain ⟨n,hn,q3⟩:=d71 e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse];exact hL)
  rw [List.length_reverse] at hn q3
  rw [d92] at q3
  have q3':((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3),(M.initialState,none),
        istk (Function.update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (d5 (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3'⟩
  rw [d9,List.length_reverse]
  omega
theorem d22 (g:List Bool → List Bool) (m:List Bool → ℕ)
    (hm:∀ y:List Bool,m (g y) ≤ m y)
    (hg:∀ y:List Bool,(g y).length ≤ y.length+m y) (y:List Bool) :
    ∀ j:ℕ,m (g^[j] y) ≤ m y∧(g^[j] y).length ≤ y.length+j * m y:=by
  intro j
  induction j with
  | zero=>simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',Nat.succ_mul]
    have h1:=hm (g^[j] y)
    have h2:=hg (g^[j] y)
    obtain ⟨i1,i2⟩:=ih
    generalize j * m y=A at i2 ⊢
    exact ⟨by omega,by omega⟩
theorem d70 (A B L V y u:ℕ) (hLV:L ≤ V) (hAB:A ≤ B) :
    A+2 * L+2 * y+u+5 ≤ B+2 * V+3 * (y+u)+5:=by
  omega
theorem iter_polyTime_measure (g:List Bool → List Bool)
    (c:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (m:List Bool → ℕ) (a:ℕ)
    (hm:∀ y:List Bool,m (g y) ≤ m y)
    (hg:∀ y:List Bool,(g y).length ≤ y.length+m y)
    (ha:∀ y:List Bool,m y ≤ a * y.length+a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>g^[p.2.length] p.1)):=by
  let e₀:Bool → c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let d₀:c.tm.Γ c.tm.k₀ → Bool:=c.inputAlphabet
  let e₁:c.tm.Γ c.tm.k₁ → Bool:=c.outputAlphabet
  let W:Polynomial ℕ :=
    Polynomial.X+Polynomial.X * (Polynomial.C a * Polynomial.X+Polynomial.C a)
  let T:Polynomial ℕ :=
    Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3) +
      Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
  have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
  have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m)∧m.map e₁=g z:=by
    intro z
    refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
  have key:∀ q:List Bool × List Bool,∃ n,n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
    rintro ⟨y,u⟩
    have hL:∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length+u.length * (a * y.length+a):=by
      intro j hj
      have h1:=(d22 g m hm hg y j).2
      have h2:j * m y ≤ u.length * (a * y.length+a):=Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n,hn,hr⟩:=d80 e₀ d₀ e₁ g c.time hd hrun y u
      (y.length+u.length * (a * y.length+a)) hL
    have hLV:y.length+u.length * (a * y.length+a) ≤
        (y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp:=d37 c.time hLV
    have hmul:u.length * (Polynomial.eval (y.length+u.length * (a * y.length+a)) c.time +
          2 * (y.length+u.length * (a * y.length+a))+3) ≤
        (y.length+u.length) * (Polynomial.eval
          ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a))
            c.time +
            2 * ((y.length+u.length) +
              (y.length+u.length) * (a * (y.length+u.length)+a))+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n,hn.trans ?_,hr⟩
    simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,d9]
    exact d70 _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm:=iterM c.tm e₀ d₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun q =>
      { steps:=Classical.choose (key q)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l=>some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
theorem iter_polyTime (g:List Bool → List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (k:ℕ) (hk:∀ y:List Bool,(g y).length ≤ y.length+k) :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
  iter_polyTime_measure g c (fun _=>k) k (fun _=>le_rfl) hk (fun _=>Nat.le_add_left k _)
end Lib.Machines.Iter
end
section
namespace Lib.Machines
open PEqualNP.Library
private theorem d2 {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ = l.map g:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [hφ,ih]
private theorem d8 {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ = []:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [hφ,ih]
theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf:PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg:PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a=>g (f a)):=by
  obtain ⟨c1⟩:=hf
  obtain ⟨c2⟩:=hg
  exact d77 ea eb ec f g c1 c2
theorem d84 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.2,p.1)):=by
  refine d10 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some (Sum.inl b)) s)
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some (Sum.inr b)) (fun _=>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d8 Sum.inl _ (fun _=>rfl) x,
    d2 Sum.inr _ Sum.inl (fun _=>rfl) w,
    d2 Sum.inl _ Sum.inr (fun _=>rfl) x,
    d8 Sum.inr _ (fun _=>rfl) w]
  simp
theorem d171 :
    PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
      PEqualNP.Library.encodePair (fun x:List Bool=>(x,x)):=by
  refine d10 _ _ _
    (fun b:Bool=>some (Sum.inl b)) (fun b:Bool=>some (Sum.inr b)) ?_
  intro x
  have h1:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inl (β := Bool) b))
    Sum.inl (fun _=>rfl) x
  have h2:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inr (α := Bool) b))
    Sum.inr (fun _=>rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair,h1,h2]
theorem d170 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1):=by
  refine d7 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
    d8 Sum.inr _ (fun _=>rfl) w]
  simp
theorem d169 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.2):=by
  refine d7 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d8 Sum.inl _ (fun _=>rfl) x,
    d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
  simp
theorem d74 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1++p.2):=by
  refine d7 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
    d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
  simp
theorem d38 {f:List Bool → List Bool}
    (hf:Lib.CPTs f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(f p.1,p.2)):=by
  obtain ⟨c⟩:=hf
  exact d61 f c
theorem d101 {g:List Bool → List Bool}
    (hg:Lib.CPTs g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.1,g p.2)) :=
  cpt_comp (cpt_comp d84 (d38 hg)) d84
theorem cpt_pair {f g:List Bool → List Bool}
    (hf:Lib.CPTs f)
    (hg:Lib.CPTs g) :
    PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
      PEqualNP.Library.encodePair (fun x:List Bool=>(f x,g x)) :=
  cpt_comp (cpt_comp d171 (d101 hg)) (d38 hf)
theorem cpt_id :
    Lib.CPTs (fun x:List Bool=>x):=by
  refine d7 _ _ _ (fun b:Bool=>some b) ?_
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
def fstRun {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q,[]=>(fin q).toList
  | q,a :: l=>(δ q a).2.toList++fstRun δ fin (δ q a).1 l
def fstRun2 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q,[]=>(fin q).toList
  | q,a :: l=>(δ q a).2.1.toList++(δ q a).2.2.toList++fstRun2 δ fin (δ q a).1 l
theorem d36 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁)
    (q:Q) (l:List Γ₀) :
    fstRun δ fin q l=fstRun2 (fun q a=>((δ q a).1,(δ q a).2,none)) fin q l:=by
  induction l generalizing q with
  | nil=>rfl
  | cons a l ih=>simp [fstRun,fstRun2,ih]
inductive TrK:Type
  | inp | tmp | out
  deriving DecidableEq
instance:Fintype TrK :=
  Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK → Type
  | .inp => Γ₀
  | .tmp=>Q × Option Γ₀
  | .out => Γ₁
abbrev TrS (Γ₀ Q:Type):Type:=Q × Option Γ₀ × Bool
def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q,some a)=>(δ q a).2.1
  | (q,none)=>fin q
def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁):Q × Option Γ₀ → Option Γ₁
  | (q,some a)=>(δ q a).2.2
  | (_,none)=>none
def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁)
    (e:Q × Option Γ₀):List Γ₁ :=
  (trO1 δ fin e).toList++(trO2 δ e).toList
def d21 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁):Q → List Γ₀ → List (Q × Option Γ₀)
  | q,[]=>[(q,none)]
  | q,a :: l=>(q,some a) :: d21 δ (δ q a).1 l
theorem d57 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q:Q) (l:List Γ₀) :
    (d21 δ q l).length=l.length+1:=by
  induction l generalizing q with
  | nil=>rfl
  | cons a l ih=>simp [d21,ih]
theorem d85 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q:Q)
    (l:List Γ₀):(d21 δ q l).flatMap (trOut δ fin)=fstRun2 δ fin q l:=by
  induction l generalizing q with
  | nil=>simp [d21,trOut,trO1,trO2,fstRun2]
  | cons a l ih=>simp [d21,trOut,trO1,trO2,fstRun2,ih]
def d65 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s=>(o s).isSome)
    (match d with
      | some dd => .push .out (fun s=>(o s).getD dd) next
      | none=>next)
    next
def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
    (d:Option Γ₁):Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
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
        (d65 (fun s=>trO2 δ (s.1,s.2.1)) d
          (d65 (fun s=>trO1 δ fin (s.1,s.2.1)) d (.goto fun _=>true)))
        .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin:Q → Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
  K:=TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main:=false
  σ := TrS Γ₀ Q
  initialState:=(q₀,none,false)
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=trProg δ fin q₀ d
def trSt (l:List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
  | .inp=>l
  | .tmp=>t
  | .out=>u
theorem d40 (l l':List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    Function.update (trSt l t u) .inp l'=trSt l' t u:=by
  funext k;cases k <;> simp [trSt]
theorem d19 (l:List Γ₀) (t t':List (Q × Option Γ₀)) (u:List Γ₁) :
    Function.update (trSt l t u) .tmp t'=trSt l t' u:=by
  funext k;cases k <;> simp [trSt]
theorem d78 (l:List Γ₀) (t:List (Q × Option Γ₀)) (u u':List Γ₁) :
    Function.update (trSt l t u) .out u'=trSt l t u':=by
  funext k;cases k <;> simp [trSt]
theorem d87 (l:List Γ₀) :
    (trSt l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:=by
  funext k;cases k <;> simp [trSt]
theorem d121 (u:List Γ₁) :
    (trSt [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:=by
  funext k;cases k <;> simp [trSt]
abbrev TrCfg (Γ₀ Γ₁ Q:Type):Type:=TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
theorem d25 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁) (hd:∀ _ : Γ₁,d≠none)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.stepAux (d65 o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList++u)):=by
  cases ho:o s with
  | none=>cases d <;> simp [d65,TM2.stepAux,ho]
  | some y =>
    cases d with
    | none=>exact absurd rfl (hd y)
    | some dd=>simp [d65,TM2.stepAux,ho,trSt,d78]
variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
  (d:Option Γ₁)
theorem d123 (s:TrS Γ₀ Q) (a : Γ₀) (l:List Γ₀) (t:List (Q × Option Γ₀))
    (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩:=by
  simp [TM2.step,trProg,TM2.stepAux,trSt,d40,d19]
theorem d142 (s:TrS Γ₀ Q) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true,(q₀,none,false),trSt [] ((s.1,none) :: t) u⟩:=by
  simp [TM2.step,trProg,TM2.stepAux,trSt,d40,d19]
theorem d122 (hd:∀ _ : Γ₁,d≠none) (s:TrS Γ₀ Q) (e:Q × Option Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e++u)⟩:=by
  simp only [TM2.step,trProg,TM2.stepAux]
  have e1:(trSt [] (e :: t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e :: t:=rfl
  rw [e1]
  simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
  rw [d19,d25 _ _ hd,d25 _ _ hd]
  simp [TM2.stepAux,trOut]
theorem d141 (s:TrS Γ₀ Q) (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] [] u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨none,(q₀,none,false),trSt [] [] u⟩:=by
  simp [TM2.step,trProg,TM2.stepAux,trSt,d19]
theorem d140 (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Q × Option Γ₀)) (s:TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1]
          (some (⟨some false,s,trSt l t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true,(q₀,none,false),trSt [] ((d21 δ s.1 l).reverse++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t s;exact d142 δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩ :=
      d123 δ fin q₀ d s a l t u
    rw [e,ih]
    simp [d21]
theorem d139 (hd:∀ _ : Γ₁,d≠none) :
    ∀ (t:List (Q × Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length+1]
          (some (⟨some true,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none,(q₀,none,false),trSt [] [] (t.reverse.flatMap (trOut δ fin)++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u s;exact d141 δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e':flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e++u)⟩ :=
      d122 δ fin q₀ d hd s e t u
    rw [e',ih]
    simp [List.flatMap_append]
theorem d138 [Fintype Γ₀] [Fintype Q] (hd:∀ _ : Γ₁,d≠none) (l:List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1 +
    (l.length+1)] (some c)) (d4 (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (d5 (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
    (some (⟨some false,(q₀,none,false),Function.update (fun _=>[]) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none,(q₀,none,false),Function.update (fun _=>[]) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA:(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1]
      (some (⟨some false,(q₀,none,false),trSt l [] []⟩:TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true,(q₀,none,false),trSt [] (d21 δ q₀ l).reverse []⟩:=by
    have:=d140 δ fin q₀ d [] l [] (q₀,none,false)
    rw [List.append_nil] at this
    exact this
  have hB:(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1]
      (some (⟨some true,(q₀,none,false),trSt [] (d21 δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none,(q₀,none,false),trSt [] [] (fstRun2 δ fin q₀ l)⟩:=by
    have:=d139 δ fin q₀ d hd (d21 δ q₀ l).reverse [] (q₀,none,false)
    rw [List.length_reverse,d57,List.reverse_reverse,d85,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply,← d87,hA,hB,d121]
theorem fst2_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin:Q → Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ _ : βΓ,d≠none:=by
    intro y
    have hn:Nonempty βΓ := ⟨y⟩
    simp [d,hn]
  exact ⟨{
    tm:=trM δ fin q₀ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 3
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=d138 δ fin q₀ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
theorem fst_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin:Q → Option βΓ) (q₀:Q)
    (h:∀ a,eb (f a)=fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a=>((δ q a).1,(δ q a).2,none)) fin q₀
    (fun a=>(h a).trans (d36 δ fin q₀ (ea a)))
end Lib.Machines
end
section
namespace Lib.Machines.Rev
open Turing PEqualNP.Library Lib.Machines
def prog:Unit → TM2.Stmt (fun _:Bool=>Bool) Unit (Option Bool)
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
  Λ := Unit
  main:=()
  σ := Option Bool
  initialState:=none
  m:=prog
abbrev RCfg:Type:=TM2.Cfg (fun _:Bool=>Bool) Unit (Option Bool)
def st (l u:List Bool):Bool → List Bool:=fun k=>cond k u l
theorem d79 (l:List Bool) :
    st l []=Function.update (fun _=>([]:List Bool)) false l:=by
  funext k;cases k <;> simp [st]
theorem st_end (u:List Bool) :
    st [] u=Function.update (fun _=>([]:List Bool)) true u:=by
  funext k;cases k <;> simp [st]
theorem d103 (x:Bool) (l u:List Bool) :
    TM2.step prog (⟨some (),none,st (x :: l) u⟩:RCfg) =
      some ⟨some (),none,st l (x :: u)⟩:=by
  simp only [TM2.step,prog,TM2.stepAux]
  simp only [st,Bool.cond_false,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,
    Option.getD_some,Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
  funext k;cases k <;> simp [st]
theorem d129 (u:List Bool) :
    TM2.step prog (⟨some (),none,st [] u⟩:RCfg)=some ⟨none,none,st [] u⟩:=by
  simp only [TM2.step,prog,TM2.stepAux]
  simp only [st,Bool.cond_false,List.head?_nil,List.tail_nil,Option.isSome_none,
    Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
  funext k;cases k <;> simp [st]
theorem loop:∀ (l u:List Bool),
    (flip bind (TM2.step prog))^[l.length+1] (some (⟨some (),none,st l u⟩:RCfg)) =
      some ⟨none,none,st [] (l.reverse++u)⟩:=by
  intro l
  induction l with
  | nil=>intro u;exact d129 u
  | cons x l ih =>
    intro u
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step prog) (some (⟨some (),none,st (x :: l) u⟩:RCfg)) =
        some ⟨some (),none,st l (x :: u)⟩:=d103 x l u
    rw [e,ih]
    simp
theorem run (l:List Bool) :
    (flip bind (TM2.step prog))^[l.length+1] (some (initList tm l)) =
      some (haltList tm l.reverse):=by
  refine (congrArg (fun c=>(flip bind (TM2.step prog))^[l.length+1] (some c))
    (d4 tm l)).trans (Eq.trans ?_ (congrArg some (d5 tm l.reverse)).symm)
  show (flip bind (TM2.step prog))^[l.length+1]
    (some (⟨some (),none,Function.update (fun _=>[]) false l⟩:RCfg)) =
    some (⟨none,none,Function.update (fun _=>[]) true l.reverse⟩:RCfg)
  rw [← d79,loop,← st_end]
  simp
noncomputable def reverseComputable :
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
        exact (congrArg (fun l=>(flip bind (TM2.step prog))^[a.length+1]
          (some (initList tm l))) (hm a)).trans
          ((run a).trans (congrArg (fun l=>some (haltList tm l)) (hm a.reverse).symm))
      steps_le_m:=by simp }
end Lib.Machines.Rev
end
section
namespace Lib.Universal
def un (n:ℕ):List Bool:=List.replicate n true
def pairB (a b:List Bool):List Bool:=un a.length++false :: (a++b)
def unpairB (s:List Bool):List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)
theorem unpairB_pairB (a b:List Bool):unpairB (pairB a b)=(a,b):=by
  have h1:(pairB a b).takeWhile id=un a.length:=by
    simp [pairB,un]
  have h2:(pairB a b).dropWhile id=false :: (a++b):=by
    simp [pairB,un]
  simp [unpairB,h1,h2,un]
end Lib.Universal
end
section
namespace Lib.Universal
def bflag (b:Bool):List Bool:=if b then [true] else []
@[simp] theorem un_zero:un 0=[]:=rfl
@[simp] theorem un_length (n:ℕ):(un n).length=n:=List.length_replicate
theorem un_succ (n:ℕ):un (n+1)=true :: un n:=rfl
theorem un_inj {a b:ℕ} (h:un a=un b):a=b:=by
  have:=congrArg List.length h
  simpa [un] using this
def hd (s:List Bool):List Bool:=s.takeWhile id
def dropN (s:List Bool):List Bool:=(s.dropWhile id).tail
def sel (f a b:List Bool):List Bool:=if f=[] then a else b
def mulU (u v:List Bool):List Bool:=un (u.length * v.length)
def spread (s:List Bool):List Bool:=s.flatMap fun b=>if b then [true,false] else [false]
def blank (s:List Bool):List Bool:=s.map fun _=>false
theorem sel_append_left (f p a b:List Bool):sel f (p++a) (p++b)=p++sel f a b:=by
  unfold sel;split_ifs <;> rfl
theorem hd_length (s:List Bool):(hd s).length ≤ s.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix id)
theorem dropN_length (s:List Bool):(dropN s).length ≤ s.length:=by
  have h1:=List.IsSuffix.length_le (List.dropWhile_suffix (p:=id) (l:=s))
  simp only [dropN,List.length_tail]
  omega
theorem iter_length (g:List Bool → List Bool) (hg:∀ s,(g s).length ≤ s.length) (k:ℕ) :
    ∀ s,(g^[k] s).length ≤ s.length:=by
  induction k with
  | zero=>intro s;exact le_rfl
  | succ k ih=>intro s;rw [Function.iterate_succ_apply];exact (ih _).trans (hg s)
theorem sel_length (f a b:List Bool) (N:ℕ) (ha:a.length ≤ N) (hb:b.length ≤ N) :
    (sel f a b).length ≤ N:=by
  unfold sel;split_ifs <;> assumption
theorem unpairB_length (s:List Bool) :
    2 * (unpairB s).1.length+(unpairB s).2.length ≤ s.length:=by
  have h:=congrArg List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s))
  simp only [List.length_append] at h
  simp only [unpairB,List.length_take,List.length_drop,List.length_tail]
  omega
theorem pairB_length (a b:List Bool):(pairB a b).length=2 * a.length+b.length+1:=by
  simp [pairB];omega
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem d39 {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':=by
  obtain rfl:f=f':=funext e
  exact h
private theorem d119 {A B C:Type} (φl:A → Option C) (φr:B → Option C) (x:List A)
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
private theorem d100 {A C:Type} (g:A → C) (l:List A) :
    l.filterMap (fun a=>some (g a))=l.map g:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [ih]
private theorem d160 {A C:Type} (l:List A) :
    l.filterMap (fun _:A=>(none:Option C))=[]:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp
theorem d117 :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>pairB p.1 p.2):=by
  have hA:ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(p.1,p.1++p.2)):=by
    refine d10 _ _ _
      (Sum.elim (fun b:Bool=>some (Sum.inl b)) (fun _:Bool=>none))
      (Sum.elim (fun b:Bool=>some (Sum.inr b)) (fun b:Bool=>some (Sum.inr b))) ?_
    rintro ⟨x,w⟩
    simp only [encodePair]
    rw [d119,d119,d100,d100,d100,d160]
    simp
  have hU:Lib.CPTs
      (fun a:List Bool=>a.map (fun _=>true)++[false]):=by
    refine fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some true))
      (fun _=>some false) () ?_
    intro a
    induction a with
    | nil=>rfl
    | cons b l ih =>
      simp only [fstRun,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢
      rw [← ih];rfl
  refine d39 (cpt_comp (cpt_comp hA (d38 hU)) d74) ?_
  rintro ⟨x,w⟩
  simp [pairB,un]
theorem d35 :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>if p.1=[] then p.2 else []):=by
  obtain ⟨c⟩:=d11 []
  have hI:=Iter.iter_polyTime (fun _:List Bool=>([]:List Bool)) c 0 (by simp)
  refine d39 (cpt_comp d84 hI) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil=>simp
  | cons b l=>simp [Function.iterate_succ_apply']
theorem d62 :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>if p.1=[] then [] else p.2):=by
  have hneg:Lib.CPTs
      (fun x:List Bool=>if x=[] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (d11 [true])) d35
  refine d39 (cpt_comp (d38 hneg) d35) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil=>simp
  | cons b l=>simp
theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf:ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x:List Bool=>x) (fun a=>if f a then [true] else []):=by
  have h:ComputableInPolyTime Computability.encodeBool (fun x:List Bool=>x)
      (fun b:Bool=>if b then [true] else []):=by
    refine d7 _ _ _ (fun b:Bool=>if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h
private def encT (u:List Bool):List Bool:=u.flatMap (fun b=>[true,b])
private def encF (v:List Bool):List Bool:=v.flatMap (fun b=>[false,b])
private def twD:Bool → Bool → Bool × Option Bool
  | true,true=>(true,some true)
  | _,_=>(false,none)
private theorem d137 (l:List Bool) :
    fstRun twD (fun _=>none) false l=[] ∧
      fstRun twD (fun _=>none) true l=l.takeWhile id:=by
  induction l with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b l ih=>cases b <;> simp [fstRun,twD,ih.1,ih.2]
private def e0D:Bool → Bool → Bool × Option Bool × Option Bool
  | false,true=>(false,none,none)
  | false,false=>(true,none,none)
  | true,b=>(true,some false,some b)
private theorem d83 (l:List Bool) :
    fstRun2 e0D (fun _=>none) true l=encF l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun2,e0D,encF,ih]
private theorem d73 (l:List Bool) :
    fstRun2 e0D (fun _=>none) false l=encF (l.dropWhile id).tail:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>cases b <;> simp [fstRun2,e0D,ih,d83]
private def mkD:Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d,false),t=>((d || !t,true),some (t || !d))
  | (d,true),b=>((d,false),some b)
private def mk (l:List Bool):List Bool:=fstRun mkD (fun _=>none) (false,false) l
private theorem d91 (q:Bool × Bool) (l:List Bool) :
    (fstRun mkD (fun _=>none) q l).length=l.length:=by
  induction l generalizing q with
  | nil=>rfl
  | cons b l ih=>obtain ⟨d,ph⟩:=q;cases ph <;> simp [fstRun,mkD,ih]
private theorem d130 (v:List Bool) :
    fstRun mkD (fun _=>none) (true,false) (encF v)=encF v:=by
  induction v with
  | nil=>rfl
  | cons b v ih=>simp [fstRun,mkD,encF] at ih ⊢;exact ih
private theorem d69 (u r:List Bool) :
    fstRun mkD (fun _=>none) (false,false) (encT u++r) =
      encT u++fstRun mkD (fun _=>none) (false,false) r:=by
  induction u with
  | nil=>rfl
  | cons b u ih=>simp [fstRun,mkD,encT] at ih ⊢;exact ih
private theorem mk_nil (u:List Bool):mk (encT u++encF [])=encT u++encF []:=by
  unfold mk;rw [d69];rfl
private theorem d153 (u:List Bool) (b:Bool) (v:List Bool) :
    mk (encT u++encF (b :: v))=encT (u++[b])++encF v:=by
  unfold mk
  rw [d69]
  have h:fstRun mkD (fun _=>none) (false,false) (encF (b :: v)) =
      true :: b :: encF v:=by
    have h':=d130 v
    simp [fstRun,mkD,encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]
private theorem d152 (k:ℕ):∀ u t:List Bool,
    mk^[k] (encT u++encF t)=encT (u++t.take k)++encF (t.drop k):=by
  induction k with
  | zero=>intro u t;simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil=>rw [mk_nil,ih];simp
    | cons b t=>rw [d153,ih];simp
private def dcD:Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none,t=>(some t,none)
  | some t,b=>(none,some (if t then Sum.inl b else Sum.inr b))
private theorem dcD_F (v:List Bool) :
    fstRun dcD (fun _=>none) none (encF v)=v.map Sum.inr:=by
  induction v with
  | nil=>rfl
  | cons b v ih=>simp [fstRun,dcD,encF] at ih ⊢;exact ih
private theorem dcD_T (u r:List Bool) :
    fstRun dcD (fun _=>none) none (encT u++r) =
      u.map Sum.inl++fstRun dcD (fun _=>none) none r:=by
  induction u with
  | nil=>rfl
  | cons b u ih=>simp [fstRun,dcD,encT] at ih ⊢;exact ih
private def rawDec (l:List (Bool ⊕ Bool)):List Bool × List Bool :=
  (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private theorem d68 (u v:List Bool) :
    rawDec (u.map Sum.inl++v.map Sum.inr)=(u,v):=by
  have h1:∀ x:List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact congrArg (a :: ·) ih
  have h2:∀ x:List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = []:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact ih
  have h3:∀ x:List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = []:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact ih
  have h4:∀ x:List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact congrArg (a :: ·) ih
  simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
theorem d34 :
    ComputableInPolyTime (fun x:List Bool=>x) encodePair unpairB:=by
  have hTw:Lib.CPTs
      (fun s:List Bool=>s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _=>none) true (fun s=>(d137 s).2.symm)
  have hE0:Lib.CPTs
      (fun s:List Bool=>encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _=>none) false (fun s=>(d73 s).symm)
  have hMk:Lib.CPTs mk :=
    fst_polyTime _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl)
  obtain ⟨cMk⟩:=hMk
  have hIt:=Iter.iter_polyTime mk cMk 0 (fun y=>by simp [mk,d91])
  have hDc:ComputableInPolyTime (fun x:List Bool=>x) (fun l:List (Bool ⊕ Bool)=>l)
      (fun l:List Bool=>fstRun dcD (fun _=>none) none l) :=
    fst_polyTime _ _ _ dcD (fun _=>none) none (fun _=>rfl)
  have hRaw:ComputableInPolyTime (fun l:List (Bool ⊕ Bool)=>l) encodePair rawDec:=by
    refine d10 _ _ _
      (fun s:Bool ⊕ Bool=>(Sum.getLeft? s).map Sum.inl)
      (fun s:Bool ⊕ Bool=>(Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec,encodePair,List.map_filterMap]
  refine d39 (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h:=d152 (s.takeWhile id).length [] (s.dropWhile id).tail
  have e:encT []++encF (s.dropWhile id).tail=encF (s.dropWhile id).tail:=rfl
  rw [e] at h
  simp only [h,List.nil_append]
  rw [dcD_T,dcD_F,d68]
  rfl
theorem cpt_iterB (g:List Bool → List Bool)
    (hg:Lib.CPTs g)
    (m:List Bool → ℕ) (a:ℕ)
    (hm:∀ y,m (g y) ≤ m y) (hgl:∀ y,(g y).length ≤ y.length+m y)
    (ha:∀ y,m y ≤ a * y.length+a) :
    Lib.CPTs
      (fun s:List Bool=>g^[(unpairB s).2.length] (unpairB s).1):=by
  obtain ⟨c⟩:=hg
  exact cpt_comp d34 (Iter.iter_polyTime_measure g c m a hm hgl ha)
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':=by
  obtain rfl:f=f':=funext e
  exact h
private def hdD:Bool → Bool → Bool × Option Bool
  | true,true=>(true,some true)
  | _,_=>(false,none)
private theorem d159 (l:List Bool) :
    fstRun hdD (fun _=>none) false l=[] ∧
      fstRun hdD (fun _=>none) true l=l.takeWhile id:=by
  induction l with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b l ih=>cases b <;> simp [fstRun,hdD,ih.1,ih.2]
theorem cpt_hd :
    Lib.CPTs hd :=
  fst_polyTime _ _ _ hdD (fun _=>none) true (fun s=>(d159 s).2.symm)
private def dnD:Bool → Bool → Bool × Option Bool
  | false,true=>(false,none)
  | false,false=>(true,none)
  | true,b=>(true,some b)
private theorem d135 (l:List Bool):fstRun dnD (fun _=>none) true l=l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun,dnD,ih]
private theorem d116 (l:List Bool) :
    fstRun dnD (fun _=>none) false l=(l.dropWhile id).tail:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>cases b <;> simp [fstRun,dnD,ih,d135]
theorem cpt_dropN :
    Lib.CPTs dropN :=
  fst_polyTime _ _ _ dnD (fun _=>none) false (fun s=>(d116 s).symm)
private def tlD:Bool → Bool → Bool × Option Bool
  | false,_=>(true,none)
  | true,b=>(true,some b)
private theorem d128 (l:List Bool):fstRun tlD (fun _=>none) true l=l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun,tlD,ih]
private theorem d102 (l:List Bool):fstRun tlD (fun _=>none) false l=l.tail:=by
  cases l with
  | nil=>rfl
  | cons b l=>simp [fstRun,tlD,d128]
theorem cpt_tail :
    Lib.CPTs
      (fun s:List Bool=>s.tail) :=
  fst_polyTime _ _ _ tlD (fun _=>none) false (fun s=>(d102 s).symm)
private theorem d118 (l:List Bool) :
    fstRun (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) () l=blank l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun,blank] at ih ⊢;exact ih
theorem cpt_blank :
    Lib.CPTs blank :=
  fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) ()
    (fun s=>(d118 s).symm)
theorem cpt_const (l:List Bool) :
    Lib.CPTs
      (fun _:List Bool=>l) :=
  d11 l
theorem cpt_unpairB1 :
    Lib.CPTs
      (fun s:List Bool=>(unpairB s).1) :=
  cptc (cpt_comp d34 d170) (fun _=>rfl)
theorem cpt_unpairB2 :
    Lib.CPTs
      (fun s:List Bool=>(unpairB s).2) :=
  cptc (cpt_comp d34 d169) (fun _=>rfl)
theorem cpt_app2 {u v:List Bool → List Bool}
    (hu:Lib.CPTs u)
    (hv:Lib.CPTs v) :
    Lib.CPTs
      (fun s=>u s++v s) :=
  cptc (cpt_comp (cpt_pair hu hv) d74) (fun _=>rfl)
theorem cpt_pairB2 {u v:List Bool → List Bool}
    (hu:Lib.CPTs u)
    (hv:Lib.CPTs v) :
    Lib.CPTs
      (fun s=>pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) d117) (fun _=>rfl)
theorem cpt_sel {f a b:List Bool → List Bool}
    (hf:Lib.CPTs f)
    (ha:Lib.CPTs a)
    (hb:Lib.CPTs b) :
    Lib.CPTs
      (fun s=>sel (f s) (a s) (b s)):=by
  have h1:=cpt_comp (cpt_pair hf ha) d35
  have h2:=cpt_comp (cpt_pair hf hb) d62
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h:f s=[] <;> simp [sel,h]
theorem cpt_iterLen {g cnt arg:List Bool → List Bool}
    (hg:Lib.CPTs g)
    (hgl:∀ s,(g s).length ≤ s.length)
    (hcnt:Lib.CPTs cnt)
    (harg:Lib.CPTs arg) :
    Lib.CPTs
      (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y=>by simpa using hgl y)
  exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
end Lib.Universal
end
section
namespace L8.R012.TightReadOnce
open PEqualNP.CircuitLowerBounds
def a3 (gs:List Gate) (w:List Bool):List Bool :=
  gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
theorem a91 (C:Circuit) (x:List Bool):C.wires x=a3 C.gates x:=rfl
theorem a18 (gs gs':List Gate) (w:List Bool) :
    a3 (gs++gs') w=a3 gs' (a3 gs w):=by
  simp [a3,List.foldl_append]
theorem a39 (gs:List Gate):∀ w:List Bool,
    ∃ t:List Bool,a3 gs w=w++t∧t.length=gs.length:=by
  induction gs with
  | nil=>intro w;exact ⟨[],by simp [a3],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i=>w.getD i false) :: t,?_,by simp [hl]⟩
    have:a3 (g :: gs) w
        = a3 gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
    rw [this,ht];simp
theorem a12 (gs:List Gate) (w:List Bool) :
    (a3 gs w).length=w.length+gs.length:=by
  obtain ⟨t,ht,hl⟩:=a39 gs w
  rw [ht];simp [hl]
theorem a28 (gs:List Gate) (w:List Bool) (i:ℕ) (h:i < w.length) :
    (a3 gs w).getD i false=w.getD i false:=by
  obtain ⟨t,ht,_⟩:=a39 gs w
  rw [ht,List.getD_append _ _ _ _ h]
def Ok (g:Gate):Prop :=
  g.inputs.length ≤ 2
variable {n:ℕ}
theorem a8 {α : Type} (L:List α) (S d : α) (j:ℕ) (h:j≠L.length) :
    (L++[S]).getD j d=L.getD j d:=by
  by_cases hj:j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
theorem a7 {α : Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
  simp
def reads (g:Gate):List ℕ :=
  match g.op with
  | .not=>g.inputs.take 1
  | _=>g.inputs
theorem a84 (g:Gate):(reads g).length ≤ g.inputs.length:=by
  cases h:g.op <;> simp [reads,h,Nat.min_le_right]
def a9 (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
  ((reads g).map fun a=>L.getD a ∅).foldr (· ∪ ·) ∅
theorem a60 (l:List ℕ) (F:ℕ → Finset (Fin n)) (i:Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
  induction l with
  | nil=>simp
  | cons b l ih=>simp [ih]
theorem a27 (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
    i ∈ a9 L g↔∃ a ∈ reads g,i ∈ L.getD a ∅ :=
  a60 _ _ _
def a37 (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
  gs.foldl (fun L g=>L++[a9 L g]) L
def a6 (n:ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n=>{i}
def Agree (x y:Fin n → Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
  L.length=w.length∧w.length=w'.length ∧
    ∀ j:ℕ,(∀ i ∈ L.getD j ∅,x i=y i) → w.getD j false=w'.getD j false
theorem a56 (g:Gate) (w w':List Bool)
    (h:∀ a ∈ reads g,w.getD a false=w'.getD a false) :
    g.op.eval (g.inputs.map fun a=>w.getD a false) =
      g.op.eval (g.inputs.map fun a=>w'.getD a false):=by
  by_cases hn:g.op = .not
  · rw [hn]
    cases hi:g.inputs with
    | nil=>simp [GateOp.eval,hi]
    | cons a l =>
      have ha:=h a (by simp [reads,hn,hi])
      change (!w.getD a false) = !w'.getD a false
      rw [ha]
  · have he:g.inputs.map (fun a=>w.getD a false) =
        g.inputs.map (fun a=>w'.getD a false):=by
      apply List.map_congr_left
      intro a ha
      exact h a (by cases ho:g.op <;> simp_all [reads])
    rw [he]
theorem a40 (x y:Fin n → Bool) (gs:List Gate) :
    ∀ (L:List (Finset (Fin n))) (w w':List Bool),Agree x y L w w' →
      Agree x y (a37 gs L) (a3 gs w) (a3 gs w'):=by
  induction gs with
  | nil=>intro L w w' h;exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1,h2,h3⟩:=h
    apply ih (L++[a9 L g])
      (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
      (w'++[g.op.eval (g.inputs.map fun i=>w'.getD i false)])
    refine ⟨by simp [h1],by simp [h2],?_⟩
    intro j hj
    by_cases hjl:j=L.length
    · subst hjl
      rw [a7] at hj
      rw [h1,a7,h2,a7]
      apply a56
      intro a ha
      exact h3 a (fun i hi=>hj i ((a27 L g i).2 ⟨a,ha,hi⟩))
    · rw [a8 _ _ _ _ hjl] at hj
      rw [a8 _ _ _ _ (by omega),a8 _ _ _ _ (by omega)]
      exact h3 j hj
theorem a58 (x y:Fin n → Bool) :
    Agree x y (a6 n) (List.ofFn x) (List.ofFn y):=by
  refine ⟨by simp [a6],by simp,?_⟩
  intro j hj
  by_cases hjn:j < n
  · have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [a6,hjn])
    simp [hjn,hx]
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
def Cnt (t:ℕ) (L:List (Finset (Fin n))):Prop :=
  ∀ W:Finset ℕ,(W.biUnion fun j=>L.getD j ∅).card ≤ t+W.card
theorem a47:Cnt 0 (a6 n):=by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn:j < n
  · simp [a6,hjn]
  · rw [List.getD_eq_default _ _ (by simp [a6];omega)];simp
theorem a87 (t:ℕ) (L:List (Finset (Fin n))) (g:Gate) (hg:g.inputs.length ≤ 2)
    (h:Cnt t L):Cnt (t+1) (L++[a9 L g]):=by
  intro W
  by_cases hW:L.length ∈ W
  · have hsub:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j=>L.getD j ∅):=by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j,hjW,hij⟩:=hi
      by_cases hjl:j=L.length
      · subst hjl
        rw [a7] at hij
        obtain ⟨a,ha,hia⟩:=(a27 L g i).1 hij
        exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
      · rw [a8 _ _ _ _ hjl] at hij
        exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
    have hc1:(W.erase L.length ∪ (reads g).toFinset).card ≤ (W.card - 1)+2:=by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (le_trans (a84 g) hg)) _
    have hWpos:1 ≤ W.card:=Finset.card_pos.2 ⟨_,hW⟩
    have:=h (W.erase L.length ∪ (reads g).toFinset)
    have:=Finset.card_le_card hsub
    omega
  · have heq:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅)
        = (W.biUnion fun j=>L.getD j ∅):=by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact a8 _ _ _ _ (fun e=>hW (e ▸ hj))
    rw [heq]
    have:=h W
    omega
theorem a53 (gs:List Gate):∀ (t:ℕ) (L:List (Finset (Fin n))),
    (∀ g ∈ gs,Ok g) → Cnt t L → Cnt (t+gs.length) (a37 gs L):=by
  induction gs with
  | nil=>intro t L _ h;exact h
  | cons g gs ih =>
    intro t L hok h
    have:=ih (t+1) (L++[a9 L g]) (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg'))
      (a87 t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega]
    exact this
theorem a20 (C:Circuit) (n k w:Nat)
    (hk:k ≤ C.gates.length) (hw:w < n+k) (x:Fin n → Bool) :
    (C.wires (List.ofFn x)).getD w false =
      (a3 (C.gates.take k) (List.ofFn x)).getD w false:=by
  change (a3 C.gates (List.ofFn x)).getD w false=_
  conv_lhs=>rw [← List.take_append_drop k C.gates]
  rw [a18]
  apply a28
  rw [a12]
  simpa [List.length_take,Nat.min_eq_left hk] using hw
theorem a70 (C:Circuit) (n k w:Nat)
    (hk:k ≤ C.gates.length) (hw:w < n+k)
    (hfan:∀ g ∈ C.gates,g.inputs.length ≤ 2) :
    ∃ S:Finset (Fin n),S.card ≤ k+1 ∧
      ∀ x y:Fin n → Bool,(∀ i ∈ S,x i=y i) →
        (C.wires (List.ofFn x)).getD w false =
          (C.wires (List.ofFn y)).getD w false:=by
  let S:=(a37 (C.gates.take k) (a6 n)).getD w ∅
  refine ⟨S,?_,?_⟩
  · have hc:=a53 (C.gates.take k) 0 (a6 n)
      (fun g hg=>hfan g (List.mem_of_mem_take hg)) a47 {w}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,
      List.length_take,Nat.min_eq_left hk] using hc
  · intro x y heq
    rw [a20 C n k w hk hw x,a20 C n k w hk hw y]
    exact (a40 x y (C.gates.take k) _ _ _ (a58 x y)).2.2 w heq
theorem a41 (C:Circuit) (n k w:Nat)
    (hk:k ≤ C.gates.length) (hw:w < n+k)
    (hfan:∀ g ∈ C.gates,g.inputs.length ≤ 2)
    (E:Finset (Fin n))
    (hsens:∀ i ∈ E,∃ x y:Fin n → Bool,
      (∀ j,j≠i → x j=y j) ∧
        (C.wires (List.ofFn x)).getD w false ≠
          (C.wires (List.ofFn y)).getD w false) :
    E.card ≤ k+1:=by
  obtain ⟨S,hcard,hdep⟩:=a70 C n k w hk hw hfan
  apply le_trans (Finset.card_le_card (t:=S) ?_) hcard
  intro i hi
  by_contra hni
  obtain ⟨x,y,hxy,hne⟩:=hsens i hi
  apply hne (hdep x y ?_)
  intro j hj
  apply hxy j
  intro hji
  subst j
  exact hni hj
def RO (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool):Prop :=
  ∀ Q:Finset (Fin n) → ((Fin n → Bool) → Bool) → Prop,
    (∀ i:Fin n,Q {i} (fun x=>x i)) →
    (∀ A B a b,Disjoint A B → Q A a → Q B b →
      Q (A ∪ B) (fun x=>a x && b x)∧Q (A ∪ B) (fun x=>a x || b x)) → Q S f
theorem a34 (i:Fin n):RO {i} (fun x=>x i):=fun _ hl _=>hl i
theorem ro_and {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b) :
    RO (A ∪ B) (fun x=>a x && b x) :=
  fun Q hl hj=>(hj A B a b hd (ha Q hl hj) (hb Q hl hj)).1
theorem ro_or {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b) :
    RO (A ∪ B) (fun x=>a x || b x) :=
  fun Q hl hj=>(hj A B a b hd (ha Q hl hj) (hb Q hl hj)).2
def Fam (L:List (Finset (Fin n))) (F:ℕ → (Fin n → Bool) → Bool) (W:Finset ℕ):Prop :=
  (∀ w ∈ W,RO (L.getD w ∅) (F w)) ∧
  (∀ w ∈ W,∀ v ∈ W,w≠v → Disjoint (L.getD w ∅) (L.getD v ∅))
def Tight (t:ℕ) (L:List (Finset (Fin n))) (F:ℕ → (Fin n → Bool) → Bool):Prop :=
  ∀ W:Finset ℕ,(W.biUnion fun j=>L.getD j ∅).card=t+W.card → Fam L F W
theorem a71:Tight 0 (a6 n) (fun j x=>(List.ofFn x).getD j false):=by
  intro W heq
  have hvalid:∀ j ∈ W,j < n:=by
    intro j hj
    by_contra hn
    have hz:(a6 n).getD j ∅ = ∅ :=
      List.getD_eq_default _ _ (by simp [a6];omega)
    have he:=heq
    rw [← Finset.insert_erase hj,Finset.biUnion_insert,hz,Finset.empty_union] at he
    rw [Finset.insert_erase hj] at he
    have hc:=a47 (n:=n) (W.erase j)
    have hcard:=Finset.card_erase_add_one hj
    omega
  constructor
  · intro j hj
    have hv:=hvalid j hj
    have hs:(a6 n).getD j ∅ = {⟨j,hv⟩}:=by simp [a6,hv]
    have hf:(fun x:Fin n → Bool=>(List.ofFn x).getD j false)=(fun x=>x ⟨j,hv⟩):=by
      funext x;simp [hv]
    rw [hs]
    change RO {⟨j,hv⟩} (fun x:Fin n → Bool=>(List.ofFn x).getD j false)
    rw [hf]
    exact a34 _
  · intro j hj k hk hne
    have hjn:=hvalid j hj
    have hkn:=hvalid k hk
    simpa [a6,hjn,hkn,Fin.ext_iff] using hne
theorem a78 (L:List (Finset (Fin n))) (g:Gate) (W:Finset ℕ)
    (hW:L.length ∈ W) :
    (W.biUnion fun j=>(L++[a9 L g]).getD j ∅) =
      ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j=>L.getD j ∅):=by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_biUnion] at hi ⊢
    obtain ⟨j,hjW,hij⟩:=hi
    by_cases hjl:j=L.length
    · subst hjl
      rw [a7] at hij
      obtain ⟨a,ha,hia⟩:=(a27 L g i).1 hij
      exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
    · rw [a8 _ _ _ _ hjl] at hij
      exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
  · intro hi
    obtain ⟨j,hj,hi⟩:=Finset.mem_biUnion.mp hi
    rcases Finset.mem_union.mp hj with hj | hj
    · refine Finset.mem_biUnion.mpr ⟨j,Finset.mem_of_mem_erase hj,?_⟩
      rw [a8 _ _ _ _ (Finset.ne_of_mem_erase hj)]
      exact hi
    · refine Finset.mem_biUnion.mpr ⟨L.length,hW,?_⟩
      rw [a7]
      exact (a27 L g i).mpr ⟨j,List.mem_toFinset.mp hj,hi⟩
theorem a62 (g:Gate)
    (ho:g.op = .and∨g.op = .or∨g.op = .not)
    (hlen:g.inputs.length ≤ 2) (hcard:(reads g).toFinset.card=2) :
    ∃ a b,g.inputs=[a,b]∧a≠b∧(g.op = .and∨g.op = .or):=by
  have hn:g.op ≠ .not:=by
    intro hn
    have hc:=List.toFinset_card_le (reads g)
    have hl:(reads g).length ≤ 1:=by simp [reads,hn]
    omega
  have hop:g.op = .and∨g.op = .or:=by rcases ho with h | h | h <;> simp_all
  have hr:reads g=g.inputs:=by rcases hop with h | h <;> simp [reads,h]
  rw [hr] at hcard
  rcases hi:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
  · simp [hi] at hcard
  · simp [hi] at hcard
  · refine ⟨a,b,rfl,?_,hop⟩
    intro hab
    simp [hi,hab] at hcard
  · simp [hi] at hlen
def nextF (L:List (Finset (Fin n))) (F:ℕ → (Fin n → Bool) → Bool) (g:Gate)
    (j:ℕ) (x:Fin n → Bool):Bool :=
  if j=L.length then g.op.eval (g.inputs.map fun a=>F a x) else F j x
theorem a80 (t:ℕ) (L:List (Finset (Fin n))) (F:ℕ → (Fin n → Bool) → Bool)
    (g:Gate) (ho:g.op = .and∨g.op = .or∨g.op = .not) (hlen:g.inputs.length ≤ 2)
    (hc:Cnt t L) (ht:Tight t L F) :
    Tight (t+1) (L++[a9 L g]) (nextF L F g):=by
  intro W heq
  have hW:L.length ∈ W:=by
    by_contra hn
    have hU:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅) =
        (W.biUnion fun j=>L.getD j ∅):=by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact a8 _ _ _ _ (fun h=>hn (h ▸ hj))
    rw [hU] at heq
    have:=hc W
    omega
  let E:=W.erase L.length
  let B:=(reads g).toFinset
  let P:=E ∪ B
  have hEc:E.card+1=W.card:=Finset.card_erase_add_one hW
  have hBc:B.card ≤ 2:=le_trans (List.toFinset_card_le _) (le_trans (a84 g) hlen)
  have hPc:P.card ≤ E.card+B.card:=Finset.card_union_le _ _
  have hU:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅) =
      (P.biUnion fun j=>L.getD j ∅):=a78 L g W hW
  rw [hU] at heq
  have hcP:=hc P
  have hB2:B.card=2:=by omega
  have hPexact:P.card=E.card+B.card:=by omega
  have hTexact:(P.biUnion fun j=>L.getD j ∅).card=t+P.card:=by omega
  have hEB:Disjoint E B:=Finset.card_union_eq_card_add_card.mp hPexact
  obtain ⟨a,b,hin,hab,hop⟩:=a62 g ho hlen hB2
  have hreads:reads g=[a,b]:=by rcases hop with h | h <;> simp [reads,h,hin]
  have haB:a ∈ B:=by simp [B,hreads]
  have hbB:b ∈ B:=by simp [B,hreads]
  have haP:a ∈ P:=Finset.mem_union_right _ haB
  have hbP:b ∈ P:=Finset.mem_union_right _ hbB
  have hF:=ht P hTexact
  have hEP:E ⊆ P:=Finset.subset_union_left
  have hneA:∀ w ∈ E,w≠a:=by
    intro w hw hwa;subst w
    exact Finset.disjoint_left.mp hEB hw haB
  have hneB:∀ w ∈ E,w≠b:=by
    intro w hw hwb;subst w
    exact Finset.disjoint_left.mp hEB hw hbB
  have hS:a9 L g=L.getD a ∅ ∪ L.getD b ∅ := by simp [a9,hreads]
  have hnew:RO (a9 L g) (nextF L F g L.length):=by
    rw [hS]
    have hd:=hF.2 a haP b hbP hab
    rcases hop with hop | hop
    · have hf:nextF L F g L.length=(fun x=>F a x && F b x):=by
        funext x;simp [nextF,hin,hop,GateOp.eval]
      rw [hf];exact ro_and hd (hF.1 a haP) (hF.1 b hbP)
    · have hf:nextF L F g L.length=(fun x=>F a x || F b x):=by
        funext x;simp [nextF,hin,hop,GateOp.eval]
      rw [hf];exact ro_or hd (hF.1 a haP) (hF.1 b hbP)
  have hother:∀ w ∈ E,(L++[a9 L g]).getD w ∅ = L.getD w ∅ :=
    fun w hw=>a8 _ _ _ _ (Finset.ne_of_mem_erase hw)
  have hnewdis:∀ w ∈ E,Disjoint (a9 L g) (L.getD w ∅):=by
    intro w hw
    rw [hS,Finset.disjoint_union_left]
    exact ⟨hF.2 a haP w (hEP hw) (hneA w hw).symm,
      hF.2 b hbP w (hEP hw) (hneB w hw).symm⟩
  constructor
  · intro w hw
    by_cases hwk:w=L.length
    · subst w
      rw [a7]
      exact hnew
    · have hwE:w ∈ E:=Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      have hf:nextF L F g w=F w:=by funext x;simp [nextF,hwk]
      rw [hf]
      exact hF.1 w (hEP hwE)
  · intro w hw v hv hne
    by_cases hwk:w=L.length
    · subst w
      have hvE:v ∈ E:=Finset.mem_erase.mpr ⟨hne.symm,hv⟩
      rw [a7,hother v hvE]
      exact hnewdis v hvE
    · have hwE:w ∈ E:=Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      by_cases hvk:v=L.length
      · subst v
        rw [a7]
        exact (hnewdis w hwE).symm
      · have hvE:v ∈ E:=Finset.mem_erase.mpr ⟨hvk,hv⟩
        rw [hother v hvE]
        exact hF.2 w (hEP hwE) v (hEP hvE) hne
theorem a59 (gs:List Gate):∀ (t:ℕ) (L:List (Finset (Fin n)))
    (v:(Fin n → Bool) → List Bool),(∀ x,(v x).length=L.length) →
    (∀ g ∈ gs,(g.op = .and∨g.op = .or∨g.op = .not)∧g.inputs.length ≤ 2) →
    Cnt t L → Tight t L (fun j x=>(v x).getD j false) →
    Tight (t+gs.length) (a37 gs L) (fun j x=>(a3 gs (v x)).getD j false):=by
  induction gs with
  | nil=>intro t L v hv _ hc ht;exact ht
  | cons g gs ih =>
    intro t L v hv hg hc ht
    let v':=fun x:Fin n → Bool=>v x++[g.op.eval (g.inputs.map fun a=>(v x).getD a false)]
    have hv':∀ x,(v' x).length=(L++[a9 L g]).length:=by
      intro x;simp [v',hv x]
    have hf:(fun j x=>(v' x).getD j false) =
        nextF L (fun j x=>(v x).getD j false) g:=by
      funext j x
      by_cases hj:j=L.length
      · subst j
        simp only [nextF,ite_true]
        dsimp only [v']
        rw [← hv x,a7]
      · simp only [nextF,hj,ite_false]
        exact a8 _ _ _ _ (by rw [hv x];exact hj)
    have hgg:=hg g List.mem_cons_self
    have ht':Tight (t+1) (L++[a9 L g]) (fun j x=>(v' x).getD j false):=by
      rw [hf]
      exact a80 t L _ g hgg.1 hgg.2 hc ht
    have hres:=ih (t+1) (L++[a9 L g]) v' hv'
      (fun g' h=>hg g' (List.mem_cons_of_mem g h)) (a87 t L g hgg.2 hc) ht'
    simpa only [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega,
      a37,a3,List.foldl_cons,v'] using hres
theorem a65 (C:Circuit) (n k w:Nat)
    (hk:k ≤ C.gates.length) (hw:w < n+k)
    (hfan:∀ g ∈ C.gates,(g.op = .and∨g.op = .or∨g.op = .not)∧g.inputs.length ≤ 2)
    (E:Finset (Fin n)) (hE:E.card=k+1)
    (hsens:∀ i ∈ E,∃ x y:Fin n → Bool,
      (∀ j,j≠i → x j=y j) ∧
      (C.wires (List.ofFn x)).getD w false≠(C.wires (List.ofFn y)).getD w false) :
    RO E (fun x=>(C.wires (List.ofFn x)).getD w false):=by
  let gs:=C.gates.take k
  let L:=a37 gs (a6 n)
  let S:=L.getD w ∅
  have hlen:gs.length=k:=by simp [gs,List.length_take,Nat.min_eq_left hk]
  have hfan':∀ g ∈ gs,(g.op = .and∨g.op = .or∨g.op = .not)∧g.inputs.length ≤ 2 :=
    fun g hg=>hfan g (List.mem_of_mem_take hg)
  have hc:=a53 gs 0 (a6 n) (fun g hg=>(hfan' g hg).2) a47
  have hSc:S.card ≤ k+1:=by
    have:=hc {w}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using this
  have hdep:∀ x y:Fin n → Bool,(∀ i ∈ S,x i=y i) →
      (C.wires (List.ofFn x)).getD w false=(C.wires (List.ofFn y)).getD w false:=by
    intro x y hxy
    rw [a20 C n k w hk hw x,a20 C n k w hk hw y]
    exact (a40 x y gs _ _ _ (a58 x y)).2.2 w hxy
  have hsub:E ⊆ S:=by
    intro i hi
    by_contra hni
    obtain ⟨x,y,hxy,hne⟩:=hsens i hi
    apply hne (hdep x y ?_)
    intro j hj
    exact hxy j (fun h=>hni (h ▸ hj))
  have hES:E=S:=Finset.eq_of_subset_of_card_le hsub (by omega)
  have hT:=a59 gs 0 (a6 n) (fun x=>List.ofFn x)
    (fun x=>by simp [a6]) hfan' a47 a71
  have heq:(({w}:Finset ℕ).biUnion fun j=>L.getD j ∅).card=(0+gs.length)+({w}:Finset ℕ).card:=by
    have hS:S.card=k+1:=by rw [←hES];exact hE
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using hS
  have hR:=(hT {w} heq).1 w (Finset.mem_singleton_self w)
  change RO S _ at hR
  rw [←hES] at hR
  have hf:(fun x:Fin n → Bool=>(a3 gs (List.ofFn x)).getD w false) =
      (fun x=>(C.wires (List.ofFn x)).getD w false):=by
    funext x;exact (a20 C n k w hk hw x).symm
  change RO E (fun x:Fin n → Bool=>(a3 gs (List.ofFn x)).getD w false) at hR
  rw [hf] at hR
  exact hR
end L8.R012.TightReadOnce
namespace L8.R012.ReadOncePath
open L8.R012.TightReadOnce
variable {n:ℕ} {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
theorem ro_nonempty (h:RO S f):S.Nonempty:=by
  apply h (fun S _=>S.Nonempty)
  · intro i;exact Finset.singleton_nonempty i
  · intro A B a b hd ha hb
    exact ⟨ha.mono Finset.subset_union_left,ha.mono Finset.subset_union_left⟩
theorem a89 (h:RO S f) (x:Fin n → Bool) (hx:∀ i ∈ S,x i=false):f x=false:=by
  apply h (fun S f=>∀ x,(∀ i ∈ S,x i=false) → f x=false) ?_ ?_ x hx
  · intro i x hx;exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x hx
    · dsimp only
      rw [ha x (fun i hi=>hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi=>hx i (Finset.mem_union_right _ hi))];rfl
    · dsimp only
      rw [ha x (fun i hi=>hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi=>hx i (Finset.mem_union_right _ hi))];rfl
theorem a82 (h:RO S f) (x y:Fin n → Bool) (hx:∀ i ∈ S,x i=y i):f x=f y:=by
  apply h (fun S f=>∀ x y,(∀ i ∈ S,x i=y i) → f x=f y) ?_ ?_ x y hx
  · intro i x y hx;exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x y hx <;> dsimp only <;>
      rw [ha x y (fun i hi=>hx i (Finset.mem_union_left _ hi)),
        hb x y (fun i hi=>hx i (Finset.mem_union_right _ hi))]
theorem a63 (h:RO S f) (x y:Fin n → Bool)
    (hxy:∀ i,x i=true → y i=true) (hf:f x=true):f y=true:=by
  apply h (fun _ f=>∀ x y,(∀ i,x i=true → y i=true) → f x=true → f y=true) ?_ ?_ x y hxy hf
  · intro i x y hxy hf;exact hxy i hf
  · intro A B a b hd ha hb
    constructor
    · intro x y hxy hf
      simp only [Bool.and_eq_true] at hf ⊢
      exact ⟨ha x y hxy hf.1,hb x y hxy hf.2⟩
    · intro x y hxy hf
      simp only [Bool.or_eq_true] at hf ⊢
      exact hf.elim (fun h=>Or.inl (ha x y hxy h)) (fun h=>Or.inr (hb x y hxy h))
theorem ro_split (h:RO S f) :
    (∃ i:Fin n,S={i}∧f=(fun x=>x i)) ∨
    ∃ A B a b,Disjoint A B∧S=A∪B∧RO A a∧RO B b ∧
      (f=(fun x=>a x && b x)∨f=(fun x=>a x || b x)):=by
  let Q:=fun S f=>RO S f ∧
    ((∃ i:Fin n,S={i}∧f=(fun x=>x i)) ∨
    ∃ A B a b,Disjoint A B∧S=A∪B∧RO A a∧RO B b ∧
      (f=(fun x=>a x && b x)∨f=(fun x=>a x || b x)))
  have hQ:Q S f:=h Q (fun i=>⟨a34 i,Or.inl ⟨i,rfl,rfl⟩⟩) (by
    intro A B a b hd ha hb
    constructor
    · exact ⟨ro_and hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inl rfl⟩⟩
    · exact ⟨ro_or hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inr rfl⟩⟩)
  exact hQ.2
def pair (i j:Fin n):Fin n → Bool:=fun k=>decide (k=i∨k=j)
def single (i:Fin n):Fin n → Bool:=fun k=>decide (k=i)
theorem a54 (i j:Fin n):pair i j=pair j i:=by funext k;simp [pair,or_comm]
theorem a66 (h:RO S f) (i j:Fin n) (hi:i ∉ S) (hj:j ∉ S):f (pair i j)=false:=by
  apply a89 h
  intro k hk
  simp only [pair,decide_eq_false_iff_not,not_or]
  exact ⟨fun hki=>hi (hki ▸ hk),fun hkj=>hj (hkj ▸ hk)⟩
theorem a26 (h:RO S f) (i j:Fin n) (hj:j ∉ S) :
    f (pair i j)=f (single i):=by
  apply a82 h
  intro k hk
  have hkj:k≠j:=fun hkj=>hj (hkj ▸ hk)
  simp [pair,single,hkj]
theorem a45 (h:RO S f) (i j:Fin n) (hi:i ∉ S) :
    f (pair i j)=f (single j):=by rw [a54];exact a26 h j i hi
end L8.R012.ReadOncePath
namespace L8.R017
open L8.R012.TightReadOnce L8.R012.ReadOncePath
variable {n:ℕ}
def NoSingle (f:(Fin n → Bool) → Bool):Prop:=∀ i,f (single i)=false
def a17 (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool):Prop :=
  ∀ i ∈ S,∃ j ∈ S,f (pair i j)=true
def a76 (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool):Prop :=
  ∀ x,f x=true↔∃ i ∈ S,∃ j ∈ S,f (pair i j)=true∧x i=true∧x j=true
theorem a88 {i:Fin n} {x:Fin n → Bool} (hi:x i=true) :
    ∀ j,single i j=true → x j=true:=by
  intro j hj
  have:j=i:=by simpa [single] using hj
  simpa [this] using hi
theorem a75 {i j:Fin n} {x:Fin n → Bool} (hi:x i=true) (hj:x j=true) :
    ∀ t,pair i j t=true → x t=true:=by
  intro t ht
  have:t=i∨t=j:=by simpa [pair] using ht
  rcases this with rfl | rfl <;> assumption
theorem a42 {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (x:Fin n → Bool) (hx:f x=true):∃ i ∈ S,x i=true:=by
  by_contra hn
  have hz:∀ i ∈ S,x i=false:=by
    intro i hi
    have h:x i≠true:=fun ht=>hn ⟨i,hi,ht⟩
    exact Bool.eq_false_iff.mpr h
  have h:=a89 hf x hz
  rw [hx] at h
  contradiction
theorem ro_all_singletons {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (hs:∀ i ∈ S,f (single i)=true) (x:Fin n → Bool) :
    f x=true↔∃ i ∈ S,x i=true:=by
  constructor
  · exact a42 hf x
  · rintro ⟨i,hi,hx⟩
    exact a63 hf _ _ (a88 hx) (hs i hi)
theorem a21 {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hc:a17 (A ∪ B) (fun x=>a x && b x)) :
    (∀ i ∈ A,a (single i)=true)∧(∀ j ∈ B,b (single j)=true):=by
  constructor
  · intro i hi
    obtain ⟨j,hj,hp⟩:=hc i (Finset.mem_union_left _ hi)
    have hia:i ∉ B:=Finset.disjoint_left.mp hd hi
    have hja:j ∉ A:=by
      intro hjA
      have hjB:j ∉ B:=Finset.disjoint_left.mp hd hjA
      have hz:=a66 hb i j hia hjB
      simp only [hz,Bool.and_false] at hp
      contradiction
    have hpA:a (pair i j)=true:=(by simpa only [Bool.and_eq_true] using hp:a (pair i j)=true∧b (pair i j)=true).1
    rwa [a26 ha i j hja] at hpA
  · intro i hi
    obtain ⟨j,hj,hp⟩:=hc i (Finset.mem_union_right _ hi)
    have hia:i ∉ A:=Finset.disjoint_right.mp hd hi
    have hja:j ∉ B:=by
      intro hjB
      have hjA:j ∉ A:=Finset.disjoint_right.mp hd hjB
      have hz:=a66 ha i j hia hjA
      simp only [hz,Bool.false_and] at hp
      contradiction
    have hpB:b (pair i j)=true:=(by simpa only [Bool.and_eq_true] using hp:a (pair i j)=true∧b (pair i j)=true).2
    rwa [a26 hb i j hja] at hpB
theorem a51 {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hs:NoSingle (fun x=>a x || b x))
    (hc:a17 (A ∪ B) (fun x=>a x || b x)):a17 A a:=by
  intro i hi
  obtain ⟨j,hj,hp⟩:=hc i (Finset.mem_union_left _ hi)
  have hia:i ∉ B:=Finset.disjoint_left.mp hd hi
  have hsA:∀ t,a (single t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).1
  have hsB:∀ t,b (single t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).2
  have hpA:a (pair i j)=true:=by
    have hp':a (pair i j)=true∨b (pair i j)=true:=by simpa only [Bool.or_eq_true] using hp
    rcases hp' with h | h
    · exact h
    · rw [a45 hb i j hia,hsB j] at h
      contradiction
  have hjA:j ∈ A:=by
    by_contra hjA
    rw [a26 ha i j hjA,hsA i] at hpA
    contradiction
  exact ⟨j,hjA,hpA⟩
theorem a43 {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (hs:NoSingle f) (hc:a17 S f):a76 S f:=by
  let Q:=fun (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool)=>RO S f∧(NoSingle f → a17 S f → a76 S f)
  have hQ:Q S f:=hf Q (by
    intro i
    refine ⟨a34 i,?_⟩
    intro hs hc
    have h:=hs i
    simp [single] at h) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1,?_⟩
      intro hs hc x
      constructor
      · intro hx
        obtain ⟨hi,hj⟩:=a21 hd ha.1 hb.1 hc
        obtain ⟨i,hiA,hxi⟩:=a42 ha.1 x (by simpa only [Bool.and_eq_true] using hx:a x=true∧b x=true).1
        obtain ⟨j,hjB,hxj⟩:=a42 hb.1 x (by simpa only [Bool.and_eq_true] using hx:a x=true∧b x=true).2
        refine ⟨i,Finset.mem_union_left _ hiA,j,Finset.mem_union_right _ hjB,?_,hxi,hxj⟩
        have hjA:j ∉ A:=Finset.disjoint_right.mp hd hjB
        have hiB:i ∉ B:=Finset.disjoint_left.mp hd hiA
        dsimp only
        rw [a26 ha.1 i j hjA,a45 hb.1 i j hiB,hi i hiA,hj j hjB]
        rfl
      · rintro ⟨i,hi,j,hj,hp,hxi,hxj⟩
        exact a63 (ro_and hd ha.1 hb.1) _ _ (a75 hxi hxj) hp
    · refine ⟨ro_or hd ha.1 hb.1,?_⟩
      intro hs hc x
      have hsA:NoSingle a:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).1
      have hsB:NoSingle b:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).2
      have hcA:=a51 hd ha.1 hb.1 hs hc
      have hcB:a17 B b:=by
        have hs':NoSingle (fun x=>b x || a x):=by simpa only [Bool.or_comm] using hs
        have hc':a17 (B ∪ A) (fun x=>b x || a x):=by
          simpa only [Finset.union_comm,Bool.or_comm] using hc
        exact a51 hd.symm hb.1 ha.1 hs' hc'
      constructor
      · intro hx
        have hx':a x=true∨b x=true:=by simpa only [Bool.or_eq_true] using hx
        rcases hx' with h | h
        · obtain ⟨i,hi,j,hj,hp,hxi,hxj⟩:=(ha.2 hsA hcA x).mp h
          refine ⟨i,Finset.mem_union_left _ hi,j,Finset.mem_union_left _ hj,?_,hxi,hxj⟩
          simp only [hp,Bool.true_or]
        · obtain ⟨i,hi,j,hj,hp,hxi,hxj⟩:=(hb.2 hsB hcB x).mp h
          refine ⟨i,Finset.mem_union_right _ hi,j,Finset.mem_union_right _ hj,?_,hxi,hxj⟩
          simp only [hp,Bool.or_true]
      · rintro ⟨i,hi,j,hj,hp,hxi,hxj⟩
        exact a63 (ro_or hd ha.1 hb.1) _ _ (a75 hxi hxj) hp)
  exact hQ.2 hs hc
end L8.R017
namespace L8.R017
open L8.R012.TightReadOnce L8.R012.ReadOncePath
variable {n:ℕ}
theorem a4 {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hs:NoSingle (fun x=>a x || b x))
    {i j:Fin n} (hi:i ∈ A) (hp:(a (pair i j) || b (pair i j))=true) :
    j ∈ A∧a (pair i j)=true:=by
  have hiB:i ∉ B:=Finset.disjoint_left.mp hd hi
  have hsA:∀ t,a (single t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).1
  have hsB:∀ t,b (single t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).2
  have hpA:a (pair i j)=true:=by
    rcases Bool.or_eq_true_iff.mp hp with h | h
    · exact h
    · rw [a45 hb i j hiB,hsB j] at h
      contradiction
  refine ⟨?_,hpA⟩
  by_contra hjA
  rw [a26 ha i j hjA,hsA i] at hpA
  contradiction
theorem a29 {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hc:a17 (A ∪ B) (fun x=>a x && b x))
    {i j:Fin n} (hi:i ∈ A) (hj:j ∈ B) :
    (a (pair i j) && b (pair i j))=true:=by
  obtain ⟨hsA,hsB⟩:=a21 hd ha hb hc
  have hiB:i ∉ B:=Finset.disjoint_left.mp hd hi
  have hjA:j ∉ A:=Finset.disjoint_right.mp hd hj
  rw [a26 ha i j hjA,a45 hb i j hiB,hsA i hi,hsB j hj]
  rfl
theorem a0 {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (hb:RO B b)
    {i j:Fin n} (hi:i ∈ A) (hp:(a (pair i j) && b (pair i j))=true) :
    j ∈ B:=by
  by_contra hjB
  have hiB:i ∉ B:=Finset.disjoint_left.mp hd hi
  rw [a66 hb i j hiB hjB,Bool.and_false] at hp
  contradiction
def Matched (mate:Fin n → Fin n) (color:Fin n → Bool)
    (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool):Prop :=
  NoSingle f ∧
  (∀ i ∈ S,mate i ∈ S) ∧
  (∀ i ∈ S,f (pair i (mate i))=true) ∧
  (∀ i j,color i≠color j → j≠mate i → f (pair i j)=false)
theorem a23 {mate:Fin n → Fin n} {color:Fin n → Bool}
    {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool} (h:Matched mate color S f) :
    a17 S f:=fun i hi=>⟨mate i,h.2.1 i hi,h.2.2.1 i hi⟩
theorem a24 {mate:Fin n → Fin n} {color:Fin n → Bool}
    {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hm:Matched mate color (A ∪ B) (fun x=>a x || b x)) :
    Matched mate color A a:=by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    exact (Bool.or_eq_false_iff.mp (hm.1 i)).1
  · intro i hi
    exact (a4 hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).1
  · intro i hi
    exact (a4 hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).2
  · intro i j hc hj
    exact (Bool.or_eq_false_iff.mp (hm.2.2.2 i j hc hj)).1
theorem a35 {mate:Fin n → Fin n} {color:Fin n → Bool}
    {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hm:Matched mate color (A ∪ B) (fun x=>a x || b x)) :
    Matched mate color B b:=by
  have h:Matched mate color (B ∪ A) (fun x=>b x || a x):=by
    simpa only [Finset.union_comm,Bool.or_comm] using hm
  exact a24 hd.symm hb ha h
theorem a13 {mate:Fin n → Fin n} {color:Fin n → Bool}
    (hmi:Function.Involutive mate) (hcol:∀ i,color (mate i)≠color i)
    {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
    (hm:Matched mate color (A ∪ B) (fun x=>a x && b x)) :
    ∀ i ∈ A,∀ j ∈ A,color i=color j → i=j:=by
  intro i hi j hj hij
  have hmj:mate j ∈ B:=a0 hd hb hj
    (hm.2.2.1 j (Finset.mem_union_left _ hj))
  have ht:(a (pair i (mate j)) && b (pair i (mate j)))=true :=
    a29 hd ha hb (a23 hm) hi hmj
  have hcm:color i≠color (mate j):=by
    intro h
    exact hcol j (h.symm.trans hij)
  have hmate:mate j=mate i:=by
    by_contra hne
    have hf:=hm.2.2.2 i (mate j) hcm hne
    dsimp only at hf
    rw [hf] at ht
    contradiction
  exact (hmi.injective hmate).symm
def a31 (color:Fin n → Bool) (S:Finset (Fin n))
    (f:(Fin n → Bool) → Bool):Prop :=
  ∀ i ∈ S,∀ j ∈ S,∀ l ∈ S,color i=color j → color i=color l →
    f (pair i j)=true → f (pair i l)=true → j=l
theorem a22 {mate:Fin n → Fin n} {color:Fin n → Bool}
    (hmi:Function.Involutive mate) (hcol:∀ i,color (mate i)≠color i)
    {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (hm:Matched mate color S f):a31 color S f:=by
  let Q:=fun (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool) =>
    RO S f∧(Matched mate color S f → a31 color S f)
  have hQ:Q S f:=hf Q (by
    intro i
    refine ⟨a34 i,?_⟩
    intro hm
    have hs:=hm.1 i
    simp [single] at hs) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1,?_⟩
      intro hm i hi j hj l hl hij hil hpj hpl
      have hinjA:=a13 hmi hcol hd ha.1 hb.1 hm
      have hm':Matched mate color (B ∪ A) (fun x=>b x && a x):=by
        simpa only [Finset.union_comm,Bool.and_comm] using hm
      have hinjB:=a13 hmi hcol hd.symm hb.1 ha.1 hm'
      rcases Finset.mem_union.mp hi with hi | hi
      · have hjB:=a0 hd hb.1 hi hpj
        have hlB:=a0 hd hb.1 hi hpl
        exact hinjB j hjB l hlB (hij.symm.trans hil)
      · have hpj':(b (pair i j) && a (pair i j))=true:=by simpa only [Bool.and_comm] using hpj
        have hpl':(b (pair i l) && a (pair i l))=true:=by simpa only [Bool.and_comm] using hpl
        have hjA:=a0 hd.symm ha.1 hi hpj'
        have hlA:=a0 hd.symm ha.1 hi hpl'
        exact hinjA j hjA l hlA (hij.symm.trans hil)
    · refine ⟨ro_or hd ha.1 hb.1,?_⟩
      intro hm i hi j hj l hl hij hil hpj hpl
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hjA,hpjA⟩:=a4 hd ha.1 hb.1 hm.1 hi hpj
        obtain ⟨hlA,hplA⟩:=a4 hd ha.1 hb.1 hm.1 hi hpl
        exact ha.2 (a24 hd ha.1 hb.1 hm) i hi j hjA l hlA hij hil hpjA hplA
      · have hm':Matched mate color (B ∪ A) (fun x=>b x || a x):=by
          simpa only [Finset.union_comm,Bool.or_comm] using hm
        have hpj':(b (pair i j) || a (pair i j))=true:=by simpa only [Bool.or_comm] using hpj
        have hpl':(b (pair i l) || a (pair i l))=true:=by simpa only [Bool.or_comm] using hpl
        obtain ⟨hjB,hpjB⟩:=a4 hd.symm hb.1 ha.1 hm'.1 hi hpj'
        obtain ⟨hlB,hplB⟩:=a4 hd.symm hb.1 ha.1 hm'.1 hi hpl'
        exact hb.2 (a35 hd ha.1 hb.1 hm) i hi j hjB l hlB hij hil hpjB hplB)
  exact hQ.2 hm
end L8.R017
namespace L8.R017
open L8.R012.TightReadOnce L8.R012.ReadOncePath
variable {n:ℕ}
theorem a11 {mate:Fin n → Fin n} {color:Fin n → Bool}
    {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (hm:Matched mate color S f) :
    ∀ i ∈ S,∀ j ∈ S,f (pair i j)=true → f (pair (mate i) (mate j))=true:=by
  let Q:=fun (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool) =>
    RO S f∧(Matched mate color S f →
      ∀ i ∈ S,∀ j ∈ S,f (pair i j)=true → f (pair (mate i) (mate j))=true)
  have hQ:Q S f:=hf Q (by
    intro i
    refine ⟨a34 i,?_⟩
    intro hm
    have hs:=hm.1 i
    simp [single] at hs) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1,?_⟩
      intro hm i hi j hj hp
      have hm':Matched mate color (B ∪ A) (fun x=>b x && a x):=by
        simpa only [Finset.union_comm,Bool.and_comm] using hm
      rcases Finset.mem_union.mp hi with hi | hi
      · have hjB:=a0 hd hb.1 hi hp
        have hmiB:=a0 hd hb.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))
        have hmjA:=a0 hd.symm ha.1 hjB
          (hm'.2.2.1 j (Finset.mem_union_left _ hjB))
        have h:=a29 hd.symm hb.1 ha.1 (a23 hm') hmiB hmjA
        simpa only [Bool.and_comm] using h
      · have hp':(b (pair i j) && a (pair i j))=true:=by
          simpa only [Bool.and_comm] using hp
        have hjA:=a0 hd.symm ha.1 hi hp'
        have hmiA:=a0 hd.symm ha.1 hi
          (hm'.2.2.1 i (Finset.mem_union_left _ hi))
        have hmjB:=a0 hd hb.1 hjA (hm.2.2.1 j (Finset.mem_union_left _ hjA))
        exact a29 hd ha.1 hb.1 (a23 hm) hmiA hmjB
    · refine ⟨ro_or hd ha.1 hb.1,?_⟩
      intro hm i hi j hj hp
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hjA,hpA⟩:=a4 hd ha.1 hb.1 hm.1 hi hp
        have h:=ha.2 (a24 hd ha.1 hb.1 hm) i hi j hjA hpA
        dsimp only
        rw [h,Bool.true_or]
      · have hm':Matched mate color (B ∪ A) (fun x=>b x || a x):=by
          simpa only [Finset.union_comm,Bool.or_comm] using hm
        have hp':(b (pair i j) || a (pair i j))=true:=by
          simpa only [Bool.or_comm] using hp
        obtain ⟨hjB,hpB⟩:=a4 hd.symm hb.1 ha.1 hm'.1 hi hp'
        have h:=hb.2 (a35 hd ha.1 hb.1 hm) i hi j hjB hpB
        dsimp only
        rw [h,Bool.or_true])
  exact hQ.2 hm
theorem matched_mirror {mate:Fin n → Fin n} {color:Fin n → Bool}
    (hmi:Function.Involutive mate)
    {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (hm:Matched mate color S f)
    {i j:Fin n} (hi:i ∈ S) (hj:j ∈ S) :
    f (pair i j)=f (pair (mate i) (mate j)):=by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact a11 hf hm i hi j hj
  · intro h
    have h':=a11 hf hm (mate i) (hm.2.1 i hi) (mate j) (hm.2.1 j hj) h
    simpa only [hmi i,hmi j] using h'
end L8.R017
namespace L8.R017
variable {α : Type*}
theorem a44 (R : α → α → Prop)
    (hs:∀ {a b},R a b → R b a) (hi:∀ a,¬ R a a)
    (hu:∀ a b c,R a b → R a c → b=c) :
    ∃ p:Equiv.Perm α,Function.Involutive p ∧
      (∀ a b,R a b↔p a=b∧b≠a) ∧
      (∀ q:Equiv.Perm α,(∀ a b,R a b↔q a=b∧b≠a) → q=p):=by
  classical
  let p : α → α := fun a=>if h:∃ b,R a b then Classical.choose h else a
  have hpR:∀ a b,R a b → p a=b:=by
    intro a b h
    have he:∃ b,R a b:=⟨b,h⟩
    dsimp only [p]
    rw [dite_eq_left he]
    exact hu a _ b (Classical.choose_spec he) h
  have hp:∀ a,p a=a∨R a (p a):=by
    intro a
    by_cases he:∃ b,R a b
    · right
      dsimp only [p]
      rw [dite_eq_left he]
      exact Classical.choose_spec he
    · left
      simp [p,he]
  have hpi:Function.Involutive p:=by
    intro a
    rcases hp a with h | h
    · rw [h,h]
    · exact hpR _ _ (hs h)
  let e:Equiv.Perm α := hpi.toPerm p
  have heval:∀ a,e a=p a:=fun _=>rfl
  have hiff:∀ a b,R a b↔e a=b∧b≠a:=by
    intro a b
    constructor
    · intro h
      refine ⟨hpR a b h,?_⟩
      intro hab
      exact hi a (hab ▸ h)
    · rintro ⟨hab,hn⟩
      rcases hp a with h | h
      · exact False.elim (hn (hab.symm.trans h))
      · exact hab ▸ h
  refine ⟨e,hpi,hiff,?_⟩
  intro q hq
  apply Equiv.ext
  intro a
  by_cases h:p a=a
  · by_cases hqa:q a=a
    · exact hqa.trans h.symm
    · have hr:=(hq a (q a)).2 ⟨rfl,hqa⟩
      have he:=hpR a (q a) hr
      exact False.elim (hqa (he.symm.trans h))
  · have hr:=(hiff a (e a)).2 ⟨rfl,h⟩
    exact (hq a (e a)).1 hr |>.1
theorem a19 {R : α → α → Prop} {p:Equiv.Perm α}
    (hp:∀ a b,R a b↔p a=b∧b≠a)
    (σ : α → α) (hσ : Function.Involutive σ)
    (hR:∀ a b,R a b → R (σ a) (σ b)) :
    ∀ a,p (σ a) = σ (p a):=by
  intro a
  by_cases he:p a=a
  · by_cases he':p (σ a) = σ a
    · rw [he,he']
    · have h:=hR (σ a) (p (σ a)) ((hp _ _).2 ⟨rfl,he'⟩)
      rw [hσ a] at h
      obtain ⟨hpa,hne⟩:=(hp _ _).1 h
      exact False.elim (hne (hpa.symm.trans he))
  · have h:=hR a (p a) ((hp _ _).2 ⟨rfl,he⟩)
    exact ((hp _ _).1 h).1
end L8.R017
namespace L8.R017
open L8.R012.TightReadOnce L8.R012.ReadOncePath
variable {n:ℕ}
theorem a48:∀ a b c d:Bool,a≠c → b≠d → c=d → a=b:=by decide
theorem matched_involution_normal_form {mate:Fin n → Fin n} {color:Fin n → Bool}
    (hmi:Function.Involutive mate) (hcol:∀ i,color (mate i)≠color i)
    {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (hf:RO S f) (hm:Matched mate color S f) :
    ∃ p:Equiv.Perm (Fin n),Function.Involutive p ∧
      (∀ i,color (p i)=color i) ∧
      (∀ i,p (mate i)=mate (p i)) ∧
      (∀ i,i ∉ S → p i=i) ∧
      (∀ x,f x=true↔∃ i ∈ S,
        (x i=true∧x (mate i)=true) ∨
        (p i≠i∧x i=true∧x (p i)=true)) ∧
      (∀ i j,(i ∈ S∧j ∈ S∧color i=color j∧f (pair i j)=true) ↔
        p i=j∧j≠i):=by
  classical
  let R:Fin n → Fin n → Prop:=fun i j =>
    i ∈ S∧j ∈ S∧color i=color j∧f (pair i j)=true
  have hsym:∀ {i j},R i j → R j i:=by
    intro i j h
    refine ⟨h.2.1,h.1,h.2.2.1.symm,?_⟩
    rw [a54]
    exact h.2.2.2
  have hirr:∀ i,¬ R i i:=by
    intro i h
    have hp:pair i i=single i:=by funext j;simp [pair,single]
    have htrue:=h.2.2.2
    rw [hp,hm.1 i] at htrue
    contradiction
  have hunique:∀ i j l,R i j → R i l → j=l:=by
    intro i j l h1 h2
    exact a22 hmi hcol hf hm i h1.1 j h1.2.1 l h2.2.1
      h1.2.2.1 h2.2.2.1 h1.2.2.2 h2.2.2.2
  obtain ⟨p,hpi,hp,hpu⟩:=a44 R hsym hirr hunique
  have hcolor:∀ i,color (p i)=color i:=by
    intro i
    by_cases he:p i=i
    · rw [he]
    · exact ((hp i (p i)).2 ⟨rfl,he⟩).2.2.1.symm
  have hmirror:∀ i j,R i j → R (mate i) (mate j):=by
    intro i j h
    refine ⟨hm.2.1 i h.1,hm.2.1 j h.2.1,?_,?_⟩
    · exact a48 _ _ _ _ (hcol i) (hcol j) h.2.2.1
    · exact a11 hf hm i h.1 j h.2.1 h.2.2.2
  have hcomm:=a19 hp mate hmi hmirror
  have hout:∀ i,i ∉ S → p i=i:=by
    intro i hi
    by_contra he
    exact hi ((hp i (p i)).2 ⟨rfl,he⟩).1
  refine ⟨p,hpi,hcolor,hcomm,hout,?_,hp⟩
  intro x
  constructor
  · intro hfx
    obtain ⟨i,hi,j,hj,hpair,hxi,hxj⟩ :=
      (a43 hf hm.1 (a23 hm) x).1 hfx
    by_cases hc:color i=color j
    · have hrij:R i j:=⟨hi,hj,hc,hpair⟩
      obtain ⟨hpij,hji⟩:=(hp i j).1 hrij
      refine ⟨i,hi,Or.inr ⟨?_,hxi,?_⟩⟩
      · simpa only [hpij] using hji
      · simpa only [hpij] using hxj
    · have hjm:j=mate i:=by
        by_contra hne
        have hz:=hm.2.2.2 i j hc hne
        rw [hz] at hpair
        contradiction
      exact ⟨i,hi,Or.inl ⟨hxi,hjm ▸ hxj⟩⟩
  · rintro ⟨i,hi,h | h⟩
    · exact a63 hf _ _ (a75 h.1 h.2) (hm.2.2.1 i hi)
    · have hr:=(hp i (p i)).2 ⟨rfl,h.1⟩
      exact a63 hf _ _ (a75 h.2.1 h.2.2) hr.2.2.2
end L8.R017
namespace L8.R017.RowColumn
open L8.R012.TightReadOnce L8.R012.ReadOncePath
variable {k:ℕ}
abbrev row (i:Fin k):Fin (k+k):=Fin.castAdd k i
abbrev col (i:Fin k):Fin (k+k):=Fin.natAdd k i
def mate:Fin (k+k) → Fin (k+k):=Fin.append col row
def color:Fin (k+k) → Bool:=Fin.append (fun _=>false) (fun _=>true)
@[simp] theorem mate_row (i:Fin k):mate (row i)=col i:=Fin.append_left _ _ i
@[simp] theorem mate_col (i:Fin k):mate (col i)=row i:=Fin.append_right _ _ i
@[simp] theorem color_row (i:Fin k):color (row i)=false:=Fin.append_left _ _ i
@[simp] theorem color_col (i:Fin k):color (col i)=true:=Fin.append_right _ _ i
theorem a61:Function.Involutive (mate (k:=k)):=by
  intro i
  induction i using Fin.addCases with
  | left j=>exact (congrArg mate (mate_row j)).trans (mate_col j)
  | right j=>exact (congrArg mate (mate_col j)).trans (mate_row j)
theorem a86 (i:Fin (k+k)):color (mate i)≠color i:=by
  induction i using Fin.addCases with
  | left j=>change color (mate (row j))≠color (row j);rw [mate_row,color_col,color_row];decide
  | right j=>change color (mate (col j))≠color (col j);rw [mate_col,color_row,color_col];decide
theorem a10:Function.Injective (row (k:=k)):=Fin.castAdd_injective k k
theorem a14:Function.Injective (col (k:=k)):=Fin.natAdd_injective k k
@[simp] theorem row_eq_iff (i j:Fin k):row i=row j↔i=j:=a10.eq_iff
@[simp] theorem col_eq_iff (i j:Fin k):col i=col j↔i=j:=a14.eq_iff
theorem a92 (p:Equiv.Perm (Fin (k+k)))
    (hc:∀ i,color (p i)=color i) (i:Fin k):∃ j,p (row i)=row j:=by
  have hcolor:=hc (row i)
  generalize he:p (row i)=v at *
  induction v using Fin.addCases with
  | left j=>exact ⟨j,rfl⟩
  | right j =>
    rw [color_row] at hcolor
    change color (col j)=false at hcolor
    rw [color_col] at hcolor
    contradiction
def a5 (p:Equiv.Perm (Fin k)) (x y:Fin k → Bool):Bool :=
  decide (∃ i:Fin k,
    (x i=true∧y i=true) ∨
    (p i≠i∧((x i=true∧x (p i)=true) ∨
      (y i=true∧y (p i)=true))))
theorem a32 (f:(Fin (k+k) → Bool) → Bool)
    (hf:RO Finset.univ f) (hm:L8.R017.Matched mate color Finset.univ f) :
    ∃ p:Equiv.Perm (Fin k),Function.Involutive p ∧
      ∀ x y,f (Fin.append x y)=a5 p x y:=by
  classical
  obtain ⟨p,hpi,hcol,hcomm,hout,hfn,hedge⟩ :=
    L8.R017.matched_involution_normal_form a61 a86 hf hm
  choose q hq using a92 p hcol
  have hqi:Function.Involutive q:=by
    intro i
    apply a10
    rw [← hq (q i),← hq i,hpi (row i)]
  let e:Equiv.Perm (Fin k):=hqi.toPerm q
  have hp_row:∀ i,p (row i)=row (e i):=hq
  have hp_col:∀ i,p (col i)=col (e i):=by
    intro i
    rw [← mate_row i,hcomm,hp_row,mate_row]
  have hnrow:∀ i,p (row i)≠row i↔e i≠i:=by
    intro i
    rw [hp_row]
    exact not_congr (a10.eq_iff)
  have hncol:∀ i,p (col i)≠col i↔e i≠i:=by
    intro i
    rw [hp_col]
    exact not_congr (a14.eq_iff)
  refine ⟨e,hqi,?_⟩
  intro x y
  apply Bool.eq_iff_iff.mpr
  rw [hfn]
  simp only [a5,decide_eq_true_eq]
  constructor
  · rintro ⟨v,hv,h⟩
    induction v using Fin.addCases with
    | left i =>
      rcases h with h | ⟨hn,h1,h2⟩
      · refine ⟨i,Or.inl ?_⟩
        simpa only [mate_row,Fin.append_left,Fin.append_right] using h
      · refine ⟨i,Or.inr ⟨(hnrow i).mp hn,Or.inl ⟨?_,?_⟩⟩⟩
        · simpa only [Fin.append_left] using h1
        · simpa only [hp_row,Fin.append_left] using h2
    | right i =>
      rcases h with h | ⟨hn,h1,h2⟩
      · refine ⟨i,Or.inl ?_⟩
        simpa only [mate_col,Fin.append_left,Fin.append_right] using h.symm
      · refine ⟨i,Or.inr ⟨(hncol i).mp hn,Or.inr ⟨?_,?_⟩⟩⟩
        · simpa only [Fin.append_right] using h1
        · simpa only [hp_col,Fin.append_right] using h2
  · rintro ⟨i,h | ⟨hn,h | h⟩⟩
    · refine ⟨row i,Finset.mem_univ _,Or.inl ?_⟩
      simpa only [mate_row,Fin.append_left,Fin.append_right] using h
    · refine ⟨row i,Finset.mem_univ _,Or.inr ⟨(hnrow i).mpr hn,?_,?_⟩⟩
      · simpa only [Fin.append_left] using h.1
      · simpa only [hp_row,Fin.append_left] using h.2
    · refine ⟨col i,Finset.mem_univ _,Or.inr ⟨(hncol i).mpr hn,?_,?_⟩⟩
      · simpa only [Fin.append_right] using h.1
      · simpa only [hp_col,Fin.append_right] using h.2
theorem a16 (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p)
    (i j:Fin k) :
    a5 p (pair i j) (fun _=>false)=true↔p i=j∧j≠i:=by
  simp only [a5,decide_eq_true_eq,Bool.false_eq_true,and_false,or_false,false_or,
    pair]
  constructor
  · rintro ⟨a,hn,ha,hpa⟩
    have ha':a=i∨a=j:=by simpa using ha
    have hpa':p a=i∨p a=j:=by simpa using hpa
    rcases ha' with hai | haj
    · subst a
      rcases hpa' with h | h
      · exact False.elim (hn h)
      · exact ⟨h,fun hji=>hn (h.trans hji)⟩
    · subst a
      rcases hpa' with h | h
      · have hij:p i=j:=by rw [← h,hp j]
        exact ⟨hij,fun hji=>hn (h.trans hji.symm)⟩
      · exact False.elim (hn h)
  · rintro ⟨hij,hji⟩
    refine ⟨i,?_,?_,?_⟩
    · exact fun h=>hji (hij.symm.trans h)
    · simp
    · simp [hij]
theorem a38 (p q:Equiv.Perm (Fin k))
    (hp:Function.Involutive p) (hq:Function.Involutive q)
    (he:∀ x y,a5 p x y=a5 q x y):p=q:=by
  have hr:∀ i j,(p i=j∧j≠i)↔(q i=j∧j≠i):=by
    intro i j
    rw [← a16 p hp i j,← a16 q hq i j,he]
  apply Equiv.ext
  intro i
  by_cases hn:p i=i
  · by_cases hnq:q i=i
    · exact hn.trans hnq.symm
    · have h:=(hr i (q i)).2 ⟨rfl,hnq⟩
      exact False.elim (hnq (h.1.symm.trans hn))
  · exact ((hr i (p i)).1 ⟨rfl,hn⟩).1.symm
theorem a15 (f:(Fin (k+k) → Bool) → Bool)
    (hf:RO Finset.univ f) (hm:L8.R017.Matched mate color Finset.univ f) :
    ∃! p:Equiv.Perm (Fin k),Function.Involutive p ∧
      ∀ x y,f (Fin.append x y)=a5 p x y:=by
  obtain ⟨p,hp,he⟩:=a32 f hf hm
  refine ⟨p,⟨hp,he⟩,?_⟩
  intro q hq
  apply a38 q p hq.1 hp
  intro x y
  exact (hq.2 x y).symm.trans (he x y)
end L8.R017.RowColumn
namespace L8.R017.RowColumn
open L8.R012.TightReadOnce L8.R012.ReadOncePath
variable {k:ℕ}
theorem a55 (hk:2 ≤ k) (i:Fin k):∃ j:Fin k,j≠i:=by
  let z:Fin k:=⟨0,by omega⟩
  let o:Fin k:=⟨1,by omega⟩
  by_cases hi:i=z
  · refine ⟨o,?_⟩
    intro h
    have hv:=congrArg Fin.val (h.trans hi)
    change 1=0 at hv
    omega
  · exact ⟨z,Ne.symm hi⟩
theorem a36 (hk:2 ≤ k) (f:(Fin (k+k) → Bool) → Bool)
    (hmono:∀ x y,(∀ i,x i=true → y i=true) → f x=true → f y=true)
    (hrep:∀ i j:Fin k,f (pair (row i) (col j))=decide (i=j)) :
    L8.R017.Matched mate color Finset.univ f:=by
  have hs:L8.R017.NoSingle f:=by
    intro v
    apply Bool.eq_false_iff.mpr
    intro htrue
    induction v using Fin.addCases with
    | left i =>
      obtain ⟨j,hji⟩:=a55 hk i
      have hx:=hmono (single (row i)) (pair (row i) (col j)) (by
        intro t ht
        have he:t=row i:=by simpa [single] using ht
        simp [pair,he]) htrue
      rw [hrep,decide_eq_false (Ne.symm hji)] at hx
      contradiction
    | right i =>
      obtain ⟨j,hji⟩:=a55 hk i
      have hx:=hmono (single (col i)) (pair (row j) (col i)) (by
        intro t ht
        have he:t=col i:=by simpa [single] using ht
        simp [pair,he]) htrue
      rw [hrep,decide_eq_false hji] at hx
      contradiction
  refine ⟨hs,by simp,?_,?_⟩
  · intro v hv
    induction v using Fin.addCases with
    | left i =>
      change f (pair (row i) (mate (row i)))=true
      rw [mate_row,hrep]
      simp
    | right i =>
      change f (pair (col i) (mate (col i)))=true
      rw [mate_col,a54,hrep]
      simp
  · intro v w hc hne
    induction v using Fin.addCases with
    | left i =>
      induction w using Fin.addCases with
      | left j=>exact False.elim (hc ((color_row i).trans (color_row j).symm))
      | right j =>
        change col j≠mate (row i) at hne
        rw [mate_row] at hne
        have hij:i≠j:=fun h=>hne (congrArg col h.symm)
        rw [hrep,decide_eq_false hij]
    | right i =>
      induction w using Fin.addCases with
      | left j =>
        change row j≠mate (col i) at hne
        rw [mate_col] at hne
        have hji:j≠i:=fun h=>hne (congrArg row h)
        rw [a54,hrep,decide_eq_false hji]
      | right j=>exact False.elim (hc ((color_col i).trans (color_col j).symm))
theorem a25 (hk:2 ≤ k) (f:(Fin (k+k) → Bool) → Bool)
    (hf:RO Finset.univ f)
    (hrep:∀ i j:Fin k,f (pair (row i) (col j))=decide (i=j)) :
    ∃! p:Equiv.Perm (Fin k),Function.Involutive p ∧
      ∀ x y,f (Fin.append x y)=a5 p x y:=by
  exact a15 f hf (a36 hk f (a63 hf) hrep)
end L8.R017.RowColumn
namespace L8.R017.CircuitForward
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open L8.R012.TightReadOnce L8.R012.ReadOncePath
open L8.R017.RowColumn
theorem a67 (g:Gate) (hg:g.op=GateOp.and∨g.op=GateOp.or)
    (w w':List Bool)
    (h:∀ i ∈ g.inputs,w.getD i false=true → w'.getD i false=true)
    (he:g.op.eval (g.inputs.map fun i=>w.getD i false)=true) :
    g.op.eval (g.inputs.map fun i=>w'.getD i false)=true:=by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi
    exact h i hi (he i hi)
  · obtain ⟨i,hi,hv⟩:=he
    exact ⟨i,hi,h i hi hv⟩
theorem a64 (gs:List Gate)
    (hm:∀ g ∈ gs,g.op=GateOp.and∨g.op=GateOp.or) :
    ∀ w w':List Bool,w.length=w'.length →
    (∀ i,w.getD i false=true → w'.getD i false=true) →
    ∀ i,(a3 gs w).getD i false=true → (a3 gs w').getD i false=true:=by
  induction gs with
  | nil=>intro w w' hl h;exact h
  | cons g gs ih =>
    intro w w' hl h i hi
    apply ih (fun g' hg'=>hm g' (List.mem_cons_of_mem _ hg'))
      (w++[g.op.eval (g.inputs.map fun a=>w.getD a false)])
      (w'++[g.op.eval (g.inputs.map fun a=>w'.getD a false)]) (by simp [hl]) ?_ i hi
    intro j hj
    by_cases he:j=w.length
    · rw [he,a7] at hj
      rw [he,hl,a7]
      exact a67 g (hm g List.mem_cons_self) w w' (fun a _=>h a) hj
    · rw [a8 _ _ _ _ he] at hj
      rw [a8 _ _ _ _ (by omega)]
      exact h j hj
theorem a74 {n:ℕ} (C:Circuit) (hm:Monotone2 C)
    (x y:Fin n → Bool) (h:∀ i,x i=true → y i=true)
    (he:C.eval (List.ofFn x)=true):C.eval (List.ofFn y)=true:=by
  apply a64 C.gates (fun g hg=>(hm g hg).1)
    (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output he
  intro j hj
  by_cases hjn:j < n
  · have hx:x ⟨j,hjn⟩=true:=by simpa [hjn] using hj
    simpa [hjn] using h ⟨j,hjn⟩ hx
  · rw [List.getD_eq_default _ _ (by simp;omega)] at hj
    contradiction
theorem a30 {k:ℕ} (i j:Fin k) :
    List.ofFn (pair (row i) (col j))=oneEach i j:=by
  have h:pair (row i) (col j) =
      Fin.append (single i) (single j):=by
    funext v
    induction v using Fin.addCases with
    | left t =>
      have hne:row t≠col j:=by
        intro h
        have hval:=congrArg (fun z:Fin (k+k)=>z.val) h
        change t.val=k+j.val at hval
        omega
      simp only [pair,single,Fin.append_left]
      simp only [hne,or_false]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using a10.eq_iff)
    | right t =>
      have hne:col t≠row i:=by
        intro h
        have hval:=congrArg (fun z:Fin (k+k)=>z.val) h
        change k+t.val=i.val at hval
        omega
      simp only [pair,single,Fin.append_right]
      simp only [hne,false_or]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using a14.eq_iff)
  rw [h,List.ofFn_fin_append]
  rfl
theorem a49 {k:ℕ} (hk:2 ≤ k) (C:Circuit)
    (hm:Monotone2 C) (hsize:C.size+1 ≤ 2*k)
    (hrep:Represents (fun i j:Fin k=>decide (i=j)) C) :
    RO Finset.univ (fun x:Fin (k+k) → Bool=>C.eval (List.ofFn x)):=by
  let f:(Fin (k+k) → Bool) → Bool:=fun x=>C.eval (List.ofFn x)
  have hrep':∀ i j:Fin k,f (pair (row i) (col j))=decide (i=j):=by
    intro i j
    exact (congrArg C.eval (a30 i j)).trans (hrep i j)
  have hm':=a36 hk f (a74 C hm) hrep'
  have hsens:∀ i ∈ (Finset.univ:Finset (Fin (k+k))),
      ∃ x y:Fin (k+k) → Bool,(∀ j,j≠i → x j=y j) ∧
        (C.wires (List.ofFn x)).getD C.output false ≠
          (C.wires (List.ofFn y)).getD C.output false:=by
    intro i hi
    refine ⟨pair i (mate i),single (mate i),?_,?_⟩
    · intro j hji
      simp [pair,single,hji]
    · change f (pair i (mate i))≠f (single (mate i))
      rw [hm'.2.2.1 i hi,hm'.1 (mate i)]
      decide
  have hvalid:C.output < (k+k)+C.gates.length:=by
    let z:Fin k:=⟨0,by omega⟩
    have ht:=hrep' z z
    have ht':(C.wires (List.ofFn (pair (row z) (col z)))).getD C.output false=true:=by
      change f (pair (row z) (col z))=true
      simpa only [decide_true] using ht
    by_contra hn
    have hl:(C.wires (List.ofFn (pair (row z) (col z)))).length=(k+k)+C.gates.length:=by
      rw [a91,a12]
      simp
    rw [List.getD_eq_default _ _ (by omega)] at ht'
    contradiction
  have hb:=a41 C (k+k) C.gates.length C.output le_rfl hvalid
    (fun g hg=>(hm g hg).2) Finset.univ hsens
  have hcard:(Finset.univ:Finset (Fin (k+k))).card=C.gates.length+1:=by
    simp only [Finset.card_univ,Fintype.card_fin] at hb ⊢
    change C.gates.length+1 ≤ 2*k at hsize
    omega
  exact a65 C (k+k) C.gates.length C.output le_rfl hvalid
    (fun g hg=>⟨by have h:=(hm g hg).1;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h;tauto,(hm g hg).2⟩)
    Finset.univ hcard hsens
theorem equality_circuit_classification {k:ℕ} (hk:2 ≤ k) (C:Circuit)
    (hm:Monotone2 C) (hsize:C.size+1 ≤ 2*k)
    (hrep:Represents (fun i j:Fin k=>decide (i=j)) C) :
    ∃! p:Equiv.Perm (Fin k),Function.Involutive p ∧
      ∀ x y,C.eval (List.ofFn x++List.ofFn y)=a5 p x y:=by
  have h:=a25 hk
    (fun x:Fin (k+k) → Bool=>C.eval (List.ofFn x))
    (a49 hk C hm hsize hrep) (by
      intro i j
      rw [a30]
      exact hrep i j)
  simpa only [List.ofFn_fin_append] using h
end L8.R017.CircuitForward
namespace L8.R017
 theorem official_forward:∀ (k:Nat),2 ≤ k → ∀ f:(Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C∧C.size+1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C ∧
    ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y)) →
  ∃! p:Equiv.Perm (Fin k),Function.Involutive p ∧
    ∀ x y,f x y=decide (∃ i:Fin k,
        (x i=true∧y i=true) ∨
        (p i≠i∧((x i=true∧x (p i)=true) ∨
          (y i=true∧y (p i)=true)))):=by
  intro k hk f h
  obtain ⟨C,hm,hs,hr,he⟩:=h
  obtain ⟨p,hp,hu⟩:=CircuitForward.equality_circuit_classification hk C hm hs hr
  refine ⟨p,⟨hp.1,?_⟩,?_⟩
  · intro x y
    exact (he x y).trans (hp.2 x y)
  · intro q hq
    apply hu q
    refine ⟨hq.1,?_⟩
    intro x y
    exact (he x y).symm.trans (hq.2 x y)
end L8.R017
namespace L8.R020.ROCompiler
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open L8.R012.TightReadOnce
variable {n:ℕ}
def GateOK (g:Gate):Prop :=
  (g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length ≤ 2
def a50 (S:Finset (Fin n)) (f:(Fin n → Bool) → Bool):Prop :=
  ∀ m:ℕ,n ≤ m → ∃ (gs:List Gate) (out:ℕ),
    (∀ g ∈ gs,GateOK g)∧gs.length+1=S.card∧out < m+gs.length ∧
    ∀ w:List Bool,w.length=m →
      (a3 gs w).getD out false=f (fun i:Fin n=>w.getD i.val false)
theorem a69 (i:Fin n):a50 {i} (fun x=>x i):=by
  intro m hm
  refine ⟨[],i.val,?_,by simp,?_,?_⟩
  · simp
  · have:=i.isLt
    simp only [List.length_nil,Nat.add_zero]
    omega
  · intro w hw
    rfl
theorem a52 {A B:Finset (Fin n)} {a b:(Fin n → Bool) → Bool}
    (hd:Disjoint A B) (ha:a50 A a) (hb:a50 B b)
    (op:GateOp) (hop:op=GateOp.and∨op=GateOp.or) :
    a50 (A ∪ B) (fun x=>op.eval [a x,b x]):=by
  intro m hm
  obtain ⟨ga,oa,oka,lena,ra,eva⟩:=ha m hm
  obtain ⟨gb,ob,okb,lenb,rb,evb⟩:=hb (m+ga.length) (by omega)
  let M:=m+ga.length+gb.length
  refine ⟨ga++gb++[⟨op,[oa,ob]⟩],M,?_,?_,?_,?_⟩
  · intro g hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact oka g hg
    · exact okb g hg
    · subst g
      exact ⟨hop,by simp⟩
  · rw [Finset.card_union_of_disjoint hd]
    simp only [List.length_append,List.length_singleton]
    omega
  · simp only [List.length_append,List.length_singleton]
    dsimp [M]
    omega
  · intro w hw
    rw [a18,a18]
    let wa:=a3 ga w
    let wb:=a3 gb wa
    have hwa:wa.length=m+ga.length:=by
      dsimp [wa]
      rw [a12,hw]
    have hwb:wb.length=M:=by
      dsimp [wb]
      rw [a12,hwa]
    have eqa:wb.getD oa false=a (fun i:Fin n=>w.getD i.val false):=by
      dsimp [wb]
      rw [a28 gb wa oa (by omega)]
      exact eva w hw
    have eqb:wb.getD ob false=b (fun i:Fin n=>w.getD i.val false):=by
      dsimp [wb]
      rw [evb wa hwa]
      congr 1
      funext i
      exact a28 ga w i.val (by have:=i.isLt;omega)
    change (a3 [⟨op,[oa,ob]⟩] wb).getD M false=_
    change (wb++[op.eval [wb.getD oa false,wb.getD ob false]]).getD M false=_
    rw [← hwb,a7,eqa,eqb]
theorem a77 {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (h:RO S f):a50 S f:=by
  apply h a50 a69
  intro A B a b hd ha hb
  constructor
  · simpa only [GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
      using a52 hd ha hb GateOp.and (Or.inl rfl)
  · simpa only [GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
      using a52 hd ha hb GateOp.or (Or.inr rfl)
theorem a83 {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (h:RO S f) :
    ∃ C:Circuit,Monotone2 C∧C.size+1=S.card∧C.output < n+C.size ∧
      ∀ x:Fin n → Bool,C.eval (List.ofFn x)=f x:=by
  obtain ⟨gs,out,hok,hlen,hout,heval⟩:=a77 h n (le_refl n)
  refine ⟨⟨gs,out⟩,?_,hlen,hout,?_⟩
  · intro g hg
    obtain ⟨ho,hl⟩:=hok g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ho,hl⟩
  · intro x
    change (a3 gs (List.ofFn x)).getD out false=f x
    rw [heval (List.ofFn x) (by simp)]
    congr 1
    funext i
    simp
theorem ro_circuit_exists {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool}
    (h:RO S f) :
    ∃ C:Circuit,Monotone2 C∧C.size+1=S.card ∧
      ∀ x:Fin n → Bool,C.eval (List.ofFn x)=f x:=by
  obtain ⟨C,hC,hsize,_,heval⟩:=a83 h
  exact ⟨C,hC,hsize,heval⟩
end L8.R020.ROCompiler
namespace L8.R019.InvolutionRO
open L8.R012.TightReadOnce L8.R012.ReadOncePath L8.R017.RowColumn
variable {k:ℕ}
theorem a33 (i j:Fin k):row i≠col j:=by
  intro h
  have e:=congrArg (fun z:Fin (k+k)=>z.val) h
  change i.val=k+j.val at e
  omega
theorem a57 (i j:Fin k):col i≠row j:=(a33 j i).symm
def supp (S:Finset (Fin k)):Finset (Fin (k+k)):=S.image row ∪ S.image col
def clause (p:Equiv.Perm (Fin k)) (i:Fin k) (x:Fin (k+k) → Bool):Prop :=
  (x (row i)=true∧x (col i)=true) ∨
  (p i≠i∧((x (row i)=true∧x (row (p i))=true) ∨
    (x (col i)=true∧x (col (p i))=true)))
noncomputable def evalOn (p:Equiv.Perm (Fin k)) (S:Finset (Fin k))
    (x:Fin (k+k) → Bool):Bool:=by
  classical
  exact decide (∃ i ∈ S,clause p i x)
theorem a81 (S T:Finset (Fin k)):supp (S ∪ T)=supp S ∪ supp T:=by
  classical
  ext i
  simp only [supp,Finset.mem_union,Finset.mem_image]
  aesop
theorem a68 {S T:Finset (Fin k)} (hd:Disjoint S T) :
    Disjoint (supp S) (supp T):=by
  classical
  rw [Finset.disjoint_left] at hd ⊢
  intro v hv hw
  simp only [supp,Finset.mem_union,Finset.mem_image] at hv hw
  rcases hv with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
    · exact hd hi ((a10 he) ▸ hj)
    · exact a57 j i he
  · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
    · exact a33 j i he
    · exact hd hi ((a14 he) ▸ hj)
theorem a73 (p:Equiv.Perm (Fin k)) (S T:Finset (Fin k)) :
    evalOn p (S ∪ T)=fun x=>evalOn p S x || evalOn p T x:=by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [evalOn,decide_eq_true_eq,Bool.or_eq_true,Finset.mem_union]
  aesop
theorem a85 (p:Equiv.Perm (Fin k)) (i:Fin k) (hi:p i=i) :
    RO (supp {i}) (evalOn p {i}):=by
  have hr:=ro_and (by simpa using a33 i i) (a34 (row i)) (a34 (col i))
  convert hr using 1
  · simp [supp]
  · funext x
    simp [evalOn,clause,hi]
theorem a90 (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p)
    (i j:Fin k) (hij:i≠j) (hpij:p i=j) :
    RO (supp {i,j}) (evalOn p {i,j}):=by
  have hpji:p j=i:=by rw [← hpij,hp i]
  have hA:=ro_or (by simpa using a33 i j) (a34 (row i)) (a34 (col j))
  have hB:=ro_or (by simpa using a57 i j) (a34 (col i)) (a34 (row j))
  have hd:Disjoint (({row i} ∪ {col j}):Finset (Fin (k+k))) ({col i} ∪ {row j}):=by
    rw [Finset.disjoint_left]
    intro v hv hw
    simp only [Finset.mem_union,Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl
    · rcases hw with he | he
      · exact a33 i i he
      · exact hij (a10 he)
    · rcases hw with he | he
      · exact hij.symm (a14 he)
      · exact a57 j j he
  have hr:=ro_and hd hA hB
  convert hr using 1
  · ext v
    simp only [supp,Finset.image_insert,Finset.image_singleton,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    tauto
  · funext x
    apply Bool.eq_iff_iff.mpr
    simp only [evalOn,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton,
      exists_eq_or_imp,exists_eq_left,clause,hpij,hpji,Bool.and_eq_true,Bool.or_eq_true]
    tauto
theorem a79 (p:Equiv.Perm (Fin k)) (S T:Finset (Fin k))
    (hd:Disjoint S T) (hS:RO (supp S) (evalOn p S)) (hT:RO (supp T) (evalOn p T)) :
    RO (supp (S ∪ T)) (evalOn p (S ∪ T)):=by
  rw [a81,a73]
  exact ro_or (a68 hd) hS hT
theorem a72 (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p)
    (S:Finset (Fin k)) (hS:∀ i ∈ S,p i ∈ S) (hne:S.Nonempty) :
    RO (supp S) (evalOn p S):=by
  classical
  revert hS hne
  refine Finset.strongInductionOn S ?_
  intro S ih hS hne
  obtain ⟨i,hi⟩:=hne
  by_cases hfix:p i=i
  · let T:=S.erase i
    have ht:T ⊂ S:=Finset.erase_ssubset hi
    have hclose:∀ j ∈ T,p j ∈ T:=by
      intro j hj
      have hjs:=Finset.mem_erase.mp hj
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        apply hjs.1
        exact p.injective (he.trans hfix.symm)
      · exact hS j hjs.2
    have heq:S={i} ∪ T:=by simp [T,hi]
    by_cases hempty:T = ∅
    · rw [heq,hempty,Finset.union_empty]
      exact a85 p i hfix
    · rw [heq]
      apply a79 p {i} T
      · simp [T]
      · exact a85 p i hfix
      · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)
  · let j:=p i
    have hij:i≠j:=Ne.symm hfix
    have hj:j ∈ S:=hS i hi
    have hpji:p j=i:=hp i
    let T:=(S.erase i).erase j
    have ht:T ⊂ S :=
      lt_of_le_of_lt (Finset.erase_subset j (S.erase i)) (Finset.erase_ssubset hi)
    have hclose:∀ a ∈ T,p a ∈ T:=by
      intro a ha
      have h:=Finset.mem_erase.mp ha
      have h':=Finset.mem_erase.mp h.2
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        exact h'.1 (p.injective he)
      · apply Finset.mem_erase.mpr
        constructor
        · intro he
          exact h.1 (p.injective (he.trans hpji.symm))
        · exact hS a h'.2
    have heq:S={i,j} ∪ T:=by
      ext a
      simp only [T,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_erase]
      constructor
      · intro ha
        by_cases hai:a=i
        · exact Or.inl (Or.inl hai)
        · by_cases haj:a=j
          · exact Or.inl (Or.inr haj)
          · exact Or.inr ⟨haj,hai,ha⟩
      · rintro ((rfl | rfl) | ⟨-,-,ha⟩)
        · exact hi
        · exact hj
        · exact ha
    by_cases hempty:T = ∅
    · rw [heq,hempty,Finset.union_empty]
      exact a90 p hp i j hij rfl
    · rw [heq]
      apply a79 p {i,j} T
      · simp [T,Finset.disjoint_left]
      · exact a90 p hp i j hij rfl
      · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)
theorem involution_ro (hk:0 < k) (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p) :
    RO Finset.univ (fun x:Fin (k+k) → Bool=>a5 p (fun i=>x (row i))
      (fun i=>x (col i))):=by
  have h:=a72 p hp Finset.univ (by simp) ⟨⟨0,hk⟩,Finset.mem_univ _⟩
  have hs:supp (Finset.univ:Finset (Fin k))=Finset.univ:=by
    ext v
    simp only [Finset.mem_univ,iff_true]
    induction v using Fin.addCases with
    | left i=>exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    | right i=>exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [hs] at h
  have he:evalOn p Finset.univ=(fun x:Fin (k+k) → Bool=>a5 p (fun i=>x (row i)) (fun i=>x (col i))):=by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [evalOn,clause,a5]
  rw [he] at h
  exact h
end L8.R019.InvolutionRO
namespace L8.R019.InverseBridge
open L8.R017.RowColumn L8.R012.TightReadOnce L8.R012.ReadOncePath
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem a46 {k:ℕ} (p:Equiv.Perm (Fin k)) (i j:Fin k) :
    a5 p (single i) (single j)=decide (i=j):=by
  apply Bool.eq_iff_iff.mpr
  simp only [a5,single,decide_eq_true_eq]
  constructor
  · rintro ⟨a,⟨hai,haj⟩ | ⟨hne,h | h⟩⟩
    · exact hai.symm.trans haj
    · exact False.elim (hne (h.2.trans h.1.symm))
    · exact False.elim (hne (h.2.trans h.1.symm))
  · intro hij
    exact ⟨i,Or.inl ⟨rfl,hij⟩⟩
theorem involution_circuit_of_compiler
    (compileRO:∀ {n:ℕ} {S:Finset (Fin n)} {f:(Fin n → Bool) → Bool},
      RO S f → ∃ C:Circuit,Monotone2 C∧C.size+1=S.card ∧
        ∀ x,C.eval (List.ofFn x)=f x)
    {k:ℕ} (hk:0 < k) (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p) :
    ∃ C:Circuit,Monotone2 C∧C.size+1 ≤ 2*k ∧
      Represents (fun i j:Fin k=>decide (i=j)) C ∧
      ∀ x y,C.eval (List.ofFn x++List.ofFn y)=a5 p x y:=by
  obtain ⟨C,hm,hs,he⟩:=compileRO (InvolutionRO.involution_ro hk p hp)
  have hfull:∀ x y,C.eval (List.ofFn x++List.ofFn y)=a5 p x y:=by
    intro x y
    simpa only [List.ofFn_fin_append,Fin.append_left,Fin.append_right]
      using he (Fin.append x y)
  refine ⟨C,hm,?_,?_,hfull⟩
  · simp only [Finset.card_univ,Fintype.card_fin] at hs
    omega
  · intro i j
    change C.eval (List.ofFn (single i)++List.ofFn (single j))=decide (i=j)
    rw [hfull,a46]
end L8.R019.InverseBridge
namespace L8.R019
theorem official_full:∀ (k:Nat),2 ≤ k → ∀ f:(Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C∧C.size+1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C ∧
    ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y)) ↔
  ∃! p:Equiv.Perm (Fin k),Function.Involutive p ∧
    ∀ x y,f x y=decide (∃ i:Fin k,
        (x i=true∧y i=true) ∨
        (p i≠i∧((x i=true∧x (p i)=true) ∨
          (y i=true∧y (p i)=true)))):=by
  intro k hk f
  constructor
  · exact L8.R017.official_forward k hk f
  · rintro ⟨p,⟨hp,hf⟩,hu⟩
    obtain ⟨C,hm,hs,hr,he⟩:=InverseBridge.involution_circuit_of_compiler
      (fun h=>L8.R020.ROCompiler.ro_circuit_exists h) (by omega:0 < k) p hp
    refine ⟨C,hm,hs,hr,?_⟩
    intro x y
    exact (hf x y).trans (he x y).symm
end L8.R019
theorem L8_thm :
∀ (k:Nat),2 ≤ k → ∀ f:(Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C∧C.size+1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C ∧
    ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y)) ↔
  ∃! p:Equiv.Perm (Fin k),Function.Involutive p ∧
    ∀ x y,f x y=decide (∃ i:Fin k,
        (x i=true∧y i=true) ∨
        (p i≠i∧((x i=true∧x (p i)=true) ∨
          (y i=true∧y (p i)=true)))):=L8.R019.official_full
end
section
namespace L9
private def testOf {v m:Nat} (ends:Fin m → Fin v × Fin v) (z:Fin m × Bool):Finset Nat :=
  {v+2 * z.1.val,v+2 * z.1.val+1,if z.2 then (ends z.1).2.val else (ends z.1).1.val}
private lemma b27 {v m:Nat} (ends:Fin m → Fin v × Fin v) (z:Fin m × Bool) :
    (if z.2 then (ends z.1).2.val else (ends z.1).1.val) < v:=by
  cases z.2 with
  | false=>exact (ends z.1).1.isLt
  | true=>exact (ends z.1).2.isLt
private lemma testOf_card {v m:Nat} (ends:Fin m → Fin v × Fin v) (z:Fin m × Bool) :
    (testOf ends z).card=3:=by
  have hlt:=b27 ends z
  unfold testOf
  rw [Finset.card_insert_of_notMem,Finset.card_insert_of_notMem,Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    omega
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
private lemma b36 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2):Function.Injective (testOf ends):=by
  intro z1 z2 h
  have hlt1:=b27 ends z1
  have hlt2:=b27 ends z2
  have ha:v+2 * z1.1.val ∈ testOf ends z2:=by
    rw [← h]
    simp [testOf]
  have he:z1.1=z2.1:=by
    simp only [testOf,Finset.mem_insert,Finset.mem_singleton] at ha
    apply Fin.ext
    omega
  have hc:(if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val) ∈ testOf ends z2:=by
    rw [← h]
    simp [testOf]
  simp only [testOf,Finset.mem_insert,Finset.mem_singleton] at hc
  have hceq:(if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val) =
      (if z2.2 then (ends z2.1).2.val else (ends z2.1).1.val):=by
    omega
  have hb:z1.2=z2.2:=by
    rw [he] at hceq
    cases hb1:z1.2 <;> cases hb2:z2.2
    · rfl
    · simp only [hb1,hb2,Bool.false_eq_true,↓reduceIte] at hceq
      exact False.elim (hends z2.1 (Fin.ext hceq))
    · simp only [hb1,hb2,Bool.false_eq_true,↓reduceIte] at hceq
      exact False.elim (hends z2.1 (Fin.ext hceq.symm))
    · rfl
  exact Prod.ext he hb
private lemma tests_card {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) :
    (Finset.univ.image (testOf ends)).card=2 * m:=by
  rw [Finset.card_image_of_injective _ (b36 ends hends),Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm]
private lemma b31 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (z:Fin m × Bool) :
    (testOf ends (z.1,!z.2) ∩ testOf ends z).card=2:=by
  have hlt1:=b27 ends (z.1,!z.2)
  have hlt2:=b27 ends z
  have hne:(if !z.2 then (ends z.1).2.val else (ends z.1).1.val) ≠
      (if z.2 then (ends z.1).2.val else (ends z.1).1.val):=by
    cases hb:z.2
    · simp only [Bool.not_false,↓reduceIte,Bool.false_eq_true]
      intro h
      exact hends z.1 (Fin.ext h.symm)
    · simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
      intro h
      exact hends z.1 (Fin.ext h)
  have heq:testOf ends (z.1,!z.2) ∩ testOf ends z={v+2 * z.1.val,v+2 * z.1.val+1}:=by
    ext x
    simp only [testOf,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨h1,h2⟩
      omega
    · rintro (rfl | rfl) <;> simp
  rw [heq,Finset.card_insert_of_notMem,Finset.card_singleton]
  simp only [Finset.mem_singleton]
  omega
private lemma b28 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (z1 z2:Fin m × Bool) (hne:z1.1≠z2.1) :
    (testOf ends z1 ∩ testOf ends z2).card ≤ 1:=by
  have hlt2:=b27 ends z2
  have hval:z1.1.val≠z2.1.val:=fun h=>hne (Fin.ext h)
  have hsub:testOf ends z1 ∩ testOf ends z2 ⊆
      {if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val}:=by
    intro x hx
    simp only [testOf,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
    omega
  calc
    (testOf ends z1 ∩ testOf ends z2).card
      ≤ ({if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val}:Finset Nat).card :=
        Finset.card_le_card hsub
    _=1:=Finset.card_singleton _
private lemma twin_filter_card {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (z:Fin m × Bool) :
    ((Finset.univ.image (testOf ends)).filter
      (fun T=>T≠testOf ends z∧(T ∩ testOf ends z).card=2)).card=1:=by
  have heq:(Finset.univ.image (testOf ends)).filter
      (fun T=>T≠testOf ends z∧(T ∩ testOf ends z).card=2) =
      {testOf ends (z.1,!z.2)}:=by
    ext T
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨w,rfl⟩,hneT,hcard⟩
      have hwe:w.1=z.1:=by
        by_contra hne
        have hle:=b28 ends w z hne
        omega
      have hwb:w.2 = !z.2:=by
        cases h1:w.2 <;> cases h2:z.2
        · exfalso
          exact hneT (congrArg (testOf ends) (Prod.ext hwe (h1.trans h2.symm)))
        · rfl
        · rfl
        · exfalso
          exact hneT (congrArg (testOf ends) (Prod.ext hwe (h1.trans h2.symm)))
      exact congrArg (testOf ends) (Prod.ext hwe hwb)
    · rintro rfl
      refine ⟨⟨(z.1,!z.2),rfl⟩,?_,b31 ends hends z⟩
      intro hEq
      have hpr:=b36 ends hends hEq
      have hbf:(!z.2)=z.2:=congrArg Prod.snd hpr
      cases z.2 <;> simp at hbf
  rw [heq,Finset.card_singleton]
private def p0 (v m t:Nat) (e:Fin m):Fin (v+2 * m+t) :=
  ⟨v+2 * e.val,by omega⟩
private def p1 (v m t:Nat) (e:Fin m):Fin (v+2 * m+t) :=
  ⟨v+2 * e.val+1,by omega⟩
private def u0 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat) (e:Fin m) :
    Fin (v+2 * m+t) :=
  ⟨(ends e).1.val,by have:=(ends e).1.isLt;omega⟩
private def u1 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat) (e:Fin m) :
    Fin (v+2 * m+t) :=
  ⟨(ends e).2.val,by have:=(ends e).2.isLt;omega⟩
private def uEnd {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat) (e:Fin m) (b:Bool) :
    Fin (v+2 * m+t) :=
  if b then u1 ends t e else u0 ends t e
private lemma b23 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (t:Nat) (e:Fin m) :
    u0 ends t e≠u1 ends t e:=by
  intro h
  have hv:(u0 ends t e).val=(u1 ends t e).val:=congrArg Fin.val h
  exact hends e (Fin.ext hv)
private lemma b7 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (e:Fin m) (b:Bool) (x:Fin (v+2 * m+t)) :
    x.val ∈ testOf ends (e,b)↔x=p0 v m t e∨x=p1 v m t e∨x=uEnd ends t e b:=by
  cases b <;> simp only [testOf,uEnd,p0,p1,u0,u1,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,Bool.false_eq_true,↓reduceIte]
private abbrev IsMatching {v m:Nat} (ends:Fin m → Fin v × Fin v) (S:Finset (Fin m)):Prop :=
  ∀ e ∈ S,∀ g ∈ S,e≠g →
    Disjoint ({(ends e).1,(ends e).2}:Finset (Fin v)) {(ends g).1,(ends g).2}
private def Wins {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (P:Equiv.Perm (Fin (v+2 * m+t))):Prop :=
  Function.Involutive P ∧
    ∀ R ∈ Finset.univ.image (testOf ends),
      ∃ u:Fin (v+2 * m+t),u.val ∈ R∧(P u).val ∈ R∧P u≠u
private def Active {v m:Nat} (t:Nat) (P:Equiv.Perm (Fin (v+2 * m+t))) :
    Finset (Fin m) :=
  Finset.univ.filter (fun e:Fin m =>
    ¬ ∃ u:Fin (v+2 * m+t),u.val=v+2 * e.val∧(P u).val=v+2 * e.val+1)
private lemma b12 {v m:Nat} (t:Nat)
    (P:Equiv.Perm (Fin (v+2 * m+t))) (e:Fin m) :
    e ∈ Active (v:=v) t P↔P (p0 v m t e)≠p1 v m t e:=by
  simp only [Active,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h hEq
    exact h ⟨p0 v m t e,rfl,congrArg Fin.val hEq⟩
  · intro hNe ⟨u,hu0,hu1⟩
    have hu:u=p0 v m t e:=Fin.ext hu0
    rw [hu] at hu1
    exact hNe (Fin.ext hu1)
private lemma b11 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (P:Equiv.Perm (Fin (v+2 * m+t))) (hW:Wins ends t P)
    (e:Fin m) (he:e ∈ Active (v:=v) t P) (b:Bool) :
    P (uEnd ends t e b)=p0 v m t e∨P (uEnd ends t e b)=p1 v m t e:=by
  have hne01:P (p0 v m t e)≠p1 v m t e:=(b12 t P e).mp he
  have hne10:P (p1 v m t e)≠p0 v m t e:=by
    intro h
    have:=congrArg P h
    rw [hW.1] at this
    exact hne01 this.symm
  have hmem:testOf ends (e,b) ∈ Finset.univ.image (testOf ends) :=
    Finset.mem_image.mpr ⟨(e,b),Finset.mem_univ _,rfl⟩
  rcases hW.2 _ hmem with ⟨x,hxR,hPxR,hne⟩
  rw [b7] at hxR hPxR
  rcases hxR with rfl | rfl | rfl
  · rcases hPxR with h | h | h
    · exact False.elim (hne h)
    · exact False.elim (hne01 h)
    · left
      rw [← h,hW.1]
  · rcases hPxR with h | h | h
    · exact False.elim (hne10 h)
    · exact False.elim (hne h)
    · right
      rw [← h,hW.1]
  · rcases hPxR with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hne h)
private lemma b5 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (t:Nat)
    (P:Equiv.Perm (Fin (v+2 * m+t))) (hW:Wins ends t P)
    (e:Fin m) (he:e ∈ Active (v:=v) t P) :
    (P (p0 v m t e)=u0 ends t e∧P (p1 v m t e)=u1 ends t e) ∨
    (P (p0 v m t e)=u1 ends t e∧P (p1 v m t e)=u0 ends t e):=by
  have h0:=b11 ends t P hW e he false
  have h1:=b11 ends t P hW e he true
  simp only [uEnd,Bool.false_eq_true,↓reduceIte] at h0 h1
  have hne:P (u0 ends t e)≠P (u1 ends t e):=fun h =>
    b23 ends hends t e (P.injective h)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact False.elim (hne (h0.trans h1.symm))
  · left
    exact ⟨by rw [← h0,hW.1],by rw [← h1,hW.1]⟩
  · right
    exact ⟨by rw [← h1,hW.1],by rw [← h0,hW.1]⟩
  · exact False.elim (hne (h0.trans h1.symm))
private lemma b33 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat)
    (P:Equiv.Perm (Fin (v+2 * m+t))) (hW:Wins ends t P) :
    IsMatching ends (Active (v:=v) t P):=by
  intro e he g hg hne
  rw [Finset.disjoint_left]
  intro w hwe hwg
  let x:Fin (v+2 * m+t):=⟨w.val,by have:=w.isLt;omega⟩
  have hxe:x=u0 ends t e∨x=u1 ends t e:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hwe
    rcases hwe with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hxg:x=u0 ends t g∨x=u1 ends t g:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hwg
    rcases hwg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hPe:P x=p0 v m t e∨P x=p1 v m t e:=by
    rcases hxe with h | h
    · rw [h];simpa [uEnd] using b11 ends t P hW e he false
    · rw [h];simpa [uEnd] using b11 ends t P hW e he true
  have hPg:P x=p0 v m t g∨P x=p1 v m t g:=by
    rcases hxg with h | h
    · rw [h];simpa [uEnd] using b11 ends t P hW g hg false
    · rw [h];simpa [uEnd] using b11 ends t P hW g hg true
  have hval:e.val=g.val:=by
    rcases hPe with h1 | h1 <;> rcases hPg with h2 | h2
    · have:=congrArg Fin.val (h1.symm.trans h2);simp only [p0] at this;omega
    · have:=congrArg Fin.val (h1.symm.trans h2);simp only [p0,p1] at this;omega
    · have:=congrArg Fin.val (h1.symm.trans h2);simp only [p0,p1] at this;omega
    · have:=congrArg Fin.val (h1.symm.trans h2);simp only [p1] at this;omega
  exact hne (Fin.ext hval)
private def b13 (v m t:Nat):Finset (Fin (v+2 * m+t)) :=
  Finset.univ.filter (fun x=>v ≤ x.val∧x.val < v+2 * m)
private def b6 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (S:Finset (Fin m)):Finset (Fin (v+2 * m+t)) :=
  S.biUnion (fun e=>{u0 ends t e,u1 ends t e})
private def remSet {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (S:Finset (Fin m)):Finset (Fin (v+2 * m+t)) :=
  Finset.univ \ (b13 v m t ∪ b6 ends t S)
private lemma b15 (v m t:Nat) (e:Fin m) :
    p0 v m t e ∈ b13 v m t:=by
  simp only [b13,p0,Finset.mem_filter,Finset.mem_univ,true_and]
  omega
private lemma b14 (v m t:Nat) (e:Fin m) :
    p1 v m t e ∈ b13 v m t:=by
  simp only [b13,p1,Finset.mem_filter,Finset.mem_univ,true_and]
  omega
private lemma b22 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat) (e:Fin m) :
    u0 ends t e ∉ b13 v m t:=by
  simp only [b13,u0,Finset.mem_filter,Finset.mem_univ,true_and]
  have:=(ends e).1.isLt
  omega
private lemma b21 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat) (e:Fin m) :
    u1 ends t e ∉ b13 v m t:=by
  simp only [b13,u1,Finset.mem_filter,Finset.mem_univ,true_and]
  have:=(ends e).2.isLt
  omega
private lemma b24 {v m t:Nat} {x:Fin (v+2 * m+t)} (hx:x ∈ b13 v m t) :
    ∃ e:Fin m,x=p0 v m t e∨x=p1 v m t e:=by
  have h1:v ≤ x.val∧x.val < v+2 * m:=(Finset.mem_filter.mp hx).2
  refine ⟨⟨(x.val - v) / 2,by omega⟩,?_⟩
  by_cases hp:(x.val - v) % 2=0
  · left
    apply Fin.ext
    simp only [p0]
    omega
  · right
    apply Fin.ext
    simp only [p1]
    omega
private lemma b38 (v m t:Nat):(b13 v m t).card=2 * m:=by
  let f:Fin (2 * m) → Fin (v+2 * m+t):=fun i=>⟨v+i.val,by omega⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Fin.ext
    have:=congrArg Fin.val h
    dsimp [f] at this
    omega
  have heq:b13 v m t=Finset.univ.image f:=by
    ext x
    simp only [b13,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨h1,h2⟩
      refine ⟨⟨x.val - v,by omega⟩,?_⟩
      apply Fin.ext
      dsimp [f]
      omega
    · rintro ⟨i,rfl⟩
      dsimp [f]
      omega
  rw [heq,Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin]
private lemma b35 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (t:Nat)
    (S:Finset (Fin m)) (hM:IsMatching ends S) :
    (b6 ends t S).card=2 * S.card:=by
  have hpw:(S:Set (Fin m)).PairwiseDisjoint (fun e=>({u0 ends t e,u1 ends t e}:Finset _)):=by
    intro e he g hg hne
    rw [Function.onFun,Finset.disjoint_left]
    intro x hxe hxg
    have hdisj:=hM e he g hg hne
    rw [Finset.disjoint_left] at hdisj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxe hxg
    rcases hxe with rfl | rfl <;> rcases hxg with h | h
    · have hv:(u0 ends t e).val=(u0 ends t g).val:=congrArg Fin.val h
      have hw:(ends e).1=(ends g).1:=Fin.ext hv
      exact hdisj (a:=(ends e).1) (by simp) (by simp [hw])
    · have hv:(u0 ends t e).val=(u1 ends t g).val:=congrArg Fin.val h
      have hw:(ends e).1=(ends g).2:=Fin.ext hv
      exact hdisj (a:=(ends e).1) (by simp) (by simp [hw])
    · have hv:(u1 ends t e).val=(u0 ends t g).val:=congrArg Fin.val h
      have hw:(ends e).2=(ends g).1:=Fin.ext hv
      exact hdisj (a:=(ends e).2) (by simp) (by simp [hw])
    · have hv:(u1 ends t e).val=(u1 ends t g).val:=congrArg Fin.val h
      have hw:(ends e).2=(ends g).2:=Fin.ext hv
      exact hdisj (a:=(ends e).2) (by simp) (by simp [hw])
  rw [b6,Finset.card_biUnion hpw]
  have h2:∀ e ∈ S,({u0 ends t e,u1 ends t e}:Finset (Fin (v+2 * m+t))).card=2:=by
    intro e _
    rw [Finset.card_insert_of_notMem,Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact b23 ends hends t e
  rw [Finset.sum_const_nat h2,Nat.mul_comm]
private lemma b26 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (S:Finset (Fin m)):Disjoint (b13 v m t) (b6 ends t S):=by
  rw [Finset.disjoint_left]
  intro x hp hu
  rw [b6,Finset.mem_biUnion] at hu
  rcases hu with ⟨e,_,hx⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact b22 ends t e hp
  · exact b21 ends t e hp
private lemma b39 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (t:Nat)
    (S:Finset (Fin m)) (hM:IsMatching ends S) :
    (remSet ends t S).card=v+t - 2 * S.card:=by
  rw [remSet,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin,
    Finset.card_union_of_disjoint (b26 ends t S),
    b38,b35 ends hends t S hM]
  omega
private lemma b18 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (S:Finset (Fin m)) (hM:IsMatching ends S)
    {e1 e2:Fin m} (he1:e1 ∈ S) (he2:e2 ∈ S)
    {x:Fin (v+2 * m+t)}
    (hx1:x=u0 ends t e1∨x=u1 ends t e1)
    (hx2:x=u0 ends t e2∨x=u1 ends t e2):e1=e2:=by
  by_contra hne
  have hdisj:=hM e1 he1 e2 he2 hne
  rw [Finset.disjoint_left] at hdisj
  rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
  · have hv:(u0 ends t e1).val=(u0 ends t e2).val:=congrArg Fin.val h
    have hw:(ends e1).1=(ends e2).1:=Fin.ext hv
    exact hdisj (a:=(ends e1).1) (by simp) (by simp [hw])
  · have hv:(u0 ends t e1).val=(u1 ends t e2).val:=congrArg Fin.val h
    have hw:(ends e1).1=(ends e2).2:=Fin.ext hv
    exact hdisj (a:=(ends e1).1) (by simp) (by simp [hw])
  · have hv:(u1 ends t e1).val=(u0 ends t e2).val:=congrArg Fin.val h
    have hw:(ends e1).2=(ends e2).1:=Fin.ext hv
    exact hdisj (a:=(ends e1).2) (by simp) (by simp [hw])
  · have hv:(u1 ends t e1).val=(u1 ends t e2).val:=congrArg Fin.val h
    have hw:(ends e1).2=(ends e2).2:=Fin.ext hv
    exact hdisj (a:=(ends e1).2) (by simp) (by simp [hw])
private def b25 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (e:Fin m) (isOdd:Bool):Fin (v+2 * m+t) :=
  if hS:e ∈ S then
    if isOdd then
      if dir ⟨e,hS⟩ then u0 ends t e else u1 ends t e
    else
      if dir ⟨e,hS⟩ then u1 ends t e else u0 ends t e
  else
    if isOdd then p0 v m t e else p1 v m t e
private def b32 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (e:S) (x:Fin (v+2 * m+t)):Fin (v+2 * m+t) :=
  if x=u0 ends t e.1 then
    if dir e then p1 v m t e.1 else p0 v m t e.1
  else
    if dir e then p0 v m t e.1 else p1 v m t e.1
private noncomputable def buildFun {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (x:Fin (v+2 * m+t)):Fin (v+2 * m+t) :=
  if hp:x ∈ b13 v m t then
    let e:Fin m:=⟨(x.val - v) / 2,by
      have h1:v ≤ x.val∧x.val < v+2 * m:=(Finset.mem_filter.mp hp).2
      omega⟩
    b25 ends t S dir e (decide ((x.val - v) % 2=1))
  else if hu:x ∈ b6 ends t S then
    let hex:∃ e ∈ S,x=u0 ends t e∨x=u1 ends t e:=by
      rw [b6,Finset.mem_biUnion] at hu
      rcases hu with ⟨e,he,hx⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      exact ⟨e,he,hx⟩
    let e:Fin m:=Classical.choose hex
    have hspec:e ∈ S∧(x=u0 ends t e∨x=u1 ends t e):=Classical.choose_spec hex
    b32 ends t S dir ⟨e,hspec.1⟩ x
  else
    have hr:x ∈ remSet ends t S:=by
      rw [remSet,Finset.mem_sdiff,Finset.mem_union]
      exact ⟨Finset.mem_univ _,fun h=>h.elim hp hu⟩
    (Q ⟨x,hr⟩).val
private lemma b4 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (e:Fin m) (hS:e ∉ S) :
    buildFun ends t S dir Q (p0 v m t e)=p1 v m t e:=by
  have hp:=b15 v m t e
  unfold buildFun
  simp only [hp,↓reduceDIte]
  have he:(⟨((p0 v m t e).val - v) / 2,by
      have h1:v ≤ (p0 v m t e).val∧(p0 v m t e).val < v+2 * m:=(Finset.mem_filter.mp hp).2
      omega⟩:Fin m)=e:=by
    apply Fin.ext
    simp only [p0]
    omega
  have hb:decide (((p0 v m t e).val - v) % 2=1)=false:=by
    rw [decide_eq_false_iff_not]
    simp only [p0]
    omega
  rw [he,hb]
  simp only [b25,hS,↓reduceDIte,Bool.false_eq_true,↓reduceIte]
private lemma b16 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (e:Fin m) (hS:e ∉ S) :
    buildFun ends t S dir Q (p1 v m t e)=p0 v m t e:=by
  have hp:=b14 v m t e
  unfold buildFun
  simp only [hp,↓reduceDIte]
  have he:(⟨((p1 v m t e).val - v) / 2,by
      have h1:v ≤ (p1 v m t e).val∧(p1 v m t e).val < v+2 * m:=(Finset.mem_filter.mp hp).2
      omega⟩:Fin m)=e:=by
    apply Fin.ext
    simp only [p1]
    omega
  have hb:decide (((p1 v m t e).val - v) % 2=1)=true:=by
    rw [decide_eq_true_eq]
    simp only [p1]
    omega
  rw [he,hb]
  simp only [b25,hS,↓reduceDIte,↓reduceIte]
private lemma b10 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (e:Fin m) (hS:e ∈ S) :
    buildFun ends t S dir Q (p0 v m t e) =
      if dir ⟨e,hS⟩ then u1 ends t e else u0 ends t e:=by
  have hp:=b15 v m t e
  unfold buildFun
  simp only [hp,↓reduceDIte]
  have he:(⟨((p0 v m t e).val - v) / 2,by
      have h1:v ≤ (p0 v m t e).val∧(p0 v m t e).val < v+2 * m:=(Finset.mem_filter.mp hp).2
      omega⟩:Fin m)=e:=by
    apply Fin.ext
    simp only [p0]
    omega
  have hb:decide (((p0 v m t e).val - v) % 2=1)=false:=by
    rw [decide_eq_false_iff_not]
    simp only [p0]
    omega
  rw [he,hb]
  simp only [b25,hS,↓reduceDIte,Bool.false_eq_true,↓reduceIte]
private lemma b17 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (e:Fin m) (hS:e ∈ S) :
    buildFun ends t S dir Q (p1 v m t e) =
      if dir ⟨e,hS⟩ then u0 ends t e else u1 ends t e:=by
  have hp:=b14 v m t e
  unfold buildFun
  simp only [hp,↓reduceDIte]
  have he:(⟨((p1 v m t e).val - v) / 2,by
      have h1:v ≤ (p1 v m t e).val∧(p1 v m t e).val < v+2 * m:=(Finset.mem_filter.mp hp).2
      omega⟩:Fin m)=e:=by
    apply Fin.ext
    simp only [p1]
    omega
  have hb:decide (((p1 v m t e).val - v) % 2=1)=true:=by
    rw [decide_eq_true_eq]
    simp only [p1]
    omega
  rw [he,hb]
  simp only [b25,hS,↓reduceDIte,↓reduceIte]
private lemma b9 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (e:Fin m) (hS:e ∈ S) :
    buildFun ends t S dir Q (u0 ends t e) =
      if dir ⟨e,hS⟩ then p1 v m t e else p0 v m t e:=by
  have hnp:=b22 ends t e
  have hu:u0 ends t e ∈ b6 ends t S:=by
    rw [b6,Finset.mem_biUnion]
    exact ⟨e,hS,by simp⟩
  unfold buildFun
  simp only [hnp,hu,↓reduceDIte]
  set hex:∃ g ∈ S,u0 ends t e=u0 ends t g∨u0 ends t e=u1 ends t g:=by
    rw [b6,Finset.mem_biUnion] at hu
    rcases hu with ⟨g,hg,hx⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    exact ⟨g,hg,hx⟩
  have hspec:=Classical.choose_spec hex
  have heq:Classical.choose hex=e :=
    b18 ends t S hM hspec.1 hS hspec.2 (Or.inl rfl)
  have hsub:(⟨Classical.choose hex,hspec.1⟩:S)=⟨e,hS⟩:=Subtype.ext heq
  rw [hsub]
  simp only [b32,↓reduceIte]
private lemma b8 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (e:Fin m) (hS:e ∈ S) :
    buildFun ends t S dir Q (u1 ends t e) =
      if dir ⟨e,hS⟩ then p0 v m t e else p1 v m t e:=by
  have hnp:=b21 ends t e
  have hu:u1 ends t e ∈ b6 ends t S:=by
    rw [b6,Finset.mem_biUnion]
    exact ⟨e,hS,by simp⟩
  unfold buildFun
  simp only [hnp,hu,↓reduceDIte]
  set hex:∃ g ∈ S,u1 ends t e=u0 ends t g∨u1 ends t e=u1 ends t g:=by
    rw [b6,Finset.mem_biUnion] at hu
    rcases hu with ⟨g,hg,hx⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    exact ⟨g,hg,hx⟩
  have hspec:=Classical.choose_spec hex
  have heq:Classical.choose hex=e :=
    b18 ends t S hM hspec.1 hS hspec.2 (Or.inr rfl)
  have hsub:(⟨Classical.choose hex,hspec.1⟩:S)=⟨e,hS⟩:=Subtype.ext heq
  rw [hsub]
  have hne:u1 ends t e≠u0 ends t e:=(b23 ends hends t e).symm
  simp only [b32,hne,↓reduceIte]
private lemma b20 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (t:Nat) (S:Finset (Fin m)) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    {x:Fin (v+2 * m+t)} (hx:x ∈ remSet ends t S) :
    buildFun ends t S dir Q x=(Q ⟨x,hx⟩).val:=by
  have hnot:x ∉ b13 v m t ∪ b6 ends t S:=(Finset.mem_sdiff.mp hx).2
  rw [Finset.mem_union,not_or] at hnot
  unfold buildFun
  simp only [hnot.1,hnot.2,↓reduceDIte]
private lemma b19 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) (dir:S → Bool)
    (Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S})
    (hQ:Function.Involutive Q) :
    Function.Involutive (buildFun ends t S dir Q):=by
  intro x
  by_cases hp:x ∈ b13 v m t
  · rcases b24 hp with ⟨e,rfl | rfl⟩
    · by_cases hS:e ∈ S
      · rw [b10 ends t S dir Q e hS]
        cases hd:dir ⟨e,hS⟩
        · simp only [Bool.false_eq_true,↓reduceIte]
          rw [b9 ends t S hM dir Q e hS,hd]
          rfl
        · simp only [↓reduceIte]
          rw [b8 ends hends t S hM dir Q e hS,hd]
          rfl
      · rw [b4 ends t S dir Q e hS,b16 ends t S dir Q e hS]
    · by_cases hS:e ∈ S
      · rw [b17 ends t S dir Q e hS]
        cases hd:dir ⟨e,hS⟩
        · simp only [Bool.false_eq_true,↓reduceIte]
          rw [b8 ends hends t S hM dir Q e hS,hd]
          rfl
        · simp only [↓reduceIte]
          rw [b9 ends t S hM dir Q e hS,hd]
          rfl
      · rw [b16 ends t S dir Q e hS,b4 ends t S dir Q e hS]
  · by_cases hu:x ∈ b6 ends t S
    · rw [b6,Finset.mem_biUnion] at hu
      rcases hu with ⟨e,hS,hx⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [b9 ends t S hM dir Q e hS]
        cases hd:dir ⟨e,hS⟩
        · simp only [Bool.false_eq_true,↓reduceIte]
          rw [b10 ends t S dir Q e hS,hd]
          rfl
        · simp only [↓reduceIte]
          rw [b17 ends t S dir Q e hS,hd]
          rfl
      · rw [b8 ends hends t S hM dir Q e hS]
        cases hd:dir ⟨e,hS⟩
        · simp only [Bool.false_eq_true,↓reduceIte]
          rw [b17 ends t S dir Q e hS,hd]
          rfl
        · simp only [↓reduceIte]
          rw [b10 ends t S dir Q e hS,hd]
          rfl
    · have hr:x ∈ remSet ends t S:=by
        rw [remSet,Finset.mem_sdiff,Finset.mem_union]
        exact ⟨Finset.mem_univ _,fun h=>h.elim hp hu⟩
      rw [b20 ends t S dir Q hr,b20 ends t S dir Q (Q ⟨x,hr⟩).2]
      exact congrArg Subtype.val (hQ ⟨x,hr⟩)
private noncomputable def buildPerm {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) (dir:S → Bool)
    (Q:{Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} //
      Function.Involutive Q}) :
    Equiv.Perm (Fin (v+2 * m+t)) :=
  (b19 ends hends t S hM dir Q.1 Q.2).toPerm
private lemma b30 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) (dir:S → Bool)
    (Q:{Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} //
      Function.Involutive Q}) :
    Wins ends t (buildPerm ends hends t S hM dir Q):=by
  refine ⟨b19 ends hends t S hM dir Q.1 Q.2,?_⟩
  intro R hR
  rw [Finset.mem_image] at hR
  rcases hR with ⟨⟨e,b⟩,_,rfl⟩
  by_cases hS:e ∈ S
  · cases b with
    | false =>
      refine ⟨u0 ends t e,?_,?_,?_⟩
      · rw [b7]
        right;right;rfl
      · rw [b7]
        have hv:buildPerm ends hends t S hM dir Q (u0 ends t e) =
            if dir ⟨e,hS⟩ then p1 v m t e else p0 v m t e :=
          b9 ends t S hM dir Q.1 e hS
        rw [hv]
        cases dir ⟨e,hS⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have hv:buildPerm ends hends t S hM dir Q (u0 ends t e) =
            if dir ⟨e,hS⟩ then p1 v m t e else p0 v m t e :=
          b9 ends t S hM dir Q.1 e hS
        rw [hv]
        have hlt:=(ends e).1.isLt
        cases dir ⟨e,hS⟩ <;> intro h <;>
          have:=congrArg Fin.val h <;> simp only [p0,p1,u0,Bool.false_eq_true,↓reduceIte] at this <;> omega
    | true =>
      refine ⟨u1 ends t e,?_,?_,?_⟩
      · rw [b7]
        right;right;rfl
      · rw [b7]
        have hv:buildPerm ends hends t S hM dir Q (u1 ends t e) =
            if dir ⟨e,hS⟩ then p0 v m t e else p1 v m t e :=
          b8 ends hends t S hM dir Q.1 e hS
        rw [hv]
        cases dir ⟨e,hS⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · have hv:buildPerm ends hends t S hM dir Q (u1 ends t e) =
            if dir ⟨e,hS⟩ then p0 v m t e else p1 v m t e :=
          b8 ends hends t S hM dir Q.1 e hS
        rw [hv]
        have hlt:=(ends e).2.isLt
        cases dir ⟨e,hS⟩ <;> intro h <;>
          have:=congrArg Fin.val h <;> simp only [p0,p1,u1,Bool.false_eq_true,↓reduceIte] at this <;> omega
  · refine ⟨p0 v m t e,?_,?_,?_⟩
    · rw [b7]
      left;rfl
    · rw [b7]
      have hv:buildPerm ends hends t S hM dir Q (p0 v m t e)=p1 v m t e :=
        b4 ends t S dir Q.1 e hS
      rw [hv]
      right;left;rfl
    · have hv:buildPerm ends hends t S hM dir Q (p0 v m t e)=p1 v m t e :=
        b4 ends t S dir Q.1 e hS
      rw [hv]
      intro h
      have:=congrArg Fin.val h
      simp only [p0,p1] at this
      omega
private lemma b34 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) (dir:S → Bool)
    (Q:{Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} //
      Function.Involutive Q}) :
    Active (v:=v) t (buildPerm ends hends t S hM dir Q)=S:=by
  ext e
  rw [b12]
  change buildFun ends t S dir Q.1 (p0 v m t e)≠p1 v m t e↔e ∈ S
  by_cases hS:e ∈ S
  · simp only [hS,iff_true]
    rw [b10 ends t S dir Q.1 e hS]
    have hlt1:=(ends e).1.isLt
    have hlt2:=(ends e).2.isLt
    cases dir ⟨e,hS⟩ <;> intro h <;>
      have:=congrArg Fin.val h <;> simp only [p1,u0,u1,Bool.false_eq_true,↓reduceIte] at this <;> omega
  · simp only [hS,iff_false,not_not]
    exact b4 ends t S dir Q.1 e hS
private lemma b37 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m))
    (P:Equiv.Perm (Fin (v+2 * m+t)))
    (hW:Wins ends t P) (hA:Active (v:=v) t P=S)
    {x:Fin (v+2 * m+t)} (hx:x ∈ remSet ends t S) :
    P x ∈ remSet ends t S:=by
  have hnot:x ∉ b13 v m t ∪ b6 ends t S:=(Finset.mem_sdiff.mp hx).2
  rw [Finset.mem_union,not_or] at hnot
  rw [remSet,Finset.mem_sdiff,Finset.mem_union]
  refine ⟨Finset.mem_univ _,?_⟩
  rintro (hp | hu)
  · rcases b24 hp with ⟨e,heq | heq⟩
    · by_cases hS:e ∈ S
      · have heA:e ∈ Active (v:=v) t P:=hA.symm ▸ hS
        have hpair:=b5 ends hends t P hW e heA
        have hxEq:x=P (p0 v m t e):=by rw [← heq,hW.1]
        apply hnot.2
        rw [b6,Finset.mem_biUnion]
        rcases hpair with ⟨h0,_⟩ | ⟨h0,_⟩
        · exact ⟨e,hS,by simp [hxEq,h0]⟩
        · exact ⟨e,hS,by simp [hxEq,h0]⟩
      · have hnotA:e ∉ Active (v:=v) t P:=fun h=>hS (hA ▸ h)
        rw [b12,not_not] at hnotA
        have hxEq:x=p1 v m t e:=by rw [← hnotA,← heq,hW.1]
        exact hnot.1 (hxEq ▸ b14 v m t e)
    · by_cases hS:e ∈ S
      · have heA:e ∈ Active (v:=v) t P:=hA.symm ▸ hS
        have hpair:=b5 ends hends t P hW e heA
        have hxEq:x=P (p1 v m t e):=by rw [← heq,hW.1]
        apply hnot.2
        rw [b6,Finset.mem_biUnion]
        rcases hpair with ⟨_,h1⟩ | ⟨_,h1⟩
        · exact ⟨e,hS,by simp [hxEq,h1]⟩
        · exact ⟨e,hS,by simp [hxEq,h1]⟩
      · have hnotA:e ∉ Active (v:=v) t P:=fun h=>hS (hA ▸ h)
        rw [b12,not_not] at hnotA
        have h10:P (p1 v m t e)=p0 v m t e:=by rw [← hnotA,hW.1]
        have hxEq:x=p0 v m t e:=by rw [← h10,← heq,hW.1]
        exact hnot.1 (hxEq ▸ b15 v m t e)
  · rw [b6,Finset.mem_biUnion] at hu
    rcases hu with ⟨e,hS,hPx⟩
    have heA:e ∈ Active (v:=v) t P:=hA.symm ▸ hS
    simp only [Finset.mem_insert,Finset.mem_singleton] at hPx
    have hpair:=b5 ends hends t P hW e heA
    apply hnot.1
    rcases hPx with hPx | hPx
    · have hxEq:x=P (u0 ends t e):=by rw [← hPx,hW.1]
      rcases hpair with ⟨h0,_⟩ | ⟨_,h1⟩
      · have:x=p0 v m t e:=by rw [hxEq,← h0,hW.1]
        exact this ▸ b15 v m t e
      · have:x=p1 v m t e:=by rw [hxEq,← h1,hW.1]
        exact this ▸ b14 v m t e
    · have hxEq:x=P (u1 ends t e):=by rw [← hPx,hW.1]
      rcases hpair with ⟨_,h1⟩ | ⟨h0,_⟩
      · have:x=p1 v m t e:=by rw [hxEq,← h1,hW.1]
        exact this ▸ b14 v m t e
      · have:x=p0 v m t e:=by rw [hxEq,← h0,hW.1]
        exact this ▸ b15 v m t e
private def b0 {v m:Nat} (ends:Fin m → Fin v × Fin v) (t:Nat)
    (S:Finset (Fin m)) (P:Equiv.Perm (Fin (v+2 * m+t))):S → Bool :=
  fun e=>decide (P (p0 v m t e.1)=u1 ends t e.1)
private def b40 {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m))
    (P:Equiv.Perm (Fin (v+2 * m+t)))
    (hW:Wins ends t P) (hA:Active (v:=v) t P=S) :
    {Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} //
      Function.Involutive Q} :=
  let f:{x:Fin (v+2 * m+t) // x ∈ remSet ends t S} →
      {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} :=
    fun x=>⟨P x.1,b37 ends hends t S P hW hA x.2⟩
  have hf:Function.Involutive f:=fun x=>Subtype.ext (hW.1 x.1)
  ⟨hf.toPerm,hf⟩
private noncomputable def fiberEquiv {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2)
    (t:Nat) (S:Finset (Fin m)) (hM:IsMatching ends S) :
    {P:Equiv.Perm (Fin (v+2 * m+t)) // Wins ends t P∧Active (v:=v) t P=S} ≃
      (S → Bool) × {Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} //
        Function.Involutive Q} where
  toFun P:=(b0 ends t S P.1,b40 ends hends t S P.1 P.2.1 P.2.2)
  invFun dq:=⟨buildPerm ends hends t S hM dq.1 dq.2,
    b30 ends hends t S hM dq.1 dq.2,
    b34 ends hends t S hM dq.1 dq.2⟩
  left_inv:=by
    rintro ⟨P,hW,hA⟩
    apply Subtype.ext
    ext x
    change (buildFun ends t S (b0 ends t S P)
      (b40 ends hends t S P hW hA).1 x).val=(P x).val
    congr 1
    by_cases hp:x ∈ b13 v m t
    · rcases b24 hp with ⟨e,rfl | rfl⟩
      · by_cases hS:e ∈ S
        · rw [b10 ends t S _ _ e hS]
          have heA:e ∈ Active (v:=v) t P:=hA.symm ▸ hS
          rcases b5 ends hends t P hW e heA with ⟨h0,_⟩ | ⟨h0,_⟩
          · have hd:b0 ends t S P ⟨e,hS⟩=false:=by
              simp only [b0,decide_eq_false_iff_not,h0]
              exact b23 ends hends t e
            rw [hd]
            exact h0.symm
          · have hd:b0 ends t S P ⟨e,hS⟩=true:=by
              simp only [b0,decide_eq_true_eq,h0]
            rw [hd]
            exact h0.symm
        · rw [b4 ends t S _ _ e hS]
          have hnotA:e ∉ Active (v:=v) t P:=fun h=>hS (hA ▸ h)
          rw [b12,not_not] at hnotA
          exact hnotA.symm
      · by_cases hS:e ∈ S
        · rw [b17 ends t S _ _ e hS]
          have heA:e ∈ Active (v:=v) t P:=hA.symm ▸ hS
          rcases b5 ends hends t P hW e heA with ⟨h0,h1⟩ | ⟨h0,h1⟩
          · have hd:b0 ends t S P ⟨e,hS⟩=false:=by
              simp only [b0,decide_eq_false_iff_not,h0]
              exact b23 ends hends t e
            rw [hd]
            exact h1.symm
          · have hd:b0 ends t S P ⟨e,hS⟩=true:=by
              simp only [b0,decide_eq_true_eq,h0]
            rw [hd]
            exact h1.symm
        · rw [b16 ends t S _ _ e hS]
          have hnotA:e ∉ Active (v:=v) t P:=fun h=>hS (hA ▸ h)
          rw [b12,not_not] at hnotA
          have h10:P (p1 v m t e)=p0 v m t e:=by rw [← hnotA,hW.1]
          exact h10.symm
    · by_cases hu:x ∈ b6 ends t S
      · rw [b6,Finset.mem_biUnion] at hu
        rcases hu with ⟨e,hS,hx⟩
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        have heA:e ∈ Active (v:=v) t P:=hA.symm ▸ hS
        rcases hx with rfl | rfl
        · rw [b9 ends t S hM _ _ e hS]
          rcases b5 ends hends t P hW e heA with ⟨h0,_⟩ | ⟨h0,h1⟩
          · have hd:b0 ends t S P ⟨e,hS⟩=false:=by
              simp only [b0,decide_eq_false_iff_not,h0]
              exact b23 ends hends t e
            simp only [hd,Bool.false_eq_true,↓reduceIte]
            rw [← h0,hW.1]
          · have hd:b0 ends t S P ⟨e,hS⟩=true:=by
              simp only [b0,decide_eq_true_eq,h0]
            simp only [hd,↓reduceIte]
            rw [← h1,hW.1]
        · rw [b8 ends hends t S hM _ _ e hS]
          rcases b5 ends hends t P hW e heA with ⟨h0,h1⟩ | ⟨h0,_⟩
          · have hd:b0 ends t S P ⟨e,hS⟩=false:=by
              simp only [b0,decide_eq_false_iff_not,h0]
              exact b23 ends hends t e
            simp only [hd,Bool.false_eq_true,↓reduceIte]
            rw [← h1,hW.1]
          · have hd:b0 ends t S P ⟨e,hS⟩=true:=by
              simp only [b0,decide_eq_true_eq,h0]
            simp only [hd,↓reduceIte]
            rw [← h0,hW.1]
      · have hr:x ∈ remSet ends t S:=by
          rw [remSet,Finset.mem_sdiff,Finset.mem_union]
          exact ⟨Finset.mem_univ _,fun h=>h.elim hp hu⟩
        rw [b20 ends t S _ _ hr]
        rfl
  right_inv:=by
    rintro ⟨dir,Q⟩
    apply Prod.ext
    · funext ⟨e,hS⟩
      simp only [b0]
      change decide (buildFun ends t S dir Q.1 (p0 v m t e)=u1 ends t e)=dir ⟨e,hS⟩
      rw [b10 ends t S dir Q.1 e hS]
      cases hd:dir ⟨e,hS⟩
      · simp only [Bool.false_eq_true,↓reduceIte,decide_eq_false_iff_not]
        exact b23 ends hends t e
      · simp only [↓reduceIte,decide_eq_true_eq]
    · apply Subtype.ext
      ext ⟨x,hx⟩
      change (buildFun ends t S dir Q.1 x).val=(Q.1 ⟨x,hx⟩).1.val
      rw [b20 ends t S dir Q.1 hx]
private def b29 {α β : Type*} (e : α ≃ β) :
    {P:Equiv.Perm α // Function.Involutive P} ≃
      {Q:Equiv.Perm β // Function.Involutive Q} where
  toFun P:=⟨e.symm.trans (P.1.trans e),fun y=>by
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    rw [P.2,Equiv.apply_symm_apply]⟩
  invFun Q:=⟨e.trans (Q.1.trans e.symm),fun x=>by
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    rw [Q.2,Equiv.symm_apply_apply]⟩
  left_inv P:=by
    apply Subtype.ext
    ext x
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  right_inv Q:=by
    apply Subtype.ext
    ext y
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
private lemma card_fiber {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (t:Nat) (S:Finset (Fin m)) :
    Nat.card {P:Equiv.Perm (Fin (v+2 * m+t)) //
      Wins ends t P∧Active (v:=v) t P=S} =
    if IsMatching ends S then
      2 ^ S.card * Nat.card {P:Equiv.Perm (Fin (v+t - 2 * S.card)) // Function.Involutive P}
    else 0:=by
  split_ifs with hM
  · have hcard:Fintype.card {x:Fin (v+2 * m+t) // x ∈ remSet ends t S} =
        v+t - 2 * S.card:=by
      rw [Fintype.card_coe]
      exact b39 ends hends t S hM
    let eRem:=Fintype.equivFinOfCardEq hcard
    let eTotal:=(fiberEquiv ends hends t S hM).trans
      (Equiv.prodCongr (Equiv.refl _) (b29 eRem))
    rw [Nat.card_congr eTotal,Nat.card_prod,Nat.card_eq_fintype_card (α := (S → Bool)),
      Fintype.card_fun,Fintype.card_bool,Fintype.card_coe]
  · have hNo:∀ P:{P:Equiv.Perm (Fin (v+2 * m+t)) //
        Wins ends t P∧Active (v:=v) t P=S},False :=
      fun ⟨P,hW,hA⟩=>hM (hA ▸ b33 ends t P hW)
    let e0:{P:Equiv.Perm (Fin (v+2 * m+t)) //
        Wins ends t P∧Active (v:=v) t P=S} ≃ Fin 0 :=
      { toFun:=fun P=>(hNo P).elim
        invFun:=fun x=>x.elim0
        left_inv:=fun P=>(hNo P).elim
        right_inv:=fun x=>x.elim0 }
    rw [Nat.card_congr e0,Nat.card_eq_fintype_card,Fintype.card_fin]
private lemma wins_pos {v m:Nat} (ends:Fin m → Fin v × Fin v)
    (hends:∀ e,(ends e).1≠(ends e).2) (t:Nat) :
    0 < Nat.card {P:Equiv.Perm (Fin (v+2 * m+t)) // Wins ends t P}:=by
  have hM0:IsMatching ends ∅ := fun _ he=>False.elim (Finset.notMem_empty _ he)
  let dir0:(∅ : Finset (Fin m)) → Bool:=fun e=>False.elim (Finset.notMem_empty e.1 e.2)
  let Q0:{Q:Equiv.Perm {x:Fin (v+2 * m+t) // x ∈ remSet ends t ∅} //
      Function.Involutive Q}:=⟨Equiv.refl _,fun _=>rfl⟩
  have hNe:Nonempty {P:Equiv.Perm (Fin (v+2 * m+t)) // Wins ends t P} :=
    ⟨⟨buildPerm ends hends t ∅ hM0 dir0 Q0,b30 ends hends t ∅ hM0 dir0 Q0⟩⟩
  exact @Nat.card_pos _ hNe _
end L9
theorem L9_thm:∀ (v m:Nat) (ends:Fin m → Fin v × Fin v),(∀ e,(ends e).1≠(ends e).2) →
  let vertices:=fun e:Fin m=>({(ends e).1,(ends e).2}:Finset (Fin v))
  let matching:=fun S:Finset (Fin m)=>∀ e ∈ S,∀ g ∈ S,e≠g → Disjoint (vertices e) (vertices g)
  let tests:=Finset.univ.image (fun z:Fin m × Bool =>
    ({v+2*z.1.val,v+2*z.1.val+1,if z.2 then (ends z.1).2.val else (ends z.1).1.val}:Finset Nat))
  let I:=fun k:Nat=>Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P}
  tests.card=2*m∧(∀ R ∈ tests,R.card=3 ∧
    (tests.filter (fun T=>T≠R∧(T ∩ R).card=2)).card=1) ∧
  ∀ t:Nat,
    let k:=v+2*m+t
    let wins:=fun P:Equiv.Perm (Fin k)=>Function.Involutive P ∧
      ∀ R ∈ tests,∃ u:Fin k,u.val ∈ R∧(P u).val ∈ R∧P u≠u
    let active:=fun P:Equiv.Perm (Fin k)=>Finset.univ.filter (fun e:Fin m =>
      ¬ ∃ u:Fin k,u.val=v+2*e.val∧(P u).val=v+2*e.val+1)
    (∀ S:Finset (Fin m),Nat.card {P:Equiv.Perm (Fin k) // wins P∧active P=S} =
      if matching S then 2^S.card * I (v+t-2*S.card) else 0) ∧
    0 < Nat.card {P:Equiv.Perm (Fin k) // wins P} ∧
    Nat.card {P:Equiv.Perm (Fin k) // wins P} =
      (Finset.univ.filter matching).sum (fun S=>2^S.card * I (v+t-2*S.card)):=by
  intro v m ends hends
  dsimp only
  refine ⟨L9.tests_card ends hends,?_,?_⟩
  · intro R hR
    rw [Finset.mem_image] at hR
    rcases hR with ⟨z,_,rfl⟩
    exact ⟨L9.testOf_card ends z,
      L9.twin_filter_card ends hends z⟩
  · intro t
    have hfib:∀ S:Finset (Fin m),
        Nat.card {P:Equiv.Perm (Fin (v+2 * m+t)) //
          L9.Wins ends t P ∧
          L9.Active (v:=v) t P=S} =
        if L9.IsMatching ends S then
          2 ^ S.card * Nat.card {P:Equiv.Perm (Fin (v+t - 2 * S.card)) // Function.Involutive P}
        else 0 :=
      L9.card_fiber ends hends t
    refine ⟨?_,L9.wins_pos ends hends t,?_⟩
    · intro S
      exact hfib S
    · let ePart:{P:Equiv.Perm (Fin (v+2 * m+t)) //
          L9.Wins ends t P} ≃
          Σ S:Finset (Fin m),{P:Equiv.Perm (Fin (v+2 * m+t)) //
            L9.Wins ends t P ∧
            L9.Active (v:=v) t P=S} :=
        { toFun:=fun ⟨P,hW⟩=>⟨L9.Active (v:=v) t P,⟨P,hW,rfl⟩⟩
          invFun:=fun ⟨_,⟨P,hW,_⟩⟩=>⟨P,hW⟩
          left_inv:=fun ⟨_,_⟩=>rfl
          right_inv:=fun ⟨_,⟨_,_,hA⟩⟩=>by subst hA;rfl }
      change Nat.card {P:Equiv.Perm (Fin (v+2 * m+t)) //
          L9.Wins ends t P}=_
      rw [Nat.card_congr ePart,Nat.card_sigma,Finset.sum_filter]
      exact Finset.sum_congr rfl (fun S _=>hfib S)
end
section
namespace L4
open Finset
lemma c64 (I:ℕ → ℕ) (t f h:ℕ) :
    f.choose h * t.descFactorial h * I (t-h) =
      (t.choose h * I (t-h)) * f.descFactorial h:=by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  ring
lemma c65 (d:ℕ) (f:Fin (d+1) → ℕ) :
    (Matrix.of fun h j:Fin (d+1)=>((f j).descFactorial h.val:ℤ)).det =
      (Matrix.vandermonde (fun j=>(f j:ℤ))).det:=by
  have h:=Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun j=>(f j:ℤ)) (fun h:Fin (d+1)=>descPochhammer ℤ h.val)
    (fun h=>descPochhammer_natDegree ℤ h.val)
    (fun h=>monic_descPochhammer ℤ h.val)
  rw [← Matrix.det_transpose]
  rw [h]
  congr 1
  ext i j
  simp [Matrix.transpose_apply,descPochhammer_eval_eq_descFactorial]
lemma c66 (I:ℕ → ℕ) (hI:I 0=1) (d:ℕ) :
    (Matrix.of fun t h:Fin (d+1)=>((t.val.choose h.val * I (t.val-h.val):ℕ):ℤ)).det=1:=by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hI]
  · intro i j hij
    have hij':i.val < j.val:=hij
    simp [Nat.choose_eq_zero_of_lt hij']
lemma c53 (I:ℕ → ℕ) (d:ℕ) (f:Fin (d+1) → ℕ) :
    (Matrix.of fun t j:Fin (d+1) =>
      (((range (t.val+1)).sum (fun h =>
        (f j).choose h * t.val.descFactorial h * I (t.val-h))):ℤ)) =
    (Matrix.of fun t h:Fin (d+1)=>((t.val.choose h.val * I (t.val-h.val):ℕ):ℤ)) *
    (Matrix.of fun h j:Fin (d+1)=>((f j).descFactorial h.val:ℤ)):=by
  ext t j
  have hn:(∑ h ∈ range (t.val+1),
      (f j).choose h * t.val.descFactorial h * I (t.val-h)) =
      ∑ h:Fin (d+1),(t.val.choose h.val * I (t.val-h.val)) *
        (f j).descFactorial h.val:=by
    rw [show (∑ h:Fin (d+1),(t.val.choose h.val * I (t.val-h.val)) *
        (f j).descFactorial h.val) =
        ∑ h ∈ range (d+1),(t.val.choose h * I (t.val-h)) *
          (f j).descFactorial h from
      Fin.sum_univ_eq_sum_range (fun h=>(t.val.choose h * I (t.val-h)) *
          (f j).descFactorial h) (d+1)]
    simp_rw [c64]
    apply sum_subset (range_mono (by omega:t.val+1 ≤ d+1))
    intro h hh hnot
    have hlt:t.val < h:=by simp only [mem_range,not_lt] at hnot;omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  simp only [Matrix.mul_apply,Matrix.of_apply]
  exact_mod_cast hn
lemma c62 (I:ℕ → ℕ) (hI:I 0=1) (d:ℕ)
    (f:Fin (d+1) → ℕ) :
    (Matrix.of fun t j:Fin (d+1) =>
      (((range (t.val+1)).sum (fun h =>
        (f j).choose h * t.val.descFactorial h * I (t.val-h))):ℤ)).det =
      (Matrix.vandermonde (fun j=>(f j:ℤ))).det:=by
  rw [c53,Matrix.det_mul,c66 I hI,one_mul,c65]
lemma c38 (d e:ℕ) :
    (Matrix.vandermonde (fun j:Fin (d+1)=>((e+2*j.val:ℕ):ℤ))).det =
      (2:ℤ)^(d*(d+1)/2) * ∏ j:Fin (d+1),(j.val.factorial:ℤ):=by
  have he:(fun j:Fin (d+1)=>((e+2*j.val:ℕ):ℤ)) =
      (fun j=>2*(j.val:ℤ)+(e:ℤ)):=by ext j;push_cast;ring
  rw [he,Matrix.det_vandermonde_add]
  have hs:(Matrix.vandermonde (fun j:Fin (d+1)=>2*(j.val:ℤ))) =
      (Matrix.of (fun i j:Fin (d+1)=>(2:ℤ)^j.val *
        Matrix.vandermonde (fun k:Fin (d+1)=>(k.val:ℤ)) i j)):=by
    ext i j
    simp [Matrix.vandermonde_apply,mul_pow]
  rw [hs,Matrix.det_mul_row,Matrix.det_vandermonde_id_eq_superFactorial]
  congr 1
  · rw [prod_pow_eq_pow_sum]
    congr 1
    rw [show (∑ i:Fin (d+1),i.val)=∑ i ∈ range (d+1),i from
      Fin.sum_univ_eq_sum_range (fun i=>i) (d+1),sum_range_id]
    simp [Nat.mul_comm]
  · rw [show (∏ j:Fin (d+1),(j.val.factorial:ℤ)) =
      ∏ j ∈ range (d+1),(j.factorial:ℤ) from
      Fin.prod_univ_eq_prod_range (fun j=>(j.factorial:ℤ)) (d+1),
      ← Nat.cast_prod,Nat.prod_range_succ_factorial]
lemma c34 :
    Nat.card {P:Equiv.Perm (Fin 0) // Function.Involutive P}=1:=by
  have h:Unique {P:Equiv.Perm (Fin 0) // Function.Involutive P} :=
    { default:=⟨Equiv.refl _,fun x=>Fin.elim0 x⟩
      uniq:=fun p=>Subtype.ext (Subsingleton.elim _ _) }
  let:=h
  exact Nat.card_unique
lemma exact_kernel_det (n:ℕ) :
    let I:=fun k:ℕ => Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P}
    let d:=n/2
    let free:=fun j:Fin (d+1)=>n % 2+2*j.val
    let kernel:=fun t f:ℕ => (range (t+1)).sum (fun h =>
      f.choose h * t.descFactorial h * I (t-h))
    let K:Matrix (Fin (d+1)) (Fin (d+1)) ℤ := fun t j=>(kernel t.val (free j):ℤ)
    K.det=(2:ℤ)^(d*(d+1)/2) * ∏ j:Fin (d+1),(j.val.factorial:ℤ):=by
  dsimp only
  have h:=(c62 (fun k:ℕ => Nat.card {P:Equiv.Perm (Fin k) //
      Function.Involutive P}) c34 (n/2)
      (fun j=>n%2+2*j.val)).trans (c38 (n/2) (n%2))
  rw [← h]
  congr 1
  ext t j
  simp only [Matrix.of_apply,Nat.cast_sum,Nat.cast_mul]
def c0 {α β : Type*} (P:Equiv.Perm (α ⊕ β)) (a : α) : α :=
  (P (Sum.inl a)).elim id (fun _=>a)
lemma c7 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (hP:Function.Involutive P):Function.Involutive (c0 P):=by
  intro a
  cases h:P (Sum.inl a) with
  | inl b =>
    have hb:P (Sum.inl b)=Sum.inl a:=by
      rw [← h]
      exact hP _
    simp [c0,h,hb]
  | inr b=>simp [c0,h]
lemma c36 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (a b : α) (hne:b≠a) :
    c0 P a=b↔P (Sum.inl a)=Sum.inl b:=by
  cases h:P (Sum.inl a) with
  | inl c=>simp [c0,h]
  | inr c=>simp [c0,h,Ne.symm hne]
lemma c24 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (R:Set α) :
    (∃ u ∈ R,∃ v ∈ R,u≠v∧P (Sum.inl u)=Sum.inl v) ↔
    ∃ u ∈ R,c0 P u ∈ R∧c0 P u≠u:=by
  constructor
  · rintro ⟨u,hu,v,hv,hne,hP⟩
    have hq:=(c36 P u v (Ne.symm hne)).mpr hP
    exact ⟨u,hu,hq ▸ hv,hq ▸ Ne.symm hne⟩
  · rintro ⟨u,hu,hv,hne⟩
    exact ⟨u,hu,c0 P u,hv,Ne.symm hne,
      (c36 P u (c0 P u) hne).mp rfl⟩
lemma c9 (n:ℕ) (P:Equiv.Perm (Fin n))
    (hP:Function.Involutive P) :
    ∃ j:Fin (n/2+1),
      (univ.filter (fun u=>P u=u)).card=n%2+2*j.val:=by
  let A:=univ.filter (fun u:Fin n=>u < P u)
  let B:=univ.filter (fun u:Fin n=>P u < u)
  let F:=univ.filter (fun u:Fin n=>P u=u)
  have hab:A.card=B.card:=by
    apply card_bij (fun u _=>P u)
    · intro u hu
      simpa only [A,B,mem_filter,mem_univ,true_and,hP u] using hu
    · intro a ha b hb heq
      exact P.injective heq
    · intro b hb
      refine ⟨P b,?_,hP b⟩
      simpa only [A,B,mem_filter,mem_univ,true_and,hP b] using hb
  have hsplit:n=F.card+A.card+B.card:=by
    have h₁:=card_filter_add_card_filter_not (s:=(univ:Finset (Fin n)))
      (fun u=>P u=u)
    have h₂:=card_filter_add_card_filter_not
      (s:=univ.filter (fun u:Fin n=>P u≠u)) (fun u=>u < P u)
    have hA:((univ.filter (fun u:Fin n=>P u≠u)).filter
        (fun u=>u < P u))=A:=by
      ext u
      simp only [A,mem_filter,mem_univ,true_and]
      constructor
      · exact fun h=>h.2
      · exact fun h=>⟨Ne.symm (ne_of_lt h),h⟩
    have hB:((univ.filter (fun u:Fin n=>P u≠u)).filter
        (fun u=>¬u < P u))=B:=by
      ext u
      simp only [B,mem_filter,mem_univ,true_and]
      omega
    rw [hA,hB] at h₂
    simp only [Fintype.card_fin,card_univ] at h₁
    change F.card+_=n at h₁
    calc
      n=F.card+(A.card+B.card):=by rw [h₂];exact h₁.symm
      _=F.card+A.card+B.card:=(Nat.add_assoc _ _ _).symm
  refine ⟨⟨F.card/2,by omega⟩,?_⟩
  change F.card=n%2+2*(F.card/2)
  omega
def c41 (n t:ℕ) (P:Equiv.Perm (Fin (n+t))) :
    Equiv.Perm (Fin n ⊕ Fin t) :=
  (finSumFinEquiv (m:=n) (n:=t)).symm.permCongr P
lemma c17 (n t:ℕ) (P:Equiv.Perm (Fin (n+t)))
    (hP:Function.Involutive P):Function.Involutive (c41 n t P):=by
  intro x
  change finSumFinEquiv.symm
    (P (finSumFinEquiv (finSumFinEquiv.symm (P (finSumFinEquiv x)))))=x
  rw [Equiv.apply_symm_apply,hP (finSumFinEquiv x),Equiv.symm_apply_apply]
def c5 (n t:ℕ) (P:Equiv.Perm (Fin (n+t)))
    (hP:Function.Involutive P):Equiv.Perm (Fin n) :=
  (c7 _ (c17 n t P hP)).toPerm _
lemma c20 (n t:ℕ) (P:Equiv.Perm (Fin (n+t)))
    (hP:Function.Involutive P) :
    Function.Involutive (c5 n t P hP) :=
  c7 _ (c17 n t P hP)
lemma c29 (n t:ℕ) (P:Equiv.Perm (Fin (n+t)))
    (hP:Function.Involutive P) (R:Finset (Fin n)) :
    (∃ u ∈ R,∃ v ∈ R,u≠v∧P (u.castAdd t)=v.castAdd t) ↔
    (∃ u ∈ R,c5 n t P hP u ∈ R ∧
      c5 n t P hP u≠u):=by
  have he (u v:Fin n) :
      c41 n t P (Sum.inl u)=Sum.inl v ↔
        P (u.castAdd t)=v.castAdd t:=by
    simp only [c41,Equiv.permCongr_apply,Equiv.symm_symm,
      Equiv.symm_apply_eq,finSumFinEquiv_apply_left]
  simpa only [he,c5,Function.Involutive.coe_toPerm,
    Set.mem_ofPred_eq] using
      (c24 (c41 n t P) {u | u ∈ R})
lemma c55 {α : Type*} [Finite α] (Q : α → Prop)
    (f : α → ℕ) (d e:ℕ)
    (hf:∀ a,Q a → ∃ j:Fin (d+1),f a=e+2*j.val) :
    Nat.card {a // Q a} =
      ∑ j:Fin (d+1),Nat.card {a // Q a∧f a=e+2*j.val}:=by
  let forget:(Σ j:Fin (d+1),{a // Q a∧f a=e+2*j.val}) → {a // Q a} :=
    fun p=>⟨p.2.val,p.2.property.1⟩
  have hi:Function.Injective forget:=by
    rintro ⟨i,a,ha,hfa⟩ ⟨j,b,hb,hfb⟩ heq
    have hab:a=b:=congrArg Subtype.val heq
    subst b
    have hij:i=j:=Fin.ext (by omega)
    subst j
    rfl
  have hs:Function.Surjective forget:=by
    intro a
    obtain ⟨j,hj⟩:=hf a.val a.property
    exact ⟨⟨j,a.val,a.property,hj⟩,rfl⟩
  have hc:=Nat.card_congr (Equiv.ofBijective forget ⟨hi,hs⟩)
  rw [Nat.card_sigma] at hc
  exact hc.symm
lemma c30 (n:ℕ) (H:Finset (Finset (Fin n))) :
    Nat.card {P:Equiv.Perm (Fin n) // Function.Involutive P ∧
      ∀ R ∈ H,∃ u ∈ R,P u ∈ R∧P u≠u} =
    ∑ j:Fin (n/2+1),Nat.card {P:Equiv.Perm (Fin n) //
      Function.Involutive P ∧
      (∀ R ∈ H,∃ u ∈ R,P u ∈ R∧P u≠u) ∧
      (univ.filter (fun u=>P u=u)).card=n%2+2*j.val}:=by
  classical
  simpa only [and_assoc] using c55
    (fun P:Equiv.Perm (Fin n)=>Function.Involutive P ∧
      ∀ R ∈ H,∃ u ∈ R,P u ∈ R∧P u≠u)
    (fun P=>(univ.filter (fun u=>P u=u)).card) (n/2) (n%2)
    (fun P hP=>c9 n P hP.1)
lemma exact_padding_zero (n:ℕ) (H:Finset (Finset (Fin n))) :
    let I:=fun k:ℕ => Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P}
    let kernel:=fun t f:ℕ => (range (t+1)).sum (fun h =>
      f.choose h * t.descFactorial h * I (t-h))
    Nat.card {P:Equiv.Perm (Fin (n+0)) // Function.Involutive P ∧
      ∀ R ∈ H,∃ u ∈ R,∃ v ∈ R,u≠v∧P (u.castAdd 0)=v.castAdd 0} =
    ∑ j:Fin (n/2+1),kernel 0 (n%2+2*j.val) *
      Nat.card {P:Equiv.Perm (Fin n) //
        Function.Involutive P ∧
        (∀ R ∈ H,∃ u ∈ R,P u ∈ R∧P u≠u) ∧
        (univ.filter (fun u=>P u=u)).card=n%2+2*j.val}:=by
  dsimp only
  simp only [Nat.zero_add,range_one,sum_singleton,Nat.choose_zero_right,
    Nat.descFactorial_zero,mul_one,Nat.sub_zero,c34,one_mul]
  rw [← c30 n H]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro P
  constructor
  · rintro ⟨hP,hw⟩
    refine ⟨hP,?_⟩
    intro R hR
    obtain ⟨u,hu,v,hv,hne,heq⟩:=hw R hR
    have heq':P u=v:=by simpa using heq
    exact ⟨u,hu,heq' ▸ hv,heq' ▸ Ne.symm hne⟩
  · rintro ⟨hP,hw⟩
    refine ⟨hP,?_⟩
    intro R hR
    obtain ⟨u,hu,hv,hne⟩:=hw R hR
    exact ⟨u,hu,P u,hv,Ne.symm hne,by simp⟩
lemma c61 (n:ℕ) (P:Equiv.Perm (Fin n))
    (h:(univ.filter (fun u=>P u=u)).card=n):P=Equiv.refl _:=by
  classical
  have hs:univ.filter (fun u=>P u=u)=univ:=by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    simp [h]
  ext u
  have hu:u ∈ univ.filter (fun u=>P u=u):=by rw [hs];simp
  exact congrArg Fin.val (mem_filter.mp hu).2
lemma c35 (n:ℕ) :
    Nat.card {P:Equiv.Perm (Fin n) // Function.Involutive P ∧
      (univ.filter (fun u=>P u=u)).card=n}=1:=by
  classical
  have h:Unique {P:Equiv.Perm (Fin n) // Function.Involutive P ∧
      (univ.filter (fun u=>P u=u)).card=n} :=
    { default:=⟨Equiv.refl _,by simp [Function.Involutive]⟩
      uniq:=fun P=>Subtype.ext (c61 n P.val P.property.2) }
  let:=h
  exact Nat.card_unique
lemma c47 {α β : Type*} [Finite α] [Fintype β]
    (f : α → β) (Q : β → Prop) [DecidablePred Q] :
    Nat.card {a // Q (f a)}=∑ b:{b // Q b},Nat.card {a // f a=b.val}:=by
  classical
  let forget:(Σ b:{b // Q b},{a // f a=b.val}) → {a // Q (f a)} :=
    fun p=>⟨p.2.val,p.2.property.symm ▸ p.1.property⟩
  have hi:Function.Injective forget:=by
    rintro ⟨⟨b,hb⟩,a,hfa⟩ ⟨⟨c,hc⟩,d,hfd⟩ heq
    have had:a=d:=congrArg Subtype.val heq
    subst d
    have hbc:b=c:=hfa.symm.trans hfd
    subst c
    rfl
  have hs:Function.Surjective forget:=by
    intro a
    exact ⟨⟨⟨f a.val,a.property⟩,a.val,rfl⟩,rfl⟩
  have hc:=Nat.card_congr (Equiv.ofBijective forget ⟨hi,hs⟩)
  rw [Nat.card_sigma] at hc
  exact hc.symm
def c21 (n t:ℕ) :
    {P:Equiv.Perm (Fin (n+t)) // Function.Involutive P} →
    {P:Equiv.Perm (Fin n) // Function.Involutive P} :=
  fun P=>⟨c5 n t P.val P.property,
    c20 n t P.val P.property⟩
def c44 (n:ℕ) (H:Finset (Finset (Fin n))) (P:Equiv.Perm (Fin n)):Prop :=
  ∀ R ∈ H,∃ u ∈ R,P u ∈ R∧P u≠u
lemma c16 (n t:ℕ) (H:Finset (Finset (Fin n)))
    (P:Equiv.Perm (Fin (n+t))) (hP:Function.Involutive P) :
    (∀ R ∈ H,∃ u ∈ R,∃ v ∈ R,u≠v∧P (u.castAdd t)=v.castAdd t) ↔
    c44 n H (c5 n t P hP):=by
  unfold c44
  exact forall_congr' fun R=>forall_congr' fun _ =>
    c29 n t P hP R
open scoped Classical in
lemma c15 (n t:ℕ) (H:Finset (Finset (Fin n))) :
    Nat.card {P:Equiv.Perm (Fin (n+t)) // Function.Involutive P ∧
      ∀ R ∈ H,∃ u ∈ R,∃ v ∈ R,u≠v∧P (u.castAdd t)=v.castAdd t} =
    ∑ Q:{Q:{P:Equiv.Perm (Fin n) // Function.Involutive P} //
      c44 n H Q.val},
      Nat.card {P:{P:Equiv.Perm (Fin (n+t)) // Function.Involutive P} //
        c21 n t P=Q.val}:=by
  classical
  let:=Fintype.ofFinite {Q:{P:Equiv.Perm (Fin n) // Function.Involutive P} //
    c44 n H Q.val}
  rw [← c47 (c21 n t) (fun Q=>c44 n H Q.val)]
  apply Nat.card_congr
  exact
    { toFun:=fun P=>⟨⟨P.val,P.property.1⟩,
        (c16 n t H P.val P.property.1).mp P.property.2⟩
      invFun:=fun P=>⟨P.val.val,P.val.property,
        (c16 n t H P.val.val P.val.property).mpr P.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
noncomputable def crossingPartner {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (a:{a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b}) : β :=
  Classical.choose a.property
lemma c3 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (a:{a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b}) :
    P (Sum.inl a.val)=Sum.inr (crossingPartner P a) :=
  Classical.choose_spec a.property
lemma c10 {α β : Type*} (P:Equiv.Perm (α ⊕ β)) :
    Function.Injective (crossingPartner P):=by
  intro a b h
  apply Subtype.ext
  apply Sum.inl_injective
  apply P.injective
  rw [c3,c3,h]
lemma crossingPartner_reverse {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (hP:Function.Involutive P)
    (a:{a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b}) :
    P (Sum.inr (crossingPartner P a))=Sum.inl a.val:=by
  rw [← c3]
  exact hP _
lemma c37 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (a:{a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b}) :
    c0 P a.val=a.val:=by
  simp [c0,c3 P a]
lemma crossing_card_bounds {α β : Type*} [Finite α] [Finite β]
    (P:Equiv.Perm (α ⊕ β)) :
    Nat.card {a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b} ≤ Nat.card β ∧
    Nat.card {a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b} ≤
      Nat.card {a : α // c0 P a=a}:=by
  constructor
  · exact Nat.card_le_card_of_injective _ (c10 P)
  · let f:{a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b} →
        {a : α // c0 P a=a}:=fun a=>⟨a.val,c37 P a⟩
    apply Nat.card_le_card_of_injective f
    intro a b h
    exact Subtype.ext (congrArg (fun x:{a : α // c0 P a=a}=>x.val) h)
def c31 {α β : Type*} (P:Equiv.Perm (α ⊕ β)) (b : β):Prop :=
  ∀ a : α,P (Sum.inl a)≠Sum.inr b
lemma c33 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (hP:Function.Involutive P) (b : β) (hb:c31 P b) :
    ∃ c : β,P (Sum.inr b)=Sum.inr c∧c31 P c:=by
  cases h:P (Sum.inr b) with
  | inl a =>
    exfalso
    apply hb a
    rw [← h]
    exact hP _
  | inr c =>
    refine ⟨c,rfl,?_⟩
    intro a ha
    have heq:=P.injective (ha.trans h.symm)
    cases heq
noncomputable def residualPad {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (hP:Function.Involutive P) (b:{b : β // c31 P b}) :
    {b : β // c31 P b} :=
  ⟨Classical.choose (c33 P hP b.val b.property),
    (Classical.choose_spec (c33 P hP b.val b.property)).2⟩
lemma c27 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (hP:Function.Involutive P) (b:{b : β // c31 P b}) :
    P (Sum.inr b.val)=Sum.inr (residualPad P hP b).val :=
  (Classical.choose_spec (c33 P hP b.val b.property)).1
lemma c19 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (hP:Function.Involutive P):Function.Involutive (residualPad P hP):=by
  intro b
  apply Subtype.ext
  apply Sum.inr_injective
  rw [← c27,← c27]
  exact hP _
lemma c18 {α β : Type*} (P:Equiv.Perm (α ⊕ β))
    (b : β):c31 P b↔b ∉ Set.range (crossingPartner P):=by
  constructor
  · intro hb ⟨a,ha⟩
    exact hb a.val (by rw [c3,ha])
  · intro hb a ha
    apply hb
    refine ⟨⟨a,b,ha⟩,?_⟩
    apply Sum.inr_injective
    exact (c3 P ⟨a,b,ha⟩).symm.trans ha
lemma unusedPad_card {α β : Type*} [Finite α] [Finite β]
    (P:Equiv.Perm (α ⊕ β)) :
    Nat.card {b : β // c31 P b}=Nat.card β -
      Nat.card {a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b}:=by
  classical
  let:=Fintype.ofFinite β
  have hc:=Nat.card_congr (Equiv.subtypeEquivRight
    (c18 P))
  rw [hc,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_range_of_injective (c10 P)]
noncomputable def gluePairing {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (U:Finset α) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) : α ⊕ β → α ⊕ β := by
  classical
  exact fun x=>match x with
    | Sum.inl a=>if h:a ∈ U then Sum.inr (e ⟨a,h⟩) else Sum.inl (Q a)
    | Sum.inr b=>if h:b ∈ Set.range e then
        Sum.inl (Classical.choose h).val else Sum.inr (R ⟨b,h⟩).val
lemma c4 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (U:Finset α) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) (a:U) :
    gluePairing Q U e R (Sum.inl a.val)=Sum.inr (e a):=by
  simp [gluePairing,a.property]
lemma c11 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (U:Finset α) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) (a:U) :
    gluePairing Q U e R (Sum.inr (e a))=Sum.inl a.val:=by
  classical
  have h:e a ∈ Set.range e:=⟨a,rfl⟩
  simp only [gluePairing,dite_eq_left h]
  exact congrArg (fun x:U=>Sum.inl x.val) (e.injective (Classical.choose_spec h))
lemma c6 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (U:Finset α) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e})
    (b:{b : β // b ∉ Set.range e}) :
    gluePairing Q U e R (Sum.inr b.val)=Sum.inr (R b).val:=by
  simp [gluePairing,b.property]
lemma c22 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q)
    (U:Finset α) (hU:∀ a ∈ U,Q a=a) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) (hR:Function.Involutive R) :
    Function.Involutive (gluePairing Q U e R):=by
  classical
  intro x
  cases x with
  | inl a =>
    by_cases ha:a ∈ U
    · rw [c4 Q U e R ⟨a,ha⟩,
        c11 Q U e R ⟨a,ha⟩]
    · have hQa:Q a ∉ U:=by
        intro h
        have hfix:=hU (Q a) h
        have heq:Q a=a:=hfix.symm.trans (hQ a)
        exact ha (heq ▸ h)
      simp [gluePairing,ha,hQa,hQ a]
  | inr b =>
    by_cases hb:b ∈ Set.range e
    · obtain ⟨a,rfl⟩:=hb
      rw [c11,c4]
    · rw [c6 Q U e R ⟨b,hb⟩,
        c6 Q U e R (R ⟨b,hb⟩)]
      exact congrArg (fun z:{b : β // b ∉ Set.range e}=>Sum.inr z.val) (hR _)
noncomputable def gluedPerm {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q)
    (U:Finset α) (hU:∀ a ∈ U,Q a=a) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) (hR:Function.Involutive R) :
    Equiv.Perm (α ⊕ β) :=
  (c22 Q hQ U hU e R hR).toPerm _
lemma c49 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q)
    (U:Finset α) (hU:∀ a ∈ U,Q a=a) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) (hR:Function.Involutive R) :
    c0 (gluedPerm Q hQ U hU e R hR)=Q:=by
  classical
  funext a
  by_cases ha:a ∈ U
  · simp [c0,gluedPerm,gluePairing,ha,hU a ha]
  · simp [c0,gluedPerm,gluePairing,ha]
lemma c43 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (U:Finset α) (e:U ↪ β)
    (R:Equiv.Perm {b : β // b ∉ Set.range e}) (a : α) :
    (∃ b : β,gluePairing Q U e R (Sum.inl a)=Sum.inr b)↔a ∈ U:=by
  classical
  by_cases ha:a ∈ U <;> simp [gluePairing,ha]
noncomputable def crossingSet {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)):Finset α := by
  classical
  exact univ.filter (fun a=>∃ b : β,P (Sum.inl a)=Sum.inr b)
lemma c12 {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) (a : α) :
    a ∈ crossingSet P↔∃ b : β,P (Sum.inl a)=Sum.inr b:=by
  classical
  simp [crossingSet]
noncomputable def crossingEmbedding {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)):crossingSet P ↪ β :=
  { toFun:=fun a=>crossingPartner P ⟨a.val,(c12 P a.val).mp a.property⟩
    inj':=by
      intro a b h
      have:=c10 P h
      exact Subtype.ext (congrArg
        (fun z:{a : α // ∃ b : β,P (Sum.inl a)=Sum.inr b}=>z.val) this) }
lemma c8 {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) (a:crossingSet P) :
    P (Sum.inl a.val)=Sum.inr (crossingEmbedding P a) :=
  c3 P ⟨a.val,(c12 P a.val).mp a.property⟩
lemma c13 {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) (b : β) :
    c31 P b↔b ∉ Set.range (crossingEmbedding P):=by
  constructor
  · intro hb ⟨a,ha⟩
    exact hb a.val (by rw [c8,ha])
  · intro hb a ha
    apply hb
    have ham:a ∈ crossingSet P:=(c12 P a).mpr ⟨b,ha⟩
    refine ⟨⟨a,ham⟩,?_⟩
    apply Sum.inr_injective
    exact (c8 P ⟨a,ham⟩).symm.trans ha
lemma c28 {α β : Type*} (e : α ≃ β) (P:Equiv.Perm α)
    (hP:Function.Involutive P):Function.Involutive (e.permCongr P):=by
  intro x
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rw [hP (e.symm x),Equiv.apply_symm_apply]
noncomputable def residualPermutation {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) (hP:Function.Involutive P) :
    Equiv.Perm {b : β // b ∉ Set.range (crossingEmbedding P)} :=
  (Equiv.subtypeEquivRight (c13 P)).permCongr
    ((c19 P hP).toPerm _)
lemma c23 {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) (hP:Function.Involutive P) :
    Function.Involutive (residualPermutation P hP) :=
  c28 _ _ (c19 P hP)
lemma c39 {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) (hP:Function.Involutive P)
    (b:{b : β // b ∉ Set.range (crossingEmbedding P)}) :
    P (Sum.inr b.val)=Sum.inr (residualPermutation P hP b).val:=by
  exact c27 P hP
    ⟨b.val,(c13 P b.val).mpr b.property⟩
lemma c52 {α β : Type*} [Fintype α]
    (P:Equiv.Perm (α ⊕ β)) :
    ∀ a ∈ crossingSet P,c0 P a=a:=by
  intro a ha
  exact c37 P ⟨a,(c12 P a).mp ha⟩
lemma c46 {α β : Type*} [Fintype α] [DecidableEq α]
    (P:Equiv.Perm (α ⊕ β)) (hP:Function.Involutive P) :
    gluePairing ((c7 P hP).toPerm _)
      (crossingSet P) (crossingEmbedding P) (residualPermutation P hP)=P:=by
  classical
  funext x
  cases x with
  | inl a =>
    by_cases ha:a ∈ crossingSet P
    · rw [c4 _ _ _ _ ⟨a,ha⟩]
      exact (c8 P ⟨a,ha⟩).symm
    · have hn:¬ ∃ b : β,P (Sum.inl a)=Sum.inr b:=by
        simpa only [c12] using ha
      cases h:P (Sum.inl a) with
      | inl c=>simp [gluePairing,ha,c0,h]
      | inr c=>exact (hn ⟨c,h⟩).elim
  | inr b =>
    by_cases hb:b ∈ Set.range (crossingEmbedding P)
    · obtain ⟨a,rfl⟩:=hb
      rw [c11]
      rw [← c8,hP]
    · rw [c6 _ _ _ _ ⟨b,hb⟩]
      exact (c39 P hP ⟨b,hb⟩).symm
def c32 {α : Type*} (Q:Equiv.Perm α) (β : Type*) :=
  Σ U:{U:Finset α // ∀ a ∈ U,Q a=a},
    Σ e:U.val ↪ β,{R:Equiv.Perm {b : β // b ∉ Set.range e} // Function.Involutive R}
noncomputable def glueData {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q) (D:c32 Q β) :
    {P:Equiv.Perm (α ⊕ β) // Function.Involutive P∧c0 P=Q} :=
  ⟨gluedPerm Q hQ D.1.val D.1.property D.2.1 D.2.2.val D.2.2.property,
    c22 Q hQ D.1.val D.1.property D.2.1 D.2.2.val D.2.2.property,
    c49 Q hQ D.1.val D.1.property D.2.1 D.2.2.val D.2.2.property⟩
lemma c58 {α β : Type*} [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q) :
    Function.Injective (glueData (β := β) Q hQ):=by
  classical
  rintro ⟨⟨U,hU⟩,e,R,hR⟩ ⟨⟨V,hV⟩,f,S,hS⟩ heq
  have hg:gluePairing Q U e R=gluePairing Q V f S :=
    congrArg (fun p=>(p.val : α ⊕ β → α ⊕ β)) heq
  have huv:U=V:=by
    ext a
    rw [← c43 Q U e R,← c43 Q V f S,hg]
  subst V
  have hef:e=f:=by
    ext a
    apply Sum.inr_injective
    rw [← c4 Q U e R a,hg,
      c4 Q U f S a]
  subst f
  have hrs:R=S:=by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    apply Sum.inr_injective
    rw [← c6 Q U e R b,hg,
      c6 Q U e S b]
  subst S
  rfl
lemma c56 {α β : Type*} [Fintype α] [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q) :
    Function.Surjective (glueData (β := β) Q hQ):=by
  classical
  rintro ⟨P,hP,hres⟩
  have hU:∀ a ∈ crossingSet P,Q a=a:=by
    intro a ha
    rw [← congrFun hres a]
    exact c52 P a ha
  let D:c32 Q β := ⟨⟨crossingSet P,hU⟩,crossingEmbedding P,
    residualPermutation P hP,c23 P hP⟩
  refine ⟨D,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change gluePairing Q (crossingSet P) (crossingEmbedding P)
    (residualPermutation P hP) x=P x
  have hperm:(c7 P hP).toPerm _=Q:=by
    apply Equiv.ext
    exact fun a=>congrFun hres a
  rw [← hperm,c46]
lemma c14 {α β : Type*} (e : α ≃ β) (P:Equiv.Perm α) :
    Function.Involutive P↔Function.Involutive (e.permCongr P):=by
  constructor
  · exact c28 e P
  · intro h a
    apply e.injective
    have hx:=h (e a)
    simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using hx
lemma c51 {α β : Type*} (e : α ≃ β) :
    Nat.card {P:Equiv.Perm α // Function.Involutive P} =
    Nat.card {P:Equiv.Perm β // Function.Involutive P} :=
  Nat.card_congr (Equiv.subtypeEquiv e.permCongr (c14 e))
lemma c54 {α : Type*} [Finite α] :
    Nat.card {P:Equiv.Perm α // Function.Involutive P} =
    Nat.card {P:Equiv.Perm (Fin (Nat.card α)) // Function.Involutive P}:=by
  let:=Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card (α := α)]
  exact c51 (Fintype.equivFin α)
lemma c48 {α β : Type*} [Finite α] [Finite β] (e : α ↪ β) :
    Nat.card {b : β // b ∉ Set.range e}=Nat.card β - Nat.card α := by
  classical
  let:=Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_range_of_injective e.injective]
open scoped Classical in
lemma c59 {α β : Type*} [Fintype α] [Fintype β]
    (Q:Equiv.Perm α) :
    Nat.card (c32 Q β) =
      ∑ U:{U:Finset α // ∀ a ∈ U,Q a=a},
        (Nat.card β).descFactorial U.val.card *
        Nat.card {P:Equiv.Perm (Fin (Nat.card β-U.val.card)) // Function.Involutive P}:=by
  classical
  unfold c32
  rw [Nat.card_sigma]
  apply sum_congr rfl
  intro U hU
  rw [Nat.card_sigma]
  have hc:∀ e:U.val ↪ β,
      Nat.card {R:Equiv.Perm {b : β // b ∉ Set.range e} // Function.Involutive R} =
      Nat.card {P:Equiv.Perm (Fin (Nat.card β-U.val.card)) // Function.Involutive P}:=by
    intro e
    have hsize:Nat.card {b : β // b ∉ Set.range e}=Nat.card β-U.val.card:=by
      rw [c48,Nat.card_eq_finsetCard]
    rw [c54,hsize]
  simp_rw [hc]
  rw [sum_const,nsmul_eq_mul]
  congr 1
  simp only [card_univ,Nat.cast_id]
  rw [Fintype.card_embedding_eq]
  simp [Nat.card_eq_fintype_card]
lemma c63 (I:ℕ → ℕ) (f t:ℕ) :
    ∑ h ∈ range (f+1),f.choose h * t.descFactorial h * I (t-h) =
    ∑ h ∈ range (t+1),f.choose h * t.descFactorial h * I (t-h):=by
  rcases le_total f t with hft | htf
  · apply sum_subset (range_mono (by omega:f+1 ≤ t+1))
    intro h hh hnot
    have hfh:f < h:=by simp only [mem_range] at hnot;omega
    simp [Nat.choose_eq_zero_of_lt hfh]
  · symm
    apply sum_subset (range_mono (by omega:t+1 ≤ f+1))
    intro h hh hnot
    have hth:t < h:=by simp only [mem_range] at hnot;omega
    simp [Nat.descFactorial_of_lt hth]
open scoped Classical in
lemma c60 {α : Type*} [Fintype α] (Q:Equiv.Perm α)
    (g:ℕ → ℕ) :
    (∑ U:{U:Finset α // ∀ a ∈ U,Q a=a},g U.val.card) =
    ∑ h ∈ range ((univ.filter (fun a=>Q a=a)).card+1),
      (univ.filter (fun a=>Q a=a)).card.choose h * g h:=by
  classical
  let F:=univ.filter (fun a=>Q a=a)
  have hm:∀ U:Finset α,U ∈ F.powerset↔∀ a ∈ U,Q a=a:=by
    intro U
    simp only [mem_powerset,F,subset_iff,mem_filter,mem_univ,true_and]
  rw [← sum_subtype F.powerset hm (fun U=>g U.card),sum_powerset_apply_card]
  simp [F]
lemma c42 {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (Q:Equiv.Perm α) (hQ:Function.Involutive Q) :
    Nat.card {P:Equiv.Perm (α ⊕ β) // Function.Involutive P∧c0 P=Q} =
    ∑ h ∈ range (Nat.card β+1),
      (univ.filter (fun a=>Q a=a)).card.choose h * (Nat.card β).descFactorial h *
      Nat.card {P:Equiv.Perm (Fin (Nat.card β-h)) // Function.Involutive P}:=by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective (glueData (β := β) Q hQ)
    ⟨c58 Q hQ,c56 Q hQ⟩),c59,
    c60 Q (fun h=>(Nat.card β).descFactorial h *
      Nat.card {P:Equiv.Perm (Fin (Nat.card β-h)) // Function.Involutive P})]
  simp_rw [← Nat.mul_assoc]
  convert! c63 (fun k=>Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P})
      (univ.filter (fun a=>Q a=a)).card (Nat.card β) using 1
  congr! 10
lemma c40 (n t:ℕ)
    (Q:{P:Equiv.Perm (Fin n) // Function.Involutive P}) :
    Nat.card {P:{P:Equiv.Perm (Fin (n+t)) // Function.Involutive P} //
      c21 n t P=Q} =
    ∑ h ∈ range (t+1),
      (univ.filter (fun a=>Q.val a=a)).card.choose h * t.descFactorial h *
      Nat.card {P:Equiv.Perm (Fin (t-h)) // Function.Involutive P}:=by
  classical
  let e:Fin (n+t) ≃ Fin n ⊕ Fin t:=finSumFinEquiv.symm
  let E:{P:Equiv.Perm (Fin (n+t)) // Function.Involutive P} ≃
      {P:Equiv.Perm (Fin n ⊕ Fin t) // Function.Involutive P} :=
    Equiv.subtypeEquiv e.permCongr (c14 e)
  have hp:∀ P:{P:Equiv.Perm (Fin (n+t)) // Function.Involutive P},
      c21 n t P=Q↔c0 (E P).val=Q.val:=by
    intro P
    constructor
    · intro h
      exact congrArg (fun z=>(z.val:Fin n → Fin n)) h
    · intro h
      apply Subtype.ext
      apply Equiv.ext
      exact fun a=>congrFun h a
  have hcard:=Nat.card_congr ((Equiv.subtypeEquiv E hp).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun P:Equiv.Perm (Fin n ⊕ Fin t)=>Function.Involutive P)
      (fun P=>c0 P=Q.val)))
  rw [hcard,c42 Q.val Q.property]
  simp only [Nat.card_eq_fintype_card (α := Fin t),Fintype.card_fin]
  apply sum_congr rfl
  intro h hh
  congr 1
  rw [Nat.card_fin]
open scoped Classical in
lemma c26 {α : Type*} [Fintype α] (Q : α → Prop)
    (f : α → ℕ) (d e:ℕ) (w:ℕ → ℕ)
    (hf:∀ a,Q a → ∃ j:Fin (d+1),f a=e+2*j.val) :
    (∑ a:{a // Q a},w (f a.val)) =
      ∑ j:Fin (d+1),w (e+2*j.val) * Nat.card {a // Q a∧f a=e+2*j.val}:=by
  classical
  let forget:(Σ j:Fin (d+1),{a // Q a∧f a=e+2*j.val}) → {a // Q a} :=
    fun p=>⟨p.2.val,p.2.property.1⟩
  have hi:Function.Injective forget:=by
    rintro ⟨i,a,ha,hfa⟩ ⟨j,b,hb,hfb⟩ heq
    have hab:a=b:=congrArg Subtype.val heq
    subst b
    have hij:i=j:=Fin.ext (by omega)
    subst j
    rfl
  have hs:Function.Surjective forget:=by
    intro a
    obtain ⟨j,hj⟩:=hf a.val a.property
    exact ⟨⟨j,a.val,a.property,hj⟩,rfl⟩
  rw [← (Equiv.ofBijective forget ⟨hi,hs⟩).sum_comp
    (fun a=>w (f a.val)),Fintype.sum_sigma]
  apply sum_congr rfl
  intro j hj
  have hw:∀ a:{a // Q a∧f a=e+2*j.val},w (f a.val)=w (e+2*j.val) :=
    fun a=>congrArg w a.property.2
  change (∑ a:{a // Q a∧f a=e+2*j.val},w (f a.val))=_
  simp only [hw,sum_const,nsmul_eq_mul,card_univ,Nat.cast_id,
    ← Nat.card_eq_fintype_card]
  exact Nat.mul_comm _ _
lemma c50 {α : Type*} (A B:Fintype α) (f : α → ℕ) :
    @Finset.sum α ℕ _ (@univ α A) f = @Finset.sum α ℕ _ (@univ α B) f:=by
  cases Subsingleton.elim A B
  rfl
lemma c57 (n t:ℕ) (H:Finset (Finset (Fin n))) :
    let I:=fun k:ℕ => Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P}
    let kernel:=fun t f:ℕ => (range (t+1)).sum (fun h =>
      f.choose h * t.descFactorial h * I (t-h))
    Nat.card {P:Equiv.Perm (Fin (n+t)) // Function.Involutive P ∧
      ∀ R ∈ H,∃ u ∈ R,∃ v ∈ R,u≠v∧P (u.castAdd t)=v.castAdd t} =
    ∑ j:Fin (n/2+1),kernel t (n%2+2*j.val) *
      Nat.card {P:Equiv.Perm (Fin n) //
        Function.Involutive P ∧
        (∀ R ∈ H,∃ u ∈ R,P u ∈ R∧P u≠u) ∧
        (univ.filter (fun u=>P u=u)).card=n%2+2*j.val}:=by
  classical
  dsimp only
  rw [c15]
  let w:ℕ → ℕ := fun f=>∑ h ∈ range (t+1),f.choose h * t.descFactorial h *
    Nat.card {P:Equiv.Perm (Fin (t-h)) // Function.Involutive P}
  have hs:(∑ Q:{Q:{P:Equiv.Perm (Fin n) // Function.Involutive P} //
      c44 n H Q.val},
      Nat.card {P:{P:Equiv.Perm (Fin (n+t)) // Function.Involutive P} //
        c21 n t P=Q.val}) =
    ∑ Q:{P:Equiv.Perm (Fin n) // Function.Involutive P∧c44 n H P},
      w (univ.filter (fun u=>Q.val u=u)).card:=by
    trans ∑ Q:{Q:{P:Equiv.Perm (Fin n) // Function.Involutive P} //
        c44 n H Q.val},w (univ.filter (fun u=>Q.val.val u=u)).card
    · apply sum_congr rfl
      intro Q hQ
      exact c40 n t Q.val
    · exact Fintype.sum_equiv
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun P:Equiv.Perm (Fin n)=>Function.Involutive P) (c44 n H)) _ _
          (fun _=>rfl)
  rw [hs]
  have hp:=c26
    (fun P:Equiv.Perm (Fin n)=>Function.Involutive P∧c44 n H P)
    (fun P=>(univ.filter (fun u=>P u=u)).card) (n/2) (n%2) w
    (fun P hP=>c9 n P hP.1)
  simp only [w,c44,and_assoc] at hp
  refine Eq.trans ?_ hp
  exact c50 _ _ _
noncomputable def invCount (k:ℕ):=Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P}
noncomputable def extKernel (t f:ℕ):=∑ h ∈ range (t+1),f.choose h * t.descFactorial h * invCount (t-h)
noncomputable def fixedCount (m f:ℕ):=Nat.card {P:Equiv.Perm (Fin m) //
  Function.Involutive P∧(univ.filter (fun u=>P u=u)).card=f}
lemma c45 (m t:ℕ) :
    invCount (m+t)=∑ j:Fin (m/2+1),
      extKernel t (m%2+2*j.val) * fixedCount m (m%2+2*j.val):=by
  have h:=c57 m t ∅
  simpa only [invCount,extKernel,fixedCount,Finset.forall_mem_empty_iff,
    and_true,true_and] using h
lemma fixedCount_diagonal (m:ℕ):fixedCount m m=1 :=
  c35 m
lemma fixedCount_zero (m f:ℕ) (h:m < f):fixedCount m f=0:=by
  have he:IsEmpty {P:Equiv.Perm (Fin m) // Function.Involutive P ∧
      (univ.filter (fun u=>P u=u)).card=f}:=by
    refine ⟨fun P => ?_⟩
    have hc:=card_le_card (filter_subset (fun u=>P.val u=u) univ)
    simp only [card_univ,Fintype.card_fin] at hc
    have hp:=P.property.2
    omega
  exact Nat.card_eq_zero.mpr (Or.inl he)
lemma c25 (e j t:ℕ) (he:e < 2) :
    invCount (t+(e+2*j))=∑ k:Fin (j+1),
      extKernel t (e+2*k.val) * fixedCount (e+2*j) (e+2*k.val):=by
  have h:=c45 (e+2*j) t
  have hm:(e+2*j)%2=e:=by omega
  have hd:(e+2*j)/2=j:=by omega
  rw [hm,hd,Nat.add_comm (e+2*j) t] at h
  exact h
lemma invCount_interpolation_padded (d e t:ℕ) (he:e < 2) (j:Fin (d+1)) :
    invCount (t+(e+2*j.val))=∑ k:Fin (d+1),
      extKernel t (e+2*k.val) * fixedCount (e+2*j.val) (e+2*k.val):=by
  rw [c25 e j.val t he]
  rw [Fin.sum_univ_eq_sum_range
      (fun k=>extKernel t (e+2*k) * fixedCount (e+2*j.val) (e+2*k)) (j.val+1),
    Fin.sum_univ_eq_sum_range
      (fun k=>extKernel t (e+2*k) * fixedCount (e+2*j.val) (e+2*k)) (d+1)]
  apply sum_subset (range_mono (by omega:j.val+1 ≤ d+1))
  intro k hk hnot
  have hjk:j.val < k:=by simp only [mem_range] at hnot;omega
  rw [fixedCount_zero (e+2*j.val) (e+2*k) (by omega),mul_zero]
lemma exact_involution_matrix_det (d e:ℕ) (he:e < 2) :
    (Matrix.of fun t j:Fin (d+1)=>(invCount (t.val+(e+2*j.val)):ℤ)).det =
      (2:ℤ)^(d*(d+1)/2) * ∏ j:Fin (d+1),(j.val.factorial:ℤ):=by
  classical
  let K:Matrix (Fin (d+1)) (Fin (d+1)) ℤ :=
    Matrix.of fun t j=>(extKernel t.val (e+2*j.val):ℤ)
  let B:Matrix (Fin (d+1)) (Fin (d+1)) ℤ :=
    Matrix.of fun k j=>(fixedCount (e+2*j.val) (e+2*k.val):ℤ)
  have hfactor:(Matrix.of fun t j:Fin (d+1) =>
      (invCount (t.val+(e+2*j.val)):ℤ))=K * B:=by
    ext t j
    simp only [K,B,Matrix.of_apply,Matrix.mul_apply]
    exact_mod_cast invCount_interpolation_padded d e t.val he j
  have hB:B.IsUpperTriangular:=by
    intro i j hij
    have hj:j.val < i.val:=hij
    change (fixedCount (e+2*j.val) (e+2*i.val):ℤ)=0
    rw [fixedCount_zero _ _ (by omega),Nat.cast_zero]
  have hdetB:B.det=1:=by
    rw [Matrix.det_of_isUpperTriangular hB]
    simp only [B,Matrix.of_apply,fixedCount_diagonal,Nat.cast_one,prod_const_one]
  have hdetK:K.det=(2:ℤ)^(d*(d+1)/2) *
      ∏ j:Fin (d+1),(j.val.factorial:ℤ):=by
    have h:=(c62 invCount c34 d (fun j=>e+2*j.val)).trans
      (c38 d e)
    rw [← h]
    congr 1
    ext t j
    simp only [K,extKernel,Matrix.of_apply,Nat.cast_sum,Nat.cast_mul]
  rw [hfactor,Matrix.det_mul,hdetB,mul_one,hdetK]
end L4
end
noncomputable section
open Classical
open PEqualNP.Library Lib.Machines Lib.Universal Lib.Machines.Rev
def q11 (k:ℕ):ℕ := Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P}
lemma q45:q11 0=1:=by
  unfold q11
  let e:{P:Equiv.Perm (Fin 0) // Function.Involutive P} ≃ Unit :=
    { toFun:=fun _=>()
      invFun:=fun _=>⟨1,fun x=>Fin.elim0 x⟩
      left_inv:=fun ⟨P,_⟩=>Subtype.ext (Equiv.ext fun x=>Fin.elim0 x)
      right_inv:=fun _=>rfl }
  rw [Nat.card_congr e];simp
lemma q153:q11 1=1:=by
  unfold q11
  let e:{P:Equiv.Perm (Fin 1) // Function.Involutive P} ≃ Unit :=
    { toFun:=fun _=>()
      invFun:=fun _=>⟨1,fun _=>rfl⟩
      left_inv:=fun ⟨P,_⟩=>Subtype.ext (Equiv.ext fun x=>Subsingleton.elim _ _)
      right_inv:=fun _=>rfl }
  rw [Nat.card_congr e];simp
lemma q162 {α β : Type*} (e : α ≃ β) :
    Nat.card {P:Equiv.Perm α // Function.Involutive P} =
      Nat.card {Q:Equiv.Perm β // Function.Involutive Q}:=by
  let φ : {P:Equiv.Perm α // Function.Involutive P} ≃
      {Q:Equiv.Perm β // Function.Involutive Q} :=
    { toFun:=fun P=>⟨(e.symm.trans P.1).trans e,fun b=>by
        simp only [Equiv.trans_apply,Equiv.symm_apply_apply,P.2 _,Equiv.apply_symm_apply]⟩
      invFun:=fun Q=>⟨(e.trans Q.1).trans e.symm,fun a=>by
        simp only [Equiv.trans_apply,Equiv.apply_symm_apply,Q.2 _,Equiv.symm_apply_apply]⟩
      left_inv:=fun P=>Subtype.ext (Equiv.ext fun a=>by simp)
      right_inv:=fun Q=>Subtype.ext (Equiv.ext fun b=>by simp) }
  exact Nat.card_congr φ
lemma q117 (m:ℕ):q11 (m+2)=q11 (m+1)+(m+1) * q11 m:=by
  unfold q11
  let last:Fin (m+2):=Fin.last (m+1)
  let S0:={P:Equiv.Perm (Fin (m+2)) // Function.Involutive P∧P last=last}
  let S1 (a:Fin (m+1)):={P:Equiv.Perm (Fin (m+2)) // Function.Involutive P∧P last=a.castSucc}
  let part:{P:Equiv.Perm (Fin (m+2)) // Function.Involutive P} ≃ S0 ⊕ Σ a:Fin (m+1),S1 a :=
    { toFun:=fun P =>
        if h:P.1 last=last then Sum.inl ⟨P.1,P.2,h⟩
        else
          have hlt:(P.1 last).val < m+1:=by
            have h1:=(P.1 last).isLt
            have hne:(P.1 last).val≠m+1:=fun he=>h (Fin.ext he)
            omega
          Sum.inr ⟨⟨(P.1 last).val,hlt⟩,⟨P.1,P.2,Fin.ext rfl⟩⟩
      invFun:=fun s =>
        match s with
        | Sum.inl P=>⟨P.1,P.2.1⟩
        | Sum.inr ⟨_,P⟩=>⟨P.1,P.2.1⟩
      left_inv:=fun P=>by
        by_cases h:P.1 last=last <;> simp [h]
      right_inv:=fun s=>by
        cases s with
        | inl P=>simp [P.2.2]
        | inr aP =>
          rcases aP with ⟨a,⟨P,hPi,hPl⟩⟩
          have hne:P last≠last:=by
            rw [hPl]
            intro he
            have:=congrArg Fin.val he
            simp only [Fin.val_castSucc,last,Fin.val_last] at this
            have:=a.isLt
            omega
          simp only [hne,↓reduceDIte]
          congr 1
          refine Sigma.ext (Fin.ext (by simp [hPl])) ?_
          exact (Subtype.heq_iff_coe_eq (fun Q=>by simp [S1,hPl])).2 rfl }
  rw [Nat.card_congr part,Nat.card_sum,Nat.card_sigma]
  have hS0:Nat.card S0=Nat.card {Q:Equiv.Perm (Fin (m+1)) // Function.Involutive Q}:=by
    let e0:S0 ≃ {Q:Equiv.Perm (Fin (m+1)) // Function.Involutive Q} :=
      { toFun:=fun P =>
          ⟨{ toFun:=fun x=>⟨(P.1 x.castSucc).val,by
                have hlt:=(P.1 x.castSucc).isLt
                have hne:P.1 x.castSucc≠last:=by
                  intro he
                  have h1:=P.1.injective (he.trans P.2.2.symm)
                  have h2:=congrArg Fin.val h1
                  simp only [Fin.val_castSucc,last,Fin.val_last] at h2
                  have:=x.isLt;omega
                have hnev:(P.1 x.castSucc).val≠m+1:=fun h=>hne (Fin.ext h)
                omega⟩
             invFun:=fun x=>⟨(P.1 x.castSucc).val,by
                have hlt:=(P.1 x.castSucc).isLt
                have hne:P.1 x.castSucc≠last:=by
                  intro he
                  have h1:=P.1.injective (he.trans P.2.2.symm)
                  have h2:=congrArg Fin.val h1
                  simp only [Fin.val_castSucc,last,Fin.val_last] at h2
                  have:=x.isLt;omega
                have hnev:(P.1 x.castSucc).val≠m+1:=fun h=>hne (Fin.ext h)
                omega⟩
             left_inv:=fun x=>Fin.ext (by simpa using congrArg Fin.val (P.2.1 x.castSucc))
             right_inv:=fun x=>Fin.ext (by simpa using congrArg Fin.val (P.2.1 x.castSucc)) },
           fun x=>Fin.ext (by simpa using congrArg Fin.val (P.2.1 x.castSucc))⟩
        invFun:=fun Q =>
          ⟨{ toFun:=fun x=>if hx:x.val < m+1 then (Q.1 ⟨x.val,hx⟩).castSucc else last
             invFun:=fun x=>if hx:x.val < m+1 then (Q.1 ⟨x.val,hx⟩).castSucc else last
             left_inv:=fun x=>by
               by_cases hx:x.val < m+1
               · simp only [hx,↓reduceDIte,Fin.val_castSucc,Fin.is_lt]
                 rw [Fin.eta,Q.2];exact Fin.ext rfl
               · have hxl:x=last:=Fin.ext (by simp only [last,Fin.val_last];have:=x.isLt;omega)
                 subst hxl;simp [last]
             right_inv:=fun x=>by
               by_cases hx:x.val < m+1
               · simp only [hx,↓reduceDIte,Fin.val_castSucc,Fin.is_lt]
                 rw [Fin.eta,Q.2];exact Fin.ext rfl
               · have hxl:x=last:=Fin.ext (by simp only [last,Fin.val_last];have:=x.isLt;omega)
                 subst hxl;simp [last] },
           ⟨fun x=>by
              by_cases hx:x.val < m+1
              · simp only [Equiv.coe_fn_mk,hx,↓reduceDIte,Fin.val_castSucc,Fin.is_lt]
                rw [Fin.eta,Q.2];exact Fin.ext rfl
              · have hxl:x=last:=Fin.ext (by simp only [last,Fin.val_last];have:=x.isLt;omega)
                subst hxl;simp [last],
            by simp [last]⟩⟩
        left_inv:=fun P=>Subtype.ext (Equiv.ext fun x=>by
          by_cases hx:x.val < m+1
          · simp only [Equiv.coe_fn_mk,hx,↓reduceDIte]
            apply Fin.ext;simp only [Fin.val_castSucc];congr 1
          · have hxl:x=last:=Fin.ext (by simp only [last,Fin.val_last];have:=x.isLt;omega)
            subst hxl;simp [last,P.2.2])
        right_inv:=fun Q=>Subtype.ext (Equiv.ext fun x=>by
          have hle:x.val ≤ m:=Nat.lt_succ_iff.1 x.isLt
          apply Fin.ext
          simp [hle]) }
    exact Nat.card_congr e0
  have hS1:∀ a:Fin (m+1),Nat.card (S1 a)=Nat.card {Q:Equiv.Perm (Fin m) // Function.Involutive Q}:=by
    intro a
    let T:={x:Fin (m+2) // x≠last∧x≠a.castSucc}
    have hTcard:Fintype.card T=m:=by
      have hne:last≠a.castSucc:=by
        intro h;have:=congrArg Fin.val h;simp [last] at this;have:=a.isLt;omega
      have hset:(Finset.univ.filter fun x:Fin (m+2)=>x≠last∧x≠a.castSucc) =
          (Finset.univ.erase last).erase a.castSucc:=by
        ext x;simp [and_comm]
      rw [Fintype.card_subtype,hset,Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne.symm,Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin]
      omega
    let eT:T ≃ Fin m:=Fintype.equivFinOfCardEq hTcard
    let e1:S1 a ≃ {Q:Equiv.Perm T // Function.Involutive Q} :=
      { toFun:=fun P =>
          have hPa:P.1 a.castSucc=last :=
            (congrArg P.1 P.2.2.symm).trans (P.2.1 last)
          have hmap:∀ x:T,P.1 x.1≠last∧P.1 x.1≠a.castSucc:=fun x =>
            ⟨fun h=>x.2.2 (P.1.injective (h.trans hPa.symm)),
             fun h=>x.2.1 (P.1.injective (h.trans P.2.2.symm))⟩
          ⟨{ toFun:=fun x=>⟨P.1 x.1,hmap x⟩
             invFun:=fun x=>⟨P.1 x.1,hmap x⟩
             left_inv:=fun x=>Subtype.ext (P.2.1 x.1)
             right_inv:=fun x=>Subtype.ext (P.2.1 x.1) },
           fun x=>Subtype.ext (P.2.1 x.1)⟩
        invFun:=fun Q =>
          have hne:last≠a.castSucc:=by
            intro h;have:=congrArg Fin.val h;simp [last] at this;have:=a.isLt;omega
          let f:Fin (m+2) → Fin (m+2):=fun x =>
            if h1:x=last then a.castSucc
            else if h2:x=a.castSucc then last
            else (Q.1 ⟨x,h1,h2⟩).1
          have hinv:Function.Involutive f:=by
            intro x
            dsimp only [f]
            by_cases h1:x=last
            · subst h1;simp [hne.symm]
            · by_cases h2:x=a.castSucc
              · subst h2;simp
              · simp only [h1,h2,↓reduceDIte]
                have hq:=(Q.1 ⟨x,h1,h2⟩).2
                simp only [hq.1,hq.2,↓reduceDIte]
                exact congrArg Subtype.val (Q.2 ⟨x,h1,h2⟩)
          ⟨⟨f,f,hinv,hinv⟩,⟨hinv,by simp [f]⟩⟩
        left_inv:=fun P=>Subtype.ext (Equiv.ext fun x=>by
          have hPa:P.1 a.castSucc=last :=
            (congrArg P.1 P.2.2.symm).trans (P.2.1 last)
          by_cases h1:x=last
          · subst h1;simp [P.2.2]
          · by_cases h2:x=a.castSucc
            · subst h2;simp [h1,hPa]
            · simp [h1,h2])
        right_inv:=fun Q=>Subtype.ext (Equiv.ext fun x=>Subtype.ext (by
          simp [x.2.1,x.2.2])) }
    rw [Nat.card_congr e1,q162 eT]
  rw [hS0]
  simp_rw [hS1,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
def q9:ℕ → ℕ
  | 0=>1
  | k+1=>(2 * k+1) * q9 k
lemma q20 (k:ℕ) :
    2 ^ k * k.factorial * q9 k=(2 * k).factorial:=by
  induction k with
  | zero=>simp [q9]
  | succ k ih =>
    have h1:2 * (k+1)=(2 * k+1)+1:=by omega
    rw [h1,Nat.factorial_succ,Nat.factorial_succ,q9,pow_succ,Nat.factorial_succ]
    calc 2 ^ k * 2 * ((k+1) * k.factorial) * ((2 * k+1) * q9 k)
        = (2 * k+1+1) * ((2 * k+1) * (2 ^ k * k.factorial * q9 k)):=by ring
      _=(2 * k+1+1) * ((2 * k+1) * (2 * k).factorial):=by rw [ih]
lemma q56 (k:ℕ) :
    L4.fixedCount (2 * k) 0=q9 k:=by
  induction k with
  | zero =>
    unfold L4.fixedCount q9
    let e:{P:Equiv.Perm (Fin 0) // Function.Involutive P ∧
        (Finset.univ.filter fun u=>P u=u).card=0} ≃ Unit :=
      { toFun:=fun _=>()
        invFun:=fun _=>⟨1,fun x=>Fin.elim0 x,by simp⟩
        left_inv:=fun ⟨P,_⟩=>Subtype.ext (Equiv.ext fun x=>Fin.elim0 x)
        right_inv:=fun _=>rfl }
    rw [Nat.card_congr e];simp
  | succ k ih =>
    unfold L4.fixedCount at ih ⊢
    rw [q9]
    have h2k:2 * (k+1)=2 * k+2:=by omega
    let last:Fin (2 * (k+1)):=⟨2 * k+1,by omega⟩
    let S (a:Fin (2 * k+1)):={P:Equiv.Perm (Fin (2 * (k+1))) //
      Function.Involutive P∧(Finset.univ.filter fun u=>P u=u).card=0 ∧
      P last=⟨a.val,by have:=a.isLt;omega⟩}
    let part:{P:Equiv.Perm (Fin (2 * (k+1))) //
        Function.Involutive P∧(Finset.univ.filter fun u=>P u=u).card=0} ≃
        Σ a:Fin (2 * k+1),S a :=
      { toFun:=fun P =>
          have hne:P.1 last≠last:=by
            intro h
            have hpos:0 < (Finset.univ.filter fun u=>P.1 u=u).card :=
              Finset.card_pos.2 ⟨last,Finset.mem_filter.2 ⟨Finset.mem_univ _,h⟩⟩
            omega
          have hlt:(P.1 last).val < 2 * k+1:=by
            have:=(P.1 last).isLt
            have hnev:(P.1 last).val≠2 * k+1:=fun h=>hne (Fin.ext h)
            omega
          ⟨⟨(P.1 last).val,hlt⟩,⟨P.1,P.2.1,P.2.2,Fin.ext rfl⟩⟩
        invFun:=fun aP=>⟨aP.2.1,aP.2.2.1,aP.2.2.2.1⟩
        left_inv:=fun _=>rfl
        right_inv:=fun ⟨a,⟨P,hPi,hPc,hPl⟩⟩=>by
          refine Sigma.ext (Fin.ext (by simp [hPl])) ?_
          exact (Subtype.heq_iff_coe_eq (fun Q=>by simp [S,hPl])).2 rfl }
    rw [Nat.card_congr part,Nat.card_sigma]
    have hSa:∀ a:Fin (2 * k+1),Nat.card (S a)=q9 k:=by
      intro a
      let a':Fin (2 * (k+1)):=⟨a.val,by have:=a.isLt;omega⟩
      have hne:last≠a':=by
        intro h;have:=congrArg Fin.val h;dsimp [last,a'] at this;have:=a.isLt;omega
      let T:={x:Fin (2 * (k+1)) // x≠last∧x≠a'}
      have hTcard:Fintype.card T=2 * k:=by
        have hset:(Finset.univ.filter fun x:Fin (2 * (k+1))=>x≠last∧x≠a') =
            (Finset.univ.erase last).erase a':=by ext x;simp [and_comm]
        rw [Fintype.card_subtype,hset,Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne.symm,Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin]
        omega
      let eT:T ≃ Fin (2 * k):=Fintype.equivFinOfCardEq hTcard
      let e1:S a ≃ {Q:Equiv.Perm T // Function.Involutive Q∧∀ x:T,Q x≠x} :=
        { toFun:=fun P =>
            have hPa:P.1 a'=last :=
              (congrArg P.1 P.2.2.2.symm).trans (P.2.1 last)
            have hmap:∀ x:T,P.1 x.1≠last∧P.1 x.1≠a':=fun x =>
              ⟨fun h=>x.2.2 (P.1.injective (h.trans hPa.symm)),
               fun h=>x.2.1 (P.1.injective (h.trans P.2.2.2.symm))⟩
            have hnofix:∀ u,P.1 u≠u:=fun u hu=>by
              have hpos:0 < (Finset.univ.filter fun v=>P.1 v=v).card :=
                Finset.card_pos.2 ⟨u,Finset.mem_filter.2 ⟨Finset.mem_univ _,hu⟩⟩
              omega
            ⟨{ toFun:=fun x=>⟨P.1 x.1,hmap x⟩
               invFun:=fun x=>⟨P.1 x.1,hmap x⟩
               left_inv:=fun x=>Subtype.ext (P.2.1 x.1)
               right_inv:=fun x=>Subtype.ext (P.2.1 x.1) },
             ⟨fun x=>Subtype.ext (P.2.1 x.1),fun x hx=>hnofix x.1 (congrArg Subtype.val hx)⟩⟩
          invFun:=fun Q =>
            let f:Fin (2 * (k+1)) → Fin (2 * (k+1)):=fun x =>
              if h1:x=last then a' else if h2:x=a' then last else (Q.1 ⟨x,h1,h2⟩).1
            have hinv:Function.Involutive f:=by
              intro x;dsimp only [f]
              by_cases h1:x=last
              · subst h1;simp [hne.symm]
              · by_cases h2:x=a'
                · subst h2;simp
                · simp only [h1,h2,↓reduceDIte]
                  have hq:=(Q.1 ⟨x,h1,h2⟩).2
                  simp only [hq.1,hq.2,↓reduceDIte]
                  exact congrArg Subtype.val (Q.2.1 ⟨x,h1,h2⟩)
            have hnofix:∀ x,f x≠x:=by
              intro x;dsimp only [f]
              by_cases h1:x=last
              · subst h1;simp [hne.symm]
              · by_cases h2:x=a'
                · subst h2;simp [hne,h1]
                · simp only [h1,h2,↓reduceDIte]
                  intro he;exact Q.2.2 ⟨x,h1,h2⟩ (Subtype.ext he)
            ⟨⟨f,f,hinv,hinv⟩,⟨hinv,by
              rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
              intro u _;exact hnofix u,by simp [f,a']⟩⟩
          left_inv:=fun P=>Subtype.ext (Equiv.ext fun x=>by
            have hPa:P.1 a'=last :=
              (congrArg P.1 P.2.2.2.symm).trans (P.2.1 last)
            by_cases h1:x=last
            · subst h1;simp [P.2.2.2,a']
            · by_cases h2:x=a'
              · subst h2;simp [h1,hPa]
              · simp [h1,h2])
          right_inv:=fun Q=>Subtype.ext (Equiv.ext fun x=>Subtype.ext (by simp [x.2.1,x.2.2])) }
      let e2:{Q:Equiv.Perm T // Function.Involutive Q∧∀ x:T,Q x≠x} ≃
          {Q:Equiv.Perm (Fin (2 * k)) // Function.Involutive Q ∧
            (Finset.univ.filter fun u=>Q u=u).card=0} :=
        { toFun:=fun Q=>⟨(eT.symm.trans Q.1).trans eT,
            fun y=>by simp [Q.2.1 _],by
              rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
              intro y _ hy
              have h1:=eT.injective (hy.trans (eT.apply_symm_apply y).symm)
              exact Q.2.2 (eT.symm y) h1⟩
          invFun:=fun Q=>⟨(eT.trans Q.1).trans eT.symm,
            fun x=>by simp [Q.2.1 _],fun x hx=>by
              have h1:=eT.symm.injective (hx.trans (eT.symm_apply_apply x).symm)
              have hpos:0 < (Finset.univ.filter fun u=>Q.1 u=u).card :=
                Finset.card_pos.2 ⟨eT x,Finset.mem_filter.2 ⟨Finset.mem_univ _,h1⟩⟩
              omega⟩
          left_inv:=fun Q=>Subtype.ext (Equiv.ext fun x=>by simp)
          right_inv:=fun Q=>Subtype.ext (Equiv.ext fun y=>by simp) }
      rw [Nat.card_congr e1,Nat.card_congr e2,ih]
    simp_rw [hSa,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
lemma q95 (j k:ℕ) (hkj:k ≤ j) :
    L4.fixedCount (2 * j) (2 * k) =
      (2 * j).choose (2 * k) * q9 (j - k):=by
  unfold L4.fixedCount
  let Fset:={F:Finset (Fin (2 * j)) // F.card=2 * k}
  let Fib (F:Fset):={P:Equiv.Perm (Fin (2 * j)) //
    Function.Involutive P∧Finset.univ.filter (fun u=>P u=u)=F.1}
  let part:{P:Equiv.Perm (Fin (2 * j)) //
      Function.Involutive P∧(Finset.univ.filter fun u=>P u=u).card=2 * k} ≃
      Σ F:Fset,Fib F :=
    { toFun:=fun P=>⟨⟨Finset.univ.filter fun u=>P.1 u=u,P.2.2⟩,⟨P.1,P.2.1,rfl⟩⟩
      invFun:=fun FP=>⟨FP.2.1,FP.2.2.1,by rw [FP.2.2.2,FP.1.2]⟩
      left_inv:=fun _=>rfl
      right_inv:=fun ⟨⟨F,hFc⟩,⟨P,hPi,hPf⟩⟩=>by
        refine Sigma.ext (Subtype.ext hPf) ?_
        exact (Subtype.heq_iff_coe_eq (fun Q=>by simp [Fib,hPf])).2 rfl }
  rw [Nat.card_congr part,Nat.card_sigma]
  have hFib:∀ F:Fset,Nat.card (Fib F)=q9 (j - k):=by
    intro F
    let T:={x:Fin (2 * j) // x ∉ F.1}
    have hTcard:Fintype.card T=2 * (j - k):=by
      have hset:(Finset.univ.filter fun x:Fin (2 * j)=>x ∉ F.1)=Finset.univ \ F.1:=by
        ext x;simp
      rw [Fintype.card_subtype,hset,Finset.card_sdiff,Finset.inter_univ,
        Finset.card_univ,Fintype.card_fin,F.2]
      omega
    let eT:T ≃ Fin (2 * (j - k)):=Fintype.equivFinOfCardEq hTcard
    let e1:Fib F ≃ {Q:Equiv.Perm T // Function.Involutive Q∧∀ x:T,Q x≠x} :=
      { toFun:=fun P =>
          have hfix:∀ u,P.1 u=u↔u ∈ F.1:=fun u=>by
            have h:=Finset.ext_iff.1 P.2.2 u
            simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h
            exact h
          have hmap:∀ x:T,P.1 x.1 ∉ F.1:=fun x hx=>by
            have h1:=(hfix (P.1 x.1)).2 hx
            have h2:=P.2.1 x.1
            rw [h2] at h1
            exact x.2 ((hfix x.1).1 h1.symm)
          ⟨{ toFun:=fun x=>⟨P.1 x.1,hmap x⟩
             invFun:=fun x=>⟨P.1 x.1,hmap x⟩
             left_inv:=fun x=>Subtype.ext (P.2.1 x.1)
             right_inv:=fun x=>Subtype.ext (P.2.1 x.1) },
           ⟨fun x=>Subtype.ext (P.2.1 x.1),fun x hx=>x.2 ((hfix x.1).1 (congrArg Subtype.val hx))⟩⟩
        invFun:=fun Q =>
          let f:Fin (2 * j) → Fin (2 * j):=fun x =>
            if hx:x ∈ F.1 then x else (Q.1 ⟨x,hx⟩).1
          have hinv:Function.Involutive f:=by
            intro x;dsimp only [f]
            by_cases hx:x ∈ F.1
            · simp [hx]
            · simp only [hx,↓reduceDIte,(Q.1 ⟨x,hx⟩).2]
              exact congrArg Subtype.val (Q.2.1 ⟨x,hx⟩)
          have hfilt:Finset.univ.filter (fun u=>f u=u)=F.1:=by
            ext u
            simp only [Finset.mem_filter,Finset.mem_univ,true_and,f]
            by_cases hu:u ∈ F.1
            · simp [hu]
            · simp only [hu,↓reduceDIte,iff_false]
              intro he;exact Q.2.2 ⟨u,hu⟩ (Subtype.ext he)
          ⟨⟨f,f,hinv,hinv⟩,⟨hinv,hfilt⟩⟩
        left_inv:=fun P=>Subtype.ext (Equiv.ext fun x=>by
          have hfix:∀ u,P.1 u=u↔u ∈ F.1:=fun u=>by
            have h:=Finset.ext_iff.1 P.2.2 u
            simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h
            exact h
          by_cases hx:x ∈ F.1
          · simp [hx,(hfix x).2 hx]
          · simp [hx])
        right_inv:=fun Q=>Subtype.ext (Equiv.ext fun x=>Subtype.ext (by simp [x.2])) }
    let e2:{Q:Equiv.Perm T // Function.Involutive Q∧∀ x:T,Q x≠x} ≃
        {Q:Equiv.Perm (Fin (2 * (j - k))) // Function.Involutive Q ∧
          (Finset.univ.filter fun u=>Q u=u).card=0} :=
      { toFun:=fun Q=>⟨(eT.symm.trans Q.1).trans eT,
          fun y=>by simp [Q.2.1 _],by
            rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
            intro y _ hy
            exact Q.2.2 (eT.symm y) (eT.injective (hy.trans (eT.apply_symm_apply y).symm))⟩
        invFun:=fun Q=>⟨(eT.trans Q.1).trans eT.symm,
          fun x=>by simp [Q.2.1 _],fun x hx=>by
            have h1:=eT.symm.injective (hx.trans (eT.symm_apply_apply x).symm)
            have hpos:0 < (Finset.univ.filter fun u=>Q.1 u=u).card :=
              Finset.card_pos.2 ⟨eT x,Finset.mem_filter.2 ⟨Finset.mem_univ _,h1⟩⟩
            omega⟩
        left_inv:=fun Q=>Subtype.ext (Equiv.ext fun x=>by simp)
        right_inv:=fun Q=>Subtype.ext (Equiv.ext fun y=>by simp) }
    rw [Nat.card_congr e1,Nat.card_congr e2]
    exact q56 (j - k)
  simp_rw [hFib,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  congr 1
  have hF:Fintype.card Fset=(Finset.powersetCard (2 * k) (Finset.univ:Finset (Fin (2 * j)))).card:=by
    rw [Fintype.card_subtype]
    congr 1;ext F;simp [Finset.mem_powersetCard]
  rw [hF,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
lemma q57 (m k:ℕ):(m+1).choose (k+1) * (k+1)=(m+1) * m.choose k:=by
  induction m generalizing k with
  | zero =>
    cases k with
    | zero=>simp
    | succ k=>simp [Nat.choose_eq_zero_of_lt]
  | succ m ih =>
    cases k with
    | zero=>simp
    | succ k =>
      rw [Nat.choose_succ_succ (m+1) (k+1),add_mul]
      have h1:=ih (k+1)
      have h2:=ih k
      have h3:(m+1).choose (k+1) * (k+2)=(m+1).choose (k+1) * (k+1)+(m+1).choose (k+1):=by ring
      rw [h3,h2,Nat.choose_succ_succ m k]
      linarith
def jinv:ℕ → ℤ
  | 0=>1
  | 1 => -1
  | m+2 => -jinv (m+1) - (m+1:ℤ) * jinv m
lemma q104 (d:ℕ) :
    ∑ a ∈ Finset.range (d+1),(d.choose a:ℤ) * jinv (d - a) * (q11 a:ℤ) =
      if d=0 then 1 else 0:=by
  cases d with
  | zero=>simp [jinv,q45]
  | succ m =>
    simp only [Nat.succ_ne_zero,↓reduceIte]
    have hsplit:∑ a ∈ Finset.range (m+2),((m+1).choose a:ℤ) * jinv (m+1 - a) * (q11 a:ℤ) =
        (∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m+1 - a) * (q11 a:ℤ)) +
        (∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m - a) * (q11 (a+1):ℤ)):=by
      rw [Finset.sum_range_succ,Nat.choose_self,Nat.sub_self,jinv,Nat.cast_one,one_mul,one_mul]
      rw [Finset.sum_range_succ',Nat.choose_zero_right,Nat.sub_zero,q45,Nat.cast_one,one_mul,mul_one]
      have hmid:∑ k ∈ Finset.range m,((m+1).choose (k+1):ℤ) * jinv (m+1 - (k+1)) * (q11 (k+1):ℤ) =
          (∑ k ∈ Finset.range m,(m.choose (k+1):ℤ) * jinv (m - k) * (q11 (k+1):ℤ)) +
          (∑ k ∈ Finset.range m,(m.choose k:ℤ) * jinv (m - k) * (q11 (k+1):ℤ)):=by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hsub:m+1 - (k+1)=m - k:=by omega
        rw [hsub,Nat.choose_succ_succ,Nat.cast_add];ring
      rw [hmid]
      have hA:∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m+1 - a) * (q11 a:ℤ) =
          jinv (m+1)+∑ k ∈ Finset.range m,(m.choose (k+1):ℤ) * jinv (m - k) * (q11 (k+1):ℤ):=by
        rw [Finset.sum_range_succ',Nat.choose_zero_right,Nat.sub_zero,q45]
        simp only [Nat.cast_one,one_mul,mul_one,add_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have hsub:m+1 - (k+1)=m - k:=by omega
        rw [hsub]
      have hB:∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m - a) * (q11 (a+1):ℤ) =
          (∑ k ∈ Finset.range m,(m.choose k:ℤ) * jinv (m - k) * (q11 (k+1):ℤ)) +
            (q11 (m+1):ℤ):=by
        rw [Finset.sum_range_succ,Nat.choose_self,Nat.sub_self,jinv]
        simp
      rw [hA,hB];ring
    rw [hsplit]
    cases m with
    | zero=>simp [jinv,q45,q153]
    | succ m =>
      have h1:∑ a ∈ Finset.range (m+2),((m+1).choose a:ℤ) * jinv (m+2 - a) * (q11 a:ℤ) =
          -(∑ a ∈ Finset.range (m+2),((m+1).choose a:ℤ) * jinv (m+1 - a) * (q11 a:ℤ)) -
          (m+1:ℤ) * ∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m - a) * (q11 a:ℤ):=by
        conv_lhs=>rw [Finset.sum_range_succ]
        conv_rhs=>rw [Finset.sum_range_succ]
        have hlast1:m+2 - (m+1)=1:=by omega
        have hlast2:m+1 - (m+1)=0:=by omega
        rw [hlast1,hlast2,jinv,jinv,Nat.choose_self,Nat.cast_one,one_mul,one_mul]
        have hsum:∑ a ∈ Finset.range (m+1),((m+1).choose a:ℤ) * jinv (m+2 - a) * (q11 a:ℤ) =
            -(∑ a ∈ Finset.range (m+1),((m+1).choose a:ℤ) * jinv (m+1 - a) * (q11 a:ℤ)) -
            (m+1:ℤ) * ∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m - a) * (q11 a:ℤ):=by
          rw [Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a ha => ?_
          have halt:a < m+1:=Finset.mem_range.1 ha
          have hsub2:m+2 - a=(m - a)+2:=by omega
          have hsub1:m+1 - a=(m - a)+1:=by omega
          rw [hsub2,hsub1,jinv]
          have hch:((m+1).choose a:ℤ) * (((m - a:ℕ):ℤ)+1)=(m+1:ℤ) * (m.choose a:ℤ):=by
            have hnat:(m+1).choose a * (m - a+1)=(m+1) * m.choose a:=by
              have hle:a ≤ m:=by omega
              have h1':(m+1).choose a * (m+1 - a)=(m+1) * m.choose a:=by
                have hc1:=Nat.choose_symm (by omega:a ≤ m+1)
                have hc2:=Nat.choose_symm hle
                rw [← hc1,← hc2]
                have h2':m+1 - a=(m - a)+1:=by omega
                rw [h2',q57]
              have h3':m - a+1=m+1 - a:=by omega
              rw [h3'];exact h1'
            exact_mod_cast hnat
          calc ((m+1).choose a:ℤ) * (-jinv (m - a+1) - (↑(m - a)+1) * jinv (m - a)) * (q11 a:ℤ)
              = -(((m+1).choose a:ℤ) * jinv (m - a+1) * (q11 a:ℤ)) -
                (((m+1).choose a:ℤ) * (((m - a:ℕ):ℤ)+1)) * jinv (m - a) * (q11 a:ℤ):=by ring
            _ = -(((m+1).choose a:ℤ) * jinv (m - a+1) * (q11 a:ℤ)) -
                (m+1:ℤ) * ((m.choose a:ℤ) * jinv (m - a) * (q11 a:ℤ)):=by rw [hch];ring
        rw [hsum];ring
      have h2:∑ a ∈ Finset.range (m+2),((m+1).choose a:ℤ) * jinv (m+1 - a) * (q11 (a+1):ℤ) =
          (∑ a ∈ Finset.range (m+2),((m+1).choose a:ℤ) * jinv (m+1 - a) * (q11 a:ℤ)) +
          (m+1:ℤ) * ∑ a ∈ Finset.range (m+1),(m.choose a:ℤ) * jinv (m - a) * (q11 a:ℤ):=by
        conv_lhs=>rw [Finset.sum_range_succ']
        conv_rhs=>rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right,Nat.sub_zero,zero_add,q45,q153,Nat.cast_one,one_mul,mul_one]
        have hsum:∑ k ∈ Finset.range (m+1),((m+1).choose (k+1):ℤ) * jinv (m+1 - (k+1)) * (q11 (k+2):ℤ) =
            (∑ k ∈ Finset.range (m+1),((m+1).choose (k+1):ℤ) * jinv (m - k) * (q11 (k+1):ℤ)) +
            (m+1:ℤ) * ∑ k ∈ Finset.range (m+1),(m.choose k:ℤ) * jinv (m - k) * (q11 k:ℤ):=by
          rw [Finset.mul_sum,← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hsub:m+1 - (k+1)=m - k:=by omega
          rw [hsub,q117,Nat.cast_add,Nat.cast_mul]
          have hch:((m+1).choose (k+1):ℤ) * (k+1:ℤ)=(m+1:ℤ) * (m.choose k:ℤ):=by
            exact_mod_cast (q57 m k)
          calc ((m+1).choose (k+1):ℤ) * jinv (m - k) * ((q11 (k+1):ℤ)+(↑(k+1):ℤ) * (q11 k:ℤ))
              = ((m+1).choose (k+1):ℤ) * jinv (m - k) * (q11 (k+1):ℤ) +
                (((m+1).choose (k+1):ℤ) * (k+1:ℤ)) * jinv (m - k) * (q11 k:ℤ):=by push_cast;ring
            _=((m+1).choose (k+1):ℤ) * jinv (m - k) * (q11 (k+1):ℤ) +
                (m+1:ℤ) * ((m.choose k:ℤ) * jinv (m - k) * (q11 k:ℤ)):=by rw [hch];ring
        have hsub2:∑ k ∈ Finset.range (m+1),((m+1).choose (k+1):ℤ) * jinv (m+1 - (k+1)) * (q11 (k+1):ℤ) =
            ∑ k ∈ Finset.range (m+1),((m+1).choose (k+1):ℤ) * jinv (m - k) * (q11 (k+1):ℤ):=by
          refine Finset.sum_congr rfl fun k _ => ?_
          have:m+1 - (k+1)=m - k:=by omega
          rw [this]
        rw [hsum,hsub2];ring
      rw [h1,h2];ring
def q8:ℕ → ℕ → ℕ
  | 0,0=>1
  | 0,_+1=>0
  | _+1,0=>0
  | m+1,h+1=>(h+1) * q8 m (h+1)+q8 m h
lemma q160 (m h:ℕ) (hmh:m < h):q8 m h=0:=by
  induction m generalizing h with
  | zero=>cases h with | zero=>omega | succ h=>rfl
  | succ m ih =>
    cases h with
    | zero=>omega
    | succ h =>
      simp only [q8]
      rw [ih (h+1) (by omega),ih h (by omega),mul_zero,add_zero]
lemma q68 (m x:ℕ) :
    ∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * (x.descFactorial h:ℤ)=(x:ℤ) ^ m:=by
  induction m with
  | zero=>simp [q8]
  | succ m ih =>
    have hstep:∀ h:ℕ,((h+1:ℤ) * (x.descFactorial (h+1):ℤ)) +
        (x.descFactorial (h+2):ℤ)=(x:ℤ) * (x.descFactorial (h+1):ℤ):=by
      intro h
      by_cases hle:h+1 ≤ x
      · rw [Nat.descFactorial_succ x (h+1)]
        have hsub:((x - (h+1):ℕ):ℤ)=(x:ℤ) - (h+1:ℤ):=by omega
        rw [Nat.cast_mul,hsub];ring
      · have h1:x.descFactorial (h+1)=0:=Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
        have h2:x.descFactorial (h+2)=0:=Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
        rw [h1,h2];simp
    rw [Finset.sum_range_succ']
    have hst0:q8 (m+1) 0=0:=rfl
    rw [hst0]
    simp only [Nat.cast_zero,zero_mul,add_zero]
    have hsum:∑ h ∈ Finset.range (m+1),(q8 (m+1) (h+1):ℤ) * (x.descFactorial (h+1):ℤ) =
        (∑ h ∈ Finset.range (m+1),((h+1:ℤ) * (q8 m (h+1):ℤ)) * (x.descFactorial (h+1):ℤ)) +
        (∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * (x.descFactorial (h+1):ℤ)):=by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [q8,Nat.cast_add,Nat.cast_mul];ring
    rw [hsum]
    have hA:∑ h ∈ Finset.range (m+1),((h+1:ℤ) * (q8 m (h+1):ℤ)) * (x.descFactorial (h+1):ℤ) =
        ∑ h ∈ Finset.range m,((h+1:ℤ) * (q8 m (h+1):ℤ)) * (x.descFactorial (h+1):ℤ):=by
      rw [Finset.sum_range_succ,q160 m (m+1) (by omega)];simp
    have hB:∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * (x.descFactorial (h+1):ℤ) =
        (q8 m 0:ℤ) * (x:ℤ) +
        ∑ h ∈ Finset.range m,(q8 m (h+1):ℤ) * (x.descFactorial (h+2):ℤ):=by
      rw [Finset.sum_range_succ',Nat.descFactorial_one];ring
    rw [hA,hB]
    have hcomb:(∑ h ∈ Finset.range m,((h+1:ℤ) * (q8 m (h+1):ℤ)) * (x.descFactorial (h+1):ℤ)) +
        (∑ h ∈ Finset.range m,(q8 m (h+1):ℤ) * (x.descFactorial (h+2):ℤ)) =
        (x:ℤ) * ∑ h ∈ Finset.range m,(q8 m (h+1):ℤ) * (x.descFactorial (h+1):ℤ):=by
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      have:=hstep h
      calc ((h+1:ℤ) * (q8 m (h+1):ℤ)) * (x.descFactorial (h+1):ℤ) +
            (q8 m (h+1):ℤ) * (x.descFactorial (h+2):ℤ)
          = (q8 m (h+1):ℤ) * (((h+1:ℤ) * (x.descFactorial (h+1):ℤ)) +
              (x.descFactorial (h+2):ℤ)):=by ring
        _=(q8 m (h+1):ℤ) * ((x:ℤ) * (x.descFactorial (h+1):ℤ)):=by rw [this]
        _=(x:ℤ) * ((q8 m (h+1):ℤ) * (x.descFactorial (h+1):ℤ)):=by ring
    have hih2:∑ h ∈ Finset.range m,(q8 m (h+1):ℤ) * (x.descFactorial (h+1):ℤ) =
        (x:ℤ) ^ m - (q8 m 0:ℤ):=by
      rw [Finset.sum_range_succ'] at ih
      simp only [Nat.descFactorial_zero,Nat.cast_one,mul_one] at ih
      linarith
    calc _=(q8 m 0:ℤ) * (x:ℤ) +
            (x:ℤ) * ∑ h ∈ Finset.range m,(q8 m (h+1):ℤ) * (x.descFactorial (h+1):ℤ):=by
              linarith [hcomb]
      _=(q8 m 0:ℤ) * (x:ℤ)+(x:ℤ) * ((x:ℤ) ^ m - (q8 m 0:ℤ)):=by rw [hih2]
      _=(x:ℤ) ^ (m+1):=by ring
lemma q69 (m h:ℕ) :
    (h.factorial:ℤ) * (q8 m h:ℤ) =
      ∑ i ∈ Finset.range (h+1),(-1:ℤ) ^ (h - i) * (h.choose i:ℤ) * (i:ℤ) ^ m:=by
  induction m generalizing h with
  | zero =>
    cases h with
    | zero=>simp [q8]
    | succ h =>
      simp only [q8,Nat.cast_zero,mul_zero,pow_zero,mul_one]
      have hbin:=add_pow (1:ℤ) (-1:ℤ) (h+1)
      rw [add_neg_cancel,zero_pow (Nat.succ_ne_zero h)] at hbin
      symm
      calc ∑ i ∈ Finset.range (h+2),(-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ)
          = ∑ i ∈ Finset.range (h+2),(1:ℤ) ^ i * (-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ):=by
            refine Finset.sum_congr rfl fun i _=>by simp
        _=0:=hbin.symm
  | succ m ih =>
    cases h with
    | zero=>simp [q8]
    | succ h =>
      simp only [q8,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
      rw [mul_add,← mul_assoc,mul_comm ((h+1).factorial:ℤ) (h+1:ℤ),mul_assoc,ih (h+1)]
      have hf:((h+1).factorial:ℤ)=(h+1:ℤ) * (h.factorial:ℤ):=by
        rw [Nat.factorial_succ];push_cast;ring
      rw [hf,mul_assoc,ih h]
      rw [Finset.mul_sum,Finset.mul_sum]
      conv_lhs=>arg 1;rw [Finset.sum_range_succ]
      conv_rhs=>rw [Finset.sum_range_succ]
      simp only [Nat.choose_self,Nat.sub_self,pow_zero,Nat.cast_one,one_mul]
      have htail:(∑ i ∈ Finset.range (h+1),(h+1:ℤ) * ((-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ m)) +
          (∑ i ∈ Finset.range (h+1),(h+1:ℤ) * ((-1:ℤ) ^ (h - i) * (h.choose i:ℤ) * (i:ℤ) ^ m)) =
          ∑ i ∈ Finset.range (h+1),(-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ (m+1):=by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hilt:i < h+1:=Finset.mem_range.1 hi
        have hpow:(-1:ℤ) ^ (h+1 - i) = -((-1:ℤ) ^ (h - i)):=by
          have:h+1 - i=(h - i)+1:=by omega
          rw [this,pow_succ];ring
        have hch:(h+1:ℤ) * (h.choose i:ℤ)=((h+1).choose i:ℤ) * (h+1 - i:ℤ):=by
          have hnat:(h+1) * h.choose i=(h+1).choose i * (h+1 - i):=by
            have hle:i ≤ h:=by omega
            have hc1:=Nat.choose_symm (by omega:i ≤ h+1)
            have hc2:=Nat.choose_symm hle
            rw [← hc1,← hc2]
            have h2':h+1 - i=(h - i)+1:=by omega
            rw [h2',q57]
          have hsub:((h+1 - i:ℕ):ℤ)=(h:ℤ)+1 - (i:ℤ):=by omega
          have hz:(h+1:ℤ) * (h.choose i:ℤ)=((h+1).choose i:ℤ) * ((h+1 - i:ℕ):ℤ):=by
            exact_mod_cast hnat
          rw [hz,hsub]
        rw [hpow]
        calc (h+1:ℤ) * (-(-1:ℤ) ^ (h - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ m) +
              (h+1:ℤ) * ((-1:ℤ) ^ (h - i) * (h.choose i:ℤ) * (i:ℤ) ^ m)
            = -(-1:ℤ) ^ (h - i) * (i:ℤ) ^ m *
                ((h+1:ℤ) * ((h+1).choose i:ℤ) - (h+1:ℤ) * (h.choose i:ℤ)):=by ring
          _ = -(-1:ℤ) ^ (h - i) * (i:ℤ) ^ m *
                ((h+1:ℤ) * ((h+1).choose i:ℤ) - ((h+1).choose i:ℤ) * (h+1 - i:ℤ)):=by rw [hch]
          _ = -(-1:ℤ) ^ (h - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ (m+1):=by ring
      have hlast:(h+1:ℤ) * (((h+1:ℕ):ℤ) ^ m)=((h+1:ℕ):ℤ) ^ (m+1):=by
        push_cast;ring
      calc ((∑ i ∈ Finset.range (h+1),(h+1:ℤ) * ((-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ m)) +
            (h+1:ℤ) * ((h+1:ℕ):ℤ) ^ m) +
            (∑ i ∈ Finset.range (h+1),(h+1:ℤ) * ((-1:ℤ) ^ (h - i) * (h.choose i:ℤ) * (i:ℤ) ^ m))
          = ((∑ i ∈ Finset.range (h+1),(h+1:ℤ) * ((-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ m)) +
            (∑ i ∈ Finset.range (h+1),(h+1:ℤ) * ((-1:ℤ) ^ (h - i) * (h.choose i:ℤ) * (i:ℤ) ^ m))) +
            (h+1:ℤ) * ((h+1:ℕ):ℤ) ^ m:=by ring
        _=(∑ i ∈ Finset.range (h+1),(-1:ℤ) ^ (h+1 - i) * ((h+1).choose i:ℤ) * (i:ℤ) ^ (m+1)) +
            ((h+1:ℕ):ℤ) ^ (m+1):=by rw [htail,hlast]
lemma q66 (j:ℕ) :
    ∑ k ∈ Finset.range (j+1),(-1:ℤ) ^ k * (q9 k:ℤ) *
      (L4.fixedCount (2 * j) (2 * k):ℤ) =
      if j=0 then 1 else 0:=by
  have hpos:(2:ℤ) ^ j * (j.factorial:ℤ)≠0:=by positivity
  apply mul_left_cancel₀ hpos
  rw [Finset.mul_sum]
  have hterm:∀ k ∈ Finset.range (j+1),
      (2:ℤ) ^ j * (j.factorial:ℤ) * ((-1:ℤ) ^ k * (q9 k:ℤ) *
        (L4.fixedCount (2 * j) (2 * k):ℤ)) =
      ((2 * j).factorial:ℤ) * ((-1:ℤ) ^ k * (j.choose k:ℤ)):=by
    intro k hk
    have hkj:k ≤ j:=Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [q95 j k hkj]
    have hnat:2 ^ j * j.factorial * (q9 k * ((2 * j).choose (2 * k) * q9 (j - k))) =
        (2 * j).factorial * j.choose k:=by
      have hdenom:(2 * k).factorial * (2 * (j - k)).factorial≠0:=by positivity
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hdenom)
      have hch1:(2 * j).choose (2 * k) * ((2 * k).factorial * (2 * (j - k)).factorial) =
          (2 * j).factorial:=by
        have h2:2 * j - 2 * k=2 * (j - k):=by omega
        rw [← h2,← mul_assoc,Nat.choose_mul_factorial_mul_factorial (by omega:2 * k ≤ 2 * j)]
      have hch2:j.choose k * (k.factorial * (j - k).factorial)=j.factorial:=by
        rw [← mul_assoc,Nat.choose_mul_factorial_mul_factorial hkj]
      have hpow:2 ^ j=2 ^ k * 2 ^ (j - k):=by rw [← pow_add,Nat.add_sub_of_le hkj]
      have hd1:=q20 k
      have hd2:=q20 (j - k)
      calc 2 ^ j * j.factorial * (q9 k * ((2 * j).choose (2 * k) * q9 (j - k))) *
            ((2 * k).factorial * (2 * (j - k)).factorial)
          = 2 ^ j * j.factorial * q9 k * q9 (j - k) *
            ((2 * j).choose (2 * k) * ((2 * k).factorial * (2 * (j - k)).factorial)):=by ring
        _=2 ^ j * j.factorial * q9 k * q9 (j - k) * (2 * j).factorial:=by rw [hch1]
        _=(2 ^ k * 2 ^ (j - k)) * (j.choose k * (k.factorial * (j - k).factorial)) *
            q9 k * q9 (j - k) * (2 * j).factorial:=by rw [hpow,← hch2]
        _=(2 * j).factorial * j.choose k *
            ((2 ^ k * k.factorial * q9 k) * (2 ^ (j - k) * (j - k).factorial * q9 (j - k))):=by ring
        _=(2 * j).factorial * j.choose k * ((2 * k).factorial * (2 * (j - k)).factorial):=by rw [hd1,hd2]
    have hint:(2:ℤ) ^ j * (j.factorial:ℤ) * ((q9 k:ℤ) * (((2 * j).choose (2 * k):ℤ) * (q9 (j - k):ℤ))) =
        ((2 * j).factorial:ℤ) * (j.choose k:ℤ):=by exact_mod_cast hnat
    calc (2:ℤ) ^ j * (j.factorial:ℤ) * ((-1:ℤ) ^ k * (q9 k:ℤ) *
            (((2 * j).choose (2 * k) * q9 (j - k):ℕ):ℤ))
        = (-1:ℤ) ^ k * ((2:ℤ) ^ j * (j.factorial:ℤ) *
            ((q9 k:ℤ) * (((2 * j).choose (2 * k):ℤ) * (q9 (j - k):ℤ)))):=by push_cast;ring
      _=(-1:ℤ) ^ k * (((2 * j).factorial:ℤ) * (j.choose k:ℤ)):=by rw [hint]
      _=((2 * j).factorial:ℤ) * ((-1:ℤ) ^ k * (j.choose k:ℤ)):=by ring
  rw [Finset.sum_congr rfl hterm,← Finset.mul_sum]
  cases j with
  | zero=>simp
  | succ j =>
    simp only [Nat.succ_ne_zero,↓reduceIte,mul_zero]
    have hbin:=add_pow (-1:ℤ) (1:ℤ) (j+1)
    rw [neg_add_cancel,zero_pow (Nat.succ_ne_zero j)] at hbin
    have hsum0:∑ k ∈ Finset.range (j+2),(-1:ℤ) ^ k * ((j+1).choose k:ℤ)=0:=by
      calc ∑ k ∈ Finset.range (j+2),(-1:ℤ) ^ k * ((j+1).choose k:ℤ)
          = ∑ k ∈ Finset.range (j+2),(-1:ℤ) ^ k * (1:ℤ) ^ (j+1 - k) * ((j+1).choose k:ℤ):=by
            refine Finset.sum_congr rfl fun k _=>by simp
        _=0:=hbin.symm
    rw [hsum0,mul_zero]
def q31 (n j:ℕ):Polynomial ℤ :=
  ((Finset.range (n+1)).erase j).prod (fun r=>Polynomial.X - Polynomial.C (2 * (r:ℤ)))
lemma q80 (n j:ℕ) (hj:j ≤ n):(q31 n j).natDegree ≤ n:=by
  unfold q31
  have h1:(((Finset.range (n+1)).erase j).prod (fun r=>Polynomial.X - Polynomial.C (2 * (r:ℤ)))).natDegree ≤
      ∑ r ∈ (Finset.range (n+1)).erase j,(Polynomial.X - Polynomial.C (2 * (r:ℤ))).natDegree :=
    Polynomial.natDegree_prod_le ((Finset.range (n+1)).erase j) (fun r=>Polynomial.X - Polynomial.C (2 * (r:ℤ)))
  have h2:∑ r ∈ (Finset.range (n+1)).erase j,(Polynomial.X - Polynomial.C (2 * (r:ℤ))).natDegree =
      ∑ _r ∈ (Finset.range (n+1)).erase j,(1:ℕ) :=
    Finset.sum_congr rfl fun r _=>Polynomial.natDegree_X_sub_C (2 * (r:ℤ))
  have h3:(∑ _r ∈ (Finset.range (n+1)).erase j,(1:ℕ))=n:=by
    rw [Finset.sum_const,smul_eq_mul,mul_one,Finset.card_erase_of_mem (Finset.mem_range.2 (by omega)),
      Finset.card_range]
    omega
  omega
lemma q127 (n j r:ℕ) (hr:r ≤ n) (hrj:r≠j) :
    (q31 n j).eval (2 * (r:ℤ))=0:=by
  unfold q31
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hrj,Finset.mem_range.2 (by omega)⟩) (by simp)
lemma q103 (n j:ℕ) (hj:j ≤ n) :
    (q31 n j).eval (2 * (j:ℤ)) =
      (-1:ℤ) ^ (n - j) * (2:ℤ) ^ n * (j.factorial:ℤ) * ((n - j).factorial:ℤ):=by
  unfold q31
  rw [Polynomial.eval_prod]
  have hsplit:(Finset.range (n+1)).erase j =
      Finset.range j ∪ Finset.Ioo j (n+1):=by
    ext r
    simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_union,Finset.mem_Ioo]
    omega
  have hdisj:Disjoint (Finset.range j) (Finset.Ioo j (n+1)):=by
    rw [Finset.disjoint_left];intro r hr1 hr2
    simp only [Finset.mem_range,Finset.mem_Ioo] at hr1 hr2;omega
  rw [hsplit,Finset.prod_union hdisj]
  have hleft:∏ r ∈ Finset.range j,(Polynomial.X - Polynomial.C (2 * (r:ℤ))).eval (2 * (j:ℤ)) =
      (2:ℤ) ^ j * (j.factorial:ℤ):=by
    have hbij:∏ r ∈ Finset.range j,((2 * (j:ℤ)) - 2 * (r:ℤ)) =
        ∏ d ∈ Finset.range j,(2 * ((d+1:ℕ):ℤ)):=by
      refine Finset.prod_bij (fun r _=>j - 1 - r) ?_ ?_ ?_ ?_
      · intro r hr;simp only [Finset.mem_range] at hr ⊢;omega
      · intro r1 hr1 r2 hr2 he;simp only [Finset.mem_range] at hr1 hr2;omega
      · intro d hd;simp only [Finset.mem_range] at hd
        exact ⟨j - 1 - d,Finset.mem_range.2 (by omega),by omega⟩
      · intro r hr;simp only [Finset.mem_range] at hr
        have h1:(j - 1 - r+1:ℕ)=j - r:=by omega
        rw [h1];omega
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    rw [hbij,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]
    congr 1
    exact_mod_cast (Finset.prod_range_add_one_eq_factorial j)
  have hright:∏ r ∈ Finset.Ioo j (n+1),(Polynomial.X - Polynomial.C (2 * (r:ℤ))).eval (2 * (j:ℤ)) =
      (-1:ℤ) ^ (n - j) * (2:ℤ) ^ (n - j) * ((n - j).factorial:ℤ):=by
    have hbij:∏ r ∈ Finset.Ioo j (n+1),((2 * (j:ℤ)) - 2 * (r:ℤ)) =
        ∏ d ∈ Finset.range (n - j),((-1:ℤ) * (2 * ((d+1:ℕ):ℤ))):=by
      refine Finset.prod_bij (fun r _=>r - j - 1) ?_ ?_ ?_ ?_
      · intro r hr;simp only [Finset.mem_Ioo,Finset.mem_range] at hr ⊢;omega
      · intro r1 hr1 r2 hr2 he;simp only [Finset.mem_Ioo] at hr1 hr2;omega
      · intro d hd;simp only [Finset.mem_range] at hd
        exact ⟨j+d+1,Finset.mem_Ioo.2 (by omega),by omega⟩
      · intro r hr;simp only [Finset.mem_Ioo] at hr
        have h1:(r - j - 1+1:ℕ)=r - j:=by omega
        rw [h1];omega
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    rw [hbij,Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_const,
      Finset.card_range,← mul_assoc]
    congr 1
    exact_mod_cast (Finset.prod_range_add_one_eq_factorial (n - j))
  rw [hleft,hright]
  have hpow:(2:ℤ) ^ j * (2:ℤ) ^ (n - j)=(2:ℤ) ^ n:=by
    rw [← pow_add,Nat.add_sub_of_le hj]
  calc (2:ℤ) ^ j * (j.factorial:ℤ) * ((-1:ℤ) ^ (n - j) * (2:ℤ) ^ (n - j) * ((n - j).factorial:ℤ))
      = (-1:ℤ) ^ (n - j) * ((2:ℤ) ^ j * (2:ℤ) ^ (n - j)) * (j.factorial:ℤ) * ((n - j).factorial:ℤ):=by ring
    _=(-1:ℤ) ^ (n - j) * (2:ℤ) ^ n * (j.factorial:ℤ) * ((n - j).factorial:ℤ):=by rw [hpow]
def q27 (n:ℕ) (Z:ℕ → ℤ):ℤ :=
  let y:ℕ → ℤ := fun h=>∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Z t
  let p:ℕ → ℤ := fun m=>∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * y h
  (-1:ℤ) ^ n * ∑ j ∈ Finset.range (n+1),
    (q9 j:ℤ) * (n.choose j:ℤ) *
      ∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * p m
lemma q106 (n:ℕ) (x:Fin (n+1) → ℤ) (Z:ℕ → ℤ)
    (hZ:∀ t:Fin (n+1),Z t.val=∑ j:Fin (n+1),(q11 (t.val+2 * j.val):ℤ) * x j) :
    q27 n Z=(2:ℤ) ^ n * (n.factorial:ℤ) * x ⟨0,Nat.succ_pos n⟩:=by
  let w:Fin (n+1) → ℤ := fun k =>
    ∑ j:Fin (n+1),(L4.fixedCount (2 * j.val) (2 * k.val):ℤ) * x j
  have hZ_fact:∀ t:Fin (n+1),
      Z t.val=∑ s ∈ Finset.range (t.val+1),
        (t.val.choose s:ℤ) * (q11 (t.val - s):ℤ) *
          ∑ k:Fin (n+1),((2 * k.val).descFactorial s:ℤ) * w k:=by
    intro t
    rw [hZ t]
    have hinv:∀ j:Fin (n+1),(q11 (t.val+2 * j.val):ℤ) =
        ∑ k:Fin (n+1),
          (∑ s ∈ Finset.range (t.val+1),((2 * k.val).choose s:ℤ) * (t.val.descFactorial s:ℤ) *
            (q11 (t.val - s):ℤ)) *
          (L4.fixedCount (2 * j.val) (2 * k.val):ℤ):=by
      intro j
      have h1:=L4.invCount_interpolation_padded n 0 t.val (by omega) j
      simp only [zero_add] at h1
      exact_mod_cast h1
    simp_rw [hinv]
    conv_lhs=>arg 2;ext j;rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hswap:∀ k:Fin (n+1),
        ∑ j:Fin (n+1),
          (∑ s ∈ Finset.range (t.val+1),((2 * k.val).choose s:ℤ) * (t.val.descFactorial s:ℤ) *
            (q11 (t.val - s):ℤ)) *
            (L4.fixedCount (2 * j.val) (2 * k.val):ℤ) * x j =
        (∑ s ∈ Finset.range (t.val+1),((2 * k.val).choose s:ℤ) * (t.val.descFactorial s:ℤ) *
          (q11 (t.val - s):ℤ)) * w k:=by
      intro k;dsimp only [w];rw [Finset.mul_sum];refine Finset.sum_congr rfl fun j _=>by ring
    rw [Finset.sum_congr rfl fun k _=>hswap k]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hch:((2 * k.val).choose s:ℤ) * (t.val.descFactorial s:ℤ) =
        (t.val.choose s:ℤ) * ((2 * k.val).descFactorial s:ℤ):=by
      exact_mod_cast (by
        have h1:=Nat.descFactorial_eq_factorial_mul_choose (2 * k.val) s
        have h2:=Nat.descFactorial_eq_factorial_mul_choose t.val s
        have hf:s.factorial≠0:=Nat.factorial_ne_zero s
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf)
        calc s.factorial * ((2 * k.val).choose s * t.val.descFactorial s)
            = (s.factorial * (2 * k.val).choose s) * t.val.descFactorial s:=by ring
          _=(2 * k.val).descFactorial s * (s.factorial * t.val.choose s):=by rw [← h1,h2]
          _=s.factorial * (t.val.choose s * (2 * k.val).descFactorial s):=by ring)
    calc ((2 * k.val).choose s:ℤ) * (t.val.descFactorial s:ℤ) * (q11 (t.val - s):ℤ) * w k
        = (((2 * k.val).choose s:ℤ) * (t.val.descFactorial s:ℤ)) * (q11 (t.val - s):ℤ) * w k:=rfl
      _=(t.val.choose s:ℤ) * ((2 * k.val).descFactorial s:ℤ) * (q11 (t.val - s):ℤ) * w k:=by rw [hch]
      _=(t.val.choose s:ℤ) * (q11 (t.val - s):ℤ) * (((2 * k.val).descFactorial s:ℤ) * w k):=by ring
  let y:ℕ → ℤ := fun h=>∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Z t
  have hy_eq:∀ h ≤ n,y h=∑ k:Fin (n+1),((2 * k.val).descFactorial h:ℤ) * w k:=by
    intro h hh
    dsimp only [y]
    have hZ':∀ t ∈ Finset.range (h+1),
        Z t=∑ s ∈ Finset.range (h+1),
          (t.choose s:ℤ) * (q11 (t - s):ℤ) *
            ∑ k:Fin (n+1),((2 * k.val).descFactorial s:ℤ) * w k:=by
      intro t ht
      have htl:t < h+1:=Finset.mem_range.1 ht
      rw [hZ_fact ⟨t,by omega⟩]
      refine Finset.sum_subset (Finset.range_mono (by omega:t+1 ≤ h+1)) fun s hs hnot => ?_
      have hgt:t < s:=by simp only [Finset.mem_range] at hnot;omega
      rw [Nat.choose_eq_zero_of_lt hgt];simp
    have hstep1:∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Z t =
        ∑ s ∈ Finset.range (h+1),
          (∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * (t.choose s:ℤ) * (q11 (t - s):ℤ)) *
            ∑ k:Fin (n+1),((2 * k.val).descFactorial s:ℤ) * w k:=by
      calc ∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Z t
          = ∑ t ∈ Finset.range (h+1),∑ s ∈ Finset.range (h+1),
              ((h.choose t:ℤ) * jinv (h - t) * (t.choose s:ℤ) * (q11 (t - s):ℤ)) *
                ∑ k:Fin (n+1),((2 * k.val).descFactorial s:ℤ) * w k:=by
            refine Finset.sum_congr rfl fun t ht => ?_
            rw [hZ' t ht,Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _=>by ring
        _=_:=by rw [Finset.sum_comm];refine Finset.sum_congr rfl fun s _=>by rw [Finset.sum_mul]
    rw [hstep1]
    rw [Finset.sum_eq_single h]
    · have hdiag:∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * (t.choose h:ℤ) * (q11 (t - h):ℤ)=1:=by
        rw [Finset.sum_eq_single h]
        · simp [jinv,q45]
        · intro t ht hne
          have hlt:t < h:=by have:=Finset.mem_range.1 ht;omega
          rw [Nat.choose_eq_zero_of_lt hlt];simp
        · intro hm;exact absurd (Finset.mem_range.2 (Nat.lt_succ_self h)) hm
      rw [hdiag,one_mul]
    · intro s hs hne
      have hslt:s < h:=by have:=Finset.mem_range.1 hs;omega
      have hzero:∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * (t.choose s:ℤ) * (q11 (t - s):ℤ)=0:=by
        have hzero':∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * (t.choose s:ℤ) * (q11 (t - s):ℤ) =
            ∑ t ∈ Finset.Ico s (h+1),(h.choose t:ℤ) * jinv (h - t) * (t.choose s:ℤ) * (q11 (t - s):ℤ):=by
          symm
          refine Finset.sum_subset (fun t ht=>Finset.mem_range.2 (Finset.mem_Ico.1 ht).2) fun t ht hnot => ?_
          have hlt:t < s:=by
            have:=Finset.mem_range.1 ht
            simp only [Finset.mem_Ico,not_and] at hnot
            by_contra hge;exact hnot (by omega) this
          rw [Nat.choose_eq_zero_of_lt hlt];simp
        rw [hzero']
        have hbij2:∑ t ∈ Finset.Ico s (h+1),(h.choose t:ℤ) * jinv (h - t) * (t.choose s:ℤ) * (q11 (t - s):ℤ) =
            (h.choose s:ℤ) * ∑ a ∈ Finset.range (h - s+1),
              ((h - s).choose a:ℤ) * jinv (h - s - a) * (q11 a:ℤ):=by
          rw [Finset.mul_sum]
          symm
          refine Finset.sum_bij (fun a _=>a+s) ?_ ?_ ?_ ?_
          · intro a ha;simp only [Finset.mem_range,Finset.mem_Ico] at ha ⊢;omega
          · intro a1 _ a2 _ he;omega
          · intro t ht;simp only [Finset.mem_Ico] at ht
            exact ⟨t - s,Finset.mem_range.2 (by omega),by omega⟩
          · intro a ha
            have hle:a+s ≤ h:=by have:=Finset.mem_range.1 ha;omega
            have h1:h - (a+s)=h - s - a:=by omega
            have h2:a+s - s=a:=by omega
            have hch:(h.choose s:ℤ) * ((h - s).choose a:ℤ)=(h.choose (a+s):ℤ) * ((a+s).choose s:ℤ):=by
              exact_mod_cast (by
                have hcm := @Nat.choose_mul h (a+s) s (by omega)
                rw [h2] at hcm
                exact hcm.symm)
            rw [h1,h2]
            calc (h.choose s:ℤ) * (((h - s).choose a:ℤ) * jinv (h - s - a) * (q11 a:ℤ))
                = ((h.choose s:ℤ) * ((h - s).choose a:ℤ)) * jinv (h - s - a) * (q11 a:ℤ):=by ring
              _=((h.choose (a+s):ℤ) * ((a+s).choose s:ℤ)) * jinv (h - s - a) * (q11 a:ℤ):=by rw [hch]
              _=(h.choose (a+s):ℤ) * jinv (h - s - a) * ((a+s).choose s:ℤ) * (q11 a:ℤ):=by ring
        rw [hbij2,q104 (h - s),ite_eq_right_iff.2 (fun h0=>by omega),mul_zero]
      rw [hzero,zero_mul]
    · intro hm;exact absurd (Finset.mem_range.2 (Nat.lt_succ_self h)) hm
  let p:ℕ → ℤ := fun m=>∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * y h
  have hp_eq:∀ m ≤ n,p m=∑ k:Fin (n+1),(2 * (k.val:ℤ)) ^ m * w k:=by
    intro m hm
    dsimp only [p]
    have h1:∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * y h =
        ∑ h ∈ Finset.range (m+1),∑ k:Fin (n+1),
          ((q8 m h:ℤ) * ((2 * k.val).descFactorial h:ℤ)) * w k:=by
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hy_eq h (by have:=Finset.mem_range.1 hh;omega),Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _=>by ring
    rw [h1,Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul,q68 m (2 * k.val)]
    push_cast;rfl
  unfold q27
  dsimp only
  have hinner:∀ (j:ℕ) (hj:j < n+1),
      ∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * p m =
      (-1:ℤ) ^ (n - j) * (2:ℤ) ^ n * (j.factorial:ℤ) * ((n - j).factorial:ℤ) *
        w ⟨j,hj⟩:=by
    intro j hj
    have hjl:j ≤ n:=Nat.lt_succ_iff.1 hj
    have h1:∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * p m =
        ∑ k:Fin (n+1),(q31 n j).eval (2 * (k.val:ℤ)) * w k:=by
      calc ∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * p m
          = ∑ m ∈ Finset.range (n+1),∑ k:Fin (n+1),
              ((q31 n j).coeff m * (2 * (k.val:ℤ)) ^ m) * w k:=by
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [hp_eq m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)),Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _=>by ring
        _=∑ k:Fin (n+1),(∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * (2 * (k.val:ℤ)) ^ m) * w k:=by
            rw [Finset.sum_comm];refine Finset.sum_congr rfl fun k _=>by rw [Finset.sum_mul]
        _=∑ k:Fin (n+1),(q31 n j).eval (2 * (k.val:ℤ)) * w k:=by
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            exact (Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (q80 n j hjl) (Nat.lt_succ_self n)) _).symm
    rw [h1,Finset.sum_eq_single (⟨j,hj⟩:Fin (n+1))]
    · rw [q103 n j hjl]
    · intro k _ hne
      have hnev:k.val≠j:=fun h=>hne (Fin.ext h)
      rw [q127 n j k.val (Nat.lt_succ_iff.1 k.isLt) hnev,zero_mul]
    · intro hm;exact absurd (Finset.mem_univ _) hm
  have houter:(-1:ℤ) ^ n * ∑ j ∈ Finset.range (n+1),
      (q9 j:ℤ) * (n.choose j:ℤ) * ∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * p m =
      (2:ℤ) ^ n * (n.factorial:ℤ) * ∑ k:Fin (n+1),(-1:ℤ) ^ k.val * (q9 k.val:ℤ) * w k:=by
    rw [← Fin.sum_univ_eq_sum_range,Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hkl:k.val ≤ n:=Nat.lt_succ_iff.1 k.isLt
    rw [hinner k.val k.isLt]
    have hch:(n.choose k.val:ℤ) * ((k.val.factorial:ℤ) * ((n - k.val).factorial:ℤ))=(n.factorial:ℤ):=by
      exact_mod_cast (by rw [← mul_assoc];exact Nat.choose_mul_factorial_mul_factorial hkl)
    have hsign:(-1:ℤ) ^ n * (-1:ℤ) ^ (n - k.val)=(-1:ℤ) ^ k.val:=by
      rw [← pow_add]
      have h2:n+(n - k.val)=k.val+2 * (n - k.val):=by omega
      rw [h2,pow_add,pow_mul];norm_num
    calc (-1:ℤ) ^ n * ((q9 k.val:ℤ) * (n.choose k.val:ℤ) *
            ((-1:ℤ) ^ (n - k.val) * (2:ℤ) ^ n * (k.val.factorial:ℤ) * ((n - k.val).factorial:ℤ) * w k))
        = ((-1:ℤ) ^ n * (-1:ℤ) ^ (n - k.val)) * (2:ℤ) ^ n *
            ((n.choose k.val:ℤ) * ((k.val.factorial:ℤ) * ((n - k.val).factorial:ℤ))) *
            (q9 k.val:ℤ) * w k:=by ring
      _=(-1:ℤ) ^ k.val * (2:ℤ) ^ n * (n.factorial:ℤ) * (q9 k.val:ℤ) * w k:=by rw [hsign,hch]
      _=(2:ℤ) ^ n * (n.factorial:ℤ) * ((-1:ℤ) ^ k.val * (q9 k.val:ℤ) * w k):=by ring
  rw [houter]
  congr 1
  simp only [w,Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (⟨0,Nat.succ_pos n⟩:Fin (n+1))]
  · rw [Finset.sum_eq_single (⟨0,Nat.succ_pos n⟩:Fin (n+1))]
    · simp [q9,L4.fixedCount_diagonal]
    · intro k _ hne
      have hgt:0 < 2 * k.val:=by have:k.val≠0:=fun h=>hne (Fin.ext h);omega
      simp only [Fin.val_mk,mul_zero]
      rw [L4.fixedCount_zero 0 (2 * k.val) hgt];simp
    · intro hm;exact absurd (Finset.mem_univ _) hm
  · intro j _ hjne
    have hcoeff:∑ k:Fin (n+1),(-1:ℤ) ^ k.val * (q9 k.val:ℤ) *
        ((L4.fixedCount (2 * j.val) (2 * k.val):ℤ) * x j) =
        (∑ k ∈ Finset.range (j.val+1),(-1:ℤ) ^ k * (q9 k:ℤ) *
          (L4.fixedCount (2 * j.val) (2 * k):ℤ)) * x j:=by
      have h1:∑ k:Fin (n+1),(-1:ℤ) ^ k.val * (q9 k.val:ℤ) *
            ((L4.fixedCount (2 * j.val) (2 * k.val):ℤ) * x j) =
          (∑ k ∈ Finset.range (n+1),(-1:ℤ) ^ k * (q9 k:ℤ) *
            (L4.fixedCount (2 * j.val) (2 * k):ℤ)) * x j:=by
        rw [Finset.sum_mul,← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun k _=>by ring
      rw [h1]
      congr 1
      symm
      refine Finset.sum_subset (Finset.range_mono (by have:=j.isLt;omega:j.val+1 ≤ n+1)) fun k hk hnot => ?_
      have hgt:j.val < k:=by simp only [Finset.mem_range] at hnot;omega
      rw [L4.fixedCount_zero (2 * j.val) (2 * k) (by omega)];simp
    rw [hcoeff,q66 j.val,ite_eq_right_iff.2 (fun h=>(hjne (Fin.ext h)).elim),zero_mul]
  · intro hm;exact absurd (Finset.mem_univ _) hm
def fnOf {k:ℕ} (p:Equiv.Perm (Fin k)):(Fin k → Bool) → (Fin k → Bool) → Bool :=
  fun x y=>decide (∃ i:Fin k,
    (x i=true∧y i=true) ∨
    (p i≠i∧((x i=true∧x (p i)=true)∨(y i=true∧y (p i)=true))))
lemma q164 {k:ℕ} {p₁ p₂:Equiv.Perm (Fin k)}
    (hp₁:Function.Involutive p₁) (hp₂:Function.Involutive p₂)
    (heq:fnOf p₁=fnOf p₂):p₁=p₂:=by
  apply Equiv.ext
  intro u
  have hfn:∀ x y,fnOf p₁ x y=fnOf p₂ x y:=fun x y=>congrFun (congrFun heq x) y
  by_cases h1:p₁ u=u
  · by_contra hne
    have h2:p₂ u≠u:=fun h=>hne (by rw [h1,h])
    let x:Fin k → Bool:=fun i=>decide (i=u∨i=p₂ u)
    have htrue2:fnOf p₂ x (fun _=>false)=true:=by
      simp only [fnOf,decide_eq_true_eq]
      exact ⟨u,Or.inr ⟨h2,Or.inl ⟨by simp [x],by simp [x]⟩⟩⟩
    have htrue1:fnOf p₁ x (fun _=>false)=true:=(hfn x (fun _=>false)).trans htrue2
    simp only [fnOf,decide_eq_true_eq] at htrue1
    rcases htrue1 with ⟨i,⟨_,hfalse⟩ | ⟨hpi,⟨hxi,hxpi⟩ | ⟨hfalse,_⟩⟩⟩
    · exact Bool.false_ne_true hfalse
    · simp only [x,decide_eq_true_eq] at hxi hxpi
      rcases hxi with rfl | rfl
      · exact hpi h1
      · rcases hxpi with hpu | hpp
        · exact h2 (p₁.injective (hpu.trans h1.symm))
        · exact hpi hpp
    · exact Bool.false_ne_true hfalse
  · let x:Fin k → Bool:=fun i=>decide (i=u∨i=p₁ u)
    have htrue1:fnOf p₁ x (fun _=>false)=true:=by
      simp only [fnOf,decide_eq_true_eq]
      exact ⟨u,Or.inr ⟨h1,Or.inl ⟨by simp [x],by simp [x]⟩⟩⟩
    have htrue2:fnOf p₂ x (fun _=>false)=true:=(hfn x (fun _=>false)).symm.trans htrue1
    simp only [fnOf,decide_eq_true_eq] at htrue2
    rcases htrue2 with ⟨i,⟨_,hfalse⟩ | ⟨hpi,⟨hxi,hxpi⟩ | ⟨hfalse,_⟩⟩⟩
    · exact (Bool.false_ne_true hfalse).elim
    · simp only [x,decide_eq_true_eq] at hxi hxpi
      rcases hxi with rfl | rfl
      · rcases hxpi with hpu | hpp
        · exact (hpi hpu).elim
        · exact hpp.symm
      · rcases hxpi with hpu | hpp
        · have h2:p₂ u=p₁ u:=by
            calc p₂ u=p₂ (p₂ (p₁ u)):=by rw [hpu]
              _=p₁ u:=hp₂ (p₁ u)
          exact h2.symm
        · exact (hpi hpp).elim
    · exact (Bool.false_ne_true hfalse).elim
lemma q76 {m:ℕ} (M:Matrix (Fin (m+1)) (Fin (m+1)) ℤ) (c:Fin (m+1) → ℤ) :
    (M.updateCol 0 (fun t=>∑ j:Fin (m+1),c j * M t j)).det=c 0 * M.det:=by
  let U:Matrix (Fin (m+1)) (Fin (m+1)) ℤ :=
    (1:Matrix (Fin (m+1)) (Fin (m+1)) ℤ).updateCol 0 c
  have hmul:M.updateCol 0 (fun t=>∑ j:Fin (m+1),c j * M t j)=M * U:=by
    ext t k
    rw [Matrix.mul_apply]
    by_cases hk:k=0
    · subst hk
      simp only [Matrix.updateCol_self,U]
      refine Finset.sum_congr rfl fun j _=>by ring
    · simp only [Matrix.updateCol_ne hk,U,Matrix.one_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk;simp [hjk]
      · intro hm;exact absurd (Finset.mem_univ k) hm
  have htri:U.IsLowerTriangular:=by
    intro i j hij
    have hij':i < j:=hij
    have hj0:j≠0:=by
      intro h;subst h;exact Nat.not_lt_zero i.val hij'
    simp only [U,Matrix.updateCol_ne hj0,Matrix.one_apply]
    exact ite_eq_right_iff.2 fun h=>(ne_of_lt hij' h).elim
  have hUdet:U.det=c 0:=by
    rw [Matrix.det_of_isLowerTriangular U htri]
    rw [Finset.prod_eq_single (0:Fin (m+1))]
    · simp [U]
    · intro i _ hi0;simp [U,Matrix.updateCol_ne hi0]
    · intro hm;exact absurd (Finset.mem_univ _) hm
  rw [hmul,Matrix.det_mul,hUdet,mul_comm]
lemma q51 (n:ℕ) (A:Fin n → Fin n → Bool) (ones:List (Fin n × Fin n))
    (hones_nodup:ones.Nodup) (hmem_ones:∀ z:Fin n × Fin n,z ∈ ones↔A z.1 z.2=true) :
    let m:=ones.length
    let ends:Fin m → Fin (2 * n) × Fin (2 * n):=fun e =>
      (⟨(ones.get e).1.val,by have:=(ones.get e).1.isLt;omega⟩,
       ⟨n+(ones.get e).2.val,by have:=(ones.get e).2.isLt;omega⟩)
    let vertices:Fin m → Finset (Fin (2 * n)):=fun e=>{(ends e).1,(ends e).2}
    let matching:Finset (Fin m) → Prop :=
      fun S=>∀ e ∈ S,∀ g ∈ S,e≠g → Disjoint (vertices e) (vertices g)
    ((Finset.univ.filter matching).filter (fun S=>S.card=n)).card =
      Matrix.permanent (fun i j:Fin n=>(A i j).toNat):=by
  intro m ends vertices matching
  let B:Matrix (Fin n) (Fin n) ℕ := fun i j=>(A i j).toNat
  have hperm:Matrix.permanent B=(Finset.univ.filter (fun σ : Equiv.Perm (Fin n)=>∀ i,A i (σ i)=true)).card:=by
    rw [Matrix.permanent]
    have hsym:∑ σ : Equiv.Perm (Fin n),∏ i:Fin n,B (σ i) i =
        ∑ σ : Equiv.Perm (Fin n),∏ i:Fin n,B i (σ i):=by
      rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [Equiv.inv_apply]
      have h1:∏ i:Fin n,B (σ⁻¹ i) i=∏ i:Fin n,B (σ⁻¹ (σ i)) (σ i) :=
        (Equiv.prod_comp σ (fun i=>B (σ⁻¹ i) i)).symm
      rw [h1]
      refine Finset.prod_congr rfl fun i _=>by simp
    rw [hsym,Finset.card_eq_sum_ones,Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h:∀ i:Fin n,A i (σ i)=true
    · rw [ite_eq_left_iff.2 (fun hn=>(hn h).elim)]
      refine Finset.prod_eq_one fun i _ => ?_
      simp [B,h i]
    · rw [ite_eq_right_iff.2 (fun hp=>(h hp).elim)]
      have ⟨i,hi⟩:∃ i,A i (σ i)≠true:=by
        by_contra hall
        exact h fun i=>by by_contra hi';exact hall ⟨i,hi'⟩
      have hfalse:A i (σ i)=false:=by cases hA:A i (σ i) <;> simp_all
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [B,hfalse])
  rw [hperm]
  let Mset:=(Finset.univ.filter matching).filter (fun S=>S.card=n)
  let Pset:=Finset.univ.filter (fun σ : Equiv.Perm (Fin n)=>∀ i,A i (σ i)=true)
  have hbijL:∀ (S:Finset (Fin m)) (hS:S ∈ Mset),
      Function.Bijective (fun e:S=>(ones.get e.1).1):=by
    intro S hS
    have hM:matching S:=(Finset.mem_filter.1 (Finset.mem_filter.1 hS).1).2
    have hC:S.card=n:=(Finset.mem_filter.1 hS).2
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_,by rw [Fintype.card_coe,Fintype.card_fin,hC]⟩
    intro e₁ e₂ heq
    by_contra hne
    have hdisj:=hM e₁.1 e₁.2 e₂.1 e₂.2 (fun h=>hne (Subtype.ext h))
    have hv1:(ends e₁.1).1 ∈ vertices e₁.1:=by simp [vertices]
    have hv2:(ends e₁.1).1 ∈ vertices e₂.1:=by
      have:(ends e₁.1).1=(ends e₂.1).1:=Fin.ext (by dsimp only [ends];exact congrArg Fin.val heq)
      rw [this];simp [vertices]
    exact Finset.disjoint_left.1 hdisj hv1 hv2
  let eLOf:∀ (S:Finset (Fin m)) (hS:S ∈ Mset),S ≃ Fin n :=
    fun S hS=>Equiv.ofBijective (fun e:S=>(ones.get e.1).1) (hbijL S hS)
  have hbijR:∀ (S:Finset (Fin m)) (hS:S ∈ Mset),
      Function.Bijective (fun i:Fin n=>(ones.get ((eLOf S hS).symm i).1).2):=by
    intro S hS
    have hM:matching S:=(Finset.mem_filter.1 (Finset.mem_filter.1 hS).1).2
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_,rfl⟩
    intro i₁ i₂ heq
    by_contra hne
    have hne':((eLOf S hS).symm i₁).1≠((eLOf S hS).symm i₂).1 :=
      fun h=>hne ((eLOf S hS).symm.injective (Subtype.ext h))
    have hdisj:=hM _ ((eLOf S hS).symm i₁).2 _ ((eLOf S hS).symm i₂).2 hne'
    have hv1:(ends ((eLOf S hS).symm i₁).1).2 ∈ vertices ((eLOf S hS).symm i₁).1:=by simp [vertices]
    have hv2:(ends ((eLOf S hS).symm i₁).1).2 ∈ vertices ((eLOf S hS).symm i₂).1:=by
      have:(ends ((eLOf S hS).symm i₁).1).2=(ends ((eLOf S hS).symm i₂).1).2 :=
        Fin.ext (by simp only [ends];exact congrArg (fun x=>n+x.val) heq)
      rw [this];simp [vertices]
    exact Finset.disjoint_left.1 hdisj hv1 hv2
  let permOf:∀ (S:Finset (Fin m)) (hS:S ∈ Mset),Equiv.Perm (Fin n) :=
    fun S hS=>Equiv.ofBijective (fun i:Fin n=>(ones.get ((eLOf S hS).symm i).1).2) (hbijR S hS)
  refine Finset.card_bij permOf ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    intro i
    set e:=(eLOf S hS).symm i
    have hi:(ones.get e.1).1=i:=(eLOf S hS).apply_symm_apply i
    have hmem:ones.get e.1 ∈ ones:=List.get_mem ones e.1
    have hA:=(hmem_ones (ones.get e.1)).1 hmem
    change A i (ones.get e.1).2=true
    rw [← hi];exact hA
  · intro S₁ hS₁ S₂ hS₂ heq
    ext e
    have hmem_iff:∀ (S:Finset (Fin m)) (hS:S ∈ Mset) (e:Fin m),
        e ∈ S↔(ones.get e).2=permOf S hS (ones.get e).1:=by
      intro S hS e
      constructor
      · intro heS
        have hsym:(eLOf S hS).symm (ones.get e).1=⟨e,heS⟩ :=
          (eLOf S hS).symm_apply_apply ⟨e,heS⟩
        change (ones.get e).2=(ones.get ((eLOf S hS).symm (ones.get e).1).1).2
        rw [hsym]
      · intro hpair
        let x:=(eLOf S hS).symm (ones.get e).1
        have hx1:(ones.get x.1).1=(ones.get e).1:=(eLOf S hS).apply_symm_apply (ones.get e).1
        have hx2:(ones.get x.1).2=(ones.get e).2:=hpair.symm
        have hgeteq:ones.get x.1=ones.get e:=Prod.ext hx1 hx2
        have hexeq:x.1=e:=(List.nodup_iff_injective_get.1 hones_nodup) hgeteq
        rw [← hexeq]
        exact x.2
    rw [hmem_iff S₁ hS₁ e,hmem_iff S₂ hS₂ e,heq]
  · intro σ hσ
    have hσA:∀ i,A i (σ i)=true:=(Finset.mem_filter.1 hσ).2
    have hex:∀ i:Fin n,∃ e:Fin m,ones.get e=(i,σ i):=by
      intro i
      have hmem:(i,σ i) ∈ ones:=(hmem_ones (i,σ i)).2 (hσA i)
      exact List.mem_iff_get.1 hmem
    let emb:Fin n → Fin m:=fun i=>Classical.choose (hex i)
    have hemb:∀ i,ones.get (emb i)=(i,σ i):=fun i=>Classical.choose_spec (hex i)
    have hemb_inj:Function.Injective emb:=by
      intro i₁ i₂ h
      have h1:=congrArg (fun e=>(ones.get e).1) h
      rw [hemb i₁,hemb i₂] at h1
      exact h1
    let S:Finset (Fin m):=Finset.univ.image emb
    have hScard:S.card=n:=by
      rw [Finset.card_image_of_injective _ hemb_inj,Finset.card_univ,Fintype.card_fin]
    have hSmatch:matching S:=by
      intro e₁ he₁ e₂ he₂ hne
      rcases Finset.mem_image.1 he₁ with ⟨i₁,_,rfl⟩
      rcases Finset.mem_image.1 he₂ with ⟨i₂,_,rfl⟩
      have hi_ne:i₁≠i₂:=fun h=>hne (by rw [h])
      rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      simp only [vertices,ends,hemb,Finset.mem_insert,Finset.mem_singleton] at hv₁ hv₂
      have hi1:=i₁.isLt;have hi2:=i₂.isLt
      have hs1:=(σ i₁).isLt;have hs2:=(σ i₂).isLt
      rcases hv₁ with rfl | rfl <;> rcases hv₂ with h | h
      · exact hi_ne (Fin.ext (by simpa using congrArg Fin.val h))
      · have:=congrArg Fin.val h;simp at this;omega
      · have:=congrArg Fin.val h;simp at this;omega
      · have hv:=congrArg Fin.val h;simp at hv
        exact hi_ne (σ.injective (Fin.ext (by omega)))
    have hSM:S ∈ Mset:=Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _,hSmatch⟩,hScard⟩
    refine ⟨S,hSM,?_⟩
    ext i
    have hmem_e:emb i ∈ S:=Finset.mem_image.2 ⟨i,Finset.mem_univ _,rfl⟩
    have heq_e:eLOf S hSM ⟨emb i,hmem_e⟩=i:=by
      change (ones.get (emb i)).1=i;rw [hemb]
    have hsym:(eLOf S hSM).symm i=⟨emb i,hmem_e⟩ :=
      (congrArg (eLOf S hSM).symm heq_e.symm).trans ((eLOf S hSM).symm_apply_apply ⟨emb i,hmem_e⟩)
    change ((ones.get ((eLOf S hSM).symm i).1).2).val=(σ i).val
    rw [hsym,hemb]
lemma math_bridge (n:ℕ) (hn:0 < n) (A:Fin n → Fin n → Bool) :
    let B:Matrix (Fin n) (Fin n) ℕ := fun i j=>(A i j).toNat
    let cells:=(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
    let ones:=cells.filter (fun z=>A z.1 z.2)
    let rows:=ones.zipIdx.flatMap (fun z=>let p:=2 * n+2 * z.2
      [[p,p+1,z.1.1.val],[p,p+1,n+z.1.2.val]])
    let size:=fun t:Fin (n+1)=>2 * n+2 * ones.length+t.val
    let Z:=fun t:Fin (n+1)=>let k:=size t
      let Fn:=(Fin k → Bool) → (Fin k → Bool) → Bool
      Nat.card {f:Fn // (∃ C:PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C∧C.size+1 ≤ 2 * k ∧
        PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C ∧
        ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y)) ∧
        ∀ R ∈ rows,f (fun i=>decide (i.val ∈ R)) (fun _=>false)=true}
    let J:Matrix (Fin (n+1)) (Fin (n+1)) ℤ := fun t j=>(q11 (t.val+2 * j.val):ℤ)
    let delta:=(2:ℤ) ^ (n * (n+1) / 2) * ∏ j:Fin (n+1),(j.val.factorial:ℤ)
    rows.length=2 * ones.length ∧
    (∀ R ∈ rows,R.length=3∧R.Nodup) ∧
    (∀ t,0 < Z t) ∧
    J.det=delta ∧
    (J.updateCol 0 (fun t=>(Z t:ℤ))).det=delta * 2 ^ n * (B.permanent:ℤ) ∧
    q27 n (fun t=>if h:t < n+1 then (Z ⟨t,h⟩:ℤ) else 0) =
      (2:ℤ) ^ (2 * n) * (n.factorial:ℤ) * (B.permanent:ℤ):=by
  intro B cells ones rows size Z J delta
  have hcells_nodup:cells.Nodup:=by
    dsimp only [cells]
    rw [List.nodup_flatMap]
    refine ⟨fun i _=>(List.nodup_finRange n).map (fun j₁ j₂ h=>(Prod.mk.inj h).2),?_⟩
    exact (List.nodup_finRange n).imp fun {i₁ i₂} hne=>by
      intro x hx₁ hx₂
      simp only [List.mem_map] at hx₁ hx₂
      rcases hx₁ with ⟨_,_,rfl⟩
      rcases hx₂ with ⟨_,_,h⟩
      exact hne (Prod.mk.inj h).1.symm
  have hones_nodup:ones.Nodup:=hcells_nodup.filter _
  have hmem_cells:∀ z:Fin n × Fin n,z ∈ cells:=by
    intro ⟨i,j⟩
    simp only [cells,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
    exact ⟨i,j,rfl⟩
  have hmem_ones:∀ z:Fin n × Fin n,z ∈ ones↔A z.1 z.2=true:=by
    intro z;simp [ones,hmem_cells]
  have hrows_len:rows.length=2 * ones.length:=by
    dsimp only [rows]
    rw [List.length_flatMap]
    have:(ones.zipIdx.map fun z=>([[2 * n+2 * z.2,2 * n+2 * z.2+1,z.1.1.val],
        [2 * n+2 * z.2,2 * n+2 * z.2+1,n+z.1.2.val]]:List (List ℕ)).length) =
        List.replicate ones.length 2:=by
      apply List.ext_getElem (by simp)
      intro i hi₁ hi₂
      simp
    rw [this,List.sum_replicate,smul_eq_mul,mul_comm]
  have hrows_3:∀ R ∈ rows,R.length=3∧R.Nodup:=by
    intro R hR
    simp only [rows,List.mem_flatMap,List.mem_cons,List.mem_nil_iff,or_false] at hR
    rcases hR with ⟨⟨⟨i,j⟩,idx⟩,_,rfl | rfl⟩
    · refine ⟨rfl,?_⟩
      have hi:=i.isLt
      refine List.nodup_cons.2 ⟨?_,List.nodup_cons.2 ⟨?_,List.nodup_singleton _⟩⟩
      · simp only [List.mem_cons,List.mem_nil_iff,or_false];omega
      · simp only [List.mem_cons,List.mem_nil_iff,or_false];omega
    · refine ⟨rfl,?_⟩
      have hj:=j.isLt
      refine List.nodup_cons.2 ⟨?_,List.nodup_cons.2 ⟨?_,List.nodup_singleton _⟩⟩
      · simp only [List.mem_cons,List.mem_nil_iff,or_false];omega
      · simp only [List.mem_cons,List.mem_nil_iff,or_false];omega
  let m:=ones.length
  let ends:Fin m → Fin (2 * n) × Fin (2 * n):=fun e =>
    (⟨(ones.get e).1.val,by have:=(ones.get e).1.isLt;omega⟩,
     ⟨n+(ones.get e).2.val,by have:=(ones.get e).2.isLt;omega⟩)
  have hends:∀ e:Fin m,(ends e).1≠(ends e).2:=by
    intro e h
    have hv:=congrArg Fin.val h
    simp only [ends] at hv
    have:=(ones.get e).1.isLt
    omega
  have h913:=L9_thm (2 * n) m ends hends
  dsimp only at h913
  let vertices:Fin m → Finset (Fin (2 * n)):=fun e=>{(ends e).1,(ends e).2}
  let matching:Finset (Fin m) → Prop :=
    fun S=>∀ e ∈ S,∀ g ∈ S,e≠g → Disjoint (vertices e) (vertices g)
  let tests:Finset (Finset ℕ):=Finset.univ.image (fun z:Fin m × Bool =>
    ({2 * n+2 * z.1.val,2 * n+2 * z.1.val+1,
      if z.2 then (ends z.1).2.val else (ends z.1).1.val}:Finset ℕ))
  have hrows_tests:∀ (R:List ℕ),R ∈ rows → ∃ T ∈ tests,∀ x,x ∈ R↔x ∈ T:=by
    intro R hR
    simp only [rows,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with ⟨⟨z,idx⟩,hmem,hR'⟩
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    have hlt:idx < m:=by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hmem
      simp at hmem
    have hget:ones.get ⟨idx,hlt⟩=z:=by
      rw [List.getElem?_eq_getElem hlt] at hmem
      exact Option.some.inj hmem
    rcases hR' with rfl | rfl
    · refine ⟨{2 * n+2 * idx,2 * n+2 * idx+1,(ends ⟨idx,hlt⟩).1.val},?_,?_⟩
      · exact Finset.mem_image.2 ⟨(⟨idx,hlt⟩,false),Finset.mem_univ _,rfl⟩
      · intro x
        simp only [ends,hget,List.mem_cons,List.not_mem_nil,or_false,
          Finset.mem_insert,Finset.mem_singleton]
    · refine ⟨{2 * n+2 * idx,2 * n+2 * idx+1,(ends ⟨idx,hlt⟩).2.val},?_,?_⟩
      · exact Finset.mem_image.2 ⟨(⟨idx,hlt⟩,true),Finset.mem_univ _,rfl⟩
      · intro x
        simp only [ends,hget,List.mem_cons,List.not_mem_nil,or_false,
          Finset.mem_insert,Finset.mem_singleton]
  have htests_rows:∀ T ∈ tests,∃ R ∈ rows,∀ x,x ∈ R↔x ∈ T:=by
    intro T hT
    rcases Finset.mem_image.1 hT with ⟨⟨e,b⟩,_,rfl⟩
    have hmem:(ones.get e,e.val) ∈ ones.zipIdx:=by
      rw [List.mem_zipIdx_iff_getElem?]
      simp
    cases b with
    | false =>
      refine ⟨[2 * n+2 * e.val,2 * n+2 * e.val+1,(ones.get e).1.val],?_,?_⟩
      · simp only [rows,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
        exact ⟨(ones.get e,e.val),hmem,Or.inl rfl⟩
      · intro x;simp [ends]
    | true =>
      refine ⟨[2 * n+2 * e.val,2 * n+2 * e.val+1,n+(ones.get e).2.val],?_,?_⟩
      · simp only [rows,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
        exact ⟨(ones.get e,e.val),hmem,Or.inr rfl⟩
      · intro x;simp [ends]
  have hZ_eq_913:∀ t:Fin (n+1),
      0 < Z t∧Z t=(Finset.univ.filter matching).sum (fun S=>2 ^ S.card * q11 (2 * n+t.val - 2 * S.card)):=by
    intro t
    have ht913:=h913.2.2 t.val
    let k:=size t
    have hk2:2 ≤ k:=by dsimp only [k,size];omega
    let wins:Equiv.Perm (Fin k) → Prop:=fun P =>
      Function.Involutive P∧∀ T ∈ tests,∃ u:Fin k,u.val ∈ T∧(P u).val ∈ T∧P u≠u
    let eZ:{P:Equiv.Perm (Fin k) // wins P} ≃
        {f:(Fin k → Bool) → (Fin k → Bool) → Bool //
          (∃ C:PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 C∧C.size+1 ≤ 2 * k ∧
            PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C ∧
            ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y)) ∧
          ∀ R ∈ rows,f (fun i=>decide (i.val ∈ R)) (fun _=>false)=true} :=
      { toFun:=fun ⟨P,hPinv,hPwin⟩ =>
          ⟨fnOf P,
            (L8_thm k hk2 (fnOf P)).2
              ⟨P,⟨hPinv,fun _ _=>rfl⟩,fun Q ⟨hQinv,hQeq⟩ =>
                (q164 hPinv hQinv (funext fun x=>funext fun y=>hQeq x y)).symm⟩,
            fun R hR=>by
              rcases hrows_tests R hR with ⟨T,hT,hRT⟩
              rcases hPwin T hT with ⟨u,huT,hPuT,hne⟩
              simp only [fnOf,decide_eq_true_eq]
              exact ⟨u,Or.inr ⟨hne,Or.inl ⟨(hRT u.val).2 huT,(hRT (P u).val).2 hPuT⟩⟩⟩⟩
        invFun:=fun ⟨f,hfC,hfR⟩ =>
          have hex:∃! P:Equiv.Perm (Fin k),Function.Involutive P ∧
              ∀ x y,f x y=fnOf P x y:=(L8_thm k hk2 f).1 hfC
          let P:=Classical.choose hex
          have hP:Function.Involutive P∧∀ x y,f x y=fnOf P x y:=(Classical.choose_spec hex).1
          ⟨P,hP.1,fun T hT=>by
            rcases htests_rows T hT with ⟨R,hR,hRT⟩
            have h1:=hfR R hR
            rw [hP.2] at h1
            simp only [fnOf,decide_eq_true_eq] at h1
            rcases h1 with ⟨u,⟨_,hfalse⟩ | ⟨hne,⟨hu,hPu⟩ | ⟨hfalse,_⟩⟩⟩
            · exact (Bool.false_ne_true hfalse).elim
            · exact ⟨u,(hRT u.val).1 hu,(hRT (P u).val).1 hPu,hne⟩
            · exact (Bool.false_ne_true hfalse).elim⟩
        left_inv:=fun ⟨P,hPinv,hPwin⟩=>by
          apply Subtype.ext
          have hex:=(L8_thm k hk2 (fnOf P)).1
            ((L8_thm k hk2 (fnOf P)).2
              ⟨P,⟨hPinv,fun _ _=>rfl⟩,fun Q ⟨hQinv,hQeq⟩ =>
                (q164 hPinv hQinv (funext fun x=>funext fun y=>hQeq x y)).symm⟩)
          have hspec:=(Classical.choose_spec hex).1
          exact q164 hspec.1 hPinv (funext fun x=>funext fun y=>(hspec.2 x y).symm)
        right_inv:=fun ⟨f,hfC,hfR⟩=>by
          apply Subtype.ext
          have hex:=(L8_thm k hk2 f).1 hfC
          have hspec:=(Classical.choose_spec hex).1
          exact funext fun x=>funext fun y=>(hspec.2 x y).symm }
    have hcard:Z t=Nat.card {P:Equiv.Perm (Fin k) // wins P}:=(Nat.card_congr eZ).symm
    rw [hcard]
    exact ⟨ht913.2.1,ht913.2.2⟩
  have hmatch_le:∀ S:Finset (Fin m),matching S → S.card ≤ n:=by
    intro S hS
    have hinj:Set.InjOn (fun e:Fin m=>(ones.get e).1) (S:Set (Fin m)):=by
      intro e₁ he₁ e₂ he₂ heq
      by_contra hne
      have hdisj:=hS e₁ he₁ e₂ he₂ hne
      have hv1:(ends e₁).1 ∈ vertices e₁:=by simp [vertices]
      have hv2:(ends e₁).1 ∈ vertices e₂:=by
        have:(ends e₁).1=(ends e₂).1:=Fin.ext (by dsimp only [ends];exact congrArg Fin.val heq)
        rw [this];simp [vertices]
      exact Finset.disjoint_left.1 hdisj hv1 hv2
    calc S.card=(S.image (fun e:Fin m=>(ones.get e).1)).card:=(Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ:Finset (Fin n)).card:=Finset.card_le_card (Finset.subset_univ _)
      _=n:=Fintype.card_fin n
  let x:Fin (n+1) → ℕ := fun j =>
    ((Finset.univ.filter matching).filter (fun S=>n - S.card=j.val)).sum (fun S=>2 ^ S.card)
  have hZ_lin:∀ t:Fin (n+1),
      (Z t:ℤ)=∑ j:Fin (n+1),(q11 (t.val+2 * j.val):ℤ) * (x j:ℤ):=by
    intro t
    rw [(hZ_eq_913 t).2]
    have hnat:(Finset.univ.filter matching).sum (fun S=>2 ^ S.card * q11 (2 * n+t.val - 2 * S.card)) =
        ∑ j:Fin (n+1),q11 (t.val+2 * j.val) * x j:=by
      have hpart:=Finset.sum_fiberwise_of_maps_to
        (s:=Finset.univ.filter matching)
        (t:=(Finset.univ:Finset (Fin (n+1))))
        (g:=fun S:Finset (Fin m)=>(⟨n - S.card,by omega⟩:Fin (n+1)))
        (f:=fun S=>2 ^ S.card * q11 (2 * n+t.val - 2 * S.card))
        (fun _ _=>Finset.mem_univ _)
      rw [← hpart]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [x]
      rw [Finset.mul_sum]
      have hfilt:(Finset.univ.filter matching).filter
            (fun S=>(⟨n - S.card,by omega⟩:Fin (n+1))=j) =
          (Finset.univ.filter matching).filter (fun S=>n - S.card=j.val):=by
        ext S;simp [Fin.ext_iff]
      rw [hfilt]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hS':=Finset.mem_filter.1 hS
      have hle:=hmatch_le S (Finset.mem_filter.1 hS'.1).2
      have hj:n - S.card=j.val:=hS'.2
      have heq:2 * n+t.val - 2 * S.card=t.val+2 * j.val:=by omega
      rw [heq,mul_comm]
    exact_mod_cast hnat
  have hx0:x ⟨0,Nat.succ_pos n⟩=2 ^ n * B.permanent:=by
    dsimp only [x]
    have hfilt_eq:(Finset.univ.filter matching).filter (fun S=>n - S.card=0) =
        (Finset.univ.filter matching).filter (fun S=>S.card=n):=by
      ext S
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro ⟨hM,h0⟩;have:=hmatch_le S hM;exact ⟨hM,by omega⟩
      · intro ⟨hM,h0⟩;exact ⟨hM,by omega⟩
    rw [hfilt_eq]
    have hsum_const:((Finset.univ.filter matching).filter (fun S=>S.card=n)).sum (fun S=>2 ^ S.card) =
        2 ^ n * ((Finset.univ.filter matching).filter (fun S=>S.card=n)).card:=by
      rw [Finset.sum_congr rfl (fun S hS=>by rw [(Finset.mem_filter.1 hS).2]),
        Finset.sum_const,smul_eq_mul,mul_comm]
    rw [hsum_const]
    congr 1
    exact q51 n A ones hones_nodup hmem_ones
  have hJdet:J.det=delta:=by
    have h914:=L4.exact_involution_matrix_det n 0 (by omega)
    dsimp only [delta]
    rw [← h914]
    congr 1
    ext t j
    simp only [J,Matrix.of_apply]
    have heq:(t.val:ℕ)+(0+2 * j.val)=t.val+2 * j.val:=by omega
    rw [heq]
    rfl
  have hupd_det:(J.updateCol 0 (fun t=>(Z t:ℤ))).det=delta * 2 ^ n * (B.permanent:ℤ):=by
    have hZeq:(fun t=>(Z t:ℤ))=fun t=>∑ j:Fin (n+1),(x j:ℤ) * J t j:=by
      funext t;rw [hZ_lin t]
      refine Finset.sum_congr rfl fun j _=>by simp [J,mul_comm]
    rw [hZeq,q76 J (fun j=>(x j:ℤ)),hJdet]
    have hx0':x 0=2 ^ n * B.permanent:=hx0
    rw [hx0']
    push_cast;ring
  have hdec:q27 n (fun t=>if h:t < n+1 then (Z ⟨t,h⟩:ℤ) else 0) =
      (2:ℤ) ^ (2 * n) * (n.factorial:ℤ) * (B.permanent:ℤ):=by
    have hspec:=q106 n (fun j=>(x j:ℤ))
      (fun t=>if h:t < n+1 then (Z ⟨t,h⟩:ℤ) else 0)
      (fun t=>by simp [t.isLt,hZ_lin t])
    rw [hspec,hx0]
    have hpow:(2:ℤ) ^ n * (2:ℤ) ^ n=(2:ℤ) ^ (2 * n):=by
      rw [← pow_add];congr 1;omega
    push_cast
    calc (2:ℤ) ^ n * (n.factorial:ℤ) * ((2:ℤ) ^ n * (B.permanent:ℤ))
        = ((2:ℤ) ^ n * (2:ℤ) ^ n) * (n.factorial:ℤ) * (B.permanent:ℤ):=by ring
      _=(2:ℤ) ^ (2 * n) * (n.factorial:ℤ) * (B.permanent:ℤ):=by rw [hpow]
  exact ⟨hrows_len,hrows_3,fun t=>(hZ_eq_913 t).1,hJdet,hupd_det,hdec⟩
abbrev CPTs (f:List Bool → List Bool):Prop :=
  ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
def q22 {K:Type} {Γ : K → Type} {Λ σ : Type}:Turing.TM2.Stmt Γ Λ σ → Set (Σ k,Γ k)
  | .push k g q=>Set.range (fun v=>(⟨k,g v⟩ : Σ k,Γ k)) ∪ q22 q
  | .peek _ _ q=>q22 q
  | .pop _ _ q=>q22 q
  | .load _ q=>q22 q
  | .branch _ q₁ q₂=>q22 q₁ ∪ q22 q₂
  | .goto _ => ∅
  | .halt => ∅
lemma q110 {K:Type} {Γ : K → Type} {Λ σ : Type} [Finite σ]
    (q:Turing.TM2.Stmt Γ Λ σ):(q22 q).Finite:=by
  induction q with
  | push _ _ _ ih=>exact (Set.finite_range _).union ih
  | peek _ _ _ ih=>exact ih
  | pop _ _ _ ih=>exact ih
  | load _ _ ih=>exact ih
  | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
  | goto _=>exact Set.finite_empty
  | halt=>exact Set.finite_empty
def q29 {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T:∀ k,Set (Γ k)) :
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩ : Σ j,Γ j) ∈ q22 q → s ∈ T k) →
    Turing.TM2.Stmt (fun k=>{s : Γ k // s ∈ T k}) Λ σ
  | .push k g q,h => .push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
      (q29 T q (fun j s hs=>h j s (Or.inr hs)))
  | .peek k f q,h => .peek k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
  | .pop k f q,h => .pop k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
  | .load a q,h => .load a (q29 T q h)
  | .branch f q₁ q₂,h => .branch f
      (q29 T q₁ (fun j s hs=>h j s (Or.inl hs)))
      (q29 T q₂ (fun j s hs=>h j s (Or.inr hs)))
  | .goto f,_ => .goto f
  | .halt,_ => .halt
def q67 {K:Type} {Γ : K → Type} {Λ σ : Type} (T:∀ k,Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s : Γ k // s ∈ T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
  ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma q181 {K:Type} {Γ : K → Type} {Λ σ : Type} (T:∀ k,Set (Γ k)) :
    Function.Injective (q67 (Λ := Λ) (σ := σ) T):=by
  rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
  simp only [q67,Turing.TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl,rfl,hS⟩:=h
  congr 1
  funext k
  exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma q84 {K:Type} [DecidableEq K] {Γ : K → Type} (T:∀ k,Set (Γ k))
    (S:∀ k,List {s : Γ k // s ∈ T k}) (k:K) (l:List {s : Γ k // s ∈ T k}) :
    (fun j=>(Function.update S k l j).map Subtype.val) =
      Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
  funext j
  by_cases h:j=k
  · subst h;simp
  · simp [h]
lemma q125 {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
    (hq:∀ k s,(⟨k,s⟩ : Σ j,Γ j) ∈ q22 q → s ∈ T k)
    (v : σ) (S:∀ k,List {s : Γ k // s ∈ T k}) :
    q67 T (Turing.TM2.stepAux (q29 T q hq) v S) =
      Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
  induction q generalizing v S with
  | push k g q ih =>
    simp only [q29,Turing.TM2.stepAux]
    rw [ih,q84];rfl
  | peek k f q ih =>
    simp only [q29,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [List.head?_map])
  | pop k f q ih =>
    simp only [q29,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [q84,List.head?_map,List.map_tail])
  | load a q ih =>
    simp only [q29,Turing.TM2.stepAux]
    exact ih hq (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [q29,Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ v S
    · exact ih₁ _ v S
  | goto f=>rfl
  | halt=>rfl
lemma cpt_to_fast {f:List Bool → List Bool} (hf:CPTs f) :
    ∃ M:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f,
      ∀ i,Finite (M.tm.Γ i):=by
  classical
  obtain ⟨c⟩:=hf
  let _:DecidableEq c.tm.K:=c.tm.kDecidableEq
  let _:Fintype c.tm.K:=c.tm.kFin
  let _:Fintype c.tm.Λ := c.tm.ΛFin
  let _:Fintype c.tm.σ := c.tm.σFin
  let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
  let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k =>
    {s | k=c.tm.k₀∨k=c.tm.k₁∨(⟨k,s⟩ : Σ j,c.tm.Γ j) ∈ ⋃ l:c.tm.Λ,q22 (c.tm.m l)}
  let e₀:{s:c.tm.Γ c.tm.k₀ // s ∈ T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀ :=
    { toFun:=Subtype.val
      invFun:=fun s=>⟨s,Or.inl rfl⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let e₁:{s:c.tm.Γ c.tm.k₁ // s ∈ T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁ :=
    { toFun:=Subtype.val
      invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s ∈ T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
  let tm':Turing.FinTM2 :=
    { K:=c.tm.K
      kDecidableEq:=c.tm.kDecidableEq
      kFin:=c.tm.kFin
      k₀:=c.tm.k₀
      k₁:=c.tm.k₁
      Γ := fun k=>{s:c.tm.Γ k // s ∈ T k}
      Λ := c.tm.Λ
      main:=c.tm.main
      ΛFin:=c.tm.ΛFin
      σ := c.tm.σ
      initialState:=c.tm.initialState
      σFin:=c.tm.σFin
      Γk₀Fin:=hΓ0Fin
      m:=fun l=>q29 T (c.tm.m l) (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
  have hFin:∀ j:tm'.K,Finite (tm'.Γ j):=by
    intro j
    by_cases h0:j=c.tm.k₀
    · subst h0;exact Finite.of_fintype _
    · by_cases h1:j=c.tm.k₁
      · subst h1
        have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin:(⋃ l:c.tm.Λ,q22 (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l=>q110 (c.tm.m l)
        have:Finite ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)):=hUfin.to_subtype
        refine Finite.of_injective (f:=fun x:tm'.Γ j =>
            (⟨⟨j,x.1⟩,by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩ : ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)))) ?_
        intro x y hxy
        have h1':=congrArg (fun z=>z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep:∀ cfg:tm'.Cfg,Option.map (q67 T) (tm'.step cfg)=c.tm.step (q67 T cfg):=by
    rintro ⟨l,v,S⟩
    cases l with
    | none=>rfl
    | some l =>
      change some (q67 T (Turing.TM2.stepAux (q29 T (c.tm.m l) _) v S)) =
        some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
      exact congrArg some (q125 T (c.tm.m l) _ v S)
  have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
      Option.map (q67 T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (q67 T cfg)):=by
    intro steps
    induction steps with
    | zero=>intro cfg;rfl
    | succ steps ih =>
      intro cfg
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
      | none =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih];rfl
      | some cfg' =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]
        exact hstep cfg'
  let M:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f :=
    { tm:=tm'
      inputAlphabet:=e₀.trans c.inputAlphabet
      outputAlphabet:=e₁.trans c.outputAlphabet
      time:=c.time
      outputsFun:=fun a =>
        { steps:=(c.outputsFun a).steps
          evals_in_steps:=by
            have horig:=(c.outputsFun a).evals_in_steps
            have hinit:q67 T (Turing.initList tm' (a.map (e₀.trans c.inputAlphabet).invFun)) =
                Turing.initList c.tm (a.map c.inputAlphabet.invFun):=by
              simp only [q67,Turing.initList]
              congr 1;funext k
              by_cases hk:k=c.tm.k₀
              · subst hk;dsimp only [tm']
                simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
              · dsimp only [tm']
                simp only [hk,↓reduceDIte,List.map_nil]
            have hhalt:q67 T (Turing.haltList tm' ((f a).map (e₁.trans c.outputAlphabet).invFun)) =
                Turing.haltList c.tm ((f a).map c.outputAlphabet.invFun):=by
              simp only [q67,Turing.haltList]
              congr 1;funext k
              by_cases hk:k=c.tm.k₁
              · subst hk;dsimp only [tm']
                simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
              · dsimp only [tm']
                simp only [hk,↓reduceDIte,List.map_nil]
            apply Option.map_injective (q181 T)
            rw [hiter,hinit,horig]
            exact (congrArg some hhalt).symm
          steps_le_m:=(c.outputsFun a).steps_le_m } }
  exact ⟨M,hFin⟩
lemma q39 {f g:List Bool → List Bool} (hf:CPTs f) (h:∀ x,f x=g x):CPTs g:=by
  have:f=g:=funext h
  rwa [← this]
lemma q157:CPTs (fun s:List Bool=>s.reverse):=⟨Rev.reverseComputable⟩
lemma q121 {g cnt arg:List Bool → List Bool} (k:ℕ)
    (hg:CPTs g) (hgl:∀ s,(g s).length ≤ s.length+k)
    (hcnt:CPTs cnt) (harg:CPTs arg) :
    CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c k hgl
  exact q39 (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
lemma q213 {g cnt arg:List Bool → List Bool}
    (m:List Bool → ℕ) (a:ℕ)
    (hg:CPTs g)
    (hm:∀ y,m (g y) ≤ m y)
    (hgl:∀ y,(g y).length ≤ y.length+m y)
    (ha:∀ y,m y ≤ a * y.length+a)
    (hcnt:CPTs cnt) (harg:CPTs arg) :
    CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure g c m a hm hgl ha
  exact q39 (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
lemma q7 (a b:List Bool):(pairB a b).length=2 * a.length+b.length+1:=by
  simp [pairB,un];omega
lemma q0 (y:List Bool) :
    2 * (unpairB y).1.length+(unpairB y).2.length ≤ y.length:=by
  dsimp only [unpairB]
  have hsplit:y=y.takeWhile id++y.dropWhile id:=(List.takeWhile_append_dropWhile (p:=id) (l:=y)).symm
  have hylen:y.length=(y.takeWhile id).length+(y.dropWhile id).length:=by
    conv_lhs=>rw [hsplit]
    exact List.length_append
  set a:=(y.takeWhile id).length
  set t:=(y.dropWhile id).tail
  have htlen:t.length ≤ (y.dropWhile id).length:=by
    dsimp only [t];cases y.dropWhile id <;> simp
  have htake:(t.take a).length=min a t.length:=List.length_take
  have hdrop:(t.drop a).length=t.length - a:=List.length_drop
  omega
lemma q18 {g cnt arg:List Bool → List Bool} (c:ℕ)
    (hg:CPTs g)
    (hw:∀ y,(unpairB (g y)).1=(unpairB y).1)
    (hgl:∀ y,(g y).length ≤ y.length+c * (unpairB y).1.length+c)
    (hcnt:CPTs cnt) (harg:CPTs arg) :
    CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
  refine q213 (fun y=>c * (unpairB y).1.length+c) c hg
    (fun y=>by rw [hw y])
    (fun y=>by have:=hgl y;omega)
    (fun y=>by
      have h1:(unpairB y).1.length ≤ y.length:=by have:=q0 y;omega
      have h2:=Nat.mul_le_mul_left c h1
      omega)
    hcnt harg
def q47 (s:List Bool):List Bool:=List.replicate s.length true
lemma q152 (s:List Bool):(q47 s).length=s.length:=List.length_replicate
lemma q89:CPTs q47 :=
  fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some true)) (fun _=>none) () (fun s=>by
    induction s with
    | nil=>rfl
    | cons b l ih=>simp only [fstRun,q47,List.length_cons,List.replicate_succ];exact congrArg (true :: ·) ih)
def q79 (s:List Bool):List Bool :=
  pairB (unpairB s).1 ((unpairB s).2++(unpairB s).1)
lemma q169:CPTs q79 :=
  cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 cpt_unpairB1)
lemma q99 (a:List Bool):∀ k b,q79^[k] (pairB (q47 a) b)=pairB (q47 a) (b++un (k * a.length))
  | 0,b=>by simp [un]
  | k+1,b=>by
    rw [Function.iterate_succ_apply,q79,unpairB_pairB,q99 a k (b++q47 a)]
    congr 1
    simp [q47,un,List.append_assoc,← List.replicate_add,Nat.succ_mul,Nat.add_comm]
lemma q42 {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
    CPTs (fun s=>mulU (u s) (v s)):=by
  have h1:CPTs (fun s=>q79^[(u s).length] (pairB (q47 (v s)) [])) :=
    q18 1 q169 (fun y=>by rw [q79,unpairB_pairB])
      (fun y=>by
        rw [q79,q7,List.length_append]
        have:=q0 y
        omega)
      hu (cpt_pairB2 (cpt_comp hv q89) (cpt_const []))
  have h2:=cpt_comp h1 cpt_unpairB2
  have heq:(fun s=>(unpairB (q79^[(u s).length] (pairB (q47 (v s)) []))).2)=(fun s=>mulU (u s) (v s)):=by
    funext s
    rw [q99,unpairB_pairB,List.nil_append];rfl
  rwa [heq] at h2
def q17 (s:List Bool):List Bool :=
  match s with
  | true :: _=>[true]
  | _=>[]
lemma q35:CPTs q17 :=
  fst_polyTime _ _ _
    (fun (st:Bool) (b:Bool)=>if st then (false,if b then some true else none) else (false,none))
    (fun _=>none) true (fun s=>by
      have hfalse:∀ l,fstRun (fun (st:Bool) (b:Bool) =>
          if st then (false,if b then some true else none) else (false,none))
          (fun _=>none) false l=[]:=by
        intro l;induction l with | nil=>rfl | cons b l ih=>simp [fstRun,ih]
      cases s with
      | nil=>rfl
      | cons b l=>cases b <;> simp [fstRun,q17,hfalse])
def q133 (s:List Bool):List Bool:=sel s [true] []
lemma q138:CPTs q133 :=
  cpt_sel cpt_id (cpt_const [true]) (cpt_const [])
def takeN (lenU xs:List Bool):List Bool :=
  (unpairB (q47 lenU++false :: xs)).1
def dropN' (lenU xs:List Bool):List Bool :=
  (unpairB (q47 lenU++false :: xs)).2
lemma q12 (lenU xs:List Bool):takeN lenU xs=xs.take lenU.length:=by
  have h1:(q47 lenU++false :: xs).takeWhile id=q47 lenU:=by
    simp [q47]
  have h2:(q47 lenU++false :: xs).dropWhile id=false :: xs:=by
    simp [q47]
  simp [takeN,unpairB,h1,h2,q152]
lemma q40 (lenU xs:List Bool):dropN' lenU xs=xs.drop lenU.length:=by
  have h1:(q47 lenU++false :: xs).takeWhile id=q47 lenU:=by
    simp [q47]
  have h2:(q47 lenU++false :: xs).dropWhile id=false :: xs:=by
    simp [q47]
  simp [dropN',unpairB,h1,h2,q152]
lemma q24 {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
    CPTs (fun s=>takeN (u s) (v s)) :=
  q39 (cpt_comp (cpt_app2 (cpt_comp hu q89) (cpt_app2 (cpt_const [false]) hv)) cpt_unpairB1) (fun _=>rfl)
lemma cpt_dropN' {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
    CPTs (fun s=>dropN' (u s) (v s)) :=
  q39 (cpt_comp (cpt_app2 (cpt_comp hu q89) (cpt_app2 (cpt_const [false]) hv)) cpt_unpairB2) (fun _=>rfl)
def q23 (xs:List Bool):List Bool :=
  xs.flatMap (fun b=>[true,b])++[false]
lemma q171:CPTs q23 :=
  fst2_polyTime _ _ _ (fun (_:Unit) (b:Bool)=>((),some true,some b))
    (fun _=>some false) () (fun s=>by
      induction s with
      | nil=>rfl
      | cons b l ih=>simp [fstRun2,q23] at ih ⊢;exact ih)
def q15:Option Bool → List Bool → List Bool
  | none,_=>[]
  | some false,true :: r=>q15 (some true) r
  | some false,false :: _=>[]
  | some false,[]=>[]
  | some true,b :: r=>b :: q15 (some false) r
  | some true,[]=>[]
def q75 (s:List Bool):List Bool:=q15 (some false) s
def q10:Option Bool → List Bool → List Bool
  | none,r=>r
  | some false,true :: r=>q10 (some true) r
  | some false,false :: r=>r
  | some false,[]=>[]
  | some true,_ :: r=>q10 (some false) r
  | some true,[]=>[]
def q43 (s:List Bool):List Bool:=q10 (some false) s
lemma q101 (xs rest:List Bool) :
    q75 (q23 xs++rest)=xs:=by
  dsimp only [q75,q23]
  induction xs with
  | nil=>rfl
  | cons b l ih=>simp only [List.flatMap_cons,List.cons_append,List.nil_append,q15];exact congrArg (b :: ·) ih
lemma q100 (xs rest:List Bool) :
    q43 (q23 xs++rest)=rest:=by
  dsimp only [q43,q23]
  induction xs with
  | nil=>rfl
  | cons b l ih=>simp only [List.flatMap_cons,List.cons_append,List.nil_append,q10];exact ih
lemma q91 (s:List Bool):(q43 s).length ≤ s.length:=by
  have h:∀ st l,(q10 st l).length ≤ l.length:=by
    intro st l
    induction l generalizing st with
    | nil =>
      cases st with
      | none=>simp [q10]
      | some f=>cases f <;> simp [q10]
    | cons b r ih =>
      cases st with
      | none=>simp [q10]
      | some f =>
        cases f with
        | false =>
          cases b <;> simp only [q10,List.length_cons]
          · omega
          · have:=ih (some true);omega
        | true =>
          simp only [q10,List.length_cons]
          have:=ih (some false);omega
  exact h (some false) s
lemma q129:CPTs q75:=by
  let δ : Option Bool → Bool → Option Bool × Option Bool:=fun st b =>
    match st,b with
    | none,_=>(none,none)
    | some false,true=>(some true,none)
    | some false,false=>(none,none)
    | some true,b=>(some false,some b)
  refine fst_polyTime _ _ _ δ (fun _=>none) (some false) fun s => ?_
  have hnone:∀ l,fstRun δ (fun _=>none) none l=[]:=by
    intro l;induction l with | nil=>rfl | cons b l ih=>simp [fstRun,δ,ih]
  have haux:∀ st l,fstRun δ (fun _=>none) st l=q15 st l:=by
    intro st l
    induction l generalizing st with
    | nil=>cases st with | none=>rfl | some f=>cases f <;> rfl
    | cons b r ih =>
      cases st with
      | none=>simp [fstRun,δ,hnone,q15]
      | some f =>
        cases f with
        | false=>cases b <;> simp [fstRun,δ,q15,ih]
        | true=>simp [fstRun,δ,q15,ih]
  exact (haux (some false) s).symm
lemma q128:CPTs q43:=by
  let δ : Option Bool → Bool → Option Bool × Option Bool:=fun st b =>
    match st,b with
    | none,b=>(none,some b)
    | some false,true=>(some true,none)
    | some false,false=>(none,none)
    | some true,_=>(some false,none)
  refine fst_polyTime _ _ _ δ (fun _=>none) (some false) fun s => ?_
  have hnone:∀ l,fstRun δ (fun _=>none) none l=l:=by
    intro l;induction l with | nil=>rfl | cons b l ih=>simp [fstRun,δ,ih]
  have haux:∀ st l,fstRun δ (fun _=>none) st l=q10 st l:=by
    intro st l
    induction l generalizing st with
    | nil=>cases st with | none=>rfl | some f=>cases f <;> rfl
    | cons b r ih =>
      cases st with
      | none=>simp [fstRun,δ,hnone,q10]
      | some f =>
        cases f with
        | false=>cases b <;> simp [fstRun,δ,q10,ih]
        | true=>simp [fstRun,δ,q10,ih]
  exact (haux (some false) s).symm
def val:List Bool → ℕ
  | []=>0
  | b :: l=>b.toNat+2 * val l
lemma q124 (l:List Bool):val l < 2 ^ l.length:=by
  induction l with
  | nil=>simp [val]
  | cons b l ih =>
    simp only [val,List.length_cons,pow_succ]
    cases b <;> simp <;> omega
lemma q58 (a b:List Bool):val (a++b)=val a+2 ^ a.length * val b:=by
  induction a with
  | nil=>simp [val]
  | cons x l ih =>
    simp only [List.cons_append,val,List.length_cons,pow_succ,ih]
    ring
lemma q52 (k:ℕ):val (List.replicate k false)=0:=by
  induction k with
  | zero=>rfl
  | succ k ih=>simp [List.replicate_succ,val,ih]
lemma q37 (l:List Bool):val (blank l)=0:=by
  have h:blank l=List.replicate l.length false:=by
    induction l with
    | nil=>rfl
    | cons _ r ih=>simp [blank,List.replicate_succ,ih]
  rw [h,q52]
lemma q33 (l:List Bool):(blank l).length=l.length:=by
  induction l with
  | nil=>rfl
  | cons _ r ih=>simp [blank,ih]
lemma q140 (k:ℕ) (l:List Bool):val (l.take k)=val l % 2 ^ k:=by
  induction k generalizing l with
  | zero=>simp [val,Nat.mod_one]
  | succ k ih =>
    cases l with
    | nil=>simp [val]
    | cons b r =>
      simp only [List.take_succ_cons,val,ih,pow_succ']
      have hlt:b.toNat < 2:=by cases b <;> decide
      have hdiv:(b.toNat+2 * val r) % (2 * 2 ^ k)=b.toNat+2 * (val r % 2 ^ k):=by
        have h1:=Nat.div_add_mod (val r) (2 ^ k)
        have h2:val r % 2 ^ k < 2 ^ k:=Nat.mod_lt _ (by positivity)
        have h3:b.toNat+2 * val r=(2 * 2 ^ k) * (val r / 2 ^ k)+(b.toNat+2 * (val r % 2 ^ k)):=by
          linarith
        rw [h3,Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
      exact hdiv.symm
lemma q194 (n:ℕ):val n.bits=n:=by
  induction n using Nat.binaryRec with
  | zero=>simp [val]
  | bit b m ih =>
    by_cases h:b=false∧m=0
    · rcases h with ⟨rfl,rfl⟩;simp [val]
    · rw [Nat.bits_append_bit m b (fun hm=>by subst hm;cases b <;> simp_all)]
      simp only [val,ih,Nat.bit]
      cases b <;> simp <;> omega
lemma q175 (k:ℕ) (hk:0 < k):k.bits.length=k.log2+1:=by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases h2:k < 2
    · have hk1:k=1:=by omega
      subst hk1;decide
    · have hdiv_pos:0 < k / 2:=by omega
      have hdiv_lt:k / 2 < k:=Nat.div_lt_self hk (by omega)
      have hlog:k.log2=(k / 2).log2+1:=by
        rw [Nat.log2_def];simp [show 2 ≤ k by omega]
      have hbits:k.bits=(decide (k % 2=1)) :: (k / 2).bits:=by
        have hdecomp:k=Nat.bit (decide (k % 2=1)) (k / 2):=by
          cases hmod:k % 2 with
          | zero=>simp [Nat.bit];omega
          | succ r =>
            have hr:r=0:=by omega
            subst hr;simp [Nat.bit];omega
        conv_lhs=>rw [hdecomp]
        rw [Nat.bits_append_bit (k / 2) (decide (k % 2=1)) (fun h0=>by omega)]
      rw [hbits,List.length_cons,ih (k / 2) hdiv_lt hdiv_pos,hlog]
lemma q78 (z h:ℕ):z.testBit h=z.bits.getD h false:=by
  induction h generalizing z with
  | zero =>
    by_cases hz:z=0
    · subst hz;simp
    · have hdecomp:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
        cases hmod:z % 2 with
        | zero=>simp [Nat.bit];omega
        | succ r =>
          have hr:r=0:=by omega
          subst hr;simp [Nat.bit];omega
      have hbits:z.bits=(decide (z % 2=1)) :: (z / 2).bits:=by
        conv_lhs=>rw [hdecomp]
        refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0 => ?_
        have hmod1:z % 2=1:=by omega
        simp [hmod1]
      rw [hbits]
      simp [Nat.testBit_zero]
  | succ h ih =>
    by_cases hz:z=0
    · subst hz;simp
    · have hdecomp:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
        cases hmod:z % 2 with
        | zero=>simp [Nat.bit];omega
        | succ r =>
          have hr:r=0:=by omega
          subst hr;simp [Nat.bit];omega
      have hbits:z.bits=(decide (z % 2=1)) :: (z / 2).bits:=by
        conv_lhs=>rw [hdecomp]
        refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0 => ?_
        have hmod1:z % 2=1:=by omega
        simp [hmod1]
      rw [hbits,List.getD_cons_succ,← ih (z / 2),Nat.testBit_succ]
def q28:List Bool → List Bool
  | []=>[true]
  | false :: l=>true :: l
  | true :: l=>false :: q28 l
lemma q182 (l:List Bool):val (q28 l)=val l+1:=by
  induction l with
  | nil=>simp [q28,val]
  | cons b l ih=>cases b <;> simp [q28,val,ih] <;> omega
lemma q183 (l:List Bool):(q28 l).length ≤ l.length+1:=by
  induction l with
  | nil=>simp [q28]
  | cons b l ih=>cases b <;> simp [q28] <;> omega
lemma q163 (n:ℕ):q28 n.bits=(n+1).bits:=by
  induction n using Nat.binaryRec with
  | zero=>decide
  | bit b m ih =>
    cases b with
    | false =>
      by_cases hm:m=0
      · subst hm;decide
      · have h1:(Nat.bit false m).bits=false :: m.bits :=
          Nat.bits_append_bit m false (fun h=>(hm h).elim)
        have h2:Nat.bit false m+1=Nat.bit true m:=by simp [Nat.bit]
        have h3:(Nat.bit true m).bits=true :: m.bits :=
          Nat.bits_append_bit m true (fun _=>by simp)
        rw [h1,h2,h3,q28]
    | true =>
      have h1:(Nat.bit true m).bits=true :: m.bits :=
        Nat.bits_append_bit m true (fun _=>by simp)
      have h2:Nat.bit true m+1=Nat.bit false (m+1):=by simp [Nat.bit];omega
      have h3:(Nat.bit false (m+1)).bits=false :: (m+1).bits :=
        Nat.bits_append_bit (m+1) false (fun h=>by omega)
      rw [h1,h2,h3,q28,ih]
lemma q139:CPTs q28:=by
  let δ : Bool → Bool → Bool × Option Bool:=fun c b =>
    match c,b with
    | false,b=>(false,some b)
    | true,false=>(false,some true)
    | true,true=>(true,some false)
  let fin:Bool → Option Bool:=fun c=>if c then some true else none
  refine fst_polyTime _ _ _ δ fin true fun s => ?_
  have hfalse:∀ l,fstRun δ fin false l=l:=by
    intro l;induction l with | nil=>rfl | cons b r ih=>simp [fstRun,δ,fin,ih]
  have htrue:∀ l,fstRun δ fin true l=q28 l:=by
    intro l
    induction l with
    | nil=>rfl
    | cons b r ih=>cases b <;> simp [fstRun,δ,fin,q28,hfalse,ih]
  exact (htrue s).symm
def q48 (u:List Bool):List Bool:=q28^[u.length] []
lemma q71 (u:List Bool):q48 u=u.length.bits:=by
  dsimp only [q48]
  have h:∀ k,q28^[k] []=k.bits:=by
    intro k
    induction k with
    | zero=>rfl
    | succ k ih=>rw [Function.iterate_succ_apply',ih,q163]
  exact h u.length
lemma q41:CPTs q48 :=
  q121 1 q139 q183 cpt_id (cpt_const [])
def q165 (kU zU:List Bool):List Bool :=
  takeN (q48 kU) (q48 zU++blank (q48 kU))
lemma q61 {uk uz:List Bool → List Bool} (hk:CPTs uk) (hz:CPTs uz) :
    CPTs (fun s=>q165 (uk s) (uz s)) :=
  q24 (cpt_comp hk q41)
    (cpt_app2 (cpt_comp hz q41) (cpt_comp (cpt_comp hk q41) cpt_blank))
lemma q86 (k z:ℕ) (hk:0 < k) :
    q165 (un k) (un z)=(List.range (k.log2+1)).map (fun h=>z.testBit h):=by
  dsimp only [q165]
  rw [q12,q71,q71,un_length,un_length]
  have hlen:k.bits.length=k.log2+1:=q175 k hk
  apply List.ext_getElem
  · rw [List.length_take,List.length_append,q33,hlen,List.length_map,List.length_range]
    omega
  · intro h hh1 hh2
    rw [List.length_map,List.length_range] at hh2
    rw [List.getElem_take,List.getElem_map,List.getElem_range,q78]
    by_cases hlt:h < z.bits.length
    · rw [List.getElem_append_left hlt,List.getD_eq_getElem _ _ hlt]
    · rw [List.getElem_append_right (by omega)]
      have hbl:∀ (l:List Bool) (i:ℕ) (hi:i < (blank l).length),(blank l)[i]=false:=by
        intro l
        induction l with
        | nil=>intro i hi;simp [blank] at hi
        | cons _ r ih =>
          intro i hi
          cases i with
          | zero=>rfl
          | succ i=>exact ih i (by simpa [blank] using hi)
      rw [hbl,List.getD_eq_default _ _ (by omega)]
def padW (wU x:List Bool):List Bool:=takeN wU (x++blank wU)
lemma q19 (wU x:List Bool):(padW wU x).length=wU.length:=by
  dsimp only [padW]
  rw [q12,List.length_take,List.length_append,q33]
  omega
lemma q26 (wU x:List Bool):val (padW wU x)=val x % 2 ^ wU.length:=by
  dsimp only [padW]
  rw [q12,q140,q58,q37,mul_zero,add_zero]
lemma q30 (wU x:List Bool) (h:x.length ≤ wU.length):val (padW wU x)=val x:=by
  rw [q26]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (q124 x) (Nat.pow_le_pow_right (by omega) h))
lemma q13 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
    CPTs (fun s=>padW (uw s) (ux s)) :=
  q24 hw (cpt_app2 hx (cpt_comp hw cpt_blank))
def natW (wU u:List Bool):List Bool:=padW wU (q48 u)
lemma q54 (wU u:List Bool):(natW wU u).length=wU.length:=q19 wU _
lemma q114 (wU u:List Bool):val (natW wU u)=u.length % 2 ^ wU.length:=by
  dsimp only [natW];rw [q26,q71,q194]
lemma q70 (wU u:List Bool) :
    ((val (natW wU u):ℤ) ≡ (u.length:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
  rw [q114]
  exact_mod_cast (Nat.mod_modEq u.length (2 ^ wU.length))
lemma q50 {uw uu:List Bool → List Bool} (hw:CPTs uw) (hu:CPTs uu) :
    CPTs (fun s=>natW (uw s) (uu s)) :=
  q13 hw (cpt_comp hu q41)
def q77 (x:List Bool):List Bool:=x.map (!·)
lemma bitNot_len (x:List Bool):(q77 x).length=x.length:=by simp [q77]
lemma q195 (x:List Bool):val (q77 x)+val x+1=2 ^ x.length:=by
  induction x with
  | nil=>simp [q77,val]
  | cons b l ih =>
    simp only [q77,List.map_cons,val,List.length_cons,pow_succ] at ih ⊢
    cases b <;> simp <;> omega
lemma q204:CPTs q77 :=
  fst_polyTime _ _ _ (fun (_:Unit) (b:Bool)=>((),some (!b))) (fun _=>none) () fun s=>by
    induction s with
    | nil=>rfl
    | cons b l ih=>simp only [fstRun,q77,List.map_cons];exact congrArg ((!b) :: ·) ih
def incW (wU x:List Bool):List Bool:=takeN wU (q28 (padW wU x))
lemma q215 (wU x:List Bool):(incW wU x).length=wU.length:=by
  dsimp only [incW];rw [q12,List.length_take]
  have h1:(padW wU x).length ≤ (q28 (padW wU x)).length:=by
    have:∀ l,l.length ≤ (q28 l).length:=by
      intro l;induction l with | nil=>simp [q28] | cons b r ih=>cases b <;> simp [q28] <;> omega
    exact this _
  rw [q19] at h1;omega
lemma q214 (wU x:List Bool):val (incW wU x)=(val x+1) % 2 ^ wU.length:=by
  dsimp only [incW]
  rw [q12,q140,q182,q26,Nat.mod_add_mod]
lemma q218 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
    CPTs (fun s=>incW (uw s) (ux s)) :=
  q24 hw (cpt_comp (q13 hw hx) q139)
def negW (wU x:List Bool):List Bool:=incW wU (q77 (padW wU x))
lemma q197 (wU x:List Bool):(negW wU x).length=wU.length:=q215 wU _
lemma q113 (wU x:List Bool) :
    ((val (negW wU x):ℤ) ≡ -(val x:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
  dsimp only [negW]
  rw [q214]
  have hnot:=q195 (padW wU x)
  rw [q19] at hnot
  have h1:val (q77 (padW wU x))+1=2 ^ wU.length - val (padW wU x):=by omega
  have h2:((val (q77 (padW wU x))+1) % 2 ^ wU.length:ℤ) ≡
      ((val (q77 (padW wU x))+1:ℕ):ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
    exact_mod_cast (Nat.mod_modEq (val (q77 (padW wU x))+1) (2 ^ wU.length))
  have h3:((val (q77 (padW wU x))+1:ℕ):ℤ)+(val (padW wU x):ℤ)=(2:ℤ) ^ wU.length:=by
    exact_mod_cast (by omega:val (q77 (padW wU x))+1+val (padW wU x)=2 ^ wU.length)
  have h4:((val (padW wU x):ℕ):ℤ) ≡ (val x:ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
    rw [q26];exact_mod_cast (Nat.mod_modEq (val x) (2 ^ wU.length))
  have h5:((val (q77 (padW wU x))+1:ℕ):ℤ) ≡ -(val (padW wU x):ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
    rw [Int.modEq_iff_dvd]
    have : -(val (padW wU x):ℤ) - ((val (q77 (padW wU x))+1:ℕ):ℤ) = -((2:ℤ) ^ wU.length):=by linarith
    rw [this];exact dvd_neg.2 (dvd_refl _)
  exact h2.trans (h5.trans h4.neg)
lemma q120 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
    CPTs (fun s=>negW (uw s) (ux s)) :=
  q218 hw (cpt_comp (q13 hw hx) q204)
def shl1W (wU x:List Bool):List Bool:=takeN wU (false :: padW wU x)
lemma q176 (wU x:List Bool):(shl1W wU x).length=wU.length:=by
  dsimp only [shl1W];rw [q12,List.length_take,List.length_cons,q19];omega
lemma q206 (wU x:List Bool):val (shl1W wU x)=(2 * val x) % 2 ^ wU.length:=by
  dsimp only [shl1W]
  rw [q12,q140,val,Bool.toNat_false,zero_add,q26,Nat.mul_mod_mod]
lemma q210 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
    CPTs (fun s=>shl1W (uw s) (ux s)) :=
  q24 hw (cpt_app2 (cpt_const [false]) (q13 hw hx))
def q16 (f:List Bool):List Bool:=sel f [false] [true]
lemma q73 {uf:List Bool → List Bool} (hf:CPTs uf) :
    CPTs (fun s=>q16 (uf s)) :=
  cpt_sel hf (cpt_const [false]) (cpt_const [true])
def xorF (a b:List Bool):List Bool:=sel a (sel b [] [true]) (sel b [true] [])
def majF (a b c:List Bool):List Bool :=
  sel a (sel b [] (sel c [] [true])) (sel b (sel c [] [true]) [true])
lemma q200 {ua ub:List Bool → List Bool} (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>xorF (ua s) (ub s)) :=
  cpt_sel ha (cpt_sel hb (cpt_const []) (cpt_const [true])) (cpt_sel hb (cpt_const [true]) (cpt_const []))
lemma q217 {ua ub uc:List Bool → List Bool} (ha:CPTs ua) (hb:CPTs ub) (hc:CPTs uc) :
    CPTs (fun s=>majF (ua s) (ub s) (uc s)) :=
  cpt_sel ha (cpt_sel hb (cpt_const []) (cpt_sel hc (cpt_const []) (cpt_const [true])))
    (cpt_sel hb (cpt_sel hc (cpt_const []) (cpt_const [true])) (cpt_const [true]))
def q123 (y:List Bool):List Bool :=
  let a:=(unpairB y).1
  let r1:=(unpairB y).2
  let b:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let c:=(unpairB r2).1
  let acc:=(unpairB r2).2
  let ba:=q17 a
  let bb:=q17 b
  let bc:=q17 c
  let sBit:=q16 (xorF (xorF ba bb) bc)
  let c':=majF ba bb bc
  pairB a.tail (pairB b.tail (pairB c' (sBit++acc)))
lemma q193 (y:List Bool):(q123 y).length ≤ y.length+6:=by
  dsimp only [q123]
  have h1:=q0 y
  have h2:=q0 (unpairB y).2
  have h3:=q0 (unpairB (unpairB y).2).2
  rw [q7,q7,q7,List.length_append]
  have ha:(unpairB y).1.tail.length ≤ (unpairB y).1.length:=by cases (unpairB y).1 <;> simp
  have hb:(unpairB (unpairB y).2).1.tail.length ≤ (unpairB (unpairB y).2).1.length:=by
    cases (unpairB (unpairB y).2).1 <;> simp
  have hs:(q16 (xorF (xorF (q17 (unpairB y).1) (q17 (unpairB (unpairB y).2).1))
      (q17 (unpairB (unpairB (unpairB y).2).2).1))).length=1:=by
    unfold q16 sel;split_ifs <;> rfl
  have hc:(majF (q17 (unpairB y).1) (q17 (unpairB (unpairB y).2).1)
      (q17 (unpairB (unpairB (unpairB y).2).2).1)).length ≤ 1:=by
    unfold majF sel;split_ifs <;> simp
  omega
lemma q192:CPTs q123:=by
  have hA:CPTs (fun y=>(unpairB y).1):=cpt_unpairB1
  have hR1:CPTs (fun y=>(unpairB y).2):=cpt_unpairB2
  have hB:CPTs (fun y=>(unpairB (unpairB y).2).1):=q39 (cpt_comp hR1 cpt_unpairB1) (fun _=>rfl)
  have hR2:CPTs (fun y=>(unpairB (unpairB y).2).2):=q39 (cpt_comp hR1 cpt_unpairB2) (fun _=>rfl)
  have hC:CPTs (fun y=>(unpairB (unpairB (unpairB y).2).2).1):=q39 (cpt_comp hR2 cpt_unpairB1) (fun _=>rfl)
  have hAcc:CPTs (fun y=>(unpairB (unpairB (unpairB y).2).2).2):=q39 (cpt_comp hR2 cpt_unpairB2) (fun _=>rfl)
  have hba:=cpt_comp hA q35
  have hbb:=cpt_comp hB q35
  have hbc:=cpt_comp hC q35
  have hs:=q73 (q200 (q200 hba hbb) hbc)
  have hc':=q217 hba hbb hbc
  exact q39 (cpt_pairB2 (cpt_comp hA cpt_tail)
    (cpt_pairB2 (cpt_comp hB cpt_tail) (cpt_pairB2 hc' (cpt_app2 hs hAcc)))) (fun _=>rfl)
def addW (wU a b:List Bool):List Bool :=
  let fin:=q123^[wU.length] (pairB (padW wU a) (pairB (padW wU b) (pairB [] [])))
  (unpairB (unpairB (unpairB fin).2).2).2.reverse
lemma q108 (k:ℕ):∀ (a b:List Bool) (c:Bool) (acc:List Bool),
    a.length=k → b.length=k →
    ∃ (acc':List Bool) (c':Bool),
      q123^[k] (pairB a (pairB b (pairB (if c then [true] else []) acc))) =
        pairB [] (pairB [] (pairB (if c' then [true] else []) (acc'.reverse++acc))) ∧
      acc'.length=k ∧
      val acc'+2 ^ k * c'.toNat=val a+val b+c.toNat:=by
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
        have hstep:q123 (pairB (ba :: ar) (pairB (bb :: br) (pairB (if c then [true] else []) acc))) =
            pairB ar (pairB br (pairB (if ((ba && bb) || (c && (ba || bb))) then [true] else [])
              (((xor (xor ba bb) c) :: acc)))):=by
          dsimp only [q123]
          simp only [unpairB_pairB,List.tail_cons]
          cases ba <;> cases bb <;> cases c <;> rfl
        rw [hstep]
        obtain ⟨acc',c',hiter,hlen,hval⟩:=ih ar br ((ba && bb) || (c && (ba || bb)))
          ((xor (xor ba bb) c) :: acc) (by simpa using ha) (by simpa using hb)
        refine ⟨(xor (xor ba bb) c) :: acc',c',?_,by simp [hlen],?_⟩
        · rw [hiter];simp
        · simp only [val,pow_succ']
          have hbit:(xor (xor ba bb) c).toNat+2 * ((ba && bb) || (c && (ba || bb))).toNat =
              ba.toNat+bb.toNat+c.toNat:=by
            cases ba <;> cases bb <;> cases c <;> decide
          linarith
lemma q180 (wU a b:List Bool) :
    (addW wU a b).length=wU.length∧val (addW wU a b)=(val a+val b) % 2 ^ wU.length:=by
  dsimp only [addW]
  obtain ⟨acc',c',hiter,hlen,hval⟩ :=
    q108 wU.length (padW wU a) (padW wU b) false [] (q19 wU a) (q19 wU b)
  simp only [Bool.false_eq_true,↓reduceIte,List.append_nil,Bool.toNat_false,add_zero] at hiter hval
  rw [hiter]
  simp only [unpairB_pairB,List.reverse_reverse]
  refine ⟨hlen,?_⟩
  have hlt:val acc' < 2 ^ wU.length:=by rw [← hlen];exact q124 acc'
  have hmod1:val acc'=(val (padW wU a)+val (padW wU b)) % 2 ^ wU.length:=by
    have:val (padW wU a)+val (padW wU b)=2 ^ wU.length * c'.toNat+val acc':=by linarith
    rw [this,Nat.mul_add_mod,Nat.mod_eq_of_lt hlt]
  rw [hmod1,q26,q26,Nat.mod_add_mod,Nat.add_mod_mod]
lemma q36 (wU a b:List Bool):(addW wU a b).length=wU.length:=(q180 wU a b).1
lemma q205 (wU a b:List Bool):val (addW wU a b)=(val a+val b) % 2 ^ wU.length :=
  (q180 wU a b).2
lemma q98 (wU a b:List Bool) :
    ((val (addW wU a b):ℤ) ≡ (val a:ℤ)+(val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
  rw [q205];exact_mod_cast (Nat.mod_modEq (val a+val b) (2 ^ wU.length))
lemma q82 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>addW (uw s) (ua s) (ub s)):=by
  have hfin:=q121 6 q192 q193 hw
    (cpt_pairB2 (q13 hw ha) (cpt_pairB2 (q13 hw hb) (cpt_const (pairB [] []))))
  exact cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) q157
def subW (wU a b:List Bool):List Bool:=addW wU a (negW wU b)
lemma q63 (wU a b:List Bool):(subW wU a b).length=wU.length:=q36 wU _ _
lemma q142 (wU a b:List Bool) :
    ((val (subW wU a b):ℤ) ≡ (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
  dsimp only [subW]
  have h1:=q98 wU a (negW wU b)
  have h2:=q113 wU b
  simpa only [sub_eq_add_neg] using h1.trans (Int.ModEq.add_left _ h2)
lemma q83 (wU a b:List Bool) (ha:val a < 2 ^ wU.length) (hge:val b ≤ val a) :
    val (subW wU a b)=val a - val b:=by
  have hmod:=q142 wU a b
  have hlt1:val (subW wU a b) < 2 ^ wU.length:=by rw [← q63 wU a b];exact q124 _
  have hlt2:val a - val b < 2 ^ wU.length:=by omega
  have hcast:((val a - val b:ℕ):ℤ)=(val a:ℤ) - (val b:ℤ):=by omega
  rw [← hcast] at hmod
  have hnat:val (subW wU a b) ≡ val a - val b [MOD 2 ^ wU.length]:=by exact_mod_cast hmod
  rw [Nat.ModEq,Nat.mod_eq_of_lt hlt1,Nat.mod_eq_of_lt hlt2] at hnat
  exact hnat
lemma q148 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>subW (uw s) (ua s) (ub s)) :=
  q82 hw ha (q120 hw hb)
def q116 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let bRem:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let aSh:=(unpairB r2).1
  let acc:=(unpairB r2).2
  let acc':=sel (q17 bRem) (padW wU acc) (addW wU acc aSh)
  let aSh':=shl1W wU aSh
  pairB wU (pairB bRem.tail (pairB aSh' acc'))
lemma q186:CPTs q116:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hb:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have ha:=cpt_comp hr2 cpt_unpairB1
  have hacc:=cpt_comp hr2 cpt_unpairB2
  have hacc':=cpt_sel (cpt_comp hb q35) (q13 hw hacc) (q82 hw hacc ha)
  have ha':=q210 hw ha
  exact cpt_pairB2 hw (cpt_pairB2 (cpt_comp hb cpt_tail) (cpt_pairB2 ha' hacc'))
def mulW (wU a b:List Bool):List Bool :=
  let fin:=q116^[wU.length] (pairB wU (pairB (padW wU b) (pairB (padW wU a) (blank wU))))
  (unpairB (unpairB (unpairB fin).2).2).2
lemma q32 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>mulW (uw s) (ua s) (ub s)):=by
  have hfin:=q18 4 q186
    (fun y=>by dsimp only [q116];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q116]
      set wU:=(unpairB y).1;set r1:=(unpairB y).2
      set bRem:=(unpairB r1).1;set r2:=(unpairB r1).2
      set aSh:=(unpairB r2).1;set acc:=(unpairB r2).2
      have h1:2 * wU.length+r1.length ≤ y.length:=q0 y
      have h2:2 * bRem.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * aSh.length+acc.length ≤ r2.length:=q0 r2
      rw [q7,q7,q7,q176]
      have hbt:bRem.tail.length ≤ bRem.length:=by cases bRem <;> simp
      have hacc:(sel (q17 bRem) (padW wU acc) (addW wU acc aSh)).length=wU.length:=by
        unfold sel;split_ifs
        · exact q19 _ _
        · exact q36 _ _ _
      omega)
    hw (cpt_pairB2 hw (cpt_pairB2 (q13 hw hb) (cpt_pairB2 (q13 hw ha) (cpt_comp hw cpt_blank))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q102 (wU:List Bool) (k:ℕ):∀ (bRem aSh acc:List Bool),
    bRem.length=k → aSh.length=wU.length → acc.length=wU.length →
    ∃ aSh' acc',
      q116^[k] (pairB wU (pairB bRem (pairB aSh acc))) =
        pairB wU (pairB [] (pairB aSh' acc')) ∧
      acc'.length=wU.length ∧
      val acc' % 2 ^ wU.length=(val acc+val aSh * val bRem) % 2 ^ wU.length:=by
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
      have hstep:q116 (pairB wU (pairB (bb :: br) (pairB aSh acc))) =
          pairB wU (pairB br (pairB (shl1W wU aSh) (if bb then addW wU acc aSh else padW wU acc))):=by
        dsimp only [q116]
        simp only [unpairB_pairB,List.tail_cons]
        cases bb <;> rfl
      rw [hstep]
      have hacc1_len:(if bb then addW wU acc aSh else padW wU acc).length=wU.length:=by
        cases bb <;> simp [q36,q19]
      obtain ⟨aSh',acc',hiter,hlen',hval'⟩ :=
        ih br (shl1W wU aSh) (if bb then addW wU acc aSh else padW wU acc)
          (by simpa using hb) (q176 wU aSh) hacc1_len
      refine ⟨aSh',acc',hiter,hlen',?_⟩
      rw [hval',q206]
      have hmod1:val (if bb then addW wU acc aSh else padW wU acc) ≡
          val acc+val aSh * bb.toNat [MOD 2 ^ wU.length]:=by
        cases bb with
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,Bool.toNat_false,mul_zero,add_zero,q26]
          exact Nat.mod_modEq _ _
        | true =>
          simp only [↓reduceIte,Bool.toNat_true,mul_one,q205]
          exact Nat.mod_modEq _ _
      have hmod2:((2 * val aSh) % 2 ^ wU.length) * val br ≡ (2 * val aSh) * val br [MOD 2 ^ wU.length] :=
        (Nat.mod_modEq _ _).mul_right _
      have hcomb:=hmod1.add hmod2
      have hrew:val acc+val aSh * bb.toNat+2 * val aSh * val br =
          val acc+val aSh * (bb.toNat+2 * val br):=by ring
      rw [hrew] at hcomb
      simpa only [Nat.ModEq,val] using hcomb
lemma q179 (wU a b:List Bool) :
    (mulW wU a b).length=wU.length∧val (mulW wU a b)=(val a * val b) % 2 ^ wU.length:=by
  dsimp only [mulW]
  obtain ⟨aSh',acc',hiter,hlen,hval⟩ :=
    q102 wU wU.length (padW wU b) (padW wU a) (blank wU)
      (q19 wU b) (q19 wU a) (q33 wU)
  rw [hiter]
  simp only [unpairB_pairB]
  refine ⟨hlen,?_⟩
  rw [q37,zero_add,q26,q26] at hval
  have hlt:val acc' < 2 ^ wU.length:=by rw [← hlen];exact q124 acc'
  rw [Nat.mod_eq_of_lt hlt] at hval
  rw [hval,Nat.mod_mul_mod,Nat.mul_mod_mod]
lemma q93 (wU a b:List Bool):(mulW wU a b).length=wU.length:=(q179 wU a b).1
lemma q115 (wU a b:List Bool):val (mulW wU a b)=(val a * val b) % 2 ^ wU.length :=
  (q179 wU a b).2
lemma q55 (wU a b:List Bool) :
    ((val (mulW wU a b):ℤ) ≡ (val a:ℤ) * (val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
  rw [q115];exact_mod_cast (Nat.mod_modEq (val a * val b) (2 ^ wU.length))
def geW (wU a b:List Bool):List Bool :=
  let w1:=true :: wU
  q133 (q17 (subW w1 (padW w1 (padW wU a)) (padW w1 (padW wU b))).reverse)
lemma q222 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>geW (uw s) (ua s) (ub s)):=by
  have hw1:=cpt_app2 (cpt_const [true]) hw
  exact cpt_comp (cpt_comp (cpt_comp (q148 hw1 (q13 hw1 (q13 hw ha))
    (q13 hw1 (q13 hw hb))) q157) q35) q138
lemma q145 (l:List Bool) (n:ℕ) (hlen:l.length=n+1) :
    q17 l.reverse=if 2 ^ n ≤ val l then [true] else []:=by
  have hsplit:∃ pref lastB,l=pref++[lastB]∧pref.length=n:=by
    cases hrev:l.reverse with
    | nil =>
      have:=congrArg List.length hrev
      simp [hlen] at this
    | cons b r =>
      refine ⟨r.reverse,b,?_,?_⟩
      · have:=congrArg List.reverse hrev
        simpa using this
      · have h1:=congrArg List.length hrev
        rw [List.length_reverse,hlen,List.length_cons] at h1
        rw [List.length_reverse];omega
  rcases hsplit with ⟨pref,lastB,rfl,hplen⟩
  simp only [List.reverse_append,List.reverse_singleton,List.singleton_append]
  rw [q58,hplen]
  have hplt:val pref < 2 ^ n:=by rw [← hplen];exact q124 pref
  cases lastB with
  | false =>
    simp only [q17,val,Bool.toNat_false,mul_zero,add_zero]
    rw [ite_eq_right_iff.2 (fun h=>by omega)]
  | true =>
    simp only [q17,val,Bool.toNat_true,mul_zero,add_zero,mul_one]
    rw [ite_eq_left_iff.2 (fun h=>by omega)]
lemma q216 (wU a b:List Bool) (ha:val a < 2 ^ wU.length) (hb:val b < 2 ^ wU.length) :
    geW wU a b=if val b ≤ val a then [true] else []:=by
  dsimp only [geW]
  set w1:=true :: wU
  set a1:=padW w1 (padW wU a)
  set b1:=padW w1 (padW wU b)
  set d:=subW w1 a1 b1
  have ha1:val a1=val a:=by
    rw [q30 w1 (padW wU a) (by rw [q19];simp [w1]),
      q26,Nat.mod_eq_of_lt ha]
  have hb1:val b1=val b:=by
    rw [q30 w1 (padW wU b) (by rw [q19];simp [w1]),
      q26,Nat.mod_eq_of_lt hb]
  have hdlen:d.length=wU.length+1:=q63 w1 a1 b1
  have hdlt:val d < 2 ^ (wU.length+1):=by rw [← hdlen];exact q124 d
  have hmod:((val d:ℤ) ≡ (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ (wU.length+1)]):=by
    have hsm:=q142 w1 a1 b1
    rw [ha1,hb1] at hsm
    simpa only [w1,List.length_cons] using hsm
  rw [q145 d wU.length hdlen]
  by_cases hle:val b ≤ val a
  · have hdeq:val d=val a - val b:=by
      have:=q83 w1 a1 b1 (by rw [ha1];simp [w1,pow_succ];omega) (by rw [ha1,hb1];exact hle)
      rw [ha1,hb1] at this;exact this
    have hltW:val d < 2 ^ wU.length:=by omega
    simp [hle,not_le.2 hltW,q133,sel]
  · have hlt:val a < val b:=by omega
    have hdeq:val d=2 ^ (wU.length+1)+val a - val b:=by
      have htarget:2 ^ (wU.length+1)+val a - val b < 2 ^ (wU.length+1):=by omega
      have hcast:((2 ^ (wU.length+1)+val a - val b:ℕ):ℤ) ≡
          (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ (wU.length+1)]:=by
        rw [Int.modEq_iff_dvd]
        have hsub:((2 ^ (wU.length+1)+val a - val b:ℕ):ℤ) =
            (2:ℤ) ^ (wU.length+1)+(val a:ℤ) - (val b:ℤ):=by
          have hge:val b ≤ 2 ^ (wU.length+1)+val a:=by rw [pow_succ];omega
          rw [Nat.cast_sub hge,Nat.cast_add,Nat.cast_pow];norm_num
        have:(val a:ℤ) - (val b:ℤ) - ((2 ^ (wU.length+1)+val a - val b:ℕ):ℤ) =
            -((2:ℤ) ^ (wU.length+1)):=by linarith
        rw [this];exact dvd_neg.2 (dvd_refl _)
      have hnat:val d ≡ 2 ^ (wU.length+1)+val a - val b [MOD 2 ^ (wU.length+1)]:=by
        exact_mod_cast (hmod.trans hcast.symm)
      rw [Nat.ModEq,Nat.mod_eq_of_lt hdlt,Nat.mod_eq_of_lt htarget] at hnat
      exact hnat
    have hgeW:2 ^ wU.length ≤ val d:=by rw [hdeq,pow_succ];omega
    simp [hle,hgeW,q133,sel]
def q118 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let b:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let aRev:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let rem:=(unpairB r3).1
  let qAcc:=(unpairB r3).2
  let rem1:=takeN wU (q16 (q17 aRev)++padW wU rem)
  let ok:=geW wU rem1 b
  let rem':=sel ok rem1 (subW wU rem1 b)
  let qAcc':=q16 ok++qAcc
  pairB wU (pairB b (pairB aRev.tail (pairB rem' qAcc')))
lemma q190:CPTs q118:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hb:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have haRev:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hrem:=cpt_comp hr3 cpt_unpairB1
  have hqAcc:=cpt_comp hr3 cpt_unpairB2
  have hrem1:=q24 hw (cpt_app2 (q73 (cpt_comp haRev q35)) (q13 hw hrem))
  have hok:=q222 hw hrem1 hb
  have hrem':=cpt_sel hok hrem1 (q148 hw hrem1 hb)
  have hqAcc':=cpt_app2 (q73 hok) hqAcc
  exact cpt_pairB2 hw (cpt_pairB2 hb (cpt_pairB2 (cpt_comp haRev cpt_tail) (cpt_pairB2 hrem' hqAcc')))
def divW (wU a b:List Bool):List Bool :=
  let fin:=q118^[wU.length] (pairB wU (pairB (padW wU b) (pairB (padW wU a).reverse (pairB (blank wU) []))))
  (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma q173 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>divW (uw s) (ua s) (ub s)):=by
  have hfin:=q18 10 q190
    (fun y=>by dsimp only [q118];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q118]
      set wU:=(unpairB y).1;set r1:=(unpairB y).2
      set b:=(unpairB r1).1;set r2:=(unpairB r1).2
      set aRev:=(unpairB r2).1;set r3:=(unpairB r2).2
      set rem:=(unpairB r3).1;set qAcc:=(unpairB r3).2
      set rem1:=takeN wU (q16 (q17 aRev)++padW wU rem)
      set ok:=geW wU rem1 b
      have h1:2 * wU.length+r1.length ≤ y.length:=q0 y
      have h2:2 * b.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * aRev.length+r3.length ≤ r2.length:=q0 r2
      have h4:2 * rem.length+qAcc.length ≤ r3.length:=q0 r3
      rw [q7,q7,q7,q7,List.length_append]
      have hat:aRev.tail.length ≤ aRev.length:=by cases aRev <;> simp
      have hrem1_len:rem1.length ≤ wU.length:=by
        dsimp only [rem1];rw [q12,List.length_take];exact Nat.min_le_left _ _
      have hrem':(sel ok rem1 (subW wU rem1 b)).length ≤ wU.length:=by
        unfold sel;split_ifs
        · exact hrem1_len
        · rw [q63]
      have hqb:(q16 ok).length=1:=by unfold q16 sel;split_ifs <;> rfl
      omega)
    hw (cpt_pairB2 hw (cpt_pairB2 (q13 hw hb)
      (cpt_pairB2 (cpt_comp (q13 hw ha) q157) (cpt_pairB2 (cpt_comp hw cpt_blank) (cpt_const [])))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q105 (wU b:List Bool) (hb_len:b.length=wU.length)
    (hb_pos:0 < val b) (hb_2:2 * val b < 2 ^ wU.length) :
    ∀ (k:ℕ) (aRev rem qAcc:List Bool),
      aRev.length=k → rem.length=wU.length → val rem < val b →
      ∃ rem' qAcc',
        q118^[k] (pairB wU (pairB b (pairB aRev (pairB rem qAcc)))) =
          pairB wU (pairB b (pairB [] (pairB rem' qAcc'))) ∧
        qAcc'.length=qAcc.length+k ∧
        val qAcc'=(val qAcc * 2 ^ k+(val rem * 2 ^ k+val aRev.reverse) / val b) ∧
        val rem'=(val rem * 2 ^ k+val aRev.reverse) % val b:=by
  intro k
  induction k with
  | zero =>
    intro aRev rem qAcc ha _ hrem_lt
    cases aRev
    · refine ⟨rem,qAcc,rfl,by simp,?_,?_⟩
      · simp [val,Nat.div_eq_of_lt hrem_lt]
      · simp [val,Nat.mod_eq_of_lt hrem_lt]
    · simp at ha
  | succ k ih =>
    intro aRev rem qAcc ha hrem_len hrem_lt
    cases aRev with
    | nil=>simp at ha
    | cons bit ar =>
      rw [Function.iterate_succ_apply]
      have hrem1_val:val (takeN wU (q16 (q17 (bit :: ar))++padW wU rem)) =
          bit.toNat+2 * val rem:=by
        have hbf:q16 (q17 (bit :: ar))=[bit]:=by cases bit <;> rfl
        rw [hbf,q12,q140,List.singleton_append,val,q30 wU rem (by omega)]
        have hltW:bit.toNat+2 * val rem < 2 ^ wU.length:=by
          have:bit.toNat ≤ 1:=by cases bit <;> decide
          omega
        exact Nat.mod_eq_of_lt hltW
      have hrem1_len:(takeN wU (q16 (q17 (bit :: ar))++padW wU rem)).length=wU.length:=by
        rw [q12,List.length_take,List.length_append,q19]
        have:(q16 (q17 (bit :: ar))).length=1:=by cases bit <;> rfl
        omega
      set rem1:=takeN wU (q16 (q17 (bit :: ar))++padW wU rem)
      have hrem1_ltW:val rem1 < 2 ^ wU.length:=by rw [← hrem1_len];exact q124 rem1
      have hb_ltW:val b < 2 ^ wU.length:=by rw [← hb_len];exact q124 b
      have hok:geW wU rem1 b=if val b ≤ val rem1 then [true] else [] :=
        q216 wU rem1 b hrem1_ltW hb_ltW
      have hstep:q118 (pairB wU (pairB b (pairB (bit :: ar) (pairB rem qAcc)))) =
          pairB wU (pairB b (pairB ar (pairB (if val b ≤ val rem1 then subW wU rem1 b else rem1)
            ((decide (val b ≤ val rem1)) :: qAcc)))):=by
        dsimp only [q118]
        simp only [unpairB_pairB,List.tail_cons]
        change pairB wU (pairB b (pairB ar (pairB (sel (geW wU rem1 b) rem1 (subW wU rem1 b))
            (q16 (geW wU rem1 b)++qAcc))))=_
        rw [hok]
        by_cases hge:val b ≤ val rem1
        · simp [hge,sel,q16]
        · simp [hge,sel,q16]
      rw [hstep]
      set rem'1:=if val b ≤ val rem1 then subW wU rem1 b else rem1
      set q'1:=(decide (val b ≤ val rem1)) :: qAcc
      have hrem'1_len:rem'1.length=wU.length:=by
        dsimp only [rem'1];split_ifs <;> simp [q63,hrem1_len]
      have hrem'1_eq:val rem'1=val rem1 % val b∧val q'1=2 * val qAcc+val rem1 / val b:=by
        have hrem1_lt2b:val rem1 < 2 * val b:=by
          have:bit.toNat ≤ 1:=by cases bit <;> decide
          omega
        by_cases hge:val b ≤ val rem1
        · have hsub:val rem'1=val rem1 - val b:=by
            dsimp only [rem'1];rw [if_pos hge];exact q83 wU rem1 b hrem1_ltW hge
          have hdiv1:val rem1 / val b=1:=by
            have h1:1 * val b ≤ val rem1:=by omega
            have h2:val rem1 < 2 * val b:=hrem1_lt2b
            have h3:=Nat.div_add_mod (val rem1) (val b)
            have h4:val rem1 % val b < val b:=Nat.mod_lt _ hb_pos
            have hge1:1 ≤ val rem1 / val b:=(Nat.le_div_iff_mul_le hb_pos).2 (by omega)
            have hlt2:val rem1 / val b < 2:=(Nat.div_lt_iff_lt_mul hb_pos).2 (by omega)
            omega
          have hmod1:val rem1 % val b=val rem1 - val b:=by
            have:=Nat.div_add_mod (val rem1) (val b)
            rw [hdiv1] at this;omega
          refine ⟨by omega,?_⟩
          dsimp only [q'1];simp [val,hge,hdiv1];omega
        · have hltb:val rem1 < val b:=by omega
          have hsub:val rem'1=val rem1:=by dsimp only [rem'1];rw [if_neg hge]
          refine ⟨by rw [hsub,Nat.mod_eq_of_lt hltb],?_⟩
          dsimp only [q'1];simp [val,hge,Nat.div_eq_of_lt hltb]
      have hrem'1_lt:val rem'1 < val b:=by rw [hrem'1_eq.1];exact Nat.mod_lt _ hb_pos
      obtain ⟨rem',qAcc',hiter,hlen',hq',hr'⟩ :=
        ih ar rem'1 q'1 (by simpa using ha) hrem'1_len hrem'1_lt
      refine ⟨rem',qAcc',hiter,by simp [hlen',q'1];omega,?_,?_⟩
      · rw [hq',hrem'1_eq.2,hrem'1_eq.1]
        have har:val (bit :: ar).reverse=val ar.reverse+2 ^ k * bit.toNat:=by
          rw [List.reverse_cons,q58,List.length_reverse,show ar.length=k by simpa using ha]
          simp [val]
        rw [har]
        have htot:val rem * 2 ^ (k+1)+(val ar.reverse+2 ^ k * bit.toNat) =
            val rem1 * 2 ^ k+val ar.reverse:=by
          rw [hrem1_val,pow_succ'];ring
        rw [htot]
        have hdm:=Nat.div_add_mod (val rem1) (val b)
        have hsplit:val rem1 * 2 ^ k+val ar.reverse =
            val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by
          calc val rem1 * 2 ^ k+val ar.reverse
              = (val b * (val rem1 / val b)+val rem1 % val b) * 2 ^ k+val ar.reverse:=by rw [hdm]
            _=val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by ring
        rw [hsplit,Nat.mul_add_div hb_pos]
        rw [pow_succ'];ring
      · rw [hr',hrem'1_eq.1]
        have har:val (bit :: ar).reverse=val ar.reverse+2 ^ k * bit.toNat:=by
          rw [List.reverse_cons,q58,List.length_reverse,show ar.length=k by simpa using ha]
          simp [val]
        rw [har]
        have htot:val rem * 2 ^ (k+1)+(val ar.reverse+2 ^ k * bit.toNat) =
            val rem1 * 2 ^ k+val ar.reverse:=by
          rw [hrem1_val,pow_succ'];ring
        rw [htot]
        have hdm:=Nat.div_add_mod (val rem1) (val b)
        have hsplit:val rem1 * 2 ^ k+val ar.reverse =
            val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by
          calc val rem1 * 2 ^ k+val ar.reverse
              = (val b * (val rem1 / val b)+val rem1 % val b) * 2 ^ k+val ar.reverse:=by rw [hdm]
            _=val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by ring
        rw [hsplit,Nat.mul_add_mod]
lemma q147 (wU a b:List Bool) (ha:val a < 2 ^ wU.length)
    (hb_pos:0 < val b) (hb_2:2 * val b < 2 ^ wU.length) :
    (divW wU a b).length=wU.length∧val (divW wU a b)=val a / val b:=by
  dsimp only [divW]
  have hb_val:val (padW wU b)=val b:=by
    rw [q26,Nat.mod_eq_of_lt (by omega)]
  have ha_val:val (padW wU a)=val a:=by
    rw [q26,Nat.mod_eq_of_lt ha]
  obtain ⟨rem',qAcc',hiter,hlen',hq',_⟩ :=
    q105 wU (padW wU b) (q19 wU b) (by rw [hb_val];exact hb_pos)
      (by rw [hb_val];exact hb_2) wU.length (padW wU a).reverse (blank wU) []
      (by rw [List.length_reverse,q19]) (q33 wU) (by rw [q37,hb_val];exact hb_pos)
  rw [hiter]
  simp only [unpairB_pairB]
  rw [List.reverse_reverse,ha_val,hb_val,q37] at hq'
  simp only [val,zero_mul,zero_add,List.length_nil] at hlen' hq'
  exact ⟨hlen',hq'⟩
def q87 (l:List Bool):List Bool:=l.dropWhile (fun b => !b)
lemma q159:CPTs q87:=by
  let δ : Bool → Bool → Bool × Option Bool:=fun st b =>
    match st,b with
    | true,b=>(true,some b)
    | false,false=>(false,none)
    | false,true=>(true,some true)
  refine fst_polyTime _ _ _ δ (fun _=>none) false fun s => ?_
  have htrue:∀ l,fstRun δ (fun _=>none) true l=l:=by
    intro l;induction l with | nil=>rfl | cons b r ih=>simp [fstRun,δ,ih]
  have hfalse:∀ l,fstRun δ (fun _=>none) false l=q87 l:=by
    intro l
    induction l with
    | nil=>rfl
    | cons b r ih=>cases b <;> simp [fstRun,δ,q87,htrue,ih]
  exact (hfalse s).symm
def q141 (x:List Bool):List Bool:=(q87 x.reverse).reverse
lemma q167:CPTs q141 :=
  q39 (cpt_comp (cpt_comp q157 q159) q157) (fun _=>rfl)
lemma q109 (x:List Bool):q141 x=(val x).bits:=by
  induction x using List.reverseRecOn with
  | nil=>rfl
  | append_singleton l b ih =>
    dsimp only [q141,q87] at ih ⊢
    rw [List.reverse_append,List.reverse_singleton,List.singleton_append]
    cases b with
    | false =>
      simp only [List.dropWhile_cons,Bool.not_false,↓reduceIte]
      rw [ih,q58]
      simp [val]
    | true =>
      simp only [List.dropWhile_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        List.reverse_cons,List.reverse_reverse]
      have hpos:∀ r:List Bool,(val (r++[true])).bits=r++[true]:=by
        intro r
        induction r with
        | nil=>decide
        | cons c r ihr =>
          have hval:val ((c :: r)++[true])=Nat.bit c (val (r++[true])):=by
            simp only [List.cons_append,val,Nat.bit]
            cases c <;> simp <;> omega
          have hne:val (r++[true])≠0:=by
            rw [q58];simp [val]
          rw [hval,Nat.bits_append_bit _ c (fun h0=>(hne h0).elim),ihr]
          rfl
      exact (hpos l).symm
def q49 (s:List Bool):List Bool:=s.filter id
lemma q150:CPTs q49 :=
  fst_polyTime _ _ _ (fun (_:Unit) (b:Bool)=>((),if b then some true else none))
    (fun _=>none) () fun s=>by
      induction s with
      | nil=>rfl
      | cons b r ih=>cases b <;> simp [fstRun,q49] at ih ⊢ <;> exact ih
def q21 (kU pU uU:List Bool):List Bool :=
  q165 kU pU++q165 kU (true :: pU)++q165 kU uU
def q92 (y:List Bool):List Bool :=
  let boundU:=(unpairB y).1
  let r1:=(unpairB y).2
  let kU:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let nU:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let iU:=(unpairB r3).1
  let r4:=(unpairB r3).2
  let jU:=(unpairB r4).1
  let r5:=(unpairB r4).2
  let jRem:=(unpairB r5).1
  let r6:=(unpairB r5).2
  let pU:=(unpairB r6).1
  let r7:=(unpairB r6).2
  let remBits:=(unpairB r7).1
  let acc:=(unpairB r7).2
  let bit:=q17 remBits
  let chunk:=sel bit [] (takeN boundU (q21 kU pU iU++q21 kU pU (nU++jU)))
  let pU':=sel bit pU (true :: true :: pU)
  let iU':=sel jRem (true :: iU) iU
  let jU':=sel jRem [] (true :: jU)
  let jRem':=sel jRem (takeN boundU nU.tail) jRem.tail
  pairB boundU (pairB kU (pairB nU (pairB iU' (pairB jU' (pairB jRem' (pairB pU' (pairB remBits.tail (acc++chunk))))))))
lemma q168:CPTs q92:=by
  have hb:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hk:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hn:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hi:=cpt_comp hr3 cpt_unpairB1
  have hr4:=cpt_comp hr3 cpt_unpairB2
  have hj:=cpt_comp hr4 cpt_unpairB1
  have hr5:=cpt_comp hr4 cpt_unpairB2
  have hjR:=cpt_comp hr5 cpt_unpairB1
  have hr6:=cpt_comp hr5 cpt_unpairB2
  have hp:=cpt_comp hr6 cpt_unpairB1
  have hr7:=cpt_comp hr6 cpt_unpairB2
  have hrem:=cpt_comp hr7 cpt_unpairB1
  have hacc:=cpt_comp hr7 cpt_unpairB2
  have hbit:=cpt_comp hrem q35
  have ht1:=cpt_app2 (cpt_app2 (q61 hk hp) (q61 hk (cpt_app2 (cpt_const [true]) hp))) (q61 hk hi)
  have ht2:=cpt_app2 (cpt_app2 (q61 hk hp) (q61 hk (cpt_app2 (cpt_const [true]) hp))) (q61 hk (cpt_app2 hn hj))
  have hchunk:=cpt_sel hbit (cpt_const []) (q24 hb (cpt_app2 ht1 ht2))
  have hp':=cpt_sel hbit hp (cpt_app2 (cpt_const [true,true]) hp)
  have hi':=cpt_sel hjR (cpt_app2 (cpt_const [true]) hi) hi
  have hj':=cpt_sel hjR (cpt_const []) (cpt_app2 (cpt_const [true]) hj)
  have hjR':=cpt_sel hjR (q24 hb (cpt_comp hn cpt_tail)) (cpt_comp hjR cpt_tail)
  exact cpt_pairB2 hb (cpt_pairB2 hk (cpt_pairB2 hn (cpt_pairB2 hi' (cpt_pairB2 hj'
    (cpt_pairB2 hjR' (cpt_pairB2 hp' (cpt_pairB2 (cpt_comp hrem cpt_tail) (cpt_app2 hacc hchunk))))))))
def q177 (kU nU bits:List Bool):List Bool :=
  let boundU:=mulU (List.replicate 6 true) (true :: kU)++nU
  let init:=pairB boundU (pairB kU (pairB nU (pairB [] (pairB [] (pairB nU.tail (pairB (nU++nU) (pairB bits [])))))))
  let fin:=q92^[(mulU nU nU).length] init
  (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2).2).2).2
lemma q184 {uk unU ub:List Bool → List Bool} (hk:CPTs uk) (hn:CPTs unU) (hb:CPTs ub) :
    CPTs (fun s=>q177 (uk s) (unU s) (ub s)):=by
  have hbound:=cpt_app2 (q42 (cpt_const (List.replicate 6 true)) (cpt_app2 (cpt_const [true]) hk)) hn
  have hinit:=cpt_pairB2 hbound (cpt_pairB2 hk (cpt_pairB2 hn
    (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const [])
      (cpt_pairB2 (cpt_comp hn cpt_tail) (cpt_pairB2 (cpt_app2 hn hn) (cpt_pairB2 hb (cpt_const []))))))))
  have hfin:=q18 30 q168
    (fun y=>by dsimp only [q92];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q92]
      set boundU:=(unpairB y).1;set r1:=(unpairB y).2
      set kU:=(unpairB r1).1;set r2:=(unpairB r1).2
      set nU:=(unpairB r2).1;set r3:=(unpairB r2).2
      set iU:=(unpairB r3).1;set r4:=(unpairB r3).2
      set jU:=(unpairB r4).1;set r5:=(unpairB r4).2
      set jRem:=(unpairB r5).1;set r6:=(unpairB r5).2
      set pU:=(unpairB r6).1;set r7:=(unpairB r6).2
      set remBits:=(unpairB r7).1;set acc:=(unpairB r7).2
      have h1:2 * boundU.length+r1.length ≤ y.length:=q0 y
      have h2:2 * kU.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * nU.length+r3.length ≤ r2.length:=q0 r2
      have h4:2 * iU.length+r4.length ≤ r3.length:=q0 r3
      have h5:2 * jU.length+r5.length ≤ r4.length:=q0 r4
      have h6:2 * jRem.length+r6.length ≤ r5.length:=q0 r5
      have h7:2 * pU.length+r7.length ≤ r6.length:=q0 r6
      have h8:2 * remBits.length+acc.length ≤ r7.length:=q0 r7
      rw [q7,q7,q7,q7,q7,q7,q7,q7,List.length_append]
      have hc:(sel (q17 remBits) [] (takeN boundU (q21 kU pU iU++q21 kU pU (nU++jU)))).length ≤
          boundU.length:=by
        unfold sel;split_ifs
        · simp
        · rw [q12,List.length_take];exact Nat.min_le_left _ _
      have hp':(sel (q17 remBits) pU (true :: true :: pU)).length ≤ pU.length+2:=by
        unfold sel;split_ifs <;> simp
      have hi':(sel jRem (true :: iU) iU).length ≤ iU.length+1:=by
        unfold sel;split_ifs <;> simp
      have hj':(sel jRem [] (true :: jU)).length ≤ jU.length+1:=by
        unfold sel;split_ifs <;> simp
      have hjR':(sel jRem (takeN boundU nU.tail) jRem.tail).length ≤ boundU.length+jRem.length:=by
        unfold sel;split_ifs
        · rw [q12,List.length_take];have:=Nat.min_le_left boundU.length nU.tail.length;omega
        · cases jRem <;> simp <;> omega
      have hrt:remBits.tail.length ≤ remBits.length:=by cases remBits <;> simp
      omega)
    (q42 hn hn) hinit
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2)
    cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
def q196 (nU bits kU:List Bool):List Bool :=
  (q47 kU++[false])++q177 kU nU bits
lemma q201 {unU ub uk:List Bool → List Bool} (hn:CPTs unU) (hb:CPTs ub) (hk:CPTs uk) :
    CPTs (fun s=>q196 (unU s) (ub s) (uk s)) :=
  cpt_app2 (cpt_app2 (cpt_comp hk q89) (cpt_const [false])) (q184 hk hn hb)
def q74 (y:List Bool):List Bool :=
  let boundOut:=(unpairB y).1
  let r1:=(unpairB y).2
  let nU:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let bits:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let kU:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let chunk:=takeN boundOut (q23 (q196 nU bits kU))
  pairB boundOut (pairB nU (pairB bits (pairB (true :: kU) (acc++chunk))))
lemma q155:CPTs q74:=by
  have hb:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hn:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hbits:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hk:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hchunk:=q24 hb (cpt_comp (q201 hn hbits hk) q171)
  exact cpt_pairB2 hb (cpt_pairB2 hn (cpt_pairB2 hbits (cpt_pairB2 (cpt_app2 (cpt_const [true]) hk) (cpt_app2 hacc hchunk))))
def writeFn (s:List Bool):List Bool :=
  let nU:=hd s
  let bits:=dropN s
  let nSq:=mulU nU nU
  let mU:=q49 (takeN nSq bits)
  let baseK:=nU++nU++mU++mU
  let kMax2:=true :: true :: (baseK++nU)
  let boundOut:=mulU (mulU (List.replicate 13 true) nSq++[true,true,true]) kMax2
  let init:=pairB boundOut (pairB nU (pairB bits (pairB baseK [])))
  let fin:=q74^[(true :: nU).length] init
  (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma cpt_writeFn:CPTs writeFn:=by
  have hn:=cpt_hd
  have hbits:=cpt_dropN
  have hnSq:=q42 hn hn
  have hm:=cpt_comp (q24 hnSq hbits) q150
  have hbaseK:=cpt_app2 (cpt_app2 (cpt_app2 hn hn) hm) hm
  have hkMax2:=cpt_app2 (cpt_const [true,true]) (cpt_app2 hbaseK hn)
  have hboundOut:=q42 (cpt_app2 (q42 (cpt_const (List.replicate 13 true)) hnSq) (cpt_const [true,true,true])) hkMax2
  have hinit:=cpt_pairB2 hboundOut (cpt_pairB2 hn (cpt_pairB2 hbits (cpt_pairB2 hbaseK (cpt_const []))))
  have hfin:=q18 20 q155
    (fun y=>by dsimp only [q74];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q74]
      set boundOut:=(unpairB y).1;set r1:=(unpairB y).2
      set nU:=(unpairB r1).1;set r2:=(unpairB r1).2
      set bits:=(unpairB r2).1;set r3:=(unpairB r2).2
      set kU:=(unpairB r3).1;set acc:=(unpairB r3).2
      have h1:2 * boundOut.length+r1.length ≤ y.length:=q0 y
      have h2:2 * nU.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * bits.length+r3.length ≤ r2.length:=q0 r2
      have h4:2 * kU.length+acc.length ≤ r3.length:=q0 r3
      rw [q7,q7,q7,q7,List.length_append,List.length_cons]
      have hc:(takeN boundOut (q23 (q196 nU bits kU))).length ≤ boundOut.length:=by
        rw [q12,List.length_take];exact Nat.min_le_left _ _
      omega)
    (cpt_app2 (cpt_const [true]) hn) hinit
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q25 (a b:ℕ):un a++un b=un (a+b):=by
  simp [un,List.replicate_append_replicate]
lemma q14 {α β : Type*} (L:List α) (f : α → List β) (n:ℕ)
    (hf:∀ a ∈ L,(f a).length=n):(L.flatMap f).length=L.length * n:=by
  induction L with
  | nil=>simp
  | cons a r ih =>
    rw [List.flatMap_cons,List.length_append,hf a (List.mem_cons_self ..),
      ih (fun x hx=>hf x (List.mem_cons_of_mem a hx)),List.length_cons,Nat.succ_mul,add_comm]
lemma q59 {α β : Type*} (L:List α) (f : α → List β) (n:ℕ)
    (hf:∀ a ∈ L,(f a).length=n) :
    ∀ (i j:ℕ) (hi:i < L.length) (hj:j < n),
      (L.flatMap f)[i * n+j]'(by
        rw [q14 L f n hf]
        have:(i+1) * n ≤ L.length * n:=Nat.mul_le_mul_right n (by omega)
        rw [Nat.succ_mul] at this;omega) =
      (f (L[i]))[j]'(by rw [hf _ (List.getElem_mem hi)];exact hj):=by
  induction L with
  | nil=>intro i _ hi;simp at hi
  | cons a r ih =>
    intro i j hi hj
    cases i with
    | zero =>
      simp only [Nat.zero_mul,zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem_append_left (by rw [hf a (List.mem_cons_self ..)];exact hj)]
    | succ i =>
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      have hlen:(f a).length=n:=hf a (List.mem_cons_self ..)
      rw [List.getElem_append_right (by rw [hlen,Nat.succ_mul];omega)]
      have hidx:(i+1) * n+j - (f a).length=i * n+j:=by rw [hlen,Nat.succ_mul];omega
      simp only [hidx]
      exact ih (fun x hx=>hf x (List.mem_cons_of_mem a hx)) i j (by simpa using hi) hj
lemma q161 (n k:ℕ) (hn:0 < n) (hk:0 < k) (A:Fin n → Fin n → Bool) :
    let cells:=(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
    let ones:=cells.filter (fun z=>A z.1 z.2)
    let rows:=ones.zipIdx.flatMap (fun z=>let p:=2 * n+2 * z.2
      [[p,p+1,z.1.1.val],[p,p+1,n+z.1.2.val]])
    let field:=fun (k z:ℕ)=>(List.range (k.log2+1)).map (fun h=>z.testBit h)
    q177 (un k) (un n) (cells.map (fun z=>A z.1 z.2)) =
      rows.flatMap (fun R=>R.flatMap (field k)):=by
  intro cells ones rows field
  dsimp only [q177]
  set boundU:=mulU (List.replicate 6 true) (true :: un k)++un n
  have hbound_len:boundU.length=6 * (k+1)+n:=by
    simp [boundU,mulU,un]
  have hchunk_le:∀ p i j:ℕ,
      (q21 (un k) (un p) (un i)++q21 (un k) (un p) (un n++un j)).length ≤ boundU.length:=by
    intro p i j
    have hun_app:un n++un j=un (n+j):=q25 n j
    have hfl:∀ z,(q165 (un k) (un z)).length=k.log2+1:=fun z=>by
      rw [q86 k z hk,List.length_map,List.length_range]
    have hlog:k.log2 ≤ k:=Nat.log2_le_self k
    have htp:∀ a b,(q21 (un k) (un a) (un b)).length=3 * (k.log2+1):=fun a b=>by
      dsimp only [q21]
      have h1:true :: un a=un (a+1):=rfl
      rw [h1,List.length_append,List.length_append,hfl,hfl,hfl];omega
    rw [List.length_append,hun_app,htp,htp,hbound_len]
    omega
  have hcells_len:cells.length=n * n:=by
    dsimp only [cells]
    rw [q14 (List.finRange n) _ n (fun _ _=>by simp),List.length_finRange]
  have hcells_get:∀ (r:ℕ) (hr:r < n * n),
      cells[r]'(by rw [hcells_len];exact hr) =
        (⟨r / n,Nat.div_lt_of_lt_mul (by omega)⟩,⟨r % n,Nat.mod_lt r hn⟩):=by
    intro r hr
    have hq:r / n < (List.finRange n).length:=by
      rw [List.length_finRange];exact Nat.div_lt_of_lt_mul (by omega)
    have hm:r % n < n:=Nat.mod_lt r hn
    have hdm:r / n * n+r % n=r:=by have:=Nat.div_add_mod r n;linarith
    have hget:=q59 (List.finRange n)
      (fun i=>(List.finRange n).map (fun j=>(i,j))) n (fun _ _=>by simp) (r / n) (r % n) hq hm
    simp only [hdm,List.getElem_map,List.getElem_finRange] at hget
    exact hget
  let encPrefix:ℕ → List Bool:=fun r =>
    (((cells.take r).filter (fun z=>A z.1 z.2)).zipIdx.flatMap
      (fun z=>let p:=2 * n+2 * z.2;[[p,p+1,z.1.1.val],[p,p+1,n+z.1.2.val]])).flatMap
      (fun R=>R.flatMap (field k))
  let cntPrefix:ℕ → ℕ := fun r=>((cells.take r).filter (fun z=>A z.1 z.2)).length
  have hinv:∀ r ≤ n * n,
      q92^[r] (pairB boundU (pairB (un k) (pairB (un n)
        (pairB [] (pairB [] (pairB (un n).tail (pairB (un n++un n) (pairB (cells.map (fun z=>A z.1 z.2)) [])))))))) =
      pairB boundU (pairB (un k) (pairB (un n)
        (pairB (un (r / n)) (pairB (un (r % n)) (pairB (un (n - 1 - r % n))
          (pairB (un (2 * n+2 * cntPrefix r))
            (pairB ((cells.drop r).map (fun z=>A z.1 z.2)) (encPrefix r)))))))):=by
    intro r hr
    induction r with
    | zero =>
      have htail:(un n).tail=un (n - 1):=by
        cases n with | zero=>omega | succ n'=>rfl
      have h2n:un n++un n=un (2 * n):=by
        rw [q25,two_mul]
      rw [htail,h2n]
      simp [cntPrefix,encPrefix]
    | succ r ih =>
      rw [Function.iterate_succ_apply',ih (by omega)]
      have hrc:r < cells.length:=by rw [hcells_len];omega
      have hdrop:(cells.drop r).map (fun z=>A z.1 z.2) =
          A (cells[r]'hrc).1 (cells[r]'hrc).2 :: (cells.drop (r+1)).map (fun z=>A z.1 z.2):=by
        rw [List.drop_eq_getElem_cons hrc,List.map_cons]
      have htake:cells.take (r+1)=cells.take r++[cells[r]'hrc] :=
        List.take_succ_eq_append_getElem hrc
      have hcellr:=hcells_get r (by omega)
      have htail_un:(un n).tail=un (n - 1):=by
        cases n with | zero=>omega | succ n'=>rfl
      have htake_jR:takeN boundU (un n).tail=un (n - 1):=by
        rw [q12,htail_un,List.take_of_length_le (by rw [un_length,hbound_len];omega)]
      have hdiv_step :
          (if n - 1 - r % n=0 then (r / n+1,0,n - 1)
           else (r / n,r % n+1,n - 1 - (r % n+1))) =
          ((r+1) / n,(r+1) % n,n - 1 - (r+1) % n):=by
        have hlt:r % n < n:=Nat.mod_lt r hn
        by_cases hwrap:r % n+1=n
        · have h0:n - 1 - r % n=0:=by omega
          have hmod:(r+1) % n=0:=by
            have:=Nat.div_add_mod r n
            have:r+1=n * (r / n+1):=by linarith
            rw [this,Nat.mul_mod_right]
          have hdiv:(r+1) / n=r / n+1:=by
            have:=Nat.div_add_mod r n
            have:r+1=n * (r / n+1):=by linarith
            rw [this,Nat.mul_div_right _ hn]
          simp [h0,hmod,hdiv]
        · have hne:n - 1 - r % n≠0:=by omega
          have hmod:(r+1) % n=r % n+1:=by
            have:=Nat.div_add_mod r n
            have:r+1=n * (r / n)+(r % n+1):=by linarith
            rw [this,Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega)]
          have hdiv:(r+1) / n=r / n:=by
            have:=Nat.div_add_mod r n
            have hstep:r+1=n * (r / n)+(r % n+1):=by linarith
            rw [hstep,Nat.mul_add_div hn,Nat.div_eq_of_lt (show r % n+1 < n by omega),add_zero]
          simp [hne,hmod,hdiv]
      dsimp only [q92]
      simp only [unpairB_pairB]
      rw [hdrop,List.tail_cons]
      have h_ij :
          sel (un (n - 1 - r % n)) (true :: un (r / n)) (un (r / n))=un ((r+1) / n) ∧
          sel (un (n - 1 - r % n)) [] (true :: un (r % n))=un ((r+1) % n) ∧
          sel (un (n - 1 - r % n)) (takeN boundU (un n).tail) (un (n - 1 - r % n)).tail =
            un (n - 1 - (r+1) % n):=by
        by_cases h0:n - 1 - r % n=0
        · have h1:=hdiv_step;simp only [h0,↓reduceIte,Prod.mk.injEq] at h1
          have:un (n - 1 - r % n)=[]:=by rw [h0];rfl
          simp only [this,sel,↓reduceIte,htake_jR,← h1.1,← h1.2.1,← h1.2.2]
          exact ⟨rfl,rfl,rfl⟩
        · have h1:=hdiv_step;simp only [h0,↓reduceIte,Prod.mk.injEq] at h1
          have hne:un (n - 1 - r % n)≠[]:=by
            intro he;have:=congrArg List.length he;simp [un] at this;omega
          have htl:(un (n - 1 - r % n)).tail=un (n - 1 - (r % n+1)):=by
            have hge:1 ≤ n - 1 - r % n:=by omega
            have heq:n - 1 - r % n=(n - 1 - (r % n+1))+1:=by omega
            rw [heq];rfl
          simp only [sel,hne,↓reduceIte,htl,← h1.1,← h1.2.1,← h1.2.2,and_self]
          exact ⟨trivial,rfl,trivial⟩
      rw [h_ij.1,h_ij.2.1,h_ij.2.2]
      have hbit_eq:q17 (A (cells[r]'hrc).1 (cells[r]'hrc).2 :: (cells.drop (r+1)).map (fun z=>A z.1 z.2)) =
          if A (cells[r]'hrc).1 (cells[r]'hrc).2 then [true] else []:=by
        cases A (cells[r]'hrc).1 (cells[r]'hrc).2 <;> rfl
      rw [hbit_eq]
      cases hA:A (cells[r]'hrc).1 (cells[r]'hrc).2 with
      | false =>
        have hcnt:cntPrefix (r+1)=cntPrefix r:=by
          dsimp only [cntPrefix];rw [htake,List.filter_append];simp [hA]
        have henc:encPrefix (r+1)=encPrefix r:=by
          dsimp only [encPrefix];rw [htake,List.filter_append];simp [hA]
        simp [sel,hcnt,henc]
      | true =>
        have hcnt:cntPrefix (r+1)=cntPrefix r+1:=by
          dsimp only [cntPrefix];rw [htake,List.filter_append];simp [hA]
        have hchunk_eq :
            takeN boundU (q21 (un k) (un (2 * n+2 * cntPrefix r)) (un (r / n)) ++
              q21 (un k) (un (2 * n+2 * cntPrefix r)) (un n++un (r % n))) =
            ([2 * n+2 * cntPrefix r,2 * n+2 * cntPrefix r+1,r / n].flatMap (field k)) ++
            ([2 * n+2 * cntPrefix r,2 * n+2 * cntPrefix r+1,n+r % n].flatMap (field k)):=by
          rw [q12,List.take_of_length_le (hchunk_le _ _ _)]
          have hun_app:un n++un (r % n)=un (n+r % n):=q25 n (r % n)
          have hsucc:true :: un (2 * n+2 * cntPrefix r)=un (2 * n+2 * cntPrefix r+1):=rfl
          dsimp only [q21]
          rw [hun_app,hsucc,q86 k _ hk,q86 k _ hk,q86 k _ hk,q86 k _ hk]
          simp [field,List.append_assoc]
        have henc:encPrefix (r+1)=encPrefix r ++
            ([2 * n+2 * cntPrefix r,2 * n+2 * cntPrefix r+1,r / n].flatMap (field k) ++
             [2 * n+2 * cntPrefix r,2 * n+2 * cntPrefix r+1,n+r % n].flatMap (field k)):=by
          dsimp only [encPrefix]
          rw [htake,List.filter_append]
          simp only [List.filter_cons,hA,↓reduceIte,List.filter_nil]
          rw [List.zipIdx_append]
          simp only [List.zipIdx_cons,List.zipIdx_nil,zero_add,List.flatMap_append,List.flatMap_cons,
            List.flatMap_nil,List.append_nil,hcellr,cntPrefix]
        have hp_succ:true :: true :: un (2 * n+2 * cntPrefix r)=un (2 * n+2 * cntPrefix (r+1)):=by
          rw [hcnt];have:2 * n+2 * (cntPrefix r+1)=(2 * n+2 * cntPrefix r)+1+1:=by omega
          rw [this];rfl
        simp only [↓reduceIte,sel,List.cons_ne_nil,hchunk_eq,hp_succ,← henc]
  have hmul:(mulU (un n) (un n)).length=n * n:=by simp [mulU,un]
  rw [hmul,hinv (n * n) le_rfl]
  simp only [unpairB_pairB,encPrefix,List.take_of_length_le (by rw [hcells_len]:cells.length ≤ n * n)]
  rfl
lemma writeFn_spec (n:ℕ) (hn:0 < n) (A:Fin n → Fin n → Bool) :
    let header:=fun m:ℕ => List.replicate m true++[false]
    let frame:=fun xs:List Bool=>xs.flatMap (fun b=>[true,b])++[false]
    let field:=fun (k z:ℕ)=>(List.range (k.log2+1)).map (fun h=>z.testBit h)
    let cells:=(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
    let ones:=cells.filter (fun z=>A z.1 z.2)
    let rows:=ones.zipIdx.flatMap (fun z=>let p:=2 * n+2 * z.2
      [[p,p+1,z.1.1.val],[p,p+1,n+z.1.2.val]])
    let size:=fun t:Fin (n+1)=>2 * n+2 * ones.length+t.val
    let query:=fun t:Fin (n+1)=>let k:=size t
      header k++rows.flatMap (fun R=>R.flatMap (field k))
    writeFn (header n++cells.map (fun z=>A z.1 z.2)) =
      (List.finRange (n+1)).flatMap (fun t=>frame (query t)):=by
  intro header frame field cells ones rows size query
  dsimp only [writeFn]
  set bits:=cells.map (fun z=>A z.1 z.2)
  have hhd:hd (header n++bits)=un n:=by
    simp [hd,header,un]
  have hdrop:dropN (header n++bits)=bits:=by
    simp [dropN,header]
  have hcells_len:cells.length=n * n:=by
    dsimp only [cells]
    rw [q14 (List.finRange n) _ n (fun _ _=>by simp),List.length_finRange]
  have hmU:q49 (takeN (mulU (un n) (un n)) bits)=un ones.length:=by
    rw [q12,List.take_of_length_le (by simp [bits,mulU,un,hcells_len])]
    have hfilt:∀ L:List (Fin n × Fin n),
        q49 (L.map (fun z=>A z.1 z.2))=un (L.filter (fun z=>A z.1 z.2)).length:=by
      intro L
      induction L with
      | nil=>rfl
      | cons x r ih =>
        cases hAx:A x.1 x.2 with
        | false=>simp [q49,hAx] at ih ⊢;exact ih
        | true=>simp only [List.map_cons,q49,List.filter_cons,id_eq,hAx,↓reduceIte,
            List.length_cons];exact congrArg (true :: ·) ih
    exact hfilt cells
  rw [hhd,hdrop,hmU]
  have hbaseK:un n++un n++un ones.length++un ones.length=un (2 * n+2 * ones.length):=by
    rw [q25,q25,q25];congr 1;omega
  rw [hbaseK]
  set base:=2 * n+2 * ones.length
  set kMax2:=true :: true :: (un base++un n)
  set boundOut:=mulU (mulU (List.replicate 13 true) (mulU (un n) (un n))++[true,true,true]) kMax2
  have hbound_len:boundOut.length=(13 * n * n+3) * (base+n+2):=by
    simp only [boundOut,kMax2,mulU,un,List.length_append,List.length_cons,List.length_replicate,
      List.length_nil]
    ring
  have hones_le:ones.length ≤ n * n:=by
    have:ones.length ≤ cells.length:=List.length_filter_le _ _
    omega
  have hquery_le:∀ t:Fin (n+1),(frame (query t)).length ≤ boundOut.length:=by
    intro t
    have hframe_len:∀ xs:List Bool,(frame xs).length=2 * xs.length+1:=by
      intro xs
      induction xs with
      | nil=>rfl
      | cons b r ih=>simp [frame] at ih ⊢;omega
    have hrows_len:rows.length=2 * ones.length:=by
      dsimp only [rows]
      rw [q14 ones.zipIdx _ 2 (fun _ _=>rfl),List.length_zipIdx];omega
    have hrows3:∀ R ∈ rows,R.length=3:=by
      intro R hR
      simp only [rows,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hR
      rcases hR with ⟨_,_,rfl | rfl⟩ <;> rfl
    have hflat_len:(rows.flatMap (fun R=>R.flatMap (field (size t)))).length =
        rows.length * (3 * ((size t).log2+1)):=by
      refine q14 rows _ (3 * ((size t).log2+1)) fun R hR => ?_
      rw [q14 R _ ((size t).log2+1) (fun _ _=>by simp [field]),hrows3 R hR]
    have hq_len:(query t).length=size t+1+2 * ones.length * (3 * ((size t).log2+1)):=by
      dsimp only [query,header]
      rw [List.length_append,List.length_append,List.length_replicate,List.length_singleton,hflat_len,hrows_len]
    have hlog:(size t).log2 ≤ size t:=Nat.log2_le_self _
    have hsize_le:size t ≤ base+n:=by dsimp only [size,base];have:=t.isLt;omega
    rw [hframe_len,hq_len,hbound_len]
    have h1:2 * (size t+1+2 * ones.length * (3 * ((size t).log2+1)))+1 ≤
        (13 * n * n+3) * (size t+2):=by
      have h2:2 * ones.length * (3 * ((size t).log2+1)) ≤ 6 * (n * n) * (size t+2):=by
        have ha:2 * ones.length * 3 ≤ 6 * (n * n):=by omega
        have hb:(size t).log2+1 ≤ size t+2:=by omega
        calc 2 * ones.length * (3 * ((size t).log2+1))
            = (2 * ones.length * 3) * ((size t).log2+1):=by ring
          _ ≤ (6 * (n * n)) * (size t+2):=Nat.mul_le_mul ha hb
      have h3:2 * (size t+1)+1 ≤ 3 * (size t+2):=by omega
      have h4:2 * (6 * (n * n) * (size t+2))+3 * (size t+2) ≤ (13 * n * n+3) * (size t+2):=by
        have:12 * (n * n)+3 ≤ 13 * n * n+3:=by nlinarith
        calc 2 * (6 * (n * n) * (size t+2))+3 * (size t+2)
            = (12 * (n * n)+3) * (size t+2):=by ring
          _ ≤ (13 * n * n+3) * (size t+2):=Nat.mul_le_mul_right _ this
      omega
    exact h1.trans (Nat.mul_le_mul_left _ (by omega))
  have hiter:∀ r ≤ n+1,
      q74^[r] (pairB boundOut (pairB (un n) (pairB bits (pairB (un base) [])))) =
      pairB boundOut (pairB (un n) (pairB bits (pairB (un (base+r))
        (((List.finRange (n+1)).take r).flatMap (fun t=>frame (query t)))))):=by
    intro r hr
    induction r with
    | zero=>simp
    | succ r ih =>
      rw [Function.iterate_succ_apply',ih (by omega)]
      dsimp only [q74]
      simp only [unpairB_pairB]
      have hq:q196 (un n) bits (un (base+r))=query ⟨r,by omega⟩:=by
        dsimp only [q196,query,size,header,q47]
        rw [un_length,q161 n (base+r) hn (by omega) A]
      have hframe_eq:q23=frame:=rfl
      rw [hq,hframe_eq,q12,List.take_of_length_le (hquery_le ⟨r,by omega⟩)]
      have htake:(List.finRange (n+1)).take (r+1) =
          (List.finRange (n+1)).take r++[⟨r,by omega⟩]:=by
        have hlt:r < (List.finRange (n+1)).length:=by simp;omega
        rw [List.take_succ_eq_append_getElem hlt]
        simp
      rw [htake,List.flatMap_append,List.flatMap_singleton]
      have hsucc:true :: un (base+r)=un (base+(r+1)):=by
        have:base+(r+1)=(base+r)+1:=by omega
        rw [this];rfl
      rw [hsucc]
  have hlen:(true :: un n).length=n+1:=by simp [un]
  rw [hlen,hiter (n+1) le_rfl]
  simp only [unpairB_pairB,List.take_of_length_le (by simp:(List.finRange (n+1)).length ≤ n+1)]
def q112 (u:List Bool):List Bool:=if u.length % 2=1 then [true] else []
lemma q137:CPTs q112:=by
  let δ : Bool → Bool → Bool × Option Bool:=fun st _=>(!st,none)
  let fin:Bool → Option Bool:=fun st=>if st then some true else none
  refine fst_polyTime _ _ _ δ fin false fun s => ?_
  have hrun:∀ (st:Bool) (l:List Bool),
      fstRun δ fin st l=if (xor st (decide (l.length % 2=1))) then [true] else []:=by
    intro st l
    induction l generalizing st with
    | nil=>cases st <;> rfl
    | cons _ r ih =>
      simp only [fstRun,δ,List.length_cons,ih]
      cases st <;> by_cases h:r.length % 2=1 <;> simp [h] <;> omega
  simpa [q112] using (hrun false s).symm
def q199 (a b:List Bool):List Bool:=q133 (dropN' a b++dropN' b a)
lemma q208 (a b:List Bool):q199 a b=if a.length=b.length then [true] else []:=by
  dsimp only [q199,q133,sel]
  rw [q40,q40]
  by_cases h:a.length=b.length
  · simp [h]
  · have hne:b.drop a.length++a.drop b.length≠[]:=by
      intro he
      have hl:=congrArg List.length he
      simp only [List.length_append,List.length_drop,List.length_nil] at hl
      omega
    simp [h,hne]
lemma q203 {ua ub:List Bool → List Bool} (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>q199 (ua s) (ub s)) :=
  cpt_comp (cpt_app2 (cpt_dropN' ha hb) (cpt_dropN' hb ha)) q138
def q96 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rU:=(unpairB r1).1
  let acc:=(unpairB r1).2
  let r1U:=true :: rU
  pairB wU (pairB r1U (mulW wU acc (natW wU r1U)))
lemma q172:CPTs q96:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hr:=cpt_comp hr1 cpt_unpairB1
  have hacc:=cpt_comp hr1 cpt_unpairB2
  have hr1U:=cpt_app2 (cpt_const [true]) hr
  exact cpt_pairB2 hw (cpt_pairB2 hr1U (q32 hw hacc (q50 hw hr1U)))
def factW (wU kU:List Bool):List Bool :=
  let fin:=q96^[kU.length] (pairB wU (pairB [] (natW wU [true])))
  (unpairB (unpairB fin).2).2
lemma q90 {uw uk:List Bool → List Bool} (hw:CPTs uw) (hk:CPTs uk) :
    CPTs (fun s=>factW (uw s) (uk s)):=by
  have hfin:=q18 6 q172
    (fun y=>by dsimp only [q96];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q96]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      rw [q7,q7,List.length_cons,q93]
      omega)
    hk (cpt_pairB2 hw (cpt_pairB2 (cpt_const []) (q50 hw (cpt_const [true]))))
  exact q39 (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q72 (wU kU:List Bool) :
    (factW wU kU).length=wU.length∧val (factW wU kU)=kU.length.factorial % 2 ^ wU.length:=by
  dsimp only [factW]
  have hiter:∀ k,
      ∃ acc,q96^[k] (pairB wU (pairB [] (natW wU [true])))=pairB wU (pairB (un k) acc) ∧
        acc.length=wU.length∧val acc=k.factorial % 2 ^ wU.length:=by
    intro k
    induction k with
    | zero =>
      refine ⟨natW wU [true],rfl,q54 wU [true],?_⟩
      simp [q114]
    | succ k ih =>
      obtain ⟨acc,h1,hlen,hval⟩:=ih
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q96]
      simp only [unpairB_pairB]
      refine ⟨mulW wU acc (natW wU (true :: un k)),rfl,q93 _ _ _,?_⟩
      rw [q115,hval,q114,List.length_cons,un_length,Nat.mod_mul_mod,Nat.mul_mod_mod,
        Nat.factorial_succ,mul_comm]
  obtain ⟨acc,h1,hlen,hval⟩:=hiter kU.length
  rw [h1];simp only [unpairB_pairB];exact ⟨hlen,hval⟩
def q132 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let base:=(unpairB r1).1
  let acc:=(unpairB r1).2
  pairB wU (pairB base (mulW wU acc base))
lemma q185:CPTs q132:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hb:=cpt_comp hr1 cpt_unpairB1
  have hacc:=cpt_comp hr1 cpt_unpairB2
  exact cpt_pairB2 hw (cpt_pairB2 hb (q32 hw hacc hb))
def powW (wU baseW eU:List Bool):List Bool :=
  let fin:=q132^[eU.length] (pairB wU (pairB (padW wU baseW) (natW wU [true])))
  (unpairB (unpairB fin).2).2
lemma q202 {uw ub ue:List Bool → List Bool} (hw:CPTs uw) (hb:CPTs ub) (he:CPTs ue) :
    CPTs (fun s=>powW (uw s) (ub s) (ue s)):=by
  have hfin:=q18 6 q185
    (fun y=>by dsimp only [q132];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q132]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      rw [q7,q7,q93]
      omega)
    he (cpt_pairB2 hw (cpt_pairB2 (q13 hw hb) (q50 hw (cpt_const [true]))))
  exact q39 (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q178 (wU baseW eU:List Bool) :
    (powW wU baseW eU).length=wU.length∧val (powW wU baseW eU)=(val baseW) ^ eU.length % 2 ^ wU.length:=by
  dsimp only [powW]
  have hiter:∀ k,
      ∃ acc,q132^[k] (pairB wU (pairB (padW wU baseW) (natW wU [true]))) =
          pairB wU (pairB (padW wU baseW) acc) ∧
        acc.length=wU.length∧val acc=(val baseW) ^ k % 2 ^ wU.length:=by
    intro k
    induction k with
    | zero =>
      refine ⟨natW wU [true],rfl,q54 _ _,by simp [q114]⟩
    | succ k ih =>
      obtain ⟨acc,h1,hlen,hval⟩:=ih
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q132]
      simp only [unpairB_pairB]
      refine ⟨mulW wU acc (padW wU baseW),rfl,q93 _ _ _,?_⟩
      rw [q115,hval,q26,Nat.mod_mul_mod,Nat.mul_mod_mod,pow_succ]
  obtain ⟨acc,h1,hlen,hval⟩:=hiter eU.length
  rw [h1];simp only [unpairB_pairB];exact ⟨hlen,hval⟩
def q107 (wU aU bU:List Bool):List Bool :=
  divW wU (factW wU aU) (mulW wU (factW wU bU) (factW wU (dropN' bU aU)))
lemma q122 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
    CPTs (fun s=>q107 (uw s) (ua s) (ub s)) :=
  q173 hw (q90 hw ha) (q32 hw (q90 hw hb) (q90 hw (cpt_dropN' hb ha)))
lemma q97 (wU aU bU:List Bool) (hba:bU.length ≤ aU.length)
    (hbound:2 * aU.length.factorial < 2 ^ wU.length) :
    (q107 wU aU bU).length=wU.length∧val (q107 wU aU bU)=aU.length.choose bU.length:=by
  dsimp only [q107]
  have hfA:=(q72 wU aU).2
  have hfB:=(q72 wU bU).2
  have hdrop_len:(dropN' bU aU).length=aU.length - bU.length:=by
    rw [q40,List.length_drop]
  have hfAB:=(q72 wU (dropN' bU aU)).2
  rw [hdrop_len] at hfAB
  have hch:=Nat.choose_mul_factorial_mul_factorial hba
  have hch_pos:0 < aU.length.choose bU.length:=Nat.choose_pos hba
  have hprod_le:bU.length.factorial * (aU.length - bU.length).factorial ≤ aU.length.factorial:=by
    have:1 * (bU.length.factorial * (aU.length - bU.length).factorial) ≤
        aU.length.choose bU.length * (bU.length.factorial * (aU.length - bU.length).factorial) :=
      Nat.mul_le_mul_right _ hch_pos
    rw [one_mul,← mul_assoc,hch] at this
    exact this
  have hden_pos:0 < bU.length.factorial * (aU.length - bU.length).factorial:=by positivity
  have hA_eq:val (factW wU aU)=aU.length.factorial:=by
    rw [hfA,Nat.mod_eq_of_lt (by omega)]
  have hB_eq:val (factW wU bU)=bU.length.factorial:=by
    have:bU.length.factorial ≤ aU.length.factorial:=Nat.factorial_le hba
    rw [hfB,Nat.mod_eq_of_lt (by omega)]
  have hAB_eq:val (factW wU (dropN' bU aU))=(aU.length - bU.length).factorial:=by
    have:(aU.length - bU.length).factorial ≤ aU.length.factorial:=Nat.factorial_le (by omega)
    rw [hfAB,Nat.mod_eq_of_lt (by omega)]
  have hden_eq:val (mulW wU (factW wU bU) (factW wU (dropN' bU aU))) =
      bU.length.factorial * (aU.length - bU.length).factorial:=by
    rw [q115,hB_eq,hAB_eq,Nat.mod_eq_of_lt (by omega)]
  have hdiv:=q147 wU (factW wU aU) (mulW wU (factW wU bU) (factW wU (dropN' bU aU)))
    (by rw [hA_eq];omega) (by rw [hden_eq];exact hden_pos) (by rw [hden_eq];omega)
  refine ⟨hdiv.1,?_⟩
  rw [hdiv.2,hA_eq,hden_eq]
  have hch':aU.length.factorial=(bU.length.factorial * (aU.length - bU.length).factorial) *
      aU.length.choose bU.length:=by linarith [hch]
  rw [hch',Nat.mul_div_right _ hden_pos]
def q94 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rU:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let a:=(unpairB r2).1
  let b:=(unpairB r2).2
  let r1U:=true :: rU
  let nxt:=subW wU (negW wU b) (mulW wU (natW wU r1U) a)
  pairB wU (pairB r1U (pairB (padW wU b) nxt))
lemma q170:CPTs q94:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hr:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have ha:=cpt_comp hr2 cpt_unpairB1
  have hb:=cpt_comp hr2 cpt_unpairB2
  have hr1U:=cpt_app2 (cpt_const [true]) hr
  have hnxt:=q148 hw (q120 hw hb) (q32 hw (q50 hw hr1U) ha)
  exact cpt_pairB2 hw (cpt_pairB2 hr1U (cpt_pairB2 (q13 hw hb) hnxt))
def jinvW (wU kU:List Bool):List Bool :=
  let oneW:=natW wU [true]
  let fin:=q94^[kU.length] (pairB wU (pairB [] (pairB oneW (negW wU oneW))))
  (unpairB (unpairB (unpairB fin).2).2).1
lemma q212 {uw uk:List Bool → List Bool} (hw:CPTs uw) (hk:CPTs uk) :
    CPTs (fun s=>jinvW (uw s) (uk s)):=by
  have hone:=q50 hw (cpt_const [true])
  have hfin:=q18 8 q170
    (fun y=>by dsimp only [q94];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q94]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      have h3:=q0 (unpairB (unpairB y).2).2
      rw [q7,q7,q7,List.length_cons,q19,q63]
      omega)
    hk (cpt_pairB2 hw (cpt_pairB2 (cpt_const []) (cpt_pairB2 hone (q120 hw hone))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB1) (fun _=>rfl)
lemma q198 (wU kU:List Bool) :
    (jinvW wU kU).length=wU.length ∧
    ((val (jinvW wU kU):ℤ) ≡ jinv kU.length [ZMOD (2:ℤ) ^ wU.length]):=by
  dsimp only [jinvW]
  set oneW:=natW wU [true]
  have hiter:∀ k,
      ∃ a b,q94^[k] (pairB wU (pairB [] (pairB oneW (negW wU oneW)))) =
          pairB wU (pairB (un k) (pairB a b)) ∧
        a.length=wU.length∧b.length=wU.length ∧
        ((val a:ℤ) ≡ jinv k [ZMOD (2:ℤ) ^ wU.length]) ∧
        ((val b:ℤ) ≡ jinv (k+1) [ZMOD (2:ℤ) ^ wU.length]):=by
    intro k
    induction k with
    | zero =>
      refine ⟨oneW,negW wU oneW,rfl,q54 _ _,q197 _ _,?_,?_⟩
      · simpa [jinv,oneW] using q70 wU [true]
      · have h1:=q113 wU oneW
        have h2:((val oneW:ℤ) ≡ (1:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
          simpa [oneW] using q70 wU [true]
        simpa [jinv] using h1.trans h2.neg
    | succ k ih =>
      obtain ⟨a,b,h1,ha_len,hb_len,ha_mod,hb_mod⟩:=ih
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q94]
      simp only [unpairB_pairB]
      set nxt:=subW wU (negW wU b) (mulW wU (natW wU (true :: un k)) a)
      refine ⟨padW wU b,nxt,rfl,q19 _ _,q63 _ _ _,?_,?_⟩
      · rw [q30 wU b (by omega)];exact hb_mod
      · have hsub:=q142 wU (negW wU b) (mulW wU (natW wU (true :: un k)) a)
        have hneg:=(q113 wU b).trans hb_mod.neg
        have hnat:((val (natW wU (true :: un k)):ℤ) ≡ ((k+1:ℕ):ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
          simpa [un_length] using q70 wU (true :: un k)
        have hmul:=(q55 wU (natW wU (true :: un k)) a).trans (hnat.mul ha_mod)
        have hcomb:=hsub.trans (hneg.sub hmul)
        simpa [jinv,Nat.cast_add,Nat.cast_one] using hcomb
  obtain ⟨a,b,h1,ha_len,_,ha_mod,_⟩:=hiter kU.length
  rw [h1];simp only [unpairB_pairB];exact ⟨ha_len,ha_mod⟩
def q46 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rU:=(unpairB r1).1
  let acc:=(unpairB r1).2
  let factorU:=rU++rU++[true]
  pairB wU (pairB (true :: rU) (mulW wU acc (natW wU factorU)))
lemma q131:CPTs q46:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hr:=cpt_comp hr1 cpt_unpairB1
  have hacc:=cpt_comp hr1 cpt_unpairB2
  have hfac:=cpt_app2 (cpt_app2 hr hr) (cpt_const [true])
  exact cpt_pairB2 hw (cpt_pairB2 (cpt_app2 (cpt_const [true]) hr) (q32 hw hacc (q50 hw hfac)))
def q81 (wU kU:List Bool):List Bool :=
  let fin:=q46^[kU.length] (pairB wU (pairB [] (natW wU [true])))
  (unpairB (unpairB fin).2).2
lemma q174 {uw uk:List Bool → List Bool} (hw:CPTs uw) (hk:CPTs uk) :
    CPTs (fun s=>q81 (uw s) (uk s)):=by
  have hfin:=q18 6 q131
    (fun y=>by dsimp only [q46];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q46]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      rw [q7,q7,List.length_cons,q93]
      omega)
    hk (cpt_pairB2 hw (cpt_pairB2 (cpt_const []) (q50 hw (cpt_const [true]))))
  exact q39 (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q154 (wU kU:List Bool) :
    (q81 wU kU).length=wU.length ∧
    ((val (q81 wU kU):ℤ) ≡ (q9 kU.length:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
  dsimp only [q81]
  have hiter:∀ k,
      ∃ acc,q46^[k] (pairB wU (pairB [] (natW wU [true])))=pairB wU (pairB (un k) acc) ∧
        acc.length=wU.length∧((val acc:ℤ) ≡ (q9 k:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
    intro k
    induction k with
    | zero =>
      refine ⟨natW wU [true],rfl,q54 _ _,by simpa [q9] using q70 wU [true]⟩
    | succ k ih =>
      obtain ⟨acc,h1,hlen,hmod⟩:=ih
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q46]
      simp only [unpairB_pairB]
      refine ⟨mulW wU acc (natW wU (un k++un k++[true])),rfl,q93 _ _ _,?_⟩
      have hfac:((val (natW wU (un k++un k++[true])):ℤ) ≡ ((2 * k+1:ℕ):ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
        have hlenf:(un k++un k++[true]).length=2 * k+1:=by simp [un];omega
        have h1:=q70 wU (un k++un k++[true])
        rw [hlenf] at h1
        exact h1
      have hmul:=(q55 wU acc (natW wU (un k++un k++[true]))).trans (hmod.mul hfac)
      simpa [q9,mul_comm,Nat.cast_mul] using hmul
  obtain ⟨acc,h1,hlen,hmod⟩:=hiter kU.length
  rw [h1];simp only [unpairB_pairB];exact ⟨hlen,hmod⟩
def q34 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let mU:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let hU:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let iU:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let term:=mulW wU (q107 wU hU iU) (powW wU (natW wU iU) mU)
  let signedTerm:=sel (q112 (dropN' iU hU)) term (negW wU term)
  pairB wU (pairB mU (pairB hU (pairB (true :: iU) (addW wU acc signedTerm))))
lemma q119:CPTs q34:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hm:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hh:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hi:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hterm:=q32 hw (q122 hw hh hi) (q202 hw (q50 hw hi) hm)
  have hsgn:=cpt_sel (cpt_comp (cpt_dropN' hi hh) q137) hterm (q120 hw hterm)
  exact cpt_pairB2 hw (cpt_pairB2 hm (cpt_pairB2 hh (cpt_pairB2 (cpt_app2 (cpt_const [true]) hi) (q82 hw hacc hsgn))))
def q64 (wU mU hU:List Bool):List Bool :=
  let fin:=q34^[(true :: hU).length] (pairB wU (pairB mU (pairB hU (pairB [] (blank wU)))))
  let num:=(unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
  divW wU num (factW wU hU)
lemma q156 {uw um uh:List Bool → List Bool} (hw:CPTs uw) (hm:CPTs um) (hh:CPTs uh) :
    CPTs (fun s=>q64 (uw s) (um s) (uh s)):=by
  have hfin:=q18 8 q119
    (fun y=>by dsimp only [q34];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q34]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      have h3:=q0 (unpairB (unpairB y).2).2
      have h4:=q0 (unpairB (unpairB (unpairB y).2).2).2
      rw [q7,q7,q7,q7,List.length_cons,q36]
      omega)
    (cpt_app2 (cpt_const [true]) hh)
    (cpt_pairB2 hw (cpt_pairB2 hm (cpt_pairB2 hh (cpt_pairB2 (cpt_const []) (cpt_comp hw cpt_blank)))))
  have hnum:=cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2
  exact q39 (q173 hw hnum (q90 hw hh)) (fun _=>rfl)
lemma q143 (wU mU hU:List Bool)
    (hfact_b:2 * hU.length.factorial < 2 ^ wU.length)
    (hprod_b:hU.length.factorial * q8 mU.length hU.length < 2 ^ wU.length) :
    (q64 wU mU hU).length=wU.length ∧
    val (q64 wU mU hU)=q8 mU.length hU.length:=by
  dsimp only [q64]
  have hiter:∀ r ≤ hU.length+1,
      ∃ acc,q34^[r] (pairB wU (pairB mU (pairB hU (pairB [] (blank wU))))) =
          pairB wU (pairB mU (pairB hU (pairB (un r) acc))) ∧
        acc.length=wU.length ∧
        ((val acc:ℤ) ≡ ∑ i ∈ Finset.range r,
          (-1:ℤ) ^ (hU.length - i) * (hU.length.choose i:ℤ) * (i:ℤ) ^ mU.length [ZMOD (2:ℤ) ^ wU.length]):=by
    intro r hr
    induction r with
    | zero =>
      refine ⟨blank wU,rfl,q33 wU,by simp [q37]⟩
    | succ r ih =>
      obtain ⟨acc,h1,hlen,hmod⟩:=ih (by omega)
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q34]
      simp only [unpairB_pairB]
      set term:=mulW wU (q107 wU hU (un r)) (powW wU (natW wU (un r)) mU)
      set sgn:=sel (q112 (dropN' (un r) hU)) term (negW wU term)
      refine ⟨addW wU acc sgn,rfl,q36 _ _ _,?_⟩
      have hbin:=(q97 wU hU (un r) (by rw [un_length];omega) hfact_b).2
      rw [un_length] at hbin
      have hpow_val:=(q178 wU (natW wU (un r)) mU).2
      have hnat_mod:((val (natW wU (un r)):ℤ) ≡ (r:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
        simpa [un_length] using q70 wU (un r)
      have hpow_mod:((val (powW wU (natW wU (un r)) mU):ℤ) ≡ (r:ℤ) ^ mU.length [ZMOD (2:ℤ) ^ wU.length]):=by
        have hp1:((val (powW wU (natW wU (un r)) mU):ℤ) ≡ ((val (natW wU (un r)):ℤ) ^ mU.length) [ZMOD (2:ℤ) ^ wU.length]):=by
          rw [hpow_val];exact_mod_cast (Nat.mod_modEq _ _)
        exact hp1.trans (hnat_mod.pow mU.length)
      have hterm_mod:((val term:ℤ) ≡ (hU.length.choose r:ℤ) * (r:ℤ) ^ mU.length [ZMOD (2:ℤ) ^ wU.length]):=by
        have hm1:=q55 wU (q107 wU hU (un r)) (powW wU (natW wU (un r)) mU)
        rw [hbin] at hm1
        exact hm1.trans (Int.ModEq.mul_left _ hpow_mod)
      have hsgn_mod:((val sgn:ℤ) ≡
          (-1:ℤ) ^ (hU.length - r) * (hU.length.choose r:ℤ) * (r:ℤ) ^ mU.length [ZMOD (2:ℤ) ^ wU.length]):=by
        dsimp only [sgn,q112]
        have hdl:(dropN' (un r) hU).length=hU.length - r:=by rw [q40,List.length_drop,un_length]
        rw [hdl]
        by_cases hodd:(hU.length - r) % 2=1
        · have hpow1:(-1:ℤ) ^ (hU.length - r) = -1:=by
            have:hU.length - r=2 * ((hU.length - r) / 2)+1:=by omega
            rw [this,pow_add,pow_mul];norm_num
          simp only [hodd,↓reduceIte,sel,List.cons_ne_nil,hpow1]
          simpa [neg_mul,one_mul,mul_assoc] using (q113 wU term).trans hterm_mod.neg
        · have hpow0:(-1:ℤ) ^ (hU.length - r)=1:=by
            have:hU.length - r=2 * ((hU.length - r) / 2):=by omega
            rw [this,pow_mul];norm_num
          simp only [hodd,↓reduceIte,sel,hpow0,one_mul]
          exact hterm_mod
      rw [Finset.sum_range_succ]
      exact (q98 wU acc sgn).trans (hmod.add hsgn_mod)
  obtain ⟨acc,h1,hlen,hmod⟩:=hiter (hU.length+1) le_rfl
  rw [List.length_cons,h1]
  simp only [unpairB_pairB]
  rw [← q69 mU.length hU.length] at hmod
  have hacc_lt:val acc < 2 ^ wU.length:=by rw [← hlen];exact q124 acc
  have hacc_eq:val acc=hU.length.factorial * q8 mU.length hU.length:=by
    have hnat:val acc ≡ hU.length.factorial * q8 mU.length hU.length [MOD 2 ^ wU.length]:=by
      exact_mod_cast hmod
    rw [Nat.ModEq,Nat.mod_eq_of_lt hacc_lt,Nat.mod_eq_of_lt hprod_b] at hnat
    exact hnat
  have hfact_eq:val (factW wU hU)=hU.length.factorial:=by
    rw [(q72 wU hU).2,Nat.mod_eq_of_lt (by omega)]
  have hdiv:=q147 wU acc (factW wU hU) hacc_lt
    (by rw [hfact_eq];exact Nat.factorial_pos _) (by rw [hfact_eq];exact hfact_b)
  refine ⟨hdiv.1,?_⟩
  rw [hdiv.2,hacc_eq,hfact_eq,Nat.mul_div_right _ (Nat.factorial_pos _)]
def getZ (wU rest tU:List Bool):List Bool :=
  padW wU (q75 (q43^[tU.length] rest))
lemma q219 {uw ur ut:List Bool → List Bool} (hw:CPTs uw) (hr:CPTs ur) (ht:CPTs ut) :
    CPTs (fun s=>getZ (uw s) (ur s) (ut s)) :=
  q13 hw (cpt_comp (cpt_iterLen q128 q91 ht hr) q129)
lemma q62 {α : Type*} (L:List α) (f : α → List Bool) :
    ∀ (t:ℕ) (ht:t < L.length),
      q43^[t] (L.flatMap (fun a=>q23 (f a))) =
        (L.drop t).flatMap (fun a=>q23 (f a)):=by
  intro t
  induction t generalizing L with
  | zero=>intro _;simp
  | succ t ih =>
    intro ht
    cases L with
    | nil=>simp at ht
    | cons a r =>
      rw [Function.iterate_succ_apply,List.flatMap_cons,q100]
      exact ih r (by simpa using ht)
lemma q207 (n:ℕ) (wU:List Bool) (Z:Fin (n+1) → ℕ)
    (hZlen:∀ t:Fin (n+1),(Z t).bits.length ≤ wU.length)
    (t:ℕ) (ht:t < n+1) :
    val (getZ wU ((List.finRange (n+1)).flatMap (fun u=>q23 (Z u).bits)) (un t))=Z ⟨t,ht⟩:=by
  dsimp only [getZ]
  rw [un_length,q62 (List.finRange (n+1)) (fun u=>(Z u).bits) t (by simp;omega)]
  have hdrop:(List.finRange (n+1)).drop t=⟨t,ht⟩ :: (List.finRange (n+1)).drop (t+1):=by
    rw [List.drop_eq_getElem_cons (by simp;omega)];simp
  rw [hdrop,List.flatMap_cons,q101,q30 wU _ (hZlen ⟨t,ht⟩),q194]
def yStep (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rest:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let hU:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let tU:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let term:=mulW wU (mulW wU (q107 wU hU tU) (jinvW wU (dropN' tU hU))) (getZ wU rest tU)
  pairB wU (pairB rest (pairB hU (pairB (true :: tU) (addW wU acc term))))
lemma q209:CPTs yStep:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hrest:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hh:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have ht:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hterm:=q32 hw (q32 hw (q122 hw hh ht) (q212 hw (cpt_dropN' ht hh)))
    (q219 hw hrest ht)
  exact cpt_pairB2 hw (cpt_pairB2 hrest (cpt_pairB2 hh (cpt_pairB2 (cpt_app2 (cpt_const [true]) ht) (q82 hw hacc hterm))))
def yW (wU rest hU:List Bool):List Bool :=
  let fin:=yStep^[(true :: hU).length] (pairB wU (pairB rest (pairB hU (pairB [] (blank wU)))))
  (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma q223 {uw ur uh:List Bool → List Bool} (hw:CPTs uw) (hr:CPTs ur) (hh:CPTs uh) :
    CPTs (fun s=>yW (uw s) (ur s) (uh s)):=by
  have hfin:=q18 8 q209
    (fun y=>by dsimp only [yStep];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [yStep]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      have h3:=q0 (unpairB (unpairB y).2).2
      have h4:=q0 (unpairB (unpairB (unpairB y).2).2).2
      rw [q7,q7,q7,q7,List.length_cons,q36]
      omega)
    (cpt_app2 (cpt_const [true]) hh)
    (cpt_pairB2 hw (cpt_pairB2 hr (cpt_pairB2 hh (cpt_pairB2 (cpt_const []) (cpt_comp hw cpt_blank)))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q220 (n:ℕ) (wU:List Bool) (Z:Fin (n+1) → ℕ)
    (hZlen:∀ t:Fin (n+1),(Z t).bits.length ≤ wU.length)
    (hfact_b:2 * n.factorial < 2 ^ wU.length)
    (h:ℕ) (hh:h ≤ n) :
    let rest:=(List.finRange (n+1)).flatMap (fun u=>q23 (Z u).bits)
    let Zf:ℕ → ℤ := fun t=>if ht:t < n+1 then (Z ⟨t,ht⟩:ℤ) else 0
    (yW wU rest (un h)).length=wU.length ∧
    ((val (yW wU rest (un h)):ℤ) ≡
      ∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Zf t [ZMOD (2:ℤ) ^ wU.length]):=by
  intro rest Zf
  dsimp only [yW]
  have hiter:∀ r ≤ h+1,
      ∃ acc,yStep^[r] (pairB wU (pairB rest (pairB (un h) (pairB [] (blank wU))))) =
          pairB wU (pairB rest (pairB (un h) (pairB (un r) acc))) ∧
        acc.length=wU.length ∧
        ((val acc:ℤ) ≡ ∑ t ∈ Finset.range r,(h.choose t:ℤ) * jinv (h - t) * Zf t [ZMOD (2:ℤ) ^ wU.length]):=by
    intro r hr
    induction r with
    | zero=>refine ⟨blank wU,rfl,q33 wU,by simp [q37]⟩
    | succ r ih =>
      obtain ⟨acc,h1,hlen,hmod⟩:=ih (by omega)
      rw [Function.iterate_succ_apply',h1]
      dsimp only [yStep]
      simp only [unpairB_pairB]
      set bW:=q107 wU (un h) (un r)
      set jW:=jinvW wU (dropN' (un r) (un h))
      set zW:=getZ wU rest (un r)
      set m1W:=mulW wU bW jW
      set m2W:=mulW wU m1W zW
      refine ⟨addW wU acc m2W,rfl,q36 _ _ _,?_⟩
      have hhf:2 * (un h).length.factorial < 2 ^ wU.length:=by
        rw [un_length];have:=Nat.factorial_le hh;omega
      have hbin:val bW=h.choose r:=by
        have:=(q97 wU (un h) (un r) (by simp [un];omega) hhf).2
        simpa only [un_length] using this
      have hjinv:((val jW:ℤ) ≡ jinv (h - r) [ZMOD (2:ℤ) ^ wU.length]):=by
        have hlen:(dropN' (un r) (un h)).length=h - r:=by
          rw [q40,List.length_drop,un_length,un_length]
        have h2:=(q198 wU (dropN' (un r) (un h))).2
        rw [hlen] at h2
        exact h2
      have hgz:val zW=Z ⟨r,by omega⟩:=q207 n wU Z hZlen r (by omega)
      have hZf:Zf r=(Z ⟨r,by omega⟩:ℤ):=by dsimp only [Zf];exact dif_pos (by omega)
      have hm1:((val m1W:ℤ) ≡ (h.choose r:ℤ) * jinv (h - r) [ZMOD (2:ℤ) ^ wU.length]):=by
        have hmul:=q55 wU bW jW
        rw [hbin] at hmul
        exact hmul.trans (Int.ModEq.mul_left _ hjinv)
      have hm2:((val m2W:ℤ) ≡ (h.choose r:ℤ) * jinv (h - r) * Zf r [ZMOD (2:ℤ) ^ wU.length]):=by
        have hmul:=q55 wU m1W zW
        rw [hgz] at hmul
        rw [hZf]
        exact hmul.trans (Int.ModEq.mul_right _ hm1)
      rw [Finset.sum_range_succ]
      exact (q98 wU acc m2W).trans (hmod.add hm2)
  obtain ⟨acc,h1,hlen,hmod⟩:=hiter (h+1) le_rfl
  rw [List.length_cons,un_length,h1]
  simp only [unpairB_pairB]
  exact ⟨hlen,hmod⟩
def pStep (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rest:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let mU:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let hU:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let term:=mulW wU (q64 wU mU hU) (yW wU rest hU)
  pairB wU (pairB rest (pairB mU (pairB (true :: hU) (addW wU acc term))))
lemma q211:CPTs pStep:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hrest:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hm:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hh:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hterm:=q32 hw (q156 hw hm hh) (q223 hw hrest hh)
  exact cpt_pairB2 hw (cpt_pairB2 hrest (cpt_pairB2 hm (cpt_pairB2 (cpt_app2 (cpt_const [true]) hh) (q82 hw hacc hterm))))
def pW (wU rest mU:List Bool):List Bool :=
  let fin:=pStep^[(true :: mU).length] (pairB wU (pairB rest (pairB mU (pairB [] (blank wU)))))
  (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma q224 {uw ur um:List Bool → List Bool} (hw:CPTs uw) (hr:CPTs ur) (hm:CPTs um) :
    CPTs (fun s=>pW (uw s) (ur s) (um s)):=by
  have hfin:=q18 8 q211
    (fun y=>by dsimp only [pStep];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [pStep]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      have h3:=q0 (unpairB (unpairB y).2).2
      have h4:=q0 (unpairB (unpairB (unpairB y).2).2).2
      rw [q7,q7,q7,q7,List.length_cons,q36]
      omega)
    (cpt_app2 (cpt_const [true]) hm)
    (cpt_pairB2 hw (cpt_pairB2 hr (cpt_pairB2 hm (cpt_pairB2 (cpt_const []) (cpt_comp hw cpt_blank)))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q221 (n:ℕ) (wU:List Bool) (Z:Fin (n+1) → ℕ)
    (hZlen:∀ t:Fin (n+1),(Z t).bits.length ≤ wU.length)
    (hfact_b:2 * n.factorial < 2 ^ wU.length)
    (hst_b:∀ m ≤ n,∀ h ≤ m,h.factorial * q8 m h < 2 ^ wU.length)
    (m:ℕ) (hm:m ≤ n) :
    let rest:=(List.finRange (n+1)).flatMap (fun u=>q23 (Z u).bits)
    let Zf:ℕ → ℤ := fun t=>if ht:t < n+1 then (Z ⟨t,ht⟩:ℤ) else 0
    let y:ℕ → ℤ := fun h=>∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Zf t
    (pW wU rest (un m)).length=wU.length ∧
    ((val (pW wU rest (un m)):ℤ) ≡
      ∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * y h [ZMOD (2:ℤ) ^ wU.length]):=by
  intro rest Zf y
  dsimp only [pW]
  have hiter:∀ r ≤ m+1,
      ∃ acc,pStep^[r] (pairB wU (pairB rest (pairB (un m) (pairB [] (blank wU))))) =
          pairB wU (pairB rest (pairB (un m) (pairB (un r) acc))) ∧
        acc.length=wU.length ∧
        ((val acc:ℤ) ≡ ∑ h ∈ Finset.range r,(q8 m h:ℤ) * y h [ZMOD (2:ℤ) ^ wU.length]):=by
    intro r hr
    induction r with
    | zero=>refine ⟨blank wU,rfl,q33 wU,by simp [q37]⟩
    | succ r ih =>
      obtain ⟨acc,h1,hlen,hmod⟩:=ih (by omega)
      rw [Function.iterate_succ_apply',h1]
      dsimp only [pStep]
      simp only [unpairB_pairB]
      refine ⟨addW wU acc _,rfl,q36 _ _ _,?_⟩
      have hrf:2 * (un r).length.factorial < 2 ^ wU.length:=by
        rw [un_length];have:=Nat.factorial_le (by omega:r ≤ n);omega
      have hsb:(un r).length.factorial * q8 (un m).length (un r).length < 2 ^ wU.length:=by
        rw [un_length,un_length];exact hst_b m hm r (by omega)
      have hst:=(q143 wU (un m) (un r) hrf hsb).2
      rw [un_length,un_length] at hst
      have hy:=(q220 n wU Z hZlen hfact_b r (by omega)).2
      have hterm:((val (mulW wU (q64 wU (un m) (un r)) (yW wU rest (un r))):ℤ) ≡
          (q8 m r:ℤ) * y r [ZMOD (2:ℤ) ^ wU.length]):=by
        have:=q55 wU (q64 wU (un m) (un r)) (yW wU rest (un r))
        rw [hst] at this
        exact this.trans (Int.ModEq.mul_left _ hy)
      rw [Finset.sum_range_succ]
      exact (q98 wU acc _).trans (hmod.add hterm)
  obtain ⟨acc,h1,hlen,hmod⟩:=hiter (m+1) le_rfl
  rw [List.length_cons,un_length,h1]
  simp only [unpairB_pairB]
  exact ⟨hlen,hmod⟩
def q44 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let twoR:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let prev:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let rem:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let cur:=padW wU (takeN wU rem)
  let nxt:=subW wU prev (mulW wU twoR cur)
  pairB wU (pairB twoR (pairB cur (pairB (dropN' wU rem) (acc++nxt))))
lemma q130:CPTs q44:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have htR:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hprev:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hrem:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hcur:=q13 hw (q24 hw hrem)
  have hnxt:=q148 hw hprev (q32 hw htR hcur)
  exact cpt_pairB2 hw (cpt_pairB2 htR (cpt_pairB2 hcur (cpt_pairB2 (cpt_dropN' hw hrem) (cpt_app2 hacc hnxt))))
def q38 (wU n1U twoR coeffs:List Bool):List Bool :=
  let fin:=q44^[n1U.length] (pairB wU (pairB (padW wU twoR) (pairB (blank wU) (pairB coeffs []))))
  (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma q149 {uw un1 utR uc:List Bool → List Bool}
    (hw:CPTs uw) (hn1:CPTs un1) (htR:CPTs utR) (hc:CPTs uc) :
    CPTs (fun s=>q38 (uw s) (un1 s) (utR s) (uc s)):=by
  have hfin:=q18 8 q130
    (fun y=>by dsimp only [q44];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q44]
      set wU:=(unpairB y).1;set r1:=(unpairB y).2
      set twoR:=(unpairB r1).1;set r2:=(unpairB r1).2
      set prev:=(unpairB r2).1;set r3:=(unpairB r2).2
      set rem:=(unpairB r3).1;set acc:=(unpairB r3).2
      have h1:2 * wU.length+r1.length ≤ y.length:=q0 y
      have h2:2 * twoR.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * prev.length+r3.length ≤ r2.length:=q0 r2
      have h4:2 * rem.length+acc.length ≤ r3.length:=q0 r3
      rw [q7,q7,q7,q7,q19,List.length_append,q63]
      have hd:(dropN' wU rem).length ≤ rem.length:=by
        rw [q40,List.length_drop];omega
      omega)
    hn1 (cpt_pairB2 hw (cpt_pairB2 (q13 hw htR) (cpt_pairB2 (cpt_comp hw cpt_blank) (cpt_pairB2 hc (cpt_const [])))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
def q53 (W m:ℕ) (arr:List Bool):List Bool:=(arr.drop (m * W)).take W
lemma q126 (wU:List Bool) (n r:ℕ) (P:Polynomial ℤ) (coeffs:List Bool)
    (hclen:coeffs.length=(n+1) * wU.length)
    (hcmod:∀ m ≤ n,((val (q53 wU.length m coeffs):ℤ) ≡ P.coeff m [ZMOD (2:ℤ) ^ wU.length])) :
    let res:=q38 wU (un (n+1)) (natW wU (un (2 * r))) coeffs
    res.length=(n+1) * wU.length ∧
    ∀ m ≤ n,((val (q53 wU.length m res):ℤ) ≡
      (P * (Polynomial.X - Polynomial.C (2 * (r:ℤ)))).coeff m [ZMOD (2:ℤ) ^ wU.length]):=by
  dsimp only [q38]
  set W:=wU.length
  set twoR:=natW wU (un (2 * r))
  have htwoR_pad:padW wU twoR=twoR:=by
    dsimp only [padW];rw [q12,List.take_append_of_le_length (by rw [q54]),List.take_of_length_le (by rw [q54])]
  have htwoR_mod:((val twoR:ℤ) ≡ 2 * (r:ℤ) [ZMOD (2:ℤ) ^ W]):=by
    have:=q70 wU (un (2 * r))
    simpa [twoR,un_length,Nat.cast_mul,Nat.cast_ofNat] using this
  have hiter:∀ k ≤ n+1,
      ∃ prev acc,
        q44^[k] (pairB wU (pairB (padW wU twoR) (pairB (blank wU) (pairB coeffs [])))) =
          pairB wU (pairB twoR (pairB prev (pairB (coeffs.drop (k * W)) acc))) ∧
        prev.length=W ∧
        (∀ hk:0 < k,((val prev:ℤ) ≡ P.coeff (k - 1) [ZMOD (2:ℤ) ^ W])) ∧
        (k=0 → val prev=0) ∧
        acc.length=k * W ∧
        ∀ m < k,((val (q53 W m acc):ℤ) ≡
          (P * (Polynomial.X - Polynomial.C (2 * (r:ℤ)))).coeff m [ZMOD (2:ℤ) ^ W]):=by
    intro k hk
    induction k with
    | zero =>
      refine ⟨blank wU,[],by simp [htwoR_pad],q33 wU,fun h=>by omega,fun _=>q37 wU,
        by simp,fun m hm=>by omega⟩
    | succ k ih =>
      obtain ⟨prev,acc,h1,hplen,hprev_pos,hprev_zero,hacclen,haccmod⟩:=ih (by omega)
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q44]
      simp only [unpairB_pairB]
      have hcur_eq:padW wU (takeN wU (coeffs.drop (k * W)))=q53 W k coeffs:=by
        have hlen_take:((coeffs.drop (k * W)).take W).length=W:=by
          rw [List.length_take,List.length_drop,hclen]
          have:(k+1) * W ≤ (n+1) * W:=Nat.mul_le_mul_right W hk
          rw [Nat.succ_mul] at this;omega
        dsimp only [padW,q53]
        rw [q12,q12]
        change (((coeffs.drop (k * W)).take W)++blank wU).take W=(coeffs.drop (k * W)).take W
        rw [List.take_append_of_le_length (by omega),List.take_of_length_le (by omega)]
      have hdrop_eq:dropN' wU (coeffs.drop (k * W))=coeffs.drop ((k+1) * W):=by
        rw [q40,List.drop_drop,Nat.succ_mul,add_comm]
      set cur:=q53 W k coeffs
      set nxt:=subW wU prev (mulW wU twoR cur)
      rw [hcur_eq,hdrop_eq]
      refine ⟨cur,acc++nxt,rfl,?_,?_,fun h=>by omega,?_,?_⟩
      · dsimp only [cur,q53]
        rw [List.length_take,List.length_drop,hclen]
        have:(k+1) * W ≤ (n+1) * W:=Nat.mul_le_mul_right W hk
        rw [Nat.succ_mul] at this;omega
      · intro _;exact hcmod k (by omega)
      · rw [List.length_append,hacclen,q63,Nat.succ_mul]
      · intro m hm
        have hcoeff_mul:(P * (Polynomial.X - Polynomial.C (2 * (r:ℤ)))).coeff m =
            (if m=0 then 0 else P.coeff (m - 1)) - 2 * (r:ℤ) * P.coeff m:=by
          rw [mul_sub,Polynomial.coeff_sub,Polynomial.coeff_mul_C]
          cases m with
          | zero=>simp [mul_comm]
          | succ m'=>simp [Polynomial.coeff_mul_X,mul_comm]
        by_cases hmk:m < k
        · have hwa:q53 W m (acc++nxt)=q53 W m acc:=by
            dsimp only [q53]
            have hle:m * W+W ≤ acc.length:=by
              rw [hacclen];have:=Nat.mul_le_mul_right W (by omega:m+1 ≤ k);rw [Nat.succ_mul] at this;omega
            rw [List.drop_append_of_le_length (by omega),
              List.take_append_of_le_length (by rw [List.length_drop];omega)]
          rw [hwa];exact haccmod m hmk
        · have hmeq:m=k:=by omega
          subst hmeq
          have hwa:q53 W m (acc++nxt)=nxt:=by
            dsimp only [q53]
            rw [← hacclen,List.drop_left,List.take_of_length_le (by rw [q63])]
          rw [hwa,hcoeff_mul]
          have hprev_m:((val prev:ℤ) ≡ (if m=0 then 0 else P.coeff (m - 1)) [ZMOD (2:ℤ) ^ W]):=by
            cases m with
            | zero=>simp [hprev_zero rfl]
            | succ m'=>simp only [Nat.succ_ne_zero,↓reduceIte];exact hprev_pos (Nat.succ_pos m')
          have hcur_m:=hcmod m (by omega)
          have hmul_m:=(q55 wU twoR cur).trans (htwoR_mod.mul hcur_m)
          exact (q142 wU prev (mulW wU twoR cur)).trans (hprev_m.sub hmul_m)
  obtain ⟨_,acc,h1,_,_,_,hacclen,haccmod⟩:=hiter (n+1) le_rfl
  rw [un_length,h1]
  simp only [unpairB_pairB]
  exact ⟨hacclen,fun m hm=>haccmod m (by omega)⟩
def q134 (y:List Bool):List Bool :=
  let boundPoly:=(unpairB y).1
  let r1:=(unpairB y).2
  let wU:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let n1U:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let jU:=(unpairB r3).1
  let r4:=(unpairB r3).2
  let rU:=(unpairB r4).1
  let coeffs:=(unpairB r4).2
  let isEq:=q199 rU jU
  let coeffs':=sel isEq (takeN boundPoly (q38 wU n1U (natW wU (rU++rU)) coeffs)) coeffs
  pairB boundPoly (pairB wU (pairB n1U (pairB jU (pairB (true :: rU) coeffs'))))
lemma q187:CPTs q134:=by
  have hb:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hw:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hn1:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hj:=cpt_comp hr3 cpt_unpairB1
  have hr4:=cpt_comp hr3 cpt_unpairB2
  have hr:=cpt_comp hr4 cpt_unpairB1
  have hc:=cpt_comp hr4 cpt_unpairB2
  have heq:=q203 hr hj
  have hmul:=q24 hb (q149 hw hn1 (q50 hw (cpt_app2 hr hr)) hc)
  have hc':=cpt_sel heq hmul hc
  exact cpt_pairB2 hb (cpt_pairB2 hw (cpt_pairB2 hn1 (cpt_pairB2 hj (cpt_pairB2 (cpt_app2 (cpt_const [true]) hr) hc'))))
def q85 (wU nU jU:List Bool):List Bool :=
  let n1U:=true :: nU
  let boundPoly:=mulU n1U wU
  let initCoeffs:=natW wU [true]++blank (mulU nU wU)
  let fin:=q134^[n1U.length] (pairB boundPoly (pairB wU (pairB n1U (pairB jU (pairB [] initCoeffs)))))
  (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2
lemma q158 {uw unU uj:List Bool → List Bool} (hw:CPTs uw) (hn:CPTs unU) (hj:CPTs uj) :
    CPTs (fun s=>q85 (uw s) (unU s) (uj s)):=by
  have hn1:=cpt_app2 (cpt_const [true]) hn
  have hbound:=q42 hn1 hw
  have hinitC:=cpt_app2 (q50 hw (cpt_const [true])) (cpt_comp (q42 hn hw) cpt_blank)
  have hfin:=q18 8 q187
    (fun y=>by dsimp only [q134];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q134]
      set boundPoly:=(unpairB y).1;set r1:=(unpairB y).2
      set wU:=(unpairB r1).1;set r2:=(unpairB r1).2
      set n1U:=(unpairB r2).1;set r3:=(unpairB r2).2
      set jU:=(unpairB r3).1;set r4:=(unpairB r3).2
      set rU:=(unpairB r4).1;set coeffs:=(unpairB r4).2
      have h1:2 * boundPoly.length+r1.length ≤ y.length:=q0 y
      have h2:2 * wU.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * n1U.length+r3.length ≤ r2.length:=q0 r2
      have h4:2 * jU.length+r4.length ≤ r3.length:=q0 r3
      have h5:2 * rU.length+coeffs.length ≤ r4.length:=q0 r4
      rw [q7,q7,q7,q7,q7,List.length_cons]
      have hc':(sel (q199 rU jU) (takeN boundPoly (q38 wU n1U (natW wU (rU++rU)) coeffs)) coeffs).length ≤
          boundPoly.length+coeffs.length:=by
        unfold sel;split_ifs
        · rw [q12,List.length_take]
          have:=Nat.min_le_left boundPoly.length (q38 wU n1U (natW wU (rU++rU)) coeffs).length
          omega
        · omega
      omega)
    hn1 (cpt_pairB2 hbound (cpt_pairB2 hw (cpt_pairB2 hn1 (cpt_pairB2 hj (cpt_pairB2 (cpt_const []) hinitC)))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q144 (wU:List Bool) (n j:ℕ) (hj:j ≤ n) :
    let arr:=q85 wU (un n) (un j)
    arr.length=(n+1) * wU.length ∧
    ∀ m ≤ n,((val (q53 wU.length m arr):ℤ) ≡ (q31 n j).coeff m [ZMOD (2:ℤ) ^ wU.length]):=by
  dsimp only [q85]
  set W:=wU.length
  set n1U:=true :: un n
  set boundPoly:=mulU n1U wU
  set initCoeffs:=natW wU [true]++blank (mulU (un n) wU)
  have hbound_len:boundPoly.length=(n+1) * W:=by simp [boundPoly,n1U,mulU,un,W]
  have hinit_len:initCoeffs.length=(n+1) * W:=by
    simp [initCoeffs,q54,q33,mulU,un,W];ring
  let prefPoly:ℕ → Polynomial ℤ := fun k =>
    ((Finset.range k).erase j).prod (fun r=>Polynomial.X - Polynomial.C (2 * (r:ℤ)))
  have hiter:∀ k ≤ n+1,
      ∃ arr,q134^[k] (pairB boundPoly (pairB wU (pairB n1U (pairB (un j) (pairB [] initCoeffs))))) =
          pairB boundPoly (pairB wU (pairB n1U (pairB (un j) (pairB (un k) arr)))) ∧
        arr.length=(n+1) * W ∧
        ∀ m ≤ n,((val (q53 W m arr):ℤ) ≡ (prefPoly k).coeff m [ZMOD (2:ℤ) ^ W]):=by
    intro k hk
    induction k with
    | zero =>
      refine ⟨initCoeffs,rfl,hinit_len,fun m hm => ?_⟩
      have hp0:prefPoly 0=1:=by simp [prefPoly]
      rw [hp0]
      cases m with
      | zero =>
        have hwa:q53 W 0 initCoeffs=natW wU [true]:=by
          dsimp only [q53,initCoeffs]
          simp only [Nat.zero_mul,List.drop_zero]
          rw [List.take_append_of_le_length (by rw [q54]),List.take_of_length_le (by rw [q54])]
        rw [hwa,Polynomial.coeff_one_zero]
        simpa [W] using q70 wU [true]
      | succ m' =>
        have hwa:val (q53 W (m'+1) initCoeffs)=0:=by
          dsimp only [q53,initCoeffs]
          have hle:(natW wU [true]).length ≤ (m'+1) * W:=by
            rw [q54,Nat.succ_mul];omega
          rw [List.drop_append,List.drop_eq_nil_of_le hle,List.nil_append]
          have hbl:∀ (l:List Bool) (a b:ℕ),val (((blank l).drop a).take b)=0:=by
            intro l a b
            have hrep:blank l=List.replicate l.length false:=by
              induction l with | nil=>rfl | cons _ r ihr=>simp [blank,List.replicate_succ,ihr]
            rw [hrep,List.drop_replicate,List.take_replicate,q52]
          exact hbl _ _ _
        rw [hwa,Polynomial.coeff_one]
        simp
    | succ k ih =>
      obtain ⟨arr,h1,halen,hamod⟩:=ih (by omega)
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q134]
      simp only [unpairB_pairB]
      rw [q208,un_length,un_length]
      by_cases hkj:k=j
      · have hpref:prefPoly (k+1)=prefPoly k:=by
          dsimp only [prefPoly]
          rw [Finset.range_add_one,← hkj,Finset.erase_insert (Finset.notMem_range_self),
            Finset.erase_eq_of_notMem Finset.notMem_range_self]
        rw [ite_eq_left_iff.2 (fun h=>(h hkj).elim)]
        simp only [sel,List.cons_ne_nil]
        exact ⟨arr,rfl,halen,fun m hm=>by rw [hpref];exact hamod m hm⟩
      · have hpref:prefPoly (k+1)=prefPoly k * (Polynomial.X - Polynomial.C (2 * (k:ℤ))):=by
          dsimp only [prefPoly]
          rw [Finset.range_add_one,Finset.erase_insert_of_ne hkj,
            Finset.prod_insert (by simp [Finset.mem_erase]),mul_comm]
        have hmul_spec:=q126 wU n k (prefPoly k) arr halen hamod
        have h2k:un k++un k=un (2 * k):=by rw [q25,two_mul]
        have hn1eq:n1U=un (n+1):=rfl
        have htake:takeN boundPoly (q38 wU n1U (natW wU (un k++un k)) arr) =
            q38 wU (un (n+1)) (natW wU (un (2 * k))) arr:=by
          rw [hn1eq,h2k,q12,List.take_of_length_le (by rw [hmul_spec.1,hbound_len])]
        simp only [hkj,↓reduceIte,sel,htake]
        exact ⟨_,rfl,hmul_spec.1,fun m hm=>by rw [hpref];exact hmul_spec.2 m hm⟩
  obtain ⟨arr,h1,halen,hamod⟩:=hiter (n+1) le_rfl
  rw [show n1U.length=n+1 by simp [n1U,un],h1]
  simp only [unpairB_pairB]
  exact ⟨halen,hamod⟩
def q135 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rest:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let mU:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let rem:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let coeffW:=padW wU (takeN wU rem)
  let term:=mulW wU coeffW (pW wU rest mU)
  pairB wU (pairB rest (pairB (true :: mU) (pairB (dropN' wU rem) (addW wU acc term))))
lemma q188:CPTs q135:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hrest:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hm:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hrem:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hcoeff:=q13 hw (q24 hw hrem)
  have hterm:=q32 hw hcoeff (q224 hw hrest hm)
  exact cpt_pairB2 hw (cpt_pairB2 hrest (cpt_pairB2 (cpt_app2 (cpt_const [true]) hm)
    (cpt_pairB2 (cpt_dropN' hw hrem) (q82 hw hacc hterm))))
def q136 (wU rest nU jU:List Bool):List Bool :=
  let arr:=q85 wU nU jU
  let fin:=q135^[(true :: nU).length] (pairB wU (pairB rest (pairB [] (pairB arr (blank wU)))))
  (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma q189 {uw ur unU uj:List Bool → List Bool}
    (hw:CPTs uw) (hr:CPTs ur) (hn:CPTs unU) (hj:CPTs uj) :
    CPTs (fun s=>q136 (uw s) (ur s) (unU s) (uj s)):=by
  have harr:=q158 hw hn hj
  have hfin:=q18 8 q188
    (fun y=>by dsimp only [q135];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q135]
      set wU:=(unpairB y).1;set r1:=(unpairB y).2
      set rest:=(unpairB r1).1;set r2:=(unpairB r1).2
      set mU:=(unpairB r2).1;set r3:=(unpairB r2).2
      set rem:=(unpairB r3).1;set acc:=(unpairB r3).2
      have h1:2 * wU.length+r1.length ≤ y.length:=q0 y
      have h2:2 * rest.length+r2.length ≤ r1.length:=q0 r1
      have h3:2 * mU.length+r3.length ≤ r2.length:=q0 r2
      have h4:2 * rem.length+acc.length ≤ r3.length:=q0 r3
      rw [q7,q7,q7,q7,List.length_cons,q36]
      have hd:(dropN' wU rem).length ≤ rem.length:=by
        rw [q40,List.length_drop];omega
      omega)
    (cpt_app2 (cpt_const [true]) hn)
    (cpt_pairB2 hw (cpt_pairB2 hr (cpt_pairB2 (cpt_const []) (cpt_pairB2 harr (cpt_comp hw cpt_blank)))))
  exact q39 (cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q166 (n:ℕ) (wU:List Bool) (Z:Fin (n+1) → ℕ)
    (hZlen:∀ t:Fin (n+1),(Z t).bits.length ≤ wU.length)
    (hfact_b:2 * n.factorial < 2 ^ wU.length)
    (hst_b:∀ m ≤ n,∀ h ≤ m,h.factorial * q8 m h < 2 ^ wU.length)
    (j:ℕ) (hj:j ≤ n) :
    let rest:=(List.finRange (n+1)).flatMap (fun u=>q23 (Z u).bits)
    let Zf:ℕ → ℤ := fun t=>if ht:t < n+1 then (Z ⟨t,ht⟩:ℤ) else 0
    let y:ℕ → ℤ := fun h=>∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) * Zf t
    let p:ℕ → ℤ := fun m=>∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) * y h
    (q136 wU rest (un n) (un j)).length=wU.length ∧
    ((val (q136 wU rest (un n) (un j)):ℤ) ≡
      ∑ m ∈ Finset.range (n+1),(q31 n j).coeff m * p m [ZMOD (2:ℤ) ^ wU.length]):=by
  intro rest Zf y p
  dsimp only [q136]
  set W:=wU.length
  set arr:=q85 wU (un n) (un j)
  have hlag:=q144 wU n j hj
  have hiter:∀ k ≤ n+1,
      ∃ acc,q135^[k] (pairB wU (pairB rest (pairB [] (pairB arr (blank wU))))) =
          pairB wU (pairB rest (pairB (un k) (pairB (arr.drop (k * W)) acc))) ∧
        acc.length=W ∧
        ((val acc:ℤ) ≡ ∑ m ∈ Finset.range k,(q31 n j).coeff m * p m [ZMOD (2:ℤ) ^ W]):=by
    intro k hk
    induction k with
    | zero=>refine ⟨blank wU,by simp,q33 wU,by simp [q37]⟩
    | succ k ih =>
      obtain ⟨acc,h1,hlen,hmod⟩:=ih (by omega)
      rw [Function.iterate_succ_apply',h1]
      dsimp only [q135]
      simp only [unpairB_pairB]
      have hcur_eq:padW wU (takeN wU (arr.drop (k * W)))=q53 W k arr:=by
        have hlen_take:((arr.drop (k * W)).take W).length=W:=by
          rw [List.length_take,List.length_drop,hlag.1]
          have:(k+1) * W ≤ (n+1) * W:=Nat.mul_le_mul_right W hk
          rw [Nat.succ_mul] at this
          dsimp only [W] at this ⊢;omega
        dsimp only [padW,q53]
        rw [q12,q12]
        change (((arr.drop (k * W)).take W)++blank wU).take W=(arr.drop (k * W)).take W
        rw [List.take_append_of_le_length (by omega),List.take_of_length_le (by omega)]
      have hdrop_eq:dropN' wU (arr.drop (k * W))=arr.drop ((k+1) * W):=by
        rw [q40,List.drop_drop,Nat.succ_mul,add_comm]
      rw [hcur_eq,hdrop_eq]
      refine ⟨addW wU acc _,rfl,q36 _ _ _,?_⟩
      have hc_mod:=hlag.2 k (by omega)
      have hp_mod:=(q221 n wU Z hZlen hfact_b hst_b k (by omega)).2
      have hterm:=(q55 wU (q53 W k arr) (pW wU rest (un k))).trans (hc_mod.mul hp_mod)
      rw [Finset.sum_range_succ]
      exact (q98 wU acc _).trans (hmod.add hterm)
  obtain ⟨acc,h1,hlen,hmod⟩:=hiter (n+1) le_rfl
  rw [List.length_cons,un_length,h1]
  simp only [unpairB_pairB]
  exact ⟨hlen,hmod⟩
def q60 (y:List Bool):List Bool :=
  let wU:=(unpairB y).1
  let r1:=(unpairB y).2
  let rest:=(unpairB r1).1
  let r2:=(unpairB r1).2
  let nU:=(unpairB r2).1
  let r3:=(unpairB r2).2
  let jU:=(unpairB r3).1
  let acc:=(unpairB r3).2
  let term:=mulW wU (mulW wU (q81 wU jU) (q107 wU nU jU)) (q136 wU rest nU jU)
  pairB wU (pairB rest (pairB nU (pairB (true :: jU) (addW wU acc term))))
lemma q151:CPTs q60:=by
  have hw:=cpt_unpairB1
  have hr1:=cpt_unpairB2
  have hrest:=cpt_comp hr1 cpt_unpairB1
  have hr2:=cpt_comp hr1 cpt_unpairB2
  have hn:=cpt_comp hr2 cpt_unpairB1
  have hr3:=cpt_comp hr2 cpt_unpairB2
  have hj:=cpt_comp hr3 cpt_unpairB1
  have hacc:=cpt_comp hr3 cpt_unpairB2
  have hterm:=q32 hw (q32 hw (q174 hw hj) (q122 hw hn hj)) (q189 hw hrest hn hj)
  exact cpt_pairB2 hw (cpt_pairB2 hrest (cpt_pairB2 hn (cpt_pairB2 (cpt_app2 (cpt_const [true]) hj) (q82 hw hacc hterm))))
def q88 (wU nU rest:List Bool):List Bool :=
  let fin:=q60^[(true :: nU).length] (pairB wU (pairB rest (pairB nU (pairB [] (blank wU)))))
  let s:=(unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
  sel (q112 nU) s (negW wU s)
lemma q191 {uw unU ur:List Bool → List Bool} (hw:CPTs uw) (hn:CPTs unU) (hr:CPTs ur) :
    CPTs (fun s=>q88 (uw s) (unU s) (ur s)):=by
  have hfin:=q18 8 q151
    (fun y=>by dsimp only [q60];rw [unpairB_pairB])
    (fun y=>by
      dsimp only [q60]
      have h1:=q0 y
      have h2:=q0 (unpairB y).2
      have h3:=q0 (unpairB (unpairB y).2).2
      have h4:=q0 (unpairB (unpairB (unpairB y).2).2).2
      rw [q7,q7,q7,q7,List.length_cons,q36]
      omega)
    (cpt_app2 (cpt_const [true]) hn)
    (cpt_pairB2 hw (cpt_pairB2 hr (cpt_pairB2 hn (cpt_pairB2 (cpt_const []) (cpt_comp hw cpt_blank)))))
  have hs:=cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) cpt_unpairB2
  exact q39 (cpt_sel (cpt_comp hn q137) hs (q120 hw hs)) (fun _=>rfl)
def readFn (s:List Bool):List Bool :=
  let nU:=hd s
  let rest:=dropN s
  let n1U:=true :: nU
  let wU:=s++mulU (List.replicate 12 true) (mulU n1U n1U)++List.replicate 16 true
  let numW:=q88 wU nU rest
  let denW:=mulW wU (powW wU (natW wU [true,true]) (nU++nU)) (factW wU nU)
  q141 (divW wU numW denW)
lemma cpt_readFn:CPTs readFn:=by
  have hn:=cpt_hd
  have hrest:=cpt_dropN
  have hn1:=cpt_app2 (cpt_const [true]) hn
  have hw:=cpt_app2 (cpt_app2 cpt_id (q42 (cpt_const (List.replicate 12 true)) (q42 hn1 hn1)))
    (cpt_const (List.replicate 16 true))
  have hnum:=q191 hw hn hrest
  have hden:=q32 hw (q202 hw (q50 hw (cpt_const [true,true])) (cpt_app2 hn hn)) (q90 hw hn)
  exact q39 (cpt_comp (q173 hw hnum hden) q167) (fun _=>rfl)
lemma q65 (k:ℕ):k.factorial ≤ 2 ^ (k * k):=by
  induction k with
  | zero=>simp
  | succ k ih =>
    rw [Nat.factorial_succ]
    have h1:k+1 ≤ 2 ^ (2 * k+1):=by
      have:k+1 ≤ 2 ^ k+2 ^ k:=by have:=Nat.lt_two_pow_self (n:=k);omega
      have hpow:2 ^ (2 * k+1)=2 * 2 ^ k * 2 ^ k:=by
        rw [pow_succ,two_mul,pow_add];ring
      have hge:1 ≤ 2 ^ k:=Nat.one_le_two_pow
      nlinarith
    have h2:(k+1) * k.factorial ≤ 2 ^ (2 * k+1) * 2 ^ (k * k):=Nat.mul_le_mul h1 ih
    rw [← pow_add] at h2
    have hexp:2 * k+1+k * k=(k+1) * (k+1):=by ring
    rwa [hexp] at h2
lemma q111 (m h:ℕ):h.factorial * q8 m h ≤ 2 ^ (h+m * h):=by
  have hcl:=q69 m h
  have hle:((h.factorial * q8 m h:ℕ):ℤ) ≤
      ∑ i ∈ Finset.range (h+1),(h.choose i:ℤ) * (h:ℤ) ^ m:=by
    rw [Nat.cast_mul,hcl]
    refine Finset.sum_le_sum fun i hi => ?_
    have hilt:i ≤ h:=Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have habs:(-1:ℤ) ^ (h - i) ≤ 1:=by
      rcases neg_one_pow_eq_or ℤ (h - i) with h1 | h1 <;> omega
    have hnn:0 ≤ (h.choose i:ℤ) * (i:ℤ) ^ m:=by positivity
    have h1:(-1:ℤ) ^ (h - i) * (h.choose i:ℤ) * (i:ℤ) ^ m ≤ (h.choose i:ℤ) * (i:ℤ) ^ m:=by
      nlinarith
    have h2:(i:ℤ) ^ m ≤ (h:ℤ) ^ m:=pow_le_pow_left₀ (by positivity) (by exact_mod_cast hilt) m
    have h3:(h.choose i:ℤ) * (i:ℤ) ^ m ≤ (h.choose i:ℤ) * (h:ℤ) ^ m :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    omega
  have hsum:(∑ i ∈ Finset.range (h+1),(h.choose i:ℤ) * (h:ℤ) ^ m) =
      (2:ℤ) ^ h * (h:ℤ) ^ m:=by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast (Nat.sum_range_choose h)
  rw [hsum] at hle
  have hnat:h.factorial * q8 m h ≤ 2 ^ h * h ^ m:=by exact_mod_cast hle
  have hh:h ^ m ≤ (2 ^ h) ^ m:=Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) m
  have hmul:2 ^ h * h ^ m ≤ 2 ^ h * (2 ^ h) ^ m:=Nat.mul_le_mul_left _ hh
  rw [← pow_mul,← pow_add,mul_comm h m] at hmul
  exact hnat.trans hmul
lemma readFn_spec (n:ℕ) (A:Fin n → Fin n → Bool) (Z:Fin (n+1) → ℕ)
    (hdec:q27 n (fun t=>if ht:t < n+1 then (Z ⟨t,ht⟩:ℤ) else 0) =
      (2:ℤ) ^ (2 * n) * (n.factorial:ℤ) *
        ((Matrix.permanent (fun i j:Fin n=>(A i j).toNat):ℕ):ℤ)) :
    let header:=fun m:ℕ => List.replicate m true++[false]
    let frame:=fun xs:List Bool=>xs.flatMap (fun b=>[true,b])++[false]
    let B:Matrix (Fin n) (Fin n) ℕ := fun i j=>(A i j).toNat
    readFn (header n++(List.finRange (n+1)).flatMap (fun t=>frame (Z t).bits)) =
      B.permanent.bits:=by
  intro header frame B
  dsimp only [readFn]
  set rest:=(List.finRange (n+1)).flatMap (fun t=>frame (Z t).bits)
  set s:=header n++rest
  have hhd:hd s=un n:=by simp [s,hd,header,un]
  have hdrop:dropN s=rest:=by simp [s,dropN,header]
  rw [hhd,hdrop]
  set n1U:=true :: un n
  set wU:=s++mulU (List.replicate 12 true) (mulU n1U n1U)++List.replicate 16 true
  set W:=wU.length
  have hW_ge:s.length+12 * (n+1) * (n+1)+16 ≤ W:=by
    simp only [W,wU,n1U,mulU,un,List.length_append,List.length_cons,List.length_replicate]
    nlinarith
  have hZlen:∀ t:Fin (n+1),(Z t).bits.length ≤ W:=by
    intro t
    have hmem:t ∈ List.finRange (n+1):=List.mem_finRange t
    have hfl:∀ (L:List (Fin (n+1))) (a:Fin (n+1)),a ∈ L →
        (frame (Z a).bits).length ≤ (L.flatMap (fun u=>frame (Z u).bits)).length:=by
      intro L a ha
      induction L with
      | nil=>simp at ha
      | cons x r ih =>
        rw [List.flatMap_cons]
        have happ:(frame (Z x).bits++r.flatMap (fun u=>frame (Z u).bits)).length =
            (frame (Z x).bits).length+(r.flatMap (fun u=>frame (Z u).bits)).length :=
          List.length_append
        rw [happ]
        rcases List.mem_cons.1 ha with rfl | hr
        · exact Nat.le_add_right _ _
        · exact le_trans (ih hr) (Nat.le_add_left _ _)
    have hfr:(Z t).bits.length ≤ (frame (Z t).bits).length:=by
      have:∀ xs:List Bool,xs.length ≤ (frame xs).length:=by
        intro xs;induction xs with | nil=>simp [frame] | cons _ r ih=>simp [frame] at ih ⊢;omega
      exact this _
    have hs_len:rest.length ≤ s.length:=by simp [s]
    have hrest_eq:rest.length=((List.finRange (n+1)).flatMap (fun u=>frame (Z u).bits)).length:=rfl
    have hle1:=hfl (List.finRange (n+1)) t hmem
    omega
  have hfact_b:2 * n.factorial < 2 ^ W:=by
    have h1:=q65 n
    have h2:2 * n.factorial ≤ 2 ^ (n * n+1):=by rw [pow_succ'];omega
    have h3:n * n+1 < W:=by nlinarith
    exact lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by omega) h3)
  have hst_b:∀ m ≤ n,∀ h ≤ m,h.factorial * q8 m h < 2 ^ W:=by
    intro m hm h hhm
    have h1:=q111 m h
    have h2:h+m * h < W:=by nlinarith
    exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by omega) h2)
  have hframe_eq:frame=q23:=rfl
  have hdecW:(q88 wU (un n) rest).length=W ∧
      ((val (q88 wU (un n) rest):ℤ) ≡
        q27 n (fun t=>if ht:t < n+1 then (Z ⟨t,ht⟩:ℤ) else 0) [ZMOD (2:ℤ) ^ W]):=by
    dsimp only [q88]
    have hiter:∀ k ≤ n+1,
        ∃ acc,q60^[k] (pairB wU (pairB rest (pairB (un n) (pairB [] (blank wU))))) =
            pairB wU (pairB rest (pairB (un n) (pairB (un k) acc))) ∧
          acc.length=W ∧
          ((val acc:ℤ) ≡ ∑ j ∈ Finset.range k,(q9 j:ℤ) * (n.choose j:ℤ) *
            ∑ m ∈ Finset.range (n+1),(q31 n j).coeff m *
              (∑ h ∈ Finset.range (m+1),(q8 m h:ℤ) *
                (∑ t ∈ Finset.range (h+1),(h.choose t:ℤ) * jinv (h - t) *
                  (if ht:t < n+1 then (Z ⟨t,ht⟩:ℤ) else 0))) [ZMOD (2:ℤ) ^ W]):=by
      intro k hk
      induction k with
      | zero=>refine ⟨blank wU,rfl,q33 wU,by simp [q37]⟩
      | succ k ih =>
        obtain ⟨acc,h1,hlen,hmod⟩:=ih (by omega)
        rw [Function.iterate_succ_apply',h1]
        dsimp only [q60]
        simp only [unpairB_pairB]
        refine ⟨addW wU acc _,rfl,q36 _ _ _,?_⟩
        have hdbl:=(q154 wU (un k)).2
        rw [un_length] at hdbl
        have hbin:=(q97 wU (un n) (un k) (by simp [un];omega) (by rw [un_length];exact hfact_b)).2
        simp only [un_length] at hbin
        have hdot:=(q166 n wU Z hZlen hfact_b hst_b k (by omega)).2
        have hm1':=q55 wU (q81 wU (un k)) (q107 wU (un n) (un k))
        rw [hbin] at hm1'
        have hm1:((val (mulW wU (q81 wU (un k)) (q107 wU (un n) (un k))):ℤ) ≡
            (q9 k:ℤ) * (n.choose k:ℤ) [ZMOD (2:ℤ) ^ W]) :=
          hm1'.trans (hdbl.mul_right (n.choose k:ℤ))
        have hm2:=(q55 wU _ (q136 wU rest (un n) (un k))).trans (hm1.mul hdot)
        rw [Finset.sum_range_succ]
        exact (q98 wU acc _).trans (hmod.add hm2)
    obtain ⟨acc,h1,hlen,hmod⟩:=hiter (n+1) le_rfl
    rw [List.length_cons,un_length,h1]
    simp only [unpairB_pairB]
    dsimp only [q112,q27]
    rw [un_length]
    by_cases hodd:n % 2=1
    · have hpow1:(-1:ℤ) ^ n = -1:=by
        have:n=2 * (n / 2)+1:=by omega
        rw [this,pow_add,pow_mul];norm_num
      simp only [hodd,↓reduceIte,sel,List.cons_ne_nil,hpow1,neg_mul,one_mul]
      exact ⟨q197 _ _,(q113 wU acc).trans hmod.neg⟩
    · have hpow0:(-1:ℤ) ^ n=1:=by
        have:n=2 * (n / 2):=by omega
        rw [this,pow_mul];norm_num
      simp only [hodd,↓reduceIte,sel,hpow0,one_mul]
      exact ⟨hlen,hmod⟩
  have hperm_le:B.permanent ≤ n.factorial:=by
    rw [Matrix.permanent]
    calc ∑ σ : Equiv.Perm (Fin n),∏ i:Fin n,B (σ i) i
        ≤ ∑ _σ : Equiv.Perm (Fin n),1:=Finset.sum_le_sum fun σ _=>by
          have h1:∀ i:Fin n,B (σ i) i ≤ 1:=fun i=>by dsimp only [B];cases A (σ i) i <;> simp
          exact Finset.prod_le_one (fun i _=>h1 i)
      _=(Finset.univ:Finset (Equiv.Perm (Fin n))).card:=by simp
      _=n.factorial:=by rw [Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
  have hnum_lt:2 ^ (2 * n) * n.factorial * B.permanent < 2 ^ W:=by
    have h1:=q65 n
    have h2:2 ^ (2 * n) * n.factorial * B.permanent ≤ 2 ^ (2 * n) * 2 ^ (n * n) * 2 ^ (n * n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (hperm_le.trans h1)
    rw [← pow_add,← pow_add] at h2
    have hexp:2 * n+n * n+n * n < W:=by nlinarith
    exact lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by omega) hexp)
  have hden_2lt:2 * (2 ^ (2 * n) * n.factorial) < 2 ^ W:=by
    have h1:=q65 n
    have h2:2 * (2 ^ (2 * n) * n.factorial) ≤ 2 ^ (1+2 * n+n * n):=by
      rw [pow_add,pow_add,pow_one,mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
    have hexp:1+2 * n+n * n < W:=by nlinarith
    exact lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by omega) hexp)
  have hnum_eq:val (q88 wU (un n) rest)=2 ^ (2 * n) * n.factorial * B.permanent:=by
    have hmod:=hdecW.2
    rw [hdec] at hmod
    have hnat:val (q88 wU (un n) rest) ≡ 2 ^ (2 * n) * n.factorial * B.permanent [MOD 2 ^ W]:=by
      exact_mod_cast hmod
    have hlt1:val (q88 wU (un n) rest) < 2 ^ W:=by rw [← hdecW.1];exact q124 _
    rw [Nat.ModEq,Nat.mod_eq_of_lt hlt1,Nat.mod_eq_of_lt hnum_lt] at hnat
    exact hnat
  have hden_eq:val (mulW wU (powW wU (natW wU [true,true]) (un n++un n)) (factW wU (un n))) =
      2 ^ (2 * n) * n.factorial:=by
    have h2eq:val (natW wU [true,true])=2:=by
      rw [q114];simp only [List.length_cons,List.length_nil]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (by norm_num:2 < 2 ^ 2) (Nat.pow_le_pow_right (by omega) (by omega)))
    have hpow_eq:val (powW wU (natW wU [true,true]) (un n++un n))=2 ^ (2 * n):=by
      rw [(q178 wU _ _).2,h2eq]
      have hlen:(un n++un n).length=2 * n:=by simp [un];omega
      rw [hlen,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by nlinarith))]
    have hf_eq:val (factW wU (un n))=n.factorial:=by
      rw [(q72 wU (un n)).2,un_length]
      exact Nat.mod_eq_of_lt (by dsimp only [W] at hfact_b;omega)
    rw [q115,hpow_eq,hf_eq]
    exact Nat.mod_eq_of_lt (by dsimp only [W] at hden_2lt;omega)
  have hdiv:=q147 wU (q88 wU (un n) rest)
    (mulW wU (powW wU (natW wU [true,true]) (un n++un n)) (factW wU (un n)))
    (by rw [hnum_eq];exact hnum_lt)
    (by rw [hden_eq];positivity)
    (by rw [hden_eq];exact hden_2lt)
  rw [q109,hdiv.2,hnum_eq,hden_eq,Nat.mul_div_cancel_left _ (by positivity)]
end
end PEqualNP.Outside.L_meta_32050
theorem PEqualNP.Outside.L_meta_32050 : (let header := fun n : Nat => List.replicate n true ++ [false]
let frame := fun xs : List Bool => xs.flatMap (fun b => [true,b]) ++ [false]
let field := fun (k z : Nat) => (List.range (k.log2+1)).map (fun h => z.testBit h)
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)
let I := fun k : Nat => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}
∃ write read : List Bool → List Bool, fast write ∧ fast read ∧
  ∀ (n : Nat), 0 < n → ∀ A : Fin n → Fin n → Bool,
    let B : Matrix (Fin n) (Fin n) Nat := fun i j => (A i j).toNat
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))
    let ones := cells.filter (fun z => A z.1 z.2)
    let rows := ones.zipIdx.flatMap (fun z => let p := 2*n+2*z.2
      [[p,p+1,z.1.1.val],[p,p+1,n+z.1.2.val]])
    let size := fun t : Fin (n+1) => 2*n+2*ones.length+t.val
    let query := fun t : Fin (n+1) => let k := size t
      header k ++ rows.flatMap (fun R => R.flatMap (field k))
    let Z := fun t : Fin (n+1) => let k := size t
      let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
      Nat.card {f : Fn // (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k ∧
        PEqualNP.Represents.Represents (fun i j : Fin k => decide (i=j)) C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
        ∀ R ∈ rows, f (fun i => decide (i.val ∈ R)) (fun _ => false) = true}
    let J : Matrix (Fin (n+1)) (Fin (n+1)) Int := fun t j => (I (t.val+2*j.val) : Int)
    let delta := (2 : Int)^(n*(n+1)/2) * ∏ j : Fin (n+1), (j.val.factorial : Int)
    write (header n ++ cells.map (fun z => A z.1 z.2)) =
      (List.finRange (n+1)).flatMap (fun t => frame (query t)) ∧
    rows.length = 2*ones.length ∧ (∀ R ∈ rows, R.length = 3 ∧ R.Nodup) ∧
    (∀ t, 0 < Z t) ∧ J.det = delta ∧
    (J.updateCol 0 (fun t => (Z t : Int))).det = delta * 2^n * (B.permanent : Int) ∧
    read (header n ++ (List.finRange (n+1)).flatMap (fun t => frame (Z t).bits)) = B.permanent.bits) := by
  refine ⟨PEqualNP.Outside.L_meta_32050.writeFn, PEqualNP.Outside.L_meta_32050.readFn,
    PEqualNP.Outside.L_meta_32050.cpt_to_fast PEqualNP.Outside.L_meta_32050.cpt_writeFn,
    PEqualNP.Outside.L_meta_32050.cpt_to_fast PEqualNP.Outside.L_meta_32050.cpt_readFn, ?_⟩
  intro n hn A
  have hmb := PEqualNP.Outside.L_meta_32050.math_bridge n hn A
  refine ⟨PEqualNP.Outside.L_meta_32050.writeFn_spec n hn A,
    hmb.1, hmb.2.1, hmb.2.2.1, hmb.2.2.2.1, hmb.2.2.2.2.1, ?_⟩
  exact PEqualNP.Outside.L_meta_32050.readFn_spec n A _ hmb.2.2.2.2.2
