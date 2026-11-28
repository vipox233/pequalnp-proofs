import Mathlib
import PEqualNP.Defs

-- Machine routines ported from lean/PEqualNP/Outside/L_meta_32050.lean at
-- 028e3e4ddd2da65f69b2c0c6ffad3ab1bf2092b9; scope renamed and graph reduction omitted.
namespace PEqualNP.Outside.L_meta_33604_aux.Writer
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
open Classical
open PEqualNP.Library Lib.Machines Lib.Universal Lib.Machines.Rev
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

open PEqualNP.Library Lib.Machines Lib.Universal

private def loopStep (f : List Bool → List Bool) (z : List Bool) : List Bool :=
  let a := unpairB z
  let b := unpairB a.2
  let c := unpairB b.2
  pairB a.1 (pairB b.1 (pairB (true :: c.1) (c.2 ++ takeN a.1 (f (pairB b.1 c.1)))))

private def boundedMap (f : List Bool → List Bool) (cap env cnt : List Bool) : List Bool :=
  let z := (loopStep f)^[cnt.length] (pairB cap (pairB env (pairB [] [])))
  (unpairB (unpairB (unpairB z).2).2).2

private theorem boundedMap_cpt {f cap env cnt : List Bool → List Bool}
    (hf : CPTs f) (hc : CPTs cap) (he : CPTs env) (hn : CPTs cnt) :
    CPTs (fun s => boundedMap f (cap s) (env s) (cnt s)) := by
  have h1 := cpt_unpairB1
  have h2 := cpt_unpairB2
  have he' := cpt_comp h2 h1
  have hb := cpt_comp h2 h2
  have hi := cpt_comp hb h1
  have ha := cpt_comp hb h2
  have step : CPTs (loopStep f) :=
    cpt_pairB2 h1 (cpt_pairB2 he' (cpt_pairB2 (cpt_app2 (cpt_const [true]) hi)
      (cpt_app2 ha (q24 h1 (cpt_comp (cpt_pairB2 he' hi) hf)))))
  have go := q18 5 step
    (fun s => by simp only [loopStep, unpairB_pairB]) (fun s => by
      dsimp only [loopStep]
      generalize ha : unpairB s = a
      generalize hb : unpairB a.2 = b
      generalize hc : unpairB b.2 = c
      have h1 := q0 s
      have h2 := q0 a.2
      have h3 := q0 b.2
      rw [ha] at h1
      rw [hb] at h2
      rw [hc] at h3
      have h4 : (takeN a.1 (f (pairB b.1 c.1))).length ≤ a.1.length := by
        rw [q12, List.length_take]
        exact Nat.min_le_left _ _
      rw [q7, q7, q7, List.length_cons, List.length_append]
      omega) hn (cpt_pairB2 hc (cpt_pairB2 he (cpt_const (pairB [] []))))
  exact cpt_comp (cpt_comp (cpt_comp go h2) h2) h2

private theorem boundedMap_spec (f : List Bool → List Bool) (cap env cnt : List Bool) :
    boundedMap f cap env cnt = (List.range cnt.length).flatMap
      (fun i => takeN cap (f (pairB env (un i)))) := by
  have run (k : ℕ) : (loopStep f)^[k] (pairB cap (pairB env (pairB [] []))) =
      pairB cap (pairB env (pairB (un k)
        ((List.range k).flatMap (fun i => takeN cap (f (pairB env (un i))))))) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [loopStep, unpairB_pairB, List.range_succ, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, un_succ]
  simp only [boundedMap, run, unpairB_pairB]

private abbrev Bits := List Bool
private abbrev cpt₂ (f : Bits → Bits → Bits) :=
  CPTs (fun z => f (unpairB z).1 (unpairB z).2)

private theorem call₂ {f : Bits → Bits → Bits} {a b : Bits → Bits}
    (hf : cpt₂ f) (ha : CPTs a) (hb : CPTs b) : CPTs (fun z => f (a z) (b z)) :=
  q39 (cpt_comp (cpt_pairB2 ha hb) hf) (fun z => by simp [unpairB_pairB])

private def flag (b : Bool) : Bits := if b then [true] else []

private theorem flag_cases (b : Bool) : flag b = [] ↔ b = false := by
  cases b <;> decide

private def flagOr (a b : Bits) : Bits := sel a (sel b [] [true]) [true]
private def flagAnd (a b : Bits) : Bits := sel a [] (sel b [] [true])
private def flagNot (a : Bits) : Bits := sel a [true] []
private def flagLt (a b : Bits) : Bits := flagNot (flagNot (dropN' a b))
private def bitAt (a b : Bits) : Bits := q17 (dropN' a b)

private theorem flagOr_cpt : cpt₂ flagOr :=
  cpt_sel cpt_unpairB1 (cpt_sel cpt_unpairB2 (cpt_const []) (cpt_const [true])) (cpt_const [true])
private theorem flagAnd_cpt : cpt₂ flagAnd :=
  cpt_sel cpt_unpairB1 (cpt_const []) (cpt_sel cpt_unpairB2 (cpt_const []) (cpt_const [true]))
private theorem flagLt_cpt : cpt₂ flagLt :=
  cpt_comp (cpt_comp (cpt_dropN' cpt_unpairB1 cpt_unpairB2) q138) q138
private theorem bitAt_cpt : cpt₂ bitAt :=
  cpt_comp (cpt_dropN' cpt_unpairB1 cpt_unpairB2) q35

private theorem flagOr_spec (a b : Bool) : flagOr (flag a) (flag b) = flag (a || b) := by
  cases a <;> cases b <;> decide
private theorem flagAnd_spec (a b : Bool) : flagAnd (flag a) (flag b) = flag (a && b) := by
  cases a <;> cases b <;> decide
private theorem flagNot_spec (a : Bool) : flagNot (flag a) = flag (!a) := by
  cases a <;> decide
private theorem flagLt_spec (a b : Bits) : flagLt a b = flag (decide (a.length < b.length)) := by
  by_cases h : a.length < b.length
  · have ne : dropN' a b ≠ [] := by simpa [q40, List.drop_eq_nil_iff] using h
    simp [flagLt, flagNot, sel, ne, flag, h]
  · have eq : dropN' a b = [] := by simpa [q40, List.drop_eq_nil_iff] using Nat.le_of_not_gt h
    simp [flagLt, flagNot, sel, eq, flag, h]

private theorem bitAt_spec (a b : Bits) : bitAt a b = flag (b.getD a.length false) := by
  rw [show b.getD a.length false = (b.drop a.length).getD 0 false by simp]
  unfold bitAt
  rw [q40]
  cases b.drop a.length with
  | nil => rfl
  | cons v l => cases v <;> rfl

private def flagAny (f : Bits → Bits) (env cnt : Bits) : Bits :=
  flagNot (flagNot (boundedMap f [true] env cnt))

private theorem flagAny_cpt {f env cnt : Bits → Bits}
    (hf : CPTs f) (he : CPTs env) (hn : CPTs cnt) :
    CPTs (fun z => flagAny f (env z) (cnt z)) :=
  cpt_comp (cpt_comp (boundedMap_cpt hf (cpt_const [true]) he hn) q138) q138

private theorem flagAny_spec (f : Bits → Bits) (env cnt : Bits) (b : ℕ → Bool)
    (h : ∀ i < cnt.length, f (pairB env (un i)) = flag (b i)) :
    flagAny f env cnt = flag (decide (∃ i < cnt.length, b i = true)) := by
  have eq : (List.range cnt.length).flatMap (fun i => takeN [true] (f (pairB env (un i)))) =
      (List.range cnt.length).flatMap (fun i => flag (b i)) := by
    apply List.flatMap_congr
    intro i hi
    rw [h i (List.mem_range.mp hi), q12]
    cases b i <;> rfl
  have empty : ((List.range cnt.length).flatMap (fun i => flag (b i))) = [] ↔
      ¬ ∃ i < cnt.length, b i = true := by
    simp only [List.flatMap_eq_nil_iff, List.mem_range, flag_cases, not_exists, not_and]
    exact forall_congr' fun i => forall_congr' fun _ => Bool.eq_false_iff
  rw [flagAny, boundedMap_spec, eq]
  by_cases yes : ∃ i < cnt.length, b i = true
  · have ne : ((List.range cnt.length).flatMap (fun i => flag (b i))) ≠ [] := fun h => empty.mp h yes
    simp [flagNot, sel, ne, flag, yes]
  · simp [flagNot, sel, empty.mpr yes, flag, yes]

private inductive Expr
  | lit : Bits → Expr
  | arg : Expr
  | outer : Expr → Expr
  | head : Expr → Expr
  | strip : Expr → Expr
  | append : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | drop : Expr → Expr → Expr
  | get : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | bor : Expr → Expr → Expr
  | band : Expr → Expr → Expr
  | bnot : Expr → Expr
  | select : Expr → Expr → Expr → Expr
  | map : Expr → Expr → Expr → Expr
  | any : Expr → Expr → Expr

private def Expr.run : Expr → Bits → Bits
  | .lit b, _ => b
  | .arg, env => (unpairB env).2
  | .outer e, env => e.run (unpairB env).1
  | .head e, env => hd (e.run env)
  | .strip e, env => dropN (e.run env)
  | .append a b, env => a.run env ++ b.run env
  | .mul a b, env => mulU (a.run env) (b.run env)
  | .drop a b, env => dropN' (a.run env) (b.run env)
  | .get a b, env => bitAt (a.run env) (b.run env)
  | .lt a b, env => flagLt (a.run env) (b.run env)
  | .bor a b, env => flagOr (a.run env) (b.run env)
  | .band a b, env => flagAnd (a.run env) (b.run env)
  | .bnot a, env => flagNot (a.run env)
  | .select a b c, env => sel (a.run env) (b.run env) (c.run env)
  | .map cap cnt body, env => boundedMap body.run (cap.run env) env (cnt.run env)
  | .any cnt body, env => flagAny body.run env (cnt.run env)

private theorem Expr.fast (e : Expr) : CPTs e.run := by
  induction e with
  | lit b => exact cpt_const b
  | arg => exact cpt_unpairB2
  | outer _ h => simpa only [Expr.run] using cpt_comp cpt_unpairB1 h
  | head _ h => simpa only [Expr.run] using cpt_comp h cpt_hd
  | strip _ h => simpa only [Expr.run] using cpt_comp h cpt_dropN
  | append _ _ ha hb => exact cpt_app2 ha hb
  | mul _ _ ha hb => exact q42 ha hb
  | drop _ _ ha hb => exact cpt_dropN' ha hb
  | get _ _ ha hb => exact call₂ bitAt_cpt ha hb
  | lt _ _ ha hb => exact call₂ flagLt_cpt ha hb
  | bor _ _ ha hb => exact call₂ flagOr_cpt ha hb
  | band _ _ ha hb => exact call₂ flagAnd_cpt ha hb
  | bnot _ ha => simpa only [Expr.run, flagNot, q133] using cpt_comp ha q138
  | select _ _ _ ha hb hc => exact cpt_sel ha hb hc
  | map _ _ _ hc hn hb => exact boundedMap_cpt hb hc cpt_id hn
  | any _ _ hn hb => exact flagAny_cpt hb cpt_id hn

private def readS (input : Expr) := input.head
private def readN (input : Expr) := input.strip.head
private def readP (input : Expr) := input.strip.strip.head
private def readPB (input : Expr) := input.strip.strip.strip
private def negHeader (input : Expr) := ((readP input).mul (readN input)).drop (readPB input)
private def readQ (input : Expr) := (negHeader input).head
private def readQB (input : Expr) := (negHeader input).strip
private def afterRows (input : Expr) :=
  ((readQ input).mul ((readN input).append (readN input))).drop (readQB input)

private def xFlag (input i : Expr) := i.get (afterRows input)
private def branchFlag (input i : Expr) :=
  let n := readN input
  (xFlag input i).select (i.get (n.drop (afterRows input)))
    (i.get ((n.append n).drop (afterRows input)))

private def negA (input index : Expr) :=
  (index.mul ((readN input).append (readN input))).drop (readQB input)
private def negB (input index : Expr) := (readN input).drop (negA input index)
private def badNegative (input : Expr) :=
  (readQ input).any ((readN input.outer).any
    ((Expr.arg.get (negA input.outer.outer (Expr.arg.outer))).band
      (Expr.arg.get (negB input.outer.outer (Expr.arg.outer)))))

private def edgeFlag (input i j : Expr) :=
  let bad := (readQ input).any
    (((i.outer.get (negA input.outer .arg)).band (j.outer.get (negA input.outer .arg))).bor
      ((i.outer.get (negB input.outer .arg)).band (j.outer.get (negB input.outer .arg))))
  ((i.lt j).bor (j.lt i)).band bad.bnot

private def posBank (input row : Expr) := (row.mul (readN input)).drop (readPB input)
private def inside (input row i j : Expr) := (i.get (posBank input row)).band (j.get (posBank input row))
private def neqFlag (i j : Expr) := (i.lt j).bor (j.lt i)
private def crossEdge (input i j : Expr) :=
  (edgeFlag input i j).band ((branchFlag input i).bnot.band (branchFlag input j))
private def someCross (input row : Expr) (extra : Expr → Expr → Expr) :=
  (readN input).any ((readN input.outer).any
    (let i := Expr.arg.outer
     let j := Expr.arg
     ((crossEdge input.outer.outer i j).band (inside input.outer.outer row.outer.outer i j)).band (extra i j)))
private def emptyPositive (input : Expr) :=
  (readP input).any ((someCross input.outer .arg (fun _ _ => .lit [true])).bnot)
private def optionalAt (input row v : Expr) :=
  someCross input row (fun i j => (neqFlag v.outer.outer i).band (neqFlag v.outer.outer j))
private def compulsory (input v : Expr) :=
  (readP input).any ((optionalAt input.outer .arg v.outer).bnot)
private def restrictEdge (input i j : Expr) :=
  (readP input).any
    ((inside input.outer .arg i.outer j.outer).bnot.band
      ((optionalAt input.outer .arg i.outer).bnot.bor (optionalAt input.outer .arg j.outer).bnot))

private def cell (input i j : Expr) :=
  let n := readN input
  let on := Expr.lit [true,false]
  let off := Expr.lit [false,false]
  let two := Expr.lit [false,true]
  let oldOld := ((crossEdge input i j).band (restrictEdge input i j).bnot).select off
    (((xFlag input i).bor (xFlag input j)).select on two)
  let oldNew := ((branchFlag input i).bnot.band (compulsory input i)).select on off
  let newOld := ((branchFlag input j).band (compulsory input j)).select on off
  ((badNegative input).bor (emptyPositive input)).select
    ((i.lt n).select ((j.lt n).select off newOld) ((j.lt n).select oldNew oldOld)) off

private def writerExpr : Expr :=
  let n := readN .arg
  let d := (readS .arg).drop (n.append n)
  .map (d.append d) d (.map (.lit [true,true]) d.outer (cell (.outer (.outer .arg)) (.outer .arg) .arg))

private def writer (input : Bits) : Bits := writerExpr.run (pairB [] input)

set_option maxHeartbeats 2000000 in
private theorem writer_fast :
    ∃ M : Turing.TM2ComputableInPolyTime (fun x : Bits => x) (fun x : Bits => x) writer,
      ∀ i, Finite (M.tm.Γ i) :=
  cpt_to_fast (f := writer) (show CPTs (fun x => writerExpr.run (pairB [] x)) from
    cpt_comp (cpt_pairB2 (cpt_const []) cpt_id) writerExpr.fast)

private def rawHeader (n : ℕ) := un n ++ [false]

private theorem hd_header (n : ℕ) (tail : Bits) : hd (rawHeader n ++ tail) = un n := by
  simp [hd, rawHeader, un]

private theorem strip_header (n : ℕ) (tail : Bits) : dropN (rawHeader n ++ tail) = tail := by
  simp [dropN, rawHeader, un]

private def cellBits (input : Bits) (i j : ℕ) :=
  (cell (.outer (.outer .arg)) (.outer .arg) .arg).run
    (pairB (pairB (pairB [] input) (un i)) (un j))

private theorem cellBits_choices (input : Bits) (i j : ℕ) :
    cellBits input i j = [false,false] ∨ cellBits input i j = [true,false] ∨ cellBits input i j = [false,true] := by
  let good (a : Bits) := a = [false,false] ∨ a = [true,false] ∨ a = [false,true]
  change good (cellBits input i j)
  have pick (f a b : Bits) (ha : good a) (hb : good b) : good (sel f a b) := by
    unfold sel
    split_ifs <;> assumption
  unfold cellBits cell
  simp only [Expr.run]
  repeat' first | apply pick | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

private theorem cellBits_len (input : Bits) (i j : ℕ) : (cellBits input i j).length = 2 := by
  obtain h | h | h := cellBits_choices input i j <;> rw [h] <;> rfl

private def rawMatrix (input : Bits) (d : ℕ) : Matrix (Fin d) (Fin d) Nat :=
  fun i j => ((cellBits input i j).getD 0 false).toNat
      + 2 * ((cellBits input i j).getD 1 false).toNat

private theorem cellBits_matrix (input : Bits) (d : ℕ) (i j : Fin d) :
    rawMatrix input d i j ≤ 2 ∧
    cellBits input i j = [(rawMatrix input d i j).testBit 0, (rawMatrix input d i j).testBit 1] := by
  obtain h | h | h := cellBits_choices input i j <;>
    rw [rawMatrix, h] <;> decide

private theorem flat_length {α β : Type*} (f : α → List β) (k : ℕ)
    (h : ∀ a, (f a).length = k) (l : List α) :
    (l.flatMap f).length = l.length*k := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih, h, Nat.succ_mul, Nat.add_comm]

private theorem writer_shape (s n : ℕ) (tail : Bits) :
    let input := rawHeader s ++ (rawHeader n ++ tail)
    let d := 2*n-s
    writer input = (List.range d).flatMap (fun i => (List.range d).flatMap (cellBits input i)) := by
  intro input d
  have cnt : ((readS .arg).drop ((readN .arg).append (readN .arg))).run (pairB [] input) = un d := by
    simp only [Expr.run, readS, readN, unpairB_pairB, input, hd_header, strip_header, q40, un_length, un]
    rw [List.replicate_append_replicate, List.drop_replicate]
    simp [d, two_mul]
  simp only [Expr.run] at cnt
  unfold writer writerExpr
  simp only [Expr.run, cnt, boundedMap_spec, List.length_append, un_length, unpairB_pairB]
  apply List.flatMap_congr
  intro i hi
  have row : ((List.range d).flatMap
      (fun j => takeN [true,true] (cellBits input i j))) = (List.range d).flatMap (cellBits input i) := by
    apply List.flatMap_congr
    intro j hj
    rw [q12]
    exact List.take_of_length_le (by rw [cellBits_len]; decide)
  change takeN (un d ++ un d) ((List.range d).flatMap
      (fun j => takeN [true,true] (cellBits input i j))) = _
  rw [row, q12, List.take_of_length_le]
  rw [flat_length _ 2 (cellBits_len input i), List.length_range, List.length_append, un_length]
  omega

private theorem writer_serializes (s n : ℕ) (tail : Bits) :
    let input := rawHeader s ++ (rawHeader n ++ tail)
    let d := 2*n-s
    (∀ i j, rawMatrix input d i j ≤ 2) ∧
      writer input = (List.finRange d).flatMap (fun i => (List.finRange d).flatMap (fun j =>
        [(rawMatrix input d i j).testBit 0, (rawMatrix input d i j).testBit 1])) := by
  intro input d
  refine ⟨fun i j => (cellBits_matrix input d i j).1, ?_⟩
  have range : (List.finRange d).map Fin.val = List.range d := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  rw [show writer input = (List.range d).flatMap (fun i => (List.range d).flatMap (cellBits input i))
    from writer_shape s n tail]
  rw [← range, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  change ((List.finRange d).map Fin.val).flatMap (cellBits input i) = _
  rw [List.flatMap_map]
  exact List.flatMap_congr fun j _ => (cellBits_matrix input d i j).2

end PEqualNP.Outside.L_meta_33604_aux.Writer


namespace PEqualNP.Outside.L_meta_33604_aux.Core

private theorem bank_length {α β : Type*} (rows : List α) (bank : α → List β) (width : ℕ)
    (h : ∀ a ∈ rows, (bank a).length = width) : (rows.flatMap bank).length = rows.length * width := by
  induction rows with
  | nil => simp
  | cons a as ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp), ih (fun b hb => h b (by simp [hb])),
      List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem bank_skip {α β : Type*} (rows : List α) (bank : α → List β) (width : ℕ)
    (h : ∀ a ∈ rows, (bank a).length = width) (tail : List β) :
    (rows.flatMap bank ++ tail).drop (rows.length * width) = tail := by
  rw [← bank_length rows bank width h]
  simp

private theorem bank_access {α β : Type*} (rows : List α) (bank : α → List β) (width : ℕ)
    (h : ∀ a ∈ rows, (bank a).length = width) (tail : List β) (z : β) :
    ∀ (i j : ℕ) (hi : i < rows.length), j < width →
      (rows.flatMap bank ++ tail).getD (i * width + j) z = (bank rows[i]).getD j z := by
  induction rows with
  | nil => intro i j hi hj; simp at hi
  | cons a as ih =>
    intro i j hi hj
    have ha : (bank a).length = width := h a (by simp)
    cases i with
    | zero =>
      simp only [List.flatMap_cons, List.append_assoc, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (by omega)
    | succ i =>
      have bound : i < as.length := by simpa using hi
      have cut : (i+1)*width + j - (bank a).length = i*width+j := by rw [Nat.succ_mul, ha]; omega
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by rw [Nat.succ_mul, ha]; omega), cut]
      exact ih (fun b hb => h b (by simp [hb])) i j bound hj

private def bankBits {n : ℕ} (R : Finset (Fin n)) : List Bool :=
  (List.finRange n).map fun i => decide (i ∈ R)

private theorem bankBits_get {n : ℕ} (R : Finset (Fin n)) (i : Fin n) :
    (bankBits R).getD i false = decide (i ∈ R) := by
  simp [bankBits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, i.isLt]

end PEqualNP.Outside.L_meta_33604_aux.Core


namespace PEqualNP.Outside.L_meta_33604_aux.Core

private def blocks {A B C : Type*} (p : Equiv.Perm (A ⊕ (B ⊕ C))) : Prop :=
  (∀ a, p (.inl a) = .inl a) ∧
  (∀ b, ∃ b', p (.inr (.inl b)) = .inr (.inl b')) ∧
  (∀ c, ∃ c', p (.inr (.inr c)) = .inr (.inr c'))

private theorem dummy_factor (A B C : Type*) [Finite B] [Finite C] :
    Nat.card {p : Equiv.Perm (A ⊕ (B ⊕ C)) // blocks p} = (Nat.card B).factorial * (Nat.card C).factorial := by
  classical
  let build (g : Equiv.Perm B × Equiv.Perm C) : {p : Equiv.Perm (A ⊕ (B ⊕ C)) // blocks p} :=
    ⟨Equiv.sumCongr (Equiv.refl A) (Equiv.sumCongr g.1 g.2),
      fun _ => rfl, fun b => ⟨g.1 b,rfl⟩, fun c => ⟨g.2 c,rfl⟩⟩
  have hbij : Function.Bijective build := by
    constructor
    · intro g h eq
      have same := congrArg Subtype.val eq
      apply Prod.ext
      · apply Equiv.ext
        intro b
        exact Sum.inl.inj (Sum.inr.inj (congrFun (congrArg Equiv.toFun same) (.inr (.inl b))))
      · apply Equiv.ext
        intro c
        exact Sum.inr.inj (Sum.inr.inj (congrFun (congrArg Equiv.toFun same) (.inr (.inr c))))
    · rintro ⟨p,pa,pb,pc⟩
      let g (b : B) := Classical.choose (pb b)
      have hg (b : B) : p (.inr (.inl b)) = .inr (.inl (g b)) := Classical.choose_spec (pb b)
      let h (c : C) := Classical.choose (pc c)
      have hh (c : C) : p (.inr (.inr c)) = .inr (.inr (h c)) := Classical.choose_spec (pc c)
      have gb : Function.Bijective g := by
        constructor
        · intro i j eq
          have im : p (.inr (.inl i)) = p (.inr (.inl j)) := by rw [hg i, hg j, eq]
          exact Sum.inl.inj (Sum.inr.inj (p.injective im))
        · intro b
          obtain ⟨x,hx⟩ := p.surjective (.inr (.inl b))
          rcases x with a | (i | c)
          · rw [pa a] at hx
            contradiction
          · exact ⟨i, Sum.inl.inj (Sum.inr.inj ((hg i).symm.trans hx))⟩
          · rw [hh c] at hx
            have inner : (Sum.inr (h c) : B ⊕ C) = Sum.inl b := Sum.inr.inj hx
            cases inner
      have hc : Function.Bijective h := by
        constructor
        · intro i j eq
          have im : p (.inr (.inr i)) = p (.inr (.inr j)) := by rw [hh i, hh j, eq]
          exact Sum.inr.inj (Sum.inr.inj (p.injective im))
        · intro c
          obtain ⟨x,hx⟩ := p.surjective (.inr (.inr c))
          rcases x with a | (b | i)
          · rw [pa a] at hx
            contradiction
          · rw [hg b] at hx
            have inner : (Sum.inl (g b) : B ⊕ C) = Sum.inr c := Sum.inr.inj hx
            cases inner
          · exact ⟨i, Sum.inr.inj (Sum.inr.inj ((hh i).symm.trans hx))⟩
      refine ⟨⟨Equiv.ofBijective g gb,Equiv.ofBijective h hc⟩, Subtype.ext (Equiv.ext ?_)⟩
      rintro (a | (b | c))
      · exact (pa a).symm
      · exact (hg b).symm
      · exact (hh c).symm
  rw [← Nat.card_congr (Equiv.ofBijective build hbij), Nat.card_prod, Nat.card_perm, Nat.card_perm]

private def extendsMatch {U D : Type*} {P Q : U → Prop} (m : Subtype P ≃ Subtype Q)
    (g : Equiv.Perm (U ⊕ D)) : Prop :=
  (∀ u : Subtype P, g (.inl u.1) = .inl (m u).1) ∧
  (∀ u : {u // ¬P u}, ∃ j : D, g (.inl u.1) = .inr j) ∧
  (∀ i : D, ∃ v : {v // ¬Q v}, g (.inr i) = .inl v.1)

private theorem extension_factor {U D : Type*} [Finite D] {P Q : U → Prop}
    (m : Subtype P ≃ Subtype Q) (pb : {u // ¬P u} ≃ D) (qb : D ≃ {v // ¬Q v}) :
    Nat.card {g : Equiv.Perm (U ⊕ D) // extendsMatch m g} = (Nat.card D).factorial ^ 2 := by
  classical
  let A := Subtype P
  let dom : A ⊕ (D ⊕ D) ≃ U ⊕ D :=
    ((Equiv.refl A).sumCongr (pb.symm.sumCongr (Equiv.refl D))).trans
      ((Equiv.sumAssoc A {u // ¬P u} D).symm.trans ((Equiv.sumCompl P).sumCongr (Equiv.refl D)))
  let cod : A ⊕ (D ⊕ D) ≃ U ⊕ D :=
    (m.sumCongr ((Equiv.refl D).sumCongr qb)).trans
      (((Equiv.refl (Subtype Q)).sumCongr (Equiv.sumComm D {v // ¬Q v})).trans
        ((Equiv.sumAssoc (Subtype Q) {v // ¬Q v} D).symm.trans
          ((Equiv.sumCompl Q).sumCongr (Equiv.refl D))))
  have da (a : A) : dom (.inl a) = .inl a.1 := rfl
  have db (b : D) : dom (.inr (.inl b)) = .inl (pb.symm b).1 := rfl
  have dc (c : D) : dom (.inr (.inr c)) = .inr c := rfl
  have ca (a : A) : cod (.inl a) = .inl (m a).1 := rfl
  have cb (b : D) : cod (.inr (.inl b)) = .inr b := rfl
  have cc (c : D) : cod (.inr (.inr c)) = .inl (qb c).1 := rfl
  let align : Equiv.Perm (A ⊕ (D ⊕ D)) ≃ Equiv.Perm (U ⊕ D) := Equiv.equivCongr dom cod
  have alignment (p : Equiv.Perm (A ⊕ (D ⊕ D))) (x : A ⊕ (D ⊕ D)) :
      align p (dom x) = cod (p x) := by simp [align]
  have test (p : Equiv.Perm (A ⊕ (D ⊕ D))) : blocks p ↔ extendsMatch m (align p) := by
    constructor
    · rintro ⟨sa,sb,sc⟩
      refine ⟨fun a => ?_,fun u => ?_,fun c => ?_⟩
      · rw [← da, alignment, sa, ca]
      · obtain ⟨b,hb⟩ := sb (pb u)
        refine ⟨b,?_⟩
        have e := alignment p (.inr (.inl (pb u)))
        simpa only [db, pb.symm_apply_apply, hb, cb] using e
      · obtain ⟨j,hj⟩ := sc c
        refine ⟨qb j,?_⟩
        have e := alignment p (.inr (.inr c))
        simpa only [dc, hj, cc] using e
    · rintro ⟨sa,sb,sc⟩
      refine ⟨fun a => ?_,fun b => ?_,fun c => ?_⟩
      · apply cod.injective
        rw [← alignment, da, sa, ca]
      · obtain ⟨j,hj⟩ := sb (pb.symm b)
        refine ⟨j,cod.injective ?_⟩
        rwa [← alignment, db, cb]
      · obtain ⟨v,hv⟩ := sc c
        refine ⟨qb.symm v,cod.injective ?_⟩
        rwa [← alignment, dc, cc, qb.apply_symm_apply]
  rw [← Nat.card_congr (align.subtypeEquiv test), dummy_factor, pow_two]

end PEqualNP.Outside.L_meta_33604_aux.Core


namespace PEqualNP.Outside.L_meta_33604_aux.Core

private def oldPart {U D : Type*} (g : Equiv.Perm (U ⊕ D)) (c : U → Bool) (i : U) : U :=
  match (if c i then g else g.symm) (.inl i) with
  | .inl j => j
  | .inr _ => i

private theorem oldPart_laws {U D : Type*} (g : Equiv.Perm (U ⊕ D)) (c : U → Bool)
    (cross : ∀ i j, g (.inl j) = .inl i → c i = false ∧ c j = true) :
    Function.Involutive (oldPart g c) ∧
      ∀ i j, g (.inl j) = .inl i ↔ c j = true ∧ oldPart g c j = i ∧ i ≠ j := by
  have forward (i j : U) (e : g (.inl j) = .inl i) :
      c i = false ∧ c j = true ∧ oldPart g c i = j ∧ oldPart g c j = i ∧ i ≠ j := by
    obtain ⟨hi,hj⟩ := cross i j e
    have rev : g.symm (.inl i) = .inl j := (g.symm_apply_eq).mpr e.symm
    refine ⟨hi,hj,?_,?_,?_⟩
    · simp [oldPart, hi, rev]
    · simp [oldPart, hj, e]
    · intro eq
      subst j
      simp_all
  constructor
  · intro i
    cases hi : c i
    · cases val : g.symm (.inl i) with
      | inl j =>
        have e : g (.inl j) = .inl i := (g.apply_eq_iff_eq_symm_apply).mpr val.symm
        obtain ⟨_,_,h1,h2,_⟩ := forward i j e
        rw [h1,h2]
      | inr j =>
        have same : oldPart g c i = i := by simp [oldPart, hi, val]
        rw [same,same]
    · cases val : g (.inl i) with
      | inl j =>
        obtain ⟨_,_,h1,h2,_⟩ := forward j i val
        rw [h2,h1]
      | inr j =>
        have same : oldPart g c i = i := by simp [oldPart, hi, val]
        rw [same,same]
  · intro i j
    constructor
    · intro e
      obtain ⟨_,hj,_,h,ne⟩ := forward i j e
      exact ⟨hj,h,ne⟩
    · rintro ⟨hj,eq,ne⟩
      cases val : g (.inl j) with
      | inl k =>
        have same : k = i := by simpa [oldPart, hj, val] using eq
        simpa only [same] using val
      | inr k =>
        have same : j = i := by simpa [oldPart, hj, val] using eq
        exact (ne same.symm).elim

end PEqualNP.Outside.L_meta_33604_aux.Core


namespace PEqualNP.Outside.L_meta_33604_aux.Core

private theorem permanent_decorated {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I Nat) :
    A.permanent = Fintype.card (Σ p : Equiv.Perm I, ∀ i, Fin (A (p i) i)) := by
  simp only [Matrix.permanent, Fintype.card_sigma, Fintype.card_pi, Fintype.card_fin]

-- Each edge touching X designates exactly one vertex of X to carry its extra bit.
private def rep {n : ℕ} (p : Fin n → Fin n) (X : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ X ∧ p i ≠ i ∧ (p i ∉ X ∨ i < p i)

private theorem color_factor {n : ℕ} (p : Fin n → Fin n) (hp : Function.Involutive p)
    (X : Finset (Fin n)) (side : Fin n → Bool)
    (proper : ∀ i, i ∉ X → p i ∉ X → p i ≠ i → side i ≠ side (p i)) :
    Nat.card (Σ c : {c : Fin n → Bool // (∀ i ∉ X, c i = side i) ∧
      ∀ i, p i ≠ i → c i ≠ c (p i)}, {i : Fin n // rep p X i} → Bool) = 2 ^ X.card := by
  classical
  have opp (i) (h : rep p X i) : ¬ rep p X (p i) := by
    rcases h with ⟨hi, hn, ho | ho⟩
    · exact fun hh => ho hh.1
    · intro hh
      rcases hh.2.2 with out | lt
      · exact out (by simpa only [hp i] using hi)
      · rw [hp i] at lt
        exact (not_lt_of_ge ho.le) lt
  have choose (i) (hne : p i ≠ i) (h : ¬rep p X i) (h' : ¬rep p X (p i)) :
      i ∉ X ∧ p i ∉ X := by
    by_cases hi : i ∈ X <;> by_cases hj : p i ∈ X
    · rcases lt_or_gt_of_ne hne with lt | lt
      · exact (h' ⟨hj, by rw [hp i]; exact Ne.symm hne,
          Or.inr (by simpa only [hp i] using lt)⟩).elim
      · exact (h ⟨hi,hne,Or.inr lt⟩).elim
    · exact (h ⟨hi,hne,Or.inl hj⟩).elim
    · exact (h' ⟨hj, by rw [hp i]; exact Ne.symm hne,
        Or.inl (by simpa only [hp i] using hi)⟩).elim
    · exact ⟨hi,hj⟩
  let raw (b : X → Bool) (i : Fin n) := if h : i ∈ X then b ⟨i,h⟩ else side i
  let norm (b : X → Bool) (i : Fin n) := if rep p X i then !raw b (p i) else raw b i
  have valid (b : X → Bool) :
      (∀ i ∉ X, norm b i = side i) ∧ ∀ i, p i ≠ i → norm b i ≠ norm b (p i) := by
    constructor
    · intro i hi
      have r : ¬rep p X i := fun h => hi h.1
      simp [norm, raw, hi, r]
    · intro i hi
      by_cases r : rep p X i
      · simp [norm, r, opp i r]
      · by_cases r' : rep p X (p i)
        · simp [norm, r, r', hp i]
        · obtain ⟨out, out'⟩ := choose i hi r r'
          simpa [norm, raw, r, r', out, out'] using proper i out out' hi
  let equiv : (X → Bool) ≃
      (Σ c : {c : Fin n → Bool // (∀ i ∉ X, c i = side i) ∧
        ∀ i, p i ≠ i → c i ≠ c (p i)}, {i : Fin n // rep p X i} → Bool) :=
    { toFun := fun b => ⟨⟨norm b, valid b⟩, fun j => raw b j⟩
      invFun := fun ⟨c, marks⟩ i => if h : rep p X i then marks ⟨i,h⟩ else c.1 i
      left_inv := by
        intro b
        funext i
        by_cases h : rep p X i <;> simp [h, norm, raw, i.2]
      right_inv := by
        rintro ⟨⟨c,hc⟩,marks⟩
        let b : X → Bool := fun i => if h : rep p X i then marks ⟨i,h⟩ else c i
        have same (i) (h : ¬rep p X i) : raw b i = c i := by
          by_cases hi : i ∈ X
          · simp [raw, hi, b, h]
          · simpa [raw, hi] using (hc.1 i hi).symm
        have cn : norm b = c := by
          funext i
          by_cases r : rep p X i
          · have ne := hc.2 i r.2.1
            rw [show norm b i = !c (p i) by simp [norm, r, same _ (opp i r)]]
            cases h₁ : c i <;> cases h₂ : c (p i) <;> simp_all
          · simp [norm, r, same i r]
        have first : (⟨norm b, valid b⟩ :
            {c : Fin n → Bool // (∀ i ∉ X, c i = side i) ∧
              ∀ i, p i ≠ i → c i ≠ c (p i)}) = ⟨c,hc⟩ := Subtype.ext cn
        refine Sigma.ext first ?_
        apply heq_of_eq
        funext j
        simp [raw, j.2.1, b, j.2] }
  rw [← Nat.card_congr equiv, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

end PEqualNP.Outside.L_meta_33604_aux.Core


-- Equality characterization ported from lean/PEqualNP/Outside/L_meta_32050.lean at
-- 028e3e4ddd2da65f69b2c0c6ffad3ab1bf2092b9; scope renamed, reduction-specific code omitted.
namespace PEqualNP.Outside.L_meta_33604_aux.Circuits
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
end PEqualNP.Outside.L_meta_33604_aux.Circuits

namespace PEqualNP.Outside.L_meta_33604_aux.Core

private def pairEnds {n : ℕ} (e : Fin n × Fin n) : Finset (Fin n) := {e.1,e.2}

private def edgesOf {n : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ p e.1 = e.2)

private def binaryEval {n : ℕ} (p : Equiv.Perm (Fin n))
    (x y : Fin n → Bool) : Bool :=
  decide (∃ i : Fin n, (x i = true ∧ y i = true) ∨
    (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨ (y i = true ∧ y (p i) = true))))

private theorem edge_in_row {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (R : Finset (Fin n)) :
    (∃ i, p i ≠ i ∧ i ∈ R ∧ p i ∈ R) ↔ ∃ e ∈ edgesOf p, pairEnds e ⊆ R := by
  constructor
  · rintro ⟨i, hn, hi, hj⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨(p i,i), by simp [edgesOf, h, hp i],
        by simpa only [pairEnds, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hj hi⟩
    · exact ⟨(i,p i), by simp [edgesOf, h],
        by simpa only [pairEnds, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj⟩
  · rintro ⟨⟨i,j⟩, he, inside⟩
    simp only [edgesOf, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [pairEnds, Finset.insert_subset_iff, Finset.singleton_subset_iff] at inside
    exact ⟨i, he.2 ▸ he.1.ne.symm, inside.1, he.2 ▸ inside.2⟩

private theorem eval_rows {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (R S : Finset (Fin n)) :
    binaryEval p (fun i => decide (i ∈ R)) (fun i => decide (i ∈ S)) = true ↔
      ¬Disjoint R S ∨ (∃ e ∈ edgesOf p, pairEnds e ⊆ R) ∨
        ∃ e ∈ edgesOf p, pairEnds e ⊆ S := by
  simp only [binaryEval, decide_eq_true_eq, Finset.not_disjoint_iff,
    ← edge_in_row _ hp, and_or_left, ← or_assoc, exists_or]

private theorem pair_probe {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (e : Fin n × Fin n) (lt : e.1 < e.2) :
    binaryEval p (fun i => decide (i ∈ pairEnds e)) (fun _ => false) = true ↔
      e ∈ edgesOf p := by
  rw [show (fun _ : Fin n => false) = (fun i => decide (i ∈ (∅ : Finset (Fin n)))) by simp,
    eval_rows p hp]
  simp only [Finset.disjoint_empty_right, not_true_eq_false, false_or]
  constructor
  · rintro (⟨⟨i,j⟩, h, sub⟩ | ⟨⟨i,j⟩, _, sub⟩)
    · simp only [edgesOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
      have hi := sub (show i ∈ pairEnds (i,j) by simp [pairEnds])
      have hj := sub (show j ∈ pairEnds (i,j) by simp [pairEnds])
      simp only [pairEnds, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases e with ⟨a,b⟩
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact (lt_irrefl _ h.1).elim
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      · exact (not_lt_of_ge lt.le h.1).elim
      · exact (lt_irrefl _ h.1).elim
    · exact (Finset.notMem_empty i (sub (by simp [pairEnds]))).elim
  · exact fun h => Or.inl ⟨e,h,Finset.Subset.refl _⟩

private theorem edgesOf_injective {n : ℕ} {p q : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (eq : edgesOf p = edgesOf q) : p = q := by
  have moves {a b : Equiv.Perm (Fin n)}
      (ha : Function.Involutive a) (hb : Function.Involutive b)
      (eq : edgesOf a = edgesOf b) (i : Fin n) (hn : a i ≠ i) : a i = b i := by
    rcases lt_or_gt_of_ne hn with h | h
    · have mem : (a i,i) ∈ edgesOf a := by simp [edgesOf, h, ha i]
      rw [eq] at mem
      have app : b (a i) = i := (Finset.mem_filter.mp mem).2.2
      exact (hb (a i)).symm.trans (congrArg b app)
    · have mem : (i,a i) ∈ edgesOf a := by simp [edgesOf, h]
      rw [eq] at mem
      exact ((Finset.mem_filter.mp mem).2.2).symm
  apply Equiv.ext
  intro i
  by_cases h : p i = i
  · by_cases h' : q i = i
    · exact h.trans h'.symm
    · exact (moves hq hp eq.symm i h').symm
  · exact moves hp hq eq i h

private theorem binaryEval_injective {n : ℕ} {p q : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (eq : binaryEval p = binaryEval q) : p = q := by
  apply edgesOf_injective hp hq
  ext e
  by_cases lt : e.1 < e.2
  · rw [← pair_probe p hp e lt, ← pair_probe q hq e lt, eq]
  · simp [edgesOf, lt]

private theorem negative_rows {n : ℕ} (p : Equiv.Perm (Fin n))
    (hp : Function.Involutive p) (neg : List (Finset (Fin n) × Finset (Fin n))) :
    (∀ z ∈ neg, binaryEval p (fun i => decide (i ∈ z.1)) (fun i => decide (i ∈ z.2)) = false) ↔
      (∀ z ∈ neg, Disjoint z.1 z.2) ∧
      edgesOf p ⊆ Finset.univ.filter (fun e => e.1 < e.2 ∧
        ∀ z ∈ neg, ¬pairEnds e ⊆ z.1 ∧ ¬pairEnds e ⊆ z.2) := by
  classical
  have rule (z : Finset (Fin n) × Finset (Fin n)) :
      binaryEval p (fun i => decide (i ∈ z.1)) (fun i => decide (i ∈ z.2)) = false ↔
      Disjoint z.1 z.2 ∧ ∀ e ∈ edgesOf p, ¬pairEnds e ⊆ z.1 ∧ ¬pairEnds e ⊆ z.2 := by
    rw [← Bool.not_eq_true, eval_rows p hp]
    push Not
    constructor
    · rintro ⟨d,left,right⟩
      exact ⟨d, fun e he => ⟨left e he, right e he⟩⟩
    · rintro ⟨d,h⟩
      exact ⟨d, fun e he => (h e he).1, fun e he => (h e he).2⟩
  constructor
  · intro h
    refine ⟨fun z hz => ((rule z).mp (h z hz)).1, fun e he => ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.1,
      fun z hz => ((rule z).mp (h z hz)).2 e he⟩
  · rintro ⟨h,sub⟩ z hz
    exact (rule z).mpr ⟨h z hz, fun e he => (Finset.mem_filter.mp (sub he)).2.2 z hz⟩

private theorem histogram_involutions (n : ℕ) (hn : 2 ≤ n)
    (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n))) (s : ℕ) :
    let E := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2 ∧
      ∀ z ∈ neg, ¬pairEnds e ⊆ z.1 ∧ ¬pairEnds e ⊆ z.2)
    let obs := fun (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (R S : Finset (Fin n)) =>
      f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
    Nat.card {f : (Fin n → Bool) → (Fin n → Bool) → Bool //
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
        PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
      (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false) ∧
      (Finset.univ.filter (fun z : Fin n × Fin n =>
        z.1 < z.2 ∧ obs f (pairEnds z) ∅ = true)).card = s} =
    Nat.card {p : Equiv.Perm (Fin n) // Function.Involutive p ∧
      (∀ R ∈ pos, ∃ e ∈ edgesOf p, pairEnds e ⊆ R) ∧
      ((∀ z ∈ neg, Disjoint z.1 z.2) ∧ edgesOf p ⊆ E) ∧ (edgesOf p).card = s} := by
  classical
  dsimp only
  have law (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p) :
      (∀ R ∈ pos, binaryEval p (fun i => decide (i ∈ R)) (fun i => decide (i ∈ (∅ : Finset (Fin n)))) = true) ↔
      ∀ R ∈ pos, ∃ e ∈ edgesOf p, pairEnds e ⊆ R := by
    simp only [eval_rows p hp, Finset.disjoint_empty_right, not_true_eq_false, false_or]
    have none : ¬ ∃ e ∈ edgesOf p, pairEnds e ⊆ ∅ := by
      rintro ⟨e, _, h⟩
      exact Finset.notMem_empty e.1 (h (by simp [pairEnds]))
    simp only [none, or_false]
  have size (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p) :
      (Finset.univ.filter (fun z : Fin n × Fin n => z.1 < z.2 ∧
        binaryEval p (fun i => decide (i ∈ pairEnds z)) (fun i => decide (i ∈ (∅ : Finset (Fin n)))) = true)) =
      edgesOf p := by
    ext e
    by_cases lt : e.1 < e.2
    · simp [lt, pair_probe p hp e lt]
    · simp [lt, edgesOf]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun ⟨p,hp,hpos,hneg,hs⟩ => ⟨binaryEval p, ?_, ?_, ?_, ?_⟩) ⟨?_,?_⟩
  · exact (PEqualNP.Outside.L_meta_33604_aux.Circuits.L8_thm n hn _).mpr
      ⟨p, ⟨hp,fun _ _ => rfl⟩, fun q hq =>
        binaryEval_injective hq.1 hp (funext fun x => funext fun y => (hq.2 x y).symm)⟩
  · exact (law p hp).mpr hpos
  · exact (negative_rows p hp neg).mpr hneg
  · rwa [size p hp]
  · intro p q eq
    exact Subtype.ext (binaryEval_injective p.2.1 q.2.1 (congrArg Subtype.val eq))
  · rintro ⟨f,hC,hpos,hneg,hs⟩
    obtain ⟨p,⟨hp,hf⟩,_⟩ := (PEqualNP.Outside.L_meta_33604_aux.Circuits.L8_thm n hn f).mp hC
    have ef : f = binaryEval p := funext fun x => funext fun y => hf x y
    subst f
    exact ⟨⟨p,hp,(law p hp).mp hpos,(negative_rows p hp neg).mp hneg,
      by simpa only [size p hp] using hs⟩,rfl⟩

end PEqualNP.Outside.L_meta_33604_aux.Core


namespace PEqualNP.Outside.L_meta_33604_aux.Core

private def ends {V : Type*} [DecidableEq V] (e : V × V) : Finset V := {e.1,e.2}

private theorem bipartite_star {V : Type*} [DecidableEq V] (c : V → Bool)
    (B : Finset (V × V)) (nonempty : B.Nonempty)
    (color : ∀ e ∈ B, c e.1 = false ∧ c e.2 = true)
    (meet : ∀ e ∈ B, ∀ f ∈ B, ¬Disjoint (ends e) (ends f)) :
    ∃ v, ∀ e ∈ B, v ∈ ends e := by
  classical
  have share (e f : V × V) (he : e ∈ B) (hf : f ∈ B) : e.1 = f.1 ∨ e.2 = f.2 := by
    obtain ⟨v, hv, hw⟩ := Finset.not_disjoint_iff.mp (meet e he f hf)
    simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hv hw
    obtain ⟨he₁, he₂⟩ := color e he
    obtain ⟨hf₁, hf₂⟩ := color f hf
    rcases hv with rfl | rfl <;> rcases hw with h | h
    · exact Or.inl h
    · rw [← h, he₁] at hf₂
      contradiction
    · rw [← h, he₂] at hf₁
      contradiction
    · exact Or.inr h
  obtain ⟨e, he⟩ := nonempty
  by_cases star : ∀ f ∈ B, e.1 = f.1
  · exact ⟨e.1, fun f hf => by simp [ends, star f hf]⟩
  push_neg at star
  obtain ⟨f, hf, hne⟩ := star
  have hv := (share e f he hf).resolve_left hne
  refine ⟨e.2, fun g hg => ?_⟩
  simp only [ends, Finset.mem_insert, Finset.mem_singleton]
  rcases share e g he hg with h | h
  · right
    exact hv.trans ((share f g hf hg).resolve_left (fun eq => hne (h.trans eq.symm)))
  · exact Or.inr h

private theorem enforce_star {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (pos : List (Finset V)) (B M : Finset E) (hMB : M ⊆ B)
    (pairwise : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (support e) (support f))
    (star : ∀ R ∈ pos, ∃ v, ∀ e ∈ B, support e ⊆ R → v ∈ support e) :
    (∀ R ∈ pos, ∃ e ∈ M, support e ⊆ R) ↔
      (∀ R ∈ pos, ∀ v, (∀ e ∈ B, support e ⊆ R → v ∈ support e) →
        (∃ e ∈ M, v ∈ support e) ∧ ∀ e ∈ M, v ∈ support e → support e ⊆ R) := by
  constructor
  · intro fit R hR v center
    obtain ⟨e, he, inside⟩ := fit R hR
    have incident := center e (hMB he) inside
    refine ⟨⟨e, he, incident⟩, fun f hf hits => ?_⟩
    have same : e = f := by
      by_contra ne
      exact (Finset.not_disjoint_iff.mpr ⟨v, incident, hits⟩) (pairwise e he f hf ne)
    exact same ▸ inside
  · intro enforced R hR
    obtain ⟨v, hv⟩ := star R hR
    obtain ⟨⟨e, he, hv'⟩, restriction⟩ := enforced R hR v hv
    exact ⟨e, he, restriction e he hv'⟩

end PEqualNP.Outside.L_meta_33604_aux.Core


namespace PEqualNP.Outside.L_meta_33604_aux.Core

private theorem extends_iff {U D : Type*} {P Q : U → Prop}
    (m : Subtype P ≃ Subtype Q) (g : Equiv.Perm (U ⊕ D)) :
    extendsMatch m g ↔
      (∀ j k : D, g (.inr j) ≠ .inr k) ∧
      ∀ i j, g (.inl j) = .inl i ↔ ∃ x : Subtype P, x.1 = j ∧ (m x).1 = i := by
  classical
  constructor
  · rintro ⟨matched,missing,dummy⟩
    refine ⟨fun j k e => ?_,fun i j => ?_⟩
    · obtain ⟨v,hv⟩ := dummy j
      simp [hv] at e
    · constructor
      · intro e
        by_cases h : P j
        · exact ⟨⟨j,h⟩, rfl, Sum.inl.inj ((matched ⟨j,h⟩).symm.trans e)⟩
        · obtain ⟨k,hk⟩ := missing ⟨j,h⟩
          simp [hk] at e
      · rintro ⟨x,rfl,h⟩
        exact (matched x).trans (congrArg Sum.inl h)
  · rintro ⟨dummy,real⟩
    refine ⟨fun u => (real _ _).mpr ⟨u,rfl,rfl⟩,fun u => ?_,fun d => ?_⟩
    · cases eq : g (.inl u.1) with
      | inl i =>
        obtain ⟨x,hx,_⟩ := (real i u).mp eq
        exact (u.2 (hx ▸ x.2)).elim
      | inr j => exact ⟨j,rfl⟩
    · cases eq : g (.inr d) with
      | inr j => exact (dummy d j eq).elim
      | inl i =>
        have no : ¬ Q i := by
          intro h
          obtain ⟨u, hu⟩ := m.surjective ⟨i,h⟩
          have im : g (.inl u.1) = .inl i := (real _ _).mpr ⟨u,rfl,congrArg Subtype.val hu⟩
          have impossible := g.injective (eq.trans im.symm)
          cases impossible
        exact ⟨⟨i,no⟩,rfl⟩

private def movesOn {U : Type*} (c : U → Bool) (p : Equiv.Perm U) (b : Bool) (i : U) :=
  c i = b ∧ p i ≠ i

private theorem mate_shores {U : Type*} (c : U → Bool) (p : Equiv.Perm U)
    (hp : Function.Involutive p) (cross : ∀ i, p i ≠ i → c i ≠ c (p i)) (i : U) :
    movesOn c p true i ↔ movesOn c p false (p i) := by
  unfold movesOn
  rw [hp i]
  by_cases h : p i = i
  · simp [h]
  · have ne := cross i h
    have rev := Ne.symm h
    cases hi : c i <;> cases hj : c (p i) <;> simp_all

private def mateMap {U : Type*} (c : U → Bool) (p : Equiv.Perm U)
    (hp : Function.Involutive p) (cross : ∀ i, p i ≠ i → c i ≠ c (p i)) :
    Subtype (movesOn c p true) ≃ Subtype (movesOn c p false) := p.subtypeEquiv (mate_shores c p hp cross)

private theorem extends_mate {U D : Type*} (c : U → Bool) (p : Equiv.Perm U)
    (hp : Function.Involutive p) (cross : ∀ i, p i ≠ i → c i ≠ c (p i)) (g : Equiv.Perm (U ⊕ D)) :
    extendsMatch (mateMap c p hp cross) g ↔
      (∀ j k : D, g (.inr j) ≠ .inr k) ∧
      ∀ i j, g (.inl j) = .inl i ↔ c j = true ∧ p j = i ∧ i ≠ j := by
  rw [extends_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨⟨x,hx⟩,rfl,h⟩
    change p x = i at h
    exact ⟨hx.1,h,fun eq => hx.2 (h.trans eq)⟩
  · rintro ⟨h,h',hne⟩
    exact ⟨⟨j,h,fun eq => hne (h'.symm.trans eq)⟩,rfl,h'⟩

private theorem edges_disjoint {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p) :
    ∀ e ∈ edgesOf p, ∀ f ∈ edgesOf p, e ≠ f → Disjoint (pairEnds e) (pairEnds f) := by
  rintro ⟨a,b⟩ he ⟨c,d⟩ hf ne
  simp only [edgesOf, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  by_contra meet
  obtain ⟨v, hv, hw⟩ := Finset.not_disjoint_iff.mp meet
  simp only [pairEnds, Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with va | vb <;> rcases hw with vc | vd
  · have eq := va.symm.trans vc
    exact ne (Prod.ext eq (he.2.symm.trans ((congrArg p eq).trans hf.2)))
  · have ad := va.symm.trans vd
    have pd : p d = c := by rw [← hf.2, hp]
    have bc : b = c := he.2.symm.trans ((congrArg p ad).trans pd)
    have h := he.1
    change a < b at h
    rw [ad,bc] at h
    exact not_lt_of_ge h.le hf.1
  · have bc := vb.symm.trans vc
    have pb : p b = a := by rw [← he.2, hp]
    have da : d = a := hf.2.symm.trans ((congrArg p bc.symm).trans pb)
    have h := hf.1
    change c < d at h
    rw [← bc,da] at h
    exact not_lt_of_ge h.le he.1
  · have eq := vb.symm.trans vd
    exact ne (Prod.ext (p.injective (he.2.trans (eq.trans hf.2.symm))) eq)

private theorem moved_card {n : ℕ} (c : Fin n → Bool) (p : Equiv.Perm (Fin n))
    (hp : Function.Involutive p) (cross : ∀ i, p i ≠ i → c i ≠ c (p i)) :
    Nat.card (Subtype (movesOn c p true)) = (edgesOf p).card := by
  classical
  let encode (i : Subtype (movesOn c p true)) : edgesOf p :=
    if h : (i : Fin n) < p i then
      ⟨(i,p i), by simp [edgesOf,h]⟩
    else
      ⟨(p i,i), by
        have lt : p i < (i : Fin n) := lt_of_le_of_ne (le_of_not_gt h) i.2.2
        simp [edgesOf,lt,hp i]⟩
  have p₂ (e : edgesOf p) :
      e.1.1 < e.1.2 ∧ p e.1.1 = e.1.2 ∧ p e.1.2 = e.1.1 := by
    obtain ⟨ord,h⟩ := (Finset.mem_filter.mp e.2).2
    exact ⟨ord,h,by rw [← h,hp]⟩
  let decode (e : edgesOf p) : Subtype (movesOn c p true) :=
    if h : c e.1.1 = true then ⟨e.1.1,h,by rw [(p₂ e).2.1]; exact (p₂ e).1.ne.symm⟩
    else ⟨e.1.2, by
      have ne := cross e.1.1 (by rw [(p₂ e).2.1]; exact (p₂ e).1.ne.symm)
      rw [(p₂ e).2.1] at ne
      cases hb : c e.1.1 <;> cases hc : c e.1.2 <;> simp_all,
      by rw [(p₂ e).2.2]; exact (p₂ e).1.ne⟩
  have h1 (i : Subtype (movesOn c p true)) : decode (encode i) = i := by
    obtain ⟨hcol,hne⟩ := i.2
    have after : c (p i) ≠ true := fun h => cross i hne (hcol.trans h.symm)
    apply Subtype.ext
    by_cases lt : (i : Fin n) < p i <;> simp [decode, encode, lt, hcol, after]
  have h2 (e : edgesOf p) : encode (decode e) = e := by
    obtain ⟨lt,first,second⟩ := p₂ e
    have ne : ¬ (e.1.2 < e.1.1) := not_lt_of_ge lt.le
    apply Subtype.ext
    by_cases h : c e.1.1 = true <;> simp [encode, decode, h, lt, first, second, ne]
  rw [Nat.card_congr (⟨encode,decode,h1,h2⟩ :
    Subtype (movesOn c p true) ≃ edgesOf p)]
  simp [Nat.card_eq_fintype_card]

end PEqualNP.Outside.L_meta_33604_aux.Core


namespace PEqualNP.Outside.L_meta_33604_aux.Writer

open Lib.Universal
open PEqualNP.Outside.L_meta_33604_aux.Core
open scoped Classical

private def negativeBank {n : ℕ} (z : Finset (Fin n) × Finset (Fin n)) : Bits :=
  bankBits z.1 ++ bankBits z.2

private def endBanks {n : ℕ} (X : Finset (Fin n)) (side : Fin n → Bool) (Y : Finset (Fin n)) : Bits :=
  bankBits X ++ List.ofFn side ++ bankBits Y

private def packedNegative {n : ℕ} (neg : List (Finset (Fin n) × Finset (Fin n))) (tail : Bits) : Bits :=
  rawHeader neg.length ++ (neg.flatMap negativeBank ++ tail)

private def packedRows {n : ℕ} (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (tail : Bits) : Bits :=
  rawHeader pos.length ++ (pos.flatMap bankBits ++ packedNegative neg tail)

private def packedInput {n : ℕ} (s : ℕ) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (tail : Bits) : Bits :=
  rawHeader s ++ (rawHeader n ++ packedRows pos neg tail)

private theorem bankBits_length {n : ℕ} (R : Finset (Fin n)) : (bankBits R).length = n := by
  simp [bankBits]

private theorem negativeBank_length {n : ℕ} (z : Finset (Fin n) × Finset (Fin n)) :
    (negativeBank z).length = n+n := by simp [negativeBank, bankBits_length]

private theorem parsedFields {n : ℕ} (s : ℕ) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (tail : Bits) (input : Expr) (env : Bits)
    (eq : input.run env = packedInput s pos neg tail) :
    (readS input).run env = un s ∧ (readN input).run env = un n ∧
    (readP input).run env = un pos.length ∧
    (readPB input).run env = pos.flatMap bankBits ++ packedNegative neg tail ∧
    (readQ input).run env = un neg.length ∧ (readQB input).run env = neg.flatMap negativeBank ++ tail ∧
    (afterRows input).run env = tail := by
  have ns : (readS input).run env = un s := by
    simp only [readS, Expr.run, eq, packedInput, hd_header]
  have nn : (readN input).run env = un n := by
    simp only [readN, Expr.run, eq, packedInput, strip_header, hd_header]
  have np : (readP input).run env = un pos.length := by
    simp only [readP, Expr.run, eq, packedInput, strip_header, packedRows, hd_header]
  have bp : (readPB input).run env = pos.flatMap bankBits ++ packedNegative neg tail := by
    simp only [readPB, Expr.run, eq, packedInput, packedRows, strip_header]
  have nh : (negHeader input).run env = packedNegative neg tail := by
    simp only [negHeader, Expr.run, q40, np, nn, bp, mulU, un_length]
    exact bank_skip pos bankBits n (fun R _ => bankBits_length R) (packedNegative neg tail)
  have nq : (readQ input).run env = un neg.length := by
    simp only [readQ, Expr.run, nh, packedNegative, hd_header]
  have bq : (readQB input).run env = neg.flatMap negativeBank ++ tail := by
    simp only [readQB, Expr.run, nh, packedNegative, strip_header]
  have endEq : (afterRows input).run env = tail := by
    simp only [afterRows, Expr.run, q40, mulU, un_length, List.length_append, nq, nn, bq]
    exact bank_skip neg negativeBank (n+n) (fun z _ => negativeBank_length z) tail
  exact ⟨ns,nn,np,bp,nq,bq,endEq⟩

private def truth (e : Expr) (env : Bits) : Prop := e.run env ≠ []

private theorem truth_any (k f : Expr) (env : Bits) :
    truth (k.any f) env ↔ ∃ i < (k.run env).length, truth f (pairB env (un i)) := by
  simp only [truth, Expr.run, flagAny, boundedMap_spec, flagNot, sel, ne_eq]
  set xs := (List.range (k.run env).length).flatMap _
  have empty : xs = [] ↔ ∀ i < (k.run env).length, f.run (pairB env (un i)) = [] := by
    dsimp only [xs]
    rw [List.flatMap_eq_nil_iff]
    simp only [List.mem_range, q12]
    apply forall_congr' fun i => forall_congr' fun _ => ?_
    cases f.run (pairB env (un i)) <;> simp
  constructor
  · intro h
    by_contra none
    have xnil : xs = [] := empty.mpr (fun i hi => by
      by_contra ne
      exact none ⟨i,hi,ne⟩)
    simp [xnil] at h
  · rintro ⟨i,hi,h⟩
    have hx : xs ≠ [] := fun eq => h (empty.mp eq i hi)
    simp [hx]

private theorem truth_or (a b : Expr) (env : Bits) :
    truth (a.bor b) env ↔ truth a env ∨ truth b env := by
  unfold truth
  simp only [Expr.run, flagOr, sel]
  split_ifs <;> simp_all

private theorem truth_and (a b : Expr) (env : Bits) :
    truth (a.band b) env ↔ truth a env ∧ truth b env := by
  unfold truth
  simp only [Expr.run, flagAnd, sel]
  split_ifs <;> simp_all

private theorem truth_not (a : Expr) (env : Bits) :
    truth a.bnot env ↔ ¬ truth a env := by
  unfold truth
  simp only [Expr.run, flagNot, sel]
  split_ifs <;> simp_all

private theorem truth_lt (a b : Expr) (env : Bits) :
    truth (a.lt b) env ↔ (a.run env).length < (b.run env).length := by
  simp only [truth, Expr.run, flagLt_spec, ne_eq, flag_cases, decide_eq_false_iff_not, not_not]

private theorem truth_get (a b : Expr) (env : Bits) :
    truth (a.get b) env ↔ (b.run env).getD (a.run env).length false = true := by
  simp only [truth, Expr.run, bitAt_spec, ne_eq, flag_cases, Bool.not_eq_false]

private theorem run_select (a b c : Expr) (env : Bits) :
    (a.select b c).run env = if truth a env then c.run env else b.run env := by
  by_cases h : a.run env = [] <;> simp [Expr.run, sel, truth, h]

private theorem getD_drop_index (l : Bits) (a b : ℕ) :
    (l.drop a).getD b false = l.getD (a+b) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

private theorem posGet {n : ℕ} (s : ℕ) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (tail : Bits)
    (input row idx : Expr) (env : Bits) (r : Fin pos.length) (i : Fin n)
    (word : input.run env = packedInput s pos neg tail)
    (rval : row.run env = un r) (ival : idx.run env = un i) :
    truth (idx.get (posBank input row)) env ↔ i ∈ pos[r] := by
  obtain ⟨_, nn, _, pb, _, _, _⟩ := parsedFields s pos neg tail input env word
  rw [truth_get]
  simp only [posBank, Expr.run, q40, getD_drop_index, mulU, rval, ival, nn, pb, un_length]
  rw [bank_access pos bankBits n (fun R _ => bankBits_length R) _ _ _ _ r.isLt i.isLt,
    bankBits_get, decide_eq_true_eq]
  rfl

private theorem negGet {n : ℕ} (s : ℕ) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (tail : Bits)
    (input row idx : Expr) (env : Bits) (r : Fin neg.length) (i : Fin n)
    (word : input.run env = packedInput s pos neg tail)
    (rval : row.run env = un r) (ival : idx.run env = un i) :
    (truth (idx.get (negA input row)) env ↔ i ∈ neg[r].1) ∧
    (truth (idx.get (negB input row)) env ↔ i ∈ neg[r].2) := by
  obtain ⟨_, nn, _, _, _, qb, _⟩ := parsedFields s pos neg tail input env word
  have access (j : ℕ) (hj : j < n+n) :=
    bank_access neg negativeBank (n+n) (fun z _ => negativeBank_length z) tail false r j r.isLt hj
  constructor
  · rw [truth_get]
    simp only [negA, Expr.run, q40, getD_drop_index, mulU, rval, ival, nn, qb, List.length_append, un_length]
    rw [access _ (by omega), negativeBank, List.getD_append _ _ _ _ (by simpa [bankBits_length] using i.isLt),
      bankBits_get, decide_eq_true_eq]
    rfl
  · rw [truth_get]
    simp only [negB, negA, Expr.run, q40, getD_drop_index, mulU, rval, ival, nn, qb, List.length_append, un_length]
    rw [access _ (by omega), negativeBank,
      List.getD_append_right _ _ _ _ (by rw [bankBits_length]; omega), bankBits_length, Nat.add_sub_cancel_left,
      bankBits_get, decide_eq_true_eq]
    rfl

private theorem xGet {n : ℕ} (s : ℕ) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (X : Finset (Fin n))
    (side : Fin n → Bool) (Y : Finset (Fin n)) (input idx : Expr) (env : Bits) (i : Fin n)
    (word : input.run env = packedInput s pos neg (endBanks X side Y))
    (ival : idx.run env = un i) : truth (xFlag input idx) env ↔ i ∈ X := by
  obtain ⟨_, _, _, _, _, _, tail⟩ := parsedFields s pos neg _ input env word
  rw [xFlag, truth_get, ival, un_length, tail, endBanks, List.append_assoc,
    List.getD_append _ _ _ _ (by simpa [bankBits_length] using i.isLt), bankBits_get, decide_eq_true_eq]

private theorem branchGet {n : ℕ} (s : ℕ) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) (X : Finset (Fin n))
    (side : Fin n → Bool) (Y : Finset (Fin n)) (input idx : Expr) (env : Bits) (i : Fin n)
    (word : input.run env = packedInput s pos neg (endBanks X side Y))
    (ival : idx.run env = un i) :
    truth (branchFlag input idx) env ↔ (if i ∈ X then decide (i ∈ Y) else side i) = true := by
  obtain ⟨_, nn, _, _, _, _, tail⟩ := parsedFields s pos neg _ input env word
  have fstDrop : (endBanks X side Y).drop n = List.ofFn side ++ bankBits Y := by
    rw [endBanks, List.append_assoc]
    exact List.drop_left' (bankBits_length X)
  have sndDrop : (endBanks X side Y).drop (n+n) = bankBits Y := by
    rw [endBanks, ← show (bankBits X ++ List.ofFn side).length = n+n by simp [bankBits_length]]
    simp
  have sideGet : (List.ofFn side).getD i false = side i := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, i.isLt]
  rw [branchFlag]
  change ¬ ((xFlag input idx).select (idx.get ((readN input).drop (afterRows input)))
    (idx.get (((readN input).append (readN input)).drop (afterRows input)))).run env = [] ↔ _
  rw [run_select, xGet s pos neg X side Y input idx env i word ival]
  by_cases hi : i ∈ X
  · simp only [hi, if_true]
    change truth (idx.get (((readN input).append (readN input)).drop (afterRows input))) env ↔ _
    rw [truth_get]
    simp only [Expr.run, q40, tail, nn, ival, un_length, List.length_append, sndDrop, bankBits_get]
  · simp only [hi, if_false]
    change truth (idx.get ((readN input).drop (afterRows input))) env ↔ _
    rw [truth_get]
    simp only [Expr.run, q40, tail, nn, ival, un_length, fstDrop]
    rw [List.getD_append _ _ _ _ (by simpa using i.isLt), sideGet]

end PEqualNP.Outside.L_meta_33604_aux.Writer


namespace PEqualNP.Outside.L_meta_33604_aux.Writer

open Lib.Universal PEqualNP.Outside.L_meta_33604_aux.Core
open scoped Classical

private structure Data (n : ℕ) where
  s : ℕ
  pos : List (Finset (Fin n))
  neg : List (Finset (Fin n) × Finset (Fin n))
  X : Finset (Fin n)
  side : Fin n → Bool
  Y : Finset (Fin n)

private def Data.word {n : ℕ} (a : Data n) := packedInput a.s a.pos a.neg (endBanks a.X a.side a.Y)
private def Data.color {n : ℕ} (a : Data n) (i : Fin n) :=
  if i ∈ a.X then decide (i ∈ a.Y) else a.side i
private def Data.freePair {n : ℕ} (a : Data n) (i j : Fin n) : Prop :=
  i ≠ j ∧ ∀ z ∈ a.neg, ¬pairEnds (i,j) ⊆ z.1 ∧ ¬pairEnds (i,j) ⊆ z.2
private def Data.crossPair {n : ℕ} (a : Data n) (i j : Fin n) : Prop :=
  a.freePair i j ∧ a.color i = false ∧ a.color j = true
private def Data.inside {n : ℕ} (_ : Data n) (R : Finset (Fin n)) (i j : Fin n) : Prop :=
  pairEnds (i,j) ⊆ R
private def Data.common {n : ℕ} (a : Data n) (R : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ i j, a.crossPair i j → a.inside R i j → v = i ∨ v = j
private def Data.barren {n : ℕ} (a : Data n) (R : Finset (Fin n)) : Prop :=
  ¬∃ i j, a.crossPair i j ∧ a.inside R i j
private def Data.fatal {n : ℕ} (a : Data n) : Prop :=
  (∃ z ∈ a.neg, ¬Disjoint z.1 z.2) ∨ ∃ R ∈ a.pos, a.barren R
private def Data.required {n : ℕ} (a : Data n) (v : Fin n) : Prop := ∃ R ∈ a.pos, a.common R v
private def Data.forbidden {n : ℕ} (a : Data n) (i j : Fin n) : Prop :=
  ∃ R ∈ a.pos, ¬a.inside R i j ∧ (a.common R i ∨ a.common R j)

private theorem truth_any_fin (k f : Expr) (env : Bits) (n : ℕ) (h : k.run env = un n) :
    truth (k.any f) env ↔ ∃ i : Fin n, truth f (pairB env (un i)) := by
  rw [truth_any, h, un_length]
  exact ⟨fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩, fun ⟨i,h⟩ => ⟨i,i.isLt,h⟩⟩

private theorem outer_run (e : Expr) (env extra : Bits) : e.outer.run (pairB env extra) = e.run env := by
  simp only [Expr.run, unpairB_pairB]
private theorem arg_run (env extra : Bits) : Expr.arg.run (pairB env extra) = extra := by
  simp only [Expr.run, unpairB_pairB]

private theorem pair_subset {n : ℕ} (R : Finset (Fin n)) (i j : Fin n) :
    pairEnds (i,j) ⊆ R ↔ i ∈ R ∧ j ∈ R := by
  simp only [pairEnds, Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem Data.readN_eq {n : ℕ} (a : Data n) {input env} (w : input.run env = a.word) :
    (readN input).run env = un n := (parsedFields a.s a.pos a.neg _ input env w).2.1
private theorem Data.readP_eq {n : ℕ} (a : Data n) {input env} (w : input.run env = a.word) :
    (readP input).run env = un a.pos.length := (parsedFields a.s a.pos a.neg _ input env w).2.2.1
private theorem Data.readQ_eq {n : ℕ} (a : Data n) {input env} (w : input.run env = a.word) :
    (readQ input).run env = un a.neg.length := (parsedFields a.s a.pos a.neg _ input env w).2.2.2.2.1

private theorem neq_spec {n : ℕ} (i j : Fin n) {u v : Expr} {env : Bits}
    (hu : u.run env = un i) (hv : v.run env = un j) : truth (neqFlag u v) env ↔ i ≠ j := by
  simp only [neqFlag, truth_or, truth_lt, hu, hv, un_length]
  exact ⟨fun h eq => by subst j; simpa using h, fun ne => lt_or_gt_of_ne (fun eq => ne (Fin.ext eq))⟩

private theorem edge_spec {n : ℕ} (a : Data n) (i j : Fin n) {input u v : Expr} {env : Bits}
    (w : input.run env = a.word) (hu : u.run env = un i) (hv : v.run env = un j) :
    truth (edgeFlag input u v) env ↔ a.freePair i j := by
  unfold edgeFlag Data.freePair
  rw [truth_and, truth_not, truth_any_fin _ _ _ _ (a.readQ_eq w)]
  change truth (neqFlag u v) env ∧ _ ↔ _
  rw [neq_spec i j hu hv, List.forall_mem_iff_get]
  refine and_congr Iff.rfl ?_
  push Not
  apply forall_congr'
  intro r
  have w' : input.outer.run (pairB env (un r)) = a.word := by simpa only [outer_run] using w
  have hu' : u.outer.run (pairB env (un r)) = un i := by simpa only [outer_run] using hu
  have hv' : v.outer.run (pairB env (un r)) = un j := by simpa only [outer_run] using hv
  have ar : Expr.arg.run (pairB env (un r)) = un (r : ℕ) := arg_run _ _
  obtain ⟨iA,iB⟩ := negGet a.s a.pos a.neg _ _ _ _ _ r i w' ar hu'
  obtain ⟨jA,jB⟩ := negGet a.s a.pos a.neg _ _ _ _ _ r j w' ar hv'
  rw [truth_or, truth_and, truth_and, iA, iB, jA, jB, pair_subset, pair_subset, not_or]
  rfl

private theorem cross_spec {n : ℕ} (a : Data n) (i j : Fin n) {input u v : Expr} {env : Bits}
    (w : input.run env = a.word) (hu : u.run env = un i) (hv : v.run env = un j) :
    truth (crossEdge input u v) env ↔ a.crossPair i j := by
  rw [crossEdge, truth_and, truth_and, truth_not, edge_spec a i j w hu hv,
    branchGet a.s a.pos a.neg a.X a.side a.Y _ _ _ i w hu,
    branchGet a.s a.pos a.neg a.X a.side a.Y _ _ _ j w hv]
  simp only [Data.crossPair, Data.color, Bool.not_eq_true]

private theorem inside_spec {n : ℕ} (a : Data n) (r : Fin a.pos.length) (i j : Fin n)
    {input row u v : Expr} {env : Bits} (w : input.run env = a.word)
    (hr : row.run env = un r) (hu : u.run env = un i) (hv : v.run env = un j) :
    truth (inside input row u v) env ↔ a.inside a.pos[r] i j := by
  rw [inside, truth_and, posGet a.s a.pos a.neg _ _ _ _ _ r i w hr hu,
    posGet a.s a.pos a.neg _ _ _ _ _ r j w hr hv, Data.inside, pair_subset]

private theorem badNegative_spec {n : ℕ} (a : Data n) {input : Expr} {env : Bits}
    (w : input.run env = a.word) : truth (badNegative input) env ↔ ∃ z ∈ a.neg, ¬Disjoint z.1 z.2 := by
  rw [badNegative, truth_any_fin _ _ _ _ (a.readQ_eq w), List.exists_mem_iff_get]
  apply exists_congr
  intro r
  have wr : input.outer.run (pairB env (un r)) = a.word := by simpa only [outer_run] using w
  rw [truth_any_fin _ _ _ _ (a.readN_eq wr), Finset.not_disjoint_iff]
  apply exists_congr
  intro i
  have wi : input.outer.outer.run (pairB (pairB env (un r)) (un i)) = a.word := by simpa only [outer_run] using w
  have ar : Expr.arg.outer.run (pairB (pairB env (un r)) (un i)) = un (r : ℕ) := by simp only [outer_run, arg_run]
  have ai : Expr.arg.run (pairB (pairB env (un r)) (un i)) = un (i : ℕ) := arg_run _ _
  obtain ⟨h₁,h₂⟩ := negGet a.s a.pos a.neg _ _ _ _ _ r i wi ar ai
  rw [truth_and, h₁, h₂]
  rfl

private theorem someCross_spec {n : ℕ} (a : Data n) (r : Fin a.pos.length)
    {input row : Expr} {env : Bits} (w : input.run env = a.word) (hr : row.run env = un r)
    (extra : Expr → Expr → Expr) (P : Fin n → Fin n → Prop)
    (extraLaw : ∀ i j : Fin n,
      truth (extra Expr.arg.outer Expr.arg) (pairB (pairB env (un i)) (un j)) ↔ P i j) :
    truth (someCross input row extra) env ↔
      ∃ i j, a.crossPair i j ∧ a.inside a.pos[r] i j ∧ P i j := by
  rw [someCross, truth_any_fin _ _ _ _ (a.readN_eq w)]
  apply exists_congr
  intro i
  have wi : input.outer.run (pairB env (un i)) = a.word := by simpa only [outer_run] using w
  rw [truth_any_fin _ _ _ _ (a.readN_eq wi)]
  apply exists_congr
  intro j
  have wj : input.outer.outer.run (pairB (pairB env (un i)) (un j)) = a.word := by simpa only [outer_run] using w
  have rj : row.outer.outer.run (pairB (pairB env (un i)) (un j)) = un r := by simpa only [outer_run] using hr
  have u : Expr.arg.outer.run (pairB (pairB env (un i)) (un j)) = un (i : ℕ) := by simp only [outer_run, arg_run]
  have v : Expr.arg.run (pairB (pairB env (un i)) (un j)) = un (j : ℕ) := arg_run _ _
  rw [truth_and, truth_and, cross_spec a i j wj u v, inside_spec a r i j wj rj u v, extraLaw i j]
  exact and_assoc

private theorem optional_spec {n : ℕ} (a : Data n) (r : Fin a.pos.length) (k : Fin n)
    {input row idx : Expr} {env : Bits} (w : input.run env = a.word)
    (hr : row.run env = un r) (hk : idx.run env = un k) :
    truth (optionalAt input row idx) env ↔ ¬ a.common a.pos[r] k := by
  have law (i j : Fin n) : truth ((neqFlag idx.outer.outer Expr.arg.outer).band
      (neqFlag idx.outer.outer Expr.arg)) (pairB (pairB env (un i)) (un j)) ↔ k ≠ i ∧ k ≠ j := by
    have ki : idx.outer.outer.run (pairB (pairB env (un i)) (un j)) = un k := by simpa only [outer_run] using hk
    have u : Expr.arg.outer.run (pairB (pairB env (un i)) (un j)) = un (i : ℕ) := by simp only [outer_run, arg_run]
    have v : Expr.arg.run (pairB (pairB env (un i)) (un j)) = un (j : ℕ) := arg_run _ _
    rw [truth_and, neq_spec k i ki u, neq_spec k j ki v]
  rw [optionalAt, someCross_spec a r w hr _ _ law, Data.common]
  push Not
  rfl

private theorem emptyPositive_spec {n : ℕ} (a : Data n) {input : Expr} {env : Bits}
    (w : input.run env = a.word) : truth (emptyPositive input) env ↔ ∃ R ∈ a.pos, a.barren R := by
  rw [emptyPositive, truth_any_fin _ _ _ _ (a.readP_eq w), List.exists_mem_iff_get]
  apply exists_congr
  intro r
  have wr : input.outer.run (pairB env (un r)) = a.word := by simpa only [outer_run] using w
  have ar : Expr.arg.run (pairB env (un r)) = un (r : ℕ) := arg_run _ _
  rw [truth_not, someCross_spec a r wr ar _ (fun _ _ => True) (by simp [truth, Expr.run])]
  simp only [and_true, Data.barren]
  rfl

private theorem required_spec {n : ℕ} (a : Data n) (i : Fin n) {input idx : Expr} {env : Bits}
    (w : input.run env = a.word) (hi : idx.run env = un i) :
    truth (compulsory input idx) env ↔ a.required i := by
  rw [compulsory, Data.required, truth_any_fin _ _ _ _ (a.readP_eq w), List.exists_mem_iff_get]
  apply exists_congr
  intro r
  have wr : input.outer.run (pairB env (un r)) = a.word := by simpa only [outer_run] using w
  have ar : Expr.arg.run (pairB env (un r)) = un (r : ℕ) := arg_run _ _
  have ir : idx.outer.run (pairB env (un r)) = un i := by simpa only [outer_run] using hi
  rw [truth_not, optional_spec a r i wr ar ir, not_not]
  rfl

private theorem forbidden_spec {n : ℕ} (a : Data n) (i j : Fin n)
    {input u v : Expr} {env : Bits} (w : input.run env = a.word)
    (hi : u.run env = un i) (hj : v.run env = un j) :
    truth (restrictEdge input u v) env ↔ a.forbidden i j := by
  rw [restrictEdge, Data.forbidden, truth_any_fin _ _ _ _ (a.readP_eq w), List.exists_mem_iff_get]
  apply exists_congr
  intro r
  have wr : input.outer.run (pairB env (un r)) = a.word := by simpa only [outer_run] using w
  have ar : Expr.arg.run (pairB env (un r)) = un (r : ℕ) := arg_run _ _
  have ir : u.outer.run (pairB env (un r)) = un i := by simpa only [outer_run] using hi
  have jr : v.outer.run (pairB env (un r)) = un j := by simpa only [outer_run] using hj
  rw [truth_and, truth_not, truth_or, truth_not, truth_not, inside_spec a r i j wr ar ir jr,
    optional_spec a r i wr ar ir, optional_spec a r j wr ar jr, not_not, not_not]
  rfl

private theorem fatal_spec {n : ℕ} (a : Data n) {input : Expr} {env : Bits}
    (w : input.run env = a.word) :
    truth ((badNegative input).bor (emptyPositive input)) env ↔ a.fatal := by
  rw [truth_or, badNegative_spec a w, emptyPositive_spec a w, Data.fatal]

private noncomputable def Data.grid {n : ℕ} (a : Data n) : Matrix (Fin n ⊕ Fin (n-a.s)) (Fin n ⊕ Fin (n-a.s)) Nat :=
  fun i j => if a.fatal then 0 else
    match i,j with
    | .inl i,.inl j =>
      if a.crossPair i j ∧ ¬a.forbidden i j then if i ∈ a.X ∨ j ∈ a.X then 2 else 1 else 0
    | .inl i,.inr _ => if a.color i = false ∧ a.required i then 0 else 1
    | .inr _,.inl j => if a.color j = true ∧ a.required j then 0 else 1
    | .inr _,.inr _ => 0

private def Data.slot {n : ℕ} (a : Data n) (hs : a.s ≤ n) :
    Fin n ⊕ Fin (n-a.s) ≃ Fin (2*n-a.s) :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem Data.slot_old {n : ℕ} (a : Data n) (hs : a.s ≤ n) (i : Fin n) :
    (a.slot hs (.inl i) : ℕ) = i := rfl
private theorem Data.slot_new {n : ℕ} (a : Data n) (hs : a.s ≤ n) (i : Fin (n-a.s)) :
    (a.slot hs (.inr i) : ℕ) = n+i := rfl

private theorem entry_read {n : ℕ} (a : Data n) (hs : a.s ≤ n) (i j : Fin n ⊕ Fin (n-a.s)) :
    rawMatrix a.word (2*n-a.s) (a.slot hs i) (a.slot hs j) = a.grid i j := by
  let env := pairB (pairB (pairB [] a.word) (un (a.slot hs i))) (un (a.slot hs j))
  let input := Expr.arg.outer.outer
  let u := Expr.arg.outer
  let v := Expr.arg
  have hw : input.run env = a.word := by simp only [env, input, outer_run, arg_run]
  have hu : u.run env = un (a.slot hs i) := by simp only [env, u, outer_run, arg_run]
  have hv : v.run env = un (a.slot hs j) := by simp only [env, v, outer_run, arg_run]
  have fault := fatal_spec a hw
  have cutU : truth (u.lt (readN input)) env ↔ (a.slot hs i : ℕ) < n := by
    rw [truth_lt, hu, a.readN_eq hw, un_length, un_length]
  have cutV : truth (v.lt (readN input)) env ↔ (a.slot hs j : ℕ) < n := by
    rw [truth_lt, hv, a.readN_eq hw, un_length, un_length]
  have calcCell : cellBits a.word (a.slot hs i) (a.slot hs j) = (cell input u v).run env := rfl
  unfold rawMatrix
  rw [calcCell]
  unfold cell Data.grid
  simp only [run_select, fault, cutU, cutV]
  by_cases bad : a.fatal
  · simp [bad, Expr.run]
  · simp only [bad, if_false]
    rcases i with i | i <;> rcases j with j | j
    · simp only [Data.slot_old] at hu hv ⊢
      have hedge := cross_spec a i j hw hu hv
      have hrest := forbidden_spec a i j hw hu hv
      have hx := xGet a.s a.pos a.neg a.X a.side a.Y _ _ _ i hw hu
      have hy := xGet a.s a.pos a.neg a.X a.side a.Y _ _ _ j hw hv
      simp only [i.isLt, j.isLt, if_true, truth_and, truth_not, truth_or, hedge, hrest, hx, hy]
      split_ifs <;> rfl
    · simp only [Data.slot_old] at hu ⊢
      simp only [Data.slot_new]
      have hreq := required_spec a i hw hu
      have hcolor := branchGet a.s a.pos a.neg a.X a.side a.Y _ _ _ i hw hu
      simp only [i.isLt, if_true, not_lt_of_ge (Nat.le_add_right n (j : ℕ)), if_false,
        truth_and, truth_not, hreq, hcolor, Data.color, Bool.not_eq_true]
      split_ifs <;> rfl
    · simp only [Data.slot_old] at hv ⊢
      simp only [Data.slot_new]
      have hreq := required_spec a j hw hv
      have hcolor := branchGet a.s a.pos a.neg a.X a.side a.Y _ _ _ j hw hv
      simp only [j.isLt, if_true, not_lt_of_ge (Nat.le_add_right n (i : ℕ)), if_false,
        truth_and, hreq, hcolor, Data.color]
      split_ifs <;> rfl
    · simp only [Data.slot_new]
      simp [Expr.run, not_lt_of_ge (Nat.le_add_right n (i : ℕ)), not_lt_of_ge (Nat.le_add_right n (j : ℕ))]

end PEqualNP.Outside.L_meta_33604_aux.Writer


namespace PEqualNP.Outside.L_meta_33604_aux.Writer

open PEqualNP.Outside.L_meta_33604_aux.Core
open scoped Classical

private theorem complement_equiv {U D : Type*} {P Q : U → Prop}
    (m : Subtype P ≃ Subtype Q) (g : Equiv.Perm (U ⊕ D)) (hg : extendsMatch m g) :
    Nonempty ({i // ¬P i} ≃ D) := by
  classical
  let f (i : {i // ¬P i}) := Classical.choose (hg.2.1 i)
  have hf (i : {i // ¬P i}) : g (.inl i.1) = .inr (f i) := Classical.choose_spec (hg.2.1 i)
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩⟩
  · intro i j eq
    apply Subtype.ext
    apply Sum.inl.inj (g.injective ?_)
    rw [hf i, hf j, eq]
  · intro j
    obtain ⟨src, he⟩ := g.surjective (.inr j)
    cases src with
    | inl i =>
      have hi : ¬ P i := by
        intro p
        have e := hg.1 ⟨i,p⟩
        rw [e] at he
        cases he
      exact ⟨⟨i,hi⟩, Sum.inr.inj ((hf ⟨i,hi⟩).symm.trans he)⟩
    | inr i =>
      obtain ⟨v,hv⟩ := hg.2.2 i
      rw [hv] at he
      cases he

private theorem card_missing {n : ℕ} (c : Fin n → Bool) (p : Equiv.Perm (Fin n))
    (hp : Function.Involutive p) (cross : ∀ i, p i ≠ i → c i ≠ c (p i)) :
    Nat.card {i // ¬ movesOn c p true i} = n - (edgesOf p).card ∧
    Nat.card {i // ¬ movesOn c p false i} = n - (edgesOf p).card := by
  classical
  have htrue := moved_card c p hp cross
  have hfalse : Nat.card (Subtype (movesOn c p false)) = (edgesOf p).card := by
    rw [← Nat.card_congr (mateMap c p hp cross), htrue]
  rw [Nat.card_eq_fintype_card] at htrue hfalse ⊢
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_compl,
    Fintype.card_fin, htrue, hfalse]
  exact ⟨rfl,rfl⟩

private theorem oldPart_unique {U D : Type*} (g : Equiv.Perm (U ⊕ D)) (c : U → Bool)
    (p : Equiv.Perm U) (hp : Function.Involutive p) (hc : ∀ i, p i ≠ i → c i ≠ c (p i))
    (h : extendsMatch (mateMap c p hp hc) g) : oldPart g c = p := by
  classical
  have ex := ((extends_mate c p hp hc g).mp h).2
  funext i
  by_cases move : p i ≠ i
  · cases side : c i
    · have other : c (p i) = true := by simpa [side] using hc i move
      have im : g (.inl (p i)) = .inl i := (ex i (p i)).mpr ⟨other,hp i,move.symm⟩
      have rev : g.symm (.inl i) = .inl (p i) := (g.symm_apply_eq).mpr im.symm
      simp [oldPart, side, rev]
    · have im : g (.inl i) = .inl (p i) := (ex (p i) i).mpr ⟨side,rfl,move⟩
      simp [oldPart, side, im]
  · have fixed : p i = i := not_not.mp move
    rw [fixed]
    cases side : c i
    · cases eq : g.symm (.inl i) with
      | inr d => simp [oldPart, side, eq]
      | inl j =>
        have im : g (.inl j) = .inl i := (g.apply_eq_iff_eq_symm_apply).mpr eq.symm
        obtain ⟨_,hj,ne⟩ := (ex i j).mp im
        have eqj := congrArg p hj
        rw [hp j, fixed] at eqj
        exact (ne eqj.symm).elim
    · cases eq : g (.inl i) with
      | inr d => simp [oldPart, side, eq]
      | inl j =>
        obtain ⟨_,hj,ne⟩ := (ex j i).mp eq
        rw [fixed] at hj
        exact (ne hj.symm).elim

private def Data.Good {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n)) : Prop :=
  Function.Involutive p ∧
  (∀ i, p i ≠ i → a.color i ≠ a.color (p i)) ∧
  (∀ j, p j ≠ j → a.color j = true → a.crossPair (p j) j ∧ ¬a.forbidden (p j) j) ∧
  (∀ i, p i = i → ¬a.required i) ∧ (edgesOf p).card = a.s

private abbrev GridPerm {n : ℕ} (a : Data n) := Equiv.Perm (Fin n ⊕ Fin (n-a.s))
private def Data.Legal {n : ℕ} (a : Data n) (g : GridPerm a) := ∀ j, 0 < a.grid (g j) j

private theorem legal_cross {n : ℕ} (a : Data n) (g : GridPerm a) (h : a.Legal g) (nf : ¬a.fatal) :
    ∀ i j, g (.inl j) = .inl i → a.crossPair i j ∧ ¬a.forbidden i j := by
  intro i j eq
  have pos := h (.inl j)
  rw [eq] at pos
  by_contra bad
  simp [Data.grid, nf, bad] at pos

private theorem legal_involution {n : ℕ} (a : Data n) (g : GridPerm a) (h : a.Legal g) (nf : ¬a.fatal) :
    Function.Involutive (oldPart g a.color) :=
  (oldPart_laws g a.color (fun i j eq => (legal_cross a g h nf i j eq).1.2)).1

private def legalMate {n : ℕ} (a : Data n) (g : GridPerm a) (h : a.Legal g) (nf : ¬a.fatal) :
    Equiv.Perm (Fin n) := (legal_involution a g h nf).toPerm _

private theorem legal_mate_good {n : ℕ} (a : Data n) (hs : a.s ≤ n) (g : GridPerm a)
    (h : a.Legal g) (nf : ¬a.fatal) : a.Good (legalMate a g h nf) := by
  classical
  let p := legalMate a g h nf
  have hp : Function.Involutive p := legal_involution a g h nf
  have hcross := legal_cross a g h nf
  have law := (oldPart_laws g a.color (fun i j eq => (hcross i j eq).1.2)).2
  change ∀ i j, g (.inl j) = .inl i ↔ a.color j = true ∧ p j = i ∧ i ≠ j at law
  have moves (i : Fin n) (hm : p i ≠ i) : a.color i ≠ a.color (p i) := by
    cases ht : a.color i
    · cases v : g.symm (.inl i) with
      | inr k => exact (hm (by simpa [p, legalMate, oldPart, ht, v])).elim
      | inl j =>
        have im : g (.inl j) = .inl i := (g.apply_eq_iff_eq_symm_apply).mpr v.symm
        have eq : p i = j := by simp [p, legalMate, oldPart, ht, v]
        rw [eq, (hcross i j im).1.2.2]
        decide
    · have im := (law (p i) i).mpr ⟨ht,rfl,hm⟩
      rw [(hcross (p i) i im).1.2.1]
      decide
  have noDD (j k : Fin (n-a.s)) : g (.inr j) ≠ .inr k := by
    intro eq
    have t := h (.inr j)
    rw [eq] at t
    simp [Data.grid,nf] at t
  have ext : extendsMatch (mateMap a.color p hp moves) g := (extends_mate _ _ hp moves _).mpr ⟨noDD, law⟩
  refine ⟨hp,moves,fun j hj hc => hcross (p j) j ((law (p j) j).mpr ⟨hc,rfl,hj⟩),?_,?_⟩
  · intro i same req
    cases side : a.color i
    · cases v : g.symm (.inl i) with
      | inl j =>
        have im : g (.inl j) = .inl i := (g.apply_eq_iff_eq_symm_apply).mpr v.symm
        have eq : p i = j := by simp [p, legalMate, oldPart, side, v]
        exact ((law i j).mp im).2.2 (same.symm.trans eq)
      | inr j =>
        have im : g (.inr j) = .inl i := (g.apply_eq_iff_eq_symm_apply).mpr v.symm
        have t := h (.inr j)
        rw [im] at t
        simp [Data.grid,nf,side,req] at t
    · cases v : g (.inl i) with
      | inl j =>
        obtain ⟨_,same',ne⟩ := (law j i).mp v
        exact ne (same'.symm.trans same)
      | inr j =>
        have t := h (.inl i)
        rw [v] at t
        simp [Data.grid,nf,side,req] at t
  · obtain ⟨f⟩ := complement_equiv _ g ext
    have card := Nat.card_congr f
    have miss := (card_missing a.color p hp moves).1
    rw [miss, Nat.card_fin] at card
    have actualBound : (edgesOf p).card ≤ n := by
      have hb := Fintype.card_subtype_le (movesOn a.color p true)
      rw [← Nat.card_eq_fintype_card, moved_card _ _ hp moves, Fintype.card_fin] at hb
      exact hb
    change (edgesOf p).card = a.s
    omega

private theorem extension_legal {n : ℕ} (a : Data n) (nf : ¬a.fatal) (p : Equiv.Perm (Fin n))
    (hp : a.Good p) (g : GridPerm a) (ext : extendsMatch (mateMap a.color p hp.1 hp.2.1) g) :
    a.Legal g := by
  have law := ((extends_mate _ _ hp.1 hp.2.1 g).mp ext).2
  rintro (j | j)
  · cases eq : g (.inl j) with
    | inl i =>
      obtain ⟨side,eq',ne⟩ := (law i j).mp eq
      have good := hp.2.2.1 j (fun h => ne (eq'.symm.trans h)) side
      subst i
      by_cases touch : p j ∈ a.X ∨ j ∈ a.X <;> simp [Data.grid,nf,good.1,good.2,touch]
    | inr k =>
      have optional : ¬ (a.color j = true ∧ a.required j) := by
        rintro ⟨side,req⟩
        have move : p j ≠ j := fun eq => hp.2.2.2.1 j eq req
        have clash := (law (p j) j).mpr ⟨side,rfl,move⟩
        rw [eq] at clash
        cases clash
      simp [Data.grid, eq, nf, optional]
  · obtain ⟨i,eq⟩ := ext.2.2 j
    have optional : ¬ (a.color i = false ∧ a.required i) := by
      rintro ⟨side,req⟩
      have move : p i ≠ i := fun eq => hp.2.2.2.1 i eq req
      exact i.2 ⟨side,move⟩
    simp [Data.grid, eq, nf, optional]

private theorem legal_extension {n : ℕ} (a : Data n) (nf : ¬a.fatal) (g : GridPerm a)
    (h : a.Legal g) (p : Equiv.Perm (Fin n)) (hp : a.Good p)
    (same : legalMate a g h nf = p) : extendsMatch (mateMap a.color p hp.1 hp.2.1) g := by
  apply (extends_mate _ _ hp.1 hp.2.1 g).mpr
  constructor
  · intro j k eq
    have t := h (.inr j)
    rw [eq] at t
    simp [Data.grid,nf] at t
  · intro i j
    rw [← same]
    exact (oldPart_laws g a.color (fun i j eq => (legal_cross a g h nf i j eq).1.2)).2 i j

private def classify {n : ℕ} (a : Data n) (hs : a.s ≤ n) (nf : ¬a.fatal)
    (g : Subtype a.Legal) : Subtype a.Good :=
  ⟨legalMate a g.1 g.2 nf,legal_mate_good a hs g.1 g.2 nf⟩

private theorem classify_fiber {n : ℕ} (a : Data n) (hs : a.s ≤ n) (nf : ¬a.fatal)
    (p : Subtype a.Good) :
    Nat.card {g : Subtype a.Legal // classify a hs nf g = p} = (n-a.s).factorial ^ 2 := by
  classical
  let mate := mateMap a.color p.1 p.2.1 p.2.2.1
  let equiv : {g : Subtype a.Legal // classify a hs nf g = p} ≃
      {g : GridPerm a // extendsMatch mate g} :=
    { toFun := fun ⟨g,h⟩ => ⟨g.1,legal_extension a nf g.1 g.2 p.1 p.2 (congrArg Subtype.val h)⟩
      invFun := fun ⟨g,h⟩ =>
        ⟨⟨g,extension_legal a nf p.1 p.2 g h⟩,Subtype.ext (Equiv.ext fun i =>
          congrFun (oldPart_unique g a.color p.1 p.2.1 p.2.2.1 h) i)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have card := card_missing a.color p.1 p.2.1 p.2.2.1
  have leftEq : Nat.card {i // ¬movesOn a.color p.1 true i} = Nat.card (Fin (n-a.s)) := by
    rw [card.1, p.2.2.2.2.2, Nat.card_fin]
  have rightEq : Nat.card (Fin (n-a.s)) = Nat.card {i // ¬movesOn a.color p.1 false i} := by
    rw [card.2, p.2.2.2.2.2, Nat.card_fin]
  let e₁ : {i // ¬movesOn a.color p.1 true i} ≃ Fin (n-a.s) :=
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using leftEq)
  let e₂ : Fin (n-a.s) ≃ {i // ¬movesOn a.color p.1 false i} :=
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using rightEq)
  rw [Nat.card_congr equiv, extension_factor mate e₁ e₂, Nat.card_fin]

end PEqualNP.Outside.L_meta_33604_aux.Writer


namespace PEqualNP.Outside.L_meta_33604_aux.Writer

open PEqualNP.Outside.L_meta_33604_aux.Core
open scoped BigOperators Classical

private theorem rep_opposite {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (X : Finset (Fin n)) (i : Fin n) (r : rep p X i) : ¬rep p X (p i) := by
  rintro ⟨hj,_,out | back⟩
  · exact out (by simpa [hp i] using r.1)
  · rcases r.2.2 with out | forward
    · exact out hj
    · rw [hp i] at back
      exact not_lt_of_ge forward.le back

private theorem rep_touch {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (X : Finset (Fin n)) (i : Fin n) (move : p i ≠ i) (touch : i ∈ X ∨ p i ∈ X) :
    rep p X i ∨ rep p X (p i) := by
  by_cases hi : i ∈ X <;> by_cases hj : p i ∈ X
  · rcases lt_or_gt_of_ne move with lt | lt
    · exact Or.inr ⟨hj, by simpa [hp i] using move.symm, Or.inr (by simpa [hp i] using lt)⟩
    · exact Or.inl ⟨hi,move,Or.inr lt⟩
  · exact Or.inl ⟨hi,move,Or.inl hj⟩
  · exact Or.inr ⟨hj,by simpa [hp i] using move.symm,Or.inl (by simpa [hp i] using hi)⟩
  · exact (touch.elim hi hj).elim

private def marking {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n)) : Fin n ⊕ Fin (n-a.s) → Prop
  | .inl i => a.color i = true ∧ p i ≠ i ∧ (i ∈ a.X ∨ p i ∈ a.X)
  | .inr _ => False

private theorem marking_card {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n)) (hp : a.Good p) :
    Nat.card (Subtype (marking a p)) = Nat.card (Subtype (rep p a.X)) := by
  classical
  have inv := hp.1
  have moves := hp.2.1
  let pick (j : Fin n) (h : marking a p (.inl j)) : Subtype (rep p a.X) :=
    if r : rep p a.X j then ⟨j,r⟩ else ⟨p j, (rep_touch p inv a.X j h.2.1 h.2.2).resolve_left r⟩
  let decode (r : Subtype (rep p a.X)) : Subtype (marking a p) :=
    if h : a.color r = true then ⟨.inl r.1,h,r.2.2.1,Or.inl r.2.1⟩ else
      ⟨.inl (p r),by
        have ne := moves r r.2.2.1
        cases h₁ : a.color r <;> cases h₂ : a.color (p r) <;> simp_all,
        by simpa [inv r] using r.2.2.1.symm, Or.inr (by simpa [inv r] using r.2.1)⟩
  let encode : Subtype (marking a p) → Subtype (rep p a.X) := fun ⟨j,h⟩ =>
    match j with
    | .inl j => pick j h
    | .inr _ => h.elim
  have left (j : Subtype (marking a p)) : decode (encode j) = j := by
    rcases j with ⟨j | j,h⟩
    · have side : a.color j = true := h.1
      have other : a.color (p j) ≠ true := fun e => moves j h.2.1 (side.trans e.symm)
      apply Subtype.ext
      by_cases r : rep p a.X j <;> simp [encode, decode, pick, r, side, other, inv j]
    · exact h.elim
  have right (i : Subtype (rep p a.X)) : encode (decode i) = i := by
    apply Subtype.ext
    by_cases h : a.color i = true <;> simp [decode,encode,pick,h,i.2,rep_opposite p inv a.X i i.2,inv i]
  exact Nat.card_congr ⟨encode,decode,left,right⟩

private theorem fixed_weight {n : ℕ} (a : Data n) (nf : ¬a.fatal) (p : Equiv.Perm (Fin n))
    (hp : a.Good p) (g : GridPerm a) (ext : extendsMatch (mateMap a.color p hp.1 hp.2.1) g) :
    (∏ j, a.grid (g j) j) = Nat.card (Subtype (rep p a.X) → Bool) := by
  classical
  have law := ((extends_mate _ _ hp.1 hp.2.1 g).mp ext).2
  have pos := extension_legal a nf p hp g ext
  have term (j : Fin n ⊕ Fin (n-a.s)) : a.grid (g j) j = if marking a p j then 2 else 1 := by
    cases j with
    | inl j =>
      cases h : g (.inl j) with
      | inl i =>
        obtain ⟨side,eq,ne⟩ := (law i j).mp h
        have move : p j ≠ j := fun q => ne (eq.symm.trans q)
        have good := hp.2.2.1 j move side
        subst i
        simp [h,Data.grid,nf,good,marking,side,move,or_comm]
      | inr d =>
        have absent : ¬marking a p (.inl j) := by
          intro m
          have real := (law (p j) j).mpr ⟨m.1,rfl,m.2.1⟩
          rw [h] at real
          cases real
        have nz := pos (.inl j)
        rw [h] at nz
        by_cases bad : a.color j = true ∧ a.required j
        · simp [Data.grid,nf,bad] at nz
        · simp [Data.grid,nf,bad,absent]
    | inr j =>
      obtain ⟨i,h⟩ := ext.2.2 j
      have nz := pos (.inr j)
      rw [h] at nz ⊢
      by_cases bad : a.color i = false ∧ a.required i
      · simp [Data.grid,nf,bad] at nz
      · simp [Data.grid,nf,bad,marking]
  simp_rw [term]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.prod_const_one, mul_one, Nat.card_fun]
  have b : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [b, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, marking_card a p hp]
  simp

private def Data.Win {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n)) := ¬a.fatal ∧ a.Good p
private noncomputable def markTotal {n : ℕ} (X : Finset (Fin n)) (p : Equiv.Perm (Fin n)) :=
  Nat.card (Subtype (rep p X) → Bool)

private theorem grid_count {n : ℕ} (a : Data n) (hn : 0 < n) (hs : a.s ≤ n) :
    a.grid.permanent = (n-a.s).factorial ^ 2 * ∑ p : Subtype a.Win, markTotal a.X p.1 := by
  classical
  by_cases nf : ¬a.fatal
  · let P := Subtype a.Good
    let G := Subtype a.Legal
    let K (p : P) := {g : G // classify a hs nf g = p}
    let ce : (Σ p : P, K p) ≃ G := Equiv.sigmaFiberEquiv (classify a hs nf)
    let pw (g : GridPerm a) := ∏ j, a.grid (g j) j
    have zero (g : GridPerm a) (ng : ¬a.Legal g) : pw g = 0 := by
      have ⟨j, bad⟩ : ∃ j, ¬ 0 < a.grid (g j) j := not_forall.mp ng
      exact Finset.prod_eq_zero (Finset.mem_univ j) (Nat.eq_zero_of_not_pos bad)
    have first : a.grid.permanent = ∑ g : G, pw g.1 := by
      rw [Matrix.permanent, ← Finset.sum_filter_add_sum_filter_not Finset.univ a.Legal pw]
      rw [Finset.sum_eq_zero (fun g hg => zero g (Finset.mem_filter.mp hg).2), add_zero]
      simpa only [Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) pw (p := a.Legal)).symm
    have switch : (∑ g : G, pw g.1) = ∑ z : Σ p : P, K p, pw (ce z).1 :=
      (Fintype.sum_equiv ce _ _ (fun _ => rfl)).symm
    have fibers : (∑ z : Σ p : P, K p, pw (ce z).1) = (n-a.s).factorial ^ 2 * ∑ p : P, markTotal a.X p.1 := by
      rw [Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have weight (g : K p) : pw g.1.1 = markTotal a.X p.1 := by
        apply fixed_weight a nf p.1 p.2 g.1.1
        exact legal_extension a nf g.1.1 g.1.2 p.1 p.2 (congrArg Subtype.val g.2)
      change (∑ g : K p, pw g.1.1) = _
      simp_rw [weight]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card, classify_fiber a hs nf]
      rfl
    rw [first,switch,fibers]
    congr 1
    let e : P ≃ Subtype a.Win := Equiv.subtypeEquivRight (fun _ => (and_iff_right nf).symm)
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · have yes := not_not.mp nf
    haveI : IsEmpty (Subtype a.Win) := ⟨fun z => z.2.1 yes⟩
    simp only [Fintype.sum_empty, mul_zero, Matrix.permanent]
    apply Finset.sum_eq_zero
    intro g _
    exact Finset.prod_eq_zero (Finset.mem_univ (.inl ⟨0,hn⟩)) (by simp [Data.grid,yes])

end PEqualNP.Outside.L_meta_33604_aux.Writer


namespace PEqualNP.Outside.L_meta_33604_aux.Writer

open PEqualNP.Outside.L_meta_33604_aux.Core
open scoped Classical BigOperators

private def ordered {n : ℕ} (i j : Fin n) : Fin n × Fin n := if i < j then (i,j) else (j,i)

private theorem ordered_ends {n : ℕ} (i j : Fin n) : pairEnds (ordered i j) = pairEnds (i,j) := by
  unfold ordered
  split_ifs
  · rfl
  · ext v
    simp [pairEnds, or_comm]

private noncomputable def Data.E {n : ℕ} (a : Data n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ ∀ z ∈ a.neg, ¬pairEnds e ⊆ z.1 ∧ ¬pairEnds e ⊆ z.2)

private theorem free_iff {n : ℕ} (a : Data n) (i j : Fin n) : a.freePair i j ↔ ordered i j ∈ a.E := by
  classical
  simp only [Data.E, Finset.mem_filter, Finset.mem_univ, true_and, ordered_ends, Data.freePair]
  have lt : (ordered i j).1 < (ordered i j).2 ↔ i ≠ j := by
    by_cases h : i < j
    · simp [ordered,h,h.ne]
    · simp only [ordered,h,if_false]
      exact ⟨fun lt => lt.ne.symm,fun ne => lt_of_le_of_ne (le_of_not_gt h) ne.symm⟩
  rw [lt]

private theorem ordered_mem {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (i j : Fin n) (move : p i = j) (ne : i ≠ j) : ordered i j ∈ edgesOf p := by
  have back : p j = i := by rw [← move,hp]
  by_cases lt : i < j
  · simp [ordered,lt,edgesOf,move]
  · have gt : j < i := lt_of_le_of_ne (le_of_not_gt lt) ne.symm
    simp [ordered,lt,edgesOf,back,gt]

private theorem in_edge {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Function.Involutive p)
    (e : Fin n × Fin n) (he : e ∈ edgesOf p) (v : Fin n) (hv : v ∈ pairEnds e) :
    p v ≠ v ∧ pairEnds (v,p v) = pairEnds e := by
  obtain ⟨lt, app⟩ := (Finset.mem_filter.mp he).2
  simp only [pairEnds, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨fun h => lt.ne (h.symm.trans app), by rw [app]⟩
  · have back : p e.2 = e.1 := by rw [← app,hp]
    refine ⟨fun h => lt.ne (back.symm.trans h), ?_⟩
    rw [back]
    ext v
    simp [pairEnds,or_comm]

private def Data.Star {n : ℕ} (a : Data n) :=
  ∀ R ∈ a.pos, ∀ e ∈ a.E, pairEnds e ⊆ R → ∀ f ∈ a.E, pairEnds f ⊆ R →
    ¬Disjoint (pairEnds e) (pairEnds f)

private theorem common_vertex {n : ℕ} (a : Data n) (star : a.Star) (R : Finset (Fin n))
    (hR : R ∈ a.pos) (nb : ¬a.barren R) : ∃ v, a.common R v := by
  classical
  let B := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => a.crossPair e.1 e.2 ∧ a.inside R e.1 e.2)
  have mem (e : Fin n × Fin n) : e ∈ B ↔ a.crossPair e.1 e.2 ∧ a.inside R e.1 e.2 := by simp [B]
  have bn : B.Nonempty := by
    obtain ⟨i,j,hi⟩ := not_not.mp nb
    exact ⟨(i,j),(mem _).mpr hi⟩
  have bc (e) (he : e ∈ B) : a.color e.1 = false ∧ a.color e.2 = true := ((mem e).mp he).1.2
  have meet (e) (he : e ∈ B) (f) (hf : f ∈ B) : ¬Disjoint (ends e) (ends f) := by
    obtain ⟨hce,hi⟩ := (mem e).mp he
    obtain ⟨hcf,hj⟩ := (mem f).mp hf
    have se := (free_iff a e.1 e.2).mp hce.1
    have sf := (free_iff a f.1 f.2).mp hcf.1
    have ei : pairEnds (ordered e.1 e.2) ⊆ R := by rw [ordered_ends]; exact hi
    have fi : pairEnds (ordered f.1 f.2) ⊆ R := by rw [ordered_ends]; exact hj
    have disj := star R hR _ se ei _ sf fi
    rw [ordered_ends, ordered_ends] at disj
    exact disj
  obtain ⟨v,hv⟩ := bipartite_star a.color B bn bc meet
  exact ⟨v,fun i j c r => by simpa [ends] using hv (i,j) ((mem _).mpr ⟨c,r⟩)⟩

private def Data.Base {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n)) :=
  Function.Involutive p ∧ (∀ R ∈ a.pos, ∃ e ∈ edgesOf p, pairEnds e ⊆ R) ∧
    ((∀ z ∈ a.neg, Disjoint z.1 z.2) ∧ edgesOf p ⊆ a.E) ∧ (edgesOf p).card = a.s

private theorem oriented_mate {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n))
    (hp : Function.Involutive p) (cross : ∀ i, p i ≠ i → a.color i ≠ a.color (p i))
    (i : Fin n) (h : p i ≠ i) :
    ∃ j, a.color j = true ∧ p j ≠ j ∧ pairEnds (p j,j) = pairEnds (i,p i) ∧ (i = p j ∨ i = j) := by
  cases side : a.color i
  · have other : a.color (p i) = true := by simpa [side] using cross i h
    exact ⟨p i,other,by simpa [hp i] using h.symm,by simp only [hp i],Or.inl (hp i).symm⟩
  · refine ⟨i,side,h,?_,Or.inr rfl⟩
    ext v
    simp [pairEnds,or_comm]

private theorem win_iff {n : ℕ} (a : Data n) (star : a.Star) (p : Equiv.Perm (Fin n)) :
    a.Win p ↔ a.Base p ∧ ∀ i, p i ≠ i → a.color i ≠ a.color (p i) := by
  classical
  constructor
  · rintro ⟨nf,hp,cross,allow,optional,size⟩
    have negatives : ∀ z ∈ a.neg, Disjoint z.1 z.2 := by
      intro z hz
      by_contra b
      exact nf (Or.inl ⟨z,hz,b⟩)
    have allowed : edgesOf p ⊆ a.E := by
      intro e he
      obtain ⟨hmove,baseEnds⟩ := in_edge p hp e he e.1 (by simp [pairEnds])
      obtain ⟨j,jc,jm,matchEnds,_⟩ := oriented_mate a p hp cross e.1 hmove
      have free := (allow j jm jc).1.1
      obtain ⟨ne,hneg⟩ := free
      have lt := (Finset.mem_filter.mp he).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt,by rwa [matchEnds,baseEnds] at hneg⟩
    have positives : ∀ R ∈ a.pos, ∃ e ∈ edgesOf p, pairEnds e ⊆ R := by
      intro R hR
      have nb : ¬a.barren R := fun b => nf (Or.inr ⟨R,hR,b⟩)
      obtain ⟨v,hv⟩ := common_vertex a star R hR nb
      have vm : p v ≠ v := fun fixed => optional v fixed ⟨R,hR,hv⟩
      obtain ⟨j,jc,jm,_,hinc⟩ := oriented_mate a p hp cross v vm
      have no := (allow j jm jc).2
      have inside : a.inside R (p j) j := by
        by_contra bad
        exact no ⟨R,hR,bad, hinc.elim (fun h => Or.inl (h ▸ hv)) (fun h => Or.inr (h ▸ hv))⟩
      have mem := ordered_mem p hp j (p j) rfl jm.symm
      refine ⟨_,mem,?_⟩
      rw [ordered_ends]
      exact (pair_subset R j (p j)).mpr ((pair_subset R (p j) j).mp inside).symm
    exact ⟨⟨hp,positives,⟨negatives,allowed⟩,size⟩,cross⟩
  · rintro ⟨⟨hp,positive,⟨negatives,allowed⟩,size⟩,cross⟩
    have hit (R) (hR : R ∈ a.pos) : ∃ j, a.crossPair (p j) j ∧ a.inside R (p j) j ∧ p j ≠ j := by
      obtain ⟨e, he, inside⟩ := positive R hR
      obtain ⟨hm,endsI⟩ := in_edge p hp e he e.1 (by simp [pairEnds])
      obtain ⟨j,side,move,endsJ,_⟩ := oriented_mate a p hp cross e.1 hm
      have other : a.color (p j) = false := by simpa [side] using cross j move
      have ends_eq : pairEnds (p j,j) = pairEnds e := endsJ.trans endsI
      have hn := (Finset.mem_filter.mp (allowed he)).2.2
      refine ⟨j, ⟨⟨move,by rwa [ends_eq]⟩,other,side⟩, ?_,move⟩
      simpa only [Data.inside,ends_eq] using inside
    refine ⟨?_,hp,cross,?_,?_,size⟩
    · rintro (⟨z,hz,bad⟩ | ⟨R,hR,none⟩)
      · exact bad (negatives z hz)
      · obtain ⟨j,hpair,hinside,_⟩ := hit R hR
        exact none ⟨p j,j,hpair,hinside⟩
    · intro j move side
      have back : p (p j) = j := hp j
      have free := (free_iff a (p j) j).mpr (allowed (ordered_mem p hp (p j) j back move))
      have other : a.color (p j) = false := by simpa [side] using cross j move
      refine ⟨⟨free,other,side⟩,?_⟩
      rintro ⟨R,hR,out,center⟩
      obtain ⟨k,ck,ik,mk⟩ := hit R hR
      cases center with
      | inl center =>
        rcases center (p k) k ck ik with h | h
        · have eq : j = k := p.injective h
          exact out (by simpa [eq] using ik)
        · have c := ck.2.2
          rw [← h,other] at c
          exact Bool.false_ne_true c
      | inr center =>
        rcases center (p k) k ck ik with h | h
        · have bad : a.color j = false := h ▸ ck.2.1
          simp [side] at bad
        · exact out (by simpa [h] using ik)
    · intro i fixed req
      obtain ⟨R,hR,center⟩ := req
      obtain ⟨j,cj,ij,mj⟩ := hit R hR
      rcases center (p j) j cj ij with rfl | rfl
      · rw [hp j] at fixed
        exact mj fixed.symm
      · exact mj fixed

end PEqualNP.Outside.L_meta_33604_aux.Writer


namespace PEqualNP.Outside.L_meta_33604_aux.Writer

open PEqualNP.Outside.L_meta_33604_aux.Core
open scoped Classical BigOperators

private theorem subtype_sum_ite {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (f : α → ℕ) :
    (∑ x : Subtype P, f x.1) = ∑ x, if P x then f x else 0 := by
  rw [← Finset.sum_filter]
  simpa only [Finset.subtype_univ] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) f (p := P))

private def Data.WithY {n : ℕ} (a : Data n) (Y : Finset (Fin n)) : Data n := { a with Y := Y }

private def Data.Proper {n : ℕ} (a : Data n) :=
  ∀ e ∈ a.E, e.1 ∉ a.X → e.2 ∉ a.X → a.side e.1 ≠ a.side e.2

private theorem compatible {n : ℕ} (a : Data n) (p : Equiv.Perm (Fin n)) (h : a.Base p) (pr : a.Proper) :
    ∀ i, i ∉ a.X → p i ∉ a.X → p i ≠ i → a.side i ≠ a.side (p i) := by
  intro i oi oj move
  have allowed := h.2.2.1.2 (ordered_mem p h.1 i (p i) rfl move.symm)
  by_cases lt : i < p i
  · simp only [ordered,lt,if_true] at allowed
    exact pr (i,p i) allowed oi oj
  · simp only [ordered,lt,if_false] at allowed
    exact (pr (p i,i) allowed oj oi).symm

private noncomputable def colors {n : ℕ} (X : Finset (Fin n)) (side : Fin n → Bool) :
    X.powerset ≃ {c : Fin n → Bool // ∀ i ∉ X, c i = side i} := by
  classical
  refine ⟨(fun Y => ⟨fun i => if i ∈ X then decide (i ∈ Y.1) else side i, fun i hi => if_neg hi⟩),
    (fun c => ⟨X.filter (fun i => c.1 i = true),Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩),?_,?_⟩
  · intro Y
    apply Subtype.ext
    ext i
    have sub : Y.1 ⊆ X := Finset.mem_powerset.mp Y.2
    by_cases hi : i ∈ X
    · simp [hi]
    · have ho : i ∉ Y.1 := fun h => hi (sub h)
      simp [hi,ho]
  · intro c
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ X
    · simp [hi]
    · simp [hi,c.2 i hi]

private theorem branch_total {n : ℕ} (a : Data n) (star : a.Star) (pr : a.Proper) :
    (∑ Y : a.X.powerset, ∑ p : Subtype (a.WithY Y.1).Win, markTotal a.X p.1) =
      2 ^ a.X.card * Nat.card (Subtype a.Base) := by
  classical
  let P := Subtype a.Base
  let C (Y : a.X.powerset) (p : Equiv.Perm (Fin n)) :=
    ∀ i, p i ≠ i → (a.WithY Y.1).color i ≠ (a.WithY Y.1).color (p i)
  let f (p : Equiv.Perm (Fin n)) := markTotal a.X p
  have inner (Y : a.X.powerset) :
      (∑ p : Subtype (a.WithY Y.1).Win, f p.1) = ∑ p : P, if C Y p.1 then f p.1 else 0 := by
    let e : Subtype (a.WithY Y.1).Win ≃ {p : P // C Y p.1} :=
      (Equiv.subtypeEquivRight (win_iff (a.WithY Y.1) star)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter a.Base (C Y)).symm
    rw [← subtype_sum_ite]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have outer (p : P) : (∑ Y : a.X.powerset, if C Y p.1 then f p.1 else 0) = 2 ^ a.X.card := by
    let pred (c : Fin n → Bool) := ∀ i, p.1 i ≠ i → c i ≠ c (p.1 i)
    let Z := {c : Fin n → Bool // (∀ i ∉ a.X, c i = a.side i) ∧ pred c}
    let col := colors a.X a.side
    let e' : Subtype (fun Y => C Y p.1) ≃ {c : {c : Fin n → Bool // ∀ i ∉ a.X, c i = a.side i} // pred c.1} :=
      col.subtypeEquiv (fun Y => show C Y p.1 ↔ pred (col Y).1 from Iff.rfl)
    let e : Subtype (fun Y => C Y p.1) ≃ Z :=
      e'.trans (Equiv.subtypeSubtypeEquivSubtypeInter _ pred)
    have h := color_factor p.1 p.2.1 a.X a.side (compatible a p.1 p.2 pr)
    change Nat.card (Σ _ : Z, Subtype (rep p.1 a.X) → Bool) = _ at h
    rw [Nat.card_congr (Equiv.sigmaEquivProd _ _), Nat.card_prod] at h
    rw [← subtype_sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, Nat.card_congr e]
    exact h
  change (∑ Y : a.X.powerset, ∑ p : Subtype (a.WithY Y.1).Win, f p.1) = _
  simp_rw [inner]
  rw [Finset.sum_comm]
  simp_rw [outer]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]
  rfl

private theorem grid_total {n : ℕ} (a : Data n) (hn : 0 < n) (hs : a.s ≤ n)
    (star : a.Star) (pr : a.Proper) :
    a.X.powerset.sum (fun Y => (a.WithY Y).grid.permanent) =
      2 ^ a.X.card * (n-a.s).factorial ^ 2 * Nat.card (Subtype a.Base) := by
  classical
  have each (Y : Finset (Fin n)) := grid_count (a.WithY Y) hn hs
  simp_rw [each]
  change (∑ Y ∈ a.X.powerset, (n-a.s).factorial ^ 2 * ∑ p : Subtype (a.WithY Y).Win,
    markTotal a.X p.1) = _
  rw [← Finset.mul_sum, ← Finset.sum_attach a.X.powerset]
  have reindex : a.X.powerset.attach = (Finset.univ : Finset (a.X.powerset : Type)) := by
    ext Y
    simp
  rw [reindex, branch_total a star pr]
  ring

private def Data.postedWord {n : ℕ} (a : Data n) : Bits :=
  let input := rawHeader n ++ rawHeader a.pos.length ++ a.pos.flatMap bankBits ++
    rawHeader a.neg.length ++ a.neg.flatMap negativeBank
  rawHeader a.s ++ input ++ bankBits a.X ++ List.ofFn a.side ++ bankBits a.Y

private theorem packed_word {n : ℕ} (a : Data n) : a.word = a.postedWord := by
  simp only [Data.word,Data.postedWord,packedInput,packedRows,packedNegative,endBanks,List.append_assoc]

private def Data.written {n : ℕ} (a : Data n) : Matrix (Fin (2*n-a.s)) (Fin (2*n-a.s)) Nat :=
  rawMatrix a.word (2*n-a.s)

private theorem written_spec {n : ℕ} (a : Data n) :
    (∀ i j, a.written i j ≤ 2) ∧
    writer a.postedWord = (List.finRange (2*n-a.s)).flatMap (fun i =>
      (List.finRange (2*n-a.s)).flatMap (fun j => [(a.written i j).testBit 0, (a.written i j).testBit 1])) := by
  rw [← packed_word a]
  exact writer_serializes a.s n (packedRows a.pos a.neg (endBanks a.X a.side a.Y))

private theorem written_permanent {n : ℕ} (a : Data n) (hs : a.s ≤ n) :
    a.written.permanent = a.grid.permanent := by
  let e := a.slot hs
  symm
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.equivCongr e e)
  intro g
  apply Fintype.prod_equiv e
  intro j
  have aligned : (Equiv.equivCongr e e g) (e j) = e (g j) := by
    simp only [Equiv.equivCongr_apply_apply, Equiv.symm_apply_apply]
  rw [aligned]
  exact (entry_read a hs (g j) j).symm

private noncomputable def Data.observedCount {n : ℕ} (a : Data n) :=
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
  let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    (∀ R ∈ a.pos, obs f R ∅ = true) ∧ (∀ z ∈ a.neg, obs f z.1 z.2 = false)
  let size := fun f : Fn => (Finset.univ.filter (fun e : Fin n × Fin n =>
    e.1 < e.2 ∧ obs f (pairEnds e) ∅ = true)).card
  Nat.card {f : Fn // fits f ∧ size f = a.s}

private theorem observed_eq_base {n : ℕ} (a : Data n) (hn : 2 ≤ n) :
    a.observedCount = Nat.card (Subtype a.Base) := by
  simp only [Data.observedCount, and_assoc]
  exact histogram_involutions n hn a.pos a.neg a.s

private theorem written_total {n : ℕ} (a : Data n) (hn : 2 ≤ n) (hs : a.s ≤ n)
    (star : a.Star) (pr : a.Proper) :
    a.X.powerset.sum (fun Y => (a.WithY Y).written.permanent) =
      2 ^ a.X.card * (n-a.s).factorial ^ 2 * a.observedCount := by
  rw [observed_eq_base a hn]
  calc
    _ = a.X.powerset.sum (fun Y => (a.WithY Y).grid.permanent) :=
      Finset.sum_congr rfl (fun Y _ => written_permanent (a.WithY Y) hs)
    _ = _ := grid_total a (by omega) hs star pr

end PEqualNP.Outside.L_meta_33604_aux.Writer

open PEqualNP.Outside.L_meta_33604_aux.Core PEqualNP.Outside.L_meta_33604_aux.Writer
open scoped Classical

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_33604 : (
let header := fun j : Nat => List.replicate j true ++ [false]
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)

∃ write : List Bool → List Bool, fast write ∧
∀ (n : Nat), 2 ≤ n →
  ∀ (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n))),
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let E := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2 ∧
    ∀ z ∈ neg, ¬(ends e ⊆ z.1) ∧ ¬(ends e ⊆ z.2))
  let proper := fun (X : Finset (Fin n)) (side : Fin n → Bool) =>
    ∀ e ∈ E, e.1 ∉ X → e.2 ∉ X → side e.1 ≠ side e.2
  (∀ R ∈ pos, ∀ e ∈ E, ends e ⊆ R → ∀ f ∈ E, ends f ⊆ R →
    ¬Disjoint (ends e) (ends f)) →
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
  let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false)

  let size := fun f : Fn => (Finset.univ.filter (fun z : Fin n × Fin n =>
    z.1 < z.2 ∧ obs f {z.1,z.2} ∅ = true)).card
  let hist := fun s : Nat => Nat.card {f : Fn // fits f ∧ size f = s}

  let bank := fun R : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ R))
  let input := header n ++ header pos.length ++ pos.flatMap bank ++
    header neg.length ++ neg.flatMap (fun z => bank z.1 ++ bank z.2)

  ∀ (X : Finset (Fin n)) (side : Fin n → Bool), proper X side →
    ∀ s : Nat, s ≤ n/2 →
      let d := 2*n-s
      ∃ A : Finset (Fin n) → Matrix (Fin d) (Fin d) Nat,
        (∀ Y ∈ X.powerset, (∀ i j, A Y i j ≤ 2) ∧
          write (header s ++ input ++ bank X ++ List.ofFn side ++ bank Y) =
            (List.finRange d).flatMap (fun i => (List.finRange d).flatMap (fun j =>
              [(A Y i j).testBit 0, (A Y i j).testBit 1]))) ∧
        X.powerset.sum (fun Y => (A Y).permanent) =
          2^X.card * ((n-s).factorial)^2 * hist s
) := by
  classical
  refine ⟨writer,writer_fast,?_⟩
  intro n hn pos neg
  dsimp only
  intro star X side proper s hs
  have hsn : s ≤ n := by omega
  let a : Data n := ⟨s,pos,neg,X,side,∅⟩
  have astar : a.Star := star
  have aproper : a.Proper := proper
  let A (Y : Finset (Fin n)) := (a.WithY Y).written
  refine ⟨A,?_,?_⟩
  · intro Y _
    exact written_spec (a.WithY Y)
  · exact written_total a hn hsn astar aproper
