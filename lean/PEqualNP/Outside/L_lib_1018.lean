import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1018

-- The machine toolkit and fixed-width arithmetic below come from
-- e01c7200bf1eeecfb2739fd2504543e799a6d8e7:lean/PEqualNP/Outside/L_meta_32050.lean.
-- The reusable toolkit has the original names; the arithmetic sits in MachineBits.
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

namespace MachineBits
open PEqualNP.Library Lib Lib.Universal Lib.Machines
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
end MachineBits

open MachineBits


abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev Row (n : ℕ) := Finset (Edge n) × Bool

def ends {n : ℕ} (e : Edge n) : Finset (Fin n) := {e.1, e.2}

def disjointEdges {n : ℕ} (Q : Finset (Edge n)) : Prop :=
  ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)

def choices {n : ℕ} (E : Finset (Edge n)) (k : ℕ) : Finset (Finset (Edge n)) :=
  E.powerset.filter (fun Q => Q.card = k ∧
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f))

def signed {n : ℕ} (rows : List (Row n)) (Q : Finset (Edge n)) : ℤ :=
  ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : ℤ) -
    ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : ℤ)

def weight {n : ℕ} (Q : Finset (Edge n)) : ℕ :=
  let V := Q.biUnion ends
  V.prod (fun i => (V.filter (fun j => i < j)).prod (fun j => (j.val-i.val)^2))

def total {n : ℕ} (E : Finset (Edge n)) (k : ℕ) (rows : List (Row n)) : ℕ :=
  (choices E k).sum (fun Q => weight Q * (signed rows Q).natAbs^2)

lemma weight_pos {n : ℕ} (Q : Finset (Edge n)) : 0 < weight Q := by
  unfold weight
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => pow_pos ?_ _
  exact Nat.sub_pos_of_lt (Finset.mem_filter.mp hj).2

lemma total_pos {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) :
    0 < total E k rows ↔ ∃ Q ∈ choices E k, signed rows Q ≠ 0 := by
  classical
  have hz : total E k rows = 0 ↔ ∀ Q ∈ choices E k, signed rows Q = 0 := by
    rw [total, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    refine forall_congr' fun Q => imp_congr_right fun _ => ?_
    simp [(Nat.pos_iff_ne_zero.mp (weight_pos Q))]
  rw [Nat.pos_iff_ne_zero]
  change (¬ total E k rows = 0) ↔ _
  rw [hz]
  push_neg
  rfl

def sign (b : Bool) : ℤ := if b then 1 else -1

def rowContribution {n : ℕ} (Q : Finset (Edge n)) (r : Row n) : ℤ :=
  if Q ⊆ r.1 then sign r.2 else 0

lemma signed_eq_sum {n : ℕ} (rows : List (Row n)) (Q : Finset (Edge n)) :
    signed rows Q = (rows.map (rowContribution Q)).sum := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    unfold signed rowContribution sign
    split <;> cases hr : r.2 <;> simp [*] <;> ring

lemma list_sum_finset_sum {α β : Type*} (L : List α) (S : Finset β) (f : α → β → ℤ) :
    (L.map (fun a => ∑ b ∈ S, f a b)).sum = ∑ b ∈ S, (L.map (fun a => f a b)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

lemma filter_choices {n k : ℕ} (E A B : Finset (Edge n)) :
    (choices E k).filter (fun Q => Q ⊆ A ∧ Q ⊆ B) = choices (E ∩ A ∩ B) k := by
  ext Q
  simp only [choices, Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  tauto

lemma weight_cast_sq {z : ℤ} : ((z.natAbs^2 : ℕ) : ℤ) = z^2 := by
  simpa only [pow_two] using (Int.natAbs_mul_self (a := z))

lemma total_eq_row_pairs {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) :
    (total E k rows : ℤ) = (rows.map (fun r => (rows.map (fun s =>
      sign r.2 * sign s.2 * (choices (E ∩ r.1 ∩ s.1) k).sum (fun Q => (weight Q : ℤ)))).sum)).sum := by
  classical
  have hh (r s : Row n) :
      sign r.2 * sign s.2 * (choices (E ∩ r.1 ∩ s.1) k).sum (fun Q => (weight Q : ℤ)) =
        (choices E k).sum (fun Q => (weight Q : ℤ) * rowContribution Q r * rowContribution Q s) := by
    rw [← filter_choices, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    by_cases hr : Q ⊆ r.1 <;> by_cases hs : Q ⊆ s.1 <;>
      simp [rowContribution, hr, hs] <;> ring
  simp_rw [hh, list_sum_finset_sum]
  unfold total
  simp only [Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro Q _
  rw [weight_cast_sq, signed_eq_sum]
  have inner (r : Row n) :
      (rows.map (fun s => (weight Q : ℤ) * rowContribution Q r * rowContribution Q s)).sum =
        (weight Q : ℤ) * rowContribution Q r * (rows.map (rowContribution Q)).sum := by
    rw [List.sum_map_mul_left]
  simp_rw [inner, List.sum_map_mul_right, List.sum_map_mul_left]
  ring

def width (n m : ℕ) : ℕ := n*n + (2*n)*n*n + 2*m + 1

lemma weight_le {n : ℕ} (Q : Finset (Edge n)) : weight Q ≤ 2 ^ ((2*n)*n*n) := by
  unfold weight
  let V := Q.biUnion ends
  have hv : V.card ≤ n := by simpa using Finset.card_le_univ V
  have hinner (i : Fin n) :
      (V.filter (fun j => i < j)).prod (fun j => (j.val-i.val)^2) ≤ (2^(2*n))^n := by
    calc
      _ ≤ (2^(2*n))^((V.filter (fun j => i < j)).card) := by
        apply Finset.prod_le_pow_card
        intro j _
        rw [mul_comm 2 n, pow_mul]
        exact Nat.pow_le_pow_left (Nat.sub_le .. |>.trans (j.isLt.le.trans (Nat.lt_two_pow_self).le)) 2
      _ ≤ _ := Nat.pow_le_pow_right (by positivity) ((Finset.card_filter_le _ _).trans hv)
  calc
    _ ≤ ((2^(2*n))^n)^V.card := Finset.prod_le_pow_card _ _ _ (fun i _ => hinner i)
    _ ≤ ((2^(2*n))^n)^n := Nat.pow_le_pow_right (by positivity) hv
    _ = _ := by simp only [← pow_mul, Nat.mul_assoc]

lemma signed_abs_le {n : ℕ} (rows : List (Row n)) (Q : Finset (Edge n)) :
    (signed rows Q).natAbs ≤ rows.length := by
  unfold signed
  have hp := List.length_filter_le (p := fun t : Row n => t.2 && decide (Q ⊆ t.1)) (l := rows)
  have hm := List.length_filter_le (p := fun t : Row n => !t.2 && decide (Q ⊆ t.1)) (l := rows)
  omega

lemma total_lt {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) :
    total E k rows < 2^(width n rows.length) := by
  have hE : E.card ≤ n*n := by simpa [Fintype.card_prod] using Finset.card_le_univ E
  have hC : (choices E k).card ≤ 2^(n*n) := by
    apply le_trans (Finset.card_filter_le _ _)
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by decide) hE
  have hm (Q : Finset (Edge n)) : (signed rows Q).natAbs^2 ≤ 2^(2*rows.length) := by
    rw [mul_comm 2 rows.length, pow_mul]
    exact Nat.pow_le_pow_left ((signed_abs_le rows Q).trans (Nat.lt_two_pow_self).le) 2
  calc
    total E k rows ≤ (choices E k).card * (2^((2*n)*n*n) * 2^(2*rows.length)) := by
      unfold total
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul (choices E k) (fun Q => weight Q * (signed rows Q).natAbs^2)
          (2^((2*n)*n*n) * 2^(2*rows.length)) (fun Q _ => Nat.mul_le_mul (weight_le Q) (hm Q))
    _ ≤ 2^(n*n) * (2^((2*n)*n*n) * 2^(2*rows.length)) := Nat.mul_le_mul_right _ hC
    _ = 2^(n*n + (2*n)*n*n + 2*rows.length) := by rw [← mul_assoc, ← pow_add, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by simp [width])

-- Packed-machine padding and finite-alphabet transport adapted from
-- e01c7200bf1eeecfb2739fd2504543e799a6d8e7:lean/PEqualNP/Outside/L_lib_1048.lean,
-- lines 3665–3676, 3777–3974 and 10399–10593. The parameter extractor is now
-- an argument, and the second unary header uses the shared parsing combinators.
-- Shared machine interface: the same revision of L_meta_32050.lean, lines 4–3107.
-- Its d37, d136, d9, Iter.iterM and Iter.d80 replace a0h, a6b, r8, a0a and a4l.
namespace Padding
open Turing PEqualNP.Library Lib.Machines Lib.Universal

private def pushedSymbols {K:Type} {Γ:K→ Type} {Λ σ:Type}:Turing.TM2.Stmt Γ Λ σ→ Set (Σ k,Γ k)
  | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,Γ k))∪ pushedSymbols q
  | .peek _ _ q=>pushedSymbols q
  | .pop _ _ q=>pushedSymbols q
  | .load _ q=>pushedSymbols q
  | .branch _ q₁ q₂=>pushedSymbols q₁∪ pushedSymbols q₂
  | .goto _=>∅
  | .halt=>∅
private lemma pushedSymbols_finite {K:Type} {Γ:K→ Type} {Λ σ:Type} [Finite σ]
    (q:Turing.TM2.Stmt Γ Λ σ):(pushedSymbols q).Finite:=by
  induction q with
  | push _ _ _ ih=>exact (Set.finite_range _).union ih
  | peek _ _ _ ih=>exact ih
  | pop _ _ _ ih=>exact ih
  | load _ _ ih=>exact ih
  | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
  | goto _=>exact Set.finite_empty
  | halt=>exact Set.finite_empty
private def restrictStmt {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T:∀ k,Set (Γ k)) :
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩:Σ j,Γ j)∈ pushedSymbols q→ s∈ T k) →
    Turing.TM2.Stmt (fun k=>{s:Γ k // s∈ T k}) Λ σ
  | .push k g q,h=>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
      (restrictStmt T q (fun j s hs=>h j s (Or.inr hs)))
  | .peek k f q,h=>.peek k (fun v o=>f v (o.map Subtype.val)) (restrictStmt T q h)
  | .pop k f q,h=>.pop k (fun v o=>f v (o.map Subtype.val)) (restrictStmt T q h)
  | .load a q,h=>.load a (restrictStmt T q h)
  | .branch f q₁ q₂,h=>.branch f
      (restrictStmt T q₁ (fun j s hs=>h j s (Or.inl hs)))
      (restrictStmt T q₂ (fun j s hs=>h j s (Or.inr hs)))
  | .goto f,_=>.goto f
  | .halt,_=>.halt
private def forgetCfg {K : Type} {Γ : K → Type} {Λ σ : Type} (T : ∀ k, Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s:Γ k // s∈ T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
  ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
private lemma forgetCfg_injective {K:Type} {Γ:K→ Type} {Λ σ:Type} (T:∀ k,Set (Γ k)) :
    Function.Injective (forgetCfg (Λ:=Λ) (σ:=σ) T):=by
  rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
  simp only [forgetCfg,Turing.TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl,rfl,hS⟩:=h
  congr 1
  funext k
  exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
private lemma map_subtype_update {K:Type} [DecidableEq K] {Γ:K→ Type} (T:∀ k,Set (Γ k))
    (S:∀ k,List {s:Γ k // s∈ T k}) (k:K) (l:List {s:Γ k // s∈ T k}) :
    (fun j=>(Function.update S k l j).map Subtype.val) =
      Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
  funext j
  by_cases h:j= k
  · subst h; simp
  · simp [h]
private lemma restrictStmt_stepAux {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
    (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
    (hq:∀ k s,(⟨k,s⟩:Σ j,Γ j)∈ pushedSymbols q→ s∈ T k)
    (v:σ) (S:∀ k,List {s:Γ k // s∈ T k}) :
    forgetCfg T (Turing.TM2.stepAux (restrictStmt T q hq) v S) =
      Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
  induction q generalizing v S with
  | push k g q ih =>
    simp only [restrictStmt,Turing.TM2.stepAux]
    rw [ih,map_subtype_update]
    rfl
  | peek k f q ih =>
    simp only [restrictStmt,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [List.head?_map])
  | pop k f q ih =>
    simp only [restrictStmt,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [map_subtype_update,List.head?_map,List.map_tail])
  | load a q ih =>
    simp only [restrictStmt,Turing.TM2.stepAux]
    exact ih hq (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [restrictStmt,Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ v S
    · exact ih₁ _ v S
  | goto f=>rfl
  | halt=>rfl
private lemma finiteAlphabetTransport (c:Turing.TM2ComputableAux Bool Bool) :
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
      (⟨k,s⟩:Σ j,c.tm.Γ j)∈ ⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)}
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
      m := fun l => restrictStmt T (c.tm.m l)
        (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
  have hFin:∀ j:tm'.K,Finite (tm'.Γ j):=by
    intro j
    by_cases h0:j= c.tm.k₀
    · subst h0; exact Finite.of_fintype _
    · by_cases h1 : j = c.tm.k₁
      · subst h1
        have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin:(⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l=>pushedSymbols_finite (c.tm.m l)
        have:Finite ↥(⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)):=hUfin.to_subtype
        refine Finite.of_injective (f:=fun x:tm'.Γ j =>
            (⟨⟨j,x.1⟩,by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩:↥(⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)))) ?_
        intro x y hxy
        have h1':=congrArg (fun z=>z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep:∀ cfg:tm'.Cfg,
      Option.map (forgetCfg T) (tm'.step cfg)= c.tm.step (forgetCfg T cfg):=by
    rintro ⟨l,v,S⟩
    cases l with
    | none=>rfl
    | some l =>
      change some (forgetCfg T (Turing.TM2.stepAux (restrictStmt T (c.tm.m l) _) v S)) =
        some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
      exact congrArg some (restrictStmt_stepAux T (c.tm.m l) _ v S)
  have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
      Option.map (forgetCfg T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (forgetCfg T cfg)):=by
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
  have hinit:forgetCfg T (Turing.initList tm' (x.map (e₀.trans c.inputAlphabet).invFun)) =
      Turing.initList c.tm (x.map c.inputAlphabet.invFun):=by
    simp only [forgetCfg,Turing.initList]
    congr 1; funext k
    by_cases hk:k= c.tm.k₀
    · subst hk
      dsimp only [tm']
      simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]
      rfl
    · dsimp only [tm']
      simp only [hk,↓reduceDIte,List.map_nil]
  have hhalt:forgetCfg T (Turing.haltList tm' (y.map (e₁.trans c.outputAlphabet).invFun)) =
      Turing.haltList c.tm (y.map c.outputAlphabet.invFun):=by
    simp only [forgetCfg,Turing.haltList]
    congr 1; funext k
    by_cases hk:k= c.tm.k₁
    · subst hk
      dsimp only [tm']
      simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]
      rfl
    · dsimp only [tm']
      simp only [hk,↓reduceDIte,List.map_nil]
  apply Option.map_injective (forgetCfg_injective T)
  rw [hiter,hinit,horig]
  exact (congrArg some hhalt).symm

private def mrW (parameter : List Bool → List Bool) (x : List Bool) : ℕ :=
  (parameter x).length

private def mrPad (parameter : List Bool → List Bool) (x : List Bool) : List Bool :=
  un (2 ^ (mrW parameter x + 1)) ++ false :: x

private def seedPair (parameter : List Bool → List Bool) (x : List Bool) :
    List Bool × List Bool :=
  (true :: false :: x, true :: parameter x)

private def doubleHeader (x : List Bool) : List Bool := hd x ++ x

private lemma hd_header (n : ℕ) (x : List Bool) :
    hd (un n ++ false :: x) = un n := by
  simp [hd, un]

private lemma dropN_header (n : ℕ) (x : List Bool) :
    dropN (un n ++ false :: x) = x := by
  have h : (un n ++ false :: x).dropWhile id = false :: x := by
    simp [un]
  simp [dropN, h]

private lemma doubleHeader_iter (x : List Bool) (j : ℕ) :
    doubleHeader^[j] (true :: false :: x) = un (2 ^ j) ++ false :: x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    show hd (un (2 ^ j) ++ false :: x) ++ (un (2 ^ j) ++ false :: x) = _
    rw [hd_header, ← List.append_assoc, pow_succ, mul_two]
    simp only [un, List.replicate_add]

private lemma doubleHeader_cpt : Lib.CPTs doubleHeader :=
  cpt_app2 cpt_hd cpt_id

private lemma seedPair_cpt {parameter : List Bool → List Bool} (hp : Lib.CPTs parameter) :
    ComputableInPolyTime (fun x : List Bool => x) encodePair (seedPair parameter) :=
  cpt_pair (cpt_app2 (cpt_const [true, false]) cpt_id)
    (cpt_app2 (cpt_const [true]) hp)

private lemma eval_power_bound_positive (p:Polynomial ℕ):∃ a d:ℕ,∀ m:ℕ,1≤ m→ p.eval m≤ a* m ^ d:=by
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

private lemma eval_power_bound (p:Polynomial ℕ):∃ A,1≤ A∧ ∀ m,p.eval m≤ A* (m+ 1) ^ A:=by
  obtain ⟨a,d,h⟩:=eval_power_bound_positive p
  refine ⟨a+ d+ 1,by omega,fun m=>?_⟩
  calc p.eval m ≤ p.eval (m + 1) := d37 p (by omega)
    _≤ a* (m+ 1) ^ d:=h (m+ 1) (by omega)
    _ ≤ (a + d + 1) * (m + 1) ^ (a + d + 1) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
private lemma combined_step_bound (A B P s1 tg s3 n2 n w L:ℕ) (hA:1≤ A) (hB:1≤ B) (hBP:B≤ P)
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
private lemma absorb_step_bound (A K n w:ℕ) (hK:A+ 1≤ K) :
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

lemma mr_fpt (parameter G : List Bool → List Bool)
    (hp : Lib.CPTs parameter) (hlen : ∀ x, (parameter x).length ≤ x.length)
    (hG : Lib.CPTs G) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : List Bool, Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ((G (List.replicate (2 ^ ((parameter x).length + 1)) true ++ false :: x)).map
          M.outputAlphabet.invFun))
        (2 ^ (c * ((parameter x).length + 1)) * (x.length + 2) ^ c)) := by
  classical
  obtain ⟨c1⟩:=seedPair_cpt hp
  obtain ⟨cg⟩:=doubleHeader_cpt
  obtain ⟨c3⟩:=hG
  obtain ⟨A1,hA1,hp1⟩:=eval_power_bound c1.time
  obtain ⟨Ag,hAg,hpg⟩:=eval_power_bound cg.time
  obtain ⟨A3,hA3,hp3⟩:=eval_power_bound c3.time
  let e₀:Bool→ cg.tm.Γ cg.tm.k₀:=cg.inputAlphabet.invFun
  let d₀:cg.tm.Γ cg.tm.k₀→ Bool:=cg.inputAlphabet
  let e₁:cg.tm.Γ cg.tm.k₁→ Bool:=cg.outputAlphabet
  let Mit:FinTM2:=Iter.iterM cg.tm e₀ d₀ e₁
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
        some (haltList cg.tm m)∧ m.map e₁= doubleHeader z:=by
    intro z
    refine ⟨(cg.outputsFun z).steps,List.map cg.outputAlphabet.invFun (doubleHeader z),
      (cg.outputsFun z).steps_le_m,(cg.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (doubleHeader z)]
    exact List.map_congr_left fun y _=>cg.outputAlphabet.right_inv y
  have key:∀ x:List Bool,∃ n,n≤ 2 ^ (2* K* (mrW parameter x+ 1))* (x.length+ 2) ^ (2* K) ∧
      (flip bind (TM2.step M1.m))^[n] (some (initList M1 (x.map c1.inputAlphabet.invFun))) =
        some (haltList M1 ((G (mrPad parameter x)).map c3.outputAlphabet.invFun)):=by
    intro x
    let n:=x.length
    let w:=mrW parameter x
    let L:=2 ^ (w+ 1)+ 1+ n
    have hw:w≤ n:=hlen x
    have hpadlen:(mrPad parameter x).length= L:=by
      simp only [mrPad,List.length_append,un_length,List.length_cons,L,n,w]; omega
    have r1:=c1.outputsFun x
    have hL:∀ j≤ (true::parameter x).length,
        (doubleHeader^[j] (true::false::x)).length≤ L:=by
      intro j hj
      rw [doubleHeader_iter]
      have hj':j≤ w+ 1:=hj
      have:2 ^ j≤ 2 ^ (w+ 1):=Nat.pow_le_pow_right (by norm_num) hj'
      simp only [List.length_append,un_length,List.length_cons,L,n]
      omega
    obtain ⟨n2,hn2,h2run⟩:=Iter.d80 e₀ d₀ e₁ doubleHeader cg.time
      (fun a=>cg.inputAlphabet.right_inv a) hrun (true::false::x) (true::parameter x)
      L hL
    have hiter:doubleHeader^[(true::parameter x).length] (true::false::x)= mrPad parameter x :=
      doubleHeader_iter x (w+ 1)
    rw [hiter] at h2run
    have r3:=c3.outputsFun (mrPad parameter x)
    obtain ⟨n23,hn23,-,h23⟩:=d136 φ2 d2 (fun h=>by simp [d2] at h)
      (encodePair (seedPair parameter x)) (mrPad parameter x) ((G (mrPad parameter x)).map c3.outputAlphabet.invFun)
      n2 r3.steps h2run r3.evals_in_steps
    have hφ1:((encodePair (seedPair parameter x)).map c1.outputAlphabet.invFun).map φ1 =
        encodePair (seedPair parameter x):=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (encodePair (seedPair parameter x))]
      exact List.map_congr_left fun y _=>c1.outputAlphabet.right_inv y
    rw [← hφ1] at h23
    obtain ⟨nt,hnt,-,ht⟩:=d136 φ1 d1 (fun h=>by simp [d1] at h)
      (x.map c1.inputAlphabet.invFun) ((encodePair (seedPair parameter x)).map c1.outputAlphabet.invFun)
      ((G (mrPad parameter x)).map c3.outputAlphabet.invFun) r1.steps n23 r1.evals_in_steps h23
    refine ⟨nt,?_,ht⟩
    have hlen1:((encodePair (seedPair parameter x)).map c1.outputAlphabet.invFun).length =
        (n+ 2)+ (w+ 1):=by
      simp only [List.length_map,seedPair,Lib.Machines.d9,List.length_cons,n,w,mrW]
    have hnt':nt≤ r1.steps+ (2* ((n+ 2)+ (w+ 1))+ 2)+ n23:=by omega
    have hn23':n23≤ n2+ (2* L+ 2)+ r3.steps:=by
      have e:List.length (α:=Mit.Γ Mit.k₁) (mrPad parameter x)= L:=hpadlen
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
    have b3':Polynomial.eval (mrPad parameter x).length c3.time≤ A* P:=by
      rw [hpadlen]; exact (hp3 L).trans (hpow A3 L (by omega) hBL)
    have b3:r3.steps≤ A* P:=r3.steps_le_m.trans b3'
    have hn2':n2≤ (w+ 1)* (cg.time.eval L+ 2* L+ 3)+ 2* L+ 2* (n+ 2) +
        (w+ 1)+ 5:=by
      have e:(true::parameter x).length= w+ 1:=rfl
      have e':(true::false::x).length= n+ 2:=rfl
      rw [e,e'] at hn2
      exact hn2
    have hA:1≤ A:=by omega
    have:=combined_step_bound A B P r1.steps (cg.time.eval L) r3.steps n2 n w L hA hB1 hBP b1 bg b3
      hBn hBw (by omega) hn2'
    have hBP':B* P= B ^ (A+ 1):=by simp only [P]; rw [pow_succ,mul_comm]
    have hfin:=absorb_step_bound A K n w (by omega)
    calc nt ≤ r1.steps + (2 * ((n + 2) + (w + 1)) + 2) + n23 := hnt'
      _≤ r1.steps+ (2* ((n+ 2)+ (w+ 1))+ 2)+ (n2+ (2* L+ 2)+ r3.steps):=by omega
      _≤ K* (B* P):=this
      _= K* (2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1):=by rw [hBP']
      _≤ _:=hfin
  let Mx:Turing.TM2ComputableAux Bool Bool:=⟨M1,c1.inputAlphabet,c3.outputAlphabet⟩
  obtain ⟨M',hfin,htrans⟩:=finiteAlphabetTransport Mx
  refine ⟨M',2* K,hfin,fun x=>htrans x (G (mrPad parameter x)) _ ?_⟩
  exact { steps := Classical.choose (key x)
          evals_in_steps:=(Classical.choose_spec (key x)).2
          steps_le_m:=(Classical.choose_spec (key x)).1 }

def secondUnary (x : List Bool) : List Bool := hd (dropN x)

lemma secondUnary_cpt : Lib.CPTs secondUnary := by
  unfold secondUnary
  exact cpt_comp cpt_dropN cpt_hd

lemma secondUnary_length (x : List Bool) : (secondUnary x).length ≤ x.length :=
  (hd_length (dropN x)).trans (dropN_length x)

lemma secondUnary_header (n k : ℕ) (payload : List Bool) :
    secondUnary ((List.replicate n true ++ [false]) ++
      (List.replicate k true ++ [false]) ++ payload) = List.replicate k true := by
  simp only [secondUnary, List.append_assoc, List.cons_append, List.nil_append]
  exact (congrArg hd (dropN_header n (un k ++ false :: payload))).trans (hd_header k payload)

lemma mr_fpt_second (G : List Bool → List Bool) (hG : Lib.CPTs G) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n k : ℕ) (payload : List Bool),
        let x := (List.replicate n true ++ [false]) ++
          (List.replicate k true ++ [false]) ++ payload
        Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
          (some ((G (List.replicate (2 ^ (k + 1)) true ++ false :: x)).map M.outputAlphabet.invFun))
          (2 ^ (c * (k + 1)) * (x.length + 2) ^ c)) := by
  obtain ⟨M, c, hfin, h⟩ := mr_fpt secondUnary G secondUnary_cpt secondUnary_length hG
  refine ⟨M, c, hfin, fun n k payload => ?_⟩
  simpa only [secondUnary_header, List.length_replicate] using
    h ((List.replicate n true ++ [false]) ++ (List.replicate k true ++ [false]) ++ payload)

end Padding

namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

-- Indexed loops are adapted from the indexed list loop in
-- e01c7200bf1eeecfb2739fd2504543e799a6d8e7:lean/PEqualNP/Outside/L_lib_1025.lean.
-- The shared arithmetic operations use the corresponding pinned L_meta_32050 helpers.

def left (s : List Bool) : List Bool := (unpairB s).1

def right (s : List Bool) : List Bool := (unpairB s).2

lemma cpLeft {f : List Bool → List Bool} (h : Lib.CPTs f) :
    Lib.CPTs (fun s => left (f s)) := cpt_comp h cpt_unpairB1

lemma cpRight {f : List Bool → List Bool} (h : Lib.CPTs f) :
    Lib.CPTs (fun s => right (f s)) := cpt_comp h cpt_unpairB2

lemma cpCons (b : Bool) {f : List Bool → List Bool} (h : Lib.CPTs f) :
    Lib.CPTs (fun s => b :: f s) := cpt_app2 (cpt_const [b]) h

lemma cpTail {f : List Bool → List Bool} (h : Lib.CPTs f) :
    Lib.CPTs (fun s => (f s).tail) := cpt_comp h cpt_tail

lemma cpTake {f g : List Bool → List Bool} (h : Lib.CPTs f) (hg : Lib.CPTs g) :
    Lib.CPTs (fun s => (g s).take (f s).length) :=
  q39 (q24 h hg) (fun s => q12 (f s) (g s))

lemma cpDrop {f g : List Bool → List Bool} (h : Lib.CPTs f) (hg : Lib.CPTs g) :
    Lib.CPTs (fun s => (g s).drop (f s).length) :=
  q39 (cpt_dropN' h hg) (fun s => q40 (f s) (g s))

def indexed (join : List Bool → List Bool → List Bool → List Bool)
    (f : List Bool → List Bool) (y : List Bool) : List Bool :=
  let cap := left y
  let count := (left (right y)).tail
  let args := left (right (right y))
  let acc := right (right (right y))
  pairB cap (pairB count (pairB args (join cap (f (pairB count (pairB args acc))) acc)))

lemma cpIndexed {join : List Bool → List Bool → List Bool → List Bool}
    (hjoin : ∀ {u v w : List Bool → List Bool}, Lib.CPTs u → Lib.CPTs v → Lib.CPTs w →
      Lib.CPTs (fun s => join (u s) (v s) (w s))) {f : List Bool → List Bool} (hf : Lib.CPTs f) :
    Lib.CPTs (indexed join f) := by
  have hcap := cpLeft cpt_id
  have hcount := cpTail (cpLeft (cpRight cpt_id))
  have hargs := cpLeft (cpRight (cpRight cpt_id))
  have hacc := cpRight (cpRight (cpRight cpt_id))
  exact cpt_pairB2 hcap (cpt_pairB2 hcount (cpt_pairB2 hargs
    (hjoin hcap (cpt_comp (cpt_pairB2 hcount (cpt_pairB2 hargs hacc)) hf) hacc)))

lemma indexed_length {join : List Bool → List Bool → List Bool → List Bool}
    (hjoin : ∀ cap val acc, (join cap val acc).length ≤ cap.length + acc.length)
    (f : List Bool → List Bool) (y : List Bool) :
    (indexed join f y).length ≤ y.length + 3 * (left y).length + 3 := by
  have h1 := unpairB_length y
  have h2 := unpairB_length (right y)
  have h3 := unpairB_length (right (right y))
  have h4 := hjoin (left y)
    (f (pairB (left (right y)).tail (pairB (left (right (right y))) (right (right (right y))))))
    (right (right (right y)))
  have h5 : (left (right y)).tail.length ≤ (left (right y)).length := by simp
  change 2 * (left y).length + (right y).length ≤ y.length at h1
  change 2 * (left (right y)).length + (right (right y)).length ≤ (right y).length at h2
  change 2 * (left (right (right y))).length + (right (right (right y))).length ≤
    (right (right y)).length at h3
  simp only [indexed, pairB_length]
  omega

def runIndexed (join : List Bool → List Bool → List Bool → List Bool)
    (f : List Bool → List Bool) (cap count args acc : List Bool) : List Bool :=
  right (right (right ((indexed join f)^[count.length]
    (pairB cap (pairB (un count.length) (pairB args acc))))))

lemma cpRunIndexed {join : List Bool → List Bool → List Bool → List Bool}
    (hjoin : ∀ {u v w : List Bool → List Bool}, Lib.CPTs u → Lib.CPTs v → Lib.CPTs w →
      Lib.CPTs (fun s => join (u s) (v s) (w s)))
    (hlen : ∀ cap val acc, (join cap val acc).length ≤ cap.length + acc.length)
    {f cap count args acc : List Bool → List Bool}
    (hf : Lib.CPTs f) (hcap : Lib.CPTs cap) (hcount : Lib.CPTs count)
    (hargs : Lib.CPTs args) (hacc : Lib.CPTs acc) :
    Lib.CPTs (fun s => runIndexed join f (cap s) (count s) (args s) (acc s)) := by
  have hinit := cpt_pairB2 hcap (cpt_pairB2 (cpt_comp hcount q89) (cpt_pairB2 hargs hacc))
  have hrun := q18 3 (cpIndexed hjoin hf)
    (fun y => by simp only [indexed, unpairB_pairB, left])
    (indexed_length hlen f) hcount hinit
  exact cpRight (cpRight (cpRight hrun))

lemma indexed_iter (join : List Bool → List Bool → List Bool → List Bool)
    (f : List Bool → List Bool) (cap args : List Bool) (n : ℕ) (acc : List Bool) :
    (indexed join f)^[n] (pairB cap (pairB (un n) (pairB args acc))) =
      pairB cap (pairB [] (pairB args ((List.range n).foldr
        (fun i x => join cap (f (pairB (un i) (pairB args x))) x) acc))) := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, List.range_succ, List.foldr_append]
    simp only [indexed, left, right, unpairB_pairB, un_succ, List.tail_cons, List.foldr_cons, List.foldr_nil]
    exact ih _

lemma runIndexed_eq (join : List Bool → List Bool → List Bool → List Bool)
    (f : List Bool → List Bool) (cap count args acc : List Bool) :
    runIndexed join f cap count args acc = (List.range count.length).foldr
      (fun i x => join cap (f (pairB (un i) (pairB args x))) x) acc := by
  simp only [runIndexed, indexed_iter, right, unpairB_pairB]

def appendBound (cap val acc : List Bool) : List Bool := val.take cap.length ++ acc

def replaceBound (cap val _ : List Bool) : List Bool := val.take cap.length

lemma appendBound_cpt {u v w : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v)
    (hw : Lib.CPTs w) : Lib.CPTs (fun s => appendBound (u s) (v s) (w s)) :=
  cpt_app2 (cpTake hu hv) hw

lemma replaceBound_cpt {u v w : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v)
    (_ : Lib.CPTs w) : Lib.CPTs (fun s => replaceBound (u s) (v s) (w s)) := cpTake hu hv

lemma appendBound_length (cap val acc : List Bool) :
    (appendBound cap val acc).length ≤ cap.length + acc.length := by simp [appendBound]

lemma replaceBound_length (cap val acc : List Bool) :
    (replaceBound cap val acc).length ≤ cap.length + acc.length := by simp [replaceBound]

def mapRange (f : List Bool → List Bool) (cap count args : List Bool) : List Bool :=
  runIndexed appendBound (fun s => f (pairB (left s) (left (right s)))) cap count args []

lemma cpMapRange {f cap count args : List Bool → List Bool} (hf : Lib.CPTs f)
    (hcap : Lib.CPTs cap) (hc : Lib.CPTs count) (ha : Lib.CPTs args) :
    Lib.CPTs (fun s => mapRange f (cap s) (count s) (args s)) :=
  cpRunIndexed appendBound_cpt appendBound_length
    (cpt_comp (cpt_pairB2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id))) hf) hcap hc ha (cpt_const [])

lemma mapRange_eq (f : List Bool → List Bool) (cap count args : List Bool)
    (h : ∀ i < count.length, (f (pairB (un i) args)).length ≤ cap.length) :
    mapRange f cap count args = (List.range count.length).flatMap (fun i => f (pairB (un i) args)) := by
  simp only [mapRange, runIndexed_eq, left, right, unpairB_pairB, appendBound]
  have hg (L : List ℕ) (hL : ∀ i ∈ L, i < count.length) :
      L.foldr (fun i x => (f (pairB (un i) args)).take cap.length ++ x) [] =
        L.flatMap (fun i => f (pairB (un i) args)) := by
    induction L with
    | nil => rfl
    | cons i L ih =>
      simp [List.take_of_length_le (h i (hL i (by simp))), ih (fun j hj => hL j (by simp [hj]))]
  exact hg _ (fun i hi => List.mem_range.mp hi)

end Packed


namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

def slot (word idx stream : List Bool) : List Bool :=
  (stream.drop (word.length * idx.length)).take word.length

lemma cpSlot {w i s : List Bool → List Bool} (hw : Lib.CPTs w) (hi : Lib.CPTs i) (hs : Lib.CPTs s) :
    Lib.CPTs (fun x => slot (w x) (i x) (s x)) :=
  q39 (cpTake hw (cpDrop (q42 hw hi) hs)) (fun x => by simp [slot, mulU])

lemma slot_flatMap {α : Type*} (L : List α) (f : α → List Bool) (w : List Bool) (i : ℕ)
    (hi : i < L.length) (hw : ∀ a ∈ L, (f a).length = w.length) :
    slot w (un i) (L.flatMap f) = f L[i] := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    have ha := hw a (by simp)
    have hL : ∀ b ∈ L, (f b).length = w.length := fun b hb => hw b (by simp [hb])
    cases i with
    | zero =>
      simp only [slot, un_length, Nat.mul_zero, List.drop_zero, List.flatMap_cons,
        List.getElem_cons_zero]
      rw [← ha, List.take_left]
    | succ i =>
      simp only [slot, un_length, List.flatMap_cons, List.getElem_cons_succ]
      rw [Nat.mul_succ, Nat.add_comm, ← ha, List.drop_length_add_append, ha]
      simpa only [slot, un_length] using ih i (by simp at hi; omega) hL

def doubleStep (s : List Bool) : List Bool :=
  (right (right s)) ++ (right (right s))

def powerTwo (cap exp : List Bool) : List Bool :=
  runIndexed replaceBound doubleStep cap exp [] (un 1)

lemma powerTwo_cpt {u v : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v) :
    Lib.CPTs (fun s => powerTwo (u s) (v s)) := by
  have h := cpRight (cpRight cpt_id)
  exact cpRunIndexed replaceBound_cpt replaceBound_length (cpt_app2 h h) hu hv
    (cpt_const []) (cpt_const [true])

lemma runIndexed_ofListFold (join : List Bool → List Bool → List Bool → List Bool)
    (f : List Bool → List Bool) (cap count args acc : List Bool) {α : Type*}
    (spec : List Bool → α → Prop) (step : ℕ → α → α) (initial : α)
    (hinit : spec acc initial)
    (hstep : ∀ i < count.length, ∀ x a, spec x a →
      spec (join cap (f (pairB (un i) (pairB args x))) x) (step i a)) :
    spec (runIndexed join f cap count args acc) ((List.range count.length).foldr step initial) := by
  rw [runIndexed_eq]
  generalize hL : List.range count.length = L
  have hs : ∀ i ∈ L, i < count.length := by simp [← hL]
  clear hL
  induction L with
  | nil => exact hinit
  | cons i L ih =>
    simp only [List.foldr_cons]
    exact hstep i (hs i (by simp)) _ _ (ih (fun j hj => hs j (by simp [hj])))

lemma powerTwo_eq (cap exp : List Bool) (h : 2 ^ exp.length ≤ cap.length) :
    powerTwo cap exp = un (2 ^ exp.length) := by
  rw [powerTwo, runIndexed_eq]
  generalize hv : List.range exp.length = L
  have hlen : L.length = exp.length := by simp [← hv]
  have hL : L.length ≤ exp.length := hlen.le
  have goal : L.foldr (fun i x => replaceBound cap (doubleStep (pairB (un i) (pairB [] x))) x)
      (un 1) = un (2 ^ L.length) := by
    clear hv hlen
    induction L with
    | nil => rfl
    | cons i L ih =>
      have ht : L.length ≤ exp.length := by simp at hL; omega
      rw [List.foldr_cons, ih ht]
      simp only [doubleStep, right, unpairB_pairB, replaceBound, List.length_cons]
      have he : un (2 ^ L.length) ++ un (2 ^ L.length) = un (2 ^ (L.length+1)) := by
        simp only [un, pow_succ, Nat.mul_two, List.replicate_add]
      rw [he, List.take_of_length_le]
      simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hL).trans h
  exact goal.trans (congrArg (fun l : ℕ => un (2^l)) hlen)

def joinAdd (w v a : List Bool) : List Bool := addW w v a

lemma cpJoinAdd {u v w : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v)
    (hw : Lib.CPTs w) : Lib.CPTs (fun s => joinAdd (u s) (v s) (w s)) := q82 hu hv hw

lemma joinAdd_length (w v a : List Bool) : (joinAdd w v a).length ≤ w.length + a.length := by
  rw [joinAdd, q36]; omega

def sumRange (f : List Bool → List Bool) (w count args : List Bool) : List Bool :=
  runIndexed joinAdd (fun s => f (pairB (left s) (left (right s)))) w count args (blank w)

lemma cpSumRange {f w c a : List Bool → List Bool} (hf : Lib.CPTs f) (hw : Lib.CPTs w)
    (hc : Lib.CPTs c) (ha : Lib.CPTs a) : Lib.CPTs (fun s => sumRange f (w s) (c s) (a s)) :=
  cpRunIndexed cpJoinAdd joinAdd_length
    (cpt_comp (cpt_pairB2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id))) hf) hw hc ha (cpt_comp hw cpt_blank)

lemma sumRange_length (f : List Bool → List Bool) (w count args : List Bool) :
    (sumRange f w count args).length = w.length := by
  simp only [sumRange, runIndexed_eq]
  cases List.range count.length with
  | nil => exact q33 w
  | cons i L => exact q36 _ _ _

def rep (w b : List Bool) (z : ℤ) : Prop := (val b : ℤ) ≡ z [ZMOD (2:ℤ)^w.length]

lemma rep_zero (w : List Bool) : rep w (blank w) 0 := by simp [rep, q37]

lemma rep_nat (w u : List Bool) : rep w (natW w u) (u.length : ℤ) := by
  rw [rep, q114]
  exact_mod_cast (Nat.mod_modEq u.length (2 ^ w.length))

lemma rep_add {w a b : List Bool} {x y : ℤ} (hx : rep w a x) (hy : rep w b y) :
    rep w (addW w a b) (x + y) := (q98 w a b).trans (hx.add hy)

lemma rep_mul {w a b : List Bool} {x y : ℤ} (hx : rep w a x) (hy : rep w b y) :
    rep w (mulW w a b) (x * y) := (q55 w a b).trans (hx.mul hy)

lemma rep_neg {w a : List Bool} {x : ℤ} (hx : rep w a x) :
    rep w (negW w a) (-x) := (q113 w a).trans hx.neg

lemma rep_pow {w a : List Bool} {x : ℤ} (hx : rep w a x) (e : List Bool) :
    rep w (powW w a e) (x ^ e.length) := by
  have h : (val (powW w a e) : ℤ) ≡ (val a : ℤ)^e.length [ZMOD (2:ℤ)^w.length] := by
    rw [(q178 w a e).2]
    exact_mod_cast (Nat.mod_modEq ((val a)^e.length) (2 ^ w.length))
  exact h.trans (hx.pow _)

lemma sumRange_rep (f : List Bool → List Bool) (w count args : List Bool) (z : ℕ → ℤ)
    (h : ∀ i < count.length, rep w (f (pairB (un i) args)) (z i)) :
    rep w (sumRange f w count args) ((List.range count.length).map z).sum := by
  simp only [sumRange, runIndexed_eq, left, right, unpairB_pairB, joinAdd]
  generalize hr : List.range count.length = L
  have hL : ∀ i ∈ L, i < count.length := by simp [← hr]
  clear hr
  induction L with
  | nil => exact rep_zero w
  | cons i L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact rep_add (h i (hL i (by simp))) (ih (fun j hj => hL j (by simp [hj])))

lemma val_eq_of_rep {w b : List Bool} {z : ℕ} (hlen : b.length = w.length)
    (hb : rep w b (z : ℤ)) (hz : z < 2 ^ w.length) : val b = z := by
  have hx : val b < 2 ^ w.length := hlen ▸ q124 b
  have hx' : (val b : ℤ) < (2:ℤ)^w.length := by exact_mod_cast hx
  have hz' : (z : ℤ) < (2:ℤ)^w.length := by exact_mod_cast hz
  unfold rep Int.ModEq at hb
  rw [Int.emod_eq_of_lt (by positivity) hx', Int.emod_eq_of_lt (by positivity) hz'] at hb
  exact_mod_cast hb

def bitFlagAt (i x : List Bool) : List Bool := q17 (x.drop i.length)

lemma cpBitFlagAt {i x : List Bool → List Bool} (hi : Lib.CPTs i) (hx : Lib.CPTs x) :
    Lib.CPTs (fun s => bitFlagAt (i s) (x s)) := cpt_comp (cpDrop hi hx) q35

lemma bitFlagAt_eq (i x : List Bool) : bitFlagAt i x = bflag (x.getD i.length false) := by
  unfold bitFlagAt
  generalize i.length = j
  induction j generalizing x with
  | zero => cases x with | nil => rfl | cons b l => cases b <;> rfl
  | succ j ih => cases x with | nil => rfl | cons b l => exact ih l

end Packed

section MatchingExterior

open scoped BigOperators Matrix

abbrev extTable (d : ℕ) := Finset (Fin d) → Finset (Fin d) → ℤ

def extVector {n d : ℕ} (x : Fin n) (i : Fin d) : ℤ := (x.val : ℤ) ^ i.val

def extAppendLeft {d : ℕ} (v : Fin d → ℤ) (D : extTable d) : extTable d :=
  fun S T => ∑ i ∈ S, (-1 : ℤ) ^ (S.filter (fun j => i < j)).card * v i * D (S.erase i) T

def extAppendRight {d : ℕ} (v : Fin d → ℤ) (D : extTable d) : extTable d :=
  fun S T => ∑ i ∈ T, (-1 : ℤ) ^ (T.filter (fun j => i < j)).card * v i * D S (T.erase i)

def extInit (d : ℕ) : extTable d := fun S T => if S = ∅ ∧ T = ∅ then 1 else 0

def extTake {n d : ℕ} (e : Fin n × Fin n) (D : extTable d) : extTable d :=
  extAppendRight (extVector e.2) (extAppendRight (extVector e.1)
    (extAppendLeft (extVector e.2) (extAppendLeft (extVector e.1) D)))

def extStep {n d : ℕ} (e : Fin n × Fin n) (D : extTable d) : extTable d := D + extTake e D

def extRun {n : ℕ} (d : ℕ) (edges : List (Fin n × Fin n)) : extTable d :=
  edges.foldr extStep (extInit d)

def extEdgeEnds {n : ℕ} (e : Fin n × Fin n) : Finset (Fin n) := {e.1, e.2}

def extMatching {n : ℕ} (Q : Finset (Fin n × Fin n)) : Prop :=
  ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (extEdgeEnds e) (extEdgeEnds f)

def extWeight {n : ℕ} (V : Finset (Fin n)) : ℕ :=
  ∏ i ∈ V, ∏ j ∈ V.filter (fun j => i < j), (j.val - i.val) ^ 2

private theorem extGreater_map {n r : ℕ} (S : Finset (Fin n)) (h : S.card = r) (i : Fin r) :
    (Finset.Ioi i).map (S.orderEmbOfFin h).toEmbedding =
      S.filter (fun j => S.orderEmbOfFin h i < j) := by
  let f := S.orderEmbOfFin h
  calc
    _ = (Finset.univ.map f.toEmbedding).filter (fun j => f i < j) := by
      rw [Finset.filter_map]
      congr 1
      ext j
      simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp_apply]
      exact f.strictMono.lt_iff_lt.symm
    _ = _ := by rw [show Finset.univ.map f.toEmbedding = S from
      Finset.map_orderEmbOfFin_univ S h]

private theorem extErase_orderEmb {d r : ℕ} (S : Finset (Fin d)) (h : S.card = r + 1)
    (i : Fin (r + 1)) (h' : (S.erase (S.orderEmbOfFin h i)).card = r) :
    (fun j => S.orderEmbOfFin h (i.succAbove j)) =
      ⇑((S.erase (S.orderEmbOfFin h i)).orderEmbOfFin h') := by
  apply Finset.orderEmbOfFin_unique h'
  · intro j
    exact Finset.mem_erase.mpr ⟨fun hj => Fin.succAbove_ne i j
      ((S.orderEmbOfFin h).injective hj), S.orderEmbOfFin_mem h _⟩
  · exact (S.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i)

private noncomputable def extMinorTuple {n d r : ℕ} (S : Finset (Fin d))
    (xs : Fin r → Fin n) : ℤ :=
  if h : S.card = r then
    (Matrix.of (fun i j : Fin r => extVector (xs j) (S.orderEmbOfFin h i))).det
  else 0

private noncomputable def extMinor {n d : ℕ} (S : Finset (Fin d)) (xs : List (Fin n)) : ℤ :=
  extMinorTuple S xs.get

private theorem extMinorTuple_snoc {n d r : ℕ} (S : Finset (Fin d))
    (xs : Fin r → Fin n) (x : Fin n) :
    extMinorTuple S (Fin.snoc xs x : Fin (r + 1) → Fin n) =
      ∑ a ∈ S, (-1 : ℤ) ^ (S.filter (fun j => a < j)).card * extVector x a *
        extMinorTuple (S.erase a) xs := by
  by_cases h : S.card = r + 1
  · let f := (S.orderEmbOfFin h).toEmbedding
    let term (a : Fin d) := (-1 : ℤ) ^ (S.filter (fun j => a < j)).card * extVector x a *
      extMinorTuple (S.erase a) xs
    let M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
      Matrix.of (fun i j => extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) j) (f i))
    change (if h' : S.card = r + 1 then
      (Matrix.of (fun i j : Fin (r + 1) => extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) j)
        (S.orderEmbOfFin h' i))).det else 0) = S.sum term
    rw [dif_pos h]
    change M.det = S.sum term
    calc
      M.det = ∑ i : Fin (r + 1), term (f i) := by
        rw [Matrix.det_succ_column M (Fin.last r)]
        apply Finset.sum_congr rfl
        intro i _
        have hi : f i ∈ S := S.orderEmbOfFin_mem h i
        have herase : (S.erase (f i)).card = r := by
          rw [Finset.card_erase_of_mem hi, h, Nat.add_sub_cancel]
        have hrank : (S.filter (fun j => f i < j)).card = r - i.val := by
          change (S.filter (fun j => S.orderEmbOfFin h i < j)).card = _
          simp only [← extGreater_map S h i, Finset.card_map, Fin.card_Ioi, Nat.succ_sub_one]
        have hpow : (-1 : ℤ) ^ (i.val + r) = (-1 : ℤ) ^ (r - i.val) := by
          have hi' := i.isLt
          rw [show i.val + r = (r - i.val) + 2 * i.val by omega, pow_add, pow_mul]
          norm_num
        have hsub : M.submatrix i.succAbove (Fin.last r).succAbove =
            Matrix.of (fun p q : Fin r =>
              extVector (xs q) ((S.erase (f i)).orderEmbOfFin herase p)) := by
          ext p q
          change extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) ((Fin.last r).succAbove q))
            (f (i.succAbove p)) = _
          rw [Fin.succAbove_last, Fin.snoc_castSucc]
          exact congrArg (extVector (xs q)) (congrFun (extErase_orderEmb S h i herase) p)
        change (-1 : ℤ) ^ (i.val + r) *
          extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) (Fin.last r)) (f i) *
          (M.submatrix i.succAbove (Fin.last r).succAbove).det = term (f i)
        rw [hpow, Fin.snoc_last, hsub]
        simp only [term, hrank, extMinorTuple, dif_pos herase]
      _ = (Finset.univ.map f).sum term := (Finset.sum_map _ _ _).symm
      _ = S.sum term :=
        congrArg (fun R : Finset (Fin d) => R.sum term) (Finset.map_orderEmbOfFin_univ S h)
  · rw [extMinorTuple, dif_neg h]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have h' : (S.erase a).card ≠ r := by
      intro heq
      exact h ((Finset.card_erase_add_one ha).symm.trans (congrArg (· + 1) heq))
    simp only [extMinorTuple, dif_neg h', mul_zero]

private theorem extMinorTuple_cast {n d r s : ℕ} (S : Finset (Fin d)) (h : r = s)
    (xs : Fin s → Fin n) : extMinorTuple S (fun i => xs (Fin.cast h i)) = extMinorTuple S xs := by
  subst s
  rfl

private theorem extMinor_concat {n d : ℕ} (S : Finset (Fin d)) (xs : List (Fin n)) (x : Fin n) :
    extMinor S (xs.concat x) =
      ∑ a ∈ S, (-1 : ℤ) ^ (S.filter (fun j => a < j)).card * extVector x a *
        extMinor (S.erase a) xs := by
  have hlen : xs.length + 1 = (xs.concat x).length := List.length_concat.symm
  have hget : (fun i => (xs.concat x).get (Fin.cast hlen i)) =
      (Fin.snoc xs.get x : Fin (xs.length + 1) → Fin n) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, List.get_eq_getElem, Fin.val_cast, Fin.val_last,
        List.concat_eq_append] using
        (List.getElem_concat_length (l := xs) (a := x) rfl (by simp))
    · simpa only [Fin.snoc_castSucc, List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc,
        List.concat_eq_append] using
        (List.getElem_append_left (as := xs) (bs := [x]) j.isLt
          (h' := by simpa using Nat.lt_succ_of_lt j.isLt))
  change extMinorTuple S (xs.concat x).get = _
  rw [← extMinorTuple_cast S hlen (xs.concat x).get, hget, extMinorTuple_snoc] <;> rfl

private noncomputable def extOuter {n : ℕ} (d : ℕ) (xs ys : List (Fin n)) : extTable d :=
  fun S T => extMinor S xs * extMinor T ys

private theorem extAppendLeft_outer {n d : ℕ} (xs ys : List (Fin n)) (x : Fin n) :
    extAppendLeft (extVector x) (extOuter d xs ys) = extOuter d (xs.concat x) ys := by
  funext S T
  simp only [extAppendLeft, extOuter, extMinor_concat, Finset.sum_mul, mul_assoc]

private theorem extAppendRight_outer {n d : ℕ} (xs ys : List (Fin n)) (x : Fin n) :
    extAppendRight (extVector x) (extOuter d xs ys) = extOuter d xs (ys.concat x) := by
  funext S T
  simp only [extAppendRight, extOuter, extMinor_concat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem extAppendLeft_sum {d : ℕ} {α : Type*} (P : Finset α) (v : Fin d → ℤ)
    (F : α → extTable d) : extAppendLeft v (P.sum F) = P.sum (fun a => extAppendLeft v (F a)) := by
  funext S T
  simp only [extAppendLeft, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem extAppendRight_sum {d : ℕ} {α : Type*} (P : Finset α) (v : Fin d → ℤ)
    (F : α → extTable d) : extAppendRight v (P.sum F) = P.sum (fun a => extAppendRight v (F a)) := by
  funext S T
  simp only [extAppendRight, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem extTake_sum {n d : ℕ} {α : Type*} (P : Finset α) (e : Fin n × Fin n)
    (F : α → extTable d) : extTake e (P.sum F) = P.sum (fun a => extTake e (F a)) := by
  simp only [extTake, extAppendLeft_sum, extAppendRight_sum]

private def extEndpoints {n : ℕ} : List (Fin n × Fin n) → Finset (Fin n × Fin n) → List (Fin n)
  | [], _ => []
  | e :: es, Q =>
    if e ∈ Q then ((extEndpoints es Q).concat e.1).concat e.2 else extEndpoints es Q

private theorem extEndpoints_congr {n : ℕ} (es : List (Fin n × Fin n)) {Q R : Finset (Fin n × Fin n)}
    (h : ∀ e ∈ es, e ∈ Q ↔ e ∈ R) : extEndpoints es Q = extEndpoints es R := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    simp only [extEndpoints, he, ht]

private theorem extRun_eq_sum {n : ℕ} (d : ℕ) (es : List (Fin n × Fin n)) (hn : es.Nodup) :
    extRun d es = ∑ Q ∈ es.toFinset.powerset, extOuter d (extEndpoints es Q) (extEndpoints es Q) := by
  induction es with
  | nil =>
    funext S T
    simp only [extRun, List.foldr_nil, List.toFinset_nil, Finset.powerset_empty, Finset.sum_singleton,
      extEndpoints, extOuter, extInit, extMinor, List.length_nil, extMinorTuple]
    by_cases hS : S = ∅ <;> by_cases hT : T = ∅ <;>
      simp [hS, hT, Finset.card_eq_zero]
  | cons e es ih =>
    have ⟨he', hn'⟩ := List.nodup_cons.mp hn
    have he : e ∉ es.toFinset := by simpa using he'
    have hnQ : ∀ {Q}, Q ∈ es.toFinset.powerset → e ∉ Q :=
      fun hQ h => he (Finset.mem_powerset.mp hQ h)
    have hdis : Disjoint es.toFinset.powerset (es.toFinset.powerset.image (insert e)) := by
      refine Finset.disjoint_left.mpr (fun Q hQ hI => ?_)
      obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hI
      exact hnQ hQ (Finset.mem_insert_self _ _)
    have hins : Set.InjOn (insert e) (↑es.toFinset.powerset : Set (Finset (Fin n × Fin n))) := by
      intro Q hQ R hR h
      have hQ' := hnQ hQ
      have hR' := hnQ hR
      simpa only [Finset.erase_insert hQ', Finset.erase_insert hR'] using
        congrArg (fun S : Finset (Fin n × Fin n) => S.erase e) h
    have htail : ∀ Q, extEndpoints es (insert e Q) = extEndpoints es Q := by
      intro Q
      exact extEndpoints_congr es (fun f hf => by
        have hfe : f ≠ e := fun h => he' (h ▸ hf)
        simp [Finset.mem_insert, hfe])
    change extStep e (extRun d es) = _
    rw [extStep, ih hn', extTake_sum, List.toFinset_cons, Finset.powerset_insert,
      Finset.sum_union hdis, Finset.sum_image hins]
    congr 1
    · apply Finset.sum_congr rfl
      intro Q hQ
      simp only [extEndpoints, if_neg (hnQ hQ)]
    · apply Finset.sum_congr rfl
      intro Q _
      simp only [extTake, extAppendLeft_outer, extAppendRight_outer, extEndpoints,
        Finset.mem_insert_self, if_true, htail]

private def extSelected {n : ℕ} (es : List (Fin n × Fin n)) (Q : Finset (Fin n × Fin n)) :=
  (es.filter (fun e => decide (e ∈ Q))).reverse

private def extEdgeList {n : ℕ} (e : Fin n × Fin n) : List (Fin n) := [e.1, e.2]

private theorem extEndpoints_flatMap {n : ℕ} (es : List (Fin n × Fin n))
    (Q : Finset (Fin n × Fin n)) : extEndpoints es Q = (extSelected es Q).flatMap extEdgeList := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e ∈ Q <;>
      simp [extEndpoints, extSelected, ih, h, extEdgeList, List.reverse_cons, List.flatMap_append,
        List.append_assoc]

private theorem extSelected_mem {n : ℕ} {es : List (Fin n × Fin n)} {Q : Finset (Fin n × Fin n)}
    (hQ : Q ⊆ es.toFinset) (e : Fin n × Fin n) : e ∈ extSelected es Q ↔ e ∈ Q := by
  simp only [extSelected, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun he => ⟨List.mem_toFinset.mp (hQ he), he⟩⟩

private theorem extSelected_nodup {n : ℕ} {es : List (Fin n × Fin n)} (hn : es.Nodup)
    (Q : Finset (Fin n × Fin n)) : (extSelected es Q).Nodup :=
  List.nodup_reverse.mpr (hn.filter _)

private theorem extEndpoints_length {n : ℕ} {es : List (Fin n × Fin n)} (hn : es.Nodup)
    {Q : Finset (Fin n × Fin n)} (hQ : Q ⊆ es.toFinset) :
    (extEndpoints es Q).length = 2 * Q.card := by
  have hcard : (extSelected es Q).toFinset = Q := Finset.ext (fun e =>
    List.mem_toFinset.trans (extSelected_mem hQ e))
  calc
    (extEndpoints es Q).length = 2 * (extSelected es Q).length := by
      rw [extEndpoints_flatMap]
      generalize extSelected es Q = L
      induction L with
      | nil => simp
      | cons e L ih => simp [extEdgeList, ih, Nat.mul_succ, Nat.add_comm] <;> omega
    _ = 2 * Q.card := by
      rw [← List.toFinset_card_of_nodup (extSelected_nodup hn Q), hcard]

private theorem extEndpoints_toFinset {n : ℕ} {es : List (Fin n × Fin n)}
    {Q : Finset (Fin n × Fin n)} (hQ : Q ⊆ es.toFinset) :
    (extEndpoints es Q).toFinset = Q.biUnion extEdgeEnds := by
  rw [extEndpoints_flatMap]
  ext x
  simp [List.mem_flatMap, Finset.mem_biUnion, extSelected_mem hQ, extEdgeList, extEdgeEnds]

private theorem extEdgeList_disjoint {n : ℕ} (e f : Fin n × Fin n) :
    List.Disjoint (extEdgeList e) (extEdgeList f) ↔ Disjoint (extEdgeEnds e) (extEdgeEnds f) := by
  simp [List.disjoint_left, Finset.disjoint_left, extEdgeEnds, extEdgeList]

private theorem extEndpoints_nodup {n : ℕ} {es : List (Fin n × Fin n)} (hn : es.Nodup)
    {Q : Finset (Fin n × Fin n)} (hQ : Q ⊆ es.toFinset) (ho : ∀ e ∈ Q, e.1 < e.2) :
    (extEndpoints es Q).Nodup ↔ extMatching Q := by
  rw [extEndpoints_flatMap, List.nodup_flatMap]
  have hwithin : ∀ e ∈ extSelected es Q, (extEdgeList e).Nodup := by
    intro e he
    have hne := ne_of_lt (ho e ((extSelected_mem hQ e).mp he))
    simp [extEdgeList, hne]
  rw [and_iff_right hwithin]
  constructor
  · intro hp e he f hf hne
    let R := fun e f : Fin n × Fin n => Disjoint (extEdgeEnds e) (extEdgeEnds f)
    haveI : Std.Symm R := ⟨fun _ _ h => h.symm⟩
    have hp' : (extSelected es Q).Pairwise R := hp.imp (fun {e f} h =>
      (extEdgeList_disjoint e f).mp h)
    exact hp'.forall ((extSelected_mem hQ e).mpr he) ((extSelected_mem hQ f).mpr hf) hne
  · intro hp
    apply (extSelected_nodup hn Q).pairwise_of_forall_ne
    intro e he f hf hne
    exact (extEdgeList_disjoint e f).mpr
      (hp e ((extSelected_mem hQ e).mp he) f ((extSelected_mem hQ f).mp hf) hne)

private theorem extMinor_univ {n d : ℕ} (xs : List (Fin n)) :
    extMinor (Finset.univ : Finset (Fin d)) xs =
      if d = xs.length then (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ))).det else 0 := by
  by_cases h : d = xs.length
  · subst d
    have hu : (Finset.univ : Finset (Fin xs.length)).card = xs.length := by simp
    have hid : (fun i : Fin xs.length => i) =
        ⇑((Finset.univ : Finset (Fin xs.length)).orderEmbOfFin hu) :=
      Finset.orderEmbOfFin_unique hu (fun _ => Finset.mem_univ _) strictMono_id
    rw [extMinor, extMinorTuple, dif_pos hu, if_pos rfl]
    have hm : (Matrix.of (fun i j : Fin xs.length => extVector (xs.get j)
        ((Finset.univ : Finset (Fin xs.length)).orderEmbOfFin hu i))) =
        (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ)))ᵀ := by
      ext i j
      change ((xs.get j).val : ℤ) ^ ((Finset.univ : Finset (Fin xs.length)).orderEmbOfFin hu i).val =
        ((xs.get j).val : ℤ) ^ i.val
      rw [← hid]
    rw [hm, Matrix.det_transpose]
  · simp [extMinor, extMinorTuple, h]

private theorem extVandermonde_sorted_sq {n r : ℕ} (V : Finset (Fin n)) (h : V.card = r) :
    (Matrix.vandermonde (fun i => ((V.orderEmbOfFin h i).val : ℤ))).det ^ 2 =
      (extWeight V : ℤ) := by
  rw [Matrix.det_vandermonde]
  simp only [← Finset.prod_pow, extWeight, Nat.cast_prod, Nat.cast_pow]
  let f := (V.orderEmbOfFin h).toEmbedding
  let g (x : Fin n) : ℤ := ∏ y ∈ V.filter (fun y => x < y), ((y.val - x.val : ℕ) : ℤ) ^ 2
  calc
    _ = ∏ i : Fin r, g (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      change (∏ j ∈ Finset.Ioi i, (((f j).val : ℤ) - (f i).val) ^ 2) =
        ∏ y ∈ V.filter (fun y => V.orderEmbOfFin h i < y), ((y.val - (f i).val : ℕ) : ℤ) ^ 2
      rw [← extGreater_map V h i, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro j hj
      have hle : (f i).val ≤ (f j).val :=
        ((V.orderEmbOfFin h).strictMono (Finset.mem_Ioi.mp hj)).le
      rw [Nat.cast_sub hle]
    _ = (Finset.univ.map f).prod g := (Finset.prod_map _ _ _).symm
    _ = _ := congrArg (fun R : Finset (Fin n) => R.prod g) (Finset.map_orderEmbOfFin_univ V h)

private theorem extVandermonde_sq {n : ℕ} (xs : List (Fin n)) (hn : xs.Nodup) :
    (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ))).det ^ 2 =
      (extWeight xs.toFinset : ℤ) := by
  let V := xs.toFinset
  have hV : V.card = xs.length := List.toFinset_card_of_nodup hn
  let f (i : Fin xs.length) : ↥V := ⟨xs.get i, List.mem_toFinset.mpr (List.get_mem xs i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hn.injective_get (congrArg Subtype.val hij)
    · intro v
      obtain ⟨i, hi⟩ := List.get_of_mem (List.mem_toFinset.mp v.property)
      exact ⟨i, Subtype.ext hi⟩
  let E := V.orderIsoOfFin hV
  let σ : Equiv.Perm (Fin xs.length) := (Equiv.ofBijective f hf).trans E.toEquiv.symm
  have hσ (i : Fin xs.length) : V.orderEmbOfFin hV (σ i) = xs.get i := by
    change (↑(E (E.symm (f i))) : Fin n) = xs.get i
    rw [E.apply_symm_apply] <;> rfl
  let M := Matrix.vandermonde (fun i => ((V.orderEmbOfFin hV i).val : ℤ))
  have hm : Matrix.vandermonde (fun i => ((xs.get i).val : ℤ)) = M.submatrix σ id := by
    ext i j
    change ((xs.get i).val : ℤ) ^ j.val = ((V.orderEmbOfFin hV (σ i)).val : ℤ) ^ j.val
    rw [hσ]
  rw [hm, ← extVandermonde_sorted_sq V hV]
  have ha := Matrix.abs_det_submatrix_equiv_equiv σ (Equiv.refl _) M
  change (M.submatrix σ id).det ^ 2 = M.det ^ 2
  calc
    _ = |(M.submatrix σ id).det| ^ 2 := (sq_abs _).symm
    _ = |M.det| ^ 2 := congrArg (fun z : ℤ => z ^ (2 : ℕ)) ha
    _ = _ := sq_abs _

private theorem extVandermonde_zero {n : ℕ} (xs : List (Fin n)) (hn : ¬ xs.Nodup) :
    (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ))).det = 0 := by
  apply Matrix.det_vandermonde_eq_zero_iff.mpr
  by_contra h
  exact hn (List.nodup_iff_injective_get.mpr (fun i j hij => by
    by_contra hne
    exact h ⟨i, j, congrArg (fun v : Fin n => (v.val : ℤ)) hij, hne⟩))

open scoped Classical in
/-- The top coefficient is independent of the order of the (distinct) allowed edges. -/
theorem extRun_matching {n : ℕ} (k : ℕ) (edges : List (Fin n × Fin n))
    (hn : edges.Nodup) (ho : ∀ e ∈ edges, e.1 < e.2) :
    extRun (2 * k) edges Finset.univ Finset.univ =
      ∑ Q ∈ (edges.toFinset.powerset.filter (fun Q => Q.card = k ∧ extMatching Q)),
        (extWeight (Q.biUnion extEdgeEnds) : ℤ) := by
  classical
  rw [extRun_eq_sum _ edges hn, Finset.sum_apply, Finset.sum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Q hQ'
  have hQ := Finset.mem_powerset.mp hQ'
  have hlen : 2 * k = (extEndpoints edges Q).length ↔ Q.card = k := by
    rw [extEndpoints_length hn hQ]
    omega
  have hN : (extEndpoints edges Q).Nodup ↔ extMatching Q :=
    extEndpoints_nodup hn hQ (fun e he => ho e (List.mem_toFinset.mp (hQ he)))
  rw [extOuter, extMinor_univ]
  by_cases hc : Q.card = k
  · rw [ite_eq_left (hlen.mpr hc)]
    by_cases hM : extMatching Q
    · rw [if_pos (And.intro hc hM), ← pow_two, extVandermonde_sq _ (hN.mpr hM),
        extEndpoints_toFinset hQ]
    · have hbad : ¬ (Q.card = k ∧ extMatching Q) := fun hh => hM hh.2
      rw [if_neg hbad, extVandermonde_zero _ (mt hN.mp hM), zero_mul]
  · have hbad : ¬ (Q.card = k ∧ extMatching Q) := fun hh => hc hh.1
    rw [ite_eq_right (mt hlen.mp hc), ite_eq_right hbad, zero_mul]

open scoped Classical in
/-- Apply the list form of the theorem to any enumeration of a common allowed edge set. -/
theorem extRun_matching_of_toFinset {n : ℕ} (k : ℕ) (A : Finset (Fin n × Fin n))
    (edges : List (Fin n × Fin n)) (hn : edges.Nodup) (hA : edges.toFinset = A)
    (ho : ∀ e ∈ A, e.1 < e.2) :
    extRun (2 * k) edges Finset.univ Finset.univ =
      ∑ Q ∈ (A.powerset.filter (fun Q => Q.card = k ∧ extMatching Q)),
        (extWeight (Q.biUnion extEdgeEnds) : ℤ) := by
  classical
  rw [← hA]
  exact extRun_matching k edges hn (fun e he => ho e (hA ▸ List.mem_toFinset.mpr he))

end MatchingExterior


namespace Packed
open Lib.Universal

def maskBits {d : ℕ} (S : Finset (Fin d)) : List Bool :=
  (List.finRange d).map (fun i => decide (i ∈ S))

def maskIndex {d : ℕ} (S : Finset (Fin d)) : ℕ := val (maskBits S)

lemma maskBits_length {d : ℕ} (S : Finset (Fin d)) : (maskBits S).length = d := by simp [maskBits]

lemma maskIndex_lt {d : ℕ} (S : Finset (Fin d)) : maskIndex S < 2^d := by
  simpa [maskIndex, maskBits_length] using q124 (maskBits S)

lemma val_cons_bit (b : Bool) (xs : List Bool) : val (b :: xs) = Nat.bit b (val xs) := by
  cases b <;> simp [val, Nat.bit] <;> omega

lemma val_length_inj {a b : List Bool} (h : a.length = b.length) (hv : val a = val b) : a = b := by
  induction a generalizing b with
  | nil => simpa using h.symm
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      have he : x = y := by
        have hm := congrArg (· % 2) hv
        change (x.toNat + 2 * val a) % 2 = (y.toNat + 2 * val b) % 2 at hm
        cases x <;> cases y <;> simp at hm ⊢ <;> omega
      subst y
      have hh : val a = val b := by simp only [val] at hv; omega
      exact congrArg (x :: ·) (ih (by simpa using h) hh)

lemma val_bitAt (xs : List Bool) (i : ℕ) : (val xs).testBit i = xs.getD i false := by
  induction xs generalizing i with
  | nil => simp [val]
  | cons b xs ih =>
    cases i with
    | zero => simp [val_cons_bit, Nat.testBit_bit_zero]
    | succ i => simpa [val_cons_bit, Nat.testBit_bit_succ] using ih i

lemma maskIndex_bit {d : ℕ} (S : Finset (Fin d)) (j : Fin d) :
    (maskIndex S).testBit j.val = decide (j ∈ S) := by
  rw [maskIndex, val_bitAt, maskBits, List.getD_eq_getElem _ _ (by simpa using j.isLt)]
  simp

lemma val_ofFn {d : ℕ} (f : Fin d → Bool) :
    val (List.ofFn f) = ∑ i : Fin d, if f i then 2^i.val else 0 := by
  induction d with
  | zero => simp [val]
  | succ d ih =>
    rw [List.ofFn_succ, val, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, pow_succ, Finset.mul_sum]
    cases h0 : f 0 <;> simp [h0, mul_comm 2]

lemma maskIndex_eq_sum {d : ℕ} (S : Finset (Fin d)) : maskIndex S = ∑ i ∈ S, 2^i.val := by
  rw [maskIndex, maskBits, List.finRange, List.map_ofFn, val_ofFn]
  simp [Finset.sum_filter]

lemma maskIndex_erase {d : ℕ} (S : Finset (Fin d)) {i : Fin d} (hi : i ∈ S) :
    maskIndex S - 2^i.val = maskIndex (S.erase i) := by
  rw [maskIndex_eq_sum, maskIndex_eq_sum, ← Finset.sum_erase_add _ _ hi]
  exact Nat.add_sub_cancel _ _

lemma maskIndex_empty {d : ℕ} (S : Finset (Fin d)) : maskIndex S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh := maskIndex_bit S i
    simp [h, hi] at hh
  · rintro rfl
    simp [maskIndex_eq_sum]

lemma maskIndex_univ (d : ℕ) : maskIndex (Finset.univ : Finset (Fin d)) = 2^d - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < d
  · simpa [hi] using maskIndex_bit (Finset.univ : Finset (Fin d)) ⟨i, hi⟩
  · have hh : maskIndex (Finset.univ : Finset (Fin d)) < 2^i :=
      (maskIndex_lt _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))
    simp [hi, Nat.testBit_eq_false_of_lt hh]

lemma maskBits_pad {d : ℕ} (S : Finset (Fin d)) :
    padW (un d) (q48 (un (maskIndex S))) = maskBits S := by
  apply val_length_inj
  · simp [q19, maskBits_length]
  · rw [q26, q71, q194, un_length, un_length, Nat.mod_eq_of_lt (maskIndex_lt S)]
    rfl

lemma mem_finRange_drop {d : ℕ} (j : Fin d) (i : ℕ) :
    j ∈ (List.finRange d).drop i ↔ i ≤ j.val := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := List.get_of_mem h
    have hp' : p.val < d - i := by simpa using p.isLt
    have he : (List.finRange d)[i + p.val]'(by simp; omega) = j := by
      simpa only [List.get_eq_getElem, List.getElem_drop, Nat.add_comm] using hp
    have he' := congrArg Fin.val he
    simp at he'
    omega
  · intro h
    let p : Fin ((List.finRange d).drop i).length := ⟨j.val-i, by simp; omega⟩
    have hp : ((List.finRange d).drop i).get p = j := by
      apply Fin.ext
      simp [p]
      omega
    rw [← hp]
    exact List.get_mem _ _

lemma maskBits_gt {d : ℕ} (S : Finset (Fin d)) (i : Fin d) :
    (q49 ((maskBits S).drop (i.val+1))).length = (S.filter (fun j => i < j)).card := by
  let L := (((List.finRange d).drop (i.val+1)).filter (fun j => decide (j ∈ S)))
  have hL : L.Nodup := (List.nodup_finRange d).drop.filter _
  have hS : L.toFinset = S.filter (fun j => i < j) := by
    ext j
    simp only [L, List.mem_toFinset, List.mem_filter, mem_finRange_drop, decide_eq_true_eq, Finset.mem_filter]
    exact ⟨fun ⟨h, hS⟩ => ⟨hS,h⟩, fun ⟨hS,h⟩ => ⟨h,hS⟩⟩
  rw [← hS, List.toFinset_card_of_nodup hL]
  simp only [q49, maskBits, ← List.map_drop, List.filter_map, List.length_map, L, Function.comp_def, id]

end Packed

namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

def pack : List (List Bool) → List Bool
  | [] => []
  | x :: xs => pairB x (pack xs)

def field : ℕ → List Bool → List Bool
  | 0, x => left x
  | j+1, x => field j (right x)

lemma cpField (j : ℕ) {f : List Bool → List Bool} (hf : Lib.CPTs f) :
    Lib.CPTs (fun s => field j (f s)) := by
  induction j generalizing f with
  | zero => exact cpLeft hf
  | succ j ih => exact ih (cpRight hf)

lemma cpPack (L : List (List Bool → List Bool)) (h : ∀ f ∈ L, Lib.CPTs f) :
    Lib.CPTs (fun s => pack (L.map (fun f => f s))) := by
  induction L with
  | nil => exact cpt_const []
  | cons f L ih => exact cpt_pairB2 (h f (by simp)) (ih (fun g hg => h g (by simp [hg])))

lemma field_pack_zero (x : List Bool) (xs : List (List Bool)) :
    field 0 (pack (x :: xs)) = x := by simp [field, pack, left, unpairB_pairB]

lemma field_pack_succ (j : ℕ) (x : List Bool) (xs : List (List Bool)) :
    field (j+1) (pack (x :: xs)) = field j (pack xs) := by simp [field, pack, right, unpairB_pairB]

lemma field_right_pair (a b : List Bool) : right (pairB a b) = b := by simp [right, unpairB_pairB]

lemma field_left_pair (a b : List Bool) : left (pairB a b) = a := by simp [left, unpairB_pairB]

def tableAt (w count s t tab : List Bool) : List Bool :=
  slot w t (slot (mulU count w) s tab)

lemma cpTableAt {w b i j tab : List Bool → List Bool} (hw : Lib.CPTs w) (hb : Lib.CPTs b)
    (hi : Lib.CPTs i) (hj : Lib.CPTs j) (ht : Lib.CPTs tab) :
    Lib.CPTs (fun s => tableAt (w s) (b s) (i s) (j s) (tab s)) :=
  cpSlot hw hj (cpSlot (q42 hb hw) hi ht)

def tableCell (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  f (pairB (left (right x)) (pairB (left x) (right (right x))))

lemma cpTableCell {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (tableCell f) := by
  unfold tableCell
  exact cpt_comp (cpt_pairB2 (cpLeft (cpRight cpt_id))
    (cpt_pairB2 (cpLeft cpt_id) (cpRight (cpRight cpt_id)))) hf

def tableRow (f : List Bool → List Bool) (w b s a : List Bool) : List Bool :=
  mapRange (tableCell f) w b (pairB s a)

lemma cpTableRow {f w b s a : List Bool → List Bool} (hf : Lib.CPTs f) (hw : Lib.CPTs w)
    (hb : Lib.CPTs b) (hs : Lib.CPTs s) (ha : Lib.CPTs a) :
    Lib.CPTs (fun x => tableRow f (w x) (b x) (s x) (a x)) :=
  cpMapRange (cpTableCell hf) hw hb (cpt_pairB2 hs ha)

def tableRowPacked (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  tableRow f (field 0 (right x)) (field 1 (right x)) (left x) (field 2 (right x))

def tableMake (f : List Bool → List Bool) (w b a : List Bool) : List Bool :=
  mapRange (tableRowPacked f) (mulU b w) b (pack [w,b,a])

lemma cpTableMake {f w b a : List Bool → List Bool} (hf : Lib.CPTs f) (hw : Lib.CPTs w)
    (hb : Lib.CPTs b) (ha : Lib.CPTs a) :
    Lib.CPTs (fun x => tableMake f (w x) (b x) (a x)) := by
  have hrow : Lib.CPTs (tableRowPacked f) :=
    cpTableRow hf (cpField 0 (cpRight cpt_id)) (cpField 1 (cpRight cpt_id))
      (cpLeft cpt_id) (cpField 2 (cpRight cpt_id))
  have hargs : Lib.CPTs (fun x => pack [w x,b x,a x]) := by
    apply cpPack [w,b,a]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  exact cpMapRange hrow (q42 hb hw) hb hargs

lemma flatMap_len {α : Type*} (L : List α) (f : α → List Bool) (k : ℕ)
    (h : ∀ a ∈ L, (f a).length = k) : (L.flatMap f).length = L.length * k := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp [h a (by simp), ih (fun b hb => h b (by simp [hb])), Nat.succ_mul, Nat.add_comm]

lemma tableMake_eq (f : List Bool → List Bool) (w b a : List Bool)
    (h : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length) :
    tableMake f w b a = (List.range b.length).flatMap (fun s =>
       (List.range b.length).flatMap (fun t => f (pairB (un s) (pairB (un t) a)))) := by
  have hrow (s : ℕ) (hs : s < b.length) :
      tableRowPacked f (pairB (un s) (pack [w,b,a])) =
      (List.range b.length).flatMap (fun t => f (pairB (un s) (pairB (un t) a))) := by
    simp only [tableRowPacked, field_left_pair, field_right_pair, field_pack_succ, field_pack_zero, tableRow]
    rw [mapRange_eq]
    · simp [tableCell, field_left_pair, field_right_pair]
    · intro t ht
      simp [tableCell, field_left_pair, field_right_pair, h s hs t ht]
  unfold tableMake
  rw [mapRange_eq]
  · exact List.flatMap_congr fun s hs => hrow s (List.mem_range.mp hs)
  · intro s hs
    rw [hrow s hs, flatMap_len _ _ w.length (fun t ht => h s hs t (List.mem_range.mp ht))]
    simp [mulU]

lemma tableMake_length (f : List Bool → List Bool) (w b a : List Bool)
    (h : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length) :
    (tableMake f w b a).length = b.length * (b.length * w.length) := by
  rw [tableMake_eq f w b a h]
  refine (flatMap_len _ _ (b.length * w.length) (fun s hs => ?_)).trans (by rw [List.length_range])
  simpa using flatMap_len _ _ w.length (fun t ht => h s (List.mem_range.mp hs) t (List.mem_range.mp ht))

lemma tableAt_make (f : List Bool → List Bool) (w b a : List Bool) (s t : ℕ)
    (hs : s < b.length) (ht : t < b.length)
    (h : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length) :
    tableAt w b (un s) (un t) (tableMake f w b a) = f (pairB (un s) (pairB (un t) a)) := by
  let row (i : ℕ) := (List.range b.length).flatMap (fun j => f (pairB (un i) (pairB (un j) a)))
  have hrow : ∀ i ∈ List.range b.length, (row i).length = (mulU b w).length := by
    intro i hi
    dsimp only [row]
    rw [flatMap_len _ _ w.length (fun j hj => h i (List.mem_range.mp hi) j (List.mem_range.mp hj))]
    simp [mulU]
  have hs' : s < (List.range b.length).length := by simpa
  have ht' : t < (List.range b.length).length := by simpa
  rw [tableMake_eq f w b a h, tableAt, slot_flatMap (List.range b.length) row _ s hs' hrow]
  simp only [List.getElem_range, row]
  rw [slot_flatMap _ _ _ t ht' (fun j hj => h s hs j (List.mem_range.mp hj))]
  simp

def tableRep {d : ℕ} (w b tab : List Bool) (D : extTable d) : Prop :=
  tab.length = b.length * (b.length * w.length) ∧
  ∀ S T, rep w (tableAt w b (un (maskIndex S)) (un (maskIndex T)) tab) (D S T)

lemma tableMake_rep {d : ℕ} (f : List Bool → List Bool) (w b a : List Bool) (D : extTable d)
    (hb : b.length = 2^d)
    (hlen : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length)
    (h : ∀ S T : Finset (Fin d),
      rep w (f (pairB (un (maskIndex S)) (pairB (un (maskIndex T)) a))) (D S T)) :
    tableRep w b (tableMake f w b a) D := by
  refine ⟨tableMake_length f w b a hlen, fun S T => ?_⟩
  rw [tableAt_make f w b a _ _ (hb ▸ maskIndex_lt S) (hb ▸ maskIndex_lt T) hlen]
  exact h S T

end Packed


namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

def signedWord (w flag b : List Bool) : List Bool := sel flag b (negW w b)

lemma cpSignedWord {w f b : List Bool → List Bool} (hw : Lib.CPTs w) (hf : Lib.CPTs f)
    (hb : Lib.CPTs b) : Lib.CPTs (fun s => signedWord (w s) (f s) (b s)) :=
  cpt_sel hf hb (q120 hw hb)

lemma pow_neg_one_mod (a : ℕ) : (-1 : ℤ)^a = if a % 2 = 1 then -1 else 1 := by
  calc
    _ = (-1 : ℤ)^(2*(a/2) + a%2) := congrArg ((-1 : ℤ) ^ ·) (by omega)
    _ = _ := by
      rw [pow_add, pow_mul]
      norm_num
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]

lemma parity_word_rep {w x u : List Bool} {z : ℤ} (hz : rep w x z) :
    rep w (signedWord w (q112 u) x) ((-1 : ℤ)^u.length * z) := by
  rw [pow_neg_one_mod]
  by_cases h : u.length % 2 = 1
  · simpa [signedWord, sel, q112, h] using rep_neg hz
  · simpa [signedWord, sel, q112, h] using hz

def initCell (s : List Bool) : List Bool :=
  let w := right (right s)
  natW w (sel (left s ++ left (right s)) [true] [])

lemma cpInitCell : Lib.CPTs initCell :=
  q50 (cpRight (cpRight cpt_id))
    (cpt_sel (cpt_app2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id))) (cpt_const [true]) (cpt_const []))

def tableInit (w b : List Bool) : List Bool := tableMake initCell w b w

lemma cpTableInit {w b : List Bool → List Bool} (hw : Lib.CPTs w) (hb : Lib.CPTs b) :
    Lib.CPTs (fun s => tableInit (w s) (b s)) := cpTableMake cpInitCell hw hb hw

lemma tableInit_rep {d : ℕ} (w b : List Bool) (hb : b.length = 2^d) :
    tableRep w b (tableInit w b) (extInit d) := by
  apply tableMake_rep _ _ _ _ _ hb
  · intro s hs t ht
    simp [initCell, field_left_pair, field_right_pair, q54]
  · intro S T
    simp only [initCell, field_left_pair, field_right_pair, extInit]
    have h := rep_nat w (sel (un (maskIndex S) ++ un (maskIndex T)) [true] [])
    by_cases hs : S = ∅ <;> by_cases ht : T = ∅ <;>
      simpa [sel, un, hs, ht, maskIndex_empty] using h

def wedgeTerm (onRight : Bool) (s : List Bool) : List Bool :=
  let i := left s
  let a := right s
  let w := field 0 a
  let d := field 1 a
  let b := field 2 a
  let v := field 3 a
  let S := field 4 a
  let T := field 5 a
  let tab := field 6 a
  let U := if onRight then T else S
  let bits := padW d (q48 U)
  let erase := U.drop (powerTwo b i).length
  let coeff := tableAt w b (if onRight then S else erase) (if onRight then erase else T) tab
  let prod := mulW w (powW w (natW w v) i) coeff
  sel (bitFlagAt i bits) (blank w) (signedWord w (q112 (q49 (bits.drop (i.length+1)))) prod)

set_option maxHeartbeats 1000000 in
lemma cpWedgeTerm (r : Bool) : Lib.CPTs (wedgeTerm r) := by
  have hi := cpLeft cpt_id
  have ha := cpRight cpt_id
  have hw := cpField 0 ha
  have hd := cpField 1 ha
  have hb := cpField 2 ha
  have hv := cpField 3 ha
  have hs := cpField 4 ha
  have ht := cpField 5 ha
  have htab := cpField 6 ha
  have hu : Lib.CPTs (fun x => if r then field 5 (right x) else field 4 (right x)) := by
    cases r
    · exact hs
    · exact ht
  have hbits := q13 hd (cpt_comp hu q41)
  have he := cpDrop (powerTwo_cpt hb hi) hu
  have hleft : Lib.CPTs (fun x => if r then field 4 (right x) else
      (if r then field 5 (right x) else field 4 (right x)).drop (powerTwo (field 2 (right x)) (left x)).length) := by
    cases r
    · exact he
    · exact hs
  have hright : Lib.CPTs (fun x => if r then
      (if r then field 5 (right x) else field 4 (right x)).drop (powerTwo (field 2 (right x)) (left x)).length
      else field 5 (right x)) := by
    cases r
    · exact ht
    · exact he
  exact cpt_sel (cpBitFlagAt hi hbits) (cpt_comp hw cpt_blank)
    (cpSignedWord hw (cpt_comp (cpt_comp (cpDrop (cpCons true hi) hbits) q150) q137)
      (q32 hw (q202 hw (q50 hw hv) hi) (cpTableAt hw hb hleft hright htab)))

def wedgeCell (r : Bool) (s : List Bool) : List Bool :=
  let a := right (right s)
  let w := field 0 a
  let d := field 1 a
  sumRange (wedgeTerm r) w d (pack [w,d,field 2 a,field 3 a,left s,left (right s),field 4 a])

lemma cpWedgeCell (r : Bool) : Lib.CPTs (wedgeCell r) := by
  have ha := cpRight (cpRight cpt_id)
  have hw := cpField 0 ha
  have hd := cpField 1 ha
  unfold wedgeCell
  apply cpSumRange (cpWedgeTerm r) hw hd
  apply cpPack [fun s => field 0 (right (right s)), fun s => field 1 (right (right s)),
    fun s => field 2 (right (right s)), fun s => field 3 (right (right s)), left,
    fun s => left (right s), fun s => field 4 (right (right s))]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw
  · exact hd
  · exact cpField 2 ha
  · exact cpField 3 ha
  · exact cpLeft cpt_id
  · exact cpLeft (cpRight cpt_id)
  · exact cpField 4 ha

def wedgeTable (r : Bool) (w d b v tab : List Bool) : List Bool :=
  tableMake (wedgeCell r) w b (pack [w,d,b,v,tab])

lemma cpWedgeTable (r : Bool) {w d b v tab : List Bool → List Bool} (hw : Lib.CPTs w)
    (hd : Lib.CPTs d) (hb : Lib.CPTs b) (hv : Lib.CPTs v) (htab : Lib.CPTs tab) :
    Lib.CPTs (fun s => wedgeTable r (w s) (d s) (b s) (v s) (tab s)) := by
  apply cpTableMake (cpWedgeCell r) hw hb
  apply cpPack [w,d,b,v,tab]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption

lemma wedgeTerm_rep {n d : ℕ} (r : Bool) (w b tab : List Bool) (v : Fin n)
    (T : extTable d) (hb : b.length = 2^d) (hT : tableRep w b tab T)
    (S U : Finset (Fin d)) (i : Fin d) :
    let M := if r then U else S
    let ix := fun X : Finset (Fin d) => un (maskIndex X)
    rep w (wedgeTerm r (pairB (un i.val) (pack [w,un d,b,un v.val,ix S,ix U,tab])))
      (if i ∈ M then (-1 : ℤ)^(M.filter (fun j => i < j)).card * extVector v i *
        T (if r then S else S.erase i) (if r then U.erase i else U) else 0) := by
  let M := if r then U else S
  let ix := fun X : Finset (Fin d) => un (maskIndex X)
  have hbits : padW (un d) (q48 (ix M)) = maskBits M := maskBits_pad M
  have hbit : bitFlagAt (un i.val) (maskBits M) = bflag (decide (i ∈ M)) := by
    rw [bitFlagAt_eq, un_length, ← val_bitAt, ← maskIndex, maskIndex_bit]
  have hcap : 2^(un i.val).length ≤ b.length := by
    rw [un_length, hb]
    exact Nat.pow_le_pow_right (by decide) i.isLt.le
  have hpow := powerTwo_eq b (un i.val) hcap
  have hsign := maskBits_gt M i
  dsimp only
  simp only [wedgeTerm, field_left_pair, field_right_pair, field_pack_succ, field_pack_zero]
  have hm : (if r then ix U else ix S) = ix M := by cases r <;> rfl
  rw [hm, hbits, hbit]
  by_cases hi : i ∈ M
  · rw [if_pos hi]
    simp only [hi, decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
    have he : (ix M).drop (powerTwo b (un i.val)).length = ix (M.erase i) := by
      rw [hpow]
      simp [ix, un, List.drop_replicate, maskIndex_erase M hi]
    rw [he]
    have harg1 : (if r then ix S else ix (M.erase i)) = ix (if r then S else S.erase i) := by
      cases r <;> rfl
    have harg2 : (if r then ix (M.erase i) else ix U) = ix (if r then U.erase i else U) := by
      cases r <;> rfl
    rw [harg1,harg2]
    have hc := hT.2 (if r then S else S.erase i) (if r then U.erase i else U)
    have hv := rep_pow (rep_nat w (un v.val)) (un i.val)
    have hp := rep_mul hv hc
    have hr := parity_word_rep (u := q49 ((maskBits M).drop ((un i.val).length+1))) hp
    rw [un_length, hsign] at hr
    simpa [extVector, ← mul_assoc, un_length] using hr
  · rw [if_neg hi]
    simpa [hi, bflag, sel] using rep_zero w

lemma sum_range_fin (d : ℕ) (z : Fin d → ℤ) :
    ((List.range d).map (fun i => if h : i<d then z ⟨i,h⟩ else 0)).sum = ∑ i, z i := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]

lemma wedgeTable_rep {n d : ℕ} (r : Bool) (w b tab : List Bool) (v : Fin n)
    (T : extTable d) (hb : b.length = 2^d) (hT : tableRep w b tab T) :
    tableRep w b (wedgeTable r w (un d) b (un v.val) tab)
      (if r then extAppendRight (extVector v) T else extAppendLeft (extVector v) T) := by
  apply tableMake_rep _ _ _ _ _ hb
  · intro s hs t ht
    simp [wedgeCell, field_left_pair, field_right_pair, field_pack_succ, field_pack_zero, sumRange_length]
  · intro S U
    let M := if r then U else S
    let z : Fin d → ℤ := fun i => if i ∈ M then
      (-1 : ℤ)^((M.filter (fun j => i < j)).card) * extVector v i *
        T (if r then S else S.erase i) (if r then U.erase i else U) else 0
    have h := sumRange_rep (wedgeTerm r) w (un d)
      (pack [w,un d,b,un v.val,un (maskIndex S),un (maskIndex U),tab])
      (fun i => if hi : i<d then z ⟨i,hi⟩ else 0)
      (fun i hi => by
        rw [un_length] at hi
        simpa [hi, z, M] using wedgeTerm_rep r w b tab v T hb hT S U ⟨i,hi⟩)
    rw [un_length, sum_range_fin] at h
    have hz : (∑ i, z i) = (if r then extAppendRight (extVector v) T else extAppendLeft (extVector v) T) S U := by
      cases r <;> simp [z, M, extAppendRight, extAppendLeft, Finset.sum_filter]
    rw [hz] at h
    simpa only [wedgeCell, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ] using h

end Packed

namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

def header (n : ℕ) : List Bool := un n ++ [false]

def pairs (n : ℕ) : List (Edge n) := (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))

def mask {n : ℕ} (E : Finset (Edge n)) : List Bool := (pairs n).map (fun e => decide (e ∈ E))

def rowBits {n : ℕ} (r : Row n) : List Bool := r.2 :: mask r.1

lemma mask_length {n : ℕ} (E : Finset (Edge n)) : (mask E).length = (pairs n).length := by simp [mask]

lemma pairs_mem {n : ℕ} (e : Edge n) : e ∈ pairs n ↔ e.1 < e.2 := by
  obtain ⟨a,b⟩ := e
  simp [pairs]

lemma pairs_nodup (n : ℕ) : (pairs n).Nodup := by
  rw [pairs,List.nodup_flatMap]
  refine ⟨fun i _=>((List.nodup_finRange n).filter _).map (fun a b h=>(Prod.mk.inj h).2),?_⟩
  refine (List.nodup_finRange n).imp (fun {a b} hab=>?_)
  intro x hx hy
  simp only [List.mem_map] at hx hy
  obtain ⟨_,_,rfl⟩:=hx
  obtain ⟨_,_,h⟩:=hy
  exact hab (Prod.mk.inj h).1.symm

def pairCell (f : List Bool → List Bool) (s : List Bool) : List Bool :=
  let j := left s
  let i := left (right s)
  let n := right (right s)
  sel (j.drop i.length) [] (f (pack [i,j,n]))

lemma cpPairCell {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (pairCell f) := by
  have hi := cpLeft (cpRight cpt_id)
  have hj := cpLeft cpt_id
  have hn := cpRight (cpRight cpt_id)
  apply cpt_sel (cpDrop hi hj) (cpt_const [])
  apply cpt_comp _ hf
  apply cpPack [fun s => left (right s), left, fun s => right (right s)]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> assumption

def pairRow (f : List Bool → List Bool) (s : List Bool) : List Bool :=
  let i := left s
  let n := left (right s)
  let cap := right (right s)
  mapRange (pairCell f) cap n (pairB i n)

lemma cpPairRow {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (pairRow f) :=
  cpMapRange (cpPairCell hf) (cpRight (cpRight cpt_id)) (cpLeft (cpRight cpt_id))
    (cpt_pairB2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id)))

def pairMap (f : List Bool → List Bool) (n cap : List Bool) : List Bool :=
  mapRange (pairRow f) (mulU n cap) n (pairB n cap)

lemma cpPairMap {f n cap : List Bool → List Bool} (hf : Lib.CPTs f) (hn : Lib.CPTs n)
    (hc : Lib.CPTs cap) : Lib.CPTs (fun s => pairMap f (n s) (cap s)) :=
  cpMapRange (cpPairRow hf) (q42 hn hc) hn (cpt_pairB2 hn hc)

lemma flatMap_filter_eq {α β : Type*} (L : List α) (p : α → Bool) (f : α → List β) :
    (L.filter p).flatMap f = L.flatMap (fun x => if p x then f x else []) := by
  induction L with
  | nil => rfl
  | cons a L ih => cases hp : p a <;> simp [hp, ih]

lemma flatMap_len_le {α : Type*} (L : List α) (f : α → List Bool) (cap : ℕ)
    (h : ∀ a ∈ L, (f a).length ≤ cap) : (L.flatMap f).length ≤ L.length * cap := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a (by simp))
      (ih (fun b hb => h b (by simp [hb])))

lemma pairMap_eq (f : List Bool → List Bool) (n : ℕ) (cap : List Bool)
    (h : ∀ i < n, ∀ j < n, i < j → (f (pack [un i,un j,un n])).length ≤ cap.length) :
    pairMap f (un n) cap = (pairs n).flatMap (fun e => f (pack [un e.1.val, un e.2.val, un n])) := by
  let emit (i j : ℕ) := if i < j then f (pack [un i,un j,un n]) else []
  have hcell (i j : ℕ) : pairCell f (pairB (un j) (pairB (un i) (un n))) = emit i j := by
    by_cases hij : i < j
    · simp [pairCell, emit, field_left_pair, field_right_pair, un, List.drop_replicate, sel, hij,
        Nat.sub_ne_zero_of_lt hij]
    · simp [pairCell, emit, field_left_pair, field_right_pair, un, List.drop_replicate, sel, hij,
        Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hij)]
  have hrow (i : ℕ) (hi : i < n) : pairRow f (pairB (un i) (pairB (un n) cap)) =
      (List.range n).flatMap (emit i) := by
    simp only [pairRow, field_left_pair, field_right_pair]
    rw [mapRange_eq]
    · simp [hcell]
    · intro j hj
      rw [hcell]
      rw [un_length] at hj
      by_cases hij : i < j
      · simpa [emit, hij] using h i hi j hj hij
      · simp [emit, hij]
  have bound (i : ℕ) (hi : i < n) : ((List.range n).flatMap (emit i)).length ≤ n * cap.length := by
    refine (flatMap_len_le _ _ cap.length fun j hj => ?_).trans (by rw [List.length_range])
    have hj' := List.mem_range.mp hj
    by_cases hij : i < j
    · simpa [emit, hij] using h i hi j hj' hij
    · simp [emit, hij]
  rw [pairMap, mapRange_eq]
  · simp only [un_length]
    rw [show (List.range n).flatMap (fun i => pairRow f (pairB (un i) (pairB (un n) cap))) =
      (List.range n).flatMap (fun i => (List.range n).flatMap (emit i)) from
        List.flatMap_congr fun i hi => hrow i (List.mem_range.mp hi)]
    simp only [pairs, List.flatMap_assoc, List.flatMap_map, flatMap_filter_eq]
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    simp only [List.flatMap_map, Function.comp_apply, decide_eq_true_eq]
    rfl
  · intro i hi
    rw [un_length] at hi
    rw [hrow i hi]
    simpa [mulU] using bound i hi

def pairCount (n : List Bool) : List Bool := pairMap (fun _ => [true]) n [true]

lemma cpPairCount {n : List Bool → List Bool} (hn : Lib.CPTs n) :
    Lib.CPTs (fun s => pairCount (n s)) := cpPairMap (cpt_const [true]) hn (cpt_const [true])

lemma pairCount_length (n : ℕ) : (pairCount (un n)).length = (pairs n).length := by
  rw [pairCount, pairMap_eq]
  · simpa using flatMap_len (pairs n) (fun _ => [true]) 1 (by simp)
  · simp

def endpointCode (n x : List Bool) : List Bool := (x ++ blank n).take n.length

lemma cpEndpointCode {n x : List Bool → List Bool} (hn : Lib.CPTs n) (hx : Lib.CPTs x) :
    Lib.CPTs (fun s => endpointCode (n s) (x s)) := cpTake hn (cpt_app2 hx (cpt_comp hn cpt_blank))

lemma endpointCode_length (n x : List Bool) : (endpointCode n x).length = n.length := by
  simp [endpointCode, q33]

def pairCode (s : List Bool) : List Bool :=
  endpointCode (field 2 s) (field 0 s) ++ endpointCode (field 2 s) (field 1 s)

lemma cpPairCode : Lib.CPTs pairCode :=
  cpt_app2 (cpEndpointCode (cpField 2 cpt_id) (cpField 0 cpt_id))
    (cpEndpointCode (cpField 2 cpt_id) (cpField 1 cpt_id))

def pairWords (n : List Bool) : List Bool := pairMap pairCode n (n ++ n)

lemma cpPairWords {n : List Bool → List Bool} (hn : Lib.CPTs n) :
    Lib.CPTs (fun s => pairWords (n s)) := cpPairMap cpPairCode hn (cpt_app2 hn hn)

lemma pairWords_eq (n : ℕ) : pairWords (un n) = (pairs n).flatMap (fun e =>
    endpointCode (un n) (un e.1.val) ++ endpointCode (un n) (un e.2.val)) := by
  rw [pairWords, pairMap_eq]
  · simp [pairCode, field_pack_zero, field_pack_succ]
  · simp [pairCode, endpointCode_length, field_pack_zero, field_pack_succ]

lemma hd_un_false (i : ℕ) (x : List Bool) : hd (un i ++ false :: x) = un i := by simp [hd, un]

lemma dropN_un_false (i : ℕ) (x : List Bool) : dropN (un i ++ false :: x) = x := by
  have h : (un i ++ false :: x).dropWhile id = false :: x := by simp [un]
  simp [dropN, h]

lemma hd_endpointCode (n i : ℕ) (hi : i ≤ n) : hd (endpointCode (un n) (un i)) = un i := by
  unfold endpointCode
  rw [un_length, List.take_append, List.take_of_length_le (by simpa using hi)]
  have h : (blank (un n)).take (n-i) = List.replicate (n-i) false := by
    simp [blank, un, Nat.sub_le]
  rw [un_length, h]
  cases e : n-i with
  | zero => simp [hd, un]
  | succ k => exact hd_un_false i _

lemma pairWords_get (n i : ℕ) (hi : i < (pairs n).length) :
    let word := slot (un n ++ un n) (un i) (pairWords (un n))
    let e := (pairs n)[i]
    hd (word.take n) = un e.1.val ∧ hd (word.drop n) = un e.2.val := by
  rw [pairWords_eq, slot_flatMap _ _ _ _ hi]
  · dsimp only
    have hfirst := endpointCode_length (un n) (un (pairs n)[i].1.val)
    rw [un_length] at hfirst
    let l := endpointCode (un n) (un (pairs n)[i].1.val)
    let r := endpointCode (un n) (un (pairs n)[i].2.val)
    have ht : (l ++ r).take n = l :=
      (congrArg (fun p => (l ++ r).take p) hfirst.symm).trans List.take_left
    have hd' : (l ++ r).drop n = r :=
      (congrArg (fun p => (l ++ r).drop p) hfirst.symm).trans List.drop_append_length
    rw [ht, hd']
    exact ⟨hd_endpointCode _ _ (pairs n)[i].1.isLt.le, hd_endpointCode _ _ (pairs n)[i].2.isLt.le⟩
  · simp [endpointCode_length]

end Packed

namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

def plusCell (s : List Bool) : List Bool :=
  let a := right (right s)
  let w := field 0 a
  let b := field 1 a
  let i := left s
  let j := left (right s)
  addW w (tableAt w b i j (field 2 a)) (tableAt w b i j (field 3 a))

lemma cpPlusCell : Lib.CPTs plusCell := by
  have ha := cpRight (cpRight cpt_id)
  have hw := cpField 0 ha
  have hb := cpField 1 ha
  have hi := cpLeft cpt_id
  have hj := cpLeft (cpRight cpt_id)
  exact q82 hw (cpTableAt hw hb hi hj (cpField 2 ha)) (cpTableAt hw hb hi hj (cpField 3 ha))

def tablePlus (w b x y : List Bool) : List Bool := tableMake plusCell w b (pack [w,b,x,y])

lemma cpTablePlus {w b x y : List Bool → List Bool} (hw : Lib.CPTs w) (hb : Lib.CPTs b)
    (hx : Lib.CPTs x) (hy : Lib.CPTs y) : Lib.CPTs (fun s => tablePlus (w s) (b s) (x s) (y s)) := by
  apply cpTableMake cpPlusCell hw hb
  apply cpPack [w,b,x,y]
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> assumption

lemma tablePlus_rep {d : ℕ} (w b x y : List Bool) {A B : extTable d} (hb : b.length = 2^d)
    (ha : tableRep w b x A) (hB : tableRep w b y B) : tableRep w b (tablePlus w b x y) (A + B) := by
  apply tableMake_rep _ _ _ _ _ hb
  · intro i hi j hj
    simp [plusCell, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ, q36]
  · intro S T
    simpa only [plusCell, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ, Pi.add_apply]
      using rep_add (ha.2 S T) (hB.2 S T)

def takeTable (w d b u v tab : List Bool) : List Bool :=
  wedgeTable true w d b v (wedgeTable true w d b u (wedgeTable false w d b v (wedgeTable false w d b u tab)))

lemma cpTakeTable {w d b u v tab : List Bool → List Bool} (hw : Lib.CPTs w) (hd : Lib.CPTs d)
    (hb : Lib.CPTs b) (hu : Lib.CPTs u) (hv : Lib.CPTs v) (htab : Lib.CPTs tab) :
    Lib.CPTs (fun s => takeTable (w s) (d s) (b s) (u s) (v s) (tab s)) :=
  cpWedgeTable true hw hd hb hv (cpWedgeTable true hw hd hb hu
    (cpWedgeTable false hw hd hb hv (cpWedgeTable false hw hd hb hu htab)))

lemma takeTable_rep {n d : ℕ} (w b tab : List Bool) (e : Edge n) (D : extTable d)
    (hb : b.length = 2^d) (hD : tableRep w b tab D) :
    tableRep w b (takeTable w (un d) b (un e.1.val) (un e.2.val) tab) (extTake e D) :=
  wedgeTable_rep true _ _ _ e.2 _ hb (wedgeTable_rep true _ _ _ e.1 _ hb
    (wedgeTable_rep false _ _ _ e.2 _ hb (wedgeTable_rep false _ _ _ e.1 _ hb hD)))

def edgeUpdate (s : List Bool) : List Bool :=
  let i := left s
  let a := left (right s)
  let tab := right (right s)
  let w := field 0 a
  let d := field 1 a
  let b := field 2 a
  let n := field 3 a
  let E := field 4 a
  let A := field 5 a
  let B := field 6 a
  let edges := field 7 a
  let keep := sel (bitFlagAt i E) [] (sel (bitFlagAt i A) [] (bitFlagAt i B))
  let e := slot (n ++ n) i edges
  let u := hd (e.take n.length)
  let v := hd (e.drop n.length)
  sel keep tab (tablePlus w b tab (takeTable w d b u v tab))

lemma cpEdgeUpdate : Lib.CPTs edgeUpdate := by
  have hi := cpLeft cpt_id
  have ha := cpLeft (cpRight cpt_id)
  have ht := cpRight (cpRight cpt_id)
  have hw := cpField 0 ha
  have hd' := cpField 1 ha
  have hb := cpField 2 ha
  have hn := cpField 3 ha
  have hE := cpBitFlagAt hi (cpField 4 ha)
  have hA := cpBitFlagAt hi (cpField 5 ha)
  have hB := cpBitFlagAt hi (cpField 6 ha)
  have he := cpSlot (cpt_app2 hn hn) hi (cpField 7 ha)
  have hu := cpt_comp (cpTake hn he) cpt_hd
  have hv := cpt_comp (cpDrop hn he) cpt_hd
  exact cpt_sel (cpt_sel hE (cpt_const []) (cpt_sel hA (cpt_const []) hB)) ht
    (cpTablePlus hw hb ht (cpTakeTable hw hd' hb hu hv ht))

def edgeRun (w d b n E A B edges p : List Bool) : List Bool :=
  runIndexed replaceBound edgeUpdate (mulU b (mulU b w)) p (pack [w,d,b,n,E,A,B,edges]) (tableInit w b)

lemma cpEdgeRun {w d b n E A B edges p : List Bool → List Bool} (hw : Lib.CPTs w) (hd' : Lib.CPTs d)
    (hb : Lib.CPTs b) (hn : Lib.CPTs n) (hE : Lib.CPTs E) (hA : Lib.CPTs A) (hB : Lib.CPTs B)
    (hedges : Lib.CPTs edges) (hp : Lib.CPTs p) : Lib.CPTs (fun s =>
      edgeRun (w s) (d s) (b s) (n s) (E s) (A s) (B s) (edges s) (p s)) := by
  apply cpRunIndexed replaceBound_cpt replaceBound_length cpEdgeUpdate (q42 hb (q42 hb hw)) hp _
    (cpTableInit hw hb)
  apply cpPack [w,d,b,n,E,A,B,edges]
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

lemma foldr_range_get {α β : Type*} (L : List α) (f : α → β → β) (z : β) :
    (List.range L.length).foldr (fun i a => if hi : i < L.length then f L[i] a else a) z = L.foldr f z := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    rw [dif_pos (Nat.zero_lt_succ _), List.getElem_cons_zero]
    congr 1
    rw [← ih]
    congr 1
    funext i a
    by_cases hi : i < L.length
    · simp [hi, Nat.succ_lt_succ hi]
    · have hni : ¬ i.succ < L.length.succ := fun h => hi (Nat.lt_of_succ_lt_succ h)
      simp [hi, hni]

lemma foldr_filter_apply {α β : Type*} (L : List α) (p : α → Bool) (f : α → β → β) (z : β) :
    L.foldr (fun i a => if p i then f i a else a) z = (L.filter p).foldr f z := by
  induction L with
  | nil => rfl
  | cons x L ih => cases hp : p x <;> simp [hp, ih]

lemma mask_bit {n : ℕ} (A : Finset (Edge n)) (i : ℕ) (hi : i < (pairs n).length) :
    bitFlagAt (un i) (mask A) = bflag (decide ((pairs n)[i] ∈ A)) := by
  rw [bitFlagAt_eq, un_length, List.getD_eq_getElem _ _ (by simpa [mask_length] using hi)]
  simp [mask]

lemma edgeRun_rep {n d : ℕ} (w b p : List Bool) (E A B : Finset (Edge n))
    (hb : b.length = 2^d) (hp : p.length = (pairs n).length) :
    tableRep w b (edgeRun w (un d) b (un n) (mask E) (mask A) (mask B) (pairWords (un n)) p)
      (extRun d ((pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B)))) := by
  let step (i : ℕ) (D : extTable d) := if hi : i < (pairs n).length then
    (if (pairs n)[i] ∈ E ∩ A ∩ B then extStep (pairs n)[i] D else D) else D
  have hfold : (List.range p.length).foldr step (extInit d) =
      extRun d ((pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B))) := by
    rw [hp]
    unfold step extRun
    exact (foldr_range_get (pairs n) (fun e D => if e ∈ E ∩ A ∩ B then extStep e D else D)
      (extInit d)).trans (by
        simpa using foldr_filter_apply (pairs n) (fun e => decide (e ∈ E ∩ A ∩ B)) extStep (extInit d))
  rw [← hfold]
  unfold edgeRun
  apply runIndexed_ofListFold _ _ _ _ _ _ (tableRep w b) step _ (tableInit_rep w b hb)
  intro i hi tab D hD
  have hix : i < (pairs n).length := hp ▸ hi
  have he := pairWords_get n i hix
  let e := (pairs n)[i]
  have hkeep : sel (bitFlagAt (un i) (mask E)) []
      (sel (bitFlagAt (un i) (mask A)) [] (bitFlagAt (un i) (mask B))) = bflag (decide (e ∈ E ∩ A ∩ B)) := by
    rw [mask_bit E i hix, mask_bit A i hix, mask_bit B i hix]
    change sel (bflag (decide (e ∈ E))) [] (sel (bflag (decide (e ∈ A))) [] (bflag (decide (e ∈ B)))) = _
    by_cases hE : e ∈ E <;> by_cases hA : e ∈ A <;> by_cases hB : e ∈ B <;>
      simp [sel, bflag, hE, hA, hB]
  simp only [edgeUpdate, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ, un_length,
    step, dif_pos hix, hkeep]
  rw [he.1,he.2]
  by_cases he' : (pairs n)[i] ∈ E ∩ A ∩ B
  · rw [if_pos he']
    simp only [show e ∈ E ∩ A ∩ B from he', decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
    have hs : tableRep w b (tablePlus w b tab (takeTable w (un d) b (un e.1.val) (un e.2.val) tab))
        (extStep e D) := tablePlus_rep w b _ _ hb hD (takeTable_rep w b tab e D hb hD)
    have hh : (tablePlus w b tab (takeTable w (un d) b (un e.1.val) (un e.2.val) tab)).length ≤
        (mulU b (mulU b w)).length := by rw [hs.1]; simp [mulU]
    change tableRep w b ((tablePlus w b tab (takeTable w (un d) b (un e.1.val) (un e.2.val) tab)).take
      (mulU b (mulU b w)).length) (extStep e D)
    rwa [List.take_of_length_le hh]
  · rw [if_neg he']
    simp only [show ¬ e ∈ E ∩ A ∩ B from he', decide_false, bflag, Bool.false_eq_true, sel, ↓reduceIte]
    have hh : tab.length ≤ (mulU b (mulU b w)).length := by rw [hD.1]; simp [mulU]
    change tableRep w b (tab.take (mulU b (mulU b w)).length) D
    rwa [List.take_of_length_le hh]

set_option maxHeartbeats 1000000 in
lemma common_top {n k : ℕ} (E A B : Finset (Edge n)) (hE : ∀ e ∈ E, e.1 < e.2) :
    extRun (2*k) ((pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B))) Finset.univ Finset.univ =
      (choices (E ∩ A ∩ B) k).sum (fun Q => (weight Q : ℤ)) := by
  let L := (pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B))
  have hsub : ∀ e ∈ E ∩ A ∩ B, e.1 < e.2 := by
    intro e he
    exact hE e (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).1
  have hL : L.toFinset = E ∩ A ∩ B := by
    ext e
    constructor
    · intro he
      exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2
    · intro he
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(pairs_mem e).mpr (hsub e he), decide_eq_true he⟩)
  classical
  have h := extRun_matching_of_toFinset k _ _ ((pairs_nodup n).filter _) hL hsub
  have hc : (E ∩ A ∩ B).powerset.filter (fun Q => Q.card = k ∧ extMatching Q) =
      choices (E ∩ A ∩ B) k := by
    ext Q
    simp only [choices, Finset.mem_filter]
    rfl
  rw [hc] at h
  exact h.trans (Finset.sum_congr rfl fun _ _ => rfl)

end Packed


namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal

def rowAt (p i data : List Bool) : List Bool := slot (true :: p) i data

lemma cpRowAt {p i data : List Bool → List Bool} (hp : Lib.CPTs p) (hi : Lib.CPTs i)
    (hd : Lib.CPTs data) : Lib.CPTs (fun x => rowAt (p x) (i x) (data x)) := cpSlot (cpCons true hp) hi hd

lemma rowAt_eq {n : ℕ} (p : List Bool) (rows : List (Row n)) (hp : p.length = (pairs n).length)
    (i : ℕ) (hi : i < rows.length) : rowAt p (un i) (rows.flatMap rowBits) = rowBits rows[i] := by
  apply slot_flatMap _ _ _ _ hi
  intro r _
  simp [rowBits, mask_length, hp]

def commonWord (w d b n E A B edges p : List Bool) : List Bool :=
  tableAt w b b.tail b.tail (edgeRun w d b n E A B edges p)

lemma cpCommonWord {w d b n E A B edges p : List Bool → List Bool} (hw : Lib.CPTs w) (hd : Lib.CPTs d)
    (hb : Lib.CPTs b) (hn : Lib.CPTs n) (hE : Lib.CPTs E) (hA : Lib.CPTs A) (hB : Lib.CPTs B)
    (hedges : Lib.CPTs edges) (hp : Lib.CPTs p) : Lib.CPTs (fun s =>
      commonWord (w s) (d s) (b s) (n s) (E s) (A s) (B s) (edges s) (p s)) :=
  cpTableAt hw hb (cpTail hb) (cpTail hb) (cpEdgeRun hw hd hb hn hE hA hB hedges hp)

lemma commonWord_rep {n k : ℕ} (w p : List Bool) (E A B : Finset (Edge n))
    (hE : ∀ e ∈ E, e.1 < e.2) (hp : p.length = (pairs n).length) :
    rep w (commonWord w (un (2*k)) (un (2^(2*k))) (un n) (mask E) (mask A) (mask B) (pairWords (un n)) p)
      ((choices (E ∩ A ∩ B) k).sum (fun Q => (weight Q : ℤ))) := by
  have h := (edgeRun_rep w (un (2^(2*k))) p E A B (by simp : (un (2^(2*k))).length = 2^(2*k)) hp).2
    Finset.univ Finset.univ
  rw [common_top E A B hE] at h
  simpa only [commonWord, maskIndex_univ, un, List.tail_replicate] using h

def rowPair (s : List Bool) : List Bool :=
  let i := left s
  let A := left (right s)
  let a := right (right s)
  let w := field 0 a
  let p := field 4 a
  let B := rowAt p i (field 8 a)
  signedWord w (xorF (q17 A) (q17 B))
    (commonWord w (field 1 a) (field 2 a) (field 3 a) (field 6 a) A.tail B.tail (field 7 a) p)

lemma cpRowPair : Lib.CPTs rowPair := by
  have ha := cpRight (cpRight cpt_id)
  have hA := cpLeft (cpRight cpt_id)
  have hp := cpField 4 ha
  have hw := cpField 0 ha
  have hB := cpRowAt hp (cpLeft cpt_id) (cpField 8 ha)
  exact cpSignedWord hw (q200 (cpt_comp hA q35) (cpt_comp hB q35))
    (cpCommonWord hw (cpField 1 ha) (cpField 2 ha) (cpField 3 ha) (cpField 6 ha) (cpTail hA)
      (cpTail hB) (cpField 7 ha) hp)

def rowSum (s : List Bool) : List Bool :=
  let a := right s
  let row := rowAt (field 4 a) (left s) (field 8 a)
  sumRange rowPair (field 0 a) (field 5 a) (pairB row a)

lemma cpRowSum : Lib.CPTs rowSum := by
  have ha := cpRight cpt_id
  exact cpSumRange cpRowPair (cpField 0 ha) (cpField 5 ha)
    (cpt_pairB2 (cpRowAt (cpField 4 ha) (cpLeft cpt_id) (cpField 8 ha)) ha)

def aggregate (a : List Bool) : List Bool := sumRange rowSum (field 0 a) (field 5 a) a

lemma cpAggregate : Lib.CPTs aggregate := cpSumRange cpRowSum (cpField 0 cpt_id) (cpField 5 cpt_id) cpt_id

def validArgs {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n)) : List Bool :=
  pack [w, un (2*k), un (2^(2*k)), un n, pairCount (un n), un rows.length, mask E, pairWords (un n), rows.flatMap rowBits]

lemma rowPair_rep {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n))
    (hE : ∀ e ∈ E, e.1 < e.2) (A : Row n) (j : ℕ) (hj : j < rows.length) :
    rep w (rowPair (pairB (un j) (pairB (rowBits A) (validArgs (k := k) w E rows))))
      (sign A.2 * sign rows[j].2 * (choices (E ∩ A.1 ∩ rows[j].1) k).sum (fun Q => (weight Q : ℤ))) := by
  simp only [rowPair, field_left_pair, field_right_pair, validArgs, field_pack_zero, field_pack_succ]
  rw [rowAt_eq _ rows (pairCount_length n) j hj]
  have h := commonWord_rep (k := k) w (pairCount (un n)) E A.1 rows[j].1 hE (pairCount_length n)
  cases hA : A.2 <;> cases hB : rows[j].2
  · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using h
  · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using rep_neg h
  · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using rep_neg h
  · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using h

lemma sum_range_list_get {α : Type*} (L : List α) (f : α → ℤ) :
    ((List.range L.length).map (fun i => if hi : i<L.length then f L[i] else 0)).sum = (L.map f).sum := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    rw [dif_pos (Nat.zero_lt_succ _), List.getElem_cons_zero, ← ih]
    congr 2
    apply List.map_congr_left
    intro i _
    by_cases hi : i < l.length
    · simp [hi, Nat.succ_lt_succ hi]
    · have hn : ¬ i.succ < l.length.succ := fun h => hi (Nat.lt_of_succ_lt_succ h)
      simp [hi, hn]

lemma rowSum_rep {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n))
    (hE : ∀ e ∈ E, e.1 < e.2) (i : ℕ) (hi : i < rows.length) :
    rep w (rowSum (pairB (un i) (validArgs (k := k) w E rows)))
      ((rows.map (fun r => sign rows[i].2 * sign r.2 *
        (choices (E ∩ rows[i].1 ∩ r.1) k).sum (fun Q => (weight Q : ℤ)))).sum) := by
  simp only [rowSum, field_left_pair, field_right_pair, validArgs, field_pack_zero, field_pack_succ]
  rw [rowAt_eq _ rows (pairCount_length n) i hi]
  let f (r : Row n) : ℤ := sign rows[i].2 * sign r.2 *
      (choices (E ∩ rows[i].1 ∩ r.1) k).sum (fun Q => (weight Q : ℤ))
  have hs := sumRange_rep rowPair w (un rows.length) (pairB (rowBits rows[i]) (validArgs (k := k) w E rows))
    (fun j => if hj : j < rows.length then f rows[j] else 0) (fun j hj => by
      rw [un_length] at hj
      simpa [hj, f] using rowPair_rep (k := k) w E rows hE rows[i] j hj)
  rw [un_length, sum_range_list_get] at hs
  exact hs

lemma aggregate_rep {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n))
    (hE : ∀ e ∈ E, e.1 < e.2) : rep w (aggregate (validArgs (k := k) w E rows)) (total E k rows : ℤ) := by
  simp only [aggregate, validArgs, field_pack_zero, field_pack_succ]
  let f (r : Row n) : ℤ := (rows.map (fun s => sign r.2 * sign s.2 *
        (choices (E ∩ r.1 ∩ s.1) k).sum (fun Q => (weight Q : ℤ)))).sum
  have hs := sumRange_rep rowSum w (un rows.length) (validArgs (k := k) w E rows)
    (fun j => if hj : j < rows.length then f rows[j] else 0) (fun j hj => by
      rw [un_length] at hj
      simpa [hj, f] using rowSum_rep (k := k) w E rows hE j hj)
  rw [un_length, sum_range_list_get] at hs
  rw [total_eq_row_pairs (k := k) E rows]
  exact hs

def widthCode (n m : List Bool) : List Bool :=
  let a := mulU n n
  a ++ mulU (n ++ n) a ++ m ++ m ++ [true]

lemma cpWidthCode {n m : List Bool → List Bool} (hn : Lib.CPTs n) (hm : Lib.CPTs m) :
    Lib.CPTs (fun s => widthCode (n s) (m s)) := by
  let ha := q42 hn hn
  exact cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 ha (q42 (cpt_app2 hn hn) ha)) hm) hm) (cpt_const [true])

lemma widthCode_length (n m : ℕ) : (widthCode (un n) (un m)).length = width n m := by
  simp [widthCode, width, mulU, two_mul, Nat.add_assoc, Nat.mul_assoc]

def inputArgs (s : List Bool) : List Bool :=
  let pad := hd s
  let input := dropN s
  let n := hd input
  let tail := dropN input
  let k := hd tail
  let d := k ++ k
  let b := powerTwo (mulU pad pad) d
  let afterK := dropN tail
  let p := pairCount n
  let E := afterK.take p.length
  let afterE := afterK.drop p.length
  let m := hd afterE
  pack [widthCode n m,d,b,n,p,m,E,pairWords n,dropN afterE]

set_option maxHeartbeats 1000000 in
lemma cpInputArgs : Lib.CPTs inputArgs := by
  have hpad := cpt_hd
  have hn := cpt_comp cpt_dropN cpt_hd
  have ht := cpt_comp cpt_dropN cpt_dropN
  have hk := cpt_comp ht cpt_hd
  have hd' := cpt_app2 hk hk
  have hb := powerTwo_cpt (q42 hpad hpad) hd'
  have ha := cpt_comp ht cpt_dropN
  have hp := cpPairCount hn
  have hE := cpTake hp ha
  have hbE := cpDrop hp ha
  have hm := cpt_comp hbE cpt_hd
  let nu := fun s => hd (dropN s)
  let tail := fun s => dropN (dropN s)
  let du := fun s => hd (tail s) ++ hd (tail s)
  let pu := fun s => pairCount (nu s)
  let ak := fun s => dropN (tail s)
  let ae := fun s => (ak s).drop (pu s).length
  let mu := fun s => hd (ae s)
  apply cpPack [fun s => widthCode (nu s) (mu s), du,
    fun s => powerTwo (mulU (hd s) (hd s)) (du s), nu, pu, mu,
    fun s => (ak s).take (pu s).length, fun s => pairWords (nu s), fun s => dropN (ae s)]
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cpWidthCode hn hm
  · exact hd'
  · exact hb
  · exact hn
  · exact hp
  · exact hm
  · exact hE
  · exact cpPairWords hn
  · exact cpt_comp hbE cpt_dropN

def encoded {n : ℕ} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) : List Bool :=
  header n ++ header k ++ mask E ++ header rows.length ++ rows.flatMap rowBits

lemma inputArgs_encoded {n : ℕ} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    inputArgs (un (2^(k+1)) ++ false :: encoded k E rows) =
      validArgs (k := k) (widthCode (un n) (un rows.length)) E rows := by
  have hd' : un k ++ un k = un (2*k) := by simp only [un, two_mul, List.replicate_add]
  have hb : 2^(un (2*k)).length ≤ (mulU (un (2^(k+1))) (un (2^(k+1)))).length := by
    simp only [un_length, mulU, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  simp only [inputArgs, encoded, header, List.append_assoc, List.cons_append,
    List.nil_append, hd_un_false, dropN_un_false, hd', validArgs, powerTwo_eq _ _ hb, un_length,
    pairCount_length, ← mask_length E, List.take_left, List.drop_append_length]

def normalizedOutput (b : List Bool) : List Bool := sel (q141 b) [false] (q141 b)

lemma cpNormalizedOutput : Lib.CPTs normalizedOutput := cpt_sel q167 (cpt_const [false]) q167

lemma normalizedOutput_eq (b : List Bool) : normalizedOutput b =
    (List.range ((val b).log2+1)).map (fun i => (val b).testBit i) := by
  unfold normalizedOutput
  rw [q109]
  by_cases h : val b = 0
  · simp [h, sel, Nat.bits]
  · have hp : 0 < val b := Nat.pos_iff_ne_zero.mpr h
    have hlen := q175 (val b) hp
    have hn : (val b).bits ≠ [] := fun hx => by rw [hx] at hlen; simp at hlen
    simp only [sel, hn, ↓reduceIte]
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi ho
      simp only [List.getElem_map, List.getElem_range, q78]
      rw [List.getD_eq_getElem _ _ hi]

def solve (s : List Bool) : List Bool := normalizedOutput (aggregate (inputArgs s))

set_option maxHeartbeats 1000000 in
lemma solve_cpt : Lib.CPTs solve := by
  have h : Lib.CPTs (fun s => aggregate (inputArgs s)) := cpt_comp cpInputArgs cpAggregate
  unfold solve
  exact cpt_comp h cpNormalizedOutput

lemma solve_encoded {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) (hE : ∀ e ∈ E, e.1 < e.2) :
    solve (un (2^(k+1)) ++ false :: encoded k E rows) =
      (List.range ((total E k rows).log2+1)).map (fun i => (total E k rows).testBit i) := by
  rw [solve, inputArgs_encoded, normalizedOutput_eq]
  let w := widthCode (un n) (un rows.length)
  have hv : val (aggregate (validArgs (k := k) w E rows)) = total E k rows := by
    apply val_eq_of_rep (w := w)
    · simp only [aggregate, sumRange_length, validArgs, field_pack_zero]
    · exact aggregate_rep w E rows hE
    · rw [show w.length = width n rows.length from widthCode_length n rows.length]
      exact total_lt (k := k) E rows
  rw [hv]

end Packed

end PEqualNP.Outside.L_lib_1018

theorem PEqualNP.Outside.L_lib_1018 :
  let header := fun z : Nat => List.replicate z true ++ [false]
  let pairs := fun n : Nat => (List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : Nat), (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ (n k : Nat) (E : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool)),
    (∀ e ∈ E, e.1 < e.2) →
    let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
    let choices := E.powerset.filter (fun Q => Q.card = k ∧
      ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f))
    let signed := fun Q : Finset (Fin n × Fin n) =>
      ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : Int) -
        ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : Int)
    let weight := fun Q : Finset (Fin n × Fin n) =>
      let V := Q.biUnion ends
      V.prod (fun i => (V.filter (fun j => i < j)).prod (fun j => (j.val-i.val)^2))
    let total := choices.sum (fun Q => weight Q * (signed Q).natAbs^2)
    let mask := fun A : Finset (Fin n × Fin n) => (pairs n).map (fun e => decide (e ∈ A))
    let x := header n ++ header k ++ mask E ++ header rows.length ++ rows.flatMap (fun t => t.2::mask t.1)
    let out := (List.range (total.log2+1)).map (fun i => total.testBit i)
    (0 < total ↔ ∃ Q ∈ choices, signed Q ≠ 0) ∧
    Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some (out.map M.outputAlphabet.invFun)) (2^(c*(k+1))*(x.length+2)^c)) := by
  intro header pairs
  obtain ⟨M,c,hfin,h⟩ := L_lib_1018.Padding.mr_fpt_second L_lib_1018.Packed.solve L_lib_1018.Packed.solve_cpt
  refine ⟨M,c,hfin,?_⟩
  intro n k E rows hE ends choices signed weight total mask x out
  refine ⟨L_lib_1018.total_pos E rows, ?_⟩
  let payload := mask E ++ header rows.length ++ rows.flatMap (fun t => t.2 :: mask t.1)
  have hx : (List.replicate n true ++ [false]) ++ (List.replicate k true ++ [false]) ++ payload = x := by
    simp only [payload, x, header, List.append_assoc]
  have hr := h n k payload
  dsimp only at hr
  rw [hx] at hr
  have ho : L_lib_1018.Packed.solve (List.replicate (2^(k+1)) true ++ false :: x) = out :=
    L_lib_1018.Packed.solve_encoded E rows hE
  rw [ho] at hr
  exact hr
