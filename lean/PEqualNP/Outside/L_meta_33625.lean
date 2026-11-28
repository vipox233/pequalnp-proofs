import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_33625
namespace aK
abbrev CPTs (f : List Bool -> List Bool) : Prop := PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f
end aK
section S1
namespace aK.Machines
open Turing
lemma iterate_none {σ : Type} (f : σ -> Option σ) (n : ℕ) :
   (flip bind f)^[n] none = none := by
 induction n with
 | zero => rfl
 | succ n ih => rw [Function.iterate_succ_apply]; exact ih
lemma simulate {σ τ : Type} (f : σ -> Option σ) (g : τ -> Option τ) (emb : σ -> τ)
   (h : ∀ c c',f c = some c' -> g (emb c) = some (emb c')) :
   ∀ (n : ℕ) (a b : σ),(flip bind f)^[n] (some a) = some b ->
     (flip bind g)^[n] (some (emb a)) = some (emb b) := by
 intro n
 induction n with
 | zero =>
   intro a b hab
   have : a = b := Option.some.inj hab
   rw [this]; rfl
 | succ n ih =>
   intro a b hab
   rw [Function.iterate_succ_apply] at hab ⊢
   cases hfa : f a with
   | none =>
     have e : flip bind f (some a) = none := hfa
     rw [e,iterate_none] at hab
     exact absurd hab (by simp)
   | some c =>
     have e : flip bind f (some a) = some c := hfa
     have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
     rw [e] at hab
     rw [e']
     exact ih c b hab
section pushes
variable {K : Type} [DecidableEq K] {Γ : K -> Type} {Λ σ : Type}
def pushes : TM2.Stmt Γ Λ σ -> ℕ
 | .push _ _ q => pushes q + 1
 | .peek _ _ q => pushes q
 | .pop _ _ q => pushes q
 | .load _ q => pushes q
 | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
 | .goto _ => 0
 | .halt => 0
lemma stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k)) (k : K) :
   ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
 induction q generalizing v S with
 | push k' f q ih =>
   simp only [TM2.stepAux,pushes]
   refine (ih _ _).trans ?_
   by_cases h : k = k'
   · subst h
     rw [Function.update_self,List.length_cons]; omega
   · rw [Function.update_of_ne h]; omega
 | peek k' f q ih => exact ih _ _
 | pop k' f q ih =>
   simp only [TM2.stepAux,pushes]
   refine (ih _ _).trans ?_
   by_cases h : k = k'
   · subst h
     rw [Function.update_self,List.length_tail]; omega
   · rw [Function.update_of_ne h]
 | load a q ih => exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
   simp only [TM2.stepAux,pushes]
   cases f v
   · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
   · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
 | goto f => simp [TM2.stepAux,pushes]
 | halt => simp [TM2.stepAux,pushes]
end pushes
noncomputable def maxPush (tm : FinTM2) : ℕ :=
 (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)
lemma step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
   (h : TM2.step tm.m c = some c') (k : tm.K) :
   (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
 obtain ⟨l,v,S⟩ := c
 cases l with
 | none => simp [TM2.step] at h
 | some l =>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   refine (stepAux_length _ _ _ _).trans ?_
   have : pushes (tm.m l) ≤ maxPush tm :=
     Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
   simpa using this
lemma run_length (tm : FinTM2) (k : tm.K) :
   ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
     (flip bind (TM2.step tm.m))^[n] (some a) = some b ->
     (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
 intro n
 induction n with
 | zero =>
   intro a b hab
   have : a = b := Option.some.inj hab
   rw [this]; simp
 | succ n ih =>
   intro a b hab
   rw [Function.iterate_succ_apply] at hab
   cases hfa : TM2.step tm.m a with
   | none =>
     have e : flip bind (TM2.step tm.m) (some a) = none := hfa
     rw [e,iterate_none] at hab
     exact absurd hab (by simp)
   | some c =>
     have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
     rw [e] at hab
     have h1 := ih c b hab
     have h2 := step_length tm a c hfa k
     rw [Nat.mul_succ]; omega
lemma initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
   initList tm s =
     (⟨some tm.main,tm.initialState,Function.update (fun _ => []) tm.k₀ s⟩ :
       TM2.Cfg tm.Γ tm.Λ tm.σ) := by
 unfold initList
 congr 1
 funext k
 by_cases h : k = tm.k₀
 · subst h; simp
 · simp [h]
lemma haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
   haltList tm s =
     (⟨none,tm.initialState,Function.update (fun _ => []) tm.k₁ s⟩ :
       TM2.Cfg tm.Γ tm.Λ tm.σ) := by
 unfold haltList
 congr 1
 funext k
 by_cases h : k = tm.k₁
 · subst h; simp
 · simp [h]
lemma eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
   rw [Polynomial.eval_add,Polynomial.eval_add]; exact add_le_add hp hq
 | monomial d c =>
   rw [Polynomial.eval_monomial,Polynomial.eval_monomial]
   exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end aK.Machines
end S1
section S2
namespace aK.Machines
open Turing
def pushList : List Bool -> TM2.Stmt (fun _ : Unit => Bool) Unit Bool
 | [] => .halt
 | a :: l => .push () (fun _ => a) (pushList l)
def constListProg (l : List Bool) : Unit -> TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
 fun _ => .pop () (fun _ o => o.isSome)
   (.branch (fun s => s)
     (.load (fun _ => false) (.goto fun _ => ()))
     (pushList l.reverse))
def constList (l : List Bool) : FinTM2 where
 K := Unit
 k₀ := ()
 k₁ := ()
 Γ _ := Bool
 Λ := Unit
 main := ()
 σ := Bool
 initialState := false
 m := constListProg l
abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool
lemma update_unit (S T : List Bool) :
   Function.update (fun _ : Unit => S) () T = fun _ => T := by
 funext k
 simp
lemma pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
   TM2.stepAux (pushList l) v (fun _ : Unit => S) =
     (⟨none,v,fun _ => l.reverse ++ S⟩ : CLCfg) := by
 induction l generalizing S with
 | nil => rfl
 | cons a l ih =>
   simp only [pushList,TM2.stepAux]
   rw [update_unit,ih]
   simp
lemma constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
   TM2.step (constListProg l) (⟨some (),false,fun _ => x :: a⟩ : CLCfg) =
     some ⟨some (),false,fun _ => a⟩ := by
 simp only [TM2.step,constListProg,TM2.stepAux]
 rw [update_unit]
 simp
lemma constList_nil (l : List Bool) :
   TM2.step (constListProg l) (⟨some (),false,fun _ => []⟩ : CLCfg) =
     some ⟨none,false,fun _ => l⟩ := by
 simp only [TM2.step,constListProg,TM2.stepAux]
 rw [update_unit]
 simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
 rw [pushList_stepAux]
 simp
lemma constList_loop (l : List Bool) (a : List Bool) :
   (flip bind (TM2.step (constListProg l)))^[a.length + 1]
       (some (⟨some (),false,fun _ => a⟩ : CLCfg)) =
     some ⟨none,false,fun _ => l⟩ := by
 induction a with
 | nil => exact constList_nil l
 | cons x a ih =>
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (constListProg l))
       (some (⟨some (),false,fun _ => x :: a⟩ : CLCfg)) =
       some ⟨some (),false,fun _ => a⟩ := constList_cons l x a
   rw [e,ih]
lemma constList_run (l : List Bool) (a : List Bool) :
   (flip bind (TM2.step (constListProg l)))^[a.length + 1]
       (some (initList (constList l) a)) = some (haltList (constList l) l) := by
 refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
   (some c)) (initList_eq (constList l) a)).trans
   (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
 show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
   (some (⟨some (),false,Function.update (fun _ => []) () a⟩ : CLCfg)) =
   some (⟨none,false,Function.update (fun _ => []) () l⟩ : CLCfg)
 rw [update_unit,update_unit]
 exact constList_loop l a
lemma constList_polyTime (l : List Bool) :
   Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) (fun _ : List Bool => l)) :=
 ⟨{
   tm := constList l
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := Polynomial.X + 1
   outputsFun := fun a =>
     { steps := a.length + 1
       evals_in_steps := by
         have hm : ∀ l : List Bool,List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
         exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
           (some (initList (constList l) x))) (hm a)).trans
           ((constList_run l a).trans
             (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
       steps_le_m := by simp } }⟩
end aK.Machines
end S2
section S3
namespace aK.Machines
open Turing
section update
variable {ι : Type} [DecidableEq ι] {β : ι -> Type}
lemma update3_fst (E : ∀ i,β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
   (x x' : β a) (y : β b) (z : β c) :
   Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
     Function.update (Function.update (Function.update E a x') b y) c z := by
 rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
lemma update3_snd (E : ∀ i,β i) {a b c : ι} (hbc : b ≠ c)
   (x : β a) (y y' : β b) (z : β c) :
   Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
     Function.update (Function.update (Function.update E a x) b y') c z := by
 rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2 : FinTM2)
abbrev CK : Type := Option (M1.K ⊕ M2.K)
abbrev CΓ : CK M1 M2 -> Type
 | none => M2.Γ M2.k₀
 | some (Sum.inl k) => M1.Γ k
 | some (Sum.inr k) => M2.Γ k
abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ -> TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
 | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o,s.2)) (tr1 q)
 | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o,s.2)) (tr1 q)
 | .load a q => .load (fun s => (a s.1,s.2)) (tr1 q)
 | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
 | .goto f => .goto (fun s => Sum.inl (f s.1))
 | .halt => .goto (fun _ => Sum.inr (Sum.inr false))
def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ -> TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
 | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .load a q => .load (fun s => (s.1,a s.2.1,s.2.2)) (tr2 q)
 | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
 | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
 | .halt => .halt
variable (M1 M2)
def tA (φ : M1.Γ M1.k₁ -> M2.Γ M2.k₀) :
   Option (M2.Γ M2.k₀) -> TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
 | some d =>
   .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1,s.2.1,o.map φ))
     (.branch (fun s => s.2.2.isSome)
       (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
       (.goto fun _ => Sum.inr (Sum.inr true)))
def tB : Option (M2.Γ M2.k₀) -> TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
 | some d =>
   .pop none (fun s o => (s.1,s.2.1,o))
     (.branch (fun s => s.2.2.isSome)
       (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
         (.goto fun _ => Sum.inr (Sum.inr true)))
       (.goto fun _ => Sum.inr (Sum.inl M2.main)))
def prog (φ : M1.Γ M1.k₁ -> M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
   CΛ M1 M2 -> TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | Sum.inl l => tr1 (M1.m l)
 | Sum.inr (Sum.inl l) => tr2 (M2.m l)
 | Sum.inr (Sum.inr false) => tA M1 M2 φ d
 | Sum.inr (Sum.inr true) => tB M1 M2 d
def comp (φ : M1.Γ M1.k₁ -> M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
 haveI := M1.kFin
 haveI := M2.kFin
 haveI := M1.ΛFin
 haveI := M2.ΛFin
 haveI := M1.σFin
 haveI := M2.σFin
 haveI := M2.Γk₀Fin
 { K := CK M1 M2
   k₀ := some (Sum.inl M1.k₀)
   k₁ := some (Sum.inr M2.k₁)
   Γ := CΓ M1 M2
   Λ := CΛ M1 M2
   main := Sum.inl M1.main
   σ := Cσ M1 M2
   initialState := (M1.initialState,M2.initialState,none)
   Γk₀Fin := M1.Γk₀Fin
   m := prog M1 M2 φ d }
variable {M1 M2}
def embStk1 (S : ∀ k,List (M1.Γ k)) : ∀ k,List (CΓ M1 M2 k)
 | none => []
 | some (Sum.inl k) => S k
 | some (Sum.inr _) => []
def embStk2 (S : ∀ k,List (M2.Γ k)) : ∀ k,List (CΓ M1 M2 k)
 | none => []
 | some (Sum.inl _) => []
 | some (Sum.inr k) => S k
lemma embStk1_update (S : ∀ k,List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
   (embStk1 (Function.update S k x) : ∀ k,List (CΓ M1 M2 k)) =
     Function.update (embStk1 S) (some (Sum.inl k)) x := by
 funext j
 rcases j with _ | j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · by_cases h : j = k
   · subst h
     rw [Function.update_self]
     show Function.update S j x j = x
     rw [Function.update_self]
   · rw [Function.update_of_ne (by simpa using h)]
     show Function.update S k x j = S j
     rw [Function.update_of_ne h]
 · rw [Function.update_of_ne (by simp)]; rfl
lemma embStk2_update (S : ∀ k,List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
   (embStk2 (Function.update S k x) : ∀ k,List (CΓ M1 M2 k)) =
     Function.update (embStk2 S) (some (Sum.inr k)) x := by
 funext j
 rcases j with _ | j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · rw [Function.update_of_ne (by simp)]; rfl
 · by_cases h : j = k
   · subst h
     rw [Function.update_self]
     show Function.update S j x j = x
     rw [Function.update_self]
   · rw [Function.update_of_ne (by simpa using h)]
     show Function.update S k x j = S j
     rw [Function.update_of_ne h]
lemma embStk1_nil :
   (embStk1 (fun _ => []) : ∀ k,List (CΓ M1 M2 k)) = fun _ => [] := by
 funext j; rcases j with _ | j | j <;> rfl
lemma embStk2_nil :
   (embStk2 (fun _ => []) : ∀ k,List (CΓ M1 M2 k)) = fun _ => [] := by
 funext j; rcases j with _ | j | j <;> rfl
def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
   TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
 ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl),(c.var,w),embStk1 c.stk⟩
def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
   TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
 ⟨c.l.map (fun l => Sum.inr (Sum.inl l)),(u,c.var,b),embStk2 c.stk⟩
lemma sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
   (S : ∀ k,List (M1.Γ k)) :
   TM2.stepAux (tr1 q) ((v,w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
 induction q generalizing v S with
 | push k f q ih =>
   have := ih v (Function.update S k (f v :: S k))
   rw [embStk1_update] at this
   exact this
 | peek k f q ih => exact ih _ _
 | pop k f q ih =>
   have := ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [embStk1_update] at this
   exact this
 | load a q ih => exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
   simp only [tr1,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f => rfl
 | halt => rfl
lemma sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
   (S : ∀ k,List (M2.Γ k)) :
   TM2.stepAux (tr2 q) ((u,v,b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
 induction q generalizing v S with
 | push k f q ih =>
   have := ih v (Function.update S k (f v :: S k))
   rw [embStk2_update] at this
   exact this
 | peek k f q ih => exact ih _ _
 | pop k f q ih =>
   have := ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [embStk2_update] at this
   exact this
 | load a q ih => exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
   simp only [tr2,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f => rfl
 | halt => rfl
variable (φ : M1.Γ M1.k₁ -> M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))
lemma step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
   (h : TM2.step M1.m c = some c') :
   TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
 obtain ⟨l,v,S⟩ := c
 cases l with
 | none => simp [TM2.step] at h
 | some l =>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (sim1 w (M1.m l) v S)
lemma step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
   (h : TM2.step M2.m c = some c') :
   TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
 obtain ⟨l,v,S⟩ := c
 cases l with
 | none => simp [TM2.step] at h
 | some l =>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (sim2 u b (M2.m l) v S)
def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k,List (CΓ M1 M2 k) :=
 Function.update (Function.update (Function.update (fun _ => [])
   (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
lemma st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
   (st l t u : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
 unfold st
 rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
lemma st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
   (st l t u : ∀ k,List (CΓ M1 M2 k)) none = t := by
 unfold st
 rw [Function.update_of_ne (by simp),Function.update_self]
lemma st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
   (st l t u : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
 unfold st
 rw [Function.update_self]
lemma st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
   Function.update (st l t u : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
 update3_fst _ (by simp) (by simp) _ _ _ _
lemma st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
   Function.update (st l t u : ∀ k,List (CΓ M1 M2 k)) none t' = st l t' u :=
 update3_snd _ (by simp) _ _ _ _
lemma st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
   Function.update (st l t u : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
 Function.update_idem _ _ _
lemma st_start (l : List (M1.Γ M1.k₁)) :
   (st l [] [] : ∀ k,List (CΓ M1 M2 k)) =
     Function.update (fun _ => [] : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
 unfold st
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [Function.update_of_ne (by simp)]
 · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
lemma st_end (u : List (M2.Γ M2.k₀)) :
   (st [] [] u : ∀ k,List (CΓ M1 M2 k)) =
     Function.update (fun _ => [] : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
 unfold st
 congr 1
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [Function.update_of_ne (by simp)]
end aK.Machines
end S3
section S4
namespace aK.Machines
open Turing
variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ -> M2.Γ M2.k₀)
abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
lemma stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
   (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
   TM2.step (prog M1 M2 φ (some dd))
       (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩ : CCfg M1 M2) =
     some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩ := by
 simp only [TM2.step,prog,tA,TM2.stepAux]
 rw [st_fst]
 simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
   Option.getD_some]
 rw [st_set_fst,st_snd,st_set_snd]
lemma stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
   (t u : List (M2.Γ M2.k₀)) :
   TM2.step (prog M1 M2 φ (some dd))
       (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st [] t u⟩ : CCfg M1 M2) =
     some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] t u⟩ := by
 simp only [TM2.step,prog,tA,TM2.stepAux]
 rw [st_fst]
 simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
 rw [st_set_fst]
lemma stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
   (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
   TM2.step (prog M1 M2 φ (some dd))
       (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩ : CCfg M1 M2) =
     some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩ := by
 simp only [TM2.step,prog,tB,TM2.stepAux]
 rw [st_snd]
 simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
 rw [st_set_snd,st_thd,st_set_thd]
lemma stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
   (u : List (M2.Γ M2.k₀)) :
   TM2.step (prog M1 M2 φ (some dd))
       (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] [] u⟩ : CCfg M1 M2) =
     some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] u⟩ := by
 simp only [TM2.step,prog,tB,TM2.stepAux]
 rw [st_snd]
 simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [st_set_snd]
lemma loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
   ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
     (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
         (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st l t u⟩ : CCfg M1 M2)) =
       some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] ((l.map φ).reverse ++ t) u⟩ := by
 intro l
 induction l with
 | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
 | cons x l ih =>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
       (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩ : CCfg M1 M2)) =
       some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩ :=
     stepA_cons φ dd v1 v2 b x l t u
   rw [e,ih]
   simp
lemma loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
   ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
     (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
         (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] t u⟩ : CCfg M1 M2)) =
       some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] (t.reverse ++ u)⟩ := by
 intro t
 induction t with
 | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
 | cons x t ih =>
   intro u b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
       (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩ : CCfg M1 M2)) =
       some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩ :=
     stepB_cons φ dd v1 v2 b x t u
   rw [e,ih]
   simp
lemma transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none -> IsEmpty (M2.Γ M2.k₀))
   (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
   ∃ n,n ≤ 2 * o.length + 2 /\
     (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
         (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,none),
           Function.update (fun _ => [] : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
           CCfg M1 M2)) =
       some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),
         Function.update (fun _ => [] : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
           (o.map φ)⟩ := by
 cases d with
 | none =>
   have := hd rfl
   have ho : o = [] := by
     cases o with
     | nil => rfl
     | cons x _ => exact (IsEmpty.false (φ x)).elim
   subst ho
   refine ⟨1,by omega,?_⟩
   show some _ = some _
   simp only [prog,tA,TM2.stepAux,List.map_nil]
   rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
 | some dd =>
   refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1),by simp; omega,?_⟩
   rw [Function.iterate_add_apply,← st_start,loopA,loopB,← st_end]
   simp
lemma emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
   emb1 (M2.initialState,none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
 rw [initList_eq]
 refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
 show (⟨_,_,embStk1 _⟩ : CCfg M1 M2) = _
 rw [embStk1_update,embStk1_nil]
 rfl
lemma emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
   emb1 w (haltList M1 o) =
     (⟨some (Sum.inr (Sum.inr false)),(M1.initialState,w),
       Function.update (fun _ => [] : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
       CCfg M1 M2) := by
 rw [haltList_eq]
 show (⟨_,_,embStk1 _⟩ : CCfg M1 M2) = _
 rw [embStk1_update,embStk1_nil]
 rfl
lemma emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
   emb2 u none (initList M2 i) =
     (⟨some (Sum.inr (Sum.inl M2.main)),(u,M2.initialState,none),
       Function.update (fun _ => [] : ∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
       CCfg M1 M2) := by
 rw [initList_eq]
 show (⟨_,_,embStk2 _⟩ : CCfg M1 M2) = _
 rw [embStk2_update,embStk2_nil]
 rfl
lemma emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
   emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
 rw [haltList_eq]
 refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
 show (⟨_,_,embStk2 _⟩ : CCfg M1 M2) = _
 rw [embStk2_update,embStk2_nil]
 rfl
lemma comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none -> IsEmpty (M2.Γ M2.k₀))
   (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
   (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
   (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
     some (haltList M2 o2)) :
   ∃ n,n ≤ s1 + (2 * o1.length + 2) + s2 /\ o1.length ≤ i.length + maxPush M1 * s1 /\
     (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
       some (haltList (comp M1 M2 φ d) o2) := by
 have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
   (emb1 (M2.initialState,none)) (step1 φ d _) s1 _ _ h1
 rw [emb1_init φ d,emb1_halt] at p1
 obtain ⟨nt,hnt,pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
 have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
   (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
 rw [emb2_init,emb2_halt φ d] at p2
 refine ⟨s2 + (nt + s1),by omega,?_,?_⟩
 · have := run_length M1 M1.k₁ s1 _ _ h1
   rw [haltList_eq,initList_eq] at this
   simp only [Function.update_self] at this
   refine this.trans (Nat.add_le_add_right ?_ _)
   by_cases h : M1.k₁ = M1.k₀
   · rw [h,Function.update_self]
   · rw [Function.update_of_ne h]; simp
 · rw [Function.iterate_add_apply,Function.iterate_add_apply,p1,pt,p2]
   rfl
lemma comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α -> List αΓ) (eb : β -> List βΓ)
   (ec : γ -> List γΓ) (f : α -> β) (g : β -> γ) (c1 : TM2ComputableInPolyTime ea eb f)
   (c2 : TM2ComputableInPolyTime eb ec g) :
   Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
 classical
 let φ : c1.tm.Γ c1.tm.k₁ -> c2.tm.Γ c2.tm.k₀ :=
   fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
 let d : Option (c2.tm.Γ c2.tm.k₀) :=
   if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
 have hd : d = none -> IsEmpty (c2.tm.Γ c2.tm.k₀) := by
   intro h
   by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
   · simp [d,hn] at h
   · exact not_nonempty_iff.mp hn
 let T : Polynomial ℕ :=
   c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
     Polynomial.C 2) +
     c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
 have key : ∀ a,∃ n,n ≤ T.eval (ea a).length /\
     (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
         (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
       some (haltList (comp c1.tm c2.tm φ d)
         (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
   intro a
   have r1 := c1.outputsFun a
   have r2 := c2.outputsFun (f a)
   have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
       List.map c2.inputAlphabet.invFun (eb (f a)) := by
     rw [List.map_map]
     refine List.map_congr_left fun y _ => ?_
     show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
     exact congrArg _ (c1.outputAlphabet.right_inv y)
   have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
       (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
       some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
     rw [hφ]; exact r2.evals_in_steps
   obtain ⟨n,hn,hlen,hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
   refine ⟨n,hn.trans ?_,hrun⟩
   have b1 := r1.steps_le_m
   have b2 := r2.steps_le_m
   simp only [List.length_map] at hlen
   have hmul : maxPush c1.tm * r1.steps ≤
       maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
   have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
       Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
         c2.time := eval_mono _ (by omega)
   simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
     Polynomial.eval_X,Polynomial.eval_comp,List.length_map]
   omega
 exact ⟨{
   tm := comp c1.tm c2.tm φ d
   inputAlphabet := c1.inputAlphabet
   outputAlphabet := c2.outputAlphabet
   time := T
   outputsFun := fun a =>
     ⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,
       (Classical.choose_spec (key a)).1⟩ }⟩
end aK.Machines
end S4
section S5
namespace aK.Machines
open Turing
variable {Γ₀ Γ₁ : Type}
abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool -> Type
 | some false => Γ₀
 | none => Option Γ₀
 | some true => Γ₁
def fmProg (φ : Γ₀ -> Option Γ₁) (d : Option Γ₁) : Bool -> TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
 | false =>
   .pop (some false) (fun _ o => o)
     (.branch (fun s => s.isSome)
       (.push none (fun s => s) (.goto fun _ => false))
       (.goto fun _ => true))
 | true =>
   .pop none (fun _ o => o.join)
     (.branch (fun s => s.isSome)
       (.branch (fun s => (s.bind φ).isSome)
         (match d with
           | some dd => .push (some true) (fun s => (s.bind φ).getD dd) (.goto fun _ => true)
           | none => .goto fun _ => true)
         (.goto fun _ => true))
       .halt)
def fm [Fintype Γ₀] (φ : Γ₀ -> Option Γ₁) (d : Option Γ₁) : FinTM2 where
 K := Option Bool
 k₀ := some false
 k₁ := some true
 Γ := FΓ Γ₀ Γ₁
 Λ := Bool
 main := false
 σ := Option Γ₀
 initialState := none
 Γk₀Fin := inferInstanceAs (Fintype Γ₀)
 m := fmProg φ d
def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k,List (FΓ Γ₀ Γ₁ k) :=
 Function.update (Function.update (Function.update (fun _ => [])
   (some false) l) none t) (some true) u
lemma fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
   fst3 l t u (some false) = l := by
 unfold fst3
 rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
lemma fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
   fst3 l t u none = t := by
 unfold fst3
 rw [Function.update_of_ne (by simp),Function.update_self]
lemma fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
   fst3 l t u (some true) = u := by
 unfold fst3
 rw [Function.update_self]
lemma fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
   Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
 update3_fst _ (by simp) (by simp) _ _ _ _
lemma fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
   Function.update (fst3 l t u) none t' = fst3 l t' u :=
 update3_snd _ (by simp) _ _ _ _
lemma fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
   Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
 Function.update_idem _ _ _
lemma fst3_start (l : List Γ₀) :
   (fst3 l [] [] : ∀ k,List (FΓ Γ₀ Γ₁ k)) =
     Function.update (fun _ => [] : ∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l := by
 unfold fst3
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [Function.update_of_ne (by simp)]
 · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
lemma fst3_end (u : List Γ₁) :
   (fst3 [] [] u : ∀ k,List (FΓ Γ₀ Γ₁ k)) =
     Function.update (fun _ => [] : ∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u := by
 unfold fst3
 congr 1
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [Function.update_of_ne (by simp)]
abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ : Γ₀ -> Option Γ₁) (d : Option Γ₁)
lemma fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (fmProg φ d) (⟨some false,b,fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
     some ⟨some false,some x,fst3 l (some x :: t) u⟩ := by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [fst3_fst]
 simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
 rw [fst3_set_fst,fst3_snd,fst3_set_snd]
lemma fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (fmProg φ d) (⟨some false,b,fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
     some ⟨some true,none,fst3 [] t u⟩ := by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [fst3_fst]
 simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [fst3_set_fst]
lemma fmB_cons (hd : d = none -> ∀ x,φ x = none) (b : Option Γ₀) (x : Γ₀)
   (t : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (fmProg φ d) (⟨some true,b,fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
     some ⟨some true,some x,fst3 [] t ((φ x).toList ++ u)⟩ := by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [fst3_snd]
 simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
   Bool.cond_true,Option.bind_some]
 rw [fst3_set_snd]
 cases hφ : φ x with
 | none => simp
 | some y =>
   cases d with
   | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
   | some dd =>
     simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,
       Option.toList_some,List.singleton_append]
     rw [fst3_thd,fst3_set_thd]
     simp [hφ]
lemma fmB_nil (b : Option Γ₀) (u : List Γ₁) :
   TM2.step (fmProg φ d) (⟨some true,b,fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
     some ⟨none,none,fst3 [] [] u⟩ := by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [fst3_snd]
 simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
   Bool.cond_false]
 rw [fst3_set_snd]
lemma fmLoopA (u : List Γ₁) :
   ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
     (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
         (some (⟨some false,b,fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
       some ⟨some true,none,fst3 [] (l.reverse.map some ++ t) u⟩ := by
 intro l
 induction l with
 | nil => intro t b; exact fmA_nil φ d b t u
 | cons x l ih =>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (fmProg φ d))
       (some (⟨some false,b,fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
       some ⟨some false,some x,fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
   rw [e,ih]
   simp
lemma fmLoopB (hd : d = none -> ∀ x,φ x = none) :
   ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
     (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
         (some (⟨some true,b,fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
       some ⟨none,none,fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
 intro t
 induction t with
 | nil => intro u b; exact fmB_nil φ d b u
 | cons x t ih =>
   intro u b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (fmProg φ d))
       (some (⟨some true,b,fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
       some ⟨some true,some x,fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
     fmB_cons φ d hd b x (t.map some) u
   rw [e,ih]
   cases hφ : φ x <;> simp [hφ]
lemma fm_run [Fintype Γ₀] (hd : d = none -> ∀ x,φ x = none) (l : List Γ₀) :
   (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
       (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
 refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
   (some c)) (initList_eq (fm φ d) l)).trans
   (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
 show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
   (some (⟨some false,none,Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
   some (⟨none,none,Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
 rw [Function.iterate_add_apply,← fst3_start,fmLoopA,← fst3_end]
 have := fmLoopB φ d hd l.reverse [] none
 rw [List.length_reverse] at this
 simpa [List.filterMap_reverse] using this
lemma filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α -> List αΓ)
   (eb : β -> List βΓ) (f : α -> β) (φ : αΓ -> Option βΓ)
   (h : ∀ a,eb (f a) = (ea a).filterMap φ) :
   Nonempty (TM2ComputableInPolyTime ea eb f) := by
 classical
 let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
 have hd : d = none -> ∀ x,φ x = none := by
   intro hdn x
   by_cases hn : Nonempty βΓ
   · simp [d,hn] at hdn
   · cases hφ : φ x with
     | none => rfl
     | some y => exact absurd ⟨y⟩ hn
 exact ⟨{
   tm := fm φ d
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
   outputsFun := fun a =>
     { steps := (ea a).length + 1 + ((ea a).length + 1)
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         have := fm_run φ d hd (ea a)
         exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
           ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
           (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
       steps_le_m := by
         simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
           Polynomial.eval_X]
         omega } }⟩
end aK.Machines
end S5
section S6
namespace aK.Machines
open Turing
abbrev TPK : Type := Fin 5
abbrev jV : TPK := 0
abbrev ni : TPK := 1
abbrev ng : TPK := 2
abbrev mY : TPK := 3
abbrev kY : TPK := 4
abbrev TPL : Type := Fin 4
abbrev km : TPL := 0
abbrev iR : TPL := 1
abbrev iG : TPL := 2
abbrev iP : TPL := 3
variable {Γ₀ Γ₁ : Type}
abbrev TPΓ (Γ₀ Γ₁ : Type) (k : TPK) : Type :=
 match k with
 | ⟨0,_⟩ => Γ₀
 | ⟨1,_⟩ => Option Γ₀
 | ⟨2,_⟩ => Option Γ₀
 | ⟨3,_⟩ => Option Γ₀
 | ⟨4,_⟩ => Γ₁
def tpWrite (φ : Γ₀ -> Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
   TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
 .branch (fun s => (s.bind φ).isSome)
   (match d with
     | some dd => .push kY (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
     | none => .goto fun _ => lbl)
   (.goto fun _ => lbl)
def tpProg (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁) (l : TPL) :
   TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
 match l with
 | ⟨0,_⟩ =>
   .pop jV (fun _ o => o)
     (.branch (fun s => s.isSome)
       (.push ni (fun s => s) (.goto fun _ => km))
       (.goto fun _ => iR))
 | ⟨1,_⟩ =>
   .pop ni (fun _ o => o.join)
     (.branch (fun s => s.isSome)
       (.push ng (fun s => s) (tpWrite φ₂ d iR))
       (.goto fun _ => iG))
 | ⟨2,_⟩ =>
   .pop ng (fun _ o => o.join)
     (.branch (fun s => s.isSome)
       (.push mY (fun s => s) (.goto fun _ => iG))
       (.goto fun _ => iP))
 | ⟨3,_⟩ =>
   .pop mY (fun _ o => o.join)
     (.branch (fun s => s.isSome)
       (tpWrite φ₁ d iP)
       .halt)
@[simp] lemma yl (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁) :
   tpProg φ₁ φ₂ d km =
     .pop jV (fun _ o => o) (.branch (fun s => s.isSome) (.push ni (fun s => s) (.goto fun _ => km)) (.goto fun _ => iR)) := rfl
@[simp] lemma yS (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁) :
   tpProg φ₁ φ₂ d iR =
     .pop ni (fun _ o => o.join) (.branch (fun s => s.isSome) (.push ng (fun s => s) (tpWrite φ₂ d iR)) (.goto fun _ => iG)) := rfl
@[simp] lemma yo (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁) :
   tpProg φ₁ φ₂ d iG =
     .pop ng (fun _ o => o.join) (.branch (fun s => s.isSome) (.push mY (fun s => s) (.goto fun _ => iG)) (.goto fun _ => iP)) := rfl
@[simp] lemma yb (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁) :
   tpProg φ₁ φ₂ d iP =
     .pop mY (fun _ o => o.join) (.branch (fun s => s.isSome) (tpWrite φ₁ d iP) .halt) := rfl
def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁) : FinTM2 where
 K := TPK
 k₀ := jV
 k₁ := kY
 Γ := TPΓ Γ₀ Γ₁
 Λ := TPL
 main := km
 σ := Option Γ₀
 initialState := none
 Γk₀Fin := inferInstanceAs (Fintype Γ₀)
 m := tpProg φ₁ φ₂ d
def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) (k : TPK) : List (TPΓ Γ₀ Γ₁ k) :=
 match k with
 | ⟨0,_⟩ => l
 | ⟨1,_⟩ => a
 | ⟨2,_⟩ => b
 | ⟨3,_⟩ => c
 | ⟨4,_⟩ => u
@[simp] lemma y8 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : st5 l a b c u jV = l := rfl
@[simp] lemma Ag (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : st5 l a b c u ni = a := rfl
@[simp] lemma zG (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : st5 l a b c u ng = b := rfl
@[simp] lemma zv (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : st5 l a b c u mY = c := rfl
@[simp] lemma zl (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : st5 l a b c u kY = u := rfl
lemma st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
   Function.update (st5 l a b c u) jV l' = st5 l' a b c u := by
 funext k; fin_cases k <;> rfl
lemma st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
   Function.update (st5 l a b c u) ni a' = st5 l a' b c u := by
 funext k; fin_cases k <;> rfl
lemma st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
   Function.update (st5 l a b c u) ng b' = st5 l a b' c u := by
 funext k; fin_cases k <;> rfl
lemma st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
   Function.update (st5 l a b c u) mY c' = st5 l a b c' u := by
 funext k; fin_cases k <;> rfl
lemma st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
   Function.update (st5 l a b c u) kY u' = st5 l a b c u' := by
 funext k; fin_cases k <;> rfl
lemma st5_start (l : List Γ₀) :
   (st5 l [] [] [] [] : ∀ k,List (TPΓ Γ₀ Γ₁ k)) =
     Function.update (fun _ => [] : ∀ k,List (TPΓ Γ₀ Γ₁ k)) jV l := by
 funext k; fin_cases k <;> rfl
lemma st5_end (u : List Γ₁) :
   (st5 [] [] [] [] u : ∀ k,List (TPΓ Γ₀ Γ₁ k)) =
     Function.update (fun _ => [] : ∀ k,List (TPΓ Γ₀ Γ₁ k)) kY u := by
 funext k; fin_cases k <;> rfl
abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂ : Γ₀ -> Option Γ₁) (d : Option Γ₁)
lemma tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
   (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some km,s,st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some km,some x,st5 l (some x :: a) b c u⟩ := by
 simp [TM2.step,tpProg,TM2.stepAux,st5,st5_set_inp,st5_set_t1]
lemma tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some km,s,st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some iR,none,st5 [] a b c u⟩ := by
 simp [TM2.step,tpProg,TM2.stepAux,st5,st5_set_inp]
lemma tpB_cons (hd : d = none -> ∀ x,φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
   (a b c : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some iR,s,st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some iR,some x,st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
 cases hφ : φ₂ x with
 | none =>
   cases d <;>
     simp [TM2.step,tpProg,tpWrite,TM2.stepAux,st5,st5_set_t1,st5_set_t2,hφ]
 | some y =>
   cases d with
   | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
   | some dd =>
     simp [TM2.step,tpProg,tpWrite,TM2.stepAux,st5,st5_set_t1,st5_set_t2,
       st5_set_out,hφ]
lemma tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some iR,s,st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some iG,none,st5 [] [] b c u⟩ := by
 simp [TM2.step,tpProg,TM2.stepAux,st5,st5_set_t1]
lemma tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some iG,s,st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some iG,some x,st5 [] [] b (some x :: c) u⟩ := by
 simp [TM2.step,tpProg,TM2.stepAux,st5,st5_set_t2,st5_set_t3]
lemma tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some iG,s,st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some iP,none,st5 [] [] [] c u⟩ := by
 simp [TM2.step,tpProg,TM2.stepAux,st5,st5_set_t2]
lemma tpE_cons (hd : d = none -> ∀ x,φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
   (c : List (Option Γ₀)) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some iP,s,st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨some iP,some x,st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
 cases hφ : φ₁ x with
 | none =>
   cases d <;>
     simp [TM2.step,tpProg,tpWrite,TM2.stepAux,st5,st5_set_t3,hφ]
 | some y =>
   cases d with
   | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
   | some dd =>
     simp [TM2.step,tpProg,tpWrite,TM2.stepAux,st5,st5_set_t3,st5_set_out,hφ]
lemma tpE_nil (s : Option Γ₀) (u : List Γ₁) :
   TM2.step (tpProg φ₁ φ₂ d) (⟨some iP,s,st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
     some ⟨none,none,st5 [] [] [] [] u⟩ := by
 simp [TM2.step,tpProg,TM2.stepAux,st5,st5_set_t3]
lemma tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
   ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
     (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
         (some (⟨some km,s,st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some iR,none,st5 [] (l.reverse.map some ++ a) b c u⟩ := by
 intro l
 induction l with
 | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
 | cons x l ih =>
   intro a s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
       (some (⟨some km,s,st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some km,some x,st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
   rw [e,ih]
   simp
lemma tpLoopB (hd : d = none -> ∀ x,φ₂ x = none) (c : List (Option Γ₀)) :
   ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
     (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
         (some (⟨some iR,s,st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some iG,none,
         st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
 intro t
 induction t with
 | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
 | cons x t ih =>
   intro b u s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
       (some (⟨some iR,s,st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some iR,some x,st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
     tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
   rw [e,ih]
   cases hφ : φ₂ x <;> simp [hφ]
lemma tpLoopC (u : List Γ₁) :
   ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
     (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
         (some (⟨some iG,s,st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some iP,none,st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
 intro t
 induction t with
 | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
 | cons x t ih =>
   intro c s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
       (some (⟨some iG,s,st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some iG,some x,st5 [] [] (t.map some) (some x :: c) u⟩ :=
     tpC_cons φ₁ φ₂ d s x (t.map some) c u
   rw [e,ih]
   simp
lemma tpLoopE (hd : d = none -> ∀ x,φ₁ x = none) :
   ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
     (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
         (some (⟨some iP,s,st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
 intro t
 induction t with
 | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
 | cons x t ih =>
   intro u s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
       (some (⟨some iP,s,st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
       some ⟨some iP,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
     tpE_cons φ₁ φ₂ d hd s x (t.map some) u
   rw [e,ih]
   cases hφ : φ₁ x <;> simp [hφ]
lemma tp_run [Fintype Γ₀] (hd₁ : d = none -> ∀ x,φ₁ x = none)
   (hd₂ : d = none -> ∀ x,φ₂ x = none) (l : List Γ₀) :
   (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
       (l.length + 1)]
       (some (initList (tp φ₁ φ₂ d) l)) =
     some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)) := by
 refine (congrArg (fun c => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 +
   (l.length + 1) + (l.length + 1) + (l.length + 1)]
   (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
   (Eq.trans ?_ (congrArg some
     (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
 show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
     (l.length + 1)]
   (some (⟨some km,none,Function.update (fun _ => []) jV l⟩ : TPCfg Γ₀ Γ₁)) =
   some (⟨none,none,Function.update (fun _ => []) kY
     (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
 have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
     (some (⟨some km,none,st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
     some ⟨some iR,none,st5 [] (l.reverse.map some) [] [] []⟩ := by
   simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
 have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
     (some (⟨some iR,none,st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
     some ⟨some iG,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
   have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
   rw [List.length_reverse] at this
   simpa [List.filterMap_reverse] using this
 have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
     (some (⟨some iG,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
     some ⟨some iP,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
   simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
 have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
     (some (⟨some iP,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
       TPCfg Γ₀ Γ₁)) =
     some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
   have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
   rw [List.length_reverse] at this
   simpa [List.filterMap_reverse] using this
 rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
   ← st5_start,hA,hB,hC,hE,st5_end]
lemma twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α -> List αΓ)
   (eb : β -> List βΓ) (f : α -> β) (φ₁ φ₂ : αΓ -> Option βΓ)
   (h : ∀ a,eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
   Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
 classical
 let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
 have hd : ∀ φ : αΓ -> Option βΓ,d = none -> ∀ x,φ x = none := by
   intro φ hdn x
   by_cases hn : Nonempty βΓ
   · simp [d,hn] at hdn
   · cases hφ : φ x with
     | none => rfl
     | some y => exact absurd ⟨y⟩ hn
 exact ⟨{
   tm := tp φ₁ φ₂ d
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
   outputsFun := fun a =>
     { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
         ((ea a).length + 1)
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
         exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
           ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
           (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
           (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
             ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
       steps_le_m := by
         simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
           Polynomial.eval_X]
         omega } }⟩
end aK.Machines
end S6
section S7
namespace aK.Machines
open Turing
abbrev FX : Type := Fin 4
abbrev n9 : FX := 0
abbrev pC : FX := 1
abbrev mL : FX := 2
abbrev ny : FX := 3
abbrev FL : Type := Fin 5
abbrev ju : FL := 0
abbrev kn : FL := 1
abbrev kU : FL := 2
abbrev ki : FL := 3
abbrev kj : FL := 4
variable (M : FinTM2)
abbrev FstΓ : M.K ⊕ FX -> Type
 | Sum.inl k => M.Γ k
 | Sum.inr ⟨0,_⟩ => Bool ⊕ Bool
 | Sum.inr ⟨1,_⟩ => Bool
 | Sum.inr ⟨2,_⟩ => Bool
 | Sum.inr ⟨3,_⟩ => Bool ⊕ Bool
abbrev FstΛ : Type := M.Λ ⊕ FL
abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)
def bit : Option (Bool ⊕ Bool) -> Bool
 | none => false
 | some (Sum.inl b) => b
 | some (Sum.inr b) => b
def isFst : Option (Bool ⊕ Bool) -> Bool
 | some (Sum.inl _) => true
 | _ => false
variable {M}
def trF : TM2.Stmt M.Γ M.Λ M.σ -> TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
 | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
 | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o,s.2)) (trF q)
 | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o,s.2)) (trF q)
 | .load a q => .load (fun s => (a s.1,s.2)) (trF q)
 | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
 | .goto f => .goto (fun s => Sum.inl (f s.1))
 | .halt => .goto (fun _ => Sum.inr kU)
variable (M)
def firstProg (e₀ : Bool -> M.Γ M.k₀) (e₁ : M.Γ M.k₁ -> Bool) :
   FstΛ M -> TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
 | Sum.inl l => trF (M.m l)
 | Sum.inr ⟨0,_⟩ =>
   .pop (Sum.inr n9) (fun s o => (s.1,o))
     (.branch (fun s => s.2.isSome)
       (.branch (fun s => isFst s.2)
         (.push (Sum.inr mL) (fun s => bit s.2) (.goto fun _ => Sum.inr ju))
         (.push (Sum.inr pC) (fun s => bit s.2) (.goto fun _ => Sum.inr ju)))
       (.goto fun _ => Sum.inr kn))
 | Sum.inr ⟨1,_⟩ =>
   .pop (Sum.inr mL) (fun s o => (s.1,o.map Sum.inl))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr kn))
       (.goto fun _ => Sum.inl M.main))
 | Sum.inr ⟨2,_⟩ =>
   .pop (Sum.inr pC) (fun s o => (s.1,o.map Sum.inl))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inr ny) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr kU))
       (.goto fun _ => Sum.inr ki))
 | Sum.inr ⟨3,_⟩ =>
   .pop (Sum.inl M.k₁) (fun s o => (s.1,o.map fun y => Sum.inl (e₁ y)))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inr mL) (fun s => bit s.2) (.goto fun _ => Sum.inr ki))
       (.goto fun _ => Sum.inr kj))
 | Sum.inr ⟨4,_⟩ =>
   .pop (Sum.inr mL) (fun s o => (s.1,o.map Sum.inl))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inr ny) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr kj))
       .halt)
def firstM (e₀ : Bool -> M.Γ M.k₀) (e₁ : M.Γ M.k₁ -> Bool) : FinTM2 :=
 haveI := M.kFin
 haveI := M.ΛFin
 haveI := M.σFin
 { K := M.K ⊕ FX
   k₀ := Sum.inr n9
   k₁ := Sum.inr ny
   Γ := FstΓ M
   Λ := FstΛ M
   main := Sum.inr ju
   σ := Fstσ M
   initialState := (M.initialState,none)
   Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
   m := firstProg M e₀ e₁ }
variable {M}
def fstk (S : ∀ k,List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
   (o : List (Bool ⊕ Bool)) : ∀ k,List (FstΓ M k)
 | Sum.inl k => S k
 | Sum.inr ⟨0,_⟩ => i
 | Sum.inr ⟨1,_⟩ => w
 | Sum.inr ⟨2,_⟩ => t
 | Sum.inr ⟨3,_⟩ => o
section fstk
variable (S : ∀ k,List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
 (o : List (Bool ⊕ Bool))
lemma fstk_set_M (k : M.K) (x : List (M.Γ k)) :
   Function.update (fstk S i w t o) (Sum.inl k) x = fstk (Function.update S k x) i w t o := by
 funext j
 rcases j with j | j
 · by_cases h : j = k
   · subst h
     rw [Function.update_self]
     show x = Function.update S j x j
     rw [Function.update_self]
   · rw [Function.update_of_ne (by simpa using h)]
     show S j = Function.update S k x j
     rw [Function.update_of_ne h]
 · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl
lemma fstk_set_I (i' : List (Bool ⊕ Bool)) :
   Function.update (fstk S i w t o) (Sum.inr n9) i' = fstk S i' w t o := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,n9] <;> rfl
lemma fstk_set_W (w' : List Bool) :
   Function.update (fstk S i w t o) (Sum.inr pC) w' = fstk S i w' t o := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,pC] <;> rfl
lemma fstk_set_T (t' : List Bool) :
   Function.update (fstk S i w t o) (Sum.inr mL) t' = fstk S i w t' o := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,mL] <;> rfl
lemma fstk_set_O (o' : List (Bool ⊕ Bool)) :
   Function.update (fstk S i w t o) (Sum.inr ny) o' = fstk S i w t o' := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,ny] <;> rfl
end fstk
abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)
def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
   (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
 ⟨some (c.l.elim (Sum.inr kU) Sum.inl),(c.var,b),fstk c.stk i w t o⟩
lemma simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
   (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k,List (M.Γ k)) :
   TM2.stepAux (trF q) ((v,b) : Fstσ M) (fstk S i w t o) =
     embF b i w t o (TM2.stepAux q v S) := by
 induction q generalizing v S with
 | push k f q ih =>
   have := ih v (Function.update S k (f v :: S k))
   rw [← fstk_set_M] at this
   exact this
 | peek k f q ih => exact ih _ _
 | pop k f q ih =>
   have := ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [← fstk_set_M] at this
   exact this
 | load a q ih => exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
   simp only [trF,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f => rfl
 | halt => rfl
lemma stepF (e₀ : Bool -> M.Γ M.k₀) (e₁ : M.Γ M.k₁ -> Bool) (b : Option (Bool ⊕ Bool))
   (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
   (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
   TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
 obtain ⟨l,v,S⟩ := c
 cases l with
 | none => simp [TM2.step] at h
 | some l =>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (simF b i w t o (M.m l) v S)
end aK.Machines
end S7
section S8
namespace aK.Machines
open Turing
lemma iter_trans {σ : Type} (f : σ -> Option σ) {a b : ℕ} {x y z : σ}
   (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
   (flip bind f)^[b + a] (some x) = some z := by
 rw [Function.iterate_add_apply,h₁,h₂]
variable {M : FinTM2} (e₀ : Bool -> M.Γ M.k₀) (e₁ : M.Γ M.k₁ -> Bool)
section fstk
variable (S : ∀ k,List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
 (o : List (Bool ⊕ Bool))
@[simp] lemma fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] lemma fstk_I : fstk S i w t o (Sum.inr n9) = i := rfl
@[simp] lemma fstk_W : fstk S i w t o (Sum.inr pC) = w := rfl
@[simp] lemma fstk_T : fstk S i w t o (Sum.inr mL) = t := rfl
@[simp] lemma fstk_O : fstk S i w t o (Sum.inr ny) = o := rfl
end fstk
variable (v : M.σ) (S : ∀ k,List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))
lemma f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr ju),(v,b),fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr ju),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_I,fstk_set_T,isFst,bit,Function.update,n9,pC,mL,ny]
lemma f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr ju),(v,b),fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr ju),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_I,fstk_set_W,isFst,bit,Function.update,n9,pC,mL,ny]
lemma f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr ju),(v,b),fstk S [] w t o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr kn),(v,none),fstk S [] w t o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_I]
lemma loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
   (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
       (some (⟨some (Sum.inr ju),(v,b),fstk S i w t o⟩ : FCfg1 M)) =
     some ⟨some (Sum.inr kn),(v,none),
       fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
         ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
 intro i
 induction i with
 | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
 | cons x i ih =>
   intro w t b
   rw [List.length_cons,Function.iterate_succ_apply]
   cases x with
   | inl a =>
     have e : flip bind (TM2.step (firstProg M e₀ e₁))
         (some (⟨some (Sum.inr ju),(v,b),fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
         some ⟨some (Sum.inr ju),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩ :=
       f1_inl e₀ e₁ v S w o b a i t
     rw [e,ih]; simp [List.filterMap_cons]
   | inr a =>
     have e : flip bind (TM2.step (firstProg M e₀ e₁))
         (some (⟨some (Sum.inr ju),(v,b),fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
         some ⟨some (Sum.inr ju),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩ :=
       f1_inr e₀ e₁ v S w o b a i t
     rw [e,ih]; simp [List.filterMap_cons]
lemma f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr kn),(v,b),fstk S [] w (a :: t) o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr kn),(v,some (Sum.inl a)),
       fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_T,fstk_set_M,bit,Function.update,n9,pC,mL,ny]
lemma f2_nil (b : Option (Bool ⊕ Bool)) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr kn),(v,b),fstk S [] w [] o⟩ : FCfg1 M) =
     some ⟨some (Sum.inl M.main),(v,none),fstk S [] w [] o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_T]
lemma loop2 : ∀ (t : List Bool) (S : ∀ k,List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
   (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
       (some (⟨some (Sum.inr kn),(v,b),fstk S [] w t o⟩ : FCfg1 M)) =
     some ⟨some (Sum.inl M.main),(v,none),
       fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩ := by
 intro t
 induction t with
 | nil =>
   intro S b
   have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
   rw [this]
   exact f2_nil e₀ e₁ v S w o b
 | cons a t ih =>
   intro S b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (firstProg M e₀ e₁))
       (some (⟨some (Sum.inr kn),(v,b),fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
       some ⟨some (Sum.inr kn),(v,some (Sum.inl a)),
         fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
   rw [e,ih]; simp
lemma f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr kU),(v,b),fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr kU),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_W,fstk_set_O,bit,Function.update,n9,pC,mL,ny]
lemma f3_nil (b : Option (Bool ⊕ Bool)) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr kU),(v,b),fstk S [] [] [] o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr ki),(v,none),fstk S [] [] [] o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_W]
lemma loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
   (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
       (some (⟨some (Sum.inr kU),(v,b),fstk S [] w [] o⟩ : FCfg1 M)) =
     some ⟨some (Sum.inr ki),(v,none),fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
 intro w
 induction w with
 | nil => intro o b; exact f3_nil e₀ e₁ v S o b
 | cons a w ih =>
   intro o b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (firstProg M e₀ e₁))
       (some (⟨some (Sum.inr kU),(v,b),fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
       some ⟨some (Sum.inr kU),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩ :=
     f3_cons e₀ e₁ v S o b a w
   rw [e,ih]; simp
lemma f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr ki),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
         FCfg1 M) =
     some ⟨some (Sum.inr ki),(v,some (Sum.inl (e₁ y))),
       fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_T,fstk_set_M,bit,Function.update,n9,pC,mL,ny]
lemma f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr ki),(v,b),fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr kj),(v,none),fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_M]
lemma loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
   (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
       (some (⟨some (Sum.inr ki),(v,b),fstk (Function.update S M.k₁ m) [] [] t o⟩ :
         FCfg1 M)) =
     some ⟨some (Sum.inr kj),(v,none),
       fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
 intro m
 induction m with
 | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
 | cons y m ih =>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (firstProg M e₀ e₁))
       (some (⟨some (Sum.inr ki),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
         FCfg1 M)) =
       some ⟨some (Sum.inr ki),(v,some (Sum.inl (e₁ y))),
         fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
   rw [e,ih]; simp
lemma f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr kj),(v,b),fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
     some ⟨some (Sum.inr kj),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_T,fstk_set_O,bit,Function.update,n9,pC,mL,ny]
lemma f5_nil (b : Option (Bool ⊕ Bool)) :
   TM2.step (firstProg M e₀ e₁)
       (⟨some (Sum.inr kj),(v,b),fstk S [] [] [] o⟩ : FCfg1 M) =
     some ⟨none,(v,none),fstk S [] [] [] o⟩ := by
 simp [TM2.step,firstProg,TM2.stepAux,fstk_set_T]
lemma loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
   (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
       (some (⟨some (Sum.inr kj),(v,b),fstk S [] [] t o⟩ : FCfg1 M)) =
     some ⟨none,(v,none),fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
 intro t
 induction t with
 | nil => intro o b; exact f5_nil e₀ e₁ v S o b
 | cons a t ih =>
   intro o b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (firstProg M e₀ e₁))
       (some (⟨some (Sum.inr kj),(v,b),fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
       some ⟨some (Sum.inr kj),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩ :=
     f5_cons e₀ e₁ v S o b a t
   rw [e,ih]; simp
end aK.Machines
end S8
section S9
namespace aK.Machines
open Turing PEqualNP.Library
variable {M : FinTM2} (e₀ : Bool -> M.Γ M.k₀) (e₁ : M.Γ M.k₁ -> Bool)
lemma fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k,List (FstΓ M k)) = fun _ => [] := by
 funext j; rcases j with j | j <;> [rfl; fin_cases j <;> rfl]
lemma fstk_nil_I (i : List (Bool ⊕ Bool)) :
   (fstk (fun _ => []) i [] [] [] : ∀ k,List (FstΓ M k)) =
     Function.update (fun _ => [] : ∀ k,List (FstΓ M k)) (Sum.inr n9) i :=
 (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])
lemma fstk_nil_O (o : List (Bool ⊕ Bool)) :
   (fstk (fun _ => []) [] [] [] o : ∀ k,List (FstΓ M k)) =
     Function.update (fun _ => [] : ∀ k,List (FstΓ M k)) (Sum.inr ny) o :=
 (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])
lemma embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
   (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
   embF b i w t o (initList M l) =
     (⟨some (Sum.inl M.main),(M.initialState,b),
       fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
 rw [initList_eq]; rfl
lemma embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
   (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
   embF b i w t o (haltList M m) =
     (⟨some (Sum.inr kU),(M.initialState,b),
       fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
 rw [haltList_eq]; rfl
lemma filterMap_const_none {γ δ : Type} (l : List γ) :
   l.filterMap (fun _ => (none : Option δ)) = [] := by
 induction l with
 | nil => rfl
 | cons a l ih => simp
lemma encodePair_left (x w : List Bool) :
   (encodePair (x,w)).filterMap Sum.getLeft? = x := by
 have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool -> Bool ⊕ Bool) : Bool -> Option Bool) = some := rfl
 have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool -> Bool ⊕ Bool) : Bool -> Option Bool) = fun _ => none := rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
   List.filterMap_some,filterMap_const_none,List.append_nil]
lemma encodePair_right (x w : List Bool) :
   (encodePair (x,w)).filterMap Sum.getRight? = w := by
 have h1 : (Sum.getRight? ∘ (Sum.inl : Bool -> Bool ⊕ Bool) : Bool -> Option Bool) = fun _ => none := rfl
 have h2 : (Sum.getRight? ∘ (Sum.inr : Bool -> Bool ⊕ Bool) : Bool -> Option Bool) = some := rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
   List.filterMap_some,filterMap_const_none,List.nil_append]
lemma encodePair_length (x w : List Bool) :
   (encodePair (x,w)).length = x.length + w.length := by
 simp [encodePair]
lemma first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
   (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
   ∃ n,n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 /\
     (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
         (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
       some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))) := by
 have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x,w0)).length + 1]
     (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
     some (⟨some (Sum.inr kn),(M.initialState,none),
       fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
   have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x,w0)) [] [] none
   rw [encodePair_left,encodePair_right,List.append_nil,List.append_nil,fstk_nil_I] at this
   exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
     (encodePair (x,w0)).length + 1] (some c))
     (initList_eq (firstM M e₀ e₁) (encodePair (x,w0)))).trans this
 have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
     (some (⟨some (Sum.inr kn),(M.initialState,none),
       fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
     some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
   have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
   rw [embF_init]
   simpa using this
 have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
   (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
 rw [embF_halt] at q3
 have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
     (some (⟨some (Sum.inr kU),(M.initialState,none),
       fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
     some (⟨some (Sum.inr ki),(M.initialState,none),
       fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
   have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
   simpa using this
 have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
     (some (⟨some (Sum.inr ki),(M.initialState,none),
       fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
     some (⟨some (Sum.inr kj),(M.initialState,none),
       fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
   have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
   simpa using this
 have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
     (some (⟨some (Sum.inr kj),(M.initialState,none),
       fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
     some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))) := by
   have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
   rw [fstk_nil_O] at this
   refine this.trans (Eq.trans ?_
     (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
   simp [encodePair]
   rfl
 refine ⟨_,?_,iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
   q4) q5) q6⟩
 simp only [encodePair_length,List.length_reverse,List.length_map]
 omega
lemma first_polyTime (f : List Bool -> List Bool)
   (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
   Nonempty (TM2ComputableInPolyTime encodePair encodePair
     (fun p : List Bool × List Bool => (f p.1,p.2))) := by
 let e₀ : Bool -> c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
 let e₁ : c.tm.Γ c.tm.k₁ -> Bool := c.outputAlphabet
 let T : Polynomial ℕ :=
   c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
     Polynomial.C 2 * Polynomial.X + Polynomial.C 5
 have key : ∀ p : List Bool × List Bool,∃ n,n ≤ T.eval (encodePair p).length /\
     (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
         (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
       some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1,p.2))) := by
   rintro ⟨x,w⟩
   have hs : ∃ s,s ≤ Polynomial.eval x.length c.time /\
       (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
         some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
     ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
   obtain ⟨s,b1,h⟩ := hs
   obtain ⟨n,hn,hrun⟩ := first_run e₀ e₁ x w _ s h
   have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
     rw [List.map_map]
     conv_rhs => rw [← List.map_id (f x)]
     exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
   rw [hm] at hrun
   refine ⟨n,hn.trans ?_,hrun⟩
   have h' := h
   rw [haltList_eq,initList_eq] at h'
   have hlen := run_length c.tm c.tm.k₁ s _ _ h'
   simp only [Function.update_self,List.length_map] at hlen
   have hin : ((Function.update (fun _ => [] : ∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
       c.tm.k₁).length ≤ x.length := by
     by_cases hk : c.tm.k₁ = c.tm.k₀
     · rw [hk,Function.update_self,List.length_map]
     · rw [Function.update_of_ne hk]; simp
   have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
     eval_mono _ (by omega)
   have hmul : maxPush c.tm * s ≤
       maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
     Nat.mul_le_mul_left _ (b1.trans b2)
   simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
     Polynomial.eval_X,encodePair_length,List.length_map]
   omega
 exact ⟨{
   tm := firstM c.tm e₀ e₁
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := T
   outputsFun := fun p =>
     { steps := Classical.choose (key p)
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
           Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
           (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
           (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
             (hm _ (encodePair (f p.1,p.2))).symm))
       steps_le_m := (Classical.choose_spec (key p)).1 } }⟩
end aK.Machines
end S9
section S10
namespace aK.Machines.Iter
open Turing
abbrev IX : Type := Fin 4
abbrev qA : IX := 0
abbrev rM : IX := 1
abbrev pj : IX := 2
abbrev ri : IX := 3
abbrev IL : Type := Fin 6
abbrev jK : IL := 0
abbrev iE : IL := 1
abbrev jN : IL := 2
abbrev lK : IL := 3
abbrev kC : IL := 4
abbrev lJ : IL := 5
variable (M : FinTM2)
abbrev ItΓ : M.K ⊕ IX -> Type
 | Sum.inl k => M.Γ k
 | Sum.inr ⟨0,_⟩ => Bool ⊕ Bool
 | Sum.inr ⟨1,_⟩ => Bool
 | Sum.inr ⟨2,_⟩ => Bool
 | Sum.inr ⟨3,_⟩ => Bool
abbrev ItΛ : Type := M.Λ ⊕ IL
abbrev Itσ : Type := M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI : TM2.Stmt M.Γ M.Λ M.σ -> TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trI q)
 | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o,s.2)) (trI q)
 | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o,s.2)) (trI q)
 | .load a q => .load (fun s => (a s.1,s.2)) (trI q)
 | .branch f q₁ q₂ => .branch (fun s => f s.1) (trI q₁) (trI q₂)
 | .goto f => .goto (fun s => Sum.inl (f s.1))
 | .halt => .goto (fun _ => Sum.inr lK)
variable (M)
def iterProg (e₀ : Bool -> M.Γ M.k₀) (d₀ : M.Γ M.k₀ -> Bool) (e₁ : M.Γ M.k₁ -> Bool) :
   ItΛ M -> TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | Sum.inl l => trI (M.m l)
 | Sum.inr ⟨0,_⟩ =>
   .pop (Sum.inr qA) (fun s o => (s.1,o))
     (.branch (fun s => s.2.isSome)
       (.branch (fun s => isFst s.2)
         (.push (Sum.inr pj) (fun s => bit s.2) (.goto fun _ => Sum.inr jK))
         (.push (Sum.inr rM) (fun s => bit s.2) (.goto fun _ => Sum.inr jK)))
       (.goto fun _ => Sum.inr iE))
 | Sum.inr ⟨1,_⟩ =>
   .pop (Sum.inr pj) (fun s o => (s.1,o.map Sum.inl))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr iE))
       (.goto fun _ => Sum.inr jN))
 | Sum.inr ⟨2,_⟩ =>
   .pop (Sum.inr rM) (fun s o => (s.1,o.map Sum.inl))
     (.branch (fun s => s.2.isSome)
       (.goto fun _ => Sum.inl M.main)
       (.goto fun _ => Sum.inr kC))
 | Sum.inr ⟨3,_⟩ =>
   .pop (Sum.inl M.k₁) (fun s o => (s.1,o.map fun y => Sum.inl (e₁ y)))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inr pj) (fun s => bit s.2) (.goto fun _ => Sum.inr lK))
       (.goto fun _ => Sum.inr iE))
 | Sum.inr ⟨4,_⟩ =>
   .pop (Sum.inl M.k₀) (fun s o => (s.1,o.map fun y => Sum.inl (d₀ y)))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inr pj) (fun s => bit s.2) (.goto fun _ => Sum.inr kC))
       (.goto fun _ => Sum.inr lJ))
 | Sum.inr ⟨5,_⟩ =>
   .pop (Sum.inr pj) (fun s o => (s.1,o.map Sum.inl))
     (.branch (fun s => s.2.isSome)
       (.push (Sum.inr ri) (fun s => bit s.2) (.goto fun _ => Sum.inr lJ))
       .halt)
def iterM (e₀ : Bool -> M.Γ M.k₀) (d₀ : M.Γ M.k₀ -> Bool) (e₁ : M.Γ M.k₁ -> Bool) : FinTM2 :=
 haveI := M.kFin
 haveI := M.ΛFin
 haveI := M.σFin
 { K := M.K ⊕ IX
   k₀ := Sum.inr qA
   k₁ := Sum.inr ri
   Γ := ItΓ M
   Λ := ItΛ M
   main := Sum.inr jK
   σ := Itσ M
   initialState := (M.initialState,none)
   Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
   m := iterProg M e₀ d₀ e₁ }
variable {M}
def istk (S : ∀ k,List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
   ∀ k,List (ItΓ M k)
 | Sum.inl k => S k
 | Sum.inr ⟨0,_⟩ => i
 | Sum.inr ⟨1,_⟩ => cn
 | Sum.inr ⟨2,_⟩ => t
 | Sum.inr ⟨3,_⟩ => o
section istk
variable (S : ∀ k,List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
@[simp] lemma istk_M (k : M.K) : istk S i cn t o (Sum.inl k) = S k := rfl
@[simp] lemma istk_I : istk S i cn t o (Sum.inr qA) = i := rfl
@[simp] lemma istk_C : istk S i cn t o (Sum.inr rM) = cn := rfl
@[simp] lemma istk_T : istk S i cn t o (Sum.inr pj) = t := rfl
@[simp] lemma istk_O : istk S i cn t o (Sum.inr ri) = o := rfl
lemma istk_set_M (k : M.K) (x : List (M.Γ k)) :
   Function.update (istk S i cn t o) (Sum.inl k) x = istk (Function.update S k x) i cn t o := by
 funext j
 rcases j with j | j
 · by_cases h : j = k
   · subst h
     rw [Function.update_self]
     show x = Function.update S j x j
     rw [Function.update_self]
   · rw [Function.update_of_ne (by simpa using h)]
     show S j = Function.update S k x j
     rw [Function.update_of_ne h]
 · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl
lemma istk_set_I (i' : List (Bool ⊕ Bool)) :
   Function.update (istk S i cn t o) (Sum.inr qA) i' = istk S i' cn t o := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,qA] <;> rfl
lemma istk_set_C (cn' : List Bool) :
   Function.update (istk S i cn t o) (Sum.inr rM) cn' = istk S i cn' t o := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,rM] <;> rfl
lemma istk_set_T (t' : List Bool) :
   Function.update (istk S i cn t o) (Sum.inr pj) t' = istk S i cn t' o := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,pj] <;> rfl
lemma istk_set_O (o' : List Bool) :
   Function.update (istk S i cn t o) (Sum.inr ri) o' = istk S i cn t o' := by
 funext j; rcases j with j | j
 · rw [Function.update_of_ne (by simp)]; rfl
 · fin_cases j <;> simp [Function.update,ri] <;> rfl
end istk
abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def embI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
   (c : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
 ⟨some (c.l.elim (Sum.inr lK) Sum.inl),(c.var,b),istk c.stk i cn t o⟩
lemma simI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
   (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k,List (M.Γ k)) :
   TM2.stepAux (trI q) ((v,b) : Itσ M) (istk S i cn t o) =
     embI b i cn t o (TM2.stepAux q v S) := by
 induction q generalizing v S with
 | push k f q ih =>
   have := ih v (Function.update S k (f v :: S k))
   rw [← istk_set_M] at this
   exact this
 | peek k f q ih => exact ih _ _
 | pop k f q ih =>
   have := ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [← istk_set_M] at this
   exact this
 | load a q ih => exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
   simp only [trI,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f => rfl
 | halt => rfl
lemma stepI (e₀ : Bool -> M.Γ M.k₀) (d₀ : M.Γ M.k₀ -> Bool) (e₁ : M.Γ M.k₁ -> Bool)
   (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
   (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
   TM2.step (iterProg M e₀ d₀ e₁) (embI b i cn t o c) = some (embI b i cn t o c') := by
 obtain ⟨l,v,S⟩ := c
 cases l with
 | none => simp [TM2.step] at h
 | some l =>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (simI b i cn t o (M.m l) v S)
lemma embI_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
   (l : List (M.Γ M.k₀)) :
   embI b i cn t o (initList M l) =
     (⟨some (Sum.inl M.main),(M.initialState,b),
       istk (Function.update (fun _ => []) M.k₀ l) i cn t o⟩ : ICfg M) := by
 rw [initList_eq]; rfl
lemma embI_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
   (m : List (M.Γ M.k₁)) :
   embI b i cn t o (haltList M m) =
     (⟨some (Sum.inr lK),(M.initialState,b),
       istk (Function.update (fun _ => []) M.k₁ m) i cn t o⟩ : ICfg M) := by
 rw [haltList_eq]; rfl
lemma istk_nil : (istk (fun _ => []) [] [] [] [] : ∀ k,List (ItΓ M k)) = fun _ => [] := by
 funext j; rcases j with j | j <;> [rfl; fin_cases j <;> rfl]
lemma istk_nil_I (i : List (Bool ⊕ Bool)) :
   (istk (fun _ => []) i [] [] [] : ∀ k,List (ItΓ M k)) =
     Function.update (fun _ => [] : ∀ k,List (ItΓ M k)) (Sum.inr qA) i :=
 (istk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [istk_nil])
lemma istk_nil_O (o : List Bool) :
   (istk (fun _ => []) [] [] [] o : ∀ k,List (ItΓ M k)) =
     Function.update (fun _ => [] : ∀ k,List (ItΓ M k)) (Sum.inr ri) o :=
 (istk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [istk_nil])
end aK.Machines.Iter
end S10
section S11
namespace aK.Machines.Iter
open Turing PEqualNP.Library
variable {M : FinTM2} (e₀ : Bool -> M.Γ M.k₀) (d₀ : M.Γ M.k₀ -> Bool) (e₁ : M.Γ M.k₁ -> Bool)
variable (v : M.σ) (S : ∀ k,List (M.Γ k))
lemma i1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
   (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr jK),(v,b),istk S (Sum.inl a :: i) cn t o⟩ : ICfg M) =
     some ⟨some (Sum.inr jK),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_I,istk_set_T,isFst,bit,Function.update,qA,rM,pj,ri]
lemma i1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
   (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr jK),(v,b),istk S (Sum.inr a :: i) cn t o⟩ : ICfg M) =
     some ⟨some (Sum.inr jK),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_I,istk_set_C,isFst,bit,Function.update,qA,rM,pj,ri]
lemma i1_nil (b : Option (Bool ⊕ Bool)) (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr jK),(v,b),istk S [] cn t o⟩ : ICfg M) =
     some ⟨some (Sum.inr iE),(v,none),istk S [] cn t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_I]
lemma iloop1 (o : List Bool) :
   ∀ (i : List (Bool ⊕ Bool)) (cn t : List Bool) (b : Option (Bool ⊕ Bool)),
   ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[i.length + 1]
       (some (⟨some (Sum.inr jK),(v,b),istk S i cn t o⟩ : ICfg M)) =
     some ⟨some (Sum.inr iE),(v,none),
       istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
         ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
 intro i
 induction i with
 | nil => intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
 | cons x i ih =>
   intro cn t b
   rw [List.length_cons,Function.iterate_succ_apply]
   cases x with
   | inl a =>
     have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
         (some (⟨some (Sum.inr jK),(v,b),istk S (Sum.inl a :: i) cn t o⟩ : ICfg M)) =
         some ⟨some (Sum.inr jK),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩ :=
       i1_inl e₀ d₀ e₁ v S b a i cn t o
     rw [e,ih]; simp [List.filterMap_cons]
   | inr a =>
     have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
         (some (⟨some (Sum.inr jK),(v,b),istk S (Sum.inr a :: i) cn t o⟩ : ICfg M)) =
         some ⟨some (Sum.inr jK),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩ :=
       i1_inr e₀ d₀ e₁ v S b a i cn t o
     rw [e,ih]; simp [List.filterMap_cons]
lemma i2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
   (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr iE),(v,b),istk S i cn (a :: t) o⟩ : ICfg M) =
     some ⟨some (Sum.inr iE),(v,some (Sum.inl a)),
       istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_T,istk_set_M,bit]
lemma i2_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr iE),(v,b),istk S i cn [] o⟩ : ICfg M) =
     some ⟨some (Sum.inr jN),(v,none),istk S i cn [] o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_T]
lemma iloop2 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
   ∀ (t : List Bool) (S : ∀ k,List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
   ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
       (some (⟨some (Sum.inr iE),(v,b),istk S i cn t o⟩ : ICfg M)) =
     some ⟨some (Sum.inr jN),(v,none),
       istk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) i cn [] o⟩ := by
 intro t
 induction t with
 | nil =>
   intro S b
   have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
   rw [this]
   exact i2_nil e₀ d₀ e₁ v S b i cn o
 | cons a t ih =>
   intro S b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
       (some (⟨some (Sum.inr iE),(v,b),istk S i cn (a :: t) o⟩ : ICfg M)) =
       some ⟨some (Sum.inr iE),(v,some (Sum.inl a)),
         istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
     i2_cons e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih]; simp
lemma i3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
   (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr jN),(v,b),istk S i (a :: cn) t o⟩ : ICfg M) =
     some ⟨some (Sum.inl M.main),(v,some (Sum.inl a)),istk S i cn t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_C]
lemma i3_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr jN),(v,b),istk S i [] t o⟩ : ICfg M) =
     some ⟨some (Sum.inr kC),(v,none),istk S i [] t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_C]
lemma i4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁))
   (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr lK),(v,b),istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
         ICfg M) =
     some ⟨some (Sum.inr lK),(v,some (Sum.inl (e₁ y))),
       istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_T,istk_set_M,bit]
lemma i4_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr lK),(v,b),istk (Function.update S M.k₁ []) i cn t o⟩ : ICfg M) =
     some ⟨some (Sum.inr iE),(v,none),istk (Function.update S M.k₁ []) i cn t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_M]
lemma iloop4 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
   ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
   ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
       (some (⟨some (Sum.inr lK),(v,b),istk (Function.update S M.k₁ m) i cn t o⟩ :
         ICfg M)) =
     some ⟨some (Sum.inr iE),(v,none),
       istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩ := by
 intro m
 induction m with
 | nil => intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
 | cons y m ih =>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
       (some (⟨some (Sum.inr lK),(v,b),
         istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ : ICfg M)) =
       some ⟨some (Sum.inr lK),(v,some (Sum.inl (e₁ y))),
         istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
     i4_cons e₀ d₀ e₁ v S b y m i cn t o
   rw [e,ih]; simp
lemma i5_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₀) (m : List (M.Γ M.k₀))
   (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr kC),(v,b),istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
         ICfg M) =
     some ⟨some (Sum.inr kC),(v,some (Sum.inl (d₀ y))),
       istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_T,istk_set_M,bit]
lemma i5_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr kC),(v,b),istk (Function.update S M.k₀ []) i cn t o⟩ : ICfg M) =
     some ⟨some (Sum.inr lJ),(v,none),istk (Function.update S M.k₀ []) i cn t o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_M]
lemma iloop5 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
   ∀ (m : List (M.Γ M.k₀)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
   ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
       (some (⟨some (Sum.inr kC),(v,b),istk (Function.update S M.k₀ m) i cn t o⟩ :
         ICfg M)) =
     some ⟨some (Sum.inr lJ),(v,none),
       istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩ := by
 intro m
 induction m with
 | nil => intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
 | cons y m ih =>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
       (some (⟨some (Sum.inr kC),(v,b),
         istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ : ICfg M)) =
       some ⟨some (Sum.inr kC),(v,some (Sum.inl (d₀ y))),
         istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
     i5_cons e₀ d₀ e₁ v S b y m i cn t o
   rw [e,ih]; simp
lemma i6_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
   (cn t o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr lJ),(v,b),istk S i cn (a :: t) o⟩ : ICfg M) =
     some ⟨some (Sum.inr lJ),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_T,istk_set_O,bit,Function.update,qA,rM,pj,ri]
lemma i6_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
   TM2.step (iterProg M e₀ d₀ e₁)
       (⟨some (Sum.inr lJ),(v,b),istk S i cn [] o⟩ : ICfg M) =
     some ⟨none,(v,none),istk S i cn [] o⟩ := by
 simp [TM2.step,iterProg,TM2.stepAux,istk_set_T]
lemma iloop6 (i : List (Bool ⊕ Bool)) (cn : List Bool) :
   ∀ (t o : List Bool) (b : Option (Bool ⊕ Bool)),
   ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
       (some (⟨some (Sum.inr lJ),(v,b),istk S i cn t o⟩ : ICfg M)) =
     some ⟨none,(v,none),istk S i cn [] (t.reverse ++ o)⟩ := by
 intro t
 induction t with
 | nil => intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
 | cons a t ih =>
   intro o b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
       (some (⟨some (Sum.inr lJ),(v,b),istk S i cn (a :: t) o⟩ : ICfg M)) =
       some ⟨some (Sum.inr lJ),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩ :=
     i6_cons e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih]; simp
lemma update_nil_nil (k : M.K) :
   Function.update (fun _ => [] : ∀ k,List (M.Γ k)) k [] = fun _ => [] :=
 Function.update_eq_self k (fun _ => [] : ∀ k,List (M.Γ k))
lemma main_loop (g : List Bool -> List Bool) (k : ℕ) (p : Polynomial ℕ)
   (hk : ∀ y : List Bool,(g y).length ≤ y.length + k)
   (hd : ∀ a,d₀ (e₀ a) = a)
   (hrun : ∀ z : List Bool,∃ (s : ℕ) (m : List (M.Γ M.k₁)),s ≤ p.eval z.length /\
     (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) /\
       m.map e₁ = g z) :
   ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),z.length + k * cn.length ≤ L ->
     ∃ n,n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 /\
       ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
           (some (⟨some (Sum.inr jN),(M.initialState,b),
             istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
         some ⟨none,(M.initialState,none),
           istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
 intro cn
 induction cn with
 | nil =>
   intro z L b hL
   have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
     rw [List.map_reverse,List.reverse_reverse,List.map_map]
     conv_rhs => rw [← List.map_id z]
     exact List.map_congr_left fun a _ => hd a
   have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
       (some (⟨some (Sum.inr jN),(M.initialState,b),
         istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
       some ⟨some (Sum.inr kC),(M.initialState,none),
         istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
     i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
   have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
   rw [update_nil_nil,List.append_nil] at q2
   have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
     ((z.map e₀).reverse.map d₀) [] none
   rw [List.append_nil,hz] at q3
   refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3⟩
   simp only [List.length_reverse,List.length_map,List.length_nil] at hL ⊢
   omega
 | cons a cn ih =>
   intro z L b hL
   obtain ⟨s,m,hs,hm,hmg⟩ := hrun z
   rw [List.length_cons] at hL
   have hgz : (g z).length ≤ z.length + k := hk z
   have hkk : k * (cn.length + 1) = k * cn.length + k := Nat.mul_succ _ _
   have hml : m.length = (g z).length := by rw [← hmg,List.length_map]
   have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
       (some (⟨some (Sum.inr jN),(M.initialState,b),
         istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
       some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
     rw [embI_init]
     exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
   have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
     (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
     s _ _ hm
   rw [embI_halt] at q2
   have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
   rw [update_nil_nil,List.append_nil,List.map_reverse,hmg] at q3
   have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
   rw [List.append_nil,List.reverse_reverse] at q4
   obtain ⟨n,hn,q5⟩ := ih (g z) L none (by omega)
   have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
   rw [e]
   refine ⟨_,?_,iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
   have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
   rw [List.length_reverse,List.length_cons,Nat.succ_mul]
   generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
   omega
lemma iter_run (g : List Bool -> List Bool) (k : ℕ) (p : Polynomial ℕ)
   (hk : ∀ y : List Bool,(g y).length ≤ y.length + k)
   (hd : ∀ a,d₀ (e₀ a) = a)
   (hrun : ∀ z : List Bool,∃ (s : ℕ) (m : List (M.Γ M.k₁)),s ≤ p.eval z.length /\
     (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) /\
       m.map e₁ = g z)
   (y u : List Bool) (L : ℕ) (hL : y.length + k * u.length ≤ L) :
   ∃ n,n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 /\
     ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
       some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
 have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length + 1]
     (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
     some (⟨some (Sum.inr iE),(M.initialState,none),
       istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
   have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y,u)) [] [] none
   rw [encodePair_left,encodePair_right,List.append_nil,List.append_nil,istk_nil_I] at this
   exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length + 1] (some c))
     (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
 rw [List.append_nil,List.reverse_reverse] at q2
 obtain ⟨n,hn,q3⟩ := main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
   (by rw [List.length_reverse]; exact hL)
 rw [List.length_reverse] at hn q3
 rw [istk_nil_O] at q3
 have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
     (some (⟨some (Sum.inr jN),(M.initialState,none),
       istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
     some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
   q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
 refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3'⟩
 rw [encodePair_length,List.length_reverse]
 omega
lemma iter_polyTime (g : List Bool -> List Bool)
   (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
   (k : ℕ) (hk : ∀ y : List Bool,(g y).length ≤ y.length + k) :
   Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
     (fun x : List Bool => x)
     (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
 let e₀ : Bool -> c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
 let d₀ : c.tm.Γ c.tm.k₀ -> Bool := c.inputAlphabet
 let e₁ : c.tm.Γ c.tm.k₁ -> Bool := c.outputAlphabet
 let W : Polynomial ℕ := Polynomial.X + Polynomial.C k * Polynomial.X
 let T : Polynomial ℕ :=
   Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
     Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
 have hd : ∀ a,d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
 have hrun : ∀ z : List Bool,∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
     s ≤ c.time.eval z.length /\
     (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
       some (haltList c.tm m) /\ m.map e₁ = g z := by
   intro z
   refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
     (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
   rw [List.map_map]
   conv_rhs => rw [← List.map_id (g z)]
   exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
 have key : ∀ q : List Bool × List Bool,∃ n,n ≤ T.eval (encodePair q).length /\
     (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
         (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
       some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
   rintro ⟨y,u⟩
   have hku : k * u.length ≤ k * (y.length + u.length) := Nat.mul_le_mul_left _ (by omega)
   obtain ⟨n,hn,hr⟩ := iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
     (y.length + u.length + k * (y.length + u.length)) (by omega)
   refine ⟨n,hn.trans ?_,hr⟩
   simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
     Polynomial.eval_X,Polynomial.eval_comp,encodePair_length]
   have hmul : u.length * (Polynomial.eval (y.length + u.length + k * (y.length + u.length))
         c.time + 2 * (y.length + u.length + k * (y.length + u.length)) + 3) ≤
       (y.length + u.length) * (Polynomial.eval
         (y.length + u.length + k * (y.length + u.length)) c.time +
           2 * (y.length + u.length + k * (y.length + u.length)) + 3) :=
     Nat.mul_le_mul_right _ (by omega)
   generalize k * (y.length + u.length) = B at hmul ⊢
   omega
 exact ⟨{
   tm := iterM c.tm e₀ d₀ e₁
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := T
   outputsFun := fun q =>
     { steps := Classical.choose (key q)
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
           Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
           (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
           (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
             (hm _ (g^[q.2.length] q.1)).symm))
       steps_le_m := (Classical.choose_spec (key q)).1 } }⟩
end aK.Machines.Iter
end S11
section S12
namespace aK.Machines.Iter
open Turing PEqualNP.Library
variable {M : FinTM2} (e₀ : Bool -> M.Γ M.k₀) (d₀ : M.Γ M.k₀ -> Bool) (e₁ : M.Γ M.k₁ -> Bool)
lemma main_loop_bdd (g : List Bool -> List Bool) (p : Polynomial ℕ)
   (hd : ∀ a,d₀ (e₀ a) = a)
   (hrun : ∀ z : List Bool,∃ (s : ℕ) (m : List (M.Γ M.k₁)),s ≤ p.eval z.length /\
     (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) /\
       m.map e₁ = g z) :
   ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),
     (∀ j ≤ cn.length,(g^[j] z).length ≤ L) ->
     ∃ n,n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 /\
       ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
           (some (⟨some (Sum.inr jN),(M.initialState,b),
             istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
         some ⟨none,(M.initialState,none),
           istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
 intro cn
 induction cn with
 | nil =>
   intro z L b hL
   have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
     rw [List.map_reverse,List.reverse_reverse,List.map_map]
     conv_rhs => rw [← List.map_id z]
     exact List.map_congr_left fun a _ => hd a
   have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
       (some (⟨some (Sum.inr jN),(M.initialState,b),
         istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
       some ⟨some (Sum.inr kC),(M.initialState,none),
         istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
     i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
   have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
   rw [update_nil_nil,List.append_nil] at q2
   have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
     ((z.map e₀).reverse.map d₀) [] none
   rw [List.append_nil,hz] at q3
   refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3⟩
   have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
   simp only [List.length_reverse,List.length_map,List.length_nil] at hz0 ⊢
   omega
 | cons a cn ih =>
   intro z L b hL
   obtain ⟨s,m,hs,hm,hmg⟩ := hrun z
   rw [List.length_cons] at hL
   have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
   have hgz : (g z).length ≤ L := hL 1 (by omega)
   have hml : m.length = (g z).length := by rw [← hmg,List.length_map]
   have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
       (some (⟨some (Sum.inr jN),(M.initialState,b),
         istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
       some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
     rw [embI_init]
     exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
   have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
     (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
     s _ _ hm
   rw [embI_halt] at q2
   have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
   rw [update_nil_nil,List.append_nil,List.map_reverse,hmg] at q3
   have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
   rw [List.append_nil,List.reverse_reverse] at q4
   obtain ⟨n,hn,q5⟩ := ih (g z) L none (fun j hj => by
     have := hL (j + 1) (by omega)
     rwa [Function.iterate_succ_apply] at this)
   have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
   rw [e]
   refine ⟨_,?_,iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
   have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
   rw [List.length_reverse,List.length_cons,Nat.succ_mul]
   generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
   omega
lemma iter_run_bdd (g : List Bool -> List Bool) (p : Polynomial ℕ)
   (hd : ∀ a,d₀ (e₀ a) = a)
   (hrun : ∀ z : List Bool,∃ (s : ℕ) (m : List (M.Γ M.k₁)),s ≤ p.eval z.length /\
     (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) /\
       m.map e₁ = g z)
   (y u : List Bool) (L : ℕ) (hL : ∀ j ≤ u.length,(g^[j] y).length ≤ L) :
   ∃ n,n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 /\
     ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
       some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
 have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length + 1]
     (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
     some (⟨some (Sum.inr iE),(M.initialState,none),
       istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
   have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y,u)) [] [] none
   rw [encodePair_left,encodePair_right,List.append_nil,List.append_nil,istk_nil_I] at this
   exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length + 1] (some c))
     (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
 rw [List.append_nil,List.reverse_reverse] at q2
 obtain ⟨n,hn,q3⟩ := main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
   (by rw [List.length_reverse]; exact hL)
 rw [List.length_reverse] at hn q3
 rw [istk_nil_O] at q3
 have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
     (some (⟨some (Sum.inr jN),(M.initialState,none),
       istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
     some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
   q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
 refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3'⟩
 rw [encodePair_length,List.length_reverse]
 omega
lemma iterate_length_measure (g : List Bool -> List Bool) (m : List Bool -> ℕ)
   (hm : ∀ y : List Bool,m (g y) ≤ m y)
   (hg : ∀ y : List Bool,(g y).length ≤ y.length + m y) (y : List Bool) :
   ∀ j : ℕ,m (g^[j] y) ≤ m y /\ (g^[j] y).length ≤ y.length + j * m y := by
 intro j
 induction j with
 | zero => simp
 | succ j ih =>
   rw [Function.iterate_succ_apply',Nat.succ_mul]
   have h1 := hm (g^[j] y)
   have h2 := hg (g^[j] y)
   obtain ⟨i1,i2⟩ := ih
   generalize j * m y = A at i2 ⊢
   exact ⟨by omega,by omega⟩
lemma measure_arith (A B L V y u : ℕ) (hLV : L ≤ V) (hAB : A ≤ B) :
   A + 2 * L + 2 * y + u + 5 ≤ B + 2 * V + 3 * (y + u) + 5 := by
 omega
lemma iter_polyTime_measure (g : List Bool -> List Bool)
   (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
   (m : List Bool -> ℕ) (a : ℕ)
   (hm : ∀ y : List Bool,m (g y) ≤ m y)
   (hg : ∀ y : List Bool,(g y).length ≤ y.length + m y)
   (ha : ∀ y : List Bool,m y ≤ a * y.length + a) :
   Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
     (fun x : List Bool => x) (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
 let e₀ : Bool -> c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
 let d₀ : c.tm.Γ c.tm.k₀ -> Bool := c.inputAlphabet
 let e₁ : c.tm.Γ c.tm.k₁ -> Bool := c.outputAlphabet
 let W : Polynomial ℕ :=
   Polynomial.X + Polynomial.X * (Polynomial.C a * Polynomial.X + Polynomial.C a)
 let T : Polynomial ℕ :=
   Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
     Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
 have hd : ∀ a,d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
 have hrun : ∀ z : List Bool,∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
     s ≤ c.time.eval z.length /\
     (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
       some (haltList c.tm m) /\ m.map e₁ = g z := by
   intro z
   refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
     (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
   rw [List.map_map]
   conv_rhs => rw [← List.map_id (g z)]
   exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
 have key : ∀ q : List Bool × List Bool,∃ n,n ≤ T.eval (encodePair q).length /\
     (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
         (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
       some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
   rintro ⟨y,u⟩
   have hL : ∀ j ≤ u.length,
       (g^[j] y).length ≤ y.length + u.length * (a * y.length + a) := by
     intro j hj
     have h1 := (iterate_length_measure g m hm hg y j).2
     have h2 : j * m y ≤ u.length * (a * y.length + a) := Nat.mul_le_mul hj (ha y)
     omega
   obtain ⟨n,hn,hr⟩ := iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
     (y.length + u.length * (a * y.length + a)) hL
   have hLV : y.length + u.length * (a * y.length + a) ≤
       (y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a) :=
     Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
       (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
   have hp := eval_mono c.time hLV
   have hmul : u.length * (Polynomial.eval (y.length + u.length * (a * y.length + a)) c.time +
         2 * (y.length + u.length * (a * y.length + a)) + 3) ≤
       (y.length + u.length) * (Polynomial.eval
         ((y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a))
           c.time +
           2 * ((y.length + u.length) +
             (y.length + u.length) * (a * (y.length + u.length) + a)) + 3) :=
     Nat.mul_le_mul (by omega) (by omega)
   refine ⟨n,hn.trans ?_,hr⟩
   simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
     Polynomial.eval_X,Polynomial.eval_comp,encodePair_length]
   exact measure_arith _ _ _ _ _ _ hLV hmul
 exact ⟨{
   tm := iterM c.tm e₀ d₀ e₁
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := T
   outputsFun := fun q =>
     { steps := Classical.choose (key q)
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
           Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
           (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
           (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
             (hm _ (g^[q.2.length] q.1)).symm))
       steps_le_m := (Classical.choose_spec (key q)).1 } }⟩
end aK.Machines.Iter
end S12
section S13
namespace aK.Machines
open PEqualNP.Library
open Turing
abbrev MulK : Type := Fin 5
abbrev mW : MulK := 0
abbrev qx : MulK := 1
abbrev nw : MulK := 2
abbrev qE : MulK := 3
abbrev nA : MulK := 4
abbrev MulL : Type := Fin 5
abbrev ci : MulL := 0
abbrev bR : MulL := 1
abbrev fJ : MulL := 2
abbrev dY : MulL := 3
abbrev dF : MulL := 4
abbrev MulΓ (k : MulK) : Type :=
 if k.val = 0 then Bool ⊕ Bool else Bool
def mulProg : MulL -> TM2.Stmt MulΓ MulL (Option Bool)
 | ⟨0,_⟩ =>
   .pop mW (fun _ o => o.map Sum.isLeft)
     (.branch (fun s => s.isSome)
       (.branch (fun s => s == some true)
         (.push qx (fun _ => true) (.goto fun _ => ci))
         (.push nw (fun _ => true) (.goto fun _ => ci)))
       (.goto fun _ => bR))
 | ⟨1,_⟩ =>
   .pop qx (fun _ o => o)
     (.branch (fun s => s.isSome)
       (.goto fun _ => fJ)
       (.goto fun _ => dF))
 | ⟨2,_⟩ =>
   .pop nw (fun _ o => o)
     (.branch (fun s => s.isSome)
       (.push qE (fun _ => true) (.push nA (fun _ => true) (.goto fun _ => fJ)))
       (.goto fun _ => dY))
 | ⟨3,_⟩ =>
   .pop qE (fun _ o => o)
     (.branch (fun s => s.isSome)
       (.push nw (fun _ => true) (.goto fun _ => dY))
       (.goto fun _ => bR))
 | ⟨4,_⟩ =>
   .pop nw (fun _ o => o)
     (.branch (fun s => s.isSome)
       (.goto fun _ => dF)
       .halt)
def mulTM : FinTM2 where
 K := MulK
 k₀ := mW
 k₁ := nA
 Γ := MulΓ
 Λ := MulL
 main := ci
 σ := Option Bool
 initialState := none
 Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
 m := mulProg
def mstk (i : List (Bool ⊕ Bool)) (a b c o : List Bool) (k : MulK) : List (MulΓ k) :=
 match k with
 | ⟨0,_⟩ => i
 | ⟨1,_⟩ => a
 | ⟨2,_⟩ => b
 | ⟨3,_⟩ => c
 | ⟨4,_⟩ => o
@[simp] lemma mstk_I (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mstk i a b c o mW = i := rfl
@[simp] lemma mstk_A (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mstk i a b c o qx = a := rfl
@[simp] lemma mstk_B (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mstk i a b c o nw = b := rfl
@[simp] lemma mstk_C (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mstk i a b c o qE = c := rfl
@[simp] lemma mstk_O (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mstk i a b c o nA = o := rfl
@[simp] lemma mstk_set_I (i i' : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   Function.update (mstk i a b c o) mW i' = mstk i' a b c o := by
 funext k; fin_cases k <;> rfl
@[simp] lemma mstk_set_A (i : List (Bool ⊕ Bool)) (a a' b c o : List Bool) :
   Function.update (mstk i a b c o) qx a' = mstk i a' b c o := by
 funext k; fin_cases k <;> rfl
@[simp] lemma mstk_set_B (i : List (Bool ⊕ Bool)) (a b b' c o : List Bool) :
   Function.update (mstk i a b c o) nw b' = mstk i a b' c o := by
 funext k; fin_cases k <;> rfl
@[simp] lemma mstk_set_C (i : List (Bool ⊕ Bool)) (a b c c' o : List Bool) :
   Function.update (mstk i a b c o) qE c' = mstk i a b c' o := by
 funext k; fin_cases k <;> rfl
@[simp] lemma mstk_set_O (i : List (Bool ⊕ Bool)) (a b c o o' : List Bool) :
   Function.update (mstk i a b c o) nA o' = mstk i a b c o' := by
 funext k; fin_cases k <;> rfl
lemma mstk_start (i : List (Bool ⊕ Bool)) :
   mstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k,List (MulΓ k)) mW i := by
 funext k; fin_cases k <;> rfl
lemma mstk_end (o : List Bool) :
   mstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k,List (MulΓ k)) nA o := by
 funext k; fin_cases k <;> rfl
abbrev MulCfg : Type := TM2.Cfg MulΓ MulL (Option Bool)
abbrev mulStep : Option MulCfg -> Option MulCfg := flip bind (TM2.step mulProg)
lemma split_inl (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mulStep (some ⟨some ci,s,mstk (Sum.inl y :: i) a b c o⟩) =
     some ⟨some ci,some true,mstk i (true :: a) b c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma split_inr (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mulStep (some ⟨some ci,s,mstk (Sum.inr y :: i) a b c o⟩) =
     some ⟨some ci,some false,mstk i a (true :: b) c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma split_nil (s : Option Bool) (a b c o : List Bool) :
   mulStep (some ⟨some ci,s,mstk [] a b c o⟩) =
     some ⟨some bR,none,mstk [] a b c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma outer_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mulStep (some ⟨some bR,s,mstk i (y :: a) b c o⟩) =
     some ⟨some fJ,some y,mstk i a b c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma outer_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (b c o : List Bool) :
   mulStep (some ⟨some bR,s,mstk i [] b c o⟩) =
     some ⟨some dF,none,mstk i [] b c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma copy_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mulStep (some ⟨some fJ,s,mstk i a (y :: b) c o⟩) =
     some ⟨some fJ,some y,mstk i a b (true :: c) (true :: o)⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma copy_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
   mulStep (some ⟨some fJ,s,mstk i a [] c o⟩) =
     some ⟨some dY,none,mstk i a [] c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma back_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mulStep (some ⟨some dY,s,mstk i a b (y :: c) o⟩) =
     some ⟨some dY,some y,mstk i a (true :: b) c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma back_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a b o : List Bool) :
   mulStep (some ⟨some dY,s,mstk i a b [] o⟩) =
     some ⟨some bR,none,mstk i a b [] o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma clean_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
   mulStep (some ⟨some dF,s,mstk i a (y :: b) c o⟩) =
     some ⟨some dF,some y,mstk i a b c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
lemma clean_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
   mulStep (some ⟨some dF,s,mstk i a [] c o⟩) =
     some ⟨none,none,mstk i a [] c o⟩ := by
 simp [mulStep,flip,TM2.step,mulProg,TM2.stepAux]
abbrev rep (n : ℕ) : List Bool := List.replicate n true
lemma rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl
lemma splitLoopW (a : List Bool) :
   ∀ (w : List Bool) (b : ℕ) (s : Option Bool),
     mulStep^[w.length + 1] (some ⟨some ci,s,mstk (w.map Sum.inr) a (rep b) [] []⟩) =
       some ⟨some bR,none,mstk [] a (rep (w.length + b)) [] []⟩ := by
 intro w
 induction w with
 | nil => intro b s; simpa using split_nil s a (rep b) [] []
 | cons y w ih =>
   intro b s
   rw [List.length_cons,Function.iterate_succ_apply,List.map_cons,split_inr,rep_succ,ih]
   rw [show w.length + (b + 1) = w.length + 1 + b from by omega]
lemma splitLoopX (w : List Bool) :
   ∀ (x : List Bool) (a : ℕ) (s : Option Bool),
     mulStep^[x.length + (w.length + 1)]
         (some ⟨some ci,s,mstk (x.map Sum.inl ++ w.map Sum.inr) (rep a) [] [] []⟩) =
       some ⟨some bR,none,mstk [] (rep (x.length + a)) (rep w.length) [] []⟩ := by
 intro x
 induction x with
 | nil =>
   intro a s
   simpa using splitLoopW (rep a) w 0 s
 | cons y x ih =>
   intro a s
   rw [List.length_cons,show x.length + 1 + (w.length + 1) = (x.length + (w.length + 1)) + 1
     from by omega,Function.iterate_succ_apply,List.map_cons,List.cons_append,split_inl,
     rep_succ,ih]
   rw [show x.length + (a + 1) = x.length + 1 + a from by omega]
lemma copyLoop (a : List Bool) :
   ∀ (b c o : ℕ) (s : Option Bool),
     mulStep^[b + 1] (some ⟨some fJ,s,mstk [] a (rep b) (rep c) (rep o)⟩) =
       some ⟨some dY,none,mstk [] a [] (rep (b + c)) (rep (b + o))⟩ := by
 intro b
 induction b with
 | zero => intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
 | succ b ih =>
   intro c o s
   rw [Function.iterate_succ_apply,← rep_succ b,copy_cons,rep_succ,rep_succ,ih]
   rw [show b + (c + 1) = b + 1 + c from by omega,show b + (o + 1) = b + 1 + o from by omega]
lemma backLoop (a o : List Bool) :
   ∀ (c b : ℕ) (s : Option Bool),
     mulStep^[c + 1] (some ⟨some dY,s,mstk [] a (rep b) (rep c) o⟩) =
       some ⟨some bR,none,mstk [] a (rep (c + b)) [] o⟩ := by
 intro c
 induction c with
 | zero => intro b s; simpa using back_nil s [] a (rep b) o
 | succ c ih =>
   intro b s
   rw [Function.iterate_succ_apply,← rep_succ c,back_cons,rep_succ,ih]
   rw [show c + (b + 1) = c + 1 + b from by omega]
lemma outerLoop (b : ℕ) :
   ∀ (a o : ℕ) (s : Option Bool),
     mulStep^[a * (2 * b + 3) + 1] (some ⟨some bR,s,mstk [] (rep a) (rep b) [] (rep o)⟩) =
       some ⟨some dF,none,mstk [] [] (rep b) [] (rep (a * b + o))⟩ := by
 intro a
 induction a with
 | zero => intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
 | succ a ih =>
   intro o s
   rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + ((b + 1) + ((b + 1) + 1))
     from by ring,Function.iterate_add_apply mulStep (a * (2 * b + 3) + 1),
     Function.iterate_add_apply mulStep (b + 1) ((b + 1) + 1),
     Function.iterate_succ_apply mulStep (b + 1),← rep_succ a,outer_cons]
   have h1 : mulStep^[b + 1]
       (some ⟨some fJ,some true,mstk [] (rep a) (rep b) [] (rep o)⟩) =
       some ⟨some dY,none,mstk [] (rep a) [] (rep b) (rep (b + o))⟩ :=
     copyLoop (rep a) b 0 o (some true)
   rw [h1]
   have h2 : mulStep^[b + 1]
       (some ⟨some dY,none,mstk [] (rep a) [] (rep b) (rep (b + o))⟩) =
       some ⟨some bR,none,mstk [] (rep a) (rep b) [] (rep (b + o))⟩ :=
     backLoop (rep a) (rep (b + o)) b 0 none
   rw [h2,ih]
   rw [show a * b + (b + o) = (a + 1) * b + o from by ring]
lemma cleanLoop (o : List Bool) :
   ∀ (b : ℕ) (s : Option Bool),
     mulStep^[b + 1] (some ⟨some dF,s,mstk [] [] (rep b) [] o⟩) =
       some ⟨none,none,mstk [] [] [] [] o⟩ := by
 intro b
 induction b with
 | zero => intro s; simpa using clean_nil s [] [] [] o
 | succ b ih =>
   intro s
   rw [Function.iterate_succ_apply,← rep_succ b,clean_cons,ih]
def mulSteps (x w : ℕ) : ℕ := (w + 1) + ((x * (2 * w + 3) + 1) + (x + (w + 1)))
lemma mul_run (x w : List Bool) :
   (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
       (some (initList mulTM (x.map Sum.inl ++ w.map Sum.inr))) =
     some (haltList mulTM (rep (x.length * w.length))) := by
 refine (congrArg (fun c => (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
   (some c)) (initList_eq mulTM _)).trans
   (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
 show mulStep^[mulSteps x.length w.length]
   (some (⟨some ci,none,Function.update (fun _ => []) mW
     (x.map Sum.inl ++ w.map Sum.inr)⟩ : MulCfg)) =
   some (⟨none,none,Function.update (fun _ => []) nA (rep (x.length * w.length))⟩ : MulCfg)
 rw [← mstk_start,← mstk_end,mulSteps,Function.iterate_add_apply mulStep (w.length + 1),
   Function.iterate_add_apply mulStep (x.length * (2 * w.length + 3) + 1)]
 have h1 : mulStep^[x.length + (w.length + 1)]
     (some ⟨some ci,none,mstk (x.map Sum.inl ++ w.map Sum.inr) [] [] [] []⟩) =
     some ⟨some bR,none,mstk [] (rep x.length) (rep w.length) [] []⟩ :=
   splitLoopX w x 0 none
 rw [h1]
 have h2 : mulStep^[x.length * (2 * w.length + 3) + 1]
     (some ⟨some bR,none,mstk [] (rep x.length) (rep w.length) [] []⟩) =
     some ⟨some dF,none,mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
   outerLoop w.length x.length 0 none
 rw [h2,cleanLoop]
lemma mul_polyTime :
   Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
     (fun x : List Bool => x)
     (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)) := by
 exact ⟨{
   tm := mulTM
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 3
   outputsFun := fun p =>
     { steps := mulSteps p.1.length p.2.length
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         have := mul_run p.1 p.2
         exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
           p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
           (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
       steps_le_m := by
         simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
           Polynomial.eval_X,Polynomial.eval_pow,encodePair,List.length_append,
           List.length_map,mulSteps]
         nlinarith [Nat.zero_le (p.1.length * p.1.length),
           Nat.zero_le (p.2.length * p.2.length),Nat.zero_le (p.1.length * p.2.length)] } }⟩
end aK.Machines
end S13
section S14
namespace aK.Machines
open PEqualNP.Library
private lemma filterMap_map_some {α β γ : Type} (h : α -> β) (φ : β -> Option γ) (g : α -> γ)
   (hφ : ∀ a,φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
 induction l with
 | nil => rfl
 | cons a l ih => simp [hφ,ih]
private lemma filterMap_map_none {α β γ : Type} (h : α -> β) (φ : β -> Option γ)
   (hφ : ∀ a,φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
 induction l with
 | nil => rfl
 | cons a l ih => simp [hφ,ih]
lemma cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α -> List αΓ} {eb : β -> List βΓ}
   {ec : γ -> List γΓ} {f : α -> β} {g : β -> γ}
   (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
   (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
   PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
 obtain ⟨c1⟩ := hf
 obtain ⟨c2⟩ := hg
 exact comp_polyTime ea eb ec f g c1 c2
lemma cpt_swap :
   PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
     PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2,p.1)) := by
 refine twoPass_polyTime _ _ _
   (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
   (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
   filterMap_map_some Sum.inr _ Sum.inl (fun _ => rfl) w,
   filterMap_map_some Sum.inl _ Sum.inr (fun _ => rfl) x,
   filterMap_map_none Sum.inr _ (fun _ => rfl) w]
 simp
lemma cpt_dup :
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     PEqualNP.Library.encodePair (fun x : List Bool => (x,x)) := by
 refine twoPass_polyTime _ _ _
   (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
 intro x
 have h1 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
   Sum.inl (fun _ => rfl) x
 have h2 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
   Sum.inr (fun _ => rfl) x
 simp only [List.map_id'] at h1 h2
 simp only [encodePair,h1,h2]
lemma cpt_fst :
   PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
     (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
 refine filterMap_polyTime _ _ _
   (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
   filterMap_map_none Sum.inr _ (fun _ => rfl) w]
 simp
lemma cpt_snd :
   PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
     (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
 refine filterMap_polyTime _ _ _
   (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
   filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
 simp
lemma cpt_append :
   PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
     (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
 refine filterMap_polyTime _ _ _
   (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
   filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
 simp
lemma cpt_first {f : List Bool -> List Bool}
   (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) f) :
   PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
     PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1,p.2)) := by
 obtain ⟨c⟩ := hf
 exact first_polyTime f c
lemma cpt_second {g : List Bool -> List Bool}
   (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) g) :
   PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
     PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1,g p.2)) :=
 cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap
lemma cpt_pair {f g : List Bool -> List Bool}
   (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) f)
   (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) g) :
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     PEqualNP.Library.encodePair (fun x : List Bool => (f x,g x)) :=
 cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)
lemma cpt_id :
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) (fun x : List Bool => x) := by
 refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
 intro x
 have h := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
   (fun _ => rfl) x
 simp only [List.map_id'] at h
 exact h.symm
end aK.Machines
end S14
section S15
namespace aK.Machines
open Turing PEqualNP.Library
lemma output_length_poly (f : List Bool -> List Bool)
   (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
   ∃ q : Polynomial ℕ,∀ x : List Bool,(f x).length ≤ q.eval x.length := by
 obtain ⟨c⟩ := hf
 refine ⟨Polynomial.X + Polynomial.C (maxPush c.tm) * c.time,fun x => ?_⟩
 obtain ⟨⟨steps,hev⟩,hle⟩ := c.outputsFun x
 have hev' : (flip bind (TM2.step c.tm.m))^[steps]
     (some (⟨some c.tm.main,c.tm.initialState,Function.update (fun _ => []) c.tm.k₀
       (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
     some (⟨none,c.tm.initialState,Function.update (fun _ => []) c.tm.k₁
       (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
   rw [← initList_eq,← haltList_eq]; exact hev
 have key := run_length c.tm c.tm.k₁ steps _ _ hev'
 simp only [Function.update_self,List.length_map] at key
 have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
     (List.map c.inputAlphabet.invFun x) : ∀ k,List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
   by_cases hk : c.tm.k₁ = c.tm.k₀
   · rw [hk]; simp
   · rw [Function.update_of_ne hk]; simp
 rw [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
 calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
   _ ≤ x.length + maxPush c.tm * c.time.eval x.length :=
     Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _
end aK.Machines
end S15
section S16
namespace aK.Machines
open Turing
def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q -> Γ₀ -> Q × Option Γ₁) (fin : Q -> Option Γ₁) :
   Q -> List Γ₀ -> List Γ₁
 | q,[] => (fin q).toList
 | q,a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l
def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (fin : Q -> Option Γ₁) :
   Q -> List Γ₀ -> List Γ₁
 | q,[] => (fin q).toList
 | q,a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l
lemma fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q -> Γ₀ -> Q × Option Γ₁) (fin : Q -> Option Γ₁)
   (q : Q) (l : List Γ₀) :
   fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1,(δ q a).2,none)) fin q l := by
 induction l generalizing q with
 | nil => rfl
 | cons a l ih => simp [fstRun,fstRun2,ih]
abbrev TrK : Type := Fin 3
abbrev k7 : TrK := 0
abbrev kZ : TrK := 1
abbrev k8 : TrK := 2
variable {Γ₀ Γ₁ Q : Type}
abbrev TrΓ (Γ₀ Γ₁ Q : Type) (k : TrK) : Type :=
 if k.val = 0 then Γ₀ else if k.val = 1 then Q × Option Γ₀ else Γ₁
abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool
def trO1 (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (fin : Q -> Option Γ₁) :
   Q × Option Γ₀ -> Option Γ₁
 | (q,some a) => (δ q a).2.1
 | (q,none) => fin q
def trO2 (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ -> Option Γ₁
 | (q,some a) => (δ q a).2.2
 | (_,none) => none
def trOut (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (fin : Q -> Option Γ₁)
   (e : Q × Option Γ₀) : List Γ₁ :=
 (trO1 δ fin e).toList ++ (trO2 δ e).toList
def trTrace (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) : Q -> List Γ₀ -> List (Q × Option Γ₀)
 | q,[] => [(q,none)]
 | q,a :: l => (q,some a) :: trTrace δ (δ q a).1 l
lemma trTrace_length (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
   (trTrace δ q l).length = l.length + 1 := by
 induction l generalizing q with
 | nil => rfl
 | cons a l ih => simp [trTrace,ih]
lemma trTrace_out (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (fin : Q -> Option Γ₁) (q : Q)
   (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
 induction l generalizing q with
 | nil => simp [trTrace,trOut,trO1,trO2,fstRun2]
 | cons a l ih => simp [trTrace,trOut,trO1,trO2,fstRun2,ih]
def trWrite (o : TrS Γ₀ Q -> Option Γ₁) (d : Option Γ₁)
   (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
   TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
 .branch (fun s => (o s).isSome)
   (match d with
     | some dd => .push k8 (fun s => (o s).getD dd) next
     | none => next)
   next
def trProg (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (fin : Q -> Option Γ₁) (q₀ : Q)
   (d : Option Γ₁) : Bool -> TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
 | false =>
   .pop k7 (fun s o => (s.1,o,o.isSome))
     (.branch (fun s => s.2.2)
       (.push kZ (fun s => (s.1,s.2.1))
         (.load (fun s => (match s.2.1 with
             | some a => (δ s.1 a).1
             | none => s.1,none,false))
           (.goto fun _ => false)))
       (.push kZ (fun s => (s.1,none))
         (.load (fun _ => (q₀,none,false)) (.goto fun _ => true))))
 | true =>
   .pop kZ (fun _ o => match o with
       | some e => (e.1,e.2,true)
       | none => (q₀,none,false))
     (.branch (fun s => s.2.2)
       (trWrite (fun s => trO2 δ (s.1,s.2.1)) d
         (trWrite (fun s => trO1 δ fin (s.1,s.2.1)) d (.goto fun _ => true)))
       .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁)
   (fin : Q -> Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
 K := TrK
 k₀ := k7
 k₁ := k8
 Γ := TrΓ Γ₀ Γ₁ Q
 Λ := Bool
 main := false
 σ := TrS Γ₀ Q
 initialState := (q₀,none,false)
 Γk₀Fin := inferInstanceAs (Fintype Γ₀)
 m := trProg δ fin q₀ d
def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) (k : TrK) : List (TrΓ Γ₀ Γ₁ Q k) :=
 match k with
 | ⟨0,_⟩ => l
 | ⟨1,_⟩ => t
 | ⟨2,_⟩ => u
@[simp] lemma yQ (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : trSt l t u k7 = l := rfl
@[simp] lemma xY (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : trSt l t u kZ = t := rfl
@[simp] lemma ym (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : trSt l t u k8 = u := rfl
lemma trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
   Function.update (trSt l t u) k7 l' = trSt l' t u := by
 funext k; fin_cases k <;> rfl
lemma trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
   Function.update (trSt l t u) kZ t' = trSt l t' u := by
 funext k; fin_cases k <;> rfl
lemma trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
   Function.update (trSt l t u) k8 u' = trSt l t u' := by
 funext k; fin_cases k <;> rfl
lemma trSt_start (l : List Γ₀) :
   (trSt l [] [] : ∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
     Function.update (fun _ => [] : ∀ k,List (TrΓ Γ₀ Γ₁ Q k)) k7 l := by
 funext k; fin_cases k <;> rfl
lemma trSt_end (u : List Γ₁) :
   (trSt [] [] u : ∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
     Function.update (fun _ => [] : ∀ k,List (TrΓ Γ₀ Γ₁ Q k)) k8 u := by
 funext k; fin_cases k <;> rfl
abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
lemma trWrite_stepAux (o : TrS Γ₀ Q -> Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁,d ≠ none)
   (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
   (t : List (Q × Option Γ₀)) (u : List Γ₁) :
   TM2.stepAux (trWrite o d next) s (trSt l t u) =
     TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
 cases ho : o s with
 | none => cases d <;> simp [trWrite,TM2.stepAux,ho]
 | some y =>
   cases d with
   | none => exact absurd rfl (hd y)
   | some dd => simp [trWrite,TM2.stepAux,ho,trSt,trSt_set_out]
variable (δ : Q -> Γ₀ -> Q × Option Γ₁ × Option Γ₁) (fin : Q -> Option Γ₁) (q₀ : Q)
 (d : Option Γ₁)
lemma trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
   (u : List Γ₁) :
   TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
     some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩ := by
 simp [TM2.step,trProg,TM2.stepAux,trSt,trSt_set_inp,trSt_set_tmp]
lemma trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
   TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
     some ⟨some true,(q₀,none,false),trSt [] ((s.1,none) :: t) u⟩ := by
 simp [TM2.step,trProg,TM2.stepAux,trSt,trSt_set_inp,trSt_set_tmp]
lemma trB_cons (hd : ∀ _ : Γ₁,d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
   (t : List (Q × Option Γ₀)) (u : List Γ₁) :
   TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
     some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e ++ u)⟩ := by
 simp only [TM2.step,trProg,TM2.stepAux]
 have e1 : (trSt [] (e :: t) u : ∀ k,List (TrΓ Γ₀ Γ₁ Q k)) kZ = e :: t := rfl
 rw [e1]
 simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
 rw [trSt_set_tmp,trWrite_stepAux _ _ hd,trWrite_stepAux _ _ hd]
 simp [TM2.stepAux,trOut]
lemma trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
   TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
     some ⟨none,(q₀,none,false),trSt [] [] u⟩ := by
 simp [TM2.step,trProg,TM2.stepAux,trSt,trSt_set_tmp]
lemma trLoopA (u : List Γ₁) :
   ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
     (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
         (some (⟨some false,s,trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
       some ⟨some true,(q₀,none,false),trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
 intro l
 induction l with
 | nil => intro t s; exact trA_nil δ fin q₀ d s t u
 | cons a l ih =>
   intro t s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e : flip bind (TM2.step (trProg δ fin q₀ d))
       (some (⟨some false,s,trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
       some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩ :=
     trA_cons δ fin q₀ d s a l t u
   rw [e,ih]
   simp [trTrace]
lemma trLoopB (hd : ∀ _ : Γ₁,d ≠ none) :
   ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
     (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
         (some (⟨some true,s,trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
       some ⟨none,(q₀,none,false),trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
 intro t
 induction t with
 | nil => intro u s; exact trB_nil δ fin q₀ d s u
 | cons e t ih =>
   intro u s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e' : flip bind (TM2.step (trProg δ fin q₀ d))
       (some (⟨some true,s,trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
       some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e ++ u)⟩ :=
     trB_cons δ fin q₀ d hd s e t u
   rw [e',ih]
   simp [List.flatMap_append]
lemma trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁,d ≠ none) (l : List Γ₀) :
   (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
       (some (initList (trM δ fin q₀ d) l)) =
     some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
 refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
   (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
   (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
 show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
   (some (⟨some false,(q₀,none,false),Function.update (fun _ => []) k7 l⟩ :
     TrCfg Γ₀ Γ₁ Q)) =
   some (⟨none,(q₀,none,false),Function.update (fun _ => []) k8 (fstRun2 δ fin q₀ l)⟩ :
     TrCfg Γ₀ Γ₁ Q)
 have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
     (some (⟨some false,(q₀,none,false),trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
     some ⟨some true,(q₀,none,false),trSt [] (trTrace δ q₀ l).reverse []⟩ := by
   have := trLoopA δ fin q₀ d [] l [] (q₀,none,false)
   rw [List.append_nil] at this
   exact this
 have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
     (some (⟨some true,(q₀,none,false),trSt [] (trTrace δ q₀ l).reverse []⟩ :
       TrCfg Γ₀ Γ₁ Q)) =
     some ⟨none,(q₀,none,false),trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
   have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀,none,false)
   rw [List.length_reverse,trTrace_length,List.reverse_reverse,trTrace_out,
     List.append_nil] at this
   exact this
 rw [Function.iterate_add_apply,← trSt_start,hA,hB,trSt_end]
lemma fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α -> List αΓ)
   (eb : β -> List βΓ) (f : α -> β) (δ : Q -> αΓ -> Q × Option βΓ × Option βΓ)
   (fin : Q -> Option βΓ) (q₀ : Q) (h : ∀ a,eb (f a) = fstRun2 δ fin q₀ (ea a)) :
   Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
 classical
 let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
 have hd : ∀ _ : βΓ,d ≠ none := by
   intro y
   have hn : Nonempty βΓ := ⟨y⟩
   simp [d,hn]
 exact ⟨{
   tm := trM δ fin q₀ d
   inputAlphabet := Equiv.refl _
   outputAlphabet := Equiv.refl _
   time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
   outputsFun := fun a =>
     { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
       evals_in_steps := by
         have hm : ∀ (γ : Type) (l : List γ),List.map (Equiv.refl γ).invFun l = l :=
           fun γ l => by simp
         have := trM_run δ fin q₀ d hd (ea a)
         exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
           1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
           (hm αΓ (ea a))).trans
           (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
             ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
       steps_le_m := by
         simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
           Polynomial.eval_X]
         omega } }⟩
lemma fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α -> List αΓ)
   (eb : β -> List βΓ) (f : α -> β) (δ : Q -> αΓ -> Q × Option βΓ) (fin : Q -> Option βΓ) (q₀ : Q)
   (h : ∀ a,eb (f a) = fstRun δ fin q₀ (ea a)) :
   Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
 fst2_polyTime ea eb f (fun q a => ((δ q a).1,(δ q a).2,none)) fin q₀
   (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))
end aK.Machines
end S16
section S17
namespace aK.Machines
open PEqualNP.Library
private lemma cpt_mul {f g : List Bool -> List Bool}
   (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) f)
   (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
     (fun x : List Bool => x) g) :
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun x : List Bool => List.replicate ((f x).length * (g x).length) true) :=
 cpt_comp (cpt_pair hf hg) mul_polyTime
private lemma pow_polyTime
   (hconst : ∀ l : List Bool,PEqualNP.Library.ComputableInPolyTime
     (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
   (n : ℕ) :
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun x : List Bool => List.replicate (x.length ^ n) true) := by
 induction n with
 | zero => simpa using hconst [true]
 | succ n ih =>
   have h := cpt_mul cpt_id ih
   have e : (fun x : List Bool =>
       List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true) =
       (fun x : List Bool => List.replicate (x.length ^ (n + 1)) true) := by
     funext x
     rw [List.length_replicate,pow_succ,Nat.mul_comm]
   rw [← e]
   exact h
lemma clock_polyTime
   (hconst : ∀ l : List Bool,PEqualNP.Library.ComputableInPolyTime
     (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
   (p : Polynomial ℕ) :
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun x : List Bool => List.replicate (p.eval x.length) true) := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
   have h := cpt_comp (cpt_pair hp hq) cpt_append
   have e : (fun x : List Bool => List.replicate (p.eval x.length) true ++
       List.replicate (q.eval x.length) true) =
       (fun x : List Bool => List.replicate ((p + q).eval x.length) true) := by
     funext x
     rw [Polynomial.eval_add,List.replicate_add]
   rw [← e]
   exact h
 | monomial n a =>
   have h := cpt_mul (hconst (List.replicate a true)) (pow_polyTime hconst n)
   have e : (fun x : List Bool => List.replicate ((List.replicate a true).length *
       (List.replicate (x.length ^ n) true).length) true) =
       (fun x : List Bool =>
         List.replicate ((Polynomial.monomial n a).eval x.length) true) := by
     funext x
     rw [List.length_replicate,List.length_replicate,Polynomial.eval_monomial]
   rw [← e]
   exact h
end aK.Machines
end S17
section S18
lemma aK.L055 : ∀ p : Polynomial ℕ,
   PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun x : List Bool => List.replicate (p.eval x.length) true) :=
 fun p => aK.Machines.clock_polyTime
   (fun l => aK.Machines.constList_polyTime l) p
end S18
section S19
namespace aK.Universal
def un (n : ℕ) : List Bool := List.replicate n true
def pairB (a b : List Bool) : List Bool := un a.length ++ false :: (a ++ b)
def unpairB (s : List Bool) : List Bool × List Bool :=
 (((s.dropWhile id).tail).take (s.takeWhile id).length,
  ((s.dropWhile id).tail).drop (s.takeWhile id).length)
lemma unpairB_pairB (a b : List Bool) : unpairB (pairB a b) = (a,b) := by
 have h1 : (pairB a b).takeWhile id = un a.length := by
   simp [pairB,un]
 have h2 : (pairB a b).dropWhile id = false :: (a ++ b) := by
   simp [pairB,un]
 simp [unpairB,h1,h2,un]
end aK.Universal
end S19
section S20
namespace aK.Universal
@[simp] lemma un_zero : un 0 = [] := rfl
@[simp] lemma un_length (n : ℕ) : (un n).length = n := List.length_replicate
lemma un_succ (n : ℕ) : un (n + 1) = true :: un n := rfl
def hd (s : List Bool) : List Bool := s.takeWhile id
def sel (f a b : List Bool) : List Bool := if f = [] then a else b
def mulU (u v : List Bool) : List Bool := un (u.length * v.length)
lemma unpairB_length (s : List Bool) :
   2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
 have h := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := s))
 simp only [List.length_append] at h
 simp only [unpairB,List.length_take,List.length_drop,List.length_tail]
 omega
lemma pairB_length (a b : List Bool) : (pairB a b).length = 2 * a.length + b.length + 1 := by
 simp [pairB]; omega
end aK.Universal
end S20
section S21
namespace aK.Universal
open PEqualNP.Library aK.Machines
private lemma cpt_congr {α β αΓ βΓ : Type} {ea : α -> List αΓ} {eb : β -> List βΓ}
   {f f' : α -> β} (h : ComputableInPolyTime ea eb f) (e : ∀ a,f a = f' a) :
   ComputableInPolyTime ea eb f' := by
 obtain rfl : f = f' := funext e
 exact h
private lemma fm_elim {A B C : Type} (φl : A -> Option C) (φr : B -> Option C) (x : List A)
   (w : List B) :
   (x.map Sum.inl ++ w.map Sum.inr).filterMap (Sum.elim φl φr) =
     x.filterMap φl ++ w.filterMap φr := by
 have h1 : ∀ x : List A,(x.map Sum.inl).filterMap (Sum.elim φl φr) = x.filterMap φl := by
   intro x; induction x with
   | nil => rfl
   | cons a l ih => simp [List.filterMap_cons,ih]
 have h2 : ∀ w : List B,(w.map Sum.inr).filterMap (Sum.elim φl φr) = w.filterMap φr := by
   intro w; induction w with
   | nil => rfl
   | cons a l ih => simp [List.filterMap_cons,ih]
 rw [List.filterMap_append,h1,h2]
private lemma fm_some {A C : Type} (g : A -> C) (l : List A) :
   l.filterMap (fun a => some (g a)) = l.map g := by
 induction l with
 | nil => rfl
 | cons a l ih => simp [ih]
private lemma fm_none {A C : Type} (l : List A) :
   l.filterMap (fun _ : A => (none : Option C)) = [] := by
 induction l with
 | nil => rfl
 | cons a l ih => simp
lemma cpt_pairB :
   ComputableInPolyTime encodePair (fun x : List Bool => x)
     (fun p : List Bool × List Bool => pairB p.1 p.2) := by
 have hA : ComputableInPolyTime encodePair encodePair
     (fun p : List Bool × List Bool => (p.1,p.1 ++ p.2)) := by
   refine twoPass_polyTime _ _ _
     (Sum.elim (fun b : Bool => some (Sum.inl b)) (fun _ : Bool => none))
     (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun b : Bool => some (Sum.inr b))) ?_
   rintro ⟨x,w⟩
   simp only [encodePair]
   rw [fm_elim,fm_elim,fm_some,fm_some,fm_some,fm_none]
   simp
 have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun a : List Bool => a.map (fun _ => true) ++ [false]) := by
   refine fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((),some true))
     (fun _ => some false) () ?_
   intro a
   induction a with
   | nil => rfl
   | cons b l ih =>
     simp only [fstRun,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢
     rw [← ih]; rfl
 refine cpt_congr (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
 rintro ⟨x,w⟩
 simp [pairB,un]
lemma cpt_ifEmpty :
   ComputableInPolyTime encodePair (fun x : List Bool => x)
     (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
 obtain ⟨c⟩ := constList_polyTime []
 have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
 refine cpt_congr (cpt_comp cpt_swap hI) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil => simp
 | cons b l => simp [Function.iterate_succ_apply']
lemma cpt_ifNonempty :
   ComputableInPolyTime encodePair (fun x : List Bool => x)
     (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
 have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun x : List Bool => if x = [] then [true] else []) :=
   cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
 refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil => simp
 | cons b l => simp
private def encT (u : List Bool) : List Bool := u.flatMap (fun b => [true,b])
private def encF (v : List Bool) : List Bool := v.flatMap (fun b => [false,b])
private def twD : Bool -> Bool -> Bool × Option Bool
 | true,true => (true,some true)
 | _,_ => (false,none)
private lemma twD_run (l : List Bool) :
   fstRun twD (fun _ => none) false l = [] /\
     fstRun twD (fun _ => none) true l = l.takeWhile id := by
 induction l with
 | nil => exact ⟨rfl,rfl⟩
 | cons b l ih => cases b <;> simp [fstRun,twD,ih.1,ih.2]
private def e0D : Bool -> Bool -> Bool × Option Bool × Option Bool
 | false,true => (false,none,none)
 | false,false => (true,none,none)
 | true,b => (true,some false,some b)
private lemma e0D_run_true (l : List Bool) :
   fstRun2 e0D (fun _ => none) true l = encF l := by
 induction l with
 | nil => rfl
 | cons b l ih => simp [fstRun2,e0D,encF,ih]
private lemma e0D_run_false (l : List Bool) :
   fstRun2 e0D (fun _ => none) false l = encF (l.dropWhile id).tail := by
 induction l with
 | nil => rfl
 | cons b l ih => cases b <;> simp [fstRun2,e0D,ih,e0D_run_true]
private def mkD : Bool × Bool -> Bool -> (Bool × Bool) × Option Bool
 | (d,false),t => ((d || !t,true),some (t || !d))
 | (d,true),b => ((d,false),some b)
private def mk (l : List Bool) : List Bool := fstRun mkD (fun _ => none) (false,false) l
private lemma mkD_length (q : Bool × Bool) (l : List Bool) :
   (fstRun mkD (fun _ => none) q l).length = l.length := by
 induction l generalizing q with
 | nil => rfl
 | cons b l ih => obtain ⟨d,ph⟩ := q; cases ph <;> simp [fstRun,mkD,ih]
private lemma mkD_done (v : List Bool) :
   fstRun mkD (fun _ => none) (true,false) (encF v) = encF v := by
 induction v with
 | nil => rfl
 | cons b v ih => simp [fstRun,mkD,encF] at ih ⊢; exact ih
private lemma mkD_marked (u r : List Bool) :
   fstRun mkD (fun _ => none) (false,false) (encT u ++ r) =
     encT u ++ fstRun mkD (fun _ => none) (false,false) r := by
 induction u with
 | nil => rfl
 | cons b u ih => simp [fstRun,mkD,encT] at ih ⊢; exact ih
private lemma mk_nil (u : List Bool) : mk (encT u ++ encF []) = encT u ++ encF [] := by
 unfold mk; rw [mkD_marked]; rfl
private lemma mk_cons (u : List Bool) (b : Bool) (v : List Bool) :
   mk (encT u ++ encF (b :: v)) = encT (u ++ [b]) ++ encF v := by
 unfold mk
 rw [mkD_marked]
 have h : fstRun mkD (fun _ => none) (false,false) (encF (b :: v)) =
     true :: b :: encF v := by
   have h' := mkD_done v
   simp [fstRun,mkD,encF] at h' ⊢
   exact h'
 rw [h]
 simp [encT]
private lemma mk_iter (k : ℕ) : ∀ u t : List Bool,
   mk^[k] (encT u ++ encF t) = encT (u ++ t.take k) ++ encF (t.drop k) := by
 induction k with
 | zero => intro u t; simp
 | succ k ih =>
   intro u t
   rw [Function.iterate_succ_apply]
   cases t with
   | nil => rw [mk_nil,ih]; simp
   | cons b t => rw [mk_cons,ih]; simp
private def dcD : Option Bool -> Bool -> Option Bool × Option (Bool ⊕ Bool)
 | none,t => (some t,none)
 | some t,b => (none,some (if t then Sum.inl b else Sum.inr b))
private lemma dcD_F (v : List Bool) :
   fstRun dcD (fun _ => none) none (encF v) = v.map Sum.inr := by
 induction v with
 | nil => rfl
 | cons b v ih => simp [fstRun,dcD,encF] at ih ⊢; exact ih
private lemma dcD_T (u r : List Bool) :
   fstRun dcD (fun _ => none) none (encT u ++ r) =
     u.map Sum.inl ++ fstRun dcD (fun _ => none) none r := by
 induction u with
 | nil => rfl
 | cons b u ih => simp [fstRun,dcD,encT] at ih ⊢; exact ih
private def rawDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
 (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private lemma rawDec_tagged (u v : List Bool) :
   rawDec (u.map Sum.inl ++ v.map Sum.inr) = (u,v) := by
 have h1 : ∀ x : List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
   intro x; induction x with
   | nil => rfl
   | cons a l ih => exact congrArg (a :: ·) ih
 have h2 : ∀ x : List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
   intro x; induction x with
   | nil => rfl
   | cons a l ih => exact ih
 have h3 : ∀ x : List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
   intro x; induction x with
   | nil => rfl
   | cons a l ih => exact ih
 have h4 : ∀ x : List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
   intro x; induction x with
   | nil => rfl
   | cons a l ih => exact congrArg (a :: ·) ih
 simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
lemma cpt_unpairB :
   ComputableInPolyTime (fun x : List Bool => x) encodePair unpairB := by
 have hTw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s : List Bool => s.takeWhile id) :=
   fst_polyTime _ _ _ twD (fun _ => none) true (fun s => (twD_run s).2.symm)
 have hE0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s : List Bool => encF (s.dropWhile id).tail) :=
   fst2_polyTime _ _ _ e0D (fun _ => none) false (fun s => (e0D_run_false s).symm)
 have hMk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk :=
   fst_polyTime _ _ _ mkD (fun _ => none) (false,false) (fun _ => rfl)
 obtain ⟨cMk⟩ := hMk
 have hIt := Iter.iter_polyTime mk cMk 0 (fun y => by simp [mk,mkD_length])
 have hDc : ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l)
     (fun l : List Bool => fstRun dcD (fun _ => none) none l) :=
   fst_polyTime _ _ _ dcD (fun _ => none) none (fun _ => rfl)
 have hRaw : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair rawDec := by
   refine twoPass_polyTime _ _ _
     (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
     (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
   intro l
   simp only [rawDec,encodePair,List.map_filterMap]
 refine cpt_congr (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
 intro s
 have h := mk_iter (s.takeWhile id).length [] (s.dropWhile id).tail
 have e : encT [] ++ encF (s.dropWhile id).tail = encF (s.dropWhile id).tail := rfl
 rw [e] at h
 simp only [h,List.nil_append]
 rw [dcD_T,dcD_F,rawDec_tagged]
 rfl
end aK.Universal
end S21
section S22
namespace aK.Universal
open PEqualNP.Library aK.Machines
private lemma cptc {α β αΓ βΓ : Type} {ea : α -> List αΓ} {eb : β -> List βΓ}
   {f f' : α -> β} (h : ComputableInPolyTime ea eb f) (e : ∀ a,f a = f' a) :
   ComputableInPolyTime ea eb f' := by
 obtain rfl : f = f' := funext e
 exact h
private def hdD : Bool -> Bool -> Bool × Option Bool
 | true,true => (true,some true)
 | _,_ => (false,none)
private lemma hdD_run (l : List Bool) :
   fstRun hdD (fun _ => none) false l = [] /\
     fstRun hdD (fun _ => none) true l = l.takeWhile id := by
 induction l with
 | nil => exact ⟨rfl,rfl⟩
 | cons b l ih => cases b <;> simp [fstRun,hdD,ih.1,ih.2]
lemma cpt_hd :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) hd :=
 fst_polyTime _ _ _ hdD (fun _ => none) true (fun s => (hdD_run s).2.symm)
private def tlD : Bool -> Bool -> Bool × Option Bool
 | false,_ => (true,none)
 | true,b => (true,some b)
private lemma tlD_true (l : List Bool) : fstRun tlD (fun _ => none) true l = l := by
 induction l with
 | nil => rfl
 | cons b l ih => simp [fstRun,tlD,ih]
private lemma tlD_false (l : List Bool) : fstRun tlD (fun _ => none) false l = l.tail := by
 cases l with
 | nil => rfl
 | cons b l => simp [fstRun,tlD,tlD_true]
lemma cpt_tail :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s : List Bool => s.tail) :=
 fst_polyTime _ _ _ tlD (fun _ => none) false (fun s => (tlD_false s).symm)
lemma cpt_const (l : List Bool) :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun _ : List Bool => l) :=
 constList_polyTime l
lemma cpt_mulU :
   ComputableInPolyTime encodePair (fun x : List Bool => x)
     (fun p : List Bool × List Bool => mulU p.1 p.2) :=
 cptc mul_polyTime (fun _ => rfl)
lemma cpt_unpairB1 :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s : List Bool => (unpairB s).1) :=
 cptc (cpt_comp cpt_unpairB cpt_fst) (fun _ => rfl)
lemma cpt_unpairB2 :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s : List Bool => (unpairB s).2) :=
 cptc (cpt_comp cpt_unpairB cpt_snd) (fun _ => rfl)
lemma cpt_app2 {u v : List Bool -> List Bool}
   (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
   (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s => u s ++ v s) :=
 cptc (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ => rfl)
lemma cpt_pairB2 {u v : List Bool -> List Bool}
   (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
   (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s => pairB (u s) (v s)) :=
 cptc (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ => rfl)
lemma cpt_mulU2 {u v : List Bool -> List Bool}
   (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
   (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s => mulU (u s) (v s)) :=
 cptc (cpt_comp (cpt_pair hu hv) cpt_mulU) (fun _ => rfl)
lemma cpt_sel {f a b : List Bool -> List Bool}
   (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
   (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
   (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s => sel (f s) (a s) (b s)) := by
 have h1 := cpt_comp (cpt_pair hf ha) cpt_ifEmpty
 have h2 := cpt_comp (cpt_pair hf hb) cpt_ifNonempty
 refine cptc (cpt_app2 h1 h2) ?_
 intro s
 by_cases h : f s = [] <;> simp [sel,h]
lemma cpt_iterLen {g cnt arg : List Bool -> List Bool}
   (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
   (hgl : ∀ s,(g s).length ≤ s.length)
   (hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt)
   (harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg) :
   ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
     (fun s => g^[(cnt s).length] (arg s)) := by
 obtain ⟨c⟩ := hg
 have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
     (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
   Iter.iter_polyTime g c 0 (fun y => by simpa using hgl y)
 exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)
end aK.Universal
end S22
section S23
namespace aK.Universal
open PEqualNP.Library aK.Machines
private lemma tV {f f' : List Bool -> List Bool} (h : aK.CPTs f) (e : ∀ a,f a = f' a) : aK.CPTs f' := by
 obtain rfl : f = f' := funext e; exact h
lemma cpt_hd1 {f : List Bool -> List Bool} (hf : aK.CPTs f) : aK.CPTs (fun y => hd (f y)) :=
 cpt_comp hf cpt_hd
lemma cpt_tail1 {f : List Bool -> List Bool} (hf : aK.CPTs f) : aK.CPTs (fun y => (f y).tail) :=
 cpt_comp hf cpt_tail
lemma cpt_unpairB1_1 {f : List Bool -> List Bool} (hf : aK.CPTs f) :
   aK.CPTs (fun y => (unpairB (f y)).1) := cpt_comp (g := fun s => (unpairB s).1) hf cpt_unpairB1
lemma cpt_unpairB2_1 {f : List Bool -> List Bool} (hf : aK.CPTs f) :
   aK.CPTs (fun y => (unpairB (f y)).2) := cpt_comp (g := fun s => (unpairB s).2) hf cpt_unpairB2
lemma cpt_cons1 (b : Bool) {f : List Bool -> List Bool} (hf : aK.CPTs f) :
   aK.CPTs (fun y => b :: f y) :=
 tV (cpt_app2 (cpt_const [b]) hf) (fun _ => rfl)
end aK.Universal
end S23
section S24
namespace aK.Loop
open PEqualNP.Library aK.Machines aK.Universal
lemma cptE {f f' : List Bool -> List Bool} (h : aK.CPTs f) (e : ∀ a,f a = f' a) :
   aK.CPTs f' := by
 obtain rfl : f = f' := funext e
 exact h
lemma cpt_iterMeasure {g cnt arg : List Bool -> List Bool} (hg : aK.CPTs g)
   (m : List Bool -> ℕ) (a : ℕ) (hm : ∀ y,m (g y) ≤ m y)
   (hgl : ∀ y,(g y).length ≤ y.length + m y) (ha : ∀ y,m y ≤ a * y.length + a)
   (hcnt : aK.CPTs cnt) (harg : aK.CPTs arg) :
   aK.CPTs (fun s => g^[(cnt s).length] (arg s)) := by
 obtain ⟨c⟩ := hg
 exact cptE (cpt_comp (cpt_pair harg hcnt) (Iter.iter_polyTime_measure g c m a hm hgl ha))
   (fun _ => rfl)
def tk (p w : List Bool) : List Bool := (unpairB (mulU p [true] ++ false :: w)).1
lemma tk_eq (p w : List Bool) : tk p w = w.take p.length := by
 have h1 : (mulU p [true] ++ false :: w).takeWhile id = un p.length := by
   simp [mulU,un]
 have h2 : (mulU p [true] ++ false :: w).dropWhile id = false :: w := by
   simp [mulU,un]
 simp [tk,unpairB,h1,h2,un]
lemma tk_length (p w : List Bool) : (tk p w).length ≤ p.length := by
 rw [tk_eq,List.length_take]
 exact Nat.min_le_left _ _
lemma cpt_tk {p w : List Bool -> List Bool} (hp : aK.CPTs p) (hw : aK.CPTs w) :
   aK.CPTs (fun s => tk (p s) (w s)) :=
 cpt_unpairB1_1 (cpt_app2 (cpt_mulU2 hp (cpt_const [true])) (cpt_cons1 false hw))
def lstep (f : List Bool -> List Bool) (y : List Bool) : List Bool :=
 pairB (unpairB y).1 (pairB (unpairB (unpairB y).2).1.tail
   (pairB (unpairB (unpairB (unpairB y).2).2).1
     (tk (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
       (unpairB (unpairB (unpairB y).2).2).1)) ++ (unpairB (unpairB (unpairB y).2).2).2)))
lemma cpt_lstep {f : List Bool -> List Bool} (hf : aK.CPTs f) : aK.CPTs (lstep f) := by
 have h1 : aK.CPTs (fun y => (unpairB y).1) := cpt_unpairB1
 have h2 : aK.CPTs (fun y => (unpairB y).2) := cpt_unpairB2
 have hr := cpt_tail1 (cpt_unpairB1_1 h2)
 have h3 := cpt_unpairB2_1 h2
 have harg := cpt_unpairB1_1 h3
 have hacc := cpt_unpairB2_1 h3
 exact cpt_pairB2 h1 (cpt_pairB2 hr (cpt_pairB2 harg
   (cpt_app2 (cpt_tk h1 (cpt_comp (cpt_pairB2 hr harg) hf)) hacc)))
lemma lstep_pairB (f : List Bool -> List Bool) (pad r arg acc : List Bool) :
   lstep f (pairB pad (pairB r (pairB arg acc))) =
     pairB pad (pairB r.tail (pairB arg (tk pad (f (pairB r.tail arg)) ++ acc))) := by
 simp only [lstep,unpairB_pairB]
lemma lstep_measure (f : List Bool -> List Bool) (y : List Bool) :
   (unpairB (lstep f y)).1.length + 3 ≤ (unpairB y).1.length + 3 := by
 simp only [lstep,unpairB_pairB]
 exact le_rfl
lemma lstep_length (f : List Bool -> List Bool) (y : List Bool) :
   (lstep f y).length ≤ y.length + ((unpairB y).1.length + 3) := by
 have h1 := unpairB_length y
 have h2 := unpairB_length (unpairB y).2
 have h3 := unpairB_length (unpairB (unpairB y).2).2
 have h4 := tk_length (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
       (unpairB (unpairB (unpairB y).2).2).1))
 have h5 : (unpairB (unpairB y).2).1.tail.length ≤ (unpairB (unpairB y).2).1.length := by
   simp
 simp only [lstep,pairB_length,List.length_append]
 omega
lemma lstep_iter (f : List Bool -> List Bool) (pad arg : List Bool) (n : ℕ)
   (hpad : ∀ i < n,(f (pairB (un i) arg)).length ≤ pad.length) (acc : List Bool) :
   (lstep f)^[n] (pairB pad (pairB (un n) (pairB arg acc))) =
     pairB pad (pairB [] (pairB arg
       ((List.range n).flatMap (fun i => f (pairB (un i) arg)) ++ acc))) := by
 induction n generalizing acc with
 | zero => simp
 | succ n ih =>
   rw [Function.iterate_succ_apply,lstep_pairB,un_succ,List.tail_cons,tk_eq,
     List.take_of_length_le (hpad n (by omega)),ih (fun i hi => hpad i (by omega)),
     List.range_succ,List.flatMap_append]
   simp
lemma cpt_flatMapRange {f cnt arg : List Bool -> List Bool} (hf : aK.CPTs f) (hcnt : aK.CPTs cnt)
   (harg : aK.CPTs arg) :
   aK.CPTs (fun s => (List.range (cnt s).length).flatMap fun i => f (pairB (un i) (arg s))) := by
 obtain ⟨P,hP⟩ := output_length_poly f hf
 have hpad : aK.CPTs (fun s => List.replicate (P.eval (pairB (cnt s) (arg s)).length) true) :=
   cpt_comp (cpt_pairB2 hcnt harg) (aK.L055 P)
 have hun : aK.CPTs (fun s => mulU (cnt s) [true]) := cpt_mulU2 hcnt (cpt_const [true])
 have hinit := cpt_pairB2 hpad (cpt_pairB2 hun (cpt_pairB2 harg (cpt_const [])))
 have hit := cpt_iterMeasure (cpt_lstep hf) (fun y => (unpairB y).1.length + 3) 3
   (lstep_measure f) (lstep_length f)
   (fun y => by have := unpairB_length y; omega) hcnt hinit
 have hout := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hit))
 refine cptE hout (fun s => ?_)
 have e : mulU (cnt s) [true] = un (cnt s).length := by simp [mulU]
 have hb : ∀ i < (cnt s).length,(f (pairB (un i) (arg s))).length ≤
     (List.replicate (P.eval (pairB (cnt s) (arg s)).length) true).length := by
   intro i hi
   rw [List.length_replicate]
   refine (hP _).trans (eval_mono P ?_)
   rw [pairB_length,pairB_length,un_length]
   omega
 show (unpairB (unpairB (unpairB ((lstep f)^[(cnt s).length]
   (pairB _ (pairB (mulU (cnt s) [true]) (pairB (arg s) []))))).2).2).2 = _
 rw [e,lstep_iter f _ (arg s) (cnt s).length hb,unpairB_pairB,unpairB_pairB,unpairB_pairB]
 simp
end aK.Loop
end S24
namespace aK.R
open PEqualNP.Library aK.Machines aK.Universal aK.Loop
def aM (v : List ℕ) : List Bool := v.flatMap (fun a => false :: un a)
def dbl (w : List Bool) : List Bool := w.flatMap (fun b => [true,b])
def encLL (S : List (List ℕ)) : List Bool := S.flatMap (fun v => false :: dbl (aM v))
def fo : List Bool -> ℕ × List ℕ
 | [] => (0,[])
 | true :: r => ((fo r).1 + 1,(fo r).2)
 | false :: r => (0,(fo r).1 :: (fo r).2)
def iS (w : List Bool) : List ℕ := (fo w).2
@[local simp] lemma zi : aM [] = [] := rfl
@[local simp] lemma oe (a : ℕ) (v : List ℕ) : aM (a :: v) = false :: (un a ++ aM v) := rfl
@[local simp] lemma y7 (v w : List ℕ) : aM (v ++ w) = aM v ++ aM w := by simp [aM]
@[local simp] lemma za : dbl [] = [] := rfl
@[local simp] lemma y9 (b : Bool) (w : List Bool) : dbl (b :: w) = true :: b :: dbl w := rfl
@[local simp] lemma zm : encLL [] = [] := rfl
@[local simp] lemma zd (v : List ℕ) (S : List (List ℕ)) :
   encLL (v :: S) = false :: (dbl (aM v) ++ encLL S) := rfl
@[local simp] lemma zh (S T : List (List ℕ)) : encLL (S ++ T) = encLL S ++ encLL T := by
 simp [encLL]
lemma v5 (a : ℕ) (w : List Bool) : fo (un a ++ w) = ((fo w).1 + a,(fo w).2) := by
 induction a with
 | zero => rfl
 | succ a ih => simp only [un_succ,List.cons_append,fo,ih,Nat.add_assoc]
lemma dh (v : List ℕ) : iS (aM v) = v := by
 have : ∀ v,fo (aM v) = (0,v) := by
   intro v; induction v with
   | nil => rfl
   | cons a v ih => simp [fo,v5,ih]
 simp [iS,this]
lemma wn (w : List Bool) : un (fo w).1 ++ aM (fo w).2 = w := by
 induction w with
 | nil => rfl
 | cons b w ih => cases b <;> simp [fo,un_succ,ih]
lemma uH (w : List Bool) : aM (iS w) = w.dropWhile id := by
 induction w with
 | nil => rfl
 | cons b w ih =>
   cases b
   · simpa [iS,fo] using wn w
   · simpa [iS,fo] using ih
def aj (f : List Bool -> ℕ) : Prop := aK.CPTs (fun s => un (f s))
def cX (f : List Bool -> List ℕ) : Prop := aK.CPTs (fun s => aM (f s))
lemma vr {Q : Type} [Fintype Q] (δ : Q -> Bool -> Q × Option Bool) (fin : Q -> Option Bool)
   (q : Q) : aK.CPTs (fstRun δ fin q) := fst_polyTime _ _ _ δ fin q (fun _ => rfl)
lemma sD (φ : Bool -> Option Bool) : aK.CPTs (fun w => w.filterMap φ) :=
 cptE (vr (fun (_ : Unit) b => ((),φ b)) (fun _ => none) ()) (fun w => by
   induction w with
   | nil => rfl
   | cons b l ih => simp only [fstRun]; rw [ih]; cases h : φ b <;> simp [h])
def oy : Bool -> Bool -> Bool × Option Bool
 | false,true => (false,none)
 | false,false => (true,some false)
 | true,b => (true,some b)
lemma tE : aK.CPTs (fun l => l.dropWhile id) := by
 have ht : ∀ l,fstRun oy (fun _ => none) true l = l := by
   intro l; induction l with
   | nil => rfl
   | cons b l ih => simp [fstRun,oy,ih]
 refine cptE (vr oy (fun _ => none) false) (fun l => ?_)
 induction l with
 | nil => rfl
 | cons b l ih => cases b <;> simp [fstRun,oy,ih,ht]
lemma sF (x : ℕ) (w : List Bool) : unpairB (un x ++ false :: w) = (w.take x,w.drop x) := by
 have h1 : (un x ++ false :: w).takeWhile id = un x := by simp [un]
 have h2 : (un x ++ false :: w).dropWhile id = false :: w := by simp [un]
 simp [unpairB,h1,h2]
lemma xC (l : List Bool) : hd l = un (l.takeWhile id).length :=
 List.eq_replicate_iff.2 ⟨rfl,fun b hb => by simpa using List.mem_takeWhile_imp hb⟩
lemma xz {α : Type} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
 induction l generalizing i with
 | nil => simp
 | cons a l ih => cases i <;> simp
lemma vT {α : Type} (E : List α -> List Bool) (f : List Bool -> List Bool)
   (hf : ∀ S,f (E S) = E S.tail) (n : ℕ) (S : List α) : f^[n] (E S) = E (S.drop n) := by
 induction n generalizing S with
 | zero => rfl
 | succ n ih => rw [Function.iterate_succ_apply,hf,ih,List.drop_tail]
def nJ (g : List Bool -> List Bool) (y : List Bool) : List Bool :=
 pairB (unpairB y).1 (tk (unpairB y).1 (g (unpairB y).2))
lemma xL (g : List Bool -> List Bool) (y : List Bool) :
   (unpairB (nJ g y)).1.length + 1 ≤ (unpairB y).1.length + 1 := by
 simp [nJ,unpairB_pairB]
lemma xm (g : List Bool -> List Bool) (y : List Bool) :
   (nJ g y).length ≤ y.length + ((unpairB y).1.length + 1) := by
 have h1 := unpairB_length y
 have h2 := tk_length (unpairB y).1 (g (unpairB y).2)
 simp only [nJ,pairB_length]; omega
lemma xK (y : List Bool) : (unpairB y).1.length + 1 ≤ 1 * y.length + 1 := by
 have := unpairB_length y; omega
lemma vF (g : List Bool -> List Bool) (pad y : List Bool) (n : ℕ)
   (h : ∀ i ≤ n,(g^[i] y).length ≤ pad.length) :
   (nJ g)^[n] (pairB pad y) = pairB pad (g^[n] y) := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [Function.iterate_succ_apply' (nJ g),ih (fun i hi => h i (by omega)),
     Function.iterate_succ_apply' g]
   simp only [nJ,unpairB_pairB,tk_eq]
   have := h (n + 1) le_rfl
   rw [Function.iterate_succ_apply'] at this
   rw [List.take_of_length_le this]
lemma pO {g cnt arg : List Bool -> List Bool} (hg : aK.CPTs g) (hcnt : aK.CPTs cnt)
   (harg : aK.CPTs arg) (P : Polynomial ℕ)
   (hb : ∀ s,∀ i ≤ (cnt s).length,(g^[i] (arg s)).length ≤ P.eval s.length) :
   aK.CPTs (fun s => g^[(cnt s).length] (arg s)) := by
 have hG : aK.CPTs (nJ g) :=
   cpt_pairB2 cpt_unpairB1 (cpt_tk cpt_unpairB1 (cpt_comp cpt_unpairB2 hg))
 have hit := cpt_iterMeasure hG (fun y => (unpairB y).1.length + 1) 1 (xL g) (xm g) xK
   hcnt (cpt_pairB2 (aK.L055 P) harg)
 exact cptE (cpt_unpairB2_1 hit) (fun s => by
   rw [vF g _ _ _ (fun i hi => by simpa using hb s i hi),unpairB_pairB])
lemma qn {F init cnt : List Bool -> List Bool} (hF : aK.CPTs F) (hi : aK.CPTs init)
   (hc : aK.CPTs cnt) (P : Polynomial ℕ)
   (hb : ∀ s,∀ i ≤ (cnt s).length,
     ((fun a => F (pairB a s))^[i] (init s)).length ≤ P.eval s.length) :
   aK.CPTs (fun s => (fun a => F (pairB a s))^[(cnt s).length] (init s)) := by
 have e : ∀ s i a,(fun y => pairB (F y) (unpairB y).2)^[i] (pairB a s) =
     pairB ((fun a => F (pairB a s))^[i] a) s := by
   intro s i; induction i with
   | zero => intro a; rfl
   | succ i ih => intro a; simp only [Function.iterate_succ_apply,unpairB_pairB,ih]
 have h := pO (cpt_pairB2 hF cpt_unpairB2) hc (cpt_pairB2 hi cpt_id)
   (Polynomial.C 2 * P + Polynomial.X + Polynomial.C 1) (fun s i hi => by
     rw [e,pairB_length]; have := hb s i hi
     simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
     omega)
 exact cptE (cpt_unpairB1_1 h) (fun s => by rw [e,unpairB_pairB])
lemma wo (F : List Bool -> List Bool) (φ : ℕ -> ℕ) (s : List Bool)
   (hF : ∀ x,F (pairB (un x) s) = un (φ x)) :
   ∀ i x,(fun a => F (pairB a s))^[i] (un x) = un (φ^[i] x) := by
 intro i; induction i with
 | zero => intro x; rfl
 | succ i ih => intro x; simp only [Function.iterate_succ_apply,hF,ih]
lemma k6 {φ : List Bool -> ℕ -> ℕ} {x0 n : List Bool -> ℕ}
   (hφ : aj (fun t => φ (unpairB t).2 (unpairB t).1.length)) (hx : aj x0) (hn : aj n)
   (P : Polynomial ℕ) (hb : ∀ s,∀ i ≤ n s,(φ s)^[i] (x0 s) ≤ P.eval s.length) :
   aj (fun s => (φ s)^[n s] (x0 s)) := by
 have e : ∀ s i x,(fun a => un (φ (unpairB (pairB a s)).2 (unpairB (pairB a s)).1.length))^[i]
     (un x) = un ((φ s)^[i] x) := fun s =>
   wo (fun t => un (φ (unpairB t).2 (unpairB t).1.length)) (φ s) s
     (fun x => by simp only [unpairB_pairB,un_length])
 have h := qn (F := fun t => un (φ (unpairB t).2 (unpairB t).1.length))
   (init := fun s => un (x0 s)) (cnt := fun s => un (n s)) hφ hx hn P
   (fun s i hi => by rw [e,un_length]; exact hb s i (by simpa using hi))
 exact cptE h (fun s => by rw [un_length,e])
lemma tK (C : ℕ -> Prop) [DecidablePred C] (i : ℕ) :
   (fun q => if C q then q else q + 1)^[i] 0 ≤ i := by
 induction i with
 | zero => exact le_rfl
 | succ i ih => rw [Function.iterate_succ_apply']; split_ifs <;> omega
lemma tj (C : ℕ -> Prop) [DecidablePred C] (m : ℕ) (hC : ∀ q,C q ↔ m < q + 1) (i : ℕ) :
   (fun q => if C q then q else q + 1)^[i] 0 = min i m := by
 induction i with
 | zero => simp
 | succ i ih =>
   rw [Function.iterate_succ_apply',ih]
   split_ifs with h
   · have := (hC _).1 h; omega
   · have := mt (hC _).2 h; omega
lemma sL {a : List Bool -> ℕ} (ha : aj a) : ∃ P : Polynomial ℕ,∀ s,a s ≤ P.eval s.length := by
 obtain ⟨P,hP⟩ := output_length_poly _ ha
 exact ⟨P,fun s => by simpa using hP s⟩
lemma s9 (n : ℕ) (x y : List Bool) : sel (un n) x y = if n = 0 then x else y := by
 cases n <;> simp [sel,un]
lemma ac (k : ℕ) : aj (fun _ => k) := cpt_const (un k)
lemma um {p : List Bool -> List Bool} (hp : aK.CPTs p) : aj (fun s => (p s).length) :=
 cptE (cpt_mulU2 hp (cpt_const [true])) (fun s => by simp [mulU])
lemma af {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) : aj (fun s => a s + b s) :=
 cptE (cpt_app2 ha hb) (fun s => by simp only [un,List.replicate_add])
lemma dj {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) : aj (fun s => a s - b s) :=
 cptE (cpt_unpairB2_1 (cpt_app2 hb (cpt_cons1 false ha))) (fun s => by
   rw [sF]; simp [un])
lemma ag {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) : aj (fun s => a s * b s) :=
 cptE (cpt_mulU2 ha hb) (fun s => by simp [mulU])
lemma tC {a b : List Bool -> ℕ} {x y : List Bool -> List Bool} (ha : aj a) (hb : aj b)
   (hx : aK.CPTs x) (hy : aK.CPTs y) : aK.CPTs (fun s => if a s < b s then x s else y s) :=
 cptE (cpt_sel (dj hb ha) hy hx) (fun s => by
   dsimp only; rw [s9]; by_cases h : a s < b s
   · simp only [h,↓reduceIte,show ¬ b s - a s = 0 by omega,↓reduceIte]
   · simp only [h,↓reduceIte,show b s - a s = 0 by omega,↓reduceIte])
lemma s8 {a b : List Bool -> ℕ} {x y : List Bool -> List Bool} (ha : aj a) (hb : aj b)
   (hx : aK.CPTs x) (hy : aK.CPTs y) : aK.CPTs (fun s => if a s = b s then x s else y s) :=
 cptE (cpt_sel (af (dj ha hb) (dj hb ha)) hx hy) (fun s => by
   dsimp only; rw [s9]; by_cases h : a s = b s
   · simp only [h,↓reduceIte,show b s - b s + (b s - b s) = 0 by omega]
   · simp only [h,↓reduceIte,show ¬ a s - b s + (b s - a s) = 0 by omega])
lemma og {a b x y : List Bool -> ℕ} (ha : aj a) (hb : aj b) (hx : aj x) (hy : aj y) :
   aj (fun s => if a s < b s then x s else y s) :=
 cptE (tC ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
lemma qV {a b x y : List Bool -> ℕ} (ha : aj a) (hb : aj b) (hx : aj x) (hy : aj y) :
   aj (fun s => if a s = b s then x s else y s) :=
 cptE (s8 ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
lemma jq : aj (fun t => (unpairB t).1.length) := um cpt_unpairB1
lemma ox {a : List Bool -> ℕ} (ha : aj a) : aj (fun t => a (unpairB t).2) := by
 unfold aj at *
 exact cpt_comp (f := fun t => (unpairB t).2) (g := fun s => un (a s)) cpt_unpairB2 ha
lemma di {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) : aj (fun s => a s / b s) := by
 obtain ⟨P,hP⟩ := sL ha
 have hφ := og (ox ha) (ag (af jq (ac 1)) (ox hb)) jq
   (af jq (ac 1))
 have h := k6 (φ := fun s q => if a s < (q + 1) * b s then q else q + 1) hφ
   (ac 0) ha P (fun s i hi => (tK _ i).trans (hi.trans (hP s)))
 refine cptE (qV hb (ac 0) (ac 0) h) (fun s => ?_)
 dsimp only
 by_cases h0 : b s = 0
 · simp [h0]
 · simp only [h0,↓reduceIte]
   rw [tj (fun q => a s < (q + 1) * b s) (a s / b s)
     (fun q => (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero h0)).symm) (a s),
     min_eq_right (Nat.div_le_self _ _)]
lemma dk {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) : aj (fun s => a s % b s) :=
 cptE (dj ha (ag hb (di ha hb))) (fun s => by dsimp only; rw [Nat.mod_eq_sub_mul_div])
lemma rr (i x : ℕ) : (fun x => x / 2)^[i] x = x / 2 ^ i := by
 induction i generalizing x with
 | zero => simp
 | succ i ih => rw [Function.iterate_succ_apply,ih,Nat.div_div_eq_div_mul,pow_succ']
lemma qp {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) :
   aj (fun s => a s / 2 ^ b s) := by
 obtain ⟨P,hP⟩ := sL ha
 have h := k6 (φ := fun _ x => x / 2) (di jq (ac 2)) ha hb P
   (fun s i _ => by rw [rr]; exact (Nat.div_le_self _ _).trans (hP s))
 exact cptE h (fun s => by dsimp only; rw [rr])
lemma tU {a : List Bool -> ℕ} (ha : aj a) : aj (fun s => (a s).log2) := by
 obtain ⟨P,hP⟩ := sL ha
 have hφ := og (qp (ox ha) (af jq (ac 1))) (ac 1)
   jq (af jq (ac 1))
 have h := k6 (φ := fun s q => if a s / 2 ^ (q + 1) < 1 then q else q + 1) hφ
   (ac 0) ha P (fun s i hi => (tK _ i).trans (hi.trans (hP s)))
 refine cptE h (fun s => ?_)
 dsimp only
 rw [tj (fun q => a s / 2 ^ (q + 1) < 1) (a s).log2 (fun q => ?_) (a s),
   min_eq_right (Nat.log2_le_self _)]
 rcases Nat.eq_zero_or_pos (a s) with h0 | h0
 · simp [h0]
 · rw [Nat.div_lt_iff_lt_mul (by positivity),one_mul,Nat.log2_lt h0.ne']
lemma uE (i : ℕ) : (fun x => x + x)^[i] 1 = 2 ^ i := by
 induction i with
 | zero => rfl
 | succ i ih => rw [Function.iterate_succ_apply',ih,pow_succ]; omega
lemma tZ {b : List Bool -> ℕ} (hb : aj b) (P : Polynomial ℕ)
   (hP : ∀ s,2 ^ b s ≤ P.eval s.length) : aj (fun s => 2 ^ b s) := by
 have h := k6 (φ := fun _ x => x + x) (af jq jq) (ac 1) hb P
   (fun s i hi => by rw [uE]; exact (Nat.pow_le_pow_right (by norm_num) hi).trans (hP s))
 exact cptE h (fun s => by dsimp only; rw [uE])
lemma sZ {a b : List Bool -> ℕ} {x y : List Bool -> List Bool} (ha : aj a) (hb : aj b)
   (hx : aK.CPTs x) (hy : aK.CPTs y) : aK.CPTs (fun s => if a s < b s then x s else y s) :=
 tC ha hb hx hy
lemma sS {a b : List Bool -> ℕ} {x y : List Bool -> List Bool} (ha : aj a) (hb : aj b)
   (hx : aK.CPTs x) (hy : aK.CPTs y) : aK.CPTs (fun s => if a s = b s then x s else y s) :=
 s8 ha hb hx hy
lemma bO {p : List Bool -> List Bool} {k : List Bool -> ℕ} (hp : aK.CPTs p) (hk : aj k) :
   aj (fun s => if (p s).getD (k s) false then 1 else 0) := by
 have h := cpt_comp (cpt_tk (cpt_const [true]) (cpt_unpairB2_1 (cpt_app2 hk (cpt_cons1 false hp))))
   (sD (fun b => if b then some true else none))
 refine cptE h (fun s => ?_)
 simp only [tk_eq,sF,List.length_singleton]
 rw [List.getD_eq_getElem?_getD,← List.head?_drop]
 rcases (p s).drop (k s) with _ | ⟨_ | _,l⟩ <;> simp [un]
lemma jY {p : List Bool -> List Bool} {k : List Bool -> ℕ} (hp : aK.CPTs p) (hk : aj k) :
   aj (fun s => (((p s).drop (k s)).takeWhile id).length) :=
 cptE (cpt_hd1 (cpt_unpairB2_1 (cpt_app2 hk (cpt_cons1 false hp)))) (fun s => by
   rw [sF]; exact xC _)
lemma dO {p : List Bool -> List Bool} (hp : aK.CPTs p) : cX (fun s => iS (p s)) :=
 cptE (cpt_comp hp tE) (fun _ => (uH _).symm)
lemma oO : cX (fun _ => []) := cpt_const []
lemma aN {a : List Bool -> ℕ} (ha : aj a) : cX (fun s => [a s]) :=
 cptE (cpt_cons1 false ha) (fun s => by simp)
lemma aR {v w : List Bool -> List ℕ} (hv : cX v) (hw : cX w) :
   cX (fun s => v s ++ w s) :=
 cptE (cpt_app2 hv hw) (fun s => by simp)
lemma vJ (a : ℕ) (w : List Bool) : (un a ++ w).dropWhile id = w.dropWhile id := by
 induction a with
 | zero => rfl
 | succ a ih => simpa [un_succ] using ih
lemma wM (v : List ℕ) : (aM v).takeWhile id = [] := by cases v <;> rfl
lemma wJ (v : List ℕ) : ((aM v).tail).dropWhile id = aM v.tail := by
 cases v with
 | nil => rfl
 | cons a v => simp only [oe,List.tail_cons,vJ]; cases v <;> rfl
lemma wH (w : List ℕ) : hd (aM w).tail = un (w.headD 0) := by
 cases w with
 | nil => rfl
 | cons a w =>
   simp only [oe,List.tail_cons,hd,List.headD_cons]
   rw [List.takeWhile_append_of_pos (by simp [un]),wM,List.append_nil]
lemma bt {v : List Bool -> List ℕ} {i : List Bool -> ℕ} (hv : cX v) (hi : aj i) :
   aj (fun s => (v s).getD (i s) 0) := by
 have h := cpt_iterLen (g := fun y => (y.tail).dropWhile id) (cpt_comp cpt_tail tE)
   (fun y => (List.IsSuffix.length_le (List.dropWhile_suffix (l := y.tail) id)).trans (by simp))
   hi hv
 exact cptE (cpt_hd1 (cpt_tail1 h)) (fun s => by
   rw [un_length,vT aM (fun y => (y.tail).dropWhile id) wJ,wH,xz])
lemma qf {v : List Bool -> List ℕ} (hv : cX v) : aj (fun s => (v s).length) := by
 have e : ∀ v : List ℕ,(aM v).filterMap (fun b => if b then none else some true) = un v.length := by
   intro v; induction v with
   | nil => rfl
   | cons a v ih =>
     simp only [oe,List.filterMap_cons,List.filterMap_append,ih]
     simp [un,List.filterMap_replicate_of_none,List.replicate_succ]
 exact cptE (cpt_comp hv (sD _)) (fun s => e _)
lemma bU {v : List Bool -> List ℕ} (hv : cX v) : aj (fun s => (v s).sum) := by
 have e : ∀ v : List ℕ,(aM v).filterMap (fun b => if b then some true else none) = un v.sum := by
   intro v; induction v with
   | nil => rfl
   | cons a v ih =>
     simp only [oe,List.filterMap_cons,List.filterMap_append,ih]
     simp [un]
 exact cptE (cpt_comp hv (sD _)) (fun s => e _)
lemma aV {A : List Bool -> List Bool} {n : List Bool -> ℕ} {G : ℕ -> List Bool -> ℕ}
   (hA : aK.CPTs A) (hn : aj n) (hG : aj (fun t => G (unpairB t).1.length (unpairB t).2)) :
   cX (fun s => (List.range (n s)).map (fun i => G i (A s))) :=
 cptE (cpt_flatMapRange (cpt_cons1 false hG) hn hA) (fun s => by
   simp [aM,List.flatMap_map,unpairB_pairB])
lemma fI {A : List Bool -> List Bool} {n : List Bool -> ℕ} {H : ℕ -> List Bool -> List ℕ}
   (hA : aK.CPTs A) (hn : aj n) (hH : cX (fun t => H (unpairB t).1.length (unpairB t).2)) :
   cX (fun s => (List.range (n s)).flatMap (fun i => H i (A s))) :=
 cptE (cpt_flatMapRange hH hn hA) (fun s => by simp [aM,List.flatMap_assoc,unpairB_pairB])
def kg : Bool -> Bool -> Bool × Option Bool
 | false,true => (false,none)
 | false,false => (true,none)
 | true,true => (false,some true)
 | true,false => (true,some false)
def nj (q : Bool) : Option Bool := if q then some false else none
lemma su {v : List Bool -> List ℕ} (hv : cX v) :
   aK.CPTs (fun s => (v s).map (fun a => decide (a ≠ 0))) := by
 have hu : ∀ (a : ℕ) w,fstRun kg nj false (un a ++ w) = fstRun kg nj false w := by
   intro a w; induction a with
   | zero => rfl
   | succ a ih => simpa [un_succ,fstRun,kg] using ih
 have e : ∀ v : List ℕ,fstRun kg nj false (aM v) = v.map (fun a => decide (a ≠ 0)) /\
     fstRun kg nj true (aM v) = false :: v.map (fun a => decide (a ≠ 0)) := by
   intro v; induction v with
   | nil => exact ⟨rfl,rfl⟩
   | cons a v ih =>
     have key : fstRun kg nj true (un a ++ aM v) =
         decide (a ≠ 0) :: v.map (fun a => decide (a ≠ 0)) := by
       cases a with
       | zero => exact ih.2
       | succ a => simp [un_succ,fstRun,kg,hu,ih.1]
     simp [fstRun,kg,key]
 exact cptE (cpt_comp hv (vr kg nj false)) (fun s => (e _).1)
lemma nN (v : List ℕ) : (aM v).length = v.length + v.sum := by
 induction v with
 | nil => rfl
 | cons a v ih => simp [ih]; omega
end aK.R
namespace aK.Fast
open PEqualNP.Library
def tQ {K:Type} {Γ : K -> Type} {Λ σ : Type}:Turing.TM2.Stmt Γ Λ σ -> Set (Σ k,Γ k)
 | .push k g q=>Set.range (fun v=>(⟨k,g v⟩ : Σ k,Γ k)) ∪ tQ q
 | .peek _ _ q=>tQ q
 | .pop _ _ q=>tQ q
 | .load _ q=>tQ q
 | .branch _ q₁ q₂=>tQ q₁ ∪ tQ q₂
 | .goto _ => ∅
 | .halt => ∅
lemma zq {K:Type} {Γ : K -> Type} {Λ σ : Type} [Finite σ]
   (q:Turing.TM2.Stmt Γ Λ σ):(tQ q).Finite:=by
 induction q with
 | push _ _ _ ih=>exact (Set.finite_range _).union ih
 | peek _ _ _ ih=>exact ih
 | pop _ _ _ ih=>exact ih
 | load _ _ ih=>exact ih
 | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
 | goto _=>exact Set.finite_empty
 | halt=>exact Set.finite_empty
def tf {K:Type} [DecidableEq K] {Γ : K -> Type} {Λ σ : Type}
   (T:∀ k,Set (Γ k)) :
   ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩ : Σ j,Γ j) ∈ tQ q -> s ∈ T k) ->
   Turing.TM2.Stmt (fun k=>{s : Γ k // s ∈ T k}) Λ σ
 | .push k g q,h => .push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
     (tf T q (fun j s hs=>h j s (Or.inr hs)))
 | .peek k f q,h => .peek k (fun v o=>f v (o.map Subtype.val)) (tf T q h)
 | .pop k f q,h => .pop k (fun v o=>f v (o.map Subtype.val)) (tf T q h)
 | .load a q,h => .load a (tf T q h)
 | .branch f q₁ q₂,h => .branch f
     (tf T q₁ (fun j s hs=>h j s (Or.inl hs)))
     (tf T q₂ (fun j s hs=>h j s (Or.inr hs)))
 | .goto f,_ => .goto f
 | .halt,_ => .halt
def uh {K:Type} {Γ : K -> Type} {Λ σ : Type} (T:∀ k,Set (Γ k))
   (cfg:Turing.TM2.Cfg (fun k=>{s : Γ k // s ∈ T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
 ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma zV {K:Type} {Γ : K -> Type} {Λ σ : Type} (T:∀ k,Set (Γ k)) :
   Function.Injective (uh (Λ := Λ) (σ := σ) T):=by
 rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
 simp only [uh,Turing.TM2.Cfg.mk.injEq] at h
 obtain ⟨rfl,rfl,hS⟩:=h
 congr 1
 funext k
 exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma Av {K:Type} [DecidableEq K] {Γ : K -> Type} (T:∀ k,Set (Γ k))
   (S:∀ k,List {s : Γ k // s ∈ T k}) (k:K) (l:List {s : Γ k // s ∈ T k}) :
   (fun j=>(Function.update S k l j).map Subtype.val) =
     Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
 funext j
 by_cases h:j=k
 · subst h;simp
 · simp [h]
lemma zB {K:Type} [DecidableEq K] {Γ : K -> Type} {Λ σ : Type}
   (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
   (hq:∀ k s,(⟨k,s⟩ : Σ j,Γ j) ∈ tQ q -> s ∈ T k)
   (v : σ) (S:∀ k,List {s : Γ k // s ∈ T k}) :
   uh T (Turing.TM2.stepAux (tf T q hq) v S) =
     Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
 induction q generalizing v S with
 | push k g q ih =>
   simp only [tf,Turing.TM2.stepAux]
   rw [ih,Av];rfl
 | peek k f q ih =>
   simp only [tf,Turing.TM2.stepAux]
   exact (ih hq _ _).trans (by rw [List.head?_map])
 | pop k f q ih =>
   simp only [tf,Turing.TM2.stepAux]
   exact (ih hq _ _).trans (by rw [Av,List.head?_map,List.map_tail])
 | load a q ih =>
   simp only [tf,Turing.TM2.stepAux]
   exact ih hq (a v) S
 | branch f q₁ q₂ ih₁ ih₂ =>
   simp only [tf,Turing.TM2.stepAux]
   cases f v
   · exact ih₂ _ v S
   · exact ih₁ _ v S
 | goto f=>rfl
 | halt=>rfl
lemma cpt_to_fast {f:List Bool -> List Bool} (hf:aK.CPTs f) :
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
   {s | k=c.tm.k₀\/k=c.tm.k₁\/(⟨k,s⟩ : Σ j,c.tm.Γ j) ∈ ⋃ l:c.tm.Λ,tQ (c.tm.m l)}
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
 let sA:Turing.FinTM2 :=
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
     m:=fun l=>tf T (c.tm.m l) (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
 have hFin:∀ j:sA.K,Finite (sA.Γ j):=by
   intro j
   by_cases h0:j=c.tm.k₀
   · subst h0;exact Finite.of_fintype _
   · by_cases h1:j=c.tm.k₁
     · subst h1
       have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
       exact Finite.of_equiv _ e₁.symm
     · have yv:(⋃ l:c.tm.Λ,tQ (c.tm.m l)).Finite :=
         Set.finite_iUnion fun l=>zq (c.tm.m l)
       have:Finite ↥(⋃ l:c.tm.Λ,tQ (c.tm.m l)):=yv.to_subtype
       refine Finite.of_injective (f:=fun x:sA.Γ j =>
           (⟨⟨j,x.1⟩,by
             rcases x.2 with h | h | h
             · exact (h0 h).elim
             · exact (h1 h).elim
             · exact h⟩ : ↥(⋃ l:c.tm.Λ,tQ (c.tm.m l)))) ?_
       intro x y hxy
       have h1':=congrArg (fun z=>z.1) hxy
       exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
 have hstep:∀ cfg:sA.Cfg,Option.map (uh T) (sA.step cfg)=c.tm.step (uh T cfg):=by
   rintro ⟨l,v,S⟩
   cases l with
   | none=>rfl
   | some l =>
     change some (uh T (Turing.TM2.stepAux (tf T (c.tm.m l) _) v S)) =
       some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
     exact congrArg some (zB T (c.tm.m l) _ v S)
 have rX:∀ (steps:ℕ) (cfg:sA.Cfg),
     Option.map (uh T) ((flip bind sA.step)^[steps] (some cfg)) =
       (flip bind c.tm.step)^[steps] (some (uh T cfg)):=by
   intro steps
   induction steps with
   | zero=>intro cfg;rfl
   | succ steps ih =>
     intro cfg
     rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
     cases hcur:(flip bind sA.step)^[steps] (some cfg) with
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
   { tm:=sA
     inputAlphabet:=e₀.trans c.inputAlphabet
     outputAlphabet:=e₁.trans c.outputAlphabet
     time:=c.time
     outputsFun:=fun a =>
       { steps:=(c.outputsFun a).steps
         evals_in_steps:=by
           have yc:=(c.outputsFun a).evals_in_steps
           have hinit:uh T (Turing.initList sA (a.map (e₀.trans c.inputAlphabet).invFun)) =
               Turing.initList c.tm (a.map c.inputAlphabet.invFun):=by
             simp only [uh,Turing.initList]
             congr 1;funext k
             by_cases hk:k=c.tm.k₀
             · subst hk;dsimp only [sA]
               simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
             · dsimp only [sA]
               simp only [hk,↓reduceDIte,List.map_nil]
           have hhalt:uh T (Turing.haltList sA ((f a).map (e₁.trans c.outputAlphabet).invFun)) =
               Turing.haltList c.tm ((f a).map c.outputAlphabet.invFun):=by
             simp only [uh,Turing.haltList]
             congr 1;funext k
             by_cases hk:k=c.tm.k₁
             · subst hk;dsimp only [sA]
               simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
             · dsimp only [sA]
               simp only [hk,↓reduceDIte,List.map_nil]
           apply Option.map_injective (zV T)
           rw [rX,hinit,yc]
           exact (congrArg some hhalt).symm
         steps_le_m:=(c.outputsFun a).steps_le_m } }
 exact ⟨M,hFin⟩
end aK.Fast
namespace bH.iF.TightReadOnce
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
 gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl
lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
   wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
 simp [wiresFrom,List.foldl_append]
lemma kl (gs : List Gate) : ∀ w : List Bool,
   ∃ t : List Bool,wiresFrom gs w = w ++ t /\ t.length = gs.length := by
 induction gs with
 | nil => intro w; exact ⟨[],by simp [wiresFrom],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
   have : wiresFrom (g :: gs) w
       = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
   rw [this,ht]; simp
lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
   (wiresFrom gs w).length = w.length + gs.length := by
 obtain ⟨t,ht,hl⟩ := kl gs w
 rw [ht]; simp [hl]
lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
   (wiresFrom gs w).getD i false = w.getD i false := by
 obtain ⟨t,ht,_⟩ := kl gs w
 rw [ht,List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
 g.inputs.length ≤ 2
variable {n : ℕ}
lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
   (L ++ [S]).getD j d = L.getD j d := by
 by_cases hj : j < L.length
 · exact List.getD_append _ _ _ _ hj
 · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
 simp
def reads (g : Gate) : List ℕ :=
 match g.op with
 | .not => g.inputs.take 1
 | _ => g.inputs
lemma reads_le (g : Gate) : (reads g).length ≤ g.inputs.length := by
 cases h : g.op <;> simp [reads,h,Nat.min_le_right]
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
 ((reads g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma mem_foldr_union (l : List ℕ) (F : ℕ -> Finset (Fin n)) (i : Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a := by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]
lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
   i ∈ gateSupp L g ↔ ∃ a ∈ reads g,i ∈ L.getD a ∅ :=
 mem_foldr_union _ _ _
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
 gs.foldl (fun L g => L ++ [gateSupp L g]) L
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}
def Agree (x y : Fin n -> Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
 L.length = w.length /\ w.length = w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i = y i) -> w.getD j false = w'.getD j false
lemma mQ (g : Gate) (w w' : List Bool)
   (h : ∀ a ∈ reads g,w.getD a false = w'.getD a false) :
   g.op.eval (g.inputs.map fun a => w.getD a false) =
     g.op.eval (g.inputs.map fun a => w'.getD a false) := by
 by_cases hn : g.op = .not
 · rw [hn]
   cases hi : g.inputs with
   | nil => simp [GateOp.eval,hi]
   | cons a l =>
     have ha := h a (by simp [reads,hn,hi])
     change (!w.getD a false) = !w'.getD a false
     rw [ha]
 · have he : g.inputs.map (fun a => w.getD a false) =
       g.inputs.map (fun a => w'.getD a false) := by
     apply List.map_congr_left
     intro a ha
     exact h a (by cases ho : g.op <;> simp_all [reads])
   rw [he]
lemma agree_wiresFrom (x y : Fin n -> Bool) (gs : List Gate) :
   ∀ (L : List (Finset (Fin n))) (w w' : List Bool),Agree x y L w w' ->
     Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
 induction gs with
 | nil => intro L w w' h; exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩ := h
   apply ih (L ++ [gateSupp L g])
     (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl : j = L.length
   · subst hjl
     rw [getD_snoc_eq] at hj
     rw [h1,getD_snoc_eq,h2,getD_snoc_eq]
     apply mQ
     intro a ha
     exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a,ha,hi⟩))
   · rw [getD_snoc_ne _ _ _ _ hjl] at hj
     rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
     exact h3 j hj
lemma agree_inputs (x y : Fin n -> Bool) :
   Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
 refine ⟨by simp [inputSupps],by simp,?_⟩
 intro j hj
 by_cases hjn : j < n
 · have hx : x ⟨j,hjn⟩ = y ⟨j,hjn⟩ := hj _ (by simp [inputSupps,hjn])
   simp [hjn,hx]
 · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
 ∀ W : Finset ℕ,(W.biUnion fun j => L.getD j ∅).card ≤ t + W.card
lemma cnt_inputs : Cnt 0 (inputSupps n) := by
 intro W
 refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _
 by_cases hjn : j < n
 · simp [inputSupps,hjn]
 · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
   (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
 intro W
 by_cases hW : L.length ∈ W
 · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
       ⊆ ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
     intro i hi
     rw [Finset.mem_biUnion] at hi ⊢
     obtain ⟨j,hjW,hij⟩ := hi
     by_cases hjl : j = L.length
     · subst hjl
       rw [getD_snoc_eq] at hij
       obtain ⟨a,ha,hia⟩ := (mem_gateSupp L g i).1 hij
       exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
     · rw [getD_snoc_ne _ _ _ _ hjl] at hij
       exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
   have hc1 : (W.erase L.length ∪ (reads g).toFinset).card ≤ (W.card - 1) + 2 := by
     refine le_trans (Finset.card_union_le _ _) ?_
     rw [Finset.card_erase_of_mem hW]
     exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hg)) _
   have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_,hW⟩
   have := h (W.erase L.length ∪ (reads g).toFinset)
   have := Finset.card_le_card hsub
   omega
 · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
       = (W.biUnion fun j => L.getD j ∅) := by
     apply Finset.biUnion_congr rfl
     intro j hj
     exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
   rw [heq]
   have := h W
   omega
lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
   (∀ g ∈ gs,Ok g) -> Cnt t L -> Cnt (t + gs.length) (suppsFrom gs L) := by
 induction gs with
 | nil => intro t L _ h; exact h
 | cons g gs ih =>
   intro t L hok h
   have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
     (cnt_step t L g (hok g List.mem_cons_self) h)
   rw [List.length_cons,show t + (gs.length + 1) = t + 1 + gs.length by omega]
   exact this
lemma f8 (C : Circuit) (n k w : Nat)
   (hk : k ≤ C.gates.length) (hw : w < n + k) (x : Fin n -> Bool) :
   (C.wires (List.ofFn x)).getD w false =
     (wiresFrom (C.gates.take k) (List.ofFn x)).getD w false := by
 change (wiresFrom C.gates (List.ofFn x)).getD w false = _
 conv_lhs => rw [← List.take_append_drop k C.gates]
 rw [wiresFrom_append]
 apply getD_wiresFrom
 rw [length_wiresFrom]
 simpa [List.length_take,Nat.min_eq_left hk] using hw
lemma qI (C : Circuit) (n k w : Nat)
   (hk : k ≤ C.gates.length) (hw : w < n + k)
   (hfan : ∀ g ∈ C.gates,g.inputs.length ≤ 2) :
   ∃ S : Finset (Fin n),S.card ≤ k + 1 /\
     ∀ x y : Fin n -> Bool,(∀ i ∈ S,x i = y i) ->
       (C.wires (List.ofFn x)).getD w false =
         (C.wires (List.ofFn y)).getD w false := by
 let S := (suppsFrom (C.gates.take k) (inputSupps n)).getD w ∅
 refine ⟨S,?_,?_⟩
 · have hc := cnt_suppsFrom (C.gates.take k) 0 (inputSupps n)
     (fun g hg => hfan g (List.mem_of_mem_take hg)) cnt_inputs {w}
   simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,
     List.length_take,Nat.min_eq_left hk] using hc
 · intro x y heq
   rw [f8 C n k w hk hw x,f8 C n k w hk hw y]
   exact (agree_wiresFrom x y (C.gates.take k) _ _ _ (agree_inputs x y)).2.2 w heq
lemma kO (C : Circuit) (n k w : Nat)
   (hk : k ≤ C.gates.length) (hw : w < n + k)
   (hfan : ∀ g ∈ C.gates,g.inputs.length ≤ 2)
   (E : Finset (Fin n))
   (qm : ∀ i ∈ E,∃ x y : Fin n -> Bool,
     (∀ j,j ≠ i -> x j = y j) /\
       (C.wires (List.ofFn x)).getD w false ≠
         (C.wires (List.ofFn y)).getD w false) :
   E.card ≤ k + 1 := by
 obtain ⟨S,hcard,hdep⟩ := qI C n k w hk hw hfan
 apply le_trans (Finset.card_le_card (t := S) ?_) hcard
 intro i hi
 by_contra hni
 obtain ⟨x,y,hxy,hne⟩ := qm i hi
 apply hne (hdep x y ?_)
 intro j hj
 apply hxy j
 intro hji
 subst j
 exact hni hj
def RO (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) : Prop :=
 ∀ Q : Finset (Fin n) -> ((Fin n -> Bool) -> Bool) -> Prop,
   (∀ i : Fin n,Q {i} (fun x => x i)) ->
   (∀ A B a b,Disjoint A B -> Q A a -> Q B b ->
     Q (A ∪ B) (fun x => a x && b x) /\ Q (A ∪ B) (fun x => a x || b x)) -> Q S f
lemma gV (i : Fin n) : RO {i} (fun x => x i) := fun _ hl _ => hl i
lemma lS {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
   RO (A ∪ B) (fun x => a x && b x) :=
 fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).1
lemma nQ {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
   RO (A ∪ B) (fun x => a x || b x) :=
 fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).2
def Fam (L : List (Finset (Fin n))) (F : ℕ -> (Fin n -> Bool) -> Bool) (W : Finset ℕ) : Prop :=
 (∀ w ∈ W,RO (L.getD w ∅) (F w)) /\
 (∀ w ∈ W,∀ v ∈ W,w ≠ v -> Disjoint (L.getD w ∅) (L.getD v ∅))
def qe (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ -> (Fin n -> Bool) -> Bool) : Prop :=
 ∀ W : Finset ℕ,(W.biUnion fun j => L.getD j ∅).card = t + W.card -> Fam L F W
lemma qX : qe 0 (inputSupps n) (fun j x => (List.ofFn x).getD j false) := by
 intro W heq
 have hvalid : ∀ j ∈ W,j < n := by
   intro j hj
   by_contra hn
   have hz : (inputSupps n).getD j ∅ = ∅ :=
     List.getD_eq_default _ _ (by simp [inputSupps]; omega)
   have he := heq
   rw [← Finset.insert_erase hj,Finset.biUnion_insert,hz,Finset.empty_union] at he
   rw [Finset.insert_erase hj] at he
   have hc := cnt_inputs (n := n) (W.erase j)
   have hcard := Finset.card_erase_add_one hj
   omega
 constructor
 · intro j hj
   have hv := hvalid j hj
   have hs : (inputSupps n).getD j ∅ = {⟨j,hv⟩} := by simp [inputSupps,hv]
   have hf : (fun x : Fin n -> Bool => (List.ofFn x).getD j false) = (fun x => x ⟨j,hv⟩) := by
     funext x; simp [hv]
   rw [hs]
   change RO {⟨j,hv⟩} (fun x : Fin n -> Bool => (List.ofFn x).getD j false)
   rw [hf]
   exact gV _
 · intro j hj k hk hne
   have hjn := hvalid j hj
   have hkn := hvalid k hk
   simpa [inputSupps,hjn,hkn,Fin.ext_iff] using hne
lemma sX (L : List (Finset (Fin n))) (g : Gate) (W : Finset ℕ)
   (hW : L.length ∈ W) :
   (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
     ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
 ext i
 constructor
 · intro hi
   rw [Finset.mem_biUnion] at hi ⊢
   obtain ⟨j,hjW,hij⟩ := hi
   by_cases hjl : j = L.length
   · subst hjl
     rw [getD_snoc_eq] at hij
     obtain ⟨a,ha,hia⟩ := (mem_gateSupp L g i).1 hij
     exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
   · rw [getD_snoc_ne _ _ _ _ hjl] at hij
     exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
 · intro hi
   obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
   rcases Finset.mem_union.mp hj with hj | hj
   · refine Finset.mem_biUnion.mpr ⟨j,Finset.mem_of_mem_erase hj,?_⟩
     rw [getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hj)]
     exact hi
   · refine Finset.mem_biUnion.mpr ⟨L.length,hW,?_⟩
     rw [getD_snoc_eq]
     exact (mem_gateSupp L g i).mpr ⟨j,List.mem_toFinset.mp hj,hi⟩
lemma nY (g : Gate)
   (ho : g.op = .and \/ g.op = .or \/ g.op = .not)
   (hlen : g.inputs.length ≤ 2) (hcard : (reads g).toFinset.card = 2) :
   ∃ a b,g.inputs = [a,b] /\ a ≠ b /\ (g.op = .and \/ g.op = .or) := by
 have hn : g.op ≠ .not := by
   intro hn
   have hc := List.toFinset_card_le (reads g)
   have hl : (reads g).length ≤ 1 := by simp [reads,hn]
   omega
 have hop : g.op = .and \/ g.op = .or := by rcases ho with h | h | h <;> simp_all
 have hr : reads g = g.inputs := by rcases hop with h | h <;> simp [reads,h]
 rw [hr] at hcard
 rcases hi : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
 · simp [hi] at hcard
 · simp [hi] at hcard
 · refine ⟨a,b,rfl,?_,hop⟩
   intro hab
   simp [hi,hab] at hcard
 · simp [hi] at hlen
def kx (L : List (Finset (Fin n))) (F : ℕ -> (Fin n -> Bool) -> Bool) (g : Gate)
   (j : ℕ) (x : Fin n -> Bool) : Bool :=
 if j = L.length then g.op.eval (g.inputs.map fun a => F a x) else F j x
lemma sP (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ -> (Fin n -> Bool) -> Bool)
   (g : Gate) (ho : g.op = .and \/ g.op = .or \/ g.op = .not) (hlen : g.inputs.length ≤ 2)
   (hc : Cnt t L) (ht : qe t L F) :
   qe (t+1) (L ++ [gateSupp L g]) (kx L F g) := by
 intro W heq
 have hW : L.length ∈ W := by
   by_contra hn
   have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
       (W.biUnion fun j => L.getD j ∅) := by
     apply Finset.biUnion_congr rfl
     intro j hj
     exact getD_snoc_ne _ _ _ _ (fun h => hn (h ▸ hj))
   rw [hU] at heq
   have := hc W
   omega
 let E := W.erase L.length
 let B := (reads g).toFinset
 let P := E ∪ B
 have hEc : E.card+1 = W.card := Finset.card_erase_add_one hW
 have hBc : B.card ≤ 2 := le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hlen)
 have hPc : P.card ≤ E.card + B.card := Finset.card_union_le _ _
 have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
     (P.biUnion fun j => L.getD j ∅) := sX L g W hW
 rw [hU] at heq
 have Bf := hc P
 have hB2 : B.card = 2 := by omega
 have vH : P.card = E.card + B.card := by omega
 have wG : (P.biUnion fun j => L.getD j ∅).card = t + P.card := by omega
 have Au : Disjoint E B := Finset.card_union_eq_card_add_card.mp vH
 obtain ⟨a,b,hin,hab,hop⟩ := nY g ho hlen hB2
 have hreads : reads g = [a,b] := by rcases hop with h | h <;> simp [reads,h,hin]
 have haB : a ∈ B := by simp [B,hreads]
 have Aj : b ∈ B := by simp [B,hreads]
 have haP : a ∈ P := Finset.mem_union_right _ haB
 have y6 : b ∈ P := Finset.mem_union_right _ Aj
 have hF := ht P wG
 have hEP : E ⊆ P := Finset.subset_union_left
 have z3 : ∀ w ∈ E,w ≠ a := by
   intro w hw hwa; subst w
   exact Finset.disjoint_left.mp Au hw haB
 have zy : ∀ w ∈ E,w ≠ b := by
   intro w hw hwb; subst w
   exact Finset.disjoint_left.mp Au hw Aj
 have hS : gateSupp L g = L.getD a ∅ ∪ L.getD b ∅ := by simp [gateSupp,hreads]
 have hnew : RO (gateSupp L g) (kx L F g L.length) := by
   rw [hS]
   have hd := hF.2 a haP b y6 hab
   rcases hop with hop | hop
   · have hf : kx L F g L.length = (fun x => F a x && F b x) := by
       funext x; simp [kx,hin,hop,GateOp.eval]
     rw [hf]; exact lS hd (hF.1 a haP) (hF.1 b y6)
   · have hf : kx L F g L.length = (fun x => F a x || F b x) := by
       funext x; simp [kx,hin,hop,GateOp.eval]
     rw [hf]; exact nQ hd (hF.1 a haP) (hF.1 b y6)
 have hother : ∀ w ∈ E,(L ++ [gateSupp L g]).getD w ∅ = L.getD w ∅ :=
   fun w hw => getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hw)
 have tx : ∀ w ∈ E,Disjoint (gateSupp L g) (L.getD w ∅) := by
   intro w hw
   rw [hS,Finset.disjoint_union_left]
   exact ⟨hF.2 a haP w (hEP hw) (z3 w hw).symm,
     hF.2 b y6 w (hEP hw) (zy w hw).symm⟩
 constructor
 · intro w hw
   by_cases hwk : w = L.length
   · subst w
     rw [getD_snoc_eq]
     exact hnew
   · have xV : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
     rw [hother w xV]
     have hf : kx L F g w = F w := by funext x; simp [kx,hwk]
     rw [hf]
     exact hF.1 w (hEP xV)
 · intro w hw v hv hne
   by_cases hwk : w = L.length
   · subst w
     have yD : v ∈ E := Finset.mem_erase.mpr ⟨hne.symm,hv⟩
     rw [getD_snoc_eq,hother v yD]
     exact tx v yD
   · have xV : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
     rw [hother w xV]
     by_cases hvk : v = L.length
     · subst v
       rw [getD_snoc_eq]
       exact (tx w xV).symm
     · have yD : v ∈ E := Finset.mem_erase.mpr ⟨hvk,hv⟩
       rw [hother v yD]
       exact hF.2 w (hEP xV) v (hEP yD) hne
lemma nX (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n)))
   (v : (Fin n -> Bool) -> List Bool),(∀ x,(v x).length = L.length) ->
   (∀ g ∈ gs,(g.op = .and \/ g.op = .or \/ g.op = .not) /\ g.inputs.length ≤ 2) ->
   Cnt t L -> qe t L (fun j x => (v x).getD j false) ->
   qe (t+gs.length) (suppsFrom gs L) (fun j x => (wiresFrom gs (v x)).getD j false) := by
 induction gs with
 | nil => intro t L v hv _ hc ht; exact ht
 | cons g gs ih =>
   intro t L v hv hg hc ht
   let v' := fun x : Fin n -> Bool => v x ++ [g.op.eval (g.inputs.map fun a => (v x).getD a false)]
   have hv' : ∀ x,(v' x).length = (L ++ [gateSupp L g]).length := by
     intro x; simp [v',hv x]
   have hf : (fun j x => (v' x).getD j false) =
       kx L (fun j x => (v x).getD j false) g := by
     funext j x
     by_cases hj : j = L.length
     · subst j
       simp only [kx,ite_true]
       dsimp only [v']
       rw [← hv x,getD_snoc_eq]
     · simp only [kx,hj,ite_false]
       exact getD_snoc_ne _ _ _ _ (by rw [hv x]; exact hj)
   have hgg := hg g List.mem_cons_self
   have ht' : qe (t+1) (L ++ [gateSupp L g]) (fun j x => (v' x).getD j false) := by
     rw [hf]
     exact sP t L _ g hgg.1 hgg.2 hc ht
   have hres := ih (t+1) (L ++ [gateSupp L g]) v' hv'
     (fun g' h => hg g' (List.mem_cons_of_mem g h)) (cnt_step t L g hgg.2 hc) ht'
   simpa only [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega,
     suppsFrom,wiresFrom,List.foldl_cons,v'] using hres
lemma oT (C : Circuit) (n k w : Nat)
   (hk : k ≤ C.gates.length) (hw : w < n+k)
   (hfan : ∀ g ∈ C.gates,(g.op = .and \/ g.op = .or \/ g.op = .not) /\ g.inputs.length ≤ 2)
   (E : Finset (Fin n)) (hE : E.card = k+1)
   (qm : ∀ i ∈ E,∃ x y : Fin n -> Bool,
     (∀ j,j ≠ i -> x j = y j) /\
     (C.wires (List.ofFn x)).getD w false ≠ (C.wires (List.ofFn y)).getD w false) :
   RO E (fun x => (C.wires (List.ofFn x)).getD w false) := by
 let gs := C.gates.take k
 let L := suppsFrom gs (inputSupps n)
 let S := L.getD w ∅
 have hlen : gs.length = k := by simp [gs,List.length_take,Nat.min_eq_left hk]
 have hfan' : ∀ g ∈ gs,(g.op = .and \/ g.op = .or \/ g.op = .not) /\ g.inputs.length ≤ 2 :=
   fun g hg => hfan g (List.mem_of_mem_take hg)
 have hc := cnt_suppsFrom gs 0 (inputSupps n) (fun g hg => (hfan' g hg).2) cnt_inputs
 have hSc : S.card ≤ k+1 := by
   have := hc {w}
   simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using this
 have hdep : ∀ x y : Fin n -> Bool,(∀ i ∈ S,x i=y i) ->
     (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
   intro x y hxy
   rw [f8 C n k w hk hw x,f8 C n k w hk hw y]
   exact (agree_wiresFrom x y gs _ _ _ (agree_inputs x y)).2.2 w hxy
 have hsub : E ⊆ S := by
   intro i hi
   by_contra hni
   obtain ⟨x,y,hxy,hne⟩ := qm i hi
   apply hne (hdep x y ?_)
   intro j hj
   exact hxy j (fun h => hni (h ▸ hj))
 have AD : E = S := Finset.eq_of_subset_of_card_le hsub (by omega)
 have hT := nX gs 0 (inputSupps n) (fun x => List.ofFn x)
   (fun x => by simp [inputSupps]) hfan' cnt_inputs qX
 have heq : (({w} : Finset ℕ).biUnion fun j => L.getD j ∅).card = (0+gs.length)+({w} : Finset ℕ).card := by
   have hS : S.card = k+1 := by rw [←AD]; exact hE
   simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using hS
 have hR := (hT {w} heq).1 w (Finset.mem_singleton_self w)
 change RO S _ at hR
 rw [←AD] at hR
 have hf : (fun x : Fin n -> Bool => (wiresFrom gs (List.ofFn x)).getD w false) =
     (fun x => (C.wires (List.ofFn x)).getD w false) := by
   funext x; exact (f8 C n k w hk hw x).symm
 change RO E (fun x : Fin n -> Bool => (wiresFrom gs (List.ofFn x)).getD w false) at hR
 rw [hf] at hR
 exact hR
end bH.iF.TightReadOnce
namespace bH.iF.ReadOncePath
open bH.iF.TightReadOnce
variable {n : ℕ} {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
lemma tM (h : RO S f) (x : Fin n -> Bool) (hx : ∀ i ∈ S,x i=false) : f x=false := by
 apply h (fun S f => ∀ x,(∀ i ∈ S,x i=false) -> f x=false) ?_ ?_ x hx
 · intro i x hx; exact hx i (Finset.mem_singleton_self _)
 · intro A B a b hd ha hb
   constructor <;> intro x hx
   · dsimp only
     rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
       hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl
   · dsimp only
     rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
       hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl
lemma sI (h : RO S f) (x y : Fin n -> Bool) (hx : ∀ i ∈ S,x i=y i) : f x=f y := by
 apply h (fun S f => ∀ x y,(∀ i ∈ S,x i=y i) -> f x=f y) ?_ ?_ x y hx
 · intro i x y hx; exact hx i (Finset.mem_singleton_self _)
 · intro A B a b hd ha hb
   constructor <;> intro x y hx <;> dsimp only <;>
     rw [ha x y (fun i hi => hx i (Finset.mem_union_left _ hi)),
       hb x y (fun i hi => hx i (Finset.mem_union_right _ hi))]
lemma mG (h : RO S f) (x y : Fin n -> Bool)
   (hxy : ∀ i,x i=true -> y i=true) (hf : f x=true) : f y=true := by
 apply h (fun _ f => ∀ x y,(∀ i,x i=true -> y i=true) -> f x=true -> f y=true) ?_ ?_ x y hxy hf
 · intro i x y hxy hf; exact hxy i hf
 · intro A B a b hd ha hb
   constructor
   · intro x y hxy hf
     simp only [Bool.and_eq_true] at hf ⊢
     exact ⟨ha x y hxy hf.1,hb x y hxy hf.2⟩
   · intro x y hxy hf
     simp only [Bool.or_eq_true] at hf ⊢
     exact hf.elim (fun h => Or.inl (ha x y hxy h)) (fun h => Or.inr (hb x y hxy h))
def pair (i j : Fin n) : Fin n -> Bool := fun k => decide (k=i \/ k=j)
def single (i : Fin n) : Fin n -> Bool := fun k => decide (k=i)
lemma pair_comm (i j : Fin n) : pair i j=pair j i := by funext k; simp [pair,or_comm]
lemma nq (h : RO S f) (i j : Fin n) (hi : i ∉ S) (hj : j ∉ S) : f (pair i j)=false := by
 apply tM h
 intro k hk
 simp only [pair,decide_eq_false_iff_not,not_or]
 exact ⟨fun hki => hi (hki ▸ hk),fun hkj => hj (hkj ▸ hk)⟩
lemma gN (h : RO S f) (i j : Fin n) (hj : j ∉ S) :
   f (pair i j)=f (single i) := by
 apply sI h
 intro k hk
 have hkj : k≠j := fun hkj => hj (hkj ▸ hk)
 simp [pair,single,hkj]
lemma j7 (h : RO S f) (i j : Fin n) (hi : i ∉ S) :
   f (pair i j)=f (single j) := by rw [pair_comm]; exact gN h j i hi
end bH.iF.ReadOncePath
namespace bH.g7
open bH.iF.TightReadOnce bH.iF.ReadOncePath
variable {n : ℕ}
def NoSingle (f : (Fin n -> Bool) -> Bool) : Prop := ∀ i,f (single i) = false
def eZ (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) : Prop :=
 ∀ i ∈ S,∃ j ∈ S,f (pair i j) = true
def Quadratic (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) : Prop :=
 ∀ x,f x = true ↔ ∃ i ∈ S,∃ j ∈ S,f (pair i j) = true /\ x i = true /\ x j = true
lemma oo {i j : Fin n} {x : Fin n -> Bool} (hi : x i = true) (hj : x j = true) :
   ∀ t,pair i j t = true -> x t = true := by
 intro t ht
 have : t = i \/ t = j := by simpa [pair] using ht
 rcases this with rfl | rfl <;> assumption
lemma mn {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (hf : RO S f) (x : Fin n -> Bool) (hx : f x = true) : ∃ i ∈ S,x i = true := by
 by_contra hn
 have hz : ∀ i ∈ S,x i = false := by
   intro i hi
   have h : x i ≠ true := fun ht => hn ⟨i,hi,ht⟩
   exact Bool.eq_false_iff.mpr h
 have h := tM hf x hz
 rw [hx] at h
 contradiction
lemma g6 {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hc : eZ (A ∪ B) (fun x => a x && b x)) :
   (∀ i ∈ A,a (single i) = true) /\ (∀ j ∈ B,b (single j) = true) := by
 constructor
 · intro i hi
   obtain ⟨j,hj,hp⟩ := hc i (Finset.mem_union_left _ hi)
   have hia : i ∉ B := Finset.disjoint_left.mp hd hi
   have hja : j ∉ A := by
     intro hjA
     have hjB : j ∉ B := Finset.disjoint_left.mp hd hjA
     have hz := nq hb i j hia hjB
     simp only [hz,Bool.and_false] at hp
     contradiction
   have hpA : a (pair i j) = true := (by simpa only [Bool.and_eq_true] using hp : a (pair i j) = true /\ b (pair i j) = true).1
   rwa [gN ha i j hja] at hpA
 · intro i hi
   obtain ⟨j,hj,hp⟩ := hc i (Finset.mem_union_right _ hi)
   have hia : i ∉ A := Finset.disjoint_right.mp hd hi
   have hja : j ∉ B := by
     intro hjB
     have hjA : j ∉ A := Finset.disjoint_right.mp hd hjB
     have hz := nq ha i j hia hjA
     simp only [hz,Bool.false_and] at hp
     contradiction
   have Ad : b (pair i j) = true := (by simpa only [Bool.and_eq_true] using hp : a (pair i j) = true /\ b (pair i j) = true).2
   rwa [gN hb i j hja] at Ad
lemma lI {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hs : NoSingle (fun x => a x || b x))
   (hc : eZ (A ∪ B) (fun x => a x || b x)) : eZ A a := by
 intro i hi
 obtain ⟨j,hj,hp⟩ := hc i (Finset.mem_union_left _ hi)
 have hia : i ∉ B := Finset.disjoint_left.mp hd hi
 have hsA : ∀ t,a (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
 have hsB : ∀ t,b (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
 have hpA : a (pair i j) = true := by
   have hp' : a (pair i j) = true \/ b (pair i j) = true := by simpa only [Bool.or_eq_true] using hp
   rcases hp' with h | h
   · exact h
   · rw [j7 hb i j hia,hsB j] at h
     contradiction
 have hjA : j ∈ A := by
   by_contra hjA
   rw [gN ha i j hjA,hsA i] at hpA
   contradiction
 exact ⟨j,hjA,hpA⟩
lemma kL {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (hf : RO S f) (hs : NoSingle f) (hc : eZ S f) : Quadratic S f := by
 let Q := fun (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) => RO S f /\ (NoSingle f -> eZ S f -> Quadratic S f)
 have hQ : Q S f := hf Q (by
   intro i
   refine ⟨gV i,?_⟩
   intro hs hc
   have h := hs i
   simp [single] at h) (by
   intro A B a b hd ha hb
   constructor
   · refine ⟨lS hd ha.1 hb.1,?_⟩
     intro hs hc x
     constructor
     · intro hx
       obtain ⟨hi,hj⟩ := g6 hd ha.1 hb.1 hc
       obtain ⟨i,hiA,hxi⟩ := mn ha.1 x (by simpa only [Bool.and_eq_true] using hx : a x = true /\ b x = true).1
       obtain ⟨j,hjB,hxj⟩ := mn hb.1 x (by simpa only [Bool.and_eq_true] using hx : a x = true /\ b x = true).2
       refine ⟨i,Finset.mem_union_left _ hiA,j,Finset.mem_union_right _ hjB,?_,hxi,hxj⟩
       have hjA : j ∉ A := Finset.disjoint_right.mp hd hjB
       have xo : i ∉ B := Finset.disjoint_left.mp hd hiA
       dsimp only
       rw [gN ha.1 i j hjA,j7 hb.1 i j xo,hi i hiA,hj j hjB]
       rfl
     · rintro ⟨i,hi,j,hj,hp,hxi,hxj⟩
       exact mG (lS hd ha.1 hb.1) _ _ (oo hxi hxj) hp
   · refine ⟨nQ hd ha.1 hb.1,?_⟩
     intro hs hc x
     have hsA : NoSingle a := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
     have hsB : NoSingle b := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
     have hcA := lI hd ha.1 hb.1 hs hc
     have hcB : eZ B b := by
       have hs' : NoSingle (fun x => b x || a x) := by simpa only [Bool.or_comm] using hs
       have hc' : eZ (B ∪ A) (fun x => b x || a x) := by
         simpa only [Finset.union_comm,Bool.or_comm] using hc
       exact lI hd.symm hb.1 ha.1 hs' hc'
     constructor
     · intro hx
       have hx' : a x = true \/ b x = true := by simpa only [Bool.or_eq_true] using hx
       rcases hx' with h | h
       · obtain ⟨i,hi,j,hj,hp,hxi,hxj⟩ := (ha.2 hsA hcA x).mp h
         refine ⟨i,Finset.mem_union_left _ hi,j,Finset.mem_union_left _ hj,?_,hxi,hxj⟩
         simp only [hp,Bool.true_or]
       · obtain ⟨i,hi,j,hj,hp,hxi,hxj⟩ := (hb.2 hsB hcB x).mp h
         refine ⟨i,Finset.mem_union_right _ hi,j,Finset.mem_union_right _ hj,?_,hxi,hxj⟩
         simp only [hp,Bool.or_true]
     · rintro ⟨i,hi,j,hj,hp,hxi,hxj⟩
       exact mG (nQ hd ha.1 hb.1) _ _ (oo hxi hxj) hp)
 exact hQ.2 hs hc
end bH.g7
namespace bH.g7
open bH.iF.TightReadOnce bH.iF.ReadOncePath
variable {n : ℕ}
lemma bf {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hs : NoSingle (fun x => a x || b x))
   {i j : Fin n} (hi : i ∈ A) (hp : (a (pair i j) || b (pair i j)) = true) :
   j ∈ A /\ a (pair i j) = true := by
 have xo : i ∉ B := Finset.disjoint_left.mp hd hi
 have hsA : ∀ t,a (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
 have hsB : ∀ t,b (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
 have hpA : a (pair i j) = true := by
   rcases Bool.or_eq_true_iff.mp hp with h | h
   · exact h
   · rw [j7 hb i j xo,hsB j] at h
     contradiction
 refine ⟨?_,hpA⟩
 by_contra hjA
 rw [gN ha i j hjA,hsA i] at hpA
 contradiction
lemma iM {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hc : eZ (A ∪ B) (fun x => a x && b x))
   {i j : Fin n} (hi : i ∈ A) (hj : j ∈ B) :
   (a (pair i j) && b (pair i j)) = true := by
 obtain ⟨hsA,hsB⟩ := g6 hd ha hb hc
 have xo : i ∉ B := Finset.disjoint_left.mp hd hi
 have hjA : j ∉ A := Finset.disjoint_right.mp hd hj
 rw [gN ha i j hjA,j7 hb i j xo,hsA i hi,hsB j hj]
 rfl
lemma aG {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (hb : RO B b)
   {i j : Fin n} (hi : i ∈ A) (hp : (a (pair i j) && b (pair i j)) = true) :
   j ∈ B := by
 by_contra hjB
 have xo : i ∉ B := Finset.disjoint_left.mp hd hi
 rw [nq hb i j xo hjB,Bool.and_false] at hp
 contradiction
def Matched (bj : Fin n -> Fin n) (aF : Fin n -> Bool)
   (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) : Prop :=
 NoSingle f /\
 (∀ i ∈ S,bj i ∈ S) /\
 (∀ i ∈ S,f (pair i (bj i)) = true) /\
 (∀ i j,aF i ≠ aF j -> j ≠ bj i -> f (pair i j) = false)
lemma gW {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool} (h : Matched bj aF S f) :
   eZ S f := fun i hi => ⟨bj i,h.2.1 i hi,h.2.2.1 i hi⟩
lemma ie {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hm : Matched bj aF (A ∪ B) (fun x => a x || b x)) :
   Matched bj aF A a := by
 refine ⟨?_,?_,?_,?_⟩
 · intro i
   exact (Bool.or_eq_false_iff.mp (hm.1 i)).1
 · intro i hi
   exact (bf hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).1
 · intro i hi
   exact (bf hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).2
 · intro i j hc hj
   exact (Bool.or_eq_false_iff.mp (hm.2.2.2 i j hc hj)).1
lemma jQ {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hm : Matched bj aF (A ∪ B) (fun x => a x || b x)) :
   Matched bj aF B b := by
 have h : Matched bj aF (B ∪ A) (fun x => b x || a x) := by
   simpa only [Finset.union_comm,Bool.or_comm] using hm
 exact ie hd.symm hb ha h
lemma fq {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   (hmi : Function.Involutive bj) (hcol : ∀ i,aF (bj i) ≠ aF i)
   {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
   (hm : Matched bj aF (A ∪ B) (fun x => a x && b x)) :
   ∀ i ∈ A,∀ j ∈ A,aF i = aF j -> i = j := by
 intro i hi j hj hij
 have AG : bj j ∈ B := aG hd hb hj
   (hm.2.2.1 j (Finset.mem_union_left _ hj))
 have ht : (a (pair i (bj j)) && b (pair i (bj j))) = true :=
   iM hd ha hb (gW hm) hi AG
 have hcm : aF i ≠ aF (bj j) := by
   intro h
   exact hcol j (h.symm.trans hij)
 have yP : bj j = bj i := by
   by_contra hne
   have hf := hm.2.2.2 i (bj j) hcm hne
   dsimp only at hf
   rw [hf] at ht
   contradiction
 exact (hmi.injective yP).symm
def je (aF : Fin n -> Bool) (S : Finset (Fin n))
   (f : (Fin n -> Bool) -> Bool) : Prop :=
 ∀ i ∈ S,∀ j ∈ S,∀ l ∈ S,aF i = aF j -> aF i = aF l ->
   f (pair i j) = true -> f (pair i l) = true -> j = l
lemma iu {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   (hmi : Function.Involutive bj) (hcol : ∀ i,aF (bj i) ≠ aF i)
   {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (hf : RO S f) (hm : Matched bj aF S f) : je aF S f := by
 let Q := fun (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) =>
   RO S f /\ (Matched bj aF S f -> je aF S f)
 have hQ : Q S f := hf Q (by
   intro i
   refine ⟨gV i,?_⟩
   intro hm
   have hs := hm.1 i
   simp [single] at hs) (by
   intro A B a b hd ha hb
   constructor
   · refine ⟨lS hd ha.1 hb.1,?_⟩
     intro hm i hi j hj l hl hij hil hpj hpl
     have hinjA := fq hmi hcol hd ha.1 hb.1 hm
     have hm' : Matched bj aF (B ∪ A) (fun x => b x && a x) := by
       simpa only [Finset.union_comm,Bool.and_comm] using hm
     have yX := fq hmi hcol hd.symm hb.1 ha.1 hm'
     rcases Finset.mem_union.mp hi with hi | hi
     · have hjB := aG hd hb.1 hi hpj
       have zS := aG hd hb.1 hi hpl
       exact yX j hjB l zS (hij.symm.trans hil)
     · have hpj' : (b (pair i j) && a (pair i j)) = true := by simpa only [Bool.and_comm] using hpj
       have hpl' : (b (pair i l) && a (pair i l)) = true := by simpa only [Bool.and_comm] using hpl
       have hjA := aG hd.symm ha.1 hi hpj'
       have hlA := aG hd.symm ha.1 hi hpl'
       exact hinjA j hjA l hlA (hij.symm.trans hil)
   · refine ⟨nQ hd ha.1 hb.1,?_⟩
     intro hm i hi j hj l hl hij hil hpj hpl
     rcases Finset.mem_union.mp hi with hi | hi
     · obtain ⟨hjA,hpjA⟩ := bf hd ha.1 hb.1 hm.1 hi hpj
       obtain ⟨hlA,hplA⟩ := bf hd ha.1 hb.1 hm.1 hi hpl
       exact ha.2 (ie hd ha.1 hb.1 hm) i hi j hjA l hlA hij hil hpjA hplA
     · have hm' : Matched bj aF (B ∪ A) (fun x => b x || a x) := by
         simpa only [Finset.union_comm,Bool.or_comm] using hm
       have hpj' : (b (pair i j) || a (pair i j)) = true := by simpa only [Bool.or_comm] using hpj
       have hpl' : (b (pair i l) || a (pair i l)) = true := by simpa only [Bool.or_comm] using hpl
       obtain ⟨hjB,hpjB⟩ := bf hd.symm hb.1 ha.1 hm'.1 hi hpj'
       obtain ⟨zS,hplB⟩ := bf hd.symm hb.1 ha.1 hm'.1 hi hpl'
       exact hb.2 (jQ hd ha.1 hb.1 hm) i hi j hjB l zS hij hil hpjB hplB)
 exact hQ.2 hm
end bH.g7
namespace bH.g7
open bH.iF.TightReadOnce bH.iF.ReadOncePath
variable {n : ℕ}
lemma lD {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (hf : RO S f) (hm : Matched bj aF S f) :
   ∀ i ∈ S,∀ j ∈ S,f (pair i j) = true -> f (pair (bj i) (bj j)) = true := by
 let Q := fun (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) =>
   RO S f /\ (Matched bj aF S f ->
     ∀ i ∈ S,∀ j ∈ S,f (pair i j) = true -> f (pair (bj i) (bj j)) = true)
 have hQ : Q S f := hf Q (by
   intro i
   refine ⟨gV i,?_⟩
   intro hm
   have hs := hm.1 i
   simp [single] at hs) (by
   intro A B a b hd ha hb
   constructor
   · refine ⟨lS hd ha.1 hb.1,?_⟩
     intro hm i hi j hj hp
     have hm' : Matched bj aF (B ∪ A) (fun x => b x && a x) := by
       simpa only [Finset.union_comm,Bool.and_comm] using hm
     rcases Finset.mem_union.mp hi with hi | hi
     · have hjB := aG hd hb.1 hi hp
       have Ae := aG hd hb.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))
       have zT := aG hd.symm ha.1 hjB
         (hm'.2.2.1 j (Finset.mem_union_left _ hjB))
       have h := iM hd.symm hb.1 ha.1 (gW hm') Ae zT
       simpa only [Bool.and_comm] using h
     · have hp' : (b (pair i j) && a (pair i j)) = true := by
         simpa only [Bool.and_comm] using hp
       have hjA := aG hd.symm ha.1 hi hp'
       have z4 := aG hd.symm ha.1 hi
         (hm'.2.2.1 i (Finset.mem_union_left _ hi))
       have zY := aG hd hb.1 hjA (hm.2.2.1 j (Finset.mem_union_left _ hjA))
       exact iM hd ha.1 hb.1 (gW hm) z4 zY
   · refine ⟨nQ hd ha.1 hb.1,?_⟩
     intro hm i hi j hj hp
     rcases Finset.mem_union.mp hi with hi | hi
     · obtain ⟨hjA,hpA⟩ := bf hd ha.1 hb.1 hm.1 hi hp
       have h := ha.2 (ie hd ha.1 hb.1 hm) i hi j hjA hpA
       dsimp only
       rw [h,Bool.true_or]
     · have hm' : Matched bj aF (B ∪ A) (fun x => b x || a x) := by
         simpa only [Finset.union_comm,Bool.or_comm] using hm
       have hp' : (b (pair i j) || a (pair i j)) = true := by
         simpa only [Bool.or_comm] using hp
       obtain ⟨hjB,Ad⟩ := bf hd.symm hb.1 ha.1 hm'.1 hi hp'
       have h := hb.2 (jQ hd ha.1 hb.1 hm) i hi j hjB Ad
       dsimp only
       rw [h,Bool.or_true])
 exact hQ.2 hm
end bH.g7
namespace bH.g7
variable {α : Type*}
lemma lg (R : α -> α -> Prop)
   (hs : ∀ {a b},R a b -> R b a) (hi : ∀ a,¬ R a a)
   (hu : ∀ a b c,R a b -> R a c -> b = c) :
   ∃ p : Equiv.Perm α,Function.Involutive p /\
     (∀ a b,R a b ↔ p a = b /\ b ≠ a) /\
     (∀ q : Equiv.Perm α,(∀ a b,R a b ↔ q a = b /\ b ≠ a) -> q = p) := by
 classical
 let p : α -> α := fun a => if h : ∃ b,R a b then Classical.choose h else a
 have hpR : ∀ a b,R a b -> p a = b := by
   intro a b h
   have he : ∃ b,R a b := ⟨b,h⟩
   dsimp only [p]
   rw [dite_eq_left he]
   exact hu a _ b (Classical.choose_spec he) h
 have hp : ∀ a,p a = a \/ R a (p a) := by
   intro a
   by_cases he : ∃ b,R a b
   · right
     dsimp only [p]
     rw [dite_eq_left he]
     exact Classical.choose_spec he
   · left
     simp [p,he]
 have hpi : Function.Involutive p := by
   intro a
   rcases hp a with h | h
   · rw [h,h]
   · exact hpR _ _ (hs h)
 let e : Equiv.Perm α := hpi.toPerm p
 have heval : ∀ a,e a = p a := fun _ => rfl
 have hiff : ∀ a b,R a b ↔ e a = b /\ b ≠ a := by
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
 by_cases h : p a = a
 · by_cases hqa : q a = a
   · exact hqa.trans h.symm
   · have hr := (hq a (q a)).2 ⟨rfl,hqa⟩
     have he := hpR a (q a) hr
     exact False.elim (hqa (he.symm.trans h))
 · have hr := (hiff a (e a)).2 ⟨rfl,h⟩
   exact (hq a (e a)).1 hr |>.1
lemma ik {R : α -> α -> Prop} {p : Equiv.Perm α}
   (hp : ∀ a b,R a b ↔ p a = b /\ b ≠ a)
   (σ : α -> α) (hσ : Function.Involutive σ)
   (hR : ∀ a b,R a b -> R (σ a) (σ b)) :
   ∀ a,p (σ a) = σ (p a) := by
 intro a
 by_cases he : p a = a
 · by_cases he' : p (σ a) = σ a
   · rw [he,he']
   · have h := hR (σ a) (p (σ a)) ((hp _ _).2 ⟨rfl,he'⟩)
     rw [hσ a] at h
     obtain ⟨hpa,hne⟩ := (hp _ _).1 h
     exact False.elim (hne (hpa.symm.trans he))
 · have h := hR a (p a) ((hp _ _).2 ⟨rfl,he⟩)
   exact ((hp _ _).1 h).1
end bH.g7
namespace bH.g7
open bH.iF.TightReadOnce bH.iF.ReadOncePath
variable {n : ℕ}
lemma lA : ∀ a b c d : Bool,a ≠ c -> b ≠ d -> c = d -> a = b := by decide
lemma matched_involution_normal_form {bj : Fin n -> Fin n} {aF : Fin n -> Bool}
   (hmi : Function.Involutive bj) (hcol : ∀ i,aF (bj i) ≠ aF i)
   {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (hf : RO S f) (hm : Matched bj aF S f) :
   ∃ p : Equiv.Perm (Fin n),Function.Involutive p /\
     (∀ i,aF (p i) = aF i) /\
     (∀ i,p (bj i) = bj (p i)) /\
     (∀ i,i ∉ S -> p i = i) /\
     (∀ x,f x = true ↔ ∃ i ∈ S,
       (x i = true /\ x (bj i) = true) \/
       (p i ≠ i /\ x i = true /\ x (p i) = true)) /\
     (∀ i j,(i ∈ S /\ j ∈ S /\ aF i = aF j /\ f (pair i j) = true) ↔
       p i = j /\ j ≠ i) := by
 classical
 let R : Fin n -> Fin n -> Prop := fun i j =>
   i ∈ S /\ j ∈ S /\ aF i = aF j /\ f (pair i j) = true
 have hsym : ∀ {i j},R i j -> R j i := by
   intro i j h
   refine ⟨h.2.1,h.1,h.2.2.1.symm,?_⟩
   rw [pair_comm]
   exact h.2.2.2
 have Af : ∀ i,¬ R i i := by
   intro i h
   have hp : pair i i = single i := by funext j; simp [pair,single]
   have htrue := h.2.2.2
   rw [hp,hm.1 i] at htrue
   contradiction
 have vM : ∀ i j l,R i j -> R i l -> j = l := by
   intro i j l h1 h2
   exact iu hmi hcol hf hm i h1.1 j h1.2.1 l h2.2.1
     h1.2.2.1 h2.2.2.1 h1.2.2.2 h2.2.2.2
 obtain ⟨p,hpi,hp,hpu⟩ := lg R hsym Af vM
 have oH : ∀ i,aF (p i) = aF i := by
   intro i
   by_cases he : p i = i
   · rw [he]
   · exact ((hp i (p i)).2 ⟨rfl,he⟩).2.2.1.symm
 have vK : ∀ i j,R i j -> R (bj i) (bj j) := by
   intro i j h
   refine ⟨hm.2.1 i h.1,hm.2.1 j h.2.1,?_,?_⟩
   · exact lA _ _ _ _ (hcol i) (hcol j) h.2.2.1
   · exact lD hf hm i h.1 j h.2.1 h.2.2.2
 have uo := ik hp bj hmi vK
 have hout : ∀ i,i ∉ S -> p i = i := by
   intro i hi
   by_contra he
   exact hi ((hp i (p i)).2 ⟨rfl,he⟩).1
 refine ⟨p,hpi,oH,uo,hout,?_,hp⟩
 intro x
 constructor
 · intro hfx
   obtain ⟨i,hi,j,hj,hpair,hxi,hxj⟩ :=
     (kL hf hm.1 (gW hm) x).1 hfx
   by_cases hc : aF i = aF j
   · have zJ : R i j := ⟨hi,hj,hc,hpair⟩
     obtain ⟨hpij,hji⟩ := (hp i j).1 zJ
     refine ⟨i,hi,Or.inr ⟨?_,hxi,?_⟩⟩
     · simpa only [hpij] using hji
     · simpa only [hpij] using hxj
   · have hjm : j = bj i := by
       by_contra hne
       have hz := hm.2.2.2 i j hc hne
       rw [hz] at hpair
       contradiction
     exact ⟨i,hi,Or.inl ⟨hxi,hjm ▸ hxj⟩⟩
 · rintro ⟨i,hi,h | h⟩
   · exact mG hf _ _ (oo h.1 h.2) (hm.2.2.1 i hi)
   · have hr := (hp i (p i)).2 ⟨rfl,h.1⟩
     exact mG hf _ _ (oo h.2.1 h.2.2) hr.2.2.2
end bH.g7
namespace bH.g7.RowColumn
open bH.iF.TightReadOnce bH.iF.ReadOncePath
variable {k : ℕ}
abbrev row (i : Fin k) : Fin (k+k) := Fin.castAdd k i
abbrev col (i : Fin k) : Fin (k+k) := Fin.natAdd k i
def bj : Fin (k+k) -> Fin (k+k) := Fin.append col row
def aF : Fin (k+k) -> Bool := Fin.append (fun _ => false) (fun _ => true)
@[local simp] lemma f7 (i : Fin k) : bj (row i) = col i := Fin.append_left _ _ i
@[local simp] lemma jy (i : Fin k) : bj (col i) = row i := Fin.append_right _ _ i
@[local simp] lemma jB (i : Fin k) : aF (row i) = false := Fin.append_left _ _ i
@[local simp] lemma jt (i : Fin k) : aF (col i) = true := Fin.append_right _ _ i
lemma n6 : Function.Involutive (bj (k := k)) := by
 intro i
 induction i using Fin.addCases with
 | left j => exact (congrArg bj (f7 j)).trans (jy j)
 | right j => exact (congrArg bj (jy j)).trans (f7 j)
lemma sy (i : Fin (k+k)) : aF (bj i) ≠ aF i := by
 induction i using Fin.addCases with
 | left j => change aF (bj (row j)) ≠ aF (row j); rw [f7,jt,jB]; decide
 | right j => change aF (bj (col j)) ≠ aF (col j); rw [jy,jB,jt]; decide
lemma dP : Function.Injective (row (k := k)) := Fin.castAdd_injective k k
lemma fu : Function.Injective (col (k := k)) := Fin.natAdd_injective k k
@[local simp] lemma wZ (i j : Fin k) : row i = row j ↔ i = j := dP.eq_iff
@[local simp] lemma xh (i j : Fin k) : col i = col j ↔ i = j := fu.eq_iff
lemma u9 (p : Equiv.Perm (Fin (k+k)))
   (hc : ∀ i,aF (p i) = aF i) (i : Fin k) : ∃ j,p (row i) = row j := by
 have oH := hc (row i)
 generalize he : p (row i) = v at *
 induction v using Fin.addCases with
 | left j => exact ⟨j,rfl⟩
 | right j =>
   rw [jB] at oH
   change aF (col j) = false at oH
   rw [jt] at oH
   contradiction
def aY (p : Equiv.Perm (Fin k)) (x y : Fin k -> Bool) : Bool :=
 decide (∃ i : Fin k,
   (x i = true /\ y i = true) \/
   (p i ≠ i /\ ((x i = true /\ x (p i) = true) \/
     (y i = true /\ y (p i) = true))))
lemma jJ (f : (Fin (k+k) -> Bool) -> Bool)
   (hf : RO Finset.univ f) (hm : bH.g7.Matched bj aF Finset.univ f) :
   ∃ p : Equiv.Perm (Fin k),Function.Involutive p /\
     ∀ x y,f (Fin.append x y) = aY p x y := by
 classical
 obtain ⟨p,hpi,hcol,uo,hout,hfn,hedge⟩ :=
   bH.g7.matched_involution_normal_form n6 sy hf hm
 choose q hq using u9 p hcol
 have y4 : Function.Involutive q := by
   intro i
   apply dP
   rw [← hq (q i),← hq i,hpi (row i)]
 let e : Equiv.Perm (Fin k) := y4.toPerm q
 have qR : ∀ i,p (row i) = row (e i) := hq
 have sQ : ∀ i,p (col i) = col (e i) := by
   intro i
   rw [← f7 i,uo,qR,f7]
 have wS : ∀ i,p (row i) ≠ row i ↔ e i ≠ i := by
   intro i
   rw [qR]
   exact not_congr (dP.eq_iff)
 have wW : ∀ i,p (col i) ≠ col i ↔ e i ≠ i := by
   intro i
   rw [sQ]
   exact not_congr (fu.eq_iff)
 refine ⟨e,y4,?_⟩
 intro x y
 apply Bool.eq_iff_iff.mpr
 rw [hfn]
 simp only [aY,decide_eq_true_eq]
 constructor
 · rintro ⟨v,hv,h⟩
   induction v using Fin.addCases with
   | left i =>
     rcases h with h | ⟨hn,h1,h2⟩
     · refine ⟨i,Or.inl ?_⟩
       simpa only [f7,Fin.append_left,Fin.append_right] using h
     · refine ⟨i,Or.inr ⟨(wS i).mp hn,Or.inl ⟨?_,?_⟩⟩⟩
       · simpa only [Fin.append_left] using h1
       · simpa only [qR,Fin.append_left] using h2
   | right i =>
     rcases h with h | ⟨hn,h1,h2⟩
     · refine ⟨i,Or.inl ?_⟩
       simpa only [jy,Fin.append_left,Fin.append_right] using h.symm
     · refine ⟨i,Or.inr ⟨(wW i).mp hn,Or.inr ⟨?_,?_⟩⟩⟩
       · simpa only [Fin.append_right] using h1
       · simpa only [sQ,Fin.append_right] using h2
 · rintro ⟨i,h | ⟨hn,h | h⟩⟩
   · refine ⟨row i,Finset.mem_univ _,Or.inl ?_⟩
     simpa only [f7,Fin.append_left,Fin.append_right] using h
   · refine ⟨row i,Finset.mem_univ _,Or.inr ⟨(wS i).mpr hn,?_,?_⟩⟩
     · simpa only [Fin.append_left] using h.1
     · simpa only [qR,Fin.append_left] using h.2
   · refine ⟨col i,Finset.mem_univ _,Or.inr ⟨(wW i).mpr hn,?_,?_⟩⟩
     · simpa only [Fin.append_right] using h.1
     · simpa only [sQ,Fin.append_right] using h.2
lemma gC (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
   (i j : Fin k) :
   aY p (pair i j) (fun _ => false) = true ↔ p i = j /\ j ≠ i := by
 simp only [aY,decide_eq_true_eq,Bool.false_eq_true,and_false,or_false,false_or,
   pair]
 constructor
 · rintro ⟨a,hn,ha,hpa⟩
   have ha' : a = i \/ a = j := by simpa using ha
   have hpa' : p a = i \/ p a = j := by simpa using hpa
   rcases ha' with hai | haj
   · subst a
     rcases hpa' with h | h
     · exact False.elim (hn h)
     · exact ⟨h,fun hji => hn (h.trans hji)⟩
   · subst a
     rcases hpa' with h | h
     · have hij : p i = j := by rw [← h,hp j]
       exact ⟨hij,fun hji => hn (h.trans hji.symm)⟩
     · exact False.elim (hn h)
 · rintro ⟨hij,hji⟩
   refine ⟨i,?_,?_,?_⟩
   · exact fun h => hji (hij.symm.trans h)
   · simp
   · simp [hij]
lemma kv (p q : Equiv.Perm (Fin k))
   (hp : Function.Involutive p) (hq : Function.Involutive q)
   (he : ∀ x y,aY p x y = aY q x y) : p = q := by
 have hr : ∀ i j,(p i = j /\ j ≠ i) ↔ (q i = j /\ j ≠ i) := by
   intro i j
   rw [← gC p hp i j,← gC q hq i j,he]
 apply Equiv.ext
 intro i
 by_cases hn : p i = i
 · by_cases hnq : q i = i
   · exact hn.trans hnq.symm
   · have h := (hr i (q i)).2 ⟨rfl,hnq⟩
     exact False.elim (hnq (h.1.symm.trans hn))
 · exact ((hr i (p i)).1 ⟨rfl,hn⟩).1.symm
lemma gH (f : (Fin (k+k) -> Bool) -> Bool)
   (hf : RO Finset.univ f) (hm : bH.g7.Matched bj aF Finset.univ f) :
   ∃! p : Equiv.Perm (Fin k),Function.Involutive p /\
     ∀ x y,f (Fin.append x y) = aY p x y := by
 obtain ⟨p,hp,he⟩ := jJ f hf hm
 refine ⟨p,⟨hp,he⟩,?_⟩
 intro q hq
 apply kv q p hq.1 hp
 intro x y
 exact (hq.2 x y).symm.trans (he x y)
end bH.g7.RowColumn
namespace bH.g7.RowColumn
open bH.iF.TightReadOnce bH.iF.ReadOncePath
variable {k : ℕ}
lemma mH (hk : 2 ≤ k) (i : Fin k) : ∃ j : Fin k,j ≠ i := by
 let z : Fin k := ⟨0,by omega⟩
 let o : Fin k := ⟨1,by omega⟩
 by_cases hi : i = z
 · refine ⟨o,?_⟩
   intro h
   have hv := congrArg Fin.val (h.trans hi)
   change 1 = 0 at hv
   omega
 · exact ⟨z,Ne.symm hi⟩
lemma jO (hk : 2 ≤ k) (f : (Fin (k+k) -> Bool) -> Bool)
   (hmono : ∀ x y,(∀ i,x i = true -> y i = true) -> f x = true -> f y = true)
   (hrep : ∀ i j : Fin k,f (pair (row i) (col j)) = decide (i = j)) :
   bH.g7.Matched bj aF Finset.univ f := by
 have hs : bH.g7.NoSingle f := by
   intro v
   apply Bool.eq_false_iff.mpr
   intro htrue
   induction v using Fin.addCases with
   | left i =>
     obtain ⟨j,hji⟩ := mH hk i
     have hx := hmono (single (row i)) (pair (row i) (col j)) (by
       intro t ht
       have he : t = row i := by simpa [single] using ht
       simp [pair,he]) htrue
     rw [hrep,decide_eq_false (Ne.symm hji)] at hx
     contradiction
   | right i =>
     obtain ⟨j,hji⟩ := mH hk i
     have hx := hmono (single (col i)) (pair (row j) (col i)) (by
       intro t ht
       have he : t = col i := by simpa [single] using ht
       simp [pair,he]) htrue
     rw [hrep,decide_eq_false hji] at hx
     contradiction
 refine ⟨hs,by simp,?_,?_⟩
 · intro v hv
   induction v using Fin.addCases with
   | left i =>
     change f (pair (row i) (bj (row i))) = true
     rw [f7,hrep]
     simp
   | right i =>
     change f (pair (col i) (bj (col i))) = true
     rw [jy,pair_comm,hrep]
     simp
 · intro v w hc hne
   induction v using Fin.addCases with
   | left i =>
     induction w using Fin.addCases with
     | left j => exact False.elim (hc ((jB i).trans (jB j).symm))
     | right j =>
       change col j ≠ bj (row i) at hne
       rw [f7] at hne
       have hij : i ≠ j := fun h => hne (congrArg col h.symm)
       rw [hrep,decide_eq_false hij]
   | right i =>
     induction w using Fin.addCases with
     | left j =>
       change row j ≠ bj (col i) at hne
       rw [jy] at hne
       have hji : j ≠ i := fun h => hne (congrArg row h)
       rw [pair_comm,hrep,decide_eq_false hji]
     | right j => exact False.elim (hc ((jt i).trans (jt j).symm))
lemma iJ (hk : 2 ≤ k) (f : (Fin (k+k) -> Bool) -> Bool)
   (hf : RO Finset.univ f)
   (hrep : ∀ i j : Fin k,f (pair (row i) (col j)) = decide (i = j)) :
   ∃! p : Equiv.Perm (Fin k),Function.Involutive p /\
     ∀ x y,f (Fin.append x y) = aY p x y := by
 exact gH f hf (jO hk f (mG hf) hrep)
end bH.g7.RowColumn
namespace bH.g7.CircuitForward
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open bH.iF.TightReadOnce bH.iF.ReadOncePath
open bH.g7.RowColumn
lemma pH (g : Gate) (hg : g.op = GateOp.and \/ g.op = GateOp.or)
   (w w' : List Bool)
   (h : ∀ i ∈ g.inputs,w.getD i false = true -> w'.getD i false = true)
   (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
   g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
 rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
 · intro i hi
   exact h i hi (he i hi)
 · obtain ⟨i,hi,hv⟩ := he
   exact ⟨i,hi,h i hi hv⟩
lemma oU (gs : List Gate)
   (hm : ∀ g ∈ gs,g.op = GateOp.and \/ g.op = GateOp.or) :
   ∀ w w' : List Bool,w.length = w'.length ->
   (∀ i,w.getD i false = true -> w'.getD i false = true) ->
   ∀ i,(wiresFrom gs w).getD i false = true -> (wiresFrom gs w').getD i false = true := by
 induction gs with
 | nil => intro w w' hl h; exact h
 | cons g gs ih =>
   intro w w' hl h i hi
   apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
     (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
     (w' ++ [g.op.eval (g.inputs.map fun a => w'.getD a false)]) (by simp [hl]) ?_ i hi
   intro j hj
   by_cases he : j = w.length
   · rw [he,getD_snoc_eq] at hj
     rw [he,hl,getD_snoc_eq]
     exact pH g (hm g List.mem_cons_self) w w' (fun a _ => h a) hj
   · rw [getD_snoc_ne _ _ _ _ he] at hj
     rw [getD_snoc_ne _ _ _ _ (by omega)]
     exact h j hj
lemma qB {n : ℕ} (C : Circuit) (hm : Monotone2 C)
   (x y : Fin n -> Bool) (h : ∀ i,x i = true -> y i = true)
   (he : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
 apply oU C.gates (fun g hg => (hm g hg).1)
   (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output he
 intro j hj
 by_cases hjn : j < n
 · have hx : x ⟨j,hjn⟩ = true := by simpa [hjn] using hj
   simpa [hjn] using h ⟨j,hjn⟩ hx
 · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
   contradiction
lemma i8 {k : ℕ} (i j : Fin k) :
   List.ofFn (pair (row i) (col j)) = oneEach i j := by
 have h : pair (row i) (col j) =
     Fin.append (single i) (single j) := by
   funext v
   induction v using Fin.addCases with
   | left t =>
     have hne : row t ≠ col j := by
       intro h
       have hval := congrArg (fun z : Fin (k+k) => z.val) h
       change t.val = k + j.val at hval
       omega
     simp only [pair,single,Fin.append_left]
     simp only [hne,or_false]
     exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using dP.eq_iff)
   | right t =>
     have hne : col t ≠ row i := by
       intro h
       have hval := congrArg (fun z : Fin (k+k) => z.val) h
       change k + t.val = i.val at hval
       omega
     simp only [pair,single,Fin.append_right]
     simp only [hne,false_or]
     exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using fu.eq_iff)
 rw [h,List.ofFn_fin_append]
 rfl
lemma lT {k : ℕ} (hk : 2 ≤ k) (C : Circuit)
   (hm : Monotone2 C) (hsize : C.size + 1 ≤ 2*k)
   (hrep : Represents (fun i j : Fin k => decide (i = j)) C) :
   RO Finset.univ (fun x : Fin (k+k) -> Bool => C.eval (List.ofFn x)) := by
 let f : (Fin (k+k) -> Bool) -> Bool := fun x => C.eval (List.ofFn x)
 have wU : ∀ i j : Fin k,f (pair (row i) (col j)) = decide (i = j) := by
   intro i j
   exact (congrArg C.eval (i8 i j)).trans (hrep i j)
 have hm' := jO hk f (qB C hm) wU
 have qm : ∀ i ∈ (Finset.univ : Finset (Fin (k+k))),
     ∃ x y : Fin (k+k) -> Bool,(∀ j,j ≠ i -> x j = y j) /\
       (C.wires (List.ofFn x)).getD C.output false ≠
         (C.wires (List.ofFn y)).getD C.output false := by
   intro i hi
   refine ⟨pair i (bj i),single (bj i),?_,?_⟩
   · intro j hji
     simp [pair,single,hji]
   · change f (pair i (bj i)) ≠ f (single (bj i))
     rw [hm'.2.2.1 i hi,hm'.1 (bj i)]
     decide
 have hvalid : C.output < (k+k) + C.gates.length := by
   let z : Fin k := ⟨0,by omega⟩
   have ht := wU z z
   have ht' : (C.wires (List.ofFn (pair (row z) (col z)))).getD C.output false = true := by
     change f (pair (row z) (col z)) = true
     simpa only [decide_true] using ht
   by_contra hn
   have hl : (C.wires (List.ofFn (pair (row z) (col z)))).length = (k+k) + C.gates.length := by
     rw [wires_eq,length_wiresFrom]
     simp
   rw [List.getD_eq_default _ _ (by omega)] at ht'
   contradiction
 have hb := kO C (k+k) C.gates.length C.output le_rfl hvalid
   (fun g hg => (hm g hg).2) Finset.univ qm
 have hcard : (Finset.univ : Finset (Fin (k+k))).card = C.gates.length + 1 := by
   simp only [Finset.card_univ,Fintype.card_fin] at hb ⊢
   change C.gates.length + 1 ≤ 2*k at hsize
   omega
 exact oT C (k+k) C.gates.length C.output le_rfl hvalid
   (fun g hg => ⟨by have h := (hm g hg).1; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h; tauto,(hm g hg).2⟩)
   Finset.univ hcard qm
lemma gx {k : ℕ} (hk : 2 ≤ k) (C : Circuit)
   (hm : Monotone2 C) (hsize : C.size + 1 ≤ 2*k)
   (hrep : Represents (fun i j : Fin k => decide (i = j)) C) :
   ∃! p : Equiv.Perm (Fin k),Function.Involutive p /\
     ∀ x y,C.eval (List.ofFn x ++ List.ofFn y) = aY p x y := by
 have h := iJ hk
   (fun x : Fin (k+k) -> Bool => C.eval (List.ofFn x))
   (lT hk C hm hsize hrep) (by
     intro i j
     rw [i8]
     exact hrep i j)
 simpa only [List.ofFn_fin_append] using h
end bH.g7.CircuitForward
namespace bH.g7
lemma official_forward : ∀ (k : Nat),2 ≤ k -> ∀ f : (Fin k -> Bool) -> (Fin k -> Bool) -> Bool,
 (∃ C : PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C /\ C.size + 1 ≤ 2*k /\
   PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C /\
   ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) ->
 ∃! p : Equiv.Perm (Fin k),Function.Involutive p /\
   ∀ x y,f x y = decide (∃ i : Fin k,
       (x i = true /\ y i = true) \/
       (p i ≠ i /\ ((x i = true /\ x (p i) = true) \/
         (y i = true /\ y (p i) = true)))) := by
 intro k hk f h
 obtain ⟨C,hm,hs,hr,he⟩ := h
 obtain ⟨p,hp,hu⟩ := CircuitForward.gx hk C hm hs hr
 refine ⟨p,⟨hp.1,?_⟩,?_⟩
 · intro x y
   exact (he x y).trans (hp.2 x y)
 · intro q hq
   apply hu q
   refine ⟨hq.1,?_⟩
   intro x y
   exact (he x y).symm.trans (hq.2 x y)
end bH.g7
namespace bH.yx.ROCompiler
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open bH.iF.TightReadOnce
variable {n : ℕ}
def GateOK (g : Gate) : Prop :=
 (g.op = GateOp.and \/ g.op = GateOp.or) /\ g.inputs.length ≤ 2
def jE (S : Finset (Fin n)) (f : (Fin n -> Bool) -> Bool) : Prop :=
 ∀ m : ℕ,n ≤ m -> ∃ (gs : List Gate) (out : ℕ),
   (∀ g ∈ gs,GateOK g) /\ gs.length + 1 = S.card /\ out < m + gs.length /\
   ∀ w : List Bool,w.length = m ->
     (wiresFrom gs w).getD out false = f (fun i : Fin n => w.getD i.val false)
lemma qd (i : Fin n) : jE {i} (fun x => x i) := by
 intro m hm
 refine ⟨[],i.val,?_,by simp,?_,?_⟩
 · simp
 · have := i.isLt
   simp only [List.length_nil,Nat.add_zero]
   omega
 · intro w hw
   rfl
lemma lL {A B : Finset (Fin n)} {a b : (Fin n -> Bool) -> Bool}
   (hd : Disjoint A B) (ha : jE A a) (hb : jE B b)
   (op : GateOp) (hop : op = GateOp.and \/ op = GateOp.or) :
   jE (A ∪ B) (fun x => op.eval [a x,b x]) := by
 intro m hm
 obtain ⟨ga,oa,oka,lena,ra,eva⟩ := ha m hm
 obtain ⟨gb,ob,okb,lenb,rb,evb⟩ := hb (m + ga.length) (by omega)
 let M := m + ga.length + gb.length
 refine ⟨ga ++ gb ++ [⟨op,[oa,ob]⟩],M,?_,?_,?_,?_⟩
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
   rw [wiresFrom_append,wiresFrom_append]
   let wa := wiresFrom ga w
   let wb := wiresFrom gb wa
   have hwa : wa.length = m + ga.length := by
     dsimp [wa]
     rw [length_wiresFrom,hw]
   have hwb : wb.length = M := by
     dsimp [wb]
     rw [length_wiresFrom,hwa]
   have AN : wb.getD oa false = a (fun i : Fin n => w.getD i.val false) := by
     dsimp [wb]
     rw [getD_wiresFrom gb wa oa (by omega)]
     exact eva w hw
   have AQ : wb.getD ob false = b (fun i : Fin n => w.getD i.val false) := by
     dsimp [wb]
     rw [evb wa hwa]
     congr 1
     funext i
     exact getD_wiresFrom ga w i.val (by have := i.isLt; omega)
   change (wiresFrom [⟨op,[oa,ob]⟩] wb).getD M false = _
   change (wb ++ [op.eval [wb.getD oa false,wb.getD ob false]]).getD M false = _
   rw [← hwb,getD_snoc_eq,AN,AQ]
lemma rC {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (h : RO S f) : jE S f := by
 apply h jE qd
 intro A B a b hd ha hb
 constructor
 · simpa only [GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
     using lL hd ha hb GateOp.and (Or.inl rfl)
 · simpa only [GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
     using lL hd ha hb GateOp.or (Or.inr rfl)
lemma sH {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (h : RO S f) :
   ∃ C : Circuit,Monotone2 C /\ C.size + 1 = S.card /\ C.output < n + C.size /\
     ∀ x : Fin n -> Bool,C.eval (List.ofFn x) = f x := by
 obtain ⟨gs,out,hok,hlen,hout,heval⟩ := rC h n (le_refl n)
 refine ⟨⟨gs,out⟩,?_,hlen,hout,?_⟩
 · intro g hg
   obtain ⟨ho,hl⟩ := hok g hg
   exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ho,hl⟩
 · intro x
   change (wiresFrom gs (List.ofFn x)).getD out false = f x
   rw [heval (List.ofFn x) (by simp)]
   congr 1
   funext i
   simp
lemma ro_circuit_exists {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool}
   (h : RO S f) :
   ∃ C : Circuit,Monotone2 C /\ C.size + 1 = S.card /\
     ∀ x : Fin n -> Bool,C.eval (List.ofFn x) = f x := by
 obtain ⟨C,hC,hsize,_,heval⟩ := sH h
 exact ⟨C,hC,hsize,heval⟩
end bH.yx.ROCompiler
namespace bH.tY.InvolutionRO
open bH.iF.TightReadOnce bH.iF.ReadOncePath bH.g7.RowColumn
variable {k : ℕ}
lemma iN (i j : Fin k) : row i ≠ col j := by
 intro h
 have e := congrArg (fun z : Fin (k+k) => z.val) h
 change i.val = k + j.val at e
 omega
lemma lW (i j : Fin k) : col i ≠ row j := (iN j i).symm
def supp (S : Finset (Fin k)) : Finset (Fin (k+k)) := S.image row ∪ S.image col
def clause (p : Equiv.Perm (Fin k)) (i : Fin k) (x : Fin (k+k) -> Bool) : Prop :=
 (x (row i) = true /\ x (col i) = true) \/
 (p i ≠ i /\ ((x (row i) = true /\ x (row (p i)) = true) \/
   (x (col i) = true /\ x (col (p i)) = true)))
noncomputable def f6 (p : Equiv.Perm (Fin k)) (S : Finset (Fin k))
   (x : Fin (k+k) -> Bool) : Bool := by
 classical
 exact decide (∃ i ∈ S,clause p i x)
lemma sV (S T : Finset (Fin k)) : supp (S ∪ T) = supp S ∪ supp T := by
 classical
 ext i
 simp only [supp,Finset.mem_union,Finset.mem_image]
 aesop
lemma pZ {S T : Finset (Fin k)} (hd : Disjoint S T) :
   Disjoint (supp S) (supp T) := by
 classical
 rw [Finset.disjoint_left] at hd ⊢
 intro v hv hw
 simp only [supp,Finset.mem_union,Finset.mem_image] at hv hw
 rcases hv with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
 · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
   · exact hd hi ((dP he) ▸ hj)
   · exact lW j i he
 · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
   · exact iN j i he
   · exact hd hi ((fu he) ▸ hj)
lemma qJ (p : Equiv.Perm (Fin k)) (S T : Finset (Fin k)) :
   f6 p (S ∪ T) = fun x => f6 p S x || f6 p T x := by
 funext x
 apply Bool.eq_iff_iff.mpr
 simp only [f6,decide_eq_true_eq,Bool.or_eq_true,Finset.mem_union]
 aesop
lemma rO (p : Equiv.Perm (Fin k)) (i : Fin k) (hi : p i = i) :
   RO (supp {i}) (f6 p {i}) := by
 have hr := lS (by simpa using iN i i) (gV (row i)) (gV (col i))
 convert hr using 1
 · simp [supp]
 · funext x
   simp [f6,clause,hi]
lemma tJ (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
   (i j : Fin k) (hij : i ≠ j) (hpij : p i = j) :
   RO (supp {i,j}) (f6 p {i,j}) := by
 have xO : p j = i := by rw [← hpij,hp i]
 have hA := nQ (by simpa using iN i j) (gV (row i)) (gV (col j))
 have hB := nQ (by simpa using lW i j) (gV (col i)) (gV (row j))
 have hd : Disjoint (({row i} ∪ {col j}) : Finset (Fin (k+k))) ({col i} ∪ {row j}) := by
   rw [Finset.disjoint_left]
   intro v hv hw
   simp only [Finset.mem_union,Finset.mem_singleton] at hv hw
   rcases hv with rfl | rfl
   · rcases hw with he | he
     · exact iN i i he
     · exact hij (dP he)
   · rcases hw with he | he
     · exact hij.symm (fu he)
     · exact lW j j he
 have hr := lS hd hA hB
 convert hr using 1
 · ext v
   simp only [supp,Finset.image_insert,Finset.image_singleton,Finset.mem_union,
     Finset.mem_insert,Finset.mem_singleton]
   tauto
 · funext x
   apply Bool.eq_iff_iff.mpr
   simp only [f6,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton,
     exists_eq_or_imp,exists_eq_left,clause,hpij,xO,Bool.and_eq_true,Bool.or_eq_true]
   tauto
lemma rZ (p : Equiv.Perm (Fin k)) (S T : Finset (Fin k))
   (hd : Disjoint S T) (hS : RO (supp S) (f6 p S)) (hT : RO (supp T) (f6 p T)) :
   RO (supp (S ∪ T)) (f6 p (S ∪ T)) := by
 rw [sV,qJ]
 exact nQ (pZ hd) hS hT
lemma qy (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
   (S : Finset (Fin k)) (hS : ∀ i ∈ S,p i ∈ S) (hne : S.Nonempty) :
   RO (supp S) (f6 p S) := by
 classical
 revert hS hne
 refine Finset.strongInductionOn S ?_
 intro S ih hS hne
 obtain ⟨i,hi⟩ := hne
 by_cases hfix : p i = i
 · let T := S.erase i
   have ht : T ⊂ S := Finset.erase_ssubset hi
   have sN : ∀ j ∈ T,p j ∈ T := by
     intro j hj
     have hjs := Finset.mem_erase.mp hj
     apply Finset.mem_erase.mpr
     constructor
     · intro he
       apply hjs.1
       exact p.injective (he.trans hfix.symm)
     · exact hS j hjs.2
   have heq : S = {i} ∪ T := by simp [T,hi]
   by_cases hempty : T = ∅
   · rw [heq,hempty,Finset.union_empty]
     exact rO p i hfix
   · rw [heq]
     apply rZ p {i} T
     · simp [T]
     · exact rO p i hfix
     · exact ih T ht sN (Finset.nonempty_iff_ne_empty.mpr hempty)
 · let j := p i
   have hij : i ≠ j := Ne.symm hfix
   have hj : j ∈ S := hS i hi
   have xO : p j = i := hp i
   let T := (S.erase i).erase j
   have ht : T ⊂ S :=
     lt_of_le_of_lt (Finset.erase_subset j (S.erase i)) (Finset.erase_ssubset hi)
   have sN : ∀ a ∈ T,p a ∈ T := by
     intro a ha
     have h := Finset.mem_erase.mp ha
     have h' := Finset.mem_erase.mp h.2
     apply Finset.mem_erase.mpr
     constructor
     · intro he
       exact h'.1 (p.injective he)
     · apply Finset.mem_erase.mpr
       constructor
       · intro he
         exact h.1 (p.injective (he.trans xO.symm))
       · exact hS a h'.2
   have heq : S = {i,j} ∪ T := by
     ext a
     simp only [T,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
       Finset.mem_erase]
     constructor
     · intro ha
       by_cases hai : a = i
       · exact Or.inl (Or.inl hai)
       · by_cases haj : a = j
         · exact Or.inl (Or.inr haj)
         · exact Or.inr ⟨haj,hai,ha⟩
     · rintro ((rfl | rfl) | ⟨-,-,ha⟩)
       · exact hi
       · exact hj
       · exact ha
   by_cases hempty : T = ∅
   · rw [heq,hempty,Finset.union_empty]
     exact tJ p hp i j hij rfl
   · rw [heq]
     apply rZ p {i,j} T
     · simp [T,Finset.disjoint_left]
     · exact tJ p hp i j hij rfl
     · exact ih T ht sN (Finset.nonempty_iff_ne_empty.mpr hempty)
lemma pW (hk : 0 < k) (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
   RO Finset.univ (fun x : Fin (k+k) -> Bool => aY p (fun i => x (row i))
     (fun i => x (col i))) := by
 have h := qy p hp Finset.univ (by simp) ⟨⟨0,hk⟩,Finset.mem_univ _⟩
 have hs : supp (Finset.univ : Finset (Fin k)) = Finset.univ := by
   ext v
   simp only [Finset.mem_univ,iff_true]
   induction v using Fin.addCases with
   | left i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
   | right i => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
 rw [hs] at h
 have he : f6 p Finset.univ = (fun x : Fin (k+k) -> Bool => aY p (fun i => x (row i)) (fun i => x (col i))) := by
   funext x
   apply Bool.eq_iff_iff.mpr
   simp [f6,clause,aY]
 rw [he] at h
 exact h
end bH.tY.InvolutionRO
namespace bH.tY.InverseBridge
open bH.g7.RowColumn bH.iF.TightReadOnce bH.iF.ReadOncePath
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
lemma li {k : ℕ} (p : Equiv.Perm (Fin k)) (i j : Fin k) :
   aY p (single i) (single j) = decide (i = j) := by
 apply Bool.eq_iff_iff.mpr
 simp only [aY,single,decide_eq_true_eq]
 constructor
 · rintro ⟨a,⟨hai,haj⟩ | ⟨hne,h | h⟩⟩
   · exact hai.symm.trans haj
   · exact False.elim (hne (h.2.trans h.1.symm))
   · exact False.elim (hne (h.2.trans h.1.symm))
 · intro hij
   exact ⟨i,Or.inl ⟨rfl,hij⟩⟩
lemma gK
   (tT : ∀ {n : ℕ} {S : Finset (Fin n)} {f : (Fin n -> Bool) -> Bool},
     RO S f -> ∃ C : Circuit,Monotone2 C /\ C.size + 1 = S.card /\
       ∀ x,C.eval (List.ofFn x) = f x)
   {k : ℕ} (hk : 0 < k) (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
   ∃ C : Circuit,Monotone2 C /\ C.size + 1 ≤ 2*k /\
     Represents (fun i j : Fin k => decide (i = j)) C /\
     ∀ x y,C.eval (List.ofFn x ++ List.ofFn y) = aY p x y := by
 obtain ⟨C,hm,hs,he⟩ := tT (InvolutionRO.pW hk p hp)
 have hfull : ∀ x y,C.eval (List.ofFn x ++ List.ofFn y) = aY p x y := by
   intro x y
   simpa only [List.ofFn_fin_append,Fin.append_left,Fin.append_right]
     using he (Fin.append x y)
 refine ⟨C,hm,?_,?_,hfull⟩
 · simp only [Finset.card_univ,Fintype.card_fin] at hs
   omega
 · intro i j
   change C.eval (List.ofFn (single i) ++ List.ofFn (single j)) = decide (i = j)
   rw [hfull,li]
end bH.tY.InverseBridge
namespace bH.tY
lemma official_full : ∀ (k : Nat),2 ≤ k -> ∀ f : (Fin k -> Bool) -> (Fin k -> Bool) -> Bool,
 (∃ C : PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C /\ C.size + 1 ≤ 2*k /\
   PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C /\
   ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
 ∃! p : Equiv.Perm (Fin k),Function.Involutive p /\
   ∀ x y,f x y = decide (∃ i : Fin k,
       (x i = true /\ y i = true) \/
       (p i ≠ i /\ ((x i = true /\ x (p i) = true) \/
         (y i = true /\ y (p i) = true)))) := by
 intro k hk f
 constructor
 · exact bH.g7.official_forward k hk f
 · rintro ⟨p,⟨hp,hf⟩,hu⟩
   obtain ⟨C,hm,hs,hr,he⟩ := InverseBridge.gK
     (fun h => bH.yx.ROCompiler.ro_circuit_exists h) (by omega : 0 < k) p hp
   refine ⟨C,hm,hs,hr,?_⟩
   intro x y
   exact (hf x y).trans (he x y).symm
end bH.tY
open Polynomial
variable {k : ℕ}
def form (p : Equiv.Perm (Fin k)) : (Fin k -> Bool) -> (Fin k -> Bool) -> Bool :=
 fun x y => decide (∃ i : Fin k,(x i = true /\ y i = true) \/
   (p i ≠ i /\ ((x i = true /\ x (p i) = true) \/ (y i = true /\ y (p i) = true))))
lemma j5 (p : Equiv.Perm (Fin k)) (hp : ∀ i,p (p i) = i) (a b : Fin k)
   (hab : a ≠ b) :
   form p (fun i => decide (i ∈ ({a,b} : Finset (Fin k)))) (fun _ => false) =
     decide (p a = b) := by
 unfold form
 rw [decide_eq_decide]
 simp only [Finset.mem_insert,Finset.mem_singleton,decide_eq_true_eq,Bool.false_eq_true,
   and_false,false_or,or_false]
 constructor
 · rintro ⟨i,hi,hxi,hxpi⟩
   rcases hxi with h1 | h1 <;> rcases hxpi with h2 | h2
   · exact absurd (h2.trans h1.symm) hi
   · rw [h1] at h2; exact h2
   · rw [h1] at h2; rw [← h2,hp b]
   · exact absurd (h2.trans h1.symm) hi
 · intro h
   exact ⟨a,by rw [h]; exact Ne.symm hab,Or.inl rfl,Or.inr h⟩
lemma vA (p q : Equiv.Perm (Fin k)) (hp : ∀ i,p (p i) = i) (hq : ∀ i,q (q i) = i)
   (h : form p = form q) : p = q := by
 refine Equiv.ext fun i => ?_
 by_cases hpi : p i = i
 · by_contra hne
   have y4 : q i ≠ i := fun h' => hne (hpi.trans h'.symm)
   have h1 := j5 q hq i (q i) (Ne.symm y4)
   rw [← h,j5 p hp i (q i) (Ne.symm y4)] at h1
   simp only [decide_true,decide_eq_true_eq] at h1
   exact hne h1
 · have h1 := j5 p hp i (p i) (Ne.symm hpi)
   rw [h,j5 q hq i (p i) (Ne.symm hpi)] at h1
   simp only [decide_true,decide_eq_true_eq] at h1
   exact h1.symm
lemma sl (hk : 2 ≤ k) (f : (Fin k -> Bool) -> (Fin k -> Bool) -> Bool) :
   (∃ C : PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C /\
     C.size + 1 ≤ 2 * k /\
     PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C /\
     ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
   ∃ p : Equiv.Perm (Fin k),(∀ i,p (p i) = i) /\ f = form p := by
 rw [bH.tY.official_full k hk f]
 constructor
 · rintro ⟨p,⟨hp,hf⟩,-⟩
   exact ⟨p,hp,funext fun x => funext fun y => hf x y⟩
 · rintro ⟨p,hp,rfl⟩
   refine ⟨p,⟨hp,fun x y => rfl⟩,?_⟩
   rintro q ⟨hq,hfq⟩
   exact (vA p q hp hq (funext fun x => funext fun y => hfq x y)).symm
def aQ (p : Equiv.Perm (Fin k)) : Finset (Fin k × Fin k) :=
 Finset.univ.filter (fun e => e.1 < e.2 /\ p e.1 = e.2)
def moved (p : Equiv.Perm (Fin k)) : Finset (Fin k) :=
 Finset.univ.filter (fun i => p i ≠ i)
lemma wg (p : Equiv.Perm (Fin k)) :
   (Finset.univ.filter (fun i => i < p i)).card = (aQ p).card := by
 apply Finset.card_nbij' (fun i => (i,p i)) (fun e => e.1)
 · intro i hi
   simp only [Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at hi
   simp [aQ,hi]
 · intro e he
   simp only [aQ,Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at he
   simp only [Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq]
   rw [he.2]; exact he.1
 · intro i _; rfl
 · intro e he
   simp only [aQ,Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at he
   ext <;> simp [he.2]
lemma tS (p : Equiv.Perm (Fin k)) (hp : ∀ i,p (p i) = i) :
   (Finset.univ.filter (fun i => p i < i)).card = (aQ p).card := by
 apply Finset.card_nbij' (fun i => (p i,i)) (fun e => e.2)
 · intro i hi
   simp only [Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at hi
   simp [aQ,hi,hp i]
 · intro e he
   simp only [aQ,Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at he
   simp only [Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq]
   rw [← he.2,hp]; rw [he.2]; exact he.1
 · intro i _; rfl
 · intro e he
   simp only [aQ,Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at he
   ext
   · simp only; rw [← he.2,hp]
   · rfl
lemma lU (p : Equiv.Perm (Fin k)) (hp : ∀ i,p (p i) = i) :
   2 * (aQ p).card = (moved p).card := by
 have hsplit : moved p = Finset.univ.filter (fun i => i < p i) ∪
     Finset.univ.filter (fun i => p i < i) := by
   ext i
   simp only [moved,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
   constructor
   · intro h; rcases lt_or_gt_of_ne h with h | h
     · exact Or.inr h
     · exact Or.inl h
   · rintro (h | h)
     · exact ne_of_gt h
     · exact ne_of_lt h
 rw [hsplit,Finset.card_union_of_disjoint,wg,tS p hp]
 · ring
 · rw [Finset.disjoint_left]
   intro i h1 h2
   simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h1 h2
   exact lt_asymm h1 h2
lemma pY (p : Equiv.Perm (Fin k)) (hp : ∀ i,p (p i) = i) :
   (aQ p).card ≤ k / 2 := by
 have h1 := lU p hp
 have h2 : (moved p).card ≤ k := by
   calc (moved p).card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
     _ = k := by simp
 omega
lemma kD {R : Type*} [CommRing R] [CharP R 2] (u : ℤˣ) (a : R) :
   u • a = a := by
 rcases Int.units_eq_one_or u with rfl | rfl
 · simp
 · rw [Units.neg_smul,one_smul,CharTwo.neg_eq]
lemma qH {R : Type*} [CommRing R] [CharP R 2] (D : Matrix (Fin k) (Fin k) R)
   (hsym : ∀ i j,D i j = D j i) :
   D.det = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => ∀ i,σ (σ i) = i),
     ∏ i,D (σ i) i := by
 rw [Matrix.det_apply]
 simp only [kD]
 rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
   (fun σ : Equiv.Perm (Fin k) => ∀ i,σ (σ i) = i)]
 have hzero : ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => ¬ ∀ i,σ (σ i) = i),
     ∏ i,D (σ i) i = 0 := by
   have hinv : ∀ σ : Equiv.Perm (Fin k),(∀ i,σ⁻¹ (σ⁻¹ i) = i) ↔ ∀ i,σ (σ i) = i := by
     intro σ
     constructor
     · intro h i
       have := h (σ (σ i))
       simp at this
       exact this.symm
     · intro h i
       have := h (σ⁻¹ (σ⁻¹ i))
       simp at this
       exact this.symm
   have hval : ∀ σ : Equiv.Perm (Fin k),∏ i,D (σ⁻¹ i) i = ∏ i,D (σ i) i := by
     intro σ
     rw [← Equiv.prod_comp σ (fun i => D (σ⁻¹ i) i)]
     simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply]
     exact Finset.prod_congr rfl fun i _ => hsym _ _
   refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
   · intro σ _
     rw [hval,CharTwo.add_self_eq_zero]
   · intro σ hσ _ heq
     simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hσ
     apply hσ
     intro i
     have : σ⁻¹ (σ i) = σ (σ i) := by rw [heq]
     simp at this
     exact this.symm
   · intro σ hσ
     simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hσ ⊢
     rwa [hinv]
   · intro σ _
     exact inv_inv σ
 rw [hzero,add_zero]
section zU
variable (pos neg : Finset (Fin k × Fin k))
abbrev Free (i : Fin k) : Prop := ∀ e ∈ pos,i ≠ e.1 /\ i ≠ e.2
noncomputable def partner (i : Fin k) : Fin k :=
 if h : ∃ e ∈ pos,e.1 = i then (Classical.choose h).2
 else if h' : ∃ e ∈ pos,e.2 = i then (Classical.choose h').1 else i
abbrev G (a b : Fin k) : Prop := Free pos a /\ Free pos b /\ (min a b,max a b) ∉ neg
abbrev Good (σ : Equiv.Perm (Fin k)) : Prop := ∀ i,σ i ≠ i -> G pos neg (σ i) i
variable {pos neg}
lemma jZ {i : Fin k} (hi : ¬ Free pos i) : ∃ e ∈ pos,i = e.1 \/ i = e.2 := by
 by_contra h
 push_neg at h
 exact hi h
section Consistent
variable (hlt : ∀ e ∈ pos ∪ neg,e.1 < e.2)
 (hdisj : ∀ e ∈ pos,∀ g ∈ pos,e ≠ g ->
   Disjoint ({e.1,e.2} : Finset (Fin k)) ({g.1,g.2} : Finset (Fin k)))
include hdisj
lemma share {e g : Fin k × Fin k} (he : e ∈ pos) (hg : g ∈ pos) (v : Fin k)
   (hv1 : v = e.1 \/ v = e.2) (hv2 : v = g.1 \/ v = g.2) : e = g := by
 by_contra hne
 have h := hdisj e he g hg hne
 rw [Finset.disjoint_left] at h
 apply h (a := v)
 · rcases hv1 with h1 | h1 <;> simp [h1]
 · rcases hv2 with h2 | h2 <;> simp [h2]
lemma iV {e : Fin k × Fin k} (he : e ∈ pos) : partner pos e.1 = e.2 := by
 unfold partner
 have h : ∃ g ∈ pos,g.1 = e.1 := ⟨e,he,rfl⟩
 rw [dif_pos h]
 obtain ⟨hg,hg1⟩ := Classical.choose_spec h
 rw [share hdisj hg he e.1 (Or.inl hg1.symm) (Or.inl rfl)]
include hlt in
lemma i9 {e : Fin k × Fin k} (he : e ∈ pos) : partner pos e.2 = e.1 := by
 unfold partner
 have hn : ¬ ∃ g ∈ pos,g.1 = e.2 := by
   rintro ⟨g,hg,hg1⟩
   have hge := share hdisj hg he e.2 (Or.inl hg1.symm) (Or.inr rfl)
   subst hge
   exact absurd hg1 (ne_of_lt (hlt g (Finset.mem_union_left _ hg)))
 rw [dif_neg hn]
 have h : ∃ g ∈ pos,g.2 = e.2 := ⟨e,he,rfl⟩
 rw [dif_pos h]
 obtain ⟨hg,hg2⟩ := Classical.choose_spec h
 rw [share hdisj hg he e.2 (Or.inr hg2.symm) (Or.inr rfl)]
include hlt in
lemma n7 {i : Fin k} (hi : ¬ Free pos i) : partner pos (partner pos i) = i := by
 obtain ⟨e,he,h | h⟩ := jZ hi <;> rw [h]
 · rw [iV hdisj he,i9 hlt hdisj he]
 · rw [i9 hlt hdisj he,iV hdisj he]
include hlt in
lemma oV {i : Fin k} (hi : ¬ Free pos i) : ¬ Free pos (partner pos i) := by
 obtain ⟨e,he,h | h⟩ := jZ hi <;> rw [h] <;> intro hf
 · rw [iV hdisj he] at hf
   exact (hf e he).2 rfl
 · rw [i9 hlt hdisj he] at hf
   exact (hf e he).1 rfl
end Consistent
noncomputable def pX (σ : Equiv.Perm (Fin k)) (i : Fin k) : Fin k :=
 if Free pos i then σ i else partner pos i
noncomputable def zQ (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin k) :=
 if h : ∀ i,pX (pos := pos) σ (pX (pos := pos) σ i) = i
 then Function.Involutive.toPerm _ h else 1
lemma jU {σ : Equiv.Perm (Fin k)} (h : ∀ i,pX (pos := pos) σ (pX (pos := pos) σ i) = i)
   (i : Fin k) : zQ (pos := pos) σ i = pX (pos := pos) σ i := by
 unfold zQ; rw [dif_pos h]; rfl
end zU
section wB
def al {n : ℕ} (e : Fin n × Fin n) : Finset (Fin n) := {e.1,e.2}
def ae (k : ℕ) : List (Fin k × Fin k) :=
 (List.finRange k).flatMap (fun i =>
   ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
def IsMatching (n : ℕ) (M : Finset (Fin n × Fin n)) : Prop :=
 (∀ e ∈ M,e.1 < e.2) /\ ∀ e ∈ M,∀ g ∈ M,e ≠ g -> Disjoint (al e) (al g)
lemma eJ {k : ℕ} (e : Fin k × Fin k) : e ∈ ae k ↔ e.1 < e.2 := by
 simp only [ae,List.mem_flatMap,List.mem_finRange,List.mem_map,List.mem_filter,
   decide_eq_true_eq,true_and]
 constructor
 · rintro ⟨i,j,hij,rfl⟩; exact hij
 · intro h; exact ⟨e.1,e.2,h,Prod.ext rfl rfl⟩
lemma jW (k : ℕ) : (ae k).Nodup := by
 rw [ae,List.nodup_flatMap]
 refine ⟨?_,?_⟩
 · intro i _
   apply List.Nodup.map (fun a b h => (Prod.ext_iff.mp h).2)
   exact (List.nodup_finRange k).filter _
 · exact (List.nodup_finRange k).imp fun {i j} hij => by
     intro e he1 he2
     simp only [List.mem_map,List.mem_filter,List.mem_finRange,true_and] at he1 he2
     rcases he1 with ⟨a,_,ha⟩
     rcases he2 with ⟨b,_,hb⟩
     apply hij
     have h1 : i = e.1 := congrArg Prod.fst ha
     have h2 : j = e.1 := congrArg Prod.fst hb
     exact h1.trans h2.symm
lemma dZ (k : ℕ) : 2 * (ae k).length = k * (k - 1) := by
 have h1 : (ae k).toFinset = Finset.univ.filter (fun e : Fin k × Fin k => e.1 < e.2) := by
   ext e; simp [eJ]
 rw [← List.toFinset_card_of_nodup (jW k),h1]
 have hdisj : Disjoint (Finset.univ.filter (fun e : Fin k × Fin k => e.1 < e.2))
     (Finset.univ.filter (fun e : Fin k × Fin k => e.2 < e.1)) := by
   rw [Finset.disjoint_left]
   intro e h1 h2
   simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h1 h2
   exact lt_asymm h1 h2
 have hswap : (Finset.univ.filter (fun e : Fin k × Fin k => e.2 < e.1)).card =
     (Finset.univ.filter (fun e : Fin k × Fin k => e.1 < e.2)).card := by
   apply Finset.card_nbij' (fun e => (e.2,e.1)) (fun e => (e.2,e.1))
   · intro e he; simp_all
   · intro e he; simp_all
   · intro e _; ext <;> rfl
   · intro e _; ext <;> rfl
 have hall : (Finset.univ.filter (fun e : Fin k × Fin k => e.1 < e.2)) ∪
     (Finset.univ.filter (fun e : Fin k × Fin k => e.2 < e.1)) =
     Finset.univ.filter (fun e : Fin k × Fin k => e.1 ≠ e.2) := by
   ext e
   simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,ne_eq]
   exact ⟨fun h => h.elim ne_of_lt ne_of_gt,lt_or_gt_of_ne⟩
 have hdiag : (Finset.univ.filter (fun e : Fin k × Fin k => e.1 = e.2)).card = k := by
   have : Finset.univ.filter (fun e : Fin k × Fin k => e.1 = e.2) =
       Finset.univ.image (fun i : Fin k => (i,i)) := by
     ext e
     simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
     exact ⟨fun h => ⟨e.1,Prod.ext rfl h⟩,fun ⟨i,hi⟩ => by rw [← hi]⟩
   rw [this,Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1),
     Finset.card_univ,Fintype.card_fin]
 have sB : Disjoint (Finset.univ.filter (fun e : Fin k × Fin k => e.1 ≠ e.2))
     (Finset.univ.filter (fun e : Fin k × Fin k => e.1 = e.2)) := by
   rw [Finset.disjoint_left]
   intro e h1 h2
   simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h1 h2
   exact h1 h2
 have vd : (Finset.univ.filter (fun e : Fin k × Fin k => e.1 ≠ e.2)) ∪
     (Finset.univ.filter (fun e : Fin k × Fin k => e.1 = e.2)) = Finset.univ := by
   ext e
   simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
   exact em' _
 have hne : (Finset.univ.filter (fun e : Fin k × Fin k => e.1 ≠ e.2)).card + k = k * k := by
   have hc : (Finset.univ.filter (fun e : Fin k × Fin k => e.1 ≠ e.2)).card +
       (Finset.univ.filter (fun e : Fin k × Fin k => e.1 = e.2)).card = k * k := by
     rw [← Finset.card_union_of_disjoint sB,vd]
     simp [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
   rwa [hdiag] at hc
 have w4 : (Finset.univ.filter (fun e : Fin k × Fin k => e.1 ≠ e.2)).card = k * (k - 1) := by
   cases k with
   | zero => simp at hne ⊢
   | succ k' =>
     simp only [Nat.add_sub_cancel]
     have hk1 : (k' + 1) * (k' + 1) = (k' + 1) * k' + (k' + 1) := by ring
     omega
 rw [← w4,← hall,Finset.card_union_of_disjoint hdisj,hswap]
 ring
lemma jX {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M) :
   ∀ i : Fin n,pX (pos := M) (1 : Equiv.Perm (Fin n)) (pX (pos := M) (1 : Equiv.Perm (Fin n)) i) = i := by
 intro i
 unfold pX
 have hlt : ∀ e ∈ M ∪ (∅ : Finset (Fin n × Fin n)),e.1 < e.2 := by
   intro e he; simp only [Finset.union_empty] at he; exact hM.1 e he
 by_cases hi : Free M i
 · have hstep : (if Free M i then (1 : Equiv.Perm (Fin n)) i else partner M i) = i := by
     rw [if_pos hi]; rfl
   rw [hstep,hstep]
 · rw [if_neg hi,if_neg (oV (neg := ∅) hlt hM.2 hi),n7 (neg := ∅) hlt hM.2 hi]
noncomputable def aP {n : ℕ} (M : Finset (Fin n × Fin n)) : Equiv.Perm (Fin n) :=
 zQ (pos := M) (1 : Equiv.Perm (Fin n))
lemma bQ {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M) :
   ∀ i : Fin n,aP M (aP M i) = i := by
 have ht := jX hM
 intro i
 rw [aP,jU ht,jU ht]
 exact ht i
lemma cW {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M)
   {e : Fin n × Fin n} (he : e ∈ M) :
   aP M e.1 = e.2 /\ aP M e.2 = e.1 := by
 have ht := jX hM
 have hlt : ∀ g ∈ M ∪ (∅ : Finset (Fin n × Fin n)),g.1 < g.2 := by
   intro g hg; simp only [Finset.union_empty] at hg; exact hM.1 g hg
 have h1 : ¬ Free M e.1 := fun hf => (hf e he).1 rfl
 have h2 : ¬ Free M e.2 := fun hf => (hf e he).2 rfl
 rw [aP,jU ht,jU ht]
 simp only [pX,h1,h2,↓reduceIte]
 exact ⟨iV hM.2 he,i9 (neg := ∅) hlt hM.2 he⟩
lemma iq {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M)
   {i : Fin n} (hi : Free M i) : aP M i = i := by
 have ht := jX hM
 rw [aP,jU ht]
 dsimp only [pX]
 rw [if_pos hi]
 rfl
lemma bo {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M) :
   aQ (aP M) = M := by
 ext e
 simp only [aQ,Finset.mem_filter,Finset.mem_univ,true_and]
 constructor
 · rintro ⟨hlt,hpe⟩
   by_cases hf : Free M e.1
   · rw [iq hM hf] at hpe
     exact absurd hpe hlt.ne
   · obtain ⟨g,hg,h1 | h2⟩ := jZ hf
     · have hm1 := (cW hM hg).1
       rw [h1,hm1] at hpe
       have heq : e = g := Prod.ext h1 hpe.symm
       rwa [heq]
     · have hm2 := (cW hM hg).2
       rw [h2,hm2] at hpe
       have hgl := hM.1 g hg
       rw [hpe,← h2] at hgl
       exact absurd hlt (lt_asymm hgl)
 · intro he
   exact ⟨hM.1 e he,(cW hM he).1⟩
lemma eh {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : ∀ i,p (p i) = i) :
   IsMatching n (aQ p) := by
 constructor
 · intro e he
   exact (Finset.mem_filter.mp he).2.1
 · intro e he g hg hne
   have he' := (Finset.mem_filter.mp he).2
   have hg' := (Finset.mem_filter.mp hg).2
   have he2 : p e.2 = e.1 := by rw [← he'.2,hp]
   have hg2 : p g.2 = g.1 := by rw [← hg'.2,hp]
   rw [Finset.disjoint_left]
   intro v hv1 hv2
   simp only [al,Finset.mem_insert,Finset.mem_singleton] at hv1 hv2
   apply hne
   rcases hv1 with rfl | rfl <;> rcases hv2 with hv | hv
   · exact Prod.ext hv (by rw [← he'.2,← hg'.2,hv])
   · exfalso
     have h : e.2 = g.1 := by rw [← he'.2,hv,hg2]
     rw [hv,h] at he'
     exact lt_asymm he'.1 hg'.1
   · exfalso
     have h : e.1 = g.2 := by rw [← he2,hv,hg'.2]
     rw [hv,h] at he'
     exact lt_asymm he'.1 hg'.1
   · exact Prod.ext (by rw [← he2,← hg2,hv]) hv
lemma gz {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : ∀ i,p (p i) = i) :
   aP (aQ p) = p := by
 have hm := eh p hp
 apply Equiv.ext
 intro i
 by_cases hi : p i = i
 · have hf : Free (aQ p) i := by
     intro e he
     have he' := (Finset.mem_filter.mp he).2
     constructor
     · intro h; subst h; rw [hi] at he'; exact he'.1.ne he'.2
     · intro h; subst h
       have : p e.2 = e.1 := by rw [← he'.2,hp]
       rw [hi] at this; exact he'.1.ne this.symm
   rw [iq hm hf,hi]
 · rcases lt_or_gt_of_ne hi with hgt | hlt
   · have he : (p i,i) ∈ aQ p := by simp [aQ,hgt,hp i]
     exact (cW hm he).2
   · have he : (i,p i) ∈ aQ p := by simp [aQ,hlt]
     exact (cW hm he).1
noncomputable def ak {n : ℕ} (M : Finset (Fin n × Fin n)) :
   (Fin n -> Bool) -> (Fin n -> Bool) -> Bool :=
 form (aP M)
lemma cO {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : ∀ i,p (p i) = i)
   (R T : Finset (Fin n)) :
   form p (fun i => decide (i ∈ R)) (fun j => decide (j ∈ T)) = false ↔
     Disjoint R T /\ ∀ e ∈ aQ p,¬(al e ⊆ R) /\ ¬(al e ⊆ T) := by
 rw [← Bool.not_eq_true]
 unfold form
 simp only [decide_eq_true_eq,not_exists,not_or,not_and,not_not]
 constructor
 · intro h
   refine ⟨Finset.disjoint_left.mpr fun i wI hiT => (h i).1 wI hiT,fun e he => ?_⟩
   have he' := (Finset.mem_filter.mp he).2
   have hne : p e.1 ≠ e.1 := by rw [he'.2]; exact he'.1.ne'
   have h2 := (h e.1).2 hne
   rw [he'.2] at h2
   simp only [al,Finset.insert_subset_iff,Finset.singleton_subset_iff,not_and]
   exact ⟨fun h1 h2' => h2.1 h1 h2',fun h1 h2' => h2.2 h1 h2'⟩
 · rintro ⟨hdisj,hall⟩ i
   refine ⟨fun wI hiT => Finset.disjoint_left.mp hdisj wI hiT,fun hpi => ?_⟩
   rcases lt_or_gt_of_ne hpi with hlt | hgt
   · have he : (p i,i) ∈ aQ p := by
       simp only [aQ,Finset.mem_filter,Finset.mem_univ,true_and]
       exact ⟨hlt,hp i⟩
     have ha := hall (p i,i) he
     simp only [al,Finset.insert_subset_iff,Finset.singleton_subset_iff,not_and] at ha
     exact ⟨fun h1 h2 => ha.1 h2 h1,fun h1 h2 => ha.2 h2 h1⟩
   · have he : (i,p i) ∈ aQ p := by simp [aQ,hgt]
     have ha := hall (i,p i) he
     simp only [al,Finset.insert_subset_iff,Finset.singleton_subset_iff,not_and] at ha
     exact ha
lemma bK {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M)
   (R T : Finset (Fin n)) :
   ak M (fun i => decide (i ∈ R)) (fun j => decide (j ∈ T)) = false ↔
     Disjoint R T /\ ∀ e ∈ M,¬(al e ⊆ R) /\ ¬(al e ⊆ T) := by
 unfold ak
 rw [cO _ (bQ hM) R T,bo hM]
lemma ku {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M)
   {e : Fin n × Fin n} (he : e.1 < e.2) :
   ak M (fun i => decide (i ∈ al e)) (fun _ => false) = decide (e ∈ M) := by
 unfold ak
 have h0 : (fun _ : Fin n => false) = (fun j => decide (j ∈ (∅ : Finset (Fin n)))) := by
   funext _; simp
 by_cases xW : e ∈ M
 · rw [decide_eq_true xW]
   by_contra hf
   have hff := Bool.eq_false_iff.mpr hf
   rw [h0,cO _ (bQ hM),bo hM] at hff
   exact (hff.2 e xW).1 (Finset.Subset.refl _)
 · rw [decide_eq_false xW]
   rw [h0,cO _ (bQ hM),bo hM]
   refine ⟨Finset.disjoint_empty_right _,fun g hg => ⟨fun hsub => ?_,fun hsub => ?_⟩⟩
   · have hge := hM.1 g hg
     have h1 := hsub (Finset.mem_insert_self g.1 {g.2})
     have h2 := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self g.2))
     simp only [al,Finset.mem_insert,Finset.mem_singleton] at h1 h2
     apply xW
     rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
     · exact absurd (h1.trans h2.symm) hge.ne
     · have heq : e = g := Prod.ext h1.symm h2.symm; rwa [heq]
     · exfalso; rw [h1,h2] at hge; exact lt_asymm hge he
     · exact absurd (h1.trans h2.symm) hge.ne
   · have h1 := hsub (Finset.mem_insert_self g.1 {g.2})
     simp at h1
lemma gw {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M) :
   (ae n).map (fun e => ak M (fun i => decide (i ∈ al e)) (fun _ => false)) =
     (ae n).map (fun e => decide (e ∈ M)) := by
 apply List.map_congr_left
 intro e he
 exact ku hM ((eJ e).mp he)
lemma fZ {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M) :
   (((ae n).map (fun e => decide (e ∈ M))).filter id).length = M.card /\ M.card ≤ n / 2 := by
 have hf : (((ae n).map (fun e => decide (e ∈ M))).filter id).length =
     ((ae n).filter (fun e => decide (e ∈ M))).length := by
   induction ae n with
   | nil => rfl
   | cons a l ih =>
     by_cases ha : a ∈ M <;> simp [ha,ih]
 rw [hf]
 have hto : ((ae n).filter (fun e => decide (e ∈ M))).toFinset = M := by
   ext e
   simp only [List.mem_toFinset,List.mem_filter,eJ,decide_eq_true_eq]
   exact ⟨fun h => h.2,fun h => ⟨hM.1 e h,h⟩⟩
 have hc : ((ae n).filter (fun e => decide (e ∈ M))).length = M.card := by
   rw [← List.toFinset_card_of_nodup ((jW n).filter _),hto]
 refine ⟨hc,?_⟩
 rw [← bo hM]
 exact pY _ (bQ hM)
lemma iO {n : ℕ} (hn : 2 ≤ n)
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (f : (Fin n -> Bool) -> (Fin n -> Bool) -> Bool) :
   let E := (ae n).toFinset.filter (fun e =>
     ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2))
   let valid := (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
     PEqualNP.MetaComplexity.Monotone2 C /\ C.size + 1 ≤ 2 * n /\
     PEqualNP.Represents.Represents (fun i j : Fin n => decide (i = j)) C /\
     ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) /\
     ∀ z ∈ hard,f (fun i => decide (i ∈ z.1)) (fun j => decide (j ∈ z.2)) = false
   valid ↔ (∀ z ∈ hard,Disjoint z.1 z.2) /\
     ∃ M : Finset (Fin n × Fin n),IsMatching n M /\ M ⊆ E /\ f = ak M := by
 intro E valid
 constructor
 · rintro ⟨hcirc,hhard⟩
   obtain ⟨p,hp,rfl⟩ := (sl hn f).mp hcirc
   have hm := eh p hp
   have hdisj : ∀ z ∈ hard,Disjoint z.1 z.2 := fun z hz =>
     ((cO p hp z.1 z.2).mp (hhard z hz)).1
   have hsub : aQ p ⊆ E := by
     intro e he
     simp only [E,Finset.mem_filter,List.mem_toFinset,eJ]
     refine ⟨hm.1 e he,fun z hz => ?_⟩
     exact ((cO p hp z.1 z.2).mp (hhard z hz)).2 e he
   refine ⟨hdisj,aQ p,hm,hsub,?_⟩
   simp [ak,gz p hp]
 · rintro ⟨hdisj,M,hM,hsub,rfl⟩
   refine ⟨(sl hn (ak M)).mpr ⟨aP M,bQ hM,rfl⟩,
     fun z hz => ?_⟩
   rw [bK hM z.1 z.2]
   refine ⟨hdisj z hz,fun e he => ?_⟩
   have Ax := hsub he
   simp only [E,Finset.mem_filter,List.mem_toFinset] at Ax
   exact Ax.2 z hz
lemma jg {α : Type*} [DecidableEq α] (B : Finset α) :
   ∑ S ∈ B.powerset,(-1 : ℤ) ^ S.card = if B = ∅ then 1 else 0 := by
 by_cases hB : B = ∅
 · subst hB; simp
 · rw [if_neg hB]
   obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hB
   refine Finset.sum_involution (fun S _ => if a ∈ S then S.erase a else insert a S) ?_ ?_ ?_ ?_
   · intro S _
     by_cases haS : a ∈ S
     · rw [if_pos haS,Finset.card_erase_of_mem haS]
       have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨a,haS⟩
       have heq : (S.card - 1) + 1 = S.card := by omega
       have hp : (-1 : ℤ) ^ S.card = - (-1 : ℤ) ^ (S.card - 1) := by
         conv_lhs => rw [← heq,pow_succ]
         ring
       rw [hp]
       ring
     · rw [if_neg haS,Finset.card_insert_of_notMem haS,pow_succ]
       ring
   · intro S _ _
     by_cases haS : a ∈ S
     · rw [if_pos haS]
       intro h
       have := congrArg (a ∈ ·) h
       simp [haS] at this
     · rw [if_neg haS]
       intro h
       have := congrArg (a ∈ ·) h
       simp [haS] at this
   · intro S hS
     rw [Finset.mem_powerset] at hS ⊢
     by_cases haS : a ∈ S
     · rw [if_pos haS]; exact (Finset.erase_subset _ _).trans hS
     · rw [if_neg haS]; exact Finset.insert_subset ha hS
   · intro S _
     by_cases haS : a ∈ S
     · rw [if_pos haS,if_neg (Finset.notMem_erase a S),Finset.insert_erase haS]
     · rw [if_neg haS,if_pos (Finset.mem_insert_self a S),Finset.erase_insert haS]
lemma kt {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching n M)
   (t : (Finset (Fin n) × Finset (Fin n)) × Bool) :
   (if ak M (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = false
     then (1 : ℤ) else 0) =
   ∑ S ∈ M.powerset,(-1 : ℤ) ^ S.card *
     (if Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2 then 1 else 0) := by
 classical
 by_cases hd : Disjoint t.1.1 t.1.2
 · let B := M.filter (fun e => al e ⊆ t.1.1 \/ al e ⊆ t.1.2)
   have hsplit : ∀ S ∈ M.powerset,
       (-1 : ℤ) ^ S.card * (if Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2 then 1 else 0) =
       if S ∈ B.powerset then (-1 : ℤ) ^ S.card else 0 := by
     intro S hS
     rw [Finset.mem_powerset] at hS
     by_cases hsub : ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2
     · have hSB : S ∈ B.powerset := by
         rw [Finset.mem_powerset]
         intro e he
         exact Finset.mem_filter.mpr ⟨hS he,hsub e he⟩
       rw [if_pos ⟨hd,hsub⟩,if_pos hSB,mul_one]
     · have hSB : S ∉ B.powerset := by
         rw [Finset.mem_powerset]
         intro h1
         apply hsub
         intro e he
         exact (Finset.mem_filter.mp (h1 he)).2
       rw [if_neg (fun h => hsub h.2),if_neg hSB,mul_zero]
   rw [Finset.sum_congr rfl hsplit,← Finset.sum_filter]
   have oY : M.powerset.filter (· ∈ B.powerset) = B.powerset := by
     ext S
     simp only [Finset.mem_filter,Finset.mem_powerset,and_iff_right_iff_imp]
     intro hSB e he
     exact (Finset.mem_filter.mp (hSB he)).1
   rw [oY,jg B]
   have hB : ak M (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = false ↔ B = ∅ := by
     rw [bK hM]
     simp only [hd,true_and,Finset.eq_empty_iff_forall_notMem,B,Finset.mem_filter,not_and,
       not_or]
   by_cases hf : ak M (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = false
   · rw [if_pos hf,if_pos (hB.mp hf)]
   · rw [if_neg hf,if_neg (fun hbe => hf (hB.mpr hbe))]
 · have hf : ak M (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) ≠ false := by
     intro h
     exact hd ((bK hM _ _).mp h).1
   simp [hf,hd]
lemma cu {α : Type*} (L : List α) (p : α -> Bool) :
   ((L.filter p).length : ℤ) = (L.map (fun x => if p x then (1 : ℤ) else 0)).sum := by
 induction L with
 | nil => rfl
 | cons a L ih =>
   by_cases ha : p a = true
   · simp [ha,ih]; omega
   · have haf : p a = false := Bool.eq_false_iff.mpr ha
     simp [haf,ih]
lemma nE {α : Type*} (L : List α) (f g : α -> ℤ) :
   (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.map_cons,List.sum_cons,ih]
   ring
lemma lF {α β : Type*} (L : List α) (S : Finset β) (f : α -> β -> ℤ) :
   (L.map (fun a => ∑ b ∈ S,f a b)).sum = ∑ b ∈ S,(L.map (fun a => f a b)).sum := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.map_cons,List.sum_cons,ih,← Finset.sum_add_distrib]
lemma im {n : ℕ}
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (nO : ∀ S ⊆ (ae n).toFinset.filter (fun e => ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2)),
     2 ≤ S.card -> (∀ e ∈ S,∀ g ∈ S,e ≠ g -> Disjoint (al e) (al g)) ->
     (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length =
       (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length) :
   let E := (ae n).toFinset.filter (fun e => ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2))
   let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
     Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2
   let ct := fun S => (soft.filter (fun t => t.2 && decide (lists S t))).length
   let bY := fun S => (soft.filter (fun t => !t.2 && decide (lists S t))).length
   let iW := fun (M : Finset (Fin n × Fin n)) =>
     (soft.filter (fun t => decide (ak M (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length
   let base := iW ∅
   let oc := fun (e : Fin n × Fin n) => (soft.length + 1) + ct {e} - bY {e}
   (∀ e,1 ≤ oc e /\ oc e ≤ 2 * soft.length + 1) /\
   (base ≤ soft.length) /\
   ∀ M : Finset (Fin n × Fin n),IsMatching n M -> M ⊆ E ->
     (soft.length + 1) * M.card + iW M = base + ∑ e ∈ M,oc e := by
 classical
 intro E lists ct bY iW base oc
 have zN : ∀ e,1 ≤ oc e /\ oc e ≤ 2 * soft.length + 1 := by
   intro e
   have hp : ct {e} ≤ soft.length := List.length_filter_le _ _
   have hn : bY {e} ≤ soft.length := List.length_filter_le _ _
   dsimp only [oc]
   omega
 have hbase : base ≤ soft.length := List.length_filter_le _ _
 refine ⟨zN,hbase,fun M hM zn => ?_⟩
 let oj := (soft.filter (fun t => t.2)).length
 have qk : ∀ N : Finset (Fin n × Fin n),IsMatching n N -> N ⊆ E ->
     (iW N : ℤ) = (oj : ℤ) + (bY ∅ : ℤ) - (ct ∅ : ℤ) +
       ∑ e ∈ N,((ct {e} : ℤ) - (bY {e} : ℤ)) := by
   intro N hN AZ
   let vX := fun (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
     ak N (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2))
   have hitem : ∀ t : (Finset (Fin n) × Finset (Fin n)) × Bool,
       (if decide (vX t = t.2) then (1 : ℤ) else 0) =
         (if t.2 then (1 : ℤ) else 0) +
         (if !t.2 then (1 : ℤ) else -1) * (if vX t = false then (1 : ℤ) else 0) := by
     intro t
     cases ht : t.2 <;> cases ho : vX t <;> simp
   have hstep1 : (iW N : ℤ) =
       (oj : ℤ) + (soft.map (fun t =>
         ∑ S ∈ N.powerset,(if !t.2 then (1 : ℤ) else -1) * ((-1 : ℤ) ^ S.card *
           (if lists S t then 1 else 0)))).sum := by
     dsimp only [iW,oj]
     rw [cu,cu]
     have hmap : (soft.map (fun t => if decide (vX t = t.2) then (1 : ℤ) else 0)) =
         soft.map (fun t => (if t.2 then (1 : ℤ) else 0) +
           ∑ S ∈ N.powerset,(if !t.2 then (1 : ℤ) else -1) * ((-1 : ℤ) ^ S.card *
             (if lists S t then 1 else 0))) := by
       apply List.map_congr_left
       intro t _
       rw [hitem t,kt hN t,Finset.mul_sum]
     rw [hmap,nE]
   rw [hstep1,lF]
   have hS : ∀ S ∈ N.powerset,
       (soft.map (fun t => (if !t.2 then (1 : ℤ) else -1) * ((-1 : ℤ) ^ S.card *
         (if lists S t then 1 else 0)))).sum =
       (-1 : ℤ) ^ S.card * ((bY S : ℤ) - (ct S : ℤ)) := by
     intro S _
     dsimp only [bY,ct]
     rw [cu,cu]
     have hgen : ∀ L : List ((Finset (Fin n) × Finset (Fin n)) × Bool),
         (L.map (fun t => (if !t.2 then (1 : ℤ) else -1) * ((-1 : ℤ) ^ S.card *
           (if lists S t then 1 else 0)))).sum =
         (-1 : ℤ) ^ S.card *
           ((L.map (fun x => if !x.2 && decide (lists S x) then (1 : ℤ) else 0)).sum -
            (L.map (fun x => if x.2 && decide (lists S x) then (1 : ℤ) else 0)).sum) := by
       intro L
       induction L with
       | nil => simp
       | cons a l ih =>
         simp only [List.map_cons,List.sum_cons,ih]
         by_cases hl : lists S a <;> cases ha : a.2 <;> simp [hl,ha] <;> ring
     exact hgen soft
   rw [Finset.sum_congr rfl hS]
   have hsplit : N.powerset = {∅} ∪ N.powerset.filter (fun S => S.card = 1) ∪
       N.powerset.filter (fun S => 2 ≤ S.card) := by
     ext S
     simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_filter,Finset.mem_powerset]
     constructor
     · intro zo
       by_cases h0 : S.card = 0
       · left; left; exact Finset.card_eq_zero.mp h0
       · by_cases h1 : S.card = 1
         · left; right; exact ⟨zo,h1⟩
         · right; exact ⟨zo,by omega⟩
     · rintro ((rfl | ⟨h,_⟩) | ⟨h,_⟩)
       · exact Finset.empty_subset _
       · exact h
       · exact h
   have hd1 : Disjoint {∅} (N.powerset.filter (fun S => S.card = 1)) := by
     rw [Finset.disjoint_left]
     intro S h1 h2
     rw [Finset.mem_singleton] at h1
     subst h1
     simp at h2
   have hd2 : Disjoint ({∅} ∪ N.powerset.filter (fun S => S.card = 1))
       (N.powerset.filter (fun S => 2 ≤ S.card)) := by
     rw [Finset.disjoint_left]
     intro S h1 h2
     rw [Finset.mem_filter] at h2
     rw [Finset.mem_union,Finset.mem_singleton] at h1
     rcases h1 with rfl | h1
     · simp at h2
     · rw [Finset.mem_filter] at h1; omega
   rw [hsplit,Finset.sum_union hd2,Finset.sum_union hd1,Finset.sum_singleton]
   have hzero : ∑ S ∈ N.powerset.filter (fun S => 2 ≤ S.card),
       (-1 : ℤ) ^ S.card * ((bY S : ℤ) - (ct S : ℤ)) = 0 := by
     apply Finset.sum_eq_zero
     intro S hS
     rw [Finset.mem_filter,Finset.mem_powerset] at hS
     have AR : S ⊆ E := hS.1.trans AZ
     have hdisj : ∀ e ∈ S,∀ g ∈ S,e ≠ g -> Disjoint (al e) (al g) :=
       fun e he g hg hne => hN.2 e (hS.1 he) g (hS.1 hg) hne
     have heq := nO S AR hS.2 hdisj
     dsimp only [ct,bY] at *
     rw [heq]
     ring
   have hones : ∑ S ∈ N.powerset.filter (fun S => S.card = 1),
       (-1 : ℤ) ^ S.card * ((bY S : ℤ) - (ct S : ℤ)) =
       ∑ e ∈ N,((ct {e} : ℤ) - (bY {e} : ℤ)) := by
     have himg : N.powerset.filter (fun S => S.card = 1) = N.image (fun e => ({e} : Finset (Fin n × Fin n))) := by
       ext S
       simp only [Finset.mem_filter,Finset.mem_powerset,Finset.mem_image,Finset.card_eq_one]
       constructor
       · rintro ⟨zo,⟨e,rfl⟩⟩
         exact ⟨e,zo (Finset.mem_singleton_self e),rfl⟩
       · rintro ⟨e,heN,rfl⟩
         exact ⟨Finset.singleton_subset_iff.mpr heN,⟨e,rfl⟩⟩
     rw [himg,Finset.sum_image (fun a _ b _ hab => Finset.singleton_injective hab)]
     apply Finset.sum_congr rfl
     intro e _
     simp only [Finset.card_singleton,pow_one]
     ring
   rw [hzero,add_zero,hones]
   simp only [Finset.card_empty,pow_zero,one_mul]
   ring
 have hM0 : IsMatching n ∅ := ⟨fun _ h => by simp at h,fun _ h => by simp at h⟩
 have h0 := qk ∅ hM0 (Finset.empty_subset _)
 simp only [Finset.sum_empty,add_zero] at h0
 have hM' := qk M hM zn
 have uC : (base : ℤ) = (oj : ℤ) + (bY ∅ : ℤ) - (ct ∅ : ℤ) := h0
 have zD : (iW M : ℤ) = (base : ℤ) + ∑ e ∈ M,((ct {e} : ℤ) - (bY {e} : ℤ)) := by
   rw [uC]; exact hM'
 have yG : ∀ e ∈ M,(oc e : ℤ) = (soft.length + 1 : ℤ) + (ct {e} : ℤ) - (bY {e} : ℤ) := by
   intro e _
   have hn : bY {e} ≤ soft.length := List.length_filter_le _ _
   dsimp only [oc]
   omega
 have hz : ((soft.length + 1) * M.card + iW M : ℤ) =
     (base : ℤ) + ∑ e ∈ M,(oc e : ℤ) := by
   push_cast
   rw [zD,Finset.sum_congr rfl yG]
   have xy : ∑ e ∈ M,((soft.length : ℤ) + 1 + (ct {e} : ℤ) - (bY {e} : ℤ)) =
       (M.card : ℤ) * ((soft.length : ℤ) + 1) + ∑ e ∈ M,((ct {e} : ℤ) - (bY {e} : ℤ)) := by
     have : ∀ e : Fin n × Fin n,((soft.length : ℤ) + 1 + (ct {e} : ℤ) - (bY {e} : ℤ)) =
         ((soft.length : ℤ) + 1) + ((ct {e} : ℤ) - (bY {e} : ℤ)) := fun _ => by ring
     simp_rw [this,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]; ring
   rw [xy]
   ring
 exact_mod_cast hz
end wB
section Prob
def ap {P U : ℕ} (u : Fin P -> Fin U) (S : Finset (Fin P)) : ℕ :=
 ∑ i ∈ S,(u i).val
def dS {P U : ℕ} (F : Finset (Finset (Fin P))) (u : Fin P -> Fin U) : Prop :=
 ∃ S ∈ F,∀ T ∈ F,T ≠ S -> ap u S < ap u T
lemma pV {P U : ℕ} (F : Finset (Finset (Fin P))) (hF : F.Nonempty)
   (u : Fin P -> Fin U) :
   ¬ dS F u ↔
     ∃ i : Fin P,∃ (hf1 : (F.filter (fun S => i ∈ S)).Nonempty)
       (hf0 : (F.filter (fun S => i ∉ S)).Nonempty),
       (F.filter (fun S => i ∈ S)).inf' hf1 (ap u) =
         (F.filter (fun S => i ∉ S)).inf' hf0 (ap u) := by
 classical
 constructor
 · intro hnu
   obtain ⟨S1,hS1,hmin1⟩ := Finset.exists_min_image F (ap u) hF
   have hnot : ¬ ∀ T ∈ F,T ≠ S1 -> ap u S1 < ap u T := fun h => hnu ⟨S1,hS1,h⟩
   push Not at hnot
   obtain ⟨S2,hS2,hne,hle⟩ := hnot
   have heq : ap u S1 = ap u S2 := le_antisymm (hmin1 S2 hS2) hle
   have hsym : ∃ i : Fin P,(i ∈ S1 /\ i ∉ S2) \/ (i ∈ S2 /\ i ∉ S1) := by
     by_contra hnone
     push Not at hnone
     apply hne
     ext i
     have h1 := (hnone i).1
     have h2 := (hnone i).2
     tauto
   obtain ⟨i,hi1 | hi2⟩ := hsym
   · have hf1 : (F.filter (fun S => i ∈ S)).Nonempty := ⟨S1,Finset.mem_filter.mpr ⟨hS1,hi1.1⟩⟩
     have hf0 : (F.filter (fun S => i ∉ S)).Nonempty := ⟨S2,Finset.mem_filter.mpr ⟨hS2,hi1.2⟩⟩
     refine ⟨i,hf1,hf0,?_⟩
     have hm1 : (F.filter (fun S => i ∈ S)).inf' hf1 (ap u) = ap u S1 := by
       apply le_antisymm
       · exact Finset.inf'_le (ap u) (Finset.mem_filter.mpr ⟨hS1,hi1.1⟩)
       · exact (Finset.le_inf'_iff _ _).mpr fun T hT => hmin1 T (Finset.mem_filter.mp hT).1
     have hm0 : (F.filter (fun S => i ∉ S)).inf' hf0 (ap u) = ap u S2 := by
       apply le_antisymm
       · exact Finset.inf'_le (ap u) (Finset.mem_filter.mpr ⟨hS2,hi1.2⟩)
       · exact (Finset.le_inf'_iff _ _).mpr fun T hT =>
           le_trans heq.symm.le (hmin1 T (Finset.mem_filter.mp hT).1)
     rw [hm1,hm0,heq]
   · have hf1 : (F.filter (fun S => i ∈ S)).Nonempty := ⟨S2,Finset.mem_filter.mpr ⟨hS2,hi2.1⟩⟩
     have hf0 : (F.filter (fun S => i ∉ S)).Nonempty := ⟨S1,Finset.mem_filter.mpr ⟨hS1,hi2.2⟩⟩
     refine ⟨i,hf1,hf0,?_⟩
     have hm1 : (F.filter (fun S => i ∈ S)).inf' hf1 (ap u) = ap u S2 := by
       apply le_antisymm
       · exact Finset.inf'_le (ap u) (Finset.mem_filter.mpr ⟨hS2,hi2.1⟩)
       · exact (Finset.le_inf'_iff _ _).mpr fun T hT =>
           le_trans heq.symm.le (hmin1 T (Finset.mem_filter.mp hT).1)
     have hm0 : (F.filter (fun S => i ∉ S)).inf' hf0 (ap u) = ap u S1 := by
       apply le_antisymm
       · exact Finset.inf'_le (ap u) (Finset.mem_filter.mpr ⟨hS1,hi2.2⟩)
       · exact (Finset.le_inf'_iff _ _).mpr fun T hT => hmin1 T (Finset.mem_filter.mp hT).1
     rw [hm1,hm0,heq]
 · rintro ⟨i,hf1,hf0,heq⟩ ⟨S,hS,huniq⟩
   obtain ⟨S1,hS1,hm1⟩ := Finset.exists_min_image (F.filter (fun S => i ∈ S)) (ap u) hf1
   obtain ⟨S0,hS0,hm0⟩ := Finset.exists_min_image (F.filter (fun S => i ∉ S)) (ap u) hf0
   have tD : (F.filter (fun S => i ∈ S)).inf' hf1 (ap u) = ap u S1 :=
     le_antisymm (Finset.inf'_le _ hS1) ((Finset.le_inf'_iff _ _).mpr hm1)
   have ti : (F.filter (fun S => i ∉ S)).inf' hf0 (ap u) = ap u S0 :=
     le_antisymm (Finset.inf'_le _ hS0) ((Finset.le_inf'_iff _ _).mpr hm0)
   have xR : ap u S1 = ap u S0 := by rw [← tD,← ti,heq]
   have hne : S1 ≠ S0 := by
     intro h
     have hi1 := (Finset.mem_filter.mp hS1).2
     have hi0 := (Finset.mem_filter.mp hS0).2
     rw [h] at hi1
     exact hi0 hi1
   have Az := (Finset.mem_filter.mp hS1).1
   have Ar := (Finset.mem_filter.mp hS0).1
   by_cases hS1S : S1 = S
   · subst hS1S
     have hlt := huniq S0 Ar hne.symm
     omega
   · by_cases hS0S : S0 = S
     · subst hS0S
       have hlt := huniq S1 Az hne
       omega
     · by_cases hiS : i ∈ S
       · have hle := hm1 S (Finset.mem_filter.mpr ⟨hS,hiS⟩)
         have hlt := huniq S1 Az hS1S
         omega
       · have hle := hm0 S (Finset.mem_filter.mpr ⟨hS,hiS⟩)
         have hlt := huniq S0 Ar hS0S
         omega
lemma iQ {P U : ℕ} (u : Fin P -> Fin U) (i : Fin P) (S : Finset (Fin P)) :
   ap u S = (if i ∈ S then (u i).val else 0) + ∑ k ∈ S.erase i,(u k).val := by
 by_cases hi : i ∈ S
 · simp only [ap,hi,↓reduceIte]
   rw [← Finset.add_sum_erase S (fun k => (u k).val) hi]
 · simp only [ap,hi,↓reduceIte,zero_add,Finset.erase_eq_of_notMem hi]
lemma jh {P U : ℕ} (hP : 0 < P) (hU : 0 < U)
   (F : Finset (Finset (Fin P))) (i : Fin P)
   (hf1 : (F.filter (fun S => i ∈ S)).Nonempty)
   (hf0 : (F.filter (fun S => i ∉ S)).Nonempty) :
   ((Finset.univ : Finset (Fin P -> Fin U)).filter (fun u =>
     (F.filter (fun S => i ∈ S)).inf' hf1 (ap u) =
       (F.filter (fun S => i ∉ S)).inf' hf0 (ap u))).card ≤ U ^ (P - 1) := by
 classical
 let qC := {k : Fin P // k ≠ i}
 let e : (Fin P -> Fin U) ≃ Fin U × (qC -> Fin U) :=
   { toFun := fun u => (u i,fun k => u k.1)
     invFun := fun p k => if hk : k = i then p.1 else p.2 ⟨k,hk⟩
     left_inv := fun u => by
       funext k
       by_cases hk : k = i <;> simp [hk]
     right_inv := fun p => by
       apply Prod.ext
       · simp
       · funext k; simp [k.2] }
 let restWt (v : qC -> Fin U) (S : Finset (Fin P)) : ℕ :=
   ∑ k ∈ S.erase i,if hk : k = i then 0 else (v ⟨k,hk⟩).val
 have tN : ∀ (x : Fin U) (v : qC -> Fin U) (S : Finset (Fin P)),i ∈ S ->
     ap (e.symm (x,v)) S = x.val + restWt v S := by
   intro x v S hiS
   rw [iQ _ i S]
   simp only [hiS,↓reduceIte,e,Equiv.coe_fn_symm_mk,↓reduceDIte]
   congr 1
   apply Finset.sum_congr rfl
   intro k hk
   have hne := (Finset.mem_erase.mp hk).1
   simp [hne]
 have sY : ∀ (x : Fin U) (v : qC -> Fin U) (S : Finset (Fin P)),i ∉ S ->
     ap (e.symm (x,v)) S = restWt v S := by
   intro x v S hiS
   rw [iQ _ i S]
   simp only [hiS,↓reduceIte,zero_add]
   apply Finset.sum_congr rfl
   intro k hk
   have hne := (Finset.mem_erase.mp hk).1
   simp [e,hne]
 have tD : ∀ (x : Fin U) (v : qC -> Fin U),
     (F.filter (fun S => i ∈ S)).inf' hf1 (ap (e.symm (x,v))) =
       x.val + (F.filter (fun S => i ∈ S)).inf' hf1 (restWt v) := by
   intro x v
   obtain ⟨S1,hS1,hm1⟩ := Finset.exists_min_image (F.filter (fun S => i ∈ S)) (restWt v) hf1
   have hR : (F.filter (fun S => i ∈ S)).inf' hf1 (restWt v) = restWt v S1 :=
     le_antisymm (Finset.inf'_le _ hS1) ((Finset.le_inf'_iff _ _).mpr hm1)
   rw [hR]
   apply le_antisymm
   · rw [← tN x v S1 (Finset.mem_filter.mp hS1).2]
     exact Finset.inf'_le _ hS1
   · rw [Finset.le_inf'_iff]
     intro S hS
     rw [tN x v S (Finset.mem_filter.mp hS).2]
     exact Nat.add_le_add_left (hm1 S hS) _
 have ti : ∀ (x : Fin U) (v : qC -> Fin U),
     (F.filter (fun S => i ∉ S)).inf' hf0 (ap (e.symm (x,v))) =
       (F.filter (fun S => i ∉ S)).inf' hf0 (restWt v) := by
   intro x v
   apply Finset.inf'_congr hf0 rfl
   intro S hS
   exact sY x v S (Finset.mem_filter.mp hS).2
 let bad := (Finset.univ : Finset (Fin P -> Fin U)).filter (fun u =>
   (F.filter (fun S => i ∈ S)).inf' hf1 (ap u) =
     (F.filter (fun S => i ∉ S)).inf' hf0 (ap u))
 have hinj : Set.InjOn (fun u => (e u).2) (bad : Set (Fin P -> Fin U)) := by
   intro u1 hu1 u2 hu2 heq
   have h1 := (Finset.mem_filter.mp hu1).2
   have h2 := (Finset.mem_filter.mp hu2).2
   apply e.injective
   apply Prod.ext _ heq
   have zE : e.symm (e u1) = u1 := e.symm_apply_apply u1
   have z8 : e.symm (e u2) = u2 := e.symm_apply_apply u2
   rw [← zE,tD,ti] at h1
   rw [← z8,tD,ti] at h2
   dsimp only at h1 h2 heq
   rw [← heq] at h2
   exact Fin.ext (by omega)
 have hle : bad.card ≤ (Finset.univ : Finset (qC -> Fin U)).card :=
   Finset.card_le_card_of_injOn (fun u => (e u).2) (fun _ _ => Finset.mem_univ _) hinj
 refine hle.trans_eq ?_
 rw [Finset.card_univ,Fintype.card_fun,Fintype.card_fin]
 have hrc : Fintype.card qC = P - 1 := by
   simp only [qC,Fintype.card_subtype,Finset.filter_ne',
     Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
 rw [hrc]
lemma kA {P U : ℕ} (hP : 0 < P) (AH : 2 * P ≤ U)
   (F : Finset (Finset (Fin P))) (hF : F.Nonempty) :
   letI : DecidablePred (fun u : Fin P -> Fin U => ¬ dS F u) := Classical.decPred _
   2 * ((Finset.univ : Finset (Fin P -> Fin U)).filter (fun u => ¬ dS F u)).card ≤ U ^ P := by
 classical
 have hU : 0 < U := by omega
 let Bad := (Finset.univ : Finset (Fin P -> Fin U)).filter (fun u => ¬ dS F u)
 have hsub : Bad ⊆ Finset.univ.biUnion (fun i : Fin P =>
     if h : (F.filter (fun S => i ∈ S)).Nonempty /\ (F.filter (fun S => i ∉ S)).Nonempty then
       Finset.univ.filter (fun u =>
         (F.filter (fun S => i ∈ S)).inf' h.1 (ap u) =
           (F.filter (fun S => i ∉ S)).inf' h.2 (ap u))
     else ∅) := by
   intro u hu
   have hu' := (Finset.mem_filter.mp hu).2
   obtain ⟨i,hf1,hf0,heq⟩ := (pV F hF u).mp hu'
   rw [Finset.mem_biUnion]
   refine ⟨i,Finset.mem_univ i,?_⟩
   rw [dif_pos ⟨hf1,hf0⟩]
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,heq⟩
 have hc : Bad.card ≤ P * U ^ (P - 1) := by
   refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
   calc ∑ i : Fin P,(if h : (F.filter (fun S => i ∈ S)).Nonempty /\ (F.filter (fun S => i ∉ S)).Nonempty then
           Finset.univ.filter (fun u =>
             (F.filter (fun S => i ∈ S)).inf' h.1 (ap u) =
               (F.filter (fun S => i ∉ S)).inf' h.2 (ap u))
         else ∅).card
       ≤ ∑ _ : Fin P,U ^ (P - 1) := by
         apply Finset.sum_le_sum
         intro i _
         split_ifs with h
         · exact jh hP hU F i h.1 h.2
         · simp
     _ = P * U ^ (P - 1) := by simp [Finset.sum_const,Finset.card_univ]
 have hpow : U ^ P = U * U ^ (P - 1) := by
   conv_lhs => rw [show P = (P - 1) + 1 by omega,pow_succ,mul_comm]
 have hfin : 2 * Bad.card ≤ U ^ P := by
   calc 2 * Bad.card
       ≤ 2 * (P * U ^ (P - 1)) := Nat.mul_le_mul_left 2 hc
     _ = (2 * P) * U ^ (P - 1) := by ring
     _ ≤ U * U ^ (P - 1) := Nat.mul_le_mul_right _ AH
     _ = U ^ P := hpow.symm
 convert hfin
def az (b : ℕ) (bits : List Bool) (base : ℕ) : ℕ :=
 (List.range b).foldl (fun acc h => 2 * acc + if bits.getD (base + h) false then 1 else 0) 0
lemma bB (b : ℕ) (bits : List Bool) (base : ℕ) : az b bits base < 2 ^ b := by
 induction b with
 | zero => simp [az]
 | succ b ih =>
   unfold az at ih ⊢
   rw [List.range_succ,List.foldl_append]
   dsimp only [List.foldl_cons,List.foldl_nil]
   rw [pow_succ']
   split_ifs <;> omega
lemma kJ {b : ℕ} {l1 l2 : List Bool} {b1 b2 : ℕ}
   (h : ∀ k < b,l1.getD (b1 + k) false = l2.getD (b2 + k) false) :
   az b l1 b1 = az b l2 b2 := by
 induction b with
 | zero => simp [az]
 | succ b ih =>
   unfold az
   rw [List.range_succ,List.foldl_append,List.foldl_append]
   dsimp only [List.foldl_cons,List.foldl_nil]
   have h1 : List.foldl (fun acc h => 2 * acc + if l1.getD (b1 + h) false = true then 1 else 0)
       0 (List.range b) = az b l1 b1 := rfl
   have h2 : List.foldl (fun acc h => 2 * acc + if l2.getD (b2 + h) false = true then 1 else 0)
       0 (List.range b) = az b l2 b2 := rfl
   rw [h1,h2,ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),h b (Nat.lt_succ_self b)]
lemma lM (b : ℕ) (f : Fin b -> Bool) :
   az b (List.ofFn f) 0 = ∑ h : Fin b,if f (Fin.rev h) then 2 ^ h.val else 0 := by
 induction b with
 | zero => simp [az]
 | succ b ih =>
   unfold az
   rw [List.range_succ,List.foldl_append]
   dsimp only [List.foldl_cons,List.foldl_nil,zero_add]
   have hget : (List.ofFn f).getD b false = f (Fin.last b) := by
     rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
     rfl
   let f' : Fin b -> Bool := fun i => f i.castSucc
   have hsub : List.foldl
       (fun acc h => 2 * acc + if (List.ofFn f).getD (0 + h) false then 1 else 0) 0 (List.range b) =
       az b (List.ofFn f') 0 := by
     apply kJ
     intro k hk
     rw [zero_add,List.getD_eq_getElem _ _ (by simp; omega),
       List.getD_eq_getElem _ _ (by simp [hk]),List.getElem_ofFn,List.getElem_ofFn]
     rfl
   have yJ : (List.ofFn f).getD (0 + b) false = f (Fin.last b) := by simpa using hget
   rw [hsub,yJ,ih f',Fin.sum_univ_succ]
   simp only [Fin.val_zero,pow_zero,Fin.rev_zero,Fin.val_succ,pow_succ',
     Fin.rev_succ,Finset.mul_sum]
   have hs : ∀ i : Fin b,
       2 * (if f' (Fin.rev i) then 2 ^ i.val else 0) =
         if f (Fin.rev i).castSucc then 2 * 2 ^ i.val else 0 := by
     intro i
     dsimp [f']
     split_ifs <;> ring
   rw [Finset.sum_congr rfl (fun i _ => hs i)]
   omega
lemma nT (b : ℕ) (g : Fin b -> Bool) :
   (∑ h : Fin b,if g h then 2 ^ h.val else 0) < 2 ^ b := by
 induction b with
 | zero => simp
 | succ b ih =>
   rw [Fin.sum_univ_castSucc,pow_succ]
   have hs : ∀ i : Fin b,
       (if g i.castSucc then 2 ^ (i.castSucc : Fin (b + 1)).val else 0) =
         if g i.castSucc then 2 ^ i.val else 0 := fun _ => rfl
   rw [Finset.sum_congr rfl (fun i _ => hs i)]
   have hlt := ih (fun i => g i.castSucc)
   simp only [Fin.val_last]
   split_ifs <;> omega
lemma kp {b lo : ℕ} (hlo : lo < 2 ^ b) :
   (2 ^ b + lo).testBit b = true := by
 rw [Nat.testBit_eq_decide_div_mod_eq]
 have h1 : (2 ^ b + lo) / 2 ^ b = 1 := by
   rw [add_comm,Nat.add_div_right _ (by positivity),Nat.div_eq_of_lt hlo]
 simp [h1]
lemma ll {b lo k : ℕ} (hk : k < b) :
   (2 ^ b + lo).testBit k = lo.testBit k := by
 rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
 have hb : b = (b - k) + k := by omega
 have hpow : 2 ^ b = 2 ^ (b - k) * 2 ^ k := by
   conv_lhs => rw [hb,pow_add]
 have wy : 0 < 2 ^ k := Nat.two_pow_pos k
 have hdiv : (2 ^ b + lo) / 2 ^ k = 2 ^ (b - k) + lo / 2 ^ k := by
   rw [hpow,mul_comm (2 ^ (b - k)) (2 ^ k),Nat.mul_add_div wy]
 have h2 : 2 ∣ 2 ^ (b - k) := by
   have hpos : 1 ≤ b - k := by omega
   rw [show b - k = (b - k - 1) + 1 by omega,pow_succ']
   exact dvd_mul_right _ _
 obtain ⟨t,ht⟩ := h2
 rw [hdiv,ht,Nat.add_mod,Nat.mul_mod_right,zero_add,Nat.mod_mod]
lemma jw (b : ℕ) (g : Fin b -> Bool) (i : Fin b) :
   (∑ h : Fin b,if g h then 2 ^ h.val else 0).testBit i.val = g i := by
 induction b with
 | zero => exact Fin.elim0 i
 | succ b ih =>
   rw [Fin.sum_univ_castSucc]
   have hs : ∀ j : Fin b,
       (if g j.castSucc then 2 ^ (j.castSucc : Fin (b + 1)).val else 0) =
         if g j.castSucc then 2 ^ j.val else 0 := fun _ => rfl
   rw [Finset.sum_congr rfl (fun j _ => hs j)]
   let lo := ∑ j : Fin b,if g j.castSucc then 2 ^ j.val else 0
   have hlo : lo < 2 ^ b := nT b (fun j => g j.castSucc)
   induction i using Fin.lastCases with
   | last =>
     simp only [Fin.val_last]
     by_cases hg : g (Fin.last b) = true
     · simp only [hg,↓reduceIte]
       rw [add_comm]
       exact kp hlo
     · have hgf : g (Fin.last b) = false := Bool.eq_false_iff.mpr hg
       simp only [hgf,Bool.false_eq_true,↓reduceIte,add_zero]
       exact Nat.testBit_eq_false_of_lt hlo
   | cast j =>
     simp only [Fin.val_castSucc,Fin.val_last]
     by_cases hg : g (Fin.last b) = true
     · simp only [hg,↓reduceIte]
       rw [add_comm,ll j.isLt]
       exact ih (fun k => g k.castSucc) j
     · have hgf : g (Fin.last b) = false := Bool.eq_false_iff.mpr hg
       simp only [hgf,Bool.false_eq_true,↓reduceIte,add_zero]
       exact ih (fun k => g k.castSucc) j
lemma lz (b x : ℕ) (hx : x < 2 ^ b) :
   (∑ h : Fin b,if x.testBit h.val then 2 ^ h.val else 0) = x := by
 apply Nat.eq_of_testBit_eq
 intro k
 by_cases hk : k < b
 · exact jw b (fun h : Fin b => x.testBit h.val) ⟨k,hk⟩
 · have hlt := nT b (fun h : Fin b => x.testBit h.val)
   have hle : 2 ^ b ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
   rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt hle),
     Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hle)]
noncomputable def pF (b : ℕ) : (Fin b -> Bool) ≃ Fin (2 ^ b) :=
 { toFun := fun f => ⟨az b (List.ofFn f) 0,bB b (List.ofFn f) 0⟩
   invFun := fun x h => x.val.testBit (Fin.rev h).val
   left_inv := fun f => by
     funext h
     dsimp only
     rw [lM]
     have h1 := jw b (fun k => f (Fin.rev k)) (Fin.rev h)
     simpa using h1
   right_inv := fun x => by
     apply Fin.ext
     dsimp only
     rw [lM]
     have h1 : ∀ k : Fin b,x.val.testBit (Fin.rev (Fin.rev k)).val = x.val.testBit k.val := by
       intro k; simp
     simp_rw [h1]
     exact lz b x.val x.isLt }
lemma oI {R P b ell : ℕ} (hR : 0 < R) (hP : 0 < P) (hb : 2 * P ≤ 2 ^ b)
   (hle : R * (P * b) ≤ ell) (F : Finset (Finset (Fin P))) (hF : F.Nonempty) :
   let r8 : (Fin ell -> Bool) -> Fin R -> Fin P -> Fin (2 ^ b) := fun tape r idx =>
     ⟨az b (List.ofFn tape) ((r.val * P + idx.val) * b),
       bB b (List.ofFn tape) ((r.val * P + idx.val) * b)⟩
   letI : DecidablePred (fun tape : Fin ell -> Bool => ∀ r : Fin R,¬ dS F (r8 tape r)) :=
     Classical.decPred _
   2 ^ R * ((Finset.univ : Finset (Fin ell -> Bool)).filter
     (fun tape => ∀ r : Fin R,¬ dS F (r8 tape r))).card ≤ 2 ^ ell := by
 classical
 intro r8
 have hb0 : 0 < b := by
   by_contra h0
   have zI : b = 0 := by omega
   subst zI
   simp at hb
   omega
 let K := R * (P * b)
 let e1 : Fin ell ≃ Fin K ⊕ Fin (ell - K) :=
   (Fin.castOrderIso (by omega : ell = K + (ell - K))).toEquiv.trans finSumFinEquiv.symm
 let e2 : (Fin ell -> Bool) ≃ (Fin R -> Fin P -> Fin b -> Bool) × (Fin (ell - K) -> Bool) :=
   { toFun := fun tape =>
       (fun r idx h => tape (e1.symm (Sum.inl ⟨(r.val * P + idx.val) * b + h.val,by
         have hr := r.isLt; have hi := idx.isLt; have hh := h.isLt
         have h1 : r.val * P + idx.val < R * P := by nlinarith
         have h2 : (r.val * P + idx.val) * b + h.val < (R * P) * b := by nlinarith
         change (r.val * P + idx.val) * b + h.val < R * (P * b)
         linarith [show R * (P * b) = (R * P) * b by ring]⟩)),
        fun pJ => tape (e1.symm (Sum.inr pJ)))
     invFun := fun p t => match e1 t with
       | Sum.inl pos =>
         let rp := pos.val / b
         let h : Fin b := ⟨pos.val % b,Nat.mod_lt _ hb0⟩
         let r : Fin R := ⟨rp / P,by
           have hlt : rp < R * P := by
             rw [Nat.div_lt_iff_lt_mul hb0]
             simpa [K,mul_assoc] using pos.isLt
           rw [Nat.div_lt_iff_lt_mul hP]
           simpa [mul_comm] using hlt⟩
         let idx : Fin P := ⟨rp % P,Nat.mod_lt _ hP⟩
         p.1 r idx h
       | Sum.inr pJ => p.2 pJ
     left_inv := fun tape => by
       funext t
       rcases h : e1 t with pos | pJ
       · simp only [h]
         congr 1
         apply e1.injective
         simp only [e1.apply_symm_apply,h,Sum.inl.injEq]
         apply Fin.ext
         dsimp only
         have h1 := Nat.div_add_mod (pos.val / b) P
         have h2 := Nat.div_add_mod pos.val b
         nlinarith
       · simp only [h]
         exact congrArg tape (e1.injective (by simp [e1.apply_symm_apply,h]))
     right_inv := fun p => by
       ext r idx h
       · dsimp only
         rw [e1.apply_symm_apply]
         have h1 : ((r.val * P + idx.val) * b + h.val) / b = r.val * P + idx.val := by
           rw [show (r.val * P + idx.val) * b + h.val = b * (r.val * P + idx.val) + h.val by ring,
             Nat.mul_add_div hb0,Nat.div_eq_of_lt h.isLt,add_zero]
         have h2 : ((r.val * P + idx.val) * b + h.val) % b = h.val := by
           simp [Nat.mod_eq_of_lt h.isLt]
         have h3 : (r.val * P + idx.val) / P = r.val := by
           rw [show r.val * P + idx.val = P * r.val + idx.val by ring,
             Nat.mul_add_div hP,Nat.div_eq_of_lt idx.isLt,add_zero]
         have h4 : (r.val * P + idx.val) % P = idx.val := by
           simp [Nat.mod_eq_of_lt idx.isLt]
         simp [h1,h2,h3,h4]
       · dsimp only
         rw [e1.apply_symm_apply] }
 let e3 : (Fin R -> Fin P -> Fin b -> Bool) × (Fin (ell - K) -> Bool) ≃
     (Fin R -> Fin P -> Fin (2 ^ b)) × (Fin (ell - K) -> Bool) :=
   Equiv.prodCongr (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => pF b) (Equiv.refl _)
 let e := e2.trans e3
 have uq : ∀ (m : ℕ) (hm : m < K),e1.symm (Sum.inl ⟨m,hm⟩) = ⟨m,lt_of_lt_of_le hm hle⟩ := by
   intro m hm
   apply Fin.ext
   simp [e1,finSumFinEquiv]
 have uQ : ∀ tape r idx,(e tape).1 r idx = r8 tape r idx := by
   intro tape r idx
   apply Fin.ext
   change az b (List.ofFn fun h : Fin b => (e2 tape).1 r idx h) 0 =
     az b (List.ofFn tape) ((r.val * P + idx.val) * b)
   apply kJ
   intro k hk
   have yh : (List.ofFn fun h : Fin b => (e2 tape).1 r idx h).getD (0 + k) false =
       (e2 tape).1 r idx ⟨k,hk⟩ := by
     rw [zero_add,List.getD_eq_getElem _ _ (by simp [hk]),List.getElem_ofFn]
   rw [yh]
   have xG : (r.val * P + idx.val) * b + k < K := by
     have hr := r.isLt; have hi := idx.isLt
     have h1 : r.val * P + idx.val < R * P := by nlinarith
     have h2 : (r.val * P + idx.val) * b + k < (R * P) * b := by nlinarith
     linarith [show K = (R * P) * b by dsimp [K]; ring]
   have hlt : (r.val * P + idx.val) * b + k < ell := lt_of_lt_of_le xG hle
   have hget : (List.ofFn tape).getD ((r.val * P + idx.val) * b + k) false =
       tape ⟨(r.val * P + idx.val) * b + k,hlt⟩ := by
     rw [List.getD_eq_getElem _ _ (by simp [hlt]),List.getElem_ofFn]
   rw [hget]
   change tape (e1.symm (Sum.inl ⟨(r.val * P + idx.val) * b + k,xG⟩)) = _
   rw [uq _ xG]
 let pR : Finset (Fin P -> Fin (2 ^ b)) :=
   Finset.univ.filter (fun u => ¬ dS F u)
 let qS := (Finset.univ : Finset (Fin ell -> Bool)).filter
   (fun tape => ∀ r : Fin R,¬ dS F (r8 tape r))
 let Target := ((Finset.univ : Finset (Fin R -> Fin P -> Fin (2 ^ b))).filter
   (fun v => ∀ r,v r ∈ pR)) ×ˢ (Finset.univ : Finset (Fin (ell - K) -> Bool))
 have himg : qS.image e = Target := by
   ext ⟨v,pJ⟩
   simp only [Finset.mem_image,qS,Target,Finset.mem_filter,Finset.mem_univ,true_and,
     Finset.mem_product,pR]
   constructor
   · rintro ⟨tape,htape,heq⟩
     have hv : ∀ r,¬ dS F ((e tape).1 r) := fun r => by
       rw [funext (uQ tape r)]; exact htape r
     rw [heq] at hv
     exact ⟨hv,trivial⟩
   · rintro ⟨hv,_⟩
     refine ⟨e.symm (v,pJ),fun r => ?_,e.apply_symm_apply _⟩
     have he' : e (e.symm (v,pJ)) = (v,pJ) := e.apply_symm_apply _
     have hr : (e (e.symm (v,pJ))).1 r = v r := congrFun (congrArg Prod.fst he') r
     rw [← funext (uQ (e.symm (v,pJ)) r),hr]
     exact hv r
 have oX : qS.card = Target.card := by
   rw [← himg,Finset.card_image_of_injective _ e.injective]
 have hprod : Target.card = pR.card ^ R * 2 ^ (ell - K) := by
   rw [Finset.card_product]
   have h1 : ((Finset.univ : Finset (Fin R -> Fin P -> Fin (2 ^ b))).filter
       (fun v => ∀ r,v r ∈ pR)).card = pR.card ^ R := by
     have heq : (Finset.univ : Finset (Fin R -> Fin P -> Fin (2 ^ b))).filter (fun v => ∀ r,v r ∈ pR) =
         Fintype.piFinset (fun _ : Fin R => pR) := by
       ext v; simp
     rw [heq,Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
   have h2 : (Finset.univ : Finset (Fin (ell - K) -> Bool)).card = 2 ^ (ell - K) := by
     rw [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
   rw [h1,h2]
 have hiso : 2 * pR.card ≤ (2 ^ b) ^ P := by
   convert kA hP hb F hF
 have hres : 2 ^ R * qS.card ≤ 2 ^ ell := by
   rw [oX,hprod]
   calc 2 ^ R * (pR.card ^ R * 2 ^ (ell - K))
       = (2 * pR.card) ^ R * 2 ^ (ell - K) := by rw [mul_pow]; ring
     _ ≤ ((2 ^ b) ^ P) ^ R * 2 ^ (ell - K) :=
         Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hiso R)
     _ = 2 ^ K * 2 ^ (ell - K) := by
         rw [← pow_mul,← pow_mul]
         congr 1
         dsimp [K]; ring
     _ = 2 ^ ell := by
         rw [← pow_add,Nat.add_sub_of_le hle]
 convert hres
lemma mE {a n m ce : ℕ} (ha : 1 ≤ a) (hn : 2 ≤ n)
   (hL : a + n + m + 4 ≤ ce) :
   let P := n * (n - 1) / 2
   let b := 2 * (Nat.log2 n + 1) + 1
   let R := a + n + m + 2
   let ell := (ce + 2) ^ 5
   0 < P /\ 2 * P ≤ 2 ^ b /\ 2 * n * n < 2 ^ b /\ 2 ^ b ≤ 8 * n * n /\
   R * (P * b) ≤ ell /\
   (n / 2 + 1) * (m + 1) ≤ 2 ^ (n + m + 2) := by
 intro P b R ell
 have tq : Nat.log2 n = Nat.log 2 n := Nat.log2_eq_log_two
 have AA : n < 2 ^ (Nat.log2 n + 1) := by
   rw [tq]; exact Nat.lt_pow_succ_log_self Nat.one_lt_two n
 have hlog2 : 2 ^ Nat.log2 n ≤ n := by
   rw [tq]; exact Nat.pow_log_le_self 2 (by omega)
 have Am : 2 ^ (Nat.log2 n + 1) ≤ 2 * n := by rw [pow_succ']; omega
 have AC : 2 ^ b = 2 * (2 ^ (Nat.log2 n + 1)) ^ 2 := by
   dsimp [b]
   rw [pow_succ',mul_comm 2 (Nat.log2 n + 1),pow_mul]
 have zO : 2 * n * n < 2 ^ b := by
   rw [AC]
   have hsq : n * n < (2 ^ (Nat.log2 n + 1)) ^ 2 := by nlinarith
   nlinarith
 have AX : 2 ^ b ≤ 8 * n * n := by
   rw [AC]
   have hsq : (2 ^ (Nat.log2 n + 1)) ^ 2 ≤ 4 * n * n := by nlinarith
   nlinarith
 have hP0 : 0 < P := by
   dsimp [P]
   have h1 : 1 ≤ n - 1 := by omega
   have h2 : 2 ≤ n * (n - 1) := by nlinarith
   omega
 have AU : 2 * P ≤ 2 ^ b := by
   have : 2 * P ≤ n * (n - 1) := Nat.mul_div_le _ 2
   have hle : n - 1 ≤ n := Nat.sub_le n 1
   nlinarith
 have yF : P ≤ ce ^ 2 := by
   have hle : n - 1 ≤ n := Nat.sub_le n 1
   have : 2 * P ≤ n * (n - 1) := Nat.mul_div_le _ 2
   have : P ≤ n * n := by nlinarith
   have : n ≤ ce := by omega
   nlinarith
 have zt : Nat.log2 n ≤ n := Nat.log2_le_self n
 have yg : b ≤ 3 * (ce + 2) := by omega
 have hL3 : 3 ≤ ce + 2 := by omega
 have yz : R ≤ ce + 2 := by omega
 have zX : R * (P * b) ≤ ell := by
   dsimp [ell]
   have h1 : P ≤ (ce + 2) ^ 2 := yF.trans (by nlinarith)
   have h2 : P * b ≤ (ce + 2) ^ 2 * (3 * (ce + 2)) := Nat.mul_le_mul h1 yg
   have h3 : (ce + 2) ^ 2 * (3 * (ce + 2)) ≤ (ce + 2) ^ 4 := by
     have : 3 * (ce + 2) ^ 3 ≤ (ce + 2) * (ce + 2) ^ 3 :=
       Nat.mul_le_mul_right _ hL3
     linarith [show (ce + 2) ^ 2 * (3 * (ce + 2)) = 3 * (ce + 2) ^ 3 by ring,
               show (ce + 2) * (ce + 2) ^ 3 = (ce + 2) ^ 4 by ring]
   calc R * (P * b)
       ≤ (ce + 2) * (ce + 2) ^ 4 := Nat.mul_le_mul yz (h2.trans h3)
     _ = (ce + 2) ^ 5 := by ring
 have hlt1 : 1 < 2 := by decide
 have hn2 : n / 2 + 1 ≤ 2 ^ n := by
   have : n < 2 ^ n := Nat.lt_pow_self hlt1
   omega
 have hm1 : m + 1 < 2 ^ (m + 1) := Nat.lt_pow_self hlt1
 have hslots : (n / 2 + 1) * (m + 1) ≤ 2 ^ (n + m + 2) := by
   calc (n / 2 + 1) * (m + 1)
       ≤ 2 ^ n * 2 ^ (m + 1) := Nat.mul_le_mul hn2 hm1.le
     _ = 2 ^ (n + (m + 1)) := (pow_add 2 n (m + 1)).symm
     _ ≤ 2 ^ (n + m + 2) := Nat.pow_le_pow_right (by decide) (by omega)
 exact ⟨hP0,AU,zO,AX,zX,hslots⟩
end Prob
section Det
lemma jz {ι R : Type*} [Semiring R] (s : Finset ι) (f : ι -> Polynomial R) (k : ℕ) :
   (∑ i ∈ s,f i).coeff k = ∑ i ∈ s,(f i).coeff k := by
 classical
 induction s using Finset.induction_on with
 | empty => simp
 | insert a s ha ih => rw [Finset.sum_insert ha,Finset.sum_insert ha,Polynomial.coeff_add,ih]
lemma jm {ι : Type*} (s : Finset ι) (g : ι -> ℕ) :
   ∏ x ∈ s,Polynomial.monomial (g x) (1 : ZMod 2) = Polynomial.monomial (∑ x ∈ s,g x) 1 := by
 classical
 induction s using Finset.induction_on with
 | empty => simp
 | insert a s ha ih =>
   rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,Polynomial.monomial_mul_monomial,one_mul]
def aa {n : ℕ} (idx : Fin (ae n).length) : Fin n × Fin n :=
 (ae n).get idx
lemma bI {n : ℕ} : Function.Injective (aa (n := n)) := by
 intro a b hab
 exact (List.Nodup.get_inj_iff (jW n)).mp hab
lemma mf {n : ℕ} (idx : Fin (ae n).length) :
   (aa idx).1 < (aa idx).2 :=
 (eJ _).mp (List.get_mem _ _)
def j8 (n : ℕ) (act : Fin (ae n).length -> Bool) : Finset (Fin n × Fin n) :=
 (Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).image aa
lemma j6 {n : ℕ} {act : Fin (ae n).length -> Bool} {idx : Fin (ae n).length} :
   aa idx ∈ j8 n act ↔ act idx = true := by
 simp only [j8,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
 constructor
 · rintro ⟨j,hj,hje⟩
   have := bI hje
   subst this
   exact hj
 · intro h
   exact ⟨idx,h,rfl⟩
lemma fh {n : ℕ} (act : Fin (ae n).length -> Bool) :
   j8 n act ⊆ (ae n).toFinset := by
 intro e he
 simp only [j8,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] at he
 rcases he with ⟨idx,_,rfl⟩
 exact List.mem_toFinset.mpr (List.get_mem _ _)
noncomputable def bG (n : ℕ) (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) :
   Matrix (Fin n) (Fin n) (Polynomial (ZMod 2)) :=
 fun i j =>
   if i = j then 1
   else ∑ idx : Fin (ae n).length,
     if act idx && ((aa idx == (i,j)) || (aa idx == (j,i)))
     then Polynomial.monomial (deg idx) 1 else 0
lemma oB (n : ℕ) (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) (i : Fin n) :
   bG n act deg i i = 1 := by
 simp [bG]
lemma oD (n : ℕ) (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) (i j : Fin n) :
   bG n act deg i j = bG n act deg j i := by
 by_cases h : i = j
 · subst h; rfl
 · simp only [bG,if_neg h,if_neg (Ne.symm h)]
   refine Finset.sum_congr rfl fun idx _ => ?_
   simp [Bool.or_comm]
lemma pq (n : ℕ) (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) (idx : Fin (ae n).length) :
   bG n act deg (aa idx).1 (aa idx).2 =
     if act idx then Polynomial.monomial (deg idx) 1 else 0 := by
 have hlt := mf idx
 have hne : (aa idx).1 ≠ (aa idx).2 := hlt.ne
 simp only [bG,if_neg hne]
 rw [Finset.sum_eq_single idx]
 · simp [beq_self_eq_true]
 · intro vV _ wp
   have h1 : (aa vV == ((aa idx).1,(aa idx).2)) = false := by
     rw [beq_eq_false_iff_ne]
     intro heq
     apply wp
     exact bI (heq.trans (Prod.ext rfl rfl))
   have h2 : (aa vV == ((aa idx).2,(aa idx).1)) = false := by
     rw [beq_eq_false_iff_ne]
     intro heq
     have hlt' := mf vV
     rw [heq] at hlt'
     exact lt_asymm hlt hlt'
   simp [h1,h2]
 · intro h
   exact absurd (Finset.mem_univ idx) h
lemma gF {n : ℕ} (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) (σ : Equiv.Perm (Fin n)) (hσ : ∀ i,σ (σ i) = i) :
   ∏ i : Fin n,bG n act deg (σ i) i =
     if aQ σ ⊆ j8 n act then
       Polynomial.monomial
         (2 * ∑ idx ∈ Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ aQ σ),deg idx) 1
     else 0 := by
 let M := aQ σ
 have hM : IsMatching n M := eh σ hσ
 let F0 : Finset (Fin n) := Finset.univ.filter (fun i => σ i = i)
 let F1 : Finset (Fin n) := M.image Prod.fst
 let F2 : Finset (Fin n) := M.image Prod.snd
 have zZ : Disjoint F1 F2 := by
   rw [Finset.disjoint_left]
   intro v hv1 hv2
   simp only [F1,F2,Finset.mem_image] at hv1 hv2
   rcases hv1 with ⟨e,he,rfl⟩
   rcases hv2 with ⟨g,hg,hge⟩
   by_cases h : e = g
   · subst h; exact (hM.1 e he).ne hge.symm
   · have hd := hM.2 e he g hg h
     rw [Finset.disjoint_left] at hd
     exact hd (a := e.1) (by simp [al]) (by simp [al,hge])
 have x8 : Disjoint F0 (F1 ∪ F2) := by
   rw [Finset.disjoint_left]
   intro i hi0 hi12
   simp only [F0,Finset.mem_filter,Finset.mem_univ,true_and] at hi0
   simp only [Finset.mem_union,F1,F2,Finset.mem_image] at hi12
   rcases hi12 with ⟨e,he,rfl⟩ | ⟨e,he,rfl⟩
   · have he' := (Finset.mem_filter.mp he).2
     rw [he'.2] at hi0
     exact he'.1.ne' hi0
   · have he' := (Finset.mem_filter.mp he).2
     have h2 : σ e.2 = e.1 := by rw [← he'.2,hσ]
     rw [h2] at hi0
     exact he'.1.ne hi0
 have hFu : F0 ∪ (F1 ∪ F2) = Finset.univ := by
   ext i
   simp only [Finset.mem_union,Finset.mem_univ,iff_true,F0,F1,F2,Finset.mem_filter,
     Finset.mem_image,true_and]
   by_cases hi : σ i = i
   · left; exact hi
   · right
     rcases lt_or_gt_of_ne hi with hlt | hlt
     · right; refine ⟨(σ i,i),?_,rfl⟩
       simp [M,aQ,hlt,hσ i]
     · left; refine ⟨(i,σ i),?_,rfl⟩
       simp [M,aQ,hlt]
 have hsplit : ∏ i : Fin n,bG n act deg (σ i) i =
     (∏ i ∈ F0,bG n act deg (σ i) i) *
     ((∏ i ∈ F1,bG n act deg (σ i) i) * (∏ i ∈ F2,bG n act deg (σ i) i)) := by
   rw [← hFu,Finset.prod_union x8,Finset.prod_union zZ]
 have hP0 : ∏ i ∈ F0,bG n act deg (σ i) i = 1 := by
   apply Finset.prod_eq_one
   intro i hi
   have hsi : σ i = i := (Finset.mem_filter.mp hi).2
   rw [hsi,oB]
 have uW : ∀ e1 ∈ M,∀ e2 ∈ M,e1.1 = e2.1 -> e1 = e2 := by
   intro e1 he1 e2 he2 h1
   by_contra hne
   have hd := hM.2 e1 he1 e2 he2 hne
   rw [Finset.disjoint_left] at hd
   exact hd (a := e1.1) (by simp [al]) (by simp [al,h1])
 have uX : ∀ e1 ∈ M,∀ e2 ∈ M,e1.2 = e2.2 -> e1 = e2 := by
   intro e1 he1 e2 he2 h2
   by_contra hne
   have hd := hM.2 e1 he1 e2 he2 hne
   rw [Finset.disjoint_left] at hd
   exact hd (a := e1.2) (by simp [al]) (by simp [al,h2])
 have hP1 : ∏ i ∈ F1,bG n act deg (σ i) i = ∏ e ∈ M,bG n act deg e.1 e.2 := by
   rw [Finset.prod_image uW]
   apply Finset.prod_congr rfl
   intro e he
   have he' := (Finset.mem_filter.mp he).2
   rw [he'.2,oD]
 have hP2 : ∏ i ∈ F2,bG n act deg (σ i) i = ∏ e ∈ M,bG n act deg e.1 e.2 := by
   rw [Finset.prod_image uX]
   apply Finset.prod_congr rfl
   intro e he
   have he' := (Finset.mem_filter.mp he).2
   have h2 : σ e.2 = e.1 := by rw [← he'.2,hσ]
   rw [h2]
 rw [hsplit,hP0,one_mul,hP1,hP2,← Finset.prod_mul_distrib]
 by_cases hsub : M ⊆ j8 n act
 · rw [if_pos hsub]
   have himg : (Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ M)).image aa = M := by
     ext e
     simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
     constructor
     · rintro ⟨idx,hi,rfl⟩; exact hi
     · intro he
       have hp : e ∈ (ae n).toFinset := fh act (hsub he)
       rw [List.mem_toFinset] at hp
       obtain ⟨idx,hidx⟩ := List.mem_iff_get.mp hp
       refine ⟨idx,?_,hidx⟩
       dsimp only [aa]
       rwa [hidx]
   have ub : ∏ e ∈ M,(bG n act deg e.1 e.2 * bG n act deg e.1 e.2) =
       ∏ idx ∈ Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ M),
         Polynomial.monomial (2 * deg idx) 1 := by
     conv_lhs => rw [← himg]
     rw [Finset.prod_image (fun a _ b _ hab => bI hab)]
     apply Finset.prod_congr rfl
     intro idx hidx
     have AY : aa idx ∈ M := (Finset.mem_filter.mp hidx).2
     have uT : act idx = true := j6.mp (hsub AY)
     rw [pq,if_pos uT,Polynomial.monomial_mul_monomial,one_mul,← two_mul]
   rw [ub,jm,Finset.mul_sum]
 · rw [if_neg hsub]
   rw [Finset.not_subset] at hsub
   obtain ⟨e,heM,heNot⟩ := hsub
   have Be : e ∈ ae n := (eJ e).mpr (hM.1 e heM)
   obtain ⟨idx,hidx⟩ := List.mem_iff_get.mp Be
   have xS : act idx = false := by
     by_contra h
     have h' : act idx = true := Bool.eq_true_of_not_eq_false h
     apply heNot
     have := j6.mpr h'
     dsimp only [aa] at this
     rwa [hidx] at this
   have hzero : bG n act deg e.1 e.2 = 0 := by
     have := pq n act deg idx
     dsimp only [aa] at this
     rw [hidx,xS,if_neg (by decide)] at this
     exact this
   exact Finset.prod_eq_zero heM (by rw [hzero,zero_mul])
open Classical in
lemma nD {n : ℕ} (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) :
   (bG n act deg).det =
     ∑ S ∈ (Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
       (fun S => IsMatching n (S.image aa)),
       Polynomial.monomial (2 * ∑ idx ∈ S,deg idx) 1 := by
 rw [qH _ (oD n act deg)]
 let Inv := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i,σ (σ i) = i)
 have vU : ∑ σ ∈ Inv,∏ i : Fin n,bG n act deg (σ i) i =
     ∑ σ ∈ Inv.filter (fun σ => aQ σ ⊆ j8 n act),
       Polynomial.monomial
         (2 * ∑ idx ∈ Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ aQ σ),deg idx) 1 := by
   rw [← Finset.sum_filter_add_sum_filter_not Inv (fun σ => aQ σ ⊆ j8 n act)]
   have hz : ∑ σ ∈ Inv.filter (fun σ => ¬ aQ σ ⊆ j8 n act),
       ∏ i : Fin n,bG n act deg (σ i) i = 0 := by
     apply Finset.sum_eq_zero
     intro σ hσ
     have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
     have h2 := (Finset.mem_filter.mp hσ).2
     rw [gF act deg σ h1,if_neg h2]
   rw [hz,add_zero]
   apply Finset.sum_congr rfl
   intro σ hσ
   have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
   have h2 := (Finset.mem_filter.mp hσ).2
   rw [gF act deg σ h1,if_pos h2]
 rw [vU]
 let A := (Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
   (fun S => IsMatching n (S.image aa))
 refine Finset.sum_nbij'
   (fun σ => Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ aQ σ))
   (fun S => aP (S.image aa))
   ?_ ?_ ?_ ?_ ?_
 · intro σ hσ
   have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
   have h2 := (Finset.mem_filter.mp hσ).2
   have himg : (Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ aQ σ)).image aa = aQ σ := by
     ext e
     simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
     constructor
     · rintro ⟨idx,hi,rfl⟩; exact hi
     · intro he
       have hp : e ∈ (ae n).toFinset := fh act (h2 he)
       rw [List.mem_toFinset] at hp
       obtain ⟨idx,hidx⟩ := List.mem_iff_get.mp hp
       refine ⟨idx,?_,hidx⟩
       dsimp only [aa]; rwa [hidx]
   simp only [A,Finset.mem_filter,Finset.mem_powerset]
   refine ⟨fun idx hidx => ?_,?_⟩
   · simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hidx ⊢
     exact j6.mp (h2 hidx)
   · rw [himg]; exact eh σ h1
 · intro S hS
   simp only [A,Finset.mem_filter,Finset.mem_powerset] at hS
   have hM : IsMatching n (S.image aa) := hS.2
   simp only [Inv,Finset.mem_filter,Finset.mem_univ,true_and]
   refine ⟨bQ hM,?_⟩
   rw [bo hM]
   intro e he
   simp only [Finset.mem_image] at he
   rcases he with ⟨idx,hidx,rfl⟩
   have uT : act idx = true := (Finset.mem_filter.mp (hS.1 hidx)).2
   exact j6.mpr uT
 · intro σ hσ
   have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
   have h2 := (Finset.mem_filter.mp hσ).2
   have himg : (Finset.univ.filter (fun idx : Fin (ae n).length => aa idx ∈ aQ σ)).image aa = aQ σ := by
     ext e
     simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
     constructor
     · rintro ⟨idx,hi,rfl⟩; exact hi
     · intro he
       have hp : e ∈ (ae n).toFinset := fh act (h2 he)
       rw [List.mem_toFinset] at hp
       obtain ⟨idx,hidx⟩ := List.mem_iff_get.mp hp
       refine ⟨idx,?_,hidx⟩
       dsimp only [aa]; rwa [hidx]
   rw [himg,gz σ h1]
 · intro S hS
   simp only [A,Finset.mem_filter,Finset.mem_powerset] at hS
   ext idx
   rw [Finset.mem_filter]
   simp only [Finset.mem_univ,true_and]
   rw [bo hS.2,Finset.mem_image]
   exact ⟨fun ⟨j,hj,hje⟩ => (bI hje) ▸ hj,fun hidx => ⟨idx,hidx,rfl⟩⟩
 · intro _ _
   rfl
open Classical in
lemma gu {n U : ℕ} (act : Fin (ae n).length -> Bool)
   (c : Fin (ae n).length -> ℕ) (u : Fin (ae n).length -> Fin U)
   (B : ℕ) (hB : ∀ S : Finset (Fin (ae n).length),
     IsMatching n (S.image aa) -> ap u S < B)
   (T w : ℕ) (hw : w < B) :
   let deg := fun idx => B * c idx + (u idx).val
   let F := ((Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
     (fun S => IsMatching n (S.image aa) /\ ∑ idx ∈ S,c idx = T))
   ((bG n act deg).det).coeff (2 * (B * T + w)) =
     if (F.filter (fun S => ap u S = w)).card % 2 = 1 then 1 else 0 := by
 intro deg F
 rw [nD,jz]
 have hterm : ∀ S ∈ (Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
     (fun S => IsMatching n (S.image aa)),
     (Polynomial.monomial (2 * ∑ idx ∈ S,deg idx) (1 : ZMod 2)).coeff (2 * (B * T + w)) =
       if S ∈ F.filter (fun S => ap u S = w) then (1 : ZMod 2) else 0 := by
   intro S hS
   have hS' := Finset.mem_filter.mp hS
   have hwt : ap u S < B := hB S hS'.2
   have hdeg : ∑ idx ∈ S,deg idx = B * (∑ idx ∈ S,c idx) + ap u S := by
     dsimp only [deg,ap]
     rw [Finset.sum_add_distrib,← Finset.mul_sum]
   rw [hdeg]
   simp only [Polynomial.coeff_monomial,Finsupp.single_apply]
   have hiff : 2 * (B * (∑ idx ∈ S,c idx) + ap u S) = 2 * (B * T + w) ↔
       S ∈ F.filter (fun S => ap u S = w) := by
     simp only [F,Finset.mem_filter,Finset.mem_powerset]
     constructor
     · intro heq
       have heq' : B * (∑ idx ∈ S,c idx) + ap u S = B * T + w := by omega
       have hmod : (B * (∑ idx ∈ S,c idx) + ap u S) % B = (B * T + w) % B :=
         congrArg (· % B) heq'
       have hw1 : ap u S = w := by
         rwa [Nat.mul_add_mod,Nat.mul_add_mod,Nat.mod_eq_of_lt hwt,Nat.mod_eq_of_lt hw] at hmod
       have hc1 : ∑ idx ∈ S,c idx = T := by
         have hBpos : 0 < B := by omega
         nlinarith [heq',hw1]
       exact ⟨⟨Finset.mem_powerset.mp hS'.1,hS'.2,hc1⟩,hw1⟩
     · rintro ⟨⟨_,_,hc1⟩,hw1⟩
       rw [hc1,hw1]
   by_cases hmem : S ∈ F.filter (fun S => ap u S = w)
   · rw [if_pos (hiff.mpr hmem),if_pos hmem]
   · rw [if_neg (fun heq => hmem (hiff.mp heq)),if_neg hmem]
 rw [Finset.sum_congr rfl hterm]
 have w3 : F.filter (fun S => ap u S = w) ⊆
     (Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
       (fun S => IsMatching n (S.image aa)) := by
   intro S hS
   simp only [F,Finset.mem_filter,Finset.mem_powerset] at hS ⊢
   exact ⟨hS.1.1,hS.1.2.1⟩
 rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr w3,
   Finset.sum_const,nsmul_eq_mul,mul_one]
 rcases Nat.mod_two_eq_zero_or_one (F.filter (fun S => ap u S = w)).card with hm | hm
 · rw [if_neg (by omega),ZMod.natCast_eq_zero_iff]
   exact Nat.dvd_of_mod_eq_zero hm
 · rw [if_pos hm]
   have hdiv : (F.filter (fun S => ap u S = w)).card =
       2 * ((F.filter (fun S => ap u S = w)).card / 2) + 1 := by omega
   rw [hdiv]
   push_cast
   have AM : (2 : ZMod 2) = 0 := by decide
   simp [AM]
open Classical in
lemma kb {n U : ℕ} (act : Fin (ae n).length -> Bool)
   (c : Fin (ae n).length -> ℕ) (u : Fin (ae n).length -> Fin U)
   (B : ℕ) (hB : ∀ S : Finset (Fin (ae n).length),
     IsMatching n (S.image aa) -> ap u S < B)
   (T : ℕ)
   (uZ : dS ((Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
     (fun S => IsMatching n (S.image aa) /\ ∑ idx ∈ S,c idx = T)) u) :
   let F := (Finset.univ.filter (fun idx : Fin (ae n).length => act idx)).powerset.filter
     (fun S => IsMatching n (S.image aa) /\ ∑ idx ∈ S,c idx = T)
   let deg := fun idx => B * c idx + (u idx).val
   ∃ S_min ∈ F,
     let tn := ap u S_min
     tn < B /\
     ((bG n act deg).det).coeff (2 * (B * T + tn)) = 1 /\
     (∀ w < tn,((bG n act deg).det).coeff (2 * (B * T + w)) = 0) /\
     ∀ idx : Fin (ae n).length,
       let cw := fun j => act j && (j != idx)
       (((bG n cw deg).det).coeff (2 * (B * T + tn)) = 0 ↔ idx ∈ S_min) := by
 intro F deg
 rcases uZ with ⟨S_min,hSmin,hstrict⟩
 have sK := Finset.mem_filter.mp hSmin
 have hwB : ap u S_min < B := hB S_min sK.2.1
 refine ⟨S_min,hSmin,hwB,?_,?_,?_⟩
 · rw [gu act c u B hB T (ap u S_min) hwB]
   have hflt : F.filter (fun S => ap u S = ap u S_min) = {S_min} := by
     ext S
     simp only [Finset.mem_filter,Finset.mem_singleton]
     constructor
     · rintro ⟨hSF,xR⟩
       by_contra hne
       have hlt := hstrict S hSF hne
       omega
     · rintro rfl
       exact ⟨hSmin,rfl⟩
   rw [hflt,Finset.card_singleton]
   simp
 · intro w hw
   rw [gu act c u B hB T w (hw.trans hwB)]
   have hflt : F.filter (fun S => ap u S = w) = ∅ := by
     rw [Finset.eq_empty_iff_forall_notMem]
     intro S hS
     rw [Finset.mem_filter] at hS
     by_cases hne : S = S_min
     · subst hne; omega
     · have hlt := hstrict S hS.1 hne; omega
   rw [hflt,Finset.card_empty]
   simp
 · intro idx cw
   have tW : ∀ j ∈ S_min,act j = true := fun j hj =>
     (Finset.mem_filter.mp (Finset.mem_powerset.mp sK.1 hj)).2
   rw [gu cw c u B hB T (ap u S_min) hwB]
   let yI := (Finset.univ.filter (fun j : Fin (ae n).length => cw j)).powerset.filter
     (fun S => IsMatching n (S.image aa) /\ ∑ j ∈ S,c j = T)
   have yL : yI.filter (fun S => ap u S = ap u S_min) =
       if idx ∈ S_min then ∅ else {S_min} := by
     by_cases hidx : idx ∈ S_min
     · rw [if_pos hidx,Finset.eq_empty_iff_forall_notMem]
       intro S hS
       have hS1 := (Finset.mem_filter.mp hS).1
       have wX := Finset.mem_powerset.mp (Finset.mem_filter.mp hS1).1
       have hSc := (Finset.mem_filter.mp hS1).2
       have hSF : S ∈ F := by
         simp only [F,Finset.mem_filter,Finset.mem_powerset]
         refine ⟨fun j hj => ?_,hSc⟩
         have oC := (Finset.mem_filter.mp (wX hj)).2
         simp only [cw,Bool.and_eq_true] at oC
         simp [oC.1]
       have hne : S ≠ S_min := by
         intro heq; subst heq
         have oC := (Finset.mem_filter.mp (wX hidx)).2
         simp [cw] at oC
       have hlt := hstrict S hSF hne
       have xR : ap u S = ap u S_min := (Finset.mem_filter.mp hS).2
       omega
     · rw [if_neg hidx]
       ext S
       rw [Finset.mem_filter,Finset.mem_singleton]
       constructor
       · rintro ⟨hSdel,xR⟩
         have w9 := (Finset.mem_filter.mp hSdel).1
         have wk := (Finset.mem_filter.mp hSdel).2
         have wz := Finset.mem_powerset.mp w9
         have hSF : S ∈ F := by
           simp only [F,Finset.mem_filter,Finset.mem_powerset]
           refine ⟨fun j hj => ?_,wk⟩
           have oC := (Finset.mem_filter.mp (wz hj)).2
           simp only [cw,Bool.and_eq_true] at oC
           simp [oC.1]
         by_contra hne
         have hlt := hstrict S hSF hne
         omega
       · rintro rfl
         refine ⟨?_,rfl⟩
         simp only [yI,Finset.mem_filter,Finset.mem_powerset]
         refine ⟨fun j hj => ?_,sK.2⟩
         simp only [Finset.mem_filter,Finset.mem_univ,true_and,cw,Bool.and_eq_true,bne_iff_ne]
         refine ⟨tW j hj,fun hjeq => hidx (hjeq ▸ hj)⟩
   rw [yL]
   by_cases hidx : idx ∈ S_min
   · rw [if_pos hidx]; simp [hidx]
   · rw [if_neg hidx]; simp [hidx]
def dD (L : ℕ) (p : Polynomial (ZMod 2)) (v : Fin L -> Bool) : Prop :=
 ∀ r : Fin L,v r = decide (p.coeff r.val = 1)
lemma jT (x y : ZMod 2) :
   decide (x + y = 1) = xor (decide (x = 1)) (decide (y = 1)) := by
 fin_cases x <;> fin_cases y <;> decide
lemma mX (x y : ZMod 2) :
   decide (x * y = 1) = (decide (x = 1) && decide (y = 1)) := by
 fin_cases x <;> fin_cases y <;> decide
lemma fd {α : Type*} (l : List α) (f : α -> ZMod 2) :
   decide ((l.map f).sum = 1) = ((l.filter (fun x => decide (f x = 1))).length % 2 == 1) := by
 have h01 : ∀ z : ZMod 2,z = 0 \/ z = 1 := fun z => by
   fin_cases z
   · exact Or.inl rfl
   · exact Or.inr rfl
 induction l with
 | nil => simp
 | cons a l ih =>
   simp only [List.map_cons,List.sum_cons,List.filter_cons]
   rw [jT,ih]
   rcases h01 (f a) with h0 | h1
   · rw [h0]; simp
   · rw [h1]
     simp only [decide_true,↓reduceIte,List.length_cons,Bool.true_xor]
     rcases Nat.mod_two_eq_zero_or_one (l.filter (fun x => decide (f x = 1))).length with hm | hm
     · simp [Nat.add_mod,hm]
     · simp [Nat.add_mod,hm]
def nk (L : ℕ) : Fin L -> Bool := fun _ => false
def fc {L : ℕ} (v w : Fin L -> Bool) : Fin L -> Bool :=
 fun r => xor (v r) (w r)
def cI {L : ℕ} (v w : Fin L -> Bool) : Fin L -> Bool :=
 fun r => ((List.finRange L).filter (fun a =>
   decide (a.val ≤ r.val) && v a && w ⟨r.val - a.val,by omega⟩)).length % 2 == 1
lemma rI (L : ℕ) : dD L 0 (nk L) := by
 intro r; simp [nk]
lemma kR {L : ℕ} {p q : Polynomial (ZMod 2)} {v w : Fin L -> Bool}
   (hp : dD L p v) (hq : dD L q w) :
   dD L (p + q) (fc v w) := by
 intro r
 rw [fc,Polynomial.coeff_add,jT,hp r,hq r]
lemma kN {L : ℕ} {p q : Polynomial (ZMod 2)} {v w : Fin L -> Bool}
   (hp : dD L p v) (hq : dD L q w) :
   dD L (p * q) (cI v w) := by
 intro r
 have yp : 0 < L := Nat.zero_lt_of_lt r.isLt
 rw [cI,Polynomial.coeff_mul]
 have hsum : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r.val,p.coeff x.1 * q.coeff x.2 =
     ((List.finRange L).map (fun a : Fin L =>
       if a.val ≤ r.val then p.coeff a.val * q.coeff (r.val - a.val) else 0)).sum := by
   rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) r.val]
   have hfin : ∑ a : Fin L,(if a.val ≤ r.val then p.coeff a.val * q.coeff (r.val - a.val) else 0) =
       ∑ a ∈ Finset.range (r.val + 1),p.coeff a * q.coeff (r.val - a) := by
     rw [← Finset.sum_filter]
     refine Finset.sum_nbij' (fun a : Fin L => a.val) (fun a : ℕ => ⟨a % L,Nat.mod_lt a yp⟩)
       ?_ ?_ ?_ ?_ ?_
     · intro a ha; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha
       exact Finset.mem_range.mpr (by omega)
     · intro a ha; simp only [Finset.mem_range] at ha
       simp only [Finset.mem_filter,Finset.mem_univ,true_and]
       rw [Nat.mod_eq_of_lt (by omega)]; omega
     · intro a _; ext; exact Nat.mod_eq_of_lt a.isLt
     · intro a ha; simp only [Finset.mem_range] at ha; exact Nat.mod_eq_of_lt (by omega)
     · intro a ha; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha
       simp [ha]
   rw [← hfin,← List.toFinset_finRange,List.sum_toFinset _ (List.nodup_finRange L)]
 rw [hsum,fd]
 have hflt : (List.finRange L).filter (fun x => decide ((if x.val ≤ r.val then p.coeff x.val * q.coeff (r.val - x.val) else 0) = 1)) =
     (List.finRange L).filter (fun a => decide (a.val ≤ r.val) && v a && w ⟨r.val - a.val,by omega⟩) := by
   congr 1
   ext a
   by_cases har : a.val ≤ r.val
   · simp only [har,↓reduceIte,decide_true,Bool.true_and]
     rw [mX,hp a,hq ⟨r.val - a.val,by omega⟩]
   · simp [har]
 rw [hflt]
def gy {L : ℕ} (n lo : ℕ) (f : Fin n -> Fin L -> Bool) : Fin L -> Bool :=
 ((List.finRange n).filter (fun k => decide (lo ≤ k.val))).foldl
   (fun acc k => fc acc (f k)) (nk L)
lemma ky {α : Type*} {L : ℕ} (l : List α)
   (g : α -> Polynomial (ZMod 2)) (f : α -> Fin L -> Bool)
   (hf : ∀ x ∈ l,dD L (g x) (f x))
   (p0 : Polynomial (ZMod 2)) (acc0 : Fin L -> Bool) (h0 : dD L p0 acc0) :
   dD L (p0 + (l.map g).sum) (l.foldl (fun acc x => fc acc (f x)) acc0) := by
 induction l generalizing p0 acc0 with
 | nil => simp [h0]
 | cons a l ih =>
   simp only [List.foldl_cons,List.map_cons,List.sum_cons,← add_assoc]
   exact ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
     (p0 + g a) (fc acc0 (f a))
     (kR h0 (hf a (List.mem_cons_self ..)))
lemma jS (n lo : ℕ) (g : ℕ -> Polynomial (ZMod 2)) :
   BirdDet.sumFrom n lo g =
     (((List.finRange n).filter (fun k => decide (lo ≤ k.val))).map (fun k => g k.val)).sum := by
 have zK : BirdDet.sumFrom n lo g = ∑ k ∈ Finset.Ico lo n,g k := by
   induction lo using BirdDet.sumFrom_induct n with
   | step lo hlo ih => rw [BirdDet.sumFrom_step n lo g hlo,ih,← Finset.sum_eq_sum_Ico_succ_bot hlo g]
   | stop lo hlo => rw [BirdDet.sumFrom_stop n lo g hlo,Finset.Ico_eq_empty hlo,Finset.sum_empty]
 rw [zK]
 cases n with
 | zero => simp
 | succ n' =>
   have xl : ((List.finRange (n' + 1)).filter (fun k => decide (lo ≤ k.val))).Nodup :=
     (List.nodup_finRange (n' + 1)).filter _
   have zA : ∑ k ∈ Finset.Ico lo (n' + 1),g k =
       ∑ k ∈ ((List.finRange (n' + 1)).filter (fun k => decide (lo ≤ k.val))).toFinset,g k.val := by
     refine Finset.sum_nbij' (fun k : ℕ => ⟨k % (n' + 1),Nat.mod_lt k (Nat.succ_pos n')⟩)
       (fun k => k.val) ?_ ?_ ?_ ?_ ?_
     · intro k hk
       simp only [Finset.mem_Ico] at hk
       simp only [List.mem_toFinset,List.mem_filter,List.mem_finRange,decide_eq_true_eq,true_and]
       rw [Nat.mod_eq_of_lt hk.2]; exact hk.1
     · intro k hk
       simp only [List.mem_toFinset,List.mem_filter,List.mem_finRange,decide_eq_true_eq,true_and] at hk
       exact Finset.mem_Ico.mpr ⟨hk,k.isLt⟩
     · intro k hk
       simp only [Finset.mem_Ico] at hk
       exact Nat.mod_eq_of_lt hk.2
     · intro k _; ext; exact Nat.mod_eq_of_lt k.isLt
     · intro k hk
       simp only [Finset.mem_Ico] at hk
       dsimp only; rw [Nat.mod_eq_of_lt hk.2]
   rw [zA,List.sum_toFinset _ xl]
lemma pI {L : ℕ} (n lo : ℕ) (g : ℕ -> Polynomial (ZMod 2))
   (f : Fin n -> Fin L -> Bool) (hf : ∀ k : Fin n,dD L (g k.val) (f k)) :
   dD L (BirdDet.sumFrom n lo g) (gy n lo f) := by
 rw [jS]
 have h := ky ((List.finRange n).filter (fun k => decide (lo ≤ k.val)))
   (fun k => g k.val) f (fun k _ => hf k) 0 (nk L) (rI L)
 unfold gy
 simpa only [zero_add] using h
def bn (n L : ℕ) (act : Fin (ae n).length -> Bool)
   (deg : Fin (ae n).length -> ℕ) : Fin n -> Fin n -> Fin L -> Bool :=
 fun i j r =>
   if i = j then decide (r.val = 0)
   else ((List.finRange (ae n).length).filter (fun idx =>
     act idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
     decide (r.val = deg idx))).length % 2 == 1
lemma il (n L : ℕ)
   (act : Fin (ae n).length -> Bool) (deg : Fin (ae n).length -> ℕ)
   (i j : Fin n) :
   dD L (bG n act deg i j) (bn n L act deg i j) := by
 intro r
 unfold bn
 by_cases hij : i = j
 · subst hij
   rw [if_pos rfl,oB,Polynomial.coeff_one]
   by_cases hr : r.val = 0 <;> simp [hr]
 · rw [if_neg hij]
   simp only [bG,if_neg hij]
   have hsum : (∑ idx : Fin (ae n).length,
       if act idx && ((aa idx == (i,j)) || (aa idx == (j,i)))
       then Polynomial.monomial (deg idx) (1 : ZMod 2) else 0).coeff r.val =
       ((List.finRange (ae n).length).map (fun idx =>
         if act idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
           decide (r.val = deg idx)
         then (1 : ZMod 2) else 0)).sum := by
     rw [jz]
     have hterm : ∀ idx : Fin (ae n).length,
         (if act idx && ((aa idx == (i,j)) || (aa idx == (j,i)))
           then Polynomial.monomial (deg idx) (1 : ZMod 2) else 0).coeff r.val =
         if act idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
           decide (r.val = deg idx)
         then (1 : ZMod 2) else 0 := by
       intro idx
       by_cases hc : act idx && ((aa idx == (i,j)) || (aa idx == (j,i)))
       · simp only [hc,↓reduceIte,Bool.true_and,Polynomial.coeff_monomial]
         by_cases hdeq : deg idx = r.val
         · simp [hdeq]
         · simp [hdeq,Ne.symm hdeq]
       · have hf : (act idx && ((aa idx == (i,j)) || (aa idx == (j,i)))) = false :=
           Bool.eq_false_iff.mpr hc
         simp [hf]
     simp_rw [hterm]
     rw [← List.toFinset_finRange,List.sum_toFinset _ (List.nodup_finRange _)]
   rw [hsum,fd]
   have hflt : (List.finRange (ae n).length).filter (fun x =>
       decide ((if act x && ((aa x == (i,j)) || (aa x == (j,i))) &&
         decide (r.val = deg x) then (1 : ZMod 2) else 0) = 1)) =
       (List.finRange (ae n).length).filter (fun idx =>
         act idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
         decide (r.val = deg idx)) := by
     congr 1
     ext idx
     by_cases hc : act idx && ((aa idx == (i,j)) || (aa idx == (j,i))) && decide (r.val = deg idx)
     · simp [hc]
     · have hf : (act idx && ((aa idx == (i,j)) || (aa idx == (j,i))) && decide (r.val = deg idx)) = false :=
         Bool.eq_false_iff.mpr hc
       simp [hf]
   rw [hflt]
def dm (n L : ℕ) (A F : Fin n -> Fin n -> Fin L -> Bool) :
   Fin n -> Fin n -> Fin L -> Bool :=
 fun i j =>
   let tR := gy n (i.val + 1) (fun k => F k k)
   let t1 := cI tR (A i j)
   let t2 := gy n (i.val + 1) (fun k => cI (F i k) (A k j))
   fc t1 t2
def dt (n L : ℕ) (A : Fin n -> Fin n -> Fin L -> Bool) : Fin L -> Bool :=
 if hn : 0 < n then ((dm n L A)^[n - 1] A) ⟨0,hn⟩ ⟨0,hn⟩ else nk L
lemma iD {n L : ℕ} (hn : 2 ≤ n)
   (act : Fin (ae n).length -> Bool) (deg : Fin (ae n).length -> ℕ) :
   dD L (bG n act deg).det (dt n L (bn n L act deg)) := by
 let nP := bG n act deg
 let dE := nP.toArray
 have qw : dE.size = n * n := Matrix.size_toArray nP
 have Aq : Matrix.ofArray dE qw = nP := Matrix.ofArray_toArray nP
 have v9 : nP.det = BirdDet.birdDet n dE := by
   conv_lhs => rw [← Aq]
   exact BirdDet.det_eq_birdDet dE qw
 have sJ : 0 < n := by omega
 have hsucc : n = (n - 1) + 1 := by omega
 have uc : BirdDet.birdDet n dE =
     (BirdDet.stepEntry n dE)^[n - 1] (BirdDet.get n dE) 0 0 := by
   conv_lhs => rw [hsucc]
   rw [BirdDet.birdDet_succ,← hsucc]
   have hm1 : (-1 : Polynomial (ZMod 2)) = 1 := CharTwo.neg_eq 1
   simp [hm1]
 have qO : ∀ i j : Fin n,BirdDet.get n dE i.val j.val = nP i j := by
   intro i j
   rw [BirdDet.get_eq]
   have hlt : n * i.val + j.val < dE.size := by
     rw [qw]
     have hi := i.isLt
     have hj := j.isLt
     nlinarith
   have xX : dE.getD (n * i.val + j.val) 0 = dE[i.mkDivMod j] := by
     rw [Array.getD,dif_pos hlt]
     rfl
   rw [xX]
   exact congrArg (fun M : Matrix (Fin n) (Fin n) (Polynomial (ZMod 2)) => M i j) Aq
 let en := bn n L act deg
 have hstep : ∀ t (i j : Fin n),
     dD L ((BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) i.val j.val)
       (((dm n L en)^[t] en) i j) := by
   intro t
   induction t with
   | zero =>
     intro i j
     simp only [Function.iterate_zero,id_eq,qO]
     exact il n L act deg i j
   | succ t ih =>
     intro i j
     simp only [Function.iterate_succ_apply']
     rw [BirdDet.stepEntry_eq]
     have hneg : (-BirdDet.sumFrom n (i.val + 1) fun k =>
         (BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) k k) =
         BirdDet.sumFrom n (i.val + 1) fun k =>
         (BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) k k :=
       CharTwo.neg_eq _
     rw [hneg,qO i j]
     have vB : dD L
         (BirdDet.sumFrom n (i.val + 1) fun k =>
           (BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) k k)
         (gy n (i.val + 1) fun k => ((dm n L en)^[t] en) k k) :=
       pI n (i.val + 1) _ _ (fun k => ih k k)
     have w6 : dD L (nP i j) (en i j) := il n L act deg i j
     have hv1 : dD L
         ((BirdDet.sumFrom n (i.val + 1) fun k =>
           (BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) k k) * nP i j)
         (cI (gy n (i.val + 1) fun k => ((dm n L en)^[t] en) k k) (en i j)) :=
       kN vB w6
     have wu : ∀ k : Fin n,
         dD L
           ((BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) i.val k.val * BirdDet.get n dE k.val j.val)
           (cI (((dm n L en)^[t] en) i k) (en k j)) := by
       intro k
       rw [qO k j]
       exact kN (ih i k) (il n L act deg k j)
     have hv2 : dD L
         (BirdDet.sumFrom n (i.val + 1) fun k =>
           (BirdDet.stepEntry n dE)^[t] (BirdDet.get n dE) i.val k * BirdDet.get n dE k j.val)
         (gy n (i.val + 1) fun k => cI (((dm n L en)^[t] en) i k) (en k j)) :=
       pI n (i.val + 1) _ _ wu
     exact kR hv1 hv2
 rw [v9,uc]
 unfold dt
 rw [dif_pos sJ]
 exact hstep (n - 1) ⟨0,sJ⟩ ⟨0,sJ⟩
end Det
section Alg
open aK aK.Machines aK.Universal aK.R aK.Loop
lemma lZ {v : List ℕ} {i : ℕ} :
   v.getD i 0 ≤ (aM v).length := by
 rw [nN]
 have hle : v.getD i 0 ≤ v.sum := by
   induction v generalizing i with
   | nil => simp
   | cons a v ih =>
     cases i with
     | zero => simp
     | succ i =>
       simp only [List.getD_cons_succ,List.sum_cons]
       exact (ih).trans (Nat.le_add_left _ _)
 omega
lemma ke {v : List ℕ} (hv : ∀ x ∈ v,x ≤ 1) :
   (aM v).length ≤ 2 * v.length := by
 rw [nN]
 have hsum : v.sum ≤ v.length := by
   induction v with
   | nil => simp
   | cons a v ih =>
     simp only [List.sum_cons,List.length_cons]
     have ha : a ≤ 1 := hv a (List.mem_cons_self ..)
     have hv' : ∀ x ∈ v,x ≤ 1 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
     have := ih hv'
     omega
 omega
lemma aH {f : List Bool -> ℕ} {g : List Bool -> List Bool}
   (hg : aK.CPTs g) (hf : aj f) : aj (fun t => f (g t)) :=
 cpt_comp (g := fun x => un (f x)) hg hf
lemma iA {f : List Bool -> List ℕ} {g : List Bool -> List Bool}
   (hg : aK.CPTs g) (hf : cX f) : cX (fun t => f (g t)) :=
 cpt_comp (g := fun x => aM (f x)) hg hf
lemma av : aj (fun t => (unpairB t).1.length) := jq
lemma kX {f : List Bool -> ℕ} (hf : aj f) :
   aj (fun t => f (unpairB t).2) := ox hf
lemma kQ {f g : List Bool -> List Bool} (hf : aK.CPTs f) (hg : aK.CPTs g) :
   aK.CPTs (fun t => g (f t)) :=
 cpt_comp (f := f) (g := g) hf hg
lemma dK {f : List Bool -> List Bool} (hf : aK.CPTs f) :
   aK.CPTs (fun t => (unpairB (f t)).1) :=
 cpt_unpairB1_1 hf
lemma ad {f : List Bool -> List Bool} (hf : aK.CPTs f) :
   aK.CPTs (fun t => (unpairB (f t)).2) :=
 cpt_unpairB2_1 hf
lemma aq {f : List Bool -> List Bool} (hf : aK.CPTs f) :
   aj (fun t => (unpairB (f t)).1.length) :=
 aH (g := f) hf av
lemma nV {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) :
   aj (fun s => if a s < b s then 1 else 0) :=
 og ha hb (ac 1) (ac 0)
lemma bE {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) :
   aj (fun s => if a s = b s then 1 else 0) :=
 qV ha hb (ac 1) (ac 0)
lemma nM {a b : List Bool -> ℕ} (ha : aj a) (hb : aj b) :
   aj (fun s => if a s ≤ b s then 1 else 0) :=
 cptE (nV ha (af hb (ac 1))) (fun s => by
   dsimp only
   by_cases h : a s ≤ b s
   · have : a s < b s + 1 := by omega
     simp [h,this]
   · have : ¬ (a s < b s + 1) := by omega
     simp [h,this])
lemma gZ {a b x y : List Bool -> ℕ} (ha : aj a) (hb : aj b)
   (hx : aj x) (hy : aj y) : aj (fun s => if a s ≤ b s then x s else y s) :=
 cptE (og ha (af hb (ac 1)) hx hy) (fun s => by
   dsimp only
   by_cases h : a s ≤ b s <;> simp [h,Nat.lt_succ_iff])
lemma cH {a b x y : List Bool -> ℕ} (ha : aj a) (hb : aj b)
   (hx : aj x) (hy : aj y) : aj (fun s => if a s = b s then x s else y s) :=
 qV ha hb hx hy
lemma sf {a b : List Bool -> ℕ} {x y : List Bool -> List ℕ}
   (ha : aj a) (hb : aj b) (hx : cX x) (hy : cX y) :
   cX (fun s => if a s < b s then x s else y s) :=
 cptE (sZ ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
lemma kM {a b : List Bool -> ℕ} {x y : List Bool -> List ℕ}
   (ha : aj a) (hb : aj b) (hx : cX x) (hy : cX y) :
   cX (fun s => if a s = b s then x s else y s) :=
 cptE (sS ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
lemma eU (k : ℕ) (rest : List Bool) :
   ((List.replicate k true ++ [false] ++ rest).takeWhile id).length = k := by
 induction k with
 | zero => simp
 | succ k ih =>
   simp only [List.replicate_succ,List.cons_append,List.takeWhile_cons,id_eq,↓reduceIte,
     List.length_cons,ih]
lemma i6 (k : ℕ) (rest : List Bool) :
   (List.replicate k true ++ [false] ++ rest).drop (k + 1) = rest := by
 induction k with
 | zero => simp
 | succ k ih =>
   simpa [List.replicate_succ,List.cons_append,add_assoc] using ih
def lG (s : List Bool) (k : ℕ) : ℕ :=
 ((s.drop k).takeWhile id).length
lemma uL (s : List Bool) (k : ℕ) : lG s k ≤ s.length := by
 unfold lG
 have h1 : ((s.drop k).takeWhile id).length ≤ (s.drop k).length := by
   exact List.IsPrefix.length_le (List.takeWhile_prefix _)
 have h2 : (s.drop k).length ≤ s.length := by simp
 omega
def ur (s : List Bool) : ℕ := lG s 0
def g8 (s : List Bool) : ℕ := lG s (ur s + 1)
def iH (s : List Bool) : ℕ := lG s (ur s + 1 + g8 s + 1)
def bq (s : List Bool) : ℕ := ur s + 1 + g8 s + 1 + iH s + 1
def bL (s : List Bool) : ℕ := bq s + iH s * (2 * g8 s)
def ro (s : List Bool) : ℕ := lG s (bL s)
def bi (s : List Bool) : ℕ := bL s + ro s + 1
def ef (s : List Bool) : ℕ := bi s + ro s * (2 * g8 s + 1)
lemma kE : aj ur := jY cpt_id (ac 0)
lemma bC : aj g8 := jY cpt_id (af kE (ac 1))
lemma iY : aj iH :=
 jY cpt_id (af (af (af kE (ac 1)) bC) (ac 1))
lemma iU : aj bq :=
 af (af (af (af (af kE (ac 1)) bC)
   (ac 1)) iY) (ac 1)
lemma i7 : aj bL :=
 af iU (ag iY (ag (ac 2) bC))
lemma f9 : aj ro := jY cpt_id i7
lemma gh : aj bi :=
 af (af i7 f9) (ac 1)
lemma qN : aj ef :=
 af gh (ag f9 (af (ag (ac 2) bC) (ac 1)))
def sW (s : List Bool) : ℕ := g8 s * (g8 s - 1) / 2
def ow (s : List Bool) : ℕ := 2 * ((g8 s).log2 + 1) + 1
def ui (s : List Bool) : ℕ := 2 ^ ow s
def iz (s : List Bool) : ℕ := g8 s * ui s + 1
def lN (s : List Bool) : ℕ := iz s * (2 * ro s + 1) + ui s
def am (s : List Bool) : ℕ := 2 * (g8 s * lN s + iz s) + 1
def s7 (s : List Bool) : ℕ := ur s + g8 s + ro s + 2
lemma pz : aj sW :=
 di (ag bC (dj bC (ac 1))) (ac 2)
lemma rY : aj ow :=
 af (ag (ac 2) (af (tU bC) (ac 1))) (ac 1)
lemma oJ : aj ui := by
 refine tZ rY (Polynomial.C 8 * (Polynomial.X + Polynomial.C 1) ^ 2) (fun s => ?_)
 have hn : g8 s ≤ s.length := uL s _
 have hlog : 2 ^ ((g8 s).log2 + 1) ≤ 2 * (g8 s + 1) := by
   rcases Nat.eq_zero_or_pos (g8 s) with h0 | hpos
   · simp [h0]
   · have := Nat.pow_log_le_self 2 hpos.ne'
     rw [← Nat.log2_eq_log_two] at this
     rw [pow_succ']
     omega
 have hpow : 2 ^ ow s = 2 * (2 ^ ((g8 s).log2 + 1)) ^ 2 := by
   dsimp [ow]
   rw [pow_add,mul_comm 2 _,pow_mul]
   ring
 have wV : 2 ^ ((g8 s).log2 + 1) ≤ 2 * (s.length + 1) := hlog.trans (by omega)
 have hsq : (2 ^ ((g8 s).log2 + 1)) ^ 2 ≤ 4 * (s.length + 1) ^ 2 := by
   have := Nat.mul_le_mul wV wV
   linarith
 simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
   Polynomial.eval_X]
 nlinarith
lemma oA : aj iz := af (ag bC oJ) (ac 1)
lemma nF : aj lN :=
 af (ag oA (af (ag (ac 2) f9) (ac 1))) oJ
lemma ru : aj am :=
 af (ag (ac 2) (af (ag bC nF) oA)) (ac 1)
lemma rD : aj s7 :=
 af (af (af kE bC) f9) (ac 2)
def dR (s : List Bool) : List ℕ :=
 (List.range (g8 s)).flatMap (fun i =>
   (List.range (g8 s)).flatMap (fun j => if i < j then [i,j] else []))
lemma kF : cX dR := by
 unfold dR
 refine fI cpt_id bC ?_
 refine fI cpt_id (kX bC) ?_
 refine sf (kX av) av
   (aR (aN (kX av)) (aN av))
   oO
def bitAt (s : List Bool) (k : ℕ) : ℕ :=
 if s.getD k false then 1 else 0
def aU (s : List Bool) : List Bool := pairB s (aM (dR s))
lemma kK : aK.CPTs aU := cpt_pairB2 cpt_id kF
def fQ (z : ℕ) (t : List Bool) : ℕ :=
 let s' := (unpairB (unpairB t).2).1
 let pf := iS (unpairB (unpairB t).2).2
 let idx := (unpairB t).1.length
 let u := pf.getD (2 * idx) 0
 let v := pf.getD (2 * idx + 1) 0
 let off := bq s' + z * (2 * g8 s')
 let vg := bitAt s' (off + u) * bitAt s' (off + v)
 let vD := bitAt s' (off + g8 s' + u) * bitAt s' (off + g8 s' + v)
 if vg + vD = 0 then 0 else 1
lemma oP : aj (fun t2 => fQ (unpairB t2).1.length (unpairB t2).2) := by
 unfold fQ
 have ht2 : aK.CPTs (fun t2 : List Bool => (unpairB t2).2) := cpt_unpairB2
 have hs2 : aK.CPTs (fun t2 : List Bool => (unpairB (unpairB (unpairB t2).2).2).1) :=
   dK (ad ht2)
 have sj : cX (fun t2 : List Bool => iS (unpairB (unpairB (unpairB t2).2).2).2) :=
   dO (ad (ad ht2))
 have nH := aq ht2
 have hu2 := bt sj (ag (ac 2) nH)
 have hv2 := bt sj (af (ag (ac 2) nH) (ac 1))
 have hn2 := aH hs2 bC
 have hoff := af (aH hs2 iU)
   (ag av (ag (ac 2) hn2))
 have sd := ag (bO hs2 (af hoff hu2)) (bO hs2 (af hoff hv2))
 have ry := ag
   (bO hs2 (af (af hoff hn2) hu2))
   (bO hs2 (af (af hoff hn2) hv2))
 exact cH (af sd ry) (ac 0) (ac 0) (ac 1)
def iL (idx : ℕ) (env : List Bool) : ℕ :=
 let s' := (unpairB env).1
 let bad := ((List.range (iH s')).map (fun z => fQ z (pairB (un idx) env))).sum
 if bad = 0 then 1 else 0
lemma n8 : aj (fun t => iL (unpairB t).1.length (unpairB t).2) := by
 unfold iL
 have hs := dK cpt_unpairB2
 have hsum := bU (aV (cpt_pairB2 av cpt_unpairB2) (aH hs iY) oP)
 have hbad : aj (fun t =>
     ((List.range (iH (unpairB (unpairB t).2).1)).map
       (fun z => fQ z (pairB (un (unpairB t).1.length) (unpairB t).2))).sum) :=
   cptE hsum (fun t => rfl)
 exact cH hbad (ac 0) (ac 1) (ac 0)
def bD (s : List Bool) : List ℕ :=
 (List.range (sW s)).map (fun idx => iL idx (aU s))
lemma pL : cX bD :=
 aV kK pz n8
def eY (i : ℕ) (arg : List Bool) : ℕ :=
 let s' := (unpairB arg).2
 let yu := (unpairB arg).1.length
 bitAt s' (yu + i) * bitAt s' (yu + g8 s' + i)
lemma mw : aj (fun t2 => eY (unpairB t2).1.length (unpairB t2).2) := by
 unfold eY
 have hs2 := ad cpt_unpairB2
 have tF := kX av
 have hn2 := aH hs2 bC
 exact ag
   (bO hs2 (af tF av))
   (bO hs2 (af (af tF hn2) av))
def gf (s : List Bool) (off : ℕ) : ℕ :=
 let overlap := ((List.range (g8 s)).map (fun i => eY i (pairB (un off) s))).sum
 if overlap = 0 then 1 else 0
lemma gY {fs : List Bool -> List Bool} {xM : List Bool -> ℕ}
   (wY : aK.CPTs fs) (wc : aj xM) :
   aj (fun t => gf (fs t) (xM t)) := by
 unfold gf
 have harg : aK.CPTs (fun t => pairB (un (xM t)) (fs t)) := cpt_pairB2 wc wY
 have yi := bU (aV harg (aH wY bC) mw)
 exact cH yi (ac 0) (ac 1) (ac 0)
def eO (z : ℕ) (t : List Bool) : ℕ :=
 let s' := (unpairB (unpairB t).2).1
 let pf := iS (unpairB (unpairB t).2).2
 let idx := (unpairB t).1.length
 let u := pf.getD (2 * idx) 0
 let v := pf.getD (2 * idx + 1) 0
 let off := bi s' + z * (2 * g8 s' + 1)
 let vg := bitAt s' (off + u) * bitAt s' (off + v)
 let vD := bitAt s' (off + g8 s' + u) * bitAt s' (off + g8 s' + v)
 let lab := bitAt s' (off + 2 * g8 s')
 if gf s' off * (vg + vD) * lab = 0 then 0 else 1
def eo (z : ℕ) (t : List Bool) : ℕ :=
 let s' := (unpairB (unpairB t).2).1
 let pf := iS (unpairB (unpairB t).2).2
 let idx := (unpairB t).1.length
 let u := pf.getD (2 * idx) 0
 let v := pf.getD (2 * idx + 1) 0
 let off := bi s' + z * (2 * g8 s' + 1)
 let vg := bitAt s' (off + u) * bitAt s' (off + v)
 let vD := bitAt s' (off + g8 s' + u) * bitAt s' (off + g8 s' + v)
 let lab := bitAt s' (off + 2 * g8 s')
 if gf s' off * (vg + vD) * (1 - lab) = 0 then 0 else 1
lemma mT : aj (fun t2 => eO (unpairB t2).1.length (unpairB t2).2) := by
 unfold eO
 have ht2 : aK.CPTs (fun t2 : List Bool => (unpairB t2).2) := cpt_unpairB2
 have hs2 : aK.CPTs (fun t2 : List Bool => (unpairB (unpairB (unpairB t2).2).2).1) :=
   dK (ad ht2)
 have sj : cX (fun t2 : List Bool => iS (unpairB (unpairB (unpairB t2).2).2).2) :=
   dO (ad (ad ht2))
 have nH := aq ht2
 have hu2 := bt sj (ag (ac 2) nH)
 have hv2 := bt sj (af (ag (ac 2) nH) (ac 1))
 have hn2 := aH hs2 bC
 have hoff := af (aH hs2 gh)
   (ag av (af (ag (ac 2) hn2) (ac 1)))
 have hdisj := gY hs2 hoff
 have sd := ag (bO hs2 (af hoff hu2)) (bO hs2 (af hoff hv2))
 have ry := ag
   (bO hs2 (af (af hoff hn2) hu2))
   (bO hs2 (af (af hoff hn2) hv2))
 have hlab := bO hs2 (af hoff (ag (ac 2) hn2))
 exact cH (ag (ag hdisj (af sd ry)) hlab)
   (ac 0) (ac 0) (ac 1)
lemma nl : aj (fun t2 => eo (unpairB t2).1.length (unpairB t2).2) := by
 unfold eo
 have ht2 : aK.CPTs (fun t2 : List Bool => (unpairB t2).2) := cpt_unpairB2
 have hs2 : aK.CPTs (fun t2 : List Bool => (unpairB (unpairB (unpairB t2).2).2).1) :=
   dK (ad ht2)
 have sj : cX (fun t2 : List Bool => iS (unpairB (unpairB (unpairB t2).2).2).2) :=
   dO (ad (ad ht2))
 have nH := aq ht2
 have hu2 := bt sj (ag (ac 2) nH)
 have hv2 := bt sj (af (ag (ac 2) nH) (ac 1))
 have hn2 := aH hs2 bC
 have hoff := af (aH hs2 gh)
   (ag av (af (ag (ac 2) hn2) (ac 1)))
 have hdisj := gY hs2 hoff
 have sd := ag (bO hs2 (af hoff hu2)) (bO hs2 (af hoff hv2))
 have ry := ag
   (bO hs2 (af (af hoff hn2) hu2))
   (bO hs2 (af (af hoff hn2) hv2))
 have hlab := bO hs2 (af hoff (ag (ac 2) hn2))
 exact cH (ag (ag hdisj (af sd ry)) (dj (ac 1) hlab))
   (ac 0) (ac 0) (ac 1)
def k9 (idx : ℕ) (env : List Bool) : ℕ :=
 let s' := (unpairB env).1
 let pos := ((List.range (ro s')).map (fun z => eO z (pairB (un idx) env))).sum
 let neg := ((List.range (ro s')).map (fun z => eo z (pairB (un idx) env))).sum
 ro s' + 1 + pos - neg
lemma po : aj (fun t => k9 (unpairB t).1.length (unpairB t).2) := by
 unfold k9
 have hs := dK cpt_unpairB2
 have harg : aK.CPTs (fun t => pairB (un (unpairB t).1.length) (unpairB t).2) :=
   cpt_pairB2 av cpt_unpairB2
 have hpos := bU (aV harg (aH hs f9) mT)
 have hneg := bU (aV harg (aH hs f9) nl)
 exact dj (af (af (aH hs f9) (ac 1)) hpos) hneg
def eP (s : List Bool) : List ℕ :=
 (List.range (sW s)).map (fun idx => k9 idx (aU s))
lemma rn : cX eP :=
 aV kK pz po
def fM (z : ℕ) (s : List Bool) : ℕ :=
 let off := bi s + z * (2 * g8 s + 1)
 let lab := bitAt s (off + 2 * g8 s)
 if gf s off + lab = 1 then 1 else 0
lemma mZ : aj (fun t => fM (unpairB t).1.length (unpairB t).2) := by
 unfold fM
 have hs := cpt_unpairB2
 have hn := aH hs bC
 have hoff := af (aH hs gh)
   (ag av (af (ag (ac 2) hn) (ac 1)))
 exact cH (af (gY hs hoff) (bO hs (af hoff (ag (ac 2) hn))))
   (ac 1) (ac 1) (ac 0)
def eT (s : List Bool) : ℕ :=
 ((List.range (ro s)).map (fun z => fM z s)).sum
lemma rm : aj eT :=
 bU (aV cpt_id f9 mZ)
def eg (s : List Bool) : List ℕ :=
 [ur s,g8 s,iH s,ro s,ef s,sW s,ow s,ui s,iz s,lN s,am s,s7 s,eT s]
   ++ dR s ++ bD s ++ eP s
lemma qD : cX eg := by
 unfold eg
 refine aR (aR (aR ?_ kF) pL) rn
 exact aR (aN kE) (aR (aN bC)
   (aR (aN iY) (aR (aN f9)
   (aR (aN qN) (aR (aN pz)
   (aR (aN rY) (aR (aN oJ)
   (aR (aN oA) (aR (aN nF)
   (aR (aN ru) (aR (aN rD)
     (aN rm))))))))))))
def aE (s : List Bool) : List Bool := pairB s (aM (eg s))
lemma ma : aK.CPTs aE := cpt_pairB2 cpt_id qD
def mS (env : List Bool) : List Bool := (unpairB env).1
def eM (env : List Bool) : List ℕ := iS (unpairB env).2
def mN (env : List Bool) : ℕ := (eM env).getD 1 0
def o9 (env : List Bool) : ℕ := (eM env).getD 4 0
def mP (env : List Bool) : ℕ := (eM env).getD 5 0
def mb (env : List Bool) : ℕ := (eM env).getD 6 0
def mB (env : List Bool) : ℕ := (eM env).getD 8 0
def ez (env : List Bool) : ℕ := (eM env).getD 10 0
def mR (env : List Bool) : ℕ := (eM env).getD 11 0
def qg (env : List Bool) : ℕ := (eM env).getD 12 0
def mM (env : List Bool) : ℕ := (eM env).getD 3 0
def mU (env : List Bool) (idx : ℕ) : ℕ := (eM env).getD (13 + 2 * idx) 0
def mV (env : List Bool) (idx : ℕ) : ℕ := (eM env).getD (13 + 2 * idx + 1) 0
def qo (env : List Bool) (idx : ℕ) : ℕ := (eM env).getD (13 + 2 * mP env + idx) 0
def mC (env : List Bool) (idx : ℕ) : ℕ := (eM env).getD (13 + 3 * mP env + idx) 0
lemma uS : aK.CPTs mS := cpt_unpairB1
lemma iI : cX eM := dO cpt_unpairB2
lemma dw (k : List Bool -> ℕ) (hk : aj k) :
   aj (fun env => (eM env).getD (k env) 0) :=
 bt iI hk
def rV (env : List Bool) : ℕ := (eM env).getD 7 0
lemma fy {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => mN (f t)) :=
 aH hf (dw _ (ac 1))
lemma oi {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => mM (f t)) :=
 aH hf (dw _ (ac 3))
lemma se {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => o9 (f t)) :=
 aH hf (dw _ (ac 4))
lemma fz {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => mP (f t)) :=
 aH hf (dw _ (ac 5))
lemma vR {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => mb (f t)) :=
 aH hf (dw _ (ac 6))
lemma sR {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => rV (f t)) :=
 aH hf (dw _ (ac 7))
lemma ou {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => mB (f t)) :=
 aH hf (dw _ (ac 8))
lemma bX {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => ez (f t)) :=
 aH hf (dw _ (ac 10))
lemma wx {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => mR (f t)) :=
 aH hf (dw _ (ac 11))
lemma lQ {f : List Bool -> List Bool} (hf : aK.CPTs f) : aj (fun t => qg (f t)) :=
 aH hf (dw _ (ac 12))
lemma tw {f : List Bool -> List Bool} {k : List Bool -> ℕ} (hf : aK.CPTs f) (hk : aj k) :
   aj (fun t => mU (f t) (k t)) :=
 bt (iA hf iI) (af (ac 13) (ag (ac 2) hk))
lemma td {f : List Bool -> List Bool} {k : List Bool -> ℕ} (hf : aK.CPTs f) (hk : aj k) :
   aj (fun t => mV (f t) (k t)) :=
 bt (iA hf iI) (af (af (ac 13) (ag (ac 2) hk)) (ac 1))
lemma oS {f : List Bool -> List Bool} {k : List Bool -> ℕ} (hf : aK.CPTs f) (hk : aj k) :
   aj (fun t => qo (f t) (k t)) :=
 bt (iA hf iI) (af (af (ac 13) (ag (ac 2) (fz hf))) hk)
lemma tP {f : List Bool -> List Bool} {k : List Bool -> ℕ} (hf : aK.CPTs f) (hk : aj k) :
   aj (fun t => mC (f t) (k t)) :=
 bt (iA hf iI) (af (af (ac 13) (ag (ac 3) (fz hf))) hk)
lemma kW (b : ℕ) (bits : List Bool) (base : ℕ) :
   az b bits base =
     ((List.range b).map (fun h => (if bits.getD (base + h) false then 1 else 0) * 2 ^ (b - 1 - h))).sum := by
 induction b with
 | zero => simp [az]
 | succ b ih =>
   unfold az at ih ⊢
   rw [List.range_succ,List.foldl_append,List.map_append,List.sum_append]
   dsimp only [List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,List.sum_cons,
     List.sum_nil]
   rw [ih]
   have hmul : 2 * ((List.range b).map (fun h =>
       (if bits.getD (base + h) false then 1 else 0) * 2 ^ (b - 1 - h))).sum =
       ((List.range b).map (fun h =>
       (if bits.getD (base + h) false then 1 else 0) * 2 ^ (b + 1 - 1 - h))).sum := by
     have hmap : ∀ l : List ℕ,(∀ h ∈ l,h < b) ->
         2 * (l.map (fun h => (if bits.getD (base + h) false then 1 else 0) * 2 ^ (b - 1 - h))).sum =
         (l.map (fun h => (if bits.getD (base + h) false then 1 else 0) * 2 ^ (b + 1 - 1 - h))).sum := by
       intro l hl
       induction l with
       | nil => simp
       | cons x xs ihx =>
         have hx : x < b := hl x (List.mem_cons_self ..)
         have hpow : 2 * 2 ^ (b - 1 - x) = 2 ^ (b + 1 - 1 - x) := by
           rw [← pow_succ']; congr 1; omega
         simp only [List.map_cons,List.sum_cons,mul_add,ihx (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
         rw [← mul_assoc,mul_comm 2 _,mul_assoc,hpow]
     exact hmap (List.range b) (fun h hh => List.mem_range.mp hh)
   rw [hmul]
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
     Nat.add_sub_cancel,Nat.sub_self,pow_zero,mul_one]
lemma lC (b U B : ℕ) (hU : U = 2 ^ b) (s' : List Bool) (off c : ℕ) :
   B * c + ((List.range b).map (fun h =>
     bitAt s' (off + h) * (U / 2 ^ (h + 1)))).sum =
   B * c + az b s' off := by
 congr 1
 rw [kW]
 congr 1
 apply List.map_congr_left
 intro h hh
 have hlt : h < b := List.mem_range.mp hh
 have hpow : U / 2 ^ (h + 1) = 2 ^ (b - 1 - h) := by
   rw [hU,Nat.pow_div (by omega) (by decide)]
   congr 1; omega
 simp [bitAt,hpow]
def ir (h : ℕ) (arg : List Bool) : ℕ :=
 let off := (unpairB arg).1.length
 let env := (unpairB arg).2
 bitAt (mS env) (off + h) * (rV env / 2 ^ (h + 1))
lemma mz : aj (fun t2 => ir (unpairB t2).1.length (unpairB t2).2) := by
 unfold ir
 have wP := ad cpt_unpairB2
 have tF := aq cpt_unpairB2
 have hU2 := sR wP
 have hpow := qp hU2 (af av (ac 1))
 exact ag (bO (kQ wP uS) (af tF av)) hpow
def kP (t idx : ℕ) (env : List Bool) : ℕ :=
 let y5 := o9 env
 let P := mP env
 let b := mb env
 let B := mB env
 let c := mC env idx
 let off := y5 + (t * P + idx) * b
 let u := ((List.range b).map (fun h => ir h (pairB (un off) env))).sum
 B * c + u
lemma nW (t idx : ℕ) (env : List Bool) :
   kP t idx env =
     mB env * mC env idx +
     ((List.range (mb env)).map (fun h =>
       bitAt (mS env) (o9 env + (t * mP env + idx) * mb env + h) * (rV env / 2 ^ (h + 1)))).sum := by
 simp [kP,ir,unpairB_pairB,un_length]
lemma pP :
   aj (fun iK =>
     let idx := (unpairB iK).1.length
     let t := (unpairB (unpairB iK).2).1.length
     let env := (unpairB (unpairB iK).2).2
     kP t idx env) := by
 unfold kP
 have henv := ad cpt_unpairB2
 have ht := aq cpt_unpairB2
 have hidx := av
 have hB := ou henv
 have hP := fz henv
 have hc' := tP henv hidx
 have hb := vR henv
 have xt := se henv
 have hoff := af xt (ag (af (ag ht hP) hidx) hb)
 have harg := cpt_pairB2 hoff henv
 have xA := bU (aV harg hb mz)
 exact af (ag hB hc') xA
lemma io (w : List Bool) (k : ℕ) :
   (iS w).getD k 0 ≤ w.length := by
 have h1 := lZ (v := iS w) (i := k)
 rw [uH] at h1
 exact h1.trans (List.IsSuffix.length_le (List.dropWhile_suffix _))
def bF (t : ℕ) (env : List Bool) : List ℕ :=
 (List.range (mP env)).map (fun idx => kP t idx env)
lemma rH :
   cX (fun eL => bF (unpairB eL).1.length (unpairB eL).2) :=
 aV cpt_id (fz cpt_unpairB2) pP
def dH (idx : ℕ) (z : List Bool) : ℕ :=
 let fD := (unpairB z).2
 let dv := iS (unpairB fD).1
 let aI := (unpairB (unpairB fD).2).1.length
 let env := (unpairB (unpairB fD).2).2
 let n := mN env
 let L := ez env
 let pJ := (unpairB z).1.length % (n * L)
 let i := (unpairB z).1.length / (n * L)
 let j := pJ / L
 let r := pJ % L
 let act := if idx = aI then 0 else qo env idx
 let u := mU env idx
 let v := mV env idx
 let hit := if (if u = i then 1 else 0) * (if v = j then 1 else 0) +
               (if u = j then 1 else 0) * (if v = i then 1 else 0) = 0 then 0 else 1
 let xH := if r = dv.getD idx 0 then 1 else 0
 act * hit * xH
lemma mA : aj (fun t2 => dH (unpairB t2).1.length (unpairB t2).2) := by
 unfold dH
 have hz := cpt_unpairB2
 have hidx := av
 have qr := ad hz
 have hdv := dO (dK qr)
 have qT := aH (ad qr) av
 have henv := ad (ad qr)
 have hn := fy henv
 have hL := bX henv
 have hpos := aq hz
 have hi := di hpos (ag hn hL)
 have hrem := dk hpos (ag hn hL)
 have hj := di hrem hL
 have hr := dk hrem hL
 have uP := oS henv hidx
 have uT := cH hidx qT (ac 0) uP
 have hu := tw henv hidx
 have hv := td henv hidx
 have hhit := cH
   (af (ag (bE hu hi) (bE hv hj))
             (ag (bE hu hj) (bE hv hi)))
   (ac 0) (ac 0) (ac 1)
 have hrm := bE hr (bt hdv hidx)
 exact ag (ag uT hhit) hrm
def gU (pos : ℕ) (fD : List Bool) : ℕ :=
 let env := (unpairB (unpairB fD).2).2
 let n := mN env
 let P := mP env
 let L := ez env
 let i := pos / (n * L)
 let pJ := pos % (n * L)
 let j := pJ / L
 let r := pJ % L
 if i = j then if r = 0 then 1 else 0
 else ((List.range P).map (fun idx => dH idx (pairB (un pos) fD))).sum % 2
lemma lO :
   aj (fun lH => gU (unpairB lH).1.length (unpairB lH).2) := by
 unfold gU
 have qr := cpt_unpairB2
 have henv := ad (ad qr)
 have hn := fy henv
 have hP := fz henv
 have hL := bX henv
 have hi := di av (ag hn hL)
 have hrem := dk av (ag hn hL)
 have hj := di hrem hL
 have hr := dk hrem hL
 have hdiag := bE hr (ac 0)
 have harg := cpt_pairB2 av qr
 have hsum := dk (bU (aV harg hP mA)) (ac 2)
 exact cH hi hj hdiag hsum
def bS (fD : List Bool) : List ℕ :=
 let env := (unpairB (unpairB fD).2).2
 (List.range (mN env * mN env * ez env)).map (fun pos => gU pos fD)
lemma ml : cX bS := by
 unfold bS
 have henv := ad (ad cpt_id)
 have hn := fy henv
 have hL := bX henv
 exact aV cpt_id (ag (ag hn hn) hL) lO
def eC (k : ℕ) (t1 : List Bool) : ℕ :=
 let q := (unpairB t1).1.length
 let z := (unpairB t1).2
 let F := iS (unpairB (unpairB z).2).1
 let env := (unpairB (unpairB (unpairB (unpairB (unpairB z).2).2).2).2).2
 let n := mN env
 let L := ez env
 let i := (unpairB z).1.length / (n * L)
 if i + 1 ≤ k then F.getD ((k * n + k) * L + q) 0 else 0
lemma lm : aj (fun t2 => eC (unpairB t2).1.length (unpairB t2).2) := by
 unfold eC
 have ht1 := cpt_unpairB2
 have hk := av
 have hq := aq ht1
 have hz := ad ht1
 have hF := dO (dK (ad hz))
 have henv := ad (ad (ad (ad (ad hz))))
 have hn := fy henv
 have hL := bX henv
 have hi := di (aq hz) (ag hn hL)
 exact gZ (af hi (ac 1)) hk
   (bt hF (af (ag (af (ag hk hn) hk) hL) hq))
   (ac 0)
def cJ (q : ℕ) (z : List Bool) : ℕ :=
 let A := iS (unpairB (unpairB (unpairB z).2).2).1
 let env := (unpairB (unpairB (unpairB (unpairB (unpairB z).2).2).2).2).2
 let n := mN env
 let L := ez env
 let i := (unpairB z).1.length / (n * L)
 let pJ := (unpairB z).1.length % (n * L)
 let j := pJ / L
 let r := pJ % L
 if q ≤ r then
   (((List.range n).map (fun k => eC k (pairB (un q) z))).sum % 2) *
   A.getD ((i * n + j) * L + (r - q)) 0
 else 0
lemma lr : aj (fun t1 => cJ (unpairB t1).1.length (unpairB t1).2) := by
 unfold cJ
 have hz := cpt_unpairB2
 have hq := av
 have hA := dO (dK (ad (ad hz)))
 have henv := ad (ad (ad (ad (ad hz))))
 have hn := fy henv
 have hL := bX henv
 have hi := di (aq hz) (ag hn hL)
 have hrem := dk (aq hz) (ag hn hL)
 have hj := di hrem hL
 have hr := dk hrem hL
 have htr := dk (bU (aV (cpt_pairB2 hq hz) hn lm)) (ac 2)
 have hAval := bt hA (af (ag (af (ag hi hn) hj) hL) (dj hr hq))
 exact gZ hq hr (ag htr hAval) (ac 0)
def da (q : ℕ) (t1 : List Bool) : ℕ :=
 let k := (unpairB t1).1.length
 let z := (unpairB t1).2
 let F := iS (unpairB (unpairB z).2).1
 let A := iS (unpairB (unpairB (unpairB z).2).2).1
 let env := (unpairB (unpairB (unpairB (unpairB (unpairB z).2).2).2).2).2
 let n := mN env
 let L := ez env
 let i := (unpairB z).1.length / (n * L)
 let pJ := (unpairB z).1.length % (n * L)
 let j := pJ / L
 let r := pJ % L
 if q ≤ r then F.getD ((i * n + k) * L + q) 0 * A.getD ((k * n + j) * L + (r - q)) 0 else 0
lemma kI : aj (fun t2 => da (unpairB t2).1.length (unpairB t2).2) := by
 unfold da
 have ht1 := cpt_unpairB2
 have hq := av
 have hk := aq ht1
 have hz := ad ht1
 have hF := dO (dK (ad hz))
 have hA := dO (dK (ad (ad hz)))
 have henv := ad (ad (ad (ad (ad hz))))
 have hn := fy henv
 have hL := bX henv
 have hi := di (aq hz) (ag hn hL)
 have hrem := dk (aq hz) (ag hn hL)
 have hj := di hrem hL
 have hr := dk hrem hL
 exact gZ hq hr
   (ag
     (bt hF (af (ag (af (ag hi hn) hk) hL) hq))
     (bt hA (af (ag (af (ag hk hn) hj) hL) (dj hr hq))))
   (ac 0)
def dL (k : ℕ) (z : List Bool) : ℕ :=
 let env := (unpairB (unpairB (unpairB (unpairB (unpairB z).2).2).2).2).2
 let n := mN env
 let L := ez env
 let i := (unpairB z).1.length / (n * L)
 if i + 1 ≤ k then
   ((List.range L).map (fun q => da q (pairB (un k) z))).sum % 2
 else 0
lemma kV : aj (fun t1 => dL (unpairB t1).1.length (unpairB t1).2) := by
 unfold dL
 have hz := cpt_unpairB2
 have hk := av
 have henv := ad (ad (ad (ad (ad hz))))
 have hn := fy henv
 have hL := bX henv
 have hi := di (aq hz) (ag hn hL)
 have hinner := dk (bU (aV (cpt_pairB2 hk hz) hL kI)) (ac 2)
 exact gZ (af hi (ac 1)) hk hinner (ac 0)
def dl (pos : ℕ) (kS : List Bool) : ℕ :=
 let y := (unpairB kS).2
 let env := (unpairB (unpairB (unpairB y).2).2).2
 let n := mN env
 let L := ez env
 let arg := pairB (un pos) kS
 let t1 := ((List.range L).map (fun q => cJ q arg)).sum % 2
 let t2 := ((List.range n).map (fun k => dL k arg)).sum % 2
 (t1 + t2) % 2
lemma kh :
   aj (fun nG => dl (unpairB nG).1.length (unpairB nG).2) := by
 unfold dl
 have henv := ad (ad (ad (ad cpt_unpairB2)))
 have hn := fy henv
 have hL := bX henv
 have harg := cpt_pairB2 av cpt_unpairB2
 have ht1 := dk (bU (aV harg hL lr)) (ac 2)
 have ht2 := dk (bU (aV harg hn kV)) (ac 2)
 exact dk (af ht1 ht2) (ac 2)
def aO (kS : List Bool) : List ℕ :=
 let y := (unpairB kS).2
 let env := (unpairB (unpairB (unpairB y).2).2).2
 (List.range (mN env * mN env * ez env)).map (fun pos => dl pos kS)
lemma mh : cX aO := by
 unfold aO
 have henv := ad (ad (ad cpt_unpairB2))
 have hn := fy henv
 have hL := bX henv
 exact aV cpt_id (ag (ag hn hn) hL) kh
def kH (aA : List Bool) : List Bool :=
 (fun a => aM (aO (pairB a aA)))^[mN (unpairB (unpairB (unpairB aA).2).2).2 - 1]
   (unpairB aA).1
lemma qG : aK.CPTs kH := by
 unfold kH
 have xu : aK.CPTs (fun aA => (unpairB (unpairB (unpairB aA).2).2).2) :=
   ad (ad (ad cpt_id))
 have ye : aj (fun aA => mN (unpairB (unpairB (unpairB aA).2).2).2 - 1) :=
   dj (fy xu) (ac 1)
 have rX := qn (F := fun z => aM (aO z))
   (init := fun aA => (unpairB aA).1)
   (cnt := fun aA => un (mN (unpairB (unpairB (unpairB aA).2).2).2 - 1))
   mh cpt_unpairB1 ye
   (Polynomial.C 2 * Polynomial.X ^ 3 + Polynomial.C 1) ?_
 · refine cptE rX (fun aA => ?_)
   rw [un_length]
 · intro aA i _
   let env := (unpairB (unpairB (unpairB aA).2).2).2
   have zR : (unpairB env).2.length ≤ env.length := by have := unpairB_length env; omega
   have zL : env.length ≤ (unpairB (unpairB aA).2).2.length := by
     dsimp only [env]
     have := unpairB_length (unpairB (unpairB aA).2).2
     omega
   have Ah : (unpairB (unpairB aA).2).2.length ≤ (unpairB aA).2.length := by
     have := unpairB_length (unpairB aA).2; omega
   have zx : (unpairB aA).2.length ≤ aA.length := by
     have := unpairB_length aA; omega
   have u5 : mN env ≤ aA.length := by
     have h1 : mN env ≤ (unpairB env).2.length := io _ _
     omega
   have w5 : ez env ≤ aA.length := by
     have h1 : ez env ≤ (unpairB env).2.length := io _ _
     omega
   cases i with
   | zero =>
     simp only [Function.iterate_zero,id_eq]
     have h1 : (unpairB aA).1.length ≤ aA.length := by have := unpairB_length aA; omega
     have hcube : aA.length ≤ aA.length ^ 3 := Nat.le_self_pow (by decide : 3 ≠ 0) aA.length
     simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
       Polynomial.eval_X]
     omega
   | succ i' =>
     simp only [Function.iterate_succ_apply']
     have hv : ∀ (a : List Bool),∀ x ∈ aO (pairB a aA),x ≤ 1 := by
       intro a x hx
       simp only [aO,List.mem_map,List.mem_range] at hx
       rcases hx with ⟨pos,_,rfl⟩
       dsimp only [dl]
       omega
     have hle := ke (hv ((fun a => aM (aO (pairB a aA)))^[i'] (unpairB aA).1))
     have hlen : (aO (pairB ((fun a => aM (aO (pairB a aA)))^[i'] (unpairB aA).1) aA)).length = mN env * mN env * ez env := by
       simp [aO,unpairB_pairB]; rfl
     rw [hlen] at hle
     have hm1 : mN env * mN env ≤ aA.length * aA.length := Nat.mul_le_mul u5 u5
     have hm2 : mN env * mN env * ez env ≤ aA.length * aA.length * aA.length :=
       Nat.mul_le_mul hm1 w5
     have hpow : aA.length * aA.length * aA.length = aA.length ^ 3 := by ring
     simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
       Polynomial.eval_X]
     omega
def fP (fD : List Bool) : List Bool :=
 kH (pairB (aM (bS fD)) fD)
lemma nZ : aK.CPTs fP := by
 unfold fP
 exact kQ (f := fun fD => pairB (aM (bS fD)) fD) (g := kH)
   (cpt_pairB2 ml cpt_id) qG
lemma oW (fD : List Bool) :
   fP fD =
     (fun a => aM (aO (pairB a (pairB (aM (bS fD)) fD))))^[mN (unpairB (unpairB fD).2).2 - 1]
       (aM (bS fD)) := by
 simp [fP,kH,unpairB_pairB]
def gL (r : ℕ) (last : List Bool) : ℕ :=
 (iS last).getD r 0
lemma ko :
   aj (fun t => gL (unpairB t).1.length (unpairB t).2) :=
 bt (dO cpt_unpairB2) av
def bm (fD : List Bool) : List ℕ :=
 (List.range (ez (unpairB (unpairB fD).2).2)).map (fun r => gL r (fP fD))
lemma mi : cX bm :=
 aV nZ (bX (ad cpt_unpairB2)) ko
def gX (aI : ℕ) (eL : List Bool) : List ℕ :=
 let t := (unpairB eL).1.length
 let env := (unpairB eL).2
 bm (pairB (aM (bF t env)) (pairB (un aI) env))
lemma lR : cX (fun z => gX (unpairB z).1.length (unpairB z).2) := by
 unfold gX
 have hz2 : aK.CPTs (fun z : List Bool => (unpairB z).2) := cpt_unpairB2
 have hre : aK.CPTs (fun z =>
     pairB (aM (bF (unpairB (unpairB z).2).1.length (unpairB (unpairB z).2).2))
       (pairB (un (unpairB z).1.length) (unpairB (unpairB z).2).2)) :=
   cpt_pairB2 (iA hz2 rH) (cpt_pairB2 av (ad hz2))
 exact iA (f := bm) hre mi
def gO (t : ℕ) (env : List Bool) : List ℕ :=
 (List.range (mP env + 1)).flatMap (fun aI => gX aI (pairB (un t) env))
lemma jF (t : ℕ) (env : List Bool) :
   gO t env = (List.range (mP env + 1)).flatMap (fun aI =>
     bm (pairB (aM (bF t env)) (pairB (un aI) env))) := by
 simp [gO,gX,unpairB_pairB,un_length]
lemma oQ :
   cX (fun eL => gO (unpairB eL).1.length (unpairB eL).2) := by
 unfold gO
 have hcnt := af (fz cpt_unpairB2) (ac 1)
 have harg : aK.CPTs (fun s => pairB (un (unpairB s).1.length) (unpairB s).2) :=
   cpt_pairB2 av cpt_unpairB2
 exact fI harg hcnt lR
def bl (s : List Bool) : List ℕ :=
 (List.range (s7 s)).flatMap (fun t => gO t (aE s))
lemma mD : cX bl :=
 fI ma rD oQ
def ah (s : List Bool) : List Bool := pairB (aM (bl s)) (aE s)
lemma qc : aK.CPTs ah := cpt_pairB2 mD ma
def j9 (w : ℕ) (x : List Bool) : List ℕ :=
 let t := (unpairB x).1.length
 let sv := (unpairB (unpairB x).2).1.length
 let jv := (unpairB (unpairB (unpairB x).2).2).1.length
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 let sU := iS (unpairB aD).1
 let env := (unpairB aD).2
 let P := mP env
 let B := mB env
 let L := ez env
 let m := mM env
 let base := qg env
 let T := (m + 1) * sv + jv - base
 let v8 := (t * (P + 1) + P) * L
 if sU.getD (v8 + 2 * (B * T + w)) 0 = 1 then [w] else []
lemma n5 : cX (fun x' => j9 (unpairB x').1.length (unpairB x').2) := by
 unfold j9
 have hx := cpt_unpairB2
 have hw := av
 have ht := aq hx
 have hsv := aq (ad hx)
 have hjv := aq (ad (ad hx))
 have hfull := ad (ad (ad hx))
 have qW := dO (dK hfull)
 have henv := ad hfull
 have hP := fz henv
 have hB := ou henv
 have hL := bX henv
 have hm := oi henv
 have hbase := lQ henv
 have hT := dj (af (ag (af hm (ac 1)) hsv) hjv) hbase
 have uB := ag (af (ag ht (af hP (ac 1))) hP) hL
 have hval := bt qW (af uB (ag (ac 2) (af (ag hB hT) hw)))
 exact kM hval (ac 1) (aN hw) oO
def ji (t aw ay : ℕ) (aD : List Bool) : List ℕ :=
 let B := mB (unpairB aD).2
 (List.range B).flatMap (fun w => j9 w (pairB (un t) (pairB (un aw) (pairB (un ay) aD))))
lemma nU {ft fs fj : List Bool -> ℕ} {ff : List Bool -> List Bool}
   (ht : aj ft) (hs : aj fs) (hj : aj fj) (hf : aK.CPTs ff) :
   cX (fun z => ji (ft z) (fs z) (fj z) (ff z)) := by
 unfold ji
 have harg := cpt_pairB2 ht (cpt_pairB2 hs (cpt_pairB2 hj hf))
 have hB := ou (ad hf)
 exact fI harg hB n5
def bT (t aw ay idx : ℕ) (aD : List Bool) : ℕ :=
 let ws := ji t aw ay aD
 let w := ws.getD 0 0
 let sU := iS (unpairB aD).1
 let env := (unpairB aD).2
 let P := mP env
 let B := mB env
 let L := ez env
 let m := mM env
 let base := qg env
 let T := (m + 1) * aw + ay - base
 let wC := (t * (P + 1) + idx) * L
 if sU.getD (wC + 2 * (B * T + w)) 0 = 0 then 1 else 0
lemma fU {ft fs fj yM : List Bool -> ℕ} {ff : List Bool -> List Bool}
   (ht : aj ft) (hs : aj fs) (hj : aj fj) (hidx : aj yM) (hf : aK.CPTs ff) :
   aj (fun z => bT (ft z) (fs z) (fj z) (yM z) (ff z)) := by
 unfold bT
 have hw := bt (nU ht hs hj hf) (ac 0)
 have qW := dO (dK hf)
 have henv := ad hf
 have hP := fz henv
 have hB := ou henv
 have hL := bX henv
 have hm := oi henv
 have hbase := lQ henv
 have hT := dj (af (ag (af hm (ac 1)) hs) hj) hbase
 have u8 := ag (af (ag ht (af hP (ac 1))) hidx) hL
 have hval := bt qW (af u8 (ag (ac 2) (af (ag hB hT) hw)))
 exact cH hval (ac 0) (ac 1) (ac 0)
def cY (k : ℕ) (x : List Bool) : ℕ :=
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 let env := (unpairB aD).2
 1 - gf (mS env) (bq (mS env) + k * (2 * mN env))
def cU (idx : ℕ) (x : List Bool) : ℕ :=
 let t := (unpairB x).1.length
 let sv := (unpairB (unpairB x).2).1.length
 let jv := (unpairB (unpairB (unpairB x).2).2).1.length
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 bT t sv jv idx aD * (1 - qo (unpairB aD).2 idx)
def aB (idx : ℕ) (x2 : List Bool) : ℕ :=
 let v := (unpairB x2).1.length
 let x := (unpairB x2).2
 let t := (unpairB x).1.length
 let sv := (unpairB (unpairB x).2).1.length
 let jv := (unpairB (unpairB (unpairB x).2).2).1.length
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 let env := (unpairB aD).2
 bT t sv jv idx aD * ((if mU env idx = v then 1 else 0) + (if mV env idx = v then 1 else 0))
def cK (v : ℕ) (x : List Bool) : ℕ :=
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 let P := mP (unpairB aD).2
 let zp := ((List.range P).map (fun idx => aB idx (pairB (un v) x))).sum
 if 2 ≤ zp then 1 else 0
def cC (idx : ℕ) (x : List Bool) : ℕ :=
 let t := (unpairB x).1.length
 let sv := (unpairB (unpairB x).2).1.length
 let jv := (unpairB (unpairB (unpairB x).2).2).1.length
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 bT t sv jv idx aD
def bJ (idx : ℕ) (x : List Bool) : ℕ :=
 let t := (unpairB x).1.length
 let sv := (unpairB (unpairB x).2).1.length
 let jv := (unpairB (unpairB (unpairB x).2).2).1.length
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 bT t sv jv idx aD * mC (unpairB aD).2 idx
lemma lE : aj (fun t2 => cY (unpairB t2).1.length (unpairB t2).2) := by
 unfold cY
 have hf := ad (ad (ad cpt_unpairB2))
 have henv := ad hf
 have hs := kQ henv uS
 have hn := fy henv
 have hoff := af (aH hs iU) (ag av (ag (ac 2) hn))
 exact dj (ac 1) (gY hs hoff)
lemma lh : aj (fun t2 => cU (unpairB t2).1.length (unpairB t2).2) := by
 unfold cU
 have hx := cpt_unpairB2
 have hidx := av
 have ht := aq hx
 have hsv := aq (ad hx)
 have hjv := aq (ad (ad hx))
 have hf := ad (ad (ad hx))
 have henv := ad hf
 have uP := oS henv hidx
 exact ag (fU ht hsv hjv hidx hf) (dj (ac 1) uP)
lemma lj : aj (fun t3 => aB (unpairB t3).1.length (unpairB t3).2) := by
 unfold aB
 have hx2 := cpt_unpairB2
 have hidx := av
 have hv := aq hx2
 have hx := ad hx2
 have ht := aq hx
 have hsv := aq (ad hx)
 have hjv := aq (ad (ad hx))
 have hf := ad (ad (ad hx))
 have henv := ad hf
 have hu := tw henv hidx
 have xZ := td henv hidx
 exact ag (fU ht hsv hjv hidx hf) (af (bE hu hv) (bE xZ hv))
lemma lB : aj (fun t2 => cK (unpairB t2).1.length (unpairB t2).2) := by
 unfold cK
 have hv := av
 have hx := cpt_unpairB2
 have hP := fz (ad (ad (ad (ad hx))))
 have yN := bU (aV (cpt_pairB2 hv hx) hP lj)
 exact gZ (ac 2) yN (ac 1) (ac 0)
lemma mg : aj (fun t2 => cC (unpairB t2).1.length (unpairB t2).2) := by
 unfold cC
 have hx := cpt_unpairB2
 have hidx := av
 have ht := aq hx
 have hsv := aq (ad hx)
 have hjv := aq (ad (ad hx))
 have hf := ad (ad (ad hx))
 exact fU ht hsv hjv hidx hf
lemma me : aj (fun t2 => bJ (unpairB t2).1.length (unpairB t2).2) := by
 unfold bJ
 have hx := cpt_unpairB2
 have hidx := av
 have ht := aq hx
 have hsv := aq (ad hx)
 have hjv := aq (ad (ad hx))
 have hf := ad (ad (ad hx))
 have henv := ad hf
 have hc := tP henv hidx
 exact ag (fU ht hsv hjv hidx hf) hc
def bM (t aw ay : ℕ) (aD : List Bool) : ℕ :=
 let env := (unpairB aD).2
 let n := mN env
 let zH := (eM env).getD 2 0
 let P := mP env
 let m := mM env
 let base := qg env
 let ws := ji t aw ay aD
 let Ay := (m + 1) * aw + ay
 let x := pairB (un t) (pairB (un aw) (pairB (un ay) aD))
 let vZ := ((List.range zH).map (fun z => cY z x)).sum
 let wj := ((List.range P).map (fun idx => cU idx x)).sum
 let w8 := ((List.range n).map (fun v => cK v x)).sum
 let sz := ((List.range P).map (fun idx => cC idx x)).sum
 let sc := base + ((List.range P).map (fun idx => bJ idx x)).sum
 if 2 ≤ n /\ base ≤ Ay /\ 0 < ws.length /\ vZ = 0 /\ wj = 0 /\ w8 = 0 /\ sz = aw /\ sc = Ay
 then 1 else 0
lemma rU (p q : Prop) [Decidable p] [Decidable q] :
   (if p then 1 else 0) * (if q then 1 else 0) = if p /\ q then 1 else 0 := by
 by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]
lemma kG {ft fs fj : List Bool -> ℕ} {ff : List Bool -> List Bool}
   (ht : aj ft) (hs : aj fs) (hj : aj fj) (hf : aK.CPTs ff) :
   aj (fun z => bM (ft z) (fs z) (fj z) (ff z)) := by
 unfold bM
 have henv := ad hf
 have hn := fy henv
 have rW := aH henv (dw _ (ac 2))
 have hP := fz henv
 have hm := oi henv
 have hbase := lQ henv
 have xT := qf (nU ht hs hj hf)
 have yH := af (ag (af hm (ac 1)) hs) hj
 have hx := cpt_pairB2 ht (cpt_pairB2 hs (cpt_pairB2 hj hf))
 have uz := bU (aV hx rW lE)
 have u7 := bU (aV hx hP lh)
 have wh := bU (aV hx hn lB)
 have hsz := bU (aV hx hP mg)
 have hsc := af hbase (bU (aV hx hP me))
 have c1 := nM (ac 2) hn
 have c2 := nM hbase yH
 have c3 := nV (ac 0) xT
 have c4 := bE uz (ac 0)
 have c5 := bE u7 (ac 0)
 have c6 := bE wh (ac 0)
 have c7 := bE hsz hs
 have c8 := bE hsc yH
 have hprod := ag (ag (ag c1 c2) (ag c3 c4))
   (ag (ag c5 c6) (ag c7 c8))
 refine cptE hprod (fun z => ?_)
 dsimp only
 simp only [rU,and_assoc]
def gP (t : ℕ) (x : List Bool) : List ℕ :=
 let sv := (unpairB x).1.length
 let jv := (unpairB (unpairB x).2).1.length
 let aD := (unpairB (unpairB x).2).2
 if bM t sv jv aD = 1 then [t] else []
lemma od : cX (fun x' => gP (unpairB x').1.length (unpairB x').2) := by
 unfold gP
 have hx := cpt_unpairB2
 have ht := av
 have hsv := aq hx
 have hjv := aq (ad hx)
 have hfull := ad (ad hx)
 exact kM (kG ht hsv hjv hfull) (ac 1) (aN ht) oO
def bP (aw ay : ℕ) (aD : List Bool) : List ℕ :=
 let env := (unpairB aD).2
 (List.range (mR env)).flatMap (fun t => gP t (pairB (un aw) (pairB (un ay) aD)))
lemma rG {fs fj : List Bool -> ℕ} {ff : List Bool -> List Bool}
   (hs : aj fs) (hj : aj fj) (hf : aK.CPTs ff) :
   cX (fun z => bP (fs z) (fj z) (ff z)) := by
 unfold bP
 have harg := cpt_pairB2 hs (cpt_pairB2 hj hf)
 have hR := wx (ad hf)
 exact fI harg hR od
def iw (idx : ℕ) (x : List Bool) : ℕ :=
 let t := (unpairB x).1.length
 let sv := (unpairB (unpairB x).2).1.length
 let jv := (unpairB (unpairB (unpairB x).2).2).1.length
 let aD := (unpairB (unpairB (unpairB x).2).2).2
 bT t sv jv idx aD
lemma mJ : aj (fun x' => iw (unpairB x').1.length (unpairB x').2) := by
 unfold iw
 have hx := cpt_unpairB2
 have hidx := av
 have ht := aq hx
 have hsv := aq (ad hx)
 have hjv := aq (ad (ad hx))
 have hfull := ad (ad (ad hx))
 exact fU ht hsv hjv hidx hfull
def bN (t aw ay : ℕ) (aD : List Bool) : List ℕ :=
 let P := mP (unpairB aD).2
 (List.range P).map (fun idx => iw idx (pairB (un t) (pairB (un aw) (pairB (un ay) aD))))
lemma pU {ft fs fj : List Bool -> ℕ} {ff : List Bool -> List Bool}
   (ht : aj ft) (hs : aj fs) (hj : aj fj) (hf : aK.CPTs ff) :
   cX (fun z => bN (ft z) (fs z) (fj z) (ff z)) := by
 unfold bN
 have harg := cpt_pairB2 ht (cpt_pairB2 hs (cpt_pairB2 hj hf))
 have hP := fz (ad hf)
 exact aV harg hP mJ
def mF (aw ay : ℕ) (aD : List Bool) : List ℕ :=
 let P := mP (unpairB aD).2
 let ts := bP aw ay aD
 if ts.length = 0 then (List.range (P + 1)).map (fun _ => 0)
 else 1 :: bN (ts.getD 0 0) aw ay aD
lemma qF {fs fj : List Bool -> ℕ} {ff : List Bool -> List Bool}
   (hs : aj fs) (hj : aj fj) (hf : aK.CPTs ff) :
   cX (fun z => mF (fs z) (fj z) (ff z)) := by
 unfold mF
 have hP := fz (ad hf)
 have hts := rG hs hj hf
 have hlen := qf hts
 have xB : cX (fun z => (List.range (mP (unpairB (ff z)).2 + 1)).map (fun _ => 0)) :=
   aV (G := fun _ _ => 0) cpt_id (af hP (ac 1)) (ac 0)
 have rE : cX (fun z => 1 :: bN ((bP (fs z) (fj z) (ff z)).getD 0 0) (fs z) (fj z) (ff z)) :=
   aR (aN (ac 1))
     (pU (bt hts (ac 0)) hs hj hf)
 exact kM hlen (ac 0) xB rE
def iZ (jv : ℕ) (x : List Bool) : List ℕ :=
 mF (unpairB x).1.length jv (unpairB x).2
lemma nC : cX (fun t => iZ (unpairB t).1.length (unpairB t).2) := by
 unfold iZ
 have hsnd : aK.CPTs (fun z : List Bool => (unpairB z).2) := cpt_unpairB2
 exact qF (aq hsnd) av (ad hsnd)
def la (sv : ℕ) (fe : List Bool) : List ℕ :=
 (List.range (mM (unpairB fe).2 + 1)).flatMap (fun jv =>
   iZ jv (pairB (un sv) fe))
lemma oM : cX (fun t => la (unpairB t).1.length (unpairB t).2) := by
 unfold la
 have hm1 := af (oi (ad cpt_unpairB2)) (ac 1)
 have harg : aK.CPTs (fun t => pairB (un (unpairB t).1.length) (unpairB t).2) :=
   cpt_pairB2 av cpt_unpairB2
 exact fI harg hm1 nC
def px (s : List Bool) : List ℕ :=
 (List.range (g8 s / 2 + 1)).flatMap (fun sv => la sv (ah s))
lemma pQ (s : List Bool) :
   px s =
     (List.range (g8 s / 2 + 1)).flatMap (fun sv =>
       (List.range (ro s + 1)).flatMap (fun jv =>
         mF sv jv (ah s))) := by
 have hm : mM (unpairB (ah s)).2 = ro s := by
   simp [mM,ah,aE,eM,unpairB_pairB,dh,eg]
 simp [px,la,iZ,hm,unpairB_pairB,un_length]
lemma rP : cX px := by
 unfold px
 exact fI qc (af (di bC (ac 2)) (ac 1)) oM
def jG (s : List Bool) : List Bool :=
 (px s).map (fun x => decide (x ≠ 0))
lemma pK : aK.CPTs jG :=
 su rP
lemma pg :
   ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) jG,
     ∀ i,Finite (M.tm.Γ i) :=
 aK.Fast.cpt_to_fast pK
end Alg
section AlgProofs
open aK aK.Universal aK.R aK.Loop
lemma aJ {α β : Type*} (L : List α) (g : α -> List β) (K : ℕ)
   (hg : ∀ x ∈ L,(g x).length = K) (d : β) (z r : ℕ) (hz : z < L.length) (hr : r < K) :
   (L.flatMap g).getD (z * K + r) d = (g (L[z]'hz)).getD r d := by
 induction L generalizing z with
 | nil => simp at hz
 | cons x xs ih =>
   have hx : (g x).length = K := hg x (List.mem_cons_self ..)
   rw [List.flatMap_cons,List.getD_eq_getElem?_getD]
   cases z with
   | zero =>
     simp only [zero_mul,zero_add,List.getElem_cons_zero]
     rw [List.getElem?_append_left (by omega),List.getD_eq_getElem?_getD]
   | succ z' =>
     simp only [Nat.succ_mul,List.getElem_cons_succ]
     have hge : (g x).length ≤ z' * K + K + r := by omega
     rw [List.getElem?_append_right hge,hx]
     have hsub : z' * K + K + r - K = z' * K + r := by omega
     rw [hsub,← List.getD_eq_getElem?_getD]
     exact ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) z' (Nat.lt_of_succ_lt_succ hz)
lemma bh (n : ℕ) :
   (List.finRange n).map Fin.val = List.range n := by
 apply List.ext_getElem
 · simp
 · intro i hi1 hi2
   simp
lemma mo (n : ℕ) (s : List Bool) (hn : g8 s = n) :
   dR s = (ae n).flatMap (fun e => [e.1.val,e.2.val]) := by
 unfold dR ae
 rw [hn]
 have h1 : ∀ (l1 : List (Fin n)),
     (l1.map Fin.val).flatMap (fun i => (List.range n).flatMap (fun j => if i < j then [i,j] else [])) =
     l1.flatMap (fun i => ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)) |>.flatMap
       (fun e => [e.1.val,e.2.val])) := by
   intro l1
   induction l1 with
   | nil => simp
   | cons i l1 ih =>
     simp only [List.map_cons,List.flatMap_cons,ih]
     congr 1
     rw [← bh n,List.flatMap_map,List.flatMap_map]
     clear ih l1
     induction List.finRange n with
     | nil => simp
     | cons j js ihj =>
       simp only [List.flatMap_cons,List.filter_cons,Function.comp_apply]
       by_cases hij : i < j
       · have xJ : i.val < j.val := hij
         simp only [hij,xJ,decide_true,↓reduceIte,List.flatMap_cons,List.cons_append,
           List.nil_append,ihj]
       · have xJ : ¬ (i.val < j.val) := hij
         simp only [hij,xJ,decide_false,Bool.false_eq_true,↓reduceIte,List.flatMap_nil,
           List.nil_append,ihj]
 have h := h1 (List.finRange n)
 rw [bh] at h
 rw [h,List.flatMap_assoc]
lemma na (n : ℕ) (s : List Bool) (hn : g8 s = n) :
   (dR s).length = 2 * (ae n).length := by
 rw [mo n s hn]
 clear hn
 induction ae n with
 | nil => simp
 | cons e es ih => simp [ih]; omega
lemma iB (n : ℕ) (s : List Bool) (hn : g8 s = n) (idx : Fin (ae n).length) :
   (dR s).getD (2 * idx.val) 0 = (aa idx).1.val /\
   (dR s).getD (2 * idx.val + 1) 0 = (aa idx).2.val := by
 rw [mo n s hn]
 have h1 := aJ (ae n) (fun e => [e.1.val,e.2.val]) 2
   (fun _ _ => rfl) 0 idx.val 0 idx.isLt (by omega)
 have h2 := aJ (ae n) (fun e => [e.1.val,e.2.val]) 2
   (fun _ _ => rfl) 0 idx.val 1 idx.isLt (by omega)
 simp only [mul_comm _ 2,add_zero] at h1
 simp only [mul_comm _ 2] at h2
 exact ⟨h1,h2⟩
lemma ai {α : Type*} (l1 l2 : List α) (d : α) (k : ℕ) (hk : k < l1.length) :
   (l1 ++ l2).getD k d = l1.getD k d := by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hk]
lemma aS {α : Type*} (l1 l2 : List α) (d : α) (k : ℕ) (hk : l1.length ≤ k) :
   (l1 ++ l2).getD k d = l2.getD (k - l1.length) d := by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hk]
lemma bA (a n : ℕ)
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (rest : List Bool) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let prefixBits := header a ++ input
   let s := prefixBits ++ rest
   ur s = a /\ g8 s = n /\ iH s = hard.length /\
   bq s = a + 1 + n + 1 + hard.length + 1 /\
   bL s = bq s + hard.length * (2 * n) /\
   ro s = soft.length /\
   bi s = bL s + soft.length + 1 /\
   ef s = prefixBits.length /\
   a + n + soft.length + 4 ≤ prefixBits.length /\
   (∀ z : ℕ,∀ hz : z < hard.length,∀ i : Fin n,
     bitAt s (bq s + z * (2 * n) + i.val) = (if i ∈ (hard[z]'hz).1 then 1 else 0) /\
     bitAt s (bq s + z * (2 * n) + n + i.val) = (if i ∈ (hard[z]'hz).2 then 1 else 0)) /\
   (∀ z : ℕ,∀ hz : z < soft.length,
     (∀ i : Fin n,
       bitAt s (bi s + z * (2 * n + 1) + i.val) = (if i ∈ (soft[z]'hz).1.1 then 1 else 0) /\
       bitAt s (bi s + z * (2 * n + 1) + n + i.val) = (if i ∈ (soft[z]'hz).1.2 then 1 else 0)) /\
     bitAt s (bi s + z * (2 * n + 1) + 2 * n) = (if (soft[z]'hz).2 then 1 else 0)) /\
   (∀ k : ℕ,s.getD (ef s + k) false = rest.getD k false) := by
 intro header bank input prefixBits s
 have dC : ∀ B : Finset (Fin n),(bank B).length = n := fun B => by simp [bank]
 have lY : ∀ z ∈ hard,(bank z.1 ++ bank z.2).length = 2 * n := fun z _ => by
   simp [dC]; omega
 have oE : ∀ t ∈ soft,(bank t.1.1 ++ bank t.1.2 ++ [t.2]).length = 2 * n + 1 := fun t _ => by
   simp [dC]; omega
 have ld : ∀ {α : Type} (L : List α) (g : α -> List Bool) (K : ℕ),
     (∀ x ∈ L,(g x).length = K) -> (L.flatMap g).length = L.length * K := by
   intro α L g K hg
   induction L with
   | nil => simp
   | cons x xs ih =>
     simp only [List.flatMap_cons,List.length_append,List.length_cons,hg x (List.mem_cons_self ..),
       ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))]
     ring
 have qP : (hard.flatMap (fun z => bank z.1 ++ bank z.2)).length = hard.length * (2 * n) :=
   ld hard (fun z => bank z.1 ++ bank z.2) (2 * n) lY
 have vy : (soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])).length = soft.length * (2 * n + 1) :=
   ld soft (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2]) (2 * n + 1) oE
 let rf := header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
   header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2]) ++ rest
 let sG := hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
   header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2]) ++ rest
 let qQ := header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2]) ++ rest
 let uD := soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2]) ++ rest
 have x5 : s = List.replicate a true ++ [false] ++ (List.replicate n true ++ [false] ++ rf) := by
   dsimp [s,prefixBits,input,header,rf]
   simp only [List.append_assoc]
 have nI : ur s = a := by
   dsimp [ur,lG]
   rw [x5,List.drop_zero,eU]
 have tI : s.drop (a + 1) = List.replicate n true ++ [false] ++ rf := by
   rw [x5]; exact i6 a _
 have bk : g8 s = n := by
   dsimp [g8,lG]
   rw [nI,tI,eU]
 have tH : s.drop (a + 1 + n + 1) =
     List.replicate hard.length true ++ [false] ++ sG := by
   rw [show a + 1 + n + 1 = (a + 1) + (n + 1) by omega,← List.drop_drop,tI,i6]
   dsimp [rf,sG,header]
   simp only [List.append_assoc]
 have mI : iH s = hard.length := by
   dsimp [iH,lG]
   rw [nI,bk,tH,eU]
 have iX : bq s = a + 1 + n + 1 + hard.length + 1 := by
   dsimp [bq]; rw [nI,bk,mI]
 have rx : s.drop (bq s) =
     hard.flatMap (fun z => bank z.1 ++ bank z.2) ++ qQ := by
   rw [iX,show a + 1 + n + 1 + hard.length + 1 = (a + 1 + n + 1) + (hard.length + 1) by omega,
     ← List.drop_drop,tH,i6]
   dsimp [sG,qQ]
   simp only [List.append_assoc]
 have gn : bL s = bq s + hard.length * (2 * n) := by
   dsimp [bL]; rw [mI,bk]
 have rJ : s.drop (bL s) =
     List.replicate soft.length true ++ [false] ++ uD := by
   rw [gn,← List.drop_drop,rx,← qP,List.drop_left]
   dsimp [qQ,uD,header]
   simp only [List.append_assoc]
 have fE : ro s = soft.length := by
   dsimp [ro,lG]
   rw [rJ,eU]
 have i5 : bi s = bL s + soft.length + 1 := by
   dsimp [bi]; rw [fE]
 have ux : s.drop (bi s) =
     soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2]) ++ rest := by
   rw [i5,show bL s + soft.length + 1 = bL s + (soft.length + 1) by omega,
     ← List.drop_drop,rJ,i6]
 have mK : prefixBits.length = ef s := by
   dsimp [prefixBits,input,header,ef]
   simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,
     qP,vy]
   rw [i5,gn,iX,fE,bk]
   omega
 have sm : s.drop (ef s) = rest := by
   rw [← mK]
   dsimp [s]
   exact List.drop_left
 have wq : a + n + soft.length + 4 ≤ prefixBits.length := by
   rw [mK]
   dsimp [ef]
   rw [i5,gn,iX,fE,bk]
   omega
 refine ⟨nI,bk,mI,iX,gn,fE,i5,mK.symm,wq,
   ?_,?_,?_⟩
 · intro z hz i
   have h1 : s.getD (bq s + z * (2 * n) + i.val) false =
       (s.drop (bq s)).getD (z * (2 * n) + i.val) false := by
     simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,add_assoc]
   have h2 : s.getD (bq s + z * (2 * n) + n + i.val) false =
       (s.drop (bq s)).getD (z * (2 * n) + (n + i.val)) false := by
     simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,add_assoc]
   rw [bitAt,bitAt,h1,h2,rx]
   have hlt1 : z * (2 * n) + i.val < (hard.flatMap (fun z => bank z.1 ++ bank z.2)).length := by
     rw [qP]; have := i.isLt; nlinarith
   have hlt2 : z * (2 * n) + (n + i.val) < (hard.flatMap (fun z => bank z.1 ++ bank z.2)).length := by
     rw [qP]; have := i.isLt; nlinarith
   rw [ai _ _ _ _ hlt1,ai _ _ _ _ hlt2]
   rw [aJ hard _ (2 * n) lY false z i.val hz (by omega)]
   rw [aJ hard _ (2 * n) lY false z (n + i.val) hz (by omega)]
   rw [ai _ _ _ _ (by rw [dC]; exact i.isLt)]
   rw [aS _ _ _ _ (by rw [dC]; omega),dC,Nat.add_sub_cancel_left]
   simp [bank,i.isLt]
 · intro z hz
   have pD : ∀ r < 2 * n + 1,s.getD (bi s + z * (2 * n + 1) + r) false =
       ((bank (soft[z]'hz).1.1 ++ bank (soft[z]'hz).1.2 ++ [(soft[z]'hz).2]).getD r false) := by
     intro r hr
     have uV : s.getD (bi s + z * (2 * n + 1) + r) false =
         (s.drop (bi s)).getD (z * (2 * n + 1) + r) false := by
       simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,add_assoc]
     rw [uV,ux]
     have hlt : z * (2 * n + 1) + r < (soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])).length := by
       rw [vy]; nlinarith
     rw [ai _ _ _ _ hlt]
     exact aJ soft _ (2 * n + 1) oE false z r hz hr
   refine ⟨fun i => ?_,?_⟩
   · have hi := i.isLt
     have hs1 : (bank (soft[z]'hz).1.1 ++ bank (soft[z]'hz).1.2 ++ [(soft[z]'hz).2]).getD i.val false =
         (bank (soft[z]'hz).1.1).getD i.val false := by
       rw [ai _ _ _ _ (by simp only [List.length_append,dC]; omega),
         ai _ _ _ _ (by rw [dC]; exact hi)]
     have hs2 : (bank (soft[z]'hz).1.1 ++ bank (soft[z]'hz).1.2 ++ [(soft[z]'hz).2]).getD (n + i.val) false =
         (bank (soft[z]'hz).1.2).getD i.val false := by
       rw [ai _ _ _ _ (by simp only [List.length_append,dC]; exact Nat.add_lt_add_left hi n),
         aS _ _ _ _ (by rw [dC]; omega),
         dC,Nat.add_sub_cancel_left]
     rw [bitAt,bitAt,pD i.val (by omega),show bi s + z * (2 * n + 1) + n + i.val =
         bi s + z * (2 * n + 1) + (n + i.val) by omega,pD (n + i.val) (by omega),hs1,hs2]
     simp [bank,hi]
   · have hbb : (bank (soft[z]'hz).1.1 ++ bank (soft[z]'hz).1.2).length = 2 * n := by
       simp only [List.length_append,dC]; omega
     rw [bitAt,pD (2 * n) (by omega),
       aS _ _ _ _ (le_of_eq hbb),hbb,Nat.sub_self]
     simp
 · intro k
   have uV : s.getD (ef s + k) false = (s.drop (ef s)).getD k false := by
     simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]
   rw [uV,sm]
lemma aC (L : ℕ) (f : ℕ -> ℕ) :
   ((List.range L).map f).sum = 0 ↔ ∀ z < L,f z = 0 := by
 induction L with
 | zero => simp
 | succ L ih =>
   simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.sum_append,
     List.sum_cons,List.sum_nil,add_zero,Nat.add_eq_zero_iff,ih]
   constructor
   · rintro ⟨h1,h2⟩ z hz
     rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hlt | rfl
     · exact h1 z hlt
     · exact h2
   · intro h
     exact ⟨fun z hz => h z (Nat.lt_succ_of_lt hz),h L (Nat.lt_succ_self L)⟩
lemma bV {α : Type*} (L : List α) (p : α -> Prop) [DecidablePred p] :
   ((List.range L.length).map (fun z =>
     if h : z < L.length then if p (L[z]'h) then 1 else 0 else 0)).sum =
   (L.filter (fun x => decide (p x))).length := by
 induction L with
 | nil => simp
 | cons a L ih =>
   have hr : List.range (a :: L).length = 0 :: List.map Nat.succ (List.range L.length) := by
     rw [List.length_cons,List.range_succ_eq_map]
   rw [hr,List.map_cons,List.sum_cons]
   have h0 : (if h : 0 < (a :: L).length then if p ((a :: L)[0]'h) then 1 else 0 else 0) =
       if p a then 1 else 0 := by simp
   rw [h0]
   have htail : (List.map (fun z => if h : z < (a :: L).length then if p ((a :: L)[z]'h) then 1 else 0 else 0)
       (List.map Nat.succ (List.range L.length))).sum =
       (List.map (fun z => if h : z < L.length then if p (L[z]'h) then 1 else 0 else 0)
       (List.range L.length)).sum := by
     congr 1
     rw [List.map_map]
     apply List.map_congr_left
     intro z hz
     have hz' : z < L.length := List.mem_range.mp hz
     simp [hz']
   rw [htail,ih,List.filter_cons]
   by_cases hp : p a <;> simp [hp] <;> omega
lemma aT {α : Type*} (L : List α) (p : α -> Bool) :
   ((List.range L.length).map (fun z =>
     if h : z < L.length then if p (L[z]'h) = true then 1 else 0 else 0)).sum =
   (L.filter p).length := by
 convert bV L (fun x => p x = true) using 2
 ext x
 simp
lemma aW (K : ℕ) (p : Fin K -> Bool) :
   ((List.range K).map (fun z =>
     if h : z < K then if p ⟨z,h⟩ = true then 1 else 0 else 0)).sum =
   ((List.finRange K).filter p).length := by
 have h := aT (List.finRange K) p
 simpa [List.length_finRange,List.getElem_finRange] using h
lemma jA (M S k v j : ℕ) (hk : k ≤ M) (hj : j < M + 1)
   (heq : (M + 1) * S + k = (M + 1) * v + j) : S = v := by
 nlinarith
lemma rL (B T W n m U : ℕ) (hT : T ≤ n * (2 * m + 1)) (hW : W < B) :
   2 * (B * T + W) < 2 * (n * (B * (2 * m + 1) + U) + B) + 1 := by
 nlinarith
lemma oZ (T sv m n : ℕ) (hT : T ≤ (m + 1) * sv + m) (hsv : sv ≤ n / 2) (hn : 2 ≤ n) :
   T ≤ n * (2 * m + 1) := by
 have := Nat.mul_div_le n 2
 nlinarith
lemma jI (K : ℕ) : K % 2 = if (K % 2 == 1) = true then 1 else 0 := by
 rcases Nat.mod_two_eq_zero_or_one K with h | h <;> simp [h]
lemma oR (idx aI em u v i j r dg : ℕ) (xW : em = 0 \/ em = 1) :
   ((if idx = aI then 0 else em) *
     (if (if u = i then 1 else 0) * (if v = j then 1 else 0) +
         (if u = j then 1 else 0) * (if v = i then 1 else 0) = 0 then 0 else 1) *
     (if r = dg then 1 else 0)) =
   if (decide (em ≠ 0) && decide (idx ≠ aI) &&
       ((u == i && v == j) || (u == j && v == i)) && decide (r = dg)) then 1 else 0 := by
 rcases xW with rfl | rfl <;>
   by_cases h1 : idx = aI <;>
   by_cases h2 : u = i <;>
   by_cases h3 : v = j <;>
   by_cases h4 : u = j <;>
   by_cases h5 : v = i <;>
   by_cases h6 : r = dg <;>
   simp [h1,h2,h3,h4,h5,h6]
lemma jx (n : ℕ) :
   ae n = (List.finRange (ae n).length).map aa := by
 apply List.ext_getElem <;> simp [aa,List.get_eq_getElem]
lemma rQ (t sv jv : ℕ) (fe : List Bool) :
   bN t sv jv fe = (List.range (mP (unpairB fe).2)).map (fun idx => bT t sv jv idx fe) := by
 unfold bN
 apply List.map_congr_left
 intro idx _
 simp only [iw,unpairB_pairB,un_length]
lemma aX {n : ℕ} (s : List Bool) (hn : g8 s = n) :
   let env := aE s
   mS env = s /\ eM env = eg s /\
   mN env = n /\ mM env = ro s /\ o9 env = ef s /\
   mP env = (ae n).length /\ mb env = ow s /\ rV env = ui s /\
   mB env = iz s /\ ez env = am s /\ mR env = s7 s /\ qg env = eT s /\
   (∀ idx : Fin (ae n).length,
     mU env idx.val = (aa idx).1.val /\
     mV env idx.val = (aa idx).2.val /\
     qo env idx.val = (bD s).getD idx.val 0 /\
     mC env idx.val = (eP s).getD idx.val 0) := by
 intro env
 have hP : sW s = (ae n).length := by
   dsimp [sW]; rw [hn]
   have := dZ n; omega
 have hmS : mS env = s := by simp [env,aE,mS,unpairB_pairB]
 have fg : eM env = eg s := by simp [env,aE,eM,unpairB_pairB,dh]
 have hsc : ∀ k < 13,(eg s).getD k 0 =
     ([ur s,g8 s,iH s,ro s,ef s,sW s,ow s,ui s,iz s,lN s,am s,s7 s,eT s]).getD k 0 := by
   intro k hk
   unfold eg
   rw [ai,ai,ai] <;>
     simp [List.length_cons,hk] <;> omega
 refine ⟨hmS,fg,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw [mN,fg,hsc 1 (by omega)]; simp [hn]
 · rw [mM,fg,hsc 3 (by omega)]; rfl
 · rw [o9,fg,hsc 4 (by omega)]; rfl
 · rw [mP,fg,hsc 5 (by omega)]; exact hP
 · rw [mb,fg,hsc 6 (by omega)]; rfl
 · rw [rV,fg,hsc 7 (by omega)]; rfl
 · rw [mB,fg,hsc 8 (by omega)]; rfl
 · rw [ez,fg,hsc 10 (by omega)]; rfl
 · rw [mR,fg,hsc 11 (by omega)]; rfl
 · rw [qg,fg,hsc 12 (by omega)]; rfl
 · intro idx
   have iy : (dR s).length = 2 * (ae n).length := na n s hn
   have oL : (bD s).length = (ae n).length := by simp [bD,hP]
   have z9 : (eP s).length = (ae n).length := by simp [eP,hP]
   have eD : ([ur s,g8 s,iH s,ro s,ef s,sW s,ow s,ui s,iz s,
       lN s,am s,s7 s,eT s] : List ℕ).length = 13 := rfl
   have uj : mP env = (ae n).length := by rw [mP,fg,hsc 5 (by omega)]; exact hP
   have hpf := iB n s hn idx
   refine ⟨?_,?_,?_,?_⟩
   · rw [mU,fg,eg]
     rw [ai _ _ _ _ (by simp [eD,iy,oL]; omega)]
     rw [ai _ _ _ _ (by simp [eD,iy]; omega)]
     rw [aS _ _ _ _ (by omega),eD]
     simp only [Nat.add_sub_cancel_left]
     exact hpf.1
   · rw [mV,fg,eg]
     rw [ai _ _ _ _ (by simp [eD,iy,oL]; omega)]
     rw [ai _ _ _ _ (by simp [eD,iy]; omega)]
     rw [aS _ _ _ _ (by omega),eD]
     rw [show 13 + 2 * idx.val + 1 - 13 = 2 * idx.val + 1 by omega]
     exact hpf.2
   · rw [qo,fg,uj,eg]
     rw [ai _ _ _ _ (by simp [eD,iy,oL]; omega)]
     rw [aS _ _ _ _ (by simp [eD,iy]; omega)]
     simp only [List.length_append,eD,iy]
     have hsub : 13 + 2 * (ae n).length + idx.val - (13 + 2 * (ae n).length) = idx.val := by omega
     rw [hsub]
   · rw [mC,fg,uj,eg]
     rw [aS _ _ _ _ (by simp [eD,iy,oL]; omega)]
     simp only [List.length_append,eD,iy,oL]
     have hsub : 13 + 3 * (ae n).length + idx.val - (13 + 2 * (ae n).length + (ae n).length) =
         idx.val := by omega
     rw [hsub]
lemma cD {n : ℕ} (S : Finset (Fin (ae n).length)) :
   (S.image (@aa n)).card = S.card :=
 Finset.card_image_of_injective S bI
lemma bW {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ -> α) :
   ((List.range m).map f).sum = ∑ i : Fin m,f i.val := by
 rw [← bh m,List.map_map]
 simp only [Function.comp_def]
 rw [← List.sum_toFinset _ (List.nodup_finRange m),List.toFinset_finRange]
lemma dr {n : ℕ} (s : List Bool) (hn : g8 s = n) (off : ℕ)
   (R T : Finset (Fin n))
   (hR : ∀ i : Fin n,bitAt s (off + i.val) = if i ∈ R then 1 else 0)
   (hT : ∀ i : Fin n,bitAt s (off + n + i.val) = if i ∈ T then 1 else 0) :
   gf s off = if Disjoint R T then 1 else 0 := by
 unfold gf
 rw [hn]
 have hzero : ((List.range n).map (fun i => eY i (pairB (un off) s))).sum = 0 ↔
     Disjoint R T := by
   rw [aC]
   simp only [eY,unpairB_pairB,un_length,hn]
   constructor
   · intro h
     rw [Finset.disjoint_left]
     intro i wI hiT
     have h0 := h i.val i.isLt
     rw [hR i,hT i,if_pos wI,if_pos hiT] at h0
     norm_num at h0
   · intro h i hi
     have h0 := hR ⟨i,hi⟩
     have h1 := hT ⟨i,hi⟩
     rw [h0,h1]
     by_cases wI : (⟨i,hi⟩ : Fin n) ∈ R
     · have hiT : (⟨i,hi⟩ : Fin n) ∉ T := Finset.disjoint_left.mp h wI
       simp [wI,hiT]
     · simp [wI]
 by_cases hD : Disjoint R T
 · have hz := hzero.mpr hD
   simp [hz,hD]
 · have hnz : ((List.range n).map (fun i => eY i (pairB (un off) s))).sum ≠ 0 := by
     intro hz; exact hD (hzero.mp hz)
   simp [hnz,hD]
lemma gI {a n : ℕ}
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (rest : List Bool) (idx : Fin (ae n).length) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let s := header a ++ input ++ rest
   let E := (ae n).toFinset.filter (fun e =>
     ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2))
   (bD s).getD idx.val 0 = if aa idx ∈ E then 1 else 0 := by
 intro header bank input s E
 have dM : s = (header a ++ input) ++ rest := by simp only [s,List.append_assoc]
 have hp := bA a n hard soft rest
 dsimp only at hp
 rw [← dM] at hp
 rcases hp with ⟨_,bk,mI,_,_,_,_,_,_,hhard_bits,_,_⟩
 have hP : sW s = (ae n).length := by
   dsimp [sW]; rw [bk]; have := dZ n; omega
 have hlt : idx.val < (List.range (sW s)).length := by rw [List.length_range,hP]; exact idx.isLt
 rw [bD,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range (by rw [hP]; exact idx.isLt)]
 dsimp only [Option.map_some,Option.getD_some,iL]
 have hps : (unpairB (aU s)).1 = s := by unfold aU; exact congrArg Prod.fst (unpairB_pairB _ _)
 rw [hps,mI]
 have hpf := iB n s bk idx
 have hemem : aa idx ∈ ae n := List.get_mem (ae n) idx
 have hzero : ((List.range hard.length).map (fun z => fQ z (pairB (un idx.val) (aU s)))).sum = 0 ↔
     aa idx ∈ E := by
   rw [aC]
   have r9 : ∀ z (hz : z < hard.length),
       fQ z (pairB (un idx.val) (aU s)) = 0 ↔
         ¬(al (aa idx) ⊆ (hard[z]'hz).1) /\ ¬(al (aa idx) ⊆ (hard[z]'hz).2) := by
     intro z hz
     simp only [fQ,aU,unpairB_pairB,un_length,dh,bk]
     rw [hpf.1,hpf.2]
     have hb1 := (hhard_bits z hz (aa idx).1).1
     have hb2 := (hhard_bits z hz (aa idx).2).1
     have hb3 := (hhard_bits z hz (aa idx).1).2
     have hb4 := (hhard_bits z hz (aa idx).2).2
     rw [hb1,hb2,hb3,hb4]
     simp only [al,Finset.insert_subset_iff,Finset.singleton_subset_iff,not_and]
     by_cases h11 : (aa idx).1 ∈ (hard[z]'hz).1 <;>
       by_cases h21 : (aa idx).2 ∈ (hard[z]'hz).1 <;>
       by_cases h12 : (aa idx).1 ∈ (hard[z]'hz).2 <;>
       by_cases h22 : (aa idx).2 ∈ (hard[z]'hz).2 <;>
       simp [h11,h21,h12,h22]
   constructor
   · intro h
     simp only [E,Finset.mem_filter,List.mem_toFinset]
     refine ⟨hemem,fun w hw => ?_⟩
     rcases List.mem_iff_getElem.mp hw with ⟨z,hz,rfl⟩
     exact (r9 z hz).mp (h z hz)
   · intro h z hz
     simp only [E,Finset.mem_filter,List.mem_toFinset] at h
     exact (r9 z hz).mpr (h.2 (hard[z]'hz) (List.getElem_mem hz))
 by_cases hE : aa idx ∈ E
 · simp [hzero.mpr hE,hE]
 · have hnz : ((List.range hard.length).map (fun z => fQ z (pairB (un idx.val) (aU s)))).sum ≠ 0 := by
     intro hz; exact hE (hzero.mp hz)
   simp [hnz,hE]
lemma g9 {a n : ℕ}
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (rest : List Bool) (idx : Fin (ae n).length) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let s := header a ++ input ++ rest
   let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
     Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2
   let ct := fun S => (soft.filter (fun t => t.2 && decide (lists S t))).length
   let bY := fun S => (soft.filter (fun t => !t.2 && decide (lists S t))).length
   (eP s).getD idx.val 0 = (soft.length + 1) + ct {aa idx} - bY {aa idx} := by
 intro header bank input s lists ct bY
 have dM : s = (header a ++ input) ++ rest := by simp only [s,List.append_assoc]
 have hp := bA a n hard soft rest
 dsimp only at hp
 rw [← dM] at hp
 rcases hp with ⟨_,bk,_,_,_,fE,_,_,_,_,hsoft_bits,_⟩
 have hP : sW s = (ae n).length := by
   dsimp [sW]; rw [bk]; have := dZ n; omega
 rw [eP,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range (by rw [hP]; exact idx.isLt)]
 dsimp only [Option.map_some,Option.getD_some,k9]
 have hps : (unpairB (aU s)).1 = s := by unfold aU; exact congrArg Prod.fst (unpairB_pairB _ _)
 rw [hps,fE]
 have hpf := iB n s bk idx
 have hdisj : ∀ z (hz : z < soft.length),
     gf s (bi s + z * (2 * n + 1)) =
       if Disjoint (soft[z]'hz).1.1 (soft[z]'hz).1.2 then 1 else 0 := by
   intro z hz
   exact dr s bk (bi s + z * (2 * n + 1)) (soft[z]'hz).1.1 (soft[z]'hz).1.2
     (fun i => (hsoft_bits z hz).1 i |>.1) (fun i => (hsoft_bits z hz).1 i |>.2)
 have t7 : ∀ z (hz : z < soft.length),
     eO z (pairB (un idx.val) (aU s)) =
       if ((soft[z]'hz).2 && decide (lists {aa idx} (soft[z]'hz))) then 1 else 0 := by
   intro z hz
   simp only [eO,aU,unpairB_pairB,un_length,dh,bk]
   rw [hpf.1,hpf.2,hdisj z hz]
   have hb1 := ((hsoft_bits z hz).1 (aa idx).1).1
   have hb2 := ((hsoft_bits z hz).1 (aa idx).2).1
   have hb3 := ((hsoft_bits z hz).1 (aa idx).1).2
   have hb4 := ((hsoft_bits z hz).1 (aa idx).2).2
   have hlab := (hsoft_bits z hz).2
   rw [hb1,hb2,hb3,hb4,hlab]
   simp only [lists,Finset.mem_singleton,forall_eq,al,Finset.insert_subset_iff,
     Finset.singleton_subset_iff]
   by_cases hd : Disjoint (soft[z]'hz).1.1 (soft[z]'hz).1.2 <;>
     by_cases h11 : (aa idx).1 ∈ (soft[z]'hz).1.1 <;>
     by_cases h21 : (aa idx).2 ∈ (soft[z]'hz).1.1 <;>
     by_cases h12 : (aa idx).1 ∈ (soft[z]'hz).1.2 <;>
     by_cases h22 : (aa idx).2 ∈ (soft[z]'hz).1.2 <;>
     cases (soft[z]'hz).2 <;>
     simp [hd,h11,h21,h12,h22]
 have t6 : ∀ z (hz : z < soft.length),
     eo z (pairB (un idx.val) (aU s)) =
       if (!(soft[z]'hz).2 && decide (lists {aa idx} (soft[z]'hz))) then 1 else 0 := by
   intro z hz
   simp only [eo,aU,unpairB_pairB,un_length,dh,bk]
   rw [hpf.1,hpf.2,hdisj z hz]
   have hb1 := ((hsoft_bits z hz).1 (aa idx).1).1
   have hb2 := ((hsoft_bits z hz).1 (aa idx).2).1
   have hb3 := ((hsoft_bits z hz).1 (aa idx).1).2
   have hb4 := ((hsoft_bits z hz).1 (aa idx).2).2
   have hlab := (hsoft_bits z hz).2
   rw [hb1,hb2,hb3,hb4,hlab]
   simp only [lists,Finset.mem_singleton,forall_eq,al,Finset.insert_subset_iff,
     Finset.singleton_subset_iff]
   by_cases hd : Disjoint (soft[z]'hz).1.1 (soft[z]'hz).1.2 <;>
     by_cases h11 : (aa idx).1 ∈ (soft[z]'hz).1.1 <;>
     by_cases h21 : (aa idx).2 ∈ (soft[z]'hz).1.1 <;>
     by_cases h12 : (aa idx).1 ∈ (soft[z]'hz).1.2 <;>
     by_cases h22 : (aa idx).2 ∈ (soft[z]'hz).1.2 <;>
     cases (soft[z]'hz).2 <;>
     simp [hd,h11,h21,h12,h22]
 have uF : ((List.range soft.length).map (fun z => eO z (pairB (un idx.val) (aU s)))).sum =
     ct {aa idx} := by
   have h1 : (List.range soft.length).map (fun z => eO z (pairB (un idx.val) (aU s))) =
       (List.range soft.length).map (fun z =>
         if h : z < soft.length then
           if ((soft[z]'h).2 && decide (lists {aa idx} (soft[z]'h))) then 1 else 0
         else 0) := by
     apply List.map_congr_left
     intro z hz
     have hlt : z < soft.length := List.mem_range.mp hz
     simp [hlt,t7 z hlt]
   rw [h1,aT soft (fun t => t.2 && decide (lists {aa idx} t))]
 have vi : ((List.range soft.length).map (fun z => eo z (pairB (un idx.val) (aU s)))).sum =
     bY {aa idx} := by
   have h1 : (List.range soft.length).map (fun z => eo z (pairB (un idx.val) (aU s))) =
       (List.range soft.length).map (fun z =>
         if h : z < soft.length then
           if (!(soft[z]'h).2 && decide (lists {aa idx} (soft[z]'h))) then 1 else 0
         else 0) := by
     apply List.map_congr_left
     intro z hz
     have hlt : z < soft.length := List.mem_range.mp hz
     simp [hlt,t6 z hlt]
   rw [h1,aT soft (fun t => !t.2 && decide (lists {aa idx} t))]
 rw [uF,vi]
lemma iC {a n : ℕ}
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (rest : List Bool) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let s := header a ++ input ++ rest
   eT s =
     (soft.filter (fun t => decide (ak (∅ : Finset (Fin n × Fin n))
       (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length := by
 intro header bank input s
 have dM : s = (header a ++ input) ++ rest := by simp only [s,List.append_assoc]
 have hp := bA a n hard soft rest
 dsimp only at hp
 rw [← dM] at hp
 rcases hp with ⟨_,bk,_,_,_,fE,_,_,_,_,hsoft_bits,_⟩
 have hM0 : IsMatching n (∅ : Finset (Fin n × Fin n)) := ⟨fun _ h => by simp at h,fun _ h => by simp at h⟩
 have hitem : ∀ z (hz : z < soft.length),
     fM z s = if (ak (∅ : Finset (Fin n × Fin n))
       (fun i => decide (i ∈ (soft[z]'hz).1.1)) (fun j => decide (j ∈ (soft[z]'hz).1.2)) = (soft[z]'hz).2)
     then 1 else 0 := by
   intro z hz
   have hdisj := dr s bk (bi s + z * (2 * n + 1))
     (soft[z]'hz).1.1 (soft[z]'hz).1.2
     (fun i => (hsoft_bits z hz).1 i |>.1) (fun i => (hsoft_bits z hz).1 i |>.2)
   have yC : ak (∅ : Finset (Fin n × Fin n))
       (fun i => decide (i ∈ (soft[z]'hz).1.1)) (fun j => decide (j ∈ (soft[z]'hz).1.2)) = false ↔
       Disjoint (soft[z]'hz).1.1 (soft[z]'hz).1.2 := by
     rw [bK hM0]
     simp
   simp only [fM,bk,hdisj,(hsoft_bits z hz).2]
   by_cases hd : Disjoint (soft[z]'hz).1.1 (soft[z]'hz).1.2
   · have hf : ak (∅ : Finset (Fin n × Fin n))
         (fun i => decide (i ∈ (soft[z]'hz).1.1)) (fun j => decide (j ∈ (soft[z]'hz).1.2)) = false :=
       yC.mpr hd
     cases hlab : (soft[z]'hz).2 <;> simp [hd,hf,hlab]
   · have ht : ak (∅ : Finset (Fin n × Fin n))
         (fun i => decide (i ∈ (soft[z]'hz).1.1)) (fun j => decide (j ∈ (soft[z]'hz).1.2)) = true := by
       cases hv : ak (∅ : Finset (Fin n × Fin n))
           (fun i => decide (i ∈ (soft[z]'hz).1.1)) (fun j => decide (j ∈ (soft[z]'hz).1.2))
       · exfalso; exact hd (yC.mp hv)
       · rfl
     cases hlab : (soft[z]'hz).2 <;> simp [hd,ht,hlab]
 unfold eT
 rw [fE]
 have h1 : (List.range soft.length).map (fun z => fM z s) =
     (List.range soft.length).map (fun z =>
       if h : z < soft.length then
         if ak (∅ : Finset (Fin n × Fin n))
           (fun i => decide (i ∈ (soft[z]'h).1.1)) (fun j => decide (j ∈ (soft[z]'h).1.2)) = (soft[z]'h).2
         then 1 else 0
       else 0) := by
   apply List.map_congr_left
   intro z hz
   have hlt : z < soft.length := List.mem_range.mp hz
   simp [hlt,hitem z hlt]
 rw [h1]
 convert bV soft (fun t =>
   ak (∅ : Finset (Fin n × Fin n))
     (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2)
lemma oN {a n : ℕ}
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (rest : List Bool) (t : ℕ) (idx : Fin (ae n).length) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let s := header a ++ input ++ rest
   (bF t (aE s)).getD idx.val 0 =
     iz s * (eP s).getD idx.val 0 +
     az (ow s) rest ((t * (ae n).length + idx.val) * (ow s)) := by
 intro header bank input s
 have dM : s = (header a ++ input) ++ rest := by simp only [s,List.append_assoc]
 have hp := bA a n hard soft rest
 dsimp only at hp
 rw [← dM] at hp
 rcases hp with ⟨_,bk,_,_,_,_,_,_,_,_,_,hrest⟩
 have hm := aX s bk
 dsimp only at hm
 rcases hm with ⟨hmS,_,_,_,hmLpref,hmP,hmb,hmU,hmB,_,_,_,hidx_m⟩
 have hlt : idx.val < mP (aE s) := by rw [hmP]; exact idx.isLt
 rw [bF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hlt]
 dsimp only [Option.map_some,Option.getD_some]
 rw [nW,hmS,hmLpref,hmP,hmb,hmU,hmB,(hidx_m idx).2.2.2]
 have hbits : ((List.range (ow s)).map (fun h =>
     bitAt s (ef s + (t * (ae n).length + idx.val) * ow s + h) * (ui s / 2 ^ (h + 1)))).sum =
     ((List.range (ow s)).map (fun h =>
     bitAt rest ((t * (ae n).length + idx.val) * ow s + h) * (ui s / 2 ^ (h + 1)))).sum := by
   apply congrArg List.sum
   apply List.map_congr_left
   intro h _
   congr 1
   simp only [bitAt,add_assoc]
   rw [hrest]
 rw [hbits]
 exact lC (ow s) (ui s) (iz s) rfl rest
   ((t * (ae n).length + idx.val) * ow s) ((eP s).getD idx.val 0)
lemma jf {n L : ℕ} (i j : Fin n) (r : Fin L) :
   let pos := (i.val * n + j.val) * L + r.val
   pos < n * n * L /\
   pos / (n * L) = i.val /\
   (pos % (n * L)) / L = j.val /\
   (pos % (n * L)) % L = r.val := by
 intro pos
 have hL : 0 < L := Nat.zero_lt_of_lt r.isLt
 have h1 : j.val * L + r.val < n * L := by nlinarith [j.isLt,r.isLt]
 have oz : pos = i.val * (n * L) + (j.val * L + r.val) := by
   dsimp [pos]; ring
 have hdiv : pos / (n * L) = i.val := by
   rw [oz,Nat.add_comm,Nat.mul_comm i.val _,Nat.add_mul_div_left _ _ (by nlinarith [i.isLt,hL]),
     Nat.div_eq_of_lt h1,zero_add]
 have hmod : pos % (n * L) = j.val * L + r.val := by
   rw [oz,Nat.add_comm,Nat.mul_comm i.val _,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h1]
 have xp : (j.val * L + r.val) / L = j.val := by
   rw [Nat.add_comm,Nat.mul_comm j.val L,Nat.add_mul_div_left _ _ hL,Nat.div_eq_of_lt r.isLt,zero_add]
 have xD : (j.val * L + r.val) % L = r.val := by
   rw [Nat.add_comm,Nat.mul_comm j.val L,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt]
 refine ⟨?_,hdiv,?_,?_⟩
 · nlinarith [i.isLt,h1]
 · rw [hmod,xp]
 · rw [hmod,xD]
def gQ (n L : ℕ) (v : List ℕ) (M : Fin n -> Fin n -> Fin L -> Bool) : Prop :=
 v.length = n * n * L /\ ∀ i j : Fin n,∀ r : Fin L,
   v.getD ((i.val * n + j.val) * L + r.val) 0 = if M i j r then 1 else 0
lemma kw {α : Type*} (l : List α) (g : α -> Bool) (acc0 : Bool) :
   (if l.foldl (fun acc x => xor acc (g x)) acc0 then 1 else 0) =
     ((if acc0 then 1 else 0) + (l.map (fun x => if g x then 1 else 0)).sum) % 2 := by
 induction l generalizing acc0 with
 | nil => cases acc0 <;> simp
 | cons a l ih =>
   rw [List.foldl_cons,List.map_cons,List.sum_cons,ih]
   cases acc0 <;> cases g a <;> simp <;> omega
lemma fN {n L : ℕ} (lo : ℕ) (f : Fin n -> Fin L -> Bool) (r : Fin L) :
   (if gy n lo f r then 1 else 0) =
     ((List.range n).map (fun k => if hk : k < n then
       if lo ≤ k then (if f ⟨k,hk⟩ r then 1 else 0) else 0 else 0)).sum % 2 := by
 unfold gy
 have yY : ∀ (l : List (Fin n)) (acc0 : Fin L -> Bool),
     (l.foldl (fun acc k => fc acc (f k)) acc0) r =
       l.foldl (fun b k => xor b (f k r)) (acc0 r) := by
   intro l acc0
   induction l generalizing acc0 with
   | nil => rfl
   | cons a l ih =>
     simp only [List.foldl_cons]
     exact ih (fc acc0 (f a))
 rw [yY]
 rw [kw]
 simp only [nk,Bool.false_eq_true,↓reduceIte,zero_add]
 congr 1
 rw [← bh n,List.map_map]
 have hmap : ∀ l : List (Fin n),
     ((l.filter (fun k => decide (lo ≤ k.val))).map (fun k => if f k r then 1 else 0)).sum =
     (l.map (fun k => if hk : k.val < n then
       if lo ≤ k.val then (if f ⟨k.val,hk⟩ r then 1 else 0) else 0 else 0)).sum := by
   intro l
   induction l with
   | nil => simp
   | cons a l ih =>
     simp only [List.filter_cons,List.map_cons,List.sum_cons,a.isLt,↓reduceDIte]
     by_cases hlo : lo ≤ a.val
     · simp [hlo,ih]
     · simp [hlo,ih]
 exact hmap (List.finRange n)
lemma nh {n : ℕ} (s : List Bool) (hn : g8 s = n)
   (t aI : ℕ) (deg : Fin (ae n).length -> ℕ)
   (hdeg : ∀ idx : Fin (ae n).length,(bF t (aE s)).getD idx.val 0 = deg idx) :
   let env := aE s
   let L := am s
   let act : Fin (ae n).length -> Bool := fun idx => decide ((bD s).getD idx.val 0 ≠ 0)
   let cw : Fin (ae n).length -> Bool := fun idx => act idx && decide (idx.val ≠ aI)
   gQ n L (bS (pairB (aM (bF t env)) (pairB (un aI) env)))
     (bn n L cw deg) := by
 intro env L act cw
 have hm := aX s hn
 dsimp only at hm
 rcases hm with ⟨_,_,hmN,_,_,hmP,_,_,_,hmLbuf,_,_,hidx_m⟩
 refine ⟨?_,?_⟩
 · simp only [bS,List.length_map,List.length_range,unpairB_pairB]
   dsimp only [env]
   rw [hmN,hmLbuf]
 · intro i j r
   have hpd := jf i j r
   dsimp only at hpd
   rcases hpd with ⟨hlt,hdiv,hjdiv,hrmod⟩
   have qK : ((i.val * n + j.val) * L + r.val) < mN env * mN env * ez env := by
     rw [hmN,hmLbuf]; exact hlt
   rw [bS,List.getD_eq_getElem?_getD,List.getElem?_map,
     List.getElem?_range (by simpa [unpairB_pairB] using qK)]
   dsimp only [Option.map_some,Option.getD_some,gU]
   rw [unpairB_pairB,unpairB_pairB]
   dsimp only [env]
   rw [hmN,hmP,hmLbuf,hdiv,hjdiv,hrmod]
   by_cases hij : i = j
   · subst hij
     simp only [bn,if_pos rfl]
     by_cases hr : r.val = 0 <;> simp [hr]
   · have vG : i.val ≠ j.val := fun h => hij (Fin.ext h)
     rw [if_neg vG]
     simp only [bn,if_neg hij]
     have hterm : ∀ idx : Fin (ae n).length,
         dH idx.val (pairB (un ((i.val * n + j.val) * L + r.val))
           (pairB (aM (bF t env)) (pairB (un aI) env))) =
         if (cw idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
           decide (r.val = deg idx)) then 1 else 0 := by
       intro idx
       have zW := (hidx_m idx).1
       have z7 := (hidx_m idx).2.1
       have zF := (hidx_m idx).2.2.1
       have xF : (bF t (aE s)).getD idx.val 0 = deg idx := hdeg idx
       simp only [dH,unpairB_pairB,un_length,dh]
       dsimp only [env] at hmN hmLbuf ⊢
       rw [hmN,hmLbuf,hdiv,hjdiv,hrmod,xF,zW,z7,zF]
       have xi : ((aa idx == (i,j)) || (aa idx == (j,i))) =
           ((aa idx).1.val == i.val && (aa idx).2.val == j.val ||
            (aa idx).1.val == j.val && (aa idx).2.val == i.val) := by
         apply Bool.eq_iff_iff.mpr
         simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,Prod.ext_iff,Fin.ext_iff]
       rw [xi]
       dsimp only [cw,act]
       have uJ : (bD s).getD idx.val 0 = 0 \/ (bD s).getD idx.val 0 = 1 := by
         have xE : sW s = (ae n).length := by
           dsimp [sW]; rw [hn]; have := dZ n; omega
         simp only [bD,xE,List.getD_eq_getElem?_getD,List.getElem?_map,
           List.getElem?_range idx.isLt,Option.map_some,Option.getD_some,iL]
         split_ifs <;> simp
       exact oR idx.val aI ((bD s).getD idx.val 0) (aa idx).1.val (aa idx).2.val
         i.val j.val r.val (deg idx) uJ
     have hsum : ((List.range (ae n).length).map (fun idx =>
         dH idx (pairB (un ((i.val * n + j.val) * L + r.val))
           (pairB (aM (bF t env)) (pairB (un aI) env))))).sum =
         ((List.finRange (ae n).length).filter (fun idx =>
           cw idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
           decide (r.val = deg idx))).length := by
       have h1 : (List.range (ae n).length).map (fun idx =>
           dH idx (pairB (un ((i.val * n + j.val) * L + r.val))
             (pairB (aM (bF t env)) (pairB (un aI) env)))) =
           (List.range (ae n).length).map (fun idx =>
             if h : idx < (ae n).length then
               if (cw ⟨idx,h⟩ && ((aa ⟨idx,h⟩ == (i,j)) || (aa ⟨idx,h⟩ == (j,i))) &&
                 decide (r.val = deg ⟨idx,h⟩)) then 1 else 0
             else 0) := by
         apply List.map_congr_left
         intro k hk
         have hlt' : k < (ae n).length := List.mem_range.mp hk
         simp [hlt',hterm ⟨k,hlt'⟩]
       rw [h1,aW (ae n).length
         (fun idx => cw idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
           decide (r.val = deg idx))]
     rw [hsum]
     rcases Nat.mod_two_eq_zero_or_one ((List.finRange (ae n).length).filter (fun idx =>
         cw idx && ((aa idx == (i,j)) || (aa idx == (j,i))) &&
         decide (r.val = deg idx))).length with hmod | hmod <;> simp [hmod]
lemma nu {n : ℕ} (s : List Bool) (hn : g8 s = n)
   (t aI : ℕ) (ss sO : List ℕ) (en lV : Fin n -> Fin n -> Fin (am s) -> Bool)
   (hA : gQ n (am s) ss en) (hF : gQ n (am s) sO lV) :
   let env := aE s
   let aA := pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env))
   gQ n (am s) (aO (pairB (aM sO) aA))
     (dm n (am s) en lV) := by
 intro env aA
 have hm := aX s hn
 dsimp only at hm
 rcases hm with ⟨_,_,hmN,_,_,_,_,_,_,hmLbuf,_,_,_⟩
 refine ⟨?_,?_⟩
 · simp only [aO,aA,List.length_map,List.length_range]
   rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,unpairB_pairB]
   dsimp only [env]
   rw [hmN,hmLbuf]
 · intro i j r
   have hL : 0 < am s := Nat.zero_lt_of_lt r.isLt
   have hpd := jf i j r
   dsimp only at hpd
   rcases hpd with ⟨hlt,hdiv,hjdiv,hrmod⟩
   have qK : ((i.val * n + j.val) * am s + r.val) < mN env * mN env * ez env := by
     rw [hmN,hmLbuf]; exact hlt
   rw [aO,List.getD_eq_getElem?_getD,List.getElem?_map,
     List.getElem?_range (by simpa [aA,unpairB_pairB] using qK)]
   dsimp only [Option.map_some,Option.getD_some,dl,aA]
   rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,unpairB_pairB]
   dsimp only [env]
   rw [hmN,hmLbuf]
   have ht1 : ((List.range (am s)).map (fun q =>
       cJ q (pairB (un ((i.val * n + j.val) * am s + r.val))
         (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env))))))).sum % 2 =
       if cI (gy n (i.val + 1) (fun k => lV k k)) (en i j) r then 1 else 0 := by
     have hitem : ∀ q (hq : q < am s),
         cJ q (pairB (un ((i.val * n + j.val) * am s + r.val))
           (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env))))) =
         if (decide (q ≤ r.val) && gy n (i.val + 1) (fun k => lV k k) ⟨q,hq⟩ &&
           en i j ⟨r.val - q,by omega⟩) then 1 else 0 := by
       intro q hq
       dsimp only [cJ]
       simp only [unpairB_pairB,un_length,dh]
       dsimp only [env] at hmN hmLbuf ⊢
       rw [hmN,hmLbuf,hdiv,hjdiv,hrmod]
       by_cases hqr : q ≤ r.val
       · rw [if_pos hqr]
         have wE : ((List.range n).map (fun k =>
             eC k (pairB (un q) (pairB (un ((i.val * n + j.val) * am s + r.val))
               (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env)))))))).sum % 2 =
             if gy n (i.val + 1) (fun k => lV k k) ⟨q,hq⟩ then 1 else 0 := by
           rw [fN]
           congr 1; congr 1
           apply List.map_congr_left
           intro k hk
           have iT : k < n := List.mem_range.mp hk
           dsimp only [eC]
           simp only [unpairB_pairB,un_length,dh]
           dsimp only [env] at hmN hmLbuf ⊢
           rw [hmN,hmLbuf,hdiv]
           simp only [iT,↓reduceDIte]
           by_cases hik : i.val + 1 ≤ k
           · rw [if_pos hik,if_pos hik,hF.2 ⟨k,iT⟩ ⟨k,iT⟩ ⟨q,hq⟩]
           · simp [hik]
         rw [wE,hA.2 i j ⟨r.val - q,by omega⟩]
         cases gy n (i.val + 1) (fun k => lV k k) ⟨q,hq⟩ <;>
           cases en i j ⟨r.val - q,by omega⟩ <;> simp [hqr]
       · rw [if_neg hqr]
         simp [hqr]
     have h1 : (List.range (am s)).map (fun q =>
           cJ q (pairB (un ((i.val * n + j.val) * am s + r.val))
             (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env)))))) =
         (List.range (am s)).map (fun q =>
           if hq : q < am s then
             if (decide (q ≤ r.val) && gy n (i.val + 1) (fun k => lV k k) ⟨q,hq⟩ &&
               en i j ⟨r.val - q,by omega⟩) then 1 else 0
           else 0) := by
       apply List.map_congr_left
       intro q hq
       have vx : q < am s := List.mem_range.mp hq
       simp [vx,hitem q vx]
     rw [h1,aW (am s)
       (fun q : Fin (am s) => decide (q.val ≤ r.val) &&
         gy n (i.val + 1) (fun k => lV k k) q && en i j ⟨r.val - q.val,by omega⟩)]
     simp only [cI]
     exact jI _
   have ht2 : ((List.range n).map (fun k =>
       dL k (pairB (un ((i.val * n + j.val) * am s + r.val))
         (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env))))))).sum % 2 =
       if gy n (i.val + 1) (fun k => cI (lV i k) (en k j)) r then 1 else 0 := by
     rw [fN]
     congr 1; congr 1
     apply List.map_congr_left
     intro k hk
     have iT : k < n := List.mem_range.mp hk
     dsimp only [dL]
     simp only [unpairB_pairB,un_length]
     dsimp only [env] at hmN hmLbuf ⊢
     rw [hmN,hmLbuf,hdiv]
     simp only [iT,↓reduceDIte]
     by_cases hik : i.val + 1 ≤ k
     · rw [if_pos hik,if_pos hik]
       have vI : ∀ q (hq : q < am s),
           da q (pairB (un k) (pairB (un ((i.val * n + j.val) * am s + r.val))
             (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env)))))) =
           if (decide (q ≤ r.val) && lV i ⟨k,iT⟩ ⟨q,hq⟩ &&
             en ⟨k,iT⟩ j ⟨r.val - q,by omega⟩) then 1 else 0 := by
         intro q hq
         dsimp only [da]
         simp only [unpairB_pairB,un_length,dh]
         dsimp only [env] at hmN hmLbuf ⊢
         rw [hmN,hmLbuf,hdiv,hjdiv,hrmod]
         by_cases hqr : q ≤ r.val
         · rw [if_pos hqr,hF.2 i ⟨k,iT⟩ ⟨q,hq⟩,hA.2 ⟨k,iT⟩ j ⟨r.val - q,by omega⟩]
           cases lV i ⟨k,iT⟩ ⟨q,hq⟩ <;> cases en ⟨k,iT⟩ j ⟨r.val - q,by omega⟩ <;> simp [hqr]
         · rw [if_neg hqr]; simp [hqr]
       have h1 : (List.range (am s)).map (fun q =>
             da q (pairB (un k) (pairB (un ((i.val * n + j.val) * am s + r.val))
               (pairB (aM sO) (pairB (aM ss) (pairB (aM (bF t env)) (pairB (un aI) env))))))) =
           (List.range (am s)).map (fun q =>
             if hq : q < am s then
               if (decide (q ≤ r.val) && lV i ⟨k,iT⟩ ⟨q,hq⟩ &&
                 en ⟨k,iT⟩ j ⟨r.val - q,by omega⟩) then 1 else 0
             else 0) := by
         apply List.map_congr_left
         intro q hq
         have vx : q < am s := List.mem_range.mp hq
         simp [vx,vI q vx]
       rw [h1,aW (am s)
         (fun q : Fin (am s) => decide (q.val ≤ r.val) && lV i ⟨k,iT⟩ q &&
           en ⟨k,iT⟩ j ⟨r.val - q.val,by omega⟩)]
       simp only [cI]
       exact jI _
     · simp [hik]
   rw [ht1,ht2]
   simp only [dm,fc]
   cases cI (gy n (i.val + 1) (fun k => lV k k)) (en i j) r <;>
     cases gy n (i.val + 1) (fun k => cI (lV i k) (en k j)) r <;>
     decide
lemma ig {n : ℕ} (s : List Bool) (bk : g8 s = n) (hn : 2 ≤ n)
   (t aI : ℕ) (deg : Fin (ae n).length -> ℕ)
   (hdeg : ∀ idx : Fin (ae n).length,(bF t (aE s)).getD idx.val 0 = deg idx) :
   let env := aE s
   let L := am s
   let act : Fin (ae n).length -> Bool := fun idx => decide ((bD s).getD idx.val 0 ≠ 0)
   let cw : Fin (ae n).length -> Bool := fun idx => act idx && decide (idx.val ≠ aI)
   (bm (pairB (aM (bF t env)) (pairB (un aI) env))).length = L /\
   ∀ r : Fin L,
     (bm (pairB (aM (bF t env)) (pairB (un aI) env))).getD r.val 0 =
       if dt n L (bn n L cw deg) r then 1 else 0 := by
 intro env L act cw
 have hm := aX s bk
 dsimp only at hm
 rcases hm with ⟨_,_,hmN,_,_,_,_,_,_,hmLbuf,_,_,_⟩
 let fD := pairB (aM (bF t env)) (pairB (un aI) env)
 let ss := bS fD
 let aA := pairB (aM ss) fD
 let en := bn n L cw deg
 have hinit : gQ n L ss en := nh s bk t aI deg hdeg
 have rX : ∀ k : ℕ,∃ sO : List ℕ,
     ((fun a => aM (aO (pairB a aA)))^[k] (aM ss)) = aM sO /\
     gQ n L sO ((dm n L en)^[k] en) := by
   intro k
   induction k with
   | zero =>
     simp only [Function.iterate_zero,id_eq]
     exact ⟨ss,rfl,hinit⟩
   | succ k ih =>
     rcases ih with ⟨sO,hFk,hFrep⟩
     simp only [Function.iterate_succ_apply',hFk]
     refine ⟨aO (pairB (aM sO) aA),rfl,?_⟩
     exact nu s bk t aI ss sO en ((dm n L en)^[k] en) hinit hFrep
 have hn0 : 0 < n := by omega
 rcases rX (n - 1) with ⟨F_final,hF_eq,hlast_rep⟩
 have uM : fP fD = aM F_final := by
   rw [oW]
   have zP : mN env = n := hmN
   simp only [fD,unpairB_pairB,zP]
   dsimp only [ss,aA] at hF_eq
   exact hF_eq
 refine ⟨?_,?_⟩
 · have qZ : ez env = L := hmLbuf
   simp [bm,fD,unpairB_pairB,qZ]
 · intro r
   have qZ : ez env = L := hmLbuf
   rw [bm,List.getD_eq_getElem?_getD,List.getElem?_map,
     List.getElem?_range (by simpa [fD,unpairB_pairB,qZ] using r.isLt)]
   dsimp only [Option.map_some,Option.getD_some,gL]
   rw [uM,dh]
   have h00 := hlast_rep.2 ⟨0,hn0⟩ ⟨0,hn0⟩ r
   simp only [zero_mul,zero_add] at h00
   rw [h00,dt,dif_pos hn0]
def uy (a n : ℕ) (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool)) : List Bool :=
 let header := fun j : ℕ => List.replicate j true ++ [false]
 let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
 let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
   header soft.length ++ soft.flatMap (fun u => bank u.1.1 ++ bank u.1.2 ++ [u.2])
 header a ++ input
lemma eu {a n : ℕ}
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (tape : List Bool) (hn : 2 ≤ n) (t aI : ℕ) (ht : t < a + n + soft.length + 2)
   (qT : aI ≤ (ae n).length) (r : ℕ)
   (hr : r < am (uy a n hard soft ++ tape)) :
   let s := uy a n hard soft ++ tape
   let P := (ae n).length
   let L := am s
   let act : Fin P -> Bool := fun idx => decide ((bD s).getD idx.val 0 ≠ 0)
   let cw : Fin P -> Bool := fun idx => act idx && decide (idx.val ≠ aI)
   let deg : Fin P -> ℕ := fun idx => iz s * (eP s).getD idx.val 0 +
     az (ow s) tape ((t * P + idx.val) * (ow s))
   (bl s).getD ((t * (P + 1) + aI) * L + r) 0 =
     if dt n L (bn n L cw deg) ⟨r,hr⟩ then 1 else 0 := by
 intro s P L act cw deg
 let r' : Fin L := ⟨r,hr⟩
 have hp := bA a n hard soft tape
 dsimp only at hp
 change _ at hp
 have yw : s = (List.replicate a true ++ [false] ++
     ((List.replicate n true ++ [false]) ++ (List.replicate hard.length true ++ [false]) ++
       hard.flatMap (fun z => (List.finRange n).map (fun i => decide (i ∈ z.1)) ++
         (List.finRange n).map (fun i => decide (i ∈ z.2))) ++
       (List.replicate soft.length true ++ [false]) ++
       soft.flatMap (fun t => (List.finRange n).map (fun i => decide (i ∈ t.1.1)) ++
         (List.finRange n).map (fun i => decide (i ∈ t.1.2)) ++ [t.2]))) ++ tape := rfl
 rw [← yw] at hp
 rcases hp with ⟨nI,bk,_,_,_,fE,_,_,_,_,_,_⟩
 have hm := aX s bk
 dsimp only at hm
 rcases hm with ⟨_,_,_,_,_,hmP,_,_,_,hmLbuf,_,_,_⟩
 have vo : s7 s = a + n + soft.length + 2 := by
   dsimp [s7]; rw [nI,bk,fE]
 have om : ∀ u : ℕ,∀ idx : Fin P,(bF u (aE s)).getD idx.val 0 =
     iz s * (eP s).getD idx.val 0 + az (ow s) tape ((u * P + idx.val) * ow s) := by
   intro u idx
   exact oN hard soft tape u idx
 have uG : ∀ u ∈ List.range (s7 s),(gO u (aE s)).length = (P + 1) * L := by
   intro u _
   rw [jF,hmP]
   have tX : ∀ j ∈ List.range (P + 1),
       (bm (pairB (aM (bF u (aE s))) (pairB (un j) (aE s)))).length = L := by
     intro j _
     exact (ig s bk hn u j _ (om u)).1
   clear om
   have ld : ∀ (l : List ℕ),(∀ j ∈ l,(bm (pairB (aM (bF u (aE s))) (pairB (un j) (aE s)))).length = L) ->
       (l.flatMap (fun j => bm (pairB (aM (bF u (aE s))) (pairB (un j) (aE s))))).length = l.length * L := by
     intro l hl
     induction l with
     | nil => simp
     | cons x xs ih =>
       simp only [List.flatMap_cons,List.length_append,List.length_cons,
         hl x (List.mem_cons_self ..),ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
       ring
   rw [ld (List.range (P + 1)) tX,List.length_range]
 have oz : (t * (P + 1) + aI) * L + r = t * ((P + 1) * L) + (aI * L + r) := by
   ring
 have vL : aI * L + r < (P + 1) * L := by
   nlinarith [qT,hr]
 have u6 : t < (List.range (s7 s)).length := by rw [List.length_range,vo]; exact ht
 rw [oz,bl]
 rw [aJ (List.range (s7 s)) (fun u => gO u (aE s)) ((P + 1) * L)
   uG 0 t (aI * L + r'.val) u6 vL]
 have xq : (List.range (s7 s))[t]'u6 = t := by simp
 rw [xq,jF,hmP]
 have ud : ∀ j ∈ List.range (P + 1),
     (bm (pairB (aM (bF t (aE s))) (pairB (un j) (aE s)))).length = L :=
   fun j _ => (ig s bk hn t j _ (om t)).1
 have rN : aI < (List.range (P + 1)).length := by rw [List.length_range]; omega
 rw [aJ (List.range (P + 1))
   (fun j => bm (pairB (aM (bF t (aE s))) (pairB (un j) (aE s))))
   L ud 0 aI r rN hr]
 have ve : (List.range (P + 1))[aI]'rN = aI := by simp
 rw [ve]
 exact (ig s bk hn t aI deg (om t)).2 r'
lemma jn (B : ℕ) (P : ℕ -> Bool) (w0 : ℕ) (hw0 : w0 < B)
   (hP0 : P w0 = true) (hmin : ∀ w < w0,P w = false) :
   let l := (List.range B).flatMap (fun w => if P w = true then [w] else [])
   0 < l.length /\ l.getD 0 0 = w0 := by
 intro l
 have hhead : ∀ (a k : ℕ),a ≤ w0 -> w0 < a + k -> (∀ w,a ≤ w -> w < w0 -> P w = false) ->
     ((List.range' a k).flatMap (fun w => if P w = true then [w] else [])).head? = some w0 := by
   intro a k hak hlt vz
   induction k generalizing a with
   | zero => omega
   | succ k ih =>
     rw [List.range'_succ,List.flatMap_cons]
     by_cases haw : a = w0
     · subst haw
       simp [hP0]
     · have yE : a < w0 := by omega
       have hPa : P a = false := vz a (le_refl a) yE
       simp only [hPa,Bool.false_eq_true,↓reduceIte,List.nil_append]
       exact ih (a + 1) (by omega) (by omega) (fun w hw1 hw2 => vz w (by omega) hw2)
 have yf : l = (List.range' 0 B).flatMap (fun w => if P w = true then [w] else []) := by
   simp [l,List.range_eq_range']
 have h0 := hhead 0 B (Nat.zero_le w0) (by omega) (fun w _ hw => hmin w hw)
 rw [← yf] at h0
 cases hl : l with
 | nil => simp [hl] at h0
 | cons x xs =>
   simp only [hl,List.head?_cons,Option.some.injEq] at h0
   subst h0
   simp
noncomputable def cZ (n a : ℕ)
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (ell : ℕ) (tape : Fin ell -> Bool) (aw : Fin (n / 2 + 1)) (ay : Fin (soft.length + 1)) : List Bool :=
 let header := fun j : ℕ => List.replicate j true ++ [false]
 let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
 let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
   header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
 let s := header a ++ input ++ List.ofFn tape
 let fe := ah s
 let ts := bP aw.val ay.val fe
 if ts.length = 0 then [] else (bN (ts.getD 0 0) aw.val ay.val fe).map (fun x => decide (x ≠ 0))
lemma qu (n a : ℕ) (hn : 2 ≤ n)
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (ell : ℕ) (tape : Fin ell -> Bool) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let prefixBits := header a ++ input
   let pairs := fun k : ℕ => (List.finRange k).flatMap (fun i =>
     ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
   let slots := (List.finRange (n / 2 + 1)).flatMap (fun s =>
     (List.finRange (soft.length + 1)).map (fun j => (s,j)))
   let enc := fun word : List Bool => if word.isEmpty then List.replicate ((pairs n).length + 1) false
     else true :: word
   jG (prefixBits ++ List.ofFn tape) = slots.flatMap (fun z => enc (cZ n a hard soft ell tape z.1 z.2)) := by
 intro header bank input prefixBits pairs slots enc
 have dM : prefixBits ++ List.ofFn tape = (header a ++ input) ++ List.ofFn tape := rfl
 have hp := bA a n hard soft (List.ofFn tape)
 dsimp only at hp
 rcases hp with ⟨_,bk,_,_,_,fE,_,_,_,_,_,_⟩
 let s := prefixBits ++ List.ofFn tape
 have hm := aX s bk
 dsimp only at hm
 rcases hm with ⟨_,_,_,_,_,hmP,_,_,_,_,_,_,_⟩
 have uK : 0 < (ae n).length := by
   have := dZ n
   have hn1 : 1 ≤ n - 1 := by omega
   have : 2 ≤ n * (n - 1) := by nlinarith
   omega
 have uf : pairs n = ae n := rfl
 rw [jG,pQ,bk,fE]
 rw [List.map_flatMap,← bh (n / 2 + 1),List.flatMap_map]
 simp only [slots,List.flatMap_assoc,List.flatMap_map,Function.comp_def]
 apply congrArg (List.flatMap · (List.finRange (n / 2 + 1)))
 funext aw
 rw [List.map_flatMap,← bh (soft.length + 1),List.flatMap_map]
 apply congrArg (List.flatMap · (List.finRange (soft.length + 1)))
 funext ay
 dsimp only [Function.comp_def,enc,mF]
 change ((if (bP aw.val ay.val (ah s)).length = 0 then
     (List.range (mP (unpairB (ah s)).2 + 1)).map (fun _ => 0)
   else 1 :: bN ((bP aw.val ay.val (ah s)).getD 0 0) aw.val ay.val (ah s)).map
     (fun x => decide (x ≠ 0))) = _
 have s6 : mP (unpairB (ah s)).2 = (ae n).length := by
   simpa [ah,unpairB_pairB] using hmP
 rw [s6]
 by_cases hts : (bP aw.val ay.val (ah s)).length = 0
 · have xe : cZ n a hard soft ell tape aw ay = [] := by
     change (if (bP aw.val ay.val (ah s)).length = 0 then [] else _) = []
     rw [if_pos hts]
   rw [xe]
   simp only [hts,↓reduceIte,List.isEmpty_nil,uf,List.map_map]
   apply List.ext_getElem <;> simp
 · have hw_ne : cZ n a hard soft ell tape aw ay =
       (bN ((bP aw.val ay.val (ah s)).getD 0 0) aw.val ay.val (ah s)).map
         (fun x => decide (x ≠ 0)) := by
     change (if (bP aw.val ay.val (ah s)).length = 0 then [] else _) = _
     rw [if_neg hts]
   rw [hw_ne]
   simp only [hts,↓reduceIte,List.map_cons,ne_eq,one_ne_zero,not_false_eq_true,decide_true]
   have uk : ((bN ((bP aw.val ay.val (ah s)).getD 0 0) aw.val ay.val (ah s)).map
       (fun x => decide (x ≠ 0))).length = (ae n).length := by
     simp [bN,ah,unpairB_pairB,hmP]
   have hne : ((bN ((bP aw.val ay.val (ah s)).getD 0 0) aw.val ay.val (ah s)).map
       (fun x => decide (x ≠ 0))).isEmpty = false := by
     cases hc : (bN ((bP aw.val ay.val (ah s)).getD 0 0) aw.val ay.val (ah s)).map
         (fun x => decide (x ≠ 0)) with
     | nil => have h0 := congrArg List.length hc; simp only [List.length_nil] at h0; rw [uk] at h0; omega
     | cons _ _ => rfl
   simp only [enc,hne,Bool.false_eq_true,↓reduceIte]
lemma pM (n : ℕ) (hn : 2 ≤ n)
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (nO : ∀ S ⊆ (ae n).toFinset.filter (fun e => ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2)),
     2 ≤ S.card -> (∀ e ∈ S,∀ g ∈ S,e ≠ g -> Disjoint (al e) (al g)) ->
     (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length =
       (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length)
   (a : ℕ) (ell : ℕ) (tape : Fin ell -> Bool)
   (aw : Fin (n / 2 + 1)) (ay : Fin (soft.length + 1))
   (hne : cZ n a hard soft ell tape aw ay ≠ []) :
   ∃ f : (Fin n -> Bool) -> (Fin n -> Bool) -> Bool,
     ((∃ C : PEqualNP.CircuitLowerBounds.Circuit,
       PEqualNP.MetaComplexity.Monotone2 C /\ C.size + 1 ≤ 2 * n /\
       PEqualNP.Represents.Represents (fun i j : Fin n => decide (i = j)) C /\
       ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) /\
       ∀ z ∈ hard,f (fun i => decide (i ∈ z.1)) (fun j => decide (j ∈ z.2)) = false) /\
     ((ae n).map (fun e => f (fun i => decide (i ∈ al e)) (fun _ => false)) |>.filter id).length = aw.val /\
     (soft.filter (fun t => decide (f (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length = ay.val /\
     cZ n a hard soft ell tape aw ay =
       (ae n).map (fun e => f (fun i => decide (i ∈ al e)) (fun _ => false)) := by
 let header := fun j : ℕ => List.replicate j true ++ [false]
 let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
 let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
   header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
 let s := header a ++ input ++ List.ofFn tape
 let fe := ah s
 let ts := bP aw.val ay.val fe
 have rh : ts.length ≠ 0 := by
   intro h0
   apply hne
   unfold cZ
   exact if_pos h0
 have vW : bM (ts.getD 0 0) aw.val ay.val fe = 1 := by
   have rR : (bP aw.val ay.val fe).getD 0 0 ∈ bP aw.val ay.val fe := by
     rw [List.getD_eq_getElem?_getD]
     cases hts : bP aw.val ay.val fe with
     | nil => exact absurd (by simp [ts,hts]) rh
     | cons t0_c _ => simp
   unfold bP at rR
   generalize h_env_fe : (unpairB fe).2 = env_fe at rR
   generalize h_ts0 : ((List.range (mR env_fe)).flatMap
     (fun t => gP t (pairB (un aw.val) (pairB (un ay.val) fe)))).getD 0 0 = t0_g at rR
   simp only [List.mem_flatMap,List.mem_range] at rR
   rcases rR with ⟨t0_v,_,ht0⟩
   dsimp only [gP] at ht0
   rw [unpairB_pairB,unpairB_pairB,un_length,un_length] at ht0
   by_cases h1 : bM t0_v aw.val ay.val fe = 1
   · rw [if_pos h1,List.mem_singleton] at ht0
     have w7 : ts.getD 0 0 = t0_g := by
       dsimp only [ts]
       unfold bP
       rw [h_env_fe,h_ts0]
     rw [w7,ht0]; exact h1
   · rw [if_neg h1] at ht0; cases ht0
 have dM : s = (header a ++ input) ++ List.ofFn tape := by simp only [s,List.append_assoc]
 have hp := bA a n hard soft (List.ofFn tape)
 dsimp only at hp
 rw [← dM] at hp
 rcases hp with ⟨_,bk,mI,_,_,fE,_,_,_,hhard_bits,_,_⟩
 have hm := aX s bk
 dsimp only at hm
 rcases hm with ⟨hmS,_,hmN,wv,_,hmP,_,_,_,_,_,hmBase,hidx_m⟩
 let t0 := ts.getD 0 0
 have hcond : 2 ≤ n /\ eT s ≤ (soft.length + 1) * aw.val + ay.val /\
     0 < (ji t0 aw.val ay.val fe).length /\
     ((List.range hard.length).map (fun z => cY z (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum = 0 /\
     ((List.range (ae n).length).map (fun idx => cU idx (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum = 0 /\
     ((List.range n).map (fun v => cK v (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum = 0 /\
     ((List.range (ae n).length).map (fun idx => cC idx (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum = aw.val /\
     eT s + ((List.range (ae n).length).map (fun idx => bJ idx (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum =
       (soft.length + 1) * aw.val + ay.val := by
   have hv' := vW
   have rW : (eM (aE s)).getD 2 0 = hard.length := by
     rw [aX s bk |>.2.1]
     unfold eg
     rw [ai,ai,ai] <;>
       simp [List.length_cons,mI] <;> omega
   dsimp only [bM,fe,ah] at hv'
   rw [unpairB_pairB,hmN,rW,hmP,wv,fE,hmBase] at hv'
   dsimp only [t0]
   split_ifs at hv' with hc
   exact hc
 rcases hcond with ⟨_,hbase_le,_,hhard_bad,hbad_mask,hbad_deg,hsz,hsc⟩
 let S : Finset (Fin (ae n).length) :=
   Finset.univ.filter (fun idx : Fin (ae n).length =>
     bT t0 aw.val ay.val idx.val fe = 1)
 let M : Finset (Fin n × Fin n) := S.image aa
 have qY : ∀ idx : ℕ,bT t0 aw.val ay.val idx fe = 0 \/
     bT t0 aw.val ay.val idx fe = 1 := by
   intro idx
   dsimp only [bT]
   split_ifs <;> simp
 have lP : ∀ z ∈ hard,Disjoint z.1 z.2 := by
   rw [aC] at hhard_bad
   intro z hz
   rcases List.mem_iff_getElem.mp hz with ⟨k,hk,rfl⟩
   have h0 := hhard_bad k hk
   simp only [cY,fe,ah,unpairB_pairB,hmS,hmN] at h0
   have hsd := dr s bk (bq s + k * (2 * n)) (hard[k]'hk).1 (hard[k]'hk).2
     (fun i => (hhard_bits k hk i).1) (fun i => (hhard_bits k hk i).2)
   rw [hsd] at h0
   by_cases hD : Disjoint (hard[k]'hk).1 (hard[k]'hk).2
   · exact hD
   · simp [hD] at h0
 let E := (ae n).toFinset.filter (fun e => ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2))
 have zn : M ⊆ E := by
   rw [aC] at hbad_mask
   intro e he
   simp only [M,Finset.mem_image] at he
   rcases he with ⟨idx,nR,rfl⟩
   have rE : bT t0 aw.val ay.val idx.val fe = 1 := (Finset.mem_filter.mp nR).2
   have h0 := hbad_mask idx.val idx.isLt
   dsimp only [cU] at h0
   rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length] at h0
   change bT t0 aw.val ay.val idx.val fe * (1 - qo (unpairB fe).2 idx.val) = 0 at h0
   have uI : (unpairB fe).2 = aE s := by simp [fe,ah,unpairB_pairB]
   rw [rE,one_mul,uI,(hidx_m idx).2.2.1,gI hard soft (List.ofFn tape) idx] at h0
   dsimp only [E]
   by_cases hmem : aa idx ∈ E
   · exact hmem
   · rw [if_neg hmem] at h0; cases h0
 have kB : IsMatching n M := by
   rw [aC] at hbad_deg
   refine ⟨fun e he => ?_,fun e1 he1 e2 he2 ut => ?_⟩
   · simp only [M,Finset.mem_image] at he
     rcases he with ⟨idx,_,rfl⟩
     exact (eJ (aa idx)).mp (List.get_mem (ae n) idx)
   · by_contra hndisj
     rw [Finset.not_disjoint_iff] at hndisj
     rcases hndisj with ⟨v,hv1,hv2⟩
     simp only [M,Finset.mem_image] at he1 he2
     rcases he1 with ⟨idx1,hidx1S,rfl⟩
     rcases he2 with ⟨idx2,hidx2S,rfl⟩
     have vY : idx1 ≠ idx2 := fun h => ut (by rw [h])
     have hv0 := hbad_deg v.val v.isLt
     dsimp only [cK] at hv0
     have uI : mP (unpairB (unpairB (unpairB (unpairB (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))).2).2).2).2 = (ae n).length := by
       simp [unpairB_pairB,fe,ah,hmP]
     rw [uI] at hv0
     have Ba : ¬ (2 ≤ ((List.range (ae n).length).map (fun idx =>
         aB idx (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))))).sum) := by
       by_cases hc : 2 ≤ ((List.range (ae n).length).map (fun idx =>
           aB idx (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))))).sum
       · rw [if_pos hc] at hv0; cases hv0
       · exact hc
     have rK : ((List.range (ae n).length).map (fun idx =>
         aB idx (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))))).sum =
         ∑ idx : Fin (ae n).length,
           aB idx.val (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))) :=
       bW (ae n).length _
     have hhit : ∀ idx ∈ ({idx1,idx2} : Finset (Fin (ae n).length)),
         1 ≤ aB idx.val (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))) := by
       intro idx hidx
       have nR : idx ∈ S := by
         simp only [Finset.mem_insert,Finset.mem_singleton] at hidx
         rcases hidx with rfl | rfl <;> assumption
       have AE : v ∈ al (aa idx) := by
         simp only [Finset.mem_insert,Finset.mem_singleton] at hidx
         rcases hidx with rfl | rfl <;> assumption
       have rE : bT t0 aw.val ay.val idx.val fe = 1 := (Finset.mem_filter.mp nR).2
       dsimp only [aB]
       simp only [unpairB_pairB,un_length]
       have yU : (unpairB fe).2 = aE s := by simp [fe,ah,unpairB_pairB]
       rw [rE,one_mul,yU,(hidx_m idx).1,(hidx_m idx).2.1]
       simp only [al,Finset.mem_insert,Finset.mem_singleton] at AE
       rcases AE with h1 | h2
       · have : (aa idx).1.val = v.val := by rw [← h1]
         simp [this]
       · have : (aa idx).2.val = v.val := by rw [← h2]
         simp [this]
     have yW : ∑ idx ∈ ({idx1,idx2} : Finset (Fin (ae n).length)),
         aB idx.val (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))) ≤
         ∑ idx : Fin (ae n).length,
           aB idx.val (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))) :=
       Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
     have Ao : 2 ≤ ∑ idx ∈ ({idx1,idx2} : Finset (Fin (ae n).length)),
         aB idx.val (pairB (un v.val) (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe)))) := by
       rw [Finset.sum_pair vY]
       have h1 := hhit idx1 (Finset.mem_insert_self _ _)
       have h2 := hhit idx2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
       omega
     omega
 have vN : S.card = aw.val := by
   have wl : ((List.range (ae n).length).map (fun idx =>
       cC idx (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum =
       ∑ idx : Fin (ae n).length,if idx ∈ S then 1 else 0 := by
     rw [bW]
     apply Finset.sum_congr rfl
     intro idx _
     simp only [cC,unpairB_pairB,un_length,S,Finset.mem_filter,Finset.mem_univ,true_and]
     rcases qY idx.val with hcb | hcb <;> simp [hcb]
   have t8 : (∑ idx : Fin (ae n).length,if idx ∈ S then 1 else 0) = S.card := by
     simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,smul_eq_mul,mul_one]
   rw [wl,t8] at hsz
   exact hsz
 have tO : M.card = aw.val := by
   rw [cD,vN]
 have hlin := im hard soft nO
 dsimp only at hlin
 rcases hlin with ⟨_,_,hscore⟩
 have wi : ((List.range (ae n).length).map (fun idx =>
     bJ idx (pairB (un t0) (pairB (un aw.val) (pairB (un ay.val) fe))))).sum =
     ∑ idx : Fin (ae n).length,if idx ∈ S then ((soft.length + 1) +
       (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ ({aa idx} : Finset (Fin n × Fin n)),al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length -
       (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ ({aa idx} : Finset (Fin n × Fin n)),al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length) else 0 := by
   rw [bW]
   apply Finset.sum_congr rfl
   intro idx _
   dsimp only [bJ]
   rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length]
   have uI : (unpairB fe).2 = aE s := by simp [fe,ah,unpairB_pairB]
   rw [uI,(hidx_m idx).2.2.2,g9 hard soft (List.ofFn tape) idx]
   simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
   rcases qY idx.val with hcb | hcb <;> simp [hcb]
 have yK : ∑ idx : Fin (ae n).length,(if idx ∈ S then ((soft.length + 1) +
       (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ ({aa idx} : Finset (Fin n × Fin n)),al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length -
       (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ ({aa idx} : Finset (Fin n × Fin n)),al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length) else 0) =
     ∑ e ∈ M,((soft.length + 1) +
       (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ x ∈ ({e} : Finset (Fin n × Fin n)),al x ⊆ t.1.1 \/ al x ⊆ t.1.2))).length -
       (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ x ∈ ({e} : Finset (Fin n × Fin n)),al x ⊆ t.1.1 \/ al x ⊆ t.1.2))).length) := by
   rw [← Finset.sum_filter (p := fun idx => idx ∈ S)]
   have oY : (Finset.univ.filter (fun idx : Fin (ae n).length => idx ∈ S)) = S := by
     ext x; simp
   rw [oY]
   dsimp only [M]
   rw [Finset.sum_image (fun a _ b _ hab => bI hab)]
 rw [wi,yK,iC] at hsc
 have uO := hscore M kB zn
 rw [hsc,tO] at uO
 have sC : (soft.filter (fun t => decide (ak M (fun i => decide (i ∈ t.1.1))
     (fun j => decide (j ∈ t.1.2)) = t.2))).length = ay.val := by
   omega
 refine ⟨ak M,?_,?_,sC,?_⟩
 · exact (iO hn hard (ak M)).mpr ⟨lP,M,kB,zn,rfl⟩
 · rw [gw kB,(fZ kB).1,tO]
 · have vf : cZ n a hard soft ell tape aw ay =
       (bN t0 aw.val ay.val (ah s)).map (fun x => decide (x ≠ 0)) := by
     change (if ts.length = 0 then [] else _) = _
     rw [if_neg rh]
   have s6 : mP (unpairB (ah s)).2 = (ae n).length := by
     simpa [ah,unpairB_pairB] using hmP
   rw [vf,rQ,s6,gw kB,
     ← bh (ae n).length,jx n,
     List.length_map,List.length_finRange,List.map_map,List.map_map,List.map_map]
   apply List.map_congr_left
   intro idx _
   dsimp only [Function.comp_def]
   by_cases nR : idx ∈ S
   · have hc : bT t0 aw.val ay.val idx.val (ah s) = 1 := (Finset.mem_filter.mp nR).2
     have wv : aa idx ∈ M := Finset.mem_image.mpr ⟨idx,nR,rfl⟩
     simp [hc,wv]
   · have hc : bT t0 aw.val ay.val idx.val (ah s) ≠ 1 :=
       fun h => nR (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
     have h0 : bT t0 aw.val ay.val idx.val (ah s) = 0 := by
       rcases qY idx.val with h | h <;> [exact h; exact absurd h hc]
     have wv : aa idx ∉ M := by
       intro h
       rcases Finset.mem_image.mp h with ⟨vV,hidx',heq⟩
       exact nR ((bI heq) ▸ hidx')
     simp [h0,wv]
lemma sp (n : ℕ) (hn : 2 ≤ n)
   (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool))
   (nO : ∀ S ⊆ (ae n).toFinset.filter (fun e => ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2)),
     2 ≤ S.card -> (∀ e ∈ S,∀ g ∈ S,e ≠ g -> Disjoint (al e) (al g)) ->
     (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length =
       (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2))).length)
   (a : ℕ) (ha : 1 ≤ a) :
   let header := fun j : ℕ => List.replicate j true ++ [false]
   let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
   let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
     header soft.length ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
   let prefixBits := header a ++ input
   let ell := (prefixBits.length + 2) ^ 5
   let belongs := fun (f : (Fin n -> Bool) -> (Fin n -> Bool) -> Bool)
       (sv : Fin (n / 2 + 1)) (jv : Fin (soft.length + 1)) =>
     ((∃ C : PEqualNP.CircuitLowerBounds.Circuit,
       PEqualNP.MetaComplexity.Monotone2 C /\ C.size + 1 ≤ 2 * n /\
       PEqualNP.Represents.Represents (fun i j : Fin n => decide (i = j)) C /\
       ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) /\
       ∀ z ∈ hard,f (fun i => decide (i ∈ z.1)) (fun j => decide (j ∈ z.2)) = false) /\
     ((ae n).map (fun e => f (fun i => decide (i ∈ al e)) (fun _ => false)) |>.filter id).length = sv.val /\
     (soft.filter (fun t => decide (f (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length = jv.val
   2 ^ a * Nat.card {tape : Fin ell -> Bool // ∀ s j,(∃ f,belongs f s j) ->
       cZ n a hard soft ell tape s j ≠ []} ≥ (2 ^ a - 1) * 2 ^ ell := by
 classical
 intro header bank input prefixBits ell belongs
 have rz : a + n + soft.length + 4 ≤ prefixBits.length :=
   (bA a n hard soft []).2.2.2.2.2.2.2.2.1
 let P := (ae n).length
 have yB : P = n * (n - 1) / 2 := by
   dsimp [P]; have := dZ n; omega
 let b := 2 * (Nat.log2 n + 1) + 1
 let R := a + n + soft.length + 2
 have hpb := mE ha hn rz
 dsimp only at hpb
 rw [← yB] at hpb
 rcases hpb with ⟨uK,hb_P,hb_n2,hb_8n2,hRPb,hslots_le⟩
 have hlin := im hard soft nO
 dsimp only at hlin
 rcases hlin with ⟨hcWt_b,hbase_le,hscore_lin⟩
 let E := (ae n).toFinset.filter (fun e => ∀ z ∈ hard,¬(al e ⊆ z.1) /\ ¬(al e ⊆ z.2))
 let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
   Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,al e ⊆ t.1.1 \/ al e ⊆ t.1.2
 let ct := fun S => (soft.filter (fun t => t.2 && decide (lists S t))).length
 let bY := fun S => (soft.filter (fun t => !t.2 && decide (lists S t))).length
 let oc := fun (e : Fin n × Fin n) => (soft.length + 1) + ct {e} - bY {e}
 have sT : ∀ (sv : Fin (n / 2 + 1)) (jv : Fin (soft.length + 1)),
     (∃ f,belongs f sv jv) ->
     2 ^ R * (Finset.univ.filter (fun tape : Fin ell -> Bool =>
       cZ n a hard soft ell tape sv jv = [])).card ≤ 2 ^ ell := by
   intro sv jv ⟨f,hf_val,hf_sz,hf_sc⟩
   have AI := (iO hn hard f).mp hf_val
   rcases AI with ⟨lP,M0,hM0,hM0E,rfl⟩
   have AL := (fZ hM0).1
   rw [gw hM0] at hf_sz
   have uA : M0.card = sv.val := by omega
   have v7 : M0 ⊆ (ae n).toFinset := Finset.Subset.trans hM0E (Finset.filter_subset _ _)
   have r7 := hscore_lin M0 hM0 hM0E
   rw [uA,hf_sc] at r7
   let base := (soft.filter (fun t => decide (ak (∅ : Finset (Fin n × Fin n))
     (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length
   have mO : base ≤ (soft.length + 1) * sv.val + jv.val := by
     dsimp [base]; omega
   let T := (soft.length + 1) * sv.val + jv.val - base
   let act : Fin P -> Bool := fun idx => decide (aa idx ∈ E)
   let F : Finset (Finset (Fin P)) :=
     (Finset.univ.filter (fun idx : Fin P => act idx)).powerset.filter
       (fun S => IsMatching n (S.image aa) /\ ∑ idx ∈ S,oc (aa idx) = T)
   have hS0 : ∃ S0 : Finset (Fin P),S0.image aa = M0 /\ S0 ⊆ Finset.univ.filter (fun idx => act idx) := by
     let S0 := Finset.univ.filter (fun idx : Fin P => aa idx ∈ M0)
     refine ⟨S0,?_,?_⟩
     · ext e
       simp only [S0,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
       constructor
       · rintro ⟨idx,hidx,rfl⟩; exact hidx
       · intro he
         have AJ : e ∈ ae n := List.mem_toFinset.mp (v7 he)
         rcases List.mem_iff_getElem.mp AJ with ⟨idx,hlt,hidx⟩
         exact ⟨⟨idx,hlt⟩,by simpa [aa,List.get_eq_getElem,hidx] using he,by simp [aa,List.get_eq_getElem,hidx]⟩
     · intro idx hidx
       simp only [S0,Finset.mem_filter,Finset.mem_univ,true_and,act,decide_eq_true_eq] at hidx ⊢
       exact hM0E hidx
   rcases hS0 with ⟨S0,hS0_img,hS0_sub⟩
   have vO : S0 ∈ F := by
     refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS0_sub,?_,?_⟩
     · rw [hS0_img]; exact hM0
     · rw [← hS0_img] at r7
       change (soft.length + 1) * sv.val + jv.val = base + ∑ e ∈ S0.image aa,oc e at r7
       rw [Finset.sum_image (fun a _ b _ hab => bI hab)] at r7
       dsimp only [T]
       rw [r7,Nat.add_sub_cancel_left]
   have ya : F.Nonempty := ⟨S0,vO⟩
   have wR := oI (by omega : 0 < R) uK hb_P hRPb F ya
   dsimp only at wR
   refine le_trans (Nat.mul_le_mul_left (2 ^ R) (Finset.card_le_card ?_)) wR
   intro tape wT
   simp only [Finset.mem_filter,Finset.mem_univ,true_and] at wT ⊢
   intro aL uZ
   apply absurd wT
   let s := prefixBits ++ List.ofFn tape
   have dM : s = (header a ++ input) ++ List.ofFn tape := rfl
   have hp := bA a n hard soft (List.ofFn tape)
   dsimp only at hp
   rw [← dM] at hp
   rcases hp with ⟨nI,bk,mI,_,_,fE,_,_,_,hhard_bits,_,_⟩
   have hm := aX s bk
   dsimp only at hm
   rcases hm with ⟨hmS,_,hmN,wv,_,hmP,hmb,hmU,hmB,hmLbuf,hmR,hmBase,hidx_m⟩
   have wN : ow s = b := by dsimp [ow]; rw [bk]
   have wQ : ui s = 2 ^ b := by dsimp [ui]; rw [wN]
   have yO : iz s = n * 2 ^ b + 1 := by dsimp [iz]; rw [bk,wQ]
   have x9 : ∀ S : Finset (Fin P),IsMatching n (S.image aa) ->
       ap (fun idx => ⟨az b (List.ofFn tape) ((aL.val * P + idx.val) * b),
         bB b (List.ofFn tape) ((aL.val * P + idx.val) * b)⟩) S < iz s := by
     intro S Bd
     have hcard : S.card ≤ n / 2 := by
       have := (fZ Bd).2
       rwa [cD] at this
     have hwt : ap (fun idx => ⟨az b (List.ofFn tape) ((aL.val * P + idx.val) * b),
         bB b (List.ofFn tape) ((aL.val * P + idx.val) * b)⟩) S ≤ S.card * 2 ^ b := by
       unfold ap
       have hterm : ∀ idx ∈ S,az b (List.ofFn tape) ((aL.val * P + idx.val) * b) ≤ 2 ^ b :=
         fun idx _ => Nat.le_of_lt (bB _ _ _)
       calc ∑ idx ∈ S,az b (List.ofFn tape) ((aL.val * P + idx.val) * b)
           ≤ ∑ _ ∈ S,2 ^ b := Finset.sum_le_sum hterm
         _ = S.card * 2 ^ b := by simp
     have AF : S.card * 2 ^ b ≤ n * 2 ^ b := Nat.mul_le_mul_right (2 ^ b) (by omega)
     rw [yO]; omega
   have tz : (fun idx : Fin P => decide ((bD s).getD idx.val 0 ≠ 0)) = act := by
     ext idx
     rw [gI hard soft (List.ofFn tape) idx]
     change decide ((if aa idx ∈ E then 1 else 0) ≠ 0) = decide (aa idx ∈ E)
     by_cases hE : aa idx ∈ E <;> simp [hE]
   have yT : (fun idx : Fin P => (eP s).getD idx.val 0) = (fun idx => oc (aa idx)) := by
     ext idx
     exact g9 hard soft (List.ofFn tape) idx
   have Ai : (Finset.univ.filter (fun idx : Fin P => act idx)).powerset.filter
       (fun S => IsMatching n (S.image aa) /\ ∑ idx ∈ S,oc (aa idx) = T) = F := rfl
   have hrec := kb act (fun idx => oc (aa idx))
     (fun idx => ⟨az b (List.ofFn tape) ((aL.val * P + idx.val) * b),
       bB b (List.ofFn tape) ((aL.val * P + idx.val) * b)⟩)
     (iz s) x9 T uZ
   dsimp only at hrec
   rcases hrec with ⟨S_min,hSmin,hw_min_lt,hcoeff_one,hcoeff_zero,hdel_iff⟩
   have qU := Finset.mem_filter.mp hSmin
   have qh := Finset.mem_powerset.mp qU.1
   have nL : IsMatching n (S_min.image aa) := qU.2.1
   have qi : ∑ idx ∈ S_min,oc (aa idx) = T := qU.2.2
   have sM : S_min.card = sv.val := by
     have my := hscore_lin (S_min.image aa) nL (by
       intro e he
       rcases Finset.mem_image.mp he with ⟨idx,hidx,rfl⟩
       have ha := Finset.mem_filter.mp (qh hidx)
       simpa [act,E] using ha.2)
     rw [cD,Finset.sum_image (fun a _ b _ hab => bI hab),
       qi] at my
     change (soft.length + 1) * S_min.card + _ = base + T at my
     have xP : (soft.filter (fun t => decide (ak (S_min.image aa)
         (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length ≤ soft.length :=
       List.length_filter_le _ _
     have wK : (soft.length + 1) * S_min.card +
         (soft.filter (fun t => decide (ak (S_min.image aa)
           (fun i => decide (i ∈ t.1.1)) (fun j => decide (j ∈ t.1.2)) = t.2))).length =
         (soft.length + 1) * sv.val + jv.val := by
       have sn : base + T = (soft.length + 1) * sv.val + jv.val := by
         dsimp [T]; exact Nat.add_sub_of_le mO
       rw [sn] at my
       exact my
     exact jA soft.length S_min.card _ sv.val jv.val xP jv.isLt wK
   have ug : T ≤ n * (2 * soft.length + 1) := by
     have yR : T ≤ (soft.length + 1) * (n / 2) + soft.length := by
       have xN : sv.val ≤ n / 2 := Nat.lt_succ_iff.mp sv.isLt
       have z6 : jv.val ≤ soft.length := Nat.lt_succ_iff.mp jv.isLt
       dsimp [T]
       have zj : (soft.length + 1) * sv.val ≤ (soft.length + 1) * (n / 2) :=
         Nat.mul_le_mul_left _ xN
       omega
     exact oZ T (n / 2) soft.length n yR (le_refl _) hn
   let jL : Fin P -> Fin (2 ^ b) := fun idx =>
     ⟨az b (List.ofFn tape) ((aL.val * P + idx.val) * b),
       bB b (List.ofFn tape) ((aL.val * P + idx.val) * b)⟩
   have yn : ap jL S_min < iz s := hw_min_lt
   have ot : 2 * (iz s * T + ap jL S_min) < am s := by
     have uw : lN s = iz s * (2 * soft.length + 1) + 2 ^ b := by
       dsimp [lN]; rw [fE,wQ]
     have vu : am s = 2 * (n * (iz s * (2 * soft.length + 1) + 2 ^ b) + iz s) + 1 := by
       dsimp [am]; rw [bk,uw]
     rw [vu]
     exact rL (iz s) T (ap jL S_min) n soft.length (2 ^ b) ug yn
   have xj : ∀ w ≤ ap jL S_min,2 * (iz s * T + w) < am s := by
     intro w hw
     exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hw _)) ot
   let r2 : Fin (am s) := ⟨2 * (iz s * T + ap jL S_min),ot⟩
   let deg : Fin P -> ℕ := fun idx => iz s * (eP s).getD idx.val 0 +
     az (ow s) (List.ofFn tape) ((aL.val * P + idx.val) * (ow s))
   have qz : deg = fun idx => iz s * oc (aa idx) +
       (az b (List.ofFn tape) ((aL.val * P + idx.val) * b)) := by
     ext idx
     dsimp only [deg]
     rw [congrFun yT idx,wN]
   have oK : aL.val < a + n + soft.length + 2 := aL.isLt
   have xn : (bl s).getD ((aL.val * (P + 1) + P) * am s + r2.val) 0 =
       if dt n (am s) (bn n (am s)
         (fun idx => decide ((bD s).getD idx.val 0 ≠ 0) && decide (idx.val ≠ P)) deg) r2 then 1 else 0 :=
     eu hard soft (List.ofFn tape) hn aL.val P oK (le_refl P) r2.val ot
   have uR : (fun idx : Fin P => decide ((bD s).getD idx.val 0 ≠ 0) && decide (idx.val ≠ P)) = act := by
     ext idx
     have z5 : idx.val ≠ P := ne_of_lt idx.isLt
     simp only [decide_eq_true z5,Bool.and_true]
     exact congrFun tz idx
   have wL := iD (L := am s) hn act deg r2
   have yZ : (bl s).getD ((aL.val * (P + 1) + P) * am s + r2.val) 0 = 1 := by
     rw [xn,uR]
     have rt : dt n (am s) (bn n (am s) act deg) r2 =
         decide ((bG n act deg).det.coeff r2.val = 1) := wL
     rw [rt,qz]
     change (if decide ((bG n act (fun idx => iz s * oc (aa idx) +
       (⟨az b (List.ofFn tape) ((aL.val * P + idx.val) * b),
         bB b (List.ofFn tape) ((aL.val * P + idx.val) * b)⟩ : Fin (2 ^ b)).val)).det.coeff
       (2 * (iz s * T + ap jL S_min)) = 1) then 1 else 0) = 1
     rw [hcoeff_one]
     simp
   have xQ : ∀ w < ap jL S_min,
       (bl s).getD ((aL.val * (P + 1) + P) * am s + (2 * (iz s * T + w))) 0 = 0 := by
     intro w hw
     have hwl : 2 * (iz s * T + w) < am s := xj w (Nat.le_of_lt hw)
     let q9 : Fin (am s) := ⟨2 * (iz s * T + w),hwl⟩
     have xU : (bl s).getD ((aL.val * (P + 1) + P) * am s + (2 * (iz s * T + w))) 0 =
         if dt n (am s) (bn n (am s)
           (fun idx => decide ((bD s).getD idx.val 0 ≠ 0) && decide (idx.val ≠ P)) deg) q9 then 1 else 0 :=
       eu hard soft (List.ofFn tape) hn aL.val P oK (le_refl P) (2 * (iz s * T + w)) hwl
     rw [xU,uR]
     have vE := iD (L := am s) hn act deg q9
     have rt : dt n (am s) (bn n (am s) act deg) q9 =
         decide ((bG n act deg).det.coeff q9.val = 1) := vE
     rw [rt,qz]
     have hcz := hcoeff_zero w hw
     change (if decide ((bG n act (fun idx => iz s * oc (aa idx) +
       (⟨az b (List.ofFn tape) ((aL.val * P + idx.val) * b),
         bB b (List.ofFn tape) ((aL.val * P + idx.val) * b)⟩ : Fin (2 ^ b)).val)).det.coeff
       (2 * (iz s * T + w)) = 1) then 1 else 0) = 0
     rw [hcz]
     simp
   have rT : 0 < (ji aL.val sv.val jv.val (ah s)).length /\
       (ji aL.val sv.val jv.val (ah s)).getD 0 0 = ap jL S_min := by
     have xI : ji aL.val sv.val jv.val (ah s) =
         (List.range (iz s)).flatMap (fun w =>
           if decide ((bl s).getD ((aL.val * (P + 1) + P) * am s + 2 * (iz s * T + w)) 0 = 1) = true
           then [w] else []) := by
       simp only [ji,ah,unpairB_pairB,un_length,hmB,j9,dh,hmP,hmLbuf,wv,fE,hmBase]
       refine congrArg (fun g => (List.range (iz s)).flatMap g) (funext fun w => ?_)
       have sn : (soft.length + 1) * sv.val + jv.val - eT s = T := by
         rw [iC]
       rw [sn]
       dsimp only [P]
       by_cases h1 : (bl s).getD ((aL.val * ((ae n).length + 1) + (ae n).length) * am s +
           2 * (iz s * T + w)) 0 = 1 <;>
         simp [h1]
     rw [xI]
     exact jn (iz s)
       (fun w => decide ((bl s).getD ((aL.val * (P + 1) + P) * am s + 2 * (iz s * T + w)) 0 = 1))
       (ap jL S_min) hw_min_lt
       (by change decide ((bl s).getD ((aL.val * (P + 1) + P) * am s + r2.val) 0 = 1) = true; rw [yZ]; decide)
       (fun w hw => by rw [xQ w hw]; decide)
   have jH : ∀ idx : Fin P,
       bT aL.val sv.val jv.val idx.val (ah s) = if idx ∈ S_min then 1 else 0 := by
     intro idx
     dsimp only [bT]
     rw [rT.2]
     simp only [ah,unpairB_pairB,dh,hmP,hmB,hmLbuf,wv,fE,hmBase]
     have sn : (soft.length + 1) * sv.val + jv.val - eT s = T := by rw [iC]
     rw [sn]
     have uU : (bl s).getD ((aL.val * (P + 1) + idx.val) * am s + r2.val) 0 =
         if dt n (am s) (bn n (am s)
           (fun j => decide ((bD s).getD j.val 0 ≠ 0) && decide (j.val ≠ idx.val)) deg) r2 then 1 else 0 :=
       eu hard soft (List.ofFn tape) hn aL.val idx.val
         oK (Nat.le_of_lt idx.isLt) r2.val ot
     have uY : (fun j : Fin P => decide ((bD s).getD j.val 0 ≠ 0) && decide (j.val ≠ idx.val)) =
         (fun j : Fin P => act j && (j != idx)) := by
       ext j
       rw [congrFun tz j]
       apply congrArg (act j && ·)
       apply Bool.eq_iff_iff.mpr
       simp [Fin.ext_iff]
     rw [uU,uY]
     have t9 := iD (L := am s) hn (fun j => act j && (j != idx)) deg r2
     have rt : dt n (am s) (bn n (am s) (fun j => act j && (j != idx)) deg) r2 =
         decide ((bG n (fun j => act j && (j != idx)) deg).det.coeff r2.val = 1) := t9
     rw [rt,qz]
     have hiff := hdel_iff idx
     change (if (if decide ((bG n (fun j => act j && (j != idx)) (fun j => iz s * oc (aa j) +
       (⟨az b (List.ofFn tape) ((aL.val * P + j.val) * b),
         bB b (List.ofFn tape) ((aL.val * P + j.val) * b)⟩ : Fin (2 ^ b)).val)).det.coeff
       (2 * (iz s * T + ap jL S_min)) = 1) then 1 else 0) = 0 then 1 else 0) =
       if idx ∈ S_min then 1 else 0
     by_cases hmem : idx ∈ S_min
     · have h0 := hiff.mpr hmem
       rw [h0]
       simp [hmem]
     · have hne0 : (bG n (fun j => act j && (j != idx)) (fun j => iz s * oc (aa j) +
         (⟨az b (List.ofFn tape) ((aL.val * P + j.val) * b),
           bB b (List.ofFn tape) ((aL.val * P + j.val) * b)⟩ : Fin (2 ^ b)).val)).det.coeff
         (2 * (iz s * T + ap jL S_min)) ≠ 0 := fun h => hmem (hiff.mp h)
       have h1 : (bG n (fun j => act j && (j != idx)) (fun j => iz s * oc (aa j) +
         (⟨az b (List.ofFn tape) ((aL.val * P + j.val) * b),
           bB b (List.ofFn tape) ((aL.val * P + j.val) * b)⟩ : Fin (2 ^ b)).val)).det.coeff
         (2 * (iz s * T + ap jL S_min)) = 1 := by
         generalize hz : (bG n (fun j => act j && (j != idx)) (fun j => iz s * oc (aa j) +
           (⟨az b (List.ofFn tape) ((aL.val * P + j.val) * b),
             bB b (List.ofFn tape) ((aL.val * P + j.val) * b)⟩ : Fin (2 ^ b)).val)).det.coeff
           (2 * (iz s * T + ap jL S_min)) = z at hne0 ⊢
         fin_cases z
         · exact absurd rfl hne0
         · rfl
       rw [h1]
       simp [hmem]
   have lX : (unpairB (ah s)).2 = aE s := by simp [ah,unpairB_pairB]
   have zu : bM aL.val sv.val jv.val (ah s) = 1 := by
     dsimp only [bM]
     have rW : (eM (aE s)).getD 2 0 = hard.length := by
       rw [aX s bk |>.2.1]
       unfold eg
       rw [ai,ai,ai] <;>
         simp [List.length_cons,mI] <;> omega
     rw [lX,hmN,rW,hmP,wv,fE,hmBase]
     have hc1 : 2 ≤ n := hn
     have hc2 : eT s ≤ (soft.length + 1) * sv.val + jv.val := by rw [iC]; exact mO
     have hc3 : 0 < (ji aL.val sv.val jv.val (ah s)).length := rT.1
     have hc4 : ((List.range hard.length).map (fun z =>
         cY z (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))))).sum = 0 := by
       rw [aC]
       intro z hz
       simp only [cY,ah,unpairB_pairB,hmS,hmN]
       rw [dr s bk (bq s + z * (2 * n)) (hard[z]'hz).1 (hard[z]'hz).2
         (fun i => (hhard_bits z hz i).1) (fun i => (hhard_bits z hz i).2)]
       rw [if_pos (lP _ (List.getElem_mem hz))]
     have hc5 : ((List.range P).map (fun idx =>
         cU idx (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))))).sum = 0 := by
       rw [aC]
       intro idx hidx
       dsimp only [cU]
       rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length]
       rw [show bT aL.val sv.val jv.val idx (ah s) =
           if (⟨idx,hidx⟩ : Fin P) ∈ S_min then 1 else 0 from jH ⟨idx,hidx⟩]
       rw [lX,(hidx_m ⟨idx,hidx⟩).2.2.1]
       by_cases hmem : (⟨idx,hidx⟩ : Fin P) ∈ S_min
       · have ha := Finset.mem_filter.mp (qh hmem)
         have hE : aa ⟨idx,hidx⟩ ∈ E := by simpa [act] using ha.2
         rw [gI hard soft (List.ofFn tape) ⟨idx,hidx⟩,if_pos hE]
         simp [hmem]
       · simp [hmem]
     have AK : ((List.range n).map (fun v =>
         cK v (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))))).sum = 0 := by
       rw [aC]
       intro v hv
       dsimp only [cK]
       rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,lX,hmP]
       have rK : ((List.range P).map (fun idx =>
           aB idx (pairB (un v) (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s))))))).sum =
           ∑ idx ∈ S_min,((if (aa idx).1.val = v then 1 else 0) + (if (aa idx).2.val = v then 1 else 0)) := by
         rw [bW]
         have oY : (Finset.univ.filter (fun idx : Fin P => idx ∈ S_min)) = S_min := by ext x; simp
         have nB : ∀ idx ∈ Finset.univ,
             aB idx.val (pairB (un v) (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s))))) ≠ 0 ->
             idx ∈ S_min := by
           intro idx _ hne
           by_contra hno
           apply hne
           dsimp only [aB]
           rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length,un_length,
             jH idx,if_neg hno,zero_mul]
         rw [← Finset.sum_filter_of_ne (p := fun idx : Fin P => idx ∈ S_min) nB,oY]
         apply Finset.sum_congr rfl
         intro idx hidx
         dsimp only [aB]
         rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length,un_length,
           jH idx,if_pos hidx,one_mul,lX,(hidx_m idx).1,(hidx_m idx).2.1]
       have hle1 : ((List.range P).map (fun idx =>
           aB idx (pairB (un v) (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s))))))).sum ≤ 1 := by
         rw [rK]
         have wm : (S_min.filter (fun idx => ⟨v,hv⟩ ∈ al (aa idx))).card ≤ 1 := by
           by_contra hgt
           have zC : 1 < (S_min.filter (fun idx => ⟨v,hv⟩ ∈ al (aa idx))).card := by omega
           rcases Finset.one_lt_card.mp zC with ⟨idx1,h1,idx2,h2,ut⟩
           have h1f := Finset.mem_filter.mp h1
           have h2f := Finset.mem_filter.mp h2
           have hdisj := nL.2 (aa idx1) (Finset.mem_image_of_mem _ h1f.1)
             (aa idx2) (Finset.mem_image_of_mem _ h2f.1) (fun h => ut (bI h))
           exact Finset.disjoint_left.mp hdisj h1f.2 h2f.2
         have vw : ∀ idx ∈ S_min,
             (if (aa idx).1.val = v then 1 else 0) + (if (aa idx).2.val = v then 1 else 0) =
             if ⟨v,hv⟩ ∈ al (aa idx) then 1 else 0 := by
           intro idx _
           have zg : (aa idx).1.val < (aa idx).2.val :=
             (eJ (aa idx)).mp (List.get_mem (ae n) idx)
           simp only [al,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
           by_cases h1 : (aa idx).1.val = v <;> by_cases h2 : (aa idx).2.val = v
           · omega
           · simp [h1,h2,Ne.symm h2]
           · simp [h1,h2,Ne.symm h1]
           · simp [h1,h2,Ne.symm h1,Ne.symm h2]
         rw [Finset.sum_congr rfl vw,Finset.sum_boole,Nat.cast_id]
         exact wm
       dsimp only [P] at hle1
       split_ifs with hge
       · omega
       · rfl
     have Ak : ((List.range P).map (fun idx =>
         cC idx (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))))).sum = sv.val := by
       rw [bW]
       have h1 : ∑ idx : Fin P,cC idx.val (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))) =
           ∑ idx : Fin P,if idx ∈ S_min then 1 else 0 := by
         apply Finset.sum_congr rfl
         intro idx _
         dsimp only [cC]
         rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length,jH idx]
       have hsc : (∑ idx : Fin P,if idx ∈ S_min then 1 else 0) = S_min.card := by
         simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,smul_eq_mul,mul_one]
       rw [h1,hsc]
       exact sM
     have Aw : eT s + ((List.range P).map (fun idx =>
         bJ idx (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))))).sum =
         (soft.length + 1) * sv.val + jv.val := by
       rw [iC,bW]
       have h1 : ∑ idx : Fin P,bJ idx.val (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))) =
           ∑ idx ∈ S_min,oc (aa idx) := by
         have oY : (Finset.univ.filter (fun idx : Fin P => idx ∈ S_min)) = S_min := by ext x; simp
         have nB : ∀ idx ∈ Finset.univ,
             bJ idx.val (pairB (un aL.val) (pairB (un sv.val) (pairB (un jv.val) (ah s)))) ≠ 0 ->
             idx ∈ S_min := by
           intro idx _ hne
           by_contra hno
           apply hne
           dsimp only [bJ]
           rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length,
             jH idx,if_neg hno,zero_mul]
         rw [← Finset.sum_filter_of_ne (p := fun idx : Fin P => idx ∈ S_min) nB,oY]
         apply Finset.sum_congr rfl
         intro idx hidx
         dsimp only [bJ]
         rw [unpairB_pairB,unpairB_pairB,unpairB_pairB,un_length,un_length,un_length,
           jH idx,if_pos hidx,one_mul,lX,(hidx_m idx).2.2.2]
         exact g9 hard soft (List.ofFn tape) idx
       rw [h1,qi]
       dsimp only [T]
       exact Nat.add_sub_of_le mO
     dsimp only [P] at hc5 Ak Aw
     simp only [hc1,hc2,hc3,hc4,hc5,AK,Ak,Aw,and_self,↓reduceIte]
   have rh : (bP sv.val jv.val (ah s)).length ≠ 0 := by
     have vo : s7 s = R := by
       dsimp [s7,R]; rw [nI,bk,fE]
     have hmem : aL.val ∈ bP sv.val jv.val (ah s) := by
       simp only [bP,List.mem_flatMap,List.mem_range]
       rw [lX,hmR,vo]
       refine ⟨aL.val,aL.isLt,?_⟩
       dsimp only [gP]
       rw [unpairB_pairB,unpairB_pairB,un_length,un_length,zu]
       simp
     exact ne_of_gt (List.length_pos_of_mem hmem)
   have uk : (bN ((bP sv.val jv.val (ah s)).getD 0 0) sv.val jv.val (ah s)).length = P := by
     dsimp only [bN,P]
     rw [lX,hmP,List.length_map,List.length_range]
   have vf : cZ n a hard soft ell tape sv jv =
       (bN ((bP sv.val jv.val (ah s)).getD 0 0) sv.val jv.val (ah s)).map
         (fun x => decide (x ≠ 0)) := by
     change (if (bP sv.val jv.val (ah s)).length = 0 then [] else _) = _
     rw [if_neg rh]
   intro hemp
   rw [vf] at hemp
   have : (bN ((bP sv.val jv.val (ah s)).getD 0 0) sv.val jv.val (ah s)).length = 0 := by
     simpa using congrArg List.length hemp
   omega
 let Bad := Finset.univ.filter (fun tape : Fin ell -> Bool =>
   ¬ ∀ s j,(∃ f,belongs f s j) -> cZ n a hard soft ell tape s j ≠ [])
 have vh : Bad ⊆ (Finset.univ : Finset (Fin (n / 2 + 1) × Fin (soft.length + 1))).biUnion
     (fun p => if ∃ f,belongs f p.1 p.2 then
       Finset.univ.filter (fun tape : Fin ell -> Bool => cZ n a hard soft ell tape p.1 p.2 = [])
     else ∅) := by
   intro tape hB
   simp only [Bad,Finset.mem_filter,Finset.mem_univ,true_and,not_forall] at hB
   rcases hB with ⟨sv,jv,hex,hemp⟩
   have hemp' : cZ n a hard soft ell tape sv jv = [] := Classical.not_not.mp hemp
   simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
   refine ⟨(sv,jv),?_⟩
   simp [hex,hemp']
 have xc : 2 ^ R * Bad.card ≤ (n / 2 + 1) * (soft.length + 1) * 2 ^ ell := by
   calc 2 ^ R * Bad.card
       ≤ 2 ^ R * ∑ p : Fin (n / 2 + 1) × Fin (soft.length + 1),
           (if ∃ f,belongs f p.1 p.2 then
             Finset.univ.filter (fun tape : Fin ell -> Bool => cZ n a hard soft ell tape p.1 p.2 = [])
           else ∅).card := Nat.mul_le_mul_left _ (Finset.card_le_card vh |>.trans Finset.card_biUnion_le)
     _ = ∑ p : Fin (n / 2 + 1) × Fin (soft.length + 1),
           2 ^ R * (if ∃ f,belongs f p.1 p.2 then
             Finset.univ.filter (fun tape : Fin ell -> Bool => cZ n a hard soft ell tape p.1 p.2 = [])
           else ∅).card := by rw [Finset.mul_sum]
     _ ≤ ∑ _p : Fin (n / 2 + 1) × Fin (soft.length + 1),2 ^ ell := by
           apply Finset.sum_le_sum
           intro p _
           by_cases hex : ∃ f,belongs f p.1 p.2
           · simp only [hex,↓reduceIte]; exact sT p.1 p.2 hex
           · simp [hex]
     _ = (n / 2 + 1) * (soft.length + 1) * 2 ^ ell := by
           simp [Finset.card_univ,Fintype.card_prod]
 have xd : 2 ^ (n + soft.length + 2) * (2 ^ a * Bad.card) ≤ 2 ^ (n + soft.length + 2) * 2 ^ ell := by
   have yV : 2 ^ R = 2 ^ (n + soft.length + 2) * 2 ^ a := by
     dsimp [R]; rw [show a + n + soft.length + 2 = (n + soft.length + 2) + a by omega,pow_add]
   have hr1 : 2 ^ (n + soft.length + 2) * (2 ^ a * Bad.card) = 2 ^ R * Bad.card := by
     rw [yV,mul_assoc]
   have hr2 : (n / 2 + 1) * (soft.length + 1) * 2 ^ ell ≤ 2 ^ (n + soft.length + 2) * 2 ^ ell :=
     Nat.mul_le_mul_right (2 ^ ell) hslots_le
   omega
 have ze : 2 ^ a * Bad.card ≤ 2 ^ ell :=
   Nat.le_of_mul_le_mul_left xd (by positivity)
 let Good := Finset.univ.filter (fun tape : Fin ell -> Bool =>
   ∀ s j,(∃ f,belongs f s j) -> cZ n a hard soft ell tape s j ≠ [])
 have htot : Good.card + Bad.card = 2 ^ ell := by
   have hd : Disjoint Good Bad := by
     rw [Finset.disjoint_left]
     intro t hG hB
     simp only [Good,Bad,Finset.mem_filter,Finset.mem_univ,true_and] at hG hB
     exact hB hG
   have hu : Good ∪ Bad = Finset.univ := by
     ext t
     simp only [Good,Bad,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
     exact iff_true_intro (Classical.em _)
   rw [← Finset.card_union_of_disjoint hd,hu]
   simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
 have oX : Nat.card {tape : Fin ell -> Bool // ∀ s j,(∃ f,belongs f s j) ->
     cZ n a hard soft ell tape s j ≠ []} = Good.card := by
   rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
 rw [oX]
 have zb : 2 ^ a * Good.card + 2 ^ a * Bad.card = 2 ^ a * 2 ^ ell := by
   rw [← mul_add,htot]
 have xg : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
 have hsub : (2 ^ a - 1) * 2 ^ ell + 2 ^ ell = 2 ^ a * 2 ^ ell := by
   calc (2 ^ a - 1) * 2 ^ ell + 2 ^ ell
       = (2 ^ a - 1 + 1) * 2 ^ ell := by ring
     _ = 2 ^ a * 2 ^ ell := by rw [Nat.sub_add_cancel xg]
 omega
lemma pnp_main : (let header := fun j : Nat => List.replicate j true ++ [false]
let fast := fun f : List Bool -> List Bool =>
 ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
   ∀ i,Finite (M.tm.Γ i)
let bits := fun (w z : Nat) => (List.range w).map (fun h => z.testBit h)
let pairs := fun k : Nat => (List.finRange k).flatMap (fun i =>
   ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
∃ (search : List Bool -> List Bool) (d : Nat),fast search /\
∀ (n : Nat),2 ≤ n ->
 ∀ (hard : List (Finset (Fin n) × Finset (Fin n)))
   (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool)),
 let m := soft.length
 let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
 let E := (pairs n).toFinset.filter (fun e =>
   ∀ z ∈ hard,¬(ends e ⊆ z.1) /\ ¬(ends e ⊆ z.2))
 let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
   Disjoint t.1.1 t.1.2 /\ ∀ e ∈ S,ends e ⊆ t.1.1 \/ ends e ⊆ t.1.2
 (∀ S ⊆ E,2 ≤ S.card ->
   (∀ e ∈ S,∀ f ∈ S,e ≠ f -> Disjoint (ends e) (ends f)) ->
   (soft.filter (fun t => t.2 && decide (lists S t))).length =
     (soft.filter (fun t => !t.2 && decide (lists S t))).length) ->
 let Fn := (Fin n -> Bool) -> (Fin n -> Bool) -> Bool
 let obs := fun (f : Fn) (R T : Finset (Fin n)) =>
   f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ T))
 let valid := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
   PEqualNP.MetaComplexity.Monotone2 C /\ C.size+1 ≤ 2*n /\
   PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C /\
   ∀ x y,f x y = C.eval (List.ofFn x ++ List.ofFn y)) /\
   ∀ z ∈ hard,obs f z.1 z.2 = false
 let code := fun f : Fn => (pairs n).map (fun e => obs f (ends e) ∅)
 let size := fun f : Fn => ((code f).filter id).length
 let score := fun f : Fn => (soft.filter (fun t => decide (obs f t.1.1 t.1.2 = t.2))).length
 let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
 let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
   header m ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
 ∀ a : Nat,1 ≤ a ->
   let prefixBits := header a ++ input
   let ell := (prefixBits.length+2)^d
   let slots := (List.finRange (n/2+1)).flatMap (fun s =>
     (List.finRange (m+1)).map (fun j => (s,j)))
   let enc := fun word : List Bool => if word.isEmpty then List.replicate ((pairs n).length+1) false
     else true::word
   let belongs := fun (f : Fn) (s : Fin (n/2+1)) (j : Fin (m+1)) =>
     valid f /\ size f = s.val /\ score f = j.val
   ∃ words : (Fin ell -> Bool) -> Fin (n/2+1) -> Fin (m+1) -> List Bool,
     (∀ tape,search (prefixBits ++ List.ofFn tape) =
       slots.flatMap (fun z => enc (words tape z.1 z.2))) /\
     (∀ tape s j,words tape s j ≠ [] -> ∃ f : Fn,belongs f s j /\ words tape s j = code f) /\
     2^a * Nat.card {tape : Fin ell -> Bool // ∀ s j,(∃ f : Fn,belongs f s j) ->
       words tape s j ≠ []} ≥ (2^a-1)*2^ell) := by
 refine ⟨jG,5,pg,?_⟩
 intro n hn hard soft m ends E lists nO Fn obs valid code size score bank input a ha prefixBits ell slots enc belongs
 refine ⟨cZ n a hard soft ell,?_,?_,?_⟩
 · intro tape
   exact qu n a hn hard soft ell tape
 · intro tape s j hne
   rcases pM n hn hard soft nO a ell tape s j hne with ⟨f,h1,h2,h3,h4⟩
   exact ⟨f,⟨h1,h2,h3⟩,h4⟩
 · exact sp n hn hard soft nO a ha
end AlgProofs
end PEqualNP.Outside.L_meta_33625
theorem PEqualNP.Outside.L_meta_33625 : (let header := fun j : Nat => List.replicate j true ++ [false]
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)
let bits := fun (w z : Nat) => (List.range w).map (fun h => z.testBit h)
let pairs := fun k : Nat => (List.finRange k).flatMap (fun i =>
    ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
∃ (search : List Bool → List Bool) (d : Nat), fast search ∧
∀ (n : Nat), 2 ≤ n →
  ∀ (hard : List (Finset (Fin n) × Finset (Fin n)))
    (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool)),
  let m := soft.length
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let E := (pairs n).toFinset.filter (fun e =>
    ∀ z ∈ hard, ¬(ends e ⊆ z.1) ∧ ¬(ends e ⊆ z.2))
  let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
    Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ S, ends e ⊆ t.1.1 ∨ ends e ⊆ t.1.2
  (∀ S ⊆ E, 2 ≤ S.card →
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f)) →
    (soft.filter (fun t => t.2 && decide (lists S t))).length =
      (soft.filter (fun t => !t.2 && decide (lists S t))).length) →
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R T : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ T))
  let valid := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    ∀ z ∈ hard, obs f z.1 z.2 = false
  let code := fun f : Fn => (pairs n).map (fun e => obs f (ends e) ∅)
  let size := fun f : Fn => ((code f).filter id).length
  let score := fun f : Fn => (soft.filter (fun t => decide (obs f t.1.1 t.1.2 = t.2))).length
  let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
  let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
    header m ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
  ∀ a : Nat, 1 ≤ a →
    let prefixBits := header a ++ input
    let ell := (prefixBits.length+2)^d
    let slots := (List.finRange (n/2+1)).flatMap (fun s =>
      (List.finRange (m+1)).map (fun j => (s,j)))
    let enc := fun word : List Bool => if word.isEmpty then List.replicate ((pairs n).length+1) false
      else true::word
    let belongs := fun (f : Fn) (s : Fin (n/2+1)) (j : Fin (m+1)) =>
      valid f ∧ size f = s.val ∧ score f = j.val
    ∃ words : (Fin ell → Bool) → Fin (n/2+1) → Fin (m+1) → List Bool,
      (∀ tape, search (prefixBits ++ List.ofFn tape) =
        slots.flatMap (fun z => enc (words tape z.1 z.2))) ∧
      (∀ tape s j, words tape s j ≠ [] → ∃ f : Fn, belongs f s j ∧ words tape s j = code f) ∧
      2^a * Nat.card {tape : Fin ell → Bool // ∀ s j, (∃ f : Fn, belongs f s j) →
        words tape s j ≠ []} ≥ (2^a-1)*2^ell) := by
  exact PEqualNP.Outside.L_meta_33625.pnp_main
