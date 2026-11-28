import PEqualNP.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_896_aux
namespace Lib
abbrev CPTs (f : List Bool → List Bool) : Prop := PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f
end Lib
section
namespace Lib.Machines
open Turing
theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih
theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
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
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab
section pushes
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0
theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]
end pushes
noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)
theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this
theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
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
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega
theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]
theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]
theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)
def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
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
theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp
theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp
theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp
theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp
theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]
theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a
theorem constList_polyTime (l : List Bool) :
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
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := by simp } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
section update
variable {ι : Type} [DecidableEq ι] {β : ι → Type}
theorem update3_fst (E : ∀ i, β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]
theorem update3_snd (E : ∀ i, β i) {a b c : ι} (hbc : b ≠ c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]
end update
variable (M1 M2 : FinTM2)
abbrev CK : Type := Option (M1.K ⊕ M2.K)
abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (Sum.inl k) => M1.Γ k
  | some (Sum.inr k) => M2.Γ k
abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))
def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt
variable (M1 M2)
def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map φ))
      (.branch (fun s => s.2.2.isSome)
        (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
        (.goto fun _ => Sum.inr (Sum.inr true)))
def tB : Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o => (s.1, s.2.1, o))
      (.branch (fun s => s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
          (.goto fun _ => Sum.inr (Sum.inr true)))
        (.goto fun _ => Sum.inr (Sum.inl M2.main)))
def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr false) => tA M1 M2 φ d
  | Sum.inr (Sum.inr true) => tB M1 M2 d
def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
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
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := prog M1 M2 φ d }
variable {M1 M2}
def embStk1 (S : ∀ k, List (M1.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []
def embStk2 (S : ∀ k, List (M2.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k
theorem embStk1_update (S : ∀ k, List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    (embStk1 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
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
theorem embStk2_update (S : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    (embStk2 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
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
theorem embStk1_nil :
    (embStk1 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl
theorem embStk2_nil :
    (embStk2 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl
def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, w), embStk1 c.stk⟩
def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (u, c.var, b), embStk2 c.stk⟩
theorem sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
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
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl
theorem sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u, v, b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
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
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl
variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))
theorem step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)
theorem step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)
def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k, List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
theorem st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]
theorem st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) none = t := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_self]
theorem st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
  unfold st
  rw [Function.update_self]
theorem st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _
theorem st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) none t' = st l t' u :=
  update3_snd _ (by simp) _ _ _ _
theorem st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
  Function.update_idem _ _ _
theorem st_start (l : List (M1.Γ M1.k₁)) :
    (st l [] [] : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
  unfold st
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
theorem st_end (u : List (M2.Γ M2.k₀)) :
    (st [] [] u : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)
abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
theorem stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst, st_snd, st_set_snd]
theorem stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] t u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [st_set_fst]
theorem stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [st_set_snd, st_thd, st_set_thd]
theorem stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] [] u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] u⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [st_set_snd]
theorem loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e, ih]
    simp
theorem loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
    ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e, ih]
    simp
theorem transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
    ∃ n, n ≤ 2 * o.length + 2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
            Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩ := by
  cases d with
  | none =>
    have := hd rfl
    have ho : o = [] := by
      cases o with
      | nil => rfl
      | cons x _ => exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1, by omega, ?_⟩
    show some _ = some _
    simp only [prog, tA, TM2.stepAux, List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl, Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1), by simp; omega, ?_⟩
    rw [Function.iterate_add_apply, ← st_start, loopA, loopB, ← st_end]
    simp
theorem emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState, none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl
theorem emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)), (M1.initialState, w),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2) := by
  rw [haltList_eq]
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl
theorem emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)), (u, M2.initialState, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2) := by
  rw [initList_eq]
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl
theorem emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl
theorem comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2) := by
  have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState, none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d, emb1_halt] at p1
  obtain ⟨nt, hnt, pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
  have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ d] at p2
  refine ⟨s2 + (nt + s1), by omega, ?_, ?_⟩
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, p1, pt, p2]
    rfl
theorem comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1 : TM2ComputableInPolyTime ea eb f)
    (c2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : Polynomial ℕ :=
    c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
  have key : ∀ a, ∃ n, n ≤ T.eval (ea a).length ∧
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
    obtain ⟨n, hn, hlen, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 := r1.steps_le_m
    have b2 := r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul : maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
    have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time := eval_mono _ (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {Γ₀ Γ₁ : Type}
abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool → Type
  | some false => Γ₀
  | none => Option Γ₀
  | some true => Γ₁
def fmProg (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
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
def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
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
def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u
theorem fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]
theorem fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]
theorem fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]
theorem fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _
theorem fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _
theorem fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _
theorem fst3_start (l : List Γ₀) :
    (fst3 l [] [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
theorem fst3_end (u : List Γ₁) :
    (fst3 [] [] u : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ : Γ₀ → Option Γ₁) (d : Option Γ₁)
theorem fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]
theorem fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]
theorem fmB_cons (hd : d = none → ∀ x, φ x = none) (b : Option Γ₀) (x : Γ₀)
    (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some, Bool.cond_true, TM2.stepAux,
        Option.toList_some, List.singleton_append]
      rw [fst3_thd, fst3_set_thd]
      simp [hφ]
theorem fmB_nil (b : Option Γ₀) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]
theorem fmLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
    rw [e, ih]
    simp
theorem fmLoopB (hd : d = none → ∀ x, φ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]
theorem fm_run [Fintype Γ₀] (hd : d = none → ∀ x, φ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
theorem filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : d = none → ∀ x, φ x = none := by
    intro hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
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
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := fm_run φ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
            ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive TPK : Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq
instance : Fintype TPK :=
  Fintype.ofList [.inp, .t1, .t2, .t3, .out] (fun x => by cases x <;> simp)
inductive TPL : Type
  | a | b | c | e
  deriving DecidableEq
instance : Fintype TPL :=
  Fintype.ofList [.a, .b, .c, .e] (fun x => by cases x <;> simp)
variable {Γ₀ Γ₁ : Type}
abbrev TPΓ (Γ₀ Γ₁ : Type) : TPK → Type
  | .inp => Γ₀
  | .t1 => Option Γ₀
  | .t2 => Option Γ₀
  | .t3 => Option Γ₀
  | .out => Γ₁
def tpWrite (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s => (s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
      | none => .goto fun _ => lbl)
    (.goto fun _ => lbl)
def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .t1 (fun s => s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t2 (fun s => s) (tpWrite φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t3 (fun s => s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (tpWrite φ₁ d .e)
        .halt)
def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := tpProg φ₁ φ₂ d
def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (TPΓ Γ₀ Γ₁ k)
  | .inp => l
  | .t1 => a
  | .t2 => b
  | .t3 => c
  | .out => u
theorem st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .inp l' = st5 l' a b c u := by
  funext k; cases k <;> simp [st5]
theorem st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t1 a' = st5 l a' b c u := by
  funext k; cases k <;> simp [st5]
theorem st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t2 b' = st5 l a b' c u := by
  funext k; cases k <;> simp [st5]
theorem st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t3 c' = st5 l a b c' u := by
  funext k; cases k <;> simp [st5]
theorem st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (st5 l a b c u) .out u' = st5 l a b c u' := by
  funext k; cases k <;> simp [st5]
theorem st5_start (l : List Γ₀) :
    (st5 l [] [] [] [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .inp l := by
  funext k; cases k <;> simp [st5]
theorem st5_end (u : List Γ₁) :
    (st5 [] [] [] [] u : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .out u := by
  funext k; cases k <;> simp [st5]
abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁)
theorem tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
    (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp, st5_set_t1]
theorem tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, none, st5 [] a b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp]
theorem tpB_cons (hd : d = none → ∀ x, φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
    (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, some x, st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2,
        st5_set_out, hφ]
theorem tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, none, st5 [] [] b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t1]
theorem tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, some x, st5 [] [] b (some x :: c) u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2, st5_set_t3]
theorem tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, none, st5 [] [] [] c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2]
theorem tpE_cons (hd : d = none → ∀ x, φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
    (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, some x, st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, st5_set_out, hφ]
theorem tpE_nil (s : Option Γ₀) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨none, none, st5 [] [] [] [] u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t3]
theorem tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
    ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
          (some (⟨some .a, s, st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, none, st5 [] (l.reverse.map some ++ a) b c u⟩ := by
  intro l
  induction l with
  | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e, ih]
    simp
theorem tpLoopB (hd : d = none → ∀ x, φ₂ x = none) (c : List (Option Γ₀)) :
    ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .b, s, st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b, s, st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, some x, st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e, ih]
    cases hφ : φ₂ x <;> simp [hφ]
theorem tpLoopC (u : List Γ₁) :
    ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .c, s, st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, none, st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
  intro t
  induction t with
  | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c, s, st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, some x, st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e, ih]
    simp
theorem tpLoopE (hd : d = none → ∀ x, φ₁ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .e, s, st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨none, none, st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e, s, st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, some x, st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e, ih]
    cases hφ : φ₁ x <;> simp [hφ]
theorem tp_run [Fintype Γ₀] (hd₁ : d = none → ∀ x, φ₁ x = none)
    (hd₂ : d = none → ∀ x, φ₂ x = none) (l : List Γ₀) :
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
    (some (⟨some .a, none, Function.update (fun _ => []) .inp l⟩ : TPCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) .out
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
  have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .a, none, st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ := by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
    have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none, none, st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
    have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    ← st5_start, hA, hB, hC, hE, st5_end]
theorem twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ φ : αΓ → Option βΓ, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
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
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
            ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
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
instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.T, FX.O] (fun x => by cases x <;> simp)
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq
instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)
variable (M : FinTM2)
abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => Bool ⊕ Bool
  | Sum.inr FX.W => Bool
  | Sum.inr FX.T => Bool
  | Sum.inr FX.O => Bool ⊕ Bool
abbrev FstΛ : Type := M.Λ ⊕ FL
abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)
def bit : Option (Bool ⊕ Bool) → Bool
  | none => false
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b
def isFst : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false
variable {M}
def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)
variable (M)
def firstProg (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l => trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)
def firstM (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := firstProg M e₀ e₁ }
variable {M}
def fstk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) : ∀ k, List (FstΓ M k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.T => t
  | Sum.inr FX.O => o
section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
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
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl
theorem fstk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i' = fstk S i' w t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
theorem fstk_set_W (w' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w' = fstk S i w' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
theorem fstk_set_T (t' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t' = fstk S i w t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
theorem fstk_set_O (o' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o' = fstk S i w t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
end fstk
abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)
def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w t o⟩
theorem simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF q) ((v, b) : Fstσ M) (fstk S i w t o) =
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
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl
theorem stepF (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) (b : Option (Bool ⊕ Bool))
    (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]
variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)
section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w t o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w t o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_T : fstk S i w t o (Sum.inr FX.T) = t := rfl
@[simp] theorem fstk_O : fstk S i w t o (Sum.inr FX.O) = o := rfl
end fstk
variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))
theorem f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_T, isFst, bit]
theorem f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isFst, bit]
theorem f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]
theorem loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
theorem f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]
theorem f2_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]
theorem loop2 : ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inl M.main), (v, none),
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
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
    rw [e, ih]; simp
theorem f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, bit]
theorem f3_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]
theorem loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w [] o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e, ih]; simp
theorem f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]
theorem f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, none), fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]
theorem loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
    rw [e, ih]; simp
theorem f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_O, bit]
theorem f5_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨none, (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]
theorem loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] t o⟩ : FCfg1 M)) =
      some ⟨none, (v, none), fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e, ih]; simp
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)
theorem fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k, List (FstΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl
theorem fstk_nil_I (i : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) i [] [] [] : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])
theorem fstk_nil_O (o : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) [] [] [] o : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])
theorem embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
  rw [initList_eq]; rfl
theorem embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
  rw [haltList_eq]; rfl
theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp
theorem encodePair_left (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]
theorem encodePair_right (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]
theorem encodePair_length (x w : List Bool) :
    (encodePair (x, w)).length = x.length + w.length := by
  simp [encodePair]
theorem first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x, w0)).length + 1]
      (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x, w0)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
      (encodePair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁, w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length, List.length_reverse, List.length_map]
  omega
theorem first_polyTime (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2))) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩
end Lib.Machines
end
section
namespace Lib.Machines.Iter
open Turing
inductive IX
  | I | C | T | O
  deriving DecidableEq
instance : Fintype IX :=
  Fintype.ofList [IX.I, IX.C, IX.T, IX.O] (fun x => by cases x <;> simp)
inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq
instance : Fintype IL :=
  Fintype.ofList [IL.l1, IL.l2, IL.l3, IL.l4, IL.l5, IL.l6] (fun x => by cases x <;> simp)
variable (M : FinTM2)
abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr IX.I => Bool ⊕ Bool
  | Sum.inr IX.C => Bool
  | Sum.inr IX.T => Bool
  | Sum.inr IX.O => Bool
abbrev ItΛ : Type := M.Λ ⊕ IL
abbrev Itσ : Type := M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr IL.l4)
variable (M)
def iterProg (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l => trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1))
          (.push (Sum.inr IX.C) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1)))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l2 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr IL.l2))
        (.goto fun _ => Sum.inr IL.l3))
  | Sum.inr IL.l3 =>
    .pop (Sum.inr IX.C) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.goto fun _ => Sum.inl M.main)
        (.goto fun _ => Sum.inr IL.l5))
  | Sum.inr IL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l4))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l5 =>
    .pop (Sum.inl M.k₀) (fun s o => (s.1, o.map fun y => Sum.inl (d₀ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l5))
        (.goto fun _ => Sum.inr IL.l6))
  | Sum.inr IL.l6 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.O) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l6))
        .halt)
def iterM (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ IX
    k₀ := Sum.inr IX.I
    k₁ := Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main := Sum.inr IL.l1
    σ := Itσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := iterProg M e₀ d₀ e₁ }
variable {M}
def istk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    ∀ k, List (ItΓ M k)
  | Sum.inl k => S k
  | Sum.inr IX.I => i
  | Sum.inr IX.C => cn
  | Sum.inr IX.T => t
  | Sum.inr IX.O => o
section istk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
@[simp] theorem istk_M (k : M.K) : istk S i cn t o (Sum.inl k) = S k := rfl
@[simp] theorem istk_I : istk S i cn t o (Sum.inr IX.I) = i := rfl
@[simp] theorem istk_C : istk S i cn t o (Sum.inr IX.C) = cn := rfl
@[simp] theorem istk_T : istk S i cn t o (Sum.inr IX.T) = t := rfl
@[simp] theorem istk_O : istk S i cn t o (Sum.inr IX.O) = o := rfl
theorem istk_set_M (k : M.K) (x : List (M.Γ k)) :
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
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl
theorem istk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr IX.I) i' = istk S i' cn t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
theorem istk_set_C (cn' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.C) cn' = istk S i cn' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
theorem istk_set_T (t' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.T) t' = istk S i cn t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
theorem istk_set_O (o' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.O) o' = istk S i cn t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
end istk
abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def embI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl), (c.var, b), istk c.stk i cn t o⟩
theorem simI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trI q) ((v, b) : Itσ M) (istk S i cn t o) =
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
    simp only [trI, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl
theorem stepI (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
    (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (iterProg M e₀ d₀ e₁) (embI b i cn t o c) = some (embI b i cn t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)
theorem embI_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (l : List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₀ l) i cn t o⟩ : ICfg M) := by
  rw [initList_eq]; rfl
theorem embI_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (m : List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₁ m) i cn t o⟩ : ICfg M) := by
  rw [haltList_eq]; rfl
theorem istk_nil : (istk (fun _ => []) [] [] [] [] : ∀ k, List (ItΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl
theorem istk_nil_I (i : List (Bool ⊕ Bool)) :
    (istk (fun _ => []) i [] [] [] : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.I) i :=
  (istk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [istk_nil])
theorem istk_nil_O (o : List Bool) :
    (istk (fun _ => []) [] [] [] o : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.O) o :=
  (istk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [istk_nil])
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
variable (v : M.σ) (S : ∀ k, List (M.Γ k))
theorem i1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_T, isFst, bit]
theorem i1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_C, isFst, bit]
theorem i1_nil (b : Option (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S [] cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk S [] cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I]
theorem iloop1 (o : List Bool) :
    ∀ (i : List (Bool ⊕ Bool)) (cn t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[i.length + 1]
        (some (⟨some (Sum.inr IL.l1), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]
theorem i2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]
theorem i2_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l3), (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]
theorem iloop2 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l3), (v, none),
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
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      i2_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp
theorem i3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i (a :: cn) t o⟩ : ICfg M) =
      some ⟨some (Sum.inl M.main), (v, some (Sum.inl a)), istk S i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]
theorem i3_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i [] t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, none), istk S i [] t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]
theorem i4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]
theorem i4_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk (Function.update S M.k₁ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]
theorem iloop4 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4), (v, b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      i4_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp
theorem i5_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₀) (m : List (M.Γ M.k₀))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]
theorem i5_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, none), istk (Function.update S M.k₀ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]
theorem iloop5 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₀)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l6), (v, none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5), (v, b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      i5_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp
theorem i6_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_O, bit]
theorem i6_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨none, (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]
theorem iloop6 (i : List (Bool ⊕ Bool)) (cn : List Bool) :
    ∀ (t o : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨none, (v, none), istk S i cn [] (t.reverse ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ :=
      i6_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp
theorem update_nil_nil (k : M.K) :
    Function.update (fun _ => [] : ∀ k, List (M.Γ k)) k [] = fun _ => [] :=
  Function.update_eq_self k (fun _ => [] : ∀ k, List (M.Γ k))
theorem main_loop (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)), z.length + k * cn.length ≤ L →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse, List.length_map, List.length_nil] at hL ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hgz : (g z).length ≤ z.length + k := hk z
    have hkk : k * (cn.length + 1) = k * cn.length + k := Nat.mul_succ _ _
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (by omega)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega
theorem iter_run (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : y.length + k * u.length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega
theorem iter_polyTime (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (k : ℕ) (hk : ∀ y : List Bool, (g y).length ≤ y.length + k) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ := Polynomial.X + Polynomial.C k * Polynomial.X
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hku : k * u.length ≤ k * (y.length + u.length) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨n, hn, hr⟩ := iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
      (y.length + u.length + k * (y.length + u.length)) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
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
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
theorem main_loop_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length, (g^[j] z).length ≤ L) →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    simp only [List.length_reverse, List.length_map, List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    have hgz : (g z).length ≤ L := hL 1 (by omega)
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (fun j hj => by
      have := hL (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega
theorem iter_run_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : ∀ j ≤ u.length, (g^[j] y).length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega
theorem iterate_length_measure (g : List Bool → List Bool) (m : List Bool → ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y) (y : List Bool) :
    ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    have h1 := hm (g^[j] y)
    have h2 := hg (g^[j] y)
    obtain ⟨i1, i2⟩ := ih
    generalize j * m y = A at i2 ⊢
    exact ⟨by omega, by omega⟩
theorem measure_arith (A B L V y u : ℕ) (hLV : L ≤ V) (hAB : A ≤ B) :
    A + 2 * L + 2 * y + u + 5 ≤ B + 2 * V + 3 * (y + u) + 5 := by
  omega
theorem iter_polyTime_measure (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ :=
    Polynomial.X + Polynomial.X * (Polynomial.C a * Polynomial.X + Polynomial.C a)
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hL : ∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length + u.length * (a * y.length + a) := by
      intro j hj
      have h1 := (iterate_length_measure g m hm hg y j).2
      have h2 : j * m y ≤ u.length * (a * y.length + a) := Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n, hn, hr⟩ := iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
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
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    exact measure_arith _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩
end Lib.Machines.Iter
end
section
namespace Lib.Machines
open PEqualNP.Library
open Turing
inductive MulK
  | I | A | B | C | O
  deriving DecidableEq
instance : Fintype MulK :=
  Fintype.ofList [.I, .A, .B, .C, .O] (fun x => by cases x <;> simp)
inductive MulL
  | split | outer | copy | back | clean
  deriving DecidableEq
instance : Fintype MulL :=
  Fintype.ofList [.split, .outer, .copy, .back, .clean] (fun x => by cases x <;> simp)
abbrev MulΓ : MulK → Type
  | .I => Bool ⊕ Bool
  | .A => Bool
  | .B => Bool
  | .C => Bool
  | .O => Bool
def mulProg : MulL → TM2.Stmt MulΓ MulL (Option Bool)
  | .split =>
    .pop .I (fun _ o => o.map Sum.isLeft)
      (.branch (fun s => s.isSome)
        (.branch (fun s => s == some true)
          (.push .A (fun _ => true) (.goto fun _ => .split))
          (.push .B (fun _ => true) (.goto fun _ => .split)))
        (.goto fun _ => .outer))
  | .outer =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .copy)
        (.goto fun _ => .clean))
  | .copy =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .C (fun _ => true) (.push .O (fun _ => true) (.goto fun _ => .copy)))
        (.goto fun _ => .back))
  | .back =>
    .pop .C (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))
  | .clean =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .clean)
        .halt)
def mulTM : FinTM2 where
  K := MulK
  k₀ := .I
  k₁ := .O
  Γ := MulΓ
  Λ := MulL
  main := .split
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := mulProg
def mstk (i : List (Bool ⊕ Bool)) (a b c o : List Bool) : ∀ k, List (MulΓ k)
  | .I => i
  | .A => a
  | .B => b
  | .C => c
  | .O => o
@[simp] theorem mstk_I (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .I = i := rfl
@[simp] theorem mstk_A (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .A = a := rfl
@[simp] theorem mstk_B (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .B = b := rfl
@[simp] theorem mstk_C (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .C = c := rfl
@[simp] theorem mstk_O (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .O = o := rfl
@[simp] theorem mstk_set_I (i i' : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    Function.update (mstk i a b c o) .I i' = mstk i' a b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_A (i : List (Bool ⊕ Bool)) (a a' b c o : List Bool) :
    Function.update (mstk i a b c o) .A a' = mstk i a' b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_B (i : List (Bool ⊕ Bool)) (a b b' c o : List Bool) :
    Function.update (mstk i a b c o) .B b' = mstk i a b' c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_C (i : List (Bool ⊕ Bool)) (a b c c' o : List Bool) :
    Function.update (mstk i a b c o) .C c' = mstk i a b c' o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_O (i : List (Bool ⊕ Bool)) (a b c o o' : List Bool) :
    Function.update (mstk i a b c o) .O o' = mstk i a b c o' := by
  funext k; cases k <;> simp [mstk]
theorem mstk_start (i : List (Bool ⊕ Bool)) :
    mstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .I i := by
  funext k; cases k <;> simp [mstk]
theorem mstk_end (o : List Bool) :
    mstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .O o := by
  funext k; cases k <;> simp [mstk]
abbrev MulCfg : Type := TM2.Cfg MulΓ MulL (Option Bool)
abbrev mulStep : Option MulCfg → Option MulCfg := flip bind (TM2.step mulProg)
theorem split_inl (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inl y :: i) a b c o⟩) =
      some ⟨some .split, some true, mstk i (true :: a) b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem split_inr (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inr y :: i) a b c o⟩) =
      some ⟨some .split, some false, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem split_nil (s : Option Bool) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk [] a b c o⟩) =
      some ⟨some .outer, none, mstk [] a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem outer_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i (y :: a) b c o⟩) =
      some ⟨some .copy, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem outer_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i [] b c o⟩) =
      some ⟨some .clean, none, mstk i [] b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem copy_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .copy, some y, mstk i a b (true :: c) (true :: o)⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem copy_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a [] c o⟩) =
      some ⟨some .back, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem back_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b (y :: c) o⟩) =
      some ⟨some .back, some y, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem back_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a b o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b [] o⟩) =
      some ⟨some .outer, none, mstk i a b [] o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem clean_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .clean, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
theorem clean_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a [] c o⟩) =
      some ⟨none, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]
abbrev rep (n : ℕ) : List Bool := List.replicate n true
theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl
theorem splitLoopW (a : List Bool) :
    ∀ (w : List Bool) (b : ℕ) (s : Option Bool),
      mulStep^[w.length + 1] (some ⟨some .split, s, mstk (w.map Sum.inr) a (rep b) [] []⟩) =
        some ⟨some .outer, none, mstk [] a (rep (w.length + b)) [] []⟩ := by
  intro w
  induction w with
  | nil => intro b s; simpa using split_nil s a (rep b) [] []
  | cons y w ih =>
    intro b s
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, split_inr, rep_succ, ih]
    rw [show w.length + (b + 1) = w.length + 1 + b from by omega]
theorem splitLoopX (w : List Bool) :
    ∀ (x : List Bool) (a : ℕ) (s : Option Bool),
      mulStep^[x.length + (w.length + 1)]
          (some ⟨some .split, s, mstk (x.map Sum.inl ++ w.map Sum.inr) (rep a) [] [] []⟩) =
        some ⟨some .outer, none, mstk [] (rep (x.length + a)) (rep w.length) [] []⟩ := by
  intro x
  induction x with
  | nil =>
    intro a s
    simpa using splitLoopW (rep a) w 0 s
  | cons y x ih =>
    intro a s
    rw [List.length_cons, show x.length + 1 + (w.length + 1) = (x.length + (w.length + 1)) + 1
      from by omega, Function.iterate_succ_apply, List.map_cons, List.cons_append, split_inl,
      rep_succ, ih]
    rw [show x.length + (a + 1) = x.length + 1 + a from by omega]
theorem copyLoop (a : List Bool) :
    ∀ (b c o : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .copy, s, mstk [] a (rep b) (rep c) (rep o)⟩) =
        some ⟨some .back, none, mstk [] a [] (rep (b + c)) (rep (b + o))⟩ := by
  intro b
  induction b with
  | zero => intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
  | succ b ih =>
    intro c o s
    rw [Function.iterate_succ_apply, ← rep_succ b, copy_cons, rep_succ, rep_succ, ih]
    rw [show b + (c + 1) = b + 1 + c from by omega, show b + (o + 1) = b + 1 + o from by omega]
theorem backLoop (a o : List Bool) :
    ∀ (c b : ℕ) (s : Option Bool),
      mulStep^[c + 1] (some ⟨some .back, s, mstk [] a (rep b) (rep c) o⟩) =
        some ⟨some .outer, none, mstk [] a (rep (c + b)) [] o⟩ := by
  intro c
  induction c with
  | zero => intro b s; simpa using back_nil s [] a (rep b) o
  | succ c ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← rep_succ c, back_cons, rep_succ, ih]
    rw [show c + (b + 1) = c + 1 + b from by omega]
theorem outerLoop (b : ℕ) :
    ∀ (a o : ℕ) (s : Option Bool),
      mulStep^[a * (2 * b + 3) + 1] (some ⟨some .outer, s, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .clean, none, mstk [] [] (rep b) [] (rep (a * b + o))⟩ := by
  intro a
  induction a with
  | zero => intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
  | succ a ih =>
    intro o s
    rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + ((b + 1) + ((b + 1) + 1))
      from by ring, Function.iterate_add_apply mulStep (a * (2 * b + 3) + 1),
      Function.iterate_add_apply mulStep (b + 1) ((b + 1) + 1),
      Function.iterate_succ_apply mulStep (b + 1), ← rep_succ a, outer_cons]
    have h1 : mulStep^[b + 1]
        (some ⟨some .copy, some true, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩ :=
      copyLoop (rep a) b 0 o (some true)
    rw [h1]
    have h2 : mulStep^[b + 1]
        (some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩) =
        some ⟨some .outer, none, mstk [] (rep a) (rep b) [] (rep (b + o))⟩ :=
      backLoop (rep a) (rep (b + o)) b 0 none
    rw [h2, ih]
    rw [show a * b + (b + o) = (a + 1) * b + o from by ring]
theorem cleanLoop (o : List Bool) :
    ∀ (b : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .clean, s, mstk [] [] (rep b) [] o⟩) =
        some ⟨none, none, mstk [] [] [] [] o⟩ := by
  intro b
  induction b with
  | zero => intro s; simpa using clean_nil s [] [] [] o
  | succ b ih =>
    intro s
    rw [Function.iterate_succ_apply, ← rep_succ b, clean_cons, ih]
def mulSteps (x w : ℕ) : ℕ := (w + 1) + ((x * (2 * w + 3) + 1) + (x + (w + 1)))
theorem mul_run (x w : List Bool) :
    (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
        (some (initList mulTM (x.map Sum.inl ++ w.map Sum.inr))) =
      some (haltList mulTM (rep (x.length * w.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
    (some c)) (initList_eq mulTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
  show mulStep^[mulSteps x.length w.length]
    (some (⟨some .split, none, Function.update (fun _ => []) .I
      (x.map Sum.inl ++ w.map Sum.inr)⟩ : MulCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (rep (x.length * w.length))⟩ : MulCfg)
  rw [← mstk_start, ← mstk_end, mulSteps, Function.iterate_add_apply mulStep (w.length + 1),
    Function.iterate_add_apply mulStep (x.length * (2 * w.length + 3) + 1)]
  have h1 : mulStep^[x.length + (w.length + 1)]
      (some ⟨some .split, none, mstk (x.map Sum.inl ++ w.map Sum.inr) [] [] [] []⟩) =
      some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩ :=
    splitLoopX w x 0 none
  rw [h1]
  have h2 : mulStep^[x.length * (2 * w.length + 3) + 1]
      (some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩) =
      some ⟨some .clean, none, mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
    outerLoop w.length x.length 0 none
  rw [h2, cleanLoop]
theorem mul_polyTime :
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
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_pow, encodePair, List.length_append,
            List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open PEqualNP.Library
private theorem filterMap_map_some {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a, φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]
private theorem filterMap_map_none {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a, φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]
theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
  obtain ⟨c1⟩ := hf
  obtain ⟨c2⟩ := hg
  exact comp_polyTime ea eb ec f g c1 c2
theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ Sum.inl (fun _ => rfl) w,
    filterMap_map_some Sum.inl _ Sum.inr (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp
theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) := by
  refine twoPass_polyTime _ _ _
    (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
  intro x
  have h1 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
    Sum.inl (fun _ => rfl) x
  have h2 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
    Sum.inr (fun _ => rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair, h1, h2]
theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp
theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp
theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp
theorem cpt_first {f : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨c⟩ := hf
  exact first_polyTime f c
theorem cpt_second {g : List Bool → List Bool}
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap
theorem cpt_pair {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (f x, g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)
theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => x) := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
  intro x
  have h := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
    (fun _ => rfl) x
  simp only [List.map_id'] at h
  exact h.symm
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
theorem output_length_poly (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ∃ q : Polynomial ℕ, ∀ x : List Bool, (f x).length ≤ q.eval x.length := by
  obtain ⟨c⟩ := hf
  refine ⟨Polynomial.X + Polynomial.C (maxPush c.tm) * c.time, fun x => ?_⟩
  obtain ⟨⟨steps, hev⟩, hle⟩ := c.outputsFun x
  have hev' : (flip bind (TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main, c.tm.initialState, Function.update (fun _ => []) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none, c.tm.initialState, Function.update (fun _ => []) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
    rw [← initList_eq, ← haltList_eq]; exact hev
  have key := run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self, List.length_map] at key
  have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x) : ∀ k, List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk]; simp
    · rw [Function.update_of_ne hk]; simp
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
    _ ≤ x.length + maxPush c.tm * c.time.eval x.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l
def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l
theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]
inductive TrK : Type
  | inp | tmp | out
  deriving DecidableEq
instance : Fintype TrK :=
  Fintype.ofList [.inp, .tmp, .out] (fun x => by cases x <;> simp)
variable {Γ₀ Γ₁ Q : Type}
abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | .inp => Γ₀
  | .tmp => Q × Option Γ₀
  | .out => Γ₁
abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool
def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q
def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none
def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList
def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l
theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]
theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]
def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push .out (fun s => (o s).getD dd) next
      | none => next)
    next
def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .tmp (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push .tmp (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop .tmp (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d
def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | .inp => l
  | .tmp => t
  | .out => u
theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .inp l' = trSt l' t u := by
  funext k; cases k <;> simp [trSt]
theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .tmp t' = trSt l t' u := by
  funext k; cases k <;> simp [trSt]
theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) .out u' = trSt l t u' := by
  funext k; cases k <;> simp [trSt]
theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .inp l := by
  funext k; cases k <;> simp [trSt]
theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .out u := by
  funext k; cases k <;> simp [trSt]
abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]
variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)
theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]
theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]
theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .tmp = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]
theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]
theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]
theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]
theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]
theorem fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
theorem fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin : Q → Option βΓ) (q₀ : Q)
    (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a => ((δ q a).1, (δ q a).2, none)) fin q₀
    (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))
end Lib.Machines
end
section
namespace Lib.Machines
open PEqualNP.Library
private theorem cpt_mul {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate ((f x).length * (g x).length) true) :=
  cpt_comp (cpt_pair hf hg) mul_polyTime
private theorem pow_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
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
      rw [List.length_replicate, pow_succ, Nat.mul_comm]
    rw [← e]
    exact h
theorem clock_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
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
      rw [Polynomial.eval_add, List.replicate_add]
    rw [← e]
    exact h
  | monomial n a =>
    have h := cpt_mul (hconst (List.replicate a true)) (pow_polyTime hconst n)
    have e : (fun x : List Bool => List.replicate ((List.replicate a true).length *
        (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool =>
          List.replicate ((Polynomial.monomial n a).eval x.length) true) := by
      funext x
      rw [List.length_replicate, List.length_replicate, Polynomial.eval_monomial]
    rw [← e]
    exact h
end Lib.Machines
end
section
theorem Lib.L055 : ∀ p : Polynomial ℕ,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) :=
  fun p => Lib.Machines.clock_polyTime
    (fun l => Lib.Machines.constList_polyTime l) p
end
section
namespace Lib.Universal
inductive Instr
  | push (k : ℕ) (tbl : List ℕ) (next : ℕ)
  | pop (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | peek (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | load (tbl : List ℕ) (next : ℕ)
  | branch (tbl : List ℕ) (next₁ next₂ : ℕ)
  | goto (tbl : List ℕ)
  | halt
  deriving DecidableEq, Repr
structure Cfg where
  pc : Option ℕ
  state : ℕ
  stk : List (List ℕ)
  deriving DecidableEq, Repr
def topIndex (st : List ℕ) : ℕ :=
  match st with
  | [] => 0
  | s :: _ => s + 1
def exec (i : Instr) (v : ℕ) (S : List (List ℕ)) : Cfg :=
  match i with
  | .push k tbl next => ⟨some next, v, S.set k (tbl.getD v 0 :: S.getD k [])⟩
  | .pop k tbl w next =>
    ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S.set k (S.getD k []).tail⟩
  | .peek k tbl w next => ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S⟩
  | .load tbl next => ⟨some next, tbl.getD v 0, S⟩
  | .branch tbl next₁ next₂ => ⟨some (if tbl.getD v 0 ≠ 0 then next₁ else next₂), v, S⟩
  | .goto tbl => ⟨some (tbl.getD v 0), v, S⟩
  | .halt => ⟨none, v, S⟩
def step (P : List Instr) (c : Cfg) : Cfg :=
  match c.pc with
  | none => c
  | some n =>
    match P[n]? with
    | none => ⟨none, c.state, c.stk⟩
    | some i => exec i c.state c.stk
structure Code where
  prog : List Instr
  nstk : ℕ
  pc₀ : ℕ
  state₀ : ℕ
  kin : ℕ
  kout : ℕ
  deriving DecidableEq, Repr
def Code.init (c : Code) (input : List ℕ) : Cfg :=
  ⟨some c.pc₀, c.state₀, (List.replicate c.nstk []).set c.kin input⟩
def Code.run (c : Code) (input : List ℕ) (t : ℕ) : Cfg :=
  (step c.prog)^[t] (c.init input)
def Code.outputsWithin (c : Code) (input : List ℕ) (t : ℕ) (out : List ℕ) : Prop :=
  (c.run input t).pc = none ∧ (c.run input t).stk.getD c.kout [] = out
end Lib.Universal
end
section
namespace Lib.Universal
def un (n : ℕ) : List Bool := List.replicate n true
def pairB (a b : List Bool) : List Bool := un a.length ++ false :: (a ++ b)
def unpairB (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)
theorem unpairB_pairB (a b : List Bool) : unpairB (pairB a b) = (a, b) := by
  have h1 : (pairB a b).takeWhile id = un a.length := by
    simp [pairB, un]
  have h2 : (pairB a b).dropWhile id = false :: (a ++ b) := by
    simp [pairB, un]
  simp [unpairB, h1, h2, un]
end Lib.Universal
end
section
namespace Lib.Universal
open Turing
def symIn : Bool ⊕ Bool → ℕ
  | Sum.inl false => 0 | Sum.inl true => 1 | Sum.inr false => 2 | Sum.inr true => 3
def bitCode (b : Bool) : ℕ := if b then 1 else 0
def symOut : ℕ → Bool ⊕ Bool
  | 0 => Sum.inl false | 1 => Sum.inl true | 2 => Sum.inr false | _ => Sum.inr true
theorem symOut_symIn (x : Bool ⊕ Bool) : symOut (symIn x) = x := by
  rcases x with (_ | _) | (_ | _) <;> rfl
theorem symIn_lt (x : Bool ⊕ Bool) : symIn x < 4 := by
  rcases x with (_ | _) | (_ | _) <;> simp [symIn]
theorem bitCode_le (b : Bool) : bitCode b ≤ 1 := by
  cases b <;> simp [bitCode]
theorem step_of_pc_none (P : List Instr) (c : Cfg) (h : c.pc = none) : step P c = c := by
  unfold step; rw [h]
theorem iterate_step_of_pc_none (P : List Instr) (c : Cfg) (h : c.pc = none) (t : ℕ) :
    (step P)^[t] c = c :=
  Function.iterate_fixed (step_of_pc_none P c h) t
theorem Code.outputsWithin_mono (c : Code) (input : List ℕ) {t t' : ℕ} (h : t ≤ t')
    (out : List ℕ) : c.outputsWithin input t out → c.outputsWithin input t' out := by
  intro ho
  have hrun : c.run input t' = c.run input t := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold Code.run
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact iterate_step_of_pc_none _ _ ho.1 s
  unfold Code.outputsWithin
  rw [hrun]
  exact ho
section Flatten
variable {K : Type} {Γ : K → Type} {Λ σ : Type}
def subs : TM2.Stmt Γ Λ σ → List (TM2.Stmt Γ Λ σ)
  | .push k f q => .push k f q :: subs q
  | .peek k f q => .peek k f q :: subs q
  | .pop k f q => .pop k f q :: subs q
  | .load a q => .load a q :: subs q
  | .branch f q₁ q₂ => .branch f q₁ q₂ :: (subs q₁ ++ subs q₂)
  | .goto f => [.goto f]
  | .halt => [.halt]
theorem subs_head (q : TM2.Stmt Γ Λ σ) : ∃ t, subs q = q :: t := by
  cases q <;> (rw [subs]; exact ⟨_, rfl⟩)
def Placed (L : List (TM2.Stmt Γ Λ σ)) (p : ℕ) (q : TM2.Stmt Γ Λ σ) : Prop :=
  ∃ A B, L = A ++ subs q ++ B ∧ A.length = p
theorem Placed.get {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) : L[p]? = some q := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  obtain ⟨t, ht⟩ := subs_head q
  rw [ht]
  simp
theorem Placed.le {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) : p + (subs q).length ≤ L.length := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  simp only [List.length_append]
  omega
theorem Placed.sub {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q r : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) (X Y : List (TM2.Stmt Γ Λ σ)) (hq : subs q = q :: (X ++ subs r ++ Y)) :
    Placed L (p + 1 + X.length) r := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  refine ⟨A ++ q :: X, Y ++ B, ?_, ?_⟩
  · rw [hq]; simp
  · simp; omega
theorem forall₂_tail {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : List.Forall₂ R l₁.tail l₂.tail := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons _ h2 => exact h2
theorem forall₂_singleton {α β : Type} {R : α → β → Prop} {l₁ : List α} {y : β}
    (h : List.Forall₂ R l₁ [y]) : ∃ s, l₁ = [s] ∧ R s y := by
  cases h with
  | cons h1 h3 => cases h3; exact ⟨_, rfl, h1⟩
theorem exists_placed (M : Λ → TM2.Stmt Γ Λ σ) (ls : List Λ) (l : Λ) (h : l ∈ ls) :
    ∃ p, Placed ((ls.map fun l => subs (M l)).flatten) p (M l) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨((s.map fun l => subs (M l)).flatten).length, (s.map fun l => subs (M l)).flatten,
    (t.map fun l => subs (M l)).flatten, by simp, rfl⟩
end Flatten
structure Env (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) where
  M : Λ → TM2.Stmt Γ Λ σ
  nσ : ℕ
  nσ_pos : 0 < nσ
  num : σ → ℕ
  σof : ℕ → σ
  σof_num : ∀ v, σof (num v) = v
  num_lt : ∀ v, num v < nσ
  nK : ℕ
  numK : K → ℕ
  numK_lt : ∀ k, numK k < nK
  numK_inj : Function.Injective numK
  L : List (TM2.Stmt Γ Λ σ)
  start : Λ → ℕ
  placed_start : ∀ l, Placed L (start l) (M l)
  k₀ : K
  inSym : ℕ → Γ k₀
  k₁ : K
  outBit : Γ k₁ → ℕ
namespace Env
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (E : Env K Γ Λ σ)
def W : ℕ := 4 + E.nσ * E.L.length + 1
theorem W_pos : 0 < E.W := by unfold W; omega
def decS (s : ℕ) : Option (Σ k, Γ k) :=
  if s < 4 then some ⟨E.k₀, E.inSym s⟩
  else match E.L[(s - 4) / E.nσ]? with
    | some (.push k f _) => some ⟨k, f (E.σof ((s - 4) % E.nσ))⟩
    | _ => none
def decode (k : K) (s : ℕ) : Option (Γ k) :=
  match E.decS s with
  | some ⟨k', y⟩ => if h : k' = k then some (h ▸ y) else none
  | none => none
theorem decode_of_decS {k : K} {s : ℕ} {y : Γ k} (h : E.decS s = some ⟨k, y⟩) :
    E.decode k s = some y := by
  simp [decode, h]
theorem decode_in {s : ℕ} (h : s < 4) : E.decode E.k₀ s = some (E.inSym s) :=
  E.decode_of_decS (by simp [decS, h])
theorem decode_push {p : ℕ} {k : K} {f : σ → Γ k} {r : TM2.Stmt Γ Λ σ}
    (h : E.L[p]? = some (.push k f r)) {a : ℕ} (ha : a < E.nσ) :
    E.decode k (4 + (a + E.nσ * p)) = some (f (E.σof a)) := by
  apply E.decode_of_decS
  unfold decS
  have e : 4 + (a + E.nσ * p) - 4 = a + E.nσ * p := by omega
  have h4 : ¬ (4 + (a + E.nσ * p) < 4) := by omega
  simp only [h4, ↓reduceIte]
  rw [e, Nat.add_mul_div_left _ _ E.nσ_pos, Nat.div_eq_of_lt ha, zero_add, h,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
theorem decode_lt {k : K} {s : ℕ} {y : Γ k} (h : E.decode k s = some y) : s + 1 < E.W := by
  by_contra hc
  unfold W at hc
  have hd : E.decS s = none := by
    unfold decS
    have h1 : E.L.length ≤ (s - 4) / E.nσ := by
      rw [Nat.le_div_iff_mul_le E.nσ_pos, Nat.mul_comm]
      omega
    have h4 : ¬ (s < 4) := by omega
    simp only [h4, ↓reduceIte]
    rw [List.getElem?_eq_none h1]
  simp [decode, hd] at h
def arg (k : K) : ℕ → Option (Γ k)
  | 0 => none
  | s + 1 => E.decode k s
theorem top_spec {k : K} {ns : List ℕ} {ys : List (Γ k)}
    (h : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    topIndex ns < E.W ∧ E.arg k (topIndex ns) = ys.head? := by
  cases h with
  | nil => exact ⟨E.W_pos, rfl⟩
  | cons h1 _ => exact ⟨E.decode_lt h1, by simpa [topIndex, arg] using h1⟩
def tbl1 (g : ℕ → ℕ) : List ℕ := (List.range E.nσ).map g
def tbl2 (g : ℕ → ℕ → ℕ) : List ℕ :=
  (List.range (E.nσ * E.W)).map fun i => g (i / E.W) (i % E.W)
theorem tbl1_get (g : ℕ → ℕ) {a : ℕ} (ha : a < E.nσ) : (E.tbl1 g)[a]?.getD 0 = g a := by
  simp [tbl1, ha]
theorem tbl2_get (g : ℕ → ℕ → ℕ) {a c : ℕ} (ha : a < E.nσ) (hc : c < E.W) :
    (E.tbl2 g)[a * E.W + c]?.getD 0 = g a c := by
  have hlt : a * E.W + c < E.nσ * E.W :=
    calc a * E.W + c < a * E.W + E.W := by omega
      _ = (a + 1) * E.W := by ring
      _ ≤ E.nσ * E.W := Nat.mul_le_mul_right _ ha
  have h1 : (a * E.W + c) / E.W = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ E.W_pos, Nat.div_eq_of_lt hc, zero_add]
  have h2 : (a * E.W + c) % E.W = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp [tbl2, hlt, h1, h2]
def pcOf : Option Λ → ℕ
  | some l => E.start l
  | none => E.L.length
def instrOf (p : ℕ) : TM2.Stmt Γ Λ σ → Instr
  | .push k _ _ => .push (E.numK k) (E.tbl1 fun a => 4 + (a + E.nσ * p)) (p + 1)
  | .peek k f _ =>
    .peek (E.numK k) (E.tbl2 fun a c => E.num (f (E.σof a) (E.arg k c))) E.W (p + 1)
  | .pop k f _ =>
    .pop (E.numK k) (E.tbl2 fun a c => E.num (f (E.σof a) (E.arg k c))) E.W (p + 1)
  | .load f _ => .load (E.tbl1 fun a => E.num (f (E.σof a))) (p + 1)
  | .branch f q₁ _ =>
    .branch (E.tbl1 fun a => if f (E.σof a) then 1 else 0) (p + 1) (p + 1 + (subs q₁).length)
  | .goto f => .goto (E.tbl1 fun a => E.start (f (E.σof a)))
  | .halt => .branch [] E.L.length E.L.length
def finTbl : List ℕ :=
  E.tbl2 fun _ c => match E.arg E.k₁ c with
    | some y => E.outBit y
    | none => 0
def P : List Instr :=
  E.L.mapIdx E.instrOf ++
    [.pop (E.numK E.k₁) E.finTbl E.W (E.L.length + 1),
     .push (E.numK E.k₁) [0, 1] (E.L.length + 2),
     .halt]
theorem step_at {p : ℕ} {q : TM2.Stmt Γ Λ σ} (h : E.L[p]? = some q) (a : ℕ)
    (T : List (List ℕ)) : step E.P ⟨some p, a, T⟩ = exec (E.instrOf p q) a T := by
  have hp : p < E.L.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have : E.P[p]? = some (E.instrOf p q) := by
    unfold P
    rw [List.getElem?_append_left (by simpa using hp), List.getElem?_mapIdx, h]
    rfl
  simp [step, this]
theorem step_fin (i : ℕ) (I : Instr)
    (h : [Instr.pop (E.numK E.k₁) E.finTbl E.W (E.L.length + 1),
      Instr.push (E.numK E.k₁) [0, 1] (E.L.length + 2), Instr.halt][i]? = some I)
    (a : ℕ) (T : List (List ℕ)) : step E.P ⟨some (E.L.length + i), a, T⟩ = exec I a T := by
  have : E.P[E.L.length + i]? = some I := by
    unfold P
    rw [List.getElem?_append_right (by simp)]
    simpa using h
  simp [step, this]
def StkRel (T : List (List ℕ)) (S : ∀ k, List (Γ k)) : Prop :=
  T.length = E.nK ∧
    ∀ k, List.Forall₂ (fun s y => E.decode k s = some y) (T.getD (E.numK k) []) (S k)
variable {E}
theorem StkRel.set {T : List (List ℕ)} {S : ∀ k, List (Γ k)} (h : E.StkRel T S) (k : K)
    {ns : List ℕ} {ys : List (Γ k)}
    (h2 : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    E.StkRel (T.set (E.numK k) ns) (Function.update S k ys) := by
  refine ⟨by simp [h.1], fun k' => ?_⟩
  by_cases hk : k' = k
  · subst hk
    have hlt : E.numK k' < T.length := by rw [h.1]; exact E.numK_lt k'
    simpa [List.getD_eq_getElem?_getD, hlt] using h2
  · have hne : E.numK k ≠ E.numK k' := fun e => hk (E.numK_inj e).symm
    rw [Function.update_of_ne hk]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne] using h.2 k'
theorem StkRel.init (k : K) {ns : List ℕ} {ys : List (Γ k)}
    (h2 : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    E.StkRel ((List.replicate E.nK []).set (E.numK k) ns)
      (Function.update (fun _ => []) k ys) := by
  refine StkRel.set ⟨by simp, fun k' => ?_⟩ k h2
  simp [List.getD_eq_getElem?_getD, E.numK_lt k']
variable (E)
theorem sim_stmt (q : TM2.Stmt Γ Λ σ) : ∀ (p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (T : List (List ℕ)), Placed E.L p q → E.StkRel T S →
    ∃ t ≤ (subs q).length, ∃ T', (step E.P)^[t] ⟨some p, E.num v, T⟩ =
        ⟨some (E.pcOf (TM2.stepAux q v S).l), E.num (TM2.stepAux q v S).var, T'⟩ ∧
      E.StkRel T' (TM2.stepAux q v S).stk := by
  induction q with
  | push k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    have hd := E.decode_push hp.get (E.num_lt v)
    rw [E.σof_num] at hd
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) v (Function.update S k (f v :: S k)) _
      (hp.sub [] [] (by simp [subs])) (hr.set k (List.Forall₂.cons hd (hr.2 k)))
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v)] using h
  | peek k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨htop, harg⟩ := E.top_spec (hr.2 k)
    rw [List.getD_eq_getElem?_getD] at htop harg
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (f v (S k).head?) S T
      (hp.sub [] [] (by simp [subs])) hr
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl2_get _ (E.num_lt v) htop, harg, E.σof_num] using h
  | pop k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨htop, harg⟩ := E.top_spec (hr.2 k)
    rw [List.getD_eq_getElem?_getD] at htop harg
    have htail : List.Forall₂ (fun s y => E.decode k s = some y)
        (T.getD (E.numK k) []).tail (S k).tail := by
      exact forall₂_tail (hr.2 k)
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (f v (S k).head?) (Function.update S k (S k).tail) _
      (hp.sub [] [] (by simp [subs])) (hr.set k htail)
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl2_get _ (E.num_lt v) htop, harg, E.σof_num] using h
  | load a q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (a v) S T (hp.sub [] [] (by simp [subs])) hr
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num] using h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    cases hf : f v
    · obtain ⟨t, ht, T', h, hr'⟩ := ih₂ (p + 1 + (subs q₁).length) v S T
        (hp.sub (subs q₁) [] (by simp [subs])) hr
      refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa [hf] using hr'⟩
      rw [Function.iterate_succ_apply, hs]
      simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, hf] using h
    · obtain ⟨t, ht, T', h, hr'⟩ := ih₁ (p + 1) v S T
        (hp.sub [] (subs q₂) (by simp [subs])) hr
      refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa [hf] using hr'⟩
      rw [Function.iterate_succ_apply, hs]
      simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, hf] using h
  | goto f =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    refine ⟨1, by simp [subs], T, ?_, by simpa using hr⟩
    rw [Function.iterate_one, hs]
    simp [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, pcOf]
  | halt =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    refine ⟨1, by simp [subs], T, ?_, by simpa using hr⟩
    rw [Function.iterate_one, hs]
    simp [instrOf, exec, pcOf]
def Rel (c : TM2.Cfg Γ Λ σ) (X : Cfg) : Prop :=
  X.pc = some (E.pcOf c.l) ∧ X.state = E.num c.var ∧ E.StkRel X.stk c.stk
theorem iterate_bind_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih
theorem sim_run : ∀ (n : ℕ) (c c' : TM2.Cfg Γ Λ σ) (X : Cfg),
    (flip bind (TM2.step E.M))^[n] (some c) = some c' → E.Rel c X →
    ∃ t ≤ E.L.length * n, E.Rel c' ((step E.P)^[t] X) := by
  intro n
  induction n with
  | zero =>
    intro c c' X h hr
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h
    exact ⟨0, by simp, hr⟩
  | succ n ih =>
    intro c c' X h hr
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    obtain ⟨pc, a, T⟩ := X
    obtain ⟨h1, h2, h3⟩ := hr
    simp only at h1 h2 h3
    subst h1 h2
    cases l with
    | none =>
      have : flip bind (TM2.step E.M) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
      rw [this, iterate_bind_none] at h
      cases h
    | some l =>
      have : flip bind (TM2.step E.M) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
          some (TM2.stepAux (E.M l) v S) := rfl
      rw [this] at h
      obtain ⟨t₁, ht₁, T', hs, hr'⟩ := E.sim_stmt (E.M l) (E.start l) v S T (E.placed_start l) h3
      have hle := (E.placed_start l).le
      obtain ⟨t₂, ht₂, hfin⟩ := ih _ c' ((step E.P)^[t₁] ⟨some (E.start l), E.num v, T⟩) h
        (by rw [hs]; exact ⟨rfl, rfl, hr'⟩)
      refine ⟨t₂ + t₁, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply]; exact hfin
theorem sim_fin (a : ℕ) (ha : a < E.nσ) (T : List (List ℕ)) (hT : T.length = E.nK) (s : ℕ)
    (y : Γ E.k₁) (hs : T.getD (E.numK E.k₁) [] = [s]) (hy : E.decode E.k₁ s = some y)
    (hb : E.outBit y ≤ 1) :
    ∃ T', (step E.P)^[3] ⟨some E.L.length, a, T⟩ = ⟨none, E.outBit y, T'⟩ ∧
      T'.getD (E.numK E.k₁) [] = [E.outBit y] := by
  have hlt : E.numK E.k₁ < T.length := by rw [hT]; exact E.numK_lt _
  have e1 := E.step_fin 0 _ rfl a T
  have e2 := E.step_fin 1 _ rfl
  have e3 := E.step_fin 2 _ rfl
  have hget : E.finTbl.getD (a * E.W + (s + 1)) 0 = E.outBit y := by
    unfold finTbl
    rw [List.getD_eq_getElem?_getD, E.tbl2_get _ ha (E.decode_lt hy)]
    simp [arg, hy]
  have hpush : [0, 1].getD (E.outBit y) 0 = E.outBit y := by
    generalize E.outBit y = c at hb
    interval_cases c <;> rfl
  refine ⟨(T.set (E.numK E.k₁) []).set (E.numK E.k₁) [E.outBit y], ?_, ?_⟩
  · simp only [Function.iterate_succ_apply, Function.iterate_zero, id, Nat.add_zero] at e1 ⊢
    rw [e1]
    simp only [exec, hs, topIndex, hget, List.tail_cons]
    rw [e2]
    simp only [exec, hpush]
    rw [e3]
    simp [exec, List.getD_eq_getElem?_getD, hlt]
  · simp [List.getD_eq_getElem?_getD, hlt]
end Env
section Compile
variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)
noncomputable def σEquiv : tm.σ ≃ Fin (@Fintype.card tm.σ tm.σFin) :=
  @Fintype.equivFin tm.σ tm.σFin
noncomputable def kEquiv : tm.K ≃ Fin (@Fintype.card tm.K tm.kFin) :=
  @Fintype.equivFin tm.K tm.kFin
noncomputable def flatList : List (TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  ((@Finset.univ tm.Λ tm.ΛFin).toList.map fun l => subs (tm.m l)).flatten
theorem flatList_placed (l : tm.Λ) : ∃ p, Placed (flatList tm) p (tm.m l) :=
  exists_placed tm.m _ l (by simp)
noncomputable def envOf : Env tm.K tm.Γ tm.Λ tm.σ where
  M := tm.m
  nσ := @Fintype.card tm.σ tm.σFin
  nσ_pos := @Fintype.card_pos tm.σ tm.σFin ⟨tm.initialState⟩
  num v := (σEquiv tm v).val
  σof n := if h : n < @Fintype.card tm.σ tm.σFin then (σEquiv tm).symm ⟨n, h⟩ else tm.initialState
  σof_num v := by simp
  num_lt v := (σEquiv tm v).isLt
  nK := @Fintype.card tm.K tm.kFin
  numK k := (kEquiv tm k).val
  numK_lt k := (kEquiv tm k).isLt
  numK_inj := fun a b h => (kEquiv tm).injective (Fin.ext h)
  L := flatList tm
  start l := Classical.choose (flatList_placed tm l)
  placed_start l := Classical.choose_spec (flatList_placed tm l)
  k₀ := tm.k₀
  inSym n := eIn.symm (symOut n)
  k₁ := tm.k₁
  outBit y := bitCode (eOut y)
theorem compile :
    ∃ (c : Code) (d : ℕ), ∀ (l : List (Bool ⊕ Bool)) (b : Bool) (n : ℕ),
      (flip bind (Turing.TM2.step tm.m))^[n] (some (Turing.initList tm (l.map eIn.invFun))) =
          some (Turing.haltList tm [eOut.invFun b]) →
      c.outputsWithin (l.map symIn) (d * n + d) [bitCode b] := by
  let E := envOf tm eIn eOut
  refine ⟨⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩,
    E.L.length + 3, fun l b n hrun => ?_⟩
  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y) (l.map symIn)
      (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have := E.decode_in (symIn_lt x)
    simpa [E, envOf, symOut_symIn] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map symIn)⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hpc, hst, hsr⟩ := E.sim_run n _ _ _ hrun hrel
  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s, hs, hy⟩ : ∃ s, T.getD (E.numK tm.k₁) [] = [s] ∧
      E.decode tm.k₁ s = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOf]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin
  rw [hbit] at hT'
  refine Code.outputsWithin_mono _ _ (t := 3 + t) ?_ _ ?_
  · have : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold Code.outputsWithin Code.run Code.init
    simp only
    rw [hfin]
    exact ⟨rfl, hT'⟩
end Compile
end Lib.Universal
end
section
namespace Lib.Universal
def bflag (b : Bool) : List Bool := if b then [true] else []
@[simp] theorem un_zero : un 0 = [] := rfl
@[simp] theorem un_length (n : ℕ) : (un n).length = n := List.length_replicate
theorem un_succ (n : ℕ) : un (n + 1) = true :: un n := rfl
theorem un_inj {a b : ℕ} (h : un a = un b) : a = b := by
  have := congrArg List.length h
  simpa [un] using this
def hd (s : List Bool) : List Bool := s.takeWhile id
def dropN (s : List Bool) : List Bool := (s.dropWhile id).tail
def sel (f a b : List Bool) : List Bool := if f = [] then a else b
def mulU (u v : List Bool) : List Bool := un (u.length * v.length)
def spread (s : List Bool) : List Bool := s.flatMap fun b => if b then [true, false] else [false]
def blank (s : List Bool) : List Bool := s.map fun _ => false
theorem sel_append_left (f p a b : List Bool) : sel f (p ++ a) (p ++ b) = p ++ sel f a b := by
  unfold sel; split_ifs <;> rfl
theorem hd_length (s : List Bool) : (hd s).length ≤ s.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix id)
theorem dropN_length (s : List Bool) : (dropN s).length ≤ s.length := by
  have h1 := List.IsSuffix.length_le (List.dropWhile_suffix (p := id) (l := s))
  simp only [dropN, List.length_tail]
  omega
theorem iter_length (g : List Bool → List Bool) (hg : ∀ s, (g s).length ≤ s.length) (k : ℕ) :
    ∀ s, (g^[k] s).length ≤ s.length := by
  induction k with
  | zero => intro s; exact le_rfl
  | succ k ih => intro s; rw [Function.iterate_succ_apply]; exact (ih _).trans (hg s)
theorem sel_length (f a b : List Bool) (N : ℕ) (ha : a.length ≤ N) (hb : b.length ≤ N) :
    (sel f a b).length ≤ N := by
  unfold sel; split_ifs <;> assumption
theorem unpairB_length (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have h := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := s))
  simp only [List.length_append] at h
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  omega
theorem pairB_length (a b : List Bool) : (pairB a b).length = 2 * a.length + b.length + 1 := by
  simp [pairB]; omega
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h
private theorem fm_elim {A B C : Type} (φl : A → Option C) (φr : B → Option C) (x : List A)
    (w : List B) :
    (x.map Sum.inl ++ w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl ++ w.filterMap φr := by
  have h1 : ∀ x : List A, (x.map Sum.inl).filterMap (Sum.elim φl φr) = x.filterMap φl := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  have h2 : ∀ w : List B, (w.map Sum.inr).filterMap (Sum.elim φl φr) = w.filterMap φr := by
    intro w; induction w with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  rw [List.filterMap_append, h1, h2]
private theorem fm_some {A C : Type} (g : A → C) (l : List A) :
    l.filterMap (fun a => some (g a)) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
private theorem fm_none {A C : Type} (l : List A) :
    l.filterMap (fun _ : A => (none : Option C)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp
theorem cpt_pairB :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  have hA : ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (p.1, p.1 ++ p.2)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun b : Bool => some (Sum.inl b)) (fun _ : Bool => none))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun b : Bool => some (Sum.inr b))) ?_
    rintro ⟨x, w⟩
    simp only [encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_some, fm_none]
    simp
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a : List Bool => a.map (fun _ => true) ++ [false]) := by
    refine fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true))
      (fun _ => some false) () ?_
    intro a
    induction a with
    | nil => rfl
    | cons b l ih =>
      simp only [fstRun, List.map_cons, List.cons_append, Option.toList_some] at ih ⊢
      rw [← ih]; rfl
  refine cpt_congr (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
  rintro ⟨x, w⟩
  simp [pairB, un]
theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
  obtain ⟨c⟩ := constList_polyTime []
  have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
  refine cpt_congr (cpt_comp cpt_swap hI) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp [Function.iterate_succ_apply']
theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
  have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => if x = [] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
  refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp
theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf : ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun a => if f a then [true] else []) := by
  have h : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => if b then [true] else []) := by
    refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h
private def encT (u : List Bool) : List Bool := u.flatMap (fun b => [true, b])
private def encF (v : List Bool) : List Bool := v.flatMap (fun b => [false, b])
private def twD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)
private theorem twD_run (l : List Bool) :
    fstRun twD (fun _ => none) false l = [] ∧
      fstRun twD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, twD, ih.1, ih.2]
private def e0D : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, none, none)
  | false, false => (true, none, none)
  | true, b => (true, some false, some b)
private theorem e0D_run_true (l : List Bool) :
    fstRun2 e0D (fun _ => none) true l = encF l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun2, e0D, encF, ih]
private theorem e0D_run_false (l : List Bool) :
    fstRun2 e0D (fun _ => none) false l = encF (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, e0D, ih, e0D_run_true]
private def mkD : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d, false), t => ((d || !t, true), some (t || !d))
  | (d, true), b => ((d, false), some b)
private def mk (l : List Bool) : List Bool := fstRun mkD (fun _ => none) (false, false) l
private theorem mkD_length (q : Bool × Bool) (l : List Bool) :
    (fstRun mkD (fun _ => none) q l).length = l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons b l ih => obtain ⟨d, ph⟩ := q; cases ph <;> simp [fstRun, mkD, ih]
private theorem mkD_done (v : List Bool) :
    fstRun mkD (fun _ => none) (true, false) (encF v) = encF v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, mkD, encF] at ih ⊢; exact ih
private theorem mkD_marked (u r : List Bool) :
    fstRun mkD (fun _ => none) (false, false) (encT u ++ r) =
      encT u ++ fstRun mkD (fun _ => none) (false, false) r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, mkD, encT] at ih ⊢; exact ih
private theorem mk_nil (u : List Bool) : mk (encT u ++ encF []) = encT u ++ encF [] := by
  unfold mk; rw [mkD_marked]; rfl
private theorem mk_cons (u : List Bool) (b : Bool) (v : List Bool) :
    mk (encT u ++ encF (b :: v)) = encT (u ++ [b]) ++ encF v := by
  unfold mk
  rw [mkD_marked]
  have h : fstRun mkD (fun _ => none) (false, false) (encF (b :: v)) =
      true :: b :: encF v := by
    have h' := mkD_done v
    simp [fstRun, mkD, encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]
private theorem mk_iter (k : ℕ) : ∀ u t : List Bool,
    mk^[k] (encT u ++ encF t) = encT (u ++ t.take k) ++ encF (t.drop k) := by
  induction k with
  | zero => intro u t; simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil => rw [mk_nil, ih]; simp
    | cons b t => rw [mk_cons, ih]; simp
private def dcD : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, t => (some t, none)
  | some t, b => (none, some (if t then Sum.inl b else Sum.inr b))
private theorem dcD_F (v : List Bool) :
    fstRun dcD (fun _ => none) none (encF v) = v.map Sum.inr := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, dcD, encF] at ih ⊢; exact ih
private theorem dcD_T (u r : List Bool) :
    fstRun dcD (fun _ => none) none (encT u ++ r) =
      u.map Sum.inl ++ fstRun dcD (fun _ => none) none r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, dcD, encT] at ih ⊢; exact ih
private def rawDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)
private theorem rawDec_tagged (u v : List Bool) :
    rawDec (u.map Sum.inl ++ v.map Sum.inr) = (u, v) := by
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [rawDec, List.filterMap_append, h1, h2, h3, h4, List.append_nil, List.nil_append]
theorem cpt_unpairB :
    ComputableInPolyTime (fun x : List Bool => x) encodePair unpairB := by
  have hTw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _ => none) true (fun s => (twD_run s).2.symm)
  have hE0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _ => none) false (fun s => (e0D_run_false s).symm)
  have hMk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk :=
    fst_polyTime _ _ _ mkD (fun _ => none) (false, false) (fun _ => rfl)
  obtain ⟨cMk⟩ := hMk
  have hIt := Iter.iter_polyTime mk cMk 0 (fun y => by simp [mk, mkD_length])
  have hDc : ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l)
      (fun l : List Bool => fstRun dcD (fun _ => none) none l) :=
    fst_polyTime _ _ _ dcD (fun _ => none) none (fun _ => rfl)
  have hRaw : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair rawDec := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
      (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec, encodePair, List.map_filterMap]
  refine cpt_congr (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h := mk_iter (s.takeWhile id).length [] (s.dropWhile id).tail
  have e : encT [] ++ encF (s.dropWhile id).tail = encF (s.dropWhile id).tail := rfl
  rw [e] at h
  simp only [h, List.nil_append]
  rw [dcD_T, dcD_F, rawDec_tagged]
  rfl
theorem cpt_iterB (g : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y, m (g y) ≤ m y) (hgl : ∀ y, (g y).length ≤ y.length + m y)
    (ha : ∀ y, m y ≤ a * y.length + a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => g^[(unpairB s).2.length] (unpairB s).1) := by
  obtain ⟨c⟩ := hg
  exact cpt_comp cpt_unpairB (Iter.iter_polyTime_measure g c m a hm hgl ha)
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h
private def hdD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)
private theorem hdD_run (l : List Bool) :
    fstRun hdD (fun _ => none) false l = [] ∧
      fstRun hdD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, hdD, ih.1, ih.2]
theorem cpt_hd :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) hd :=
  fst_polyTime _ _ _ hdD (fun _ => none) true (fun s => (hdD_run s).2.symm)
private def dnD : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, none)
  | true, b => (true, some b)
private theorem dnD_true (l : List Bool) : fstRun dnD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, dnD, ih]
private theorem dnD_false (l : List Bool) :
    fstRun dnD (fun _ => none) false l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, dnD, ih, dnD_true]
theorem cpt_dropN :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropN :=
  fst_polyTime _ _ _ dnD (fun _ => none) false (fun s => (dnD_false s).symm)
private def tlD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, b => (true, some b)
private theorem tlD_true (l : List Bool) : fstRun tlD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tlD, ih]
private theorem tlD_false (l : List Bool) : fstRun tlD (fun _ => none) false l = l.tail := by
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, tlD, tlD_true]
theorem cpt_tail :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.tail) :=
  fst_polyTime _ _ _ tlD (fun _ => none) false (fun s => (tlD_false s).symm)
private theorem blank_run (l : List Bool) :
    fstRun (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) () l = blank l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, blank] at ih ⊢; exact ih
theorem cpt_blank :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) blank :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) ()
    (fun s => (blank_run s).symm)
private def spD : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, some false)
  | _, false => ((), some false, none)
private theorem spD_run (l : List Bool) : fstRun2 spD (fun _ => none) () l = spread l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, spD, spread] at ih ⊢ <;> exact ih
theorem cpt_spread :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) spread :=
  fst2_polyTime _ _ _ spD (fun _ => none) () (fun s => (spD_run s).symm)
theorem cpt_const (l : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => l) :=
  constList_polyTime l
theorem cpt_mulU :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => mulU p.1 p.2) :=
  cptc mul_polyTime (fun _ => rfl)
theorem cpt_unpairB1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) :=
  cptc (cpt_comp cpt_unpairB cpt_fst) (fun _ => rfl)
theorem cpt_unpairB2 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) :=
  cptc (cpt_comp cpt_unpairB cpt_snd) (fun _ => rfl)
theorem cpt_app2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => u s ++ v s) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ => rfl)
theorem cpt_pairB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ => rfl)
theorem cpt_mulU2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_mulU) (fun _ => rfl)
theorem cpt_sel {f a b : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => sel (f s) (a s) (b s)) := by
  have h1 := cpt_comp (cpt_pair hf ha) cpt_ifEmpty
  have h2 := cpt_comp (cpt_pair hf hb) cpt_ifNonempty
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h : f s = [] <;> simp [sel, h]
theorem cpt_iterLen {g cnt arg : List Bool → List Bool}
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (hgl : ∀ s, (g s).length ≤ s.length)
    (hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt)
    (harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y => by simpa using hgl y)
  exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptE_mini {f f' : List Bool → List Bool} (h : Lib.CPTs f) (e : ∀ a, f a = f' a) : Lib.CPTs f' := by
  obtain rfl : f = f' := funext e; exact h
theorem cpt_hd1 {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (fun y => hd (f y)) :=
  cpt_comp hf cpt_hd
theorem cpt_dropN1 {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (fun y => dropN (f y)) :=
  cpt_comp hf cpt_dropN
theorem cpt_tail1 {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (fun y => (f y).tail) :=
  cpt_comp hf cpt_tail
theorem cpt_unpairB1_1 {f : List Bool → List Bool} (hf : Lib.CPTs f) :
    Lib.CPTs (fun y => (unpairB (f y)).1) := cpt_comp (g := fun s => (unpairB s).1) hf cpt_unpairB1
theorem cpt_unpairB2_1 {f : List Bool → List Bool} (hf : Lib.CPTs f) :
    Lib.CPTs (fun y => (unpairB (f y)).2) := cpt_comp (g := fun s => (unpairB s).2) hf cpt_unpairB2
theorem cpt_cons1 (b : Bool) {f : List Bool → List Bool} (hf : Lib.CPTs f) :
    Lib.CPTs (fun y => b :: f y) :=
  cptE_mini (cpt_app2 (cpt_const [b]) hf) (fun _ => rfl)
theorem cpt_iterGrow {g cnt arg : List Bool → List Bool} (hg : Lib.CPTs g) (k : ℕ)
    (hgl : ∀ y, (g y).length ≤ y.length + k) (hcnt : Lib.CPTs cnt) (harg : Lib.CPTs arg) :
    Lib.CPTs (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  exact cptE_mini (cpt_comp (cpt_pair harg hcnt) (Iter.iter_polyTime g c k hgl)) (fun _ => rfl)
end Lib.Universal
end
section
namespace Lib.SearchHelpers
open PEqualNP.Search
theorem bits_injective : Function.Injective Nat.bits := by
  intro n m h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]
theorem digits_append_inj : ∀ (ds ds' : List Bool) (b b' : Bool) (r r' : List Bool),
    (ds.flatMap fun d => [true, d]) ++ (false :: b :: r) =
      (ds'.flatMap fun d => [true, d]) ++ (false :: b' :: r') →
    ds = ds' ∧ b = b' ∧ r = r' := by
  intro ds
  induction ds with
  | nil =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp_all
    | cons d ds' => simp at h
  | cons d ds ih =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp at h
    | cons d' ds' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hd, h⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih ds' b b' r r' h
      exact ⟨by rw [hd, h1], h2, h3⟩
theorem literal_append_inj (l l' : Literal) (r r' : List Bool)
    (h : encodeLiteral l ++ r = encodeLiteral l' ++ r') : l = l' ∧ r = r' := by
  obtain ⟨i, b⟩ := l
  obtain ⟨i', b'⟩ := l'
  simp only [encodeLiteral, List.cons_append, List.nil_append, List.append_assoc,
    List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := h
  obtain ⟨h1, -, h3⟩ := digits_append_inj _ _ true true r r' h
  exact ⟨by rw [bits_injective h1, hb], h3⟩
theorem encodeLiteral_head (l : Literal) (r : List Bool) :
    ∃ t, encodeLiteral l ++ r = true :: t := ⟨_, rfl⟩
theorem clause_append_inj : ∀ (c c' : Clause) (r r' : List Bool),
    encodeClause c ++ r = encodeClause c' ++ r' → c = c' ∧ r = r' := by
  intro c
  induction c with
  | nil =>
    intro c' r r' h
    cases c' with
    | nil => simpa [encodeClause] using h
    | cons l' c' =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l' (c'.flatMap encodeLiteral ++ [false, false] ++ r')
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
  | cons l c ih =>
    intro c' r r' h
    cases c' with
    | nil =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l (c.flatMap encodeLiteral ++ [false, false] ++ r)
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
    | cons l' c' =>
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := literal_append_inj l l' _ _ h
      have := ih c' r r' (by simpa [encodeClause, List.append_assoc] using h2)
      exact ⟨by rw [h1, this.1], this.2⟩
theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro φ
  induction φ with
  | nil =>
    intro φ' h
    cases φ' with
    | nil => rfl
    | cons c φ' => simp [encodeCNF, encodeClause] at h
  | cons c φ ih =>
    intro φ' h
    cases φ' with
    | nil => simp [encodeCNF, encodeClause] at h
    | cons c' φ' =>
      simp only [encodeCNF, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := clause_append_inj c c' _ _ h
      rw [h1, ih h2]
end Lib.SearchHelpers
end
section
namespace Lib.SearchHelpers.Tab
open Lib.Universal PEqualNP.Search
def uvar : List ℕ → ℕ
  | [] => 0
  | a :: r => 2 ^ a * (2 * uvar r + 1)
def vP (t q : ℕ) : ℕ := uvar [0, q, t]
def vQ (t v : ℕ) : ℕ := uvar [1, v, t]
def vC (t k j x : ℕ) : ℕ := uvar [2, k, x, j, t]
def imp (prem : List ℕ) (concl : ℕ) : Clause :=
  prem.map (fun x => (x, false)) ++ [(concl, true)]
def pcCode : Option ℕ → ℕ
  | none => 0
  | some n => n + 1
def instrAt (P : List Instr) : ℕ → Instr
  | 0 => .halt
  | q + 1 => P.getD q .halt
def nextCode (i : Instr) (v : ℕ) : ℕ :=
  match i with
  | .push _ _ next => next + 1
  | .pop _ _ _ next => next + 1
  | .peek _ _ _ next => next + 1
  | .load _ next => next + 1
  | .branch tbl next₁ next₂ => (if tbl.getD v 0 ≠ 0 then next₁ else next₂) + 1
  | .goto tbl => tbl.getD v 0 + 1
  | .halt => 0
def rdStack (i : Instr) : Option ℕ :=
  match i with
  | .pop k _ _ _ => some k
  | .peek k _ _ _ => some k
  | _ => none
def newState (i : Instr) (v a : ℕ) : ℕ :=
  match i with
  | .pop _ tbl w _ => tbl.getD (v * w + a) 0
  | .peek _ tbl w _ => tbl.getD (v * w + a) 0
  | .load tbl _ => tbl.getD v 0
  | _ => v
inductive Op
  | keep
  | push (tbl : List ℕ)
  | pop
  deriving DecidableEq, Repr
def stackOp (i : Instr) (k : ℕ) : Op :=
  match i with
  | .push k' tbl _ => if k' = k then .push tbl else .keep
  | .pop k' _ _ _ => if k' = k then .pop else .keep
  | _ => .keep
def reads (K B t : ℕ) (o : Option ℕ) : List (List ℕ × ℕ) :=
  match o with
  | none => [([], 0)]
  | some k =>
    if k < K then (List.range (B + 1)).map fun x => ([vC t k 0 x], x)
    else [([], 0)]
def pcClauses (B t q : ℕ) (i : Instr) : CNF :=
  (List.range B).map fun v => imp [vP t q, vQ t v] (vP (t + 1) (nextCode i v))
def stateClauses (K B t q : ℕ) (i : Instr) : CNF :=
  (List.range B).flatMap fun v =>
    (reads K B t (rdStack i)).map fun r =>
      imp (vP t q :: vQ t v :: r.1) (vQ (t + 1) (newState i v r.2))
def cellClauses (H B t q k : ℕ) (op : Op) : CNF :=
  match op with
  | .keep =>
    (List.range H).flatMap fun j =>
      (List.range (B + 1)).map fun x => imp [vP t q, vC t k j x] (vC (t + 1) k j x)
  | .push tbl =>
    ((List.range B).map fun v =>
      imp [vP t q, vQ t v] (vC (t + 1) k 0 (tbl.getD v 0 + 1)))
    ++ ((List.range (H - 1)).flatMap fun j =>
      (List.range (B + 1)).map fun x => imp [vP t q, vC t k j x] (vC (t + 1) k (j + 1) x))
  | .pop =>
    ((List.range (H - 1)).flatMap fun j =>
      (List.range (B + 1)).map fun x => imp [vP t q, vC t k (j + 1) x] (vC (t + 1) k j x))
    ++ [imp [vP t q] (vC (t + 1) k (H - 1) 0)]
def stepClauses (K H B : ℕ) (P : List Instr) (t : ℕ) : CNF :=
  (List.range (B + 1)).flatMap fun q =>
    pcClauses B t q (instrAt P q) ++ stateClauses K B t q (instrAt P q) ++
      (List.range K).flatMap fun k => cellClauses H B t q k (stackOp (instrAt P q) k)
def initClauses (c : Code) (zs : List ℕ) (m H : ℕ) : CNF :=
  [imp [] (vP 0 (c.pc₀ + 1)), imp [] (vQ 0 c.state₀)]
  ++ ((List.range c.nstk).flatMap fun k =>
    if k = c.kin then [] else (List.range H).map fun j => imp [] (vC 0 k j 0))
  ++ (if c.kin < c.nstk then
      ((List.range zs.length).map fun j => imp [] (vC 0 c.kin j (zs.getD j 0 + 1)))
      ++ ((List.range m).map fun j =>
        [(vC 0 c.kin (zs.length + j) 0, true), (vC 0 c.kin (zs.length + j) 3, true),
          (vC 0 c.kin (zs.length + j) 4, true)])
      ++ ((List.range (m - 1)).map fun j =>
        imp [vC 0 c.kin (zs.length + j) 0] (vC 0 c.kin (zs.length + (j + 1)) 0))
      ++ ((List.range H).map fun j => imp [] (vC 0 c.kin (zs.length + m + j) 0))
    else [])
def finalClauses (c : Code) (B T : ℕ) : CNF :=
  ((List.range B).map fun p => [(vP T (p + 1), false)])
  ++ (if c.kout < c.nstk then
      [[(vC T c.kout 0 0, false)]]
      ++ ((List.range B).flatMap fun x =>
        if x = 1 then [] else [[(vC T c.kout 0 (x + 1), false)]])
      ++ ((List.range B).map fun x => [(vC T c.kout 1 (x + 1), false)])
    else [[]])
def Instr.bd : Instr → ℕ
  | .push _ tbl next => tbl.sum + next
  | .pop _ tbl _ next => tbl.sum + next
  | .peek _ tbl _ next => tbl.sum + next
  | .load tbl next => tbl.sum + next
  | .branch _ next₁ next₂ => next₁ + next₂
  | .goto tbl => tbl.sum
  | .halt => 0
def bound (c : Code) : ℕ :=
  c.pc₀ + c.state₀ + (c.prog.map Instr.bd).sum + 4
def cellsOf (n m T : ℕ) : ℕ := n + m + T + 2
def tableau (c : Code) (zs : List ℕ) (m T : ℕ) : CNF :=
  initClauses c zs m (cellsOf zs.length m T)
  ++ ((List.range T).flatMap fun t =>
    stepClauses c.nstk (cellsOf zs.length m T) (bound c) c.prog t)
  ++ finalClauses c (bound c) T
end Lib.SearchHelpers.Tab
end
section
namespace Lib.SearchHelpers.Tab
open Lib.Universal PEqualNP.Search
namespace Snd
def cellVal (st : List ℕ) (j : ℕ) : ℕ :=
  match st[j]? with
  | none => 0
  | some s => s + 1
theorem cellVal_nil (j : ℕ) : cellVal [] j = 0 := by simp [cellVal]
theorem cellVal_cons_zero (a : ℕ) (st : List ℕ) : cellVal (a :: st) 0 = a + 1 := by
  simp [cellVal]
theorem cellVal_cons_succ (a : ℕ) (st : List ℕ) (j : ℕ) :
    cellVal (a :: st) (j + 1) = cellVal st j := by
  simp [cellVal]
theorem cellVal_tail (st : List ℕ) (j : ℕ) : cellVal st.tail j = cellVal st (j + 1) := by
  cases st <;> simp [cellVal]
theorem cellVal_of_le {st : List ℕ} {j : ℕ} (h : st.length ≤ j) : cellVal st j = 0 := by
  simp [cellVal, List.getElem?_eq_none h]
theorem cellVal_zero (st : List ℕ) : cellVal st 0 = topIndex st := by
  cases st <;> simp [cellVal, topIndex]
theorem cellVal_le {st : List ℕ} {B : ℕ} (h : ∀ s ∈ st, s < B) (j : ℕ) : cellVal st j ≤ B := by
  rcases hj : st[j]? with _ | s
  · simp [cellVal, hj]
  · simp only [cellVal, hj]
    exact Nat.succ_le_of_lt (h s (List.mem_of_getElem? hj))
theorem cellVal_append_left {zs r : List ℕ} {j : ℕ} (h : j < zs.length) :
    cellVal (zs ++ r) j = zs.getD j 0 + 1 := by
  simp [cellVal, List.getElem?_append_left h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
theorem cellVal_append_right (zs r : List ℕ) (j : ℕ) :
    cellVal (zs ++ r) (zs.length + j) = cellVal r j := by
  simp [cellVal, List.getElem?_append_right]
theorem getD_le_sum (tbl : List ℕ) (v : ℕ) : tbl.getD v 0 ≤ tbl.sum := by
  induction tbl generalizing v with
  | nil => simp
  | cons a r ih =>
    cases v with
    | zero => simp
    | succ v =>
      simp only [List.getD_cons_succ, List.sum_cons]
      exact (ih v).trans (Nat.le_add_left _ _)
theorem le_sum_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b r ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp only [List.sum_cons]
      exact (ih h).trans (Nat.le_add_left _ _)
theorem eval_all {σ : Assignment} {φ : CNF} (h : CNF.eval σ φ = true) {cl : Clause}
    (hc : cl ∈ φ) : Clause.eval σ cl = true := by
  unfold CNF.eval at h
  exact List.all_eq_true.1 h cl hc
theorem imp_true {σ : Assignment} {prem : List ℕ} {concl : ℕ}
    (h : Clause.eval σ (imp prem concl) = true) (hp : ∀ x ∈ prem, σ x = true) :
    σ concl = true := by
  unfold Clause.eval imp at h
  rcases List.any_eq_true.1 h with ⟨l, hl, he⟩
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have := hp x hx
    simp [Literal.eval, this] at he
  · rw [List.mem_singleton] at hl
    subst hl
    simpa [Literal.eval] using he
theorem imp0 {σ : Assignment} {a : ℕ} (h : Clause.eval σ (imp [] a) = true) : σ a = true :=
  imp_true h (by simp)
theorem imp1 {σ : Assignment} {x a : ℕ} (h : Clause.eval σ (imp [x] a) = true)
    (hx : σ x = true) : σ a = true :=
  imp_true h (by simpa using hx)
theorem imp2 {σ : Assignment} {x y a : ℕ} (h : Clause.eval σ (imp [x, y] a) = true)
    (hx : σ x = true) (hy : σ y = true) : σ a = true :=
  imp_true h (by simp [hx, hy])
theorem unit_false {σ : Assignment} {x : ℕ} (h : Clause.eval σ [(x, false)] = true) :
    σ x = false := by
  simpa [Clause.eval, Literal.eval] using h
theorem step_eq (P : List Instr) (cfg : Cfg) :
    step P cfg = exec (instrAt P (pcCode cfg.pc)) cfg.state cfg.stk := by
  rcases cfg with ⟨pc, v, S⟩
  cases pc with
  | none => rfl
  | some n =>
    simp only [step, pcCode, instrAt, List.getD_eq_getElem?_getD]
    cases P[n]? <;> rfl
theorem exec_pc (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    pcCode (exec i v S).pc = nextCode i v := by
  cases i <;> rfl
theorem exec_state (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).state =
      newState i v (match rdStack i with
        | none => 0
        | some k => topIndex (S.getD k [])) := by
  cases i <;> rfl
theorem exec_len (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).stk.length = S.length := by
  cases i <;> simp [exec]
theorem exec_stk (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ) (hk : k < S.length) :
    (exec i v S).stk.getD k [] =
      match stackOp i k with
      | .keep => S.getD k []
      | .push tbl => tbl.getD v 0 :: S.getD k []
      | .pop => (S.getD k []).tail := by
  cases i with
  | push k' tbl nx =>
    by_cases h : k' = k
    · subst h
      simp [exec, stackOp, List.getD_eq_getElem?_getD, hk]
    · simp [exec, stackOp, List.getD_eq_getElem?_getD, h, List.getElem?_set_ne h]
  | pop k' tbl w nx =>
    by_cases h : k' = k
    · subst h
      simp [exec, stackOp, List.getD_eq_getElem?_getD, hk]
    · simp [exec, stackOp, List.getD_eq_getElem?_getD, h, List.getElem?_set_ne h]
  | _ => rfl
theorem stackOp_push_bd {i : Instr} {k : ℕ} {tbl : List ℕ} (h : stackOp i k = .push tbl) :
    tbl.sum ≤ Instr.bd i := by
  cases i with
  | push k' tbl' nx =>
    simp only [stackOp] at h
    split_ifs at h
    cases h
    simp [Instr.bd]
  | pop k' tbl' w nx =>
    simp only [stackOp] at h
    split_ifs at h
  | _ => cases h
theorem nextCode_le {i : Instr} {B : ℕ} (h : Instr.bd i < B) (v : ℕ) : nextCode i v ≤ B := by
  cases i with
  | branch tbl a b =>
    simp only [nextCode, Instr.bd] at *
    split_ifs <;> omega
  | goto tbl =>
    simp only [nextCode, Instr.bd] at *
    have := getD_le_sum tbl v
    omega
  | halt => exact Nat.zero_le _
  | _ =>
    simp only [nextCode, Instr.bd] at *
    omega
theorem exec_state_lt {i : Instr} {B v : ℕ} (h : Instr.bd i < B) (hv : v < B)
    (S : List (List ℕ)) : (exec i v S).state < B := by
  cases i with
  | pop k tbl w nx =>
    simp only [exec, Instr.bd] at *
    have := getD_le_sum tbl (v * w + topIndex (S.getD k []))
    omega
  | peek k tbl w nx =>
    simp only [exec, Instr.bd] at *
    have := getD_le_sum tbl (v * w + topIndex (S.getD k []))
    omega
  | load tbl nx =>
    simp only [exec, Instr.bd] at *
    have := getD_le_sum tbl v
    omega
  | _ => exact hv
theorem instrAt_bd {P : List Instr} {B : ℕ} (hP : ∀ i ∈ P, Instr.bd i < B) (hB : 0 < B)
    (q : ℕ) : Instr.bd (instrAt P q) < B := by
  cases q with
  | zero => exact hB
  | succ n =>
    simp only [instrAt, List.getD_eq_getElem?_getD]
    rcases hn : P[n]? with _ | i
    · exact hB
    · exact hP i (List.mem_of_getElem? hn)
theorem mem_step {K H B t q : ℕ} {P : List Instr} {cl : Clause} (hq : q ≤ B)
    (h : cl ∈ pcClauses B t q (instrAt P q) ∨ cl ∈ stateClauses K B t q (instrAt P q) ∨
      ∃ k < K, cl ∈ cellClauses H B t q k (stackOp (instrAt P q) k)) :
    cl ∈ stepClauses K H B P t := by
  simp only [stepClauses, List.mem_flatMap, List.mem_range, List.mem_append]
  refine ⟨q, Nat.lt_succ_of_le hq, ?_⟩
  rcases h with h | h | ⟨k, hk, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨k, hk, h⟩
theorem keep_cl {σ : Assignment} {H B t q k : ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k .keep, Clause.eval σ cl = true) {j x : ℕ}
    (hj : j < H) (hx : x ≤ B) (hp : σ (vP t q) = true) (hc : σ (vC t k j x) = true) :
    σ (vC (t + 1) k j x) = true :=
  imp2 (hcl _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_map.2 ⟨x, List.mem_range.2 (Nat.lt_succ_of_le hx), rfl⟩⟩)) hp hc
theorem push_cl_top {σ : Assignment} {H B t q k : ℕ} {tbl : List ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k (.push tbl), Clause.eval σ cl = true) {v : ℕ}
    (hv : v < B) (hp : σ (vP t q) = true) (hq : σ (vQ t v) = true) :
    σ (vC (t + 1) k 0 (tbl.getD v 0 + 1)) = true :=
  imp2 (hcl _ (List.mem_append_left _ (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩))) hp hq
theorem push_cl_shift {σ : Assignment} {H B t q k : ℕ} {tbl : List ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k (.push tbl), Clause.eval σ cl = true) {j x : ℕ}
    (hj : j < H - 1) (hx : x ≤ B) (hp : σ (vP t q) = true) (hc : σ (vC t k j x) = true) :
    σ (vC (t + 1) k (j + 1) x) = true :=
  imp2 (hcl _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_map.2 ⟨x, List.mem_range.2 (Nat.lt_succ_of_le hx), rfl⟩⟩))) hp hc
theorem pop_cl_shift {σ : Assignment} {H B t q k : ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k .pop, Clause.eval σ cl = true) {j x : ℕ}
    (hj : j < H - 1) (hx : x ≤ B) (hp : σ (vP t q) = true)
    (hc : σ (vC t k (j + 1) x) = true) : σ (vC (t + 1) k j x) = true :=
  imp2 (hcl _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_map.2 ⟨x, List.mem_range.2 (Nat.lt_succ_of_le hx), rfl⟩⟩))) hp hc
theorem pop_cl_last {σ : Assignment} {H B t q k : ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k .pop, Clause.eval σ cl = true)
    (hp : σ (vP t q) = true) : σ (vC (t + 1) k (H - 1) 0) = true :=
  imp1 (hcl _ (List.mem_append_right _ (List.mem_singleton.2 rfl))) hp
structure Inv (σ : Assignment) (K H B h t : ℕ) (cfg : Cfg) : Prop where
  pc : σ (vP t (pcCode cfg.pc)) = true
  st : σ (vQ t cfg.state) = true
  cell : ∀ k < K, ∀ j < H, σ (vC t k j (cellVal (cfg.stk.getD k []) j)) = true
  len : cfg.stk.length = K
  pcB : pcCode cfg.pc ≤ B
  stB : cfg.state < B
  symB : ∀ k < K, ∀ s ∈ cfg.stk.getD k [], s < B
  ht : ∀ k < K, (cfg.stk.getD k []).length ≤ h
theorem reads_ok {σ : Assignment} {K H B t : ℕ} {S : List (List ℕ)} (hlen : S.length = K)
    (hcell : ∀ k < K, ∀ j < H, σ (vC t k j (cellVal (S.getD k []) j)) = true) (hH : 0 < H)
    (hsym : ∀ k < K, ∀ s ∈ S.getD k [], s < B) (o : Option ℕ) :
    ∃ r ∈ reads K B t o, (∀ x ∈ r.1, σ x = true) ∧
      r.2 = (match o with
        | none => 0
        | some k => topIndex (S.getD k [])) := by
  cases o with
  | none => exact ⟨([], 0), by simp [reads], by simp, rfl⟩
  | some k =>
    by_cases hk : k < K
    · refine ⟨([vC t k 0 (cellVal (S.getD k []) 0)], cellVal (S.getD k []) 0), ?_, ?_,
        cellVal_zero _⟩
      · simp only [reads, hk, ↓reduceIte]
        exact List.mem_map.2 ⟨_, List.mem_range.2
          (Nat.lt_succ_of_le (cellVal_le (hsym k hk) 0)), rfl⟩
      · intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact hcell k hk 0 hH
    · refine ⟨([], 0), by simp [reads, hk], by simp, ?_⟩
      have : S.getD k [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      show 0 = topIndex (S.getD k [])
      rw [this]
      rfl
theorem step_inv {σ : Assignment} {K H B h t : ℕ} {P : List Instr} {cfg : Cfg}
    (hI : Inv σ K H B h t cfg) (hH : h < H) (hP : ∀ i ∈ P, Instr.bd i < B)
    (hc : ∀ cl ∈ stepClauses K H B P t, Clause.eval σ cl = true) :
    Inv σ K H B (h + 1) (t + 1) (step P cfg) := by
  obtain ⟨hpc, hst, hcell, hlen, hpcB, hstB, hsymB, hht⟩ := hI
  rw [step_eq]
  have hbd : Instr.bd (instrAt P (pcCode cfg.pc)) < B :=
    instrAt_bd hP (Nat.lt_of_le_of_lt (Nat.zero_le _) hstB) _
  have hcl : ∀ k < K, ∀ cl ∈ cellClauses H B t (pcCode cfg.pc) k
      (stackOp (instrAt P (pcCode cfg.pc)) k), Clause.eval σ cl = true :=
    fun k hk cl hm => hc cl (mem_step hpcB (Or.inr (Or.inr ⟨k, hk, hm⟩)))
  have hstk := fun k (hk : k < K) =>
    exec_stk (instrAt P (pcCode cfg.pc)) cfg.state cfg.stk k (hlen ▸ hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_pc]
    exact imp2 (hc _ (mem_step hpcB (Or.inl
      (List.mem_map.2 ⟨cfg.state, List.mem_range.2 hstB, rfl⟩)))) hpc hst
  · rw [exec_state]
    obtain ⟨r, hr, hprem, hr2⟩ := reads_ok (σ := σ) (B := B) (t := t) hlen hcell
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hH) hsymB (rdStack (instrAt P (pcCode cfg.pc)))
    rw [← hr2]
    refine imp_true (hc _ (mem_step hpcB (Or.inr (Or.inl
      (List.mem_flatMap.2 ⟨cfg.state, List.mem_range.2 hstB,
        List.mem_map.2 ⟨r, hr, rfl⟩⟩))))) ?_
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hpc
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hst
    · exact hprem x hx
  · intro k hk j hj
    have hs := hstk k hk
    have hcl' := hcl k hk
    cases hop : stackOp (instrAt P (pcCode cfg.pc)) k with
    | keep =>
      rw [hop] at hs hcl'
      simp only at hs
      rw [hs]
      exact keep_cl hcl' hj (cellVal_le (hsymB k hk) j) hpc (hcell k hk j hj)
    | push tbl =>
      rw [hop] at hs hcl'
      simp only at hs
      rw [hs]
      cases j with
      | zero =>
        rw [cellVal_cons_zero]
        exact push_cl_top hcl' hstB hpc hst
      | succ j =>
        rw [cellVal_cons_succ]
        exact push_cl_shift hcl' (by omega) (cellVal_le (hsymB k hk) j) hpc
          (hcell k hk j (by omega))
    | pop =>
      rw [hop] at hs hcl'
      simp only at hs
      rw [hs, cellVal_tail]
      by_cases hj' : j < H - 1
      · exact pop_cl_shift hcl' hj' (cellVal_le (hsymB k hk) (j + 1)) hpc
          (hcell k hk (j + 1) (by omega))
      · have h0 : cellVal (cfg.stk.getD k []) (j + 1) = 0 :=
          cellVal_of_le (by have := hht k hk; omega)
        have hjH : j = H - 1 := by omega
        rw [h0, hjH]
        exact pop_cl_last hcl' hpc
  · exact (exec_len _ _ _).trans hlen
  · rw [exec_pc]
    exact nextCode_le hbd _
  · exact exec_state_lt hbd hstB _
  · intro k hk s hs'
    have hs := hstk k hk
    cases hop : stackOp (instrAt P (pcCode cfg.pc)) k with
    | keep =>
      rw [hop] at hs
      simp only at hs
      rw [hs] at hs'
      exact hsymB k hk s hs'
    | push tbl =>
      rw [hop] at hs
      simp only at hs
      rw [hs] at hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · have h1 := getD_le_sum tbl cfg.state
        have h2 := stackOp_push_bd hop
        omega
      · exact hsymB k hk s hs'
    | pop =>
      rw [hop] at hs
      simp only at hs
      rw [hs] at hs'
      exact hsymB k hk s (List.mem_of_mem_tail hs')
  · intro k hk
    have hs := hstk k hk
    have hl := hht k hk
    cases hop : stackOp (instrAt P (pcCode cfg.pc)) k with
    | keep =>
      rw [hop] at hs
      simp only at hs
      rw [hs]
      omega
    | push tbl =>
      rw [hop] at hs
      simp only at hs
      rw [hs, List.length_cons]
      omega
    | pop =>
      rw [hop] at hs
      simp only at hs
      rw [hs, List.length_tail]
      omega
theorem wit_exists (f : ℕ → ℕ → Bool) (m : ℕ)
    (h1 : ∀ j < m, f j 0 = true ∨ f j 3 = true ∨ f j 4 = true)
    (h2 : ∀ j, j + 1 < m → f j 0 = true → f (j + 1) 0 = true) :
    ∃ w : List Bool, w.length ≤ m ∧
      ∀ j < m, f j (cellVal (w.map (fun b => cond b 3 2)) j) = true := by
  induction m generalizing f with
  | zero => exact ⟨[], Nat.le_refl _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    by_cases h0 : f 0 0 = true
    · refine ⟨[], Nat.zero_le _, fun j hj => ?_⟩
      simp only [List.map_nil, cellVal_nil]
      induction j with
      | zero => exact h0
      | succ j ihj => exact h2 j hj (ihj (by omega))
    · obtain ⟨w, hw, hwj⟩ := ih (fun j => f (j + 1)) (fun j hj => h1 (j + 1) (by omega))
        (fun j hj => h2 (j + 1) (by omega))
      rcases h1 0 (Nat.succ_pos _) with h | h | h
      · exact absurd h h0
      · refine ⟨false :: w, by simpa using hw, fun j hj => ?_⟩
        cases j with
        | zero => simpa [cellVal_cons_zero] using h
        | succ j => simpa [cellVal_cons_succ] using hwj j (by omega)
      · refine ⟨true :: w, by simpa using hw, fun j hj => ?_⟩
        cases j with
        | zero => simpa [cellVal_cons_zero] using h
        | succ j => simpa [cellVal_cons_succ] using hwj j (by omega)
theorem wit {σ : Assignment} (c : Code) (zs : List ℕ) (m H : ℕ)
    (hinit : ∀ cl ∈ initClauses c zs m H, Clause.eval σ cl = true) :
    ∃ w : List Bool, w.length ≤ m ∧ (c.kin < c.nstk → ∀ j < m,
      σ (vC 0 c.kin (zs.length + j) (cellVal (w.map (fun b => cond b 3 2)) j)) = true) := by
  by_cases hk : c.kin < c.nstk
  · unfold initClauses at hinit
    simp only [hk, ↓reduceIte] at hinit
    have h1 : ∀ j < m, σ (vC 0 c.kin (zs.length + j) 0) = true ∨
        σ (vC 0 c.kin (zs.length + j) 3) = true ∨ σ (vC 0 c.kin (zs.length + j) 4) = true := by
      intro j hj
      have := hinit _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))))
      simpa [Clause.eval, Literal.eval] using this
    have h2 : ∀ j, j + 1 < m → σ (vC 0 c.kin (zs.length + j) 0) = true →
        σ (vC 0 c.kin (zs.length + (j + 1)) 0) = true := by
      intro j hj h0
      exact imp1 (hinit _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩))))) h0
    obtain ⟨w, hw, hj⟩ := wit_exists (fun j x => σ (vC 0 c.kin (zs.length + j) x)) m h1 h2
    exact ⟨w, hw, fun _ => hj⟩
  · exact ⟨[], Nat.zero_le _, fun h => absurd h hk⟩
theorem init_stk_kin (c : Code) (inp : List ℕ) (hk : c.kin < c.nstk) :
    (c.init inp).stk.getD c.kin [] = inp := by
  simp [Code.init, List.getD_eq_getElem?_getD, hk]
theorem init_stk_ne (c : Code) (inp : List ℕ) {k : ℕ} (hne : k ≠ c.kin) :
    (c.init inp).stk.getD k [] = [] := by
  simp only [Code.init]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), List.getElem?_replicate]
  split_ifs <;> rfl
theorem init_inv {σ : Assignment} (c : Code) (zs : List ℕ) (m H : ℕ) (w : List Bool)
    (hz : ∀ z ∈ zs, z < 4) (hw : w.length ≤ m)
    (hinit : ∀ cl ∈ initClauses c zs m H, Clause.eval σ cl = true)
    (hwit : c.kin < c.nstk → ∀ j < m,
      σ (vC 0 c.kin (zs.length + j) (cellVal (w.map (fun b => cond b 3 2)) j)) = true) :
    Inv σ c.nstk H (bound c) (zs.length + m) 0
      (c.init (zs ++ w.map (fun b => cond b 3 2))) := by
  unfold initClauses at hinit
  have hB : 4 ≤ bound c := by unfold bound; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact imp0 (hinit _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons.2 (Or.inl rfl)))))
  · exact imp0 (hinit _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))
  · intro k hk j hj
    by_cases hkin : k = c.kin
    · subst hkin
      simp only [hk, ↓reduceIte] at hinit
      rw [init_stk_kin c _ hk]
      rcases Nat.lt_or_ge j zs.length with h1 | h1
      · rw [cellVal_append_left h1]
        exact imp0 (hinit _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.2 ⟨j, List.mem_range.2 h1, rfl⟩))))))
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h1
        rw [cellVal_append_right]
        rcases Nat.lt_or_ge j' m with h2 | h2
        · exact hwit hk j' h2
        · obtain ⟨j'', rfl⟩ := Nat.exists_eq_add_of_le h2
          rw [cellVal_of_le (by rw [List.length_map]; omega)]
          have := imp0 (hinit _ (List.mem_append_right _ (List.mem_append_right _
            (List.mem_map.2 ⟨j'', List.mem_range.2 (by omega), rfl⟩))))
          rwa [Nat.add_assoc] at this
    · rw [init_stk_ne c _ hkin, cellVal_nil]
      exact imp0 (hinit _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by
          simp only [hkin, ↓reduceIte]
          exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩))))
  · simp [Code.init]
  · show c.pc₀ + 1 ≤ bound c
    unfold bound
    omega
  · show c.state₀ < bound c
    unfold bound
    omega
  · intro k hk s hs
    by_cases hkin : k = c.kin
    · subst hkin
      rw [init_stk_kin c _ hk] at hs
      rcases List.mem_append.1 hs with hs | hs
      · exact Nat.lt_of_lt_of_le (hz s hs) hB
      · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
        cases b <;> simp <;> omega
    · rw [init_stk_ne c _ hkin] at hs
      simp at hs
  · intro k hk
    by_cases hkin : k = c.kin
    · subst hkin
      rw [init_stk_kin c _ hk, List.length_append, List.length_map]
      omega
    · rw [init_stk_ne c _ hkin]
      exact Nat.zero_le _
theorem prog_bd (c : Code) : ∀ i ∈ c.prog, Instr.bd i < bound c := by
  intro i hi
  have := le_sum_of_mem (List.mem_map_of_mem (f := Instr.bd) hi)
  unfold bound
  omega
theorem final_out {σ : Assignment} {c : Code} {H B h T : ℕ} {cfg : Cfg}
    (hI : Inv σ c.nstk H B h T cfg) (hH : 2 ≤ H)
    (hf : ∀ cl ∈ finalClauses c B T, Clause.eval σ cl = true) :
    cfg.pc = none ∧ cfg.stk.getD c.kout [] = [1] := by
  unfold finalClauses at hf
  constructor
  · rcases hpc : cfg.pc with _ | n
    · rfl
    · have h1 := hI.pc
      have h2 := hI.pcB
      rw [hpc] at h1 h2
      have h3 := unit_false (hf _ (List.mem_append_left _
        (List.mem_map.2 ⟨n, List.mem_range.2 h2, rfl⟩)))
      rw [show pcCode (some n) = n + 1 from rfl, h3] at h1
      cases h1
  · by_cases hk : c.kout < c.nstk
    · simp only [hk, ↓reduceIte] at hf
      have h0 := hI.cell c.kout hk 0 (by omega)
      have h1 := hI.cell c.kout hk 1 (by omega)
      have hsym := hI.symB c.kout hk
      have hA : σ (vC T c.kout 0 0) = false :=
        unit_false (hf _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_singleton.2 rfl)))))
      have hBx : ∀ x < B, x ≠ 1 → σ (vC T c.kout 0 (x + 1)) = false := fun x hx hne =>
        unit_false (hf _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, List.mem_range.2 hx, by
            simp only [hne, ↓reduceIte]
            exact List.mem_singleton.2 rfl⟩)))))
      have hCx : ∀ x < B, σ (vC T c.kout 1 (x + 1)) = false := fun x hx =>
        unit_false (hf _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩))))
      rcases hO : cfg.stk.getD c.kout [] with _ | ⟨a, r⟩
      · rw [hO, cellVal_nil, hA] at h0
        cases h0
      · rw [hO] at h0 h1 hsym
        rw [cellVal_cons_zero] at h0
        have ha : a = 1 := by
          by_contra hne
          rw [hBx a (hsym a (by simp)) hne] at h0
          cases h0
        subst ha
        rcases r with _ | ⟨b, r'⟩
        · rfl
        · rw [cellVal_cons_succ, cellVal_cons_zero, hCx b (hsym b (by simp))] at h1
          cases h1
    · have := hf [] (List.mem_append_right _ (by
        simp only [hk, ↓reduceIte]
        exact List.mem_singleton.2 rfl))
      simp [Clause.eval] at this
end Snd
theorem accepts_of_sat (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4)
    (h : PEqualNP.Search.Satisfiable (tableau c zs m T)) :
    ∃ w : List Bool, w.length ≤ m ∧
      c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1] := by
  obtain ⟨σ, hσ⟩ := h
  have hall : ∀ cl ∈ tableau c zs m T, Clause.eval σ cl = true :=
    fun cl hcl => Snd.eval_all hσ hcl
  have hinit : ∀ cl ∈ initClauses c zs m (cellsOf zs.length m T), Clause.eval σ cl = true :=
    fun cl hcl => hall cl (List.mem_append_left _ (List.mem_append_left _ hcl))
  have hstep : ∀ t < T, ∀ cl ∈ stepClauses c.nstk (cellsOf zs.length m T) (bound c) c.prog t,
      Clause.eval σ cl = true :=
    fun t ht cl hcl => hall cl (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, hcl⟩)))
  have hfin : ∀ cl ∈ finalClauses c (bound c) T, Clause.eval σ cl = true :=
    fun cl hcl => hall cl (List.mem_append_right _ hcl)
  obtain ⟨w, hw, hwit⟩ := Snd.wit c zs m (cellsOf zs.length m T) hinit
  refine ⟨w, hw, ?_⟩
  have hrun : ∀ t ≤ T, Snd.Inv σ c.nstk (cellsOf zs.length m T) (bound c)
      (zs.length + m + t) t (c.run (zs ++ w.map (fun b => cond b 3 2)) t) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact Snd.init_inv c zs m _ w hz hw hinit hwit
    | succ t ih =>
      intro ht
      have hlt : zs.length + m + t < cellsOf zs.length m T := by
        show zs.length + m + t < zs.length + m + T + 2
        omega
      have := Snd.step_inv (ih (by omega)) hlt (Snd.prog_bd c) (hstep t (by omega))
      rw [Code.run, Function.iterate_succ_apply']
      exact this
  exact Snd.final_out (hrun T (Nat.le_refl _))
    (by show 2 ≤ zs.length + m + T + 2; omega) hfin
end Lib.SearchHelpers.Tab
end
section
namespace Lib.SearchHelpers.Tab
open Lib.Universal PEqualNP.Search
namespace Cpl
theorem pow_odd_inj (a : ℕ) :
    ∀ b u v : ℕ, 2 ^ a * (2 * u + 1) = 2 ^ b * (2 * v + 1) → a = b ∧ u = v := by
  induction a with
  | zero =>
    intro b u v h
    cases b with
    | zero =>
      rw [pow_zero, one_mul, one_mul] at h
      exact ⟨rfl, by omega⟩
    | succ b =>
      exfalso
      have e : 2 ^ (b + 1) * (2 * v + 1) = 2 * (2 ^ b * (2 * v + 1)) := by ring
      rw [e, pow_zero, one_mul] at h
      generalize 2 ^ b * (2 * v + 1) = Y at h
      omega
  | succ a ih =>
    intro b u v h
    cases b with
    | zero =>
      exfalso
      have e : 2 ^ (a + 1) * (2 * u + 1) = 2 * (2 ^ a * (2 * u + 1)) := by ring
      rw [e, pow_zero, one_mul] at h
      generalize 2 ^ a * (2 * u + 1) = Y at h
      omega
    | succ b =>
      have e1 : 2 ^ (a + 1) * (2 * u + 1) = 2 * (2 ^ a * (2 * u + 1)) := by ring
      have e2 : 2 ^ (b + 1) * (2 * v + 1) = 2 * (2 ^ b * (2 * v + 1)) := by ring
      rw [e1, e2] at h
      have h' := ih b u v (Nat.eq_of_mul_eq_mul_left (by norm_num) h)
      exact ⟨by rw [h'.1], h'.2⟩
theorem uvar_inj : ∀ l l' : List ℕ, uvar l = uvar l' → l = l'
  | [], [], _ => rfl
  | [], b :: s, h => by
    exfalso
    have hpos : 0 < 2 ^ b * (2 * uvar s + 1) := by positivity
    simp only [uvar] at h
    exact absurd h hpos.ne
  | a :: r, [], h => by
    exfalso
    have hpos : 0 < 2 ^ a * (2 * uvar r + 1) := by positivity
    simp only [uvar] at h
    exact absurd h hpos.ne'
  | a :: r, b :: s, h => by
    simp only [uvar] at h
    obtain ⟨h1, h2⟩ := pow_odd_inj a b _ _ h
    rw [h1, uvar_inj r s h2]
def cellOf (st : List ℕ) (j : ℕ) : ℕ := ((st[j]?).map (· + 1)).getD 0
theorem cellOf_zero (st : List ℕ) : cellOf st 0 = topIndex st := by
  cases st <;> simp [cellOf, topIndex]
theorem cellOf_cons_zero (a : ℕ) (st : List ℕ) : cellOf (a :: st) 0 = a + 1 := by
  simp [cellOf]
theorem cellOf_cons_succ (a : ℕ) (st : List ℕ) (j : ℕ) :
    cellOf (a :: st) (j + 1) = cellOf st j := by
  simp [cellOf]
theorem cellOf_tail (st : List ℕ) (j : ℕ) : cellOf st.tail j = cellOf st (j + 1) := by
  cases st <;> simp [cellOf]
theorem cellOf_eq_zero_iff (st : List ℕ) (j : ℕ) : cellOf st j = 0 ↔ st.length ≤ j := by
  by_cases hj : j < st.length
  · simp [cellOf, List.getElem?_eq_getElem hj]
    omega
  · have hj' : st.length ≤ j := by omega
    simp [cellOf, hj']
theorem cellOf_append_left (zs ws : List ℕ) (j : ℕ) (hj : j < zs.length) :
    cellOf (zs ++ ws) j = zs.getD j 0 + 1 := by
  simp [cellOf, List.getElem?_append_left hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]
theorem cellOf_append_right (zs ws : List ℕ) (j : ℕ) :
    cellOf (zs ++ ws) (zs.length + j) = cellOf ws j := by
  simp [cellOf, List.getElem?_append_right]
theorem cellOf_witness (w : List Bool) (j : ℕ) :
    cellOf (w.map fun b => cond b 3 2) j = 0 ∨ cellOf (w.map fun b => cond b 3 2) j = 3 ∨
      cellOf (w.map fun b => cond b 3 2) j = 4 := by
  unfold cellOf
  rw [List.getElem?_map]
  cases w[j]? with
  | none => simp
  | some b => cases b <;> simp
theorem getD_of_le (S : List (List ℕ)) (k : ℕ) (h : S.length ≤ k) : S.getD k [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem getD_set (S : List (List ℕ)) (k k' : ℕ) (x : List ℕ) :
    (S.set k x).getD k' [] = if k = k' ∧ k < S.length then x else S.getD k' [] := by
  by_cases hk : k = k'
  · subst hk
    by_cases hl : k < S.length
    · simp [List.getD_eq_getElem?_getD, hl]
    · have hl' : S.length ≤ k := by omega
      rw [ite_eq_right (by tauto), List.set_eq_of_length_le hl']
  · rw [ite_eq_right (by tauto)]
    simp [List.getD_eq_getElem?_getD, hk]
theorem getD_replicate (n k : ℕ) : (List.replicate n ([] : List ℕ)).getD k [] = [] := by
  by_cases hk : k < n
  · simp [List.getD_eq_getElem?_getD, hk]
  · exact getD_of_le _ _ (by simp; omega)
theorem step_eq (P : List Instr) (cfg : Cfg) :
    step P cfg = exec (instrAt P (pcCode cfg.pc)) cfg.state cfg.stk := by
  obtain ⟨pc, v, S⟩ := cfg
  cases pc with
  | none => simp [step, pcCode, instrAt, exec]
  | some n =>
    simp only [step, pcCode, instrAt, List.getD_eq_getElem?_getD]
    cases P[n]? with
    | none => simp [exec]
    | some i => simp
theorem run_zero (c : Code) (input : List ℕ) : c.run input 0 = c.init input := rfl
theorem run_succ (c : Code) (input : List ℕ) (t : ℕ) :
    c.run input (t + 1) = exec (instrAt c.prog (pcCode (c.run input t).pc))
      (c.run input t).state (c.run input t).stk := by
  rw [← step_eq]
  exact Function.iterate_succ_apply' _ _ _
theorem pcCode_exec (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    pcCode (exec i v S).pc = nextCode i v := by
  cases i <;> rfl
theorem state_exec (i : Instr) (v : ℕ) (S : List (List ℕ)) (a : ℕ)
    (h : ∀ k, rdStack i = some k → a = topIndex (S.getD k [])) :
    (exec i v S).state = newState i v a := by
  cases i <;> simp_all [exec, newState, rdStack]
theorem exec_len (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).stk.length = S.length := by
  cases i <;> simp [exec]
theorem stk_exec_keep (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ)
    (h : stackOp i k = .keep) : (exec i v S).stk.getD k [] = S.getD k [] := by
  cases i with
  | push k' tbl next =>
    have hk : k' ≠ k := by
      intro e
      simp [stackOp, e] at h
    simp [exec, hk]
  | pop k' tbl w next =>
    have hk : k' ≠ k := by
      intro e
      simp [stackOp, e] at h
    simp [exec, hk]
  | _ => rfl
theorem stk_exec_push (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ) (tbl : List ℕ)
    (hk : k < S.length) (h : stackOp i k = .push tbl) :
    (exec i v S).stk.getD k [] = tbl.getD v 0 :: S.getD k [] := by
  cases i with
  | push k' tbl' next =>
    by_cases e : k' = k
    · subst e
      simp only [stackOp, ite_true, Op.push.injEq] at h
      subst h
      simp [exec, hk]
    · simp [stackOp, e] at h
  | pop k' tbl' w next =>
    by_cases e : k' = k <;> simp [stackOp, e] at h
  | _ => simp [stackOp] at h
theorem stk_exec_pop (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ)
    (hk : k < S.length) (h : stackOp i k = .pop) :
    (exec i v S).stk.getD k [] = (S.getD k []).tail := by
  cases i with
  | push k' tbl' next =>
    by_cases e : k' = k <;> simp [stackOp, e] at h
  | pop k' tbl' w next =>
    by_cases e : k' = k
    · subst e
      simp [exec, hk]
    · simp [stackOp, e] at h
  | _ => simp [stackOp] at h
theorem exec_height (i : Instr) (v : ℕ) (S : List (List ℕ)) (n : ℕ)
    (h : ∀ k, (S.getD k []).length ≤ n) (k : ℕ) :
    ((exec i v S).stk.getD k []).length ≤ n + 1 := by
  have hk := h k
  cases i with
  | push k' tbl next =>
    have hk' := h k'
    simp only [exec]
    rw [getD_set]
    split_ifs <;> (try simp only [List.length_cons]) <;> omega
  | pop k' tbl w next =>
    have hk' := h k'
    simp only [exec]
    rw [getD_set]
    split_ifs <;> (try simp only [List.length_tail]) <;> omega
  | _ => exact Nat.le_succ_of_le hk
theorem len_run (c : Code) (input : List ℕ) (t : ℕ) : (c.run input t).stk.length = c.nstk := by
  induction t with
  | zero => simp [run_zero, Code.init]
  | succ t ih => rw [run_succ, exec_len, ih]
theorem stk_init (c : Code) (input : List ℕ) (k : ℕ) :
    (c.run input 0).stk.getD k [] = if c.kin = k ∧ c.kin < c.nstk then input else [] := by
  rw [run_zero]
  simp only [Code.init]
  rw [getD_set, getD_replicate, List.length_replicate]
theorem height (c : Code) (input : List ℕ) (t k : ℕ) :
    ((c.run input t).stk.getD k []).length ≤ input.length + t := by
  induction t generalizing k with
  | zero =>
    rw [stk_init]
    split_ifs <;> simp
  | succ t ih =>
    rw [run_succ]
    exact exec_height _ _ _ _ ih k
def Holds (c : Code) (input : List ℕ) (x : ℕ) : Prop :=
  ∃ t, x = vP t (pcCode (c.run input t).pc) ∨ x = vQ t (c.run input t).state ∨
    ∃ k j, x = vC t k j (cellOf ((c.run input t).stk.getD k []) j)
noncomputable def asg (c : Code) (input : List ℕ) : Assignment :=
  fun x => @decide (Holds c input x) (Classical.propDecidable _)
theorem asg_iff (c : Code) (input : List ℕ) (x : ℕ) : asg c input x = true ↔ Holds c input x := by
  unfold asg
  exact @decide_eq_true_iff _ (Classical.propDecidable _)
theorem asg_vP (c : Code) (input : List ℕ) (t q : ℕ) :
    asg c input (vP t q) = true ↔ q = pcCode (c.run input t).pc := by
  rw [asg_iff]
  constructor
  · rintro ⟨t', h | h | ⟨k, j, h⟩⟩
    · simp only [vP] at h
      have h' := uvar_inj _ _ h
      simp only [List.cons.injEq, and_true, true_and] at h'
      obtain ⟨h1, rfl⟩ := h'
      exact h1
    · simp only [vP, vQ] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vP, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
  · rintro rfl
    exact ⟨t, Or.inl rfl⟩
theorem asg_vQ (c : Code) (input : List ℕ) (t v : ℕ) :
    asg c input (vQ t v) = true ↔ v = (c.run input t).state := by
  rw [asg_iff]
  constructor
  · rintro ⟨t', h | h | ⟨k, j, h⟩⟩
    · simp only [vP, vQ] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vQ] at h
      have h' := uvar_inj _ _ h
      simp only [List.cons.injEq, and_true, true_and] at h'
      obtain ⟨h1, rfl⟩ := h'
      exact h1
    · simp only [vQ, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
  · rintro rfl
    exact ⟨t, Or.inr (Or.inl rfl)⟩
theorem asg_vC (c : Code) (input : List ℕ) (t k j x : ℕ) :
    asg c input (vC t k j x) = true ↔ x = cellOf ((c.run input t).stk.getD k []) j := by
  rw [asg_iff]
  constructor
  · rintro ⟨t', h | h | ⟨k', j', h⟩⟩
    · simp only [vP, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vQ, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vC] at h
      have h' := uvar_inj _ _ h
      simp only [List.cons.injEq, and_true, true_and] at h'
      obtain ⟨rfl, h1, rfl, rfl⟩ := h'
      exact h1
  · rintro rfl
    exact ⟨t, Or.inr (Or.inr ⟨k, j, rfl⟩)⟩
theorem eval_imp (σ : Assignment) (prem : List ℕ) (concl : ℕ)
    (h : (∀ x ∈ prem, σ x = true) → σ concl = true) : Clause.eval σ (imp prem concl) = true := by
  unfold Clause.eval imp
  rw [List.any_append, Bool.or_eq_true]
  by_cases hp : ∀ x ∈ prem, σ x = true
  · right
    simp [Literal.eval, h hp]
  · left
    push Not at hp
    obtain ⟨x, hx, hx'⟩ := hp
    rw [List.any_eq_true]
    refine ⟨(x, false), List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    simpa [Literal.eval] using hx'
theorem eval_neg (σ : Assignment) (x : ℕ) (h : ¬ σ x = true) :
    Clause.eval σ [(x, false)] = true := by
  simpa [Clause.eval, Literal.eval] using h
theorem eval_pos (σ : Assignment) (cl : Clause) (x : ℕ) (hx : (x, true) ∈ cl)
    (h : σ x = true) : Clause.eval σ cl = true := by
  unfold Clause.eval
  rw [List.any_eq_true]
  exact ⟨(x, true), hx, by simp [Literal.eval, h]⟩
theorem reads_ok (c : Code) (input : List ℕ) (t B : ℕ) (o : Option ℕ) (r : List ℕ × ℕ)
    (hr : r ∈ reads c.nstk B t o) (h3 : ∀ x ∈ r.1, asg c input x = true) (k : ℕ)
    (hk : o = some k) : r.2 = topIndex ((c.run input t).stk.getD k []) := by
  subst hk
  simp only [reads] at hr
  split_ifs at hr with hlt
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨x, -, rfl⟩ := hr
    have h := (asg_vC c input t k 0 x).1 (h3 _ (by simp))
    rw [cellOf_zero] at h
    exact h
  · rw [List.mem_singleton] at hr
    subst hr
    rw [getD_of_le _ _ (by rw [len_run]; omega)]
    rfl
theorem step_ok (c : Code) (input : List ℕ) (t H B : ℕ) (hH : input.length + t ≤ H) :
    ∀ cl ∈ stepClauses c.nstk H B c.prog t, Clause.eval (asg c input) cl = true := by
  intro cl hcl
  simp only [stepClauses, List.mem_flatMap, List.mem_append, List.mem_range] at hcl
  obtain ⟨q, -, (hcl | hcl) | ⟨k, hk, hcl⟩⟩ := hcl
  · simp only [pcClauses, List.mem_map, List.mem_range] at hcl
    obtain ⟨v, -, rfl⟩ := hcl
    apply eval_imp
    intro hp
    have h1 := (asg_vP c input t q).1 (hp _ (by simp))
    have h2 := (asg_vQ c input t v).1 (hp _ (by simp))
    rw [asg_vP, run_succ, pcCode_exec, ← h1, ← h2]
  · simp only [stateClauses, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
    obtain ⟨v, -, r, hr, rfl⟩ := hcl
    apply eval_imp
    intro hp
    have h1 := (asg_vP c input t q).1 (hp _ (by simp))
    have h2 := (asg_vQ c input t v).1 (hp _ (by simp))
    have h3 : ∀ x ∈ r.1, asg c input x = true := fun x hx => hp x (by simp [hx])
    rw [asg_vQ, run_succ, ← h1, ← h2]
    symm
    apply state_exec
    intro k hk
    exact reads_ok c input t B _ r hr h3 k hk
  · have hkS : k < (c.run input t).stk.length := by rw [len_run]; exact hk
    cases hop : stackOp (instrAt c.prog q) k with
    | keep =>
      rw [hop] at hcl
      simp only [cellClauses, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
      obtain ⟨j, -, x, -, rfl⟩ := hcl
      apply eval_imp
      intro hp
      have h1 := (asg_vP c input t q).1 (hp _ (by simp))
      have h2 := (asg_vC c input t k j x).1 (hp _ (by simp))
      rw [asg_vC, run_succ, ← h1, stk_exec_keep _ _ _ _ hop]
      exact h2
    | push tbl =>
      rw [hop] at hcl
      simp only [cellClauses, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range] at hcl
      rcases hcl with ⟨v, -, rfl⟩ | ⟨j, -, x, -, rfl⟩
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        have h2 := (asg_vQ c input t v).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, ← h2, stk_exec_push _ _ _ _ _ hkS hop, cellOf_cons_zero]
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        have h2 := (asg_vC c input t k j x).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, stk_exec_push _ _ _ _ _ hkS hop, cellOf_cons_succ]
        exact h2
    | pop =>
      rw [hop] at hcl
      simp only [cellClauses, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range, List.mem_singleton] at hcl
      rcases hcl with ⟨j, -, x, -, rfl⟩ | rfl
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        have h2 := (asg_vC c input t k (j + 1) x).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, stk_exec_pop _ _ _ _ hkS hop, cellOf_tail]
        exact h2
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, stk_exec_pop _ _ _ _ hkS hop, eq_comm, cellOf_eq_zero_iff,
          List.length_tail]
        have hh := height c input t k
        omega
theorem init_ok (c : Code) (zs : List ℕ) (w : List Bool) (m H : ℕ) (hw : w.length ≤ m) :
    ∀ cl ∈ initClauses c zs m H,
      Clause.eval (asg c (zs ++ w.map fun b => cond b 3 2)) cl = true := by
  intro cl hcl
  simp only [initClauses, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with ((rfl | rfl) | ⟨k, hk, hcl⟩) | hcl
  · apply eval_imp
    intro _
    rw [asg_vP]
    rfl
  · apply eval_imp
    intro _
    rw [asg_vQ]
    rfl
  · split_ifs at hcl with hkin
    · simp at hcl
    · simp only [List.mem_map, List.mem_range] at hcl
      obtain ⟨j, -, rfl⟩ := hcl
      apply eval_imp
      intro _
      rw [asg_vC, stk_init, ite_eq_right (fun e => hkin e.1.symm)]
      simp [cellOf]
  · split_ifs at hcl with hkin
    · have hin : (c.run (zs ++ w.map fun b => cond b 3 2) 0).stk.getD c.kin [] =
          zs ++ w.map fun b => cond b 3 2 := by
        rw [stk_init, ite_eq_left ⟨rfl, hkin⟩]
      simp only [List.mem_append, List.mem_map, List.mem_range] at hcl
      rcases hcl with ((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
      · apply eval_imp
        intro _
        rw [asg_vC, hin, cellOf_append_left _ _ _ hj]
      · have hcell := cellOf_append_right zs (w.map fun b => cond b 3 2) j
        rcases cellOf_witness w j with h0 | h0 | h0
        · refine eval_pos _ _ (vC 0 c.kin (zs.length + j) 0) (by simp) ?_
          rw [asg_vC, hin, hcell, h0]
        · refine eval_pos _ _ (vC 0 c.kin (zs.length + j) 3) (by simp) ?_
          rw [asg_vC, hin, hcell, h0]
        · refine eval_pos _ _ (vC 0 c.kin (zs.length + j) 4) (by simp) ?_
          rw [asg_vC, hin, hcell, h0]
      · apply eval_imp
        intro hp
        have h1 := (asg_vC c _ 0 c.kin (zs.length + j) 0).1 (hp _ (by simp))
        rw [hin, eq_comm, cellOf_eq_zero_iff] at h1
        rw [asg_vC, hin, eq_comm, cellOf_eq_zero_iff]
        omega
      · apply eval_imp
        intro _
        rw [asg_vC, hin, eq_comm, cellOf_eq_zero_iff]
        simp only [List.length_append, List.length_map]
        omega
    · simp at hcl
theorem final_ok (c : Code) (input : List ℕ) (B T : ℕ) (h : c.outputsWithin input T [1]) :
    ∀ cl ∈ finalClauses c B T, Clause.eval (asg c input) cl = true := by
  obtain ⟨hpc, hout⟩ := h
  intro cl hcl
  simp only [finalClauses, List.mem_append, List.mem_map, List.mem_range] at hcl
  rcases hcl with ⟨p, -, rfl⟩ | hcl
  · apply eval_neg
    rw [asg_vP, hpc]
    simp [pcCode]
  · split_ifs at hcl with hk
    · simp only [List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_map,
        List.mem_range] at hcl
      rcases hcl with (rfl | ⟨x, -, hx⟩) | ⟨x, -, rfl⟩
      · apply eval_neg
        rw [asg_vC, hout]
        simp [cellOf]
      · split_ifs at hx with hx1
        · simp at hx
        · rw [List.mem_singleton] at hx
          subst hx
          apply eval_neg
          rw [asg_vC, hout]
          simp [cellOf, hx1]
      · apply eval_neg
        rw [asg_vC, hout]
        simp [cellOf]
    · exfalso
      rw [getD_of_le _ _ (by rw [len_run]; omega)] at hout
      simp at hout
end Cpl
theorem sat_of_accepts (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4)
    (w : List Bool) (hw : w.length ≤ m)
    (h : c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1]) :
    PEqualNP.Search.Satisfiable (tableau c zs m T) := by
  refine ⟨Cpl.asg c (zs ++ w.map (fun b => cond b 3 2)), ?_⟩
  unfold CNF.eval tableau
  rw [List.all_eq_true]
  intro cl hcl
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hcl
  rcases hcl with (hcl | ⟨t, ht, hcl⟩) | hcl
  · exact Cpl.init_ok c zs w m _ hw cl hcl
  · refine Cpl.step_ok c _ t _ _ ?_ cl hcl
    have _ := hz
    have hl : (zs ++ w.map (fun b => cond b 3 2)).length = zs.length + w.length := by simp
    rw [hl]
    unfold cellsOf
    omega
  · exact Cpl.final_ok c _ _ T h cl hcl
end Lib.SearchHelpers.Tab
end
section
namespace Lib.SearchHelpers.Tab.StepW
open PEqualNP.Library Lib.Machines Lib.Universal
theorem cptE {f f' : List Bool → List Bool} (h : Lib.CPTs f) (e : ∀ a, f a = f' a) :
    Lib.CPTs f' := by
  obtain rfl : f = f' := funext e
  exact h
theorem cpt_iterMeasure {g cnt arg : List Bool → List Bool} (hg : Lib.CPTs g)
    (m : List Bool → ℕ) (a : ℕ) (hm : ∀ y, m (g y) ≤ m y)
    (hgl : ∀ y, (g y).length ≤ y.length + m y) (ha : ∀ y, m y ≤ a * y.length + a)
    (hcnt : Lib.CPTs cnt) (harg : Lib.CPTs arg) :
    Lib.CPTs (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  exact cptE (cpt_comp (cpt_pair harg hcnt) (Iter.iter_polyTime_measure g c m a hm hgl ha))
    (fun _ => rfl)
def tk (p w : List Bool) : List Bool := (unpairB (mulU p [true] ++ false :: w)).1
theorem tk_eq (p w : List Bool) : tk p w = w.take p.length := by
  have h1 : (mulU p [true] ++ false :: w).takeWhile id = un p.length := by
    simp [mulU, un]
  have h2 : (mulU p [true] ++ false :: w).dropWhile id = false :: w := by
    simp [mulU, un]
  simp [tk, unpairB, h1, h2, un]
theorem tk_length (p w : List Bool) : (tk p w).length ≤ p.length := by
  rw [tk_eq, List.length_take]
  exact Nat.min_le_left _ _
theorem cpt_tk {p w : List Bool → List Bool} (hp : Lib.CPTs p) (hw : Lib.CPTs w) :
    Lib.CPTs (fun s => tk (p s) (w s)) :=
  cpt_unpairB1_1 (cpt_app2 (cpt_mulU2 hp (cpt_const [true])) (cpt_cons1 false hw))
def lstep (f : List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1 (pairB (unpairB (unpairB y).2).1.tail
    (pairB (unpairB (unpairB (unpairB y).2).2).1
      (tk (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
        (unpairB (unpairB (unpairB y).2).2).1)) ++ (unpairB (unpairB (unpairB y).2).2).2)))
theorem cpt_lstep {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (lstep f) := by
  have h1 : Lib.CPTs (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : Lib.CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have hr := cpt_tail1 (cpt_unpairB1_1 h2)
  have h3 := cpt_unpairB2_1 h2
  have harg := cpt_unpairB1_1 h3
  have hacc := cpt_unpairB2_1 h3
  exact cpt_pairB2 h1 (cpt_pairB2 hr (cpt_pairB2 harg
    (cpt_app2 (cpt_tk h1 (cpt_comp (cpt_pairB2 hr harg) hf)) hacc)))
theorem lstep_pairB (f : List Bool → List Bool) (pad r arg acc : List Bool) :
    lstep f (pairB pad (pairB r (pairB arg acc))) =
      pairB pad (pairB r.tail (pairB arg (tk pad (f (pairB r.tail arg)) ++ acc))) := by
  simp only [lstep, unpairB_pairB]
theorem lstep_measure (f : List Bool → List Bool) (y : List Bool) :
    (unpairB (lstep f y)).1.length + 3 ≤ (unpairB y).1.length + 3 := by
  simp only [lstep, unpairB_pairB]
  exact le_rfl
theorem lstep_length (f : List Bool → List Bool) (y : List Bool) :
    (lstep f y).length ≤ y.length + ((unpairB y).1.length + 3) := by
  have h1 := unpairB_length y
  have h2 := unpairB_length (unpairB y).2
  have h3 := unpairB_length (unpairB (unpairB y).2).2
  have h4 := tk_length (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
        (unpairB (unpairB (unpairB y).2).2).1))
  have h5 : (unpairB (unpairB y).2).1.tail.length ≤ (unpairB (unpairB y).2).1.length := by
    simp
  simp only [lstep, pairB_length, List.length_append]
  omega
theorem lstep_iter (f : List Bool → List Bool) (pad arg : List Bool) (n : ℕ)
    (hpad : ∀ i < n, (f (pairB (un i) arg)).length ≤ pad.length) (acc : List Bool) :
    (lstep f)^[n] (pairB pad (pairB (un n) (pairB arg acc))) =
      pairB pad (pairB [] (pairB arg
        ((List.range n).flatMap (fun i => f (pairB (un i) arg)) ++ acc))) := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, lstep_pairB, un_succ, List.tail_cons, tk_eq,
      List.take_of_length_le (hpad n (by omega)), ih (fun i hi => hpad i (by omega)),
      List.range_succ, List.flatMap_append]
    simp
theorem cpt_flatMapRange {f cnt arg : List Bool → List Bool} (hf : Lib.CPTs f) (hcnt : Lib.CPTs cnt)
    (harg : Lib.CPTs arg) :
    Lib.CPTs (fun s => (List.range (cnt s).length).flatMap fun i => f (pairB (un i) (arg s))) := by
  obtain ⟨P, hP⟩ := output_length_poly f hf
  have hpad : Lib.CPTs (fun s => List.replicate (P.eval (pairB (cnt s) (arg s)).length) true) :=
    cpt_comp (cpt_pairB2 hcnt harg) (Lib.L055 P)
  have hun : Lib.CPTs (fun s => mulU (cnt s) [true]) := cpt_mulU2 hcnt (cpt_const [true])
  have hinit := cpt_pairB2 hpad (cpt_pairB2 hun (cpt_pairB2 harg (cpt_const [])))
  have hit := cpt_iterMeasure (cpt_lstep hf) (fun y => (unpairB y).1.length + 3) 3
    (lstep_measure f) (lstep_length f)
    (fun y => by have := unpairB_length y; omega) hcnt hinit
  have hout := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hit))
  refine cptE hout (fun s => ?_)
  have e : mulU (cnt s) [true] = un (cnt s).length := by simp [mulU]
  have hb : ∀ i < (cnt s).length, (f (pairB (un i) (arg s))).length ≤
      (List.replicate (P.eval (pairB (cnt s) (arg s)).length) true).length := by
    intro i hi
    rw [List.length_replicate]
    refine (hP _).trans (eval_mono P ?_)
    rw [pairB_length, pairB_length, un_length]
    omega
  show (unpairB (unpairB (unpairB ((lstep f)^[(cnt s).length]
    (pairB _ (pairB (mulU (cnt s) [true]) (pairB (arg s) []))))).2).2).2 = _
  rw [e, lstep_iter f _ (arg s) (cnt s).length hb, unpairB_pairB, unpairB_pairB, unpairB_pairB]
  simp
end Lib.SearchHelpers.Tab.StepW
end
section
namespace Lib.SearchHelpers.Tab.StepW
open PEqualNP.Library Lib.Machines Lib.Universal PEqualNP.Search
theorem bits_pow_mul (a m : ℕ) (hm : m ≠ 0) :
    (2 ^ a * m).bits = List.replicate a false ++ m.bits := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
    rw [e, Nat.bit0_bits _ (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hm), ih]
    rfl
theorem bits_uvar (l : List ℕ) :
    (uvar l).bits = l.flatMap fun a => List.replicate a false ++ [true] := by
  induction l with
  | nil => simp [uvar]
  | cons a r ih =>
    simp only [uvar]
    rw [bits_pow_mul _ _ (by omega), Nat.bit1_bits, ih]
    simp
def digs : List ℕ → List Bool
  | [] => []
  | a :: r => spread (un a) ++ true :: true :: digs r
theorem spread_un (a : ℕ) :
    spread (un a) = (List.replicate a false).flatMap fun d => [true, d] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [un_succ, List.replicate_succ, List.flatMap_cons, ← ih]
    rfl
theorem digs_eq (l : List ℕ) : ((uvar l).bits.flatMap fun d => [true, d]) = digs l := by
  rw [bits_uvar]
  induction l with
  | nil => rfl
  | cons a r ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.flatMap_append, ih, digs, spread_un]
    simp
theorem encodeLiteral_uvar (l : List ℕ) (b : Bool) :
    encodeLiteral (uvar l, b) = true :: b :: (digs l ++ [false, true]) := by
  simp [encodeLiteral, digs_eq]
theorem encodeCNF_append (φ ψ : CNF) : encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  simp [encodeCNF]
theorem encodeCNF_flatMap {α : Type} (l : List α) (φ : α → CNF) :
    encodeCNF (l.flatMap φ) = l.flatMap fun a => encodeCNF (φ a) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, encodeCNF_append, ih, List.flatMap_cons]
def NatC (n : List Bool → ℕ) : Prop := Lib.CPTs (fun s => un (n s))
def DigC (l : List Bool → List ℕ) : Prop := Lib.CPTs (fun s => digs (l s))
def VarC (v : List Bool → ℕ) : Prop := ∀ b : Bool, Lib.CPTs (fun s => encodeLiteral (v s, b))
def ClC (c : List Bool → Clause) : Prop := Lib.CPTs (fun s => encodeClause (c s))
def CnfC (φ : List Bool → CNF) : Prop := Lib.CPTs (fun s => encodeCNF (φ s))
theorem natC_const (k : ℕ) : NatC (fun _ => k) := cpt_const (un k)
theorem natC_succ {n : List Bool → ℕ} (h : NatC n) : NatC (fun s => n s + 1) :=
  cptE (cpt_cons1 true h) (fun _ => rfl)
theorem natC_pred {n : List Bool → ℕ} (h : NatC n) : NatC (fun s => n s - 1) :=
  cptE (cpt_tail1 h) (fun s => by
    show (un (n s)).tail = un (n s - 1)
    cases n s <;> rfl)
theorem natC_len {u : List Bool → List Bool} (hu : Lib.CPTs u) : NatC (fun s => (u s).length) :=
  cptE (cpt_mulU2 hu (cpt_const [true])) (fun s => by simp [mulU])
theorem natC_fst : NatC (fun y => (unpairB y).1.length) := natC_len cpt_unpairB1
theorem natC_snd {n : List Bool → ℕ} (h : NatC n) : NatC (fun y => n (unpairB y).2) :=
  cptE (cpt_comp cpt_unpairB2 (show Lib.CPTs (fun s => un (n s)) from h)) (fun _ => rfl)
theorem digC_nil : DigC (fun _ => []) := cpt_const []
theorem digC_cons {a : List Bool → ℕ} {l : List Bool → List ℕ} (ha : NatC a) (hl : DigC l) :
    DigC (fun s => a s :: l s) :=
  cptE (cpt_app2 (cpt_comp ha cpt_spread) (cpt_cons1 true (cpt_cons1 true hl))) (fun _ => rfl)
theorem varC_of_dig {l : List Bool → List ℕ} (hl : DigC l) : VarC (fun s => uvar (l s)) :=
  fun b => cptE (cpt_cons1 true (cpt_cons1 b (cpt_app2 hl (cpt_const [false, true]))))
    (fun _ => (encodeLiteral_uvar _ _).symm)
theorem varC_vP {t q : List Bool → ℕ} (ht : NatC t) (hq : NatC q) :
    VarC (fun s => vP (t s) (q s)) :=
  varC_of_dig (digC_cons (natC_const 0) (digC_cons hq (digC_cons ht digC_nil)))
theorem varC_vQ {t v : List Bool → ℕ} (ht : NatC t) (hv : NatC v) :
    VarC (fun s => vQ (t s) (v s)) :=
  varC_of_dig (digC_cons (natC_const 1) (digC_cons hv (digC_cons ht digC_nil)))
theorem varC_vC {t k j x : List Bool → ℕ} (ht : NatC t) (hk : NatC k) (hj : NatC j)
    (hx : NatC x) : VarC (fun s => vC (t s) (k s) (j s) (x s)) :=
  varC_of_dig (digC_cons (natC_const 2) (digC_cons hk (digC_cons hx (digC_cons hj
    (digC_cons ht digC_nil)))))
theorem clC_nil : ClC (fun _ => []) := cptE (cpt_const [false, false]) (fun _ => rfl)
theorem clC_cons {v : List Bool → ℕ} {c : List Bool → Clause} (hv : VarC v) (b : Bool)
    (hc : ClC c) : ClC (fun s => (v s, b) :: c s) :=
  cptE (cpt_app2 (hv b) hc) (fun _ => by simp [encodeClause])
theorem clC_imp_nil {c : List Bool → ℕ} (hc : VarC c) : ClC (fun s => imp [] (c s)) :=
  cptE (clC_cons hc true clC_nil) (fun _ => rfl)
theorem clC_imp_cons {a c : List Bool → ℕ} {p : List Bool → List ℕ} (ha : VarC a)
    (h : ClC (fun s => imp (p s) (c s))) : ClC (fun s => imp (a s :: p s) (c s)) :=
  cptE (clC_cons ha false h) (fun _ => rfl)
theorem cnfC_nil : CnfC (fun _ => []) := cpt_const []
theorem cnfC_append {φ ψ : List Bool → CNF} (h1 : CnfC φ) (h2 : CnfC ψ) :
    CnfC (fun s => φ s ++ ψ s) :=
  cptE (cpt_app2 h1 h2) (fun _ => (encodeCNF_append _ _).symm)
theorem cnfC_cons {c : List Bool → Clause} {φ : List Bool → CNF} (h1 : ClC c) (h2 : CnfC φ) :
    CnfC (fun s => c s :: φ s) :=
  cptE (cpt_app2 h1 h2) (fun _ => by simp [encodeCNF])
theorem cnfC_flatMap_const {α : Type} (l : List α) {φ : α → List Bool → CNF}
    (h : ∀ a, CnfC (φ a)) : CnfC (fun s => l.flatMap fun a => φ a s) := by
  induction l with
  | nil => exact cnfC_nil
  | cons a l ih => exact cnfC_append (h a) ih
theorem cnfC_map_const {α : Type} (l : List α) {c : α → List Bool → Clause}
    (h : ∀ a, ClC (c a)) : CnfC (fun s => l.map fun a => c a s) := by
  induction l with
  | nil => exact cnfC_nil
  | cons a l ih => exact cnfC_cons (h a) ih
theorem cnfC_flatMap_range {n : List Bool → ℕ} (hn : NatC n) {φ : ℕ → List Bool → CNF}
    (h : CnfC (fun y => φ (unpairB y).1.length (unpairB y).2)) :
    CnfC (fun s => (List.range (n s)).flatMap fun j => φ j s) := by
  have h' := cpt_flatMapRange h hn cpt_id
  refine cptE h' (fun s => ?_)
  simp only [unpairB_pairB, un_length]
  exact (encodeCNF_flatMap _ _).symm
theorem pcC (B q : ℕ) (i : Instr) {t : List Bool → ℕ} (ht : NatC t) :
    CnfC (fun s => pcClauses B (t s) q i) := by
  refine cnfC_map_const (List.range B)
    (c := fun v s => imp [vP (t s) q, vQ (t s) v] (vP (t s + 1) (nextCode i v))) (fun v => ?_)
  exact clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons (varC_vQ ht (natC_const v))
    (clC_imp_nil (varC_vP (natC_succ ht) (natC_const _))))
theorem readsC (K B q v : ℕ) (o : Option ℕ) (g : ℕ → ℕ) {t : List Bool → ℕ} (ht : NatC t) :
    CnfC (fun s => (reads K B (t s) o).map fun r =>
      imp (vP (t s) q :: vQ (t s) v :: r.1) (vQ (t s + 1) (g r.2))) := by
  have hnone : CnfC (fun s => [imp [vP (t s) q, vQ (t s) v] (vQ (t s + 1) (g 0))]) :=
    cnfC_cons (clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
      (varC_vQ ht (natC_const v)) (clC_imp_nil (varC_vQ (natC_succ ht) (natC_const _)))))
      cnfC_nil
  cases o with
  | none => exact hnone
  | some k =>
    by_cases hk : k < K
    · have h : CnfC (fun s => (List.range (B + 1)).map fun x =>
          imp [vP (t s) q, vQ (t s) v, vC (t s) k 0 x] (vQ (t s + 1) (g x))) :=
        cnfC_map_const _ (fun x => clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
          (varC_vQ ht (natC_const v)) (clC_imp_cons
            (varC_vC ht (natC_const k) (natC_const 0) (natC_const x))
            (clC_imp_nil (varC_vQ (natC_succ ht) (natC_const _))))))
      refine cptE h (fun s => ?_)
      simp only [reads, hk, ↓reduceIte, List.map_map]
      rfl
    · refine cptE hnone (fun s => ?_)
      simp [reads, hk]
theorem stateC (K B q : ℕ) (i : Instr) {t : List Bool → ℕ} (ht : NatC t) :
    CnfC (fun s => stateClauses K B (t s) q i) :=
  cnfC_flatMap_const (List.range B) (fun v => readsC K B q v (rdStack i) (newState i v) ht)
theorem rowC (B q k : ℕ) {t j j' : List Bool → ℕ} (ht : NatC t) (hj : NatC j)
    (hj' : NatC j') :
    CnfC (fun s => (List.range (B + 1)).map fun x =>
      imp [vP (t s) q, vC (t s) k (j s) x] (vC (t s + 1) k (j' s) x)) :=
  cnfC_map_const _ (fun x => clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
    (varC_vC ht (natC_const k) hj (natC_const x))
    (clC_imp_nil (varC_vC (natC_succ ht) (natC_const k) hj' (natC_const x)))))
theorem cellC (B q k : ℕ) (op : Op) {H t : List Bool → ℕ} (hH : NatC H) (ht : NatC t) :
    CnfC (fun s => cellClauses (H s) B (t s) q k op) := by
  cases op with
  | keep =>
    exact cnfC_flatMap_range hH
      (φ := fun j s => (List.range (B + 1)).map fun x =>
        imp [vP (t s) q, vC (t s) k j x] (vC (t s + 1) k j x))
      (rowC B q k (natC_snd ht) natC_fst natC_fst)
  | push tbl =>
    refine cnfC_append ?_ ?_
    · exact cnfC_map_const (List.range B)
        (c := fun v s => imp [vP (t s) q, vQ (t s) v] (vC (t s + 1) k 0 (tbl.getD v 0 + 1)))
        (fun v => clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
          (varC_vQ ht (natC_const v)) (clC_imp_nil
            (varC_vC (natC_succ ht) (natC_const k) (natC_const 0) (natC_const _)))))
    · exact cnfC_flatMap_range (natC_pred hH)
        (φ := fun j s => (List.range (B + 1)).map fun x =>
          imp [vP (t s) q, vC (t s) k j x] (vC (t s + 1) k (j + 1) x))
        (rowC B q k (natC_snd ht) natC_fst (natC_succ natC_fst))
  | pop =>
    refine cnfC_append ?_ ?_
    · exact cnfC_flatMap_range (natC_pred hH)
        (φ := fun j s => (List.range (B + 1)).map fun x =>
          imp [vP (t s) q, vC (t s) k (j + 1) x] (vC (t s + 1) k j x))
        (rowC B q k (natC_snd ht) (natC_succ natC_fst) natC_fst)
    · exact cnfC_cons (clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_nil
        (varC_vC (natC_succ ht) (natC_const k) (natC_pred hH) (natC_const 0)))) cnfC_nil
theorem stepC (K B : ℕ) (P : List Instr) {H t : List Bool → ℕ} (hH : NatC H) (ht : NatC t) :
    CnfC (fun s => stepClauses K (H s) B P (t s)) :=
  cnfC_flatMap_const (List.range (B + 1)) (fun q =>
    cnfC_append (cnfC_append (pcC B q (instrAt P q) ht) (stateC K B q (instrAt P q) ht))
      (cnfC_flatMap_const (List.range K)
        (fun k => cellC B q k (stackOp (instrAt P q) k) hH ht)))
end Lib.SearchHelpers.Tab.StepW
namespace Lib.SearchHelpers.Tab
open PEqualNP.Library Lib.Machines Lib.Universal StepW
theorem cpt_stepPart (c : Lib.Universal.Code) (p q : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        ((List.range (q.eval x.length)).flatMap fun t =>
          stepClauses c.nstk (cellsOf x.length (p.eval x.length) (q.eval x.length))
            (bound c) c.prog t)) := by
  have hT : NatC (fun x => q.eval x.length) := Lib.L055 q
  have hH : NatC (fun x => cellsOf x.length (p.eval x.length) (q.eval x.length)) := by
    refine cptE (natC_len (cpt_app2 cpt_id (cpt_app2 (Lib.L055 p)
      (cpt_app2 (Lib.L055 q) (cpt_const [true, true]))))) (fun x => ?_)
    congr 1
    simp only [cellsOf, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  exact cnfC_flatMap_range hT
    (φ := fun t x => stepClauses c.nstk (cellsOf x.length (p.eval x.length) (q.eval x.length))
      (bound c) c.prog t)
    (stepC c.nstk (bound c) c.prog (natC_snd hH) natC_fst)
end Lib.SearchHelpers.Tab
end
section
namespace Lib.SearchHelpers.Tab
namespace Edge
open PEqualNP.Library Lib.Machines Lib.Universal PEqualNP.Search
theorem cptE {f f' : List Bool → List Bool} (h : Lib.CPTs f) (e : ∀ a, f a = f' a) : Lib.CPTs f' := by
  obtain rfl : f = f' := funext e
  exact h
def U (a : ℕ) : List Bool := (List.replicate a true).flatMap fun _ => [true, false]
theorem U_zero : U 0 = [] := rfl
theorem U_succ (a : ℕ) : U (a + 1) = true :: false :: U a := by
  simp [U, List.replicate_succ]
theorem U_add (a b : ℕ) : U (a + b) = U a ++ U b := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, U_succ, U_succ, ih]
    rfl
theorem U_length (a : ℕ) : (U a).length = 2 * a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [U_succ]; simp only [List.length_cons, ih]; omega
theorem bits_pow_mul (a n : ℕ) (hn : n ≠ 0) :
    (2 ^ a * n).bits = List.replicate a false ++ n.bits := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 2 ^ (a + 1) * n = 2 * (2 ^ a * n) := by ring
    have h0 : 2 ^ a * n ≠ 0 := Nat.mul_ne_zero (by positivity) hn
    rw [e, Nat.bit0_bits _ h0, ih, List.replicate_succ, List.cons_append]
theorem bits_uvar (l : List ℕ) :
    (uvar l).bits = l.flatMap fun a => List.replicate a false ++ [true] := by
  induction l with
  | nil => simp [uvar]
  | cons a r ih =>
    rw [uvar, bits_pow_mul _ _ (by omega), Nat.bit1_bits, ih]
    simp
theorem digits_block (a : ℕ) :
    ((List.replicate a false ++ [true]).flatMap fun d => [true, d]) = U a ++ [true, true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, List.flatMap_cons, ih, U_succ]
    rfl
theorem encodeLiteral_uvar (l : List ℕ) (pol : Bool) :
    encodeLiteral (uvar l, pol) =
      [true, pol] ++ (l.flatMap fun a => U a ++ [true, true]) ++ [false, true] := by
  have h : ((uvar l).bits.flatMap fun d => [true, d]) = l.flatMap fun a => U a ++ [true, true] := by
    rw [bits_uvar]
    induction l with
    | nil => rfl
    | cons a r ih =>
      rw [List.flatMap_cons, List.flatMap_append, digits_block, ih, List.flatMap_cons]
  simp only [encodeLiteral]
  rw [h]
def lpre (pol : Bool) (pre : List ℕ) : List Bool :=
  [true, pol] ++ pre.flatMap fun a => U a ++ [true, true]
def lpost (post : List ℕ) : List Bool :=
  [true, true] ++ (post.flatMap fun a => U a ++ [true, true]) ++ [false, true]
theorem encodeLiteral_split (pol : Bool) (pre : List ℕ) (i : ℕ) (post : List ℕ) :
    encodeLiteral (uvar (pre ++ i :: post), pol) = lpre pol pre ++ (U i ++ lpost post) := by
  rw [encodeLiteral_uvar]
  simp [lpre, lpost, List.flatMap_append, List.flatMap_cons]
theorem encodeClause_single (pol : Bool) (pre : List ℕ) (i : ℕ) (post : List ℕ) :
    encodeClause [(uvar (pre ++ i :: post), pol)] =
      lpre pol pre ++ (U i ++ (lpost post ++ [false, false])) := by
  simp only [encodeClause, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeLiteral_split]
  simp only [List.append_assoc]
theorem encodeCNF_append (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF]
theorem encodeCNF_map {ι : Type} (l : List ι) (f : ι → Clause) :
    encodeCNF (l.map f) = l.flatMap fun i => encodeClause (f i) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.flatMap_cons] at ih ⊢
    rw [← ih]
    rfl
theorem flatMap_congr_mem {ι β : Type} (l : List ι) (f g : ι → List β)
    (h : ∀ i ∈ l, f i = g i) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
      ih (fun i hi => h i (by simp [hi]))]
theorem cpt_unary {f : List Bool → List Bool} (hf : Lib.CPTs f) :
    Lib.CPTs (fun x => un (f x).length) := by
  have h : Lib.CPTs (fun x : List Bool => un x.length) := by
    refine filterMap_polyTime _ _ _ (fun _ : Bool => some true) ?_
    intro x
    induction x with
    | nil => rfl
    | cons a l ih =>
      simp only [un, List.length_cons, List.replicate_succ, List.filterMap_cons] at ih ⊢
      exact congrArg (List.cons true) ih
  exact cpt_comp (g := fun x : List Bool => un x.length) hf h
theorem cpt_U {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (fun x => U (f x).length) := by
  have h : Lib.CPTs (fun x : List Bool => U x.length) := by
    refine fst2_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true, some false))
      (fun _ => none) () ?_
    intro x
    induction x with
    | nil => rfl
    | cons a l ih =>
      show U (l.length + 1) = _
      rw [U_succ]
      exact congrArg (fun r => true :: false :: r) ih
  exact cpt_comp (g := fun x : List Bool => U x.length) hf h
theorem cpt_flatMap_const {ι : Type} (l : List ι) (f : ι → List Bool → List Bool)
    (h : ∀ i, Lib.CPTs (f i)) : Lib.CPTs (fun x => l.flatMap fun i => f i x) := by
  induction l with
  | nil => exact cpt_const []
  | cons a l ih => exact cptE (cpt_app2 (h a) ih) (fun x => by simp)
theorem cpt_encFlatMap_const {ι : Type} (l : List ι) (f : ι → List Bool → CNF)
    (h : ∀ i, Lib.CPTs (fun x => encodeCNF (f i x))) :
    Lib.CPTs (fun x => encodeCNF (l.flatMap fun i => f i x)) := by
  refine cptE (cpt_flatMap_const l (fun i x => encodeCNF (f i x)) h) (fun x => ?_)
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, encodeCNF_append, ih]
theorem cpt_encMap_const {ι : Type} (l : List ι) (f : ι → List Bool → Clause)
    (h : ∀ i, Lib.CPTs (fun x => encodeCNF [f i x])) :
    Lib.CPTs (fun x => encodeCNF (l.map fun i => f i x)) := by
  refine cptE (cpt_encFlatMap_const l (fun i x => [f i x]) h) (fun x => ?_)
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl
def loopG (blk : List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1
    (pairB (unpairB (unpairB y).2).1.tail
      ((unpairB (unpairB y).2).2 ++
        blk (pairB (unpairB (unpairB y).1).1
          ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
            (unpairB (unpairB y).1).2))))
theorem tail_iter (k : ℕ) (l : List Bool) : (fun s : List Bool => s.tail)^[k] l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l <;> simp
theorem cpt_loopG {blk : List Bool → List Bool} (hblk : Lib.CPTs blk) : Lib.CPTs (loopG blk) := by
  have h1 : Lib.CPTs (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : Lib.CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have h21 := cpt_unpairB1_1 h2
  have h22 := cpt_unpairB2_1 h2
  have h11 := cpt_unpairB1_1 h1
  have h12 := cpt_unpairB2_1 h1
  have hJ := cpt_iterLen cpt_tail (fun s => by simp) h21 h12
  exact cpt_pairB2 h1 (cpt_pairB2 (cpt_tail1 h21)
    (cpt_app2 h22 (cpt_comp (cpt_pairB2 h11 hJ) hblk)))
theorem loopG_pair (blk : List Bool → List Bool) (e C r out : List Bool) :
    loopG blk (pairB (pairB e C) (pairB r out)) =
      pairB (pairB e C) (pairB r.tail (out ++ blk (pairB e (C.drop r.length)))) := by
  simp only [loopG, unpairB_pairB, tail_iter]
theorem loopG_iter (blk : List Bool → List Bool) (e : List Bool) (N : ℕ) :
    ∀ i, i ≤ N → (loopG blk)^[i] (pairB (pairB e (un N)) (pairB (un N) [])) =
      pairB (pairB e (un N))
        (pairB (un (N - i)) ((List.range i).flatMap fun j => blk (pairB e (un j)))) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), loopG_pair]
    have e1 : (un (N - i)).tail = un (N - (i + 1)) := by
      simp only [un, List.tail_replicate]
      congr 1
    have e2 : (un N).drop (un (N - i)).length = un i := by
      simp only [un, List.length_replicate, List.drop_replicate]
      congr 1
      omega
    rw [e1, e2, List.range_succ, List.flatMap_append]
    simp
theorem cpt_loop {blk : List Bool → List Bool} (hblk : Lib.CPTs blk) (a : ℕ)
    (hlen : ∀ s, (blk s).length ≤ a * s.length + a) {env cnt : List Bool → List Bool}
    (henv : Lib.CPTs env) (hcnt : Lib.CPTs cnt) :
    Lib.CPTs (fun x => (List.range (cnt x).length).flatMap fun j => blk (pairB (env x) (un j))) := by
  have hI := cpt_iterB (loopG blk) (cpt_loopG hblk)
    (fun y => a * ((unpairB y).1.length + 1) + a + 2) (2 * a + 2)
    (fun y => by simp only [loopG, unpairB_pairB]; exact le_rfl)
    (fun y => by
      have h1 := unpairB_length y
      have h2 := unpairB_length (unpairB y).2
      have h3 := unpairB_length (unpairB y).1
      have hJ : ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
          (unpairB (unpairB y).1).2).length ≤ (unpairB (unpairB y).1).2.length :=
        iter_length _ (fun s => by simp) _ _
      have hb := hlen (pairB (unpairB (unpairB y).1).1
        ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
          (unpairB (unpairB y).1).2))
      rw [pairB_length] at hb
      have hb' := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left a
        (show 2 * (unpairB (unpairB y).1).1.length +
          ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
            (unpairB (unpairB y).1).2).length + 1 ≤ (unpairB y).1.length + 1 by omega)) a)
      simp only [loopG, pairB_length, List.length_append, List.length_tail]
      omega)
    (fun y => by
      have h1 := unpairB_length y
      have h4 : a * ((unpairB y).1.length + 1) ≤ a * (y.length + 1) :=
        Nat.mul_le_mul_left a (by omega)
      have h5 : (2 * a + 2) * y.length = 2 * (a * y.length) + 2 * y.length := by ring
      have h6 : a * (y.length + 1) = a * y.length + a := by ring
      omega)
  have hC := cpt_unary hcnt
  have hin : Lib.CPTs (fun x => pairB (pairB (pairB (env x) (un (cnt x).length))
      (pairB (un (cnt x).length) [])) (un (cnt x).length)) :=
    cpt_pairB2 (cpt_pairB2 (cpt_pairB2 henv hC) (cpt_pairB2 hC (cpt_const []))) hC
  have hout := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_comp hin hI))
  refine cptE hout (fun x => ?_)
  simp only [unpairB_pairB]
  rw [show (un (cnt x).length).length = (cnt x).length by simp [un],
    loopG_iter blk (env x) (cnt x).length _ le_rfl]
  simp only [unpairB_pairB]
structure LitT where
  pol : Bool
  pre : List ℕ
  ex : ℕ
  post : List ℕ
def LitT.lit (lt : LitT) (i : ℕ) : Literal := (uvar (lt.pre ++ (i + lt.ex) :: lt.post), lt.pol)
def lblk (lt : LitT) (s : List Bool) : List Bool :=
  lpre lt.pol lt.pre ++ (U (unpairB s).1.length ++ (U (unpairB s).2.length ++
    (U lt.ex ++ lpost lt.post)))
def tblk (tm : List LitT) (s : List Bool) : List Bool :=
  (tm.flatMap fun lt => lblk lt s) ++ [false, false]
theorem cpt_tblk (tm : List LitT) : Lib.CPTs (tblk tm) := by
  have h : ∀ lt : LitT, Lib.CPTs (lblk lt) := fun lt =>
    cpt_app2 (cpt_const _) (cpt_app2 (cpt_U cpt_unpairB1)
      (cpt_app2 (cpt_U cpt_unpairB2) (cpt_const _)))
  exact cpt_app2 (cpt_flatMap_const tm lblk h) (cpt_const _)
theorem tblk_length (tm : List LitT) : ∃ a, ∀ s, (tblk tm s).length ≤ a * s.length + a := by
  have h : ∃ a, ∀ s, (tm.flatMap fun lt => lblk lt s).length ≤ a * s.length + a := by
    induction tm with
    | nil => exact ⟨0, fun s => by simp⟩
    | cons lt tm ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + ((lpre lt.pol lt.pre).length + 2 * lt.ex + (lpost lt.post).length + 2),
        fun s => ?_⟩
      have h1 := ha s
      have h2 := unpairB_length s
      have h3 : 2 * s.length ≤
          ((lpre lt.pol lt.pre).length + 2 * lt.ex + (lpost lt.post).length + 2) * s.length :=
        Nat.mul_le_mul_right _ (by omega)
      have h4 : (lblk lt s).length = (lpre lt.pol lt.pre).length +
          (2 * (unpairB s).1.length + (2 * (unpairB s).2.length +
            (2 * lt.ex + (lpost lt.post).length))) := by
        simp only [lblk, List.length_append, U_length]
      simp only [List.flatMap_cons, List.length_append]
      rw [Nat.add_mul]
      omega
  obtain ⟨a, ha⟩ := h
  refine ⟨a + 2, fun s => ?_⟩
  have h1 := ha s
  simp only [tblk, List.length_append, List.length_cons, List.length_nil]
  rw [Nat.add_mul]
  omega
theorem tblk_spec (tm : List LitT) (e : List Bool) (j : ℕ) :
    tblk tm (pairB e (un j)) = encodeClause (tm.map fun lt => lt.lit (e.length + j)) := by
  have h : ∀ lt : LitT, lblk lt (pairB e (un j)) = encodeLiteral (lt.lit (e.length + j)) := by
    intro lt
    simp only [lblk, LitT.lit, unpairB_pairB, encodeLiteral_split, U_add, un,
      List.length_replicate, List.append_assoc]
  simp only [tblk, encodeClause]
  congr 1
  induction tm with
  | nil => rfl
  | cons lt tm ih => rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih, h]
theorem cpt_tmplLoop (tm : List LitT) {off cnt : List Bool → List Bool} (hoff : Lib.CPTs off)
    (hcnt : Lib.CPTs cnt) :
    Lib.CPTs (fun x => encodeCNF ((List.range (cnt x).length).map fun j =>
      tm.map fun lt => lt.lit ((off x).length + j))) := by
  obtain ⟨a, ha⟩ := tblk_length tm
  refine cptE (cpt_loop (cpt_tblk tm) a ha hoff hcnt) (fun x => ?_)
  rw [encodeCNF_map]
  exact flatMap_congr_mem _ _ _ (fun j _ => tblk_spec tm (off x) j)
def iblk (A0 A1 Bc : List Bool) (s : List Bool) : List Bool :=
  sel (hd ((fun l : List Bool => l.tail)^[(unpairB s).2.length] (unpairB s).1)) A0 A1 ++
    (U (unpairB s).2.length ++ Bc)
theorem cpt_iblk (A0 A1 Bc : List Bool) : Lib.CPTs (iblk A0 A1 Bc) := by
  have h1 : Lib.CPTs (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : Lib.CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have hJ := cpt_iterLen cpt_tail (fun s => by simp) h2 h1
  exact cpt_app2 (cpt_sel (cpt_hd1 hJ) (cpt_const A0) (cpt_const A1))
    (cpt_app2 (cpt_U h2) (cpt_const Bc))
theorem iblk_length (A0 A1 Bc : List Bool) (s : List Bool) :
    (iblk A0 A1 Bc s).length ≤
      (A0.length + A1.length + Bc.length + 2) * s.length +
        (A0.length + A1.length + Bc.length + 2) := by
  have h1 := unpairB_length s
  have h2 := sel_length (hd ((fun l : List Bool => l.tail)^[(unpairB s).2.length] (unpairB s).1))
    A0 A1 (A0.length + A1.length) (by omega) (by omega)
  have h3 : 2 * s.length ≤ (A0.length + A1.length + Bc.length + 2) * s.length :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [iblk, List.length_append, U_length]
  omega
theorem sel_hd_drop (A0 A1 : List Bool) (x : List Bool) :
    ∀ j, j < x.length → sel (hd (x.drop j)) A0 A1 = if x.getD j false then A1 else A0 := by
  induction x with
  | nil => intro j hj; simp at hj
  | cons b x ih =>
    intro j hj
    cases j with
    | zero => cases b <;> simp [hd, sel]
    | succ j =>
      have := ih j (by simpa using hj)
      simpa using this
theorem getD_map_sym (x : List Bool) :
    ∀ j, (x.map fun b => cond b 1 0).getD j 0 = cond (x.getD j false) 1 0 := by
  induction x with
  | nil => intro j; simp
  | cons b x ih =>
    intro j
    cases j with
    | zero => simp
    | succ j => simpa using ih j
theorem iblk_spec (k : ℕ) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    iblk (lpre true [2, k, 1]) (lpre true [2, k, 2]) (lpost [0] ++ [false, false])
        (pairB x (un j)) =
      encodeClause (imp [] (vC 0 k j ((x.map fun b => cond b 1 0).getD j 0 + 1))) := by
  have h : ∀ v, encodeClause (imp [] (vC 0 k j v)) =
      lpre true [2, k, v] ++ (U j ++ (lpost [0] ++ [false, false])) :=
    fun v => encodeClause_single true [2, k, v] j [0]
  rw [h, getD_map_sym]
  simp only [iblk, unpairB_pairB, tail_iter, un, List.length_replicate]
  rw [sel_hd_drop _ _ x j hj]
  cases x.getD j false <;> rfl
theorem cpt_inputLoop (k : ℕ) :
    Lib.CPTs (fun x => encodeCNF ((List.range x.length).map fun j =>
      imp [] (vC 0 k j ((x.map fun b => cond b 1 0).getD j 0 + 1)))) := by
  refine cptE (cpt_loop (cpt_iblk _ _ _) _ (iblk_length (lpre true [2, k, 1])
    (lpre true [2, k, 2]) (lpost [0] ++ [false, false])) cpt_id cpt_id) (fun x => ?_)
  rw [encodeCNF_map]
  exact flatMap_congr_mem _ _ _ (fun j hj => iblk_spec k x j (List.mem_range.1 hj))
theorem cpt_unitLast (pol : Bool) (pre : List ℕ) {t : List Bool → List Bool} (ht : Lib.CPTs t) :
    Lib.CPTs (fun x => encodeCNF [[(uvar (pre ++ [(t x).length]), pol)]]) := by
  refine cptE (cpt_app2 (cpt_const (lpre pol pre))
    (cpt_app2 (cpt_U ht) (cpt_const (lpost [] ++ [false, false])))) (fun x => ?_)
  have h := encodeClause_single pol pre (t x).length []
  simp only [encodeCNF, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact h.symm
end Edge
open PEqualNP.Library Lib.Machines Lib.Universal PEqualNP.Search in
theorem cpt_initPart (c : Lib.Universal.Code) (p q : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        (initClauses c (x.map (fun b => cond b 1 0)) (p.eval x.length)
          (cellsOf x.length (p.eval x.length) (q.eval x.length)))) := by
  have hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) := L055 p
  have hH : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate
        (cellsOf x.length (p.eval x.length) (q.eval x.length)) true) :=
    Edge.cptE (L055 (Polynomial.X + p + q + Polynomial.C 2)) (fun x => by simp [cellsOf])
  have hnil : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => ([] : List Bool)) := cpt_const []
  have hblank : ∀ (k : ℕ) {off : List Bool → List Bool},
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) off →
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => encodeCNF
          ((List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
            imp [] (vC 0 k ((off x).length + j) 0))) := by
    intro k off hoff
    refine Edge.cptE (Edge.cpt_tmplLoop [⟨true, [2, k, 0], 0, [0]⟩] hoff hH) (fun x => ?_)
    simp only [List.length_replicate]
    rfl
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => encodeCNF [imp [] (vP 0 (c.pc₀ + 1)), imp [] (vQ 0 c.state₀)]) :=
    cpt_const _
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF ((List.range c.nstk).flatMap fun k =>
        if k = c.kin then []
        else (List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
          imp [] (vC 0 k j 0))) := by
    refine Edge.cpt_encFlatMap_const (List.range c.nstk) _ (fun k => ?_)
    by_cases hk : k = c.kin
    · simp only [eq_true hk, ↓reduceIte]
      exact cpt_const _
    · simp only [eq_false hk, ↓reduceIte]
      exact Edge.cptE (hblank k hnil) (fun x => by simp)
  have hC : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF (if c.kin < c.nstk then
        ((List.range x.length).map fun j =>
          imp [] (vC 0 c.kin j ((x.map fun b => cond b 1 0).getD j 0 + 1)))
        ++ ((List.range (p.eval x.length)).map fun j =>
          [(vC 0 c.kin (x.length + j) 0, true), (vC 0 c.kin (x.length + j) 3, true),
            (vC 0 c.kin (x.length + j) 4, true)])
        ++ ((List.range (p.eval x.length - 1)).map fun j =>
          imp [vC 0 c.kin (x.length + j) 0] (vC 0 c.kin (x.length + (j + 1)) 0))
        ++ ((List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
          imp [] (vC 0 c.kin (x.length + p.eval x.length + j) 0))
      else [])) := by
    by_cases hk : c.kin < c.nstk
    · simp only [eq_true hk, ↓reduceIte, Edge.encodeCNF_append]
      have h1 := Edge.cpt_inputLoop c.kin
      have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (p.eval x.length)).map fun j =>
            [(vC 0 c.kin (x.length + j) 0, true), (vC 0 c.kin (x.length + j) 3, true),
              (vC 0 c.kin (x.length + j) 4, true)])) := by
        refine Edge.cptE (Edge.cpt_tmplLoop [⟨true, [2, c.kin, 0], 0, [0]⟩,
          ⟨true, [2, c.kin, 3], 0, [0]⟩, ⟨true, [2, c.kin, 4], 0, [0]⟩] cpt_id hm) (fun x => ?_)
        simp only [List.length_replicate]
        rfl
      have h3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (p.eval x.length - 1)).map fun j =>
            imp [vC 0 c.kin (x.length + j) 0] (vC 0 c.kin (x.length + (j + 1)) 0))) := by
        refine Edge.cptE (Edge.cpt_tmplLoop [⟨false, [2, c.kin, 0], 0, [0]⟩,
          ⟨true, [2, c.kin, 0], 1, [0]⟩] cpt_id (cpt_tail1 hm)) (fun x => ?_)
        simp only [List.length_tail, List.length_replicate]
        rfl
      have h4 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF
            ((List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
              imp [] (vC 0 c.kin (x.length + p.eval x.length + j) 0))) :=
        Edge.cptE (hblank c.kin (cpt_app2 cpt_id hm)) (fun x => by simp)
      exact cpt_app2 (cpt_app2 (cpt_app2 h1 h2) h3) h4
    · simp only [eq_false hk, ↓reduceIte]
      exact cpt_const _
  refine Edge.cptE (cpt_app2 (cpt_app2 hA hB) hC) (fun x => ?_)
  simp only [initClauses, Edge.encodeCNF_append, List.length_map]
open PEqualNP.Library Lib.Machines Lib.Universal PEqualNP.Search in
theorem cpt_finalPart (c : Lib.Universal.Code) (q : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF (finalClauses c (bound c) (q.eval x.length))) := by
  have hT : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (q.eval x.length) true) := L055 q
  have hunit : ∀ (pol : Bool) (pre : List ℕ),
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => encodeCNF [[(uvar (pre ++ [q.eval x.length]), pol)]]) :=
    fun pol pre => Edge.cptE (Edge.cpt_unitLast pol pre hT) (fun x => by simp)
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF
        ((List.range (bound c)).map fun p => [(vP (q.eval x.length) (p + 1), false)])) :=
    Edge.cpt_encMap_const _ _ (fun p => hunit false [0, p + 1])
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF (if c.kout < c.nstk then
        [[(vC (q.eval x.length) c.kout 0 0, false)]]
        ++ ((List.range (bound c)).flatMap fun v =>
          if v = 1 then [] else [[(vC (q.eval x.length) c.kout 0 (v + 1), false)]])
        ++ ((List.range (bound c)).map fun v => [(vC (q.eval x.length) c.kout 1 (v + 1), false)])
      else [[]])) := by
    by_cases hk : c.kout < c.nstk
    · simp only [eq_true hk, ↓reduceIte, Edge.encodeCNF_append]
      have h1 := hunit false [2, c.kout, 0, 0]
      have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (bound c)).flatMap fun v =>
            if v = 1 then [] else [[(vC (q.eval x.length) c.kout 0 (v + 1), false)]])) := by
        refine Edge.cpt_encFlatMap_const _ _ (fun v => ?_)
        by_cases hv : v = 1
        · simp only [eq_true hv, ↓reduceIte]
          exact cpt_const _
        · simp only [eq_false hv, ↓reduceIte]
          exact hunit false [2, c.kout, v + 1, 0]
      have h3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (bound c)).map fun v =>
            [(vC (q.eval x.length) c.kout 1 (v + 1), false)])) :=
        Edge.cpt_encMap_const _ _ (fun v => hunit false [2, c.kout, v + 1, 1])
      exact cpt_app2 (cpt_app2 h1 h2) h3
    · simp only [eq_false hk, ↓reduceIte]
      exact cpt_const _
  refine Edge.cptE (cpt_app2 hA hB) (fun x => ?_)
  simp only [finalClauses, Edge.encodeCNF_append]
open PEqualNP.Library Lib.Machines Lib.Universal PEqualNP.Search in
theorem cpt_tableau_of (c : Lib.Universal.Code) (p q : Polynomial ℕ)
    (hstep : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        ((List.range (q.eval x.length)).flatMap fun t =>
          stepClauses c.nstk (cellsOf x.length (p.eval x.length) (q.eval x.length))
            (bound c) c.prog t))) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        (tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length))) := by
  refine Edge.cptE (cpt_app2 (cpt_app2 (cpt_initPart c p q) hstep) (cpt_finalPart c q))
    (fun x => ?_)
  simp only [tableau, Edge.encodeCNF_append, List.length_map]
end Lib.SearchHelpers.Tab
end
section
namespace Lib.SearchHelpers.Tab
open PEqualNP.Library Lib.Universal PEqualNP.Search
theorem map_symIn_encodePair (x w : List Bool) :
    (encodePair (x, w)).map symIn =
      x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2) := by
  simp only [encodePair, List.map_append, List.map_map]
  congr 1 <;> (apply List.map_congr_left; intro b _; cases b <;> rfl)
theorem npHard_SAT : PEqualNP.Library.NPHard PEqualNP.Search.SAT := by
  intro L' hL'
  obtain ⟨R, p, ⟨fR, hfR, ⟨cR⟩⟩, hL⟩ := hL'
  obtain ⟨c, d, hc⟩ := compile cR.tm cR.inputAlphabet cR.outputAlphabet
  have hrun : ∀ x w : List Bool, ∃ n, n ≤ cR.time.eval (x.length + w.length) ∧
      c.outputsWithin (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2))
        (d * n + d) [bitCode (fR (x, w))] := by
    intro x w
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cR.time.eval (encodePair (x, w)).length ∧
        (flip bind (Turing.TM2.step cR.tm.m))^[n]
          (some (Turing.initList cR.tm ((encodePair (x, w)).map cR.inputAlphabet.invFun))) =
        some (Turing.haltList cR.tm [cR.outputAlphabet.invFun (fR (x, w))]) :=
      ⟨(cR.outputsFun (x, w)).steps, (cR.outputsFun (x, w)).steps_le_m,
        (cR.outputsFun (x, w)).evals_in_steps⟩
    have h := hc (encodePair (x, w)) (fR (x, w)) n hev
    rw [map_symIn_encodePair] at h
    refine ⟨n, ?_, h⟩
    simpa [encodePair] using hn
  let q : Polynomial ℕ :=
    p + Polynomial.C d * cR.time.comp (Polynomial.X + p) + Polynomial.C d
  have hq : ∀ n : ℕ, q.eval n = p.eval n + d * cR.time.eval (n + p.eval n) + d := by
    intro n; simp [q, Polynomial.eval_comp]
  have hzs : ∀ x : List Bool, ∀ z ∈ x.map (fun b => cond b 1 0), z < 4 := by
    intro x z hz
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
    cases b <;> simp
  refine ⟨fun x => encodeCNF
    (tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length)),
    cpt_tableau_of c p q (cpt_stepPart c p q), fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨w, hwl, hw⟩ := (hL x).1 hx
    refine ⟨_, rfl, sat_of_accepts c _ _ _ (hzs x) w hwl ?_⟩
    obtain ⟨n, hn, ho⟩ := hrun x w
    have hfw : fR (x, w) = true := (hfR (x, w)).1 hw
    rw [hfw] at ho
    have hle : d * n + d ≤ q.eval x.length := by
      rw [hq]
      have h1 : n ≤ cR.time.eval (x.length + p.eval x.length) :=
        hn.trans (Lib.Machines.eval_mono _ (by omega))
      have h2 : d * n ≤ d * cR.time.eval (x.length + p.eval x.length) :=
        Nat.mul_le_mul_left d h1
      omega
    exact Code.outputsWithin_mono c _ hle _ ho
  · rintro ⟨φ, hφ, hsat⟩
    have hφ' : φ = tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length) :=
      Lib.SearchHelpers.encodeCNF_injective hφ
    rw [hφ'] at hsat
    obtain ⟨w, hwl, ho⟩ := accepts_of_sat c _ _ _ (hzs x) hsat
    obtain ⟨n, -, ho'⟩ := hrun x w
    have h1 := Code.outputsWithin_mono c _ (le_max_left (q.eval x.length) (d * n + d)) _ ho
    have h2 := Code.outputsWithin_mono c _ (le_max_right (q.eval x.length) (d * n + d)) _ ho'
    have heq : [1] = [bitCode (fR (x, w))] := h1.2.symm.trans h2.2
    have hfw : fR (x, w) = true := by
      cases hb : fR (x, w) with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    exact (hL x).2 ⟨w, hwl, (hfR (x, w)).2 hfw⟩
end Lib.SearchHelpers.Tab
end
section
namespace Lib.SearchHelpers.SatV
open PEqualNP.Search Lib.Universal Lib.Machines Lib.SearchHelpers
def headI : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | true :: d :: r => true :: d :: headI r
  | false :: d :: _ => [false, d]
def dropI : List Bool → List Bool
  | [] => []
  | [_] => []
  | true :: _ :: r => dropI r
  | false :: _ :: r => r
def polB : List Bool → Bool
  | _ :: b :: _ => b
  | _ => false
def isEnd : List Bool → Bool
  | false :: false :: _ => true
  | _ => false
def vcode (i : ℕ) : List Bool := (i.bits.flatMap fun d => [true, d]) ++ [false, true]
inductive WS : Type
  | a | b | c | d | abT | abF | cT | cF | dead
  deriving DecidableEq
instance : Fintype WS :=
  ⟨{.a, .b, .c, .d, .abT, .abF, .cT, .cF, .dead}, fun q => by cases q <;> simp⟩
def wfD : WS → Bool → WS
  | .a, true => .abT
  | .a, false => .abF
  | .b, true => .abT
  | .b, false => .abF
  | .abT, _ => .c
  | .abF, false => .a
  | .abF, true => .dead
  | .c, true => .cT
  | .c, false => .cF
  | .d, true => .cT
  | .d, false => .dead
  | .cT, true => .c
  | .cT, false => .d
  | .cF, true => .b
  | .cF, false => .dead
  | .dead, _ => .dead
def wfB (x : List Bool) : Bool := decide (x.foldl wfD .a = .a)
theorem headI_dropI : ∀ s : List Bool, headI s ++ dropI s = s
  | [] => rfl
  | [_] => rfl
  | true :: d :: r => by simp [headI, dropI, headI_dropI r]
  | false :: d :: r => by simp [headI, dropI]
theorem dropI_length (s : List Bool) : (dropI s).length ≤ s.length := by
  have h := congrArg List.length (headI_dropI s)
  simp only [List.length_append] at h; omega
theorem headI_digits (ds : List Bool) (b : Bool) (r : List Bool) :
    headI ((ds.flatMap fun d => [true, d]) ++ false :: b :: r) =
      (ds.flatMap fun d => [true, d]) ++ [false, b] := by
  induction ds with
  | nil => simp [headI]
  | cons d ds ih => simpa [headI] using ih
theorem dropI_digits (ds : List Bool) (b : Bool) (r : List Bool) :
    dropI ((ds.flatMap fun d => [true, d]) ++ false :: b :: r) = r := by
  induction ds with
  | nil => simp [dropI]
  | cons d ds ih => simpa [dropI] using ih
theorem headI_vcode (i : ℕ) (r : List Bool) : headI (vcode i ++ r) = vcode i := by
  simpa [vcode] using headI_digits i.bits true r
theorem dropI_vcode (i : ℕ) (r : List Bool) : dropI (vcode i ++ r) = r := by
  simpa [vcode] using dropI_digits i.bits true r
theorem encodeLiteral_eq (l : Literal) : encodeLiteral l = true :: l.2 :: vcode l.1 := by
  simp [encodeLiteral, vcode]
theorem headI_lit (l : Literal) (r : List Bool) :
    headI (encodeLiteral l ++ r) = encodeLiteral l := by
  simp [encodeLiteral_eq, headI, headI_vcode]
theorem dropI_lit (l : Literal) (r : List Bool) : dropI (encodeLiteral l ++ r) = r := by
  simp [encodeLiteral_eq, dropI, dropI_vcode]
theorem isEnd_lit (l : Literal) (r : List Bool) : isEnd (encodeLiteral l ++ r) = false := by
  simp [encodeLiteral_eq, isEnd]
theorem vcode_injective : Function.Injective vcode := by
  intro i j h
  have h' : (i.bits.flatMap fun d => [true, d]) ++ (false :: true :: []) =
      (j.bits.flatMap fun d => [true, d]) ++ (false :: true :: []) := h
  exact bits_injective (digits_append_inj _ _ true true [] [] h').1
theorem vcode_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    vcode (Nat.bit b n) = true :: b :: vcode n := by
  simp [vcode, Nat.bits_append_bit n b h]
theorem vcode_zero : vcode 0 = [false, true] := by simp [vcode]
theorem foldl_dead (s : List Bool) : s.foldl wfD .dead = .dead := by
  induction s with
  | nil => rfl
  | cons x s ih => simpa [wfD] using ih
theorem foldl_vcode (n : ℕ) : ∀ r : List Bool,
    (vcode n ++ r).foldl wfD .c = r.foldl wfD .b ∧
      (n ≠ 0 → (vcode n ++ r).foldl wfD .d = r.foldl wfD .b) := by
  induction n using Nat.binaryRec' with
  | zero => intro r; simp [vcode_zero, wfD]
  | bit b n h ih =>
    intro r; obtain ⟨ih1, ih2⟩ := ih r; rw [vcode_bit b n h]
    cases b
    · have hn : n ≠ 0 := fun h0 => by simpa using h h0
      simp [wfD, ih2 hn]
    · simp [wfD, ih1]
theorem foldl_lit (l : Literal) (r : List Bool) :
    (encodeLiteral l ++ r).foldl wfD .a = r.foldl wfD .b ∧
      (encodeLiteral l ++ r).foldl wfD .b = r.foldl wfD .b := by
  simp [encodeLiteral_eq, wfD, (foldl_vcode l.1 r).1]
theorem foldl_clause (c : Clause) (r : List Bool) :
    (encodeClause c ++ r).foldl wfD .a = r.foldl wfD .a ∧
      (encodeClause c ++ r).foldl wfD .b = r.foldl wfD .a := by
  induction c with
  | nil => simp [encodeClause, wfD]
  | cons l c ih =>
    have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause]
    rw [e, (foldl_lit l _).1, (foldl_lit l _).2, ih.2]; exact ⟨rfl, rfl⟩
theorem foldl_cnf (φ : CNF) : (encodeCNF φ).foldl wfD .a = .a := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
    rw [e, (foldl_clause c _).1, ih]
def Good : WS → List Bool → Prop
  | .a, s => ∃ φ : CNF, s = encodeCNF φ
  | .b, s => ∃ (c : Clause) (φ : CNF), s = encodeClause c ++ encodeCNF φ
  | .c, s => ∃ (n : ℕ) (c : Clause) (φ : CNF), s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | .d, s => ∃ (n : ℕ) (c : Clause) (φ : CNF), n ≠ 0 ∧ s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | _, _ => True
theorem enc_cons_cons (n : ℕ) (p : Bool) (c : Clause) (φ : CNF) :
    true :: p :: (vcode n ++ (encodeClause c ++ encodeCNF φ)) =
      encodeClause ((n, p) :: c) ++ encodeCNF φ := by
  simp [encodeClause, encodeLiteral_eq]
theorem good_of_accept : ∀ (s : List Bool) (q : WS), s.foldl wfD q = .a → Good q s
  | [], q, h => by cases q <;> first | trivial | exact ⟨[], rfl⟩
  | [x], q, h => by cases q <;> first | trivial | (cases x <;> simp [wfD] at h)
  | x :: y :: r, q, h => by
    have ih := good_of_accept r
    cases q
    case abT | abF | cT | cF | dead => trivial
    case a =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h; exact ⟨[] :: φ, by simp [encodeCNF, encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨((n, y) :: c) :: φ, by rw [enc_cons_cons]; simp [encodeCNF]⟩
    case b =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h; exact ⟨[], φ, by simp [encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h; exact ⟨(n, y) :: c, φ, enc_cons_cons _ _ _ _⟩
    case c =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · obtain ⟨c, φ, rfl⟩ := ih _ h; exact ⟨0, c, φ, by simp [vcode_zero]⟩
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩
    case d =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by simp [hn], by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by simp, by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩
theorem wfB_iff (x : List Bool) : wfB x = true ↔ ∃ φ : CNF, encodeCNF φ = x := by
  rw [wfB, decide_eq_true_iff]
  constructor
  · intro h; obtain ⟨φ, rfl⟩ := good_of_accept x .a h; exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩; exact foldl_cnf φ
inductive IS : Type | b | t | f | e deriving DecidableEq
instance : Fintype IS := ⟨{.b, .t, .f, .e}, fun q => by cases q <;> simp⟩
def hiD : IS → Bool → IS × Option Bool
  | .b, true => (.t, some true)
  | .b, false => (.f, some false)
  | .t, d => (.b, some d)
  | .f, d => (.e, some d)
  | .e, _ => (.e, none)
theorem hiD_e (l : List Bool) : fstRun hiD (fun _ => none) IS.e l = [] := by
  induction l with | nil => rfl | cons a l ih => simp [fstRun, hiD, ih]
theorem hiD_run : ∀ s : List Bool, fstRun hiD (fun _ => none) IS.b s = headI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, hiD, headI, hiD_run r]
  | false :: d :: r => by simp [fstRun, hiD, headI, hiD_e]
theorem cpt_headI : Lib.CPTs headI :=
  fst_polyTime _ _ _ hiD (fun _ => none) IS.b (fun s => (hiD_run s).symm)
def diD : IS → Bool → IS × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, _ => (.e, none)
  | .e, a => (.e, some a)
theorem diD_e (l : List Bool) : fstRun diD (fun _ => none) IS.e l = l := by
  induction l with | nil => rfl | cons a l ih => simp [fstRun, diD, ih]
theorem diD_run : ∀ s : List Bool, fstRun diD (fun _ => none) IS.b s = dropI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, diD, dropI, diD_run r]
  | false :: d :: r => by simp [fstRun, diD, dropI, diD_e]
theorem cpt_dropI : Lib.CPTs dropI :=
  fst_polyTime _ _ _ diD (fun _ => none) IS.b (fun s => (diD_run s).symm)
def ieD : IS → Bool → IS × Option Bool
  | .b, false => (.f, none)
  | .f, false => (.t, none)
  | .t, _ => (.t, none)
  | _, _ => (.e, none)
def ieF : IS → Option Bool | .t => some true | _ => none
theorem ieD_e (l : List Bool) : fstRun ieD ieF IS.e l = [] := by
  induction l with | nil => rfl | cons a l ih => simp [fstRun, ieD, ih]
theorem ieD_t (l : List Bool) : fstRun ieD ieF IS.t l = [true] := by
  induction l with | nil => rfl | cons a l ih => simp [fstRun, ieD, ih]
theorem ieD_run (s : List Bool) : fstRun ieD ieF IS.b s = bflag (isEnd s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp [fstRun, ieD, ieD_e, ieD_t, isEnd, bflag]
theorem cpt_isEndF : Lib.CPTs (fun s => bflag (isEnd s)) :=
  fst_polyTime _ _ _ ieD ieF IS.b (fun s => (ieD_run s).symm)
def poD : IS → Bool → IS × Option Bool
  | .b, _ => (.t, none)
  | .t, true => (.e, some true)
  | .t, false => (.e, none)
  | _, _ => (.e, none)
theorem poD_e (l : List Bool) : fstRun poD (fun _ => none) IS.e l = [] := by
  induction l with | nil => rfl | cons a l ih => simp [fstRun, poD, ih]
theorem poD_run (s : List Bool) : fstRun poD (fun _ => none) IS.b s = bflag (polB s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · rfl
  · cases b <;> simp [fstRun, poD, poD_e, polB, bflag]
theorem cpt_polF : Lib.CPTs (fun s => bflag (polB s)) :=
  fst_polyTime _ _ _ poD (fun _ => none) IS.b (fun s => (poD_run s).symm)
inductive Ph : Type | b | t | f deriving DecidableEq
instance : Fintype Ph := ⟨{.b, .t, .f}, fun q => by cases q <;> simp⟩
theorem neS_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l = [true] := by
  induction l with | nil => rfl | cons b l ih => simp [fstRun, ih]
theorem cpt_neS :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with | nil => rfl | cons b l => simp [fstRun, neS_true, Computability.encodeBool])
end Lib.SearchHelpers.SatV
end
section
open PEqualNP.Library PEqualNP.Search Lib.Machines Lib.Universal Lib.SearchHelpers Lib.SearchHelpers.SatV Lib.SearchHelpers.Tab.StepW
def header (n : ℕ) : List Bool := List.replicate n true ++ [false]
def occsAux : ℕ → CNF → List (ℕ × Literal)
  | _, [] => []
  | ci, c :: cs => c.map (fun l => (ci, l)) ++ occsAux (ci + 1) cs
def occs (φ : CNF) : List (ℕ × Literal) := occsAux 0 φ
lemma occsAux_mem_clause_lt : ∀ (ci : ℕ) (φ : CNF) (p : ℕ × Literal),
    p ∈ occsAux ci φ → ci ≤ p.1 ∧ p.1 < ci + φ.length := by
  intro ci φ
  induction φ generalizing ci with
  | nil => intro p hp; simp [occsAux] at hp
  | cons c cs ih =>
    intro p hp
    simp only [occsAux, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨l, _, rfl⟩ | hp'
    · simp
    · obtain ⟨h1, h2⟩ := ih (ci + 1) p hp'
      simp only [List.length_cons]; omega
lemma occsAux_exists_clause : ∀ (ci : ℕ) (φ : CNF) (i : ℕ) (hi : i < φ.length)
    (l : Literal), l ∈ φ[i] → (ci + i, l) ∈ occsAux ci φ := by
  intro ci φ
  induction φ generalizing ci with
  | nil => intro i hi; simp at hi
  | cons c cs ih =>
    intro i hi l hl
    cases i with
    | zero =>
      simp only [occsAux, Nat.add_zero, List.mem_append, List.mem_map]
      left; exact ⟨l, hl, rfl⟩
    | succ i' =>
      simp only [occsAux, List.mem_append]
      right
      have h' := ih (ci + 1) i' (by simpa using hi) l (by simpa using hl)
      rwa [show ci + 1 + i' = ci + (i' + 1) by omega] at h'
lemma occsAux_mem_getElem : ∀ (ci : ℕ) (φ : CNF) (k : ℕ) (l : Literal),
    (k, l) ∈ occsAux ci φ → ∃ (hk : k - ci < φ.length), ci ≤ k ∧ l ∈ φ[k - ci] := by
  intro ci φ
  induction φ generalizing ci with
  | nil => intro k l h; simp [occsAux] at h
  | cons c cs ih =>
    intro k l h
    simp only [occsAux, List.mem_append, List.mem_map] at h
    rcases h with ⟨l', hl', heq⟩ | h'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨by simp, le_rfl, by simpa using hl'⟩
    · obtain ⟨hk, hle, hmem⟩ := ih (ci + 1) k l h'
      have hsub : k - ci = (k - (ci + 1)) + 1 := by omega
      refine ⟨by simp [hsub]; omega, by omega, ?_⟩
      simpa [hsub] using hmem
def occEdge (φ : CNF) (a b : Fin (occs φ).length) : Bool :=
  decide (a.val < b.val ∧
    (((occs φ).get a).1 = ((occs φ).get b).1 ∨
      (((occs φ).get a).2.1 = ((occs φ).get b).2.1 ∧ ((occs φ).get a).2.2 ≠ ((occs φ).get b).2.2)))
def occEdges (φ : CNF) : List (Fin (occs φ).length × Fin (occs φ).length) :=
  (List.finRange (occs φ).length).flatMap fun a =>
    (List.finRange (occs φ).length).filterMap fun b =>
      if occEdge φ a b then some (a, b) else none
lemma occs_length_ge (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    φ.length ≤ (occs φ).length := by
  have haux : ∀ ci (ψ : CNF), (∀ c ∈ ψ, c ≠ []) → ψ.length ≤ (occsAux ci ψ).length := by
    intro ci ψ
    induction ψ generalizing ci with
    | nil => intro _; simp [occsAux]
    | cons c cs ih =>
      intro h
      have hc : 1 ≤ c.length := List.length_pos_of_ne_nil (h c (by simp))
      have hcs := ih (ci + 1) (fun x hx => h x (by simp [hx]))
      simp only [occsAux, List.length_append, List.length_map, List.length_cons]
      omega
  exact haux 0 φ hne
abbrev CPTs (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f
lemma cpt_ext {f g : List Bool → List Bool} (hf : CPTs f) (h : ∀ s, f s = g s) : CPTs g := by
  obtain rfl : f = g := funext h
  exact hf
def toUnary (s : List Bool) : List Bool := un s.length
lemma cpt_toUnary : CPTs toUnary := by
  refine fst_polyTime (Q := Unit) _ _ toUnary
    (fun _ _ => ((), some true)) (fun _ => none) () (fun s => ?_)
  induction s with
  | nil => rfl
  | cons _ l ih =>
    change true :: toUnary l = true :: fstRun
      (fun _ _ => ((), some true)) (fun _ => none) () l
    rw [ih]
lemma cpt_toUnary1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun s => toUnary (f s)) :=
  cpt_comp hf cpt_toUnary
def hasFalse (s : List Bool) : List Bool :=
  bflag (decide (false ∈ s))
lemma fstRun_hasFalse (q : Bool) (s : List Bool) :
    fstRun (fun (st : Bool) (b : Bool) => (st || !b, none))
      (fun st => if st then some true else none) q s =
    bflag (q || decide (false ∈ s)) := by
  induction s generalizing q with
  | nil =>
    cases q <;> rfl
  | cons b l ih =>
    simp only [fstRun, ih]
    cases q <;> cases b <;> simp [bflag]
lemma cpt_hasFalse : CPTs hasFalse :=
  fst_polyTime (Q := Bool) _ _ hasFalse
    (fun st b => (st || !b, none)) (fun st => if st then some true else none) false
    (fun s => by simpa [hasFalse] using (fstRun_hasFalse false s).symm)
lemma cpt_hasFalse1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun s => hasFalse (f s)) :=
  cpt_comp hf cpt_hasFalse
lemma header_parse_iff (s : List Bool) :
    false ∈ s ↔ s = header (hd s).length ++
      dropN s := by
  constructor
  · intro hf
    have hsplit : s.takeWhile id ++ s.dropWhile id = s := List.takeWhile_append_dropWhile
    have hdw_ne : s.dropWhile id ≠ [] := by
      intro hemp
      rw [hemp, List.append_nil] at hsplit
      have hmem : false ∈ s.takeWhile id := by rwa [hsplit]
      have := List.mem_takeWhile_imp hmem
      simp at this
    cases hdw : s.dropWhile id with
    | nil => exact (hdw_ne hdw).elim
    | cons b r =>
      have hb : b = false := by
        have hhead_dw : ∀ (l : List Bool) (x : Bool) (t : List Bool),
            l.dropWhile id = x :: t → x = false := by
          intro l
          induction l with
          | nil => intro x t h; simp at h
          | cons y ys ih =>
            intro x t h
            cases y
            · simp at h; exact h.1
            · simp at h; exact ih x t h
        exact hhead_dw s b r hdw
      subst hb
      have htw : s.takeWhile id = List.replicate (s.takeWhile id).length true := by
        apply List.eq_replicate_iff.mpr
        refine ⟨rfl, fun x hx => ?_⟩
        exact List.mem_takeWhile_imp hx
      unfold header hd dropN
      rw [hdw, List.tail_cons, ← htw, List.append_assoc, List.singleton_append, ← hdw, hsplit]
  · intro h
    rw [h]; simp [header]
lemma hd_header_append (n : ℕ) (r : List Bool) :
    hd (header n ++ r) = un n := by
  simp [hd, header, un]
lemma dropN_header_append (n : ℕ) (r : List Bool) :
    dropN (header n ++ r) = r := by
  simp [dropN, header]
def andF (a b : List Bool) : List Bool :=
  sel a [] (sel b [] [true])
def orF (a b : List Bool) : List Bool :=
  sel a (sel b [] [true]) [true]
def notF (a : List Bool) : List Bool :=
  sel a [true] []
def xorF (a b : List Bool) : List Bool :=
  sel a
    (sel b [] [true])
    (sel b [true] [])
def eqF (a b : List Bool) : List Bool :=
  bflag (decide (a = b))
def leU (u v : List Bool) : List Bool :=
  eqF (tk u v) u
def ltU (u v : List Bool) : List Bool := leU (true :: u) v
def dropK (k s : List Bool) : List Bool := List.tail^[k.length] s
def getBit (idx bits : List Bool) : List Bool :=
  hd
    (tk [true] (dropK idx bits))
def parityRun : Bool → List Bool → Bool
  | q, [] => q
  | q, b :: l => parityRun (xor q b) l
def parityF (s : List Bool) : List Bool :=
  bflag (parityRun false s)
lemma andF_bflag (a b : Bool) :
    andF (bflag a)
         (bflag b) =
    bflag (a && b) := by
  cases a <;> cases b <;> rfl
lemma orF_bflag (a b : Bool) :
    orF (bflag a)
        (bflag b) =
    bflag (a || b) := by
  cases a <;> cases b <;> rfl
lemma notF_bflag (a : Bool) :
    notF (bflag a) =
    bflag (!a) := by
  cases a <;> rfl
lemma xorF_bflag (a b : Bool) :
    xorF (bflag a)
         (bflag b) =
    bflag (xor a b) := by
  cases a <;> cases b <;> rfl
lemma leU_un (a b : ℕ) :
    leU (un a) (un b) =
    bflag (decide (a ≤ b)) := by
  unfold leU eqF
  rw [tk_eq, un_length]
  simp only [un, List.take_replicate]
  congr 1
  simp only [decide_eq_decide]
  constructor
  · intro h
    have := congrArg List.length h
    simp at this
    omega
  · intro h
    rw [Nat.min_eq_left h]
lemma ltU_un (a b : ℕ) :
    ltU (un a) (un b) =
    bflag (decide (a < b)) := by
  unfold ltU
  rw [← un_succ, leU_un]
  congr 1
lemma tail_iter_eq_drop (k : ℕ) (s : List Bool) : List.tail^[k] s = s.drop k := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases s with
    | nil => simp
    | cons a l => simp
lemma dropK_eq (k s : List Bool) : dropK k s = s.drop k.length := tail_iter_eq_drop k.length s
lemma getBit_eq (idx bits : List Bool) :
    getBit idx bits = bflag (bits.getD idx.length false) := by
  unfold getBit
  rw [tk_eq, dropK_eq]
  simp only [List.length_singleton]
  by_cases h : idx.length < bits.length
  · have hdrop : bits.drop idx.length = bits[idx.length] :: bits.drop (idx.length + 1) :=
      List.drop_eq_getElem_cons h
    rw [hdrop, List.take_succ_cons, List.take_zero]
    rw [List.getD_eq_getElem _ _ h]
    cases bits[idx.length] <;> rfl
  · have hge : bits.length ≤ idx.length := Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le hge, List.take_nil, List.getD_eq_default _ _ hge]
    rfl
lemma cpt_andF {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => andF (u s) (v s)) :=
  cpt_sel hu (cpt_const [])
    (cpt_sel hv (cpt_const [])
      (cpt_const [true]))
lemma cpt_orF {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => orF (u s) (v s)) :=
  cpt_sel hu
    (cpt_sel hv (cpt_const [])
      (cpt_const [true]))
    (cpt_const [true])
lemma cpt_notF {u : List Bool → List Bool} (hu : CPTs u) : CPTs (fun s => notF (u s)) :=
  cpt_sel hu (cpt_const [true])
    (cpt_const [])
lemma cpt_xorF {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => xorF (u s) (v s)) :=
  cpt_sel hu
    (cpt_sel hv (cpt_const [])
      (cpt_const [true]))
    (cpt_sel hv (cpt_const [true])
      (cpt_const []))
def headTrueF (s : List Bool) : List Bool :=
  Lib.Machines.fstRun (fun (q : Bool) (b : Bool) => (true, if !q && b then some true else none))
    (fun _ => none) false s
def headFalseF (s : List Bool) : List Bool :=
  Lib.Machines.fstRun (fun (q : Bool) (b : Bool) => (true, if !q && !b then some true else none))
    (fun _ => none) false s
lemma fstRun_headTrue_true (l : List Bool) :
    Lib.Machines.fstRun (fun (q : Bool) (b : Bool) => (true, if !q && b then some true else none))
      (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => dsimp only [Lib.Machines.fstRun]; exact ih
lemma fstRun_headFalse_true (l : List Bool) :
    Lib.Machines.fstRun (fun (q : Bool) (b : Bool) => (true, if !q && !b then some true else none))
      (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => dsimp only [Lib.Machines.fstRun]; exact ih
lemma headTrueF_eq (s : List Bool) : headTrueF s = bflag (decide (s.head? = some true)) := by
  cases s with
  | nil => rfl
  | cons b l =>
    cases b
    · dsimp only [headTrueF, Lib.Machines.fstRun, bflag]; exact fstRun_headTrue_true l
    · dsimp only [headTrueF, Lib.Machines.fstRun, bflag]; exact congrArg (true :: ·) (fstRun_headTrue_true l)
lemma headFalseF_eq (s : List Bool) : headFalseF s = bflag (decide (s.head? = some false)) := by
  cases s with
  | nil => rfl
  | cons b l =>
    cases b
    · dsimp only [headFalseF, Lib.Machines.fstRun, bflag]; exact congrArg (true :: ·) (fstRun_headFalse_true l)
    · dsimp only [headFalseF, Lib.Machines.fstRun, bflag]; exact fstRun_headFalse_true l
lemma cpt_headTrueF : CPTs headTrueF :=
  Lib.Machines.fst_polyTime (Q := Bool) _ _ headTrueF _ _ false (fun _ => rfl)
lemma cpt_headFalseF : CPTs headFalseF :=
  Lib.Machines.fst_polyTime (Q := Bool) _ _ headFalseF _ _ false (fun _ => rfl)
def eqStep (y : List Bool) : List Bool :=
  let ab := (unpairB y).1
  let bad := (unpairB y).2
  let a := (unpairB ab).1
  let b := (unpairB ab).2
  let same := orF (andF (notF a) (notF b))
    (orF (andF (headTrueF a) (headTrueF b)) (andF (headFalseF a) (headFalseF b)))
  pairB (pairB a.tail b.tail) (sel same (true :: bad) bad)
lemma eqStep_length (y : List Bool) : (eqStep y).length ≤ y.length + 4 := by
  have h1 := unpairB_length y
  have h2 := unpairB_length (unpairB y).1
  unfold eqStep
  have hs := sel_length
    (orF (andF (notF (unpairB (unpairB y).1).1) (notF (unpairB (unpairB y).1).2))
      (orF (andF (headTrueF (unpairB (unpairB y).1).1) (headTrueF (unpairB (unpairB y).1).2))
        (andF (headFalseF (unpairB (unpairB y).1).1) (headFalseF (unpairB (unpairB y).1).2))))
    (true :: (unpairB y).2) (unpairB y).2 ((unpairB y).2.length + 1)
    (by simp) (by omega)
  have ht1 : (unpairB (unpairB y).1).1.tail.length ≤ (unpairB (unpairB y).1).1.length := by simp
  have ht2 : (unpairB (unpairB y).1).2.tail.length ≤ (unpairB (unpairB y).1).2.length := by simp
  rw [pairB_length, pairB_length]
  omega
lemma cpt_eqStep : CPTs eqStep := by
  have hab := cpt_unpairB1
  have hbad := cpt_unpairB2
  have ha := cpt_unpairB1_1 hab
  have hb := cpt_unpairB2_1 hab
  have hsame := cpt_orF (cpt_andF (cpt_notF ha) (cpt_notF hb))
    (cpt_orF (cpt_andF (cpt_comp ha cpt_headTrueF) (cpt_comp hb cpt_headTrueF))
      (cpt_andF (cpt_comp ha cpt_headFalseF) (cpt_comp hb cpt_headFalseF)))
  exact cpt_pairB2 (cpt_pairB2 (cpt_tail1 ha) (cpt_tail1 hb))
    (cpt_sel hsame (cpt_cons1 true hbad) hbad)
lemma eqStep_pair (a b bad : List Bool) :
    eqStep (pairB (pairB a b) bad) =
      pairB (pairB a.tail b.tail) (if a.head? = b.head? then bad else true :: bad) := by
  unfold eqStep
  simp only [unpairB_pairB, headTrueF_eq, headFalseF_eq]
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => cases y <;> rfl
  | cons x xs =>
    cases b with
    | nil => cases x <;> rfl
    | cons y ys => cases x <;> cases y <;> rfl
lemma eqStep_iter (k : ℕ) : ∀ a b bad : List Bool, ∃ bad' : List Bool,
    eqStep^[k] (pairB (pairB a b) bad) = pairB (pairB (a.drop k) (b.drop k)) bad' ∧
      (bad' = [] ↔ bad = [] ∧ ∀ j < k, (a.drop j).head? = (b.drop j).head?) := by
  induction k with
  | zero => intro a b bad; exact ⟨bad, rfl, by simp⟩
  | succ k ih =>
    intro a b bad
    obtain ⟨bad', h1, h2⟩ := ih a.tail b.tail (if a.head? = b.head? then bad else true :: bad)
    have hd1 : a.tail.drop k = a.drop (k + 1) := by cases a <;> simp
    have hd2 : b.tail.drop k = b.drop (k + 1) := by cases b <;> simp
    refine ⟨bad', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, eqStep_pair, h1, hd1, hd2]
    · rw [h2]
      have hiff : (if a.head? = b.head? then bad else true :: bad) = [] ↔ bad = [] ∧ a.head? = b.head? := by
        split_ifs with h <;> simp [h]
      rw [hiff]
      constructor
      · rintro ⟨⟨hb, h0⟩, hrest⟩
        refine ⟨hb, fun j hj => ?_⟩
        cases j with
        | zero => simpa using h0
        | succ j' =>
          have h' := hrest j' (by omega)
          have ha : a.tail.drop j' = a.drop (j' + 1) := by cases a <;> simp
          have hb' : b.tail.drop j' = b.drop (j' + 1) := by cases b <;> simp
          rwa [ha, hb'] at h'
      · rintro ⟨hb, hall⟩
        refine ⟨⟨hb, by simpa using hall 0 (by omega)⟩, fun j hj => ?_⟩
        have h' := hall (j + 1) (by omega)
        have ha : a.tail.drop j = a.drop (j + 1) := by cases a <;> simp
        have hb' : b.tail.drop j = b.drop (j + 1) := by cases b <;> simp
        rwa [ha, hb']
lemma list_eq_of_drop_head (a b : List Bool)
    (h : ∀ j < (a ++ b).length + 1, (a.drop j).head? = (b.drop j).head?) : a = b := by
  induction a generalizing b with
  | nil =>
    have h0 := h 0 (by simp)
    cases b with | nil => rfl | cons y ys => simp at h0
  | cons x xs ih =>
    have h0 := h 0 (by simp)
    cases b with
    | nil => simp at h0
    | cons y ys =>
      simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h0
      subst h0
      congr 1
      apply ih ys
      intro j hj
      have := h (j + 1) (by simp at hj ⊢; omega)
      simpa using this
lemma cpt_eqF' {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => eqF (u s) (v s)) := by
  have hit := cpt_iterGrow cpt_eqStep 4 eqStep_length
    (cpt_cons1 true (cpt_app2 hu hv))
    (cpt_pairB2 (cpt_pairB2 hu hv) (cpt_const []))
  refine cpt_ext (cpt_notF (cpt_unpairB2_1 hit)) (fun s => ?_)
  obtain ⟨bad', h1, h2⟩ := eqStep_iter (true :: (u s ++ v s)).length (u s) (v s) []
  rw [h1, unpairB_pairB]
  unfold notF sel eqF bflag
  by_cases hbad : bad' = []
  · simp only [hbad, ↓reduceIte]
    have hall := (h2.mp hbad).2
    have heq : u s = v s := list_eq_of_drop_head (u s) (v s) (by simpa using hall)
    simp [heq]
  · simp only [hbad, ↓reduceIte]
    have hne : u s ≠ v s := by
      intro heq; apply hbad; rw [h2]; exact ⟨rfl, fun j _ => by rw [heq]⟩
    simp [hne]
lemma cpt_leU {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => leU (u s) (v s)) :=
  cpt_eqF' (cpt_tk hu hv) hu
lemma cpt_ltU {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => ltU (u s) (v s)) :=
  cpt_leU (cpt_cons1 true hu) hv
lemma cpt_dropK {k u : List Bool → List Bool} (hk : CPTs k) (hu : CPTs u) :
    CPTs (fun s => dropK (k s) (u s)) :=
  cpt_iterLen cpt_tail
    (fun s => by cases s <;> simp) hk hu
lemma cpt_getBit {idx bits : List Bool → List Bool} (hi : CPTs idx) (hb : CPTs bits) :
    CPTs (fun s => getBit (idx s) (bits s)) :=
  cpt_hd1
    (cpt_tk
      (cpt_const [true]) (cpt_dropK hi hb))
lemma fstRun_parity (q : Bool) (s : List Bool) :
    fstRun (fun (st : Bool) (b : Bool) => (xor st b, none))
      (fun st => if st then some true else none) q s =
    bflag (parityRun q s) := by
  induction s generalizing q with
  | nil => cases q <;> rfl
  | cons b l ih =>
    dsimp only [fstRun, parityRun]
    exact ih (xor q b)
lemma cpt_parityF : CPTs parityF :=
  fst_polyTime (Q := Bool) _ _ parityF
    (fun st b => (xor st b, none)) (fun st => if st then some true else none) false
    (fun s => (fstRun_parity false s).symm)
lemma cpt_parityF1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun s => parityF (f s)) :=
  cpt_comp hf cpt_parityF
lemma parityRun_append (q : Bool) (l₁ l₂ : List Bool) :
    parityRun q (l₁ ++ l₂) = parityRun (parityRun q l₁) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons b l ih => simp [parityRun, ih]
lemma parityRun_xor (q : Bool) (l : List Bool) :
    parityRun q l = xor q (parityRun false l) := by
  induction l generalizing q with
  | nil => cases q <;> rfl
  | cons b l ih =>
    simp only [parityRun]
    rw [ih (xor q b), Bool.false_xor, ih b]
    cases q <;> cases b <;> cases parityRun false l <;> rfl
lemma flatMap_range_eq_nil_iff (N : ℕ) (f : ℕ → List Bool) :
    ((List.range N).flatMap f = []) ↔ ∀ i < N, f i = [] := by
  simp only [List.flatMap_eq_nil_iff, List.mem_range]
lemma andF_true_true : andF [true] [true] = [true] := rfl
lemma notF_eq_true_of_ne_nil {a : List Bool} (h : notF a ≠ []) : notF a = [true] := by
  cases a <;> simp [notF, sel] at h ⊢
lemma andF_ne_nil_iff (a b : List Bool) :
    andF a b ≠ [] ↔ a ≠ [] ∧ b ≠ [] := by
  cases a <;> cases b <;> simp [andF, sel]
lemma andF_eq_true_iff (a b : List Bool) :
    andF a b = [true] ↔ a ≠ [] ∧ b ≠ [] := by
  cases a <;> cases b <;> simp [andF, sel]
lemma bflag_ne_nil_iff (b : Bool) :
    bflag b ≠ [] ↔ b = true := by
  cases b <;> simp [bflag]
lemma hd_eq_un_length (s : List Bool) :
    hd s =
      un (hd s).length := by
  unfold hd un
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, fun x hx => List.mem_takeWhile_imp hx⟩
lemma un_append_un (a b : ℕ) :
    un a ++ un b =
      un (a + b) := by
  unfold un
  rw [List.replicate_add]
def wfNoEmptyD : WS → Bool →
    WS
  | .a, true => .abT
  | .a, false => .dead
  | .b, true => .abT
  | .b, false => .abF
  | .abT, _ => .c
  | .abF, false => .a
  | .abF, true => .dead
  | .c, true => .cT
  | .c, false => .cF
  | .d, true => .cT
  | .d, false => .dead
  | .cT, true => .c
  | .cT, false => .d
  | .cF, true => .b
  | .cF, false => .dead
  | .dead, _ => .dead
def wfNoEmptyB (x : List Bool) : Bool := decide (x.foldl wfNoEmptyD .a = .a)
def wfNoEmptyF (x : List Bool) : List Bool := bflag (wfNoEmptyB x)
lemma fstRun_wfNoEmpty (q : WS) (x : List Bool) :
    fstRun (fun st b => (wfNoEmptyD st b, none))
      (fun st => if st = .a then some true else none) q x =
    bflag (decide (x.foldl wfNoEmptyD q = .a)) := by
  induction x generalizing q with
  | nil =>
    by_cases h : q = .a <;> simp [fstRun, bflag, h]
  | cons b l ih =>
    dsimp only [fstRun, List.foldl]
    exact ih (wfNoEmptyD q b)
lemma cpt_wfNoEmptyF : CPTs wfNoEmptyF :=
  fst_polyTime (Q := WS) _ _ wfNoEmptyF
    (fun st b => (wfNoEmptyD st b, none)) (fun st => if st = .a then some true else none) .a
    (fun x => (fstRun_wfNoEmpty .a x).symm)
lemma wfNoEmptyD_dead (s : List Bool) : s.foldl wfNoEmptyD .dead = .dead := by
  induction s with
  | nil => rfl
  | cons b l ih => simpa [List.foldl, wfNoEmptyD] using ih
lemma wfNoEmptyD_eq_wfD (q : WS) (s : List Bool)
    (hne : s.foldl wfNoEmptyD q ≠ .dead) :
    s.foldl wfNoEmptyD q = s.foldl wfD q := by
  induction s generalizing q with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl] at hne ⊢
    cases q <;> cases b
    · exfalso; rw [wfNoEmptyD, wfNoEmptyD_dead] at hne; exact hne rfl
    all_goals exact ih _ hne
lemma wfNoEmptyD_vcode (v : ℕ) :
    (vcode v).foldl wfNoEmptyD .c = .b ∧
    (v ≠ 0 → (vcode v).foldl wfNoEmptyD .d = .b) := by
  refine Nat.binaryRec ?_ (fun b n ih => ?_) v
  · simp [vcode_zero, wfNoEmptyD]
  · by_cases hbn : Nat.bit b n = 0
    · rw [hbn]; simp [vcode_zero, wfNoEmptyD]
    · have hcond : n = 0 → b = true := by
        intro hn; subst hn; cases b <;> simp at hbn ⊢
      rw [vcode_bit b n hcond]
      cases b
      · have hn0 : n ≠ 0 := fun hn => by simp [hn] at hbn
        simp [wfNoEmptyD, ih.2 hn0]
      · simp [wfNoEmptyD, ih.1]
lemma wfNoEmptyD_lit (l : Literal) :
    (encodeLiteral l).foldl wfNoEmptyD .a = .b ∧
    (encodeLiteral l).foldl wfNoEmptyD .b = .b := by
  rw [encodeLiteral_eq]
  simp [wfNoEmptyD, (wfNoEmptyD_vcode l.1).1]
lemma wfNoEmptyD_lits (ls : Clause) :
    (ls.flatMap encodeLiteral).foldl wfNoEmptyD .b = .b := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.foldl_append, (wfNoEmptyD_lit l).2, ih]
lemma wfNoEmptyD_clause (c : Clause) :
    (encodeClause c).foldl wfNoEmptyD .a = if c = [] then .dead else .a := by
  cases c with
  | nil => rfl
  | cons l ls =>
    simp only [encodeClause, List.flatMap_cons, List.append_assoc, List.foldl_append,
      (wfNoEmptyD_lit l).1, wfNoEmptyD_lits, reduceCtorEq, ↓reduceIte]
    rfl
lemma wfNoEmptyD_cnf (φ : CNF) :
    (encodeCNF φ).foldl wfNoEmptyD .a =
      if ∀ c ∈ φ, c ≠ [] then .a else .dead := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
    rw [encodeCNF, List.flatMap_cons, List.foldl_append, wfNoEmptyD_clause]
    by_cases hc : c = []
    · simp [hc, wfNoEmptyD_dead]
    · simp only [hc, ↓reduceIte, encodeCNF] at ih ⊢
      rw [ih]
      simp [hc]
lemma wfNoEmptyB_iff (x : List Bool) :
    wfNoEmptyB x = true ↔ ∃ φ : CNF,
      encodeCNF φ = x ∧ ∀ c ∈ φ, c ≠ [] := by
  unfold wfNoEmptyB
  rw [decide_eq_true_eq]
  constructor
  · intro h
    have hne : x.foldl wfNoEmptyD .a ≠ .dead := by rw [h]; decide
    have hwf : wfB x = true := by
      unfold wfB
      rw [decide_eq_true_eq, ← wfNoEmptyD_eq_wfD .a x hne, h]
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp hwf
    refine ⟨φ, rfl, ?_⟩
    rw [wfNoEmptyD_cnf] at h
    by_contra hnot
    simp [hnot] at h
  · rintro ⟨φ, rfl, hne⟩
    rw [wfNoEmptyD_cnf]
    split_ifs
    rfl
def clitD : Ph → Bool →
    Ph × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, true => (.b, some true)
  | .f, false => (.b, none)
def countLits (s : List Bool) : List Bool :=
  fstRun clitD (fun _ => none) .b s
lemma cpt_countLits : CPTs countLits :=
  fst_polyTime (Q := Ph) _ _
    countLits clitD (fun _ => none) .b (fun _ => rfl)
def cclD : Ph → Bool →
    Ph × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, false => (.b, some true)
  | .f, true => (.b, none)
def countClauses (s : List Bool) : List Bool :=
  fstRun cclD (fun _ => none) .b s
lemma cpt_countClauses : CPTs countClauses :=
  fst_polyTime (Q := Ph) _ _
    countClauses cclD (fun _ => none) .b (fun _ => rfl)
lemma countLits_digits (ds r : List Bool) :
    fstRun clitD (fun _ => none) .b
      ((ds.flatMap fun d => [true, d]) ++ r) =
    fstRun clitD (fun _ => none) .b r := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      fstRun, clitD, Option.toList_none, List.nil_append, ih]
lemma countLits_lit (l : Literal) (r : List Bool) :
    fstRun clitD (fun _ => none) .b
      (encodeLiteral l ++ r) =
    true :: fstRun clitD (fun _ => none) .b r := by
  rw [encodeLiteral_eq, vcode]
  simp only [List.cons_append, List.append_assoc, fstRun, clitD]
  rw [countLits_digits]
  rfl
lemma countLits_clause (c : Clause) (r : List Bool) :
    fstRun clitD (fun _ => none) .b
      (encodeClause c ++ r) =
    un c.length ++
      fstRun clitD (fun _ => none) .b r := by
  unfold encodeClause
  induction c with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.append_assoc, List.append_assoc, countLits_lit,
      ← List.append_assoc, ih]
    simp only [List.length_cons, un, List.replicate_succ, List.cons_append]
lemma occsAux_length (ci : ℕ) (φ : CNF) :
    (occsAux ci φ).length = (φ.map List.length).sum := by
  induction φ generalizing ci with
  | nil => rfl
  | cons c cs ih =>
    simp [occsAux, ih (ci + 1)]
lemma countLits_cnf (φ : CNF) :
    countLits (encodeCNF φ) = un (occs φ).length := by
  unfold countLits occs
  rw [occsAux_length]
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [encodeCNF, List.flatMap_cons, countLits_clause,
      List.map_cons, List.sum_cons, ← un_append_un]
    congr 1
lemma countClauses_digits (ds r : List Bool) :
    fstRun cclD (fun _ => none) .b
      ((ds.flatMap fun d => [true, d]) ++ r) =
    fstRun cclD (fun _ => none) .b r := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      fstRun, cclD, Option.toList_none, List.nil_append, ih]
lemma countClauses_lit (l : Literal) (r : List Bool) :
    fstRun cclD (fun _ => none) .b
      (encodeLiteral l ++ r) =
    fstRun cclD (fun _ => none) .b r := by
  rw [encodeLiteral_eq, vcode]
  simp only [List.cons_append, List.append_assoc, fstRun, cclD]
  rw [countClauses_digits]
  rfl
lemma countClauses_clause (c : Clause) (r : List Bool) :
    fstRun cclD (fun _ => none) .b
      (encodeClause c ++ r) =
    true :: fstRun cclD (fun _ => none) .b r := by
  unfold encodeClause
  induction c with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.append_assoc, List.append_assoc, countClauses_lit,
      ← List.append_assoc, ih]
lemma countClauses_cnf (φ : CNF) :
    countClauses (encodeCNF φ) = un φ.length := by
  unfold countClauses
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [encodeCNF, List.flatMap_cons, countClauses_clause,
      List.length_cons, un, List.replicate_succ]
    congr 1
def stepOcc (y : List Bool) : List Bool :=
  let r1 := dropI (unpairB y).1
  let cl := (unpairB y).2
  sel
    (bflag (isEnd r1))
    (pairB r1 cl)
    (pairB (dropI r1) (true :: cl))
lemma stepOcc_length (y : List Bool) : (stepOcc y).length ≤ y.length + 2 := by
  have h1 := unpairB_length y
  have h2 := dropI_length (unpairB y).1
  have h3 := dropI_length
    (dropI (unpairB y).1)
  unfold stepOcc
  apply sel_length
  · rw [pairB_length]; omega
  · rw [pairB_length, List.length_cons]; omega
lemma cpt_stepOcc : CPTs stepOcc := by
  have hr := cpt_unpairB1
  have hcl := cpt_unpairB2
  have hr1 := cpt_comp hr cpt_dropI
  have hr2 := cpt_comp hr1 cpt_dropI
  have hend := cpt_comp hr1 cpt_isEndF
  exact cpt_sel hend
    (cpt_pairB2 hr1 hcl)
    (cpt_pairB2 hr2 (cpt_cons1 true hcl))
def occState (s uA : List Bool) : List Bool :=
  stepOcc^[uA.length] (pairB s [])
lemma cpt_occState {fs fu : List Bool → List Bool} (hs : CPTs fs) (hu : CPTs fu) :
    CPTs (fun y => occState (fs y) (fu y)) :=
  cpt_iterGrow cpt_stepOcc 2 stepOcc_length hu
    (cpt_pairB2 hs (cpt_const []))
lemma stepOcc_iter_spec (a : ℕ) :
    ∀ (ci : ℕ) (c : Clause) (φ : CNF)
      (_hc : c ≠ []) (_hφ : ∀ cl ∈ φ, cl ≠ [])
      (ha : a < (c.map (fun l => (ci, l)) ++ occsAux (ci + 1) φ).length),
      let st := stepOcc^[a] (pairB
        (encodeClause c ++ encodeCNF φ)
        (un ci))
      headI (unpairB st).1 =
        encodeLiteral ((c.map (fun l => (ci, l)) ++ occsAux (ci + 1) φ)[a]'ha).2 ∧
      (unpairB st).2 =
        un ((c.map (fun l => (ci, l)) ++ occsAux (ci + 1) φ)[a]'ha).1 := by
  induction a with
  | zero =>
    intro ci c φ hc _ ha
    cases c with
    | nil => exact (hc rfl).elim
    | cons l ls =>
      simp only [Function.iterate_zero, id_eq, unpairB_pairB,
        encodeClause, List.flatMap_cons, List.append_assoc,
        headI_lit, List.map_cons, List.cons_append,
        List.getElem_cons_zero, and_self]
  | succ a ih =>
    intro ci c φ hc hφ ha
    cases c with
    | nil => exact (hc rfl).elim
    | cons l ls =>
      cases ls with
      | nil =>
        cases φ with
        | nil =>
          simp [occsAux] at ha
        | cons c' cs' =>
          have hc' : c' ≠ [] := hφ c' (by simp)
          have hcs' : ∀ cl ∈ cs', cl ≠ [] := fun cl hcl => hφ cl (by simp [hcl])
          have hstep : stepOcc (pairB
              (encodeClause [l] ++ encodeCNF (c' :: cs'))
              (un ci)) =
              pairB
                (encodeClause c' ++ encodeCNF cs')
                (un (ci + 1)) := by
            unfold stepOcc
            simp only [unpairB_pairB, encodeClause,
              List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
              dropI_lit, List.cons_append, List.nil_append,
              isEnd, bflag,
              sel, dropI,
              encodeCNF, un_succ]
            rfl
          have ha' : a < (c'.map (fun x => (ci + 1, x)) ++ occsAux (ci + 1 + 1) cs').length := by
            simp only [occsAux, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
              List.length_cons] at ha
            omega
          have hrec := ih (ci + 1) c' cs' hc' hcs' ha'
          simp only [Function.iterate_succ_apply, hstep]
          simpa [occsAux] using hrec
      | cons l' ls' =>
        have hstep : stepOcc (pairB
            (encodeClause (l :: l' :: ls') ++ encodeCNF φ)
            (un ci)) =
            pairB
              (encodeClause (l' :: ls') ++ encodeCNF φ)
              (un ci) := by
          unfold stepOcc
          simp only [unpairB_pairB, encodeClause,
            List.flatMap_cons, List.append_assoc,
            dropI_lit,
            isEnd_lit,
            bflag, sel]
          rfl
        have ha' : a < ((l' :: ls').map (fun x => (ci, x)) ++ occsAux (ci + 1) φ).length := by
          simp only [List.map_cons, List.cons_append, List.length_cons] at ha ⊢
          omega
        have hrec := ih ci (l' :: ls') φ (by simp) hφ ha'
        simp only [Function.iterate_succ_apply, hstep]
        simpa using hrec
lemma occState_spec (φ : CNF) (hne : ∀ c ∈ φ, c ≠ [])
    (a : Fin (occs φ).length) :
    headI
      (unpairB
        (occState (encodeCNF φ) (un a.val))).1 =
      encodeLiteral ((occs φ).get a).2 ∧
    (unpairB
        (occState (encodeCNF φ) (un a.val))).2 =
      un ((occs φ).get a).1 := by
  cases φ with
  | nil =>
    have := a.isLt; simp [occs, occsAux] at this
  | cons c cs =>
    have hc : c ≠ [] := hne c (by simp)
    have hcs : ∀ cl ∈ cs, cl ≠ [] := fun cl hcl => hne cl (by simp [hcl])
    have ha : a.val < (c.map (fun l => (0, l)) ++ occsAux 1 cs).length := by
      simpa [occs, occsAux] using a.isLt
    have h := stepOcc_iter_spec a.val 0 c cs hc hcs ha
    unfold occState
    rw [un_length, List.get_eq_getElem]
    exact h
def hasOccEdgeF (s uA uB : List Bool) : List Bool :=
  let stA := occState s uA
  let stB := occState s uB
  let litA := headI (unpairB stA).1
  let clA := (unpairB stA).2
  let litB := headI (unpairB stB).1
  let clB := (unpairB stB).2
  let varA := litA.tail.tail
  let varB := litB.tail.tail
  let polA := bflag (polB litA)
  let polB := bflag (polB litB)
  andF (ltU uA uB) (orF (eqF clA clB) (andF (eqF varA varB) (xorF polA polB)))
lemma cpt_hasOccEdgeF {fs fa fb : List Bool → List Bool} (hs : CPTs fs) (ha : CPTs fa) (hb : CPTs fb) :
    CPTs (fun y => hasOccEdgeF (fs y) (fa y) (fb y)) := by
  have hstA := cpt_occState hs ha
  have hstB := cpt_occState hs hb
  have hlitA := cpt_comp (cpt_unpairB1_1 hstA)
    cpt_headI
  have hclA := cpt_unpairB2_1 hstA
  have hlitB := cpt_comp (cpt_unpairB1_1 hstB)
    cpt_headI
  have hclB := cpt_unpairB2_1 hstB
  have hvarA := cpt_comp
    (cpt_comp hlitA cpt_tail)
    cpt_tail
  have hvarB := cpt_comp
    (cpt_comp hlitB cpt_tail)
    cpt_tail
  have hpolA := cpt_comp hlitA cpt_polF
  have hpolB := cpt_comp hlitB cpt_polF
  exact cpt_andF (cpt_ltU ha hb) (cpt_orF (cpt_eqF' hclA hclB)
    (cpt_andF (cpt_eqF' hvarA hvarB) (cpt_xorF hpolA hpolB)))
lemma hasOccEdgeF_spec (φ : CNF) (hne : ∀ c ∈ φ, c ≠ [])
    (a b : Fin (occs φ).length) :
    hasOccEdgeF (encodeCNF φ) (un a.val)
      (un b.val) =
    bflag (occEdge φ a b) := by
  obtain ⟨hlA, hcA⟩ := occState_spec φ hne a
  obtain ⟨hlB, hcB⟩ := occState_spec φ hne b
  unfold hasOccEdgeF
  dsimp only
  rw [hlA, hcA, hlB, hcB]
  rw [encodeLiteral_eq,
    encodeLiteral_eq]
  simp only [List.tail_cons, polB, ltU_un]
  have hcl : eqF (un ((occs φ).get a).1)
      (un ((occs φ).get b).1) =
      bflag (decide (((occs φ).get a).1 = ((occs φ).get b).1)) := by
    unfold eqF; congr 1; simp only [decide_eq_decide]
    exact ⟨un_inj, fun h => by rw [h]⟩
  have hvar : eqF (vcode ((occs φ).get a).2.1)
      (vcode ((occs φ).get b).2.1) =
      bflag (decide (((occs φ).get a).2.1 = ((occs φ).get b).2.1)) := by
    unfold eqF; congr 1; simp only [decide_eq_decide]
    exact ⟨fun h => vcode_injective h, fun h => by rw [h]⟩
  rw [hcl, hvar, xorF_bflag, andF_bflag, orF_bflag, andF_bflag]
  congr 1
lemma flatMap_range_eq_finRange {α : Type} (N : ℕ) (f : Fin N → List α) :
    (List.range N).flatMap (fun i => if h : i < N then f ⟨i, h⟩ else []) =
    (List.finRange N).flatMap f := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.finRange_succ_last, List.flatMap_append, List.flatMap_singleton]
    have hpref : (List.range N).flatMap (fun i => if h : i < N + 1 then f ⟨i, h⟩ else []) =
        (List.range N).flatMap (fun i => if h : i < N then f (Fin.castSucc ⟨i, h⟩) else []) := by
      apply List.flatMap_congr; intro i hi
      have hlt : i < N := List.mem_range.mp hi
      simp [hlt, Nat.lt_succ_of_lt hlt]
    rw [hpref, ih (fun i => f i.castSucc), List.flatMap_map]
    simp [Fin.last]
end
end PEqualNP.Outside.L_lib_896_aux

namespace PEqualNP.Outside.L_lib_896_aux.S895

def localPartner (c : Fin 3) : Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 5, 4, 7, 6],
    ![4, 5, 3, 2, 0, 1, 7, 6],
    ![6, 7, 3, 2, 5, 4, 0, 1]] c

lemma localPartner_involutive (c : Fin 3) :
    Function.Involutive (localPartner c) := by
  fin_cases c <;> intro r <;> fin_cases r <;> decide

lemma localPartner_ne (c : Fin 3) (r : Fin 8) : localPartner c r ≠ r := by
  fin_cases c <;> fin_cases r <;> decide

def localPerm (c : Fin 3) : Equiv.Perm (Fin 8) where
  toFun := localPartner c
  invFun := localPartner c
  left_inv := localPartner_involutive c
  right_inv := localPartner_involutive c

lemma localPartner_zero (c : Fin 3) :
    (localPartner c 0).val = 2 + 2*c.val := by
  fin_cases c <;> decide

lemma localPartner_one (c : Fin 3) :
    (localPartner c 1).val = 3 + 2*c.val := by
  fin_cases c <;> decide

lemma localPartner_other (c d : Fin 3) (h : c ≠ d) :
    (localPartner c ⟨2+2*d.val, by omega⟩).val = 3+2*d.val := by
  fin_cases c <;> fin_cases d <;> first | contradiction | decide

lemma local_orientation (c : Fin 3) :
    ∃ u : Fin 8, u.val ∈ ([0,2,4,6] : List Nat) ∧
      (localPartner c u).val ∈ ([0,2,4,6] : List Nat) ∧ localPartner c u ≠ u := by
  refine ⟨0, by decide, ?_, localPartner_ne c 0⟩
  fin_cases c <;> decide

lemma local_triangle (c d : Fin 3) (b : Fin 2) :
    ∃ u : Fin 8, u.val ∈ ([b.val,2+2*d.val,3+2*d.val] : List Nat) ∧
      (localPartner c u).val ∈ ([b.val,2+2*d.val,3+2*d.val] : List Nat) ∧
      localPartner c u ≠ u := by
  fin_cases c <;> fin_cases d <;> fin_cases b <;> decide

def blockPerm {n : Nat} (a : Fin n → Fin 3) : Equiv.Perm (Fin n × Fin 8) where
  toFun p := (p.1, localPartner (a p.1) p.2)
  invFun p := (p.1, localPartner (a p.1) p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact localPartner_involutive (a p.1) p.2
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact localPartner_involutive (a p.1) p.2

def coordinates (n : Nat) : Fin (n*8+1) ≃ (Fin n × Fin 8) ⊕ Fin 1 :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl (Fin 1)))

def globalPerm {n : Nat} (a : Fin n → Fin 3) : Equiv.Perm (Fin (n*8+1)) :=
  (coordinates n).trans
    ((Equiv.sumCongr (blockPerm a) (Equiv.refl (Fin 1))).trans (coordinates n).symm)

lemma globalPerm_involutive {n : Nat} (a : Fin n → Fin 3) :
    Function.Involutive (globalPerm a) := by
  intro x
  apply (coordinates n).injective
  simp only [globalPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases h : coordinates n x with
  | inl p =>
    rcases p with ⟨i,r⟩
    simp [Equiv.sumCongr_apply, blockPerm]
    exact localPartner_involutive (a i) r
  | inr p => rfl

lemma globalPerm_block {n : Nat} (a : Fin n → Fin 3) (i : Fin n) (r : Fin 8) :
    globalPerm a (Fin.castSucc (finProdFinEquiv (i,r))) =
      Fin.castSucc (finProdFinEquiv (i,localPartner (a i) r)) := by
  simp [globalPerm, coordinates, finSumFinEquiv_symm_apply_castSucc, blockPerm]
  rfl

lemma globalPerm_injective {n : Nat} :
    Function.Injective (fun a : Fin n → Fin 3 => globalPerm a) := by
  intro a b h
  funext i
  have hh := congrArg (fun P : Equiv.Perm (Fin (n*8+1)) =>
    P (Fin.castSucc (finProdFinEquiv (i,(0 : Fin 8))))) h
  rw [globalPerm_block,globalPerm_block] at hh
  have hv := congrArg Fin.val hh
  change (localPartner (a i) 0).val + 8*i.val =
    (localPartner (b i) 0).val + 8*i.val at hv
  rw [localPartner_zero,localPartner_zero] at hv
  apply Fin.ext
  omega

lemma globalPerm_last {n : Nat} (a : Fin n → Fin 3) :
    globalPerm a (Fin.last (n*8)) = Fin.last (n*8) := by
  apply (coordinates n).injective
  simp [globalPerm,coordinates,finSumFinEquiv_symm_last]

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895.Comb

abbrev Ban := (Nat × Nat) × (Nat × Nat)
def bits (w v : Nat) := (List.range w).map (fun j => v.testBit j)
def header (n : Nat) := List.replicate n true ++ [false]
def width (n : Nat) := n.log2+1
def legal (n : Nat) (B : List Ban) := 2 ≤ n ∧ ∀ e ∈ B,
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3
def pack (k : Nat) (rows : List (List Nat)) :=
  header k ++ rows.flatMap (fun row => row.flatMap (bits (width k)))
def well (k : Nat) (rows : List (List Nat)) := ∀ row ∈ rows,
  row.length = 4 ∧ row.Nodup ∧ ∀ v ∈ row, v < k

def flag (i c : Nat) := [8*i+2+2*c,8*i+3+2*c]
def block (n i : Nat) :=
  [[8*i,8*i+2,8*i+4,8*i+6]] ++ (List.range 3).flatMap (fun c =>
    (List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
      [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j])))
def emit (n : Nat) (B : List Ban) :=
  (List.range n).flatMap (block n) ++ B.map (fun e => flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2)

lemma bits_length (w v : Nat) : (bits w v).length = w := by simp [bits]
lemma header_length (n : Nat) : (header n).length = n+1 := by simp [header]
lemma flag_length (i c : Nat) : (flag i c).length = 2 := rfl

lemma flatMap_length_constant {α β : Type*} (L : List α) (F : α → List β) (r : Nat)
    (h : ∀ a ∈ L, (F a).length = r) : (L.flatMap F).length = L.length*r := by
  revert h
  induction L with
  | nil => simp
  | cons a L ih =>
    intro h
    rw [List.flatMap_cons,List.length_append,h a (by simp),ih (fun b hb => h b (by simp [hb]))]
    simp [List.length_cons,Nat.add_mul]
    omega

lemma block_length (n i : Nat) : (block n i).length = 25 := by
  have inner (c : Nat) : ((List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
      [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j]))).length = 8 := by
    rw [flatMap_length_constant (List.range 2) _ 4 (by intro b hb; simp)]
    norm_num
  unfold block
  rw [List.length_append,flatMap_length_constant (List.range 3) _ 8 (by intro c hc; exact inner c)]
  norm_num

lemma emit_length (n : Nat) (B : List Ban) : (emit n B).length = 25*n+B.length := by
  unfold emit
  rw [List.length_append,List.length_map,
    flatMap_length_constant (List.range n) (block n) 25 (by intro i hi; exact block_length n i)]
  simp only [List.length_range]
  omega

lemma block_disjoint {i j a b : Nat} (ha : a < 8) (hb : b < 8) (hij : i ≠ j) :
    8*i+a ≠ 8*j+b := by omega

lemma succ_mod_ne (n i : Nat) (hn : 2 ≤ n) (hi : i < n) : i ≠ (i+1) % n := by
  by_cases h : i+1 < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have eq : i+1 = n := by omega
    rw [eq,Nat.mod_self]
    omega

lemma orientation_well {n i : Nat} (hi : i < n) :
    ([8*i,8*i+2,8*i+4,8*i+6] : List Nat).length = 4 ∧
    ([8*i,8*i+2,8*i+4,8*i+6] : List Nat).Nodup ∧
    ∀ v ∈ ([8*i,8*i+2,8*i+4,8*i+6] : List Nat), v < 8*n+1 := by
  refine ⟨rfl,?_,?_⟩
  · simp [List.nodup_cons] <;> omega
  · intro v hv
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega

lemma triangle_well {n i c b j : Nat} (hn : 2 ≤ n) (hi : i < n)
    (hc : c < 3) (hb : b < 2) (hj : j < 4) :
    ([8*i+b] ++ flag i c ++ [8*((i+1) % n)+j]).length = 4 ∧
    ([8*i+b] ++ flag i c ++ [8*((i+1) % n)+j]).Nodup ∧
    ∀ v ∈ [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j], v < 8*n+1 := by
  have hs : (i+1) % n < n := Nat.mod_lt _ (by omega)
  have hne := succ_mod_ne n i hn hi
  have h0 := block_disjoint (i := i) (j := (i+1) % n) (a := b) (b := j) (by omega) (by omega) hne
  have h1 := block_disjoint (i := i) (j := (i+1) % n) (a := 2+2*c) (b := j) (by omega) (by omega) hne
  have h2 := block_disjoint (i := i) (j := (i+1) % n) (a := 3+2*c) (b := j) (by omega) (by omega) hne
  refine ⟨by simp [flag],?_,?_⟩
  · simp [flag,List.nodup_cons] <;> omega
  · intro v hv
    simp only [flag,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
    rcases hv with (rfl | (rfl | rfl)) | rfl <;> omega

lemma ban_well {n i j c d : Nat} (hij : i < j) (hjn : j < n) (hc : c < 3) (hd : d < 3) :
    (flag i c ++ flag j d).length = 4 ∧ (flag i c ++ flag j d).Nodup ∧
    ∀ v ∈ flag i c ++ flag j d, v < 8*n+1 := by
  refine ⟨by simp [flag],?_,?_⟩
  · simp [flag,List.nodup_cons] <;> omega
  · intro v hv
    simp only [flag,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
    rcases hv with (rfl | rfl) | (rfl | rfl) <;> omega

lemma emit_well (n : Nat) (B : List Ban) (h : legal n B) : well (8*n+1) (emit n B) := by
  intro row hrow
  simp only [emit,List.mem_append] at hrow
  rcases hrow with hrow | hrow
  · obtain ⟨i,hi,hrow⟩ := List.mem_flatMap.mp hrow
    have hin := List.mem_range.mp hi
    simp only [block,List.mem_append,List.mem_singleton] at hrow
    rcases hrow with rfl | hrow
    · exact orientation_well hin
    · obtain ⟨c,hc,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨b,hb,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hrow
      exact triangle_well h.1 hin (List.mem_range.mp hc) (List.mem_range.mp hb) (List.mem_range.mp hj)
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hrow
    obtain ⟨hij,hjn,hc,hd⟩ := h.2 e he
    exact ban_well hij hjn hc hd

lemma pack_length_of_well (k : Nat) (rows : List (List Nat)) (h : well k rows) :
    (pack k rows).length = k+1+4*rows.length*width k := by
  unfold pack
  rw [List.length_append,header_length,
    flatMap_length_constant rows (fun row => row.flatMap (bits (width k))) (4*width k) ?_]
  · ring
  · intro row hrow
    rw [flatMap_length_constant row (bits (width k)) (width k) (by intro v hv; exact bits_length _ _)]
    rw [(h row hrow).1]

lemma emit_pack_length (n : Nat) (B : List Ban) (h : legal n B) :
    (pack (8*n+1) (emit n B)).length =
      (8*n+1)+1+4*(25*n+B.length)*width (8*n+1) := by
  rw [pack_length_of_well _ _ (emit_well n B h),emit_length]
end PEqualNP.Outside.L_lib_896_aux.S895.Comb

namespace PEqualNP.Outside.L_lib_896_aux.S895.Comb
open PEqualNP.Outside.L_lib_896_aux.S895

def valid (n : Nat) (B : List Ban) (a : Fin n → Fin 3) :=
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2

def wins (k : Nat) (rows : List (List Nat)) (P : Equiv.Perm (Fin k)) :=
  Function.Involutive P ∧ ∀ row ∈ rows, ∃ u : Fin k,
    u.val ∈ row ∧ (P u).val ∈ row ∧ P u ≠ u

def coord {n : Nat} (i : Fin n) (r : Fin 8) : Fin (n*8+1) :=
  Fin.castSucc (finProdFinEquiv (i,r))
lemma coord_val {n : Nat} (i : Fin n) (r : Fin 8) :
    (coord i r).val = r.val+8*i.val := rfl
lemma globalPerm_coord {n : Nat} (a : Fin n → Fin 3) (i : Fin n) (r : Fin 8) :
    globalPerm a (coord i r) = coord i (localPartner (a i) r) := globalPerm_block a i r

def hit {n : Nat} (a : Fin n → Fin 3) (row : List Nat) :=
  ∃ u : Fin (n*8+1), u.val ∈ row ∧ (globalPerm a u).val ∈ row ∧ globalPerm a u ≠ u

lemma hit_mono {n : Nat} {a : Fin n → Fin 3} {row row' : List Nat}
    (h : hit a row) (hs : row ⊆ row') : hit a row' := by
  obtain ⟨u,hu,hpu,hne⟩ := h
  exact ⟨u,hs hu,hs hpu,hne⟩

lemma lift_local {n : Nat} (a : Fin n → Fin 3) (i : Fin n) (L row : List Nat)
    (hl : ∃ r : Fin 8, r.val ∈ L ∧ (localPartner (a i) r).val ∈ L ∧ localPartner (a i) r ≠ r)
    (hm : ∀ x ∈ L, 8*i.val+x ∈ row) : hit a row := by
  obtain ⟨r,hr,hpr,hne⟩ := hl
  refine ⟨coord i r,?_,?_,?_⟩
  · simpa only [coord_val,Nat.add_comm] using hm r.val hr
  · rw [globalPerm_coord,coord_val]
    simpa only [Nat.add_comm] using hm (localPartner (a i) r).val hpr
  · rw [globalPerm_coord]
    intro eq
    have hv := congrArg Fin.val eq
    rw [coord_val,coord_val] at hv
    exact hne (Fin.ext (by omega))

lemma orientation_hit {n i : Nat} (a : Fin n → Fin 3) (hi : i < n) :
    hit a [8*i,8*i+2,8*i+4,8*i+6] := by
  apply lift_local a ⟨i,hi⟩ [0,2,4,6] _ (local_orientation _)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

lemma triangle_hit {n i c b : Nat} (a : Fin n → Fin 3) (hi : i < n)
    (hc : c < 3) (hb : b < 2) (pad : Nat) :
    hit a ([8*i+b] ++ flag i c ++ [pad]) := by
  apply lift_local a ⟨i,hi⟩ [b,2+2*c,3+2*c] _
    (local_triangle (a ⟨i,hi⟩) ⟨c,hc⟩ ⟨b,hb⟩)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [flag,Nat.add_assoc]

lemma assignment_lookup {n : Nat} (a : Fin n → Fin 3) (i : Fin n) :
    (List.ofFn (fun j => (a j).val)).getD i.val 3 = (a i).val := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

lemma flag_hit {n i c : Nat} (a : Fin n → Fin 3) (hi : i < n) (hc : c < 3)
    (hne : (a ⟨i,hi⟩).val ≠ c) : hit a (flag i c) := by
  let ii : Fin n := ⟨i,hi⟩
  let cc : Fin 3 := ⟨c,hc⟩
  have hn : a ii ≠ cc := by
    intro h
    exact hne (congrArg Fin.val h)
  let r : Fin 8 := ⟨2+2*c,by omega⟩
  have hr : (localPartner (a ii) r).val = 3+2*c := localPartner_other (a ii) cc hn
  apply lift_local a ii [2+2*c,3+2*c] _
    ⟨r,by simp [r],by simp [hr],localPartner_ne _ _⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> simp [flag,ii,Nat.add_assoc]

lemma ban_hit {n : Nat} (B : List Ban) (hlegal : legal n B) (a : Fin n → Fin 3)
    (hvalid : valid n B a) (e : Ban) (he : e ∈ B) :
    hit a (flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2) := by
  obtain ⟨hij,hjn,hc,hd⟩ := hlegal.2 e he
  have hin : e.1.1 < n := by omega
  have hv := hvalid e he
  rw [assignment_lookup a ⟨e.1.1,hin⟩,assignment_lookup a ⟨e.2.1,hjn⟩] at hv
  rcases hv with hv | hv
  · apply hit_mono (flag_hit a hin hc hv)
    intro x hx
    exact List.mem_append.mpr (Or.inl hx)
  · apply hit_mono (flag_hit a hjn hd hv)
    intro x hx
    exact List.mem_append.mpr (Or.inr hx)

lemma globalPerm_wins {n : Nat} (B : List Ban) (hlegal : legal n B) (a : Fin n → Fin 3)
    (hvalid : valid n B a) : wins (n*8+1) (emit n B) (globalPerm a) := by
  refine ⟨globalPerm_involutive a,?_⟩
  intro row hrow
  change hit a row
  simp only [emit,List.mem_append] at hrow
  rcases hrow with hrow | hrow
  · obtain ⟨i,hi,hrow⟩ := List.mem_flatMap.mp hrow
    have hin := List.mem_range.mp hi
    simp only [block,List.mem_append,List.mem_singleton] at hrow
    rcases hrow with rfl | hrow
    · exact orientation_hit a hin
    · obtain ⟨c,hc,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨b,hb,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hrow
      exact triangle_hit a hin (List.mem_range.mp hc) (List.mem_range.mp hb) _
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hrow
    exact ban_hit B hlegal a hvalid e he

lemma forward_solution {n : Nat} (B : List Ban) (hlegal : legal n B) (a : Fin n → Fin 3)
    (hvalid : valid n B a) : ∃ P : Equiv.Perm (Fin (8*n+1)), wins (8*n+1) (emit n B) P := by
  have hh : ∃ P : Equiv.Perm (Fin (n*8+1)), wins (n*8+1) (emit n B) P :=
    ⟨globalPerm a,globalPerm_wins B hlegal a hvalid⟩
  have heq : n*8+1 = 8*n+1 := by omega
  exact heq ▸ hh
end PEqualNP.Outside.L_lib_896_aux.S895.Comb

namespace PEqualNP.Outside.L_lib_896_aux.S895.Comb
open PEqualNP.Outside.L_lib_896_aux.S895

lemma ports_miss_ban {i j c d b : Nat} (hij : i < j) (hc : c < 3) (hd : d < 3) (hb : b < 2) :
    8*i+b ∉ flag i c ++ flag j d ∧ 8*j+b ∉ flag i c ++ flag j d := by
  constructor <;> simp [flag] <;> omega

lemma not_hit_selected_flags {n : Nat} (a : Fin n → Fin 3) (i j : Fin n)
    (hij : i.val < j.val) (c d : Nat) (hc : c < 3) (hd : d < 3)
    (hci : (a i).val = c) (hdj : (a j).val = d) :
    ¬ hit a (flag i.val c ++ flag j.val d) := by
  intro ⟨u,hu,hpu,hne⟩
  simp only [flag,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with (he | ho) | (he | ho)
  · have eq : u = coord i (localPartner (a i) 0) := by
      apply Fin.ext
      rw [coord_val,localPartner_zero,hci]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 0) (by omega)).1 (by simpa using hpu)
  · have eq : u = coord i (localPartner (a i) 1) := by
      apply Fin.ext
      rw [coord_val,localPartner_one,hci]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 1) (by omega)).1 (by simpa [Nat.add_comm] using hpu)
  · have eq : u = coord j (localPartner (a j) 0) := by
      apply Fin.ext
      rw [coord_val,localPartner_zero,hdj]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 0) (by omega)).2 (by simpa using hpu)
  · have eq : u = coord j (localPartner (a j) 1) := by
      apply Fin.ext
      rw [coord_val,localPartner_one,hdj]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 1) (by omega)).2 (by simpa [Nat.add_comm] using hpu)

lemma globalPerm_valid_of_wins {n : Nat} (B : List Ban) (hlegal : legal n B)
    (a : Fin n → Fin 3) (hwins : wins (n*8+1) (emit n B) (globalPerm a)) : valid n B a := by
  intro e he
  obtain ⟨hij,hjn,hc,hd⟩ := hlegal.2 e he
  have hin : e.1.1 < n := by omega
  let i : Fin n := ⟨e.1.1,hin⟩
  let j : Fin n := ⟨e.2.1,hjn⟩
  rw [assignment_lookup a i,assignment_lookup a j]
  by_cases hci : (a i).val = e.1.2
  · by_cases hdj : (a j).val = e.2.2
    · have hr : flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2 ∈ emit n B := by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨e,he,rfl⟩)
      exact False.elim (not_hit_selected_flags a i j hij _ _ hc hd hci hdj (hwins.2 _ hr))
    · exact Or.inr hdj
  · exact Or.inl hci

lemma valid_iff_globalPerm_wins {n : Nat} (B : List Ban) (hlegal : legal n B)
    (a : Fin n → Fin 3) : valid n B a ↔ wins (n*8+1) (emit n B) (globalPerm a) :=
  ⟨globalPerm_wins B hlegal a,globalPerm_valid_of_wins B hlegal a⟩

def solutionMap {n : Nat} (B : List Ban) (hlegal : legal n B) :
    {a : Fin n → Fin 3 // valid n B a} →
    {P : Equiv.Perm (Fin (n*8+1)) // wins (n*8+1) (emit n B) P} :=
  fun a => ⟨globalPerm a.val,globalPerm_wins B hlegal a.val a.property⟩

lemma solutionMap_injective {n : Nat} (B : List Ban) (hlegal : legal n B) :
    Function.Injective (solutionMap B hlegal) := by
  intro a b h
  apply Subtype.ext
  apply globalPerm_injective
  exact congrArg Subtype.val h

def CanonicalConverse (n : Nat) (B : List Ban) : Prop :=
  ∀ P : Equiv.Perm (Fin (n*8+1)), wins (n*8+1) (emit n B) P →
    ∃ a : Fin n → Fin 3, globalPerm a = P

lemma solutionMap_surjective_of_canonical_converse {n : Nat} (B : List Ban) (hlegal : legal n B)
    (remaining_canonical_converse : CanonicalConverse n B) :
    Function.Surjective (solutionMap B hlegal) := by
  intro P
  obtain ⟨a,ha⟩ := remaining_canonical_converse P.val P.property
  have hw : wins (n*8+1) (emit n B) (globalPerm a) := by rw [ha]; exact P.property
  refine ⟨⟨a,globalPerm_valid_of_wins B hlegal a hw⟩,?_⟩
  apply Subtype.ext
  exact ha

noncomputable def solutionsEquiv_of_canonical_converse {n : Nat} (B : List Ban) (hlegal : legal n B)
    (remaining_canonical_converse : CanonicalConverse n B) :
    {a : Fin n → Fin 3 // valid n B a} ≃
    {P : Equiv.Perm (Fin (n*8+1)) // wins (n*8+1) (emit n B) P} :=
  Equiv.ofBijective (solutionMap B hlegal)
    ⟨solutionMap_injective B hlegal,solutionMap_surjective_of_canonical_converse B hlegal remaining_canonical_converse⟩

lemma bijection_of_canonical_converse {n : Nat} (B : List Ban) (hlegal : legal n B)
    (remaining_canonical_converse : CanonicalConverse n B) :
    Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
      {P : Equiv.Perm (Fin (8*n+1)) // wins (8*n+1) (emit n B) P}) := by
  have hh : Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
      {P : Equiv.Perm (Fin (n*8+1)) // wins (n*8+1) (emit n B) P}) :=
    ⟨solutionsEquiv_of_canonical_converse B hlegal remaining_canonical_converse⟩
  have heq : n*8+1 = 8*n+1 := by omega
  exact heq ▸ hh
end PEqualNP.Outside.L_lib_896_aux.S895.Comb

namespace PEqualNP.Outside.L_lib_896_aux.S895

theorem padded_set_forcing {α : Type*} [DecidableEq α] (P : α → α)
    (hP : Function.Involutive P) (T D : Finset α) (hcard : T.card < D.card)
    (hwin : ∀ x ∈ D, ∃ u ∈ insert x T, P u ∈ insert x T ∧ P u ≠ u) :
    ∃ u ∈ T, P u ∈ T ∧ P u ≠ u := by
  classical
  by_contra hnone
  have hno : ∀ u ∈ T, P u ∈ T → P u = u := by
    intro u hu hpu
    by_contra hneq
    exact hnone ⟨u,hu,hpu,hneq⟩
  have hmap : ∀ x ∈ D, P x ∈ T := by
    intro x hx
    obtain ⟨u,hu,hpu,hneq⟩ := hwin x hx
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases Finset.mem_insert.mp hpu with hfix | hpT
      · exact False.elim (hneq hfix)
      · exact hpT
    · rcases Finset.mem_insert.mp hpu with heq | hpT
      · rw [← heq,hP u]
        exact hu
      · exact False.elim (hneq (hno u hu hpT))
  have hle : D.card ≤ T.card := Finset.card_le_card_of_injOn P
    (fun x hx => hmap x hx) (fun a _ b _ hab => hP.injective hab)
  omega

theorem padded_triangle_forcing {α : Type*} [DecidableEq α] (P : α → α)
    (hP : Function.Involutive P) (T D : Finset α) (hT : T.card ≤ 3) (hD : 4 ≤ D.card)
    (hwin : ∀ x ∈ D, ∃ u ∈ insert x T, P u ∈ insert x T ∧ P u ≠ u) :
    ∃ u ∈ T, P u ∈ T ∧ P u ≠ u :=
  padded_set_forcing P hP T D (by omega) hwin

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895
lemma involution_reverse {α : Type*} {P : α → α} (hP : Function.Involutive P)
    {a b : α} (h : P a = b) : P b = a := by rw [← h,hP a]
lemma triple_pair_cases {α : Type*} [DecidableEq α] {P : α → α} (hP : Function.Involutive P)
    (a b c : α)
    (hw : ∃ u ∈ ({a,b,c} : Finset α), P u ∈ ({a,b,c} : Finset α) ∧ P u ≠ u) :
    P a = b ∨ P a = c ∨ P b = c := by
  obtain ⟨u,hu,hpu,hneq⟩ := hw
  simp only[Finset.mem_insert,Finset.mem_singleton] at hu hpu
  rcases hu with rfl | rfl | rfl
  · rcases hpu with h | h | h
    · exact False.elim (hneq h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hpu with h | h | h
    · exact Or.inl (involution_reverse hP h)
    · exact False.elim (hneq h)
    · exact Or.inr (Or.inr (h))
  · rcases hpu with h | h | h
    · exact Or.inr (Or.inl (involution_reverse hP h))
    · exact Or.inr (Or.inr ((involution_reverse hP h)))
    · exact False.elim (hneq h)
lemma quad_pair_cases {α : Type*} [DecidableEq α] {P : α → α} (hP : Function.Involutive P)
    (a b c d : α)
    (hw : ∃ u ∈ ({a,b,c,d} : Finset α), P u ∈ ({a,b,c,d} : Finset α) ∧ P u ≠ u) :
    P a = b ∨ P a = c ∨ P a = d ∨ P b = c ∨ P b = d ∨ P c = d := by
  obtain ⟨u,hu,hpu,hneq⟩ := hw
  simp only[Finset.mem_insert,Finset.mem_singleton] at hu hpu
  rcases hu with rfl | rfl | rfl | rfl
  · rcases hpu with h | h | h | h
    · exact False.elim (hneq h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases hpu with h | h | h | h
    · exact Or.inl (involution_reverse hP h)
    · exact False.elim (hneq h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hpu with h | h | h | h
    · exact Or.inr (Or.inl (involution_reverse hP h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (involution_reverse hP h))))
    · exact False.elim (hneq h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
  · rcases hpu with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (involution_reverse hP h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (involution_reverse hP h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((involution_reverse hP h))))))
    · exact False.elim (hneq h)
end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895

lemma ambient_classification {α : Type*} (P : α → α) (v : Fin 8 → α)
    (hv : Function.Injective v) (hP : Function.Involutive P)
    (h00 : P (v 0) = v 2 ∨ P (v 0) = v 3 ∨ P (v 2) = v 3)
    (h01 : P (v 1) = v 2 ∨ P (v 1) = v 3 ∨ P (v 2) = v 3)
    (h10 : P (v 0) = v 4 ∨ P (v 0) = v 5 ∨ P (v 4) = v 5)
    (h11 : P (v 1) = v 4 ∨ P (v 1) = v 5 ∨ P (v 4) = v 5)
    (h20 : P (v 0) = v 6 ∨ P (v 0) = v 7 ∨ P (v 6) = v 7)
    (h21 : P (v 1) = v 6 ∨ P (v 1) = v 7 ∨ P (v 6) = v 7)
    (ho : P (v 0) = v 2 ∨ P (v 0) = v 4 ∨ P (v 0) = v 6 ∨
      P (v 2) = v 4 ∨ P (v 2) = v 6 ∨ P (v 4) = v 6) :
    ∃ c : Fin 3, ∀ r : Fin 8, P (v r) = v (localPartner c r) := by
  have hi0 := hP (v 0)
  have hi1 := hP (v 1)
  have hi2 := hP (v 2)
  have hi3 := hP (v 3)
  have hi4 := hP (v 4)
  have hi5 := hP (v 5)
  have hi6 := hP (v 6)
  have hi7 := hP (v 7)
  rcases ho with h|h|h|h|h|h
  · refine ⟨0,?_⟩
    intro r
    fin_cases r <;> simp_all [localPartner,hv.eq_iff] <;> aesop (add simp hv.eq_iff)
  · refine ⟨1,?_⟩
    intro r
    fin_cases r <;> simp_all [localPartner,hv.eq_iff] <;> aesop (add simp hv.eq_iff)
  · refine ⟨2,?_⟩
    intro r
    fin_cases r <;> simp_all [localPartner,hv.eq_iff] <;> aesop (add simp hv.eq_iff)
  all_goals exfalso
  all_goals simp_all [hv.eq_iff]
  all_goals aesop (add simp hv.eq_iff)

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895
open PEqualNP.Outside.L_lib_896_aux.S895.Comb

lemma coordinate_cover {n : Nat} (x : Fin (n*8+1)) (hx : x ≠ Fin.last (n*8)) :
    ∃ i : Fin n, ∃ r : Fin 8, x = coord i r := by
  have hv : x.val ≠ n*8 := fun h => hx (Fin.ext h)
  let y : Fin (n*8) := ⟨x.val,by omega⟩
  obtain ⟨⟨i,r⟩,hh⟩ := (finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n*8)).surjective y
  refine ⟨i,r,?_⟩
  apply Fin.ext
  exact (congrArg Fin.val hh).symm

lemma reconstruct_global {n : Nat} (P : Equiv.Perm (Fin (n*8+1)))
    (hP : Function.Involutive P) (a : Fin n → Fin 3)
    (hblock : ∀ i r, P (coord i r) = coord i (localPartner (a i) r)) :
    globalPerm a = P := by
  have hlast : P (Fin.last (n*8)) = Fin.last (n*8) := by
    by_contra hneq
    obtain ⟨i,r,he⟩ := coordinate_cover (P (Fin.last (n*8))) hneq
    have hh := hP (Fin.last (n*8))
    rw [he,hblock i r] at hh
    have hlt : (coord i (localPartner (a i) r)).val < n*8 :=
      (finProdFinEquiv (i,localPartner (a i) r)).isLt
    have hv := congrArg Fin.val hh
    change (coord i (localPartner (a i) r)).val = n*8 at hv
    omega
  apply Equiv.ext
  intro x
  by_cases hx : x = Fin.last (n*8)
  · subst x
    rw [globalPerm_last,hlast]
  · obtain ⟨i,r,rfl⟩ := coordinate_cover x hx
    exact (globalPerm_coord a i r).trans (hblock i r).symm

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895
open PEqualNP.Outside.L_lib_896_aux.S895.Comb

def basePort (b : Fin 2) : Fin 8 := ⟨b.val,by have := b.isLt; omega⟩
def evenPort (c : Fin 3) : Fin 8 := ⟨2+2*c.val,by have := c.isLt; omega⟩
def oddPort (c : Fin 3) : Fin 8 := ⟨3+2*c.val,by have := c.isLt; omega⟩
def padPort (j : Fin 4) : Fin 8 := ⟨j.val,by have := j.isLt; omega⟩
def nextIndex {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val+1) % n,Nat.mod_lt _ (by have := i.isLt; omega)⟩
def padCoord {n : Nat} (i : Fin n) (j : Fin 4) : Fin (n*8+1) :=
  coord (nextIndex i) (padPort j)

lemma coord_injective {n : Nat} (i : Fin n) : Function.Injective (coord i) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  rw [coord_val,coord_val] at hh
  omega
lemma padCoord_injective {n : Nat} (i : Fin n) : Function.Injective (padCoord i) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change r.val+8*((i.val+1) % n) = s.val+8*((i.val+1) % n) at hh
  omega

lemma orientation_mem_emit {n : Nat} (B : List Ban) (i : Fin n) :
    [8*i.val,8*i.val+2,8*i.val+4,8*i.val+6] ∈ emit n B := by
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
  exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
lemma triangle_mem_emit {n : Nat} (B : List Ban) (i : Fin n)
    (c : Fin 3) (b : Fin 2) (j : Fin 4) :
    [8*i.val+b.val] ++ flag i.val c.val ++ [8*((i.val+1) % n)+j.val] ∈ emit n B := by
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨c.val,List.mem_range.mpr c.isLt,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b.val,List.mem_range.mpr b.isLt,?_⟩
  exact List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩

lemma fin_mem_of_val_mem {k : Nat} (u : Fin k) (L : List (Fin k))
    (h : u.val ∈ L.map Fin.val) : u ∈ L := by
  obtain ⟨v,hv,heq⟩ := List.mem_map.mp h
  have hvu : v = u := Fin.ext heq
  simpa [hvu] using hv
lemma pair_from_list {k : Nat} (P : Equiv.Perm (Fin k)) (L : List (Fin k))
    (h : ∃ u : Fin k, u.val ∈ L.map Fin.val ∧ (P u).val ∈ L.map Fin.val ∧ P u ≠ u) :
    ∃ u ∈ L.toFinset, P u ∈ L.toFinset ∧ P u ≠ u := by
  obtain ⟨u,hu,hpu,hneq⟩ := h
  exact ⟨u,List.mem_toFinset.mpr (fin_mem_of_val_mem u L hu),
    List.mem_toFinset.mpr (fin_mem_of_val_mem (P u) L hpu),hneq⟩

lemma orientation_core_pair {n : Nat} (B : List Ban)
    (P : Equiv.Perm (Fin (n*8+1))) (hw : wins (n*8+1) (emit n B) P) (i : Fin n) :
    ∃ u ∈ ({coord i 0,coord i 2,coord i 4,coord i 6} : Finset (Fin (n*8+1))),
      P u ∈ ({coord i 0,coord i 2,coord i 4,coord i 6} : Finset (Fin (n*8+1))) ∧ P u ≠ u := by
  let L : List (Fin (n*8+1)) := [coord i 0,coord i 2,coord i 4,coord i 6]
  have heq : L.map Fin.val = [8*i.val,8*i.val+2,8*i.val+4,8*i.val+6] := by
    simp [L,coord_val,Nat.add_comm]
  have hh := hw.2 _ (orientation_mem_emit B i)
  rw [← heq] at hh
  have hp := pair_from_list P L hh
  simpa [L] using hp

lemma triangle_core_pair {n : Nat} (B : List Ban)
    (P : Equiv.Perm (Fin (n*8+1))) (hw : wins (n*8+1) (emit n B) P)
    (i : Fin n) (c : Fin 3) (b : Fin 2) :
    ∃ u ∈ ({coord i (basePort b),coord i (evenPort c),coord i (oddPort c)} : Finset (Fin (n*8+1))),
      P u ∈ ({coord i (basePort b),coord i (evenPort c),coord i (oddPort c)} : Finset (Fin (n*8+1))) ∧ P u ≠ u := by
  let T : Finset (Fin (n*8+1)) := {coord i (basePort b),coord i (evenPort c),coord i (oddPort c)}
  let D : Finset (Fin (n*8+1)) := Finset.univ.image (padCoord i)
  have hD : 4 ≤ D.card := by
    dsimp [D]
    rw [Finset.card_image_of_injective _ (padCoord_injective i)]
    simp
  apply padded_triangle_forcing P hw.1 T D Finset.card_le_three hD
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  let L : List (Fin (n*8+1)) :=
    [coord i (basePort b),coord i (evenPort c),coord i (oddPort c),padCoord i j]
  have heq : L.map Fin.val =
      [8*i.val+b.val] ++ flag i.val c.val ++ [8*((i.val+1) % n)+j.val] := by
    simp [L,coord_val,basePort,evenPort,oddPort,padCoord,padPort,nextIndex,flag,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hh := hw.2 _ (triangle_mem_emit B i c b j)
  rw [← heq] at hh
  have hp := pair_from_list P L hh
  have hs : L.toFinset = insert (padCoord i j) T := by
    ext y
    simp [L,T,or_assoc,or_left_comm,or_comm]
  simpa only [hs] using hp

lemma block_selected {n : Nat} (B : List Ban)
    (P : Equiv.Perm (Fin (n*8+1))) (hw : wins (n*8+1) (emit n B) P) (i : Fin n) :
    ∃ c : Fin 3, ∀ r : Fin 8, P (coord i r) = coord i (localPartner c r) := by
  have ht (c : Fin 3) (b : Fin 2) := triple_pair_cases hw.1
    (coord i (basePort b)) (coord i (evenPort c)) (coord i (oddPort c))
    (triangle_core_pair B P hw i c b)
  apply ambient_classification P (coord i) (coord_injective i) hw.1
  · simpa [basePort,evenPort,oddPort] using ht 0 0
  · simpa [basePort,evenPort,oddPort] using ht 0 1
  · simpa [basePort,evenPort,oddPort] using ht 1 0
  · simpa [basePort,evenPort,oddPort] using ht 1 1
  · simpa [basePort,evenPort,oddPort] using ht 2 0
  · simpa [basePort,evenPort,oddPort] using ht 2 1
  · exact quad_pair_cases hw.1 _ _ _ _ (orientation_core_pair B P hw i)

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895
open PEqualNP.Outside.L_lib_896_aux.S895.Comb

lemma canonical_converse (n : Nat) (B : List Ban) : CanonicalConverse n B := by
  classical
  intro P hw
  let a : Fin n → Fin 3 := fun i => Classical.choose (block_selected B P hw i)
  have ha : ∀ i r, P (coord i r) = coord i (localPartner (a i) r) :=
    fun i => Classical.choose_spec (block_selected B P hw i)
  exact ⟨a,reconstruct_global P hw.1 a ha⟩

theorem emitted_bijection {n : Nat} (B : List Ban) (hlegal : legal n B) :
    Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
      {P : Equiv.Perm (Fin (8*n+1)) // wins (8*n+1) (emit n B) P}) :=
  bijection_of_canonical_converse B hlegal (canonical_converse n B)

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895

def bits (w v : Nat) : List Bool := (List.range w).map (fun j => v.testBit j)

lemma bits_shift_tag (w i tag : Nat) (ht : tag < 8) :
    bits (w+3) (8*i+tag) = bits 3 tag ++ bits w i := by
  simp only [bits]
  rw [show w+3=3+w by omega,List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj' : j < 3 := List.mem_range.mp hj
    simpa only [show (2:Nat)^3=8 from rfl,if_pos hj'] using
      (Nat.testBit_two_pow_mul_add i (b:=tag) (i:=3) ht j)
  · apply List.map_congr_left
    intro j hj
    have hb : ¬3+j < 3 := by omega
    simpa only [show (2:Nat)^3=8 from rfl,if_neg hb,Nat.add_sub_cancel_left,Function.comp_def] using
      (Nat.testBit_two_pow_mul_add i (b:=tag) (i:=3) ht (3+j))

lemma flag_even_tag_lt (c : Nat) (hc : c<3) : 2+2*c < 8 := by omega
lemma flag_odd_tag_lt (c : Nat) (hc : c<3) : 3+2*c < 8 := by omega

end PEqualNP.Outside.L_lib_896_aux.S895

namespace PEqualNP.Outside.L_lib_896_aux.S895

abbrev Ban := (Nat × Nat) × (Nat × Nat)
def width (n : Nat) := n.log2+1
def header (n : Nat) := List.replicate n true ++ [false]
def legalRecord (n : Nat) (e : Ban) : Prop :=
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3

def recordBits (n : Nat) (e : Ban) :=
  bits (width n) e.1.1 ++ bits 2 e.1.2 ++ bits (width n) e.2.1 ++ bits 2 e.2.2

def enc (n : Nat) (B : List Ban) := header n ++ B.flatMap (recordBits n)
def legal (n : Nat) (B : List Ban) := 2≤n ∧ ∀ e∈B, legalRecord n e

lemma bits_length (w v : Nat) : (bits w v).length = w := by simp [bits]
lemma recordBits_length (n : Nat) (e : Ban) : (recordBits n e).length = 2*width n+4 := by
  simp only [recordBits,List.length_append,bits_length]; omega

lemma bits_injective (w a b : Nat) (ha : a < 2^w) (hb : b < 2^w)
    (h : bits w a = bits w b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<w
  · have hh := congrArg (fun l : List Bool => l.getD j false) h
    simpa [bits,List.getD_eq_getElem?_getD,hj] using hh
  · have hp : 2^w ≤ 2^j := by gcongr; omega
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp),Nat.testBit_lt_two_pow (hb.trans_le hp)]

lemma header_unique (n m : Nat) (a b : List Bool)
    (h : List.replicate n true ++ false::a = List.replicate m true ++ false::b) : n=m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      apply congrArg Nat.succ
      apply ih m
      simpa using (List.cons.inj h).2

lemma recordBits_injective (n : Nat) (a b : Ban) (ha : legalRecord n a) (hb : legalRecord n b)
    (h : recordBits n a = recordBits n b) : a=b := by
  dsimp only [legalRecord] at ha hb
  simp only [recordBits,List.append_assoc] at h
  obtain ⟨hi,h⟩ := List.append_inj h (by simp [bits_length])
  obtain ⟨hc,h⟩ := List.append_inj h (by simp [bits_length])
  obtain ⟨hj,hd⟩ := List.append_inj h (by simp [bits_length])
  have hn : n < 2^(width n) := Nat.lt_log2_self
  have hi' := bits_injective (width n) a.1.1 b.1.1 (lt_trans (lt_trans ha.1 ha.2.1) hn)
    (lt_trans (lt_trans hb.1 hb.2.1) hn) hi
  have hj' := bits_injective (width n) a.2.1 b.2.1 (lt_trans ha.2.1 hn) (lt_trans hb.2.1 hn) hj
  have hc' := bits_injective 2 a.1.2 b.1.2 (by omega) (by omega) hc
  have hd' := bits_injective 2 a.2.2 b.2.2 (by omega) (by omega) hd
  exact Prod.ext (Prod.ext hi' hc') (Prod.ext hj' hd')

lemma payload_injective (n : Nat) (B : List Ban) : ∀ B' : List Ban,
    (∀ e∈B, legalRecord n e) → (∀ e∈B', legalRecord n e) →
    B.flatMap (recordBits n) = B'.flatMap (recordBits n) → B=B' := by
  induction B with
  | nil =>
    intro B' hB hB' h
    cases B' with
    | nil => rfl
    | cons e es =>
      have hh := congrArg List.length h
      simp only [List.flatMap_nil,List.length_nil,List.flatMap_cons,List.length_append,recordBits_length] at hh
      omega
  | cons e es ih =>
    intro B' hB hB' h
    cases B' with
    | nil =>
      have hh := congrArg List.length h
      simp only [List.flatMap_nil,List.length_nil,List.flatMap_cons,List.length_append,recordBits_length] at hh
      omega
    | cons e' es' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨hh,ht⟩ := List.append_inj h (by rw [recordBits_length,recordBits_length])
      have he := recordBits_injective n e e' (hB e List.mem_cons_self) (hB' e' List.mem_cons_self) hh
      have hs := ih es' (fun a ha => hB a (List.mem_cons_of_mem e ha))
        (fun a ha => hB' a (List.mem_cons_of_mem e' ha)) ht
      rw [he,hs]

theorem enc_legal_injective (n m : Nat) (B B' : List Ban)
    (hn : legal n B) (hm : legal m B') (h : enc n B = enc m B') : n=m ∧ B=B' := by
  have he : n=m := header_unique n m (B.flatMap (recordBits n)) (B'.flatMap (recordBits m))
    (by simpa only [enc,header,List.append_assoc,List.singleton_append] using h)
  subst m
  refine ⟨rfl,?_⟩
  have hp : B.flatMap (recordBits n) = B'.flatMap (recordBits n) := List.append_cancel_left h
  exact payload_injective n B B' hn.2 hm.2 hp

end PEqualNP.Outside.L_lib_896_aux.S895
namespace PEqualNP.Outside.L_lib_896_aux.M896
open PEqualNP.Library PEqualNP.Search Lib.Machines Lib.Universal Lib.SearchHelpers Lib.SearchHelpers.SatV Lib.SearchHelpers.Tab.StepW

abbrev bits := S895.Comb.bits
abbrev header896 := S895.Comb.header
abbrev width := S895.Comb.width
abbrev pack := S895.Comb.pack
abbrev well := S895.Comb.well
abbrev wins := S895.Comb.wins

def lang : Language Bool := {x | ∃ k rows, well k rows ∧ pack k rows = x ∧
  ∃ P : Equiv.Perm (Fin k), wins k rows P}

def witness (k : Nat) (P : Equiv.Perm (Fin k)) : List Bool :=
  (List.finRange k).flatMap (fun i => bits (width k) (P i).val)

def R : Set (List Bool × List Bool) := {z | ∃ k rows, well k rows ∧ pack k rows = z.1 ∧
  ∃ P : Equiv.Perm (Fin k), wins k rows P ∧ witness k P = z.2}

lemma log2_le_self_aux (k : Nat) : k.log2 ≤ k := by
  by_cases h : k = 0
  · subst h; simp
  · have h1 : 2 ^ k.log2 ≤ k := Nat.log2_self_le h
    have h2 : k.log2 < 2 ^ k.log2 := Nat.lt_two_pow_self
    omega

lemma width_le_succ (k : Nat) : width k ≤ k + 1 := by
  unfold width S895.Comb.width
  have := log2_le_self_aux k
  omega

lemma width_pos (k : Nat) : 0 < width k := by
  unfold width S895.Comb.width
  omega

lemma bits_inj_k (k v1 v2 : Nat) (h1 : v1 < k) (h2 : v2 < k)
    (h : bits (width k) v1 = bits (width k) v2) : v1 = v2 := by
  have hk : k < 2 ^ (width k) := Nat.lt_log2_self
  exact S895.bits_injective (width k) v1 v2 (lt_trans h1 hk) (lt_trans h2 hk) h

lemma listBits_inj (k : Nat) (L1 : List Nat) : ∀ L2 : List Nat,
    L1.length = L2.length →
    (∀ v ∈ L1, v < k) → (∀ v ∈ L2, v < k) →
    L1.flatMap (bits (width k)) = L2.flatMap (bits (width k)) → L1 = L2 := by
  induction L1 with
  | nil =>
    intro L2 hlen _ _ _
    cases L2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro L2 hlen h1 h2 hflat
    cases L2 with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.flatMap_cons] at hflat
      obtain ⟨hh, ht⟩ := List.append_inj hflat
        (by rw [S895.Comb.bits_length, S895.Comb.bits_length])
      have hab := bits_inj_k k a b (h1 a List.mem_cons_self) (h2 b List.mem_cons_self) hh
      have hrest := ih bs (by simpa using hlen)
        (fun v hv => h1 v (List.mem_cons_of_mem a hv))
        (fun v hv => h2 v (List.mem_cons_of_mem b hv)) ht
      rw [hab, hrest]

lemma rowBits_length (k : Nat) (row : List Nat) (h : row.length = 4) :
    (row.flatMap (bits (width k))).length = 4 * width k := by
  rw [S895.Comb.flatMap_length_constant row (bits (width k)) (width k)
    (fun _ _ => S895.Comb.bits_length _ _), h]

lemma rowsBits_inj (k : Nat) (rows1 : List (List Nat)) : ∀ rows2 : List (List Nat),
    well k rows1 → well k rows2 →
    rows1.flatMap (fun row => row.flatMap (bits (width k))) =
      rows2.flatMap (fun row => row.flatMap (bits (width k))) →
    rows1 = rows2 := by
  induction rows1 with
  | nil =>
    intro rows2 _ hw2 hflat
    cases rows2 with
    | nil => rfl
    | cons r rs =>
      have hl := congrArg List.length hflat
      have hr := rowBits_length k r (hw2 r List.mem_cons_self).1
      have hwp := width_pos k
      simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons, List.length_append, hr] at hl
      omega
  | cons r1 rs1 ih =>
    intro rows2 hw1 hw2 hflat
    cases rows2 with
    | nil =>
      have hl := congrArg List.length hflat
      have hr := rowBits_length k r1 (hw1 r1 List.mem_cons_self).1
      have hwp := width_pos k
      simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons, List.length_append, hr] at hl
      omega
    | cons r2 rs2 =>
      simp only [List.flatMap_cons] at hflat
      have hr1 := hw1 r1 List.mem_cons_self
      have hr2 := hw2 r2 List.mem_cons_self
      obtain ⟨hh, ht⟩ := List.append_inj hflat
        (by rw [rowBits_length k r1 hr1.1, rowBits_length k r2 hr2.1])
      have hreq := listBits_inj k r1 r2 (by omega) hr1.2.2 hr2.2.2 hh
      have hrseq := ih rs2
        (fun r hr => hw1 r (List.mem_cons_of_mem r1 hr))
        (fun r hr => hw2 r (List.mem_cons_of_mem r2 hr)) ht
      rw [hreq, hrseq]

lemma pack_well_inj {k1 k2 : Nat} {rows1 rows2 : List (List Nat)}
    (hw1 : well k1 rows1) (hw2 : well k2 rows2) (hp : pack k1 rows1 = pack k2 rows2) :
    k1 = k2 ∧ rows1 = rows2 := by
  have hk : k1 = k2 := S895.header_unique k1 k2
    (rows1.flatMap (fun row => row.flatMap (bits (width k1))))
    (rows2.flatMap (fun row => row.flatMap (bits (width k2))))
    (by simpa only [pack, S895.Comb.pack, S895.Comb.header, List.append_assoc, List.singleton_append] using hp)
  subst k2
  refine ⟨rfl, ?_⟩
  have hflat : rows1.flatMap (fun row => row.flatMap (bits (width k1))) =
      rows2.flatMap (fun row => row.flatMap (bits (width k1))) := List.append_cancel_left hp
  exact rowsBits_inj k1 rows1 rows2 hw1 hw2 hflat

lemma witness_eq_map_flatMap (k : Nat) (P : Equiv.Perm (Fin k)) :
    witness k P = ((List.finRange k).map (fun i => (P i).val)).flatMap (bits (width k)) := by
  unfold witness
  rw [List.flatMap_map]

lemma witness_length (k : Nat) (P : Equiv.Perm (Fin k)) :
    (witness k P).length = k * width k := by
  unfold witness
  rw [S895.Comb.flatMap_length_constant _ _ (width k) (fun _ _ => S895.Comb.bits_length _ _),
    List.length_finRange]

lemma witness_inj (k : Nat) (P1 P2 : Equiv.Perm (Fin k))
    (h : witness k P1 = witness k P2) : P1 = P2 := by
  rw [witness_eq_map_flatMap, witness_eq_map_flatMap] at h
  have hm := listBits_inj k
    ((List.finRange k).map (fun i => (P1 i).val))
    ((List.finRange k).map (fun i => (P2 i).val))
    (by simp)
    (fun v hv => by obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv; exact (P1 i).isLt)
    (fun v hv => by obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv; exact (P2 i).isLt)
    h
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hi1 : i.val < ((List.finRange k).map (fun j => (P1 j).val)).length := by simp
  have hi2 : i.val < ((List.finRange k).map (fun j => (P2 j).val)).length := by simp
  have hget := congrArg (fun l : List Nat => l.getD i.val 0) hm
  rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hget
  simpa using hget

lemma witness_length_le : ∀ x w, (x, w) ∈ R → w.length ≤ (x.length + 1) ^ 2 := by
  rintro x w ⟨k, rows, _, rfl, P, _, rfl⟩
  rw [witness_length]
  have hx : k + 1 ≤ (pack k rows).length := by
    unfold pack S895.Comb.pack
    rw [List.length_append, S895.Comb.header_length]
    omega
  have hw : width k ≤ k + 1 := width_le_succ k
  have h1 : k * width k ≤ (k + 1) * (k + 1) := Nat.mul_le_mul (by omega) hw
  have h2 : (k + 1) * (k + 1) ≤ ((pack k rows).length + 1) * ((pack k rows).length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [sq]
  exact h1.trans h2

lemma witness_equiv : ∀ k rows, well k rows →
    ∃ E : {P : Equiv.Perm (Fin k) // wins k rows P} ≃
      {w : List Bool // (pack k rows, w) ∈ R}, ∀ P, (E P).val = witness k P.val := by
  intro k rows hw
  let f : {P : Equiv.Perm (Fin k) // wins k rows P} →
      {w : List Bool // (pack k rows, w) ∈ R} :=
    fun P => ⟨witness k P.1, ⟨k, rows, hw, rfl, P.1, P.2, rfl⟩⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, fun P => rfl⟩
  · intro P1 P2 h
    exact Subtype.ext (witness_inj k P1.1 P2.1 (congrArg Subtype.val h))
  · rintro ⟨w, hmem⟩
    rcases hmem with ⟨k', rows', hw', hp, P', hwins', hw_eq⟩
    obtain ⟨rfl, rfl⟩ := pack_well_inj hw' hw hp
    exact ⟨⟨P', hwins'⟩, Subtype.ext hw_eq⟩

def halfD : Bool → Bool → Bool × Option Bool
  | false, true => (true, none)
  | true, true => (false, some true)
  | _, false => (false, none)

def halfU (s : List Bool) : List Bool :=
  fstRun halfD (fun _ => none) false s

lemma cpt_halfU : CPTs halfU :=
  fst_polyTime (Q := Bool) _ _ halfU halfD (fun _ => none) false (fun _ => rfl)

lemma halfU_aux_length (q : Bool) (s : List Bool) :
    (fstRun halfD (fun _ => none) q s).length ≤ s.length := by
  induction s generalizing q with
  | nil => simp [fstRun]
  | cons b l ih =>
    simp only [fstRun]
    cases q <;> cases b <;> simp [halfD]
    all_goals have := ih true; have := ih false; omega

lemma halfU_length (s : List Bool) : (halfU s).length ≤ s.length :=
  halfU_aux_length false s

lemma halfU_un (v : Nat) : halfU (un v) = un (v / 2) := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    match v with
    | 0 => rfl
    | 1 => rfl
    | v + 2 =>
      have h1 : un (v + 2) = true :: true :: un v := by
        simp [un, List.replicate_succ]
      rw [h1]
      change true :: halfU (un v) = un ((v + 2) / 2)
      rw [ih v (by omega)]
      have hdiv : (v + 2) / 2 = v / 2 + 1 := by omega
      rw [hdiv, un_succ]

def wStep (y : List Bool) : List Bool :=
  let u := (unpairB y).1
  let acc := (unpairB y).2
  sel u (pairB u acc) (pairB (halfU u) (true :: acc))

lemma wStep_length (y : List Bool) : (wStep y).length ≤ y.length + 2 := by
  have h1 := unpairB_length y
  have h2 := halfU_length (unpairB y).1
  unfold wStep
  apply sel_length
  · rw [pairB_length]; omega
  · rw [pairB_length, List.length_cons]; omega

lemma cpt_wStep : CPTs wStep :=
  cpt_sel cpt_unpairB1
    (cpt_pairB2 cpt_unpairB1 cpt_unpairB2)
    (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_halfU) (cpt_cons1 true cpt_unpairB2))

def widthU (uK : List Bool) : List Bool :=
  (unpairB (wStep^[uK.length] (pairB (halfU uK) [true]))).2

lemma cpt_widthU : CPTs widthU :=
  cpt_unpairB2_1
    (cpt_iterGrow cpt_wStep 2 wStep_length cpt_id
      (cpt_pairB2 cpt_halfU (cpt_const [true])))

lemma cpt_widthU1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun s => widthU (f s)) :=
  cpt_comp hf cpt_widthU

lemma log2_step (u : Nat) (hu : 2 ≤ u) : u.log2 = (u / 2).log2 + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_of_one_lt_of_le (by omega) hu

lemma wStep_pairB (u acc : List Bool) :
    wStep (pairB u acc) = sel u (pairB u acc) (pairB (halfU u) (true :: acc)) := by
  unfold wStep
  rw [unpairB_pairB]

lemma wStep_iter_un (t : Nat) : ∀ (u acc : Nat), u ≤ t →
    wStep^[t] (pairB (un u) (un acc)) =
      pairB [] (un (acc + if u = 0 then 0 else u.log2 + 1)) := by
  induction t with
  | zero =>
    intro u acc hu
    have hu0 : u = 0 := by omega
    subst hu0
    simp [un]
  | succ t ih =>
    intro u acc hu
    rw [Function.iterate_succ_apply, wStep_pairB]
    cases u with
    | zero =>
      have hsel : sel (un 0) (pairB (un 0) (un acc)) (pairB (halfU (un 0)) (true :: un acc)) =
          pairB (un 0) (un acc) := rfl
      rw [hsel]
      simpa using ih 0 acc (by omega)
    | succ u' =>
      have hne : un (u' + 1) ≠ [] := by simp [un]
      rw [sel, ite_eq_right hne, halfU_un, ← un_succ]
      have hdiv : (u' + 1) / 2 ≤ t := by omega
      rw [ih ((u' + 1) / 2) (acc + 1) hdiv]
      congr 2
      by_cases hu2 : 2 ≤ u' + 1
      · have hpos : (u' + 1) / 2 ≠ 0 := by omega
        have hpos1 : u' + 1 ≠ 0 := by omega
        rw [ite_eq_right hpos, ite_eq_right hpos1, log2_step (u' + 1) hu2]
        omega
      · have hu1 : u' = 0 := by omega
        subst hu1
        simp

lemma widthU_un (k : Nat) : widthU (un k) = un (width k) := by
  unfold widthU
  rw [un_length, halfU_un]
  have hle : k / 2 ≤ k := Nat.div_le_self k 2
  have h1 : [true] = un 1 := rfl
  rw [h1, wStep_iter_un k (k / 2) 1 hle, unpairB_pairB]
  apply congrArg un
  unfold width S895.Comb.width
  by_cases hk : 2 ≤ k
  · have hpos : k / 2 ≠ 0 := by omega
    rw [ite_eq_right hpos, log2_step k hk]
    ring
  · have hzero : k / 2 = 0 := by omega
    rw [ite_eq_left hzero]
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl <;> simp

lemma parityRun_un (q : Bool) (v : Nat) :
    parityRun q (un v) = xor q (v.testBit 0) := by
  induction v generalizing q with
  | zero =>
    simp [un, parityRun]
  | succ v ih =>
    rw [un_succ]
    simp only [parityRun, ih]
    have hbit : (v + 1).testBit 0 = !(v.testBit 0) := by
      simp only [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with hv | hv
      · have h1 : (v + 1) % 2 = 1 := by omega
        simp [hv, h1]
      · have h1 : (v + 1) % 2 = 0 := by omega
        simp [hv, h1]
    rw [hbit]
    cases q <;> cases v.testBit 0 <;> rfl

lemma parityF_un (v : Nat) : parityF (un v) = bflag (v.testBit 0) := by
  unfold parityF
  rw [parityRun_un, Bool.false_xor]

def bStep (y : List Bool) : List Bool :=
  let u := (unpairB y).1
  let out := (unpairB y).2
  pairB (halfU u) (out ++ sel (parityF u) [false] [true])

lemma bStep_length (y : List Bool) : (bStep y).length ≤ y.length + 2 := by
  have h1 := unpairB_length y
  have h2 := halfU_length (unpairB y).1
  have h3 : (sel (parityF (unpairB y).1) [false] [true]).length ≤ 1 := by
    apply sel_length <;> simp
  unfold bStep
  rw [pairB_length, List.length_append]
  omega

lemma cpt_bStep : CPTs bStep :=
  cpt_pairB2
    (cpt_comp cpt_unpairB1 cpt_halfU)
    (cpt_app2 cpt_unpairB2
      (cpt_sel (cpt_parityF1 cpt_unpairB1) (cpt_const [false]) (cpt_const [true])))

def bitsU (uW uV : List Bool) : List Bool :=
  (unpairB (bStep^[uW.length] (pairB uV []))).2

lemma cpt_bitsU {fw fv : List Bool → List Bool} (hw : CPTs fw) (hv : CPTs fv) :
    CPTs (fun s => bitsU (fw s) (fv s)) :=
  cpt_unpairB2_1
    (cpt_iterGrow cpt_bStep 2 bStep_length hw (cpt_pairB2 hv (cpt_const [])))

lemma testBit_div_two_aux (v j : Nat) : (v / 2).testBit j = v.testBit (j + 1) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, pow_succ']

lemma bits_succ (w v : Nat) :
    bits (w + 1) v = v.testBit 0 :: bits w (v / 2) := by
  unfold bits S895.Comb.bits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact (testBit_div_two_aux v j).symm

lemma bStep_iter_un (w : Nat) : ∀ (v : Nat) (out : List Bool),
    bStep^[w] (pairB (un v) out) = pairB (un (v / 2 ^ w)) (out ++ bits w v) := by
  induction w with
  | zero =>
    intro v out
    simp [bits, S895.Comb.bits]
  | succ w ih =>
    intro v out
    rw [Function.iterate_succ_apply]
    have hstep : bStep (pairB (un v) out) =
        pairB (un (v / 2)) (out ++ [v.testBit 0]) := by
      simp only [bStep, unpairB_pairB, halfU_un, parityF_un]
      cases v.testBit 0 <;> rfl
    rw [hstep, ih (v / 2) (out ++ [v.testBit 0])]
    rw [Nat.div_div_eq_div_mul, ← pow_succ', List.append_assoc, List.singleton_append, ← bits_succ]

lemma bitsU_un (w v : Nat) : bitsU (un w) (un v) = bits w v := by
  unfold bitsU
  rw [un_length, bStep_iter_un, unpairB_pairB, List.nil_append]

lemma flatMap_unique {α : Type} (n v : Nat) (hv : v < n) (f : Nat → List α)
    (h0 : ∀ j < n, j ≠ v → f j = []) : (List.range n).flatMap f = f v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases heq : v = n
    · subst heq
      have hnil : (List.range v).flatMap f = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro j hj
        have hlt := List.mem_range.mp hj
        exact h0 j (by omega) (by omega)
      rw [hnil, List.nil_append]
    · have hlt : v < n := by omega
      have hlast : f n = [] := h0 n (by omega) (by omega)
      rw [ih hlt (fun j hj hne => h0 j (by omega) hne), hlast, List.append_nil]

def validSliceStep (y : List Bool) : List Bool :=
  let uV := (unpairB y).1
  let r := (unpairB y).2
  let uW := (unpairB r).1
  let sl := (unpairB r).2
  sel (eqF sl (bitsU uW uV)) [] [true]

lemma cpt_validSliceStep : CPTs validSliceStep :=
  cpt_sel
    (cpt_eqF' (cpt_unpairB2_1 cpt_unpairB2)
      (cpt_bitsU (cpt_unpairB1_1 cpt_unpairB2) cpt_unpairB1))
    (cpt_const []) (cpt_const [true])

def validSlice (uK uW sl : List Bool) : List Bool :=
  (List.range uK.length).flatMap fun v =>
    validSliceStep (pairB (un v) (pairB uW sl))

lemma cpt_validSlice {fk fw fsl : List Bool → List Bool}
    (hk : CPTs fk) (hw : CPTs fw) (hsl : CPTs fsl) :
    CPTs (fun s => validSlice (fk s) (fw s) (fsl s)) :=
  cpt_flatMapRange cpt_validSliceStep hk (cpt_pairB2 hw hsl)

lemma validSlice_spec (k : Nat) (sl : List Bool) :
    validSlice (un k) (un (width k)) sl ≠ [] ↔ ∃ v < k, sl = bits (width k) v := by
  unfold validSlice
  rw [un_length, ne_eq, flatMap_range_eq_nil_iff]
  push_neg
  constructor
  · rintro ⟨v, hv, hne⟩
    simp only [validSliceStep, unpairB_pairB, bitsU_un, eqF] at hne
    by_cases h : sl = bits (width k) v
    · exact ⟨v, hv, h⟩
    · simp [h, bflag, sel] at hne
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp [validSliceStep, unpairB_pairB, bitsU_un, eqF, bflag, sel]

def decodeValStep (y : List Bool) : List Bool :=
  let uV := (unpairB y).1
  let r := (unpairB y).2
  let uW := (unpairB r).1
  let sl := (unpairB r).2
  sel (eqF sl (bitsU uW uV)) [] uV

lemma cpt_decodeValStep : CPTs decodeValStep :=
  cpt_sel
    (cpt_eqF' (cpt_unpairB2_1 cpt_unpairB2)
      (cpt_bitsU (cpt_unpairB1_1 cpt_unpairB2) cpt_unpairB1))
    (cpt_const []) cpt_unpairB1

def decodeVal (uK uW sl : List Bool) : List Bool :=
  (List.range uK.length).flatMap fun v =>
    decodeValStep (pairB (un v) (pairB uW sl))

lemma cpt_decodeVal {fk fw fsl : List Bool → List Bool}
    (hk : CPTs fk) (hw : CPTs fw) (hsl : CPTs fsl) :
    CPTs (fun s => decodeVal (fk s) (fw s) (fsl s)) :=
  cpt_flatMapRange cpt_decodeValStep hk (cpt_pairB2 hw hsl)

lemma decodeVal_bits (k v : Nat) (hv : v < k) :
    decodeVal (un k) (un (width k)) (bits (width k) v) = un v := by
  unfold decodeVal
  rw [un_length]
  have hu := flatMap_unique k v hv
    (fun j => decodeValStep (pairB (un j) (pairB (un (width k)) (bits (width k) v))))
    (fun j hj hne => by
      simp only [decodeValStep, unpairB_pairB, bitsU_un, eqF]
      have hnb : bits (width k) v ≠ bits (width k) j :=
        fun heq => hne (bits_inj_k k v j hv hj heq).symm
      simp [hnb, bflag, sel])
  rw [hu]
  simp [decodeValStep, unpairB_pairB, bitsU_un, eqF, bflag, sel]

def sliceAt (uIdx uLen bs : List Bool) : List Bool :=
  tk uLen (dropK (mulU uIdx uLen) bs)

lemma cpt_sliceAt {fi fl fb : List Bool → List Bool}
    (hi : CPTs fi) (hl : CPTs fl) (hb : CPTs fb) :
    CPTs (fun s => sliceAt (fi s) (fl s) (fb s)) :=
  cpt_tk hl (cpt_dropK (cpt_mulU2 hi hl) hb)

lemma sliceAt_un (i w : Nat) (bs : List Bool) :
    sliceAt (un i) (un w) bs = (bs.drop (i * w)).take w := by
  unfold sliceAt
  rw [tk_eq, dropK_eq]
  simp [mulU, un_length]

lemma sliceAt_flatMap_bits (w : Nat) (L : List Nat) : ∀ i (hi : i < L.length),
    sliceAt (un i) (un w) (L.flatMap (bits w)) = bits w (L[i]'hi) := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons a as ih =>
    intro i hi
    rw [sliceAt_un, List.flatMap_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
      have htake := List.take_left (l₁ := bits w a) (l₂ := as.flatMap (bits w))
      rwa [S895.Comb.bits_length] at htake
    | succ i' =>
      have hmul : (i' + 1) * w = (bits w a).length + i' * w := by
        rw [S895.Comb.bits_length]; ring
      rw [hmul, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        Nat.add_sub_cancel_left]
      simp only [List.getElem_cons_succ]
      have hi' : i' < as.length := by simpa using hi
      have hrec := ih i' hi'
      rwa [sliceAt_un] at hrec

lemma flatMap_bits_of_slices (w : Nat) (N : Nat) :
    ∀ (bs : List Bool) (f : Nat → Nat),
      bs.length = N * w →
      (∀ i < N, sliceAt (un i) (un w) bs = bits w (f i)) →
      ((List.range N).map f).flatMap (bits w) = bs := by
  induction N with
  | zero =>
    intro bs f hlen _
    have : bs.length = 0 := by simpa using hlen
    exact (List.eq_nil_of_length_eq_zero this).symm
  | succ N ih =>
    intro bs f hlen hslice
    have h0 := hslice 0 (by omega)
    rw [sliceAt_un, Nat.zero_mul, List.drop_zero] at h0
    have hdrop_len : (bs.drop w).length = N * w := by
      rw [List.length_drop, hlen]; ring_nf; omega
    have hdrop_sl : ∀ i < N, sliceAt (un i) (un w) (bs.drop w) = bits w (f (i + 1)) := by
      intro i hi
      rw [sliceAt_un, List.drop_drop]
      have hmul : w + i * w = (i + 1) * w := by ring
      rw [hmul]
      have := hslice (i + 1) (by omega)
      rwa [sliceAt_un] at this
    have hrec := ih (bs.drop w) (fun i => f (i + 1)) hdrop_len hdrop_sl
    rw [List.range_succ_eq_map, List.map_cons, List.flatMap_cons, List.map_map]
    change bits w (f 0) ++ ((List.range N).map (fun i => f (i + 1))).flatMap (bits w) = bs
    rw [hrec, ← h0, List.take_append_drop]

lemma flatMap_rows_4 (w : Nat) (m : Nat) (g : Nat → Nat) :
    (((List.range m).map fun r => [g (4 * r), g (4 * r + 1), g (4 * r + 2), g (4 * r + 3)]).flatMap
      (fun row => row.flatMap (bits w))) =
    ((List.range (4 * m)).map g).flatMap (bits w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih]
    have h4 : 4 * (m + 1) = 4 * m + 4 := by omega
    rw [h4, List.range_add, List.map_append, List.flatMap_append]
    congr 1
    simp [List.range_succ]

def checkPermStep (y : List Bool) : List Bool :=
  let uI := (unpairB y).1
  let r := (unpairB y).2
  let uK := (unpairB r).1
  let r2 := (unpairB r).2
  let uW := (unpairB r2).1
  let wWit := (unpairB r2).2
  let slI := sliceAt uI uW wWit
  let okVal := validSlice uK uW slI
  let uPI := decodeVal uK uW slI
  let okInv := eqF (decodeVal uK uW (sliceAt uPI uW wWit)) uI
  notF (andF okVal okInv)

lemma cpt_checkPermStep : CPTs checkPermStep := by
  have huI := cpt_unpairB1
  have hr := cpt_unpairB2
  have huK := cpt_unpairB1_1 hr
  have hr2 := cpt_unpairB2_1 hr
  have huW := cpt_unpairB1_1 hr2
  have hw := cpt_unpairB2_1 hr2
  have hslI := cpt_sliceAt huI huW hw
  have hokVal := cpt_validSlice huK huW hslI
  have huPI := cpt_decodeVal huK huW hslI
  have hokInv := cpt_eqF' (cpt_decodeVal huK huW (cpt_sliceAt huPI huW hw)) huI
  exact cpt_notF (cpt_andF hokVal hokInv)

def checkPerm (uK uW wWit : List Bool) : List Bool :=
  notF ((List.range uK.length).flatMap fun i =>
    checkPermStep (pairB (un i) (pairB uK (pairB uW wWit))))

lemma cpt_checkPerm {fk fw fww : List Bool → List Bool}
    (hk : CPTs fk) (hw : CPTs fw) (hww : CPTs fww) :
    CPTs (fun s => checkPerm (fk s) (fw s) (fww s)) :=
  cpt_notF (cpt_flatMapRange cpt_checkPermStep hk (cpt_pairB2 hk (cpt_pairB2 hw hww)))

def checkRowStep (y : List Bool) : List Bool :=
  let uR := (unpairB y).1
  let r1 := (unpairB y).2
  let uK := (unpairB r1).1
  let r2 := (unpairB r1).2
  let uW := (unpairB r2).1
  let r3 := (unpairB r2).2
  let rest := (unpairB r3).1
  let wWit := (unpairB r3).2
  let uBase := mulU (un 4) uR
  let sl0 := sliceAt uBase uW rest
  let sl1 := sliceAt (true :: uBase) uW rest
  let sl2 := sliceAt (true :: true :: uBase) uW rest
  let sl3 := sliceAt (true :: true :: true :: uBase) uW rest
  let okVals := andF (validSlice uK uW sl0)
    (andF (validSlice uK uW sl1) (andF (validSlice uK uW sl2) (validSlice uK uW sl3)))
  let v0 := decodeVal uK uW sl0
  let v1 := decodeVal uK uW sl1
  let v2 := decodeVal uK uW sl2
  let v3 := decodeVal uK uW sl3
  let okNodup := andF (notF (eqF v0 v1))
    (andF (notF (eqF v0 v2))
      (andF (notF (eqF v0 v3))
        (andF (notF (eqF v1 v2))
          (andF (notF (eqF v1 v3)) (notF (eqF v2 v3))))))
  let p0 := decodeVal uK uW (sliceAt v0 uW wWit)
  let p1 := decodeVal uK uW (sliceAt v1 uW wWit)
  let p2 := decodeVal uK uW (sliceAt v2 uW wWit)
  let okWin := orF (eqF p0 v1)
    (orF (eqF p0 v2)
      (orF (eqF p0 v3)
        (orF (eqF p1 v2)
          (orF (eqF p1 v3) (eqF p2 v3)))))
  notF (andF okVals (andF okNodup okWin))

lemma cpt_checkRowStep : CPTs checkRowStep := by
  have huR := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huK := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have huW := cpt_unpairB1_1 hr2
  have hr3 := cpt_unpairB2_1 hr2
  have hrest := cpt_unpairB1_1 hr3
  have hww := cpt_unpairB2_1 hr3
  have huBase := cpt_mulU2 (cpt_const (un 4)) huR
  have hsl0 := cpt_sliceAt huBase huW hrest
  have hsl1 := cpt_sliceAt (cpt_cons1 true huBase) huW hrest
  have hsl2 := cpt_sliceAt (cpt_cons1 true (cpt_cons1 true huBase)) huW hrest
  have hsl3 := cpt_sliceAt (cpt_cons1 true (cpt_cons1 true (cpt_cons1 true huBase))) huW hrest
  have hokVals := cpt_andF (cpt_validSlice huK huW hsl0)
    (cpt_andF (cpt_validSlice huK huW hsl1)
      (cpt_andF (cpt_validSlice huK huW hsl2) (cpt_validSlice huK huW hsl3)))
  have hv0 := cpt_decodeVal huK huW hsl0
  have hv1 := cpt_decodeVal huK huW hsl1
  have hv2 := cpt_decodeVal huK huW hsl2
  have hv3 := cpt_decodeVal huK huW hsl3
  have hokNodup := cpt_andF (cpt_notF (cpt_eqF' hv0 hv1))
    (cpt_andF (cpt_notF (cpt_eqF' hv0 hv2))
      (cpt_andF (cpt_notF (cpt_eqF' hv0 hv3))
        (cpt_andF (cpt_notF (cpt_eqF' hv1 hv2))
          (cpt_andF (cpt_notF (cpt_eqF' hv1 hv3)) (cpt_notF (cpt_eqF' hv2 hv3))))))
  have hp0 := cpt_decodeVal huK huW (cpt_sliceAt hv0 huW hww)
  have hp1 := cpt_decodeVal huK huW (cpt_sliceAt hv1 huW hww)
  have hp2 := cpt_decodeVal huK huW (cpt_sliceAt hv2 huW hww)
  have hokWin := cpt_orF (cpt_eqF' hp0 hv1)
    (cpt_orF (cpt_eqF' hp0 hv2)
      (cpt_orF (cpt_eqF' hp0 hv3)
        (cpt_orF (cpt_eqF' hp1 hv2)
          (cpt_orF (cpt_eqF' hp1 hv3) (cpt_eqF' hp2 hv3)))))
  exact cpt_notF (cpt_andF hokVals (cpt_andF hokNodup hokWin))

def checkRows (uRows uK uW rest wWit : List Bool) : List Bool :=
  notF ((List.range uRows.length).flatMap fun r =>
    checkRowStep (pairB (un r) (pairB uK (pairB uW (pairB rest wWit)))))

lemma cpt_checkRows {fr fk fw frest fww : List Bool → List Bool}
    (hr : CPTs fr) (hk : CPTs fk) (hw : CPTs fw) (hrest : CPTs frest) (hww : CPTs fww) :
    CPTs (fun s => checkRows (fr s) (fk s) (fw s) (frest s) (fww s)) :=
  cpt_notF (cpt_flatMapRange cpt_checkRowStep hr
    (cpt_pairB2 hk (cpt_pairB2 hw (cpt_pairB2 hrest hww))))

def okRestStep (y : List Bool) : List Bool :=
  let uM := (unpairB y).1
  let r := (unpairB y).2
  let uRest := (unpairB r).1
  let uRowBits := (unpairB r).2
  sel (eqF uRest (mulU uM uRowBits)) [] [true]

lemma cpt_okRestStep : CPTs okRestStep :=
  cpt_sel
    (cpt_eqF' (cpt_unpairB1_1 cpt_unpairB2) (cpt_mulU2 cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)))
    (cpt_const []) (cpt_const [true])

def uRowsStep (y : List Bool) : List Bool :=
  let uM := (unpairB y).1
  let r := (unpairB y).2
  let uRest := (unpairB r).1
  let uRowBits := (unpairB r).2
  sel (eqF uRest (mulU uM uRowBits)) [] uM

lemma cpt_uRowsStep : CPTs uRowsStep :=
  cpt_sel
    (cpt_eqF' (cpt_unpairB1_1 cpt_unpairB2) (cpt_mulU2 cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)))
    (cpt_const []) cpt_unpairB1

def verifRFlag (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let wWit := (unpairB s).2
  let okHdr := hasFalse x
  let uK := hd x
  let rest := dropN x
  let uW := widthU uK
  let uRowBits := mulU (un 4) uW
  let uRest := toUnary rest
  let okRest := (List.range (true :: uRest).length).flatMap fun m =>
    okRestStep (pairB (un m) (pairB uRest uRowBits))
  let uRows := (List.range (true :: uRest).length).flatMap fun m =>
    uRowsStep (pairB (un m) (pairB uRest uRowBits))
  let okWitLen := eqF (toUnary wWit) (mulU uK uW)
  let okPerm := checkPerm uK uW wWit
  let okRows := checkRows uRows uK uW rest wWit
  andF okHdr (andF okRest (andF okWitLen (andF okPerm okRows)))

lemma cpt_verifRFlag : CPTs verifRFlag := by
  have hx := cpt_unpairB1
  have hww := cpt_unpairB2
  have hokHdr := cpt_hasFalse1 hx
  have huK := cpt_hd1 hx
  have hrest := cpt_dropN1 hx
  have huW := cpt_widthU1 huK
  have huRowBits := cpt_mulU2 (cpt_const (un 4)) huW
  have huRest := cpt_toUnary1 hrest
  have hcnt := cpt_cons1 true huRest
  have hokRest := cpt_flatMapRange cpt_okRestStep hcnt (cpt_pairB2 huRest huRowBits)
  have huRows := cpt_flatMapRange cpt_uRowsStep hcnt (cpt_pairB2 huRest huRowBits)
  have hokWitLen := cpt_eqF' (cpt_toUnary1 hww) (cpt_mulU2 huK huW)
  have hokPerm := cpt_checkPerm huK huW hww
  have hokRows := cpt_checkRows huRows huK huW hrest hww
  exact cpt_andF hokHdr (cpt_andF hokRest (cpt_andF hokWitLen (cpt_andF hokPerm hokRows)))

def verifR (z : List Bool × List Bool) : Bool :=
  !(verifRFlag (pairB z.1 z.2)).isEmpty

lemma notF_ne_nil_iff (a : List Bool) : notF a ≠ [] ↔ a = [] := by
  cases a <;> simp [notF, sel]

lemma ne_nil_of_notF_eq_nil {a : List Bool} (h : notF a = []) : a ≠ [] := by
  cases a with
  | nil => simp [notF, sel] at h
  | cons _ _ => simp

lemma eqF_un_eq_nil_of_ne {a b : Nat} (hab : a ≠ b) : eqF (un a) (un b) = [] := by
  have hne : un a ≠ un b := fun h => hab (un_inj h)
  simp [eqF, hne, bflag]

lemma orF_ne_nil_iff (a b : List Bool) : orF a b ≠ [] ↔ a ≠ [] ∨ b ≠ [] := by
  cases a <;> cases b <;> simp [orF, sel]

lemma eqF_ne_nil_iff (a b : List Bool) : eqF a b ≠ [] ↔ a = b := by
  unfold eqF
  rw [bflag_ne_nil_iff, decide_eq_true_eq]

lemma un_eq_un_iff (a b : Nat) : un a = un b ↔ a = b :=
  ⟨un_inj, fun h => by rw [h]⟩

lemma row_get_eq_4 (row : List Nat) (h : row.length = 4) :
    row = [row[0]'(by omega), row[1]'(by omega), row[2]'(by omega), row[3]'(by omega)] := by
  match row with
  | [a, b, c, d] => rfl
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ => simp at h

lemma rows_flatMap_eq_flatten (k : Nat) (rows : List (List Nat)) :
    rows.flatMap (fun row => row.flatMap (bits (width k))) =
      rows.flatten.flatMap (bits (width k)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.flatten_cons, List.flatMap_append, ih]

lemma flatten_length_of_well (k : Nat) (rows : List (List Nat)) (hw : well k rows) :
    rows.flatten.length = 4 * rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    have hr := (hw r List.mem_cons_self).1
    have hrs := ih (fun x hx => hw x (List.mem_cons_of_mem r hx))
    simp only [List.flatten_cons, List.length_append, hr, hrs, List.length_cons]
    omega

lemma flatten_getElem_of_well (k : Nat) (rows : List (List Nat)) (hw : well k rows)
    (r t : Nat) (hr : r < rows.length) (ht : t < 4) :
    rows.flatten[4 * r + t]'(by rw [flatten_length_of_well k rows hw]; omega) =
      (rows[r]'hr)[t]'(by rw [(hw (rows[r]'hr) (List.getElem_mem hr)).1]; exact ht) := by
  induction rows generalizing r with
  | nil => simp at hr
  | cons row rs ih =>
    have hrl := (hw row List.mem_cons_self).1
    cases r with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
      rw [List.getElem_append_left (by omega)]
    | succ r' =>
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [List.getElem_append_right (by omega)]
      have hidx : 4 * (r' + 1) + t - row.length = 4 * r' + t := by omega
      simp only [hidx]
      exact ih (fun x hx => hw x (List.mem_cons_of_mem row hx)) r' (by simpa using hr)

lemma verifR_complete (x wWit : List Bool) (hz : (x, wWit) ∈ R) :
    verifRFlag (pairB x wWit) ≠ [] := by
  rcases hz with ⟨k, rows, hwell, rfl, P, hwins, rfl⟩
  unfold verifRFlag
  simp only [unpairB_pairB]
  repeat rw [andF_ne_nil_iff]
  have hx_hdr : pack k rows = header k ++ rows.flatMap (fun row => row.flatMap (bits (width k))) := rfl
  have hhd : hd (pack k rows) = un k := by rw [hx_hdr, hd_header_append]
  have hdn : dropN (pack k rows) = rows.flatMap (fun row => row.flatMap (bits (width k))) := by
    rw [hx_hdr, dropN_header_append]
  rw [hhd, hdn, widthU_un]
  have hrest_len : (rows.flatMap (fun row => row.flatMap (bits (width k)))).length =
      rows.length * (4 * width k) := by
    rw [S895.Comb.flatMap_length_constant rows _ (4 * width k)
      (fun row hrow => rowBits_length k row (hwell row hrow).1)]
  have hwp : 0 < width k := width_pos k
  have hmul_row : mulU (un 4) (un (width k)) = un (4 * width k) := by simp [mulU, un_length]
  have hmlt : rows.length < (true :: toUnary (rows.flatMap (fun row => row.flatMap (bits (width k))))).length := by
    simp only [List.length_cons, toUnary, un_length, hrest_len]
    have : rows.length * 1 ≤ rows.length * (4 * width k) := Nat.mul_le_mul_left _ (by omega)
    omega
  have huRows_eq : ((List.range (true :: toUnary (rows.flatMap (fun row => row.flatMap (bits (width k))))).length).flatMap
      fun m => uRowsStep (pairB (un m)
        (pairB (toUnary (rows.flatMap (fun row => row.flatMap (bits (width k)))))
          (mulU (un 4) (un (width k)))))) = un rows.length := by
    rw [flatMap_unique _ rows.length hmlt _ (fun m _ hne => by
      simp only [uRowsStep, unpairB_pairB, toUnary, hrest_len, hmul_row, mulU, un_length, eqF]
      have hneq : un (rows.length * (4 * width k)) ≠ un (m * (4 * width k)) := by
        intro heq
        have := un_inj heq
        have : rows.length = m := Nat.eq_of_mul_eq_mul_right (by omega) this
        exact hne this.symm
      simp [hneq, bflag, sel])]
    simp [uRowsStep, unpairB_pairB, toUnary, hrest_len, hmul_row, mulU, un_length, eqF, bflag, sel]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hx_hdr]; unfold hasFalse header; simp [bflag]
  · rw [ne_eq, flatMap_range_eq_nil_iff]; push_neg
    refine ⟨rows.length, hmlt, ?_⟩
    simp [okRestStep, unpairB_pairB, toUnary, hrest_len, hmul_row, mulU, un_length, eqF, bflag, sel]
  · rw [eqF_ne_nil_iff]
    simp [toUnary, witness_length, mulU, un_length]
  · unfold checkPerm
    rw [notF_ne_nil_iff, un_length, flatMap_range_eq_nil_iff]
    intro i hi
    simp only [checkPermStep, unpairB_pairB]
    rw [witness_eq_map_flatMap]
    have hsl : sliceAt (un i) (un (width k))
        (((List.finRange k).map fun j => (P j).val).flatMap (bits (width k))) =
        bits (width k) (P ⟨i, hi⟩).val := by
      rw [sliceAt_flatMap_bits (width k) _ i (by simp [hi])]
      simp
    rw [hsl, decodeVal_bits k (P ⟨i, hi⟩).val (P ⟨i, hi⟩).isLt]
    have hsl2 : sliceAt (un (P ⟨i, hi⟩).val) (un (width k))
        (((List.finRange k).map fun j => (P j).val).flatMap (bits (width k))) =
        bits (width k) i := by
      rw [sliceAt_flatMap_bits (width k) _ (P ⟨i, hi⟩).val (by simp [(P ⟨i, hi⟩).isLt])]
      have hinv : P (P ⟨i, hi⟩) = ⟨i, hi⟩ := hwins.1 ⟨i, hi⟩
      simpa using congrArg (fun x : Fin k => bits (width k) x.val) hinv
    rw [hsl2, decodeVal_bits k i hi]
    have hv1 : validSlice (un k) (un (width k)) (bits (width k) (P ⟨i, hi⟩).val) ≠ [] :=
      (validSlice_spec k _).mpr ⟨(P ⟨i, hi⟩).val, (P ⟨i, hi⟩).isLt, rfl⟩
    have heq1 : eqF (un i) (un i) ≠ [] := (eqF_ne_nil_iff _ _).mpr rfl
    have hand1 : andF (validSlice (un k) (un (width k)) (bits (width k) (P ⟨i, hi⟩).val))
        (eqF (un i) (un i)) ≠ [] := (andF_ne_nil_iff _ _).mpr ⟨hv1, heq1⟩
    cases h : andF (validSlice (un k) (un (width k)) (bits (width k) (P ⟨i, hi⟩).val))
        (eqF (un i) (un i)) with
    | nil => exact (hand1 h).elim
    | cons _ _ => rfl
  · rw [huRows_eq]
    unfold checkRows
    rw [notF_ne_nil_iff, un_length, flatMap_range_eq_nil_iff]
    intro r hr
    simp only [checkRowStep, unpairB_pairB]
    have hrow_mem : rows[r]'hr ∈ rows := List.getElem_mem hr
    have hrow_well := hwell (rows[r]'hr) hrow_mem
    have hrow_len := hrow_well.1
    let v0 := (rows[r]'hr)[0]'(by omega)
    let v1 := (rows[r]'hr)[1]'(by omega)
    let v2 := (rows[r]'hr)[2]'(by omega)
    let v3 := (rows[r]'hr)[3]'(by omega)
    have hrow_eq : rows[r]'hr = [v0, v1, v2, v3] := row_get_eq_4 (rows[r]'hr) hrow_len
    have hv0 : v0 < k := hrow_well.2.2 v0 (by rw [hrow_eq]; simp)
    have hv1 : v1 < k := hrow_well.2.2 v1 (by rw [hrow_eq]; simp)
    have hv2 : v2 < k := hrow_well.2.2 v2 (by rw [hrow_eq]; simp)
    have hv3 : v3 < k := hrow_well.2.2 v3 (by rw [hrow_eq]; simp)
    have hsl_t : ∀ t (ht : t < 4),
        sliceAt (un (4 * r + t)) (un (width k))
          (rows.flatMap (fun row => row.flatMap (bits (width k)))) =
        bits (width k) ((rows[r]'hr)[t]'(by omega)) := by
      intro t ht
      rw [rows_flatMap_eq_flatten, sliceAt_flatMap_bits (width k) rows.flatten (4 * r + t)
        (by rw [flatten_length_of_well k rows hwell]; omega)]
      rw [flatten_getElem_of_well k rows hwell r t hr ht]
    have hbase0 : mulU (un 4) (un r) = un (4 * r) := by simp [mulU, un_length]
    have hbase1 : true :: mulU (un 4) (un r) = un (4 * r + 1) := by rw [hbase0, un_succ]
    have hbase2 : true :: true :: mulU (un 4) (un r) = un (4 * r + 2) := by
      rw [hbase0, ← un_succ, ← un_succ]
    have hbase3 : true :: true :: true :: mulU (un 4) (un r) = un (4 * r + 3) := by
      rw [hbase0, ← un_succ, ← un_succ, ← un_succ]
    have hwit_sl : ∀ (v : Nat) (hv : v < k),
        decodeVal (un k) (un (width k)) (sliceAt (un v) (un (width k)) (witness k P)) =
        un (P ⟨v, hv⟩).val := by
      intro v hv
      rw [witness_eq_map_flatMap, sliceAt_flatMap_bits (width k) _ v (by simp [hv])]
      simp only [List.getElem_map, List.getElem_finRange]
      exact decodeVal_bits k (P ⟨v, hv⟩).val (P ⟨v, hv⟩).isLt
    have hnodup := hrow_well.2.1
    rw [hrow_eq] at hnodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup
    obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, _⟩ := hnodup
    have hwin_row := hwins.2 (rows[r]'hr) hrow_mem
    rw [hrow_eq] at hwin_row
    obtain ⟨u, hu, hpu, hune⟩ := hwin_row
    have hpair : (P ⟨v0, hv0⟩).val = v1 ∨ (P ⟨v0, hv0⟩).val = v2 ∨ (P ⟨v0, hv0⟩).val = v3 ∨
        (P ⟨v1, hv1⟩).val = v2 ∨ (P ⟨v1, hv1⟩).val = v3 ∨ (P ⟨v2, hv2⟩).val = v3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hpu
      have hune_v : (P u).val ≠ u.val := fun h => hune (Fin.ext h)
      rcases hu with hu | hu | hu | hu
      · have hu' : u = ⟨v0, hv0⟩ := Fin.ext hu
        rw [hu'] at hpu hune_v
        rcases hpu with h | h | h | h
        · exact (hune_v h).elim
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · have hu' : u = ⟨v1, hv1⟩ := Fin.ext hu
        rw [hu'] at hpu hune_v
        rcases hpu with h | h | h | h
        · left
          have : P ⟨v0, hv0⟩ = ⟨v1, hv1⟩ := by
            rw [show (⟨v0, hv0⟩ : Fin k) = P ⟨v1, hv1⟩ from Fin.ext h.symm, hwins.1]
          exact congrArg Fin.val this
        · exact (hune_v h).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · have hu' : u = ⟨v2, hv2⟩ := Fin.ext hu
        rw [hu'] at hpu hune_v
        rcases hpu with h | h | h | h
        · right; left
          have : P ⟨v0, hv0⟩ = ⟨v2, hv2⟩ := by
            rw [show (⟨v0, hv0⟩ : Fin k) = P ⟨v2, hv2⟩ from Fin.ext h.symm, hwins.1]
          exact congrArg Fin.val this
        · right; right; right; left
          have : P ⟨v1, hv1⟩ = ⟨v2, hv2⟩ := by
            rw [show (⟨v1, hv1⟩ : Fin k) = P ⟨v2, hv2⟩ from Fin.ext h.symm, hwins.1]
          exact congrArg Fin.val this
        · exact (hune_v h).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · have hu' : u = ⟨v3, hv3⟩ := Fin.ext hu
        rw [hu'] at hpu hune_v
        rcases hpu with h | h | h | h
        · right; right; left
          have : P ⟨v0, hv0⟩ = ⟨v3, hv3⟩ := by
            rw [show (⟨v0, hv0⟩ : Fin k) = P ⟨v3, hv3⟩ from Fin.ext h.symm, hwins.1]
          exact congrArg Fin.val this
        · right; right; right; right; left
          have : P ⟨v1, hv1⟩ = ⟨v3, hv3⟩ := by
            rw [show (⟨v1, hv1⟩ : Fin k) = P ⟨v3, hv3⟩ from Fin.ext h.symm, hwins.1]
          exact congrArg Fin.val this
        · right; right; right; right; right
          have : P ⟨v2, hv2⟩ = ⟨v3, hv3⟩ := by
            rw [show (⟨v2, hv2⟩ : Fin k) = P ⟨v3, hv3⟩ from Fin.ext h.symm, hwins.1]
          exact congrArg Fin.val this
        · exact (hune_v h).elim
    have hne_body : ∀ a : List Bool, a ≠ [] → notF a = [] := by
      intro a ha; cases a with | nil => exact (ha rfl).elim | cons _ _ => rfl
    apply hne_body
    have h1 : sliceAt (mulU (un 4) (un r)) (un (width k))
        (rows.flatMap fun row => row.flatMap (bits (width k))) = bits (width k) v0 := by
      simpa [hbase0, v0] using hsl_t 0 (by omega)
    have h2 : sliceAt (true :: mulU (un 4) (un r)) (un (width k))
        (rows.flatMap fun row => row.flatMap (bits (width k))) = bits (width k) v1 := by
      simpa [hbase1, v1] using hsl_t 1 (by omega)
    have h3 : sliceAt (true :: true :: mulU (un 4) (un r)) (un (width k))
        (rows.flatMap fun row => row.flatMap (bits (width k))) = bits (width k) v2 := by
      simpa [hbase2, v2] using hsl_t 2 (by omega)
    have h4 : sliceAt (true :: true :: true :: mulU (un 4) (un r)) (un (width k))
        (rows.flatMap fun row => row.flatMap (bits (width k))) = bits (width k) v3 := by
      simpa [hbase3, v3] using hsl_t 3 (by omega)
    rw [h1, h2, h3, h4,
      decodeVal_bits k v0 hv0, decodeVal_bits k v1 hv1,
      decodeVal_bits k v2 hv2, decodeVal_bits k v3 hv3,
      hwit_sl v0 hv0, hwit_sl v1 hv1, hwit_sl v2 hv2]
    repeat rw [andF_ne_nil_iff]
    refine ⟨⟨(validSlice_spec k _).mpr ⟨v0, hv0, rfl⟩,
      (validSlice_spec k _).mpr ⟨v1, hv1, rfl⟩,
      (validSlice_spec k _).mpr ⟨v2, hv2, rfl⟩,
      (validSlice_spec k _).mpr ⟨v3, hv3, rfl⟩⟩, ?_, ?_⟩
    · repeat rw [notF_ne_nil_iff]
      exact ⟨eqF_un_eq_nil_of_ne h01, eqF_un_eq_nil_of_ne h02, eqF_un_eq_nil_of_ne h03,
        eqF_un_eq_nil_of_ne h12, eqF_un_eq_nil_of_ne h13, eqF_un_eq_nil_of_ne h23⟩
    · repeat rw [orF_ne_nil_iff]
      repeat rw [eqF_ne_nil_iff]
      repeat rw [un_eq_un_iff]
      exact hpair

lemma verifR_sound (x wWit : List Bool) (hne : verifRFlag (pairB x wWit) ≠ []) :
    (x, wWit) ∈ R := by
  unfold verifRFlag at hne
  simp only [unpairB_pairB] at hne
  repeat rw [andF_ne_nil_iff] at hne
  obtain ⟨hokHdr, hokRest, hokWitLen, hokPerm, hokRows⟩ := hne
  have hf : false ∈ x := by
    unfold hasFalse at hokHdr
    rwa [bflag_ne_nil_iff, decide_eq_true_eq] at hokHdr
  set k := (hd x).length
  set rest := dropN x
  have huK : hd x = un k := hd_eq_un_length x
  have hx_eq : x = header k ++ rest := (header_parse_iff x).mp hf
  rw [huK, widthU_un] at hokRest hokWitLen hokPerm hokRows
  have hwp : 0 < width k := width_pos k
  have hm_ex : ∃ m < (true :: toUnary rest).length, rest.length = m * (4 * width k) := by
    rw [ne_eq, flatMap_range_eq_nil_iff] at hokRest
    push_neg at hokRest
    obtain ⟨m, hm, hne_m⟩ := hokRest
    simp only [okRestStep, unpairB_pairB, toUnary, mulU, un_length, eqF] at hne_m
    by_cases heq : un rest.length = un (m * (4 * width k))
    · exact ⟨m, hm, un_inj heq⟩
    · simp [heq, bflag, sel] at hne_m
  obtain ⟨m, hm_lt, hrest_len⟩ := hm_ex
  have huRows_eq : ((List.range (true :: toUnary rest).length).flatMap fun j =>
      uRowsStep (pairB (un j) (pairB (toUnary rest) (mulU (un 4) (un (width k)))))) = un m := by
    rw [flatMap_unique _ m hm_lt _ (fun j _ hne_j => by
      simp only [uRowsStep, unpairB_pairB, toUnary, hrest_len, mulU, un_length, eqF]
      have hneq : un (m * (4 * width k)) ≠ un (j * (4 * width k)) := by
        intro heq
        have := un_inj heq
        have : m = j := Nat.eq_of_mul_eq_mul_right (by omega) this
        exact hne_j this.symm
      simp [hneq, bflag, sel])]
    simp [uRowsStep, unpairB_pairB, toUnary, hrest_len, mulU, un_length, eqF, bflag, sel]
  rw [huRows_eq] at hokRows
  have hwit_len : wWit.length = k * width k := by
    rw [eqF_ne_nil_iff] at hokWitLen
    simp only [toUnary, mulU, un_length] at hokWitLen
    exact un_inj hokWitLen
  unfold checkPerm at hokPerm
  rw [notF_ne_nil_iff, un_length, flatMap_range_eq_nil_iff] at hokPerm
  have hperm_i : ∀ i < k,
      let sl := sliceAt (un i) (un (width k)) wWit
      (∃ v < k, sl = bits (width k) v) ∧
      decodeVal (un k) (un (width k))
        (sliceAt (decodeVal (un k) (un (width k)) sl) (un (width k)) wWit) = un i := by
    intro i hi
    have hstep := hokPerm i hi
    simp only [checkPermStep, unpairB_pairB] at hstep
    have hnot := ne_nil_of_notF_eq_nil hstep
    rw [andF_ne_nil_iff, validSlice_spec, eqF_ne_nil_iff] at hnot
    exact hnot
  let pFun : Nat → Nat := fun i =>
    (decodeVal (un k) (un (width k)) (sliceAt (un i) (un (width k)) wWit)).length
  have hp_spec : ∀ i < k, pFun i < k ∧
      sliceAt (un i) (un (width k)) wWit = bits (width k) (pFun i) ∧
      pFun (pFun i) = i := by
    intro i hi
    obtain ⟨⟨v, hv, hsl⟩, hinv⟩ := hperm_i i hi
    have hdec : decodeVal (un k) (un (width k)) (sliceAt (un i) (un (width k)) wWit) = un v := by
      rw [hsl, decodeVal_bits k v hv]
    have hpv : pFun i = v := by simp [pFun, hdec, un_length]
    rw [hdec] at hinv
    have hp_inv : pFun v = i := by simp [pFun, hinv, un_length]
    rw [hpv]
    exact ⟨hv, hsl, hp_inv⟩
  let P : Equiv.Perm (Fin k) :=
    { toFun := fun i => ⟨pFun i.val, (hp_spec i.val i.isLt).1⟩
      invFun := fun i => ⟨pFun i.val, (hp_spec i.val i.isLt).1⟩
      left_inv := fun i => Fin.ext (hp_spec i.val i.isLt).2.2
      right_inv := fun i => Fin.ext (hp_spec i.val i.isLt).2.2 }
  have hP_invol : Function.Involutive P := fun i => Fin.ext (hp_spec i.val i.isLt).2.2
  have hwit_eq : witness k P = wWit := by
    rw [witness_eq_map_flatMap]
    have hmap : (List.finRange k).map (fun i => (P i).val) = (List.range k).map pFun := by
      apply List.ext_getElem (by simp)
      intro i hi1 hi2
      simp [P]
    rw [hmap]
    exact flatMap_bits_of_slices (width k) k wWit pFun hwit_len
      (fun i hi => (hp_spec i hi).2.1)
  unfold checkRows at hokRows
  rw [notF_ne_nil_iff, un_length, flatMap_range_eq_nil_iff] at hokRows
  let gVal : Nat → Nat := fun idx =>
    (decodeVal (un k) (un (width k)) (sliceAt (un idx) (un (width k)) rest)).length
  let rows : List (List Nat) :=
    (List.range m).map fun r =>
      [gVal (4 * r), gVal (4 * r + 1), gVal (4 * r + 2), gVal (4 * r + 3)]
  have hrow_ok : ∀ r < m,
      let v0 := gVal (4 * r)
      let v1 := gVal (4 * r + 1)
      let v2 := gVal (4 * r + 2)
      let v3 := gVal (4 * r + 3)
      (v0 < k ∧ v1 < k ∧ v2 < k ∧ v3 < k) ∧
      (sliceAt (un (4 * r)) (un (width k)) rest = bits (width k) v0 ∧
       sliceAt (un (4 * r + 1)) (un (width k)) rest = bits (width k) v1 ∧
       sliceAt (un (4 * r + 2)) (un (width k)) rest = bits (width k) v2 ∧
       sliceAt (un (4 * r + 3)) (un (width k)) rest = bits (width k) v3) ∧
      (v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3) ∧
      (pFun v0 = v1 ∨ pFun v0 = v2 ∨ pFun v0 = v3 ∨ pFun v1 = v2 ∨ pFun v1 = v3 ∨ pFun v2 = v3) := by
    intro r hr
    have hstep := hokRows r hr
    simp only [checkRowStep, unpairB_pairB] at hstep
    have hnot := ne_nil_of_notF_eq_nil hstep
    have hbase0 : mulU (un 4) (un r) = un (4 * r) := by simp [mulU, un_length]
    have hbase1 : true :: mulU (un 4) (un r) = un (4 * r + 1) := by rw [hbase0, un_succ]
    have hbase2 : true :: true :: mulU (un 4) (un r) = un (4 * r + 2) := by
      rw [hbase0, ← un_succ, ← un_succ]
    have hbase3 : true :: true :: true :: mulU (un 4) (un r) = un (4 * r + 3) := by
      rw [hbase0, ← un_succ, ← un_succ, ← un_succ]
    rw [hbase3, hbase2, hbase1, hbase0] at hnot
    repeat rw [andF_ne_nil_iff] at hnot
    obtain ⟨⟨hs0, hs1, hs2, hs3⟩, ⟨hn01, hn02, hn03, hn12, hn13, hn23⟩, hwin_r⟩ := hnot
    obtain ⟨w0, hw0, hsl0⟩ := (validSlice_spec k _).mp hs0
    obtain ⟨w1, hw1, hsl1⟩ := (validSlice_spec k _).mp hs1
    obtain ⟨w2, hw2, hsl2⟩ := (validSlice_spec k _).mp hs2
    obtain ⟨w3, hw3, hsl3⟩ := (validSlice_spec k _).mp hs3
    have hd0 : decodeVal (un k) (un (width k)) (sliceAt (un (4 * r)) (un (width k)) rest) = un w0 := by
      rw [hsl0, decodeVal_bits k w0 hw0]
    have hd1 : decodeVal (un k) (un (width k)) (sliceAt (un (4 * r + 1)) (un (width k)) rest) = un w1 := by
      rw [hsl1, decodeVal_bits k w1 hw1]
    have hd2 : decodeVal (un k) (un (width k)) (sliceAt (un (4 * r + 2)) (un (width k)) rest) = un w2 := by
      rw [hsl2, decodeVal_bits k w2 hw2]
    have hd3 : decodeVal (un k) (un (width k)) (sliceAt (un (4 * r + 3)) (un (width k)) rest) = un w3 := by
      rw [hsl3, decodeVal_bits k w3 hw3]
    have hg0 : gVal (4 * r) = w0 := by simp [gVal, hd0, un_length]
    have hg1 : gVal (4 * r + 1) = w1 := by simp [gVal, hd1, un_length]
    have hg2 : gVal (4 * r + 2) = w2 := by simp [gVal, hd2, un_length]
    have hg3 : gVal (4 * r + 3) = w3 := by simp [gVal, hd3, un_length]
    simp only [hd0, hd1, hd2, hd3] at hn01 hn02 hn03 hn12 hn13 hn23 hwin_r
    have hp_eq : ∀ w (hw : w < k),
        decodeVal (un k) (un (width k)) (sliceAt (un w) (un (width k)) wWit) = un (pFun w) := by
      intro w hw
      rw [(hp_spec w hw).2.1, decodeVal_bits k (pFun w) (hp_spec w hw).1]
    simp only [hp_eq w0 hw0, hp_eq w1 hw1, hp_eq w2 hw2] at hwin_r
    repeat rw [orF_ne_nil_iff] at hwin_r
    repeat rw [eqF_ne_nil_iff] at hwin_r
    repeat rw [un_eq_un_iff] at hwin_r
    have hne_of : ∀ a b : Nat, notF (eqF (un a) (un b)) ≠ [] → a ≠ b := by
      intro a b h hab
      subst hab
      simp [eqF, bflag, notF, sel] at h
    rw [hg0, hg1, hg2, hg3]
    exact ⟨⟨hw0, hw1, hw2, hw3⟩, ⟨hsl0, hsl1, hsl2, hsl3⟩,
      ⟨hne_of _ _ hn01, hne_of _ _ hn02, hne_of _ _ hn03,
       hne_of _ _ hn12, hne_of _ _ hn13, hne_of _ _ hn23⟩, hwin_r⟩
  have hrest_eq : rows.flatMap (fun row => row.flatMap (bits (width k))) = rest := by
    rw [flatMap_rows_4]
    apply flatMap_bits_of_slices (width k) (4 * m) rest gVal (by rw [hrest_len]; ring)
    intro idx hidx
    have hr : idx / 4 < m := by omega
    have hro := (hrow_ok (idx / 4) hr).2.1
    have hmod : idx % 4 = 0 ∨ idx % 4 = 1 ∨ idx % 4 = 2 ∨ idx % 4 = 3 := by omega
    rcases hmod with h | h | h | h
    · have heq : idx = 4 * (idx / 4) := by omega
      rw [heq]; exact hro.1
    · have heq : idx = 4 * (idx / 4) + 1 := by omega
      rw [heq]; exact hro.2.1
    · have heq : idx = 4 * (idx / 4) + 2 := by omega
      rw [heq]; exact hro.2.2.1
    · have heq : idx = 4 * (idx / 4) + 3 := by omega
      rw [heq]; exact hro.2.2.2
  refine ⟨k, rows, ?_, ?_, P, ⟨hP_invol, ?_⟩, hwit_eq⟩
  · intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    have hr' := List.mem_range.mp hr
    obtain ⟨⟨h0, h1, h2, h3⟩, _, ⟨hn01, hn02, hn03, hn12, hn13, hn23⟩, _⟩ := hrow_ok r hr'
    refine ⟨rfl, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨hn01, hn02, hn03⟩, ⟨hn12, hn13⟩, hn23⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
  · unfold pack S895.Comb.pack
    change header k ++ rows.flatMap (fun row => row.flatMap (bits (width k))) = x
    rw [hrest_eq, ← hx_eq]
  · intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    have hr' := List.mem_range.mp hr
    obtain ⟨⟨h0, h1, h2, h3⟩, _, ⟨hn01, hn02, hn03, hn12, hn13, hn23⟩, hpair⟩ := hrow_ok r hr'
    rcases hpair with h | h | h | h | h | h
    · refine ⟨⟨gVal (4 * r), h0⟩, by simp, by simp [P, h], ?_⟩
      intro heq; apply hn01; symm; simpa [P, h] using congrArg Fin.val heq
    · refine ⟨⟨gVal (4 * r), h0⟩, by simp, by simp [P, h], ?_⟩
      intro heq; apply hn02; symm; simpa [P, h] using congrArg Fin.val heq
    · refine ⟨⟨gVal (4 * r), h0⟩, by simp, by simp [P, h], ?_⟩
      intro heq; apply hn03; symm; simpa [P, h] using congrArg Fin.val heq
    · refine ⟨⟨gVal (4 * r + 1), h1⟩, by simp, by simp [P, h], ?_⟩
      intro heq; apply hn12; symm; simpa [P, h] using congrArg Fin.val heq
    · refine ⟨⟨gVal (4 * r + 1), h1⟩, by simp, by simp [P, h], ?_⟩
      intro heq; apply hn13; symm; simpa [P, h] using congrArg Fin.val heq
    · refine ⟨⟨gVal (4 * r + 2), h2⟩, by simp, by simp [P, h], ?_⟩
      intro heq; apply hn23; symm; simpa [P, h] using congrArg Fin.val heq

lemma verifR_iff (z : List Bool × List Bool) : z ∈ R ↔ verifR z = true := by
  rcases z with ⟨x, wWit⟩
  have hne_iff : verifR (x, wWit) = true ↔ verifRFlag (pairB x wWit) ≠ [] := by
    unfold verifR
    cases h : verifRFlag (pairB x wWit) <;> simp
  rw [hne_iff]
  exact ⟨verifR_complete x wWit, verifR_sound x wWit⟩

lemma decidable_R : DecidableInPolyTime encodePair R :=
  ⟨verifR, verifR_iff,
    cpt_comp (g := fun l : List Bool => !l.isEmpty)
      (cpt_comp (g := verifRFlag) cpt_pairB cpt_verifRFlag)
      cpt_neS⟩

def anchorBans : List S895.Comb.Ban :=
  [((0, 0), (1, 1)), ((0, 0), (1, 2)),
   ((0, 1), (1, 0)), ((0, 1), (1, 1)), ((0, 1), (1, 2)),
   ((0, 2), (1, 0)), ((0, 2), (1, 1)), ((0, 2), (1, 2))]

def boolBans (m : Nat) : List S895.Comb.Ban :=
  (List.range m).map (fun p => ((0, 0), (2 + p, 2)))

def oppBans (φ : CNF) : List S895.Comb.Ban :=
  let m := (occs φ).length
  (List.range m).flatMap fun p =>
    (List.range m).flatMap fun q =>
      if h : p < q ∧ q < m then
        let lp := ((occs φ)[p]'(by omega)).2
        let lq := ((occs φ)[q]'h.2).2
        if lp.1 = lq.1 ∧ lp.2 ≠ lq.2 then [((2 + p, 1), (2 + q, 1))] else []
      else []

def clauseAutoBans (φ : CNF) : List S895.Comb.Ban :=
  let m := (occs φ).length
  (List.range m).flatMap fun p =>
    if hp : p < m then
      let u := 2 + m + p
      let cp := ((occs φ)[p]'hp).1
      [((2 + p, 1), (u, 0)), ((2 + p, 0), (u, 1))] ++
      (if h0 : p = 0 then [((0, 0), (u, 2))]
       else if ((occs φ)[p - 1]'(by omega)).1 ≠ cp then [((0, 0), (u, 2))] else []) ++
      (if hp1 : p + 1 < m then
         if cp = ((occs φ)[p + 1]'hp1).1 then
           [((u, 0), (u + 1, 2)), ((u, 1), (u + 1, 0)), ((u, 1), (u + 1, 1)),
            ((u, 2), (u + 1, 0)), ((u, 2), (u + 1, 1))]
         else [((0, 0), (u, 0))]
       else [((0, 0), (u, 0))])
    else []

def occBans (φ : CNF) : List S895.Comb.Ban :=
  anchorBans ++ boolBans (occs φ).length ++ oppBans φ ++ clauseAutoBans φ

lemma occBans_legal (φ : CNF) : S895.Comb.legal (2 + 2 * (occs φ).length) (occBans φ) := by
  refine ⟨by omega, fun e he => ?_⟩
  simp only [occBans, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · simp only [anchorBans, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    have hp' := List.mem_range.mp hp
    dsimp only; omega
  · obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
    by_cases hcond : p < q ∧ q < (occs φ).length
    · rw [dite_eq_left hcond] at he
      dsimp only at he
      split_ifs at he
      · simp only [List.mem_singleton] at he; subst he; dsimp only; omega
      · simp at he
    · rw [dite_eq_right hcond] at he; simp at he
  · obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    have hp' := List.mem_range.mp hp
    simp only [hp', ↓reduceDIte, List.mem_append] at he
    rcases he with (he | he) | he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> dsimp only <;> omega
    · split_ifs at he
      · simp only [List.mem_singleton] at he; subst he; dsimp only; omega
      · simp only [List.mem_singleton] at he; subst he; dsimp only; omega
      · simp at he
    · split_ifs at he with hp1 hsame
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
      · simp only [List.mem_singleton] at he; subst he; dsimp only; omega
      · simp only [List.mem_singleton] at he; subst he; dsimp only; omega

lemma occsAux_mono (ci : Nat) (φ : CNF) : ∀ p q (hp : p < (occsAux ci φ).length)
    (hq : q < (occsAux ci φ).length), p ≤ q →
    ((occsAux ci φ)[p]'hp).1 ≤ ((occsAux ci φ)[q]'hq).1 := by
  induction φ generalizing ci with
  | nil => intro p q _ hq _; simp [occsAux] at hq
  | cons c cs ih =>
    intro p q hp hq hpq
    simp only [occsAux] at hp hq ⊢
    by_cases hqc : q < c.length
    · have hpc : p < c.length := by omega
      rw [List.getElem_append_left (by simp [hpc]), List.getElem_append_left (by simp [hqc])]
      simp
    · by_cases hpc : p < c.length
      · rw [List.getElem_append_left (by simp [hpc]), List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map]
        have hmem := List.getElem_mem (l := occsAux (ci + 1) cs) (n := q - (c.map (fun l => (ci, l))).length) (by simp at hq ⊢; omega)
        have hge := (occsAux_mem_clause_lt (ci + 1) cs _ hmem).1
        omega
      · rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp only [List.length_map]
        exact ih (ci + 1) (p - c.length) (q - c.length) (by simp at hp; omega) (by simp at hq; omega) (by omega)

lemma occs_mono (φ : CNF) (p q : Nat) (hp : p < (occs φ).length) (hq : q < (occs φ).length)
    (hpq : p ≤ q) : ((occs φ)[p]'hp).1 ≤ ((occs φ)[q]'hq).1 :=
  occsAux_mono 0 φ p q hp hq hpq

lemma exists_last_in_clause (φ : CNF) (i : Nat) :
    ∀ p (hp : p < (occs φ).length), ((occs φ)[p]'hp).1 = i →
      ∃ q, ∃ hq : q < (occs φ).length, ((occs φ)[q]'hq).1 = i ∧
        ∀ (hq1 : q + 1 < (occs φ).length), ((occs φ)[q + 1]'hq1).1 ≠ i := by
  intro p hp hpi
  induction hrem : (occs φ).length - p generalizing p with
  | zero => omega
  | succ d ih =>
    by_cases hnext : ∃ hp1 : p + 1 < (occs φ).length, ((occs φ)[p + 1]'hp1).1 = i
    · obtain ⟨hp1, hpi1⟩ := hnext
      exact ih (p + 1) hp1 hpi1 (by omega)
    · exact ⟨p, hp, hpi, fun hp1 hEq => hnext ⟨hp1, hEq⟩⟩

lemma valid_ban_at {n : Nat} {B : List S895.Comb.Ban} {a : Fin n → Fin 3}
    (hv : S895.Comb.valid n B a) {i ci j cj : Nat} (hi : i < n) (hj : j < n)
    (hmem : ((i, ci), (j, cj)) ∈ B) :
    (a ⟨i, hi⟩).val ≠ ci ∨ (a ⟨j, hj⟩).val ≠ cj := by
  have h := hv ((i, ci), (j, cj)) hmem
  simpa only [S895.Comb.assignment_lookup a ⟨i, hi⟩, S895.Comb.assignment_lookup a ⟨j, hj⟩] using h

lemma occBans_sat_of_valid (φ : CNF) (hne : ∀ c ∈ φ, c ≠ [])
  (h : ∃ a : Fin (2 + 2 * (occs φ).length) → Fin 3,
    S895.Comb.valid (2 + 2 * (occs φ).length) (occBans φ) a) : Satisfiable φ := by
  set m := (occs φ).length
  set n := 2 + 2 * m
  rcases h with ⟨a, ha⟩
  have hanc : ∀ e ∈ anchorBans, e ∈ occBans φ := fun e he =>
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he)))))
  have ha01 : (a ⟨0, by omega⟩).val = 0 ∧ (a ⟨1, by omega⟩).val = 0 := by
    have h01 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 0), (1, 1)) (by simp [anchorBans]))
    have h02 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 0), (1, 2)) (by simp [anchorBans]))
    have h10 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 1), (1, 0)) (by simp [anchorBans]))
    have h11 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 1), (1, 1)) (by simp [anchorBans]))
    have h12 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 1), (1, 2)) (by simp [anchorBans]))
    have h20 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 2), (1, 0)) (by simp [anchorBans]))
    have h21 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 2), (1, 1)) (by simp [anchorBans]))
    have h22 := valid_ban_at ha (by omega) (by omega) (hanc ((0, 2), (1, 2)) (by simp [anchorBans]))
    have hb0 := (a ⟨0, by omega⟩).isLt
    have hb1 := (a ⟨1, by omega⟩).isLt
    omega
  have hbool : ∀ p (hp : p < m), (a ⟨2 + p, by omega⟩).val ≠ 2 := by
    intro p hp
    have hm : ((0, 0), (2 + p, 2)) ∈ occBans φ :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩))))))
    have hv := valid_ban_at ha (by omega) (by omega) hm
    omega
  have hauto_mem : ∀ p (hp : p < m) (e : S895.Comb.Ban),
      e ∈ ([((2 + p, 1), (2 + m + p, 0)), ((2 + p, 0), (2 + m + p, 1))] ++
        (if h0 : p = 0 then [((0, 0), (2 + m + p, 2))]
         else if ((occs φ)[p - 1]'(by omega)).1 ≠ ((occs φ)[p]'hp).1 then [((0, 0), (2 + m + p, 2))] else []) ++
        (if hp1 : p + 1 < m then
           if ((occs φ)[p]'hp).1 = ((occs φ)[p + 1]'hp1).1 then
             [((2 + m + p, 0), (2 + m + p + 1, 2)), ((2 + m + p, 1), (2 + m + p + 1, 0)),
              ((2 + m + p, 1), (2 + m + p + 1, 1)), ((2 + m + p, 2), (2 + m + p + 1, 0)),
              ((2 + m + p, 2), (2 + m + p + 1, 1))]
           else [((0, 0), (2 + m + p, 0))]
         else [((0, 0), (2 + m + p, 0))])) →
      e ∈ occBans φ := by
    intro p hp e he
    apply List.mem_append.mpr; right
    unfold clauseAutoBans
    apply List.mem_flatMap.mpr
    refine ⟨p, List.mem_range.mpr hp, ?_⟩
    rw [dite_eq_left hp]
    exact he
  have hchain : ∀ p (hp : p < m), (a ⟨2 + m + p, by omega⟩).val ≠ 0 →
      ∃ q ≤ p, ∃ hq : q < m, ((occs φ)[q]'hq).1 = ((occs φ)[p]'hp).1 ∧
        (a ⟨2 + q, by omega⟩).val = 1 := by
    intro p
    induction p with
    | zero =>
      intro hp hne0
      have hlt := (a ⟨2 + m + 0, by omega⟩).isLt
      have hno2 : (a ⟨2 + m + 0, by omega⟩).val ≠ 2 := by
        have hm := hauto_mem 0 hp ((0, 0), (2 + m + 0, 2)) (by simp)
        have hv := valid_ban_at ha (by omega) (by omega) hm
        omega
      have heq1 : (a ⟨2 + m + 0, by omega⟩).val = 1 := by omega
      have hno0 : (a ⟨2 + 0, by omega⟩).val ≠ 0 := by
        have hm := hauto_mem 0 hp ((2 + 0, 0), (2 + m + 0, 1)) (by simp)
        have hv := valid_ban_at ha (by omega) (by omega) hm
        omega
      have hb0 := hbool 0 hp
      have hlt0 := (a ⟨2 + 0, by omega⟩).isLt
      exact ⟨0, le_rfl, hp, rfl, by omega⟩
    | succ p' ih =>
      intro hp hne0
      have hlt := (a ⟨2 + m + (p' + 1), by omega⟩).isLt
      by_cases heq1 : (a ⟨2 + m + (p' + 1), by omega⟩).val = 1
      · have hm := hauto_mem (p' + 1) hp ((2 + (p' + 1), 0), (2 + m + (p' + 1), 1)) (by simp)
        have hv := valid_ban_at ha (by omega) (by omega) hm
        have hb := hbool (p' + 1) hp
        have hltp := (a ⟨2 + (p' + 1), by omega⟩).isLt
        exact ⟨p' + 1, le_rfl, hp, rfl, by omega⟩
      · have heq2 : (a ⟨2 + m + (p' + 1), by omega⟩).val = 2 := by omega
        have hp' : p' < m := by omega
        have hsame : ((occs φ)[p']'hp').1 = ((occs φ)[p' + 1]'hp).1 := by
          by_contra hdiff
          have hm := hauto_mem (p' + 1) hp ((0, 0), (2 + m + (p' + 1), 2)) (by
            apply List.mem_append.mpr; left
            apply List.mem_append.mpr; right
            simp [hdiff])
          have hv := valid_ban_at ha (by omega) (by omega) hm
          omega
        have hm := hauto_mem p' hp' ((2 + m + p', 0), (2 + m + p' + 1, 2)) (by
          apply List.mem_append.mpr; right
          simp [hp, hsame])
        have hv := valid_ban_at ha (by omega) (by omega) hm
        have hprev_ne0 : (a ⟨2 + m + p', by omega⟩).val ≠ 0 := by
          have : (⟨2 + m + p' + 1, by omega⟩ : Fin n) = ⟨2 + m + (p' + 1), by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [this] at hv
          omega
        obtain ⟨q, hqp, hqm, hqcl, hqa⟩ := ih hp' hprev_ne0
        exact ⟨q, by omega, hqm, hqcl.trans hsame, hqa⟩
  classical
  let σ : Assignment := fun v =>
    decide (∃ q : Fin m, ((occs φ)[q.val]'q.isLt).2 = (v, true) ∧ (a ⟨2 + q.val, by omega⟩).val = 1)
  have hlit_true : ∀ q (hq : q < m), (a ⟨2 + q, by omega⟩).val = 1 →
      Literal.eval σ ((occs φ)[q]'hq).2 = true := by
    intro q hq hqa
    unfold Literal.eval
    rcases hlit : ((occs φ)[q]'hq).2 with ⟨v, pol⟩
    cases pol
    · simp only [beq_iff_eq, σ, decide_eq_false_iff_not]
      rintro ⟨q', hq'l, hq'a⟩
      have hne_q : q ≠ q'.val := by
        intro heq
        subst heq
        rw [hlit] at hq'l
        simp at hq'l
      rcases lt_or_gt_of_ne hne_q with hlt | hgt
      · have hm : ((2 + q, 1), (2 + q'.val, 1)) ∈ occBans φ := by
          apply List.mem_append.mpr; left
          apply List.mem_append.mpr; right
          unfold oppBans
          apply List.mem_flatMap.mpr
          refine ⟨q, List.mem_range.mpr hq, List.mem_flatMap.mpr ⟨q'.val, List.mem_range.mpr q'.isLt, ?_⟩⟩
          have hc : q < q'.val ∧ q'.val < (occs φ).length := ⟨hlt, q'.isLt⟩
          rw [dite_eq_left hc]
          dsimp only
          rw [hlit, hq'l]
          simp
        have hv := valid_ban_at ha (by omega) (by omega) hm
        omega
      · have hm : ((2 + q'.val, 1), (2 + q, 1)) ∈ occBans φ := by
          apply List.mem_append.mpr; left
          apply List.mem_append.mpr; right
          unfold oppBans
          apply List.mem_flatMap.mpr
          refine ⟨q'.val, List.mem_range.mpr q'.isLt, List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, ?_⟩⟩
          have hc : q'.val < q ∧ q < (occs φ).length := ⟨hgt, hq⟩
          rw [dite_eq_left hc]
          dsimp only
          rw [hlit, hq'l]
          simp
        have hv := valid_ban_at ha (by omega) (by omega) hm
        omega
    · simp only [beq_iff_eq, σ, decide_eq_true_eq]
      exact ⟨⟨q, hq⟩, hlit, hqa⟩
  refine ⟨σ, ?_⟩
  rw [CNF.eval, List.all_eq_true]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hcne : φ[i] ≠ [] := hne _ (List.getElem_mem hi)
  have ⟨l, hl⟩ : ∃ l, l ∈ φ[i] := by
    cases hci : φ[i] with
    | nil => exact (hcne hci).elim
    | cons l ls => exact ⟨l, List.mem_cons_self⟩
  have hmem_occ : (i, l) ∈ occs φ := by
    simpa [occs] using occsAux_exists_clause 0 φ i hi l hl
  obtain ⟨p0, hp0, hp0_eq⟩ := List.mem_iff_getElem.mp hmem_occ
  obtain ⟨pMax, hpMax, hpMax_cl, hnot_next⟩ :=
    exists_last_in_clause φ i p0 hp0 (by simp [hp0_eq])
  have hend_mem : ((0, 0), (2 + m + pMax, 0)) ∈ occBans φ := by
    apply hauto_mem pMax hpMax
    apply List.mem_append.mpr; right
    by_cases hp1 : pMax + 1 < m
    · have hne1 : ((occs φ)[pMax]'hpMax).1 ≠ ((occs φ)[pMax + 1]'hp1).1 := by
        rw [hpMax_cl]; exact (hnot_next hp1).symm
      simp [hp1, hne1]
    · simp [hp1]
  have hv_end := valid_ban_at ha (by omega) (by omega) hend_mem
  have hne0 : (a ⟨2 + m + pMax, by omega⟩).val ≠ 0 := by omega
  obtain ⟨q, _, hqm, hqcl, hqa⟩ := hchain pMax hpMax hne0
  have hq_mem := List.getElem_mem hqm
  have hq_i : ((occs φ)[q]'hqm).1 = i := hqcl.trans hpMax_cl
  obtain ⟨_, _, hl_in⟩ := occsAux_mem_getElem 0 φ i ((occs φ)[q]'hqm).2 (by
    have : (i, ((occs φ)[q]'hqm).2) = (occs φ)[q]'hqm := Prod.ext hq_i.symm rfl
    rw [this]; exact hq_mem)
  rw [Clause.eval, List.any_eq_true]
  exact ⟨((occs φ)[q]'hqm).2, by simpa using hl_in, hlit_true q hqm hqa⟩

lemma occBans_valid_of_sat (φ : CNF) (hsat : Satisfiable φ) :
  ∃ a : Fin (2 + 2 * (occs φ).length) → Fin 3,
    S895.Comb.valid (2 + 2 * (occs φ).length) (occBans φ) a := by
  set m := (occs φ).length
  set n := 2 + 2 * m
  rcases hsat with ⟨σ, hσ⟩
  classical
  let a : Fin n → Fin 3 := fun idx =>
    if h2 : idx.val < 2 then 0
    else if hm : idx.val < 2 + m then
      let p := idx.val - 2
      if Literal.eval σ ((occs φ)[p]'(by omega)).2 then 1 else 0
    else
      let p := idx.val - (2 + m)
      if ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'(by omega)).1 ∧
          Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true then 2
      else if Literal.eval σ ((occs φ)[p]'(by omega)).2 = true then 1 else 0
  have ha0 : (a ⟨0, by omega⟩).val = 0 := by simp [a]
  have ha1 : (a ⟨1, by omega⟩).val = 0 := by simp [a]
  have ha_lit : ∀ p (hp : p < m),
      (a ⟨2 + p, by omega⟩).val = if Literal.eval σ ((occs φ)[p]'hp).2 then 1 else 0 := by
    intro p hp
    simp only [a, show ¬(2 + p < 2) by omega, show 2 + p < 2 + m by omega, ↓reduceDIte,
      Nat.add_sub_cancel_left]
    split_ifs <;> rfl
  have ha_auto : ∀ p (hp : p < m),
      (a ⟨2 + m + p, by omega⟩).val =
        if ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
            Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true then 2
        else if Literal.eval σ ((occs φ)[p]'hp).2 = true then 1 else 0 := by
    intro p hp
    simp only [a, show ¬(2 + m + p < 2) by omega, show ¬(2 + m + p < 2 + m) by omega,
      ↓reduceDIte, Nat.add_sub_cancel_left]
    split_ifs <;> rfl
  have ha_auto_ne0 : ∀ p (hp : p < m),
      (Literal.eval σ ((occs φ)[p]'hp).2 = true ∨
       ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
         Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true) →
      (a ⟨2 + m + p, by omega⟩).val ≠ 0 := by
    intro p hp h
    rw [ha_auto p hp]
    by_cases hex : ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
        Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true
    · rw [ite_eq_left hex]; decide
    · rw [ite_eq_right hex]
      rcases h with hev | hex'
      · rw [ite_eq_left hev]; decide
      · exact (hex hex').elim
  have ha_auto_ne1 : ∀ p (hp : p < m),
      (Literal.eval σ ((occs φ)[p]'hp).2 ≠ true ∨
       ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
         Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true) →
      (a ⟨2 + m + p, by omega⟩).val ≠ 1 := by
    intro p hp h
    rw [ha_auto p hp]
    by_cases hex : ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
        Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true
    · rw [ite_eq_left hex]; decide
    · rw [ite_eq_right hex]
      rcases h with hev | hex'
      · rw [ite_eq_right hev]; decide
      · exact (hex hex').elim
  have ha_auto_ne2 : ∀ p (hp : p < m),
      (¬∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
         Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true) →
      (a ⟨2 + m + p, by omega⟩).val ≠ 2 := by
    intro p hp hno
    rw [ha_auto p hp, ite_eq_right hno]
    by_cases hev : Literal.eval σ ((occs φ)[p]'hp).2 = true
    · rw [ite_eq_left hev]; decide
    · rw [ite_eq_right hev]; decide
  have ha_auto_eq2 : ∀ p (hp : p < m),
      (∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp).1 ∧
         Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true) →
      (a ⟨2 + m + p, by omega⟩).val = 2 := by
    intro p hp hex
    rw [ha_auto p hp, ite_eq_left hex]
  refine ⟨a, ?_⟩
  intro e he
  obtain ⟨hij, hjn, _, _⟩ := (occBans_legal φ).2 e he
  have hin : e.1.1 < n := by omega
  rw [S895.Comb.assignment_lookup a ⟨e.1.1, hin⟩, S895.Comb.assignment_lookup a ⟨e.2.1, hjn⟩]
  simp only [occBans, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · simp only [anchorBans, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; rw [ha0, ha1]; decide)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    have hp' := List.mem_range.mp hp
    dsimp only
    right
    rw [ha_lit p hp']
    by_cases hev : Literal.eval σ ((occs φ)[p]'hp').2 = true
    · rw [ite_eq_left hev]; decide
    · rw [ite_eq_right hev]; decide
  · obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
    by_cases hcond : p < q ∧ q < (occs φ).length
    · rw [dite_eq_left hcond] at he
      dsimp only at he
      split_ifs at he with hopp
      · simp only [List.mem_singleton] at he; subst he; dsimp only
        have hp' : p < m := by omega
        have hq' : q < m := hcond.2
        rw [ha_lit p hp', ha_lit q hq']
        by_cases hevp : Literal.eval σ ((occs φ)[p]'hp').2 = true
        · right
          have hevq : Literal.eval σ ((occs φ)[q]'hq').2 = false := by
            unfold Literal.eval at hevp ⊢
            rw [beq_iff_eq] at hevp
            rw [← hopp.1, hevp]
            cases hb1 : ((occs φ)[p]'hp').2.2 <;> cases hb2 : ((occs φ)[q]'hq').2.2 <;> simp_all
          simp [hevq]
        · left; simp [hevp]
      · simp at he
    · rw [dite_eq_right hcond] at he; simp at he
  · obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    have hp' := List.mem_range.mp hp
    simp only [hp', ↓reduceDIte, List.mem_append] at he
    rcases he with (he | he) | he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · dsimp only
        by_cases hevp : Literal.eval σ ((occs φ)[p]'hp').2 = true
        · right; exact ha_auto_ne0 p hp' (Or.inl hevp)
        · left; rw [ha_lit p hp', ite_eq_right hevp]; decide
      · dsimp only
        by_cases hevp : Literal.eval σ ((occs φ)[p]'hp').2 = true
        · left; rw [ha_lit p hp', ite_eq_left hevp]; decide
        · right; exact ha_auto_ne1 p hp' (Or.inl hevp)
    · split_ifs at he with h0 hdiff
      · simp only [List.mem_singleton] at he; subst he; dsimp only
        right
        exact ha_auto_ne2 p hp' (fun ⟨q, hql, _⟩ => by omega)
      · simp only [List.mem_singleton] at he; subst he; dsimp only
        right
        apply ha_auto_ne2 p hp'
        rintro ⟨q, hql, hqcl, _⟩
        have h1 := occs_mono φ q.val (p - 1) q.isLt (by omega) (by omega)
        have h2 := occs_mono φ (p - 1) p (by omega) hp' (by omega)
        omega
      · simp at he
    · split_ifs at he with hp1 hsame
      · have hidx_eq : (⟨2 + m + p + 1, by omega⟩ : Fin n) = ⟨2 + m + (p + 1), by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl
        · dsimp only; rw [hidx_eq]
          by_cases hex : ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp').1 ∧
              Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true
          · left; exact ha_auto_ne0 p hp' (Or.inr hex)
          · by_cases hevp : Literal.eval σ ((occs φ)[p]'hp').2 = true
            · left; exact ha_auto_ne0 p hp' (Or.inl hevp)
            · right
              apply ha_auto_ne2 (p + 1) hp1
              rintro ⟨q, hql, hqcl, hqev⟩
              by_cases hqp : q.val < p
              · exact hex ⟨q, hqp, hqcl.trans hsame.symm, hqev⟩
              · have hqe : q.val = p := by omega
                have : ((occs φ)[q.val]'q.isLt).2 = ((occs φ)[p]'hp').2 := by congr 2
                rw [this] at hqev; exact hevp hqev
        · dsimp only; rw [hidx_eq]
          by_cases hevp : Literal.eval σ ((occs φ)[p]'hp').2 = true
          · right
            have h2 := ha_auto_eq2 (p + 1) hp1 ⟨⟨p, hp'⟩, Nat.lt_succ_self p, hsame, hevp⟩
            omega
          · left; exact ha_auto_ne1 p hp' (Or.inl hevp)
        · dsimp only; rw [hidx_eq]
          by_cases hevp : Literal.eval σ ((occs φ)[p]'hp').2 = true
          · right
            have h2 := ha_auto_eq2 (p + 1) hp1 ⟨⟨p, hp'⟩, Nat.lt_succ_self p, hsame, hevp⟩
            omega
          · left; exact ha_auto_ne1 p hp' (Or.inl hevp)
        · dsimp only; rw [hidx_eq]
          by_cases hex : ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp').1 ∧
              Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true
          · right
            obtain ⟨q, hql, hqcl, hqev⟩ := hex
            have h2 := ha_auto_eq2 (p + 1) hp1 ⟨q, by omega, hqcl.trans hsame, hqev⟩
            omega
          · left; exact ha_auto_ne2 p hp' hex
        · dsimp only; rw [hidx_eq]
          by_cases hex : ∃ q : Fin m, q.val < p ∧ ((occs φ)[q.val]'q.isLt).1 = ((occs φ)[p]'hp').1 ∧
              Literal.eval σ ((occs φ)[q.val]'q.isLt).2 = true
          · right
            obtain ⟨q, hql, hqcl, hqev⟩ := hex
            have h2 := ha_auto_eq2 (p + 1) hp1 ⟨q, by omega, hqcl.trans hsame, hqev⟩
            omega
          · left; exact ha_auto_ne2 p hp' hex
      · simp only [List.mem_singleton] at he; subst he; dsimp only
        right
        set ci := ((occs φ)[p]'hp').1
        obtain ⟨hci, _, _⟩ := occsAux_mem_getElem 0 φ ci ((occs φ)[p]'hp').2 (List.getElem_mem hp')
        have hcl_sat : Clause.eval σ (φ[ci]'(by simpa using hci)) = true := by
          rw [CNF.eval, List.all_eq_true] at hσ
          exact hσ _ (List.getElem_mem (by simpa using hci))
        rw [Clause.eval, List.any_eq_true] at hcl_sat
        obtain ⟨l, hl_in, hl_ev⟩ := hcl_sat
        have hocc_l : (ci, l) ∈ occs φ := by
          simpa [occs] using occsAux_exists_clause 0 φ ci (by simpa using hci) l hl_in
        obtain ⟨q, hqm, hq_eq⟩ := List.mem_iff_getElem.mp hocc_l
        have hq_le : q ≤ p := by
          by_contra hgt
          have h1 := occs_mono φ p (p + 1) hp' hp1 (by omega)
          have h2 := occs_mono φ (p + 1) q hp1 hqm (by omega)
          have hq1 : ((occs φ)[q]'hqm).1 = ci := by simp [hq_eq]
          omega
        by_cases hqlt : q < p
        · exact ha_auto_ne0 p hp' (Or.inr ⟨⟨q, hqm⟩, hqlt, by simp [hq_eq, ci], by simp [hq_eq, hl_ev]⟩)
        · have hqeq : q = p := by omega
          subst hqeq
          exact ha_auto_ne0 q hp' (Or.inl (by simp [hq_eq, hl_ev]))
      · simp only [List.mem_singleton] at he; subst he; dsimp only
        right
        set ci := ((occs φ)[p]'hp').1
        obtain ⟨hci, _, _⟩ := occsAux_mem_getElem 0 φ ci ((occs φ)[p]'hp').2 (List.getElem_mem hp')
        have hcl_sat : Clause.eval σ (φ[ci]'(by simpa using hci)) = true := by
          rw [CNF.eval, List.all_eq_true] at hσ
          exact hσ _ (List.getElem_mem (by simpa using hci))
        rw [Clause.eval, List.any_eq_true] at hcl_sat
        obtain ⟨l, hl_in, hl_ev⟩ := hcl_sat
        have hocc_l : (ci, l) ∈ occs φ := by
          simpa [occs] using occsAux_exists_clause 0 φ ci (by simpa using hci) l hl_in
        obtain ⟨q, hqm, hq_eq⟩ := List.mem_iff_getElem.mp hocc_l
        have hq_le : q ≤ p := by omega
        by_cases hqlt : q < p
        · exact ha_auto_ne0 p hp' (Or.inr ⟨⟨q, hqm⟩, hqlt, by simp [hq_eq, ci], by simp [hq_eq, hl_ev]⟩)
        · have hqeq : q = p := by omega
          subst hqeq
          exact ha_auto_ne0 q hp' (Or.inl (by simp [hq_eq, hl_ev]))

lemma occBans_sat_iff (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    (∃ a : Fin (2 + 2 * (occs φ).length) → Fin 3,
      S895.Comb.valid (2 + 2 * (occs φ).length) (occBans φ) a) ↔ Satisfiable φ :=
  ⟨occBans_sat_of_valid φ hne, occBans_valid_of_sat φ⟩

lemma flatMap_flatMap_aux {α β γ : Type*} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap (fun a => (f a).flatMap g) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, List.flatMap_append, ih]

lemma cpt_flatMap_list {α : Type} (L : List α) (f : α → List Bool → List Bool)
    (hf : ∀ a ∈ L, CPTs (f a)) : CPTs (fun s => L.flatMap (fun a => f a s)) := by
  induction L with
  | nil => exact cpt_const []
  | cons a as ih =>
    exact cpt_app2 (hf a List.mem_cons_self) (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

def emitFlagU (uW uI uC : List Bool) : List Bool :=
  let uEven := un 2 ++ mulU (un 8) uI ++ mulU (un 2) uC
  bitsU uW uEven ++ bitsU uW (true :: uEven)

lemma cpt_emitFlagU {fw fi fc : List Bool → List Bool}
    (hw : CPTs fw) (hi : CPTs fi) (hc : CPTs fc) :
    CPTs (fun s => emitFlagU (fw s) (fi s) (fc s)) := by
  have huEven := cpt_app2 (cpt_app2 (cpt_const (un 2)) (cpt_mulU2 (cpt_const (un 8)) hi))
    (cpt_mulU2 (cpt_const (un 2)) hc)
  exact cpt_app2 (cpt_bitsU hw huEven) (cpt_bitsU hw (cpt_cons1 true huEven))

lemma emitFlagU_un (w i c : Nat) :
    emitFlagU (un w) (un i) (un c) = (S895.Comb.flag i c).flatMap (bits w) := by
  unfold emitFlagU S895.Comb.flag
  simp only [mulU, un_length, un_append_un, ← un_succ, bitsU_un,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 2 <;> omega

def emitBanU (uW uI uCI uJ uCJ : List Bool) : List Bool :=
  emitFlagU uW uI uCI ++ emitFlagU uW uJ uCJ

lemma cpt_emitBanU {fw fi fci fj fcj : List Bool → List Bool}
    (hw : CPTs fw) (hi : CPTs fi) (hci : CPTs fci) (hj : CPTs fj) (hcj : CPTs fcj) :
    CPTs (fun s => emitBanU (fw s) (fi s) (fci s) (fj s) (fcj s)) :=
  cpt_app2 (cpt_emitFlagU hw hi hci) (cpt_emitFlagU hw hj hcj)

lemma emitBanU_un (w i ci j cj : Nat) :
    emitBanU (un w) (un i) (un ci) (un j) (un cj) =
      (S895.Comb.flag i ci ++ S895.Comb.flag j cj).flatMap (bits w) := by
  unfold emitBanU
  rw [emitFlagU_un, emitFlagU_un, List.flatMap_append]

lemma emitBanU_un' (w i ci j cj : Nat) :
    emitBanU (un w) (un i) (un ci) (un j) (un cj) =
      (S895.Comb.flag i ci).flatMap (bits w) ++ (S895.Comb.flag j cj).flatMap (bits w) := by
  rw [emitBanU_un, List.flatMap_append]

def emitBlockU (y : List Bool) : List Bool :=
  let uI := (unpairB y).1
  let r := (unpairB y).2
  let uN := (unpairB r).1
  let uW := (unpairB r).2
  let u8i := mulU (un 8) uI
  let uNext := sel (eqF (true :: uI) uN) (true :: uI) []
  let u8next := mulU (un 8) uNext
  let orient := bitsU uW u8i ++ bitsU uW (u8i ++ un 2) ++
    bitsU uW (u8i ++ un 4) ++ bitsU uW (u8i ++ un 6)
  let tris := (List.range 3).flatMap fun c =>
    (List.range 2).flatMap fun b =>
      (List.range 4).flatMap fun j =>
        bitsU uW (u8i ++ un b) ++ emitFlagU uW uI (un c) ++ bitsU uW (u8next ++ un j)
  orient ++ tris

lemma cpt_emitBlockU : CPTs emitBlockU := by
  have huI := cpt_unpairB1
  have hr := cpt_unpairB2
  have huN := cpt_unpairB1_1 hr
  have huW := cpt_unpairB2_1 hr
  have hu8i := cpt_mulU2 (cpt_const (un 8)) huI
  have huNext := cpt_sel (cpt_eqF' (cpt_cons1 true huI) huN) (cpt_cons1 true huI) (cpt_const [])
  have hu8next := cpt_mulU2 (cpt_const (un 8)) huNext
  have horient := cpt_app2 (cpt_app2 (cpt_app2 (cpt_bitsU huW hu8i)
    (cpt_bitsU huW (cpt_app2 hu8i (cpt_const (un 2)))))
    (cpt_bitsU huW (cpt_app2 hu8i (cpt_const (un 4)))))
    (cpt_bitsU huW (cpt_app2 hu8i (cpt_const (un 6))))
  have htris : CPTs (fun y =>
      let uI := (unpairB y).1
      let r := (unpairB y).2
      let uN := (unpairB r).1
      let uW := (unpairB r).2
      let u8i := mulU (un 8) uI
      let uNext := sel (eqF (true :: uI) uN) (true :: uI) []
      let u8next := mulU (un 8) uNext
      (List.range 3).flatMap fun c =>
        (List.range 2).flatMap fun b =>
          (List.range 4).flatMap fun j =>
            bitsU uW (u8i ++ un b) ++ emitFlagU uW uI (un c) ++ bitsU uW (u8next ++ un j)) := by
    refine cpt_flatMap_list (List.range 3) _ (fun c _ => ?_)
    refine cpt_flatMap_list (List.range 2) _ (fun b _ => ?_)
    refine cpt_flatMap_list (List.range 4) _ (fun j _ => ?_)
    exact cpt_app2 (cpt_app2 (cpt_bitsU huW (cpt_app2 hu8i (cpt_const (un b))))
      (cpt_emitFlagU huW huI (cpt_const (un c))))
      (cpt_bitsU huW (cpt_app2 hu8next (cpt_const (un j))))
  exact cpt_app2 horient htris

lemma emitBlockU_un (w n i : Nat) (hi : i < n) :
    emitBlockU (pairB (un i) (pairB (un n) (un w))) =
      (S895.Comb.block n i).flatMap (fun row => row.flatMap (bits w)) := by
  unfold emitBlockU S895.Comb.block
  simp only [unpairB_pairB, List.flatMap_append, List.flatMap_singleton]
  have hnext : sel (eqF (true :: un i) (un n)) (true :: un i) [] = un ((i + 1) % n) := by
    rw [← un_succ]
    by_cases h : i + 1 = n
    · rw [h, Nat.mod_self]
      simp [eqF, bflag, sel, un]
    · have hlt : i + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hne : un (i + 1) ≠ un n := fun heq => h (un_inj heq)
      simp [eqF, hne, bflag, sel]
  rw [hnext]
  congr 1
  · simp [mulU, un_length, un_append_un, bitsU_un, List.append_assoc]
  · simp only [flatMap_flatMap_aux, List.flatMap_map]
    apply List.flatMap_congr; intro c _
    apply List.flatMap_congr; intro b _
    apply List.flatMap_congr; intro j _
    simp [mulU, un_length, un_append_un, bitsU_un, emitFlagU_un, List.flatMap_append,
      List.append_assoc]

def emitBlocksU (uN uW : List Bool) : List Bool :=
  (List.range uN.length).flatMap fun i =>
    emitBlockU (pairB (un i) (pairB uN uW))

lemma cpt_emitBlocksU {fn fw : List Bool → List Bool} (hn : CPTs fn) (hw : CPTs fw) :
    CPTs (fun s => emitBlocksU (fn s) (fw s)) :=
  cpt_flatMapRange cpt_emitBlockU hn (cpt_pairB2 hn hw)

lemma emitBlocksU_un (w n : Nat) :
    emitBlocksU (un n) (un w) =
      ((List.range n).flatMap (S895.Comb.block n)).flatMap (fun row => row.flatMap (bits w)) := by
  unfold emitBlocksU
  rw [un_length, flatMap_flatMap_aux]
  apply List.flatMap_congr; intro i hi
  exact emitBlockU_un w n i (List.mem_range.mp hi)

def emitAnchorBansU (uW : List Bool) : List Bool :=
  anchorBans.flatMap fun e => emitBanU uW (un e.1.1) (un e.1.2) (un e.2.1) (un e.2.2)

lemma cpt_emitAnchorBansU {fw : List Bool → List Bool} (hw : CPTs fw) :
    CPTs (fun s => emitAnchorBansU (fw s)) :=
  cpt_flatMap_list anchorBans _ (fun _ _ =>
    cpt_emitBanU hw (cpt_const _) (cpt_const _) (cpt_const _) (cpt_const _))

lemma emitAnchorBansU_un (w : Nat) :
    emitAnchorBansU (un w) =
      (anchorBans.map (fun e => S895.Comb.flag e.1.1 e.1.2 ++ S895.Comb.flag e.2.1 e.2.2)).flatMap
        (fun row => row.flatMap (bits w)) := by
  unfold emitAnchorBansU
  rw [List.flatMap_map]
  apply List.flatMap_congr; intro e _
  exact emitBanU_un w e.1.1 e.1.2 e.2.1 e.2.2

def emitBoolBanStep (y : List Bool) : List Bool :=
  let uP := (unpairB y).1
  let uW := (unpairB y).2
  emitBanU uW (un 0) (un 0) (un 2 ++ uP) (un 2)

lemma cpt_emitBoolBanStep : CPTs emitBoolBanStep :=
  cpt_emitBanU cpt_unpairB2 (cpt_const (un 0)) (cpt_const (un 0))
    (cpt_app2 (cpt_const (un 2)) cpt_unpairB1) (cpt_const (un 2))

def emitBoolBansU (uM uW : List Bool) : List Bool :=
  (List.range uM.length).flatMap fun p =>
    emitBoolBanStep (pairB (un p) uW)

lemma cpt_emitBoolBansU {fm fw : List Bool → List Bool} (hm : CPTs fm) (hw : CPTs fw) :
    CPTs (fun s => emitBoolBansU (fm s) (fw s)) :=
  cpt_flatMapRange cpt_emitBoolBanStep hm hw

lemma emitBoolBansU_un (w m : Nat) :
    emitBoolBansU (un m) (un w) =
      ((boolBans m).map (fun e => S895.Comb.flag e.1.1 e.1.2 ++ S895.Comb.flag e.2.1 e.2.2)).flatMap
        (fun row => row.flatMap (bits w)) := by
  unfold emitBoolBansU boolBans
  rw [un_length, List.map_map, List.flatMap_map]
  apply List.flatMap_congr; intro p _
  simp only [emitBoolBanStep, unpairB_pairB, un_append_un, Function.comp_def]
  exact emitBanU_un w 0 0 (2 + p) 2

def emitOppQ (y : List Bool) : List Bool :=
  let uQ := (unpairB y).1
  let r1 := (unpairB y).2
  let uP := (unpairB r1).1
  let r2 := (unpairB r1).2
  let s := (unpairB r2).1
  let uW := (unpairB r2).2
  let litP := headI (unpairB (occState s uP)).1
  let litQ := headI (unpairB (occState s uQ)).1
  let varP := litP.tail.tail
  let varQ := litQ.tail.tail
  let polP := bflag (polB litP)
  let polQ := bflag (polB litQ)
  let cond := andF (ltU uP uQ) (andF (eqF varP varQ) (xorF polP polQ))
  sel cond [] (emitBanU uW (un 2 ++ uP) (un 1) (un 2 ++ uQ) (un 1))

lemma cpt_emitOppQ : CPTs emitOppQ := by
  have huQ := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huP := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hs := cpt_unpairB1_1 hr2
  have huW := cpt_unpairB2_1 hr2
  have hlitP := cpt_comp (cpt_unpairB1_1 (cpt_occState hs huP)) cpt_headI
  have hlitQ := cpt_comp (cpt_unpairB1_1 (cpt_occState hs huQ)) cpt_headI
  have hvarP := cpt_tail1 (cpt_tail1 hlitP)
  have hvarQ := cpt_tail1 (cpt_tail1 hlitQ)
  have hpolP := cpt_comp hlitP cpt_polF
  have hpolQ := cpt_comp hlitQ cpt_polF
  have hcond := cpt_andF (cpt_ltU huP huQ) (cpt_andF (cpt_eqF' hvarP hvarQ) (cpt_xorF hpolP hpolQ))
  exact cpt_sel hcond (cpt_const [])
    (cpt_emitBanU huW (cpt_app2 (cpt_const (un 2)) huP) (cpt_const (un 1))
      (cpt_app2 (cpt_const (un 2)) huQ) (cpt_const (un 1)))

def emitOppP (y : List Bool) : List Bool :=
  let uP := (unpairB y).1
  let r1 := (unpairB y).2
  let uM := (unpairB r1).1
  let r2 := (unpairB r1).2
  (List.range uM.length).flatMap fun q =>
    emitOppQ (pairB (un q) (pairB uP r2))

lemma cpt_emitOppP : CPTs emitOppP :=
  cpt_flatMapRange cpt_emitOppQ
    (cpt_unpairB1_1 cpt_unpairB2)
    (cpt_pairB2 cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2))

def emitOppBansU (s uM uW : List Bool) : List Bool :=
  (List.range uM.length).flatMap fun p =>
    emitOppP (pairB (un p) (pairB uM (pairB s uW)))

lemma cpt_emitOppBansU {fs fm fw : List Bool → List Bool}
    (hs : CPTs fs) (hm : CPTs fm) (hw : CPTs fw) :
    CPTs (fun y => emitOppBansU (fs y) (fm y) (fw y)) :=
  cpt_flatMapRange cpt_emitOppP hm (cpt_pairB2 hm (cpt_pairB2 hs hw))

lemma emitOppBansU_cnf (w : Nat) (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    emitOppBansU (encodeCNF φ) (un (occs φ).length) (un w) =
      ((oppBans φ).map (fun e => S895.Comb.flag e.1.1 e.1.2 ++ S895.Comb.flag e.2.1 e.2.2)).flatMap
        (fun row => row.flatMap (bits w)) := by
  unfold emitOppBansU oppBans
  dsimp only
  rw [un_length, List.flatMap_map, flatMap_flatMap_aux]
  apply List.flatMap_congr; intro p hp
  have hp' := List.mem_range.mp hp
  simp only [emitOppP, unpairB_pairB, un_length, flatMap_flatMap_aux]
  apply List.flatMap_congr; intro q hq
  have hq' := List.mem_range.mp hq
  simp only [emitOppQ, unpairB_pairB]
  obtain ⟨hlP, _⟩ := occState_spec φ hne ⟨p, hp'⟩
  obtain ⟨hlQ, _⟩ := occState_spec φ hne ⟨q, hq'⟩
  rw [hlP, hlQ, encodeLiteral_eq, encodeLiteral_eq]
  simp only [List.tail_cons, polB, ltU_un, List.get_eq_getElem]
  have hvar : eqF (vcode ((occs φ)[p]'hp').2.1) (vcode ((occs φ)[q]'hq').2.1) =
      bflag (decide (((occs φ)[p]'hp').2.1 = ((occs φ)[q]'hq').2.1)) := by
    unfold eqF; congr 1; simp only [decide_eq_decide]
    exact ⟨fun h => vcode_injective h, fun h => by rw [h]⟩
  rw [hvar, xorF_bflag, andF_bflag, andF_bflag]
  by_cases hpq : p < q
  · have hc : p < q ∧ q < (occs φ).length := ⟨hpq, hq'⟩
    rw [dite_eq_left hc]
    by_cases hopp : ((occs φ)[p]'hp').2.1 = ((occs φ)[q]'hq').2.1 ∧
        ((occs φ)[p]'hp').2.2 ≠ ((occs φ)[q]'hq').2.2
    · have hcond : (decide (p < q) && (decide (((occs φ)[p]'hp').2.1 = ((occs φ)[q]'hq').2.1) &&
          xor ((occs φ)[p]'hp').2.2 ((occs φ)[q]'hq').2.2)) = true := by
        cases h1 : ((occs φ)[p]'hp').2.2 <;> cases h2 : ((occs φ)[q]'hq').2.2 <;> simp_all
      rw [hcond, ite_eq_left hopp]
      simp only [bflag, sel, reduceCtorEq, ↓reduceIte, List.flatMap_singleton]
      rw [un_append_un, un_append_un, emitBanU_un]
    · have hcond : (decide (p < q) && (decide (((occs φ)[p]'hp').2.1 = ((occs φ)[q]'hq').2.1) &&
          xor ((occs φ)[p]'hp').2.2 ((occs φ)[q]'hq').2.2)) = false := by
        cases h1 : ((occs φ)[p]'hp').2.2 <;> cases h2 : ((occs φ)[q]'hq').2.2 <;> simp_all
      rw [hcond]
      simp [hopp, bflag, sel]
  · have hc : ¬(p < q ∧ q < (occs φ).length) := fun h => hpq h.1
    rw [dite_eq_right hc]
    simp [hpq, bflag, sel]

def emitClauseAutoStep (y : List Bool) : List Bool :=
  let uP := (unpairB y).1
  let r1 := (unpairB y).2
  let s := (unpairB r1).1
  let r2 := (unpairB r1).2
  let uM := (unpairB r2).1
  let uW := (unpairB r2).2
  let uU := un 2 ++ uM ++ uP
  let uU1 := true :: uU
  let clP := (unpairB (occState s uP)).2
  let clPrev := (unpairB (occState s uP.tail)).2
  let clNext := (unpairB (occState s (true :: uP))).2
  let part1 := emitBanU uW (un 2 ++ uP) (un 1) uU (un 0) ++
    emitBanU uW (un 2 ++ uP) (un 0) uU (un 1)
  let isStart := orF (notF uP) (notF (eqF clPrev clP))
  let part2 := sel isStart [] (emitBanU uW (un 0) (un 0) uU (un 2))
  let sameNext := andF (ltU (true :: uP) uM) (eqF clP clNext)
  let trans := emitBanU uW uU (un 0) uU1 (un 2) ++
    emitBanU uW uU (un 1) uU1 (un 0) ++
    emitBanU uW uU (un 1) uU1 (un 1) ++
    emitBanU uW uU (un 2) uU1 (un 0) ++
    emitBanU uW uU (un 2) uU1 (un 1)
  let part3 := sel sameNext (emitBanU uW (un 0) (un 0) uU (un 0)) trans
  part1 ++ part2 ++ part3

lemma cpt_emitClauseAutoStep : CPTs emitClauseAutoStep := by
  have huP := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have hs := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have huM := cpt_unpairB1_1 hr2
  have huW := cpt_unpairB2_1 hr2
  have huU := cpt_app2 (cpt_app2 (cpt_const (un 2)) huM) huP
  have huU1 := cpt_cons1 true huU
  have hclP := cpt_unpairB2_1 (cpt_occState hs huP)
  have hclPrev := cpt_unpairB2_1 (cpt_occState hs (cpt_tail1 huP))
  have hclNext := cpt_unpairB2_1 (cpt_occState hs (cpt_cons1 true huP))
  have hpart1 := cpt_app2
    (cpt_emitBanU huW (cpt_app2 (cpt_const (un 2)) huP) (cpt_const (un 1)) huU (cpt_const (un 0)))
    (cpt_emitBanU huW (cpt_app2 (cpt_const (un 2)) huP) (cpt_const (un 0)) huU (cpt_const (un 1)))
  have hisStart := cpt_orF (cpt_notF huP) (cpt_notF (cpt_eqF' hclPrev hclP))
  have hpart2 := cpt_sel hisStart (cpt_const [])
    (cpt_emitBanU huW (cpt_const (un 0)) (cpt_const (un 0)) huU (cpt_const (un 2)))
  have hsameNext := cpt_andF (cpt_ltU (cpt_cons1 true huP) huM) (cpt_eqF' hclP hclNext)
  have htrans := cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2
    (cpt_emitBanU huW huU (cpt_const (un 0)) huU1 (cpt_const (un 2)))
    (cpt_emitBanU huW huU (cpt_const (un 1)) huU1 (cpt_const (un 0))))
    (cpt_emitBanU huW huU (cpt_const (un 1)) huU1 (cpt_const (un 1))))
    (cpt_emitBanU huW huU (cpt_const (un 2)) huU1 (cpt_const (un 0))))
    (cpt_emitBanU huW huU (cpt_const (un 2)) huU1 (cpt_const (un 1)))
  have hpart3 := cpt_sel hsameNext
    (cpt_emitBanU huW (cpt_const (un 0)) (cpt_const (un 0)) huU (cpt_const (un 0)))
    htrans
  exact cpt_app2 (cpt_app2 hpart1 hpart2) hpart3

def emitClauseAutoBansU (s uM uW : List Bool) : List Bool :=
  (List.range uM.length).flatMap fun p =>
    emitClauseAutoStep (pairB (un p) (pairB s (pairB uM uW)))

lemma cpt_emitClauseAutoBansU {fs fm fw : List Bool → List Bool}
    (hs : CPTs fs) (hm : CPTs fm) (hw : CPTs fw) :
    CPTs (fun y => emitClauseAutoBansU (fs y) (fm y) (fw y)) :=
  cpt_flatMapRange cpt_emitClauseAutoStep hm (cpt_pairB2 hs (cpt_pairB2 hm hw))

lemma emitClauseAutoBansU_cnf (w : Nat) (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    emitClauseAutoBansU (encodeCNF φ) (un (occs φ).length) (un w) =
      ((clauseAutoBans φ).map (fun e => S895.Comb.flag e.1.1 e.1.2 ++ S895.Comb.flag e.2.1 e.2.2)).flatMap
        (fun row => row.flatMap (bits w)) := by
  unfold emitClauseAutoBansU clauseAutoBans
  dsimp only
  rw [un_length, List.flatMap_map, flatMap_flatMap_aux]
  apply List.flatMap_congr; intro p hp
  have hp' := List.mem_range.mp hp
  simp only [emitClauseAutoStep, unpairB_pairB, hp', ↓reduceDIte,
    List.flatMap_append, un_append_un, ← un_succ]
  have hclP := (occState_spec φ hne ⟨p, hp'⟩).2
  simp only [List.get_eq_getElem] at hclP
  rw [hclP]
  congr 1
  · congr 1
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact congrArg₂ (· ++ ·) (emitBanU_un' w (2 + p) 1 (2 + (occs φ).length + p) 0)
        (emitBanU_un' w (2 + p) 0 (2 + (occs φ).length + p) 1)
    · by_cases h0 : p = 0
      · subst h0
        rw [dite_eq_left rfl]
        have hnot0 : notF (un 0) = [true] := rfl
        rw [hnot0]
        change emitBanU (un w) (un 0) (un 0) (un (2 + (occs φ).length + 0)) (un 2) = _
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact emitBanU_un' w 0 0 (2 + (occs φ).length + 0) 2
      · have hp_pred : p - 1 < (occs φ).length := by omega
        have htail : (un p).tail = un (p - 1) := by
          cases p with
          | zero => exact (h0 rfl).elim
          | succ p' => simp [un, List.replicate_succ]
        have hclPrev := (occState_spec φ hne ⟨p - 1, hp_pred⟩).2
        simp only [List.get_eq_getElem] at hclPrev
        rw [htail, hclPrev]
        have hnotP : notF (un p) = [] := by
          cases p with
          | zero => exact (h0 rfl).elim
          | succ p' => simp [un, List.replicate_succ, notF, sel]
        rw [hnotP]
        by_cases hdiff : ((occs φ)[p - 1]'hp_pred).1 ≠ ((occs φ)[p]'hp').1
        · have hne_un : un ((occs φ)[p - 1]'hp_pred).1 ≠ un ((occs φ)[p]'hp').1 :=
            fun heq => hdiff (un_inj heq)
          have heq_nil : eqF (un ((occs φ)[p - 1]'hp_pred).1) (un ((occs φ)[p]'hp').1) = [] := by
            simp [eqF, hne_un, bflag]
          rw [dite_eq_right h0, ite_eq_left hdiff, heq_nil]
          change emitBanU (un w) (un 0) (un 0) (un (2 + (occs φ).length + p)) (un 2) = _
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact emitBanU_un' w 0 0 (2 + (occs φ).length + p) 2
        · push_neg at hdiff
          simp [h0, hdiff, eqF, bflag, notF, orF, sel]
  · rw [ltU_un]
    by_cases hp1 : p + 1 < (occs φ).length
    · have hclNext := (occState_spec φ hne ⟨p + 1, hp1⟩).2
      simp only [List.get_eq_getElem] at hclNext
      rw [hclNext]
      by_cases hsame : ((occs φ)[p]'hp').1 = ((occs φ)[p + 1]'hp1).1
      · have hcond : andF (bflag (decide (p + 1 < (occs φ).length)))
            (eqF (un ((occs φ)[p]'hp').1) (un ((occs φ)[p + 1]'hp1).1)) = [true] := by
          rw [eqF, andF_bflag]; simp [hp1, hsame, bflag]
        rw [dite_eq_left hp1, ite_eq_left hsame, hcond]
        change emitBanU (un w) (un (2 + (occs φ).length + p)) (un 0) (un (2 + (occs φ).length + p + 1)) (un 2) ++
          emitBanU (un w) (un (2 + (occs φ).length + p)) (un 1) (un (2 + (occs φ).length + p + 1)) (un 0) ++
          emitBanU (un w) (un (2 + (occs φ).length + p)) (un 1) (un (2 + (occs φ).length + p + 1)) (un 1) ++
          emitBanU (un w) (un (2 + (occs φ).length + p)) (un 2) (un (2 + (occs φ).length + p + 1)) (un 0) ++
          emitBanU (un w) (un (2 + (occs φ).length + p)) (un 2) (un (2 + (occs φ).length + p + 1)) (un 1) = _
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, emitBanU_un', List.append_assoc]
      · have hne_un : un ((occs φ)[p]'hp').1 ≠ un ((occs φ)[p + 1]'hp1).1 :=
          fun heq => hsame (un_inj heq)
        have hcond : andF (bflag (decide (p + 1 < (occs φ).length)))
            (eqF (un ((occs φ)[p]'hp').1) (un ((occs φ)[p + 1]'hp1).1)) = [] := by
          rw [eqF, andF_bflag]; simp [hp1, hne_un, bflag]
        rw [dite_eq_left hp1, ite_eq_right hsame, hcond]
        change emitBanU (un w) (un 0) (un 0) (un (2 + (occs φ).length + p)) (un 0) = _
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact emitBanU_un' w 0 0 (2 + (occs φ).length + p) 0
    · have hcond : andF (bflag (decide (p + 1 < (occs φ).length)))
          (eqF (un ((occs φ)[p]'hp').1)
            (unpairB (occState (encodeCNF φ) (un (p + 1)))).2) = [] := by
        simp [hp1, bflag, andF, sel]
      rw [dite_eq_right hp1, hcond]
      change emitBanU (un w) (un 0) (un 0) (un (2 + (occs φ).length + p)) (un 0) = _
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact emitBanU_un' w 0 0 (2 + (occs φ).length + p) 0

def buildInst (s : List Bool) : List Bool :=
  let uM := countLits s
  let uN := un 2 ++ uM ++ uM
  let uK := true :: mulU (un 8) uN
  let uW := widthU uK
  (uK ++ [false]) ++ emitBlocksU uN uW ++
    emitAnchorBansU uW ++ emitBoolBansU uM uW ++
    emitOppBansU s uM uW ++ emitClauseAutoBansU s uM uW

lemma cpt_buildInst : CPTs buildInst := by
  have huM := cpt_countLits
  have huN := cpt_app2 (cpt_app2 (cpt_const (un 2)) huM) huM
  have huK := cpt_cons1 true (cpt_mulU2 (cpt_const (un 8)) huN)
  have huW := cpt_widthU1 huK
  exact cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2
    (cpt_app2 huK (cpt_const [false]))
    (cpt_emitBlocksU huN huW))
    (cpt_emitAnchorBansU huW))
    (cpt_emitBoolBansU huM huW))
    (cpt_emitOppBansU cpt_id huM huW))
    (cpt_emitClauseAutoBansU cpt_id huM huW)

lemma buildInst_cnf (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    buildInst (encodeCNF φ) =
      pack (8 * (2 + 2 * (occs φ).length) + 1)
        (S895.Comb.emit (2 + 2 * (occs φ).length) (occBans φ)) := by
  unfold buildInst
  dsimp only
  rw [countLits_cnf]
  have huN : un 2 ++ un (occs φ).length ++ un (occs φ).length =
      un (2 + 2 * (occs φ).length) := by
    rw [un_append_un, un_append_un]; apply congrArg un; omega
  have huK : true :: mulU (un 8) (un (2 + 2 * (occs φ).length)) =
      un (8 * (2 + 2 * (occs φ).length) + 1) := by
    simp [mulU, un_length, un_succ]
  rw [huN, huK, widthU_un, emitBlocksU_un, emitAnchorBansU_un, emitBoolBansU_un,
    emitOppBansU_cnf _ φ hne, emitClauseAutoBansU_cnf _ φ hne]
  unfold pack S895.Comb.pack S895.Comb.header S895.Comb.emit occBans
  simp only [un, List.map_append, List.flatMap_append, List.append_assoc]

def reduce (s : List Bool) : List Bool :=
  sel (wfNoEmptyF s) [] (buildInst s)

lemma cpt_reduce : CPTs reduce :=
  cpt_sel cpt_wfNoEmptyF (cpt_const []) cpt_buildInst

lemma nil_not_mem_lang : [] ∉ lang := by
  rintro ⟨k, rows, _, hp, _⟩
  have hl := congrArg List.length hp
  unfold pack S895.Comb.pack at hl
  rw [List.length_append, S895.Comb.header_length] at hl
  simp at hl

lemma reduce_iff (s : List Bool) : s ∈ SAT ↔ reduce s ∈ lang := by
  by_cases hwf : wfNoEmptyB s = true
  · obtain ⟨φ, rfl, hne⟩ := (wfNoEmptyB_iff s).mp hwf
    have hred : reduce (encodeCNF φ) =
        pack (8 * (2 + 2 * (occs φ).length) + 1)
          (S895.Comb.emit (2 + 2 * (occs φ).length) (occBans φ)) := by
      unfold reduce wfNoEmptyF
      rw [hwf]
      simpa [bflag, sel] using buildInst_cnf φ hne
    rw [hred]
    have hleg := occBans_legal φ
    have hwell := S895.Comb.emit_well _ _ hleg
    have hsat_iff : encodeCNF φ ∈ SAT ↔ Satisfiable φ := by
      constructor
      · rintro ⟨ψ, hψ, hsat⟩
        rwa [encodeCNF_injective hψ] at hsat
      · intro hsat; exact ⟨φ, rfl, hsat⟩
    rw [hsat_iff, ← occBans_sat_iff φ hne]
    obtain ⟨E⟩ := S895.emitted_bijection (occBans φ) hleg
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨_, _, hwell, rfl, (E ⟨a, ha⟩).1, (E ⟨a, ha⟩).2⟩
    · rintro ⟨k', rows', hw', hp, P', hwins'⟩
      obtain ⟨rfl, rfl⟩ := pack_well_inj hw' hwell hp
      exact ⟨(E.symm ⟨P', hwins'⟩).1, (E.symm ⟨P', hwins'⟩).2⟩
  · have hwfF : wfNoEmptyB s = false := by cases h : wfNoEmptyB s <;> simp_all
    have hred : reduce s = [] := by
      unfold reduce wfNoEmptyF
      rw [hwfF]; rfl
    rw [hred]
    constructor
    · rintro ⟨φ, rfl, σ, hσ⟩
      have hne : ∀ c ∈ φ, c ≠ [] := by
        intro c hc heq
        subst heq
        rw [CNF.eval, List.all_eq_true] at hσ
        have := hσ [] hc
        simp [Clause.eval] at this
      have := (wfNoEmptyB_iff (encodeCNF φ)).mpr ⟨φ, rfl, hne⟩
      rw [hwfF] at this
      simp at this
    · intro h; exact (nil_not_mem_lang h).elim

lemma sat_reducible_lang : PolyTimeReducible SAT lang :=
  ⟨reduce, cpt_reduce, reduce_iff⟩

lemma lang_in_NP : lang ∈ NP := by
  refine ⟨R, (Polynomial.X + 1) ^ 2, decidable_R, fun x => ?_⟩
  constructor
  · rintro ⟨k, rows, hw, rfl, P, hwins⟩
    have hmem : (pack k rows, witness k P) ∈ R := ⟨k, rows, hw, rfl, P, hwins, rfl⟩
    refine ⟨witness k P, ?_, hmem⟩
    rw [sq, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, ← sq]
    exact witness_length_le (pack k rows) (witness k P) hmem
  · rintro ⟨w, _, k, rows, hw, rfl, P, hwins, rfl⟩
    exact ⟨k, rows, hw, rfl, P, hwins⟩

lemma lang_npHard : NPHard lang := by
  intro L' hL'
  obtain ⟨f, hf, hiff⟩ := Lib.SearchHelpers.Tab.npHard_SAT L' hL'
  exact ⟨fun x => reduce (f x), cpt_comp (g := reduce) hf cpt_reduce, fun x => (hiff x).trans (reduce_iff (f x))⟩

lemma lang_npComplete : NPComplete lang :=
  ⟨lang_in_NP, lang_npHard⟩

theorem main_result :
    NPComplete lang ∧ PolyTimeReducible SAT lang ∧
      DecidableInPolyTime encodePair R ∧
      (∀ x w, (x, w) ∈ R → w.length ≤ (x.length + 1) ^ 2) ∧
      (∀ k rows, well k rows → ∃ E : {P : Equiv.Perm (Fin k) // wins k rows P} ≃
        {w : List Bool // (pack k rows, w) ∈ R}, ∀ P, (E P).val = witness k P.val) :=
  ⟨lang_npComplete, sat_reducible_lang, decidable_R, witness_length_le, witness_equiv⟩

end PEqualNP.Outside.L_lib_896_aux.M896
theorem PEqualNP.Outside.L_lib_896 : (let bits := fun (w v : Nat) => (List.range w).map (fun j => v.testBit j)
let header := fun n : Nat => List.replicate n true ++ [false]
let width := fun n : Nat => n.log2+1
let pack := fun (k : Nat) (rows : List (List Nat)) =>
  header k ++ rows.flatMap (fun row => row.flatMap (bits (width k)))
let well := fun (k : Nat) (rows : List (List Nat)) => ∀ row ∈ rows,
  row.length = 4 ∧ row.Nodup ∧ ∀ v ∈ row, v < k
let wins := fun (k : Nat) (rows : List (List Nat)) (P : Equiv.Perm (Fin k)) =>
  Function.Involutive P ∧ ∀ row ∈ rows, ∃ u : Fin k, u.val ∈ row ∧
    (P u).val ∈ row ∧ P u ≠ u
let lang : Language Bool := {x | ∃ k rows, well k rows ∧ pack k rows = x ∧
  ∃ P : Equiv.Perm (Fin k), wins k rows P}
let witness := fun (k : Nat) (P : Equiv.Perm (Fin k)) =>
  (List.finRange k).flatMap (fun i => bits (width k) (P i).val)
let R : Set (List Bool × List Bool) := {z | ∃ k rows, well k rows ∧ pack k rows = z.1 ∧
  ∃ P : Equiv.Perm (Fin k), wins k rows P ∧ witness k P = z.2}
PEqualNP.Library.NPComplete lang ∧ PEqualNP.Library.PolyTimeReducible PEqualNP.Search.SAT lang ∧
  PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair R ∧
  (∀ x w, (x,w) ∈ R → w.length ≤ (x.length+1)^2) ∧
  (∀ k rows, well k rows → ∃ E : {P : Equiv.Perm (Fin k) // wins k rows P} ≃
    {w : List Bool // (pack k rows,w) ∈ R}, ∀ P, (E P).val = witness k P.val)) :=
  PEqualNP.Outside.L_lib_896_aux.M896.main_result
