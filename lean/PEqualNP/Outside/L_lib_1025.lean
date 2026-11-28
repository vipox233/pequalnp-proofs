import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1025
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
namespace Lib.Loop
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
end Lib.Loop
end
end PEqualNP.Outside.L_lib_1025

namespace PEqualNP.Outside.L_lib_1025
namespace Lib.R
open PEqualNP.Library Lib.Machines Lib.Universal Lib.Loop

def encV (v : List ℕ) : List Bool := v.flatMap (fun a => false :: un a)

def dbl (w : List Bool) : List Bool := w.flatMap (fun b => [true, b])

def encLL (S : List (List ℕ)) : List Bool := S.flatMap (fun v => false :: dbl (encV v))

def dsl_dv : List Bool → ℕ × List ℕ
  | [] => (0, [])
  | true :: r => ((dsl_dv r).1 + 1, (dsl_dv r).2)
  | false :: r => (0, (dsl_dv r).1 :: (dsl_dv r).2)

def decV (w : List Bool) : List ℕ := (dsl_dv w).2

def dr : List Bool → List Bool × List (List Bool)
  | [] => ([], [])
  | false :: r => (([] : List Bool), (dr r).1 :: (dr r).2)
  | true :: b :: r => (b :: (dr r).1, (dr r).2)
  | [true] => ([], [])
def decLL (w : List Bool) : List (List ℕ) := (dr w).2.map decV

@[local simp] theorem dsl_eV0 : encV [] = [] := rfl
@[local simp] theorem dsl_eV1 (a : ℕ) (v : List ℕ) : encV (a :: v) = false :: (un a ++ encV v) := rfl
@[local simp] theorem dsl_eVa (v w : List ℕ) : encV (v ++ w) = encV v ++ encV w := by simp [encV]
@[local simp] theorem dsl_db0 : dbl [] = [] := rfl
@[local simp] theorem dsl_db1 (b : Bool) (w : List Bool) : dbl (b :: w) = true :: b :: dbl w := rfl
@[local simp] theorem dsl_eL0 : encLL [] = [] := rfl
@[local simp] theorem dsl_eL1 (v : List ℕ) (S : List (List ℕ)) :
    encLL (v :: S) = false :: (dbl (encV v) ++ encLL S) := rfl
@[local simp] theorem dsl_eLa (S T : List (List ℕ)) : encLL (S ++ T) = encLL S ++ encLL T := by
  simp [encLL]

theorem dsl_dvu (a : ℕ) (w : List Bool) : dsl_dv (un a ++ w) = ((dsl_dv w).1 + a, (dsl_dv w).2) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [un_succ, List.cons_append, dsl_dv, ih, Nat.add_assoc]
theorem decV_encV (v : List ℕ) : decV (encV v) = v := by
  have : ∀ v, dsl_dv (encV v) = (0, v) := by
    intro v; induction v with
    | nil => rfl
    | cons a v ih => simp [dsl_dv, dsl_dvu, ih]
  simp [decV, this]
theorem dsl_dvi (w : List Bool) : un (dsl_dv w).1 ++ encV (dsl_dv w).2 = w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [dsl_dv, un_succ, ih]
theorem dsl_ed (w : List Bool) : encV (decV w) = w.dropWhile id := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simpa [decV, dsl_dv] using dsl_dvi w
    · simpa [decV, dsl_dv] using ih
theorem dsl_drd (x w : List Bool) : dr (dbl x ++ w) = (x ++ (dr w).1, (dr w).2) := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [dr, ih]
theorem decLL_encLL (S : List (List ℕ)) : decLL (encLL S) = S := by
  have : ∀ S, dr (encLL S) = ([], S.map encV) := by
    intro S; induction S with
    | nil => rfl
    | cons v S ih => simp [dr, dsl_drd, ih]
  simp [decLL, this, Function.comp_def, decV_encV]

def NatR (f : List Bool → ℕ) : Prop := Lib.CPTs (fun s => un (f s))
def VecR (f : List Bool → List ℕ) : Prop := Lib.CPTs (fun s => encV (f s))
def LLR (f : List Bool → List (List ℕ)) : Prop := Lib.CPTs (fun s => encLL (f s))

theorem dsl_T {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Bool) (fin : Q → Option Bool)
    (q : Q) : Lib.CPTs (fstRun δ fin q) := fst_polyTime _ _ _ δ fin q (fun _ => rfl)
theorem dsl_T2 {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Bool × Option Bool)
    (fin : Q → Option Bool) (q : Q) : Lib.CPTs (fstRun2 δ fin q) :=
  fst2_polyTime _ _ _ δ fin q (fun _ => rfl)
theorem dsl_fm (φ : Bool → Option Bool) : Lib.CPTs (fun w => w.filterMap φ) :=
  cptE (dsl_T (fun (_ : Unit) b => ((), φ b)) (fun _ => none) ()) (fun w => by
    induction w with
    | nil => rfl
    | cons b l ih => simp only [fstRun]; rw [ih]; cases h : φ b <;> simp [h])
theorem dsl_fl {Q : Type} (δ : Q → Bool → Q × Option Bool) (q : Q) (l : List Bool) :
    (fstRun δ (fun _ => none) q l).length ≤ l.length := by
  induction l generalizing q with
  | nil => simp [fstRun]
  | cons a l ih =>
    simp only [fstRun, List.length_append, List.length_cons]
    have := ih (δ q a).1
    cases (δ q a).2 <;> simp <;> omega
theorem dsl_skip {Q : Type} (δ : Q → Bool → Q × Option Bool) (fin : Q → Option Bool) (q q' : Q)
    (h1 : δ q true = (q', none)) (h2 : ∀ b, δ q' b = (q, none)) (x y : List Bool) :
    fstRun δ fin q (dbl x ++ y) = fstRun δ fin q y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [dsl_db1, List.cons_append, fstRun, h1, h2]; simpa using ih
theorem dsl_cdbl : Lib.CPTs dbl :=
  cptE (dsl_T2 (fun (_ : Unit) b => ((), some true, some b)) (fun _ => none) ()) (fun w => by
    induction w with
    | nil => rfl
    | cons b l ih => simp only [fstRun2]; rw [ih]; rfl)
def dsl_dwD : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, some false)
  | true, b => (true, some b)
theorem dsl_cdw : Lib.CPTs (fun l => l.dropWhile id) := by
  have ht : ∀ l, fstRun dsl_dwD (fun _ => none) true l = l := by
    intro l; induction l with
    | nil => rfl
    | cons b l ih => simp [fstRun, dsl_dwD, ih]
  refine cptE (dsl_T dsl_dwD (fun _ => none) false) (fun l => ?_)
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, dsl_dwD, ih, ht]
theorem dsl_up (x : ℕ) (w : List Bool) : unpairB (un x ++ false :: w) = (w.take x, w.drop x) := by
  have h1 : (un x ++ false :: w).takeWhile id = un x := by simp [un]
  have h2 : (un x ++ false :: w).dropWhile id = false :: w := by simp [un]
  simp [unpairB, h1, h2]
theorem dsl_tw (l : List Bool) : hd l = un (l.takeWhile id).length :=
  List.eq_replicate_iff.2 ⟨rfl, fun b hb => by simpa using List.mem_takeWhile_imp hb⟩
theorem dsl_hg {α : Type} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih => cases i <;> simp
theorem dsl_itT {α : Type} (E : List α → List Bool) (f : List Bool → List Bool)
    (hf : ∀ S, f (E S) = E S.tail) (n : ℕ) (S : List α) : f^[n] (E S) = E (S.drop n) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hf, ih, List.drop_tail]

def dsl_G (g : List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1 (tk (unpairB y).1 (g (unpairB y).2))
theorem dsl_G1 (g : List Bool → List Bool) (y : List Bool) :
    (unpairB (dsl_G g y)).1.length + 1 ≤ (unpairB y).1.length + 1 := by
  simp [dsl_G, unpairB_pairB]
theorem dsl_G2 (g : List Bool → List Bool) (y : List Bool) :
    (dsl_G g y).length ≤ y.length + ((unpairB y).1.length + 1) := by
  have h1 := unpairB_length y
  have h2 := tk_length (unpairB y).1 (g (unpairB y).2)
  simp only [dsl_G, pairB_length]; omega
theorem dsl_G3 (y : List Bool) : (unpairB y).1.length + 1 ≤ 1 * y.length + 1 := by
  have := unpairB_length y; omega
theorem dsl_Git (g : List Bool → List Bool) (pad y : List Bool) (n : ℕ)
    (h : ∀ i ≤ n, (g^[i] y).length ≤ pad.length) :
    (dsl_G g)^[n] (pairB pad y) = pairB pad (g^[n] y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply' (dsl_G g), ih (fun i hi => h i (by omega)),
      Function.iterate_succ_apply' g]
    simp only [dsl_G, unpairB_pairB, tk_eq]
    have := h (n + 1) le_rfl
    rw [Function.iterate_succ_apply'] at this
    rw [List.take_of_length_le this]
theorem dsl_iterBound {g cnt arg : List Bool → List Bool} (hg : Lib.CPTs g) (hcnt : Lib.CPTs cnt)
    (harg : Lib.CPTs arg) (P : Polynomial ℕ)
    (hb : ∀ s, ∀ i ≤ (cnt s).length, (g^[i] (arg s)).length ≤ P.eval s.length) :
    Lib.CPTs (fun s => g^[(cnt s).length] (arg s)) := by
  have hG : Lib.CPTs (dsl_G g) :=
    cpt_pairB2 cpt_unpairB1 (cpt_tk cpt_unpairB1 (cpt_comp cpt_unpairB2 hg))
  have hit := cpt_iterMeasure hG (fun y => (unpairB y).1.length + 1) 1 (dsl_G1 g) (dsl_G2 g) dsl_G3
    hcnt (cpt_pairB2 (Lib.L055 P) harg)
  exact cptE (cpt_unpairB2_1 hit) (fun s => by
    rw [dsl_Git g _ _ _ (fun i hi => by simpa using hb s i hi), unpairB_pairB])

theorem dsl_iterR {F init cnt : List Bool → List Bool} (hF : Lib.CPTs F) (hi : Lib.CPTs init)
    (hc : Lib.CPTs cnt) (P : Polynomial ℕ)
    (hb : ∀ s, ∀ i ≤ (cnt s).length,
      ((fun a => F (pairB a s))^[i] (init s)).length ≤ P.eval s.length) :
    Lib.CPTs (fun s => (fun a => F (pairB a s))^[(cnt s).length] (init s)) := by
  have e : ∀ s i a, (fun y => pairB (F y) (unpairB y).2)^[i] (pairB a s) =
      pairB ((fun a => F (pairB a s))^[i] a) s := by
    intro s i; induction i with
    | zero => intro a; rfl
    | succ i ih => intro a; simp only [Function.iterate_succ_apply, unpairB_pairB, ih]
  have h := dsl_iterBound (cpt_pairB2 hF cpt_unpairB2) hc (cpt_pairB2 hi cpt_id)
    (Polynomial.C 2 * P + Polynomial.X + Polynomial.C 1) (fun s i hi => by
      rw [e, pairB_length]; have := hb s i hi
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega)
  exact cptE (cpt_unpairB1_1 h) (fun s => by rw [e, unpairB_pairB])
theorem dsl_itU (F : List Bool → List Bool) (φ : ℕ → ℕ) (s : List Bool)
    (hF : ∀ x, F (pairB (un x) s) = un (φ x)) :
    ∀ i x, (fun a => F (pairB a s))^[i] (un x) = un (φ^[i] x) := by
  intro i; induction i with
  | zero => intro x; rfl
  | succ i ih => intro x; simp only [Function.iterate_succ_apply, hF, ih]
theorem dsl_loopN {φ : List Bool → ℕ → ℕ} {x0 n : List Bool → ℕ}
    (hφ : NatR (fun t => φ (unpairB t).2 (unpairB t).1.length)) (hx : NatR x0) (hn : NatR n)
    (P : Polynomial ℕ) (hb : ∀ s, ∀ i ≤ n s, (φ s)^[i] (x0 s) ≤ P.eval s.length) :
    NatR (fun s => (φ s)^[n s] (x0 s)) := by
  have e : ∀ s i x, (fun a => un (φ (unpairB (pairB a s)).2 (unpairB (pairB a s)).1.length))^[i]
      (un x) = un ((φ s)^[i] x) := fun s =>
    dsl_itU (fun t => un (φ (unpairB t).2 (unpairB t).1.length)) (φ s) s
      (fun x => by simp only [unpairB_pairB, un_length])
  have h := dsl_iterR (F := fun t => un (φ (unpairB t).2 (unpairB t).1.length))
    (init := fun s => un (x0 s)) (cnt := fun s => un (n s)) hφ hx hn P
    (fun s i hi => by rw [e, un_length]; exact hb s i (by simpa using hi))
  exact cptE h (fun s => by rw [un_length, e])
theorem dsl_cle (C : ℕ → Prop) [DecidablePred C] (i : ℕ) :
    (fun q => if C q then q else q + 1)^[i] 0 ≤ i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => rw [Function.iterate_succ_apply']; split_ifs <;> omega
theorem dsl_cnt (C : ℕ → Prop) [DecidablePred C] (m : ℕ) (hC : ∀ q, C q ↔ m < q + 1) (i : ℕ) :
    (fun q => if C q then q else q + 1)^[i] 0 = min i m := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    split_ifs with h
    · have := (hC _).1 h; omega
    · have := mt (hC _).2 h; omega
theorem dsl_le {a : List Bool → ℕ} (ha : NatR a) : ∃ P : Polynomial ℕ, ∀ s, a s ≤ P.eval s.length := by
  obtain ⟨P, hP⟩ := output_length_poly _ ha
  exact ⟨P, fun s => by simpa using hP s⟩
theorem dsl_sel (n : ℕ) (x y : List Bool) : sel (un n) x y = if n = 0 then x else y := by
  cases n <;> simp [sel, un]

theorem natR_const (k : ℕ) : NatR (fun _ => k) := cpt_const (un k)
theorem natR_len {p : List Bool → List Bool} (hp : Lib.CPTs p) : NatR (fun s => (p s).length) :=
  cptE (cpt_mulU2 hp (cpt_const [true])) (fun s => by simp [mulU])
theorem natR_add {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) : NatR (fun s => a s + b s) :=
  cptE (cpt_app2 ha hb) (fun s => by simp only [un, List.replicate_add])
theorem natR_sub {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) : NatR (fun s => a s - b s) :=
  cptE (cpt_unpairB2_1 (cpt_app2 hb (cpt_cons1 false ha))) (fun s => by
    rw [dsl_up]; simp [un])
theorem natR_mul {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) : NatR (fun s => a s * b s) :=
  cptE (cpt_mulU2 ha hb) (fun s => by simp [mulU])
theorem dsl_cil {a b : List Bool → ℕ} {x y : List Bool → List Bool} (ha : NatR a) (hb : NatR b)
    (hx : Lib.CPTs x) (hy : Lib.CPTs y) : Lib.CPTs (fun s => if a s < b s then x s else y s) :=
  cptE (cpt_sel (natR_sub hb ha) hy hx) (fun s => by
    dsimp only; rw [dsl_sel]; by_cases h : a s < b s
    · simp only [h, ↓reduceIte, show ¬ b s - a s = 0 by omega, ↓reduceIte]
    · simp only [h, ↓reduceIte, show b s - a s = 0 by omega, ↓reduceIte])
theorem dsl_cie {a b : List Bool → ℕ} {x y : List Bool → List Bool} (ha : NatR a) (hb : NatR b)
    (hx : Lib.CPTs x) (hy : Lib.CPTs y) : Lib.CPTs (fun s => if a s = b s then x s else y s) :=
  cptE (cpt_sel (natR_add (natR_sub ha hb) (natR_sub hb ha)) hx hy) (fun s => by
    dsimp only; rw [dsl_sel]; by_cases h : a s = b s
    · simp only [h, ↓reduceIte, show b s - b s + (b s - b s) = 0 by omega]
    · simp only [h, ↓reduceIte, show ¬ a s - b s + (b s - a s) = 0 by omega])
theorem dsl_nlt {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if a s < b s then x s else y s) :=
  cptE (dsl_cil ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
theorem dsl_neq {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if a s = b s then x s else y s) :=
  cptE (dsl_cie ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
theorem dsl_L1 : NatR (fun t => (unpairB t).1.length) := natR_len cpt_unpairB1
theorem dsl_nc2 {a : List Bool → ℕ} (ha : NatR a) : NatR (fun t => a (unpairB t).2) := by
  unfold NatR at *
  exact cpt_comp (f := fun t => (unpairB t).2) (g := fun s => un (a s)) cpt_unpairB2 ha
theorem natR_div {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) : NatR (fun s => a s / b s) := by
  obtain ⟨P, hP⟩ := dsl_le ha
  have hφ := dsl_nlt (dsl_nc2 ha) (natR_mul (natR_add dsl_L1 (natR_const 1)) (dsl_nc2 hb)) dsl_L1
    (natR_add dsl_L1 (natR_const 1))
  have h := dsl_loopN (φ := fun s q => if a s < (q + 1) * b s then q else q + 1) hφ
    (natR_const 0) ha P (fun s i hi => (dsl_cle _ i).trans (hi.trans (hP s)))
  refine cptE (dsl_neq hb (natR_const 0) (natR_const 0) h) (fun s => ?_)
  dsimp only
  by_cases h0 : b s = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    rw [dsl_cnt (fun q => a s < (q + 1) * b s) (a s / b s)
      (fun q => (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero h0)).symm) (a s),
      min_eq_right (Nat.div_le_self _ _)]
theorem natR_mod {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) : NatR (fun s => a s % b s) :=
  cptE (natR_sub ha (natR_mul hb (natR_div ha hb))) (fun s => by dsimp only; rw [Nat.mod_eq_sub_mul_div])
theorem dsl_half (i x : ℕ) : (fun x => x / 2)^[i] x = x / 2 ^ i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply, ih, Nat.div_div_eq_div_mul, pow_succ']
theorem dsl_halfN {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) :
    NatR (fun s => a s / 2 ^ b s) := by
  obtain ⟨P, hP⟩ := dsl_le ha
  have h := dsl_loopN (φ := fun _ x => x / 2) (natR_div dsl_L1 (natR_const 2)) ha hb P
    (fun s i _ => by rw [dsl_half]; exact (Nat.div_le_self _ _).trans (hP s))
  exact cptE h (fun s => by dsimp only; rw [dsl_half])
theorem natR_log2 {a : List Bool → ℕ} (ha : NatR a) : NatR (fun s => (a s).log2) := by
  obtain ⟨P, hP⟩ := dsl_le ha
  have hφ := dsl_nlt (dsl_halfN (dsl_nc2 ha) (natR_add dsl_L1 (natR_const 1))) (natR_const 1)
    dsl_L1 (natR_add dsl_L1 (natR_const 1))
  have h := dsl_loopN (φ := fun s q => if a s / 2 ^ (q + 1) < 1 then q else q + 1) hφ
    (natR_const 0) ha P (fun s i hi => (dsl_cle _ i).trans (hi.trans (hP s)))
  refine cptE h (fun s => ?_)
  dsimp only
  rw [dsl_cnt (fun q => a s / 2 ^ (q + 1) < 1) (a s).log2 (fun q => ?_) (a s),
    min_eq_right (Nat.log2_le_self _)]
  rcases Nat.eq_zero_or_pos (a s) with h0 | h0
  · simp [h0]
  · rw [Nat.div_lt_iff_lt_mul (by positivity), one_mul, Nat.log2_lt h0.ne']
theorem natR_testBit {a b : List Bool → ℕ} (ha : NatR a) (hb : NatR b) :
    NatR (fun s => if (a s).testBit (b s) then 1 else 0) :=
  cptE (natR_mod (dsl_halfN ha hb) (natR_const 2)) (fun s => by
    dsimp only; rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (a s / 2 ^ b s) with h | h <;> simp [h])
theorem dsl_pm (A C i : ℕ) : (fun x => x * A % C)^[i] (1 % C) = A ^ i % C := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ, Nat.mod_mul_mod]
theorem natR_powmod {a b c : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hc : NatR c)
    (hc0 : ∀ s, 0 < c s) : NatR (fun s => a s ^ b s % c s) := by
  obtain ⟨P, hP⟩ := dsl_le hc
  have h := dsl_loopN (φ := fun s x => x * a s % c s)
    (natR_mod (natR_mul dsl_L1 (dsl_nc2 ha)) (dsl_nc2 hc)) (natR_mod (natR_const 1) hc) hb P
    (fun s i _ => by rw [dsl_pm]; exact (Nat.mod_lt _ (hc0 s)).le.trans (hP s))
  exact cptE h (fun s => by dsimp only; rw [dsl_pm])

theorem dsl_powmodS {a b c : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hc : NatR c) :
    NatR (fun s => a s ^ b s % (c s + 1)) :=
  natR_powmod ha hb (natR_add hc (natR_const 1)) (fun _ => Nat.succ_pos _)
theorem dsl_p2 (i : ℕ) : (fun x => x + x)^[i] 1 = 2 ^ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ]; omega
theorem natR_pow2 {b : List Bool → ℕ} (hb : NatR b) (P : Polynomial ℕ)
    (hP : ∀ s, 2 ^ b s ≤ P.eval s.length) : NatR (fun s => 2 ^ b s) := by
  have h := dsl_loopN (φ := fun _ x => x + x) (natR_add dsl_L1 dsl_L1) (natR_const 1) hb P
    (fun s i hi => by rw [dsl_p2]; exact (Nat.pow_le_pow_right (by norm_num) hi).trans (hP s))
  exact cptE h (fun s => by dsimp only; rw [dsl_p2])

theorem cpt_ite_lt {a b : List Bool → ℕ} {x y : List Bool → List Bool} (ha : NatR a) (hb : NatR b)
    (hx : Lib.CPTs x) (hy : Lib.CPTs y) : Lib.CPTs (fun s => if a s < b s then x s else y s) :=
  dsl_cil ha hb hx hy
theorem cpt_ite_eq {a b : List Bool → ℕ} {x y : List Bool → List Bool} (ha : NatR a) (hb : NatR b)
    (hx : Lib.CPTs x) (hy : Lib.CPTs y) : Lib.CPTs (fun s => if a s = b s then x s else y s) :=
  dsl_cie ha hb hx hy

theorem natR_bit {p : List Bool → List Bool} {k : List Bool → ℕ} (hp : Lib.CPTs p) (hk : NatR k) :
    NatR (fun s => if (p s).getD (k s) false then 1 else 0) := by
  have h := cpt_comp (cpt_tk (cpt_const [true]) (cpt_unpairB2_1 (cpt_app2 hk (cpt_cons1 false hp))))
    (dsl_fm (fun b => if b then some true else none))
  refine cptE h (fun s => ?_)
  simp only [tk_eq, dsl_up, List.length_singleton]
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  rcases (p s).drop (k s) with _ | ⟨_ | _, l⟩ <;> simp [un]
theorem natR_runAt {p : List Bool → List Bool} {k : List Bool → ℕ} (hp : Lib.CPTs p) (hk : NatR k) :
    NatR (fun s => (((p s).drop (k s)).takeWhile id).length) :=
  cptE (cpt_hd1 (cpt_unpairB2_1 (cpt_app2 hk (cpt_cons1 false hp)))) (fun s => by
    rw [dsl_up]; exact dsl_tw _)

theorem vecR_dec {p : List Bool → List Bool} (hp : Lib.CPTs p) : VecR (fun s => decV (p s)) :=
  cptE (cpt_comp hp dsl_cdw) (fun _ => (dsl_ed _).symm)
theorem vecR_nil : VecR (fun _ => []) := cpt_const []
theorem vecR_single {a : List Bool → ℕ} (ha : NatR a) : VecR (fun s => [a s]) :=
  cptE (cpt_cons1 false ha) (fun s => by simp)
theorem vecR_append {v w : List Bool → List ℕ} (hv : VecR v) (hw : VecR w) :
    VecR (fun s => v s ++ w s) :=
  cptE (cpt_app2 hv hw) (fun s => by simp)
theorem dsl_dwu (a : ℕ) (w : List Bool) : (un a ++ w).dropWhile id = w.dropWhile id := by
  induction a with
  | zero => rfl
  | succ a ih => simpa [un_succ] using ih
theorem dsl_twV (v : List ℕ) : (encV v).takeWhile id = [] := by cases v <;> rfl
theorem dsl_stV (v : List ℕ) : ((encV v).tail).dropWhile id = encV v.tail := by
  cases v with
  | nil => rfl
  | cons a v => simp only [dsl_eV1, List.tail_cons, dsl_dwu]; cases v <;> rfl
theorem dsl_hdV (w : List ℕ) : hd (encV w).tail = un (w.headD 0) := by
  cases w with
  | nil => rfl
  | cons a w =>
    simp only [dsl_eV1, List.tail_cons, hd, List.headD_cons]
    rw [List.takeWhile_append_of_pos (by simp [un]), dsl_twV, List.append_nil]
theorem natR_get {v : List Bool → List ℕ} {i : List Bool → ℕ} (hv : VecR v) (hi : NatR i) :
    NatR (fun s => (v s).getD (i s) 0) := by
  have h := cpt_iterLen (g := fun y => (y.tail).dropWhile id) (cpt_comp cpt_tail dsl_cdw)
    (fun y => (List.IsSuffix.length_le (List.dropWhile_suffix (l := y.tail) id)).trans (by simp))
    hi hv
  exact cptE (cpt_hd1 (cpt_tail1 h)) (fun s => by
    rw [un_length, dsl_itT encV (fun y => (y.tail).dropWhile id) dsl_stV, dsl_hdV, dsl_hg])
theorem natR_vlen {v : List Bool → List ℕ} (hv : VecR v) : NatR (fun s => (v s).length) := by
  have e : ∀ v : List ℕ, (encV v).filterMap (fun b => if b then none else some true) = un v.length := by
    intro v; induction v with
    | nil => rfl
    | cons a v ih =>
      simp only [dsl_eV1, List.filterMap_cons, List.filterMap_append, ih]
      simp [un, List.filterMap_replicate_of_none, List.replicate_succ]
  exact cptE (cpt_comp hv (dsl_fm _)) (fun s => e _)
theorem natR_sum {v : List Bool → List ℕ} (hv : VecR v) : NatR (fun s => (v s).sum) := by
  have e : ∀ v : List ℕ, (encV v).filterMap (fun b => if b then some true else none) = un v.sum := by
    intro v; induction v with
    | nil => rfl
    | cons a v ih =>
      simp only [dsl_eV1, List.filterMap_cons, List.filterMap_append, ih]
      simp [un]
  exact cptE (cpt_comp hv (dsl_fm _)) (fun s => e _)

theorem vecR_gen {A : List Bool → List Bool} {n : List Bool → ℕ} {G : ℕ → List Bool → ℕ}
    (hA : Lib.CPTs A) (hn : NatR n) (hG : NatR (fun t => G (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s => (List.range (n s)).map (fun i => G i (A s))) :=
  cptE (cpt_flatMapRange (cpt_cons1 false hG) hn hA) (fun s => by
    simp [encV, List.flatMap_map, unpairB_pairB])
theorem vecR_flat {A : List Bool → List Bool} {n : List Bool → ℕ} {H : ℕ → List Bool → List ℕ}
    (hA : Lib.CPTs A) (hn : NatR n) (hH : VecR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s => (List.range (n s)).flatMap (fun i => H i (A s))) :=
  cptE (cpt_flatMapRange hH hn hA) (fun s => by simp [encV, List.flatMap_assoc, unpairB_pairB])
def dsl_bD : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, none)
  | true, true => (false, some true)
  | true, false => (true, some false)
def dsl_bF (q : Bool) : Option Bool := if q then some false else none

theorem cpt_bitsOf {v : List Bool → List ℕ} (hv : VecR v) :
    Lib.CPTs (fun s => (v s).map (fun a => decide (a ≠ 0))) := by
  have hu : ∀ (a : ℕ) w, fstRun dsl_bD dsl_bF false (un a ++ w) = fstRun dsl_bD dsl_bF false w := by
    intro a w; induction a with
    | zero => rfl
    | succ a ih => simpa [un_succ, fstRun, dsl_bD] using ih
  have e : ∀ v : List ℕ, fstRun dsl_bD dsl_bF false (encV v) = v.map (fun a => decide (a ≠ 0)) ∧
      fstRun dsl_bD dsl_bF true (encV v) = false :: v.map (fun a => decide (a ≠ 0)) := by
    intro v; induction v with
    | nil => exact ⟨rfl, rfl⟩
    | cons a v ih =>
      have key : fstRun dsl_bD dsl_bF true (un a ++ encV v) =
          decide (a ≠ 0) :: v.map (fun a => decide (a ≠ 0)) := by
        cases a with
        | zero => exact ih.2
        | succ a => simp [un_succ, fstRun, dsl_bD, hu, ih.1]
      simp [fstRun, dsl_bD, key]
  exact cptE (cpt_comp hv (dsl_T dsl_bD dsl_bF false)) (fun s => (e _).1)

def dsl_lD : Bool × Bool × Bool → Bool → (Bool × Bool × Bool) × Option Bool × Option Bool
  | (_, false, _), false => ((true, false, true), some false, none)
  | (r, false, d), true => ((r, true, d), none, none)
  | (false, true, _), _ => ((false, false, false), none, none)
  | (true, true, d), b =>
    if d && b then ((true, false, true), none, none) else ((true, false, false), some true, some b)
def dsl_rT (d : Bool) (x : List Bool) : List Bool := if d then x.dropWhile id else x
theorem dsl_lB (w : List Bool) : ∀ d, fstRun2 dsl_lD (fun _ => none) (true, false, d) w =
    dbl (dsl_rT d (dr w).1) ++ encLL ((dr w).2.map decV) := by
  induction w using dr.induct with
  | case1 => intro d; cases d <;> rfl
  | case2 r ih => intro d; simp [fstRun2, dsl_lD, dr, ih, dsl_rT, dsl_ed]
  | case3 b r ih => intro d; cases d <;> cases b <;> simp [fstRun2, dsl_lD, dr, ih, dsl_rT]
  | case4 => intro d; cases d <;> rfl
theorem dsl_lA (w : List Bool) : fstRun2 dsl_lD (fun _ => none) (false, false, false) w =
    encLL (decLL w) := by
  induction w using dr.induct with
  | case1 => rfl
  | case2 r ih => simp [fstRun2, dsl_lD, dr, decLL, dsl_lB, dsl_rT, dsl_ed]
  | case3 b r ih => simpa [fstRun2, dsl_lD, dr, decLL] using ih
  | case4 => rfl
theorem llR_dec {p : List Bool → List Bool} (hp : Lib.CPTs p) : LLR (fun s => decLL (p s)) :=
  cptE (cpt_comp hp (dsl_T2 dsl_lD (fun _ => none) (false, false, false))) (fun _ => dsl_lA _)
theorem llR_nil : LLR (fun _ => []) := cpt_const []
theorem llR_single {v : List Bool → List ℕ} (hv : VecR v) : LLR (fun s => [v s]) :=
  cptE (cpt_cons1 false (cpt_comp hv dsl_cdbl)) (fun s => by simp)
theorem llR_append {S T : List Bool → List (List ℕ)} (hS : LLR S) (hT : LLR T) :
    LLR (fun s => S s ++ T s) :=
  cptE (cpt_app2 hS hT) (fun s => by simp)
def dsl_sD : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (false, false), false => ((true, false), some false)
  | (false, false), true => ((false, true), none)
  | (false, true), _ => ((false, false), none)
  | (true, _), b => ((true, false), some b)
def dsl_xD : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (false, false), false => ((true, false), none)
  | (false, false), true => ((false, true), none)
  | (false, true), b => ((false, false), some b)
  | (true, _), _ => ((true, false), none)
theorem dsl_rs (S : List (List ℕ)) :
    fstRun dsl_sD (fun _ => none) (false, false) (encLL S).tail = encLL S.tail := by
  have hc : ∀ x l, fstRun dsl_sD (fun _ => none) (true, x) l = l := by
    intro x l; induction l generalizing x with
    | nil => rfl
    | cons b l ih => simp [fstRun, dsl_sD, ih]
  cases S with
  | nil => rfl
  | cons v S =>
    simp only [dsl_eL1, List.tail_cons]
    rw [dsl_skip dsl_sD _ (false, false) (false, true) rfl (fun _ => rfl)]
    cases S with
    | nil => rfl
    | cons w S => simp [fstRun, dsl_sD, hc]
theorem dsl_xL (S : List (List ℕ)) :
    fstRun dsl_xD (fun _ => none) (false, false) (encLL S).tail = encV (S.headD []) := by
  have hd0 : ∀ x l, fstRun dsl_xD (fun _ => none) (true, x) l = [] := by
    intro x l; induction l generalizing x with
    | nil => rfl
    | cons b l ih => simp [fstRun, dsl_xD, ih]
  have hb : ∀ x y, fstRun dsl_xD (fun _ => none) (false, false) (dbl x ++ y) =
      x ++ fstRun dsl_xD (fun _ => none) (false, false) y := by
    intro x y; induction x with
    | nil => rfl
    | cons b x ih => simp [fstRun, dsl_xD, ih]
  cases S with
  | nil => rfl
  | cons v S =>
    simp only [dsl_eL1, List.tail_cons, List.headD_cons]
    rw [hb]
    cases S with
    | nil => simp [fstRun]
    | cons w S => simp [fstRun, dsl_xD, hd0]
theorem vecR_row {S : List Bool → List (List ℕ)} {j : List Bool → ℕ} (hS : LLR S) (hj : NatR j) :
    VecR (fun s => (S s).getD (j s) []) := by
  have h := cpt_iterLen (g := fun y => fstRun dsl_sD (fun _ => none) (false, false) y.tail)
    (cpt_comp cpt_tail (dsl_T dsl_sD _ (false, false)))
    (fun y => (dsl_fl _ _ _).trans (by simp)) hj hS
  exact cptE (cpt_comp (cpt_tail1 h) (dsl_T dsl_xD (fun _ => none) (false, false))) (fun s => by
    rw [un_length, dsl_itT encLL (fun y => fstRun dsl_sD (fun _ => none) (false, false) y.tail)
      dsl_rs, dsl_xL, dsl_hg])
def dsl_cD : Bool → Bool → Bool × Option Bool
  | false, false => (false, some true)
  | false, true => (true, none)
  | true, _ => (false, none)
theorem natR_llen {S : List Bool → List (List ℕ)} (hS : LLR S) : NatR (fun s => (S s).length) := by
  have e : ∀ S : List (List ℕ), fstRun dsl_cD (fun _ => none) false (encLL S) = un S.length := by
    intro S; induction S with
    | nil => rfl
    | cons v S ih =>
      simp only [dsl_eL1, fstRun, dsl_cD, Option.toList_some]
      rw [dsl_skip dsl_cD _ false true rfl (fun _ => rfl), ih]; rfl
  exact cptE (cpt_comp hS (dsl_T dsl_cD _ false)) (fun s => e _)
theorem llR_gen {A : List Bool → List Bool} {n : List Bool → ℕ} {H : ℕ → List Bool → List ℕ}
    (hA : Lib.CPTs A) (hn : NatR n) (hH : VecR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s => (List.range (n s)).map (fun i => H i (A s))) :=
  cptE (cpt_flatMapRange (cpt_cons1 false (cpt_comp hH dsl_cdbl)) hn hA) (fun s => by
    simp [encLL, List.flatMap_map, unpairB_pairB])
theorem llR_flat {A : List Bool → List Bool} {n : List Bool → ℕ} {H : ℕ → List Bool → List (List ℕ)}
    (hA : Lib.CPTs A) (hn : NatR n) (hH : LLR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s => (List.range (n s)).flatMap (fun i => H i (A s))) :=
  cptE (cpt_flatMapRange hH hn hA) (fun s => by simp [encLL, List.flatMap_assoc, unpairB_pairB])

theorem cpt_iterBound {g cnt arg : List Bool → List Bool} (hg : Lib.CPTs g) (hcnt : Lib.CPTs cnt)
    (harg : Lib.CPTs arg) (P : Polynomial ℕ)
    (hb : ∀ s, ∀ i ≤ (cnt s).length, (g^[i] (arg s)).length ≤ P.eval s.length) :
    Lib.CPTs (fun s => g^[(cnt s).length] (arg s)) := dsl_iterBound hg hcnt harg P hb

theorem encV_length (v : List ℕ) : (encV v).length = v.length + v.sum := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [ih]; omega
theorem encLL_length_le (S : List (List ℕ)) :
    (encLL S).length ≤ S.length + 2 * (S.map (fun v => v.length + v.sum)).sum := by
  have hd : ∀ w, (dbl w).length = 2 * w.length := by
    intro w; induction w with
    | nil => rfl
    | cons b w ih => simp [ih]; omega
  induction S with
  | nil => simp
  | cons v S ih =>
    simp only [dsl_eL1, List.length_cons, List.length_append, hd, encV_length, List.map_cons,
      List.sum_cons]
    omega
theorem natR_le_poly {a : List Bool → ℕ} (ha : NatR a) : ∃ P : Polynomial ℕ, ∀ s, a s ≤ P.eval s.length :=
  dsl_le ha

end Lib.R
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Lib.Fast
open PEqualNP.Library
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
lemma cpt_to_fast {f:List Bool → List Bool} (hf:Lib.CPTs f) :
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
end Lib.Fast
end PEqualNP.Outside.L_lib_1025

namespace PEqualNP.Outside.L_lib_1025
namespace Alg

abbrev g (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

abbrev gg (S : List (List ℕ)) (j : ℕ) : List ℕ := S.getD j []

def bit (x : List Bool) (k : ℕ) : ℕ := if x.getD k false then 1 else 0
def runAt (x : List Bool) (k : ℕ) : ℕ := ((x.drop k).takeWhile id).length

def pI (n : ℕ) : List ℕ := (List.range n).flatMap (fun i =>
  (List.range n).flatMap (fun j => if i < j then [i] else []))
def pJ (n : ℕ) : List ℕ := (List.range n).flatMap (fun i =>
  (List.range n).flatMap (fun j => if i < j then [j] else []))

def nV (x : List Bool) : ℕ := runAt x 0
def pN (x : List Bool) : ℕ := (pI (nV x)).length
def Em (x : List Bool) : List ℕ := (List.range (pN x)).map (fun k => bit x (nV x + 1 + k))
def Pm (x : List Bool) : List ℕ := (List.range (pN x)).map (fun k => bit x (nV x + 1 + pN x + k))
def oL (x : List Bool) : ℕ := nV x + 1 + 2 * pN x
def lenV (x : List Bool) : ℕ := runAt x (oL x)
def oR (x : List Bool) : ℕ := oL x + lenV x + 1

def rowM (x : List Bool) : List (List ℕ) := (List.range (lenV x)).map (fun r =>
  (List.range (pN x)).map (fun k => bit x (oR x + r * (pN x + 1) + 1 + k)))

def rowS (x : List Bool) : List ℕ := (List.range (lenV x)).map (fun r => bit x (oR x + r * (pN x + 1)))

def missP (Pm row : List ℕ) : ℕ := ((List.range Pm.length).map (fun k => g Pm k * (1 - g row k))).sum

def Frows (Pm : List ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  (List.range rows.length).flatMap (fun r => if missP Pm (gg rows r) = 0 then [gg rows r] else [])
def Fsig (Pm : List ℕ) (rows : List (List ℕ)) (sg : List ℕ) : List ℕ :=
  (List.range rows.length).flatMap (fun r => if missP Pm (gg rows r) = 0 then [g sg r] else [])

def inVP (pi pj Pm : List ℕ) (v : ℕ) : ℕ :=
  ((List.range Pm.length).map (fun k => g Pm k * (if g pi k = v then 1 else if g pj k = v then 1 else 0))).sum

def Uset (pi pj Em Pm : List ℕ) : List ℕ := (List.range Em.length).flatMap (fun k =>
  if g Em k = 0 then [] else if inVP pi pj Pm (g pi k) + inVP pi pj Pm (g pj k) = 0 then [k] else [])

def firstNZ (v : List ℕ) : ℕ :=
  ((List.range v.length).map (fun i => if ((List.range (i + 1)).map (fun j => g v j)).sum = 0 then 1 else 0)).sum

def isPr (c : ℕ) : ℕ := if c < 2 then 0 else
  if ((List.range c).map (fun d => if d < 2 then 0 else if c % d = 0 then 1 else 0)).sum = 0 then 1 else 0

def primeAbove (B : ℕ) : ℕ := B + 1 + firstNZ ((List.range (B + 2)).map (fun i => isPr (B + 1 + i)))

def wedgeV (q N : ℕ) (x v : List ℕ) : List ℕ := (List.range (2 ^ N)).map (fun J =>
  ((List.range N).map (fun b => if J.testBit b then
      (if ((List.range N).map (fun c => if b < c then (if J.testBit c then 1 else 0) else 0)).sum % 2 = 0
        then g v b * g x (J - 2 ^ b) % q else q - g v b * g x (J - 2 ^ b) % q)
    else 0)).sum % q)

def vv (q N a : ℕ) : List ℕ := (List.range N).map (fun b => a ^ b % q)

def e0 (q N : ℕ) : List ℕ := (List.range (2 ^ N)).map (fun J => if J = 0 then 1 % q else 0)

def wedgeLab (q N : ℕ) (pi pj τ : List ℕ) : List ℕ :=
  ((fun p : ℕ × List ℕ => (p.1 + 1,
      wedgeV q N (wedgeV q N p.2 (vv q N (g pi (g τ p.1)))) (vv q N (g pj (g τ p.1)))))^[τ.length]
    (0, e0 q N)).2

def chi (F : List (List ℕ)) (τ : List ℕ) (r : ℕ) : ℕ :=
  if ((List.range τ.length).map (fun i => 1 - g (gg F r) (g τ i))).sum = 0 then 1 else 0

def vecL (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (τ : List ℕ) : List ℕ :=
  (List.range (2 ^ N * F.length)).map (fun k =>
    g (wedgeLab q N pi pj τ) (k / F.length) * chi F τ (k % F.length) % q)

def posC (F : List (List ℕ)) (fs : List ℕ) (τ : List ℕ) : ℕ :=
  ((List.range F.length).map (fun r => g fs r * chi F τ r)).sum
def negC (F : List (List ℕ)) (fs : List ℕ) (τ : List ℕ) : ℕ :=
  ((List.range F.length).map (fun r => (1 - g fs r) * chi F τ r)).sum

def ends (pi pj τ : List ℕ) : List ℕ := (List.range (2 * τ.length)).map (fun i =>
  if i % 2 = 0 then g pi (g τ (i / 2)) else g pj (g τ (i / 2)))

def clash (pi pj τ : List ℕ) : ℕ :=
  ((List.range (ends pi pj τ).length).map (fun i =>
    ((List.range (ends pi pj τ).length).map (fun j =>
      if i < j then (if g (ends pi pj τ) i = g (ends pi pj τ) j then 1 else 0) else 0)).sum)).sum

def hit (pi pj : List ℕ) (F : List (List ℕ)) (fs τ : List ℕ) : ℕ :=
  if clash pi pj τ = 0 then (if posC F fs τ = negC F fs τ then 0 else 1) else 0

def red1 (q : ℕ) (v b : List ℕ) (p : ℕ) : List ℕ :=
  (List.range v.length).map (fun i => (g b p * g v i + (q - g v p) * g b i) % q)

def redAll (q : ℕ) (B : List (List ℕ)) (pv : List ℕ) (v : List ℕ) : List ℕ :=
  ((fun p : ℕ × List ℕ => (p.1 + 1, red1 q p.2 (gg B p.1) (g pv p.1)))^[B.length] (0, v)).2

structure ESt where
  B : List (List ℕ)
  pv : List ℕ
  sl : List (List ℕ)

def insertG (q : ℕ) (vec : List ℕ → List ℕ) (st : ESt) (τ : List ℕ) : ESt :=
  let r := redAll q st.B st.pv (vec τ)
  if r.sum = 0 then st else ⟨st.B ++ [r], st.pv ++ [firstNZ r], st.sl ++ [τ]⟩

def selectG (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) : List (List ℕ) :=
  ((fun p : ℕ × ESt => (p.1 + 1, insertG q vec p.2 (gg C p.1)))^[C.length] (0, ⟨[], [], []⟩)).2.sl
def selectE (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (C : List (List ℕ)) : List (List ℕ) :=
  selectG q (vecL q N pi pj F) C

def cand (U : List ℕ) (S : List (List ℕ)) : List (List ℕ) :=
  (List.range S.length).flatMap (fun j => (List.range U.length).map (fun u => gg S j ++ [g U u]))
def hits (pi pj : List ℕ) (F : List (List ℕ)) (fs : List ℕ) (C : List (List ℕ)) : List (List ℕ) :=
  (List.range C.length).flatMap (fun j => if hit pi pj F fs (gg C j) = 0 then [] else [gg C j])

def lvl (q N : ℕ) (pi pj U : List ℕ) (F : List (List ℕ)) (fs : List ℕ)
    (st : List (List ℕ) × List (List ℕ)) : List (List ℕ) × List (List ℕ) :=
  if st.2.length = 0 then
    (if (hits pi pj F fs st.1).length = 0 then (cand U (selectE q N pi pj F st.1), [])
      else (st.1, [gg (hits pi pj F fs st.1) 0]))
  else st

def found (x : List Bool) : List (List ℕ) :=
  let n := nV x
  let pi := pI n
  let pj := pJ n
  let F := Frows (Pm x) (rowM x)
  let fs := Fsig (Pm x) (rowM x) (rowS x)
  let K := Nat.log2 F.length
  let q := primeAbove (n + F.length)
  ((lvl q (2 * K) pi pj (Uset pi pj (Em x) (Pm x)) F fs)^[K + 1] ([[]], [])).2

def outBits (x : List Bool) (τ : List ℕ) : List Bool :=
  let F := Frows (Pm x) (rowM x)
  let fs := Fsig (Pm x) (rowM x) (rowS x)
  let a := posC F fs τ
  let b := negC F fs τ
  [true] ++ (List.range (pN x)).map (fun k =>
      decide (g (Pm x) k + ((List.range τ.length).map (fun i => if g τ i = k then 1 else 0)).sum ≠ 0)) ++
    [decide (a < b)] ++ (List.range ((lenV x).log2 + 1)).map (fun i => ((a - b) + (b - a)).testBit i)

def solveV (x : List Bool) : List Bool :=
  if (found x).length = 0 then [false] else outBits x (gg (found x) 0)

def zv (q : ℕ) (v : List ℕ) : ℕ → ZMod q := fun i => ((v.getD i 0 : ℕ) : ZMod q)

end Alg
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg

def pairsF (n : ℕ) : List (Fin n × Fin n) := (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i, j)))
def maskF {n : ℕ} (A : Finset (Fin n × Fin n)) : List Bool := (pairsF n).map (fun e => decide (e ∈ A))
def inputF (n : ℕ) (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool)) :
    List Bool :=
  (List.replicate n true ++ [false]) ++ maskF E ++ maskF P ++
    (List.replicate rows.length true ++ [false]) ++ rows.flatMap (fun t => t.2 :: maskF t.1)

def ind {n : ℕ} (A : Finset (Fin n × Fin n)) : List ℕ := (pairsF n).map (fun e => if e ∈ A then 1 else 0)

theorem dec_fm {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    l.flatMap (fun j => if p j then [f j] else []) = (l.filter (fun j => decide (p j))).map f := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]
theorem dec_rng (n : ℕ) : List.range n = List.map Fin.val (List.finRange n) :=
  List.ext_getElem (by simp) (by simp)
theorem dec_pI (n : ℕ) : pI n = (pairsF n).map (fun e => (e.1 : ℕ)) := by
  rw [pI, pairsF, dec_rng, List.flatMap_map, List.map_flatMap]
  congr 1; funext i
  rw [List.flatMap_map, List.map_map]
  exact dec_fm (List.finRange n) (fun j : Fin n => (i : ℕ) < j) (fun _ => (i : ℕ))
theorem dec_pJ (n : ℕ) : pJ n = (pairsF n).map (fun e => (e.2 : ℕ)) := by
  rw [pJ, pairsF, dec_rng, List.flatMap_map, List.map_flatMap]
  congr 1; funext i
  rw [List.flatMap_map, List.map_map]
  exact dec_fm (List.finRange n) (fun j : Fin n => (i : ℕ) < j) (fun j : Fin n => (j : ℕ))

theorem pI_length (n : ℕ) : (pI n).length = (pairsF n).length := by simp [dec_pI]
theorem pJ_length (n : ℕ) : (pJ n).length = (pairsF n).length := by simp [dec_pJ]
theorem pairsF_get (n k : ℕ) (hk : k < (pairsF n).length) :
    (((pairsF n)[k]'hk).1 : ℕ) = g (pI n) k ∧ (((pairsF n)[k]'hk).2 : ℕ) = g (pJ n) k := by
  simp [dec_pI, dec_pJ, hk]
theorem pairsF_nodup (n : ℕ) : (pairsF n).Nodup := by
  rw [pairsF, List.nodup_flatMap]
  refine ⟨fun i _ => ((List.nodup_finRange n).filter _).map (fun a b h => (Prod.mk.inj h).2), ?_⟩
  exact (List.nodup_finRange n).imp (fun hab => List.disjoint_left.2 (by
    intro e h1 h2; simp at h1 h2; obtain ⟨_, _, rfl⟩ := h1; obtain ⟨_, _, h⟩ := h2
    exact hab (congrArg Prod.fst h).symm))
theorem mem_pairsF (n : ℕ) (e : Fin n × Fin n) : e ∈ pairsF n ↔ e.1 < e.2 := by
  obtain ⟨a, b⟩ := e; simp [pairsF]

theorem dec_bitA (a b : List Bool) (k : ℕ) : bit (a ++ b) (a.length + k) = bit b k := by
  simp [bit, List.getElem?_append_right]
theorem dec_bitB (a b : List Bool) (k : ℕ) (h : k < a.length) : bit (a ++ b) k = bit a k := by
  simp [bit, List.getElem?_append_left h]
theorem dec_runA (a b : List Bool) (k : ℕ) : runAt (a ++ b) (a.length + k) = runAt b k := by
  simp [runAt, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right a.length k)]
theorem dec_run0 (m : ℕ) (l : List Bool) : runAt (List.replicate m true ++ false :: l) 0 = m := by
  induction m with
  | zero => simp [runAt]
  | succ m ih => simp_all [runAt, List.replicate_succ]
theorem dec_fmb {α : Type} (l : List α) (f : α → List Bool) (m : ℕ) (hf : ∀ a, (f a).length = m)
    (r j : ℕ) (hr : r < l.length) (hj : j < m) : bit (l.flatMap f) (r * m + j) = bit (f l[r]) j := by
  induction l generalizing r with
  | nil => simp at hr
  | cons a l ih =>
    rw [List.flatMap_cons]
    rcases r with _ | r
    · simpa using dec_bitB _ _ j (by rw [hf]; exact hj)
    · have : (r + 1) * m + j = (f a).length + (r * m + j) := by rw [hf]; ring
      rw [this, dec_bitA]; exact ih r (by simpa using hr)
theorem dec_maskF {n : ℕ} (A : Finset (Fin n × Fin n)) (k : ℕ) (h : k < (pairsF n).length) :
    bit (maskF A) k = if (pairsF n)[k] ∈ A then 1 else 0 := by
  simp [bit, maskF, h]
@[simp] theorem dec_maskL {n : ℕ} (A : Finset (Fin n × Fin n)) : (maskF A).length = (pairsF n).length := by
  simp [maskF]

section dec
variable (n : ℕ) (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool))
theorem dec_eq : inputF n E P rows = (List.replicate n true ++ [false]) ++ (maskF E ++ (maskF P ++
    ((List.replicate rows.length true ++ [false]) ++ rows.flatMap (fun t => t.2 :: maskF t.1)))) := by
  simp [inputF]
theorem nV_inputF : nV (inputF n E P rows) = n := by
  rw [dec_eq, nV]; simpa using dec_run0 n _
theorem pN_inputF : pN (inputF n E P rows) = (pairsF n).length := by
  rw [pN, nV_inputF, pI_length]
theorem Em_inputF : Em (inputF n E P rows) = ind E := by
  apply List.ext_getElem (by simp [Em, ind, pN_inputF])
  intro k h1 h2
  simp only [Em, ind, List.getElem_map, List.getElem_range, nV_inputF]
  simp [Em, pN_inputF] at h1
  rw [dec_eq, show n + 1 + k = (List.replicate n true ++ [false]).length + k by simp, dec_bitA,
    dec_bitB _ _ _ (by simpa using h1), dec_maskF _ _ h1]
theorem Pm_inputF : Pm (inputF n E P rows) = ind P := by
  apply List.ext_getElem (by simp [Pm, ind, pN_inputF])
  intro k h1 h2
  simp only [Pm, ind, List.getElem_map, List.getElem_range, nV_inputF, pN_inputF]
  simp [Pm, pN_inputF] at h1
  rw [dec_eq, show n + 1 + (pairsF n).length + k = (List.replicate n true ++ [false]).length +
    ((maskF E).length + k) by simp; omega, dec_bitA, dec_bitA,
    dec_bitB _ _ _ (by simpa using h1), dec_maskF _ _ h1]
theorem dec_oL : oL (inputF n E P rows) = n + 1 + 2 * (pairsF n).length := by
  rw [oL, nV_inputF, pN_inputF]
theorem lenV_inputF : lenV (inputF n E P rows) = rows.length := by
  rw [lenV, dec_oL, dec_eq, show n + 1 + 2 * (pairsF n).length = (List.replicate n true ++ [false]).length +
    ((maskF E).length + ((maskF P).length + 0)) by simp; omega, dec_runA, dec_runA, dec_runA]
  simpa using dec_run0 _ _
theorem dec_pos (r j : ℕ) : oR (inputF n E P rows) + r * ((pairsF n).length + 1) + j =
    (List.replicate n true ++ [false]).length + ((maskF E).length + ((maskF P).length +
    ((List.replicate rows.length true ++ [false]).length + (r * ((pairsF n).length + 1) + j)))) := by
  simp [oR, dec_oL, lenV_inputF]; ring
theorem dec_row (r j : ℕ) (hr : r < rows.length) (hj : j < (pairsF n).length + 1) :
    bit (inputF n E P rows) (oR (inputF n E P rows) + r * ((pairsF n).length + 1) + j) =
      bit (rows[r].2 :: maskF rows[r].1) j := by
  rw [dec_pos, dec_eq, dec_bitA, dec_bitA, dec_bitA, dec_bitA,
    dec_fmb _ _ _ (fun t => by simp) _ _ hr hj]
theorem rowM_inputF : rowM (inputF n E P rows) = rows.map (fun t => ind t.1) := by
  apply List.ext_getElem (by simp [rowM, lenV_inputF])
  intro r h1 h2
  simp [rowM, lenV_inputF] at h1
  apply List.ext_getElem (by simp [rowM, ind, pN_inputF])
  intro k h3 h4
  simp [rowM, pN_inputF] at h3
  simp only [rowM, ind, List.getElem_map, List.getElem_range, pN_inputF]
  rw [add_assoc, dec_row _ _ _ _ _ _ h1 (by omega), show 1 + k = [rows[r].2].length + k by simp,
    ← List.singleton_append, dec_bitA, dec_maskF _ _ h3]
theorem rowS_inputF : rowS (inputF n E P rows) = rows.map (fun t => if t.2 then 1 else 0) := by
  apply List.ext_getElem (by simp [rowS, lenV_inputF])
  intro r h1 h2
  simp [rowS, lenV_inputF] at h1
  simp only [rowS, List.getElem_map, List.getElem_range, pN_inputF]
  have := dec_row n E P rows r 0 h1 (by omega)
  rw [add_zero] at this
  rw [this]; simp [bit]
end dec

end Alg
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg

def LwZ (q N : ℕ) (v : ℕ → ZMod q) : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q) where
  toFun x J := if J < 2 ^ N then
    ∑ b ∈ Finset.range N, (if J.testBit b then
      ((-1 : ZMod q) ^ ((Finset.range N).filter (fun c => b < c ∧ J.testBit c)).card) * v b * x (J - 2 ^ b)
      else 0) else 0
  map_add' x y := by
    funext J; dsimp only [Pi.add_apply]; split_ifs
    · rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    · simp
  map_smul' c x := by
    funext J; dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs
    · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    · simp

theorem ext_L (q N : ℕ) (v x : ℕ → ZMod q) (J : ℕ) : LwZ q N v x J = if J < 2 ^ N then
    ∑ b ∈ Finset.range N, (if J.testBit b then
      ((-1 : ZMod q) ^ ((Finset.range N).filter (fun c => b < c ∧ J.testBit c)).card) * v b * x (J - 2 ^ b)
      else 0) else 0 := rfl

theorem ext_ls {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem ext_gd {α : Type*} (n i : ℕ) (f : ℕ → α) (d : α) :
    ((List.range n).map f).getD i d = if i < n then f i else d := by
  rw [List.getD_eq_getElem?_getD]; by_cases h : i < n <;> simp [h]

theorem ext_cnt (N b J : ℕ) :
    ((List.range N).map (fun c => if b < c then (if J.testBit c then 1 else 0) else 0)).sum =
      ((Finset.range N).filter (fun c => b < c ∧ J.testBit c)).card := by
  rw [ext_ls, Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h1 : b < c <;> by_cases h2 : J.testBit c <;> simp [h1, h2]

theorem ext_sgn (q : ℕ) (hq : 0 < q) (k A : ℕ) :
    (((if k % 2 = 0 then A % q else q - A % q : ℕ)) : ZMod q) = (-1) ^ k * A := by
  rcases Nat.even_or_odd k with h | h
  · rw [ite_eq_left (Nat.even_iff.mp h), h.neg_one_pow, ZMod.natCast_mod, one_mul]
  · rw [ite_eq_right (by rw [Nat.odd_iff.mp h]; omega), h.neg_one_pow, Nat.cast_sub (Nat.mod_lt _ hq).le,
      ZMod.natCast_self, ZMod.natCast_mod]; ring

theorem zv_wedgeV (q N : ℕ) (hq : 0 < q) (x v : List ℕ) :
    zv q (wedgeV q N x v) = LwZ q N (zv q v) (zv q x) := by
  funext J
  simp only [zv, wedgeV, ext_gd, ext_cnt, ext_L]
  split_ifs with hJ
  · rw [ZMod.natCast_mod, ext_ls, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : J.testBit b
    · rw [ite_eq_left hb, ite_eq_left hb, ext_sgn q hq, Nat.cast_mul]; ring
    · rw [ite_eq_right hb, ite_eq_right hb, Nat.cast_zero]
  · simp

def ext_W (q N : ℕ) (pi pj τ : List ℕ) : ℕ → List ℕ
  | 0 => e0 q N
  | k + 1 => wedgeV q N (wedgeV q N (ext_W q N pi pj τ k) (vv q N (g pi (g τ k)))) (vv q N (g pj (g τ k)))

theorem ext_it (q N : ℕ) (pi pj τ : List ℕ) (k : ℕ) :
    ((fun p : ℕ × List ℕ => (p.1 + 1,
      wedgeV q N (wedgeV q N p.2 (vv q N (g pi (g τ p.1)))) (vv q N (g pj (g τ p.1)))))^[k]
      (0, e0 q N)) = (k, ext_W q N pi pj τ k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem ext_wl (q N : ℕ) (pi pj τ : List ℕ) : wedgeLab q N pi pj τ = ext_W q N pi pj τ τ.length :=
  congrArg Prod.snd (ext_it q N pi pj τ τ.length)

theorem wedgeLab_nil (q N : ℕ) (pi pj : List ℕ) : wedgeLab q N pi pj [] = e0 q N := rfl

theorem ext_Wa (q N : ℕ) (pi pj τ : List ℕ) (e : ℕ) :
    ∀ k ≤ τ.length, ext_W q N pi pj (τ ++ [e]) k = ext_W q N pi pj τ k
  | 0, _ => rfl
  | k + 1, h => by
    have h2 : g (τ ++ [e]) k = g τ k := by
      simp only [g, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
    simp only [ext_W]; rw [ext_Wa q N pi pj τ e k (by omega), h2]

theorem wedgeLab_snoc (q N : ℕ) (pi pj τ : List ℕ) (e : ℕ) :
    wedgeLab q N pi pj (τ ++ [e]) =
      wedgeV q N (wedgeV q N (wedgeLab q N pi pj τ) (vv q N (g pi e))) (vv q N (g pj e)) := by
  have h2 : g (τ ++ [e]) τ.length = e := by simp only [g, List.getD_eq_getElem?_getD]; simp
  rw [ext_wl, ext_wl, List.length_append, List.length_singleton, ext_W,
    ext_Wa q N pi pj τ e _ le_rfl, h2]

theorem ext_Wl (q N : ℕ) (pi pj τ : List ℕ) : ∀ k, (ext_W q N pi pj τ k).length = 2 ^ N
  | 0 => by simp [ext_W, e0]
  | k + 1 => by simp [ext_W, wedgeV]

theorem wedgeLab_length (q N : ℕ) (pi pj τ : List ℕ) : (wedgeLab q N pi pj τ).length = 2 ^ N := by
  rw [ext_wl]; exact ext_Wl _ _ _ _ _ _

theorem wedgeLab_lt (q N : ℕ) (hq : 0 < q) (pi pj τ : List ℕ) : ∀ a ∈ wedgeLab q N pi pj τ, a < q := by
  intro a ha
  rw [ext_wl] at ha
  revert ha
  cases τ.length with
  | zero =>
    intro ha
    simp only [ext_W, e0, List.mem_map] at ha
    obtain ⟨J, -, rfl⟩ := ha
    split_ifs
    · exact Nat.mod_lt _ hq
    · exact hq
  | succ k =>
    intro ha
    simp only [ext_W, wedgeV, List.mem_map] at ha
    obtain ⟨J, -, rfl⟩ := ha
    exact Nat.mod_lt _ hq

def ext_G (q N : ℕ) (u : ℕ → ℕ → ZMod q) : ℕ → ℕ → ZMod q
  | 0 => zv q (e0 q N)
  | r + 1 => LwZ q N (u r) (ext_G q N u r)

theorem ext_e0 (q N J : ℕ) : zv q (e0 q N) J = if J = 0 then 1 else 0 := by
  simp only [zv, e0, ext_gd]
  by_cases h : J = 0
  · subst h; simp [ZMod.natCast_mod]
  · simp [h]

theorem ext_bm {J c : ℕ} : J.testBit c = true ↔ ∃ j < J.bitIndices.length, J.bitIndices.getD j 0 = c := by
  rw [← Nat.mem_bitIndices, List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, List.getD_eq_getElem _ _ hj⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, (List.getD_eq_getElem _ _ hj).symm⟩

theorem ext_bN {N J c : ℕ} (hJ : J < 2 ^ N) (hc : J.testBit c = true) : c < N := by
  by_contra h
  have := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hJ (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)))
  simp_all

theorem ext_lt {l : List ℕ} (hl : l.SortedLT) {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
    l.getD i 0 < l.getD j 0 ↔ i < j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact hl.lt_iff_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)

theorem ext_inj {l : List ℕ} (hl : l.SortedLT) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i 0 = l.getD j 0) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · have := (ext_lt hl hi hj).mpr h'; omega
  · exact h'
  · have := (ext_lt hl hj hi).mpr h'; omega

theorem ext_er (J i : ℕ) (hi : i < J.bitIndices.length) :
    (J - 2 ^ J.bitIndices.getD i 0).bitIndices = J.bitIndices.eraseIdx i := by
  have hs : (J.bitIndices.eraseIdx i).SortedLT :=
    (Nat.bitIndices_sorted.pairwise.sublist (List.eraseIdx_sublist _ _)).sortedLT
  have hJ := Nat.sum_map_two_pow_bitIndices J
  set l := J.bitIndices
  have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have h3 : (l.map (fun i => 2 ^ i)).sum =
      ((l.take i).map (fun i => 2 ^ i)).sum + 2 ^ l[i] + ((l.drop (i + 1)).map (fun i => 2 ^ i)).sum := by
    conv_lhs => rw [hl]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]; ring
  have h4 : J - 2 ^ l.getD i 0 = ((l.eraseIdx i).map (fun i => 2 ^ i)).sum := by
    rw [List.eraseIdx_eq_take_drop_succ, List.getD_eq_getElem _ _ hi, List.map_append, List.sum_append]
    omega
  rw [h4, Nat.bitIndices_sum_map_two_pow hs]

theorem ext_ge (l : List ℕ) (i k : ℕ) :
    (l.eraseIdx i).getD k 0 = l.getD (if k < i then k else k + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eraseIdx_of_lt h]
  · rw [List.getElem?_eraseIdx_of_ge (not_lt.mp h)]

theorem ext_sa {r : ℕ} (i : Fin (r + 1)) (k : Fin r) :
    (i.succAbove k : ℕ) = if (k : ℕ) < i then (k : ℕ) else (k : ℕ) + 1 := by
  rcases lt_or_ge (k : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), ite_eq_left h]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), ite_eq_right (by omega)]; rfl

theorem ext_key {M : Type*} [AddCommMonoid M] (N J : ℕ) (hJ : J < 2 ^ N) (F : ℕ → M) :
    (∑ b ∈ Finset.range N, if J.testBit b then F b else 0) =
      ∑ i ∈ Finset.range J.bitIndices.length, F (J.bitIndices.getD i 0) := by
  rw [← Finset.sum_filter]
  have : (Finset.range N).filter (fun b => J.testBit b = true) =
      (Finset.range J.bitIndices.length).image (fun i => J.bitIndices.getD i 0) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    exact ⟨fun h => ext_bm.mp h.2, fun h => ⟨ext_bN hJ (ext_bm.mpr h), ext_bm.mpr h⟩⟩
  rw [this, Finset.sum_image fun a ha b hb hab =>
    ext_inj Nat.bitIndices_sorted (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab]

theorem ext_card (N J r : ℕ) (hJ : J < 2 ^ N) (hr : J.bitIndices.length = r + 1) (i : ℕ) (hi : i < r + 1) :
    ((Finset.range N).filter (fun c => J.bitIndices.getD i 0 < c ∧ J.testBit c)).card = r - i := by
  have hs := @Nat.bitIndices_sorted J
  have hi' : i < J.bitIndices.length := by omega
  have : (Finset.range N).filter (fun c => J.bitIndices.getD i 0 < c ∧ J.testBit c) =
      (Finset.Ioc i r).image (fun j => J.bitIndices.getD j 0) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Ioc]
    constructor
    · rintro ⟨-, hlt, hb⟩
      obtain ⟨j, hj, rfl⟩ := ext_bm.mp hb
      exact ⟨j, ⟨(ext_lt hs hi' hj).mp hlt, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      have hj : j < J.bitIndices.length := by omega
      exact ⟨ext_bN hJ (ext_bm.mpr ⟨j, hj, rfl⟩), (ext_lt hs hi' hj).mpr h1, ext_bm.mpr ⟨j, hj, rfl⟩⟩
  rw [this, Finset.card_image_of_injOn fun a ha b hb hab => ext_inj hs
    (by simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha; omega)
    (by simp only [Finset.coe_Ioc, Set.mem_Ioc] at hb; omega) hab, Nat.card_Ioc]

theorem ext_det (q N : ℕ) (u : ℕ → ℕ → ZMod q) (r J : ℕ) :
    ext_G q N u r J = if J < 2 ^ N ∧ J.bitIndices.length = r then
      (Matrix.of fun i k : Fin r => u k (J.bitIndices.getD i 0)).det else 0 := by
  induction r generalizing J with
  | zero =>
    rw [ext_G, ext_e0, Matrix.det_fin_zero]
    by_cases h : J = 0
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right]; rintro ⟨-, h2⟩; apply h
      rw [← Nat.sum_map_two_pow_bitIndices J, List.length_eq_zero_iff.mp h2]; rfl
  | succ r ih =>
    rw [ext_G, ext_L]
    by_cases hJ : J < 2 ^ N
    swap
    · simp [hJ]
    rw [ite_eq_left hJ, ext_key N J hJ]
    by_cases hr : J.bitIndices.length = r + 1
    · rw [ite_eq_left ⟨hJ, hr⟩, Matrix.det_succ_column _ (Fin.last r), hr, Finset.sum_range]
      refine Fintype.sum_congr _ _ fun i => ?_
      have hi := i.isLt
      have hi' : (i : ℕ) < J.bitIndices.length := by omega
      rw [ih, ext_er J i hi', ite_eq_left ⟨lt_of_le_of_lt (Nat.sub_le _ _) hJ, by rw [List.length_eraseIdx_of_lt hi']; omega⟩,
        ext_card N J r hJ hr i hi]
      simp only [Matrix.of_apply, Fin.val_last, Fin.succAbove_last]
      congr 1
      · congr 1
        rw [show (i : ℕ) + r = (r - i) + 2 * i by omega, pow_add, pow_mul]; simp
      · congr 1; ext a b
        simp only [Matrix.of_apply, Matrix.submatrix_apply, ext_ge, ext_sa, Fin.val_castSucc]
    · rw [ite_eq_right (fun h => hr h.2)]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ih, ext_er J i hi, ite_eq_right, mul_zero]
      rintro ⟨-, h⟩; rw [List.length_eraseIdx_of_lt hi] at h; omega

def ext_u (q N : ℕ) (pi pj τ : List ℕ) (i : ℕ) : ℕ → ZMod q :=
  zv q (vv q N (if i % 2 = 0 then g pi (g τ (i / 2)) else g pj (g τ (i / 2))))

theorem ext_wz (q N : ℕ) (hq : 0 < q) (pi pj τ : List ℕ) (k : ℕ) :
    zv q (ext_W q N pi pj τ k) = ext_G q N (ext_u q N pi pj τ) (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ha : ext_u q N pi pj τ (2 * k) = zv q (vv q N (g pi (g τ k))) := by
      simp only [ext_u]; rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega]
    have hb : ext_u q N pi pj τ (2 * k + 1) = zv q (vv q N (g pj (g τ k))) := by
      simp only [ext_u]; rw [ite_eq_right (by omega), show (2 * k + 1) / 2 = k by omega]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, ext_W, ext_G, ext_G, zv_wedgeV q N hq,
      zv_wedgeV q N hq, ih, ha, hb]

theorem ext_wz2 (q N : ℕ) (hq : 0 < q) (pi pj τ : List ℕ) :
    zv q (wedgeLab q N pi pj τ) = ext_G q N (ext_u q N pi pj τ) (2 * τ.length) := by
  rw [ext_wl, ext_wz q N hq]

theorem ext_ue (q N : ℕ) (pi pj τ : List ℕ) (i : ℕ) (h : i < 2 * τ.length) :
    ext_u q N pi pj τ i = zv q (vv q N ((ends pi pj τ).getD i 0)) := by
  rw [ext_u, ends, ext_gd, ite_eq_left h]

theorem ext_cl (pi pj τ : List ℕ) : clash pi pj τ = 0 ↔
    ∀ i j, i < j → j < 2 * τ.length → (ends pi pj τ).getD i 0 ≠ (ends pi pj τ).getD j 0 := by
  have hL : (ends pi pj τ).length = 2 * τ.length := by simp [ends]
  simp only [clash, g, ext_ls, hL, Finset.sum_eq_zero_iff, Finset.mem_range]
  constructor
  · intro h i j hij hj he
    have := h i (by omega) j hj
    rw [ite_eq_left hij, ite_eq_left he] at this; exact one_ne_zero this
  · intro h i _ j hj
    split_ifs with h1 h2
    · exact absurd h2 (h i j h1 hj)
    · rfl
    · rfl

theorem ext_gs (r : ℕ) : ((List.range r).map (fun i => 2 ^ i)).sum + 1 = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, pow_succ]; simp; omega

theorem wedgeLab_zero (q N : ℕ) [Fact q.Prime] (pi pj τ : List ℕ) (h : clash pi pj τ ≠ 0) :
    zv q (wedgeLab q N pi pj τ) = 0 := by
  have hq0 := (Fact.out : q.Prime).pos
  obtain ⟨i, j, hij, hj, he⟩ : ∃ i j, i < j ∧ j < 2 * τ.length ∧
      (ends pi pj τ).getD i 0 = (ends pi pj τ).getD j 0 := by
    by_contra hc; exact h ((ext_cl pi pj τ).mpr fun i j hij hj he => hc ⟨i, j, hij, hj, he⟩)
  funext J
  rw [ext_wz2 q N hq0, ext_det, Pi.zero_apply]
  split_ifs
  · refine Matrix.det_zero_of_column_eq (i := (⟨i, by omega⟩ : Fin (2 * τ.length))) (j := ⟨j, hj⟩)
      (fun h => by simp [Fin.ext_iff] at h; omega) fun k => ?_
    simp only [Matrix.of_apply]
    rw [ext_ue _ _ _ _ _ _ (by omega : i < 2 * τ.length), ext_ue _ _ _ _ _ _ hj, he]
  · rfl

theorem wedgeLab_ne_zero (q N : ℕ) [Fact q.Prime] (pi pj τ : List ℕ) (h : clash pi pj τ = 0)
    (hN : 2 * τ.length ≤ N) (hq : ∀ a ∈ ends pi pj τ, a < q) :
    zv q (wedgeLab q N pi pj τ) ≠ 0 := by
  have hq0 := (Fact.out : q.Prime).pos
  have hd := (ext_cl pi pj τ).mp h
  have hL : (ends pi pj τ).length = 2 * τ.length := by simp [ends]
  have hm : ∀ k < 2 * τ.length, (ends pi pj τ).getD k 0 < q := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hq _ (List.getElem_mem _)
  intro h0
  have hJ := ext_gs (2 * τ.length)
  have h1 := congrFun h0 ((List.range (2 * τ.length)).map (fun i => 2 ^ i)).sum
  rw [Pi.zero_apply, ext_wz2 q N hq0, ext_det, Nat.bitIndices_sum_map_two_pow (List.sortedLT_range _),
    ite_eq_left ⟨lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by norm_num) hN), by simp⟩] at h1
  have hM : Matrix.transpose (Matrix.vandermonde fun k : Fin (2 * τ.length) =>
      (((ends pi pj τ).getD k 0 : ℕ) : ZMod q)) = Matrix.of fun i k : Fin (2 * τ.length) =>
        ext_u q N pi pj τ k ((List.range (2 * τ.length)).getD i 0) := by
    ext i k
    have hi := i.isLt
    rw [Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.of_apply,
      List.getD_eq_getElem (List.range _) _ (by simp), List.getElem_range, ext_ue _ _ _ _ _ _ k.isLt, zv, vv,
      ext_gd, ite_eq_left (by omega), ZMod.natCast_mod, Nat.cast_pow]
  refine (Matrix.det_vandermonde_ne_zero_iff (v := fun k : Fin (2 * τ.length) =>
    (((ends pi pj τ).getD k 0 : ℕ) : ZMod q))).mpr ?_ (by rw [← Matrix.det_transpose, hM]; exact h1)
  intro a b hab
  simp only at hab
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hm _ a.isLt), Nat.mod_eq_of_lt (hm _ b.isLt)] at hab
  rcases lt_trichotomy (a : ℕ) b with h' | h' | h'
  · exact absurd hab (hd _ _ h' b.isLt)
  · exact Fin.ext h'
  · exact absurd hab.symm (hd _ _ h' a.isLt)

end Alg
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg

def selStep (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) (p : ℕ × ESt) : ℕ × ESt :=
  (p.1 + 1, insertG q vec p.2 (gg C p.1))
theorem selectG_eq (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) :
    selectG q vec C = ((selStep q vec C)^[C.length] (0, ⟨[], [], []⟩)).2.sl := rfl

theorem el_fst {α : Type} (f : ℕ × α → ℕ × α) (h : ∀ p, (f p).1 = p.1 + 1) (x : α) :
    ∀ k, (f^[k] (0, x)).1 = k
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', h, el_fst f h x k]
theorem el_gP {α : Type} (P : α → Prop) (l : List α) (d : α) (i : ℕ) (h0 : P d)
    (h : ∀ a ∈ l, P a) : P (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases e : l[i]? with
  | none => simpa using h0
  | some a => simpa using h a (List.mem_of_getElem? e)
theorem el_mem {α : Type} (l : List α) (d : α) (k : ℕ) (h : k < l.length) : l.getD k d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
theorem el_gapp {α : Type} (l : List α) (a d : α) (j : ℕ) :
    (l ++ [a]).getD j d = if j < l.length then l.getD j d else if j = l.length then a else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega
theorem el_cnt (a : ℕ) : ∀ n, ((List.range n).map fun i => if i < a then 1 else 0).sum = min n a
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, el_cnt a n]; simp; split_ifs <;> omega
theorem el_fnz (v : List ℕ) (h : ∃ i, i < v.length ∧ g v i ≠ 0) :
    firstNZ v < v.length ∧ g v (firstNZ v) ≠ 0 := by
  classical
  have e : firstNZ v = Nat.find h := by
    unfold firstNZ
    rw [List.map_congr_left (g := fun i => if i < Nat.find h then 1 else 0), el_cnt]
    · exact min_eq_right (Nat.find_spec h).1.le
    intro i _
    have : ((List.range (i + 1)).map fun j => g v j).sum = 0 ↔ i < Nat.find h := by
      rw [List.sum_eq_zero_iff]
      simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      constructor
      · intro H; by_contra H'; push Not at H'; exact (Nat.find_spec h).2 (H _ (by omega))
      · intro H j hj
        have := Nat.find_min h (show j < Nat.find h by omega)
        by_cases hj2 : j < v.length
        · by_contra H2; exact this ⟨hj2, H2⟩
        · exact List.getD_eq_default _ _ (by omega)
    simp only [this]
  rw [e]; exact Nat.find_spec h
theorem el_g1 (q : ℕ) (w b : List ℕ) (p i : ℕ) :
    g (red1 q w b p) i = if i < w.length then (g b p * g w i + (q - g w p) * g b i) % q else 0 := by
  simp only [g]; split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp [red1, h])]; simp [red1]
  · rw [List.getD_eq_default]; simp [red1]; omega
theorem el_m0 (q a b : ℕ) (h : a ≤ q) : (b * a + (q - a) * b) % q = 0 := by
  rw [show b * a + (q - a) * b = q * b by zify [h]; ring]; exact Nat.mul_mod_right q b

def el_I (q D : ℕ) (st : ESt) : Prop :=
  st.pv.length = st.B.length ∧ st.sl.length = st.B.length ∧
  (∀ b ∈ st.B, b.length = D ∧ ∀ a ∈ b, a < q) ∧
  ∀ j < st.B.length, g st.pv j < D ∧ g (gg st.B j) (g st.pv j) ≠ 0 ∧
    ∀ l, j < l → l < st.B.length → g (gg st.B l) (g st.pv j) = 0
def el_it (q : ℕ) (B : List (List ℕ)) (pv v : List ℕ) (k : ℕ) : ℕ × List ℕ :=
  (fun p : ℕ × List ℕ => (p.1 + 1, red1 q p.2 (gg B p.1) (g pv p.1)))^[k] (0, v)
theorem el_its (q : ℕ) (B : List (List ℕ)) (pv v : List ℕ) (k : ℕ) :
    el_it q B pv v (k + 1) = (k + 1, red1 q (el_it q B pv v k).2 (gg B k) (g pv k)) := by
  have := el_fst (fun p : ℕ × List ℕ => (p.1 + 1, red1 q p.2 (gg B p.1) (g pv p.1))) (fun _ => rfl) v k
  simp only [el_it, Function.iterate_succ_apply', this]
theorem el_redA (q D : ℕ) (hq : 0 < q) (st : ESt) (hI : el_I q D st) (v : List ℕ)
    (hv : v.length = D) (hv2 : ∀ a ∈ v, a < q) : ∀ k ≤ st.B.length,
    (el_it q st.B st.pv v k).2.length = D ∧ (∀ a ∈ (el_it q st.B st.pv v k).2, a < q) ∧
      ∀ j < k, g (el_it q st.B st.pv v k).2 (g st.pv j) = 0
  | 0 => fun _ => ⟨hv, hv2, by simp⟩
  | k + 1 => fun hk => by
    obtain ⟨h1, h2, h3⟩ := el_redA q D hq st hI v hv hv2 k (by omega)
    rw [el_its]
    refine ⟨by simp [red1, h1], ?_, ?_⟩
    · intro a ha; simp only [red1, List.mem_map] at ha; obtain ⟨i, _, rfl⟩ := ha; exact Nat.mod_lt _ hq
    · intro j hj; rw [el_g1]; split_ifs
      · rcases (show j < k ∨ j = k by omega) with hj | rfl
        · rw [h3 j hj, (hI.2.2.2 j (by omega)).2.2 k hj (by omega)]; simp
        · exact el_m0 _ _ _ (el_gP (· < q) _ _ _ hq h2).le
      · rfl
theorem el_insI (q D : ℕ) (hq : 0 < q) (vec : List ℕ → List ℕ) (st : ESt) (hI : el_I q D st)
    (τ : List ℕ) (hv : (vec τ).length = D) (hv2 : ∀ a ∈ vec τ, a < q) :
    el_I q D (insertG q vec st τ) := by
  obtain ⟨hr1, hr2, hr3⟩ := el_redA q D hq st hI _ hv hv2 _ le_rfl
  have hr1' : (redAll q st.B st.pv (vec τ)).length = D := hr1
  unfold insertG; dsimp only; split_ifs with hs
  · exact hI
  have hne : ∃ i, i < (redAll q st.B st.pv (vec τ)).length ∧ g (redAll q st.B st.pv (vec τ)) i ≠ 0 := by
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ redAll q st.B st.pv (vec τ), a ≠ 0 := by
      by_contra H; push Not at H; exact hs (List.sum_eq_zero_iff.mpr H)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ⟨i, hi, by simp only [g]; rwa [List.getD_eq_getElem _ _ hi]⟩
  have hp := el_fnz _ hne
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
  refine ⟨by simp [hI1], by simp [hI2], ?_, ?_⟩
  · intro b hb; rw [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hI3 b hb
    · exact ⟨hr1, hr2⟩
  · intro j hj; simp only [List.length_append, List.length_singleton] at hj
    simp only [g, gg, el_gapp, hI1]
    rcases (show j < st.B.length ∨ j = st.B.length by omega) with hj | rfl
    · simp only [hj, ite_true]; obtain ⟨a1, a2, a3⟩ := hI4 j hj; refine ⟨a1, a2, fun l hl1 hl2 => ?_⟩
      simp only [List.length_append, List.length_singleton] at hl2
      rcases (show l < st.B.length ∨ l = st.B.length by omega) with hl | rfl
      · simp only [hl, ite_true]; exact a3 l hl1 hl
      · simp only [lt_irrefl, ite_false, ite_true]; exact hr3 j hj
    · simp only [lt_irrefl, ite_false, ite_true]
      exact ⟨by omega, hp.2, fun l h1 h2 => by simp at h2; omega⟩

def el_st (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) (i : ℕ) : ℕ × ESt :=
  (selStep q vec C)^[i] (0, ⟨[], [], []⟩)
theorem el_sts (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) (i : ℕ) :
    el_st q vec C (i + 1) = (i + 1, insertG q vec (el_st q vec C i).2 (gg C i)) := by
  have := el_fst (selStep q vec C) (fun _ => rfl) ⟨[], [], []⟩ i
  simp only [el_st, Function.iterate_succ_apply', selStep, this]
theorem el_sub (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) :
    ∀ i ≤ C.length, ∀ τ ∈ (el_st q vec C i).2.sl, τ ∈ C
  | 0 => fun _ τ h => by simp [el_st] at h
  | i + 1 => fun hi τ hτ => by
    rw [el_sts] at hτ; unfold insertG at hτ; dsimp only at hτ; split_ifs at hτ
    · exact el_sub q vec C i (by omega) τ hτ
    · rw [List.mem_append, List.mem_singleton] at hτ
      rcases hτ with h | rfl
      · exact el_sub q vec C i (by omega) τ h
      · exact el_mem C [] i (by omega)
theorem el_invI (q : ℕ) (hq : 0 < q) (vec : List ℕ → List ℕ) (D : ℕ)
    (hlen : ∀ τ, (vec τ).length = D) (hlt : ∀ τ, ∀ a ∈ vec τ, a < q) (C : List (List ℕ)) :
    ∀ i, el_I q D (el_st q vec C i).2
  | 0 => by show el_I q D ⟨[], [], []⟩; exact ⟨rfl, rfl, by simp, by simp⟩
  | i + 1 => by rw [el_sts]; exact el_insI q D hq vec _ (el_invI q hq vec D hlen hlt C i) _ (hlen _) (hlt _)
theorem el_Blen (q D : ℕ) (st : ESt) (hI : el_I q D st) : st.B.length ≤ D := by
  have := Finset.card_le_card_of_injOn (fun j => g st.pv j) (s := Finset.range st.B.length)
    (t := Finset.range D) ?_ ?_
  · simpa using this
  · intro j hj; simp at hj ⊢; exact (hI.2.2.2 j hj).1
  · intro j1 hj1 j2 hj2 e; simp at hj1 hj2; by_contra hne; dsimp only at e
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := (hI.2.2.2 j1 hj1).2.2 j2 h hj2; rw [e] at this; exact (hI.2.2.2 j2 hj2).2.1 this
    · have := (hI.2.2.2 j2 hj2).2.2 j1 h hj1; rw [← e] at this; exact (hI.2.2.2 j1 hj1).2.1 this
theorem el_pvlt (q D : ℕ) (st : ESt) (hI : el_I q D st) : ∀ p ∈ st.pv, p < D := by
  intro p hp; obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  have := (hI.2.2.2 j (hI.1 ▸ hj)).1; simp only [g] at this; rwa [List.getD_eq_getElem _ _ hj] at this

theorem selStep_inv (q : ℕ) (hq : 0 < q) (vec : List ℕ → List ℕ) (D : ℕ)
    (hlen : ∀ τ, (vec τ).length = D) (hlt : ∀ τ, ∀ a ∈ vec τ, a < q) (C : List (List ℕ))
    (i : ℕ) (hi : i ≤ C.length) :
    ((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).1 = i ∧
    (((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.B.length ≤ D) ∧
    (((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.pv.length = ((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.B.length) ∧
    (((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.sl.length = ((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.B.length) ∧
    (∀ b ∈ ((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.B, b.length = D ∧ ∀ a ∈ b, a < q) ∧
    (∀ p ∈ ((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.pv, p < D) ∧
    (∀ τ ∈ ((selStep q vec C)^[i] (0, ⟨[], [], []⟩)).2.sl, τ ∈ C) := by
  have hI := el_invI q hq vec D hlen hlt C i
  exact ⟨el_fst _ (fun _ => rfl) _ i, el_Blen q D _ hI, hI.1, hI.2.1, hI.2.2.1, el_pvlt q D _ hI,
    el_sub q vec C i hi⟩
theorem selectG_sub (q : ℕ) (vec : List ℕ → List ℕ) (C : List (List ℕ)) :
    ∀ τ ∈ selectG q vec C, τ ∈ C := fun τ h => el_sub q vec C _ le_rfl τ h
theorem selectG_length (q : ℕ) (hq : 0 < q) (vec : List ℕ → List ℕ) (D : ℕ)
    (hlen : ∀ τ, (vec τ).length = D) (hlt : ∀ τ, ∀ a ∈ vec τ, a < q) (C : List (List ℕ)) :
    (selectG q vec C).length ≤ D := by
  obtain ⟨-, h1, -, h2, -⟩ := selStep_inv q hq vec D hlen hlt C _ le_rfl
  rw [selectG_eq, h2]; exact h1

def el_sp (q : ℕ) (f : List ℕ → ℕ → ZMod q) (L : List (List ℕ)) : Submodule (ZMod q) (ℕ → ZMod q) :=
  Submodule.span (ZMod q) {z | ∃ τ ∈ L, z = f τ}
theorem el_sps (q : ℕ) (f : List ℕ → ℕ → ZMod q) (L : List (List ℕ)) (a : List ℕ) :
    el_sp q f (L ++ [a]) = el_sp q f L ⊔ Submodule.span (ZMod q) {f a} := by
  unfold el_sp; rw [← Submodule.span_union]; congr 1; ext z
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨τ, h | rfl, rfl⟩; exacts [Or.inl ⟨τ, h, rfl⟩, Or.inr rfl]
  · rintro (⟨τ, h, rfl⟩ | rfl); exacts [⟨τ, Or.inl h, rfl⟩, ⟨_, Or.inr rfl, rfl⟩]
theorem el_sp0 (q : ℕ) (f : List ℕ → ℕ → ZMod q) : el_sp q f [] = ⊥ := by simp [el_sp]
theorem el_swap {K V : Type} [Field K] [AddCommGroup V] [Module K V] (W : Submodule K V) (x y : V)
    (c : K) (hc : c ≠ 0) (h : x - c • y ∈ W) : W ⊔ Submodule.span K {x} = W ⊔ Submodule.span K {y} := by
  apply le_antisymm <;> apply sup_le le_sup_left <;> rw [Submodule.span_singleton_le_iff_mem]
  · have : x = (x - c • y) + c • y := by abel
    rw [this]; exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)))
  · have : y = c⁻¹ • (x - (x - c • y)) := by simp [smul_smul, inv_mul_cancel₀ hc]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)) (Submodule.mem_sup_left h))
theorem el_zv1 (q : ℕ) (w b : List ℕ) (p : ℕ) (hb : b.length ≤ w.length) (hw : g w p ≤ q) :
    zv q (red1 q w b p) = (g b p : ZMod q) • zv q w - (g w p : ZMod q) • zv q b := by
  funext i
  simp only [zv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have := el_g1 q w b p i
  simp only [g] at this hw ⊢
  split_ifs at this with hi
  · rw [this, ZMod.natCast_mod]; push_cast [Nat.cast_sub hw, ZMod.natCast_self]; ring
  · have e1 : w.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
    have e2 : b.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
    rw [this, e1, e2]; simp
theorem el_redB (q D : ℕ) [Fact q.Prime] (st : ESt) (hI : el_I q D st) (v : List ℕ)
    (hv : v.length = D) (hv2 : ∀ a ∈ v, a < q) : ∀ k ≤ st.B.length,
    ∃ c : ZMod q, c ≠ 0 ∧ zv q (el_it q st.B st.pv v k).2 - c • zv q v ∈ el_sp q (zv q) st.B
  | 0 => fun _ => ⟨1, one_ne_zero, by
    show zv q v - _ • _ ∈ _; rw [one_smul, sub_self]; exact zero_mem _⟩
  | k + 1 => fun hk => by
    have hq : 0 < q := (Fact.out : q.Prime).pos
    obtain ⟨c, hc, h⟩ := el_redB q D st hI v hv hv2 k (by omega)
    obtain ⟨h1, h2, -⟩ := el_redA q D hq st hI v hv hv2 k (by omega)
    have hb : (gg st.B k).length = D ∧ ∀ a ∈ gg st.B k, a < q := hI.2.2.1 _ (el_mem st.B [] k hk)
    have hp := (hI.2.2.2 k hk).2.1
    refine ⟨(g (gg st.B k) (g st.pv k) : ZMod q) * c, mul_ne_zero ?_ hc, ?_⟩
    · intro h0; have h3 := congrArg ZMod.val h0
      rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (el_gP (· < q) _ _ _ hq hb.2)] at h3
      exact hp h3
    · rw [el_its]; dsimp only
      rw [el_zv1 _ _ _ _ (by omega) (el_gP (· < q) _ _ _ hq h2).le]
      have hbm : zv q (gg st.B k) ∈ el_sp q (zv q) st.B :=
        Submodule.subset_span ⟨_, el_mem st.B [] k hk, rfl⟩
      convert Submodule.sub_mem _ (Submodule.smul_mem _ (g (gg st.B k) (g st.pv k) : ZMod q) h)
        (Submodule.smul_mem _ (g (el_it q st.B st.pv v k).2 (g st.pv k) : ZMod q) hbm) using 1
      rw [smul_sub, smul_smul]; abel
theorem el_insS (q D : ℕ) [Fact q.Prime] (vec : List ℕ → List ℕ) (st : ESt) (hI : el_I q D st)
    (hS : el_sp q (zv q) st.B = el_sp q (fun τ => zv q (vec τ)) st.sl)
    (τ : List ℕ) (hv : (vec τ).length = D) (hv2 : ∀ a ∈ vec τ, a < q) :
    el_sp q (zv q) (insertG q vec st τ).B = el_sp q (fun τ => zv q (vec τ)) (insertG q vec st τ).sl ∧
    el_sp q (fun τ => zv q (vec τ)) (insertG q vec st τ).sl =
      el_sp q (fun τ => zv q (vec τ)) st.sl ⊔ Submodule.span (ZMod q) {zv q (vec τ)} := by
  obtain ⟨c, hc, h⟩ := el_redB q D st hI _ hv hv2 _ le_rfl
  rw [hS] at h
  unfold insertG; dsimp only; split_ifs with hs
  · refine ⟨hS, ?_⟩; symm; apply sup_eq_left.mpr; rw [Submodule.span_singleton_le_iff_mem]
    have hz : zv q (redAll q st.B st.pv (vec τ)) = 0 := funext fun i => by
      simp only [zv, Pi.zero_apply]
      rw [(el_gP (· = 0) _ 0 i rfl (List.sum_eq_zero_iff.mp hs) : (redAll q st.B st.pv (vec τ)).getD i 0 = 0)]
      simp
    change zv q _ - _ ∈ _ at h
    rw [show (el_it q st.B st.pv (vec τ) st.B.length).2 = redAll q st.B st.pv (vec τ) from rfl, hz,
      zero_sub, neg_mem_iff] at h
    have := Submodule.smul_mem _ c⁻¹ h; rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · simp only [el_sps, hS, and_true]
    exact el_swap _ _ _ c hc h
theorem el_spAll (q : ℕ) [Fact q.Prime] (vec : List ℕ → List ℕ) (D : ℕ)
    (hlen : ∀ τ, (vec τ).length = D) (hlt : ∀ τ, ∀ a ∈ vec τ, a < q) (C : List (List ℕ)) :
    ∀ i ≤ C.length, el_sp q (zv q) (el_st q vec C i).2.B = el_sp q (fun τ => zv q (vec τ)) (el_st q vec C i).2.sl ∧
      el_sp q (fun τ => zv q (vec τ)) (el_st q vec C i).2.sl = el_sp q (fun τ => zv q (vec τ)) (C.take i)
  | 0 => fun _ => ⟨by simp only [el_st, Function.iterate_zero, id, el_sp0],
      by simp only [el_st, Function.iterate_zero, id, el_sp0, List.take_zero]⟩
  | i + 1 => fun hi => by
    obtain ⟨h1, h2⟩ := el_spAll q vec D hlen hlt C i (by omega)
    rw [el_sts]
    obtain ⟨e1, e2⟩ := el_insS q D vec _ (el_invI q (Fact.out : q.Prime).pos vec D hlen hlt C i) h1
      (gg C i) (hlen _) (hlt _)
    refine ⟨e1, ?_⟩
    have : C.take (i + 1) = C.take i ++ [gg C i] := by
      have e : gg C i = C[i] := List.getD_eq_getElem _ _ (by omega)
      rw [e]; exact List.take_succ_eq_append_getElem (by omega)
    rw [e2, h2, this, el_sps]
theorem selectG_span (q : ℕ) [Fact q.Prime] (vec : List ℕ → List ℕ) (D : ℕ)
    (hlen : ∀ τ, (vec τ).length = D) (hlt : ∀ τ, ∀ a ∈ vec τ, a < q) (C : List (List ℕ)) :
    Submodule.span (ZMod q) {z | ∃ τ ∈ selectG q vec C, z = zv q (vec τ)} =
      Submodule.span (ZMod q) {z | ∃ τ ∈ C, z = zv q (vec τ)} := by
  have := (el_spAll q vec D hlen hlt C _ le_rfl).2
  rw [List.take_length] at this; exact this

end Alg
end PEqualNP.Outside.L_lib_1025

namespace PEqualNP.Outside.L_lib_1025
namespace Alg

def sgn {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (Q : Finset (Fin n × Fin n)) : ℤ :=
  ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : ℤ) -
    ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : ℤ)
section mob
variable {n : ℕ}
theorem mob_split (rows : List (Finset (Fin n × Fin n) × Bool)) (a : Fin n × Fin n) (Q) :
    sgn rows Q = sgn (rows.filter (fun t => decide (a ∈ t.1))) Q +
      sgn (rows.filter (fun t => !decide (a ∈ t.1))) Q := by
  induction rows with
  | nil => simp [sgn]
  | cons t l ih =>
    obtain ⟨s, b⟩ := t
    by_cases h1 : a ∈ s <;> by_cases h2 : Q ⊆ s <;> cases b <;>
      simp [sgn, h1, h2] at ih ⊢ <;> omega
theorem mob_ins (rows : List (Finset (Fin n × Fin n) × Bool)) (a : Fin n × Fin n) (Q) :
    sgn (rows.filter (fun t => decide (a ∈ t.1))) Q = sgn rows (insert a Q) := by
  induction rows with
  | nil => simp [sgn]
  | cons t l ih =>
    obtain ⟨s, b⟩ := t
    by_cases h1 : a ∈ s <;> by_cases h2 : Q ⊆ s <;> cases b <;>
      simp [sgn, h1, h2, Finset.insert_subset_iff] at ih ⊢ <;> omega
theorem mob_len (rows : List (Finset (Fin n × Fin n) × Bool)) (a : Fin n × Fin n) (P) :
    (rows.filter (fun t => decide (P ⊆ t.1))).length =
      ((rows.filter (fun t => decide (a ∈ t.1))).filter (fun t => decide (P ⊆ t.1))).length +
      ((rows.filter (fun t => !decide (a ∈ t.1))).filter (fun t => decide (P ⊆ t.1))).length := by
  induction rows with
  | nil => simp
  | cons t l ih =>
    by_cases h1 : a ∈ t.1 <;> by_cases h2 : P ⊆ t.1 <;> simp [h1, h2] at ih ⊢ <;> omega
theorem mob_abs (rows : List (Finset (Fin n × Fin n) × Bool)) (P) :
    (sgn rows P).natAbs ≤ (rows.filter (fun t => decide (P ⊆ t.1))).length := by
  induction rows with
  | nil => simp [sgn]
  | cons t l ih =>
    obtain ⟨s, b⟩ := t
    by_cases h2 : P ⊆ s <;> cases b <;> simp [sgn, h2] at ih ⊢ <;> omega
end mob

theorem mobius_bound {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool))
    (P R : Finset (Fin n × Fin n)) (hzero : ∀ S, S ⊂ R → sgn rows (P ∪ S) = 0) :
    2 ^ R.card * (sgn rows (P ∪ R)).natAbs ≤ (rows.filter (fun t => decide (P ⊆ t.1))).length := by
  induction R using Finset.induction_on generalizing rows with
  | empty => simpa using mob_abs rows P
  | insert a R ha ih =>
    have hs : ∀ S, S ⊂ R → insert a S ⊂ insert a R := fun S hS =>
      ⟨Finset.insert_subset_insert a hS.1, fun h => hS.2 (fun x hx => by
        have := h (Finset.mem_insert_of_mem hx)
        rcases Finset.mem_insert.1 this with rfl | h' <;> [exact absurd hx ha; exact h'])⟩
    have e1 : ∀ S, sgn (rows.filter (fun t => decide (a ∈ t.1))) (P ∪ S) = sgn rows (P ∪ insert a S) :=
      fun S => by rw [mob_ins, Finset.union_insert]
    have h1 := ih (rows.filter (fun t => decide (a ∈ t.1))) (fun S hS => by
      rw [e1]; exact hzero _ (hs S hS))
    have h2 := ih (rows.filter (fun t => !decide (a ∈ t.1))) (fun S hS => by
      have := mob_split rows a (P ∪ S)
      rw [e1, hzero _ (hs S hS), hzero _ (hS.trans (Finset.ssubset_insert ha))] at this
      omega)
    have e2 := mob_split rows a (P ∪ R)
    rw [e1, hzero _ (Finset.ssubset_insert ha)] at e2
    rw [e1] at h1
    have e3 : (sgn (rows.filter (fun t => !decide (a ∈ t.1))) (P ∪ R)).natAbs =
      (sgn rows (P ∪ insert a R)).natAbs := by omega
    rw [e3] at h2
    rw [mob_len rows a P, Finset.card_insert_of_notMem ha, pow_succ]
    nlinarith
end Alg
end PEqualNP.Outside.L_lib_1025

namespace PEqualNP.Outside.L_lib_1025
namespace Alg

theorem lv_gm {α : Type} (d : α) (S : List α) {j : ℕ} (hj : j < S.length) : S.getD j d ∈ S := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem lv_mg {α : Type} (d : α) {S : List α} {τ : α} (h : τ ∈ S) : ∃ j < S.length, S.getD j d = τ := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, hj, List.getD_eq_getElem _ _ hj⟩

theorem lv_cand (U : List ℕ) (S : List (List ℕ)) (τ : List ℕ) :
    τ ∈ cand U S ↔ ∃ ρ ∈ S, ∃ e ∈ U, τ = ρ ++ [e] := by
  simp only [cand, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, u, hu, rfl⟩; exact ⟨_, lv_gm _ _ hj, _, lv_gm _ _ hu, rfl⟩
  · rintro ⟨ρ, hρ, e, he, rfl⟩
    obtain ⟨j, hj, rfl⟩ := lv_mg [] hρ
    obtain ⟨u, hu, rfl⟩ := lv_mg 0 he
    exact ⟨j, hj, u, hu, rfl⟩

theorem lv_hits (pi pj : List ℕ) (F : List (List ℕ)) (fs : List ℕ) (C : List (List ℕ)) (τ : List ℕ) :
    τ ∈ hits pi pj F fs C ↔ τ ∈ C ∧ hit pi pj F fs τ ≠ 0 := by
  simp only [hits, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨j, hj, h⟩
    split_ifs at h with h0
    · simp at h
    · rw [List.mem_singleton] at h; subst h; exact ⟨lv_gm _ _ hj, h0⟩
  · rintro ⟨hτ, h0⟩
    obtain ⟨j, hj, rfl⟩ := lv_mg [] hτ
    exact ⟨j, hj, by simp only [h0, ↓reduceIte, List.mem_singleton]⟩

theorem lv_ls (q m : ℕ) (f : ℕ → ℕ) :
    ((((List.range m).map f).sum : ℕ) : ZMod q) = ∑ r ∈ Finset.range m, (f r : ZMod q) := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem lv_zv (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (τ : List ℕ) (k : ℕ) :
    zv q (vecL q N pi pj F τ) k = if k < 2 ^ N * F.length then
      zv q (wedgeLab q N pi pj τ) (k / F.length) * (chi F τ (k % F.length) : ZMod q) else 0 := by
  unfold zv vecL
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [ZMod.natCast_mod]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp

theorem lv_fun (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (τ : List ℕ) {r : ℕ} (hr : r < F.length) :
    LinearMap.funLeft (ZMod q) (ZMod q) (fun J => J * F.length + r) (zv q (vecL q N pi pj F τ)) =
      (chi F τ r : ZMod q) • zv q (wedgeLab q N pi pj τ) := by
  funext J
  simp only [LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul, lv_zv]
  have h1 : (J * F.length + r) / F.length = J := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  have h2 : (J * F.length + r) % F.length = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  rw [h1, h2]
  split_ifs with h
  · ring
  · have : 2 ^ N ≤ J := by
      by_contra h'; apply h
      calc J * F.length + r < (J + 1) * F.length := by rw [Nat.succ_mul]; omega
        _ ≤ 2 ^ N * F.length := Nat.mul_le_mul_right _ (by omega)
    have h3 : (wedgeLab q N pi pj τ)[J]? = none := by
      rw [List.getElem?_eq_none_iff, wedgeLab_length]; exact this
    simp [zv, h3]

theorem lv_chi (F : List (List ℕ)) (σ : List ℕ) (e r : ℕ) :
    chi F (σ ++ [e]) r = chi F σ r * (if 1 - g (gg F r) e = 0 then 1 else 0) := by
  have h1 : (List.range σ.length).map (fun i => 1 - g (gg F r) (g (σ ++ [e]) i)) =
      (List.range σ.length).map (fun i => 1 - g (gg F r) (g σ i)) :=
    List.map_congr_left (fun i hi => by rw [List.mem_range] at hi; simp [List.getElem?_append_left hi])
  have h2 : g (σ ++ [e]) σ.length = e := by simp
  simp only [chi, List.length_append, List.length_singleton, List.range_succ, List.map_append, List.sum_append,
    h1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2]
  split_ifs <;> omega

def lv_L (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (e : ℕ) : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q) :=
  LinearMap.pi (fun k => if k < 2 ^ N * F.length then
    ((if 1 - g (gg F (k % F.length)) e = 0 then 1 else 0 : ℕ) : ZMod q) •
      (LinearMap.proj (k / F.length) ∘ₗ LwZ q N (zv q (vv q N (g pj e))) ∘ₗ LwZ q N (zv q (vv q N (g pi e))) ∘ₗ
        LinearMap.funLeft (ZMod q) (ZMod q) (fun J => J * F.length + k % F.length)) else 0)

theorem lv_L_ap (q N : ℕ) (hq : 0 < q) (pi pj : List ℕ) (F : List (List ℕ)) (σ : List ℕ) (e : ℕ) :
    lv_L q N pi pj F e (zv q (vecL q N pi pj F σ)) = zv q (vecL q N pi pj F (σ ++ [e])) := by
  funext k
  rw [lv_zv]
  simp only [lv_L, LinearMap.pi_apply]
  by_cases hk : k < 2 ^ N * F.length
  · simp only [hk, ↓reduceIte]
    have hr : k % F.length < F.length := Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos F.length with h | h
      · rw [h, Nat.mul_zero] at hk; omega
      · exact h)
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, lv_fun q N pi pj F σ hr,
      map_smul, wedgeLab_snoc, zv_wedgeV q N hq, lv_chi, smul_eq_mul]
    simp [mul_comm]
  · simp [hk]

def lv_c (q : ℕ) (F : List (List ℕ)) (fs : List ℕ) : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q) :=
  ∑ r ∈ Finset.range F.length, (((g fs r : ℕ) : ZMod q) - ((1 - g fs r : ℕ) : ZMod q)) •
    LinearMap.funLeft (ZMod q) (ZMod q) (fun J => J * F.length + r)

theorem lv_c_ap (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (fs τ : List ℕ) :
    lv_c q F fs (zv q (vecL q N pi pj F τ)) =
      ((posC F fs τ : ZMod q) - (negC F fs τ : ZMod q)) • zv q (wedgeLab q N pi pj τ) := by
  rw [lv_c, LinearMap.sum_apply, posC, negC, lv_ls, lv_ls, ← Finset.sum_sub_distrib, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [LinearMap.smul_apply, lv_fun q N pi pj F τ (Finset.mem_range.mp hr), smul_smul]
  congr 1; push_cast; ring

theorem lv_snd (q N : ℕ) [Fact q.Prime] (pi pj : List ℕ) (F : List (List ℕ)) (fs τ : List ℕ)
    (h : lv_c q F fs (zv q (vecL q N pi pj F τ)) ≠ 0) : hit pi pj F fs τ ≠ 0 := by
  rw [lv_c_ap] at h
  have hc : clash pi pj τ = 0 := by
    by_contra hc; exact h (by rw [wedgeLab_zero q N pi pj τ hc, smul_zero])
  have hp : posC F fs τ ≠ negC F fs τ := by
    intro he; exact h (by rw [he, sub_self, zero_smul])
  simp [hit, hc, hp]

theorem lv_le (F : List (List ℕ)) (f : ℕ → ℕ) (h : ∀ r, f r ≤ 1) :
    ((List.range F.length).map f).sum ≤ F.length := by
  have := List.sum_le_length_nsmul ((List.range F.length).map f) 1 (by simpa using fun r _ => h r)
  simpa using this

theorem lv_cmp (q N K : ℕ) [Fact q.Prime] (hN : N = 2 * K) (pi pj : List ℕ) (F : List (List ℕ)) (fs τ : List ℕ)
    (hq : ∀ a ∈ ends pi pj τ, a < q) (hm : F.length < q) (hfs : ∀ a ∈ fs, a ≤ 1) (hl : τ.length ≤ K)
    (h : hit pi pj F fs τ ≠ 0) : lv_c q F fs (zv q (vecL q N pi pj F τ)) ≠ 0 := by
  have hc : clash pi pj τ = 0 := by by_contra hc; simp [hit, hc] at h
  have hp : posC F fs τ ≠ negC F fs τ := by intro he; simp [hit, he] at h
  have hch : ∀ r, chi F τ r ≤ 1 := fun r => by unfold chi; split_ifs <;> omega
  have hg : ∀ r, g fs r ≤ 1 := fun r => by
    rw [g, List.getD_eq_getElem?_getD]
    cases h' : fs[r]? with
    | none => simp
    | some a => simpa using hfs a (List.mem_of_getElem? h')
  have h1 : posC F fs τ < q := lt_of_le_of_lt (lv_le F _ (fun r =>
    le_trans (Nat.mul_le_mul (hg r) (hch r)) (by norm_num))) hm
  have h2 : negC F fs τ < q := lt_of_le_of_lt (lv_le F _ (fun r =>
    le_trans (Nat.mul_le_mul (Nat.sub_le 1 _) (hch r)) (by norm_num))) hm
  rw [lv_c_ap]
  refine smul_ne_zero ?_ (wedgeLab_ne_zero q N pi pj τ hc (by omega) hq)
  intro he; apply hp
  have := congrArg ZMod.val (sub_eq_zero.mp he)
  rwa [ZMod.val_cast_of_lt h1, ZMod.val_cast_of_lt h2] at this

def lv_I (q N : ℕ) (pi pj U : List ℕ) (F : List (List ℕ)) (fs : List ℕ) (i : ℕ)
    (st : List (List ℕ) × List (List ℕ)) : Prop :=
  (st.2 = [] ∧ (∀ τ ∈ st.1, τ.length = i ∧ ∀ e ∈ τ, e ∈ U) ∧
    (∀ σ : List ℕ, σ.length = i → (∀ e ∈ σ, e ∈ U) → zv q (vecL q N pi pj F σ) ∈
      Submodule.span (ZMod q) {z | ∃ τ ∈ st.1, z = zv q (vecL q N pi pj F τ)}) ∧
    ∀ σ : List ℕ, (∀ e ∈ σ, e ∈ U) → σ.length < i → hit pi pj F fs σ = 0) ∨
  (∃ τ : List ℕ, st.2 = [τ] ∧ (∀ e ∈ τ, e ∈ U) ∧ τ.length < i ∧ hit pi pj F fs τ ≠ 0 ∧
    ∀ σ : List ℕ, (∀ e ∈ σ, e ∈ U) → σ.length < τ.length → hit pi pj F fs σ = 0)

theorem lv_step (q N K : ℕ) [Fact q.Prime] (hN : N = 2 * K) (pi pj U : List ℕ)
    (F : List (List ℕ)) (fs : List ℕ)
    (hq : ∀ τ : List ℕ, (∀ e ∈ τ, e ∈ U) → ∀ a ∈ ends pi pj τ, a < q)
    (hm : F.length < q) (hfs : ∀ a ∈ fs, a ≤ 1) (i : ℕ) (hi : i ≤ K) (st : List (List ℕ) × List (List ℕ))
    (h : lv_I q N pi pj U F fs i st) : lv_I q N pi pj U F fs (i + 1) (lvl q N pi pj U F fs st) := by
  have q0 : 0 < q := (Fact.out : q.Prime).pos
  have hvl : ∀ τ, (vecL q N pi pj F τ).length = 2 ^ N * F.length := fun τ => by simp [vecL]
  have hvq : ∀ τ, ∀ a ∈ vecL q N pi pj F τ, a < q := fun τ a ha => by
    simp only [vecL, List.mem_map] at ha; obtain ⟨k, _, rfl⟩ := ha; exact Nat.mod_lt _ q0
  rcases h with ⟨h2, hC, hsp, hno⟩ | ⟨τ, h2, hU, hl, hh, hmin⟩
  · unfold lvl; simp only [h2, List.length_nil, ↓reduceIte]
    split_ifs with hH
    · left
      refine ⟨rfl, fun τ hτ => ?_, fun σ hσ hU => ?_, fun σ hU hl => ?_⟩
      · obtain ⟨ρ, hρ, e, he, rfl⟩ := (lv_cand _ _ _).mp hτ
        obtain ⟨h1, h3⟩ := hC ρ (selectG_sub _ _ _ ρ hρ)
        refine ⟨by simp [h1], fun x hx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact h3 x hx
        · rw [List.mem_singleton.mp hx]; exact he
      · obtain ⟨ρ, e, rfl⟩ : ∃ ρ e, σ = ρ ++ [e] := by
          rcases List.eq_nil_or_concat σ with h0 | ⟨ρ, e, h0⟩
          · subst h0; simp at hσ
          · exact ⟨ρ, e, by rw [h0, List.concat_eq_append]⟩
        have hρ := hsp ρ (by simpa using hσ) (fun x hx => hU x (List.mem_append_left _ hx))
        rw [← selectG_span q _ _ hvl hvq] at hρ
        have := Submodule.apply_mem_span_image_of_mem_span (lv_L q N pi pj F e) hρ
        rw [lv_L_ap q N q0] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
        exact ⟨τ ++ [e], (lv_cand _ _ _).mpr ⟨τ, hτ, e, hU e (by simp), rfl⟩, lv_L_ap q N q0 _ _ _ _ _⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
        · exact hno σ hU hl
        by_contra hσ
        have hc := lv_cmp q N K hN pi pj F fs σ (hq σ hU) hm hfs (by omega) hσ
        apply hc
        have hk : Submodule.span (ZMod q) {z | ∃ τ ∈ st.1, z = zv q (vecL q N pi pj F τ)} ≤
            LinearMap.ker (lv_c q F fs) := by
          rw [Submodule.span_le]
          rintro _ ⟨τ, hτ, rfl⟩
          by_contra h0
          have := (lv_hits pi pj F fs st.1 τ).mpr ⟨hτ, lv_snd q N pi pj F fs τ h0⟩
          rw [List.length_eq_zero_iff] at hH; rw [hH] at this; simp at this
        exact hk (hsp σ hl hU)
    · right
      have h0 : 0 < (hits pi pj F fs st.1).length := Nat.pos_of_ne_zero hH
      obtain ⟨hτ, hh⟩ := (lv_hits pi pj F fs st.1 (gg (hits pi pj F fs st.1) 0)).mp (lv_gm [] _ h0)
      obtain ⟨h1, h3⟩ := hC _ hτ
      exact ⟨_, rfl, h3, by omega, hh, fun σ hU hl => hno σ hU (by omega)⟩
  · unfold lvl; simp only [h2, List.length_singleton, one_ne_zero, ↓reduceIte]
    exact Or.inr ⟨τ, h2, hU, by omega, hh, hmin⟩

theorem found_spec (q N K : ℕ) [Fact q.Prime] (hN : N = 2 * K) (pi pj U : List ℕ)
    (F : List (List ℕ)) (fs : List ℕ)
    (hq : ∀ τ : List ℕ, (∀ e ∈ τ, e ∈ U) → ∀ a ∈ ends pi pj τ, a < q)
    (hm : F.length < q) (hfs : ∀ a ∈ fs, a ≤ 1) (_hfsl : fs.length = F.length) :
    (((lvl q N pi pj U F fs)^[K + 1] ([[]], [])).2 = [] ∧
      ∀ τ : List ℕ, (∀ e ∈ τ, e ∈ U) → τ.length ≤ K → hit pi pj F fs τ = 0) ∨
    (∃ τ : List ℕ, ((lvl q N pi pj U F fs)^[K + 1] ([[]], [])).2 = [τ] ∧ (∀ e ∈ τ, e ∈ U) ∧
      τ.length ≤ K ∧ hit pi pj F fs τ ≠ 0 ∧
      ∀ σ : List ℕ, (∀ e ∈ σ, e ∈ U) → σ.length < τ.length → hit pi pj F fs σ = 0) := by
  have hall : ∀ i ≤ K + 1, lv_I q N pi pj U F fs i ((lvl q N pi pj U F fs)^[i] ([[]], [])) := by
    intro i hi
    induction i with
    | zero =>
      left
      refine ⟨rfl, fun τ hτ => by simp at hτ; simp [hτ], fun σ hσ _ => ?_, fun σ _ hl => by simp at hl⟩
      rw [List.length_eq_zero_iff] at hσ; subst hσ
      exact Submodule.subset_span ⟨[], by simp, rfl⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact lv_step q N K hN pi pj U F fs hq hm hfs i (by omega) _ (ih (by omega))
  rcases hall (K + 1) le_rfl with ⟨h2, -, -, hno⟩ | ⟨τ, h2, hU, hl, hh, hmin⟩
  · exact Or.inl ⟨h2, fun τ hU hl => hno τ hU (by omega)⟩
  · exact Or.inr ⟨τ, h2, hU, by omega, hh, hmin⟩

end Alg
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg
open Lib.R Lib.Universal Lib.Loop

theorem tqzN {f : List Bool → ℕ} (h : NatR f) :
    ∀ ⦃p : List Bool → List Bool⦄, Lib.CPTs p → NatR (fun t => f (p t)) :=
  fun _ hp => Lib.Machines.cpt_comp (g := fun s => un (f s)) hp h
theorem tqzV {f : List Bool → List ℕ} (h : VecR f) :
    ∀ ⦃p : List Bool → List Bool⦄, Lib.CPTs p → VecR (fun t => f (p t)) :=
  fun _ hp => Lib.Machines.cpt_comp (g := fun s => encV (f s)) hp h
theorem tqzL {f : List Bool → List (List ℕ)} (h : LLR f) :
    ∀ ⦃p : List Bool → List Bool⦄, Lib.CPTs p → LLR (fun t => f (p t)) :=
  fun _ hp => Lib.Machines.cpt_comp (g := fun s => encLL (f s)) hp h
theorem tqzI : ∀ ⦃p : List Bool → List Bool⦄, Lib.CPTs p → NatR (fun t => (unpairB (p t)).1.length) :=
  fun _ hp => natR_len (cpt_unpairB1_1 hp)
theorem tqgN {n : List Bool → ℕ} {H : ℕ → List Bool → ℕ} (hn : NatR n)
    (hH : NatR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s => (List.range (n s)).map (fun i => H i s)) := vecR_gen Lib.Machines.cpt_id hn hH
theorem tqgF {n : List Bool → ℕ} {H : ℕ → List Bool → List ℕ} (hn : NatR n)
    (hH : VecR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s => (List.range (n s)).flatMap (fun i => H i s)) := vecR_flat Lib.Machines.cpt_id hn hH
theorem tqgL {n : List Bool → ℕ} {H : ℕ → List Bool → List ℕ} (hn : NatR n)
    (hH : VecR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s => (List.range (n s)).map (fun i => H i s)) := llR_gen Lib.Machines.cpt_id hn hH
theorem tqgLF {n : List Bool → ℕ} {H : ℕ → List Bool → List (List ℕ)} (hn : NatR n)
    (hH : LLR (fun t => H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s => (List.range (n s)).flatMap (fun i => H i s)) := llR_flat Lib.Machines.cpt_id hn hH
theorem tqnE {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if a s = b s then x s else y s) :=
  cptE (cpt_ite_eq ha hb hx hy) (fun _ => (apply_ite un _ _ _).symm)
theorem tqnL {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if a s < b s then x s else y s) :=
  cptE (cpt_ite_lt ha hb hx hy) (fun _ => (apply_ite un _ _ _).symm)
theorem tqnT {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if (a s).testBit (b s) then x s else y s) :=
  cptE (cpt_ite_eq (natR_testBit ha hb) (natR_const 1) hx hy)
    (fun s => by dsimp only; cases (a s).testBit (b s) <;> rfl)
theorem tqvE {a b : List Bool → ℕ} {x y : List Bool → List ℕ} (ha : NatR a) (hb : NatR b)
    (hx : VecR x) (hy : VecR y) : VecR (fun s => if a s = b s then x s else y s) :=
  cptE (cpt_ite_eq ha hb hx hy) (fun _ => (apply_ite encV _ _ _).symm)
theorem tqvL {a b : List Bool → ℕ} {x y : List Bool → List ℕ} (ha : NatR a) (hb : NatR b)
    (hx : VecR x) (hy : VecR y) : VecR (fun s => if a s < b s then x s else y s) :=
  cptE (cpt_ite_lt ha hb hx hy) (fun _ => (apply_ite encV _ _ _).symm)
theorem tqlE {a b : List Bool → ℕ} {x y : List Bool → List (List ℕ)} (ha : NatR a) (hb : NatR b)
    (hx : LLR x) (hy : LLR y) : LLR (fun s => if a s = b s then x s else y s) :=
  cptE (cpt_ite_eq ha hb hx hy) (fun _ => (apply_ite encLL _ _ _).symm)

theorem tqI {n : List Bool → ℕ} (hn : NatR n) : VecR (fun s => pI (n s)) := by
  have := tqzN hn; unfold pI
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgF, tqvL, vecR_single, vecR_nil, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem tqJ {n : List Bool → ℕ} (hn : NatR n) : VecR (fun s => pJ (n s)) := by
  have := tqzN hn; unfold pJ
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgF, tqvL, vecR_single, vecR_nil, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_nV : NatR (fun s => nV s) := natR_runAt Lib.Machines.cpt_id (natR_const 0)
theorem tqcN {f : List Bool → ℕ} (h : NatR f) : Lib.CPTs (fun s => un (f s)) := h
theorem tqcV {f : List Bool → List ℕ} (h : VecR f) : Lib.CPTs (fun s => encV (f s)) := h
theorem natR_pN : NatR (fun s => pN s) := natR_vlen (tqI natR_nV)
theorem vecR_pI {n : List Bool → ℕ} (hn : NatR n) : VecR (fun s => pI (n s)) := tqI hn
theorem vecR_pJ {n : List Bool → ℕ} (hn : NatR n) : VecR (fun s => pJ (n s)) := tqJ hn
theorem vecR_Em : VecR (fun s => Em s) := by
  unfold Em bit
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, natR_bit, natR_add, natR_const, tqzN natR_nV, tqzN natR_pN, tqzI,
    Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_Pm : VecR (fun s => Pm s) := by
  unfold Pm bit
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, natR_bit, natR_add, natR_const, tqzN natR_nV, tqzN natR_pN, tqzI,
    Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_lenV : NatR (fun s => lenV s) := by
  unfold lenV runAt oL
  apply_rules (maxDepth := 500) (transparency := .reducible) [natR_runAt, natR_add, natR_mul, natR_const, natR_nV, natR_pN, Lib.Machines.cpt_id]
theorem llR_rowM : LLR (fun s => rowM s) := by
  unfold rowM oR oL bit
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgL, tqgN, natR_bit, natR_add,
    natR_mul, natR_const, tqzN natR_nV, tqzN natR_pN, tqzN natR_lenV, tqzI, Lib.Machines.cpt_id,
    cpt_unpairB2_1]
theorem vecR_rowS : VecR (fun s => rowS s) := by
  unfold rowS oR oL bit
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, natR_bit, natR_add, natR_mul,
    natR_const, tqzN natR_nV, tqzN natR_pN, tqzN natR_lenV, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem llR_Frows {pm : List Bool → List ℕ} {rows : List Bool → List (List ℕ)} (hp : VecR pm)
    (hr : LLR rows) : LLR (fun s => Frows (pm s) (rows s)) := by
  have := tqzV hp; have := tqzL hr; unfold Frows missP
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgLF, tqlE, llR_single, llR_nil,
    vecR_row, natR_sum, tqgN, natR_mul, natR_sub, natR_get, natR_vlen, natR_llen, natR_const, tqzI,
    Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_Fsig {pm sg : List Bool → List ℕ} {rows : List Bool → List (List ℕ)} (hp : VecR pm)
    (hr : LLR rows) (hs : VecR sg) : VecR (fun s => Fsig (pm s) (rows s) (sg s)) := by
  have := tqzV hp; have := tqzL hr; have := tqzV hs; unfold Fsig missP
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgF, tqvE, vecR_single, vecR_nil,
    vecR_row, natR_sum, tqgN, natR_mul, natR_sub, natR_get, natR_vlen, natR_llen, natR_const, tqzI,
    Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_Uset {pi pj em pm : List Bool → List ℕ} (hi : VecR pi) (hj : VecR pj) (he : VecR em)
    (hp : VecR pm) : VecR (fun s => Uset (pi s) (pj s) (em s) (pm s)) := by
  have := tqzV hi; have := tqzV hj; have := tqzV he; have := tqzV hp; unfold Uset inVP
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgF, tqvE, vecR_single, vecR_nil,
    natR_sum, tqgN, natR_mul, tqnE, natR_add, natR_get, natR_vlen, natR_const, tqzI,
    Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_firstNZ {v : List Bool → List ℕ} (hv : VecR v) : NatR (fun s => firstNZ (v s)) := by
  have := tqzV hv; unfold firstNZ
  apply_rules (maxDepth := 500) (transparency := .reducible) [natR_sum, tqgN, tqnE, natR_add,
    natR_get, natR_vlen, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_primeAbove {B : List Bool → ℕ} (hB : NatR B) : NatR (fun s => primeAbove (B s)) := by
  have := tqzN hB; unfold primeAbove isPr
  apply_rules (maxDepth := 500) (transparency := .reducible) [natR_firstNZ, natR_sum, tqgN, tqnE,
    tqnL, natR_add, natR_mod, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]

end Alg
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg
open Lib.R Lib.Universal Lib.Loop

theorem tqW (q N : ℕ) (x v : List ℕ) : wedgeV q N x v = (List.range (2 ^ N)).map (fun J =>
  ((List.range N).map (fun b => if J.testBit b then
      (if ((List.range N).map (fun c => if b < c then (if J.testBit c then 1 else 0) else 0)).sum % 2 = 0
        then g v b * g x (J - 2 ^ b % (J + 1)) % q else q - g v b * g x (J - 2 ^ b % (J + 1)) % q)
    else 0)).sum % q) := by
  unfold wedgeV; congr 1; funext J; congr 3; funext b
  by_cases h : J.testBit b
  · rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (Nat.ge_two_pow_of_testBit h))]
  · simp [h]
theorem vecR_wedgeV {q N : List Bool → ℕ} {x v : List Bool → List ℕ} (hq : NatR q) (hN : NatR N)
    (hP : NatR (fun s => 2 ^ N s)) (hx : VecR x) (hv : VecR v) :
    VecR (fun s => wedgeV (q s) (N s) (x s) (v s)) := by
  have := tqzN hq; have := tqzN hN; have := tqzN hP; have := tqzV hx; have := tqzV hv
  simp only [tqW]
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, dsl_powmodS, natR_mod, natR_sum, tqnT, tqnE, tqnL,
    natR_mul, natR_sub, natR_get, natR_add, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_vv {q N a : List Bool → ℕ} (hq : NatR q) (hq0 : ∀ s, 0 < q s) (hN : NatR N) (ha : NatR a) :
    VecR (fun s => vv (q s) (N s) (a s)) := by
  have e : (fun s => vv (q s) (N s) (a s)) =
      fun s => (List.range (N s)).map (fun b => a s ^ b % (q s - 1 + 1)) := by
    funext s; simp only [vv, Nat.sub_add_cancel (hq0 s)]
  rw [e]; have hq1 := natR_sub hq (natR_const 1)
  have := tqzN hq1; have := tqzN ha
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, dsl_powmodS, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_e0 {q N : List Bool → ℕ} (hq : NatR q) (hP : NatR (fun s => 2 ^ N s)) :
    VecR (fun s => e0 (q s) (N s)) := by
  have := tqzN hq; unfold e0
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, tqnE, natR_mod, natR_const, tqzI, Lib.Machines.cpt_id,
    cpt_unpairB2_1]
def tqS (q N : ℕ) (pi pj τ : List ℕ) (p : ℕ × List ℕ) : ℕ × List ℕ :=
  (p.1 + 1, wedgeV q N (wedgeV q N p.2 (vv q N (g pi (g τ p.1)))) (vv q N (g pj (g τ p.1))))
def tqE (s : List Bool) (p : ℕ × List ℕ) : List Bool := pairB (un p.1) (pairB (encV p.2) s)
def tqT (q N : List Bool → ℕ) (pi pj τ : List Bool → List ℕ) (t : List Bool) : List Bool :=
  tqE (unpairB (unpairB t).2).2 (tqS (q (unpairB (unpairB t).2).2) (N (unpairB (unpairB t).2).2)
    (pi (unpairB (unpairB t).2).2) (pj (unpairB (unpairB t).2).2) (τ (unpairB (unpairB t).2).2)
    ((unpairB t).1.length, decV (unpairB (unpairB t).2).1))
theorem tqit (q N : List Bool → ℕ) (pi pj τ : List Bool → List ℕ) (s : List Bool) (k : ℕ) :
    ∀ p, (tqT q N pi pj τ)^[k] (tqE s p) = tqE s ((tqS (q s) (N s) (pi s) (pj s) (τ s))^[k] p) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    have : tqT q N pi pj τ (tqE s p) = tqE s (tqS (q s) (N s) (pi s) (pj s) (τ s) p) := by
      simp [tqT, tqE, unpairB_pairB, decV_encV]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, this, ih]
theorem tqinv (q N : ℕ) (pi pj τ : List ℕ) (hq : 0 < q) (k : ℕ) :
    ((tqS q N pi pj τ)^[k] (0, e0 q N)).1 = k ∧ ((tqS q N pi pj τ)^[k] (0, e0 q N)).2.length = 2 ^ N
      ∧ ∀ a ∈ ((tqS q N pi pj τ)^[k] (0, e0 q N)).2, a < q := by
  induction k with
  | zero =>
    refine ⟨rfl, by simp [e0], fun a ha => ?_⟩
    simp only [Function.iterate_zero, id, e0, List.mem_map, List.mem_range] at ha
    obtain ⟨J, -, rfl⟩ := ha
    split_ifs <;> simp [Nat.mod_lt _ hq, hq]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨by simp [tqS, ih.1], by simp [tqS, wedgeV], fun a ha => ?_⟩
    simp only [tqS, wedgeV, List.mem_map, List.mem_range] at ha
    obtain ⟨J, -, rfl⟩ := ha
    exact Nat.mod_lt _ hq
theorem vecR_wedgeLab {q N : List Bool → ℕ} {pi pj τ : List Bool → List ℕ} (hq : NatR q)
    (hq0 : ∀ s, 0 < q s) (hN : NatR N) (hP : NatR (fun s => 2 ^ N s)) (hi : VecR pi)
    (hj : VecR pj) (ht : VecR τ) : VecR (fun s => wedgeLab (q s) (N s) (pi s) (pj s) (τ s)) := by
  have hT : Lib.CPTs (tqT q N pi pj τ) := by
    have := tqzN hq; have := tqzN hN; have := tqzN hP; have := tqzV hi; have := tqzV hj; have := tqzV ht
    unfold tqT tqE tqS; dsimp only
    apply_rules (maxDepth := 500) (transparency := .reducible) [cpt_pairB2, tqcN, tqcV, vecR_wedgeV, vecR_vv, vecR_dec,
      natR_get, natR_add, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1, cpt_unpairB1_1]
    all_goals exact fun _ => hq0 _
  have hA : Lib.CPTs (fun s => tqE s (0, e0 (q s) (N s))) := by
    unfold tqE; dsimp only
    apply_rules (maxDepth := 500) (transparency := .reducible) [cpt_pairB2, tqcN, tqcV, vecR_e0, natR_const,
      Lib.Machines.cpt_id]
  obtain ⟨Pt, ht'⟩ := natR_le_poly (natR_vlen ht)
  obtain ⟨PP, hP'⟩ := natR_le_poly hP
  obtain ⟨Pq, hq'⟩ := natR_le_poly hq
  have := cpt_iterBound hT (natR_vlen ht) hA
    (Polynomial.C 2 * Pt + Polynomial.C 2 * (PP + PP * Pq) + Polynomial.X + Polynomial.C 2) (by
      intro s i hi'
      obtain ⟨h1, h4, h2⟩ := tqinv (q s) (N s) (pi s) (pj s) (τ s) (hq0 s) i
      have h3 := List.sum_le_length_nsmul _ (q s) (fun a ha => (h2 a ha).le)
      have h5 := Nat.mul_le_mul (hP' s) (hq' s)
      have h6 := ht' s; have h7 := hP' s
      simp only [un_length] at hi'
      rw [h4] at h3; rw [tqit]
      simp only [tqE, pairB_length, un_length, encV_length, smul_eq_mul, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at *
      linarith)
  refine cptE (vecR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 this))) (fun s => ?_)
  have e : wedgeLab (q s) (N s) (pi s) (pj s) (τ s) =
    ((tqS (q s) (N s) (pi s) (pj s) (τ s))^[(τ s).length] (0, e0 (q s) (N s))).2 := rfl
  dsimp only; rw [e, tqit]; simp only [un_length, tqE, unpairB_pairB, decV_encV]
theorem natR_chi {F : List Bool → List (List ℕ)} {τ : List Bool → List ℕ} {r : List Bool → ℕ}
    (hF : LLR F) (ht : VecR τ) (hr : NatR r) : NatR (fun s => chi (F s) (τ s) (r s)) := by
  have := tqzL hF; have := tqzV ht; have := tqzN hr; unfold chi
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqnE, natR_sum, tqgN, natR_sub, natR_get, vecR_row,
    natR_vlen, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_vecL {q N : List Bool → ℕ} {pi pj τ : List Bool → List ℕ}
    {F : List Bool → List (List ℕ)} (hq : NatR q) (hq0 : ∀ s, 0 < q s) (hN : NatR N)
    (hP : NatR (fun s => 2 ^ N s)) (hi : VecR pi) (hj : VecR pj) (hF : LLR F) (ht : VecR τ) :
    VecR (fun s => vecL (q s) (N s) (pi s) (pj s) (F s) (τ s)) := by
  have := tqzN hq; have := tqzN hN; have := tqzN hP; have := tqzV hi; have := tqzV hj; have := tqzL hF
  have := tqzV ht
  have : ∀ ⦃p : List Bool → List Bool⦄, ∀ s, 0 < q (p s) := fun _ s => hq0 _
  unfold vecL
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, natR_mod, natR_mul, natR_get, natR_div, natR_llen,
    vecR_wedgeLab, natR_chi, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_posC {F : List Bool → List (List ℕ)} {fs τ : List Bool → List ℕ} (hF : LLR F)
    (hf : VecR fs) (ht : VecR τ) : NatR (fun s => posC (F s) (fs s) (τ s)) := by
  have := tqzL hF; have := tqzV hf; have := tqzV ht; unfold posC
  apply_rules (maxDepth := 500) (transparency := .reducible) [natR_sum, tqgN, natR_mul, natR_get, natR_llen, natR_chi,
    tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_negC {F : List Bool → List (List ℕ)} {fs τ : List Bool → List ℕ} (hF : LLR F)
    (hf : VecR fs) (ht : VecR τ) : NatR (fun s => negC (F s) (fs s) (τ s)) := by
  have := tqzL hF; have := tqzV hf; have := tqzV ht; unfold negC
  apply_rules (maxDepth := 500) (transparency := .reducible) [natR_sum, tqgN, natR_mul, natR_sub, natR_const, natR_get,
    natR_llen, natR_chi, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem vecR_ends {pi pj τ : List Bool → List ℕ} (hi : VecR pi) (hj : VecR pj) (ht : VecR τ) :
    VecR (fun s => ends (pi s) (pj s) (τ s)) := by
  have := tqzV hi; have := tqzV hj; have := tqzV ht; unfold ends
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqgN, natR_mul, natR_vlen, tqnE, natR_mod, natR_div,
    natR_get, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]
theorem natR_hit {pi pj fs τ : List Bool → List ℕ} {F : List Bool → List (List ℕ)} (hi : VecR pi)
    (hj : VecR pj) (hF : LLR F) (hf : VecR fs) (ht : VecR τ) :
    NatR (fun s => hit (pi s) (pj s) (F s) (fs s) (τ s)) := by
  have := tqzV hi; have := tqzV hj; have := tqzL hF; have := tqzV hf; have := tqzV ht; unfold hit clash
  apply_rules (maxDepth := 500) (transparency := .reducible) [tqnE, tqnL, natR_posC, natR_negC, natR_sum, tqgN, natR_get,
    natR_vlen, vecR_ends, natR_const, tqzI, Lib.Machines.cpt_id, cpt_unpairB2_1]

end Alg
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg
open Lib.R Lib.Universal

theorem tcC {f h : List Bool → List Bool} (hf : Lib.CPTs f) (hh : Lib.CPTs h) :
    Lib.CPTs (fun s => f (h s)) := Lib.Machines.cpt_comp hh hf
theorem tcn1 {a : List Bool → ℕ} (h : NatR a) : NatR (fun t => a (unpairB t).1) := tcC h cpt_unpairB1
theorem tcn2 {a : List Bool → ℕ} (h : NatR a) : NatR (fun t => a (unpairB t).2) := tcC h cpt_unpairB2
theorem tcv1 {a : List Bool → List ℕ} (h : VecR a) : VecR (fun t => a (unpairB t).1) := tcC h cpt_unpairB1
theorem tcv2 {a : List Bool → List ℕ} (h : VecR a) : VecR (fun t => a (unpairB t).2) := tcC h cpt_unpairB2
theorem tcl1 {a : List Bool → List (List ℕ)} (h : LLR a) : LLR (fun t => a (unpairB t).1) :=
  tcC h cpt_unpairB1
theorem tcl2 {a : List Bool → List (List ℕ)} (h : LLR a) : LLR (fun t => a (unpairB t).2) :=
  tcC h cpt_unpairB2
theorem tci : NatR (fun t => (unpairB t).1.length) := natR_len cpt_unpairB1
theorem tci2 : NatR (fun t => (unpairB (unpairB t).2).1.length) := natR_len (cpt_unpairB1_1 cpt_unpairB2)
theorem tcNI {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if a s = b s then x s else y s) :=
  Lib.Loop.cptE (cpt_ite_eq ha hb hx hy) (fun s => (apply_ite un _ _ _).symm)
theorem tcNL {a b x y : List Bool → ℕ} (ha : NatR a) (hb : NatR b) (hx : NatR x) (hy : NatR y) :
    NatR (fun s => if a s < b s then x s else y s) :=
  Lib.Loop.cptE (cpt_ite_lt ha hb hx hy) (fun s => (apply_ite un _ _ _).symm)
theorem tcLI {a b : List Bool → ℕ} {x y : List Bool → List (List ℕ)} (ha : NatR a) (hb : NatR b)
    (hx : LLR x) (hy : LLR y) : LLR (fun s => if a s = b s then x s else y s) :=
  Lib.Loop.cptE (cpt_ite_eq ha hb hx hy) (fun s => (apply_ite encLL _ _ _).symm)

theorem tc_unl (n : ℕ) : (un n).length = n := by simp [un]
theorem tc_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [dbl, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
    omega
theorem tc_ell (S : List (List ℕ)) :
    (encLL S).length = (S.map (fun v => 2 * (encV v).length + 1)).sum := by
  induction S with
  | nil => rfl
  | cons v S ih =>
    simp only [encLL, List.flatMap_cons, List.length_append, List.length_cons, tc_dbl, List.map_cons,
      List.sum_cons] at *
    omega
theorem tc_ellm {S : List (List ℕ)} {v : List ℕ} (h : v ∈ S) :
    (encV v).length ≤ (encLL S).length := by
  rw [tc_ell]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun v => 2 * (encV v).length + 1) h)
  omega
theorem tc_elle {S : List (List ℕ)} {M : ℕ} (h : ∀ v ∈ S, (encV v).length ≤ M) :
    (encLL S).length ≤ S.length * (2 * M + 1) := by
  rw [tc_ell]
  have := List.sum_le_length_nsmul (S.map (fun v => 2 * (encV v).length + 1)) (2 * M + 1)
    (by simp only [List.mem_map]; rintro _ ⟨v, hv, rfl⟩; have := h v hv; omega)
  simpa using this
theorem tc_sumle {l : List ℕ} {q : ℕ} (h : ∀ a ∈ l, a ≤ q) : l.sum ≤ l.length * q := by
  have := List.sum_le_length_nsmul l q h; simpa using this
theorem tc_evle {v : List ℕ} {M : ℕ} (h : ∀ a ∈ v, a ≤ M) : (encV v).length ≤ v.length * (M + 1) := by
  rw [encV_length, Nat.mul_succ]; have := tc_sumle h; omega
theorem tc_itinv {α : Type} (F : ℕ × α → ℕ × α) (P : α → Prop) (x : ℕ × α) (h0 : P x.2)
    (hs : ∀ y, P y.2 → P (F y).2) (i : ℕ) : P (F^[i] x).2 := by
  induction i with
  | zero => exact h0
  | succ i ih => rw [Function.iterate_succ_apply']; exact hs _ ih
theorem tc_isnd {α : Type} (h : α → α) (k n : ℕ) (a : α) :
    ((fun p : ℕ × α => (p.1 + 1, h p.2))^[k] (n, a)).2 = h^[k] a := by
  induction k generalizing n a with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]

def tcG {α : Type} (E : α → List Bool) (D : List Bool → α) (f : List Bool → ℕ → α → α)
    (t : List Bool) : List Bool :=
  pairB (unpairB t).1 (pairB (true :: (unpairB (unpairB t).2).1)
    (E (f (unpairB t).1 (unpairB (unpairB t).2).1.length (D (unpairB (unpairB t).2).2))))
theorem tc_lp {α : Type} (E : α → List Bool) (D : List Bool → α) (hD : ∀ a, D (E a) = a)
    (f : List Bool → ℕ → α → α) (k : List Bool → ℕ) (a0 : List Bool → α)
    (hf : Lib.CPTs (fun t => E (f (unpairB t).1 (unpairB (unpairB t).2).1.length
      (D (unpairB (unpairB t).2).2))))
    (hk : NatR k) (ha : Lib.CPTs (fun u => E (a0 u))) (B : List Bool → ℕ) (hB : NatR B)
    (hb : ∀ u i, i ≤ k u →
      (E ((fun p : ℕ × α => (p.1 + 1, f u p.1 p.2))^[i] (0, a0 u)).2).length ≤ B u) :
    Lib.CPTs (fun u => E ((fun p : ℕ × α => (p.1 + 1, f u p.1 p.2))^[k u] (0, a0 u)).2) := by
  have hg : Lib.CPTs (tcG E D f) :=
    cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_cons1 true (cpt_unpairB1_1 cpt_unpairB2)) hf)
  have h1 : ∀ u i, ((fun p : ℕ × α => (p.1 + 1, f u p.1 p.2))^[i] (0, a0 u)).1 = i := by
    intro u i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih]
  have h2 : ∀ u i, (tcG E D f)^[i] (pairB u (pairB [] (E (a0 u)))) =
      pairB u (pairB (un i) (E ((fun p : ℕ × α => (p.1 + 1, f u p.1 p.2))^[i] (0, a0 u)).2)) := by
    intro u i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp only [tcG, unpairB_pairB, hD, tc_unl, h1]
      rfl
  obtain ⟨P, hP⟩ := natR_le_poly (natR_add (natR_add (natR_mul (natR_const 2)
    (natR_len Lib.Machines.cpt_id)) (natR_mul (natR_const 2) hk)) (natR_add hB (natR_const 2)))
  have hI := cpt_iterBound hg hk (cpt_pairB2 Lib.Machines.cpt_id (cpt_pairB2 (cpt_const []) ha)) P
    (by
      intro u i hi
      rw [tc_unl] at hi
      rw [h2]
      simp only [pairB_length, tc_unl]
      have := hb u i hi
      have := hP u
      beta_reduce at this
      omega)
  refine Lib.Loop.cptE (cpt_unpairB2_1 (cpt_unpairB2_1 hI)) (fun u => ?_)
  rw [tc_unl, h2]
  simp only [unpairB_pairB]

theorem tc_red1 {q p : List Bool → ℕ} {v b : List Bool → List ℕ} (hq : NatR q) (hv : VecR v)
    (hb : VecR b) (hp : NatR p) : VecR (fun s => red1 (q s) (v s) (b s) (p s)) :=
  vecR_gen (A := fun s => s) (n := fun s => (v s).length)
    (G := fun i s => (g (b s) (p s) * g (v s) i + (q s - g (v s) (p s)) * g (b s) i) % q s)
    Lib.Machines.cpt_id (natR_vlen hv)
    (natR_mod (natR_add (natR_mul (natR_get (tcv2 hb) (tcn2 hp)) (natR_get (tcv2 hv) tci))
      (natR_mul (natR_sub (tcn2 hq) (natR_get (tcv2 hv) (tcn2 hp))) (natR_get (tcv2 hb) tci)))
      (tcn2 hq))
theorem tc_red1l (q : ℕ) (v b : List ℕ) (p : ℕ) : (red1 q v b p).length = v.length := by
  simp [red1]
theorem tc_red1lt {q : ℕ} (hq : 0 < q) (v b : List ℕ) (p : ℕ) : ∀ a ∈ red1 q v b p, a < q := by
  simp only [red1, List.mem_map]; rintro _ ⟨i, -, rfl⟩; exact Nat.mod_lt _ hq
theorem tc_redAll {q : List Bool → ℕ} {B : List Bool → List (List ℕ)} {pv v : List Bool → List ℕ}
    (hq : NatR q) (hq0 : ∀ s, 0 < q s) (hB : LLR B) (hpv : VecR pv) (hv : VecR v) :
    VecR (fun s => redAll (q s) (B s) (pv s) (v s)) :=
  tc_lp encV decV decV_encV (fun u i w => red1 (q u) w (gg (B u) i) (g (pv u) i))
    (fun u => (B u).length) v
    (tc_red1 (tcn1 hq) (vecR_dec (cpt_unpairB2_1 cpt_unpairB2)) (vecR_row (tcl1 hB) tci2)
      (natR_get (tcv1 hpv) tci2))
    (natR_llen hB) hv (fun u => (v u).length + (v u).sum + (v u).length * q u)
    (natR_add (natR_add (natR_vlen hv) (natR_sum hv)) (natR_mul (natR_vlen hv) hq))
    (fun u i _ => by
      obtain ⟨h1, h2 | h2⟩ := tc_itinv (fun p : ℕ × List ℕ => (p.1 + 1, red1 (q u) p.2 (gg (B u) p.1) (g (pv u) p.1)))
        (fun w => w.length = (v u).length ∧ (w = v u ∨ ∀ a ∈ w, a < q u)) (0, v u) ⟨rfl, Or.inl rfl⟩ (fun y hy => ⟨(tc_red1l _ _ _ _).trans hy.1, Or.inr (tc_red1lt (hq0 u) _ _ _)⟩) i
      · rw [h2, encV_length]; omega
      · have := tc_sumle (fun a ha => (h2 a ha).le); rw [h1] at this; rw [encV_length, h1]; omega)

def tcE (st : ESt) : List Bool := pairB (encLL st.B) (pairB (encV st.pv) (encLL st.sl))
def tcD (t : List Bool) : ESt :=
  ⟨decLL (unpairB t).1, decV (unpairB (unpairB t).2).1, decLL (unpairB (unpairB t).2).2⟩
theorem tcDE (st : ESt) : tcD (tcE st) = st := by
  cases st; simp only [tcD, tcE, unpairB_pairB, decV_encV, decLL_encLL]
theorem tc_ins {q : List Bool → ℕ} {st : List Bool → ESt} {vec : List Bool → List ℕ → List ℕ}
    {τ : List Bool → List ℕ} (hq : NatR q) (hq0 : ∀ s, 0 < q s) (hB : LLR (fun s => (st s).B))
    (hp : VecR (fun s => (st s).pv)) (hl : LLR (fun s => (st s).sl)) (ht : VecR τ)
    (hw : VecR (fun s => vec s (τ s))) :
    Lib.CPTs (fun s => tcE (insertG (q s) (vec s) (st s) (τ s))) := by
  have hr := tc_redAll hq hq0 hB hp hw
  refine Lib.Loop.cptE (cpt_ite_eq (natR_sum hr) (natR_const 0) (cpt_pairB2 hB (cpt_pairB2 hp hl))
    (cpt_pairB2 (llR_append hB (llR_single hr)) (cpt_pairB2 (vecR_append hp
      (vecR_single (natR_firstNZ hr))) (llR_append hl (llR_single ht))))) (fun s => ?_)
  simp only [insertG]; split_ifs <;> rfl
theorem tc_vecLl (q N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (τ : List ℕ) :
    (vecL q N pi pj F τ).length = 2 ^ N * F.length := by simp [vecL]
theorem tc_vecLlt {q : ℕ} (hq : 0 < q) (N : ℕ) (pi pj : List ℕ) (F : List (List ℕ)) (τ : List ℕ) :
    ∀ a ∈ vecL q N pi pj F τ, a < q := by
  simp only [vecL, List.mem_map]; rintro _ ⟨k, -, rfl⟩; exact Nat.mod_lt _ hq
theorem tc_sel {q N : List Bool → ℕ} {pi pj : List Bool → List ℕ} {F C : List Bool → List (List ℕ)}
    (hq : NatR q) (hq0 : ∀ s, 0 < q s) (hN : NatR N) (hP : NatR (fun s => 2 ^ N s))
    (hi : VecR pi) (hj : VecR pj) (hF : LLR F) (hC : LLR C) :
    LLR (fun s => selectE (q s) (N s) (pi s) (pj s) (F s) (C s)) := by
  have hL := tc_lp tcE tcD tcDE
    (fun u i st => insertG (q u) (vecL (q u) (N u) (pi u) (pj u) (F u)) st (gg (C u) i))
    (fun u => (C u).length) (fun _ => ⟨[], [], []⟩)
    (tc_ins (st := fun t => tcD (unpairB (unpairB t).2).2)
      (vec := fun t w => vecL (q (unpairB t).1) (N (unpairB t).1) (pi (unpairB t).1) (pj (unpairB t).1)
        (F (unpairB t).1) w) (τ := fun t => gg (C (unpairB t).1) (unpairB (unpairB t).2).1.length)
      (tcn1 hq) (fun _ => hq0 _)
      (llR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)))
      (vecR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))))
      (llR_dec (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))))
      (vecR_row (tcl1 hC) tci2)
      (vecR_vecL (tcn1 hq) (fun _ => hq0 _) (tcn1 hN) (tcn1 hP) (tcv1 hi) (tcv1 hj) (tcl1 hF)
        (vecR_row (tcl1 hC) tci2)))
    (natR_llen hC) (cpt_const (tcE ⟨[], [], []⟩))
    (fun u => 2 * (2 ^ N u * (F u).length * (2 * (2 ^ N u * (F u).length +
        2 ^ N u * (F u).length * q u) + 1)) + (2 * (2 ^ N u * (F u).length +
        2 ^ N u * (F u).length * (2 ^ N u * (F u).length)) +
        2 ^ N u * (F u).length * (2 * (encLL (C u)).length + 1) + 1) + 1)
    (natR_add (natR_add (natR_mul (natR_const 2) (natR_mul (natR_mul hP (natR_llen hF))
      (natR_add (natR_mul (natR_const 2) (natR_add (natR_mul hP (natR_llen hF))
        (natR_mul (natR_mul hP (natR_llen hF)) hq))) (natR_const 1))))
      (natR_add (natR_add (natR_mul (natR_const 2) (natR_add (natR_mul hP (natR_llen hF))
        (natR_mul (natR_mul hP (natR_llen hF)) (natR_mul hP (natR_llen hF)))))
        (natR_mul (natR_mul hP (natR_llen hF)) (natR_add (natR_mul (natR_const 2)
          (natR_len hC)) (natR_const 1)))) (natR_const 1))) (natR_const 1))
    (fun u i hi => by
      obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := selStep_inv (q u) (hq0 u)
        (vecL (q u) (N u) (pi u) (pj u) (F u)) _ (tc_vecLl _ _ _ _ _) (tc_vecLlt (hq0 u) _ _ _ _)
        (C u) i hi
      show (tcE ((selStep (q u) (vecL (q u) (N u) (pi u) (pj u) (F u)) (C u))^[i]
        (0, ⟨[], [], []⟩)).2).length ≤ _
      generalize ((selStep (q u) (vecL (q u) (N u) (pi u) (pj u) (F u)) (C u))^[i]
        (0, ⟨[], [], []⟩)).2 = st at h1 h2 h3 h4 h5 h6 ⊢
      generalize 2 ^ N u * (F u).length = D at *
      have x1 : (encLL st.B).length ≤ D * (2 * (D + D * q u) + 1) :=
        (tc_elle (M := D + D * q u) (fun b hb => by
          rw [encV_length, (h4 b hb).1]
          have := tc_sumle (fun a ha => ((h4 b hb).2 a ha).le); rw [(h4 b hb).1] at this; omega)).trans
          (Nat.mul_le_mul_right _ h1)
      have x2 : (encV st.pv).length ≤ D + D * D := by
        rw [encV_length]
        have := tc_sumle (fun a ha => (h5 a ha).le)
        have := Nat.mul_le_mul_right D (h2.trans_le h1)
        omega
      have x3 : (encLL st.sl).length ≤ D * (2 * (encLL (C u)).length + 1) :=
        (tc_elle (fun v hv => tc_ellm (h6 v hv))).trans (Nat.mul_le_mul_right _ (h3.trans_le h1))
      simp only [tcE, pairB_length]
      omega)
  exact Lib.Loop.cptE (cpt_unpairB2_1 (cpt_unpairB2_1 hL)) (fun u => by
    simp only [tcE, unpairB_pairB]; rfl)

theorem tc_cand {U : List Bool → List ℕ} {S : List Bool → List (List ℕ)} (hU : VecR U) (hS : LLR S) :
    LLR (fun s => cand (U s) (S s)) :=
  llR_flat (A := fun s => s) (n := fun s => (S s).length)
    (H := fun j s => (List.range (U s).length).map (fun k => gg (S s) j ++ [g (U s) k]))
    Lib.Machines.cpt_id (natR_llen hS)
    (llR_gen (A := fun t => t) (n := fun t => (U (unpairB t).2).length)
      (H := fun k t => gg (S (unpairB t).2) (unpairB t).1.length ++ [g (U (unpairB t).2) k])
      Lib.Machines.cpt_id (natR_vlen (tcv2 hU))
      (vecR_append (vecR_row (tcl2 (tcl2 hS)) tci2) (vecR_single (natR_get (tcv2 (tcv2 hU)) tci))))
theorem tc_hits {pi pj fs : List Bool → List ℕ} {F C : List Bool → List (List ℕ)} (hi : VecR pi)
    (hj : VecR pj) (hF : LLR F) (hf : VecR fs) (hC : LLR C) :
    LLR (fun s => hits (pi s) (pj s) (F s) (fs s) (C s)) :=
  llR_flat (A := fun s => s) (n := fun s => (C s).length)
    (H := fun j s => if hit (pi s) (pj s) (F s) (fs s) (gg (C s) j) = 0 then [] else [gg (C s) j])
    Lib.Machines.cpt_id (natR_llen hC)
    (tcLI (natR_hit (tcv2 hi) (tcv2 hj) (tcl2 hF) (tcv2 hf) (vecR_row (tcl2 hC) tci))
      (natR_const 0) llR_nil (llR_single (vecR_row (tcl2 hC) tci)))
def tcE2 (p : List (List ℕ) × List (List ℕ)) : List Bool := pairB (encLL p.1) (encLL p.2)
def tcD2 (t : List Bool) : List (List ℕ) × List (List ℕ) := (decLL (unpairB t).1, decLL (unpairB t).2)
theorem tcDE2 (p : List (List ℕ) × List (List ℕ)) : tcD2 (tcE2 p) = p := by
  simp [tcD2, tcE2, unpairB_pairB, decLL_encLL]
theorem tc_lvl {q N : List Bool → ℕ} {pi pj U fs : List Bool → List ℕ} {F : List Bool → List (List ℕ)}
    {st : List Bool → List (List ℕ) × List (List ℕ)} (hq : NatR q) (hq0 : ∀ s, 0 < q s) (hN : NatR N)
    (hP : NatR (fun s => 2 ^ N s)) (hi : VecR pi) (hj : VecR pj) (hU : VecR U) (hF : LLR F)
    (hf : VecR fs) (h1 : LLR (fun s => (st s).1)) (h2 : LLR (fun s => (st s).2)) :
    Lib.CPTs (fun s => tcE2 (lvl (q s) (N s) (pi s) (pj s) (U s) (F s) (fs s) (st s))) := by
  have hH := tc_hits hi hj hF hf h1
  refine Lib.Loop.cptE (cpt_ite_eq (natR_llen h2) (natR_const 0) (cpt_ite_eq (natR_llen hH)
    (natR_const 0) (cpt_pairB2 (tc_cand hU (tc_sel hq hq0 hN hP hi hj hF h1)) llR_nil)
    (cpt_pairB2 h1 (llR_single (vecR_row hH (natR_const 0))))) (cpt_pairB2 h1 h2)) (fun s => ?_)
  simp only [lvl]; split_ifs <;> rfl

theorem tc_ggm {C : List (List ℕ)} {j : ℕ} (h : j < C.length) : gg C j ∈ C := by
  simp [gg, List.getElem?_eq_getElem h, List.getElem_mem]
theorem tc_gm {U : List ℕ} {j : ℕ} (h : j < U.length) : g U j ∈ U := by
  simp [g, List.getElem?_eq_getElem h, List.getElem_mem]
theorem tc_hm {pi pj fs : List ℕ} {F C : List (List ℕ)} {x : List ℕ} (h : x ∈ hits pi pj F fs C) :
    x ∈ C := by
  simp only [hits, List.mem_flatMap, List.mem_range] at h
  obtain ⟨j, hj, hx⟩ := h
  split_ifs at hx
  · simp at hx
  · rw [List.mem_singleton] at hx; rw [hx]; exact tc_ggm hj
theorem tc_candl (U : List ℕ) (S : List (List ℕ)) : (cand U S).length = S.length * U.length := by
  simp [cand, List.length_flatMap]
theorem tc_candm {U : List ℕ} {S : List (List ℕ)} {τ : List ℕ} (h : τ ∈ cand U S) :
    ∃ j < S.length, ∃ k < U.length, τ = gg S j ++ [g U k] := by
  simp only [cand, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, k, hk, rfl⟩ := h
  exact ⟨j, hj, k, hk, rfl⟩
theorem tc_lvlinv (q N : ℕ) (hq : 0 < q) (pi pj U : List ℕ) (F : List (List ℕ)) (fs : List ℕ)
    (i : ℕ) :
    ((lvl q N pi pj U F fs)^[i] ([[]], [])).1.length ≤ 1 + 2 ^ N * F.length * U.length ∧
    (∀ τ ∈ ((lvl q N pi pj U F fs)^[i] ([[]], [])).1, τ.length ≤ i ∧ ∀ e ∈ τ, e ∈ U) ∧
    (∀ τ ∈ ((lvl q N pi pj U F fs)^[i] ([[]], [])).2, τ ∈ ((lvl q N pi pj U F fs)^[i] ([[]], [])).1) ∧
    ((lvl q N pi pj U F fs)^[i] ([[]], [])).2.length ≤ 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize (lvl q N pi pj U F fs)^[i] ([[]], []) = st at ih
    obtain ⟨C, d⟩ := st
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [lvl, selectE]
    split_ifs with a b
    · refine ⟨?_, ?_, by simp, by simp⟩
      · rw [tc_candl]
        have := Nat.mul_le_mul_right U.length
          (selectG_length q hq (vecL q N pi pj F) _ (tc_vecLl q N pi pj F) (tc_vecLlt hq N pi pj F) C)
        omega
      · intro τ hτ
        obtain ⟨j, hj, k, hk, rfl⟩ := tc_candm hτ
        obtain ⟨l1, l2⟩ := h2 _ (selectG_sub q (vecL q N pi pj F) C _ (tc_ggm hj))
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun e he => ?_⟩
        rcases List.mem_append.1 he with he | he
        · exact l2 e he
        · rw [List.mem_singleton] at he; rw [he]; exact tc_gm hk
    · refine ⟨h1, fun τ hτ => ⟨(h2 τ hτ).1.trans (Nat.le_succ _), (h2 τ hτ).2⟩, ?_, by simp⟩
      intro τ hτ; rw [List.mem_singleton] at hτ; rw [hτ]; exact tc_hm (tc_ggm (Nat.pos_of_ne_zero b))
    · exact ⟨h1, fun τ hτ => ⟨(h2 τ hτ).1.trans (Nat.le_succ _), (h2 τ hτ).2⟩, h3, h4⟩

def tcF (s : List Bool) : List (List ℕ) := Frows (Pm s) (rowM s)
def tcS (s : List Bool) : List ℕ := Fsig (Pm s) (rowM s) (rowS s)
def tcK (s : List Bool) : ℕ := Nat.log2 (tcF s).length
def tcQ (s : List Bool) : ℕ := primeAbove (nV s + (tcF s).length)
def tcU (s : List Bool) : List ℕ := Uset (pI (nV s)) (pJ (nV s)) (Em s) (Pm s)
def tcL (s : List Bool) : List (List ℕ) × List (List ℕ) → List (List ℕ) × List (List ℕ) :=
  lvl (tcQ s) (2 * tcK s) (pI (nV s)) (pJ (nV s)) (tcU s) (tcF s) (tcS s)
theorem tc_fe (s : List Bool) : found s = ((tcL s)^[tcK s + 1] ([[]], [])).2 := rfl
theorem tc_hF : LLR tcF := llR_Frows vecR_Pm llR_rowM
theorem tc_hS : VecR tcS := vecR_Fsig vecR_Pm llR_rowM vecR_rowS
theorem tc_hK : NatR tcK := natR_log2 (natR_llen tc_hF)
theorem tc_hQ : NatR tcQ := natR_primeAbove (natR_add natR_nV (natR_llen tc_hF))
theorem tc_hQ0 (s : List Bool) : 0 < tcQ s := by unfold tcQ primeAbove; omega
theorem tc_hN : NatR (fun s => 2 * tcK s) := natR_mul (natR_const 2) tc_hK
theorem tc_hU : VecR tcU := vecR_Uset (vecR_pI natR_nV) (vecR_pJ natR_nV) vecR_Em vecR_Pm
theorem tc_hP : NatR (fun s => 2 ^ (2 * tcK s)) := by
  obtain ⟨Pf, hPf⟩ := natR_le_poly (natR_llen tc_hF)
  refine natR_pow2 tc_hN (Pf ^ 2 + 1) (fun s => ?_)
  have h1 := hPf s
  beta_reduce at h1 ⊢
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_one, pow_mul']
  rcases Nat.eq_zero_or_pos (tcF s).length with h | h
  · simp [tcK, h]
  · have h2 := Nat.pow_le_pow_left ((Nat.log2_self_le h.ne').trans h1) 2
    unfold tcK; omega
theorem tc_hL : Lib.CPTs (fun t => tcE2 (tcL (unpairB t).1 (tcD2 (unpairB (unpairB t).2).2))) :=
  tc_lvl (st := fun t => tcD2 (unpairB (unpairB t).2).2) (tcn1 tc_hQ) (fun _ => tc_hQ0 _)
    (tcn1 (a := fun s => 2 * tcK s) tc_hN) (tcn1 (a := fun s => 2 ^ (2 * tcK s)) tc_hP)
    (tcv1 (a := fun s => pI (nV s)) (vecR_pI natR_nV)) (tcv1 (a := fun s => pJ (nV s)) (vecR_pJ natR_nV))
    (tcv1 tc_hU)
    (tcl1 tc_hF) (tcv1 tc_hS)
    (llR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)))
    (llR_dec (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)))
def tcBd (u : List Bool) : ℕ := 3 * ((1 + 2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length) *
  (2 * ((tcK u + 1) * ((tcU u).sum + 1)) + 1)) + 1
theorem tc_hBd : NatR tcBd := natR_add (
  natR_mul (natR_const 3) (natR_mul (natR_add (natR_const 1) (natR_mul (natR_mul tc_hP
    (natR_llen tc_hF)) (natR_vlen tc_hU))) (natR_add (natR_mul (natR_const 2) (natR_mul
    (natR_add tc_hK (natR_const 1)) (natR_add (natR_sum tc_hU) (natR_const 1)))) (natR_const 1)))) (natR_const 1)
theorem tc_fb (u : List Bool) (i : ℕ) (hi : i ≤ tcK u + 1) :
    (tcE2 ((tcL u)^[i] ([[]], []))).length ≤ tcBd u := by
  obtain ⟨h1, h2, h3, h4⟩ := tc_lvlinv (tcQ u) (2 * tcK u) (tc_hQ0 u) (pI (nV u)) (pJ (nV u))
    (tcU u) (tcF u) (tcS u) i
  change _ ≤ 3 * ((1 + 2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length) *
    (2 * ((tcK u + 1) * ((tcU u).sum + 1)) + 1)) + 1
  have hX := Nat.le_add_right 1 (2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length)
  unfold tcL
  generalize (lvl (tcQ u) (2 * tcK u) (pI (nV u)) (pJ (nV u)) (tcU u) (tcF u) (tcS u))^[i]
    ([[]], []) = st at h1 h2 h3 h4 ⊢
  have hM : ∀ τ ∈ st.1, (encV τ).length ≤ (tcK u + 1) * ((tcU u).sum + 1) := fun τ hτ =>
    (tc_evle (fun a ha => List.le_sum_of_mem ((h2 τ hτ).2 a ha))).trans
      (Nat.mul_le_mul_right _ (((h2 τ hτ).1).trans hi))
  have x1 := (tc_elle hM).trans (Nat.mul_le_mul_right _ h1)
  have x2 := (tc_elle (fun τ hτ => hM τ (h3 τ hτ))).trans (Nat.mul_le_mul_right _ h4)
  simp only [tcE2, pairB_length]
  generalize (1 + 2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length) = X at *
  generalize (2 * ((tcK u + 1) * ((tcU u).sum + 1)) + 1) = Y at *
  nlinarith
theorem tc_found : LLR (fun s => found s) := by
  have hL := tc_lp tcE2 tcD2 tcDE2 (fun u _ st => tcL u st) (fun u => tcK u + 1) (fun _ => ([[]], []))
    tc_hL (natR_add tc_hK (natR_const 1)) (cpt_const (tcE2 ([[]], []))) tcBd tc_hBd
    (fun u i hi => by rw [tc_isnd]; exact tc_fb u i hi)
  exact Lib.Loop.cptE (cpt_unpairB2_1 hL) (fun u => by
    beta_reduce; rw [tc_fe, tcE2, unpairB_pairB, tc_isnd])

theorem tc_oA {τ : List Bool → List ℕ} (ht : VecR τ) : VecR (fun s => (List.range (pN s)).map
    (fun k => g (Pm s) k + ((List.range (τ s).length).map (fun i => if g (τ s) i = k then 1 else 0)).sum)) :=
  vecR_gen (A := fun s => s) (n := pN) (G := fun k s => g (Pm s) k +
    ((List.range (τ s).length).map (fun i => if g (τ s) i = k then 1 else 0)).sum)
    Lib.Machines.cpt_id natR_pN
    (natR_add (natR_get (tcv2 vecR_Pm) tci) (natR_sum (vecR_gen (A := fun t => t)
      (n := fun t => (τ (unpairB t).2).length)
      (G := fun i t => if g (τ (unpairB t).2) i = (unpairB t).1.length then 1 else 0)
      Lib.Machines.cpt_id (natR_vlen (tcv2 ht))
      (tcNI (natR_get (tcv2 (tcv2 ht)) tci) tci2 (natR_const 1) (natR_const 0)))))
def tcA (s : List Bool) (τ : List ℕ) : ℕ := posC (tcF s) (tcS s) τ
def tcB (s : List Bool) (τ : List ℕ) : ℕ := negC (tcF s) (tcS s) τ
theorem tc_oc {τ : List Bool → List ℕ} (ht : VecR τ) :
    NatR (fun s => (tcA s (τ s) - tcB s (τ s)) + (tcB s (τ s) - tcA s (τ s))) :=
  natR_add (natR_sub (natR_posC tc_hF tc_hS ht) (natR_negC tc_hF tc_hS ht))
    (natR_sub (natR_negC tc_hF tc_hS ht) (natR_posC tc_hF tc_hS ht))
theorem tc_oB {τ : List Bool → List ℕ} (ht : VecR τ) : VecR (fun s => (List.range ((lenV s).log2 + 1)).map
    (fun i => if ((tcA s (τ s) - tcB s (τ s)) + (tcB s (τ s) - tcA s (τ s))).testBit i then 1 else 0)) :=
  vecR_gen (A := fun s => s) (n := fun s => (lenV s).log2 + 1) (G := fun i s =>
    if ((tcA s (τ s) - tcB s (τ s)) + (tcB s (τ s) - tcA s (τ s))).testBit i then 1 else 0)
    Lib.Machines.cpt_id (natR_add (natR_log2 natR_lenV) (natR_const 1))
    (natR_testBit (tcn2 (a := fun s => (tcA s (τ s) - tcB s (τ s)) + (tcB s (τ s) - tcA s (τ s)))
      (tc_oc ht)) tci)
theorem tc_e2 (c : Prop) [Decidable c] : decide ((if c then 1 else 0) ≠ 0) = decide c := by
  by_cases h : c <;> simp [h]
theorem tc_oe (s : List Bool) (τ : List ℕ) : outBits s τ = [true] ++
    ((List.range (pN s)).map (fun k => g (Pm s) k +
      ((List.range τ.length).map (fun i => if g τ i = k then 1 else 0)).sum)).map (fun a => decide (a ≠ 0)) ++
    [if tcA s τ < tcB s τ then 1 else 0].map (fun a => decide (a ≠ 0)) ++
    ((List.range ((lenV s).log2 + 1)).map (fun i => if ((tcA s τ - tcB s τ) + (tcB s τ - tcA s τ)).testBit i
      then 1 else 0)).map (fun a => decide (a ≠ 0)) := by
  simp only [List.map_map, List.map_cons, List.map_nil, Function.comp_def, tc_e2]
  rfl
theorem tc_out {τ : List Bool → List ℕ} (ht : VecR τ) : Lib.CPTs (fun s => outBits s (τ s)) :=
  Lib.Loop.cptE (cpt_app2 (cpt_app2 (cpt_app2 (cpt_const [true]) (cpt_bitsOf (tc_oA ht)))
    (cpt_bitsOf (vecR_single (tcNL (natR_posC tc_hF tc_hS ht) (natR_negC tc_hF tc_hS ht)
      (natR_const 1) (natR_const 0))))) (cpt_bitsOf (tc_oB ht))) (fun s => (tc_oe s (τ s)).symm)

end Alg

theorem cpt_solveV : Lib.CPTs Alg.solveV :=
  Lib.Loop.cptE (Lib.R.cpt_ite_eq (Lib.R.natR_llen Alg.tc_found) (Lib.R.natR_const 0)
    (Lib.Universal.cpt_const [false]) (Alg.tc_out (Lib.R.vecR_row Alg.tc_found (Lib.R.natR_const 0))))
    (fun _ => rfl)
end PEqualNP.Outside.L_lib_1025
namespace PEqualNP.Outside.L_lib_1025
namespace Alg

theorem mn_rm {α β : Type*} (l : List α) (f : ℕ → β) (h : α → β)
    (H : ∀ r (hr : r < l.length), f r = h l[r]) : (List.range l.length).map f = l.map h := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact H i (by simpa using h1)

theorem mn_rfm {α β : Type*} (l : List α) (f : ℕ → List β) (h : α → List β)
    (H : ∀ r (hr : r < l.length), f r = h l[r]) : (List.range l.length).flatMap f = l.flatMap h := by
  simp only [List.flatMap_def, mn_rm l f h H]

theorem mn_cnt {α : Type*} (l : List α) (p : α → Bool) :
    (l.map (fun t => if p t then 1 else 0)).sum = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [List.filter_cons, h, ih] <;> omega

theorem mn_flt {α β : Type*} (l : List α) (c : α → Prop) [DecidablePred c] (f : α → β) :
    l.flatMap (fun t => if c t then [f t] else []) = (l.filter (fun t => decide (c t))).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : c a <;> simp [List.filter_cons, h, ih]

theorem mn_cntlt (c N : ℕ) : ((List.range N).map (fun i => if i < c then 1 else 0)).sum = min c N := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; split_ifs <;> omega

theorem mn_isPr (c : ℕ) : isPr c ≠ 0 ↔ c.Prime := by
  unfold isPr
  rw [Nat.prime_def_lt']
  split_ifs with h1 h2
  · simp; omega
  · rw [List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map] at h2
    simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
    refine ⟨by omega, fun d hd hdc hdvd => ?_⟩
    have := h2 d (List.mem_range.2 hdc)
    rw [if_neg (by omega), if_pos (Nat.mod_eq_zero_of_dvd hdvd)] at this
    exact one_ne_zero this
  · simp only [ne_eq, not_true_eq_false, false_iff, not_and, not_forall]
    intro _
    rw [List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map] at h2
    push_neg at h2
    obtain ⟨d, hd, hne⟩ := h2
    refine ⟨d, ?_, List.mem_range.1 hd, ?_⟩ <;> split_ifs at hne with h3 h4 <;> simp_all
    · omega
    · exact Nat.dvd_of_mod_eq_zero h4

theorem mn_fnz (v : List ℕ) (h : ∃ j, g v j ≠ 0) : firstNZ v < v.length ∧ g v (firstNZ v) ≠ 0 := by
  have hi0 : g v (Nat.find h) ≠ 0 := Nat.find_spec h
  have hlt : Nat.find h < v.length := by
    by_contra hc
    apply hi0
    simp only [g]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show v.length ≤ Nat.find h by omega)]
    rfl
  have : firstNZ v = Nat.find h := by
    unfold firstNZ
    rw [List.map_congr_left (g := fun i => if i < Nat.find h then 1 else 0), mn_cntlt]
    · omega
    · intro i _
      refine if_congr ?_ rfl rfl
      rw [List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map, Nat.lt_find_iff]
      simp [Nat.lt_succ_iff]
  rw [this]; exact ⟨hlt, hi0⟩

theorem mn_q (B : ℕ) : (primeAbove B).Prime ∧ B < primeAbove B := by
  unfold primeAbove
  have hv : ∀ j, j < B + 2 → g ((List.range (B + 2)).map (fun i => isPr (B + 1 + i))) j = isPr (B + 1 + j) :=
    fun j hj => by simp [g, List.getD_eq_getElem?_getD, List.getElem?_range hj]
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (B + 1) (by omega)
  obtain ⟨hl, hne⟩ := mn_fnz ((List.range (B + 2)).map (fun i => isPr (B + 1 + i)))
    ⟨p - (B + 1), by rw [hv _ (by omega), show B + 1 + (p - (B + 1)) = p by omega]; exact (mn_isPr p).2 hp⟩
  simp only [List.length_map, List.length_range] at hl
  rw [hv _ hl] at hne
  exact ⟨(mn_isPr _).1 hne, by omega⟩

def mn_ix {n : ℕ} (e : Fin n × Fin n) : ℕ := (pairsF n).idxOf e

theorem mn_il {n : ℕ} (A : Finset (Fin n × Fin n)) : (ind A).length = (pairsF n).length := by
  simp [ind]

theorem mn_ixl {n : ℕ} {e : Fin n × Fin n} (h : e.1 < e.2) : mn_ix e < (pairsF n).length :=
  List.idxOf_lt_length_of_mem ((mem_pairsF n e).2 h)

theorem mn_gix {n : ℕ} {e : Fin n × Fin n} (h : e.1 < e.2) : (pairsF n)[mn_ix e]'(mn_ixl h) = e :=
  List.getElem_idxOf _

theorem mn_ixg {n k : ℕ} (hk : k < (pairsF n).length) : mn_ix ((pairsF n)[k]) = k :=
  (pairsF_nodup n).idxOf_getElem k hk

theorem mn_gpi {n : ℕ} {e : Fin n × Fin n} (h : e.1 < e.2) :
    g (pI n) (mn_ix e) = e.1 ∧ g (pJ n) (mn_ix e) = e.2 := by
  have := pairsF_get n _ (mn_ixl h)
  rw [mn_gix h] at this
  exact ⟨this.1.symm, this.2.symm⟩

theorem mn_gind {n : ℕ} (A : Finset (Fin n × Fin n)) (k : ℕ) (hk : k < (pairsF n).length) :
    g (ind A) k = if (pairsF n)[k] ∈ A then 1 else 0 := by
  simp [g, ind, List.getD_eq_getElem?_getD, hk]

theorem mn_gi {n : ℕ} (A : Finset (Fin n × Fin n)) {e : Fin n × Fin n} (h : e.1 < e.2) :
    g (ind A) (mn_ix e) = if e ∈ A then 1 else 0 := by
  rw [mn_gind A _ (mn_ixl h), mn_gix h]

def mn_val {n : ℕ} (E Q : Finset (Fin n × Fin n)) : Prop :=
  Q ⊆ E ∧ ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint ({e.1, e.2} : Finset (Fin n)) {f.1, f.2}
def mn_good {n : ℕ} (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool))
    (Q : Finset (Fin n × Fin n)) : Prop := P ⊆ Q ∧ mn_val E Q ∧ sgn rows Q ≠ 0
def mn_ok {n : ℕ} (E P : Finset (Fin n × Fin n)) (e : Fin n × Fin n) : Prop :=
  e ∈ E ∧ ∀ f ∈ P, Disjoint ({e.1, e.2} : Finset (Fin n)) {f.1, f.2}

theorem mn_nd {n : ℕ} (a : Fin n × Fin n) : ¬ Disjoint ({a.1, a.2} : Finset (Fin n)) {a.1, a.2} :=
  fun h => Finset.insert_ne_empty _ _ (disjoint_self.1 h)

theorem mn_ldsj {n : ℕ} (a b : Fin n × Fin n) :
    List.Disjoint [(a.1 : ℕ), a.2] [(b.1 : ℕ), b.2] ↔ Disjoint ({a.1, a.2} : Finset (Fin n)) {b.1, b.2} := by
  simp only [List.Disjoint, Finset.disjoint_left, List.mem_cons, List.not_mem_nil, Finset.mem_insert,
    Finset.mem_singleton, or_false]
  constructor
  · intro h x hx hy
    exact h (a := (x : ℕ)) (by rcases hx with rfl | rfl <;> simp) (by rcases hy with rfl | rfl <;> simp)
  · intro h x hx hy
    rcases hx with rfl | rfl <;> rcases hy with h' | h'
    all_goals first
      | exact h (Or.inl rfl) (Or.inl (Fin.ext h')) | exact h (Or.inl rfl) (Or.inr (Fin.ext h'))
      | exact h (Or.inr rfl) (Or.inl (Fin.ext h')) | exact h (Or.inr rfl) (Or.inr (Fin.ext h'))

theorem mn_miss {n : ℕ} {P : Finset (Fin n × Fin n)} (hPe : ∀ e ∈ P, e.1 < e.2) (T : Finset (Fin n × Fin n)) :
    missP (ind P) (ind T) = 0 ↔ P ⊆ T := by
  unfold missP
  rw [mn_il, List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map]
  simp only [List.mem_range]
  constructor
  · intro H e he
    have := H _ (mn_ixl (hPe e he))
    rw [mn_gi P (hPe e he), mn_gi T (hPe e he), if_pos he] at this
    by_contra hT
    rw [if_neg hT] at this
    exact one_ne_zero this
  · intro H k hk
    rw [mn_gind P k hk, mn_gind T k hk]
    by_cases h : (pairsF n)[k] ∈ P
    · simp [h, H h]
    · simp [h]

def mn_rP {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (P : Finset (Fin n × Fin n)) :=
  rows.filter (fun t => decide (P ⊆ t.1))
def mn_F0 {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (P : Finset (Fin n × Fin n)) : List (List ℕ) :=
  (mn_rP rows P).map (fun t => ind t.1)
def mn_f0 {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (P : Finset (Fin n × Fin n)) : List ℕ :=
  (mn_rP rows P).map (fun t => if t.2 then 1 else 0)

theorem mn_F {n : ℕ} (P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool))
    (hPe : ∀ e ∈ P, e.1 < e.2) : Frows (ind P) (rows.map (fun t => ind t.1)) = mn_F0 rows P := by
  unfold Frows mn_F0 mn_rP
  rw [List.length_map, mn_rfm rows _ (fun t => if P ⊆ t.1 then [ind t.1] else []) (fun r hr => ?_)]
  · exact mn_flt _ _ _
  · simp [gg, List.getD_eq_getElem?_getD, hr, mn_miss hPe]

theorem mn_Fs {n : ℕ} (P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool))
    (hPe : ∀ e ∈ P, e.1 < e.2) :
    Fsig (ind P) (rows.map (fun t => ind t.1)) (rows.map (fun t => if t.2 then 1 else 0)) = mn_f0 rows P := by
  unfold Fsig mn_f0 mn_rP
  rw [List.length_map, mn_rfm rows _ (fun t => if P ⊆ t.1 then [if t.2 then 1 else 0] else []) (fun r hr => ?_)]
  · exact mn_flt _ _ _
  · simp [gg, g, List.getD_eq_getElem?_getD, hr, mn_miss hPe]

theorem mn_inv {n : ℕ} {P : Finset (Fin n × Fin n)} (hPe : ∀ e ∈ P, e.1 < e.2) (w : Fin n) :
    inVP (pI n) (pJ n) (ind P) (w : ℕ) = 0 ↔ ∀ f ∈ P, w ∉ ({f.1, f.2} : Finset (Fin n)) := by
  unfold inVP
  rw [mn_il, List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map]
  simp only [List.mem_range]
  constructor
  · intro H f hf
    have := H _ (mn_ixl (hPe f hf))
    rw [mn_gi P (hPe f hf), (mn_gpi (hPe f hf)).1, (mn_gpi (hPe f hf)).2, if_pos hf] at this
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> rintro rfl <;> simp at this
  · intro H k hk
    rw [mn_gind P k hk, ← (pairsF_get n k hk).1, ← (pairsF_get n k hk).2]
    by_cases h1 : (pairsF n)[k] ∈ P
    · have := H _ h1
      rw [if_pos h1, one_mul]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
      rw [if_neg (fun h => this.1 (Fin.ext h).symm), if_neg (fun h => this.2 (Fin.ext h).symm)]
    · rw [if_neg h1, zero_mul]

theorem mn_okk {n : ℕ} {E P : Finset (Fin n × Fin n)} (hPe : ∀ e ∈ P, e.1 < e.2) {k : ℕ}
    (hk : k < (pairsF n).length) : mn_ok E P ((pairsF n)[k]) ↔ (pairsF n)[k] ∈ E ∧
      inVP (pI n) (pJ n) (ind P) (g (pI n) k) + inVP (pI n) (pJ n) (ind P) (g (pJ n) k) = 0 := by
  rw [Nat.add_eq_zero_iff, ← (pairsF_get n k hk).1, ← (pairsF_get n k hk).2, mn_inv hPe, mn_inv hPe]
  unfold mn_ok
  simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
  exact ⟨fun ⟨a, b⟩ => ⟨a, fun f hf => (b f hf).1, fun f hf => (b f hf).2⟩,
    fun ⟨a, b, c⟩ => ⟨a, fun f hf => ⟨b f hf, c f hf⟩⟩⟩

theorem mn_U {n : ℕ} {E P : Finset (Fin n × Fin n)} (hPe : ∀ e ∈ P, e.1 < e.2) (k : ℕ) :
    k ∈ Uset (pI n) (pJ n) (ind E) (ind P) ↔ ∃ hk : k < (pairsF n).length, mn_ok E P ((pairsF n)[k]) := by
  unfold Uset
  rw [mn_il]
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, hk⟩
    rw [mn_gind E a ha] at hk
    by_cases h1 : (pairsF n)[a] ∈ E
    · rw [if_neg (by simp [h1])] at hk
      split_ifs at hk with h2
      · obtain rfl := List.mem_singleton.1 hk
        exact ⟨ha, (mn_okk hPe ha).2 ⟨h1, h2⟩⟩
      · simp at hk
    · rw [if_pos (by simp [h1])] at hk; simp at hk
  · rintro ⟨hk, hok⟩
    obtain ⟨h1, h2⟩ := (mn_okk hPe hk).1 hok
    exact ⟨k, hk, by rw [mn_gind E k hk, if_neg (by simp [h1]), if_pos h2]; simp⟩

theorem mn_lab {n : ℕ} {E P : Finset (Fin n × Fin n)} (hPe : ∀ e ∈ P, e.1 < e.2) (τ : List ℕ)
    (hτ : ∀ k ∈ τ, k ∈ Uset (pI n) (pJ n) (ind E) (ind P)) :
    ∃ es : List (Fin n × Fin n), τ = es.map mn_ix ∧ ∀ e ∈ es, mn_ok E P e := by
  induction τ with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons k τ ih =>
    obtain ⟨hk, hok⟩ := (mn_U hPe k).1 (hτ k (by simp))
    obtain ⟨es, rfl, hes⟩ := ih (fun j hj => hτ j (by simp [hj]))
    exact ⟨(pairsF n)[k] :: es, by rw [List.map_cons, mn_ixg hk], List.forall_mem_cons.2 ⟨hok, hes⟩⟩

theorem mn_ixU {n : ℕ} {E P : Finset (Fin n × Fin n)} (hPe : ∀ e ∈ P, e.1 < e.2) {e : Fin n × Fin n}
    (h : e.1 < e.2) (he : mn_ok E P e) : mn_ix e ∈ Uset (pI n) (pJ n) (ind E) (ind P) :=
  (mn_U hPe _).2 ⟨mn_ixl h, by rw [mn_gix h]; exact he⟩

theorem mn_ends (pi pj τ : List ℕ) : ends pi pj τ = τ.flatMap (fun k => [g pi k, g pj k]) := by
  induction τ with
  | nil => rfl
  | cons k τ ih =>
    rw [List.flatMap_cons, ← ih]
    simp only [ends, List.length_cons]
    rw [show 2 * (τ.length + 1) = 2 * τ.length + 1 + 1 by ring, List.range_succ_eq_map,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.succ_eq_add_one, List.cons_append,
      List.nil_append]
    rw [List.cons.injEq, List.cons.injEq]
    refine ⟨by simp [g], by simp [g], List.map_congr_left (fun i _ => ?_)⟩
    rw [show i + 1 + 1 = i + 2 by ring, Nat.add_mod_right, Nat.add_div_right _ (by norm_num)]
    simp [g]

theorem mn_endsE {n : ℕ} (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) :
    ends (pI n) (pJ n) (es.map mn_ix) = es.flatMap (fun e => [(e.1 : ℕ), (e.2 : ℕ)]) := by
  rw [mn_ends, List.flatMap_map]
  simp only [List.flatMap_def]
  congr 1
  exact List.map_congr_left (fun e he => by rw [(mn_gpi (hes e he)).1, (mn_gpi (hes e he)).2])

theorem mn_clash (pi pj τ : List ℕ) : clash pi pj τ = 0 ↔ (ends pi pj τ).Nodup := by
  unfold clash
  generalize ends pi pj τ = l
  rw [List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map, List.nodup_iff_pairwise_ne,
    List.pairwise_iff_getElem]
  simp only [List.mem_range, List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map]
  constructor
  · intro H i j hi hj hij heq
    have := H i hi j hj
    simp [hij, g, List.getD_eq_getElem?_getD, hi, hj, heq] at this
  · intro H i hi j hj
    split_ifs with h1 h2
    · exact absurd (by simpa [g, List.getD_eq_getElem?_getD, hi, hj] using h2) (H i j hi hj h1)
    · rfl
    · rfl

theorem mn_chi {n : ℕ} (F : List (List ℕ)) (r : ℕ) (T : Finset (Fin n × Fin n)) (hT : gg F r = ind T)
    (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) :
    chi F (es.map mn_ix) r = if es.toFinset ⊆ T then 1 else 0 := by
  unfold chi
  rw [hT, mn_rm (es.map mn_ix) _ (fun k => 1 - g (ind T) k) (fun i hi => by
    simp only [List.length_map] at hi; simp [g, List.getD_eq_getElem?_getD, hi]), List.map_map]
  refine if_congr ?_ rfl rfl
  rw [List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map]
  simp only [Function.comp_apply, Finset.subset_iff, List.mem_toFinset]
  refine forall₂_congr (fun e he => ?_)
  rw [mn_gi T (hes e he)]
  split_ifs with h <;> simp [h]

theorem mn_pos {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (P : Finset (Fin n × Fin n))
    (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) :
    posC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) =
      (rows.filter (fun t => t.2 && decide (P ∪ es.toFinset ⊆ t.1))).length := by
  unfold posC
  rw [show (mn_F0 rows P).length = (mn_rP rows P).length by simp [mn_F0],
    mn_rm (mn_rP rows P) _ (fun t => if (t.2 && decide (es.toFinset ⊆ t.1)) = true then 1 else 0)
      (fun r hr => ?_), mn_cnt]
  · unfold mn_rP
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    rintro ⟨T, _ | _⟩ _ <;> simp [Finset.union_subset_iff] <;> exact Bool.and_comm _ _
  · rw [mn_chi (mn_F0 rows P) r (mn_rP rows P)[r].1 (by simp [mn_F0, gg, List.getD_eq_getElem?_getD, hr]) es hes]
    simp only [mn_f0, g, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hr,
      Option.map_some, Option.getD_some]
    cases (mn_rP rows P)[r].2 <;> simp

theorem mn_neg {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (P : Finset (Fin n × Fin n))
    (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) :
    negC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) =
      (rows.filter (fun t => !t.2 && decide (P ∪ es.toFinset ⊆ t.1))).length := by
  unfold negC
  rw [show (mn_F0 rows P).length = (mn_rP rows P).length by simp [mn_F0],
    mn_rm (mn_rP rows P) _ (fun t => if (!t.2 && decide (es.toFinset ⊆ t.1)) = true then 1 else 0)
      (fun r hr => ?_), mn_cnt]
  · unfold mn_rP
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    rintro ⟨T, _ | _⟩ _ <;> simp [Finset.union_subset_iff] <;> exact Bool.and_comm _ _
  · rw [mn_chi (mn_F0 rows P) r (mn_rP rows P)[r].1 (by simp [mn_F0, gg, List.getD_eq_getElem?_getD, hr]) es hes]
    simp only [mn_f0, g, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hr,
      Option.map_some, Option.getD_some]
    cases (mn_rP rows P)[r].2 <;> simp

theorem mn_hitE {n : ℕ} (rows : List (Finset (Fin n × Fin n) × Bool)) (P : Finset (Fin n × Fin n))
    (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) :
    hit (pI n) (pJ n) (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) ≠ 0 ↔
      (es.flatMap (fun e => [(e.1 : ℕ), (e.2 : ℕ)])).Nodup ∧ sgn rows (P ∪ es.toFinset) ≠ 0 := by
  have : hit (pI n) (pJ n) (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) ≠ 0 ↔
      clash (pI n) (pJ n) (es.map mn_ix) = 0 ∧
        posC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) ≠ negC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) := by
    unfold hit; split_ifs <;> simp [*]
  rw [this, mn_clash, mn_endsE es hes, mn_pos rows P es hes, mn_neg rows P es hes]
  unfold sgn
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem mn_mb {n : ℕ} (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) (k : ℕ)
    (hk : k < (pairsF n).length) (A : Finset (Fin n × Fin n)) :
    decide (g (ind A) k + ((List.range (es.map mn_ix).length).map
      (fun i => if g (es.map mn_ix) i = k then 1 else 0)).sum ≠ 0) = decide ((pairsF n)[k] ∈ A ∪ es.toFinset) := by
  rw [mn_gind A k hk, mn_rm (es.map mn_ix) _ (fun j => if j = k then 1 else 0) (fun i hi => by
    simp only [List.length_map] at hi; simp [g, List.getD_eq_getElem?_getD, hi]), List.map_map]
  have hB : (pairsF n)[k] ∈ es ↔ (es.map ((fun j => if j = k then 1 else 0) ∘ mn_ix)).sum ≠ 0 := by
    rw [ne_eq, List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map]
    simp only [Function.comp_apply, ite_eq_right_iff, one_ne_zero, imp_false, not_forall, not_not]
    constructor
    · intro h; exact ⟨_, h, mn_ixg hk⟩
    · rintro ⟨e, he, hek⟩; subst hek; rw [mn_gix (hes e he)]; exact he
  apply decide_eq_decide.2
  rw [Finset.mem_union, List.mem_toFinset, hB]
  generalize (es.map ((fun j => if j = k then 1 else 0) ∘ mn_ix)).sum = S
  split_ifs with h1 <;> simp [h1] <;> omega

theorem mn_out {n : ℕ} (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool))
    (hPe : ∀ e ∈ P, e.1 < e.2) (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, e.1 < e.2) :
    outBits (inputF n E P rows) (es.map mn_ix) = [true] ++ maskF (P ∪ es.toFinset) ++
      [decide (sgn rows (P ∪ es.toFinset) < 0)] ++
        (List.range (rows.length.log2 + 1)).map (fun i => (sgn rows (P ∪ es.toFinset)).natAbs.testBit i) := by
  simp only [outBits, Pm_inputF, rowM_inputF, rowS_inputF, pN_inputF, lenV_inputF, mn_F P rows hPe,
    mn_Fs P rows hPe, mn_pos rows P es hes, mn_neg rows P es hes, sgn]
  rw [mn_rm (pairsF n) _ (fun e => decide (e ∈ P ∪ es.toFinset)) (fun k hk => mn_mb es hes k hk P)]
  have key : ∀ a b : ℕ, decide (a < b) = decide ((a : ℤ) - b < 0) ∧ (a - b) + (b - a) = ((a : ℤ) - b).natAbs :=
    fun a b => ⟨decide_eq_decide.2 (by omega), by omega⟩
  rw [(key _ _).1, (key _ _).2]; rfl

theorem mn_gd {n : ℕ} {E P : Finset (Fin n × Fin n)} {rows : List (Finset (Fin n × Fin n) × Bool)}
    (hP : mn_val E P) (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, mn_ok E P e)
    (hnd : (es.flatMap (fun e => [(e.1 : ℕ), (e.2 : ℕ)])).Nodup) (hs : sgn rows (P ∪ es.toFinset) ≠ 0) :
    mn_good E P rows (P ∪ es.toFinset) ∧ (P ∪ es.toFinset) \ P = es.toFinset ∧
      es.toFinset.card = es.length := by
  rw [List.nodup_flatMap] at hnd
  have hpw : ∀ a ∈ es, ∀ b ∈ es, a ≠ b → Disjoint ({a.1, a.2} : Finset (Fin n)) {b.1, b.2} :=
    fun a ha b hb => List.Pairwise.forall_of_forall_of_flip
      (R := fun a b => a ≠ b → Disjoint ({a.1, a.2} : Finset (Fin n)) {b.1, b.2}) (fun x _ h => absurd rfl h)
      (hnd.2.imp (fun {a b} h (_ : a ≠ b) => (mn_ldsj a b).1 h)) (hnd.2.imp (fun {a b} h (_ : b ≠ a) => ((mn_ldsj a b).1 h).symm)) ha hb
  have hnd' : es.Nodup := hnd.2.imp (fun {a b} h hab => by subst hab; exact mn_nd a ((mn_ldsj a a).1 h))
  have hPR : Disjoint P es.toFinset := Finset.disjoint_left.2 (fun e heP heR =>
    mn_nd e ((hes e (List.mem_toFinset.1 heR)).2 e heP))
  refine ⟨⟨Finset.subset_union_left, ⟨Finset.union_subset hP.1
    (fun e he => (hes e (List.mem_toFinset.1 he)).1), ?_⟩, hs⟩,
    Finset.union_sdiff_cancel_left hPR, List.toFinset_card_of_nodup hnd'⟩
  intro e he f hf hef
  simp only [Finset.mem_union, List.mem_toFinset] at he hf
  rcases he with he | he <;> rcases hf with hf | hf
  · exact hP.2 e he f hf hef
  · exact ((hes f hf).2 e he).symm
  · exact (hes e he).2 f hf
  · exact hpw e he f hf hef

theorem mn_fg {n : ℕ} {E P : Finset (Fin n × Fin n)} {rows : List (Finset (Fin n × Fin n) × Bool)}
    (hE : ∀ e ∈ E, e.1 < e.2) (Q : Finset (Fin n × Fin n)) (hQ : mn_good E P rows Q) :
    (∀ e ∈ (Q \ P).toList, mn_ok E P e) ∧
      ((Q \ P).toList.flatMap (fun e => [(e.1 : ℕ), (e.2 : ℕ)])).Nodup ∧
      P ∪ (Q \ P).toList.toFinset = Q ∧ (Q \ P).toList.length = (Q \ P).card := by
  obtain ⟨hPQ, ⟨hQE, hQm⟩, -⟩ := hQ
  refine ⟨fun e he => ?_, List.nodup_flatMap.2 ⟨fun e he => ?_,
    (Finset.nodup_toList _).pairwise_of_forall_ne (fun a ha b hb hab => ?_)⟩,
    by rw [Finset.toList_toFinset, Finset.union_sdiff_of_subset hPQ], Finset.length_toList _⟩
  · rw [Finset.mem_toList, Finset.mem_sdiff] at he
    exact ⟨hQE he.1, fun f hf => hQm e he.1 f (hPQ hf) (fun h => he.2 (h ▸ hf))⟩
  · rw [Finset.mem_toList, Finset.mem_sdiff] at he
    have := Fin.lt_def.1 (hE e (hQE he.1))
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_true]
    omega
  · rw [Finset.mem_toList, Finset.mem_sdiff] at ha hb
    exact (mn_ldsj a b).2 (hQm a ha.1 b hb.1 hab)

theorem mn_exmin {α : Type*} (p : Finset α → Prop) (h : ∃ Q, p Q) :
    ∃ Q, p Q ∧ ∀ S, p S → Q.card ≤ S.card := by
  classical
  have h' : ∃ k, ∃ Q, p Q ∧ Q.card = k := ⟨_, h.choose, h.choose_spec, rfl⟩
  obtain ⟨Q, hQ, hc⟩ := Nat.find_spec h'
  exact ⟨Q, hQ, fun S hS => hc ▸ Nat.find_min' h' ⟨S, hS, rfl⟩⟩

theorem mn_min {n : ℕ} {E P : Finset (Fin n × Fin n)} {rows : List (Finset (Fin n × Fin n) × Bool)}
    (Q : Finset (Fin n × Fin n)) (hQ : mn_good E P rows Q)
    (hmin : ∀ S, mn_good E P rows S → Q.card ≤ S.card) :
    2 ^ (Q \ P).card * (sgn rows Q).natAbs ≤ (mn_rP rows P).length := by
  have := mobius_bound rows P (Q \ P) (fun S hS => by
    by_contra hne
    have hSQ : P ∪ S ⊆ Q := Finset.union_subset hQ.1 (hS.subset.trans Finset.sdiff_subset)
    have := hmin (P ∪ S) ⟨Finset.subset_union_left, ⟨hSQ.trans hQ.2.1.1,
      fun e he f hf hef => hQ.2.1.2 e (hSQ he) f (hSQ hf) hef⟩, hne⟩
    have h1 := Finset.card_union_le P S
    have h2 := Finset.card_lt_card hS
    have h3 := Finset.card_sdiff_add_card_eq_card hQ.1
    omega)
  rwa [Finset.union_sdiff_of_subset hQ.1] at this

theorem mn_main (n : ℕ) (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool))
    (hE : ∀ e ∈ E, e.1 < e.2) (hP : mn_val E P) :
    ((mn_rP rows P).length = 0 → solveV (inputF n E P rows) = [false]) ∧
    (solveV (inputF n E P rows) = [false] ↔ ¬ ∃ Q, mn_good E P rows Q) ∧
    ((∃ Q, mn_good E P rows Q) → ∃ Q, mn_good E P rows Q ∧ (∀ S, mn_good E P rows S → Q.card ≤ S.card) ∧
      2 ^ ((Q \ P).card) * (sgn rows Q).natAbs ≤ (mn_rP rows P).length ∧ solveV (inputF n E P rows) =
        [true] ++ maskF Q ++ [decide (sgn rows Q < 0)] ++
          (List.range (rows.length.log2 + 1)).map (fun i => (sgn rows Q).natAbs.testBit i)) := by
  have hPe : ∀ e ∈ P, e.1 < e.2 := fun e he => hE e (hP.1 he)
  have hq := mn_q (n + (mn_rP rows P).length)
  haveI : Fact (primeAbove (n + (mn_rP rows P).length)).Prime := ⟨hq.1⟩
  have hfd : found (inputF n E P rows) = ((lvl (primeAbove (n + (mn_rP rows P).length))
      (2 * Nat.log2 (mn_rP rows P).length) (pI n) (pJ n) (Uset (pI n) (pJ n) (ind E) (ind P))
      (mn_F0 rows P) (mn_f0 rows P))^[Nat.log2 (mn_rP rows P).length + 1] ([[]], [])).2 := by
    simp only [found, nV_inputF, Pm_inputF, Em_inputF, rowM_inputF, rowS_inputF, mn_F P rows hPe,
      mn_Fs P rows hPe]
    simp only [mn_F0, List.length_map]
  have hsv : solveV (inputF n E P rows) = if (found (inputF n E P rows)).length = 0 then [false]
      else outBits (inputF n E P rows) (gg (found (inputF n E P rows)) 0) := rfl
  have hgh : ∀ S, mn_good E P rows S →
      (∀ k ∈ (S \ P).toList.map mn_ix, k ∈ Uset (pI n) (pJ n) (ind E) (ind P)) ∧
      ((S \ P).toList.map mn_ix).length = (S \ P).card ∧
      hit (pI n) (pJ n) (mn_F0 rows P) (mn_f0 rows P) ((S \ P).toList.map mn_ix) ≠ 0 := by
    intro S hS
    obtain ⟨h1, h2, h3, h4⟩ := mn_fg hE S hS
    refine ⟨fun k hk => ?_, by rw [List.length_map, h4], (mn_hitE rows P _ (fun e he => hE e (h1 e he).1)).2
      ⟨h2, by rw [h3]; exact hS.2.2⟩⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
    exact mn_ixU hPe (hE e (h1 e he).1) (h1 e he)
  rcases found_spec (primeAbove (n + (mn_rP rows P).length)) (2 * Nat.log2 (mn_rP rows P).length)
      (Nat.log2 (mn_rP rows P).length) rfl (pI n) (pJ n) (Uset (pI n) (pJ n) (ind E) (ind P))
      (mn_F0 rows P) (mn_f0 rows P)
      (fun τ hτ a ha => by
        obtain ⟨es, rfl, hes⟩ := mn_lab hPe τ hτ
        rw [mn_endsE es (fun e he => hE e (hes e he).1), List.mem_flatMap] at ha
        obtain ⟨e, -, he⟩ := ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> omega)
      (by simp only [mn_F0, List.length_map]; omega)
      (by simp only [mn_f0, List.mem_map]; rintro a ⟨t, -, rfl⟩; split_ifs <;> omega)
      (by simp [mn_F0, mn_f0]) with ⟨h0, hno⟩ | ⟨τ, h1, hU, hK, hhit, hmin⟩
  · have hs : solveV (inputF n E P rows) = [false] := by rw [hsv, hfd, h0]; rfl
    have hnone : ¬ ∃ Q, mn_good E P rows Q := by
      intro hex
      obtain ⟨Q, hQ, hQm⟩ := mn_exmin _ hex
      have hb := mn_min Q hQ hQm
      have hs0 : (sgn rows Q).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hQ.2.2
      have hm0 : (mn_rP rows P).length ≠ 0 := by
        intro h; rw [h] at hb; exact hs0 (by simpa using hb)
      have hK : (Q \ P).card ≤ Nat.log2 (mn_rP rows P).length :=
        (Nat.le_log2 hm0).2 (le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hs0)) hb)
      obtain ⟨g1, g2, g3⟩ := hgh Q hQ
      exact g3 (hno _ g1 (by rw [g2]; exact hK))
    exact ⟨fun _ => hs, iff_of_true hs hnone, fun h => absurd h hnone⟩
  · obtain ⟨es, rfl, hes⟩ := mn_lab hPe τ hU
    have hes' : ∀ e ∈ es, e.1 < e.2 := fun e he => hE e (hes e he).1
    obtain ⟨hnd, hsg⟩ := (mn_hitE rows P es hes').1 hhit
    obtain ⟨hgood, hdiff, hcard⟩ := mn_gd hP es hes hnd hsg
    have hQm : ∀ S, mn_good E P rows S → (P ∪ es.toFinset).card ≤ S.card := by
      intro S hS
      obtain ⟨g1, g2, g3⟩ := hgh S hS
      have := not_lt.1 (fun h => g3 (hmin _ g1 h))
      rw [g2, List.length_map] at this
      have c1 := Finset.card_sdiff_add_card_eq_card hS.1
      have c2 := Finset.card_sdiff_add_card_eq_card hgood.1
      rw [hdiff, hcard] at c2
      omega
    have hb := mn_min _ hgood hQm
    have hs : solveV (inputF n E P rows) = [true] ++ maskF (P ∪ es.toFinset) ++
        [decide (sgn rows (P ∪ es.toFinset) < 0)] ++ (List.range (rows.length.log2 + 1)).map
          (fun i => (sgn rows (P ∪ es.toFinset)).natAbs.testBit i) := by
      rw [hsv, hfd, h1]; exact mn_out E P rows hPe es hes'
    refine ⟨fun h => ?_, ⟨fun h => ?_, fun h => absurd ⟨_, hgood⟩ h⟩, fun _ => ⟨_, hgood, hQm, hb, hs⟩⟩
    · rw [h] at hb
      exact absurd (Int.natAbs_eq_zero.1 (by simpa using hb)) hgood.2.2
    · rw [hs] at h; simp at h

theorem solveV_spec : ∀ (n : Nat) (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool)),
  (∀ e ∈ E, e.1 < e.2) →
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let valid := fun Q : Finset (Fin n × Fin n) => Q ⊆ E ∧
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)
  valid P →
  let signed := fun Q : Finset (Fin n × Fin n) =>
    ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : Int) -
      ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : Int)
  let mask := fun A : Finset (Fin n × Fin n) => ((fun n : Nat => (List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))) n).map (fun e => decide (e ∈ A))
  let good := fun Q => P ⊆ Q ∧ valid Q ∧ signed Q ≠ 0
  let m := (rows.filter (fun t => decide (P ⊆ t.1))).length
  let x := (fun z : Nat => List.replicate z true ++ [false]) n ++ mask E ++ mask P ++
    (fun z : Nat => List.replicate z true ++ [false]) rows.length ++ rows.flatMap (fun t => t.2 :: mask t.1)
  (m = 0 → solveV x = [false]) ∧ (solveV x = [false] ↔ ¬ ∃ Q, good Q) ∧
  ((∃ Q, good Q) → ∃ Q, good Q ∧ (∀ S, good S → Q.card ≤ S.card) ∧
    2^((Q \ P).card)*(signed Q).natAbs ≤ m ∧ solveV x =
      [true] ++ mask Q ++ [decide (signed Q < 0)] ++
        (List.range (rows.length.log2+1)).map (fun i => (signed Q).natAbs.testBit i)) := by
  intro n E P rows hE
  exact mn_main n E P rows hE
end Alg
end PEqualNP.Outside.L_lib_1025
theorem PEqualNP.Outside.L_lib_1025 : (let header := fun z : Nat => List.replicate z true ++ [false]
let pairs := fun n : Nat => (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)
∃ solve : List Bool → List Bool, fast solve ∧
∀ (n : Nat) (E P : Finset (Fin n × Fin n)) (rows : List (Finset (Fin n × Fin n) × Bool)),
  (∀ e ∈ E, e.1 < e.2) →
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let valid := fun Q : Finset (Fin n × Fin n) => Q ⊆ E ∧
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)
  valid P →
  let signed := fun Q : Finset (Fin n × Fin n) =>
    ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : Int) -
      ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : Int)
  let mask := fun A : Finset (Fin n × Fin n) => (pairs n).map (fun e => decide (e ∈ A))
  let good := fun Q => P ⊆ Q ∧ valid Q ∧ signed Q ≠ 0
  let m := (rows.filter (fun t => decide (P ⊆ t.1))).length
  let x := header n ++ mask E ++ mask P ++ header rows.length ++ rows.flatMap (fun t => t.2 :: mask t.1)
  (m = 0 → solve x = [false]) ∧ (solve x = [false] ↔ ¬ ∃ Q, good Q) ∧
  ((∃ Q, good Q) → ∃ Q, good Q ∧ (∀ S, good S → Q.card ≤ S.card) ∧
    2^((Q \ P).card)*(signed Q).natAbs ≤ m ∧ solve x =
      [true] ++ mask Q ++ [decide (signed Q < 0)] ++
        (List.range (rows.length.log2+1)).map (fun i => (signed Q).natAbs.testBit i))) := by
  intro header pairs fast
  refine ⟨PEqualNP.Outside.L_lib_1025.Alg.solveV,
    PEqualNP.Outside.L_lib_1025.Lib.Fast.cpt_to_fast PEqualNP.Outside.L_lib_1025.cpt_solveV, ?_⟩
  exact PEqualNP.Outside.L_lib_1025.Alg.solveV_spec
