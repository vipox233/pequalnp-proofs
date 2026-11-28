import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_398
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
abbrev F2 := ZMod 2
def header (n : ℕ) : List Bool := List.replicate n true ++ [false]
def pack (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool) : List Bool :=
  header n ++ header m ++ header k ++ header d ++
    (List.finRange m).flatMap (fun e => (List.finRange n).flatMap
      (fun i => (List.finRange n).map (fun j => A e i j)))
def quad (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x : Fin n → F2) (e : Fin m) : F2 :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => if A e i j then x i * x j else 0))
def feasible (n m k d : ℕ) (Q : (Fin n → F2) → Fin m → F2) : Prop :=
  let X := Fin n → F2
  let Y := Fin m → F2
  let tree := fun (target : (X × Y) → Y) (allowed : Set (Set Y)) (K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (query : List Bool → (X × Y) →ₗ[F2] F2)
      (bias : List Bool → F2) (out : List Bool → Set Y),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : X × Y, (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → target z ∈ out p
  let allowed := {L : Set Y | ∃ (R : Submodule F2 Y) (c : Y),
      Module.finrank F2 R ≤ k ∧ L = {w : Y | w - c ∈ R}}
  tree (fun z => z.2 + Q z.1) allowed (2 ^ d)
lemma header_append_inj : ∀ {n₁ n₂ : ℕ} {r₁ r₂ : List Bool},
    header n₁ ++ r₁ = header n₂ ++ r₂ → n₁ = n₂ ∧ r₁ = r₂ := by
  intro n₁
  induction n₁ with
  | zero =>
    intro n₂ r₁ r₂ h
    cases n₂ with
    | zero => simpa [header] using h
    | succ n₂ => simp [header, List.replicate_succ] at h
  | succ n₁ ih =>
    intro n₂ r₁ r₂ h
    cases n₂ with
    | zero => simp [header, List.replicate_succ] at h
    | succ n₂ =>
      simp only [header, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hn, hr⟩ := ih h
      exact ⟨congrArg Nat.succ hn, hr⟩
lemma finRange_flatMap_length {β : Type*} (n : ℕ) (f : Fin n → List β) (L : ℕ)
    (hf : ∀ i, (f i).length = L) : ((List.finRange n).flatMap f).length = n * L := by
  rw [List.length_flatMap]
  have : ((List.finRange n).map (fun i => (f i).length)) = List.replicate n L := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [hf]
  rw [this, List.sum_replicate, smul_eq_mul]
lemma finRange_flatMap_inj {n : ℕ} {L : ℕ} {f g : Fin n → List Bool}
    (hf : ∀ i, (f i).length = L) (hg : ∀ i, (g i).length = L)
    (heq : (List.finRange n).flatMap f = (List.finRange n).flatMap g) : f = g := by
  have hgen : ∀ (l : List (Fin n)), (∀ i ∈ l, (f i).length = L) → (∀ i ∈ l, (g i).length = L) →
      l.flatMap f = l.flatMap g → ∀ i ∈ l, f i = g i := by
    intro l
    induction l with
    | nil => intro _ _ _ i hi; simp at hi
    | cons a l ih =>
      intro hfl hgl he i hi
      simp only [List.flatMap_cons] at he
      have hlen : (f a).length = (g a).length := by
        rw [hfl a (by simp), hgl a (by simp)]
      have ⟨hfa, htl⟩ := List.append_inj he hlen
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact hfa
      · exact ih (fun x hx => hfl x (by simp [hx])) (fun x hx => hgl x (by simp [hx])) htl i hi'
  funext i
  exact hgen (List.finRange n) (fun x _ => hf x) (fun x _ => hg x) heq i (List.mem_finRange i)
lemma pack_inj {n₁ m₁ k₁ d₁ n₂ m₂ k₂ d₂ : ℕ}
    {A₁ : Fin m₁ → Fin n₁ → Fin n₁ → Bool} {A₂ : Fin m₂ → Fin n₂ → Fin n₂ → Bool}
    (h : pack n₁ m₁ k₁ d₁ A₁ = pack n₂ m₂ k₂ d₂ A₂) :
    n₁ = n₂ ∧ m₁ = m₂ ∧ k₁ = k₂ ∧ d₁ = d₂ ∧ HEq A₁ A₂ := by
  unfold pack at h
  simp only [List.append_assoc] at h
  obtain ⟨hn, h1⟩ := header_append_inj h
  subst hn
  obtain ⟨hm, h2⟩ := header_append_inj h1
  subst hm
  obtain ⟨hk, h3⟩ := header_append_inj h2
  subst hk
  obtain ⟨hd, h4⟩ := header_append_inj h3
  subst hd
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  apply heq_of_eq
  have h1' := finRange_flatMap_inj (L := n₁ * n₁)
    (fun e => finRange_flatMap_length n₁ _ n₁ (fun i => by simp))
    (fun e => finRange_flatMap_length n₁ _ n₁ (fun i => by simp)) h4
  funext e
  have h2' := finRange_flatMap_inj (L := n₁)
    (fun i => by simp) (fun i => by simp) (congrFun h1' e)
  funext i
  have h3' := congrFun h2' i
  funext j
  have hget := congrArg (fun l => l[j.val]?) h3'
  simpa using hget
lemma zmod2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl
lemma zmod2_add_self (a : F2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide
lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
lemma zmod2_eq_of_decide_eq {a b c : F2} (h : decide (a = c) = decide (b = c)) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;> simp_all
def polar (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x y : Fin n → F2) (e : Fin m) : F2 :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    if xor (A e i j) (A e j i) then x i * y j else 0))
lemma polar_eq_sum (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x y : Fin n → F2) (e : Fin m) :
    polar n m A x y e =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (if A e i j then x i * y j else 0) + (if A e j i then x i * y j else 0))) := by
  unfold polar
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  cases A e i j <;> cases A e j i <;> simp [zmod2_add_self]
lemma quad_add (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x y : Fin n → F2) (e : Fin m) :
    quad n m A (x + y) e = quad n m A x e + quad n m A y e + polar n m A x y e := by
  rw [polar_eq_sum]
  unfold quad
  have hswap :
      Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
        if A e j i then x i * y j else 0)) =
      Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
        if A e i j then y i * x j else 0)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring
  simp only [Finset.sum_add_distrib]
  rw [hswap]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.add_apply]
  split_ifs <;> ring
lemma polar_eq_quad_diff (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x y : Fin n → F2) :
    polar n m A x y = quad n m A (x + y) + quad n m A x + quad n m A y := by
  funext e
  simp only [Pi.add_apply, quad_add]
  have h1 : quad n m A x e + quad n m A x e = 0 := zmod2_add_self _
  have h2 : quad n m A y e + quad n m A y e = 0 := zmod2_add_self _
  calc polar n m A x y e
      = (quad n m A x e + quad n m A x e) + (quad n m A y e + quad n m A y e) +
          polar n m A x y e := by rw [h1, h2]; ring
    _ = quad n m A x e + quad n m A y e + polar n m A x y e + quad n m A x e +
          quad n m A y e := by ring
lemma polar_add_left (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x₁ x₂ y : Fin n → F2) :
    polar n m A (x₁ + x₂) y = polar n m A x₁ y + polar n m A x₂ y := by
  funext e
  simp only [Pi.add_apply, polar, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> ring
lemma polar_add_right (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x y₁ y₂ : Fin n → F2) :
    polar n m A x (y₁ + y₂) = polar n m A x y₁ + polar n m A x y₂ := by
  funext e
  simp only [Pi.add_apply, polar, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> ring
lemma polar_smul_left (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (c : F2) (x y : Fin n → F2) :
    polar n m A (c • x) y = c • polar n m A x y := by
  rcases zmod2_cases c with rfl | rfl <;> funext e <;> simp [polar]
lemma polar_smul_right (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (c : F2) (x y : Fin n → F2) :
    polar n m A x (c • y) = c • polar n m A x y := by
  rcases zmod2_cases c with rfl | rfl <;> funext e <;> simp [polar]
lemma polar_zero_left (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (y : Fin n → F2) :
    polar n m A 0 y = 0 := by
  funext e; simp [polar]
lemma polar_zero_right (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x : Fin n → F2) :
    polar n m A x 0 = 0 := by
  funext e; simp [polar]
def SubspaceFeasible (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool) : Prop :=
  ∃ (UX : Submodule F2 (Fin n → F2)) (R : Submodule F2 (Fin m → F2)),
    Module.finrank F2 R ≤ k ∧
    (n - Module.finrank F2 UX) + (m - Module.finrank F2 R) ≤ d ∧
    ∀ u ∈ UX, ∀ v ∈ UX, polar n m A u v ∈ R
lemma card_submodule_eq_pow {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    (U : Submodule F2 V) [Fintype U] :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  have h := Module.card_eq_pow_finrank (K := F2) (V := U)
  simpa [ZMod.card] using h
lemma exists_functionals_ker {V : Type*} [AddCommGroup V] [Module F2 V] [Module.Finite F2 V]
    (U : Submodule F2 V) :
    ∃ (ℓ : Fin (Module.finrank F2 V - Module.finrank F2 U) → (V →ₗ[F2] F2)),
      ∀ v : V, (∀ i, ℓ i v = 0) ↔ v ∈ U := by
  have hq : Module.finrank F2 (V ⧸ U) = Module.finrank F2 V - Module.finrank F2 U := by
    have h := Submodule.finrank_quotient_add_finrank U
    omega
  let b := Module.finBasis F2 (V ⧸ U)
  let e : Fin (Module.finrank F2 V - Module.finrank F2 U) ≃ Fin (Module.finrank F2 (V ⧸ U)) :=
    finCongr hq.symm
  refine ⟨fun i => (b.coord (e i)).comp U.mkQ, fun v => ?_⟩
  constructor
  · intro hv
    have hzero : U.mkQ v = 0 := by
      apply b.ext_elem
      intro j
      have h1 := hv (e.symm j)
      simp only [LinearMap.comp_apply, Module.Basis.coord_apply, Equiv.apply_symm_apply] at h1
      simpa [map_zero] using h1
    exact (Submodule.Quotient.mk_eq_zero U).mp hzero
  · intro hv i
    have hzero : U.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hv
    simp [hzero]
lemma follow_leaf {n m : ℕ} (N J : Finset (List Bool))
    (query : List Bool → ((Fin n → F2) × (Fin m → F2)) →ₗ[F2] F2)
    (bias : List Bool → F2)
    (h0 : [] ∈ N)
    (hchild : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (z : (Fin n → F2) × (Fin m → F2)) :
    ∃ p ∈ N \ J, ∀ j : Fin p.length,
      decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j := by
  let M := N.sup List.length
  have haux : ∀ (r : ℕ) (p : List Bool), p ∈ N → M < p.length + r →
      (∀ j : Fin p.length, decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) →
      ∃ q ∈ N \ J, ∀ j : Fin q.length,
        decide (query (q.take j.val) z = bias (q.take j.val)) = q.get j := by
    intro r
    induction r with
    | zero =>
      intro p hp hlen _
      have hle : p.length ≤ M := Finset.le_sup (f := List.length) hp
      omega
    | succ r ih =>
      intro p hp hlen hmatch
      by_cases hJ : p ∈ J
      · let b := decide (query p z = bias p)
        have hmem : p ++ [b] ∈ N := by
          cases hb : b
          · exact (hchild p hJ).1
          · exact (hchild p hJ).2
        refine ih (p ++ [b]) hmem (by simp; omega) ?_
        intro j
        by_cases hj : j.val < p.length
        · have htake : (p ++ [b]).take j.val = p.take j.val := by
            rw [List.take_append_of_le_length (by omega)]
          have hget : (p ++ [b]).get j = p.get ⟨j.val, hj⟩ := by
            simp [List.getElem_append_left hj]
          rw [htake, hget]
          exact hmatch ⟨j.val, hj⟩
        · have hjeq : j.val = p.length := by
            have := j.isLt
            simp at this
            omega
          have htake : (p ++ [b]).take j.val = p := by
            rw [hjeq, List.take_left]
          have hget : (p ++ [b]).get j = b := by
            simp [hjeq]
          rw [htake, hget]
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hmatch⟩
  exact haux (M + 1) [] h0 (by simp) (fun j => Fin.elim0 j)
lemma feasible_to_subspace {n m k d : ℕ} {A : Fin m → Fin n → Fin n → Bool}
    (hf : feasible n m k d (quad n m A)) : SubspaceFeasible n m k d A := by
  classical
  obtain ⟨N, J, query, bias, out, h0, _, _, hchild, hcard, hout⟩ := hf
  let X := Fin n → F2
  let Y := Fin m → F2
  let fiber : List Bool → Finset (X × Y) := fun p =>
    Finset.univ.filter fun z =>
      ∀ j : Fin p.length, decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j
  have hcover : (Finset.univ : Finset (X × Y)).card ≤ ∑ p ∈ N \ J, (fiber p).card := by
    calc (Finset.univ : Finset (X × Y)).card
        ≤ ((N \ J).biUnion fiber).card := by
          apply Finset.card_le_card
          intro z _
          obtain ⟨p, hp, hmatch⟩ := follow_leaf N J query bias h0 hchild z
          exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmatch⟩⟩
      _ ≤ ∑ p ∈ N \ J, (fiber p).card := Finset.card_biUnion_le
  have hXYcard : (Finset.univ : Finset (X × Y)).card = 2 ^ (n + m) := by
    simp [X, Y, Fintype.card_prod, Fintype.card_pi, ZMod.card, pow_add]
  have hne : (N \ J).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty, hXYcard] at hcover
    have : 0 < 2 ^ (n + m) := by positivity
    omega
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (N \ J) (fun q => (fiber q).card) hne
  have hsum_le : ∑ q ∈ N \ J, (fiber q).card ≤ (N \ J).card * (fiber p).card := by
    calc ∑ q ∈ N \ J, (fiber q).card
        ≤ ∑ _q ∈ N \ J, (fiber p).card := Finset.sum_le_sum hmax
      _ = (N \ J).card * (fiber p).card := by simp
  have hp_card_ge : 2 ^ (n + m) ≤ 2 ^ d * (fiber p).card := by
    calc 2 ^ (n + m)
        = (Finset.univ : Finset (X × Y)).card := hXYcard.symm
      _ ≤ ∑ q ∈ N \ J, (fiber q).card := hcover
      _ ≤ (N \ J).card * (fiber p).card := hsum_le
      _ ≤ 2 ^ d * (fiber p).card := Nat.mul_le_mul_right _ hcard
  have hfp_ne : (fiber p).Nonempty := by
    by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty] at hem
    rw [hem, Finset.card_empty, Nat.mul_zero] at hp_card_ge
    have : 0 < 2 ^ (n + m) := by positivity
    omega
  obtain ⟨z0, hz0⟩ := hfp_ne
  have hz0_match : ∀ j : Fin p.length,
      decide (query (p.take j.val) z0 = bias (p.take j.val)) = p.get j :=
    (Finset.mem_filter.mp hz0).2
  let U : Submodule F2 (X × Y) := ⨅ j : Fin p.length, LinearMap.ker (query (p.take j.val))
  have hmem_fiber : ∀ z : X × Y, z ∈ fiber p ↔ z - z0 ∈ U := by
    intro z
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, U, Submodule.mem_iInf,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    constructor
    · intro hz j
      exact zmod2_eq_of_decide_eq ((hz j).trans (hz0_match j).symm)
    · intro hq j
      rw [hq j]
      exact hz0_match j
  have hfp_eq_cardU : (fiber p).card = Fintype.card U := by
    rw [← Fintype.card_coe]
    symm
    apply Fintype.card_of_bijective (f := fun u : U => (⟨z0 + u.val, by
      rw [hmem_fiber]; simp [u.property]⟩ : {z // z ∈ fiber p}))
    constructor
    · intro u₁ u₂ h
      apply Subtype.ext
      have h' : z0 + u₁.val = z0 + u₂.val := congrArg Subtype.val h
      exact add_left_cancel h'
    · intro ⟨z, hz⟩
      refine ⟨⟨z - z0, (hmem_fiber z).mp hz⟩, ?_⟩
      apply Subtype.ext
      simp
  rw [hfp_eq_cardU, card_submodule_eq_pow, ← pow_add] at hp_card_ge
  have hdimU : n + m ≤ d + Module.finrank F2 U :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hp_card_ge
  obtain ⟨⟨R, c, hRk, hout_eq⟩, hleaf⟩ := hout p hp
  have hleaf' : ∀ u ∈ U, (z0.2 + u.2) + quad n m A (z0.1 + u.1) - c ∈ R := by
    intro u hu
    have hzin : z0 + u ∈ fiber p := by
      rw [hmem_fiber]; simp [hu]
    have hmem := hleaf (z0 + u) (Finset.mem_filter.mp hzin).2
    rw [hout_eq] at hmem
    simpa using hmem
  have hbase : z0.2 + quad n m A z0.1 - c ∈ R := by
    have h0 := hleaf' 0 U.zero_mem
    change (z0.2 + 0) + quad n m A (z0.1 + 0) - c ∈ R at h0
    simpa only [add_zero] using h0
  have hshift : ∀ u ∈ U, u.2 + quad n m A (z0.1 + u.1) + quad n m A z0.1 ∈ R := by
    intro u hu
    have hsub := R.sub_mem (hleaf' u hu) hbase
    have heq : (z0.2 + u.2 + quad n m A (z0.1 + u.1) - c) - (z0.2 + quad n m A z0.1 - c) =
        u.2 + quad n m A (z0.1 + u.1) + quad n m A z0.1 := by
      funext e
      change (z0.2 e + u.2 e + quad n m A (z0.1 + u.1) e - c e) -
          (z0.2 e + quad n m A z0.1 e - c e) =
        u.2 e + quad n m A (z0.1 + u.1) e + quad n m A z0.1 e
      simp only [zmod2_sub_eq_add]
      have hz2 : z0.2 e + z0.2 e = 0 := zmod2_add_self _
      have hc2 : c e + c e = 0 := zmod2_add_self _
      calc z0.2 e + u.2 e + quad n m A (z0.1 + u.1) e + c e +
            (z0.2 e + quad n m A z0.1 e + c e)
          = (z0.2 e + z0.2 e) + (c e + c e) +
            (u.2 e + quad n m A (z0.1 + u.1) e + quad n m A z0.1 e) := by ring
        _ = u.2 e + quad n m A (z0.1 + u.1) e + quad n m A z0.1 e := by rw [hz2, hc2]; ring
    rwa [heq] at hsub
  let UX : Submodule F2 X := U.map (LinearMap.fst F2 X Y)
  let UY : Submodule F2 Y := U.comap (LinearMap.inr F2 X Y)
  have hUY_le_R : UY ≤ R := by
    intro v hv
    have h1 := hshift (0, v) hv
    have h2 : v + quad n m A (z0.1 + 0) + quad n m A z0.1 = v := by
      funext e
      simp only [add_zero]
      have hq : quad n m A z0.1 e + quad n m A z0.1 e = 0 := zmod2_add_self _
      change v e + quad n m A z0.1 e + quad n m A z0.1 e = v e
      calc v e + quad n m A z0.1 e + quad n m A z0.1 e
          = v e + (quad n m A z0.1 e + quad n m A z0.1 e) := by ring
        _ = v e := by rw [hq, add_zero]
    rwa [h2] at h1
  have hfinU : Module.finrank F2 U = Module.finrank F2 UX + Module.finrank F2 UY := by
    let f : U →ₗ[F2] X := (LinearMap.fst F2 X Y).domRestrict U
    have hrange : LinearMap.range f = UX := by
      ext x
      simp [f, UX]
    have hker : Module.finrank F2 (LinearMap.ker f) = Module.finrank F2 UY := by
      refine LinearEquiv.finrank_eq ?_
      exact
        { toFun := fun w => ⟨w.1.1.2, by
            have h0 : w.1.1.1 = 0 := w.2
            show (0, w.1.1.2) ∈ U
            have : (0, w.1.1.2) = w.1.1 := Prod.ext h0.symm rfl
            rw [this]; exact w.1.2⟩
          invFun := fun v => ⟨⟨(0, v.1), v.2⟩, rfl⟩
          left_inv := fun w => by
            apply Subtype.ext; apply Subtype.ext
            exact Prod.ext w.2.symm rfl
          right_inv := fun v => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, hker] at hrn
    exact hrn.symm
  have hUY_le_finR : Module.finrank F2 UY ≤ Module.finrank F2 R := Submodule.finrank_mono hUY_le_R
  have hUX_le : Module.finrank F2 UX ≤ n := by
    calc Module.finrank F2 UX ≤ Module.finrank F2 X := Submodule.finrank_le UX
      _ = n := by simp [X]
  have hR_le : Module.finrank F2 R ≤ m := by
    calc Module.finrank F2 R ≤ Module.finrank F2 Y := Submodule.finrank_le R
      _ = m := by simp [Y]
  have hdim_fin : (n - Module.finrank F2 UX) + (m - Module.finrank F2 R) ≤ d := by
    have h1 : Module.finrank F2 U ≤ Module.finrank F2 UX + Module.finrank F2 R := by
      rw [hfinU]; exact Nat.add_le_add_left hUY_le_finR _
    omega
  refine ⟨UX, R, hRk, hdim_fin, ?_⟩
  intro x₁ hx₁ x₂ hx₂
  obtain ⟨⟨u₁, v₁⟩, hu₁, hx₁eq⟩ := Submodule.mem_map.mp hx₁
  obtain ⟨⟨u₂, v₂⟩, hu₂, hx₂eq⟩ := Submodule.mem_map.mp hx₂
  simp only [LinearMap.fst_apply] at hx₁eq hx₂eq
  subst hx₁eq; subst hx₂eq
  have h1 := hshift (u₁, v₁) hu₁
  have h2 := hshift (u₂, v₂) hu₂
  have h12 := hshift (u₁ + u₂, v₁ + v₂) (U.add_mem hu₁ hu₂)
  have hsum := R.add_mem (R.add_mem h1 h2) h12
  have hpol : polar n m A u₁ u₂ =
      (v₁ + quad n m A (z0.1 + u₁) + quad n m A z0.1) +
      (v₂ + quad n m A (z0.1 + u₂) + quad n m A z0.1) +
      ((v₁ + v₂) + quad n m A (z0.1 + (u₁ + u₂)) + quad n m A z0.1) := by
    funext e
    change polar n m A u₁ u₂ e =
      (v₁ e + quad n m A (z0.1 + u₁) e + quad n m A z0.1 e) +
      (v₂ e + quad n m A (z0.1 + u₂) e + quad n m A z0.1 e) +
      ((v₁ e + v₂ e) + quad n m A (z0.1 + (u₁ + u₂)) e + quad n m A z0.1 e)
    have hq1 := quad_add n m A z0.1 u₁ e
    have hq2 := quad_add n m A z0.1 u₂ e
    have hq12 := quad_add n m A z0.1 (u₁ + u₂) e
    have hqu := quad_add n m A u₁ u₂ e
    have hpr : polar n m A z0.1 (u₁ + u₂) e =
        polar n m A z0.1 u₁ e + polar n m A z0.1 u₂ e := by
      have := congrFun (polar_add_right n m A z0.1 u₁ u₂) e
      simpa using this
    rw [hq1, hq2, hq12, hqu, hpr]
    have hv1 : v₁ e + v₁ e = 0 := zmod2_add_self _
    have hv2 : v₂ e + v₂ e = 0 := zmod2_add_self _
    have hqz : quad n m A z0.1 e + quad n m A z0.1 e = 0 := zmod2_add_self _
    have hqu1 : quad n m A u₁ e + quad n m A u₁ e = 0 := zmod2_add_self _
    have hqu2 : quad n m A u₂ e + quad n m A u₂ e = 0 := zmod2_add_self _
    have hp1 : polar n m A z0.1 u₁ e + polar n m A z0.1 u₁ e = 0 := zmod2_add_self _
    have hp2 : polar n m A z0.1 u₂ e + polar n m A z0.1 u₂ e = 0 := zmod2_add_self _
    calc polar n m A u₁ u₂ e
        = (v₁ e + v₁ e) + (v₂ e + v₂ e) + (quad n m A z0.1 e + quad n m A z0.1 e) +
          (quad n m A z0.1 e + quad n m A z0.1 e) +
          (quad n m A z0.1 e + quad n m A z0.1 e) +
          (quad n m A u₁ e + quad n m A u₁ e) + (quad n m A u₂ e + quad n m A u₂ e) +
          (polar n m A z0.1 u₁ e + polar n m A z0.1 u₁ e) +
          (polar n m A z0.1 u₂ e + polar n m A z0.1 u₂ e) +
          polar n m A u₁ u₂ e := by
            rw [hv1, hv2, hqz, hqu1, hqu2, hp1, hp2]; ring
      _ = v₁ e + (quad n m A z0.1 e + quad n m A u₁ e + polar n m A z0.1 u₁ e) +
            quad n m A z0.1 e +
          (v₂ e + (quad n m A z0.1 e + quad n m A u₂ e + polar n m A z0.1 u₂ e) +
            quad n m A z0.1 e) +
          (v₁ e + v₂ e + (quad n m A z0.1 e + (quad n m A u₁ e + quad n m A u₂ e +
            polar n m A u₁ u₂ e) + (polar n m A z0.1 u₁ e + polar n m A z0.1 u₂ e)) +
            quad n m A z0.1 e) := by ring
  rw [hpol]
  exact hsum
lemma list_bool_len_finset_card (L : ℕ) :
    ((Finset.univ : Finset (Fin L → Bool)).image List.ofFn).card = 2 ^ L := by
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp [Fintype.card_pi]
lemma subspace_to_feasible {n m k d : ℕ} {A : Fin m → Fin n → Fin n → Bool}
    (hs : SubspaceFeasible n m k d A) : feasible n m k d (quad n m A) := by
  classical
  obtain ⟨UX, R, hRk, hdim, hpol⟩ := hs
  let X := Fin n → F2
  let Y := Fin m → F2
  have hXfin : Module.finrank F2 X = n := by simp [X]
  have hYfin : Module.finrank F2 Y = m := by simp [Y]
  let cX := n - Module.finrank F2 UX
  let t := m - Module.finrank F2 R
  obtain ⟨ℓ0, hℓ0⟩ := exists_functionals_ker UX
  obtain ⟨φ0, hφ0⟩ := exists_functionals_ker R
  have hcX_eq : cX = Module.finrank F2 X - Module.finrank F2 UX := by rw [hXfin]
  have ht_eq : t = Module.finrank F2 Y - Module.finrank F2 R := by rw [hYfin]
  let ℓ : Fin cX → (X →ₗ[F2] F2) := fun i => ℓ0 (finCongr hcX_eq i)
  let φ : Fin t → (Y →ₗ[F2] F2) := fun i => φ0 (finCongr ht_eq i)
  have hℓ : ∀ x : X, (∀ i : Fin cX, ℓ i x = 0) ↔ x ∈ UX := by
    intro x
    rw [← hℓ0 x]
    constructor
    · intro h i
      have h' := h (finCongr hcX_eq.symm i)
      simpa [ℓ] using h'
    · intro h i
      exact h _
  have hφ : ∀ y : Y, (∀ i : Fin t, φ i y = 0) ↔ y ∈ R := by
    intro y
    rw [← hφ0 y]
    constructor
    · intro h i
      have h' := h (finCongr ht_eq.symm i)
      simpa [φ] using h'
    · intro h i
      exact h _
  let matchesX : List Bool → X → Prop := fun pX x =>
    ∀ j : Fin cX, decide (ℓ j x = 1) = pX.getD j.val false
  let repX : List Bool → X := fun pX =>
    if h : ∃ x : X, matchesX pX x then Classical.choose h else 0
  have hlin_aux : ∀ (x0 : X) (r : Fin t),
      ∃ L : X →ₗ[F2] F2, ∀ u ∈ UX, L u = φ r (quad n m A (x0 + u) + quad n m A x0) := by
    intro x0 r
    let f : UX →ₗ[F2] F2 :=
      { toFun := fun u => φ r (quad n m A (x0 + u.1) + quad n m A x0)
        map_add' := fun u₁ u₂ => by
          have hp : polar n m A u₁.1 u₂.1 ∈ R := hpol u₁.1 u₁.2 u₂.1 u₂.2
          have hφp : φ r (polar n m A u₁.1 u₂.1) = 0 := (hφ _).mpr hp r
          have hdiff : quad n m A (x0 + (u₁.1 + u₂.1)) + quad n m A x0 =
              (quad n m A (x0 + u₁.1) + quad n m A x0) +
              (quad n m A (x0 + u₂.1) + quad n m A x0) + polar n m A u₁.1 u₂.1 := by
            funext e
            simp only [Pi.add_apply]
            have hq1 := quad_add n m A x0 u₁.1 e
            have hq2 := quad_add n m A x0 u₂.1 e
            have hq12 := quad_add n m A x0 (u₁.1 + u₂.1) e
            have hqu := quad_add n m A u₁.1 u₂.1 e
            have hpr : polar n m A x0 (u₁.1 + u₂.1) e =
                polar n m A x0 u₁.1 e + polar n m A x0 u₂.1 e := by
              have := congrFun (polar_add_right n m A x0 u₁.1 u₂.1) e
              simpa using this
            rw [hq1, hq2, hq12, hqu, hpr]
            have hqz : quad n m A x0 e + quad n m A x0 e = 0 := zmod2_add_self _
            calc quad n m A x0 e + (quad n m A u₁.1 e + quad n m A u₂.1 e + polar n m A u₁.1 u₂.1 e) +
                  (polar n m A x0 u₁.1 e + polar n m A x0 u₂.1 e) + quad n m A x0 e
                = (quad n m A x0 e + quad n m A x0 e) +
                  (quad n m A x0 e + (quad n m A u₁.1 e + quad n m A u₂.1 e + polar n m A u₁.1 u₂.1 e) +
                    (polar n m A x0 u₁.1 e + polar n m A x0 u₂.1 e) + quad n m A x0 e) := by
                    rw [hqz, zero_add]
              _ = quad n m A x0 e + quad n m A u₁.1 e + polar n m A x0 u₁.1 e + quad n m A x0 e +
                  (quad n m A x0 e + quad n m A u₂.1 e + polar n m A x0 u₂.1 e + quad n m A x0 e) +
                  polar n m A u₁.1 u₂.1 e := by ring
          show φ r (quad n m A (x0 + (u₁.1 + u₂.1)) + quad n m A x0) =
            φ r (quad n m A (x0 + u₁.1) + quad n m A x0) +
            φ r (quad n m A (x0 + u₂.1) + quad n m A x0)
          rw [hdiff, map_add, map_add, hφp, add_zero]
        map_smul' := fun c u => by
          rcases zmod2_cases c with rfl | rfl
          · simp only [zero_smul, ZeroMemClass.coe_zero, add_zero, RingHom.id_apply]
            have hz : quad n m A x0 + quad n m A x0 = 0 := by
              funext e; exact zmod2_add_self _
            rw [hz, map_zero]
          · simp }
    obtain ⟨L, hL⟩ := f.exists_extend
    refine ⟨L, fun u hu => ?_⟩
    have := LinearMap.congr_fun hL ⟨u, hu⟩
    simpa [f] using this
  let extL : List Bool → Fin t → (X →ₗ[F2] F2) := fun pX r =>
    Classical.choose (hlin_aux (repX pX) r)
  have hextL : ∀ pX r u, u ∈ UX →
      extL pX r u = φ r (quad n m A (repX pX + u) + quad n m A (repX pX)) :=
    fun pX r => Classical.choose_spec (hlin_aux (repX pX) r)
  let D := cX + t
  let layer : ℕ → Finset (List Bool) := fun l =>
    (Finset.univ : Finset (Fin l → Bool)).image List.ofFn
  let N : Finset (List Bool) := (Finset.range (D + 1)).biUnion layer
  let J : Finset (List Bool) := (Finset.range D).biUnion layer
  have hmem_layer : ∀ {l : ℕ} {p : List Bool}, p ∈ layer l ↔ p.length = l := by
    intro l p
    simp only [layer, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, rfl⟩; simp
    · intro hp; subst hp; exact ⟨fun i => p.get i, List.ofFn_get p⟩
  have hmemN : ∀ p : List Bool, p ∈ N ↔ p.length ≤ D := by
    intro p
    simp only [N, Finset.mem_biUnion, Finset.mem_range, hmem_layer]
    constructor
    · rintro ⟨l, hl, rfl⟩; omega
    · intro hp; exact ⟨p.length, by omega, rfl⟩
  have hmemJ : ∀ p : List Bool, p ∈ J ↔ p.length < D := by
    intro p
    simp only [J, Finset.mem_biUnion, Finset.mem_range, hmem_layer]
    constructor
    · rintro ⟨l, hl, rfl⟩; omega
    · intro hp; exact ⟨p.length, hp, rfl⟩
  have hsdiff : N \ J = layer D := by
    ext p
    simp only [Finset.mem_sdiff, hmemN, hmemJ, hmem_layer]
    omega
  let query : List Bool → (X × Y) →ₗ[F2] F2 := fun p =>
    if h1 : p.length < cX then
      (ℓ ⟨p.length, h1⟩).comp (LinearMap.fst F2 X Y)
    else if h2 : p.length < D then
      (φ ⟨p.length - cX, by omega⟩).comp (LinearMap.snd F2 X Y) +
        (extL (p.take cX) ⟨p.length - cX, by omega⟩).comp (LinearMap.fst F2 X Y)
    else 0
  let bias : List Bool → F2 := fun _ => 1
  let reaches : List Bool → (X × Y) → Prop := fun p z =>
    ∀ j : Fin p.length, decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j
  let out : List Bool → Set Y := fun p =>
    if h : ∃ z : X × Y, reaches p z then
      let zp := Classical.choose h
      {w : Y | w - (zp.2 + quad n m A zp.1) ∈ R}
    else
      {w : Y | w - 0 ∈ R}
  refine ⟨N, J, query, bias, out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmemN]; simp
  · intro p hp; rw [hmemN]; rw [hmemJ] at hp; omega
  · intro p b hp; rw [hmemJ]; rw [hmemN] at hp; simp at hp; omega
  · intro p hp; rw [hmemJ] at hp; constructor <;> (rw [hmemN]; simp; omega)
  · rw [hsdiff, list_bool_len_finset_card]
    exact Nat.pow_le_pow_right (by norm_num) hdim
  · intro p hp
    rw [hsdiff, hmem_layer] at hp
    constructor
    · show ∃ (R' : Submodule F2 Y) (c' : Y), Module.finrank F2 R' ≤ k ∧ out p = {w : Y | w - c' ∈ R'}
      by_cases hex : ∃ z : X × Y, reaches p z
      · refine ⟨R, (Classical.choose hex).2 + quad n m A (Classical.choose hex).1, hRk, ?_⟩
        simp only [out, hex, ↓reduceDIte]
      · refine ⟨R, 0, hRk, ?_⟩
        simp only [out, hex, ↓reduceDIte]
    · intro z hz
      have hex : ∃ z' : X × Y, reaches p z' := ⟨z, hz⟩
      let zp := Classical.choose hex
      have hzp : reaches p zp := Classical.choose_spec hex
      have hout_p : out p = {w : Y | w - (zp.2 + quad n m A zp.1) ∈ R} := by
        simp only [out, hex, ↓reduceDIte, zp]
      rw [hout_p]
      show z.2 + quad n m A z.1 - (zp.2 + quad n m A zp.1) ∈ R
      have hmatch_z : matchesX (p.take cX) z.1 := by
        intro j
        have hjlt : j.val < p.length := by omega
        have h1 := hz ⟨j.val, hjlt⟩
        have hlen : (p.take j.val).length = j.val := by simp; omega
        have hq : query (p.take j.val) z = ℓ j z.1 := by
          simp only [query, hlen, j.isLt, ↓reduceDIte]; rfl
        rw [hq] at h1
        have hget : (p.take cX).getD j.val false = p.get ⟨j.val, hjlt⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt,
            List.getElem?_eq_getElem hjlt]
          rfl
        rw [hget]
        exact h1
      have hmatch_zp : matchesX (p.take cX) zp.1 := by
        intro j
        have hjlt : j.val < p.length := by omega
        have h1 := hzp ⟨j.val, hjlt⟩
        have hlen : (p.take j.val).length = j.val := by simp; omega
        have hq : query (p.take j.val) zp = ℓ j zp.1 := by
          simp only [query, hlen, j.isLt, ↓reduceDIte]; rfl
        rw [hq] at h1
        have hget : (p.take cX).getD j.val false = p.get ⟨j.val, hjlt⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt,
            List.getElem?_eq_getElem hjlt]
          rfl
        rw [hget]
        exact h1
      have hrep : matchesX (p.take cX) (repX (p.take cX)) := by
        have hexX : ∃ x : X, matchesX (p.take cX) x := ⟨z.1, hmatch_z⟩
        simp only [repX, hexX, ↓reduceDIte]
        exact Classical.choose_spec hexX
      let x0 := repX (p.take cX)
      have hz_u : z.1 + x0 ∈ UX := by
        rw [← hℓ]
        intro j
        have h1 : ℓ j z.1 = ℓ j x0 := zmod2_eq_of_decide_eq ((hmatch_z j).trans (hrep j).symm)
        rw [map_add, h1, zmod2_add_self]
      have hzp_u : zp.1 + x0 ∈ UX := by
        rw [← hℓ]
        intro j
        have h1 : ℓ j zp.1 = ℓ j x0 := zmod2_eq_of_decide_eq ((hmatch_zp j).trans (hrep j).symm)
        rw [map_add, h1, zmod2_add_self]
      have hdiff_u : z.1 - zp.1 = (z.1 + x0) + (zp.1 + x0) := by
        funext i
        change z.1 i - zp.1 i = (z.1 i + x0 i) + (zp.1 i + x0 i)
        rw [zmod2_sub_eq_add]
        have hx0 : x0 i + x0 i = 0 := zmod2_add_self _
        calc z.1 i + zp.1 i = z.1 i + zp.1 i + (x0 i + x0 i) := by rw [hx0, add_zero]
          _ = z.1 i + x0 i + (zp.1 i + x0 i) := by ring
      rw [← hφ]
      intro r
      have hjlt : cX + r.val < p.length := by omega
      have hlen : (p.take (cX + r.val)).length = cX + r.val := by simp; omega
      have htake_cX : (p.take (cX + r.val)).take cX = p.take cX := by
        rw [List.take_take, Nat.min_eq_left (Nat.le_add_right cX r.val)]
      have hq_eq : ∀ w : X × Y, query (p.take (cX + r.val)) w =
          φ r w.2 + extL (p.take cX) r w.1 := by
        intro w
        have hn1 : ¬ (p.take (cX + r.val)).length < cX := by omega
        have hn2 : (p.take (cX + r.val)).length < D := by omega
        simp only [query, hn1, hn2, ↓reduceDIte, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.snd_apply, LinearMap.fst_apply, htake_cX]
        have hidx : (⟨(p.take (cX + r.val)).length - cX, by omega⟩ : Fin t) = r := by
          apply Fin.ext; simp [hlen]
        rw [hidx]
      have hqz : query (p.take (cX + r.val)) z = query (p.take (cX + r.val)) zp :=
        zmod2_eq_of_decide_eq ((hz ⟨cX + r.val, hjlt⟩).trans (hzp ⟨cX + r.val, hjlt⟩).symm)
      rw [hq_eq z, hq_eq zp] at hqz
      have hlin_z : extL (p.take cX) r (z.1 + x0) =
          φ r (quad n m A z.1 + quad n m A x0) := by
        have hx : x0 + (z.1 + x0) = z.1 := by
          funext i
          change x0 i + (z.1 i + x0 i) = z.1 i
          have hx0 : x0 i + x0 i = 0 := zmod2_add_self _
          calc x0 i + (z.1 i + x0 i) = z.1 i + (x0 i + x0 i) := by ring
            _ = z.1 i := by rw [hx0, add_zero]
        simpa [x0, hx] using hextL (p.take cX) r (z.1 + x0) hz_u
      have hlin_zp : extL (p.take cX) r (zp.1 + x0) =
          φ r (quad n m A zp.1 + quad n m A x0) := by
        have hx : x0 + (zp.1 + x0) = zp.1 := by
          funext i
          change x0 i + (zp.1 i + x0 i) = zp.1 i
          have hx0 : x0 i + x0 i = 0 := zmod2_add_self _
          calc x0 i + (zp.1 i + x0 i) = zp.1 i + (x0 i + x0 i) := by ring
            _ = zp.1 i := by rw [hx0, add_zero]
        simpa [x0, hx] using hextL (p.take cX) r (zp.1 + x0) hzp_u
      have hφ_quad : φ r (quad n m A z.1) + φ r (quad n m A zp.1) =
          extL (p.take cX) r z.1 + extL (p.take cX) r zp.1 := by
        have h1 : extL (p.take cX) r (z.1 - zp.1) =
            extL (p.take cX) r (z.1 + x0) + extL (p.take cX) r (zp.1 + x0) := by
          rw [hdiff_u, map_add]
        rw [map_sub, hlin_z, hlin_zp, map_add, map_add, zmod2_sub_eq_add] at h1
        have hqx0 : φ r (quad n m A x0) + φ r (quad n m A x0) = 0 := zmod2_add_self _
        calc φ r (quad n m A z.1) + φ r (quad n m A zp.1)
            = φ r (quad n m A z.1) + φ r (quad n m A zp.1) +
                (φ r (quad n m A x0) + φ r (quad n m A x0)) := by rw [hqx0, add_zero]
          _ = φ r (quad n m A z.1) + φ r (quad n m A x0) +
                (φ r (quad n m A zp.1) + φ r (quad n m A x0)) := by ring
          _ = extL (p.take cX) r z.1 + extL (p.take cX) r zp.1 := h1.symm
      rw [map_sub, map_add, map_add, zmod2_sub_eq_add]
      have hqz0 : (φ r z.2 + extL (p.take cX) r z.1) + (φ r zp.2 + extL (p.take cX) r zp.1) = 0 := by
        rw [hqz, zmod2_add_self]
      calc φ r z.2 + φ r (quad n m A z.1) + (φ r zp.2 + φ r (quad n m A zp.1))
          = (φ r z.2 + φ r zp.2) + (φ r (quad n m A z.1) + φ r (quad n m A zp.1)) := by ring
        _ = (φ r z.2 + φ r zp.2) + (extL (p.take cX) r z.1 + extL (p.take cX) r zp.1) := by
              rw [hφ_quad]
        _ = (φ r z.2 + extL (p.take cX) r z.1) + (φ r zp.2 + extL (p.take cX) r zp.1) := by ring
        _ = 0 := hqz0
theorem feasible_iff_subspace {n m k d : ℕ} {A : Fin m → Fin n → Fin n → Bool} :
    feasible n m k d (quad n m A) ↔ SubspaceFeasible n m k d A :=
  ⟨feasible_to_subspace, subspace_to_feasible⟩
def b2f (b : Bool) : F2 := if b then 1 else 0
lemma b2f_decide_eq_one (x : F2) : b2f (decide (x = 1)) = x := by
  rcases zmod2_cases x with rfl | rfl <;> decide
lemma b2f_mul (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide
def MatrixFeasible (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool) : Prop :=
  ∃ (a t : ℕ) (U : Fin a → Fin n → Bool) (P : Fin n → Fin a → Bool)
    (W : Fin t → Fin m → Bool) (Q : Fin m → Fin t → Bool),
    a ≤ n ∧ t ≤ m ∧ m ≤ k + t ∧ n + t ≤ a + d ∧
    (∀ α β : Fin a, (Finset.univ.sum fun i : Fin n =>
      b2f (U α i && P i β)) = if α = β then 1 else 0) ∧
    (∀ r s : Fin t, (Finset.univ.sum fun e : Fin m =>
      b2f (W r e && Q e s)) = if r = s then 1 else 0) ∧
    (∀ (r : Fin t) (α β : Fin a),
      (Finset.univ.sum fun e : Fin m =>
        Finset.univ.sum fun i : Fin n =>
          Finset.univ.sum fun j : Fin n =>
            b2f (W r e && xor (A e i j) (A e j i) && U α i && U β j)) = 0)
lemma sum_smul_single {n : ℕ} (x : Fin n → F2) :
    (Finset.univ.sum fun i : Fin n => x i • Pi.single (M := fun _ => F2) i (1 : F2)) = x := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]
lemma subspace_to_matrix {n m k d : ℕ} {A : Fin m → Fin n → Fin n → Bool}
    (hs : SubspaceFeasible n m k d A) : MatrixFeasible n m k d A := by
  classical
  obtain ⟨UX, R, hRk, hdim, hpol⟩ := hs
  let a := Module.finrank F2 UX
  let t := m - Module.finrank F2 R
  have ha_le : a ≤ n := by
    calc a = Module.finrank F2 UX := rfl
      _ ≤ Module.finrank F2 (Fin n → F2) := Submodule.finrank_le UX
      _ = n := by simp
  have hR_le : Module.finrank F2 R ≤ m := by
    calc Module.finrank F2 R ≤ Module.finrank F2 (Fin m → F2) := Submodule.finrank_le R
      _ = m := by simp
  have ht_le : t ≤ m := Nat.sub_le _ _
  let bU := Module.finBasis F2 UX
  have hextU : ∀ β : Fin a, ∃ L : (Fin n → F2) →ₗ[F2] F2, ∀ u : UX, L u.1 = bU.coord β u := by
    intro β
    obtain ⟨L, hL⟩ := (bU.coord β).exists_extend
    exact ⟨L, fun u => LinearMap.congr_fun hL u⟩
  let LU : Fin a → ((Fin n → F2) →ₗ[F2] F2) := fun β => Classical.choose (hextU β)
  have hLU : ∀ β (u : UX), LU β u.1 = bU.coord β u := fun β => Classical.choose_spec (hextU β)
  let U : Fin a → Fin n → Bool := fun α i => decide ((bU α).1 i = 1)
  let P : Fin n → Fin a → Bool := fun i β => decide (LU β (Pi.single i 1) = 1)
  have hq : Module.finrank F2 ((Fin m → F2) ⧸ R) = t := by
    have h := Submodule.finrank_quotient_add_finrank R
    have hm : Module.finrank F2 (Fin m → F2) = m := by simp
    omega
  let bQ := Module.finBasis F2 ((Fin m → F2) ⧸ R)
  let eQ : Fin t ≃ Fin (Module.finrank F2 ((Fin m → F2) ⧸ R)) := finCongr hq.symm
  let φ : Fin t → ((Fin m → F2) →ₗ[F2] F2) := fun r => (bQ.coord (eQ r)).comp R.mkQ
  have hlift : ∀ s : Fin t, ∃ q : Fin m → F2, R.mkQ q = bQ (eQ s) := fun s =>
    Submodule.Quotient.mk_surjective R (bQ (eQ s))
  let qvec : Fin t → (Fin m → F2) := fun s => Classical.choose (hlift s)
  have hqvec : ∀ s : Fin t, R.mkQ (qvec s) = bQ (eQ s) := fun s => Classical.choose_spec (hlift s)
  let W : Fin t → Fin m → Bool := fun r e => decide (φ r (Pi.single e 1) = 1)
  let Q : Fin m → Fin t → Bool := fun e s => decide (qvec s e = 1)
  refine ⟨a, t, U, P, W, Q, ha_le, ht_le, by omega, by omega, ?_, ?_, ?_⟩
  · intro α β
    have hsum : (Finset.univ.sum fun i : Fin n => b2f (U α i && P i β)) = LU β (bU α).1 := by
      calc (Finset.univ.sum fun i : Fin n => b2f (U α i && P i β))
          = Finset.univ.sum fun i : Fin n => (bU α).1 i * LU β (Pi.single i 1) := by
              apply Finset.sum_congr rfl; intro i _
              rw [b2f_mul, b2f_decide_eq_one, b2f_decide_eq_one]
        _ = LU β (Finset.univ.sum fun i : Fin n => (bU α).1 i • Pi.single (M := fun _ => F2) i 1) := by
              rw [map_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [map_smul, smul_eq_mul]
        _ = LU β (bU α).1 := by rw [sum_smul_single]
    rw [hsum, hLU β (bU α)]
    simp [Module.Basis.coord_apply, bU.repr_self, Finsupp.single_apply]
  · intro r s
    have hsum : (Finset.univ.sum fun e : Fin m => b2f (W r e && Q e s)) = φ r (qvec s) := by
      calc (Finset.univ.sum fun e : Fin m => b2f (W r e && Q e s))
          = Finset.univ.sum fun e : Fin m => qvec s e * φ r (Pi.single e 1) := by
              apply Finset.sum_congr rfl; intro e _
              rw [b2f_mul, b2f_decide_eq_one, b2f_decide_eq_one, mul_comm]
        _ = φ r (Finset.univ.sum fun e : Fin m => qvec s e • Pi.single (M := fun _ => F2) e 1) := by
              rw [map_sum]
              apply Finset.sum_congr rfl; intro e _
              rw [map_smul, smul_eq_mul]
        _ = φ r (qvec s) := by rw [sum_smul_single]
    rw [hsum]
    simp only [φ, LinearMap.comp_apply, hqvec s, Module.Basis.coord_apply, bQ.repr_self,
      Finsupp.single_apply]
    by_cases hrs : r = s
    · subst hrs; simp
    · have hne : eQ s ≠ eQ r := fun h => hrs (eQ.injective h).symm
      simp [hrs, hne]
  · intro r α β
    have hp : polar n m A (bU α).1 (bU β).1 ∈ R := hpol _ (bU α).2 _ (bU β).2
    have hφ0 : φ r (polar n m A (bU α).1 (bU β).1) = 0 := by
      simp only [φ, LinearMap.comp_apply]
      have hz : R.mkQ (polar n m A (bU α).1 (bU β).1) = 0 := (Submodule.Quotient.mk_eq_zero R).mpr hp
      rw [hz, map_zero]
    rw [← hφ0]
    have hφ_expand : φ r (polar n m A (bU α).1 (bU β).1) =
        Finset.univ.sum fun e : Fin m =>
          b2f (W r e) * polar n m A (bU α).1 (bU β).1 e := by
      calc φ r (polar n m A (bU α).1 (bU β).1)
          = φ r (Finset.univ.sum fun e : Fin m =>
              polar n m A (bU α).1 (bU β).1 e • Pi.single (M := fun _ => F2) e 1) := by
              rw [sum_smul_single]
        _ = Finset.univ.sum fun e : Fin m =>
              b2f (W r e) * polar n m A (bU α).1 (bU β).1 e := by
              rw [map_sum]
              apply Finset.sum_congr rfl; intro e _
              rw [map_smul, smul_eq_mul, b2f_decide_eq_one, mul_comm]
    rw [hφ_expand]
    apply Finset.sum_congr rfl; intro e _
    unfold polar
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [b2f_mul, b2f_mul, b2f_mul, b2f_decide_eq_one, b2f_decide_eq_one, b2f_decide_eq_one]
    cases xor (A e i j) (A e j i)
    · simp [b2f]
    · simp [b2f]; ring
lemma matrix_to_subspace {n m k d : ℕ} {A : Fin m → Fin n → Fin n → Bool}
    (hm : MatrixFeasible n m k d A) : SubspaceFeasible n m k d A := by
  classical
  obtain ⟨a, t, U, P, W, Q, ha_le, ht_le, hmk, hnd, hUP, hWQ, hbil⟩ := hm
  let uvec : Fin a → (Fin n → F2) := fun α i => b2f (U α i)
  let UX : Submodule F2 (Fin n → F2) := Submodule.span F2 (Set.range uvec)
  let LP : (Fin n → F2) →ₗ[F2] (Fin a → F2) :=
    { toFun := fun x β => Finset.univ.sum fun i : Fin n => x i * b2f (P i β)
      map_add' := fun x y => by
        funext β; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext β; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
  have hLP_surj : Function.Surjective (LP.domRestrict UX) := by
    intro y
    refine ⟨⟨Finset.univ.sum fun α : Fin a => y α • uvec α,
      Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)⟩, ?_⟩
    funext β
    show LP (Finset.univ.sum fun α : Fin a => y α • uvec α) β = y β
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    have hLP_u : ∀ α : Fin a, LP (uvec α) β = if α = β then 1 else 0 := by
      intro α
      calc LP (uvec α) β
          = Finset.univ.sum fun i : Fin n => b2f (U α i && P i β) := by
              show (Finset.univ.sum fun i : Fin n => uvec α i * b2f (P i β)) = _
              apply Finset.sum_congr rfl; intro i _; rw [b2f_mul]
        _ = if α = β then 1 else 0 := hUP α β
    simp only [hLP_u, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have ha_le_finUX : a ≤ Module.finrank F2 UX := by
    have h := LinearMap.finrank_le_finrank_of_surjective hLP_surj
    simpa using h
  let LW : (Fin m → F2) →ₗ[F2] (Fin t → F2) :=
    { toFun := fun y r => Finset.univ.sum fun e : Fin m => b2f (W r e) * y e
      map_add' := fun x y => by
        funext r; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext r
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _; ring }
  let R : Submodule F2 (Fin m → F2) := LinearMap.ker LW
  have hLW_surj : Function.Surjective LW := by
    intro z
    refine ⟨Finset.univ.sum fun s : Fin t => z s • (fun e => b2f (Q e s)), ?_⟩
    funext r
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    have hLW_q : ∀ s : Fin t, LW (fun e => b2f (Q e s)) r = if r = s then 1 else 0 := by
      intro s
      calc LW (fun e => b2f (Q e s)) r
          = Finset.univ.sum fun e : Fin m => b2f (W r e && Q e s) := by
              show (Finset.univ.sum fun e : Fin m => b2f (W r e) * b2f (Q e s)) = _
              apply Finset.sum_congr rfl; intro e _; rw [b2f_mul]
        _ = if r = s then 1 else 0 := hWQ r s
    simp only [hLW_q, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hfinR : t + Module.finrank F2 R = m := by
    have hrn := LinearMap.finrank_range_add_finrank_ker LW
    have hrange : LinearMap.range LW = ⊤ := LinearMap.range_eq_top.mpr hLW_surj
    rw [hrange] at hrn
    simpa [R] using hrn
  refine ⟨UX, R, by omega, by omega, ?_⟩
  intro x hx y hy
  refine Submodule.span_induction (p := fun u _ => ∀ v ∈ UX, polar n m A u v ∈ R)
    ?_ ?_ ?_ ?_ hx y hy
  · rintro _ ⟨α, rfl⟩ v hv
    refine Submodule.span_induction (p := fun v _ => polar n m A (uvec α) v ∈ R)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨β, rfl⟩
      show LW (polar n m A (uvec α) (uvec β)) = 0
      funext r
      show (Finset.univ.sum fun e : Fin m => b2f (W r e) * polar n m A (uvec α) (uvec β) e) = 0
      rw [← hbil r α β]
      apply Finset.sum_congr rfl; intro e _
      unfold polar
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [b2f_mul, b2f_mul, b2f_mul]
      cases xor (A e i j) (A e j i) <;> simp [uvec, b2f]
    · rw [polar_zero_right]; exact R.zero_mem
    · intro v₁ v₂ _ _ h1 h2; rw [polar_add_right]; exact R.add_mem h1 h2
    · intro c v _ hv; rw [polar_smul_right]; exact R.smul_mem c hv
  · intro v _; rw [polar_zero_left]; exact R.zero_mem
  · intro u₁ u₂ _ _ h1 h2 v hv; rw [polar_add_left]; exact R.add_mem (h1 v hv) (h2 v hv)
  · intro c u _ hu v hv; rw [polar_smul_left]; exact R.smul_mem c (hu v hv)
theorem feasible_iff_matrix {n m k d : ℕ} {A : Fin m → Fin n → Fin n → Bool} :
    feasible n m k d (quad n m A) ↔ MatrixFeasible n m k d A :=
  feasible_iff_subspace.trans ⟨subspace_to_matrix, matrix_to_subspace⟩
def graphAdj {n m : ℕ} (u v : Fin m → Fin n) (e : Fin m) (i j : Fin n) : Bool :=
  decide (i = u e ∧ j = v e)
lemma polar_graphAdj {n m : ℕ} (u v : Fin m → Fin n) (_huv : ∀ e, u e < v e)
    (x y : Fin n → F2) (e : Fin m) :
    polar n m (graphAdj u v) x y e = x (u e) * y (v e) + x (v e) * y (u e) := by
  rw [polar_eq_sum]
  simp only [Finset.sum_add_distrib]
  have h1 : (Finset.univ.sum fun i : Fin n => Finset.univ.sum fun j : Fin n =>
      if graphAdj u v e i j then x i * y j else 0) = x (u e) * y (v e) := by
    have hinner : ∀ i : Fin n, (Finset.univ.sum fun j : Fin n =>
        if graphAdj u v e i j then x i * y j else 0) = if i = u e then x i * y (v e) else 0 := by
      intro i
      by_cases hi : i = u e
      · subst hi
        simp [graphAdj]
      · simp [graphAdj, hi]
    simp [hinner]
  have h2 : (Finset.univ.sum fun i : Fin n => Finset.univ.sum fun j : Fin n =>
      if graphAdj u v e j i then x i * y j else 0) = x (v e) * y (u e) := by
    have hinner : ∀ i : Fin n, (Finset.univ.sum fun j : Fin n =>
        if graphAdj u v e j i then x i * y j else 0) = if i = v e then x i * y (u e) else 0 := by
      intro i
      by_cases hi : i = v e
      · subst hi
        simp [graphAdj]
      · simp [graphAdj, hi]
    simp [hinner]
  rw [h1, h2]
lemma exists_pivot_set {n : ℕ} (UX : Submodule F2 (Fin n → F2)) :
    ∃ S : Finset (Fin n), S.card = n - Module.finrank F2 UX ∧
      ∀ a : Fin n, a ∉ S → ∃ w ∈ UX, ∀ b : Fin n, b ∉ S → w b = if b = a then 1 else 0 := by
  classical
  let Q := (Fin n → F2) ⧸ UX
  let vec : Fin n → Q := fun i => UX.mkQ (Pi.single i 1)
  let P : Finset (Fin n) → Prop := fun S => Submodule.span F2 (vec '' (S : Set (Fin n))) = ⊤
  have hPun : P Finset.univ := by
    dsimp only [P]
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective UX q
    change UX.mkQ x ∈ _
    rw [← sum_smul_single x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp, rfl⟩)
  let cands := Finset.univ.filter P
  have hcne : cands.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPun⟩⟩
  obtain ⟨S, hSmem, hSmin⟩ := Finset.exists_min_image cands Finset.card hcne
  have hPS : P S := (Finset.mem_filter.mp hSmem).2
  have hli : LinearIndependent F2 (fun i : S => vec i.1) := by
    rw [linearIndependent_iff']
    intro t c hsum i hi
    by_contra hci
    have hci1 : c i = 1 := by
      rcases zmod2_cases (c i) with h0 | h1
      · exact (hci h0).elim
      · exact h1
    have hveci : vec i.1 ∈ Submodule.span F2 (vec '' ((S.erase i.1 : Finset (Fin n)) : Set (Fin n))) := by
      have h1 : vec i.1 = ∑ j ∈ t.erase i, c j • vec j.1 := by
        have hadd := Finset.add_sum_erase t (fun j : S => c j • vec j.1) hi
        rw [hci1, one_smul] at hadd
        have h2 : vec i.1 + (∑ j ∈ t.erase i, c j • vec j.1) = 0 := hadd.trans hsum
        have h3 : vec i.1 = -(∑ j ∈ t.erase i, c j • vec j.1) := eq_neg_of_add_eq_zero_left h2
        have hneg : ∀ q : Q, -q = q := by
          intro q
          obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective UX q
          change -UX.mkQ x = UX.mkQ x
          rw [← map_neg]
          congr 1; funext j; rcases zmod2_cases (x j) with h | h <;> simp [h]
        rw [h3, hneg]
      rw [h1]
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      exact ⟨j.1, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨Subtype.coe_ne_coe.mpr hne, j.2⟩), rfl⟩
    have hP' : P (S.erase i.1) := by
      dsimp only [P]
      rw [eq_top_iff, ← hPS, Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      by_cases hji : j = i.1
      · subst hji; exact hveci
      · exact Submodule.subset_span ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hji, hj⟩), rfl⟩
    have hcard_lt : (S.erase i.1).card < S.card := Finset.card_erase_lt_of_mem i.2
    have hcard_ge := hSmin (S.erase i.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
    omega
  have hspan : Submodule.span F2 (Set.range (fun i : S => vec i.1)) = ⊤ := by
    convert hPS using 2
    ext q; simp
  let bQ : Module.Basis S F2 Q := Module.Basis.mk hli (le_of_eq hspan.symm)
  have hScard : S.card = n - Module.finrank F2 UX := by
    have h1 : Module.finrank F2 ((Fin n → F2) ⧸ UX) = S.card := by
      change Module.finrank F2 Q = S.card
      rw [Module.finrank_eq_card_basis bQ, Fintype.card_coe]
    have h2 := Submodule.finrank_quotient_add_finrank UX
    have h3 : Module.finrank F2 (Fin n → F2) = n := by simp
    omega
  refine ⟨S, hScard, fun a ha => ?_⟩
  have hrepr := bQ.sum_repr (vec a)
  let x : Fin n → F2 := Pi.single a 1 - ∑ i : S, (bQ.repr (vec a) i) • Pi.single i.1 1
  refine ⟨x, ?_, fun b hb => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero UX]
    change UX.mkQ x = 0
    simp only [x, map_sub, map_sum, map_smul]
    have hsum : (∑ i : S, bQ.repr (vec a) i • UX.mkQ (Pi.single i.1 1)) = UX.mkQ (Pi.single a 1) := by
      simpa [bQ, vec] using hrepr
    rw [hsum, sub_self]
  · simp only [x, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    have hzero : (∑ i : S, bQ.repr (vec a) i * if b = i.1 then (1 : F2) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : b ≠ i.1 := fun h => hb (h ▸ i.2)
      simp [hne]
    rw [hzero, sub_zero]
lemma graph_lower_bound {n m k d : ℕ} (u v : Fin m → Fin n) (huv : ∀ e, u e < v e)
    (hinj : Function.Injective (fun e => (u e, v e)))
    (hf : feasible n m k d (quad n m (graphAdj u v))) :
    ∃ (S : Finset (Fin n)) (r : ℕ), r ≤ k ∧ S.card + (m - r) ≤ d ∧
      (Finset.univ.filter fun e : Fin m => u e ∉ S ∧ v e ∉ S).card ≤ r := by
  classical
  obtain ⟨UX, R, hRk, hdim, hpol⟩ := feasible_to_subspace hf
  obtain ⟨S, hScard, hpiv⟩ := exists_pivot_set UX
  let Eout := Finset.univ.filter fun e : Fin m => u e ∉ S ∧ v e ∉ S
  let proj : R →ₗ[F2] (Eout → F2) :=
    { toFun := fun y e => y.1 e.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective proj := by
    intro z
    have hsingle : ∀ e0 : Eout, ∃ y : R, proj y = Pi.single e0 1 := by
      intro e0
      have he0 : u e0.1 ∉ S ∧ v e0.1 ∉ S := (Finset.mem_filter.mp e0.2).2
      obtain ⟨wa, hwa_mem, hwa⟩ := hpiv (u e0.1) he0.1
      obtain ⟨wb, hwb_mem, hwb⟩ := hpiv (v e0.1) he0.2
      refine ⟨⟨polar n m (graphAdj u v) wa wb, hpol wa hwa_mem wb hwb_mem⟩, ?_⟩
      funext e
      have he : u e.1 ∉ S ∧ v e.1 ∉ S := (Finset.mem_filter.mp e.2).2
      show polar n m (graphAdj u v) wa wb e.1 = Pi.single (M := fun _ => F2) e0 (1 : F2) e
      rw [polar_graphAdj u v huv wa wb e.1, hwa (u e.1) he.1, hwb (v e.1) he.2,
        hwa (v e.1) he.2, hwb (u e.1) he.1, Pi.single_apply]
      have hno : ¬ (v e.1 = u e0.1 ∧ u e.1 = v e0.1) := by
        intro ⟨h1, h2⟩
        have ha := huv e.1
        have hb := huv e0.1
        omega
      by_cases hee : e = e0
      · subst hee
        have hne : v e.1 ≠ u e.1 := ne_of_gt (huv e.1)
        simp [hne]
      · have hne_pair : ¬ (u e.1 = u e0.1 ∧ v e.1 = v e0.1) := by
          intro ⟨h1, h2⟩
          exact hee (Subtype.ext (hinj (Prod.ext h1 h2)))
        by_cases h1 : u e.1 = u e0.1
        · have h2 : v e.1 ≠ v e0.1 := fun h => hne_pair ⟨h1, h⟩
          have h3 : v e.1 ≠ u e0.1 := by rw [← h1]; exact ne_of_gt (huv e.1)
          simp [hee, h1, h2, h3]
        · by_cases h3 : v e.1 = u e0.1
          · have h4 : u e.1 ≠ v e0.1 := fun h => hno ⟨h3, h⟩
            simp [hee, h1, h3, h4]
          · simp [hee, h1, h3]
    choose y hy using hsingle
    refine ⟨Finset.univ.sum fun e0 : Eout => z e0 • y e0, ?_⟩
    rw [map_sum]
    funext e
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hy, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hEout_le : Eout.card ≤ Module.finrank F2 R := by
    have h := LinearMap.finrank_le_finrank_of_surjective hsurj
    simpa [Fintype.card_coe] using h
  refine ⟨S, Module.finrank F2 R, hRk, by omega, hEout_le⟩
def coordSubspace {n : ℕ} (S : Finset (Fin n)) : Submodule F2 (Fin n → F2) where
  carrier := {x | ∀ i ∈ S, x i = 0}
  zero_mem' _ _ := rfl; add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  smul_mem' _ _ hx i hi := by simp [hx i hi]
lemma finrank_coord_subspace {n : ℕ} (S : Finset (Fin n)) :
    Module.finrank F2 (coordSubspace S) = n - S.card := by
  classical
  let e : coordSubspace S ≃ₗ[F2] ({i : Fin n // i ∉ S} → F2) :=
    { toFun := fun x i => x.1 i.1
      invFun := fun y => ⟨fun i => if h : i ∈ S then 0 else y ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        apply Subtype.ext; funext i
        by_cases hi : i ∈ S
        · simp [hi, x.2 i hi]
        · simp [hi]
      right_inv := fun y => by
        funext ⟨i, hi⟩; simp [hi]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe]
lemma graph_upper_bound {n m k d : ℕ} (u v : Fin m → Fin n) (huv : ∀ e, u e < v e)
    (hk : k ≤ m) (S : Finset (Fin n))
    (hcov : (Finset.univ.filter fun e : Fin m => u e ∉ S ∧ v e ∉ S).card ≤ k)
    (hbud : S.card + (m - k) ≤ d) :
    feasible n m k d (quad n m (graphAdj u v)) := by
  classical
  rw [feasible_iff_subspace]
  let Eout := Finset.univ.filter fun e : Fin m => u e ∉ S ∧ v e ∉ S
  have hEout_card : Eout.card ≤ k := hcov
  have hcompl_card : k - Eout.card ≤ Eoutᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨E2, hE2sub, hE2card⟩ := Finset.exists_subset_card_eq hcompl_card
  let E1 := Eout ∪ E2
  have hsub : Eout ⊆ E1 := Finset.subset_union_left
  have hdisj : Disjoint Eout E2 :=
    Finset.disjoint_of_subset_right hE2sub disjoint_compl_right
  have hE1card : E1.card = k := by
    rw [Finset.card_union_of_disjoint hdisj, hE2card]; omega
  let UX : Submodule F2 (Fin n → F2) := coordSubspace S
  let R : Submodule F2 (Fin m → F2) := coordSubspace E1ᶜ
  have hUXfin : Module.finrank F2 UX = n - S.card := finrank_coord_subspace S
  have hRfin : Module.finrank F2 R = k := by
    have h := finrank_coord_subspace E1ᶜ
    have hc : E1ᶜ.card = m - k := by
      rw [Finset.card_compl, Fintype.card_fin, hE1card]
    change Module.finrank F2 (coordSubspace E1ᶜ) = k
    rw [h, hc]
    omega
  have hS_le : S.card ≤ n := by
    have := Finset.card_le_univ S; simpa using this
  refine ⟨UX, R, by rw [hRfin], by rw [hUXfin, hRfin]; omega, ?_⟩
  intro x hx y hy e he
  rw [polar_graphAdj u v huv x y e]
  have henot : e ∉ Eout := fun h => (Finset.mem_compl.mp he) (hsub h)
  simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at henot
  rcases henot with hu | hv
  · rw [hx (u e) hu, hy (u e) hu]; simp
  · rw [hx (v e) hv, hy (v e) hv]; simp
def HasVC {n m : ℕ} (u v : Fin m → Fin n) (c : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ c ∧ ∀ e : Fin m, u e ∈ S ∨ v e ∈ S
def blowupU {p q n0 e0 : ℕ} (hpq : p < q) (u0 : Fin e0 → Fin n0)
    (idx : Fin (q * e0)) : Fin ((q - p) * n0 + 2 * p * e0) :=
  if h : idx.val < (q - p) * e0 then
    have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
    have hdiv : idx.val / e0 < q - p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm e0]; exact h)
    have hmod : idx.val % e0 < e0 := Nat.mod_lt _ he0
    ⟨(idx.val / e0) * n0 + (u0 ⟨idx.val % e0, hmod⟩).val, by
      have hu := (u0 ⟨idx.val % e0, hmod⟩).isLt
      have hm1 : (idx.val / e0 + 1) * n0 ≤ (q - p) * n0 := Nat.mul_le_mul_right n0 hdiv
      have : (idx.val / e0) * n0 + n0 = (idx.val / e0 + 1) * n0 := by ring
      omega⟩
  else
    ⟨(q - p) * n0 + 2 * (idx.val - (q - p) * e0), by
      have hidx := idx.isLt
      have hmul : (q - p) * e0 + p * e0 = q * e0 := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hpq)]
      have h2 : 2 * p * e0 = 2 * (p * e0) := Nat.mul_assoc 2 p e0
      omega⟩
def blowupV {p q n0 e0 : ℕ} (hpq : p < q) (v0 : Fin e0 → Fin n0)
    (idx : Fin (q * e0)) : Fin ((q - p) * n0 + 2 * p * e0) :=
  if h : idx.val < (q - p) * e0 then
    have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
    have hdiv : idx.val / e0 < q - p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm e0]; exact h)
    have hmod : idx.val % e0 < e0 := Nat.mod_lt _ he0
    ⟨(idx.val / e0) * n0 + (v0 ⟨idx.val % e0, hmod⟩).val, by
      have hv := (v0 ⟨idx.val % e0, hmod⟩).isLt
      have hm1 : (idx.val / e0 + 1) * n0 ≤ (q - p) * n0 := Nat.mul_le_mul_right n0 hdiv
      have : (idx.val / e0) * n0 + n0 = (idx.val / e0 + 1) * n0 := by ring
      omega⟩
  else
    ⟨(q - p) * n0 + 2 * (idx.val - (q - p) * e0) + 1, by
      have hidx := idx.isLt
      have hmul : (q - p) * e0 + p * e0 = q * e0 := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hpq)]
      have h2 : 2 * p * e0 = 2 * (p * e0) := Nat.mul_assoc 2 p e0
      omega⟩
lemma blowupU_val_lt {p q n0 e0 : ℕ} (hpq : p < q) (u0 : Fin e0 → Fin n0)
    (idx : Fin (q * e0)) (h : idx.val < (q - p) * e0) (he0 : 0 < e0) :
    (blowupU hpq u0 idx).val = (idx.val / e0) * n0 + (u0 ⟨idx.val % e0, Nat.mod_lt _ he0⟩).val := by
  simp [blowupU, h]
lemma blowupU_val_ge {p q n0 e0 : ℕ} (hpq : p < q) (u0 : Fin e0 → Fin n0)
    (idx : Fin (q * e0)) (h : (q - p) * e0 ≤ idx.val) :
    (blowupU hpq u0 idx).val = (q - p) * n0 + 2 * (idx.val - (q - p) * e0) := by
  have hn : ¬ idx.val < (q - p) * e0 := by omega
  simp [blowupU, hn]
lemma blowupV_val_lt {p q n0 e0 : ℕ} (hpq : p < q) (v0 : Fin e0 → Fin n0)
    (idx : Fin (q * e0)) (h : idx.val < (q - p) * e0) (he0 : 0 < e0) :
    (blowupV hpq v0 idx).val = (idx.val / e0) * n0 + (v0 ⟨idx.val % e0, Nat.mod_lt _ he0⟩).val := by
  simp [blowupV, h]
lemma blowupV_val_ge {p q n0 e0 : ℕ} (hpq : p < q) (v0 : Fin e0 → Fin n0)
    (idx : Fin (q * e0)) (h : (q - p) * e0 ≤ idx.val) :
    (blowupV hpq v0 idx).val = (q - p) * n0 + 2 * (idx.val - (q - p) * e0) + 1 := by
  have hn : ¬ idx.val < (q - p) * e0 := by omega
  simp [blowupV, hn]
lemma blowup_lt {p q n0 e0 : ℕ} (hpq : p < q) (u0 v0 : Fin e0 → Fin n0)
    (huv : ∀ j, u0 j < v0 j) (idx : Fin (q * e0)) :
    blowupU hpq u0 idx < blowupV hpq v0 idx := by
  unfold blowupU blowupV
  split_ifs with h
  · simp only [Fin.lt_def]
    have hmod : idx.val % e0 < e0 := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)
    have := huv ⟨idx.val % e0, hmod⟩
    omega
  · simp only [Fin.lt_def]; omega
lemma blowup_inj {p q n0 e0 : ℕ} (hpq : p < q) (u0 v0 : Fin e0 → Fin n0)
    (hinj : Function.Injective (fun j => (u0 j, v0 j))) :
    Function.Injective (fun idx : Fin (q * e0) => (blowupU hpq u0 idx, blowupV hpq v0 idx)) := by
  intro i₁ i₂ h
  have hu : (blowupU hpq u0 i₁).val = (blowupU hpq u0 i₂).val := congrArg (fun x => x.1.val) h
  have hv : (blowupV hpq v0 i₁).val = (blowupV hpq v0 i₂).val := congrArg (fun x => x.2.val) h
  unfold blowupU at hu
  unfold blowupV at hv
  split_ifs at hu hv with h1 h2 h2
  · have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h1
    have hn0 : 0 < n0 := by
      have hm := Nat.mod_lt i₁.val he0
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) (u0 ⟨i₁.val % e0, hm⟩).isLt
    have hm1 := Nat.mod_lt i₁.val he0
    have hm2 := Nat.mod_lt i₂.val he0
    have hu1 := (u0 ⟨i₁.val % e0, hm1⟩).isLt
    have hu2 := (u0 ⟨i₂.val % e0, hm2⟩).isLt
    have hdiv_eq : i₁.val / e0 = i₂.val / e0 := by
      have hd1 := congrArg (· / n0) hu
      dsimp at hd1
      rw [Nat.mul_comm (i₁.val / e0) n0, Nat.mul_comm (i₂.val / e0) n0,
        Nat.mul_add_div hn0, Nat.mul_add_div hn0,
        Nat.div_eq_of_lt hu1, Nat.div_eq_of_lt hu2] at hd1
      omega
    have hu_eq : u0 ⟨i₁.val % e0, hm1⟩ = u0 ⟨i₂.val % e0, hm2⟩ := by
      apply Fin.ext; dsimp at hu; rw [hdiv_eq] at hu; omega
    have hv_eq : v0 ⟨i₁.val % e0, hm1⟩ = v0 ⟨i₂.val % e0, hm2⟩ := by
      apply Fin.ext; dsimp at hv; rw [hdiv_eq] at hv; omega
    have hmod_eq : i₁.val % e0 = i₂.val % e0 := by
      have := hinj (Prod.ext hu_eq hv_eq)
      exact congrArg Fin.val this
    apply Fin.ext
    have h1d := Nat.div_add_mod i₁.val e0
    have h2d := Nat.div_add_mod i₂.val e0
    rw [hdiv_eq, hmod_eq] at h1d
    omega
  · exfalso
    have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h1
    have hdiv : i₁.val / e0 < q - p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm e0]; exact h1)
    have hu1 := (u0 ⟨i₁.val % e0, Nat.mod_lt _ he0⟩).isLt
    have hm1 : (i₁.val / e0 + 1) * n0 ≤ (q - p) * n0 := Nat.mul_le_mul_right n0 hdiv
    have : (i₁.val / e0) * n0 + n0 = (i₁.val / e0 + 1) * n0 := by ring
    dsimp at hu; omega
  · exfalso
    have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h2
    have hdiv : i₂.val / e0 < q - p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm e0]; exact h2)
    have hu2 := (u0 ⟨i₂.val % e0, Nat.mod_lt _ he0⟩).isLt
    have hm2 : (i₂.val / e0 + 1) * n0 ≤ (q - p) * n0 := Nat.mul_le_mul_right n0 hdiv
    have : (i₂.val / e0) * n0 + n0 = (i₂.val / e0 + 1) * n0 := by ring
    dsimp at hu; omega
  · apply Fin.ext; dsimp at hu; omega
theorem blowup_iff_vc {p q n0 e0 c : ℕ} (hpq : p < q) (u0 v0 : Fin e0 → Fin n0)
    (huv : ∀ j, u0 j < v0 j) (hinj : Function.Injective (fun j => (u0 j, v0 j))) :
    feasible ((q - p) * n0 + 2 * p * e0) (q * e0) (p * e0) ((q - p) * (e0 + c))
      (quad _ _ (graphAdj (blowupU hpq u0) (blowupV hpq v0))) ↔
    HasVC u0 v0 c := by
  classical
  let r := q - p
  have hr_pos : 0 < r := Nat.sub_pos_of_lt hpq
  have hrp : r + p = q := Nat.sub_add_cancel (le_of_lt hpq)
  have hmq : r * e0 + p * e0 = q * e0 := by rw [← Nat.add_mul, hrp]
  have hmq' : (q - p) * e0 + p * e0 = q * e0 := hmq
  constructor
  · intro hf
    obtain ⟨S, rv, hrv_le, hSbud, hEout⟩ :=
      graph_lower_bound (blowupU hpq u0) (blowupV hpq v0) (blowup_lt hpq u0 v0 huv)
        (blowup_inj hpq u0 v0 hinj) hf
    let Sorig := S.filter fun w : Fin (r * n0 + 2 * p * e0) => w.val < r * n0
    let Sdum := S.filter fun w : Fin (r * n0 + 2 * p * e0) => r * n0 ≤ w.val
    have hSsplit : Sorig.card + Sdum.card = S.card := by
      have h := Finset.card_filter_add_card_filter_not (s := S) (fun w => w.val < r * n0)
      have hsd : Sdum = S.filter (fun w => ¬ w.val < r * n0) := by
        ext w; simp [Sdum]
      rw [hsd]; exact h
    let Emiss := (Finset.univ : Finset (Fin (q * e0))).filter fun idx =>
      idx.val < r * e0 ∧ blowupU hpq u0 idx ∉ Sorig ∧ blowupV hpq v0 idx ∉ Sorig
    let EdumUncov := (Finset.univ : Finset (Fin (q * e0))).filter fun idx =>
      r * e0 ≤ idx.val ∧ blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S
    let EdumCov := (Finset.univ : Finset (Fin (q * e0))).filter fun idx =>
      r * e0 ≤ idx.val ∧ (blowupU hpq u0 idx ∈ S ∨ blowupV hpq v0 idx ∈ S)
    have hEdumTotal : EdumUncov.card + EdumCov.card = p * e0 := by
      let allDum := (Finset.univ : Finset (Fin (q * e0))).filter fun idx => r * e0 ≤ idx.val
      have h1 : EdumUncov.card + EdumCov.card = allDum.card := by
        have h := Finset.card_filter_add_card_filter_not (s := allDum)
          (fun idx => blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S)
        have hdu : EdumUncov = allDum.filter (fun idx => blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S) := by
          ext idx; simp [EdumUncov, allDum]
        have hdc : EdumCov = allDum.filter (fun idx => ¬ (blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S)) := by
          ext idx; simp only [EdumCov, allDum, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        rw [hdu, hdc]; exact h
      rw [h1]
      have hbij : allDum.card = p * e0 := by
        rw [← Fintype.card_fin (p * e0), ← Fintype.card_coe]
        apply Fintype.card_of_bijective (f := fun idx : allDum =>
          (⟨idx.1.val - r * e0, by
            have := idx.1.isLt
            have hge := (Finset.mem_filter.mp idx.2).2
            omega⟩ : Fin (p * e0)))
        constructor
        · intro a b hab
          apply Subtype.ext; apply Fin.ext
          have ha := (Finset.mem_filter.mp a.2).2
          have hb := (Finset.mem_filter.mp b.2).2
          have := congrArg Fin.val hab; dsimp at this; omega
        · intro s
          refine ⟨⟨⟨r * e0 + s.val, by omega⟩, by simp [allDum]⟩, ?_⟩
          apply Fin.ext; simp
      exact hbij
    have hEdumCov_le : EdumCov.card ≤ Sdum.card := by
      let f : Fin (q * e0) → Fin (r * n0 + 2 * p * e0) := fun idx =>
        if blowupU hpq u0 idx ∈ S then blowupU hpq u0 idx else blowupV hpq v0 idx
      have hmap : ∀ idx ∈ EdumCov, f idx ∈ Sdum := by
        intro idx hidx
        obtain ⟨_, hge, hor⟩ := Finset.mem_filter.mp hidx
        by_cases hu : blowupU hpq u0 idx ∈ S
        · simp only [f, hu, ↓reduceIte]
          refine Finset.mem_filter.mpr ⟨hu, ?_⟩
          rw [blowupU_val_ge hpq u0 idx hge]
          exact Nat.le_add_right _ _
        · simp only [f, hu, ↓reduceIte]
          refine Finset.mem_filter.mpr ⟨hor.resolve_left hu, ?_⟩
          rw [blowupV_val_ge hpq v0 idx hge]
          exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
      have hinj_f : Set.InjOn f EdumCov := by
        intro i₁ hi₁ i₂ hi₂ heq
        have hg1 : (q - p) * e0 ≤ i₁.val := (Finset.mem_filter.mp hi₁).2.1
        have hg2 : (q - p) * e0 ≤ i₂.val := (Finset.mem_filter.mp hi₂).2.1
        have hf1 : (f i₁).val = r * n0 + 2 * (i₁.val - r * e0) ∨
            (f i₁).val = r * n0 + 2 * (i₁.val - r * e0) + 1 := by
          unfold f; split_ifs
          · left; exact blowupU_val_ge hpq u0 i₁ hg1
          · right; exact blowupV_val_ge hpq v0 i₁ hg1
        have hf2 : (f i₂).val = r * n0 + 2 * (i₂.val - r * e0) ∨
            (f i₂).val = r * n0 + 2 * (i₂.val - r * e0) + 1 := by
          unfold f; split_ifs
          · left; exact blowupU_val_ge hpq u0 i₂ hg2
          · right; exact blowupV_val_ge hpq v0 i₂ hg2
        have hval : (f i₁).val = (f i₂).val := congrArg Fin.val heq
        apply Fin.ext
        rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2 <;> omega
      exact Finset.card_le_card_of_injOn f hmap hinj_f
    have hEmiss_sub : Emiss ∪ EdumUncov ⊆
        Finset.univ.filter (fun idx : Fin (q * e0) => blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S) := by
      intro idx hidx
      rcases Finset.mem_union.mp hidx with h1 | h2
      · obtain ⟨_, hlt, hu, hv⟩ := Finset.mem_filter.mp h1
        have hlt' : idx.val < (q - p) * e0 := hlt
        have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt'
        have hdiv : idx.val / e0 < q - p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm e0]; exact hlt')
        have hm1 : (idx.val / e0 + 1) * n0 ≤ r * n0 := Nat.mul_le_mul_right n0 hdiv
        have hmul_eq : (idx.val / e0) * n0 + n0 = (idx.val / e0 + 1) * n0 := by ring
        have hu_lt : (blowupU hpq u0 idx).val < r * n0 := by
          rw [blowupU_val_lt hpq u0 idx hlt' he0]
          have := (u0 ⟨idx.val % e0, Nat.mod_lt _ he0⟩).isLt; omega
        have hv_lt : (blowupV hpq v0 idx).val < r * n0 := by
          rw [blowupV_val_lt hpq v0 idx hlt' he0]
          have := (v0 ⟨idx.val % e0, Nat.mod_lt _ he0⟩).isLt; omega
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => hu (Finset.mem_filter.mpr ⟨h, hu_lt⟩),
          fun h => hv (Finset.mem_filter.mpr ⟨h, hv_lt⟩)⟩
      · obtain ⟨_, _, hu, hv⟩ := Finset.mem_filter.mp h2
        simp [hu, hv]
    have hdisj : Disjoint Emiss EdumUncov := by
      rw [Finset.disjoint_left]
      intro idx h1 h2
      have ha := (Finset.mem_filter.mp h1).2.1
      have hb := (Finset.mem_filter.mp h2).2.1
      omega
    have hEmiss_plus : Emiss.card + EdumUncov.card ≤ rv := by
      calc Emiss.card + EdumUncov.card = (Emiss ∪ EdumUncov).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ _ := Finset.card_le_card hEmiss_sub
        _ ≤ rv := hEout
    have hEmiss_le_Sdum : Emiss.card ≤ Sdum.card := by omega
    have hS_le_rc : S.card ≤ r * c := by
      have hrc : (q - p) * (e0 + c) = r * e0 + r * c := Nat.mul_add r e0 c
      omega
    let Srep : Finset (Fin (r * n0 + 2 * p * e0)) := Sorig ∪ Emiss.image (blowupU hpq u0)
    have hSrep_card : Srep.card ≤ r * c := by
      calc Srep.card ≤ Sorig.card + (Emiss.image (blowupU hpq u0)).card := Finset.card_union_le _ _
        _ ≤ Sorig.card + Emiss.card := Nat.add_le_add_left Finset.card_image_le _
        _ ≤ Sorig.card + Sdum.card := Nat.add_le_add_left hEmiss_le_Sdum _
        _ = S.card := hSsplit
        _ ≤ r * c := hS_le_rc
    let copySet : Fin r → Finset (Fin n0) := fun t =>
      Finset.univ.filter fun w : Fin n0 =>
        (⟨t.val * n0 + w.val, by
          have hm1 : (t.val + 1) * n0 ≤ r * n0 := Nat.mul_le_mul_right n0 t.isLt
          have : t.val * n0 + n0 = (t.val + 1) * n0 := by ring
          omega⟩ : Fin (r * n0 + 2 * p * e0)) ∈ Srep
    have hsum_copies : (∑ t : Fin r, (copySet t).card) ≤ Srep.card := by
      let emb : (t : Fin r) → Fin n0 → Fin (r * n0 + 2 * p * e0) := fun t w =>
        ⟨t.val * n0 + w.val, by
          have hm1 : (t.val + 1) * n0 ≤ r * n0 := Nat.mul_le_mul_right n0 t.isLt
          have : t.val * n0 + n0 = (t.val + 1) * n0 := by ring
          omega⟩
      have hbi_sub : (Finset.univ : Finset (Fin r)).biUnion (fun t => (copySet t).image (emb t)) ⊆ Srep := by
        intro x hx
        obtain ⟨t, _, hx'⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx'
        exact (Finset.mem_filter.mp hw).2
      have hdisj_t : Set.PairwiseDisjoint (Finset.univ : Finset (Fin r))
          (fun t => (copySet t).image (emb t)) := by
        intro t₁ _ t₂ _ hne
        show Disjoint ((copySet t₁).image (emb t₁)) ((copySet t₂).image (emb t₂))
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨w₁, _, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨w₂, _, heq⟩ := Finset.mem_image.mp hx2
        have hv : t₂.val * n0 + w₂.val = t₁.val * n0 + w₁.val := congrArg Fin.val heq
        have hn0 : 0 < n0 := Nat.lt_of_le_of_lt (Nat.zero_le _) w₁.isLt
        have hd := congrArg (· / n0) hv
        rw [Nat.mul_comm t₂.val n0, Nat.mul_comm t₁.val n0,
          Nat.mul_add_div hn0, Nat.mul_add_div hn0, Nat.div_eq_of_lt w₁.isLt,
          Nat.div_eq_of_lt w₂.isLt] at hd
        exact hne (Fin.ext (by omega))
      have hinj_emb : ∀ t : Fin r, Function.Injective (emb t) := by
        intro t w₁ w₂ heq
        apply Fin.ext
        have := congrArg Fin.val heq; dsimp [emb] at this; omega
      calc (∑ t : Fin r, (copySet t).card)
          = ∑ t : Fin r, ((copySet t).image (emb t)).card := by
              apply Finset.sum_congr rfl; intro t _
              exact (Finset.card_image_of_injective _ (hinj_emb t)).symm
        _ = ((Finset.univ : Finset (Fin r)).biUnion (fun t => (copySet t).image (emb t))).card :=
              (Finset.card_biUnion hdisj_t).symm
        _ ≤ Srep.card := Finset.card_le_card hbi_sub
    have hex_copy : ∃ t : Fin r, (copySet t).card ≤ c := by
      by_contra hall
      push Not at hall
      have hgt : r * (c + 1) ≤ ∑ t : Fin r, (copySet t).card := by
        calc r * (c + 1) = ∑ _t : Fin r, (c + 1) := by simp
          _ ≤ ∑ t : Fin r, (copySet t).card := Finset.sum_le_sum fun t _ => hall t
      have : r * (c + 1) = r * c + r := by ring
      omega
    obtain ⟨t, ht_card⟩ := hex_copy
    refine ⟨copySet t, ht_card, fun j => ?_⟩
    have hidx_lt : t.val * e0 + j.val < (q - p) * e0 := by
      have hm1 : (t.val + 1) * e0 ≤ r * e0 := Nat.mul_le_mul_right e0 t.isLt
      have : t.val * e0 + e0 = (t.val + 1) * e0 := by ring
      have := j.isLt; omega
    let idx : Fin (q * e0) := ⟨t.val * e0 + j.val, by omega⟩
    have he0 : 0 < e0 := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have hdiv : idx.val / e0 = t.val := by
      show (t.val * e0 + j.val) / e0 = t.val
      rw [Nat.mul_comm t.val e0, Nat.mul_add_div he0, Nat.div_eq_of_lt j.isLt, add_zero]
    have hmod : idx.val % e0 = j.val := by
      show (t.val * e0 + j.val) % e0 = j.val
      rw [Nat.mul_comm t.val e0, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
    have hfin_mod : (⟨idx.val % e0, Nat.mod_lt _ he0⟩ : Fin e0) = j := Fin.ext hmod
    have hu_eq : blowupU hpq u0 idx =
        ⟨t.val * n0 + (u0 j).val, by
          have hm1 : (t.val + 1) * n0 ≤ (q - p) * n0 := Nat.mul_le_mul_right n0 t.isLt
          have : t.val * n0 + n0 = (t.val + 1) * n0 := by ring
          have := (u0 j).isLt; omega⟩ := by
      apply Fin.ext
      rw [blowupU_val_lt hpq u0 idx hidx_lt he0, hdiv, hfin_mod]
    have hv_eq : blowupV hpq v0 idx =
        ⟨t.val * n0 + (v0 j).val, by
          have hm1 : (t.val + 1) * n0 ≤ (q - p) * n0 := Nat.mul_le_mul_right n0 t.isLt
          have : t.val * n0 + n0 = (t.val + 1) * n0 := by ring
          have := (v0 j).isLt; omega⟩ := by
      apply Fin.ext
      rw [blowupV_val_lt hpq v0 idx hidx_lt he0, hdiv, hfin_mod]
    by_cases h1 : blowupU hpq u0 idx ∈ Sorig
    · left; simp only [copySet, Finset.mem_filter, Finset.mem_univ, true_and, ← hu_eq]
      exact Finset.mem_union_left _ h1
    · by_cases h2 : blowupV hpq v0 idx ∈ Sorig
      · right; simp only [copySet, Finset.mem_filter, Finset.mem_univ, true_and, ← hv_eq]
        exact Finset.mem_union_left _ h2
      · left; simp only [copySet, Finset.mem_filter, Finset.mem_univ, true_and, ← hu_eq]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨idx,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hidx_lt, h1, h2⟩, rfl⟩)
  · rintro ⟨S0, hS0card, hS0cov⟩
    let emb : Fin r × Fin n0 → Fin (r * n0 + 2 * p * e0) := fun tw =>
      ⟨tw.1.val * n0 + tw.2.val, by
        have hm1 : (tw.1.val + 1) * n0 ≤ r * n0 := Nat.mul_le_mul_right n0 tw.1.isLt
        have : tw.1.val * n0 + n0 = (tw.1.val + 1) * n0 := by ring
        have := tw.2.isLt; omega⟩
    let S := ((Finset.univ : Finset (Fin r)) ×ˢ S0).image emb
    have hScard : S.card ≤ r * c := by
      calc S.card ≤ ((Finset.univ : Finset (Fin r)) ×ˢ S0).card := Finset.card_image_le
        _ = r * S0.card := by simp [Finset.card_product]
        _ ≤ r * c := Nat.mul_le_mul_left r hS0card
    have hcov : (Finset.univ.filter fun idx : Fin (q * e0) =>
        blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S).card ≤ p * e0 := by
      let allDum := (Finset.univ : Finset (Fin (q * e0))).filter fun idx => r * e0 ≤ idx.val
      have hsub : (Finset.univ.filter fun idx : Fin (q * e0) =>
          blowupU hpq u0 idx ∉ S ∧ blowupV hpq v0 idx ∉ S) ⊆ allDum := by
        intro idx hidx
        obtain ⟨_, hu, hv⟩ := Finset.mem_filter.mp hidx
        simp only [allDum, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hlt
        push Not at hlt
        have hlt' : idx.val < (q - p) * e0 := hlt
        have he0 : 0 < e0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt'
        let t : Fin r := ⟨idx.val / e0, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm e0]; exact hlt')⟩
        let j : Fin e0 := ⟨idx.val % e0, Nat.mod_lt _ he0⟩
        rcases hS0cov j with hju | hjv
        · apply hu
          refine Finset.mem_image.mpr ⟨(t, u0 j), Finset.mem_product.mpr ⟨Finset.mem_univ _, hju⟩, ?_⟩
          apply Fin.ext; rw [blowupU_val_lt hpq u0 idx hlt' he0]
        · apply hv
          refine Finset.mem_image.mpr ⟨(t, v0 j), Finset.mem_product.mpr ⟨Finset.mem_univ _, hjv⟩, ?_⟩
          apply Fin.ext; rw [blowupV_val_lt hpq v0 idx hlt' he0]
      calc _ ≤ allDum.card := Finset.card_le_card hsub
        _ = p * e0 := by
          rw [← Fintype.card_fin (p * e0), ← Fintype.card_coe]
          apply Fintype.card_of_bijective (f := fun idx : allDum =>
            (⟨idx.1.val - r * e0, by
              have := idx.1.isLt
              have hge := (Finset.mem_filter.mp idx.2).2
              omega⟩ : Fin (p * e0)))
          constructor
          · intro a b hab
            apply Subtype.ext; apply Fin.ext
            have ha := (Finset.mem_filter.mp a.2).2
            have hb := (Finset.mem_filter.mp b.2).2
            have := congrArg Fin.val hab; dsimp at this; omega
          · intro s
            refine ⟨⟨⟨r * e0 + s.val, by omega⟩, by simp [allDum]⟩, ?_⟩
            apply Fin.ext; simp
    have hbud : S.card + (q * e0 - p * e0) ≤ (q - p) * (e0 + c) := by
      have hrc : (q - p) * (e0 + c) = r * e0 + r * c := Nat.mul_add r e0 c
      omega
    exact graph_upper_bound (blowupU hpq u0) (blowupV hpq v0) (blowup_lt hpq u0 v0 huv)
      (by omega) S hcov hbud
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
lemma mem_occEdges (φ : CNF) (a b : Fin (occs φ).length) :
    (a, b) ∈ occEdges φ ↔ occEdge φ a b = true := by
  unfold occEdges
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨a', b', h⟩
    split_ifs at h with he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact he
  · intro he
    exact ⟨a, b, by simp [he]⟩
lemma occEdges_nodup (φ : CNF) : (occEdges φ).Nodup := by
  unfold occEdges
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · apply List.Nodup.filterMap (f := fun b => if occEdge φ a b then some (a, b) else none)
    · intro b₁ b₂ p h1 h2
      split_ifs at h1 h2
      · have h1' := Option.some.inj (Option.mem_def.mp h1)
        have h2' := Option.some.inj (Option.mem_def.mp h2)
        exact (Prod.mk.inj (h1'.trans h2'.symm)).2
      · simp at h2
      · simp at h1
      · simp at h1
    · exact List.nodup_finRange _
  · refine List.Pairwise.imp (fun {a₁ a₂} hne => ?_) (List.nodup_finRange _)
    intro p hp1 hp2
    simp only [List.mem_filterMap, List.mem_finRange, true_and] at hp1 hp2
    obtain ⟨b₁, hb1⟩ := hp1
    obtain ⟨b₂, hb2⟩ := hp2
    split_ifs at hb1 hb2
    have h1 := Option.some.inj hb1
    have h2 := Option.some.inj hb2
    have hpair : (a₁, b₁) = (a₂, b₂) := h1.trans h2.symm
    exact hne (Prod.mk.inj hpair).1
lemma occEdges_lt (φ : CNF) (e : Fin (occEdges φ).length) :
    ((occEdges φ).get e).1 < ((occEdges φ).get e).2 := by
  have hmem : (occEdges φ).get e ∈ occEdges φ := List.get_mem _ _
  rw [show (occEdges φ).get e = (((occEdges φ).get e).1, ((occEdges φ).get e).2) from rfl,
    mem_occEdges] at hmem
  unfold occEdge at hmem
  simp only [decide_eq_true_eq] at hmem
  exact hmem.1
lemma occEdges_inj (φ : CNF) :
    Function.Injective (fun e : Fin (occEdges φ).length =>
      (((occEdges φ).get e).1, ((occEdges φ).get e).2)) := by
  intro e₁ e₂ h
  have hget : (occEdges φ).get e₁ = (occEdges φ).get e₂ := Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact (List.nodup_iff_injective_get.mp (occEdges_nodup φ)) hget
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
theorem occGraph_vc_iff_sat (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    HasVC (fun e : Fin (occEdges φ).length => ((occEdges φ).get e).1)
          (fun e : Fin (occEdges φ).length => ((occEdges φ).get e).2)
          ((occs φ).length - φ.length) ↔
    Satisfiable φ := by
  classical
  constructor
  · rintro ⟨S, hScard, hScov⟩
    let I : Finset (Fin (occs φ).length) := Sᶜ
    have hIcard : φ.length ≤ I.card := by
      have hlen := occs_length_ge φ hne
      have hcompl : I.card = (occs φ).length - S.card := by
        rw [Finset.card_compl, Fintype.card_fin]
      have hSle : S.card ≤ (occs φ).length := by simpa using Finset.card_le_univ S
      omega
    have hindep : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
        ((occs φ).get a).1 ≠ ((occs φ).get b).1 ∧
        ¬ (((occs φ).get a).2.1 = ((occs φ).get b).2.1 ∧ ((occs φ).get a).2.2 ≠ ((occs φ).get b).2.2) := by
      intro a ha b hb hne_ab
      have hno : ∀ x ∈ I, ∀ y ∈ I, occEdge φ x y = false := by
        intro x hx y hy
        by_contra htrue
        have htr : occEdge φ x y = true := by cases h : occEdge φ x y <;> simp_all
        have hmem : (x, y) ∈ occEdges φ := (mem_occEdges φ x y).mpr htr
        obtain ⟨e, he⟩ := List.mem_iff_get.mp hmem
        have hcov := hScov e
        dsimp only at hcov
        rw [he] at hcov
        rcases hcov with hxS | hyS
        · exact (Finset.mem_compl.mp hx) hxS
        · exact (Finset.mem_compl.mp hy) hyS
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_ab) with hlt | hgt
      · have hf := hno a ha b hb
        unfold occEdge at hf
        simp only [decide_eq_false_iff_not, not_and, not_or] at hf
        have h' := hf hlt
        exact ⟨h'.1, fun ⟨h1, h2⟩ => h'.2 h1 h2⟩
      · have hf := hno b hb a ha
        unfold occEdge at hf
        simp only [decide_eq_false_iff_not, not_and, not_or] at hf
        have h' := hf hgt
        exact ⟨Ne.symm h'.1, fun ⟨h1, h2⟩ => h'.2 h1.symm h2.symm⟩
    let cIdx : Fin (occs φ).length → Fin φ.length := fun a =>
      ⟨((occs φ).get a).1, by
        have h := occsAux_mem_clause_lt 0 φ ((occs φ).get a) (List.get_mem _ _)
        omega⟩
    have hinj_c : Set.InjOn cIdx I := by
      intro a ha b hb heq
      by_contra hne_ab
      exact (hindep a ha b hb hne_ab).1 (congrArg Fin.val heq)
    have himg_card : (I.image cIdx).card = φ.length := by
      have h1 : (I.image cIdx).card = I.card := Finset.card_image_of_injOn hinj_c
      have h2 : (I.image cIdx).card ≤ φ.length := by
        simpa using Finset.card_le_univ (I.image cIdx)
      omega
    have himg_univ : I.image cIdx = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using himg_card)
    let σ : Assignment := fun v =>
      decide (∃ a ∈ I, ((occs φ).get a).2 = (v, true))
    refine ⟨σ, ?_⟩
    rw [CNF.eval, List.all_eq_true]
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    have hmem_u : (⟨i, hi⟩ : Fin φ.length) ∈ I.image cIdx := by rw [himg_univ]; simp
    obtain ⟨a, haI, haIdx⟩ := Finset.mem_image.mp hmem_u
    have ha1 : ((occs φ).get a).1 = i := congrArg Fin.val haIdx
    have hmem_occ : (i, ((occs φ).get a).2) ∈ occsAux 0 φ := by
      rw [← ha1]; exact List.get_mem _ _
    obtain ⟨_, _, hl_mem⟩ := occsAux_mem_getElem 0 φ i ((occs φ).get a).2 hmem_occ
    rw [Clause.eval, List.any_eq_true]
    refine ⟨((occs φ).get a).2, by simpa using hl_mem, ?_⟩
    unfold Literal.eval
    cases hpol : ((occs φ).get a).2.2
    · simp only [beq_iff_eq, σ, decide_eq_false_iff_not]
      rintro ⟨b, hbI, hb_eq⟩
      by_cases hab : a = b
      · subst hab; rw [hb_eq] at hpol; simp at hpol
      · have hc2 := (hindep a haI b hbI hab).2
        apply hc2
        refine ⟨?_, ?_⟩
        · rw [hb_eq]
        · rw [hb_eq, hpol]; simp
    · simp only [beq_iff_eq, σ, decide_eq_true_eq]
      exact ⟨a, haI, Prod.ext rfl hpol⟩
  · rintro ⟨σ, hσ⟩
    rw [CNF.eval, List.all_eq_true] at hσ
    have hpick : ∀ i : Fin φ.length, ∃ a : Fin (occs φ).length,
        ((occs φ).get a).1 = i.val ∧ Literal.eval σ ((occs φ).get a).2 = true := by
      intro i
      have hcl := hσ φ[i.val] (List.getElem_mem i.isLt)
      rw [Clause.eval, List.any_eq_true] at hcl
      obtain ⟨l, hl_mem, hl_eval⟩ := hcl
      have hocc : (i.val, l) ∈ occs φ := by
        simpa [occs] using occsAux_exists_clause 0 φ i.val i.isLt l hl_mem
      obtain ⟨a, ha⟩ := List.mem_iff_get.mp hocc
      exact ⟨a, by rw [ha], by rw [ha]; exact hl_eval⟩
    choose pick hpick_c hpick_ev using hpick
    have hinj_pick : Function.Injective pick := by
      intro i j h
      apply Fin.ext
      have := congrArg (fun a => ((occs φ).get a).1) h
      rw [hpick_c i, hpick_c j] at this
      exact this
    let I : Finset (Fin (occs φ).length) := Finset.univ.image pick
    have hIcard : I.card = φ.length := by
      rw [Finset.card_image_of_injective _ hinj_pick, Finset.card_fin]
    let S : Finset (Fin (occs φ).length) := Iᶜ
    have hScard : S.card ≤ (occs φ).length - φ.length := by
      rw [Finset.card_compl, Fintype.card_fin, hIcard]
    refine ⟨S, hScard, fun e => ?_⟩
    by_contra hboth
    push Not at hboth
    obtain ⟨hu, hv⟩ := hboth
    have huI : ((occEdges φ).get e).1 ∈ I := by simpa [S] using hu
    have hvI : ((occEdges φ).get e).2 ∈ I := by simpa [S] using hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp huI
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvI
    have hmem : (occEdges φ).get e ∈ occEdges φ := List.get_mem _ _
    rw [show (occEdges φ).get e = (((occEdges φ).get e).1, ((occEdges φ).get e).2) from rfl,
      mem_occEdges] at hmem
    unfold occEdge at hmem
    simp only [decide_eq_true_eq] at hmem
    obtain ⟨hlt, hsame | ⟨hvar, hpol⟩⟩ := hmem
    · rw [← hi, ← hj, hpick_c i, hpick_c j] at hsame
      have hij : i = j := Fin.ext hsame
      subst hij
      rw [← hi, ← hj] at hlt
      exact lt_irrefl _ hlt
    · have he1 := hpick_ev i
      have he2 := hpick_ev j
      rw [hi] at he1; rw [hj] at he2
      unfold Literal.eval at he1 he2
      simp only [beq_iff_eq] at he1 he2
      rw [hvar] at he1
      exact hpol (he1.symm.trans he2)
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
lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide
lemma b2f_parityRun_flatMap {N : ℕ} (f : Fin N → Bool) :
    b2f (parityRun false ((List.range N).flatMap fun i =>
      if h : i < N then bflag (f ⟨i, h⟩) else [])) =
    Finset.univ.sum fun i : Fin N => b2f (f i) := by
  induction N with
  | zero => simp [parityRun, b2f]
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, parityRun_append,
      Fin.sum_univ_castSucc]
    have hpref : ((List.range N).flatMap fun i =>
        if h : i < N + 1 then bflag (f ⟨i, h⟩) else []) =
        ((List.range N).flatMap fun i =>
          if h : i < N then bflag (f (Fin.castSucc ⟨i, h⟩)) else []) := by
      apply List.flatMap_congr
      intro i hi
      have hlt : i < N := List.mem_range.mp hi
      simp [hlt, Nat.lt_succ_of_lt hlt]
    rw [hpref, parityRun_xor, b2f_xor, ih (fun i => f i.castSucc)]
    have hlast : b2f (parityRun false
        (if h : N < N + 1 then bflag (f ⟨N, h⟩) else [])) =
        b2f (f (Fin.last N)) := by
      simp only [Nat.lt_succ_self, ↓reduceDIte]
      change b2f (parityRun false (bflag (f (Fin.last N)))) =
        b2f (f (Fin.last N))
      cases f (Fin.last N) <;> rfl
    rw [hlast]
lemma flatMap_range_eq_nil_iff (N : ℕ) (f : ℕ → List Bool) :
    ((List.range N).flatMap f = []) ↔ ∀ i < N, f i = [] := by
  simp only [List.flatMap_eq_nil_iff, List.mem_range]
def flat2 (a b : ℕ) (M : Fin a → Fin b → Bool) : List Bool :=
  (List.finRange a).flatMap fun i => (List.finRange b).map fun j => M i j
def flat3 (m n : ℕ) (A : Fin m → Fin n → Fin n → Bool) : List Bool :=
  (List.finRange m).flatMap fun e => (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => A e i j
def unflat2 (a b : ℕ) (bits : List Bool) (i : Fin a) (j : Fin b) : Bool :=
  bits.getD (i.val * b + j.val) false
def unflat3 (m n : ℕ) (bits : List Bool) (e : Fin m) (i j : Fin n) : Bool :=
  bits.getD (e.val * (n * n) + i.val * n + j.val) false
lemma flat2_length (a b : ℕ) (M : Fin a → Fin b → Bool) : (flat2 a b M).length = a * b :=
  finRange_flatMap_length a _ b (fun _ => by simp)
lemma flat3_length (m n : ℕ) (A : Fin m → Fin n → Fin n → Bool) :
    (flat3 m n A).length = m * (n * n) :=
  finRange_flatMap_length m _ (n * n) (fun _ => finRange_flatMap_length n _ n (fun _ => by simp))
lemma getD_finRange_flatMap {a L : ℕ} (f : Fin a → List Bool) (hf : ∀ i, (f i).length = L)
    (i : Fin a) (k : ℕ) (hk : k < L) :
    ((List.finRange a).flatMap f).getD (i.val * L + k) false = (f i).getD k false := by
  have hgen : ∀ (l : List (Fin a)) (idx : ℕ) (hidx : idx < l.length),
      (l.flatMap f).getD (idx * L + k) false = (f l[idx]).getD k false := by
    intro l
    induction l with
    | nil => intro idx hidx; simp at hidx
    | cons x xs ih =>
      intro idx hidx
      cases idx with
      | zero =>
        simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
        have hlt : k < (f x).length := by rw [hf x]; exact hk
        rw [List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le hlt (by simp)),
          List.getElem_append_left hlt, List.getD_eq_getElem _ _ hlt]
      | succ idx' =>
        simp only [List.flatMap_cons, List.getElem_cons_succ]
        have hlen : (f x).length = L := hf x
        have hge : (f x).length ≤ (idx' + 1) * L + k := by
          rw [hlen, Nat.succ_mul]; omega
        have hsub : (idx' + 1) * L + k - (f x).length = idx' * L + k := by
          rw [hlen, Nat.succ_mul]; omega
        by_cases hlt : (idx' + 1) * L + k < (f x ++ xs.flatMap f).length
        · have hlt' : idx' * L + k < (xs.flatMap f).length := by
            simp only [List.length_append] at hlt; omega
          rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right hge]
          have heq : (xs.flatMap f)[(idx' + 1) * L + k - (f x).length]'(by
              simp only [List.length_append] at hlt; omega) =
              (xs.flatMap f)[idx' * L + k]'hlt' := by congr 1
          rw [heq, ← List.getD_eq_getElem _ _ hlt']
          exact ih idx' (by simpa using hidx)
        · exfalso
          have hxslen : (xs.flatMap f).length = xs.length * L := by
            rw [List.length_flatMap]
            have : (xs.map fun y => (f y).length) = List.replicate xs.length L := by
              apply List.ext_getElem
              · simp
              · intro j h1 h2; simp [hf]
            rw [this, List.sum_replicate, smul_eq_mul]
          have hidx' : idx' < xs.length := by simpa using hidx
          have hm1 : (idx' + 1) * L ≤ xs.length * L := Nat.mul_le_mul_right L hidx'
          have : idx' * L + L = (idx' + 1) * L := by ring
          simp only [List.length_append, hlen, hxslen] at hlt
          omega
  have h1 := hgen (List.finRange a) i.val (by simp)
  simpa using h1
lemma flat2_getD {a b : ℕ} (M : Fin a → Fin b → Bool) (i : Fin a) (j : Fin b) :
    (flat2 a b M).getD (i.val * b + j.val) false = M i j := by
  unfold flat2
  rw [getD_finRange_flatMap _ (fun _ => by simp) i j.val j.isLt]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp
lemma flat3_getD {m n : ℕ} (A : Fin m → Fin n → Fin n → Bool) (e : Fin m) (i j : Fin n) :
    (flat3 m n A).getD (e.val * (n * n) + i.val * n + j.val) false = A e i j := by
  unfold flat3
  have hlt : i.val * n + j.val < n * n := by
    have hm1 : (i.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n i.isLt
    have : i.val * n + n = (i.val + 1) * n := by ring
    have := j.isLt; omega
  rw [Nat.add_assoc, getD_finRange_flatMap _ (fun _ => finRange_flatMap_length n _ n (fun _ => by simp))
    e (i.val * n + j.val) hlt]
  exact flat2_getD (A e) i j
lemma flat3_unflat3 {m n : ℕ} (bits : List Bool) (hlen : bits.length = m * (n * n)) :
    flat3 m n (unflat3 m n bits) = bits := by
  apply List.ext_getElem
  · rw [flat3_length, hlen]
  · intro idx h1 h2
    have hnm : idx < m * (n * n) := by omega
    have hnn_pos : 0 < n * n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hnm
    have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hnn_pos
    let e : Fin m := ⟨idx / (n * n), Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (n * n)]; exact hnm)⟩
    let rem := idx % (n * n)
    have hrem : rem < n * n := Nat.mod_lt _ hnn_pos
    let i : Fin n := ⟨rem / n, Nat.div_lt_of_lt_mul hrem⟩
    let j : Fin n := ⟨rem % n, Nat.mod_lt _ hn_pos⟩
    have hidx_eq : e.val * (n * n) + i.val * n + j.val = idx := by
      have h1' : (n * n) * (idx / (n * n)) + idx % (n * n) = idx := Nat.div_add_mod idx (n * n)
      have h2' : n * (rem / n) + rem % n = rem := Nat.div_add_mod rem n
      have hm1 : (idx / (n * n)) * (n * n) = (n * n) * (idx / (n * n)) := Nat.mul_comm _ _
      have hm2 : (rem / n) * n = n * (rem / n) := Nat.mul_comm _ _
      change (idx / (n * n)) * (n * n) + (rem / n) * n + rem % n = idx
      omega
    have hget := flat3_getD (unflat3 m n bits) e i j
    rw [hidx_eq] at hget
    rw [List.getD_eq_getElem _ _ h1] at hget
    rw [hget]
    unfold unflat3
    rw [hidx_eq, List.getD_eq_getElem _ _ h2]
def matIdTerm (y : List Bool) : List Bool :=
  let ui := (unpairB y).1
  let rest := (unpairB y).2
  let uβ := (unpairB rest).1
  let r1 := (unpairB rest).2
  let uα := (unpairB r1).1
  let r2 := (unpairB r1).2
  let uR := (unpairB r2).1
  let r3 := (unpairB r2).2
  let uC := (unpairB r3).1
  let r4 := (unpairB r3).2
  let bits1 := (unpairB r4).1
  let bits2 := (unpairB r4).2
  andF
    (getBit (mulU uα uC ++ ui) bits1)
    (getBit (mulU ui uR ++ uβ) bits2)
lemma cpt_matIdTerm : CPTs matIdTerm := by
  have hui := cpt_unpairB1
  have hrest := cpt_unpairB2
  have huβ := cpt_unpairB1_1 hrest
  have hr1 := cpt_unpairB2_1 hrest
  have huα := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have huR := cpt_unpairB1_1 hr2
  have hr3 := cpt_unpairB2_1 hr2
  have huC := cpt_unpairB1_1 hr3
  have hr4 := cpt_unpairB2_1 hr3
  have hb1 := cpt_unpairB1_1 hr4
  have hb2 := cpt_unpairB2_1 hr4
  exact cpt_andF
    (cpt_getBit (cpt_app2 (cpt_mulU2 huα huC) hui) hb1)
    (cpt_getBit (cpt_app2 (cpt_mulU2 hui huR) huβ) hb2)
def matIdEntry (y : List Bool) : List Bool :=
  let uβ := (unpairB y).1
  let r1 := (unpairB y).2
  let uα := (unpairB r1).1
  let r2 := (unpairB r1).2
  let r3 := (unpairB r2).2
  let uC := (unpairB r3).1
  let dot := parityF ((List.range uC.length).flatMap fun i =>
    matIdTerm (pairB (un i) y))
  xorF dot (eqF uα uβ)
lemma cpt_matIdEntry : CPTs matIdEntry := by
  have huβ := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huα := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hr3 := cpt_unpairB2_1 hr2
  have huC := cpt_unpairB1_1 hr3
  have hdot := cpt_parityF1
    (cpt_flatMapRange cpt_matIdTerm huC
      cpt_id)
  exact cpt_xorF hdot (cpt_eqF' huα huβ)
def matIdRow (y : List Bool) : List Bool :=
  let r2 := (unpairB y).2
  let uR := (unpairB r2).1
  (List.range uR.length).flatMap fun β =>
    matIdEntry (pairB (un β) y)
lemma cpt_matIdRow : CPTs matIdRow :=
  cpt_flatMapRange cpt_matIdEntry
    (cpt_unpairB1_1 cpt_unpairB2)
    cpt_id
def checkMatId (y : List Bool) : List Bool :=
  let uR := (unpairB y).1
  notF ((List.range uR.length).flatMap fun α =>
    matIdRow (pairB (un α) y))
lemma cpt_checkMatId : CPTs checkMatId :=
  cpt_notF (cpt_flatMapRange cpt_matIdRow
    cpt_unpairB1 cpt_id)
lemma checkMatId_spec (R C : ℕ) (bits1 bits2 : List Bool) :
    checkMatId (pairB (un R)
      (pairB (un C)
        (pairB bits1 bits2))) = [true] ↔
    ∀ α β : Fin R, (Finset.univ.sum fun i : Fin C =>
      b2f (unflat2 R C bits1 α i && unflat2 C R bits2 i β)) = if α = β then 1 else 0 := by
  unfold checkMatId notF sel
  simp only [unpairB_pairB, un_length]
  split_ifs with h
  · simp only [true_iff]
    rw [flatMap_range_eq_nil_iff] at h
    intro α β
    have hα := h α.val α.isLt
    unfold matIdRow at hα
    simp only [unpairB_pairB, un_length] at hα
    rw [flatMap_range_eq_nil_iff] at hα
    have hβ := hα β.val β.isLt
    unfold matIdEntry at hβ
    simp only [unpairB_pairB, un_length] at hβ
    have hterm : ((List.range C).flatMap fun i =>
        matIdTerm (pairB (un i)
          (pairB (un β.val)
            (pairB (un α.val)
              (pairB (un R)
                (pairB (un C)
                  (pairB bits1 bits2))))))) =
        ((List.range C).flatMap fun i =>
          if hi : i < C then bflag
            (unflat2 R C bits1 α ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ β) else []) := by
      apply List.flatMap_congr
      intro i hi
      have hlt : i < C := List.mem_range.mp hi
      simp only [matIdTerm, unpairB_pairB, getBit_eq,
        List.length_append, mulU, un_length,
        andF_bflag, hlt, ↓reduceDIte, unflat2]
    rw [hterm] at hβ
    have heq_ab : eqF (un α.val) (un β.val) =
        bflag (decide (α = β)) := by
      unfold eqF; congr 1; simp only [decide_eq_decide]
      exact ⟨fun he => Fin.ext (un_inj he), fun he => by rw [he]⟩
    rw [heq_ab] at hβ
    unfold parityF at hβ
    rw [xorF_bflag] at hβ
    have hxor_false : xor (parityRun false ((List.range C).flatMap fun i =>
        if hi : i < C then bflag
          (unflat2 R C bits1 α ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ β) else []))
        (decide (α = β)) = false := by
      revert hβ
      cases xor (parityRun false ((List.range C).flatMap fun i =>
        if hi : i < C then bflag
          (unflat2 R C bits1 α ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ β) else []))
        (decide (α = β)) <;> simp [bflag]
    have hpar_eq : parityRun false ((List.range C).flatMap fun i =>
        if hi : i < C then bflag
          (unflat2 R C bits1 α ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ β) else []) =
        decide (α = β) := by
      revert hxor_false
      cases parityRun false ((List.range C).flatMap fun i =>
        if hi : i < C then bflag
          (unflat2 R C bits1 α ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ β) else []) <;>
        cases decide (α = β) <;> simp
    rw [← b2f_parityRun_flatMap, hpar_eq]
    by_cases hab : α = β <;> simp [hab, b2f]
  · simp only [false_iff]
    intro hall
    apply h
    rw [flatMap_range_eq_nil_iff]
    intro α hα
    unfold matIdRow
    simp only [unpairB_pairB, un_length]
    rw [flatMap_range_eq_nil_iff]
    intro β hβ
    unfold matIdEntry
    simp only [unpairB_pairB, un_length]
    have hterm : ((List.range C).flatMap fun i =>
        matIdTerm (pairB (un i)
          (pairB (un β)
            (pairB (un α)
              (pairB (un R)
                (pairB (un C)
                  (pairB bits1 bits2))))))) =
        ((List.range C).flatMap fun i =>
          if hi : i < C then bflag
            (unflat2 R C bits1 ⟨α, hα⟩ ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ ⟨β, hβ⟩) else []) := by
      apply List.flatMap_congr
      intro i hi
      have hlt : i < C := List.mem_range.mp hi
      simp only [matIdTerm, unpairB_pairB, getBit_eq,
        List.length_append, mulU, un_length,
        andF_bflag, hlt, ↓reduceDIte, unflat2]
    rw [hterm]
    have hsum := hall ⟨α, hα⟩ ⟨β, hβ⟩
    rw [← b2f_parityRun_flatMap] at hsum
    have hpar : parityRun false ((List.range C).flatMap fun i =>
        if hi : i < C then bflag
          (unflat2 R C bits1 ⟨α, hα⟩ ⟨i, hi⟩ && unflat2 C R bits2 ⟨i, hi⟩ ⟨β, hβ⟩) else []) =
        decide (α = β) := by
      by_cases hab : α = β
      · subst hab
        simp only [↓reduceIte, decide_true] at hsum ⊢
        cases h1 : parityRun false _ <;> simp_all [b2f]
      · have hne : (⟨α, hα⟩ : Fin R) ≠ ⟨β, hβ⟩ := fun he => hab (congrArg Fin.val he)
        simp only [hne, ↓reduceIte, hab, decide_false] at hsum ⊢
        cases h1 : parityRun false _ <;> simp_all [b2f]
    have heq_ab : eqF (un α) (un β) =
        bflag (decide (α = β)) := by
      unfold eqF; congr 1; simp only [decide_eq_decide]
      exact ⟨un_inj, fun he => by rw [he]⟩
    unfold parityF
    rw [hpar, heq_ab, xorF_bflag]
    cases decide (α = β) <;> rfl
def bilJ (y : List Bool) : List Bool :=
  let uJ := (unpairB y).1
  let s1 := (unpairB y).2
  let uI := (unpairB s1).1
  let s2 := (unpairB s1).2
  let uE := (unpairB s2).1
  let s3 := (unpairB s2).2
  let uβ := (unpairB s3).1
  let s4 := (unpairB s3).2
  let uα := (unpairB s4).1
  let s5 := (unpairB s4).2
  let uR := (unpairB s5).1
  let env := (unpairB s5).2
  let uN := (unpairB env).1
  let e1 := (unpairB env).2
  let uM := (unpairB e1).1
  let e2 := (unpairB e1).2
  let e3 := (unpairB e2).2
  let e4 := (unpairB e3).2
  let bitsA := (unpairB e4).1
  let e5 := (unpairB e4).2
  let bitsU := (unpairB e5).1
  let bitsW := (unpairB e5).2
  let uNN := mulU uN uN
  let idxE := mulU uE uNN
  let aij := getBit (idxE ++ mulU uI uN ++ uJ) bitsA
  let aji := getBit (idxE ++ mulU uJ uN ++ uI) bitsA
  let wre := getBit (mulU uR uM ++ uE) bitsW
  let uai := getBit (mulU uα uN ++ uI) bitsU
  let ubj := getBit (mulU uβ uN ++ uJ) bitsU
  andF (andF (andF wre (xorF aij aji)) uai) ubj
lemma cpt_bilJ : CPTs bilJ := by
  have huJ := cpt_unpairB1
  have hs1 := cpt_unpairB2
  have huI := cpt_unpairB1_1 hs1
  have hs2 := cpt_unpairB2_1 hs1
  have huE := cpt_unpairB1_1 hs2
  have hs3 := cpt_unpairB2_1 hs2
  have huβ := cpt_unpairB1_1 hs3
  have hs4 := cpt_unpairB2_1 hs3
  have huα := cpt_unpairB1_1 hs4
  have hs5 := cpt_unpairB2_1 hs4
  have huR := cpt_unpairB1_1 hs5
  have henv := cpt_unpairB2_1 hs5
  have huN := cpt_unpairB1_1 henv
  have he1 := cpt_unpairB2_1 henv
  have huM := cpt_unpairB1_1 he1
  have he2 := cpt_unpairB2_1 he1
  have he3 := cpt_unpairB2_1 he2
  have he4 := cpt_unpairB2_1 he3
  have hbA := cpt_unpairB1_1 he4
  have he5 := cpt_unpairB2_1 he4
  have hbU := cpt_unpairB1_1 he5
  have hbW := cpt_unpairB2_1 he5
  have huNN := cpt_mulU2 huN huN
  have hidxE := cpt_mulU2 huE huNN
  have haij := cpt_getBit (cpt_app2
    (cpt_app2 hidxE (cpt_mulU2 huI huN)) huJ) hbA
  have haji := cpt_getBit (cpt_app2
    (cpt_app2 hidxE (cpt_mulU2 huJ huN)) huI) hbA
  have hwre := cpt_getBit (cpt_app2
    (cpt_mulU2 huR huM) huE) hbW
  have huai := cpt_getBit (cpt_app2
    (cpt_mulU2 huα huN) huI) hbU
  have hubj := cpt_getBit (cpt_app2
    (cpt_mulU2 huβ huN) huJ) hbU
  exact cpt_andF (cpt_andF (cpt_andF hwre (cpt_xorF haij haji)) huai) hubj
def bilI (y : List Bool) : List Bool :=
  let s2 := (unpairB y).2
  let s3 := (unpairB s2).2
  let s4 := (unpairB s3).2
  let s5 := (unpairB s4).2
  let env := (unpairB s5).2
  let uN := (unpairB env).1
  (List.range uN.length).flatMap fun j =>
    bilJ (pairB (un j) y)
lemma cpt_bilI : CPTs bilI := by
  have hs2 := cpt_unpairB2
  have hs3 := cpt_unpairB2_1 hs2
  have hs4 := cpt_unpairB2_1 hs3
  have hs5 := cpt_unpairB2_1 hs4
  have henv := cpt_unpairB2_1 hs5
  have huN := cpt_unpairB1_1 henv
  exact cpt_flatMapRange cpt_bilJ huN
    cpt_id
def bilE (y : List Bool) : List Bool :=
  let s3 := (unpairB y).2
  let s4 := (unpairB s3).2
  let s5 := (unpairB s4).2
  let env := (unpairB s5).2
  let uN := (unpairB env).1
  (List.range uN.length).flatMap fun i =>
    bilI (pairB (un i) y)
lemma cpt_bilE : CPTs bilE := by
  have hs3 := cpt_unpairB2
  have hs4 := cpt_unpairB2_1 hs3
  have hs5 := cpt_unpairB2_1 hs4
  have henv := cpt_unpairB2_1 hs5
  have huN := cpt_unpairB1_1 henv
  exact cpt_flatMapRange cpt_bilI huN
    cpt_id
def bilBeta (y : List Bool) : List Bool :=
  let s4 := (unpairB y).2
  let s5 := (unpairB s4).2
  let env := (unpairB s5).2
  let e1 := (unpairB env).2
  let uM := (unpairB e1).1
  parityF ((List.range uM.length).flatMap fun e =>
    bilE (pairB (un e) y))
lemma cpt_bilBeta : CPTs bilBeta := by
  have hs4 := cpt_unpairB2
  have hs5 := cpt_unpairB2_1 hs4
  have henv := cpt_unpairB2_1 hs5
  have he1 := cpt_unpairB2_1 henv
  have huM := cpt_unpairB1_1 he1
  exact cpt_parityF1 (cpt_flatMapRange cpt_bilE huM
    cpt_id)
def bilAlpha (y : List Bool) : List Bool :=
  let s5 := (unpairB y).2
  let env := (unpairB s5).2
  let e1 := (unpairB env).2
  let e2 := (unpairB e1).2
  let uA := (unpairB e2).1
  (List.range uA.length).flatMap fun β =>
    bilBeta (pairB (un β) y)
lemma cpt_bilAlpha : CPTs bilAlpha := by
  have hs5 := cpt_unpairB2
  have henv := cpt_unpairB2_1 hs5
  have he1 := cpt_unpairB2_1 henv
  have he2 := cpt_unpairB2_1 he1
  have huA := cpt_unpairB1_1 he2
  exact cpt_flatMapRange cpt_bilBeta huA
    cpt_id
def bilR (y : List Bool) : List Bool :=
  let env := (unpairB y).2
  let e1 := (unpairB env).2
  let e2 := (unpairB e1).2
  let uA := (unpairB e2).1
  (List.range uA.length).flatMap fun α =>
    bilAlpha (pairB (un α) y)
lemma cpt_bilR : CPTs bilR := by
  have henv := cpt_unpairB2
  have he1 := cpt_unpairB2_1 henv
  have he2 := cpt_unpairB2_1 he1
  have huA := cpt_unpairB1_1 he2
  exact cpt_flatMapRange cpt_bilAlpha huA
    cpt_id
def checkBilin (env : List Bool) : List Bool :=
  let e1 := (unpairB env).2
  let e2 := (unpairB e1).2
  let e3 := (unpairB e2).2
  let uT := (unpairB e3).1
  notF ((List.range uT.length).flatMap fun r =>
    bilR (pairB (un r) env))
lemma cpt_checkBilin : CPTs checkBilin := by
  have he1 := cpt_unpairB2
  have he2 := cpt_unpairB2_1 he1
  have he3 := cpt_unpairB2_1 he2
  have huT := cpt_unpairB1_1 he3
  exact cpt_notF (cpt_flatMapRange cpt_bilR huT
    cpt_id)
lemma b2f_parityRun_flatMap_nested {N : ℕ} (g : Fin N → List Bool) :
    b2f (parityRun false ((List.range N).flatMap fun i =>
      if h : i < N then g ⟨i, h⟩ else [])) =
    Finset.univ.sum fun i : Fin N => b2f (parityRun false (g i)) := by
  induction N with
  | zero => simp [parityRun, b2f]
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, parityRun_append,
      Fin.sum_univ_castSucc]
    have hpref : ((List.range N).flatMap fun i => if h : i < N + 1 then g ⟨i, h⟩ else []) =
        ((List.range N).flatMap fun i =>
          if h : i < N then g (Fin.castSucc ⟨i, h⟩) else []) := by
      apply List.flatMap_congr; intro i hi
      have hlt : i < N := List.mem_range.mp hi
      simp [hlt, Nat.lt_succ_of_lt hlt]
    rw [hpref, parityRun_xor, b2f_xor, ih (fun i => g i.castSucc)]
    simp [Fin.last]
lemma checkBilin_spec (n m a t : ℕ) (bitsA bitsU bitsW : List Bool) :
    checkBilin (pairB (un n)
      (pairB (un m)
        (pairB (un a)
          (pairB (un t)
            (pairB bitsA
              (pairB bitsU bitsW)))))) = [true] ↔
    ∀ (r : Fin t) (α β : Fin a),
      (Finset.univ.sum fun e : Fin m => Finset.univ.sum fun i : Fin n => Finset.univ.sum fun j : Fin n =>
        b2f (unflat2 t m bitsW r e &&
          xor (unflat3 m n bitsA e i j) (unflat3 m n bitsA e j i) &&
          unflat2 a n bitsU α i && unflat2 a n bitsU β j)) = 0 := by
  let env := pairB (un n)
      (pairB (un m)
        (pairB (un a)
          (pairB (un t)
            (pairB bitsA
              (pairB bitsU bitsW)))))
  have htriple : ∀ (r : Fin t) (α β : Fin a),
      b2f (parityRun false ((List.range m).flatMap fun e =>
        bilE (pairB (un e)
          (pairB (un β.val)
            (pairB (un α.val)
              (pairB (un r.val) env)))))) =
      Finset.univ.sum fun e : Fin m => Finset.univ.sum fun i : Fin n => Finset.univ.sum fun j : Fin n =>
        b2f (unflat2 t m bitsW r e &&
          xor (unflat3 m n bitsA e i j) (unflat3 m n bitsA e j i) &&
          unflat2 a n bitsU α i && unflat2 a n bitsU β j) := by
    intro r α β
    have h1 : ((List.range m).flatMap fun e =>
        bilE (pairB (un e)
          (pairB (un β.val)
            (pairB (un α.val)
              (pairB (un r.val) env))))) =
        ((List.range m).flatMap fun e => if he : e < m then
          (List.range n).flatMap fun i => if hi : i < n then
            (List.range n).flatMap fun j => if hj : j < n then
              bflag
                (unflat2 t m bitsW r ⟨e, he⟩ &&
                  xor (unflat3 m n bitsA ⟨e, he⟩ ⟨i, hi⟩ ⟨j, hj⟩)
                      (unflat3 m n bitsA ⟨e, he⟩ ⟨j, hj⟩ ⟨i, hi⟩) &&
                  unflat2 a n bitsU α ⟨i, hi⟩ && unflat2 a n bitsU β ⟨j, hj⟩)
            else []
          else []
        else []) := by
      apply List.flatMap_congr; intro e he
      have he' : e < m := List.mem_range.mp he
      simp only [he', ↓reduceDIte, bilE, unpairB_pairB,
        un_length, env]
      apply List.flatMap_congr; intro i hi
      have hi' : i < n := List.mem_range.mp hi
      simp only [hi', ↓reduceDIte, bilI, unpairB_pairB,
        un_length]
      apply List.flatMap_congr; intro j hj
      have hj' : j < n := List.mem_range.mp hj
      simp only [hj', ↓reduceDIte, bilJ, unpairB_pairB, getBit_eq,
        List.length_append, mulU, un_length,
        andF_bflag, xorF_bflag, unflat2, unflat3]
    rw [h1]
    refine Eq.trans (b2f_parityRun_flatMap_nested (N := m) (fun e =>
      (List.range n).flatMap fun i => if hi : i < n then
        (List.range n).flatMap fun j => if hj : j < n then
          bflag
            (unflat2 t m bitsW r e &&
              xor (unflat3 m n bitsA e ⟨i, hi⟩ ⟨j, hj⟩)
                  (unflat3 m n bitsA e ⟨j, hj⟩ ⟨i, hi⟩) &&
              unflat2 a n bitsU α ⟨i, hi⟩ && unflat2 a n bitsU β ⟨j, hj⟩)
        else []
      else [])) ?_
    apply Finset.sum_congr rfl; intro e _
    refine Eq.trans (b2f_parityRun_flatMap_nested (N := n) (fun i =>
      (List.range n).flatMap fun j => if hj : j < n then
        bflag
          (unflat2 t m bitsW r e &&
            xor (unflat3 m n bitsA e i ⟨j, hj⟩)
                (unflat3 m n bitsA e ⟨j, hj⟩ i) &&
            unflat2 a n bitsU α i && unflat2 a n bitsU β ⟨j, hj⟩)
      else [])) ?_
    apply Finset.sum_congr rfl; intro i _
    exact b2f_parityRun_flatMap (N := n) (fun j : Fin n =>
      unflat2 t m bitsW r e &&
        xor (unflat3 m n bitsA e i j) (unflat3 m n bitsA e j i) &&
        unflat2 a n bitsU α i && unflat2 a n bitsU β j)
  change checkBilin env = [true] ↔ _
  unfold checkBilin notF sel
  simp only [env, unpairB_pairB, un_length]
  split_ifs with h
  · simp only [true_iff]
    rw [flatMap_range_eq_nil_iff] at h
    intro r α β
    have hr := h r.val r.isLt
    unfold bilR at hr
    simp only [unpairB_pairB, un_length] at hr
    rw [flatMap_range_eq_nil_iff] at hr
    have hα := hr α.val α.isLt
    unfold bilAlpha at hα
    simp only [unpairB_pairB, un_length] at hα
    rw [flatMap_range_eq_nil_iff] at hα
    have hβ := hα β.val β.isLt
    unfold bilBeta parityF at hβ
    simp only [unpairB_pairB, un_length] at hβ
    rw [← htriple r α β]
    revert hβ
    cases parityRun false ((List.range m).flatMap fun e =>
      bilE (pairB (un e)
        (pairB (un β.val)
          (pairB (un α.val)
            (pairB (un r.val) env)))))
    · intro _; rfl
    · intro hβ; simp [bflag] at hβ
  · simp only [false_iff]
    intro hall
    apply h
    rw [flatMap_range_eq_nil_iff]; intro r hr
    unfold bilR
    simp only [unpairB_pairB, un_length]
    rw [flatMap_range_eq_nil_iff]; intro α hα
    unfold bilAlpha
    simp only [unpairB_pairB, un_length]
    rw [flatMap_range_eq_nil_iff]; intro β hβ
    unfold bilBeta parityF
    simp only [unpairB_pairB, un_length]
    have hs := hall ⟨r, hr⟩ ⟨α, hα⟩ ⟨β, hβ⟩
    rw [← htriple ⟨r, hr⟩ ⟨α, hα⟩ ⟨β, hβ⟩] at hs
    revert hs
    cases parityRun false ((List.range m).flatMap fun e =>
      bilE (pairB (un e)
        (pairB (un β)
          (pairB (un α)
            (pairB (un r) env)))))
    · intro _; rfl
    · intro hs; simp [b2f] at hs
def verifFlag (p q : ℕ) (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let w := (unpairB s).2
  let ok0 := hasFalse x
  let uN := hd x
  let x1 := dropN x
  let ok1 := hasFalse x1
  let uM := hd x1
  let x2 := dropN x1
  let ok2 := hasFalse x2
  let uK := hd x2
  let x3 := dropN x2
  let ok3 := hasFalse x3
  let uD := hd x3
  let bitsA := dropN x3
  let okLenA := eqF (toUnary bitsA)
    (mulU uM (mulU uN uN))
  let pm := mulU (un p) uM
  let qk := mulU (un q) uK
  let qk1 := mulU (un q) (true :: uK)
  let okK := andF (leU qk pm) (ltU pm qk1)
  let okW0 := hasFalse w
  let uA := hd w
  let w1 := dropN w
  let okW1 := hasFalse w1
  let uT := hd w1
  let w2 := dropN w1
  let szU := mulU uA uN
  let szP := mulU uN uA
  let szW := mulU uT uM
  let szQ := mulU uM uT
  let okLenW := eqF (toUnary w2) (szU ++ szP ++ szW ++ szQ)
  let bitsU := tk szU w2
  let w3 := dropK szU w2
  let bitsP := tk szP w3
  let w4 := dropK szP w3
  let bitsW := tk szW w4
  let w5 := dropK szW w4
  let bitsQ := tk szQ w5
  let okIne := andF (leU uA uN) (andF (leU uT uM)
    (andF (leU uM (uK ++ uT)) (leU (uN ++ uT) (uA ++ uD))))
  let okUP := checkMatId (pairB uA
    (pairB uN (pairB bitsU bitsP)))
  let okWQ := checkMatId (pairB uT
    (pairB uM (pairB bitsW bitsQ)))
  let okBil := checkBilin (pairB uN
    (pairB uM (pairB uA
      (pairB uT (pairB bitsA
        (pairB bitsU bitsW))))))
  andF ok0 (andF ok1 (andF ok2 (andF ok3 (andF okLenA (andF okK
    (andF okW0 (andF okW1 (andF okLenW (andF okIne
      (andF okUP (andF okWQ okBil)))))))))))
lemma cpt_verifFlag (p q : ℕ) : CPTs (verifFlag p q) := by
  have hx := cpt_unpairB1
  have hw := cpt_unpairB2
  have hok0 := cpt_hasFalse1 hx
  have huN := cpt_hd1 hx
  have hx1 := cpt_dropN1 hx
  have hok1 := cpt_hasFalse1 hx1
  have huM := cpt_hd1 hx1
  have hx2 := cpt_dropN1 hx1
  have hok2 := cpt_hasFalse1 hx2
  have huK := cpt_hd1 hx2
  have hx3 := cpt_dropN1 hx2
  have hok3 := cpt_hasFalse1 hx3
  have huD := cpt_hd1 hx3
  have hbA := cpt_dropN1 hx3
  have hokLenA := cpt_eqF' (cpt_toUnary1 hbA)
    (cpt_mulU2 huM (cpt_mulU2 huN huN))
  have hpm := cpt_mulU2
    (cpt_const (un p)) huM
  have hqk := cpt_mulU2
    (cpt_const (un q)) huK
  have hqk1 := cpt_mulU2
    (cpt_const (un q))
    (cpt_cons1 true huK)
  have hokK := cpt_andF (cpt_leU hqk hpm) (cpt_ltU hpm hqk1)
  have hokW0 := cpt_hasFalse1 hw
  have huA := cpt_hd1 hw
  have hw1 := cpt_dropN1 hw
  have hokW1 := cpt_hasFalse1 hw1
  have huT := cpt_hd1 hw1
  have hw2 := cpt_dropN1 hw1
  have hszU := cpt_mulU2 huA huN
  have hszP := cpt_mulU2 huN huA
  have hszW := cpt_mulU2 huT huM
  have hszQ := cpt_mulU2 huM huT
  have hokLenW := cpt_eqF' (cpt_toUnary1 hw2)
    (cpt_app2
      (cpt_app2
        (cpt_app2 hszU hszP) hszW) hszQ)
  have hbU := cpt_tk hszU hw2
  have hw3 := cpt_dropK hszU hw2
  have hbP := cpt_tk hszP hw3
  have hw4 := cpt_dropK hszP hw3
  have hbW := cpt_tk hszW hw4
  have hw5 := cpt_dropK hszW hw4
  have hbQ := cpt_tk hszQ hw5
  have hokIne := cpt_andF (cpt_leU huA huN) (cpt_andF (cpt_leU huT huM)
    (cpt_andF (cpt_leU huM (cpt_app2 huK huT))
      (cpt_leU (cpt_app2 huN huT)
        (cpt_app2 huA huD))))
  have hokUP := cpt_comp
    (cpt_pairB2 huA
      (cpt_pairB2 huN (cpt_pairB2 hbU hbP)))
    cpt_checkMatId
  have hokWQ := cpt_comp
    (cpt_pairB2 huT
      (cpt_pairB2 huM (cpt_pairB2 hbW hbQ)))
    cpt_checkMatId
  have hokBil := cpt_comp
    (cpt_pairB2 huN
      (cpt_pairB2 huM
        (cpt_pairB2 huA
          (cpt_pairB2 huT
            (cpt_pairB2 hbA
              (cpt_pairB2 hbU hbW))))))
    cpt_checkBilin
  exact cpt_andF hok0 (cpt_andF hok1 (cpt_andF hok2 (cpt_andF hok3 (cpt_andF hokLenA (cpt_andF hokK
    (cpt_andF hokW0 (cpt_andF hokW1 (cpt_andF hokLenW (cpt_andF hokIne
      (cpt_andF hokUP (cpt_andF hokWQ hokBil)))))))))))
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
lemma div_eq_iff_bounds {p m q k : ℕ} (hq : 0 < q) :
    k = p * m / q ↔ q * k ≤ p * m ∧ p * m < q * (k + 1) := by
  constructor
  · rintro rfl
    refine ⟨Nat.mul_div_le (p * m) q, ?_⟩
    have h1 := Nat.div_add_mod (p * m) q
    have h2 := Nat.mod_lt (p * m) hq
    have : q * (p * m / q + 1) = q * (p * m / q) + q := by ring
    omega
  · rintro ⟨h1, h2⟩
    have hle : k ≤ p * m / q :=
      (Nat.le_div_iff_mul_le hq).mpr (by rw [Nat.mul_comm k q]; exact h1)
    have hlt : p * m / q < k + 1 :=
      (Nat.div_lt_iff_lt_mul hq).mpr (by rw [Nat.mul_comm (k + 1) q]; exact h2)
    omega
theorem lang_in_NP (p q : ℕ) (hpq : p < q) :
    ({s | ∃ (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool),
      pack n m k d A = s ∧ k = p * m / q ∧ feasible n m k d (quad n m A)} : Language Bool) ∈
    NP := by
  have hq_pos : 0 < q := by omega
  let neS : List Bool → Bool := fun l => !l.isEmpty
  let verif : List Bool × List Bool → Bool := fun xw =>
    neS (verifFlag p q (pairB xw.1 xw.2))
  let R : Set (List Bool × List Bool) := {xw | verif xw = true}
  let Pwit : Polynomial ℕ := Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  refine ⟨R, Pwit, ⟨verif, fun _ => Iff.rfl, ?_⟩, fun x => ?_⟩
  · exact cpt_comp (g := neS)
      (cpt_comp cpt_pairB (cpt_verifFlag p q))
      cpt_neS
  · constructor
    · rintro ⟨n, m, k, d, A, rfl, hk, hfeas⟩
      obtain ⟨a, t, U, P, W, Q, han, htm, hmkt, hntad, hUP, hWQ, hbil⟩ :=
        feasible_iff_matrix.mp hfeas
      let w : List Bool := header a ++ header t ++ flat2 a n U ++ flat2 n a P ++
        flat2 t m W ++ flat2 m t Q
      have hn_le : n ≤ (pack n m k d A).length := by
        unfold pack header; simp
      have hm_le : m ≤ (pack n m k d A).length := by
        unfold pack header; simp; omega
      have hw_len : w.length ≤ Pwit.eval (pack n m k d A).length := by
        simp only [w, header, flat2_length, List.length_append, List.length_replicate,
          List.length_singleton, Pwit, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        have ha_le : a ≤ (pack n m k d A).length := le_trans han hn_le
        have ht_le : t ≤ (pack n m k d A).length := le_trans htm hm_le
        have h1 : a * n ≤ (pack n m k d A).length ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul ha_le hn_le
        have h2 : n * a ≤ (pack n m k d A).length ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul hn_le ha_le
        have h3 : t * m ≤ (pack n m k d A).length ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul ht_le hm_le
        have h4 : m * t ≤ (pack n m k d A).length ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul hm_le ht_le
        omega
      refine ⟨w, hw_len, ?_⟩
      show !(verifFlag p q (pairB (pack n m k d A) w)).isEmpty = true
      have hflag : verifFlag p q (pairB (pack n m k d A) w) = [true] := by
        unfold verifFlag
        simp only [unpairB_pairB]
        have hx_eq : pack n m k d A = header n ++ (header m ++ (header k ++ (header d ++ flat3 m n A))) := by
          unfold pack flat3; simp [List.append_assoc]
        have hw_eq : w = header a ++ (header t ++ (flat2 a n U ++ flat2 n a P ++ flat2 t m W ++ flat2 m t Q)) := by
          simp [w, List.append_assoc]
        rw [hx_eq, hw_eq]
        simp only [hd_header_append, dropN_header_append, mulU,
          List.length_cons, un_length, un_append_un]
        have htkU : tk
            (un (a * n))
            (flat2 a n U ++ flat2 n a P ++ flat2 t m W ++ flat2 m t Q) = flat2 a n U := by
          rw [tk_eq, un_length,
            List.append_assoc, List.append_assoc, ← flat2_length a n U, List.take_left]
        have hdrU : dropK (un (a * n))
            (flat2 a n U ++ flat2 n a P ++ flat2 t m W ++ flat2 m t Q) =
            flat2 n a P ++ flat2 t m W ++ flat2 m t Q := by
          rw [dropK_eq, un_length,
            List.append_assoc, List.append_assoc, ← flat2_length a n U, List.drop_left,
            ← List.append_assoc]
        have htkP : tk
            (un (n * a))
            (flat2 n a P ++ flat2 t m W ++ flat2 m t Q) = flat2 n a P := by
          rw [tk_eq, un_length,
            List.append_assoc, ← flat2_length n a P, List.take_left]
        have hdrP : dropK (un (n * a))
            (flat2 n a P ++ flat2 t m W ++ flat2 m t Q) = flat2 t m W ++ flat2 m t Q := by
          rw [dropK_eq, un_length,
            List.append_assoc, ← flat2_length n a P, List.drop_left]
        have htkW : tk
            (un (t * m))
            (flat2 t m W ++ flat2 m t Q) = flat2 t m W := by
          rw [tk_eq, un_length,
            ← flat2_length t m W, List.take_left]
        have hdrW : dropK (un (t * m))
            (flat2 t m W ++ flat2 m t Q) = flat2 m t Q := by
          rw [dropK_eq, un_length, ← flat2_length t m W, List.drop_left]
        have htkQ : tk
            (un (m * t)) (flat2 m t Q) = flat2 m t Q := by
          rw [tk_eq, un_length,
            ← flat2_length m t Q, List.take_length]
        rw [htkU, hdrU, htkP, hdrP, htkW, hdrW, htkQ]
        have hUP' : checkMatId (pairB (un a)
            (pairB (un n)
              (pairB (flat2 a n U) (flat2 n a P)))) = [true] := by
          rw [checkMatId_spec]
          intro α β
          simp only [unflat2, flat2_getD]
          exact hUP α β
        have hWQ' : checkMatId (pairB (un t)
            (pairB (un m)
              (pairB (flat2 t m W) (flat2 m t Q)))) = [true] := by
          rw [checkMatId_spec]
          intro r s
          simp only [unflat2, flat2_getD]
          exact hWQ r s
        have hBil' : checkBilin (pairB (un n)
            (pairB (un m)
              (pairB (un a)
                (pairB (un t)
                  (pairB (flat3 m n A)
                    (pairB (flat2 a n U) (flat2 t m W))))))) = [true] := by
          rw [checkBilin_spec]
          intro r α β
          simp only [unflat2, unflat3, flat2_getD, flat3_getD]
          exact hbil r α β
        have hkb := (div_eq_iff_bounds hq_pos).mp hk
        have hhf : ∀ c r, hasFalse (header c ++ r) = [true] := fun c r => by
          unfold hasFalse header; simp [bflag]
        have hlenA : eqF (toUnary (flat3 m n A)) (un (m * (n * n))) = [true] := by
          unfold eqF toUnary; rw [flat3_length]; simp [bflag]
        have hlenW : eqF (toUnary (flat2 a n U ++ flat2 n a P ++ flat2 t m W ++ flat2 m t Q))
            (un (a * n + n * a + t * m + m * t)) = [true] := by
          unfold eqF toUnary
          simp only [List.length_append, flat2_length, decide_true,
            bflag, ↓reduceIte]
        rw [hhf, hhf, hhf, hhf, hhf, hhf, hlenA, hlenW, hUP', hWQ', hBil']
        simp only [leU_un, ltU_un, hkb.1, hkb.2, han, htm, hmkt, hntad, decide_true,
          bflag, ↓reduceIte, andF_true_true]
      rw [hflag]; rfl
    · rintro ⟨w, _, hw⟩
      have hne : verifFlag p q (pairB x w) ≠ [] := by
        change !(verifFlag p q (pairB x w)).isEmpty = true at hw
        cases h : verifFlag p q (pairB x w) <;> simp_all
      unfold verifFlag at hne
      simp only [unpairB_pairB] at hne
      repeat rw [andF_ne_nil_iff] at hne
      obtain ⟨hok0, hok1, hok2, hok3, hokLenA, ⟨hokK1, hokK2⟩, hokW0, hokW1, hokLenW,
        ⟨hokI1, hokI2, hokI3, hokI4⟩, hokUP, hokWQ, hokBil⟩ := hne
      have hf0 : false ∈ x := by
        unfold hasFalse at hok0; rw [bflag_ne_nil_iff, decide_eq_true_eq] at hok0; exact hok0
      have hf1 : false ∈ dropN x := by
        unfold hasFalse at hok1; rw [bflag_ne_nil_iff, decide_eq_true_eq] at hok1; exact hok1
      have hf2 : false ∈ dropN (dropN x) := by
        unfold hasFalse at hok2; rw [bflag_ne_nil_iff, decide_eq_true_eq] at hok2; exact hok2
      have hf3 : false ∈ dropN (dropN (dropN x)) := by
        unfold hasFalse at hok3; rw [bflag_ne_nil_iff, decide_eq_true_eq] at hok3; exact hok3
      have hfw0 : false ∈ w := by
        unfold hasFalse at hokW0; rw [bflag_ne_nil_iff, decide_eq_true_eq] at hokW0; exact hokW0
      have hfw1 : false ∈ dropN w := by
        unfold hasFalse at hokW1; rw [bflag_ne_nil_iff, decide_eq_true_eq] at hokW1; exact hokW1
      let n := (hd x).length
      let x1 := dropN x
      let m := (hd x1).length
      let x2 := dropN x1
      let k := (hd x2).length
      let x3 := dropN x2
      let d := (hd x3).length
      let bitsA := dropN x3
      let a := (hd w).length
      let w1 := dropN w
      let t := (hd w1).length
      let w2 := dropN w1
      have huN_eq : hd x = un n := hd_eq_un_length x
      have huM_eq : hd x1 = un m := hd_eq_un_length x1
      have huK_eq : hd x2 = un k := hd_eq_un_length x2
      have huD_eq : hd x3 = un d := hd_eq_un_length x3
      have huA_eq : hd w = un a := hd_eq_un_length w
      have huT_eq : hd w1 = un t := hd_eq_un_length w1
      have hx_split : x = header n ++ header m ++ header k ++ header d ++ bitsA := by
        have h0 := (header_parse_iff x).mp hf0
        have h1 := (header_parse_iff x1).mp hf1
        have h2 := (header_parse_iff x2).mp hf2
        have h3 := (header_parse_iff x3).mp hf3
        calc x = header n ++ x1 := h0
          _ = header n ++ (header m ++ x2) := by rw [h1]
          _ = header n ++ (header m ++ (header k ++ x3)) := by rw [h2]
          _ = header n ++ (header m ++ (header k ++ (header d ++ bitsA))) := by rw [h3]
          _ = header n ++ header m ++ header k ++ header d ++ bitsA := by simp [List.append_assoc]
      have hlenA : bitsA.length = m * (n * n) := by
        unfold eqF toUnary at hokLenA
        rw [bflag_ne_nil_iff, decide_eq_true_eq] at hokLenA
        simpa [mulU, n, m] using un_inj hokLenA
      have hk_eq : k = p * m / q := by
        rw [div_eq_iff_bounds hq_pos]
        simp only [mulU, un_length,
          List.length_cons] at hokK1 hokK2
        rw [leU_un, bflag_ne_nil_iff, decide_eq_true_eq] at hokK1
        rw [ltU_un, bflag_ne_nil_iff, decide_eq_true_eq] at hokK2
        exact ⟨hokK1, hokK2⟩
      have han : a ≤ n := by
        change leU (hd w) (hd x) ≠ [] at hokI1
        rw [huA_eq, huN_eq, leU_un, bflag_ne_nil_iff, decide_eq_true_eq] at hokI1
        exact hokI1
      have htm : t ≤ m := by
        change leU (hd w1) (hd x1) ≠ [] at hokI2
        rw [huT_eq, huM_eq, leU_un, bflag_ne_nil_iff, decide_eq_true_eq] at hokI2
        exact hokI2
      have hmkt : m ≤ k + t := by
        change leU (hd x1)
          (hd x2 ++ hd w1) ≠ [] at hokI3
        rw [huM_eq, huK_eq, huT_eq, un_append_un, leU_un, bflag_ne_nil_iff, decide_eq_true_eq] at hokI3
        exact hokI3
      have hntad : n + t ≤ a + d := by
        change leU (hd x ++ hd w1)
          (hd w ++ hd x3) ≠ [] at hokI4
        rw [huN_eq, huT_eq, huA_eq, huD_eq, un_append_un, un_append_un, leU_un,
          bflag_ne_nil_iff, decide_eq_true_eq] at hokI4
        exact hokI4
      let bitsU := tk
        (mulU (hd w) (hd x)) w2
      let w3 := dropK (mulU (hd w) (hd x)) w2
      let bitsP := tk
        (mulU (hd x) (hd w)) w3
      let w4 := dropK (mulU (hd x) (hd w)) w3
      let bitsW := tk
        (mulU (hd w1) (hd x1)) w4
      let w5 := dropK (mulU (hd w1) (hd x1)) w4
      let bitsQ := tk
        (mulU (hd x1) (hd w1)) w5
      have hUP_eq : checkMatId (pairB (un a)
          (pairB (un n)
            (pairB bitsU bitsP))) = [true] := by
        rw [← huA_eq, ← huN_eq]
        exact notF_eq_true_of_ne_nil hokUP
      have hWQ_eq : checkMatId (pairB (un t)
          (pairB (un m)
            (pairB bitsW bitsQ))) = [true] := by
        rw [← huT_eq, ← huM_eq]
        exact notF_eq_true_of_ne_nil hokWQ
      have hBil_eq : checkBilin (pairB (un n)
          (pairB (un m)
            (pairB (un a)
              (pairB (un t)
                (pairB bitsA
                  (pairB bitsU bitsW)))))) = [true] := by
        rw [← huN_eq, ← huM_eq, ← huA_eq, ← huT_eq]
        exact notF_eq_true_of_ne_nil hokBil
      refine ⟨n, m, k, d, unflat3 m n bitsA, ?_, hk_eq, ?_⟩
      · change header n ++ header m ++ header k ++ header d ++ flat3 m n (unflat3 m n bitsA) = x
        rw [flat3_unflat3 bitsA hlenA, hx_split]
      · rw [feasible_iff_matrix]
        exact ⟨a, t, unflat2 a n bitsU, unflat2 n a bitsP, unflat2 t m bitsW, unflat2 m t bitsQ,
          han, htm, hmkt, hntad,
          (checkMatId_spec a n bitsU bitsP).mp hUP_eq,
          (checkMatId_spec t m bitsW bitsQ).mp hWQ_eq,
          (checkBilin_spec n m a t bitsA bitsU bitsW).mp hBil_eq⟩
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
def countOccEdgesB (y : List Bool) : List Bool :=
  let uA := (unpairB y).1
  let r1 := (unpairB y).2
  let uN0 := (unpairB r1).1
  let s := (unpairB r1).2
  (List.range uN0.length).flatMap fun b =>
    hasOccEdgeF s uA (un b)
lemma cpt_countOccEdgesB : CPTs countOccEdgesB := by
  have huA := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huN0 := cpt_unpairB1_1 hr1
  have hstep : CPTs (fun z =>
      let uB := (unpairB z).1
      let y := (unpairB z).2
      let uA := (unpairB y).1
      let r1 := (unpairB y).2
      let s := (unpairB r1).2
      hasOccEdgeF s uA uB) :=
    cpt_hasOccEdgeF
      (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
      (cpt_unpairB1_1 cpt_unpairB2)
      cpt_unpairB1
  exact cpt_ext
    (cpt_flatMapRange hstep huN0 cpt_id)
    (fun y => by
      dsimp only [countOccEdgesB]
      apply List.flatMap_congr; intro b _
      simp [unpairB_pairB])
def countOccEdges (s : List Bool) : List Bool :=
  let uN0 := countLits s
  (List.range uN0.length).flatMap fun a =>
    countOccEdgesB (pairB (un a)
      (pairB uN0 s))
lemma cpt_countOccEdges : CPTs countOccEdges :=
  cpt_flatMapRange cpt_countOccEdgesB cpt_countLits
    (cpt_pairB2 cpt_countLits cpt_id)
lemma countOccEdges_cnf (φ : CNF) (hne : ∀ c ∈ φ, c ≠ []) :
    countOccEdges (encodeCNF φ) =
      un (occEdges φ).length := by
  have h1 : countOccEdges (encodeCNF φ) =
      (occEdges φ).map (fun _ => true) := by
    unfold countOccEdges occEdges
    dsimp only
    rw [countLits_cnf, un_length, List.map_flatMap]
    have houter : ((List.range (occs φ).length).flatMap fun a =>
        countOccEdgesB (pairB (un a)
          (pairB (un (occs φ).length)
            (encodeCNF φ)))) =
        (List.range (occs φ).length).flatMap (fun a =>
          if ha : a < (occs φ).length then
            ((List.finRange (occs φ).length).filterMap fun b =>
              if occEdge φ ⟨a, ha⟩ b then some ((⟨a, ha⟩ : Fin (occs φ).length), b) else none).map (fun _ => true)
          else []) := by
      apply List.flatMap_congr; intro a ha
      have ha' : a < (occs φ).length := List.mem_range.mp ha
      simp only [ha', ↓reduceDIte, countOccEdgesB, unpairB_pairB,
        un_length]
      have hinner : ((List.range (occs φ).length).flatMap fun b =>
          hasOccEdgeF (encodeCNF φ) (un a)
            (un b)) =
          (List.range (occs φ).length).flatMap (fun b =>
            if hb : b < (occs φ).length then
              bflag (occEdge φ ⟨a, ha'⟩ ⟨b, hb⟩)
            else []) := by
        apply List.flatMap_congr; intro b hb
        have hb' : b < (occs φ).length := List.mem_range.mp hb
        simp only [hb', ↓reduceDIte]
        exact hasOccEdgeF_spec φ hne ⟨a, ha'⟩ ⟨b, hb'⟩
      rw [hinner, flatMap_range_eq_finRange (occs φ).length (fun b : Fin (occs φ).length =>
        bflag (occEdge φ ⟨a, ha'⟩ b))]
      have hfm : ∀ (l : List (Fin (occs φ).length)),
          (l.flatMap fun b => bflag (occEdge φ ⟨a, ha'⟩ b)) =
          (l.filterMap fun b => if occEdge φ ⟨a, ha'⟩ b then some ((⟨a, ha'⟩ : Fin (occs φ).length), b) else none).map (fun _ => true) := by
        intro l
        induction l with
        | nil => rfl
        | cons x xs ih =>
          rw [List.flatMap_cons, List.filterMap_cons, ih]
          cases h : occEdge φ ⟨a, ha'⟩ x <;> simp [h, bflag]
      exact hfm (List.finRange (occs φ).length)
    rw [houter, flatMap_range_eq_finRange (occs φ).length (fun a : Fin (occs φ).length =>
      ((List.finRange (occs φ).length).filterMap fun b =>
        if occEdge φ a b then some (a, b) else none).map (fun _ => true))]
  rw [h1]
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp, fun x hx => by simp at hx; exact hx.2⟩
def emitEdgeCell (y : List Bool) : List Bool :=
  let uJ := (unpairB y).1
  let r1 := (unpairB y).2
  let uI := (unpairB r1).1
  let r2 := (unpairB r1).2
  let r3 := (unpairB r2).2
  let uU := (unpairB r3).1
  let uV := (unpairB r3).2
  sel (andF (eqF uI uU) (eqF uJ uV)) [false] [true]
lemma cpt_emitEdgeCell : CPTs emitEdgeCell := by
  have huJ := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huI := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have hr3 := cpt_unpairB2_1 hr2
  have huU := cpt_unpairB1_1 hr3
  have huV := cpt_unpairB2_1 hr3
  exact cpt_sel (cpt_andF (cpt_eqF' huI huU) (cpt_eqF' huJ huV))
    (cpt_const [false]) (cpt_const [true])
def emitEdgeRow (y : List Bool) : List Bool :=
  let r2 := (unpairB y).2
  let uN := (unpairB r2).1
  (List.range uN.length).flatMap fun j =>
    emitEdgeCell (pairB (un j) y)
lemma cpt_emitEdgeRow : CPTs emitEdgeRow :=
  cpt_flatMapRange cpt_emitEdgeCell
    (cpt_unpairB1_1 cpt_unpairB2)
    cpt_id
def emitEdgeMat (y : List Bool) : List Bool :=
  let uN := (unpairB y).1
  (List.range uN.length).flatMap fun i =>
    emitEdgeRow (pairB (un i) y)
lemma cpt_emitEdgeMat : CPTs emitEdgeMat :=
  cpt_flatMapRange cpt_emitEdgeRow
    cpt_unpairB1 cpt_id
lemma emitEdgeMat_spec (n : ℕ) (u v : Fin n) :
    emitEdgeMat (pairB (un n)
      (pairB (un u.val)
        (un v.val))) =
    (List.finRange n).flatMap fun i => (List.finRange n).map fun j => decide (i = u ∧ j = v) := by
  unfold emitEdgeMat
  simp only [unpairB_pairB, un_length]
  have h1 : ((List.range n).flatMap fun i =>
      emitEdgeRow (pairB (un i)
        (pairB (un n)
          (pairB (un u.val)
            (un v.val))))) =
      (List.range n).flatMap (fun i => if hi : i < n then
        (List.finRange n).map fun j => decide ((⟨i, hi⟩ : Fin n) = u ∧ j = v) else []) := by
    apply List.flatMap_congr; intro i hi
    have hi' : i < n := List.mem_range.mp hi
    simp only [hi', ↓reduceDIte, emitEdgeRow, unpairB_pairB,
      un_length]
    have h2 : ((List.range n).flatMap fun j =>
        emitEdgeCell (pairB (un j)
          (pairB (un i)
            (pairB (un n)
              (pairB (un u.val)
                (un v.val)))))) =
        (List.range n).flatMap (fun j => if hj : j < n then
          [decide ((⟨i, hi'⟩ : Fin n) = u ∧ (⟨j, hj⟩ : Fin n) = v)] else []) := by
      apply List.flatMap_congr; intro j hj
      have hj' : j < n := List.mem_range.mp hj
      simp only [hj', ↓reduceDIte, emitEdgeCell, unpairB_pairB]
      have heq1 : eqF (un i) (un u.val) =
          bflag (decide ((⟨i, hi'⟩ : Fin n) = u)) := by
        unfold eqF; congr 1; simp only [decide_eq_decide]
        exact ⟨fun h => Fin.ext (un_inj h),
          fun h => congrArg un (congrArg Fin.val h)⟩
      have heq2 : eqF (un j) (un v.val) =
          bflag (decide ((⟨j, hj'⟩ : Fin n) = v)) := by
        unfold eqF; congr 1; simp only [decide_eq_decide]
        exact ⟨fun h => Fin.ext (un_inj h),
          fun h => congrArg un (congrArg Fin.val h)⟩
      rw [heq1, heq2, andF_bflag]
      by_cases hiu : (⟨i, hi'⟩ : Fin n) = u <;> by_cases hjv : (⟨j, hj'⟩ : Fin n) = v <;>
        simp [hiu, hjv, bflag, sel]
    rw [h2, flatMap_range_eq_finRange n (fun j : Fin n => [decide ((⟨i, hi'⟩ : Fin n) = u ∧ j = v)])]
    have hmap : ∀ (l : List (Fin n)) (f : Fin n → Bool),
        (l.flatMap fun j => [f j]) = l.map f := by
      intro l f; induction l with | nil => rfl | cons x xs ih => simp [ih]
    exact hmap _ _
  rw [h1, flatMap_range_eq_finRange n (fun i : Fin n =>
    (List.finRange n).map fun j => decide (i = u ∧ j = v))]
def emitCopyB (y : List Bool) : List Bool :=
  let uB := (unpairB y).1
  let r1 := (unpairB y).2
  let uA := (unpairB r1).1
  let r2 := (unpairB r1).2
  let uT := (unpairB r2).1
  let r3 := (unpairB r2).2
  let uN := (unpairB r3).1
  let r4 := (unpairB r3).2
  let uN0 := (unpairB r4).1
  let s := (unpairB r4).2
  let base := mulU uT uN0
  sel (hasOccEdgeF s uA uB) []
    (emitEdgeMat (pairB uN
      (pairB (base ++ uA) (base ++ uB))))
lemma cpt_emitCopyB : CPTs emitCopyB := by
  have huB := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huA := cpt_unpairB1_1 hr1
  have hr2 := cpt_unpairB2_1 hr1
  have huT := cpt_unpairB1_1 hr2
  have hr3 := cpt_unpairB2_1 hr2
  have huN := cpt_unpairB1_1 hr3
  have hr4 := cpt_unpairB2_1 hr3
  have huN0 := cpt_unpairB1_1 hr4
  have hs := cpt_unpairB2_1 hr4
  have hbase := cpt_mulU2 huT huN0
  have hmat := cpt_comp
    (cpt_pairB2 huN
      (cpt_pairB2
        (cpt_app2 hbase huA)
        (cpt_app2 hbase huB)))
    cpt_emitEdgeMat
  exact cpt_sel (cpt_hasOccEdgeF hs huA huB)
    (cpt_const []) hmat
def emitCopyA (y : List Bool) : List Bool :=
  let r2 := (unpairB y).2
  let r3 := (unpairB r2).2
  let r4 := (unpairB r3).2
  let uN0 := (unpairB r4).1
  (List.range uN0.length).flatMap fun b =>
    emitCopyB (pairB (un b) y)
lemma cpt_emitCopyA : CPTs emitCopyA := by
  have hr2 := cpt_unpairB2
  have hr3 := cpt_unpairB2_1 hr2
  have hr4 := cpt_unpairB2_1 hr3
  have huN0 := cpt_unpairB1_1 hr4
  exact cpt_flatMapRange cpt_emitCopyB huN0
    cpt_id
def emitCopyT (y : List Bool) : List Bool :=
  let r3 := (unpairB y).2
  let r4 := (unpairB r3).2
  let uN0 := (unpairB r4).1
  (List.range uN0.length).flatMap fun a =>
    emitCopyA (pairB (un a) y)
lemma cpt_emitCopyT : CPTs emitCopyT := by
  have hr3 := cpt_unpairB2
  have hr4 := cpt_unpairB2_1 hr3
  have huN0 := cpt_unpairB1_1 hr4
  exact cpt_flatMapRange cpt_emitCopyA huN0
    cpt_id
def emitCopies (p q : ℕ) (y : List Bool) : List Bool :=
  (List.range (q - p)).flatMap fun t =>
    emitCopyT (pairB (un t) y)
lemma cpt_emitCopies (p q : ℕ) : CPTs (emitCopies p q) := by
  have h1 := cpt_flatMapRange
    (f := emitCopyT) (cnt := fun _ => un (q - p)) (arg := id)
    cpt_emitCopyT
    (cpt_const (un (q - p)))
    cpt_id
  exact cpt_ext h1 (fun y => by simp [emitCopies, un_length])
def emitDumEdge (y : List Bool) : List Bool :=
  let uS := (unpairB y).1
  let r1 := (unpairB y).2
  let uN := (unpairB r1).1
  let uBase := (unpairB r1).2
  let uU := uBase ++ uS ++ uS
  let uV := true :: uU
  emitEdgeMat (pairB uN (pairB uU uV))
lemma cpt_emitDumEdge : CPTs emitDumEdge := by
  have huS := cpt_unpairB1
  have hr1 := cpt_unpairB2
  have huN := cpt_unpairB1_1 hr1
  have huBase := cpt_unpairB2_1 hr1
  have huU := cpt_app2
    (cpt_app2 huBase huS) huS
  have huV := cpt_cons1 true huU
  exact cpt_comp
    (g := emitEdgeMat)
    (cpt_pairB2 huN (cpt_pairB2 huU huV))
    cpt_emitEdgeMat
def emitDumEdges (y : List Bool) : List Bool :=
  let uPE := (unpairB y).1
  let r1 := (unpairB y).2
  (List.range uPE.length).flatMap fun s =>
    emitDumEdge (pairB (un s) r1)
lemma cpt_emitDumEdges : CPTs emitDumEdges :=
  cpt_flatMapRange cpt_emitDumEdge
    cpt_unpairB1 cpt_unpairB2
def bgBase (p q : ℕ) (s : List Bool) : List Bool :=
  mulU (un (q - p)) (countLits s)
def bgPE (p : ℕ) (s : List Bool) : List Bool :=
  mulU (un p) (countOccEdges s)
def bgN (p q : ℕ) (s : List Bool) : List Bool :=
  bgBase p q s ++ bgPE p s ++ bgPE p s
def bgHdr (p q : ℕ) (s : List Bool) : List Bool :=
  let uM := mulU (un q) (countOccEdges s)
  let uD := mulU (un (q - p))
    (countOccEdges s ++ dropK (countClauses s) (countLits s))
  (bgN p q s ++ [false]) ++ (uM ++ [false]) ++ (bgPE p s ++ [false]) ++ (uD ++ [false])
def bgCop (p q : ℕ) (s : List Bool) : List Bool :=
  emitCopies p q (pairB (bgN p q s)
    (pairB (countLits s) s))
def bgDum (p q : ℕ) (s : List Bool) : List Bool :=
  emitDumEdges (pairB (bgPE p s)
    (pairB (bgN p q s) (bgBase p q s)))
def buildGraph (p q : ℕ) (s : List Bool) : List Bool :=
  bgHdr p q s ++ bgCop p q s ++ bgDum p q s
lemma cpt_bgBase (p q : ℕ) : CPTs (bgBase p q) :=
  cpt_mulU2
    (cpt_const (un (q - p))) cpt_countLits
lemma cpt_bgPE (p : ℕ) : CPTs (bgPE p) :=
  cpt_mulU2
    (cpt_const (un p)) cpt_countOccEdges
lemma cpt_bgN (p q : ℕ) : CPTs (bgN p q) :=
  cpt_app2
    (cpt_app2 (cpt_bgBase p q) (cpt_bgPE p)) (cpt_bgPE p)
lemma cpt_bgHdr (p q : ℕ) : CPTs (bgHdr p q) := by
  have huM := cpt_mulU2
    (cpt_const (un q)) cpt_countOccEdges
  have huD := cpt_mulU2
    (cpt_const (un (q - p)))
    (cpt_app2 cpt_countOccEdges (cpt_dropK cpt_countClauses cpt_countLits))
  have hf := cpt_const [false]
  exact cpt_app2
    (cpt_app2
      (cpt_app2
        (cpt_app2 (cpt_bgN p q) hf)
        (cpt_app2 huM hf))
      (cpt_app2 (cpt_bgPE p) hf))
    (cpt_app2 huD hf)
lemma cpt_bgCop (p q : ℕ) : CPTs (bgCop p q) :=
  cpt_comp
    (f := fun s => pairB (bgN p q s)
      (pairB (countLits s) s))
    (g := emitCopies p q)
    (cpt_pairB2 (cpt_bgN p q)
      (cpt_pairB2 cpt_countLits cpt_id))
    (cpt_emitCopies p q)
lemma cpt_bgDum (p q : ℕ) : CPTs (bgDum p q) :=
  cpt_comp
    (f := fun s => pairB (bgPE p s)
      (pairB (bgN p q s) (bgBase p q s)))
    (g := emitDumEdges)
    (cpt_pairB2 (cpt_bgPE p)
      (cpt_pairB2 (cpt_bgN p q) (cpt_bgBase p q)))
    cpt_emitDumEdges
lemma cpt_buildGraph (p q : ℕ) : CPTs (buildGraph p q) :=
  cpt_app2
    (cpt_app2 (cpt_bgHdr p q) (cpt_bgCop p q)) (cpt_bgDum p q)
lemma finRange_flatMap_congr_len {α : Type} {m n : ℕ} (h : m = n) (f : Fin m → List α) :
    (List.finRange m).flatMap f = (List.finRange n).flatMap (fun i => f ⟨i.val, by omega⟩) := by
  subst h; rfl
lemma finRange_flatMap_split {α : Type} (a b : ℕ) (f : Fin (a + b) → List α) :
    (List.finRange (a + b)).flatMap f =
      (List.finRange a).flatMap (fun i => f ⟨i.val, by omega⟩) ++
      (List.finRange b).flatMap (fun j => f ⟨a + j.val, by omega⟩) := by
  induction b with
  | zero =>
    simp [List.finRange]
  | succ b ih =>
    rw [finRange_flatMap_congr_len (Nat.add_assoc a b 1).symm f, List.finRange_succ_last,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
    conv_rhs => rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
    rw [← List.append_assoc]
    congr 1
    exact ih (fun i => f ⟨i.val, by omega⟩)
lemma finRange_flatMap_mul {α : Type} (r e : ℕ) (f : Fin (r * e) → List α) :
    (List.finRange (r * e)).flatMap f =
      (List.finRange r).flatMap fun t => (List.finRange e).flatMap fun j =>
        f ⟨t.val * e + j.val, by
          have hm1 : (t.val + 1) * e ≤ r * e := Nat.mul_le_mul_right e t.isLt
          have : t.val * e + e = (t.val + 1) * e := by ring
          have := j.isLt; omega⟩ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [finRange_flatMap_congr_len (Nat.succ_mul r e) f, finRange_flatMap_split,
      ih (fun idx => f ⟨idx.val, by rw [Nat.succ_mul]; omega⟩),
      List.finRange_succ_last, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
    rfl
lemma buildGraph_spec {p q : ℕ} (hpq : p < q) (φ : CNF)
    (hne : ∀ c ∈ φ, c ≠ []) :
    let N0 := (occs φ).length
    let e0 := (occEdges φ).length
    let u0 : Fin e0 → Fin N0 := fun e => ((occEdges φ).get e).1
    let v0 : Fin e0 → Fin N0 := fun e => ((occEdges φ).get e).2
    buildGraph p q (encodeCNF φ) =
      pack ((q - p) * N0 + 2 * p * e0) (q * e0) (p * e0)
        ((q - p) * (e0 + (N0 - φ.length)))
        (graphAdj (blowupU hpq u0) (blowupV hpq v0)) := by
  intro N0 e0 u0 v0
  have hqp : (q - p) * e0 + p * e0 = q * e0 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hpq)]
  have hn_eq : (q - p) * N0 + p * e0 + p * e0 = (q - p) * N0 + 2 * p * e0 := by ring
  let n := (q - p) * N0 + 2 * p * e0
  let U := blowupU hpq u0
  let V := blowupV hpq v0
  unfold buildGraph bgHdr bgCop bgDum bgN bgBase bgPE
  simp only [countLits_cnf φ, countClauses_cnf φ, countOccEdges_cnf φ hne,
    mulU, un_length, un_append_un]
  have huC : dropK (un φ.length) (un N0) =
      un (N0 - φ.length) := by
    rw [dropK_eq, un_length]
    simp [un]
  rw [huC, un_append_un, hn_eq]
  have hcop : emitCopies p q (pairB (un n)
      (pairB (un N0)
        (encodeCNF φ))) =
      (List.finRange ((q - p) * e0)).flatMap fun idx =>
        (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
          graphAdj U V ⟨idx.val, by omega⟩ i j := by
    rw [finRange_flatMap_mul]
    unfold emitCopies
    have houter : ((List.range (q - p)).flatMap fun t =>
        emitCopyT (pairB (un t)
          (pairB (un n)
            (pairB (un N0)
              (encodeCNF φ))))) =
        (List.range (q - p)).flatMap (fun t => if ht : t < q - p then
          (List.finRange e0).flatMap fun j =>
            (List.finRange n).flatMap fun i => (List.finRange n).map fun k =>
              graphAdj U V ⟨t * e0 + j.val, by
                have hm1 : (t + 1) * e0 ≤ (q - p) * e0 := Nat.mul_le_mul_right e0 ht
                have : t * e0 + e0 = (t + 1) * e0 := by ring
                have := j.isLt; omega⟩ i k else []) := by
      apply List.flatMap_congr; intro t ht
      have ht' : t < q - p := List.mem_range.mp ht
      simp only [ht', ↓reduceDIte, emitCopyT, unpairB_pairB,
        un_length]
      let fEdge : Fin N0 × Fin N0 → List Bool := fun ab =>
        let uu : Fin n := ⟨t * N0 + ab.1.val, by
          have hm1 : (t + 1) * N0 ≤ (q - p) * N0 := Nat.mul_le_mul_right N0 ht'
          have : t * N0 + N0 = (t + 1) * N0 := by ring
          have := ab.1.isLt; omega⟩
        let vv : Fin n := ⟨t * N0 + ab.2.val, by
          have hm1 : (t + 1) * N0 ≤ (q - p) * N0 := Nat.mul_le_mul_right N0 ht'
          have : t * N0 + N0 = (t + 1) * N0 := by ring
          have := ab.2.isLt; omega⟩
        (List.finRange n).flatMap fun i => (List.finRange n).map fun k => decide (i = uu ∧ k = vv)
      have ha_eq : ((List.range N0).flatMap fun a =>
          emitCopyA (pairB (un a)
            (pairB (un t)
              (pairB (un n)
                (pairB (un N0)
                  (encodeCNF φ)))))) =
          (occEdges φ).flatMap fEdge := by
        unfold occEdges
        rw [List.flatMap_assoc]
        have hstep1 : ((List.range N0).flatMap fun a =>
            emitCopyA (pairB (un a)
              (pairB (un t)
                (pairB (un n)
                  (pairB (un N0)
                    (encodeCNF φ)))))) =
            (List.range N0).flatMap (fun a => if ha : a < N0 then
              ((List.finRange N0).filterMap fun b =>
                if occEdge φ ⟨a, ha⟩ b then some (⟨a, ha⟩, b) else none).flatMap fEdge else []) := by
          apply List.flatMap_congr; intro a ha
          have ha' : a < N0 := List.mem_range.mp ha
          simp only [ha', ↓reduceDIte, emitCopyA, unpairB_pairB,
            un_length]
          have hb_eq : ((List.range N0).flatMap fun b =>
              emitCopyB (pairB (un b)
                (pairB (un a)
                  (pairB (un t)
                    (pairB (un n)
                      (pairB (un N0)
                        (encodeCNF φ))))))) =
              (List.range N0).flatMap (fun b => if hb : b < N0 then
                if occEdge φ ⟨a, ha'⟩ ⟨b, hb⟩ then fEdge (⟨a, ha'⟩, ⟨b, hb⟩) else [] else []) := by
            apply List.flatMap_congr; intro b hb
            have hb' : b < N0 := List.mem_range.mp hb
            simp only [hb', ↓reduceDIte, emitCopyB, unpairB_pairB,
              mulU, un_length, un_append_un]
            rw [hasOccEdgeF_spec φ hne ⟨a, ha'⟩ ⟨b, hb'⟩]
            cases ho : occEdge φ ⟨a, ha'⟩ ⟨b, hb'⟩
            · rfl
            · simp only [bflag, sel,
                reduceCtorEq, ↓reduceIte]
              have hlt1 : t * N0 + a < n := by
                have hm1 : (t + 1) * N0 ≤ (q - p) * N0 := Nat.mul_le_mul_right N0 ht'
                have : t * N0 + N0 = (t + 1) * N0 := by ring
                omega
              have hlt2 : t * N0 + b < n := by
                have hm1 : (t + 1) * N0 ≤ (q - p) * N0 := Nat.mul_le_mul_right N0 ht'
                have : t * N0 + N0 = (t + 1) * N0 := by ring
                omega
              exact emitEdgeMat_spec n ⟨t * N0 + a, hlt1⟩ ⟨t * N0 + b, hlt2⟩
          rw [hb_eq, flatMap_range_eq_finRange N0 (fun b : Fin N0 =>
              if occEdge φ ⟨a, ha'⟩ b then fEdge (⟨a, ha'⟩, b) else [])]
          have hfm : ∀ (l : List (Fin N0)),
              (l.flatMap fun b => if occEdge φ ⟨a, ha'⟩ b then fEdge (⟨a, ha'⟩, b) else []) =
              (l.filterMap fun b => if occEdge φ ⟨a, ha'⟩ b then some (⟨a, ha'⟩, b) else none).flatMap fEdge := by
            intro l
            induction l with
            | nil => rfl
            | cons x xs ih =>
              cases h : occEdge φ ⟨a, ha'⟩ x <;> simp [h, ih]
          exact hfm (List.finRange N0)
        rw [hstep1, flatMap_range_eq_finRange N0 (fun a : Fin N0 =>
            ((List.finRange N0).filterMap fun b =>
              if occEdge φ a b then some (a, b) else none).flatMap fEdge)]
      rw [ha_eq]
      have hlist_fin : ∀ (l : List (Fin N0 × Fin N0)),
          l.flatMap fEdge = (List.finRange l.length).flatMap fun j => fEdge (l.get j) := by
        intro l
        have hmap : l = (List.finRange l.length).map (fun j => l.get j) := by
          apply List.ext_getElem
          · simp
          · intro idx h1 h2; simp
        conv_lhs => rw [hmap]
        rw [List.flatMap_map]
      rw [hlist_fin (occEdges φ)]
      apply List.flatMap_congr; intro j _
      have he0_pos : 0 < e0 := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
      have hidx_lt : t * e0 + j.val < (q - p) * e0 := by
        have hm1 : (t + 1) * e0 ≤ (q - p) * e0 := Nat.mul_le_mul_right e0 ht'
        have : t * e0 + e0 = (t + 1) * e0 := by ring
        have := j.isLt; omega
      let idx : Fin (q * e0) := ⟨t * e0 + j.val, by omega⟩
      have hdiv : idx.val / e0 = t := by
        show (t * e0 + j.val) / e0 = t
        rw [Nat.mul_comm t e0, Nat.mul_add_div he0_pos, Nat.div_eq_of_lt j.isLt, add_zero]
      have hmod : idx.val % e0 = j.val := by
        show (t * e0 + j.val) % e0 = j.val
        rw [Nat.mul_comm t e0, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      have hfin_mod : (⟨idx.val % e0, Nat.mod_lt _ he0_pos⟩ : Fin e0) = j := Fin.ext hmod
      have hu_lt : t * N0 + (u0 j).val < n := by
        have hm1 : (t + 1) * N0 ≤ (q - p) * N0 := Nat.mul_le_mul_right N0 ht'
        have : t * N0 + N0 = (t + 1) * N0 := by ring
        have := (u0 j).isLt; omega
      have hv_lt : t * N0 + (v0 j).val < n := by
        have hm1 : (t + 1) * N0 ≤ (q - p) * N0 := Nat.mul_le_mul_right N0 ht'
        have : t * N0 + N0 = (t + 1) * N0 := by ring
        have := (v0 j).isLt; omega
      have hu_eq : U idx = ⟨t * N0 + (u0 j).val, hu_lt⟩ := by
        apply Fin.ext
        rw [blowupU_val_lt hpq u0 idx hidx_lt he0_pos, hdiv, hfin_mod]
      have hv_eq : V idx = ⟨t * N0 + (v0 j).val, hv_lt⟩ := by
        apply Fin.ext
        rw [blowupV_val_lt hpq v0 idx hidx_lt he0_pos, hdiv, hfin_mod]
      change (List.finRange n).flatMap (fun i => (List.finRange n).map fun k =>
          decide (i = ⟨t * N0 + (u0 j).val, hu_lt⟩ ∧ k = ⟨t * N0 + (v0 j).val, hv_lt⟩)) =
        (List.finRange n).flatMap (fun i => (List.finRange n).map fun k =>
          decide (i = U idx ∧ k = V idx))
      rw [hu_eq, hv_eq]
    rw [houter, flatMap_range_eq_finRange (q - p) (fun t : Fin (q - p) =>
      (List.finRange e0).flatMap fun j =>
        (List.finRange n).flatMap fun i => (List.finRange n).map fun k =>
          graphAdj U V ⟨t.val * e0 + j.val, by
            have hm1 : (t.val + 1) * e0 ≤ (q - p) * e0 := Nat.mul_le_mul_right e0 t.isLt
            have : t.val * e0 + e0 = (t.val + 1) * e0 := by ring
            have := j.isLt; omega⟩ i k)]
  have hdum : emitDumEdges (pairB (un (p * e0))
      (pairB (un n)
        (un ((q - p) * N0)))) =
      (List.finRange (p * e0)).flatMap fun s =>
        (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
          graphAdj U V ⟨(q - p) * e0 + s.val, by omega⟩ i j := by
    unfold emitDumEdges
    simp only [unpairB_pairB, un_length]
    have h1 : ((List.range (p * e0)).flatMap fun s =>
        emitDumEdge (pairB (un s)
          (pairB (un n)
            (un ((q - p) * N0))))) =
        (List.range (p * e0)).flatMap (fun s => if hs : s < p * e0 then
          (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
            graphAdj U V ⟨(q - p) * e0 + s, by omega⟩ i j else []) := by
      apply List.flatMap_congr; intro s hs
      have hs' : s < p * e0 := List.mem_range.mp hs
      simp only [hs', ↓reduceDIte, emitDumEdge, unpairB_pairB,
        un_append_un, ← un_succ]
      let idx : Fin (q * e0) := ⟨(q - p) * e0 + s, by omega⟩
      have hge : (q - p) * e0 ≤ idx.val := Nat.le_add_right _ _
      have hu_eq : (U idx).val = (q - p) * N0 + s + s := by
        rw [blowupU_val_ge hpq u0 idx hge]
        dsimp [idx]; omega
      have hv_eq : (V idx).val = (q - p) * N0 + s + s + 1 := by
        rw [blowupV_val_ge hpq v0 idx hge]
        dsimp [idx]; omega
      rw [← hv_eq, ← hu_eq]
      exact emitEdgeMat_spec n (U idx) (V idx)
    rw [h1, flatMap_range_eq_finRange (p * e0) (fun s : Fin (p * e0) =>
      (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
        graphAdj U V ⟨(q - p) * e0 + s.val, by omega⟩ i j)]
  rw [hcop, hdum]
  unfold pack header
  have hflat : ((List.finRange (q * e0)).flatMap fun e =>
      (List.finRange n).flatMap fun i => (List.finRange n).map fun j => graphAdj U V e i j) =
      ((List.finRange ((q - p) * e0)).flatMap fun idx =>
        (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
          graphAdj U V ⟨idx.val, by omega⟩ i j) ++
      ((List.finRange (p * e0)).flatMap fun s =>
        (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
          graphAdj U V ⟨(q - p) * e0 + s.val, by omega⟩ i j) := by
    rw [finRange_flatMap_congr_len hqp.symm (fun e =>
      (List.finRange n).flatMap fun i => (List.finRange n).map fun j => graphAdj U V e i j),
      finRange_flatMap_split]
  rw [hflat]
  simp only [un, List.length_replicate, List.append_assoc]
  rfl
def packNo (p q : ℕ) : List Bool :=
  if h : p < q then
    let u0 : Fin 1 → Fin 2 := fun _ => ⟨0, by omega⟩
    let v0 : Fin 1 → Fin 2 := fun _ => ⟨1, by omega⟩
    pack ((q - p) * 2 + 2 * p * 1) (q * 1) (p * 1) ((q - p) * (1 + 0))
      (graphAdj (blowupU h u0) (blowupV h v0))
  else []
lemma packNo_not_in_lang {p q : ℕ} (hpq : p < q) :
    packNo p q ∉ ({s | ∃ (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool),
      pack n m k d A = s ∧ k = p * m / q ∧ feasible n m k d (quad n m A)} : Language Bool) := by
  rintro ⟨n, m, k, d, A, hpack, _, hfeas⟩
  unfold packNo at hpack
  simp only [hpq, ↓reduceDIte] at hpack
  obtain ⟨rfl, rfl, rfl, rfl, hA⟩ := pack_inj hpack
  subst hA
  let u0 : Fin 1 → Fin 2 := fun _ => ⟨0, by omega⟩
  let v0 : Fin 1 → Fin 2 := fun _ => ⟨1, by omega⟩
  have hvc : HasVC u0 v0 0 :=
    (blowup_iff_vc (c := 0) hpq u0 v0 (fun _ => Nat.zero_lt_one)
      (fun e₁ e₂ _ => Subsingleton.elim e₁ e₂)).mp hfeas
  obtain ⟨S, hScard, hScov⟩ := hvc
  have hSemp : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hScard)
  rcases hScov ⟨0, by omega⟩ with h | h <;> simp [hSemp] at h
def reduce (p q : ℕ) (s : List Bool) : List Bool :=
  sel (wfNoEmptyF s) (packNo p q) (buildGraph p q s)
lemma cpt_reduce (p q : ℕ) : CPTs (reduce p q) :=
  cpt_sel cpt_wfNoEmptyF
    (cpt_const (packNo p q)) (cpt_buildGraph p q)
lemma reduce_graphCode {p q : ℕ} (hpq : p < q) (s : List Bool) :
    ∃ (n m d : ℕ) (u v : Fin m → Fin n),
      (∀ e, u e < v e) ∧ Function.Injective (fun e : Fin m => (u e, v e)) ∧
      pack n m (p * m / q) d (fun e i j => decide (i = u e ∧ j = v e)) = reduce p q s := by
  have hq_pos : 0 < q := by omega
  unfold reduce wfNoEmptyF
  cases hwf : wfNoEmptyB s
  · simp only [bflag, sel,
      packNo, hpq, ↓reduceDIte]
    let u0 : Fin 1 → Fin 2 := fun _ => ⟨0, by omega⟩
    let v0 : Fin 1 → Fin 2 := fun _ => ⟨1, by omega⟩
    have hdiv : p * (q * 1) / q = p * 1 := by
      rw [mul_one, mul_one, Nat.mul_div_cancel p hq_pos]
    refine ⟨(q - p) * 2 + 2 * p * 1, q * 1, (q - p) * (1 + 0),
      blowupU hpq u0, blowupV hpq v0,
      blowup_lt hpq u0 v0 (fun _ => Nat.zero_lt_one),
      blowup_inj hpq u0 v0 (fun e₁ e₂ _ => Subsingleton.elim e₁ e₂), ?_⟩
    rw [hdiv]; rfl
  · simp only [bflag, sel,
      reduceCtorEq, ↓reduceIte]
    obtain ⟨φ, rfl, hne⟩ := (wfNoEmptyB_iff s).mp hwf
    let N0 := (occs φ).length
    let e0 := (occEdges φ).length
    let u0 : Fin e0 → Fin N0 := fun e => ((occEdges φ).get e).1
    let v0 : Fin e0 → Fin N0 := fun e => ((occEdges φ).get e).2
    have hdiv : p * (q * e0) / q = p * e0 := by
      rw [← Nat.mul_assoc, Nat.mul_comm p q, Nat.mul_assoc, Nat.mul_div_cancel_left _ hq_pos]
    refine ⟨(q - p) * N0 + 2 * p * e0, q * e0, (q - p) * (e0 + (N0 - φ.length)),
      blowupU hpq u0, blowupV hpq v0,
      blowup_lt hpq u0 v0 (occEdges_lt φ),
      blowup_inj hpq u0 v0 (occEdges_inj φ), ?_⟩
    rw [hdiv]
    exact (buildGraph_spec hpq φ hne).symm
lemma reduce_iff {p q : ℕ} (hpq : p < q) (s : List Bool) :
    s ∈ SAT ↔
      reduce p q s ∈ ({x | ∃ (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool),
        pack n m k d A = x ∧ k = p * m / q ∧ feasible n m k d (quad n m A)} : Language Bool) := by
  have hq_pos : 0 < q := by omega
  unfold reduce wfNoEmptyF
  cases hwf : wfNoEmptyB s
  · simp only [bflag, sel]
    constructor
    · rintro ⟨φ, rfl, σ, hσ⟩
      have hne : ∀ c ∈ φ, c ≠ [] := by
        intro c hc he
        subst he
        rw [CNF.eval, List.all_eq_true] at hσ
        have := hσ [] hc
        simp [Clause.eval] at this
      have htr : wfNoEmptyB (encodeCNF φ) = true :=
        (wfNoEmptyB_iff _).mpr ⟨φ, rfl, hne⟩
      rw [hwf] at htr; simp at htr
    · intro hmem
      exact (packNo_not_in_lang hpq hmem).elim
  · simp only [bflag, sel,
      reduceCtorEq, ↓reduceIte]
    obtain ⟨φ, rfl, hne⟩ := (wfNoEmptyB_iff s).mp hwf
    let N0 := (occs φ).length
    let e0 := (occEdges φ).length
    let u0 : Fin e0 → Fin N0 := fun e => ((occEdges φ).get e).1
    let v0 : Fin e0 → Fin N0 := fun e => ((occEdges φ).get e).2
    have hbg := buildGraph_spec hpq φ hne
    have hdiv : p * (q * e0) / q = p * e0 := by
      rw [← Nat.mul_assoc, Nat.mul_comm p q, Nat.mul_assoc, Nat.mul_div_cancel_left _ hq_pos]
    constructor
    · rintro ⟨ψ, henc, hsat⟩
      have hφψ : ψ = φ := encodeCNF_injective henc
      subst hφψ
      have hvc : HasVC u0 v0 (N0 - ψ.length) := (occGraph_vc_iff_sat ψ hne).mpr hsat
      have hfeas := (blowup_iff_vc (c := N0 - ψ.length) hpq u0 v0 (occEdges_lt ψ) (occEdges_inj ψ)).mpr hvc
      exact ⟨(q - p) * N0 + 2 * p * e0, q * e0, p * e0, (q - p) * (e0 + (N0 - ψ.length)),
        graphAdj (blowupU hpq u0) (blowupV hpq v0), hbg.symm, hdiv.symm, hfeas⟩
    · rintro ⟨n, m, k, d, A, hpack, _, hfeas⟩
      rw [hbg] at hpack
      obtain ⟨rfl, rfl, rfl, rfl, hA⟩ := pack_inj hpack
      subst hA
      have hvc := (blowup_iff_vc (c := N0 - φ.length) hpq u0 v0 (occEdges_lt φ) (occEdges_inj φ)).mp hfeas
      exact ⟨φ, rfl, (occGraph_vc_iff_sat φ hne).mp hvc⟩
def tmPushSet {K : Type} {Γ : K → Type} {Λ σ : Type} : Turing.TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k g q => Set.range (fun v => (⟨k, g v⟩ : Σ k, Γ k)) ∪ tmPushSet q
  | .peek _ _ q => tmPushSet q
  | .pop _ _ q => tmPushSet q
  | .load _ q => tmPushSet q
  | .branch _ q₁ q₂ => tmPushSet q₁ ∪ tmPushSet q₂
  | .goto _ => ∅
  | .halt => ∅
lemma tmPushSet_finite {K : Type} {Γ : K → Type} {Λ σ : Type} [Finite σ]
    (q : Turing.TM2.Stmt Γ Λ σ) : (tmPushSet q).Finite := by
  induction q with
  | push _ _ _ ih => exact (Set.finite_range _).union ih
  | peek _ _ _ ih => exact ih
  | pop _ _ _ ih => exact ih
  | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty
def restStmt {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T : ∀ k, Set (Γ k)) :
    ∀ (q : Turing.TM2.Stmt Γ Λ σ), (∀ k s, (⟨k, s⟩ : Σ j, Γ j) ∈ tmPushSet q → s ∈ T k) →
    Turing.TM2.Stmt (fun k => {s : Γ k // s ∈ T k}) Λ σ
  | .push k g q, h => .push k (fun v => ⟨g v, h k (g v) (Or.inl ⟨v, rfl⟩)⟩)
      (restStmt T q (fun j s hs => h j s (Or.inr hs)))
  | .peek k f q, h => .peek k (fun v o => f v (o.map Subtype.val)) (restStmt T q h)
  | .pop k f q, h => .pop k (fun v o => f v (o.map Subtype.val)) (restStmt T q h)
  | .load a q, h => .load a (restStmt T q h)
  | .branch f q₁ q₂, h => .branch f
      (restStmt T q₁ (fun j s hs => h j s (Or.inl hs)))
      (restStmt T q₂ (fun j s hs => h j s (Or.inr hs)))
  | .goto f, _ => .goto f
  | .halt, _ => .halt
def projCfg {K : Type} {Γ : K → Type} {Λ σ : Type} (T : ∀ k, Set (Γ k))
    (cfg : Turing.TM2.Cfg (fun k => {s : Γ k // s ∈ T k}) Λ σ) : Turing.TM2.Cfg Γ Λ σ :=
  ⟨cfg.l, cfg.var, fun k => (cfg.stk k).map Subtype.val⟩
lemma projCfg_inj {K : Type} {Γ : K → Type} {Λ σ : Type} (T : ∀ k, Set (Γ k)) :
    Function.Injective (projCfg (Λ := Λ) (σ := σ) T) := by
  rintro ⟨l₁, v₁, S₁⟩ ⟨l₂, v₂, S₂⟩ h
  simp only [projCfg, Turing.TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl, rfl, hS⟩ := h
  congr 1
  funext k
  exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma map_update_val {K : Type} [DecidableEq K] {Γ : K → Type} (T : ∀ k, Set (Γ k))
    (S : ∀ k, List {s : Γ k // s ∈ T k}) (k : K) (l : List {s : Γ k // s ∈ T k}) :
    (fun j => (Function.update S k l j).map Subtype.val) =
      Function.update (fun j => (S j).map Subtype.val) k (l.map Subtype.val) := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]
lemma projCfg_stepAux {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T : ∀ k, Set (Γ k)) (q : Turing.TM2.Stmt Γ Λ σ)
    (hq : ∀ k s, (⟨k, s⟩ : Σ j, Γ j) ∈ tmPushSet q → s ∈ T k)
    (v : σ) (S : ∀ k, List {s : Γ k // s ∈ T k}) :
    projCfg T (Turing.TM2.stepAux (restStmt T q hq) v S) =
      Turing.TM2.stepAux q v (fun k => (S k).map Subtype.val) := by
  induction q generalizing v S with
  | push k g q ih =>
    simp only [restStmt, Turing.TM2.stepAux]
    rw [ih, map_update_val]
    rfl
  | peek k f q ih =>
    simp only [restStmt, Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [List.head?_map])
  | pop k f q ih =>
    simp only [restStmt, Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [map_update_val, List.head?_map, List.map_tail])
  | load a q ih =>
    simp only [restStmt, Turing.TM2.stepAux]
    exact ih hq (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [restStmt, Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ v S
    · exact ih₁ _ v S
  | goto f => rfl
  | halt => rfl
lemma cpt_to_finTM2 {f : List Bool → List Bool} (hf : CPTs f) :
    ∃ (P : Polynomial ℕ)
      (M : Turing.TM2ComputableInTime (fun s : List Bool => s) (fun s : List Bool => s) f),
      (∀ j, Finite (M.tm.Γ j)) ∧ (∀ b, M.time b ≤ P.eval b) := by
  classical
  obtain ⟨c⟩ := hf
  let _ : DecidableEq c.tm.K := c.tm.kDecidableEq
  let _ : Fintype c.tm.K := c.tm.kFin
  let _ : Fintype c.tm.Λ := c.tm.ΛFin
  let _ : Fintype c.tm.σ := c.tm.σFin
  let _ : Fintype (c.tm.Γ c.tm.k₀) := c.tm.Γk₀Fin
  let T : ∀ k : c.tm.K, Set (c.tm.Γ k) := fun k =>
    {s | k = c.tm.k₀ ∨ k = c.tm.k₁ ∨ (⟨k, s⟩ : Σ j, c.tm.Γ j) ∈ ⋃ l : c.tm.Λ, tmPushSet (c.tm.m l)}
  let e₀ : {s : c.tm.Γ c.tm.k₀ // s ∈ T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀ :=
    { toFun := Subtype.val
      invFun := fun s => ⟨s, Or.inl rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₁ : {s : c.tm.Γ c.tm.k₁ // s ∈ T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁ :=
    { toFun := Subtype.val
      invFun := fun s => ⟨s, Or.inr (Or.inl rfl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let hΓ0Fin : Fintype {s : c.tm.Γ c.tm.k₀ // s ∈ T c.tm.k₀} := Fintype.ofEquiv _ e₀.symm
  let tm' : Turing.FinTM2 :=
    { K := c.tm.K
      kDecidableEq := c.tm.kDecidableEq
      kFin := c.tm.kFin
      k₀ := c.tm.k₀
      k₁ := c.tm.k₁
      Γ := fun k => {s : c.tm.Γ k // s ∈ T k}
      Λ := c.tm.Λ
      main := c.tm.main
      ΛFin := c.tm.ΛFin
      σ := c.tm.σ
      initialState := c.tm.initialState
      σFin := c.tm.σFin
      Γk₀Fin := hΓ0Fin
      m := fun l => restStmt T (c.tm.m l) (fun k s hs => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l, hs⟩))) }
  have hFin : ∀ j : tm'.K, Finite (tm'.Γ j) := by
    intro j
    by_cases h0 : j = c.tm.k₀
    · subst h0; exact Finite.of_fintype _
    · by_cases h1 : j = c.tm.k₁
      · subst h1
        have : Finite (c.tm.Γ c.tm.k₁) := Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin : (⋃ l : c.tm.Λ, tmPushSet (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l => tmPushSet_finite (c.tm.m l)
        have : Finite ↥(⋃ l : c.tm.Λ, tmPushSet (c.tm.m l)) := hUfin.to_subtype
        refine Finite.of_injective (f := fun x : tm'.Γ j =>
            (⟨⟨j, x.1⟩, by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩ : ↥(⋃ l : c.tm.Λ, tmPushSet (c.tm.m l)))) ?_
        intro x y hxy
        have h1' := congrArg (fun z => z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep : ∀ cfg : tm'.Cfg, Option.map (projCfg T) (tm'.step cfg) = c.tm.step (projCfg T cfg) := by
    rintro ⟨l, v, S⟩
    cases l with
    | none => rfl
    | some l =>
      change some (projCfg T (Turing.TM2.stepAux (restStmt T (c.tm.m l) _) v S)) =
        some (Turing.TM2.stepAux (c.tm.m l) v (fun k => (S k).map Subtype.val))
      exact congrArg some (projCfg_stepAux T (c.tm.m l) _ v S)
  have hiter : ∀ (steps : ℕ) (cfg : tm'.Cfg),
      Option.map (projCfg T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (projCfg T cfg)) := by
    intro steps
    induction steps with
    | zero => intro cfg; rfl
    | succ steps ih =>
      intro cfg
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      cases hcur : (flip bind tm'.step)^[steps] (some cfg) with
      | none =>
        have hih := ih cfg
        rw [hcur] at hih
        rw [← hih]; rfl
      | some cfg' =>
        have hih := ih cfg
        rw [hcur] at hih
        rw [← hih]
        exact hstep cfg'
  let M : Turing.TM2ComputableInTime (fun s : List Bool => s) (fun s : List Bool => s) f :=
    { tm := tm'
      inputAlphabet := e₀.trans c.inputAlphabet
      outputAlphabet := e₁.trans c.outputAlphabet
      time := fun b => c.time.eval b
      outputsFun := fun a =>
        { steps := (c.outputsFun a).steps
          evals_in_steps := by
            have horig := (c.outputsFun a).evals_in_steps
            have hinit : projCfg T (Turing.initList tm' (a.map (e₀.trans c.inputAlphabet).invFun)) =
                Turing.initList c.tm (a.map c.inputAlphabet.invFun) := by
              simp only [projCfg, Turing.initList]
              congr 1; funext k
              by_cases hk : k = c.tm.k₀
              · subst hk
                dsimp only [tm']
                simp only [↓reduceDIte, eq_mpr_eq_cast, cast_eq, List.map_map]
                rfl
              · dsimp only [tm']
                simp only [hk, ↓reduceDIte, List.map_nil]
            have hhalt : projCfg T (Turing.haltList tm' ((f a).map (e₁.trans c.outputAlphabet).invFun)) =
                Turing.haltList c.tm ((f a).map c.outputAlphabet.invFun) := by
              simp only [projCfg, Turing.haltList]
              congr 1; funext k
              by_cases hk : k = c.tm.k₁
              · subst hk
                dsimp only [tm']
                simp only [↓reduceDIte, eq_mpr_eq_cast, cast_eq, List.map_map]
                rfl
              · dsimp only [tm']
                simp only [hk, ↓reduceDIte, List.map_nil]
            apply Option.map_injective (projCfg_inj T)
            rw [hiter, hinit, horig]
            exact (congrArg some hhalt).symm
          steps_le_m := (c.outputsFun a).steps_le_m } }
  exact ⟨c.time, M, hFin, fun _ => le_rfl⟩
end
end PEqualNP.Outside.L_pcx_398
theorem PEqualNP.Outside.L_pcx_398 : (let F := ZMod 2
let header := fun n : ℕ => List.replicate n true ++ [false]
let pack := fun (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool) =>
  header n ++ header m ++ header k ++ header d ++
    (List.finRange m).flatMap (fun e => (List.finRange n).flatMap
      (fun i => (List.finRange n).map (fun j => A e i j)))
let quad := fun (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool)
    (x : Fin n → F) (e : Fin m) =>
  Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    if A e i j then x i * x j else 0))
let feasible := fun (n m k d : ℕ) (Q : (Fin n → F) → Fin m → F) =>
  let X := Fin n → F
  let Y := Fin m → F
  let tree := fun (target : (X × Y) → Y) (allowed : Set (Set Y)) (K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (query : List Bool → (X × Y) →ₗ[F] F)
      (bias : List Bool → F) (out : List Bool → Set Y),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : X × Y, (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → target z ∈ out p
  let allowed := {L : Set Y | ∃ (R : Submodule F Y) (c : Y),
      Module.finrank F R ≤ k ∧ L = {w : Y | w-c ∈ R}}
  tree (fun z => z.2 + Q z.1) allowed (2^d)
∀ (p q : ℕ) (_ : p < q),
  let lang : Language Bool := {s | ∃ (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool),
    pack n m k d A = s ∧ k = p*m/q ∧ feasible n m k d (quad n m A)}
  let graphCode := fun s : List Bool => ∃ (n m d : ℕ) (u v : Fin m → Fin n),
    (∀ e, u e < v e) ∧ Function.Injective (fun e : Fin m => (u e, v e)) ∧
    pack n m (p*m/q) d (fun e i j => decide (i = u e ∧ j = v e)) = s
  PEqualNP.Library.NPComplete lang ∧
    ∃ (reduce : List Bool → List Bool) (P : Polynomial ℕ)
      (M : Turing.TM2ComputableInTime (fun s : List Bool => s) (fun s : List Bool => s) reduce),
      (∀ j, Finite (M.tm.Γ j)) ∧ (∀ b, M.time b ≤ P.eval b) ∧
      ∀ s : List Bool, graphCode (reduce s) ∧ (s ∈ PEqualNP.Search.SAT ↔ reduce s ∈ lang)) := by
  dsimp only
  intro p q hpq
  constructor
  · refine ⟨PEqualNP.Outside.L_pcx_398.lang_in_NP p q hpq, fun L' hL' => ?_⟩
    obtain ⟨g, hg, hiff⟩ := PEqualNP.Outside.L_pcx_398.Lib.SearchHelpers.Tab.npHard_SAT L' hL'
    exact ⟨fun x => PEqualNP.Outside.L_pcx_398.reduce p q (g x),
      PEqualNP.Outside.L_pcx_398.Lib.Machines.cpt_comp hg (PEqualNP.Outside.L_pcx_398.cpt_reduce p q),
      fun x => (hiff x).trans (PEqualNP.Outside.L_pcx_398.reduce_iff hpq (g x))⟩
  · obtain ⟨P, M, hFin, htime⟩ :=
      PEqualNP.Outside.L_pcx_398.cpt_to_finTM2 (PEqualNP.Outside.L_pcx_398.cpt_reduce p q)
    exact ⟨PEqualNP.Outside.L_pcx_398.reduce p q, P, M, hFin, htime, fun s =>
      ⟨PEqualNP.Outside.L_pcx_398.reduce_graphCode hpq s,
       PEqualNP.Outside.L_pcx_398.reduce_iff hpq s⟩⟩
